import Vehicle_lib
import EstimatorProbe

/-!
`vehicle_replay LINES STORAGE OUT TASKS FRAMES ANSWERS GYRO_STORED ACCEL_STORED` (README.md "Phase 5: the whole-vehicle
replay"): the translated vehicle on a recorded session, as `HAL_Lockstep::run` (reference/hal/lockstep.cpp) runs the
reference: the translated static construction (`Vehicle_lib.staticConstruct`), `AP_Vehicle::setup()`, then
`AP_Vehicle::loop()` and the IO processes, repeatedly, until the input lines are consumed. The translated scheduler
decides what runs; this file is the HAL (lockstep.cpp's drivers, the `PMem.hal` hook of the translation, exported as
`cpp2lean_vehicle_hal`) and the boundary: it consumes the input lines (LINES, prepared by
ardupilot/vehicle/vehicle_replay.py: the estimator record of each line, its RC frame, battery and uplink bytes) where
the vehicle waits, and writes one output line per consumed line (OUT: `t=<us> pwm=<16> [down=<hex>]`, as lockstep.cpp's
`emit_output`) and the scheduler's tasks of that step (TASKS: `t tick tasks`, as est_probe.cpp's `tasks=`).

The HAL, as lockstep.cpp:
* the clock is the estimator World's (`EstScheduler`, fed every input line ahead; it consumes one when the HAL consumes
  one, and runs its timer processes: the sensor stand-ins);
* `delay`, `delay_microseconds`, `delay_microseconds_boost` consume lines until the time has passed; consuming line k
  writes output line k-1, appends the uplink to SERIAL0, takes the RC frame and the battery, steps the World (clock,
  GPS latch, sensor timer processes), runs the vehicle's timer processes, the timer failsafe and the IO processes;
  `delay` runs the delay callback while the remaining time is at least its threshold (Scheduler::delay's rule);
* a delay inside the World (`ins.init`, `barometer.calibrate`, `wait_for_sample`: EstScheduler's delays) consumes lines
  there; the memory side catches up at the next HAL call, the next loop, or the end of setup (each line: its output line,
  uplink, RC, battery, failsafe, IO processes, and the delay callback once per line while one is registered): the
  deviation from the reference's order is that this work follows the World call instead of interleaving with it;
* RCInput, RCOutput (SITL's write/cork/push with the safety state and BRD_SAFETY_MASK), AnalogIn (the battery pins),
  Util (soft armed, safety state, the RTC), the UARTs (GCSMemory's SERIAL0), Storage (the memory's).
-/

open Vehicle_lib
open FloatLib.Floats (Binary32 Binary64)

namespace VehicleReplay

abbrev M := PMem.M

-- the HAL's scalar state (`Mem.hx`)
def iLines := 0      -- input lines consumed by the memory side
def iHave := 1       -- an output line is due (lockstep.cpp `have_line`)
def iSafety := 2     -- RCOutput safety state: 1 SAFETY_DISARMED, 2 SAFETY_ARMED
def iCorked := 3
def iRcFresh := 4
def iRcHave := 5
def iBattV := 6      -- binary32 bits
def iBattA := 7
def iDcbFn := 8      -- delay callback (function address), its threshold
def iDcbMin := 9
def iFsFn := 10      -- timer failsafe
def iInTimer := 11
def iInIo := 12
def iDone := 13      -- the input is exhausted
def iDcbCount := 14
def iInDcb := 15
def iPrevTick := 16
def iCurT := 17      -- the time of the last consumed line
def iAnalog := 20
def iUnknown := 21
def iLive := 22      -- (Phase 5c) live mode: the input lines from standard input
def iWritten := 23   -- (Phase 5c) live mode: output lines written so far (index into `Mem.hb`)
def iCurLine := 24   -- (Phase 5c) the line of the World's last lock-step point
def nSlots := 32
-- `Mem.hn`: 0 RC input PWM, 1 RCOutput out, 2 pending, 3 IO processes (obj, method pairs), 4 analog source pins,
-- 5 the scheduler's `_last_run` at the last step, 6 timer processes (obj, method pairs)
-- `Mem.hs`: the prepared input lines; `Mem.hb`: the output lines, then (after a separator) the task lines

def gx (i : Nat) : M UInt64 := return (← get).hx[i]!
def sx (i : Nat) (v : UInt64) : M Unit := modify fun s => { s with hx := s.hx.set! i v }
def gn (i : Nat) : M (Array UInt64) := return (← get).hn[i]!
def sn (i : Nat) (v : Array UInt64) : M Unit := modify fun s => { s with hn := s.hn.set! i v }
/-- (Phase 5d, speed) change slot `i` in place: `Array.modify` takes the element out of `hn` first, so `f` gets the only
reference (`sn i ((← gn i).push v)` copied the whole array: slot 8 holds every input line's time, so each line copied
all earlier ones, about 3 % of the replay's time at the end of the flight) -/
def modN (i : Nat) (f : Array UInt64 → Array UInt64) : M Unit := modify fun s => { s with hn := s.hn.modify i f }

def hexDigit (c : Char) : Nat := if c.isDigit then c.toNat - '0'.toNat else c.toNat - 'a'.toNat + 10
def hexBytes (s : String) : ByteArray := Id.run do
  let cs := s.toList.toArray
  let mut out := ByteArray.empty
  for k in [0:cs.size / 2] do
    out := out.push (UInt8.ofNat (hexDigit cs[2 * k]! * 16 + hexDigit cs[2 * k + 1]!))
  return out
def hexNat (s : String) : Nat := s.foldl (fun a c => a * 16 + hexDigit c) 0
def toHex (b : ByteArray) : String := Id.run do
  let d := "0123456789abcdef".toList.toArray
  let mut s := ""
  for x in b.toList do
    s := s.push d[(x / 16).toNat]! |>.push d[(x % 16).toNat]!
  return s

def copterA : UInt64 := addr'copter
def schedA : UInt64 := addr'copter + 208

-- the copter_ref layout of AP_Scheduler (clang): _num_tasks +97, _tick_counter +98, _tick_counter32 +100, _last_run +104
def tasksOfStep : M String := do
  let tick32 ← PMem.ldU32 (schedA + 100)
  let prev ← gx iPrevTick
  let lr ← PMem.ldU64 (schedA + 104)
  let n := (← PMem.ldU8 (schedA + 97)).toNat
  if lr == 0 || n == 0 then return "-"
  let tick16 ← PMem.ldU16 (schedA + 98)
  let snap ← gn 5
  let mut cur : Array UInt64 := #[]
  for i in [0:n] do
    cur := cur.push (← PMem.ldU16 (lr + (2 * i).toUInt64)).toUInt64
  sn 5 cur
  sx iPrevTick tick32.toUInt64
  if tick32.toUInt64 == prev then return "-"
  let mut ran : Array String := #[]
  for i in [0:n] do
    let c := cur[i]!
    if c != snap.getD i 0 || c == tick16.toUInt64 then ran := ran.push (toString i)
  return if ran.isEmpty then "-" else String.intercalate "," ran.toList

/-- lockstep.cpp `emit_output`: the output line of the last consumed line (and the step's tasks) -/
def emitOutput : M Unit := do
  let s ← get
  let out := s.hn[1]!
  let pwm := String.intercalate "," ((List.range 16).map fun i => toString (out[i]!.toNat))
  let t ← gx iCurT
  let down := if s.tx.size == 0 then "" else " down=" ++ toHex s.tx
  let tasks ← tasksOfStep
  let tick := (← PMem.ldU32 (schedA + 100)).toNat
  let dcb ← gx iDcbCount
  let ev := (← get).w.est_scheduler._events
  let wl := (← get).w.est_scheduler._lines
  let l1 := (s!"t={t.toNat} pwm={pwm}{down}").toUTF8
  let l2 := (s!"T {t.toNat} {tick} {tasks} {dcb.toNat} {ev.toNat} {wl.toNat}").toUTF8
  modify fun s => { s with tx := ByteArray.empty, hb := (s.hb.push l1).push l2 }
  sx iDcbCount 0

def toks (k : Nat) : M (Array String) := do
  return (((← get).hs[k]!).splitOn " ").toArray

/-- (Phase 5c) live mode: the output lines not yet written (from index `from_`) to standard output, flushed, then the
next input line from standard input ("" at its end): lockstep.cpp's `emit_output` and `getline` (the vehicle is in the
lock-step loop of sim/fly_reference.py through sim/lean_vehicle.py). An opaque function of the driver (as the HAL hook
`PMem.hal`): its implementation does the IO; `k` (the line's index) keeps each call distinct. -/
@[extern "cpp2lean_vehicle_live_read"]
opaque liveRead (k : Nat) (outs : Array ByteArray) (from_ : Nat) : String

@[export cpp2lean_vehicle_live_read]
unsafe def liveReadImpl (k : Nat) (outs : Array ByteArray) (from_ : Nat) : String :=
  let act : IO String := do
    let out ← IO.getStdout
    for i in [from_:outs.size] do
      let b := outs[i]!
      if b.size > 2 && b.get! 0 == 116 && b.get! 1 == 61 then   -- `t=`: an output line
        out.write b
        out.write "\n".toUTF8
    out.flush
    let inp ← IO.getStdin
    let l ← inp.getLine
    return String.ofList (l.toList.filter (fun c => c != '\n' && c != '\r'))
  match unsafeIO act with
  | .ok l => l
  | .error _ => ""

def callDelayCb : M Unit := do
  if (← gx iDcbFn) == 0 || (← gx iInDcb) != 0 then return
  sx iInDcb 1
  modify fun s => { s with inDelayCb := true }
  AP_Vehicle.scheduler_delay_callback
  modify fun s => { s with inDelayCb := false }
  sx iInDcb 0

def runProcs (slot flag : Nat) : M Unit := do
  if (← gx flag) != 0 then return
  sx flag 1
  let ps ← gn slot
  for j in [0:ps.size / 2] do
    fnptr'0 ps[2 * j + 1]! ps[2 * j]!
  sx flag 0

def runFailsafe : M Unit := do
  if (← gx iFsFn) != 0 then failsafe_check_static

/-- the time of input line `l` (1-based), from the input lines' times (`Mem.hn` slot 8) -/
def lineTime (l : Nat) : M UInt64 := do
  return (← gn 8).getD (l - 1) 0

/-- (Phase 5c) the World's events of a lock-step point (`Output.est_mark`, reference/hal/est_scheduler.cpp) drained by
the translation's worldOutputs'drain: the vehicle's part of lockstep.cpp's step and delay at that point. The memory side's
clock is the line's time during that work (the World's own clock may be another one: a call being repeated). -/
def withLineClock (l : Nat) (act : M Unit) : M Unit := do
  let wc := (← get).w.est_scheduler._clock_us
  let lt ← lineTime l
  modify fun s => { s with w := { s.w with est_scheduler := { s.w.est_scheduler with _clock_us := lt } } }
  act
  modify fun s => { s with w := { s.w with est_scheduler := { s.w.est_scheduler with _clock_us := wc } } }

/-- lockstep.cpp's step, second half (HALSITL::Scheduler::timer_event): after the World's timer processes (the sensors'),
the vehicle's timer processes, the timer failsafe, the IO processes -/
def lineProcs (l : Nat) : M Unit := withLineClock l do
  if (← gx iInTimer) == 0 then
    runProcs 6 iInTimer
  runFailsafe
  runProcs 3 iInIo

/-- lockstep.cpp's Scheduler::delay after one `delay_microseconds(1000)` inside a delay of the World: the delay callback
when `_min_delay_cb_ms <= remaining` (counted as lockstep.cpp counts it) -/
def worldDelayCb (remaining : UInt64) : M Unit := do
  let minCb := (← gx iDcbMin)
  if minCb ≤ remaining then
    sx iDcbCount ((← gx iDcbCount) + 1)
    withLineClock (← gx iCurLine).toNat callDelayCb

/-- lockstep.cpp's step, first half: the output line of the last line (if any), the next input line (from the prepared
lines; in live mode from standard input), its uplink, RC frame and battery, and its record fed to the World's scheduler,
which consumes it at its next step (a wait of the World's code or the HAL's `delay`). The World is never fed ahead: a
wait of the World's code that runs out of lines is repeated with the next line (VehicleBridge: `cpp2lean::world_events`, `cpp2lean::world_next`). -/
def readLine : M Unit := do
  if (← gx iHave) != 0 then emitOutput
  let k := (← gx iLines).toNat
  if k ≥ (← get).hs.size then
    if (← gx iLive) != 0 && (← gx iDone) == 0 then
      let s ← get
      let l := liveRead k s.hb (← gx iWritten).toNat
      sx iWritten (← get).hb.size.toUInt64
      if l != "" then modify fun s => { s with hs := s.hs.push l }
  if k ≥ (← get).hs.size then
    sx iHave 0
    sx iDone 1
    return
  -- (diagnosis, VEHICLE_REPLAY_MEMDUMP) the memory's bytes at the start of consuming line k + 1, as the reference's
  -- `Lockstep::step` entry with k lines read
  if (← gn 7).contains k.toUInt64 then
    let mb := (← get).m
    modify fun s => { s with hb := s.hb.push ((s!"M {k} ").toUTF8 ++ mb) }
  let t ← toks k
  sx iCurT (t[1]!.toNat!).toUInt64
  modN 8 (·.push (t[1]!.toNat!).toUInt64)
  if t[114]! != "-" then
    sn 0 ((t[114]!.splitOn ",").toArray.map fun x => x.toNat!.toUInt64)
    sx iRcFresh 1
    sx iRcHave 1
  if t[115]! != "-" then
    match t[115]!.splitOn "," with
    | [v, a] =>
      sx iBattV (hexNat v).toUInt64
      sx iBattA (hexNat a).toUInt64
    | _ => pure ()
  if t[116]! != "-" then
    modify fun s => { s with rx := s.rx.extract s.rxPos s.rx.size ++ hexBytes t[116]!, rxPos := 0 }
  sx iLines (k + 1).toUInt64
  sx iHave 1
  -- SERIAL0's channel (its object, once GCS::setup_console made it; its sequence number)
  if (← get).chan0 == 0 then
    -- clang's layouts (as VehicleHarnessData): GCS::_chan at +32 of GCS, the channel's transmit sequence at +418
    let g ← PMem.ldU64 addr'GCS___singleton
    let c ← if g != 0 then PMem.ldU64 (g + 32) else pure 0
    if c != 0 then modify fun s => { s with chan0 := c, seqAddr := c + 418 }
  modify fun s => { s with curStep := k + 1 }
  -- the line's record to the World's scheduler (lockstep.cpp: the line parsed; the GPS latch is the World's step)
  modify fun s => { s with w := { s.w with est_scheduler := (Estimator_lib.EstScheduler.feed s.w.est_scheduler (EstimatorProbe.record t)).1 } }

/-- the World's events of the last World call or step: the translation's drain (saves, notifications, texts, MAVLink
sends, and the lock-step points `est_mark`, which call back into `halM`) -/
def drainWorld : M Unit := worldOutputs'drain

/-- the HAL's own wait (lockstep.cpp's `delay_microseconds` outside the World): the next line, which the World consumes
at once (its step: the clock, the GPS latch, the sensors' timer processes), then the vehicle's part through the
step's lock-step points -/
def worldStep : M Unit := do
  modify fun s =>
    let sc := s.w.est_scheduler
    let (sc', w', o') := Estimator_lib.EstScheduler.step sc { s.w with est_scheduler := default } s.eo
    { s with w := { w' with est_scheduler := sc' }, eo := o' }
  drainWorld

def delayUs (usec : UInt64) : M Unit := do
  let start ← PMem.clock
  repeat
    if (← PMem.clock) - start ≥ usec || (← gx iDone) != 0 then break
    readLine
    if (← gx iDone) != 0 then break
    worldStep

def delayMs (ms : UInt64) : M Unit := do
  let start := ((← PMem.clock) / 1000).toUInt32
  let mut now := start
  repeat
    delayUs 1000
    let minCb := (← gx iDcbMin).toUInt32
    if minCb ≤ ms.toUInt32 - (now - start) then
      sx iDcbCount ((← gx iDcbCount) + 1)
      callDelayCb
    now := ((← PMem.clock) / 1000).toUInt32
    if now - start ≥ ms.toUInt32 || (← gx iDone) != 0 then break

def f32 (b : UInt64) : Binary32 := Binary32.ofBits b.toUInt32
def bits (x : Binary32) : UInt64 := (Binary32.toBits x).toUInt64

/-- HALSITL::ADCSource::voltage_latest on the line's battery (lockstep.cpp `AnalogSource`) -/
def pinVoltage (pin : UInt64) : M UInt64 := do
  let v := f32 (← gx iBattV)
  let a := f32 (← gx iBattA)
  let volt := v / (10.1 : Binary32)
  let curr := a / (17.0 : Binary32)
  return match pin.toNat with
    | 254 => bits (65535.0 : Binary32)   -- ANALOG_INPUT_BOARD_VCC: ADC_MAX_PIN_VALUE
    | 12 => bits curr
    | 13 => bits volt
    | 14 => bits (curr * (0.25 : Binary32))
    | 15 => bits (volt * (0.25 : Binary32))
    | _ => 0

def addProc (slot : Nat) (fa : UInt64) : M Unit := do
  let obj ← PMem.ldU64 fa
  let meth ← PMem.ldU64 (fa + 8)
  let ps ← gn slot
  for j in [0:ps.size / 2] do
    if ps[2 * j]! == obj && ps[2 * j + 1]! == meth then return
  if ps.size / 2 < 8 then sn slot (ps.push obj |>.push meth)

/-- C's `printf` formatting of the console's `printf` (the conversions the vehicle's console texts use: %s %u %d %i %x
%c %%, with `l` length modifiers), its arguments as the translation passes them (64-bit words, strings by address) -/
def cformat (fmt : UInt64) (args : Array UInt64) : M ByteArray := do
  let mut out := ByteArray.empty
  let mut p := fmt
  let mut ai := 0
  repeat
    let c ← PMem.ldU8 p
    if c == 0 then break
    p := p + 1
    if c != 37 then
      out := out.push c
      continue
    let mut d ← PMem.ldU8 p
    while d == 108 || d == 104 || d == 122 do   -- l, h, z
      p := p + 1
      d ← PMem.ldU8 p
    p := p + 1
    let a := args.getD ai 0
    if d == 37 then
      out := out.push 37
      continue
    ai := ai + 1
    match d.toNat with
    | 115 =>   -- %s
      let mut q := a
      repeat
        let ch ← PMem.ldU8 q
        if ch == 0 then break
        out := out.push ch
        q := q + 1
    | 117 => out := out ++ (toString a.toUInt32.toNat).toUTF8
    | 100 | 105 => out := out ++ (toString a.toUInt32.toInt32.toInt).toUTF8
    | 120 => out := out ++ (String.ofList (Nat.toDigits 16 a.toUInt32.toNat)).toUTF8
    | 99 => out := out.push a.toUInt8
    | _ => out := out.push 37 |>.push d
  return out

/-- the HAL members (lockstep.cpp's drivers; AP_HAL's defaults where lockstep.cpp keeps them) -/
def halM (name : String) (this : UInt64) (a : Array UInt64) : M UInt64 := do
  if (← get).hx[iUnknown]! == 7 && !(← get).sysInit then
    let s ← get
    modify fun s' => { s' with log := s'.log.push s!"{name} {a.toList} wl={s.w.est_scheduler._lines} ml={s.hx[iLines]!}" }
  match name with
  | "cpp2lean::est_mark" => do
    -- (Phase 5c) a lock-step point of the World (reference/hal/est_scheduler.cpp `est_mark`), from the drain
    match a[0]!.toNat with
    | 0 => sx iCurLine a[1]!
    | 1 =>
      sx iCurLine a[1]!
      lineProcs a[1]!.toNat
    | 2 => worldDelayCb a[1]!
    | _ => pure ()
    return 0
  | "cpp2lean::world_more" => return (if (← gx iDone) == 0 then 1 else 0)
  | "cpp2lean::world_events" => do
    -- (Phase 5c) a wait of the World's code ran out of lines (VehicleBridge: the call is repeated from its start): the
    -- lock-step points and events of this attempt up to that point (from a[0], the ones done in earlier attempts) are
    -- the reference's, run now (the World is the one the attempt left); the result is the number of events done; then
    -- `cpp2lean::world_next` (after the World is set back) writes the output line and reads and feeds the next line
    let eo := (← get).eo
    let p := a[0]!.toNat
    let x := (List.range (eo.size - p)).find? (fun i => match eo[p + i]? with
      | some (Estimator_lib.Output.est_mark k _) => k == 3
      | _ => false) |>.map (· + p) |>.getD eo.size
    modify fun s => { s with eo := eo.extract p x }
    drainWorld
    return x.toUInt64
  | "cpp2lean::world_next" => do
    readLine
    return 0
  | "cpp2lean::world_unexpected_wait" => do
    modify fun s => { s with log := s.log.push s!"world wait without a snapshot at line {s.hx[iLines]!}" }
    return 0
  | "AP_HAL::Scheduler::delay" => do
    delayMs a[0]!
    return 0
  | "AP_HAL::Scheduler::delay_microseconds" | "AP_HAL::Scheduler::delay_microseconds_boost" => do
    delayUs a[0]!
    return 0
  | "AP_HAL::Scheduler::register_delay_callback" => do
    sx iDcbFn a[0]!
    sx iDcbMin a[1]!
    return 0
  | "AP_HAL::Scheduler::register_timer_failsafe" => do
    sx iFsFn a[0]!
    return 0
  | "AP_HAL::Scheduler::register_io_process" => do
    addProc 3 a[0]!
    return 0
  | "AP_HAL::Scheduler::register_timer_process" => do
    addProc 6 a[0]!
    return 0
  | "AP_HAL::Scheduler::expect_delay_ms" => return 0
  | "AP_HAL::Scheduler::in_main_thread" => return 1
  | "AP_HAL::RCInput::new_input" =>
    let r ← gx iRcFresh
    sx iRcFresh 0
    return r
  | "AP_HAL::RCInput::num_channels" => return (if (← gx iRcHave) != 0 then 16 else 0)
  | "AP_HAL::RCInput::read" =>
    let pw0 ← gn 0
    if a.size == 1 then return (if a[0]! < 16 then pw0.getD a[0]!.toNat 0 else 0)
    -- read(periods, len)
    let n := if (← gx iRcHave) != 0 then min a[1]!.toNat 16 else 0
    let pw ← gn 0
    for i in [0:n] do
      PMem.stU16 (a[0]! + (2 * i).toUInt64) (pw.getD i 0).toUInt16
    return n.toUInt64
  | "AP_HAL::RCOutput::write" =>
    let ch := a[0]!.toNat
    let mut p := a[1]!
    if (← gx iSafety) == 1 then
      -- AP_BoardConfig::get_singleton()->get_safety_mask(): BRD_SAFETY_MASK (state.ignore_safety_channels, +8)
      let bc ← PMem.ldU64 addr'AP_BoardConfig___singleton
      let mask ← if bc != 0 then PMem.ldU32 (bc + 8) else pure 0
      if (mask >>> ch.toUInt32) &&& 1 == 0 then p := 0
    if ch < 32 then
      if (← gx iCorked) != 0 then modN 2 (·.set! ch p) else modN 1 (·.set! ch p)
    return 0
  | "AP_HAL::RCOutput::read" | "AP_HAL::RCOutput::read_last_sent" =>
    let o ← gn 1
    if a.size == 1 then return (if a[0]! < 32 then o[a[0]!.toNat]! else 0)
    let out ← gn 1
    for i in [0:min a[1]!.toNat 32] do
      PMem.stU16 (a[0]! + (2 * i).toUInt64) out[i]!.toUInt16
    return 0
  | "AP_HAL::RCOutput::cork" =>
    if (← gx iCorked) == 0 then
      sn 2 (← gn 1)
      sx iCorked 1
    return 0
  | "AP_HAL::RCOutput::push" =>
    if (← gx iCorked) != 0 then
      sn 1 (← gn 2)
      sx iCorked 0
    return 0
  | "AP_HAL::RCOutput::force_safety_on" => do
    sx iSafety 1
    return 1
  | "AP_HAL::RCOutput::force_safety_off" => do
    sx iSafety 2
    return 0
  | "AP_HAL::RCOutput::get_freq" => return 50
  | "AP_HAL::RCOutput::enable_ch" | "AP_HAL::RCOutput::disable_ch" | "AP_HAL::RCOutput::set_freq"
  | "AP_HAL::RCOutput::set_default_rate" | "AP_HAL::RCOutput::set_output_mode" | "AP_HAL::RCOutput::set_dshot_rate"
  | "AP_HAL::RCOutput::set_dshot_esc_type" | "AP_HAL::RCOutput::set_esc_scaling" | "AP_HAL::RCOutput::update_channel_masks"
  | "AP_HAL::RCOutput::get_output_mode_banner" => return 0
  | "AP_HAL::Util::set_soft_armed" => do
    modify (fun s => { s with armed := a[0]! != 0 })
    return 0
  | "AP_HAL::Util::safety_switch_state" => gx iSafety
  | "AP_HAL::Util::get_hw_rtc" => return 1767225600 * 1000000 + (← PMem.clock)
  | "AP_HAL::Util::was_watchdog_reset" | "AP_HAL::Util::was_watchdog_armed" | "AP_HAL::Util::was_watchdog_safety_off"
  | "AP_HAL::Util::get_system_load" => return 0
  | "AP_HAL::Util::get_system_id" =>
    -- lockstep.cpp's Util::get_system_id: `strncpy(buf, "cpp2lean-lockstep", 50); return true;` (Phase 5c: the banner
    -- is translated; AP_HAL::Util::snprintf/vsnprintf are translated code now, not HAL)
    let id := "cpp2lean-lockstep".toUTF8
    for i in [0:50] do
      PMem.stU8 (a[0]! + i.toUInt64) (if i < id.size then id.get! i else 0)
    return 1
  | "AP_HAL::Util::get_system_id_unformatted" =>
    -- lockstep.cpp's Util::get_system_id_unformatted (Phase 5d: AUTOPILOT_VERSION's uid2, reached by the QGroundControl
    -- session): `len = MIN(len, strlen(id)); memcpy(buf, id, len); return true;`
    let id := "cpp2lean-lockstep".toUTF8
    let n := min (← PMem.ldU8 a[1]!).toNat id.size
    for i in [0:n] do
      PMem.stU8 (a[0]! + i.toUInt64) (id.get! i)
    PMem.stU8 a[1]! n.toUInt8
    return 1
  | "AP_HAL::AnalogIn::power_status_flags" => return 0   -- AP_HAL::AnalogIn's (lockstep.cpp does not override it)
  | "AP_HAL::AnalogIn::channel" =>
    let pins ← gn 4
    sn 4 (pins.push a[0]!)
    return 0x100 + 8 * pins.size.toUInt64
  | "AP_HAL::AnalogIn::board_voltage" => return bits (5.0 : Binary32)
  | "AP_HAL::AnalogIn::servorail_voltage" => return 0
  | "AP_HAL::AnalogSource::set_pin" =>
    let k := ((this - 0x100) / 8).toNat
    modN 4 (·.set! k a[0]!)
    return (if a[0]! != 255 then 1 else 0)
  | "AP_HAL::AnalogSource::voltage_average" | "AP_HAL::AnalogSource::voltage_latest"
  | "AP_HAL::AnalogSource::voltage_average_ratiometric" =>
    let k := ((this - 0x100) / 8).toNat
    pinVoltage ((← gn 4).getD k 0)
  | "AP_HAL::BetterStream::printf" =>
    -- the console is SERIAL0 (lockstep.cpp: `&d_serial0` as console): its transmit queue
    let b ← cformat a[0]! (a.extract 1 a.size)
    modify fun s => { s with tx := s.tx ++ b.extract 0 (16384 - s.tx.size) }
    return 0
  | "AP_HAL::Util::available_memory" => return 512 * 1024
  | "AP_HAL::GPIO::arming_checks" => return 1
  | "AP_HAL::Storage::healthy" => return 1
  | "AP_HAL::HAL::serial" => return (0x10 : UInt64) + a[0]!
  | "AP_HAL::UARTDriver::begin" =>
    -- (Phase 5c) lockstep.cpp's UART::_begin: a baud rate is kept (0 changes nothing); SERIAL3 (`AP_HAL::HAL::serial` 3,
    -- 0x13) is the GPS's port, which the World holds (its stand-in EstUART, reference/hal/est_uart.h): its begin there
    if this == 0x13 && a[0]! != 0 then
      modify fun s => { s with w := { s.w with est_uart := Estimator_lib.EstUART.begin_uint32_t_uint16_t2 s.w.est_uart a[0]!.toUInt32 0 0 } }
    return 0
  | "AP_HAL::UARTDriver::set_options" => return (if a[0]! == 0 then 1 else 0)   -- AP_HAL::UARTDriver's: options == 0
  | "AP_HAL::UARTDriver::disable_rxtx" | "AP_HAL::UARTDriver::set_unbuffered_writes" => return 0
  | _ =>
    modify fun s => { s with log := s.log.push s!"hal? {name}" }
    return 0

@[export cpp2lean_vehicle_hal]
def halImplDef (name : String) (this : UInt64) (args : Array UInt64) (s : PMem.Mem) : UInt64 × PMem.Mem :=
  (halM name this args).run s

end VehicleReplay

open VehicleReplay in
def main (args : List String) : IO UInt32 := do
  match args with
  | [linesP, stP, outP, tasksP, gyroS, accelS, framesP] =>
    -- (Phase 5c) no recorded frame is read any more (FRAMES may be absent or empty); LINES `-`: live mode (standard input)
    let frameLines ← if framesP != "-" && (← System.FilePath.pathExists framesP) then IO.FS.lines framesP else pure #[]
    let mut frames : Array (UInt32 × Array ByteArray) := #[]
    for l in frameLines do
      match l.splitOn " " with
      | [i, h] =>
        let id := i.toNat!.toUInt32
        match frames.findIdx? (·.1 == id) with
        | some j => frames := frames.modify j fun (a, fs) => (a, fs.push (hexBytes h))
        | none => frames := frames.push (id, #[hexBytes h])
      | _ => pure ()
    let st ← IO.FS.readBinFile stP
    let live := linesP == "-"
    let lines ← if live then pure #[] else IO.FS.lines linesP
    let m0 := initMem st
    let w0 := m0.w
    let w0 := { w0 with gps'inp := { w0.gps'inp with params_0_type_configured := true, find_serial_found_SerialProtocol_GPS_at1 := #[true, true] },
                        ins'inp := { w0.ins'inp with gyro_id__gyro_count_loaded := gyroS == "1", accel_id__accel_count_loaded := accelS == "1", was_watchdog_reset := false } }
    let dumpAt : Array UInt64 := match (← IO.getEnv "VEHICLE_REPLAY_MEMDUMP") with
      | some s => ((s.splitOn ",").filter (· != "")).toArray.map (·.toNat!.toUInt64)
      | none => #[]
    let hn0 : Array (Array UInt64) := #[Array.replicate 16 0, Array.replicate 32 0, Array.replicate 32 0, #[], #[], #[], #[], dumpAt, #[]]
    let mut m : PMem.Mem := { m0 with w := w0, hs := lines, hx := Array.replicate nSlots 0, hn := hn0 }
    m := { m with frames := frames, framePos := frames.map (fun _ => 0) }
    -- AP_HAL::Scheduler::_min_delay_cb_ms is 0 until a callback is registered (a static object: zero), so lockstep.cpp's
    -- delay counts a callback (`delay_callbacks`) in every iteration until then, and runs none
    m := { m with hx := m.hx.set! iSafety 1 }
    if live then m := { m with hx := m.hx.set! iLive 1 }
    if (← IO.getEnv "VEHICLE_REPLAY_TRACE").isSome then m := { m with hx := m.hx.set! iUnknown 7 }
    let t0 ← IO.monoNanosNow
    -- C++ static construction, then HAL_Lockstep::run: setup(), set_system_initialized(), loop() + IO processes
    let ((), m1) := (do staticDynamicInit; staticConstruct : PMem.M Unit).run m
    m := m1
    let ((), m2) := (do AP_Vehicle.setup copterA : PMem.M Unit).run m
    m := { m2 with sysInit := true }
    let ((lr, alr, lp, nt), _) := (do
        return ((← PMem.ldI16 (schedA + 58)), (← PMem.ldU16 (schedA + 60)), (← PMem.ldU16 (schedA + 64)), (← PMem.ldU8 (schedA + 97))) : PMem.M _).run m
    IO.eprintln s!"vehicle_replay: AP_Scheduler _loop_rate_hz={lr} _active_loop_rate_hz={alr} _loop_period_us={lp} _num_tasks={nt}"
    let t1 ← IO.monoNanosNow
    IO.eprintln s!"vehicle_replay: setup done in {(t1 - t0).toFloat / 1e9} s, {m.hx[iLines]!} lines consumed"
    let mut loops := 0
    let mut stepNs : Array Nat := #[]
    let mut stepLn : Array UInt64 := #[]
    let mut last := m.hx[iLines]!
    let mut ta ← IO.monoNanosNow
    repeat
      if m.hx[iDone]! != 0 then break
      let ((), m3) := (do AP_Vehicle.loop copterA; runProcs 3 iInIo : PMem.M Unit).run m
      m := m3
      loops := loops + 1
      if m.hx[iLines]! != last then
        let tb ← IO.monoNanosNow
        stepNs := stepNs.push (tb - ta)
        stepLn := stepLn.push m.hx[iLines]!
        ta := tb
        last := m.hx[iLines]!
    let t2 ← IO.monoNanosNow
    let outs := m.hb
    let h ← IO.FS.Handle.mk outP .write
    let ht ← IO.FS.Handle.mk tasksP .write
    for b in outs do
      if b.size > 2 && b.get! 0 == 77 && b.get! 1 == 32 then
        -- a memory dump: `M <k> <bytes>` -> <OUT>.mem<k>
        let sp := (List.range (b.size - 2)).find? (fun i => b.get! (i + 2) == 32) |>.getD 0
        let k := String.fromUTF8! (b.extract 2 (sp + 2))
        IO.FS.writeBinFile s!"{outP}.mem{k}" (b.extract (sp + 3) b.size)
        continue
      let s := String.fromUTF8! b
      if s.startsWith "T " then ht.putStrLn s else h.putStrLn s
    -- the HAL storage at the end (lockstep.cpp's `--storage-out`)
    IO.FS.writeBinFile s!"{outP}.storage" m.st
    -- (Phase 5d, profiling) VEHICLE_REPLAY_STEPS=FILE: per main-loop step the input lines consumed so far and the
    -- step's wall time in ns
    if let some sp := (← IO.getEnv "VEHICLE_REPLAY_STEPS") then
      let hs ← IO.FS.Handle.mk sp .write
      for i in [0:stepNs.size] do
        hs.putStrLn s!"{stepLn[i]!} {stepNs[i]!}"
    let sorted := stepNs.qsort (· < ·)
    let n := sorted.size
    let mean := if n == 0 then 0.0 else (sorted.foldl (· + ·) 0).toFloat / n.toFloat / 1e3
    let p99 := if n == 0 then 0 else sorted[n * 99 / 100]!
    let mx := if n == 0 then 0 else sorted[n - 1]!
    ht.putStrLn s!"# loops={loops} lines={m.hx[iLines]!} setup_s={(t1 - t0).toFloat / 1e9} loop_s={(t2 - t1).toFloat / 1e9}"
    ht.putStrLn s!"# step_us mean={mean} p99={p99.toFloat / 1e3} max={mx.toFloat / 1e3} n={n}"
    ht.putStrLn s!"# unreached={m.unreached.toList.eraseDups}"
    let lg := m.log.toList.eraseDups
    ht.putStrLn s!"# log ({m.log.size}): {lg.take 60}"
    if m.hx[iUnknown]! == 7 then
      for l in m.log do IO.eprintln l
    IO.eprintln s!"vehicle_replay: {m.hx[iLines]!} lines, {loops} loops, {(t2 - t0).toFloat / 1e9} s; step mean {mean} us p99 {p99.toFloat / 1e3} us max {mx.toFloat / 1e3} us"
    return 0
  | _ => IO.eprintln "usage: vehicle_replay LINES STORAGE OUT TASKS GYRO_STORED ACCEL_STORED FRAMES"; return 2
