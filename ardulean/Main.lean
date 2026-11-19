import ArduLean.Vehicle
import ArduLean.Driver.EstimatorProbe

/-!
`ardulean LINES STORAGE OUT TASKS GYRO_STORED ACCEL_STORED FRAMES`: the driver of the ArduLean executable, the translated
vehicle on the lock-step boundary, as `HAL_Lockstep::run` (reference/hal/lockstep.cpp on branch cpp2lean) runs the
reference: the translated static construction (`Vehicle_lib.staticConstruct`), `AP_Vehicle::setup()`, then
`AP_Vehicle::loop()` and the IO processes, repeatedly, until the input lines are consumed. The translated scheduler
decides what runs; this file is the HAL's waits and lock-step points (the `PMem.hal` hook of the translation, exported
as `cpp2lean_vehicle_hal`; the HAL's devices are ArduLean/Runtime/Hal.lean's `PMem.halDev`) and the boundary: it consumes the input
lines where the vehicle waits (per line: the estimator record, its RC frame, battery and uplink bytes, as
sim/harness/vehicle.py prepares them), and writes one output line per consumed line (OUT: `t=<us> pwm=<16> [down=<hex>]`,
as lockstep.cpp's `emit_output`) and the scheduler's tasks of that step (TASKS: `t tick tasks`, as est_probe.cpp's
`tasks=`). LINES is a file of prepared lines (replaying a recorded flight, sim/checks/replay_check.py), or `-`: live mode, the
lines on standard input and each output line on standard output as soon as the vehicle needs the next input line
(sim/harness/vehicle.py). GYRO_STORED and ACCEL_STORED (`0` or `1`): whether the INS ids are stored in the boot image;
FRAMES: `-` (no recorded downlink frame is read).
Diagnosis variables (their names keep the executable's earlier name): VEHICLE_REPLAY_MEMDUMP=k1,k2,...
(memory images at those lines, OUT.mem<k>), VEHICLE_REPLAY_TRACE (the translation's log on standard error at the end),
VEHICLE_REPLAY_STEPS=FILE (per main-loop step the lines consumed and the wall time).

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

namespace ArduLean

abbrev M := PMem.M

-- the HAL's state (`Mem.hx` slots, `Mem.hn`), its accessors and its devices: ArduLean/Runtime/Hal.lean (`VehicleHal`,
-- `PMem.halDev`); `Mem.hs`: the prepared input lines; `Mem.hb`: the output lines, then (after a separator) the task lines
open VehicleHal

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

-- AP_Scheduler's layout in the C++ build of branch cpp2lean (clang): _num_tasks +97, _tick_counter +98, _tick_counter32 +100, _last_run +104
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
lock-step loop of the flight programs of sim/ through sim/harness/vehicle.py). An opaque function of the driver (as the HAL hook
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

/-- the HAL members that call back into the vehicle or step the World (configuration key `hal_callbacks`: the
translation calls them as `PMem.hal`, exported here as `cpp2lean_vehicle_hal`): lockstep.cpp's waits and the World's
lock-step points; every other member is a device of ArduLean/Runtime/Hal.lean (`PMem.halDev`, which the translation
calls directly) -/
def halM (name : String) (this : UInt64) (a : Array UInt64) : M UInt64 := do
  if ["cpp2lean::est_mark", "cpp2lean::world_events", "cpp2lean::world_next", "AP_HAL::Scheduler::delay",
      "AP_HAL::Scheduler::delay_microseconds", "AP_HAL::Scheduler::delay_microseconds_boost"].contains name &&
      (← get).hx[iUnknown]! == 7 && !(← get).sysInit then
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
  | "AP_HAL::Scheduler::delay" => do
    delayMs a[0]!
    return 0
  | "AP_HAL::Scheduler::delay_microseconds" | "AP_HAL::Scheduler::delay_microseconds_boost" => do
    delayUs a[0]!
    return 0
  | _ => PMem.halDev name this a

@[export cpp2lean_vehicle_hal]
def halImplDef (name : String) (this : UInt64) (args : Array UInt64) (s : PMem.Mem) : UInt64 × PMem.Mem :=
  (halM name this args).run s

end ArduLean

open ArduLean VehicleHal in
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
    -- the address of `AP_BoardConfig::_singleton` for RCOutput::write's BRD_SAFETY_MASK (ArduLean/Runtime/Hal.lean)
    m := { m with hx := m.hx.set! iBoardCfg addr'AP_BoardConfig___singleton }
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
    IO.eprintln s!"ardulean: AP_Scheduler _loop_rate_hz={lr} _active_loop_rate_hz={alr} _loop_period_us={lp} _num_tasks={nt}"
    let t1 ← IO.monoNanosNow
    IO.eprintln s!"ardulean: setup done in {(t1 - t0).toFloat / 1e9} s, {m.hx[iLines]!} lines consumed"
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
    -- (total definitions) whether a loop of the translation ran out of fuel (`PMem.Mem.fuelOut`, sticky)
    ht.putStrLn s!"# fuel_out={m.fuelOut}"
    -- (total definitions) whether a call in a recursive component ran out of depth (`PMem.Mem.depthOut`, sticky)
    ht.putStrLn s!"# depth_out={m.depthOut}"
    let lg := m.log.toList.eraseDups
    ht.putStrLn s!"# log ({m.log.size}): {lg.take 60}"
    if m.hx[iUnknown]! == 7 then
      for l in m.log do IO.eprintln l
    IO.eprintln s!"ardulean: {m.hx[iLines]!} lines, {loops} loops, {(t2 - t0).toFloat / 1e9} s; step mean {mean} us p99 {p99.toFloat / 1e3} us max {mx.toFloat / 1e3} us"
    return 0
  | _ => IO.eprintln "usage: ardulean LINES STORAGE OUT TASKS GYRO_STORED ACCEL_STORED FRAMES"; return 2
