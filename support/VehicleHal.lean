import VehicleMemoryV

/-!
Written by hand for cpp2lean; copied by `cpp2lean.py --param-memory` next to a translation whose configuration
names it (`imports`: the vehicle translation, `ardupilot/vehicle/Vehicle.json`). Do not edit the copies.

The HAL's devices of the vehicle translation as definitions (README.md "Phase 5: total definitions"): the members of
lockstep.cpp's drivers (reference/hal/lockstep.cpp) that change only the HAL's state and the memory, and never call
back into the translated vehicle or step the estimator World: RCInput, RCOutput (SITL's write/cork/push with the
safety state and BRD_SAFETY_MASK), AnalogIn (the battery pins), Util (soft armed, safety state, the RTC, the system
id), the UARTs, Storage, the console's `printf`, and the registrations of the scheduler's callbacks (which only record
them). The translation calls these as `PMem.halDev`, an ordinary definition the kernel can unfold, so that a statement
about the motor outputs sees what `RCOutput::write` does. The members that call back (`AP_HAL::Scheduler::delay`,
`delay_microseconds`, `delay_microseconds_boost` and the World's lock-step points `cpp2lean::est_mark`,
`cpp2lean::world_events`, `cpp2lean::world_next`: they consume input lines, step the World and run the vehicle's
callbacks, the IO processes and the timer failsafe) stay with the replay driver (lean/VehicleReplay.lean), behind
`PMem.hal` (configuration key `hal_callbacks`). This file holds no vehicle logic.

The HAL's state lives in the memory state (`Mem.hx`: the scalar slots below; `Mem.hn`: 0 RC input PWM, 1 RCOutput
out, 2 pending, 3 IO processes (obj, method pairs), 4 analog source pins, 5 the scheduler's `_last_run` at the last
step, 6 timer processes (obj, method pairs), 7 memory dump points, 8 the input lines' times).
-/

open FloatLib.Floats (Binary32 Binary64)

namespace VehicleHal

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
def iBoardCfg := 25  -- the address of `AP_BoardConfig::_singleton` (set by the driver: BRD_SAFETY_MASK for RCOutput::write)
def nSlots := 32

def gx (i : Nat) : M UInt64 := return (← get).hx[i]!
def sx (i : Nat) (v : UInt64) : M Unit := modify fun s => { s with hx := s.hx.set! i v }
def gn (i : Nat) : M (Array UInt64) := return (← get).hn[i]!
def sn (i : Nat) (v : Array UInt64) : M Unit := modify fun s => { s with hn := s.hn.set! i v }
/-- (Phase 5d, speed) change slot `i` in place: `Array.modify` takes the element out of `hn` first, so `f` gets the only
reference (`sn i ((← gn i).push v)` copied the whole array: slot 8 holds every input line's time, so each line copied
all earlier ones, about 3 % of the replay's time at the end of the flight) -/
def modN (i : Nat) (f : Array UInt64 → Array UInt64) : M Unit := modify fun s => { s with hn := s.hn.modify i f }

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
%c %%, with `l` length modifiers), its arguments as the translation passes them (64-bit words, strings by address).
The loops are fuel loops (`PMem.loopFuel`), as the translation's. -/
def cformat (fmt : UInt64) (args : Array UInt64) : M ByteArray := do
  let mut out := ByteArray.empty
  let mut p := fmt
  let mut ai := 0
  for _ in PMem.loopFuel do
    let c ← PMem.ldU8 p
    if c == 0 then break
    p := p + 1
    if c != 37 then
      out := out.push c
      continue
    let mut d ← PMem.ldU8 p
    for _ in PMem.loopFuel do
      if !(d == 108 || d == 104 || d == 122) then break   -- l, h, z
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
      for _ in PMem.loopFuel do
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

end VehicleHal

namespace PMem

open VehicleHal in
/-- The HAL's devices (lockstep.cpp's drivers; AP_HAL's defaults where lockstep.cpp keeps them): a call of a HAL member
that does not call back into the vehicle, with the object's address and the arguments as 64-bit words, its result as a
64-bit word. -/
def halDev (name : String) (this : UInt64) (a : Array UInt64) : M UInt64 := do
  if (← get).hx[iUnknown]! == 7 && !(← get).sysInit then
    let s ← get
    modify fun s' => { s' with log := s'.log.push s!"{name} {a.toList} wl={s.w.est_scheduler._lines} ml={s.hx[iLines]!}" }
  match name with
  | "cpp2lean::world_more" => return (if (← gx iDone) == 0 then 1 else 0)
  | "cpp2lean::world_unexpected_wait" => do
    modify fun s => { s with log := s.log.push s!"world wait without a snapshot at line {s.hx[iLines]!}" }
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
      let bc ← PMem.ldU64 (← gx iBoardCfg)
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

end PMem
