import ArduLean.Runtime.Bridge
import ArduLean.Vehicle.libraries.AP_Param.AP_Param
import ArduLean.Vehicle.libraries.AP_BoardConfig.AP_BoardConfig
import ArduLean.Vehicle.libraries.GCS_MAVLink.GCS_MAVLink
import ArduLean.Vehicle.libraries.GCS_MAVLink.GCS_MAVLink_2
import ArduLean.Vehicle.World

/-!
ArduPilot `libraries/AP_BoardConfig`, part 2 of 2. Sources: `libraries/AP_BoardConfig/board_drivers.cpp`, `libraries/AP_BoardConfig/AP_BoardConfig.cpp`.

Items of `lean/Vehicle_lib.lean` (the vehicle translation), unchanged; placed by `tools/split_modules.py` (`ArduLean/Vehicle/INDEX.md`).
-/

open FloatLib.Floats (Binary32 Binary64)

set_option linter.unusedVariables false
set_option linter.unreachableTactic false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false

namespace Vehicle_lib

/-- C++ `AP_BoardConfig::init : void ()`, `AP_BoardConfig.cpp:497-531`. -/
def AP_BoardConfig.init (this : UInt64) : PMem.M Unit := do
  AP_BoardConfig.board_setup this
  let t'1 ← PMem.ldU64 ((0xba88 : UInt64) /- &hal -/ + 88)
  let t'2 ← PMem.halDev "AP_HAL::Util::get_hw_rtc" t'1 #[]
  let t'3 ← VehicleBridge.rtc'0
  VehicleBridge.AP_RTC.set_utc_usec'2 t'3 t'2 (2 : UInt8)
  worldOutputs'drain
  let t'4 ← AP_ParamT'unsigned_short_2.operator_const_unsigned_short__ (this + 74)
  let t'5 ← PMem.ldU16 t'4
  if (decide ((UInt32.toInt32 (UInt16.toUInt32 (t'5))) > (0 : Int32))) then
    let t'6 ← AP_ParamT'unsigned_short_2.operator_const_unsigned_short__ (this + 74)
    let t'7 ← PMem.ldU16 t'6
    let mut delay_ms : UInt16 := t'7
    let t'8 ← PMem.ldU64 ((0xba88 : UInt64) /- &hal -/ + 88)
    let t'9 ← PMem.halDev "AP_HAL::Util::was_watchdog_armed" t'8 #[]
    if ((t'9 != 0) && (decide ((UInt32.toInt32 (UInt16.toUInt32 (delay_ms))) > (200 : Int32)))) then
      let t'10 := Int16.toUInt16 (Int32.toInt16 ((200 : Int32)))
      delay_ms := t'10
    let t'11 ← PMem.ldU64 ((0xba88 : UInt64) /- &hal -/ + 80)
    discard <| PMem.hal "AP_HAL::Scheduler::delay" t'11 #[(UInt16.toUInt64 (delay_ms))]
  return ()

/-- C++ `AP_BoardConfig::board_init_safety : void ()`, `board_drivers.cpp:35-50`. -/
def AP_BoardConfig.board_init_safety.body (fp : UInt64) (this : UInt64) : PMem.M Unit := do
  let t'1 ← AP_ParamTBase'signed_char_1.get (this + 4)
  let t'2 ← PMem.ldI8 t'1
  let mut force_safety_off : Bool := ((Int8.toInt32 (t'2)) == (0 : Int32))
  let mut sc'5 := !force_safety_off
  if sc'5 then
    let t'3 ← PMem.ldU64 ((0xba88 : UInt64) /- &hal -/ + 88)
    let t'4 ← PMem.halDev "AP_HAL::Util::was_watchdog_safety_off" t'3 #[]
    sc'5 := (t'4 != 0)
  if sc'5 then
    let t'6 ← gcs
    GCS.send_text t'6 (6 : UInt32) (0x168ad : UInt64) /- "Forcing safety off for watchdog" -/ (fp + 0)
    force_safety_off := true
  if force_safety_off then
    let t'7 ← PMem.ldU64 ((0xba88 : UInt64) /- &hal -/ + 72)
    discard <| PMem.halDev "AP_HAL::RCOutput::force_safety_off" t'7 #[]
    let mut count : UInt8 := Int8.toUInt8 (Int32.toInt8 ((20 : Int32)))
    for _ in PMem.loopFuel do
      let t'8 ← PMem.ldU64 ((0xba88 : UInt64) /- &hal -/ + 88)
      let t'9 ← PMem.halDev "AP_HAL::Util::safety_switch_state" t'8 #[]
      let mut sc'12 := ((UInt32.toInt32 (UInt8.toUInt32 ((UInt64.toUInt8 (t'9))))) != (UInt32.toInt32 (UInt8.toUInt32 ((2 : UInt8)))))
      if sc'12 then
        let t'10 := count
        let t'11 := (t'10 - 1)
        count := t'11
        sc'12 := t'10 != (0 : UInt8)
      if !(sc'12) then break
      let t'13 ← PMem.ldU64 ((0xba88 : UInt64) /- &hal -/ + 80)
      discard <| PMem.hal "AP_HAL::Scheduler::delay" t'13 #[(UInt16.toUInt64 ((Int16.toUInt16 (Int32.toInt16 ((20 : Int32))))))]
  return ()

def AP_BoardConfig.board_init_safety (this : UInt64) : PMem.M Unit := do
  let fp ← PMem.enter 8
  let r ← AP_BoardConfig.board_init_safety.body fp this
  PMem.leave fp
  return r

/-- C++ `AP_BoardConfig::init_safety : void ()`, `AP_BoardConfig.cpp:539-543`. -/
def AP_BoardConfig.init_safety (this : UInt64) : PMem.M Unit := do
  AP_BoardConfig.board_init_safety this
  AP_BoardConfig.board_init_debug this
  return ()

end Vehicle_lib
