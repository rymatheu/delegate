import ArduLean.Runtime.Boundary
import ArduLean.Vehicle.libraries.AP_HAL.AP_HAL
import ArduLean.Vehicle.libraries.AP_Param.AP_Param

/-!
ArduPilot `libraries/AP_Notify`. Sources: `libraries/AP_Notify/AP_Notify.cpp`.

Items of `lean/Vehicle_lib.lean` (the vehicle translation), unchanged; placed by `tools/split_modules.py` (`ArduLean/Vehicle/INDEX.md`).
-/

open FloatLib.Floats (Binary32 Binary64)

set_option linter.unusedVariables false
set_option linter.unreachableTactic false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false

namespace Vehicle_lib

/-- C++ `AP_Notify::get_singleton : AP_Notify *()`, `AP_Common.h:51-53`. -/
def AP_Notify.get_singleton  : PMem.M UInt64 := do
  let t'1 ← PMem.ldU64 (0xed68 : UInt64) /- &AP_Notify::_singleton -/
  return t'1

/-- C++ `AP_Notify::send_text : void (const char *)`, `AP_Notify.cpp:478-483`. -/
def AP_Notify.send_text (this : UInt64) (str : UInt64) : PMem.M Unit := do
  let mut str := str
  let t'1 ← PMem.strncpy (this + 23) str (51 : UInt64)
  discard <| pure (t'1)
  let t'2 := Int32.toInt8 ((0 : Int32))
  PMem.stI8 ((this + 23) + ((UInt64.toInt64 (((51 : UInt64) - (Int64.toUInt64 (Int32.toInt64 ((1 : Int32))))))) * 1).toUInt64) t'2
  let t'3 := ((← PMem.clock) / 1000).toUInt32
  PMem.stU32 (this + 76) t'3
  return ()

/-- C++ `AP_Notify::set_flight_mode_str : void (const char *)`, `AP_Notify.cpp:472-476`. -/
def AP_Notify.set_flight_mode_str (this : UInt64) (str : UInt64) : PMem.M Unit := do
  let mut str := str
  let t'1 ← PMem.strncpy (this + 80) str (5 : UInt64)
  discard <| pure (t'1)
  let t'2 := Int32.toInt8 ((0 : Int32))
  PMem.stI8 ((this + 80) + ((UInt64.toInt64 (((5 : UInt64) - (Int64.toUInt64 (Int32.toInt64 ((1 : Int32))))))) * 1).toUInt64) t'2
  return ()

/-- C++ `AP_Notify::update : void ()`, `AP_Notify.cpp:418-428`. NOT TRANSLATED (the back end rejects: no body for function d194:0x134ebf838 (NotifyDevice::update, None)): a stub. -/
def AP_Notify.update (this : UInt64) : PMem.M Unit := do
  PMem.unreached "rejected AP_Notify::update"
  return ()

/-- C++ `AP_Notify::AP_Notify : void ()`, `AP_Notify.cpp:215-222`. -/
def AP_Notify.AP_Notify (this : UInt64) : PMem.M Unit := do
  HALSITL.Semaphore.Semaphore (this + 0)
  AP_Param.AP_Param'2 (this + 8)
  AP_Param.AP_Param'2 (this + 9)
  AP_Param.AP_Param'2 (this + 10)
  AP_Param.AP_Param'2 (this + 11)
  AP_Param.AP_Param'2 (this + 12)
  AP_Param.AP_Param'2 (this + 13)
  AP_Param.AP_Param'2 (this + 16)
  AP_Param.AP_Param'2 (this + 20)
  AP_Param.AP_Param'2 (this + 21)
  AP_Param.AP_Param'2 (this + 22)
  AP_Param.setup_object_defaults this (0x5220 : UInt64) /- &AP_Notify::var_info -/
  let t'1 ← PMem.ldU64 (0xed68 : UInt64) /- &AP_Notify::_singleton -/
  if (t'1 != (0 : UInt64)) then
    pure ()
  PMem.stU64 (0xed68 : UInt64) /- &AP_Notify::_singleton -/ this
  return ()

end Vehicle_lib
