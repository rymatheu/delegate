import ArduLean.Runtime.Memory
import ArduLean.Vehicle.libraries.AP_Param.AP_Param
import ArduLean.Vehicle.libraries.AP_Common.AP_Common

/-!
ArduPilot `libraries/AP_RCMapper`. Sources: `libraries/AP_RCMapper/AP_RCMapper.cpp`.

Items of `lean/Vehicle_lib.lean` (the vehicle translation), unchanged; placed by `tools/split_modules.py` (`ArduLean/Vehicle/INDEX.md`).
-/

open FloatLib.Floats (Binary32 Binary64)

set_option linter.unusedVariables false
set_option linter.unreachableTactic false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false

namespace Vehicle_lib

/-- C++ `AP::rcmap : RCMapper *()`, `AP_RCMapper.cpp:79-81`. -/
def AP.rcmap  : PMem.M UInt64 := do
  let t'1 ← RCMapper.get_singleton
  return t'1

/-- C++ `RCMapper::RCMapper : void ()`, `AP_RCMapper.cpp:70-77`. -/
def RCMapper.RCMapper (this : UInt64) : PMem.M Unit := do
  AP_Param.AP_Param'2 (this + 0)
  AP_Param.AP_Param'2 (this + 1)
  AP_Param.AP_Param'2 (this + 2)
  AP_Param.AP_Param'2 (this + 3)
  AP_Param.AP_Param'2 (this + 4)
  AP_Param.AP_Param'2 (this + 5)
  let t'1 ← PMem.ldU64 (0x12ee8 : UInt64) /- &RCMapper::_singleton -/
  if (t'1 != (0 : UInt64)) then
    pure ()
  AP_Param.setup_object_defaults this (0x4548 : UInt64) /- &RCMapper::var_info -/
  PMem.stU64 (0x12ee8 : UInt64) /- &RCMapper::_singleton -/ this
  return ()

end Vehicle_lib
