import ArduLean.Runtime.Memory
import ArduLean.Vehicle.libraries.AP_HAL.AP_HAL
import ArduLean.Vehicle.libraries.AP_Param.AP_Param
import ArduLean.Vehicle.libraries.AP_Common.AP_Common

/-!
ArduPilot `libraries/AP_CANManager`. Sources: `libraries/AP_CANManager/AP_CANManager.cpp`.

Items of `lean/Vehicle_lib.lean` (the vehicle translation), unchanged; placed by `tools/split_modules.py` (`ArduLean/Vehicle/INDEX.md`).
-/

open FloatLib.Floats (Binary32 Binary64)

set_option linter.unusedVariables false
set_option linter.unreachableTactic false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false

namespace Vehicle_lib

/-- C++ `AP::can : AP_CANManager &()`, `AP_CANManager.cpp:399-402`. -/
def AP.can  : PMem.M UInt64 := do
  let t'1 ← AP_CANManager.get_singleton
  return t'1

/-- C++ `AP_CANManager::AP_CANManager : void ()`, `AP_CANManager.cpp:105-112`. -/
def AP_CANManager.AP_CANManager (this : UInt64) : PMem.M Unit := do
  AP_CANManager.CANIface_Params.CANIface_Params ((this + 0) + 0)
  AP_CANManager.CANIface_Params.CANIface_Params ((this + 0) + 16)
  AP_CANManager.CANDriver_Params.CANDriver_Params ((this + 48) + 0)
  AP_CANManager.CANDriver_Params.CANDriver_Params ((this + 48) + 24)
  AP_Param.AP_Param'2 (this + 98)
  HALSITL.Semaphore.Semaphore (this + 104)
  AP_Param.setup_object_defaults this (0x3e48 : UInt64) /- &AP_CANManager::var_info -/
  let t'1 ← PMem.ldU64 (0x134b8 : UInt64) /- &AP_CANManager::_singleton -/
  if (t'1 != (0 : UInt64)) then
    pure ()
  PMem.stU64 (0x134b8 : UInt64) /- &AP_CANManager::_singleton -/ this
  return ()

end Vehicle_lib
