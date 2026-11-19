import ArduLean.Runtime.Memory
import ArduLean.Vehicle.libraries.AP_Param.AP_Param
import ArduLean.Vehicle.libraries.AP_Param.AP_Param_2

/-!
ArduPilot `libraries/AP_GPS`. Sources: `libraries/AP_GPS/AP_GPS.cpp`.

Items of `lean/Vehicle_lib.lean` (the vehicle translation), unchanged; placed by `tools/split_modules.py` (`ArduLean/Vehicle/INDEX.md`).
-/

open FloatLib.Floats (Binary32 Binary64)

set_option linter.unusedVariables false
set_option linter.unreachableTactic false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false

namespace Vehicle_lib

/-- C++ `AP_GPS::convert_parameters : void ()`, `AP_GPS.cpp:353-397`. -/
def AP_GPS.convert_parameters.body (fp : UInt64) (this : UInt64) : PMem.M Unit := do
  let t'1 ← AP_Param.find_top_level_key_by_pointer this (fp + 0)
  if !t'1 then
    return ()
  let t'2 ← PMem.ldU16 (fp + 0)
  AP_Param.convert_old_parameters'2 t'2 (0xcce0 : UInt64) /- &AP_GPS::convert_parameters(...)::conversion_info -/ (UInt64.toUInt8 (((160 : UInt64) / (16 : UInt64)))) (Int8.toUInt8 (Int32.toInt8 ((0 : Int32))))
  return ()

def AP_GPS.convert_parameters (this : UInt64) : PMem.M Unit := do
  let fp ← PMem.enter 2
  let r ← AP_GPS.convert_parameters.body fp this
  PMem.leave fp
  return r

end Vehicle_lib
