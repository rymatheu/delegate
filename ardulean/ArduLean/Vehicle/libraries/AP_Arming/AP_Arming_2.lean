import ArduLean.Runtime.Memory
import ArduLean.Vehicle.libraries.AP_Param.AP_Param
import ArduLean.Vehicle.libraries.AP_Mission.AP_Mission
import ArduLean.Vehicle.libraries.AP_Param.AP_Param_2
import ArduLean.Vehicle.libraries.AP_Mission.AP_Mission_2

/-!
ArduPilot `libraries/AP_Arming`, part 2 of 3. Sources: `libraries/AP_Arming/AP_Arming.cpp`.

Items of `lean/Vehicle_lib.lean` (the vehicle translation), unchanged; placed by `tools/split_modules.py` (`ArduLean/Vehicle/INDEX.md`).
-/

open FloatLib.Floats (Binary32 Binary64)

set_option linter.unusedVariables false
set_option linter.unreachableTactic false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false

namespace Vehicle_lib

/-- C++ `AP_Arming::terrain_database_required : bool () const`, `AP_Arming.cpp:1258-1272`. -/
def AP_Arming.terrain_database_required (this : UInt64) : PMem.M Bool := do
  let t'1 ← AP.mission
  let t'2 ← AP_Mission.contains_terrain_alt_items t'1
  if t'2 then
    return true
  return false

/-- C++ `AP_Arming::init : void ()`, `AP_Arming.cpp:230-262`. -/
def AP_Arming.init.body (fp : UInt64) (this : UInt64) : PMem.M Unit := do
  let t'1 ← AP_Param.configured (this + 12)
  if !t'1 then
    let t'2 ← AP_ParamTBase'unsigned_int_3.get (this + 12)
    let t'3 ← PMem.ldU32 t'2
    let mut skipchk_new : Int32 := UInt32.toInt32 (t'3)
    let mut idx : UInt32 := Int32.toUInt32 ((8 : Int32))
    let t'4 ← AP_Param.get_param_by_index this idx (3 : UInt32) (fp + 0)
    if t'4 then
      let t'5 ← PMem.ldI32 (fp + 0)
      if (t'5 == (0 : Int32)) then
        let t'6 := -(1 : Int32)
        skipchk_new := t'6
      else
        let t'7 ← PMem.ldI32 (fp + 0)
        if !((t'7 &&& (1 : Int32)) != (0 : Int32)) then
          let mut check_mask : UInt32 := ((((1 : UInt32) <<< (Int32.toUInt32 ((21 : Int32)))) - (Int32.toUInt32 ((1 : Int32)))) &&& (Int32.toUInt32 ((~~~(1 : Int32)))))
          let t'8 ← PMem.ldI32 (fp + 0)
          let t'9 := UInt32.toInt32 (((Int32.toUInt32 ((~~~t'8))) &&& check_mask))
          skipchk_new := t'9
        else
          skipchk_new := (0 : Int32)
    PMem.stU32 (fp + 4) (Int32.toUInt32 (skipchk_new))
    AP_ParamTBase'unsigned_int_3.set_and_save (this + 12) (fp + 4)
  return ()

def AP_Arming.init (this : UInt64) : PMem.M Unit := do
  let fp ← PMem.enter 8
  let r ← AP_Arming.init.body fp this
  PMem.leave fp
  return r

end Vehicle_lib
