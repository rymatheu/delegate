import ArduLean.Runtime.Boundary
import ArduLean.Vehicle.libraries.AP_Param.AP_Param

/-!
ArduPilot `libraries/AP_Vehicle`, part 1 of 2. Sources: `libraries/AP_Vehicle/AP_Vehicle.cpp`.

Items of `lean/Vehicle_lib.lean` (the vehicle translation), unchanged; placed by `tools/split_modules.py` (`ArduLean/Vehicle/INDEX.md`).
-/

open FloatLib.Floats (Binary32 Binary64)

set_option linter.unusedVariables false
set_option linter.unreachableTactic false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false

namespace Vehicle_lib

/-- C++ `AP_Vehicle::get_singleton : AP_Vehicle *()`, `AP_Vehicle.cpp:1258-1261`. -/
def AP_Vehicle.get_singleton  : PMem.M UInt64 := do
  let t'1 ← PMem.ldU64 (0xdf18 : UInt64) /- &AP_Vehicle::_singleton -/
  return t'1

/-- C++ `AP::vehicle : AP_Vehicle *()`, `AP_Vehicle.cpp:1265-1268`. -/
def AP.vehicle  : PMem.M UInt64 := do
  let t'1 ← AP_Vehicle.get_singleton
  return t'1

/-- C++ `AP_Vehicle::block_GCS_mode_change : bool (uint8_t, const uint8_t *, uint8_t) const`, `AP_Vehicle.cpp:1231-1246`. -/
def AP_Vehicle.block_GCS_mode_change (this : UInt64) (mode_num : UInt8) (mode_list : UInt64) (mode_list_length : UInt8) : PMem.M Bool := do
  let mut mode_num := mode_num
  let mut mode_list := mode_list
  let mut mode_list_length := mode_list_length
  if (mode_list == (0 : UInt64)) then
    return false
  for i'1 in [0:mode_list_length.toNat] do
    let i : UInt8 := UInt8.ofNat i'1
    let t'2 ← PMem.ldU8 (mode_list + ((UInt64.toInt64 (UInt8.toUInt64 (i))) * 1).toUInt64)
    if ((UInt32.toInt32 (UInt8.toUInt32 (t'2))) == (UInt32.toInt32 (UInt8.toUInt32 (mode_num)))) then
      let mut mask : UInt32 := ((1 : UInt32) <<< (Int32.toUInt32 ((UInt32.toInt32 (UInt8.toUInt32 (i))))))
      let t'3 ← AP_ParamT'unsigned_int_3.operator_const_unsigned_int__ (this + 6756)
      let t'4 ← PMem.ldU32 t'3
      return ((t'4 &&& mask) != (Int32.toUInt32 ((0 : Int32))))
  return false

/-- C++ `AP_Vehicle::set_likely_flying : void (bool)`, `AP_Common.h:155-160`. -/
def AP_Vehicle.set_likely_flying (this : UInt64) (b : Bool) : PMem.M Unit := do
  let mut b := b
  let mut sc'2 := b
  if sc'2 then
    let t'1 ← PMem.ldB (this + 6761)
    sc'2 := !t'1
  if sc'2 then
    let t'3 := ((← PMem.clock) / 1000).toUInt32
    PMem.stU32 (this + 6764) t'3
  PMem.stB (this + 6761) b
  return ()

/-- C++ `AP_Vehicle::get_common_scheduler_tasks : void (const AP_Scheduler::Task *&, uint8_t &)`, `AP_Vehicle.cpp:726-730`. -/
def AP_Vehicle.get_common_scheduler_tasks (this : UInt64) (tasks : UInt64) (num_tasks : UInt64) : PMem.M Unit := do
  let t'1 := (0xcc38 : UInt64) /- &AP_Vehicle::scheduler_tasks -/
  PMem.stU64 tasks t'1
  let t'2 := UInt64.toUInt8 (((128 : UInt64) / (32 : UInt64)))
  PMem.stU8 num_tasks t'2
  return ()

/-- `AP_Vehicle.set_control_channels` as a pure function of its arguments (it reads and writes no memory). -/
def AP_Vehicle.set_control_channels.pure' (this : UInt64) : Id Unit := do
  return ()

/-- C++ `AP_Vehicle::set_control_channels : void ()`, `AP_Common.h:331-?`. -/
def AP_Vehicle.set_control_channels (this : UInt64) : PMem.M Unit :=
  pure (_root_.Vehicle_lib.AP_Vehicle.set_control_channels.pure' this)

/-- C++ `AP_Vehicle::get_time_flying_ms : uint32_t () const`, `AP_Common.h:175-180`. -/
def AP_Vehicle.get_time_flying_ms (this : UInt64) : PMem.M UInt32 := do
  let t'1 ← PMem.ldB (this + 6761)
  if !t'1 then
    return Int32.toUInt32 ((0 : Int32))
  let t'2 ← PMem.ldU32 (this + 6764)
  return ((((← PMem.clock) / 1000).toUInt32) - t'2)

end Vehicle_lib
