import ArduLean.Runtime.Bridge
import ArduLean.Vehicle.libraries.AP_Param.AP_Param

/-!
ArduPilot `libraries/AP_Arming`, part 1 of 3. Sources: `libraries/AP_Arming/AP_Arming.cpp`, `libraries/AP_Arming/AP_Arming.h`.

Items of `lean/Vehicle_lib.lean` (the vehicle translation), unchanged; placed by `tools/split_modules.py` (`ArduLean/Vehicle/INDEX.md`).
-/

open FloatLib.Floats (Binary32 Binary64)

set_option linter.unusedVariables false
set_option linter.unreachableTactic false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false

namespace Vehicle_lib

/-- C++ `AP_Arming::arming_required : AP_Arming::Required () const`, `AP_Arming.cpp:2051-2062`. -/
def AP_Arming.arming_required (this : UInt64) : PMem.M Int32 := do
  let t'1 ← AP_Enum'AP_Arming_Required.operator_const_AP_Arming.Required (this + 8)
  return t'1

/-- C++ `AP_Arming::is_armed : bool () const`, `AP_Arming.cpp:309-312`. -/
def AP_Arming.is_armed (this : UInt64) : PMem.M Bool := do
  let t'1 ← PMem.ldB (this + 35)
  let mut sc'3 := t'1
  if !sc'3 then
    let t'2 ← AP_Arming.arming_required this
    sc'3 := (t'2 == (0 : Int32))
  return sc'3

/-- C++ `AP_Arming::get_singleton : AP_Arming *()`, `AP_Arming.cpp:2220-2223`. -/
def AP_Arming.get_singleton  : PMem.M UInt64 := do
  let t'1 ← PMem.ldU64 (0xce40 : UInt64) /- &AP_Arming::_singleton -/
  return t'1

/-- C++ `AP::arming : AP_Arming &()`, `AP_Arming.cpp:2227-2230`. -/
def AP.arming  : PMem.M UInt64 := do
  let t'1 ← AP_Arming.get_singleton
  return t'1

/-- `AP_Arming.method_is_GCS` as a pure function of its arguments (it reads and writes no memory). -/
def AP_Arming.method_is_GCS.pure' (method : Int32) : Id Bool := do
  let mut method := method
  return ((method == (1 : Int32)) || (method == (35 : Int32)))

/-- C++ `AP_Arming::method_is_GCS : bool (Method)`, `AP_Arming.h:172-174`. -/
def AP_Arming.method_is_GCS (method : Int32) : PMem.M Bool :=
  pure (_root_.Vehicle_lib.AP_Arming.method_is_GCS.pure' method)

/-- C++ `AP_Arming::get_rudder_arming_type : RudderArming () const`, `AP_Common.h:140-?`. -/
def AP_Arming.get_rudder_arming_type (this : UInt64) : PMem.M Int32 := do
  let t'1 ← AP_ParamTBase'signed_char_1.get (this + 20)
  let t'2 ← PMem.ldI8 t'1
  return Int8.toInt32 (t'2)

/-- C++ `AP_Arming::option_enabled : bool (Option) const`, `AP_Common.h:166-168`. -/
def AP_Arming.option_enabled (this : UInt64) (option : Int32) : PMem.M Bool := do
  let mut option := option
  let t'1 ← AP_ParamT'unsigned_int_3.operator_const_unsigned_int__ (this + 28)
  let t'2 ← PMem.ldU32 t'1
  return ((t'2 &&& (Int32.toUInt32 (option))) != (Int32.toUInt32 ((0 : Int32))))

/-- C++ `AP_Arming::check_enabled : bool (const AP_Arming::Check) const`, `AP_Arming.cpp:329-332`. -/
def AP_Arming.check_enabled (this : UInt64) (check : Int32) : PMem.M Bool := do
  let mut check := check
  let t'1 ← AP_ParamT'unsigned_int_3.operator_const_unsigned_int__ (this + 12)
  let t'2 ← PMem.ldU32 t'1
  return ((t'2 &&& (Int32.toUInt32 (check))) == (Int32.toUInt32 ((0 : Int32))))

/-- C++ `AP_Arming::get_enabled_checks : uint32_t () const`, `AP_Arming.cpp:322-327`. -/
def AP_Arming.get_enabled_checks (this : UInt64) : PMem.M UInt32 := do
  let mut check_mask : UInt32 := (((Int32.toUInt32 ((2097152 : Int32))) - (Int32.toUInt32 ((1 : Int32)))) &&& (Int32.toUInt32 ((~~~(1 : Int32)))))
  let t'1 ← AP_ParamT'unsigned_int_3.operator_const_unsigned_int__ (this + 12)
  let t'2 ← PMem.ldU32 t'1
  return ((~~~t'2) &&& check_mask)

/-- C++ `AP_Arming::should_skip_all_checks : bool () const`, `AP_Common.h:119-?`. -/
def AP_Arming.should_skip_all_checks (this : UInt64) : PMem.M Bool := do
  let t'1 ← AP_Arming.get_enabled_checks this
  return (t'1 == (Int32.toUInt32 ((0 : Int32))))

/-- C++ `AP_Arming::ins_accels_consistent : bool (const AP_InertialSensor &)`, `AP_Arming.cpp:457-481`. -/
def AP_Arming.ins_accels_consistent (this : UInt64) (ins : UInt64) : PMem.M Bool := do
  let mut now : UInt32 := ((← PMem.clock) / 1000).toUInt32
  let t'1 ← AP_ParamT'float_4.operator_const_float__'1 (this + 16)
  let t'2 ← PMem.ldF32 t'1
  let t'3 ← VehicleBridge.AP_InertialSensor.accels_consistent'1 ins t'2
  if !t'3 then
    let t'4 := Int32.toUInt32 ((0 : Int32))
    PMem.stU32 (this + 36) t'4
    return false
  let t'5 ← PMem.ldU32 (this + 36)
  if (t'5 == (Int32.toUInt32 ((0 : Int32)))) then
    PMem.stU32 (this + 36) now
  let t'6 ← VehicleBridge.AP_InertialSensor.get_accel_count'0 ins
  let mut sc'8 := (decide ((UInt32.toInt32 (UInt8.toUInt32 (t'6))) > (1 : Int32)))
  if sc'8 then
    let t'7 ← PMem.ldU32 (this + 36)
    sc'8 := (decide ((now - t'7) < (Int32.toUInt32 ((10000 : Int32)))))
  if sc'8 then
    return false
  return true

/-- C++ `AP_Arming::ins_gyros_consistent : bool (const AP_InertialSensor &)`, `AP_Arming.cpp:483-508`. -/
def AP_Arming.ins_gyros_consistent (this : UInt64) (ins : UInt64) : PMem.M Bool := do
  let mut now : UInt32 := ((← PMem.clock) / 1000).toUInt32
  let t'1 ← VehicleBridge.AP_InertialSensor.gyros_consistent'1 ins (Int8.toUInt8 (Int32.toInt8 ((5 : Int32))))
  if !t'1 then
    let t'2 := Int32.toUInt32 ((0 : Int32))
    PMem.stU32 (this + 40) t'2
    return false
  let t'3 ← PMem.ldU32 (this + 40)
  if (t'3 == (Int32.toUInt32 ((0 : Int32)))) then
    PMem.stU32 (this + 40) now
  let t'4 ← VehicleBridge.AP_InertialSensor.get_gyro_count'0 ins
  let mut sc'6 := (decide ((UInt32.toInt32 (UInt8.toUInt32 (t'4))) > (1 : Int32)))
  if sc'6 then
    let t'5 ← PMem.ldU32 (this + 40)
    sc'6 := (decide ((now - t'5) < (Int32.toUInt32 ((10000 : Int32)))))
  if sc'6 then
    return false
  return true

/-- C++ `AP_Arming::arm_time_us : uint64_t () const`, `AP_Common.h:112-?`. -/
def AP_Arming.arm_time_us (this : UInt64) : PMem.M UInt64 := do
  let t'1 ← AP_Arming.is_armed this
  let mut c'2 : UInt64 := default
  if t'1 then
    let t'3 ← PMem.ldU64 (this + 56)
    c'2 := t'3
  else
    c'2 := Int64.toUInt64 (Int32.toInt64 ((0 : Int32)))
  return c'2

/-- C++ `AP_Arming::AP_Arming : void ()`, `AP_Arming.cpp:220-228`. -/
def AP_Arming.AP_Arming (this : UInt64) : PMem.M Unit := do
  AP_Enum'AP_Arming_Required.AP_Enum (this + 8)
  AP_Param.AP_Param'2 (this + 12)
  AP_Param.AP_Param'2 (this + 16)
  AP_Param.AP_Param'2 (this + 20)
  AP_Param.AP_Param'2 (this + 24)
  AP_Param.AP_Param'2 (this + 28)
  AP_Param.AP_Param'2 (this + 32)
  AP_Enum'AP_Arming_RequireLocation.AP_Enum (this + 34)
  PMem.stI32 (this + 44) (100 : Int32)
  PMem.stI32 (this + 48) (100 : Int32)
  let t'1 ← PMem.ldU64 (0xce40 : UInt64) /- &AP_Arming::_singleton -/
  if (t'1 != 0) then
    pure ()
  PMem.stU64 (0xce40 : UInt64) /- &AP_Arming::_singleton -/ this
  AP_Param.setup_object_defaults this (0x2168 : UInt64) /- &AP_Arming::var_info -/
  return ()

end Vehicle_lib
