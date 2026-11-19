import ArduLean.Runtime.CFloat
import ArduLean.Estimator.libraries.AP_Math.AP_Math
import ArduLean.Estimator.libraries.AP_Param.AP_Param
import ArduLean.Estimator.libraries.AP_NavEKF.AP_NavEKF
import ArduLean.Estimator.libraries.AP_GPS.AP_GPS
import ArduLean.Estimator.libraries.AP_AHRS.AP_AHRS
import ArduLean.Estimator.World_2

/-!
ArduPilot `libraries/AP_Param`, part 2 of 3. Sources: `libraries/AP_Param/AP_ParamT.cpp`, `libraries/AP_Param/AP_Param.h`.

Items of `lean/Estimator_lib.lean` (the estimator translation), unchanged; placed by `tools/split_modules.py` (`ArduLean/Estimator/INDEX.md`).
-/

open FloatLib.Floats (Binary32 Binary64)

set_option maxRecDepth 200000
-- AP_DAL's `const log_RISH old_RISH = _RISH;` read only by WRITE_REPLAY_BLOCK_IFCHANGED, which is `(void)old`
-- without logging (HAL_LOGGING_ENABLED 0): an unused binding, as in the C++
set_option linter.unusedVariables false

namespace Estimator_lib

namespace AP_Enum_AP_NavEKF_Source_SourceXY

/-- C++ `const AP_NavEKF_Source::SourceXY AP_Enum<AP_NavEKF_Source::SourceXY>::operator const AP_NavEKF_Source::SourceXY() const`, `AP_Param/AP_Param.h:1140-1142`. -/
def op_to_AP_NavEKF_Source_SourceXY (s : State) : AP_NavEKF_Source.SourceXY := Id.run do
  return AP_NavEKF_Source.SourceXY.ofInt (Int8.toUInt8 s._value)

end AP_Enum_AP_NavEKF_Source_SourceXY

namespace AP_Enum_GPSUse

/-- C++ `const GPSUse AP_Enum<GPSUse>::operator const GPSUse() const`, `AP_Param/AP_Param.h:1140-1142`. -/
def op_to_GPSUse (s : State) : GPSUse := Id.run do
  return GPSUse.ofInt (Int8.toUInt8 s._value)

end AP_Enum_GPSUse

namespace AP_Enum_AP_AHRS_EKFType

/-- C++ `void AP_ParamTBase<signed char, 1>::set(const signed char & v)`, `AP_Param/AP_Param.h:923-925` (a member of `AP_ParamTBase<signed char, 1>`, translated for `AP_Enum<AP_AHRS::EKFType>`). -/
def set_int8_t (s : State) (v : Int8) : State := Id.run do
  let mut s := s
  s := { s with _value := v }
  return s

/-- C++ `void AP_Enum<AP_AHRS::EKFType>::set(AP_AHRS::EKFType v)`, `AP_Param/AP_Param.h:1143-1145`. -/
def set_EKFType (s : State) (v : AP_AHRS.EKFType) : State := Id.run do
  let mut s := s
  s := set_int8_t s (UInt8.toInt8 (AP_AHRS.EKFType.toInt v))
  return s

end AP_Enum_AP_AHRS_EKFType

namespace AP_Enum_AP_GPS_GPS_Type

/-- C++ `const AP_GPS::GPS_Type AP_Enum<AP_GPS::GPS_Type>::operator const AP_GPS::GPS_Type() const`, `AP_Param/AP_Param.h:1140-1142`. -/
def op_to_AP_GPS_GPS_Type (s : State) : AP_GPS.GPS_Type := Id.run do
  return AP_GPS.GPS_Type.ofInt (Int32.toUInt32 (Int8.toInt32 s._value))

end AP_Enum_AP_GPS_GPS_Type

namespace AP_Enum_AP_NavEKF_Source_SourceZ

/-- C++ `const AP_NavEKF_Source::SourceZ AP_Enum<AP_NavEKF_Source::SourceZ>::operator const AP_NavEKF_Source::SourceZ() const`, `AP_Param/AP_Param.h:1140-1142`. -/
def op_to_AP_NavEKF_Source_SourceZ (s : State) : AP_NavEKF_Source.SourceZ := Id.run do
  return AP_NavEKF_Source.SourceZ.ofInt (Int8.toUInt8 s._value)

end AP_Enum_AP_NavEKF_Source_SourceZ

namespace AP_Enum_AP_NavEKF_Source_SourceYaw

/-- C++ `const AP_NavEKF_Source::SourceYaw AP_Enum<AP_NavEKF_Source::SourceYaw>::operator const AP_NavEKF_Source::SourceYaw() const`, `AP_Param/AP_Param.h:1140-1142`. -/
def op_to_AP_NavEKF_Source_SourceYaw (s : State) : AP_NavEKF_Source.SourceYaw := Id.run do
  return AP_NavEKF_Source.SourceYaw.ofInt (Int8.toUInt8 s._value)

end AP_Enum_AP_NavEKF_Source_SourceYaw

namespace AP_ParamT_float_4

/-- C++ `void AP_ParamTBase<float, 4>::set_and_save_ifchanged(const float & v)`, `AP_Param/AP_ParamT.cpp:91-100` (a member of `AP_ParamTBase<float, 4>`, translated for `AP_ParamT<float, 4>`). -/
def set_and_save_ifchanged (s : State) (o : Outputs) (sp : String) (v : Binary32) : State × Outputs := Id.run do
  let mut s := s
  let mut o := o
  if v == s._value then
    return (s, o)
  s := set s v
  o := o.push (Output.AP_Param_save sp true)
  return (s, o)

end AP_ParamT_float_4

namespace AP_ParamT_float_4

/-- C++ `void AP_ParamTBase<float, 4>::set_and_save(const float & v)`, `AP_Param/AP_ParamT.cpp:79-83` (a member of `AP_ParamTBase<float, 4>`, translated for `AP_ParamT<float, 4>`). -/
def set_and_save (s : State) (o : Outputs) (sp : String) (v : Binary32) : State × Outputs := Id.run do
  let mut s := s
  let mut o := o
  let force : Bool := decide (Binary32.abs (s._value - v) < (Binary32.ofBits 0x34000000 /- 1.1920929E-7 -/))
  s := set s v
  o := o.push (Output.AP_Param_save sp force)
  return (s, o)

end AP_ParamT_float_4

namespace AP_ParamT_unsigned_int_3

/-- C++ `void AP_ParamTBase<unsigned int, 3>::set_and_save_ifchanged(const unsigned int & v)`, `AP_Param/AP_ParamT.cpp:91-100` (a member of `AP_ParamTBase<unsigned int, 3>`, translated for `AP_ParamT<unsigned int, 3>`). -/
def set_and_save_ifchanged (s : State) (o : Outputs) (sp : String) (v : UInt32) : State × Outputs := Id.run do
  let mut s := s
  let mut o := o
  if v == s._value then
    return (s, o)
  s := set s v
  o := o.push (Output.AP_Param_save sp true)
  return (s, o)

end AP_ParamT_unsigned_int_3

namespace AP_ParamT_signed_char_1

/-- C++ `void AP_ParamTBase<signed char, 1>::set_and_save_ifchanged(const signed char & v)`, `AP_Param/AP_ParamT.cpp:91-100` (a member of `AP_ParamTBase<signed char, 1>`, translated for `AP_ParamT<signed char, 1>`). -/
def set_and_save_ifchanged (s : State) (o : Outputs) (sp : String) (v : Int8) : State × Outputs := Id.run do
  let mut s := s
  let mut o := o
  if Int8.toInt32 v == Int8.toInt32 s._value then
    return (s, o)
  s := set s v
  o := o.push (Output.AP_Param_save sp true)
  return (s, o)

end AP_ParamT_signed_char_1

namespace AP_ParamV_Vector3_float_5

/-- C++ `void AP_ParamV<Vector3<float>, 5>::set_and_save_ifchanged(const Vector3<float> & v)`, `AP_Param/AP_ParamT.cpp:139-148`. -/
def set_and_save_ifchanged (s : State) (o : Outputs) (sp : String) (v : Vector3f.State) : State × Outputs := Id.run do
  let mut s := s
  let mut o := o
  if Vector3f.op_eq s._value v then
    return (s, o)
  s := set s v
  o := o.push (Output.AP_Param_save sp true)
  return (s, o)

end AP_ParamV_Vector3_float_5

namespace AP_ParamT_unsigned_int_3

/-- C++ `void AP_ParamTBase<unsigned int, 3>::set_and_save(const unsigned int & v)`, `AP_Param/AP_ParamT.cpp:79-83` (a member of `AP_ParamTBase<unsigned int, 3>`, translated for `AP_ParamT<unsigned int, 3>`). -/
def set_and_save (s : State) (o : Outputs) (sp : String) (v : UInt32) : State × Outputs := Id.run do
  let mut s := s
  let mut o := o
  let force : Bool := decide (Binary32.abs (UInt32.toBinary32 (s._value - v)) < (Binary32.ofBits 0x34000000 /- 1.1920929E-7 -/))
  s := set s v
  o := o.push (Output.AP_Param_save sp force)
  return (s, o)

end AP_ParamT_unsigned_int_3

namespace AP_ParamT_unsigned_int_3

/-- C++ `void AP_ParamTBase<unsigned int, 3>::set_and_notify(const unsigned int & v)`, `AP_Param/AP_ParamT.cpp:65-75` (a member of `AP_ParamTBase<unsigned int, 3>`, translated for `AP_ParamT<unsigned int, 3>`). -/
def set_and_notify (s : State) (o : Outputs) (sp : String) (v : UInt32) : State × Outputs := Id.run do
  let mut s := s
  let mut o := o
  if v != s._value then
    s := set s v
    o := o.push (Output.AP_Param_notify sp)
  return (s, o)

end AP_ParamT_unsigned_int_3

namespace AP_ParamT_signed_char_1

/-- C++ `void AP_ParamTBase<signed char, 1>::set_and_notify(const signed char & v)`, `AP_Param/AP_ParamT.cpp:65-75` (a member of `AP_ParamTBase<signed char, 1>`, translated for `AP_ParamT<signed char, 1>`). -/
def set_and_notify (s : State) (o : Outputs) (sp : String) (v : Int8) : State × Outputs := Id.run do
  let mut s := s
  let mut o := o
  if Int8.toInt32 v != Int8.toInt32 s._value then
    s := set s v
    o := o.push (Output.AP_Param_notify sp)
  return (s, o)

end AP_ParamT_signed_char_1

namespace AP_ParamV_Vector3_float_5

/-- C++ `void AP_ParamV<Vector3<float>, 5>::set_and_save(const Vector3<float> & v)`, `AP_Param/AP_ParamT.cpp:127-131`. -/
def set_and_save (s : State) (o : Outputs) (sp : String) (v : Vector3f.State) : State × Outputs := Id.run do
  let mut s := s
  let mut o := o
  let force : Bool := (Vector3f.op_ne s._value v)
  s := set s v
  o := o.push (Output.AP_Param_save sp force)
  return (s, o)

end AP_ParamV_Vector3_float_5

end Estimator_lib
