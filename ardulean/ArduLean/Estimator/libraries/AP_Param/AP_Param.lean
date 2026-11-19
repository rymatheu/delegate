import ArduLean.Runtime.CFloat
import ArduLean.Estimator.libraries.AP_Math.AP_Math

/-!
ArduPilot `libraries/AP_Param`, part 1 of 3. Sources: `libraries/AP_Param/AP_Param.h`, `libraries/AP_Param/AP_ParamT.cpp`.

Items of `lean/Estimator_lib.lean` (the estimator translation), unchanged; placed by `tools/split_modules.py` (`ArduLean/Estimator/INDEX.md`).
-/

open FloatLib.Floats (Binary32 Binary64)

set_option maxRecDepth 200000
-- AP_DAL's `const log_RISH old_RISH = _RISH;` read only by WRITE_REPLAY_BLOCK_IFCHANGED, which is `(void)old`
-- without logging (HAL_LOGGING_ENABLED 0): an unused binding, as in the C++
set_option linter.unusedVariables false

namespace Estimator_lib

namespace AP_ParamT_signed_char_1

/-- State of C++ `AP_ParamT<signed char, 1>` (`AP_Param/AP_Param.h:961-981`): its data members; base classes flattened, base first: `AP_ParamTBase<signed char, 1>`, `AP_Param`. -/
structure State where
  /-- `signed char _value` of `AP_ParamTBase<signed char, 1>` (`AP_Param/AP_Param.h:958`). -/
  _value : Int8 := (0 : Int8)
deriving Inhabited

end AP_ParamT_signed_char_1

namespace AP_ParamT_unsigned_short_2

/-- State of C++ `AP_ParamT<unsigned short, 2>` (`AP_Param/AP_Param.h:961-981`): its data members; base classes flattened, base first: `AP_ParamTBase<unsigned short, 2>`, `AP_Param`. -/
structure State where
  /-- `unsigned short _value` of `AP_ParamTBase<unsigned short, 2>` (`AP_Param/AP_Param.h:958`). -/
  _value : UInt16 := (0 : UInt16)
deriving Inhabited

end AP_ParamT_unsigned_short_2

namespace AP_ParamT_float_4

/-- State of C++ `AP_ParamT<float, 4>` (`AP_Param/AP_Param.h:983-1040`): its data members; base classes flattened, base first: `AP_ParamTBase<float, 4>`, `AP_Param`. -/
structure State where
  /-- `float _value` of `AP_ParamTBase<float, 4>` (`AP_Param/AP_Param.h:958`). -/
  _value : Binary32 := (Binary32.ofBits 0x00000000 /- 0.0 -/)
deriving Inhabited

end AP_ParamT_float_4

namespace AP_Enum_GPSUse

/-- State of C++ `AP_Enum<GPSUse>` (`AP_Param/AP_Param.h:1136-1149`): its data members; base classes flattened, base first: `AP_ParamT<signed char, 1>`, `AP_ParamTBase<signed char, 1>`, `AP_Param`. -/
structure State where
  /-- `signed char _value` of `AP_ParamTBase<signed char, 1>` (`AP_Param/AP_Param.h:958`). -/
  _value : Int8 := (0 : Int8)
deriving Inhabited

end AP_Enum_GPSUse

namespace AP_Enum_AP_AHRS_EKFType

/-- State of C++ `AP_Enum<AP_AHRS::EKFType>` (`AP_Param/AP_Param.h:1136-1149`): its data members; base classes flattened, base first: `AP_ParamT<signed char, 1>`, `AP_ParamTBase<signed char, 1>`, `AP_Param`. -/
structure State where
  /-- `signed char _value` of `AP_ParamTBase<signed char, 1>` (`AP_Param/AP_Param.h:958`). -/
  _value : Int8 := (0 : Int8)
deriving Inhabited

end AP_Enum_AP_AHRS_EKFType

namespace AP_ParamV_Vector3_float_5

/-- State of C++ `AP_ParamV<Vector3<float>, 5>` (`AP_Param/AP_ParamT.cpp:150`): its data members; base classes flattened, base first: `AP_Param`. -/
structure State where
  /-- `Vector3<float> _value` of `AP_ParamV<Vector3<float>, 5>` (`AP_Param/AP_Param.h:1097`). -/
  _value : Vector3f.State := {}
deriving Inhabited

end AP_ParamV_Vector3_float_5

namespace AP_Enum_AP_NavEKF_Source_SourceXY

/-- State of C++ `AP_Enum<AP_NavEKF_Source::SourceXY>` (`AP_Param/AP_Param.h:1136-1149`): its data members; base classes flattened, base first: `AP_ParamT<signed char, 1>`, `AP_ParamTBase<signed char, 1>`, `AP_Param`. -/
structure State where
  /-- `signed char _value` of `AP_ParamTBase<signed char, 1>` (`AP_Param/AP_Param.h:958`). -/
  _value : Int8 := (0 : Int8)
deriving Inhabited

end AP_Enum_AP_NavEKF_Source_SourceXY

namespace AP_Enum_AP_NavEKF_Source_SourceZ

/-- State of C++ `AP_Enum<AP_NavEKF_Source::SourceZ>` (`AP_Param/AP_Param.h:1136-1149`): its data members; base classes flattened, base first: `AP_ParamT<signed char, 1>`, `AP_ParamTBase<signed char, 1>`, `AP_Param`. -/
structure State where
  /-- `signed char _value` of `AP_ParamTBase<signed char, 1>` (`AP_Param/AP_Param.h:958`). -/
  _value : Int8 := (0 : Int8)
deriving Inhabited

end AP_Enum_AP_NavEKF_Source_SourceZ

namespace AP_Enum_AP_NavEKF_Source_SourceYaw

/-- State of C++ `AP_Enum<AP_NavEKF_Source::SourceYaw>` (`AP_Param/AP_Param.h:1136-1149`): its data members; base classes flattened, base first: `AP_ParamT<signed char, 1>`, `AP_ParamTBase<signed char, 1>`, `AP_Param`. -/
structure State where
  /-- `signed char _value` of `AP_ParamTBase<signed char, 1>` (`AP_Param/AP_Param.h:958`). -/
  _value : Int8 := (0 : Int8)
deriving Inhabited

end AP_Enum_AP_NavEKF_Source_SourceYaw

namespace AP_ParamT_short_2

/-- State of C++ `AP_ParamT<short, 2>` (`AP_Param/AP_Param.h:961-981`): its data members; base classes flattened, base first: `AP_ParamTBase<short, 2>`, `AP_Param`. -/
structure State where
  /-- `short _value` of `AP_ParamTBase<short, 2>` (`AP_Param/AP_Param.h:958`). -/
  _value : Int16 := (0 : Int16)
deriving Inhabited

end AP_ParamT_short_2

namespace AP_ParamT_unsigned_char_1

/-- State of C++ `AP_ParamT<unsigned char, 1>` (`AP_Param/AP_Param.h:961-981`): its data members; base classes flattened, base first: `AP_ParamTBase<unsigned char, 1>`, `AP_Param`. -/
structure State where
  /-- `unsigned char _value` of `AP_ParamTBase<unsigned char, 1>` (`AP_Param/AP_Param.h:958`). -/
  _value : UInt8 := (0 : UInt8)
deriving Inhabited

end AP_ParamT_unsigned_char_1

namespace AP_ParamT_unsigned_int_3

/-- State of C++ `AP_ParamT<unsigned int, 3>` (`AP_Param/AP_Param.h:961-981`): its data members; base classes flattened, base first: `AP_ParamTBase<unsigned int, 3>`, `AP_Param`. -/
structure State where
  /-- `unsigned int _value` of `AP_ParamTBase<unsigned int, 3>` (`AP_Param/AP_Param.h:958`). -/
  _value : UInt32 := (0 : UInt32)
deriving Inhabited

end AP_ParamT_unsigned_int_3

namespace AP_Enum_NavEKF3_LogLevel

/-- State of C++ `AP_Enum<NavEKF3::LogLevel>` (`AP_Param/AP_Param.h:1136-1149`): its data members; base classes flattened, base first: `AP_ParamT<signed char, 1>`, `AP_ParamTBase<signed char, 1>`, `AP_Param`. -/
structure State where
  /-- `signed char _value` of `AP_ParamTBase<signed char, 1>` (`AP_Param/AP_Param.h:958`). -/
  _value : Int8 := (0 : Int8)
deriving Inhabited

end AP_Enum_NavEKF3_LogLevel

namespace AP_Enum_Compass_LearnType

/-- State of C++ `AP_Enum<Compass::LearnType>` (`AP_Param/AP_Param.h:1136-1149`): its data members; base classes flattened, base first: `AP_ParamT<signed char, 1>`, `AP_ParamTBase<signed char, 1>`, `AP_Param`. -/
structure State where
  /-- `signed char _value` of `AP_ParamTBase<signed char, 1>` (`AP_Param/AP_Param.h:958`). -/
  _value : Int8 := (0 : Int8)
deriving Inhabited

end AP_Enum_Compass_LearnType

namespace AP_Enum_AP_GPS_GPS_Type

/-- State of C++ `AP_Enum<AP_GPS::GPS_Type>` (`AP_Param/AP_Param.h:1136-1149`): its data members; base classes flattened, base first: `AP_ParamT<signed char, 1>`, `AP_ParamTBase<signed char, 1>`, `AP_Param`. -/
structure State where
  /-- `signed char _value` of `AP_ParamTBase<signed char, 1>` (`AP_Param/AP_Param.h:958`). -/
  _value : Int8 := (0 : Int8)
deriving Inhabited

end AP_Enum_AP_GPS_GPS_Type

namespace AP_Enum_AP_GPS_SBAS_Mode

/-- State of C++ `AP_Enum<AP_GPS::SBAS_Mode>` (`AP_Param/AP_Param.h:1136-1149`): its data members; base classes flattened, base first: `AP_ParamT<signed char, 1>`, `AP_ParamTBase<signed char, 1>`, `AP_Param`. -/
structure State where
  /-- `signed char _value` of `AP_ParamTBase<signed char, 1>` (`AP_Param/AP_Param.h:958`). -/
  _value : Int8 := (0 : Int8)
deriving Inhabited

end AP_Enum_AP_GPS_SBAS_Mode

namespace AP_ParamT_int_3

/-- State of C++ `AP_ParamT<int, 3>` (`AP_Param/AP_Param.h:961-981`): its data members; base classes flattened, base first: `AP_ParamTBase<int, 3>`, `AP_Param`. -/
structure State where
  /-- `int _value` of `AP_ParamTBase<int, 3>` (`AP_Param/AP_Param.h:958`). -/
  _value : Int32 := (0 : Int32)
deriving Inhabited

end AP_ParamT_int_3

namespace AP_ParamT_float_4

/-- C++ `void AP_ParamTBase<float, 4>::set(const float & v)`, `AP_Param/AP_Param.h:923-925` (a member of `AP_ParamTBase<float, 4>`, translated for `AP_ParamT<float, 4>`). -/
def set (s : State) (v : Binary32) : State := Id.run do
  let mut s := s
  s := { s with _value := v }
  return s

end AP_ParamT_float_4

namespace AP_ParamT_signed_char_1

/-- C++ `const signed char & AP_ParamTBase<signed char, 1>::get() const`, `AP_Param/AP_Param.h:917-919` (a member of `AP_ParamTBase<signed char, 1>`, translated for `AP_ParamT<signed char, 1>`). -/
def get_void (s : State) : Int8 := Id.run do
  return s._value

end AP_ParamT_signed_char_1

namespace AP_ParamV_Vector3_float_5

/-- C++ `const Vector3<float> & AP_ParamV<Vector3<float>, 5>::get() const`, `AP_Param/AP_Param.h:1059-1061`. -/
def get_void (s : State) : Vector3f.State := Id.run do
  return s._value

end AP_ParamV_Vector3_float_5

namespace AP_Enum_AP_AHRS_EKFType

/-- C++ `const signed char & AP_ParamTBase<signed char, 1>::get() const`, `AP_Param/AP_Param.h:917-919` (a member of `AP_ParamTBase<signed char, 1>`, translated for `AP_Enum<AP_AHRS::EKFType>`). -/
def get_void (s : State) : Int8 := Id.run do
  return s._value

end AP_Enum_AP_AHRS_EKFType

namespace AP_ParamT_unsigned_short_2

/-- C++ `const unsigned short & AP_ParamT<unsigned short, 2>::operator const unsigned short &() const`, `AP_Param/AP_Param.h:978-980`. -/
def op_to_unsigned_short (s : State) : UInt16 := Id.run do
  return s._value

end AP_ParamT_unsigned_short_2

namespace AP_ParamT_signed_char_1

/-- C++ `const signed char & AP_ParamT<signed char, 1>::operator const signed char &() const`, `AP_Param/AP_Param.h:978-980`. -/
def op_to_signed_char (s : State) : Int8 := Id.run do
  return s._value

end AP_ParamT_signed_char_1

namespace AP_ParamT_unsigned_short_2

/-- C++ `const unsigned short & AP_ParamTBase<unsigned short, 2>::get() const`, `AP_Param/AP_Param.h:917-919` (a member of `AP_ParamTBase<unsigned short, 2>`, translated for `AP_ParamT<unsigned short, 2>`). -/
def get_void (s : State) : UInt16 := Id.run do
  return s._value

end AP_ParamT_unsigned_short_2

namespace AP_ParamT_signed_char_1

/-- C++ `void AP_ParamTBase<signed char, 1>::set_enable(const signed char & v)`, `AP_Param/AP_ParamT.cpp:33-41` (a member of `AP_ParamTBase<signed char, 1>`, translated for `AP_ParamT<signed char, 1>`). -/
def set_enable (s : State) (v : Int8) : State := Id.run do
  let mut s := s
  if Int8.toInt32 v != Int8.toInt32 s._value then
    pure ()  -- C++ `AP_Param::invalidate_count(...)`: left out (--drop)
  s := { s with _value := v }
  return s

end AP_ParamT_signed_char_1

namespace AP_ParamT_float_4

/-- C++ `const float & AP_ParamT<float, 4>::operator const float &() const`, `AP_Param/AP_Param.h:1006-1008`. -/
def op_to_float (s : State) : Binary32 := Id.run do
  return s._value

end AP_ParamT_float_4

namespace AP_ParamT_unsigned_char_1

/-- C++ `const unsigned char & AP_ParamT<unsigned char, 1>::operator const unsigned char &() const`, `AP_Param/AP_Param.h:978-980`. -/
def op_to_unsigned_char (s : State) : UInt8 := Id.run do
  return s._value

end AP_ParamT_unsigned_char_1

namespace AP_ParamV_Vector3_float_5

/-- C++ `const Vector3<float> & AP_ParamV<Vector3<float>, 5>::operator const Vector3<float> &() const`, `AP_Param/AP_Param.h:1092-1094`. -/
def op_to_Vector3_float (s : State) : Vector3f.State := Id.run do
  return s._value

end AP_ParamV_Vector3_float_5

namespace AP_ParamT_short_2

/-- C++ `const short & AP_ParamT<short, 2>::operator const short &() const`, `AP_Param/AP_Param.h:978-980`. -/
def op_to_short (s : State) : Int16 := Id.run do
  return s._value

end AP_ParamT_short_2

namespace AP_ParamT_float_4

/-- C++ `const float & AP_ParamTBase<float, 4>::get() const`, `AP_Param/AP_Param.h:917-919` (a member of `AP_ParamTBase<float, 4>`, translated for `AP_ParamT<float, 4>`). -/
def get_void (s : State) : Binary32 := Id.run do
  return s._value

end AP_ParamT_float_4

namespace AP_Enum_AP_NavEKF_Source_SourceYaw

/-- C++ `const signed char & AP_ParamTBase<signed char, 1>::get() const`, `AP_Param/AP_Param.h:917-919` (a member of `AP_ParamTBase<signed char, 1>`, translated for `AP_Enum<AP_NavEKF_Source::SourceYaw>`). -/
def get_void (s : State) : Int8 := Id.run do
  return s._value

end AP_Enum_AP_NavEKF_Source_SourceYaw

namespace AP_ParamT_unsigned_int_3

/-- C++ `const unsigned int & AP_ParamT<unsigned int, 3>::operator const unsigned int &() const`, `AP_Param/AP_Param.h:978-980`. -/
def op_to_unsigned_int (s : State) : UInt32 := Id.run do
  return s._value

end AP_ParamT_unsigned_int_3

namespace AP_ParamT_float_4

/-- C++ `double AP_ParamT<float, 4>::operator double() const`, `AP_Param/AP_Param.h:1014-1016`. -/
def op_to_double (s : State) : Binary64 := Id.run do
  return Binary32.toBinary64 s._value

end AP_ParamT_float_4

namespace AP_ParamT_signed_char_1

/-- C++ `void AP_ParamTBase<signed char, 1>::set(const signed char & v)`, `AP_Param/AP_Param.h:923-925` (a member of `AP_ParamTBase<signed char, 1>`, translated for `AP_ParamT<signed char, 1>`). -/
def set (s : State) (v : Int8) : State := Id.run do
  let mut s := s
  s := { s with _value := v }
  return s

end AP_ParamT_signed_char_1

namespace AP_ParamT_unsigned_char_1

/-- C++ `void AP_ParamTBase<unsigned char, 1>::set(const unsigned char & v)`, `AP_Param/AP_Param.h:923-925` (a member of `AP_ParamTBase<unsigned char, 1>`, translated for `AP_ParamT<unsigned char, 1>`). -/
def set (s : State) (v : UInt8) : State := Id.run do
  let mut s := s
  s := { s with _value := v }
  return s

/-- C++ `void AP_ParamTBase<unsigned char, 1>::set_and_default(const unsigned char & v)`, `AP_Param/AP_ParamT.cpp:56-61` (a member of `AP_ParamTBase<unsigned char, 1>`, translated for `AP_ParamT<unsigned char, 1>`). -/
def set_and_default (s : State) (v : UInt8) : State := Id.run do
  let mut s := s
  pure ()  -- C++ `AP_Param::add_default(...)`: left out (--drop)
  s := set s v
  return s

/-- C++ `const unsigned char & AP_ParamTBase<unsigned char, 1>::get() const`, `AP_Param/AP_Param.h:917-919` (a member of `AP_ParamTBase<unsigned char, 1>`, translated for `AP_ParamT<unsigned char, 1>`). -/
def get_void (s : State) : UInt8 := Id.run do
  return s._value

end AP_ParamT_unsigned_char_1

namespace AP_ParamT_float_4

/-- C++ `float AP_ParamT<float, 4>::operator-() const`, `AP_Param/AP_Param.h:1022`. -/
def op_sub_void (s : State) : Binary32 := Id.run do
  return -s._value

end AP_ParamT_float_4

namespace AP_ParamV_Vector3_float_5

/-- C++ `void AP_ParamV<Vector3<float>, 5>::set(const Vector3<float> & v)`, `AP_Param/AP_Param.h:1065-1067`. -/
def set (s : State) (v : Vector3f.State) : State := Id.run do
  let mut s := s
  s := { s with _value := v }
  return s

end AP_ParamV_Vector3_float_5

namespace AP_Enum_AP_NavEKF_Source_SourceXY

/-- C++ `const signed char & AP_ParamTBase<signed char, 1>::get() const`, `AP_Param/AP_Param.h:917-919` (a member of `AP_ParamTBase<signed char, 1>`, translated for `AP_Enum<AP_NavEKF_Source::SourceXY>`). -/
def get_void (s : State) : Int8 := Id.run do
  return s._value

end AP_Enum_AP_NavEKF_Source_SourceXY

namespace AP_Enum_AP_NavEKF_Source_SourceZ

/-- C++ `const signed char & AP_ParamTBase<signed char, 1>::get() const`, `AP_Param/AP_Param.h:917-919` (a member of `AP_ParamTBase<signed char, 1>`, translated for `AP_Enum<AP_NavEKF_Source::SourceZ>`). -/
def get_void (s : State) : Int8 := Id.run do
  return s._value

end AP_Enum_AP_NavEKF_Source_SourceZ

namespace AP_Enum_AP_AHRS_EKFType

/-- C++ `const signed char & AP_ParamT<signed char, 1>::operator const signed char &() const`, `AP_Param/AP_Param.h:978-980` (a member of `AP_ParamT<signed char, 1>`, translated for `AP_Enum<AP_AHRS::EKFType>`). -/
def op_to_signed_char (s : State) : Int8 := Id.run do
  return s._value

end AP_Enum_AP_AHRS_EKFType

namespace AP_ParamT_unsigned_int_3

/-- C++ `void AP_ParamTBase<unsigned int, 3>::set(const unsigned int & v)`, `AP_Param/AP_Param.h:923-925` (a member of `AP_ParamTBase<unsigned int, 3>`, translated for `AP_ParamT<unsigned int, 3>`). -/
def set (s : State) (v : UInt32) : State := Id.run do
  let mut s := s
  s := { s with _value := v }
  return s

end AP_ParamT_unsigned_int_3

namespace AP_ParamT_short_2

/-- C++ `void AP_ParamTBase<short, 2>::set(const short & v)`, `AP_Param/AP_Param.h:923-925` (a member of `AP_ParamTBase<short, 2>`, translated for `AP_ParamT<short, 2>`). -/
def set (s : State) (v : Int16) : State := Id.run do
  let mut s := s
  s := { s with _value := v }
  return s

end AP_ParamT_short_2

namespace AP_ParamT_int_3

/-- C++ `void AP_ParamTBase<int, 3>::set(const int & v)`, `AP_Param/AP_Param.h:923-925` (a member of `AP_ParamTBase<int, 3>`, translated for `AP_ParamT<int, 3>`). -/
def set (s : State) (v : Int32) : State := Id.run do
  let mut s := s
  s := { s with _value := v }
  return s

end AP_ParamT_int_3

end Estimator_lib
