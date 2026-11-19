import ArduLean.Runtime.CFloat
import ArduLean.Estimator.libraries.AP_Math.AP_Math
import ArduLean.Estimator.libraries.AP_Param.AP_Param
import ArduLean.Estimator.libraries.AP_Baro.AP_Baro

/-!
ArduPilot `libraries/AP_Math`, part 2 of 3. Sources: `libraries/AP_Math/AP_Math.h`, `libraries/AP_Math/vectorN.h`.

Items of `lean/Estimator_lib.lean` (the estimator translation), unchanged; placed by `tools/split_modules.py` (`ArduLean/Estimator/INDEX.md`).
-/

open FloatLib.Floats (Binary32 Binary64)

set_option maxRecDepth 200000
-- AP_DAL's `const log_RISH old_RISH = _RISH;` read only by WRITE_REPLAY_BLOCK_IFCHANGED, which is `(void)old`
-- without logging (HAL_LOGGING_ENABLED 0): an unused binding, as in the C++
set_option linter.unusedVariables false

namespace Estimator_lib

namespace VectorN_AP_Baro_SITL_readings_baro_50

/-- State of C++ `VectorN<AP_Baro_SITL::readings_baro, 50>` (`AP_Math/vectorN.h:33-176`): its data members. -/
structure State where
  /-- `AP_Baro_SITL::readings_baro _v[50]` of `VectorN<AP_Baro_SITL::readings_baro, 50>` (`AP_Math/vectorN.h:175`). -/
  _v : Array AP_Baro_SITL.readings_baro := Array.replicate 50 {}
deriving Inhabited

/-- C++ `VectorN<AP_Baro_SITL::readings_baro, 50>::VectorN()`, `AP_Math/vectorN.h:38-42`. -/
def init_void : State := Id.run do
  let mut s : State := {}
  for i' in [0:50] do
    let i : Int32 := Nat.toInt32 i'
    s := { s with _v := s._v.set! (Int32.toNatClampNeg i) ({ time := (0 : UInt32), data := (Binary32.ofBits 0x00000000 /- 0.0 -/) }) }
  return s

end VectorN_AP_Baro_SITL_readings_baro_50

/-- C++ `auto MAX(const AP_ParamT<signed char, AP_PARAM_INT8> & one, const unsigned short & two)`, `AP_Math/AP_Math.h:307-310`. -/
def MAX_AP_ParamT_signed_char_1_uint16_t (one : AP_ParamT_signed_char_1.State) (two : UInt16) : UInt16 := Id.run do
  return if Int8.toInt32 (AP_ParamT_signed_char_1.op_to_signed_char one) > UInt32.toInt32 (UInt16.toUInt32 two) then Int16.toUInt16 (Int8.toInt16 (AP_ParamT_signed_char_1.op_to_signed_char one)) else two

/-- C++ `auto MAX(const AP_ParamT<short, AP_PARAM_INT16> & one, const unsigned short & two)`, `AP_Math/AP_Math.h:307-310`. -/
def MAX_AP_ParamT_short_2_uint16_t (one : AP_ParamT_short_2.State) (two : UInt16) : UInt16 := Id.run do
  return if Int16.toInt32 (AP_ParamT_short_2.op_to_short one) > UInt32.toInt32 (UInt16.toUInt32 two) then Int16.toUInt16 (AP_ParamT_short_2.op_to_short one) else two

/-- C++ `ftype sq(const AP_ParamT<float, AP_PARAM_FLOAT> val)`, `AP_Math/AP_Math.h:261-265`. -/
def sq_AP_ParamT_float_4 (val : AP_ParamT_float_4.State) : Binary64 := Id.run do
  let v : Binary64 := AP_ParamT_float_4.op_to_double val
  return v * v

/-- C++ `auto MAX(const double & one, const AP_ParamT<float, AP_PARAM_FLOAT> & two)`, `AP_Math/AP_Math.h:307-310`. -/
def MAX_double_AP_ParamT_float_4 (one : Binary64) (two : AP_ParamT_float_4.State) : Binary64 := Id.run do
  return if one > Binary32.toBinary64 (AP_ParamT_float_4.op_to_float two) then one else Binary32.toBinary64 (AP_ParamT_float_4.op_to_float two)

/-- C++ `auto MAX(const AP_ParamT<float, AP_PARAM_FLOAT> & one, const double & two)`, `AP_Math/AP_Math.h:307-310`. -/
def MAX_AP_ParamT_float_4_double (one : AP_ParamT_float_4.State) (two : Binary64) : Binary64 := Id.run do
  return if Binary32.toBinary64 (AP_ParamT_float_4.op_to_float one) > two then Binary32.toBinary64 (AP_ParamT_float_4.op_to_float one) else two

/-- C++ `auto MAX(const AP_ParamT<float, AP_PARAM_FLOAT> & one, const float & two)`, `AP_Math/AP_Math.h:307-310`. -/
def MAX_AP_ParamT_float_4_float (one : AP_ParamT_float_4.State) (two : Binary32) : Binary32 := Id.run do
  return if AP_ParamT_float_4.op_to_float one > two then AP_ParamT_float_4.op_to_float one else two

/-- C++ `auto MIN(const AP_ParamT<float, AP_PARAM_FLOAT> & one, const float & two)`, `AP_Math/AP_Math.h:300-303`. -/
def MIN_AP_ParamT_float_4_float (one : AP_ParamT_float_4.State) (two : Binary32) : Binary32 := Id.run do
  return if AP_ParamT_float_4.op_to_float one < two then AP_ParamT_float_4.op_to_float one else two

/-- C++ `bool is_zero(const AP_ParamT<float, AP_PARAM_FLOAT> fVal1)`, `AP_Math/AP_Math.h:55-59`. -/
def is_zero_AP_ParamT_float_4 (fVal1 : AP_ParamT_float_4.State) : Bool := Id.run do
  return is_zero_float (AP_ParamT_float_4.op_to_float fVal1)

end Estimator_lib
