import ArduLean.Runtime.CFloat
import ArduLean.Estimator.libraries.AP_Math.AP_Math
import ArduLean.Estimator.libraries.AP_Common.AP_Common
import ArduLean.Estimator.libraries.AP_Param.AP_Param
import ArduLean.Estimator.libraries.AP_Compass.AP_Compass

/-!
ArduPilot `libraries/AP_Common`, part 2 of 3. Sources: `libraries/AP_Common/TSIndex.h`.

Items of `lean/Estimator_lib.lean` (the estimator translation), unchanged; placed by `tools/split_modules.py` (`ArduLean/Estimator/INDEX.md`).
-/

open FloatLib.Floats (Binary32 Binary64)

set_option maxRecDepth 200000
-- AP_DAL's `const log_RISH old_RISH = _RISH;` read only by WRITE_REPLAY_BLOCK_IFCHANGED, which is `(void)old`
-- without logging (HAL_LOGGING_ENABLED 0): an unused binding, as in the C++
set_option linter.unusedVariables false

namespace Estimator_lib

namespace RestrictIDTypeArray_Compass_mag_state_4_typesafe_index_unsigned_char_TAG_StateIndex

/-- State of C++ `RestrictIDTypeArray<Compass::mag_state, 4, typesafe_index<unsigned char, TAG_StateIndex>>` (`AP_Common/TSIndex.h:105-118`): its data members. -/
structure State where
  /-- `Compass::mag_state _priv_instance[4]` of `RestrictIDTypeArray<Compass::mag_state, 4, typesafe_index<unsigned char, TAG_StateIndex>>` (`AP_Common/TSIndex.h:108`). -/
  _priv_instance : Array Compass.mag_state.State := Array.replicate 4 {}
deriving Inhabited

end RestrictIDTypeArray_Compass_mag_state_4_typesafe_index_unsigned_char_TAG_StateIndex

namespace RestrictIDTypeArray_AP_ParamT_signed_char_AP_PARAM_INT8_3_typesafe_index_unsigned_char_TAG_Priority

/-- State of C++ `RestrictIDTypeArray<AP_ParamT<signed char, AP_PARAM_INT8>, 3, typesafe_index<unsigned char, TAG_Priority>>` (`AP_Common/TSIndex.h:105-118`): its data members. -/
structure State where
  /-- `AP_ParamT<signed char, AP_PARAM_INT8> _priv_instance[3]` of `RestrictIDTypeArray<AP_ParamT<signed char, AP_PARAM_INT8>, 3, typesafe_index<unsigned char, TAG_Priority>>` (`AP_Common/TSIndex.h:108`). -/
  _priv_instance : Array AP_ParamT_signed_char_1.State := Array.replicate 3 {}
deriving Inhabited

end RestrictIDTypeArray_AP_ParamT_signed_char_AP_PARAM_INT8_3_typesafe_index_unsigned_char_TAG_Priority

namespace RestrictIDTypeArray_AP_ParamT_unsigned_int_AP_PARAM_INT32_3_typesafe_index_unsigned_char_TAG_Priority

/-- State of C++ `RestrictIDTypeArray<AP_ParamT<unsigned int, AP_PARAM_INT32>, 3, typesafe_index<unsigned char, TAG_Priority>>` (`AP_Common/TSIndex.h:105-118`): its data members. -/
structure State where
  /-- `AP_ParamT<unsigned int, AP_PARAM_INT32> _priv_instance[3]` of `RestrictIDTypeArray<AP_ParamT<unsigned int, AP_PARAM_INT32>, 3, typesafe_index<unsigned char, TAG_Priority>>` (`AP_Common/TSIndex.h:108`). -/
  _priv_instance : Array AP_ParamT_unsigned_int_3.State := Array.replicate 3 {}
deriving Inhabited

end RestrictIDTypeArray_AP_ParamT_unsigned_int_AP_PARAM_INT32_3_typesafe_index_unsigned_char_TAG_Priority

namespace RestrictIDTypeArray_Compass_mag_state_4_typesafe_index_unsigned_char_TAG_StateIndex

/-- C++ `const Compass::mag_state & RestrictIDTypeArray<Compass::mag_state, 4, typesafe_index<unsigned char, TAG_StateIndex>>::operator[](const typesafe_index<unsigned char, TAG_StateIndex> & index) const`, `AP_Common/TSIndex.h:114-117`. -/
def op_index (s : State) (index : typesafe_index_unsigned_char_TAG_StateIndex.State) : Compass.mag_state.State := Id.run do
  return s._priv_instance[UInt8.toNat (typesafe_index_unsigned_char_TAG_StateIndex.get_int index)]!

end RestrictIDTypeArray_Compass_mag_state_4_typesafe_index_unsigned_char_TAG_StateIndex

end Estimator_lib
