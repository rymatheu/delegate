import ArduLean.Runtime.CFloat
import ArduLean.Estimator.libraries.AP_Param.AP_Param
import ArduLean.Estimator.World_2
import ArduLean.Estimator.libraries.AP_Compass.AP_Compass_2

/-!
ArduPilot `libraries/AP_Param`, part 3 of 3. Sources: `libraries/AP_Param/AP_Param.h`.

Items of `lean/Estimator_lib.lean` (the estimator translation), unchanged; placed by `tools/split_modules.py` (`ArduLean/Estimator/INDEX.md`).
-/

open FloatLib.Floats (Binary32 Binary64)

set_option maxRecDepth 200000
-- AP_DAL's `const log_RISH old_RISH = _RISH;` read only by WRITE_REPLAY_BLOCK_IFCHANGED, which is `(void)old`
-- without logging (HAL_LOGGING_ENABLED 0): an unused binding, as in the C++
set_option linter.unusedVariables false

namespace Estimator_lib

namespace AP_Enum_Compass_LearnType

/-- C++ `const Compass::LearnType AP_Enum<Compass::LearnType>::operator const Compass::LearnType() const`, `AP_Param/AP_Param.h:1140-1142`. -/
def op_to_Compass_LearnType (s : State) : Compass.LearnType := Id.run do
  return Compass.LearnType.ofInt (Int8.toInt32 s._value)

end AP_Enum_Compass_LearnType

namespace AP_Enum_Compass_LearnType

/-- C++ `void AP_ParamTBase<signed char, 1>::set(const signed char & v)`, `AP_Param/AP_Param.h:923-925` (a member of `AP_ParamTBase<signed char, 1>`, translated for `AP_Enum<Compass::LearnType>`). -/
def set_int8_t (s : State) (v : Int8) : State := Id.run do
  let mut s := s
  s := { s with _value := v }
  return s

/-- C++ `void AP_ParamTBase<signed char, 1>::set_and_save(const signed char & v)`, `AP_Param/AP_ParamT.cpp:79-83` (a member of `AP_ParamTBase<signed char, 1>`, translated for `AP_Enum<Compass::LearnType>`). -/
def set_and_save_int8_t (s : State) (o : Outputs) (sp : String) (v : Int8) : State × Outputs := Id.run do
  let mut s := s
  let mut o := o
  let force : Bool := decide (Binary32.abs (Int32.toBinary32 (Int8.toInt32 s._value - Int8.toInt32 v)) < (Binary32.ofBits 0x34000000 /- 1.1920929E-7 -/))
  s := set_int8_t s v
  o := o.push (Output.AP_Param_save sp force)
  return (s, o)

/-- C++ `void AP_Enum<Compass::LearnType>::set_and_save(Compass::LearnType v)`, `AP_Param/AP_Param.h:1146-1148`. -/
def set_and_save_LearnType (s : State) (o : Outputs) (sp : String) (v : Compass.LearnType) : State × Outputs := Id.run do
  let mut s := s
  let mut o := o
  let (t'1, t'2) := set_and_save_int8_t s o sp (Int32.toInt8 (Compass.LearnType.toInt v))
  s := t'1
  o := t'2
  return (s, o)

/-- C++ `void AP_Enum<Compass::LearnType>::set(Compass::LearnType v)`, `AP_Param/AP_Param.h:1143-1145`. -/
def set_LearnType (s : State) (v : Compass.LearnType) : State := Id.run do
  let mut s := s
  s := set_int8_t s (Int32.toInt8 (Compass.LearnType.toInt v))
  return s

end AP_Enum_Compass_LearnType

end Estimator_lib
