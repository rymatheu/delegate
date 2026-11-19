import ArduLean.Runtime.Memory
import ArduLean.Vehicle.libraries.AP_Math.AP_Math
import ArduLean.Vehicle.libraries.AP_Param.AP_Param
import ArduLean.Vehicle.libraries.RC_Channel.RC_Channel

/-!
ArduPilot `libraries/AP_Math`, part 2 of 2. Sources: `libraries/AP_Math/AP_Math.h`, `libraries/AP_Math/AP_Math.cpp`.

Items of `lean/Vehicle_lib.lean` (the vehicle translation), unchanged; placed by `tools/split_modules.py` (`ArduLean/Vehicle/INDEX.md`).
-/

open FloatLib.Floats (Binary32 Binary64)

set_option linter.unusedVariables false
set_option linter.unreachableTactic false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false

namespace Vehicle_lib

/-- C++ `is_positive : bool (const AP_ParamT<float, AP_PARAM_FLOAT>)`, `<built-in>:65-69`. -/
def is_positive'AP_ParamT_float_AP_PARAM_FLOAT (fVal1 : UInt64) : PMem.M Bool := do
  let t'1 ← AP_ParamT'float_4.operator_const_float__'1 fVal1
  let t'2 ← PMem.ldF32 t'1
  return (decide (t'2 ≥ (Binary32.ofBits 0x34000000 /- 11920929/100000000000000 -/)))

/-- C++ `MAX : auto (const AP_ParamT<float, AP_PARAM_FLOAT> &, const float &) -> decltype(one > two ? one : two)`, `AP_Math.h:307-310`. -/
def MAX'AP_ParamT_float_AP_PARAM_FLOAT_float (one : UInt64) (two : UInt64) : PMem.M UInt64 := do
  let t'1 ← AP_ParamT'float_4.operator_const_float__'1 one
  let t'2 ← PMem.ldF32 t'1
  let t'3 ← PMem.ldF32 two
  let mut c'4 : UInt64 := 0
  if (decide (t'2 > t'3)) then
    let t'5 ← AP_ParamT'float_4.operator_const_float__'1 one
    c'4 := t'5
  else
    c'4 := two
  return c'4

/-- C++ `MIN : auto (const float &, const AP_ParamT<float, AP_PARAM_FLOAT> &) -> decltype(one < two ? one : two)`, `AP_Math.h:300-303`. -/
def MIN'float_AP_ParamT_float_AP_PARAM_FLOAT (one : UInt64) (two : UInt64) : PMem.M UInt64 := do
  let t'1 ← PMem.ldF32 one
  let t'2 ← AP_ParamT'float_4.operator_const_float__'1 two
  let t'3 ← PMem.ldF32 t'2
  let mut c'4 : UInt64 := 0
  if (decide (t'1 < t'3)) then
    c'4 := one
  else
    let t'5 ← AP_ParamT'float_4.operator_const_float__'1 two
    c'4 := t'5
  return c'4

/-- C++ `is_zero : bool (const AP_ParamT<float, AP_PARAM_FLOAT>)`, `AP_Math.h:?-59`. -/
def is_zero'AP_ParamT_float_AP_PARAM_FLOAT (fVal1 : UInt64) : PMem.M Bool := do
  let t'1 ← AP_ParamT'float_4.operator_const_float__'1 fVal1
  let t'2 ← PMem.ldF32 t'1
  let t'3 ← is_zero t'2
  return t'3

/-- C++ `calc_lowpass_alpha_dt : float (float, float)`, `AP_Math.cpp:418-432`. -/
def calc_lowpass_alpha_dt (dt : Binary32) (cutoff_freq : Binary32) : PMem.M Binary32 := do
  let mut dt := dt
  let mut cutoff_freq := cutoff_freq
  let t'1 ← is_negative'float dt
  let mut sc'3 := t'1
  if !sc'3 then
    let t'2 ← is_negative'float cutoff_freq
    sc'3 := t'2
  if sc'3 then
    return Binary64.toBinary32 ((Binary64.ofBits 0x3ff0000000000000 /- 1 -/))
  let t'4 ← is_zero cutoff_freq
  if t'4 then
    return Binary64.toBinary32 ((Binary64.ofBits 0x3ff0000000000000 /- 1 -/))
  let t'5 ← is_zero dt
  if t'5 then
    return Binary64.toBinary32 ((Binary64.ofBits 0x0000000000000000 /- 0 -/))
  let mut rc : Binary32 := ((Binary32.ofBits 0x3f800000 /- 1 -/) / (((Binary64.toBinary32 ((Binary64.ofBits 0x400921fb54442d18 /- 31415926535897931/10000000000000000 -/))) * (Int32.toBinary32 ((2 : Int32)))) * cutoff_freq))
  return (dt / (dt + rc))

/-- C++ `MIN : auto (const AP_ParamT<float, AP_PARAM_FLOAT> &, const float &) -> decltype(one < two ? one : two)`, `AP_Math.h:300-303`. -/
def MIN'AP_ParamT_float_AP_PARAM_FLOAT_float (one : UInt64) (two : UInt64) : PMem.M UInt64 := do
  let t'1 ← AP_ParamT'float_4.operator_const_float__'1 one
  let t'2 ← PMem.ldF32 t'1
  let t'3 ← PMem.ldF32 two
  let mut c'4 : UInt64 := 0
  if (decide (t'2 < t'3)) then
    let t'5 ← AP_ParamT'float_4.operator_const_float__'1 one
    c'4 := t'5
  else
    c'4 := two
  return c'4

/-- C++ `is_negative : bool (const AP_ParamT<float, AP_PARAM_FLOAT>)`, `<built-in>:76-80`. -/
def is_negative'AP_ParamT_float_AP_PARAM_FLOAT (fVal1 : UInt64) : PMem.M Bool := do
  let t'1 ← AP_ParamT'float_4.operator_const_float__'1 fVal1
  let t'2 ← PMem.ldF32 t'1
  return (decide ((Binary32.toBinary64 (t'2)) ≤ ((-(Binary64.ofBits 0x3ff0000000000000 /- 1 -/)) * (Binary32.toBinary64 ((Binary32.ofBits 0x34000000 /- 11920929/100000000000000 -/))))))

/-- C++ `sq : ftype (const AP_ParamT<float, AP_PARAM_FLOAT>)`, `AP_Math.h:?-265`. -/
def sq'AP_ParamT_float_AP_PARAM_FLOAT (val : UInt64) : PMem.M Binary64 := do
  let t'1 ← AP_ParamT'float_4.operator_double val
  let mut v : Binary64 := t'1
  return (v * v)

end Vehicle_lib
