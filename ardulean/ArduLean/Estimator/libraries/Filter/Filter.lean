import ArduLean.Musl.cosf
import ArduLean.Musl.tanf
import ArduLean.Estimator.libraries.AP_Math.AP_Math

/-!
ArduPilot `libraries/Filter`. Sources: `libraries/Filter/LowPassFilter2p.cpp`, `libraries/Filter/LowPassFilter.cpp`, `libraries/Filter/DerivativeFilter.h`, `libraries/Filter/LowPassFilter2p.h`, `libraries/Filter/DerivativeFilter.cpp`, `libraries/Filter/FilterWithBuffer.h`.

Items of `lean/Estimator_lib.lean` (the estimator translation), unchanged; placed by `tools/split_modules.py` (`ArduLean/Estimator/INDEX.md`).
-/

open FloatLib.Floats (Binary32 Binary64)

set_option maxRecDepth 200000
-- AP_DAL's `const log_RISH old_RISH = _RISH;` read only by WRITE_REPLAY_BLOCK_IFCHANGED, which is `(void)old`
-- without logging (HAL_LOGGING_ENABLED 0): an unused binding, as in the C++
set_option linter.unusedVariables false

namespace Estimator_lib

namespace DerivativeFilterFloat_Size7

/-- State of C++ `DerivativeFilter<float, 7>` (`Filter/DerivativeFilter.h:27-51`): its data members; base classes flattened, base first: `FilterWithBuffer<float, 7>`, `Filter<float>`. -/
structure State where
  /-- `float samples[7]` of `FilterWithBuffer<float, 7>` (`Filter/FilterWithBuffer.h:49`). -/
  samples : Array Binary32 := Array.replicate 7 (Binary32.ofBits 0x00000000 /- 0.0 -/)
  /-- `uint8_t sample_index` of `FilterWithBuffer<float, 7>` (`Filter/FilterWithBuffer.h:50`). -/
  sample_index : UInt8 := (0 : UInt8)
  /-- `bool _new_data` of `DerivativeFilter<float, 7>` (`Filter/DerivativeFilter.h:45`). -/
  _new_data : Bool := false
  /-- `float _last_slope` of `DerivativeFilter<float, 7>` (`Filter/DerivativeFilter.h:46`). -/
  _last_slope : Binary32 := (Binary32.ofBits 0x00000000 /- 0.0 -/)
  /-- `uint32_t _timestamps[7]` of `DerivativeFilter<float, 7>` (`Filter/DerivativeFilter.h:50`). -/
  _timestamps : Array UInt32 := Array.replicate 7 (0 : UInt32)
deriving Inhabited

/-- C++ `void FilterWithBuffer<float, 7>::reset()`, `Filter/FilterWithBuffer.h:91-100` (a member of `FilterWithBuffer<float, 7>`, translated for `DerivativeFilter<float, 7>`). -/
def FilterWithBuffer_float_7.reset (s : State) : State := Id.run do
  let mut s := s
  for i' in [0:7] do
    let i : Int8 := Nat.toInt8 i'
    s := { s with samples := s.samples.set! (Int8.toNatClampNeg i) (Binary32.ofBits 0x00000000 /- 0 -/) }
  s := { s with sample_index := Int8.toUInt8 (Int32.toInt8 (0 : Int32)) }
  return s

/-- C++ `void DerivativeFilter<float, 7>::reset()`, `Filter/DerivativeFilter.cpp:116-120`. -/
def reset (s : State) : State := Id.run do
  let mut s := s
  s := FilterWithBuffer_float_7.reset s
  return s

/-- C++ `FilterWithBuffer<float, 7>::FilterWithBuffer()`, `Filter/FilterWithBuffer.h:82-87` (a member of `FilterWithBuffer<float, 7>`, translated for `DerivativeFilter<float, 7>`). -/
def FilterWithBuffer_float_7.init (s : State) : State := Id.run do
  let mut s := s
  s := { s with sample_index := Int8.toUInt8 (Int32.toInt8 (0 : Int32)) }
  s := reset s
  return s

/-- C++ `DerivativeFilter<float, 7>::DerivativeFilter()`, `Filter/DerivativeFilter.h:32-33`. -/
def init : State := Id.run do
  let mut s : State := {}
  s := FilterWithBuffer_float_7.init s
  return s

end DerivativeFilterFloat_Size7

namespace LowPassFilter_Vector3_float

/-- State of C++ `LowPassFilter<Vector3<float>>` (`Filter/LowPassFilter.cpp:130`): its data members; base classes flattened, base first: `DigitalLPF<Vector3<float>>`. -/
structure State where
  /-- `Vector3<float> output` of `DigitalLPF<Vector3<float>>` (`Filter/LowPassFilter.h:71`). -/
  output : Vector3f.State := {}
  /-- `bool initialised` of `DigitalLPF<Vector3<float>>` (`Filter/LowPassFilter.h:72`). -/
  initialised : Bool := false
  /-- `float cutoff_freq` of `LowPassFilter<Vector3<float>>` (`Filter/LowPassFilter.h:125`). -/
  cutoff_freq : Binary32 := (Binary32.ofBits 0x00000000 /- 0.0 -/)
deriving Inhabited

/-- C++ `DigitalLPF<Vector3<float>>::DigitalLPF()`, `Filter/LowPassFilter.cpp:17-20` (a member of `DigitalLPF<Vector3<float>>`, translated for `LowPassFilter<Vector3<float>>`). -/
def DigitalLPF_Vector3_float.init (s : State) : State := Id.run do
  let mut s := s
  s := { s with output := Vector3f.init_void }
  s := { s with output := Vector3f.init_void }
  return s

/-- C++ `LowPassFilter<Vector3<float>>::LowPassFilter()`, `Filter/LowPassFilter.h:110`. -/
def init_void : State := Id.run do
  let mut s : State := {}
  s := DigitalLPF_Vector3_float.init s
  return s

end LowPassFilter_Vector3_float

namespace DigitalBiquadFilter_Vector3_float

/-- State of C++ `DigitalBiquadFilter<Vector3<float>>` (`Filter/LowPassFilter2p.h:25-51`): its data members. -/
structure State where
  /-- `Vector3<float> _delay_element_1` of `DigitalBiquadFilter<Vector3<float>>` (`Filter/LowPassFilter2p.h:48`). -/
  _delay_element_1 : Vector3f.State := {}
  /-- `Vector3<float> _delay_element_2` of `DigitalBiquadFilter<Vector3<float>>` (`Filter/LowPassFilter2p.h:49`). -/
  _delay_element_2 : Vector3f.State := {}
  /-- `bool initialised` of `DigitalBiquadFilter<Vector3<float>>` (`Filter/LowPassFilter2p.h:50`). -/
  initialised : Bool := false
deriving Inhabited

/-- C++ `DigitalBiquadFilter<Vector3<float>>::DigitalBiquadFilter()`, `Filter/LowPassFilter2p.cpp:13-16`. -/
def init : State := Id.run do
  let mut s : State := {}
  s := { s with _delay_element_1 := Vector3f.init_void }
  s := { s with _delay_element_2 := Vector3f.init_void }
  s := { s with _delay_element_1 := Vector3f.init_void }
  s := { s with _delay_element_2 := Vector3f.init_void }
  return s

end DigitalBiquadFilter_Vector3_float

/-- C++ `struct DigitalBiquadFilter<Vector3<float>>::biquad_params`, `Filter/LowPassFilter2p.h:28-36`. -/
structure DigitalBiquadFilter_Vector3_float_biquad_params where
  /-- `float cutoff_freq` of `DigitalBiquadFilter<Vector3<float>>::biquad_params` (`Filter/LowPassFilter2p.h:29`). -/
  cutoff_freq : Binary32 := (Binary32.ofBits 0x00000000 /- 0.0 -/)
  /-- `float sample_freq` of `DigitalBiquadFilter<Vector3<float>>::biquad_params` (`Filter/LowPassFilter2p.h:30`). -/
  sample_freq : Binary32 := (Binary32.ofBits 0x00000000 /- 0.0 -/)
  /-- `float a1` of `DigitalBiquadFilter<Vector3<float>>::biquad_params` (`Filter/LowPassFilter2p.h:31`). -/
  a1 : Binary32 := (Binary32.ofBits 0x00000000 /- 0.0 -/)
  /-- `float a2` of `DigitalBiquadFilter<Vector3<float>>::biquad_params` (`Filter/LowPassFilter2p.h:32`). -/
  a2 : Binary32 := (Binary32.ofBits 0x00000000 /- 0.0 -/)
  /-- `float b0` of `DigitalBiquadFilter<Vector3<float>>::biquad_params` (`Filter/LowPassFilter2p.h:33`). -/
  b0 : Binary32 := (Binary32.ofBits 0x00000000 /- 0.0 -/)
  /-- `float b1` of `DigitalBiquadFilter<Vector3<float>>::biquad_params` (`Filter/LowPassFilter2p.h:34`). -/
  b1 : Binary32 := (Binary32.ofBits 0x00000000 /- 0.0 -/)
  /-- `float b2` of `DigitalBiquadFilter<Vector3<float>>::biquad_params` (`Filter/LowPassFilter2p.h:35`). -/
  b2 : Binary32 := (Binary32.ofBits 0x00000000 /- 0.0 -/)
deriving Inhabited

namespace LowPassFilter2p_Vector3_float

/-- State of C++ `LowPassFilter2p<Vector3<float>>` (`Filter/LowPassFilter2p.cpp:126`): its data members. -/
structure State where
  /-- `struct DigitalBiquadFilter<Vector3<float>>::biquad_params _params` of `LowPassFilter2p<Vector3<float>>` (`Filter/LowPassFilter2p.h:71`). -/
  _params : DigitalBiquadFilter_Vector3_float_biquad_params := {}
  /-- `DigitalBiquadFilter<Vector3<float>> _filter` of `LowPassFilter2p<Vector3<float>>` (`Filter/LowPassFilter2p.h:74`). -/
  _filter : DigitalBiquadFilter_Vector3_float.State := DigitalBiquadFilter_Vector3_float.init
deriving Inhabited

/-- C++ `LowPassFilter2p<Vector3<float>>::LowPassFilter2p()`, `Filter/LowPassFilter2p.cpp:75-77`. -/
def init_void : State := Id.run do
  let mut s : State := {}
  s := { s with _filter := DigitalBiquadFilter_Vector3_float.init }
  s := { s with _params := { cutoff_freq := (Binary32.ofBits 0x00000000 /- 0.0 -/), sample_freq := (Binary32.ofBits 0x00000000 /- 0.0 -/), a1 := (Binary32.ofBits 0x00000000 /- 0.0 -/), a2 := (Binary32.ofBits 0x00000000 /- 0.0 -/), b0 := (Binary32.ofBits 0x00000000 /- 0.0 -/), b1 := (Binary32.ofBits 0x00000000 /- 0.0 -/), b2 := (Binary32.ofBits 0x00000000 /- 0.0 -/) } }
  return s

end LowPassFilter2p_Vector3_float

namespace LowPassFilter_Vector3_float

/-- C++ `Vector3<float> DigitalLPF<Vector3<float>>::_apply(const Vector3<float> & sample, const float & alpha)`, `Filter/LowPassFilter.cpp:24-31` (a member of `DigitalLPF<Vector3<float>>`, translated for `LowPassFilter<Vector3<float>>`). -/
def _apply (s : State) (sample : Vector3f.State) (alpha : Binary32) : State × Vector3f.State := Id.run do
  let mut s := s
  let (t'1, _) := Vector3f.op_add_assign s.output (Vector3f.op_mul_float (Vector3f.op_sub_Vector3f sample s.output) alpha)
  s := { s with output := t'1 }
  if !s.initialised then
    s := { s with initialised := true }
    s := { s with output := sample }
  return (s, s.output)

/-- C++ `Vector3<float> LowPassFilter<Vector3<float>>::apply(const Vector3<float> & sample, const float & dt)`, `Filter/LowPassFilter.cpp:119-122`. -/
def apply (s : State) (sample : Vector3f.State) (dt : Binary32) : State × Vector3f.State := Id.run do
  let mut s := s
  let alpha : Binary32 := Estimator_lib.calc_lowpass_alpha_dt dt s.cutoff_freq
  let (t'1, t'2) := _apply s sample alpha
  s := t'1
  return (s, t'2)

end LowPassFilter_Vector3_float

namespace DigitalBiquadFilter_Vector3_float

/-- C++ `void DigitalBiquadFilter<Vector3<float>>::reset(const Vector3<float> & value, const struct biquad_params & params)`, `Filter/LowPassFilter2p.cpp:43-46`. -/
def reset_Vector3f_DigitalBiquadFilter_Vector3_float_biquad_params (s : State) (value : Vector3f.State) (params : DigitalBiquadFilter_Vector3_float_biquad_params) : State := Id.run do
  let mut s := s
  s := { s with _delay_element_2 := Vector3f.op_mul_float value (Binary64.toBinary32 ((Binary64.ofBits 0x3ff0000000000000 /- 1.0 -/) / Binary32.toBinary64 ((Binary32.ofBits 0x3f800000 /- 1 -/) + params.a1 + params.a2))) }
  s := { s with _delay_element_1 := s._delay_element_2 }
  s := { s with initialised := true }
  return s

/-- C++ `Vector3<float> DigitalBiquadFilter<Vector3<float>>::apply(const Vector3<float> & sample, const struct biquad_params & params)`, `Filter/LowPassFilter2p.cpp:19-35`. -/
def apply (s : State) (sample : Vector3f.State) (params : DigitalBiquadFilter_Vector3_float_biquad_params) : State × Vector3f.State := Id.run do
  let mut s := s
  if !(Estimator_lib.is_positive_float params.cutoff_freq) || !(Estimator_lib.is_positive_float params.sample_freq) then
    return (s, sample)
  if !s.initialised then
    s := reset_Vector3f_DigitalBiquadFilter_Vector3_float_biquad_params s sample params
  let delay_element_0 : Vector3f.State := Vector3f.op_sub_Vector3f (Vector3f.op_sub_Vector3f sample (Vector3f.op_mul_float s._delay_element_1 params.a1)) (Vector3f.op_mul_float s._delay_element_2 params.a2)
  let output : Vector3f.State := Vector3f.op_add (Vector3f.op_add (Vector3f.op_mul_float delay_element_0 params.b0) (Vector3f.op_mul_float s._delay_element_1 params.b1)) (Vector3f.op_mul_float s._delay_element_2 params.b2)
  s := { s with _delay_element_2 := s._delay_element_1 }
  s := { s with _delay_element_1 := delay_element_0 }
  return (s, output)

end DigitalBiquadFilter_Vector3_float

namespace LowPassFilter2p_Vector3_float

/-- C++ `Vector3<float> LowPassFilter2p<Vector3<float>>::apply(const Vector3<float> & sample)`, `Filter/LowPassFilter2p.cpp:104-106`. -/
def apply (s : State) (sample : Vector3f.State) : State × Vector3f.State := Id.run do
  let mut s := s
  let (t'1, t'2) := DigitalBiquadFilter_Vector3_float.apply s._filter sample s._params
  s := { s with _filter := t'1 }
  return (s, t'2)

end LowPassFilter2p_Vector3_float

namespace DigitalBiquadFilter_Vector3_float

/-- C++ `void DigitalBiquadFilter<Vector3<float>>::reset()`, `Filter/LowPassFilter2p.cpp:38-40`. -/
def reset_void (s : State) : State := Id.run do
  let mut s := s
  s := { s with initialised := false }
  return s

end DigitalBiquadFilter_Vector3_float

namespace LowPassFilter2p_Vector3_float

/-- C++ `void LowPassFilter2p<Vector3<float>>::reset()`, `Filter/LowPassFilter2p.cpp:109-111`. -/
def reset_void (s : State) : State := Id.run do
  let mut s := s
  s := { s with _filter := DigitalBiquadFilter_Vector3_float.reset_void s._filter }
  return s

end LowPassFilter2p_Vector3_float

namespace DigitalBiquadFilter_Vector3_float

/-- C++ `static void DigitalBiquadFilter<Vector3<float>>::compute_params(float sample_freq, float cutoff_freq, biquad_params & ret)`, `Filter/LowPassFilter2p.cpp:49-67`. -/
def compute_params (sample_freq cutoff_freq : Binary32) (ret : DigitalBiquadFilter_Vector3_float_biquad_params) : DigitalBiquadFilter_Vector3_float_biquad_params := Id.run do
  let mut ret := ret
  ret := { ret with cutoff_freq := Estimator_lib.MIN_float2 cutoff_freq (Binary64.toBinary32 (Binary32.toBinary64 sample_freq * (Binary64.ofBits 0x3fd999999999999a /- 0.4 -/))) }
  ret := { ret with sample_freq := sample_freq }
  if !(Estimator_lib.is_positive_float ret.cutoff_freq) then
    return ret
  let fr : Binary32 := ret.sample_freq / ret.cutoff_freq
  let ohm : Binary32 := Musl.tanf.tanf (Binary64.toBinary32 ((Binary64.ofBits 0x400921fb54442d18 /- 3.1415926535897931 -/) / Binary32.toBinary64 fr))
  let c : Binary32 := (Binary32.ofBits 0x3f800000 /- 1.0f -/) + (Binary32.ofBits 0x40000000 /- 2.0f -/) * Musl.cosf.cosf (Binary32.ofBits 0x3f490fdb /- (float)884279719003555/1125899906842624 -/) * ohm + ohm * ohm
  ret := { ret with b0 := ohm * ohm / c }
  ret := { ret with b1 := (Binary32.ofBits 0x40000000 /- 2.0f -/) * ret.b0 }
  ret := { ret with b2 := ret.b0 }
  ret := { ret with a1 := (Binary32.ofBits 0x40000000 /- 2.0f -/) * (ohm * ohm - (Binary32.ofBits 0x3f800000 /- 1.0f -/)) / c }
  ret := { ret with a2 := ((Binary32.ofBits 0x3f800000 /- 1.0f -/) - (Binary32.ofBits 0x40000000 /- 2.0f -/) * Musl.cosf.cosf (Binary32.ofBits 0x3f490fdb /- (float)884279719003555/1125899906842624 -/) * ohm + ohm * ohm) / c }
  return ret

end DigitalBiquadFilter_Vector3_float

namespace LowPassFilter2p_Vector3_float

/-- C++ `void LowPassFilter2p<Vector3<float>>::set_cutoff_frequency(float sample_freq, float cutoff_freq)`, `Filter/LowPassFilter2p.cpp:88-90`. -/
def set_cutoff_frequency (s : State) (sample_freq : Binary32) (cutoff_freq : Binary32) : State := Id.run do
  let mut s := s
  s := { s with _params := DigitalBiquadFilter_Vector3_float.compute_params sample_freq cutoff_freq s._params }
  return s

end LowPassFilter2p_Vector3_float

namespace DerivativeFilterFloat_Size7

/-- C++ `float DerivativeFilter<float, 7>::slope()`, `Filter/DerivativeFilter.cpp:52-112`. -/
def slope (s : State) : State × Binary32 := Id.run do
  let mut s := s
  if !s._new_data then
    return (s, s._last_slope)
  let mut result : Binary32 := (Binary32.ofBits 0x00000000 /- 0 -/)
  if s._timestamps[6]! == s._timestamps[5]! then
    return (s, (Binary32.ofBits 0x00000000 /- 0 -/))
  let t'1 := UInt32.toInt32 (UInt8.toUInt32 (7 : UInt8))
  if t'1 == (5 : Int32) then
    result := (Binary32.ofBits 0x40800000 /- 2*2 -/) * (s.samples[Int32.toNatClampNeg ((((UInt32.toInt32 (UInt8.toUInt32 s.sample_index) - (1 : Int32)) + (1 : Int32) + (1 : Int32)) + (3 : Int32) * UInt32.toInt32 (UInt8.toUInt32 (7 : UInt8)) / (2 : Int32)) % UInt32.toInt32 (UInt8.toUInt32 (7 : UInt8)))]! - s.samples[Int32.toNatClampNeg ((((UInt32.toInt32 (UInt8.toUInt32 s.sample_index) - (1 : Int32)) + -(1 : Int32) + (1 : Int32)) + (3 : Int32) * UInt32.toInt32 (UInt8.toUInt32 (7 : UInt8)) / (2 : Int32)) % UInt32.toInt32 (UInt8.toUInt32 (7 : UInt8)))]!) / UInt32.toBinary32 (s._timestamps[Int32.toNatClampNeg ((((UInt32.toInt32 (UInt8.toUInt32 s.sample_index) - (1 : Int32)) + (1 : Int32) + (1 : Int32)) + (3 : Int32) * UInt32.toInt32 (UInt8.toUInt32 (7 : UInt8)) / (2 : Int32)) % UInt32.toInt32 (UInt8.toUInt32 (7 : UInt8)))]! - s._timestamps[Int32.toNatClampNeg ((((UInt32.toInt32 (UInt8.toUInt32 s.sample_index) - (1 : Int32)) + -(1 : Int32) + (1 : Int32)) + (3 : Int32) * UInt32.toInt32 (UInt8.toUInt32 (7 : UInt8)) / (2 : Int32)) % UInt32.toInt32 (UInt8.toUInt32 (7 : UInt8)))]!) + (Binary32.ofBits 0x40800000 /- 4*1 -/) * (s.samples[Int32.toNatClampNeg ((((UInt32.toInt32 (UInt8.toUInt32 s.sample_index) - (1 : Int32)) + (2 : Int32) + (1 : Int32)) + (3 : Int32) * UInt32.toInt32 (UInt8.toUInt32 (7 : UInt8)) / (2 : Int32)) % UInt32.toInt32 (UInt8.toUInt32 (7 : UInt8)))]! - s.samples[Int32.toNatClampNeg ((((UInt32.toInt32 (UInt8.toUInt32 s.sample_index) - (1 : Int32)) + -(2 : Int32) + (1 : Int32)) + (3 : Int32) * UInt32.toInt32 (UInt8.toUInt32 (7 : UInt8)) / (2 : Int32)) % UInt32.toInt32 (UInt8.toUInt32 (7 : UInt8)))]!) / UInt32.toBinary32 (s._timestamps[Int32.toNatClampNeg ((((UInt32.toInt32 (UInt8.toUInt32 s.sample_index) - (1 : Int32)) + (2 : Int32) + (1 : Int32)) + (3 : Int32) * UInt32.toInt32 (UInt8.toUInt32 (7 : UInt8)) / (2 : Int32)) % UInt32.toInt32 (UInt8.toUInt32 (7 : UInt8)))]! - s._timestamps[Int32.toNatClampNeg ((((UInt32.toInt32 (UInt8.toUInt32 s.sample_index) - (1 : Int32)) + -(2 : Int32) + (1 : Int32)) + (3 : Int32) * UInt32.toInt32 (UInt8.toUInt32 (7 : UInt8)) / (2 : Int32)) % UInt32.toInt32 (UInt8.toUInt32 (7 : UInt8)))]!)
    result := result / (Binary32.ofBits 0x41000000 /- 8 -/)
  else if t'1 == (7 : Int32) then
    result := (Binary32.ofBits 0x41200000 /- 2*5 -/) * (s.samples[Int32.toNatClampNeg ((((UInt32.toInt32 (UInt8.toUInt32 s.sample_index) - (1 : Int32)) + (1 : Int32) + (1 : Int32)) + (3 : Int32) * UInt32.toInt32 (UInt8.toUInt32 (7 : UInt8)) / (2 : Int32)) % UInt32.toInt32 (UInt8.toUInt32 (7 : UInt8)))]! - s.samples[Int32.toNatClampNeg ((((UInt32.toInt32 (UInt8.toUInt32 s.sample_index) - (1 : Int32)) + -(1 : Int32) + (1 : Int32)) + (3 : Int32) * UInt32.toInt32 (UInt8.toUInt32 (7 : UInt8)) / (2 : Int32)) % UInt32.toInt32 (UInt8.toUInt32 (7 : UInt8)))]!) / UInt32.toBinary32 (s._timestamps[Int32.toNatClampNeg ((((UInt32.toInt32 (UInt8.toUInt32 s.sample_index) - (1 : Int32)) + (1 : Int32) + (1 : Int32)) + (3 : Int32) * UInt32.toInt32 (UInt8.toUInt32 (7 : UInt8)) / (2 : Int32)) % UInt32.toInt32 (UInt8.toUInt32 (7 : UInt8)))]! - s._timestamps[Int32.toNatClampNeg ((((UInt32.toInt32 (UInt8.toUInt32 s.sample_index) - (1 : Int32)) + -(1 : Int32) + (1 : Int32)) + (3 : Int32) * UInt32.toInt32 (UInt8.toUInt32 (7 : UInt8)) / (2 : Int32)) % UInt32.toInt32 (UInt8.toUInt32 (7 : UInt8)))]!) + (Binary32.ofBits 0x41800000 /- 4*4 -/) * (s.samples[Int32.toNatClampNeg ((((UInt32.toInt32 (UInt8.toUInt32 s.sample_index) - (1 : Int32)) + (2 : Int32) + (1 : Int32)) + (3 : Int32) * UInt32.toInt32 (UInt8.toUInt32 (7 : UInt8)) / (2 : Int32)) % UInt32.toInt32 (UInt8.toUInt32 (7 : UInt8)))]! - s.samples[Int32.toNatClampNeg ((((UInt32.toInt32 (UInt8.toUInt32 s.sample_index) - (1 : Int32)) + -(2 : Int32) + (1 : Int32)) + (3 : Int32) * UInt32.toInt32 (UInt8.toUInt32 (7 : UInt8)) / (2 : Int32)) % UInt32.toInt32 (UInt8.toUInt32 (7 : UInt8)))]!) / UInt32.toBinary32 (s._timestamps[Int32.toNatClampNeg ((((UInt32.toInt32 (UInt8.toUInt32 s.sample_index) - (1 : Int32)) + (2 : Int32) + (1 : Int32)) + (3 : Int32) * UInt32.toInt32 (UInt8.toUInt32 (7 : UInt8)) / (2 : Int32)) % UInt32.toInt32 (UInt8.toUInt32 (7 : UInt8)))]! - s._timestamps[Int32.toNatClampNeg ((((UInt32.toInt32 (UInt8.toUInt32 s.sample_index) - (1 : Int32)) + -(2 : Int32) + (1 : Int32)) + (3 : Int32) * UInt32.toInt32 (UInt8.toUInt32 (7 : UInt8)) / (2 : Int32)) % UInt32.toInt32 (UInt8.toUInt32 (7 : UInt8)))]!) + (Binary32.ofBits 0x40c00000 /- 6*1 -/) * (s.samples[Int32.toNatClampNeg ((((UInt32.toInt32 (UInt8.toUInt32 s.sample_index) - (1 : Int32)) + (3 : Int32) + (1 : Int32)) + (3 : Int32) * UInt32.toInt32 (UInt8.toUInt32 (7 : UInt8)) / (2 : Int32)) % UInt32.toInt32 (UInt8.toUInt32 (7 : UInt8)))]! - s.samples[Int32.toNatClampNeg ((((UInt32.toInt32 (UInt8.toUInt32 s.sample_index) - (1 : Int32)) + -(3 : Int32) + (1 : Int32)) + (3 : Int32) * UInt32.toInt32 (UInt8.toUInt32 (7 : UInt8)) / (2 : Int32)) % UInt32.toInt32 (UInt8.toUInt32 (7 : UInt8)))]!) / UInt32.toBinary32 (s._timestamps[Int32.toNatClampNeg ((((UInt32.toInt32 (UInt8.toUInt32 s.sample_index) - (1 : Int32)) + (3 : Int32) + (1 : Int32)) + (3 : Int32) * UInt32.toInt32 (UInt8.toUInt32 (7 : UInt8)) / (2 : Int32)) % UInt32.toInt32 (UInt8.toUInt32 (7 : UInt8)))]! - s._timestamps[Int32.toNatClampNeg ((((UInt32.toInt32 (UInt8.toUInt32 s.sample_index) - (1 : Int32)) + -(3 : Int32) + (1 : Int32)) + (3 : Int32) * UInt32.toInt32 (UInt8.toUInt32 (7 : UInt8)) / (2 : Int32)) % UInt32.toInt32 (UInt8.toUInt32 (7 : UInt8)))]!)
    result := result / (Binary32.ofBits 0x42000000 /- 32 -/)
  else if t'1 == (9 : Int32) then
    result := (Binary32.ofBits 0x41e00000 /- 2*14 -/) * (s.samples[Int32.toNatClampNeg ((((UInt32.toInt32 (UInt8.toUInt32 s.sample_index) - (1 : Int32)) + (1 : Int32) + (1 : Int32)) + (3 : Int32) * UInt32.toInt32 (UInt8.toUInt32 (7 : UInt8)) / (2 : Int32)) % UInt32.toInt32 (UInt8.toUInt32 (7 : UInt8)))]! - s.samples[Int32.toNatClampNeg ((((UInt32.toInt32 (UInt8.toUInt32 s.sample_index) - (1 : Int32)) + -(1 : Int32) + (1 : Int32)) + (3 : Int32) * UInt32.toInt32 (UInt8.toUInt32 (7 : UInt8)) / (2 : Int32)) % UInt32.toInt32 (UInt8.toUInt32 (7 : UInt8)))]!) / UInt32.toBinary32 (s._timestamps[Int32.toNatClampNeg ((((UInt32.toInt32 (UInt8.toUInt32 s.sample_index) - (1 : Int32)) + (1 : Int32) + (1 : Int32)) + (3 : Int32) * UInt32.toInt32 (UInt8.toUInt32 (7 : UInt8)) / (2 : Int32)) % UInt32.toInt32 (UInt8.toUInt32 (7 : UInt8)))]! - s._timestamps[Int32.toNatClampNeg ((((UInt32.toInt32 (UInt8.toUInt32 s.sample_index) - (1 : Int32)) + -(1 : Int32) + (1 : Int32)) + (3 : Int32) * UInt32.toInt32 (UInt8.toUInt32 (7 : UInt8)) / (2 : Int32)) % UInt32.toInt32 (UInt8.toUInt32 (7 : UInt8)))]!) + (Binary32.ofBits 0x42600000 /- 4*14 -/) * (s.samples[Int32.toNatClampNeg ((((UInt32.toInt32 (UInt8.toUInt32 s.sample_index) - (1 : Int32)) + (2 : Int32) + (1 : Int32)) + (3 : Int32) * UInt32.toInt32 (UInt8.toUInt32 (7 : UInt8)) / (2 : Int32)) % UInt32.toInt32 (UInt8.toUInt32 (7 : UInt8)))]! - s.samples[Int32.toNatClampNeg ((((UInt32.toInt32 (UInt8.toUInt32 s.sample_index) - (1 : Int32)) + -(2 : Int32) + (1 : Int32)) + (3 : Int32) * UInt32.toInt32 (UInt8.toUInt32 (7 : UInt8)) / (2 : Int32)) % UInt32.toInt32 (UInt8.toUInt32 (7 : UInt8)))]!) / UInt32.toBinary32 (s._timestamps[Int32.toNatClampNeg ((((UInt32.toInt32 (UInt8.toUInt32 s.sample_index) - (1 : Int32)) + (2 : Int32) + (1 : Int32)) + (3 : Int32) * UInt32.toInt32 (UInt8.toUInt32 (7 : UInt8)) / (2 : Int32)) % UInt32.toInt32 (UInt8.toUInt32 (7 : UInt8)))]! - s._timestamps[Int32.toNatClampNeg ((((UInt32.toInt32 (UInt8.toUInt32 s.sample_index) - (1 : Int32)) + -(2 : Int32) + (1 : Int32)) + (3 : Int32) * UInt32.toInt32 (UInt8.toUInt32 (7 : UInt8)) / (2 : Int32)) % UInt32.toInt32 (UInt8.toUInt32 (7 : UInt8)))]!) + (Binary32.ofBits 0x42100000 /- 6* 6 -/) * (s.samples[Int32.toNatClampNeg ((((UInt32.toInt32 (UInt8.toUInt32 s.sample_index) - (1 : Int32)) + (3 : Int32) + (1 : Int32)) + (3 : Int32) * UInt32.toInt32 (UInt8.toUInt32 (7 : UInt8)) / (2 : Int32)) % UInt32.toInt32 (UInt8.toUInt32 (7 : UInt8)))]! - s.samples[Int32.toNatClampNeg ((((UInt32.toInt32 (UInt8.toUInt32 s.sample_index) - (1 : Int32)) + -(3 : Int32) + (1 : Int32)) + (3 : Int32) * UInt32.toInt32 (UInt8.toUInt32 (7 : UInt8)) / (2 : Int32)) % UInt32.toInt32 (UInt8.toUInt32 (7 : UInt8)))]!) / UInt32.toBinary32 (s._timestamps[Int32.toNatClampNeg ((((UInt32.toInt32 (UInt8.toUInt32 s.sample_index) - (1 : Int32)) + (3 : Int32) + (1 : Int32)) + (3 : Int32) * UInt32.toInt32 (UInt8.toUInt32 (7 : UInt8)) / (2 : Int32)) % UInt32.toInt32 (UInt8.toUInt32 (7 : UInt8)))]! - s._timestamps[Int32.toNatClampNeg ((((UInt32.toInt32 (UInt8.toUInt32 s.sample_index) - (1 : Int32)) + -(3 : Int32) + (1 : Int32)) + (3 : Int32) * UInt32.toInt32 (UInt8.toUInt32 (7 : UInt8)) / (2 : Int32)) % UInt32.toInt32 (UInt8.toUInt32 (7 : UInt8)))]!) + (Binary32.ofBits 0x41000000 /- 8* 1 -/) * (s.samples[Int32.toNatClampNeg ((((UInt32.toInt32 (UInt8.toUInt32 s.sample_index) - (1 : Int32)) + (4 : Int32) + (1 : Int32)) + (3 : Int32) * UInt32.toInt32 (UInt8.toUInt32 (7 : UInt8)) / (2 : Int32)) % UInt32.toInt32 (UInt8.toUInt32 (7 : UInt8)))]! - s.samples[Int32.toNatClampNeg ((((UInt32.toInt32 (UInt8.toUInt32 s.sample_index) - (1 : Int32)) + -(4 : Int32) + (1 : Int32)) + (3 : Int32) * UInt32.toInt32 (UInt8.toUInt32 (7 : UInt8)) / (2 : Int32)) % UInt32.toInt32 (UInt8.toUInt32 (7 : UInt8)))]!) / UInt32.toBinary32 (s._timestamps[Int32.toNatClampNeg ((((UInt32.toInt32 (UInt8.toUInt32 s.sample_index) - (1 : Int32)) + (4 : Int32) + (1 : Int32)) + (3 : Int32) * UInt32.toInt32 (UInt8.toUInt32 (7 : UInt8)) / (2 : Int32)) % UInt32.toInt32 (UInt8.toUInt32 (7 : UInt8)))]! - s._timestamps[Int32.toNatClampNeg ((((UInt32.toInt32 (UInt8.toUInt32 s.sample_index) - (1 : Int32)) + -(4 : Int32) + (1 : Int32)) + (3 : Int32) * UInt32.toInt32 (UInt8.toUInt32 (7 : UInt8)) / (2 : Int32)) % UInt32.toInt32 (UInt8.toUInt32 (7 : UInt8)))]!)
    result := result / (Binary32.ofBits 0x43000000 /- 128 -/)
  else if t'1 == (11 : Int32) then
    result := (Binary32.ofBits 0x42a80000 /- 2*42 -/) * (s.samples[Int32.toNatClampNeg ((((UInt32.toInt32 (UInt8.toUInt32 s.sample_index) - (1 : Int32)) + (1 : Int32) + (1 : Int32)) + (3 : Int32) * UInt32.toInt32 (UInt8.toUInt32 (7 : UInt8)) / (2 : Int32)) % UInt32.toInt32 (UInt8.toUInt32 (7 : UInt8)))]! - s.samples[Int32.toNatClampNeg ((((UInt32.toInt32 (UInt8.toUInt32 s.sample_index) - (1 : Int32)) + -(1 : Int32) + (1 : Int32)) + (3 : Int32) * UInt32.toInt32 (UInt8.toUInt32 (7 : UInt8)) / (2 : Int32)) % UInt32.toInt32 (UInt8.toUInt32 (7 : UInt8)))]!) / UInt32.toBinary32 (s._timestamps[Int32.toNatClampNeg ((((UInt32.toInt32 (UInt8.toUInt32 s.sample_index) - (1 : Int32)) + (1 : Int32) + (1 : Int32)) + (3 : Int32) * UInt32.toInt32 (UInt8.toUInt32 (7 : UInt8)) / (2 : Int32)) % UInt32.toInt32 (UInt8.toUInt32 (7 : UInt8)))]! - s._timestamps[Int32.toNatClampNeg ((((UInt32.toInt32 (UInt8.toUInt32 s.sample_index) - (1 : Int32)) + -(1 : Int32) + (1 : Int32)) + (3 : Int32) * UInt32.toInt32 (UInt8.toUInt32 (7 : UInt8)) / (2 : Int32)) % UInt32.toInt32 (UInt8.toUInt32 (7 : UInt8)))]!) + (Binary32.ofBits 0x43400000 /- 4*48 -/) * (s.samples[Int32.toNatClampNeg ((((UInt32.toInt32 (UInt8.toUInt32 s.sample_index) - (1 : Int32)) + (2 : Int32) + (1 : Int32)) + (3 : Int32) * UInt32.toInt32 (UInt8.toUInt32 (7 : UInt8)) / (2 : Int32)) % UInt32.toInt32 (UInt8.toUInt32 (7 : UInt8)))]! - s.samples[Int32.toNatClampNeg ((((UInt32.toInt32 (UInt8.toUInt32 s.sample_index) - (1 : Int32)) + -(2 : Int32) + (1 : Int32)) + (3 : Int32) * UInt32.toInt32 (UInt8.toUInt32 (7 : UInt8)) / (2 : Int32)) % UInt32.toInt32 (UInt8.toUInt32 (7 : UInt8)))]!) / UInt32.toBinary32 (s._timestamps[Int32.toNatClampNeg ((((UInt32.toInt32 (UInt8.toUInt32 s.sample_index) - (1 : Int32)) + (2 : Int32) + (1 : Int32)) + (3 : Int32) * UInt32.toInt32 (UInt8.toUInt32 (7 : UInt8)) / (2 : Int32)) % UInt32.toInt32 (UInt8.toUInt32 (7 : UInt8)))]! - s._timestamps[Int32.toNatClampNeg ((((UInt32.toInt32 (UInt8.toUInt32 s.sample_index) - (1 : Int32)) + -(2 : Int32) + (1 : Int32)) + (3 : Int32) * UInt32.toInt32 (UInt8.toUInt32 (7 : UInt8)) / (2 : Int32)) % UInt32.toInt32 (UInt8.toUInt32 (7 : UInt8)))]!) + (Binary32.ofBits 0x43220000 /- 6*27 -/) * (s.samples[Int32.toNatClampNeg ((((UInt32.toInt32 (UInt8.toUInt32 s.sample_index) - (1 : Int32)) + (3 : Int32) + (1 : Int32)) + (3 : Int32) * UInt32.toInt32 (UInt8.toUInt32 (7 : UInt8)) / (2 : Int32)) % UInt32.toInt32 (UInt8.toUInt32 (7 : UInt8)))]! - s.samples[Int32.toNatClampNeg ((((UInt32.toInt32 (UInt8.toUInt32 s.sample_index) - (1 : Int32)) + -(3 : Int32) + (1 : Int32)) + (3 : Int32) * UInt32.toInt32 (UInt8.toUInt32 (7 : UInt8)) / (2 : Int32)) % UInt32.toInt32 (UInt8.toUInt32 (7 : UInt8)))]!) / UInt32.toBinary32 (s._timestamps[Int32.toNatClampNeg ((((UInt32.toInt32 (UInt8.toUInt32 s.sample_index) - (1 : Int32)) + (3 : Int32) + (1 : Int32)) + (3 : Int32) * UInt32.toInt32 (UInt8.toUInt32 (7 : UInt8)) / (2 : Int32)) % UInt32.toInt32 (UInt8.toUInt32 (7 : UInt8)))]! - s._timestamps[Int32.toNatClampNeg ((((UInt32.toInt32 (UInt8.toUInt32 s.sample_index) - (1 : Int32)) + -(3 : Int32) + (1 : Int32)) + (3 : Int32) * UInt32.toInt32 (UInt8.toUInt32 (7 : UInt8)) / (2 : Int32)) % UInt32.toInt32 (UInt8.toUInt32 (7 : UInt8)))]!) + (Binary32.ofBits 0x42800000 /- 8* 8 -/) * (s.samples[Int32.toNatClampNeg ((((UInt32.toInt32 (UInt8.toUInt32 s.sample_index) - (1 : Int32)) + (4 : Int32) + (1 : Int32)) + (3 : Int32) * UInt32.toInt32 (UInt8.toUInt32 (7 : UInt8)) / (2 : Int32)) % UInt32.toInt32 (UInt8.toUInt32 (7 : UInt8)))]! - s.samples[Int32.toNatClampNeg ((((UInt32.toInt32 (UInt8.toUInt32 s.sample_index) - (1 : Int32)) + -(4 : Int32) + (1 : Int32)) + (3 : Int32) * UInt32.toInt32 (UInt8.toUInt32 (7 : UInt8)) / (2 : Int32)) % UInt32.toInt32 (UInt8.toUInt32 (7 : UInt8)))]!) / UInt32.toBinary32 (s._timestamps[Int32.toNatClampNeg ((((UInt32.toInt32 (UInt8.toUInt32 s.sample_index) - (1 : Int32)) + (4 : Int32) + (1 : Int32)) + (3 : Int32) * UInt32.toInt32 (UInt8.toUInt32 (7 : UInt8)) / (2 : Int32)) % UInt32.toInt32 (UInt8.toUInt32 (7 : UInt8)))]! - s._timestamps[Int32.toNatClampNeg ((((UInt32.toInt32 (UInt8.toUInt32 s.sample_index) - (1 : Int32)) + -(4 : Int32) + (1 : Int32)) + (3 : Int32) * UInt32.toInt32 (UInt8.toUInt32 (7 : UInt8)) / (2 : Int32)) % UInt32.toInt32 (UInt8.toUInt32 (7 : UInt8)))]!) + (Binary32.ofBits 0x41200000 /- 10* 1 -/) * (s.samples[Int32.toNatClampNeg ((((UInt32.toInt32 (UInt8.toUInt32 s.sample_index) - (1 : Int32)) + (5 : Int32) + (1 : Int32)) + (3 : Int32) * UInt32.toInt32 (UInt8.toUInt32 (7 : UInt8)) / (2 : Int32)) % UInt32.toInt32 (UInt8.toUInt32 (7 : UInt8)))]! - s.samples[Int32.toNatClampNeg ((((UInt32.toInt32 (UInt8.toUInt32 s.sample_index) - (1 : Int32)) + -(5 : Int32) + (1 : Int32)) + (3 : Int32) * UInt32.toInt32 (UInt8.toUInt32 (7 : UInt8)) / (2 : Int32)) % UInt32.toInt32 (UInt8.toUInt32 (7 : UInt8)))]!) / UInt32.toBinary32 (s._timestamps[Int32.toNatClampNeg ((((UInt32.toInt32 (UInt8.toUInt32 s.sample_index) - (1 : Int32)) + (5 : Int32) + (1 : Int32)) + (3 : Int32) * UInt32.toInt32 (UInt8.toUInt32 (7 : UInt8)) / (2 : Int32)) % UInt32.toInt32 (UInt8.toUInt32 (7 : UInt8)))]! - s._timestamps[Int32.toNatClampNeg ((((UInt32.toInt32 (UInt8.toUInt32 s.sample_index) - (1 : Int32)) + -(5 : Int32) + (1 : Int32)) + (3 : Int32) * UInt32.toInt32 (UInt8.toUInt32 (7 : UInt8)) / (2 : Int32)) % UInt32.toInt32 (UInt8.toUInt32 (7 : UInt8)))]!)
    result := result / (Binary32.ofBits 0x44000000 /- 512 -/)
  else
    result := (Binary32.ofBits 0x00000000 /- 0 -/)
  if Binary32.isNaN result || Binary32.isInf result then
    result := (Binary32.ofBits 0x00000000 /- 0 -/)
  s := { s with _new_data := false }
  s := { s with _last_slope := result }
  return (s, result)

end DerivativeFilterFloat_Size7

namespace DerivativeFilterFloat_Size7

/-- C++ `float FilterWithBuffer<float, 7>::apply(float sample)`, `Filter/FilterWithBuffer.h:104-115` (a member of `FilterWithBuffer<float, 7>`, translated for `DerivativeFilter<float, 7>`). -/
def apply (s : State) (sample : Binary32) : State × Binary32 := Id.run do
  let mut s := s
  let t'1 := s.sample_index
  s := { s with sample_index := s.sample_index + (1 : UInt8) }
  s := { s with samples := s.samples.set! (UInt8.toNat t'1) sample }
  if UInt32.toInt32 (UInt8.toUInt32 s.sample_index) ≥ UInt32.toInt32 (UInt8.toUInt32 (7 : UInt8)) then
    s := { s with sample_index := Int8.toUInt8 (Int32.toInt8 (0 : Int32)) }
  return (s, sample)

/-- C++ `void DerivativeFilter<float, 7>::update(float sample, uint32_t timestamp)`, `Filter/DerivativeFilter.cpp:27-48`. -/
def update (s : State) (sample : Binary32) (timestamp : UInt32) : State := Id.run do
  let mut s := s
  let i : UInt8 := s.sample_index
  let mut i1 : UInt8 := (0 : UInt8)  -- uninitialized in C++; assigned before every read
  if UInt32.toInt32 (UInt8.toUInt32 i) == (0 : Int32) then
    i1 := Int8.toUInt8 (Int32.toInt8 (UInt32.toInt32 (UInt8.toUInt32 (7 : UInt8)) - (1 : Int32)))
  else
    i1 := Int8.toUInt8 (Int32.toInt8 (UInt32.toInt32 (UInt8.toUInt32 i) - (1 : Int32)))
  if s._timestamps[UInt8.toNat i1]! == timestamp then
    return s
  s := { s with _timestamps := s._timestamps.set! (UInt8.toNat i) timestamp }
  let (t'1, _) := apply s sample
  s := t'1
  s := { s with _new_data := true }
  return s

end DerivativeFilterFloat_Size7

namespace LowPassFilter_Vector3_float

/-- C++ `const Vector3<float> & DigitalLPF<Vector3<float>>::get() const`, `Filter/LowPassFilter.cpp:35-37` (a member of `DigitalLPF<Vector3<float>>`, translated for `LowPassFilter<Vector3<float>>`). -/
def get (s : State) : Vector3f.State := Id.run do
  return s.output

end LowPassFilter_Vector3_float

namespace LowPassFilter_Vector3_float

/-- C++ `void LowPassFilter<Vector3<float>>::set_cutoff_frequency(const float & new_cutoff_freq)`, `Filter/LowPassFilter.cpp:107-109`. -/
def set_cutoff_frequency (s : State) (new_cutoff_freq : Binary32) : State := Id.run do
  let mut s := s
  s := { s with cutoff_freq := new_cutoff_freq }
  return s

end LowPassFilter_Vector3_float

end Estimator_lib
