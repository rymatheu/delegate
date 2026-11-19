import ArduLean.Runtime.Boundary
import ArduLean.Vehicle.libraries.AP_Math.AP_Math
import ArduLean.Vehicle.libraries.Filter.Filter
import ArduLean.Vehicle.libraries.AP_Math.AP_Math_2

/-!
ArduPilot `libraries/Filter`, part 2 of 2. Sources: `libraries/Filter/SlewLimiter.cpp`, `libraries/Filter/LowPassFilter.cpp`.

Items of `lean/Vehicle_lib.lean` (the vehicle translation), unchanged; placed by `tools/split_modules.py` (`ArduLean/Vehicle/INDEX.md`).
-/

open FloatLib.Floats (Binary32 Binary64)

set_option linter.unusedVariables false
set_option linter.unreachableTactic false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false

namespace Vehicle_lib

/-- C++ `LowPassFilter<float>::apply : float (const float &, const float &)`, `LowPassFilter.cpp:119-122`. -/
def LowPassFilter'float.apply.body (fp : UInt64) (this : UInt64) (sample : UInt64) (dt : UInt64) : PMem.M Binary32 := do
  let t'1 ← PMem.ldF32 dt
  let t'2 ← PMem.ldF32 (this + 8)
  let t'3 ← calc_lowpass_alpha_dt t'1 t'2
  PMem.stF32 (fp + 0) t'3
  let t'4 ← DigitalLPF'float._apply this sample (fp + 0)
  return t'4

def LowPassFilter'float.apply (this : UInt64) (sample : UInt64) (dt : UInt64) : PMem.M Binary32 := do
  let fp ← PMem.enter 4
  let r ← LowPassFilter'float.apply.body fp this sample dt
  PMem.leave fp
  return r

/-- C++ `SlewLimiter::modifier : float (float, float)`, `SlewLimiter.cpp:45-138`. -/
def SlewLimiter.modifier.body (fp : UInt64) (this : UInt64) (sample : Binary32) (dt : Binary32) : PMem.M Binary32 := do
  let mut sample := sample
  PMem.stF32 (fp + 0) dt
  let t'1 ← PMem.ldF32 (fp + 0)
  let t'2 ← is_positive'float t'1
  if !t'2 then
    return Binary64.toBinary32 ((Binary64.ofBits 0x3ff0000000000000 /- 1 -/))
  let t'3 ← PMem.ldF32 (this + 36)
  let t'4 ← PMem.ldF32 (fp + 0)
  PMem.stF32 (fp + 4) ((sample - t'3) / t'4)
  let t'5 ← LowPassFilter'float.apply (this + 16) (fp + 4) (fp + 0)
  let mut slew_rate : Binary32 := t'5
  PMem.stF32 (this + 36) sample
  let mut now_ms : UInt32 := ((← PMem.clock) / 1000).toUInt32
  let t'6 ← PMem.ldF32 (fp + 0)
  let t'7 ← PMem.ldU64 (this + 8)
  let t'8 ← PMem.ldF32 t'7
  let t'9 ← PMem.ldU64 (this + 8)
  let t'10 ← PMem.ldF32 t'9
  let mut decay_alpha : Binary32 := ((Binary32.fmin t'6 t'8) / t'10)
  let mut attack_alpha : Binary32 := (Binary32.fmin ((Binary32.ofBits 0x40000000 /- 2 -/) * decay_alpha) (Binary32.ofBits 0x3f800000 /- 1 -/))
  let t'11 ← PMem.ldF32 (this + 40)
  if (decide (slew_rate > t'11)) then
    PMem.stF32 (this + 40) slew_rate
    PMem.stU32 (this + 48) now_ms
  else
    let t'12 ← PMem.ldU32 (this + 48)
    if (decide ((now_ms - t'12) > (Int32.toUInt32 ((300 : Int32))))) then
      let t'13 := (this + 40)
      let t'14 ← PMem.ldF32 t'13
      let t'15 := (t'14 * ((Binary32.ofBits 0x3f800000 /- 1 -/) - decay_alpha))
      PMem.stF32 t'13 t'15
  let t'16 ← PMem.ldF32 (this + 44)
  if (decide ((-slew_rate) > t'16)) then
    let t'17 := -slew_rate
    PMem.stF32 (this + 44) t'17
    PMem.stU32 (this + 52) now_ms
  else
    let t'18 ← PMem.ldU32 (this + 52)
    if (decide ((now_ms - t'18) > (Int32.toUInt32 ((300 : Int32))))) then
      let t'19 := (this + 44)
      let t'20 ← PMem.ldF32 t'19
      let t'21 := (t'20 * ((Binary32.ofBits 0x3f800000 /- 1 -/) - decay_alpha))
      PMem.stF32 t'19 t'21
  let t'22 ← PMem.ldF32 (this + 40)
  let t'23 ← PMem.ldF32 (this + 44)
  let mut raw_slew_rate : Binary32 := ((Binary32.ofBits 0x3f000000 /- 1/2 -/) * (t'22 + t'23))
  let t'24 ← PMem.ldF32 (this + 28)
  let t'25 := ((((Binary32.ofBits 0x3f800000 /- 1 -/) - attack_alpha) * t'24) + (attack_alpha * raw_slew_rate))
  PMem.stF32 (this + 28) t'25
  let t'26 ← PMem.ldF32 (this + 28)
  let t'27 := (Binary32.fmin t'26 raw_slew_rate)
  PMem.stF32 (this + 28) t'27
  let t'28 ← PMem.ldU64 this
  let t'29 ← PMem.ldF32 t'28
  if (decide (t'29 ≤ (Int32.toBinary32 ((0 : Int32))))) then
    return Binary64.toBinary32 ((Binary64.ofBits 0x3ff0000000000000 /- 1 -/))
  let t'30 ← PMem.ldF32 (this + 40)
  let t'31 ← PMem.ldU64 this
  let t'32 ← PMem.ldF32 t'31
  let t'33 ← PMem.ldF32 (this + 44)
  let t'34 ← PMem.ldU64 this
  let t'35 ← PMem.ldF32 t'34
  let mut limited_raw_slew_rate : Binary32 := ((Binary32.ofBits 0x3f000000 /- 1/2 -/) * ((Binary32.fmin t'30 ((Binary32.ofBits 0x41200000 /- 10 -/) * t'32)) + (Binary32.fmin t'33 ((Binary32.ofBits 0x41200000 /- 10 -/) * t'35))))
  let t'36 ← PMem.ldB (this + 76)
  let mut sc'39 := !t'36
  if sc'39 then
    let t'37 ← PMem.ldU64 this
    let t'38 ← PMem.ldF32 t'37
    sc'39 := (decide (slew_rate > t'38))
  if sc'39 then
    let t'40 ← PMem.ldU8 (this + 56)
    if (decide ((UInt32.toInt32 (UInt8.toUInt32 (t'40))) ≥ (2 : Int32))) then
      let t'41 := Int8.toUInt8 (Int32.toInt8 ((0 : Int32)))
      PMem.stU8 (this + 56) t'41
    let t'42 ← PMem.ldU8 (this + 56)
    PMem.stU32 ((this + 60) + ((UInt64.toInt64 (UInt8.toUInt64 (t'42))) * 4).toUInt64) now_ms
    let t'43 := (this + 56)
    let t'44 ← PMem.ldU8 t'43
    let t'45 := (t'44 + 1)
    PMem.stU8 t'43 t'45
    PMem.stB (this + 76) true
    PMem.stB (this + 77) false
  let t'46 ← PMem.ldB (this + 77)
  let mut sc'49 := !t'46
  if sc'49 then
    let t'47 ← PMem.ldU64 this
    let t'48 ← PMem.ldF32 t'47
    sc'49 := (decide ((-slew_rate) > t'48))
  if sc'49 then
    let t'50 ← PMem.ldU8 (this + 57)
    if (decide ((UInt32.toInt32 (UInt8.toUInt32 (t'50))) ≥ (2 : Int32))) then
      let t'51 := Int8.toUInt8 (Int32.toInt8 ((0 : Int32)))
      PMem.stU8 (this + 57) t'51
    let t'52 ← PMem.ldU8 (this + 57)
    PMem.stU32 ((this + 68) + ((UInt64.toInt64 (UInt8.toUInt64 (t'52))) * 4).toUInt64) now_ms
    let t'53 := (this + 57)
    let t'54 ← PMem.ldU8 t'53
    let t'55 := (t'54 + 1)
    PMem.stU8 t'53 t'55
    PMem.stB (this + 77) true
    PMem.stB (this + 76) false
  PMem.stU32 (fp + 8) now_ms
  for index'56 in [0:2] do
    let index : UInt8 := UInt8.ofNat index'56
    let t'57 ← MIN'unsigned_int_unsigned_int (fp + 8) ((this + 60) + ((UInt64.toInt64 (UInt8.toUInt64 (index))) * 4).toUInt64)
    let t'58 ← PMem.ldU32 t'57
    PMem.stU32 (fp + 8) t'58
    let t'59 ← MIN'unsigned_int_unsigned_int (fp + 8) ((this + 68) + ((UInt64.toInt64 (UInt8.toUInt64 (index))) * 4).toUInt64)
    let t'60 ← PMem.ldU32 t'59
    PMem.stU32 (fp + 8) t'60
  let mut modifier_input : Binary32 := limited_raw_slew_rate
  let t'61 ← PMem.ldU32 (fp + 8)
  if (decide ((now_ms - t'61) > (Int32.toUInt32 ((((2 : Int32) + (1 : Int32)) * (300 : Int32)))))) then
    let t'62 ← PMem.ldU32 (fp + 8)
    let mut oldest_time_from_window : Binary32 := ((Binary32.ofBits 0x3a83126f /- 20000001/20000000000 -/) * (UInt32.toBinary32 (((now_ms - t'62) - (Int32.toUInt32 ((((2 : Int32) + (1 : Int32)) * (300 : Int32))))))))
    let t'63 ← PMem.ldU64 (this + 8)
    let t'64 ← PMem.ldF32 t'63
    let t'65 := (modifier_input * (Musl.expf.expf ((-oldest_time_from_window) / t'64)))
    modifier_input := t'65
  let t'66 ← PMem.ldF32 (this + 32)
  let t'67 := ((((Binary32.ofBits 0x3f800000 /- 1 -/) - attack_alpha) * t'66) + (attack_alpha * modifier_input))
  PMem.stF32 (this + 32) t'67
  let t'68 ← PMem.ldF32 (this + 32)
  let t'69 := (Binary32.fmin t'68 modifier_input)
  PMem.stF32 (this + 32) t'69
  let mut mod : Binary32 := (Binary32.ofBits 0x3f800000 /- 1 -/)
  let t'70 ← PMem.ldF32 (this + 32)
  let t'71 ← PMem.ldU64 this
  let t'72 ← PMem.ldF32 t'71
  if (decide (t'70 > t'72)) then
    let t'73 ← PMem.ldU64 this
    let t'74 ← PMem.ldF32 t'73
    let t'75 ← PMem.ldU64 this
    let t'76 ← PMem.ldF32 t'75
    let t'77 ← PMem.ldF32 (this + 32)
    let t'78 ← PMem.ldU64 this
    let t'79 ← PMem.ldF32 t'78
    let t'80 := (t'74 / (t'76 + ((Binary32.ofBits 0x3fc00000 /- 3/2 -/) * (t'77 - t'79))))
    mod := t'80
  return mod

def SlewLimiter.modifier (this : UInt64) (sample : Binary32) (dt : Binary32) : PMem.M Binary32 := do
  let fp ← PMem.enter 12
  let r ← SlewLimiter.modifier.body fp this sample dt
  PMem.leave fp
  return r

/-- C++ `LowPassFilter<Vector3<float>>::apply : Vector3<float> (const Vector3<float> &, const float &)`, `LowPassFilter.cpp:119-122`. -/
def LowPassFilter'Vector3_float.apply.body (fp : UInt64) (this : UInt64) (sret : UInt64) (sample : UInt64) (dt : UInt64) : PMem.M Unit := do
  let t'1 ← PMem.ldF32 dt
  let t'2 ← PMem.ldF32 (this + 16)
  let t'3 ← calc_lowpass_alpha_dt t'1 t'2
  PMem.stF32 (fp + 0) t'3
  DigitalLPF'Vector3_float._apply this (fp + 8) sample (fp + 0)
  let t'4 := (fp + 8)
  Vector3'float.Vector3'3 sret t'4
  return ()

def LowPassFilter'Vector3_float.apply (this : UInt64) (sret : UInt64) (sample : UInt64) (dt : UInt64) : PMem.M Unit := do
  let fp ← PMem.enter 20
  let r ← LowPassFilter'Vector3_float.apply.body fp this sret sample dt
  PMem.leave fp
  return r

end Vehicle_lib
