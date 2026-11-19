import ArduLean.Runtime.Memory
import ArduLean.Vehicle.libraries.AP_Math.AP_Math

/-!
ArduPilot `libraries/Filter`, part 1 of 2. Sources: `libraries/Filter/DerivativeFilter.cpp`, `libraries/Filter/LowPassFilter.cpp`, `libraries/Filter/FilterWithBuffer.h`, `libraries/Filter/SlewLimiter.cpp`, `libraries/Filter/FilterClass.h`, `libraries/Filter/LowPassFilter.h`.

Items of `lean/Vehicle_lib.lean` (the vehicle translation), unchanged; placed by `tools/split_modules.py` (`ArduLean/Vehicle/INDEX.md`).
-/

open FloatLib.Floats (Binary32 Binary64)

set_option linter.unusedVariables false
set_option linter.unreachableTactic false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false

namespace Vehicle_lib

/-- C++ `DigitalLPF<float>::reset : void (const float &)`, `LowPassFilter.cpp:41-44`. -/
def DigitalLPF'float.reset (this : UInt64) (value : UInt64) : PMem.M Unit := do
  let t'1 ← PMem.ldF32 value
  PMem.stF32 this t'1
  PMem.stB (this + 4) true
  return ()

/-- C++ `DigitalLPF<float>::_apply : float (const float &, const float &)`, `LowPassFilter.cpp:24-31`. -/
def DigitalLPF'float._apply (this : UInt64) (sample : UInt64) (alpha : UInt64) : PMem.M Binary32 := do
  let t'1 ← PMem.ldF32 this
  let t'2 ← PMem.ldF32 sample
  let t'3 ← PMem.ldF32 this
  let t'4 ← PMem.ldF32 alpha
  let t'5 := (t'1 + ((t'2 - t'3) * t'4))
  PMem.stF32 this t'5
  let t'6 ← PMem.ldB (this + 4)
  if !t'6 then
    PMem.stB (this + 4) true
    let t'7 ← PMem.ldF32 sample
    PMem.stF32 this t'7
  let t'8 ← PMem.ldF32 this
  return t'8

/-- `DigitalLPF'float.get` as a pure function of its arguments (it reads and writes no memory). -/
def DigitalLPF'float.get.pure' (this : UInt64) : Id UInt64 := do
  return this

/-- C++ `DigitalLPF<float>::get : const float &() const`, `LowPassFilter.cpp:35-37`. -/
def DigitalLPF'float.get (this : UInt64) : PMem.M UInt64 :=
  pure (_root_.Vehicle_lib.DigitalLPF'float.get.pure' this)

/-- C++ `FilterWithBuffer<float, 7>::apply : float (float)`, `FilterWithBuffer.h:104-115`. -/
def FilterWithBuffer'float_7.apply (this : UInt64) (sample : Binary32) : PMem.M Binary32 := do
  let mut sample := sample
  let t'1 := (this + 36)
  let t'2 ← PMem.ldU8 t'1
  let t'3 := (t'2 + 1)
  PMem.stU8 t'1 t'3
  PMem.stF32 ((this + 8) + ((UInt64.toInt64 (UInt8.toUInt64 (t'2))) * 4).toUInt64) sample
  let t'4 ← PMem.ldU8 (this + 36)
  if (decide ((UInt32.toInt32 (UInt8.toUInt32 (t'4))) ≥ (UInt32.toInt32 (UInt8.toUInt32 ((7 : UInt8)))))) then
    let t'5 := Int8.toUInt8 (Int32.toInt8 ((0 : Int32)))
    PMem.stU8 (this + 36) t'5
  return sample

/-- C++ `DerivativeFilter<float, 7>::update : void (float, uint32_t)`, `DerivativeFilter.cpp:27-48`. -/
def DerivativeFilter'float_7.update (this : UInt64) (sample : Binary32) (timestamp : UInt32) : PMem.M Unit := do
  let mut sample := sample
  let mut timestamp := timestamp
  let t'1 ← PMem.ldU8 (this + 36)
  let mut i : UInt8 := t'1
  let mut i1 : UInt8 := default  -- uninitialized in C
  if ((UInt32.toInt32 (UInt8.toUInt32 (i))) == (0 : Int32)) then
    let t'2 := Int8.toUInt8 (Int32.toInt8 (((UInt32.toInt32 (UInt8.toUInt32 ((7 : UInt8)))) - (1 : Int32))))
    i1 := t'2
  else
    let t'3 := Int8.toUInt8 (Int32.toInt8 (((UInt32.toInt32 (UInt8.toUInt32 (i))) - (1 : Int32))))
    i1 := t'3
  let t'4 ← PMem.ldU32 ((this + 44) + ((UInt64.toInt64 (UInt8.toUInt64 (i1))) * 4).toUInt64)
  if (t'4 == timestamp) then
    return ()
  PMem.stU32 ((this + 44) + ((UInt64.toInt64 (UInt8.toUInt64 (i))) * 4).toUInt64) timestamp
  let t'5 ← FilterWithBuffer'float_7.apply this sample
  discard <| pure (t'5)
  PMem.stB (this + 37) true
  return ()

/-- C++ `DerivativeFilter<float, 7>::slope : float ()`, `DerivativeFilter.cpp:52-112`. -/
def DerivativeFilter'float_7.slope (this : UInt64) : PMem.M Binary32 := do
  let t'1 ← PMem.ldB (this + 37)
  if !t'1 then
    let t'2 ← PMem.ldF32 (this + 40)
    return t'2
  let mut result : Binary32 := Int32.toBinary32 ((0 : Int32))
  let t'3 ← PMem.ldU32 ((this + 44) + ((Int32.toInt64 (((UInt32.toInt32 (UInt8.toUInt32 ((7 : UInt8)))) - (1 : Int32)))) * 4).toUInt64)
  let t'4 ← PMem.ldU32 ((this + 44) + ((Int32.toInt64 (((UInt32.toInt32 (UInt8.toUInt32 ((7 : UInt8)))) - (2 : Int32)))) * 4).toUInt64)
  if (t'3 == t'4) then
    return Int32.toBinary32 ((0 : Int32))
  let sw'5 := UInt32.toInt32 (UInt8.toUInt32 ((7 : UInt8)))
  if sw'5 == (5 : Int32) then
    let t'6 ← PMem.ldU8 (this + 36)
    let t'7 ← PMem.ldF32 ((this + 8) + ((Int32.toInt64 (((((((UInt32.toInt32 (UInt8.toUInt32 (t'6))) - (1 : Int32)) + (1 : Int32)) + (1 : Int32)) + (((3 : Int32) * (UInt32.toInt32 (UInt8.toUInt32 ((7 : UInt8))))) / (2 : Int32))) % (UInt32.toInt32 (UInt8.toUInt32 ((7 : UInt8))))))) * 4).toUInt64)
    let t'8 ← PMem.ldU8 (this + 36)
    let t'9 ← PMem.ldF32 ((this + 8) + ((Int32.toInt64 (((((((UInt32.toInt32 (UInt8.toUInt32 (t'8))) - (1 : Int32)) + (-(1 : Int32))) + (1 : Int32)) + (((3 : Int32) * (UInt32.toInt32 (UInt8.toUInt32 ((7 : UInt8))))) / (2 : Int32))) % (UInt32.toInt32 (UInt8.toUInt32 ((7 : UInt8))))))) * 4).toUInt64)
    let t'10 ← PMem.ldU8 (this + 36)
    let t'11 ← PMem.ldU32 ((this + 44) + ((Int32.toInt64 (((((((UInt32.toInt32 (UInt8.toUInt32 (t'10))) - (1 : Int32)) + (1 : Int32)) + (1 : Int32)) + (((3 : Int32) * (UInt32.toInt32 (UInt8.toUInt32 ((7 : UInt8))))) / (2 : Int32))) % (UInt32.toInt32 (UInt8.toUInt32 ((7 : UInt8))))))) * 4).toUInt64)
    let t'12 ← PMem.ldU8 (this + 36)
    let t'13 ← PMem.ldU32 ((this + 44) + ((Int32.toInt64 (((((((UInt32.toInt32 (UInt8.toUInt32 (t'12))) - (1 : Int32)) + (-(1 : Int32))) + (1 : Int32)) + (((3 : Int32) * (UInt32.toInt32 (UInt8.toUInt32 ((7 : UInt8))))) / (2 : Int32))) % (UInt32.toInt32 (UInt8.toUInt32 ((7 : UInt8))))))) * 4).toUInt64)
    let t'14 ← PMem.ldU8 (this + 36)
    let t'15 ← PMem.ldF32 ((this + 8) + ((Int32.toInt64 (((((((UInt32.toInt32 (UInt8.toUInt32 (t'14))) - (1 : Int32)) + (2 : Int32)) + (1 : Int32)) + (((3 : Int32) * (UInt32.toInt32 (UInt8.toUInt32 ((7 : UInt8))))) / (2 : Int32))) % (UInt32.toInt32 (UInt8.toUInt32 ((7 : UInt8))))))) * 4).toUInt64)
    let t'16 ← PMem.ldU8 (this + 36)
    let t'17 ← PMem.ldF32 ((this + 8) + ((Int32.toInt64 (((((((UInt32.toInt32 (UInt8.toUInt32 (t'16))) - (1 : Int32)) + (-(2 : Int32))) + (1 : Int32)) + (((3 : Int32) * (UInt32.toInt32 (UInt8.toUInt32 ((7 : UInt8))))) / (2 : Int32))) % (UInt32.toInt32 (UInt8.toUInt32 ((7 : UInt8))))))) * 4).toUInt64)
    let t'18 ← PMem.ldU8 (this + 36)
    let t'19 ← PMem.ldU32 ((this + 44) + ((Int32.toInt64 (((((((UInt32.toInt32 (UInt8.toUInt32 (t'18))) - (1 : Int32)) + (2 : Int32)) + (1 : Int32)) + (((3 : Int32) * (UInt32.toInt32 (UInt8.toUInt32 ((7 : UInt8))))) / (2 : Int32))) % (UInt32.toInt32 (UInt8.toUInt32 ((7 : UInt8))))))) * 4).toUInt64)
    let t'20 ← PMem.ldU8 (this + 36)
    let t'21 ← PMem.ldU32 ((this + 44) + ((Int32.toInt64 (((((((UInt32.toInt32 (UInt8.toUInt32 (t'20))) - (1 : Int32)) + (-(2 : Int32))) + (1 : Int32)) + (((3 : Int32) * (UInt32.toInt32 (UInt8.toUInt32 ((7 : UInt8))))) / (2 : Int32))) % (UInt32.toInt32 (UInt8.toUInt32 ((7 : UInt8))))))) * 4).toUInt64)
    let t'22 := ((((Int32.toBinary32 (((2 : Int32) * (2 : Int32)))) * (t'7 - t'9)) / (UInt32.toBinary32 ((t'11 - t'13)))) + (((Int32.toBinary32 (((4 : Int32) * (1 : Int32)))) * (t'15 - t'17)) / (UInt32.toBinary32 ((t'19 - t'21)))))
    result := t'22
    let t'23 := (result / (Int32.toBinary32 ((8 : Int32))))
    result := t'23
  else if sw'5 == (7 : Int32) then
    let t'24 ← PMem.ldU8 (this + 36)
    let t'25 ← PMem.ldF32 ((this + 8) + ((Int32.toInt64 (((((((UInt32.toInt32 (UInt8.toUInt32 (t'24))) - (1 : Int32)) + (1 : Int32)) + (1 : Int32)) + (((3 : Int32) * (UInt32.toInt32 (UInt8.toUInt32 ((7 : UInt8))))) / (2 : Int32))) % (UInt32.toInt32 (UInt8.toUInt32 ((7 : UInt8))))))) * 4).toUInt64)
    let t'26 ← PMem.ldU8 (this + 36)
    let t'27 ← PMem.ldF32 ((this + 8) + ((Int32.toInt64 (((((((UInt32.toInt32 (UInt8.toUInt32 (t'26))) - (1 : Int32)) + (-(1 : Int32))) + (1 : Int32)) + (((3 : Int32) * (UInt32.toInt32 (UInt8.toUInt32 ((7 : UInt8))))) / (2 : Int32))) % (UInt32.toInt32 (UInt8.toUInt32 ((7 : UInt8))))))) * 4).toUInt64)
    let t'28 ← PMem.ldU8 (this + 36)
    let t'29 ← PMem.ldU32 ((this + 44) + ((Int32.toInt64 (((((((UInt32.toInt32 (UInt8.toUInt32 (t'28))) - (1 : Int32)) + (1 : Int32)) + (1 : Int32)) + (((3 : Int32) * (UInt32.toInt32 (UInt8.toUInt32 ((7 : UInt8))))) / (2 : Int32))) % (UInt32.toInt32 (UInt8.toUInt32 ((7 : UInt8))))))) * 4).toUInt64)
    let t'30 ← PMem.ldU8 (this + 36)
    let t'31 ← PMem.ldU32 ((this + 44) + ((Int32.toInt64 (((((((UInt32.toInt32 (UInt8.toUInt32 (t'30))) - (1 : Int32)) + (-(1 : Int32))) + (1 : Int32)) + (((3 : Int32) * (UInt32.toInt32 (UInt8.toUInt32 ((7 : UInt8))))) / (2 : Int32))) % (UInt32.toInt32 (UInt8.toUInt32 ((7 : UInt8))))))) * 4).toUInt64)
    let t'32 ← PMem.ldU8 (this + 36)
    let t'33 ← PMem.ldF32 ((this + 8) + ((Int32.toInt64 (((((((UInt32.toInt32 (UInt8.toUInt32 (t'32))) - (1 : Int32)) + (2 : Int32)) + (1 : Int32)) + (((3 : Int32) * (UInt32.toInt32 (UInt8.toUInt32 ((7 : UInt8))))) / (2 : Int32))) % (UInt32.toInt32 (UInt8.toUInt32 ((7 : UInt8))))))) * 4).toUInt64)
    let t'34 ← PMem.ldU8 (this + 36)
    let t'35 ← PMem.ldF32 ((this + 8) + ((Int32.toInt64 (((((((UInt32.toInt32 (UInt8.toUInt32 (t'34))) - (1 : Int32)) + (-(2 : Int32))) + (1 : Int32)) + (((3 : Int32) * (UInt32.toInt32 (UInt8.toUInt32 ((7 : UInt8))))) / (2 : Int32))) % (UInt32.toInt32 (UInt8.toUInt32 ((7 : UInt8))))))) * 4).toUInt64)
    let t'36 ← PMem.ldU8 (this + 36)
    let t'37 ← PMem.ldU32 ((this + 44) + ((Int32.toInt64 (((((((UInt32.toInt32 (UInt8.toUInt32 (t'36))) - (1 : Int32)) + (2 : Int32)) + (1 : Int32)) + (((3 : Int32) * (UInt32.toInt32 (UInt8.toUInt32 ((7 : UInt8))))) / (2 : Int32))) % (UInt32.toInt32 (UInt8.toUInt32 ((7 : UInt8))))))) * 4).toUInt64)
    let t'38 ← PMem.ldU8 (this + 36)
    let t'39 ← PMem.ldU32 ((this + 44) + ((Int32.toInt64 (((((((UInt32.toInt32 (UInt8.toUInt32 (t'38))) - (1 : Int32)) + (-(2 : Int32))) + (1 : Int32)) + (((3 : Int32) * (UInt32.toInt32 (UInt8.toUInt32 ((7 : UInt8))))) / (2 : Int32))) % (UInt32.toInt32 (UInt8.toUInt32 ((7 : UInt8))))))) * 4).toUInt64)
    let t'40 ← PMem.ldU8 (this + 36)
    let t'41 ← PMem.ldF32 ((this + 8) + ((Int32.toInt64 (((((((UInt32.toInt32 (UInt8.toUInt32 (t'40))) - (1 : Int32)) + (3 : Int32)) + (1 : Int32)) + (((3 : Int32) * (UInt32.toInt32 (UInt8.toUInt32 ((7 : UInt8))))) / (2 : Int32))) % (UInt32.toInt32 (UInt8.toUInt32 ((7 : UInt8))))))) * 4).toUInt64)
    let t'42 ← PMem.ldU8 (this + 36)
    let t'43 ← PMem.ldF32 ((this + 8) + ((Int32.toInt64 (((((((UInt32.toInt32 (UInt8.toUInt32 (t'42))) - (1 : Int32)) + (-(3 : Int32))) + (1 : Int32)) + (((3 : Int32) * (UInt32.toInt32 (UInt8.toUInt32 ((7 : UInt8))))) / (2 : Int32))) % (UInt32.toInt32 (UInt8.toUInt32 ((7 : UInt8))))))) * 4).toUInt64)
    let t'44 ← PMem.ldU8 (this + 36)
    let t'45 ← PMem.ldU32 ((this + 44) + ((Int32.toInt64 (((((((UInt32.toInt32 (UInt8.toUInt32 (t'44))) - (1 : Int32)) + (3 : Int32)) + (1 : Int32)) + (((3 : Int32) * (UInt32.toInt32 (UInt8.toUInt32 ((7 : UInt8))))) / (2 : Int32))) % (UInt32.toInt32 (UInt8.toUInt32 ((7 : UInt8))))))) * 4).toUInt64)
    let t'46 ← PMem.ldU8 (this + 36)
    let t'47 ← PMem.ldU32 ((this + 44) + ((Int32.toInt64 (((((((UInt32.toInt32 (UInt8.toUInt32 (t'46))) - (1 : Int32)) + (-(3 : Int32))) + (1 : Int32)) + (((3 : Int32) * (UInt32.toInt32 (UInt8.toUInt32 ((7 : UInt8))))) / (2 : Int32))) % (UInt32.toInt32 (UInt8.toUInt32 ((7 : UInt8))))))) * 4).toUInt64)
    let t'48 := (((((Int32.toBinary32 (((2 : Int32) * (5 : Int32)))) * (t'25 - t'27)) / (UInt32.toBinary32 ((t'29 - t'31)))) + (((Int32.toBinary32 (((4 : Int32) * (4 : Int32)))) * (t'33 - t'35)) / (UInt32.toBinary32 ((t'37 - t'39))))) + (((Int32.toBinary32 (((6 : Int32) * (1 : Int32)))) * (t'41 - t'43)) / (UInt32.toBinary32 ((t'45 - t'47)))))
    result := t'48
    let t'49 := (result / (Int32.toBinary32 ((32 : Int32))))
    result := t'49
  else if sw'5 == (9 : Int32) then
    let t'50 ← PMem.ldU8 (this + 36)
    let t'51 ← PMem.ldF32 ((this + 8) + ((Int32.toInt64 (((((((UInt32.toInt32 (UInt8.toUInt32 (t'50))) - (1 : Int32)) + (1 : Int32)) + (1 : Int32)) + (((3 : Int32) * (UInt32.toInt32 (UInt8.toUInt32 ((7 : UInt8))))) / (2 : Int32))) % (UInt32.toInt32 (UInt8.toUInt32 ((7 : UInt8))))))) * 4).toUInt64)
    let t'52 ← PMem.ldU8 (this + 36)
    let t'53 ← PMem.ldF32 ((this + 8) + ((Int32.toInt64 (((((((UInt32.toInt32 (UInt8.toUInt32 (t'52))) - (1 : Int32)) + (-(1 : Int32))) + (1 : Int32)) + (((3 : Int32) * (UInt32.toInt32 (UInt8.toUInt32 ((7 : UInt8))))) / (2 : Int32))) % (UInt32.toInt32 (UInt8.toUInt32 ((7 : UInt8))))))) * 4).toUInt64)
    let t'54 ← PMem.ldU8 (this + 36)
    let t'55 ← PMem.ldU32 ((this + 44) + ((Int32.toInt64 (((((((UInt32.toInt32 (UInt8.toUInt32 (t'54))) - (1 : Int32)) + (1 : Int32)) + (1 : Int32)) + (((3 : Int32) * (UInt32.toInt32 (UInt8.toUInt32 ((7 : UInt8))))) / (2 : Int32))) % (UInt32.toInt32 (UInt8.toUInt32 ((7 : UInt8))))))) * 4).toUInt64)
    let t'56 ← PMem.ldU8 (this + 36)
    let t'57 ← PMem.ldU32 ((this + 44) + ((Int32.toInt64 (((((((UInt32.toInt32 (UInt8.toUInt32 (t'56))) - (1 : Int32)) + (-(1 : Int32))) + (1 : Int32)) + (((3 : Int32) * (UInt32.toInt32 (UInt8.toUInt32 ((7 : UInt8))))) / (2 : Int32))) % (UInt32.toInt32 (UInt8.toUInt32 ((7 : UInt8))))))) * 4).toUInt64)
    let t'58 ← PMem.ldU8 (this + 36)
    let t'59 ← PMem.ldF32 ((this + 8) + ((Int32.toInt64 (((((((UInt32.toInt32 (UInt8.toUInt32 (t'58))) - (1 : Int32)) + (2 : Int32)) + (1 : Int32)) + (((3 : Int32) * (UInt32.toInt32 (UInt8.toUInt32 ((7 : UInt8))))) / (2 : Int32))) % (UInt32.toInt32 (UInt8.toUInt32 ((7 : UInt8))))))) * 4).toUInt64)
    let t'60 ← PMem.ldU8 (this + 36)
    let t'61 ← PMem.ldF32 ((this + 8) + ((Int32.toInt64 (((((((UInt32.toInt32 (UInt8.toUInt32 (t'60))) - (1 : Int32)) + (-(2 : Int32))) + (1 : Int32)) + (((3 : Int32) * (UInt32.toInt32 (UInt8.toUInt32 ((7 : UInt8))))) / (2 : Int32))) % (UInt32.toInt32 (UInt8.toUInt32 ((7 : UInt8))))))) * 4).toUInt64)
    let t'62 ← PMem.ldU8 (this + 36)
    let t'63 ← PMem.ldU32 ((this + 44) + ((Int32.toInt64 (((((((UInt32.toInt32 (UInt8.toUInt32 (t'62))) - (1 : Int32)) + (2 : Int32)) + (1 : Int32)) + (((3 : Int32) * (UInt32.toInt32 (UInt8.toUInt32 ((7 : UInt8))))) / (2 : Int32))) % (UInt32.toInt32 (UInt8.toUInt32 ((7 : UInt8))))))) * 4).toUInt64)
    let t'64 ← PMem.ldU8 (this + 36)
    let t'65 ← PMem.ldU32 ((this + 44) + ((Int32.toInt64 (((((((UInt32.toInt32 (UInt8.toUInt32 (t'64))) - (1 : Int32)) + (-(2 : Int32))) + (1 : Int32)) + (((3 : Int32) * (UInt32.toInt32 (UInt8.toUInt32 ((7 : UInt8))))) / (2 : Int32))) % (UInt32.toInt32 (UInt8.toUInt32 ((7 : UInt8))))))) * 4).toUInt64)
    let t'66 ← PMem.ldU8 (this + 36)
    let t'67 ← PMem.ldF32 ((this + 8) + ((Int32.toInt64 (((((((UInt32.toInt32 (UInt8.toUInt32 (t'66))) - (1 : Int32)) + (3 : Int32)) + (1 : Int32)) + (((3 : Int32) * (UInt32.toInt32 (UInt8.toUInt32 ((7 : UInt8))))) / (2 : Int32))) % (UInt32.toInt32 (UInt8.toUInt32 ((7 : UInt8))))))) * 4).toUInt64)
    let t'68 ← PMem.ldU8 (this + 36)
    let t'69 ← PMem.ldF32 ((this + 8) + ((Int32.toInt64 (((((((UInt32.toInt32 (UInt8.toUInt32 (t'68))) - (1 : Int32)) + (-(3 : Int32))) + (1 : Int32)) + (((3 : Int32) * (UInt32.toInt32 (UInt8.toUInt32 ((7 : UInt8))))) / (2 : Int32))) % (UInt32.toInt32 (UInt8.toUInt32 ((7 : UInt8))))))) * 4).toUInt64)
    let t'70 ← PMem.ldU8 (this + 36)
    let t'71 ← PMem.ldU32 ((this + 44) + ((Int32.toInt64 (((((((UInt32.toInt32 (UInt8.toUInt32 (t'70))) - (1 : Int32)) + (3 : Int32)) + (1 : Int32)) + (((3 : Int32) * (UInt32.toInt32 (UInt8.toUInt32 ((7 : UInt8))))) / (2 : Int32))) % (UInt32.toInt32 (UInt8.toUInt32 ((7 : UInt8))))))) * 4).toUInt64)
    let t'72 ← PMem.ldU8 (this + 36)
    let t'73 ← PMem.ldU32 ((this + 44) + ((Int32.toInt64 (((((((UInt32.toInt32 (UInt8.toUInt32 (t'72))) - (1 : Int32)) + (-(3 : Int32))) + (1 : Int32)) + (((3 : Int32) * (UInt32.toInt32 (UInt8.toUInt32 ((7 : UInt8))))) / (2 : Int32))) % (UInt32.toInt32 (UInt8.toUInt32 ((7 : UInt8))))))) * 4).toUInt64)
    let t'74 ← PMem.ldU8 (this + 36)
    let t'75 ← PMem.ldF32 ((this + 8) + ((Int32.toInt64 (((((((UInt32.toInt32 (UInt8.toUInt32 (t'74))) - (1 : Int32)) + (4 : Int32)) + (1 : Int32)) + (((3 : Int32) * (UInt32.toInt32 (UInt8.toUInt32 ((7 : UInt8))))) / (2 : Int32))) % (UInt32.toInt32 (UInt8.toUInt32 ((7 : UInt8))))))) * 4).toUInt64)
    let t'76 ← PMem.ldU8 (this + 36)
    let t'77 ← PMem.ldF32 ((this + 8) + ((Int32.toInt64 (((((((UInt32.toInt32 (UInt8.toUInt32 (t'76))) - (1 : Int32)) + (-(4 : Int32))) + (1 : Int32)) + (((3 : Int32) * (UInt32.toInt32 (UInt8.toUInt32 ((7 : UInt8))))) / (2 : Int32))) % (UInt32.toInt32 (UInt8.toUInt32 ((7 : UInt8))))))) * 4).toUInt64)
    let t'78 ← PMem.ldU8 (this + 36)
    let t'79 ← PMem.ldU32 ((this + 44) + ((Int32.toInt64 (((((((UInt32.toInt32 (UInt8.toUInt32 (t'78))) - (1 : Int32)) + (4 : Int32)) + (1 : Int32)) + (((3 : Int32) * (UInt32.toInt32 (UInt8.toUInt32 ((7 : UInt8))))) / (2 : Int32))) % (UInt32.toInt32 (UInt8.toUInt32 ((7 : UInt8))))))) * 4).toUInt64)
    let t'80 ← PMem.ldU8 (this + 36)
    let t'81 ← PMem.ldU32 ((this + 44) + ((Int32.toInt64 (((((((UInt32.toInt32 (UInt8.toUInt32 (t'80))) - (1 : Int32)) + (-(4 : Int32))) + (1 : Int32)) + (((3 : Int32) * (UInt32.toInt32 (UInt8.toUInt32 ((7 : UInt8))))) / (2 : Int32))) % (UInt32.toInt32 (UInt8.toUInt32 ((7 : UInt8))))))) * 4).toUInt64)
    let t'82 := ((((((Int32.toBinary32 (((2 : Int32) * (14 : Int32)))) * (t'51 - t'53)) / (UInt32.toBinary32 ((t'55 - t'57)))) + (((Int32.toBinary32 (((4 : Int32) * (14 : Int32)))) * (t'59 - t'61)) / (UInt32.toBinary32 ((t'63 - t'65))))) + (((Int32.toBinary32 (((6 : Int32) * (6 : Int32)))) * (t'67 - t'69)) / (UInt32.toBinary32 ((t'71 - t'73))))) + (((Int32.toBinary32 (((8 : Int32) * (1 : Int32)))) * (t'75 - t'77)) / (UInt32.toBinary32 ((t'79 - t'81)))))
    result := t'82
    let t'83 := (result / (Int32.toBinary32 ((128 : Int32))))
    result := t'83
  else if sw'5 == (11 : Int32) then
    let t'84 ← PMem.ldU8 (this + 36)
    let t'85 ← PMem.ldF32 ((this + 8) + ((Int32.toInt64 (((((((UInt32.toInt32 (UInt8.toUInt32 (t'84))) - (1 : Int32)) + (1 : Int32)) + (1 : Int32)) + (((3 : Int32) * (UInt32.toInt32 (UInt8.toUInt32 ((7 : UInt8))))) / (2 : Int32))) % (UInt32.toInt32 (UInt8.toUInt32 ((7 : UInt8))))))) * 4).toUInt64)
    let t'86 ← PMem.ldU8 (this + 36)
    let t'87 ← PMem.ldF32 ((this + 8) + ((Int32.toInt64 (((((((UInt32.toInt32 (UInt8.toUInt32 (t'86))) - (1 : Int32)) + (-(1 : Int32))) + (1 : Int32)) + (((3 : Int32) * (UInt32.toInt32 (UInt8.toUInt32 ((7 : UInt8))))) / (2 : Int32))) % (UInt32.toInt32 (UInt8.toUInt32 ((7 : UInt8))))))) * 4).toUInt64)
    let t'88 ← PMem.ldU8 (this + 36)
    let t'89 ← PMem.ldU32 ((this + 44) + ((Int32.toInt64 (((((((UInt32.toInt32 (UInt8.toUInt32 (t'88))) - (1 : Int32)) + (1 : Int32)) + (1 : Int32)) + (((3 : Int32) * (UInt32.toInt32 (UInt8.toUInt32 ((7 : UInt8))))) / (2 : Int32))) % (UInt32.toInt32 (UInt8.toUInt32 ((7 : UInt8))))))) * 4).toUInt64)
    let t'90 ← PMem.ldU8 (this + 36)
    let t'91 ← PMem.ldU32 ((this + 44) + ((Int32.toInt64 (((((((UInt32.toInt32 (UInt8.toUInt32 (t'90))) - (1 : Int32)) + (-(1 : Int32))) + (1 : Int32)) + (((3 : Int32) * (UInt32.toInt32 (UInt8.toUInt32 ((7 : UInt8))))) / (2 : Int32))) % (UInt32.toInt32 (UInt8.toUInt32 ((7 : UInt8))))))) * 4).toUInt64)
    let t'92 ← PMem.ldU8 (this + 36)
    let t'93 ← PMem.ldF32 ((this + 8) + ((Int32.toInt64 (((((((UInt32.toInt32 (UInt8.toUInt32 (t'92))) - (1 : Int32)) + (2 : Int32)) + (1 : Int32)) + (((3 : Int32) * (UInt32.toInt32 (UInt8.toUInt32 ((7 : UInt8))))) / (2 : Int32))) % (UInt32.toInt32 (UInt8.toUInt32 ((7 : UInt8))))))) * 4).toUInt64)
    let t'94 ← PMem.ldU8 (this + 36)
    let t'95 ← PMem.ldF32 ((this + 8) + ((Int32.toInt64 (((((((UInt32.toInt32 (UInt8.toUInt32 (t'94))) - (1 : Int32)) + (-(2 : Int32))) + (1 : Int32)) + (((3 : Int32) * (UInt32.toInt32 (UInt8.toUInt32 ((7 : UInt8))))) / (2 : Int32))) % (UInt32.toInt32 (UInt8.toUInt32 ((7 : UInt8))))))) * 4).toUInt64)
    let t'96 ← PMem.ldU8 (this + 36)
    let t'97 ← PMem.ldU32 ((this + 44) + ((Int32.toInt64 (((((((UInt32.toInt32 (UInt8.toUInt32 (t'96))) - (1 : Int32)) + (2 : Int32)) + (1 : Int32)) + (((3 : Int32) * (UInt32.toInt32 (UInt8.toUInt32 ((7 : UInt8))))) / (2 : Int32))) % (UInt32.toInt32 (UInt8.toUInt32 ((7 : UInt8))))))) * 4).toUInt64)
    let t'98 ← PMem.ldU8 (this + 36)
    let t'99 ← PMem.ldU32 ((this + 44) + ((Int32.toInt64 (((((((UInt32.toInt32 (UInt8.toUInt32 (t'98))) - (1 : Int32)) + (-(2 : Int32))) + (1 : Int32)) + (((3 : Int32) * (UInt32.toInt32 (UInt8.toUInt32 ((7 : UInt8))))) / (2 : Int32))) % (UInt32.toInt32 (UInt8.toUInt32 ((7 : UInt8))))))) * 4).toUInt64)
    let t'100 ← PMem.ldU8 (this + 36)
    let t'101 ← PMem.ldF32 ((this + 8) + ((Int32.toInt64 (((((((UInt32.toInt32 (UInt8.toUInt32 (t'100))) - (1 : Int32)) + (3 : Int32)) + (1 : Int32)) + (((3 : Int32) * (UInt32.toInt32 (UInt8.toUInt32 ((7 : UInt8))))) / (2 : Int32))) % (UInt32.toInt32 (UInt8.toUInt32 ((7 : UInt8))))))) * 4).toUInt64)
    let t'102 ← PMem.ldU8 (this + 36)
    let t'103 ← PMem.ldF32 ((this + 8) + ((Int32.toInt64 (((((((UInt32.toInt32 (UInt8.toUInt32 (t'102))) - (1 : Int32)) + (-(3 : Int32))) + (1 : Int32)) + (((3 : Int32) * (UInt32.toInt32 (UInt8.toUInt32 ((7 : UInt8))))) / (2 : Int32))) % (UInt32.toInt32 (UInt8.toUInt32 ((7 : UInt8))))))) * 4).toUInt64)
    let t'104 ← PMem.ldU8 (this + 36)
    let t'105 ← PMem.ldU32 ((this + 44) + ((Int32.toInt64 (((((((UInt32.toInt32 (UInt8.toUInt32 (t'104))) - (1 : Int32)) + (3 : Int32)) + (1 : Int32)) + (((3 : Int32) * (UInt32.toInt32 (UInt8.toUInt32 ((7 : UInt8))))) / (2 : Int32))) % (UInt32.toInt32 (UInt8.toUInt32 ((7 : UInt8))))))) * 4).toUInt64)
    let t'106 ← PMem.ldU8 (this + 36)
    let t'107 ← PMem.ldU32 ((this + 44) + ((Int32.toInt64 (((((((UInt32.toInt32 (UInt8.toUInt32 (t'106))) - (1 : Int32)) + (-(3 : Int32))) + (1 : Int32)) + (((3 : Int32) * (UInt32.toInt32 (UInt8.toUInt32 ((7 : UInt8))))) / (2 : Int32))) % (UInt32.toInt32 (UInt8.toUInt32 ((7 : UInt8))))))) * 4).toUInt64)
    let t'108 ← PMem.ldU8 (this + 36)
    let t'109 ← PMem.ldF32 ((this + 8) + ((Int32.toInt64 (((((((UInt32.toInt32 (UInt8.toUInt32 (t'108))) - (1 : Int32)) + (4 : Int32)) + (1 : Int32)) + (((3 : Int32) * (UInt32.toInt32 (UInt8.toUInt32 ((7 : UInt8))))) / (2 : Int32))) % (UInt32.toInt32 (UInt8.toUInt32 ((7 : UInt8))))))) * 4).toUInt64)
    let t'110 ← PMem.ldU8 (this + 36)
    let t'111 ← PMem.ldF32 ((this + 8) + ((Int32.toInt64 (((((((UInt32.toInt32 (UInt8.toUInt32 (t'110))) - (1 : Int32)) + (-(4 : Int32))) + (1 : Int32)) + (((3 : Int32) * (UInt32.toInt32 (UInt8.toUInt32 ((7 : UInt8))))) / (2 : Int32))) % (UInt32.toInt32 (UInt8.toUInt32 ((7 : UInt8))))))) * 4).toUInt64)
    let t'112 ← PMem.ldU8 (this + 36)
    let t'113 ← PMem.ldU32 ((this + 44) + ((Int32.toInt64 (((((((UInt32.toInt32 (UInt8.toUInt32 (t'112))) - (1 : Int32)) + (4 : Int32)) + (1 : Int32)) + (((3 : Int32) * (UInt32.toInt32 (UInt8.toUInt32 ((7 : UInt8))))) / (2 : Int32))) % (UInt32.toInt32 (UInt8.toUInt32 ((7 : UInt8))))))) * 4).toUInt64)
    let t'114 ← PMem.ldU8 (this + 36)
    let t'115 ← PMem.ldU32 ((this + 44) + ((Int32.toInt64 (((((((UInt32.toInt32 (UInt8.toUInt32 (t'114))) - (1 : Int32)) + (-(4 : Int32))) + (1 : Int32)) + (((3 : Int32) * (UInt32.toInt32 (UInt8.toUInt32 ((7 : UInt8))))) / (2 : Int32))) % (UInt32.toInt32 (UInt8.toUInt32 ((7 : UInt8))))))) * 4).toUInt64)
    let t'116 ← PMem.ldU8 (this + 36)
    let t'117 ← PMem.ldF32 ((this + 8) + ((Int32.toInt64 (((((((UInt32.toInt32 (UInt8.toUInt32 (t'116))) - (1 : Int32)) + (5 : Int32)) + (1 : Int32)) + (((3 : Int32) * (UInt32.toInt32 (UInt8.toUInt32 ((7 : UInt8))))) / (2 : Int32))) % (UInt32.toInt32 (UInt8.toUInt32 ((7 : UInt8))))))) * 4).toUInt64)
    let t'118 ← PMem.ldU8 (this + 36)
    let t'119 ← PMem.ldF32 ((this + 8) + ((Int32.toInt64 (((((((UInt32.toInt32 (UInt8.toUInt32 (t'118))) - (1 : Int32)) + (-(5 : Int32))) + (1 : Int32)) + (((3 : Int32) * (UInt32.toInt32 (UInt8.toUInt32 ((7 : UInt8))))) / (2 : Int32))) % (UInt32.toInt32 (UInt8.toUInt32 ((7 : UInt8))))))) * 4).toUInt64)
    let t'120 ← PMem.ldU8 (this + 36)
    let t'121 ← PMem.ldU32 ((this + 44) + ((Int32.toInt64 (((((((UInt32.toInt32 (UInt8.toUInt32 (t'120))) - (1 : Int32)) + (5 : Int32)) + (1 : Int32)) + (((3 : Int32) * (UInt32.toInt32 (UInt8.toUInt32 ((7 : UInt8))))) / (2 : Int32))) % (UInt32.toInt32 (UInt8.toUInt32 ((7 : UInt8))))))) * 4).toUInt64)
    let t'122 ← PMem.ldU8 (this + 36)
    let t'123 ← PMem.ldU32 ((this + 44) + ((Int32.toInt64 (((((((UInt32.toInt32 (UInt8.toUInt32 (t'122))) - (1 : Int32)) + (-(5 : Int32))) + (1 : Int32)) + (((3 : Int32) * (UInt32.toInt32 (UInt8.toUInt32 ((7 : UInt8))))) / (2 : Int32))) % (UInt32.toInt32 (UInt8.toUInt32 ((7 : UInt8))))))) * 4).toUInt64)
    let t'124 := (((((((Int32.toBinary32 (((2 : Int32) * (42 : Int32)))) * (t'85 - t'87)) / (UInt32.toBinary32 ((t'89 - t'91)))) + (((Int32.toBinary32 (((4 : Int32) * (48 : Int32)))) * (t'93 - t'95)) / (UInt32.toBinary32 ((t'97 - t'99))))) + (((Int32.toBinary32 (((6 : Int32) * (27 : Int32)))) * (t'101 - t'103)) / (UInt32.toBinary32 ((t'105 - t'107))))) + (((Int32.toBinary32 (((8 : Int32) * (8 : Int32)))) * (t'109 - t'111)) / (UInt32.toBinary32 ((t'113 - t'115))))) + (((Int32.toBinary32 (((10 : Int32) * (1 : Int32)))) * (t'117 - t'119)) / (UInt32.toBinary32 ((t'121 - t'123)))))
    result := t'124
    let t'125 := (result / (Int32.toBinary32 ((512 : Int32))))
    result := t'125
  else
    let t'126 := Int32.toBinary32 ((0 : Int32))
    result := t'126
  if ((Binary32.isNaN result) || (Binary32.isInf result)) then
    let t'127 := Int32.toBinary32 ((0 : Int32))
    result := t'127
  PMem.stB (this + 37) false
  PMem.stF32 (this + 40) result
  return result

/-- C++ `LowPassFilter<float>::set_cutoff_frequency : void (const float &)`, `LowPassFilter.cpp:107-109`. -/
def LowPassFilter'float.set_cutoff_frequency (this : UInt64) (new_cutoff_freq : UInt64) : PMem.M Unit := do
  let t'1 ← PMem.ldF32 new_cutoff_freq
  PMem.stF32 (this + 8) t'1
  return ()

/-- C++ `DigitalLPF<float>::DigitalLPF : void ()`, `LowPassFilter.cpp:17-20`. -/
def DigitalLPF'float.DigitalLPF (this : UInt64) : PMem.M Unit := do
  let t'1 := (Binary32.ofBits 0x00000000 /- 0 -/)
  PMem.stF32 this t'1
  return ()

/-- C++ `LowPassFilter<float>::LowPassFilter : void ()`, `LowPassFilter.h:110-?`. -/
def LowPassFilter'float.LowPassFilter (this : UInt64) : PMem.M Unit := do
  DigitalLPF'float.DigitalLPF this
  return ()

/-- C++ `SlewLimiter::SlewLimiter : void (const float &, const float &)`, `SlewLimiter.cpp:33-39`. -/
def SlewLimiter.SlewLimiter.body (fp : UInt64) (this : UInt64) (_slew_rate_max : UInt64) (_slew_rate_tau : UInt64) : PMem.M Unit := do
  PMem.stU64 (this + 0) _slew_rate_max
  PMem.stU64 (this + 8) _slew_rate_tau
  LowPassFilter'float.LowPassFilter (this + 16)
  PMem.stF32 (fp + 0) (Binary32.ofBits 0x41c80000 /- 25 -/)
  LowPassFilter'float.set_cutoff_frequency (this + 16) (fp + 0)
  PMem.stF32 (fp + 4) (Binary64.toBinary32 ((Binary64.ofBits 0x0000000000000000 /- 0 -/)))
  DigitalLPF'float.reset (this + 16) (fp + 4)
  return ()

def SlewLimiter.SlewLimiter (this : UInt64) (_slew_rate_max : UInt64) (_slew_rate_tau : UInt64) : PMem.M Unit := do
  let fp ← PMem.enter 8
  let r ← SlewLimiter.SlewLimiter.body fp this _slew_rate_max _slew_rate_tau
  PMem.leave fp
  return r

/-- `Filter'float.Filter` as a pure function of its arguments (it reads and writes no memory). -/
def Filter'float.Filter.pure' (this : UInt64) : Id Unit := do
  return ()

/-- C++ `Filter<float>::Filter : void () noexcept`, `FilterClass.h:?-?`. -/
def Filter'float.Filter (this : UInt64) : PMem.M Unit :=
  pure (_root_.Vehicle_lib.Filter'float.Filter.pure' this)

/-- C++ `FilterWithBuffer<float, 7>::reset : void ()`, `FilterWithBuffer.h:91-100`. -/
def FilterWithBuffer'float_7.reset (this : UInt64) : PMem.M Unit := do
  let mut i : Int8 := Int32.toInt8 ((0 : Int32))
  let mut first'1 := true
  for _ in PMem.loopFuel do
    if !first'1 then
      let t'2 := i
      let t'3 := (t'2 + 1)
      i := t'3
      pure ()
    first'1 := false
    if !((decide ((Int8.toInt32 (i)) < (UInt32.toInt32 (UInt8.toUInt32 ((7 : UInt8))))))) then break
    let t'4 := Int32.toBinary32 ((0 : Int32))
    PMem.stF32 ((this + 8) + ((Int8.toInt64 (i)) * 4).toUInt64) t'4
  let t'5 := Int8.toUInt8 (Int32.toInt8 ((0 : Int32)))
  PMem.stU8 (this + 36) t'5
  return ()

/-- C++ `DerivativeFilter<float, 7>::reset : void ()`, `DerivativeFilter.cpp:116-120`. -/
def DerivativeFilter'float_7.reset (this : UInt64) : PMem.M Unit := do
  FilterWithBuffer'float_7.reset this
  return ()

/-- C++ `SlewLimiter::get_slew_rate : float () const`, `AP_Common.h:28-30`. -/
def SlewLimiter.get_slew_rate (this : UInt64) : PMem.M Binary32 := do
  let t'1 ← PMem.ldF32 (this + 28)
  return t'1

/-- C++ `DigitalLPF<Vector3<float>>::_apply : Vector3<float> (const Vector3<float> &, const float &)`, `LowPassFilter.cpp:24-31`. -/
def DigitalLPF'Vector3_float._apply.body (fp : UInt64) (this : UInt64) (sret : UInt64) (sample : UInt64) (alpha : UInt64) : PMem.M Unit := do
  Vector3'float.operator_'2 sample (fp + 0) this
  let t'1 := (fp + 0)
  let t'2 ← PMem.ldF32 alpha
  Vector3'float.operator_ t'1 (fp + 16) t'2
  let t'3 := (fp + 16)
  let t'4 ← Vector3'float.operator__'3 this t'3
  discard <| pure (t'4)
  let t'5 ← PMem.ldB (this + 12)
  if !t'5 then
    PMem.stB (this + 12) true
    discard <| PMem.memcpy this sample 12
    discard <| pure (this)
  Vector3'float.Vector3'4 sret this
  return ()

def DigitalLPF'Vector3_float._apply (this : UInt64) (sret : UInt64) (sample : UInt64) (alpha : UInt64) : PMem.M Unit := do
  let fp ← PMem.enter 28
  let r ← DigitalLPF'Vector3_float._apply.body fp this sret sample alpha
  PMem.leave fp
  return r

/-- `DigitalLPF'Vector3_float.get` as a pure function of its arguments (it reads and writes no memory). -/
def DigitalLPF'Vector3_float.get.pure' (this : UInt64) : Id UInt64 := do
  return this

/-- C++ `DigitalLPF<Vector3<float>>::get : const Vector3<float> &() const`, `LowPassFilter.cpp:35-37`. -/
def DigitalLPF'Vector3_float.get (this : UInt64) : PMem.M UInt64 :=
  pure (_root_.Vehicle_lib.DigitalLPF'Vector3_float.get.pure' this)

/-- C++ `LowPassFilter<float>::LowPassFilter : void (const float &)`, `LowPassFilter.cpp:100-103`. -/
def LowPassFilter'float.LowPassFilter'2 (this : UInt64) (new_cutoff_freq : UInt64) : PMem.M Unit := do
  DigitalLPF'float.DigitalLPF this
  LowPassFilter'float.set_cutoff_frequency this new_cutoff_freq
  return ()

/-- C++ `DigitalLPF<Vector3<float>>::DigitalLPF : void ()`, `LowPassFilter.cpp:17-20`. -/
def DigitalLPF'Vector3_float.DigitalLPF.body (fp : UInt64) (this : UInt64) : PMem.M Unit := do
  Vector3'float.Vector3'2 (this + 0)
  Vector3'float.Vector3'2 (fp + 0)
  discard <| PMem.memcpy this (fp + 0) 12
  discard <| pure (this)
  return ()

def DigitalLPF'Vector3_float.DigitalLPF (this : UInt64) : PMem.M Unit := do
  let fp ← PMem.enter 12
  let r ← DigitalLPF'Vector3_float.DigitalLPF.body fp this
  PMem.leave fp
  return r

/-- C++ `LowPassFilter<Vector3<float>>::set_cutoff_frequency : void (const float &)`, `LowPassFilter.cpp:107-109`. -/
def LowPassFilter'Vector3_float.set_cutoff_frequency (this : UInt64) (new_cutoff_freq : UInt64) : PMem.M Unit := do
  let t'1 ← PMem.ldF32 new_cutoff_freq
  PMem.stF32 (this + 16) t'1
  return ()

/-- C++ `LowPassFilter<Vector3<float>>::LowPassFilter : void (const float &)`, `LowPassFilter.cpp:100-103`. -/
def LowPassFilter'Vector3_float.LowPassFilter (this : UInt64) (new_cutoff_freq : UInt64) : PMem.M Unit := do
  DigitalLPF'Vector3_float.DigitalLPF this
  LowPassFilter'Vector3_float.set_cutoff_frequency this new_cutoff_freq
  return ()

end Vehicle_lib
