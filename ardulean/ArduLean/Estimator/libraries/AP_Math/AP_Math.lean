import ArduLean.Musl.acosf
import ArduLean.Musl.asinf
import ArduLean.Musl.atan2
import ArduLean.Musl.atan2f
import ArduLean.Musl.cos
import ArduLean.Musl.cosf
import ArduLean.Musl.fmod
import ArduLean.Musl.fmodf
import ArduLean.Musl.sin
import ArduLean.Musl.sinf

/-!
ArduPilot `libraries/AP_Math`, part 1 of 3. Sources: `libraries/AP_Math/vector3.cpp`, `libraries/AP_Math/quaternion.cpp`, `libraries/AP_Math/matrix3.cpp`, `libraries/AP_Math/matrix3.h`, `libraries/AP_Math/rotations.h`, `libraries/AP_Math/AP_Math.h`, `libraries/AP_Math/AP_Math.cpp`, `libraries/AP_Math/vector3.h` and 5 more.

Items of `lean/Estimator_lib.lean` (the estimator translation), unchanged; placed by `tools/split_modules.py` (`ArduLean/Estimator/INDEX.md`).
-/

open FloatLib.Floats (Binary32 Binary64)

set_option maxRecDepth 200000
-- AP_DAL's `const log_RISH old_RISH = _RISH;` read only by WRITE_REPLAY_BLOCK_IFCHANGED, which is `(void)old`
-- without logging (HAL_LOGGING_ENABLED 0): an unused binding, as in the C++
set_option linter.unusedVariables false

namespace Estimator_lib

namespace Vector3f

/-- State of C++ `Vector3<float>` (`AP_Math/vector3.cpp:632`): its data members. -/
structure State where
  /-- `float x` of `Vector3<float>` (`AP_Math/vector3.h:76`). -/
  x : Binary32 := (Binary32.ofBits 0x00000000 /- 0.0 -/)
  /-- `float y` of `Vector3<float>` (`AP_Math/vector3.h:76`). -/
  y : Binary32 := (Binary32.ofBits 0x00000000 /- 0.0 -/)
  /-- `float z` of `Vector3<float>` (`AP_Math/vector3.h:76`). -/
  z : Binary32 := (Binary32.ofBits 0x00000000 /- 0.0 -/)
deriving Inhabited

end Vector3f

namespace Matrix3f

/-- State of C++ `Matrix3<float>` (`AP_Math/matrix3.cpp:261`): its data members. -/
structure State where
  /-- `Vector3<float> a` of `Matrix3<float>` (`AP_Math/matrix3.h:54`). -/
  a : Vector3f.State := {}
  /-- `Vector3<float> b` of `Matrix3<float>` (`AP_Math/matrix3.h:54`). -/
  b : Vector3f.State := {}
  /-- `Vector3<float> c` of `Matrix3<float>` (`AP_Math/matrix3.h:54`). -/
  c : Vector3f.State := {}
deriving Inhabited

end Matrix3f

namespace Vector3f

/-- C++ `Vector3<float>::Vector3()`, `AP_Math/vector3.h:79-82`. -/
def init_void : State := Id.run do
  let mut s : State := {}
  s := { s with x := (Binary32.ofBits 0x00000000 /- 0 -/) }
  s := { s with y := (Binary32.ofBits 0x00000000 /- 0 -/) }
  s := { s with z := (Binary32.ofBits 0x00000000 /- 0 -/) }
  return s

end Vector3f

namespace Matrix3f

/-- C++ `Matrix3<float>::Matrix3()`, `AP_Math/matrix3.h:58`. -/
def init_void : State := Id.run do
  let mut s : State := {}
  s := { s with a := Vector3f.init_void }
  s := { s with b := Vector3f.init_void }
  s := { s with c := Vector3f.init_void }
  return s

end Matrix3f

namespace Quaternion

/-- State of C++ `QuaternionT<float>` (`AP_Math/quaternion.cpp:846`): its data members. -/
structure State where
  /-- `float q1` of `QuaternionT<float>` (`AP_Math/quaternion.h:31`). -/
  q1 : Binary32 := (Binary32.ofBits 0x00000000 /- 0.0 -/)
  /-- `float q2` of `QuaternionT<float>` (`AP_Math/quaternion.h:31`). -/
  q2 : Binary32 := (Binary32.ofBits 0x00000000 /- 0.0 -/)
  /-- `float q3` of `QuaternionT<float>` (`AP_Math/quaternion.h:31`). -/
  q3 : Binary32 := (Binary32.ofBits 0x00000000 /- 0.0 -/)
  /-- `float q4` of `QuaternionT<float>` (`AP_Math/quaternion.h:31`). -/
  q4 : Binary32 := (Binary32.ofBits 0x00000000 /- 0.0 -/)
deriving Inhabited

/-- C++ `QuaternionT<float>::QuaternionT()`, `AP_Math/quaternion.h:35-39`. -/
def init_void : State := Id.run do
  let mut s : State := {}
  s := { s with q1 := (Binary32.ofBits 0x3f800000 /- 1 -/) }
  s := { s with q4 := (Binary32.ofBits 0x00000000 /- 0 -/) }
  s := { s with q3 := s.q4 }
  s := { s with q2 := s.q3 }
  return s

end Quaternion

namespace Vector2f

/-- State of C++ `Vector2<float>` (`AP_Math/vector2.cpp:452`): its data members. -/
structure State where
  /-- `float x` of `Vector2<float>` (`AP_Math/vector2.h:47`). -/
  x : Binary32 := (Binary32.ofBits 0x00000000 /- 0.0 -/)
  /-- `float y` of `Vector2<float>` (`AP_Math/vector2.h:47`). -/
  y : Binary32 := (Binary32.ofBits 0x00000000 /- 0.0 -/)
deriving Inhabited

end Vector2f

namespace Vector2p

/-- State of C++ `Vector2<double>` (`AP_Math/vector2.cpp:453`): its data members. -/
structure State where
  /-- `double x` of `Vector2<double>` (`AP_Math/vector2.h:47`). -/
  x : Binary64 := (Binary64.ofBits 0x0000000000000000 /- 0.0 -/)
  /-- `double y` of `Vector2<double>` (`AP_Math/vector2.h:47`). -/
  y : Binary64 := (Binary64.ofBits 0x0000000000000000 /- 0.0 -/)
deriving Inhabited

end Vector2p

namespace Vector2f

/-- C++ `Vector2<float>::Vector2(const float x0, const float y0)`, `AP_Math/vector2.h:55-57`. -/
def init_float2 (x0 : Binary32) (y0 : Binary32) : State := Id.run do
  let mut s : State := {}
  s := { s with x := x0 }
  s := { s with y := y0 }
  return s

end Vector2f

namespace Vector3p

/-- State of C++ `Vector3<double>` (`AP_Math/vector3.cpp:633`): its data members. -/
structure State where
  /-- `double x` of `Vector3<double>` (`AP_Math/vector3.h:76`). -/
  x : Binary64 := (Binary64.ofBits 0x0000000000000000 /- 0.0 -/)
  /-- `double y` of `Vector3<double>` (`AP_Math/vector3.h:76`). -/
  y : Binary64 := (Binary64.ofBits 0x0000000000000000 /- 0.0 -/)
  /-- `double z` of `Vector3<double>` (`AP_Math/vector3.h:76`). -/
  z : Binary64 := (Binary64.ofBits 0x0000000000000000 /- 0.0 -/)
deriving Inhabited

end Vector3p

namespace Matrix3_double

/-- State of C++ `Matrix3<double>` (`AP_Math/matrix3.cpp:262`): its data members. -/
structure State where
  /-- `Vector3<double> a` of `Matrix3<double>` (`AP_Math/matrix3.h:54`). -/
  a : Vector3p.State := {}
  /-- `Vector3<double> b` of `Matrix3<double>` (`AP_Math/matrix3.h:54`). -/
  b : Vector3p.State := {}
  /-- `Vector3<double> c` of `Matrix3<double>` (`AP_Math/matrix3.h:54`). -/
  c : Vector3p.State := {}
deriving Inhabited

end Matrix3_double

namespace Vector3p

/-- C++ `Vector3<double>::Vector3()`, `AP_Math/vector3.h:79-82`. -/
def init_void : State := Id.run do
  let mut s : State := {}
  s := { s with x := (Binary64.ofBits 0x0000000000000000 /- 0 -/) }
  s := { s with y := (Binary64.ofBits 0x0000000000000000 /- 0 -/) }
  s := { s with z := (Binary64.ofBits 0x0000000000000000 /- 0 -/) }
  return s

end Vector3p

namespace Matrix3_double

/-- C++ `Matrix3<double>::Matrix3()`, `AP_Math/matrix3.h:58`. -/
def init_void : State := Id.run do
  let mut s : State := {}
  s := { s with a := Vector3p.init_void }
  s := { s with b := Vector3p.init_void }
  s := { s with c := Vector3p.init_void }
  return s

end Matrix3_double

namespace QuaternionT_double

/-- State of C++ `QuaternionT<double>` (`AP_Math/quaternion.cpp:847`): its data members. -/
structure State where
  /-- `double q1` of `QuaternionT<double>` (`AP_Math/quaternion.h:31`). -/
  q1 : Binary64 := (Binary64.ofBits 0x0000000000000000 /- 0.0 -/)
  /-- `double q2` of `QuaternionT<double>` (`AP_Math/quaternion.h:31`). -/
  q2 : Binary64 := (Binary64.ofBits 0x0000000000000000 /- 0.0 -/)
  /-- `double q3` of `QuaternionT<double>` (`AP_Math/quaternion.h:31`). -/
  q3 : Binary64 := (Binary64.ofBits 0x0000000000000000 /- 0.0 -/)
  /-- `double q4` of `QuaternionT<double>` (`AP_Math/quaternion.h:31`). -/
  q4 : Binary64 := (Binary64.ofBits 0x0000000000000000 /- 0.0 -/)
deriving Inhabited

/-- C++ `QuaternionT<double>::QuaternionT()`, `AP_Math/quaternion.h:35-39`. -/
def init_void : State := Id.run do
  let mut s : State := {}
  s := { s with q1 := (Binary64.ofBits 0x3ff0000000000000 /- 1 -/) }
  s := { s with q4 := (Binary64.ofBits 0x0000000000000000 /- 0 -/) }
  s := { s with q3 := s.q4 }
  s := { s with q2 := s.q3 }
  return s

end QuaternionT_double

/-- C++ `bool is_positive(const float fVal1)`, `AP_Math/AP_Math.h:65-69`. -/
def is_positive_float (fVal1 : Binary32) : Bool := Id.run do
  return (decide (fVal1 ≥ (Binary32.ofBits 0x34000000 /- 1.1920929E-7 -/)))

/-- C++ `bool is_zero(const float x)`, `AP_Math/ftype.h:61-63`. -/
def is_zero_float (x : Binary32) : Bool := Id.run do
  return decide (Binary32.abs x < (Binary32.ofBits 0x34000000 /- 1.1920929E-7 -/))

-- not read in the Lean: line
set_option linter.unusedVariables false in
/-- C++ `float constrain_value_line(const float amt, const float low, const float high, uint32_t line)`, `AP_Math/AP_Math.cpp:283-304`. -/
def constrain_value_line_float (amt low high : Binary32) (line : UInt32) : Binary32 := Id.run do
  if Binary32.isNaN amt then
    pure ()  -- C++ `AP_InternalError::error(...)`: left out (--drop)
    return (low + high) / (Binary32.ofBits 0x40000000 /- 2 -/)
  if amt < low then
    return low
  if amt > high then
    return high
  return amt

/-- C++ `auto MIN(const float & one, const float & two)`, `AP_Math/AP_Math.h:300-303`. -/
def MIN_float2 (one two : Binary32) : Binary32 := Id.run do
  return if one < two then one else two

/-- C++ `enum Rotation`, `AP_Math/rotations.h:27-83`. -/
inductive Rotation where
  | ROTATION_NONE
  | ROTATION_YAW_45
  | ROTATION_YAW_90
  | ROTATION_YAW_135
  | ROTATION_YAW_180
  | ROTATION_YAW_225
  | ROTATION_YAW_270
  | ROTATION_YAW_315
  | ROTATION_ROLL_180
  | ROTATION_ROLL_180_YAW_45
  | ROTATION_ROLL_180_YAW_90
  | ROTATION_ROLL_180_YAW_135
  | ROTATION_PITCH_180
  | ROTATION_ROLL_180_YAW_225
  | ROTATION_ROLL_180_YAW_270
  | ROTATION_ROLL_180_YAW_315
  | ROTATION_ROLL_90
  | ROTATION_ROLL_90_YAW_45
  | ROTATION_ROLL_90_YAW_90
  | ROTATION_ROLL_90_YAW_135
  | ROTATION_ROLL_270
  | ROTATION_ROLL_270_YAW_45
  | ROTATION_ROLL_270_YAW_90
  | ROTATION_ROLL_270_YAW_135
  | ROTATION_PITCH_90
  | ROTATION_PITCH_270
  | ROTATION_PITCH_180_YAW_90
  | ROTATION_PITCH_180_YAW_270
  | ROTATION_ROLL_90_PITCH_90
  | ROTATION_ROLL_180_PITCH_90
  | ROTATION_ROLL_270_PITCH_90
  | ROTATION_ROLL_90_PITCH_180
  | ROTATION_ROLL_270_PITCH_180
  | ROTATION_ROLL_90_PITCH_270
  | ROTATION_ROLL_180_PITCH_270
  | ROTATION_ROLL_270_PITCH_270
  | ROTATION_ROLL_90_PITCH_180_YAW_90
  | ROTATION_ROLL_90_YAW_270
  | ROTATION_ROLL_90_PITCH_68_YAW_293
  | ROTATION_PITCH_315
  | ROTATION_ROLL_90_PITCH_315
  | ROTATION_PITCH_7
  | ROTATION_ROLL_45
  | ROTATION_ROLL_315
  | ROTATION_MAX
  | ROTATION_CUSTOM_OLD
  | ROTATION_CUSTOM_1
  | ROTATION_CUSTOM_2
  | ROTATION_CUSTOM_END
deriving DecidableEq, Inhabited

/-- The value of each enumerator of `Rotation` (underlying type `uint8_t`). -/
def Rotation.toInt : Rotation → UInt8
  | .ROTATION_NONE => (0 : UInt8)
  | .ROTATION_YAW_45 => (1 : UInt8)
  | .ROTATION_YAW_90 => (2 : UInt8)
  | .ROTATION_YAW_135 => (3 : UInt8)
  | .ROTATION_YAW_180 => (4 : UInt8)
  | .ROTATION_YAW_225 => (5 : UInt8)
  | .ROTATION_YAW_270 => (6 : UInt8)
  | .ROTATION_YAW_315 => (7 : UInt8)
  | .ROTATION_ROLL_180 => (8 : UInt8)
  | .ROTATION_ROLL_180_YAW_45 => (9 : UInt8)
  | .ROTATION_ROLL_180_YAW_90 => (10 : UInt8)
  | .ROTATION_ROLL_180_YAW_135 => (11 : UInt8)
  | .ROTATION_PITCH_180 => (12 : UInt8)
  | .ROTATION_ROLL_180_YAW_225 => (13 : UInt8)
  | .ROTATION_ROLL_180_YAW_270 => (14 : UInt8)
  | .ROTATION_ROLL_180_YAW_315 => (15 : UInt8)
  | .ROTATION_ROLL_90 => (16 : UInt8)
  | .ROTATION_ROLL_90_YAW_45 => (17 : UInt8)
  | .ROTATION_ROLL_90_YAW_90 => (18 : UInt8)
  | .ROTATION_ROLL_90_YAW_135 => (19 : UInt8)
  | .ROTATION_ROLL_270 => (20 : UInt8)
  | .ROTATION_ROLL_270_YAW_45 => (21 : UInt8)
  | .ROTATION_ROLL_270_YAW_90 => (22 : UInt8)
  | .ROTATION_ROLL_270_YAW_135 => (23 : UInt8)
  | .ROTATION_PITCH_90 => (24 : UInt8)
  | .ROTATION_PITCH_270 => (25 : UInt8)
  | .ROTATION_PITCH_180_YAW_90 => (26 : UInt8)
  | .ROTATION_PITCH_180_YAW_270 => (27 : UInt8)
  | .ROTATION_ROLL_90_PITCH_90 => (28 : UInt8)
  | .ROTATION_ROLL_180_PITCH_90 => (29 : UInt8)
  | .ROTATION_ROLL_270_PITCH_90 => (30 : UInt8)
  | .ROTATION_ROLL_90_PITCH_180 => (31 : UInt8)
  | .ROTATION_ROLL_270_PITCH_180 => (32 : UInt8)
  | .ROTATION_ROLL_90_PITCH_270 => (33 : UInt8)
  | .ROTATION_ROLL_180_PITCH_270 => (34 : UInt8)
  | .ROTATION_ROLL_270_PITCH_270 => (35 : UInt8)
  | .ROTATION_ROLL_90_PITCH_180_YAW_90 => (36 : UInt8)
  | .ROTATION_ROLL_90_YAW_270 => (37 : UInt8)
  | .ROTATION_ROLL_90_PITCH_68_YAW_293 => (38 : UInt8)
  | .ROTATION_PITCH_315 => (39 : UInt8)
  | .ROTATION_ROLL_90_PITCH_315 => (40 : UInt8)
  | .ROTATION_PITCH_7 => (41 : UInt8)
  | .ROTATION_ROLL_45 => (42 : UInt8)
  | .ROTATION_ROLL_315 => (43 : UInt8)
  | .ROTATION_MAX => (44 : UInt8)
  | .ROTATION_CUSTOM_OLD => (100 : UInt8)
  | .ROTATION_CUSTOM_1 => (101 : UInt8)
  | .ROTATION_CUSTOM_2 => (102 : UInt8)
  | .ROTATION_CUSTOM_END => (103 : UInt8)

/-- The enumerator of `Rotation` with value `v` (the C++ converts only enumerator values; any other
value gives the first enumerator, the `Inhabited` default). -/
def Rotation.ofInt (v : UInt8) : Rotation :=
  if v == (0 : UInt8) then .ROTATION_NONE
  else if v == (1 : UInt8) then .ROTATION_YAW_45
  else if v == (2 : UInt8) then .ROTATION_YAW_90
  else if v == (3 : UInt8) then .ROTATION_YAW_135
  else if v == (4 : UInt8) then .ROTATION_YAW_180
  else if v == (5 : UInt8) then .ROTATION_YAW_225
  else if v == (6 : UInt8) then .ROTATION_YAW_270
  else if v == (7 : UInt8) then .ROTATION_YAW_315
  else if v == (8 : UInt8) then .ROTATION_ROLL_180
  else if v == (9 : UInt8) then .ROTATION_ROLL_180_YAW_45
  else if v == (10 : UInt8) then .ROTATION_ROLL_180_YAW_90
  else if v == (11 : UInt8) then .ROTATION_ROLL_180_YAW_135
  else if v == (12 : UInt8) then .ROTATION_PITCH_180
  else if v == (13 : UInt8) then .ROTATION_ROLL_180_YAW_225
  else if v == (14 : UInt8) then .ROTATION_ROLL_180_YAW_270
  else if v == (15 : UInt8) then .ROTATION_ROLL_180_YAW_315
  else if v == (16 : UInt8) then .ROTATION_ROLL_90
  else if v == (17 : UInt8) then .ROTATION_ROLL_90_YAW_45
  else if v == (18 : UInt8) then .ROTATION_ROLL_90_YAW_90
  else if v == (19 : UInt8) then .ROTATION_ROLL_90_YAW_135
  else if v == (20 : UInt8) then .ROTATION_ROLL_270
  else if v == (21 : UInt8) then .ROTATION_ROLL_270_YAW_45
  else if v == (22 : UInt8) then .ROTATION_ROLL_270_YAW_90
  else if v == (23 : UInt8) then .ROTATION_ROLL_270_YAW_135
  else if v == (24 : UInt8) then .ROTATION_PITCH_90
  else if v == (25 : UInt8) then .ROTATION_PITCH_270
  else if v == (26 : UInt8) then .ROTATION_PITCH_180_YAW_90
  else if v == (27 : UInt8) then .ROTATION_PITCH_180_YAW_270
  else if v == (28 : UInt8) then .ROTATION_ROLL_90_PITCH_90
  else if v == (29 : UInt8) then .ROTATION_ROLL_180_PITCH_90
  else if v == (30 : UInt8) then .ROTATION_ROLL_270_PITCH_90
  else if v == (31 : UInt8) then .ROTATION_ROLL_90_PITCH_180
  else if v == (32 : UInt8) then .ROTATION_ROLL_270_PITCH_180
  else if v == (33 : UInt8) then .ROTATION_ROLL_90_PITCH_270
  else if v == (34 : UInt8) then .ROTATION_ROLL_180_PITCH_270
  else if v == (35 : UInt8) then .ROTATION_ROLL_270_PITCH_270
  else if v == (36 : UInt8) then .ROTATION_ROLL_90_PITCH_180_YAW_90
  else if v == (37 : UInt8) then .ROTATION_ROLL_90_YAW_270
  else if v == (38 : UInt8) then .ROTATION_ROLL_90_PITCH_68_YAW_293
  else if v == (39 : UInt8) then .ROTATION_PITCH_315
  else if v == (40 : UInt8) then .ROTATION_ROLL_90_PITCH_315
  else if v == (41 : UInt8) then .ROTATION_PITCH_7
  else if v == (42 : UInt8) then .ROTATION_ROLL_45
  else if v == (43 : UInt8) then .ROTATION_ROLL_315
  else if v == (44 : UInt8) then .ROTATION_MAX
  else if v == (100 : UInt8) then .ROTATION_CUSTOM_OLD
  else if v == (101 : UInt8) then .ROTATION_CUSTOM_1
  else if v == (102 : UInt8) then .ROTATION_CUSTOM_2
  else if v == (103 : UInt8) then .ROTATION_CUSTOM_END
  else default

namespace Vector3f

/-- C++ `void Vector3<float>::rotate(enum Rotation rotation)`, `AP_Math/vector3.cpp:29-274`. -/
def rotate (s : State) (rotation : Rotation) : State := Id.run do
  let mut s := s
  let mut tmp : Binary32 := (Binary32.ofBits 0x00000000 /- 0.0 -/)  -- uninitialized in C++; assigned before every read
  match rotation with
  | .ROTATION_NONE =>
    return s
  | .ROTATION_YAW_45 =>
    tmp := Binary64.toBinary32 ((Binary64.ofBits 0x3fe6a09e667f3bcd /- 0.70710678118654757 -/) * Binary32.toBinary64 (s.x - s.y))
    s := { s with y := Binary64.toBinary32 ((Binary64.ofBits 0x3fe6a09e667f3bcd /- 0.70710678118654757 -/) * Binary32.toBinary64 (s.x + s.y)) }
    s := { s with x := tmp }
    return s
  | .ROTATION_YAW_90 =>
    tmp := s.x
    s := { s with x := -s.y }
    s := { s with y := tmp }
    return s
  | .ROTATION_YAW_135 =>
    tmp := Binary64.toBinary32 (-(Binary64.ofBits 0x3fe6a09e667f3bcd /- 0.70710678118654757 -/) * Binary32.toBinary64 (s.x + s.y))
    s := { s with y := Binary64.toBinary32 ((Binary64.ofBits 0x3fe6a09e667f3bcd /- 0.70710678118654757 -/) * Binary32.toBinary64 (s.x - s.y)) }
    s := { s with x := tmp }
    return s
  | .ROTATION_YAW_180 =>
    s := { s with x := -s.x }
    s := { s with y := -s.y }
    return s
  | .ROTATION_YAW_225 =>
    tmp := Binary64.toBinary32 ((Binary64.ofBits 0x3fe6a09e667f3bcd /- 0.70710678118654757 -/) * Binary32.toBinary64 (s.y - s.x))
    s := { s with y := Binary64.toBinary32 (-(Binary64.ofBits 0x3fe6a09e667f3bcd /- 0.70710678118654757 -/) * Binary32.toBinary64 (s.x + s.y)) }
    s := { s with x := tmp }
    return s
  | .ROTATION_YAW_270 =>
    tmp := s.x
    s := { s with x := s.y }
    s := { s with y := -tmp }
    return s
  | .ROTATION_YAW_315 =>
    tmp := Binary64.toBinary32 ((Binary64.ofBits 0x3fe6a09e667f3bcd /- 0.70710678118654757 -/) * Binary32.toBinary64 (s.x + s.y))
    s := { s with y := Binary64.toBinary32 ((Binary64.ofBits 0x3fe6a09e667f3bcd /- 0.70710678118654757 -/) * Binary32.toBinary64 (s.y - s.x)) }
    s := { s with x := tmp }
    return s
  | .ROTATION_ROLL_180 =>
    s := { s with y := -s.y }
    s := { s with z := -s.z }
    return s
  | .ROTATION_ROLL_180_YAW_45 =>
    tmp := Binary64.toBinary32 ((Binary64.ofBits 0x3fe6a09e667f3bcd /- 0.70710678118654757 -/) * Binary32.toBinary64 (s.x + s.y))
    s := { s with y := Binary64.toBinary32 ((Binary64.ofBits 0x3fe6a09e667f3bcd /- 0.70710678118654757 -/) * Binary32.toBinary64 (s.x - s.y)) }
    s := { s with x := tmp }
    s := { s with z := -s.z }
    return s
  | .ROTATION_ROLL_180_YAW_90 | .ROTATION_PITCH_180_YAW_270 =>
    tmp := s.x
    s := { s with x := s.y }
    s := { s with y := tmp }
    s := { s with z := -s.z }
    return s
  | .ROTATION_ROLL_180_YAW_135 =>
    tmp := Binary64.toBinary32 ((Binary64.ofBits 0x3fe6a09e667f3bcd /- 0.70710678118654757 -/) * Binary32.toBinary64 (s.y - s.x))
    s := { s with y := Binary64.toBinary32 ((Binary64.ofBits 0x3fe6a09e667f3bcd /- 0.70710678118654757 -/) * Binary32.toBinary64 (s.y + s.x)) }
    s := { s with x := tmp }
    s := { s with z := -s.z }
    return s
  | .ROTATION_PITCH_180 =>
    s := { s with x := -s.x }
    s := { s with z := -s.z }
    return s
  | .ROTATION_ROLL_180_YAW_225 =>
    tmp := Binary64.toBinary32 (-(Binary64.ofBits 0x3fe6a09e667f3bcd /- 0.70710678118654757 -/) * Binary32.toBinary64 (s.x + s.y))
    s := { s with y := Binary64.toBinary32 ((Binary64.ofBits 0x3fe6a09e667f3bcd /- 0.70710678118654757 -/) * Binary32.toBinary64 (s.y - s.x)) }
    s := { s with x := tmp }
    s := { s with z := -s.z }
    return s
  | .ROTATION_ROLL_180_YAW_270 | .ROTATION_PITCH_180_YAW_90 =>
    tmp := s.x
    s := { s with x := -s.y }
    s := { s with y := -tmp }
    s := { s with z := -s.z }
    return s
  | .ROTATION_ROLL_180_YAW_315 =>
    tmp := Binary64.toBinary32 ((Binary64.ofBits 0x3fe6a09e667f3bcd /- 0.70710678118654757 -/) * Binary32.toBinary64 (s.x - s.y))
    s := { s with y := Binary64.toBinary32 (-(Binary64.ofBits 0x3fe6a09e667f3bcd /- 0.70710678118654757 -/) * Binary32.toBinary64 (s.x + s.y)) }
    s := { s with x := tmp }
    s := { s with z := -s.z }
    return s
  | .ROTATION_ROLL_90 =>
    tmp := s.z
    s := { s with z := s.y }
    s := { s with y := -tmp }
    return s
  | .ROTATION_ROLL_90_YAW_45 =>
    tmp := s.z
    s := { s with z := s.y }
    s := { s with y := -tmp }
    tmp := Binary64.toBinary32 ((Binary64.ofBits 0x3fe6a09e667f3bcd /- 0.70710678118654757 -/) * Binary32.toBinary64 (s.x - s.y))
    s := { s with y := Binary64.toBinary32 ((Binary64.ofBits 0x3fe6a09e667f3bcd /- 0.70710678118654757 -/) * Binary32.toBinary64 (s.x + s.y)) }
    s := { s with x := tmp }
    return s
  | .ROTATION_ROLL_90_YAW_90 =>
    tmp := s.z
    s := { s with z := s.y }
    s := { s with y := -tmp }
    tmp := s.x
    s := { s with x := -s.y }
    s := { s with y := tmp }
    return s
  | .ROTATION_ROLL_90_YAW_135 =>
    tmp := s.z
    s := { s with z := s.y }
    s := { s with y := -tmp }
    tmp := Binary64.toBinary32 (-(Binary64.ofBits 0x3fe6a09e667f3bcd /- 0.70710678118654757 -/) * Binary32.toBinary64 (s.x + s.y))
    s := { s with y := Binary64.toBinary32 ((Binary64.ofBits 0x3fe6a09e667f3bcd /- 0.70710678118654757 -/) * Binary32.toBinary64 (s.x - s.y)) }
    s := { s with x := tmp }
    return s
  | .ROTATION_ROLL_270 =>
    tmp := s.z
    s := { s with z := -s.y }
    s := { s with y := tmp }
    return s
  | .ROTATION_ROLL_270_YAW_45 =>
    tmp := s.z
    s := { s with z := -s.y }
    s := { s with y := tmp }
    tmp := Binary64.toBinary32 ((Binary64.ofBits 0x3fe6a09e667f3bcd /- 0.70710678118654757 -/) * Binary32.toBinary64 (s.x - s.y))
    s := { s with y := Binary64.toBinary32 ((Binary64.ofBits 0x3fe6a09e667f3bcd /- 0.70710678118654757 -/) * Binary32.toBinary64 (s.x + s.y)) }
    s := { s with x := tmp }
    return s
  | .ROTATION_ROLL_270_YAW_90 =>
    tmp := s.z
    s := { s with z := -s.y }
    s := { s with y := tmp }
    tmp := s.x
    s := { s with x := -s.y }
    s := { s with y := tmp }
    return s
  | .ROTATION_ROLL_270_YAW_135 =>
    tmp := s.z
    s := { s with z := -s.y }
    s := { s with y := tmp }
    tmp := Binary64.toBinary32 (-(Binary64.ofBits 0x3fe6a09e667f3bcd /- 0.70710678118654757 -/) * Binary32.toBinary64 (s.x + s.y))
    s := { s with y := Binary64.toBinary32 ((Binary64.ofBits 0x3fe6a09e667f3bcd /- 0.70710678118654757 -/) * Binary32.toBinary64 (s.x - s.y)) }
    s := { s with x := tmp }
    return s
  | .ROTATION_PITCH_90 =>
    tmp := s.z
    s := { s with z := -s.x }
    s := { s with x := tmp }
    return s
  | .ROTATION_PITCH_270 =>
    tmp := s.z
    s := { s with z := s.x }
    s := { s with x := -tmp }
    return s
  | .ROTATION_ROLL_90_PITCH_90 =>
    tmp := s.z
    s := { s with z := s.y }
    s := { s with y := -tmp }
    tmp := s.z
    s := { s with z := -s.x }
    s := { s with x := tmp }
    return s
  | .ROTATION_ROLL_180_PITCH_90 =>
    s := { s with y := -s.y }
    s := { s with z := -s.z }
    tmp := s.z
    s := { s with z := -s.x }
    s := { s with x := tmp }
    return s
  | .ROTATION_ROLL_270_PITCH_90 =>
    tmp := s.z
    s := { s with z := -s.y }
    s := { s with y := tmp }
    tmp := s.z
    s := { s with z := -s.x }
    s := { s with x := tmp }
    return s
  | .ROTATION_ROLL_90_PITCH_180 =>
    tmp := s.z
    s := { s with z := s.y }
    s := { s with y := -tmp }
    s := { s with x := -s.x }
    s := { s with z := -s.z }
    return s
  | .ROTATION_ROLL_270_PITCH_180 =>
    tmp := s.z
    s := { s with z := -s.y }
    s := { s with y := tmp }
    s := { s with x := -s.x }
    s := { s with z := -s.z }
    return s
  | .ROTATION_ROLL_90_PITCH_270 =>
    tmp := s.z
    s := { s with z := s.y }
    s := { s with y := -tmp }
    tmp := s.z
    s := { s with z := s.x }
    s := { s with x := -tmp }
    return s
  | .ROTATION_ROLL_180_PITCH_270 =>
    s := { s with y := -s.y }
    s := { s with z := -s.z }
    tmp := s.z
    s := { s with z := s.x }
    s := { s with x := -tmp }
    return s
  | .ROTATION_ROLL_270_PITCH_270 =>
    tmp := s.z
    s := { s with z := -s.y }
    s := { s with y := tmp }
    tmp := s.z
    s := { s with z := s.x }
    s := { s with x := -tmp }
    return s
  | .ROTATION_ROLL_90_PITCH_180_YAW_90 =>
    tmp := s.z
    s := { s with z := s.y }
    s := { s with y := -tmp }
    s := { s with x := -s.x }
    s := { s with z := -s.z }
    tmp := s.x
    s := { s with x := -s.y }
    s := { s with y := tmp }
    return s
  | .ROTATION_ROLL_90_YAW_270 =>
    tmp := s.z
    s := { s with z := s.y }
    s := { s with y := -tmp }
    tmp := s.x
    s := { s with x := s.y }
    s := { s with y := -tmp }
    return s
  | .ROTATION_ROLL_90_PITCH_68_YAW_293 =>
    let tmpx : Binary32 := s.x
    let tmpy : Binary32 := s.y
    let tmpz : Binary32 := s.z
    s := { s with x := Binary64.toBinary32 ((Binary64.ofBits 0x3fc24f19de11379b /- 0.14303897231223747232853327204793 -/) * Binary32.toBinary64 tmpx + (Binary64.ofBits 0x3fd79a08b14429b6 /- 0.36877648650320382639478111741482 -/) * Binary32.toBinary64 tmpy + -(Binary64.ofBits 0x3fed63e9aa5ff077 /- 0.91844638134308709265241077446262 -/) * Binary32.toBinary64 tmpz) }
    s := { s with y := Binary64.toBinary32 (-(Binary64.ofBits 0x3fd541a9d6a43d34 /- 0.33213277779664740485543461545603 -/) * Binary32.toBinary64 tmpx + -(Binary64.ofBits 0x3feb66b912a37d2b /- 0.85628942146641884303193137384369 -/) * Binary32.toBinary64 tmpy + -(Binary64.ofBits 0x3fd9509e15659ed7 /- 0.39554550256296522325882847326284 -/) * Binary32.toBinary64 tmpz) }
    s := { s with z := Binary64.toBinary32 (-(Binary64.ofBits 0x3fedd598b97018d2 /- 0.93232380121551217122544130688766 -/) * Binary32.toBinary64 tmpx + (Binary64.ofBits 0x3fd724db617bb07d /- 0.36162457008209242248497616856184 -/) * Binary32.toBinary64 tmpy + (Binary64.ofBits 0x3c79877ebd12c4c9 /- 0.00000000000000002214311861220361 -/) * Binary32.toBinary64 tmpz) }
    return s
  | .ROTATION_PITCH_315 =>
    tmp := Binary64.toBinary32 ((Binary64.ofBits 0x3fe6a09e667f3bcd /- 0.70710678118654757 -/) * Binary32.toBinary64 (s.x - s.z))
    s := { s with z := Binary64.toBinary32 ((Binary64.ofBits 0x3fe6a09e667f3bcd /- 0.70710678118654757 -/) * Binary32.toBinary64 (s.x + s.z)) }
    s := { s with x := tmp }
    return s
  | .ROTATION_ROLL_90_PITCH_315 =>
    tmp := s.z
    s := { s with z := s.y }
    s := { s with y := -tmp }
    tmp := Binary64.toBinary32 ((Binary64.ofBits 0x3fe6a09e667f3bcd /- 0.70710678118654757 -/) * Binary32.toBinary64 (s.x - s.z))
    s := { s with z := Binary64.toBinary32 ((Binary64.ofBits 0x3fe6a09e667f3bcd /- 0.70710678118654757 -/) * Binary32.toBinary64 (s.x + s.z)) }
    s := { s with x := tmp }
    return s
  | .ROTATION_PITCH_7 =>
    let sin_pitch : Binary32 := (Binary32.ofBits 0x3df996a2 /- 0.1218693434051474899781908334262 -/)
    let cos_pitch : Binary32 := (Binary32.ofBits 0x3f7e1781 /- 0.99254615164132198312785249072476 -/)
    let tmpx'2 : Binary32 := s.x
    let tmpz'2 : Binary32 := s.z
    s := { s with x := cos_pitch * tmpx'2 + sin_pitch * tmpz'2 }
    s := { s with z := -sin_pitch * tmpx'2 + cos_pitch * tmpz'2 }
    return s
  | .ROTATION_ROLL_45 =>
    tmp := Binary64.toBinary32 ((Binary64.ofBits 0x3fe6a09e667f3bcd /- 0.70710678118654757 -/) * Binary32.toBinary64 (s.y - s.z))
    s := { s with z := Binary64.toBinary32 ((Binary64.ofBits 0x3fe6a09e667f3bcd /- 0.70710678118654757 -/) * Binary32.toBinary64 (s.y + s.z)) }
    s := { s with y := tmp }
    return s
  | .ROTATION_ROLL_315 =>
    tmp := Binary64.toBinary32 ((Binary64.ofBits 0x3fe6a09e667f3bcd /- 0.70710678118654757 -/) * Binary32.toBinary64 (s.y + s.z))
    s := { s with z := Binary64.toBinary32 ((Binary64.ofBits 0x3fe6a09e667f3bcd /- 0.70710678118654757 -/) * Binary32.toBinary64 (s.z - s.y)) }
    s := { s with y := tmp }
    return s
  | .ROTATION_CUSTOM_1 | .ROTATION_CUSTOM_2 | .ROTATION_MAX | .ROTATION_CUSTOM_OLD | .ROTATION_CUSTOM_END =>
    pure ()
  pure ()  -- C++ `AP_InternalError::error(...)`: left out (--drop)
  return s

end Vector3f

namespace Vector3f

/-- C++ `Vector3<float> & Vector3<float>::operator+=(const Vector3<float> & v)`, `AP_Math/vector3.cpp:376-380`. -/
def op_add_assign (s : State) (v : Vector3f.State) : State × Vector3f.State := Id.run do
  let mut s := s
  s := { s with x := s.x + v.x }
  s := { s with y := s.y + v.y }
  s := { s with z := s.z + v.z }
  return (s, s)

/-- C++ `void Vector3<float>::zero()`, `AP_Math/vector3.h:229-232`. -/
def zero (s : State) : State := Id.run do
  let mut s := s
  s := { s with z := (Binary32.ofBits 0x00000000 /- 0 -/) }
  s := { s with y := s.z }
  s := { s with x := s.y }
  return s

/-- C++ `Vector3<float>::Vector3(const float x0, const float y0, const float z0)`, `AP_Math/vector3.h:85-88`. -/
def init_float3 (x0 : Binary32) (y0 : Binary32) (z0 : Binary32) : State := Id.run do
  let mut s : State := {}
  s := { s with x := x0 }
  s := { s with y := y0 }
  s := { s with z := z0 }
  return s

/-- C++ `Vector3<float> Vector3<float>::operator*(const float num) const`, `AP_Math/vector3.cpp:389-392`. -/
def op_mul_float (s : State) (num : Binary32) : Vector3f.State := Id.run do
  return Vector3f.init_float3 (s.x * num) (s.y * num) (s.z * num)

end Vector3f

namespace Matrix3f

/-- C++ `Matrix3<float>::Matrix3(const float ax, const float ay, const float az, const float bx, const float by, const float bz, const float cx, const float cy, const float cz)`, `AP_Math/matrix3.h:67-72`. -/
def init_float9 (ax : Binary32) (ay : Binary32) (az : Binary32) (bx : Binary32) («by» : Binary32) (bz : Binary32) (cx : Binary32) (cy : Binary32) (cz : Binary32) : State := Id.run do
  let mut s : State := {}
  s := { s with a := Vector3f.init_float3 ax ay az }
  s := { s with b := Vector3f.init_float3 bx «by» bz }
  s := { s with c := Vector3f.init_float3 cx cy cz }
  return s

/-- C++ `Vector3<float> Matrix3<float>::operator*(const Vector3<float> & v) const`, `AP_Math/matrix3.cpp:146-151`. -/
def op_mul_Vector3f (s : State) (v : Vector3f.State) : Vector3f.State := Id.run do
  return Vector3f.init_float3 (s.a.x * v.x + s.a.y * v.y + s.a.z * v.z) (s.b.x * v.x + s.b.y * v.y + s.b.z * v.z) (s.c.x * v.x + s.c.y * v.y + s.c.z * v.z)

end Matrix3f

namespace Vector3f

/-- C++ `Vector3<float> & Vector3<float>::operator*=(const float num)`, `AP_Math/vector3.cpp:343-347`. -/
def op_mul_assign_float (s : State) (num : Binary32) : State × Vector3f.State := Id.run do
  let mut s := s
  s := { s with x := s.x * num }
  s := { s with y := s.y * num }
  s := { s with z := s.z * num }
  return (s, s)

/-- C++ `bool Vector3<float>::is_zero() const`, `AP_Math/vector3.h:321-323`. -/
def is_zero (s : State) : Bool := Id.run do
  return Estimator_lib.is_zero_float s.x && Estimator_lib.is_zero_float s.y && Estimator_lib.is_zero_float s.z

end Vector3f

namespace Vector3f

/-- C++ `bool Vector3<float>::is_inf() const`, `AP_Math/vector3.cpp:370-373`. -/
def is_inf (s : State) : Bool := Id.run do
  return Binary32.isInf s.x || Binary32.isInf s.y || Binary32.isInf s.z

/-- C++ `bool Vector3<float>::is_nan() const`, `AP_Math/vector3.cpp:364-367`. -/
def is_nan (s : State) : Bool := Id.run do
  return Binary32.isNaN s.x || Binary32.isNaN s.y || Binary32.isNaN s.z

end Vector3f

/-- C++ `float sq(const float val)`, `AP_Math/AP_Math.h:266-269`. -/
def sq_float (val : Binary32) : Binary32 := Id.run do
  return val * val

/-- C++ `float norm(const float first, const float second, const float third)`, `AP_Math/AP_Math.h:294-296`. -/
def norm_float3 (first second third : Binary32) : Binary32 := Id.run do
  return Binary32.sqrt (sq_float first + sq_float second + sq_float third)

namespace Vector3f

/-- C++ `float Vector3<float>::length() const`, `AP_Math/vector3.cpp:324-327`. -/
def length (s : State) : Binary32 := Id.run do
  return Estimator_lib.norm_float3 s.x s.y s.z

end Vector3f

namespace Vector3f

/-- C++ `Vector3<float> & Vector3<float>::operator/=(const float num)`, `AP_Math/vector3.cpp:350-354`. -/
def op_div_assign (s : State) (num : Binary32) : State × Vector3f.State := Id.run do
  let mut s := s
  s := { s with x := s.x / num }
  s := { s with y := s.y / num }
  s := { s with z := s.z / num }
  return (s, s)

end Vector3f

namespace Vector3f

/-- C++ `Vector3<float> & Vector3<float>::operator-=(const Vector3<float> & v)`, `AP_Math/vector3.cpp:357-361`. -/
def op_sub_assign (s : State) (v : Vector3f.State) : State × Vector3f.State := Id.run do
  let mut s := s
  s := { s with x := s.x - v.x }
  s := { s with y := s.y - v.y }
  s := { s with z := s.z - v.z }
  return (s, s)

end Vector3f

namespace Vector3f

/-- C++ `Vector3<float> Vector3<float>::operator-(const Vector3<float> & v) const`, `AP_Math/vector3.cpp:395-398`. -/
def op_sub_Vector3f (s : State) (v : Vector3f.State) : Vector3f.State := Id.run do
  return Vector3f.init_float3 (s.x - v.x) (s.y - v.y) (s.z - v.z)

end Vector3f

/-- C++ `bool is_negative(const float fVal1)`, `AP_Math/AP_Math.h:76-80`. -/
def is_negative_float (fVal1 : Binary32) : Bool := Id.run do
  return (decide (Binary32.toBinary64 fVal1 ≤ (-(Binary64.ofBits 0x3ff0000000000000 /- 1.0 -/) * (Binary64.ofBits 0x3e80000000000000 /- (double)1/8388608 -/))))

/-- C++ `float calc_lowpass_alpha_dt(float dt, float cutoff_freq)`, `AP_Math/AP_Math.cpp:418-432`. -/
def calc_lowpass_alpha_dt (dt cutoff_freq : Binary32) : Binary32 := Id.run do
  if is_negative_float dt || is_negative_float cutoff_freq then
    pure ()  -- C++ `AP_InternalError::error(...)`: left out (--drop)
    return (Binary32.ofBits 0x3f800000 /- 1.0 -/)
  if is_zero_float cutoff_freq then
    return (Binary32.ofBits 0x3f800000 /- 1.0 -/)
  if is_zero_float dt then
    return (Binary32.ofBits 0x00000000 /- 0.0 -/)
  let rc : Binary32 := (Binary32.ofBits 0x3f800000 /- 1.0f -/) / (((Binary32.ofBits 0x40490fdb /- (float)884279719003555/281474976710656 -/) * (Binary32.ofBits 0x40000000 /- (float)2 -/)) * cutoff_freq)
  return dt / (dt + rc)

namespace Vector3f

/-- C++ `Vector3<float> Vector3<float>::operator+(const Vector3<float> & v) const`, `AP_Math/vector3.cpp:401-404`. -/
def op_add (s : State) (v : Vector3f.State) : Vector3f.State := Id.run do
  return Vector3f.init_float3 (s.x + v.x) (s.y + v.y) (s.z + v.z)

end Vector3f

namespace Vector3f

/-- C++ `Vector3<float> Vector3<float>::operator%(const Vector3<float> & v) const`, `AP_Math/vector3.cpp:310-314`. -/
def op_mod (s : State) (v : Vector3f.State) : Vector3f.State := Id.run do
  let temp : Vector3f.State := Vector3f.init_float3 (s.y * v.z - s.z * v.y) (s.z * v.x - s.x * v.z) (s.x * v.y - s.y * v.x)
  return temp

end Vector3f

namespace Matrix3f

/-- C++ `Vector3<float> Matrix3<float>::mul_transpose(const Vector3<float> & v) const`, `AP_Math/matrix3.cpp:163-168`. -/
def mul_transpose (s : State) (v : Vector3f.State) : Vector3f.State := Id.run do
  return Vector3f.init_float3 (s.a.x * v.x + s.b.x * v.y + s.c.x * v.z) (s.a.y * v.x + s.b.y * v.y + s.c.y * v.z) (s.a.z * v.x + s.b.z * v.y + s.c.z * v.z)

end Matrix3f

namespace Vector3f

/-- C++ `void Vector3<float>::rotate_inverse(enum Rotation rotation)`, `AP_Math/vector3.cpp:277-294`. -/
def rotate_inverse (s : State) (rotation : Rotation) : State := Id.run do
  let mut s := s
  let mut x_vec : Vector3f.State := Vector3f.init_float3 (Binary32.ofBits 0x3f800000 /- 1.0f -/) (Binary32.ofBits 0x00000000 /- 0.0f -/) (Binary32.ofBits 0x00000000 /- 0.0f -/)
  let mut y_vec : Vector3f.State := Vector3f.init_float3 (Binary32.ofBits 0x00000000 /- 0.0f -/) (Binary32.ofBits 0x3f800000 /- 1.0f -/) (Binary32.ofBits 0x00000000 /- 0.0f -/)
  let mut z_vec : Vector3f.State := Vector3f.init_float3 (Binary32.ofBits 0x00000000 /- 0.0f -/) (Binary32.ofBits 0x00000000 /- 0.0f -/) (Binary32.ofBits 0x3f800000 /- 1.0f -/)
  x_vec := Vector3f.rotate x_vec rotation
  y_vec := Vector3f.rotate y_vec rotation
  z_vec := Vector3f.rotate z_vec rotation
  let M : Matrix3f.State := Matrix3f.init_float9 x_vec.x y_vec.x z_vec.x x_vec.y y_vec.y z_vec.y x_vec.z y_vec.z z_vec.z
  s := Matrix3f.mul_transpose M s
  return s

end Vector3f

/-- C++ `float degrees(float rad)`, `AP_Math/AP_Math.h:255-258`. -/
def degrees (rad : Binary32) : Binary32 := Id.run do
  return rad * ((Binary32.ofBits 0x43340000 /- 180 -/) / (Binary32.ofBits 0x40490fdb /- (float)884279719003555/281474976710656 -/))

/-- C++ `float norm(const float first, const float second)`, `AP_Math/AP_Math.h:291-293`. -/
def norm_float2 (first second : Binary32) : Binary32 := Id.run do
  return Binary32.sqrt (sq_float first + sq_float second)

namespace Matrix3f

/-- C++ `void Matrix3<float>::from_euler(float roll, float pitch, float yaw)`, `AP_Math/matrix3.cpp:26-44`. -/
def from_euler (s : State) (roll : Binary32) (pitch : Binary32) (yaw : Binary32) : State := Id.run do
  let mut s := s
  let cp : Binary32 := Musl.cosf.cosf pitch
  let sp : Binary32 := Musl.sinf.sinf pitch
  let sr : Binary32 := Musl.sinf.sinf roll
  let cr : Binary32 := Musl.cosf.cosf roll
  let sy : Binary32 := Musl.sinf.sinf yaw
  let cy : Binary32 := Musl.cosf.cosf yaw
  s := { s with a.x := cp * cy }
  s := { s with a.y := (sr * sp * cy) - (cr * sy) }
  s := { s with a.z := (cr * sp * cy) + (sr * sy) }
  s := { s with b.x := cp * sy }
  s := { s with b.y := (sr * sp * sy) + (cr * cy) }
  s := { s with b.z := (cr * sp * sy) - (sr * cy) }
  s := { s with c.x := -sp }
  s := { s with c.y := sr * cp }
  s := { s with c.z := cr * cp }
  return s

end Matrix3f

/-- C++ `float radians(float deg)`, `AP_Math/AP_Math.h:232-235`. -/
def radians_float (deg : Binary32) : Binary32 := Id.run do
  return deg * ((Binary32.ofBits 0x40490fdb /- (float)884279719003555/281474976710656 -/) / (Binary32.ofBits 0x43340000 /- 180 -/))

namespace Vector2f

/-- C++ `bool Vector2<float>::is_zero() const`, `AP_Math/vector2.h:295-297`. -/
def is_zero (s : State) : Bool := Id.run do
  return Estimator_lib.is_zero_float s.x && Estimator_lib.is_zero_float s.y

/-- C++ `float Vector2<float>::length() const`, `AP_Math/vector2.cpp:30-33`. -/
def length (s : State) : Binary32 := Id.run do
  return Estimator_lib.norm_float2 s.x s.y

/-- C++ `float Vector2<float>::operator*(const Vector2<float> & v) const`, `AP_Math/vector2.cpp:50-53`. -/
def op_mul_Vector2f (s : State) (v : Vector2f.State) : Binary32 := Id.run do
  return s.x * v.x + s.y * v.y

/-- C++ `float Vector2<float>::angle(const Vector2<float> & v2) const`, `AP_Math/vector2.cpp:145-159`. -/
def angle_Vector2f (s : State) (v2 : Vector2f.State) : Binary32 := Id.run do
  let len : Binary32 := length s * Vector2f.length v2
  if len ≤ (Binary32.ofBits 0x00000000 /- 0 -/) then
    return (Binary32.ofBits 0x00000000 /- 0.0f -/)
  let cosv : Binary32 := (op_mul_Vector2f s v2) / len
  if cosv ≥ (Binary32.ofBits 0x3f800000 /- 1 -/) then
    return (Binary32.ofBits 0x00000000 /- 0.0f -/)
  if cosv ≤ (Binary32.ofBits 0xbf800000 /- -1 -/) then
    return (Binary32.ofBits 0x40490fdb /- (float)884279719003555/281474976710656 -/)
  return Musl.acosf.acosf cosv

/-- C++ `Vector2<float> Vector2<float>::operator-(const Vector2<float> & v) const`, `AP_Math/vector2.cpp:115-118`. -/
def op_sub_Vector2f (s : State) (v : Vector2f.State) : Vector2f.State := Id.run do
  return Vector2f.init_float2 (s.x - v.x) (s.y - v.y)

end Vector2f

namespace Vector3f

/-- C++ `const Vector2<float> & Vector3<float>::xy() const`, `AP_Math/vector3.h:203-205`. -/
def xy (s : State) : Vector2f.State := Id.run do
  return { x := s.x, y := s.y }

/-- C++ `float Vector3<float>::operator*(const Vector3<float> & v) const`, `AP_Math/vector3.cpp:318-321`. -/
def op_mul_Vector3f (s : State) (v : Vector3f.State) : Binary32 := Id.run do
  return s.x * v.x + s.y * v.y + s.z * v.z

/-- C++ `float Vector3<float>::angle(const Vector3<float> & v2) const`, `AP_Math/vector3.cpp:425-436`. -/
def angle (s : State) (v2 : Vector3f.State) : Binary32 := Id.run do
  let len : Binary32 := length s * Vector3f.length v2
  if len ≤ (Binary32.ofBits 0x00000000 /- 0 -/) then
    return (Binary32.ofBits 0x00000000 /- 0.0f -/)
  let cosv : Binary32 := (op_mul_Vector3f s v2) / len
  if decide (cosv ≥ (Binary32.ofBits 0x3f800000 /- 1 -/)) || decide (cosv ≤ (Binary32.ofBits 0xbf800000 /- -1 -/)) then
    return (Binary32.ofBits 0x00000000 /- 0.0f -/)
  return Musl.acosf.acosf cosv

end Vector3f

namespace Vector3f

/-- C++ `Vector3<float> Vector3<float>::operator/(const float num) const`, `AP_Math/vector3.cpp:383-386`. -/
def op_div (s : State) (num : Binary32) : Vector3f.State := Id.run do
  return Vector3f.init_float3 (s.x / num) (s.y / num) (s.z / num)

end Vector3f

/-- C++ `auto MIN(const int & one, const unsigned char & two)`, `AP_Math/AP_Math.h:300-303`. -/
def MIN_int32_t_uint8_t (one : Int32) (two : UInt8) : Int32 := Id.run do
  return if one < UInt32.toInt32 (UInt8.toUInt32 two) then one else UInt32.toInt32 (UInt8.toUInt32 two)

namespace Vector2p

/-- C++ `Vector2<double>::Vector2()`, `AP_Math/vector2.h:50-52`. -/
def init_void : State := Id.run do
  let mut s : State := {}
  s := { s with x := (Binary64.ofBits 0x0000000000000000 /- 0 -/) }
  s := { s with y := (Binary64.ofBits 0x0000000000000000 /- 0 -/) }
  return s

end Vector2p

/-- C++ `auto MIN(const unsigned short & one, const int & two)`, `AP_Math/AP_Math.h:300-303`. -/
def MIN_uint16_t_int32_t (one : UInt16) (two : Int32) : Int32 := Id.run do
  return if UInt32.toInt32 (UInt16.toUInt32 one) < two then UInt32.toInt32 (UInt16.toUInt32 one) else two

/-- C++ `auto MIN(const unsigned char & one, const unsigned char & two)`, `AP_Math/AP_Math.h:300-303`. -/
def MIN_uint8_t2 (one two : UInt8) : UInt8 := Id.run do
  return if UInt32.toInt32 (UInt8.toUInt32 one) < UInt32.toInt32 (UInt8.toUInt32 two) then one else two

/-- C++ `auto MAX(const double & one, const float & two)`, `AP_Math/AP_Math.h:307-310`. -/
def MAX_double_float (one : Binary64) (two : Binary32) : Binary64 := Id.run do
  return if one > Binary32.toBinary64 two then one else Binary32.toBinary64 two

/-- C++ `auto MAX(const unsigned short & one, const unsigned short & two)`, `AP_Math/AP_Math.h:307-310`. -/
def MAX_uint16_t2 (one two : UInt16) : UInt16 := Id.run do
  return if UInt32.toInt32 (UInt16.toUInt32 one) > UInt32.toInt32 (UInt16.toUInt32 two) then one else two

/-- C++ `auto MAX(const unsigned short & one, const int & two)`, `AP_Math/AP_Math.h:307-310`. -/
def MAX_uint16_t_int32_t (one : UInt16) (two : Int32) : Int32 := Id.run do
  return if UInt32.toInt32 (UInt16.toUInt32 one) > two then UInt32.toInt32 (UInt16.toUInt32 one) else two

namespace QuaternionT_double

/-- C++ `void QuaternionT<double>::from_euler(double roll, double pitch, double yaw)`, `AP_Math/quaternion.cpp:421-434`. -/
def from_euler_double3 (s : State) (roll : Binary64) (pitch : Binary64) (yaw : Binary64) : State := Id.run do
  let mut s := s
  let cr2 : Binary64 := Musl.cos.cos (roll * (Binary64.ofBits 0x3fe0000000000000 /- 0.5 -/))
  let cp2 : Binary64 := Musl.cos.cos (pitch * (Binary64.ofBits 0x3fe0000000000000 /- 0.5 -/))
  let cy2 : Binary64 := Musl.cos.cos (yaw * (Binary64.ofBits 0x3fe0000000000000 /- 0.5 -/))
  let sr2 : Binary64 := Musl.sin.sin (roll * (Binary64.ofBits 0x3fe0000000000000 /- 0.5 -/))
  let sp2 : Binary64 := Musl.sin.sin (pitch * (Binary64.ofBits 0x3fe0000000000000 /- 0.5 -/))
  let sy2 : Binary64 := Musl.sin.sin (yaw * (Binary64.ofBits 0x3fe0000000000000 /- 0.5 -/))
  s := { s with q1 := cr2 * cp2 * cy2 + sr2 * sp2 * sy2 }
  s := { s with q2 := sr2 * cp2 * cy2 - cr2 * sp2 * sy2 }
  s := { s with q3 := cr2 * sp2 * cy2 + sr2 * cp2 * sy2 }
  s := { s with q4 := cr2 * cp2 * sy2 - sr2 * sp2 * cy2 }
  return s

end QuaternionT_double

namespace Vector2p

/-- C++ `void Vector2<double>::zero()`, `AP_Math/vector2.h:140-143`. -/
def zero (s : State) : State := Id.run do
  let mut s := s
  s := { s with y := (Binary64.ofBits 0x0000000000000000 /- 0 -/) }
  s := { s with x := s.y }
  return s

end Vector2p

namespace Vector3p

/-- C++ `Vector3<double>::Vector3(const double x0, const double y0, const double z0)`, `AP_Math/vector3.h:85-88`. -/
def init_double3 (x0 : Binary64) (y0 : Binary64) (z0 : Binary64) : State := Id.run do
  let mut s : State := {}
  s := { s with x := x0 }
  s := { s with y := y0 }
  s := { s with z := z0 }
  return s

end Vector3p

namespace Vector3f

/-- C++ `Vector3<double> Vector3<float>::todouble() const`, `AP_Math/vector3.h:280-282`. -/
def todouble (s : State) : Vector3p.State := Id.run do
  return Vector3p.init_double3 (Binary32.toBinary64 s.x) (Binary32.toBinary64 s.y) (Binary32.toBinary64 s.z)

end Vector3f

namespace Vector3p

/-- C++ `void Vector3<double>::zero()`, `AP_Math/vector3.h:229-232`. -/
def zero (s : State) : State := Id.run do
  let mut s := s
  s := { s with z := (Binary64.ofBits 0x0000000000000000 /- 0 -/) }
  s := { s with y := s.z }
  s := { s with x := s.y }
  return s

end Vector3p

/-- C++ `ftype sq(const double val)`, `AP_Math/AP_Math.h:261-265`. -/
def sq_double (val : Binary64) : Binary64 := Id.run do
  let v : Binary64 := val
  return v * v

/-- C++ `ftype sq(const double first, const double parameters)`, `AP_Math/AP_Math.h:276-279`. -/
def sq_double2 (first parameters : Binary64) : Binary64 := Id.run do
  return sq_double first + sq_double parameters

/-- C++ `ftype sq(const double first, const double parameters, const double parameters)`, `AP_Math/AP_Math.h:276-279`. -/
def sq_double3 (first parameters'1 parameters'2 : Binary64) : Binary64 := Id.run do
  return sq_double first + sq_double2 parameters'1 parameters'2

/-- C++ `ftype norm(const double first, const double second, const double parameters)`, `AP_Math/AP_Math.h:286-289`. -/
def norm_double3 (first second parameters : Binary64) : Binary64 := Id.run do
  return Binary64.sqrt (sq_double3 first second parameters)

namespace Vector3p

/-- C++ `double Vector3<double>::length() const`, `AP_Math/vector3.cpp:324-327`. -/
def length (s : State) : Binary64 := Id.run do
  return Estimator_lib.norm_double3 s.x s.y s.z

/-- C++ `Vector3<double> & Vector3<double>::operator/=(const double num)`, `AP_Math/vector3.cpp:350-354`. -/
def op_div_assign (s : State) (num : Binary64) : State × Vector3p.State := Id.run do
  let mut s := s
  s := { s with x := s.x / num }
  s := { s with y := s.y / num }
  s := { s with z := s.z / num }
  return (s, s)

/-- C++ `void Vector3<double>::normalize()`, `AP_Math/vector3.h:223-226`. -/
def normalize (s : State) : State := Id.run do
  let mut s := s
  let (t'1, _) := op_div_assign s (length s)
  s := t'1
  return s

end Vector3p

-- not read in the Lean: line
set_option linter.unusedVariables false in
/-- C++ `double constrain_value_line(const double amt, const double low, const double high, uint32_t line)`, `AP_Math/AP_Math.cpp:283-304`. -/
def constrain_value_line_double (amt low high : Binary64) (line : UInt32) : Binary64 := Id.run do
  if Binary64.isNaN amt then
    pure ()  -- C++ `AP_InternalError::error(...)`: left out (--drop)
    return (low + high) / (Binary64.ofBits 0x4000000000000000 /- 2 -/)
  if amt < low then
    return low
  if amt > high then
    return high
  return amt

/-- C++ `auto MAX(const double & one, const double & two)`, `AP_Math/AP_Math.h:307-310`. -/
def MAX_double2 (one two : Binary64) : Binary64 := Id.run do
  return if one > two then one else two

namespace Matrix3_double

/-- C++ `Vector3<double> Matrix3<double>::operator*(const Vector3<double> & v) const`, `AP_Math/matrix3.cpp:146-151`. -/
def op_mul_Vector3p (s : State) (v : Vector3p.State) : Vector3p.State := Id.run do
  return Vector3p.init_double3 (s.a.x * v.x + s.a.y * v.y + s.a.z * v.z) (s.b.x * v.x + s.b.y * v.y + s.b.z * v.z) (s.c.x * v.x + s.c.y * v.y + s.c.z * v.z)

end Matrix3_double

/-- C++ `bool is_zero(const double x)`, `AP_Math/ftype.h:68-74`. -/
def is_zero_double (x : Binary64) : Bool := Id.run do
  return decide (Binary64.abs x < (Binary64.ofBits 0x3e80000000000000 /- (double)1/8388608 -/))

namespace QuaternionT_double

/-- C++ `void QuaternionT<double>::from_axis_angle(const Vector3<double> & axis, double theta)`, `AP_Math/quaternion.cpp:469-483`. -/
def from_axis_angle_Vector3p_double (s : State) (axis : Vector3p.State) (theta : Binary64) : State := Id.run do
  let mut s := s
  if Estimator_lib.is_zero_double theta then
    s := { s with q1 := (Binary64.ofBits 0x3ff0000000000000 /- 1.0f -/) }
    s := { s with q4 := (Binary64.ofBits 0x0000000000000000 /- 0.0f -/) }
    s := { s with q3 := s.q4 }
    s := { s with q2 := s.q3 }
    return s
  let st2 : Binary64 := Musl.sin.sin ((Binary64.ofBits 0x3fe0000000000000 /- 0.5 -/) * theta)
  s := { s with q1 := Musl.cos.cos ((Binary64.ofBits 0x3fe0000000000000 /- 0.5 -/) * theta) }
  s := { s with q2 := axis.x * st2 }
  s := { s with q3 := axis.y * st2 }
  s := { s with q4 := axis.z * st2 }
  return s

/-- C++ `void QuaternionT<double>::from_axis_angle(Vector3<double> v)`, `AP_Math/quaternion.cpp:454-464`. -/
def from_axis_angle_Vector3p (s : State) (v : Vector3p.State) : State := Id.run do
  let mut s := s
  let mut v := v
  let theta : Binary64 := Vector3p.length v
  if Estimator_lib.is_zero_double theta then
    s := { s with q1 := (Binary64.ofBits 0x3ff0000000000000 /- 1.0f -/) }
    s := { s with q4 := (Binary64.ofBits 0x0000000000000000 /- 0.0f -/) }
    s := { s with q3 := s.q4 }
    s := { s with q2 := s.q3 }
    return s
  let (t'1, _) := Vector3p.op_div_assign v theta
  v := t'1
  s := from_axis_angle_Vector3p_double s v theta
  return s

/-- C++ `QuaternionT<double> & QuaternionT<double>::operator*=(const QuaternionT<double> & v)`, `AP_Math/quaternion.cpp:762-780`. -/
def op_mul_assign (s : State) (v : QuaternionT_double.State) : State × QuaternionT_double.State := Id.run do
  let mut s := s
  let w1 : Binary64 := s.q1
  let x1 : Binary64 := s.q2
  let y1 : Binary64 := s.q3
  let z1 : Binary64 := s.q4
  let w2 : Binary64 := v.q1
  let x2 : Binary64 := v.q2
  let y2 : Binary64 := v.q3
  let z2 : Binary64 := v.q4
  s := { s with q1 := w1 * w2 - x1 * x2 - y1 * y2 - z1 * z2 }
  s := { s with q2 := w1 * x2 + x1 * w2 + y1 * z2 - z1 * y2 }
  s := { s with q3 := w1 * y2 - x1 * z2 + y1 * w2 + z1 * x2 }
  s := { s with q4 := w1 * z2 + x1 * y2 - y1 * x2 + z1 * w2 }
  return (s, s)

/-- C++ `void QuaternionT<double>::rotate(const Vector3<double> & v)`, `AP_Math/quaternion.cpp:487-492`. -/
def rotate_Vector3p (s : State) (v : Vector3p.State) : State := Id.run do
  let mut s := s
  let mut r : QuaternionT_double.State := QuaternionT_double.init_void
  r := QuaternionT_double.from_axis_angle_Vector3p r v
  let (t'1, _) := op_mul_assign s r
  s := t'1
  return s

/-- C++ `double QuaternionT<double>::length() const`, `AP_Math/quaternion.cpp:633-636`. -/
def length (s : State) : Binary64 := Id.run do
  return Binary64.sqrt (Estimator_lib.sq_double s.q1 + Estimator_lib.sq_double s.q2 + Estimator_lib.sq_double s.q3 + Estimator_lib.sq_double s.q4)

/-- C++ `void QuaternionT<double>::normalize()`, `AP_Math/quaternion.cpp:662-675`. -/
def normalize (s : State) : State := Id.run do
  let mut s := s
  let quatMag : Binary64 := length s
  if !(Estimator_lib.is_zero_double quatMag) then
    let quatMagInv : Binary64 := (Binary64.ofBits 0x3ff0000000000000 /- 1.0f -/) / quatMag
    s := { s with q1 := s.q1 * quatMagInv }
    s := { s with q2 := s.q2 * quatMagInv }
    s := { s with q3 := s.q3 * quatMagInv }
    s := { s with q4 := s.q4 * quatMagInv }
  else
    pure ()  -- C++ `AP_InternalError::error(...)`: left out (--drop)
  return s

/-- C++ `void QuaternionT<double>::rotation_matrix(Matrix3d & m) const`, `AP_Math/quaternion.cpp:34-55`. -/
def rotation_matrix_Matrix3_double (s : State) (m : Matrix3_double.State) : Matrix3_double.State := Id.run do
  let mut m := m
  let q3q3 : Binary64 := s.q3 * s.q3
  let q3q4 : Binary64 := s.q3 * s.q4
  let q2q2 : Binary64 := s.q2 * s.q2
  let q2q3 : Binary64 := s.q2 * s.q3
  let q2q4 : Binary64 := s.q2 * s.q4
  let q1q2 : Binary64 := s.q1 * s.q2
  let q1q3 : Binary64 := s.q1 * s.q3
  let q1q4 : Binary64 := s.q1 * s.q4
  let q4q4 : Binary64 := s.q4 * s.q4
  m := { m with a.x := (Binary64.ofBits 0x3ff0000000000000 /- 1.0f -/) - (Binary64.ofBits 0x4000000000000000 /- 2.0f -/) * (q3q3 + q4q4) }
  m := { m with a.y := (Binary64.ofBits 0x4000000000000000 /- 2.0f -/) * (q2q3 - q1q4) }
  m := { m with a.z := (Binary64.ofBits 0x4000000000000000 /- 2.0f -/) * (q2q4 + q1q3) }
  m := { m with b.x := (Binary64.ofBits 0x4000000000000000 /- 2.0f -/) * (q2q3 + q1q4) }
  m := { m with b.y := (Binary64.ofBits 0x3ff0000000000000 /- 1.0f -/) - (Binary64.ofBits 0x4000000000000000 /- 2.0f -/) * (q2q2 + q4q4) }
  m := { m with b.z := (Binary64.ofBits 0x4000000000000000 /- 2.0f -/) * (q3q4 - q1q2) }
  m := { m with c.x := (Binary64.ofBits 0x4000000000000000 /- 2.0f -/) * (q2q4 - q1q3) }
  m := { m with c.y := (Binary64.ofBits 0x4000000000000000 /- 2.0f -/) * (q3q4 + q1q2) }
  m := { m with c.z := (Binary64.ofBits 0x3ff0000000000000 /- 1.0f -/) - (Binary64.ofBits 0x4000000000000000 /- 2.0f -/) * (q2q2 + q3q3) }
  return m

end QuaternionT_double

/-- C++ `double wrap_2PI(const double radian)`, `AP_Math/AP_Math.cpp:260-267`. -/
def wrap_2PI_double (radian : Binary64) : Binary64 := Id.run do
  let mut res : Binary64 := Musl.fmod.fmod radian (Binary32.toBinary64 ((Binary32.ofBits 0x40490fdb /- (float)884279719003555/281474976710656 -/) * (Binary32.ofBits 0x40000000 /- (float)2 -/)))
  if res < (Binary64.ofBits 0x0000000000000000 /- 0 -/) then
    res := res + (Binary64.ofBits 0x401921fb60000000 /- (double)13176795/2097152 -/)
  return res

/-- C++ `double wrap_PI(const double radian)`, `AP_Math/AP_Math.cpp:270-277`. -/
def wrap_PI_double (radian : Binary64) : Binary64 := Id.run do
  let mut res : Binary64 := wrap_2PI_double radian
  if res > (Binary64.ofBits 0x400921fb54442d18 /- 3.1415926535897931 -/) then
    res := res - ((Binary64.ofBits 0x400921fb54442d18 /- 3.1415926535897931 -/) * (Binary64.ofBits 0x4000000000000000 /- (double)2 -/))
  return res

namespace Vector3p

/-- C++ `Vector3<double> & Vector3<double>::operator*=(const double num)`, `AP_Math/vector3.cpp:343-347`. -/
def op_mul_assign_double (s : State) (num : Binary64) : State × Vector3p.State := Id.run do
  let mut s := s
  s := { s with x := s.x * num }
  s := { s with y := s.y * num }
  s := { s with z := s.z * num }
  return (s, s)

end Vector3p

namespace QuaternionT_double

/-- C++ `void QuaternionT<double>::to_axis_angle(Vector3<double> & v) const`, `AP_Math/quaternion.cpp:497-505`. -/
def to_axis_angle (s : State) (v : Vector3p.State) : Vector3p.State := Id.run do
  let mut v := v
  let l : Binary64 := Binary64.sqrt (Estimator_lib.sq_double s.q2 + Estimator_lib.sq_double s.q3 + Estimator_lib.sq_double s.q4)
  v := Vector3p.init_double3 s.q2 s.q3 s.q4
  if !(Estimator_lib.is_zero_double l) then
    let (t'1, _) := Vector3p.op_div_assign v l
    v := t'1
    let (t'3, _) := Vector3p.op_mul_assign_double v (Estimator_lib.wrap_PI_double ((Binary64.ofBits 0x4000000000000000 /- 2.0f -/) * Musl.atan2.atan2 l s.q1))
    v := t'3
  return v

end QuaternionT_double

namespace Vector3p

/-- C++ `Vector3<double> & Vector3<double>::operator+=(const Vector3<double> & v)`, `AP_Math/vector3.cpp:376-380`. -/
def op_add_assign (s : State) (v : Vector3p.State) : State × Vector3p.State := Id.run do
  let mut s := s
  s := { s with x := s.x + v.x }
  s := { s with y := s.y + v.y }
  s := { s with z := s.z + v.z }
  return (s, s)

end Vector3p

/-- C++ `float radians(int deg)`, `AP_Math/AP_Math.h:237-240`. -/
def radians_int32_t (deg : Int32) : Binary32 := Id.run do
  return Int32.toBinary32 deg * ((Binary32.ofBits 0x40490fdb /- (float)884279719003555/281474976710656 -/) / (Binary32.ofBits 0x43340000 /- 180 -/))

namespace Vector3p

/-- C++ `Vector3<double> Vector3<double>::operator-(const Vector3<double> & v) const`, `AP_Math/vector3.cpp:395-398`. -/
def op_sub_Vector3p (s : State) (v : Vector3p.State) : Vector3p.State := Id.run do
  return Vector3p.init_double3 (s.x - v.x) (s.y - v.y) (s.z - v.z)

/-- C++ `Vector3<double> Vector3<double>::operator/(const double num) const`, `AP_Math/vector3.cpp:383-386`. -/
def op_div (s : State) (num : Binary64) : Vector3p.State := Id.run do
  return Vector3p.init_double3 (s.x / num) (s.y / num) (s.z / num)

/-- C++ `Vector3<double> & Vector3<double>::operator-=(const Vector3<double> & v)`, `AP_Math/vector3.cpp:357-361`. -/
def op_sub_assign (s : State) (v : Vector3p.State) : State × Vector3p.State := Id.run do
  let mut s := s
  s := { s with x := s.x - v.x }
  s := { s with y := s.y - v.y }
  s := { s with z := s.z - v.z }
  return (s, s)

/-- C++ `Vector3<double> Vector3<double>::operator*(const double num) const`, `AP_Math/vector3.cpp:389-392`. -/
def op_mul_double (s : State) (num : Binary64) : Vector3p.State := Id.run do
  return Vector3p.init_double3 (s.x * num) (s.y * num) (s.z * num)

end Vector3p

/-- C++ `auto MIN(const float & one, const double & two)`, `AP_Math/AP_Math.h:300-303`. -/
def MIN_float_double (one : Binary32) (two : Binary64) : Binary64 := Id.run do
  return if Binary32.toBinary64 one < two then Binary32.toBinary64 one else two

/-- C++ `auto MAX(const float & one, const double & two)`, `AP_Math/AP_Math.h:307-310`. -/
def MAX_float_double (one : Binary32) (two : Binary64) : Binary64 := Id.run do
  return if Binary32.toBinary64 one > two then Binary32.toBinary64 one else two

/-- C++ `typename std::enable_if<std::is_floating_point<typename std::common_type<double, double>::type>::value, bool>::type is_equal(const double v_1, const double v_2)`, `AP_Math/AP_Math.cpp:25-41`. -/
def is_equal_double2 (v_1 v_2 : Binary64) : Bool := Id.run do
  if true then
    return decide (Binary64.abs (v_1 - v_2) < (Binary64.ofBits 0x3cb0000000000000 /- (double)1/4503599627370496 -/))
  return decide (Binary32.abs (Binary64.toBinary32 (v_1 - v_2)) < (Binary32.ofBits 0x34000000 /- 1.1920929E-7 -/))

namespace Vector3p

/-- C++ `bool Vector3<double>::operator!=(const Vector3<double> & v) const`, `AP_Math/vector3.cpp:419-422`. -/
def op_ne (s : State) (v : Vector3p.State) : Bool := Id.run do
  return (!(Estimator_lib.is_equal_double2 s.x v.x) || !(Estimator_lib.is_equal_double2 s.y v.y) || !(Estimator_lib.is_equal_double2 s.z v.z))

end Vector3p

namespace QuaternionT_double

/-- C++ `bool QuaternionT<double>::is_zero() const`, `AP_Math/quaternion.cpp:679-681`. -/
def is_zero (s : State) : Bool := Id.run do
  return Estimator_lib.is_zero_double s.q1 && Estimator_lib.is_zero_double s.q2 && Estimator_lib.is_zero_double s.q3 && Estimator_lib.is_zero_double s.q4

end QuaternionT_double

/-- C++ `ftype norm(const double first, const double second)`, `AP_Math/AP_Math.h:286-289`. -/
def norm_double2 (first second : Binary64) : Binary64 := Id.run do
  return Binary64.sqrt (sq_double2 first second)

namespace Vector2p

/-- C++ `double Vector2<double>::length() const`, `AP_Math/vector2.cpp:30-33`. -/
def length (s : State) : Binary64 := Id.run do
  return Estimator_lib.norm_double2 s.x s.y

end Vector2p

namespace Vector3p

/-- C++ `const Vector2<double> & Vector3<double>::xy() const`, `AP_Math/vector3.h:203-205`. -/
def xy (s : State) : Vector2p.State := Id.run do
  return { x := s.x, y := s.y }

end Vector3p

/-- C++ `int constrain_value(const int amt, const int low, const int high)`, `AP_Math/AP_Math.cpp:310-331`. -/
def constrain_value_int32_t (amt low high : Int32) : Int32 := Id.run do
  if false then
    if false then
      pure ()  -- C++ `AP_InternalError::error(...)`: left out (--drop)
      return (low + high) / (2 : Int32)
  if amt < low then
    return low
  if amt > high then
    return high
  return amt

/-- C++ `int32_t constrain_int32(const int32_t amt, const int32_t low, const int32_t high)`, `AP_Math/AP_Math.h:201-204`. -/
def constrain_int32 (amt low high : Int32) : Int32 := Id.run do
  return constrain_value_int32_t amt low high

/-- C++ `auto MIN(const unsigned int & one, const unsigned int & two)`, `AP_Math/AP_Math.h:300-303`. -/
def MIN_uint32_t2 (one two : UInt32) : UInt32 := Id.run do
  return if one < two then one else two

/-- C++ `auto MIN(const double & one, const float & two)`, `AP_Math/AP_Math.h:300-303`. -/
def MIN_double_float (one : Binary64) (two : Binary32) : Binary64 := Id.run do
  return if one < Binary32.toBinary64 two then one else Binary32.toBinary64 two

/-- C++ `auto MAX(const unsigned int & one, const unsigned int & two)`, `AP_Math/AP_Math.h:307-310`. -/
def MAX_uint32_t2 (one two : UInt32) : UInt32 := Id.run do
  return if one > two then one else two

/-- C++ `auto MAX(const unsigned char & one, const unsigned char & two)`, `AP_Math/AP_Math.h:307-310`. -/
def MAX_uint8_t2 (one two : UInt8) : UInt8 := Id.run do
  return if UInt32.toInt32 (UInt8.toUInt32 one) > UInt32.toInt32 (UInt8.toUInt32 two) then one else two

namespace Matrix3_double

/-- C++ `void Matrix3<double>::zero()`, `AP_Math/matrix3.h:222-224`. -/
def zero (s : State) : State := Id.run do
  let mut s := s
  s := { a := { x := (Binary64.ofBits 0x0000000000000000 /- 0.0 -/), y := (Binary64.ofBits 0x0000000000000000 /- 0.0 -/), z := (Binary64.ofBits 0x0000000000000000 /- 0.0 -/) }, b := { x := (Binary64.ofBits 0x0000000000000000 /- 0.0 -/), y := (Binary64.ofBits 0x0000000000000000 /- 0.0 -/), z := (Binary64.ofBits 0x0000000000000000 /- 0.0 -/) }, c := { x := (Binary64.ofBits 0x0000000000000000 /- 0.0 -/), y := (Binary64.ofBits 0x0000000000000000 /- 0.0 -/), z := (Binary64.ofBits 0x0000000000000000 /- 0.0 -/) } }
  return s

end Matrix3_double

namespace QuaternionT_double

/-- C++ `void QuaternionT<double>::initialise()`, `AP_Math/quaternion.h:153-157`. -/
def initialise (s : State) : State := Id.run do
  let mut s := s
  s := { s with q1 := (Binary64.ofBits 0x3ff0000000000000 /- 1.0f -/) }
  s := { s with q4 := (Binary64.ofBits 0x0000000000000000 /- 0.0f -/) }
  s := { s with q3 := s.q4 }
  s := { s with q2 := s.q3 }
  return s

end QuaternionT_double

namespace Matrix3_double

/-- C++ `Vector3<double> Matrix3<double>::mul_transpose(const Vector3<double> & v) const`, `AP_Math/matrix3.cpp:163-168`. -/
def mul_transpose (s : State) (v : Vector3p.State) : Vector3p.State := Id.run do
  return Vector3p.init_double3 (s.a.x * v.x + s.b.x * v.y + s.c.x * v.z) (s.a.y * v.x + s.b.y * v.y + s.c.y * v.z) (s.a.z * v.x + s.b.z * v.y + s.c.z * v.z)

end Matrix3_double

namespace Vector3p

/-- C++ `bool Vector3<double>::is_zero() const`, `AP_Math/vector3.h:325-327`. -/
def is_zero (s : State) : Bool := Id.run do
  return Estimator_lib.is_zero_double s.x && Estimator_lib.is_zero_double s.y && Estimator_lib.is_zero_double s.z

/-- C++ `Vector3<double> Vector3<double>::operator%(const Vector3<double> & v) const`, `AP_Math/vector3.cpp:310-314`. -/
def op_mod (s : State) (v : Vector3p.State) : Vector3p.State := Id.run do
  let temp : Vector3p.State := Vector3p.init_double3 (s.y * v.z - s.z * v.y) (s.z * v.x - s.x * v.z) (s.x * v.y - s.y * v.x)
  return temp

end Vector3p

namespace Vector2p

/-- C++ `Vector2<double>::Vector2(const double x0, const double y0)`, `AP_Math/vector2.h:55-57`. -/
def init_double2 (x0 : Binary64) (y0 : Binary64) : State := Id.run do
  let mut s : State := {}
  s := { s with x := x0 }
  s := { s with y := y0 }
  return s

end Vector2p

namespace Vector2p

/-- C++ `Vector2<double> & Vector2<double>::operator+=(const Vector2<double> & v)`, `AP_Math/vector2.cpp:96-100`. -/
def op_add_assign (s : State) (v : Vector2p.State) : State × Vector2p.State := Id.run do
  let mut s := s
  s := { s with x := s.x + v.x }
  s := { s with y := s.y + v.y }
  return (s, s)

/-- C++ `Vector2<double> Vector2<double>::operator*(const double num) const`, `AP_Math/vector2.cpp:109-112`. -/
def op_mul_double (s : State) (num : Binary64) : Vector2p.State := Id.run do
  return Vector2p.init_double2 (s.x * num) (s.y * num)

end Vector2p

/-- C++ `double radians(double deg)`, `AP_Math/AP_Math.h:227-230`. -/
def radians_double (deg : Binary64) : Binary64 := Id.run do
  return deg * (Binary64.ofBits 0x3f91df46a0000000 /- (double)9370165/536870912 -/)

namespace Matrix3_double

/-- C++ `Matrix3<double>::Matrix3(const double ax, const double ay, const double az, const double bx, const double by, const double bz, const double cx, const double cy, const double cz)`, `AP_Math/matrix3.h:67-72`. -/
def init_double9 (ax : Binary64) (ay : Binary64) (az : Binary64) (bx : Binary64) («by» : Binary64) (bz : Binary64) (cx : Binary64) (cy : Binary64) (cz : Binary64) : State := Id.run do
  let mut s : State := {}
  s := { s with a := Vector3p.init_double3 ax ay az }
  s := { s with b := Vector3p.init_double3 bx «by» bz }
  s := { s with c := Vector3p.init_double3 cx cy cz }
  return s

/-- C++ `Matrix3<double>::Matrix3(const Vector3<double> & a0, const Vector3<double> & b0, const Vector3<double> & c0)`, `AP_Math/matrix3.h:61-64`. -/
def init_Vector3p3 (a0 : Vector3p.State) (b0 : Vector3p.State) (c0 : Vector3p.State) : State := Id.run do
  let mut s : State := {}
  s := { s with a := a0 }
  s := { s with b := b0 }
  s := { s with c := c0 }
  return s

/-- C++ `Matrix3<double> Matrix3<double>::operator*(const Matrix3<double> & m) const`, `AP_Math/matrix3.cpp:172-184`. -/
def op_mul_Matrix3_double (s : State) (m : Matrix3_double.State) : Matrix3_double.State := Id.run do
  let temp : Matrix3_double.State := Matrix3_double.init_Vector3p3 (Vector3p.init_double3 (s.a.x * m.a.x + s.a.y * m.b.x + s.a.z * m.c.x) (s.a.x * m.a.y + s.a.y * m.b.y + s.a.z * m.c.y) (s.a.x * m.a.z + s.a.y * m.b.z + s.a.z * m.c.z)) (Vector3p.init_double3 (s.b.x * m.a.x + s.b.y * m.b.x + s.b.z * m.c.x) (s.b.x * m.a.y + s.b.y * m.b.y + s.b.z * m.c.y) (s.b.x * m.a.z + s.b.y * m.b.z + s.b.z * m.c.z)) (Vector3p.init_double3 (s.c.x * m.a.x + s.c.y * m.b.x + s.c.z * m.c.x) (s.c.x * m.a.y + s.c.y * m.b.y + s.c.z * m.c.y) (s.c.x * m.a.z + s.c.y * m.b.z + s.c.z * m.c.z))
  return temp

/-- C++ `Matrix3<double> Matrix3<double>::transposed() const`, `AP_Math/matrix3.cpp:187-192`. -/
def transposed (s : State) : Matrix3_double.State := Id.run do
  return Matrix3_double.init_Vector3p3 (Vector3p.init_double3 s.a.x s.b.x s.c.x) (Vector3p.init_double3 s.a.y s.b.y s.c.y) (Vector3p.init_double3 s.a.z s.b.z s.c.z)

end Matrix3_double

namespace QuaternionT_double

/-- C++ `QuaternionT<double>::QuaternionT(const double _q1, const double _q2, const double _q3, const double _q4)`, `AP_Math/quaternion.h:42-45`. -/
def init_double4 (_q1 : Binary64) (_q2 : Binary64) (_q3 : Binary64) (_q4 : Binary64) : State := Id.run do
  let mut s : State := {}
  s := { s with q1 := _q1 }
  s := { s with q2 := _q2 }
  s := { s with q3 := _q3 }
  s := { s with q4 := _q4 }
  return s

/-- C++ `QuaternionT<double> QuaternionT<double>::inverse() const`, `AP_Math/quaternion.cpp:647-650`. -/
def inverse (s : State) : QuaternionT_double.State := Id.run do
  return QuaternionT_double.init_double4 s.q1 (-s.q2) (-s.q3) (-s.q4)

end QuaternionT_double

namespace Matrix3f

/-- C++ `Matrix3<float>::Matrix3(const Vector3<float> & a0, const Vector3<float> & b0, const Vector3<float> & c0)`, `AP_Math/matrix3.h:61-64`. -/
def init_Vector3f3 (a0 : Vector3f.State) (b0 : Vector3f.State) (c0 : Vector3f.State) : State := Id.run do
  let mut s : State := {}
  s := { s with a := a0 }
  s := { s with b := b0 }
  s := { s with c := c0 }
  return s

/-- C++ `Matrix3<float> Matrix3<float>::transposed() const`, `AP_Math/matrix3.cpp:187-192`. -/
def transposed (s : State) : Matrix3f.State := Id.run do
  return Matrix3f.init_Vector3f3 (Vector3f.init_float3 s.a.x s.b.x s.c.x) (Vector3f.init_float3 s.a.y s.b.y s.c.y) (Vector3f.init_float3 s.a.z s.b.z s.c.z)

end Matrix3f

/-- C++ `typename std::enable_if<std::is_floating_point<typename std::common_type<float, float>::type>::value, bool>::type is_equal(const float v_1, const float v_2)`, `AP_Math/AP_Math.cpp:25-41`. -/
def is_equal_float2 (v_1 v_2 : Binary32) : Bool := Id.run do
  if false then
    return decide (Binary32.toBinary64 (Binary32.abs (v_1 - v_2)) < (Binary64.ofBits 0x3cb0000000000000 /- (double)1/4503599627370496 -/))
  return decide (Binary32.abs (v_1 - v_2) < (Binary32.ofBits 0x34000000 /- 1.1920929E-7 -/))

namespace Vector3f

/-- C++ `bool Vector3<float>::operator==(const Vector3<float> & v) const`, `AP_Math/vector3.cpp:413-416`. -/
def op_eq (s : State) (v : Vector3f.State) : Bool := Id.run do
  return (Estimator_lib.is_equal_float2 s.x v.x && Estimator_lib.is_equal_float2 s.y v.y && Estimator_lib.is_equal_float2 s.z v.z)

end Vector3f

namespace QuaternionT_double

/-- C++ `void QuaternionT<double>::rotation_matrix(Matrix3f & m) const`, `AP_Math/quaternion.cpp:59-80`. -/
def rotation_matrix_Matrix3f (s : State) (m : Matrix3f.State) : Matrix3f.State := Id.run do
  let mut m := m
  let q3q3 : Binary64 := s.q3 * s.q3
  let q3q4 : Binary64 := s.q3 * s.q4
  let q2q2 : Binary64 := s.q2 * s.q2
  let q2q3 : Binary64 := s.q2 * s.q3
  let q2q4 : Binary64 := s.q2 * s.q4
  let q1q2 : Binary64 := s.q1 * s.q2
  let q1q3 : Binary64 := s.q1 * s.q3
  let q1q4 : Binary64 := s.q1 * s.q4
  let q4q4 : Binary64 := s.q4 * s.q4
  m := { m with a.x := Binary64.toBinary32 ((Binary64.ofBits 0x3ff0000000000000 /- 1.0f -/) - (Binary64.ofBits 0x4000000000000000 /- 2.0f -/) * (q3q3 + q4q4)) }
  m := { m with a.y := Binary64.toBinary32 ((Binary64.ofBits 0x4000000000000000 /- 2.0f -/) * (q2q3 - q1q4)) }
  m := { m with a.z := Binary64.toBinary32 ((Binary64.ofBits 0x4000000000000000 /- 2.0f -/) * (q2q4 + q1q3)) }
  m := { m with b.x := Binary64.toBinary32 ((Binary64.ofBits 0x4000000000000000 /- 2.0f -/) * (q2q3 + q1q4)) }
  m := { m with b.y := Binary64.toBinary32 ((Binary64.ofBits 0x3ff0000000000000 /- 1.0f -/) - (Binary64.ofBits 0x4000000000000000 /- 2.0f -/) * (q2q2 + q4q4)) }
  m := { m with b.z := Binary64.toBinary32 ((Binary64.ofBits 0x4000000000000000 /- 2.0f -/) * (q3q4 - q1q2)) }
  m := { m with c.x := Binary64.toBinary32 ((Binary64.ofBits 0x4000000000000000 /- 2.0f -/) * (q2q4 - q1q3)) }
  m := { m with c.y := Binary64.toBinary32 ((Binary64.ofBits 0x4000000000000000 /- 2.0f -/) * (q3q4 + q1q2)) }
  m := { m with c.z := Binary64.toBinary32 ((Binary64.ofBits 0x3ff0000000000000 /- 1.0f -/) - (Binary64.ofBits 0x4000000000000000 /- 2.0f -/) * (q2q2 + q3q3)) }
  return m

end QuaternionT_double

namespace Vector3p

/-- C++ `Vector3<float> Vector3<double>::tofloat() const`, `AP_Math/vector3.h:277-279`. -/
def tofloat (s : State) : Vector3f.State := Id.run do
  return Vector3f.init_float3 (Binary64.toBinary32 s.x) (Binary64.toBinary32 s.y) (Binary64.toBinary32 s.z)

/-- C++ `Vector3<double> Vector3<double>::operator+(const Vector3<double> & v) const`, `AP_Math/vector3.cpp:401-404`. -/
def op_add (s : State) (v : Vector3p.State) : Vector3p.State := Id.run do
  return Vector3p.init_double3 (s.x + v.x) (s.y + v.y) (s.z + v.z)

end Vector3p

/-- C++ `float wrap_360(const float angle)`, `AP_Math/AP_Math.cpp:184-191`. -/
def wrap_360_float (angle : Binary32) : Binary32 := Id.run do
  let mut res : Binary32 := Musl.fmodf.fmodf angle (Binary32.ofBits 0x43b40000 /- 360.0f -/)
  if res < (Binary32.ofBits 0x00000000 /- 0 -/) then
    res := res + (Binary32.ofBits 0x43b40000 /- 360.0f -/)
  return res

/-- C++ `float safe_sqrt(const float v)`, `AP_Math/AP_Math.cpp:72-81`. -/
def safe_sqrt_float (v : Binary32) : Binary32 := Id.run do
  let val : Binary32 := v
  if decide (Binary32.toBinary64 val ≥ Int32.toBinary64 (0 : Int32)) then
    return Binary32.sqrt val
  return (Binary32.ofBits 0x00000000 /- 0 -/)

/-- C++ `float safe_asin(const float v)`, `AP_Math/AP_Math.cpp:50-63`. -/
def safe_asin_float (v : Binary32) : Binary32 := Id.run do
  let f : Binary32 := v
  if Binary32.isNaN f then
    return (Binary32.ofBits 0x00000000 /- 0.0f -/)
  if f ≥ (Binary32.ofBits 0x3f800000 /- 1.0f -/) then
    return (Binary32.ofBits 0x3fc90fdb /- (float)884279719003555/562949953421312 -/)
  if f ≤ -(Binary32.ofBits 0x3f800000 /- 1.0f -/) then
    return (Binary32.ofBits 0xbfc90fdb /- (float)-884279719003555/562949953421312 -/)
  return Musl.asinf.asinf f

namespace Matrix3f

/-- C++ `void Matrix3<float>::to_euler(float * roll, float * pitch, float * yaw) const`, `AP_Math/matrix3.cpp:49-60`. -/
def to_euler (s : State) (roll'given : Bool) (roll : Binary32) (pitch'given : Bool) (pitch : Binary32) (yaw'given : Bool) (yaw : Binary32) : Binary32 × Binary32 × Binary32 := Id.run do
  let mut roll := roll
  let mut pitch := pitch
  let mut yaw := yaw
  if pitch'given then
    pitch := -(Estimator_lib.safe_asin_float s.c.x)
  if roll'given then
    roll := Musl.atan2f.atan2f s.c.y s.c.z
  if yaw'given then
    yaw := Musl.atan2f.atan2f s.b.x s.a.x
  return (roll, pitch, yaw)

end Matrix3f

namespace Vector2f

/-- C++ `Vector2<float> & Vector2<float>::operator/=(const float num)`, `AP_Math/vector2.cpp:70-74`. -/
def op_div_assign (s : State) (num : Binary32) : State × Vector2f.State := Id.run do
  let mut s := s
  s := { s with x := s.x / num }
  s := { s with y := s.y / num }
  return (s, s)

/-- C++ `void Vector2<float>::normalize()`, `AP_Math/vector2.cpp:268-271`. -/
def normalize (s : State) : State := Id.run do
  let mut s := s
  let (t'1, _) := op_div_assign s (length s)
  s := t'1
  return s

/-- C++ `bool Vector2<float>::is_inf() const`, `AP_Math/vector2.cpp:90-93`. -/
def is_inf (s : State) : Bool := Id.run do
  return Binary32.isInf s.x || Binary32.isInf s.y

/-- C++ `bool Vector2<float>::is_nan() const`, `AP_Math/vector2.cpp:84-87`. -/
def is_nan (s : State) : Bool := Id.run do
  return Binary32.isNaN s.x || Binary32.isNaN s.y

end Vector2f

namespace Matrix3f

/-- C++ `Matrix3<float> Matrix3<float>::operator*(const Matrix3<float> & m) const`, `AP_Math/matrix3.cpp:172-184`. -/
def op_mul_Matrix3f (s : State) (m : Matrix3f.State) : Matrix3f.State := Id.run do
  let temp : Matrix3f.State := Matrix3f.init_Vector3f3 (Vector3f.init_float3 (s.a.x * m.a.x + s.a.y * m.b.x + s.a.z * m.c.x) (s.a.x * m.a.y + s.a.y * m.b.y + s.a.z * m.c.y) (s.a.x * m.a.z + s.a.y * m.b.z + s.a.z * m.c.z)) (Vector3f.init_float3 (s.b.x * m.a.x + s.b.y * m.b.x + s.b.z * m.c.x) (s.b.x * m.a.y + s.b.y * m.b.y + s.b.z * m.c.y) (s.b.x * m.a.z + s.b.y * m.b.z + s.b.z * m.c.z)) (Vector3f.init_float3 (s.c.x * m.a.x + s.c.y * m.b.x + s.c.z * m.c.x) (s.c.x * m.a.y + s.c.y * m.b.y + s.c.z * m.c.y) (s.c.x * m.a.z + s.c.y * m.b.z + s.c.z * m.c.z))
  return temp

end Matrix3f

namespace Matrix3f

/-- C++ `Matrix3<float> Matrix3<float>::operator+(const Matrix3<float> & m) const`, `AP_Math/matrix3.h:99-102`. -/
def op_add (s : State) (m : Matrix3f.State) : Matrix3f.State := Id.run do
  return Matrix3f.init_Vector3f3 (Vector3f.op_add s.a m.a) (Vector3f.op_add s.b m.b) (Vector3f.op_add s.c m.c)

/-- C++ `Matrix3<float> & Matrix3<float>::operator+=(const Matrix3<float> & m)`, `AP_Math/matrix3.h:103-106`. -/
def op_add_assign (s : State) (m : Matrix3f.State) : State × Matrix3f.State := Id.run do
  let mut s := s
  s := op_add s m
  return (s, s)

/-- C++ `void Matrix3<float>::rotate(const Vector3<float> & g)`, `AP_Math/matrix3.cpp:120-127`. -/
def rotate (s : State) (g : Vector3f.State) : State := Id.run do
  let mut s := s
  let (t'1, _) := op_add_assign s (Matrix3f.init_float9 (s.a.y * g.z - s.a.z * g.y) (s.a.z * g.x - s.a.x * g.z) (s.a.x * g.y - s.a.y * g.x) (s.b.y * g.z - s.b.z * g.y) (s.b.z * g.x - s.b.x * g.z) (s.b.x * g.y - s.b.y * g.x) (s.c.y * g.z - s.c.z * g.y) (s.c.z * g.x - s.c.x * g.z) (s.c.x * g.y - s.c.y * g.x))
  s := t'1
  return s

end Matrix3f

namespace Matrix3f

/-- C++ `bool Matrix3<float>::is_nan()`, `AP_Math/matrix3.h:233-236`. -/
def is_nan (s : State) : Bool := Id.run do
  return Vector3f.is_nan s.a || Vector3f.is_nan s.b || Vector3f.is_nan s.c

end Matrix3f

/-- C++ `float wrap_180(const float angle)`, `AP_Math/AP_Math.cpp:150-157`. -/
def wrap_180_float (angle : Binary32) : Binary32 := Id.run do
  let mut res : Binary32 := wrap_360_float angle
  if res > (Binary32.ofBits 0x43340000 /- 180 -/) then
    res := res - (Binary32.ofBits 0x43b40000 /- 360 -/)
  return res

namespace Matrix3f

/-- C++ `Vector2<float> Matrix3<float>::mulXY(const Vector3<float> & v) const`, `AP_Math/matrix3.cpp:155-159`. -/
def mulXY (s : State) (v : Vector3f.State) : Vector2f.State := Id.run do
  return Vector2f.init_float2 (s.a.x * v.x + s.a.y * v.y + s.a.z * v.z) (s.b.x * v.x + s.b.y * v.y + s.b.z * v.z)

end Matrix3f

namespace Vector2f

/-- C++ `float Vector2<float>::operator%(const Vector2<float> & v) const`, `AP_Math/vector2.cpp:57-60`. -/
def op_mod (s : State) (v : Vector2f.State) : Binary32 := Id.run do
  return s.x * v.y - s.y * v.x

end Vector2f

namespace Vector3f

/-- C++ `Vector3<float> & Vector3<float>::operator*=(const Vector3<float> & v)`, `AP_Math/vector3.h:130-133`. -/
def op_mul_assign_Vector3f (s : State) (v : Vector3f.State) : State × Vector3f.State := Id.run do
  let mut s := s
  s := { s with x := s.x * v.x }
  s := { s with y := s.y * v.y }
  s := { s with z := s.z * v.z }
  return (s, s)

end Vector3f

/-- C++ `float wrap_2PI(const float radian)`, `AP_Math/AP_Math.cpp:251-258`. -/
def wrap_2PI_float (radian : Binary32) : Binary32 := Id.run do
  let mut res : Binary32 := Musl.fmodf.fmodf radian ((Binary32.ofBits 0x40490fdb /- (float)884279719003555/281474976710656 -/) * (Binary32.ofBits 0x40000000 /- (float)2 -/))
  if res < (Binary32.ofBits 0x00000000 /- 0 -/) then
    res := res + ((Binary32.ofBits 0x40490fdb /- (float)884279719003555/281474976710656 -/) * (Binary32.ofBits 0x40000000 /- (float)2 -/))
  return res

/-- C++ `float wrap_PI(const float radian)`, `AP_Math/AP_Math.cpp:270-277`. -/
def wrap_PI_float (radian : Binary32) : Binary32 := Id.run do
  let mut res : Binary32 := wrap_2PI_float radian
  if res > (Binary32.ofBits 0x40490fdb /- (float)884279719003555/281474976710656 -/) then
    res := res - (Binary32.ofBits 0x40c90fdb /- (float)884279719003555/140737488355328 -/)
  return res

/-- C++ `auto MAX(const float & one, const int & two)`, `AP_Math/AP_Math.h:307-310`. -/
def MAX_float_int32_t (one : Binary32) (two : Int32) : Binary32 := Id.run do
  return if one > Int32.toBinary32 two then one else Int32.toBinary32 two

namespace Matrix3f

/-- C++ `Vector3<float> Matrix3<float>::colx() const`, `AP_Math/matrix3.h:163-166`. -/
def colx (s : State) : Vector3f.State := Id.run do
  return Vector3f.init_float3 s.a.x s.b.x s.c.x

end Matrix3f

namespace Vector3f

/-- C++ `void Vector3<float>::normalize()`, `AP_Math/vector3.h:223-226`. -/
def normalize (s : State) : State := Id.run do
  let mut s := s
  let (t'1, _) := op_div_assign s (length s)
  s := t'1
  return s

end Vector3f

namespace Vector2f

/-- C++ `Vector2<float>::Vector2()`, `AP_Math/vector2.h:50-52`. -/
def init_void : State := Id.run do
  let mut s : State := {}
  s := { s with x := (Binary32.ofBits 0x00000000 /- 0 -/) }
  s := { s with y := (Binary32.ofBits 0x00000000 /- 0 -/) }
  return s

/-- C++ `Vector2<float> Vector2<float>::operator+(const Vector2<float> & v) const`, `AP_Math/vector2.cpp:121-124`. -/
def op_add (s : State) (v : Vector2f.State) : Vector2f.State := Id.run do
  return Vector2f.init_float2 (s.x + v.x) (s.y + v.y)

/-- C++ `Vector2<float> Vector2<float>::operator*(const float num) const`, `AP_Math/vector2.cpp:109-112`. -/
def op_mul_float (s : State) (num : Binary32) : Vector2f.State := Id.run do
  return Vector2f.init_float2 (s.x * num) (s.y * num)

/-- C++ `Vector2<float> & Vector2<float>::operator*=(const float num)`, `AP_Math/vector2.cpp:63-67`. -/
def op_mul_assign (s : State) (num : Binary32) : State × Vector2f.State := Id.run do
  let mut s := s
  s := { s with x := s.x * num }
  s := { s with y := s.y * num }
  return (s, s)

/-- C++ `Vector2<float> & Vector2<float>::operator+=(const Vector2<float> & v)`, `AP_Math/vector2.cpp:96-100`. -/
def op_add_assign (s : State) (v : Vector2f.State) : State × Vector2f.State := Id.run do
  let mut s := s
  s := { s with x := s.x + v.x }
  s := { s with y := s.y + v.y }
  return (s, s)

end Vector2f

namespace Quaternion

/-- C++ `void QuaternionT<float>::from_axis_angle(const Vector3<float> & axis, float theta)`, `AP_Math/quaternion.cpp:469-483`. -/
def from_axis_angle_Vector3f_float (s : State) (axis : Vector3f.State) (theta : Binary32) : State := Id.run do
  let mut s := s
  if Estimator_lib.is_zero_float theta then
    s := { s with q1 := (Binary32.ofBits 0x3f800000 /- 1.0f -/) }
    s := { s with q4 := (Binary32.ofBits 0x00000000 /- 0.0f -/) }
    s := { s with q3 := s.q4 }
    s := { s with q2 := s.q3 }
    return s
  let st2 : Binary32 := Binary64.toBinary32 (Musl.sin.sin ((Binary64.ofBits 0x3fe0000000000000 /- 0.5 -/) * Binary32.toBinary64 theta))
  s := { s with q1 := Binary64.toBinary32 (Musl.cos.cos ((Binary64.ofBits 0x3fe0000000000000 /- 0.5 -/) * Binary32.toBinary64 theta)) }
  s := { s with q2 := axis.x * st2 }
  s := { s with q3 := axis.y * st2 }
  s := { s with q4 := axis.z * st2 }
  return s

/-- C++ `void QuaternionT<float>::from_axis_angle(Vector3<float> v)`, `AP_Math/quaternion.cpp:454-464`. -/
def from_axis_angle_Vector3f (s : State) (v : Vector3f.State) : State := Id.run do
  let mut s := s
  let mut v := v
  let theta : Binary32 := Vector3f.length v
  if Estimator_lib.is_zero_float theta then
    s := { s with q1 := (Binary32.ofBits 0x3f800000 /- 1.0f -/) }
    s := { s with q4 := (Binary32.ofBits 0x00000000 /- 0.0f -/) }
    s := { s with q3 := s.q4 }
    s := { s with q2 := s.q3 }
    return s
  let (t'1, _) := Vector3f.op_div_assign v theta
  v := t'1
  s := from_axis_angle_Vector3f_float s v theta
  return s

/-- C++ `QuaternionT<float> & QuaternionT<float>::operator*=(const QuaternionT<float> & v)`, `AP_Math/quaternion.cpp:762-780`. -/
def op_mul_assign (s : State) (v : Quaternion.State) : State × Quaternion.State := Id.run do
  let mut s := s
  let w1 : Binary32 := s.q1
  let x1 : Binary32 := s.q2
  let y1 : Binary32 := s.q3
  let z1 : Binary32 := s.q4
  let w2 : Binary32 := v.q1
  let x2 : Binary32 := v.q2
  let y2 : Binary32 := v.q3
  let z2 : Binary32 := v.q4
  s := { s with q1 := w1 * w2 - x1 * x2 - y1 * y2 - z1 * z2 }
  s := { s with q2 := w1 * x2 + x1 * w2 + y1 * z2 - z1 * y2 }
  s := { s with q3 := w1 * y2 - x1 * z2 + y1 * w2 + z1 * x2 }
  s := { s with q4 := w1 * z2 + x1 * y2 - y1 * x2 + z1 * w2 }
  return (s, s)

/-- C++ `void QuaternionT<float>::rotate(const Vector3<float> & v)`, `AP_Math/quaternion.cpp:487-492`. -/
def rotate_Vector3f (s : State) (v : Vector3f.State) : State := Id.run do
  let mut s := s
  let mut r : Quaternion.State := Quaternion.init_void
  r := Quaternion.from_axis_angle_Vector3f r v
  let (t'1, _) := op_mul_assign s r
  s := t'1
  return s

/-- C++ `void QuaternionT<float>::from_rotation_matrix(const Matrix3<float> & m)`, `AP_Math/quaternion.cpp:86-129`. -/
def from_rotation_matrix (s : State) (m : Matrix3f.State) : State := Id.run do
  let mut s := s
  let tr : Binary32 := m.a.x + m.b.y + m.c.z
  if tr > (Binary32.ofBits 0x00000000 /- 0 -/) then
    let S : Binary32 := Binary32.sqrt (tr + (Binary32.ofBits 0x3f800000 /- (float)1 -/)) * (Binary32.ofBits 0x40000000 /- 2 -/)
    s := { s with q1 := (Binary32.ofBits 0x3e800000 /- 0.25f -/) * S }
    s := { s with q2 := (m.c.y - m.b.z) / S }
    s := { s with q3 := (m.a.z - m.c.x) / S }
    s := { s with q4 := (m.b.x - m.a.y) / S }
  else if (decide (m.a.x > m.b.y)) && (decide (m.a.x > m.c.z)) then
    let S'2 : Binary32 := Binary32.sqrt ((Binary32.ofBits 0x3f800000 /- 1 -/) + m.a.x - m.b.y - m.c.z) * (Binary32.ofBits 0x40000000 /- 2.0f -/)
    s := { s with q1 := (m.c.y - m.b.z) / S'2 }
    s := { s with q2 := (Binary32.ofBits 0x3e800000 /- 0.25f -/) * S'2 }
    s := { s with q3 := (m.a.y + m.b.x) / S'2 }
    s := { s with q4 := (m.a.z + m.c.x) / S'2 }
  else if m.b.y > m.c.z then
    let S'3 : Binary32 := Binary32.sqrt ((Binary32.ofBits 0x3f800000 /- 1 -/) + m.b.y - m.a.x - m.c.z) * (Binary32.ofBits 0x40000000 /- 2.0f -/)
    s := { s with q1 := (m.a.z - m.c.x) / S'3 }
    s := { s with q2 := (m.a.y + m.b.x) / S'3 }
    s := { s with q3 := (Binary32.ofBits 0x3e800000 /- 0.25f -/) * S'3 }
    s := { s with q4 := (m.b.z + m.c.y) / S'3 }
  else
    let S'4 : Binary32 := Binary32.sqrt ((Binary32.ofBits 0x3f800000 /- 1 -/) + m.c.z - m.a.x - m.b.y) * (Binary32.ofBits 0x40000000 /- 2.0f -/)
    s := { s with q1 := (m.b.x - m.a.y) / S'4 }
    s := { s with q2 := (m.a.z + m.c.x) / S'4 }
    s := { s with q3 := (m.b.z + m.c.y) / S'4 }
    s := { s with q4 := (Binary32.ofBits 0x3e800000 /- 0.25f -/) * S'4 }
  return s

end Quaternion

namespace Vector3f

/-- C++ `Vector3<float> Vector3<float>::operator-() const`, `AP_Math/vector3.cpp:407-410`. -/
def op_sub_void (s : State) : Vector3f.State := Id.run do
  return Vector3f.init_float3 (-s.x) (-s.y) (-s.z)

end Vector3f

namespace QuaternionT_double

/-- C++ `bool QuaternionT<double>::is_nan() const`, `AP_Math/quaternion.h:54-57`. -/
def is_nan (s : State) : Bool := Id.run do
  return Binary64.isNaN s.q1 || Binary64.isNaN s.q2 || Binary64.isNaN s.q3 || Binary64.isNaN s.q4

end QuaternionT_double

namespace Vector3p

/-- C++ `bool Vector3<double>::is_nan() const`, `AP_Math/vector3.cpp:364-367`. -/
def is_nan (s : State) : Bool := Id.run do
  return Binary64.isNaN s.x || Binary64.isNaN s.y || Binary64.isNaN s.z

end Vector3p

namespace QuaternionT_double

/-- C++ `double QuaternionT<double>::get_euler_roll() const`, `AP_Math/quaternion.cpp:587-590`. -/
def get_euler_roll (s : State) : Binary64 := Id.run do
  return (Musl.atan2.atan2 ((Binary64.ofBits 0x4000000000000000 /- (double)2 -/) * (s.q1 * s.q2 + s.q3 * s.q4)) ((Binary64.ofBits 0x3ff0000000000000 /- (double)1 -/) - (Binary64.ofBits 0x4000000000000000 /- (double)2 -/) * (s.q2 * s.q2 + s.q3 * s.q3)))

end QuaternionT_double

/-- C++ `float safe_asin(const double v)`, `AP_Math/AP_Math.cpp:50-63`. -/
def safe_asin_double (v : Binary64) : Binary32 := Id.run do
  let f : Binary32 := Binary64.toBinary32 v
  if Binary32.isNaN f then
    return (Binary32.ofBits 0x00000000 /- 0.0f -/)
  if f ≥ (Binary32.ofBits 0x3f800000 /- 1.0f -/) then
    return (Binary32.ofBits 0x3fc90fdb /- (float)884279719003555/562949953421312 -/)
  if f ≤ -(Binary32.ofBits 0x3f800000 /- 1.0f -/) then
    return (Binary32.ofBits 0xbfc90fdb /- (float)-884279719003555/562949953421312 -/)
  return Musl.asinf.asinf f

namespace QuaternionT_double

/-- C++ `double QuaternionT<double>::get_euler_pitch() const`, `AP_Math/quaternion.cpp:594-597`. -/
def get_euler_pitch (s : State) : Binary64 := Id.run do
  return Binary32.toBinary64 (Estimator_lib.safe_asin_double ((Binary64.ofBits 0x4000000000000000 /- 2.0f -/) * (s.q1 * s.q3 - s.q4 * s.q2)))

/-- C++ `double QuaternionT<double>::get_euler_yaw() const`, `AP_Math/quaternion.cpp:601-604`. -/
def get_euler_yaw (s : State) : Binary64 := Id.run do
  return Musl.atan2.atan2 ((Binary64.ofBits 0x4000000000000000 /- (double)2 -/) * (s.q1 * s.q4 + s.q2 * s.q3)) ((Binary64.ofBits 0x3ff0000000000000 /- (double)1 -/) - (Binary64.ofBits 0x4000000000000000 /- (double)2 -/) * (s.q3 * s.q3 + s.q4 * s.q4))

/-- C++ `void QuaternionT<double>::to_euler(double & roll, double & pitch, double & yaw) const`, `AP_Math/quaternion.cpp:608-613`. -/
def to_euler_double3 (s : State) (roll : Binary64) (pitch : Binary64) (yaw : Binary64) : Binary64 × Binary64 × Binary64 := Id.run do
  let mut roll := roll
  let mut pitch := pitch
  let mut yaw := yaw
  roll := get_euler_roll s
  pitch := get_euler_pitch s
  yaw := get_euler_yaw s
  return (roll, pitch, yaw)

end QuaternionT_double

/-- C++ `auto MIN(const unsigned short & one, const unsigned short & two)`, `AP_Math/AP_Math.h:300-303`. -/
def MIN_uint16_t2 (one two : UInt16) : UInt16 := Id.run do
  return if UInt32.toInt32 (UInt16.toUInt32 one) < UInt32.toInt32 (UInt16.toUInt32 two) then one else two

/-- C++ `bool is_positive(const double fVal1)`, `AP_Math/AP_Math.h:85-87`. -/
def is_positive_double (fVal1 : Binary64) : Bool := Id.run do
  return (decide (fVal1 ≥ (Binary64.ofBits 0x3e80000000000000 /- (double)1/8388608 -/)))

namespace Vector3p

/-- C++ `double Vector3<double>::operator*(const Vector3<double> & v) const`, `AP_Math/vector3.cpp:318-321`. -/
def op_mul_Vector3p (s : State) (v : Vector3p.State) : Binary64 := Id.run do
  return s.x * v.x + s.y * v.y + s.z * v.z

/-- C++ `double Vector3<double>::length_squared() const`, `AP_Math/vector3.h:211-214`. -/
def length_squared (s : State) : Binary64 := Id.run do
  return (op_mul_Vector3p s s)

/-- C++ `Vector3<double> Vector3<double>::operator-() const`, `AP_Math/vector3.cpp:407-410`. -/
def op_sub_void (s : State) : Vector3p.State := Id.run do
  return Vector3p.init_double3 (-s.x) (-s.y) (-s.z)

end Vector3p

namespace Vector2p

/-- C++ `double Vector2<double>::length_squared() const`, `AP_Math/vector2.cpp:24-27`. -/
def length_squared (s : State) : Binary64 := Id.run do
  return (s.x * s.x + s.y * s.y)

end Vector2p

namespace Matrix3_double

/-- C++ `Vector3<double> Matrix3<double>::to_euler312() const`, `AP_Math/matrix3.cpp:81-91`. -/
def to_euler312 (s : State) : Vector3p.State := Id.run do
  return Vector3p.init_double3 (Binary32.toBinary64 (Estimator_lib.safe_asin_double s.c.y)) (Musl.atan2.atan2 (-s.c.x) s.c.z) (Musl.atan2.atan2 (-s.a.y) s.b.y)

end Matrix3_double

namespace QuaternionT_double

/-- C++ `Vector3<double> QuaternionT<double>::to_vector312() const`, `AP_Math/quaternion.cpp:625-630`. -/
def to_vector312 (s : State) : Vector3p.State := Id.run do
  let mut m : Matrix3_double.State := Matrix3_double.init_void
  m := rotation_matrix_Matrix3_double s m
  return Matrix3_double.to_euler312 m

end QuaternionT_double

namespace Matrix3_double

/-- C++ `void Matrix3<double>::from_euler312(double roll, double pitch, double yaw)`, `AP_Math/matrix3.cpp:97-115`. -/
def from_euler312 (s : State) (roll : Binary64) (pitch : Binary64) (yaw : Binary64) : State := Id.run do
  let mut s := s
  let c3 : Binary64 := Musl.cos.cos pitch
  let s3 : Binary64 := Musl.sin.sin pitch
  let s2 : Binary64 := Musl.sin.sin roll
  let c2 : Binary64 := Musl.cos.cos roll
  let s1 : Binary64 := Musl.sin.sin yaw
  let c1 : Binary64 := Musl.cos.cos yaw
  s := { s with a.x := c1 * c3 - s1 * s2 * s3 }
  s := { s with b.y := c1 * c2 }
  s := { s with c.z := c3 * c2 }
  s := { s with a.y := -c2 * s1 }
  s := { s with a.z := s3 * c1 + c3 * s2 * s1 }
  s := { s with b.x := c3 * s1 + s3 * s2 * c1 }
  s := { s with b.z := s1 * s3 - s2 * c1 * c3 }
  s := { s with c.x := -s3 * c2 }
  s := { s with c.y := s2 }
  return s

end Matrix3_double

namespace QuaternionT_double

/-- C++ `void QuaternionT<double>::from_rotation_matrix(const Matrix3<double> & m)`, `AP_Math/quaternion.cpp:86-129`. -/
def from_rotation_matrix (s : State) (m : Matrix3_double.State) : State := Id.run do
  let mut s := s
  let tr : Binary64 := m.a.x + m.b.y + m.c.z
  if tr > (Binary64.ofBits 0x0000000000000000 /- 0 -/) then
    let S : Binary64 := Binary64.sqrt (tr + (Binary64.ofBits 0x3ff0000000000000 /- (double)1 -/)) * (Binary64.ofBits 0x4000000000000000 /- 2 -/)
    s := { s with q1 := (Binary64.ofBits 0x3fd0000000000000 /- 0.25f -/) * S }
    s := { s with q2 := (m.c.y - m.b.z) / S }
    s := { s with q3 := (m.a.z - m.c.x) / S }
    s := { s with q4 := (m.b.x - m.a.y) / S }
  else if (decide (m.a.x > m.b.y)) && (decide (m.a.x > m.c.z)) then
    let S'2 : Binary64 := Binary64.sqrt ((Binary64.ofBits 0x3ff0000000000000 /- (double)1 -/) + m.a.x - m.b.y - m.c.z) * (Binary64.ofBits 0x4000000000000000 /- 2.0f -/)
    s := { s with q1 := (m.c.y - m.b.z) / S'2 }
    s := { s with q2 := (Binary64.ofBits 0x3fd0000000000000 /- 0.25f -/) * S'2 }
    s := { s with q3 := (m.a.y + m.b.x) / S'2 }
    s := { s with q4 := (m.a.z + m.c.x) / S'2 }
  else if m.b.y > m.c.z then
    let S'3 : Binary64 := Binary64.sqrt ((Binary64.ofBits 0x3ff0000000000000 /- (double)1 -/) + m.b.y - m.a.x - m.c.z) * (Binary64.ofBits 0x4000000000000000 /- 2.0f -/)
    s := { s with q1 := (m.a.z - m.c.x) / S'3 }
    s := { s with q2 := (m.a.y + m.b.x) / S'3 }
    s := { s with q3 := (Binary64.ofBits 0x3fd0000000000000 /- 0.25f -/) * S'3 }
    s := { s with q4 := (m.b.z + m.c.y) / S'3 }
  else
    let S'4 : Binary64 := Binary64.sqrt ((Binary64.ofBits 0x3ff0000000000000 /- (double)1 -/) + m.c.z - m.a.x - m.b.y) * (Binary64.ofBits 0x4000000000000000 /- 2.0f -/)
    s := { s with q1 := (m.b.x - m.a.y) / S'4 }
    s := { s with q2 := (m.a.z + m.c.x) / S'4 }
    s := { s with q3 := (m.b.z + m.c.y) / S'4 }
    s := { s with q4 := (Binary64.ofBits 0x3fd0000000000000 /- 0.25f -/) * S'4 }
  return s

/-- C++ `void QuaternionT<double>::from_vector312(double roll, double pitch, double yaw)`, `AP_Math/quaternion.cpp:444-450`. -/
def from_vector312 (s : State) (roll : Binary64) (pitch : Binary64) (yaw : Binary64) : State := Id.run do
  let mut s := s
  let mut m : Matrix3_double.State := Matrix3_double.init_void
  m := Matrix3_double.from_euler312 m roll pitch yaw
  s := from_rotation_matrix s m
  return s

/-- C++ `QuaternionT<double> QuaternionT<double>::operator/(const QuaternionT<double> & v) const`, `AP_Math/quaternion.cpp:793-816`. -/
def op_div (s : State) (v : QuaternionT_double.State) : QuaternionT_double.State := Id.run do
  let mut ret : QuaternionT_double.State := QuaternionT_double.init_void
  if is_zero s then
    pure ()  -- C++ `AP_InternalError::error(...)`: left out (--drop)
  let rquat0 : Binary64 := v.q1
  let rquat1 : Binary64 := v.q2
  let rquat2 : Binary64 := v.q3
  let rquat3 : Binary64 := v.q4
  ret := { ret with q1 := (rquat0 * s.q1 + rquat1 * s.q2 + rquat2 * s.q3 + rquat3 * s.q4) }
  ret := { ret with q2 := (rquat0 * s.q2 - rquat1 * s.q1 - rquat2 * s.q4 + rquat3 * s.q3) }
  ret := { ret with q3 := (rquat0 * s.q3 + rquat1 * s.q4 - rquat2 * s.q1 - rquat3 * s.q2) }
  ret := { ret with q4 := (rquat0 * s.q4 - rquat1 * s.q3 + rquat2 * s.q2 - rquat3 * s.q1) }
  return ret

/-- C++ `QuaternionT<double> QuaternionT<double>::operator*(const QuaternionT<double> & v) const`, `AP_Math/quaternion.cpp:712-731`. -/
def op_mul_QuaternionT_double (s : State) (v : QuaternionT_double.State) : QuaternionT_double.State := Id.run do
  let mut ret : QuaternionT_double.State := QuaternionT_double.init_void
  let w2 : Binary64 := v.q1
  let x2 : Binary64 := v.q2
  let y2 : Binary64 := v.q3
  let z2 : Binary64 := v.q4
  ret := { ret with q1 := s.q1 * w2 - s.q2 * x2 - s.q3 * y2 - s.q4 * z2 }
  ret := { ret with q2 := s.q1 * x2 + s.q2 * w2 + s.q3 * z2 - s.q4 * y2 }
  ret := { ret with q3 := s.q1 * y2 - s.q2 * z2 + s.q3 * w2 + s.q4 * x2 }
  ret := { ret with q4 := s.q1 * z2 + s.q2 * y2 - s.q3 * x2 + s.q4 * w2 }
  return ret

end QuaternionT_double

namespace Matrix3_double

/-- C++ `void Matrix3<double>::from_euler(double roll, double pitch, double yaw)`, `AP_Math/matrix3.cpp:26-44`. -/
def from_euler (s : State) (roll : Binary64) (pitch : Binary64) (yaw : Binary64) : State := Id.run do
  let mut s := s
  let cp : Binary64 := Musl.cos.cos pitch
  let sp : Binary64 := Musl.sin.sin pitch
  let sr : Binary64 := Musl.sin.sin roll
  let cr : Binary64 := Musl.cos.cos roll
  let sy : Binary64 := Musl.sin.sin yaw
  let cy : Binary64 := Musl.cos.cos yaw
  s := { s with a.x := cp * cy }
  s := { s with a.y := (sr * sp * cy) - (cr * sy) }
  s := { s with a.z := (cr * sp * cy) + (sr * sy) }
  s := { s with b.x := cp * sy }
  s := { s with b.y := (sr * sp * sy) + (cr * cy) }
  s := { s with b.z := (cr * sp * sy) - (sr * cy) }
  s := { s with c.x := -sp }
  s := { s with c.y := sr * cp }
  s := { s with c.z := cr * cp }
  return s

end Matrix3_double

namespace QuaternionT_double

/-- C++ `void QuaternionT<double>::to_euler(Vector3d & rpy) const`, `AP_Math/quaternion.h:129-131`. -/
def to_euler_Vector3p (s : State) (rpy : Vector3p.State) : Vector3p.State := Id.run do
  let mut rpy := rpy
  let (t'1, t'2, t'3) := to_euler_double3 s rpy.x rpy.y rpy.z
  rpy := { rpy with x := t'1 }
  rpy := { rpy with y := t'2 }
  rpy := { rpy with z := t'3 }
  return rpy

end QuaternionT_double

namespace Matrix3_double

/-- C++ `void Matrix3<double>::to_euler(double * roll, double * pitch, double * yaw) const`, `AP_Math/matrix3.cpp:49-60`. -/
def to_euler (s : State) (roll'given : Bool) (roll : Binary64) (pitch'given : Bool) (pitch : Binary64) (yaw'given : Bool) (yaw : Binary64) : Binary64 × Binary64 × Binary64 := Id.run do
  let mut roll := roll
  let mut pitch := pitch
  let mut yaw := yaw
  if pitch'given then
    pitch := Binary32.toBinary64 (-(Estimator_lib.safe_asin_double s.c.x))
  if roll'given then
    roll := Musl.atan2.atan2 s.c.y s.c.z
  if yaw'given then
    yaw := Musl.atan2.atan2 s.b.x s.a.x
  return (roll, pitch, yaw)

end Matrix3_double

/-- C++ `auto MAX(const float & one, const float & two)`, `AP_Math/AP_Math.h:307-310`. -/
def MAX_float2 (one two : Binary32) : Binary32 := Id.run do
  return if one > two then one else two

namespace Quaternion

/-- C++ `QuaternionT<float>::QuaternionT(const float _q1, const float _q2, const float _q3, const float _q4)`, `AP_Math/quaternion.h:42-45`. -/
def init_float4 (_q1 : Binary32) (_q2 : Binary32) (_q3 : Binary32) (_q4 : Binary32) : State := Id.run do
  let mut s : State := {}
  s := { s with q1 := _q1 }
  s := { s with q2 := _q2 }
  s := { s with q3 := _q3 }
  s := { s with q4 := _q4 }
  return s

end Quaternion

namespace QuaternionT_double

/-- C++ `QuaternionT<float> QuaternionT<double>::tofloat() const`, `AP_Math/quaternion.h:198-200`. -/
def tofloat (s : State) : Quaternion.State := Id.run do
  return Quaternion.init_float4 (Binary64.toBinary32 s.q1) (Binary64.toBinary32 s.q2) (Binary64.toBinary32 s.q3) (Binary64.toBinary32 s.q4)

end QuaternionT_double

namespace QuaternionT_double

/-- C++ `void QuaternionT<double>::to_euler(float & roll, float & pitch, float & yaw) const`, `AP_Math/quaternion.cpp:616-621`. -/
def to_euler_float3 (s : State) (roll : Binary32) (pitch : Binary32) (yaw : Binary32) : Binary32 × Binary32 × Binary32 := Id.run do
  let mut roll := roll
  let mut pitch := pitch
  let mut yaw := yaw
  roll := Binary64.toBinary32 (get_euler_roll s)
  pitch := Binary64.toBinary32 (get_euler_pitch s)
  yaw := Binary64.toBinary32 (get_euler_yaw s)
  return (roll, pitch, yaw)

/-- C++ `void QuaternionT<double>::to_euler(Vector3f & rpy) const`, `AP_Math/quaternion.h:125-127`. -/
def to_euler_Vector3f (s : State) (rpy : Vector3f.State) : Vector3f.State := Id.run do
  let mut rpy := rpy
  let (t'1, t'2, t'3) := to_euler_float3 s rpy.x rpy.y rpy.z
  rpy := { rpy with x := t'1 }
  rpy := { rpy with y := t'2 }
  rpy := { rpy with z := t'3 }
  return rpy

end QuaternionT_double

namespace Vector2p

/-- C++ `Vector2<double> Vector2<double>::todouble() const`, `AP_Math/vector2.h:181-183`. -/
def todouble (s : State) : Vector2p.State := Id.run do
  return Vector2p.init_double2 s.x s.y

/-- C++ `Vector2<double> Vector2<double>::operator+(const Vector2<double> & v) const`, `AP_Math/vector2.cpp:121-124`. -/
def op_add (s : State) (v : Vector2p.State) : Vector2p.State := Id.run do
  return Vector2p.init_double2 (s.x + v.x) (s.y + v.y)

end Vector2p

namespace Vector2p

/-- C++ `Vector2<float> Vector2<double>::tofloat() const`, `AP_Math/vector2.h:178-180`. -/
def tofloat (s : State) : Vector2f.State := Id.run do
  return Vector2f.init_float2 (Binary64.toBinary32 s.x) (Binary64.toBinary32 s.y)

end Vector2p

namespace Matrix3f

/-- C++ `void Matrix3<float>::transpose()`, `AP_Math/matrix3.h:191-194`. -/
def transpose (s : State) : State := Id.run do
  let mut s := s
  s := transposed s
  return s

end Matrix3f

/-- C++ `bool check_lat(int32_t lat)`, `AP_Math/location.cpp:47-50`. -/
def check_lat_int32_t (lat : Int32) : Bool := Id.run do
  return decide (Int64.toBinary32 (if Int32.toInt64 lat < (0 : Int64) then -Int32.toInt64 lat else Int32.toInt64 lat) ≤ (Binary32.ofBits 0x42b40000 /- 90 -/) * (Binary32.ofBits 0x4b189680 /- 1e7 -/))

/-- C++ `bool check_lng(int32_t lng)`, `AP_Math/location.cpp:51-54`. -/
def check_lng_int32_t (lng : Int32) : Bool := Id.run do
  return decide (Int64.toBinary32 (if Int32.toInt64 lng < (0 : Int64) then -Int32.toInt64 lng else Int32.toInt64 lng) ≤ (Binary32.ofBits 0x43340000 /- 180 -/) * (Binary32.ofBits 0x4b189680 /- 1e7 -/))

namespace Quaternion

/-- C++ `void QuaternionT<float>::rotation_matrix(Matrix3f & m) const`, `AP_Math/quaternion.cpp:59-80`. -/
def rotation_matrix_Matrix3f (s : State) (m : Matrix3f.State) : Matrix3f.State := Id.run do
  let mut m := m
  let q3q3 : Binary32 := s.q3 * s.q3
  let q3q4 : Binary32 := s.q3 * s.q4
  let q2q2 : Binary32 := s.q2 * s.q2
  let q2q3 : Binary32 := s.q2 * s.q3
  let q2q4 : Binary32 := s.q2 * s.q4
  let q1q2 : Binary32 := s.q1 * s.q2
  let q1q3 : Binary32 := s.q1 * s.q3
  let q1q4 : Binary32 := s.q1 * s.q4
  let q4q4 : Binary32 := s.q4 * s.q4
  m := { m with a.x := (Binary32.ofBits 0x3f800000 /- 1.0f -/) - (Binary32.ofBits 0x40000000 /- 2.0f -/) * (q3q3 + q4q4) }
  m := { m with a.y := (Binary32.ofBits 0x40000000 /- 2.0f -/) * (q2q3 - q1q4) }
  m := { m with a.z := (Binary32.ofBits 0x40000000 /- 2.0f -/) * (q2q4 + q1q3) }
  m := { m with b.x := (Binary32.ofBits 0x40000000 /- 2.0f -/) * (q2q3 + q1q4) }
  m := { m with b.y := (Binary32.ofBits 0x3f800000 /- 1.0f -/) - (Binary32.ofBits 0x40000000 /- 2.0f -/) * (q2q2 + q4q4) }
  m := { m with b.z := (Binary32.ofBits 0x40000000 /- 2.0f -/) * (q3q4 - q1q2) }
  m := { m with c.x := (Binary32.ofBits 0x40000000 /- 2.0f -/) * (q2q4 - q1q3) }
  m := { m with c.y := (Binary32.ofBits 0x40000000 /- 2.0f -/) * (q3q4 + q1q2) }
  m := { m with c.z := (Binary32.ofBits 0x3f800000 /- 1.0f -/) - (Binary32.ofBits 0x40000000 /- 2.0f -/) * (q2q2 + q3q3) }
  return m

/-- C++ `float QuaternionT<float>::roll_pitch_difference(const QuaternionT<float> & v) const`, `AP_Math/quaternion.cpp:827-843`. -/
def roll_pitch_difference (s : State) (v : Quaternion.State) : Binary32 := Id.run do
  let mut m : Matrix3f.State := Matrix3f.init_void
  let mut vm : Matrix3f.State := Matrix3f.init_void
  m := rotation_matrix_Matrix3f s m
  vm := Quaternion.rotation_matrix_Matrix3f v vm
  let z_unit_vec : Vector3f.State := Vector3f.init_float3 (Binary32.ofBits 0x00000000 /- 0 -/) (Binary32.ofBits 0x00000000 /- 0 -/) (Binary32.ofBits 0x3f800000 /- 1 -/)
  let z_unit_m : Vector3f.State := Matrix3f.mul_transpose m z_unit_vec
  let z_unit_vm : Vector3f.State := Matrix3f.mul_transpose vm z_unit_vec
  let vec_diff : Vector3f.State := Vector3f.op_sub_Vector3f z_unit_vm z_unit_m
  let vec_len_div2 : Binary32 := Estimator_lib.constrain_value_line_float (Binary64.toBinary32 (Binary32.toBinary64 (Vector3f.length vec_diff) * (Binary64.ofBits 0x3fe0000000000000 /- 0.5 -/))) (Binary32.ofBits 0x00000000 /- (float)0 -/) (Binary32.ofBits 0x3f800000 /- (float)1 -/) (Int32.toUInt32 (839 : Int32))
  return Binary64.toBinary32 ((Binary64.ofBits 0x4000000000000000 /- 2.0 -/) * Binary32.toBinary64 (Musl.asinf.asinf vec_len_div2))

/-- C++ `QuaternionT<float> QuaternionT<float>::inverse() const`, `AP_Math/quaternion.cpp:647-650`. -/
def inverse (s : State) : Quaternion.State := Id.run do
  return Quaternion.init_float4 s.q1 (-s.q2) (-s.q3) (-s.q4)

/-- C++ `QuaternionT<float> QuaternionT<float>::operator*(const QuaternionT<float> & v) const`, `AP_Math/quaternion.cpp:712-731`. -/
def op_mul_Quaternion (s : State) (v : Quaternion.State) : Quaternion.State := Id.run do
  let mut ret : Quaternion.State := Quaternion.init_void
  let w2 : Binary32 := v.q1
  let x2 : Binary32 := v.q2
  let y2 : Binary32 := v.q3
  let z2 : Binary32 := v.q4
  ret := { ret with q1 := s.q1 * w2 - s.q2 * x2 - s.q3 * y2 - s.q4 * z2 }
  ret := { ret with q2 := s.q1 * x2 + s.q2 * w2 + s.q3 * z2 - s.q4 * y2 }
  ret := { ret with q3 := s.q1 * y2 - s.q2 * z2 + s.q3 * w2 + s.q4 * x2 }
  ret := { ret with q4 := s.q1 * z2 + s.q2 * y2 - s.q3 * x2 + s.q4 * w2 }
  return ret

/-- C++ `QuaternionT<float> QuaternionT<float>::angular_difference(const QuaternionT<float> & v) const`, `AP_Math/quaternion.cpp:820-823`. -/
def angular_difference (s : State) (v : Quaternion.State) : Quaternion.State := Id.run do
  return Quaternion.op_mul_Quaternion (Quaternion.inverse v) s

/-- C++ `void QuaternionT<float>::to_axis_angle(Vector3<float> & v) const`, `AP_Math/quaternion.cpp:497-505`. -/
def to_axis_angle (s : State) (v : Vector3f.State) : Vector3f.State := Id.run do
  let mut v := v
  let l : Binary32 := Binary32.sqrt (Estimator_lib.sq_float s.q2 + Estimator_lib.sq_float s.q3 + Estimator_lib.sq_float s.q4)
  v := Vector3f.init_float3 s.q2 s.q3 s.q4
  if !(Estimator_lib.is_zero_float l) then
    let (t'1, _) := Vector3f.op_div_assign v l
    v := t'1
    let (t'3, _) := Vector3f.op_mul_assign_float v (Estimator_lib.wrap_PI_float ((Binary32.ofBits 0x40000000 /- 2.0f -/) * Musl.atan2f.atan2f l s.q1))
    v := t'3
  return v

end Quaternion

namespace Matrix3f

/-- C++ `void Matrix3<float>::zero()`, `AP_Math/matrix3.h:222-224`. -/
def zero (s : State) : State := Id.run do
  let mut s := s
  s := { a := { x := (Binary32.ofBits 0x00000000 /- 0.0 -/), y := (Binary32.ofBits 0x00000000 /- 0.0 -/), z := (Binary32.ofBits 0x00000000 /- 0.0 -/) }, b := { x := (Binary32.ofBits 0x00000000 /- 0.0 -/), y := (Binary32.ofBits 0x00000000 /- 0.0 -/), z := (Binary32.ofBits 0x00000000 /- 0.0 -/) }, c := { x := (Binary32.ofBits 0x00000000 /- 0.0 -/), y := (Binary32.ofBits 0x00000000 /- 0.0 -/), z := (Binary32.ofBits 0x00000000 /- 0.0 -/) } }
  return s

/-- C++ `void Matrix3<float>::identity()`, `AP_Math/matrix3.h:227-230`. -/
def identity (s : State) : State := Id.run do
  let mut s := s
  s := zero s
  s := { s with c.z := (Binary32.ofBits 0x3f800000 /- 1 -/) }
  s := { s with b.y := s.c.z }
  s := { s with a.x := s.b.y }
  return s

end Matrix3f

/-- C++ `auto MIN(const int & one, const int & two)`, `AP_Math/AP_Math.h:300-303`. -/
def MIN_int32_t2 (one two : Int32) : Int32 := Id.run do
  return if one < two then one else two

/-- C++ `float wrap_360_cd(const float angle)`, `AP_Math/AP_Math.cpp:213-220`. -/
def wrap_360_cd_float (angle : Binary32) : Binary32 := Id.run do
  let mut res : Binary32 := Musl.fmodf.fmodf angle (Binary32.ofBits 0x470ca000 /- 36000.0f -/)
  if res < (Binary32.ofBits 0x00000000 /- 0 -/) then
    res := res + (Binary32.ofBits 0x470ca000 /- 36000.0f -/)
  return res

/-- C++ `auto MIN(const unsigned char & one, const int & two)`, `AP_Math/AP_Math.h:300-303`. -/
def MIN_uint8_t_int32_t (one : UInt8) (two : Int32) : Int32 := Id.run do
  return if UInt32.toInt32 (UInt8.toUInt32 one) < two then UInt32.toInt32 (UInt8.toUInt32 one) else two

namespace Vector3f

/-- C++ `bool Vector3<float>::operator!=(const Vector3<float> & v) const`, `AP_Math/vector3.cpp:419-422`. -/
def op_ne (s : State) (v : Vector3f.State) : Bool := Id.run do
  return (!(Estimator_lib.is_equal_float2 s.x v.x) || !(Estimator_lib.is_equal_float2 s.y v.y) || !(Estimator_lib.is_equal_float2 s.z v.z))

end Vector3f

end Estimator_lib
