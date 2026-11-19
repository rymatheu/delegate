import ArduLean.Runtime.GcsPort

/-!
ArduPilot `libraries/AP_Math`, part 1 of 2. Sources: `libraries/AP_Math/SCurve.cpp`, `libraries/AP_Math/control.cpp`, `libraries/AP_Math/SplineCurve.cpp`, `libraries/AP_Math/AP_Math.h`, `libraries/AP_Math/vector2.cpp`, `libraries/AP_Math/quaternion.cpp`, `libraries/AP_Math/vector3.cpp`, `libraries/AP_Math/vector3.h` and 9 more.

Items of `lean/Vehicle_lib.lean` (the vehicle translation), unchanged; placed by `tools/split_modules.py` (`ArduLean/Vehicle/INDEX.md`).
-/

open FloatLib.Floats (Binary32 Binary64)

set_option linter.unusedVariables false
set_option linter.unreachableTactic false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false

namespace Vehicle_lib

/-- C++ `MIN : auto (const unsigned long &, const unsigned int &) -> decltype(one < two ? one : two)`, `AP_Math.h:300-303`. -/
def MIN'unsigned_long_unsigned_int (one : UInt64) (two : UInt64) : PMem.M UInt64 := do
  let t'1 ← PMem.ldU64 one
  let t'2 ← PMem.ldU32 two
  let mut c'3 : UInt64 := default
  if (decide (t'1 < (UInt32.toUInt64 (t'2)))) then
    let t'4 ← PMem.ldU64 one
    c'3 := t'4
  else
    let t'5 ← PMem.ldU32 two
    c'3 := UInt32.toUInt64 (t'5)
  return c'3

/-- C++ `Vector3<float>::Vector3 : void (const float, const float, const float)`, `AP_Common.h:85-88`. -/
def Vector3'float.Vector3 (this : UInt64) (x0 : Binary32) (y0 : Binary32) (z0 : Binary32) : PMem.M Unit := do
  let mut x0 := x0
  let mut y0 := y0
  let mut z0 := z0
  PMem.stF32 (this + 0) x0
  PMem.stF32 (this + 4) y0
  PMem.stF32 (this + 8) z0
  return ()

/-- `constrain_value_line'float` as a pure function of its arguments (it reads and writes no memory). -/
def constrain_value_line'float.pure' (amt : Binary32) (low : Binary32) (high : Binary32) (line : UInt32) : Id Binary32 := do
  let mut amt := amt
  let mut low := low
  let mut high := high
  let mut line := line
  if (Binary32.isNaN amt) then
    return ((low + high) / (Int32.toBinary32 ((2 : Int32))))
  if (decide (amt < low)) then
    return low
  if (decide (amt > high)) then
    return high
  return amt

/-- C++ `constrain_value_line : float (const float, const float, const float, uint32_t)`, `AP_Math.cpp:283-304`. -/
def constrain_value_line'float (amt : Binary32) (low : Binary32) (high : Binary32) (line : UInt32) : PMem.M Binary32 :=
  pure (_root_.Vehicle_lib.constrain_value_line'float.pure' amt low high line)

/-- C++ `MIN : auto (const unsigned long &, const unsigned long &) -> decltype(one < two ? one : two)`, `AP_Math.h:300-303`. -/
def MIN'unsigned_long_unsigned_long (one : UInt64) (two : UInt64) : PMem.M UInt64 := do
  let t'1 ← PMem.ldU64 one
  let t'2 ← PMem.ldU64 two
  let mut c'3 : UInt64 := 0
  if (decide (t'1 < t'2)) then
    c'3 := one
  else
    c'3 := two
  return c'3

/-- C++ `MIN : auto (const unsigned int &, const unsigned int &) -> decltype(one < two ? one : two)`, `AP_Math.h:300-303`. -/
def MIN'unsigned_int_unsigned_int (one : UInt64) (two : UInt64) : PMem.M UInt64 := do
  let t'1 ← PMem.ldU32 one
  let t'2 ← PMem.ldU32 two
  let mut c'3 : UInt64 := 0
  if (decide (t'1 < t'2)) then
    c'3 := one
  else
    c'3 := two
  return c'3

/-- `is_equal'float_float` as a pure function of its arguments (it reads and writes no memory). -/
def is_equal'float_float.pure' (v_1 : Binary32) (v_2 : Binary32) : Id Bool := do
  let mut v_1 := v_1
  let mut v_2 := v_2
  if false then
    return (decide ((Binary32.toBinary64 ((Binary32.abs (v_1 - v_2)))) < (Binary64.ofBits 0x3cb0000000000000)))
  return (decide ((Binary32.abs (v_1 - v_2)) < (Binary32.ofBits 0x34000000)))

/-- C++ `is_equal : typename std::enable_if<std::is_floating_point<typename std::common_type<float, float>::type>::value, bool>::type (const float, const float)`, `AP_Math.cpp:25-41`. -/
def is_equal'float_float (v_1 : Binary32) (v_2 : Binary32) : PMem.M Bool :=
  pure (_root_.Vehicle_lib.is_equal'float_float.pure' v_1 v_2)

/-- C++ `Vector3<float>::Vector3 : void ()`, `vector3.h:79-82`. -/
def Vector3'float.Vector3'2 (this : UInt64) : PMem.M Unit := do
  PMem.stF32 (this + 0) (Int32.toBinary32 ((0 : Int32)))
  PMem.stF32 (this + 4) (Int32.toBinary32 ((0 : Int32)))
  PMem.stF32 (this + 8) (Int32.toBinary32 ((0 : Int32)))
  return ()

/-- C++ `QuaternionT<float>::QuaternionT : void ()`, `quaternion.h:35-39`. -/
def QuaternionT'float.QuaternionT (this : UInt64) : PMem.M Unit := do
  let t'1 := Int32.toBinary32 ((1 : Int32))
  PMem.stF32 this t'1
  let t'2 := Int32.toBinary32 ((0 : Int32))
  PMem.stF32 (this + 12) t'2
  let t'3 ← PMem.ldF32 (this + 12)
  PMem.stF32 (this + 8) t'3
  let t'4 ← PMem.ldF32 (this + 8)
  PMem.stF32 (this + 4) t'4
  return ()

/-- C++ `Vector3<float>::zero : void ()`, `vector3.h:229-232`. -/
def Vector3'float.zero (this : UInt64) : PMem.M Unit := do
  let t'1 := Int32.toBinary32 ((0 : Int32))
  PMem.stF32 (this + 8) t'1
  let t'2 ← PMem.ldF32 (this + 8)
  PMem.stF32 (this + 4) t'2
  let t'3 ← PMem.ldF32 (this + 4)
  PMem.stF32 this t'3
  return ()

/-- `is_zero` as a pure function of its arguments (it reads and writes no memory). -/
def is_zero.pure' (x : Binary32) : Id Bool := do
  let mut x := x
  return (decide ((Binary32.abs x) < (Binary32.ofBits 0x34000000 /- 11920929/100000000000000 -/)))

/-- C++ `is_zero : bool (const float)`, `ftype.h:61-63`. -/
def is_zero (x : Binary32) : PMem.M Bool :=
  pure (_root_.Vehicle_lib.is_zero.pure' x)

/-- C++ `MIN : auto (const float &, const float &) -> decltype(one < two ? one : two)`, `AP_Math.h:300-303`. -/
def MIN'float_float (one : UInt64) (two : UInt64) : PMem.M UInt64 := do
  let t'1 ← PMem.ldF32 one
  let t'2 ← PMem.ldF32 two
  let mut c'3 : UInt64 := 0
  if (decide (t'1 < t'2)) then
    c'3 := one
  else
    c'3 := two
  return c'3

/-- `is_positive'float` as a pure function of its arguments (it reads and writes no memory). -/
def is_positive'float.pure' (fVal1 : Binary32) : Id Bool := do
  let mut fVal1 := fVal1
  return (decide (fVal1 ≥ (Binary32.ofBits 0x34000000 /- 11920929/100000000000000 -/)))

/-- C++ `is_positive : bool (const float)`, `<built-in>:65-69`. -/
def is_positive'float (fVal1 : Binary32) : PMem.M Bool :=
  pure (_root_.Vehicle_lib.is_positive'float.pure' fVal1)

/-- `is_negative'float` as a pure function of its arguments (it reads and writes no memory). -/
def is_negative'float.pure' (fVal1 : Binary32) : Id Bool := do
  let mut fVal1 := fVal1
  return (decide ((Binary32.toBinary64 (fVal1)) ≤ ((-(Binary64.ofBits 0x3ff0000000000000 /- 1 -/)) * (Binary32.toBinary64 ((Binary32.ofBits 0x34000000 /- 11920929/100000000000000 -/))))))

/-- C++ `is_negative : bool (const float)`, `<built-in>:76-80`. -/
def is_negative'float (fVal1 : Binary32) : PMem.M Bool :=
  pure (_root_.Vehicle_lib.is_negative'float.pure' fVal1)

/-- `sq` as a pure function of its arguments (it reads and writes no memory). -/
def sq.pure' (val : Binary32) : Id Binary32 := do
  let mut val := val
  return (val * val)

/-- C++ `sq : float (const float)`, `AP_Math.h:266-269`. -/
def sq (val : Binary32) : PMem.M Binary32 :=
  pure (_root_.Vehicle_lib.sq.pure' val)

/-- `inv_sqrt_controller` as a pure function of its arguments (it reads and writes no memory). -/
def inv_sqrt_controller.pure' (output : Binary32) (p : Binary32) (D_max : Binary32) : Id Binary32 := do
  let mut output := output
  let mut p := p
  let mut D_max := D_max
  let t'1 ← _root_.Vehicle_lib.is_positive'float.pure' D_max
  let mut sc'3 := t'1
  if sc'3 then
    let t'2 ← _root_.Vehicle_lib.is_zero.pure' p
    sc'3 := t'2
  if sc'3 then
    return ((output * output) / ((Binary64.toBinary32 ((Binary64.ofBits 0x4000000000000000 /- 2 -/))) * D_max))
  let t'4 ← _root_.Vehicle_lib.is_negative'float.pure' D_max
  let mut sc'6 := t'4
  if !sc'6 then
    let t'5 ← _root_.Vehicle_lib.is_zero.pure' D_max
    sc'6 := t'5
  let mut sc'8 := sc'6
  if sc'8 then
    let t'7 ← _root_.Vehicle_lib.is_zero.pure' p
    sc'8 := !t'7
  if sc'8 then
    return (output / p)
  let t'9 ← _root_.Vehicle_lib.is_negative'float.pure' D_max
  let mut sc'11 := t'9
  if !sc'11 then
    let t'10 ← _root_.Vehicle_lib.is_zero.pure' D_max
    sc'11 := t'10
  let mut sc'13 := sc'11
  if sc'13 then
    let t'12 ← _root_.Vehicle_lib.is_zero.pure' p
    sc'13 := t'12
  if sc'13 then
    return Binary64.toBinary32 ((Binary64.ofBits 0x0000000000000000 /- 0 -/))
  let mut linear_velocity : Binary32 := (D_max / p)
  if (decide ((Binary32.abs output) < linear_velocity)) then
    return (output / p)
  let t'14 ← _root_.Vehicle_lib.sq.pure' p
  let mut linear_dist : Binary32 := (D_max / t'14)
  let t'15 ← _root_.Vehicle_lib.sq.pure' output
  let mut stopping_dist : Binary32 := ((linear_dist * (Binary32.ofBits 0x3f000000 /- 1/2 -/)) + (t'15 / ((Binary64.toBinary32 ((Binary64.ofBits 0x4000000000000000 /- 2 -/))) * D_max)))
  let t'16 ← _root_.Vehicle_lib.is_positive'float.pure' output
  let mut c'17 : Binary32 := default
  if t'16 then
    c'17 := stopping_dist
  else
    c'17 := -stopping_dist
  return c'17

/-- C++ `inv_sqrt_controller : float (float, float, float)`, `control.cpp:630-659`. -/
def inv_sqrt_controller (output : Binary32) (p : Binary32) (D_max : Binary32) : PMem.M Binary32 :=
  pure (_root_.Vehicle_lib.inv_sqrt_controller.pure' output p D_max)

/-- `radians` as a pure function of its arguments (it reads and writes no memory). -/
def radians.pure' (deg : Binary32) : Id Binary32 := do
  let mut deg := deg
  return (deg * ((Binary64.toBinary32 ((Binary64.ofBits 0x400921fb54442d18 /- 31415926535897931/10000000000000000 -/))) / (Binary32.ofBits 0x43340000 /- 180 -/)))

/-- C++ `radians : float (float)`, `AP_Math.h:232-235`. -/
def radians (deg : Binary32) : PMem.M Binary32 :=
  pure (_root_.Vehicle_lib.radians.pure' deg)

/-- `safe_sqrt'float` as a pure function of its arguments (it reads and writes no memory). -/
def safe_sqrt'float.pure' (v : Binary32) : Id Binary32 := do
  let mut v := v
  let mut val : Binary32 := v
  if (decide (val ≥ (Int32.toBinary32 ((0 : Int32))))) then
    return (Binary32.sqrt val)
  return Int32.toBinary32 ((0 : Int32))

/-- C++ `safe_sqrt : float (const float)`, `AP_Math.cpp:72-81`. -/
def safe_sqrt'float (v : Binary32) : PMem.M Binary32 :=
  pure (_root_.Vehicle_lib.safe_sqrt'float.pure' v)

/-- `Vector3'float.xy` as a pure function of its arguments (it reads and writes no memory). -/
def Vector3'float.xy.pure' (this : UInt64) : Id UInt64 := do
  return this

/-- C++ `Vector3<float>::xy : Vector2<float> &()`, `vector3.h:206-208`. -/
def Vector3'float.xy (this : UInt64) : PMem.M UInt64 :=
  pure (_root_.Vehicle_lib.Vector3'float.xy.pure' this)

/-- C++ `MAX : auto (const float &, const float &) -> decltype(one > two ? one : two)`, `AP_Math.h:307-310`. -/
def MAX'float_float (one : UInt64) (two : UInt64) : PMem.M UInt64 := do
  let t'1 ← PMem.ldF32 one
  let t'2 ← PMem.ldF32 two
  let mut c'3 : UInt64 := 0
  if (decide (t'1 > t'2)) then
    c'3 := one
  else
    c'3 := two
  return c'3

/-- `Vector3'double.xy` as a pure function of its arguments (it reads and writes no memory). -/
def Vector3'double.xy.pure' (this : UInt64) : Id UInt64 := do
  return this

/-- C++ `Vector3<double>::xy : Vector2<double> &()`, `vector3.h:206-208`. -/
def Vector3'double.xy (this : UInt64) : PMem.M UInt64 :=
  pure (_root_.Vehicle_lib.Vector3'double.xy.pure' this)

/-- C++ `Vector2<float>::zero : void ()`, `AP_Common.h:140-143`. -/
def Vector2'float.zero (this : UInt64) : PMem.M Unit := do
  let t'1 := Int32.toBinary32 ((0 : Int32))
  PMem.stF32 (this + 4) t'1
  let t'2 ← PMem.ldF32 (this + 4)
  PMem.stF32 this t'2
  return ()

/-- C++ `Vector2<double>::zero : void ()`, `AP_Common.h:140-143`. -/
def Vector2'double.zero (this : UInt64) : PMem.M Unit := do
  let t'1 := Int32.toBinary64 ((0 : Int32))
  PMem.stF64 (this + 8) t'1
  let t'2 ← PMem.ldF64 (this + 8)
  PMem.stF64 this t'2
  return ()

/-- C++ `Vector2<double>::Vector2 : void (Vector2<double> &&) noexcept`, `AP_Common.h:?-?`. -/
def Vector2'double.Vector2 (this : UInt64) (arg : UInt64) : PMem.M Unit := do
  let t'1 ← PMem.ldF64 arg
  PMem.stF64 (this + 0) t'1
  let t'2 ← PMem.ldF64 (arg + 8)
  PMem.stF64 (this + 8) t'2
  return ()

/-- C++ `Vector2<double>::Vector2 : void (const double, const double)`, `vector2.h:55-57`. -/
def Vector2'double.Vector2'2 (this : UInt64) (x0 : Binary64) (y0 : Binary64) : PMem.M Unit := do
  let mut x0 := x0
  let mut y0 := y0
  PMem.stF64 (this + 0) x0
  PMem.stF64 (this + 8) y0
  return ()

/-- C++ `Vector2<double>::operator- : Vector2<double> (const Vector2<double> &) const`, `vector2.cpp:115-118`. -/
def Vector2'double.operator_.body (fp : UInt64) (this : UInt64) (sret : UInt64) (v : UInt64) : PMem.M Unit := do
  let t'1 ← PMem.ldF64 this
  let t'2 ← PMem.ldF64 v
  let t'3 ← PMem.ldF64 (this + 8)
  let t'4 ← PMem.ldF64 (v + 8)
  Vector2'double.Vector2'2 (fp + 0) (t'1 - t'2) (t'3 - t'4)
  Vector2'double.Vector2 sret (fp + 0)
  return ()

def Vector2'double.operator_ (this : UInt64) (sret : UInt64) (v : UInt64) : PMem.M Unit := do
  let fp ← PMem.enter 16
  let r ← Vector2'double.operator_.body fp this sret v
  PMem.leave fp
  return r

/-- C++ `Vector2<float>::Vector2 : void (const float, const float)`, `vector2.h:55-57`. -/
def Vector2'float.Vector2'2 (this : UInt64) (x0 : Binary32) (y0 : Binary32) : PMem.M Unit := do
  let mut x0 := x0
  let mut y0 := y0
  PMem.stF32 (this + 0) x0
  PMem.stF32 (this + 4) y0
  return ()

/-- C++ `Vector2<float>::Vector2 : void (Vector2<float> &&) noexcept`, `AP_Common.h:?-?`. -/
def Vector2'float.Vector2'3 (this : UInt64) (arg : UInt64) : PMem.M Unit := do
  let t'1 ← PMem.ldF32 arg
  PMem.stF32 (this + 0) t'1
  let t'2 ← PMem.ldF32 (arg + 4)
  PMem.stF32 (this + 4) t'2
  return ()

/-- C++ `Vector2<float>::operator- : Vector2<float> (const Vector2<float> &) const`, `vector2.cpp:115-118`. -/
def Vector2'float.operator_.body (fp : UInt64) (this : UInt64) (sret : UInt64) (v : UInt64) : PMem.M Unit := do
  let t'1 ← PMem.ldF32 this
  let t'2 ← PMem.ldF32 v
  let t'3 ← PMem.ldF32 (this + 4)
  let t'4 ← PMem.ldF32 (v + 4)
  Vector2'float.Vector2'2 (fp + 0) (t'1 - t'2) (t'3 - t'4)
  Vector2'float.Vector2'3 sret (fp + 0)
  return ()

def Vector2'float.operator_ (this : UInt64) (sret : UInt64) (v : UInt64) : PMem.M Unit := do
  let fp ← PMem.enter 8
  let r ← Vector2'float.operator_.body fp this sret v
  PMem.leave fp
  return r

/-- C++ `Vector3<float>::Vector3 : void (Vector3<float> &&) noexcept`, `AP_Common.h:?-?`. -/
def Vector3'float.Vector3'3 (this : UInt64) (arg : UInt64) : PMem.M Unit := do
  let t'1 ← PMem.ldF32 arg
  PMem.stF32 (this + 0) t'1
  let t'2 ← PMem.ldF32 (arg + 4)
  PMem.stF32 (this + 4) t'2
  let t'3 ← PMem.ldF32 (arg + 8)
  PMem.stF32 (this + 8) t'3
  return ()

/-- C++ `Vector3<float>::Vector3 : void (const Vector3<float> &) noexcept`, `vector3.h:72-?`. -/
def Vector3'float.Vector3'4 (this : UInt64) (arg : UInt64) : PMem.M Unit := do
  let t'1 ← PMem.ldF32 arg
  PMem.stF32 (this + 0) t'1
  let t'2 ← PMem.ldF32 (arg + 4)
  PMem.stF32 (this + 4) t'2
  let t'3 ← PMem.ldF32 (arg + 8)
  PMem.stF32 (this + 8) t'3
  return ()

/-- `angle_rad_to_accel_mss` as a pure function of its arguments (it reads and writes no memory). -/
def angle_rad_to_accel_mss.pure' (angle_rad : Binary32) : Id Binary32 := do
  let mut angle_rad := angle_rad
  return ((Binary32.ofBits 0x411ce80a /- 122583127/12500000 -/) * (Musl.tanf.tanf angle_rad))

/-- C++ `angle_rad_to_accel_mss : float (float)`, `control.cpp:823-827`. -/
def angle_rad_to_accel_mss (angle_rad : Binary32) : PMem.M Binary32 :=
  pure (_root_.Vehicle_lib.angle_rad_to_accel_mss.pure' angle_rad)

/-- `norm` as a pure function of its arguments (it reads and writes no memory). -/
def norm.pure' (first : Binary32) (second : Binary32) : Id Binary32 := do
  let mut first := first
  let mut second := second
  let t'1 ← _root_.Vehicle_lib.sq.pure' first
  let t'2 ← _root_.Vehicle_lib.sq.pure' second
  return (Binary32.sqrt (t'1 + t'2))

/-- C++ `norm : float (const float, const float)`, `AP_Math.h:291-293`. -/
def norm (first : Binary32) (second : Binary32) : PMem.M Binary32 :=
  pure (_root_.Vehicle_lib.norm.pure' first second)

/-- C++ `Vector2<float>::length : float () const`, `vector2.cpp:30-33`. -/
def Vector2'float.length (this : UInt64) : PMem.M Binary32 := do
  let t'1 ← PMem.ldF32 this
  let t'2 ← PMem.ldF32 (this + 4)
  let t'3 ← norm t'1 t'2
  return t'3

/-- C++ `Vector2<float>::limit_length : bool (float)`, `vector2.cpp:37-46`. -/
def Vector2'float.limit_length (this : UInt64) (max_length : Binary32) : PMem.M Bool := do
  let mut max_length := max_length
  let t'1 ← Vector2'float.length this
  let mut len : Binary32 := t'1
  let mut sc'3 := (decide (len > max_length))
  if sc'3 then
    let t'2 ← is_positive'float len
    sc'3 := t'2
  if sc'3 then
    let t'4 ← PMem.ldF32 this
    let t'5 := (t'4 * (max_length / len))
    PMem.stF32 this t'5
    let t'6 := (this + 4)
    let t'7 ← PMem.ldF32 t'6
    let t'8 := (t'7 * (max_length / len))
    PMem.stF32 t'6 t'8
    return true
  return false

/-- C++ `Vector2<float>::operator* : Vector2<float> (const float) const`, `vector2.cpp:109-112`. -/
def Vector2'float.operator_'2.body (fp : UInt64) (this : UInt64) (sret : UInt64) (num : Binary32) : PMem.M Unit := do
  let mut num := num
  let t'1 ← PMem.ldF32 this
  let t'2 ← PMem.ldF32 (this + 4)
  Vector2'float.Vector2'2 (fp + 0) (t'1 * num) (t'2 * num)
  Vector2'float.Vector2'3 sret (fp + 0)
  return ()

def Vector2'float.operator_'2 (this : UInt64) (sret : UInt64) (num : Binary32) : PMem.M Unit := do
  let fp ← PMem.enter 8
  let r ← Vector2'float.operator_'2.body fp this sret num
  PMem.leave fp
  return r

/-- C++ `QuaternionT<float>::zero : void ()`, `<scratch space>:686-689`. -/
def QuaternionT'float.zero (this : UInt64) : PMem.M Unit := do
  let t'1 := Binary64.toBinary32 ((Binary64.ofBits 0x0000000000000000 /- 0 -/))
  PMem.stF32 (this + 12) t'1
  let t'2 ← PMem.ldF32 (this + 12)
  PMem.stF32 (this + 8) t'2
  let t'3 ← PMem.ldF32 (this + 8)
  PMem.stF32 (this + 4) t'3
  let t'4 ← PMem.ldF32 (this + 4)
  PMem.stF32 this t'4
  return ()

/-- C++ `QuaternionT<float>::QuaternionT : void (const float, const float, const float, const float)`, `quaternion.h:42-45`. -/
def QuaternionT'float.QuaternionT'2 (this : UInt64) (_q1 : Binary32) (_q2 : Binary32) (_q3 : Binary32) (_q4 : Binary32) : PMem.M Unit := do
  let mut _q1 := _q1
  let mut _q2 := _q2
  let mut _q3 := _q3
  let mut _q4 := _q4
  PMem.stF32 (this + 0) _q1
  PMem.stF32 (this + 4) _q2
  PMem.stF32 (this + 8) _q3
  PMem.stF32 (this + 12) _q4
  return ()

/-- C++ `QuaternionT<float>::length_squared : float () const`, `quaternion.cpp:640-643`. -/
def QuaternionT'float.length_squared (this : UInt64) : PMem.M Binary32 := do
  let t'1 ← PMem.ldF32 this
  let t'2 ← PMem.ldF32 this
  let t'3 ← PMem.ldF32 (this + 4)
  let t'4 ← PMem.ldF32 (this + 4)
  let t'5 ← PMem.ldF32 (this + 8)
  let t'6 ← PMem.ldF32 (this + 8)
  let t'7 ← PMem.ldF32 (this + 12)
  let t'8 ← PMem.ldF32 (this + 12)
  return ((((t'1 * t'2) + (t'3 * t'4)) + (t'5 * t'6)) + (t'7 * t'8))

/-- C++ `QuaternionT<float>::is_unit_length : bool () const`, `<scratch space>:695-709`. -/
def QuaternionT'float.is_unit_length (this : UInt64) : PMem.M Bool := do
  let t'1 ← QuaternionT'float.length_squared this
  if (decide ((Binary32.toBinary64 ((Binary32.abs (t'1 - (Int32.toBinary32 ((1 : Int32))))))) < (Binary64.ofBits 0x3f50624dd2f1a9fc /- 1/1000 -/))) then
    return true
  return false

/-- `Vector3'float.operator__` as a pure function of its arguments (it reads and writes no memory). -/
def Vector3'float.operator__.pure' (this : UInt64) (i : UInt8) : Id UInt64 := do
  let mut i := i
  let mut _v : UInt64 := this
  return (_v + ((UInt64.toInt64 (UInt8.toUInt64 (i))) * 4).toUInt64)

/-- C++ `Vector3<float>::operator[] : const float &(uint8_t) const`, `vector3.h:144-150`. -/
def Vector3'float.operator__ (this : UInt64) (i : UInt8) : PMem.M UInt64 :=
  pure (_root_.Vehicle_lib.Vector3'float.operator__.pure' this i)

/-- C++ `QuaternionT<float>::from_euler : void (float, float, float)`, `quaternion.cpp:421-434`. -/
def QuaternionT'float.from_euler'2 (this : UInt64) (roll : Binary32) (pitch : Binary32) (yaw : Binary32) : PMem.M Unit := do
  let mut roll := roll
  let mut pitch := pitch
  let mut yaw := yaw
  let mut cr2 : Binary32 := Binary64.toBinary32 ((Musl.cos.cos ((Binary32.toBinary64 (roll)) * (Binary64.ofBits 0x3fe0000000000000 /- 1/2 -/))))
  let mut cp2 : Binary32 := Binary64.toBinary32 ((Musl.cos.cos ((Binary32.toBinary64 (pitch)) * (Binary64.ofBits 0x3fe0000000000000 /- 1/2 -/))))
  let mut cy2 : Binary32 := Binary64.toBinary32 ((Musl.cos.cos ((Binary32.toBinary64 (yaw)) * (Binary64.ofBits 0x3fe0000000000000 /- 1/2 -/))))
  let mut sr2 : Binary32 := Binary64.toBinary32 ((Musl.sin.sin ((Binary32.toBinary64 (roll)) * (Binary64.ofBits 0x3fe0000000000000 /- 1/2 -/))))
  let mut sp2 : Binary32 := Binary64.toBinary32 ((Musl.sin.sin ((Binary32.toBinary64 (pitch)) * (Binary64.ofBits 0x3fe0000000000000 /- 1/2 -/))))
  let mut sy2 : Binary32 := Binary64.toBinary32 ((Musl.sin.sin ((Binary32.toBinary64 (yaw)) * (Binary64.ofBits 0x3fe0000000000000 /- 1/2 -/))))
  let t'1 := (((cr2 * cp2) * cy2) + ((sr2 * sp2) * sy2))
  PMem.stF32 this t'1
  let t'2 := (((sr2 * cp2) * cy2) - ((cr2 * sp2) * sy2))
  PMem.stF32 (this + 4) t'2
  let t'3 := (((cr2 * sp2) * cy2) + ((sr2 * cp2) * sy2))
  PMem.stF32 (this + 8) t'3
  let t'4 := (((cr2 * cp2) * sy2) - ((sr2 * sp2) * cy2))
  PMem.stF32 (this + 12) t'4
  return ()

/-- C++ `QuaternionT<float>::from_euler : void (const Vector3<float> &)`, `ftype.h:436-439`. -/
def QuaternionT'float.from_euler (this : UInt64) (v : UInt64) : PMem.M Unit := do
  let t'1 ← Vector3'float.operator__ v (Int8.toUInt8 (Int32.toInt8 ((0 : Int32))))
  let t'2 ← PMem.ldF32 t'1
  let t'3 ← Vector3'float.operator__ v (Int8.toUInt8 (Int32.toInt8 ((1 : Int32))))
  let t'4 ← PMem.ldF32 t'3
  let t'5 ← Vector3'float.operator__ v (Int8.toUInt8 (Int32.toInt8 ((2 : Int32))))
  let t'6 ← PMem.ldF32 t'5
  QuaternionT'float.from_euler'2 this t'2 t'4 t'6
  return ()

/-- C++ `QuaternionT<float>::get_euler_roll : float () const`, `quaternion.cpp:587-590`. -/
def QuaternionT'float.get_euler_roll (this : UInt64) : PMem.M Binary32 := do
  let t'1 ← PMem.ldF32 this
  let t'2 ← PMem.ldF32 (this + 4)
  let t'3 ← PMem.ldF32 (this + 8)
  let t'4 ← PMem.ldF32 (this + 12)
  let t'5 ← PMem.ldF32 (this + 4)
  let t'6 ← PMem.ldF32 (this + 4)
  let t'7 ← PMem.ldF32 (this + 8)
  let t'8 ← PMem.ldF32 (this + 8)
  return (Musl.atan2f.atan2f ((Binary32.ofBits 0x40000000 /- 2 -/) * ((t'1 * t'2) + (t'3 * t'4))) ((Binary32.ofBits 0x3f800000 /- 1 -/) - ((Binary32.ofBits 0x40000000 /- 2 -/) * ((t'5 * t'6) + (t'7 * t'8)))))

/-- `safe_asin'float` as a pure function of its arguments (it reads and writes no memory). -/
def safe_asin'float.pure' (v : Binary32) : Id Binary32 := do
  let mut v := v
  let mut f : Binary32 := v
  if (Binary32.isNaN f) then
    return (Binary32.ofBits 0x00000000 /- 0 -/)
  if (decide (f ≥ (Binary32.ofBits 0x3f800000 /- 1 -/))) then
    return Binary64.toBinary32 (((Binary64.ofBits 0x400921fb54442d18 /- 31415926535897931/10000000000000000 -/) / (Int32.toBinary64 ((2 : Int32)))))
  if (decide (f ≤ (-(Binary32.ofBits 0x3f800000 /- 1 -/)))) then
    return Binary64.toBinary32 ((-((Binary64.ofBits 0x400921fb54442d18 /- 31415926535897931/10000000000000000 -/) / (Int32.toBinary64 ((2 : Int32))))))
  return (Musl.asinf.asinf f)

/-- C++ `safe_asin : float (const float)`, `definitions.h:50-63`. -/
def safe_asin'float (v : Binary32) : PMem.M Binary32 :=
  pure (_root_.Vehicle_lib.safe_asin'float.pure' v)

/-- C++ `QuaternionT<float>::get_euler_pitch : float () const`, `ftype.h:594-597`. -/
def QuaternionT'float.get_euler_pitch (this : UInt64) : PMem.M Binary32 := do
  let t'1 ← PMem.ldF32 this
  let t'2 ← PMem.ldF32 (this + 8)
  let t'3 ← PMem.ldF32 (this + 12)
  let t'4 ← PMem.ldF32 (this + 4)
  let t'5 ← safe_asin'float ((Binary32.ofBits 0x40000000 /- 2 -/) * ((t'1 * t'2) - (t'3 * t'4)))
  return t'5

/-- C++ `QuaternionT<float>::get_euler_yaw : float () const`, `ftype.h:601-604`. -/
def QuaternionT'float.get_euler_yaw (this : UInt64) : PMem.M Binary32 := do
  let t'1 ← PMem.ldF32 this
  let t'2 ← PMem.ldF32 (this + 12)
  let t'3 ← PMem.ldF32 (this + 4)
  let t'4 ← PMem.ldF32 (this + 8)
  let t'5 ← PMem.ldF32 (this + 8)
  let t'6 ← PMem.ldF32 (this + 8)
  let t'7 ← PMem.ldF32 (this + 12)
  let t'8 ← PMem.ldF32 (this + 12)
  return (Musl.atan2f.atan2f ((Binary32.ofBits 0x40000000 /- 2 -/) * ((t'1 * t'2) + (t'3 * t'4))) ((Binary32.ofBits 0x3f800000 /- 1 -/) - ((Binary32.ofBits 0x40000000 /- 2 -/) * ((t'5 * t'6) + (t'7 * t'8)))))

/-- C++ `QuaternionT<float>::to_euler : void (float &, float &, float &) const`, `ftype.h:616-621`. -/
def QuaternionT'float.to_euler (this : UInt64) (roll : UInt64) (pitch : UInt64) (yaw : UInt64) : PMem.M Unit := do
  let t'1 ← QuaternionT'float.get_euler_roll this
  PMem.stF32 roll t'1
  let t'2 ← QuaternionT'float.get_euler_pitch this
  PMem.stF32 pitch t'2
  let t'3 ← QuaternionT'float.get_euler_yaw this
  PMem.stF32 yaw t'3
  return ()

/-- C++ `Vector3<double>::Vector3 : void ()`, `vector3.h:79-82`. -/
def Vector3'double.Vector3 (this : UInt64) : PMem.M Unit := do
  PMem.stF64 (this + 0) (Int32.toBinary64 ((0 : Int32)))
  PMem.stF64 (this + 8) (Int32.toBinary64 ((0 : Int32)))
  PMem.stF64 (this + 16) (Int32.toBinary64 ((0 : Int32)))
  return ()

/-- C++ `Vector3<double>::Vector3 : void (const double, const double, const double)`, `vector3.h:85-88`. -/
def Vector3'double.Vector3'3 (this : UInt64) (x0 : Binary64) (y0 : Binary64) (z0 : Binary64) : PMem.M Unit := do
  let mut x0 := x0
  let mut y0 := y0
  let mut z0 := z0
  PMem.stF64 (this + 0) x0
  PMem.stF64 (this + 8) y0
  PMem.stF64 (this + 16) z0
  return ()

/-- C++ `Vector3<double>::operator+= : Vector3<double> &(const Vector3<double> &)`, `vector3.cpp:376-380`. -/
def Vector3'double.operator__ (this : UInt64) (v : UInt64) : PMem.M UInt64 := do
  let t'1 ← PMem.ldF64 this
  let t'2 ← PMem.ldF64 v
  let t'3 := (t'1 + t'2)
  PMem.stF64 this t'3
  let t'4 := (this + 8)
  let t'5 ← PMem.ldF64 t'4
  let t'6 ← PMem.ldF64 (v + 8)
  let t'7 := (t'5 + t'6)
  PMem.stF64 t'4 t'7
  let t'8 := (this + 16)
  let t'9 ← PMem.ldF64 t'8
  let t'10 ← PMem.ldF64 (v + 16)
  let t'11 := (t'9 + t'10)
  PMem.stF64 t'8 t'11
  return this

/-- `wrap_2PI` as a pure function of its arguments (it reads and writes no memory). -/
def wrap_2PI.pure' (radian : Binary32) : Id Binary32 := do
  let mut radian := radian
  let mut res : Binary32 := (Musl.fmodf.fmodf radian ((Binary64.toBinary32 ((Binary64.ofBits 0x400921fb54442d18 /- 31415926535897931/10000000000000000 -/))) * (Int32.toBinary32 ((2 : Int32)))))
  if (decide (res < (Int32.toBinary32 ((0 : Int32))))) then
    let t'1 := (res + ((Binary64.toBinary32 ((Binary64.ofBits 0x400921fb54442d18 /- 31415926535897931/10000000000000000 -/))) * (Int32.toBinary32 ((2 : Int32)))))
    res := t'1
  return res

/-- C++ `wrap_2PI : float (const float)`, `AP_Math.cpp:251-258`. -/
def wrap_2PI (radian : Binary32) : PMem.M Binary32 :=
  pure (_root_.Vehicle_lib.wrap_2PI.pure' radian)

/-- `wrap_PI'float` as a pure function of its arguments (it reads and writes no memory). -/
def wrap_PI'float.pure' (radian : Binary32) : Id Binary32 := do
  let mut radian := radian
  let t'1 ← _root_.Vehicle_lib.wrap_2PI.pure' radian
  let mut res : Binary32 := t'1
  if (decide (res > (Binary64.toBinary32 ((Binary64.ofBits 0x400921fb54442d18 /- 31415926535897931/10000000000000000 -/))))) then
    let t'2 := (res - (Binary64.toBinary32 (((Binary64.ofBits 0x400921fb54442d18 /- 31415926535897931/10000000000000000 -/) * (Int32.toBinary64 ((2 : Int32)))))))
    res := t'2
  return res

/-- C++ `wrap_PI : float (const float)`, `AP_Math.cpp:270-277`. -/
def wrap_PI'float (radian : Binary32) : PMem.M Binary32 :=
  pure (_root_.Vehicle_lib.wrap_PI'float.pure' radian)

/-- C++ `Vector3<double>::zero : void ()`, `vector3.h:229-232`. -/
def Vector3'double.zero (this : UInt64) : PMem.M Unit := do
  let t'1 := Int32.toBinary64 ((0 : Int32))
  PMem.stF64 (this + 16) t'1
  let t'2 ← PMem.ldF64 (this + 16)
  PMem.stF64 (this + 8) t'2
  let t'3 ← PMem.ldF64 (this + 8)
  PMem.stF64 this t'3
  return ()

/-- C++ `Vector2<float>::Vector2 : void ()`, `vector2.h:50-52`. -/
def Vector2'float.Vector2 (this : UInt64) : PMem.M Unit := do
  PMem.stF32 (this + 0) (Int32.toBinary32 ((0 : Int32)))
  PMem.stF32 (this + 4) (Int32.toBinary32 ((0 : Int32)))
  return ()

/-- C++ `SCurve::add_segment : void (uint8_t &, float, SegmentType, float, float, float, float)`, `SCurve.cpp:1199-1208`. -/
def SCurve.add_segment (this : UInt64) (index : UInt64) (end_time : Binary32) (seg_type : Int32) (jerk_ref : Binary32) (end_accel : Binary32) (end_vel : Binary32) (end_pos : Binary32) : PMem.M Unit := do
  let mut end_time := end_time
  let mut seg_type := seg_type
  let mut jerk_ref := jerk_ref
  let mut end_accel := end_accel
  let mut end_vel := end_vel
  let mut end_pos := end_pos
  let t'1 ← PMem.ldU8 index
  PMem.stF32 (((this + 32) + ((UInt64.toInt64 (UInt8.toUInt64 (t'1))) * 24).toUInt64) + 8) end_time
  let t'2 ← PMem.ldU8 index
  PMem.stI32 (((this + 32) + ((UInt64.toInt64 (UInt8.toUInt64 (t'2))) * 24).toUInt64) + 4) seg_type
  let t'3 ← PMem.ldU8 index
  PMem.stF32 ((this + 32) + ((UInt64.toInt64 (UInt8.toUInt64 (t'3))) * 24).toUInt64) jerk_ref
  let t'4 ← PMem.ldU8 index
  PMem.stF32 (((this + 32) + ((UInt64.toInt64 (UInt8.toUInt64 (t'4))) * 24).toUInt64) + 12) end_accel
  let t'5 ← PMem.ldU8 index
  PMem.stF32 (((this + 32) + ((UInt64.toInt64 (UInt8.toUInt64 (t'5))) * 24).toUInt64) + 16) end_vel
  let t'6 ← PMem.ldU8 index
  PMem.stF32 (((this + 32) + ((UInt64.toInt64 (UInt8.toUInt64 (t'6))) * 24).toUInt64) + 20) end_pos
  let t'7 ← PMem.ldU8 index
  let t'8 := (t'7 + 1)
  PMem.stU8 index t'8
  return ()

/-- C++ `SCurve::init : void ()`, `SCurve.cpp:46-61`. -/
def SCurve.init.body (fp : UInt64) (this : UInt64) : PMem.M Unit := do
  let t'1 := (Binary32.ofBits 0x00000000 /- 0 -/)
  PMem.stF32 this t'1
  let t'2 := (Binary32.ofBits 0x00000000 /- 0 -/)
  PMem.stF32 (this + 4) t'2
  let t'3 := (Binary32.ofBits 0x00000000 /- 0 -/)
  PMem.stF32 (this + 8) t'3
  let t'4 := (Binary32.ofBits 0x00000000 /- 0 -/)
  PMem.stF32 (this + 12) t'4
  let t'5 := (Binary32.ofBits 0x00000000 /- 0 -/)
  PMem.stF32 (this + 20) t'5
  let t'6 := (Binary32.ofBits 0x00000000 /- 0 -/)
  PMem.stF32 (this + 24) t'6
  let t'7 := Int8.toUInt8 (Int32.toInt8 ((0 : Int32)))
  PMem.stU8 (this + 28) t'7
  SCurve.add_segment this (this + 28) (Binary32.ofBits 0x00000000 /- 0 -/) (0 : Int32) (Binary32.ofBits 0x00000000 /- 0 -/) (Binary32.ofBits 0x00000000 /- 0 -/) (Binary32.ofBits 0x00000000 /- 0 -/) (Binary32.ofBits 0x00000000 /- 0 -/)
  PMem.stB (this + 584) false
  Vector3'float.zero (this + 588)
  let t'8 := (Binary32.ofBits 0x00000000 /- 0 -/)
  PMem.stF32 (this + 600) t'8
  discard <| PMem.memset ((fp + 0) + 0) 0 4
  discard <| PMem.memset ((fp + 0) + 4) 0 4
  discard <| PMem.memset ((fp + 0) + 8) 0 4
  Vector2'float.Vector2 ((fp + 0) + 12)
  discard <| PMem.memcpy (this + 604) (fp + 0) 20
  discard <| pure ((this + 604))
  return ()

def SCurve.init (this : UInt64) : PMem.M Unit := do
  let fp ← PMem.enter 20
  let r ← SCurve.init.body fp this
  PMem.leave fp
  return r

/-- `stopping_distance` as a pure function of its arguments (it reads and writes no memory). -/
def stopping_distance.pure' (velocity : Binary32) (p : Binary32) (accel_max : Binary32) : Id Binary32 := do
  let mut velocity := velocity
  let mut p := p
  let mut accel_max := accel_max
  let t'1 ← _root_.Vehicle_lib.inv_sqrt_controller.pure' velocity p accel_max
  return t'1

/-- C++ `stopping_distance : float (float, float, float)`, `control.cpp:712-716`. -/
def stopping_distance (velocity : Binary32) (p : Binary32) (accel_max : Binary32) : PMem.M Binary32 :=
  pure (_root_.Vehicle_lib.stopping_distance.pure' velocity p accel_max)

/-- C++ `Vector2<double>::operator-= : Vector2<double> &(const Vector2<double> &)`, `vector2.cpp:77-81`. -/
def Vector2'double.operator__ (this : UInt64) (v : UInt64) : PMem.M UInt64 := do
  let t'1 ← PMem.ldF64 this
  let t'2 ← PMem.ldF64 v
  let t'3 := (t'1 - t'2)
  PMem.stF64 this t'3
  let t'4 := (this + 8)
  let t'5 ← PMem.ldF64 t'4
  let t'6 ← PMem.ldF64 (v + 8)
  let t'7 := (t'5 - t'6)
  PMem.stF64 t'4 t'7
  return this

/-- C++ `Vector2<float>::Vector2 : void (const Vector2<float> &) noexcept`, `AP_Common.h:45-?`. -/
def Vector2'float.Vector2'4 (this : UInt64) (arg : UInt64) : PMem.M Unit := do
  let t'1 ← PMem.ldF32 arg
  PMem.stF32 (this + 0) t'1
  let t'2 ← PMem.ldF32 (arg + 4)
  PMem.stF32 (this + 4) t'2
  return ()

/-- C++ `Vector2<float>::operator-= : Vector2<float> &(const Vector2<float> &)`, `vector2.cpp:77-81`. -/
def Vector2'float.operator__'2 (this : UInt64) (v : UInt64) : PMem.M UInt64 := do
  let t'1 ← PMem.ldF32 this
  let t'2 ← PMem.ldF32 v
  let t'3 := (t'1 - t'2)
  PMem.stF32 this t'3
  let t'4 := (this + 4)
  let t'5 ← PMem.ldF32 t'4
  let t'6 ← PMem.ldF32 (v + 4)
  let t'7 := (t'5 - t'6)
  PMem.stF32 t'4 t'7
  return this

/-- C++ `Vector2<double>::operator+= : Vector2<double> &(const Vector2<double> &)`, `vector2.cpp:96-100`. -/
def Vector2'double.operator__'2 (this : UInt64) (v : UInt64) : PMem.M UInt64 := do
  let t'1 ← PMem.ldF64 this
  let t'2 ← PMem.ldF64 v
  let t'3 := (t'1 + t'2)
  PMem.stF64 this t'3
  let t'4 := (this + 8)
  let t'5 ← PMem.ldF64 t'4
  let t'6 ← PMem.ldF64 (v + 8)
  let t'7 := (t'5 + t'6)
  PMem.stF64 t'4 t'7
  return this

/-- C++ `Vector2<float>::todouble : Vector2<double> () const`, `vector2.h:181-183`. -/
def Vector2'float.todouble.body (fp : UInt64) (this : UInt64) (sret : UInt64) : PMem.M Unit := do
  let t'1 ← PMem.ldF32 this
  let t'2 ← PMem.ldF32 (this + 4)
  Vector2'double.Vector2'2 (fp + 0) (Binary32.toBinary64 (t'1)) (Binary32.toBinary64 (t'2))
  Vector2'double.Vector2 sret (fp + 0)
  return ()

def Vector2'float.todouble (this : UInt64) (sret : UInt64) : PMem.M Unit := do
  let fp ← PMem.enter 16
  let r ← Vector2'float.todouble.body fp this sret
  PMem.leave fp
  return r

/-- C++ `Vector2<double>::operator+ : Vector2<double> (const Vector2<double> &) const`, `vector2.cpp:121-124`. -/
def Vector2'double.operator_'2.body (fp : UInt64) (this : UInt64) (sret : UInt64) (v : UInt64) : PMem.M Unit := do
  let t'1 ← PMem.ldF64 this
  let t'2 ← PMem.ldF64 v
  let t'3 ← PMem.ldF64 (this + 8)
  let t'4 ← PMem.ldF64 (v + 8)
  Vector2'double.Vector2'2 (fp + 0) (t'1 + t'2) (t'3 + t'4)
  Vector2'double.Vector2 sret (fp + 0)
  return ()

def Vector2'double.operator_'2 (this : UInt64) (sret : UInt64) (v : UInt64) : PMem.M Unit := do
  let fp ← PMem.enter 16
  let r ← Vector2'double.operator_'2.body fp this sret v
  PMem.leave fp
  return r

/-- `is_zero'2` as a pure function of its arguments (it reads and writes no memory). -/
def is_zero'2.pure' (x : Binary64) : Id Bool := do
  let mut x := x
  return (decide ((Binary64.abs x) < (Binary32.toBinary64 ((Binary32.ofBits 0x34000000 /- 11920929/100000000000000 -/)))))

/-- C++ `is_zero : bool (const double)`, `ftype.h:68-74`. -/
def is_zero'2 (x : Binary64) : PMem.M Bool :=
  pure (_root_.Vehicle_lib.is_zero'2.pure' x)

/-- C++ `Vector3<double>::is_zero : bool () const`, `vector3.h:325-327`. -/
def Vector3'double.is_zero (this : UInt64) : PMem.M Bool := do
  let t'1 ← PMem.ldF64 this
  let t'2 ← is_zero'2 t'1
  let mut sc'5 := t'2
  if sc'5 then
    let t'3 ← PMem.ldF64 (this + 8)
    let t'4 ← is_zero'2 t'3
    sc'5 := t'4
  let mut sc'8 := sc'5
  if sc'8 then
    let t'6 ← PMem.ldF64 (this + 16)
    let t'7 ← is_zero'2 t'6
    sc'8 := t'7
  return sc'8

/-- C++ `Vector3<double>::Vector3 : void (Vector3<double> &&) noexcept`, `AP_Common.h:?-?`. -/
def Vector3'double.Vector3'2 (this : UInt64) (arg : UInt64) : PMem.M Unit := do
  let t'1 ← PMem.ldF64 arg
  PMem.stF64 (this + 0) t'1
  let t'2 ← PMem.ldF64 (arg + 8)
  PMem.stF64 (this + 8) t'2
  let t'3 ← PMem.ldF64 (arg + 16)
  PMem.stF64 (this + 16) t'3
  return ()

/-- `norm'2` as a pure function of its arguments (it reads and writes no memory). -/
def norm'2.pure' (first : Binary32) (second : Binary32) (third : Binary32) : Id Binary32 := do
  let mut first := first
  let mut second := second
  let mut third := third
  let t'1 ← _root_.Vehicle_lib.sq.pure' first
  let t'2 ← _root_.Vehicle_lib.sq.pure' second
  let t'3 ← _root_.Vehicle_lib.sq.pure' third
  return (Binary32.sqrt ((t'1 + t'2) + t'3))

/-- C++ `norm : float (const float, const float, const float)`, `AP_Math.h:294-296`. -/
def norm'2 (first : Binary32) (second : Binary32) (third : Binary32) : PMem.M Binary32 :=
  pure (_root_.Vehicle_lib.norm'2.pure' first second third)

/-- C++ `Vector3<float>::length : float () const`, `vector3.cpp:324-327`. -/
def Vector3'float.length (this : UInt64) : PMem.M Binary32 := do
  let t'1 ← PMem.ldF32 this
  let t'2 ← PMem.ldF32 (this + 4)
  let t'3 ← PMem.ldF32 (this + 8)
  let t'4 ← norm'2 t'1 t'2 t'3
  return t'4

/-- C++ `SCurve::time_end : float () const`, `SCurve.cpp:722-728`. -/
def SCurve.time_end (this : UInt64) : PMem.M Binary32 := do
  let t'1 ← PMem.ldU8 (this + 28)
  if ((UInt32.toInt32 (UInt8.toUInt32 (t'1))) != (UInt32.toInt32 (UInt8.toUInt32 ((23 : UInt8))))) then
    return (Binary32.ofBits 0x00000000 /- 0 -/)
  let t'2 ← PMem.ldF32 (((this + 32) + ((Int32.toInt64 ((22 : Int32))) * 24).toUInt64) + 8)
  return t'2

/-- C++ `SCurve::finished : bool () const`, `SCurve.cpp:610-613`. -/
def SCurve.finished (this : UInt64) : PMem.M Bool := do
  let t'1 ← PMem.ldF32 (this + 24)
  let t'2 ← SCurve.time_end this
  return (decide (t'1 ≥ t'2))

/-- C++ `Vector3<double>::tofloat : Vector3<float> () const`, `vector3.h:277-279`. -/
def Vector3'double.tofloat.body (fp : UInt64) (this : UInt64) (sret : UInt64) : PMem.M Unit := do
  let t'1 ← PMem.ldF64 this
  let t'2 ← PMem.ldF64 (this + 8)
  let t'3 ← PMem.ldF64 (this + 16)
  Vector3'float.Vector3 (fp + 0) (Binary64.toBinary32 (t'1)) (Binary64.toBinary32 (t'2)) (Binary64.toBinary32 (t'3))
  Vector3'float.Vector3'3 sret (fp + 0)
  return ()

def Vector3'double.tofloat (this : UInt64) (sret : UInt64) : PMem.M Unit := do
  let fp ← PMem.enter 12
  let r ← Vector3'double.tofloat.body fp this sret
  PMem.leave fp
  return r

/-- C++ `Vector3<float>::is_zero : bool () const`, `vector3.h:321-323`. -/
def Vector3'float.is_zero (this : UInt64) : PMem.M Bool := do
  let t'1 ← PMem.ldF32 this
  let t'2 ← _root_.Vehicle_lib.is_zero t'1
  let mut sc'5 := t'2
  if sc'5 then
    let t'3 ← PMem.ldF32 (this + 4)
    let t'4 ← _root_.Vehicle_lib.is_zero t'3
    sc'5 := t'4
  let mut sc'8 := sc'5
  if sc'8 then
    let t'6 ← PMem.ldF32 (this + 8)
    let t'7 ← _root_.Vehicle_lib.is_zero t'6
    sc'8 := t'7
  return sc'8

/-- C++ `Vector3<double>::operator- : Vector3<double> (const Vector3<double> &) const`, `vector3.cpp:395-398`. -/
def Vector3'double.operator_.body (fp : UInt64) (this : UInt64) (sret : UInt64) (v : UInt64) : PMem.M Unit := do
  let t'1 ← PMem.ldF64 this
  let t'2 ← PMem.ldF64 v
  let t'3 ← PMem.ldF64 (this + 8)
  let t'4 ← PMem.ldF64 (v + 8)
  let t'5 ← PMem.ldF64 (this + 16)
  let t'6 ← PMem.ldF64 (v + 16)
  Vector3'double.Vector3'3 (fp + 0) (t'1 - t'2) (t'3 - t'4) (t'5 - t'6)
  Vector3'double.Vector3'2 sret (fp + 0)
  return ()

def Vector3'double.operator_ (this : UInt64) (sret : UInt64) (v : UInt64) : PMem.M Unit := do
  let fp ← PMem.enter 24
  let r ← Vector3'double.operator_.body fp this sret v
  PMem.leave fp
  return r

/-- C++ `Vector3<float>::operator* : float (const Vector3<float> &) const`, `vector3.cpp:318-321`. -/
def Vector3'float.operator_'4 (this : UInt64) (v : UInt64) : PMem.M Binary32 := do
  let t'1 ← PMem.ldF32 this
  let t'2 ← PMem.ldF32 v
  let t'3 ← PMem.ldF32 (this + 4)
  let t'4 ← PMem.ldF32 (v + 4)
  let t'5 ← PMem.ldF32 (this + 8)
  let t'6 ← PMem.ldF32 (v + 8)
  return (((t'1 * t'2) + (t'3 * t'4)) + (t'5 * t'6))

/-- C++ `Vector3<float>::length_squared : float () const`, `vector3.h:211-214`. -/
def Vector3'float.length_squared (this : UInt64) : PMem.M Binary32 := do
  let t'1 ← Vector3'float.operator_'4 this this
  return t'1

/-- C++ `SCurve::set_straight_geometry : void ()`, `SCurve.cpp:165-173`. -/
def SCurve.set_straight_geometry.body (fp : UInt64) (this : UInt64) : PMem.M Unit := do
  PMem.stB (this + 584) false
  let t'1 := (Binary32.ofBits 0x00000000 /- 0 -/)
  PMem.stF32 (this + 604) t'1
  let t'2 ← Vector3'float.xy (this + 588)
  let t'3 ← Vector2'float.length t'2
  PMem.stF32 ((this + 604) + 4) t'3
  let t'4 := (Binary32.ofBits 0x00000000 /- 0 -/)
  PMem.stF32 ((this + 604) + 8) t'4
  Vector2'float.Vector2 (fp + 0)
  discard <| PMem.memcpy ((this + 604) + 12) (fp + 0) 8
  discard <| pure (((this + 604) + 12))
  let t'5 ← Vector3'float.length (this + 588)
  PMem.stF32 (this + 600) t'5
  return ()

def SCurve.set_straight_geometry (this : UInt64) : PMem.M Unit := do
  let fp ← PMem.enter 8
  let r ← SCurve.set_straight_geometry.body fp this
  PMem.leave fp
  return r

/-- C++ `Vector2<float>::operator+ : Vector2<float> (const Vector2<float> &) const`, `vector2.cpp:121-124`. -/
def Vector2'float.operator_'3.body (fp : UInt64) (this : UInt64) (sret : UInt64) (v : UInt64) : PMem.M Unit := do
  let t'1 ← PMem.ldF32 this
  let t'2 ← PMem.ldF32 v
  let t'3 ← PMem.ldF32 (this + 4)
  let t'4 ← PMem.ldF32 (v + 4)
  Vector2'float.Vector2'2 (fp + 0) (t'1 + t'2) (t'3 + t'4)
  Vector2'float.Vector2'3 sret (fp + 0)
  return ()

def Vector2'float.operator_'3 (this : UInt64) (sret : UInt64) (v : UInt64) : PMem.M Unit := do
  let fp ← PMem.enter 8
  let r ← Vector2'float.operator_'3.body fp this sret v
  PMem.leave fp
  return r

/-- C++ `SCurve::set_arc_geometry : void (const Vector2f &, float, float)`, `SCurve.cpp:178-186`. -/
def SCurve.set_arc_geometry (this : UInt64) (center_ne_rel : UInt64) (radius : Binary32) (angle_rad : Binary32) : PMem.M Unit := do
  let mut radius := radius
  let mut angle_rad := angle_rad
  PMem.stB (this + 584) true
  PMem.stF32 (this + 604) angle_rad
  PMem.stF32 ((this + 604) + 8) radius
  discard <| PMem.memcpy ((this + 604) + 12) center_ne_rel 8
  discard <| pure (((this + 604) + 12))
  let t'1 := (radius * (Binary32.abs angle_rad))
  PMem.stF32 ((this + 604) + 4) t'1
  let t'2 ← PMem.ldF32 ((this + 588) + 8)
  let t'3 ← sq t'2
  let t'4 ← PMem.ldF32 ((this + 604) + 4)
  let t'5 ← sq t'4
  let t'6 ← safe_sqrt'float (t'3 + t'5)
  PMem.stF32 (this + 600) t'6
  return ()

/-- C++ `SCurve::valid : bool () const`, `SCurve.cpp:1211-1245`. -/
def SCurve.valid (this : UInt64) : PMem.M Bool := do
  let t'1 ← PMem.ldU8 (this + 28)
  if ((UInt32.toInt32 (UInt8.toUInt32 (t'1))) != (UInt32.toInt32 (UInt8.toUInt32 ((23 : UInt8))))) then
    return false
  let mut i : UInt8 := Int8.toUInt8 (Int32.toInt8 ((0 : Int32)))
  let mut first'2 := true
  for _ in PMem.loopFuel do
    if !first'2 then
      let t'3 := i
      let t'4 := (t'3 + 1)
      i := t'4
      pure ()
    first'2 := false
    let t'5 ← PMem.ldU8 (this + 28)
    if !((decide ((UInt32.toInt32 (UInt8.toUInt32 (i))) < (UInt32.toInt32 (UInt8.toUInt32 (t'5)))))) then break
    let t'6 ← PMem.ldF32 ((this + 32) + ((UInt64.toInt64 (UInt8.toUInt64 (i))) * 24).toUInt64)
    let mut sc'8 := !(Binary32.isFinite t'6)
    if !sc'8 then
      let t'7 ← PMem.ldF32 (((this + 32) + ((UInt64.toInt64 (UInt8.toUInt64 (i))) * 24).toUInt64) + 8)
      sc'8 := !(Binary32.isFinite t'7)
    let mut sc'10 := sc'8
    if !sc'10 then
      let t'9 ← PMem.ldF32 (((this + 32) + ((UInt64.toInt64 (UInt8.toUInt64 (i))) * 24).toUInt64) + 12)
      sc'10 := !(Binary32.isFinite t'9)
    let mut sc'12 := sc'10
    if !sc'12 then
      let t'11 ← PMem.ldF32 (((this + 32) + ((UInt64.toInt64 (UInt8.toUInt64 (i))) * 24).toUInt64) + 16)
      sc'12 := !(Binary32.isFinite t'11)
    let mut sc'15 := sc'12
    if !sc'15 then
      let t'13 ← PMem.ldF32 (((this + 32) + ((UInt64.toInt64 (UInt8.toUInt64 (i))) * 24).toUInt64) + 16)
      let t'14 ← is_negative'float t'13
      sc'15 := t'14
    let mut sc'17 := sc'15
    if !sc'17 then
      let t'16 ← PMem.ldF32 (((this + 32) + ((UInt64.toInt64 (UInt8.toUInt64 (i))) * 24).toUInt64) + 20)
      sc'17 := !(Binary32.isFinite t'16)
    if sc'17 then
      return false
    if (decide ((UInt32.toInt32 (UInt8.toUInt32 (i))) ≥ (1 : Int32))) then
      let t'18 ← PMem.ldF32 (((this + 32) + ((UInt64.toInt64 (UInt8.toUInt64 (i))) * 24).toUInt64) + 8)
      let t'19 ← PMem.ldF32 (((this + 32) + ((Int32.toInt64 (((UInt32.toInt32 (UInt8.toUInt32 (i))) - (1 : Int32)))) * 24).toUInt64) + 8)
      let t'20 ← is_negative'float (t'18 - t'19)
      let mut sc'24 := t'20
      if !sc'24 then
        let t'21 ← PMem.ldF32 (((this + 32) + ((UInt64.toInt64 (UInt8.toUInt64 (i))) * 24).toUInt64) + 20)
        let t'22 ← PMem.ldF32 (((this + 32) + ((Int32.toInt64 (((UInt32.toInt32 (UInt8.toUInt32 (i))) - (1 : Int32)))) * 24).toUInt64) + 20)
        let t'23 ← is_negative'float (t'21 - t'22)
        sc'24 := t'23
      if sc'24 then
        return false
  let t'25 ← PMem.ldU8 (this + 28)
  let t'26 ← PMem.ldF32 (((this + 32) + ((Int32.toInt64 (((UInt32.toInt32 (UInt8.toUInt32 (t'25))) - (1 : Int32)))) * 24).toUInt64) + 12)
  let t'27 ← is_zero t'26
  if !t'27 then
    return false
  return true

/-- C++ `SCurve::debug : void () const`, `SCurve.cpp:1249-1261`. -/
def SCurve.debug (this : UInt64) : PMem.M Unit := do
  let mut i : UInt8 := Int8.toUInt8 (Int32.toInt8 ((0 : Int32)))
  let mut first'1 := true
  for _ in PMem.loopFuel do
    if !first'1 then
      let t'2 := i
      let t'3 := (t'2 + 1)
      i := t'3
      pure ()
    first'1 := false
    let t'4 ← PMem.ldU8 (this + 28)
    if !((decide ((UInt32.toInt32 (UInt8.toUInt32 (i))) < (UInt32.toInt32 (UInt8.toUInt32 (t'4)))))) then break
  return ()

/-- C++ `kinematic_limit : float (float, float, float, float, float)`, `control.cpp:756-804`. -/
def kinematic_limit.body (fp : UInt64) (dir_xy : Binary32) (dir_z : Binary32) (max_xy : Binary32) (max_z_neg : Binary32) (max_z_pos : Binary32) : PMem.M Binary32 := do
  let mut dir_xy := dir_xy
  let mut dir_z := dir_z
  let mut max_xy := max_xy
  PMem.stF32 (fp + 0) max_z_neg
  PMem.stF32 (fp + 4) max_z_pos
  let t'1 ← is_negative'float dir_xy
  let mut sc'3 := t'1
  if !sc'3 then
    let t'2 ← is_positive'float max_xy
    sc'3 := !t'2
  let mut sc'6 := sc'3
  if !sc'6 then
    let t'4 ← PMem.ldF32 (fp + 4)
    let t'5 ← is_positive'float t'4
    sc'6 := !t'5
  let mut sc'9 := sc'6
  if !sc'9 then
    let t'7 ← PMem.ldF32 (fp + 0)
    let t'8 ← is_positive'float t'7
    sc'9 := !t'8
  if sc'9 then
    return Binary64.toBinary32 ((Binary64.ofBits 0x0000000000000000 /- 0 -/))
  let t'10 ← sq dir_xy
  let t'11 ← sq dir_z
  let t'12 ← safe_sqrt'float (t'10 + t'11)
  let mut dir_length : Binary32 := t'12
  let t'13 ← is_positive'float dir_length
  if !t'13 then
    return Binary64.toBinary32 ((Binary64.ofBits 0x0000000000000000 /- 0 -/))
  let t'14 ← is_zero dir_xy
  if t'14 then
    let t'15 ← is_positive'float dir_z
    let mut c'16 : Binary32 := default
    if t'15 then
      let t'17 ← PMem.ldF32 (fp + 4)
      c'16 := t'17
    else
      let t'18 ← PMem.ldF32 (fp + 0)
      c'16 := t'18
    return c'16
  let t'19 ← is_zero dir_z
  if t'19 then
    return max_xy
  let t'20 := (dir_xy / dir_length)
  dir_xy := t'20
  let t'21 := (dir_z / dir_length)
  dir_z := t'21
  let mut slope : Binary32 := (dir_z / dir_xy)
  let t'22 ← is_positive'float slope
  if t'22 then
    let t'23 ← PMem.ldF32 (fp + 4)
    if (decide (slope < (t'23 / max_xy))) then
      return (max_xy / dir_xy)
    let t'24 ← PMem.ldF32 (fp + 4)
    return (t'24 / dir_z)
  let t'25 ← PMem.ldF32 (fp + 0)
  if (decide ((-slope) < (t'25 / max_xy))) then
    return (max_xy / dir_xy)
  let t'26 ← PMem.ldF32 (fp + 0)
  return ((-t'26) / dir_z)

def kinematic_limit (dir_xy : Binary32) (dir_z : Binary32) (max_xy : Binary32) (max_z_neg : Binary32) (max_z_pos : Binary32) : PMem.M Binary32 := do
  let fp ← PMem.enter 8
  let r ← kinematic_limit.body fp dir_xy dir_z max_xy max_z_neg max_z_pos
  PMem.leave fp
  return r

/-- C++ `SCurve::calculate_path : void (float, float, float, float, float, float, float &, float &, float &, float &, float &)`, `SCurve.cpp:941-1075`. -/
def SCurve.calculate_path.body (fp : UInt64) (Sm : Binary32) (Jm : Binary32) (V0 : Binary32) (Am : Binary32) (Vm : Binary32) (L : Binary32) (Jm_out : UInt64) (tj_out : UInt64) (t2_out : UInt64) (t4_out : UInt64) (t6_out : UInt64) : PMem.M Unit := do
  let mut Sm := Sm
  let mut Jm := Jm
  let mut V0 := V0
  PMem.stF32 (fp + 0) Am
  let mut Vm := Vm
  let mut L := L
  let t'1 := (Binary32.ofBits 0x00000000 /- 0 -/)
  PMem.stF32 Jm_out t'1
  let t'2 := (Binary32.ofBits 0x00000000 /- 0 -/)
  PMem.stF32 tj_out t'2
  let t'3 := (Binary32.ofBits 0x00000000 /- 0 -/)
  PMem.stF32 t2_out t'3
  let t'4 := (Binary32.ofBits 0x00000000 /- 0 -/)
  PMem.stF32 t4_out t'4
  let t'5 := (Binary32.ofBits 0x00000000 /- 0 -/)
  PMem.stF32 t6_out t'5
  let t'6 ← is_positive'float Sm
  let mut sc'8 := !t'6
  if !sc'8 then
    let t'7 ← is_positive'float Jm
    sc'8 := !t'7
  let mut sc'11 := sc'8
  if !sc'11 then
    let t'9 ← PMem.ldF32 (fp + 0)
    let t'10 ← is_positive'float t'9
    sc'11 := !t'10
  let mut sc'13 := sc'11
  if !sc'13 then
    let t'12 ← is_positive'float Vm
    sc'13 := !t'12
  let mut sc'15 := sc'13
  if !sc'15 then
    let t'14 ← is_positive'float L
    sc'15 := !t'14
  if sc'15 then
    return ()
  if (decide (V0 ≥ Vm)) then
    return ()
  PMem.stF32 (fp + 8) ((Jm * (Binary64.toBinary32 ((Binary64.ofBits 0x400921fb54442d18 /- 31415926535897931/10000000000000000 -/)))) / ((Binary32.ofBits 0x40000000 /- 2 -/) * Sm))
  let t'16 ← PMem.ldF32 (fp + 8)
  PMem.stF32 (fp + 12) ((Vm - V0) / ((Binary32.ofBits 0x40000000 /- 2 -/) * t'16))
  let t'17 ← MIN'float_float (fp + 0) (fp + 12)
  let t'18 ← PMem.ldF32 (fp + 8)
  let t'19 ← PMem.ldF32 (fp + 8)
  let t'20 ← sq t'19
  PMem.stF32 (fp + 16) ((L - (((Binary32.ofBits 0x40800000 /- 4 -/) * V0) * t'18)) / ((Binary32.ofBits 0x40800000 /- 4 -/) * t'20))
  let t'21 ← MIN'float_float t'17 (fp + 16)
  let t'22 ← PMem.ldF32 t'21
  let mut At : Binary32 := t'22
  let t'23 ← is_positive'float At
  if !t'23 then
    return ()
  let t'24 ← PMem.ldF32 (fp + 8)
  if (decide ((Binary32.abs At) < (Jm * t'24))) then
    let t'25 ← is_zero V0
    if t'25 then
      PMem.stF32 (fp + 20) (Musl.powf.powf ((L * (Binary64.toBinary32 ((Binary64.ofBits 0x400921fb54442d18 /- 31415926535897931/10000000000000000 -/)))) / ((Binary32.ofBits 0x41000000 /- 8 -/) * Sm)) ((Binary32.ofBits 0x3f800000 /- 1 -/) / (Binary32.ofBits 0x40800000 /- 4 -/)))
      let t'26 ← MIN'float_float (fp + 8) (fp + 20)
      PMem.stF32 (fp + 24) (Musl.powf.powf ((Vm * (Binary64.toBinary32 ((Binary64.ofBits 0x400921fb54442d18 /- 31415926535897931/10000000000000000 -/)))) / ((Binary32.ofBits 0x40800000 /- 4 -/) * Sm)) ((Binary32.ofBits 0x3f800000 /- 1 -/) / (Binary32.ofBits 0x40400000 /- 3 -/)))
      let t'27 ← MIN'float_float t'26 (fp + 24)
      let t'28 ← PMem.ldF32 (fp + 0)
      let t'29 ← safe_sqrt'float ((t'28 * (Binary64.toBinary32 ((Binary64.ofBits 0x400921fb54442d18 /- 31415926535897931/10000000000000000 -/)))) / ((Binary32.ofBits 0x40000000 /- 2 -/) * Sm))
      PMem.stF32 (fp + 28) t'29
      let t'30 ← MIN'float_float t'27 (fp + 28)
      let t'31 ← PMem.ldF32 t'30
      PMem.stF32 (fp + 8) t'31
      let t'32 ← PMem.ldF32 (fp + 8)
      let t'33 := ((((Binary32.ofBits 0x40000000 /- 2 -/) * Sm) * t'32) / (Binary64.toBinary32 ((Binary64.ofBits 0x400921fb54442d18 /- 31415926535897931/10000000000000000 -/))))
      Jm := t'33
      let t'34 ← PMem.ldF32 (fp + 8)
      let t'35 := (Jm * t'34)
      PMem.stF32 (fp + 0) t'35
    else
      PMem.stF32 (fp + 0) At
      let t'36 ← PMem.ldF32 (fp + 0)
      let t'37 ← PMem.ldF32 (fp + 8)
      let t'38 := (t'36 / t'37)
      Jm := t'38
    let t'39 ← PMem.ldF32 (fp + 0)
    let t'40 ← PMem.ldF32 (fp + 8)
    let mut sc'45 := (decide (Vm ≤ (V0 + (((Binary32.ofBits 0x40000000 /- 2 -/) * t'39) * t'40))))
    if !sc'45 then
      let t'41 ← PMem.ldF32 (fp + 8)
      let t'42 ← PMem.ldF32 (fp + 0)
      let t'43 ← PMem.ldF32 (fp + 8)
      let t'44 ← sq t'43
      sc'45 := (decide (L ≤ ((((Binary32.ofBits 0x40800000 /- 4 -/) * V0) * t'41) + (((Binary32.ofBits 0x40800000 /- 4 -/) * t'42) * t'44))))
    if sc'45 then
      let t'46 := (Binary32.ofBits 0x00000000 /- 0 -/)
      PMem.stF32 t2_out t'46
      let t'47 := (Binary32.ofBits 0x00000000 /- 0 -/)
      PMem.stF32 t4_out t'47
      let t'48 := (Binary32.ofBits 0x00000000 /- 0 -/)
      PMem.stF32 t6_out t'48
    else
      let t'49 := (Binary32.ofBits 0x00000000 /- 0 -/)
      PMem.stF32 t2_out t'49
      let t'50 ← PMem.ldF32 (fp + 0)
      let t'51 ← PMem.ldF32 (fp + 8)
      let t'52 ← PMem.ldF32 (fp + 0)
      let t'53 ← PMem.ldF32 (fp + 0)
      let t'54 ← PMem.ldF32 (fp + 0)
      PMem.stF32 (fp + 32) ((-(((V0 - Vm) + (t'50 * t'51)) + ((t'52 * t'53) / Jm))) / t'54)
      let t'55 ← PMem.ldF32 (fp + 0)
      let t'56 ← PMem.ldF32 (fp + 0)
      let t'57 ← PMem.ldF32 (fp + 0)
      let t'58 ← PMem.ldF32 (fp + 0)
      let t'59 ← PMem.ldF32 (fp + 0)
      let t'60 ← PMem.ldF32 (fp + 0)
      let t'61 ← PMem.ldF32 (fp + 0)
      let t'62 ← PMem.ldF32 (fp + 0)
      let t'63 ← PMem.ldF32 (fp + 8)
      let t'64 ← PMem.ldF32 (fp + 8)
      let t'65 ← PMem.ldF32 (fp + 0)
      let t'66 ← PMem.ldF32 (fp + 0)
      let t'67 ← PMem.ldF32 (fp + 0)
      let t'68 ← PMem.ldF32 (fp + 0)
      let t'69 ← PMem.ldF32 (fp + 0)
      let t'70 ← PMem.ldF32 (fp + 0)
      let t'71 ← PMem.ldF32 (fp + 8)
      let t'72 ← PMem.ldF32 (fp + 0)
      let t'73 ← PMem.ldF32 (fp + 8)
      let t'74 ← safe_sqrt'float ((((((((((t'57 * t'58) * t'59) * t'60) * ((Binary32.ofBits 0x3f800000 /- 1 -/) / (Binary32.ofBits 0x40800000 /- 4 -/))) + ((Jm * Jm) * (V0 * V0))) + ((((t'61 * t'62) * (Jm * Jm)) * (t'63 * t'64)) * ((Binary32.ofBits 0x3f800000 /- 1 -/) / (Binary32.ofBits 0x40800000 /- 4 -/)))) + (((t'65 * (Jm * Jm)) * L) * (Binary32.ofBits 0x40000000 /- 2 -/))) - (((t'66 * t'67) * Jm) * V0)) + (((((t'68 * t'69) * t'70) * Jm) * t'71) * ((Binary32.ofBits 0x3f800000 /- 1 -/) / (Binary32.ofBits 0x40000000 /- 2 -/)))) - (((t'72 * (Jm * Jm)) * V0) * t'73))
      let t'75 ← PMem.ldF32 (fp + 0)
      let t'76 ← PMem.ldF32 (fp + 8)
      let t'77 ← PMem.ldF32 (fp + 0)
      PMem.stF32 (fp + 36) ((((((t'55 * t'56) * ((-(Binary32.ofBits 0x40400000 /- 3 -/)) / (Binary32.ofBits 0x40000000 /- 2 -/))) + t'74) - (Jm * V0)) - (((t'75 * Jm) * t'76) * ((Binary32.ofBits 0x40400000 /- 3 -/) / (Binary32.ofBits 0x40000000 /- 2 -/)))) / (t'77 * Jm))
      let t'78 ← PMem.ldF32 (fp + 0)
      let t'79 ← PMem.ldF32 (fp + 0)
      let t'80 ← PMem.ldF32 (fp + 0)
      let t'81 ← PMem.ldF32 (fp + 0)
      let t'82 ← PMem.ldF32 (fp + 0)
      let t'83 ← PMem.ldF32 (fp + 0)
      let t'84 ← PMem.ldF32 (fp + 0)
      let t'85 ← PMem.ldF32 (fp + 0)
      let t'86 ← PMem.ldF32 (fp + 8)
      let t'87 ← PMem.ldF32 (fp + 8)
      let t'88 ← PMem.ldF32 (fp + 0)
      let t'89 ← PMem.ldF32 (fp + 0)
      let t'90 ← PMem.ldF32 (fp + 0)
      let t'91 ← PMem.ldF32 (fp + 0)
      let t'92 ← PMem.ldF32 (fp + 0)
      let t'93 ← PMem.ldF32 (fp + 0)
      let t'94 ← PMem.ldF32 (fp + 8)
      let t'95 ← PMem.ldF32 (fp + 0)
      let t'96 ← PMem.ldF32 (fp + 8)
      let t'97 ← safe_sqrt'float ((((((((((t'80 * t'81) * t'82) * t'83) * ((Binary32.ofBits 0x3f800000 /- 1 -/) / (Binary32.ofBits 0x40800000 /- 4 -/))) + ((Jm * Jm) * (V0 * V0))) + ((((t'84 * t'85) * (Jm * Jm)) * (t'86 * t'87)) * ((Binary32.ofBits 0x3f800000 /- 1 -/) / (Binary32.ofBits 0x40800000 /- 4 -/)))) + (((t'88 * (Jm * Jm)) * L) * (Binary32.ofBits 0x40000000 /- 2 -/))) - (((t'89 * t'90) * Jm) * V0)) + (((((t'91 * t'92) * t'93) * Jm) * t'94) * ((Binary32.ofBits 0x3f800000 /- 1 -/) / (Binary32.ofBits 0x40000000 /- 2 -/)))) - (((t'95 * (Jm * Jm)) * V0) * t'96))
      let t'98 ← PMem.ldF32 (fp + 0)
      let t'99 ← PMem.ldF32 (fp + 8)
      let t'100 ← PMem.ldF32 (fp + 0)
      PMem.stF32 (fp + 40) ((((((t'78 * t'79) * ((-(Binary32.ofBits 0x40400000 /- 3 -/)) / (Binary32.ofBits 0x40000000 /- 2 -/))) - t'97) - (Jm * V0)) - (((t'98 * Jm) * t'99) * ((Binary32.ofBits 0x40400000 /- 3 -/) / (Binary32.ofBits 0x40000000 /- 2 -/)))) / (t'100 * Jm))
      let t'101 ← MAX'float_float (fp + 36) (fp + 40)
      let t'102 ← MIN'float_float (fp + 32) t'101
      let t'103 ← PMem.ldF32 t'102
      PMem.stF32 t4_out t'103
      PMem.stF32 (fp + 44) (Binary32.ofBits 0x00000000 /- 0 -/)
      let t'104 ← MAX'float_float t4_out (fp + 44)
      let t'105 ← PMem.ldF32 t'104
      PMem.stF32 t4_out t'105
      let t'106 := (Binary32.ofBits 0x00000000 /- 0 -/)
      PMem.stF32 t6_out t'106
  else
    let t'107 ← PMem.ldF32 (fp + 0)
    let t'108 ← PMem.ldF32 (fp + 8)
    let t'109 ← PMem.ldF32 (fp + 0)
    let t'110 ← PMem.ldF32 (fp + 0)
    let mut sc'121 := (decide (Vm < ((V0 + (t'107 * t'108)) + ((t'109 * t'110) / Jm))))
    if !sc'121 then
      let t'111 ← PMem.ldF32 (fp + 0)
      let t'112 ← PMem.ldF32 (fp + 0)
      let t'113 ← PMem.ldF32 (fp + 0)
      let t'114 ← PMem.ldF32 (fp + 0)
      let t'115 ← PMem.ldF32 (fp + 0)
      let t'116 ← PMem.ldF32 (fp + 8)
      let t'117 ← PMem.ldF32 (fp + 8)
      let t'118 ← PMem.ldF32 (fp + 0)
      let t'119 ← PMem.ldF32 (fp + 8)
      let t'120 ← PMem.ldF32 (fp + 8)
      sc'121 := (decide (L < (((((Binary32.ofBits 0x3f800000 /- 1 -/) / (Jm * Jm)) * (((t'111 * t'112) * t'113) + ((t'114 * Jm) * ((V0 * (Binary32.ofBits 0x40000000 /- 2 -/)) + ((t'115 * t'116) * (Binary32.ofBits 0x40000000 /- 2 -/)))))) + ((V0 * t'117) * (Binary32.ofBits 0x40000000 /- 2 -/))) + (t'118 * (t'119 * t'120)))))
    if sc'121 then
      let t'122 ← PMem.ldF32 (fp + 8)
      let t'123 ← PMem.ldF32 (fp + 8)
      let t'124 ← PMem.ldF32 (fp + 8)
      let t'125 ← safe_sqrt'float ((((V0 * (-(Binary32.ofBits 0x40800000 /- 4 -/))) + (Vm * (Binary32.ofBits 0x40800000 /- 4 -/))) + (Jm * (t'123 * t'124))) / Jm)
      PMem.stF32 (fp + 48) ((Jm * (t'122 + t'125)) * ((-(Binary32.ofBits 0x3f800000 /- 1 -/)) / (Binary32.ofBits 0x40000000 /- 2 -/)))
      let t'126 ← PMem.ldF32 (fp + 8)
      let t'127 ← PMem.ldF32 (fp + 8)
      let t'128 ← PMem.ldF32 (fp + 8)
      let t'129 ← safe_sqrt'float ((((V0 * (-(Binary32.ofBits 0x40800000 /- 4 -/))) + (Vm * (Binary32.ofBits 0x40800000 /- 4 -/))) + (Jm * (t'127 * t'128))) / Jm)
      PMem.stF32 (fp + 52) ((Jm * (t'126 - t'129)) * ((-(Binary32.ofBits 0x3f800000 /- 1 -/)) / (Binary32.ofBits 0x40000000 /- 2 -/)))
      let t'130 ← MAX'float_float (fp + 48) (fp + 52)
      let t'131 ← MIN'float_float (fp + 0) t'130
      let t'132 ← PMem.ldF32 (fp + 8)
      let t'133 ← PMem.ldF32 (fp + 8)
      let t'134 ← PMem.ldF32 (fp + 8)
      let t'135 ← PMem.ldF32 (fp + 8)
      let t'136 ← PMem.ldF32 (fp + 8)
      let t'137 ← PMem.ldF32 (fp + 8)
      let t'138 ← PMem.ldF32 (fp + 8)
      let t'139 ← PMem.ldF32 (fp + 8)
      let t'140 ← PMem.ldF32 (fp + 8)
      let t'141 ← PMem.ldF32 (fp + 8)
      let t'142 ← PMem.ldF32 (fp + 8)
      let t'143 ← PMem.ldF32 (fp + 8)
      let t'144 ← safe_sqrt'float ((Musl.powf.powf ((((((-(Jm * Jm)) * L) * ((Binary32.ofBits 0x3f800000 /- 1 -/) / (Binary32.ofBits 0x40000000 /- 2 -/))) + ((((Jm * Jm) * Jm) * ((t'135 * t'136) * t'137)) * ((Binary32.ofBits 0x41000000 /- 8 -/) / (Binary32.ofBits 0x41d80000 /- 27 -/)))) - (((Jm * t'138) * (((Jm * Jm) * (t'139 * t'140)) + ((Jm * V0) * (Binary32.ofBits 0x40000000 /- 2 -/)))) * ((Binary32.ofBits 0x3f800000 /- 1 -/) / (Binary32.ofBits 0x40400000 /- 3 -/)))) + (((Jm * Jm) * V0) * t'141)) (Binary32.ofBits 0x40000000 /- 2 -/)) - (Musl.powf.powf ((((Jm * Jm) * (t'142 * t'143)) * ((Binary32.ofBits 0x3f800000 /- 1 -/) / (Binary32.ofBits 0x41100000 /- 9 -/))) - ((Jm * V0) * ((Binary32.ofBits 0x40000000 /- 2 -/) / (Binary32.ofBits 0x40400000 /- 3 -/)))) (Binary32.ofBits 0x40400000 /- 3 -/)))
      let t'145 ← PMem.ldF32 (fp + 8)
      let t'146 ← PMem.ldF32 (fp + 8)
      let t'147 ← PMem.ldF32 (fp + 8)
      let t'148 ← PMem.ldF32 (fp + 8)
      let t'149 ← PMem.ldF32 (fp + 8)
      let t'150 ← PMem.ldF32 (fp + 8)
      let t'151 ← PMem.ldF32 (fp + 8)
      let t'152 ← PMem.ldF32 (fp + 8)
      let t'153 ← PMem.ldF32 (fp + 8)
      let t'154 ← PMem.ldF32 (fp + 8)
      let t'155 ← PMem.ldF32 (fp + 8)
      let t'156 ← PMem.ldF32 (fp + 8)
      let t'157 ← PMem.ldF32 (fp + 8)
      let t'158 ← PMem.ldF32 (fp + 8)
      let t'159 ← PMem.ldF32 (fp + 8)
      let t'160 ← PMem.ldF32 (fp + 8)
      let t'161 ← safe_sqrt'float ((Musl.powf.powf ((((((-(Jm * Jm)) * L) * ((Binary32.ofBits 0x3f800000 /- 1 -/) / (Binary32.ofBits 0x40000000 /- 2 -/))) + ((((Jm * Jm) * Jm) * ((t'152 * t'153) * t'154)) * ((Binary32.ofBits 0x41000000 /- 8 -/) / (Binary32.ofBits 0x41d80000 /- 27 -/)))) - (((Jm * t'155) * (((Jm * Jm) * (t'156 * t'157)) + ((Jm * V0) * (Binary32.ofBits 0x40000000 /- 2 -/)))) * ((Binary32.ofBits 0x3f800000 /- 1 -/) / (Binary32.ofBits 0x40400000 /- 3 -/)))) + (((Jm * Jm) * V0) * t'158)) (Binary32.ofBits 0x40000000 /- 2 -/)) - (Musl.powf.powf ((((Jm * Jm) * (t'159 * t'160)) * ((Binary32.ofBits 0x3f800000 /- 1 -/) / (Binary32.ofBits 0x41100000 /- 9 -/))) - ((Jm * V0) * ((Binary32.ofBits 0x40000000 /- 2 -/) / (Binary32.ofBits 0x40400000 /- 3 -/)))) (Binary32.ofBits 0x40400000 /- 3 -/)))
      let t'162 ← PMem.ldF32 (fp + 8)
      let t'163 ← PMem.ldF32 (fp + 8)
      let t'164 ← PMem.ldF32 (fp + 8)
      let t'165 ← PMem.ldF32 (fp + 8)
      let t'166 ← PMem.ldF32 (fp + 8)
      let t'167 ← PMem.ldF32 (fp + 8)
      let t'168 ← PMem.ldF32 (fp + 8)
      PMem.stF32 (fp + 56) ((((Jm * t'132) * ((-(Binary32.ofBits 0x40000000 /- 2 -/)) / (Binary32.ofBits 0x40400000 /- 3 -/))) + ((((((Jm * Jm) * (t'133 * t'134)) * ((Binary32.ofBits 0x3f800000 /- 1 -/) / (Binary32.ofBits 0x41100000 /- 9 -/))) - ((Jm * V0) * ((Binary32.ofBits 0x40000000 /- 2 -/) / (Binary32.ofBits 0x40400000 /- 3 -/)))) * (Binary32.ofBits 0x3f800000 /- 1 -/)) / (Musl.powf.powf ((((t'144 + (((Jm * Jm) * L) * ((Binary32.ofBits 0x3f800000 /- 1 -/) / (Binary32.ofBits 0x40000000 /- 2 -/)))) - ((((Jm * Jm) * Jm) * ((t'145 * t'146) * t'147)) * ((Binary32.ofBits 0x41000000 /- 8 -/) / (Binary32.ofBits 0x41d80000 /- 27 -/)))) + (((Jm * t'148) * (((Jm * Jm) * (t'149 * t'150)) + ((Jm * V0) * (Binary32.ofBits 0x40000000 /- 2 -/)))) * ((Binary32.ofBits 0x3f800000 /- 1 -/) / (Binary32.ofBits 0x40400000 /- 3 -/)))) - (((Jm * Jm) * V0) * t'151)) ((Binary32.ofBits 0x3f800000 /- 1 -/) / (Binary32.ofBits 0x40400000 /- 3 -/))))) + (Musl.powf.powf ((((t'161 + (((Jm * Jm) * L) * ((Binary32.ofBits 0x3f800000 /- 1 -/) / (Binary32.ofBits 0x40000000 /- 2 -/)))) - ((((Jm * Jm) * Jm) * ((t'162 * t'163) * t'164)) * ((Binary32.ofBits 0x41000000 /- 8 -/) / (Binary32.ofBits 0x41d80000 /- 27 -/)))) + (((Jm * t'165) * (((Jm * Jm) * (t'166 * t'167)) + ((Jm * V0) * (Binary32.ofBits 0x40000000 /- 2 -/)))) * ((Binary32.ofBits 0x3f800000 /- 1 -/) / (Binary32.ofBits 0x40400000 /- 3 -/)))) - (((Jm * Jm) * V0) * t'168)) ((Binary32.ofBits 0x3f800000 /- 1 -/) / (Binary32.ofBits 0x40400000 /- 3 -/))))
      let t'169 ← MIN'float_float t'131 (fp + 56)
      let t'170 ← PMem.ldF32 t'169
      PMem.stF32 (fp + 0) t'170
      let t'171 ← PMem.ldF32 (fp + 0)
      let t'172 ← PMem.ldF32 (fp + 8)
      let t'173 := ((t'171 / Jm) - t'172)
      PMem.stF32 t2_out t'173
      let t'174 := (Binary32.ofBits 0x00000000 /- 0 -/)
      PMem.stF32 t4_out t'174
      let t'175 ← PMem.ldF32 t2_out
      PMem.stF32 t6_out t'175
    else
      let t'176 ← PMem.ldF32 (fp + 0)
      let t'177 ← PMem.ldF32 (fp + 8)
      let t'178 := ((t'176 / Jm) - t'177)
      PMem.stF32 t2_out t'178
      let t'179 ← PMem.ldF32 (fp + 0)
      let t'180 ← PMem.ldF32 (fp + 8)
      let t'181 ← PMem.ldF32 (fp + 0)
      let t'182 ← PMem.ldF32 (fp + 0)
      let t'183 ← PMem.ldF32 (fp + 0)
      PMem.stF32 (fp + 60) ((-(((V0 - Vm) + (t'179 * t'180)) + ((t'181 * t'182) / Jm))) / t'183)
      let t'184 ← PMem.ldF32 (fp + 0)
      let t'185 ← PMem.ldF32 (fp + 0)
      let t'186 ← PMem.ldF32 (fp + 0)
      let t'187 ← PMem.ldF32 (fp + 0)
      let t'188 ← PMem.ldF32 (fp + 0)
      let t'189 ← PMem.ldF32 (fp + 0)
      let t'190 ← PMem.ldF32 (fp + 0)
      let t'191 ← PMem.ldF32 (fp + 0)
      let t'192 ← PMem.ldF32 (fp + 8)
      let t'193 ← PMem.ldF32 (fp + 8)
      let t'194 ← PMem.ldF32 (fp + 0)
      let t'195 ← PMem.ldF32 (fp + 0)
      let t'196 ← PMem.ldF32 (fp + 0)
      let t'197 ← PMem.ldF32 (fp + 0)
      let t'198 ← PMem.ldF32 (fp + 0)
      let t'199 ← PMem.ldF32 (fp + 0)
      let t'200 ← PMem.ldF32 (fp + 8)
      let t'201 ← PMem.ldF32 (fp + 0)
      let t'202 ← PMem.ldF32 (fp + 8)
      let t'203 ← safe_sqrt'float ((((((((((t'186 * t'187) * t'188) * t'189) * ((Binary32.ofBits 0x3f800000 /- 1 -/) / (Binary32.ofBits 0x40800000 /- 4 -/))) + ((Jm * Jm) * (V0 * V0))) + ((((t'190 * t'191) * (Jm * Jm)) * (t'192 * t'193)) * ((Binary32.ofBits 0x3f800000 /- 1 -/) / (Binary32.ofBits 0x40800000 /- 4 -/)))) + (((t'194 * (Jm * Jm)) * L) * (Binary32.ofBits 0x40000000 /- 2 -/))) - (((t'195 * t'196) * Jm) * V0)) + (((((t'197 * t'198) * t'199) * Jm) * t'200) * ((Binary32.ofBits 0x3f800000 /- 1 -/) / (Binary32.ofBits 0x40000000 /- 2 -/)))) - (((t'201 * (Jm * Jm)) * V0) * t'202))
      let t'204 ← PMem.ldF32 (fp + 0)
      let t'205 ← PMem.ldF32 (fp + 8)
      let t'206 ← PMem.ldF32 (fp + 0)
      PMem.stF32 (fp + 64) ((((((t'184 * t'185) * ((-(Binary32.ofBits 0x40400000 /- 3 -/)) / (Binary32.ofBits 0x40000000 /- 2 -/))) + t'203) - (Jm * V0)) - (((t'204 * Jm) * t'205) * ((Binary32.ofBits 0x40400000 /- 3 -/) / (Binary32.ofBits 0x40000000 /- 2 -/)))) / (t'206 * Jm))
      let t'207 ← PMem.ldF32 (fp + 0)
      let t'208 ← PMem.ldF32 (fp + 0)
      let t'209 ← PMem.ldF32 (fp + 0)
      let t'210 ← PMem.ldF32 (fp + 0)
      let t'211 ← PMem.ldF32 (fp + 0)
      let t'212 ← PMem.ldF32 (fp + 0)
      let t'213 ← PMem.ldF32 (fp + 0)
      let t'214 ← PMem.ldF32 (fp + 0)
      let t'215 ← PMem.ldF32 (fp + 8)
      let t'216 ← PMem.ldF32 (fp + 8)
      let t'217 ← PMem.ldF32 (fp + 0)
      let t'218 ← PMem.ldF32 (fp + 0)
      let t'219 ← PMem.ldF32 (fp + 0)
      let t'220 ← PMem.ldF32 (fp + 0)
      let t'221 ← PMem.ldF32 (fp + 0)
      let t'222 ← PMem.ldF32 (fp + 0)
      let t'223 ← PMem.ldF32 (fp + 8)
      let t'224 ← PMem.ldF32 (fp + 0)
      let t'225 ← PMem.ldF32 (fp + 8)
      let t'226 ← safe_sqrt'float ((((((((((t'209 * t'210) * t'211) * t'212) * ((Binary32.ofBits 0x3f800000 /- 1 -/) / (Binary32.ofBits 0x40800000 /- 4 -/))) + ((Jm * Jm) * (V0 * V0))) + ((((t'213 * t'214) * (Jm * Jm)) * (t'215 * t'216)) * ((Binary32.ofBits 0x3f800000 /- 1 -/) / (Binary32.ofBits 0x40800000 /- 4 -/)))) + (((t'217 * (Jm * Jm)) * L) * (Binary32.ofBits 0x40000000 /- 2 -/))) - (((t'218 * t'219) * Jm) * V0)) + (((((t'220 * t'221) * t'222) * Jm) * t'223) * ((Binary32.ofBits 0x3f800000 /- 1 -/) / (Binary32.ofBits 0x40000000 /- 2 -/)))) - (((t'224 * (Jm * Jm)) * V0) * t'225))
      let t'227 ← PMem.ldF32 (fp + 0)
      let t'228 ← PMem.ldF32 (fp + 8)
      let t'229 ← PMem.ldF32 (fp + 0)
      PMem.stF32 (fp + 68) ((((((t'207 * t'208) * ((-(Binary32.ofBits 0x40400000 /- 3 -/)) / (Binary32.ofBits 0x40000000 /- 2 -/))) - t'226) - (Jm * V0)) - (((t'227 * Jm) * t'228) * ((Binary32.ofBits 0x40400000 /- 3 -/) / (Binary32.ofBits 0x40000000 /- 2 -/)))) / (t'229 * Jm))
      let t'230 ← MAX'float_float (fp + 64) (fp + 68)
      let t'231 ← MIN'float_float (fp + 60) t'230
      let t'232 ← PMem.ldF32 t'231
      PMem.stF32 t4_out t'232
      PMem.stF32 (fp + 72) (Binary32.ofBits 0x00000000 /- 0 -/)
      let t'233 ← MAX'float_float t4_out (fp + 72)
      let t'234 ← PMem.ldF32 t'233
      PMem.stF32 t4_out t'234
      let t'235 ← PMem.ldF32 t2_out
      PMem.stF32 t6_out t'235
  let t'236 ← PMem.ldF32 (fp + 8)
  PMem.stF32 tj_out t'236
  PMem.stF32 Jm_out Jm
  let t'237 ← PMem.ldF32 Jm_out
  let mut sc'240 := !(Binary32.isFinite t'237)
  if !sc'240 then
    let t'238 ← PMem.ldF32 Jm_out
    let t'239 ← is_negative'float t'238
    sc'240 := t'239
  let mut sc'242 := sc'240
  if !sc'242 then
    let t'241 ← PMem.ldF32 tj_out
    sc'242 := !(Binary32.isFinite t'241)
  let mut sc'245 := sc'242
  if !sc'245 then
    let t'243 ← PMem.ldF32 tj_out
    let t'244 ← is_negative'float t'243
    sc'245 := t'244
  let mut sc'247 := sc'245
  if !sc'247 then
    let t'246 ← PMem.ldF32 t2_out
    sc'247 := !(Binary32.isFinite t'246)
  let mut sc'250 := sc'247
  if !sc'250 then
    let t'248 ← PMem.ldF32 t2_out
    let t'249 ← is_negative'float t'248
    sc'250 := t'249
  let mut sc'252 := sc'250
  if !sc'252 then
    let t'251 ← PMem.ldF32 t4_out
    sc'252 := !(Binary32.isFinite t'251)
  let mut sc'255 := sc'252
  if !sc'255 then
    let t'253 ← PMem.ldF32 t4_out
    let t'254 ← is_negative'float t'253
    sc'255 := t'254
  let mut sc'257 := sc'255
  if !sc'257 then
    let t'256 ← PMem.ldF32 t6_out
    sc'257 := !(Binary32.isFinite t'256)
  let mut sc'260 := sc'257
  if !sc'260 then
    let t'258 ← PMem.ldF32 t6_out
    let t'259 ← is_negative'float t'258
    sc'260 := t'259
  if sc'260 then
    let t'261 := (Binary32.ofBits 0x00000000 /- 0 -/)
    PMem.stF32 Jm_out t'261
    let t'262 := (Binary32.ofBits 0x00000000 /- 0 -/)
    PMem.stF32 t2_out t'262
    let t'263 := (Binary32.ofBits 0x00000000 /- 0 -/)
    PMem.stF32 t4_out t'263
    let t'264 := (Binary32.ofBits 0x00000000 /- 0 -/)
    PMem.stF32 t6_out t'264
  return ()

def SCurve.calculate_path (Sm : Binary32) (Jm : Binary32) (V0 : Binary32) (Am : Binary32) (Vm : Binary32) (L : Binary32) (Jm_out : UInt64) (tj_out : UInt64) (t2_out : UInt64) (t4_out : UInt64) (t6_out : UInt64) : PMem.M Unit := do
  let fp ← PMem.enter 76
  let r ← SCurve.calculate_path.body fp Sm Jm V0 Am Vm L Jm_out tj_out t2_out t4_out t6_out
  PMem.leave fp
  return r

/-- C++ `SCurve::add_segment_const_jerk : void (uint8_t &, float, float)`, `SCurve.cpp:1090-1109`. -/
def SCurve.add_segment_const_jerk (this : UInt64) (index : UInt64) (tj : Binary32) (J0 : Binary32) : PMem.M Unit := do
  let mut tj := tj
  let mut J0 := J0
  let t'1 ← is_positive'float tj
  if !t'1 then
    let t'2 ← PMem.ldU8 index
    let t'3 ← PMem.ldF32 (((this + 32) + ((Int32.toInt64 (((UInt32.toInt32 (UInt8.toUInt32 (t'2))) - (1 : Int32)))) * 24).toUInt64) + 8)
    let t'4 ← PMem.ldU8 index
    let t'5 ← PMem.ldF32 (((this + 32) + ((Int32.toInt64 (((UInt32.toInt32 (UInt8.toUInt32 (t'4))) - (1 : Int32)))) * 24).toUInt64) + 12)
    let t'6 ← PMem.ldU8 index
    let t'7 ← PMem.ldF32 (((this + 32) + ((Int32.toInt64 (((UInt32.toInt32 (UInt8.toUInt32 (t'6))) - (1 : Int32)))) * 24).toUInt64) + 16)
    let t'8 ← PMem.ldU8 index
    let t'9 ← PMem.ldF32 (((this + 32) + ((Int32.toInt64 (((UInt32.toInt32 (UInt8.toUInt32 (t'8))) - (1 : Int32)))) * 24).toUInt64) + 20)
    SCurve.add_segment this index t'3 (0 : Int32) J0 t'5 t'7 t'9
    return ()
  let mut J : Binary32 := J0
  let t'10 ← PMem.ldU8 index
  let t'11 ← PMem.ldF32 (((this + 32) + ((Int32.toInt64 (((UInt32.toInt32 (UInt8.toUInt32 (t'10))) - (1 : Int32)))) * 24).toUInt64) + 8)
  let mut T : Binary32 := (t'11 + tj)
  let t'12 ← PMem.ldU8 index
  let t'13 ← PMem.ldF32 (((this + 32) + ((Int32.toInt64 (((UInt32.toInt32 (UInt8.toUInt32 (t'12))) - (1 : Int32)))) * 24).toUInt64) + 12)
  let mut A : Binary32 := (t'13 + (J0 * tj))
  let t'14 ← PMem.ldU8 index
  let t'15 ← PMem.ldF32 (((this + 32) + ((Int32.toInt64 (((UInt32.toInt32 (UInt8.toUInt32 (t'14))) - (1 : Int32)))) * 24).toUInt64) + 16)
  let t'16 ← PMem.ldU8 index
  let t'17 ← PMem.ldF32 (((this + 32) + ((Int32.toInt64 (((UInt32.toInt32 (UInt8.toUInt32 (t'16))) - (1 : Int32)))) * 24).toUInt64) + 12)
  let t'18 ← sq tj
  let mut V : Binary32 := ((t'15 + (t'17 * tj)) + (((Binary32.ofBits 0x3f000000 /- 1/2 -/) * J0) * t'18))
  let t'19 ← PMem.ldU8 index
  let t'20 ← PMem.ldF32 (((this + 32) + ((Int32.toInt64 (((UInt32.toInt32 (UInt8.toUInt32 (t'19))) - (1 : Int32)))) * 24).toUInt64) + 20)
  let t'21 ← PMem.ldU8 index
  let t'22 ← PMem.ldF32 (((this + 32) + ((Int32.toInt64 (((UInt32.toInt32 (UInt8.toUInt32 (t'21))) - (1 : Int32)))) * 24).toUInt64) + 16)
  let t'23 ← PMem.ldU8 index
  let t'24 ← PMem.ldF32 (((this + 32) + ((Int32.toInt64 (((UInt32.toInt32 (UInt8.toUInt32 (t'23))) - (1 : Int32)))) * 24).toUInt64) + 12)
  let t'25 ← sq tj
  let mut P : Binary32 := (((t'20 + (t'22 * tj)) + (((Binary32.ofBits 0x3f000000 /- 1/2 -/) * t'24) * t'25)) + ((((Binary32.ofBits 0x3f800000 /- 1 -/) / (Binary32.ofBits 0x40c00000 /- 6 -/)) * J0) * (Musl.powf.powf tj (Binary32.ofBits 0x40400000 /- 3 -/))))
  SCurve.add_segment this index T (0 : Int32) J A V P
  return ()

/-- C++ `SCurve::add_segment_incr_jerk : void (uint8_t &, float, float)`, `SCurve.cpp:1114-1138`. -/
def SCurve.add_segment_incr_jerk (this : UInt64) (index : UInt64) (tj : Binary32) (Jm : Binary32) : PMem.M Unit := do
  let mut tj := tj
  let mut Jm := Jm
  let t'1 ← is_positive'float tj
  if !t'1 then
    let t'2 ← PMem.ldU8 index
    let t'3 ← PMem.ldF32 (((this + 32) + ((Int32.toInt64 (((UInt32.toInt32 (UInt8.toUInt32 (t'2))) - (1 : Int32)))) * 24).toUInt64) + 8)
    let t'4 ← PMem.ldU8 index
    let t'5 ← PMem.ldF32 (((this + 32) + ((Int32.toInt64 (((UInt32.toInt32 (UInt8.toUInt32 (t'4))) - (1 : Int32)))) * 24).toUInt64) + 12)
    let t'6 ← PMem.ldU8 index
    let t'7 ← PMem.ldF32 (((this + 32) + ((Int32.toInt64 (((UInt32.toInt32 (UInt8.toUInt32 (t'6))) - (1 : Int32)))) * 24).toUInt64) + 16)
    let t'8 ← PMem.ldU8 index
    let t'9 ← PMem.ldF32 (((this + 32) + ((Int32.toInt64 (((UInt32.toInt32 (UInt8.toUInt32 (t'8))) - (1 : Int32)))) * 24).toUInt64) + 20)
    SCurve.add_segment this index t'3 (0 : Int32) (Binary32.ofBits 0x00000000 /- 0 -/) t'5 t'7 t'9
    return ()
  let mut Beta : Binary32 := ((Binary64.toBinary32 ((Binary64.ofBits 0x400921fb54442d18 /- 31415926535897931/10000000000000000 -/))) / tj)
  let mut Alpha : Binary32 := (Jm * (Binary32.ofBits 0x3f000000 /- 1/2 -/))
  let mut AT : Binary32 := (Alpha * tj)
  let t'10 ← sq tj
  let t'11 ← sq Beta
  let mut VT : Binary32 := (Alpha * ((t'10 * (Binary32.ofBits 0x3f000000 /- 1/2 -/)) - ((Binary32.ofBits 0x40000000 /- 2 -/) / t'11)))
  let t'12 ← sq Beta
  let mut PT : Binary32 := (Alpha * ((((-(Binary32.ofBits 0x3f800000 /- 1 -/)) / t'12) * tj) + (((Binary32.ofBits 0x3f800000 /- 1 -/) / (Binary32.ofBits 0x40c00000 /- 6 -/)) * (Musl.powf.powf tj (Binary32.ofBits 0x40400000 /- 3 -/)))))
  let mut J : Binary32 := Jm
  let t'13 ← PMem.ldU8 index
  let t'14 ← PMem.ldF32 (((this + 32) + ((Int32.toInt64 (((UInt32.toInt32 (UInt8.toUInt32 (t'13))) - (1 : Int32)))) * 24).toUInt64) + 8)
  let mut T : Binary32 := (t'14 + tj)
  let t'15 ← PMem.ldU8 index
  let t'16 ← PMem.ldF32 (((this + 32) + ((Int32.toInt64 (((UInt32.toInt32 (UInt8.toUInt32 (t'15))) - (1 : Int32)))) * 24).toUInt64) + 12)
  let mut A : Binary32 := (t'16 + AT)
  let t'17 ← PMem.ldU8 index
  let t'18 ← PMem.ldF32 (((this + 32) + ((Int32.toInt64 (((UInt32.toInt32 (UInt8.toUInt32 (t'17))) - (1 : Int32)))) * 24).toUInt64) + 16)
  let t'19 ← PMem.ldU8 index
  let t'20 ← PMem.ldF32 (((this + 32) + ((Int32.toInt64 (((UInt32.toInt32 (UInt8.toUInt32 (t'19))) - (1 : Int32)))) * 24).toUInt64) + 12)
  let mut V : Binary32 := ((t'18 + (t'20 * tj)) + VT)
  let t'21 ← PMem.ldU8 index
  let t'22 ← PMem.ldF32 (((this + 32) + ((Int32.toInt64 (((UInt32.toInt32 (UInt8.toUInt32 (t'21))) - (1 : Int32)))) * 24).toUInt64) + 20)
  let t'23 ← PMem.ldU8 index
  let t'24 ← PMem.ldF32 (((this + 32) + ((Int32.toInt64 (((UInt32.toInt32 (UInt8.toUInt32 (t'23))) - (1 : Int32)))) * 24).toUInt64) + 16)
  let t'25 ← PMem.ldU8 index
  let t'26 ← PMem.ldF32 (((this + 32) + ((Int32.toInt64 (((UInt32.toInt32 (UInt8.toUInt32 (t'25))) - (1 : Int32)))) * 24).toUInt64) + 12)
  let t'27 ← sq tj
  let mut P : Binary32 := (((t'22 + (t'24 * tj)) + (((Binary32.ofBits 0x3f000000 /- 1/2 -/) * t'26) * t'27)) + PT)
  SCurve.add_segment this index T (1 : Int32) J A V P
  return ()

/-- C++ `SCurve::add_segment_decr_jerk : void (uint8_t &, float, float)`, `SCurve.cpp:1143-1170`. -/
def SCurve.add_segment_decr_jerk (this : UInt64) (index : UInt64) (tj : Binary32) (Jm : Binary32) : PMem.M Unit := do
  let mut tj := tj
  let mut Jm := Jm
  let t'1 ← is_positive'float tj
  if !t'1 then
    let t'2 ← PMem.ldU8 index
    let t'3 ← PMem.ldF32 (((this + 32) + ((Int32.toInt64 (((UInt32.toInt32 (UInt8.toUInt32 (t'2))) - (1 : Int32)))) * 24).toUInt64) + 8)
    let t'4 ← PMem.ldU8 index
    let t'5 ← PMem.ldF32 (((this + 32) + ((Int32.toInt64 (((UInt32.toInt32 (UInt8.toUInt32 (t'4))) - (1 : Int32)))) * 24).toUInt64) + 12)
    let t'6 ← PMem.ldU8 index
    let t'7 ← PMem.ldF32 (((this + 32) + ((Int32.toInt64 (((UInt32.toInt32 (UInt8.toUInt32 (t'6))) - (1 : Int32)))) * 24).toUInt64) + 16)
    let t'8 ← PMem.ldU8 index
    let t'9 ← PMem.ldF32 (((this + 32) + ((Int32.toInt64 (((UInt32.toInt32 (UInt8.toUInt32 (t'8))) - (1 : Int32)))) * 24).toUInt64) + 20)
    SCurve.add_segment this index t'3 (0 : Int32) (Binary32.ofBits 0x00000000 /- 0 -/) t'5 t'7 t'9
    return ()
  let mut Beta : Binary32 := ((Binary64.toBinary32 ((Binary64.ofBits 0x400921fb54442d18 /- 31415926535897931/10000000000000000 -/))) / tj)
  let mut Alpha : Binary32 := (Jm * (Binary32.ofBits 0x3f000000 /- 1/2 -/))
  let mut AT : Binary32 := (Alpha * tj)
  let t'10 ← sq tj
  let t'11 ← sq Beta
  let mut VT : Binary32 := (Alpha * ((t'10 * (Binary32.ofBits 0x3f000000 /- 1/2 -/)) - ((Binary32.ofBits 0x40000000 /- 2 -/) / t'11)))
  let t'12 ← sq Beta
  let mut PT : Binary32 := (Alpha * ((((-(Binary32.ofBits 0x3f800000 /- 1 -/)) / t'12) * tj) + (((Binary32.ofBits 0x3f800000 /- 1 -/) / (Binary32.ofBits 0x40c00000 /- 6 -/)) * (Musl.powf.powf tj (Binary32.ofBits 0x40400000 /- 3 -/)))))
  let mut A2T : Binary32 := (Jm * tj)
  let t'13 ← sq tj
  let mut V2T : Binary32 := (Jm * t'13)
  let t'14 ← sq Beta
  let mut P2T : Binary32 := (Alpha * (((((-(Binary32.ofBits 0x3f800000 /- 1 -/)) / t'14) * (Binary32.ofBits 0x40000000 /- 2 -/)) * tj) + (((Binary32.ofBits 0x40800000 /- 4 -/) / (Binary32.ofBits 0x40400000 /- 3 -/)) * (Musl.powf.powf tj (Binary32.ofBits 0x40400000 /- 3 -/)))))
  let mut J : Binary32 := Jm
  let t'15 ← PMem.ldU8 index
  let t'16 ← PMem.ldF32 (((this + 32) + ((Int32.toInt64 (((UInt32.toInt32 (UInt8.toUInt32 (t'15))) - (1 : Int32)))) * 24).toUInt64) + 8)
  let mut T : Binary32 := (t'16 + tj)
  let t'17 ← PMem.ldU8 index
  let t'18 ← PMem.ldF32 (((this + 32) + ((Int32.toInt64 (((UInt32.toInt32 (UInt8.toUInt32 (t'17))) - (1 : Int32)))) * 24).toUInt64) + 12)
  let mut A : Binary32 := ((t'18 - AT) + A2T)
  let t'19 ← PMem.ldU8 index
  let t'20 ← PMem.ldF32 (((this + 32) + ((Int32.toInt64 (((UInt32.toInt32 (UInt8.toUInt32 (t'19))) - (1 : Int32)))) * 24).toUInt64) + 16)
  let t'21 ← PMem.ldU8 index
  let t'22 ← PMem.ldF32 (((this + 32) + ((Int32.toInt64 (((UInt32.toInt32 (UInt8.toUInt32 (t'21))) - (1 : Int32)))) * 24).toUInt64) + 12)
  let mut V : Binary32 := (((t'20 - VT) + ((t'22 - AT) * tj)) + V2T)
  let t'23 ← PMem.ldU8 index
  let t'24 ← PMem.ldF32 (((this + 32) + ((Int32.toInt64 (((UInt32.toInt32 (UInt8.toUInt32 (t'23))) - (1 : Int32)))) * 24).toUInt64) + 20)
  let t'25 ← PMem.ldU8 index
  let t'26 ← PMem.ldF32 (((this + 32) + ((Int32.toInt64 (((UInt32.toInt32 (UInt8.toUInt32 (t'25))) - (1 : Int32)))) * 24).toUInt64) + 16)
  let t'27 ← PMem.ldU8 index
  let t'28 ← PMem.ldF32 (((this + 32) + ((Int32.toInt64 (((UInt32.toInt32 (UInt8.toUInt32 (t'27))) - (1 : Int32)))) * 24).toUInt64) + 12)
  let t'29 ← sq tj
  let mut P : Binary32 := ((((t'24 - PT) + ((t'26 - VT) * tj)) + (((Binary32.ofBits 0x3f000000 /- 1/2 -/) * (t'28 - AT)) * t'29)) + P2T)
  SCurve.add_segment this index T (2 : Int32) J A V P
  return ()

/-- C++ `SCurve::add_segments_jerk : void (uint8_t &, float, float, float)`, `SCurve.cpp:1080-1085`. -/
def SCurve.add_segments_jerk (this : UInt64) (index : UInt64) (tj : Binary32) (Jm : Binary32) (Tcj : Binary32) : PMem.M Unit := do
  let mut tj := tj
  let mut Jm := Jm
  let mut Tcj := Tcj
  SCurve.add_segment_incr_jerk this index tj Jm
  SCurve.add_segment_const_jerk this index Tcj Jm
  SCurve.add_segment_decr_jerk this index tj Jm
  return ()

/-- C++ `SCurve::add_segments : void (float)`, `SCurve.cpp:900-931`. -/
def SCurve.add_segments.body (fp : UInt64) (this : UInt64) (L : Binary32) : PMem.M Unit := do
  let mut L := L
  let t'1 ← is_zero L
  if t'1 then
    return ()
  let t'2 ← PMem.ldF32 this
  let t'3 ← PMem.ldF32 (this + 4)
  let t'4 ← PMem.ldF32 (this + 8)
  let t'5 ← PMem.ldF32 (this + 20)
  SCurve.calculate_path t'2 t'3 (Binary32.ofBits 0x00000000 /- 0 -/) t'4 t'5 (L * (Binary32.ofBits 0x3f000000 /- 1/2 -/)) (fp + 0) (fp + 8) (fp + 16) (fp + 24) (fp + 32)
  let t'6 ← PMem.ldF32 (fp + 8)
  let t'7 ← PMem.ldF32 (fp + 0)
  let t'8 ← PMem.ldF32 (fp + 16)
  SCurve.add_segments_jerk this (this + 28) t'6 t'7 t'8
  let t'9 ← PMem.ldF32 (fp + 24)
  SCurve.add_segment_const_jerk this (this + 28) t'9 (Binary32.ofBits 0x00000000 /- 0 -/)
  let t'10 ← PMem.ldF32 (fp + 8)
  let t'11 ← PMem.ldF32 (fp + 0)
  let t'12 ← PMem.ldF32 (fp + 32)
  SCurve.add_segments_jerk this (this + 28) t'10 (-t'11) t'12
  let t'13 := (Binary32.ofBits 0x00000000 /- 0 -/)
  PMem.stF32 (((this + 32) + ((Int32.toInt64 ((7 : Int32))) * 24).toUInt64) + 12) t'13
  for i'14 in [8:15] do
    let i : UInt8 := UInt8.ofNat i'14
    SCurve.add_segment_const_jerk this (this + 28) (Binary32.ofBits 0x00000000 /- 0 -/) (Binary32.ofBits 0x00000000 /- 0 -/)
  PMem.stF32 (fp + 36) (Binary32.ofBits 0x00000000 /- 0 -/)
  let t'15 ← PMem.ldF32 (((this + 32) + ((Int32.toInt64 ((14 : Int32))) * 24).toUInt64) + 20)
  let t'16 ← PMem.ldF32 (((this + 32) + ((Int32.toInt64 ((14 : Int32))) * 24).toUInt64) + 16)
  PMem.stF32 (fp + 40) ((L - ((Binary32.ofBits 0x40000000 /- 2 -/) * t'15)) / t'16)
  let t'17 ← MAX'float_float (fp + 36) (fp + 40)
  let t'18 ← PMem.ldF32 t'17
  let mut t15 : Binary32 := t'18
  SCurve.add_segment_const_jerk this (this + 28) t15 (Binary32.ofBits 0x00000000 /- 0 -/)
  let t'19 ← PMem.ldF32 (fp + 8)
  let t'20 ← PMem.ldF32 (fp + 0)
  let t'21 ← PMem.ldF32 (fp + 32)
  SCurve.add_segments_jerk this (this + 28) t'19 (-t'20) t'21
  let t'22 ← PMem.ldF32 (fp + 24)
  SCurve.add_segment_const_jerk this (this + 28) t'22 (Binary32.ofBits 0x00000000 /- 0 -/)
  let t'23 ← PMem.ldF32 (fp + 8)
  let t'24 ← PMem.ldF32 (fp + 0)
  let t'25 ← PMem.ldF32 (fp + 16)
  SCurve.add_segments_jerk this (this + 28) t'23 t'24 t'25
  let t'26 := (Binary32.ofBits 0x00000000 /- 0 -/)
  PMem.stF32 (((this + 32) + ((Int32.toInt64 ((22 : Int32))) * 24).toUInt64) + 12) t'26
  let t'27 := (Binary32.ofBits 0x00000000 /- 0 -/)
  PMem.stF32 (((this + 32) + ((Int32.toInt64 ((22 : Int32))) * 24).toUInt64) + 16) t'27
  return ()

def SCurve.add_segments (this : UInt64) (L : Binary32) : PMem.M Unit := do
  let fp ← PMem.enter 44
  let r ← SCurve.add_segments.body fp this L
  PMem.leave fp
  return r

/-- C++ `SCurve::generate_path : void (float, float, float, float, float, float, float, float)`, `SCurve.cpp:193-235`. -/
def SCurve.generate_path.body (fp : UInt64) (this : UInt64) (speed_xy : Binary32) (speed_up : Binary32) (speed_down : Binary32) (accel_xy : Binary32) (accel_z : Binary32) (accel_c : Binary32) (snap_maximum : Binary32) (jerk_maximum : Binary32) : PMem.M Unit := do
  PMem.stF32 (fp + 0) speed_xy
  let mut speed_up := speed_up
  let mut speed_down := speed_down
  PMem.stF32 (fp + 4) accel_xy
  let mut accel_z := accel_z
  PMem.stF32 (fp + 8) accel_c
  let mut snap_maximum := snap_maximum
  let mut jerk_maximum := jerk_maximum
  let t'1 ← PMem.ldB (this + 584)
  if t'1 then
    let t'2 ← PMem.ldF32 (fp + 8)
    let t'3 ← is_positive'float t'2
    let mut c'4 : Binary32 := default
    if t'3 then
      let t'5 ← PMem.ldF32 (fp + 8)
      c'4 := t'5
    else
      let t'6 ← PMem.ldF32 (fp + 4)
      c'4 := t'6
    PMem.stF32 (this + 12) c'4
    let t'7 ← PMem.ldF32 (this + 12)
    let t'8 ← PMem.ldF32 ((this + 604) + 8)
    let t'9 ← safe_sqrt'float (t'7 * t'8)
    PMem.stF32 (fp + 12) t'9
    let t'10 ← MIN'float_float (fp + 0) (fp + 12)
    let t'11 ← PMem.ldF32 t'10
    PMem.stF32 (fp + 0) t'11
  PMem.stF32 this snap_maximum
  PMem.stF32 (this + 4) jerk_maximum
  let t'12 ← PMem.ldF32 ((this + 604) + 4)
  let t'13 ← PMem.ldF32 ((this + 588) + 8)
  let t'14 ← PMem.ldF32 (fp + 0)
  let t'15 ← kinematic_limit t'12 t'13 t'14 speed_up speed_down
  PMem.stF32 (this + 20) t'15
  let t'16 ← PMem.ldF32 ((this + 604) + 4)
  let t'17 ← PMem.ldF32 ((this + 588) + 8)
  let t'18 ← PMem.ldF32 (fp + 4)
  let t'19 ← kinematic_limit t'16 t'17 t'18 accel_z accel_z
  PMem.stF32 (this + 8) t'19
  PMem.stF32 (this + 16) accel_z
  let t'20 ← PMem.ldF32 this
  let t'21 ← is_positive'float t'20
  let mut sc'24 := !t'21
  if !sc'24 then
    let t'22 ← PMem.ldF32 (this + 4)
    let t'23 ← is_positive'float t'22
    sc'24 := !t'23
  let mut sc'27 := sc'24
  if !sc'27 then
    let t'25 ← PMem.ldF32 (this + 8)
    let t'26 ← is_positive'float t'25
    sc'27 := !t'26
  let mut sc'30 := sc'27
  if !sc'30 then
    let t'28 ← PMem.ldF32 (this + 20)
    let t'29 ← is_positive'float t'28
    sc'30 := !t'29
  if sc'30 then
    SCurve.init this
    return ()
  let t'31 ← PMem.ldF32 (this + 600)
  SCurve.add_segments this t'31
  let t'32 ← SCurve.valid this
  if !t'32 then
    SCurve.debug this
    SCurve.init this
  return ()

def SCurve.generate_path (this : UInt64) (speed_xy : Binary32) (speed_up : Binary32) (speed_down : Binary32) (accel_xy : Binary32) (accel_z : Binary32) (accel_c : Binary32) (snap_maximum : Binary32) (jerk_maximum : Binary32) : PMem.M Unit := do
  let fp ← PMem.enter 16
  let r ← SCurve.generate_path.body fp this speed_xy speed_up speed_down accel_xy accel_z accel_c snap_maximum jerk_maximum
  PMem.leave fp
  return r

/-- C++ `SCurve::calculate_track : void (const Vector3p &, const Vector3p &, float, float, float, float, float, float, float, float, float)`, `SCurve.cpp:65-109`. -/
def SCurve.calculate_track.body (fp : UInt64) (this : UInt64) (origin : UInt64) (destination : UInt64) (arc_ang_rad : Binary32) (speed_xy : Binary32) (speed_up : Binary32) (speed_down : Binary32) (accel_xy : Binary32) (accel_z : Binary32) (accel_c : Binary32) (snap_maximum : Binary32) (jerk_maximum : Binary32) : PMem.M Unit := do
  let mut arc_ang_rad := arc_ang_rad
  let mut speed_xy := speed_xy
  let mut speed_up := speed_up
  let mut speed_down := speed_down
  let mut accel_xy := accel_xy
  let mut accel_z := accel_z
  let mut accel_c := accel_c
  let mut snap_maximum := snap_maximum
  let mut jerk_maximum := jerk_maximum
  SCurve.init this
  let t'1 := (Binary32.abs speed_xy)
  speed_xy := t'1
  let t'2 := (Binary32.abs speed_up)
  speed_up := t'2
  let t'3 := (Binary32.abs speed_down)
  speed_down := t'3
  let t'4 := (Binary32.abs accel_xy)
  accel_xy := t'4
  let t'5 := (Binary32.abs accel_z)
  accel_z := t'5
  Vector3'double.operator_ destination (fp + 0) origin
  let t'6 := (fp + 0)
  Vector3'double.tofloat t'6 (fp + 24)
  let t'7 := (fp + 24)
  discard <| PMem.memcpy (this + 588) t'7 12
  discard <| pure ((this + 588))
  let t'8 ← Vector3'float.is_zero (this + 588)
  let mut sc'11 := t'8
  if !sc'11 then
    let t'9 ← Vector3'float.length_squared (this + 588)
    let t'10 ← is_zero t'9
    sc'11 := t'10
  if sc'11 then
    Vector3'float.zero (this + 588)
    return ()
  let t'12 ← Vector3'float.xy (this + 588)
  Vector2'float.Vector2'4 (fp + 40) t'12
  let t'13 ← Vector2'float.length (fp + 40)
  let mut chord_length : Binary32 := t'13
  let t'14 ← is_positive'float chord_length
  let mut sc'17 := !t'14
  if !sc'17 then
    let t'15 ← wrap_PI'float arc_ang_rad
    let t'16 ← radians (Binary32.ofBits 0x3f800000 /- 1 -/)
    sc'17 := (decide ((Binary32.abs t'15) < t'16))
  if sc'17 then
    SCurve.set_straight_geometry this
  else
    let mut radius : Binary32 := (Binary32.abs (chord_length / ((Binary32.ofBits 0x40000000 /- 2 -/) * (Binary32.abs (Musl.sinf.sinf (arc_ang_rad * (Binary32.ofBits 0x3f000000 /- 1/2 -/)))))))
    let t'18 ← sq radius
    let t'19 ← sq (chord_length * (Binary32.ofBits 0x3f000000 /- 1/2 -/))
    let t'20 ← safe_sqrt'float (t'18 - t'19)
    let mut center_offset : Binary32 := t'20
    let t'21 ← is_negative'float arc_ang_rad
    let mut c'22 : Binary32 := default
    if t'21 then
      c'22 := -(Binary32.ofBits 0x3f800000 /- 1 -/)
    else
      c'22 := (Binary32.ofBits 0x3f800000 /- 1 -/)
    let mut turn_dir : Binary32 := c'22
    let t'23 ← wrap_PI'float (Binary32.abs arc_ang_rad)
    let t'24 ← is_positive'float t'23
    let mut c'25 : Binary32 := default
    if t'24 then
      c'25 := (Binary32.ofBits 0x3f800000 /- 1 -/)
    else
      c'25 := -(Binary32.ofBits 0x3f800000 /- 1 -/)
    let mut center_side : Binary32 := c'25
    Vector2'float.operator_'2 (fp + 40) (fp + 56) (Binary32.ofBits 0x3f000000 /- 1/2 -/)
    let t'26 := (fp + 56)
    let t'27 ← PMem.ldF32 ((fp + 40) + 4)
    let t'28 ← PMem.ldF32 (fp + 40)
    Vector2'float.Vector2'2 (fp + 64) (-t'27) t'28
    Vector2'float.operator_'2 (fp + 64) (fp + 72) (((center_side * turn_dir) * center_offset) / chord_length)
    let t'29 := (fp + 72)
    Vector2'float.operator_'3 t'26 (fp + 80) t'29
    let t'30 := (fp + 80)
    Vector2'float.Vector2'3 (fp + 48) t'30
    SCurve.set_arc_geometry this (fp + 48) radius arc_ang_rad
  let t'31 ← PMem.ldF32 (this + 600)
  let t'32 ← is_zero t'31
  if t'32 then
    Vector3'float.zero (this + 588)
    return ()
  SCurve.generate_path this speed_xy speed_up speed_down accel_xy accel_z accel_c snap_maximum jerk_maximum
  return ()

def SCurve.calculate_track (this : UInt64) (origin : UInt64) (destination : UInt64) (arc_ang_rad : Binary32) (speed_xy : Binary32) (speed_up : Binary32) (speed_down : Binary32) (accel_xy : Binary32) (accel_z : Binary32) (accel_c : Binary32) (snap_maximum : Binary32) (jerk_maximum : Binary32) : PMem.M Unit := do
  let fp ← PMem.enter 88
  let r ← SCurve.calculate_track.body fp this origin destination arc_ang_rad speed_xy speed_up speed_down accel_xy accel_z accel_c snap_maximum jerk_maximum
  PMem.leave fp
  return r

/-- C++ `SCurve::fill_empty_segments : void (uint8_t, uint8_t, uint8_t)`, `SCurve.cpp:1184-1194`. -/
def SCurve.fill_empty_segments (this : UInt64) (first : UInt8) (last : UInt8) (src : UInt8) : PMem.M Unit := do
  let mut first := first
  let mut last := last
  let mut src := src
  let mut i : UInt8 := first
  let mut first'1 := true
  for _ in PMem.loopFuel do
    if !first'1 then
      let t'2 := i
      let t'3 := (t'2 + 1)
      i := t'3
      pure ()
    first'1 := false
    if !((decide ((UInt32.toInt32 (UInt8.toUInt32 (i))) ≤ (UInt32.toInt32 (UInt8.toUInt32 (last)))))) then break
    PMem.stI32 (((this + 32) + ((UInt64.toInt64 (UInt8.toUInt64 (i))) * 24).toUInt64) + 4) (0 : Int32)
    let t'4 := (Binary32.ofBits 0x00000000 /- 0 -/)
    PMem.stF32 ((this + 32) + ((UInt64.toInt64 (UInt8.toUInt64 (i))) * 24).toUInt64) t'4
    let t'5 ← PMem.ldF32 (((this + 32) + ((UInt64.toInt64 (UInt8.toUInt64 (src))) * 24).toUInt64) + 8)
    PMem.stF32 (((this + 32) + ((UInt64.toInt64 (UInt8.toUInt64 (i))) * 24).toUInt64) + 8) t'5
    let t'6 := (Binary32.ofBits 0x00000000 /- 0 -/)
    PMem.stF32 (((this + 32) + ((UInt64.toInt64 (UInt8.toUInt64 (i))) * 24).toUInt64) + 12) t'6
    let t'7 ← PMem.ldF32 (((this + 32) + ((UInt64.toInt64 (UInt8.toUInt64 (src))) * 24).toUInt64) + 16)
    PMem.stF32 (((this + 32) + ((UInt64.toInt64 (UInt8.toUInt64 (i))) * 24).toUInt64) + 16) t'7
    let t'8 ← PMem.ldF32 (((this + 32) + ((UInt64.toInt64 (UInt8.toUInt64 (src))) * 24).toUInt64) + 20)
    PMem.stF32 (((this + 32) + ((UInt64.toInt64 (UInt8.toUInt64 (i))) * 24).toUInt64) + 20) t'8
  return ()

/-- C++ `SCurve::extend_const_vel_to : void (float)`, `SCurve.cpp:1173-1181`. -/
def SCurve.extend_const_vel_to.body (fp : UInt64) (this : UInt64) (target_pos : Binary32) : PMem.M Unit := do
  let mut target_pos := target_pos
  PMem.stF32 (fp + 0) (Binary32.ofBits 0x00000000 /- 0 -/)
  let t'1 ← PMem.ldF32 (((this + 32) + ((Int32.toInt64 ((22 : Int32))) * 24).toUInt64) + 20)
  PMem.stF32 (fp + 4) (target_pos - t'1)
  let t'2 ← MAX'float_float (fp + 0) (fp + 4)
  let t'3 ← PMem.ldF32 t'2
  let mut dP : Binary32 := t'3
  let t'4 ← PMem.ldF32 (((this + 32) + ((Int32.toInt64 ((15 : Int32))) * 24).toUInt64) + 16)
  let t'5 ← is_positive'float t'4
  let mut c'6 : Binary32 := default
  if t'5 then
    let t'7 ← PMem.ldF32 (((this + 32) + ((Int32.toInt64 ((15 : Int32))) * 24).toUInt64) + 16)
    c'6 := (dP / t'7)
  else
    c'6 := (Binary32.ofBits 0x00000000 /- 0 -/)
  let mut t15 : Binary32 := c'6
  for i'8 in [15:23] do
    let i : UInt8 := UInt8.ofNat i'8
    let t'9 := (((this + 32) + ((UInt64.toInt64 (UInt8.toUInt64 (i))) * 24).toUInt64) + 8)
    let t'10 ← PMem.ldF32 t'9
    let t'11 := (t'10 + t15)
    PMem.stF32 t'9 t'11
    let t'12 := (((this + 32) + ((UInt64.toInt64 (UInt8.toUInt64 (i))) * 24).toUInt64) + 20)
    let t'13 ← PMem.ldF32 t'12
    let t'14 := (t'13 + dP)
    PMem.stF32 t'12 t'14
  return ()

def SCurve.extend_const_vel_to (this : UInt64) (target_pos : Binary32) : PMem.M Unit := do
  let fp ← PMem.enter 8
  let r ← SCurve.extend_const_vel_to.body fp this target_pos
  PMem.leave fp
  return r

/-- C++ `SCurve::set_origin_speed_max : float (float)`, `SCurve.cpp:444-513`. -/
def SCurve.set_origin_speed_max.body (fp : UInt64) (this : UInt64) (speed : Binary32) : PMem.M Binary32 := do
  PMem.stF32 (fp + 0) speed
  let t'1 ← PMem.ldU8 (this + 28)
  if ((UInt32.toInt32 (UInt8.toUInt32 (t'1))) != (UInt32.toInt32 (UInt8.toUInt32 ((23 : UInt8))))) then
    return (Binary32.ofBits 0x00000000 /- 0 -/)
  let t'2 ← PMem.ldF32 (fp + 0)
  let t'3 := (Binary32.abs t'2)
  PMem.stF32 (fp + 0) t'3
  let t'4 ← PMem.ldF32 (((this + 32) + ((Int32.toInt64 ((0 : Int32))) * 24).toUInt64) + 16)
  let t'5 ← PMem.ldF32 (fp + 0)
  let t'6 ← is_equal'float_float t'4 t'5
  if t'6 then
    let t'7 ← PMem.ldF32 (fp + 0)
    return t'7
  let t'8 ← PMem.ldF32 (((this + 32) + ((Int32.toInt64 ((7 : Int32))) * 24).toUInt64) + 16)
  PMem.stF32 (fp + 8) t'8
  let t'9 ← MIN'float_float (fp + 0) (fp + 8)
  let t'10 ← PMem.ldF32 t'9
  PMem.stF32 (fp + 0) t'10
  let t'11 ← PMem.ldF32 this
  let t'12 ← PMem.ldF32 (this + 4)
  let t'13 ← PMem.ldF32 (fp + 0)
  let t'14 ← PMem.ldF32 (this + 8)
  let t'15 ← PMem.ldF32 (fp + 8)
  let t'16 ← PMem.ldF32 (this + 600)
  SCurve.calculate_path t'11 t'12 t'13 t'14 t'15 (t'16 * (Binary32.ofBits 0x3f000000 /- 1/2 -/)) (fp + 16) (fp + 24) (fp + 32) (fp + 40) (fp + 48)
  PMem.stU8 (fp + 56) (Int8.toUInt8 (Int32.toInt8 ((0 : Int32))))
  let t'17 ← PMem.ldF32 (fp + 0)
  SCurve.add_segment this (fp + 56) (Binary32.ofBits 0x00000000 /- 0 -/) (0 : Int32) (Binary32.ofBits 0x00000000 /- 0 -/) (Binary32.ofBits 0x00000000 /- 0 -/) t'17 (Binary32.ofBits 0x00000000 /- 0 -/)
  let t'18 ← PMem.ldF32 (fp + 24)
  let t'19 ← PMem.ldF32 (fp + 16)
  let t'20 ← PMem.ldF32 (fp + 32)
  SCurve.add_segments_jerk this (fp + 56) t'18 t'19 t'20
  let t'21 ← PMem.ldF32 (fp + 40)
  SCurve.add_segment_const_jerk this (fp + 56) t'21 (Binary32.ofBits 0x00000000 /- 0 -/)
  let t'22 ← PMem.ldF32 (fp + 24)
  let t'23 ← PMem.ldF32 (fp + 16)
  let t'24 ← PMem.ldF32 (fp + 48)
  SCurve.add_segments_jerk this (fp + 56) t'22 (-t'23) t'24
  let t'25 := (Binary32.ofBits 0x00000000 /- 0 -/)
  PMem.stF32 (((this + 32) + ((Int32.toInt64 ((7 : Int32))) * 24).toUInt64) + 12) t'25
  PMem.stF32 (fp + 60) (Binary32.ofBits 0x00000000 /- 0 -/)
  let t'26 ← PMem.ldF32 (this + 600)
  let t'27 ← PMem.ldF32 (((this + 32) + ((Int32.toInt64 ((7 : Int32))) * 24).toUInt64) + 20)
  PMem.stF32 (fp + 64) ((t'26 * (Binary32.ofBits 0x3f000000 /- 1/2 -/)) - t'27)
  let t'28 ← MIN'float_float (fp + 60) (fp + 64)
  let t'29 ← PMem.ldF32 t'28
  let mut dPstart : Binary32 := t'29
  let t'30 ← PMem.ldF32 (((this + 32) + ((Int32.toInt64 ((7 : Int32))) * 24).toUInt64) + 16)
  let mut dt : Binary32 := (dPstart / t'30)
  for i'31 in [0:8] do
    let i : UInt8 := UInt8.ofNat i'31
    let t'32 := (((this + 32) + ((UInt64.toInt64 (UInt8.toUInt64 (i))) * 24).toUInt64) + 8)
    let t'33 ← PMem.ldF32 t'32
    let t'34 := (t'33 + dt)
    PMem.stF32 t'32 t'34
    let t'35 := (((this + 32) + ((UInt64.toInt64 (UInt8.toUInt64 (i))) * 24).toUInt64) + 20)
    let t'36 ← PMem.ldF32 t'35
    let t'37 := (t'36 + dPstart)
    PMem.stF32 t'35 t'37
  SCurve.fill_empty_segments this (Int8.toUInt8 (Int32.toInt8 (((7 : Int32) + (1 : Int32))))) (Int8.toUInt8 (Int32.toInt8 ((14 : Int32)))) (Int8.toUInt8 (Int32.toInt8 ((7 : Int32))))
  let t'38 := Int8.toUInt8 (Int32.toInt8 ((15 : Int32)))
  PMem.stU8 (fp + 56) t'38
  SCurve.add_segment_const_jerk this (fp + 56) (Binary32.ofBits 0x00000000 /- 0 -/) (Binary32.ofBits 0x00000000 /- 0 -/)
  let t'39 ← PMem.ldF32 this
  let t'40 ← PMem.ldF32 (this + 4)
  let t'41 ← PMem.ldF32 (this + 8)
  let t'42 ← PMem.ldF32 (((this + 32) + ((Int32.toInt64 ((15 : Int32))) * 24).toUInt64) + 16)
  let t'43 ← PMem.ldF32 (this + 600)
  SCurve.calculate_path t'39 t'40 (Binary32.ofBits 0x00000000 /- 0 -/) t'41 t'42 (t'43 * (Binary32.ofBits 0x3f000000 /- 1/2 -/)) (fp + 16) (fp + 24) (fp + 32) (fp + 40) (fp + 48)
  let t'44 ← PMem.ldF32 (fp + 24)
  let t'45 ← PMem.ldF32 (fp + 16)
  let t'46 ← PMem.ldF32 (fp + 48)
  SCurve.add_segments_jerk this (fp + 56) t'44 (-t'45) t'46
  let t'47 ← PMem.ldF32 (fp + 40)
  SCurve.add_segment_const_jerk this (fp + 56) t'47 (Binary32.ofBits 0x00000000 /- 0 -/)
  let t'48 ← PMem.ldF32 (fp + 24)
  let t'49 ← PMem.ldF32 (fp + 16)
  let t'50 ← PMem.ldF32 (fp + 32)
  SCurve.add_segments_jerk this (fp + 56) t'48 t'49 t'50
  let t'51 := (Binary32.ofBits 0x00000000 /- 0 -/)
  PMem.stF32 (((this + 32) + ((Int32.toInt64 ((22 : Int32))) * 24).toUInt64) + 12) t'51
  PMem.stF32 (fp + 68) (Binary32.ofBits 0x00000000 /- 0 -/)
  let t'52 ← MAX'float_float (fp + 68) (((this + 32) + ((Int32.toInt64 ((22 : Int32))) * 24).toUInt64) + 16)
  let t'53 ← PMem.ldF32 t'52
  PMem.stF32 (((this + 32) + ((Int32.toInt64 ((22 : Int32))) * 24).toUInt64) + 16) t'53
  let t'54 ← PMem.ldF32 (this + 600)
  SCurve.extend_const_vel_to this t'54
  let t'55 ← SCurve.valid this
  if !t'55 then
    SCurve.debug this
    SCurve.init this
    return (Binary32.ofBits 0x00000000 /- 0 -/)
  let t'56 ← PMem.ldF32 (fp + 0)
  return t'56

def SCurve.set_origin_speed_max (this : UInt64) (speed : Binary32) : PMem.M Binary32 := do
  let fp ← PMem.enter 72
  let r ← SCurve.set_origin_speed_max.body fp this speed
  PMem.leave fp
  return r

/-- C++ `check_lat : bool (int32_t)`, `location.cpp:47-50`. -/
def check_lat (lat : Int32) : PMem.M Bool := do
  let mut lat := lat
  let t'1 ← PMem.labs (Int32.toInt64 (lat))
  return (decide ((Int64.toBinary32 (t'1)) ≤ ((Int32.toBinary32 ((90 : Int32))) * (Binary64.toBinary32 ((Binary64.ofBits 0x416312d000000000 /- 10000000 -/))))))

/-- C++ `check_lng : bool (int32_t)`, `location.cpp:51-54`. -/
def check_lng (lng : Int32) : PMem.M Bool := do
  let mut lng := lng
  let t'1 ← PMem.labs (Int32.toInt64 (lng))
  return (decide ((Int64.toBinary32 (t'1)) ≤ ((Int32.toBinary32 ((180 : Int32))) * (Binary64.toBinary32 ((Binary64.ofBits 0x416312d000000000 /- 10000000 -/))))))

/-- C++ `check_latlng : bool (int32_t, int32_t)`, `location.cpp:59-62`. -/
def check_latlng (lat : Int32) (lng : Int32) : PMem.M Bool := do
  let mut lat := lat
  let mut lng := lng
  let t'1 ← check_lat lat
  let mut sc'3 := t'1
  if sc'3 then
    let t'2 ← check_lng lng
    sc'3 := t'2
  return sc'3

/-- C++ `MAX : auto (const double &, const float &) -> decltype(one > two ? one : two)`, `AP_Math.h:307-310`. -/
def MAX'double_float (one : UInt64) (two : UInt64) : PMem.M Binary64 := do
  let t'1 ← PMem.ldF64 one
  let t'2 ← PMem.ldF32 two
  let mut c'3 : Binary64 := default
  if (decide (t'1 > (Binary32.toBinary64 (t'2)))) then
    let t'4 ← PMem.ldF64 one
    c'3 := t'4
  else
    let t'5 ← PMem.ldF32 two
    c'3 := Binary32.toBinary64 (t'5)
  return c'3

/-- C++ `Vector3<double>::operator*= : Vector3<double> &(const double)`, `vector3.cpp:343-347`. -/
def Vector3'double.operator__'2 (this : UInt64) (num : Binary64) : PMem.M UInt64 := do
  let mut num := num
  let t'1 ← PMem.ldF64 this
  let t'2 := (t'1 * num)
  PMem.stF64 this t'2
  let t'3 := (this + 8)
  let t'4 ← PMem.ldF64 t'3
  let t'5 := (t'4 * num)
  PMem.stF64 t'3 t'5
  let t'6 := (this + 16)
  let t'7 ← PMem.ldF64 t'6
  let t'8 := (t'7 * num)
  PMem.stF64 t'6 t'8
  return this

/-- C++ `Vector2<double>::Vector2 : void ()`, `vector2.h:50-52`. -/
def Vector2'double.Vector2'3 (this : UInt64) : PMem.M Unit := do
  PMem.stF64 (this + 0) (Int32.toBinary64 ((0 : Int32)))
  PMem.stF64 (this + 8) (Int32.toBinary64 ((0 : Int32)))
  return ()

/-- C++ `Vector2<double>::operator*= : Vector2<double> &(const double)`, `vector2.cpp:63-67`. -/
def Vector2'double.operator__'3 (this : UInt64) (num : Binary64) : PMem.M UInt64 := do
  let mut num := num
  let t'1 ← PMem.ldF64 this
  let t'2 := (t'1 * num)
  PMem.stF64 this t'2
  let t'3 := (this + 8)
  let t'4 ← PMem.ldF64 t'3
  let t'5 := (t'4 * num)
  PMem.stF64 t'3 t'5
  return this

/-- C++ `MAX : auto (const int &, const float &) -> decltype(one > two ? one : two)`, `AP_Math.h:307-310`. -/
def MAX'int_float (one : UInt64) (two : UInt64) : PMem.M Binary32 := do
  let t'1 ← PMem.ldI32 one
  let t'2 ← PMem.ldF32 two
  let mut c'3 : Binary32 := default
  if (decide ((Int32.toBinary32 (t'1)) > t'2)) then
    let t'4 ← PMem.ldI32 one
    c'3 := Int32.toBinary32 (t'4)
  else
    let t'5 ← PMem.ldF32 two
    c'3 := t'5
  return c'3

/-- C++ `Vector3<float>::operator* : Vector3<float> (const float) const`, `vector3.cpp:389-392`. -/
def Vector3'float.operator_.body (fp : UInt64) (this : UInt64) (sret : UInt64) (num : Binary32) : PMem.M Unit := do
  let mut num := num
  let t'1 ← PMem.ldF32 this
  let t'2 ← PMem.ldF32 (this + 4)
  let t'3 ← PMem.ldF32 (this + 8)
  Vector3'float.Vector3 (fp + 0) (t'1 * num) (t'2 * num) (t'3 * num)
  Vector3'float.Vector3'3 sret (fp + 0)
  return ()

def Vector3'float.operator_ (this : UInt64) (sret : UInt64) (num : Binary32) : PMem.M Unit := do
  let fp ← PMem.enter 12
  let r ← Vector3'float.operator_.body fp this sret num
  PMem.leave fp
  return r

/-- C++ `Vector3<float>::operator/ : Vector3<float> (const float) const`, `vector3.cpp:383-386`. -/
def Vector3'float.operator_'3.body (fp : UInt64) (this : UInt64) (sret : UInt64) (num : Binary32) : PMem.M Unit := do
  let mut num := num
  let t'1 ← PMem.ldF32 this
  let t'2 ← PMem.ldF32 (this + 4)
  let t'3 ← PMem.ldF32 (this + 8)
  Vector3'float.Vector3 (fp + 0) (t'1 / num) (t'2 / num) (t'3 / num)
  Vector3'float.Vector3'3 sret (fp + 0)
  return ()

def Vector3'float.operator_'3 (this : UInt64) (sret : UInt64) (num : Binary32) : PMem.M Unit := do
  let fp ← PMem.enter 12
  let r ← Vector3'float.operator_'3.body fp this sret num
  PMem.leave fp
  return r

/-- C++ `Vector3<float>::projected : Vector3<float> (const Vector3<float> &) const`, `vector3.h:255-258`. -/
def Vector3'float.projected.body (fp : UInt64) (this : UInt64) (sret : UInt64) (v : UInt64) : PMem.M Unit := do
  let t'1 ← Vector3'float.operator_'4 this v
  Vector3'float.operator_ v (fp + 0) t'1
  let t'2 := (fp + 0)
  let t'3 ← Vector3'float.operator_'4 v v
  Vector3'float.operator_'3 t'2 (fp + 16) t'3
  let t'4 := (fp + 16)
  Vector3'float.Vector3'3 sret t'4
  return ()

def Vector3'float.projected (this : UInt64) (sret : UInt64) (v : UInt64) : PMem.M Unit := do
  let fp ← PMem.enter 28
  let r ← Vector3'float.projected.body fp this sret v
  PMem.leave fp
  return r

/-- C++ `MIN : auto (const int &, const float &) -> decltype(one < two ? one : two)`, `AP_Math.h:300-303`. -/
def MIN'int_float (one : UInt64) (two : UInt64) : PMem.M Binary32 := do
  let t'1 ← PMem.ldI32 one
  let t'2 ← PMem.ldF32 two
  let mut c'3 : Binary32 := default
  if (decide ((Int32.toBinary32 (t'1)) < t'2)) then
    let t'4 ← PMem.ldI32 one
    c'3 := Int32.toBinary32 (t'4)
  else
    let t'5 ← PMem.ldF32 two
    c'3 := t'5
  return c'3

/-- C++ `Vector3<float>::operator- : Vector3<float> (const Vector3<float> &) const`, `vector3.cpp:395-398`. -/
def Vector3'float.operator_'2.body (fp : UInt64) (this : UInt64) (sret : UInt64) (v : UInt64) : PMem.M Unit := do
  let t'1 ← PMem.ldF32 this
  let t'2 ← PMem.ldF32 v
  let t'3 ← PMem.ldF32 (this + 4)
  let t'4 ← PMem.ldF32 (v + 4)
  let t'5 ← PMem.ldF32 (this + 8)
  let t'6 ← PMem.ldF32 (v + 8)
  Vector3'float.Vector3 (fp + 0) (t'1 - t'2) (t'3 - t'4) (t'5 - t'6)
  Vector3'float.Vector3'3 sret (fp + 0)
  return ()

def Vector3'float.operator_'2 (this : UInt64) (sret : UInt64) (v : UInt64) : PMem.M Unit := do
  let fp ← PMem.enter 12
  let r ← Vector3'float.operator_'2.body fp this sret v
  PMem.leave fp
  return r

/-- `sq'double` as a pure function of its arguments (it reads and writes no memory). -/
def sq'double.pure' (val : Binary64) : Id Binary64 := do
  let mut val := val
  let mut v : Binary64 := val
  return (v * v)

/-- C++ `sq : ftype (const double)`, `AP_Math.h:?-265`. -/
def sq'double (val : Binary64) : PMem.M Binary64 :=
  pure (_root_.Vehicle_lib.sq'double.pure' val)

/-- `sq'double_double` as a pure function of its arguments (it reads and writes no memory). -/
def sq'double_double.pure' (first : Binary64) (parameters : Binary64) : Id Binary64 := do
  let mut first := first
  let mut parameters := parameters
  let t'1 ← _root_.Vehicle_lib.sq'double.pure' first
  let t'2 ← _root_.Vehicle_lib.sq'double.pure' parameters
  return (t'1 + t'2)

/-- C++ `sq : ftype (const double, const double)`, `AP_Math.h:?-279`. -/
def sq'double_double (first : Binary64) (parameters : Binary64) : PMem.M Binary64 :=
  pure (_root_.Vehicle_lib.sq'double_double.pure' first parameters)

/-- `norm'double_double` as a pure function of its arguments (it reads and writes no memory). -/
def norm'double_double.pure' (first : Binary64) (second : Binary64) : Id Binary64 := do
  let mut first := first
  let mut second := second
  let t'1 ← _root_.Vehicle_lib.sq'double_double.pure' first second
  return (Binary64.sqrt t'1)

/-- C++ `norm : ftype (const double, const double)`, `ftype.h:?-289`. -/
def norm'double_double (first : Binary64) (second : Binary64) : PMem.M Binary64 :=
  pure (_root_.Vehicle_lib.norm'double_double.pure' first second)

/-- C++ `rc_input_to_roll_pitch_rad : void (float, float, float, float, float &, float &)`, `control.cpp:856-876`. -/
def rc_input_to_roll_pitch_rad.body (fp : UInt64) (roll_in_norm : Binary32) (pitch_in_norm : Binary32) (angle_max_rad : Binary32) (angle_limit_rad : Binary32) (roll_out_rad : UInt64) (pitch_out_rad : UInt64) : PMem.M Unit := do
  let mut roll_in_norm := roll_in_norm
  let mut pitch_in_norm := pitch_in_norm
  PMem.stF32 (fp + 0) angle_max_rad
  let mut angle_limit_rad := angle_limit_rad
  let t'1 ← radians (Binary64.toBinary32 ((Binary64.ofBits 0x4055400000000000 /- 85 -/)))
  PMem.stF32 (fp + 4) t'1
  let t'2 ← MIN'float_float (fp + 0) (fp + 4)
  let t'3 ← PMem.ldF32 t'2
  PMem.stF32 (fp + 0) t'3
  Vector2'float.Vector2 (fp + 8)
  let t'4 ← PMem.ldF32 (fp + 0)
  let t'5 := -(Musl.tanf.tanf (t'4 * pitch_in_norm))
  PMem.stF32 (fp + 8) t'5
  let t'6 ← PMem.ldF32 (fp + 0)
  let t'7 := (Musl.tanf.tanf (t'6 * roll_in_norm))
  PMem.stF32 ((fp + 8) + 4) t'7
  let t'8 ← radians (Binary64.toBinary32 ((Binary64.ofBits 0x4024000000000000 /- 10 -/)))
  let t'9 ← PMem.ldF32 (fp + 0)
  let t'10 ← constrain_value_line'float angle_limit_rad t'8 t'9 (Int32.toUInt32 ((867 : Int32)))
  angle_limit_rad := t'10
  let mut thrust_limit : Binary32 := (Musl.tanf.tanf angle_limit_rad)
  let t'11 ← Vector2'float.limit_length (fp + 8) thrust_limit
  discard <| pure (t'11)
  let t'12 ← PMem.ldF32 (fp + 8)
  let t'13 := -(Musl.atanf.atanf t'12)
  PMem.stF32 pitch_out_rad t'13
  let t'14 ← PMem.ldF32 pitch_out_rad
  let t'15 ← PMem.ldF32 ((fp + 8) + 4)
  let t'16 := (Musl.atanf.atanf ((Musl.cosf.cosf t'14) * t'15))
  PMem.stF32 roll_out_rad t'16
  return ()

def rc_input_to_roll_pitch_rad (roll_in_norm : Binary32) (pitch_in_norm : Binary32) (angle_max_rad : Binary32) (angle_limit_rad : Binary32) (roll_out_rad : UInt64) (pitch_out_rad : UInt64) : PMem.M Unit := do
  let fp ← PMem.enter 16
  let r ← rc_input_to_roll_pitch_rad.body fp roll_in_norm pitch_in_norm angle_max_rad angle_limit_rad roll_out_rad pitch_out_rad
  PMem.leave fp
  return r

/-- C++ `MAX : auto (const int &, const int &) -> decltype(one > two ? one : two)`, `AP_Math.h:307-310`. -/
def MAX'int_int (one : UInt64) (two : UInt64) : PMem.M UInt64 := do
  let t'1 ← PMem.ldI32 one
  let t'2 ← PMem.ldI32 two
  let mut c'3 : UInt64 := 0
  if (decide (t'1 > t'2)) then
    c'3 := one
  else
    c'3 := two
  return c'3

/-- C++ `Matrix3<float>::operator* : Vector3<float> (const Vector3<float> &) const`, `matrix3.cpp:146-151`. -/
def Matrix3'float.operator_.body (fp : UInt64) (this : UInt64) (sret : UInt64) (v : UInt64) : PMem.M Unit := do
  let t'1 ← PMem.ldF32 this
  let t'2 ← PMem.ldF32 v
  let t'3 ← PMem.ldF32 (this + 4)
  let t'4 ← PMem.ldF32 (v + 4)
  let t'5 ← PMem.ldF32 (this + 8)
  let t'6 ← PMem.ldF32 (v + 8)
  let t'7 ← PMem.ldF32 (this + 12)
  let t'8 ← PMem.ldF32 v
  let t'9 ← PMem.ldF32 ((this + 12) + 4)
  let t'10 ← PMem.ldF32 (v + 4)
  let t'11 ← PMem.ldF32 ((this + 12) + 8)
  let t'12 ← PMem.ldF32 (v + 8)
  let t'13 ← PMem.ldF32 (this + 24)
  let t'14 ← PMem.ldF32 v
  let t'15 ← PMem.ldF32 ((this + 24) + 4)
  let t'16 ← PMem.ldF32 (v + 4)
  let t'17 ← PMem.ldF32 ((this + 24) + 8)
  let t'18 ← PMem.ldF32 (v + 8)
  Vector3'float.Vector3 (fp + 0) (((t'1 * t'2) + (t'3 * t'4)) + (t'5 * t'6)) (((t'7 * t'8) + (t'9 * t'10)) + (t'11 * t'12)) (((t'13 * t'14) + (t'15 * t'16)) + (t'17 * t'18))
  Vector3'float.Vector3'3 sret (fp + 0)
  return ()

def Matrix3'float.operator_ (this : UInt64) (sret : UInt64) (v : UInt64) : PMem.M Unit := do
  let fp ← PMem.enter 12
  let r ← Matrix3'float.operator_.body fp this sret v
  PMem.leave fp
  return r

/-- C++ `MAX : auto (const float &, const double &) -> decltype(one > two ? one : two)`, `AP_Math.h:307-310`. -/
def MAX'float_double (one : UInt64) (two : UInt64) : PMem.M Binary64 := do
  let t'1 ← PMem.ldF32 one
  let t'2 ← PMem.ldF64 two
  let mut c'3 : Binary64 := default
  if (decide ((Binary32.toBinary64 (t'1)) > t'2)) then
    let t'4 ← PMem.ldF32 one
    c'3 := Binary32.toBinary64 (t'4)
  else
    let t'5 ← PMem.ldF64 two
    c'3 := t'5
  return c'3

/-- C++ `MIN : auto (const int &, const unsigned char &) -> decltype(one < two ? one : two)`, `AP_Math.h:300-303`. -/
def MIN'int_unsigned_char (one : UInt64) (two : UInt64) : PMem.M Int32 := do
  let t'1 ← PMem.ldI32 one
  let t'2 ← PMem.ldU8 two
  let mut c'3 : Int32 := default
  if (decide (t'1 < (UInt32.toInt32 (UInt8.toUInt32 (t'2))))) then
    let t'4 ← PMem.ldI32 one
    c'3 := t'4
  else
    let t'5 ← PMem.ldU8 two
    c'3 := UInt32.toInt32 (UInt8.toUInt32 (t'5))
  return c'3

/-- `constrain_value'short` as a pure function of its arguments (it reads and writes no memory). -/
def constrain_value'short.pure' (amt : Int16) (low : Int16) (high : Int16) : Id Int16 := do
  let mut amt := amt
  let mut low := low
  let mut high := high
  if false then
    if false then
      return Int32.toInt16 ((((Int16.toInt32 (low)) + (Int16.toInt32 (high))) / (2 : Int32)))
  if (decide ((Int16.toInt32 (amt)) < (Int16.toInt32 (low)))) then
    return low
  if (decide ((Int16.toInt32 (amt)) > (Int16.toInt32 (high)))) then
    return high
  return amt

/-- C++ `constrain_value : short (const short, const short, const short)`, `<scratch space>:310-331`. -/
def constrain_value'short (amt : Int16) (low : Int16) (high : Int16) : PMem.M Int16 :=
  pure (_root_.Vehicle_lib.constrain_value'short.pure' amt low high)

/-- `constrain_int16` as a pure function of its arguments (it reads and writes no memory). -/
def constrain_int16.pure' (amt : Int16) (low : Int16) (high : Int16) : Id Int16 := do
  let mut amt := amt
  let mut low := low
  let mut high := high
  let t'1 ← _root_.Vehicle_lib.constrain_value'short.pure' amt low high
  return t'1

/-- C++ `constrain_int16 : int16_t (const int16_t, const int16_t, const int16_t)`, `AP_Math.h:191-194`. -/
def constrain_int16 (amt : Int16) (low : Int16) (high : Int16) : PMem.M Int16 :=
  pure (_root_.Vehicle_lib.constrain_int16.pure' amt low high)

/-- C++ `Vector3<double>::operator- : Vector3<double> () const`, `vector3.cpp:407-410`. -/
def Vector3'double.operator_'2.body (fp : UInt64) (this : UInt64) (sret : UInt64) : PMem.M Unit := do
  let t'1 ← PMem.ldF64 this
  let t'2 ← PMem.ldF64 (this + 8)
  let t'3 ← PMem.ldF64 (this + 16)
  Vector3'double.Vector3'3 (fp + 0) (-t'1) (-t'2) (-t'3)
  Vector3'double.Vector3'2 sret (fp + 0)
  return ()

def Vector3'double.operator_'2 (this : UInt64) (sret : UInt64) : PMem.M Unit := do
  let fp ← PMem.enter 24
  let r ← Vector3'double.operator_'2.body fp this sret
  PMem.leave fp
  return r

/-- C++ `SplineCurve::set_speed_accel : void (float, float, float, float, float)`, `SplineCurve.cpp:34-42`. -/
def SplineCurve.set_speed_accel (this : UInt64) (speed_xy : Binary32) (speed_up : Binary32) (speed_down : Binary32) (accel_xy : Binary32) (accel_z : Binary32) : PMem.M Unit := do
  let mut speed_xy := speed_xy
  let mut speed_up := speed_up
  let mut speed_down := speed_down
  let mut accel_xy := accel_xy
  let mut accel_z := accel_z
  let t'1 := (Binary32.abs speed_xy)
  PMem.stF32 (this + 172) t'1
  let t'2 := (Binary32.abs speed_up)
  PMem.stF32 (this + 176) t'2
  let t'3 := (Binary32.abs speed_down)
  PMem.stF32 (this + 180) t'3
  let t'4 := (Binary32.abs accel_xy)
  PMem.stF32 (this + 184) t'4
  let t'5 := (Binary32.abs accel_z)
  PMem.stF32 (this + 188) t'5
  return ()

/-- C++ `SCurve::set_destination_speed_max : void (float)`, `SCurve.cpp:516-560`. -/
def SCurve.set_destination_speed_max.body (fp : UInt64) (this : UInt64) (speed : Binary32) : PMem.M Unit := do
  PMem.stF32 (fp + 0) speed
  let t'1 ← PMem.ldU8 (this + 28)
  if ((UInt32.toInt32 (UInt8.toUInt32 (t'1))) != (UInt32.toInt32 (UInt8.toUInt32 ((23 : UInt8))))) then
    return ()
  let t'2 ← PMem.ldF32 (fp + 0)
  let t'3 := (Binary32.abs t'2)
  PMem.stF32 (fp + 0) t'3
  let t'4 ← PMem.ldF32 (((this + 32) + ((Int32.toInt64 (((UInt32.toInt32 (UInt8.toUInt32 ((23 : UInt8)))) - (1 : Int32)))) * 24).toUInt64) + 16)
  let t'5 ← PMem.ldF32 (fp + 0)
  let t'6 ← is_equal'float_float t'4 t'5
  if t'6 then
    return ()
  let t'7 ← PMem.ldF32 (((this + 32) + ((Int32.toInt64 ((15 : Int32))) * 24).toUInt64) + 16)
  PMem.stF32 (fp + 8) t'7
  let t'8 ← MIN'float_float (fp + 0) (fp + 8)
  let t'9 ← PMem.ldF32 t'8
  PMem.stF32 (fp + 0) t'9
  let t'10 ← PMem.ldF32 this
  let t'11 ← PMem.ldF32 (this + 4)
  let t'12 ← PMem.ldF32 (fp + 0)
  let t'13 ← PMem.ldF32 (this + 8)
  let t'14 ← PMem.ldF32 (fp + 8)
  let t'15 ← PMem.ldF32 (this + 600)
  SCurve.calculate_path t'10 t'11 t'12 t'13 t'14 (t'15 * (Binary32.ofBits 0x3f000000 /- 1/2 -/)) (fp + 16) (fp + 24) (fp + 32) (fp + 40) (fp + 48)
  PMem.stU8 (fp + 56) (Int8.toUInt8 (Int32.toInt8 ((15 : Int32))))
  SCurve.add_segment_const_jerk this (fp + 56) (Binary32.ofBits 0x00000000 /- 0 -/) (Binary32.ofBits 0x00000000 /- 0 -/)
  let t'16 ← PMem.ldF32 (fp + 24)
  let t'17 ← PMem.ldF32 (fp + 16)
  let t'18 ← PMem.ldF32 (fp + 48)
  SCurve.add_segments_jerk this (fp + 56) t'16 (-t'17) t'18
  let t'19 ← PMem.ldF32 (fp + 40)
  SCurve.add_segment_const_jerk this (fp + 56) t'19 (Binary32.ofBits 0x00000000 /- 0 -/)
  let t'20 ← PMem.ldF32 (fp + 24)
  let t'21 ← PMem.ldF32 (fp + 16)
  let t'22 ← PMem.ldF32 (fp + 32)
  SCurve.add_segments_jerk this (fp + 56) t'20 t'21 t'22
  let t'23 := (Binary32.ofBits 0x00000000 /- 0 -/)
  PMem.stF32 (((this + 32) + ((Int32.toInt64 ((22 : Int32))) * 24).toUInt64) + 12) t'23
  PMem.stF32 (fp + 60) (Binary32.ofBits 0x00000000 /- 0 -/)
  let t'24 ← MAX'float_float (fp + 60) (((this + 32) + ((Int32.toInt64 ((22 : Int32))) * 24).toUInt64) + 16)
  let t'25 ← PMem.ldF32 t'24
  PMem.stF32 (((this + 32) + ((Int32.toInt64 ((22 : Int32))) * 24).toUInt64) + 16) t'25
  let t'26 ← PMem.ldF32 (this + 600)
  SCurve.extend_const_vel_to this t'26
  let t'27 ← SCurve.valid this
  if !t'27 then
    SCurve.debug this
    SCurve.init this
  return ()

def SCurve.set_destination_speed_max (this : UInt64) (speed : Binary32) : PMem.M Unit := do
  let fp ← PMem.enter 64
  let r ← SCurve.set_destination_speed_max.body fp this speed
  PMem.leave fp
  return r

/-- C++ `SCurve::calc_javp_for_segment_const_jerk : void (float, float, float, float, float, float &, float &, float &, float &) const`, `SCurve.cpp:846-852`. -/
def SCurve.calc_javp_for_segment_const_jerk (this : UInt64) (time_now : Binary32) (J0 : Binary32) (A0 : Binary32) (V0 : Binary32) (P0 : Binary32) (Jt : UInt64) (At : UInt64) (Vt : UInt64) (Pt : UInt64) : PMem.M Unit := do
  let mut time_now := time_now
  let mut J0 := J0
  let mut A0 := A0
  let mut V0 := V0
  let mut P0 := P0
  PMem.stF32 Jt J0
  let t'1 := (A0 + (J0 * time_now))
  PMem.stF32 At t'1
  let t'2 := ((V0 + (A0 * time_now)) + (((Binary32.ofBits 0x3f000000 /- 1/2 -/) * J0) * (time_now * time_now)))
  PMem.stF32 Vt t'2
  let t'3 := (((P0 + (V0 * time_now)) + (((Binary32.ofBits 0x3f000000 /- 1/2 -/) * A0) * (time_now * time_now))) + ((((Binary32.ofBits 0x3f800000 /- 1 -/) / (Binary32.ofBits 0x40c00000 /- 6 -/)) * J0) * ((time_now * time_now) * time_now)))
  PMem.stF32 Pt t'3
  return ()

/-- C++ `SCurve::calc_javp_for_segment_incr_jerk : void (float, float, float, float, float, float, float &, float &, float &, float &) const`, `SCurve.cpp:855-870`. -/
def SCurve.calc_javp_for_segment_incr_jerk (this : UInt64) (time_now : Binary32) (tj : Binary32) (Jm : Binary32) (A0 : Binary32) (V0 : Binary32) (P0 : Binary32) (Jt : UInt64) (At : UInt64) (Vt : UInt64) (Pt : UInt64) : PMem.M Unit := do
  let mut time_now := time_now
  let mut tj := tj
  let mut Jm := Jm
  let mut A0 := A0
  let mut V0 := V0
  let mut P0 := P0
  let t'1 ← is_positive'float tj
  if !t'1 then
    let t'2 := (Binary32.ofBits 0x00000000 /- 0 -/)
    PMem.stF32 Jt t'2
    PMem.stF32 At A0
    PMem.stF32 Vt V0
    PMem.stF32 Pt P0
    return ()
  let mut Alpha : Binary32 := (Jm * (Binary32.ofBits 0x3f000000 /- 1/2 -/))
  let mut Beta : Binary32 := ((Binary64.toBinary32 ((Binary64.ofBits 0x400921fb54442d18 /- 31415926535897931/10000000000000000 -/))) / tj)
  let t'3 := (Alpha * ((Binary32.ofBits 0x3f800000 /- 1 -/) - (Musl.cosf.cosf (Beta * time_now))))
  PMem.stF32 Jt t'3
  let t'4 := ((A0 + (Alpha * time_now)) - ((Alpha / Beta) * (Musl.sinf.sinf (Beta * time_now))))
  PMem.stF32 At t'4
  let t'5 := ((((V0 + (A0 * time_now)) + ((Alpha * (Binary32.ofBits 0x3f000000 /- 1/2 -/)) * (time_now * time_now))) + ((Alpha / (Beta * Beta)) * (Musl.cosf.cosf (Beta * time_now)))) - (Alpha / (Beta * Beta)))
  PMem.stF32 Vt t'5
  let t'6 := (((((P0 + (V0 * time_now)) + (((Binary32.ofBits 0x3f000000 /- 1/2 -/) * A0) * (time_now * time_now))) + (((-Alpha) / (Beta * Beta)) * time_now)) + ((Alpha * ((time_now * time_now) * time_now)) / (Binary32.ofBits 0x40c00000 /- 6 -/))) + ((Alpha / ((Beta * Beta) * Beta)) * (Musl.sinf.sinf (Beta * time_now))))
  PMem.stF32 Pt t'6
  return ()

/-- C++ `SCurve::calc_javp_for_segment_decr_jerk : void (float, float, float, float, float, float, float &, float &, float &, float &) const`, `SCurve.cpp:873-891`. -/
def SCurve.calc_javp_for_segment_decr_jerk (this : UInt64) (time_now : Binary32) (tj : Binary32) (Jm : Binary32) (A0 : Binary32) (V0 : Binary32) (P0 : Binary32) (Jt : UInt64) (At : UInt64) (Vt : UInt64) (Pt : UInt64) : PMem.M Unit := do
  let mut time_now := time_now
  let mut tj := tj
  let mut Jm := Jm
  let mut A0 := A0
  let mut V0 := V0
  let mut P0 := P0
  let t'1 ← is_positive'float tj
  if !t'1 then
    let t'2 := (Binary32.ofBits 0x00000000 /- 0 -/)
    PMem.stF32 Jt t'2
    PMem.stF32 At A0
    PMem.stF32 Vt V0
    PMem.stF32 Pt P0
    return ()
  let mut Alpha : Binary32 := (Jm * (Binary32.ofBits 0x3f000000 /- 1/2 -/))
  let mut Beta : Binary32 := ((Binary64.toBinary32 ((Binary64.ofBits 0x400921fb54442d18 /- 31415926535897931/10000000000000000 -/))) / tj)
  let mut AT : Binary32 := (Alpha * tj)
  let mut VT : Binary32 := (Alpha * (((tj * tj) * (Binary32.ofBits 0x3f000000 /- 1/2 -/)) - ((Binary32.ofBits 0x40000000 /- 2 -/) / (Beta * Beta))))
  let mut PT : Binary32 := (Alpha * ((((-(Binary32.ofBits 0x3f800000 /- 1 -/)) / (Beta * Beta)) * tj) + (((Binary32.ofBits 0x3f800000 /- 1 -/) / (Binary32.ofBits 0x40c00000 /- 6 -/)) * ((tj * tj) * tj))))
  let t'3 := (Alpha * ((Binary32.ofBits 0x3f800000 /- 1 -/) - (Musl.cosf.cosf (Beta * (time_now + tj)))))
  PMem.stF32 Jt t'3
  let t'4 := (((A0 - AT) + (Alpha * (time_now + tj))) - ((Alpha / Beta) * (Musl.sinf.sinf (Beta * (time_now + tj)))))
  PMem.stF32 At t'4
  let t'5 := (((((V0 - VT) + ((A0 - AT) * time_now)) + ((((Binary32.ofBits 0x3f000000 /- 1/2 -/) * Alpha) * (time_now + tj)) * (time_now + tj))) + ((Alpha / (Beta * Beta)) * (Musl.cosf.cosf (Beta * (time_now + tj))))) - (Alpha / (Beta * Beta)))
  PMem.stF32 Vt t'5
  let t'6 := ((((((P0 - PT) + ((V0 - VT) * time_now)) + (((Binary32.ofBits 0x3f000000 /- 1/2 -/) * (A0 - AT)) * (time_now * time_now))) + (((-Alpha) / (Beta * Beta)) * (time_now + tj))) + ((((Alpha / (Binary32.ofBits 0x40c00000 /- 6 -/)) * (time_now + tj)) * (time_now + tj)) * (time_now + tj))) + ((Alpha / ((Beta * Beta) * Beta)) * (Musl.sinf.sinf (Beta * (time_now + tj)))))
  PMem.stF32 Pt t'6
  return ()

/-- C++ `SCurve::get_jerk_accel_vel_pos_at_time : void (float, float &, float &, float &, float &) const`, `SCurve.cpp:784-843`. -/
def SCurve.get_jerk_accel_vel_pos_at_time.body (fp : UInt64) (this : UInt64) (time_now : Binary32) (Jt_out : UInt64) (At_out : UInt64) (Vt_out : UInt64) (Pt_out : UInt64) : PMem.M Unit := do
  let mut time_now := time_now
  let t'1 := (Binary32.ofBits 0x00000000 /- 0 -/)
  PMem.stF32 Jt_out t'1
  let t'2 := (Binary32.ofBits 0x00000000 /- 0 -/)
  PMem.stF32 At_out t'2
  let t'3 := (Binary32.ofBits 0x00000000 /- 0 -/)
  PMem.stF32 Vt_out t'3
  let t'4 := (Binary32.ofBits 0x00000000 /- 0 -/)
  PMem.stF32 Pt_out t'4
  let t'5 ← PMem.ldU8 (this + 28)
  if ((UInt32.toInt32 (UInt8.toUInt32 (t'5))) != (UInt32.toInt32 (UInt8.toUInt32 ((23 : UInt8))))) then
    return ()
  let mut Jtype : Int32 := default  -- uninitialized in C
  let t'6 ← PMem.ldU8 (this + 28)
  let mut pnt : UInt8 := t'6
  let mut Jm : Binary32 := default  -- uninitialized in C
  let mut tj : Binary32 := default  -- uninitialized in C
  let mut T0 : Binary32 := default  -- uninitialized in C
  let mut A0 : Binary32 := default  -- uninitialized in C
  let mut V0 : Binary32 := default  -- uninitialized in C
  let mut P0 : Binary32 := default  -- uninitialized in C
  let mut i : UInt8 := Int8.toUInt8 (Int32.toInt8 ((0 : Int32)))
  let mut first'7 := true
  for _ in PMem.loopFuel do
    if !first'7 then
      let t'8 := i
      let t'9 := (t'8 + 1)
      i := t'9
      pure ()
    first'7 := false
    let t'10 ← PMem.ldU8 (this + 28)
    if !((decide ((UInt32.toInt32 (UInt8.toUInt32 (i))) < (UInt32.toInt32 (UInt8.toUInt32 (t'10)))))) then break
    let t'11 ← PMem.ldU8 (this + 28)
    let t'12 ← PMem.ldF32 (((this + 32) + ((Int32.toInt64 ((((UInt32.toInt32 (UInt8.toUInt32 (t'11))) - (1 : Int32)) - (UInt32.toInt32 (UInt8.toUInt32 (i)))))) * 24).toUInt64) + 8)
    if (decide (time_now < t'12)) then
      let t'13 ← PMem.ldU8 (this + 28)
      let t'14 := Int8.toUInt8 (Int32.toInt8 ((((UInt32.toInt32 (UInt8.toUInt32 (t'13))) - (1 : Int32)) - (UInt32.toInt32 (UInt8.toUInt32 (i))))))
      pnt := t'14
  if ((UInt32.toInt32 (UInt8.toUInt32 (pnt))) == (0 : Int32)) then
    Jtype := (0 : Int32)
    let t'15 := (Binary32.ofBits 0x00000000 /- 0 -/)
    Jm := t'15
    let t'16 := (Binary32.ofBits 0x00000000 /- 0 -/)
    tj := t'16
    let t'17 ← PMem.ldF32 (((this + 32) + ((UInt64.toInt64 (UInt8.toUInt64 (pnt))) * 24).toUInt64) + 8)
    T0 := t'17
    let t'18 ← PMem.ldF32 (((this + 32) + ((UInt64.toInt64 (UInt8.toUInt64 (pnt))) * 24).toUInt64) + 12)
    A0 := t'18
    let t'19 ← PMem.ldF32 (((this + 32) + ((UInt64.toInt64 (UInt8.toUInt64 (pnt))) * 24).toUInt64) + 16)
    V0 := t'19
    let t'20 ← PMem.ldF32 (((this + 32) + ((UInt64.toInt64 (UInt8.toUInt64 (pnt))) * 24).toUInt64) + 20)
    P0 := t'20
  else
    let t'21 ← PMem.ldU8 (this + 28)
    if ((UInt32.toInt32 (UInt8.toUInt32 (pnt))) == (UInt32.toInt32 (UInt8.toUInt32 (t'21)))) then
      Jtype := (0 : Int32)
      let t'22 := (Binary32.ofBits 0x00000000 /- 0 -/)
      Jm := t'22
      let t'23 := (Binary32.ofBits 0x00000000 /- 0 -/)
      tj := t'23
      let t'24 ← PMem.ldF32 (((this + 32) + ((Int32.toInt64 (((UInt32.toInt32 (UInt8.toUInt32 (pnt))) - (1 : Int32)))) * 24).toUInt64) + 8)
      T0 := t'24
      let t'25 ← PMem.ldF32 (((this + 32) + ((Int32.toInt64 (((UInt32.toInt32 (UInt8.toUInt32 (pnt))) - (1 : Int32)))) * 24).toUInt64) + 12)
      A0 := t'25
      let t'26 ← PMem.ldF32 (((this + 32) + ((Int32.toInt64 (((UInt32.toInt32 (UInt8.toUInt32 (pnt))) - (1 : Int32)))) * 24).toUInt64) + 16)
      V0 := t'26
      let t'27 ← PMem.ldF32 (((this + 32) + ((Int32.toInt64 (((UInt32.toInt32 (UInt8.toUInt32 (pnt))) - (1 : Int32)))) * 24).toUInt64) + 20)
      P0 := t'27
    else
      let t'28 ← PMem.ldI32 (((this + 32) + ((UInt64.toInt64 (UInt8.toUInt64 (pnt))) * 24).toUInt64) + 4)
      Jtype := t'28
      let t'29 ← PMem.ldF32 ((this + 32) + ((UInt64.toInt64 (UInt8.toUInt64 (pnt))) * 24).toUInt64)
      Jm := t'29
      let t'30 ← PMem.ldF32 (((this + 32) + ((UInt64.toInt64 (UInt8.toUInt64 (pnt))) * 24).toUInt64) + 8)
      let t'31 ← PMem.ldF32 (((this + 32) + ((Int32.toInt64 (((UInt32.toInt32 (UInt8.toUInt32 (pnt))) - (1 : Int32)))) * 24).toUInt64) + 8)
      let t'32 := (t'30 - t'31)
      tj := t'32
      let t'33 ← PMem.ldF32 (((this + 32) + ((Int32.toInt64 (((UInt32.toInt32 (UInt8.toUInt32 (pnt))) - (1 : Int32)))) * 24).toUInt64) + 8)
      T0 := t'33
      let t'34 ← PMem.ldF32 (((this + 32) + ((Int32.toInt64 (((UInt32.toInt32 (UInt8.toUInt32 (pnt))) - (1 : Int32)))) * 24).toUInt64) + 12)
      A0 := t'34
      let t'35 ← PMem.ldF32 (((this + 32) + ((Int32.toInt64 (((UInt32.toInt32 (UInt8.toUInt32 (pnt))) - (1 : Int32)))) * 24).toUInt64) + 16)
      V0 := t'35
      let t'36 ← PMem.ldF32 (((this + 32) + ((Int32.toInt64 (((UInt32.toInt32 (UInt8.toUInt32 (pnt))) - (1 : Int32)))) * 24).toUInt64) + 20)
      P0 := t'36
  let sw'37 := Jtype
  if sw'37 == (0 : Int32) then
    SCurve.calc_javp_for_segment_const_jerk this (time_now - T0) Jm A0 V0 P0 Jt_out At_out Vt_out Pt_out
  else if sw'37 == (1 : Int32) then
    SCurve.calc_javp_for_segment_incr_jerk this (time_now - T0) tj Jm A0 V0 P0 Jt_out At_out Vt_out Pt_out
  else if sw'37 == (2 : Int32) then
    SCurve.calc_javp_for_segment_decr_jerk this (time_now - T0) tj Jm A0 V0 P0 Jt_out At_out Vt_out Pt_out
  else
    pure ()
  PMem.stF32 (fp + 0) (Binary32.ofBits 0x00000000 /- 0 -/)
  let t'38 ← MAX'float_float (fp + 0) Pt_out
  let t'39 ← PMem.ldF32 t'38
  PMem.stF32 Pt_out t'39
  return ()

def SCurve.get_jerk_accel_vel_pos_at_time (this : UInt64) (time_now : Binary32) (Jt_out : UInt64) (At_out : UInt64) (Vt_out : UInt64) (Pt_out : UInt64) : PMem.M Unit := do
  let fp ← PMem.enter 4
  let r ← SCurve.get_jerk_accel_vel_pos_at_time.body fp this time_now Jt_out At_out Vt_out Pt_out
  PMem.leave fp
  return r

/-- C++ `SCurve::set_speed_max : void (float, float, float)`, `SCurve.cpp:238-440`. -/
def SCurve.set_speed_max.body (fp : UInt64) (this : UInt64) (speed_xy : Binary32) (speed_up : Binary32) (speed_down : Binary32) : PMem.M Unit := do
  PMem.stF32 (fp + 0) speed_xy
  let mut speed_up := speed_up
  let mut speed_down := speed_down
  let t'1 ← PMem.ldF32 (fp + 0)
  let t'2 := (Binary32.abs t'1)
  PMem.stF32 (fp + 0) t'2
  let t'3 := (Binary32.abs speed_up)
  speed_up := t'3
  let t'4 := (Binary32.abs speed_down)
  speed_down := t'4
  let t'5 ← PMem.ldU8 (this + 28)
  if ((UInt32.toInt32 (UInt8.toUInt32 (t'5))) != (UInt32.toInt32 (UInt8.toUInt32 ((23 : UInt8))))) then
    return ()
  let t'6 ← PMem.ldB (this + 584)
  if t'6 then
    let t'7 ← PMem.ldF32 (this + 12)
    let t'8 ← PMem.ldF32 ((this + 604) + 8)
    let t'9 ← safe_sqrt'float (t'7 * t'8)
    PMem.stF32 (fp + 4) t'9
    let t'10 ← MIN'float_float (fp + 0) (fp + 4)
    let t'11 ← PMem.ldF32 t'10
    PMem.stF32 (fp + 0) t'11
  let t'12 ← PMem.ldF32 ((this + 604) + 4)
  let t'13 ← PMem.ldF32 ((this + 588) + 8)
  let t'14 ← PMem.ldF32 (fp + 0)
  let t'15 ← kinematic_limit t'12 t'13 t'14 speed_up speed_down
  let mut track_speed_max : Binary32 := t'15
  let t'16 ← PMem.ldF32 (this + 20)
  let t'17 ← is_equal'float_float t'16 track_speed_max
  if t'17 then
    return ()
  let t'18 ← is_zero track_speed_max
  if t'18 then
    return ()
  PMem.stF32 (this + 20) track_speed_max
  let t'19 ← PMem.ldF32 (this + 24)
  let t'20 ← PMem.ldF32 (((this + 32) + ((Int32.toInt64 ((15 : Int32))) * 24).toUInt64) + 8)
  if (decide (t'19 ≥ t'20)) then
    return ()
  let t'21 ← PMem.ldF32 (((this + 32) + ((Int32.toInt64 ((22 : Int32))) * 24).toUInt64) + 20)
  let mut Pend : Binary32 := t'21
  let t'22 ← MIN'float_float (this + 20) (((this + 32) + ((Int32.toInt64 ((22 : Int32))) * 24).toUInt64) + 16)
  let t'23 ← PMem.ldF32 t'22
  PMem.stF32 (fp + 8) t'23
  let t'24 ← PMem.ldF32 (this + 24)
  let t'25 ← is_zero t'24
  if t'25 then
    let t'26 ← MIN'float_float (this + 20) (((this + 32) + ((Int32.toInt64 ((0 : Int32))) * 24).toUInt64) + 16)
    let t'27 ← PMem.ldF32 t'26
    let mut Vstart : Binary32 := t'27
    let t'28 := Int8.toUInt8 (Int32.toInt8 ((0 : Int32)))
    PMem.stU8 (this + 28) t'28
    SCurve.add_segment this (this + 28) (Binary32.ofBits 0x00000000 /- 0 -/) (0 : Int32) (Binary32.ofBits 0x00000000 /- 0 -/) (Binary32.ofBits 0x00000000 /- 0 -/) (Binary32.ofBits 0x00000000 /- 0 -/) (Binary32.ofBits 0x00000000 /- 0 -/)
    SCurve.add_segments this Pend
    let t'29 ← SCurve.set_origin_speed_max this Vstart
    discard <| pure (t'29)
    let t'30 ← PMem.ldF32 (fp + 8)
    SCurve.set_destination_speed_max this t'30
    return ()
  let t'31 ← PMem.ldF32 (this + 24)
  let t'32 ← PMem.ldF32 (((this + 32) + ((Int32.toInt64 ((7 : Int32))) * 24).toUInt64) + 8)
  let mut sc'35 := (decide (t'31 ≥ t'32))
  if sc'35 then
    let t'33 ← PMem.ldF32 (this + 24)
    let t'34 ← PMem.ldF32 (((this + 32) + ((Int32.toInt64 ((14 : Int32))) * 24).toUInt64) + 8)
    sc'35 := (decide (t'33 ≤ t'34))
  if sc'35 then
    PMem.stI32 (((this + 32) + ((Int32.toInt64 ((0 : Int32))) * 24).toUInt64) + 4) (0 : Int32)
    let t'36 := (Binary32.ofBits 0x00000000 /- 0 -/)
    PMem.stF32 ((this + 32) + ((Int32.toInt64 ((0 : Int32))) * 24).toUInt64) t'36
    let t'37 ← PMem.ldF32 (((this + 32) + ((Int32.toInt64 ((7 : Int32))) * 24).toUInt64) + 8)
    PMem.stF32 (((this + 32) + ((Int32.toInt64 ((0 : Int32))) * 24).toUInt64) + 8) t'37
    let t'38 ← PMem.ldF32 (((this + 32) + ((Int32.toInt64 ((7 : Int32))) * 24).toUInt64) + 12)
    PMem.stF32 (((this + 32) + ((Int32.toInt64 ((0 : Int32))) * 24).toUInt64) + 12) t'38
    let t'39 ← PMem.ldF32 (((this + 32) + ((Int32.toInt64 ((7 : Int32))) * 24).toUInt64) + 16)
    PMem.stF32 (((this + 32) + ((Int32.toInt64 ((0 : Int32))) * 24).toUInt64) + 16) t'39
    let t'40 ← PMem.ldF32 (((this + 32) + ((Int32.toInt64 ((7 : Int32))) * 24).toUInt64) + 20)
    PMem.stF32 (((this + 32) + ((Int32.toInt64 ((0 : Int32))) * 24).toUInt64) + 20) t'40
    for i'41 in [1:8] do
      let i : UInt8 := UInt8.ofNat i'41
      discard <| PMem.memcpy ((this + 32) + ((UInt64.toInt64 (UInt8.toUInt64 (i))) * 24).toUInt64) ((this + 32) + ((Int32.toInt64 (((UInt32.toInt32 (UInt8.toUInt32 (i))) + (7 : Int32)))) * 24).toUInt64) 24
      discard <| pure (((this + 32) + ((UInt64.toInt64 (UInt8.toUInt64 (i))) * 24).toUInt64))
    SCurve.fill_empty_segments this (Int8.toUInt8 (Int32.toInt8 (((7 : Int32) + (1 : Int32))))) (Int8.toUInt8 (Int32.toInt8 ((14 : Int32)))) (Int8.toUInt8 (Int32.toInt8 ((7 : Int32))))
  else
    let t'42 ← PMem.ldF32 (this + 24)
    let t'43 ← PMem.ldF32 (((this + 32) + ((Int32.toInt64 ((14 : Int32))) * 24).toUInt64) + 8)
    let mut sc'46 := (decide (t'42 > t'43))
    if sc'46 then
      let t'44 ← PMem.ldF32 (this + 24)
      let t'45 ← PMem.ldF32 (((this + 32) + ((Int32.toInt64 ((15 : Int32))) * 24).toUInt64) + 8)
      sc'46 := (decide (t'44 ≤ t'45))
    if sc'46 then
      PMem.stI32 (((this + 32) + ((Int32.toInt64 ((0 : Int32))) * 24).toUInt64) + 4) (0 : Int32)
      let t'47 := (Binary32.ofBits 0x00000000 /- 0 -/)
      PMem.stF32 ((this + 32) + ((Int32.toInt64 ((0 : Int32))) * 24).toUInt64) t'47
      let t'48 ← PMem.ldF32 (((this + 32) + ((Int32.toInt64 ((14 : Int32))) * 24).toUInt64) + 8)
      PMem.stF32 (((this + 32) + ((Int32.toInt64 ((0 : Int32))) * 24).toUInt64) + 8) t'48
      let t'49 := (Binary32.ofBits 0x00000000 /- 0 -/)
      PMem.stF32 (((this + 32) + ((Int32.toInt64 ((0 : Int32))) * 24).toUInt64) + 12) t'49
      let t'50 ← PMem.ldF32 (((this + 32) + ((Int32.toInt64 ((14 : Int32))) * 24).toUInt64) + 16)
      PMem.stF32 (((this + 32) + ((Int32.toInt64 ((0 : Int32))) * 24).toUInt64) + 16) t'50
      let t'51 ← PMem.ldF32 (((this + 32) + ((Int32.toInt64 ((14 : Int32))) * 24).toUInt64) + 20)
      PMem.stF32 (((this + 32) + ((Int32.toInt64 ((0 : Int32))) * 24).toUInt64) + 20) t'51
      let t'52 ← PMem.ldF32 (this + 24)
      SCurve.get_jerk_accel_vel_pos_at_time this t'52 (fp + 16) (fp + 24) (fp + 32) (fp + 40)
      for i'2'53 in [1:15] do
        let i'2 : UInt8 := UInt8.ofNat i'2'53
        PMem.stI32 (((this + 32) + ((UInt64.toInt64 (UInt8.toUInt64 (i'2))) * 24).toUInt64) + 4) (0 : Int32)
        let t'54 := (Binary32.ofBits 0x00000000 /- 0 -/)
        PMem.stF32 ((this + 32) + ((UInt64.toInt64 (UInt8.toUInt64 (i'2))) * 24).toUInt64) t'54
        let t'55 ← PMem.ldF32 (this + 24)
        PMem.stF32 (((this + 32) + ((UInt64.toInt64 (UInt8.toUInt64 (i'2))) * 24).toUInt64) + 8) t'55
        let t'56 := (Binary32.ofBits 0x00000000 /- 0 -/)
        PMem.stF32 (((this + 32) + ((UInt64.toInt64 (UInt8.toUInt64 (i'2))) * 24).toUInt64) + 12) t'56
        let t'57 ← PMem.ldF32 (fp + 32)
        PMem.stF32 (((this + 32) + ((UInt64.toInt64 (UInt8.toUInt64 (i'2))) * 24).toUInt64) + 16) t'57
        let t'58 ← PMem.ldF32 (fp + 40)
        PMem.stF32 (((this + 32) + ((UInt64.toInt64 (UInt8.toUInt64 (i'2))) * 24).toUInt64) + 20) t'58
  let t'59 ← PMem.ldF32 (this + 24)
  let t'60 ← PMem.ldF32 (((this + 32) + ((Int32.toInt64 ((4 : Int32))) * 24).toUInt64) + 8)
  let mut sc'64 := (decide (t'59 ≤ t'60))
  if sc'64 then
    let t'61 ← PMem.ldF32 (((this + 32) + ((Int32.toInt64 ((4 : Int32))) * 24).toUInt64) + 8)
    let t'62 ← PMem.ldF32 (((this + 32) + ((Int32.toInt64 (((4 : Int32) - (1 : Int32)))) * 24).toUInt64) + 8)
    let t'63 ← is_positive'float (t'61 - t'62)
    sc'64 := t'63
  let mut sc'67 := sc'64
  if sc'67 then
    let t'65 ← PMem.ldF32 (this + 20)
    let t'66 ← PMem.ldF32 (((this + 32) + ((Int32.toInt64 ((7 : Int32))) * 24).toUInt64) + 16)
    sc'67 := (decide (t'65 < t'66))
  let mut sc'70 := sc'67
  if sc'70 then
    let t'68 ← PMem.ldF32 (((this + 32) + ((Int32.toInt64 ((4 : Int32))) * 24).toUInt64) + 12)
    let t'69 ← is_positive'float t'68
    sc'70 := t'69
  if sc'70 then
    let t'71 ← PMem.ldF32 (((this + 32) + ((Int32.toInt64 ((0 : Int32))) * 24).toUInt64) + 16)
    let mut Vstart'2 : Binary32 := t'71
    let t'72 ← PMem.ldF32 (((this + 32) + ((Int32.toInt64 ((7 : Int32))) * 24).toUInt64) + 16)
    let t'73 ← PMem.ldF32 (((this + 32) + ((Int32.toInt64 ((4 : Int32))) * 24).toUInt64) + 12)
    let t'74 ← PMem.ldF32 (((this + 32) + ((Int32.toInt64 ((4 : Int32))) * 24).toUInt64) + 8)
    let t'75 ← MAX'float_float (this + 24) (((this + 32) + ((Int32.toInt64 (((4 : Int32) - (1 : Int32)))) * 24).toUInt64) + 8)
    let t'76 ← PMem.ldF32 t'75
    PMem.stF32 (fp + 48) (t'72 - (t'73 * (t'74 - t'76)))
    let t'77 ← PMem.ldF32 this
    let t'78 ← PMem.ldF32 (this + 4)
    let t'79 ← PMem.ldF32 (this + 8)
    let t'80 ← MAX'float_float (fp + 48) (this + 20)
    let t'81 ← PMem.ldF32 t'80
    SCurve.calculate_path t'77 t'78 Vstart'2 t'79 t'81 (Pend * (Binary32.ofBits 0x3f000000 /- 1/2 -/)) (fp + 56) (fp + 64) (fp + 72) (fp + 80) (fp + 88)
    PMem.stU8 (fp + 96) (Int8.toUInt8 (Int32.toInt8 (((0 : Int32) + (1 : Int32)))))
    let t'82 ← PMem.ldF32 (fp + 64)
    let t'83 ← PMem.ldF32 (fp + 56)
    let t'84 ← PMem.ldF32 (fp + 72)
    SCurve.add_segments_jerk this (fp + 96) t'82 t'83 t'84
    let t'85 ← PMem.ldF32 (fp + 80)
    SCurve.add_segment_const_jerk this (fp + 96) t'85 (Binary32.ofBits 0x00000000 /- 0 -/)
    let t'86 ← PMem.ldF32 (fp + 64)
    let t'87 ← PMem.ldF32 (fp + 56)
    let t'88 ← PMem.ldF32 (fp + 88)
    SCurve.add_segments_jerk this (fp + 96) t'86 (-t'87) t'88
    let t'89 := (Binary32.ofBits 0x00000000 /- 0 -/)
    PMem.stF32 (((this + 32) + ((Int32.toInt64 ((7 : Int32))) * 24).toUInt64) + 12) t'89
    SCurve.fill_empty_segments this (Int8.toUInt8 (Int32.toInt8 (((7 : Int32) + (1 : Int32))))) (Int8.toUInt8 (Int32.toInt8 ((15 : Int32)))) (Int8.toUInt8 (Int32.toInt8 ((7 : Int32))))
    let t'90 ← PMem.ldF32 this
    let t'91 ← PMem.ldF32 (this + 4)
    let t'92 ← PMem.ldF32 (this + 8)
    let t'93 ← MAX'float_float (fp + 48) (this + 20)
    let t'94 ← PMem.ldF32 t'93
    SCurve.calculate_path t'90 t'91 (Binary32.ofBits 0x00000000 /- 0 -/) t'92 t'94 (Pend * (Binary32.ofBits 0x3f000000 /- 1/2 -/)) (fp + 56) (fp + 64) (fp + 72) (fp + 80) (fp + 88)
    let t'95 := Int8.toUInt8 (Int32.toInt8 (((15 : Int32) + (1 : Int32))))
    PMem.stU8 (fp + 96) t'95
    let t'96 ← PMem.ldF32 (fp + 64)
    let t'97 ← PMem.ldF32 (fp + 56)
    let t'98 ← PMem.ldF32 (fp + 88)
    SCurve.add_segments_jerk this (fp + 96) t'96 (-t'97) t'98
    let t'99 ← PMem.ldF32 (fp + 80)
    SCurve.add_segment_const_jerk this (fp + 96) t'99 (Binary32.ofBits 0x00000000 /- 0 -/)
    let t'100 ← PMem.ldF32 (fp + 64)
    let t'101 ← PMem.ldF32 (fp + 56)
    let t'102 ← PMem.ldF32 (fp + 72)
    SCurve.add_segments_jerk this (fp + 96) t'100 t'101 t'102
    let t'103 := (Binary32.ofBits 0x00000000 /- 0 -/)
    PMem.stF32 (((this + 32) + ((Int32.toInt64 ((22 : Int32))) * 24).toUInt64) + 12) t'103
    PMem.stF32 (fp + 100) (Binary32.ofBits 0x00000000 /- 0 -/)
    let t'104 ← MAX'float_float (fp + 100) (((this + 32) + ((Int32.toInt64 ((22 : Int32))) * 24).toUInt64) + 16)
    let t'105 ← PMem.ldF32 t'104
    PMem.stF32 (((this + 32) + ((Int32.toInt64 ((22 : Int32))) * 24).toUInt64) + 16) t'105
    SCurve.extend_const_vel_to this Pend
  SCurve.fill_empty_segments this (Int8.toUInt8 (Int32.toInt8 (((7 : Int32) + (1 : Int32))))) (Int8.toUInt8 (Int32.toInt8 ((14 : Int32)))) (Int8.toUInt8 (Int32.toInt8 ((7 : Int32))))
  let t'106 ← PMem.ldF32 (this + 20)
  let t'107 ← PMem.ldF32 (((this + 32) + ((Int32.toInt64 ((7 : Int32))) * 24).toUInt64) + 16)
  let t'108 ← is_equal'float_float t'106 t'107
  if !t'108 then
    let t'109 ← PMem.ldF32 (((this + 32) + ((Int32.toInt64 ((15 : Int32))) * 24).toUInt64) + 20)
    let t'110 ← PMem.ldF32 (((this + 32) + ((Int32.toInt64 ((7 : Int32))) * 24).toUInt64) + 20)
    let mut L : Binary32 := (t'109 - t'110)
    PMem.stF32 (fp + 104) (Int32.toBinary32 ((0 : Int32)))
    PMem.stF32 (fp + 112) (Int32.toBinary32 ((0 : Int32)))
    PMem.stF32 (fp + 120) (Int32.toBinary32 ((0 : Int32)))
    PMem.stF32 (fp + 128) (Int32.toBinary32 ((0 : Int32)))
    PMem.stF32 (fp + 136) (Int32.toBinary32 ((0 : Int32)))
    let t'111 ← PMem.ldF32 (this + 20)
    let t'112 ← PMem.ldF32 (((this + 32) + ((Int32.toInt64 ((7 : Int32))) * 24).toUInt64) + 16)
    let t'113 ← PMem.ldF32 this
    PMem.stF32 (fp + 140) (Musl.powf.powf (((Binary32.abs (t'111 - t'112)) * (Binary64.toBinary32 ((Binary64.ofBits 0x400921fb54442d18 /- 31415926535897931/10000000000000000 -/)))) / ((Binary32.ofBits 0x40800000 /- 4 -/) * t'113)) ((Binary32.ofBits 0x3f800000 /- 1 -/) / (Binary32.ofBits 0x40400000 /- 3 -/)))
    let t'114 ← PMem.ldF32 (this + 4)
    let t'115 ← PMem.ldF32 this
    PMem.stF32 (fp + 144) ((t'114 * (Binary64.toBinary32 ((Binary64.ofBits 0x400921fb54442d18 /- 31415926535897931/10000000000000000 -/)))) / ((Binary32.ofBits 0x40000000 /- 2 -/) * t'115))
    let t'116 ← MIN'float_float (fp + 140) (fp + 144)
    let t'117 ← PMem.ldF32 t'116
    let mut jerk_time : Binary32 := t'117
    let t'118 ← PMem.ldF32 (this + 20)
    let t'119 ← PMem.ldF32 (((this + 32) + ((Int32.toInt64 ((7 : Int32))) * 24).toUInt64) + 16)
    let mut sc'121 := (decide (t'118 < t'119))
    if sc'121 then
      let t'120 ← PMem.ldF32 (((this + 32) + ((Int32.toInt64 ((7 : Int32))) * 24).toUInt64) + 16)
      sc'121 := (decide ((jerk_time * (Binary32.ofBits 0x41400000 /- 12 -/)) < (L / t'120)))
    if sc'121 then
      let t'122 ← PMem.ldF32 this
      let t'123 ← PMem.ldF32 (this + 4)
      let t'124 ← PMem.ldF32 (this + 20)
      let t'125 ← PMem.ldF32 (this + 8)
      let t'126 ← PMem.ldF32 (((this + 32) + ((Int32.toInt64 ((7 : Int32))) * 24).toUInt64) + 16)
      SCurve.calculate_path t'122 t'123 t'124 t'125 t'126 (L * (Binary32.ofBits 0x3f000000 /- 1/2 -/)) (fp + 104) (fp + 112) (fp + 136) (fp + 128) (fp + 120)
      let t'127 ← PMem.ldF32 (fp + 104)
      let t'128 := -t'127
      PMem.stF32 (fp + 104) t'128
    else
      let t'129 ← PMem.ldF32 (this + 20)
      let t'130 ← PMem.ldF32 (((this + 32) + ((Int32.toInt64 ((7 : Int32))) * 24).toUInt64) + 16)
      let mut sc'132 := (decide (t'129 > t'130))
      if sc'132 then
        let t'131 ← PMem.ldF32 (((this + 32) + ((Int32.toInt64 ((7 : Int32))) * 24).toUInt64) + 16)
        sc'132 := (decide ((L / (jerk_time * (Binary32.ofBits 0x41400000 /- 12 -/))) > t'131))
      if sc'132 then
        PMem.stF32 (fp + 148) (L / (jerk_time * (Binary32.ofBits 0x41400000 /- 12 -/)))
        let t'133 ← MIN'float_float (this + 20) (fp + 148)
        let t'134 ← PMem.ldF32 t'133
        let mut Vm : Binary32 := t'134
        let t'135 ← PMem.ldF32 this
        let t'136 ← PMem.ldF32 (this + 4)
        let t'137 ← PMem.ldF32 (((this + 32) + ((Int32.toInt64 ((7 : Int32))) * 24).toUInt64) + 16)
        let t'138 ← PMem.ldF32 (this + 8)
        SCurve.calculate_path t'135 t'136 t'137 t'138 Vm (L * (Binary32.ofBits 0x3f000000 /- 1/2 -/)) (fp + 104) (fp + 112) (fp + 120) (fp + 128) (fp + 136)
    PMem.stU8 (fp + 152) (Int8.toUInt8 (Int32.toInt8 (((7 : Int32) + (1 : Int32)))))
    let t'139 ← PMem.ldF32 (fp + 104)
    let t'140 ← is_zero t'139
    let mut sc'143 := !t'140
    if sc'143 then
      let t'141 ← PMem.ldF32 (fp + 120)
      let t'142 ← is_negative'float t'141
      sc'143 := !t'142
    let mut sc'146 := sc'143
    if sc'146 then
      let t'144 ← PMem.ldF32 (fp + 128)
      let t'145 ← is_negative'float t'144
      sc'146 := !t'145
    let mut sc'149 := sc'146
    if sc'149 then
      let t'147 ← PMem.ldF32 (fp + 136)
      let t'148 ← is_negative'float t'147
      sc'149 := !t'148
    if sc'149 then
      let t'150 ← PMem.ldF32 (fp + 112)
      let t'151 ← PMem.ldF32 (fp + 104)
      let t'152 ← PMem.ldF32 (fp + 120)
      SCurve.add_segments_jerk this (fp + 152) t'150 t'151 t'152
      let t'153 ← PMem.ldF32 (fp + 128)
      SCurve.add_segment_const_jerk this (fp + 152) t'153 (Binary32.ofBits 0x00000000 /- 0 -/)
      let t'154 ← PMem.ldF32 (fp + 112)
      let t'155 ← PMem.ldF32 (fp + 104)
      let t'156 ← PMem.ldF32 (fp + 136)
      SCurve.add_segments_jerk this (fp + 152) t'154 (-t'155) t'156
      let t'157 := (Binary32.ofBits 0x00000000 /- 0 -/)
      PMem.stF32 (((this + 32) + ((Int32.toInt64 ((14 : Int32))) * 24).toUInt64) + 12) t'157
  PMem.stU8 (fp + 160) (Int8.toUInt8 (Int32.toInt8 ((15 : Int32))))
  let t'158 ← MIN'float_float (fp + 8) (((this + 32) + ((Int32.toInt64 ((14 : Int32))) * 24).toUInt64) + 16)
  let t'159 ← PMem.ldF32 t'158
  PMem.stF32 (fp + 8) t'159
  SCurve.add_segment_const_jerk this (fp + 160) (Binary32.ofBits 0x00000000 /- 0 -/) (Binary32.ofBits 0x00000000 /- 0 -/)
  let t'160 ← PMem.ldF32 (fp + 8)
  let t'161 ← PMem.ldF32 (((this + 32) + ((Int32.toInt64 ((14 : Int32))) * 24).toUInt64) + 16)
  if (decide (t'160 < t'161)) then
    let t'162 ← PMem.ldF32 this
    let t'163 ← PMem.ldF32 (this + 4)
    let t'164 ← PMem.ldF32 (fp + 8)
    let t'165 ← PMem.ldF32 (this + 8)
    let t'166 ← PMem.ldF32 (((this + 32) + ((Int32.toInt64 ((15 : Int32))) * 24).toUInt64) + 16)
    let t'167 ← PMem.ldF32 (((this + 32) + ((Int32.toInt64 ((15 : Int32))) * 24).toUInt64) + 20)
    SCurve.calculate_path t'162 t'163 t'164 t'165 t'166 (Pend - t'167) (fp + 168) (fp + 176) (fp + 184) (fp + 192) (fp + 200)
    let t'168 ← PMem.ldF32 (fp + 176)
    let t'169 ← PMem.ldF32 (fp + 168)
    let t'170 ← PMem.ldF32 (fp + 200)
    SCurve.add_segments_jerk this (fp + 160) t'168 (-t'169) t'170
    let t'171 ← PMem.ldF32 (fp + 192)
    SCurve.add_segment_const_jerk this (fp + 160) t'171 (Binary32.ofBits 0x00000000 /- 0 -/)
    let t'172 ← PMem.ldF32 (fp + 176)
    let t'173 ← PMem.ldF32 (fp + 168)
    let t'174 ← PMem.ldF32 (fp + 184)
    SCurve.add_segments_jerk this (fp + 160) t'172 t'173 t'174
  else
    SCurve.fill_empty_segments this (Int8.toUInt8 (Int32.toInt8 (((15 : Int32) + (1 : Int32))))) (Int8.toUInt8 (Int32.toInt8 ((22 : Int32)))) (Int8.toUInt8 (Int32.toInt8 ((15 : Int32))))
  let t'175 := (Binary32.ofBits 0x00000000 /- 0 -/)
  PMem.stF32 (((this + 32) + ((Int32.toInt64 ((22 : Int32))) * 24).toUInt64) + 12) t'175
  PMem.stF32 (fp + 204) (Binary32.ofBits 0x00000000 /- 0 -/)
  let t'176 ← MAX'float_float (fp + 204) (((this + 32) + ((Int32.toInt64 ((22 : Int32))) * 24).toUInt64) + 16)
  let t'177 ← PMem.ldF32 t'176
  PMem.stF32 (((this + 32) + ((Int32.toInt64 ((22 : Int32))) * 24).toUInt64) + 16) t'177
  SCurve.extend_const_vel_to this Pend
  let t'178 ← SCurve.valid this
  if !t'178 then
    SCurve.debug this
    SCurve.init this
  return ()

def SCurve.set_speed_max (this : UInt64) (speed_xy : Binary32) (speed_up : Binary32) (speed_down : Binary32) : PMem.M Unit := do
  let fp ← PMem.enter 208
  let r ← SCurve.set_speed_max.body fp this speed_xy speed_up speed_down
  PMem.leave fp
  return r

/-- C++ `Vector3<double>::Vector3 : void (const Vector3<double> &) noexcept`, `vector3.h:72-?`. -/
def Vector3'double.Vector3'4 (this : UInt64) (arg : UInt64) : PMem.M Unit := do
  let t'1 ← PMem.ldF64 arg
  PMem.stF64 (this + 0) t'1
  let t'2 ← PMem.ldF64 (arg + 8)
  PMem.stF64 (this + 8) t'2
  let t'3 ← PMem.ldF64 (arg + 16)
  PMem.stF64 (this + 16) t'3
  return ()

/-- C++ `SplineCurve::get_destination_speed_max : float () const`, `AP_Common.h:33-?`. -/
def SplineCurve.get_destination_speed_max (this : UInt64) : PMem.M Binary32 := do
  let t'1 ← PMem.ldF32 (this + 196)
  return t'1

/-- C++ `SplineCurve::set_destination_speed_max : void (float)`, `AP_Common.h:34-?`. -/
def SplineCurve.set_destination_speed_max.body (fp : UInt64) (this : UInt64) (destination_speed_max : Binary32) : PMem.M Unit := do
  PMem.stF32 (fp + 0) destination_speed_max
  let t'1 ← MIN'float_float (this + 196) (fp + 0)
  let t'2 ← PMem.ldF32 t'1
  PMem.stF32 (this + 196) t'2
  return ()

def SplineCurve.set_destination_speed_max (this : UInt64) (destination_speed_max : Binary32) : PMem.M Unit := do
  let fp ← PMem.enter 4
  let r ← SplineCurve.set_destination_speed_max.body fp this destination_speed_max
  PMem.leave fp
  return r

/-- `SplineCurve.get_destination_vel` as a pure function of its arguments (it reads and writes no memory). -/
def SplineCurve.get_destination_vel.pure' (this : UInt64) : Id UInt64 := do
  return (this + 60)

/-- C++ `SplineCurve::get_destination_vel : const Vector3f &()`, `AP_Common.h:27-?`. -/
def SplineCurve.get_destination_vel (this : UInt64) : PMem.M UInt64 :=
  pure (_root_.Vehicle_lib.SplineCurve.get_destination_vel.pure' this)

/-- `sq'double_double_double` as a pure function of its arguments (it reads and writes no memory). -/
def sq'double_double_double.pure' (first : Binary64) (parameters : Binary64) (parameters'2 : Binary64) : Id Binary64 := do
  let mut first := first
  let mut parameters := parameters
  let mut parameters'2 := parameters'2
  let t'1 ← _root_.Vehicle_lib.sq'double.pure' first
  let t'2 ← _root_.Vehicle_lib.sq'double_double.pure' parameters parameters'2
  return (t'1 + t'2)

/-- C++ `sq : ftype (const double, const double, const double)`, `AP_Math.h:?-279`. -/
def sq'double_double_double (first : Binary64) (parameters : Binary64) (parameters'2 : Binary64) : PMem.M Binary64 :=
  pure (_root_.Vehicle_lib.sq'double_double_double.pure' first parameters parameters'2)

/-- `norm'double_double_double` as a pure function of its arguments (it reads and writes no memory). -/
def norm'double_double_double.pure' (first : Binary64) (second : Binary64) (parameters : Binary64) : Id Binary64 := do
  let mut first := first
  let mut second := second
  let mut parameters := parameters
  let t'1 ← _root_.Vehicle_lib.sq'double_double_double.pure' first second parameters
  return (Binary64.sqrt t'1)

/-- C++ `norm : ftype (const double, const double, const double)`, `ftype.h:?-289`. -/
def norm'double_double_double (first : Binary64) (second : Binary64) (parameters : Binary64) : PMem.M Binary64 :=
  pure (_root_.Vehicle_lib.norm'double_double_double.pure' first second parameters)

/-- C++ `Vector3<double>::length : double () const`, `vector3.cpp:324-327`. -/
def Vector3'double.length (this : UInt64) : PMem.M Binary64 := do
  let t'1 ← PMem.ldF64 this
  let t'2 ← PMem.ldF64 (this + 8)
  let t'3 ← PMem.ldF64 (this + 16)
  let t'4 ← norm'double_double_double t'1 t'2 t'3
  return t'4

/-- C++ `kinematic_limit : float (Vector3f, float, float, float)`, `control.cpp:734-740`. -/
def kinematic_limit'2 (direction : UInt64) (max_xy : Binary32) (max_z_neg : Binary32) (max_z_pos : Binary32) : PMem.M Binary32 := do
  let mut max_xy := max_xy
  let mut max_z_neg := max_z_neg
  let mut max_z_pos := max_z_pos
  let t'1 ← Vector3'float.xy direction
  let t'2 ← Vector2'float.length t'1
  let mut dir_xy : Binary32 := t'2
  let t'3 ← PMem.ldF32 (direction + 8)
  let t'4 ← kinematic_limit dir_xy t'3 max_xy max_z_neg max_z_pos
  return t'4

/-- C++ `Vector3<float>::normalized : Vector3<float> () const`, `vector3.h:235-238`. -/
def Vector3'float.normalized.body (fp : UInt64) (this : UInt64) (sret : UInt64) : PMem.M Unit := do
  let t'1 ← Vector3'float.length this
  Vector3'float.operator_'3 this (fp + 0) t'1
  let t'2 := (fp + 0)
  Vector3'float.Vector3'3 sret t'2
  return ()

def Vector3'float.normalized (this : UInt64) (sret : UInt64) : PMem.M Unit := do
  let fp ← PMem.enter 12
  let r ← Vector3'float.normalized.body fp this sret
  PMem.leave fp
  return r

/-- C++ `Vector3<float>::dot : float (const Vector3<float> &) const`, `vector3.h:156-158`. -/
def Vector3'float.dot (this : UInt64) (v : UInt64) : PMem.M Binary32 := do
  let t'1 ← Vector3'float.operator_'4 this v
  return t'1

/-- C++ `Vector3<float>::operator+ : Vector3<float> (const Vector3<float> &) const`, `vector3.cpp:401-404`. -/
def Vector3'float.operator_'5.body (fp : UInt64) (this : UInt64) (sret : UInt64) (v : UInt64) : PMem.M Unit := do
  let t'1 ← PMem.ldF32 this
  let t'2 ← PMem.ldF32 v
  let t'3 ← PMem.ldF32 (this + 4)
  let t'4 ← PMem.ldF32 (v + 4)
  let t'5 ← PMem.ldF32 (this + 8)
  let t'6 ← PMem.ldF32 (v + 8)
  Vector3'float.Vector3 (fp + 0) (t'1 + t'2) (t'3 + t'4) (t'5 + t'6)
  Vector3'float.Vector3'3 sret (fp + 0)
  return ()

def Vector3'float.operator_'5 (this : UInt64) (sret : UInt64) (v : UInt64) : PMem.M Unit := do
  let fp ← PMem.enter 12
  let r ← Vector3'float.operator_'5.body fp this sret v
  PMem.leave fp
  return r

/-- C++ `Vector3<double>::operator* : Vector3<double> (const double) const`, `vector3.cpp:389-392`. -/
def Vector3'double.operator_'3.body (fp : UInt64) (this : UInt64) (sret : UInt64) (num : Binary64) : PMem.M Unit := do
  let mut num := num
  let t'1 ← PMem.ldF64 this
  let t'2 ← PMem.ldF64 (this + 8)
  let t'3 ← PMem.ldF64 (this + 16)
  Vector3'double.Vector3'3 (fp + 0) (t'1 * num) (t'2 * num) (t'3 * num)
  Vector3'double.Vector3'2 sret (fp + 0)
  return ()

def Vector3'double.operator_'3 (this : UInt64) (sret : UInt64) (num : Binary64) : PMem.M Unit := do
  let fp ← PMem.enter 24
  let r ← Vector3'double.operator_'3.body fp this sret num
  PMem.leave fp
  return r

/-- C++ `Vector3<double>::operator+ : Vector3<double> (const Vector3<double> &) const`, `vector3.cpp:401-404`. -/
def Vector3'double.operator_'4.body (fp : UInt64) (this : UInt64) (sret : UInt64) (v : UInt64) : PMem.M Unit := do
  let t'1 ← PMem.ldF64 this
  let t'2 ← PMem.ldF64 v
  let t'3 ← PMem.ldF64 (this + 8)
  let t'4 ← PMem.ldF64 (v + 8)
  let t'5 ← PMem.ldF64 (this + 16)
  let t'6 ← PMem.ldF64 (v + 16)
  Vector3'double.Vector3'3 (fp + 0) (t'1 + t'2) (t'3 + t'4) (t'5 + t'6)
  Vector3'double.Vector3'2 sret (fp + 0)
  return ()

def Vector3'double.operator_'4 (this : UInt64) (sret : UInt64) (v : UInt64) : PMem.M Unit := do
  let fp ← PMem.enter 24
  let r ← Vector3'double.operator_'4.body fp this sret v
  PMem.leave fp
  return r

/-- C++ `SplineCurve::calc_target_pos_vel : void (float, Vector3p &, Vector3f &, Vector3f &, Vector3f &)`, `SplineCurve.cpp:233-251`. -/
def SplineCurve.calc_target_pos_vel.body (fp : UInt64) (this : UInt64) (time : Binary32) (position : UInt64) (velocity : UInt64) (acceleration : UInt64) (jerk : UInt64) : PMem.M Unit := do
  let mut time := time
  let t'1 ← sq time
  let mut time_sq : Binary32 := t'1
  let mut time_cubed : Binary32 := (time_sq * time)
  Vector3'double.operator_'3 ((this + 72) + ((Int32.toInt64 ((1 : Int32))) * 24).toUInt64) (fp + 0) (Binary32.toBinary64 (time))
  let t'2 := (fp + 0)
  Vector3'double.operator_'4 ((this + 72) + ((Int32.toInt64 ((0 : Int32))) * 24).toUInt64) (fp + 24) t'2
  let t'3 := (fp + 24)
  Vector3'double.operator_'3 ((this + 72) + ((Int32.toInt64 ((2 : Int32))) * 24).toUInt64) (fp + 48) (Binary32.toBinary64 (time_sq))
  let t'4 := (fp + 48)
  Vector3'double.operator_'4 t'3 (fp + 72) t'4
  let t'5 := (fp + 72)
  Vector3'double.operator_'3 ((this + 72) + ((Int32.toInt64 ((3 : Int32))) * 24).toUInt64) (fp + 96) (Binary32.toBinary64 (time_cubed))
  let t'6 := (fp + 96)
  Vector3'double.operator_'4 t'5 (fp + 120) t'6
  let t'7 := (fp + 120)
  discard <| PMem.memcpy position t'7 24
  discard <| pure (position)
  Vector3'double.tofloat ((this + 72) + ((Int32.toInt64 ((1 : Int32))) * 24).toUInt64) (fp + 144)
  let t'8 := (fp + 144)
  Vector3'double.tofloat ((this + 72) + ((Int32.toInt64 ((2 : Int32))) * 24).toUInt64) (fp + 160)
  let t'9 := (fp + 160)
  Vector3'float.operator_ t'9 (fp + 176) (Binary64.toBinary32 ((Binary64.ofBits 0x4000000000000000 /- 2 -/)))
  let t'10 := (fp + 176)
  Vector3'float.operator_ t'10 (fp + 192) time
  let t'11 := (fp + 192)
  Vector3'float.operator_'5 t'8 (fp + 208) t'11
  let t'12 := (fp + 208)
  Vector3'double.tofloat ((this + 72) + ((Int32.toInt64 ((3 : Int32))) * 24).toUInt64) (fp + 224)
  let t'13 := (fp + 224)
  Vector3'float.operator_ t'13 (fp + 240) (Binary64.toBinary32 ((Binary64.ofBits 0x4008000000000000 /- 3 -/)))
  let t'14 := (fp + 240)
  Vector3'float.operator_ t'14 (fp + 256) time_sq
  let t'15 := (fp + 256)
  Vector3'float.operator_'5 t'12 (fp + 272) t'15
  let t'16 := (fp + 272)
  discard <| PMem.memcpy velocity t'16 12
  discard <| pure (velocity)
  Vector3'double.tofloat ((this + 72) + ((Int32.toInt64 ((2 : Int32))) * 24).toUInt64) (fp + 288)
  let t'17 := (fp + 288)
  Vector3'float.operator_ t'17 (fp + 304) (Binary64.toBinary32 ((Binary64.ofBits 0x4000000000000000 /- 2 -/)))
  let t'18 := (fp + 304)
  Vector3'double.tofloat ((this + 72) + ((Int32.toInt64 ((3 : Int32))) * 24).toUInt64) (fp + 320)
  let t'19 := (fp + 320)
  Vector3'float.operator_ t'19 (fp + 336) (Binary64.toBinary32 ((Binary64.ofBits 0x4018000000000000 /- 6 -/)))
  let t'20 := (fp + 336)
  Vector3'float.operator_ t'20 (fp + 352) time
  let t'21 := (fp + 352)
  Vector3'float.operator_'5 t'18 (fp + 368) t'21
  let t'22 := (fp + 368)
  discard <| PMem.memcpy acceleration t'22 12
  discard <| pure (acceleration)
  Vector3'double.tofloat ((this + 72) + ((Int32.toInt64 ((3 : Int32))) * 24).toUInt64) (fp + 384)
  let t'23 := (fp + 384)
  Vector3'float.operator_ t'23 (fp + 400) (Binary64.toBinary32 ((Binary64.ofBits 0x4018000000000000 /- 6 -/)))
  let t'24 := (fp + 400)
  discard <| PMem.memcpy jerk t'24 12
  discard <| pure (jerk)
  return ()

def SplineCurve.calc_target_pos_vel (this : UInt64) (time : Binary32) (position : UInt64) (velocity : UInt64) (acceleration : UInt64) (jerk : UInt64) : PMem.M Unit := do
  let fp ← PMem.enter 412
  let r ← SplineCurve.calc_target_pos_vel.body fp this time position velocity acceleration jerk
  PMem.leave fp
  return r

/-- C++ `SplineCurve::calc_dt_speed_max : void (float, float, float &, Vector3p &, Vector3f &, float &, float &)`, `SplineCurve.cpp:134-216`. -/
def SplineCurve.calc_dt_speed_max.body (fp : UInt64) (this : UInt64) (time : Binary32) (distance_delta : Binary32) (spline_dt : UInt64) (target_pos : UInt64) (spline_vel_unit : UInt64) (speed_max : UInt64) (accel_max : UInt64) : PMem.M Unit := do
  let mut time := time
  let mut distance_delta := distance_delta
  let t'1 := (Binary32.ofBits 0x00000000 /- 0 -/)
  PMem.stF32 spline_dt t'1
  Vector3'float.zero spline_vel_unit
  let t'2 := (Binary32.ofBits 0x00000000 /- 0 -/)
  PMem.stF32 speed_max t'2
  let t'3 := (Binary32.ofBits 0x00000000 /- 0 -/)
  PMem.stF32 accel_max t'3
  Vector3'float.Vector3'2 (fp + 0)
  Vector3'float.Vector3'2 (fp + 16)
  Vector3'float.Vector3'2 (fp + 32)
  SplineCurve.calc_target_pos_vel this time target_pos (fp + 0) (fp + 16) (fp + 32)
  let t'4 ← Vector3'float.is_zero (fp + 0)
  let mut sc'6 := t'4
  if sc'6 then
    let t'5 ← Vector3'float.is_zero (fp + 16)
    sc'6 := t'5
  let mut sc'8 := sc'6
  if sc'8 then
    let t'7 ← Vector3'float.is_zero (fp + 32)
    sc'8 := t'7
  if sc'8 then
    PMem.stB (this + 200) true
    return ()
  let t'9 ← Vector3'float.length (fp + 0)
  let mut spline_vel_length : Binary32 := t'9
  let t'10 ← is_zero spline_vel_length
  if t'10 then
    let t'11 ← Vector3'float.length_squared (fp + 16)
    let t'12 ← is_zero t'11
    if t'12 then
      Vector3'float.normalized (fp + 32) (fp + 48)
      let t'13 := (fp + 48)
      discard <| PMem.memcpy spline_vel_unit t'13 12
      discard <| pure (spline_vel_unit)
      let t'14 ← Vector3'float.length (fp + 32)
      let t'15 := (Musl.powf.powf (((Binary32.ofBits 0x40c00000 /- 6 -/) * distance_delta) / t'14) ((Binary32.ofBits 0x3f800000 /- 1 -/) / (Binary32.ofBits 0x40400000 /- 3 -/)))
      PMem.stF32 spline_dt t'15
    else
      Vector3'float.normalized (fp + 16) (fp + 64)
      let t'16 := (fp + 64)
      discard <| PMem.memcpy spline_vel_unit t'16 12
      discard <| pure (spline_vel_unit)
      let t'17 ← Vector3'float.length (fp + 16)
      let t'18 ← safe_sqrt'float (((Binary32.ofBits 0x40000000 /- 2 -/) * distance_delta) / t'17)
      PMem.stF32 spline_dt t'18
  else
    Vector3'float.normalized (fp + 0) (fp + 80)
    let t'19 := (fp + 80)
    discard <| PMem.memcpy spline_vel_unit t'19 12
    discard <| pure (spline_vel_unit)
    let t'20 := (distance_delta / spline_vel_length)
    PMem.stF32 spline_dt t'20
  let t'21 ← Vector3'float.dot (fp + 16) spline_vel_unit
  let mut spline_accel_tangent_length : Binary32 := t'21
  Vector3'float.operator_ spline_vel_unit (fp + 112) spline_accel_tangent_length
  let t'22 := (fp + 112)
  Vector3'float.operator_'2 (fp + 16) (fp + 128) t'22
  let t'23 := (fp + 128)
  Vector3'float.Vector3'3 (fp + 96) t'23
  let t'24 ← Vector3'float.length (fp + 96)
  let mut spline_accel_norm_length : Binary32 := t'24
  Vector3'float.Vector3'4 (fp + 144) spline_vel_unit
  let t'25 ← PMem.ldF32 (this + 172)
  let t'26 ← PMem.ldF32 (this + 176)
  let t'27 ← PMem.ldF32 (this + 180)
  let t'28 ← kinematic_limit'2 (fp + 144) t'25 t'26 t'27
  let mut tangential_speed_max : Binary32 := t'28
  Vector3'float.Vector3'4 (fp + 160) (fp + 96)
  let t'29 ← PMem.ldF32 (this + 184)
  let t'30 ← PMem.ldF32 (this + 188)
  let t'31 ← PMem.ldF32 (this + 188)
  let t'32 ← kinematic_limit'2 (fp + 160) t'29 t'30 t'31
  let mut accel_norm_max : Binary32 := ((Binary32.ofBits 0x3f000000 /- 1/2 -/) * t'32)
  let t'33 ← is_zero tangential_speed_max
  if t'33 then
    PMem.stB (this + 200) true
    return ()
  let t'34 ← is_positive'float accel_norm_max
  let mut sc'36 := t'34
  if sc'36 then
    let t'35 ← is_positive'float spline_accel_norm_length
    sc'36 := t'35
  let mut sc'38 := sc'36
  if sc'38 then
    let t'37 ← is_positive'float spline_vel_length
    sc'38 := t'37
  let mut sc'40 := sc'38
  if sc'40 then
    let t'39 ← sq (spline_vel_length / tangential_speed_max)
    sc'40 := (decide ((spline_accel_norm_length / accel_norm_max) > t'39))
  if sc'40 then
    let t'41 ← safe_sqrt'float (spline_accel_norm_length / accel_norm_max)
    let t'42 := (spline_vel_length / t'41)
    PMem.stF32 speed_max t'42
  else
    PMem.stF32 speed_max tangential_speed_max
  Vector3'float.Vector3'4 (fp + 176) spline_vel_unit
  let t'43 ← PMem.ldF32 (this + 184)
  let t'44 ← PMem.ldF32 (this + 188)
  let t'45 ← PMem.ldF32 (this + 188)
  let t'46 ← kinematic_limit'2 (fp + 176) t'43 t'44 t'45
  let t'47 := ((Binary32.ofBits 0x3f000000 /- 1/2 -/) * t'46)
  PMem.stF32 accel_max t'47
  let t'48 ← PMem.ldF32 accel_max
  let t'49 ← is_zero t'48
  if t'49 then
    PMem.stB (this + 200) true
    return ()
  Vector3'double.operator_ (this + 24) (fp + 192) target_pos
  let t'50 := (fp + 192)
  let t'51 ← Vector3'double.length t'50
  let mut dist : Binary32 := Binary64.toBinary32 (t'51)
  let t'52 ← PMem.ldF32 accel_max
  let t'53 ← PMem.ldF32 (this + 196)
  let t'54 ← sq t'53
  let t'55 ← PMem.ldF32 accel_max
  let t'56 ← safe_sqrt'float (((Binary32.ofBits 0x40000000 /- 2 -/) * t'52) * (dist + (t'54 / ((Binary32.ofBits 0x40000000 /- 2 -/) * t'55))))
  PMem.stF32 (fp + 216) t'56
  let t'57 ← MIN'float_float speed_max (fp + 216)
  let t'58 ← PMem.ldF32 t'57
  PMem.stF32 speed_max t'58
  return ()

def SplineCurve.calc_dt_speed_max (this : UInt64) (time : Binary32) (distance_delta : Binary32) (spline_dt : UInt64) (target_pos : UInt64) (spline_vel_unit : UInt64) (speed_max : UInt64) (accel_max : UInt64) : PMem.M Unit := do
  let fp ← PMem.enter 220
  let r ← SplineCurve.calc_dt_speed_max.body fp this time distance_delta spline_dt target_pos spline_vel_unit speed_max accel_max
  PMem.leave fp
  return r

/-- C++ `Vector3<double>::operator* : double (const Vector3<double> &) const`, `vector3.cpp:318-321`. -/
def Vector3'double.operator_'5 (this : UInt64) (v : UInt64) : PMem.M Binary64 := do
  let t'1 ← PMem.ldF64 this
  let t'2 ← PMem.ldF64 v
  let t'3 ← PMem.ldF64 (this + 8)
  let t'4 ← PMem.ldF64 (v + 8)
  let t'5 ← PMem.ldF64 (this + 16)
  let t'6 ← PMem.ldF64 (v + 16)
  return (((t'1 * t'2) + (t'3 * t'4)) + (t'5 * t'6))

/-- C++ `Vector3<double>::length_squared : double () const`, `vector3.h:211-214`. -/
def Vector3'double.length_squared (this : UInt64) : PMem.M Binary64 := do
  let t'1 ← Vector3'double.operator_'5 this this
  return t'1

/-- C++ `Vector3<float>::todouble : Vector3<double> () const`, `vector3.h:280-282`. -/
def Vector3'float.todouble.body (fp : UInt64) (this : UInt64) (sret : UInt64) : PMem.M Unit := do
  let t'1 ← PMem.ldF32 this
  let t'2 ← PMem.ldF32 (this + 4)
  let t'3 ← PMem.ldF32 (this + 8)
  Vector3'double.Vector3'3 (fp + 0) (Binary32.toBinary64 (t'1)) (Binary32.toBinary64 (t'2)) (Binary32.toBinary64 (t'3))
  Vector3'double.Vector3'2 sret (fp + 0)
  return ()

def Vector3'float.todouble (this : UInt64) (sret : UInt64) : PMem.M Unit := do
  let fp ← PMem.enter 24
  let r ← Vector3'float.todouble.body fp this sret
  PMem.leave fp
  return r

/-- C++ `SplineCurve::update_solution : void (const Vector3p &, const Vector3p &, const Vector3f &, const Vector3f &)`, `SplineCurve.cpp:220-226`. -/
def SplineCurve.update_solution.body (fp : UInt64) (this : UInt64) (origin : UInt64) (dest : UInt64) (origin_vel : UInt64) (dest_vel : UInt64) : PMem.M Unit := do
  discard <| PMem.memcpy ((this + 72) + ((Int32.toInt64 ((0 : Int32))) * 24).toUInt64) origin 24
  discard <| pure (((this + 72) + ((Int32.toInt64 ((0 : Int32))) * 24).toUInt64))
  Vector3'float.todouble origin_vel (fp + 0)
  let t'1 := (fp + 0)
  discard <| PMem.memcpy ((this + 72) + ((Int32.toInt64 ((1 : Int32))) * 24).toUInt64) t'1 24
  discard <| pure (((this + 72) + ((Int32.toInt64 ((1 : Int32))) * 24).toUInt64))
  Vector3'double.operator_'2 origin (fp + 24)
  let t'2 := (fp + 24)
  Vector3'double.operator_'3 t'2 (fp + 48) (Binary64.ofBits 0x4008000000000000 /- 3 -/)
  let t'3 := (fp + 48)
  Vector3'float.todouble origin_vel (fp + 72)
  let t'4 := (fp + 72)
  Vector3'double.operator_'3 t'4 (fp + 96) (Binary64.ofBits 0x4000000000000000 /- 2 -/)
  let t'5 := (fp + 96)
  Vector3'double.operator_ t'3 (fp + 120) t'5
  let t'6 := (fp + 120)
  Vector3'double.operator_'3 dest (fp + 144) (Binary64.ofBits 0x4008000000000000 /- 3 -/)
  let t'7 := (fp + 144)
  Vector3'double.operator_'4 t'6 (fp + 168) t'7
  let t'8 := (fp + 168)
  Vector3'float.todouble dest_vel (fp + 192)
  let t'9 := (fp + 192)
  Vector3'double.operator_ t'8 (fp + 216) t'9
  let t'10 := (fp + 216)
  discard <| PMem.memcpy ((this + 72) + ((Int32.toInt64 ((2 : Int32))) * 24).toUInt64) t'10 24
  discard <| pure (((this + 72) + ((Int32.toInt64 ((2 : Int32))) * 24).toUInt64))
  Vector3'double.operator_'3 origin (fp + 240) (Binary64.ofBits 0x4000000000000000 /- 2 -/)
  let t'11 := (fp + 240)
  Vector3'float.todouble origin_vel (fp + 264)
  let t'12 := (fp + 264)
  Vector3'double.operator_'4 t'11 (fp + 288) t'12
  let t'13 := (fp + 288)
  Vector3'double.operator_'3 dest (fp + 312) (Binary64.ofBits 0x4000000000000000 /- 2 -/)
  let t'14 := (fp + 312)
  Vector3'double.operator_ t'13 (fp + 336) t'14
  let t'15 := (fp + 336)
  Vector3'float.todouble dest_vel (fp + 360)
  let t'16 := (fp + 360)
  Vector3'double.operator_'4 t'15 (fp + 384) t'16
  let t'17 := (fp + 384)
  discard <| PMem.memcpy ((this + 72) + ((Int32.toInt64 ((3 : Int32))) * 24).toUInt64) t'17 24
  discard <| pure (((this + 72) + ((Int32.toInt64 ((3 : Int32))) * 24).toUInt64))
  return ()

def SplineCurve.update_solution (this : UInt64) (origin : UInt64) (dest : UInt64) (origin_vel : UInt64) (dest_vel : UInt64) : PMem.M Unit := do
  let fp ← PMem.enter 408
  let r ← SplineCurve.update_solution.body fp this origin dest origin_vel dest_vel
  PMem.leave fp
  return r

/-- C++ `SplineCurve::set_origin_and_destination : void (const Vector3p &, const Vector3p &, const Vector3f &, const Vector3f &)`, `SplineCurve.cpp:48-97`. -/
def SplineCurve.set_origin_and_destination.body (fp : UInt64) (this : UInt64) (origin : UInt64) (destination : UInt64) (origin_vel : UInt64) (destination_vel : UInt64) : PMem.M Unit := do
  discard <| PMem.memcpy this origin 24
  discard <| pure (this)
  discard <| PMem.memcpy (this + 24) destination 24
  discard <| pure ((this + 24))
  Vector3'double.operator_ destination (fp + 0) origin
  let t'1 := (fp + 0)
  let t'2 ← Vector3'double.length_squared t'1
  let t'3 ← is_zero'2 t'2
  PMem.stB (this + 201) t'3
  let t'4 ← PMem.ldB (this + 201)
  if t'4 then
    let t'5 := (Binary32.ofBits 0x3f800000 /- 1 -/)
    PMem.stF32 (this + 168) t'5
    Vector3'float.zero (this + 48)
    Vector3'float.zero (this + 60)
    PMem.stB (this + 200) true
    let t'6 := (Binary32.ofBits 0x00000000 /- 0 -/)
    PMem.stF32 (this + 192) t'6
    let t'7 := (Binary32.ofBits 0x00000000 /- 0 -/)
    PMem.stF32 (this + 196) t'7
    return ()
  discard <| PMem.memcpy (this + 48) origin_vel 12
  discard <| pure ((this + 48))
  discard <| PMem.memcpy (this + 60) destination_vel 12
  discard <| pure ((this + 60))
  PMem.stB (this + 200) false
  let t'8 := (Binary32.ofBits 0x00000000 /- 0 -/)
  PMem.stF32 (this + 168) t'8
  let t'9 ← Vector3'float.length (this + 48)
  let t'10 ← Vector3'float.length (this + 60)
  let mut vel_len : Binary32 := (t'9 + t'10)
  Vector3'double.operator_ (this + 24) (fp + 24) this
  let t'11 := (fp + 24)
  let t'12 ← Vector3'double.length t'11
  let mut pos_len : Binary32 := Binary64.toBinary32 ((t'12 * (Binary32.toBinary64 ((Binary32.ofBits 0x40800000 /- 4 -/)))))
  if (decide (vel_len > pos_len)) then
    let mut vel_scaling : Binary32 := (pos_len / vel_len)
    Vector3'float.operator_ (this + 48) (fp + 48) vel_scaling
    let t'13 := (fp + 48)
    Vector3'float.operator_ (this + 60) (fp + 64) vel_scaling
    let t'14 := (fp + 64)
    SplineCurve.update_solution this this (this + 24) t'13 t'14
  else
    SplineCurve.update_solution this this (this + 24) (this + 48) (this + 60)
  Vector3'double.Vector3 (fp + 80)
  Vector3'float.Vector3'2 (fp + 104)
  SplineCurve.calc_dt_speed_max this (Binary32.ofBits 0x00000000 /- 0 -/) (Binary32.ofBits 0x00000000 /- 0 -/) (fp + 120) (fp + 80) (fp + 104) (this + 192) (fp + 128)
  let t'15 ← Vector3'float.is_zero (this + 60)
  if t'15 then
    let t'16 := (Binary32.ofBits 0x00000000 /- 0 -/)
    PMem.stF32 (this + 196) t'16
  else
    SplineCurve.calc_dt_speed_max this (Binary32.ofBits 0x3f800000 /- 1 -/) (Binary32.ofBits 0x00000000 /- 0 -/) (fp + 120) (fp + 80) (fp + 104) (this + 196) (fp + 128)
  return ()

def SplineCurve.set_origin_and_destination (this : UInt64) (origin : UInt64) (destination : UInt64) (origin_vel : UInt64) (destination_vel : UInt64) : PMem.M Unit := do
  let fp ← PMem.enter 132
  let r ← SplineCurve.set_origin_and_destination.body fp this origin destination origin_vel destination_vel
  PMem.leave fp
  return r

/-- C++ `SplineCurve::get_origin_speed_max : float () const`, `AP_Common.h:30-?`. -/
def SplineCurve.get_origin_speed_max (this : UInt64) : PMem.M Binary32 := do
  let t'1 ← PMem.ldF32 (this + 192)
  return t'1

/-- C++ `Vector2<double>::tofloat : Vector2<float> () const`, `vector2.h:178-180`. -/
def Vector2'double.tofloat.body (fp : UInt64) (this : UInt64) (sret : UInt64) : PMem.M Unit := do
  let t'1 ← PMem.ldF64 this
  let t'2 ← PMem.ldF64 (this + 8)
  Vector2'float.Vector2'2 (fp + 0) (Binary64.toBinary32 (t'1)) (Binary64.toBinary32 (t'2))
  Vector2'float.Vector2'3 sret (fp + 0)
  return ()

def Vector2'double.tofloat (this : UInt64) (sret : UInt64) : PMem.M Unit := do
  let fp ← PMem.enter 8
  let r ← Vector2'double.tofloat.body fp this sret
  PMem.leave fp
  return r

/-- C++ `get_horizontal_distance : float (const Vector2<float> &, const Vector2<float> &)`, `location.h:15-18`. -/
def get_horizontal_distance'float.body (fp : UInt64) (origin : UInt64) (destination : UInt64) : PMem.M Binary32 := do
  Vector2'float.operator_ destination (fp + 0) origin
  let t'1 := (fp + 0)
  let t'2 ← Vector2'float.length t'1
  return t'2

def get_horizontal_distance'float (origin : UInt64) (destination : UInt64) : PMem.M Binary32 := do
  let fp ← PMem.enter 8
  let r ← get_horizontal_distance'float.body fp origin destination
  PMem.leave fp
  return r

/-- C++ `Vector3<float>::operator*= : Vector3<float> &(const float)`, `vector3.cpp:343-347`. -/
def Vector3'float.operator__'2 (this : UInt64) (num : Binary32) : PMem.M UInt64 := do
  let mut num := num
  let t'1 ← PMem.ldF32 this
  let t'2 := (t'1 * num)
  PMem.stF32 this t'2
  let t'3 := (this + 4)
  let t'4 ← PMem.ldF32 t'3
  let t'5 := (t'4 * num)
  PMem.stF32 t'3 t'5
  let t'6 := (this + 8)
  let t'7 ← PMem.ldF32 t'6
  let t'8 := (t'7 * num)
  PMem.stF32 t'6 t'8
  return this

/-- `is_equal'double_double` as a pure function of its arguments (it reads and writes no memory). -/
def is_equal'double_double.pure' (v_1 : Binary64) (v_2 : Binary64) : Id Bool := do
  let mut v_1 := v_1
  let mut v_2 := v_2
  if false then
    return (decide ((Binary64.abs (v_1 - v_2)) < (Binary64.ofBits 0x3cb0000000000000)))
  return (decide ((Binary32.abs (Binary64.toBinary32 ((v_1 - v_2)))) < (Binary32.ofBits 0x34000000)))

/-- C++ `is_equal : typename std::enable_if<std::is_floating_point<typename std::common_type<double, double>::type>::value, bool>::type (const double, const double)`, `AP_Math.cpp:25-41`. -/
def is_equal'double_double (v_1 : Binary64) (v_2 : Binary64) : PMem.M Bool :=
  pure (_root_.Vehicle_lib.is_equal'double_double.pure' v_1 v_2)

/-- C++ `Vector2<float>::is_zero : bool () const`, `vector2.h:295-297`. -/
def Vector2'float.is_zero (this : UInt64) : PMem.M Bool := do
  let t'1 ← PMem.ldF32 this
  let t'2 ← _root_.Vehicle_lib.is_zero t'1
  let mut sc'5 := t'2
  if sc'5 then
    let t'3 ← PMem.ldF32 (this + 4)
    let t'4 ← _root_.Vehicle_lib.is_zero t'3
    sc'5 := t'4
  return sc'5

/-- `radians'2` as a pure function of its arguments (it reads and writes no memory). -/
def radians'2.pure' (deg : Int32) : Id Binary32 := do
  let mut deg := deg
  return ((Int32.toBinary32 (deg)) * ((Binary64.toBinary32 ((Binary64.ofBits 0x400921fb54442d18 /- 31415926535897931/10000000000000000 -/))) / (Binary32.ofBits 0x43340000 /- 180 -/)))

/-- C++ `radians : float (int)`, `AP_Math.h:237-240`. -/
def radians'2 (deg : Int32) : PMem.M Binary32 :=
  pure (_root_.Vehicle_lib.radians'2.pure' deg)

/-- C++ `sqrt_controller : float (float, float, float, float)`, `control.cpp:575-610`. -/
def sqrt_controller.body (fp : UInt64) (error : Binary32) (p : Binary32) (second_ord_lim : Binary32) (dt : Binary32) : PMem.M Binary32 := do
  PMem.stF32 (fp + 0) error
  let mut p := p
  let mut second_ord_lim := second_ord_lim
  let mut dt := dt
  let mut correction_rate : Binary32 := default  -- uninitialized in C
  let t'1 ← is_negative'float second_ord_lim
  let mut sc'3 := t'1
  if !sc'3 then
    let t'2 ← is_zero second_ord_lim
    sc'3 := t'2
  if sc'3 then
    let t'4 ← PMem.ldF32 (fp + 0)
    let t'5 := (t'4 * p)
    correction_rate := t'5
  else
    let t'6 ← is_zero p
    if t'6 then
      let t'7 ← PMem.ldF32 (fp + 0)
      let t'8 ← is_positive'float t'7
      if t'8 then
        let t'9 ← PMem.ldF32 (fp + 0)
        let t'10 ← safe_sqrt'float (((Binary64.toBinary32 ((Binary64.ofBits 0x4000000000000000 /- 2 -/))) * second_ord_lim) * t'9)
        correction_rate := t'10
      else
        let t'11 ← PMem.ldF32 (fp + 0)
        let t'12 ← is_negative'float t'11
        if t'12 then
          let t'13 ← PMem.ldF32 (fp + 0)
          let t'14 ← safe_sqrt'float (((Binary64.toBinary32 ((Binary64.ofBits 0x4000000000000000 /- 2 -/))) * second_ord_lim) * (-t'13))
          let t'15 := -t'14
          correction_rate := t'15
        else
          let t'16 := Binary64.toBinary32 ((Binary64.ofBits 0x0000000000000000 /- 0 -/))
          correction_rate := t'16
    else
      let t'17 ← sq p
      let mut linear_dist : Binary32 := (second_ord_lim / t'17)
      let t'18 ← PMem.ldF32 (fp + 0)
      if (decide (t'18 > linear_dist)) then
        let t'19 ← PMem.ldF32 (fp + 0)
        let t'20 ← safe_sqrt'float (((Binary64.toBinary32 ((Binary64.ofBits 0x4000000000000000 /- 2 -/))) * second_ord_lim) * (t'19 - (linear_dist / (Binary64.toBinary32 ((Binary64.ofBits 0x4000000000000000 /- 2 -/))))))
        correction_rate := t'20
      else
        let t'21 ← PMem.ldF32 (fp + 0)
        if (decide (t'21 < (-linear_dist))) then
          let t'22 ← PMem.ldF32 (fp + 0)
          let t'23 ← safe_sqrt'float (((Binary64.toBinary32 ((Binary64.ofBits 0x4000000000000000 /- 2 -/))) * second_ord_lim) * ((-t'22) - (linear_dist / (Binary64.toBinary32 ((Binary64.ofBits 0x4000000000000000 /- 2 -/))))))
          let t'24 := -t'23
          correction_rate := t'24
        else
          let t'25 ← PMem.ldF32 (fp + 0)
          let t'26 := (t'25 * p)
          correction_rate := t'26
  let t'27 ← is_positive'float dt
  if t'27 then
    let t'28 ← PMem.ldF32 (fp + 0)
    let t'29 ← PMem.ldF32 (fp + 0)
    let t'30 ← constrain_value_line'float correction_rate ((-(Binary32.abs t'28)) / dt) ((Binary32.abs t'29) / dt) (Int32.toUInt32 ((606 : Int32)))
    return t'30
  else
    return correction_rate

def sqrt_controller (error : Binary32) (p : Binary32) (second_ord_lim : Binary32) (dt : Binary32) : PMem.M Binary32 := do
  let fp ← PMem.enter 4
  let r ← sqrt_controller.body fp error p second_ord_lim dt
  PMem.leave fp
  return r

/-- `sqrt_controller_accel` as a pure function of its arguments (it reads and writes no memory). -/
def sqrt_controller_accel.pure' (error : Binary32) (rate_cmd : Binary32) (rate_state : Binary32) (p : Binary32) (second_ord_lim : Binary32) : Id Binary32 := do
  let mut error := error
  let mut rate_cmd := rate_cmd
  let mut rate_state := rate_state
  let mut p := p
  let mut second_ord_lim := second_ord_lim
  let t'1 ← _root_.Vehicle_lib.is_positive'float.pure' (rate_cmd * rate_state)
  if !t'1 then
    return Binary64.toBinary32 ((Binary64.ofBits 0x0000000000000000 /- 0 -/))
  let t'2 ← _root_.Vehicle_lib.is_positive'float.pure' second_ord_lim
  if !t'2 then
    return ((-p) * rate_state)
  let t'3 ← _root_.Vehicle_lib.is_positive'float.pure' p
  if !t'3 then
    let t'4 ← _root_.Vehicle_lib.is_zero.pure' rate_cmd
    if t'4 then
      return Binary64.toBinary32 ((Binary64.ofBits 0x0000000000000000 /- 0 -/))
    return ((-(second_ord_lim / (Binary32.abs rate_cmd))) * rate_state)
  let t'5 ← _root_.Vehicle_lib.sq.pure' p
  let mut linear_dist : Binary32 := (second_ord_lim / t'5)
  if (decide ((Binary32.abs error) ≤ linear_dist)) then
    return ((-p) * rate_state)
  let t'6 ← _root_.Vehicle_lib.is_zero.pure' rate_cmd
  if t'6 then
    return (Binary32.ofBits 0x00000000 /- 0 -/)
  return ((-(second_ord_lim / (Binary32.abs rate_cmd))) * rate_state)

/-- C++ `sqrt_controller_accel : float (float, float, float, float, float)`, `control.cpp:673-706`. -/
def sqrt_controller_accel (error : Binary32) (rate_cmd : Binary32) (rate_state : Binary32) (p : Binary32) (second_ord_lim : Binary32) : PMem.M Binary32 :=
  pure (_root_.Vehicle_lib.sqrt_controller_accel.pure' error rate_cmd rate_state p second_ord_lim)

/-- C++ `shape_accel : void (float, float &, float, float)`, `control.cpp:127-142`. -/
def shape_accel (accel_desired : Binary32) (accel : UInt64) (jerk_max : Binary32) (dt : Binary32) : PMem.M Unit := do
  let mut accel_desired := accel_desired
  let mut jerk_max := jerk_max
  let mut dt := dt
  let t'1 ← is_positive'float jerk_max
  if !t'1 then
    return ()
  let t'2 ← is_positive'float dt
  if t'2 then
    let t'3 ← PMem.ldF32 accel
    let mut accel_delta : Binary32 := (accel_desired - t'3)
    let t'4 ← constrain_value_line'float accel_delta ((-jerk_max) * dt) (jerk_max * dt) (Int32.toUInt32 ((139 : Int32)))
    accel_delta := t'4
    let t'5 ← PMem.ldF32 accel
    let t'6 := (t'5 + accel_delta)
    PMem.stF32 accel t'6
  return ()

/-- C++ `shape_pos_vel_accel : void (postype_t, float, float, postype_t, float, float &, float, float, float, float, float, float, bool)`, `control.cpp:269-346`. -/
def shape_pos_vel_accel.body (fp : UInt64) (pos_desired : Binary64) (vel_desired : Binary32) (accel_desired : Binary32) (pos : Binary64) (vel : Binary32) (accel : UInt64) (vel_min : Binary32) (vel_max : Binary32) (accel_min : Binary32) (accel_max : Binary32) (jerk_max : Binary32) (dt : Binary32) (limit_total : Bool) : PMem.M Unit := do
  let mut pos_desired := pos_desired
  let mut vel_desired := vel_desired
  let mut accel_desired := accel_desired
  let mut pos := pos
  let mut vel := vel
  PMem.stF32 (fp + 0) vel_min
  PMem.stF32 (fp + 4) vel_max
  let mut accel_min := accel_min
  let mut accel_max := accel_max
  let mut jerk_max := jerk_max
  let mut dt := dt
  let mut limit_total := limit_total
  let t'1 ← PMem.ldF32 (fp + 0)
  let t'2 ← is_positive'float t'1
  let mut sc'5 := t'2
  if !sc'5 then
    let t'3 ← PMem.ldF32 (fp + 4)
    let t'4 ← is_negative'float t'3
    sc'5 := t'4
  let mut sc'7 := sc'5
  if !sc'7 then
    let t'6 ← is_negative'float accel_min
    sc'7 := !t'6
  let mut sc'9 := sc'7
  if !sc'9 then
    let t'8 ← is_positive'float accel_max
    sc'9 := !t'8
  let mut sc'11 := sc'9
  if !sc'11 then
    let t'10 ← is_positive'float jerk_max
    sc'11 := !t'10
  if sc'11 then
    return ()
  let mut pos_error : Binary32 := Binary64.toBinary32 ((pos_desired - pos))
  let mut accel_lim : Binary32 := default  -- uninitialized in C
  let mut k_v : Binary32 := default  -- uninitialized in C
  let t'12 ← is_positive'float pos_error
  if t'12 then
    let t'13 := -accel_min
    accel_lim := t'13
    let t'14 := (jerk_max / accel_lim)
    k_v := t'14
  else
    accel_lim := accel_max
    let t'15 := (jerk_max / accel_lim)
    k_v := t'15
  let mut vel_corr : Binary32 := (vel - vel_desired)
  let t'16 ← sqrt_controller pos_error k_v accel_lim dt
  PMem.stF32 (fp + 8) t'16
  let t'17 ← PMem.ldF32 (fp + 8)
  let t'18 ← sqrt_controller_accel pos_error t'17 vel_corr k_v accel_lim
  let mut accel_corr_cmd : Binary32 := t'18
  let t'19 ← PMem.ldF32 (fp + 8)
  let t'20 := (t'19 + (accel_corr_cmd / k_v))
  PMem.stF32 (fp + 8) t'20
  let t'21 ← PMem.ldF32 (fp + 0)
  let t'22 ← is_negative'float t'21
  if t'22 then
    let t'23 ← MAX'float_float (fp + 8) (fp + 0)
    let t'24 ← PMem.ldF32 t'23
    PMem.stF32 (fp + 8) t'24
  let t'25 ← PMem.ldF32 (fp + 4)
  let t'26 ← is_positive'float t'25
  if t'26 then
    let t'27 ← MIN'float_float (fp + 8) (fp + 4)
    let t'28 ← PMem.ldF32 t'27
    PMem.stF32 (fp + 8) t'28
  let t'29 ← PMem.ldF32 (fp + 8)
  PMem.stF32 (fp + 16) (vel_desired + t'29)
  if limit_total then
    let t'30 ← PMem.ldF32 (fp + 0)
    let t'31 ← is_negative'float t'30
    if t'31 then
      let t'32 ← MAX'float_float (fp + 16) (fp + 0)
      let t'33 ← PMem.ldF32 t'32
      PMem.stF32 (fp + 16) t'33
    let t'34 ← PMem.ldF32 (fp + 4)
    let t'35 ← is_positive'float t'34
    if t'35 then
      let t'36 ← MIN'float_float (fp + 16) (fp + 4)
      let t'37 ← PMem.ldF32 t'36
      PMem.stF32 (fp + 16) t'37
  let t'38 ← PMem.ldF32 (fp + 16)
  let mut accel_target : Binary32 := ((t'38 - vel) * k_v)
  let t'39 ← constrain_value_line'float accel_target accel_min accel_max (Int32.toUInt32 ((334 : Int32)))
  accel_target := t'39
  let t'40 := (accel_target + accel_desired)
  accel_target := t'40
  if limit_total then
    let t'41 ← constrain_value_line'float accel_target accel_min accel_max (Int32.toUInt32 ((341 : Int32)))
    accel_target := t'41
  shape_accel accel_target accel jerk_max dt
  return ()

def shape_pos_vel_accel (pos_desired : Binary64) (vel_desired : Binary32) (accel_desired : Binary32) (pos : Binary64) (vel : Binary32) (accel : UInt64) (vel_min : Binary32) (vel_max : Binary32) (accel_min : Binary32) (accel_max : Binary32) (jerk_max : Binary32) (dt : Binary32) (limit_total : Bool) : PMem.M Unit := do
  let fp ← PMem.enter 20
  let r ← shape_pos_vel_accel.body fp pos_desired vel_desired accel_desired pos vel accel vel_min vel_max accel_min accel_max jerk_max dt limit_total
  PMem.leave fp
  return r

/-- C++ `shape_angle_vel_accel : void (float, float, float, float, float, float &, float, float, float, float, float, bool)`, `control.cpp:433-441`. -/
def shape_angle_vel_accel (angle_desired : Binary32) (angle_vel_desired : Binary32) (angle_accel_desired : Binary32) (angle : Binary32) (angle_vel : Binary32) (angle_accel : UInt64) (angle_vel_min : Binary32) (angle_vel_max : Binary32) (angle_accel_max : Binary32) (angle_jerk_max : Binary32) (dt : Binary32) (limit_total : Bool) : PMem.M Unit := do
  let mut angle_desired := angle_desired
  let mut angle_vel_desired := angle_vel_desired
  let mut angle_accel_desired := angle_accel_desired
  let mut angle := angle
  let mut angle_vel := angle_vel
  let mut angle_vel_min := angle_vel_min
  let mut angle_vel_max := angle_vel_max
  let mut angle_accel_max := angle_accel_max
  let mut angle_jerk_max := angle_jerk_max
  let mut dt := dt
  let mut limit_total := limit_total
  let t'1 ← wrap_PI'float (angle_desired - angle)
  let mut angle_desired_wrapped : Binary32 := (angle + t'1)
  shape_pos_vel_accel (Binary32.toBinary64 (angle_desired_wrapped)) angle_vel_desired angle_accel_desired (Binary32.toBinary64 (angle)) angle_vel angle_accel angle_vel_min angle_vel_max (-angle_accel_max) angle_accel_max angle_jerk_max dt limit_total
  return ()

/-- C++ `Vector2<float>::operator+= : Vector2<float> &(const Vector2<float> &)`, `vector2.cpp:96-100`. -/
def Vector2'float.operator__ (this : UInt64) (v : UInt64) : PMem.M UInt64 := do
  let t'1 ← PMem.ldF32 this
  let t'2 ← PMem.ldF32 v
  let t'3 := (t'1 + t'2)
  PMem.stF32 this t'3
  let t'4 := (this + 4)
  let t'5 ← PMem.ldF32 t'4
  let t'6 ← PMem.ldF32 (v + 4)
  let t'7 := (t'5 + t'6)
  PMem.stF32 t'4 t'7
  return this

/-- C++ `Vector2<float>::operator*= : Vector2<float> &(const float)`, `vector2.cpp:63-67`. -/
def Vector2'float.operator__'3 (this : UInt64) (num : Binary32) : PMem.M UInt64 := do
  let mut num := num
  let t'1 ← PMem.ldF32 this
  let t'2 := (t'1 * num)
  PMem.stF32 this t'2
  let t'3 := (this + 4)
  let t'4 ← PMem.ldF32 t'3
  let t'5 := (t'4 * num)
  PMem.stF32 t'3 t'5
  return this

/-- `check_lat'2` as a pure function of its arguments (it reads and writes no memory). -/
def check_lat'2.pure' (lat : Binary32) : Id Bool := do
  let mut lat := lat
  return (decide ((Binary32.abs lat) ≤ (Int32.toBinary32 ((90 : Int32)))))

/-- C++ `check_lat : bool (float)`, `location.cpp:39-42`. -/
def check_lat'2 (lat : Binary32) : PMem.M Bool :=
  pure (_root_.Vehicle_lib.check_lat'2.pure' lat)

/-- `check_lng'2` as a pure function of its arguments (it reads and writes no memory). -/
def check_lng'2.pure' (lng : Binary32) : Id Bool := do
  let mut lng := lng
  return (decide ((Binary32.abs lng) ≤ (Int32.toBinary32 ((180 : Int32)))))

/-- C++ `check_lng : bool (float)`, `location.cpp:43-46`. -/
def check_lng'2 (lng : Binary32) : PMem.M Bool :=
  pure (_root_.Vehicle_lib.check_lng'2.pure' lng)

/-- `degrees` as a pure function of its arguments (it reads and writes no memory). -/
def degrees.pure' (rad : Binary32) : Id Binary32 := do
  let mut rad := rad
  return (rad * ((Binary32.ofBits 0x43340000 /- 180 -/) / (Binary64.toBinary32 ((Binary64.ofBits 0x400921fb54442d18 /- 31415926535897931/10000000000000000 -/)))))

/-- C++ `degrees : float (float)`, `AP_Math.h:255-258`. -/
def degrees (rad : Binary32) : PMem.M Binary32 :=
  pure (_root_.Vehicle_lib.degrees.pure' rad)

/-- C++ `MIN : auto (const unsigned char &, const int &) -> decltype(one < two ? one : two)`, `AP_Math.h:300-303`. -/
def MIN'unsigned_char_int (one : UInt64) (two : UInt64) : PMem.M Int32 := do
  let t'1 ← PMem.ldU8 one
  let t'2 ← PMem.ldI32 two
  let mut c'3 : Int32 := default
  if (decide ((UInt32.toInt32 (UInt8.toUInt32 (t'1))) < t'2)) then
    let t'4 ← PMem.ldU8 one
    c'3 := UInt32.toInt32 (UInt8.toUInt32 (t'4))
  else
    let t'5 ← PMem.ldI32 two
    c'3 := t'5
  return c'3

/-- C++ `MIN : auto (const unsigned int &, const unsigned short &) -> decltype(one < two ? one : two)`, `AP_Math.h:300-303`. -/
def MIN'unsigned_int_unsigned_short (one : UInt64) (two : UInt64) : PMem.M UInt32 := do
  let t'1 ← PMem.ldU32 one
  let t'2 ← PMem.ldU16 two
  let mut c'3 : UInt32 := default
  if (decide (t'1 < (UInt16.toUInt32 (t'2)))) then
    let t'4 ← PMem.ldU32 one
    c'3 := t'4
  else
    let t'5 ← PMem.ldU16 two
    c'3 := UInt16.toUInt32 (t'5)
  return c'3

/-- C++ `MIN : auto (const float &, const unsigned short &) -> decltype(one < two ? one : two)`, `AP_Math.h:300-303`. -/
def MIN'float_unsigned_short (one : UInt64) (two : UInt64) : PMem.M Binary32 := do
  let t'1 ← PMem.ldF32 one
  let t'2 ← PMem.ldU16 two
  let mut c'3 : Binary32 := default
  if (decide (t'1 < (Int32.toBinary32 ((UInt32.toInt32 (UInt16.toUInt32 (t'2))))))) then
    let t'4 ← PMem.ldF32 one
    c'3 := t'4
  else
    let t'5 ← PMem.ldU16 two
    c'3 := Int32.toBinary32 ((UInt32.toInt32 (UInt16.toUInt32 (t'5))))
  return c'3

/-- C++ `QuaternionT<float>::QuaternionT : void (QuaternionT<float> &&) noexcept`, `quaternion.h:?-?`. -/
def QuaternionT'float.QuaternionT'3 (this : UInt64) (arg : UInt64) : PMem.M Unit := do
  let t'1 ← PMem.ldF32 arg
  PMem.stF32 (this + 0) t'1
  let t'2 ← PMem.ldF32 (arg + 4)
  PMem.stF32 (this + 4) t'2
  let t'3 ← PMem.ldF32 (arg + 8)
  PMem.stF32 (this + 8) t'3
  let t'4 ← PMem.ldF32 (arg + 12)
  PMem.stF32 (this + 12) t'4
  return ()

/-- C++ `QuaternionT<float>::QuaternionT : void (const QuaternionT<float> &) noexcept`, `AP_Common.h:29-?`. -/
def QuaternionT'float.QuaternionT'4 (this : UInt64) (arg : UInt64) : PMem.M Unit := do
  let t'1 ← PMem.ldF32 arg
  PMem.stF32 (this + 0) t'1
  let t'2 ← PMem.ldF32 (arg + 4)
  PMem.stF32 (this + 4) t'2
  let t'3 ← PMem.ldF32 (arg + 8)
  PMem.stF32 (this + 8) t'3
  let t'4 ← PMem.ldF32 (arg + 12)
  PMem.stF32 (this + 12) t'4
  return ()

/-- C++ `MIN : auto (const float &, const int &) -> decltype(one < two ? one : two)`, `AP_Math.h:300-303`. -/
def MIN'float_int (one : UInt64) (two : UInt64) : PMem.M Binary32 := do
  let t'1 ← PMem.ldF32 one
  let t'2 ← PMem.ldI32 two
  let mut c'3 : Binary32 := default
  if (decide (t'1 < (Int32.toBinary32 (t'2)))) then
    let t'4 ← PMem.ldF32 one
    c'3 := t'4
  else
    let t'5 ← PMem.ldI32 two
    c'3 := Int32.toBinary32 (t'5)
  return c'3

/-- C++ `Vector2<float>::length_squared : float () const`, `vector2.cpp:24-27`. -/
def Vector2'float.length_squared (this : UInt64) : PMem.M Binary32 := do
  let t'1 ← PMem.ldF32 this
  let t'2 ← PMem.ldF32 this
  let t'3 ← PMem.ldF32 (this + 4)
  let t'4 ← PMem.ldF32 (this + 4)
  return ((t'1 * t'2) + (t'3 * t'4))

/-- C++ `Vector2<float>::operator/ : Vector2<float> (const float) const`, `vector2.cpp:103-106`. -/
def Vector2'float.operator_'5.body (fp : UInt64) (this : UInt64) (sret : UInt64) (num : Binary32) : PMem.M Unit := do
  let mut num := num
  let t'1 ← PMem.ldF32 this
  let t'2 ← PMem.ldF32 (this + 4)
  Vector2'float.Vector2'2 (fp + 0) (t'1 / num) (t'2 / num)
  Vector2'float.Vector2'3 sret (fp + 0)
  return ()

def Vector2'float.operator_'5 (this : UInt64) (sret : UInt64) (num : Binary32) : PMem.M Unit := do
  let fp ← PMem.enter 8
  let r ← Vector2'float.operator_'5.body fp this sret num
  PMem.leave fp
  return r

/-- C++ `Vector2<float>::normalized : Vector2<float> () const`, `vector2.cpp:275-278`. -/
def Vector2'float.normalized.body (fp : UInt64) (this : UInt64) (sret : UInt64) : PMem.M Unit := do
  let t'1 ← Vector2'float.length this
  Vector2'float.operator_'5 this (fp + 0) t'1
  let t'2 := (fp + 0)
  Vector2'float.Vector2'3 sret t'2
  return ()

def Vector2'float.normalized (this : UInt64) (sret : UInt64) : PMem.M Unit := do
  let fp ← PMem.enter 8
  let r ← Vector2'float.normalized.body fp this sret
  PMem.leave fp
  return r

/-- C++ `Vector2<float>::operator* : float (const Vector2<float> &) const`, `vector2.cpp:50-53`. -/
def Vector2'float.operator_'4 (this : UInt64) (v : UInt64) : PMem.M Binary32 := do
  let t'1 ← PMem.ldF32 this
  let t'2 ← PMem.ldF32 v
  let t'3 ← PMem.ldF32 (this + 4)
  let t'4 ← PMem.ldF32 (v + 4)
  return ((t'1 * t'2) + (t'3 * t'4))

/-- C++ `get_bearing_rad : float (const Vector2f &, const Vector2f &)`, `location.cpp:27-30`. -/
def get_bearing_rad (origin : UInt64) (destination : UInt64) : PMem.M Binary32 := do
  let t'1 ← PMem.ldF32 (destination + 4)
  let t'2 ← PMem.ldF32 (origin + 4)
  let t'3 ← PMem.ldF32 destination
  let t'4 ← PMem.ldF32 origin
  let t'5 ← wrap_2PI (Musl.atan2f.atan2f (t'1 - t'2) (t'3 - t'4))
  return t'5

/-- C++ `Vector2<double>::angle : double () const`, `ftype.h:162-165`. -/
def Vector2'double.angle (this : UInt64) : PMem.M Binary64 := do
  let t'1 ← PMem.ldF64 (this + 8)
  let t'2 ← PMem.ldF64 this
  return (Musl.atan2.atan2 t'1 t'2)

/-- C++ `SCurve::SCurve : void ()`, `SCurve.cpp:40-43`. -/
def SCurve.SCurve (this : UInt64) : PMem.M Unit := do
  Vector3'float.Vector3'2 (this + 588)
  Vector2'float.Vector2 ((this + 604) + 12)
  SCurve.init this
  return ()

/-- C++ `MAX : auto (const float &, const int &) -> decltype(one > two ? one : two)`, `AP_Math.h:307-310`. -/
def MAX'float_int (one : UInt64) (two : UInt64) : PMem.M Binary32 := do
  let t'1 ← PMem.ldF32 one
  let t'2 ← PMem.ldI32 two
  let mut c'3 : Binary32 := default
  if (decide (t'1 > (Int32.toBinary32 (t'2)))) then
    let t'4 ← PMem.ldF32 one
    c'3 := t'4
  else
    let t'5 ← PMem.ldI32 two
    c'3 := Int32.toBinary32 (t'5)
  return c'3

/-- C++ `fill_nanf : void (float *, uint16_t)`, `AP_Math.cpp:440-461`. -/
def fill_nanf (f : UInt64) (count : UInt16) : PMem.M Unit := do
  let mut f := f
  let mut count := count
  let t'1 ← PMem.ldB (0xedf8 : UInt64) /- &fill_nanf(...)::created -/
  if !t'1 then
    let mut i : UInt16 := Int16.toUInt16 (Int32.toInt16 ((0 : Int32)))
    let mut first'2 := true
    for _ in PMem.loopFuel do
      if !first'2 then
        let t'3 := i
        let t'4 := (t'3 + 1)
        i := t'4
        pure ()
      first'2 := false
      if !((decide ((UInt16.toUInt64 (i)) < ((8192 : UInt64) / (4 : UInt64))))) then break
      PMem.stB (0xedf8 : UInt64) /- &fill_nanf(...)::created -/ true
      let t'5 := (Binary32.ofBits 0x7fa00000)
      PMem.stF32 ((0xee00 : UInt64) /- &fill_nanf(...)::many_nanfs -/ + ((UInt64.toInt64 (UInt16.toUInt64 (i))) * 4).toUInt64) t'5
  if (decide ((UInt16.toUInt64 (count)) > ((8192 : UInt64) / (4 : UInt64)))) then
    pure ()
  let t'6 ← PMem.memcpy f (0xee00 : UInt64) /- &fill_nanf(...)::many_nanfs -/ ((UInt16.toUInt64 (count)) * (4 : UInt64))
  discard <| pure (t'6)
  return ()

/-- C++ `MAX : auto (const unsigned short &, const unsigned short &) -> decltype(one > two ? one : two)`, `AP_Math.h:307-310`. -/
def MAX'unsigned_short_unsigned_short (one : UInt64) (two : UInt64) : PMem.M UInt64 := do
  let t'1 ← PMem.ldU16 one
  let t'2 ← PMem.ldU16 two
  let mut c'3 : UInt64 := 0
  if (decide ((UInt32.toInt32 (UInt16.toUInt32 (t'1))) > (UInt32.toInt32 (UInt16.toUInt32 (t'2))))) then
    c'3 := one
  else
    c'3 := two
  return c'3

/-- C++ `MIN : auto (const unsigned short &, const unsigned short &) -> decltype(one < two ? one : two)`, `AP_Math.h:300-303`. -/
def MIN'unsigned_short_unsigned_short (one : UInt64) (two : UInt64) : PMem.M UInt64 := do
  let t'1 ← PMem.ldU16 one
  let t'2 ← PMem.ldU16 two
  let mut c'3 : UInt64 := 0
  if (decide ((UInt32.toInt32 (UInt16.toUInt32 (t'1))) < (UInt32.toInt32 (UInt16.toUInt32 (t'2))))) then
    c'3 := one
  else
    c'3 := two
  return c'3

/-- C++ `Vector3<float>::operator*= : Vector3<float> &(const Vector3<float> &)`, `vector3.h:130-133`. -/
def Vector3'float.operator__'4 (this : UInt64) (v : UInt64) : PMem.M UInt64 := do
  let t'1 ← PMem.ldF32 this
  let t'2 ← PMem.ldF32 v
  let t'3 := (t'1 * t'2)
  PMem.stF32 this t'3
  let t'4 := (this + 4)
  let t'5 ← PMem.ldF32 t'4
  let t'6 ← PMem.ldF32 (v + 4)
  let t'7 := (t'5 * t'6)
  PMem.stF32 t'4 t'7
  let t'8 := (this + 8)
  let t'9 ← PMem.ldF32 t'8
  let t'10 ← PMem.ldF32 (v + 8)
  let t'11 := (t'9 * t'10)
  PMem.stF32 t'8 t'11
  return this

/-- C++ `Vector3<float>::operator+= : Vector3<float> &(const Vector3<float> &)`, `vector3.cpp:376-380`. -/
def Vector3'float.operator__'3 (this : UInt64) (v : UInt64) : PMem.M UInt64 := do
  let t'1 ← PMem.ldF32 this
  let t'2 ← PMem.ldF32 v
  let t'3 := (t'1 + t'2)
  PMem.stF32 this t'3
  let t'4 := (this + 4)
  let t'5 ← PMem.ldF32 t'4
  let t'6 ← PMem.ldF32 (v + 4)
  let t'7 := (t'5 + t'6)
  PMem.stF32 t'4 t'7
  let t'8 := (this + 8)
  let t'9 ← PMem.ldF32 t'8
  let t'10 ← PMem.ldF32 (v + 8)
  let t'11 := (t'9 + t'10)
  PMem.stF32 t'8 t'11
  return this

/-- C++ `QuaternionT<float>::operator* : QuaternionT<float> (const QuaternionT<float> &) const`, `quaternion.cpp:712-731`. -/
def QuaternionT'float.operator_.body (fp : UInt64) (this : UInt64) (sret : UInt64) (v : UInt64) : PMem.M Unit := do
  QuaternionT'float.QuaternionT (fp + 0)
  let w1 : UInt64 := this
  let x1 : UInt64 := (this + 4)
  let y1 : UInt64 := (this + 8)
  let z1 : UInt64 := (this + 12)
  let t'1 ← PMem.ldF32 v
  let mut w2 : Binary32 := t'1
  let t'2 ← PMem.ldF32 (v + 4)
  let mut x2 : Binary32 := t'2
  let t'3 ← PMem.ldF32 (v + 8)
  let mut y2 : Binary32 := t'3
  let t'4 ← PMem.ldF32 (v + 12)
  let mut z2 : Binary32 := t'4
  let t'5 ← PMem.ldF32 w1
  let t'6 ← PMem.ldF32 x1
  let t'7 ← PMem.ldF32 y1
  let t'8 ← PMem.ldF32 z1
  let t'9 := ((((t'5 * w2) - (t'6 * x2)) - (t'7 * y2)) - (t'8 * z2))
  PMem.stF32 (fp + 0) t'9
  let t'10 ← PMem.ldF32 w1
  let t'11 ← PMem.ldF32 x1
  let t'12 ← PMem.ldF32 y1
  let t'13 ← PMem.ldF32 z1
  let t'14 := ((((t'10 * x2) + (t'11 * w2)) + (t'12 * z2)) - (t'13 * y2))
  PMem.stF32 ((fp + 0) + 4) t'14
  let t'15 ← PMem.ldF32 w1
  let t'16 ← PMem.ldF32 x1
  let t'17 ← PMem.ldF32 y1
  let t'18 ← PMem.ldF32 z1
  let t'19 := ((((t'15 * y2) - (t'16 * z2)) + (t'17 * w2)) + (t'18 * x2))
  PMem.stF32 ((fp + 0) + 8) t'19
  let t'20 ← PMem.ldF32 w1
  let t'21 ← PMem.ldF32 x1
  let t'22 ← PMem.ldF32 y1
  let t'23 ← PMem.ldF32 z1
  let t'24 := ((((t'20 * z2) + (t'21 * y2)) - (t'22 * x2)) + (t'23 * w2))
  PMem.stF32 ((fp + 0) + 12) t'24
  QuaternionT'float.QuaternionT'3 sret (fp + 0)
  return ()

def QuaternionT'float.operator_ (this : UInt64) (sret : UInt64) (v : UInt64) : PMem.M Unit := do
  let fp ← PMem.enter 16
  let r ← QuaternionT'float.operator_.body fp this sret v
  PMem.leave fp
  return r

/-- C++ `QuaternionT<float>::to_euler : void (Vector3f &) const`, `quaternion.h:125-127`. -/
def QuaternionT'float.to_euler'2 (this : UInt64) (rpy : UInt64) : PMem.M Unit := do
  QuaternionT'float.to_euler this rpy (rpy + 4) (rpy + 8)
  return ()

/-- C++ `Vector3<float>::operator/= : Vector3<float> &(const float)`, `vector3.cpp:350-354`. -/
def Vector3'float.operator__'5 (this : UInt64) (num : Binary32) : PMem.M UInt64 := do
  let mut num := num
  let t'1 ← PMem.ldF32 this
  let t'2 := (t'1 / num)
  PMem.stF32 this t'2
  let t'3 := (this + 4)
  let t'4 ← PMem.ldF32 t'3
  let t'5 := (t'4 / num)
  PMem.stF32 t'3 t'5
  let t'6 := (this + 8)
  let t'7 ← PMem.ldF32 t'6
  let t'8 := (t'7 / num)
  PMem.stF32 t'6 t'8
  return this

/-- C++ `QuaternionT<float>::from_axis_angle : void (const Vector3<float> &, float)`, `quaternion.cpp:469-483`. -/
def QuaternionT'float.from_axis_angle'2 (this : UInt64) (axis : UInt64) (theta : Binary32) : PMem.M Unit := do
  let mut theta := theta
  let t'1 ← _root_.Vehicle_lib.is_zero theta
  if t'1 then
    let t'2 := (Binary32.ofBits 0x3f800000 /- 1 -/)
    PMem.stF32 this t'2
    let t'3 := (Binary32.ofBits 0x00000000 /- 0 -/)
    PMem.stF32 (this + 12) t'3
    let t'4 ← PMem.ldF32 (this + 12)
    PMem.stF32 (this + 8) t'4
    let t'5 ← PMem.ldF32 (this + 8)
    PMem.stF32 (this + 4) t'5
    return ()
  let mut st2 : Binary32 := Binary64.toBinary32 ((Musl.sin.sin ((Binary64.ofBits 0x3fe0000000000000 /- 1/2 -/) * (Binary32.toBinary64 (theta)))))
  let t'6 := Binary64.toBinary32 ((Musl.cos.cos ((Binary64.ofBits 0x3fe0000000000000 /- 1/2 -/) * (Binary32.toBinary64 (theta)))))
  PMem.stF32 this t'6
  let t'7 ← PMem.ldF32 axis
  let t'8 := (t'7 * st2)
  PMem.stF32 (this + 4) t'8
  let t'9 ← PMem.ldF32 (axis + 4)
  let t'10 := (t'9 * st2)
  PMem.stF32 (this + 8) t'10
  let t'11 ← PMem.ldF32 (axis + 8)
  let t'12 := (t'11 * st2)
  PMem.stF32 (this + 12) t'12
  return ()

/-- C++ `QuaternionT<float>::from_axis_angle : void (Vector3<float>)`, `ftype.h:454-464`. -/
def QuaternionT'float.from_axis_angle (this : UInt64) (v : UInt64) : PMem.M Unit := do
  let t'1 ← Vector3'float.length v
  let mut theta : Binary32 := t'1
  let t'2 ← _root_.Vehicle_lib.is_zero theta
  if t'2 then
    let t'3 := (Binary32.ofBits 0x3f800000 /- 1 -/)
    PMem.stF32 this t'3
    let t'4 := (Binary32.ofBits 0x00000000 /- 0 -/)
    PMem.stF32 (this + 12) t'4
    let t'5 ← PMem.ldF32 (this + 12)
    PMem.stF32 (this + 8) t'5
    let t'6 ← PMem.ldF32 (this + 8)
    PMem.stF32 (this + 4) t'6
    return ()
  let t'7 ← Vector3'float.operator__'5 v theta
  discard <| pure (t'7)
  QuaternionT'float.from_axis_angle'2 this v theta
  return ()

/-- `input_expo` as a pure function of its arguments (it reads and writes no memory). -/
def input_expo.pure' (input : Binary32) (expo : Binary32) : Id Binary32 := do
  let mut input := input
  let mut expo := expo
  let t'1 ← _root_.Vehicle_lib.constrain_value_line'float.pure' input (-(Binary64.toBinary32 ((Binary64.ofBits 0x3ff0000000000000 /- 1 -/)))) (Binary64.toBinary32 ((Binary64.ofBits 0x3ff0000000000000 /- 1 -/))) (Int32.toUInt32 ((813 : Int32)))
  input := t'1
  if (decide (expo < (Binary64.toBinary32 ((Binary64.ofBits 0x3fee666666666666 /- 23749999999999999/25000000000000000 -/))))) then
    return ((((Int32.toBinary32 ((1 : Int32))) - expo) * input) / ((Int32.toBinary32 ((1 : Int32))) - (expo * (Binary32.abs input))))
  return input

/-- C++ `input_expo : float (float, float)`, `control.cpp:810-820`. -/
def input_expo (input : Binary32) (expo : Binary32) : PMem.M Binary32 :=
  pure (_root_.Vehicle_lib.input_expo.pure' input expo)

/-- C++ `update_vel_accel : void (float &, float, float, float, float)`, `control.cpp:46-59`. -/
def update_vel_accel (vel : UInt64) (accel : Binary32) (dt : Binary32) (limit : Binary32) (vel_error : Binary32) : PMem.M Unit := do
  let mut accel := accel
  let mut dt := dt
  let mut limit := limit
  let mut vel_error := vel_error
  let mut delta_vel : Binary32 := (accel * dt)
  let t'1 ← is_positive'float (delta_vel * limit)
  let mut sc'3 := t'1
  if sc'3 then
    let t'2 ← is_positive'float (vel_error * limit)
    sc'3 := t'2
  if sc'3 then
    let t'4 ← PMem.ldF32 vel
    let t'5 ← is_negative'float (t'4 * limit)
    if t'5 then
      let t'6 ← PMem.ldF32 vel
      let t'7 ← PMem.ldF32 vel
      let t'8 ← constrain_value_line'float delta_vel (-(Binary32.abs t'6)) (Binary32.abs t'7) (Int32.toUInt32 ((53 : Int32)))
      delta_vel := t'8
    else
      let t'9 := Binary64.toBinary32 ((Binary64.ofBits 0x0000000000000000 /- 0 -/))
      delta_vel := t'9
  let t'10 ← PMem.ldF32 vel
  let t'11 := (t'10 + delta_vel)
  PMem.stF32 vel t'11
  return ()

/-- C++ `update_pos_vel_accel : void (postype_t &, float &, float, float, float, float, float)`, `control.cpp:67-78`. -/
def update_pos_vel_accel (pos : UInt64) (vel : UInt64) (accel : Binary32) (dt : Binary32) (limit : Binary32) (pos_error : Binary32) (vel_error : Binary32) : PMem.M Unit := do
  let mut accel := accel
  let mut dt := dt
  let mut limit := limit
  let mut pos_error := pos_error
  let mut vel_error := vel_error
  let t'1 ← PMem.ldF32 vel
  let t'2 ← sq dt
  let mut delta_pos : Binary32 := ((t'1 * dt) + ((accel * (Binary32.ofBits 0x3f000000 /- 1/2 -/)) * t'2))
  let t'3 ← is_positive'float (delta_pos * limit)
  let mut sc'5 := t'3
  if sc'5 then
    let t'4 ← is_positive'float (pos_error * limit)
    sc'5 := t'4
  if sc'5 then
    let t'6 := Binary64.toBinary32 ((Binary64.ofBits 0x0000000000000000 /- 0 -/))
    delta_pos := t'6
  let t'7 ← PMem.ldF64 pos
  let t'8 := (t'7 + (Binary32.toBinary64 (delta_pos)))
  PMem.stF64 pos t'8
  update_vel_accel vel accel dt limit vel_error
  return ()

/-- C++ `shape_vel_accel : void (float, float, float, float &, float, float, float, float, bool)`, `control.cpp:182-222`. -/
def shape_vel_accel (vel_desired : Binary32) (accel_desired : Binary32) (vel : Binary32) (accel : UInt64) (accel_min : Binary32) (accel_max : Binary32) (jerk_max : Binary32) (dt : Binary32) (limit_total_accel : Bool) : PMem.M Unit := do
  let mut vel_desired := vel_desired
  let mut accel_desired := accel_desired
  let mut vel := vel
  let mut accel_min := accel_min
  let mut accel_max := accel_max
  let mut jerk_max := jerk_max
  let mut dt := dt
  let mut limit_total_accel := limit_total_accel
  let t'1 ← is_negative'float accel_min
  let mut sc'3 := !t'1
  if !sc'3 then
    let t'2 ← is_positive'float accel_max
    sc'3 := !t'2
  let mut sc'5 := sc'3
  if !sc'5 then
    let t'4 ← is_positive'float jerk_max
    sc'5 := !t'4
  if sc'5 then
    return ()
  let mut vel_error : Binary32 := (vel_desired - vel)
  let mut KPa : Binary32 := default  -- uninitialized in C
  let t'6 ← is_positive'float vel_error
  if t'6 then
    let t'7 := (jerk_max / accel_max)
    KPa := t'7
  else
    let t'8 := (jerk_max / (-accel_min))
    KPa := t'8
  let t'9 ← sqrt_controller vel_error KPa jerk_max dt
  let mut accel_target : Binary32 := t'9
  let t'10 ← constrain_value_line'float accel_target accel_min accel_max (Int32.toUInt32 ((211 : Int32)))
  accel_target := t'10
  let t'11 := (accel_target + accel_desired)
  accel_target := t'11
  if limit_total_accel then
    let t'12 ← constrain_value_line'float accel_target accel_min accel_max (Int32.toUInt32 ((218 : Int32)))
    accel_target := t'12
  shape_accel accel_target accel jerk_max dt
  return ()

/-- `cd_to_rad` as a pure function of its arguments (it reads and writes no memory). -/
def cd_to_rad.pure' (cdeg : Binary32) : Id Binary32 := do
  let mut cdeg := cdeg
  return (cdeg * ((Binary64.toBinary32 ((Binary64.ofBits 0x400921fb54442d18 /- 31415926535897931/10000000000000000 -/))) / (Binary32.ofBits 0x468ca000 /- 18000 -/)))

/-- C++ `cd_to_rad : float (float)`, `AP_Math.h:243-246`. -/
def cd_to_rad (cdeg : Binary32) : PMem.M Binary32 :=
  pure (_root_.Vehicle_lib.cd_to_rad.pure' cdeg)

/-- C++ `QuaternionT<float>::length : float () const`, `quaternion.cpp:633-636`. -/
def QuaternionT'float.length (this : UInt64) : PMem.M Binary32 := do
  let t'1 ← PMem.ldF32 this
  let t'2 ← sq t'1
  let t'3 ← PMem.ldF32 (this + 4)
  let t'4 ← sq t'3
  let t'5 ← PMem.ldF32 (this + 8)
  let t'6 ← sq t'5
  let t'7 ← PMem.ldF32 (this + 12)
  let t'8 ← sq t'7
  return (Binary32.sqrt (((t'2 + t'4) + t'6) + t'8))

/-- C++ `QuaternionT<float>::normalize : void ()`, `ftype.h:662-675`. -/
def QuaternionT'float.normalize (this : UInt64) : PMem.M Unit := do
  let t'1 ← QuaternionT'float.length this
  let mut quatMag : Binary32 := t'1
  let t'2 ← _root_.Vehicle_lib.is_zero quatMag
  if !t'2 then
    let mut quatMagInv : Binary32 := ((Binary32.ofBits 0x3f800000 /- 1 -/) / quatMag)
    let t'3 ← PMem.ldF32 this
    let t'4 := (t'3 * quatMagInv)
    PMem.stF32 this t'4
    let t'5 := (this + 4)
    let t'6 ← PMem.ldF32 t'5
    let t'7 := (t'6 * quatMagInv)
    PMem.stF32 t'5 t'7
    let t'8 := (this + 8)
    let t'9 ← PMem.ldF32 t'8
    let t'10 := (t'9 * quatMagInv)
    PMem.stF32 t'8 t'10
    let t'11 := (this + 12)
    let t'12 ← PMem.ldF32 t'11
    let t'13 := (t'12 * quatMagInv)
    PMem.stF32 t'11 t'13
  else
    pure ()
  return ()

/-- C++ `QuaternionT<float>::operator*= : QuaternionT<float> &(const QuaternionT<float> &)`, `quaternion.cpp:762-780`. -/
def QuaternionT'float.operator__ (this : UInt64) (v : UInt64) : PMem.M UInt64 := do
  let t'1 ← PMem.ldF32 this
  let mut w1 : Binary32 := t'1
  let t'2 ← PMem.ldF32 (this + 4)
  let mut x1 : Binary32 := t'2
  let t'3 ← PMem.ldF32 (this + 8)
  let mut y1 : Binary32 := t'3
  let t'4 ← PMem.ldF32 (this + 12)
  let mut z1 : Binary32 := t'4
  let t'5 ← PMem.ldF32 v
  let mut w2 : Binary32 := t'5
  let t'6 ← PMem.ldF32 (v + 4)
  let mut x2 : Binary32 := t'6
  let t'7 ← PMem.ldF32 (v + 8)
  let mut y2 : Binary32 := t'7
  let t'8 ← PMem.ldF32 (v + 12)
  let mut z2 : Binary32 := t'8
  let t'9 := ((((w1 * w2) - (x1 * x2)) - (y1 * y2)) - (z1 * z2))
  PMem.stF32 this t'9
  let t'10 := ((((w1 * x2) + (x1 * w2)) + (y1 * z2)) - (z1 * y2))
  PMem.stF32 (this + 4) t'10
  let t'11 := ((((w1 * y2) - (x1 * z2)) + (y1 * w2)) + (z1 * x2))
  PMem.stF32 (this + 8) t'11
  let t'12 := ((((w1 * z2) + (x1 * y2)) - (y1 * x2)) + (z1 * w2))
  PMem.stF32 (this + 12) t'12
  return this

/-- C++ `QuaternionT<float>::inverse : QuaternionT<float> () const`, `quaternion.cpp:647-650`. -/
def QuaternionT'float.inverse.body (fp : UInt64) (this : UInt64) (sret : UInt64) : PMem.M Unit := do
  let t'1 ← PMem.ldF32 this
  let t'2 ← PMem.ldF32 (this + 4)
  let t'3 ← PMem.ldF32 (this + 8)
  let t'4 ← PMem.ldF32 (this + 12)
  QuaternionT'float.QuaternionT'2 (fp + 0) t'1 (-t'2) (-t'3) (-t'4)
  QuaternionT'float.QuaternionT'3 sret (fp + 0)
  return ()

def QuaternionT'float.inverse (this : UInt64) (sret : UInt64) : PMem.M Unit := do
  let fp ← PMem.enter 16
  let r ← QuaternionT'float.inverse.body fp this sret
  PMem.leave fp
  return r

/-- C++ `QuaternionT<float>::operator* : Vector3<float> (const Vector3<float> &) const`, `quaternion.cpp:738-759`. -/
def QuaternionT'float.operator_'2.body (fp : UInt64) (this : UInt64) (sret : UInt64) (v : UInt64) : PMem.M Unit := do
  Vector3'float.Vector3'4 (fp + 0) v
  let t'1 ← PMem.ldF32 (this + 8)
  let t'2 ← PMem.ldF32 (v + 8)
  let t'3 ← PMem.ldF32 (this + 12)
  let t'4 ← PMem.ldF32 (v + 4)
  PMem.stF32 ((fp + 16) + 0) ((t'1 * t'2) - (t'3 * t'4))
  let t'5 ← PMem.ldF32 (this + 12)
  let t'6 ← PMem.ldF32 v
  let t'7 ← PMem.ldF32 (this + 4)
  let t'8 ← PMem.ldF32 (v + 8)
  PMem.stF32 ((fp + 16) + 4) ((t'5 * t'6) - (t'7 * t'8))
  let t'9 ← PMem.ldF32 (this + 4)
  let t'10 ← PMem.ldF32 (v + 4)
  let t'11 ← PMem.ldF32 (this + 8)
  let t'12 ← PMem.ldF32 v
  PMem.stF32 ((fp + 16) + 8) ((t'9 * t'10) - (t'11 * t'12))
  let t'13 := ((fp + 16) + ((Int32.toInt64 ((0 : Int32))) * 4).toUInt64)
  let t'14 ← PMem.ldF32 t'13
  let t'15 ← PMem.ldF32 ((fp + 16) + ((Int32.toInt64 ((0 : Int32))) * 4).toUInt64)
  let t'16 := (t'14 + t'15)
  PMem.stF32 t'13 t'16
  let t'17 := ((fp + 16) + ((Int32.toInt64 ((1 : Int32))) * 4).toUInt64)
  let t'18 ← PMem.ldF32 t'17
  let t'19 ← PMem.ldF32 ((fp + 16) + ((Int32.toInt64 ((1 : Int32))) * 4).toUInt64)
  let t'20 := (t'18 + t'19)
  PMem.stF32 t'17 t'20
  let t'21 := ((fp + 16) + ((Int32.toInt64 ((2 : Int32))) * 4).toUInt64)
  let t'22 ← PMem.ldF32 t'21
  let t'23 ← PMem.ldF32 ((fp + 16) + ((Int32.toInt64 ((2 : Int32))) * 4).toUInt64)
  let t'24 := (t'22 + t'23)
  PMem.stF32 t'21 t'24
  let t'25 ← PMem.ldF32 (fp + 0)
  let t'26 ← PMem.ldF32 this
  let t'27 ← PMem.ldF32 ((fp + 16) + ((Int32.toInt64 ((0 : Int32))) * 4).toUInt64)
  let t'28 ← PMem.ldF32 (this + 8)
  let t'29 ← PMem.ldF32 ((fp + 16) + ((Int32.toInt64 ((2 : Int32))) * 4).toUInt64)
  let t'30 ← PMem.ldF32 (this + 12)
  let t'31 ← PMem.ldF32 ((fp + 16) + ((Int32.toInt64 ((1 : Int32))) * 4).toUInt64)
  let t'32 := (t'25 + (((t'26 * t'27) + (t'28 * t'29)) - (t'30 * t'31)))
  PMem.stF32 (fp + 0) t'32
  let t'33 := ((fp + 0) + 4)
  let t'34 ← PMem.ldF32 t'33
  let t'35 ← PMem.ldF32 this
  let t'36 ← PMem.ldF32 ((fp + 16) + ((Int32.toInt64 ((1 : Int32))) * 4).toUInt64)
  let t'37 ← PMem.ldF32 (this + 12)
  let t'38 ← PMem.ldF32 ((fp + 16) + ((Int32.toInt64 ((0 : Int32))) * 4).toUInt64)
  let t'39 ← PMem.ldF32 (this + 4)
  let t'40 ← PMem.ldF32 ((fp + 16) + ((Int32.toInt64 ((2 : Int32))) * 4).toUInt64)
  let t'41 := (t'34 + (((t'35 * t'36) + (t'37 * t'38)) - (t'39 * t'40)))
  PMem.stF32 t'33 t'41
  let t'42 := ((fp + 0) + 8)
  let t'43 ← PMem.ldF32 t'42
  let t'44 ← PMem.ldF32 this
  let t'45 ← PMem.ldF32 ((fp + 16) + ((Int32.toInt64 ((2 : Int32))) * 4).toUInt64)
  let t'46 ← PMem.ldF32 (this + 4)
  let t'47 ← PMem.ldF32 ((fp + 16) + ((Int32.toInt64 ((1 : Int32))) * 4).toUInt64)
  let t'48 ← PMem.ldF32 (this + 8)
  let t'49 ← PMem.ldF32 ((fp + 16) + ((Int32.toInt64 ((0 : Int32))) * 4).toUInt64)
  let t'50 := (t'43 + (((t'44 * t'45) + (t'46 * t'47)) - (t'48 * t'49)))
  PMem.stF32 t'42 t'50
  Vector3'float.Vector3'3 sret (fp + 0)
  return ()

def QuaternionT'float.operator_'2 (this : UInt64) (sret : UInt64) (v : UInt64) : PMem.M Unit := do
  let fp ← PMem.enter 28
  let r ← QuaternionT'float.operator_'2.body fp this sret v
  PMem.leave fp
  return r

/-- C++ `Vector3<float>::operator% : Vector3<float> (const Vector3<float> &) const`, `vector3.cpp:310-314`. -/
def Vector3'float.operator_'6.body (fp : UInt64) (this : UInt64) (sret : UInt64) (v : UInt64) : PMem.M Unit := do
  let t'1 ← PMem.ldF32 (this + 4)
  let t'2 ← PMem.ldF32 (v + 8)
  let t'3 ← PMem.ldF32 (this + 8)
  let t'4 ← PMem.ldF32 (v + 4)
  let t'5 ← PMem.ldF32 (this + 8)
  let t'6 ← PMem.ldF32 v
  let t'7 ← PMem.ldF32 this
  let t'8 ← PMem.ldF32 (v + 8)
  let t'9 ← PMem.ldF32 this
  let t'10 ← PMem.ldF32 (v + 4)
  let t'11 ← PMem.ldF32 (this + 4)
  let t'12 ← PMem.ldF32 v
  Vector3'float.Vector3 (fp + 0) ((t'1 * t'2) - (t'3 * t'4)) ((t'5 * t'6) - (t'7 * t'8)) ((t'9 * t'10) - (t'11 * t'12))
  Vector3'float.Vector3'3 sret (fp + 0)
  return ()

def Vector3'float.operator_'6 (this : UInt64) (sret : UInt64) (v : UInt64) : PMem.M Unit := do
  let fp ← PMem.enter 12
  let r ← Vector3'float.operator_'6.body fp this sret v
  PMem.leave fp
  return r

/-- C++ `QuaternionT<float>::to_axis_angle : void (Vector3<float> &) const`, `quaternion.cpp:497-505`. -/
def QuaternionT'float.to_axis_angle.body (fp : UInt64) (this : UInt64) (v : UInt64) : PMem.M Unit := do
  let t'1 ← PMem.ldF32 (this + 4)
  let t'2 ← sq t'1
  let t'3 ← PMem.ldF32 (this + 8)
  let t'4 ← sq t'3
  let t'5 ← PMem.ldF32 (this + 12)
  let t'6 ← sq t'5
  let mut l : Binary32 := (Binary32.sqrt ((t'2 + t'4) + t'6))
  let t'7 ← PMem.ldF32 (this + 4)
  let t'8 ← PMem.ldF32 (this + 8)
  let t'9 ← PMem.ldF32 (this + 12)
  Vector3'float.Vector3 (fp + 0) t'7 t'8 t'9
  discard <| PMem.memcpy v (fp + 0) 12
  discard <| pure (v)
  let t'10 ← _root_.Vehicle_lib.is_zero l
  if !t'10 then
    let t'11 ← Vector3'float.operator__'5 v l
    discard <| pure (t'11)
    let t'12 ← PMem.ldF32 this
    let t'13 ← wrap_PI'float ((Binary32.ofBits 0x40000000 /- 2 -/) * (Musl.atan2f.atan2f l t'12))
    let t'14 ← Vector3'float.operator__'2 v t'13
    discard <| pure (t'14)
  return ()

def QuaternionT'float.to_axis_angle (this : UInt64) (v : UInt64) : PMem.M Unit := do
  let fp ← PMem.enter 12
  let r ← QuaternionT'float.to_axis_angle.body fp this v
  PMem.leave fp
  return r

/-- `SCurve.get_origin_to_destination` as a pure function of its arguments (it reads and writes no memory). -/
def SCurve.get_origin_to_destination.pure' (this : UInt64) : Id UInt64 := do
  return (this + 588)

/-- C++ `SCurve::get_origin_to_destination : const Vector3f &() const`, `AP_Common.h:98-?`. -/
def SCurve.get_origin_to_destination (this : UInt64) : PMem.M UInt64 :=
  pure (_root_.Vehicle_lib.SCurve.get_origin_to_destination.pure' this)

/-- C++ `Vector2<float>::rotate : void (float)`, `ftype.h:441-449`. -/
def Vector2'float.rotate (this : UInt64) (angle_rad : Binary32) : PMem.M Unit := do
  let mut angle_rad := angle_rad
  let mut cs : Binary32 := (Musl.cosf.cosf angle_rad)
  let mut sn : Binary32 := (Musl.sinf.sinf angle_rad)
  let t'1 ← PMem.ldF32 this
  let t'2 ← PMem.ldF32 (this + 4)
  let mut rx : Binary32 := ((t'1 * cs) - (t'2 * sn))
  let t'3 ← PMem.ldF32 this
  let t'4 ← PMem.ldF32 (this + 4)
  let mut ry : Binary32 := ((t'3 * sn) + (t'4 * cs))
  PMem.stF32 this rx
  PMem.stF32 (this + 4) ry
  return ()

/-- C++ `Vector3<float>::Vector3 : void (const Vector2<float> &, const float)`, `vector3.h:91-94`. -/
def Vector3'float.Vector3'5 (this : UInt64) (v0 : UInt64) (z0 : Binary32) : PMem.M Unit := do
  let mut z0 := z0
  let t'1 ← PMem.ldF32 v0
  PMem.stF32 (this + 0) t'1
  let t'2 ← PMem.ldF32 (v0 + 4)
  PMem.stF32 (this + 4) t'2
  PMem.stF32 (this + 8) z0
  return ()

/-- C++ `SCurve::calculate_circle_track : void (const Vector3p &, const Vector2f &, float, float, float, float, float, float, float, float, float, float)`, `SCurve.cpp:116-160`. -/
def SCurve.calculate_circle_track.body (fp : UInt64) (this : UInt64) (origin : UInt64) (center_ne : UInt64) (total_angle_rad : Binary32) (climb_d_m : Binary32) (speed_xy : Binary32) (speed_up : Binary32) (speed_down : Binary32) (accel_xy : Binary32) (accel_z : Binary32) (accel_c : Binary32) (snap_maximum : Binary32) (jerk_maximum : Binary32) : PMem.M Unit := do
  let mut total_angle_rad := total_angle_rad
  let mut climb_d_m := climb_d_m
  let mut speed_xy := speed_xy
  let mut speed_up := speed_up
  let mut speed_down := speed_down
  let mut accel_xy := accel_xy
  let mut accel_z := accel_z
  let mut accel_c := accel_c
  let mut snap_maximum := snap_maximum
  let mut jerk_maximum := jerk_maximum
  SCurve.init this
  let t'1 := (Binary32.abs speed_xy)
  speed_xy := t'1
  let t'2 := (Binary32.abs speed_up)
  speed_up := t'2
  let t'3 := (Binary32.abs speed_down)
  speed_down := t'3
  let t'4 := (Binary32.abs accel_xy)
  accel_xy := t'4
  let t'5 := (Binary32.abs accel_z)
  accel_z := t'5
  let t'6 ← Vector3'double.xy origin
  Vector2'double.tofloat t'6 (fp + 8)
  let t'7 := (fp + 8)
  Vector2'float.operator_ center_ne (fp + 16) t'7
  let t'8 := (fp + 16)
  Vector2'float.Vector2'3 (fp + 0) t'8
  let t'9 ← Vector2'float.length (fp + 0)
  let mut radius : Binary32 := t'9
  let t'10 ← is_positive'float radius
  let mut sc'12 := !t'10
  if !sc'12 then
    let t'11 ← radians (Binary32.ofBits 0x3f800000 /- 1 -/)
    sc'12 := (decide ((Binary32.abs total_angle_rad) < t'11))
  if sc'12 then
    Vector3'float.zero (this + 588)
    return ()
  Vector2'float.Vector2'4 (fp + 24) (fp + 0)
  Vector2'float.rotate (fp + 24) total_angle_rad
  Vector2'float.operator_ (fp + 0) (fp + 48) (fp + 24)
  let t'13 := (fp + 48)
  Vector3'float.Vector3'5 (fp + 32) t'13 climb_d_m
  discard <| PMem.memcpy (this + 588) (fp + 32) 12
  discard <| pure ((this + 588))
  SCurve.set_arc_geometry this (fp + 0) radius total_angle_rad
  let t'14 ← PMem.ldF32 (this + 600)
  let t'15 ← is_zero t'14
  if t'15 then
    Vector3'float.zero (this + 588)
    return ()
  SCurve.generate_path this speed_xy speed_up speed_down accel_xy accel_z accel_c snap_maximum jerk_maximum
  return ()

def SCurve.calculate_circle_track (this : UInt64) (origin : UInt64) (center_ne : UInt64) (total_angle_rad : Binary32) (climb_d_m : Binary32) (speed_xy : Binary32) (speed_up : Binary32) (speed_down : Binary32) (accel_xy : Binary32) (accel_z : Binary32) (accel_c : Binary32) (snap_maximum : Binary32) (jerk_maximum : Binary32) : PMem.M Unit := do
  let fp ← PMem.enter 56
  let r ← SCurve.calculate_circle_track.body fp this origin center_ne total_angle_rad climb_d_m speed_xy speed_up speed_down accel_xy accel_z accel_c snap_maximum jerk_maximum
  PMem.leave fp
  return r

/-- C++ `SCurve::get_arc_angle_covered_rad : float () const`, `SCurve.cpp:617-633`. -/
def SCurve.get_arc_angle_covered_rad.body (fp : UInt64) (this : UInt64) : PMem.M Binary32 := do
  let t'1 ← PMem.ldB (this + 584)
  let mut sc'4 := !t'1
  if !sc'4 then
    let t'2 ← PMem.ldF32 (this + 600)
    let t'3 ← is_positive'float t'2
    sc'4 := !t'3
  if sc'4 then
    return Binary64.toBinary32 ((Binary64.ofBits 0x0000000000000000 /- 0 -/))
  PMem.stF32 (fp + 0) (Binary32.ofBits 0x00000000 /- 0 -/)
  let t'5 ← PMem.ldF32 (this + 24)
  SCurve.get_jerk_accel_vel_pos_at_time this t'5 (fp + 24) (fp + 16) (fp + 8) (fp + 0)
  let t'6 ← PMem.ldF32 (this + 604)
  let t'7 ← PMem.ldF32 (fp + 0)
  let t'8 ← PMem.ldF32 (this + 600)
  return ((Binary32.abs t'6) * (t'7 / t'8))

def SCurve.get_arc_angle_covered_rad (this : UInt64) : PMem.M Binary32 := do
  let fp ← PMem.enter 28
  let r ← SCurve.get_arc_angle_covered_rad.body fp this
  PMem.leave fp
  return r

/-- C++ `Vector2<double>::length : double () const`, `vector2.cpp:30-33`. -/
def Vector2'double.length (this : UInt64) : PMem.M Binary64 := do
  let t'1 ← PMem.ldF64 this
  let t'2 ← PMem.ldF64 (this + 8)
  let t'3 ← norm'double_double t'1 t'2
  return t'3

/-- C++ `get_horizontal_distance : float (const Vector2<double> &, const Vector2<double> &)`, `location.h:15-18`. -/
def get_horizontal_distance'double.body (fp : UInt64) (origin : UInt64) (destination : UInt64) : PMem.M Binary32 := do
  Vector2'double.operator_ destination (fp + 0) origin
  let t'1 := (fp + 0)
  let t'2 ← Vector2'double.length t'1
  return Binary64.toBinary32 (t'2)

def get_horizontal_distance'double (origin : UInt64) (destination : UInt64) : PMem.M Binary32 := do
  let fp ← PMem.enter 16
  let r ← get_horizontal_distance'double.body fp origin destination
  PMem.leave fp
  return r

/-- C++ `update_vel_accel_xy : void (Vector2f &, const Vector2f &, float, const Vector2f &, const Vector2f &)`, `control.cpp:86-98`. -/
def update_vel_accel_xy.body (fp : UInt64) (vel : UInt64) (accel : UInt64) (dt : Binary32) (limit : UInt64) (vel_error : UInt64) : PMem.M Unit := do
  let mut dt := dt
  Vector2'float.operator_'2 accel (fp + 8) dt
  let t'1 := (fp + 8)
  Vector2'float.Vector2'3 (fp + 0) t'1
  let t'2 ← Vector2'float.is_zero limit
  let mut sc'4 := !t'2
  if sc'4 then
    let t'3 ← Vector2'float.is_zero (fp + 0)
    sc'4 := !t'3
  if sc'4 then
    let t'5 ← Vector2'float.operator_'4 (fp + 0) limit
    let t'6 ← is_positive'float t'5
    let mut sc'9 := t'6
    if sc'9 then
      let t'7 ← Vector2'float.operator_'4 vel_error limit
      let t'8 ← is_positive'float t'7
      sc'9 := t'8
    let mut sc'12 := sc'9
    if sc'12 then
      let t'10 ← Vector2'float.operator_'4 vel limit
      let t'11 ← is_negative'float t'10
      sc'12 := !t'11
    if sc'12 then
      Vector2'float.zero (fp + 0)
  let t'13 ← Vector2'float.operator__ vel (fp + 0)
  discard <| pure (t'13)
  return ()

def update_vel_accel_xy (vel : UInt64) (accel : UInt64) (dt : Binary32) (limit : UInt64) (vel_error : UInt64) : PMem.M Unit := do
  let fp ← PMem.enter 16
  let r ← update_vel_accel_xy.body fp vel accel dt limit vel_error
  PMem.leave fp
  return r

/-- C++ `update_pos_vel_accel_xy : void (Vector2p &, Vector2f &, const Vector2f &, float, const Vector2f &, const Vector2f &, const Vector2f &)`, `control.cpp:106-121`. -/
def update_pos_vel_accel_xy.body (fp : UInt64) (pos : UInt64) (vel : UInt64) (accel : UInt64) (dt : Binary32) (limit : UInt64) (pos_error : UInt64) (vel_error : UInt64) : PMem.M Unit := do
  let mut dt := dt
  Vector2'float.operator_'2 vel (fp + 8) dt
  let t'1 := (fp + 8)
  Vector2'float.operator_'2 accel (fp + 16) (Binary32.ofBits 0x3f000000 /- 1/2 -/)
  let t'2 := (fp + 16)
  let t'3 ← sq dt
  Vector2'float.operator_'2 t'2 (fp + 24) t'3
  let t'4 := (fp + 24)
  Vector2'float.operator_'3 t'1 (fp + 32) t'4
  let t'5 := (fp + 32)
  Vector2'float.Vector2'3 (fp + 0) t'5
  let t'6 ← Vector2'float.length_squared limit
  let t'7 ← is_zero t'6
  if !t'7 then
    let t'8 ← Vector2'float.operator_'4 (fp + 0) limit
    let t'9 ← is_positive'float t'8
    let mut sc'12 := t'9
    if sc'12 then
      let t'10 ← Vector2'float.operator_'4 pos_error limit
      let t'11 ← is_positive'float t'10
      sc'12 := t'11
    if sc'12 then
      Vector2'float.zero (fp + 0)
  Vector2'float.todouble (fp + 0) (fp + 40)
  let t'13 := (fp + 40)
  let t'14 ← Vector2'double.operator__'2 pos t'13
  discard <| pure (t'14)
  update_vel_accel_xy vel accel dt limit vel_error
  return ()

def update_pos_vel_accel_xy (pos : UInt64) (vel : UInt64) (accel : UInt64) (dt : Binary32) (limit : UInt64) (pos_error : UInt64) (vel_error : UInt64) : PMem.M Unit := do
  let fp ← PMem.enter 56
  let r ← update_pos_vel_accel_xy.body fp pos vel accel dt limit pos_error vel_error
  PMem.leave fp
  return r

/-- C++ `Vector2<float>::dot : float (const Vector2<float> &) const`, `vector2.h:96-98`. -/
def Vector2'float.dot (this : UInt64) (v : UInt64) : PMem.M Binary32 := do
  let t'1 ← Vector2'float.operator_'4 this v
  return t'1

/-- C++ `limit_accel_corner_xy : bool (const Vector2f &, Vector2f &, float)`, `control.cpp:512-568`. -/
def limit_accel_corner_xy.body (fp : UInt64) (vel : UInt64) (accel : UInt64) (accel_max : Binary32) : PMem.M Bool := do
  PMem.stF32 (fp + 0) accel_max
  let t'1 ← PMem.ldF32 (fp + 0)
  let t'2 ← is_positive'float t'1
  if !t'2 then
    return false
  let t'3 ← Vector2'float.is_zero vel
  if t'3 then
    let t'4 ← PMem.ldF32 (fp + 0)
    let t'5 ← Vector2'float.limit_length accel t'4
    return t'5
  let t'6 ← PMem.ldF32 (fp + 0)
  let t'7 ← Vector2'float.limit_length accel ((Binary64.toBinary32 ((Binary64.ofBits 0x4000000000000000 /- 2 -/))) * t'6)
  discard <| pure (t'7)
  Vector2'float.normalized vel (fp + 16)
  let t'8 := (fp + 16)
  Vector2'float.Vector2'3 (fp + 8) t'8
  let t'9 ← Vector2'float.dot accel (fp + 8)
  PMem.stF32 (fp + 24) t'9
  let t'10 ← PMem.ldF32 (fp + 24)
  Vector2'float.operator_'2 (fp + 8) (fp + 40) t'10
  let t'11 := (fp + 40)
  Vector2'float.Vector2'3 (fp + 32) t'11
  Vector2'float.operator_ accel (fp + 56) (fp + 32)
  let t'12 := (fp + 56)
  Vector2'float.Vector2'3 (fp + 48) t'12
  let t'13 ← PMem.ldF32 (fp + 24)
  let t'14 ← is_positive'float t'13
  if t'14 then
    let t'15 ← Vector2'float.length (fp + 48)
    PMem.stF32 (fp + 64) t'15
    let t'16 ← MIN'float_float (fp + 64) (fp + 0)
    let t'17 ← PMem.ldF32 t'16
    let mut accel_cross_mag : Binary32 := t'17
    let t'18 ← PMem.ldF32 (fp + 0)
    let t'19 ← sq t'18
    let t'20 ← sq accel_cross_mag
    let t'21 ← safe_sqrt'float (t'19 - t'20)
    let mut accel_along_max : Binary32 := t'21
    let t'22 ← PMem.ldF32 (fp + 0)
    let t'23 ← Vector2'float.limit_length (fp + 48) t'22
    discard <| pure (t'23)
    let t'24 ← Vector2'float.limit_length (fp + 32) accel_along_max
    discard <| pure (t'24)
    Vector2'float.operator_'3 (fp + 48) (fp + 72) (fp + 32)
    let t'25 := (fp + 72)
    discard <| PMem.memcpy accel t'25 8
    discard <| pure (accel)
    return true
  let t'26 ← PMem.ldF32 (fp + 0)
  PMem.stF32 (fp + 80) (-t'26)
  let t'27 ← MAX'float_float (fp + 24) (fp + 80)
  let t'28 ← PMem.ldF32 t'27
  PMem.stF32 (fp + 24) t'28
  let t'29 ← PMem.ldF32 (fp + 24)
  Vector2'float.operator_'2 (fp + 8) (fp + 88) t'29
  let t'30 := (fp + 88)
  discard <| PMem.memcpy (fp + 32) t'30 8
  discard <| pure ((fp + 32))
  let t'31 ← PMem.ldF32 (fp + 0)
  let t'32 ← sq t'31
  let t'33 ← PMem.ldF32 (fp + 24)
  let t'34 ← sq t'33
  let t'35 ← safe_sqrt'float (t'32 - t'34)
  let mut accel_cross_max : Binary32 := t'35
  let t'36 ← Vector2'float.limit_length (fp + 48) accel_cross_max
  discard <| pure (t'36)
  Vector2'float.operator_'3 (fp + 48) (fp + 96) (fp + 32)
  let t'37 := (fp + 96)
  discard <| PMem.memcpy accel t'37 8
  discard <| pure (accel)
  return true

def limit_accel_corner_xy (vel : UInt64) (accel : UInt64) (accel_max : Binary32) : PMem.M Bool := do
  let fp ← PMem.enter 104
  let r ← limit_accel_corner_xy.body fp vel accel accel_max
  PMem.leave fp
  return r

/-- C++ `shape_accel_xy : void (const Vector2f &, Vector2f &, float, float)`, `control.cpp:148-163`. -/
def shape_accel_xy.body (fp : UInt64) (accel_desired : UInt64) (accel : UInt64) (jerk_max : Binary32) (dt : Binary32) : PMem.M Unit := do
  let mut jerk_max := jerk_max
  let mut dt := dt
  let t'1 ← is_positive'float jerk_max
  if !t'1 then
    return ()
  let t'2 ← is_positive'float dt
  if t'2 then
    Vector2'float.operator_ accel_desired (fp + 8) accel
    let t'3 := (fp + 8)
    Vector2'float.Vector2'3 (fp + 0) t'3
    let t'4 ← Vector2'float.limit_length (fp + 0) (jerk_max * dt)
    discard <| pure (t'4)
    Vector2'float.operator_'3 accel (fp + 16) (fp + 0)
    let t'5 := (fp + 16)
    discard <| PMem.memcpy accel t'5 8
    discard <| pure (accel)
  return ()

def shape_accel_xy (accel_desired : UInt64) (accel : UInt64) (jerk_max : Binary32) (dt : Binary32) : PMem.M Unit := do
  let fp ← PMem.enter 24
  let r ← shape_accel_xy.body fp accel_desired accel jerk_max dt
  PMem.leave fp
  return r

/-- C++ `shape_pos_vel_accel_xy : void (const Vector2p &, const Vector2f &, const Vector2f &, const Vector2p &, const Vector2f &, Vector2f &, float, float, float, float, bool)`, `control.cpp:356-422`. -/
def shape_pos_vel_accel_xy.body (fp : UInt64) (pos_desired : UInt64) (vel_desired : UInt64) (accel_desired : UInt64) (pos : UInt64) (vel : UInt64) (accel : UInt64) (vel_max : Binary32) (accel_max : Binary32) (jerk_max : Binary32) (dt : Binary32) (limit_total : Bool) : PMem.M Unit := do
  let mut vel_max := vel_max
  let mut accel_max := accel_max
  let mut jerk_max := jerk_max
  let mut dt := dt
  let mut limit_total := limit_total
  let t'1 ← is_negative'float vel_max
  let mut sc'3 := t'1
  if !sc'3 then
    let t'2 ← is_positive'float accel_max
    sc'3 := !t'2
  let mut sc'5 := sc'3
  if !sc'5 then
    let t'4 ← is_positive'float jerk_max
    sc'5 := !t'4
  if sc'5 then
    return ()
  let mut k_v : Binary32 := (jerk_max / accel_max)
  Vector2'float.Vector2 (fp + 0)
  Vector2'double.operator_ pos_desired (fp + 16) pos
  let t'6 := (fp + 16)
  Vector2'double.tofloat t'6 (fp + 32)
  let t'7 := (fp + 32)
  Vector2'float.Vector2'3 (fp + 8) t'7
  let t'8 ← Vector2'float.length (fp + 8)
  let mut pos_error_length : Binary32 := t'8
  let t'9 ← is_positive'float pos_error_length
  if t'9 then
    Vector2'float.operator_ vel (fp + 40) vel_desired
    let t'10 := (fp + 40)
    let t'11 ← Vector2'float.dot t'10 (fp + 8)
    let mut vel_corr_proj : Binary32 := (t'11 / pos_error_length)
    let t'12 ← sqrt_controller pos_error_length k_v accel_max dt
    let mut vel_corr_cmd_length : Binary32 := t'12
    let t'13 ← sqrt_controller_accel pos_error_length vel_corr_cmd_length vel_corr_proj k_v accel_max
    let mut accel_corr_cmd_length : Binary32 := t'13
    let t'14 := (vel_corr_cmd_length + (accel_corr_cmd_length / k_v))
    vel_corr_cmd_length := t'14
    let t'15 ← is_positive'float vel_max
    if t'15 then
      let t'16 ← constrain_value_line'float vel_corr_cmd_length (-vel_max) vel_max (Int32.toUInt32 ((392 : Int32)))
      vel_corr_cmd_length := t'16
    Vector2'float.operator_'2 (fp + 8) (fp + 48) (vel_corr_cmd_length / pos_error_length)
    let t'17 := (fp + 48)
    discard <| PMem.memcpy (fp + 0) t'17 8
    discard <| pure ((fp + 0))
  Vector2'float.operator_'3 vel_desired (fp + 64) (fp + 0)
  let t'18 := (fp + 64)
  Vector2'float.Vector2'3 (fp + 56) t'18
  let mut sc'20 := limit_total
  if sc'20 then
    let t'19 ← is_positive'float vel_max
    sc'20 := t'19
  if sc'20 then
    let t'21 ← Vector2'float.limit_length (fp + 56) vel_max
    discard <| pure (t'21)
  Vector2'float.operator_ (fp + 56) (fp + 80) vel
  let t'22 := (fp + 80)
  Vector2'float.operator_'2 t'22 (fp + 88) k_v
  let t'23 := (fp + 88)
  Vector2'float.Vector2'3 (fp + 72) t'23
  let t'24 ← limit_accel_corner_xy vel (fp + 72) accel_max
  discard <| pure (t'24)
  let t'25 ← Vector2'float.operator__ (fp + 72) accel_desired
  discard <| pure (t'25)
  if limit_total then
    let t'26 ← Vector2'float.limit_length (fp + 72) accel_max
    discard <| pure (t'26)
  shape_accel_xy (fp + 72) accel jerk_max dt
  return ()

def shape_pos_vel_accel_xy (pos_desired : UInt64) (vel_desired : UInt64) (accel_desired : UInt64) (pos : UInt64) (vel : UInt64) (accel : UInt64) (vel_max : Binary32) (accel_max : Binary32) (jerk_max : Binary32) (dt : Binary32) (limit_total : Bool) : PMem.M Unit := do
  let fp ← PMem.enter 96
  let r ← shape_pos_vel_accel_xy.body fp pos_desired vel_desired accel_desired pos vel accel vel_max accel_max jerk_max dt limit_total
  PMem.leave fp
  return r

/-- C++ `Vector2<double>::Vector2 : void (const Vector2<double> &) noexcept`, `AP_Common.h:45-?`. -/
def Vector2'double.Vector2'4 (this : UInt64) (arg : UInt64) : PMem.M Unit := do
  let t'1 ← PMem.ldF64 arg
  PMem.stF64 (this + 0) t'1
  let t'2 ← PMem.ldF64 (arg + 8)
  PMem.stF64 (this + 8) t'2
  return ()

/-- C++ `sqrt_controller : Vector2f (const Vector2f &, float, float, float)`, `control.cpp:616-625`. -/
def sqrt_controller'2.body (fp : UInt64) (sret : UInt64) (error : UInt64) (p : Binary32) (second_ord_lim : Binary32) (dt : Binary32) : PMem.M Unit := do
  let mut p := p
  let mut second_ord_lim := second_ord_lim
  let mut dt := dt
  let t'1 ← Vector2'float.length error
  let mut error_length : Binary32 := t'1
  let t'2 ← is_positive'float error_length
  if !t'2 then
    Vector2'float.Vector2 (fp + 0)
    Vector2'float.Vector2'3 sret (fp + 0)
    return ()
  let t'3 ← sqrt_controller error_length p second_ord_lim dt
  let mut correction_length : Binary32 := t'3
  Vector2'float.operator_'2 error (fp + 8) (correction_length / error_length)
  let t'4 := (fp + 8)
  Vector2'float.Vector2'3 sret t'4
  return ()

def sqrt_controller'2 (sret : UInt64) (error : UInt64) (p : Binary32) (second_ord_lim : Binary32) (dt : Binary32) : PMem.M Unit := do
  let fp ← PMem.enter 16
  let r ← sqrt_controller'2.body fp sret error p second_ord_lim dt
  PMem.leave fp
  return r

/-- C++ `Vector2<float>::is_nan : bool () const`, `ftype.h:84-87`. -/
def Vector2'float.is_nan (this : UInt64) : PMem.M Bool := do
  let t'1 ← PMem.ldF32 this
  let mut sc'3 := (Binary32.isNaN t'1)
  if !sc'3 then
    let t'2 ← PMem.ldF32 (this + 4)
    sc'3 := (Binary32.isNaN t'2)
  return sc'3

/-- C++ `Vector2<float>::is_inf : bool () const`, `vector2.cpp:90-93`. -/
def Vector2'float.is_inf (this : UInt64) : PMem.M Bool := do
  let t'1 ← PMem.ldF32 this
  let mut sc'3 := (Binary32.isInf t'1)
  if !sc'3 then
    let t'2 ← PMem.ldF32 (this + 4)
    sc'3 := (Binary32.isInf t'2)
  return sc'3

/-- C++ `limit_accel_xy : bool (const Vector2f &, Vector2f &, float)`, `control.cpp:449-501`. -/
def limit_accel_xy.body (fp : UInt64) (vel_norm : UInt64) (accel : UInt64) (accel_max : Binary32) : PMem.M Bool := do
  let mut accel_max := accel_max
  let t'1 ← is_positive'float accel_max
  if !t'1 then
    return false
  let t'2 ← Vector2'float.length_squared accel
  let t'3 ← sq accel_max
  if (decide (t'2 ≤ t'3)) then
    return false
  Vector2'float.Vector2'4 (fp + 0) accel
  let t'4 ← Vector2'float.limit_length (fp + 0) accel_max
  discard <| pure (t'4)
  let t'5 ← Vector2'float.length vel_norm
  let mut ref_mag : Binary32 := t'5
  let t'6 ← is_positive'float ref_mag
  if !t'6 then
    discard <| PMem.memcpy accel (fp + 0) 8
    discard <| pure (accel)
    return true
  Vector2'float.operator_'5 vel_norm (fp + 16) ref_mag
  let t'7 := (fp + 16)
  Vector2'float.Vector2'3 (fp + 8) t'7
  let t'8 ← Vector2'float.operator_'4 (fp + 8) accel
  let mut accel_dir : Binary32 := t'8
  Vector2'float.operator_'2 (fp + 8) (fp + 32) accel_dir
  let t'9 := (fp + 32)
  Vector2'float.operator_ accel (fp + 40) t'9
  let t'10 := (fp + 40)
  Vector2'float.Vector2'3 (fp + 24) t'10
  let t'11 ← Vector2'float.limit_length (fp + 24) accel_max
  if t'11 then
    let t'12 := Binary64.toBinary32 ((Binary64.ofBits 0x0000000000000000 /- 0 -/))
    accel_dir := t'12
  else
    let t'13 ← sq accel_max
    let t'14 ← Vector2'float.length_squared (fp + 24)
    let t'15 ← safe_sqrt'float (t'13 - t'14)
    let mut accel_max_dir : Binary32 := t'15
    let t'16 ← constrain_value_line'float accel_dir (-accel_max_dir) accel_max_dir (Int32.toUInt32 ((486 : Int32)))
    accel_dir := t'16
  Vector2'float.operator_'2 (fp + 8) (fp + 56) accel_dir
  let t'17 := (fp + 56)
  Vector2'float.operator_'3 (fp + 24) (fp + 64) t'17
  let t'18 := (fp + 64)
  Vector2'float.Vector2'3 (fp + 48) t'18
  let t'19 ← constrain_value_line'float (ref_mag / (Binary32.ofBits 0x3e800000 /- 1/4 -/)) (Binary32.ofBits 0x00000000 /- 0 -/) (Binary32.ofBits 0x3f800000 /- 1 -/) (Int32.toUInt32 ((497 : Int32)))
  let mut prioritise_ratio : Binary32 := t'19
  Vector2'float.operator_'2 (fp + 0) (fp + 72) ((Binary32.ofBits 0x3f800000 /- 1 -/) - prioritise_ratio)
  let t'20 := (fp + 72)
  Vector2'float.operator_'2 (fp + 48) (fp + 80) prioritise_ratio
  let t'21 := (fp + 80)
  Vector2'float.operator_'3 t'20 (fp + 88) t'21
  let t'22 := (fp + 88)
  discard <| PMem.memcpy accel t'22 8
  discard <| pure (accel)
  return true

def limit_accel_xy (vel_norm : UInt64) (accel : UInt64) (accel_max : Binary32) : PMem.M Bool := do
  let fp ← PMem.enter 96
  let r ← limit_accel_xy.body fp vel_norm accel accel_max
  PMem.leave fp
  return r

/-- `accel_mss_to_angle_rad` as a pure function of its arguments (it reads and writes no memory). -/
def accel_mss_to_angle_rad.pure' (accel_mss : Binary32) : Id Binary32 := do
  let mut accel_mss := accel_mss
  return (Musl.atanf.atanf (accel_mss / (Binary32.ofBits 0x411ce80a /- 122583127/12500000 -/)))

/-- C++ `accel_mss_to_angle_rad : float (float)`, `control.cpp:838-842`. -/
def accel_mss_to_angle_rad (accel_mss : Binary32) : PMem.M Binary32 :=
  pure (_root_.Vehicle_lib.accel_mss_to_angle_rad.pure' accel_mss)

/-- C++ `Vector2<float>::angle : float () const`, `ftype.h:162-165`. -/
def Vector2'float.angle (this : UInt64) : PMem.M Binary32 := do
  let t'1 ← PMem.ldF32 (this + 4)
  let t'2 ← PMem.ldF32 this
  return (Musl.atan2f.atan2f t'1 t'2)

/-- C++ `Vector3<float>::normalize : void ()`, `vector3.h:223-226`. -/
def Vector3'float.normalize (this : UInt64) : PMem.M Unit := do
  let t'1 ← Vector3'float.length this
  let t'2 ← Vector3'float.operator__'5 this t'1
  discard <| pure (t'2)
  return ()

/-- C++ `SCurve::advance_time : void (float)`, `SCurve.cpp:778-781`. -/
def SCurve.advance_time.body (fp : UInt64) (this : UInt64) (dt : Binary32) : PMem.M Unit := do
  let mut dt := dt
  let t'1 ← PMem.ldF32 (this + 24)
  PMem.stF32 (fp + 0) (t'1 + dt)
  let t'2 ← SCurve.time_end this
  PMem.stF32 (fp + 4) t'2
  let t'3 ← MIN'float_float (fp + 0) (fp + 4)
  let t'4 ← PMem.ldF32 t'3
  PMem.stF32 (this + 24) t'4
  return ()

def SCurve.advance_time (this : UInt64) (dt : Binary32) : PMem.M Unit := do
  let fp ← PMem.enter 8
  let r ← SCurve.advance_time.body fp this dt
  PMem.leave fp
  return r

/-- C++ `Vector2<float>::operator- : Vector2<float> () const`, `vector2.cpp:127-130`. -/
def Vector2'float.operator_'6.body (fp : UInt64) (this : UInt64) (sret : UInt64) : PMem.M Unit := do
  let t'1 ← PMem.ldF32 this
  let t'2 ← PMem.ldF32 (this + 4)
  Vector2'float.Vector2'2 (fp + 0) (-t'1) (-t'2)
  Vector2'float.Vector2'3 sret (fp + 0)
  return ()

def Vector2'float.operator_'6 (this : UInt64) (sret : UInt64) : PMem.M Unit := do
  let fp ← PMem.enter 8
  let r ← Vector2'float.operator_'6.body fp this sret
  PMem.leave fp
  return r

/-- C++ `Vector2<float>::operator/= : Vector2<float> &(const float)`, `vector2.cpp:70-74`. -/
def Vector2'float.operator__'4 (this : UInt64) (num : Binary32) : PMem.M UInt64 := do
  let mut num := num
  let t'1 ← PMem.ldF32 this
  let t'2 := (t'1 / num)
  PMem.stF32 this t'2
  let t'3 := (this + 4)
  let t'4 ← PMem.ldF32 t'3
  let t'5 := (t'4 / num)
  PMem.stF32 t'3 t'5
  return this

/-- C++ `SCurve::project_scurve_onto_track : void (float, float, float, Vector3p &, Vector3f &, Vector3f &)`, `SCurve.cpp:668-719`. -/
def SCurve.project_scurve_onto_track.body (fp : UInt64) (this : UInt64) (scurve_A1 : Binary32) (scurve_V1 : Binary32) (scurve_P1 : Binary32) (pos : UInt64) (vel : UInt64) (accel : UInt64) : PMem.M Unit := do
  let mut scurve_A1 := scurve_A1
  let mut scurve_V1 := scurve_V1
  let mut scurve_P1 := scurve_P1
  let t'1 ← PMem.ldF32 (this + 600)
  let t'2 ← is_zero t'1
  if t'2 then
    return ()
  let t'3 ← PMem.ldB (this + 584)
  if t'3 then
    let t'4 ← PMem.ldF32 ((this + 604) + 8)
    let t'5 ← is_positive'float t'4
    if !t'5 then
      SCurve.init this
      return ()
    Vector2'float.operator_'6 ((this + 604) + 12) (fp + 8)
    let t'6 := (fp + 8)
    Vector2'float.Vector2'3 (fp + 0) t'6
    let t'7 ← PMem.ldF32 (this + 604)
    let t'8 ← is_negative'float t'7
    let mut c'9 : Binary32 := default
    if t'8 then
      c'9 := -(Binary32.ofBits 0x3f800000 /- 1 -/)
    else
      c'9 := (Binary32.ofBits 0x3f800000 /- 1 -/)
    let mut turn_dir : Binary32 := c'9
    let t'10 ← PMem.ldF32 (this + 604)
    let t'11 ← PMem.ldF32 (this + 600)
    Vector2'float.rotate (fp + 0) ((turn_dir * (Binary32.abs t'10)) * (scurve_P1 / t'11))
    let t'12 ← PMem.ldF32 ((this + 588) + 8)
    let t'13 ← PMem.ldF32 (this + 600)
    let mut dz_ds : Binary32 := (t'12 / t'13)
    Vector2'float.operator_'3 ((this + 604) + 12) (fp + 32) (fp + 0)
    let t'14 := (fp + 32)
    Vector3'float.Vector3'5 (fp + 16) t'14 (scurve_P1 * dz_ds)
    Vector3'float.todouble (fp + 16) (fp + 40)
    let t'15 := (fp + 40)
    let t'16 ← Vector3'double.operator__ pos t'15
    discard <| pure (t'16)
    let t'17 ← PMem.ldF32 ((fp + 0) + 4)
    let t'18 ← PMem.ldF32 (fp + 0)
    Vector2'float.Vector2'2 (fp + 72) (-t'17) t'18
    Vector2'float.operator_'2 (fp + 72) (fp + 80) turn_dir
    let t'19 := (fp + 80)
    Vector2'float.Vector2'3 (fp + 64) t'19
    let t'20 ← PMem.ldF32 ((this + 604) + 8)
    let t'21 ← Vector2'float.operator__'4 (fp + 64) t'20
    discard <| pure (t'21)
    let t'22 ← PMem.ldF32 ((this + 604) + 4)
    let t'23 ← PMem.ldF32 (this + 600)
    let mut horiz_ds : Binary32 := (t'22 / t'23)
    let t'24 ← PMem.ldF32 (fp + 64)
    let t'25 ← PMem.ldF32 ((fp + 64) + 4)
    Vector3'float.Vector3 (fp + 88) (t'24 * horiz_ds) (t'25 * horiz_ds) dz_ds
    Vector3'float.operator_ (fp + 88) (fp + 104) scurve_V1
    let t'26 := (fp + 104)
    let t'27 ← Vector3'float.operator__'3 vel t'26
    discard <| pure (t'27)
    Vector3'float.operator_ (fp + 88) (fp + 120) scurve_A1
    let t'28 := (fp + 120)
    let t'29 ← Vector3'float.operator__'3 accel t'28
    discard <| pure (t'29)
    let t'30 ← Vector3'float.xy accel
    let t'31 ← PMem.ldF32 ((this + 604) + 8)
    let t'32 ← sq ((scurve_V1 * horiz_ds) / t'31)
    Vector2'float.operator_'2 (fp + 0) (fp + 136) t'32
    let t'33 := (fp + 136)
    let t'34 ← Vector2'float.operator__'2 t'30 t'33
    discard <| pure (t'34)
    return ()
  Vector3'float.normalized (this + 588) (fp + 160)
  let t'35 := (fp + 160)
  Vector3'float.Vector3'3 (fp + 144) t'35
  Vector3'float.todouble (fp + 144) (fp + 176)
  let t'36 := (fp + 176)
  Vector3'double.operator_'3 t'36 (fp + 200) (Binary32.toBinary64 (scurve_P1))
  let t'37 := (fp + 200)
  let t'38 ← Vector3'double.operator__ pos t'37
  discard <| pure (t'38)
  Vector3'float.operator_ (fp + 144) (fp + 224) scurve_V1
  let t'39 := (fp + 224)
  let t'40 ← Vector3'float.operator__'3 vel t'39
  discard <| pure (t'40)
  Vector3'float.operator_ (fp + 144) (fp + 240) scurve_A1
  let t'41 := (fp + 240)
  let t'42 ← Vector3'float.operator__'3 accel t'41
  discard <| pure (t'42)
  return ()

def SCurve.project_scurve_onto_track (this : UInt64) (scurve_A1 : Binary32) (scurve_V1 : Binary32) (scurve_P1 : Binary32) (pos : UInt64) (vel : UInt64) (accel : UInt64) : PMem.M Unit := do
  let fp ← PMem.enter 252
  let r ← SCurve.project_scurve_onto_track.body fp this scurve_A1 scurve_V1 scurve_P1 pos vel accel
  PMem.leave fp
  return r

/-- C++ `Vector3<double>::operator-= : Vector3<double> &(const Vector3<double> &)`, `vector3.cpp:357-361`. -/
def Vector3'double.operator__'3 (this : UInt64) (v : UInt64) : PMem.M UInt64 := do
  let t'1 ← PMem.ldF64 this
  let t'2 ← PMem.ldF64 v
  let t'3 := (t'1 - t'2)
  PMem.stF64 this t'3
  let t'4 := (this + 8)
  let t'5 ← PMem.ldF64 t'4
  let t'6 ← PMem.ldF64 (v + 8)
  let t'7 := (t'5 - t'6)
  PMem.stF64 t'4 t'7
  let t'8 := (this + 16)
  let t'9 ← PMem.ldF64 t'8
  let t'10 ← PMem.ldF64 (v + 16)
  let t'11 := (t'9 - t'10)
  PMem.stF64 t'8 t'11
  return this

/-- C++ `SCurve::move_to_pos_vel_accel : void (float, Vector3p &, Vector3f &, Vector3f &)`, `SCurve.cpp:646-654`. -/
def SCurve.move_to_pos_vel_accel.body (fp : UInt64) (this : UInt64) (dt : Binary32) (pos : UInt64) (vel : UInt64) (accel : UInt64) : PMem.M Unit := do
  let mut dt := dt
  SCurve.advance_time this dt
  PMem.stF32 (fp + 0) (Binary32.ofBits 0x00000000 /- 0 -/)
  let t'1 ← PMem.ldF32 (this + 24)
  SCurve.get_jerk_accel_vel_pos_at_time this t'1 (fp + 24) (fp + 16) (fp + 8) (fp + 0)
  let t'2 ← PMem.ldF32 (fp + 16)
  let t'3 ← PMem.ldF32 (fp + 8)
  let t'4 ← PMem.ldF32 (fp + 0)
  SCurve.project_scurve_onto_track this t'2 t'3 t'4 pos vel accel
  Vector3'float.todouble (this + 588) (fp + 32)
  let t'5 := (fp + 32)
  let t'6 ← Vector3'double.operator__'3 pos t'5
  discard <| pure (t'6)
  return ()

def SCurve.move_to_pos_vel_accel (this : UInt64) (dt : Binary32) (pos : UInt64) (vel : UInt64) (accel : UInt64) : PMem.M Unit := do
  let fp ← PMem.enter 56
  let r ← SCurve.move_to_pos_vel_accel.body fp this dt pos vel accel
  PMem.leave fp
  return r

/-- C++ `SCurve::move_from_pos_vel_accel : void (float, Vector3p &, Vector3f &, Vector3f &)`, `SCurve.cpp:636-643`. -/
def SCurve.move_from_pos_vel_accel.body (fp : UInt64) (this : UInt64) (dt : Binary32) (pos : UInt64) (vel : UInt64) (accel : UInt64) : PMem.M Unit := do
  let mut dt := dt
  SCurve.advance_time this dt
  PMem.stF32 (fp + 0) (Binary32.ofBits 0x00000000 /- 0 -/)
  let t'1 ← PMem.ldF32 (this + 24)
  SCurve.get_jerk_accel_vel_pos_at_time this t'1 (fp + 24) (fp + 16) (fp + 8) (fp + 0)
  let t'2 ← PMem.ldF32 (fp + 16)
  let t'3 ← PMem.ldF32 (fp + 8)
  let t'4 ← PMem.ldF32 (fp + 0)
  SCurve.project_scurve_onto_track this t'2 t'3 t'4 pos vel accel
  return ()

def SCurve.move_from_pos_vel_accel (this : UInt64) (dt : Binary32) (pos : UInt64) (vel : UInt64) (accel : UInt64) : PMem.M Unit := do
  let fp ← PMem.enter 28
  let r ← SCurve.move_from_pos_vel_accel.body fp this dt pos vel accel
  PMem.leave fp
  return r

/-- C++ `SCurve::get_time_remaining : float () const`, `SCurve.cpp:731-737`. -/
def SCurve.get_time_remaining (this : UInt64) : PMem.M Binary32 := do
  let t'1 ← PMem.ldU8 (this + 28)
  if ((UInt32.toInt32 (UInt8.toUInt32 (t'1))) != (UInt32.toInt32 (UInt8.toUInt32 ((23 : UInt8))))) then
    return (Binary32.ofBits 0x00000000 /- 0 -/)
  let t'2 ← PMem.ldF32 (((this + 32) + ((Int32.toInt64 ((22 : Int32))) * 24).toUInt64) + 8)
  let t'3 ← PMem.ldF32 (this + 24)
  return (t'2 - t'3)

/-- C++ `SCurve::get_time_elapsed : float () const`, `AP_Common.h:141-?`. -/
def SCurve.get_time_elapsed (this : UInt64) : PMem.M Binary32 := do
  let t'1 ← PMem.ldF32 (this + 24)
  return t'1

/-- C++ `SCurve::time_decel_start : float () const`, `SCurve.cpp:769-775`. -/
def SCurve.time_decel_start (this : UInt64) : PMem.M Binary32 := do
  let t'1 ← PMem.ldU8 (this + 28)
  if ((UInt32.toInt32 (UInt8.toUInt32 (t'1))) != (UInt32.toInt32 (UInt8.toUInt32 ((23 : UInt8))))) then
    return (Binary32.ofBits 0x00000000 /- 0 -/)
  let t'2 ← PMem.ldF32 (((this + 32) + ((Int32.toInt64 ((15 : Int32))) * 24).toUInt64) + 8)
  return t'2

/-- C++ `SCurve::time_accel_end : float () const`, `SCurve.cpp:759-765`. -/
def SCurve.time_accel_end (this : UInt64) : PMem.M Binary32 := do
  let t'1 ← PMem.ldU8 (this + 28)
  if ((UInt32.toInt32 (UInt8.toUInt32 (t'1))) != (UInt32.toInt32 (UInt8.toUInt32 ((23 : UInt8))))) then
    return (Binary32.ofBits 0x00000000 /- 0 -/)
  let t'2 ← PMem.ldF32 (((this + 32) + ((Int32.toInt64 ((7 : Int32))) * 24).toUInt64) + 8)
  return t'2

/-- C++ `SCurve::move_from_time_pos_vel_accel : void (float, Vector3p &, Vector3f &, Vector3f &)`, `SCurve.cpp:657-663`. -/
def SCurve.move_from_time_pos_vel_accel.body (fp : UInt64) (this : UInt64) (time_now : Binary32) (pos : UInt64) (vel : UInt64) (accel : UInt64) : PMem.M Unit := do
  let mut time_now := time_now
  PMem.stF32 (fp + 0) (Binary32.ofBits 0x00000000 /- 0 -/)
  PMem.stF32 (fp + 8) (Binary32.ofBits 0x00000000 /- 0 -/)
  PMem.stF32 (fp + 16) (Binary32.ofBits 0x00000000 /- 0 -/)
  PMem.stF32 (fp + 24) (Binary32.ofBits 0x00000000 /- 0 -/)
  SCurve.get_jerk_accel_vel_pos_at_time this time_now (fp + 24) (fp + 16) (fp + 8) (fp + 0)
  let t'1 ← PMem.ldF32 (fp + 16)
  let t'2 ← PMem.ldF32 (fp + 8)
  let t'3 ← PMem.ldF32 (fp + 0)
  SCurve.project_scurve_onto_track this t'1 t'2 t'3 pos vel accel
  return ()

def SCurve.move_from_time_pos_vel_accel (this : UInt64) (time_now : Binary32) (pos : UInt64) (vel : UInt64) (accel : UInt64) : PMem.M Unit := do
  let fp ← PMem.enter 28
  let r ← SCurve.move_from_time_pos_vel_accel.body fp this time_now pos vel accel
  PMem.leave fp
  return r

/-- C++ `SCurve::get_speed_along_track : float () const`, `AP_Common.h:132-?`. -/
def SCurve.get_speed_along_track (this : UInt64) : PMem.M Binary32 := do
  let t'1 ← PMem.ldF32 (this + 20)
  return t'1

/-- C++ `SCurve::get_accel_z_max : float () const`, `AP_Common.h:138-?`. -/
def SCurve.get_accel_z_max (this : UInt64) : PMem.M Binary32 := do
  let t'1 ← PMem.ldF32 (this + 16)
  return t'1

/-- C++ `SCurve::advance_target_along_track : bool (SCurve &, SCurve &, float, float, bool, float, Vector3p &, Vector3f &, Vector3f &)`, `SCurve.cpp:570-607`. -/
def SCurve.advance_target_along_track.body (fp : UInt64) (this : UInt64) (prev_leg : UInt64) (next_leg : UInt64) (wp_radius : Binary32) (accel_corner : Binary32) (fast_waypoint : Bool) (dt : Binary32) (target_pos : UInt64) (target_vel : UInt64) (target_accel : UInt64) : PMem.M Bool := do
  let mut wp_radius := wp_radius
  let mut accel_corner := accel_corner
  let mut fast_waypoint := fast_waypoint
  let mut dt := dt
  SCurve.move_to_pos_vel_accel prev_leg dt target_pos target_vel target_accel
  SCurve.move_from_pos_vel_accel this dt target_pos target_vel target_accel
  let t'1 ← SCurve.finished this
  let mut s_finished : Bool := t'1
  let t'2 ← SCurve.get_time_remaining this
  let mut time_to_destination : Binary32 := t'2
  let mut sc'5 := fast_waypoint
  if sc'5 then
    let t'3 ← SCurve.get_time_elapsed next_leg
    let t'4 ← is_zero t'3
    sc'5 := t'4
  let mut sc'8 := sc'5
  if sc'8 then
    let t'6 ← SCurve.get_time_elapsed this
    let t'7 ← SCurve.time_decel_start this
    sc'8 := (decide (t'6 ≥ t'7))
  let mut sc'11 := sc'8
  if sc'11 then
    let t'9 ← SCurve.get_time_remaining this
    let t'10 ← SCurve.time_accel_end next_leg
    sc'11 := (decide (t'9 ≤ t'10))
  if sc'11 then
    let t'12 ← SCurve.get_origin_to_destination this
    Vector3'float.todouble t'12 (fp + 24)
    let t'13 := (fp + 24)
    Vector3'double.operator_'2 t'13 (fp + 48)
    let t'14 := (fp + 48)
    Vector3'double.Vector3'2 (fp + 0) t'14
    Vector3'float.Vector3'2 (fp + 72)
    Vector3'float.Vector3'2 (fp + 88)
    let t'15 ← SCurve.get_time_elapsed this
    SCurve.move_from_time_pos_vel_accel this (t'15 + (time_to_destination * (Binary32.ofBits 0x3f000000 /- 1/2 -/))) (fp + 0) (fp + 72) (fp + 88)
    SCurve.move_from_time_pos_vel_accel next_leg (time_to_destination * (Binary32.ofBits 0x3f000000 /- 1/2 -/)) (fp + 0) (fp + 72) (fp + 88)
    let t'16 ← SCurve.get_speed_along_track this
    PMem.stF32 (fp + 100) t'16
    let t'17 ← SCurve.get_speed_along_track next_leg
    PMem.stF32 (fp + 104) t'17
    let t'18 ← MIN'float_float (fp + 100) (fp + 104)
    let t'19 ← PMem.ldF32 t'18
    let mut speed_min : Binary32 := t'19
    let t'20 ← SCurve.get_accel_z_max this
    PMem.stF32 (fp + 108) t'20
    let t'21 ← SCurve.get_accel_z_max next_leg
    PMem.stF32 (fp + 112) t'21
    let t'22 ← MIN'float_float (fp + 108) (fp + 112)
    let t'23 ← PMem.ldF32 t'22
    let mut accel_z_lim : Binary32 := t'23
    let t'24 ← Vector3'double.length (fp + 0)
    let mut sc'26 := (decide (t'24 < (Binary32.toBinary64 (wp_radius))))
    if sc'26 then
      let t'25 ← Vector3'float.length (fp + 72)
      sc'26 := (decide (t'25 < speed_min))
    let mut sc'30 := sc'26
    if sc'30 then
      let t'27 ← PMem.ldF32 (fp + 88)
      let t'28 ← PMem.ldF32 ((fp + 88) + 4)
      Vector2'float.Vector2'2 (fp + 120) t'27 t'28
      let t'29 ← Vector2'float.length (fp + 120)
      sc'30 := (decide (t'29 < accel_corner))
    let mut sc'32 := sc'30
    if sc'32 then
      let t'31 ← PMem.ldF32 ((fp + 88) + 8)
      sc'32 := (decide ((Binary32.abs t'31) < accel_z_lim))
    if sc'32 then
      SCurve.move_from_pos_vel_accel next_leg dt target_pos target_vel target_accel
  else
    let t'33 ← SCurve.get_time_elapsed next_leg
    let t'34 ← is_zero t'33
    if !t'34 then
      SCurve.move_from_pos_vel_accel next_leg dt target_pos target_vel target_accel
      let t'35 ← SCurve.get_time_elapsed next_leg
      let t'36 ← SCurve.get_time_remaining this
      if (decide (t'35 ≥ t'36)) then
        s_finished := true
  return s_finished

def SCurve.advance_target_along_track (this : UInt64) (prev_leg : UInt64) (next_leg : UInt64) (wp_radius : Binary32) (accel_corner : Binary32) (fast_waypoint : Bool) (dt : Binary32) (target_pos : UInt64) (target_vel : UInt64) (target_accel : UInt64) : PMem.M Bool := do
  let fp ← PMem.enter 128
  let r ← SCurve.advance_target_along_track.body fp this prev_leg next_leg wp_radius accel_corner fast_waypoint dt target_pos target_vel target_accel
  PMem.leave fp
  return r

/-- C++ `SplineCurve::advance_target_along_track : void (float, Vector3p &, Vector3f &)`, `SplineCurve.cpp:102-130`. -/
def SplineCurve.advance_target_along_track.body (fp : UInt64) (this : UInt64) (dt : Binary32) (target_pos : UInt64) (target_vel : UInt64) : PMem.M Unit := do
  let mut dt := dt
  let t'1 ← PMem.ldB (this + 201)
  if t'1 then
    discard <| PMem.memcpy target_pos (this + 24) 24
    discard <| pure (target_pos)
    Vector3'float.zero target_vel
    return ()
  let t'2 ← Vector3'float.length target_vel
  let mut speed_cms : Binary32 := t'2
  let mut distance_delta : Binary32 := (speed_cms * dt)
  Vector3'float.Vector3'2 (fp + 8)
  let t'3 ← PMem.ldF32 (this + 168)
  SplineCurve.calc_dt_speed_max this t'3 distance_delta (fp + 0) target_pos (fp + 8) (fp + 24) (fp + 32)
  let t'4 ← PMem.ldF32 (fp + 24)
  let t'5 ← PMem.ldF32 (fp + 32)
  let t'6 ← PMem.ldF32 (fp + 32)
  let t'7 ← constrain_value_line'float t'4 (speed_cms - (t'5 * dt)) (speed_cms + (t'6 * dt)) (Int32.toUInt32 ((120 : Int32)))
  speed_cms := t'7
  Vector3'float.operator_ (fp + 8) (fp + 40) speed_cms
  let t'8 := (fp + 40)
  discard <| PMem.memcpy target_vel t'8 12
  discard <| pure (target_vel)
  let t'9 := (this + 168)
  let t'10 ← PMem.ldF32 t'9
  let t'11 ← PMem.ldF32 (fp + 0)
  let t'12 := (t'10 + t'11)
  PMem.stF32 t'9 t'12
  let t'13 ← PMem.ldF32 (this + 168)
  if (decide (t'13 ≥ (Binary32.ofBits 0x3f800000 /- 1 -/))) then
    let t'14 := (Binary32.ofBits 0x3f800000 /- 1 -/)
    PMem.stF32 (this + 168) t'14
    PMem.stB (this + 200) true
  return ()

def SplineCurve.advance_target_along_track (this : UInt64) (dt : Binary32) (target_pos : UInt64) (target_vel : UInt64) : PMem.M Unit := do
  let fp ← PMem.enter 52
  let r ← SplineCurve.advance_target_along_track.body fp this dt target_pos target_vel
  PMem.leave fp
  return r

/-- C++ `SplineCurve::reached_destination : bool () const`, `SplineCurve.h:24-?`. -/
def SplineCurve.reached_destination (this : UInt64) : PMem.M Bool := do
  let t'1 ← PMem.ldB (this + 200)
  return t'1

/-- C++ `shape_vel_accel_xy : void (const Vector2f &, const Vector2f &, const Vector2f &, Vector2f &, float, float, float, bool)`, `control.cpp:230-259`. -/
def shape_vel_accel_xy.body (fp : UInt64) (vel_desired : UInt64) (accel_desired : UInt64) (vel : UInt64) (accel : UInt64) (accel_max : Binary32) (jerk_max : Binary32) (dt : Binary32) (limit_total_accel : Bool) : PMem.M Unit := do
  let mut accel_max := accel_max
  let mut jerk_max := jerk_max
  let mut dt := dt
  let mut limit_total_accel := limit_total_accel
  let t'1 ← is_positive'float accel_max
  let mut sc'3 := !t'1
  if !sc'3 then
    let t'2 ← is_positive'float jerk_max
    sc'3 := !t'2
  if sc'3 then
    return ()
  let mut KPa : Binary32 := (jerk_max / accel_max)
  Vector2'float.operator_ vel_desired (fp + 8) vel
  let t'4 := (fp + 8)
  Vector2'float.Vector2'3 (fp + 0) t'4
  sqrt_controller'2 (fp + 24) (fp + 0) KPa jerk_max dt
  let t'5 := (fp + 24)
  Vector2'float.Vector2'3 (fp + 16) t'5
  let t'6 ← limit_accel_corner_xy vel (fp + 16) accel_max
  discard <| pure (t'6)
  let t'7 ← Vector2'float.operator__ (fp + 16) accel_desired
  discard <| pure (t'7)
  if limit_total_accel then
    let t'8 ← Vector2'float.limit_length (fp + 16) accel_max
    discard <| pure (t'8)
  shape_accel_xy (fp + 16) accel jerk_max dt
  return ()

def shape_vel_accel_xy (vel_desired : UInt64) (accel_desired : UInt64) (vel : UInt64) (accel : UInt64) (accel_max : Binary32) (jerk_max : Binary32) (dt : Binary32) (limit_total_accel : Bool) : PMem.M Unit := do
  let fp ← PMem.enter 32
  let r ← shape_vel_accel_xy.body fp vel_desired accel_desired vel accel accel_max jerk_max dt limit_total_accel
  PMem.leave fp
  return r

/-- C++ `Vector2<double>::operator* : Vector2<double> (const double) const`, `vector2.cpp:109-112`. -/
def Vector2'double.operator_'3.body (fp : UInt64) (this : UInt64) (sret : UInt64) (num : Binary64) : PMem.M Unit := do
  let mut num := num
  let t'1 ← PMem.ldF64 this
  let t'2 ← PMem.ldF64 (this + 8)
  Vector2'double.Vector2'2 (fp + 0) (t'1 * num) (t'2 * num)
  Vector2'double.Vector2 sret (fp + 0)
  return ()

def Vector2'double.operator_'3 (this : UInt64) (sret : UInt64) (num : Binary64) : PMem.M Unit := do
  let fp ← PMem.enter 16
  let r ← Vector2'double.operator_'3.body fp this sret num
  PMem.leave fp
  return r

/-- C++ `MIN : auto (const float &, const double &) -> decltype(one < two ? one : two)`, `AP_Math.h:300-303`. -/
def MIN'float_double (one : UInt64) (two : UInt64) : PMem.M Binary64 := do
  let t'1 ← PMem.ldF32 one
  let t'2 ← PMem.ldF64 two
  let mut c'3 : Binary64 := default
  if (decide ((Binary32.toBinary64 (t'1)) < t'2)) then
    let t'4 ← PMem.ldF32 one
    c'3 := Binary32.toBinary64 (t'4)
  else
    let t'5 ← PMem.ldF64 two
    c'3 := t'5
  return c'3

/-- C++ `QuaternionT<float>::is_zero : bool () const`, `<scratch space>:679-681`. -/
def QuaternionT'float.is_zero (this : UInt64) : PMem.M Bool := do
  let t'1 ← PMem.ldF32 this
  let t'2 ← _root_.Vehicle_lib.is_zero t'1
  let mut sc'5 := t'2
  if sc'5 then
    let t'3 ← PMem.ldF32 (this + 4)
    let t'4 ← _root_.Vehicle_lib.is_zero t'3
    sc'5 := t'4
  let mut sc'8 := sc'5
  if sc'8 then
    let t'6 ← PMem.ldF32 (this + 8)
    let t'7 ← _root_.Vehicle_lib.is_zero t'6
    sc'8 := t'7
  let mut sc'11 := sc'8
  if sc'11 then
    let t'9 ← PMem.ldF32 (this + 12)
    let t'10 ← _root_.Vehicle_lib.is_zero t'9
    sc'11 := t'10
  return sc'11

/-- C++ `MIN : auto (const unsigned char &, const unsigned char &) -> decltype(one < two ? one : two)`, `AP_Math.h:300-303`. -/
def MIN'unsigned_char_unsigned_char (one : UInt64) (two : UInt64) : PMem.M UInt64 := do
  let t'1 ← PMem.ldU8 one
  let t'2 ← PMem.ldU8 two
  let mut c'3 : UInt64 := 0
  if (decide ((UInt32.toInt32 (UInt8.toUInt32 (t'1))) < (UInt32.toInt32 (UInt8.toUInt32 (t'2))))) then
    c'3 := one
  else
    c'3 := two
  return c'3

/-- C++ `MAX : auto (const unsigned int &, const unsigned int &) -> decltype(one > two ? one : two)`, `AP_Math.h:307-310`. -/
def MAX'unsigned_int_unsigned_int (one : UInt64) (two : UInt64) : PMem.M UInt64 := do
  let t'1 ← PMem.ldU32 one
  let t'2 ← PMem.ldU32 two
  let mut c'3 : UInt64 := 0
  if (decide (t'1 > t'2)) then
    c'3 := one
  else
    c'3 := two
  return c'3

end Vehicle_lib
