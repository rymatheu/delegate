import AP_Math.vector2

/-!
# `AP_Math/vector3.h` and `vector3.cpp`

`Vector3f` is `Vector3<float>`; `Vector3p` is `Vector3<postype_t>` = `Vector3d` on SITL
(`control.h:10`). Mirrors, at ArduPilot 802db19de1, `vector3.h:71-94` (constructors),
`:155-158` (`dot`), `:169-172` (`cross`), `:202-207` (`xy`), `:210-238` (`length_squared`,
`normalize`, `zero`, `normalized`), `:277-282` (`tofloat`, `todouble`), `:320-327`
(`is_zero` specializations), and `vector3.cpp:308-436` (cross `%`, dot `*`, `length`,
`limit_length_xy`, arithmetic, `is_nan`, `is_inf`, `angle`).

Conventions. Methods that mutate `*this` return the new value; `limit_length_xy` also returns the
C++ `bool`. `xy()` returns a reference in C++; here `xy` reads it and `set_xy` writes it.
`Vector3f.length` is `norm(float, float, float)` = `sqrtf((sq(x) + sq(y)) + sq(z))`, while
`Vector3p.length` is the variadic `norm<double,...>` template, whose `sq(x, y, z)` expands to
`sq(x) + (sq(y) + sq(z))` (`AP_Math.h:275-289`): the association differs and is kept. The
overload `angle(v2)` is `angle_between`; the constructor from a `Vector2` and `z` is `of_xy`.

Left out: `==`/`!=`, `*=` by a vector, `operator[]`, `row_times_mat`, `mul_rowcol`, `scale`,
`rotate`, `rotate_inverse`, `rotate_xy`, `reflect`, `project`, `projected`, `distance_squared`,
`distance_to_segment`, `offset_bearing`, `rfu_to_frd`, `perpendicular`, the closest-point and
segment functions; and for `Vector3p`, `cross`, `angle`, `is_inf`, `limit_length_xy`. None is called
by the cascade.
-/

/-- `Vector3<float>`; the default is the zero vector. -/
structure Vector3f where
  x : Float32 := 0
  y : Float32 := 0
  z : Float32 := 0
deriving Repr, Inhabited

/-- `Vector3<double>` (= `Vector3p` on SITL). -/
structure Vector3p where
  x : Float := 0
  y : Float := 0
  z : Float := 0
deriving Repr, Inhabited

namespace Vector3f

/-- `Vector3(const Vector2<T> &v0, const T z0)`. -/
def of_xy (v0 : Vector2f) (z0 : Float32) : Vector3f := ⟨v0.x, v0.y, z0⟩

/-- Unary `operator-`. -/
def neg (v : Vector3f) : Vector3f := ⟨-v.x, -v.y, -v.z⟩
/-- `operator+`. -/
def add (a v : Vector3f) : Vector3f := ⟨a.x + v.x, a.y + v.y, a.z + v.z⟩
/-- `operator-`. -/
def sub (a v : Vector3f) : Vector3f := ⟨a.x - v.x, a.y - v.y, a.z - v.z⟩
/-- `operator*(const T num)`. -/
def mul (a : Vector3f) (num : Float32) : Vector3f := ⟨a.x * num, a.y * num, a.z * num⟩
/-- `operator/(const T num)`. -/
def div (a : Vector3f) (num : Float32) : Vector3f := ⟨a.x / num, a.y / num, a.z / num⟩
/-- Dot product `operator*` (`vector3.cpp:317-321`): `x*v.x + y*v.y + z*v.z`. -/
def dot (a v : Vector3f) : Float32 := a.x * v.x + a.y * v.y + a.z * v.z
/-- Cross product `operator%` (`vector3.cpp:308-314`). -/
def cross (a v : Vector3f) : Vector3f :=
  ⟨a.y * v.z - a.z * v.y, a.z * v.x - a.x * v.z, a.x * v.y - a.y * v.x⟩

instance : Neg Vector3f := ⟨neg⟩
instance : Add Vector3f := ⟨add⟩
instance : Sub Vector3f := ⟨sub⟩
instance : HMul Vector3f Float32 Vector3f := ⟨mul⟩
instance : HDiv Vector3f Float32 Vector3f := ⟨div⟩
instance : HMul Vector3f Vector3f Float32 := ⟨dot⟩
instance : HMod Vector3f Vector3f Vector3f := ⟨cross⟩

/-- `xy()` read. -/
def xy (v : Vector3f) : Vector2f := ⟨v.x, v.y⟩
/-- `xy() = w`. -/
def set_xy (v : Vector3f) (w : Vector2f) : Vector3f := ⟨w.x, w.y, v.z⟩
/-- `zero()`. -/
def zero (_v : Vector3f) : Vector3f := ⟨0, 0, 0⟩
/-- `length_squared()`: `*this * *this`. -/
def length_squared (v : Vector3f) : Float32 := v * v
/-- `length()`: `norm(x, y, z)`. -/
def length (v : Vector3f) : Float32 := AP_Math.norm3 v.x v.y v.z

/-- `limit_length_xy(max_length)` (`vector3.cpp:330-340`). -/
def limit_length_xy (v : Vector3f) (max_length : Float32) : Vector3f × Bool :=
  let length_xy := AP_Math.norm v.x v.y
  if length_xy > max_length && AP_Math.is_positive length_xy then
    (⟨v.x * (max_length / length_xy), v.y * (max_length / length_xy), v.z⟩, true)
  else (v, false)

/-- `normalize()`: `*this /= length()`. -/
def normalize (v : Vector3f) : Vector3f := v / v.length
/-- `normalized()`. -/
def normalized (v : Vector3f) : Vector3f := v / v.length
/-- `is_nan()`. -/
def is_nan (v : Vector3f) : Bool := v.x.isNaN || v.y.isNaN || v.z.isNaN
/-- `is_inf()`. -/
def is_inf (v : Vector3f) : Bool := v.x.isInf || v.y.isInf || v.z.isInf
/-- `is_zero()`, `Vector3<float>` specialization (`vector3.h:321-323`). -/
def is_zero (v : Vector3f) : Bool :=
  AP_Math.is_zero v.x && AP_Math.is_zero v.y && AP_Math.is_zero v.z

/-- `angle(v2)` (`vector3.cpp:424-436`); `acosF(float)` resolves to `acosf`. -/
def angle_between (v v2 : Vector3f) : Float32 :=
  let len := v.length * v2.length
  if len ≤ 0 then 0.0
  else
    let cosv := (v * v2) / len
    if cosv ≥ 1 || cosv ≤ -1 then 0.0
    else cosv.acos

/-- `tofloat()`. -/
def tofloat (v : Vector3f) : Vector3f := v
/-- `todouble()`, i.e. `topostype()` on SITL. -/
def topostype (v : Vector3f) : Vector3p :=
  ⟨AP_Math.topostype v.x, AP_Math.topostype v.y, AP_Math.topostype v.z⟩

end Vector3f

namespace Vector3p

/-- `Vector3(const Vector2<T> &v0, const T z0)`. -/
def of_xy (v0 : Vector2p) (z0 : Float) : Vector3p := ⟨v0.x, v0.y, z0⟩

/-- Unary `operator-`. -/
def neg (v : Vector3p) : Vector3p := ⟨-v.x, -v.y, -v.z⟩
/-- `operator+`. -/
def add (a v : Vector3p) : Vector3p := ⟨a.x + v.x, a.y + v.y, a.z + v.z⟩
/-- `operator-`. -/
def sub (a v : Vector3p) : Vector3p := ⟨a.x - v.x, a.y - v.y, a.z - v.z⟩
/-- `operator*(const T num)`. -/
def mul (a : Vector3p) (num : Float) : Vector3p := ⟨a.x * num, a.y * num, a.z * num⟩
/-- `operator/(const T num)`. -/
def div (a : Vector3p) (num : Float) : Vector3p := ⟨a.x / num, a.y / num, a.z / num⟩
/-- Dot product `operator*`. -/
def dot (a v : Vector3p) : Float := a.x * v.x + a.y * v.y + a.z * v.z

instance : Neg Vector3p := ⟨neg⟩
instance : Add Vector3p := ⟨add⟩
instance : Sub Vector3p := ⟨sub⟩
instance : HMul Vector3p Float Vector3p := ⟨mul⟩
instance : HDiv Vector3p Float Vector3p := ⟨div⟩
instance : HMul Vector3p Vector3p Float := ⟨dot⟩

/-- `xy()` read. -/
def xy (v : Vector3p) : Vector2p := ⟨v.x, v.y⟩
/-- `xy() = w`. -/
def set_xy (v : Vector3p) (w : Vector2p) : Vector3p := ⟨w.x, w.y, v.z⟩
/-- `zero()`. -/
def zero (_v : Vector3p) : Vector3p := ⟨0, 0, 0⟩
/-- `length_squared()`: `*this * *this`. -/
def length_squared (v : Vector3p) : Float := v * v
/-- `length()`: `norm<double,double,double>`, i.e. `sqrt(sq(x) + (sq(y) + sq(z)))`. -/
def length (v : Vector3p) : Float := (v.x * v.x + (v.y * v.y + v.z * v.z)).sqrt
/-- `normalize()`. -/
def normalize (v : Vector3p) : Vector3p := v / v.length
/-- `normalized()`. -/
def normalized (v : Vector3p) : Vector3p := v / v.length
/-- `is_nan()`. -/
def is_nan (v : Vector3p) : Bool := v.x.isNaN || v.y.isNaN || v.z.isNaN
/-- `is_zero()`, `Vector3<double>` specialization (`vector3.h:325-327`). -/
def is_zero (v : Vector3p) : Bool :=
  AP_Math.is_zero_d v.x && AP_Math.is_zero_d v.y && AP_Math.is_zero_d v.z

/-- `tofloat()`. -/
def tofloat (v : Vector3p) : Vector3f :=
  ⟨AP_Math.tofloat v.x, AP_Math.tofloat v.y, AP_Math.tofloat v.z⟩
/-- `todouble()`. -/
def topostype (v : Vector3p) : Vector3p := v

end Vector3p
