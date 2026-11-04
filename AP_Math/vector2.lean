import AP_Math.AP_Math

/-!
# `AP_Math/vector2.h` and `vector2.cpp`

`Vector2f` is `Vector2<float>`; `Vector2p` is `Vector2<postype_t>` = `Vector2d` on SITL
(`control.h:9`). Mirrors, at ArduPilot 802db19de1, `vector2.h:44-183` (struct, inline methods),
`:294-301` (`is_zero` specializations) and `vector2.cpp:23-165` (arithmetic, `length`,
`limit_length`, dot `*`, cross `%`, `is_nan`, `is_inf`, `angle`; the overload `angle(v2)` is `angle_between`), `:266-278` (`normalize`,
`normalized`).

Conventions. Methods that mutate `*this` return the new value; `limit_length` returns the new
vector and the C++ `bool`. `Vector2f.is_zero` is the specialized `::is_zero(x) && ::is_zero(y)`
(magnitudes below `FLT_EPSILON`), not the generic `x == 0 && y == 0`. `Vector2p.length` is the
`norm<double,double>` template, `sqrt(sq(x) + sq(y))` in `double`. Notation: `+ - *` (by a
scalar) `/` are the C++ operators, `a * b` between vectors is the dot product and `a % b` the cross
product; write scalar literals next to a vector with an ascription, `v * (0.5 : Float32)`.

Left out: `==`/`!=`, `reflect`, `project`, `projected`, `offset_bearing`, `rotate`,
`perpendicular`, `closest_point`, the `closest_distance_*` family, `segment_intersection`,
`circle_segment_intersection`, `point_on_segment`, `operator[]`; and for `Vector2p`, `angle` and
`is_inf`. None is called by the cascade.
-/

/-- `Vector2<float>`; the default is the zero vector (trivial constructor). -/
structure Vector2f where
  x : Float32 := 0
  y : Float32 := 0
deriving Repr, Inhabited

/-- `Vector2<double>` (= `Vector2p` on SITL). -/
structure Vector2p where
  x : Float := 0
  y : Float := 0
deriving Repr, Inhabited

namespace Vector2f

/-- Unary `operator-`. -/
def neg (v : Vector2f) : Vector2f := ⟨-v.x, -v.y⟩
/-- `operator+`. -/
def add (a v : Vector2f) : Vector2f := ⟨a.x + v.x, a.y + v.y⟩
/-- `operator-`. -/
def sub (a v : Vector2f) : Vector2f := ⟨a.x - v.x, a.y - v.y⟩
/-- `operator*(const T num)`. -/
def mul (a : Vector2f) (num : Float32) : Vector2f := ⟨a.x * num, a.y * num⟩
/-- `operator/(const T num)`. -/
def div (a : Vector2f) (num : Float32) : Vector2f := ⟨a.x / num, a.y / num⟩
/-- Dot product `operator*(const Vector2<T>&)`: `x*v.x + y*v.y`. -/
def dot (a v : Vector2f) : Float32 := a.x * v.x + a.y * v.y
/-- Cross product `operator%`: `x*v.y - y*v.x`. -/
def cross (a v : Vector2f) : Float32 := a.x * v.y - a.y * v.x

instance : Neg Vector2f := ⟨neg⟩
instance : Add Vector2f := ⟨add⟩
instance : Sub Vector2f := ⟨sub⟩
instance : HMul Vector2f Float32 Vector2f := ⟨mul⟩
instance : HDiv Vector2f Float32 Vector2f := ⟨div⟩
instance : HMul Vector2f Vector2f Float32 := ⟨dot⟩
instance : HMod Vector2f Vector2f Float32 := ⟨cross⟩

/-- `zero()`. -/
def zero (_v : Vector2f) : Vector2f := ⟨0, 0⟩
/-- `length_squared()`: `x*x + y*y`. -/
def length_squared (v : Vector2f) : Float32 := v.x * v.x + v.y * v.y
/-- `length()`: `norm(x, y)`. -/
def length (v : Vector2f) : Float32 := AP_Math.norm v.x v.y

/-- `limit_length(max_length)`: the new vector and whether it was limited. -/
def limit_length (v : Vector2f) (max_length : Float32) : Vector2f × Bool :=
  let len := v.length
  if len > max_length && AP_Math.is_positive len then
    (⟨v.x * (max_length / len), v.y * (max_length / len)⟩, true)
  else (v, false)

/-- `normalize()`: `*this /= length()`. -/
def normalize (v : Vector2f) : Vector2f := v / v.length
/-- `normalized()`: `*this / length()`. -/
def normalized (v : Vector2f) : Vector2f := v / v.length
/-- `is_nan()`. -/
def is_nan (v : Vector2f) : Bool := v.x.isNaN || v.y.isNaN
/-- `is_inf()`. -/
def is_inf (v : Vector2f) : Bool := v.x.isInf || v.y.isInf
/-- `is_zero()`, `Vector2<float>` specialization (`vector2.h:295-297`). -/
def is_zero (v : Vector2f) : Bool := AP_Math.is_zero v.x && AP_Math.is_zero v.y

/-- `angle(v2)` (`vector2.cpp:144-159`); `acosF(float)` resolves to `acosf`. -/
def angle_between (v v2 : Vector2f) : Float32 :=
  let len := v.length * v2.length
  if len ≤ 0 then 0.0
  else
    let cosv := (v * v2) / len
    if cosv ≥ 1 then 0.0
    else if cosv ≤ -1 then AP_Math.M_PI
    else cosv.acos

/-- `angle()` (`vector2.cpp:161-165`): `atan2F(y, x)`, which resolves to `atan2f`. -/
def angle (v : Vector2f) : Float32 := Float32.atan2 v.y v.x

/-- `tofloat()`. -/
def tofloat (v : Vector2f) : Vector2f := v
/-- `todouble()`, i.e. `topostype()` on SITL. -/
def topostype (v : Vector2f) : Vector2p := ⟨AP_Math.topostype v.x, AP_Math.topostype v.y⟩

end Vector2f

namespace Vector2p

/-- Unary `operator-`. -/
def neg (v : Vector2p) : Vector2p := ⟨-v.x, -v.y⟩
/-- `operator+`. -/
def add (a v : Vector2p) : Vector2p := ⟨a.x + v.x, a.y + v.y⟩
/-- `operator-`. -/
def sub (a v : Vector2p) : Vector2p := ⟨a.x - v.x, a.y - v.y⟩
/-- `operator*(const T num)`. -/
def mul (a : Vector2p) (num : Float) : Vector2p := ⟨a.x * num, a.y * num⟩
/-- `operator/(const T num)`. -/
def div (a : Vector2p) (num : Float) : Vector2p := ⟨a.x / num, a.y / num⟩
/-- Dot product `operator*`. -/
def dot (a v : Vector2p) : Float := a.x * v.x + a.y * v.y
/-- Cross product `operator%`. -/
def cross (a v : Vector2p) : Float := a.x * v.y - a.y * v.x

instance : Neg Vector2p := ⟨neg⟩
instance : Add Vector2p := ⟨add⟩
instance : Sub Vector2p := ⟨sub⟩
instance : HMul Vector2p Float Vector2p := ⟨mul⟩
instance : HDiv Vector2p Float Vector2p := ⟨div⟩
instance : HMul Vector2p Vector2p Float := ⟨dot⟩
instance : HMod Vector2p Vector2p Float := ⟨cross⟩

/-- `zero()`. -/
def zero (_v : Vector2p) : Vector2p := ⟨0, 0⟩
/-- `length_squared()`. -/
def length_squared (v : Vector2p) : Float := v.x * v.x + v.y * v.y
/-- `length()`: `norm<double,double>(x, y)` = `sqrt(sq(x) + sq(y))` in `double`. -/
def length (v : Vector2p) : Float := (v.x * v.x + v.y * v.y).sqrt

/-- `limit_length(max_length)`; uses `is_positive(double)`. -/
def limit_length (v : Vector2p) (max_length : Float) : Vector2p × Bool :=
  let len := v.length
  if len > max_length && AP_Math.is_positive_d len then
    (⟨v.x * (max_length / len), v.y * (max_length / len)⟩, true)
  else (v, false)

/-- `normalize()`. -/
def normalize (v : Vector2p) : Vector2p := v / v.length
/-- `normalized()`. -/
def normalized (v : Vector2p) : Vector2p := v / v.length
/-- `is_nan()`. -/
def is_nan (v : Vector2p) : Bool := v.x.isNaN || v.y.isNaN
/-- `is_zero()`, `Vector2<double>` specialization (`vector2.h:299-301`). -/
def is_zero (v : Vector2p) : Bool := AP_Math.is_zero_d v.x && AP_Math.is_zero_d v.y

/-- `tofloat()`: `Vector2<float>{float(x), float(y)}`. -/
def tofloat (v : Vector2p) : Vector2f := ⟨AP_Math.tofloat v.x, AP_Math.tofloat v.y⟩
/-- `todouble()`. -/
def topostype (v : Vector2p) : Vector2p := v

end Vector2p
