/-!
# `AC_PID.Compat`: local stand-ins for the `AP_Math` helpers that `AC_PID` uses

ArduPilot commit 802db19de1, SITL configuration (`-cl-single-precision-constant`, so every
literal below is a `float`). The `AP_Math/` port is written in parallel; until it lands,
`AC_PID` uses these minimal versions. Each one mirrors the C++ cited next to it.

-- TODO: replace by AP_Math.* (every definition in this file), then delete this file.

Mirrors:
- `libraries/AP_Math/ftype.h:61-63` (`is_zero(float)`), `AP_Math.h:64-80` (`is_positive`,
  `is_negative` for `float`), `AP_Math.h:261-269` (`sq(float)`), `AP_Math.h:288-290`
  (`norm(float, float)`), `AP_Math.h:298-310` (`MIN`, `MAX`).
- `AP_Math.cpp:71-81` (`safe_sqrt`), `:282-304` (`constrain_value_line`, behind
  `constrain_float`, `AP_Math.h:178`), `:418-432` (`calc_lowpass_alpha_dt`).
- `AP_Math/control.cpp:575-614` (`sqrt_controller`, scalar), `:616-628` (vector form),
  `:630-659` (`inv_sqrt_controller`).
- `AP_Math/vector2.h`/`vector2.cpp`: the operators, `length` (:29-33), `limit_length`
  (:35-46), dot product (:48-53), `is_nan`/`is_inf` (:83-93), `tofloat` (`vector2.h:178-180`),
  `topostype` (`control.h:11`, `todouble` when `HAL_WITH_POSTYPE_DOUBLE`).
- `AP_Math/definitions.h:11`, `:20` (`M_PI`, `M_2PI`).

Left out: the `INTERNAL_ERROR` reports in `constrain_value_line` and
`calc_lowpass_alpha_dt` (no effect on the returned value); every other `AP_Math` function.
-/

namespace AC_PID.Compat

/-- `float`. -/
abbrev ftype := Float32
/-- `postype_t`, `double` on SITL (`HAL_WITH_POSTYPE_DOUBLE`). -/
abbrev postype := Float

/-- `(float)x` on a `postype_t`: round to nearest. -/
@[inline] def tofloat (x : postype) : ftype := x.toFloat32
/-- `(double)x` on a `float`: exact widening. -/
@[inline] def topostype (x : ftype) : postype := x.toFloat

/-- `FLT_EPSILON = 2^-23` (`float.h`). -/
def FLT_EPSILON : ftype := Float32.ofBits 0x34000000

/-- `M_PI` (`definitions.h:11`): the literal rounded to `float`, `0x40490FDB`. -/
def M_PI : ftype := Float32.ofBits 0x40490FDB
/-- `M_2PI = M_PI * 2` (`definitions.h:20`), a `float` product. -/
def M_2PI : ftype := M_PI * 2

@[inline] def fabsf (x : ftype) : ftype := x.abs
@[inline] def sqrtf (x : ftype) : ftype := x.sqrt

/-- `is_zero(float)`, `ftype.h:61-63`: `fabsf(x) < FLT_EPSILON`. -/
def is_zero (x : ftype) : Bool := fabsf x < FLT_EPSILON
/-- `is_positive`, `AP_Math.h:64-69`: `x >= FLT_EPSILON`. -/
def is_positive (x : ftype) : Bool := x ≥ FLT_EPSILON
/-- `is_negative`, `AP_Math.h:75-80`: `x <= (-1.0 * FLT_EPSILON)`. -/
def is_negative (x : ftype) : Bool := x ≤ (-1.0 : ftype) * FLT_EPSILON

/-- `sq(float)`, `AP_Math.h:266-269`. -/
@[inline] def sq (v : ftype) : ftype := v * v

/-- `MIN`, `AP_Math.h:298-303`: `one < two ? one : two`. -/
@[inline] def MIN (one two : ftype) : ftype := if one < two then one else two
/-- `MAX`, `AP_Math.h:305-310`: `one > two ? one : two`. -/
@[inline] def MAX (one two : ftype) : ftype := if one > two then one else two

/-- `constrain_float(amt, low, high)`, `AP_Math.cpp:282-304`. NaN goes to the midpoint. -/
def constrain_float (amt low high : ftype) : ftype :=
  if amt.isNaN then (low + high) / 2
  else if amt < low then low
  else if amt > high then high
  else amt

/-- `safe_sqrt(float)`, `AP_Math.cpp:71-81`: `isgreaterequal(val, 0) ? sqrtf(val) : 0`. -/
def safe_sqrt (val : ftype) : ftype := if val ≥ 0 then sqrtf val else 0

/-- `calc_lowpass_alpha_dt`, `AP_Math.cpp:418-432`. -/
def calc_lowpass_alpha_dt (dt cutoff_freq : ftype) : ftype :=
  if is_negative dt || is_negative cutoff_freq then 1.0
  else if is_zero cutoff_freq then 1.0
  else if is_zero dt then 0.0
  else
    let rc : ftype := 1.0 / (M_2PI * cutoff_freq)
    dt / (dt + rc)

/-- `sqrt_controller(float error, float p, float second_ord_lim, float dt)`,
`control.cpp:575-614`. -/
def sqrt_controller (error p second_ord_lim dt : ftype) : ftype :=
  let correction_rate : ftype :=
    if is_negative second_ord_lim || is_zero second_ord_lim then
      error * p
    else if is_zero p then
      if is_positive error then safe_sqrt (2.0 * second_ord_lim * error)
      else if is_negative error then -safe_sqrt (2.0 * second_ord_lim * (-error))
      else 0.0
    else
      let linear_dist : ftype := second_ord_lim / sq p
      if error > linear_dist then
        safe_sqrt (2.0 * second_ord_lim * (error - (linear_dist / 2.0)))
      else if error < -linear_dist then
        -safe_sqrt (2.0 * second_ord_lim * (-error - (linear_dist / 2.0)))
      else
        error * p
  if is_positive dt then
    constrain_float correction_rate (-fabsf error / dt) (fabsf error / dt)
  else
    correction_rate

/-- `inv_sqrt_controller`, `control.cpp:630-659`. -/
def inv_sqrt_controller (output p D_max : ftype) : ftype :=
  if is_positive D_max && is_zero p then
    (output * output) / (2.0 * D_max)
  else if (is_negative D_max || is_zero D_max) && !is_zero p then
    output / p
  else if (is_negative D_max || is_zero D_max) && is_zero p then
    0.0
  else
    let linear_velocity : ftype := D_max / p
    if fabsf output < linear_velocity then
      output / p
    else
      let linear_dist : ftype := D_max / sq p
      let stopping_dist : ftype := (linear_dist * 0.5) + sq output / (2.0 * D_max)
      if is_positive output then stopping_dist else -stopping_dist

/-- `Vector2<T>` (`vector2.h`). -/
structure Vector2 (T : Type) where
  x : T
  y : T
deriving Repr, Inhabited

/-- `Vector2f = Vector2<float>`. -/
abbrev Vector2f := Vector2 Float32
/-- `Vector2p = Vector2<postype_t>`. -/
abbrev Vector2p := Vector2 Float

/-- `Vector3f = Vector3<float>`, only the components (used for the `AC_PID_2D` overload). -/
structure Vector3f where
  x : Float32
  y : Float32
  z : Float32
deriving Repr, Inhabited

namespace Vector2

variable {T : Type}

/-- `Vector2<T>(x+v.x, y+v.y)`, `vector2.cpp:120-124`. -/
instance [Add T] : Add (Vector2 T) := ⟨fun a b => ⟨a.x + b.x, a.y + b.y⟩⟩
/-- `Vector2<T>(x-v.x, y-v.y)`, `vector2.cpp:114-118`. -/
instance [Sub T] : Sub (Vector2 T) := ⟨fun a b => ⟨a.x - b.x, a.y - b.y⟩⟩
/-- `Vector2<T>(-x, -y)`, `vector2.cpp:126-130`. -/
instance [Neg T] : Neg (Vector2 T) := ⟨fun a => ⟨-a.x, -a.y⟩⟩
/-- `Vector2<T>(x*num, y*num)`, `vector2.cpp:108-112`. -/
instance [Mul T] : HMul (Vector2 T) T (Vector2 T) := ⟨fun a n => ⟨a.x * n, a.y * n⟩⟩
/-- `Vector2<T>(x/num, y/num)`, `vector2.cpp:102-106`. -/
instance [Div T] : HDiv (Vector2 T) T (Vector2 T) := ⟨fun a n => ⟨a.x / n, a.y / n⟩⟩

/-- `Vector2<T>{}` and `zero()`. -/
def zero [OfNat T 0] : Vector2 T := ⟨0, 0⟩

/-- Dot product, C++ `operator *(const Vector2<T>&)`, `vector2.cpp:48-53`: `x*v.x + y*v.y`. -/
def dot [Add T] [Mul T] (a b : Vector2 T) : T := a.x * b.x + a.y * b.y

/-- `is_nan()`, `vector2.cpp:83-87`. -/
def is_nan (v : Vector2f) : Bool := v.x.isNaN || v.y.isNaN
/-- `is_inf()`, `vector2.cpp:89-93`. -/
def is_inf (v : Vector2f) : Bool := v.x.isInf || v.y.isInf

/-- `length()` for `float`, `vector2.cpp:29-33` → `norm(x, y)` (`AP_Math.h:288-290`). -/
def length (v : Vector2f) : Float32 := sqrtf (sq v.x + sq v.y)

/-- `limit_length(max_length)`, `vector2.cpp:35-46`. Returns the new vector and the C++
return value. -/
def limit_length (v : Vector2f) (max_length : Float32) : Vector2f × Bool :=
  let len := v.length
  if len > max_length && is_positive len then
    (⟨v.x * (max_length / len), v.y * (max_length / len)⟩, true)
  else
    (v, false)

/-- `tofloat()`, `vector2.h:178-180`. -/
def tofloat (v : Vector2p) : Vector2f := ⟨Compat.tofloat v.x, Compat.tofloat v.y⟩
/-- `topostype()` = `todouble()` on SITL (`control.h:11`). -/
def topostype (v : Vector2f) : Vector2p := ⟨Compat.topostype v.x, Compat.topostype v.y⟩

end Vector2

/-- `sqrt_controller(const Vector2f& error, ...)`, `control.cpp:616-628`. -/
def sqrt_controller_vec (error : Vector2f) (p second_ord_lim dt : ftype) : Vector2f :=
  let error_length := error.length
  if !is_positive error_length then
    Vector2.zero
  else
    let correction_length := sqrt_controller error_length p second_ord_lim dt
    error * (correction_length / error_length)

end AC_PID.Compat
