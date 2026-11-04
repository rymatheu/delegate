/-!
# `AP_Math/ftype.h`, numeric types

Mirrors `libraries/AP_Math/ftype.h:58-74` (`is_zero`) and `control.h:7-17` (`postype_t`,
`topostype`) at ArduPilot 802db19de1, SITL configuration (`HAL_WITH_POSTYPE_DOUBLE = 1`,
`HAL_WITH_EKF_DOUBLE = 1`).

Naming: `ftype` is `Float32` for every control quantity (PORT.md). ArduPilot's own `ftype` typedef
is `double` under `HAL_WITH_EKF_DOUBLE` (`ftype.h:14-15`); it only affects the EKF and the
`sq`/`norm` templates on `double` arguments, which `vector2.lean` and `vector3.lean` reproduce for
`Vector2p`/`Vector3p` explicitly. Overloads on `double` carry the suffix `_d`.

Left out: the `sinF`/`cosF`/... macros (`ftype.h:14-50`). With `-fsingle-precision-constant` every
call site in the ported code passes a `float`, and the C++ overloads of `sin`, `cos`, `atan2` and
`sqrt` brought into the global namespace by `<math.h>` then resolve to `sinf`, `cosf`, `atan2f` and
`sqrtf` (checked with g++ 15 and Apple clang 17, see `quaternion.lean`).
-/

/-- `float`. -/
abbrev ftype := Float32

/-- `postype_t` (`control.h:8`): `double` in the SITL build. -/
abbrev postype := Float

namespace AP_Math

/-- `(float)x` for a `postype_t` (the C++ `float(x)` in `tofloat()`). -/
def tofloat (x : postype) : ftype := x.toFloat32

/-- `(double)x` for a `float` (the implicit widening, and `todouble()`). -/
def topostype (x : ftype) : postype := x.toFloat

/-- `FLT_EPSILON` = 2^-23 (`float.h`), bit pattern `0x34000000`. -/
def FLT_EPSILON : Float32 := Float32.ofBits 0x34000000

/-- `(double)FLT_EPSILON`, bit pattern `0x3E80000000000000`. -/
def FLT_EPSILON_d : Float := Float.ofBits 0x3E80000000000000

/-- `is_zero(float)` (`ftype.h:61-63`). -/
def is_zero (x : Float32) : Bool := x.abs < FLT_EPSILON

/-- `is_zero(double)` with `AP_MATH_ALLOW_DOUBLE_FUNCTIONS` (true on SITL, `ftype.h:68-74`). -/
def is_zero_d (x : Float) : Bool := x.abs < FLT_EPSILON_d

end AP_Math
