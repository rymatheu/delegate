import AP_Math.definitions

/-!
# `AP_Math/AP_Math.h` and `AP_Math.cpp`, scalar helpers

Mirrors, at ArduPilot 802db19de1:
- `AP_Math.h:51-94` (`is_positive`, `is_negative`, float template and `double` overloads),
  `:226-310` (`radians`, `cd_to_rad`, `rad_to_cd`, `degrees`, `sq`, `norm`, `MIN`, `MAX`);
- `AP_Math.cpp:24-41` (`is_equal`, float case), `:49-63` (`safe_asin`), `:71-81` (`safe_sqrt`),
  `:251-258` (`wrap_2PI`, float), `:269-277` (`wrap_PI`), `:282-304` (`constrain_value_line`,
  i.e. `constrain_float`), `:418-432` (`calc_lowpass_alpha_dt`).

Deviation: core Lean has no `fmodf`, so `fmodf` is defined here from the bit patterns. C99
`fmod` is exact (its result is representable), so this is the C function, not an approximation.

Left out: `wrap_180`, `wrap_360` and their `_cd` forms, `linear_interpolate`, `expo_curve`,
`throttle_curve`, the integer `constrain_*`, `constrain_double`, random numbers, matrix helpers,
`get_vel_correction_for_sensor_offset`, the `double` `wrap_2PI`/`wrap_PI`, and the variadic
`sq`/`norm` templates beyond what `vector2.lean`/`vector3.lean` inline.
-/

namespace AP_Math

/-- `is_positive<float>` (`AP_Math.h:64-69`): `x >= FLT_EPSILON`. -/
def is_positive (x : Float32) : Bool := x ≥ FLT_EPSILON

/-- `is_negative<float>` (`AP_Math.h:75-80`): `x <= -1.0 * FLT_EPSILON`. -/
def is_negative (x : Float32) : Bool := x ≤ (-1.0 * FLT_EPSILON)

/-- `is_positive(double)` (`AP_Math.h:85-87`). -/
def is_positive_d (x : Float) : Bool := x ≥ FLT_EPSILON_d

/-- `is_negative(double)` (`AP_Math.h:92-94`). The C++ forms `-1.0f * FLT_EPSILON` in `float` and
widens it; the product is exact, so it equals `-1.0 * FLT_EPSILON_d`. -/
def is_negative_d (x : Float) : Bool := x ≤ ((-1.0 : Float) * FLT_EPSILON_d)

/-- `is_equal<float, float>` (`AP_Math.cpp:24-41`): `fabsf(v_1 - v_2) < FLT_EPSILON`. -/
def is_equal (v_1 v_2 : Float32) : Bool := (v_1 - v_2).abs < FLT_EPSILON

/-- `constrain_float` (`AP_Math.h:178` → `constrain_value_line<float>`, `AP_Math.cpp:282-304`):
NaN goes to the midpoint `(low + high) / 2`. -/
def constrain_float (amt low high : Float32) : Float32 :=
  if amt.isNaN then (low + high) / 2
  else if amt < low then low
  else if amt > high then high
  else amt

/-- `safe_sqrt<float>` (`AP_Math.cpp:71-81`): `sqrtf(v)` if `isgreaterequal(v, 0)`, else 0. -/
def safe_sqrt (v : Float32) : Float32 :=
  if v ≥ 0 then v.sqrt else 0

/-- `safe_asin<float>` (`AP_Math.cpp:49-63`). -/
def safe_asin (v : Float32) : Float32 :=
  if v.isNaN then 0.0
  else if v ≥ 1.0 then M_PI_2
  else if v ≤ -1.0 then -M_PI_2
  else v.asin

/-- `sq(float)` (`AP_Math.h:266-269`). -/
def sq (val : Float32) : Float32 := val * val

/-- `norm(float, float)` (`AP_Math.h:291-293`). -/
def norm (first second : Float32) : Float32 := (sq first + sq second).sqrt

/-- `norm(float, float, float)` (`AP_Math.h:294-296`). -/
def norm3 (first second third : Float32) : Float32 := (sq first + sq second + sq third).sqrt

/-- `MIN` (`AP_Math.h:299-303`): `one < two ? one : two`. Not Lean's `min`, which tests `≤`
and differs on signed zeros and NaN. -/
def MIN (one two : Float32) : Float32 := if one < two then one else two

/-- `MAX` (`AP_Math.h:306-310`): `one > two ? one : two`. -/
def MAX (one two : Float32) : Float32 := if one > two then one else two

/-- `radians(float)` (`AP_Math.h:232-235`). -/
def radians (deg : Float32) : Float32 := deg * DEG_TO_RAD

/-- `cd_to_rad` (`AP_Math.h:243-246`). -/
def cd_to_rad (cdeg : Float32) : Float32 := cdeg * CDEG_TO_RAD

/-- `rad_to_cd` (`AP_Math.h:249-252`). -/
def rad_to_cd (rad : Float32) : Float32 := rad * RAD_TO_CDEG

/-- `degrees(float)` (`AP_Math.h:255-258`). -/
def degrees (rad : Float32) : Float32 := rad * RAD_TO_DEG

/-- Magnitude bits of a non-negative finite `float` as `(m, e)` with value `m * 2^e`. -/
def fmodf_decode (b : UInt32) : Nat × Int :=
  let e := ((b >>> 23) &&& 0xff).toNat
  let m := (b &&& 0x7fffff).toNat
  if e = 0 then (m, -149) else (m + 2 ^ 23, (e : Int) - 150)

/-- `2^k` as a `float`, for `-149 ≤ k ≤ 127`. -/
def fmodf_pow2 (k : Int) : Float32 :=
  if k ≥ -126 then Float32.ofBits (UInt32.ofNat ((k + 127).toNat * 2 ^ 23))
  else Float32.ofBits (UInt32.ofNat (2 ^ (k + 149).toNat))

/-- C99 `fmodf(x, y)`: `x - n*y` with `n = trunc(x/y)`, computed exactly; the sign is that of `x`.
NaN if `x` is NaN or infinite or `y` is NaN or zero; `x` if `y` is infinite or `|x| < |y|`. -/
def fmodf (x y : Float32) : Float32 :=
  if x.isNaN || y.isNaN || x.isInf || y == 0 then Float32.ofBits 0x7fc00000
  else if y.isInf then x
  else if x.abs < y.abs then x
  else
    let (mx, ex) := fmodf_decode x.abs.toBits
    let (my, ey) := fmodf_decode y.abs.toBits
    -- here `ex ≥ ey`, and `r < my ≤ 2^24`, so both conversions below are exact
    let r := (mx * 2 ^ (ex - ey).toNat) % my
    let mag := (UInt64.ofNat r).toFloat32 * fmodf_pow2 ey
    if x.toBits >>> 31 == 1 then -mag else mag

/-- `wrap_2PI(float)` (`AP_Math.cpp:251-258`). -/
def wrap_2PI (radian : Float32) : Float32 :=
  let res := fmodf radian M_2PI
  if res < 0 then res + M_2PI else res

/-- `wrap_PI<float>` (`AP_Math.cpp:269-277`). -/
def wrap_PI (radian : Float32) : Float32 :=
  let res := wrap_2PI radian
  if res > M_PI then res - M_2PI else res

/-- `calc_lowpass_alpha_dt` (`AP_Math.cpp:418-432`); the `INTERNAL_ERROR` report is dropped. -/
def calc_lowpass_alpha_dt (dt cutoff_freq : Float32) : Float32 :=
  if is_negative dt || is_negative cutoff_freq then 1.0
  else if is_zero cutoff_freq then 1.0
  else if is_zero dt then 0.0
  else
    let rc := 1.0 / (M_2PI * cutoff_freq)
    dt / (dt + rc)

end AP_Math
