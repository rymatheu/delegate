import FloatModel.Lit
import FloatModel.Err
import Contracts.Mission.Spec
import AC_PID_lib
import AP_Math_lib

/-!
# The float layer on the translated code

What the translator emits, in terms of the float layer (`FLOAT.md`):

* every library's `constrain_value_line_float` is `Float32.cvl` (the NaN-safe clamp, `cvl_between`,
  `cvl_mem`, `cvl_of_between`, `cvl_symm`), and `AP_Math_lib.constrain_value_line_double` is
  `Float.cvl` (the simp set `cvl_eqs`);
* every library's `MIN_float2`/`MAX_float2` (`MIN`/`MAX` of `AP_Math.h`) is
  `if a < b then a else b` / `if a > b then a else b` (`Float32.ite_lt_min`, `ite_gt_max`);
* `CppLibm.fminf`/`fmaxf` and the `float`/`double` conversions (opaque externs) as `Near`
  statements under `LibmSpec`.
-/

namespace Contracts.Track.FloatLib

open Contracts.Mission

/-! ## The clamps -/

theorem motors_cvl (a lo hi : Float32) (l : UInt32) :
    AP_Motors_lib.constrain_value_line_float a lo hi l = Float32.cvl a lo hi := rfl
theorem attitude_cvl (a lo hi : Float32) (l : UInt32) :
    AC_Attitude_lib.constrain_value_line_float a lo hi l = Float32.cvl a lo hi := rfl
theorem poscontrol_cvl (a lo hi : Float32) (l : UInt32) :
    AC_PosControl_lib.constrain_value_line_float a lo hi l = Float32.cvl a lo hi := rfl
theorem wpnav_cvl (a lo hi : Float32) (l : UInt32) :
    AC_WPNav_lib.constrain_value_line_float a lo hi l = Float32.cvl a lo hi := rfl
theorem ahrs_cvl (a lo hi : Float32) (l : UInt32) :
    AHRS_View_lib.constrain_value_line_float a lo hi l = Float32.cvl a lo hi := rfl
theorem pid_cvl (a lo hi : Float32) (l : UInt32) :
    AC_PID_lib.constrain_value_line_float a lo hi l = Float32.cvl a lo hi := rfl
theorem math_cvl (a lo hi : Float32) (l : UInt32) :
    AP_Math_lib.constrain_value_line_float a lo hi l = Float32.cvl a lo hi := rfl
theorem math_cvl_double (a lo hi : Float) (l : UInt32) :
    AP_Math_lib.constrain_value_line_double a lo hi l = Float.cvl a lo hi := rfl

/-- All the translated clamps, as `Float32.cvl`/`Float.cvl`. -/
theorem cvl_eqs :
    (AP_Motors_lib.constrain_value_line_float = fun a lo hi _ => Float32.cvl a lo hi) ∧
    (AC_Attitude_lib.constrain_value_line_float = fun a lo hi _ => Float32.cvl a lo hi) ∧
    (AC_PosControl_lib.constrain_value_line_float = fun a lo hi _ => Float32.cvl a lo hi) ∧
    (AC_WPNav_lib.constrain_value_line_float = fun a lo hi _ => Float32.cvl a lo hi) ∧
    (AHRS_View_lib.constrain_value_line_float = fun a lo hi _ => Float32.cvl a lo hi) ∧
    (AC_PID_lib.constrain_value_line_float = fun a lo hi _ => Float32.cvl a lo hi) ∧
    (AP_Math_lib.constrain_value_line_float = fun a lo hi _ => Float32.cvl a lo hi) ∧
    (AP_Math_lib.constrain_value_line_double = fun a lo hi _ => Float.cvl a lo hi) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The clamp of a finite value into finite bounds `lo ≤ hi` (below `maxFinite32 / 2`) is the real
clamp: `max lo (min a hi)`. -/
theorem cvl_toReal {a lo hi : Float32} (ha : a.IsFinite) (hlo : lo.IsFinite) (hhi : hi.IsFinite)
    (hle : lo.toReal ≤ hi.toReal) :
    (Float32.cvl a lo hi).toReal = max lo.toReal (min a.toReal hi.toReal) := by
  unfold Float32.cvl
  rw [ite_eq_right (by rw [Float32.not_isNaN_of_isFinite ha]; decide)]
  by_cases h1 : a < lo
  · rw [ite_eq_left h1]
    have := (Float32.lt_iff_toReal_lt ha hlo).1 h1
    rw [min_eq_left (by linarith), max_eq_left this.le]
  · rw [ite_eq_right h1]
    have h1' := not_lt.1 ((Float32.lt_iff_toReal_lt ha hlo).not.1 h1)
    by_cases h2 : a > hi
    · rw [ite_eq_left h2]
      have := (Float32.lt_iff_toReal_lt hhi ha).1 h2
      rw [min_eq_right this.le, max_eq_right hle]
    · rw [ite_eq_right h2]
      have h2' := not_lt.1 ((Float32.lt_iff_toReal_lt hhi ha).not.1 h2)
      rw [min_eq_left h2', max_eq_right h1']

/-! ## `MIN`/`MAX` -/

theorem motors_min (a b : Float32) : AP_Motors_lib.MIN_float2 a b = if a < b then a else b := rfl
theorem motors_max (a b : Float32) : AP_Motors_lib.MAX_float2 a b = if a > b then a else b := rfl
theorem attitude_min (a b : Float32) : AC_Attitude_lib.MIN_float2 a b = if a < b then a else b :=
  rfl
theorem attitude_max (a b : Float32) : AC_Attitude_lib.MAX_float2 a b = if a > b then a else b :=
  rfl
theorem poscontrol_min (a b : Float32) :
    AC_PosControl_lib.MIN_float2 a b = if a < b then a else b := rfl
theorem poscontrol_max (a b : Float32) :
    AC_PosControl_lib.MAX_float2 a b = if a > b then a else b := rfl
theorem wpnav_min (a b : Float32) : AC_WPNav_lib.MIN_float2 a b = if a < b then a else b := rfl
theorem wpnav_max (a b : Float32) : AC_WPNav_lib.MAX_float2 a b = if a > b then a else b := rfl
theorem math_min (a b : Float32) : AP_Math_lib.MIN_float2 a b = if a < b then a else b := rfl
theorem math_max (a b : Float32) : AP_Math_lib.MAX_float2 a b = if a > b then a else b := rfl

/-! ## The C library and the conversions, under `LibmSpec` -/

theorem fminf_near (hL : LibmSpec) {a b : Float32} (ha : a.IsFinite) (hb : b.IsFinite) :
    Float32.Near (CppLibm.fminf a b) (min a.toReal b.toReal) 0 :=
  Float32.Near.of_eq (hL.fminf a b ha hb).1 (hL.fminf a b ha hb).2

theorem fmaxf_near (hL : LibmSpec) {a b : Float32} (ha : a.IsFinite) (hb : b.IsFinite) :
    Float32.Near (CppLibm.fmaxf a b) (max a.toReal b.toReal) 0 :=
  Float32.Near.of_eq (hL.fmaxf a b ha hb).1 (hL.fmaxf a b ha hb).2

/-- `(double) f` is exact. -/
theorem toFloat_near (hL : LibmSpec) {a : Float32} (ha : a.IsFinite) :
    Float.Near (Float32.toFloat a) a.toReal 0 :=
  Float.Near.of_eq (hL.f32ToF64 a ha).1 (hL.f32ToF64 a ha).2

/-- `(float) d` rounds correctly on the `float` range. -/
theorem toFloat32_near (hL : LibmSpec) {a : Float} (ha : a.IsFinite)
    (hM : |a.toReal| ≤ Float.Model.UnpackedFloat.maxFinite32) :
    Float32.Near (Float.toFloat32 a) a.toReal (2 ^ (-24 : ℤ) * |a.toReal| + 2 ^ (-150 : ℤ)) :=
  ⟨(hL.f64ToF32 a ha hM).1, (hL.f64ToF32 a ha hM).2⟩

/-- `(float) d` of a `double` literal that is a `float` value is that value (the translator writes
`float` constants of the C++ source as `Float.toFloat32 (c : Float)`). -/
theorem toFloat32_exact (hL : LibmSpec) {a : Float} {b : Float32} (ha : a.IsFinite)
    (hb : b.IsFinite) (h : b.toReal = a.toReal) :
    Float32.Near (Float.toFloat32 a) a.toReal 0 :=
  Float32.Near.of_eq (hL.f64ToF32_exact a b ha hb h).1 (hL.f64ToF32_exact a b ha hb h).2

end Contracts.Track.FloatLib
