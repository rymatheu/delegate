import Contracts.Mission.FloatCalc
import Contracts.Mission.NavStop

/-!
# Shared float facts for the attitude-loop controller lemmas (milestone M4, C-series)

The translated attitude library `AC_Attitude_lib` has its own copies of the `AP_Math` predicates
(`is_positive`, `is_zero`, `is_negative`) and of `constrain_value_line`. This file reads them as
real comparisons on finite floats, gives the attitude controller's parameter values (the mission's
tuned set) as a hypothesis structure `AttParams`, and the `float` value of `π` that `radians` and
`calc_lowpass_alpha_dt` use (`Float.toFloat32 M_PI`, an opaque conversion: `LibmSpec.f64ToF32`).
-/

namespace Contracts.Track.Att

open Float.Model UnpackedFloat Contracts.Mission AC_Attitude_lib

noncomputable section

theorem eps_toReal : (1.1920929e-7 : Float32).toReal = 2 ^ (-23 : ℤ) := by
  rw [f32_toReal_1p1920929Em7]; norm_num

/-- `is_positive` of a finite float: at least `FLT_EPSILON = 2⁻²³`. -/
theorem isPos_iff {x : Float32} (hx : x.IsFinite) :
    is_positive_float x = true ↔ 2 ^ (-23 : ℤ) ≤ x.toReal := by
  show decide ((1.1920929e-7 : Float32) ≤ x) = true ↔ _
  rw [decide_eq_true_iff, Float32.le_iff_toReal_le f32_isFinite_1p1920929Em7 hx, eps_toReal]

theorem isPosAP_iff {x : Float32} (hx : x.IsFinite) :
    is_positive_AP_Float x = true ↔ 2 ^ (-23 : ℤ) ≤ x.toReal := by
  show decide ((1.1920929e-7 : Float32) ≤ x) = true ↔ _
  rw [decide_eq_true_iff, Float32.le_iff_toReal_le f32_isFinite_1p1920929Em7 hx, eps_toReal]

/-- `is_zero` of a finite float: below `FLT_EPSILON` in magnitude. -/
theorem isZero_iff {x : Float32} (hx : x.IsFinite) :
    is_zero_float x = true ↔ |x.toReal| < 2 ^ (-23 : ℤ) := by
  show decide (Float32.abs x < (1.1920929e-7 : Float32)) = true ↔ _
  rw [decide_eq_true_iff, Float32.lt_iff_toReal_lt ((Float32.isFinite_abs x).2 hx)
    f32_isFinite_1p1920929Em7, Float32.toReal_abs, eps_toReal]

theorem isZero_false {x : Float32} (hx : x.IsFinite) (h : 2 ^ (-23 : ℤ) ≤ |x.toReal|) :
    is_zero_float x = false := by
  rcases hz : is_zero_float x with _ | _
  · rfl
  · have := (isZero_iff hx).1 hz; linarith

theorem isZeroAP_eq (x : Float32) : is_zero_AP_Float x = is_zero_float x := rfl

theorem isPos_false {x : Float32} (hx : x.IsFinite) (h : x.toReal < 2 ^ (-23 : ℤ)) :
    is_positive_float x = false := by
  rcases hz : is_positive_float x with _ | _
  · rfl
  · have := (isPos_iff hx).1 hz; linarith

theorem isPos_true {x : Float32} (hx : x.IsFinite) (h : 2 ^ (-23 : ℤ) ≤ x.toReal) :
    is_positive_float x = true := (isPos_iff hx).2 h

/-- The threshold `-1.0 * (double) FLT_EPSILON` of `is_negative`, as a `double`: within `2⁻⁷⁰` of
`-2⁻²³`. -/
theorem negEps (hL : LibmSpec) :
    A64 (-(1.0 : Float) * Float32.toFloat (1.1920929e-7 : Float32)) (-2 ^ (-23 : ℤ)) (1 / 2 ^ 70) := by
  obtain ⟨f2, e2⟩ := hL.f32ToF64 _ f32_isFinite_1p1920929Em7
  have fm1 : (-(1.0 : Float)).IsFinite := (Float.isFinite_neg _).2 f64_isFinite_1p0
  have em1 : (-(1.0 : Float)).toReal = -1 := by rw [Float.toReal_neg, f64_toReal_1p0]
  have hm := A64.mul (A64.of_exact fm1) (A64.of_exact f2)
    (by rw [e2, eps_toReal, em1]; norm_num)
  refine (hm.congr (by rw [e2, eps_toReal, em1]; ring)).mono ?_
  rw [e2, eps_toReal, em1]; have := η64_small; simp only [u64]; norm_num; linarith

/-- `is_negative` (computed in `double`) is false above `-2⁻²⁴`. -/
theorem isNeg_false (hL : LibmSpec) {x : Float32} (hx : x.IsFinite)
    (h : -2 ^ (-24 : ℤ) ≤ x.toReal) : is_negative_float x = false := by
  show decide (Float32.toFloat x ≤ -(1.0 : Float) * Float32.toFloat (1.1920929e-7 : Float32)) = false
  rw [decide_eq_false_iff_not]
  obtain ⟨f1, e1⟩ := hL.f32ToF64 x hx
  have hn := negEps hL
  rw [Float.le_iff_toReal_le f1 hn.1, e1]
  intro hle
  have := (abs_le.1 hn.2).2
  have h2 : (2 : ℝ) ^ (-24 : ℤ) = 1 / 16777216 := by norm_num
  have h3 : (2 : ℝ) ^ (-23 : ℤ) = 1 / 8388608 := by norm_num
  rw [h2] at h; rw [h3] at this; norm_num at this; linarith

/-- `is_negative` is true below `-2⁻²²`. -/
theorem isNeg_true (hL : LibmSpec) {x : Float32} (hx : x.IsFinite)
    (h : x.toReal ≤ -2 ^ (-22 : ℤ)) : is_negative_float x = true := by
  show decide (Float32.toFloat x ≤ -(1.0 : Float) * Float32.toFloat (1.1920929e-7 : Float32)) = true
  rw [decide_eq_true_iff]
  obtain ⟨f1, e1⟩ := hL.f32ToF64 x hx
  have hn := negEps hL
  rw [Float.le_iff_toReal_le f1 hn.1, e1]
  have := (abs_le.1 hn.2).1
  have h2 : (2 : ℝ) ^ (-22 : ℤ) = 1 / 4194304 := by norm_num
  have h3 : (2 : ℝ) ^ (-23 : ℤ) = 1 / 8388608 := by norm_num
  rw [h2] at h; rw [h3] at this; norm_num at this; linarith

/-- `constrain_value` of finite floats with `low ≤ high` is the real clamp. -/
theorem constrain_spec {amt low high : Float32} (line : UInt32) (ha : amt.IsFinite)
    (hl : low.IsFinite) (hh : high.IsFinite) (hlh : low.toReal ≤ high.toReal) :
    (constrain_value_line_float amt low high line).IsFinite ∧
      (constrain_value_line_float amt low high line).toReal =
        max low.toReal (min high.toReal amt.toReal) := by
  simp only [constrain_value_line_float, Id.run, Contracts.Mission.Float32.isNaN_of_isFinite ha,
    Bool.false_eq_true, ite_false, id_pure_eq]
  by_cases h1 : amt < low
  · rw [ite_eq_left h1]
    have := (Float32.lt_iff_toReal_lt ha hl).1 h1
    exact ⟨hl, by rw [min_eq_right (by linarith), max_eq_left this.le]⟩
  · rw [ite_eq_right h1]
    have h1' : low.toReal ≤ amt.toReal := not_lt.1 ((Float32.lt_iff_toReal_lt ha hl).not.1 h1)
    by_cases h2 : amt > high
    · rw [ite_eq_left h2]
      have := (Float32.lt_iff_toReal_lt hh ha).1 h2
      exact ⟨hh, by rw [min_eq_left this.le, max_eq_right hlh]⟩
    · rw [ite_eq_right h2]
      have h2' : amt.toReal ≤ high.toReal :=
        not_lt.1 ((Float32.lt_iff_toReal_lt hh ha).not.1 h2)
      exact ⟨ha, by rw [min_eq_right h2', max_eq_right h1']⟩

/-- Inside the bounds, `constrain_value` returns its argument. -/
theorem constrain_inside {amt low high : Float32} (line : UInt32) (ha : amt.IsFinite)
    (hl : low.IsFinite) (hh : high.IsFinite) (h1 : low.toReal ≤ amt.toReal)
    (h2 : amt.toReal ≤ high.toReal) :
    constrain_value_line_float amt low high line = amt := by
  simp only [constrain_value_line_float, Id.run, Contracts.Mission.Float32.isNaN_of_isFinite ha,
    Bool.false_eq_true, ite_false, id_pure_eq]
  rw [ite_eq_right (fun h => absurd ((Float32.lt_iff_toReal_lt ha hl).1 h) (not_lt.2 h1)),
    ite_eq_right (fun h => absurd ((Float32.lt_iff_toReal_lt hh ha).1 h) (not_lt.2 h2))]

/-! ## `π` in `float` -/

/-- `M_PI` as a `double`. -/
def piD : ℝ := 884279719003555 / 281474976710656

theorem piD_close : |piD - Real.pi| ≤ 1 / 10 ^ 15 := by
  have h1 := Real.pi_gt_d20; have h2 := Real.pi_lt_d20
  rw [abs_le]; constructor <;> norm_num [piD] <;> linarith

/-- `(float) M_PI` is within `2⁻²⁴ π + 2⁻¹⁴⁹` of `M_PI`. -/
theorem pi32 (hL : LibmSpec) :
    A32 (Float.toFloat32 (3.1415926535897931 : Float)) piD (u32 * piD + η32) := by
  have h := A64.toFloat32 hL (A64.of_exact f64_isFinite_3p1415926535897931)
    (by rw [f64_toReal_3p1415926535897931, abs_of_nonneg (by norm_num)]; simp only [capF]; norm_num)
  rw [f64_toReal_3p1415926535897931] at h
  refine (h.congr rfl).mono ?_
  simp only [piD, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 884279719003555 / 281474976710656)]
  norm_num

end

end Contracts.Track.Att
