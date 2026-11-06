import Contracts.Mission.NavStop
import Contracts.Mission.FloatCalc

/-!
# The `AP_Math` helpers of the navigator's translation (`AC_WPNav_lib`)

`is_positive`, `is_zero`, `is_negative`, `MIN`, `MAX`, `safe_sqrt` as real statements on finite
floats.
-/

namespace Contracts.Mission

open Float.Model UnpackedFloat AC_WPNav_lib

noncomputable section

theorem wp_isPos_iff {x : Float32} (hx : x.IsFinite) :
    is_positive_float x = true ↔ 2 ^ (-23 : ℤ) ≤ x.toReal := by
  show decide ((1.1920929e-7 : Float32) ≤ x) = true ↔ _
  rw [decide_eq_true_iff, Float32.le_iff_toReal_le f32_isFinite_1p1920929Em7 hx, f32_toReal_eps]

theorem wp_isZero_iff {x : Float32} (hx : x.IsFinite) :
    is_zero_float x = true ↔ |x.toReal| < 2 ^ (-23 : ℤ) := by
  show decide (Float32.abs x < (1.1920929e-7 : Float32)) = true ↔ _
  rw [decide_eq_true_iff, Float32.lt_iff_toReal_lt ((Float32.isFinite_abs x).2 hx)
    f32_isFinite_1p1920929Em7, Float32.toReal_abs, f32_toReal_eps]

/-- Multiplying a finite `double` by `-1.0` is exact. -/
theorem f64_neg_one_mul {y : Float} (hy : y.IsFinite) :
    (-(1.0 : Float) * y).IsFinite ∧ (-(1.0 : Float) * y).toReal = -y.toReal := by
  have fm1 : (-(1.0 : Float)).IsFinite := (Float.isFinite_neg _).2 f64_isFinite_1p0
  have em1 : (-(1.0 : Float)).toReal = -1 := by rw [Float.toReal_neg, f64_toReal_1p0]
  have hm : |(-(1.0 : Float)).toReal * y.toReal| ≤ maxFinite := by
    rw [em1, neg_one_mul, abs_neg]; exact Float.abs_toReal_le_maxFinite y
  have hf := (Float.isFinite_neg y).2 hy
  obtain ⟨b1, b2⟩ := Float.mul_bracket fm1 hy hm hf
  simp only [Float.toReal_neg, f64_toReal_1p0] at b1 b2
  obtain ⟨fin, -⟩ := Float.mul_err_all fm1 hy hm
  exact ⟨fin, le_antisymm (b2 (by ring_nf; exact le_rfl)) (b1 (by ring_nf; exact le_rfl))⟩

theorem wp_isNeg_iff (hL : LibmSpec) {x : Float32} (hx : x.IsFinite) :
    is_negative_float x = true ↔ x.toReal ≤ -2 ^ (-23 : ℤ) := by
  show decide (Float32.toFloat x ≤ -(1.0 : Float) * Float32.toFloat (1.1920929e-7 : Float32)) = true ↔ _
  obtain ⟨f1, e1⟩ := hL.f32ToF64 x hx
  obtain ⟨f2, e2⟩ := hL.f32ToF64 _ f32_isFinite_1p1920929Em7
  obtain ⟨f3, e3⟩ := f64_neg_one_mul f2
  rw [decide_eq_true_iff, Float.le_iff_toReal_le f1 f3, e1, e3, e2, f32_toReal_eps]

theorem wp_min_spec {a b : Float32} (ha : a.IsFinite) (hb : b.IsFinite) :
    (MIN_float2 a b).IsFinite ∧ (MIN_float2 a b).toReal = min a.toReal b.toReal := by
  simp only [MIN_float2, Id.run, id_pure_eq]
  by_cases h : a < b
  · rw [ite_eq_left h]
    exact ⟨ha, (min_eq_left ((Float32.lt_iff_toReal_lt ha hb).1 h).le).symm⟩
  · rw [ite_eq_right h]
    exact ⟨hb, (min_eq_right (not_lt.1 ((Float32.lt_iff_toReal_lt ha hb).not.1 h))).symm⟩

theorem wp_max_spec {a b : Float32} (ha : a.IsFinite) (hb : b.IsFinite) :
    (MAX_float2 a b).IsFinite ∧ (MAX_float2 a b).toReal = max a.toReal b.toReal := by
  simp only [MAX_float2, Id.run, id_pure_eq]
  by_cases h : a > b
  · rw [ite_eq_left h]
    exact ⟨ha, (max_eq_left ((Float32.lt_iff_toReal_lt hb ha).1 h).le).symm⟩
  · rw [ite_eq_right h]
    exact ⟨hb, (max_eq_right (not_lt.1 ((Float32.lt_iff_toReal_lt hb ha).not.1 h))).symm⟩

theorem wp_safe_sqrt (hL : LibmSpec) {v : Float32} (hv : v.IsFinite) :
    (0 ≤ v.toReal → safe_sqrt_float v = Float32.sqrt v) ∧
      (v.toReal < 0 → safe_sqrt_float v = 0) := by
  obtain ⟨f1, e1⟩ := hL.f32ToF64 v hv
  have h0 : Int32.toFloat (0 : Int32) = 0 := by decide
  have h0' : Int32.toFloat32 (0 : Int32) = 0 := by decide
  simp only [safe_sqrt_float, Id.run, id_pure_eq, h0, h0', ge_iff_le]
  constructor
  · intro h
    rw [ite_eq_left (decide_eq_true ((Float.le_iff_toReal_le Float.isFinite_zero f1).2
      (by rw [e1, Float.toReal_zero]; exact h)))]
  · intro h
    rw [ite_eq_right (fun hc => by
      have := (Float.le_iff_toReal_le Float.isFinite_zero f1).1 (of_decide_eq_true hc)
      rw [e1, Float.toReal_zero] at this; linarith)]

end

end Contracts.Mission
