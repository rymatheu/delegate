import Contracts.Mission.SCurveTableNear

/-!
# The constant-velocity time `t₁₅` of `add_segments`

`t₁₅ = MAX(0, (L - 2 P₁₄) / V₁₄)` in `float`: finite, nonnegative, and when positive
`V₁₄ t₁₅` is within `2·10⁻⁶` of `L - 2 P₁₄` (`t15_spec`).
-/

namespace Contracts.Mission

open Float.Model UnpackedFloat AC_WPNav_lib

noncomputable section

namespace SCT

theorem t15_spec {L : Float32} {e : SCurve.segment_t} (fL : L.IsFinite) (fP : e.end_pos.IsFinite)
    (fV : e.end_vel.IsFinite) (hL0 : 0 ≤ L.toReal) (hL1 : L.toReal ≤ 4) (hP : |e.end_pos.toReal| ≤ 2)
    (hV0 : 1 / 100000 ≤ e.end_vel.toReal) (hV1 : e.end_vel.toReal ≤ 4) :
    (t15F L e).IsFinite ∧ 0 ≤ (t15F L e).toReal ∧
      (0 < (t15F L e).toReal →
        |e.end_vel.toReal * (t15F L e).toReal - (L.toReal - 2 * e.end_pos.toReal)| ≤ 2 / 10 ^ 6) := by
  have two : B32 (2.0 : Float32) 2 0 2 := B32.sce_lit f32_isFinite_2p0 f32_toReal_2p0 (by norm_num)
  have eP := B32.of_exact fP hP
  have eL := B32.of_exact fL (R := 4) (by rw [abs_of_nonneg hL0]; exact hL1)
  have m := B32.mul two eP (e := 239 / 10 ^ 9) (R := 4) (by norm_num [capF]) (by norm_num [capF])
    (by norm_num)
  have n := B32.sub eL m (e := 718 / 10 ^ 9) (R := 8) (by norm_num) (by norm_num [capF])
    (by norm_num)
  have hV : A32 e.end_vel e.end_vel.toReal 0 := A32.of_exact fV
  have hVp : 0 < e.end_vel.toReal := by linarith
  have d := A32.div n.1 hV hVp (by rw [add_zero, abs_of_pos hVp]) (by
    have hq : |(L.toReal - 2 * e.end_pos.toReal) / e.end_vel.toReal| ≤ 8 * 100000 := by
      rw [abs_div, abs_of_pos hVp, div_le_iff₀ hVp]
      have := n.2; nlinarith
    have : (|e.end_vel.toReal| * (718 / 10 ^ 9) + |L.toReal - 2 * e.end_pos.toReal| * 0) /
        (e.end_vel.toReal * |e.end_vel.toReal|) ≤ 1 := by
      rw [abs_of_pos hVp, mul_zero, add_zero, div_le_one (by positivity)]; nlinarith
    linarith [show (8 * 100000 : ℝ) + 1 ≤ capF by norm_num [capF]])
  obtain ⟨fD, hD⟩ := d
  set D := (L - 2.0 * e.end_pos) / e.end_vel with hDdef
  set r := L.toReal - 2 * e.end_pos.toReal with hr
  have hrb : |r| ≤ 8 := n.2
  obtain ⟨fM, hM⟩ := wp_max_spec f32_isFinite_0p0 fD
  have ht : t15F L e = MAX_float2 (0.0 : Float32) D := rfl
  rw [ht]
  refine ⟨fM, by rw [hM]; exact le_max_left _ _, fun hpos => ?_⟩
  rw [hM, f32_toReal_0p0] at hpos ⊢
  have hDpos : 0 < D.toReal := by
    rcases le_total D.toReal 0 with h | h
    · rw [max_eq_left h] at hpos; exact absurd hpos (lt_irrefl 0)
    · rcases h.lt_or_eq with h | h
      · exact h
      · rw [← h, max_self] at hpos; exact absurd hpos (lt_irrefl 0)
  rw [max_eq_right hDpos.le]
  rw [abs_of_pos hVp, mul_zero, add_zero] at hD
  -- `|V D - r| = V |D - r / V|`
  have key : e.end_vel.toReal * D.toReal - r = e.end_vel.toReal * (D.toReal - r / e.end_vel.toReal) := by
    field_simp
  rw [key, abs_mul, abs_of_pos hVp]
  have h1 : e.end_vel.toReal * (718 / 10 ^ 9) / (e.end_vel.toReal * e.end_vel.toReal) =
      718 / 10 ^ 9 / e.end_vel.toReal := by field_simp
  rw [h1] at hD
  have hq : |r / e.end_vel.toReal| = |r| / e.end_vel.toReal := by rw [abs_div, abs_of_pos hVp]
  rw [hq] at hD
  have h2 : e.end_vel.toReal * (718 / 10 ^ 9 / e.end_vel.toReal + 2 ^ (-24 : ℤ) *
      (|r| / e.end_vel.toReal + 718 / 10 ^ 9 / e.end_vel.toReal) + η32) =
      718 / 10 ^ 9 + 2 ^ (-24 : ℤ) * (|r| + 718 / 10 ^ 9) + e.end_vel.toReal * η32 := by
    field_simp
  have h3 := mul_le_mul_of_nonneg_left hD hVp.le
  rw [h2] at h3
  have hu : (2 : ℝ) ^ (-24 : ℤ) = 1 / 16777216 := by norm_num
  rw [hu] at h3
  have he := η32_small
  have he0 := η32_pos
  have : e.end_vel.toReal * η32 ≤ 4 * (1 / 10 ^ 40) := mul_le_mul hV1 he he0.le (by norm_num)
  nlinarith

end SCT

end

end Contracts.Mission
