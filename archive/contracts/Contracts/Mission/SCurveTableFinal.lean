import Contracts.Mission.SCurveTableChain
import Contracts.Mission.SCurveTableT15
import Contracts.Mission.SCurveTableAssemble

/-!
# Pieces of the final assembly of `add_segments_spec`

The empty segments `8 … 14` copy entry `7` (`copy_step`), the jerk fields of the entries are
finite, and the real arithmetic of the accelerating phase (`accel_VP`: `V₇² ≤ 2 A P₇` and
`P₇ ≤ 5/2 V₇`).
-/

namespace Contracts.Mission

open Float.Model UnpackedFloat AC_WPNav_lib

noncomputable section

namespace SCT

theorem isPos_zero : is_positive_float (0.0 : Float32) = false := by
  rcases Bool.eq_false_or_eq_true (is_positive_float (0.0 : Float32)) with h | h
  · have := (wp_isPos_iff f32_isFinite_0p0).1 h
    rw [f32_toReal_0p0] at this
    have : (0 : ℝ) < 2 ^ (-23 : ℤ) := by positivity
    linarith
  · exact h

/-- The empty segments `8 … 14` copy the previous entry. -/
theorem copy_step {L Jm tj t2 t4 : Float32} {E : ℕ → SCurve.segment_t}
    (hEs : ∀ k, E (k + 1) = stepE L Jm tj t2 t4 t2 k (E k)) {k : ℕ} (hk1 : 7 ≤ k) (hk2 : k < 14)
    {J T T2 T4 t15 eT eA eV eP : ℝ}
    (h : Near (E k) (SC.tEnd J T T2 T4 t15 k) (SC.node J T T2 T4 t15 k) eT eA eV eP) :
    Near (E (k + 1)) (SC.tEnd J T T2 T4 t15 (k + 1)) (SC.node J T T2 T4 t15 (k + 1)) eT eA eV eP ∧
      (E (k + 1)).end_time = (E k).end_time ∧ (E (k + 1)).end_accel = (E k).end_accel ∧
      (E (k + 1)).seg_type = .CONSTANT_JERK ∧ (E (k + 1)).jerk_ref = 0.0 := by
  have ee : E (k + 1) = constE (E k) 0.0 0.0 := by
    rw [hEs]; interval_cases k <;> rfl
  have ne : SC.node J T T2 T4 t15 (k + 1) = SC.constNode (SC.node J T T2 T4 t15 k) 0 0 := by
    interval_cases k <;> rfl
  have te : SC.tEnd J T T2 T4 t15 (k + 1) = SC.tEnd J T T2 T4 t15 k + 0 := by
    interval_cases k <;> rfl
  obtain ⟨e1, e2, -, -, e5, e6⟩ := constE_neg (p := E k) (J0 := 0.0) isPos_zero
  rw [ee, ne, te]
  exact ⟨near_gated h isPos_zero 0, e1, e2, e5, e6⟩

theorem incrE_jerk_fin {p : SCurve.segment_t} {tj Jm : Float32} (fJ : Jm.IsFinite) :
    (incrE p tj Jm).jerk_ref.IsFinite := by
  unfold incrE; split
  · exact fJ
  · exact f32_isFinite_0p0

theorem decrE_jerk_fin {p : SCurve.segment_t} {tj Jm : Float32} (fJ : Jm.IsFinite) :
    (decrE p tj Jm).jerk_ref.IsFinite := by
  unfold decrE; split
  · exact fJ
  · exact f32_isFinite_0p0

theorem constE_jerk {p : SCurve.segment_t} {tin J0 : Float32} : (constE p tin J0).jerk_ref = J0 := by
  unfold constE; split <;> rfl

theorem constE_type {p : SCurve.segment_t} {tin J0 : Float32} :
    (constE p tin J0).seg_type = .CONSTANT_JERK := by
  unfold constE; split <;> rfl

/-- The accelerating phase: `V₇² ≤ 2 A P₇` and `P₇ ≤ 5/2 V₇`. -/
theorem accel_VP {A R t : ℝ} (hA : 0 ≤ A) (hR : 0 ≤ R) (hR1 : R ≤ 1) (ht : 0 ≤ t) (ht1 : t ≤ 3) :
    (A * (R + t)) ^ 2 ≤ 2 * A * (A * (R + t) * (2 * R + t) / 2) ∧
      A * (R + t) * (2 * R + t) / 2 ≤ 5 / 2 * (A * (R + t)) := by
  have hV : 0 ≤ A * (R + t) := by positivity
  constructor
  · have : (A * (R + t)) ^ 2 = A * (R + t) * (A * (R + t)) := by ring
    have h2 : A * (R + t) * (A * (R + t)) ≤ A * (R + t) * (A * (2 * R + t)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (by linarith) hA) hV
    nlinarith
  · have : 2 * R + t ≤ 5 := by linarith
    nlinarith

theorem le_of_sq_le {v c d : ℝ} (_hv : 0 ≤ v) (h : v ^ 2 ≤ c) (hd : 0 ≤ d) (hc : c ≤ d ^ 2) :
    v ≤ d := by
  by_contra hc'
  have := mul_self_lt_mul_self hd (not_le.1 hc')
  nlinarith

/-- The end of the profile when `t₁₅ > 0`: `2 P₇ + V₇ Q ≤ L + 2 e_P + 2·10⁻⁶ + e_V Q`. -/
theorem final_core {L P7 V7 P V Q eP eV : ℝ} (hQ0 : 0 ≤ Q) (hP : |P - P7| ≤ eP)
    (hV : |V - V7| ≤ eV) (hVQ : V * Q ≤ L - 2 * P + 2 / 10 ^ 6) :
    2 * P7 + V7 * Q ≤ L + 2 * eP + 2 / 10 ^ 6 + eV * Q := by
  have h1 := abs_le.1 hP
  have h2 := abs_le.1 hV
  have : V7 * Q ≤ V * Q + eV * Q := by
    have := mul_le_mul_of_nonneg_right (show V7 ≤ V + eV by linarith) hQ0
    linarith
  linarith

/-- `Q ≤ K` when the accelerating phase covers nearly half the leg. -/
theorem q_le_low {L Lh P7 V7 P V Q eP eV K : ℝ} (hLh : |Lh - L / 2| ≤ 11 / 10 ^ 8)
    (hlow : Lh * (1 - 1 / 10 ^ 4) ≤ P7) (hPV : P7 ≤ 5 / 2 * V7) (hP : |P - P7| ≤ eP)
    (hV : |V - V7| ≤ eV) (hVQ : V * Q ≤ L - 2 * P + 2 / 10 ^ 6) (hVpos : 0 < V) (hK : 0 ≤ K)
    (hcond : 2 * eP + 2 / 10 ^ 6 + K * eV + (4 / 10 * K + 2) * (11 / 10 ^ 8) <
      (19998 / 100000 * K - 1 / 10 ^ 4) * L) : Q ≤ K := by
  by_contra hc
  have hKQ : V * K < V * Q := mul_lt_mul_of_pos_left (not_le.1 hc) hVpos
  have h1 := abs_le.1 hP
  have h2 := abs_le.1 hV
  have h3 := abs_le.1 hLh
  have hV7 : 2 / 5 * P7 - eV ≤ V := by linarith
  have h4 : K * (2 / 5 * P7 - eV) ≤ K * V := mul_le_mul_of_nonneg_left hV7 hK
  nlinarith

/-- `Q` when `V₇ ≥ 1/4`. -/
theorem q_le_fast {L P7 V7 P V Q eP eV : ℝ} (hP70 : 0 ≤ P7) (h4 : 1 / 4 ≤ V7) (hP : |P - P7| ≤ eP)
    (hV : |V - V7| ≤ eV) (hVQ : V * Q ≤ L - 2 * P + 2 / 10 ^ 6) (hQ0 : 0 ≤ Q) :
    (1 / 4 - eV) * Q ≤ L + 2 * eP + 2 / 10 ^ 6 := by
  have h1 := abs_le.1 hP
  have h2 := abs_le.1 hV
  have := mul_le_mul_of_nonneg_right (show 1 / 4 - eV ≤ V by linarith) hQ0
  linarith

end SCT

end

end Contracts.Mission
