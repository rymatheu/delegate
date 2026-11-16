import Contracts.Track.AttitudeYawPhaseCore

/-!
# Y5: the overshoot bound (scaled units)

A sharper invariant than `InvU`: the "stopping point under maximal braking" of every state that
moves toward negative errors stays above `−Ml`:

  `0 ≤ w → −Ml ≤ ε − DU w a`,

where `DU w a` (a cubic in `w` and `max a 0`) dominates the distance travelled when the acceleration
is ramped down at the jerk limit to `−10` and held (`DU_ramp`, `DU_floor`: one braking tick lowers `DU`
by at least `w`). A tick that does not brake maximally has a target `t ≥ a'`, which forces the new
error beyond a threshold (`tU_lin_thr`, `tU_sqrt_thr`); the polynomial inequalities `DU_*` (Handelman
certificates, checked by `linarith`) show that the new stopping point is then above `−3000`.
Reversals of the rate (`w < 0 ≤ w'`) happen only in the linear zone (the jerk reserve `Rs_step`
excludes them in the sqrt zones), and cost at most `1000 + 2000`. With `Ml = Mu = 3000`
(`3000 h²J = 9π/3200 ≈ 0.0088` rad) the error stays above `−9π/3200` for all ticks.
-/

noncomputable section

namespace Contracts.Track.YawPhase

/-- The max-braking distance bound. -/
def DU (w a : ℝ) : ℝ :=
  13/250*w^2 + 26/25*w - 17/200*w*(a+10) + 13/250*w*(a+10)^2 + 6/5*(max a 0)^2 + 3/5*(max a 0)^3

theorem DU_ge {w a : ℝ} (hw : 0 ≤ w) (_ha : -10 ≤ a) : w ≤ DU w a := by
  unfold DU
  have h1 := sq_nonneg (max a 0); have h2 : 0 ≤ max a 0 ^ 3 := pow_nonneg (le_max_right _ _) 3
  nlinarith [mul_nonneg hw (sq_nonneg (a + 10 - 17/20)), sq_nonneg w]

theorem DU_floor {w a : ℝ} (ha' : a ≤ -9) (hw : 10 ≤ w) :
    w ≤ DU w a - DU (w - 10) (-10) := by
  unfold DU
  rw [max_eq_right (by linarith : a ≤ 0), max_eq_right (by norm_num : (-10:ℝ) ≤ 0)]
  nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ w) (sq_nonneg (a + 10 - 17/20))]

theorem DU_ramp {w a : ℝ} (hw : 0 ≤ w) (_ha : -9 ≤ a) (ha2 : a ≤ 10) (hw' : 0 ≤ w + (a - 1)) :
    w ≤ DU w a - DU (w + (a - 1)) (a - 1) := by
  unfold DU
  rcases le_total 1 a with h1 | h1
  · rw [max_eq_left (by linarith : (0:ℝ) ≤ a), max_eq_left (by linarith : (0:ℝ) ≤ a - 1)]
    nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ 10 - a) (by linarith : (0:ℝ) ≤ a - 1),
      pow_nonneg (by linarith : (0:ℝ) ≤ a - 1) 3,
      mul_nonneg (by linarith : (0:ℝ) ≤ 10 - a) (sq_nonneg (a - 12/5))]
  · rcases le_total 0 a with h0 | h0
    · rw [max_eq_left h0, max_eq_right (by linarith : a - 1 ≤ 0)]
      nlinarith [mul_nonneg hw h0, mul_nonneg hw' h0, mul_nonneg hw' (sq_nonneg (a + 9)), sq_nonneg a,
        pow_nonneg h0 3]
    · rw [max_eq_right h0, max_eq_right (by linarith : a - 1 ≤ 0)]
      nlinarith [mul_nonneg hw' (sq_nonneg (a + 9)), mul_nonneg hw (by linarith : (0:ℝ) ≤ a + 9),
        mul_nonneg hw' (by linarith : (0:ℝ) ≤ a + 9), mul_nonneg hw (sq_nonneg (a + 9))]

/-! ### Polynomial inequalities (Handelman certificates) -/

theorem DU_lin_pos {w x : ℝ} (g0 : 0 ≤ w) (g1 : 0 ≤ x + 10) (g2 : 0 ≤ 10 - x) (g3 : 0 ≤ w + x) (g4 : 0 ≤ 1000 - 100 * x - 10 * w) (g5 : 0 ≤ 100 * x + 10 * w + 1000) (g6 : 0 ≤ x) :
    DU (w + x) x ≤ 100 * x + 10 * w + 3000 := by
  unfold DU; rw [max_eq_left g6]
  linarith [g6, mul_nonneg (g2) g5, mul_nonneg (mul_nonneg (g0) g0) g6, mul_nonneg (mul_nonneg (g0) g6) g6, mul_nonneg (mul_nonneg (g1) g3) g4, mul_nonneg (mul_nonneg (g1) g4) g4, mul_nonneg (mul_nonneg (g1) g4) g5, mul_nonneg (mul_nonneg (g3) g3) g4, mul_nonneg (mul_nonneg (g3) g4) g4, mul_nonneg (mul_nonneg (g4) g4) g4]

theorem DU_lin_neg {w x : ℝ} (_g0 : 0 ≤ w) (g1 : 0 ≤ x + 10) (_g2 : 0 ≤ 10 - x) (g3 : 0 ≤ w + x) (g4 : 0 ≤ 1000 - 100 * x - 10 * w) (g5 : 0 ≤ 100 * x + 10 * w + 1000) (g6 : 0 ≤ -x) :
    DU (w + x) x ≤ 100 * x + 10 * w + 3000 := by
  unfold DU; rw [max_eq_right (by linarith : x ≤ 0)]
  linarith [mul_nonneg (g4) g5, mul_nonneg (mul_nonneg (g1) g3) g3, mul_nonneg (mul_nonneg (g1) g3) g4, mul_nonneg (mul_nonneg (g1) g3) g6, mul_nonneg (mul_nonneg (g1) g4) g4, mul_nonneg (mul_nonneg (g1) g4) g5, mul_nonneg (mul_nonneg (g1) g5) g5]

theorem DU_flip {w x : ℝ} (g0 : 0 ≤ w) (g1 : 0 ≤ x - w) (g2 : 0 ≤ 10 - x) :
    DU w x ≤ 2000 := by
  unfold DU; rw [max_eq_left (by linarith : (0:ℝ) ≤ x)]
  linarith [mul_nonneg (g0) g0, mul_nonneg (g2) g2, mul_nonneg (mul_nonneg (g0) g0) g1, mul_nonneg (mul_nonneg (g0) g0) g2, mul_nonneg (mul_nonneg (g0) g1) g1, mul_nonneg (mul_nonneg (g0) g1) g2, mul_nonneg (mul_nonneg (g0) g2) g2, mul_nonneg (mul_nonneg (g1) g1) g1, mul_nonneg (mul_nonneg (g1) g1) g2, mul_nonneg (mul_nonneg (g1) g2) g2]

theorem DU_tiny_pos {w x : ℝ} (g0 : 0 ≤ w) (g1 : 0 ≤ 1 / 1000 - w) (g2 : 0 ≤ x + 10) (g3 : 0 ≤ 10 - x) (g4 : 0 ≤ w + x) (g5 : 0 ≤ x) :
    DU (w + x) x ≤ 4000 := by
  unfold DU; rw [max_eq_left g5]
  linarith [mul_nonneg (mul_nonneg (g0) g1) g2, mul_nonneg (mul_nonneg (g0) g5) g5, mul_nonneg (mul_nonneg (g1) g1) g1, mul_nonneg (mul_nonneg (g1) g1) g4, mul_nonneg (mul_nonneg (g1) g2) g2, mul_nonneg (mul_nonneg (g1) g3) g4, mul_nonneg (mul_nonneg (g2) g3) g3, mul_nonneg (mul_nonneg (g3) g3) g4, mul_nonneg (mul_nonneg (g3) g4) g4, mul_nonneg (mul_nonneg (g5) g5) g5]

theorem DU_tiny_neg {w x : ℝ} (g0 : 0 ≤ w) (g1 : 0 ≤ 1 / 1000 - w) (g2 : 0 ≤ x + 10) (g3 : 0 ≤ 10 - x) (g4 : 0 ≤ w + x) (g5 : 0 ≤ -x) :
    DU (w + x) x ≤ 4000 := by
  unfold DU; rw [max_eq_right (by linarith : x ≤ 0)]
  linarith [mul_nonneg (mul_nonneg (g0) g1) g3, mul_nonneg (mul_nonneg (g0) g2) g4, mul_nonneg (mul_nonneg (g1) g1) g5, mul_nonneg (mul_nonneg (g1) g2) g2, mul_nonneg (mul_nonneg (g1) g4) g5, mul_nonneg (mul_nonneg (g2) g2) g2, mul_nonneg (mul_nonneg (g2) g3) g3, mul_nonneg (mul_nonneg (g3) g4) g5, mul_nonneg (mul_nonneg (g4) g4) g5]

theorem DU_bneg {w x : ℝ} (g0 : 0 ≤ w) (g1 : 0 ≤ x + 10) (g2 : 0 ≤ -(w + 10 * x)) (g3 : 0 ≤ w + x) (_g4 : 0 ≤ -x) :
    DU (w + x) x ≤ 4000 := by
  unfold DU; rw [max_eq_right (by linarith : x ≤ 0)]
  linarith [mul_nonneg (mul_nonneg (g0) g1) g1, mul_nonneg (mul_nonneg (g0) g1) g2, mul_nonneg (mul_nonneg (g0) g2) g2, mul_nonneg (mul_nonneg (g0) g2) g3, mul_nonneg (mul_nonneg (g1) g1) g1, mul_nonneg (mul_nonneg (g1) g1) g2, mul_nonneg (mul_nonneg (g1) g2) g2, mul_nonneg (mul_nonneg (g1) g3) g3, mul_nonneg (mul_nonneg (g2) g2) g2]

theorem DU_sq0_pos {w x : ℝ} (g0 : 0 ≤ w) (g1 : 0 ≤ x + 10) (g2 : 0 ≤ 10 - x) (g3 : 0 ≤ w + x) (_g4 : 0 ≤ w + 10 * x - 0) (g5 : 0 ≤ 400 - (w + 10 * x)) (g6 : 0 ≤ x) :
    DU (w + x) x ≤ (w + 10 * x + 1 / 5 * w) ^ 2 / 20 + 3500 := by
  unfold DU; rw [max_eq_left g6]
  linarith [mul_nonneg (g1) g5, mul_nonneg (mul_nonneg (g0) g0) g0, mul_nonneg (mul_nonneg (g0) g0) g6, mul_nonneg (mul_nonneg (g0) g1) g5, mul_nonneg (mul_nonneg (g1) g1) g2, mul_nonneg (mul_nonneg (g1) g2) g3, mul_nonneg (mul_nonneg (g2) g2) g2, mul_nonneg (mul_nonneg (g2) g2) g3, mul_nonneg (mul_nonneg (g3) g3) g5, mul_nonneg (mul_nonneg (g5) g5) g5]

theorem DU_sq0_neg {w x : ℝ} (g0 : 0 ≤ w) (g1 : 0 ≤ x + 10) (g2 : 0 ≤ 10 - x) (g3 : 0 ≤ w + x) (_g4 : 0 ≤ w + 10 * x - 0) (g5 : 0 ≤ 400 - (w + 10 * x)) (g6 : 0 ≤ -x) :
    DU (w + x) x ≤ (w + 10 * x + 1 / 5 * w) ^ 2 / 20 + 3500 := by
  unfold DU; rw [max_eq_right (by linarith : x ≤ 0)]
  linarith [mul_nonneg (mul_nonneg (g0) g5) g5, mul_nonneg (mul_nonneg (g1) g1) g1, mul_nonneg (mul_nonneg (g1) g1) g3, mul_nonneg (mul_nonneg (g1) g1) g5, mul_nonneg (mul_nonneg (g1) g2) g3, mul_nonneg (mul_nonneg (g1) g5) g5, mul_nonneg (mul_nonneg (g2) g3) g3, mul_nonneg (mul_nonneg (g3) g3) g3, mul_nonneg (mul_nonneg (g3) g3) g5, mul_nonneg (mul_nonneg (g5) g5) g5]

theorem DU_sq1_pos {w x : ℝ} (_g0 : 0 ≤ w) (g1 : 0 ≤ x + 10) (g2 : 0 ≤ 10 - x) (g3 : 0 ≤ w + x) (g4 : 0 ≤ w + 10 * x - 400) (g5 : 0 ≤ 800 - (w + 10 * x)) (g6 : 0 ≤ x) :
    DU (w + x) x ≤ (w + 10 * x + 1 / 9 * w) ^ 2 / 20 + 3500 := by
  unfold DU; rw [max_eq_left g6]
  linarith [mul_nonneg (mul_nonneg (g1) g1) g2, mul_nonneg (mul_nonneg (g1) g2) g3, mul_nonneg (mul_nonneg (g1) g2) g4, mul_nonneg (mul_nonneg (g1) g5) g5, mul_nonneg (mul_nonneg (g2) g2) g3, mul_nonneg (mul_nonneg (g2) g3) g3, mul_nonneg (mul_nonneg (g3) g3) g4, mul_nonneg (mul_nonneg (g3) g3) g5, mul_nonneg (mul_nonneg (g3) g5) g5, mul_nonneg (mul_nonneg (g5) g5) g5]

theorem DU_sq1_neg {w x : ℝ} (g0 : 0 ≤ w) (g1 : 0 ≤ x + 10) (g2 : 0 ≤ 10 - x) (g3 : 0 ≤ w + x) (g4 : 0 ≤ w + 10 * x - 400) (g5 : 0 ≤ 800 - (w + 10 * x)) (g6 : 0 ≤ -x) :
    DU (w + x) x ≤ (w + 10 * x + 1 / 9 * w) ^ 2 / 20 + 3500 := by
  unfold DU; rw [max_eq_right (by linarith : x ≤ 0)]
  linarith [mul_nonneg (mul_nonneg (g0) g3) g3, mul_nonneg (mul_nonneg (g0) g3) g4, mul_nonneg (mul_nonneg (g0) g5) g5, mul_nonneg (mul_nonneg (g1) g1) g1, mul_nonneg (mul_nonneg (g1) g1) g3, mul_nonneg (mul_nonneg (g1) g1) g5, mul_nonneg (mul_nonneg (g1) g2) g3, mul_nonneg (mul_nonneg (g1) g3) g3, mul_nonneg (mul_nonneg (g4) g5) g6, mul_nonneg (mul_nonneg (g5) g5) g5]

theorem DU_sq2_pos {w x : ℝ} (g0 : 0 ≤ w) (g1 : 0 ≤ x + 10) (g2 : 0 ≤ 10 - x) (g3 : 0 ≤ w + x) (g4 : 0 ≤ w + 10 * x - 800) (g5 : 0 ≤ 8000 / 9 - (w + 10 * x)) (g6 : 0 ≤ x) :
    DU (w + x) x ≤ (w + 10 * x + 9 / 89 * w) ^ 2 / 20 + 3500 := by
  unfold DU; rw [max_eq_left g6]
  linarith [mul_nonneg (mul_nonneg (g0) g0) g6, mul_nonneg (mul_nonneg (g0) g1) g4, mul_nonneg (mul_nonneg (g1) g1) g5, mul_nonneg (mul_nonneg (g1) g2) g3, mul_nonneg (mul_nonneg (g1) g2) g6, mul_nonneg (mul_nonneg (g1) g5) g5, mul_nonneg (mul_nonneg (g2) g2) g3, mul_nonneg (mul_nonneg (g2) g3) g5, mul_nonneg (mul_nonneg (g3) g3) g4, mul_nonneg (mul_nonneg (g5) g5) g5]

theorem DU_sq2_neg {w x : ℝ} (_g0 : 0 ≤ w) (g1 : 0 ≤ x + 10) (g2 : 0 ≤ 10 - x) (g3 : 0 ≤ w + x) (g4 : 0 ≤ w + 10 * x - 800) (g5 : 0 ≤ 8000 / 9 - (w + 10 * x)) (g6 : 0 ≤ -x) :
    DU (w + x) x ≤ (w + 10 * x + 9 / 89 * w) ^ 2 / 20 + 3500 := by
  unfold DU; rw [max_eq_right (by linarith : x ≤ 0)]
  linarith [mul_nonneg (mul_nonneg (g1) g1) g1, mul_nonneg (mul_nonneg (g1) g1) g3, mul_nonneg (mul_nonneg (g1) g2) g3, mul_nonneg (mul_nonneg (g1) g2) g4, mul_nonneg (mul_nonneg (g1) g5) g5, mul_nonneg (mul_nonneg (g2) g3) g3, mul_nonneg (mul_nonneg (g3) g3) g3, mul_nonneg (mul_nonneg (g3) g3) g4, mul_nonneg (mul_nonneg (g5) g5) g5]

/-! ### Thresholds for a non-maximal braking tick -/

theorem fU_lin {ε : ℝ} (h : |ε| ≤ 1000) : fU ε = ε / 10 := by
  unfold fU; rw [ite_eq_left h]
  unfold clampY
  have := abs_le.mp (le_refl |ε|)
  rcases le_total 0 ε with h0 | h0
  · rw [abs_of_nonneg h0]; rw [min_eq_right (by linarith), max_eq_right (by linarith)]
  · rw [abs_of_nonpos h0]; rw [min_eq_right (by linarith), max_eq_right (by linarith)]

/-- `v ≤ max(−VsU, fU ε + cU)`. -/
theorem vU_le_max (θ ε w : ℝ) : vU θ ε w ≤ max (-VsU) (fU ε + cU θ ε w) := by
  unfold vU
  exact le_trans clampY_le_max (max_le (le_max_left _ _) clampY_le_max)

/-- If the target is at least `x > −10`, then `v ≥ w + 10 x` and `v ≤ fU ε + cU`. -/
theorem tU_ge_v {θ ε w x : ℝ} (hw : 0 ≤ w) (hx : -10 < x) (hxt : x ≤ tU θ ε w) :
    w + 10 * x ≤ vU θ ε w ∧ vU θ ε w ≤ fU ε + cU θ ε w := by
  have h1 : x ≤ (vU θ ε w - w) / 10 := by
    have := le_trans hxt (clampY_le_max (l := -10) (h := 10))
    rcases le_total (-10) ((vU θ ε w - w) / 10) with h | h
    · rw [max_eq_right h] at this; exact this
    · rw [max_eq_left h] at this; linarith
  refine ⟨by linarith, ?_⟩
  have h2 := vU_le_max θ ε w
  rcases le_total (-VsU) (fU ε + cU θ ε w) with h | h
  · rw [max_eq_right h] at h2; exact h2
  · rw [max_eq_left h] at h2; norm_num [VsU] at h2; linarith

theorem tU_lin_thr {θ ε w x : ℝ} (hε : |ε| ≤ 1000) (hw : 0 ≤ w) (hx : -10 < x)
    (hxt : x ≤ tU θ ε w) : 100 * x + 10 * w ≤ ε := by
  obtain ⟨h1, h2⟩ := tU_ge_v hw hx hxt
  rw [fU_lin hε] at h2
  have hc : cU θ ε w ≤ 0 := by
    unfold cU; split_ifs
    · linarith
    · nlinarith [div_nonneg (by norm_num : (0:ℝ) ≤ 100) (abs_nonneg (fU ε))]
  linarith

theorem tU_sqrt_thr {θ ε w x : ℝ} (hε : 1000 < ε) (hw : 0 ≤ w) (hx : -10 < x)
    (hxt : x ≤ tU θ ε w) :
    w + 10 * x ≤ VsU ∧
      ((w + 10 * x) * fU ε + 100 * w ≤ fU ε ^ 2 ∨ (fU ε * w < θ ∧ w + 10 * x ≤ fU ε)) := by
  obtain ⟨h1, h2⟩ := tU_ge_v hw hx hxt
  refine ⟨le_trans h1 (vU_le θ ε w), ?_⟩
  obtain ⟨-, hF⟩ := fU_big hε
  have h1000 : ¬ |ε| ≤ 1000 := by rw [abs_of_pos (by linarith)]; linarith
  unfold cU at h2
  by_cases hσ : θ ≤ fU ε * w
  · rw [ite_eq_left hσ, ite_eq_right h1000, abs_of_pos (by linarith : (0:ℝ) < fU ε)] at h2
    left
    have hF0 : 0 < fU ε := by linarith
    have : (w + 10 * x) * fU ε ≤ (fU ε + -(100 / fU ε) * w) * fU ε :=
      mul_le_mul_of_nonneg_right (le_trans h1 h2) hF0.le
    have e : (fU ε + -(100 / fU ε) * w) * fU ε = fU ε ^ 2 - 100 * w := by field_simp; ring
    linarith
  · rw [ite_eq_right hσ] at h2
    right; exact ⟨lt_of_not_ge hσ, by linarith⟩

theorem tU_negzone {θ ε w : ℝ} (hθ : 0 < θ) (hε : ε < -1000) (hw : 0 ≤ w) : tU θ ε w ≤ -10 := by
  have hf : fU ε ≤ -100 := by
    have := (fU_big (by linarith : (1000:ℝ) < -ε)).2
    rw [fU_neg] at this; linarith
  have hc : cU θ ε w = 0 := by
    unfold cU; rw [ite_eq_right]; intro h; nlinarith
  have hv : vU θ ε w ≤ -100 := by
    have := vU_le_max θ ε w; rw [hc, add_zero] at this
    exact le_trans this (max_le (by norm_num [VsU]) hf)
  unfold tU
  refine le_trans clampY_le_max (max_le le_rfl ?_)
  linarith

/-- The jerk-limited step is at least the maximal-braking step, and either equals it or is at
most the target. -/
theorem jstep_cases {a t : ℝ} (ha : -10 ≤ a) (ht : -10 ≤ t) :
    max (a - 1) (-10) ≤ a + clampY (-1) 1 (t - a) ∧
      (a + clampY (-1) 1 (t - a) = max (a - 1) (-10) ∨ a + clampY (-1) 1 (t - a) ≤ t) := by
  rcases clampY_cases (L := 1) (x := t - a) (by norm_num) with ⟨hc, hc'⟩ | ⟨hc, hc1, hc2⟩ | ⟨hc, hc'⟩ <;>
    rw [hc]
  · refine ⟨max_le (by linarith) (by linarith), Or.inl ?_⟩
    rw [max_eq_left (by linarith)]; ring
  · exact ⟨max_le (by linarith) (by linarith), Or.inr (by linarith)⟩
  · exact ⟨max_le (by linarith) (by linarith), Or.inr (by linarith)⟩

/-! ### The overshoot invariant -/

/-- One half of the overshoot invariant. -/
def Hd (Mu Ml : ℝ) (s : YawState) : Prop :=
  s.e ≤ Mu ∧ s.α ≤ 10 ∧ s.ω + max s.α 0 ^ 2 / 2 ≤ VsU ∧
    (1000 < s.e → 0 ≤ s.ω → min s.α 0 ^ 2 ≤ 2 * s.ω) ∧
    (0 ≤ s.ω → -Ml ≤ s.e - DU s.ω s.α)

def InvD (Mu Ml : ℝ) (s : YawState) : Prop := Hd Mu Ml s ∧ Hd Ml Mu (negS s)

/-- The new stopping point after a tick with `w ≥ 0` that ends with `w' ≥ 0`. -/
theorem stop_step {θ e w a Ml : ℝ} (hθ : 0 < θ) (hθ1 : θ ≤ 1 / 10) (hMl : 3000 ≤ Ml)
    (hw : 0 ≤ w) (ha1 : -10 ≤ a) (ha2 : a ≤ 10) (hK : -Ml ≤ e - DU w a)
    (hw' : 0 ≤ w + aU θ (e - w) w a) :
    -Ml ≤ (e - w) - DU (w + aU θ (e - w) w a) (aU θ (e - w) w a) := by
  set t := tU θ (e - w) w with ht
  set x := aU θ (e - w) w a with hx
  have hxdef : x = a + clampY (-1) 1 (t - a) := rfl
  obtain ⟨ht1, ht2⟩ := tU_bounds θ (e - w) w
  obtain ⟨hmb, hcase⟩ := jstep_cases ha1 ht1
  rw [← hxdef] at hmb hcase
  obtain ⟨hx1, hx2⟩ := jstep_bounds ha1 ha2 ht1 ht2 (a := a) (t := t)
  rw [← hxdef] at hx1 hx2
  have hmax : ∀ y : ℝ, x = max (a - 1) (-10) → -Ml ≤ (e - w) - DU (w + x) x := by
    intro _ heq
    rcases le_total (-9) a with h9 | h9
    · rw [max_eq_left (by linarith)] at heq
      rw [heq] at hw' ⊢
      have := DU_ramp hw h9 ha2 hw'
      linarith
    · rw [max_eq_right (by linarith)] at heq
      rw [heq] at hw' ⊢
      have := DU_floor h9 (by linarith : 10 ≤ w)
      have e1 : w + -10 = w - 10 := by ring
      rw [e1]; linarith
  rcases hcase with heq | hle
  · exact hmax 0 heq
  by_cases heq : x = max (a - 1) (-10)
  · exact hmax 0 heq
  have hxm : -10 < x := lt_of_le_of_lt (le_max_right _ _) (lt_of_le_of_ne hmb (Ne.symm heq))
  have hg0 : 0 ≤ w := hw
  have hg1 : 0 ≤ x + 10 := by linarith
  have hg2 : 0 ≤ 10 - x := by linarith
  have hg3 : 0 ≤ w + x := hw'
  rcases lt_or_ge (e - w) (-1000) with hz | hz
  · exfalso; have := tU_negzone hθ hz hw; linarith
  rcases le_or_gt (e - w) 1000 with hz' | hz'
  · -- linear zone
    have habs : |e - w| ≤ 1000 := abs_le.mpr ⟨hz, hz'⟩
    have hth := tU_lin_thr habs hw hxm hle
    have hg4 : 0 ≤ 1000 - 100 * x - 10 * w := by linarith
    have hg5 : 0 ≤ 100 * x + 10 * w + 1000 := by linarith
    have hD : DU (w + x) x ≤ 100 * x + 10 * w + 3000 := by
      rcases le_total 0 x with hx0 | hx0
      · exact DU_lin_pos hg0 hg1 hg2 hg3 hg4 hg5 hx0
      · exact DU_lin_neg hg0 hg1 hg2 hg3 hg4 hg5 (by linarith)
    linarith
  · -- positive sqrt zone
    obtain ⟨hb, hcases⟩ := tU_sqrt_thr hz' hw hxm hle
    obtain ⟨hF, hF100⟩ := fU_big hz'
    have hFsq : fU (e - w) ^ 2 = 20 * ((e - w) - 500) := by
      rw [hF, Real.sq_sqrt (by linarith)]
    set F := fU (e - w)
    have hVs : VsU = 8000 / 9 := rfl
    rcases hcases with hC | ⟨hσ, -⟩
    · rcases lt_or_ge (w + 10 * x) 0 with hb0 | hb0
      · have : DU (w + x) x ≤ 4000 := DU_bneg hg0 hg1 (by linarith) hg3 (by linarith)
        linarith
      have hFpos : 0 < F := by linarith
      -- F ≥ b + c w on a piece `b ≤ B` with `c = 100 / (B + 100)`
      have piece : ∀ c B : ℝ, 0 ≤ c → c * (B + 100) = 100 → w + 10 * x ≤ B →
          w + 10 * x + c * w ≤ F := by
        intro c B hc hcB hbB
        have hwB : c * w ≤ 100 := by rw [← hcB]; exact mul_le_mul_of_nonneg_left (by linarith) hc
        have h100 : 0 ≤ 100 - c * (w + 10 * x + c * w) := by
          have : c * (w + 10 * x) ≤ c * B := mul_le_mul_of_nonneg_left hbB hc
          have : c * (c * w) ≤ c * 100 := mul_le_mul_of_nonneg_left hwB hc
          nlinarith
        have key : (F - (w + 10 * x + c * w)) * (F + (w + 10 * x + c * w) - (w + 10 * x)) =
            (F ^ 2 - ((w + 10 * x) * F + 100 * w)) + w * (100 - c * (w + 10 * x + c * w)) := by ring
        have hk : 0 ≤ (F - (w + 10 * x + c * w)) * (F + (w + 10 * x + c * w) - (w + 10 * x)) := by
          rw [key]; exact add_nonneg (by linarith) (mul_nonneg hw h100)
        by_contra hlt
        rw [not_le] at hlt
        have := mul_neg_of_neg_of_pos (sub_neg.mpr hlt) (by nlinarith : 0 < F + (w + 10 * x + c * w) - (w + 10 * x))
        linarith
      rcases le_total (w + 10 * x) 400 with hp | hp
      · have hl := piece (1 / 5) 400 (by norm_num) (by norm_num) hp
        have hsq : (w + 10 * x + 1 / 5 * w) ^ 2 ≤ F ^ 2 := pow_le_pow_left₀ (by linarith) hl 2
        have : DU (w + x) x ≤ (w + 10 * x + 1 / 5 * w) ^ 2 / 20 + 3500 := by
          rcases le_total 0 x with hx0 | hx0
          · exact DU_sq0_pos hg0 hg1 hg2 hg3 (by linarith) (by linarith) hx0
          · exact DU_sq0_neg hg0 hg1 hg2 hg3 (by linarith) (by linarith) (by linarith)
        linarith
      rcases le_total (w + 10 * x) 800 with hp2 | hp2
      · have hl := piece (1 / 9) 800 (by norm_num) (by norm_num) hp2
        have hsq : (w + 10 * x + 1 / 9 * w) ^ 2 ≤ F ^ 2 := pow_le_pow_left₀ (by linarith) hl 2
        have : DU (w + x) x ≤ (w + 10 * x + 1 / 9 * w) ^ 2 / 20 + 3500 := by
          rcases le_total 0 x with hx0 | hx0
          · exact DU_sq1_pos hg0 hg1 hg2 hg3 (by linarith) (by linarith) hx0
          · exact DU_sq1_neg hg0 hg1 hg2 hg3 (by linarith) (by linarith) (by linarith)
        linarith
      · have hb' : w + 10 * x ≤ 8000 / 9 := by rw [hVs] at hb; exact hb
        have hl := piece (9 / 89) (8000 / 9) (by norm_num) (by norm_num) hb'
        have hsq : (w + 10 * x + 9 / 89 * w) ^ 2 ≤ F ^ 2 := pow_le_pow_left₀ (by linarith) hl 2
        have : DU (w + x) x ≤ (w + 10 * x + 9 / 89 * w) ^ 2 / 20 + 3500 := by
          rcases le_total 0 x with hx0 | hx0
          · exact DU_sq2_pos hg0 hg1 hg2 hg3 (by linarith) (by linarith) hx0
          · exact DU_sq2_neg hg0 hg1 hg2 hg3 (by linarith) (by linarith) (by linarith)
        linarith
    · -- tiny rate
      have hwt : w ≤ 1 / 1000 := by
        have : 100 * w ≤ F * w := mul_le_mul_of_nonneg_right hF100.le hw
        linarith
      have : DU (w + x) x ≤ 4000 := by
        rcases le_total 0 x with hx0 | hx0
        · exact DU_tiny_pos hg0 (by linarith) hg1 hg2 hg3 hx0
        · exact DU_tiny_neg hg0 (by linarith) hg1 hg2 hg3 (by linarith)
      linarith

theorem Hd_step {θ Mu Ml : ℝ} {s : YawState} (hθ : 0 < θ) (hθ1 : θ ≤ 1 / 10) (_hMu : 3000 ≤ Mu)
    (hMl : 3000 ≤ Ml) (h1 : Hd Mu Ml s) (h2 : Hd Ml Mu (negS s)) : Hd Mu Ml (tickU θ s) := by
  obtain ⟨e, w, a⟩ := s
  simp only [Hd, negS] at h1 h2
  obtain ⟨he1, ha1, hW1, hR1, hK1⟩ := h1
  obtain ⟨he2, ha2, hW2, hR2, hK2⟩ := h2
  have hV : VsU = 8000 / 9 := rfl
  have hq1 := sq_nonneg (max a 0)
  have hq2 := sq_nonneg (max (-a) 0)
  have hwV : w ≤ VsU := by linarith
  have hwV' : -w ≤ VsU := by linarith
  set t := tU θ (e - w) w with ht
  set x := aU θ (e - w) w a with hx
  have hxdef : x = a + clampY (-1) 1 (t - a) := rfl
  obtain ⟨ht1, ht2⟩ := tU_bounds θ (e - w) w
  have ht3 : t ≤ (VsU - w) / 10 := tU_le_V (by linarith)
  obtain ⟨hx1, hx2⟩ := jstep_bounds (by linarith) ha1 ht1 ht2 (t := t) (a := a)
  rw [← hxdef] at hx1 hx2
  have hWn : w + x + max x 0 ^ 2 / 2 ≤ VsU := by
    rw [hV] at hW1 ht3 ⊢; exact Wc_step hW1 (by linarith) ha1 ht3 ht2 hxdef
  simp only [Hd, tickU]
  rw [← hx]
  refine ⟨?_, hx2, hWn, ?_, ?_⟩
  · -- e' ≤ Mu
    rcases le_or_gt 0 w with hw | hw
    · linarith
    · have := hK2 (by linarith)
      have := DU_ge (by linarith : 0 ≤ -w) (by linarith : -10 ≤ -a)
      linarith
  · -- sqrt zone safety
    intro hε hw'
    rcases le_or_gt 0 w with hw | hw
    · have hR := hR1 (by linarith) hw
      have := tU_sqrt (θ := θ) hε hw
      exact (Rs_step hw hR (by linarith) ht1 this hxdef).2
    · have : 0 ≤ x := by linarith
      rw [min_eq_right this]; linarith
  · -- the stopping point
    intro hw'
    rcases le_or_gt 0 w with hw | hw
    · exact stop_step hθ hθ1 hMl hw (by linarith) ha1 (hK1 hw) hw'
    · have hxpos : 0 < x := by linarith
      rcases lt_or_ge (e - w) (-1000) with hb | hb
      · exfalso
        have hR := hR2 (by linarith) (by linarith)
        have hts := tU_sqrt (θ := θ) (ε := -(e - w)) (w := -w) (by linarith) (by linarith)
        rw [tU_neg] at hts
        have hx' : -x = -a + clampY (-1) 1 (-t - -a) := by
          rw [hxdef, show -t - -a = -(t - a) by ring, clampY_neg (by norm_num)]; ring
        have := Rs_step (by linarith) hR (by linarith) (by linarith) (by rw [← ht] at hts; linarith) hx'
        obtain ⟨h3, h4⟩ := this
        rw [min_eq_left (by linarith : -x ≤ 0)] at h4
        have h5 : (-x) ^ 2 ≤ 0 := le_trans h4 (by linarith)
        have h6 : 0 < x ^ 2 := pow_pos hxpos 2
        rw [neg_sq] at h5
        linarith
      · have := DU_flip hw' (by linarith : 0 ≤ x - (w + x)) (by linarith : 0 ≤ 10 - x)
        linarith

theorem InvD_step {θ Mu Ml : ℝ} {s : YawState} (hθ : 0 < θ) (hθ1 : θ ≤ 1 / 10) (hMu : 3000 ≤ Mu)
    (hMl : 3000 ≤ Ml) (h : InvD Mu Ml s) : InvD Mu Ml (tickU θ s) := by
  refine ⟨Hd_step hθ hθ1 hMu hMl h.1 h.2, ?_⟩
  rw [← tickU_neg]
  exact Hd_step hθ hθ1 hMl hMu h.2 (by rw [negS_negS]; exact h.1)

theorem InvD_traj {θ Mu Ml : ℝ} {s : YawState} (hθ : 0 < θ) (hθ1 : θ ≤ 1 / 10) (hMu : 3000 ≤ Mu)
    (hMl : 3000 ≤ Ml) (h : InvD Mu Ml s) : ∀ t, InvD Mu Ml (trajU θ s t) := by
  intro t; induction t with
  | zero => exact h
  | succ n ih => exact InvD_step hθ hθ1 hMu hMl ih

theorem InvD_bounds {Mu Ml : ℝ} {s : YawState} (h : InvD Mu Ml s) : -Ml ≤ s.e ∧ s.e ≤ Mu ∧
    |s.α| ≤ 10 ∧ |s.ω| ≤ VsU := by
  obtain ⟨⟨h1, h2, h3, -, -⟩, ⟨h1', h2', h3', -, -⟩⟩ := h
  simp only [negS] at h1' h2' h3'
  have := sq_nonneg (max s.α 0); have := sq_nonneg (max (-s.α) 0)
  refine ⟨by linarith, h1, abs_le.mpr ⟨by linarith, h2⟩, abs_le.mpr ⟨by linarith, by linarith⟩⟩

theorem InvD_init {Mu Ml ε₀ a₀ : ℝ} (he : 0 < ε₀) (hM : ε₀ ≤ Mu) (hMl : 3000 ≤ Ml) (ha0 : 0 ≤ a₀)
    (ha1 : a₀ ≤ 10) : InvD Mu Ml ⟨ε₀, 0, a₀⟩ := by
  have hV : VsU = 8000 / 9 := rfl
  refine ⟨⟨hM, ha1, ?_, fun _ _ => ?_, fun _ => ?_⟩,
    ⟨by simp only [negS]; linarith, by simp only [negS]; linarith, ?_,
      fun h _ => by simp only [negS] at h; linarith, ?_⟩⟩
  · simp only; rw [max_eq_left ha0, hV]; nlinarith
  · simp only; rw [min_eq_right ha0]; norm_num
  · simp only [DU]; rw [max_eq_left ha0]
    nlinarith [pow_le_pow_left₀ ha0 ha1 3, pow_le_pow_left₀ ha0 ha1 2]
  · simp only [negS]; rw [max_eq_right (by linarith : -a₀ ≤ 0), hV]; norm_num
  · intro _; simp only [negS, DU]; rw [max_eq_right (by linarith : -a₀ ≤ 0)]; ring_nf; linarith

/-- Re-anchoring the upper bound at a state in the sqrt zone moving toward 0. -/
theorem InvD_reanchor {Mu Ml : ℝ} {s : YawState} (h : InvD Mu Ml s) (hMl : 0 ≤ Ml) (he : 1000 < s.e)
    (hw : 0 ≤ s.ω) : InvD (max s.e 3000) Ml s := by
  obtain ⟨⟨h1, h2, h3, h4, h5⟩, ⟨h1', h2', h3', h4', h5'⟩⟩ := h
  simp only [negS] at h1' h2' h3' h4' h5'
  have hR := h4 he hw
  refine ⟨⟨le_max_left _ _, h2, h3, h4, h5⟩,
    ⟨by simp only [negS]; linarith, h2', h3', fun h _ => by simp only [negS] at h; linarith, ?_⟩⟩
  intro hw'
  simp only [negS] at hw' ⊢
  have hw0 : s.ω = 0 := by linarith
  rw [hw0] at hR
  have ha : 0 ≤ s.α := by
    by_contra hc; rw [not_le] at hc; rw [min_eq_left hc.le] at hR; nlinarith
  simp only [DU]; rw [hw0, max_eq_right (by linarith : -s.α ≤ 0)]
  ring_nf
  linarith [le_max_left s.e 3000]

end Contracts.Track.YawPhase
