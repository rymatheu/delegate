import Contracts.Mission.SubSpec

/-!
# Milestone (c), geometric part: the corner blend stays within the turn check of the polyline

When the navigator blends from leg `A` (direction `u`, ending at the corner `c`) into leg `B`
(direction `v`, starting at `c`), its target is `c - a u + b v`, where `a` is the distance still to go
on `A` and `b` the distance done on `B`. The blend starts only if the configuration at the midpoint of
the remaining time, `-a_m u + b_m v`, is shorter than `WP_RADIUS_M` (`SCurve::advance_target_along_track`);
the switch happens at that midpoint, and the S-curves are monotone, so before the switch `a ≥ a_m`,
`b ≤ b_m` and after it `a ≤ a_m`, `b ≥ b_m`. In both phases the target is within
`‖b_m v - a_m u‖` of `A ∪ B` (`blend_near`).
-/

namespace Contracts.Mission

open Contracts Contracts.STL

noncomputable section

/-- The first phase: still at least `a_m` to go on `A`, at most `b_m` done on `B`. -/
theorem blend_near_first {c u v : P3} (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) {La a b am bm r : ℝ}
    (ha0 : 0 ≤ a) (haL : a ≤ La) (hb0 : 0 ≤ b) (ham0 : 0 ≤ am)
    (hr : ‖bm • v - am • u‖ ≤ r) (ha : am ≤ a) (hb : b ≤ bm) :
    ∃ y ∈ segment ℝ (c - La • u) c, dist (c - a • u + b • v) y ≤ r := by
  set k := inner ℝ u v with hk
  have hk1 : |k| ≤ 1 := by
    have := abs_real_inner_le_norm u v; rw [hu, hv, mul_one] at this; exact this
  have hr0 : 0 ≤ r := (norm_nonneg _).trans hr
  -- `‖b_m v - a_m u‖² = (a_m - b_m k)² + b_m² (1 - k²)`
  have hM : ‖bm • v - am • u‖ ^ 2 = (am - bm * k) ^ 2 + bm ^ 2 * (1 - k ^ 2) := by
    rw [norm_sub_sq_real, norm_smul, norm_smul, inner_smul_left, inner_smul_right, hu, hv,
      real_inner_comm, ← hk]
    simp only [Real.norm_eq_abs, conj_trivial, mul_one, sq_abs]
    ring
  have hR2 : (am - bm * k) ^ 2 + bm ^ 2 * (1 - k ^ 2) ≤ r ^ 2 := by
    rw [← hM]; exact pow_le_pow_left₀ (norm_nonneg _) hr 2
  have hk2 : 0 ≤ 1 - k ^ 2 := by nlinarith [abs_nonneg k, sq_abs k]
  -- the distance from `c - a u + b v` to `c - s u`
  have hd : ∀ s : ℝ, dist (c - a • u + b • v) (c - s • u) ^ 2 =
      (s - a + b * k) ^ 2 + b ^ 2 * (1 - k ^ 2) := by
    intro s
    rw [dist_eq_norm, show c - a • u + b • v - (c - s • u) = (s - a) • u + b • v by
      simp only [sub_smul]; abel]
    rw [norm_add_sq_real, norm_smul, norm_smul, inner_smul_left, inner_smul_right, hu, hv, ← hk]
    simp only [Real.norm_eq_abs, conj_trivial, mul_one, sq_abs]
    ring
  have key : ∀ s : ℝ, (s - a + b * k) ^ 2 + b ^ 2 * (1 - k ^ 2) ≤ r ^ 2 →
      dist (c - a • u + b • v) (c - s • u) ≤ r := by
    intro s h
    rw [← hd] at h
    exact (pow_le_pow_iff_left₀ dist_nonneg hr0 two_ne_zero).1 h
  have hmem : ∀ s : ℝ, 0 ≤ s → s ≤ La → c - s • u ∈ segment ℝ (c - La • u) c := by
    intro s h0 h1
    rcases eq_or_lt_of_le (h0.trans h1) with hL | hL
    · have : s = 0 := by linarith
      subst this; rw [← hL]; simp
    refine ⟨s / La, 1 - s / La, div_nonneg h0 hL.le, by rw [sub_nonneg, div_le_one hL]; exact h1,
      by ring, ?_⟩
    rw [smul_sub, sub_smul, one_smul, smul_smul, div_mul_cancel₀ _ hL.ne']; abel
  have hbb : b ^ 2 * (1 - k ^ 2) ≤ bm ^ 2 * (1 - k ^ 2) :=
    mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hb0 hb 2) hk2
  rcases lt_or_ge (a - b * k) 0 with hs | hs
  · -- the projection falls beyond the corner: take `c`
    refine ⟨c - (0 : ℝ) • u, hmem 0 le_rfl (ha0.trans haL), key 0 ?_⟩
    have hkpos : 0 < b * k := by linarith
    have h1 : b * k ≤ bm * k := by
      have : 0 < k := by
        rcases lt_or_ge 0 k with h | h
        · exact h
        · nlinarith
      exact mul_le_mul_of_nonneg_right hb this.le
    have h2 : (0 - a + b * k) ^ 2 ≤ (am - bm * k) ^ 2 := by nlinarith
    linarith
  rcases le_or_gt (a - b * k) La with hs' | hs'
  · -- the projection is on `A`
    refine ⟨c - (a - b * k) • u, hmem _ hs hs', key _ ?_⟩
    have : (a - b * k - a + b * k) ^ 2 = 0 := by ring
    nlinarith [sq_nonneg (am - bm * k)]
  · -- the projection falls before the start of `A`: take `c - a u`, at distance `b`
    refine ⟨c - a • u, hmem a ha0 haL, key a ?_⟩
    have hkn : b * k < 0 := by linarith
    have : bm * k ≤ 0 := by
      rcases le_or_gt k 0 with h | h
      · exact mul_nonpos_of_nonneg_of_nonpos (hb0.trans hb) h
      · nlinarith
    have h3 : bm ^ 2 ≤ (am - bm * k) ^ 2 + bm ^ 2 * (1 - k ^ 2) := by nlinarith
    have h4 : (a - a + b * k) ^ 2 + b ^ 2 * (1 - k ^ 2) = b ^ 2 := by ring
    rw [h4]
    nlinarith [pow_le_pow_left₀ hb0 hb 2]

/-- The second phase: at most `a_m` to go on `A`, at least `b_m` done on `B`. -/
theorem blend_near_second {c u v : P3} (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) {Lb a b am bm r : ℝ}
    (ha0 : 0 ≤ a) (hb0 : 0 ≤ b) (hbL : b ≤ Lb) (hbm0 : 0 ≤ bm)
    (hr : ‖bm • v - am • u‖ ≤ r) (ha : a ≤ am) (hb : bm ≤ b) :
    ∃ y ∈ segment ℝ c (c + Lb • v), dist (c - a • u + b • v) y ≤ r := by
  have hu' : ‖-v‖ = 1 := by rw [norm_neg, hv]
  have hv' : ‖-u‖ = 1 := by rw [norm_neg, hu]
  have hr' : ‖am • (-u) - bm • (-v)‖ ≤ r := by
    rw [smul_neg, smul_neg, neg_sub_neg]; exact hr
  obtain ⟨y, hy, hd⟩ := blend_near_first (c := c) hu' hv' hb0 hbL ha0 hbm0 hr' hb ha
  refine ⟨y, ?_, ?_⟩
  · rw [segment_symm]; simpa [sub_neg_eq_add] using hy
  · have : c - b • (-v) + a • (-u) = c - a • u + b • v := by simp only [smul_neg]; abel
    rwa [this] at hd

/-- **The blend**: in either phase the target `c - a u + b v` is within `‖b_m v - a_m u‖` of the two
legs. -/
theorem blend_near {c u v : P3} (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) {La Lb a b am bm r : ℝ}
    (ha0 : 0 ≤ a) (haL : a ≤ La) (hb0 : 0 ≤ b) (hbL : b ≤ Lb) (ham0 : 0 ≤ am) (hbm0 : 0 ≤ bm)
    (hr : ‖bm • v - am • u‖ ≤ r) (h : (am ≤ a ∧ b ≤ bm) ∨ (a ≤ am ∧ bm ≤ b)) :
    ∃ y ∈ segment ℝ (c - La • u) c ∪ segment ℝ c (c + Lb • v), dist (c - a • u + b • v) y ≤ r := by
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · obtain ⟨y, hy, hd⟩ := blend_near_first hu hv ha0 haL hb0 ham0 hr h1 h2
    exact ⟨y, Or.inl hy, hd⟩
  · obtain ⟨y, hy, hd⟩ := blend_near_second hu hv ha0 hb0 hbL hbm0 hr h1 h2
    exact ⟨y, Or.inr hy, hd⟩

end

end Contracts.Mission
