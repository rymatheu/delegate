import Mathlib

/-!
# Y5, the yaw phase lemma: the scaled model

The yaw axis of `attitude_command_model` (desired rate 0, `ATC_ACC_Y_MAX = 270°/s²`,
`ATC_RATE_WPY_MAX = 60°/s`, `input_tc = 10·dt`), written in the units

  `ε = e / (h²J)`, `w = ω / (hJ)`, `a = α / J`  (`h = 1/400`, `J = 3π/20` the jerk step per tick),

in which every constant is rational: the acceleration limit is `10`, the jerk step `1`, the slew
`8000/9`, `k_v·h = 1/10`, the linear distance `1000`, and the sqrt controller is
`√(20 (|ε| − 500))`. Only the `is_positive` threshold of `sqrt_controller_accel` keeps a
parameter `θ > 0` (`θ = 2⁻²³/(hJ)²` for the real model, `AttitudeYawPhase.lean`).

This file has the scaled step `tickU` (odd: `tickU_neg`), bounds on its acceleration target
`tU` (`tU_bounds`, `tU_le_V`, the sqrt zone `tU_sqrt`, the slew zone `tU_slew`), and the
two-dimensional facts about the jerk-limited step `a' = a + clamp(t − a, ±1)`, `w' = w + a'`:

* `Wc_step`: `w + max(a,0)²/2 ≤ 8000/9` is preserved when `t ≤ (8000/9 − w)/10`: the rate never
  exceeds the slew;
* `Rs_step`: the jerk reserve `w ≥ 0 ∧ min(a,0)² ≤ 2w` is preserved when `t ≥ 10 − w/5`, the bound
  in the sqrt zone: the rate keeps its sign there (`traj_sqrt_mono`).

The overshoot invariant is in `AttitudeYawPhaseOvershoot.lean`.
-/

noncomputable section
namespace Contracts.Track.YawPhase

def clampY (l h x : ℝ) : ℝ := max l (min h x)

theorem clampY_cases {L x : ℝ} (hL : 0 ≤ L) :
    (clampY (-L) L x = -L ∧ x ≤ -L) ∨ (clampY (-L) L x = x ∧ -L ≤ x ∧ x ≤ L) ∨
      (clampY (-L) L x = L ∧ L ≤ x) := by
  unfold clampY
  rcases le_total x (-L) with h | h
  · left; refine ⟨?_, h⟩; rw [min_eq_right (by linarith), max_eq_left h]
  · rcases le_total x L with h' | h'
    · right; left; exact ⟨by rw [min_eq_right h', max_eq_right h], h, h'⟩
    · right; right; exact ⟨by rw [min_eq_left h', max_eq_right (by linarith)], h'⟩

theorem clampY_neg {L : ℝ} (hL : 0 ≤ L) (x : ℝ) : clampY (-L) L (-x) = -clampY (-L) L x := by
  simp only [clampY, max_def, min_def]; split_ifs <;> linarith

theorem clampY_mul {c : ℝ} (hc : 0 ≤ c) (l h x : ℝ) : clampY (c * l) (c * h) (c * x) = c * clampY l h x := by
  simp only [clampY, mul_max_of_nonneg _ _ hc, mul_min_of_nonneg _ _ hc]

theorem clampY_mono {l h x y : ℝ} (hxy : x ≤ y) : clampY l h x ≤ clampY l h y :=
  max_le_max le_rfl (min_le_min le_rfl hxy)

theorem clampY_le' {l h x : ℝ} (hlh : l ≤ h) : clampY l h x ≤ h := max_le hlh (min_le_left _ _)
theorem le_clampY' {l h x : ℝ} : l ≤ clampY l h x := le_max_left _ _
theorem clampY_le_max {l h x : ℝ} : clampY l h x ≤ max l x := max_le_max le_rfl (min_le_right _ _)
theorem min_le_clampY {l h x : ℝ} : min h x ≤ clampY l h x := by
  unfold clampY; exact le_max_right _ _

/-- the jerk-limited step stays in `[-10, 10]`. -/
theorem jstep_bounds {a t : ℝ} (ha1 : -10 ≤ a) (ha2 : a ≤ 10) (ht1 : -10 ≤ t) (ht2 : t ≤ 10) :
    -10 ≤ a + clampY (-1) 1 (t - a) ∧ a + clampY (-1) 1 (t - a) ≤ 10 := by
  rcases clampY_cases (L := 1) (x := t - a) (by norm_num) with ⟨hc, hc'⟩ | ⟨hc, hc1, hc2⟩ | ⟨hc, hc'⟩ <;>
    rw [hc] <;> constructor <;> linarith

theorem jstep_lower {a t : ℝ} (ha1 : -10 ≤ a) (ht1 : -10 ≤ t) :
    -10 ≤ a + clampY (-1) 1 (t - a) := by
  rcases clampY_cases (L := 1) (x := t - a) (by norm_num) with ⟨hc, hc'⟩ | ⟨hc, hc1, hc2⟩ | ⟨hc, hc'⟩ <;>
    rw [hc] <;> linarith

theorem Wc_step {w a t x : ℝ} (hW : w + max a 0 ^ 2 / 2 ≤ 8000 / 9) (ha1 : -10 ≤ a) (ha2 : a ≤ 10)
    (ht : t ≤ (8000 / 9 - w) / 10) (ht2 : t ≤ 10) (hx : x = a + clampY (-1) 1 (t - a)) :
    w + x + max x 0 ^ 2 / 2 ≤ 8000 / 9 := by
  have hq : 0 ≤ max a 0 ^ 2 := sq_nonneg _
  have hpa : a ≤ max a 0 := le_max_left _ _
  rcases clampY_cases (L := 1) (x := t - a) (by norm_num) with ⟨hc, hc'⟩ | ⟨hc, hc1, hc2⟩ | ⟨hc, hc'⟩ <;>
    rw [hc] at hx <;> subst hx
  · rcases le_total (a + -1) 0 with h1 | h1
    · rw [max_eq_right h1]; linarith
    · rw [max_eq_left h1]; rw [max_eq_left (by linarith : (0:ℝ) ≤ a)] at hW; nlinarith
  · have : a + (t - a) = t := by ring
    rw [this]
    rcases le_total t 0 with h1 | h1
    · rw [max_eq_right h1]; linarith
    · rw [max_eq_left h1]; nlinarith
  · rcases le_total (a + 1) 0 with h1 | h1
    · rw [max_eq_right h1]; linarith
    · rw [max_eq_left h1]; nlinarith

theorem Rs_step {w a t x : ℝ} (hw : 0 ≤ w) (hR : min a 0 ^ 2 ≤ 2 * w) (ha1 : -10 ≤ a)
    (ht1 : -10 ≤ t) (ht2 : 10 - w / 5 ≤ t) (hx : x = a + clampY (-1) 1 (t - a)) :
    0 ≤ w + x ∧ min x 0 ^ 2 ≤ 2 * (w + x) := by
  rcases clampY_cases (L := 1) (x := t - a) (by norm_num) with ⟨hc, hc'⟩ | ⟨hc, hc1, hc2⟩ | ⟨hc, hc'⟩ <;>
    rw [hc] at hx <;> subst hx
  · -- x = a - 1 ≥ t
    rcases le_total (a + -1) 0 with h1 | h1
    · rw [min_eq_left h1]; constructor <;> nlinarith
    · rw [min_eq_right h1]; constructor <;> linarith
  · have : a + (t - a) = t := by ring
    rw [this]
    rcases le_total t 0 with h1 | h1
    · rw [min_eq_left h1]; constructor <;> nlinarith
    · rw [min_eq_right h1]; constructor <;> linarith
  · rcases le_total a 0 with h0 | h0
    · rw [min_eq_left h0] at hR
      rcases le_total (a + 1) 0 with h1 | h1
      · rw [min_eq_left h1]; constructor <;> nlinarith
      · rw [min_eq_right h1]; constructor <;> linarith
    · rw [min_eq_right (by linarith : (0:ℝ) ≤ a + 1)]; constructor <;> linarith


/-! ## scaled model -/

def VsU : ℝ := 8000 / 9

structure YawState where
  e : ℝ
  ω : ℝ
  α : ℝ

def negS (s : YawState) : YawState := ⟨-s.e, -s.ω, -s.α⟩

def fU (ε : ℝ) : ℝ :=
  clampY (-|ε|) |ε|
    (if |ε| ≤ 1000 then ε / 10 else if 0 < ε then √(20 * (ε - 500)) else -√(20 * (-ε - 500)))

def cU (θ ε w : ℝ) : ℝ :=
  if θ ≤ fU ε * w then (if |ε| ≤ 1000 then -w else -(100 / |fU ε|) * w) else 0

def vU (θ ε w : ℝ) : ℝ := clampY (-VsU) VsU (clampY (-VsU) VsU (fU ε + cU θ ε w))

def tU (θ ε w : ℝ) : ℝ := clampY (-10) 10 ((vU θ ε w - w) / 10)

def aU (θ ε w a : ℝ) : ℝ := a + clampY (-1) 1 (tU θ ε w - a)

def tickU (θ : ℝ) (s : YawState) : YawState :=
  ⟨s.e - s.ω, s.ω + aU θ (s.e - s.ω) s.ω s.α, aU θ (s.e - s.ω) s.ω s.α⟩

theorem fU_neg (ε : ℝ) : fU (-ε) = -fU ε := by
  unfold fU
  rw [abs_neg, ← clampY_neg (abs_nonneg ε)]
  congr 1
  by_cases h1 : |ε| ≤ 1000
  · rw [ite_eq_left h1, ite_eq_left h1]; ring
  · rw [ite_eq_right h1, ite_eq_right h1]
    have hne : ε ≠ 0 := by rintro rfl; simp at h1
    rcases lt_or_gt_of_ne hne with h | h
    · rw [ite_eq_left (neg_pos.mpr h), ite_eq_right (not_lt.mpr h.le), neg_neg]
    · rw [ite_eq_right (by linarith : ¬ (0:ℝ) < -ε), ite_eq_left h, neg_neg]

theorem cU_neg (θ ε w : ℝ) : cU θ (-ε) (-w) = -cU θ ε w := by
  unfold cU
  rw [fU_neg, abs_neg, abs_neg, neg_mul_neg]
  split_ifs <;> ring

theorem vU_neg (θ ε w : ℝ) : vU θ (-ε) (-w) = -vU θ ε w := by
  unfold vU
  have hV : (0:ℝ) ≤ VsU := by norm_num [VsU]
  rw [fU_neg, cU_neg, ← neg_add, clampY_neg hV, clampY_neg hV]

theorem tU_neg (θ ε w : ℝ) : tU θ (-ε) (-w) = -tU θ ε w := by
  unfold tU
  rw [vU_neg, show (-vU θ ε w - -w) / 10 = -((vU θ ε w - w) / 10) by ring, clampY_neg (by norm_num)]

theorem aU_neg (θ ε w a : ℝ) : aU θ (-ε) (-w) (-a) = -aU θ ε w a := by
  unfold aU
  rw [tU_neg, show -tU θ ε w - -a = -(tU θ ε w - a) by ring, clampY_neg (by norm_num)]; ring

theorem tickU_neg (θ : ℝ) (s : YawState) : tickU θ (negS s) = negS (tickU θ s) := by
  simp only [tickU, negS, show -s.e - -s.ω = -(s.e - s.ω) by ring, aU_neg]
  congr 1; ring

theorem fU_nonpos {ε : ℝ} (h : ε ≤ 0) : fU ε ≤ 0 := by
  unfold fU
  refine le_trans clampY_le_max (max_le (by linarith [abs_nonneg ε]) ?_)
  split_ifs with h1 h2
  · linarith
  · linarith
  · linarith [Real.sqrt_nonneg (20 * (-ε - 500))]

theorem fU_big {ε : ℝ} (h : 1000 < ε) : fU ε = √(20 * (ε - 500)) ∧ 100 < fU ε := by
  have h1 : ¬ |ε| ≤ 1000 := by rw [abs_of_pos (by linarith)]; linarith
  have hs : √(20 * (ε - 500)) ≤ ε := by
    rw [Real.sqrt_le_left (by linarith)]; nlinarith
  have hs2 : 100 < √(20 * (ε - 500)) := by
    rw [Real.lt_sqrt (by norm_num)]; linarith
  have : fU ε = √(20 * (ε - 500)) := by
    unfold fU
    rw [abs_of_pos (show (0:ℝ) < ε by linarith), ite_eq_right (by linarith), ite_eq_left (by linarith)]
    unfold clampY
    rw [min_eq_right hs, max_eq_right (by linarith)]
  exact ⟨this, this ▸ hs2⟩

theorem tU_bounds (θ ε w : ℝ) : -10 ≤ tU θ ε w ∧ tU θ ε w ≤ 10 :=
  ⟨le_clampY', clampY_le' (by norm_num)⟩

theorem vU_le (θ ε w : ℝ) : vU θ ε w ≤ VsU := clampY_le' (by norm_num [VsU])

theorem tU_le_V {θ ε w : ℝ} (hw : w ≤ VsU + 100) : tU θ ε w ≤ (VsU - w) / 10 := by
  unfold tU
  refine le_trans clampY_le_max (max_le ?_ ?_)
  · linarith
  · linarith [vU_le θ ε w]

/-- the sqrt zone: `ε > 1000`, `w ≥ 0`. -/
theorem tU_sqrt {θ ε w : ℝ} (he : 1000 < ε) (hw : 0 ≤ w) : 10 - w / 5 ≤ tU θ ε w := by
  obtain ⟨hf, hf1⟩ := fU_big he
  have h1 : ¬ |ε| ≤ 1000 := by rw [abs_of_pos (by linarith)]; linarith
  have hc : -w ≤ cU θ ε w := by
    unfold cU
    split_ifs
    · rw [abs_of_pos (by linarith : (0:ℝ) < fU ε)]
      have : 100 / fU ε ≤ 1 := by rw [div_le_one (by linarith)]; linarith
      nlinarith [div_nonneg (by norm_num : (0:ℝ) ≤ 100) (by linarith : (0:ℝ) ≤ fU ε)]
    · linarith
  have hv : 100 - w ≤ vU θ ε w := by
    unfold vU
    refine le_trans ?_ (min_le_clampY)
    refine le_min (by norm_num [VsU]; linarith) ?_
    refine le_trans ?_ (min_le_clampY)
    exact le_min (by norm_num [VsU]; linarith) (by linarith)
  unfold tU
  refine le_trans ?_ min_le_clampY
  exact le_min (by linarith) (by linarith)

/-- the slew zone: `ε ≥ 50000`, `0 ≤ w ≤ VsU`. -/
theorem tU_slew {θ ε w : ℝ} (he : 50000 ≤ ε) (hw : 0 ≤ w) (hwV : w ≤ VsU) : 0 ≤ tU θ ε w := by
  obtain ⟨hf, -⟩ := fU_big (by linarith : (1000:ℝ) < ε)
  have hf2 : 994 < fU ε := by
    rw [hf, Real.lt_sqrt (by norm_num)]; linarith
  have hc : -(100 / fU ε) * VsU ≤ cU θ ε w := by
    unfold cU
    have h1 : ¬ |ε| ≤ 1000 := by rw [abs_of_pos (by linarith)]; linarith
    have hp : 0 ≤ 100 / fU ε := div_nonneg (by norm_num) (by linarith)
    split_ifs
    · rw [abs_of_pos (by linarith : (0:ℝ) < fU ε)]; nlinarith
    · nlinarith
  have hq : 100 / fU ε ≤ 100 / 994 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hf2.le
  have hv : VsU ≤ vU θ ε w := by
    unfold vU
    have : VsU ≤ fU ε + cU θ ε w := by
      have : (100 / fU ε) * VsU ≤ 100 / 994 * VsU := mul_le_mul_of_nonneg_right hq (by norm_num [VsU])
      norm_num [VsU] at *; linarith
    have hid : ∀ x, VsU ≤ x → clampY (-VsU) VsU x = VsU := by
      intro x hx; unfold clampY; rw [min_eq_left hx, max_eq_right (by norm_num [VsU])]
    rw [hid _ this, hid _ le_rfl]
  unfold tU
  refine le_trans ?_ min_le_clampY
  exact le_min (by norm_num) (by linarith)


/-! ## Trajectories -/

theorem negS_negS (s : YawState) : negS (negS s) = s := by
  obtain ⟨e, w, a⟩ := s; simp [negS]

/-- The scaled trajectory. -/
def trajU (θ : ℝ) (s : YawState) : ℕ → YawState
  | 0 => s
  | t + 1 => tickU θ (trajU θ s t)

/-- monotone phase in the sqrt zone. -/
theorem traj_sqrt_mono {θ ε₀ a₀ : ℝ} (ha0 : 0 ≤ a₀) :
    ∀ t, (∀ s ≤ t, 1000 < (trajU θ ⟨ε₀, 0, a₀⟩ s).e) →
      0 ≤ (trajU θ ⟨ε₀, 0, a₀⟩ t).ω ∧ min (trajU θ ⟨ε₀, 0, a₀⟩ t).α 0 ^ 2 ≤ 2 * (trajU θ ⟨ε₀, 0, a₀⟩ t).ω ∧
      -10 ≤ (trajU θ ⟨ε₀, 0, a₀⟩ t).α := by
  intro t; induction t with
  | zero => intro _; simp only [trajU]; rw [min_eq_right ha0]; norm_num; linarith
  | succ n ih =>
    intro hs
    obtain ⟨hw, hR, ha⟩ := ih (fun s hs' => hs s (by omega))
    have he := hs (n + 1) le_rfl
    simp only [trajU, tickU] at he ⊢
    have := tU_sqrt (θ := θ) he hw
    obtain ⟨r1, r2⟩ := Rs_step hw hR ha (tU_bounds _ _ _).1 this rfl
    refine ⟨r1, r2, ?_⟩
    exact jstep_lower ha (tU_bounds _ _ _).1
end Contracts.Track.YawPhase
