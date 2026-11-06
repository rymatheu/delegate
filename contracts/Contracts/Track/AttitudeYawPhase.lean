import Contracts.Track.AttitudeYawPhaseOvershoot

/-!
# Y5: the yaw phase lemma (TRACK_PLAN.md §3.8)

The real-valued model of the yaw axis of `AC_AttitudeControl::attitude_command_model`
(`Translated/AC_Attitude_lib.lean`: `shape_angle_vel_accel` → `shape_pos_vel_accel` with
`limit_total = true`, `sqrt_controller_float4`, `sqrt_controller_accel`, `shape_accel`), with
desired heading rate `0`, `ATC_ACC_Y_MAX = 270°/s²` (`A = 3π/2`), `ATC_RATE_WPY_MAX = 60°/s`
(`V = π/3`), yaw rate time constant `0` so `input_tc = 10·dt`, `dt = h = 1/400`:
`k_v = 1/(10h) = 40`, jerk step per tick `J = A/10 = 3π/20`, linear distance `ld = A/k_v²`.

* `sqrtCtrl e = clamp(φ, ±|e|/h)`, `φ = k_v e` if `|e| ≤ ld`, else `sign(e)·√(2A(|e| − ld/2))`;
* `accelCorr e ω = −k_v ω` (`|e| ≤ ld`) or `−(A/|sqrtCtrl e|)·ω` (else) when
  `sqrtCtrl e · ω ≥ 2⁻²³`, and `0` otherwise;
* `velTarget = clamp(clamp(sqrtCtrl e + accelCorr/k_v, ±V), ±V)`,
  `accTarget = clamp(k_v (velTarget − ω), ±A)`, `accNext = α + clamp(accTarget − α, ±J)`.

**Indexing.** `traj s₀ 0 = s₀ = (e₀, ω₀, α₀)` and `traj s₀ (t+1) = tick (traj s₀ t)`, where
`tick (e, ω, α) = (e', ω + h α', α')`, `e' = e − h ω` (the target heading is first advanced by the
previous rate) and `α' = accNext e' ω α`. So `e_{t+1} = e_t − h ω_t` and
`(ω_{t+1}, α_{t+1}) = step(e_{t+1}, ω_t, α_t)`. From rest (`ω₀ = 0`) `e₁ = e₀`.

## Results (start from rest: `0 < e₀`, `ω₀ = 0`, `0 ≤ α₀ ≤ A`)

* `yaw_bounds`: for all `t`, `−9π/3200 ≤ e_t ≤ max e₀ (9π/3200)`, `|ω_t| ≤ V`, `|α_t| ≤ A`
  (`9π/3200 ≈ 0.00884` rad ≈ 0.51°: the overshoot past the target, and every later excursion,
  is below half a degree).
* `yaw_first_ticks`: `e₁ = e₀`, `ω₁ > 0`, `e₂ < e₀`.
* `yaw_after_two`: for `t ≥ 2`, `e_t ≤ max e₂ (9π/3200)`.
* `yaw_no_wrap`: if `e₀ ≤ π` then `|e_t| < π` for all `t ≥ 2`; if `e₀ < π`, for all `t`.
* `yaw_sqrt_zone_monotone`: while the error has stayed above `ld` (`∀ s ≤ t, ld < e_s`),
  `ω_t ≥ 0` and `e_{t+1} ≤ e_t` (the error moves monotonically toward 0, away from ±π).
* `yaw_slew_rate`: while `e_s ≥ 0.15` (`1 ≤ s ≤ t+1`), `α_{t+1} ≥ 0` and `ω_t ≤ ω_{t+1}`;
  `yaw_slew_decrease`: once `ω_{t₀} ≥ 0.9 V`, `e_{t+1} ≤ e_t − 0.9 V h` for all later `t` in that
  range.

## Corrections to the numerical claims

* (i) as stated ("`ω_t ≥ 0` for every `t` with `e_t ≥ 0`") is false: after the final overshoot the
  error returns above 0 while `ω < 0` (e.g. `e₀ = 1`, `α₀ = 0`: at `t = 591`,
  `e = 5.7·10⁻⁸`, `ω = −2.1·10⁻⁵`); in the linear zone the dead band of `is_positive`
  (`σ = 0` below `2⁻²³`) makes the closed loop underdamped (eigenvalues of modulus `√0.9`), so the
  tail oscillates about 0 forever. Proved here: `ω_t ≥ 0` while the error is in the sqrt zone.
* (iii) as stated (`e_t ≤ e₀`) is false for small `e₀`: the tail exceeds `e₀` by up to
  `2.2·10⁻⁶` (e.g. `e₀ = 10⁻⁹`, `α₀ = 4`). Proved here: `e_t ≤ max e₀ (9π/3200)`.
* (ii) (`e_t ≥ −0.002`; numerically the minimum is `−0.00169`, at `e₀ → 0`, `α₀ = A`) is proved with
  the constant `9π/3200 ≈ 0.00884` instead of `0.002`: `e_t ≥ −9π/3200`.
-/

noncomputable section

namespace Contracts.Track.YawPhase

open Real

/-- Tick length `dt`. -/
def hT : ℝ := 1 / 400
/-- `ATC_ACC_Y_MAX = 270°/s²` in rad/s². -/
def accMax : ℝ := 3 * π / 2
/-- `ATC_RATE_WPY_MAX = 60°/s` in rad/s. -/
def slew : ℝ := π / 3
/-- `k_v = jerk_max / accel_max = 1 / input_tc`, `input_tc = 10 dt`. -/
def kv : ℝ := 40
/-- The jerk step per tick, `jerk_max·dt = (accel_max / input_tc)·dt = accel_max / 10`. -/
def jerkStep : ℝ := 3 * π / 20
/-- `linear_dist = second_ord_lim / p²`. -/
def linDist : ℝ := accMax / kv ^ 2
/-- The `is_positive` threshold (`FLT_EPSILON`). -/
def fltEps : ℝ := 2 ^ (-23 : ℤ)

/-- `sqrt_controller(error, k_v, accel_max, dt)`. -/
def sqrtCtrl (e : ℝ) : ℝ :=
  clampY (-(|e| / hT)) (|e| / hT)
    (if |e| ≤ linDist then kv * e
     else if 0 < e then √(2 * accMax * (e - linDist / 2)) else -√(2 * accMax * (-e - linDist / 2)))

/-- `sqrt_controller_accel(error, vel_corr_cmd, ω, k_v, accel_max)`. -/
def accelCorr (e ω : ℝ) : ℝ :=
  if fltEps ≤ sqrtCtrl e * ω then
    (if |e| ≤ linDist then -kv * ω else -(accMax / |sqrtCtrl e|) * ω)
  else 0

/-- `vel_target` of `shape_pos_vel_accel` (`limit_total = true`, `vel_desired = 0`). -/
def velTarget (e ω : ℝ) : ℝ :=
  clampY (-slew) slew (clampY (-slew) slew (sqrtCtrl e + accelCorr e ω / kv))

/-- `accel_target = constrain((vel_target − vel)·k_v, −accel_max, accel_max)`. -/
def accTarget (e ω : ℝ) : ℝ := clampY (-accMax) accMax (kv * (velTarget e ω - ω))

/-- `shape_accel`: the jerk-limited new acceleration. -/
def accNext (e ω α : ℝ) : ℝ := α + clampY (-jerkStep) jerkStep (accTarget e ω - α)

/-- One tick: advance the heading error by the previous rate, then shape. -/
def tick (s : YawState) : YawState :=
  ⟨s.e - hT * s.ω, s.ω + hT * accNext (s.e - hT * s.ω) s.ω s.α, accNext (s.e - hT * s.ω) s.ω s.α⟩

/-- The trajectory: `traj s₀ 0 = s₀`, `traj s₀ (t+1) = tick (traj s₀ t)`. -/
def traj (s₀ : YawState) : ℕ → YawState
  | 0 => s₀
  | t + 1 => tick (traj s₀ t)

/-! ## The scaling to `AttitudeYawPhaseCore` -/

/-- The rate unit `hJ = 3π/8000`. -/
def uY : ℝ := 3 * π / 8000

theorem uY_pos : 0 < uY := by unfold uY; positivity
theorem hT_pos : 0 < hT := by unfold hT; norm_num
theorem huY_pos : 0 < hT * uY := mul_pos hT_pos uY_pos
theorem jerk_pos : 0 < jerkStep := by unfold jerkStep; positivity

/-- The scaled `is_positive` threshold. -/
def θY : ℝ := fltEps / uY ^ 2

theorem θY_pos : 0 < θY := by unfold θY fltEps; have := uY_pos; positivity

theorem θY_le : θY ≤ 1 / 10 := by
  have hu := uY_pos
  unfold θY fltEps
  rw [div_le_iff₀ (by positivity)]
  have : (3 : ℝ) < π := Real.pi_gt_three
  have h1 : (9 / 8000 : ℝ) ≤ uY := by unfold uY; linarith
  have h2 : (9 / 8000 : ℝ) ^ 2 ≤ uY ^ 2 := pow_le_pow_left₀ (by norm_num) h1 2
  rw [zpow_neg]
  norm_num at h2 ⊢
  linarith

def unsc (s : YawState) : YawState := ⟨hT * uY * s.e, uY * s.ω, jerkStep * s.α⟩

theorem lin_iff (ε : ℝ) : |hT * uY * ε| ≤ linDist ↔ |ε| ≤ 1000 := by
  rw [abs_mul, abs_of_pos huY_pos, show linDist = hT * uY * 1000 by
    unfold linDist accMax kv hT uY; ring]
  exact mul_le_mul_iff_of_pos_left huY_pos

theorem sqrtCtrl_scale (ε : ℝ) : sqrtCtrl (hT * uY * ε) = uY * fU ε := by
  have hu := uY_pos
  unfold sqrtCtrl fU
  rw [show |hT * uY * ε| / hT = uY * |ε| by
      rw [abs_mul, abs_of_pos huY_pos]; unfold hT; field_simp,
    show -(uY * |ε|) = uY * -|ε| by ring, ← clampY_mul hu.le]
  congr 1
  by_cases h1 : |ε| ≤ 1000
  · rw [ite_eq_left ((lin_iff ε).mpr h1), ite_eq_left h1]; unfold kv hT uY; ring
  · rw [ite_eq_right (fun h => h1 ((lin_iff ε).mp h)), ite_eq_right h1]
    have hsq : ∀ X : ℝ, √(uY ^ 2 * X) = uY * √X := fun X => by
      rw [Real.sqrt_mul (sq_nonneg uY), Real.sqrt_sq hu.le]
    by_cases h2 : 0 < ε
    · rw [ite_eq_left (mul_pos huY_pos h2), ite_eq_left h2,
        show 2 * accMax * (hT * uY * ε - linDist / 2) = uY ^ 2 * (20 * (ε - 500)) by
          unfold linDist accMax kv hT uY; ring, hsq]
    · rw [ite_eq_right (fun h => h2 (pos_of_mul_pos_right h huY_pos.le)), ite_eq_right h2,
        show 2 * accMax * (-(hT * uY * ε) - linDist / 2) = uY ^ 2 * (20 * (-ε - 500)) by
          unfold linDist accMax kv hT uY; ring, hsq]
      ring

theorem accelCorr_scale (ε w : ℝ) : accelCorr (hT * uY * ε) (uY * w) = kv * uY * cU θY ε w := by
  have hu := uY_pos
  unfold accelCorr cU
  rw [sqrtCtrl_scale]
  have hc : fltEps ≤ uY * fU ε * (uY * w) ↔ θY ≤ fU ε * w := by
    rw [show uY * fU ε * (uY * w) = fU ε * w * uY ^ 2 by ring, θY, div_le_iff₀ (by positivity)]
  by_cases h : θY ≤ fU ε * w
  · rw [ite_eq_left (hc.mpr h), ite_eq_left h]
    by_cases h1 : |ε| ≤ 1000
    · rw [ite_eq_left ((lin_iff ε).mpr h1), ite_eq_left h1]; ring
    · rw [ite_eq_right (fun h' => h1 ((lin_iff ε).mp h')), ite_eq_right h1, abs_mul, abs_of_pos hu]
      by_cases hf : |fU ε| = 0
      · rw [hf]; simp
      · field_simp; unfold accMax kv uY; ring
  · rw [ite_eq_right (fun h' => h (hc.mp h')), ite_eq_right h]; ring

theorem velTarget_scale (ε w : ℝ) : velTarget (hT * uY * ε) (uY * w) = uY * vU θY ε w := by
  have hu := uY_pos
  unfold velTarget vU
  rw [sqrtCtrl_scale, accelCorr_scale,
    show uY * fU ε + kv * uY * cU θY ε w / kv = uY * (fU ε + cU θY ε w) by unfold kv; ring,
    show slew = uY * VsU by unfold slew uY VsU; ring, show -(uY * VsU) = uY * -VsU by ring,
    clampY_mul hu.le, clampY_mul hu.le]

theorem accTarget_scale (ε w : ℝ) : accTarget (hT * uY * ε) (uY * w) = jerkStep * tU θY ε w := by
  unfold accTarget tU
  rw [velTarget_scale, show kv * (uY * vU θY ε w - uY * w) = jerkStep * ((vU θY ε w - w) / 10) by
      unfold kv uY jerkStep; ring,
    show accMax = jerkStep * 10 by unfold accMax jerkStep; ring,
    show -(jerkStep * 10) = jerkStep * -10 by ring, clampY_mul jerk_pos.le]

theorem accNext_scale (ε w a : ℝ) :
    accNext (hT * uY * ε) (uY * w) (jerkStep * a) = jerkStep * aU θY ε w a := by
  have hJ : ∀ X, clampY (-jerkStep) jerkStep (jerkStep * X) = jerkStep * clampY (-1) 1 X := fun X => by
    have := clampY_mul jerk_pos.le (-1) 1 X; rwa [mul_neg_one, mul_one] at this
  unfold accNext aU
  rw [accTarget_scale, show jerkStep * tU θY ε w - jerkStep * a = jerkStep * (tU θY ε w - a) by ring, hJ]
  ring

theorem tick_scale (s : YawState) : tick (unsc s) = unsc (tickU θY s) := by
  obtain ⟨ε, w, a⟩ := s
  simp only [tick, unsc, tickU]
  rw [show hT * uY * ε - hT * (uY * w) = hT * uY * (ε - w) by ring, accNext_scale]
  have hJu : hT * jerkStep = uY := by unfold hT jerkStep uY; ring
  have hω : uY * w + hT * (jerkStep * aU θY (ε - w) w a) = uY * (w + aU θY (ε - w) w a) := by
    rw [← hJu]; ring
  rw [hω]

theorem traj_scale (s : YawState) (t : ℕ) : traj (unsc s) t = unsc (trajU θY s t) := by
  induction t with
  | zero => rfl
  | succ n ih => simp only [traj, trajU, ih, tick_scale]

theorem trajU_add (θ : ℝ) (s : YawState) (n k : ℕ) : trajU θ (trajU θ s k) n = trajU θ s (n + k) := by
  induction n with
  | zero => simp [trajU]
  | succ m ih => rw [show m + 1 + k = (m + k) + 1 by omega]; simp only [trajU, ih]

/-- The start from rest, in scaled units. -/
def s0U (e₀ α₀ : ℝ) : YawState := ⟨e₀ / (hT * uY), 0, α₀ / jerkStep⟩

theorem unsc_s0U (e₀ α₀ : ℝ) : unsc (s0U e₀ α₀) = ⟨e₀, 0, α₀⟩ := by
  simp only [unsc, s0U, mul_zero]
  rw [mul_div_cancel₀ _ huY_pos.ne', mul_div_cancel₀ _ jerk_pos.ne']

theorem traj_rest (e₀ α₀ : ℝ) (t : ℕ) : traj ⟨e₀, 0, α₀⟩ t = unsc (trajU θY (s0U e₀ α₀) t) := by
  rw [← traj_scale, unsc_s0U]

/-- `9π/3200 = h·hJ·3000`. -/
def Mrad : ℝ := 9 * π / 3200

theorem Mrad_eq : Mrad = hT * uY * 3000 := by unfold Mrad hT uY; ring

theorem Mrad_lt_pi : Mrad < π := by unfold Mrad; linarith [Real.pi_pos]

section rest

variable {e₀ α₀ : ℝ}

theorem s0U_inv (he : 0 < e₀) (ha0 : 0 ≤ α₀) (ha1 : α₀ ≤ accMax) :
    InvD (max (e₀ / (hT * uY)) 3000) 3000 (s0U e₀ α₀) := by
  apply InvD_init (div_pos he huY_pos) (le_max_left _ _) le_rfl (div_nonneg ha0 jerk_pos.le)
  rw [div_le_iff₀ jerk_pos]; unfold accMax jerkStep at *; linarith

theorem invD_rest (he : 0 < e₀) (ha0 : 0 ≤ α₀) (ha1 : α₀ ≤ accMax) (t : ℕ) :
    InvD (max (e₀ / (hT * uY)) 3000) 3000 (trajU θY (s0U e₀ α₀) t) :=
  InvD_traj θY_pos θY_le (le_max_right _ _) le_rfl (s0U_inv he ha0 ha1) t

/-- **Bounds for every tick.** -/
theorem yaw_bounds (he : 0 < e₀) (ha0 : 0 ≤ α₀) (ha1 : α₀ ≤ accMax) (t : ℕ) :
    -(9 * π / 3200) ≤ (traj ⟨e₀, 0, α₀⟩ t).e ∧ (traj ⟨e₀, 0, α₀⟩ t).e ≤ max e₀ (9 * π / 3200) ∧
      |(traj ⟨e₀, 0, α₀⟩ t).ω| ≤ slew ∧ |(traj ⟨e₀, 0, α₀⟩ t).α| ≤ accMax := by
  obtain ⟨h1, h2, h3, h4⟩ := InvD_bounds (invD_rest he ha0 ha1 t)
  rw [traj_rest]
  set s := trajU θY (s0U e₀ α₀) t
  have hk := huY_pos
  have hM : hT * uY * max (e₀ / (hT * uY)) 3000 = max e₀ (9 * π / 3200) := by
    rw [mul_max_of_nonneg _ _ hk.le, mul_div_cancel₀ _ hk.ne', ← Mrad_eq, Mrad]
  simp only [unsc]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [show 9 * π / 3200 = hT * uY * 3000 from Mrad_eq]; nlinarith
  · rw [← hM]; exact mul_le_mul_of_nonneg_left h2 hk.le
  · rw [abs_mul, abs_of_pos uY_pos, show slew = uY * VsU by unfold slew uY VsU; ring]
    exact mul_le_mul_of_nonneg_left h4 uY_pos.le
  · rw [abs_mul, abs_of_pos jerk_pos, show accMax = jerkStep * 10 by unfold accMax jerkStep; ring]
    exact mul_le_mul_of_nonneg_left h3 jerk_pos.le

theorem fU_pos {ε : ℝ} (h : 0 < ε) : 0 < fU ε := by
  unfold fU
  rw [abs_of_pos h]
  refine lt_of_lt_of_le ?_ min_le_clampY
  refine lt_min h ?_
  split_ifs with h1
  · linarith
  · exact Real.sqrt_pos.mpr (by linarith)

/-- From rest the first acceleration is positive. -/
theorem first_rate_pos {θ ε₀ a₀ : ℝ} (hθ : 0 < θ) (he : 0 < ε₀) (ha0 : 0 ≤ a₀) :
    0 < aU θ (ε₀ - 0) 0 a₀ := by
  rw [sub_zero]
  have hc : cU θ ε₀ 0 = 0 := by unfold cU; rw [mul_zero, ite_eq_right (not_le.mpr hθ)]
  have hv : 0 < vU θ ε₀ 0 := by
    unfold vU; rw [hc, add_zero]
    have hf := fU_pos he
    refine lt_of_lt_of_le ?_ min_le_clampY
    refine lt_min (by norm_num [VsU]) ?_
    refine lt_of_lt_of_le ?_ min_le_clampY
    exact lt_min (by norm_num [VsU]) hf
  have ht : 0 < tU θ ε₀ 0 := by
    unfold tU; rw [sub_zero]
    refine lt_of_lt_of_le ?_ min_le_clampY
    exact lt_min (by norm_num) (by linarith)
  unfold aU
  rcases clampY_cases (L := 1) (x := tU θ ε₀ 0 - a₀) (by norm_num) with ⟨hc, hc'⟩ | ⟨hc, hc1, hc2⟩ | ⟨hc, hc'⟩ <;>
    rw [hc] <;> linarith

/-- **The first ticks.** `e₁ = e₀`, `ω₁ > 0`, `e₂ < e₀`. -/
theorem yaw_first_ticks (he : 0 < e₀) (ha0 : 0 ≤ α₀) :
    (traj ⟨e₀, 0, α₀⟩ 1).e = e₀ ∧ 0 < (traj ⟨e₀, 0, α₀⟩ 1).ω ∧ (traj ⟨e₀, 0, α₀⟩ 2).e < e₀ := by
  have hp := first_rate_pos θY_pos (div_pos he huY_pos) (div_nonneg ha0 jerk_pos.le)
  have key : hT * uY * (e₀ / (hT * uY)) = e₀ := mul_div_cancel₀ _ huY_pos.ne'
  simp only [traj_rest, trajU, tickU, unsc, s0U, zero_add, sub_zero] at hp ⊢
  refine ⟨key, mul_pos uY_pos hp, ?_⟩
  rw [mul_sub, key]
  linarith [mul_pos huY_pos hp]

/-- **From the second tick on**, the error stays below `max e₂ (9π/3200)`. -/
theorem yaw_after_two (he : 0 < e₀) (ha0 : 0 ≤ α₀) (ha1 : α₀ ≤ accMax) (t : ℕ) (ht : 2 ≤ t) :
    (traj ⟨e₀, 0, α₀⟩ t).e ≤ max (traj ⟨e₀, 0, α₀⟩ 2).e (9 * π / 3200) := by
  have hk := huY_pos
  set S := trajU θY (s0U e₀ α₀) with hS
  have hp := first_rate_pos θY_pos (div_pos he huY_pos) (div_nonneg ha0 jerk_pos.le)
  have hw1 : (S 1).ω = aU θY (e₀ / (hT * uY) - 0) 0 (α₀ / jerkStep) := by
    simp only [hS, trajU, tickU, s0U, zero_add]
  have he1 : (S 1).e = e₀ / (hT * uY) := by simp only [hS, trajU, tickU, s0U, sub_zero]
  have he2 : (S 2).e = (S 1).e - (S 1).ω := by simp only [hS, trajU, tickU]
  rw [traj_rest, traj_rest]
  simp only [unsc]
  rw [← hS]
  obtain ⟨t', rfl⟩ : ∃ t', t = t' + 2 := ⟨t - 2, by omega⟩
  by_cases hbig : 1000 < (S 2).e
  · -- reanchor at tick 2
    have hall : ∀ s ≤ 2, 1000 < (S s).e := by
      intro s hs
      interval_cases s
      · simp only [hS, trajU, s0U]; rw [← he1]; linarith [hw1 ▸ hp]
      · linarith [hw1 ▸ hp]
      · exact hbig
    obtain ⟨hw2, -, -⟩ := traj_sqrt_mono (θ := θY) (ε₀ := e₀ / (hT * uY)) (a₀ := α₀ / jerkStep)
      (div_nonneg ha0 jerk_pos.le) 2 hall
    have hI := InvD_reanchor (invD_rest he ha0 ha1 2) (by norm_num) hbig hw2
    have hI' := InvD_traj θY_pos θY_le (le_max_right _ _) le_rfl hI t'
    rw [trajU_add] at hI'
    have := (InvD_bounds hI').2.1
    calc hT * uY * (S (t' + 2)).e ≤ hT * uY * max (S 2).e 3000 := mul_le_mul_of_nonneg_left this hk.le
      _ = max (hT * uY * (S 2).e) (9 * π / 3200) := by
        rw [mul_max_of_nonneg _ _ hk.le, ← Mrad_eq, Mrad]
  · -- small: the global bound is already below 9π/3200
    have hI := (InvD_bounds (invD_rest he ha0 ha1 (t' + 2))).2.1
    have hw1V : (S 1).ω ≤ VsU := by
      have := (InvD_bounds (invD_rest he ha0 ha1 1)).2.2.2; exact (abs_le.mp this).2
    have hsmall : e₀ / (hT * uY) ≤ 3000 := by
      rw [← he1]; norm_num [VsU] at hw1V; rw [not_lt] at hbig; linarith
    rw [max_eq_right hsmall] at hI
    calc hT * uY * (S (t' + 2)).e ≤ hT * uY * 3000 := mul_le_mul_of_nonneg_left hI hk.le
      _ = 9 * π / 3200 := by rw [← Mrad_eq, Mrad]
      _ ≤ _ := le_max_right _ _

/-- **No wrap.** For a step command `0 < e₀ ≤ π` from rest, the error never reaches `±π` again
after the first tick (`e₁ = e₀`). For `e₀ < π` it never does at all. -/
theorem yaw_no_wrap (he : 0 < e₀) (hπ : e₀ ≤ π) (ha0 : 0 ≤ α₀) (ha1 : α₀ ≤ accMax) (t : ℕ)
    (ht : 2 ≤ t) : |(traj ⟨e₀, 0, α₀⟩ t).e| < π := by
  have h1 := (yaw_bounds he ha0 ha1 t).1
  have h2 := yaw_after_two he ha0 ha1 t ht
  have h3 := (yaw_first_ticks he ha0).2.2
  have hM := Mrad_lt_pi; unfold Mrad at hM
  rw [abs_lt]; constructor
  · linarith
  · exact lt_of_le_of_lt h2 (max_lt (by linarith) hM)

theorem yaw_no_wrap_lt (he : 0 < e₀) (hπ : e₀ < π) (ha0 : 0 ≤ α₀) (ha1 : α₀ ≤ accMax) (t : ℕ) :
    |(traj ⟨e₀, 0, α₀⟩ t).e| < π := by
  obtain ⟨h1, h2, -, -⟩ := yaw_bounds he ha0 ha1 t
  have hM := Mrad_lt_pi; unfold Mrad at hM
  rw [abs_lt]; constructor
  · linarith
  · exact lt_of_le_of_lt h2 (max_lt hπ hM)

/-- **Monotone phase.** While the error has stayed in the sqrt zone (`e_s > ld` for `s ≤ t`), the
shaped rate is nonnegative and the error is nonincreasing. -/
theorem yaw_sqrt_zone_monotone (ha0 : 0 ≤ α₀) (t : ℕ)
    (hs : ∀ s ≤ t, linDist < (traj ⟨e₀, 0, α₀⟩ s).e) :
    0 ≤ (traj ⟨e₀, 0, α₀⟩ t).ω ∧ (traj ⟨e₀, 0, α₀⟩ (t + 1)).e ≤ (traj ⟨e₀, 0, α₀⟩ t).e := by
  have hk := huY_pos
  have hld : linDist = hT * uY * 1000 := by unfold linDist accMax kv hT uY; ring
  have hs' : ∀ s ≤ t, 1000 < (trajU θY (s0U e₀ α₀) s).e := by
    intro s hst
    have := hs s hst
    rw [traj_rest, hld] at this; simp only [unsc] at this
    exact lt_of_mul_lt_mul_left this hk.le
  obtain ⟨hw0, -, -⟩ := traj_sqrt_mono (θ := θY) (div_nonneg ha0 jerk_pos.le) t hs'
  have hw : 0 ≤ (trajU θY (s0U e₀ α₀) t).ω := hw0
  have hstep : (trajU θY (s0U e₀ α₀) (t + 1)).e =
      (trajU θY (s0U e₀ α₀) t).e - (trajU θY (s0U e₀ α₀) t).ω := rfl
  rw [traj_rest, traj_rest]
  simp only [unsc]
  rw [hstep]
  constructor
  · exact mul_nonneg uY_pos.le hw
  · nlinarith [mul_nonneg hk.le hw]

theorem jstep_nonneg {a t : ℝ} (ha : 0 ≤ a) (ht : 0 ≤ t) : 0 ≤ a + clampY (-1) 1 (t - a) := by
  rcases clampY_cases (L := 1) (x := t - a) (by norm_num) with ⟨hc, hc'⟩ | ⟨hc, hc1, hc2⟩ | ⟨hc, hc'⟩ <;>
    rw [hc] <;> linarith

theorem slewU (he : 0 < e₀) (ha0 : 0 ≤ α₀) (ha1 : α₀ ≤ accMax) (t : ℕ)
    (hs : ∀ s, 1 ≤ s → s ≤ t → 50000 ≤ (trajU θY (s0U e₀ α₀) s).e) :
    0 ≤ (trajU θY (s0U e₀ α₀) t).α ∧ 0 ≤ (trajU θY (s0U e₀ α₀) t).ω := by
  induction t with
  | zero => exact ⟨div_nonneg ha0 jerk_pos.le, le_rfl⟩
  | succ n ih =>
    obtain ⟨ha, hw⟩ := ih (fun s h1 h2 => hs s h1 (by omega))
    have hε := hs (n + 1) (by omega) le_rfl
    have hwV := (abs_le.mp (InvD_bounds (invD_rest he ha0 ha1 n)).2.2.2).2
    have hstep : trajU θY (s0U e₀ α₀) (n + 1) = tickU θY (trajU θY (s0U e₀ α₀) n) := rfl
    rw [hstep] at hε ⊢
    simp only [tickU] at hε ⊢
    have ht := tU_slew (θ := θY) hε hw hwV
    have := jstep_nonneg ha ht
    exact ⟨this, by unfold aU; linarith⟩

theorem e_scale_015 {ε : ℝ} (h : 0.15 ≤ hT * uY * ε) : 50000 ≤ ε := by
  have hk := huY_pos
  have h2 : hT * uY * 50000 ≤ 0.15 := by unfold hT uY; nlinarith [Real.pi_lt_d2]
  exact le_of_mul_le_mul_left (h2.trans h) hk

/-- **Slew phase (Tier 3).** While the error stays at or above `0.15` rad (ticks `1 … t+1`), the
shaped acceleration stays nonnegative and the rate is nondecreasing. -/
theorem yaw_slew_rate (he : 0 < e₀) (ha0 : 0 ≤ α₀) (ha1 : α₀ ≤ accMax) (t : ℕ)
    (hs : ∀ s, 1 ≤ s → s ≤ t + 1 → 0.15 ≤ (traj ⟨e₀, 0, α₀⟩ s).e) :
    0 ≤ (traj ⟨e₀, 0, α₀⟩ (t + 1)).α ∧ (traj ⟨e₀, 0, α₀⟩ t).ω ≤ (traj ⟨e₀, 0, α₀⟩ (t + 1)).ω := by
  have hs' : ∀ s, 1 ≤ s → s ≤ t + 1 → 50000 ≤ (trajU θY (s0U e₀ α₀) s).e := by
    intro s h1 h2; have := hs s h1 h2; rw [traj_rest] at this; exact e_scale_015 this
  obtain ⟨ha, -⟩ := slewU he ha0 ha1 (t + 1) hs'
  have hstep : trajU θY (s0U e₀ α₀) (t + 1) = tickU θY (trajU θY (s0U e₀ α₀) t) := rfl
  rw [traj_rest, traj_rest]
  simp only [unsc]
  rw [hstep] at ha ⊢
  simp only [tickU] at ha ⊢
  exact ⟨mul_nonneg jerk_pos.le ha, by nlinarith [mul_nonneg uY_pos.le ha]⟩

/-- **Slew phase rate (Tier 3).** Once the rate has reached `0.9·V` at tick `t₀`, and as long as
the error stays at or above `0.15` rad, the error decreases by at least `0.9·V·h` per tick. -/
theorem yaw_slew_decrease (he : 0 < e₀) (ha0 : 0 ≤ α₀) (ha1 : α₀ ≤ accMax) (t₀ t : ℕ)
    (h0 : t₀ ≤ t) (hs : ∀ s, 1 ≤ s → s ≤ t + 1 → 0.15 ≤ (traj ⟨e₀, 0, α₀⟩ s).e)
    (hω : 0.9 * slew ≤ (traj ⟨e₀, 0, α₀⟩ t₀).ω) :
    (traj ⟨e₀, 0, α₀⟩ (t + 1)).e ≤ (traj ⟨e₀, 0, α₀⟩ t).e - 0.9 * slew * hT := by
  have hmono : ∀ k, t₀ + k ≤ t → (traj ⟨e₀, 0, α₀⟩ t₀).ω ≤ (traj ⟨e₀, 0, α₀⟩ (t₀ + k)).ω := by
    intro k; induction k with
    | zero => intro _; exact le_rfl
    | succ m ih =>
      intro hk
      have := (yaw_slew_rate he ha0 ha1 (t₀ + m) (fun s h1 h2 => hs s h1 (by omega))).2
      exact (ih (by omega)).trans this
  have hw := hmono (t - t₀) (by omega)
  rw [show t₀ + (t - t₀) = t by omega] at hw
  have hstep : (traj ⟨e₀, 0, α₀⟩ (t + 1)).e = (traj ⟨e₀, 0, α₀⟩ t).e - hT * (traj ⟨e₀, 0, α₀⟩ t).ω := rfl
  rw [hstep]
  have : 0 < hT := hT_pos
  nlinarith

end rest

end Contracts.Track.YawPhase
