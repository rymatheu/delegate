import Contracts.Track.Reach.Composite

/-!
# The stalled-target equilibrium and the stall set (REACH.md §3)

If the navigator's S-curve clock converges to `q*` (the target stalls), the target position
converges to `Γ(q*)` while the navigator keeps feeding the S-curve's velocity `v* = Γ'(q*)` and
acceleration `a*` at `q*`. In the error coordinates the target's defects are then constant:
`d₁ = −h v* − h²/2 a*`, `d₂ = −h a*` (the target does not move, but claims `v*, a*`). This file
computes the equilibria of the models under these constant inputs, exactly:

* `joint_stall_eq`: for the joint horizontal–attitude axis (any shaping mode `σ`), the state
  `e = (2/3) v*`, `ev = −v*`, `I = −a*`, all other states `0`, is a fixed point of `jtick`. The
  vehicle sits ahead of the target by `v*/kP` (`kP = 1.5`) at rest; the velocity integrator absorbs
  the feed-forward `a*`.
* `vert_stall_eq`: for the vertical channel, `ez = v* + a*/5`, `ev = −v*`, `eV = −a*/5`, all other
  states `0` is a fixed point of `Vertical.tick` (the vertical velocity loop has no integrator, so the
  feed-forward `a*` costs a velocity error `a*/kpVel`, `kpVel = 5`).
* `stall_dev`: the deviation from the equilibrium follows the same switched linear dynamics, with the
  inputs' deviations from their limits as disturbance (so `Vc_traj`/`asymptotic_gain` apply).
* `stall_ratio`: the raw scaler at the equilibrium. With `pe = −e*` (target minus vehicle), `ve = 0`
  (the vehicle at rest) and the leg direction `d = v/|v|` of a straight leg (`v* = v d`,
  `a* = a d`), the numerator over `|v_T|` is `1 + d_z² (1/2 + 3/10 · a/v)`. Hence
  `stall_ratio_ge_one`: on a horizontal leg, or while the S-curve does not decelerate (`a ≥ 0`), the
  stalled raw scaler is `clamp(0.05 + ratio, 0, 1) = 1`; the stall set is contained in the
  deceleration at the end of a leg with a vertical component, where
  `a/v ≤ −(7/2 /d_z² + 5/3)` (`stall_needs`).
-/

namespace Contracts.Track.Reach

open Matrix

/-! ## The joint axis -/

/-- The stalled equilibrium of the joint axis. -/
noncomputable def jEq (v a : ℝ) : Fin 14 → ℝ := ![2 / 3 * v, -v, 0, 0, -a, 0, 0, 0, 0, 0, 0, 0, 0, 0]

/-- The constant inputs of a stalled target: feed-forward `a*`, defects `−h v* − h²/2 a*`, `−h a*`. -/
noncomputable def jU (v a : ℝ) : Fin 7 → ℝ :=
  ![a, -(1 / 400) * v - (1 / 400) ^ 2 / 2 * a, -(1 / 400) * a, 0, 0, 0, 0]

/-- The cast of the joint input matrix. -/
noncomputable def BjR : Matrix (Fin 14) (Fin 7) ℝ := AttJ.castM AttJ.Bj

set_option maxHeartbeats 4000000 in
/-- **The stalled equilibrium of the joint axis**, for every shaping mode. -/
theorem joint_stall_eq (σ : ℝ) (v a : ℝ) : AttJ.jtick σ (jEq v a) (jU v a) = jEq v a := by
  funext i
  fin_cases i <;>
    simp [AttJ.jtick, jEq, jU, AttJ.hc, AttJ.hp, AttJ.aE, AttJ.kpPos, AttJ.kpH, AttJ.kiH,
      AttJ.kdH, AttJ.aT, AttJ.kpR, AttJ.kiR, AttJ.kdR, AttJ.kP, AttJ.kv, AttJ.bR] <;> ring

/-- The deviation from the stalled equilibrium follows the switched linear model with the inputs'
deviations as disturbance. -/
theorem stall_dev (σ : Fin 2) (x : Fin 14 → ℝ) (u : Fin 7 → ℝ) (v a : ℝ) (w : Fin 14 → ℝ) :
    AttJ.jtick (σ : ℝ) x u + w - jEq v a =
      AttJ.AjR σ *ᵥ (x - jEq v a) + (BjR *ᵥ (u - jU v a) + w) := by
  have h1 := AttJ.jtick_eq_sw σ x u
  have h2 := AttJ.jtick_eq_sw σ (jEq v a) (jU v a)
  rw [joint_stall_eq] at h2
  rw [h1, mulVec_sub, mulVec_sub]
  conv_lhs => rw [h2]
  simp only [BjR]
  abel

/-! ## The vertical channel -/

/-- The stalled equilibrium of the vertical channel. -/
noncomputable def vEq (v a : ℝ) : Fin 8 → ℝ := ![v + a / 5, -v, -(a / 5), 0, 0, 0, 0, 0]

set_option maxHeartbeats 4000000 in
/-- **The stalled equilibrium of the vertical channel.** -/
theorem vert_stall_eq (v a : ℝ) :
    Vertical.tick (vEq v a) a (-(1 / 400) * v - (1 / 400) ^ 2 / 2 * a) (-(1 / 400) * a) =
      vEq v a := by
  funext i
  fin_cases i <;>
    simp [Vertical.tick, vEq, Vertical.per, Vertical.αT, Vertical.αV, Vertical.αA,
      Vertical.kpPos, Vertical.kpVel, Vertical.kpAcc, Vertical.kiDt, Vertical.amax, Vertical.tw,
      Vertical.grav] <;> ring

/-! ## The raw scaler at the stalled equilibrium -/

/-- The numerator of the raw scaler over `|v_T|²` at the stalled equilibrium of a straight leg with
unit direction `d = (dn, de, dz)`, S-curve speed `v > 0` and acceleration `a` (along `d`):
`ve = 0`, `pe = −e*` with `e* = ((2/3) v dn, (2/3) v de, (v + a/5) dz)`, `kP = 3/2`. -/
noncomputable def stallNum (dn de dz v a : ℝ) : ℝ :=
  (0 - 3 / 2 * (-(2 / 3 * v * dn) * dn - (2 / 3 * v * de) * de - ((v + a / 5) * dz) * dz)) / v

/-- **The stalled ratio**: `stallNum = 1 + d_z² (1/2 + 3/10 · a/v)` for a unit direction. -/
theorem stall_ratio (dn de dz v a : ℝ) (hv : 0 < v) (hd : dn ^ 2 + de ^ 2 + dz ^ 2 = 1) :
    stallNum dn de dz v a = 1 + dz ^ 2 * (1 / 2 + 3 / 10 * (a / v)) := by
  unfold stallNum
  field_simp
  have : dn ^ 2 + de ^ 2 = 1 - dz ^ 2 := by linarith
  nlinarith [this]

/-- On a horizontal leg, or while the S-curve does not decelerate, the stalled ratio is at least
`1`, so the stalled raw scaler `clamp(0.05 + ratio, 0, 1)` is `1`: no stall is possible there. -/
theorem stall_ratio_ge_one (dn de dz v a : ℝ) (hv : 0 < v) (hd : dn ^ 2 + de ^ 2 + dz ^ 2 = 1)
    (h : dz = 0 ∨ 0 ≤ a) : 1 ≤ stallNum dn de dz v a := by
  rw [stall_ratio dn de dz v a hv hd]
  rcases h with h | h
  · simp [h]
  · have : 0 ≤ a / v := div_nonneg h hv.le
    have : 0 ≤ dz ^ 2 * (1 / 2 + 3 / 10 * (a / v)) := by positivity
    linarith

/-- A stall (stalled raw scaler `≤ ρ < 1`, i.e. `0.05 + ratio ≤ ρ`) needs the end of a
deceleration on a leg with a vertical component: `dz ≠ 0` and `a/v ≤ −((1.05 − ρ)/d_z² + 1/2)·10/3`. -/
theorem stall_needs (dn de dz v a ρ : ℝ) (hv : 0 < v) (hd : dn ^ 2 + de ^ 2 + dz ^ 2 = 1)
    (hs : 1 / 20 + stallNum dn de dz v a ≤ ρ) (hρ : ρ < 21 / 20) :
    dz ≠ 0 ∧ a / v ≤ -((21 / 20 - ρ) / dz ^ 2 + 1 / 2) * (10 / 3) := by
  rw [stall_ratio dn de dz v a hv hd] at hs
  have hdz : dz ≠ 0 := by
    rintro rfl; simp at hs; linarith
  refine ⟨hdz, ?_⟩
  have hdz2 : 0 < dz ^ 2 := by positivity
  have h1 : dz ^ 2 * (1 / 2 + 3 / 10 * (a / v)) ≤ ρ - 21 / 20 := by linarith
  have h2 : 1 / 2 + 3 / 10 * (a / v) ≤ (ρ - 21 / 20) / dz ^ 2 := by
    rw [le_div_iff₀ hdz2]; linarith
  have e : -((21 / 20 - ρ) / dz ^ 2 + 1 / 2) * (10 / 3) = ((ρ - 21 / 20) / dz ^ 2 - 1 / 2) * (10 / 3) := by
    ring
  rw [e]; linarith

/-! ## Asymptotic gain -/

open Filter Topology in
/-- **Asymptotic gain** of a contraction: if `V (k+1) ≤ μ V k + c k` with `0 ≤ μ < 1`, `V ≥ 0`, and
`c k` is eventually at most `C + η` for every `η > 0`, then `V k` is eventually at most
`C/(1 − μ) + η` for every `η > 0`. With the composite `Vc` and the stalled inputs, this is the
convergence of the closed-loop state to the stalled equilibrium, up to the floor `C` of the
`float` and plant residuals. -/
theorem asymptotic_gain {V c : ℕ → ℝ} {μ C : ℝ} (hμ : 0 ≤ μ) (hμ1 : μ < 1) (hV : ∀ k, 0 ≤ V k)
    (hC : 0 ≤ C) (h : ∀ k, V (k + 1) ≤ μ * V k + c k)
    (hc : ∀ η > 0, ∀ᶠ k in atTop, c k ≤ C + η) :
    ∀ η > 0, ∀ᶠ k in atTop, V k ≤ C / (1 - μ) + η := by
  intro η hη
  have h1μ : 0 < 1 - μ := by linarith
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hc (η * (1 - μ) / 2) (by positivity))
  -- from `N` on, the comparison with the constant `C + η(1−μ)/2`
  have hcomp : ∀ n, V (N + n) ≤ μ ^ n * V N + (C + η * (1 - μ) / 2) / (1 - μ) := by
    intro n
    have := Vertical.comparison_const (V := fun k => V (N + k)) (c := C + η * (1 - μ) / 2)
      hμ hμ1 (by positivity)
      (fun k => by
        have := h (N + k)
        have := hN (N + k) (by omega)
        rw [show N + (k + 1) = N + k + 1 by omega]
        nlinarith [hV (N + k)]) n
    simpa using this
  have hpow : Tendsto (fun n => μ ^ n * V N) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hμ hμ1).mul_const (V N)
  obtain ⟨M, hM⟩ := eventually_atTop.1 (hpow.eventually (Iio_mem_nhds (by positivity :
    (0 : ℝ) < η / 2)))
  refine eventually_atTop.2 ⟨N + M, fun k hk => ?_⟩
  obtain ⟨n, rfl⟩ : ∃ n, k = N + n := ⟨k - N, by omega⟩
  have h1 := hcomp n
  have h2 : μ ^ n * V N < η / 2 := hM n (by omega)
  have e : (C + η * (1 - μ) / 2) / (1 - μ) = C / (1 - μ) + η / 2 := by field_simp
  linarith

end Contracts.Track.Reach
