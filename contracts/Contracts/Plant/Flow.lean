module

public import Contracts.Plant.Invariants
public import DynamicalSystems.Mathlib.Analysis.ODE.GlobalExistenceLinear
public import DynamicalSystems.Mathlib.Analysis.ODE.RadialTruncation
public import Mathlib.Analysis.ODE.Gronwall
-- the body of `radialTrunc` (a scaling) is needed for `radialTrunc_eq_smul`
import all DynamicalSystems.Mathlib.Analysis.ODE.RadialTruncation

/-!
# The flow under zero-order hold and the sampled step

**Truncation.** `F(·, u)` is Lipschitz on every ball (`vf_lipschitz_ball`), hence locally Lipschitz
(`vf_locallyLipschitz`), but not globally. The library's radial retraction `radialTrunc R`
(identity on the ball of radius `R`, `2`-Lipschitz, image in the ball) gives the globally Lipschitz
field `vfT R u = F(radialTrunc R ·, u)` (`vfT_lipschitz`, constant `2 Klip R`), and the library's
`LipschitzWith.exists_autonomousFlow` (Picard-Lindelöf on bounded intervals, patched; proved in
`DynamicalSystems/Mathlib/Analysis/ODE/GlobalExistenceLinear.lean`, axioms `propext`,
`Classical.choice`, `Quot.sound`) gives its global flow `flowT R u : AutonomousFlow ℝ X`.

**No truncation is visible.** The truncation is a scaling of the state by `c ∈ [0, 1]`
(`radialTrunc_eq_smul`), so a curve of `flowT R u` is a scaled solution (`scaledSol_flowT`), and
the a priori estimate keeps it in the ball of radius `box ‖x‖` over one period. With
`R = box ‖x‖` the truncation is the identity along the whole curve, which is therefore an integral
curve of the true field `F` on `[0, h]` (`traj_hasDerivAt`).

**The step.** `traj x u t = flowT (box ‖x‖) u t x` and `step x u = traj x u h`: the state after one
control period with the actuators held at `u`. It is the endpoint of the unique solution of
`ẋ = F(x, u)` on `[0, h]` from `x` (`step_spec`, `step_unique`), it does not depend on the
truncation radius once that is at least `box ‖x‖` (`step_eq_flowT`), it keeps `‖q‖²`
(`qnormSq_traj`, `qnormSq_step`), it moves by at most the Grönwall bound
`‖F(x, u)‖ (e^{K t} - 1) / K` with `K = Klip (box ‖x‖)` (`norm_traj_sub_le`), and the level hover
state is a fixed point (`step_hover`).
-/

@[expose] public section

namespace Contracts.Plant

noncomputable section

open Set Metric

/-! ## Local Lipschitz continuity -/

/-- **`F(·, u)` is locally Lipschitz** (it is polynomial in the state). -/
theorem vf_locallyLipschitz (u : Fin 4 → ℝ) : LocallyLipschitz (fun x => vf x u) := by
  intro x
  refine ⟨Real.toNNReal (Klip (‖x‖ + 1)), closedBall x 1, closedBall_mem_nhds x one_pos,
    LipschitzOnWith.of_dist_le_mul fun a ha b hb => ?_⟩
  have hn : ∀ y ∈ closedBall x 1, ‖y‖ ≤ ‖x‖ + 1 := fun y hy => by
    rw [mem_closedBall, dist_eq_norm] at hy
    have := norm_sub_norm_le y x; linarith
  rw [dist_eq_norm, dist_eq_norm,
    Real.coe_toNNReal _ (Klip_pos (by positivity : (0 : ℝ) ≤ ‖x‖ + 1)).le]
  exact vf_lipschitz_ball u (hn a ha) (hn b hb)

/-- `F(·, u)` is continuous. -/
theorem vf_continuous (u : Fin 4 → ℝ) : Continuous (fun x => vf x u) :=
  (vf_locallyLipschitz u).continuous

/-! ## The truncated field and its flow -/

/-- The radial retraction is a scaling by `c ∈ [0, 1]`. -/
theorem radialTrunc_eq_smul {R : ℝ} (hR : 0 ≤ R) (y : X) :
    ∃ c : ℝ, 0 ≤ c ∧ c ≤ 1 ∧ radialTrunc R y = c • y := by
  unfold radialTrunc
  split_ifs with hy
  · exact ⟨1, zero_le_one, le_rfl, (one_smul _ _).symm⟩
  · push Not at hy
    have : 0 < ‖y‖ := lt_of_le_of_lt hR hy
    exact ⟨R / ‖y‖, div_nonneg hR this.le, (div_le_one this).2 hy.le, rfl⟩

/-- **The truncated field** `F(radialTrunc R ·, u)` (radius `max R 0`). -/
def vfT (R : ℝ) (u : Fin 4 → ℝ) (y : X) : X := vf (radialTrunc (max R 0) y) u

/-- The truncated field agrees with `F` on the ball of radius `R`. -/
theorem vfT_eq_vf {R : ℝ} (hR : 0 ≤ R) (u : Fin 4 → ℝ) {y : X} (hy : ‖y‖ ≤ R) :
    vfT R u y = vf y u := by
  rw [vfT, max_eq_left hR, radialTrunc_eq_self hy]

/-- The truncated field is globally Lipschitz, with constant `2 Klip R`. -/
theorem vfT_lipschitz (R : ℝ) (u : Fin 4 → ℝ) :
    LipschitzWith (Real.toNNReal (2 * Klip (max R 0))) (vfT R u) := by
  set R' := max R 0
  have hR' : 0 ≤ R' := le_max_right _ _
  have hK := Klip_pos hR'
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [dist_eq_norm, dist_eq_norm, Real.coe_toNNReal _ (by positivity)]
  calc ‖vfT R u x - vfT R u y‖ ≤ Klip R' * ‖radialTrunc R' x - radialTrunc R' y‖ :=
        vf_lipschitz_ball u (norm_radialTrunc_le hR' x) (norm_radialTrunc_le hR' y)
    _ ≤ Klip R' * (2 * ‖x - y‖) :=
        mul_le_mul_of_nonneg_left (norm_radialTrunc_sub_radialTrunc_le hR' x y) hK.le
    _ = 2 * Klip R' * ‖x - y‖ := by ring

/-- **The flow of the truncated field** (`LipschitzWith.exists_autonomousFlow`). -/
def flowT (R : ℝ) (u : Fin 4 → ℝ) : AutonomousFlow ℝ X :=
  (LipschitzWith.exists_autonomousFlow (vfT_lipschitz R u)).choose

/-- `flowT R u` is the fundamental solution of the truncated field. -/
theorem flowT_spec (R : ℝ) (u : Fin 4 → ℝ) : (flowT R u).IsFundamentalSolution (vfT R u) :=
  (LipschitzWith.exists_autonomousFlow (vfT_lipschitz R u)).choose_spec

/-- A curve of the truncated flow is a scaled solution. -/
theorem scaledSol_flowT {R : ℝ} (hR : 0 ≤ R) (u : Fin 4 → ℝ) (x : X) (T : ℝ) :
    ScaledSol u T (fun t => flowT R u t x) := by
  intro t _
  obtain ⟨c, hc0, hc1, hc⟩ := radialTrunc_eq_smul hR (flowT R u t x)
  refine ⟨c, hc0, hc1, ?_⟩
  have := flowT_spec R u x t
  simp only [vfT, max_eq_left hR] at this
  rwa [hc] at this

/-! ## The trajectory of one period and the step -/

/-- **The trajectory under held actuators** `u` from `x`: the truncated flow at radius
`box ‖x‖`, which over `[0, h]` is the true solution. -/
def traj (x : X) (u : Fin 4 → ℝ) (t : ℝ) : X := flowT (box ‖x‖) u t x

/-- **The plant step**: the state after one control period `h` with the actuators held at `u`. -/
def step (x : X) (u : Fin 4 → ℝ) : X := traj x u h

section traj
variable (x : X) (u : Fin 4 → ℝ)

theorem traj_zero : traj x u 0 = x := (flowT _ u).map_id x

theorem scaledSol_traj (T : ℝ) : ScaledSol u T (traj x u) :=
  scaledSol_flowT (box_nonneg (norm_nonneg x)) u x T

/-- The trajectory stays in the ball of radius `box ‖x‖` over one period. -/
theorem traj_norm_le : ∀ t ∈ Icc 0 h, ‖traj x u t‖ ≤ box ‖x‖ :=
  norm_le_box_of_scaledSol (scaledSol_traj x u h) (by rw [traj_zero])

theorem norm_le_box : ‖x‖ ≤ box ‖x‖ := by
  simpa [traj_zero] using traj_norm_le x 0 0 ⟨le_rfl, h_pos.le⟩

/-- **The trajectory is an integral curve of the true field on `[0, h]`.** -/
theorem traj_hasDerivAt : ∀ t ∈ Icc 0 h, HasDerivAt (traj x u) (vf (traj x u t) u) t := by
  intro t ht
  have := flowT_spec (box ‖x‖) u x t
  simp only at this
  change HasDerivAt (traj x u) (vfT (box ‖x‖) u (traj x u t)) t at this
  rwa [vfT_eq_vf (box_nonneg (norm_nonneg x)) u (traj_norm_le x u t ht)] at this

/-- The trajectory as an `IsIntegralCurveOn` of `F(·, u)` on `[0, h]`. -/
theorem traj_isIntegralCurveOn : IsIntegralCurveOn (traj x u) (fun _ y => vf y u) (Icc 0 h) :=
  fun t ht => (traj_hasDerivAt x u t ht).hasDerivWithinAt

theorem traj_continuousOn : ContinuousOn (traj x u) (Icc 0 h) :=
  fun t ht => (traj_hasDerivAt x u t ht).continuousAt.continuousWithinAt

/-- **The step is an integral curve evaluation.** -/
theorem step_spec : ∃ γ : ℝ → X, γ 0 = x ∧ γ h = step x u ∧
    ∀ t ∈ Icc 0 h, HasDerivAt γ (vf (γ t) u) t :=
  ⟨traj x u, traj_zero x u, rfl, traj_hasDerivAt x u⟩

end traj

/-- **Uniqueness on `[0, h]`.** A curve continuous on `[0, h]`, starting at `x`, with right
derivative `F(γ t, u)` on `[0, h)`, is the trajectory. -/
theorem traj_unique {x : X} {u : Fin 4 → ℝ} {γ : ℝ → X} (h0 : γ 0 = x)
    (hc : ContinuousOn γ (Icc 0 h))
    (hd : ∀ t ∈ Ico 0 h, HasDerivWithinAt γ (vf (γ t) u) (Ici t) t) :
    EqOn γ (traj x u) (Icc 0 h) := by
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hc
  set R := max C (box ‖x‖)
  have hR : 0 ≤ R := le_max_of_le_right (box_nonneg (norm_nonneg x))
  refine ODE_solution_unique_of_mem_Icc_right (v := fun _ y => vf y u)
    (s := fun _ => closedBall 0 R) (K := Real.toNNReal (Klip R)) ?_ hc hd ?_
    (traj_continuousOn x u) ?_ ?_ (h0.trans (traj_zero x u).symm)
  · intro _ _
    refine LipschitzOnWith.of_dist_le_mul fun a ha b hb => ?_
    rw [dist_eq_norm, dist_eq_norm, Real.coe_toNNReal _ (Klip_pos hR).le]
    exact vf_lipschitz_ball u (mem_closedBall_zero_iff.1 ha) (mem_closedBall_zero_iff.1 hb)
  · exact fun t ht => mem_closedBall_zero_iff.2 ((hC t (Ico_subset_Icc_self ht)).trans
      (le_max_left _ _))
  · exact fun t ht => (traj_hasDerivAt x u t (Ico_subset_Icc_self ht)).hasDerivWithinAt
  · exact fun t ht => mem_closedBall_zero_iff.2
      ((traj_norm_le x u t (Ico_subset_Icc_self ht)).trans (le_max_right _ _))

/-- **Uniqueness of the step.** Every solution on `[0, h]` from `x` under `u` ends at
`step x u`. -/
theorem step_unique {x : X} {u : Fin 4 → ℝ} {γ : ℝ → X} (h0 : γ 0 = x)
    (hc : ContinuousOn γ (Icc 0 h))
    (hd : ∀ t ∈ Ico 0 h, HasDerivWithinAt γ (vf (γ t) u) (Ici t) t) : γ h = step x u :=
  traj_unique h0 hc hd ⟨h_pos.le, le_rfl⟩

/-- **The step does not depend on the truncation radius**: for every `R ≥ box ‖x‖`, the truncated
flow at time `h` is the step. -/
theorem step_eq_flowT {x : X} {u : Fin 4 → ℝ} {R : ℝ} (hR : box ‖x‖ ≤ R) :
    flowT R u h x = step x u := by
  have hR0 : 0 ≤ R := (box_nonneg (norm_nonneg x)).trans hR
  set γ := fun t => flowT R u t x
  have hb := norm_le_box_of_scaledSol (scaledSol_flowT hR0 u x h) (r := ‖x‖)
    (by simp [(flowT R u).map_id])
  have hd : ∀ t ∈ Icc 0 h, HasDerivAt γ (vf (γ t) u) t := fun t ht => by
    have := flowT_spec R u x t
    simp only at this
    rwa [vfT_eq_vf hR0 u ((hb t ht).trans hR)] at this
  exact step_unique (γ := γ) ((flowT R u).map_id x)
    (fun t ht => (hd t ht).continuousAt.continuousWithinAt)
    (fun t ht => (hd t (Ico_subset_Icc_self ht)).hasDerivWithinAt)

/-! ## Invariance of the unit sphere -/

/-- **`‖q‖` is constant along every solution** of `F(·, u)` on `[0, T]`. -/
theorem qnormSq_const_of_solution {u : Fin 4 → ℝ} {T : ℝ} {γ : ℝ → X}
    (hγ : ∀ t ∈ Icc 0 T, HasDerivAt γ (vf (γ t) u) t) :
    ∀ t ∈ Icc 0 T, qnormSq (γ t) = qnormSq (γ 0) :=
  qnormSq_scaledSol (scaledSol_of_hasDerivAt hγ)

/-- `‖q‖` is constant along the trajectory. -/
theorem qnormSq_traj (x : X) (u : Fin 4 → ℝ) :
    ∀ t ∈ Icc 0 h, qnormSq (traj x u t) = qnormSq x := by
  intro t ht; rw [qnormSq_const_of_solution (traj_hasDerivAt x u) t ht, traj_zero]

/-- **The unit sphere is invariant under the step**: `‖q‖² ` of the next state is that of the
current state; in particular a unit quaternion stays a unit quaternion. -/
theorem qnormSq_step (x : X) (u : Fin 4 → ℝ) : qnormSq (step x u) = qnormSq x :=
  qnormSq_traj x u h ⟨h_pos.le, le_rfl⟩

/-! ## Grönwall bound over one period -/

/-- The box is monotone in the radius. -/
theorem box_mono {r r' : ℝ} (hr : 0 ≤ r) (hrr : r ≤ r') : box r ≤ box r' := by
  have hsq : r ^ 2 ≤ r' ^ 2 := pow_le_pow_left₀ hr hrr 2
  have := h_pos; have := amax_pos; have := grav_pos
  have hv : vB r ≤ vB r' := by
    unfold vB
    have : amax * (4 * r ^ 2) ≤ amax * (4 * r' ^ 2) := by nlinarith
    have : h * (grav + amax * (4 * r ^ 2)) ≤ h * (grav + amax * (4 * r' ^ 2)) :=
      mul_le_mul_of_nonneg_left (by linarith) h_pos.le
    linarith
  have hp : pB r ≤ pB r' := by
    unfold pB
    have := mul_le_mul_of_nonneg_left hv h_pos.le
    linarith
  have hq : qB r ≤ qB r' := by unfold qB; linarith
  have hw : wB r ≤ wB r' := by
    unfold wB
    apply Real.sqrt_le_sqrt
    apply div_le_div_of_nonneg_right _ Jx_pos.le
    apply mul_le_mul_of_nonneg_right _ (Real.exp_pos 1).le
    have : (0 : ℝ) ≤ Jx + Jy + Jz := by norm_num [Jx, Jy, Jz]
    nlinarith
  exact max_le_max (max_le_max hp hv) (max_le_max hq hw)

/-- **Grönwall bound**, with the Lipschitz constant of any ball of radius `R ≥ box ‖x‖`. -/
theorem norm_traj_sub_le_of_le (x : X) (u : Fin 4 → ℝ) {R : ℝ} (hR : box ‖x‖ ≤ R) :
    ∀ t ∈ Icc 0 h, ‖traj x u t - x‖ ≤ gronwallBound 0 (Klip R) ‖vf x u‖ t := by
  intro t ht
  have := norm_le_gronwallBound_of_norm_deriv_right_le (f := fun t => traj x u t - x)
    (f' := fun t => vf (traj x u t) u) (δ := 0) (K := Klip R) (ε := ‖vf x u‖)
    (a := 0) (b := h) ((traj_continuousOn x u).sub continuousOn_const)
    (fun s hs => ((traj_hasDerivAt x u s (Ico_subset_Icc_self hs)).sub_const x).hasDerivWithinAt)
    (by simp [traj_zero])
    (fun s hs => by
      have h1 := vf_lipschitz_ball u ((traj_norm_le x u s (Ico_subset_Icc_self hs)).trans hR)
        ((norm_le_box x).trans hR)
      calc ‖vf (traj x u s) u‖ = ‖(vf (traj x u s) u - vf x u) + vf x u‖ := by
            rw [sub_add_cancel]
        _ ≤ ‖vf (traj x u s) u - vf x u‖ + ‖vf x u‖ := norm_add_le _ _
        _ ≤ _ := by linarith) t ht
  simpa using this

/-- **Grönwall bound.** Over `[0, h]` the trajectory moves by at most
`gronwallBound 0 K ‖F(x, u)‖ t = ‖F(x, u)‖ (e^{K t} - 1) / K`, with `K = Klip (box ‖x‖)` the
Lipschitz constant of `F(·, u)` on the ball the trajectory stays in. -/
theorem norm_traj_sub_le (x : X) (u : Fin 4 → ℝ) :
    ∀ t ∈ Icc 0 h, ‖traj x u t - x‖ ≤ gronwallBound 0 (Klip (box ‖x‖)) ‖vf x u‖ t :=
  norm_traj_sub_le_of_le x u le_rfl

/-- **Grönwall bound on a ball**: for `‖x‖ ≤ r` and `t ∈ [0, h]`,
`‖Φ_u t x - x‖ ≤ gronwallBound 0 (Klip (box r)) ‖F(x, u)‖ t`. -/
theorem norm_traj_sub_le_ball {x : X} {r : ℝ} (u : Fin 4 → ℝ) (hx : ‖x‖ ≤ r) :
    ∀ t ∈ Icc 0 h, ‖traj x u t - x‖ ≤ gronwallBound 0 (Klip (box r)) ‖vf x u‖ t :=
  norm_traj_sub_le_of_le x u (box_mono (norm_nonneg x) hx)

/-- The Grönwall bound written out: `‖traj x u t - x‖ ≤ ‖F(x, u)‖ (e^{K t} - 1) / K`. -/
theorem norm_traj_sub_le_exp (x : X) (u : Fin 4 → ℝ) :
    ∀ t ∈ Icc 0 h, ‖traj x u t - x‖ ≤
      ‖vf x u‖ / Klip (box ‖x‖) * (Real.exp (Klip (box ‖x‖) * t) - 1) := by
  intro t ht
  have := norm_traj_sub_le x u t ht
  simpa [gronwallBound_of_K_ne_0 (Klip_pos (box_nonneg (norm_nonneg x))).ne'] using this

/-- The crude companion: `‖traj x u t - x‖ ≤ Mbd (box ‖x‖) · t`. -/
theorem norm_traj_sub_le_mul (x : X) (u : Fin 4 → ℝ) :
    ∀ t ∈ Icc 0 h, ‖traj x u t - x‖ ≤ Mbd (box ‖x‖) * t := by
  intro t ht
  have := norm_image_sub_le_of_norm_deriv_le_segment' (f := traj x u)
    (f' := fun s => vf (traj x u s) u) (C := Mbd (box ‖x‖))
    (fun s hs => (traj_hasDerivAt x u s hs).hasDerivWithinAt)
    (fun s hs => norm_vf_le u (traj_norm_le x u s (Ico_subset_Icc_self hs))) t ht
  simpa [traj_zero] using this

/-! ## Hover -/

/-- The level state at rest at height `z` (NED down coordinate), facing north. -/
def hoverState (z : ℝ) : State := ⟨⟨0, 0, z⟩, ⟨0, 0, 0⟩, ⟨1, 0, 0, 0⟩, ⟨0, 0, 0⟩⟩

/-- The hover state in flat coordinates. -/
def hoverX (z : ℝ) : X := (hoverState z).toX

/-- At the hover thrust fraction `1 / thrust2weight` on every motor the thrust balances gravity. -/
theorem accel_hover {u : Fin 4 → ℝ} (hu : ∀ i, u i = 1 / thrust2weight) : accel u = grav := by
  have hc : ∀ i, clip01 (u i) = 1 / thrust2weight := fun i => by
    rw [hu i]; exact clip01_of_mem (by norm_num [thrust2weight]) (by norm_num [thrust2weight])
  rw [accel, thrust_eq, hc, hc, hc, hc, fmax_eq]
  field_simp [mass_pos.ne']
  norm_num [thrust2weight]
  ring

/-- **Hover equilibrium.** The level state at rest with four equal actuators
`1 / thrust2weight` is an equilibrium of `F`. -/
theorem vf_hover (z : ℝ) {u : Fin 4 → ℝ} (hu : ∀ i, u i = 1 / thrust2weight) :
    vf (hoverX z) u = 0 := by
  have hA := accel_hover hu
  have hc : ∀ i, clip01 (u i) = 1 / thrust2weight := fun i => by
    rw [hu i]; exact clip01_of_mem (by norm_num [thrust2weight]) (by norm_num [thrust2weight])
  have hx : torqueX u = 0 := by simp only [torqueX, force, hc]; ring
  have hy : torqueY u = 0 := by simp only [torqueY, force, hc]; ring
  have hz : torqueZ u = 0 := by simp only [torqueZ, hc]; ring
  funext i
  fin_cases i <;>
    simp [vf_0, vf_1, vf_2, vf_3, vf_4, vf_5, vf_6, vf_7, vf_8, vf_9, vf_10, vf_11, vf_12, hoverX,
      hoverState, State.toX, hA, hx, hy, hz]

/-- **The hover state is a fixed point of the step.** -/
theorem step_hover (z : ℝ) {u : Fin 4 → ℝ} (hu : ∀ i, u i = 1 / thrust2weight) :
    step (hoverX z) u = hoverX z :=
  (step_unique (γ := fun _ => hoverX z) rfl continuousOn_const
    (fun _ _ => by rw [vf_hover z hu]; exact hasDerivWithinAt_const _ _ _)).symm

end

end Contracts.Plant
