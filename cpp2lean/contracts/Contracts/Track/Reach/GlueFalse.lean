import Contracts.Track.Reach.Loop

/-!
# `HoverGlue` as stated is false (REACH.md §"Glue")

`HoverGlue sense32 senseP w₀ wp κ c₀ ν` (Loop.lean) quantifies over **every** behavior of `Mloop`.
`Mloop` does not constrain the initial plant state (`Mplant` is `liftStep` of the plant's step, and
the controller is the lift of `tickT` from `none`): for every world, every pair of ports and every
initial plant state there is a behavior (`driftB_mem`, the joint step iterated, as in
`waypoint_reach_nonvacuous`).

Take the behavior that starts at `wp` itself, level, with no body rates, moving north at speed `V`.
Its composite error state must start as `pureOffset 0 = 0`, which is in `D` (`Vc = 0 ≤ ν`), so the
first disturbance has `Vc (w 0) ≤ c₀`, so `ξ 1 = w 0` has `‖posErr (ξ 1)‖² ≤ γ_e c₀`. But the plant
moves the vehicle by at least `h V − (g + a_max) h²` north in one period, whatever the actuators
(`drift_north_ge`, from `v_scaledSol` of `Plant/Invariants.lean`). For `V` large enough the two
contradict (`not_hoverGlue`).

Under the hypotheses of `hover_practically_exponentially_stable` (`0 ≤ κ`, `0 ≤ c₀`, `ρ < 1`,
`ρ ν + c₀/(1 − λ) ≤ ν`) the region is nonempty (`0 ≤ ν`), so that theorem is vacuous as stated
(`hoverGlue_hyps_false`). The corrected statement restricts the behaviors (hover start, the hover
world, the hold of the target) and replaces the `Vc`-ball by the ℓ1 tube: `GlueTube.lean`.
-/

namespace Contracts.Track.Reach

open Contracts Contracts.STL Contracts.Lift Contracts.Mission Set

noncomputable section

/-- The plant state at `p`, level and facing north, no body rates, moving north at `V`, with the
hover actuators held. -/
def driftP (p : P3) (V : ℝ) : Plant.PState :=
  ⟨(⟨⟨p 0, p 1, p 2⟩, ⟨V, 0, 0⟩, ⟨1, 0, 0, 0⟩, ⟨0, 0, 0⟩⟩ : Plant.State).toX, hoverHeld⟩

/-- The behavior of the loop from `driftP p V`: the joint step iterated. -/
def driftB (sense32 : ℝ → Float32) (senseP : ℝ → Float) (w₀ : Vehicle.World) (p : P3) (V : ℝ) :
    ℕ → X :=
  fun t => (jointStep sense32 senseP w₀
    (runState (jointStep sense32 senseP w₀) (driftP p V, none) (fun _ => ()) t) ()).2

/-- `driftB` is a behavior of the closed loop. -/
theorem driftB_mem (sense32 : ℝ → Float32) (senseP : ℝ → Float) (w₀ : Vehicle.World) (p : P3)
    (V : ℝ) : driftB sense32 senseP w₀ p V ∈ Mloop sense32 senseP w₀ :=
  ⟨mem_Mplant.2 fun _ => ⟨rfl, rfl⟩,
    ⟨fun t => (runState (jointStep sense32 senseP w₀) (driftP p V, none) (fun _ => ()) t).2, rfl,
      fun _ => rfl⟩⟩

theorem driftB_zero (sense32 : ℝ → Float32) (senseP : ℝ → Float) (w₀ : Vehicle.World) (p : P3)
    (V : ℝ) : (driftB sense32 senseP w₀ p V 0).phys = driftP p V := rfl

/-- **One period of the plant moves a north-moving level vehicle north**, whatever the actuators:
`x₀' ≥ x₀ + h V − (g + a_max) h²` (the velocity changes by at most `(g + a_max ‖q‖²) t`). -/
theorem drift_north_ge (p : P3) (V : ℝ) (u : Fin 4 → ℝ) :
    p 0 + Plant.h * V - (Plant.grav + Plant.amax) * Plant.h ^ 2 ≤
      Plant.step (driftP p V).x u 0 := by
  set x0 := (driftP p V).x with hx0
  have hq : Plant.qnormSq x0 = 1 := by
    simp [x0, driftP, Plant.qnormSq, Plant.State.toX]
  have h0 : x0 0 = p 0 := by simp [x0, driftP, Plant.State.toX]
  have h3 : x0 3 = V := by simp [x0, driftP, Plant.State.toX]
  have hS := Plant.scaledSol_traj x0 u Plant.h
  have hv := Plant.v_scaledSol hS 3 (Or.inl rfl)
  have hγ0 : Plant.traj x0 u 0 = x0 := Plant.traj_zero x0 u
  rw [hγ0, hq, h3, mul_one] at hv
  have hd := Plant.traj_hasDerivAt x0 u
  have hh := Plant.h_pos
  have hg := Plant.grav_pos
  have ha := Plant.amax_pos
  -- f t = γ t 0 - t V has derivative γ t 3 - V, bounded by (g + amax) h on [0, h]
  have key := Plant.abs_sub_le_of_deriv (f := fun t => Plant.traj x0 u t 0 - t * V)
    (g := fun t => Plant.traj x0 u t 3 - V) (T := Plant.h) (C := (Plant.grav + Plant.amax) * Plant.h)
    (fun t ht => by
      have h1 := hasDerivAt_pi.1 (hd t ht) 0
      rw [Plant.vf_0] at h1
      have h2 := h1.sub ((hasDerivAt_id t).mul_const V)
      simp only [id, one_mul] at h2
      exact h2)
    (fun t ht => by
      calc |Plant.traj x0 u t 3 - V| ≤ (Plant.grav + Plant.amax) * t := hv t ht
        _ ≤ (Plant.grav + Plant.amax) * Plant.h :=
          mul_le_mul_of_nonneg_left ht.2 (by positivity))
    Plant.h ⟨hh.le, le_rfl⟩
  simp only [hγ0, h0, zero_mul, sub_zero] at key
  have := (abs_le.1 key).1
  have e : Plant.step x0 u 0 = Plant.traj x0 u Plant.h 0 := rfl
  rw [e]
  nlinarith

/-- `Vc` of the pure offset `0` is `0`. -/
theorem Vc_pureOffset_zero : Vc (pureOffset 0) = 0 :=
  le_antisymm (by simpa using Vc_pureOffset 0) (Vc_nonneg _)

/-- `pureOffset 0` is the zero state, so one model step from it is the disturbance. -/
theorem cstep_pureOffset_zero (σn σe : Fin 2) (w : CS) : cstep σn σe (pureOffset 0) w = w := by
  rcases w with ⟨wv, wn, we⟩
  simp [cstep, pureOffset]

/-- **`HoverGlue` is false** for every world, every pair of ports, every target `wp` and every
`κ`, `c₀`, `ν ≥ 0`: the behavior from `wp` moving north fast enough leaves the ball that the glue
allows after one tick. -/
theorem not_hoverGlue (sense32 : ℝ → Float32) (senseP : ℝ → Float) (w₀ : Vehicle.World) (wp : P3)
    {κ c₀ ν : ℝ} (hν : 0 ≤ ν) : ¬ HoverGlue sense32 senseP w₀ wp κ c₀ ν := by
  intro hG
  set B := Real.sqrt (γe * c₀) with hB
  have hh := Plant.h_pos
  set V := (B + (Plant.grav + Plant.amax) * Plant.h ^ 2 + 1) / Plant.h with hV
  set x := driftB sense32 senseP w₀ wp V
  obtain ⟨ξ, w, σn, σe, h0, hpos, hstep, hw⟩ := hG x (driftB_mem sense32 senseP w₀ wp V)
  have hp0 : pos (x 0) = wp := by
    ext i; fin_cases i <;> simp [x, pos, driftB_zero, driftP, Plant.State.toX]
  rw [hp0, sub_self] at h0
  have hD0 : Vc (ξ 0) ≤ ν := by rw [h0, Vc_pureOffset_zero]; exact hν
  have hw0 := hw 0 hD0
  rw [h0, Vc_pureOffset_zero, mul_zero, zero_add] at hw0
  have h1 : ξ 1 = w 0 := by rw [hstep 0, h0, cstep_pureOffset_zero]
  -- the model's position error after one tick
  have hsq := pos_sq_le (ξ 1)
  rw [h1] at hsq
  have hle : ‖posErr (ξ 1)‖ ≤ B := by
    rw [h1, hB]
    exact Real.le_sqrt_of_sq_le (hsq.trans (mul_le_mul_of_nonneg_left hw0 γe_pos.le))
  rw [hpos 1] at hle
  -- the plant's north displacement
  have hx1 : (x 1).phys = Plant.next (x 0).phys (x 0).out.act :=
    (mem_Mplant.1 (driftB_mem sense32 senseP w₀ wp V).1 0).1
  have hn := drift_north_ge wp V (Plant.act (x 0).out.act)
  have e1 : (pos (x 1) - wp) 0 = Plant.step (driftP wp V).x (Plant.act (x 0).out.act) 0 - wp 0 := by
    simp [pos, hx1, Plant.next, Plant.nextR, driftB_zero, x]
  have hc : |(pos (x 1) - wp) 0| ≤ ‖pos (x 1) - wp‖ := by
    simpa [Real.norm_eq_abs] using PiLp.norm_apply_le (pos (x 1) - wp) 0
  have hVh : Plant.h * V = B + (Plant.grav + Plant.amax) * Plant.h ^ 2 + 1 := by
    rw [hV]; field_simp
  have : B + 1 ≤ (pos (x 1) - wp) 0 := by rw [e1]; linarith
  have := (le_abs_self _).trans hc
  linarith

/-- **Under the hypotheses of `hover_practically_exponentially_stable`, `HoverGlue` is false**:
the hypotheses force `ν ≥ 0`. So that theorem, as stated, is vacuous. -/
theorem hoverGlue_hyps_false (sense32 : ℝ → Float32) (senseP : ℝ → Float) (w₀ : Vehicle.World)
    (wp : P3) {κ c₀ ν : ℝ} (_hκ : 0 ≤ κ) (hc₀ : 0 ≤ c₀) (hρ : lamC + κ / (1 - lamC) < 1)
    (hν : (lamC + κ / (1 - lamC)) * ν + c₀ / (1 - lamC) ≤ ν) :
    ¬ HoverGlue sense32 senseP w₀ wp κ c₀ ν := by
  apply not_hoverGlue
  have hl1 : (0 : ℝ) < 1 - lamC := by linarith [lamC_lt_one]
  have : 0 ≤ c₀ / (1 - lamC) := by positivity
  nlinarith

/-! ## The `Vc`-ball cannot carry the code's tilt quantization

`attitude_from_thrust_vector` (AC_AttitudeControl.cpp) takes the commanded tilt as
`acosf(constrain(-n.z, -1, 1))` of the normalized thrust vector `n`. In `float` the dot product is
exactly `1` for every horizontal command `|a| ≤ 3.38·10⁻³` m/s² (tilt `≤ 3.45·10⁻⁴` rad): the
desired attitude is then exactly level (`scratchpad/glue/quant.py`, a float32 emulation of
`Vector3f::length`, `normalize`, the dot product and `acosf`; not kernel-checked). In the joint model
(`AttitudeJoint.lean`) a desired-tilt error `δ` (scaled by `g`, m/s²) is the disturbance
`δ · h_c k_v² · (e₆ + h_c e₇ + e₈ − e₉)` (through `es = c − θ_T` into `ω'`, `θ_T'`, the rate error and
the rate PID's target filter). At `δ = 3.38·10⁻³` its `V_j` is `7.1·10⁵` (`quant_V_ge`), while the
hypotheses of `hover_practically_exponentially_stable` with the linear-zone `ν ≤ 1.99·10⁹` force
`c₀ ≤ ν (1 − λ)² ≤ 179.1` (`c₀_le_of_hyps`). So no instance of `HoverGlue` (restricted or not) with
the readout of REACH.md §5 can hold inside the linear zone: `ball_route_floor`. -/

/-- The direction of a desired-tilt error in the joint per-axis model. -/
noncomputable def quantDir : Fin 14 → ℝ := fun i =>
  ((AttJ.hc : ℝ) * (AttJ.kv : ℝ) ^ 2) *
    ![0, 0, 0, 0, 0, 0, 1, (AttJ.hc : ℝ), 1, -1, 0, 0, 0, 0] i

/-- **The quantization disturbance of one tick is large in `V_j`**: `V_j(3.38·10⁻³ · quantDir) ≥ 7·10⁵`. -/
theorem quant_V_ge : 700000 ≤ AttJ.V ((338 / 100000 : ℝ) • quantDir) := by
  simp [AttJ.V, Vertical.qf, AttJ.PjR, AttJ.castM, AttJ.Pj, dotProduct, Matrix.mulVec, quantDir,
    Fin.sum_univ_succ, AttJ.hc, AttJ.kv]
  norm_num

/-- The hypotheses of `hover_practically_exponentially_stable` force `c₀ ≤ ν (1 − λ)²`. -/
theorem c₀_le_of_hyps {κ c₀ ν : ℝ} (hκ : 0 ≤ κ)
    (hν : (lamC + κ / (1 - lamC)) * ν + c₀ / (1 - lamC) ≤ ν) (hν0 : 0 ≤ ν) :
    c₀ ≤ ν * (1 - lamC) ^ 2 := by
  have hl1 : (0 : ℝ) < 1 - lamC := by linarith [lamC_lt_one]
  have hk : 0 ≤ κ / (1 - lamC) := div_nonneg hκ hl1.le
  have h1 : c₀ / (1 - lamC) ≤ ν * (1 - lamC) := by nlinarith
  have := (div_le_iff₀ hl1).1 h1
  nlinarith

/-- **The `Vc`-ball route is infeasible at the code's floor**: under the hypotheses of
`hover_practically_exponentially_stable` and the linear-zone limit `ν ≤ 1.99·10⁹`, the floor `c₀` is
below `Vc` of one tick's tilt-quantization disturbance (on either horizontal axis). -/
theorem ball_route_floor {κ c₀ ν : ℝ} (hκ : 0 ≤ κ) (_hρ : lamC + κ / (1 - lamC) < 1)
    (hν : (lamC + κ / (1 - lamC)) * ν + c₀ / (1 - lamC) ≤ ν) (hν0 : 0 ≤ ν)
    (hzone : ν ≤ 199 / 100 * 10 ^ 9) :
    c₀ < Vc ⟨0, (338 / 100000 : ℝ) • quantDir, 0⟩ := by
  have h1 := c₀_le_of_hyps hκ hν hν0
  have h2 := quant_V_ge
  have hz : AttJ.V 0 = 0 := by simp [AttJ.V, Vertical.qf]
  have hzv : Vertical.V 0 = 0 := by simp [Vertical.V, Vertical.qf]
  have h3 : ν * (1 - lamC) ^ 2 ≤ 199 / 100 * 10 ^ 9 * (1 - lamC) ^ 2 :=
    mul_le_mul_of_nonneg_right hzone (sq_nonneg _)
  simp only [Vc, hz, hzv, mul_zero, add_zero]
  norm_num [lamC] at h1 h3
  linarith

end

end Contracts.Track.Reach
