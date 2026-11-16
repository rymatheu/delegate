import Contracts.Track.Reach.HoverCert
import Contracts.Track.Reach.Leg

/-!
# Hover stability on the loop (REACH.md §8.7)

```
theorem hover_stable (sense32 senseP w₀) (wp p₀ : P3) (ψ₀ : ℝ) (hP : LegParams w₀)
    (hH : HoldWorld w₀ wp) (hd : ∀ i, |(p₀ - wp) i| ≤ 0.021) (hwp : ∀ i, |wp i| ≤ 3.9)
    (hS : Plant.CopterSense sense32 senseP) (hL : LibmSpec)
    (hF : HoverFacts sense32 senseP w₀ wp p₀ ψ₀) :
    Mloop sense32 senseP w₀ ⊨
      ⟨Ahover p₀ ψ₀, {x | ∀ t, ‖p_t − wp‖ ≤ 3.68 · 0.9997ᵗ · ‖p_0 − wp‖ + 0.0036}⟩
```

**Hovering at a fixed position target is a practically exponentially stable equilibrium of the
closed loop**: the controller's world `w₀` holds the target `wp` (the single-waypoint mission
complete, its S-curve finished, `HoldWorld`), the vehicle starts at `p₀` within 2.1 cm of `wp` per
axis, at rest, level, at any heading `ψ₀`, the hover actuators held (`Ahover p₀ ψ₀`); then every
behavior of the loop stays within `3.68 · 0.9997ᵗ · ‖p₀ − wp‖ + 3.6` mm of `wp` (decay time constant
3333 ticks, 8.3 s), and in the box `BoxS` at every tick (`hover_stable_box`).

`HoverFacts` is the one named hypothesis: for every behavior of the loop from the start, the
per-tick facts `HoverRun` (REACH.md §8.7 gives the measured value of each). The proof:

* the horizontal rows of every tick are **derived from the code**: the hold tick hands
  `NE_update_controller` its state (`GlueTick.tick_hold_ps`), the readouts match (`neGlue_hold`),
  M6's `horizontal_tick_eq_D` bounds the controller rows (`wHβ_bound`), the plant row is the
  rigid body's (`prow_ahover`, from `Plant.step_pv_sharp`); what remains of the row is the attitude
  deviation `etaA` from the lag law, whose excess over `0.01` m/s² is a field (`att`);
* the vertical rows are the code part (`vcode`, INDUCTION's `wV_bound`) plus the structured
  disturbance `CtrlV.wS` (tilt coupling through the plant, the sampled specific force and the angle
  boost), whose excess over its floor is a field (`vstruct`);
* the model-level theorem (`hover_box_s`, `hover_axes_s`) with the decay constants `cHd`, `cVd`
  (HoverCert.lean) gives the three axes; `norm_le_axes3` gives the distance.
-/

namespace Contracts.Track.Reach.Hover

open Contracts Contracts.STL Contracts.Mission Matrix Finset Contracts.Track
open Contracts.Track.Induction Contracts.Track.Induction.TG Contracts.Track.Reach.Glue
open Vehicle AC_PosControl_lib AC_PosControl Contracts.Track.CtrlV

noncomputable section

/-! ## Three axes into one distance -/

/-- `‖e‖ ≤ k ‖d‖ + √(Σ uᵢ²) + √(Σ βᵢ²)` from `|eᵢ| ≤ k |dᵢ| + uᵢ + βᵢ`. -/
theorem norm_le_axes3 {e d : EuclideanSpace ℝ (Fin 3)} {k : ℝ} (u β : Fin 3 → ℝ) (hk : 0 ≤ k)
    (hu : ∀ i, 0 ≤ u i) (hβ : ∀ i, 0 ≤ β i) (h : ∀ i, |e i| ≤ k * |d i| + u i + β i) :
    ‖e‖ ≤ k * ‖d‖ + Real.sqrt (u 0 ^ 2 + u 1 ^ 2 + u 2 ^ 2) +
      Real.sqrt (β 0 ^ 2 + β 1 ^ 2 + β 2 ^ 2) := by
  have h1 := norm_le_axes (e := e) (d := d) (fun i => u i + β i) hk
    (fun i => add_nonneg (hu i) (hβ i)) (fun i => by simpa [add_assoc] using h i)
  set U : EuclideanSpace ℝ (Fin 3) := WithLp.toLp 2 u
  set B : EuclideanSpace ℝ (Fin 3) := WithLp.toLp 2 β
  have hU : ‖U‖ = Real.sqrt (u 0 ^ 2 + u 1 ^ 2 + u 2 ^ 2) := by
    rw [EuclideanSpace.norm_eq]; simp [U, Fin.sum_univ_three, sq_abs]
  have hB : ‖B‖ = Real.sqrt (β 0 ^ 2 + β 1 ^ 2 + β 2 ^ 2) := by
    rw [EuclideanSpace.norm_eq]; simp [B, Fin.sum_univ_three, sq_abs]
  have hUB : Real.sqrt ((u 0 + β 0) ^ 2 + (u 1 + β 1) ^ 2 + (u 2 + β 2) ^ 2) = ‖U + B‖ := by
    rw [EuclideanSpace.norm_eq]; simp [U, B, Fin.sum_univ_three, sq_abs]
  have := norm_add_le U B
  rw [hUB] at h1
  linarith

/-! ## The plant row from `Ahover` -/

/-- The quaternion of every behavior of the plant from a hover start is a unit quaternion. -/
theorem qnorm_one_hover {sense32 : ℝ → Float32} {senseP : ℝ → Float} {x : ℕ → Mission.X}
    {p₀ : P3} {ψ₀ : ℝ} (hx : x ∈ Mplant sense32 senseP) (hA : x ∈ Reach.Ahover p₀ ψ₀) (t : ℕ) :
    Plant.qnormSq (x t).phys.x = 1 := by
  induction t with
  | zero =>
    have h0 : (x 0).phys = startP p₀ ψ₀ := hA
    rw [h0]
    simp only [startP, startState, yawQuat, Plant.qnormSq, Plant.State.toX]
    simp
  | succ t ih =>
    rw [(mem_Mplant.1 hx t).1]
    simp only [Plant.next, Plant.nextR]
    rw [Plant.qnormSq_step]; exact ih

/-- **The horizontal position row from a hover start** (`prow_le` with `Ahover`). -/
theorem prow_ahover {sense32 : ℝ → Float32} {senseP : ℝ → Float} {x : ℕ → Mission.X}
    {p₀ : P3} {ψ₀ : ℝ} (hx : x ∈ Mplant sense32 senseP) (hA : x ∈ Reach.Ahover p₀ ψ₀) (t : ℕ)
    (hw : |ph x t 10| ≤ 2 ∧ |ph x t 11| ≤ 2 ∧ |ph x t 12| ≤ 7 / 5) (a : Fin 2) :
    |prow x t a| ≤ 18 / 10 ^ 8 := by
  have hW : Plant.WBd (x t).phys.x 2 := ⟨hw.1, hw.2.1, hw.2.2.trans (by norm_num)⟩
  have h := prow_step (x t).phys.x (Plant.act (x t).out.act) (qnorm_one_hover hx hA t) hW a.castSucc
  have hn := (mem_Mplant.1 hx t).1
  simp only [prow, aReal, ph, hn, Plant.next, Plant.nextR]
  rw [show pIx a.castSucc = Plant.pI a.castSucc from rfl,
    show vIx a.castSucc = Plant.vI a.castSucc from rfl]
  exact h

/-! ## The hold world and the facts -/

/-- **The hold world at `wp`** (the context of the theorem, not used by its proof): the controller
in Auto past the mission's start, the mission complete, the S-curve finished, the position target
at `wp`. A world in this state is what a single-waypoint mission at `wp` reaches after its loiter
S-curve when the vehicle starts at `wp` (the hover campaign's settle phase, REACH.md §8.7). -/
structure HoldWorld (w₀ : Vehicle.World) (wp : P3) : Prop where
  in_auto : w₀.in_auto = true
  started : w₀.au.waiting_to_start = false
  complete : w₀.au.state = .COMPLETE
  finished : AC_WPNav_lib.SCurve.finished w₀.wps._scurve_this_leg = true
  target : !₂[w₀.ps._pos_desired_ned_m.x.toReal, w₀.ps._pos_desired_ned_m.y.toReal,
    w₀.ps._pos_desired_ned_m.z.toReal] = wp

/-- The persistent floor of the structured vertical disturbance `CtrlV.wS` (`εVs − εV`). -/
def εS : Fin 8 → ℝ := ![1 / 10 ^ 9, 1 / 10 ^ 8, 0, 1 / 10 ^ 6, 3 / 10 ^ 10, 0, 2 / 10 ^ 7, 0]

/-- The offset of the start from the target. -/
def offs (wp : P3) (x : ℕ → Mission.X) : Fin 3 → ℝ := fun i => (pos (x 0) - wp) i

/-- The box of the readouts at every tick up to `t`. -/
def BoxTo (w₀ : Vehicle.World) (x : ℕ → Mission.X) (t : ℕ) : Prop :=
  ∀ k, k ≤ t → BoxS (ξV w₀ x) (ξH w₀ x) k

/-- The state the tick `t` hands to `NE_update_controller` on a steady hold tick. -/
abbrev neS (w₀ : Vehicle.World) (x : ℕ → Mission.X) (t : ℕ) (P : AC_WPNav_lib.Vector3p.State)
    (V A : AC_WPNav_lib.Vector3f.State) : State :=
  neIn (Induction.run w₀ x t) (x t).smp P V A

/-- **The per-tick facts of one behavior of the loop from the hover start.** Measured on the hover
campaign (244 displaced holds flown by `copter_ref`, `staging/text/hover-campaign.csv`, REACH.md
§8.7); every assumed number is at least 2 % above the measured one. -/
structure HoverRun (w₀ : Vehicle.World) (wp : P3) (x : ℕ → Mission.X) : Prop where
  /-- **The readouts at the start** besides the offset: at rest (velocity errors `0`), level (the
  lag state and the command history `0` by definition), the controller of the hold relaxed: per
  coordinate within `ε0Vs = (0, 1e-6, 1e-5, 2e-5, 1e-4, 1e-4, 1e-4, 1e-4)` and `ε0Hs = (0, 1e-6,
  1e-5, 1e-4, 1e-5, 1e-5, 1e-4, 1e-4, 1e-4)`. Measured (the readouts at the move, reconstructed
  from the trace with the code's laws): horizontal `0` in every coordinate; vertical `ev 0`,
  `eV ≤ 1.9e-6`, `eA ≤ 1.04e-5`, `I ≤ 1.1e-7`, `f, u, w ≤ 6.3e-8` (in `Mloop` the takeover sets
  `f = u = MOT_THST_HOVER − 1/2.25 = −4.4e-5`). -/
  init : (∀ j, j ≠ 0 → |ξV w₀ x 0 j| ≤ ε0Vs j) ∧ ∀ a j, j ≠ 0 → |ξH w₀ x 0 a j| ≤ ε0Hs j
  /-- **The target is held at `wp`**, with zero velocity and acceleration targets, at every tick.
  Measured: exactly (the largest deviation of the position target from `wp` and the largest
  velocity and acceleration targets over every tick of every run are `0`). -/
  target : ∀ t, posTarget (x t) = wp ∧ velTarget (x t) = 0 ∧ accDes w₀ x t = 0
  /-- **Every tick is a steady hold tick**: Auto mode past the mission's start, the mission not
  running, no speed change requested of the navigator, no terrain following (the hypotheses of
  `GlueTick.tick_hold_ps`). Not observable in the trace; the world's state machine is in `COMPLETE`
  (`HoldWorld`) and nothing of the hold tick starts a mission. -/
  hold : ∀ t, (Induction.run w₀ x t).in_auto = true ∧
    (Induction.run w₀ x t).au.waiting_to_start = false ∧
    (Induction.run w₀ x t).au.state ≠ .RUNNING ∧
    SpeedSteady (preNav (Induction.run w₀ x t) (x t).smp).wpp
      (preNav (Induction.run w₀ x t) (x t).smp).wps ∧
    (preNav (Induction.run w₀ x t) (x t).smp).wps._is_terrain_alt = false
  /-- **The horizontal controller's region** (C15: `NE_update_controller` on its region
  `HCtl.NERegion`, the vertical controller active after it), while the box has held: no EKF reset,
  the gains, the offsets zero, finite floats, `‖e‖ ≤ 0.4`, targets and estimates within their
  bounds, the PID's state, the command below the acceleration limit. Observable parts measured:
  `‖e‖ ≤ 0.0297`, speed `≤ 0.0343` m/s, command `≤ 0.434` m/s² against the limit. -/
  ne : ∀ t, BoxTo w₀ x t → ∀ P V A,
    (navW (preNav (Induction.run w₀ x t) (x t).smp)).ps =
        NE_update_controller (preNav (Induction.run w₀ x t) (x t).smp).pp (neS w₀ x t P V A)
          (posInputs (spoolW (preNav (Induction.run w₀ x t) (x t).smp))) →
      HCtl.NERegion (preNav (Induction.run w₀ x t) (x t).smp).pp (neS w₀ x t P V A)
          (posInputs (spoolW (preNav (Induction.run w₀ x t) (x t).smp))) ∧
        D_is_active (D_handle_ekf_reset (NE_update_controller
            (preNav (Induction.run w₀ x t) (x t).smp).pp (neS w₀ x t P V A)
            (posInputs (spoolW (preNav (Induction.run w₀ x t) (x t).smp))))
            (posInputs (navW (preNav (Induction.run w₀ x t) (x t).smp))))
          (posInputs (navW (preNav (Induction.run w₀ x t) (x t).smp))) = true
  /-- **The body rates** while the box has held: `|p|, |q| ≤ 2`, `|r| ≤ 1.4` rad/s (the hypothesis
  of the plant's position row). Measured: `0.285`, `0.282`, `1.1e-4` rad/s. -/
  rates : ∀ t, BoxTo w₀ x t → |ph x t 10| ≤ 2 ∧ |ph x t 11| ≤ 2 ∧ |ph x t 12| ≤ 7 / 5
  /-- **The attitude deviation from the lag law** (`etaA = aReal − aLag`, HORIZONTAL.md §7), while
  the box has held: its excess over `εη = 0.01` m/s², summed with the weights `λ^(-(k+1))`, is at
  most `226 · ‖d‖∞`. Measured: the deviation reaches `0.0584` m/s² at a corner start (the field of
  the earlier glue, `|etaA| ≤ 0.01` at every tick, was **false**), at most `0.00395` after the
  transient; the excess ends by tick 237 and its weighted sum is at most `220.75 · ‖d‖∞`. -/
  att : ∀ N, (∀ k < N, BoxS (ξV w₀ x) (ξH w₀ x) k) → ∀ a,
    wsum (fun k => exc (etaA w₀ x k a) (1 / 100)) N ≤ κη * dinf (offs wp x)
  /-- **The code part of the vertical rows** (INDUCTION's `vglue` with `wV_bound`: the C-series
  join `CtrlV.vertical_tick_split` at the box's magnitudes), while the box has held: the row minus
  the structured disturbance `wSv` within `εV = (1e-10, 2.5e-8, 2e-7, 4e-6, 2e-7, 1e-7, 3.2e-6,
  4e-7)`. Stated on the rows rather than as `VGlue` because `VTickHyp.ht0` (`ticks32 ≠ 0`) fails
  at the tick-counter wrap, where the tick computes the same loop time
  (`GlueTick.schedW_loop_time`). Not observable (float rounding); the reconstruction of the code's
  laws reproduces the logged command within `4.5e-7`. -/
  vcode : ∀ t, BoxTo w₀ x t → ∀ j,
    |(ξV w₀ x (t + 1) - Vertical.AvR *ᵥ ξV w₀ x t - wSv w₀ x t) j| ≤ εV j
  /-- **The structured vertical disturbance** `CtrlV.wS` (plant residuals `ρz`, `ρv` of the tilted
  thrust, the sampled specific force's residual `ρam` through the acceleration filter, the angle
  boost `τ`), while the box has held: its excess over `εS = (1e-9, 1e-8, 0, 1e-6, 3e-10, 0, 2e-7, 0)`,
  summed with the weights `λ^(-(k+1))`, is at most `κV j · ‖d‖∞`, `κV = (8.1e-4, 0.035, 0, 3.32,
  8.3e-4, 0, 0.8, 0)`. Measured: the rows reach `6.9e-8, 1.02e-5, 0, 9.8e-4, 2.4e-7, 0, 2.3e-4, 0`
  at a corner start (the earlier per-tick bound `εVh` was **false** in rows 0, 1, 3, 4, 6); after
  the transient `1.2e-10, 1.9e-9, 0, 3.2e-7, 8.1e-11, 0, 5.0e-8, 0`; the excess ends by tick 919;
  weighted sums at most `(7.86e-4, 0.0339, 0, 3.245, 8.10e-4, 0, 0.779, 0) · ‖d‖∞`. -/
  vstruct : ∀ N, (∀ k < N, BoxS (ξV w₀ x) (ξH w₀ x) k) → ∀ j,
    wsum (fun k => exc (wSv w₀ x k j) (εS j)) N ≤ κV j * dinf (offs wp x)

/-- **The facts of hover** (the one named hypothesis of `hover_stable`): `HoverRun` for every
behavior of the loop from the start. -/
structure HoverFacts (sense32 : ℝ → Float32) (senseP : ℝ → Float) (w₀ : Vehicle.World) (wp p₀ : P3)
    (ψ₀ : ℝ) : Prop where
  /-- The per-tick facts of every behavior from the hover start. -/
  run : ∀ x ∈ Mloop sense32 senseP w₀ ∩ Reach.Ahover p₀ ψ₀, HoverRun w₀ wp x

/-! ## From the facts to the model -/

section Rows

variable {sense32 : ℝ → Float32} {senseP : ℝ → Float} {w₀ : Vehicle.World} {wp p₀ : P3} {ψ₀ : ℝ}
  {x : ℕ → Mission.X}

theorem pos_zero (hA : x ∈ Reach.Ahover p₀ ψ₀) : pos (x 0) = p₀ := by
  have h0 : (x 0).phys = startP p₀ ψ₀ := hA
  ext i
  fin_cases i <;> simp [pos, h0, startP, startState, Plant.State.toX]

/-- With the target held, the forcing of the readouts is zero. -/
theorem forceH_zero (hR : HoverRun w₀ wp x) (t : ℕ) (a : Fin 2) :
    Horizontal.forceOf (refH w₀ x a) t = 0 := by
  obtain ⟨p0, v0, a0⟩ := hR.target t
  obtain ⟨p1, v1, -⟩ := hR.target (t + 1)
  have hv0 : velTarget (x t) a.castSucc = 0 := by rw [v0]; rfl
  have hv1 : velTarget (x (t + 1)) a.castSucc = 0 := by rw [v1]; rfl
  have ha0 : accDes w₀ x t a.castSucc = 0 := by rw [a0]; rfl
  ext j
  simp [Horizontal.forceOf, refH, refAx, p0, p1, hv0, hv1, ha0, Horizontal.defect₁,
    Horizontal.defect₂]

theorem forceV_zero (hR : HoverRun w₀ wp x) (t : ℕ) : Vertical.forceOf (refV w₀ x) t = 0 := by
  obtain ⟨p0, v0, a0⟩ := hR.target t
  obtain ⟨p1, v1, -⟩ := hR.target (t + 1)
  have hv0 : velTarget (x t) 2 = 0 := by rw [v0]; rfl
  have hv1 : velTarget (x (t + 1)) 2 = 0 := by rw [v1]; rfl
  have ha0 : accDes w₀ x t 2 = 0 := by rw [a0]; rfl
  ext j
  simp [Vertical.forceOf, refV, refAx, p0, p1, hv0, hv1, ha0, Vertical.defect₁, Vertical.defect₂]

/-- **The horizontal rows of a tick from the code** (while the box has held up to it): the
controller and plant rows within `εHβ` (`neGlue_hold`, `wHβ_bound`, `prow_ahover`), so the row is
within `εHβ` plus the attitude deviation through `eAcc`. -/
theorem rowH_code (hL : LibmSpec) (hS : Plant.CopterSense sense32 senseP)
    (hx : x ∈ Mloop sense32 senseP w₀) (hA : x ∈ Reach.Ahover p₀ ψ₀) (hR : HoverRun w₀ wp x)
    (hwp : ∀ i : Fin 2, |wp i.castSucc| ≤ 39 / 10) (t : ℕ) (hB : BoxTo w₀ x t) (a : Fin 2) (j : Fin 9) :
    |(ξH w₀ x (t + 1) a - Horizontal.AhR *ᵥ ξH w₀ x t a) j| ≤
      εHβ j + eAcc j * |etaA w₀ x t a| := by
  obtain ⟨hin, hws, hst, hSS, hT⟩ := hR.hold t
  obtain ⟨P, V, A, heq, himp⟩ := neGlue_hold hL hx.2 t hin hws hst hSS hT
  obtain ⟨hreg, hD⟩ := hR.ne t hB P V A heq
  have hg : NEGlue w₀ x t := himp hreg hD
  have hBt := (hB t le_rfl).2
  have hrow : ∀ b, |prow x t b| ≤ 18 / 10 ^ 8 := prow_ahover hx.1 hA t (hR.rates t hB)
  obtain ⟨p0, v0, -⟩ := hR.target t
  have hv : ∀ b : Fin 2, |ph x t (vIx b.castSucc)| ≤ 2 := by
    intro b
    have h1 := hBt b 1
    have e : outH 1 ⬝ᵥ ξH w₀ x t b = ph x t (vIx b.castSucc) := by
      have := ξH_one w₀ x t b
      rw [v0] at this
      simp [outH, dotProduct, Pi.single_apply, this]
    rw [e] at h1
    exact h1.trans (by simp [bHs]; norm_num)
  have hp : ∀ b : Fin 2, |ph x t (pIx b.castSucc)| ≤ 4 := by
    intro b
    have h1 := hBt b 0
    have e : outH 0 ⬝ᵥ ξH w₀ x t b = ph x t (pIx b.castSucc) - wp b.castSucc := by
      have := ξH_zero w₀ x t b
      rw [p0] at this
      simp [outH, dotProduct, Pi.single_apply, this]
    rw [e] at h1
    have h2 : |(1 : ℝ) / 10| = 1 / 10 := by norm_num
    have hb : bHs 0 = 1 / 10 := by simp [bHs]
    rw [hb] at h1
    have h3 := hwp b
    have := abs_sub_abs_le_abs_sub (ph x t (pIx b.castSucc)) (wp b.castSucc)
    linarith
  have hW := wHβ_bound hL hS hx.1 t hg hrow hv hp a j
  have e : (ξH w₀ x (t + 1) a - Horizontal.AhR *ᵥ ξH w₀ x t a) j =
      wHβ w₀ x t a j + etaA w₀ x t a * eAcc j := by
    simp only [wHβ, forceH_zero hR t a, Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      Pi.zero_apply]
    ring
  rw [e]
  have he : 0 ≤ eAcc j := by fin_cases j <;> norm_num [eAcc, Plant.h]
  calc |wHβ w₀ x t a j + etaA w₀ x t a * eAcc j| ≤ |wHβ w₀ x t a j| + |etaA w₀ x t a * eAcc j| :=
        abs_add_le _ _
    _ ≤ εHβ j + eAcc j * |etaA w₀ x t a| := by
        rw [abs_mul, abs_of_nonneg he, mul_comm]; linarith

/-- The floor `εHs` covers the code part and `εη = 0.01` through `eAcc`. -/
theorem εHs_split (j : Fin 9) : εHβ j + eAcc j * (1 / 100) ≤ εHs j := by
  fin_cases j <;> simp [εHβ, εHs, εHh, eAcc, Plant.h] <;> norm_num

/-- The floor `εVs` is the code part plus `εS`. -/
theorem εVs_split (j : Fin 8) : εV j + εS j ≤ εVs j := by
  fin_cases j <;> simp [εV, εS, εVs] <;> norm_num

theorem excH_le (hL : LibmSpec) (hS : Plant.CopterSense sense32 senseP)
    (hx : x ∈ Mloop sense32 senseP w₀) (hA : x ∈ Reach.Ahover p₀ ψ₀) (hR : HoverRun w₀ wp x)
    (hwp : ∀ i : Fin 2, |wp i.castSucc| ≤ 39 / 10) (t : ℕ) (hB : BoxTo w₀ x t) (a : Fin 2) (j : Fin 9) :
    exc ((ξH w₀ x (t + 1) a - Horizontal.AhR *ᵥ ξH w₀ x t a) j) (εHs j) ≤
      eAcc j * exc (etaA w₀ x t a) (1 / 100) := by
  have h1 := rowH_code hL hS hx hA hR hwp t hB a j
  have h2 := εHs_split j
  have he : 0 ≤ eAcc j := by fin_cases j <;> norm_num [eAcc, Plant.h]
  unfold exc
  refine max_le ?_ (mul_nonneg he (le_max_right _ _))
  have := le_max_left (|etaA w₀ x t a| - 1 / 100) 0
  nlinarith

theorem excV_le (hR : HoverRun w₀ wp x) (t : ℕ) (hB : BoxTo w₀ x t) (j : Fin 8) :
    exc ((ξV w₀ x (t + 1) - Vertical.AvR *ᵥ ξV w₀ x t) j) (εVs j) ≤ exc (wSv w₀ x t j) (εS j) := by
  have h1 := hR.vcode t hB j
  have h2 := εVs_split j
  apply exc_le_of
  have e : (ξV w₀ x (t + 1) - Vertical.AvR *ᵥ ξV w₀ x t) j =
      (ξV w₀ x (t + 1) - Vertical.AvR *ᵥ ξV w₀ x t - wSv w₀ x t) j + wSv w₀ x t j := by
    simp only [Pi.sub_apply]; ring
  rw [e]
  have := abs_add_le ((ξV w₀ x (t + 1) - Vertical.AvR *ᵥ ξV w₀ x t - wSv w₀ x t) j) (wSv w₀ x t j)
  linarith

/-- A pointwise bound passes to the weighted sums. -/
theorem wsum_le_wsum {s s' : ℕ → ℝ} (N : ℕ) (h : ∀ k < N, s k ≤ s' k) : wsum s N ≤ wsum s' N := by
  unfold wsum
  refine Finset.sum_le_sum fun k hk => ?_
  exact div_le_div_of_nonneg_right (h k (mem_range.mp hk)) (pow_pos lam_pos _).le

theorem wsum_mul (c : ℝ) (s : ℕ → ℝ) (N : ℕ) : wsum (fun k => c * s k) N = c * wsum s N := by
  unfold wsum; rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun k _ => ?_; ring

/-- **The model of the readouts**, from the facts. -/
theorem hoverModelS_of_run (hL : LibmSpec) (hS : Plant.CopterSense sense32 senseP)
    (hx : x ∈ Mloop sense32 senseP w₀) (hA : x ∈ Reach.Ahover p₀ ψ₀) (hR : HoverRun w₀ wp x)
    (hwp : ∀ i : Fin 2, |wp i.castSucc| ≤ 39 / 10) :
    HoverModelS (ξV w₀ x) (fun t => ξV w₀ x (t + 1) - Vertical.AvR *ᵥ ξV w₀ x t) (ξH w₀ x)
      (fun t a => ξH w₀ x (t + 1) a - Horizontal.AhR *ᵥ ξH w₀ x t a) 0 (offs wp x) where
  stepV t _ := by abel
  stepH t _ a := by abel
  initV j := by
    by_cases hj : j = 0
    · subst hj
      rw [ξV_pos w₀ x 0 wp (hR.target 0).1]
      simp [ε0Vs, offs]
    · rw [Pi.single_eq_of_ne hj, sub_zero]; exact hR.init.1 j hj
  initH a j := by
    by_cases hj : j = 0
    · subst hj
      rw [ξH_pos w₀ x 0 wp (hR.target 0).1 a]
      simp [ε0Hs, ε0Hh, offs]
    · rw [Pi.single_eq_of_ne hj, sub_zero]; exact hR.init.2 a j hj
  sumV N hB j := by
    refine (wsum_le_wsum N fun k hk => ?_).trans (hR.vstruct N (fun k hk => by simpa using hB k hk) j)
    simp only [zero_add]
    exact excV_le hR k (fun k' hk' => by simpa using hB k' (by omega)) j
  sumH N hB a j := by
    have h1 : wsum (fun k => exc ((ξH w₀ x (0 + k + 1) a - Horizontal.AhR *ᵥ ξH w₀ x (0 + k) a) j)
        (εHs j)) N ≤ wsum (fun k => eAcc j * exc (etaA w₀ x k a) (1 / 100)) N := by
      refine wsum_le_wsum N fun k hk => ?_
      simp only [zero_add]
      exact excH_le hL hS hx hA hR hwp k (fun k' hk' => by simpa using hB k' (by omega)) a j
    have he : 0 ≤ eAcc j := by fin_cases j <;> norm_num [eAcc, Plant.h]
    refine h1.trans ?_
    rw [wsum_mul, κH_eq]
    have := mul_le_mul_of_nonneg_left (hR.att N (fun k hk => by simpa using hB k hk) a) he
    linarith

end Rows

/-! ## The theorem -/

/-- **Hover is practically exponentially stable on the loop.** From the hold world at `wp`, every
behavior from a start at rest, level, at any heading, within 2.1 cm of `wp` per axis stays within
`3.68 · 0.9997ᵗ · ‖p_0 − wp‖ + 3.6` mm of `wp` at every tick. -/
theorem hover_stable (sense32 : ℝ → Float32) (senseP : ℝ → Float) (w₀ : Vehicle.World)
    (wp p₀ : P3) (ψ₀ : ℝ) (_hP : Leg.LegParams w₀) (_hH : HoldWorld w₀ wp)
    (hd : ∀ i, |(p₀ - wp) i| ≤ 21 / 1000) (hwp : ∀ i : Fin 2, |wp i.castSucc| ≤ 39 / 10)
    (hS : Plant.CopterSense sense32 senseP) (hL : LibmSpec)
    (hF : HoverFacts sense32 senseP w₀ wp p₀ ψ₀) :
    Mloop sense32 senseP w₀ ⊨
      ⟨Reach.Ahover p₀ ψ₀, {x | ∀ t, dist (pos (x t)) wp ≤
        368 / 100 * (9997 / 10000 : ℝ) ^ t * dist (pos (x 0)) wp + 36 / 10000}⟩ := by
  rintro x ⟨hx, hA⟩ t
  have hR := hF.run x ⟨hx, hA⟩
  have hM := hoverModelS_of_run hL hS hx hA hR hwp
  have hd' : ∀ i, |offs wp x i| ≤ dMax := by
    intro i; simp only [offs, pos_zero hA, dMax]; exact hd i
  obtain ⟨hH, hV⟩ := hover_axes_s hM hd' cHd cVd respH_cHd respV_cVd t
  simp only [zero_add] at hH hV
  set D := pos (x 0) - wp with hDdef
  have hnd : dinf (offs wp x) ≤ ‖D‖ := by
    refine dinf_le fun i => ?_
    simpa [offs, D] using PiLp.norm_apply_le D i
  have hl0 : 0 ≤ lam ^ t := pow_nonneg lam_pos.le t
  have hlv : (Vertical.lamv : ℝ) ^ t ≤ lam ^ t := pow_le_pow_left₀ lamv_nonneg lamv_le t
  have hmH := mH_le
  have hmV := mV_le
  have hmH0 : 0 ≤ ∑ j, cHd j * κH j := by
    refine Finset.sum_nonneg fun j _ => mul_nonneg ?_ (κH_nonneg j)
    fin_cases j <;> simp [cHd] <;> norm_num
  have hmV0 : 0 ≤ ∑ j, cVd j * κV j := by
    refine Finset.sum_nonneg fun j _ => mul_nonneg ?_ (κV_nonneg j)
    fin_cases j <;> simp [cVd] <;> norm_num
  have hD0 := dinf_nonneg (offs wp x)
  -- the three axes
  set uH := lam ^ t * (1438 / 10000 * ‖D‖)
  set uV := lam ^ t * (274 / 10000 * ‖D‖)
  have hax : ∀ i, |(pos (x t) - wp) i| ≤ 347 / 100 * lam ^ t * |D i| +
      ![uH, uH, uV] i + ![251 / 100000, 251 / 100000, 35 / 100000] i := by
    have hDn := norm_nonneg D
    intro i
    fin_cases i
    · have h := hH 0
      have e0 : outH 0 ⬝ᵥ ξH w₀ x t 0 = (pos (x t) - wp) 0 := by
        have h0 : ξH w₀ x t 0 0 = (pos (x t) - wp) 0 := ξH_pos w₀ x t wp (hR.target t).1 0
        simp [outH, dotProduct, Pi.single_apply, h0]
      rw [e0] at h
      have h2 : lam ^ t * ((∑ j, cHd j * κH j) * dinf (offs wp x)) ≤ uH :=
        mul_le_mul_of_nonneg_left (mul_le_mul hmH hnd hD0 (by norm_num)) hl0
      have hd0 : (offs wp x) (0 : Fin 2).castSucc = D 0 := by simp [offs, D]
      rw [hd0] at h
      simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero]
      linarith
    · have h := hH 1
      have e0 : outH 0 ⬝ᵥ ξH w₀ x t 1 = (pos (x t) - wp) 1 := by
        have h0 : ξH w₀ x t 1 0 = (pos (x t) - wp) 1 := ξH_pos w₀ x t wp (hR.target t).1 1
        simp [outH, dotProduct, Pi.single_apply, h0]
      rw [e0] at h
      have h2 : lam ^ t * ((∑ j, cHd j * κH j) * dinf (offs wp x)) ≤ uH :=
        mul_le_mul_of_nonneg_left (mul_le_mul hmH hnd hD0 (by norm_num)) hl0
      have hd0 : (offs wp x) (1 : Fin 2).castSucc = D 1 := by simp [offs, D]
      rw [hd0] at h
      simp only [Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_zero]
      linarith
    · have h := hV
      have e0 : outV 0 ⬝ᵥ ξV w₀ x t = (pos (x t) - wp) 2 := by
        rw [← ξV_pos w₀ x t wp (hR.target t).1]; simp [outV, dotProduct, Pi.single_apply]
      rw [e0] at h
      have h2 : lam ^ t * ((∑ j, cVd j * κV j) * dinf (offs wp x)) ≤ uV :=
        mul_le_mul_of_nonneg_left (mul_le_mul hmV hnd hD0 (by norm_num)) hl0
      have hd2 : offs wp x 2 = D 2 := by simp [offs, D]
      rw [hd2] at h
      have h3 : 1452 / 1000 * (Vertical.lamv : ℝ) ^ t * |D 2| ≤ 347 / 100 * lam ^ t * |D 2| := by
        apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
        nlinarith [pow_nonneg lamv_nonneg t]
      simp only [Fin.reduceFinMk, Fin.isValue, Matrix.cons_val]
      linarith
  have key := norm_le_axes3 (e := pos (x t) - wp) (d := D) ![uH, uH, uV]
    ![251 / 100000, 251 / 100000, 35 / 100000] (by positivity)
    (fun i => by fin_cases i <;> simp [uH, uV] <;> positivity)
    (fun i => by fin_cases i <;> simp <;> norm_num) hax
  rw [dist_eq_norm, dist_eq_norm]
  refine key.trans ?_
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons]
  have hs1 : Real.sqrt (uH ^ 2 + uH ^ 2 + uV ^ 2) ≤ lam ^ t * (21 / 100 * ‖D‖) := by
    rw [Real.sqrt_le_left (by positivity)]
    simp only [uH, uV]
    have hDn := norm_nonneg D
    have : (1438 / 10000 : ℝ) ^ 2 + (1438 / 10000) ^ 2 + (274 / 10000) ^ 2 ≤ (21 / 100) ^ 2 := by
      norm_num
    nlinarith [mul_nonneg (mul_nonneg hl0 hl0) (mul_nonneg hDn hDn)]
  have hs2 : Real.sqrt ((251 / 100000 : ℝ) ^ 2 + (251 / 100000) ^ 2 + (35 / 100000) ^ 2) ≤
      36 / 10000 := by
    rw [Real.sqrt_le_left (by norm_num)]; norm_num
  have hl : lam = 9997 / 10000 := rfl
  rw [← hl]
  nlinarith [norm_nonneg D]


/-- **The box at every tick** (the companion of `hover_stable`): position errors `≤ 0.1`, velocity
errors `≤ 0.5`, integrators, throttle filter and `_throttle_in` within their bounds, the horizontal
command `≤ 0.5` m/s² and its change `≤ 0.075` per tick. -/
theorem hover_stable_box (sense32 : ℝ → Float32) (senseP : ℝ → Float) (w₀ : Vehicle.World)
    (wp p₀ : P3) (ψ₀ : ℝ) (hd : ∀ i, |(p₀ - wp) i| ≤ 21 / 1000)
    (hwp : ∀ i : Fin 2, |wp i.castSucc| ≤ 39 / 10)
    (hS : Plant.CopterSense sense32 senseP) (hL : LibmSpec)
    (hF : HoverFacts sense32 senseP w₀ wp p₀ ψ₀) :
    Mloop sense32 senseP w₀ ⊨
      ⟨Reach.Ahover p₀ ψ₀, {x | ∀ t, BoxS (ξV w₀ x) (ξH w₀ x) t}⟩ := by
  rintro x ⟨hx, hA⟩ t
  have hM := hoverModelS_of_run hL hS hx hA (hF.run x ⟨hx, hA⟩) hwp
  have hd' : ∀ i, |offs wp x i| ≤ dMax := by
    intro i; simp only [offs, pos_zero hA, dMax]; exact hd i
  simpa using hover_box_s hM hd' t

/-- **Nonvacuity**: the loop has behaviors from every hover start (any world, ports, `p₀`, `ψ₀`). -/
theorem hover_stable_nonvacuous (sense32 : ℝ → Float32) (senseP : ℝ → Float) (w₀ : Vehicle.World)
    (p₀ : P3) (ψ₀ : ℝ) : (Mloop sense32 senseP w₀ ∩ Reach.Ahover p₀ ψ₀).Nonempty :=
  Leg.waypoint_reach_h_nonvacuous sense32 senseP w₀ p₀ ψ₀

end

end Contracts.Track.Reach.Hover
