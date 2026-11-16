import Contracts.Track.Reach.Model
import Contracts.Mission.Theorem

/-!
# The statements on the closed loop `Mloop` (REACH.md §5)

* `ReachParams`, `ReachWorld`: the world of a single-waypoint mission to `w'` (MissionParams'
  shape: explicit equalities of the fields the proofs read, the mission array `#[w']`).
* `Ahover p₀ ψ₀`: at tick 0 the vehicle hovers at `p₀`: at rest, level with heading `ψ₀` (any),
  hover actuators held (`startP p₀ ψ₀`, as `Atakeoff` but at `p₀`).
* `ReachGoal r w'`: `∃ T, ∀ t ≥ T, ‖p_t − w'‖ ≤ r` (STL `◇□ near w' r`, unbounded).
* `waypoint_reach_nonvacuous`: `Mloop ∩ Ahover p₀ ψ₀` is nonempty for every world, every pair of
  ports, every `p₀`, `ψ₀` (the joint step iterated).
* **The missing fact, as Lean propositions.** `HoverGlue` and `ReachFacts` state what the closed loop
  must be shown to satisfy, tick by tick, for the model theorems to apply: the existence of the
  composite error state of the loop (read off `Vehicle.tick`'s world and the plant), its position
  coordinates equal to `pos − target`, and its one-tick model step with a bounded disturbance on the
  region (`HoverGlue`); the code facts of the clock and the closed-loop convergence facts along
  `navProgress` (`ReachFacts`). Neither is proved: they are the tick glue of INDUCTION.md §3
  (`ne_glue`, `vglue`, `attitude_tracks`, `CtrlInv`, `NavInv`), extended to unbounded time.
* `hover_practically_exponentially_stable`: from `HoverGlue`, the loop statement
  `‖p_t − w‖ ≤ c (√ρ)ᵗ ‖p₀ − w‖ + b` on `Mloop` (conditional on `HoverGlue`).
* `waypoint_reach_of_facts`: from `ReachFacts`, `Mloop ⊨ ⟨Ahover p₀ ψ₀, ReachGoal r w'⟩` (conditional).
-/

namespace Contracts.Track.Reach

open Contracts Contracts.STL Contracts.Lift Contracts.Mission Filter Topology

noncomputable section

/-! ## The world, the assumption, the goal -/

/-- The parameters of a single-waypoint world: the mission is the one waypoint `w'` (doubles), the
other fields as in `MissionParams`. -/
structure ReachParams (w : Vehicle.World) (w' : AC_WPNav_lib.Vector3p.State) : Prop where
  mission : w.mission = #[w']
  wpp : w.wpp = MissionData.wppC
  kp_ne : w.pp._p_pos_ne_m._kp = 1.5
  kp_d : w.pp._p_pos_d_m._kp = 1
  jerk_ne : w.pp._shaping_jerk_ne_msss = 5
  rate_r : w.ap._ang_vel_roll_max_degs = 0
  rate_p : w.ap._ang_vel_pitch_max_degs = 0
  acc_r : w.ap._accel_roll_max_degss = 1800
  acc_p : w.ap._accel_pitch_max_degss = 1800
  input_tc : w.ap._input_tc = 0.05
  kimax_rr : w.ap._pid_rate_roll._kimax = 0.5
  kimax_rp : w.ap._pid_rate_pitch._kimax = 0.5
  kimax_ry : w.ap._pid_rate_yaw._kimax = 0.5
  kimax_vd : w.pp._pid_vel_d_m._kimax = 10
  kimax_ad : w.pp._pid_accel_d_m._kimax = 0.8

/-- **The single-waypoint world**: booted from some parameter lines, with the parameters of
`ReachParams`. -/
structure ReachWorld (w₀ : Vehicle.World) (w' : AC_WPNav_lib.Vector3p.State) : Prop where
  built : ∃ lines w, Vehicle.construct lines = .ok w ∧ w₀ = Vehicle.boot w
  params : ReachParams w₀ w'

/-- The waypoint as a point of NED space. -/
def wpt (w' : AC_WPNav_lib.Vector3p.State) : P3 := !₂[w'.x.toReal, w'.y.toReal, w'.z.toReal]

/-- **The hover assumption**: at tick 0 the vehicle hovers at `p₀`, at rest, level with heading
`ψ₀` (any), hover actuators held. -/
def Ahover (p₀ : P3) (ψ₀ : ℝ) : Set (ℕ → X) := {x | (x 0).phys = startP p₀ ψ₀}

/-- **The reach goal** `◇□ (‖p − w'‖ ≤ r)`, unbounded. -/
def ReachGoal (r : ℝ) (w' : P3) : Set (ℕ → X) := {x | ∃ T, ∀ t ≥ T, dist (pos (x t)) w' ≤ r}

theorem pos_startP (p : P3) (ψ : ℝ) (x : X) (h : x.phys = startP p ψ) : pos x = p := by
  ext i; fin_cases i <;> simp [pos, h, startP, startState, Plant.State.toX]

/-! ## Nonvacuity -/

/-- The behavior of the loop from hover at `p₀` with heading `ψ₀`. -/
def witnessAt (sense32 : ℝ → Float32) (senseP : ℝ → Float) (w₀ : Vehicle.World) (p₀ : P3)
    (ψ₀ : ℝ) : ℕ → X :=
  fun t => (jointStep sense32 senseP w₀
    (runState (jointStep sense32 senseP w₀) (startP p₀ ψ₀, none) (fun _ => ()) t) ()).2

/-- **Nonvacuity**: for every world, every pair of ports, every hover point and heading, the loop has
a behavior from hover. -/
theorem waypoint_reach_nonvacuous (sense32 : ℝ → Float32) (senseP : ℝ → Float)
    (w₀ : Vehicle.World) (p₀ : P3) (ψ₀ : ℝ) :
    (Mloop sense32 senseP w₀ ∩ Ahover p₀ ψ₀).Nonempty :=
  ⟨witnessAt sense32 senseP w₀ p₀ ψ₀, ⟨mem_Mplant.2 fun t => ⟨rfl, rfl⟩,
    ⟨fun t => (runState (jointStep sense32 senseP w₀) (startP p₀ ψ₀, none) (fun _ => ()) t).2, rfl,
      fun t => rfl⟩⟩, rfl⟩

/-! ## Hover: the glue and the loop statement -/

/-- **The tick glue of hover (open).** Every behavior of the loop has a composite error state `ξ`
(vertical block and the two joint horizontal–attitude axes, read off the controller's world and the
plant) whose position coordinates are `pos − wp`, which starts as the pure position offset, and
which follows the composite model with a disturbance bounded on `D = {Vc ≤ ν}` by `κ Vc + c₀`. -/
def HoverGlue (sense32 : ℝ → Float32) (senseP : ℝ → Float) (w₀ : Vehicle.World) (wp : P3)
    (κ c₀ ν : ℝ) : Prop :=
  ∀ x ∈ Mloop sense32 senseP w₀, ∃ (ξ w : ℕ → CS) (σn σe : ℕ → Fin 2),
    ξ 0 = pureOffset (pos (x 0) - wp) ∧ (∀ t, posErr (ξ t) = pos (x t) - wp) ∧
      (∀ t, ξ (t + 1) = cstep (σn t) (σe t) (ξ t) (w t)) ∧
      ∀ t, Vc (ξ t) ≤ ν → Vc (w t) ≤ κ * Vc (ξ t) + c₀

/-- **Hover is a practically exponentially stable equilibrium of the closed loop**, conditional on
the open tick glue `HoverGlue`: from hover at `p₀` with `10¹⁵ ‖p₀ − w‖² ≤ ν` (inside `D`), any
heading, `‖p_t − w‖ ≤ c (√ρ)ᵗ ‖p₀ − w‖ + b` for all `t`, with `c = √(10¹⁵ γ_e) ≤ 37.93`
(`c_hover_le`), `ρ = λ + κ/(1 − λ)`, `λ = 0.9997`, `b = √(γ_e c₀/((1 − λ)(1 − ρ)))`. -/
theorem hover_practically_exponentially_stable (sense32 : ℝ → Float32) (senseP : ℝ → Float)
    (w₀ : Vehicle.World) (wp : P3) {κ c₀ ν : ℝ} (hκ : 0 ≤ κ) (hc₀ : 0 ≤ c₀)
    (hρ : lamC + κ / (1 - lamC) < 1) (hν : (lamC + κ / (1 - lamC)) * ν + c₀ / (1 - lamC) ≤ ν)
    (hG : HoverGlue sense32 senseP w₀ wp κ c₀ ν) :
    Mloop sense32 senseP w₀ ⊨
      ⟨{x | ∃ p₀ ψ₀, x ∈ Ahover p₀ ψ₀ ∧ 10 ^ 15 * ‖p₀ - wp‖ ^ 2 ≤ ν},
       {x | ∀ t, dist (pos (x t)) wp ≤
          Real.sqrt (10 ^ 15 * γe) * Real.sqrt (lamC + κ / (1 - lamC)) ^ t * dist (pos (x 0)) wp +
            Real.sqrt (γe * (c₀ / ((1 - lamC) * (1 - (lamC + κ / (1 - lamC))))))}⟩ := by
  rintro x ⟨hx, p₀, ψ₀, hA, hD⟩
  obtain ⟨ξ, w, σn, σe, h0, hpos, hstep, hw⟩ := hG x hx
  have hp0 : pos (x 0) = p₀ := pos_startP p₀ ψ₀ (x 0) hA
  intro t
  have := (hover_pes_model σn σe ξ w (pos (x 0)) wp hκ hc₀ hρ hν hstep hw h0
    (by rw [hp0]; exact hD) t).2
  rw [hpos t] at this
  simpa [dist_eq_norm] using this

/-! ## Reach: the facts and the loop statement -/

/-- The track scaler stored after tick `t` (`_track_dt_scalar` of the controller's world after the
tick): the summand of `navProgress`. -/
def scRun (w₀ : Vehicle.World) (x : ℕ → X) (t : ℕ) : ℝ :=
  (ctrlWorld w₀ x (t + 1)).wps._track_dt_scalar.toReal

/-- `navProgress` is the sum of the stored scalers: `q (t+1) = q t + s (t+1)` exactly. -/
theorem navProgress_succ (w₀ : Vehicle.World) (x : ℕ → X) (t : ℕ) :
    navProgress w₀ x (t + 1) = navProgress w₀ x t + scRun w₀ x (t + 1) := by
  simp only [navProgress, scRun]
  rw [Finset.sum_range_succ]

/-- **The facts of the single-waypoint loop (open).** For every behavior of the loop from hover:
the code facts of the clock (the stored scaler `≥ 0`, `code_filter_nonneg`; the filter of the raw
scaler `r`, `code_filter_step`), a path `Γ` of the target in S-curve time and a stall set `Z` within
`d_Z` of `w'`, and the closed-loop facts `HL` (off `Z` a converging clock lets the raw scaler
recover to `ρ`: `stall_scaler_ge` at the stalled equilibrium of `joint_stall_eq`/`vert_stall_eq`,
reached by `asymptotic_gain`), `HS` (the vehicle converges to within `b_S` of the stalled target)
and `HE` (after the end of the S-curve, through the mission's completion and the loiter at the
stopping point, the vehicle ends within `b_E` of `w'`). -/
def ReachFacts (sense32 : ℝ → Float32) (senseP : ℝ → Float) (w₀ : Vehicle.World) (w' : P3)
    (ρ dZ bS bE : ℝ) : Prop :=
  ∀ x ∈ Mloop sense32 senseP w₀, ∀ p₀ ψ₀, x ∈ Ahover p₀ ψ₀ →
    ∃ (r : ℕ → ℝ) (Γ : ℝ → P3) (Z : Set ℝ),
      (∀ t, 0 ≤ scRun w₀ x t) ∧ Pacing.FilterRun (scRun w₀ x) r Pacing.α₀ (1 / 10 ^ 7) ∧
      (∀ q' ∈ Z, dist (Γ q') w' ≤ dZ) ∧
      (∀ q', q' ∉ Z → Tendsto (navProgress w₀ x) atTop (𝓝 q') → ∀ᶠ t in atTop, ρ ≤ r t) ∧
      (∀ q', Tendsto (navProgress w₀ x) atTop (𝓝 q') →
        ∀ᶠ t in atTop, dist (pos (x t)) (Γ q') ≤ bS) ∧
      (Tendsto (navProgress w₀ x) atTop atTop → ∀ᶠ t in atTop, dist (pos (x t)) w' ≤ bE)

/-- **Waypoint reach on the loop, conditional on `ReachFacts`**: from hover at any `p₀`, any heading
`ψ₀`, the loop reaches the ball of radius `max b_E (d_Z + b_S)` around `w'` and stays in it. -/
theorem waypoint_reach_of_facts (sense32 : ℝ → Float32) (senseP : ℝ → Float) (w₀ : Vehicle.World)
    (w' : P3) {ρ dZ bS bE : ℝ} (hρ : 13 / 10 ^ 6 ≤ ρ)
    (hF : ReachFacts sense32 senseP w₀ w' ρ dZ bS bE) (p₀ : P3) (ψ₀ : ℝ) :
    Mloop sense32 senseP w₀ ⊨ ⟨Ahover p₀ ψ₀, ReachGoal (max bE (dZ + bS)) w'⟩ := by
  rintro x ⟨hx, hA⟩
  obtain ⟨r, Γ, Z, hs, hf, hZ, HL, HS, HE⟩ := hF x hx p₀ ψ₀ hA
  exact reach_model (fun t => pos (x t)) w' Γ hs hf (navProgress_succ w₀ x) Z hρ hZ HL HS HE

end

end Contracts.Track.Reach
