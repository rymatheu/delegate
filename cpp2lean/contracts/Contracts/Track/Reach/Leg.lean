import Contracts.Track.Reach.LegGains

/-!
# The leg theorem: horizontal waypoint reachability from hover, bounded time (REACH.md §9)

```
theorem waypoint_reach_h (sense32 senseP w₀) (p₀ : P3) (w' : Vector3p.State) (ψ₀ : ℝ)
    (hP : LegParams w₀) (hmin : 1/100 ≤ dist p₀ (wpt w')) (hR : dist p₀ (wpt w') ≤ 36/10) (hZ : wpt w' 2 = p₀ 2)
    (hW : ReachWorld w₀ w')
    (hS : Plant.CopterSense sense32 senseP) (hL : LibmSpec) (hF : LegFacts sense32 senseP w₀ p₀ w' ψ₀) :
    Mloop sense32 senseP w₀ ⊨
      ⟨Ahover p₀ ψ₀, lang_t 0 (.eventually 0 4800 (.always 0 1200 (near (wpt w') (1/10))))⟩
```

From a hover at `p₀` (any heading `ψ₀`), with the single waypoint `w'` at the same altitude between
1 cm and 3.6 m away (a leg shorter than 1 cm starts with the vehicle at the setpoint: it is the hold
of `Glue.hover_hold`): within 4800 ticks (12 s) the vehicle is within 0.1 m of `w'` for 1200 consecutive ticks.
The waypoint is the mission's `Vector3p.State` (as `ReachWorld` takes it); the formula reads it as
the point `wpt w'`.

`LegFacts` is the one named hypothesis: for every behavior of the loop from hover, the per-tick facts
`LegRun`: the start of the tube (`init`), the per-tick disturbance rows and reference limits while
the box holds (`tick`), the sum of the velocity defect over the run (`d2sum`), and the navigator's
phases (`phase`: the S-curve on the leg, its end by tick 2200, the completion, the loiter target,
the target held after the loiter).

Everything above the facts is proved: the box and the tracking tube along the leg (`LegTube`), the
completion by tick 2617 (decay after the end of the leg's S-curve), the loiter target within 0.081
of `w'` (`LegNav`), the hold window (`LegHold`), the formula. The proof of `waypoint_reach_h` is in
`LegHold.lean` (it needs the three parts); this file holds the statement and the facts.
-/

namespace Contracts.Track.Reach.Leg

open Contracts Contracts.STL Contracts.Mission Matrix Finset Contracts.Track.Induction
  Contracts.Track.Reach.Glue

noncomputable section

/-! ## The reference and the disturbances of one behavior -/

/-- The target acceleration of axis `a` after tick `t` (`_accel_desired_ned_mss`). -/
def aH (w₀ : Vehicle.World) (x : ℕ → X) (t : ℕ) (a : Fin 2) : ℝ := (refH w₀ x a t).2.2

/-- The position defect of the target sequence of axis `a` over tick `t`:
`sp' − sp − h vsp − h²/2 asp`. -/
def d1H (w₀ : Vehicle.World) (x : ℕ → X) (t : ℕ) (a : Fin 2) : ℝ :=
  Horizontal.defect₁ (refH w₀ x a t).1 (refH w₀ x a (t + 1)).1 (refH w₀ x a t).2.1
    (refH w₀ x a t).2.2

/-- The velocity defect of the target sequence of axis `a` over tick `t`: `vsp' − vsp − h asp`. -/
def d2H (w₀ : Vehicle.World) (x : ℕ → X) (t : ℕ) (a : Fin 2) : ℝ :=
  Horizontal.defect₂ (refH w₀ x a t).2.1 (refH w₀ x a (t + 1)).2.1 (refH w₀ x a t).2.2

/-- The vertical target acceleration after tick `t`. -/
def aZ (w₀ : Vehicle.World) (x : ℕ → X) (t : ℕ) : ℝ := (refV w₀ x t).2.2

/-- The vertical position defect over tick `t`. -/
def d1Z (w₀ : Vehicle.World) (x : ℕ → X) (t : ℕ) : ℝ :=
  Vertical.defect₁ (refV w₀ x t).1 (refV w₀ x (t + 1)).1 (refV w₀ x t).2.1 (refV w₀ x t).2.2

/-- The vertical velocity defect over tick `t`. -/
def d2Z (w₀ : Vehicle.World) (x : ℕ → X) (t : ℕ) : ℝ :=
  Vertical.defect₂ (refV w₀ x t).2.1 (refV w₀ x (t + 1)).2.1 (refV w₀ x t).2.2

/-- **The horizontal disturbance of tick `t`**: what the code's tick and the plant add to the model
driven by the actual target sequence. -/
def legWH (w₀ : Vehicle.World) (x : ℕ → X) (t : ℕ) (a : Fin 2) : Fin 9 → ℝ :=
  ξH w₀ x (t + 1) a - (Horizontal.AhR *ᵥ ξH w₀ x t a + Horizontal.forceOf (refH w₀ x a) t)

/-- **The vertical disturbance of tick `t`**. -/
def legWV (w₀ : Vehicle.World) (x : ℕ → X) (t : ℕ) : Fin 8 → ℝ :=
  ξV w₀ x (t + 1) - (Vertical.AvR *ᵥ ξV w₀ x t + Vertical.forceOf (refV w₀ x) t)

/-! ## The facts -/

/-- **The navigator's phases of one behavior** (`Tc`: the completion tick, whose sample sets the
loiter target; `Tl`: the end of the loiter S-curve). The direction witness `c` and the field
`legH` (the S-curve's bounds along the leg) were removed on 2026-11-06: the proof no longer uses them
(the completion is by decay, not through the tube along the leg).
Measured side: the coordinator's campaign (204 horizontal legs from hover, 0.2–3.6 m, 6 directions,
headings 0/90/180/−45°, altitudes 0.5–3 m; `reach-legs-campaign.csv`, the traces of
`reach-legs-defects.csv` read per tick, REACH.md §9.3). REACH.md §9.3 argues for each field that it
holds on every behavior from hover under the hypotheses of `waypoint_reach_h` (leg `≥ 1` cm). -/
structure LegPhase (w₀ : Vehicle.World) (w' : P3) (x : ℕ → X) (Tc Tl : ℕ) :
    Prop where
  /-- The completion comes after the first two ticks (an S-curve of a leg `≥ 1` cm lasts more than
  100 ticks and the completion needs it finished), and the loiter S-curve (from `w'` to the stopping
  point, at most `0.081` m, jerk 5) lasts at most 450 ticks (measured `≤ 436`, on a 0.2 m leg; the
  previous bound 400 was false). -/
  order : ts ≤ Tc ∧ Tc ≤ Tl ∧ Tl ≤ Tc + 450
  /-- **The vertical target on the leg is constant** up to the leg's rounding: the vertical
  direction is `u_z = Δz / ‖Δ‖` with `Δz` the `double` rounding of the altitudes (sensed position,
  stopping point at rest, `w'.z`), `|Δz| ≲ 10⁻¹⁵ |z|`, and `‖Δ‖ ≥ 1` cm (`hmin`), so
  `|u_z| ≤ 10⁻¹³ |z|` and the vertical acceleration `≤ 1.5 |u_z|` is far below `10⁻³` (measured:
  the vertical target acceleration and defects are exactly 0 before the completion). -/
  legV : ∀ t, ts ≤ t → t < Tc → |aZ w₀ x t| ≤ 1 / 1000 ∧ |d1Z w₀ x t| ≤ 1 / 10 ^ 8 ∧
    |d2Z w₀ x t| ≤ 1 / 10 ^ 7
  /-- **The target is held after the loiter** (the loiter S-curve finished: the position target is
  the loiter point; the velocity and acceleration targets are the finished S-curve's end values,
  zero up to `10⁻⁶`, measured `≤ 1.0·10⁻⁸` and `≤ 4.9·10⁻⁷`; `tick_hold_ps`, `HoldScenario`). -/
  hold : ∀ t, Tl ≤ t → posTarget (x t) = posTarget (x Tl) ∧
    ∀ i, |velTarget (x t) i| ≤ 1 / 10 ^ 6 ∧ |accDes w₀ x t i| ≤ 1 / 10 ^ 6
  /-- **The leg S-curve has finished by tick 2200, and the completion test** (`Te`: the tick at
  which the leg's S-curve has finished; measured `≤ 2107` ticks at 3.6 m, start-up slowdown
  included; the completion follows within one tick). From `Te` to the completion the target is at
  `w'` within `10⁻³` (measured `8.6·10⁻⁷`) and the reference is at rest: target acceleration
  `≤ 10⁻⁶`, defects `≤ 10⁻⁸`, `3·10⁻⁶` per axis (measured `1.0·10⁻⁷`, `2.2·10⁻¹⁰`, `8.6·10⁻⁸`); the
  completion fires on the tick after the first on which the vehicle is within `0.099` of `w'`
  (`advance_wp_target_along_track` sets `reached_destination` when the S-curve is finished and the
  estimate is within `WP_RADIUS = 0.1`; `verify_nav_wp_done` reads it on the next tick). -/
  arrive : ∃ Te, ts ≤ Te ∧ Te ≤ 2200 ∧
    (∀ t, Te ≤ t → t < Tc → dist (posTarget (x t)) w' ≤ 1 / 1000 ∧
      ∀ a, |aH w₀ x t a| ≤ 1 / 10 ^ 6 ∧ |d1H w₀ x t a| ≤ 1 / 10 ^ 8 ∧
        |d2H w₀ x t a| ≤ 3 / 10 ^ 6) ∧
    ∀ t, Te ≤ t → t < Tc → dist (pos (x t)) w' ≤ 99 / 1000 → Tc ≤ t + 1
  /-- **The state at completion**: distance to `w'` plus speed `≤ 0.08` (the vehicle near the end
  of the S-curve, which the ℓ1 envelope bound cannot give; a certified nominal of the leg family
  would, as `nom_complete` does for the course). Measured `≤ 0.0554` (`0.0698` on the 3D
  campaign); final distance (loiter point plus hold error) `≤ 0.034`. -/
  atComplete : dist (pos (x Tc)) w' + ‖vel (x Tc)‖ ≤ 8 / 100
  /-- **The loiter target** (`loiter_dest_bound`, NavStop.lean, at the completion tick's estimates,
  the sample, within `10⁻⁶` of the plant state): the stopping point is within `dist + ‖v‖` of `w'`
  plus its `float` rounding, `≤ 10⁻³` for positions up to about 300 m from the origin (`2⁻²⁰ |p|`
  per axis, `stop_NE_bound`). Measured: the loiter point is within the bound minus `0.0012`. -/
  loiter : dist (posTarget (x Tl)) w' ≤ dist (pos (x Tc)) w' + ‖vel (x Tc)‖ + 1 / 1000

/-- **The per-tick facts of one behavior of the loop from hover.** -/
structure LegRun (w₀ : Vehicle.World) (w' : P3) (x : ℕ → X) : Prop where
  /-- **The start of the tube** (the takeover and the first tick from `startP p₀ ψ₀`, C16:
  `takeover`, `ModeAuto::init`, `mission_start`): at tick 2 the readouts are within `ε0VL`, `ε0HL`
  (LegTube.lean, measured values there), the S-curve's acceleration is `≤ 10⁻³` (measured
  `≤ 7.6·10⁻⁵`) and the velocity defect `≤ 10⁻⁶` (measured `≤ 1.2·10⁻⁷`). **Repaired 2026-11-06**:
  the vertical start asked `|ev| ≤ 10⁻⁶` and `|eA| ≤ 10⁻⁵` and was false on every run: the trim
  `MOT_THST_HOVER 0.4444` against the plant's `1/2.25` (the hypothesis `LegParams`) sinks the vehicle
  at `9.80·10⁻⁴` m/s² from tick 0, so at tick 2 the vertical velocity error is `4.90–5.03·10⁻⁶`
  (measured) and the acceleration PID's filtered error `2.34·10⁻⁴` (computed); `ε0VL` now has
  `10⁻⁵` and `2·10⁻³` in these entries. The other trims (`I`, `f`, `u`, `w`) are within `4.4·10⁻⁵`
  (`w` measured `4.45·10⁻⁵`). -/
  init : (∀ j, |ξV w₀ x ts j| ≤ ε0VL j) ∧ (∀ a j, |ξH w₀ x ts a j| ≤ ε0HL j) ∧
    (∀ a, |aH w₀ x ts a| ≤ 1 / 1000) ∧ ∀ a, |d2H w₀ x ts a| ≤ 1 / 10 ^ 6
  /-- **The tick glue and the reference limits, per tick while the box holds** (`TickBounds`):
  the disturbance rows `legWV ≤ εVL` (`vglue` with `vertical_tick_split` at the box, plus the
  structured tilt coupling at leg tilts `≤ 0.03` m/s²) and `legWH ≤ εHL` (`ne_glue` with
  `wHβ_bound`, `prow_le`, and the attitude deviation `εη = 0.01` m/s² of M4's `attitude_tracks`,
  which includes the heading coupling of the yaw slew of `WP_YAW_BEHAVIOR 2`, `AttitudeYawPhase`);
  the box is `BoxL` (INDUCTION's, with the horizontal position error widened to `0.15`: the
  horizontal controller's region `NERegion` asks `‖e‖ ≤ 0.4`, the command and its rate keep M4's
  class `CmdOK`); and the navigator's limits on the whole run (leg and loiter S-curves): target
  acceleration `≤ 1.501` per axis (measured `1.5000003`), its change `≤ 0.013` per tick (jerk 5:
  `0.0125`), position defect `≤ 1.3·10⁻⁴` (measured `1.258·10⁻⁴`), velocity defect `≤ 8·10⁻⁴`
  (measured `7.68·10⁻⁴`; the field asked `1.3·10⁻⁴` until 2026-11-06 and was false), its change
  `≤ 1.1·10⁻⁵` per tick (measured `1.007·10⁻⁵`); vertically acceleration `≤ 0.5` (measured
  `0.028`, the loiter's vertical move), defects `≤ 10⁻⁵` (measured `2.4·10⁻⁶`) and `≤ 2·10⁻⁵`
  (measured `1.89·10⁻⁵`; the field asked `10⁻⁵` until 2026-11-06 and was false). The controller
  invariant `CtrlInv` (finiteness, flags, branches) is carried inside: the rows hold because it
  does. Measured: tracking error `≤ 0.0419` m, target speed `≤ 1.0000002`. -/
  tick : ∀ t, ts ≤ t → t < hzn → (∀ k, ts ≤ k → k ≤ t → BoxL (ξV w₀ x) (ξH w₀ x) k) →
    TickBounds (ξV w₀ x) (legWV w₀ x) (aZ w₀ x) (d1Z w₀ x) (d2Z w₀ x) (ξH w₀ x) (legWH w₀ x)
      (aH w₀ x) (d1H w₀ x) (d2H w₀ x) t
  /-- **The velocity defect summed over the run** (leg and loiter S-curves): `≤ 1/4` per axis while
  the box holds (measured `≤ 0.2404` over the whole recorded run; after it the target is held and
  the defect is `≤ 10⁻⁸` per tick). The decay arguments carry the defect through this sum and the
  peak of the tail of the response (`env_tail_l1`). -/
  d2sum : ∀ N, ts + N ≤ hzn → (∀ k, ts ≤ k → k ≤ ts + N → BoxL (ξV w₀ x) (ξH w₀ x) k) → ∀ a,
    ∑ k ∈ Finset.range N, |d2H w₀ x (ts + k) a| ≤ 1 / 4
  /-- The navigator's phases (`LegPhase`). -/
  phase : ∃ Tc Tl : ℕ, LegPhase w₀ w' x Tc Tl

/-- **The facts of the leg** (the one named hypothesis of `waypoint_reach_h`): `LegRun` for every
behavior of the loop from hover. (The numbers of the reference directions, `RefGains`, are certified:
`refGains_certified`, LegGains.lean.) -/
structure LegFacts (sense32 : ℝ → Float32) (senseP : ℝ → Float) (w₀ : Vehicle.World) (p₀ : P3)
    (w' : AC_WPNav_lib.Vector3p.State) (ψ₀ : ℝ) : Prop where
  /-- The per-tick facts of every behavior from hover. -/
  run : ∀ x ∈ Mloop sense32 senseP w₀ ∩ Reach.Ahover p₀ ψ₀, LegRun w₀ (wpt w') x

/-! ## The parameters the models are built on -/

/-- **The parameters of the leg's models** (the values of `sim/params/copter-cf2x*.txt`, `MissionData`):
the fields of the world that the channel models (`Vertical.Av`, `Horizontal.Ah`, their ε tables and
the trims of the start) are built on and that `ReachWorld` does not fix (REACH.md §8.1 item 4).
`MOT_THST_HOVER 0.4444` (the construct default is `0.35`, which would put the vertical trims at
`0.094` instead of `4.4·10⁻⁵`), no hover learning (it would move the trim), the linear thrust curve
(`MOT_THST_EXPO 0`, `MOT_SPIN_MIN 0`, `MOT_SPIN_MAX 1`, `MOT_BAT_VOLT_MAX 0`), the angle P gains
(`ATC_ANG_RLL_P 9`, `ATC_ANG_PIT_P 9`), the horizontal velocity PID (`PSC_NE_VEL_P 6`, `I 1`,
`D 0.5`, `FF 0`, filters 5 Hz), and the vertical controllers as `D_update_controller` reads them
(`CtrlV.DPar2`: `PSC_D_POS_P 1`, `PSC_D_VEL_P 5`, `PSC_D_ACC_P 0.05`, `PSC_D_ACC_I 0.1`, the filters
5, 5, 20 Hz, `PSC_D_ACC_IMAX ≤ 2`). The attitude rate PIDs are not pinned: the attitude loop enters
the models only through the lag law and its deviation row `εη` (a fact of `tick`). -/
structure LegParams (w : Vehicle.World) : Prop where
  hover : w.mp._throttle_hover = 0.4444
  hover_learn : w.mp._throttle_hover_learn = 0
  expo : w.mp.thr_lin.curve_expo = 0
  spin_min : w.mp.thr_lin.spin_min = 0
  spin_max : w.mp.thr_lin.spin_max = 1
  batt : w.mp.thr_lin.batt_voltage_max = 0
  ang_r : w.ap._p_angle_roll._kp = 9
  ang_p : w.ap._p_angle_pitch._kp = 9
  ne_kp : w.pp._pid_vel_ne_m._kp = 6
  ne_ki : w.pp._pid_vel_ne_m._ki = 1
  ne_kd : w.pp._pid_vel_ne_m._kd = 0.5
  ne_kff : w.pp._pid_vel_ne_m._kff = 0
  ne_fE : w.pp._pid_vel_ne_m._filt_E_hz = 5
  ne_fD : w.pp._pid_vel_ne_m._filt_D_hz = 5
  vert : CtrlV.DPar2 w.pp

/-! ## The statement -/

/-- The goal: within 4800 ticks, 1200 consecutive ticks within `0.1` of `w'`. -/
def legGoal (w' : P3) : Formula X := .eventually 0 4800 (.always 0 1200 (near w' (1 / 10)))

/-- **The statement of the leg theorem** (proved as `waypoint_reach_h`, LegHold.lean). -/
def WaypointReachH (sense32 : ℝ → Float32) (senseP : ℝ → Float) (w₀ : Vehicle.World) (p₀ : P3)
    (w' : AC_WPNav_lib.Vector3p.State) (ψ₀ : ℝ) : Prop :=
  LegParams w₀ → 1 / 100 ≤ dist p₀ (wpt w') → dist p₀ (wpt w') ≤ 36 / 10 → wpt w' 2 = p₀ 2 → ReachWorld w₀ w' →
    Plant.CopterSense sense32 senseP → LibmSpec → LegFacts sense32 senseP w₀ p₀ w' ψ₀ →
    Mloop sense32 senseP w₀ ⊨ ⟨Ahover p₀ ψ₀, lang_t 0 (legGoal (wpt w'))⟩

/-- **Nonvacuity**: the loop has behaviors from every hover (for every world, ports, `p₀`, `ψ₀`). -/
theorem waypoint_reach_h_nonvacuous (sense32 : ℝ → Float32) (senseP : ℝ → Float)
    (w₀ : Vehicle.World) (p₀ : P3) (ψ₀ : ℝ) :
    (Mloop sense32 senseP w₀ ∩ Ahover p₀ ψ₀).Nonempty :=
  waypoint_reach_nonvacuous sense32 senseP w₀ p₀ ψ₀

end

end Contracts.Track.Reach.Leg
