import Contracts.Track.Induction.Vert
import Contracts.Mission.NavStop
import Contracts.Track.PacingArrive

/-!
# M9, part 3: the pieces the induction takes as hypotheses

`Pieces sense32 senseP w₀` bundles the interfaces of the other milestones (`Iface`: the
invariants and the phase functions they define) and every lemma the induction needs from them, in
the form their documents promise (INDUCTION.md §3 lists each field with its source):

* **C16, the first ticks** (TRACK_PLAN.md §4.1): `init_world`, `init`, `init_tube`;
* **the vertical channel** (VERTICAL.md §7, CTRL_VERTICAL.md): `vglue` (the join's hypotheses
  inside the tick), `wVs_def` (`(float) π` is `LibmSpec.pi32`); the rows come from the C-series' finished
  `CtrlV.vertical_tick_split` (`wV_bound`);
* **the horizontal channel** (HORIZONTAL.md §7, CTRL_HORIZONTAL.md): `ne_glue` (the call of
  `NE_update_controller` inside the tick); the controller rows come from M6's finished
  `HCtl.horizontal_tick_eq_D` and the plant row from `Plant.step_pv_sharp` (`wHβ_bound`,
  `prow_le`);
* **the attitude contract M4** (HORIZONTAL.md §7, structured form; TRACK_PLAN.md §8.2):
  `attitude_tracks`, `att_step`, `att_rates`;
* **the heading subsystem** (TRACK_PLAN.md §3.8): `yaw_step`;
* **the C-series code invariant**: `ctrl_step`;
* **the navigator** (MISSION.md, `nav_contract` (d)): `nav_step` (one tick: geometry, leash
  inactive), `nav_bounds`;
* **pacing** (PACING.md §6, the inputs of `Pacing.pacing_course` and `Pacing.hold_course`): the
  code facts of the scaler along the run (`pace_filter`, `pace_raw`, `pace_s0`, `pace_q`,
  `pace_q0`, `pace_scaler`), the navigator's progress and `τ_v` (`q_nav`, `τv_nav`; the escape
  itself is the hypothesis `Mission.ClimbEscape` of the theorem), the course windows and speeds (`pace_gaps`,
  `pace_speed`, `pace_win`, `pace_end`);
* **the certified nominal** (M5, M6, M8): the gains `peakV`, `gainV`, `peakH`, `gainH`, and the
  phase-resolved nominal bounds `nom_box`, `nom_T1`, `nom_climbout`, `nom_w07`, `nom_corner`,
  `nom_win0`, `nom_along`, `nom_rest`, `nom_complete`;
* **the hold** (TRACK_PLAN.md §3.11): `loiter_nav` (with `Pacing.hold_course`, which uses the
  finished `Mission.loiter_dest_bound`).

Every step hypothesis is about one tick (`Region` at `t`, conclusion at `t + 1`). The pacing facts
are per tick along the run, and
`loiter_nav` takes the invariant up to the tick.
-/

namespace Contracts.Track.Induction

open Contracts Contracts.STL Contracts.Mission Matrix Finset AC_PosControl_lib

noncomputable section

/-- A `float` vector of the navigator as a point. -/
def v3 (a : AC_WPNav_lib.Vector3f.State) : P3 := !₂[a.x.toReal, a.y.toReal, a.z.toReal]

/-- The waypoint index of corner `i` (`w₁ … w₆`). -/
def cIdx (i : Fin 6) : Fin 8 := ⟨i.val + 1, by omega⟩

/-- A behavior of the closed loop from the takeoff assumption. -/
def Beh (sense32 : ℝ → Float32) (senseP : ℝ → Float) (w₀ : Vehicle.World) (x : ℕ → Mission.X) :
    Prop :=
  x ∈ Mloop sense32 senseP w₀ ∧ x ∈ Atakeoff

/-- The hypotheses of `loiter_dest_bound` on the position controller's state other than the speed
bound: the gains and limits, zero offsets, finite estimates. -/
structure LoiterHyps (p : AC_PosControl.Params) (s : AC_PosControl.State) : Prop where
  hkp : p._p_pos_ne_m._kp = 1.5
  hacc : s._accel_max_ne_mss = 1.5
  hvm : s._vel_max_ne_ms = 1
  hkpd : p._p_pos_d_m._kp = 1
  haccd : s._accel_max_d_mss = 1
  hpox : A64 s._pos_offset_ned_m.x 0 0
  hpoy : A64 s._pos_offset_ned_m.y 0 0
  hpoz : A64 s._pos_offset_ned_m.z 0 0
  hvox : A32 s._vel_offset_ned_ms.x 0 0
  hvoy : A32 s._vel_offset_ned_ms.y 0 0
  hvoz : A32 s._vel_offset_ned_ms.z 0 0
  hpx : s._pos_estimate_ned_m.x.IsFinite
  hpy : s._pos_estimate_ned_m.y.IsFinite
  hpz : s._pos_estimate_ned_m.z.IsFinite
  hvx : s._vel_estimate_ned_ms.x.IsFinite
  hvy : s._vel_estimate_ned_ms.y.IsFinite
  hvz : s._vel_estimate_ned_ms.z.IsFinite

/-- **The pieces.** -/
structure Pieces (sense32 : ℝ → Float32) (senseP : ℝ → Float) (w₀ : Vehicle.World)
    extends Iface where
  -- ### C16: the first ticks
  /-- M2's precondition on the mission's world (the integrator limits of the parameter files are
  proper and the stored integrators within them); a parameter check like `missionParams_of_ok`. -/
  init_world : IntOK w₀
  /-- The subsystem invariants at tick 0, from `Atakeoff` and the takeover. -/
  init : ∀ x, Beh sense32 senseP w₀ x →
    toIface.AttInv x 0 ∧ toIface.YawInv x 0 ∧ toIface.NavInv x 0 ∧ toIface.CtrlInv x 0
  /-- The tubes over ticks 0–2 (the special branches `first_tick`, `reset_filter`, evaluated from
  `startP p ψ₀`), and the deviation at tick 2 per coordinate. -/
  init_tube : ∀ x, Beh sense32 senseP w₀ x →
    (∀ t ≤ 2, TubeOK toIface w₀ x t) ∧ (∀ j, |ηV toIface w₀ x 2 j| ≤ ε0V j) ∧
      ∀ a j, |ηH toIface w₀ x 2 a j| ≤ ε0H j
  -- ### The vertical channel (VERTICAL.md §7)
  /-- The vertical tick glue (C15): the hypotheses of the C-series join `CtrlV.VTickHyp` at the
  region's magnitudes, and the targets. With `CtrlV.vertical_tick_split` it gives the per-tick bound
  of `wV` (`wV_bound`). -/
  vglue : ∀ x, Beh sense32 senseP w₀ x → ∀ t, 2 ≤ t → Region toIface w₀ x t → VGlue w₀ x t
  /-- The structured vertical disturbance is the join's `wS` (the instance sets `wVs := wSv w₀`). -/
  wVs_def : ∀ x t, toIface.wVs x t = wSv w₀ x t
  -- ### The horizontal channel (HORIZONTAL.md §7)
  /-- The horizontal tick glue (C15): the call of `NE_update_controller` and its region inside
  the tick, with the readouts of `Run.lean`; with M6's `HCtl.horizontal_tick_eq_D` it gives the
  per-tick bound of `wHβ` (`wHβ_bound`). -/
  ne_glue : ∀ x, Beh sense32 senseP w₀ x → ∀ t, 2 ≤ t → Region toIface w₀ x t → NEGlue w₀ x t
  -- ### The attitude contract (M4)
  /-- The structured form of HORIZONTAL.md §7: the realized acceleration is the lag law plus the
  structured heading coupling `etaHat` plus at most `εη`. -/
  attitude_tracks : ∀ x, Beh sense32 senseP w₀ x → ∀ t, 2 ≤ t → Region toIface w₀ x t →
    ∀ a, |etaA w₀ x t a - toIface.etaHat x t a| ≤ εη
  /-- The attitude invariant is kept under commands of the class (`|a_NE| ≤ 4`, `|Δa_NE| ≤ 0.05`
  per tick) and any heading command. -/
  att_step : ∀ x, Beh sense32 senseP w₀ x → ∀ t, Region toIface w₀ x t → CmdOK w₀ x t →
    toIface.AttInv x (t + 1)
  /-- The attitude invariant bounds the body rates (D3, D4). -/
  att_rates : ∀ x, Beh sense32 senseP w₀ x → ∀ t, toIface.AttInv x t →
    |ph x t 10| ≤ 2 ∧ |ph x t 11| ≤ 2 ∧ |ph x t 12| ≤ 7 / 5
  -- ### The heading subsystem (TRACK_PLAN.md §3.8)
  /-- The yaw phase lemma, as an invariant: from any heading error and any step command the shaped
  yaw rate, the yaw rate PID and the mixer's yaw stay in their bounds (Y1–Y5). -/
  yaw_step : ∀ x, Beh sense32 senseP w₀ x → ∀ t, Region toIface w₀ x t → toIface.YawInv x (t + 1)
  -- ### The C-series code invariant
  /-- Finite floats, flags and branch conditions of the controller code are kept on the region. -/
  ctrl_step : ∀ x, Beh sense32 senseP w₀ x → ∀ t, Region toIface w₀ x t →
    toIface.CtrlInv x (t + 1)
  -- ### The navigator
  /-- One tick of the navigator (target geometry, the leash `AC_P_2D/1D::update_all` leaves the
  target alone while the sampled error is at most `δs`): the invariant is kept. -/
  nav_step : ∀ x, Beh sense32 senseP w₀ x → ∀ t, Region toIface w₀ x t → smpErr (x t) ≤ δs →
    toIface.NavInv x (t + 1)
  /-- The targets are within the course's bounding box and the S-curve speeds. -/
  nav_bounds : ∀ x, Beh sense32 senseP w₀ x → ∀ t, toIface.NavInv x t →
    ∀ i, |posTarget (x t) i| ≤ 3 ∧ |velTarget (x t) i| ≤ 3 / 2
  -- ### Pacing: the code facts along the run (PACING.md §6; discharged by C15 glue + M8)
  /-- `Pacing.code_filter_step` on the run: the filter step of tick `t + 1`. -/
  pace_filter : ∀ x, Beh sense32 senseP w₀ x → ∀ t, Region toIface w₀ x (t + 1) →
    -(1 / 1000) ≤ toIface.sc x t → toIface.sc x t ≤ 1 + 1 / 1000 →
      |toIface.sc x (t + 1) - (toIface.sc x t + (toIface.r x (t + 1) - toIface.sc x t) * Pacing.α₀)|
        ≤ 1 / 10 ^ 7
  /-- `Pacing.rawScaler_unit` on the run. -/
  pace_raw : ∀ x, Beh sense32 senseP w₀ x → ∀ t, 0 ≤ toIface.r x t ∧ toIface.r x t ≤ 1
  /-- The initial scaler (`1.0` after `wp_and_spline_init_m`). -/
  pace_s0 : ∀ x, Beh sense32 senseP w₀ x →
    -((1 / 10 ^ 7) / Pacing.α₀) ≤ toIface.sc x 0 ∧ toIface.sc x 0 ≤ 1 + (1 / 10 ^ 7) / Pacing.α₀
  /-- `Pacing.prog_step` on the run (`vel_dt_scalar = 1`). -/
  pace_q : ∀ x, Beh sense32 senseP w₀ x → ∀ t, Region toIface w₀ x (t + 1) →
    |toIface.q x (t + 1) - toIface.q x t - toIface.sc x (t + 1)| ≤ 1 / 10 ^ 7
  /-- The first S-curve step. -/
  pace_q0 : ∀ x, Beh sense32 senseP w₀ x → |toIface.q x 0 - toIface.sc x 0| ≤ 1 / 10 ^ 7
  /-- The raw scaler of tick `t + 1` is `rawScaler` of the logged inputs, which are (up to the
  `float` sensing) the velocity target after tick `t`, the position error against it and the sampled
  velocity of tick `t + 1`. -/
  pace_scaler : ∀ x, Beh sense32 senseP w₀ x → ∀ t, (∀ k ≤ t + 1, Inv1 toIface w₀ x k) →
    ∃ (vT pe ve : AC_WPNav_lib.Vector3f.State) (kP : Float32),
      toIface.r x (t + 1) = (Pacing.rawScaler vT pe ve kP).toReal ∧ kP.IsFinite ∧
      kP.toReal = 3 / 2 ∧ Pacing.Fin3 vT 3 ∧ Pacing.Fin3 pe 4 ∧ Pacing.Fin3 ve 3 ∧
      v3 vT = velTarget (x t) ∧ dist (v3 ve) (vel (x (t + 1))) ≤ 1 / 10 ^ 5 ∧
      dist (v3 pe) (posTarget (x t) - pos (x (t + 1))) ≤ 1 / 10 ^ 5
  -- ### Pacing: the closed loop and the course (PACING.md §3, M7)
  /-- The S-curve progress is the navigator's `Mission.navProgress` up to tick `350` (so the escape
  `hesc` of `Pacing.pacing_course` is the hypothesis `Mission.ClimbEscape`). -/
  q_nav : ∀ x, Beh sense32 senseP w₀ x → ∀ t ≤ 350, toIface.q x t = navProgress w₀ x t
  /-- `τ_v` is the navigator's `Mission.climbTau`. -/
  τv_nav : ∀ x, Beh sense32 senseP w₀ x → toIface.τv x = climbTau w₀ x
  /-- The arrival windows of the course (M7, `pacing_course`'s `ha0 … ha7`). -/
  pace_gaps : ∀ x, Beh sense32 senseP w₀ x →
    (240 ≤ toIface.ar x 0 - toIface.τv x ∧ toIface.ar x 0 - toIface.τv x ≤ 510) ∧
    (2 ≤ toIface.ar x 1 - toIface.ar x 0 ∧ toIface.ar x 1 - toIface.ar x 0 ≤ 860) ∧
    (2 ≤ toIface.ar x 2 - toIface.ar x 1 ∧ toIface.ar x 2 - toIface.ar x 1 ≤ 743) ∧
    (2 ≤ toIface.ar x 3 - toIface.ar x 2 ∧ toIface.ar x 3 - toIface.ar x 2 ≤ 743) ∧
    (2 ≤ toIface.ar x 4 - toIface.ar x 3 ∧ toIface.ar x 4 - toIface.ar x 3 ≤ 1450) ∧
    (2 ≤ toIface.ar x 5 - toIface.ar x 4 ∧ toIface.ar x 5 - toIface.ar x 4 ≤ 743) ∧
    (2 ≤ toIface.ar x 6 - toIface.ar x 5 ∧ toIface.ar x 6 - toIface.ar x 5 ≤ 743) ∧
    (2 ≤ toIface.ar x 7 - toIface.ar x 6 ∧ toIface.ar x 7 - toIface.ar x 6 ≤ 750)
  /-- The S-curve speed on the phases (M7): `0.36` from the escape to the `w1` window, `0.6`
  between the corners, `0.48` into `w7`. -/
  pace_speed : ∀ x, Beh sense32 senseP w₀ x → ∀ t, toIface.NavInv x t →
    (toIface.τv x - 1 ≤ toIface.q x t → toIface.q x t < toIface.ar x 1 →
      36 / 100 ≤ ‖velTarget (x t)‖) ∧
    (∀ i : Fin 8, 2 ≤ (i : ℕ) → (i : ℕ) ≤ 6 → toIface.ar x (i - 1) - 1 ≤ toIface.q x t →
      toIface.q x t < toIface.ar x i → 6 / 10 ≤ ‖velTarget (x t)‖) ∧
    (toIface.ar x 6 - 1 ≤ toIface.q x t → toIface.q x t < toIface.ar x 7 →
      48 / 100 ≤ ‖velTarget (x t)‖)
  /-- The arrival windows of `w₁ … w₇` (M7, S-curve geometry). -/
  pace_win : ∀ x, Beh sense32 senseP w₀ x → ∀ i : Fin 8, 1 ≤ (i : ℕ) → ∀ t, toIface.NavInv x t →
    toIface.ar x i ≤ toIface.q x t → toIface.q x t < toIface.ar x i + 2 →
      dist (posTarget (x t)) (wp i) ≤ rPass (wp i)
  /-- The end of the last S-curve (M7): until completion the target stays within `rPass w7`. -/
  pace_end : ∀ x, Beh sense32 senseP w₀ x → ∀ t, toIface.NavInv x t → ¬ complete w₀ x t →
    toIface.ar x 7 - 1 ≤ toIface.q x t → dist (posTarget (x t)) w7 ≤ rPass w7
  -- ### The certified nominal (M5, M6, M8)
  /-- Peak gains of the vertical model (certificate). -/
  peakV : ∀ o j m, |resp Vertical.AvR (outV o) m j| ≤ PV o j
  /-- ℓ1 gains of the vertical model (certificate). -/
  gainV : ∀ o j N, ∑ m ∈ range N, |resp Vertical.AvR (outV o) m j| ≤ GV o j
  /-- Peak gains of the horizontal model (certificate). -/
  peakH : ∀ o j m, |resp Horizontal.AhR (outH o) m j| ≤ PH o j
  /-- ℓ1 gains of the horizontal model (certificate). -/
  gainH : ∀ o j N, ∑ m ∈ range N, |resp Horizontal.AhR (outH o) m j| ≤ GH o j
  /-- The nominal stays in the boxes shrunk by the tubes (TRACK_PLAN.md §3.6: `ξ̂ ⊕ Tube ⊆ D°`). -/
  nom_box : ∀ x, Beh sense32 senseP w₀ x → ∀ t, Pre toIface w₀ x t →
    (∀ o, |outV o ⬝ᵥ nomV toIface w₀ x t| ≤ bV o - τV o) ∧
      ∀ a o, |outH o ⬝ᵥ nomH toIface w₀ x a t| ≤ bH o - τH o
  /-- T1 on the nominal (VERTICAL.md `scurve_climb`, HORIZONTAL.md `course_norm`, phase-resolved). -/
  nom_T1 : ∀ x, Beh sense32 senseP w₀ x → ∀ t, Pre toIface w₀ x t → ‖nomE3 toIface w₀ x t‖ + τ3 ≤ δ
  /-- T3 on the nominal (TRACK_PLAN.md §3.9). -/
  nom_climbout : ∀ x, Beh sense32 senseP w₀ x → ∀ t, Pre toIface w₀ x t →
    inColumn (posTarget (x t)) → ρ < polyDist (posTarget (x t)) → ‖nomE3 toIface w₀ x t‖ + τ3 ≤ δ₀
  /-- T4 at `w0 = w7` on the nominal (signed vertical error on the climb, the hold). -/
  nom_w07 : ∀ x, Beh sense32 senseP w₀ x → ∀ t, Pre toIface w₀ x t →
    dist (posTarget (x t)) w7 ≤ rPassEnd → dist (posTarget (x t) + nomE3 toIface w₀ x t) w7 + τ3 ≤ rWp
  /-- T4 at `w₁ … w₆` (TRACK_PLAN.md §3.10), on the nominal: while the target is within
  `rPassMid` of the corner, the nominal vehicle (target plus nominal error) is within `r` of it with
  the 3D tube to spare. Discharged from the finished `Horizontal.corner_vehicle` (planar, signed),
  the alignment of the target with the course table, the time warp and heading coupling, and the
  vertical per-leg response (INDUCTION.md §2, corner budget). -/
  nom_corner : ∀ x, Beh sense32 senseP w₀ x → ∀ t, Pre toIface w₀ x t → ∀ i : Fin 6,
    dist (posTarget (x t)) (wp (cIdx i)) ≤ rPassMid →
      dist (posTarget (x t) + nomE3 toIface w₀ x t) (wp (cIdx i)) + τ3 ≤ rWp
  /-- The vehicle's arrival at `w0` (the first link of the reach chain): on the window
  `q ∈ [a₀, a₀ + 2)` the nominal vehicle is within `r` of `w0` with the tube to spare (the climb
  certificate; Monte Carlo: closest approach 0.070–0.073 m). -/
  nom_win0 : ∀ x, Beh sense32 senseP w₀ x → ∀ t, Pre toIface w₀ x t →
    toIface.ar x 0 ≤ toIface.q x t → toIface.q x t < toIface.ar x 0 + 2 →
      dist (posTarget (x t) + nomE3 toIface w₀ x t) (wp 0) + τ3 ≤ rWp
  /-- The along-track errors on the phases (the hypotheses of P-1, `rawScaler_ge`), on the nominal
  with the tubes to spare (PACING.md: measured `0.0216` m and `0.0425` m/s). -/
  nom_along : ∀ x, Beh sense32 senseP w₀ x → ∀ t, Pre toIface w₀ x (t + 1) →
    toIface.τv x - 1 ≤ toIface.q x t → toIface.q x t < toIface.ar x 7 →
      inner ℝ (velTarget (x t)) (velTarget (x t) - (velTarget (x (t + 1)) + nomV3 toIface w₀ x (t + 1)))
          ≤ (55 / 1000 - τ3v - 1 / 10 ^ 4) * ‖velTarget (x t)‖ ∧
        inner ℝ (velTarget (x t)) (posTarget (x t) - (posTarget (x (t + 1)) + nomE3 toIface w₀ x (t + 1)))
          ≤ (3 / 100 - τ3 - 1 / 10 ^ 4) * ‖velTarget (x t)‖
  /-- T6 on the nominal: the velocity error while the target rests at `w7`. -/
  nom_rest : ∀ x, Beh sense32 senseP w₀ x → ∀ t, Pre toIface w₀ x t →
    dist (posTarget (x t)) w7 ≤ rRest → ‖velTarget (x t)‖ ≤ rRest →
      ‖nomV3 toIface w₀ x t‖ + τ3v + 1 / 10 ^ 4 ≤ δv
  /-- The state at the completion tick (TRACK_PLAN.md §3.11, `hold_course`'s `hd`, `hv`): the
  nominal vehicle within `0.03` of `w7` and its nominal speed at most `0.05`, with the tubes. -/
  nom_complete : ∀ x, Beh sense32 senseP w₀ x → ∀ tc, Pre toIface w₀ x tc → complete w₀ x tc →
    (∀ k < tc, ¬ complete w₀ x k) →
      dist (posTarget (x tc) + nomE3 toIface w₀ x tc) w7 + τ3 + 1 / 10 ^ 6 ≤ 3 / 100 ∧
        ‖velTarget (x tc) + nomV3 toIface w₀ x tc‖ + τ3v + 1 / 10 ^ 6 ≤ 5 / 100
  -- ### The hold (TRACK_PLAN.md §3.11)
  /-- `loiter_start` at the completion tick: the stopping point is computed from estimates within
  `10⁻⁶` of the vehicle's state, and from then on the loiter target is no farther from `w7` than the
  stopping point (`hold_course`'s `hpost`). -/
  loiter_nav : ∀ x, Beh sense32 senseP w₀ x → ∀ tc, (∀ k ≤ tc, Inv1 toIface w₀ x k) →
    complete w₀ x tc → (∀ k < tc, ¬ complete w₀ x k) →
      ∃ (p : AC_PosControl.Params) (s : AC_PosControl.State), LoiterHyps p s ∧
        dist (estPos s) (pos (x tc)) ≤ 1 / 10 ^ 6 ∧ dist (estVel s) (vel (x tc)) ≤ 1 / 10 ^ 6 ∧
        ∀ t, tc ≤ t → (∀ k ≤ t, Inv1 toIface w₀ x k) →
          dist (posTarget (x t)) w7 ≤ dist (stopPt p s) w7


end

end Contracts.Track.Induction
