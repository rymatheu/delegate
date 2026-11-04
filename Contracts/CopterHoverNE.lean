import Contracts.CopterHoverUniverse
import Contracts.CopterZeroPos

/-!
# `NE_update_controller` at the hover: the frame

`Contracts.CopterZero.NE_update_controller_Z` gives the zero facts of the horizontal position
controller (`NEConcl`) but says nothing about the fields it leaves alone. This file adds the
frame, under the same hypotheses (the controller ran on the previous tick, so the
`NE_init_controller` branch is not taken):

* `NE_update_offsets_frame`: `NE_update_offsets` writes only the `x`, `y` components of the six
  offset vectors;
* `NE_update_controller_frame`: the result is `s` with exactly the position-loop state, the
  velocity PID, `_last_update_ne_ticks := clock.ticks32`, `_ne_control_scale_factor := 1.0`, the
  four attitude targets and the `x`, `y` components of eleven vectors replaced; the new limit
  vector is finite, the new desired horizontal position has the value of the old one, and the yaw
  targets are those of `calculate_yaw_and_rate_yaw_Z` when `0 ≤ _vel_max_ne_ms ≤ 10³⁰`;
* `NE_update_controller_hover`: `NEConcl` together with the frame written with the result's own
  fields, and the facts the next tick needs (ticks, scale factor, finite limit vector, unchanged
  `z` components, estimates, desired velocity and acceleration, desired position equal to the
  estimate in value); `NE_update_controller_hover_ZD` (a zero desired position stays a zero),
  `NE_update_controller_hover_yaw` (yaw targets) and `NE_update_controller_NEOK` (`NEOK` for the
  next tick);
* `NE_update_controller_hover_run`: the same for `runParams.psc`, whose velocity PID gains are
  `Pid2OK` (`runParams_pid2OK`).

The roll and pitch targets are left as unspecified values (they pass through `atanf`, `cosf`).
-/

open Float.Model UnpackedFloat AP_Math AC_PosControl Contracts.CopterZero

namespace Contracts.CopterHover

/-- `NE_update_offsets` writes only the `x`, `y` components of the six offset vectors. -/
theorem NE_update_offsets_frame (s : AC_PosControl.State) (clock : Clock) :
    ∃ a1 b1 a2 b2 : Float, ∃ a3 b3 a4 b4 a5 b5 a6 b6 : Float32, NE_update_offsets s clock =
      { s with
        _pos_offset_target_ned_m := { s._pos_offset_target_ned_m with x := a1, y := b1 },
        _pos_offset_ned_m := { s._pos_offset_ned_m with x := a2, y := b2 },
        _vel_offset_target_ned_ms := { s._vel_offset_target_ned_ms with x := a3, y := b3 },
        _vel_offset_ned_ms := { s._vel_offset_ned_ms with x := a4, y := b4 },
        _accel_offset_target_ned_mss := { s._accel_offset_target_ned_mss with x := a5, y := b5 },
        _accel_offset_ned_mss := { s._accel_offset_ned_mss with x := a6, y := b6 } } := by
  unfold NE_update_offsets
  simp only [Id.run, pure]
  split <;> exact ⟨_, _, _, _, _, _, _, _, _, _, _, _, rfl⟩


/-- `calculate_yaw_and_rate_yaw` as an update of the two yaw fields by its own results. -/
theorem calc_yaw_frame (X : AC_PosControl.State) (att : AttitudeControlInputs) :
    calculate_yaw_and_rate_yaw X att = { X with
      _yaw_target_rad := (calculate_yaw_and_rate_yaw X att)._yaw_target_rad,
      _yaw_rate_target_rads := (calculate_yaw_and_rate_yaw X att)._yaw_rate_target_rads } := by
  obtain ⟨a, b, e⟩ := calculate_yaw_and_rate_yaw_eq X att
  rw [e]

/-- **The frame of `NE_update_controller` at the hover**, with witnesses for the written values:
under the hypotheses of `NE_update_controller_Z`, the result is `s` with the listed fields
replaced, the limit vector's `x`, `y` are finite, the desired position's `x`, `y` keep their
values, and for `0 ≤ _vel_max_ne_ms ≤ 10³⁰` the yaw target is the attitude target's yaw and the
yaw rate target is `0`. -/
theorem NE_update_controller_frame (C : ConvZero) (p : Params) (s : AC_PosControl.State)
    (ahrs : AHRSInputs) (att : AttitudeControlInputs) (clock : Clock) (h : NEOK p s ahrs)
    (hact : NE_is_active s clock = true) (hoff : OffZ s)
    (hpdx : s._pos_desired_ned_m.x.IsFinite) (hpdy : s._pos_desired_ned_m.y.IsFinite)
    (hpex : s._pos_estimate_ned_m.x.IsFinite) (hpey : s._pos_estimate_ned_m.y.IsFinite)
    (hpx : s._pos_desired_ned_m.x.toReal = s._pos_estimate_ned_m.x.toReal)
    (hpy : s._pos_desired_ned_m.y.toReal = s._pos_estimate_ned_m.y.toReal)
    (hvd : ZV2 s._vel_desired_ned_ms.xy) (hve : ZV2 s._vel_estimate_ned_ms.xy)
    (had : ZV2 s._accel_desired_ned_mss.xy) (hpid : ZPID2 s._pid_vel_ne_m) :
    ∃ a1 b1 a2 b2 : Float, ∃ a3 b3 a4 b4 a5 b5 a6 b6 : Float32,
    ∃ ptx pty pdx pdy : Float, ∃ vtx vty atx aty lvx lvy roll pitch yaw yr : Float32,
    ∃ pp : AC_P_2D.State, ∃ pid : AC_PID_2D.State,
      NE_update_controller p s ahrs att clock = { s with
        _p_pos_ne_m := pp, _pid_vel_ne_m := pid,
        _last_update_ne_ticks := clock.ticks32, _ne_control_scale_factor := 1.0,
        _roll_target_rad := roll, _pitch_target_rad := pitch,
        _yaw_target_rad := yaw, _yaw_rate_target_rads := yr,
        _pos_desired_ned_m := { s._pos_desired_ned_m with x := pdx, y := pdy },
        _pos_target_ned_m := { s._pos_target_ned_m with x := ptx, y := pty },
        _vel_target_ned_ms := { s._vel_target_ned_ms with x := vtx, y := vty },
        _accel_target_ned_mss := { s._accel_target_ned_mss with x := atx, y := aty },
        _limit_vector_ned := { s._limit_vector_ned with x := lvx, y := lvy },
        _pos_offset_target_ned_m := { s._pos_offset_target_ned_m with x := a1, y := b1 },
        _pos_offset_ned_m := { s._pos_offset_ned_m with x := a2, y := b2 },
        _vel_offset_target_ned_ms := { s._vel_offset_target_ned_ms with x := a3, y := b3 },
        _vel_offset_ned_ms := { s._vel_offset_ned_ms with x := a4, y := b4 },
        _accel_offset_target_ned_mss := { s._accel_offset_target_ned_mss with x := a5, y := b5 },
        _accel_offset_ned_mss := { s._accel_offset_ned_mss with x := a6, y := b6 } } ∧
      lvx.IsFinite ∧ lvy.IsFinite ∧
      pdx.IsFinite ∧ pdx.toReal = s._pos_desired_ned_m.x.toReal ∧
      pdy.IsFinite ∧ pdy.toReal = s._pos_desired_ned_m.y.toReal ∧
      (0 ≤ s._vel_max_ne_ms.toReal → s._vel_max_ne_ms.toReal ≤ 1e30 →
        yaw = att.get_att_target_euler_rad.z ∧ yr = 0) := by
  unfold NE_update_controller
  simp (config := {zeta := false}) only [Id.run, pure]
  extract_lets s0 sc dz jpf jpm si
  simp (config := {zeta := false}) only [s0, hact, Bool.not_true, Bool.false_eq_true, if_false, jpm]
  extract_lets s1 s2 s3 cp comb sA sB vt2 vt1 vt0 sC vtne sD cv1 cv0 sE at2 at1 at0 sF sG atne sH
    amax accmax sI jpv vn
  obtain ⟨a1, b1, a2, b2, a3, b3, a4, b4, a5, b5, a6, b6, hoffeq⟩ := NE_update_offsets_frame s1 clock
  have hoffZ : OffZ s2 := NE_update_offsets_Z C s1 clock hoff h.dt h.dtb h.amax h.jmax h.jmaxb
  have e2 : s2 = _ := hoffeq
  clear_value s2
  subst e2
  have hpo : ZV2p s3._pos_offset_ned_m.xy := hoffZ.2.1
  have hvo : ZV2 s3._vel_offset_ned_ms.xy := hoffZ.2.2.2.1
  have hao : ZV2 s3._accel_offset_ned_mss.xy := hoffZ.2.2.2.2.2
  -- the position loop: zero error
  have hd0 : ZD (Vector2f.topostype dz).x := C.toFloat_zero _ Z_zero
  have hd1 : ZD (Vector2f.topostype dz).y := C.toFloat_zero _ Z_zero
  have hex : ZD (s3._pos_target_ned_m.xy - comb).x := by
    have a1 : ((s._pos_desired_ned_m.xy + s3._pos_offset_ned_m.xy).x).IsFinite ∧
        ((s._pos_desired_ned_m.xy + s3._pos_offset_ned_m.xy).x).toReal =
          s._pos_desired_ned_m.x.toReal :=
      add_ZD_right hpdx hpo.1
    have a2 : ((s._pos_estimate_ned_m.xy + Vector2f.topostype dz).x).IsFinite ∧
        ((s._pos_estimate_ned_m.xy + Vector2f.topostype dz).x).toReal =
          s._pos_estimate_ned_m.x.toReal :=
      add_ZD_right hpex hd0
    exact ZD_sub_eq (a := (s._pos_desired_ned_m.xy + s3._pos_offset_ned_m.xy).x)
      (b := (s._pos_estimate_ned_m.xy + Vector2f.topostype dz).x) a1.1 a2.1
      (a1.2.trans (hpx.trans a2.2.symm))
  have hey : ZD (s3._pos_target_ned_m.xy - comb).y := by
    have a1 : ((s._pos_desired_ned_m.xy + s3._pos_offset_ned_m.xy).y).IsFinite ∧
        ((s._pos_desired_ned_m.xy + s3._pos_offset_ned_m.xy).y).toReal =
          s._pos_desired_ned_m.y.toReal :=
      add_ZD_right hpdy hpo.2
    have a2 : ((s._pos_estimate_ned_m.xy + Vector2f.topostype dz).y).IsFinite ∧
        ((s._pos_estimate_ned_m.xy + Vector2f.topostype dz).y).toReal =
          s._pos_estimate_ned_m.y.toReal :=
      add_ZD_right hpey hd1
    exact ZD_sub_eq (a := (s._pos_desired_ned_m.xy + s3._pos_offset_ned_m.xy).y)
      (b := (s._pos_estimate_ned_m.xy + Vector2f.topostype dz).y) a1.1 a2.1
      (a1.2.trans (hpy.trans a2.2.symm))
  have hE : ZV2 (s3._pos_target_ned_m.xy - comb).tofloat :=
    ⟨C.toFloat32_zero _ hex, C.toFloat32_zero _ hey⟩
  have EP := p2_update_all_Z p._p_pos_ne_m s3._p_pos_ne_m hE
  -- the desired position keeps its value
  have eT : sA._pos_target_ned_m.xy = s3._pos_target_ned_m.xy := EP.2.1
  have hpdX : sB._pos_desired_ned_m.x.IsFinite ∧
      sB._pos_desired_ned_m.x.toReal = s._pos_desired_ned_m.x.toReal := by
    show (sA._pos_target_ned_m.xy.x - s3._pos_offset_ned_m.xy.x).IsFinite ∧
      (sA._pos_target_ned_m.xy.x - s3._pos_offset_ned_m.xy.x).toReal = _
    rw [eT]
    have a1 := add_ZD_right hpdx hpo.1
    exact sub_exact_d a1.1 hpo.1.1 hpdx (by rw [hpo.1.2, sub_zero]; exact a1.2)
  have hpdY : sB._pos_desired_ned_m.y.IsFinite ∧
      sB._pos_desired_ned_m.y.toReal = s._pos_desired_ned_m.y.toReal := by
    show (sA._pos_target_ned_m.xy.y - s3._pos_offset_ned_m.xy.y).IsFinite ∧
      (sA._pos_target_ned_m.xy.y - s3._pos_offset_ned_m.xy.y).toReal = _
    rw [eT]
    have a1 := add_ZD_right hpdy hpo.2
    exact sub_exact_d a1.1 hpo.2.1 hpdy (by rw [hpo.2.2, sub_zero]; exact a1.2)
  -- the velocity and acceleration loops
  have hvt2 : ZV2 vt2 := EP.2.2.1
  have hvtne : ZV2 vtne := ZV2_add (ZV2_mul (ZV2_mul hvt2 h.scale) h.nescale) (ZV2_add hvd hvo)
  have hVT : ZV2 sD._vel_target_ned_ms.xy := hvtne
  have hVE : ZV2 cv0 := ZV2_add hve ZV2_default
  have FP := pid2_update_all_Z _ h.pid (s := sD._pid_vel_ne_m) hpid hVT hVE (dt := sD._dt_s) h.dt
    (h.dtb.trans (by norm_num)) (limit := sD._limit_vector_ned.xy) h.lim
  have hat2 : ZV2 at2 := FP.2
  have hatne : ZV2 atne := ZV2_add (ZV2_mul (ZV2_mul hat2 h.scale) h.nescale)
    (ZV2_add had hao)
  split
  all_goals
    simp only [jpv, jpf]
    split
  all_goals
    rw [calc_yaw_frame]
    refine ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
      rfl, ?_, ?_, hpdX.1, hpdX.2, hpdY.1, hpdY.2, ?_⟩
    · first | exact Z_zero.1 | exact hatne.1.1
    · first | exact Z_zero.1 | exact hatne.2.1
    · intro h0 h1
      rw [calculate_yaw_and_rate_yaw_Z _ att ?_ ?_ ?_ ?_]
      · exact ⟨rfl, rfl⟩
      · exact hvd
      · exact h.vmax
      · exact h0
      · exact h1

/-- **`NE_update_controller` at the hover: zero facts and frame.** Under the hypotheses of
`NE_update_controller_Z`, the result `r` satisfies `NEConcl`, and `r` is `s` with exactly these
fields replaced: the position-loop state `_p_pos_ne_m`, the velocity PID `_pid_vel_ne_m`,
`_last_update_ne_ticks` (now `clock.ticks32`), `_ne_control_scale_factor` (now `1.0`), the four
attitude targets, and the `x`, `y` components of the desired and target positions, the velocity
and acceleration targets, the limit vector and the six offset vectors. In particular every
vertical field, the `z` components of all vectors, the limits, the vertical PIDs, the terrain
terms, the estimates, the desired velocity and acceleration and `_dt_s` are those of `s`. The
limit vector's `x`, `y` are finite, and the desired horizontal position keeps its value (so it
still equals the estimate in value, the hypothesis `hpx`, `hpy` of the next tick). -/
theorem NE_update_controller_hover (C : ConvZero) (p : Params) (s : AC_PosControl.State)
    (ahrs : AHRSInputs) (att : AttitudeControlInputs) (clock : Clock) (h : NEOK p s ahrs)
    (hact : NE_is_active s clock = true) (hoff : OffZ s)
    (hpdx : s._pos_desired_ned_m.x.IsFinite) (hpdy : s._pos_desired_ned_m.y.IsFinite)
    (hpex : s._pos_estimate_ned_m.x.IsFinite) (hpey : s._pos_estimate_ned_m.y.IsFinite)
    (hpx : s._pos_desired_ned_m.x.toReal = s._pos_estimate_ned_m.x.toReal)
    (hpy : s._pos_desired_ned_m.y.toReal = s._pos_estimate_ned_m.y.toReal)
    (hvd : ZV2 s._vel_desired_ned_ms.xy) (hve : ZV2 s._vel_estimate_ned_ms.xy)
    (had : ZV2 s._accel_desired_ned_mss.xy) (hpid : ZPID2 s._pid_vel_ne_m) :
    let r := NE_update_controller p s ahrs att clock
    NEConcl r ∧
    r = { s with
      _p_pos_ne_m := r._p_pos_ne_m, _pid_vel_ne_m := r._pid_vel_ne_m,
      _last_update_ne_ticks := r._last_update_ne_ticks,
      _ne_control_scale_factor := r._ne_control_scale_factor,
      _roll_target_rad := r._roll_target_rad, _pitch_target_rad := r._pitch_target_rad,
      _yaw_target_rad := r._yaw_target_rad, _yaw_rate_target_rads := r._yaw_rate_target_rads,
      _pos_desired_ned_m := { s._pos_desired_ned_m with
        x := r._pos_desired_ned_m.x, y := r._pos_desired_ned_m.y },
      _pos_target_ned_m := { s._pos_target_ned_m with
        x := r._pos_target_ned_m.x, y := r._pos_target_ned_m.y },
      _vel_target_ned_ms := { s._vel_target_ned_ms with
        x := r._vel_target_ned_ms.x, y := r._vel_target_ned_ms.y },
      _accel_target_ned_mss := { s._accel_target_ned_mss with
        x := r._accel_target_ned_mss.x, y := r._accel_target_ned_mss.y },
      _limit_vector_ned := { s._limit_vector_ned with
        x := r._limit_vector_ned.x, y := r._limit_vector_ned.y },
      _pos_offset_target_ned_m := { s._pos_offset_target_ned_m with
        x := r._pos_offset_target_ned_m.x, y := r._pos_offset_target_ned_m.y },
      _pos_offset_ned_m := { s._pos_offset_ned_m with
        x := r._pos_offset_ned_m.x, y := r._pos_offset_ned_m.y },
      _vel_offset_target_ned_ms := { s._vel_offset_target_ned_ms with
        x := r._vel_offset_target_ned_ms.x, y := r._vel_offset_target_ned_ms.y },
      _vel_offset_ned_ms := { s._vel_offset_ned_ms with
        x := r._vel_offset_ned_ms.x, y := r._vel_offset_ned_ms.y },
      _accel_offset_target_ned_mss := { s._accel_offset_target_ned_mss with
        x := r._accel_offset_target_ned_mss.x, y := r._accel_offset_target_ned_mss.y },
      _accel_offset_ned_mss := { s._accel_offset_ned_mss with
        x := r._accel_offset_ned_mss.x, y := r._accel_offset_ned_mss.y } } ∧
    r._last_update_ne_ticks = clock.ticks32 ∧ r._ne_control_scale_factor = 1.0 ∧
    FinV2 r._limit_vector_ned.xy ∧
    r._pos_desired_ned_m.z = s._pos_desired_ned_m.z ∧ r._pos_target_ned_m.z = s._pos_target_ned_m.z ∧
    r._vel_desired_ned_ms = s._vel_desired_ned_ms ∧
    r._accel_desired_ned_mss = s._accel_desired_ned_mss ∧
    r._pos_estimate_ned_m = s._pos_estimate_ned_m ∧ r._vel_estimate_ned_ms = s._vel_estimate_ned_ms ∧
    r._pos_desired_ned_m.x.IsFinite ∧
    r._pos_desired_ned_m.x.toReal = s._pos_desired_ned_m.x.toReal ∧
    r._pos_desired_ned_m.y.IsFinite ∧
    r._pos_desired_ned_m.y.toReal = s._pos_desired_ned_m.y.toReal ∧
    r._pos_desired_ned_m.x.toReal = r._pos_estimate_ned_m.x.toReal ∧
    r._pos_desired_ned_m.y.toReal = r._pos_estimate_ned_m.y.toReal ∧
    r._pos_offset_target_ned_m.z = s._pos_offset_target_ned_m.z ∧
    r._pos_offset_ned_m.z = s._pos_offset_ned_m.z ∧
    r._vel_offset_target_ned_ms.z = s._vel_offset_target_ned_ms.z ∧
    r._vel_offset_ned_ms.z = s._vel_offset_ned_ms.z ∧
    r._accel_offset_target_ned_mss.z = s._accel_offset_target_ned_mss.z ∧
    r._accel_offset_ned_mss.z = s._accel_offset_ned_mss.z ∧
    r._vel_target_ned_ms.z = s._vel_target_ned_ms.z ∧
    r._accel_target_ned_mss.z = s._accel_target_ned_mss.z ∧
    r._limit_vector_ned.z = s._limit_vector_ned.z := by
  have hZ := NE_update_controller_Z C p s ahrs att clock h hact hoff hpdx hpdy hpex hpey hpx hpy hvd hve had hpid
  obtain ⟨a1, b1, a2, b2, a3, b3, a4, b4, a5, b5, a6, b6, ptx, pty, pdx, pdy, vtx, vty, atx, aty,
    lvx, lvy, roll, pitch, yaw, yr, pp, pid, e, hl1, hl2, hx1, hx2, hy1, hy2, -⟩ :=
    NE_update_controller_frame C p s ahrs att clock h hact hoff hpdx hpdy hpex hpey hpx hpy hvd hve had hpid
  rw [e] at hZ ⊢
  exact ⟨hZ, rfl, rfl, rfl, ⟨hl1, hl2⟩, rfl, rfl, rfl, rfl, rfl, rfl, hx1, hx2, hy1, hy2,
    hx2.trans hpx, hy2.trans hpy, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- At a zero desired horizontal position, `NE_update_controller` keeps it a zero. -/
theorem NE_update_controller_hover_ZD (C : ConvZero) (p : Params) (s : AC_PosControl.State)
    (ahrs : AHRSInputs) (att : AttitudeControlInputs) (clock : Clock) (h : NEOK p s ahrs)
    (hact : NE_is_active s clock = true) (hoff : OffZ s)
    (hpdx : s._pos_desired_ned_m.x.IsFinite) (hpdy : s._pos_desired_ned_m.y.IsFinite)
    (hpex : s._pos_estimate_ned_m.x.IsFinite) (hpey : s._pos_estimate_ned_m.y.IsFinite)
    (hpx : s._pos_desired_ned_m.x.toReal = s._pos_estimate_ned_m.x.toReal)
    (hpy : s._pos_desired_ned_m.y.toReal = s._pos_estimate_ned_m.y.toReal)
    (hvd : ZV2 s._vel_desired_ned_ms.xy) (hve : ZV2 s._vel_estimate_ned_ms.xy)
    (had : ZV2 s._accel_desired_ned_mss.xy) (hpid : ZPID2 s._pid_vel_ne_m)
    (hzx : ZD s._pos_desired_ned_m.x) (hzy : ZD s._pos_desired_ned_m.y) :
    ZD (NE_update_controller p s ahrs att clock)._pos_desired_ned_m.x ∧
      ZD (NE_update_controller p s ahrs att clock)._pos_desired_ned_m.y := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hx1, hx2, hy1, hy2, -⟩ :=
    NE_update_controller_hover C p s ahrs att clock h hact hoff hpdx hpdy hpex hpey hpx hpy hvd hve had hpid
  exact ⟨⟨hx1, hx2.trans hzx.2⟩, ⟨hy1, hy2.trans hzy.2⟩⟩

/-- At the hover, `NE_update_controller` sets the yaw target to the attitude target's yaw and the
yaw rate target to `0` (for `0 ≤ _vel_max_ne_ms ≤ 10³⁰`). -/
theorem NE_update_controller_hover_yaw (C : ConvZero) (p : Params) (s : AC_PosControl.State)
    (ahrs : AHRSInputs) (att : AttitudeControlInputs) (clock : Clock) (h : NEOK p s ahrs)
    (hact : NE_is_active s clock = true) (hoff : OffZ s)
    (hpdx : s._pos_desired_ned_m.x.IsFinite) (hpdy : s._pos_desired_ned_m.y.IsFinite)
    (hpex : s._pos_estimate_ned_m.x.IsFinite) (hpey : s._pos_estimate_ned_m.y.IsFinite)
    (hpx : s._pos_desired_ned_m.x.toReal = s._pos_estimate_ned_m.x.toReal)
    (hpy : s._pos_desired_ned_m.y.toReal = s._pos_estimate_ned_m.y.toReal)
    (hvd : ZV2 s._vel_desired_ned_ms.xy) (hve : ZV2 s._vel_estimate_ned_ms.xy)
    (had : ZV2 s._accel_desired_ned_mss.xy) (hpid : ZPID2 s._pid_vel_ne_m)
    (hvm0 : 0 ≤ s._vel_max_ne_ms.toReal) (hvmb : s._vel_max_ne_ms.toReal ≤ 1e30) :
    (NE_update_controller p s ahrs att clock)._yaw_target_rad = att.get_att_target_euler_rad.z ∧
      (NE_update_controller p s ahrs att clock)._yaw_rate_target_rads = 0 := by
  obtain ⟨a1, b1, a2, b2, a3, b3, a4, b4, a5, b5, a6, b6, ptx, pty, pdx, pdy, vtx, vty, atx, aty,
    lvx, lvy, roll, pitch, yaw, yr, pp, pid, e, -, -, -, -, -, -, hyaw⟩ :=
    NE_update_controller_frame C p s ahrs att clock h hact hoff hpdx hpdy hpex hpey hpx hpy hvd hve had hpid
  rw [e]
  exact hyaw hvm0 hvmb

/-- The next tick's `NEOK`: after `NE_update_controller` at the hover, the controller limits are
those of `s`, the limit vector is finite and the control scale factor is `1.0`; only the AHRS
scaler of the next tick must be finite. -/
theorem NE_update_controller_NEOK (C : ConvZero) (p : Params) (s : AC_PosControl.State)
    (ahrs : AHRSInputs) (att : AttitudeControlInputs) (clock : Clock) (h : NEOK p s ahrs)
    (hact : NE_is_active s clock = true) (hoff : OffZ s)
    (hpdx : s._pos_desired_ned_m.x.IsFinite) (hpdy : s._pos_desired_ned_m.y.IsFinite)
    (hpex : s._pos_estimate_ned_m.x.IsFinite) (hpey : s._pos_estimate_ned_m.y.IsFinite)
    (hpx : s._pos_desired_ned_m.x.toReal = s._pos_estimate_ned_m.x.toReal)
    (hpy : s._pos_desired_ned_m.y.toReal = s._pos_estimate_ned_m.y.toReal)
    (hvd : ZV2 s._vel_desired_ned_ms.xy) (hve : ZV2 s._vel_estimate_ned_ms.xy)
    (had : ZV2 s._accel_desired_ned_mss.xy) (hpid : ZPID2 s._pid_vel_ne_m)
    (ahrs' : AHRSInputs) (hsc : ahrs'.get_control_gain_scaler_XY.IsFinite) :
    NEOK p (NE_update_controller p s ahrs att clock) ahrs' := by
  obtain ⟨-, e, -, hsf, hlim, -⟩ := NE_update_controller_hover C p s ahrs att clock h hact hoff hpdx hpdy hpex hpey hpx hpy hvd hve had hpid
  rw [e]
  exact ⟨h.pid, h.dt, h.dtb, h.amax, h.jmax, h.jmaxb, h.vmax, hlim, hsc, hsf ▸ by decide⟩

/-! ## The run parameters -/

/-- The binary32 literal `5.0`. -/
theorem lit_five : (5.0 : Float32).IsFinite ∧ (5.0 : Float32).toReal = 5 := by
  have h := litPos (x := (5.0 : Float32)) (m := 10485760) (e := -21) (hm := by decide) (by rfl)
  refine ⟨h.1, ?_⟩
  rw [h.2]; norm_num

/-- The horizontal velocity PID gains of the run parameters (`P = 2`, `I = 1`, `D = 0.25`,
`FF = 0`, `FLTE = FLTD = 5`) are `Pid2OK`. -/
theorem runParams_pid2OK : Pid2OK runParams.psc._pid_vel_ne_m where
  P := by decide
  I := by decide
  D := by decide
  FF := by decide
  FLTE := by decide
  FLTD := by decide
  FLTEb := by
    show |(5.0 : Float32).toReal| ≤ 1e30
    rw [lit_five.2]; norm_num
  FLTDb := by
    show |(5.0 : Float32).toReal| ≤ 1e30
    rw [lit_five.2]; norm_num

/-- `NEOK` for the run parameters, from the facts about the state and the AHRS scaler. -/
theorem NEOK_run (s : AC_PosControl.State) (ahrs : AHRSInputs) (hdt : s._dt_s.IsFinite)
    (hdtb : |s._dt_s.toReal| ≤ 1e18) (hamax : s._accel_max_ne_mss.IsFinite)
    (hjmax : s._jerk_max_ne_msss.IsFinite) (hjmaxb : |s._jerk_max_ne_msss.toReal| ≤ 1e18)
    (hvmax : s._vel_max_ne_ms.IsFinite) (hlim : FinV2 s._limit_vector_ned.xy)
    (hscale : ahrs.get_control_gain_scaler_XY.IsFinite)
    (hnescale : s._ne_control_scale_factor.IsFinite) : NEOK runParams.psc s ahrs :=
  ⟨runParams_pid2OK, hdt, hdtb, hamax, hjmax, hjmaxb, hvmax, hlim, hscale, hnescale⟩

/-- **`NE_update_controller_hover` for the run parameters** (`runParams.psc`), with the velocity
PID gains discharged (`runParams_pid2OK`). -/
theorem NE_update_controller_hover_run (C : ConvZero) (s : AC_PosControl.State)
    (ahrs : AHRSInputs) (att : AttitudeControlInputs) (clock : Clock)
    (hdt : s._dt_s.IsFinite) (hdtb : |s._dt_s.toReal| ≤ 1e18)
    (hamax : s._accel_max_ne_mss.IsFinite) (hjmax : s._jerk_max_ne_msss.IsFinite)
    (hjmaxb : |s._jerk_max_ne_msss.toReal| ≤ 1e18) (hvmax : s._vel_max_ne_ms.IsFinite)
    (hlim : FinV2 s._limit_vector_ned.xy) (hscale : ahrs.get_control_gain_scaler_XY.IsFinite)
    (hnescale : s._ne_control_scale_factor.IsFinite)
    (hact : NE_is_active s clock = true) (hoff : OffZ s)
    (hpdx : s._pos_desired_ned_m.x.IsFinite) (hpdy : s._pos_desired_ned_m.y.IsFinite)
    (hpex : s._pos_estimate_ned_m.x.IsFinite) (hpey : s._pos_estimate_ned_m.y.IsFinite)
    (hpx : s._pos_desired_ned_m.x.toReal = s._pos_estimate_ned_m.x.toReal)
    (hpy : s._pos_desired_ned_m.y.toReal = s._pos_estimate_ned_m.y.toReal)
    (hvd : ZV2 s._vel_desired_ned_ms.xy) (hve : ZV2 s._vel_estimate_ned_ms.xy)
    (had : ZV2 s._accel_desired_ned_mss.xy) (hpid : ZPID2 s._pid_vel_ne_m) :
    let r := NE_update_controller runParams.psc s ahrs att clock
    NEConcl r ∧
    r = { s with
      _p_pos_ne_m := r._p_pos_ne_m, _pid_vel_ne_m := r._pid_vel_ne_m,
      _last_update_ne_ticks := r._last_update_ne_ticks,
      _ne_control_scale_factor := r._ne_control_scale_factor,
      _roll_target_rad := r._roll_target_rad, _pitch_target_rad := r._pitch_target_rad,
      _yaw_target_rad := r._yaw_target_rad, _yaw_rate_target_rads := r._yaw_rate_target_rads,
      _pos_desired_ned_m := { s._pos_desired_ned_m with
        x := r._pos_desired_ned_m.x, y := r._pos_desired_ned_m.y },
      _pos_target_ned_m := { s._pos_target_ned_m with
        x := r._pos_target_ned_m.x, y := r._pos_target_ned_m.y },
      _vel_target_ned_ms := { s._vel_target_ned_ms with
        x := r._vel_target_ned_ms.x, y := r._vel_target_ned_ms.y },
      _accel_target_ned_mss := { s._accel_target_ned_mss with
        x := r._accel_target_ned_mss.x, y := r._accel_target_ned_mss.y },
      _limit_vector_ned := { s._limit_vector_ned with
        x := r._limit_vector_ned.x, y := r._limit_vector_ned.y },
      _pos_offset_target_ned_m := { s._pos_offset_target_ned_m with
        x := r._pos_offset_target_ned_m.x, y := r._pos_offset_target_ned_m.y },
      _pos_offset_ned_m := { s._pos_offset_ned_m with
        x := r._pos_offset_ned_m.x, y := r._pos_offset_ned_m.y },
      _vel_offset_target_ned_ms := { s._vel_offset_target_ned_ms with
        x := r._vel_offset_target_ned_ms.x, y := r._vel_offset_target_ned_ms.y },
      _vel_offset_ned_ms := { s._vel_offset_ned_ms with
        x := r._vel_offset_ned_ms.x, y := r._vel_offset_ned_ms.y },
      _accel_offset_target_ned_mss := { s._accel_offset_target_ned_mss with
        x := r._accel_offset_target_ned_mss.x, y := r._accel_offset_target_ned_mss.y },
      _accel_offset_ned_mss := { s._accel_offset_ned_mss with
        x := r._accel_offset_ned_mss.x, y := r._accel_offset_ned_mss.y } } ∧
    r._last_update_ne_ticks = clock.ticks32 ∧ r._ne_control_scale_factor = 1.0 ∧
    FinV2 r._limit_vector_ned.xy ∧
    r._pos_desired_ned_m.z = s._pos_desired_ned_m.z ∧ r._pos_target_ned_m.z = s._pos_target_ned_m.z ∧
    r._vel_desired_ned_ms = s._vel_desired_ned_ms ∧
    r._accel_desired_ned_mss = s._accel_desired_ned_mss ∧
    r._pos_estimate_ned_m = s._pos_estimate_ned_m ∧ r._vel_estimate_ned_ms = s._vel_estimate_ned_ms ∧
    r._pos_desired_ned_m.x.IsFinite ∧
    r._pos_desired_ned_m.x.toReal = s._pos_desired_ned_m.x.toReal ∧
    r._pos_desired_ned_m.y.IsFinite ∧
    r._pos_desired_ned_m.y.toReal = s._pos_desired_ned_m.y.toReal ∧
    r._pos_desired_ned_m.x.toReal = r._pos_estimate_ned_m.x.toReal ∧
    r._pos_desired_ned_m.y.toReal = r._pos_estimate_ned_m.y.toReal ∧
    r._pos_offset_target_ned_m.z = s._pos_offset_target_ned_m.z ∧
    r._pos_offset_ned_m.z = s._pos_offset_ned_m.z ∧
    r._vel_offset_target_ned_ms.z = s._vel_offset_target_ned_ms.z ∧
    r._vel_offset_ned_ms.z = s._vel_offset_ned_ms.z ∧
    r._accel_offset_target_ned_mss.z = s._accel_offset_target_ned_mss.z ∧
    r._accel_offset_ned_mss.z = s._accel_offset_ned_mss.z ∧
    r._vel_target_ned_ms.z = s._vel_target_ned_ms.z ∧
    r._accel_target_ned_mss.z = s._accel_target_ned_mss.z ∧
    r._limit_vector_ned.z = s._limit_vector_ned.z :=
  NE_update_controller_hover C runParams.psc s ahrs att clock
    (NEOK_run s ahrs hdt hdtb hamax hjmax hjmaxb hvmax hlim hscale hnescale) hact hoff hpdx hpdy
    hpex hpey hpx hpy hvd hve had hpid

end Contracts.CopterHover
