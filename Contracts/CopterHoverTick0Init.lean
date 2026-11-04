import Contracts.CopterHoverTick0Boot

/-!
# Tick 0 of the hover run: the switch into Auto

On the first tick the vehicle is not yet in Auto, so `Copter.loop` calls the harness's
`enter_auto` after the common prefix: `ModeAuto::init` runs `wp_and_spline_init_m` (with speed
`0` and no stopping point given), sets `waiting_to_start`, and the rate time constants are set.
This file follows `wp_and_spline_init_m` on the boot navigator and the position controller left
by the prefix (the boot controller with the loop time and the estimates of the sample):

* `D_init_controller_stopping_point` (`t0_Dinit_frame`, `t0_Dinit_facts`): the terrain terms and
  the vertical offsets are zeros, both vertical PIDs are put in reset, the acceleration
  integrator is set to a zero (the stored throttle is the hover throttle and the acceleration
  target is the clipped estimate itself, so all three terms vanish), the update stamp is the
  current tick, and the position target is the stopping point, which at zero vertical speed is
  the narrowed and widened altitude estimate, within `10⁻⁶` of `-1` (`t0_stop_D`, with
  `WidenSpec` and `NarrowSpec`);
* `NE_init_controller_stopping_point` (`t0_NEinit_frame`, `t0_NEinit_facts`): the controller is
  active (the boot stamp `0` is one tick old), so the acceleration target stays the zero vector;
  the horizontal offsets, desired velocity and acceleration, velocity PID memory are zeros, the
  horizontal position target is the zero stopping point, and the update stamp is the current tick;
* the speed and acceleration limits (`t0_limits`): the values of the run, evaluated by the kernel
  on closed terms (`PscLim`, and `_accel_max_d_mss = WP_ACC_Z = 1`);
* the navigator (`t0_init_nav`): the steady speed bookkeeping, three empty legs, the reached flag
  set, origin and destination at the stopping point, time stamp `millis() = 2`.

`t0_enter_auto` collects the facts in `Boot7`.
-/

namespace Contracts.CopterHover

open AP_Math AC_WPNav Contracts.CopterZero
open Contracts.CopterVertNear (Near32 Near64 NarrowSpec dtF near_narrow near_add u32 η32 u32_le
  η32_le u32_nonneg η32_nonneg constrain_float_of_near)

/-! ## The vertical stopping point at rest -/

/-- **The vertical stopping point at zero vertical speed**: within `10⁻⁶` of `-1` for an altitude
estimate within `10⁻¹⁵` of `-1`, a zero vertical speed estimate, zero offsets and a vertical
acceleration limit of at least `1/100`. -/
theorem t0_stop_D (N : NarrowSpec 2) (W : WidenSpec) {psc : AC_PosControl.State}
    (hpez : Near64 psc._pos_estimate_ned_m.z (-1) 1e-15)
    (hvez : CopterZero.Z psc._vel_estimate_ned_ms.z)
    (hpo : ZD psc._pos_offset_ned_m.z) (hvo : CopterZero.Z psc._vel_offset_ned_ms.z)
    (haf : psc._accel_max_d_mss.IsFinite) (ha1 : 1 / 100 ≤ psc._accel_max_d_mss.toReal) :
    Near64 (AC_PosControl.get_stopping_point_D_m runParams.psc psc) (-1) 1e-6 := by
  have hkP : AC_P_1D.kP runParams.psc._p_pos_d_m = 1.0 := by decide
  have hp1 : is_positive (1.0 : Float32) = true := by decide
  have he : (2 : ℝ) ^ (-23 : ℤ) ≤ 1 / 100 := by rw [eps_eq]; norm_num
  have hpa : is_positive psc._accel_max_d_mss = true := is_positive_of_ge haf (he.trans ha1)
  have hu := u32_le; have hu0 := u32_nonneg; have hη := η32_le; have hη0 := η32_nonneg
  unfold AC_PosControl.get_stopping_point_D_m
  simp only [hkP, hp1, hpa, Bool.not_true, Bool.or_false, Bool.false_eq_true, if_false]
  -- the position, narrowed, widened, offset removed, narrowed again
  have h0 := near_narrow N hpez (by norm_num)
  have h0' : Near32 (tofloat psc._pos_estimate_ned_m.z) (-1) (1 / 10000000) :=
    h0.mono (by norm_num; nlinarith)
  set c0 := tofloat psc._pos_estimate_ned_m.z with hc0
  obtain ⟨hw1, hw2⟩ : (topostype c0).IsFinite ∧ (topostype c0).toReal = c0.toReal :=
    W.exact c0 h0'.1
  obtain ⟨hd1, hd2⟩ := sub_exact_d (f := topostype c0) hw1 hpo.1 hw1 (by rw [hpo.2, sub_zero])
  have h1 : Near64 (topostype c0 - psc._pos_offset_ned_m.z) (-1) (1 / 10000000) := by
    refine ⟨hd1, ?_⟩
    rw [hd2, hw2]
    exact h0'.2
  have h2 := near_narrow N h1 (by norm_num)
  have h2' : Near32 (tofloat (topostype c0 - psc._pos_offset_ned_m.z)) (-1) (2 / 10000000) :=
    h2.mono (by norm_num; nlinarith)
  -- the velocity: a zero, whose stopping distance is a zero
  have hv := Z_sub hvez hvo
  have hvb : |(psc._vel_estimate_ned_ms.z - psc._vel_offset_ned_ms.z).toReal| <
      psc._accel_max_d_mss.toReal := by
    rw [hv.2, abs_zero]; linarith
  obtain ⟨hs1, hs2⟩ := stopping_distance_small hv.1 haf hvb ha1
  have hs : Near32 (stopping_distance (psc._vel_estimate_ned_ms.z - psc._vel_offset_ned_ms.z) 1.0
      psc._accel_max_d_mss) 0 0 := ⟨hs1, by rw [hs2, hv.2]; simp⟩
  have hlo : (-(3.0 : Float32)).IsFinite := (Float32.isFinite_neg _).2 lit_three32.1
  have hc := constrain_float_of_near hs hlo lit_two.1
    (by rw [Float32.toReal_neg, lit_three32.2]; norm_num) (by rw [lit_two.2]; norm_num)
  have hc' : constrain_float (stopping_distance (psc._vel_estimate_ned_ms.z -
      psc._vel_offset_ned_ms.z) 1.0 psc._accel_max_d_mss)
      (-AC_PosControl.POSCONTROL_STOPPING_DIST_UP_MAX_M)
      AC_PosControl.POSCONTROL_STOPPING_DIST_DOWN_MAX_M = stopping_distance
      (psc._vel_estimate_ned_ms.z - psc._vel_offset_ned_ms.z) 1.0 psc._accel_max_d_mss := hc
  rw [hc']
  -- the sum, widened
  have hsum := near_add (B := 2) h2' hs (by norm_num) (by norm_num)
  obtain ⟨hw3, hw4⟩ : (topostype (tofloat (topostype c0 - psc._pos_offset_ned_m.z) +
      stopping_distance (psc._vel_estimate_ned_ms.z - psc._vel_offset_ned_ms.z) 1.0
        psc._accel_max_d_mss)).IsFinite ∧ (topostype (tofloat (topostype c0 -
      psc._pos_offset_ned_m.z) + stopping_distance (psc._vel_estimate_ned_ms.z -
      psc._vel_offset_ned_ms.z) 1.0 psc._accel_max_d_mss)).toReal = (tofloat (topostype c0 -
      psc._pos_offset_ned_m.z) + stopping_distance (psc._vel_estimate_ned_ms.z -
      psc._vel_offset_ned_ms.z) 1.0 psc._accel_max_d_mss).toReal := W.exact _ hsum.1
  refine ⟨hw3, ?_⟩
  rw [hw4]
  have := hsum.2
  rw [show (-1 : ℝ) + 0 = -1 by norm_num] at this
  refine this.trans ?_
  norm_num
  nlinarith

/-! ## `D_init_controller_stopping_point` -/

/-- `D_init_controller` writes only the terrain terms, the vertical offsets, the `z` components
of the position, velocity and acceleration targets and desired values, the two vertical PIDs and
the update stamp. -/
theorem t0_Dinit_frame (p : AC_PosControl.Params) (s : AC_PosControl.State)
    (ahrs : AC_PosControl.AHRSInputs) (mi : AP_Motors.Inputs)
    (att : AC_PosControl.AttitudeControlInputs) (clock : AC_PosControl.Clock)
    (hclk : ¬ (clock.millis - s._posvelaccel_offset_target_d_ms >
      AC_PosControl.POSCONTROL_POSVELACCEL_OFFSET_TARGET_TIMEOUT_MS)) :
    let r := AC_PosControl.D_init_controller p s ahrs mi att clock
    r = { s with
      _pos_terrain_target_d_m := r._pos_terrain_target_d_m
      _pos_terrain_d_m := r._pos_terrain_d_m
      _vel_terrain_d_ms := r._vel_terrain_d_ms
      _accel_terrain_d_mss := r._accel_terrain_d_mss
      _pos_offset_target_ned_m := { s._pos_offset_target_ned_m with
        z := r._pos_offset_target_ned_m.z }
      _pos_offset_ned_m := { s._pos_offset_ned_m with z := r._pos_offset_ned_m.z }
      _vel_offset_target_ned_ms := { s._vel_offset_target_ned_ms with
        z := r._vel_offset_target_ned_ms.z }
      _vel_offset_ned_ms := { s._vel_offset_ned_ms with z := r._vel_offset_ned_ms.z }
      _accel_offset_target_ned_mss := { s._accel_offset_target_ned_mss with
        z := r._accel_offset_target_ned_mss.z }
      _accel_offset_ned_mss := { s._accel_offset_ned_mss with z := r._accel_offset_ned_mss.z }
      _pos_target_ned_m := { s._pos_target_ned_m with z := r._pos_target_ned_m.z }
      _pos_desired_ned_m := { s._pos_desired_ned_m with z := r._pos_desired_ned_m.z }
      _vel_target_ned_ms := { s._vel_target_ned_ms with z := r._vel_target_ned_ms.z }
      _vel_desired_ned_ms := { s._vel_desired_ned_ms with z := r._vel_desired_ned_ms.z }
      _accel_target_ned_mss := { s._accel_target_ned_mss with z := r._accel_target_ned_mss.z }
      _accel_desired_ned_mss := { s._accel_desired_ned_mss with z := r._accel_desired_ned_mss.z }
      _pid_vel_d_m := r._pid_vel_d_m
      _pid_accel_d_m := r._pid_accel_d_m
      _last_update_d_ticks := r._last_update_d_ticks } := by
  intro r
  simp only [r, AC_PosControl.D_init_controller, AC_PosControl.D_init_offsets,
    AC_PosControl.init_terrain, Id.run, pure, hclk, if_false]

/-- `D_init_controller_stopping_point` is `D_init_controller` followed by the stopping point as
desired and target altitude, with zero desired vertical velocity and acceleration. -/
theorem t0_Dinit_stop_eq (p : AC_PosControl.Params) (s : AC_PosControl.State)
    (ahrs : AC_PosControl.AHRSInputs) (mi : AP_Motors.Inputs)
    (att : AC_PosControl.AttitudeControlInputs) (clock : AC_PosControl.Clock) :
    let r := AC_PosControl.D_init_controller p s ahrs mi att clock
    AC_PosControl.D_init_controller_stopping_point p s ahrs mi att clock = { r with
      _pos_desired_ned_m := { r._pos_desired_ned_m with
        z := AC_PosControl.get_stopping_point_D_m p r }
      _pos_target_ned_m := { r._pos_target_ned_m with
        z := AC_PosControl.get_stopping_point_D_m p r + r._pos_offset_ned_m.z }
      _vel_desired_ned_ms := { r._vel_desired_ned_ms with z := 0.0 }
      _accel_desired_ned_mss := { r._accel_desired_ned_mss with z := 0.0 } } := rfl

/-- The values `D_init_controller` writes, at the boot state: zero terrain terms and vertical
offsets (from zero offsets), both vertical PIDs in reset, a zero acceleration integrator (when the
stored throttle is the hover throttle and the acceleration estimate is within the acceleration
limit), and the current tick as update stamp. -/
theorem t0_Dinit_facts (s : AC_PosControl.State) (ahrs : AC_PosControl.AHRSInputs)
    (mi : AP_Motors.Inputs) (att : AC_PosControl.AttitudeControlInputs)
    (clock : AC_PosControl.Clock) (hoff : DOffZ s)
    (hclk : ¬ (clock.millis - s._posvelaccel_offset_target_d_ms >
      AC_PosControl.POSCONTROL_POSVELACCEL_OFFSET_TARGET_TIMEOUT_MS))
    (hthr : att.get_throttle_in = AP_Motors.get_throttle_hover mi)
    (hhov : mi._throttle_hover = CopterVertNear.hoverF)
    (hkim : s._pid_accel_d_m_kimax = AC_PosControl.POSCONTROL_D_ACC_IMAX)
    (hamax : s._accel_max_d_mss.IsFinite)
    (hest : (AC_PosControl.get_estimated_accel_D_mss ahrs).IsFinite)
    (hestb : |(AC_PosControl.get_estimated_accel_D_mss ahrs).toReal| ≤ s._accel_max_d_mss.toReal) :
    let r := AC_PosControl.D_init_controller runParams.psc s ahrs mi att clock
    TerrZ r ∧ DOffZ r ∧ r._pid_vel_d_m._reset_filter = true ∧
      r._pid_accel_d_m._flags._reset_filter = true ∧ CopterZero.Z r._pid_accel_d_m._integrator ∧
      r._last_update_d_ticks = clock.ticks32 := by
  intro r
  obtain ⟨hpt, hpo, hvt, hvo, hat, hao⟩ := hoff
  have hamaxn := (Float32.isFinite_neg _).2 hamax
  have hc : constrain_float (AC_PosControl.get_estimated_accel_D_mss ahrs) (-s._accel_max_d_mss)
      s._accel_max_d_mss = AC_PosControl.get_estimated_accel_D_mss ahrs :=
    constrain_float_of_near (Near32.exact hest) hamaxn hamax
      (by rw [Float32.toReal_neg]; have := abs_le.1 hestb; linarith)
      (by have := abs_le.1 hestb; linarith)
  have hff : CopterZero.Z runParams.psc.PSC_D_ACC_FF := Z_lit0
  have hkP : runParams.psc.PSC_D_ACC_P.IsFinite := by decide
  have hIM : (AC_PosControl.POSCONTROL_D_ACC_IMAX).IsFinite ∧
      0 ≤ (AC_PosControl.POSCONTROL_D_ACC_IMAX).toReal := by
    refine ⟨by decide, ?_⟩
    exact nonneg_of_le (by decide) (by decide)
  have hint : CopterZero.Z (constrain_float
      (-(att.get_throttle_in - AP_Motors.get_throttle_hover mi) -
        runParams.psc.PSC_D_ACC_P * (AC_PosControl.get_estimated_accel_D_mss ahrs -
          AC_PosControl.get_estimated_accel_D_mss ahrs) -
        runParams.psc.PSC_D_ACC_FF * AC_PosControl.get_estimated_accel_D_mss ahrs)
      (-AC_PosControl.POSCONTROL_D_ACC_IMAX) AC_PosControl.POSCONTROL_D_ACC_IMAX) := by
    have hh : (AP_Motors.get_throttle_hover mi).IsFinite := by
      rw [CopterVertNear.throttle_hover_eq mi hhov]; exact CopterVertNear.near_H.1
    have h1 : CopterZero.Z (att.get_throttle_in - AP_Motors.get_throttle_hover mi) := by
      rw [hthr]; exact sub_exact hh hh Z_zero.1 (by rw [sub_self, Z_zero.2])
    have h2 : CopterZero.Z (AC_PosControl.get_estimated_accel_D_mss ahrs -
        AC_PosControl.get_estimated_accel_D_mss ahrs) :=
      sub_exact hest hest Z_zero.1 (by rw [sub_self, Z_zero.2])
    refine constrain_Z (Z_sub (Z_sub (Z_neg h1) (Z_mul_right hkP h2)) (Z_mul_left hff hest))
      ((Float32.isFinite_neg _).2 hIM.1) hIM.1
      (by rw [Float32.toReal_neg]; linarith [hIM.2]) hIM.2
  refine ⟨?_, ?_, rfl, rfl, ?_, rfl⟩
  · simp only [r, AC_PosControl.D_init_controller, AC_PosControl.D_init_offsets,
      AC_PosControl.init_terrain, Id.run, pure, hclk, if_false]
    exact ⟨Z_lit0, Z_lit0, Z_lit0, Z_lit0⟩
  · simp only [r, AC_PosControl.D_init_controller, AC_PosControl.D_init_offsets,
      AC_PosControl.init_terrain, Id.run, pure, hclk, if_false]
    exact ⟨hpt, hpt, hvt, hvt, hat, hat⟩
  · simp only [r, AC_PosControl.D_init_controller, AC_PosControl.D_init_offsets,
      AC_PosControl.init_terrain, Id.run, pure, AC_PID.set_integrator,
      AC_PosControl.pid_accel_d_m_params, AC_PID.kP, AC_PID.ff, hclk, if_false, hc, hkim]
    exact hint

/-! ## `NE_init_controller_stopping_point` -/

/-- `NE_init_controller_stopping_point` on an active controller (no fresh acceleration target)
before the offset timeout: the frame of the written fields. -/
theorem t0_NEinit_frame (p : AC_PosControl.Params) (s : AC_PosControl.State)
    (ahrs : AC_PosControl.AHRSInputs) (att : AC_PosControl.AttitudeControlInputs)
    (clock : AC_PosControl.Clock)
    (hclk : ¬ (clock.millis - s._posvelaccel_offset_target_ne_ms >
      AC_PosControl.POSCONTROL_POSVELACCEL_OFFSET_TARGET_TIMEOUT_MS))
    (hact : clock.ticks32 - s._last_update_ne_ticks ≤ 1) :
    let r := AC_PosControl.NE_init_controller_stopping_point p s ahrs att clock
    r = { s with
      _pos_offset_ned_m := { s._pos_offset_ned_m with
        x := r._pos_offset_ned_m.x, y := r._pos_offset_ned_m.y }
      _vel_offset_ned_ms := { s._vel_offset_ned_ms with
        x := r._vel_offset_ned_ms.x, y := r._vel_offset_ned_ms.y }
      _accel_offset_ned_mss := { s._accel_offset_ned_mss with
        x := r._accel_offset_ned_mss.x, y := r._accel_offset_ned_mss.y }
      _roll_target_rad := r._roll_target_rad
      _pitch_target_rad := r._pitch_target_rad
      _yaw_target_rad := r._yaw_target_rad
      _yaw_rate_target_rads := r._yaw_rate_target_rads
      _angle_max_override_rad := r._angle_max_override_rad
      _pos_target_ned_m := { s._pos_target_ned_m with
        x := r._pos_target_ned_m.x, y := r._pos_target_ned_m.y }
      _pos_desired_ned_m := { s._pos_desired_ned_m with
        x := r._pos_desired_ned_m.x, y := r._pos_desired_ned_m.y }
      _vel_target_ned_ms := { s._vel_target_ned_ms with
        x := r._vel_target_ned_ms.x, y := r._vel_target_ned_ms.y }
      _vel_desired_ned_ms := { s._vel_desired_ned_ms with
        x := r._vel_desired_ned_ms.x, y := r._vel_desired_ned_ms.y }
      _accel_desired_ned_mss := { s._accel_desired_ned_mss with
        x := r._accel_desired_ned_mss.x, y := r._accel_desired_ned_mss.y }
      _accel_target_ned_mss := { s._accel_target_ned_mss with
        x := r._accel_target_ned_mss.x, y := r._accel_target_ned_mss.y }
      _pid_vel_ne_m := r._pid_vel_ne_m
      _last_update_ne_ticks := r._last_update_ne_ticks } := by
  intro r
  simp only [r, AC_PosControl.NE_init_controller_stopping_point, AC_PosControl.NE_init_controller,
    AC_PosControl.NE_init_offsets, AC_PosControl.NE_is_active, Id.run, pure, hclk, hact,
    if_false, decide_true, Bool.not_true, Bool.false_eq_true]
  rfl

/-- The values `NE_init_controller_stopping_point` writes at the boot state: zero horizontal
offsets, velocity PID memory, desired velocity and acceleration, a zero horizontal position target
and desired position (the stopping point at rest), and the current tick as update stamp. -/
theorem t0_NEinit_facts (s : AC_PosControl.State) (ahrs : AC_PosControl.AHRSInputs)
    (att : AC_PosControl.AttitudeControlInputs) (clock : AC_PosControl.Clock)
    (hclk : ¬ (clock.millis - s._posvelaccel_offset_target_ne_ms >
      AC_PosControl.POSCONTROL_POSVELACCEL_OFFSET_TARGET_TIMEOUT_MS))
    (hact : clock.ticks32 - s._last_update_ne_ticks ≤ 1) (hoff : OffZ s)
    (hpex : ZD s._pos_estimate_ned_m.x) (hpey : ZD s._pos_estimate_ned_m.y)
    (hvex : CopterZero.Z s._vel_estimate_ned_ms.x) (hvey : CopterZero.Z s._vel_estimate_ned_ms.y)
    (hat : ZV2 s._accel_target_ned_mss.xy) (hpid : ZPID2 s._pid_vel_ne_m) :
    let r := AC_PosControl.NE_init_controller_stopping_point runParams.psc s ahrs att clock
    OffZ r ∧ ZPID2 r._pid_vel_ne_m ∧ r._last_update_ne_ticks = clock.ticks32 ∧
      ZD r._pos_desired_ned_m.x ∧ ZD r._pos_desired_ned_m.y ∧
      ZD r._pos_target_ned_m.x ∧ ZD r._pos_target_ned_m.y ∧
      ZV2 r._vel_desired_ned_ms.xy ∧ ZV2 r._accel_desired_ned_mss.xy := by
  intro r
  obtain ⟨o1, o2, o3, o4, o5, o6⟩ := hoff
  -- the state before the stopping point
  set q := AC_PosControl.NE_init_controller runParams.psc s ahrs att clock with hq
  have hqe : q = { s with
      _pos_offset_ned_m := s._pos_offset_ned_m.set_xy s._pos_offset_target_ned_m.xy
      _vel_offset_ned_ms := s._vel_offset_ned_ms.set_xy s._vel_offset_target_ned_ms.xy
      _accel_offset_ned_mss := s._accel_offset_ned_mss.set_xy s._accel_offset_target_ned_mss.xy
      _roll_target_rad := att.get_att_target_euler_rad.x
      _pitch_target_rad := att.get_att_target_euler_rad.y
      _yaw_target_rad := att.get_att_target_euler_rad.z
      _yaw_rate_target_rads := 0.0
      _angle_max_override_rad := 0.0
      _pos_target_ned_m := s._pos_target_ned_m.set_xy s._pos_estimate_ned_m.xy
      _pos_desired_ned_m := s._pos_desired_ned_m.set_xy
        (s._pos_estimate_ned_m.xy - s._pos_offset_target_ned_m.xy)
      _vel_target_ned_ms := s._vel_target_ned_ms.set_xy s._vel_estimate_ned_ms.xy
      _vel_desired_ned_ms := s._vel_desired_ned_ms.set_xy
        (s._vel_estimate_ned_ms.xy - s._vel_offset_target_ned_ms.xy)
      _accel_desired_ned_mss := s._accel_desired_ned_mss.set_xy s._accel_desired_ned_mss.xy.zero
      _accel_target_ned_mss := s._accel_target_ned_mss.set_xy
        (s._accel_target_ned_mss.xy.limit_length (MIN att.get_althold_lean_angle_max_rad
          (AC_PosControl.get_lean_angle_max_rad runParams.psc { s with
            _angle_max_override_rad := 0.0 } att) |> angle_rad_to_accel_mss)).1
      _pid_vel_ne_m := AC_PID_2D.set_integrator runParams.psc._pid_vel_ne_m
        (AC_PID_2D.reset_filter s._pid_vel_ne_m)
        ((s._accel_target_ned_mss.xy.limit_length (MIN att.get_althold_lean_angle_max_rad
          (AC_PosControl.get_lean_angle_max_rad runParams.psc { s with
            _angle_max_override_rad := 0.0 } att) |> angle_rad_to_accel_mss)).1 -
          s._vel_estimate_ned_ms.xy * AC_PID_2D.ff runParams.psc._pid_vel_ne_m)
      _last_update_ne_ticks := clock.ticks32 } := by
    simp only [hq, AC_PosControl.NE_init_controller, AC_PosControl.NE_init_offsets,
      AC_PosControl.NE_is_active, Id.run, pure, hclk, hact, if_false, decide_true, Bool.not_true,
      Bool.false_eq_true]
    rfl
  have hr : r = { q with
      _pos_desired_ned_m := q._pos_desired_ned_m.set_xy
        (AC_PosControl.get_stopping_point_NE_m runParams.psc q)
      _pos_target_ned_m := q._pos_target_ned_m.set_xy
        ((q._pos_desired_ned_m.set_xy (AC_PosControl.get_stopping_point_NE_m runParams.psc q)).xy +
          q._pos_offset_ned_m.xy)
      _vel_desired_ned_ms := q._vel_desired_ned_ms.set_xy q._vel_desired_ned_ms.xy.zero
      _accel_desired_ned_mss := q._accel_desired_ned_mss.set_xy
        q._accel_desired_ned_mss.xy.zero } := rfl
  have qoff : OffZ q := by rw [hqe]; exact ⟨o1, o1, o3, o3, o5, o5⟩
  obtain ⟨sx, sy⟩ := stopping_point_NE_zero (psc := q) (by rw [hqe]; exact hpex)
    (by rw [hqe]; exact hpey) (by rw [hqe]; exact hvex) (by rw [hqe]; exact hvey) qoff
  have hlim : (s._accel_target_ned_mss.xy.limit_length (MIN att.get_althold_lean_angle_max_rad
      (AC_PosControl.get_lean_angle_max_rad runParams.psc { s with
        _angle_max_override_rad := 0.0 } att) |> angle_rad_to_accel_mss)).1 =
      s._accel_target_ned_mss.xy := ZV2_limit_length hat _
  have hff : (AC_PID_2D.ff runParams.psc._pid_vel_ne_m).IsFinite := by decide
  have hint : ZV2 (s._accel_target_ned_mss.xy - s._vel_estimate_ned_ms.xy *
      AC_PID_2D.ff runParams.psc._pid_vel_ne_m) := ZV2_sub hat (ZV2_mul_v ⟨hvex, hvey⟩ hff)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hr]; exact qoff
  · rw [hr, hqe]
    obtain ⟨p1, p2, p3, p4⟩ := hpid
    refine ⟨p1, p2, p3, ?_⟩
    simp only [AC_PID_2D.set_integrator]
    rw [hlim, ZV2_limit_length hint]
    exact hint
  · rw [hr, hqe]
  · rw [hr]; exact sx
  · rw [hr]; exact sy
  · rw [hr]; exact ZD_add sx qoff.2.1.1
  · rw [hr]; exact ZD_add sy qoff.2.1.2
  · rw [hr]; exact ZV2_zero q._vel_desired_ned_ms.xy
  · rw [hr]; exact ZV2_zero q._accel_desired_ned_mss.xy

/-! ## The speed and acceleration limits -/

/-- The attitude inputs that `NE_set_max_speed_accel_m` reads, with the others zeroed. -/
def t0attC (att : AC_PosControl.AttitudeControlInputs) : AC_PosControl.AttitudeControlInputs :=
  { get_att_target_euler_rad := ⟨0, 0, 0⟩, get_althold_lean_angle_max_rad := 0,
    lean_angle_max_rad := 0, get_throttle_in := 0,
    get_ang_vel_roll_max_rads := att.get_ang_vel_roll_max_rads,
    get_ang_vel_pitch_max_rads := att.get_ang_vel_pitch_max_rads,
    get_accel_roll_max_radss := att.get_accel_roll_max_radss,
    get_accel_pitch_max_radss := att.get_accel_pitch_max_radss,
    get_bf_feedforward := att.get_bf_feedforward }

/-- The boot position controller of the run, a closed term for the kernel computations. -/
abbrev t0P0 : AC_PosControl.State := AC_PosControl.init runParams.psc

/-- `NE_set_max_speed_accel_m` writes the horizontal speed, acceleration and jerk limits; the
jerk limit depends only on the arguments and the attitude limits. -/
theorem t0_NEmax_frame (p : AC_PosControl.Params) (s : AC_PosControl.State)
    (att : AC_PosControl.AttitudeControlInputs) (v a : Float32) :
    AC_PosControl.NE_set_max_speed_accel_m p s att v a = { s with
      _vel_max_ne_ms := v.abs, _accel_max_ne_mss := a.abs,
      _jerk_max_ne_msss :=
        (AC_PosControl.NE_set_max_speed_accel_m p t0P0 (t0attC att) v a)._jerk_max_ne_msss } := by
  unfold AC_PosControl.NE_set_max_speed_accel_m t0attC
  simp only [Id.run]
  split_ifs <;> rfl

/-- The acceleration PID of the run filters the error (`PSC_D_ACC_FLTE = 20`) but not the target
(`PSC_D_ACC_FLTT = 0`). -/
theorem t0_filt_TE : is_positive runParams.psc.PSC_D_ACC_FLTT = false ∧
    is_positive runParams.psc.PSC_D_ACC_FLTE = true := by
  decide

/-- `D_set_max_speed_accel_m` with three nonzero limits writes them (as magnitudes) and a jerk
limit that depends only on the arguments. -/
theorem t0_Dmax_frame (s : AC_PosControl.State) (d u a : Float32)
    (hd : is_zero d = false) (hu : is_zero u = false) (ha : is_zero a = false) :
    AC_PosControl.D_set_max_speed_accel_m runParams.psc s d u a = { s with
      _vel_max_down_ms := d.abs, _vel_max_up_ms := u.abs, _accel_max_d_mss := a.abs,
      _jerk_max_d_msss :=
        (AC_PosControl.D_set_max_speed_accel_m runParams.psc t0P0 d u a)._jerk_max_d_msss } := by
  unfold AC_PosControl.D_set_max_speed_accel_m
  simp only [Id.run, pure, hd, hu, ha, Bool.not_false, if_true, AC_PosControl.pid_accel_d_m_params,
    AC_PID.filt_T_hz, AC_PID.filt_E_hz, t0_filt_TE.1, t0_filt_TE.2, Bool.false_eq_true, if_false]

/-- `AC_P_1D.set_limits` writes the three limits, which do not depend on the state. -/
theorem t0_set_limits_frame (p : AC_P_1D.Params) (X : AC_P_1D.State) (a b c d : Float32) :
    AC_P_1D.set_limits p X a b c d =
      { AC_P_1D.set_limits p ⟨0, 0, 0, 0⟩ a b c d with _error := X._error } := by
  unfold AC_P_1D.set_limits
  simp only [Id.run]
  split_ifs <;> rfl

/-- The horizontal speed `wp_and_spline_init_m` passes to the position controller at boot. -/
abbrev t0v0 : Float32 :=
  MAX (if is_positive (0.0 : Float32) then 0.0 else MAX runParams.wpnav.WP_SPD WP_SPD_MIN)
    WP_SPD_MIN

/-- The limits of the run, evaluated by the kernel: the vertical position error limits
`-1.625`, `3.625`, `D1_max = 1`, the horizontal speed `10`, acceleration `2.5`, jerk `5`, the
vertical speeds `2.5` up and `1.5` down, acceleration `1`, jerk `5`. -/
theorem t0_limit_vals :
    (AC_P_1D.set_limits runParams.psc._p_pos_d_m ⟨0, 0, 0, 0⟩
      (-(get_default_speed_down_ms runParams.wpnav).abs)
      (get_default_speed_up_ms runParams.wpnav).abs
      (get_accel_D_mss runParams.wpnav).abs 0.0)._error_min = -1.625 ∧
    (AC_P_1D.set_limits runParams.psc._p_pos_d_m ⟨0, 0, 0, 0⟩
      (-(get_default_speed_down_ms runParams.wpnav).abs)
      (get_default_speed_up_ms runParams.wpnav).abs
      (get_accel_D_mss runParams.wpnav).abs 0.0)._error_max = 3.625 ∧
    (AC_P_1D.set_limits runParams.psc._p_pos_d_m ⟨0, 0, 0, 0⟩
      (-(get_default_speed_down_ms runParams.wpnav).abs)
      (get_default_speed_up_ms runParams.wpnav).abs
      (get_accel_D_mss runParams.wpnav).abs 0.0)._D1_max = 1.0 ∧
    t0v0.abs = 10.0 ∧ (get_wp_acceleration_mss runParams.wpnav).abs = 2.5 ∧
    (AC_PosControl.NE_set_max_speed_accel_m runParams.psc t0P0
      (t0attC (Copter.attInputs runParams {})) t0v0
      (get_wp_acceleration_mss runParams.wpnav))._jerk_max_ne_msss = 5.0 ∧
    (get_default_speed_down_ms runParams.wpnav).abs = 1.5 ∧
    (get_default_speed_up_ms runParams.wpnav).abs = 2.5 ∧
    (get_accel_D_mss runParams.wpnav).abs = 1.0 ∧
    (AC_PosControl.D_set_max_speed_accel_m runParams.psc t0P0
      (get_default_speed_down_ms runParams.wpnav) (get_default_speed_up_ms runParams.wpnav)
      (get_accel_D_mss runParams.wpnav))._jerk_max_d_msss = 5.0 ∧
    is_zero (get_default_speed_down_ms runParams.wpnav) = false ∧
    is_zero (get_default_speed_up_ms runParams.wpnav) = false ∧
    is_zero (get_accel_D_mss runParams.wpnav) = false := by
  decide +kernel

/-! ## The position controller after `wp_and_spline_init_m` -/

/-- `wp_and_spline_init_m` on the boot navigator, for the position controller: the two
initializations followed by the four limit setters. -/
theorem t0_init_psc (Q : AC_PosControl.State) (env : AC_WPNav.Env) :
    (wp_and_spline_init_m runParams.wpnav runParams.psc (AC_WPNav.init runParams.wpnav) Q env).2 =
      AC_PosControl.D_set_correction_speed_accel_m runParams.psc
        (AC_PosControl.D_set_max_speed_accel_m runParams.psc
          (AC_PosControl.NE_set_correction_speed_accel_m runParams.psc
            (AC_PosControl.NE_set_max_speed_accel_m runParams.psc
              (AC_PosControl.NE_init_controller_stopping_point runParams.psc
                (AC_PosControl.D_init_controller_stopping_point runParams.psc Q env.ahrs env.motors
                  env.att env.clock) env.ahrs env.att env.clock)
              env.att t0v0 (get_wp_acceleration_mss runParams.wpnav))
            t0v0 (get_wp_acceleration_mss runParams.wpnav))
          (get_default_speed_down_ms runParams.wpnav) (get_default_speed_up_ms runParams.wpnav)
          (get_accel_D_mss runParams.wpnav))
        (get_default_speed_down_ms runParams.wpnav) (get_default_speed_up_ms runParams.wpnav)
        (get_accel_D_mss runParams.wpnav) := rfl

/-- The position controller left by the prefix of tick 0: the boot controller with the loop
time `dtF` and the estimates of the sample. -/
abbrev t0Q0 (zP : Float) : AC_PosControl.State :=
  { AC_PosControl.init runParams.psc with
    _dt_s := dtF, _pos_estimate_ned_m := ⟨0, 0, zP⟩, _vel_estimate_ned_ms := ⟨0, 0, 0⟩ }

/-- **The position controller after the switch into Auto** (`PscT0`): the loop time, the limits
of `PscLim` with the vertical acceleration limit `1` and a horizontal speed limit in `[0, 10³⁰]`,
a zero desired velocity, zero offsets, terrain terms, horizontal velocity PID memory, a finite
limit vector and scale factor, the position target within `10⁻⁶` of `-1`, the estimates of the
sample, both update stamps at the first tick, both vertical PIDs in reset with a zero
acceleration integrator, and the stopping point of the navigator within `10⁻⁶` of the
waypoint. -/
structure PscT0 (q : AC_PosControl.State) (zP : Float) : Prop where
  dt : q._dt_s = dtF
  psclim : PscLim q
  amax1 : q._accel_max_d_mss.toReal = 1
  vmax0 : 0 ≤ q._vel_max_ne_ms.toReal
  vmaxb : q._vel_max_ne_ms.toReal ≤ 1e30
  vel_desired : ZV q._vel_desired_ned_ms
  doff : DOffZ q
  terr : TerrZ q
  off : OffZ q
  pid_ne : ZPID2 q._pid_vel_ne_m
  lim : FinV2 q._limit_vector_ned.xy
  nescale : q._ne_control_scale_factor.IsFinite
  pos_target : Near64 q._pos_target_ned_m.z (-1) 1e-6
  pex : ZD q._pos_estimate_ned_m.x
  pey : ZD q._pos_estimate_ned_m.y
  pez : q._pos_estimate_ned_m.z = zP
  vex : CopterZero.Z q._vel_estimate_ned_ms.x
  vey : CopterZero.Z q._vel_estimate_ned_ms.y
  vez : CopterZero.Z q._vel_estimate_ned_ms.z
  d_ticks : q._last_update_d_ticks = 1
  ne_ticks : q._last_update_ne_ticks = 1
  v_reset : q._pid_vel_d_m._reset_filter = true
  a_reset : q._pid_accel_d_m._flags._reset_filter = true
  a_int : CopterZero.Z q._pid_accel_d_m._integrator
  sp_x : ZD (get_wp_stopping_point_NED_m runParams.psc q).x
  sp_y : ZD (get_wp_stopping_point_NED_m runParams.psc q).y
  sp_z : Near64 (get_wp_stopping_point_NED_m runParams.psc q).z (-1) 1e-6

/-- `PscT0` from its fields: the stopping point of the navigator follows from the estimates,
the offsets and the acceleration limit (`stopping_point_NE_zero`, `t0_stop_D`). -/
theorem PscT0.mk' (N : NarrowSpec 2) (W : WidenSpec) {q : AC_PosControl.State} {zP : Float}
    (hz : Near64 zP (-1) 1e-15)
    (dt : q._dt_s = dtF) (psclim : PscLim q) (amax1 : q._accel_max_d_mss.toReal = 1)
    (vmax0 : 0 ≤ q._vel_max_ne_ms.toReal) (vmaxb : q._vel_max_ne_ms.toReal ≤ 1e30)
    (vel_desired : ZV q._vel_desired_ned_ms) (doff : DOffZ q) (terr : TerrZ q) (off : OffZ q)
    (pid_ne : ZPID2 q._pid_vel_ne_m) (lim : FinV2 q._limit_vector_ned.xy)
    (nescale : q._ne_control_scale_factor.IsFinite)
    (pos_target : Near64 q._pos_target_ned_m.z (-1) 1e-6)
    (pe : q._pos_estimate_ned_m = ⟨0, 0, zP⟩) (ve : q._vel_estimate_ned_ms = ⟨0, 0, 0⟩)
    (d_ticks : q._last_update_d_ticks = 1) (ne_ticks : q._last_update_ne_ticks = 1)
    (v_reset : q._pid_vel_d_m._reset_filter = true)
    (a_reset : q._pid_accel_d_m._flags._reset_filter = true)
    (a_int : CopterZero.Z q._pid_accel_d_m._integrator) : PscT0 q zP := by
  have pex : ZD q._pos_estimate_ned_m.x := by rw [pe]; exact ZD_zero
  have pey : ZD q._pos_estimate_ned_m.y := by rw [pe]; exact ZD_zero
  have vex : CopterZero.Z q._vel_estimate_ned_ms.x := by rw [ve]; exact Z_zero
  have vey : CopterZero.Z q._vel_estimate_ned_ms.y := by rw [ve]; exact Z_zero
  have vez : CopterZero.Z q._vel_estimate_ned_ms.z := by rw [ve]; exact Z_zero
  obtain ⟨sx, sy⟩ := stopping_point_NE_zero pex pey vex vey off
  have sz := t0_stop_D N W (psc := q) (by rw [pe]; exact hz) vez doff.2.1 doff.2.2.2.1
    psclim.amax (by rw [amax1]; norm_num)
  exact ⟨dt, psclim, amax1, vmax0, vmaxb, vel_desired, doff, terr, off, pid_ne, lim, nescale,
    pos_target, pex, pey, by rw [pe], vex, vey, vez, d_ticks, ne_ticks, v_reset, a_reset, a_int,
    sx, sy, sz⟩

set_option maxHeartbeats 1000000 in
/-- **`wp_and_spline_init_m` on the position controller of tick 0** gives `PscT0`, for an
environment at the first tick (`ticks32 = 1`, `millis() = 2`), whose attitude controller stores
the hover throttle, whose motors have `MOT_THST_HOVER = 0.4444`, whose acceleration estimate is
within the boot limit `2.5`, and whose attitude limits are those of the run parameters. -/
theorem t0_psc7 (N : NarrowSpec 2) (W : WidenSpec) {zP : Float} (hz : Near64 zP (-1) 1e-15)
    (env : AC_WPNav.Env) (hclk : env.clock = ⟨1, 2⟩)
    (hthr : env.att.get_throttle_in = AP_Motors.get_throttle_hover env.motors)
    (hhov : env.motors._throttle_hover = CopterVertNear.hoverF)
    (hest : (AC_PosControl.get_estimated_accel_D_mss env.ahrs).IsFinite)
    (hestb : |(AC_PosControl.get_estimated_accel_D_mss env.ahrs).toReal| ≤ 1)
    (hatt : t0attC env.att = t0attC (Copter.attInputs runParams {})) :
    PscT0 (wp_and_spline_init_m runParams.wpnav runParams.psc (AC_WPNav.init runParams.wpnav)
      (t0Q0 zP) env).2 zP := by
  obtain ⟨l1, l2, l3, l4, l5, l6, l7, l8, l9, l10, l11, l12, l13⟩ := t0_limit_vals
  rw [t0_init_psc]
  -- `D_init_controller`
  have hclkD : ¬ (env.clock.millis - (t0Q0 zP)._posvelaccel_offset_target_d_ms >
      AC_PosControl.POSCONTROL_POSVELACCEL_OFFSET_TARGET_TIMEOUT_MS) := by
    rw [hclk]
    show ¬ ((2 : UInt32) - 0 > AC_PosControl.POSCONTROL_POSVELACCEL_OFFSET_TARGET_TIMEOUT_MS)
    decide
  have h25 : (t0Q0 zP)._accel_max_d_mss.IsFinite ∧ (t0Q0 zP)._accel_max_d_mss.toReal = 5 / 2 := by
    obtain ⟨h1, h2⟩ := CopterVertNear.lit32 (x := AC_PosControl.POSCONTROL_ACCEL_D_MSS) 10485760
      (-22) (by decide) rfl
    have e : (t0Q0 zP)._accel_max_d_mss = AC_PosControl.POSCONTROL_ACCEL_D_MSS := rfl
    rw [e, h2]
    exact ⟨h1, by norm_num⟩
  have hoff0 : DOffZ (t0Q0 zP) := ⟨ZD_zero, ZD_zero, Z_zero, Z_zero, Z_zero, Z_zero⟩
  obtain ⟨d1, d2, d3, d4, d5, d6⟩ := t0_Dinit_facts (t0Q0 zP) env.ahrs env.motors env.att env.clock
    hoff0 hclkD hthr hhov rfl h25.1 hest (by rw [h25.2]; linarith)
  have eD := t0_Dinit_frame runParams.psc (t0Q0 zP) env.ahrs env.motors env.att env.clock hclkD
  set Q1 := AC_PosControl.D_init_controller runParams.psc (t0Q0 zP) env.ahrs env.motors env.att
    env.clock with hQ1
  have hSP1 := t0_stop_D N W (psc := Q1) (by rw [eD]; exact hz) (by rw [eD]; exact Z_zero) d2.2.1
    d2.2.2.2.1 (by rw [eD]; exact h25.1) (by rw [eD, h25.2]; norm_num)
  rw [t0_Dinit_stop_eq]
  set Q1s : AC_PosControl.State := { Q1 with
      _pos_desired_ned_m := { Q1._pos_desired_ned_m with
        z := AC_PosControl.get_stopping_point_D_m runParams.psc Q1 }
      _pos_target_ned_m := { Q1._pos_target_ned_m with
        z := AC_PosControl.get_stopping_point_D_m runParams.psc Q1 + Q1._pos_offset_ned_m.z }
      _vel_desired_ned_ms := { Q1._vel_desired_ned_ms with z := 0.0 }
      _accel_desired_ned_mss := { Q1._accel_desired_ned_mss with z := 0.0 } } with hQ1s
  -- `NE_init_controller`
  have hclkN : ¬ (env.clock.millis - Q1s._posvelaccel_offset_target_ne_ms >
      AC_PosControl.POSCONTROL_POSVELACCEL_OFFSET_TARGET_TIMEOUT_MS) := by
    rw [hclk, hQ1s, eD]
    show ¬ ((2 : UInt32) - 0 > AC_PosControl.POSCONTROL_POSVELACCEL_OFFSET_TARGET_TIMEOUT_MS)
    decide
  have hactN : env.clock.ticks32 - Q1s._last_update_ne_ticks ≤ 1 := by
    rw [hclk, hQ1s, eD]
    show (1 : UInt32) - 0 ≤ 1
    decide
  have hoff1 : OffZ Q1s := by
    rw [hQ1s, eD]
    exact ⟨⟨ZD_zero, ZD_zero⟩, ⟨ZD_zero, ZD_zero⟩, ⟨Z_zero, Z_zero⟩, ⟨Z_zero, Z_zero⟩,
      ⟨Z_zero, Z_zero⟩, ⟨Z_zero, Z_zero⟩⟩
  have hpid1 : ZPID2 Q1s._pid_vel_ne_m := by
    rw [hQ1s, eD]; exact ⟨⟨Z_lit0, Z_lit0⟩, ⟨Z_lit0, Z_lit0⟩, ⟨Z_lit0, Z_lit0⟩, ⟨Z_lit0, Z_lit0⟩⟩
  obtain ⟨n1, n2, n3, n4, n5, n6, n7, n8, n9⟩ := t0_NEinit_facts Q1s env.ahrs env.att env.clock
    hclkN hactN hoff1 (by rw [hQ1s, eD]; exact ZD_zero) (by rw [hQ1s, eD]; exact ZD_zero)
    (by rw [hQ1s, eD]; exact Z_zero) (by rw [hQ1s, eD]; exact Z_zero)
    (by rw [hQ1s, eD]; exact ⟨Z_zero, Z_zero⟩) hpid1
  have eN := t0_NEinit_frame runParams.psc Q1s env.ahrs env.att env.clock hclkN hactN
  set Q2 := AC_PosControl.NE_init_controller_stopping_point runParams.psc Q1s env.ahrs env.att
    env.clock with hQ2
  -- the limits
  rw [t0_NEmax_frame, hatt]
  set Q3 : AC_PosControl.State := { Q2 with
      _vel_max_ne_ms := t0v0.abs,
      _accel_max_ne_mss := (get_wp_acceleration_mss runParams.wpnav).abs,
      _jerk_max_ne_msss := (AC_PosControl.NE_set_max_speed_accel_m runParams.psc t0P0
        (t0attC (Copter.attInputs runParams {})) t0v0
        (get_wp_acceleration_mss runParams.wpnav))._jerk_max_ne_msss } with hQ3
  rw [t0_Dmax_frame _ _ _ _ l11 l12 l13]
  unfold AC_PosControl.D_set_correction_speed_accel_m AC_PosControl.NE_set_correction_speed_accel_m
  rw [t0_set_limits_frame]
  -- the fields
  have hLe : ∀ x : Float32, x = -1.625 → x.IsFinite ∧ x.toReal = -(13 / 8) := by
    rintro x rfl
    obtain ⟨h1, h2⟩ := CopterVertNear.lit32 (x := (1.625 : Float32)) 13631488 (-23) (by decide) rfl
    exact ⟨(Float32.isFinite_neg _).2 h1, by rw [Float32.toReal_neg, h2]; norm_num⟩
  have hLx : ∀ x : Float32, x = 3.625 → x.IsFinite ∧ x.toReal = 29 / 8 := by
    rintro x rfl
    obtain ⟨h1, h2⟩ := CopterVertNear.lit32 (x := (3.625 : Float32)) 15204352 (-22) (by decide) rfl
    exact ⟨h1, by rw [h2]; norm_num⟩
  have hL25 : ∀ x : Float32, x = 2.5 → x.IsFinite ∧ x.toReal = 5 / 2 := by
    rintro x rfl
    obtain ⟨h1, h2⟩ := CopterVertNear.lit32 (x := (2.5 : Float32)) 10485760 (-22) (by decide) rfl
    exact ⟨h1, by rw [h2]; norm_num⟩
  have hL15 : ∀ x : Float32, x = 1.5 → x.IsFinite ∧ x.toReal = 3 / 2 := by
    rintro x rfl
    obtain ⟨h1, h2⟩ := CopterVertNear.lit32 (x := (1.5 : Float32)) 12582912 (-23) (by decide) rfl
    exact ⟨h1, by rw [h2]; norm_num⟩
  have hL5 : ∀ x : Float32, x = 5.0 → x.IsFinite ∧ x.toReal = 5 := by
    rintro x rfl; exact lit_five
  have hL10 : ∀ x : Float32, x = 10.0 → x.IsFinite ∧ x.toReal = 10 := by
    rintro x rfl; exact lit_ten
  have hL1 : ∀ x : Float32, x = 1.0 → x.IsFinite ∧ x.toReal = 1 := by
    rintro x rfl; exact lit_one
  obtain ⟨e1, e2⟩ := hLe _ l1
  obtain ⟨x1, x2⟩ := hLx _ l2
  obtain ⟨D1, D2⟩ := hL1 _ l3
  obtain ⟨v1, v2⟩ := hL10 _ l4
  obtain ⟨a1, a2⟩ := hL25 _ l5
  obtain ⟨j1, j2⟩ := hL5 _ l6
  obtain ⟨dn1, dn2⟩ := hL15 _ l7
  obtain ⟨up1, up2⟩ := hL25 _ l8
  obtain ⟨am1, am2⟩ := hL1 _ l9
  obtain ⟨jd1, jd2⟩ := hL5 _ l10
  -- the fields of `Q2` that the limits keep
  have q_off : OffZ Q2 := n1
  have q_doff : DOffZ Q2 := by rw [eN, hQ1s]; exact d2
  have q_terr : TerrZ Q2 := by rw [eN, hQ1s]; exact d1
  have q_pe : Q2._pos_estimate_ned_m = ⟨0, 0, zP⟩ := by rw [eN, hQ1s, eD]
  have q_ve : Q2._vel_estimate_ned_ms = ⟨0, 0, 0⟩ := by rw [eN, hQ1s, eD]
  have q_vd : ZV Q2._vel_desired_ned_ms := by
    refine ⟨n8.1, n8.2, ?_⟩
    rw [eN, hQ1s]; exact Z_lit0
  have q_pt : Near64 Q2._pos_target_ned_m.z (-1) 1e-6 := by
    rw [eN, hQ1s]
    obtain ⟨f1, f2⟩ := add_ZD_right hSP1.1 d2.2.1
    exact ⟨f1, by rw [f2]; exact hSP1.2⟩
  have q_vo : CopterZero.Z Q2._vel_offset_ned_ms.z := by rw [eN, hQ1s]; exact d2.2.2.2.1
  have q_po : ZD Q2._pos_offset_ned_m.z := by rw [eN, hQ1s]; exact d2.2.1
  have q_lim : FinV2 Q2._limit_vector_ned.xy := by
    rw [eN, hQ1s, eD]; exact ⟨Float32.isFinite_zero, Float32.isFinite_zero⟩
  have q_sc : Q2._ne_control_scale_factor.IsFinite := by rw [eN, hQ1s, eD]; exact lit_one.1
  have q_dt : Q2._dt_s = dtF := by rw [eN, hQ1s, eD]
  have q_dtk : Q2._last_update_d_ticks = 1 := by rw [eN, hQ1s, d6, hclk]
  have q_vr : Q2._pid_vel_d_m._reset_filter = true := by rw [eN, hQ1s]; exact d3
  have q_ar : Q2._pid_accel_d_m._flags._reset_filter = true := by rw [eN, hQ1s]; exact d4
  have q_ai : CopterZero.Z Q2._pid_accel_d_m._integrator := by rw [eN, hQ1s]; exact d5
  have q_km : Q2._pid_accel_d_m_kimax = AC_PosControl.POSCONTROL_D_ACC_IMAX := by
    rw [eN, hQ1s, eD]; rfl
  have q_ntk : Q2._last_update_ne_ticks = 1 := by rw [n3, hclk]
  have hab : ∀ {x : Float32} {c B : ℝ}, x.toReal = c → |c| ≤ B → |x.toReal| ≤ B :=
    fun h hc => h ▸ hc
  have b1 := hab j2 (by norm_num : |(5 : ℝ)| ≤ 1e18)
  have b2 := hab am2 (by norm_num : |(1 : ℝ)| ≤ 1e18)
  have b3 := hab jd2 (by norm_num : |(5 : ℝ)| ≤ 1e11)
  have b4 := e2.trans_le (by norm_num : -(13 / 8 : ℝ) ≤ -(1 / 100))
  have b5 := (by norm_num : (1 / 100 : ℝ) ≤ 29 / 8).trans_eq x2.symm
  have b6 := (by norm_num : (1 / 100 : ℝ) ≤ 1).trans_eq D2.symm
  have b7 := (by norm_num : (0 : ℝ) ≤ 10).trans_eq v2.symm
  have b8 := v2.trans_le (by norm_num : (10 : ℝ) ≤ 1e30)
  have q3j1 : Q3._jerk_max_ne_msss.IsFinite := by rw [hQ3]; dsimp only; exact j1
  have q3b1 : |Q3._jerk_max_ne_msss.toReal| ≤ 1e18 := by rw [hQ3]; dsimp only; exact b1
  have q3v1 : Q3._vel_max_ne_ms.IsFinite := by rw [hQ3]; dsimp only; exact v1
  have q3b7 : 0 ≤ Q3._vel_max_ne_ms.toReal := by rw [hQ3]; dsimp only; exact b7
  have q3b8 : Q3._vel_max_ne_ms.toReal ≤ 1e30 := by rw [hQ3]; dsimp only; exact b8
  have q3a1 : Q3._accel_max_ne_mss.IsFinite := by rw [hQ3]; dsimp only; exact a1
  have q3_dt : Q3._dt_s = dtF := by rw [hQ3]; dsimp only; exact q_dt
  have q3_km : Q3._pid_accel_d_m_kimax = AC_PosControl.POSCONTROL_D_ACC_IMAX := by
    rw [hQ3]; dsimp only; exact q_km
  have q3_vd : ZV Q3._vel_desired_ned_ms := by rw [hQ3]; dsimp only; exact q_vd
  have q3_doff : DOffZ Q3 := by rw [hQ3]; unfold DOffZ; dsimp only; exact q_doff
  have q3_terr : TerrZ Q3 := by rw [hQ3]; unfold TerrZ; dsimp only; exact q_terr
  have q3_off : OffZ Q3 := by rw [hQ3]; unfold OffZ; dsimp only; exact q_off
  have q3_pid : ZPID2 Q3._pid_vel_ne_m := by rw [hQ3]; dsimp only; exact n2
  have q3_lim : FinV2 Q3._limit_vector_ned.xy := by rw [hQ3]; dsimp only; exact q_lim
  have q3_sc : Q3._ne_control_scale_factor.IsFinite := by rw [hQ3]; dsimp only; exact q_sc
  have q3_pt : Near64 Q3._pos_target_ned_m.z (-1) 1e-6 := by rw [hQ3]; dsimp only; exact q_pt
  have q3_pe : Q3._pos_estimate_ned_m = ⟨0, 0, zP⟩ := by rw [hQ3]; dsimp only; exact q_pe
  have q3_ve : Q3._vel_estimate_ned_ms = ⟨0, 0, 0⟩ := by rw [hQ3]; dsimp only; exact q_ve
  have q3_dtk : Q3._last_update_d_ticks = 1 := by rw [hQ3]; dsimp only; exact q_dtk
  have q3_ntk : Q3._last_update_ne_ticks = 1 := by rw [hQ3]; dsimp only; exact q_ntk
  have q3_vr : Q3._pid_vel_d_m._reset_filter = true := by rw [hQ3]; dsimp only; exact q_vr
  have q3_ar : Q3._pid_accel_d_m._flags._reset_filter = true := by rw [hQ3]; dsimp only; exact q_ar
  have q3_ai : CopterZero.Z Q3._pid_accel_d_m._integrator := by rw [hQ3]; dsimp only; exact q_ai
  clear_value Q3
  -- the result
  refine PscT0.mk' N W hz ?_ ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_⟩ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  all_goals dsimp only [DOffZ, TerrZ, OffZ]
  · exact q3_dt
  · exact e1
  · exact b4
  · exact x1
  · exact b5
  · exact D1
  · exact b6
  · exact q3_km
  · exact q3v1
  · exact q3a1
  · exact q3j1
  · exact q3b1
  · exact up1
  · exact dn1
  · exact am1
  · exact b2
  · exact jd1
  · exact b3
  · exact am2
  · exact q3b7
  · exact q3b8
  · exact q3_vd
  · exact q3_doff
  · exact q3_terr
  · exact q3_off
  · exact q3_pid
  · exact q3_lim
  · exact q3_sc
  · exact q3_pt
  · exact q3_pe
  · exact q3_ve
  · exact q3_dtk
  · exact q3_ntk
  · exact q3_vr
  · exact q3_ar
  · exact q3_ai

/-! ## The navigator after `wp_and_spline_init_m` -/

/-- `wp_and_spline_init_m` (speed `0`, no stopping point given) on the navigator: the frame of
the written fields, the jerk limit and the origin. -/
theorem t0_wpinit_frame (p : AC_WPNav.Params) (psc_p : AC_PosControl.Params) (s : AC_WPNav.State)
    (psc : AC_PosControl.State) (env : AC_WPNav.Env) :
    let W := (wp_and_spline_init_m p psc_p s psc env).1
    let Q := (wp_and_spline_init_m p psc_p s psc env).2
    W = { s with
      _wp_radius_m := MAX s._wp_radius_m WP_RADIUS_M_MIN
      _wp_speed_ms := MAX s._wp_speed_ms WP_SPD_MIN
      _check_wp_speed_change := !is_positive (0.0 : Float32)
      _wp_desired_speed_ne_ms := MAX (if is_positive (0.0 : Float32) then 0.0
        else MAX s._wp_speed_ms WP_SPD_MIN) WP_SPD_MIN
      _wp_jerk_msss := W._wp_jerk_msss
      _scurve_jerk_max_msss := W._scurve_jerk_max_msss
      _scurve_snap_max_mssss := W._scurve_snap_max_mssss
      _path_prev_leg := SimplePath.init
      _path_this_leg := SimplePath.init
      _path_next_leg := SimplePath.init
      _track_dt_scalar := 1.0
      _flags := { reached_destination := true, fast_waypoint := false }
      _origin_ned_m := W._origin_ned_m
      _destination_ned_m := W._origin_ned_m
      _is_terrain_alt := false
      _offset_vel_ms := MAX (if is_positive (0.0 : Float32) then 0.0
        else MAX s._wp_speed_ms WP_SPD_MIN) WP_SPD_MIN
      _offset_accel_mss := 0.0
      _paused := false
      _wp_last_update_ms := env.clock.millis } ∧
    W._wp_jerk_msss = (if !is_positive s._wp_jerk_msss then get_wp_acceleration_mss p
      else s._wp_jerk_msss) ∧
    W._origin_ned_m = (if (({} : Vector3p).is_zero) then get_wp_stopping_point_NED_m psc_p Q
      else {}) := by
  intro W Q
  simp only [W, Q, wp_and_spline_init_m, calc_scurve_jerk_and_snap, Id.run]
  split_ifs <;> exact ⟨rfl, rfl, rfl⟩

/-- The closed facts of the boot navigator of the run: speed `10`, radius `2`, jerk `1`, and the
default stopping point argument is the zero vector. -/
theorem t0_nav_vals :
    MAX (AC_WPNav.init runParams.wpnav)._wp_radius_m WP_RADIUS_M_MIN = 2.0 ∧
    MAX (AC_WPNav.init runParams.wpnav)._wp_speed_ms WP_SPD_MIN = 10.0 ∧
    (!is_positive (0.0 : Float32)) = true ∧ t0v0 = 10.0 ∧
    is_positive (AC_WPNav.init runParams.wpnav)._wp_jerk_msss = true ∧
    (AC_WPNav.init runParams.wpnav)._wp_jerk_msss = 1.0 ∧
    (({} : Vector3p).is_zero) = true := by
  decide +kernel

/-- **The navigator after the switch into Auto**: the steady speed bookkeeping (as `NavSteady`
asks, except the origin), three empty legs, the reached flag set, origin and destination at the
stopping point of the position controller, the time stamp of the environment's clock. -/
structure NavT0 (w : AC_WPNav.State) (q : AC_PosControl.State) (t : UInt32) : Prop where
  wp_speed : w._wp_speed_ms = 10.0
  wp_radius : w._wp_radius_m = 2.0
  wp_jerk : w._wp_jerk_msss = 1.0
  flags : w._flags = { reached_destination := true, fast_waypoint := false }
  check_speed : w._check_wp_speed_change = true
  last_speed : w._last_wp_speed_ms = 10.0
  last_speed_up : w._last_wp_speed_up_ms = 2.5
  last_speed_down : w._last_wp_speed_down_ms = 1.5
  prev_leg : w._path_prev_leg = SimplePath.init
  this_leg : w._path_this_leg = SimplePath.init
  next_leg : w._path_next_leg = SimplePath.init
  desired_speed : w._wp_desired_speed_ne_ms = 10.0
  origin : w._origin_ned_m = get_wp_stopping_point_NED_m runParams.psc q
  dest : w._destination_ned_m = get_wp_stopping_point_NED_m runParams.psc q
  track_dt : w._track_dt_scalar = 1.0
  offset_vel : w._offset_vel_ms = 10.0
  offset_accel : w._offset_accel_mss = 0.0
  paused : w._paused = false
  terrain_alt : w._is_terrain_alt = false
  last_update : w._wp_last_update_ms = t

/-- `wp_and_spline_init_m` on the boot navigator gives `NavT0`. -/
theorem t0_init_nav (psc : AC_PosControl.State) (env : AC_WPNav.Env) :
    NavT0 (wp_and_spline_init_m runParams.wpnav runParams.psc (AC_WPNav.init runParams.wpnav)
      psc env).1
      (wp_and_spline_init_m runParams.wpnav runParams.psc (AC_WPNav.init runParams.wpnav)
      psc env).2 env.clock.millis := by
  obtain ⟨hW, hJ, hO⟩ := t0_wpinit_frame runParams.wpnav runParams.psc
    (AC_WPNav.init runParams.wpnav) psc env
  obtain ⟨v1, v2, v3, v4, -, v6, v7⟩ := t0_nav_vals
  generalize (wp_and_spline_init_m runParams.wpnav runParams.psc (AC_WPNav.init runParams.wpnav)
    psc env) = R at hW hJ hO ⊢
  obtain ⟨W, Q⟩ := R
  dsimp only at hW hJ hO ⊢
  rw [v7, if_pos rfl] at hO
  simp only [v6] at hJ
  rw [hW]
  exact ⟨v2, v1, hJ, rfl, v3, rfl, rfl, rfl, rfl, rfl, rfl, v4, hO, hO, rfl, v4, rfl, rfl, rfl, rfl⟩

/-! ## The switch into Auto -/

/-- `enter_auto` with the (nonempty) hover mission: `ModeAuto::init` runs
`wp_and_spline_init_m`, sets the submode `STARTING` and `waiting_to_start`; then the rate time
constants are set and the Auto flag is raised. -/
theorem t0_enter_auto_eq (s : Copter.State) :
    Copter.enter_auto runParams s = some { s with
      mode_auto := { s.mode_auto with _mode := .STARTING, waiting_to_start := true }
      wp_nav := (wp_and_spline_init_m runParams.wpnav runParams.psc s.wp_nav s.pos_control
        (s.wpEnv runParams)).1
      pos_control := (wp_and_spline_init_m runParams.wpnav runParams.psc s.wp_nav s.pos_control
        (s.wpEnv runParams)).2
      attitude_control := { s.attitude_control with
        _rate_rp_tc := runParams.ACRO_RP_RATE_TC, _rate_y_tc := runParams.PILOT_Y_RATE_TC }
      in_auto := true } := by
  have hm : Copter.ModeAuto.mission_present runParams = true := by
    simp [Copter.ModeAuto.mission_present, runParams_mission_ne]
  unfold Copter.enter_auto Copter.ModeAuto.init
  simp only [hm, Bool.not_true, Bool.false_eq_true, if_false]
  rfl

end Contracts.CopterHover
