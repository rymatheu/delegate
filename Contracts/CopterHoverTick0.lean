import Contracts.CopterHoverTick0Run

/-!
# Tick 0 of the hover run

The first tick of the closed-loop hover run, from the boot harness state
`CopterLift.Harness.init runParams` and the plant state `phys0`, to the invariant `InvP1` of
`Contracts.CopterHover` (from which `tick_one` and then `tick_steady` carry the run on), plus the
vertical acceleration limit `_accel_max_d_mss = WP_ACC_Z = 1` that `tick_one` assumes.

The tick is the composition of the stages of the files `CopterHoverTick0Boot` (the takeover and
the common prefix), `CopterHoverTick0Init` (the switch into Auto), `CopterHoverTick0Start` (the
mission start) and `CopterHoverTick0Run` (the first `wp_run`):

1. the sample of `phys0` is level and at rest (`t0_sample`); the takeover gives `AttT0`, `MotT0`
   (`t0_takeover`); the prefix gives the explicit state of `t0_prefix`;
2. the vehicle is not in Auto, so `loop` calls `enter_auto` (`t0_loop`, `t0_enter_auto_eq`);
   `wp_and_spline_init_m` gives `PscT0` and `NavT0` (`t0_psc7`, `t0_init_nav`);
3. `ModeAuto.run` starts the mission and dispatches to `wp_run` (`t0_run_eq`), with the navigator
   of `t0_set_dest` (empty leg by `t0_leg_is_zero`);
4. `wp_run_t0` gives `InvCore`, `NavP1` and the frame, and the plant moves to
   `vstate (-1) (-k h (Hf - 4/9)) (-k Hf)`, a vertical speed of `2.45 · 10⁻⁶` m/s.

Hypotheses: `LibmZero32`, `LibmCos32` (finite boot motor factors), `ConvZero`, `NarrowSpec 2`,
`WidenSpec` (the stopping point widens a nonzero `float` altitude) and `CopterSense`.
-/

namespace Contracts.CopterHover

open AP_Math AC_WPNav Contracts.CopterZero
open Contracts.CopterVertNear (Near32 Near64 NarrowSpec dtF)

/-- On a state not yet in Auto, `Copter.loop` is the prefix, the switch into Auto, and
`update_flight_mode`. -/
theorem t0_loop (p : Copter.Parameters) (st : Copter.State) (smp : Copter.AHRS.Sample)
    (h : (prefixState p st smp).in_auto = false) :
    Copter.loop p st smp =
      (Copter.enter_auto p (prefixState p st smp)).bind
        (fun s => some (Copter.update_flight_mode p s)) := by
  unfold prefixState at h
  unfold Copter.loop
  dsimp only
  rw [if_neg (by rw [h]; exact Bool.false_ne_true)]
  rfl

/-- The specific force of `phys0` is `-k Hf`. -/
theorem t0_sf : QuadPlant.thrust2weight * CopterPlant.gravity * Hf = CopterVert.k * Hf := by
  rw [CopterVertNear.k_eq, QuadPlant.thrust2weight, CopterPlant.gravity]; ring

/-- The vertical speed after tick 0, `-k h (Hf - 4/9) ≈ 2.45 · 10⁻⁶` m/s, is below `10⁻⁵`. -/
theorem t0_w1 : |0 - CopterVert.k * CopterVert.h * (Hf - 4 / 9)| ≤ 1e-5 := by
  rw [CopterVertNear.k_eq, CopterVertNear.h_eq,
    show Hf = 7455795 / 16777216 from CopterVertNear.Hf_eq]
  norm_num [abs_le]

set_option maxHeartbeats 1000000 in
/-- **Tick 0 of the harness.** From the boot state and the sample of `phys0`, the harness step
sets the started flag, reaches the invariant `InvP1` with the plant stepped by the printed
actuators, and leaves the vertical acceleration limit at `WP_ACC_Z = 1`. -/
theorem tick_zero (L : LibmZero32) (LC : LibmCos32) (C : ConvZero) (N : CopterVertNear.NarrowSpec 2)
    (W : WidenSpec) {sense32 : ℝ → Float32} {senseP : ℝ → Float}
    (S : CopterPlant.CopterSense sense32 senseP) :
    let r := CopterLift.tick runParams (CopterLift.Harness.init runParams)
      (CopterPlant.sample sense32 senseP phys0)
    r.1.started = true ∧ InvP1 r.1.st (CopterPlant.dyn phys0 r.2) ∧
      1 / 100 ≤ r.1.st.pos_control._accel_max_d_mss.toReal := by
  intro r
  -- the sample
  have hsmp := t0_sample S
  set zP := senseP (-1) with hzP
  set fs := sense32 (-(QuadPlant.thrust2weight * CopterPlant.gravity * Hf)) with hfs
  have hFb : |-(CopterVert.k * Hf)| ≤ 10.05 := by
    rw [CopterVertNear.k_eq, show Hf = 7455795 / 16777216 from CopterVertNear.Hf_eq]
    norm_num [abs_le]
  obtain ⟨nz, -, nf⟩ := CopterVertNear.sense_near S (ζ := 0) (w := 0) (f := -(CopterVert.k * Hf))
    (by norm_num) (by norm_num) hFb
  have hz : Near64 zP (-1) 1e-15 := by
    rw [hzP]; have := nz; rwa [show (0 : ℝ) - 1 = -1 by norm_num] at this
  have hfn : Near32 fs (-(CopterVert.k * Hf)) 6e-7 := by rw [hfs, t0_sf]; exact nf
  set smp := t0smp zP fs with hsmpd
  have hq : smp.quat = ⟨1, 0, 0, 0⟩ := rfl
  have hg : smp.gyro = ⟨0, 0, 0⟩ := rfl
  have hdt : smp.dt_us = 2500 := rfl
  -- the takeover
  obtain ⟨a0, m0, hT, hA0, hM0⟩ := t0_takeover L LC smp hq
  set T := Copter.takeover runParams t0S0 smp with hTdef
  -- the prefix
  obtain ⟨a6, mo, m, h6, hA6, ha6dt, hM6⟩ := t0_prefix T smp hg hdt
    (by rw [hT]; exact hA0) (by rw [hT]; exact hM0)
  set s6 := prefixState runParams T smp with hs6
  have h6in : s6.in_auto = false := by rw [h6, hT]; rfl
  -- the switch into Auto
  have hloop := t0_loop runParams T smp h6in
  rw [← hs6, t0_enter_auto_eq] at hloop
  -- the state after the prefix
  have hTsch : T.scheduler = {} := by rw [hT]; rfl
  have hs6w : s6.wp_nav = AC_WPNav.init runParams.wpnav := by rw [h6, hT]; rfl
  have hs6p : s6.pos_control = t0Q0 zP := by rw [h6, hT]; rfl
  have hs6y : s6.auto_yaw = {} := by rw [h6, hT]; rfl
  have hs6mo : s6.mode_auto = {} := by rw [h6, hT]; rfl
  have hs6a : s6.attitude_control = a6 := by rw [h6]
  have hs6m : s6.motors = mo := by rw [h6]
  have hs6act : s6.actuators = mo._actuator := by rw [h6]
  have hs6ahrs : s6.ahrs = Copter.AHRS.update smp := by rw [h6]
  have hs6sch : s6.scheduler = (Copter.scheduler_loop T smp.dt_us).scheduler := by rw [h6]
  have hs6t : s6.scheduler.ticks32 = 1 := by
    rw [hs6sch]; unfold Copter.scheduler_loop; rw [hTsch]; rfl
  have hs6u : s6.scheduler.micros = 2500 := by
    rw [hs6sch]; unfold Copter.scheduler_loop; rw [hTsch]; rfl
  have hclk6 : s6.clock = ⟨1, 2⟩ := by
    unfold Copter.State.clock; rw [hs6t, hs6u]; rfl
  obtain ⟨vcp, vcr, -, -, -, -, -, -, -, vq, -, vacc, vpos, vvel, -⟩ := ahrs_update_level L smp hq
  -- the environment of `wp_and_spline_init_m`
  have hIs := Istar_val
  have hfs' : Near32 fs (-(CopterVert.k * (CopterVertNear.Istar + 4 / 9))) 6e-7 := by
    rw [CopterVertNear.Istar, sub_add_cancel]; exact hfn
  have hmeas := CopterVertNear.accel_meas_near hfs' (by rw [hIs]; norm_num [abs_le])
  have hest : (AC_PosControl.get_estimated_accel_D_mss (s6.wpEnv runParams).ahrs).IsFinite ∧
      |(AC_PosControl.get_estimated_accel_D_mss (s6.wpEnv runParams).ahrs).toReal| ≤ 1 := by
    have e : AC_PosControl.get_estimated_accel_D_mss (s6.wpEnv runParams).ahrs =
        fs + GRAVITY_MSS := by
      show s6.ahrs.accel_ef.z + GRAVITY_MSS = fs + GRAVITY_MSS
      rw [hs6ahrs, vacc]; rfl
    rw [e]
    refine ⟨hmeas.1, ?_⟩
    have h1 := hmeas.2
    have h2 := abs_le.1 h1
    rw [CopterVertNear.k_eq, hIs] at h2
    rw [abs_le]; constructor <;> linarith
  have hhov6 : mo._throttle_hover = CopterVertNear.hoverF := hM6.motlim.hover
  have hthr6 : (s6.wpEnv runParams).att.get_throttle_in =
      AP_Motors.get_throttle_hover (s6.wpEnv runParams).motors := by
    show s6.attitude_control._throttle_in = AP_Motors.get_throttle_hover s6.motors.toInputs
    rw [hs6a, hs6m, hA6.thr, CopterVertNear.throttle_hover_eq _ hhov6]
  have hQ7 : PscT0 (wp_and_spline_init_m runParams.wpnav runParams.psc s6.wp_nav s6.pos_control
      (s6.wpEnv runParams)).2 zP := by
    rw [hs6w, hs6p]
    exact t0_psc7 N W hz (s6.wpEnv runParams) hclk6 hthr6
      (by show s6.motors._throttle_hover = _; rw [hs6m]; exact hhov6) hest.1 hest.2
      (by show t0attC (Copter.attInputs runParams s6.attitude_control) = _; rfl)
  have hW7 : NavT0 (wp_and_spline_init_m runParams.wpnav runParams.psc s6.wp_nav s6.pos_control
      (s6.wpEnv runParams)).1 (wp_and_spline_init_m runParams.wpnav runParams.psc s6.wp_nav
      s6.pos_control (s6.wpEnv runParams)).2 (s6.wpEnv runParams).clock.millis := by
    rw [hs6w, hs6p]
    exact t0_init_nav _ _
  generalize hR7 : wp_and_spline_init_m runParams.wpnav runParams.psc s6.wp_nav s6.pos_control
    (s6.wpEnv runParams) = R7 at hloop hQ7 hW7
  obtain ⟨W7, Q7⟩ := R7
  dsimp only at hloop hQ7 hW7
  -- the state after the switch into Auto
  set s7 : Copter.State := { s6 with
      mode_auto := { s6.mode_auto with _mode := .STARTING, waiting_to_start := true }
      wp_nav := W7
      pos_control := Q7
      attitude_control := { s6.attitude_control with
        _rate_rp_tc := runParams.ACRO_RP_RATE_TC, _rate_y_tc := runParams.PILOT_Y_RATE_TC }
      in_auto := true } with hs7
  have hloop7 : Copter.loop runParams T smp = some (Copter.ModeAuto.run runParams s7) := by
    rw [hloop]; rfl
  have hclk7 : s7.clock = ⟨1, 2⟩ := hclk6
  have hact7 : AC_WPNav.is_active s7.wp_nav s7.clock = true := by
    show AC_WPNav.is_active W7 s7.clock = true
    unfold AC_WPNav.is_active
    rw [hW7.last_update, hclk7, show (s6.wpEnv runParams).clock = s6.clock from rfl, hclk6]
    decide
  have hyaw7 : s7.auto_yaw._mode = .LOOK_AT_NEXT_WP := by
    show s6.auto_yaw._mode = _; rw [hs6y]
  have hrun := t0_run_eq s7 rfl hact7 hyaw7
  -- the mission start
  have hleg := calculate_track_empty W7._destination_ned_m hoverWP
    (AC_PosControl.NE_get_max_speed_ms Q7) (AC_PosControl.get_max_speed_up_ms Q7)
    (AC_PosControl.get_max_speed_down_ms Q7) (get_wp_acceleration_mss runParams.wpnav)
    (get_accel_D_mss runParams.wpnav)
    (t0_leg_is_zero C N (by rw [hW7.dest]; exact hQ7.sp_x) (by rw [hW7.dest]; exact hQ7.sp_y)
      (by rw [hW7.dest]; exact ⟨hQ7.sp_z.1, hQ7.sp_z.2.trans (by norm_num)⟩))
  have hsd := t0_set_dest W7 Q7 (s7.wpEnv runParams) hact7 hW7.flags hW7.this_leg hleg
  generalize hs8 : ({ s7 with
      wp_nav := (set_wp_destination_NED_m runParams.wpnav runParams.psc s7.wp_nav s7.pos_control
        (s7.wpEnv runParams) hoverWP).1
      pos_control := (set_wp_destination_NED_m runParams.wpnav runParams.psc s7.wp_nav
        s7.pos_control (s7.wpEnv runParams) hoverWP).2
      mode_auto := { s7.mode_auto with
        _mode := .WP, waiting_to_start := false, loiter_time := 0, loiter_time_max := 0,
        mission := (⟨.MISSION_RUNNING, some hoverCmd, true⟩ : Copter.Mission) } } :
      Copter.State) = s8 at hrun
  have e8w : s8.wp_nav = { W7 with
      _path_prev_leg := SimplePath.init
      _origin_ned_m := W7._destination_ned_m
      _destination_ned_m := hoverWP
      _is_terrain_alt := false
      _path_this_leg := SimplePath.init
      _path_next_leg := SimplePath.init
      _next_destination_ned_m := W7._next_destination_ned_m.zero
      _flags := { reached_destination := false, fast_waypoint := false } } := by
    rw [← hs8]
    show (set_wp_destination_NED_m runParams.wpnav runParams.psc W7 Q7 (s7.wpEnv runParams)
      hoverWP).1 = _
    rw [hsd]
  have e8p : s8.pos_control = Q7 := by
    rw [← hs8]
    show (set_wp_destination_NED_m runParams.wpnav runParams.psc W7 Q7 (s7.wpEnv runParams)
      hoverWP).2 = _
    rw [hsd]
  have e8m : s8.motors = mo := by rw [← hs8]; exact hs6m
  have e8act : s8.actuators = mo._actuator := by rw [← hs8]; exact hs6act
  have e8ahrs : s8.ahrs = Copter.AHRS.update smp := by rw [← hs8]; exact hs6ahrs
  have e8a : s8.attitude_control = { a6 with
      _rate_rp_tc := runParams.ACRO_RP_RATE_TC, _rate_y_tc := runParams.PILOT_Y_RATE_TC } := by
    rw [← hs8]; show { s6.attitude_control with
      _rate_rp_tc := runParams.ACRO_RP_RATE_TC, _rate_y_tc := runParams.PILOT_Y_RATE_TC } = _
    rw [hs6a]
  have e8sch : s8.scheduler = s6.scheduler := by rw [← hs8]
  have e8y : s8.auto_yaw = s7.auto_yaw := by rw [← hs8]
  have e8in : s8.in_auto = true := by rw [← hs8]
  have e8mo : s8.mode_auto = { s7.mode_auto with
      _mode := .WP, waiting_to_start := false, loiter_time := 0, loiter_time_max := 0,
      mission := (⟨.MISSION_RUNNING, some hoverCmd, true⟩ : Copter.Mission) } := by rw [← hs8]
  -- `Pre0`
  have hpre : Pre0 s8 m zP := {
    hz := hz
    m_dt := hM6.m_dt, m_F := hM6.m_F, m_Fv := hM6.m_Fv, m_T := hM6.m_T, m_cut := hM6.m_cut
    F_eq := by rw [e8m]; exact hM6.F_eq
    act := by rw [e8act]; exact hM6.act
    lower := by rw [e8m]; exact hM6.lower
    upper := by rw [e8m]; exact hM6.upper
    motlim := by rw [e8m]; exact hM6.motlim
    boost := by rw [e8m]; exact hM6.boost
    cp := by rw [e8ahrs]; exact vcp
    cr := by rw [e8ahrs]; exact vcr
    quat := by rw [e8ahrs]; exact vq
    fs := by rw [e8ahrs, vacc]; exact hfn
    psc := by rw [e8p]; exact hQ7
    att := by
      rw [e8a]
      exact ⟨hA6.target, hA6.euler, hA6.ang_vel, hA6.ang_accel, hA6.body, hA6.sysid,
        hA6.act_sysid, hA6.rate_roll, hA6.rate_pitch, hA6.rate_yaw, hA6.pd, hA6.isc, hA6.angP,
        hA6.ff, hA6.thrust_angle, hA6.thr⟩
    att_dt := by rw [e8a]; exact ha6dt
    ytc := by rw [e8a]; show runParams.PILOT_Y_RATE_TC.IsFinite; decide
    ticks := by rw [e8sch]; exact hs6t
    micros := by rw [e8sch]; exact hs6u }
  -- the navigator of the mission start
  have hn8 : NavSteady { s8.wp_nav with _origin_ned_m := hoverWP } := by
    rw [e8w]
    exact ⟨hW7.wp_speed, hW7.wp_radius, hW7.wp_jerk, rfl, hW7.check_speed, hW7.last_speed,
      hW7.last_speed_up, hW7.last_speed_down, rfl, rfl, rfl, hW7.desired_speed, rfl, hW7.track_dt,
      hW7.offset_vel, hW7.offset_accel, hW7.paused, rfl⟩
  have ho8 : s8.wp_nav._origin_ned_m = get_wp_stopping_point_NED_m runParams.psc Q7 := by
    rw [e8w]; exact hW7.dest
  obtain ⟨hI, hN, hmo', hy', hi', hsch', hact', hamax'⟩ := wp_run_t0 L C N s8 m zP hpre hn8
    (by rw [ho8]; exact hQ7.sp_x) (by rw [ho8]; exact hQ7.sp_y) (by rw [ho8]; exact hQ7.sp_z)
    (by rw [e8w]) (by rw [e8w]) (by rw [e8y]; exact hyaw7)
  -- the harness step
  have hr : r = (⟨Copter.ModeAuto.wp_run runParams s8, true⟩,
      (Copter.ModeAuto.wp_run runParams s8).actuators) := by
    show CopterLift.tick runParams (CopterLift.Harness.init runParams)
      (CopterPlant.sample sense32 senseP phys0) = _
    rw [hsmp]
    unfold CopterLift.tick
    dsimp only
    rw [show (CopterLift.Harness.init runParams).started = false from rfl, if_neg (by decide)]
    rw [show (CopterLift.Harness.init runParams).st = t0S0 from rfl, ← hTdef, hloop7]
    dsimp only
    rw [hrun]
  rw [hr]
  -- the plant after the tick
  have hHf0 : (0 : ℝ) ≤ Hf := by
    rw [show Hf = 7455795 / 16777216 from CopterVertNear.Hf_eq]; norm_num
  have hHf1 : Hf ≤ 1 := by rw [show Hf = 7455795 / 16777216 from CopterVertNear.Hf_eq]; norm_num
  have hphys0 : phys0 = CopterPlant.vstate (0 - 1) 0
      (-(QuadPlant.thrust2weight * CopterPlant.gravity * Hf)) := by
    rw [phys0]; norm_num
  have hpv := CopterVertNear.plant_vert (0 - 1) 0
    (-(QuadPlant.thrust2weight * CopterPlant.gravity * Hf))
    (Copter.ModeAuto.wp_run runParams s8).actuators
    hHf0 hHf1 (fun i => by rw [hact', e8act]; exact (hM6.act i).2)
  refine ⟨rfl, ⟨?_, hN, ?_, ?_, ?_⟩, ?_⟩
  · show InvCore _ (CopterPlant.dyn phys0 _)
    rw [hphys0]; exact hI _
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · show (Copter.ModeAuto.wp_run runParams s8).in_auto = true
      rw [hi', e8in]
    · show (Copter.ModeAuto.wp_run runParams s8).mode_auto._mode = .WP
      rw [hmo', e8mo]
    · show (Copter.ModeAuto.wp_run runParams s8).mode_auto.waiting_to_start = false
      rw [hmo', e8mo]
    · show (Copter.ModeAuto.wp_run runParams s8).mode_auto.mission.state = .MISSION_RUNNING
      rw [hmo', e8mo]
    · show (Copter.ModeAuto.wp_run runParams s8).mode_auto.mission.nav_cmd = some hoverCmd
      rw [hmo', e8mo]
    · show (Copter.ModeAuto.wp_run runParams s8).mode_auto.mission.nav_cmd_loaded = true
      rw [hmo', e8mo]
    · show (Copter.ModeAuto.wp_run runParams s8).mode_auto.loiter_time_max = 0
      rw [hmo', e8mo]
    · show (Copter.ModeAuto.wp_run runParams s8).auto_yaw._mode = .LOOK_AT_NEXT_WP
      rw [hy', e8y]; exact hyaw7
    · show (Copter.ModeAuto.wp_run runParams s8).scheduler.ticks32 = 1
      rw [hsch', e8sch]; exact hs6t
    · show (Copter.ModeAuto.wp_run runParams s8).scheduler.micros = 2500
      rw [hsch', e8sch]; exact hs6u
  · show (CopterPlant.dyn phys0 _).p.z = -1
    rw [hphys0, hpv]
    show (0 - 1 : ℝ) + CopterVert.h * 0 = -1
    ring
  · show |(CopterPlant.dyn phys0 _).v.z| ≤ 1e-5
    rw [hphys0, hpv]
    exact t0_w1
  · show 1 / 100 ≤ (Copter.ModeAuto.wp_run runParams s8).pos_control._accel_max_d_mss.toReal
    rw [hamax', e8p, hQ7.amax1]
    norm_num

end Contracts.CopterHover
