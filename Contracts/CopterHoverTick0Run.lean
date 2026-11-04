import Contracts.CopterHoverTick0Nav

/-!
# Tick 0 of the hover run: the first `wp_run`

The last stage of tick 0: `wp_run` on the state left by the mission start, with AutoYaw in
`LOOK_AT_NEXT_WP`. The facts it needs about that state are collected in `Pre0` (the analogue of
`PreRun` for the first tick: the motors with the throttle filter at `Hf`, input equal to output,
both vertical PIDs in reset with a zero acceleration integrator, the position target within
`10⁻⁶` of `-1`, the attitude controller of the takeover). `wp_run_t0` follows the steady proof
`wp_run_steady` with three changes:

* the navigator step is `t0_update_wpnav` (leg origin at the boot stopping point, destination
  reached on this tick);
* the vertical tick is `vert_tick0` (both PIDs in reset), which puts the exact values in the
  sublevel set `V ≤ 1/10` and establishes `VInv`;
* the heading is `Angle_And_Rate` (`get_heading_next_wp`): the yaw target of the position
  controller, which `NE_update_controller` sets to the attitude controller's Euler yaw target, a
  zero, and a zero yaw rate (`multi_angle_and_rate_Z`).

The result is `InvCore` for the plant stepped from `vstate (-1) 0 f` by the actuators (whatever
the stored specific force `f`), `NavP1` for the navigator, and the frame of the mode, AutoYaw,
scheduler, actuators and the vertical acceleration limit.
-/

open Float.Model UnpackedFloat AP_Math Contracts.CopterZero Contracts.CopterPlant
open Contracts.CopterVertNear (Near32 Near64 NarrowSpec dtF VInv vx hoverF)

namespace Contracts.CopterHover

/-- **What the first `wp_run` needs**, on the state `s` reached by the mission start, with `m`
the motors object the throttle filter update of the tick started from and `zP` the altitude
reading. -/
structure Pre0 (s : Copter.State) (m : AP_MotorsMulticopter.State) (zP : Float) : Prop where
  hz : Near64 zP (-1) 1e-15
  -- the motors before the filter update
  m_dt : m._dt_s = dtF
  m_F : m._throttle_filter_value.IsFinite
  m_Fv : m._throttle_filter_value.toReal = Hf
  m_T : m._throttle_in = m._throttle_filter_value
  m_cut : m._throttle_filter_cutoff = AC_PosControl.POSCONTROL_THROTTLE_CUTOFF_FREQ_HZ
  -- the motors after `motors_output_main`
  F_eq : s.motors._throttle_filter_value =
    (AP_MotorsMulticopter.update_throttle_filter m)._throttle_filter_value
  act : ∀ i : Fin 4, (s.actuators[i]).IsFinite ∧ (s.actuators[i]).toReal = Hf
  lower : s.motors.limit.throttle_lower = false
  upper : s.motors.limit.throttle_upper = false
  motlim : MotLim s.motors
  boost : Z s.motors._thrust_boost_ratio
  -- the AHRS of the tick
  cp : One s.ahrs.cos_pitch
  cr : One s.ahrs.cos_roll
  quat : IdQ s.ahrs.quat_body_to_ned
  fs : Near32 s.ahrs.accel_ef.z (-(CopterVert.k * Hf)) 6e-7
  -- the position controller
  psc : PscT0 s.pos_control zP
  -- the attitude controller
  att : AttT0 s.attitude_control
  att_dt : s.attitude_control._dt_s = dtF
  ytc : s.attitude_control._rate_y_tc.IsFinite
  -- the clock
  ticks : s.scheduler.ticks32 = 1
  micros : s.scheduler.micros = 2500

/-- `wp_run` with AutoYaw in `LOOK_AT_NEXT_WP`, as the composition of its calls. -/
theorem wp_run_next_wp (p : Copter.Parameters) (s : Copter.State)
    (hy : s.auto_yaw._mode = .LOOK_AT_NEXT_WP) :
    Copter.ModeAuto.wp_run p s =
      let r1 := AC_WPNav.update_wpnav p.wpnav p.psc s.wp_nav s.pos_control (s.wpEnv p)
      let r2 := AC_PosControl.D_update_controller p.psc r1.2.1 s.ahrs.posInputs s.motors.toInputs
        (Copter.attInputs p s.attitude_control) s.clock
      let r3 := AC_AttitudeControl_Multi.set_throttle_out p.att s.attitude_control
        s.motors.toInputs s.ahrs.cos_pitch s.ahrs.cos_roll r2.2.throttle_in r2.2.apply_angle_boost
        r2.2.filt_cutoff
      { s with
        wp_nav := r1.1
        pos_control := r2.1
        attitude_control := AC_AttitudeControl_Multi.input_thrust_vector_heading p.att r3.1
          s.ahrs.quat_body_to_ned (AC_PosControl.get_thrust_vector r2.1)
          { yaw_angle_rad := AC_PosControl.get_yaw_rad r2.1,
            yaw_rate_rads := AC_PosControl.get_yaw_rate_rads r2.1,
            heading_mode := .Angle_And_Rate }
        motors := { s.motors with toInputs := r3.2 }
        auto_yaw := { s.auto_yaw with
          _pilot_yaw_rate_rads := 0.0
          _yaw_angle_rad := AC_PosControl.get_yaw_rad r2.1
          _yaw_rate_rads := AC_PosControl.get_yaw_rate_rads r2.1 } } := by
  unfold Copter.ModeAuto.wp_run
  simp only [Id.run]
  rw [get_heading_next_wp]
  · rfl
  · exact hy

set_option maxHeartbeats 4000000 in
/-- **`wp_run` at tick 0.** On a state satisfying `Pre0`, with the navigator of the mission start
(steady except for the origin `o`, zero horizontally and within `10⁻⁶` of `-1` vertically,
destination `hoverWP` not yet reached) and AutoYaw in `LOOK_AT_NEXT_WP`, `wp_run` establishes
the core invariant for the plant stepped from `vstate (-1) 0 f` by the actuators of the tick
(whatever `f`), `NavP1` for the navigator, and changes neither the mode, nor AutoYaw's mode, nor
the Auto flag, nor the scheduler, nor the actuators, nor the vertical acceleration limit. -/
theorem wp_run_t0 (L : LibmZero32) (C : ConvZero) (N : NarrowSpec 2)
    (s : Copter.State) (m : AP_MotorsMulticopter.State) (zP : Float) (hp : Pre0 s m zP)
    (hn : NavSteady { s.wp_nav with _origin_ned_m := hoverWP })
    (hox : ZD s.wp_nav._origin_ned_m.x) (hoy : ZD s.wp_nav._origin_ned_m.y)
    (hoz : Near64 s.wp_nav._origin_ned_m.z (-1) 1e-6)
    (hd : s.wp_nav._destination_ned_m = hoverWP)
    (hr : s.wp_nav._flags.reached_destination = false)
    (hy : s.auto_yaw._mode = .LOOK_AT_NEXT_WP) :
    (∀ f : ℝ, InvCore (Copter.ModeAuto.wp_run runParams s)
      (dyn (vstate (0 - 1) 0 f) (Copter.ModeAuto.wp_run runParams s).actuators)) ∧
    NavP1 (Copter.ModeAuto.wp_run runParams s).wp_nav ∧
    (Copter.ModeAuto.wp_run runParams s).mode_auto = s.mode_auto ∧
    (Copter.ModeAuto.wp_run runParams s).auto_yaw._mode = s.auto_yaw._mode ∧
    (Copter.ModeAuto.wp_run runParams s).in_auto = s.in_auto ∧
    (Copter.ModeAuto.wp_run runParams s).scheduler = s.scheduler ∧
    (Copter.ModeAuto.wp_run runParams s).actuators = s.actuators ∧
    (Copter.ModeAuto.wp_run runParams s).pos_control._accel_max_d_mss =
      s.pos_control._accel_max_d_mss := by
  rw [wp_run_next_wp runParams s hy]
  have hq := hp.psc
  have hpez : Near64 s.pos_control._pos_estimate_ned_m.z (-1) 1e-15 := by
    rw [hq.pez]; exact hp.hz
  have hpt' : Near64 s.pos_control._pos_target_ned_m.z (-1) (1 / 100) :=
    ⟨hq.pos_target.1, hq.pos_target.2.trans (by norm_num)⟩
  have hclk : s.clock = ⟨1, 2⟩ := by
    unfold Copter.State.clock; rw [hp.ticks, hp.micros]; rfl
  -- the navigator
  obtain ⟨nav', tp, tv, ta, hnav', hno', hnd', hnr', hnl', htpx, htpy, htpz, htv, hta, hU⟩ :=
    t0_update_wpnav C N hn hox hoy hoz hd hr (s.wpEnv runParams) hq.dt hq.vel_desired
      hq.doff.2.2.2.1 hq.terr.2.1 hpez hq.pex hq.pey ⟨hq.off.2.1.1, hq.off.2.1.2, hq.doff.2.1⟩ hpt'
  rw [hU]
  dsimp only
  -- the horizontal position controller
  set psc0 := AC_PosControl.set_pos_vel_accel_NED_m
    (AC_PosControl.set_pos_terrain_target_D_m s.pos_control 0.0) tp tv ta with hpsc0
  have hdt0 : psc0._dt_s = dtF := hq.dt
  have hne_act : AC_PosControl.NE_is_active psc0 (s.wpEnv runParams).clock = true := by
    show AC_PosControl.NE_is_active psc0 s.clock = true
    unfold AC_PosControl.NE_is_active
    rw [hclk, show psc0._last_update_ne_ticks = 1 from hq.ne_ticks]
    decide
  have hNEOK := NEOK_run psc0 (s.wpEnv runParams).ahrs
    (by rw [hdt0]; exact CopterVertNear.dtF_val.1) (by rw [hdt0]; exact dtF_abs) hq.psclim.amax_ne
    hq.psclim.jmax_ne hq.psclim.jmax_ne_b hq.psclim.vmax_ne hq.lim lit_one.1 hq.nescale
  obtain ⟨hyaw1, hyaw2⟩ := NE_update_controller_hover_yaw C runParams.psc psc0
    (s.wpEnv runParams).ahrs (s.wpEnv runParams).att (s.wpEnv runParams).clock hNEOK hne_act hq.off
    htpx.1 htpy.1 hq.pex.1 hq.pey.1 (htpx.2.trans hq.pex.2.symm) (htpy.2.trans hq.pey.2.symm)
    ⟨htv.1, htv.2.1⟩ ⟨hq.vex, hq.vey⟩ ⟨hta.1, hta.2.1⟩ hq.pid_ne hq.vmax0 hq.vmaxb
  obtain ⟨hNE, hr, hrt, hrs, hrl, hrpdz, hrptz, hrvd, hrad, hrpe, hrve, -, -, -, -, -, -, hro1,
      hro2, hro3, hro4, hro5, hro6, -, -, -⟩ :=
    NE_update_controller_hover_run C psc0 (s.wpEnv runParams).ahrs (s.wpEnv runParams).att
      (s.wpEnv runParams).clock (by rw [hdt0]; exact CopterVertNear.dtF_val.1)
      (by rw [hdt0]; exact dtF_abs) hq.psclim.amax_ne hq.psclim.jmax_ne hq.psclim.jmax_ne_b
      hq.psclim.vmax_ne hq.lim lit_one.1 hq.nescale hne_act hq.off htpx.1 htpy.1 hq.pex.1
      hq.pey.1 (htpx.2.trans hq.pex.2.symm) (htpy.2.trans hq.pey.2.symm)
      ⟨htv.1, htv.2.1⟩ ⟨hq.vex, hq.vey⟩ ⟨hta.1, hta.2.1⟩ hq.pid_ne
  generalize AC_PosControl.NE_update_controller runParams.psc psc0 (s.wpEnv runParams).ahrs
    (s.wpEnv runParams).att (s.wpEnv runParams).clock = r at *
  have er : ∀ {α : Type} (f : AC_PosControl.State → α), (∀ q : AC_PosControl.State,
      f { psc0 with
        _p_pos_ne_m := q._p_pos_ne_m, _pid_vel_ne_m := q._pid_vel_ne_m,
        _last_update_ne_ticks := q._last_update_ne_ticks,
        _ne_control_scale_factor := q._ne_control_scale_factor,
        _roll_target_rad := q._roll_target_rad, _pitch_target_rad := q._pitch_target_rad,
        _yaw_target_rad := q._yaw_target_rad, _yaw_rate_target_rads := q._yaw_rate_target_rads,
        _pos_desired_ned_m := { psc0._pos_desired_ned_m with
          x := q._pos_desired_ned_m.x, y := q._pos_desired_ned_m.y },
        _pos_target_ned_m := { psc0._pos_target_ned_m with
          x := q._pos_target_ned_m.x, y := q._pos_target_ned_m.y },
        _vel_target_ned_ms := { psc0._vel_target_ned_ms with
          x := q._vel_target_ned_ms.x, y := q._vel_target_ned_ms.y },
        _accel_target_ned_mss := { psc0._accel_target_ned_mss with
          x := q._accel_target_ned_mss.x, y := q._accel_target_ned_mss.y },
        _limit_vector_ned := { psc0._limit_vector_ned with
          x := q._limit_vector_ned.x, y := q._limit_vector_ned.y },
        _pos_offset_target_ned_m := { psc0._pos_offset_target_ned_m with
          x := q._pos_offset_target_ned_m.x, y := q._pos_offset_target_ned_m.y },
        _pos_offset_ned_m := { psc0._pos_offset_ned_m with
          x := q._pos_offset_ned_m.x, y := q._pos_offset_ned_m.y },
        _vel_offset_target_ned_ms := { psc0._vel_offset_target_ned_ms with
          x := q._vel_offset_target_ned_ms.x, y := q._vel_offset_target_ned_ms.y },
        _vel_offset_ned_ms := { psc0._vel_offset_ned_ms with
          x := q._vel_offset_ned_ms.x, y := q._vel_offset_ned_ms.y },
        _accel_offset_target_ned_mss := { psc0._accel_offset_target_ned_mss with
          x := q._accel_offset_target_ned_mss.x, y := q._accel_offset_target_ned_mss.y },
        _accel_offset_ned_mss := { psc0._accel_offset_ned_mss with
          x := q._accel_offset_ned_mss.x, y := q._accel_offset_ned_mss.y } } = f psc0) →
      f r = f psc0 := by
    intro α f hf; rw [hr]; exact hf r
  have hr_dt : r._dt_s = dtF := (er (·._dt_s) (fun _ => rfl)).trans hdt0
  have hr_pp : r._p_pos_d_m = s.pos_control._p_pos_d_m := er (·._p_pos_d_m) (fun _ => rfl)
  have hr_pv : r._pid_vel_d_m = s.pos_control._pid_vel_d_m := er (·._pid_vel_d_m) (fun _ => rfl)
  have hr_pa : r._pid_accel_d_m = s.pos_control._pid_accel_d_m :=
    er (·._pid_accel_d_m) (fun _ => rfl)
  have hr_lud : r._last_update_d_ticks = s.pos_control._last_update_d_ticks :=
    er (·._last_update_d_ticks) (fun _ => rfl)
  have hr_key : pscKey r = pscKey s.pos_control := er pscKey (fun _ => rfl)
  have hr_amax : r._accel_max_d_mss = s.pos_control._accel_max_d_mss :=
    er (·._accel_max_d_mss) (fun _ => rfl)
  have hr_ter : r._pos_terrain_target_d_m = 0.0 := er (·._pos_terrain_target_d_m) (fun _ => rfl)
  have hr_ter2 : r._pos_terrain_d_m = s.pos_control._pos_terrain_d_m :=
    er (·._pos_terrain_d_m) (fun _ => rfl)
  have hr_ter3 : r._vel_terrain_d_ms = s.pos_control._vel_terrain_d_ms :=
    er (·._vel_terrain_d_ms) (fun _ => rfl)
  have hr_ter4 : r._accel_terrain_d_mss = s.pos_control._accel_terrain_d_mss :=
    er (·._accel_terrain_d_mss) (fun _ => rfl)
  have hrlim : PscLim r := PscLim.congr hq.psclim hr_key
  -- the vertical position controller
  have hactD : AC_PosControl.D_is_active r s.clock = true := by
    unfold AC_PosControl.D_is_active
    rw [hr_lud, hclk, hq.d_ticks]
    decide
  have hoffD : DOffZ r := ⟨hro1 ▸ hq.doff.1, hro2 ▸ hq.doff.2.1, hro3 ▸ hq.doff.2.2.1,
    hro4 ▸ hq.doff.2.2.2.1, hro5 ▸ hq.doff.2.2.2.2.1, hro6 ▸ hq.doff.2.2.2.2.2⟩
  have hterD : TerrZ r := ⟨hr_ter ▸ Z_lit0, hr_ter2 ▸ hq.terr.2.1, hr_ter3 ▸ hq.terr.2.2.1,
    hr_ter4 ▸ hq.terr.2.2.2⟩
  have hlD : DLim r := ⟨by rw [hr_dt]; exact CopterVertNear.dtF_val.1,
    by rw [hr_dt]; exact dtF_abs.trans (by norm_num), hrlim.up, hrlim.down, hrlim.amax,
    hrlim.amax_b, hrlim.jmax, hrlim.jmax_b⟩
  obtain ⟨s1, hO1, hT1, hs1, sD, hD, hsD, hpvD, hpaD, hppD, hptD, -, hvtD, hatD, hludD, hkimD,
      hlvzD, hDOD, hTZD, -, -, -, -, -, -, hatxD, hatyD, htgtD, -⟩ :=
    D_update_controller_hover C r s.ahrs.posInputs s.motors.toInputs
      (Copter.attInputs runParams s.attitude_control) s.clock hactD hp.lower hp.upper
      hp.motlim.hover hrlim.kimax hoffD hterD hlD
  rw [hD]
  dsimp only
  rw [hr_dt] at hpvD hpaD
  rw [hr_dt]
  -- the target and the feed-forward sums
  obtain ⟨htf, htv'⟩ := htgtD (by rw [hrpdz]; exact htpz.1)
  have htgt : Near64 (s1._pos_desired_ned_m.z + s1._pos_offset_ned_m.z +
      topostype s1._pos_terrain_d_m) (-1) 1e-6 := ⟨htf, by rw [htv', hrpdz]; exact htpz.2⟩
  have h1vd : s1._vel_desired_ned_ms = r._vel_desired_ned_ms := by rw [hs1]
  have h1ad : s1._accel_desired_ned_mss = r._accel_desired_ned_mss := by rw [hs1]
  have hvff : Z (s1._vel_desired_ned_ms.z + s1._vel_offset_ned_ms.z + s1._vel_terrain_d_ms) :=
    Z_add (Z_add (by rw [h1vd, hrvd]; exact htv.2.2) hO1.2.2.2.1) hT1.2.2.1
  have haff : Z (s1._accel_desired_ned_mss.z + s1._accel_offset_ned_mss.z +
      s1._accel_terrain_d_mss) :=
    Z_add (Z_add (by rw [h1ad, hrad]; exact hta.2.2) hO1.2.2.2.2.2) hT1.2.2.2
  -- the vertical tick, both PIDs in reset
  have hzs : Near64 r._pos_estimate_ned_m.z (-1) 1e-15 := by rw [hrpe]; exact hpez
  have hws : Z r._vel_estimate_ned_ms.z := by rw [hrve]; exact hq.vez
  have hN1 : NarrowSpec 1 := narrow_mono N (by norm_num)
  obtain ⟨hF', hVn, hVI⟩ := vert_tick0 hN1 r._p_pos_d_m r._pid_vel_d_m r._pid_accel_d_m m
    runParams.att s.attitude_control s.motors.toInputs
    (zs := r._pos_estimate_ned_m.z) (ws := r._vel_estimate_ned_ms.z)
    (fs := s.ahrs.posInputs.get_accel_ef.z) (scZ := s.ahrs.posInputs.get_control_gain_scaler_Z)
    false false (by rw [hr_pv]; exact hq.v_reset) (by rw [hr_pa]; exact hq.a_reset)
    (by rw [hr_pa]; exact hq.a_int) hp.m_F hp.m_Fv hp.m_T hp.m_cut hp.m_dt hzs hws hp.fs htgt
    (hr_pp ▸ hrlim.emin) (hr_pp ▸ hrlim.emin_le) (hr_pp ▸ hrlim.emax) (hr_pp ▸ hrlim.emax_ge)
    (hr_pp ▸ hrlim.D1) (hr_pp ▸ hrlim.D1_ge) lit_one hvff haff hp.cp hp.cr
    (L.cos_zero _ hp.att.thrust_angle) hp.motlim.hover
  have hP1t := (p1d_near0 hN1 r._p_pos_d_m htgt hzs (hr_pp ▸ hrlim.emin) (hr_pp ▸ hrlim.emin_le)
    (hr_pp ▸ hrlim.emax) (hr_pp ▸ hrlim.emax_ge) (hr_pp ▸ hrlim.D1) (hr_pp ▸ hrlim.D1_ge)).2.1
  have hP1fr := p1d_update_all_frame { P := AC_PosControl.POSCONTROL_D_POS_P } r._p_pos_d_m
    (s1._pos_desired_ned_m.z + s1._pos_offset_ned_m.z + topostype s1._pos_terrain_d_m)
    r._pos_estimate_ned_m.z
  generalize AC_P_1D.update_all { P := AC_PosControl.POSCONTROL_D_POS_P } r._p_pos_d_m
    (s1._pos_desired_ned_m.z + s1._pos_offset_ned_m.z + topostype s1._pos_terrain_d_m)
    r._pos_estimate_ned_m.z = P1 at *
  generalize AC_PID_Basic.update_all CopterVertNear.pv r._pid_vel_d_m _ _ dtF false false = rv at *
  generalize AC_PID.update_all CopterVertNear.pa r._pid_accel_d_m _ _ dtF false = ra at *
  generalize hST : AC_AttitudeControl_Multi.set_throttle_out runParams.att s.attitude_control
    s.motors.toInputs s.ahrs.cos_pitch s.ahrs.cos_roll _ true
    AC_PosControl.POSCONTROL_THROTTLE_CUTOFF_FREQ_HZ = ST at *
  obtain ⟨att2, m2⟩ := ST
  obtain ⟨hA2, hM2⟩ := set_throttle_out_frame' hST
  dsimp only at hVI ⊢
  -- the attitude controller
  have h2dt : att2._dt_s = dtF := by rw [hA2]; exact hp.att_dt
  have h2P : att2._angle_P_scale = AC_AttitudeControl.VECTORF_111 := by rw [hA2]; exact hp.att.angP
  have h2y : att2._rate_y_tc.IsFinite := by rw [hA2]; exact hp.ytc
  have h2t : IdQ att2._attitude_target := by rw [hA2]; exact hp.att.target
  have h2v : ZV att2._ang_vel_target_rads := by rw [hA2]; exact hp.att.ang_vel
  have h2a : ZV att2._ang_accel_target_rads := by rw [hA2]; exact hp.att.ang_accel
  have hx : Z (AC_PosControl.get_thrust_vector sD).x := by
    show Z sD._accel_target_ned_mss.x
    rw [hatxD]; exact hNE.1.1
  have hyv : Z (AC_PosControl.get_thrust_vector sD).y := by
    show Z sD._accel_target_ned_mss.y
    rw [hatyD]; exact hNE.1.2
  have hyawD : Z (AC_PosControl.get_yaw_rad sD) := by
    show Z sD._yaw_target_rad
    rw [hsD, hs1]
    show Z r._yaw_target_rad
    rw [hyaw1]
    exact hp.att.euler.2.2
  have hyawrD : Z (AC_PosControl.get_yaw_rate_rads sD) := by
    show Z sD._yaw_rate_target_rads
    rw [hsD, hs1]
    show Z r._yaw_rate_target_rads
    rw [hyaw2]
    exact Z_zero
  obtain ⟨hatt3, hb3, ht3, hta3, -, hv3, ha3, -, -, hff3⟩ :=
    multi_angle_and_rate_Z L C runParams.att runParams_cap runParams_rateMaxOK att2
      (runParams_angOK att2.toState h2dt h2P) (inputOK_run att2.toState h2dt h2y) h2t h2v h2a
      hp.quat hx hyv rfl
      { yaw_angle_rad := AC_PosControl.get_yaw_rad sD,
        yaw_rate_rads := AC_PosControl.get_yaw_rate_rads sD, heading_mode := .Angle_And_Rate }
      rfl hyawD hyawrD
  generalize AC_AttitudeControl_Multi.input_thrust_vector_heading runParams.att att2
    s.ahrs.quat_body_to_ned (AC_PosControl.get_thrust_vector sD) _ = att3 at *
  -- field facts of the new position controller
  have dNE : sD._last_update_ne_ticks = r._last_update_ne_ticks := by rw [hsD, hs1]
  have dPN : sD._pid_vel_ne_m = r._pid_vel_ne_m := by rw [hsD, hs1]
  have dNS : sD._ne_control_scale_factor = r._ne_control_scale_factor := by rw [hsD, hs1]
  have dVD : sD._vel_desired_ned_ms = r._vel_desired_ned_ms := by rw [hsD, hs1]
  have dOff : OffZ sD := by rw [hsD, hs1]; exact hNE.2.1
  have dLim : FinV2 sD._limit_vector_ned.xy := by rw [hsD, hs1]; exact hrl
  have dAm : sD._accel_max_d_mss = r._accel_max_d_mss := by rw [hsD, hs1]
  have dKey : pscKey sD = pscKey r := by
    unfold pscKey
    rw [hppD, hP1fr, hkimD, hsD, hs1]
  have hm2F : m2._throttle_filter_value = s.motors._throttle_filter_value := by rw [hM2]
  have hm2H : m2._throttle_hover = s.motors._throttle_hover := by rw [hM2]
  -- the new state
  refine ⟨fun f => ?_, ⟨hnav', hno' ▸ hox, hno' ▸ hoy, hno' ▸ hoz, hnd', hnr', ?_⟩, rfl, rfl, rfl,
    rfl, rfl, dAm.trans hr_amax⟩
  · have hHf0 : (0 : ℝ) ≤ Hf := by
      rw [show Hf = 7455795 / 16777216 from CopterVertNear.Hf_eq]; norm_num
    have hHf1 : Hf ≤ 1 := by rw [show Hf = 7455795 / 16777216 from CopterVertNear.Hf_eq]; norm_num
    have hpv := CopterVertNear.plant_vert (0 - 1) 0 f s.actuators hHf0 hHf1 (fun i => (hp.act i).2)
    have hFF : s.motors._throttle_filter_value.toReal = Hf := by rw [hp.F_eq]; exact hF'
    exact {
      plant := ⟨0, 0 - CopterVert.k * CopterVert.h *
          ((AP_MotorsMulticopter.update_throttle_filter m)._throttle_filter_value.toReal - 4 / 9),
        by
          rw [hpv]
          show _ = vstate _ _ (-(CopterVert.k * m2._throttle_filter_value.toReal))
          rw [hm2F, hFF, hF']
          congr 1; ring,
        by
          show CopterVert.V (vx _ _ sD._pid_vel_d_m._error sD._pid_accel_d_m._error
            sD._pid_accel_d_m._integrator m2._throttle_filter_value) ≤ 1 / 10
          rw [hpvD, hpaD, hm2F, hp.F_eq]; exact hVn⟩
      vinv := by
        show VInv sD._pid_vel_d_m sD._pid_accel_d_m _
        rw [hpvD, hpaD]
        exact vinv_congr hVI (hm2F.trans hp.F_eq) rfl rfl
      d_ticks := hludD
      ne_ticks := dNE.trans hrt
      motlim := MotLim.congr hp.motlim rfl rfl rfl rfl rfl hm2H
      boost := hp.boost
      psclim := PscLim.congr hrlim dKey
      vel_desired := by rw [dVD, hrvd]; exact htv
      doff := hDOD
      terr := hTZD
      off := dOff
      pid_ne := by rw [dPN]; exact hNE.2.2.1
      lim := dLim
      nescale := by rw [dNS, hrs]; exact lit_one.1
      pos_target := by rw [hptD, hP1t]; exact ⟨htgt.1, htgt.2.trans (by norm_num)⟩
      target := ht3
      ang_vel := hv3
      ang_accel := ha3
      body := hb3
      sysid := by rw [hatt3, hA2]; exact hp.att.sysid
      act_sysid := by rw [hatt3, hA2]; exact hp.att.act_sysid
      rate_roll := by rw [hatt3, hA2]; exact hp.att.rate_roll
      rate_pitch := by rw [hatt3, hA2]; exact hp.att.rate_pitch
      rate_yaw := by rw [hatt3, hA2]; exact hp.att.rate_yaw
      pd := by rw [hatt3, hA2]; exact hp.att.pd
      isc := by rw [hatt3, hA2]; exact hp.att.isc
      ff := by rw [hff3]; exact lit_one.1
      thrust_angle := hta3
      ytc := by rw [hatt3, hA2]; exact hp.ytc }
  · rw [hnl']
    show UInt32.ofNat (s.scheduler.micros / 1000) = 2
    rw [hp.micros]; rfl

end Contracts.CopterHover
