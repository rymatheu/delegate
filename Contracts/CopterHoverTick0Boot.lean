import Contracts.CopterHoverTick1
import Contracts.CopterHoverMotorInit
import Contracts.CopterHoverVert0

/-!
# Tick 0 of the hover run: the harness takeover and the common prefix

The first tick of the closed-loop hover run starts from the boot state `Copter.State.init
runParams` and the sample of `phys0`. This file covers the part of that tick before the switch
into Auto:

* `t0_sample`: the sample of `phys0` is `t0smp zP fs`, level, at rest, with the position reading
  `zP = senseP (-1)` and the specific force reading `fs`;
* `t0_takeover`: `Copter.takeover` relaxes the attitude controller to the identity attitude (the
  Euler-angle target is a zero by `LibmZero32`, the rate targets and rate PIDs are zero) and, with
  `run.start_hover`, stores the hover throttle `MOT_THST_HOVER` in the attitude controller and in
  the motors, whose throttle filter output is set to the stored throttle. The facts are collected
  in `AttT0` (attitude controller) and `MotT0` (motors);
* `t0_prefix`: the common prefix of the loop (`scheduler_loop` on the first tick, so the loop time
  is `1 / SCHED_LOOP_RATE = dtF`, `ins_update`, `run_rate_controller_main`, `motors_output_main`,
  `read_AHRS`, `read_inertia`) gives a state `Boot6`: the position controller is the boot one with
  the loop time and the estimates of the sample, the throttle filter keeps its value `Hf` exactly
  (the filter input equals its output), the four actuators have the value `Hf`, and the attitude
  controller keeps the facts of `AttT0` with the loop time `dtF`.

Hypotheses: `LibmZero32`, `LibmCos32` (the boot motor factors are finite).
-/

namespace Contracts.CopterHover

open AP_Math Contracts.CopterZero
open Contracts.CopterVertNear (Near32 Near64 NarrowSpec dtF)

/-! ## The sample of `phys0` -/

/-- A level sample at rest on the vertical through the waypoint: position reading `zP`,
specific force reading `fs`. -/
def t0smp (zP : Float) (fs : Float32) : Copter.AHRS.Sample :=
  { pos := ⟨0, 0, zP⟩, vel := ⟨0, 0, 0⟩, accel_ef := ⟨0, 0, fs⟩, quat := ⟨1, 0, 0, 0⟩,
    gyro := ⟨0, 0, 0⟩, dt_us := CopterPlant.dtUs }

/-- The sample of `phys0` under ports that send `0` to `+0` and `1` to `1`. -/
theorem t0_sample {sense32 : ℝ → Float32} {senseP : ℝ → Float}
    (S : CopterPlant.CopterSense sense32 senseP) :
    CopterPlant.sample sense32 senseP phys0 =
      t0smp (senseP (-1)) (sense32 (-(QuadPlant.thrust2weight * CopterPlant.gravity * Hf))) := by
  rw [phys0, CopterPlant.sample_vstate S.f32.zero S.f32.one S.pos.zero, S.f32.zero]
  rfl

/-! ## The takeover -/

/-- The boot state of the run. -/
abbrev t0S0 : Copter.State := Copter.State.init runParams

/-- The attitude controller after `relax_attitude_controllers` at boot, at the identity
attitude. -/
abbrev t0_att1 : AC_AttitudeControl_Multi.State :=
  AC_AttitudeControl_Multi.relax_attitude_controllers t0S0.attitude_control ⟨1, 0, 0, 0⟩

/-- The attitude-controller facts of the tick-0 state: identity target, zero Euler-angle target,
zero target and body rates, zero rate PIDs and system-identification offsets, unit scales, finite
feed-forward scalar, zero thrust angle, and the hover throttle stored by the takeover. -/
structure AttT0 (a : AC_AttitudeControl_Multi.State) : Prop where
  target : IdQ a._attitude_target
  euler : ZV a._euler_angle_target_rad
  ang_vel : ZV a._ang_vel_target_rads
  ang_accel : ZV a._ang_accel_target_rads
  body : ZV a._ang_vel_body_rads
  sysid : ZV a._sysid_ang_vel_body_rads
  act_sysid : ZV a._actuator_sysid
  rate_roll : ZPID a._pid_rate_roll
  rate_pitch : ZPID a._pid_rate_pitch
  rate_yaw : ZPID a._pid_rate_yaw
  pd : a._pd_scale = AC_AttitudeControl.VECTORF_111
  isc : a._i_scale = AC_AttitudeControl.VECTORF_111
  angP : a._angle_P_scale = AC_AttitudeControl.VECTORF_111
  ff : a._feedforward_scalar.IsFinite
  thrust_angle : Z a._thrust_angle_rad
  thr : a._throttle_in = CopterVertNear.hoverF

/-- The motors facts of the tick-0 state: the constant fields of `MotLim`, a zero boost ratio,
zero roll, pitch and yaw inputs, the stored throttle of value `Hf` equal to the throttle filter
output, the `2 Hz` filter cutoff. -/
structure MotT0 (m : AP_MotorsMatrix.State) : Prop where
  motlim : MotLim m
  boost : Z m._thrust_boost_ratio
  roll_in : Z m._roll_in
  roll_ff : Z m._roll_in_ff
  pitch_in : Z m._pitch_in
  pitch_ff : Z m._pitch_in_ff
  yaw_in : Z m._yaw_in
  yaw_ff : Z m._yaw_in_ff
  thr_fin : m._throttle_in.IsFinite
  thr_val : m._throttle_in.toReal = Hf
  filt : m._throttle_filter_value = m._throttle_in
  cutoff : m._throttle_filter_cutoff = AC_PosControl.POSCONTROL_THROTTLE_CUTOFF_FREQ_HZ

/-- The value of `MOT_THST_HOVER` is `Hf`. -/
theorem t0_hoverF_val : CopterVertNear.hoverF.toReal = Hf := by
  have := CopterVertNear.near_H.2
  rw [abs_nonpos_iff, sub_eq_zero] at this
  exact this

/-- `relax_attitude_controllers` at boot, at the identity attitude. -/
theorem t0_att1_facts (L : LibmZero32) :
    IdQ t0_att1._attitude_target ∧ ZV t0_att1._euler_angle_target_rad ∧
    ZV t0_att1._ang_vel_target_rads ∧ ZV t0_att1._ang_accel_target_rads ∧
    ZV t0_att1._ang_vel_body_rads ∧ ZV t0_att1._sysid_ang_vel_body_rads ∧
    ZV t0_att1._actuator_sysid ∧ ZPID t0_att1._pid_rate_roll ∧ ZPID t0_att1._pid_rate_pitch ∧
    ZPID t0_att1._pid_rate_yaw ∧ t0_att1._pd_scale = AC_AttitudeControl.VECTORF_111 ∧
    t0_att1._i_scale = AC_AttitudeControl.VECTORF_111 ∧
    t0_att1._angle_P_scale = AC_AttitudeControl.VECTORF_111 ∧
    t0_att1._feedforward_scalar = 1.0 ∧ Z t0_att1._thrust_angle_rad := by
  have hq : IdQ (⟨1, 0, 0, 0⟩ : Quaternion) := ⟨One_one, Z_zero, Z_zero, Z_zero⟩
  refine ⟨hq, to_euler_vec_Id L hq, ZV_zero_lit, ZV_zero_lit, ZV_zero_lit, ZV_zero_lit, ZV_zero_lit,
    ?_, ?_, ?_, rfl, rfl, rfl, rfl, Z_lit0⟩ <;>
    exact ⟨Z_lit0, Z_lit0, Z_lit0, Z_lit0, Z_lit0⟩

/-- `takeover` as a state update: the attitude controller and the motors' inputs from
`set_throttle_out(hover)` on the relaxed attitude controller, with the throttle filter output set
to the stored throttle. -/
theorem t0_takeover_eq (smp : Copter.AHRS.Sample) (hq : smp.quat = ⟨1, 0, 0, 0⟩) :
    Copter.takeover runParams t0S0 smp =
      { t0S0 with
        attitude_control := (AC_AttitudeControl_Multi.set_throttle_out runParams.att t0_att1
          t0S0.motors.toInputs (Copter.AHRS.update smp).cos_pitch (Copter.AHRS.update smp).cos_roll
          (AP_Motors.get_throttle_hover t0S0.motors.toInputs) true
          AC_PosControl.POSCONTROL_THROTTLE_CUTOFF_FREQ_HZ).1
        motors := { t0S0.motors with toInputs :=
          { (AC_AttitudeControl_Multi.set_throttle_out runParams.att t0_att1
          t0S0.motors.toInputs (Copter.AHRS.update smp).cos_pitch (Copter.AHRS.update smp).cos_roll
          (AP_Motors.get_throttle_hover t0S0.motors.toInputs) true
          AC_PosControl.POSCONTROL_THROTTLE_CUTOFF_FREQ_HZ).2 with
            _throttle_filter_value := (AC_AttitudeControl_Multi.set_throttle_out runParams.att
          t0_att1 t0S0.motors.toInputs (Copter.AHRS.update smp).cos_pitch
          (Copter.AHRS.update smp).cos_roll (AP_Motors.get_throttle_hover t0S0.motors.toInputs) true
          AC_PosControl.POSCONTROL_THROTTLE_CUTOFF_FREQ_HZ).2._throttle_in } } } := by
  unfold Copter.takeover
  simp only [show runParams.start_hover = true from rfl, Bool.not_true, Bool.false_eq_true,
    if_false, Copter.AHRS.update, hq]

/-- **The takeover at boot.** On a level sample, `takeover` changes only the attitude controller
and the motors, which then satisfy `AttT0` and `MotT0`. -/
theorem t0_takeover (L : LibmZero32) (LC : LibmCos32) (smp : Copter.AHRS.Sample)
    (hq : smp.quat = ⟨1, 0, 0, 0⟩) :
    ∃ (a : AC_AttitudeControl_Multi.State) (m : AP_MotorsMatrix.State),
      Copter.takeover runParams t0S0 smp = { t0S0 with attitude_control := a, motors := m } ∧
      AttT0 a ∧ MotT0 m := by
  obtain ⟨vcp, vcr, -, -, -, -, -, -, -, -, -, -, -, -, -⟩ := ahrs_update_level L smp hq
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15⟩ := t0_att1_facts L
  obtain ⟨f1, f2, f3, f4, f5, f6, f7⟩ := init_factors LC
  have hhov : AP_Motors.get_throttle_hover t0S0.motors.toInputs = CopterVertNear.hoverF :=
    CopterVertNear.throttle_hover_eq _ f7
  rw [t0_takeover_eq smp hq]
  generalize hST : AC_AttitudeControl_Multi.set_throttle_out runParams.att t0_att1
    t0S0.motors.toInputs (Copter.AHRS.update smp).cos_pitch (Copter.AHRS.update smp).cos_roll
    (AP_Motors.get_throttle_hover t0S0.motors.toInputs) true
    AC_PosControl.POSCONTROL_THROTTLE_CUTOFF_FREQ_HZ = ST
  have hval := CopterVertNear.set_throttle_out_val runParams.att t0_att1 t0S0.motors.toInputs
    (c := AC_PosControl.POSCONTROL_THROTTLE_CUTOFF_FREQ_HZ) vcp vcr (L.cos_zero _ a15)
    (thr := AP_Motors.get_throttle_hover t0S0.motors.toInputs)
    (by rw [hhov]; exact CopterVertNear.near_H.1)
  have hthr : (AC_AttitudeControl_Multi.set_throttle_out runParams.att t0_att1
      t0S0.motors.toInputs (Copter.AHRS.update smp).cos_pitch (Copter.AHRS.update smp).cos_roll
      (AP_Motors.get_throttle_hover t0S0.motors.toInputs) true
      AC_PosControl.POSCONTROL_THROTTLE_CUTOFF_FREQ_HZ).1._throttle_in =
      AP_Motors.get_throttle_hover t0S0.motors.toInputs := by
    simp only [AC_AttitudeControl_Multi.set_throttle_out,
      AC_AttitudeControl_Multi.update_althold_lean_angle_max,
      AC_AttitudeControl_Multi.get_throttle_boosted]
    split_ifs <;> rfl
  rw [hST] at hval hthr
  obtain ⟨att, mo⟩ := ST
  obtain ⟨hA, hM⟩ := set_throttle_out_frame' hST
  simp only at hval hthr
  obtain ⟨hv1, hv2, hv3⟩ := hval
  refine ⟨att, _, rfl, ?_, ?_⟩
  · rw [hA]
    exact ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, by rw [a14]; exact lit_one.1,
      a15, hthr.trans hhov⟩
  · have hm0 : ∀ i : Fin 4, CopterZero.One t0S0.motors._throttle_factor[i] := f5
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -⟩ :=
      init_fields
    obtain ⟨z1, z2, z3, z4, z5, z6, -, -, -, z10, -⟩ := init_Z
    rw [hM] at hv1 hv2 hv3 ⊢
    exact ⟨⟨f1, f2, f3, f4, hm0, f7⟩, z10, z1, z2, z3, z4, z5, z6, hv1,
      by rw [hv2, hhov]; exact t0_hoverF_val, rfl, hv3⟩

/-! ## The common prefix -/

/-- The state after the common prefix of tick 0: the motors facts the first `wp_run` needs, with
`m` the motors object the throttle filter update of the tick started from. -/
structure MotBoot6 (mo : AP_MotorsMatrix.State) (m : AP_MotorsMulticopter.State) : Prop where
  m_dt : m._dt_s = dtF
  m_F : m._throttle_filter_value.IsFinite
  m_Fv : m._throttle_filter_value.toReal = Hf
  m_T : m._throttle_in = m._throttle_filter_value
  m_cut : m._throttle_filter_cutoff = AC_PosControl.POSCONTROL_THROTTLE_CUTOFF_FREQ_HZ
  F_eq : mo._throttle_filter_value =
    (AP_MotorsMulticopter.update_throttle_filter m)._throttle_filter_value
  F_fin : mo._throttle_filter_value.IsFinite
  F_val : mo._throttle_filter_value.toReal = Hf
  T_eq : mo._throttle_in = m._throttle_in
  cut : mo._throttle_filter_cutoff = m._throttle_filter_cutoff
  act : ∀ i : Fin 4, (mo._actuator[i]).IsFinite ∧ (mo._actuator[i]).toReal = Hf
  lower : mo.limit.throttle_lower = false
  upper : mo.limit.throttle_upper = false
  motlim : MotLim mo
  boost : Z mo._thrust_boost_ratio

/-- The throttle filter keeps its value when its input equals its output. -/
theorem t0_filter_keep (m : AP_MotorsMulticopter.State)
    (hc : m._throttle_filter_cutoff = AC_PosControl.POSCONTROL_THROTTLE_CUTOFF_FREQ_HZ)
    (hdt : m._dt_s = dtF) (hF : m._throttle_filter_value.IsFinite)
    (hFv : m._throttle_filter_value.toReal = Hf) (hT : m._throttle_in = m._throttle_filter_value) :
    (AP_MotorsMulticopter.update_throttle_filter m)._throttle_filter_value.IsFinite ∧
      (AP_MotorsMulticopter.update_throttle_filter m)._throttle_filter_value.toReal = Hf := by
  have hIs := Istar_val
  have hIsb : |CopterVertNear.Istar| ≤ 1 / 20000 := by rw [hIs]; norm_num [abs_le]
  have hφv : m._throttle_filter_value.toReal = 4 / 9 + CopterVertNear.Istar := by
    rw [hFv, CopterVertNear.Istar]; ring
  have hTn : Near32 m._throttle_in (4 / 9 + CopterVertNear.Istar) 3.7e-8 := by
    rw [hT]; exact (Near32.of_val hF hφv).mono (by norm_num)
  have hTF := CopterVertNear.throttle_filter_near m hc hdt (Near32.of_val hF hφv) hTn
    (hIsb.trans (by norm_num)) (hIsb.trans (by norm_num))
  rw [hTF.1]
  have hZ0 : Z (m._throttle_in - m._throttle_filter_value) := by
    rw [hT]; exact sub_exact hF hF Z_zero.1 (by rw [sub_self, Z_zero.2])
  have hZ1 := CopterVertNear.zero_mul_Z CopterVertNear.near_am.1 hZ0
  have := CopterVertNear.add_zero_val hF hZ1
  exact ⟨this.1, this.2.trans hFv⟩

set_option maxHeartbeats 1000000 in
/-- **The common prefix of tick 0.** From a state with the takeover facts `AttT0`, `MotT0`, on a
sample with zero gyro and period `2500 µs`, the prefix (`scheduler_loop`, `ins_update`,
`run_rate_controller_main`, `motors_output_main`, `read_AHRS`, `read_inertia`) changes only the
scheduler, the INS gyro, the AHRS, the attitude controller (which keeps `AttT0`, with the loop
time `dtF`, whatever the tick count), the position controller (the loop time and the estimates of
the sample), the motors (`MotBoot6`) and the actuators. -/
theorem t0_prefix (st : Copter.State) (smp : Copter.AHRS.Sample)
    (hg : smp.gyro = ⟨0, 0, 0⟩) (hdt : smp.dt_us = 2500)
    (hA : AttT0 st.attitude_control) (hM : MotT0 st.motors) :
    ∃ (a : AC_AttitudeControl_Multi.State) (mo : AP_MotorsMatrix.State)
      (m : AP_MotorsMulticopter.State),
      prefixState runParams st smp = { st with
        scheduler := (Copter.scheduler_loop st smp.dt_us).scheduler
        ins_gyro := smp.gyro
        ahrs := Copter.AHRS.update smp
        attitude_control := a
        pos_control := { st.pos_control with
          _dt_s := dtF, _pos_estimate_ned_m := smp.pos, _vel_estimate_ned_ms := smp.vel }
        motors := mo
        actuators := mo._actuator } ∧
      AttT0 a ∧ a._dt_s = dtF ∧ MotBoot6 mo m := by
  set s2 := Copter.ins_update (Copter.scheduler_loop st smp.dt_us) smp with hs2
  have h2dt : s2.scheduler.last_loop_time_s = dtF := by
    show (Copter.scheduler_loop st smp.dt_us).scheduler.last_loop_time_s = dtF
    rw [hdt]; exact scheduler_loop_dt st
  have h2g : ZV s2.ins_gyro := by
    show ZV smp.gyro
    rw [hg]; exact ZV_zero_lit
  -- the rate controller
  obtain ⟨mix, pr, pp, py, r1, r2, r3, f1, f2, f3, hpr, hpp, hpy, hr1, hr2, hr3, hf1, hf2, hf3,
      e3⟩ :=
    run_rate_controller_main_Z s2 h2dt h2g hA.body hA.sysid hA.act_sysid hA.rate_roll
      hA.rate_pitch hA.rate_yaw hA.pd hA.isc hA.ff
  set s3 := Copter.run_rate_controller_main runParams s2 with hs3
  have hm3 : s3.motors = { st.motors with
      _dt_s := dtF, _roll_in := r1, _pitch_in := r2, _yaw_in := r3, _roll_in_ff := f1,
      _pitch_in_ff := f2, _yaw_in_ff := f3 } := by rw [e3]; rfl
  -- the throttle filter of this tick
  set m3 := s3.motors.toState with hm3def
  have m3F : m3._throttle_filter_value = st.motors._throttle_filter_value := by rw [hm3def, hm3]
  have m3c : m3._throttle_filter_cutoff = st.motors._throttle_filter_cutoff := by rw [hm3def, hm3]
  have m3t : m3._throttle_in = st.motors._throttle_in := by rw [hm3def, hm3]
  have m3dt : m3._dt_s = dtF := by rw [hm3def, hm3]
  have hmF : m3._throttle_filter_value.IsFinite := by rw [m3F, hM.filt]; exact hM.thr_fin
  have hmFv : m3._throttle_filter_value.toReal = Hf := by rw [m3F, hM.filt]; exact hM.thr_val
  have hmT : m3._throttle_in = m3._throttle_filter_value := by rw [m3F, m3t, hM.filt]
  have hmc : m3._throttle_filter_cutoff = AC_PosControl.POSCONTROL_THROTTLE_CUTOFF_FREQ_HZ := by
    rw [m3c]; exact hM.cutoff
  obtain ⟨hF1, hF2⟩ := t0_filter_keep m3 hmc m3dt hmF hmFv hmT
  have hHf0 : 0 < Hf := by rw [show Hf = 7455795 / 16777216 from CopterVertNear.Hf_eq]; norm_num
  have hHf1 : Hf < 1 := by rw [show Hf = 7455795 / 16777216 from CopterVertNear.Hf_eq]; norm_num
  -- the motors output
  obtain ⟨⟨m4, e4⟩, hF4, hti4, hcut4, hhov4, havg4, hlo4, hup4, hen4, hrf4, hpf4, hyf4, htf4, hb4,
      hdt4, -, -, -, -, -, -, hact4⟩ :=
    motors_output_main_hover s3 (by rw [hm3]; exact hM.motlim.enabled)
      (by rw [hm3]; exact hM.motlim.roll) (by rw [hm3]; exact hM.motlim.pitch)
      (by rw [hm3]; exact hM.motlim.yaw) (by rw [hm3]; exact hM.motlim.thr)
      (by rw [hm3]; exact hr1) (by rw [hm3]; exact hf1) (by rw [hm3]; exact hr2)
      (by rw [hm3]; exact hf2) (by rw [hm3]; exact hr3) (by rw [hm3]; exact hf3)
      (by rw [hm3]; exact hM.boost) (by rw [hm3]) hF1 (by rw [hF2]; exact hHf0)
      (by rw [hF2]; exact hHf1)
  set s4 := Copter.motors_output_main runParams s3 with hs4
  have e6 : prefixState runParams st smp = { s4 with
      ahrs := Copter.AHRS.update smp
      pos_control := { s4.pos_control with
        _pos_estimate_ned_m := smp.pos
        _vel_estimate_ned_ms := smp.vel } } := by
    show Copter.read_inertia (Copter.read_AHRS s4 smp) = _
    rw [read_inertia_eq]
    rfl
  refine ⟨{ st.attitude_control with
      _dt_s := dtF, _rate_gyro_rads := s2.ins_gyro, _throttle_rpy_mix := mix,
      _pid_rate_roll := pr, _pid_rate_pitch := pp, _pid_rate_yaw := py,
      _pd_scale_used := st.attitude_control._pd_scale,
      _i_scale_used := st.attitude_control._i_scale,
      _angle_P_scale_used := st.attitude_control._angle_P_scale,
      _sysid_ang_vel_body_rads := ⟨0, 0, 0⟩, _actuator_sysid := ⟨0, 0, 0⟩,
      _pd_scale := AC_AttitudeControl.VECTORF_111, _i_scale := AC_AttitudeControl.VECTORF_111,
      _angle_P_scale := AC_AttitudeControl.VECTORF_111 }, m4, m3, ?_, ?_, rfl, ?_⟩
  · rw [e6, e4, e3]; rfl
  · exact ⟨hA.target, hA.euler, hA.ang_vel, hA.ang_accel, hA.body, ZV_zero_lit, ZV_zero_lit, hpr,
      hpp, hpy, rfl, rfl, rfl, hA.ff, hA.thrust_angle, hA.thr⟩
  · have hm4 : s4.motors = m4 := by rw [e4]
    rw [hm4] at hF4 hti4 hcut4 hhov4 hlo4 hup4 hen4 hrf4 hpf4 hyf4 htf4 hb4
    have hact : s4.actuators = m4._actuator := by rw [e4]
    rw [hact] at hact4
    exact {
      m_dt := m3dt, m_F := hmF, m_Fv := hmFv, m_T := hmT, m_cut := hmc
      F_eq := hF4
      F_fin := by rw [hF4]; exact hF1
      F_val := by rw [hF4]; exact hF2
      T_eq := by rw [hti4, hm3]; exact m3t.symm
      cut := by rw [hcut4, hm3]; exact m3c.symm
      act := fun i => ⟨(hact4 i).1, (hact4 i).2.trans hF2⟩
      lower := hlo4
      upper := hup4
      motlim := MotLim.congr hM.motlim (hen4.trans (by rw [hm3])) (hrf4.trans (by rw [hm3]))
        (hpf4.trans (by rw [hm3])) (hyf4.trans (by rw [hm3])) (htf4.trans (by rw [hm3]))
        (hhov4.trans (by rw [hm3]))
      boost := hb4 }

end Contracts.CopterHover
