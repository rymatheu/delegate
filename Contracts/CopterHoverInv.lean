import Contracts.CopterHoverNav
import Contracts.CopterHoverDctl
import Contracts.CopterHoverNE
import Contracts.CopterHoverMotors
import Contracts.CopterHoverAtt
import Contracts.CopterVertNearTick

/-!
# The steady hover tick preserves the steady invariant

The assembly step of the closed-loop hover theorem: one steady tick of the controller
(`CopterLift.tick runParams ⟨st, true⟩`, i.e. `Copter.loop` on a state already in Auto) closed with
the Crazyflie plant (`CopterPlant.sample`, `CopterPlant.dyn`) maps the steady invariant to itself.
The first ticks (boot, mission start, mission exit into LOITER) are not treated here.

**The invariant.** `InvCore st phys` holds everything except the mode and the navigator, so that
it can serve the first ticks too:

* the plant is `vstate (ζ - 1) w (-k F)`, on the vertical through the waypoint, level, at rest
  horizontally, with the specific force of the stored throttle filter output `F`, and the exact
  vertical values `vx ζ w Ev Ea I F` lie in the sublevel set `V ≤ 1/10` of `CopterVert`;
* the vertical floats satisfy `CopterVertNear.VInv`;
* both update stamps of the position controller are the current tick (the scheduler increments
  it first, so both controllers are active, in `uint32_t` arithmetic: no condition on the tick
  count, which may wrap);
* the attitude controller is at the hover fixed point (identity target, zero target and body rates,
  rate PIDs at zero, unit PD and I scales, zero system-identification offsets, zero thrust angle,
  finite feed-forward scalar and yaw time constant);
* the horizontal controller, the six offset vectors and the terrain terms are at zero, the desired
  velocity is a zero vector, the position target is within `1 cm` of `-1`;
* the limits read by the tick are those of `MotLim` and `PscLim` (finiteness and the few bounds the
  building blocks ask for, not their concrete values).

`InvSteady` adds `NavSteady` and the mode facts `ModeSteady` (in Auto, submode `LOITER`, mission
started and complete, AutoYaw `HOLD`).

**The proof**, stage by stage, never unfolding the mixer or the whole loop:

1. `prefix_run`: the common prefix `prefixState` (`scheduler_loop`, `ins_update`,
   `run_rate_controller_main`, `motors_output_main`, `read_AHRS`, `read_inertia`) on a state with
   `InvCore`, at the sample of the plant (`sample_vstate`), gives a state with `PreRun`: what
   `wp_run` needs, stated without the navigator or the mode (`run_rate_controller_main_Z`,
   `CopterVertNear.motors_tick` for `0 < F' < 1`, `motors_output_main_hover`,
   `ahrs_update_level`, `CopterVertNear.sense_near`). The loop time is `dtF` whatever the tick
   count (`scheduler_loop_dt`).
2. `wp_run_steady`: `wp_run` on a `PreRun` state with the steady navigator and AutoYaw `HOLD`
   (`wp_run_hold`): the navigator (`update_wpnav_steady`), the horizontal controller
   (`NE_update_controller_hover_run`), the vertical controller (`D_update_controller_hover`), the
   vertical tick (`CopterVertNear.vert_tick`, `vert_tick_V`, `p1d_near`), `set_throttle_out`
   (`set_throttle_out_frame`) and the thrust-vector entry (`multi_rate_only_Z`), followed by the
   plant (`CopterVertNear.plant_vert`), re-establish `InvCore` and `NavSteady`.
3. `run_steady`, `loop_prefix`, `loop_steady`, `tick_steady`: the mission is complete, so
   `ModeAuto.run` is `wp_run`; `Copter.loop` is the prefix followed by `ModeAuto.run`; the harness
   step returns the new state and its actuators.
4. `InvCore.box`: the core invariant puts the plant in the hover box.

Hypotheses: `LibmZero32`, `ConvZero`, `NarrowSpec 2` (the navigator's terrain scaler narrows an
altitude error of a few centimeters; `vert_tick` needs only `NarrowSpec 1`, `narrow_mono`) and
`CopterSense`.
-/

open Float.Model UnpackedFloat AP_Math Contracts.CopterZero Contracts.CopterPlant
open Contracts.CopterVertNear (Near32 Near64 NarrowSpec dtF VInv vx hoverF)

namespace Contracts.CopterHover

/-! ## The invariant -/

/-- The constant fields of the motors object that the hover tick reads: the four motors enabled,
finite roll, pitch and yaw factors, throttle factors of value one, `MOT_THST_HOVER = 0.4444`. -/
structure MotLim (m : AP_MotorsMatrix.State) : Prop where
  enabled : m.motor_enabled = #v[true, true, true, true]
  roll : ∀ i : Fin 4, (m._roll_factor[i]).IsFinite
  pitch : ∀ i : Fin 4, (m._pitch_factor[i]).IsFinite
  yaw : ∀ i : Fin 4, (m._yaw_factor[i]).IsFinite
  thr : ∀ i : Fin 4, One m._throttle_factor[i]
  hover : m._throttle_hover = hoverF

/-- The constant limits of the position controller that the hover tick reads: the vertical
position error limits and `D1_max` at least `1 cm` away from zero, the RAM `PSC_D_ACC_IMAX` at
`0.8`, finite horizontal limits (jerk at most `10¹⁸`), finite vertical limits (acceleration at most
`10¹⁸`, jerk at most `10¹¹`). -/
structure PscLim (p : AC_PosControl.State) : Prop where
  emin : p._p_pos_d_m._error_min.IsFinite
  emin_le : p._p_pos_d_m._error_min.toReal ≤ -(1 / 100)
  emax : p._p_pos_d_m._error_max.IsFinite
  emax_ge : 1 / 100 ≤ p._p_pos_d_m._error_max.toReal
  D1 : p._p_pos_d_m._D1_max.IsFinite
  D1_ge : 1 / 100 ≤ p._p_pos_d_m._D1_max.toReal
  kimax : p._pid_accel_d_m_kimax = AC_PosControl.POSCONTROL_D_ACC_IMAX
  vmax_ne : p._vel_max_ne_ms.IsFinite
  amax_ne : p._accel_max_ne_mss.IsFinite
  jmax_ne : p._jerk_max_ne_msss.IsFinite
  jmax_ne_b : |p._jerk_max_ne_msss.toReal| ≤ 1e18
  up : p._vel_max_up_ms.IsFinite
  down : p._vel_max_down_ms.IsFinite
  amax : p._accel_max_d_mss.IsFinite
  amax_b : |p._accel_max_d_mss.toReal| ≤ 1e18
  jmax : p._jerk_max_d_msss.IsFinite
  jmax_b : |p._jerk_max_d_msss.toReal| ≤ 1e11

/-- **The core invariant** at the start of a tick after the first (everything except the mode and
the navigator). The plant is on the vertical through the waypoint, level, at rest horizontally,
with the specific force of the stored throttle filter output `F` and the exact vertical values in
the sublevel set `V ≤ 1/10`; the vertical floats satisfy `VInv`; the controllers' update stamps are
the current tick (the scheduler then increments it, so both controllers are active); the attitude
controller is at the hover fixed point (identity target, zero rates, rate PIDs at zero, unit scales,
zero thrust angle); the horizontal controller, the offsets and the terrain terms are at zero; the
position target has the value `-1` within `1 cm`; the limits are those of `MotLim`, `PscLim`. -/
structure InvCore (st : Copter.State) (phys : CState) : Prop where
  plant : ∃ ζ w : ℝ,
    phys = vstate (ζ - 1) w (-(CopterVert.k * st.motors._throttle_filter_value.toReal)) ∧
    CopterVert.V (vx ζ w st.pos_control._pid_vel_d_m._error st.pos_control._pid_accel_d_m._error
      st.pos_control._pid_accel_d_m._integrator st.motors._throttle_filter_value) ≤ 1 / 10
  vinv : VInv st.pos_control._pid_vel_d_m st.pos_control._pid_accel_d_m st.motors.toState
  d_ticks : st.pos_control._last_update_d_ticks = st.scheduler.ticks32
  ne_ticks : st.pos_control._last_update_ne_ticks = st.scheduler.ticks32
  -- motors
  motlim : MotLim st.motors
  boost : Z st.motors._thrust_boost_ratio
  -- position controller
  psclim : PscLim st.pos_control
  vel_desired : ZV st.pos_control._vel_desired_ned_ms
  doff : DOffZ st.pos_control
  terr : TerrZ st.pos_control
  off : OffZ st.pos_control
  pid_ne : ZPID2 st.pos_control._pid_vel_ne_m
  lim : FinV2 st.pos_control._limit_vector_ned.xy
  nescale : st.pos_control._ne_control_scale_factor.IsFinite
  pos_target : Near64 st.pos_control._pos_target_ned_m.z (-1) (1 / 100)
  -- attitude controller
  target : IdQ st.attitude_control._attitude_target
  ang_vel : ZV st.attitude_control._ang_vel_target_rads
  ang_accel : ZV st.attitude_control._ang_accel_target_rads
  body : ZV st.attitude_control._ang_vel_body_rads
  sysid : ZV st.attitude_control._sysid_ang_vel_body_rads
  act_sysid : ZV st.attitude_control._actuator_sysid
  rate_roll : ZPID st.attitude_control._pid_rate_roll
  rate_pitch : ZPID st.attitude_control._pid_rate_pitch
  rate_yaw : ZPID st.attitude_control._pid_rate_yaw
  pd : st.attitude_control._pd_scale = AC_AttitudeControl.VECTORF_111
  isc : st.attitude_control._i_scale = AC_AttitudeControl.VECTORF_111
  ff : st.attitude_control._feedforward_scalar.IsFinite
  thrust_angle : Z st.attitude_control._thrust_angle_rad
  ytc : st.attitude_control._rate_y_tc.IsFinite

/-- The mode facts of the steady LOITER state: in Auto, submode `LOITER`, the mission started and
complete (so `mission_update` does nothing and `ModeAuto.run` is `wp_run`), AutoYaw `HOLD`. -/
structure ModeSteady (st : Copter.State) : Prop where
  in_auto : st.in_auto = true
  submode : st.mode_auto._mode = .LOITER
  started : st.mode_auto.waiting_to_start = false
  complete : st.mode_auto.mission.state = .MISSION_COMPLETE
  yaw : st.auto_yaw._mode = .HOLD

/-- **The steady invariant**: the core invariant, the steady navigator and the mode facts. -/
def InvSteady (st : Copter.State) (phys : CState) : Prop :=
  InvCore st phys ∧ NavSteady st.wp_nav ∧ ModeSteady st

/-- **What `wp_run` needs**, on the state `s` reached by the common prefix of a tick
(`scheduler_loop`, `ins_update`, `run_rate_controller_main`, `motors_output_main`, `read_AHRS`,
`read_inertia`), with `m` the motors object the filter update of this tick started from and
`ζ`, `w` the plant's vertical state at the sample. Nothing here mentions the navigator or the
mode. -/
structure PreRun (s : Copter.State) (m : AP_MotorsMulticopter.State) (ζ w : ℝ) : Prop where
  -- the vertical floats at the start of the tick
  hV : CopterVert.V (vx ζ w s.pos_control._pid_vel_d_m._error s.pos_control._pid_accel_d_m._error
      s.pos_control._pid_accel_d_m._integrator m._throttle_filter_value) ≤ 1 / 10
  vinv : VInv s.pos_control._pid_vel_d_m s.pos_control._pid_accel_d_m m
  m_dt : m._dt_s = dtF
  -- the motors after `motors_output_main`
  F_eq : s.motors._throttle_filter_value =
    (AP_MotorsMulticopter.update_throttle_filter m)._throttle_filter_value
  F_pos : 0 < s.motors._throttle_filter_value.toReal
  F_lt : s.motors._throttle_filter_value.toReal < 1
  act : ∀ i : Fin 4, (s.actuators[i]).IsFinite ∧
    (s.actuators[i]).toReal = s.motors._throttle_filter_value.toReal
  lower : s.motors.limit.throttle_lower = false
  upper : s.motors.limit.throttle_upper = false
  motlim : MotLim s.motors
  boost : Z s.motors._thrust_boost_ratio
  -- the AHRS of the tick
  cp : One s.ahrs.cos_pitch
  cr : One s.ahrs.cos_roll
  quat : IdQ s.ahrs.quat_body_to_ned
  fs : Near32 s.ahrs.accel_ef.z (-(CopterVert.k * m._throttle_filter_value.toReal)) 6e-7
  -- the estimates
  pex : ZD s.pos_control._pos_estimate_ned_m.x
  pey : ZD s.pos_control._pos_estimate_ned_m.y
  pez : Near64 s.pos_control._pos_estimate_ned_m.z (ζ - 1) 1e-15
  vex : Z s.pos_control._vel_estimate_ned_ms.x
  vey : Z s.pos_control._vel_estimate_ned_ms.y
  vez : Near32 s.pos_control._vel_estimate_ned_ms.z w 6e-10
  -- the position controller
  psc_dt : s.pos_control._dt_s = dtF
  psclim : PscLim s.pos_control
  vel_desired : ZV s.pos_control._vel_desired_ned_ms
  doff : DOffZ s.pos_control
  terr : TerrZ s.pos_control
  off : OffZ s.pos_control
  pid_ne : ZPID2 s.pos_control._pid_vel_ne_m
  lim : FinV2 s.pos_control._limit_vector_ned.xy
  nescale : s.pos_control._ne_control_scale_factor.IsFinite
  pos_target : Near64 s.pos_control._pos_target_ned_m.z (-1) (1 / 100)
  d_active : AC_PosControl.D_is_active s.pos_control s.clock = true
  ne_active : AC_PosControl.NE_is_active s.pos_control s.clock = true
  -- the attitude controller
  att_dt : s.attitude_control._dt_s = dtF
  angP : s.attitude_control._angle_P_scale = AC_AttitudeControl.VECTORF_111
  target : IdQ s.attitude_control._attitude_target
  ang_vel : ZV s.attitude_control._ang_vel_target_rads
  ang_accel : ZV s.attitude_control._ang_accel_target_rads
  sysid : ZV s.attitude_control._sysid_ang_vel_body_rads
  act_sysid : ZV s.attitude_control._actuator_sysid
  rate_roll : ZPID s.attitude_control._pid_rate_roll
  rate_pitch : ZPID s.attitude_control._pid_rate_pitch
  rate_yaw : ZPID s.attitude_control._pid_rate_yaw
  pd : s.attitude_control._pd_scale = AC_AttitudeControl.VECTORF_111
  isc : s.attitude_control._i_scale = AC_AttitudeControl.VECTORF_111
  thrust_angle : Z s.attitude_control._thrust_angle_rad
  ytc : s.attitude_control._rate_y_tc.IsFinite

/-! ## Small facts -/

/-- `NarrowSpec` on a range implies it on a smaller one. -/
theorem narrow_mono {R R' : ℝ} (h : NarrowSpec R) (hR : R' ≤ R) : NarrowSpec R' :=
  ⟨fun x hx hb => h.err x hx (hb.trans hR)⟩

/-- `VInv` reads only three fields of the motors object. -/
theorem vinv_congr {sv : AC_PID_Basic.State} {sa : AC_PID.State} {m m' : AP_MotorsMulticopter.State}
    (h : VInv sv sa m) (e1 : m'._throttle_filter_value = m._throttle_filter_value)
    (e2 : m'._throttle_filter_cutoff = m._throttle_filter_cutoff)
    (e3 : m'._throttle_in = m._throttle_in) : VInv sv sa m' :=
  ⟨h.v_reset, h.v_err, h.v_der, h.v_der_b, h.a_reset, h.a_tgt, h.a_tgt_b, h.a_err, h.a_int, h.a_der,
    h.a_der_b, e1 ▸ h.F_fin, e2 ▸ h.cutoff, e3 ▸ h.throttle⟩

/-- `MotLim` reads only six fields. -/
theorem MotLim.congr {m m' : AP_MotorsMatrix.State} (h : MotLim m)
    (e1 : m'.motor_enabled = m.motor_enabled) (e2 : m'._roll_factor = m._roll_factor)
    (e3 : m'._pitch_factor = m._pitch_factor) (e4 : m'._yaw_factor = m._yaw_factor)
    (e5 : m'._throttle_factor = m._throttle_factor) (e6 : m'._throttle_hover = m._throttle_hover) :
    MotLim m' :=
  ⟨e1 ▸ h.enabled, e2 ▸ h.roll, e3 ▸ h.pitch, e4 ▸ h.yaw, e5 ▸ h.thr, e6 ▸ h.hover⟩

/-- The fields `PscLim` reads. -/
def pscKey (p : AC_PosControl.State) : List Float32 :=
  [p._p_pos_d_m._error_min, p._p_pos_d_m._error_max, p._p_pos_d_m._D1_max, p._pid_accel_d_m_kimax,
    p._vel_max_ne_ms, p._accel_max_ne_mss, p._jerk_max_ne_msss, p._vel_max_up_ms,
    p._vel_max_down_ms, p._accel_max_d_mss, p._jerk_max_d_msss]

/-- `PscLim` reads only the fields of `pscKey`. -/
theorem PscLim.congr {p q : AC_PosControl.State} (h : PscLim p) (e : pscKey q = pscKey p) :
    PscLim q := by
  simp only [pscKey, List.cons.injEq, and_true] at e
  obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11⟩ := e
  exact ⟨e1 ▸ h.emin, e1 ▸ h.emin_le, e2 ▸ h.emax, e2 ▸ h.emax_ge, e3 ▸ h.D1, e3 ▸ h.D1_ge,
    e4 ▸ h.kimax, e5 ▸ h.vmax_ne, e6 ▸ h.amax_ne, e7 ▸ h.jmax_ne, e7 ▸ h.jmax_ne_b, e8 ▸ h.up,
    e9 ▸ h.down, e10 ▸ h.amax, e10 ▸ h.amax_b, e11 ▸ h.jmax, e11 ▸ h.jmax_b⟩

/-- `AC_P_1D.update_all` writes only `_error`. -/
theorem p1d_update_all_frame (p : AC_P_1D.Params) (s : AC_P_1D.State) (t m : postype) :
    (AC_P_1D.update_all p s t m).1 = { s with _error := (AC_P_1D.update_all p s t m).fst._error } := by
  unfold AC_P_1D.update_all
  simp only [Id.run]
  split_ifs <;> rfl

/-- `set_throttle_out` writes only the attitude controller's `_throttle_in`,
`_althold_lean_angle_max_rad`, `_angle_boost`, and the motors' `_throttle_filter_cutoff` (to the
cutoff passed in), `_throttle_in`, `_throttle_avg_max`. -/
theorem set_throttle_out_frame (p : AC_AttitudeControl_Multi.Params)
    (s : AC_AttitudeControl_Multi.State) (m : AP_Motors.Inputs) (cp cr thr : Float32) (b : Bool)
    (c : Float32) :
    let r := AC_AttitudeControl_Multi.set_throttle_out p s m cp cr thr b c
    r.1 = { s with
      _throttle_in := r.fst._throttle_in
      _althold_lean_angle_max_rad := r.fst._althold_lean_angle_max_rad
      _angle_boost := r.fst._angle_boost } ∧
    r.2 = { m with
      _throttle_filter_cutoff := c
      _throttle_in := r.snd._throttle_in
      _throttle_avg_max := r.snd._throttle_avg_max } := by
  intro r
  simp only [r, AC_AttitudeControl_Multi.set_throttle_out,
    AC_AttitudeControl_Multi.update_althold_lean_angle_max,
    AC_AttitudeControl_Multi.get_throttle_boosted]
  split_ifs <;> exact ⟨rfl, rfl⟩

/-- `set_throttle_out_frame` for a named result. -/
theorem set_throttle_out_frame' {p : AC_AttitudeControl_Multi.Params}
    {s : AC_AttitudeControl_Multi.State} {m : AP_Motors.Inputs} {cp cr thr : Float32} {b : Bool}
    {c : Float32} {a : AC_AttitudeControl_Multi.State} {mo : AP_Motors.Inputs}
    (h : AC_AttitudeControl_Multi.set_throttle_out p s m cp cr thr b c = (a, mo)) :
    a = { s with
      _throttle_in := a._throttle_in
      _althold_lean_angle_max_rad := a._althold_lean_angle_max_rad
      _angle_boost := a._angle_boost } ∧
    mo = { m with
      _throttle_filter_cutoff := c
      _throttle_in := mo._throttle_in
      _throttle_avg_max := mo._throttle_avg_max } := by
  have := set_throttle_out_frame p s m cp cr thr b c
  rw [h] at this
  exact this

/-- The loop time of the scheduler at a `2500 µs` sample is `dtF`, on the first tick
(`1 / SCHED_LOOP_RATE`) as on the others. -/
theorem scheduler_loop_dt (st : Copter.State) :
    (Copter.scheduler_loop st 2500).scheduler.last_loop_time_s = dtF := by
  unfold Copter.scheduler_loop
  dsimp only
  split
  · decide
  · rfl

/-- One tick after the stamp, the controller is active (`uint32_t` arithmetic). -/
theorem ticks_active (t : UInt32) : decide ((t + 1) - t ≤ 1) = true := by
  have : (t + 1) - t = 1 := by grind
  rw [this]; decide

/-- `read_inertia` writes the estimates from the AHRS view (both AHRS calls succeed). -/
theorem read_inertia_eq (s : Copter.State) :
    Copter.read_inertia s = { s with
      pos_control := { s.pos_control with
        _pos_estimate_ned_m := s.ahrs.pos_ned
        _vel_estimate_ned_ms := s.ahrs.vel_ned } } := rfl

/-! ## The common prefix of a tick -/

/-- The common prefix of `Copter.loop` on a state that is already in Auto: `scheduler_loop`,
`ins_update`, `run_rate_controller_main`, `motors_output_main`, `read_AHRS`, `read_inertia`. -/
def prefixState (p : Copter.Parameters) (st : Copter.State) (smp : Copter.AHRS.Sample) :
    Copter.State :=
  Copter.read_inertia (Copter.read_AHRS (Copter.motors_output_main p (Copter.run_rate_controller_main p
    (Copter.ins_update (Copter.scheduler_loop st smp.dt_us) smp))) smp)

set_option maxHeartbeats 1000000 in
/-- **The common prefix of a tick after the first.** From the core invariant and the sample of the
plant, the state after `read_inertia` satisfies `PreRun` (with `m` the motors object after the rate
controller, before the throttle filter update), the plant is `vstate (ζ - 1) w (-k F)`, the
scheduler has advanced by one tick, and the navigator, the mode, AutoYaw and the Auto flag are
unchanged. -/
theorem prefix_run (L : LibmZero32) {sense32 : ℝ → Float32} {senseP : ℝ → Float}
    (S : CopterSense sense32 senseP) (st : Copter.State) (phys : CState) (h : InvCore st phys) :
    ∃ (ζ w : ℝ) (m : AP_MotorsMulticopter.State),
      phys = vstate (ζ - 1) w (-(CopterVert.k * st.motors._throttle_filter_value.toReal)) ∧
      PreRun (prefixState runParams st (sample sense32 senseP phys)) m ζ w ∧
      (prefixState runParams st (sample sense32 senseP phys)).wp_nav = st.wp_nav ∧
      (prefixState runParams st (sample sense32 senseP phys)).mode_auto = st.mode_auto ∧
      (prefixState runParams st (sample sense32 senseP phys)).auto_yaw = st.auto_yaw ∧
      (prefixState runParams st (sample sense32 senseP phys)).in_auto = st.in_auto ∧
      (prefixState runParams st (sample sense32 senseP phys)).scheduler.ticks32 =
        st.scheduler.ticks32 + 1 := by
  obtain ⟨ζ, w, hphys, hV⟩ := h.plant
  set F := st.motors._throttle_filter_value with hFdef
  have b0 := CopterVert.bound_0 hV
  have b1 := CopterVert.bound_1 hV
  have b3 := CopterVert.bound_3 hV
  have b4 := CopterVert.bound_4 hV
  have b5 := CopterVert.bound_5 hV
  -- the sample
  set smp := sample sense32 senseP phys with hsmp_def
  have hsmp : smp =
      { pos := ⟨0, 0, senseP (ζ - 1)⟩, vel := ⟨0, 0, sense32 w⟩,
        accel_ef := ⟨0, 0, sense32 (-(CopterVert.k * F.toReal))⟩, quat := ⟨1, 0, 0, 0⟩,
        gyro := ⟨0, 0, 0⟩, dt_us := dtUs } := by
    rw [hsmp_def, hphys]; exact sample_vstate S.f32.zero S.f32.one S.pos.zero _ _ _
  have hdt_us : smp.dt_us = 2500 := by rw [hsmp]; rfl
  have hq : smp.quat = ⟨1, 0, 0, 0⟩ := by rw [hsmp]
  have hgyro : smp.gyro = ⟨0, 0, 0⟩ := by rw [hsmp]
  have hpos : smp.pos = ⟨0, 0, senseP (ζ - 1)⟩ := by rw [hsmp]
  have hvel : smp.vel = ⟨0, 0, sense32 w⟩ := by rw [hsmp]
  have hacc : smp.accel_ef = ⟨0, 0, sense32 (-(CopterVert.k * F.toReal))⟩ := by rw [hsmp]
  -- the readings
  have hFb : |-(CopterVert.k * F.toReal)| ≤ 10.05 := by
    have := abs_le.1 b5
    rw [abs_le]; simp only [vx] at this
    rw [CopterVertNear.k_eq]; constructor <;> nlinarith
  obtain ⟨nz, nw, nf⟩ := CopterVertNear.sense_near S b0 b1 hFb
  -- scheduler and INS
  set s2 := Copter.ins_update (Copter.scheduler_loop st smp.dt_us) smp with hs2
  have h2dt : s2.scheduler.last_loop_time_s = dtF := by
    show (Copter.scheduler_loop st smp.dt_us).scheduler.last_loop_time_s = dtF
    rw [hdt_us]; exact scheduler_loop_dt st
  have h2g : ZV s2.ins_gyro := by
    show ZV smp.gyro
    rw [hgyro]; exact ZV_zero_lit
  -- the rate controller
  obtain ⟨mix, pr, pp, py, r1, r2, r3, f1, f2, f3, hpr, hpp, hpy, hr1, hr2, hr3, hf1, hf2, hf3, e3⟩ :=
    run_rate_controller_main_Z s2 h2dt h2g h.body h.sysid h.act_sysid h.rate_roll h.rate_pitch
      h.rate_yaw h.pd h.isc h.ff
  set s3 := Copter.run_rate_controller_main runParams s2 with hs3
  have hm3 : s3.motors = { st.motors with
      _dt_s := dtF, _roll_in := r1, _pitch_in := r2, _yaw_in := r3, _roll_in_ff := f1,
      _pitch_in_ff := f2, _yaw_in_ff := f3 } := by rw [e3]; rfl
  have hp3 : s3.pos_control = AC_PosControl.set_dt_s st.pos_control dtF := by rw [e3]; rfl
  have ha3 : s3.attitude_control = { st.attitude_control with
      _dt_s := dtF, _rate_gyro_rads := s2.ins_gyro, _throttle_rpy_mix := mix,
      _pid_rate_roll := pr, _pid_rate_pitch := pp, _pid_rate_yaw := py,
      _pd_scale_used := st.attitude_control._pd_scale,
      _i_scale_used := st.attitude_control._i_scale,
      _angle_P_scale_used := st.attitude_control._angle_P_scale,
      _sysid_ang_vel_body_rads := ⟨0, 0, 0⟩, _actuator_sysid := ⟨0, 0, 0⟩,
      _pd_scale := AC_AttitudeControl.VECTORF_111, _i_scale := AC_AttitudeControl.VECTORF_111,
      _angle_P_scale := AC_AttitudeControl.VECTORF_111 } := by rw [e3]; rfl
  have hw3 : s3.wp_nav = st.wp_nav := by rw [e3]; rfl
  have hmo3 : s3.mode_auto = st.mode_auto := by rw [e3]; rfl
  have hy3 : s3.auto_yaw = st.auto_yaw := by rw [e3]; rfl
  have hi3 : s3.in_auto = st.in_auto := by rw [e3]; rfl
  have hsc3 : s3.scheduler.ticks32 = st.scheduler.ticks32 + 1 := by rw [e3]; rfl
  -- the throttle filter of this tick
  set m3 := s3.motors.toState with hm3def
  have m3F : m3._throttle_filter_value = F := by rw [hm3def, hm3]
  have m3c : m3._throttle_filter_cutoff = st.motors._throttle_filter_cutoff := by rw [hm3def, hm3]
  have m3t : m3._throttle_in = st.motors._throttle_in := by rw [hm3def, hm3]
  have m3dt : m3._dt_s = dtF := by rw [hm3def, hm3]
  have vinv3 : VInv st.pos_control._pid_vel_d_m st.pos_control._pid_accel_d_m m3 :=
    vinv_congr h.vinv m3F m3c m3t
  have hF' := CopterVertNear.motors_tick vinv3.cutoff m3dt vinv3.F_fin
    (φ := F.toReal - 4 / 9) (by rw [m3F]; ring) vinv3.throttle b5 b3 b4
  have hF'b : |(1 - CopterVert.am) * (F.toReal - 4 / 9) + CopterVert.am *
      (-(CopterVert.kp * st.pos_control._pid_accel_d_m._error.toReal) -
        (st.pos_control._pid_accel_d_m._integrator.toReal - CopterVertNear.Istar))| ≤ 0.013 := by
    have h5 := abs_le.1 b5; have h3 := abs_le.1 b3; have h4 := abs_le.1 b4
    simp only [vx] at h5 h3 h4
    rw [CopterVertNear.am_eq, CopterVertNear.kp_eq]
    rw [abs_le]; constructor <;> nlinarith
  have hF'0 : 0 < (AP_MotorsMulticopter.update_throttle_filter m3)._throttle_filter_value.toReal := by
    have := hF'.lo; have := abs_le.1 hF'b; linarith
  have hF'1 : (AP_MotorsMulticopter.update_throttle_filter m3)._throttle_filter_value.toReal < 1 := by
    have := hF'.hi; have := abs_le.1 hF'b; linarith
  -- the motors output
  obtain ⟨⟨m4, e4⟩, hF4, hti4, hcut4, hhov4, havg4, hlo4, hup4, hen4, hrf4, hpf4, hyf4, htf4, hb4,
      hdt4, -, -, -, -, -, -, hact4⟩ :=
    motors_output_main_hover s3 (by rw [hm3]; exact h.motlim.enabled)
      (by rw [hm3]; exact h.motlim.roll) (by rw [hm3]; exact h.motlim.pitch)
      (by rw [hm3]; exact h.motlim.yaw) (by rw [hm3]; exact h.motlim.thr)
      (by rw [hm3]; exact hr1) (by rw [hm3]; exact hf1) (by rw [hm3]; exact hr2)
      (by rw [hm3]; exact hf2) (by rw [hm3]; exact hr3) (by rw [hm3]; exact hf3)
      (by rw [hm3]; exact h.boost) (by rw [hm3]) hF'.1 hF'0 hF'1
  set s4 := Copter.motors_output_main runParams s3 with hs4
  -- the AHRS and the estimates
  obtain ⟨vcp, vcr, -, -, -, -, -, -, -, vq, -, vacc, vpos, vvel, -⟩ := ahrs_update_level L smp hq
  have e6 : prefixState runParams st smp = { s4 with
      ahrs := Copter.AHRS.update smp
      pos_control := { s4.pos_control with
        _pos_estimate_ned_m := smp.pos
        _vel_estimate_ned_ms := smp.vel } } := by
    show Copter.read_inertia (Copter.read_AHRS s4 smp) = _
    rw [read_inertia_eq]
    show { Copter.read_AHRS s4 smp with
      pos_control := { s4.pos_control with
        _pos_estimate_ned_m := (Copter.AHRS.update smp).pos_ned
        _vel_estimate_ned_ms := (Copter.AHRS.update smp).vel_ned } } = _
    rw [vpos, vvel]; rfl
  have hp4 : s4.pos_control = AC_PosControl.set_dt_s st.pos_control dtF := by rw [e4, hp3]
  have hps6 : (prefixState runParams st smp).pos_control = { st.pos_control with
      _dt_s := dtF, _pos_estimate_ned_m := smp.pos, _vel_estimate_ned_ms := smp.vel } := by
    rw [e6]; dsimp only; rw [hp4]; rfl
  have hpa6 : (prefixState runParams st smp).attitude_control = s3.attitude_control := by
    rw [e6]; dsimp only; rw [e4] 
  have hm6 : (prefixState runParams st smp).motors = s4.motors := by rw [e6]
  have hact6 : (prefixState runParams st smp).actuators = s4.actuators := by rw [e6]
  have hahrs6 : (prefixState runParams st smp).ahrs = Copter.AHRS.update smp := by rw [e6]
  have hsch6 : (prefixState runParams st smp).scheduler.ticks32 = st.scheduler.ticks32 + 1 := by
    rw [e6]; dsimp only; rw [e4]; exact hsc3
  have hw6 : (prefixState runParams st smp).wp_nav = st.wp_nav := by
    rw [e6]; dsimp only; rw [e4]; exact hw3
  have hmo6 : (prefixState runParams st smp).mode_auto = st.mode_auto := by
    rw [e6]; dsimp only; rw [e4]; exact hmo3
  have hy6 : (prefixState runParams st smp).auto_yaw = st.auto_yaw := by
    rw [e6]; dsimp only; rw [e4]; exact hy3
  have hi6 : (prefixState runParams st smp).in_auto = st.in_auto := by
    rw [e6]; dsimp only; rw [e4]; exact hi3
  clear_value s2 s3 s4
  generalize prefixState runParams st smp = s6 at hps6 hpa6 hm6 hact6 hahrs6 hsch6 hw6 hmo6 hy6 hi6 ⊢
  refine ⟨ζ, w, m3, hphys, ?_, hw6, hmo6, hy6, hi6, hsch6⟩
  rw [ha3] at hpa6
  have hclock : s6.clock.ticks32 = st.scheduler.ticks32 + 1 := hsch6
  exact {
    hV := by rw [hps6, m3F]; exact hV
    vinv := by rw [hps6]; exact vinv3
    m_dt := m3dt
    F_eq := by rw [hm6]; exact hF4
    F_pos := by rw [hm6, hF4]; exact hF'0
    F_lt := by rw [hm6, hF4]; exact hF'1
    act := by intro i; rw [hact6, hm6, hF4]; exact hact4 i
    lower := by rw [hm6]; exact hlo4
    upper := by rw [hm6]; exact hup4
    motlim := by
      rw [hm6]
      exact MotLim.congr h.motlim (hen4.trans (by rw [hm3])) (hrf4.trans (by rw [hm3]))
        (hpf4.trans (by rw [hm3])) (hyf4.trans (by rw [hm3])) (htf4.trans (by rw [hm3]))
        (hhov4.trans (by rw [hm3]))
    boost := by rw [hm6]; exact hb4
    cp := by rw [hahrs6]; exact vcp
    cr := by rw [hahrs6]; exact vcr
    quat := by rw [hahrs6]; exact vq
    fs := by rw [hahrs6, vacc, hacc, m3F]; exact nf
    pex := by rw [hps6, hpos]; exact ZD_zero
    pey := by rw [hps6, hpos]; exact ZD_zero
    pez := by rw [hps6, hpos]; exact nz
    vex := by rw [hps6, hvel]; exact Z_zero
    vey := by rw [hps6, hvel]; exact Z_zero
    vez := by rw [hps6, hvel]; exact nw
    psc_dt := by rw [hps6]
    psclim := by rw [hps6]; exact PscLim.congr h.psclim rfl
    vel_desired := by rw [hps6]; exact h.vel_desired
    doff := by rw [hps6]; exact h.doff
    terr := by rw [hps6]; exact h.terr
    off := by rw [hps6]; exact h.off
    pid_ne := by rw [hps6]; exact h.pid_ne
    lim := by rw [hps6]; exact h.lim
    nescale := by rw [hps6]; exact h.nescale
    pos_target := by rw [hps6]; exact h.pos_target
    d_active := by
      unfold AC_PosControl.D_is_active
      rw [hclock, hps6]; dsimp only; rw [h.d_ticks]; exact ticks_active _
    ne_active := by
      unfold AC_PosControl.NE_is_active
      rw [hclock, hps6]; dsimp only; rw [h.ne_ticks]; exact ticks_active _
    att_dt := by rw [hpa6]
    angP := by rw [hpa6]
    target := by rw [hpa6]; exact h.target
    ang_vel := by rw [hpa6]; exact h.ang_vel
    ang_accel := by rw [hpa6]; exact h.ang_accel
    sysid := by rw [hpa6]; exact ZV_zero_lit
    act_sysid := by rw [hpa6]; exact ZV_zero_lit
    rate_roll := by rw [hpa6]; exact hpr
    rate_pitch := by rw [hpa6]; exact hpp
    rate_yaw := by rw [hpa6]; exact hpy
    pd := by rw [hpa6]
    isc := by rw [hpa6]
    thrust_angle := by rw [hpa6]; exact h.thrust_angle
    ytc := by rw [hpa6]; exact h.ytc }

/-! ## `wp_run` at the steady state -/

/-- `wp_run` with AutoYaw in `HOLD`, as the composition of its calls. -/
theorem wp_run_hold (p : Copter.Parameters) (s : Copter.State) (hy : s.auto_yaw._mode = .HOLD) :
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
          { yaw_angle_rad := r3.1._euler_angle_target_rad.z, yaw_rate_rads := 0.0,
            heading_mode := .Rate_Only }
        motors := { s.motors with toInputs := r3.2 }
        auto_yaw := { s.auto_yaw with
          _pilot_yaw_rate_rads := 0.0
          _yaw_angle_rad := r3.1._euler_angle_target_rad.z
          _yaw_rate_rads := 0.0 } } := by
  unfold Copter.ModeAuto.wp_run
  simp only [Id.run]
  rw [get_heading_hold]
  · rfl
  · exact hy

/-- `InputOK` for the run parameters at the loop time `dtF` and a finite yaw rate time constant. -/
theorem inputOK_run (s : AC_AttitudeControl.State) (hdt : s._dt_s = dtF)
    (hy : s._rate_y_tc.IsFinite) : InputOK runParams.att.toParams s := by
  refine ⟨by decide, by decide, by decide, abs_le_thousand (by decide) (by decide) (by decide),
    abs_le_thousand (by decide) (by decide) (by decide),
    abs_le_thousand (by decide) (by decide) (by decide), by decide, hy, by decide, ?_, ?_⟩
  · rw [hdt]; exact CopterVertNear.dtF_val.1
  · rw [hdt]; exact dtF_abs

set_option maxHeartbeats 4000000 in
/-- **`wp_run` at the steady state.** On a state satisfying `PreRun` with the steady navigator and
AutoYaw in `HOLD`, `wp_run` re-establishes the core invariant for the plant stepped by the
actuators of the tick (from the vertical state `(ζ - 1, w)` of the sample, whatever the stored
specific force), keeps the navigator steady, and changes neither the mode, nor AutoYaw's mode, nor
the Auto flag, nor the scheduler. -/
theorem wp_run_steady (L : LibmZero32) (C : ConvZero) (N : NarrowSpec 2)
    (s : Copter.State) (m : AP_MotorsMulticopter.State) (ζ w : ℝ) (hp : PreRun s m ζ w)
    (hn : NavSteady s.wp_nav) (hy : s.auto_yaw._mode = .HOLD) :
    (∀ f : ℝ, InvCore (Copter.ModeAuto.wp_run runParams s)
      (dyn (vstate (ζ - 1) w f) (Copter.ModeAuto.wp_run runParams s).actuators)) ∧
    NavSteady (Copter.ModeAuto.wp_run runParams s).wp_nav ∧
    (Copter.ModeAuto.wp_run runParams s).mode_auto = s.mode_auto ∧
    (Copter.ModeAuto.wp_run runParams s).auto_yaw._mode = s.auto_yaw._mode ∧
    (Copter.ModeAuto.wp_run runParams s).in_auto = s.in_auto ∧
    (Copter.ModeAuto.wp_run runParams s).scheduler = s.scheduler := by
  rw [wp_run_hold runParams s hy]
  have b0 : |ζ| ≤ 1 / 200 := CopterVert.bound_0 hp.hV
  -- the navigator
  have hpe : Near64 s.pos_control._pos_estimate_ned_m.z (-1) (1 / 100) := by
    refine ⟨hp.pez.1, ?_⟩
    have h1 := abs_le.1 hp.pez.2; have h2 := abs_le.1 b0
    rw [abs_le]; constructor <;> linarith
  obtain ⟨nav', tp, tv, ta, hnav', htpx, htpy, htpz, htv, hta, hU⟩ :=
    update_wpnav_steady C N hn (s.wpEnv runParams) hp.psc_dt hp.vel_desired hp.doff.2.2.2.1
      hp.terr.2.1 hpe hp.pos_target
  rw [hU]
  dsimp only
  -- the horizontal position controller
  set psc0 := AC_PosControl.set_pos_vel_accel_NED_m
    (AC_PosControl.set_pos_terrain_target_D_m s.pos_control 0.0) tp tv ta with hpsc0
  have hdt0 : psc0._dt_s = dtF := hp.psc_dt
  obtain ⟨hNE, hr, hrt, hrs, hrl, hrpdz, hrptz, hrvd, hrad, hrpe, hrve, -, -, -, -, -, -, hro1, hro2,
      hro3, hro4, hro5, hro6, -, -, -⟩ :=
    NE_update_controller_hover_run C psc0 (s.wpEnv runParams).ahrs (s.wpEnv runParams).att
      (s.wpEnv runParams).clock (by rw [hdt0]; exact CopterVertNear.dtF_val.1)
      (by rw [hdt0]; exact dtF_abs) hp.psclim.amax_ne hp.psclim.jmax_ne hp.psclim.jmax_ne_b
      hp.psclim.vmax_ne hp.lim lit_one.1 hp.nescale hp.ne_active hp.off htpx.1 htpy.1 hp.pex.1
      hp.pey.1 (htpx.2.trans hp.pex.2.symm) (htpy.2.trans hp.pey.2.symm)
      ⟨htv.1, htv.2.1⟩ ⟨hp.vex, hp.vey⟩ ⟨hta.1, hta.2.1⟩ hp.pid_ne
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
  have hr_ter : r._pos_terrain_target_d_m = 0.0 := er (·._pos_terrain_target_d_m) (fun _ => rfl)
  have hr_ter2 : r._pos_terrain_d_m = s.pos_control._pos_terrain_d_m :=
    er (·._pos_terrain_d_m) (fun _ => rfl)
  have hr_ter3 : r._vel_terrain_d_ms = s.pos_control._vel_terrain_d_ms :=
    er (·._vel_terrain_d_ms) (fun _ => rfl)
  have hr_ter4 : r._accel_terrain_d_mss = s.pos_control._accel_terrain_d_mss :=
    er (·._accel_terrain_d_mss) (fun _ => rfl)
  have hrlim : PscLim r := PscLim.congr hp.psclim hr_key
  -- the vertical position controller
  have hactD : AC_PosControl.D_is_active r s.clock = true := by
    unfold AC_PosControl.D_is_active; rw [hr_lud]; exact hp.d_active
  have hoffD : DOffZ r := ⟨hro1 ▸ hp.doff.1, hro2 ▸ hp.doff.2.1, hro3 ▸ hp.doff.2.2.1,
    hro4 ▸ hp.doff.2.2.2.1, hro5 ▸ hp.doff.2.2.2.2.1, hro6 ▸ hp.doff.2.2.2.2.2⟩
  have hterD : TerrZ r := ⟨hr_ter ▸ Z_lit0, hr_ter2 ▸ hp.terr.2.1, hr_ter3 ▸ hp.terr.2.2.1,
    hr_ter4 ▸ hp.terr.2.2.2⟩
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
      topostype s1._pos_terrain_d_m) (-1) 0 := ⟨htf, by rw [htv', hrpdz]; exact htpz.2⟩
  have h1vd : s1._vel_desired_ned_ms = r._vel_desired_ned_ms := by rw [hs1]
  have h1ad : s1._accel_desired_ned_mss = r._accel_desired_ned_mss := by rw [hs1]
  have hvff : Z (s1._vel_desired_ned_ms.z + s1._vel_offset_ned_ms.z + s1._vel_terrain_d_ms) :=
    Z_add (Z_add (by rw [h1vd, hrvd]; exact htv.2.2) hO1.2.2.2.1) hT1.2.2.1
  have haff : Z (s1._accel_desired_ned_mss.z + s1._accel_offset_ned_mss.z +
      s1._accel_terrain_d_mss) :=
    Z_add (Z_add (by rw [h1ad, hrad]; exact hta.2.2) hO1.2.2.2.2.2) hT1.2.2.2
  -- the vertical tick
  have hV' : CopterVert.V (vx ζ w r._pid_vel_d_m._error r._pid_accel_d_m._error
      r._pid_accel_d_m._integrator m._throttle_filter_value) ≤ 1 / 10 := by
    rw [hr_pv, hr_pa]; exact hp.hV
  have hI' : VInv r._pid_vel_d_m r._pid_accel_d_m m := by rw [hr_pv, hr_pa]; exact hp.vinv
  have hzs : Near64 r._pos_estimate_ned_m.z (ζ - 1) 1e-15 := by rw [hrpe]; exact hp.pez
  have hws : Near32 r._vel_estimate_ned_ms.z w 6e-10 := by rw [hrve]; exact hp.vez
  have hN1 : NarrowSpec 1 := narrow_mono N (by norm_num)
  obtain ⟨⟨n, hn, hstep⟩, hVI⟩ := CopterVertNear.vert_tick hN1 r._p_pos_d_m r._pid_vel_d_m
    r._pid_accel_d_m m runParams.att s.attitude_control s.motors.toInputs (ζ := ζ) (w := w)
    (zs := r._pos_estimate_ned_m.z) (ws := r._vel_estimate_ned_ms.z)
    (fs := s.ahrs.posInputs.get_accel_ef.z) (scZ := s.ahrs.posInputs.get_control_gain_scaler_Z)
    false false hV' hI' hp.m_dt hzs hws hp.fs htgt (hr_pp ▸ hrlim.emin) (hr_pp ▸ hrlim.emin_le)
    (hr_pp ▸ hrlim.emax) (hr_pp ▸ hrlim.emax_ge) (hr_pp ▸ hrlim.D1) (hr_pp ▸ hrlim.D1_ge)
    lit_one hvff haff hp.cp hp.cr (L.cos_zero _ hp.thrust_angle) hp.motlim.hover
  have hP1t := (CopterVertNear.p1d_near hN1 r._p_pos_d_m htgt hzs (le_refl _) b0
    (hr_pp ▸ hrlim.emin) (hr_pp ▸ hrlim.emin_le) (hr_pp ▸ hrlim.emax) (hr_pp ▸ hrlim.emax_ge)
    (hr_pp ▸ hrlim.D1) (hr_pp ▸ hrlim.D1_ge)).2.1
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
  dsimp only
  -- the attitude controller
  have h2dt : att2._dt_s = dtF := by rw [hA2]; exact hp.att_dt
  have h2P : att2._angle_P_scale = AC_AttitudeControl.VECTORF_111 := by rw [hA2]; exact hp.angP
  have h2y : att2._rate_y_tc.IsFinite := by rw [hA2]; exact hp.ytc
  have h2t : IdQ att2._attitude_target := by rw [hA2]; exact hp.target
  have h2v : ZV att2._ang_vel_target_rads := by rw [hA2]; exact hp.ang_vel
  have h2a : ZV att2._ang_accel_target_rads := by rw [hA2]; exact hp.ang_accel
  have hx : Z (AC_PosControl.get_thrust_vector sD).x := by
    show Z sD._accel_target_ned_mss.x
    rw [hatxD]; exact hNE.1.1
  have hyv : Z (AC_PosControl.get_thrust_vector sD).y := by
    show Z sD._accel_target_ned_mss.y
    rw [hatyD]; exact hNE.1.2
  obtain ⟨hatt3, hb3, ht3, hta3, -, hv3, ha3, -, -, hff3⟩ :=
    multi_rate_only_Z L C runParams.att runParams_cap runParams_rateMaxOK att2
      (runParams_angOK att2.toState h2dt h2P) (inputOK_run att2.toState h2dt h2y) h2t h2v h2a
      hp.quat hx hyv rfl
      { yaw_angle_rad := att2._euler_angle_target_rad.z, yaw_rate_rads := 0.0,
        heading_mode := .Rate_Only } rfl Z_lit0
  generalize AC_AttitudeControl_Multi.input_thrust_vector_heading runParams.att att2
    s.ahrs.quat_body_to_ned (AC_PosControl.get_thrust_vector sD) _ = att3 at *
  -- field facts of the new position controller
  have dNE : sD._last_update_ne_ticks = r._last_update_ne_ticks := by rw [hsD, hs1]
  have dPN : sD._pid_vel_ne_m = r._pid_vel_ne_m := by rw [hsD, hs1]
  have dNS : sD._ne_control_scale_factor = r._ne_control_scale_factor := by rw [hsD, hs1]
  have dVD : sD._vel_desired_ned_ms = r._vel_desired_ned_ms := by rw [hsD, hs1]
  have dOff : OffZ sD := by rw [hsD, hs1]; exact hNE.2.1
  have dLim : FinV2 sD._limit_vector_ned.xy := by rw [hsD, hs1]; exact hrl
  have dKey : pscKey sD = pscKey r := by
    unfold pscKey
    rw [hppD, hP1fr, hkimD, hsD, hs1]
  have hm2F : m2._throttle_filter_value = s.motors._throttle_filter_value := by rw [hM2]
  have hm2H : m2._throttle_hover = s.motors._throttle_hover := by rw [hM2]
  -- the new state
  refine ⟨fun f => ?_, hnav', rfl, rfl, rfl, rfl⟩
  have hpv := CopterVertNear.plant_vert (ζ - 1) w f s.actuators hp.F_pos.le hp.F_lt.le
    (fun i => (hp.act i).2)
  have hVn := (CopterVertNear.vert_tick_V hV' ⟨n, hn, hstep⟩).1
  exact {
    plant := ⟨ζ + CopterVert.h * w, w - CopterVert.k * CopterVert.h *
        ((AP_MotorsMulticopter.update_throttle_filter m)._throttle_filter_value.toReal - 4 / 9),
      by
        rw [hpv]
        show _ = vstate _ _ (-(CopterVert.k * m2._throttle_filter_value.toReal))
        rw [hm2F, hp.F_eq]
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
    sysid := by rw [hatt3, hA2]; exact hp.sysid
    act_sysid := by rw [hatt3, hA2]; exact hp.act_sysid
    rate_roll := by rw [hatt3, hA2]; exact hp.rate_roll
    rate_pitch := by rw [hatt3, hA2]; exact hp.rate_pitch
    rate_yaw := by rw [hatt3, hA2]; exact hp.rate_yaw
    pd := by rw [hatt3, hA2]; exact hp.pd
    isc := by rw [hatt3, hA2]; exact hp.isc
    ff := by rw [hff3]; exact lit_one.1
    thrust_angle := hta3
    ytc := by rw [hatt3, hA2]; exact hp.ytc }

/-! ## The tick -/

/-- `ModeAuto.run` at the steady mode: the mission is complete, so `mission_update` returns its
argument, and the `LOITER` submode runs `loiter_run`, which is `wp_run`. -/
theorem run_steady (p : Copter.Parameters) (s : Copter.State)
    (hw : s.mode_auto.waiting_to_start = false)
    (hc : s.mode_auto.mission.state = .MISSION_COMPLETE) (hm : s.mode_auto._mode = .LOITER) :
    Copter.ModeAuto.run p s = Copter.ModeAuto.wp_run p s := by
  have hmu : Copter.ModeAuto.mission_update p s = s := by
    unfold Copter.ModeAuto.mission_update
    simp [hc]
  unfold Copter.ModeAuto.run
  simp only [Id.run, hw, Bool.false_eq_true, if_false, hmu, hm]
  rfl

/-- On a state already in Auto, `Copter.loop` is the prefix followed by `update_flight_mode`. -/
theorem loop_prefix (p : Copter.Parameters) (st : Copter.State) (smp : Copter.AHRS.Sample)
    (h : (prefixState p st smp).in_auto = true) :
    Copter.loop p st smp = some (Copter.update_flight_mode p (prefixState p st smp)) := by
  unfold prefixState at h
  unfold Copter.loop
  dsimp only
  rw [if_pos h]
  rfl

/-- **One steady tick of the controller.** From the steady invariant and the plant's sample,
`Copter.loop` succeeds and the new state satisfies the steady invariant with the plant stepped by
the new actuators. -/
theorem loop_steady (L : LibmZero32) (C : ConvZero) (N : NarrowSpec 2)
    {sense32 : ℝ → Float32} {senseP : ℝ → Float} (S : CopterSense sense32 senseP)
    (st : Copter.State) (phys : CState) (h : InvSteady st phys) :
    ∃ st', Copter.loop runParams st (sample sense32 senseP phys) = some st' ∧
      InvSteady st' (dyn phys st'.actuators) := by
  obtain ⟨hc, hn, hm⟩ := h
  obtain ⟨ζ, w, m, hphys, hpre, hw, hmo, hy, hi, -⟩ := prefix_run L S st phys hc
  have hloop := loop_prefix runParams st (sample sense32 senseP phys) (hi.trans hm.in_auto)
  have hrun : Copter.update_flight_mode runParams (prefixState runParams st
      (sample sense32 senseP phys)) =
      Copter.ModeAuto.wp_run runParams (prefixState runParams st (sample sense32 senseP phys)) :=
    run_steady runParams _ (by rw [hmo]; exact hm.started) (by rw [hmo]; exact hm.complete)
      (by rw [hmo]; exact hm.submode)
  obtain ⟨hI, hN, hmo', hy', hi', -⟩ := wp_run_steady L C N _ m ζ w hpre (by rw [hw]; exact hn)
    (by rw [hy]; exact hm.yaw)
  refine ⟨_, hloop.trans (congrArg some hrun), ?_, hN, ?_⟩
  · have := hI (-(CopterVert.k * st.motors._throttle_filter_value.toReal))
    rw [← hphys] at this
    exact this
  · refine ⟨hi'.trans (hi.trans hm.in_auto), ?_, ?_, ?_, ?_⟩
    · rw [hmo', hmo]; exact hm.submode
    · rw [hmo', hmo]; exact hm.started
    · rw [hmo', hmo]; exact hm.complete
    · rw [hy', hy]; exact hm.yaw

/-- **One steady tick of the harness** (`CopterLift.tick`, the step of the `copter` executable):
it keeps the started flag and the steady invariant, with the plant stepped by the printed
actuators. -/
theorem tick_steady (L : LibmZero32) (C : ConvZero) (N : CopterVertNear.NarrowSpec 2)
    {sense32 : ℝ → Float32} {senseP : ℝ → Float} (S : CopterPlant.CopterSense sense32 senseP)
    (st : Copter.State) (phys : CopterPlant.CState) (h : InvSteady st phys) :
    let r := CopterLift.tick runParams ⟨st, true⟩ (CopterPlant.sample sense32 senseP phys)
    r.1.started = true ∧ InvSteady r.1.st (CopterPlant.dyn phys r.2) := by
  intro r
  obtain ⟨st', hl, hI⟩ := loop_steady L C N S st phys h
  have hr : r = (⟨st', true⟩, st'.actuators) := by
    show CopterLift.tick runParams ⟨st, true⟩ (CopterPlant.sample sense32 senseP phys) = _
    unfold CopterLift.tick
    dsimp only
    rw [if_pos rfl, hl]
  rw [hr]
  exact ⟨rfl, hI⟩

/-- **The core invariant puts the plant in the hover box**: on the vertical through the waypoint,
altitude within `5 mm` of it, vertical speed within `1 cm/s`. -/
theorem InvCore.box {st : Copter.State} {phys : CState} (h : InvCore st phys) :
    ∃ z w f : ℝ, phys = vstate z w f ∧ |z + 1| ≤ 1 / 200 ∧ |w| ≤ 1 / 100 := by
  obtain ⟨ζ, w, hphys, hV⟩ := h.plant
  obtain ⟨b0, b1⟩ := CopterVert.box_of_V hV
  exact ⟨ζ - 1, w, _, hphys, by rw [sub_add_cancel]; exact b0, b1⟩

end Contracts.CopterHover
