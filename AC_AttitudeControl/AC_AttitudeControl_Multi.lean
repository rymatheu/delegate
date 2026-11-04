import AC_AttitudeControl.AC_AttitudeControl
import AP_Motors.Interface

/-!
# `AC_AttitudeControl_Multi`

Mirrors, at ArduPilot 802db19de1, `libraries/AC_AttitudeControl/AC_AttitudeControl_Multi.h:9-157`
(rate PID defaults `:9-39`, the three `AC_PID` members `:106-149`, `_thr_mix_*` and
`_throttle_gain_boost` `:151-156`, inline `set_throttle_mix_*`/`get_throttle_mix`/
`is_throttle_mix_min` `:69-76`) and `AC_AttitudeControl_Multi.cpp`: `:8-335` `var_info` (as
`Params`), `:337-346` constructor, `:349-362` `update_althold_lean_angle_max`, `:364-378`
`set_throttle_out`, `:380-384` `set_throttle_mix_max`, `:388-405` `get_throttle_boosted`, `:409-413`
`get_throttle_avg_max`, `:416-426` `update_throttle_gain_boost`, `:429-454`
`update_throttle_rpy_mix`, `:456-484` `rate_controller_run_dt`, `:487-491` `rate_controller_run`.

## Conventions

- `Params extends AC_AttitudeControl.Params` with the rate PID subgroups `ATC_RAT_RLL_`,
  `ATC_RAT_PIT_`, `ATC_RAT_YAW_` (so `p.ATC_RAT_RLL.P` is `ATC_RAT_RLL_P`; fields as in
  `AC_PID.Params`) and `ATC_THR_MIX_MIN/MAX/MAN`, `ATC_THR_G_BOOST`, with the Copter defaults of
  `AC_AttitudeControl_Multi.h:9-39`, `:106-149` and `.cpp:311-332`. (SITL's
  `Tools/autotest/default_params/copter.parm` overrides `ATC_RAT_YAW_P = 0.3`, `ATC_RAT_YAW_I =
  0.02`; that is a parameter file, not a code default.)
- `State extends AC_AttitudeControl.State` with the three rate PID states `_pid_rate_roll`,
  `_pid_rate_pitch`, `_pid_rate_yaw`.
- A call into `_motors` takes and returns the motors record `m : AP_Motors.Inputs`; reads of the
  motors object read `m`. AHRS reads are explicit arguments after the state and the motors
  record: `ahrs_cos_pitch`, `ahrs_cos_roll` (`_ahrs.cos_pitch()`, `_ahrs.cos_roll()`), and
  `attitude_body` (`_ahrs.get_quat_body_to_ned`).
- `_motors.get_throttle_slew_rate()` (`AP_Motors_Class.h:221`) is not part of
  `AP_Motors.Inputs`, so `update_throttle_gain_boost` and `rate_controller_run_dt` take it as the
  explicit argument `motors_throttle_slew_rate`. With the default `ATC_THR_G_BOOST = 0` the boost
  factors are `constrain_float(1, 1, 2) = 1` and `constrain_float(1, 1, 4) = 1`, so its value does not
  affect the result.
- The base-class entry points that need the rate PIDs are re-exported here with the PIDs filled in
  from `Params`/`State` (`input_thrust_vector_heading`, ...).

## Left out

- `parameter_sanity_check` (`:494-514`): it rewrites parameters (`set_and_save`); the defaults
  `THR_MIX_MAN = 0.1 ∈ [0.1, 4]`, `THR_MIX_MIN = 0.1 ∈ [0.1, 0.5]`, `THR_MIX_MAX = 0.5 ∈ [0.5, 5]`,
  `MIN ≤ MAX` leave it a no-op.
- `set_notch_sample_rate` (`:516-523`, notch filters, see `AC_PID.lean`), `_rate_gyro_time_us`
  (`:470`, timestamp), `_motors_multi` (the same object as `_motors`), and the `AP_Param` plumbing.
-/

namespace AC_AttitudeControl_Multi

open AP_Math
open AC_AttitudeControl (AC_ATTITUDE_CONTROL_ANGLE_LIMIT_THROTTLE_MAX AC_ATTITUDE_CONTROL_THR_G_BOOST_THRESH
  AC_ATTITUDE_CONTROL_MAX AC_ATTITUDE_CONTROL_MIN_DEFAULT AC_ATTITUDE_CONTROL_MAN_DEFAULT
  AC_ATTITUDE_CONTROL_MAX_DEFAULT HeadingCommand)

/-! ### Rate PID defaults, `AC_AttitudeControl_Multi.h:9-39` -/

def AC_ATC_MULTI_RATE_RP_P : ftype := 0.135
def AC_ATC_MULTI_RATE_RP_I : ftype := 0.135
def AC_ATC_MULTI_RATE_RP_D : ftype := 0.0036
def AC_ATC_MULTI_RATE_RP_IMAX : ftype := 0.5
def AC_ATC_MULTI_RATE_RPY_FILT_HZ : ftype := 20.0
def AC_ATC_MULTI_RATE_YAW_P : ftype := 0.180
def AC_ATC_MULTI_RATE_YAW_I : ftype := 0.018
def AC_ATC_MULTI_RATE_YAW_D : ftype := 0.0
def AC_ATC_MULTI_RATE_YAW_IMAX : ftype := 0.5
def AC_ATC_MULTI_RATE_YAW_FILT_HZ : ftype := 2.5

/-- `_pid_rate_roll` defaults (`.h:106-119`). -/
def pid_rate_roll_defaults : AC_PID.Defaults :=
  { p := AC_ATC_MULTI_RATE_RP_P, i := AC_ATC_MULTI_RATE_RP_I, d := AC_ATC_MULTI_RATE_RP_D, ff := 0.0,
    imax := AC_ATC_MULTI_RATE_RP_IMAX, filt_T_hz := AC_ATC_MULTI_RATE_RPY_FILT_HZ, filt_E_hz := 0.0,
    filt_D_hz := AC_ATC_MULTI_RATE_RPY_FILT_HZ, srmax := 0, srtau := 1.0 }
/-- `_pid_rate_pitch` defaults (`.h:121-134`). -/
def pid_rate_pitch_defaults : AC_PID.Defaults :=
  { p := AC_ATC_MULTI_RATE_RP_P, i := AC_ATC_MULTI_RATE_RP_I, d := AC_ATC_MULTI_RATE_RP_D, ff := 0.0,
    imax := AC_ATC_MULTI_RATE_RP_IMAX, filt_T_hz := AC_ATC_MULTI_RATE_RPY_FILT_HZ, filt_E_hz := 0.0,
    filt_D_hz := AC_ATC_MULTI_RATE_RPY_FILT_HZ, srmax := 0, srtau := 1.0 }
/-- `_pid_rate_yaw` defaults (`.h:136-149`). -/
def pid_rate_yaw_defaults : AC_PID.Defaults :=
  { p := AC_ATC_MULTI_RATE_YAW_P, i := AC_ATC_MULTI_RATE_YAW_I, d := AC_ATC_MULTI_RATE_YAW_D, ff := 0.0,
    imax := AC_ATC_MULTI_RATE_YAW_IMAX, filt_T_hz := AC_ATC_MULTI_RATE_RPY_FILT_HZ,
    filt_E_hz := AC_ATC_MULTI_RATE_YAW_FILT_HZ, filt_D_hz := AC_ATC_MULTI_RATE_RPY_FILT_HZ, srmax := 0,
    srtau := 1.0 }

/-! ### Parameters and state -/

/-- `AC_AttitudeControl_Multi::var_info` (`.cpp:8-335`), Copter defaults. -/
structure Params extends AC_AttitudeControl.Params where
  /-- `_pid_rate_roll`, subgroup `RAT_RLL_` (`.cpp:110`). -/
  ATC_RAT_RLL : AC_PID.Params := (AC_PID.init pid_rate_roll_defaults).1
  /-- `_pid_rate_pitch`, subgroup `RAT_PIT_` (`.cpp:207`). -/
  ATC_RAT_PIT : AC_PID.Params := (AC_PID.init pid_rate_pitch_defaults).1
  /-- `_pid_rate_yaw`, subgroup `RAT_YAW_` (`.cpp:304`). -/
  ATC_RAT_YAW : AC_PID.Params := (AC_PID.init pid_rate_yaw_defaults).1
  /-- `_thr_mix_min` (`.cpp:311`). -/
  ATC_THR_MIX_MIN : ftype := AC_ATTITUDE_CONTROL_MIN_DEFAULT
  /-- `_thr_mix_max` (`.cpp:318`). -/
  ATC_THR_MIX_MAX : ftype := AC_ATTITUDE_CONTROL_MAX_DEFAULT
  /-- `_thr_mix_man` (`.cpp:325`). -/
  ATC_THR_MIX_MAN : ftype := AC_ATTITUDE_CONTROL_MAN_DEFAULT
  /-- `_throttle_gain_boost` (`.cpp:332`). -/
  ATC_THR_G_BOOST : ftype := 0.0
deriving Repr

/-- Members of `AC_AttitudeControl_Multi` that are not parameters: the rate PID states. -/
structure State extends AC_AttitudeControl.State where
  _pid_rate_roll : AC_PID.State := (AC_PID.init pid_rate_roll_defaults).2
  _pid_rate_pitch : AC_PID.State := (AC_PID.init pid_rate_pitch_defaults).2
  _pid_rate_yaw : AC_PID.State := (AC_PID.init pid_rate_yaw_defaults).2
deriving Repr

/-- `get_rate_roll_pid()` (`.h:50`), parameter part. -/
def get_rate_roll_pid (p : Params) : AC_PID.Params := p.ATC_RAT_RLL
/-- `get_rate_pitch_pid()` (`.h:51`), parameter part. -/
def get_rate_pitch_pid (p : Params) : AC_PID.Params := p.ATC_RAT_PIT
/-- `get_rate_yaw_pid()` (`.h:52`), parameter part. -/
def get_rate_yaw_pid (p : Params) : AC_PID.Params := p.ATC_RAT_YAW

/-- Apply a base-class state update. -/
def lift (f : AC_AttitudeControl.State → AC_AttitudeControl.State) (s : State) : State :=
  { s with toState := f s.toState }

/-! ### Throttle mix, `.h:69-76`, `.cpp:380-384`, `:429-454` -/

/-- `set_throttle_mix_min` (`.h:69`). -/
def set_throttle_mix_min (p : Params) (s : State) : State :=
  { s with _throttle_rpy_mix_desired := p.ATC_THR_MIX_MIN }
/-- `set_throttle_mix_man` (`.h:70`). -/
def set_throttle_mix_man (p : Params) (s : State) : State :=
  { s with _throttle_rpy_mix_desired := p.ATC_THR_MIX_MAN }
/-- `set_throttle_mix_value` (`.h:72`). -/
def set_throttle_mix_value (s : State) (value : ftype) : State :=
  { s with _throttle_rpy_mix := value, _throttle_rpy_mix_desired := value }
/-- `get_throttle_mix` (`.h:73`). -/
def get_throttle_mix (s : State) : ftype := s._throttle_rpy_mix
/-- `is_throttle_mix_min` (`.h:76`). -/
def is_throttle_mix_min (p : Params) (s : State) : Bool := s._throttle_rpy_mix < 1.25 * p.ATC_THR_MIX_MIN

/-- `set_throttle_mix_max(ratio)` (`.cpp:380-384`). -/
def set_throttle_mix_max (p : Params) (s : State) (ratio : ftype) : State :=
  let ratio := constrain_float ratio 0.0 1.0
  { s with _throttle_rpy_mix_desired := (1.0 - ratio) * p.ATC_THR_MIX_MIN + ratio * p.ATC_THR_MIX_MAX }

/-- `update_throttle_rpy_mix` (`.cpp:429-454`): slew `_throttle_rpy_mix` toward
`_throttle_rpy_mix_desired`. Reads `_motors.get_throttle_hover()`, `get_throttle()`,
`get_throttle_out()`. -/
def update_throttle_rpy_mix (s : State) (m : AP_Motors.Inputs) : State :=
  let mix :=
    if s._throttle_rpy_mix < s._throttle_rpy_mix_desired then
      -- increase quickly (i.e. from 0.1 to 0.9 in 0.4 seconds)
      s._throttle_rpy_mix + MIN (2.0 * s._dt_s) (s._throttle_rpy_mix_desired - s._throttle_rpy_mix)
    else if s._throttle_rpy_mix > s._throttle_rpy_mix_desired then
      -- reduce more slowly (from 0.9 to 0.1 in 1.6 seconds)
      let mix := s._throttle_rpy_mix - MIN (0.5 * s._dt_s) (s._throttle_rpy_mix - s._throttle_rpy_mix_desired)
      -- if the mix is still higher than that being used, reset immediately
      let throttle_hover := AP_Motors.get_throttle_hover m
      let throttle_in := AP_Motors.get_throttle m
      let throttle_out := MAX (AP_Motors.get_throttle_out m) throttle_in
      let mix_used :=
        if throttle_out < throttle_hover then
          (throttle_out - throttle_in) / (throttle_hover - throttle_in)
        else
          throttle_out / throttle_hover
      MIN mix (MAX mix_used s._throttle_rpy_mix_desired)
    else s._throttle_rpy_mix
  { s with _throttle_rpy_mix := constrain_float mix 0.1 AC_ATTITUDE_CONTROL_MAX }

/-! ### Throttle output, `.cpp:349-413` -/

/-- `update_althold_lean_angle_max(throttle_in)` (`.cpp:349-362`). Reads
`_motors_multi.get_throttle_thrust_max()`. -/
def update_althold_lean_angle_max (p : Params) (s : State) (m : AP_Motors.Inputs) (throttle_in : ftype) :
    State :=
  -- calc maximum tilt angle based on throttle
  let thr_max := AP_Motors.get_throttle_thrust_max m
  -- divide by zero check
  if is_zero thr_max then
    { s with _althold_lean_angle_max_rad := 0.0 }
  else
    let althold_lean_angle_max :=
      (constrain_float (throttle_in / (AC_ATTITUDE_CONTROL_ANGLE_LIMIT_THROTTLE_MAX * thr_max)) 0.0 1.0).acos
    { s with _althold_lean_angle_max_rad := s._althold_lean_angle_max_rad
        + (s._dt_s / (s._dt_s + p._angle_limit_tc)) * (althold_lean_angle_max - s._althold_lean_angle_max_rad) }

/-- `get_throttle_boosted(throttle_in)` (`.cpp:388-405`); returns `(state, throttle_out)` (the
state carries `_angle_boost`). `ahrs_cos_pitch * ahrs_cos_roll` is the measured tilt cosine. -/
def get_throttle_boosted (p : Params) (s : State) (ahrs_cos_pitch ahrs_cos_roll : ftype)
    (throttle_in : ftype) : State × ftype :=
  if !p._angle_boost_enabled then
    ({ s with _angle_boost := 0 }, throttle_in)
  else
    -- inverted_factor is 1 for tilt angles below 84 degrees
    let cos_tilt := ahrs_cos_pitch * ahrs_cos_roll
    let inverted_factor := constrain_float (10.0 * cos_tilt) 0.0 1.0
    let cos_tilt_target := s._thrust_angle_rad.cos
    let boost_factor := 1.0 / constrain_float cos_tilt_target 0.1 1.0
    let throttle_out := throttle_in * inverted_factor * boost_factor
    ({ s with _angle_boost := constrain_float (throttle_out - throttle_in) (-1.0) 1.0 }, throttle_out)

/-- `get_throttle_avg_max(throttle_in)` (`.cpp:409-413`). Reads `_motors.get_throttle_hover()`. -/
def get_throttle_avg_max (s : State) (m : AP_Motors.Inputs) (throttle_in : ftype) : ftype :=
  let throttle_in := constrain_float throttle_in 0.0 1.0
  MAX throttle_in (throttle_in * MAX 0.0 (1.0 - s._throttle_rpy_mix)
    + AP_Motors.get_throttle_hover m * s._throttle_rpy_mix)

/-- `set_throttle_out(throttle_in, apply_angle_boost, filter_cutoff)` (`.cpp:364-378`); returns the
state and the motors record after `set_throttle_filter_cutoff`, `set_throttle`,
`set_throttle_avg_max`. -/
def set_throttle_out (p : Params) (s : State) (m : AP_Motors.Inputs) (ahrs_cos_pitch ahrs_cos_roll : ftype)
    (throttle_in : ftype) (apply_angle_boost : Bool) (filter_cutoff : ftype) : State × AP_Motors.Inputs :=
  let s := { s with _throttle_in := throttle_in }
  let s := update_althold_lean_angle_max p s m throttle_in
  let m := AP_Motors.set_throttle_filter_cutoff m filter_cutoff
  let (s, throttle_in) :=
    if apply_angle_boost then
      -- Apply angle boost
      get_throttle_boosted p s ahrs_cos_pitch ahrs_cos_roll throttle_in
    else
      -- Clear angle_boost for logging purposes
      ({ s with _angle_boost := 0.0 }, throttle_in)
  let m := AP_Motors.set_throttle m throttle_in
  let m := AP_Motors.set_throttle_avg_max m (get_throttle_avg_max s m (MAX throttle_in s._throttle_in))
  (s, m)

/-! ### Rate controller, `.cpp:416-426`, `:456-491` -/

/-- `update_throttle_gain_boost` (`.cpp:416-426`). `motors_throttle_slew_rate` is
`_motors.get_throttle_slew_rate()`. -/
def update_throttle_gain_boost (p : Params) (s : State) (motors_throttle_slew_rate : ftype) : State :=
  -- Boost PD and Angle P on very rapid throttle changes
  if motors_throttle_slew_rate > AC_ATTITUDE_CONTROL_THR_G_BOOST_THRESH then
    let pd_boost := constrain_float (p.ATC_THR_G_BOOST + 1.0) 1.0 2.0
    let s := lift (fun b => AC_AttitudeControl.set_PD_scale_mult b ⟨pd_boost, pd_boost, 1.0⟩) s
    let angle_p_boost :=
      constrain_float ((p.ATC_THR_G_BOOST + 1.0) * (p.ATC_THR_G_BOOST + 1.0)) 1.0 4.0
    lift (fun b => AC_AttitudeControl.set_angle_P_scale_mult b ⟨angle_p_boost, angle_p_boost, 1.0⟩) s
  else s

/-- `rate_controller_run_dt(gyro_rads, dt)` (`.cpp:456-484`). Consumes `_ang_vel_body_rads`
as stored by the attitude controller (in ArduCopter, on the previous tick); stores `gyro_rads` as
`_rate_gyro_rads`; updates the three rate PIDs; returns the state and the motors record after
`set_roll`, `set_roll_ff`, `set_pitch`, `set_pitch_ff`, `set_yaw`, `set_yaw_ff`. The anti-windup
flags are `m.limit.roll/pitch/yaw` as passed in. -/
def rate_controller_run_dt (p : Params) (s : State) (m : AP_Motors.Inputs)
    (motors_throttle_slew_rate : ftype) (gyro_rads : Vector3f) (dt : ftype) : State × AP_Motors.Inputs :=
  -- take a copy of the target so that it can't be changed from under us.
  let ang_vel_body := s._ang_vel_body_rads
  -- boost angle_p/pd each cycle on high throttle slew
  let s := update_throttle_gain_boost p s motors_throttle_slew_rate
  -- move throttle vs attitude mixing towards desired
  let s := update_throttle_rpy_mix s m
  let ang_vel_body := ang_vel_body + s._sysid_ang_vel_body_rads
  let s := { s with _rate_gyro_rads := gyro_rads }
  let (pid_roll, roll_out) := AC_PID.update_all (get_rate_roll_pid p) s._pid_rate_roll ang_vel_body.x
    gyro_rads.x dt m.limit.roll s._pd_scale.x s._i_scale.x
  let m := AP_Motors.set_roll m (roll_out + s._actuator_sysid.x)
  let m := AP_Motors.set_roll_ff m (AC_PID.get_ff pid_roll)
  let (pid_pitch, pitch_out) := AC_PID.update_all (get_rate_pitch_pid p) s._pid_rate_pitch ang_vel_body.y
    gyro_rads.y dt m.limit.pitch s._pd_scale.y s._i_scale.y
  let m := AP_Motors.set_pitch m (pitch_out + s._actuator_sysid.y)
  let m := AP_Motors.set_pitch_ff m (AC_PID.get_ff pid_pitch)
  let (pid_yaw, yaw_out) := AC_PID.update_all (get_rate_yaw_pid p) s._pid_rate_yaw ang_vel_body.z
    gyro_rads.z dt m.limit.yaw s._pd_scale.z s._i_scale.z
  let m := AP_Motors.set_yaw m (yaw_out + s._actuator_sysid.z)
  let m := AP_Motors.set_yaw_ff m (AC_PID.get_ff pid_yaw * s._feedforward_scalar)
  let s := { s with _pid_rate_roll := pid_roll, _pid_rate_pitch := pid_pitch, _pid_rate_yaw := pid_yaw }
  let s := { s with _pd_scale_used := s._pd_scale, _i_scale_used := s._i_scale,
                    _angle_P_scale_used := s._angle_P_scale }
  (s, m)

/-- `rate_controller_run()` (`.cpp:487-491`): `rate_controller_run_dt(_ahrs.get_gyro_latest(),
_dt_s)`; `gyro_latest_rads` is `_ahrs.get_gyro_latest()`. -/
def rate_controller_run (p : Params) (s : State) (m : AP_Motors.Inputs) (motors_throttle_slew_rate : ftype)
    (gyro_latest_rads : Vector3f) : State × AP_Motors.Inputs :=
  rate_controller_run_dt p s m motors_throttle_slew_rate gyro_latest_rads s._dt_s

/-! ### Base-class methods with the derived class's PIDs filled in -/

/-- `set_dt_s` (`AC_AttitudeControl.h:74`). -/
def set_dt_s (s : State) (dt_s : ftype) : State := lift (AC_AttitudeControl.set_dt_s · dt_s) s

/-- `rate_controller_target_reset` (`AC_AttitudeControl.cpp:289-296`). -/
def rate_controller_target_reset (s : State) : State := lift AC_AttitudeControl.rate_controller_target_reset s

/-- `set_yaw_rate_tc` (`AC_AttitudeControl.h:507`). -/
def set_yaw_rate_tc (s : State) (input_tc : ftype) : State := lift (AC_AttitudeControl.set_yaw_rate_tc · input_tc) s

/-- `attitude_controller_run_quat` (`AC_AttitudeControl.cpp:989-1029`). -/
def attitude_controller_run_quat (p : Params) (s : State) (attitude_body : Quaternion) : State :=
  lift (AC_AttitudeControl.attitude_controller_run_quat p.toParams (get_rate_yaw_pid p) · attitude_body) s

/-- `input_thrust_vector_rate_heading_rads` (`AC_AttitudeControl.cpp:832-885`). -/
def input_thrust_vector_rate_heading_rads (p : Params) (s : State) (attitude_body : Quaternion)
    (thrust_vector : Vector3f) (heading_rate_rads : ftype) (slew_yaw : Bool := true) : State :=
  lift (fun b => AC_AttitudeControl.input_thrust_vector_rate_heading_rads p.toParams (get_rate_yaw_pid p) b
    attitude_body thrust_vector heading_rate_rads slew_yaw) s

/-- `input_thrust_vector_heading_rad(thrust_vector, heading_angle_rad, heading_rate_rads)`
(`AC_AttitudeControl.cpp:890-929`). -/
def input_thrust_vector_heading_rad (p : Params) (s : State) (attitude_body : Quaternion)
    (thrust_vector : Vector3f) (heading_angle_rad heading_rate_rads : ftype) : State :=
  lift (fun b => AC_AttitudeControl.input_thrust_vector_heading_rad p.toParams (get_rate_yaw_pid p) b
    attitude_body thrust_vector heading_angle_rad heading_rate_rads) s

/-- `input_thrust_vector_heading(thrust_vector, HeadingCommand)` (`AC_AttitudeControl.cpp:932-945`). -/
def input_thrust_vector_heading (p : Params) (s : State) (attitude_body : Quaternion)
    (thrust_vector : Vector3f) (heading : HeadingCommand) : State :=
  lift (fun b => AC_AttitudeControl.input_thrust_vector_heading p.toParams (get_rate_yaw_pid p) b
    attitude_body thrust_vector heading) s

/-- `reset_rate_controller_I_terms` (`AC_AttitudeControl.cpp:273-278`). -/
def reset_rate_controller_I_terms (s : State) : State :=
  let (r, q, y) := AC_AttitudeControl.reset_rate_controller_I_terms s._pid_rate_roll s._pid_rate_pitch
    s._pid_rate_yaw
  { s with _pid_rate_roll := r, _pid_rate_pitch := q, _pid_rate_yaw := y }

/-- `reset_rate_controller_I_terms_smoothly` (`AC_AttitudeControl.cpp:281-286`). -/
def reset_rate_controller_I_terms_smoothly (p : Params) (s : State) : State :=
  let (r, q, y) := AC_AttitudeControl.reset_rate_controller_I_terms_smoothly s.toState
    (get_rate_roll_pid p) (get_rate_pitch_pid p) (get_rate_yaw_pid p)
    s._pid_rate_roll s._pid_rate_pitch s._pid_rate_yaw
  { s with _pid_rate_roll := r, _pid_rate_pitch := q, _pid_rate_yaw := y }

/-- `relax_attitude_controllers` (`AC_AttitudeControl.cpp:246-271`). -/
def relax_attitude_controllers (s : State) (attitude_body : Quaternion) : State :=
  let (b, r, q, y) := AC_AttitudeControl.relax_attitude_controllers s.toState attitude_body
    s._pid_rate_roll s._pid_rate_pitch s._pid_rate_yaw
  { s with toState := b, _pid_rate_roll := r, _pid_rate_pitch := q, _pid_rate_yaw := y }

/-- `reset_target_and_rate` (`AC_AttitudeControl.cpp:1252-1263`). -/
def reset_target_and_rate (s : State) (attitude_body : Quaternion) (reset_rate : Bool := true) : State :=
  lift (AC_AttitudeControl.reset_target_and_rate · attitude_body reset_rate) s

/-- `reset_yaw_target_and_rate` (`AC_AttitudeControl.cpp:1267-1283`). -/
def reset_yaw_target_and_rate (s : State) (ahrs_yaw : ftype) (reset_rate : Bool := true) : State :=
  lift (AC_AttitudeControl.reset_yaw_target_and_rate · ahrs_yaw reset_rate) s

/-- `inertial_frame_reset` (`AC_AttitudeControl.cpp:1286-1297`). -/
def inertial_frame_reset (s : State) (attitude_body : Quaternion) : State :=
  lift (AC_AttitudeControl.inertial_frame_reset · attitude_body) s

end AC_AttitudeControl_Multi
