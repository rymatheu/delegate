import AP_Math
import AC_PID.AC_P
import AC_PID.AC_PID

/-!
# `AC_AttitudeControl`, the base class

Mirrors, at ArduPilot 802db19de1, `libraries/AC_AttitudeControl/AC_AttitudeControl.h`
(`:15-45` constants, `:47-722` the class: members `:561-707`, `HeadingMode`/`HeadingCommand`
`:711-721`) and `AC_AttitudeControl.cpp`:
`:9-27` Copter build constants, `:32-206` `var_info` (as `Params`), `:211-217`
`get_slew_yaw_max_rads`, `:233-243` `get_latest_gyro`, `:246-271` `relax_attitude_controllers`,
`:273-286` `reset_rate_controller_I_terms(_smoothly)`, `:289-296` `rate_controller_target_reset`,
`:832-885` `input_thrust_vector_rate_heading_rads`, `:890-929` `input_thrust_vector_heading_rad`,
`:932-945` `input_thrust_vector_heading`, `:947-976` `attitude_from_thrust_vector`, `:979-986`
`update_attitude_target`, `:989-1029` `attitude_controller_run_quat`, `:1033-1052`
`thrust_heading_rotation_angles`, `:1056-1104` `thrust_vector_rotation_angles`, `:1108-1130`
`attitude_command_model`, `:1206-1226` `ang_vel_limit`, `:1252-1297` `reset_target_and_rate`,
`reset_yaw_target_and_rate`, `inertial_frame_reset`, `:1303-1342` `euler_derivative_to_body`,
`body_to_euler_derivative`, `:1345-1374` `update_ang_vel_target_from_att_error`, `:1399-1422`
`get_althold_lean_angle_max_cd/rad`, `lean_angle_max_cd/rad`; and the inline accessors of
`AC_AttitudeControl.h:74-142`, `:330-345`, `:384-387`, `:408-429`, `:487`, `:504-526`.

Build configuration: Copter (`APM_BUILD_ArduCopter`), so `AC_ATTITUDE_CONTROL_INPUT_TC_DEFAULT =
0.10`, `AC_ATTITUDE_CONTROL_ANGLE_LIMIT_MIN = 10`, `AC_ATTITUDE_CONTROL_AFTER_RATE_CONTROL = 1`
(`AC_AttitudeControl.cpp:14-19`). All literals are `float` (`-fsingle-precision-constant`, see
`AP_Math/definitions.lean`).

## Conventions

- `Params` is the `AP_Param` table with the ArduPilot parameter names (`ATC_` prefix of Copter's
  `attitude_control` group); its defaults are the `var_info` defaults. The angle P objects
  `_p_angle_roll/pitch/yaw` are the `AC_P` subgroups `ATC_ANG_RLL_`, `ATC_ANG_PIT_`, `ATC_ANG_YAW_`, so
  `p.ATC_ANG_RLL.P` is `ATC_ANG_RLL_P`. Accessors named as the C++ members (`_input_tc`,
  `_rate_bf_ff_enabled`, ...) are provided so the bodies read as the C++.
  Parameter names at this commit: `ATC_ACC_R_MAX`/`ATC_ACC_P_MAX`/`ATC_ACC_Y_MAX` (formerly
  `ATC_ACCEL_*_MAX`) and `ATC_RATE_WPY_MAX` (formerly `ATC_SLEW_YAW`), `AC_AttitudeControl.cpp:36-49`.
- `State` holds the non-parameter members, with the C++ names and their initial values (the
  constructor initialisers of `AC_AttitudeControl.h:49-63`, the in-class initialisers, and zero for
  the rest, since ArduPilot zero-fills objects). `Quaternion`'s default is the identity.
- Every mutating method is a pure function `Params → State → inputs → State` (or `State × out`).
  C++ reference out-parameters become return values, in parameter order.
- AHRS reads become explicit arguments placed after the state, before the C++ arguments:
  `attitude_body` is `_ahrs.get_quat_body_to_ned(...)` and `ahrs_yaw` is `_ahrs.yaw`.
- The rate PIDs belong to the derived class and are reached through the pure-virtual
  `get_rate_roll_pid()` etc. (`AC_AttitudeControl.h:83-88`). Base methods that use them take the
  PID parameters (`get_rate_yaw_pid : AC_PID.Params`) and, when they mutate them, the PID states as
  explicit arguments, and return the updated PID states. `AC_AttitudeControl_Multi` wraps them.
- The gyro used by the attitude controller is `get_latest_gyro()`, which for Copter
  (`AC_ATTITUDE_CONTROL_AFTER_RATE_CONTROL = 1`) is the stored `_rate_gyro_rads` written by the last
  `rate_controller_run_dt`, not an AHRS read; it is therefore state, not an argument.

## Left out

- The `input_euler_*`, `input_rate_*`, `input_quaternion`, `input_angle_step_*` and
  `input_rate_step_*` entry points (`:344-826`), `body_to_euler_limit` (`:1229-1248`, used only by
  them) and `command_model_rate_predictor` (`:1134-1152`): other modes. Note that
  `Mode::make_safe_ground_handling` (`mode.cpp:663-690`, the Auto ground path) calls
  `input_euler_angle_roll_pitch_euler_rate_yaw_rad`, which is therefore not available here.
- `landed_gain_reduction` (`:299-315`) and the `ATC_LAND_*_MULT` parameters. Its only effect is
  `_pd_scale *= m` and `_angle_P_scale *= m` with `m = (1,1,1)·(1 - r) + (LAND_R, LAND_P, LAND_Y)·r`.
  Not landed and starting from `r = 0`, `r` stays `MAX(0, 0 - step) = 0`, so `m = 1·1 + LAND·0 =
  (1,1,1)` exactly for finite multipliers, and multiplying by 1 is the identity. When landed with
  the default multipliers (1.0) `m` is `(1 - r)·1 + 1·r`; evaluated in `Float32` over the whole ramp
  `r := MIN(1, r + dt/(2·0.1))` and back down at `dt = 0.0025` (200 ticks each way) it is exactly 1
  at every tick, so the default configuration needs no landed model either.
- `_rate_gyro_time_us` (timestamp, `AP_HAL::micros64`), `_landed_gain_ratio`, `_singleton`,
  `max_rate_step_bf_*`, `pre_arm_checks`, `get_rpy_srate`, `convert_parameters`, `scale_I_to_angle_P`,
  `accel_limiting`, `use_sqrt_controller`, the sysid setters (`rate_bf_*_sysid_rads`,
  `actuator_*_sysid`), the `set_*_max_*` parameter setters, `Write_Rate`/`Write_ANG` (logging), the
  `AP_Param` plumbing, the custom-controller hook, and the tailsitter/heli virtuals (no-ops for
  Multi). `_sysid_ang_vel_body_rads` and `_actuator_sysid` are kept as state because
  `rate_controller_run_dt` adds them (adding `+0` turns `-0` into `+0`), but nothing here sets them:
  they stay zero, as `rate_controller_target_reset` re-zeroes them every tick in ArduCopter.
- `_disturb_*` does not exist at this commit.
-/

namespace AC_AttitudeControl

open AP_Math

/-! ### Constants, `AC_AttitudeControl.h:15-45`, `AC_AttitudeControl.cpp:9-27` -/

/-- `AC_ATTITUDE_CONTROL_ANGLE_P` (`.h:15`). -/
def AC_ATTITUDE_CONTROL_ANGLE_P : ftype := 4.5
/-- `AC_ATTITUDE_ACCEL_RP_CONTROLLER_MIN_RADSS` = `radians(40.0f)` (`.h:17`). -/
def AC_ATTITUDE_ACCEL_RP_CONTROLLER_MIN_RADSS : ftype := radians 40.0
/-- `AC_ATTITUDE_ACCEL_RP_CONTROLLER_MAX_RADSS` = `radians(720.0f)` (`.h:18`). -/
def AC_ATTITUDE_ACCEL_RP_CONTROLLER_MAX_RADSS : ftype := radians 720.0
/-- `AC_ATTITUDE_ACCEL_Y_CONTROLLER_MIN_RADSS` = `radians(10.0f)` (`.h:19`). -/
def AC_ATTITUDE_ACCEL_Y_CONTROLLER_MIN_RADSS : ftype := radians 10.0
/-- `AC_ATTITUDE_ACCEL_Y_CONTROLLER_MAX_RADSS` = `radians(120.0f)` (`.h:20`). -/
def AC_ATTITUDE_ACCEL_Y_CONTROLLER_MAX_RADSS : ftype := radians 120.0
/-- `AC_ATTITUDE_CONTROL_RATE_WPY_MAX_DEFAULT` (`.h:21`). -/
def AC_ATTITUDE_CONTROL_RATE_WPY_MAX_DEFAULT : ftype := 60.0
/-- `AC_ATTITUDE_CONTROL_ACCEL_RP_MAX_DEFAULT_DEGSS` (`.h:22`). -/
def AC_ATTITUDE_CONTROL_ACCEL_RP_MAX_DEFAULT_DEGSS : ftype := 1100.0
/-- `AC_ATTITUDE_CONTROL_ACCEL_Y_MAX_DEFAULT_DEGSS` (`.h:23`). -/
def AC_ATTITUDE_CONTROL_ACCEL_Y_MAX_DEFAULT_DEGSS : ftype := 270.0
/-- `AC_ATTITUDE_RATE_RELAX_TC` (`.h:27`). -/
def AC_ATTITUDE_RATE_RELAX_TC : ftype := 0.16
/-- `AC_ATTITUDE_THRUST_ERROR_ANGLE_RAD` = `radians(30.0f)` (`.h:29`). -/
def AC_ATTITUDE_THRUST_ERROR_ANGLE_RAD : ftype := radians 30.0
/-- `AC_ATTITUDE_YAW_MAX_ERROR_ANGLE_RAD` = `radians(45.0f)` (`.h:30`). -/
def AC_ATTITUDE_YAW_MAX_ERROR_ANGLE_RAD : ftype := radians 45.0
/-- `AC_ATTITUDE_CONTROL_RATE_BF_FF_DEFAULT` (`.h:32`). -/
def AC_ATTITUDE_CONTROL_RATE_BF_FF_DEFAULT : Int8 := 1
/-- `AC_ATTITUDE_CONTROL_ANGLE_LIMIT_TC_DEFAULT` (`.h:34`). -/
def AC_ATTITUDE_CONTROL_ANGLE_LIMIT_TC_DEFAULT : ftype := 1.0
/-- `AC_ATTITUDE_CONTROL_ANGLE_LIMIT_THROTTLE_MAX` (`.h:35`). -/
def AC_ATTITUDE_CONTROL_ANGLE_LIMIT_THROTTLE_MAX : ftype := 0.8
/-- `AC_ATTITUDE_CONTROL_MIN_DEFAULT` (`.h:37`). -/
def AC_ATTITUDE_CONTROL_MIN_DEFAULT : ftype := 0.1
/-- `AC_ATTITUDE_CONTROL_MAN_DEFAULT` (`.h:38`). -/
def AC_ATTITUDE_CONTROL_MAN_DEFAULT : ftype := 0.1
/-- `AC_ATTITUDE_CONTROL_MAX_DEFAULT` (`.h:39`). -/
def AC_ATTITUDE_CONTROL_MAX_DEFAULT : ftype := 0.5
/-- `AC_ATTITUDE_CONTROL_MAX` (`.h:42`). -/
def AC_ATTITUDE_CONTROL_MAX : ftype := 5.0
/-- `AC_ATTITUDE_CONTROL_THR_MIX_DEFAULT` (`.h:44`). -/
def AC_ATTITUDE_CONTROL_THR_MIX_DEFAULT : ftype := 0.5
/-- `AC_ATTITUDE_CONTROL_THR_G_BOOST_THRESH` (`.h:45`). -/
def AC_ATTITUDE_CONTROL_THR_G_BOOST_THRESH : ftype := 1.0
/-- `AC_ATTITUDE_CONTROL_INPUT_TC_DEFAULT`, Copter (`.cpp:16`). -/
def AC_ATTITUDE_CONTROL_INPUT_TC_DEFAULT : ftype := 0.10
/-- `AC_ATTITUDE_CONTROL_ANGLE_LIMIT_MIN`, Copter (`.cpp:17`). -/
def AC_ATTITUDE_CONTROL_ANGLE_LIMIT_MIN : ftype := 10.0
/-- `AC_ATTITUDE_CONTROL_ANGLE_LIMIT_MAX` (`.cpp:22`). -/
def AC_ATTITUDE_CONTROL_ANGLE_LIMIT_MAX : ftype := 80.0
/-- `AC_ATTITUDE_CONTROL_ANGLE_MAX_DEFAULT` (`.cpp:26`). -/
def AC_ATTITUDE_CONTROL_ANGLE_MAX_DEFAULT : ftype := 30.0
/-- `VECTORF_111` (`.h:549`). -/
def VECTORF_111 : Vector3f := ⟨1.0, 1.0, 1.0⟩

/-! ### Parameters, `var_info` (`AC_AttitudeControl.cpp:32-206`) -/

/-- The `AC_AttitudeControl` parameter table, Copter defaults. -/
structure Params where
  /-- `_rate_bf_ff_enabled` (`.cpp:47`). -/
  ATC_RATE_FF_ENAB : Int8 := AC_ATTITUDE_CONTROL_RATE_BF_FF_DEFAULT
  /-- `_angle_boost_enabled` (`.cpp:60`). -/
  ATC_ANGLE_BOOST : Int8 := 1
  /-- `_p_angle_roll`, subgroup `ANG_RLL_` (`.cpp:69`; initial P from `.h:51`). -/
  ATC_ANG_RLL : AC_P.Params := AC_P.init AC_ATTITUDE_CONTROL_ANGLE_P
  /-- `_p_angle_pitch`, subgroup `ANG_PIT_` (`.cpp:78`). -/
  ATC_ANG_PIT : AC_P.Params := AC_P.init AC_ATTITUDE_CONTROL_ANGLE_P
  /-- `_p_angle_yaw`, subgroup `ANG_YAW_` (`.cpp:87`). -/
  ATC_ANG_YAW : AC_P.Params := AC_P.init AC_ATTITUDE_CONTROL_ANGLE_P
  /-- `_angle_limit_tc` (`.cpp:94`). -/
  ATC_ANG_LIM_TC : ftype := AC_ATTITUDE_CONTROL_ANGLE_LIMIT_TC_DEFAULT
  /-- `_ang_vel_roll_max_degs` (`.cpp:104`), deg/s, 0 = unlimited. -/
  ATC_RATE_R_MAX : ftype := 0.0
  /-- `_ang_vel_pitch_max_degs` (`.cpp:114`). -/
  ATC_RATE_P_MAX : ftype := 0.0
  /-- `_ang_vel_yaw_max_degs` (`.cpp:124`). -/
  ATC_RATE_Y_MAX : ftype := 0.0
  /-- `_input_tc` (`.cpp:134`), s. -/
  ATC_INPUT_TC : ftype := AC_ATTITUDE_CONTROL_INPUT_TC_DEFAULT
  /-- `_angle_max_deg` (`.cpp:164`), deg. -/
  ATC_ANGLE_MAX : ftype := AC_ATTITUDE_CONTROL_ANGLE_MAX_DEFAULT
  /-- `_rate_wp_yaw_max_degs` (`.cpp:173`), deg/s. -/
  ATC_RATE_WPY_MAX : ftype := AC_ATTITUDE_CONTROL_RATE_WPY_MAX_DEFAULT
  /-- `_accel_yaw_max_degss` (`.cpp:183`), deg/s². -/
  ATC_ACC_Y_MAX : ftype := AC_ATTITUDE_CONTROL_ACCEL_Y_MAX_DEFAULT_DEGSS
  /-- `_accel_roll_max_degss` (`.cpp:193`), deg/s². -/
  ATC_ACC_R_MAX : ftype := AC_ATTITUDE_CONTROL_ACCEL_RP_MAX_DEFAULT_DEGSS
  /-- `_accel_pitch_max_degss` (`.cpp:203`), deg/s². -/
  ATC_ACC_P_MAX : ftype := AC_ATTITUDE_CONTROL_ACCEL_RP_MAX_DEFAULT_DEGSS
deriving Repr

namespace Params
/-- `_rate_bf_ff_enabled`, read as a C++ boolean. -/
def _rate_bf_ff_enabled (p : Params) : Bool := p.ATC_RATE_FF_ENAB != 0
/-- `_angle_boost_enabled`, read as a C++ boolean. -/
def _angle_boost_enabled (p : Params) : Bool := p.ATC_ANGLE_BOOST != 0
def _p_angle_roll (p : Params) : AC_P.Params := p.ATC_ANG_RLL
def _p_angle_pitch (p : Params) : AC_P.Params := p.ATC_ANG_PIT
def _p_angle_yaw (p : Params) : AC_P.Params := p.ATC_ANG_YAW
def _angle_limit_tc (p : Params) : ftype := p.ATC_ANG_LIM_TC
def _ang_vel_roll_max_degs (p : Params) : ftype := p.ATC_RATE_R_MAX
def _ang_vel_pitch_max_degs (p : Params) : ftype := p.ATC_RATE_P_MAX
def _ang_vel_yaw_max_degs (p : Params) : ftype := p.ATC_RATE_Y_MAX
def _input_tc (p : Params) : ftype := p.ATC_INPUT_TC
def _angle_max_deg (p : Params) : ftype := p.ATC_ANGLE_MAX
def _rate_wp_yaw_max_degs (p : Params) : ftype := p.ATC_RATE_WPY_MAX
def _accel_roll_max_degss (p : Params) : ftype := p.ATC_ACC_R_MAX
def _accel_pitch_max_degss (p : Params) : ftype := p.ATC_ACC_P_MAX
def _accel_yaw_max_degss (p : Params) : ftype := p.ATC_ACC_Y_MAX
end Params

/-! ### State, `AC_AttitudeControl.h:603-701` -/

/-- The non-parameter members of `AC_AttitudeControl`. -/
structure State where
  /-- Latest gyro used by the rate controller (`.h:604`), written by `rate_controller_run_dt`. -/
  _rate_gyro_rads : Vector3f := {}
  /-- `_dt_s` (`.h:609`). -/
  _dt_s : ftype := 0
  /-- 321 Euler angles of `_attitude_target` (`.h:613`). -/
  _euler_angle_target_rad : Vector3f := {}
  /-- Euler-angle derivative of the target (`.h:618`). -/
  _euler_rate_target_rads : Vector3f := {}
  /-- Target attitude, body to NED (`.h:622`). -/
  _attitude_target : Quaternion := {}
  /-- Target angular velocity in the target frame (`.h:627`). -/
  _ang_vel_target_rads : Vector3f := {}
  /-- Target angular acceleration (`.h:628`). -/
  _ang_accel_target_rads : Vector3f := {}
  /-- Body-frame rate target consumed by the rate controller (`.h:632`). -/
  _ang_vel_body_rads : Vector3f := {}
  /-- System-identification rate offset (`.h:637`); always zero here. -/
  _sysid_ang_vel_body_rads : Vector3f := {}
  /-- System-identification actuator offset (`.h:642`); always zero here. -/
  _actuator_sysid : Vector3f := {}
  /-- Body-frame attitude error kept for EKF resets (`.h:645`). -/
  _attitude_ang_error : Quaternion := {}
  /-- Current tilt angle (`.h:648`). -/
  _thrust_angle_rad : ftype := 0
  /-- Angle between target and current thrust vectors (`.h:651`). -/
  _thrust_error_angle_rad : ftype := 0
  /-- Throttle passed to `set_throttle_out`, before angle boost (`.h:654`). -/
  _throttle_in : ftype := 0.0
  /-- `_angle_boost` (`.h:658`, initialised to 0 at `.h:54`). -/
  _angle_boost : ftype := 0
  /-- `_use_sqrt_controller` (`.h:662`, initialised to true at `.h:55`). -/
  _use_sqrt_controller : Bool := true
  /-- `_althold_lean_angle_max_rad` (`.h:665`). -/
  _althold_lean_angle_max_rad : ftype := 0.0
  /-- `_throttle_rpy_mix_desired` (`.h:668`, initialised at `.h:56`). -/
  _throttle_rpy_mix_desired : ftype := AC_ATTITUDE_CONTROL_THR_MIX_DEFAULT
  /-- `_throttle_rpy_mix` (`.h:671`, initialised at `.h:57`). -/
  _throttle_rpy_mix : ftype := AC_ATTITUDE_CONTROL_THR_MIX_DEFAULT
  /-- `_feedforward_scalar` (`.h:674`). -/
  _feedforward_scalar : ftype := 1.0
  /-- `_rate_rp_tc` (`.h:678`): set by Copter's `set_mode` from `ACRO_RP_RATE_TC` (default 0). -/
  _rate_rp_tc : ftype := 0
  /-- `_rate_y_tc` (`.h:680`): set by Copter's `set_mode` from `PILOT_Y_RATE_TC` (default 0,
  `ArduCopter/Parameters.cpp:1249`); `attitude_command_model` then uses `10·dt`. -/
  _rate_y_tc : ftype := 0
  /-- `_angle_P_scale` (`.h:683`). -/
  _angle_P_scale : Vector3f := VECTORF_111
  /-- `_angle_P_scale_used` (`.h:686`). -/
  _angle_P_scale_used : Vector3f := {}
  /-- `_pd_scale` (`.h:689`). -/
  _pd_scale : Vector3f := VECTORF_111
  /-- `_pd_scale_used` (`.h:692`). -/
  _pd_scale_used : Vector3f := {}
  /-- `_i_scale` (`.h:695`). -/
  _i_scale : Vector3f := VECTORF_111
  /-- `_i_scale_used` (`.h:698`). -/
  _i_scale_used : Vector3f := {}
deriving Repr

/-- `HeadingMode` (`.h:711-715`). -/
inductive HeadingMode where
  | Angle_Only
  | Angle_And_Rate
  | Rate_Only
deriving Repr, DecidableEq

/-- `HeadingCommand` (`.h:716-720`). -/
structure HeadingCommand where
  yaw_angle_rad : ftype
  yaw_rate_rads : ftype
  heading_mode : HeadingMode
deriving Repr

/-! ### Accessors -/

/-- `set_dt_s` (`.h:74`). -/
def set_dt_s (s : State) (dt_s : ftype) : State := { s with _dt_s := dt_s }
/-- `get_dt_s` (`.h:77`). -/
def get_dt_s (s : State) : ftype := s._dt_s

/-- `get_accel_roll_max_radss` (`.h:91`). -/
def get_accel_roll_max_radss (p : Params) : ftype := radians p._accel_roll_max_degss
/-- `get_accel_pitch_max_radss` (`.h:100`). -/
def get_accel_pitch_max_radss (p : Params) : ftype := radians p._accel_pitch_max_degss
/-- `get_accel_yaw_max_radss` (`.h:109`). -/
def get_accel_yaw_max_radss (p : Params) : ftype := radians p._accel_yaw_max_degss
/-- `get_ang_vel_roll_max_rads` (`.h:118`). -/
def get_ang_vel_roll_max_rads (p : Params) : ftype := radians p._ang_vel_roll_max_degs
/-- `get_ang_vel_pitch_max_rads` (`.h:124`). -/
def get_ang_vel_pitch_max_rads (p : Params) : ftype := radians p._ang_vel_pitch_max_degs
/-- `get_ang_vel_yaw_max_rads` (`.h:130`). -/
def get_ang_vel_yaw_max_rads (p : Params) : ftype := radians p._ang_vel_yaw_max_degs
/-- `get_input_tc` (`.h:139`). -/
def get_input_tc (p : Params) : ftype := p._input_tc

/-- `get_slew_yaw_max_rads` (`.cpp:211-217`). -/
def get_slew_yaw_max_rads (p : Params) : ftype :=
  if !is_positive p._ang_vel_yaw_max_degs then
    radians p._rate_wp_yaw_max_degs
  else
    MIN (radians p._ang_vel_yaw_max_degs) (radians p._rate_wp_yaw_max_degs)

/-- `get_latest_gyro` (`.cpp:233-243`) with `AC_ATTITUDE_CONTROL_AFTER_RATE_CONTROL = 1`:
the gyro stored by the last `rate_controller_run_dt`. -/
def get_latest_gyro (s : State) : Vector3f := s._rate_gyro_rads

/-- `get_att_target_euler_cd` (`.h:330`): `_euler_angle_target_rad * degrees(100.0f)`. -/
def get_att_target_euler_cd (s : State) : Vector3f := s._euler_angle_target_rad * degrees 100.0
/-- `get_att_target_euler_rad` (`.h:331`). -/
def get_att_target_euler_rad (s : State) : Vector3f := s._euler_angle_target_rad
/-- `get_attitude_target_quat` (`.h:335`). -/
def get_attitude_target_quat (s : State) : Quaternion := s._attitude_target
/-- `get_attitude_target_ang_vel` (`.h:338`). -/
def get_attitude_target_ang_vel (s : State) : Vector3f := s._ang_vel_target_rads
/-- `get_att_error_angle_deg` (`.h:341`). -/
def get_att_error_angle_deg (s : State) : ftype := degrees s._thrust_error_angle_rad
/-- `rate_bf_targets` (`.h:384`). -/
def rate_bf_targets (s : State) : Vector3f := s._ang_vel_body_rads + s._sysid_ang_vel_body_rads
/-- `get_rate_ef_target_rads` (`.h:387`). -/
def get_rate_ef_target_rads (s : State) : Vector3f := s._euler_rate_target_rads
/-- `get_bf_feedforward` (`.h:396`). -/
def get_bf_feedforward (p : Params) : Bool := p._rate_bf_ff_enabled
/-- `get_throttle_in` (`.h:408`). -/
def get_throttle_in (s : State) : ftype := s._throttle_in
/-- `angle_boost` (`.h:411`). -/
def angle_boost (s : State) : ftype := s._angle_boost
/-- `lean_angle_deg` (`.h:428`). -/
def lean_angle_deg (s : State) : ftype := degrees s._thrust_angle_rad
/-- `lean_angle_rad` (`.h:429`). -/
def lean_angle_rad (s : State) : ftype := s._thrust_angle_rad
/-- `get_roll_trim_cd` (`.h:483`): 0 except for heli. -/
def get_roll_trim_cd (_s : State) : ftype := 0
/-- `get_roll_trim_rad` (`.h:487`). -/
def get_roll_trim_rad (s : State) : ftype := cd_to_rad (get_roll_trim_cd s)
/-- `set_roll_pitch_rate_tc` (`.h:504`). -/
def set_roll_pitch_rate_tc (s : State) (input_tc : ftype) : State := { s with _rate_rp_tc := input_tc }
/-- `set_yaw_rate_tc` (`.h:507`). -/
def set_yaw_rate_tc (s : State) (input_tc : ftype) : State := { s with _rate_y_tc := input_tc }

/-- `Vector3f::operator*=(const Vector3f&)` (`vector3.h:130-133`), non-uniform scaling. -/
def vec_mul_assign (a v : Vector3f) : Vector3f := ⟨a.x * v.x, a.y * v.y, a.z * v.z⟩

/-- `set_angle_P_scale` (`.h:511`). -/
def set_angle_P_scale (s : State) (angle_P_scale : Vector3f) : State :=
  { s with _angle_P_scale := angle_P_scale }
/-- `set_angle_P_scale_mult` (`.h:517`). -/
def set_angle_P_scale_mult (s : State) (angle_P_scale : Vector3f) : State :=
  { s with _angle_P_scale := vec_mul_assign s._angle_P_scale angle_P_scale }
/-- `get_last_angle_P_scale` (`.h:520`). -/
def get_last_angle_P_scale (s : State) : Vector3f := s._angle_P_scale_used
/-- `set_PD_scale_mult` (`.h:526`). -/
def set_PD_scale_mult (s : State) (pd_scale : Vector3f) : State :=
  { s with _pd_scale := vec_mul_assign s._pd_scale pd_scale }
/-- `set_I_scale_mult` (`.h:532`). -/
def set_I_scale_mult (s : State) (i_scale : Vector3f) : State :=
  { s with _i_scale := vec_mul_assign s._i_scale i_scale }

/-- `get_althold_lean_angle_max_rad` (`.cpp:1407-1410`). -/
def get_althold_lean_angle_max_rad (s : State) : ftype :=
  MAX s._althold_lean_angle_max_rad (radians AC_ATTITUDE_CONTROL_ANGLE_LIMIT_MIN)
/-- `get_althold_lean_angle_max_cd` (`.cpp:1399-1403`). -/
def get_althold_lean_angle_max_cd (s : State) : ftype := rad_to_cd (get_althold_lean_angle_max_rad s)
/-- `lean_angle_max_cd` (`.cpp:1413-1416`). -/
def lean_angle_max_cd (p : Params) : ftype :=
  constrain_float p._angle_max_deg AC_ATTITUDE_CONTROL_ANGLE_LIMIT_MIN AC_ATTITUDE_CONTROL_ANGLE_LIMIT_MAX * 100
/-- `lean_angle_max_rad` (`.cpp:1419-1422`). -/
def lean_angle_max_rad (p : Params) : ftype :=
  radians (constrain_float p._angle_max_deg AC_ATTITUDE_CONTROL_ANGLE_LIMIT_MIN AC_ATTITUDE_CONTROL_ANGLE_LIMIT_MAX)

/-! ### Kinematics, `AC_AttitudeControl.cpp:1303-1342` -/

/-- `euler_derivative_to_body(att, euler_derivative_rads, body_derivative_rads&)` (`:1303-1316`);
returns `body_derivative_rads` (every component is written). -/
def euler_derivative_to_body (att : Quaternion) (euler_derivative_rads : Vector3f) : Vector3f :=
  let theta := att.get_euler_pitch
  let phi := att.get_euler_roll
  let sin_theta := theta.sin
  let cos_theta := theta.cos
  let sin_phi := phi.sin
  let cos_phi := phi.cos
  ⟨euler_derivative_rads.x - sin_theta * euler_derivative_rads.z,
   cos_phi * euler_derivative_rads.y + sin_phi * cos_theta * euler_derivative_rads.z,
   (-sin_phi) * euler_derivative_rads.y + cos_theta * cos_phi * euler_derivative_rads.z⟩

/-- `body_to_euler_derivative(att, body_derivative_rads, euler_derivative_rads&)` (`:1323-1342`);
returns `(euler_derivative_rads, ok)`. On gimbal lock (`is_zero(cos_theta)`) the output is left as
passed in (`euler_derivative_rads`) and the result is `false`. -/
def body_to_euler_derivative (att : Quaternion) (body_derivative_rads euler_derivative_rads : Vector3f) :
    Vector3f × Bool :=
  let theta := att.get_euler_pitch
  let phi := att.get_euler_roll
  let sin_theta := theta.sin
  let cos_theta := theta.cos
  let sin_phi := phi.sin
  let cos_phi := phi.cos
  if is_zero cos_theta then
    (euler_derivative_rads, false)
  else
    (⟨body_derivative_rads.x + sin_phi * (sin_theta / cos_theta) * body_derivative_rads.y
        + cos_phi * (sin_theta / cos_theta) * body_derivative_rads.z,
      cos_phi * body_derivative_rads.y - sin_phi * body_derivative_rads.z,
      (sin_phi / cos_theta) * body_derivative_rads.y + (cos_phi / cos_theta) * body_derivative_rads.z⟩,
     true)

/-! ### Rate-loop housekeeping, `AC_AttitudeControl.cpp:246-296` -/

/-- `reset_rate_controller_I_terms` (`:273-278`) on the three rate PID states (roll, pitch, yaw). -/
def reset_rate_controller_I_terms (pid_roll pid_pitch pid_yaw : AC_PID.State) :
    AC_PID.State × AC_PID.State × AC_PID.State :=
  (AC_PID.reset_I pid_roll, AC_PID.reset_I pid_pitch, AC_PID.reset_I pid_yaw)

/-- `reset_rate_controller_I_terms_smoothly` (`:281-286`). -/
def reset_rate_controller_I_terms_smoothly (s : State)
    (get_rate_roll_pid get_rate_pitch_pid get_rate_yaw_pid : AC_PID.Params)
    (pid_roll pid_pitch pid_yaw : AC_PID.State) : AC_PID.State × AC_PID.State × AC_PID.State :=
  (AC_PID.relax_integrator get_rate_roll_pid pid_roll 0.0 s._dt_s AC_ATTITUDE_RATE_RELAX_TC,
   AC_PID.relax_integrator get_rate_pitch_pid pid_pitch 0.0 s._dt_s AC_ATTITUDE_RATE_RELAX_TC,
   AC_PID.relax_integrator get_rate_yaw_pid pid_yaw 0.0 s._dt_s AC_ATTITUDE_RATE_RELAX_TC)

/-- `relax_attitude_controllers` (`:246-271`). `attitude_body` is
`_ahrs.get_quat_body_to_ned(...)`. Returns the state and the three rate PID states. -/
def relax_attitude_controllers (s : State) (attitude_body : Quaternion)
    (pid_roll pid_pitch pid_yaw : AC_PID.State) :
    State × AC_PID.State × AC_PID.State × AC_PID.State :=
  -- take a copy of the last gyro used by the rate controller before using it
  let gyro := get_latest_gyro s
  -- Initialize the attitude variables to the current attitude
  let s := { s with _attitude_target := attitude_body }
  let s := { s with _euler_angle_target_rad := s._attitude_target.to_euler_vec }
  let s := { s with _attitude_ang_error := s._attitude_ang_error.initialise }
  -- Initialize the angular rate variables to the current rate
  let s := { s with _ang_vel_target_rads := gyro }
  let s := { s with _euler_rate_target_rads :=
    (body_to_euler_derivative s._attitude_target s._ang_vel_target_rads s._euler_rate_target_rads).1 }
  -- Initialize remaining variables
  let s := { s with _thrust_error_angle_rad := 0.0 }
  -- Reset the PID filters
  let pid_roll := AC_PID.reset_filter pid_roll
  let pid_pitch := AC_PID.reset_filter pid_pitch
  let pid_yaw := AC_PID.reset_filter pid_yaw
  -- Reset the I terms
  let (pid_roll, pid_pitch, pid_yaw) := reset_rate_controller_I_terms pid_roll pid_pitch pid_yaw
  -- finally update the attitude target
  let s := { s with _ang_vel_body_rads := gyro }
  (s, pid_roll, pid_pitch, pid_yaw)

/-- `rate_controller_target_reset` (`:289-296`). -/
def rate_controller_target_reset (s : State) : State :=
  { s with _sysid_ang_vel_body_rads := s._sysid_ang_vel_body_rads.zero,
           _actuator_sysid := s._actuator_sysid.zero,
           _pd_scale := VECTORF_111,
           _i_scale := VECTORF_111,
           _angle_P_scale := VECTORF_111 }

/-! ### Target resets, `AC_AttitudeControl.cpp:1252-1297` -/

/-- `reset_target_and_rate(reset_rate = true)` (`:1252-1263`). -/
def reset_target_and_rate (s : State) (attitude_body : Quaternion) (reset_rate : Bool := true) : State :=
  -- move attitude target to current attitude
  let s := { s with _attitude_target := attitude_body }
  let s := { s with _euler_angle_target_rad := s._attitude_target.to_euler_vec }
  if reset_rate then
    { s with _ang_vel_target_rads := s._ang_vel_target_rads.zero,
             _ang_accel_target_rads := s._ang_accel_target_rads.zero,
             _euler_rate_target_rads := s._euler_rate_target_rads.zero }
  else s

/-- `reset_yaw_target_and_rate(reset_rate = true)` (`:1267-1283`). `ahrs_yaw` is `_ahrs.yaw`. -/
def reset_yaw_target_and_rate (s : State) (ahrs_yaw : ftype) (reset_rate : Bool := true) : State :=
  -- move attitude target to current heading
  let yaw_shift := ahrs_yaw - s._euler_angle_target_rad.z
  let _attitude_target_update := Quaternion.from_axis_angle ⟨0.0, 0.0, yaw_shift⟩
  let s := { s with _attitude_target := _attitude_target_update * s._attitude_target }
  if reset_rate then
    -- set yaw rate to zero
    let s := { s with _euler_rate_target_rads := { s._euler_rate_target_rads with z := 0.0 } }
    let s := { s with _ang_accel_target_rads := { s._ang_accel_target_rads with z := 0.0 } }
    -- Convert euler angle derivative of desired attitude into a body-frame angular velocity vector
    { s with _ang_vel_target_rads := euler_derivative_to_body s._attitude_target s._euler_rate_target_rads }
  else s

/-- `inertial_frame_reset` (`:1286-1297`). -/
def inertial_frame_reset (s : State) (attitude_body : Quaternion) : State :=
  -- Recalculate the target quaternion
  let s := { s with _attitude_target := attitude_body * s._attitude_ang_error }
  -- calculate the attitude target euler angles
  { s with _euler_angle_target_rad := s._attitude_target.to_euler_vec }

/-! ### Shaping and limits -/

/-- `attitude_command_model(error_angle, desired_ang_vel, target_ang_vel&, target_ang_accel&,
max_ang_vel, accel_max, input_tc, dt)` (`:1108-1130`); returns `(target_ang_vel, target_ang_accel)`.
-/
def attitude_command_model (error_angle desired_ang_vel target_ang_vel target_ang_accel max_ang_vel
    accel_max input_tc dt : ftype) : ftype × ftype :=
  if !is_positive dt then
    (target_ang_vel, target_ang_accel)
  else
    -- protect against divide by zero
    let accel_max := if !is_positive accel_max then radians 1800 else accel_max
    let input_tc := if !is_positive input_tc then dt * 10.0 else input_tc
    let target_ang_accel :=
      shape_angle_vel_accel error_angle desired_ang_vel 0.0
        0.0 target_ang_vel target_ang_accel
        (-max_ang_vel) max_ang_vel accel_max
        (accel_max / input_tc) dt true
    let target_ang_vel := target_ang_vel + target_ang_accel * dt
    (target_ang_vel, target_ang_accel)

/-- `ang_vel_limit(euler_rad&, ang_vel_roll_max_rads, ang_vel_pitch_max_rads,
ang_vel_yaw_max_rads)` (`:1206-1226`); returns `euler_rad`. -/
def ang_vel_limit (euler_rad : Vector3f) (ang_vel_roll_max_rads ang_vel_pitch_max_rads
    ang_vel_yaw_max_rads : ftype) : Vector3f :=
  let euler_rad :=
    if is_zero ang_vel_roll_max_rads || is_zero ang_vel_pitch_max_rads then
      let euler_rad :=
        if !is_zero ang_vel_roll_max_rads then
          { euler_rad with x := constrain_float euler_rad.x (-ang_vel_roll_max_rads) ang_vel_roll_max_rads }
        else euler_rad
      if !is_zero ang_vel_pitch_max_rads then
        { euler_rad with y := constrain_float euler_rad.y (-ang_vel_pitch_max_rads) ang_vel_pitch_max_rads }
      else euler_rad
    else
      let thrust_vector_ang_vel : Vector2f :=
        ⟨euler_rad.x / ang_vel_roll_max_rads, euler_rad.y / ang_vel_pitch_max_rads⟩
      let thrust_vector_length := thrust_vector_ang_vel.length
      if thrust_vector_length > 1.0 then
        { euler_rad with
          x := thrust_vector_ang_vel.x * ang_vel_roll_max_rads / thrust_vector_length
          y := thrust_vector_ang_vel.y * ang_vel_pitch_max_rads / thrust_vector_length }
      else euler_rad
  if !is_zero ang_vel_yaw_max_rads then
    { euler_rad with z := constrain_float euler_rad.z (-ang_vel_yaw_max_rads) ang_vel_yaw_max_rads }
  else euler_rad

/-- `update_ang_vel_target_from_att_error(attitude_error_rot_vec_rad)` (`:1345-1374`). -/
def update_ang_vel_target_from_att_error (p : Params) (s : State)
    (attitude_error_rot_vec_rad : Vector3f) : Vector3f :=
  -- Compute the roll angular velocity demand from the roll angle error
  let angleP_roll := AC_P.kP p._p_angle_roll * s._angle_P_scale.x
  let x :=
    if s._use_sqrt_controller && !is_zero (get_accel_roll_max_radss p) then
      sqrt_controller attitude_error_rot_vec_rad.x angleP_roll
        (constrain_float (get_accel_roll_max_radss p / 2.0) AC_ATTITUDE_ACCEL_RP_CONTROLLER_MIN_RADSS
          AC_ATTITUDE_ACCEL_RP_CONTROLLER_MAX_RADSS) s._dt_s
    else
      angleP_roll * attitude_error_rot_vec_rad.x
  -- Compute the pitch angular velocity demand from the pitch angle error
  let angleP_pitch := AC_P.kP p._p_angle_pitch * s._angle_P_scale.y
  let y :=
    if s._use_sqrt_controller && !is_zero (get_accel_pitch_max_radss p) then
      sqrt_controller attitude_error_rot_vec_rad.y angleP_pitch
        (constrain_float (get_accel_pitch_max_radss p / 2.0) AC_ATTITUDE_ACCEL_RP_CONTROLLER_MIN_RADSS
          AC_ATTITUDE_ACCEL_RP_CONTROLLER_MAX_RADSS) s._dt_s
    else
      angleP_pitch * attitude_error_rot_vec_rad.y
  -- Compute the yaw angular velocity demand from the yaw angle error
  let angleP_yaw := AC_P.kP p._p_angle_yaw * s._angle_P_scale.z
  let z :=
    if s._use_sqrt_controller && !is_zero (get_accel_yaw_max_radss p) then
      sqrt_controller attitude_error_rot_vec_rad.z angleP_yaw
        (constrain_float (get_accel_yaw_max_radss p / 2.0) AC_ATTITUDE_ACCEL_Y_CONTROLLER_MIN_RADSS
          AC_ATTITUDE_ACCEL_Y_CONTROLLER_MAX_RADSS) s._dt_s
    else
      angleP_yaw * attitude_error_rot_vec_rad.z
  ⟨x, y, z⟩

/-! ### Thrust vector and attitude error -/

/-- `attitude_from_thrust_vector(thrust_vector, heading_angle_rad)` (`:947-976`). -/
def attitude_from_thrust_vector (thrust_vector : Vector3f) (heading_angle_rad : ftype) : Quaternion :=
  let thrust_vector_up : Vector3f := ⟨0.0, 0.0, -1.0⟩
  let thrust_vector :=
    if is_zero thrust_vector.length_squared then thrust_vector_up
    else thrust_vector.normalize
  -- the cross product of the desired and target thrust vector defines the rotation vector
  let thrust_vec_cross := thrust_vector_up % thrust_vector
  -- the dot product is used to calculate the angle between the target and desired thrust vectors
  let thrust_vector_angle := (constrain_float (thrust_vector_up * thrust_vector) (-1.0) 1.0).acos
  -- Normalize the thrust rotation vector
  let thrust_vector_length := thrust_vec_cross.length
  let thrust_vec_cross :=
    if is_zero thrust_vector_length || is_zero thrust_vector_angle then thrust_vector_up
    else thrust_vec_cross / thrust_vector_length
  let thrust_vec_quat := Quaternion.from_axis_angle_theta thrust_vec_cross thrust_vector_angle
  let yaw_quat := Quaternion.from_axis_angle_theta ⟨0.0, 0.0, 1.0⟩ heading_angle_rad
  thrust_vec_quat * yaw_quat

/-- `update_attitude_target` (`:979-986`). -/
def update_attitude_target (s : State) : State :=
  -- rotate target and normalize
  let attitude_target_update := Quaternion.from_axis_angle (s._ang_vel_target_rads * s._dt_s)
  let _attitude_target := s._attitude_target * attitude_target_update
  { s with _attitude_target := _attitude_target.normalize }

/-- `thrust_vector_rotation_angles(attitude_target, attitude_body, thrust_vector_correction&,
attitude_error_rad&, thrust_angle_rad&, thrust_error_angle_rad&)` (`:1056-1104`); returns
`(thrust_vector_correction, attitude_error_rad, thrust_angle_rad, thrust_error_angle_rad)`. -/
def thrust_vector_rotation_angles (attitude_target attitude_body : Quaternion) :
    Quaternion × Vector3f × ftype × ftype :=
  -- The direction of thrust is [0,0,-1] is any body-fixed frame, inc. body frame and target frame.
  let thrust_vector_up : Vector3f := ⟨0.0, 0.0, -1.0⟩
  let att_target_thrust_vec := attitude_target * thrust_vector_up
  let att_body_thrust_vec := attitude_body * thrust_vector_up
  -- the dot product is used to calculate the current lean angle for use of external functions
  let thrust_angle_rad := (constrain_float (thrust_vector_up * att_body_thrust_vec) (-1.0) 1.0).acos
  -- the cross product of the desired and target thrust vector defines the rotation vector
  let thrust_vec_cross := att_body_thrust_vec % att_target_thrust_vec
  -- the dot product is used to calculate the angle between the target and desired thrust vectors
  let thrust_error_angle_rad :=
    (constrain_float (att_body_thrust_vec * att_target_thrust_vec) (-1.0) 1.0).acos
  -- Normalize the thrust rotation vector
  let thrust_vector_length := thrust_vec_cross.length
  let thrust_vec_cross :=
    if is_zero thrust_vector_length || is_zero thrust_error_angle_rad then thrust_vector_up
    else thrust_vec_cross / thrust_vector_length
  -- express the axis in the body frame
  let thrust_vec_cross := attitude_body.inverse * thrust_vec_cross
  let thrust_vector_correction := Quaternion.from_axis_angle_theta thrust_vec_cross thrust_error_angle_rad
  -- calculate the angle error in x and y.
  let rotation_rad := thrust_vector_correction.to_axis_angle
  let ex := rotation_rad.x
  let ey := rotation_rad.y
  -- calculate the remaining rotation required after thrust vector is rotated transformed to the body frame
  let heading_vec_correction_quat :=
    thrust_vector_correction.inverse * attitude_body.inverse * attitude_target
  -- calculate the angle error in z (x and y should be zero here).
  let rotation_rad := heading_vec_correction_quat.to_axis_angle
  let ez := rotation_rad.z
  (thrust_vector_correction, ⟨ex, ey, ez⟩, thrust_angle_rad, thrust_error_angle_rad)

/-- `thrust_heading_rotation_angles(attitude_target&, attitude_body, attitude_error_rad&,
thrust_angle_rad&, thrust_error_angle_rad&)` (`:1033-1052`); returns
`(attitude_target, attitude_error_rad, thrust_angle_rad, thrust_error_angle_rad)`.
`get_rate_yaw_pid` is the derived class's yaw rate PID (only `kP()` is read). -/
def thrust_heading_rotation_angles (p : Params) (get_rate_yaw_pid : AC_PID.Params)
    (attitude_target attitude_body : Quaternion) : Quaternion × Vector3f × ftype × ftype :=
  let (thrust_vector_correction, attitude_error_rad, thrust_angle_rad, thrust_error_angle_rad) :=
    thrust_vector_rotation_angles attitude_target attitude_body
  -- Limit Yaw Error based to the maximum that would saturate the output when yaw rate is zero.
  let heading_accel_max := constrain_float (get_accel_yaw_max_radss p / 2.0)
    AC_ATTITUDE_ACCEL_Y_CONTROLLER_MIN_RADSS AC_ATTITUDE_ACCEL_Y_CONTROLLER_MAX_RADSS
  if !is_zero (AC_PID.kP get_rate_yaw_pid) then
    let heading_error_max := MIN
      (inv_sqrt_controller (1.0 / AC_PID.kP get_rate_yaw_pid) (AC_P.kP p._p_angle_yaw) heading_accel_max)
      AC_ATTITUDE_YAW_MAX_ERROR_ANGLE_RAD
    if !is_zero (AC_P.kP p._p_angle_yaw) && attitude_error_rad.z.abs > heading_error_max then
      let ez := constrain_float (wrap_PI attitude_error_rad.z) (-heading_error_max) heading_error_max
      let attitude_error_rad := { attitude_error_rad with z := ez }
      let heading_vec_correction_quat := Quaternion.from_axis_angle ⟨0.0, 0.0, attitude_error_rad.z⟩
      let attitude_target := attitude_body * thrust_vector_correction * heading_vec_correction_quat
      (attitude_target, attitude_error_rad, thrust_angle_rad, thrust_error_angle_rad)
    else (attitude_target, attitude_error_rad, thrust_angle_rad, thrust_error_angle_rad)
  else (attitude_target, attitude_error_rad, thrust_angle_rad, thrust_error_angle_rad)

/-! ### The attitude controller -/

/-- `attitude_controller_run_quat` (`:989-1029`). `attitude_body` is
`_ahrs.get_quat_body_to_ned(attitude_body)` (`:993`); the gyro is `get_latest_gyro()` (state). -/
def attitude_controller_run_quat (p : Params) (get_rate_yaw_pid : AC_PID.Params) (s : State)
    (attitude_body : Quaternion) : State :=
  -- This vector represents the angular error to rotate the thrust vector using x and y and heading using z
  let (_attitude_target, attitude_error, _thrust_angle_rad, _thrust_error_angle_rad) :=
    thrust_heading_rotation_angles p get_rate_yaw_pid s._attitude_target attitude_body
  let s := { s with _attitude_target := _attitude_target, _thrust_angle_rad := _thrust_angle_rad,
                    _thrust_error_angle_rad := _thrust_error_angle_rad }
  -- Compute the angular velocity corrections in the body frame from the attitude error
  let ang_vel_body_rads := update_ang_vel_target_from_att_error p s attitude_error
  -- ensure angular velocity does not go over configured limits
  let ang_vel_body_rads := ang_vel_limit ang_vel_body_rads (radians p._ang_vel_roll_max_degs)
    (radians p._ang_vel_pitch_max_degs) (radians p._ang_vel_yaw_max_degs)
  -- rotation from the target frame to the body frame
  let rotation_target_to_body := attitude_body.inverse * s._attitude_target
  -- target angle velocity vector in the body frame
  let ang_vel_body_feedforward := rotation_target_to_body * s._ang_vel_target_rads
  let gyro := get_latest_gyro s
  -- Correct the thrust vector and smoothly add feedforward and yaw input
  let s := { s with _feedforward_scalar := 1.0 }
  let (s, ang_vel_body_rads) :=
    if s._thrust_error_angle_rad > AC_ATTITUDE_THRUST_ERROR_ANGLE_RAD * 2.0 then
      (s, { ang_vel_body_rads with z := gyro.z })
    else if s._thrust_error_angle_rad > AC_ATTITUDE_THRUST_ERROR_ANGLE_RAD then
      let s := { s with _feedforward_scalar :=
        (1.0 - (s._thrust_error_angle_rad - AC_ATTITUDE_THRUST_ERROR_ANGLE_RAD) / AC_ATTITUDE_THRUST_ERROR_ANGLE_RAD) }
      let x := ang_vel_body_rads.x + ang_vel_body_feedforward.x * s._feedforward_scalar
      let y := ang_vel_body_rads.y + ang_vel_body_feedforward.y * s._feedforward_scalar
      let z := ang_vel_body_rads.z + ang_vel_body_feedforward.z
      let z := gyro.z * (1.0 - s._feedforward_scalar) + z * s._feedforward_scalar
      (s, ⟨x, y, z⟩)
    else
      (s, ang_vel_body_rads + ang_vel_body_feedforward)
  -- Record error to handle EKF resets
  let s := { s with _attitude_ang_error := attitude_body.inverse * s._attitude_target }
  -- finally update the attitude target
  { s with _ang_vel_body_rads := ang_vel_body_rads }

/-! ### Thrust-vector entry points -/

/-- `input_thrust_vector_rate_heading_rads(thrust_vector, heading_rate_rads, slew_yaw = true)`
(`:832-885`). -/
def input_thrust_vector_rate_heading_rads (p : Params) (get_rate_yaw_pid : AC_PID.Params) (s : State)
    (attitude_body : Quaternion) (thrust_vector : Vector3f) (heading_rate_rads : ftype)
    (slew_yaw : Bool := true) : State :=
  let yaw_rate_max_rads := radians p._ang_vel_yaw_max_degs
  -- Replace global yaw rate limit with the slew rate limit (0 disables limiting).
  let yaw_rate_max_rads := if slew_yaw then get_slew_yaw_max_rads p else yaw_rate_max_rads
  -- update attitude target
  let s := update_attitude_target s
  -- calculate the attitude target euler angles
  let s := { s with _euler_angle_target_rad := s._attitude_target.to_euler_vec }
  -- Convert thrust vector to an attitude quaternion (zero yaw; yaw is commanded separately).
  let thrust_vec_quat := attitude_from_thrust_vector thrust_vector 0.0
  let (thrust_vec_correction_quat, attitude_error, _returned_thrust_vector_angle,
      _thrust_vector_diff_angle) := thrust_vector_rotation_angles thrust_vec_quat s._attitude_target
  let s :=
    if p._rate_bf_ff_enabled then
      let (vx, ax) := attitude_command_model attitude_error.x 0.0 s._ang_vel_target_rads.x
        s._ang_accel_target_rads.x (radians p._ang_vel_roll_max_degs) (get_accel_roll_max_radss p)
        p._input_tc s._dt_s
      let (vy, ay) := attitude_command_model attitude_error.y 0.0 s._ang_vel_target_rads.y
        s._ang_accel_target_rads.y (radians p._ang_vel_pitch_max_degs) (get_accel_pitch_max_radss p)
        p._input_tc s._dt_s
      -- Shape yaw rate input into yaw angular velocity/acceleration targets
      let (vz, az) := attitude_command_model 0.0 heading_rate_rads s._ang_vel_target_rads.z
        s._ang_accel_target_rads.z yaw_rate_max_rads (get_accel_yaw_max_radss p) s._rate_y_tc s._dt_s
      { s with _ang_vel_target_rads := ⟨vx, vy, vz⟩, _ang_accel_target_rads := ⟨ax, ay, az⟩ }
    else
      -- No shaping/feedforward: directly update the attitude target
      let heading_rate_rads :=
        if is_positive yaw_rate_max_rads then
          constrain_float heading_rate_rads (-yaw_rate_max_rads) yaw_rate_max_rads
        else heading_rate_rads
      let yaw_quat := Quaternion.from_axis_angle ⟨0.0, 0.0, heading_rate_rads * s._dt_s⟩
      let _attitude_target := s._attitude_target * thrust_vec_correction_quat * yaw_quat
      let s := { s with _attitude_target := _attitude_target.normalize }
      -- Zero rate and acceleration feedforward targets
      { s with _euler_rate_target_rads := s._euler_rate_target_rads.zero,
               _ang_vel_target_rads := s._ang_vel_target_rads.zero,
               _ang_accel_target_rads := s._ang_accel_target_rads.zero }
  -- Convert body-frame angular velocity into euler angle derivative of desired attitude
  let s := { s with _euler_rate_target_rads :=
    (body_to_euler_derivative s._attitude_target s._ang_vel_target_rads s._euler_rate_target_rads).1 }
  -- Call quaternion attitude controller
  attitude_controller_run_quat p get_rate_yaw_pid s attitude_body

/-- `input_thrust_vector_heading_rad(thrust_vector, heading_angle_rad, heading_rate_rads)`
(`:890-929`). -/
def input_thrust_vector_heading_rad (p : Params) (get_rate_yaw_pid : AC_PID.Params) (s : State)
    (attitude_body : Quaternion) (thrust_vector : Vector3f) (heading_angle_rad heading_rate_rads : ftype) :
    State :=
  -- update attitude target
  let s := update_attitude_target s
  -- calculate the attitude target euler angles
  let s := { s with _euler_angle_target_rad := s._attitude_target.to_euler_vec }
  -- Convert thrust vector and heading into a desired attitude quaternion.
  let desired_attitude_quat := attitude_from_thrust_vector thrust_vector heading_angle_rad
  let s :=
    if p._rate_bf_ff_enabled then
      -- Compute attitude error required to move from the current target attitude to the desired attitude.
      let (_thrust_vec_correction_quat, attitude_error, _returned_thrust_vector_angle,
          _thrust_vector_diff_angle) := thrust_vector_rotation_angles desired_attitude_quat s._attitude_target
      let (vx, ax) := attitude_command_model attitude_error.x 0.0 s._ang_vel_target_rads.x
        s._ang_accel_target_rads.x (radians p._ang_vel_roll_max_degs) (get_accel_roll_max_radss p)
        p._input_tc s._dt_s
      let (vy, ay) := attitude_command_model attitude_error.y 0.0 s._ang_vel_target_rads.y
        s._ang_accel_target_rads.y (radians p._ang_vel_pitch_max_degs) (get_accel_pitch_max_radss p)
        p._input_tc s._dt_s
      let (vz, az) := attitude_command_model attitude_error.z heading_rate_rads s._ang_vel_target_rads.z
        s._ang_accel_target_rads.z (get_slew_yaw_max_rads p) (get_accel_yaw_max_radss p) s._rate_y_tc
        s._dt_s
      { s with _ang_vel_target_rads := ⟨vx, vy, vz⟩, _ang_accel_target_rads := ⟨ax, ay, az⟩ }
    else
      -- No shaping/feedforward: directly set the attitude target to the desired attitude.
      let s := { s with _attitude_target := desired_attitude_quat }
      -- Zero rate and acceleration feedforward targets
      { s with _euler_rate_target_rads := s._euler_rate_target_rads.zero,
               _ang_vel_target_rads := s._ang_vel_target_rads.zero,
               _ang_accel_target_rads := s._ang_accel_target_rads.zero }
  -- Convert body-frame angular velocity into euler angle derivative of desired attitude
  let s := { s with _euler_rate_target_rads :=
    (body_to_euler_derivative s._attitude_target s._ang_vel_target_rads s._euler_rate_target_rads).1 }
  -- Call quaternion attitude controller
  attitude_controller_run_quat p get_rate_yaw_pid s attitude_body

/-- `input_thrust_vector_heading_rad(thrust_vector, heading_rad)` (`.h:293`): heading rate 0. -/
def input_thrust_vector_heading_rad_zero_rate (p : Params) (get_rate_yaw_pid : AC_PID.Params) (s : State)
    (attitude_body : Quaternion) (thrust_vector : Vector3f) (heading_rad : ftype) : State :=
  input_thrust_vector_heading_rad p get_rate_yaw_pid s attitude_body thrust_vector heading_rad 0.0

/-- `input_thrust_vector_heading(thrust_vector, HeadingCommand heading)` (`:932-945`), the form
called by `ModeAuto::wp_run` (`mode_auto.cpp:1153`). -/
def input_thrust_vector_heading (p : Params) (get_rate_yaw_pid : AC_PID.Params) (s : State)
    (attitude_body : Quaternion) (thrust_vector : Vector3f) (heading : HeadingCommand) : State :=
  match heading.heading_mode with
  | .Rate_Only =>
    input_thrust_vector_rate_heading_rads p get_rate_yaw_pid s attitude_body thrust_vector heading.yaw_rate_rads
  | .Angle_Only =>
    input_thrust_vector_heading_rad p get_rate_yaw_pid s attitude_body thrust_vector heading.yaw_angle_rad 0.0
  | .Angle_And_Rate =>
    input_thrust_vector_heading_rad p get_rate_yaw_pid s attitude_body thrust_vector heading.yaw_angle_rad
      heading.yaw_rate_rads

end AC_AttitudeControl
