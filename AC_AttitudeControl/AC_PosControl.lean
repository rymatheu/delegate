import AP_Math
import AC_PID
import AP_Motors.Interface

/-!
# `AC_PosControl`

Mirrors `libraries/AC_AttitudeControl/AC_PosControl.h:18-36` (defaults), `:48-62`, `:109-122`,
`:214-230`, `:303-568`, `:595`, `:607` (accessors), `:714-791` (members) and
`libraries/AC_AttitudeControl/AC_PosControl.cpp` at ArduPilot 802db19de1, Copter build
(`APM_BUILD_TYPE(APM_BUILD_ArduCopter)`): the defaults `:51-80`, the parameter table `:91-347`,
the constructor `:353-373`, and the methods listed with their line ranges below. SI units
throughout, as in the C++.

## Shape

One C++ object is split into `Params` (the `AP_Param` table, fields named as the ArduPilot
parameters: `PSC_NE_POS_P`, `PSC_D_ACC_IMAX`, ...) and `State` (the C++ members, same names).
Every method is a pure function `Params → State → environment → C++ arguments → State × outputs`.
The environment records hold exactly what the C++ reads from the objects it holds references to,
with fields named as the C++ getters, so the Copter loop can wire them:
- `AHRSInputs`: `_ahrs` (`AP_AHRS_View`: `cos_yaw()`, `sin_yaw()`, `yaw`, `get_accel_ef()`) and
  `AP::ahrs()` (`get_control_gain_scaler_XY()`, `get_control_gain_scaler_Z()`);
- `AHRSEstimates`: what `update_estimates` reads from `AP::ahrs()` (see there);
- `AP_Motors.Inputs`: `_motors` (`get_throttle_hover()`, `limit.throttle_lower/upper`);
- `AttitudeControlInputs`: `_attitude_control` (`get_att_target_euler_rad()`,
  `get_althold_lean_angle_max_rad()`, `lean_angle_max_rad()`, `get_throttle_in()`, the rate and
  acceleration maxima, `get_bf_feedforward()`);
- `Clock`: `AP::scheduler().ticks32()` and `AP_HAL::millis()`.
The one write to another object on the Auto path, `_attitude_control.set_throttle_out(...)` in
`D_update_controller` (`:1145`), is returned as a `SetThrottleOut` record with the three C++
arguments (throttle, angle-boost flag, filter cutoff); the caller applies it.

The PID objects are the `AC_PID` port: `_p_pos_ne_m : AC_P_2D`, `_p_pos_d_m : AC_P_1D`,
`_pid_vel_ne_m : AC_PID_2D`, `_pid_vel_d_m : AC_PID_Basic`, `_pid_accel_d_m : AC_PID`. Their
states live in `State`; their gains are built from `Params` by `Params._p_pos_ne_m` etc. One
parameter is written at run time: `D_update_controller` raises `PSC_D_ACC_IMAX` to the hover
throttle (`:1127-1129`, `_kimax.set`, RAM only). Its RAM value is the state field
`_pid_accel_d_m_kimax` (C++ `_pid_accel_d_m._kimax`), initialised from `PSC_D_ACC_IMAX`, and
`pid_accel_d_m_params` reads it.

## Methods ported (C++ lines)

`set_dt_s`/`get_dt_s` (h:50-53), `update_estimates` (cpp:1446-1465), `input_pos_NED_m`
(:386-429), `terrain_scaler_D_m` (:433-440), `NE_set_max_speed_accel_m` (:458-479),
`NE_set_correction_speed_accel_m` (:493-497), `NE_init_controller_stopping_point` (:502-510),
`NE_init_controller` (:544-586), `NE_update_offsets` (:644-663), `NE_is_active` (:689-693),
`NE_update_controller` (:697-788), `D_set_max_speed_accel_m` (:806-827),
`D_set_correction_speed_accel_m` (:841-845), `D_init_controller_stopping_point` (:868-877),
`D_init_controller` (:895-929), `D_update_offsets` (:1039-1066), `D_is_active` (:1069-1073),
`D_update_controller` (:1079-1162), `get_lean_angle_max_rad` (:1170-1179),
`set_pos_vel_accel_NED_m` (:1183-1188), `set_pos_vel_accel_NE_m` (:1192-1197),
`lean_angles_rad_to_accel_NED_mss` (:1200-1215), `init_terrain` (:1220-1231),
`init_pos_terrain_D_m` (:1243-1248), `NE_init_offsets` (:1254-1272), `D_init_offsets`
(:1275-1293), `set_posvelaccel_offset_target_NE_m`/`_D_m` (:1342-1371), `get_thrust_vector`
(:1374-1379), `get_stopping_point_NE_m` (:1382-1410), `get_stopping_point_D_m` (:1413-1429),
`update_terrain` (:1596-1612), `accel_NE_mss_to_lean_angles_rad` (:1615-1625),
`lean_angles_to_accel_NE_mss` (:1628-1637), `calculate_yaw_and_rate_yaw` (:1641-1670),
`calculate_overspeed_gain` (:1673-1687), and the inline accessors of the header.

Terrain and offsets are kept although they are zero in a plain Auto mission: `AC_WPNav` calls
`terrain_scaler_D_m`, `set_pos_terrain_target_D_m`, `get_pos_offset_NED_m` and
`get_vel_offset_D_ms` every tick (`AC_WPNav.cpp:566-580`), `terrain_scaler_D_m` is not trivial
for a zero terrain offset (it scales the horizontal speed by the vertical tracking error when
`WPNAV_TER_MARGIN > 0`, default 10 m), and `NE_update_controller`/`D_update_controller` add the
offsets and terrain terms into their sums, which is visible in floating point (`-0.0 + 0.0`).

## Left out

- EKF reset handling: `NE_handle_ekf_reset`, `D_handle_ekf_reset`, `NE_init_ekf_reset`,
  `D_init_ekf_reset` (:1690-1764), `_ahrs_position_*_reset_count`, `_ekf_reset_method`. They act
  only when the EKF reports a position reset (the count changes), which does not happen in a
  fault-free run; the port equals the C++ while the reset counts stay constant.
- High-vibration compensation: `_vibe_comp_enabled` is taken as `false` (its default; it is set
  only by `Copter::update_vibration_compensation` on detected clipping), so the branch
  `get_throttle_with_vibration_override` (:1131-1133, :1470-1485) is not ported, and
  `update_estimates` takes `high_vibes` as an argument.
- System-ID disturbances `_disturb_pos_ne_m`, `_disturb_vel_ne_ms` (h:741-742, cpp:727-747,
  :786-787): zero outside `ModeSystemId`. The additions of the zero vector are kept as written
  (`comb_pos_ne_m += 0`, `comb_vel_ne_ms += 0`) so the floating-point result is the same.
- `has_good_timing` and the `INTERNAL_ERROR` reports (:705-708, :1087-1090): diagnostics only.
- Logging (`write_log`, `Write_PSC*`, `Write_PSO*`), `pre_arm_checks`, `convert_parameters`,
  `AP_Param` plumbing, the singleton.
- `NED_standby_reset` and standby handling; the centimetre wrappers (`*_cm`, `*_cms`);
  methods used only by other modes or Auto submodes other than WP: `NE_relax_velocity_controller`,
  `NE_soften_for_landing`, `NE_stop_pos_stabilisation`, `NE_stop_vel_stabilisation`,
  `input_accel_NE_m`, `input_vel_accel_NE_m`, `input_pos_vel_accel_NE_m`,
  `D_init_controller_no_descent`, `D_relax_controller`, `input_accel_D_m`, `input_vel_accel_D_m`,
  `D_set_pos_target_from_climb_rate_ms`, `input_pos_vel_accel_D_m`,
  `D_set_alt_target_with_slew_m`, `crosstrack_error_m`, `get_bearing_to_target_rad`,
  `get_fwd_pitch_is_limited` (Plane only), the scripting offset accessors.
- Forward pitch compensation: there is none in `AC_PosControl` at this commit for Copter
  (`get_fwd_pitch_is_limited` is compiled only for Plane, :1570-1587); nothing to port.

## Not one to one

- C++ references become return values. `update_all` of `AC_P_2D`/`AC_P_1D` rewrites its
  `target` argument (`_pos_target_ned_m.xy()`, `_pos_target_ned_m.z`); the port stores the
  returned target back, as the C++ does in place. `get_stopping_point_NE_m`/`_D_m` return the
  stopping point instead of writing through a reference.
- `update_estimates` takes the AHRS results as an argument (`AHRSEstimates`, see there).
- `set_throttle_out` is returned (`SetThrottleOut`), not called.
- `NE_get_pos_p` and the other PID accessors return the `(Params, State)` pair of the PID.
- `_pid_accel_d_m._kimax` is the state field `_pid_accel_d_m_kimax` (see above).
- `input_pos_NED_m` (:386-429) is not on the default Auto path (callers: `AC_WPNav_OA` with object
  avoidance enabled, Guided, the precision-landing retry); it is ported because of :410:
  `kinematic_limit(travel_dir_unit, _vel_max_ne_ms, _vel_max_up_ms, _vel_max_down_ms)` passes
  `(up, down)` to the parameters `(max_z_neg, max_z_pos)` of `kinematic_limit`
  (`control.cpp:734-804`). With `travel_dir_unit.z` in NED (positive down), `max_z_pos` bounds
  descent, so the call bounds descent by the climb limit and climb by the descent limit. The port
  mirrors the call as written.
- `float pos_d_m = pos_ned_m.z;` in `input_pos_NED_m` (:423) narrows a `postype_t` to `float`
  before it is widened again by `shape_pos_vel_accel`; the port writes `topostype (tofloat _)`.
-/

namespace AC_PosControl

open AP_Math

/-! ### Constants, `AC_PosControl.h:18-36`, `AC_PosControl.cpp:51-87` -/

/-- `POSCONTROL_ACCEL_NE_MSS` (h:19). -/
def POSCONTROL_ACCEL_NE_MSS : ftype := 1.0
/-- `POSCONTROL_JERK_NE_MSSS` (h:20). -/
def POSCONTROL_JERK_NE_MSSS : ftype := 5.0
/-- `POSCONTROL_STOPPING_DIST_UP_MAX_M` (h:22). -/
def POSCONTROL_STOPPING_DIST_UP_MAX_M : ftype := 3.0
/-- `POSCONTROL_STOPPING_DIST_DOWN_MAX_M` (h:23). -/
def POSCONTROL_STOPPING_DIST_DOWN_MAX_M : ftype := 2.0
/-- `POSCONTROL_SPEED_MS` (h:25). -/
def POSCONTROL_SPEED_MS : ftype := 5.0
/-- `POSCONTROL_SPEED_DOWN_MS` (h:26). -/
def POSCONTROL_SPEED_DOWN_MS : ftype := 1.5
/-- `POSCONTROL_SPEED_UP_MS` (h:27). -/
def POSCONTROL_SPEED_UP_MS : ftype := 2.5
/-- `POSCONTROL_ACCEL_D_MSS` (h:29). -/
def POSCONTROL_ACCEL_D_MSS : ftype := 2.5
/-- `POSCONTROL_JERK_D_MSSS` (h:30). -/
def POSCONTROL_JERK_D_MSSS : ftype := 5.0
/-- `POSCONTROL_THROTTLE_CUTOFF_FREQ_HZ` (h:32). -/
def POSCONTROL_THROTTLE_CUTOFF_FREQ_HZ : ftype := 2.0
/-- `POSCONTROL_OVERSPEED_GAIN_U` (h:34). -/
def POSCONTROL_OVERSPEED_GAIN_U : ftype := 2.0
/-- `POSCONTROL_RELAX_TC` (h:36). -/
def POSCONTROL_RELAX_TC : ftype := 0.16
/-- `POSCONTROL_POSVELACCEL_OFFSET_TARGET_TIMEOUT_MS` (cpp:87). -/
def POSCONTROL_POSVELACCEL_OFFSET_TARGET_TIMEOUT_MS : UInt32 := 3000

/-- Copter defaults, `AC_PosControl.cpp:51-80` (the `#else` branch, not Heli). -/
def POSCONTROL_D_POS_P : ftype := 1.0
def POSCONTROL_D_VEL_P : ftype := 5.0
def POSCONTROL_D_VEL_IMAX : ftype := 10.0
def POSCONTROL_D_VEL_FILT_HZ : ftype := 5.0
def POSCONTROL_D_VEL_FILT_D_HZ : ftype := 5.0
def POSCONTROL_D_ACC_I : ftype := 0.1
def POSCONTROL_D_ACC_D : ftype := 0.0
def POSCONTROL_D_ACC_IMAX : ftype := 0.8
def POSCONTROL_D_ACC_FILT_HZ : ftype := 20.0
def POSCONTROL_NE_POS_P : ftype := 1.0
def POSCONTROL_NE_VEL_IMAX : ftype := 10.0
def POSCONTROL_NE_VEL_FILT_HZ : ftype := 5.0
def POSCONTROL_NE_VEL_FILT_D_HZ : ftype := 5.0
def POSCONTROL_D_ACC_P : ftype := 0.05
def POSCONTROL_NE_VEL_P : ftype := 2.0
def POSCONTROL_NE_VEL_I : ftype := 1.0
def POSCONTROL_NE_VEL_D : ftype := 0.25

/-! ### Parameters, `AC_PosControl.cpp:91-347` -/

/-- The parameter table `var_info` with its sub-groups, prefix `PSC` (`ArduCopter/Parameters.cpp:388`).
C++ members: `_p_pos_d_m` (`_D_POS_`), `_p_pos_ne_m` (`_NE_POS_`), `_lean_angle_max_deg`
(`_ANGLE_MAX`), `_shaping_jerk_ne_msss` (`_NE_JERK`), `_shaping_jerk_d_msss` (`_D_JERK`),
`_pid_vel_d_m` (`_D_VEL_`), `_pid_accel_d_m` (`_D_ACC_`), `_pid_vel_ne_m` (`_NE_VEL_`). -/
structure Params where
  PSC_D_POS_P : ftype
  PSC_NE_POS_P : ftype
  PSC_ANGLE_MAX : ftype
  PSC_NE_JERK : ftype
  PSC_D_JERK : ftype
  PSC_D_VEL_P : ftype
  PSC_D_VEL_I : ftype
  PSC_D_VEL_IMAX : ftype
  PSC_D_VEL_FLTE : ftype
  PSC_D_VEL_D : ftype
  PSC_D_VEL_FLTD : ftype
  PSC_D_VEL_FF : ftype
  PSC_D_ACC_P : ftype
  PSC_D_ACC_I : ftype
  PSC_D_ACC_D : ftype
  PSC_D_ACC_FF : ftype
  PSC_D_ACC_IMAX : ftype
  PSC_D_ACC_FLTT : ftype
  PSC_D_ACC_FLTE : ftype
  PSC_D_ACC_FLTD : ftype
  PSC_D_ACC_SMAX : ftype
  PSC_D_ACC_PDMX : ftype
  PSC_D_ACC_D_FF : ftype
  PSC_D_ACC_NTF : Int8
  PSC_D_ACC_NEF : Int8
  PSC_NE_VEL_P : ftype
  PSC_NE_VEL_I : ftype
  PSC_NE_VEL_IMAX : ftype
  PSC_NE_VEL_FLTE : ftype
  PSC_NE_VEL_D : ftype
  PSC_NE_VEL_FLTD : ftype
  PSC_NE_VEL_FF : ftype
deriving Repr

/-- Copter defaults: the constructor arguments (`:357-361`) loaded by
`AP_Param::setup_object_defaults` (`:370`), and the table defaults `_ANGLE_MAX = 0` (`:125`),
`_NE_JERK = POSCONTROL_JERK_NE_MSSS` (`:136`), `_D_JERK = POSCONTROL_JERK_D_MSSS` (`:145`);
`AC_PID`'s `SMAX`, `PDMX`, `D_FF`, `NTF`, `NEF` default to 0 (`AC_PID.cpp:67-96`,
`AC_PID.h:42-43`). -/
def defaults : Params where
  PSC_D_POS_P := POSCONTROL_D_POS_P
  PSC_NE_POS_P := POSCONTROL_NE_POS_P
  PSC_ANGLE_MAX := 0.0
  PSC_NE_JERK := POSCONTROL_JERK_NE_MSSS
  PSC_D_JERK := POSCONTROL_JERK_D_MSSS
  -- `_pid_vel_d_m(POSCONTROL_D_VEL_P, 0.0f, 0.0f, 0.0f, POSCONTROL_D_VEL_IMAX,
  --   POSCONTROL_D_VEL_FILT_HZ, POSCONTROL_D_VEL_FILT_D_HZ)` (:360)
  PSC_D_VEL_P := POSCONTROL_D_VEL_P
  PSC_D_VEL_I := 0.0
  PSC_D_VEL_IMAX := POSCONTROL_D_VEL_IMAX
  PSC_D_VEL_FLTE := POSCONTROL_D_VEL_FILT_HZ
  PSC_D_VEL_D := 0.0
  PSC_D_VEL_FLTD := POSCONTROL_D_VEL_FILT_D_HZ
  PSC_D_VEL_FF := 0.0
  -- `_pid_accel_d_m(POSCONTROL_D_ACC_P, POSCONTROL_D_ACC_I, POSCONTROL_D_ACC_D, 0.0f,
  --   POSCONTROL_D_ACC_IMAX, 0.0f, POSCONTROL_D_ACC_FILT_HZ, 0.0f)` (:361)
  PSC_D_ACC_P := POSCONTROL_D_ACC_P
  PSC_D_ACC_I := POSCONTROL_D_ACC_I
  PSC_D_ACC_D := POSCONTROL_D_ACC_D
  PSC_D_ACC_FF := 0.0
  PSC_D_ACC_IMAX := POSCONTROL_D_ACC_IMAX
  PSC_D_ACC_FLTT := 0.0
  PSC_D_ACC_FLTE := POSCONTROL_D_ACC_FILT_HZ
  PSC_D_ACC_FLTD := 0.0
  PSC_D_ACC_SMAX := 0.0
  PSC_D_ACC_PDMX := 0.0
  PSC_D_ACC_D_FF := 0.0
  PSC_D_ACC_NTF := 0
  PSC_D_ACC_NEF := 0
  -- `_pid_vel_ne_m(POSCONTROL_NE_VEL_P, POSCONTROL_NE_VEL_I, POSCONTROL_NE_VEL_D, 0.0f,
  --   POSCONTROL_NE_VEL_IMAX, POSCONTROL_NE_VEL_FILT_HZ, POSCONTROL_NE_VEL_FILT_D_HZ)` (:359)
  PSC_NE_VEL_P := POSCONTROL_NE_VEL_P
  PSC_NE_VEL_I := POSCONTROL_NE_VEL_I
  PSC_NE_VEL_IMAX := POSCONTROL_NE_VEL_IMAX
  PSC_NE_VEL_FLTE := POSCONTROL_NE_VEL_FILT_HZ
  PSC_NE_VEL_D := POSCONTROL_NE_VEL_D
  PSC_NE_VEL_FLTD := POSCONTROL_NE_VEL_FILT_D_HZ
  PSC_NE_VEL_FF := 0.0

namespace Params

/-- Gains of `_p_pos_ne_m` (`AC_P_2D`, `PSC_NE_POS_`). -/
def _p_pos_ne_m (p : Params) : AC_P_2D.Params := { P := p.PSC_NE_POS_P }
/-- Gains of `_p_pos_d_m` (`AC_P_1D`, `PSC_D_POS_`). -/
def _p_pos_d_m (p : Params) : AC_P_1D.Params := { P := p.PSC_D_POS_P }
/-- Gains of `_pid_vel_ne_m` (`AC_PID_2D`, `PSC_NE_VEL_`). -/
def _pid_vel_ne_m (p : Params) : AC_PID_2D.Params :=
  { P := p.PSC_NE_VEL_P, I := p.PSC_NE_VEL_I, IMAX := p.PSC_NE_VEL_IMAX,
    FLTE := p.PSC_NE_VEL_FLTE, D := p.PSC_NE_VEL_D, FLTD := p.PSC_NE_VEL_FLTD,
    FF := p.PSC_NE_VEL_FF }
/-- Gains of `_pid_vel_d_m` (`AC_PID_Basic`, `PSC_D_VEL_`). -/
def _pid_vel_d_m (p : Params) : AC_PID_Basic.Params :=
  { P := p.PSC_D_VEL_P, I := p.PSC_D_VEL_I, IMAX := p.PSC_D_VEL_IMAX,
    FLTE := p.PSC_D_VEL_FLTE, D := p.PSC_D_VEL_D, FLTD := p.PSC_D_VEL_FLTD,
    FF := p.PSC_D_VEL_FF }

end Params

/-! ### State, `AC_PosControl.h:729-788` -/

/-- The C++ members on the Auto path, same names. Left out: `_disturb_pos_ne_m`,
`_disturb_vel_ne_ms` (zero), `_ahrs_position_NE_reset_count`, `_ahrs_position_D_reset_count`,
`_ekf_reset_method`, `_vibe_comp_enabled` (false); see the file header. -/
structure State where
  _p_pos_ne_m : AC_P_2D.State
  _p_pos_d_m : AC_P_1D.State
  _pid_vel_ne_m : AC_PID_2D.State
  _pid_vel_d_m : AC_PID_Basic.State
  _pid_accel_d_m : AC_PID.State
  /-- RAM value of `PSC_D_ACC_IMAX` (`_pid_accel_d_m._kimax`), raised by `D_update_controller`. -/
  _pid_accel_d_m_kimax : ftype
  _dt_s : ftype
  _last_update_ne_ticks : UInt32
  _last_update_d_ticks : UInt32
  _vel_max_ne_ms : ftype
  _vel_max_up_ms : ftype
  _vel_max_down_ms : ftype
  _accel_max_ne_mss : ftype
  _accel_max_d_mss : ftype
  _jerk_max_ne_msss : ftype
  _jerk_max_d_msss : ftype
  _vel_d_control_ratio : ftype
  _ne_control_scale_factor : ftype
  _roll_target_rad : ftype
  _pitch_target_rad : ftype
  _yaw_target_rad : ftype
  _yaw_rate_target_rads : ftype
  _pos_estimate_ned_m : Vector3p
  _pos_desired_ned_m : Vector3p
  _pos_target_ned_m : Vector3p
  _vel_estimate_ned_ms : Vector3f
  _vel_desired_ned_ms : Vector3f
  _vel_target_ned_ms : Vector3f
  _accel_desired_ned_mss : Vector3f
  _accel_target_ned_mss : Vector3f
  _limit_vector_ned : Vector3f
  _pos_terrain_target_d_m : ftype
  _pos_terrain_d_m : ftype
  _vel_terrain_d_ms : ftype
  _accel_terrain_d_mss : ftype
  _pos_offset_target_ned_m : Vector3p
  _pos_offset_ned_m : Vector3p
  _vel_offset_target_ned_ms : Vector3f
  _vel_offset_ned_ms : Vector3f
  _accel_offset_target_ned_mss : Vector3f
  _accel_offset_ned_mss : Vector3f
  _posvelaccel_offset_target_ne_ms : UInt32
  _posvelaccel_offset_target_d_ms : UInt32
  _angle_max_override_rad : ftype
deriving Repr

/-- Constructor `AC_PosControl(ahrs, motors, attitude_control)`, `AC_PosControl.cpp:353-373`.
Members the initialiser list does not set start at zero (ArduPilot objects are zero-filled);
`_vel_d_control_ratio = 2.0f` and `_ne_control_scale_factor = 1.0` are the in-class
initialisers (h:740, :743). The PID states are those of their constructors. -/
def init (p : Params) : State where
  _p_pos_ne_m := (AC_P_2D.init p.PSC_NE_POS_P).2
  _p_pos_d_m := (AC_P_1D.init p.PSC_D_POS_P).2
  _pid_vel_ne_m := (AC_PID_2D.init p.PSC_NE_VEL_P p.PSC_NE_VEL_I p.PSC_NE_VEL_D p.PSC_NE_VEL_FF
    p.PSC_NE_VEL_IMAX p.PSC_NE_VEL_FLTE p.PSC_NE_VEL_FLTD).2
  _pid_vel_d_m := (AC_PID_Basic.init p.PSC_D_VEL_P p.PSC_D_VEL_I p.PSC_D_VEL_D p.PSC_D_VEL_FF
    p.PSC_D_VEL_IMAX p.PSC_D_VEL_FLTE p.PSC_D_VEL_FLTD).2
  _pid_accel_d_m := (AC_PID.init
    { p := p.PSC_D_ACC_P, i := p.PSC_D_ACC_I, d := p.PSC_D_ACC_D,
      ff := p.PSC_D_ACC_FF, imax := p.PSC_D_ACC_IMAX, filt_T_hz := p.PSC_D_ACC_FLTT,
      filt_E_hz := p.PSC_D_ACC_FLTE, filt_D_hz := p.PSC_D_ACC_FLTD }).2
  _pid_accel_d_m_kimax := p.PSC_D_ACC_IMAX
  _dt_s := 0.0
  _last_update_ne_ticks := 0
  _last_update_d_ticks := 0
  _vel_max_ne_ms := POSCONTROL_SPEED_MS
  _vel_max_up_ms := POSCONTROL_SPEED_UP_MS
  _vel_max_down_ms := POSCONTROL_SPEED_DOWN_MS
  _accel_max_ne_mss := POSCONTROL_ACCEL_NE_MSS
  _accel_max_d_mss := POSCONTROL_ACCEL_D_MSS
  _jerk_max_ne_msss := POSCONTROL_JERK_NE_MSSS
  _jerk_max_d_msss := POSCONTROL_JERK_D_MSSS
  _vel_d_control_ratio := 2.0
  _ne_control_scale_factor := 1.0
  _roll_target_rad := 0.0
  _pitch_target_rad := 0.0
  _yaw_target_rad := 0.0
  _yaw_rate_target_rads := 0.0
  _pos_estimate_ned_m := {}
  _pos_desired_ned_m := {}
  _pos_target_ned_m := {}
  _vel_estimate_ned_ms := {}
  _vel_desired_ned_ms := {}
  _vel_target_ned_ms := {}
  _accel_desired_ned_mss := {}
  _accel_target_ned_mss := {}
  _limit_vector_ned := {}
  _pos_terrain_target_d_m := 0.0
  _pos_terrain_d_m := 0.0
  _vel_terrain_d_ms := 0.0
  _accel_terrain_d_mss := 0.0
  _pos_offset_target_ned_m := {}
  _pos_offset_ned_m := {}
  _vel_offset_target_ned_ms := {}
  _vel_offset_ned_ms := {}
  _accel_offset_target_ned_mss := {}
  _accel_offset_ned_mss := {}
  _posvelaccel_offset_target_ne_ms := 0
  _posvelaccel_offset_target_d_ms := 0
  _angle_max_override_rad := 0.0

/-- Gains of `_pid_accel_d_m` (`AC_PID`, `PSC_D_ACC_`), with the RAM `IMAX`. -/
def pid_accel_d_m_params (p : Params) (s : State) : AC_PID.Params :=
  { P := p.PSC_D_ACC_P, I := p.PSC_D_ACC_I, D := p.PSC_D_ACC_D, FF := p.PSC_D_ACC_FF,
    IMAX := s._pid_accel_d_m_kimax, FLTT := p.PSC_D_ACC_FLTT, FLTE := p.PSC_D_ACC_FLTE,
    FLTD := p.PSC_D_ACC_FLTD, SMAX := p.PSC_D_ACC_SMAX, PDMX := p.PSC_D_ACC_PDMX,
    D_FF := p.PSC_D_ACC_D_FF, NTF := p.PSC_D_ACC_NTF, NEF := p.PSC_D_ACC_NEF }

/-! ### Environment -/

/-- What the C++ reads from `_ahrs` (`AP_AHRS_View&`, h:715) and from `AP::ahrs()`. -/
structure AHRSInputs where
  /-- `_ahrs.cos_yaw()` (`AP_AHRS_View.h:74-76`). -/
  cos_yaw : ftype
  /-- `_ahrs.sin_yaw()` (`AP_AHRS_View.h:83-85`). -/
  sin_yaw : ftype
  /-- `_ahrs.yaw` (`AP_AHRS_View.h:185`). -/
  yaw : ftype
  /-- `_ahrs.get_accel_ef()` (`AP_AHRS_View.h:148-150`): earth-frame specific force, `(0, 0, -g)`
  at rest. -/
  get_accel_ef : Vector3f
  /-- `AP::ahrs().get_control_gain_scaler_XY()` (`AP_AHRS.h:324`); 1 except with optical flow. -/
  get_control_gain_scaler_XY : ftype := 1.0
  /-- `AP::ahrs().get_control_gain_scaler_Z()` (`AP_AHRS.h:325`). -/
  get_control_gain_scaler_Z : ftype := 1.0
deriving Repr

/-- What `update_estimates` reads from `AP::ahrs()`. The two NED getters write their output
unconditionally and return a validity flag (`AP_AHRS.h:263-267`, `AP_AHRS.cpp:2091-2095`), so
both the written value and the flag are inputs. The two fallbacks write only on success
(`AP_AHRS.cpp:1044-1052`, `:990-993`), so they are `Option`s: `some v` means "returned true and
wrote `v`". -/
structure AHRSEstimates where
  /-- `get_relative_position_NED_origin(vec)`: the vector written. -/
  relative_position_NED_origin : Vector3p
  /-- Its return value. -/
  relative_position_NED_origin_ok : Bool
  /-- `get_relative_position_D_origin_float(posD)`. -/
  relative_position_D_origin_float : Option ftype
  /-- `get_velocity_NED(vec)`: the vector written. -/
  velocity_NED : Vector3f
  /-- Its return value. -/
  velocity_NED_ok : Bool
  /-- `get_vert_pos_rate_D(velocity)`. -/
  vert_pos_rate_D : Option ftype
deriving Repr

/-- What the C++ reads from `_attitude_control` (`AC_AttitudeControl&`, h:717), named as the
getters (`AC_AttitudeControl.h:91`, `:118`, `:331`, `:396`, `:408`, `:415`, `:425`). -/
structure AttitudeControlInputs where
  get_att_target_euler_rad : Vector3f
  get_althold_lean_angle_max_rad : ftype
  lean_angle_max_rad : ftype
  get_throttle_in : ftype
  get_ang_vel_roll_max_rads : ftype
  get_ang_vel_pitch_max_rads : ftype
  get_accel_roll_max_radss : ftype
  get_accel_pitch_max_radss : ftype
  get_bf_feedforward : Bool
deriving Repr

/-- `AP::scheduler().ticks32()` and `AP_HAL::millis()`. -/
structure Clock where
  ticks32 : UInt32
  millis : UInt32
deriving Repr

/-- The call `_attitude_control.set_throttle_out(throttle_in, apply_angle_boost, filt_cutoff)`
(`AC_AttitudeControl_Multi.h:61`), returned by `D_update_controller` for the caller to make. -/
structure SetThrottleOut where
  throttle_in : ftype
  apply_angle_boost : Bool
  filt_cutoff : ftype
deriving Repr

/-! ### Accessors, `AC_PosControl.h` -/

/-- `set_dt_s(dt)` (h:50). -/
def set_dt_s (s : State) (dt : ftype) : State := { s with _dt_s := dt }
/-- `get_dt_s()` (h:53). -/
def get_dt_s (s : State) : ftype := s._dt_s
/-- `get_shaping_jerk_NE_msss()` (h:62). -/
def get_shaping_jerk_NE_msss (p : Params) : ftype := p.PSC_NE_JERK
/-- `NE_get_max_speed_ms()` (h:112). -/
def NE_get_max_speed_ms (s : State) : ftype := s._vel_max_ne_ms
/-- `NE_get_max_accel_mss()` (h:115). -/
def NE_get_max_accel_mss (s : State) : ftype := s._accel_max_ne_mss
/-- `NE_set_pos_error_max_m(error_max_m)` (h:119). -/
def NE_set_pos_error_max_m (s : State) (error_max_m : ftype) : State :=
  { s with _p_pos_ne_m := AC_P_2D.set_error_max s._p_pos_ne_m error_max_m }
/-- `NE_get_pos_error_max_m()` (h:122). -/
def NE_get_pos_error_max_m (s : State) : ftype := AC_P_2D.get_error_max s._p_pos_ne_m
/-- `D_get_max_accel_mss()` (h:214). -/
def D_get_max_accel_mss (s : State) : ftype := s._accel_max_d_mss
/-- `get_pos_error_up_m()` (h:217). -/
def get_pos_error_up_m (s : State) : ftype := AC_P_1D.get_error_min s._p_pos_d_m
/-- `get_pos_error_down_m()` (h:220). -/
def get_pos_error_down_m (s : State) : ftype := AC_P_1D.get_error_max s._p_pos_d_m
/-- `get_max_speed_up_ms()` (h:227). -/
def get_max_speed_up_ms (s : State) : ftype := s._vel_max_up_ms
/-- `get_max_speed_down_ms()` (h:230). -/
def get_max_speed_down_ms (s : State) : ftype := s._vel_max_down_ms
/-- `get_pos_estimate_NED_m()` (h:313). -/
def get_pos_estimate_NED_m (s : State) : Vector3p := s._pos_estimate_ned_m
/-- `get_pos_estimate_U_m()` (h:316): `-_pos_estimate_ned_m.z`, narrowed to the `float` return. -/
def get_pos_estimate_U_m (s : State) : ftype := tofloat (-s._pos_estimate_ned_m.z)
/-- `get_pos_target_NED_m()` (h:319). -/
def get_pos_target_NED_m (s : State) : Vector3p := s._pos_target_ned_m
/-- `set_pos_desired_NE_m(pos_desired_ne_m)` (h:322). -/
def set_pos_desired_NE_m (s : State) (pos_desired_ne_m : Vector2p) : State :=
  { s with _pos_desired_ned_m := s._pos_desired_ned_m.set_xy pos_desired_ne_m }
/-- `get_pos_desired_NED_m()` (h:325). -/
def get_pos_desired_NED_m (s : State) : Vector3p := s._pos_desired_ned_m
/-- `get_pos_target_U_m()` (h:332). -/
def get_pos_target_U_m (s : State) : ftype := tofloat (-s._pos_target_ned_m.z)
/-- `get_pos_desired_U_m()` (h:346). -/
def get_pos_desired_U_m (s : State) : ftype := tofloat (-s._pos_desired_ned_m.z)
/-- `get_pos_error_NED_m()` (h:361). -/
def get_pos_error_NED_m (s : State) : Vector3f :=
  ⟨(AC_P_2D.get_error s._p_pos_ne_m).x, (AC_P_2D.get_error s._p_pos_ne_m).y,
   AC_P_1D.get_error s._p_pos_d_m⟩
/-- `get_pos_error_NE_m()` (h:364). -/
def get_pos_error_NE_m (s : State) : ftype := (AC_P_2D.get_error s._p_pos_ne_m).length
/-- `get_pos_error_D_m()` (h:371). -/
def get_pos_error_D_m (s : State) : ftype := AC_P_1D.get_error s._p_pos_d_m
/-- `get_vel_estimate_NED_ms()` (h:377). -/
def get_vel_estimate_NED_ms (s : State) : Vector3f := s._vel_estimate_ned_ms
/-- `get_vel_estimate_U_ms()` (h:380). -/
def get_vel_estimate_U_ms (s : State) : ftype := -s._vel_estimate_ned_ms.z
/-- `set_vel_desired_NED_ms(vel_desired_ned_ms)` (h:387). -/
def set_vel_desired_NED_ms (s : State) (vel_desired_ned_ms : Vector3f) : State :=
  { s with _vel_desired_ned_ms := vel_desired_ned_ms }
/-- `get_vel_desired_NED_ms()` (h:397). -/
def get_vel_desired_NED_ms (s : State) : Vector3f := s._vel_desired_ned_ms
/-- `get_vel_desired_U_ms()` (h:400). -/
def get_vel_desired_U_ms (s : State) : ftype := -s._vel_desired_ned_ms.z
/-- `get_vel_target_NED_ms()` (h:407). -/
def get_vel_target_NED_ms (s : State) : Vector3f := s._vel_target_ned_ms
/-- `get_vel_target_U_ms()` (h:417). -/
def get_vel_target_U_ms (s : State) : ftype := -s._vel_target_ned_ms.z
/-- `set_accel_desired_NE_mss(accel_desired_ne_mss)` (h:423). -/
def set_accel_desired_NE_mss (s : State) (accel_desired_ne_mss : Vector2f) : State :=
  { s with _accel_desired_ned_mss := s._accel_desired_ned_mss.set_xy accel_desired_ne_mss }
/-- `get_accel_target_NED_mss()` (h:426). -/
def get_accel_target_NED_mss (s : State) : Vector3f := s._accel_target_ned_mss
/-- `set_pos_terrain_target_D_m(pos_terrain_target_d_m)` (h:438). -/
def set_pos_terrain_target_D_m (s : State) (pos_terrain_target_d_m : ftype) : State :=
  { s with _pos_terrain_target_d_m := pos_terrain_target_d_m }
/-- `get_pos_terrain_D_m()` (h:450). -/
def get_pos_terrain_D_m (s : State) : ftype := s._pos_terrain_d_m
/-- `get_vel_terrain_D_ms()` (h:453). -/
def get_vel_terrain_D_ms (s : State) : ftype := s._vel_terrain_d_ms
/-- `get_pos_offset_NED_m()` (h:485). -/
def get_pos_offset_NED_m (s : State) : Vector3p := s._pos_offset_ned_m
/-- `get_vel_offset_NED_ms()` (h:488). -/
def get_vel_offset_NED_ms (s : State) : Vector3f := s._vel_offset_ned_ms
/-- `get_accel_offset_NED_mss()` (h:491). -/
def get_accel_offset_NED_mss (s : State) : Vector3f := s._accel_offset_ned_mss
/-- `get_vel_offset_D_ms()` (h:500). -/
def get_vel_offset_D_ms (s : State) : ftype := s._vel_offset_ned_ms.z
/-- `get_accel_offset_D_mss()` (h:503). -/
def get_accel_offset_D_mss (s : State) : ftype := s._accel_offset_ned_mss.z
/-- `get_roll_rad()` (h:508). -/
def get_roll_rad (s : State) : ftype := s._roll_target_rad
/-- `get_pitch_rad()` (h:511). -/
def get_pitch_rad (s : State) : ftype := s._pitch_target_rad
/-- `get_yaw_rad()` (h:514). -/
def get_yaw_rad (s : State) : ftype := s._yaw_target_rad
/-- `get_yaw_rate_rads()` (h:517). -/
def get_yaw_rate_rads (s : State) : ftype := s._yaw_rate_target_rads
/-- `set_lean_angle_max_rad(angle_max_rad)` (h:539). -/
def set_lean_angle_max_rad (s : State) (angle_max_rad : ftype) : State :=
  { s with _angle_max_override_rad := angle_max_rad }
/-- `NE_get_pos_p()` (h:552): the `AC_P_2D` object, as its gains and state. WPNav reads `kP()`. -/
def NE_get_pos_p (p : Params) (s : State) : AC_P_2D.Params × AC_P_2D.State :=
  (p._p_pos_ne_m, s._p_pos_ne_m)
/-- `D_get_pos_p()` (h:555). -/
def D_get_pos_p (p : Params) (s : State) : AC_P_1D.Params × AC_P_1D.State :=
  (p._p_pos_d_m, s._p_pos_d_m)
/-- `NE_get_vel_pid()` (h:558). -/
def NE_get_vel_pid (p : Params) (s : State) : AC_PID_2D.Params × AC_PID_2D.State :=
  (p._pid_vel_ne_m, s._pid_vel_ne_m)
/-- `D_get_vel_pid()` (h:561). -/
def D_get_vel_pid (p : Params) (s : State) : AC_PID_Basic.Params × AC_PID_Basic.State :=
  (p._pid_vel_d_m, s._pid_vel_d_m)
/-- `D_get_accel_pid()` (h:564). -/
def D_get_accel_pid (p : Params) (s : State) : AC_PID.Params × AC_PID.State :=
  (pid_accel_d_m_params p s, s._pid_accel_d_m)
/-- `NE_set_externally_limited()` (h:568). -/
def NE_set_externally_limited (s : State) : State :=
  { s with _limit_vector_ned :=
      { s._limit_vector_ned with x := s._accel_target_ned_mss.x, y := s._accel_target_ned_mss.y } }
/-- `get_vel_D_control_ratio()` (h:595). -/
def get_vel_D_control_ratio (s : State) : ftype := constrain_float s._vel_d_control_ratio 0.0 1.0
/-- `get_estimated_accel_D_mss()` (h:607): `_ahrs.get_accel_ef().z + GRAVITY_MSS`. -/
def get_estimated_accel_D_mss (ahrs : AHRSInputs) : ftype := ahrs.get_accel_ef.z + GRAVITY_MSS
/-- `get_estimated_accel_U_mss()` (h:611). -/
def get_estimated_accel_U_mss (ahrs : AHRSInputs) : ftype := -get_estimated_accel_D_mss ahrs

/-! ### Methods -/

/-- `get_lean_angle_max_rad()`, `AC_PosControl.cpp:1170-1179`. -/
def get_lean_angle_max_rad (p : Params) (s : State) (att : AttitudeControlInputs) : ftype :=
  if is_positive s._angle_max_override_rad then s._angle_max_override_rad
  else if !is_positive p.PSC_ANGLE_MAX then att.lean_angle_max_rad
  else radians p.PSC_ANGLE_MAX

/-- `NE_is_active()`, `AC_PosControl.cpp:689-693` (`uint32_t` arithmetic wraps). -/
def NE_is_active (s : State) (clock : Clock) : Bool :=
  let dt_ticks : UInt32 := clock.ticks32 - s._last_update_ne_ticks
  dt_ticks ≤ 1

/-- `D_is_active()`, `AC_PosControl.cpp:1069-1073`. -/
def D_is_active (s : State) (clock : Clock) : Bool :=
  let dt_ticks : UInt32 := clock.ticks32 - s._last_update_d_ticks
  dt_ticks ≤ 1

/-- `update_estimates(high_vibes)`, `AC_PosControl.cpp:1446-1465`. The AHRS results are the
argument `est` (see `AHRSEstimates`): `_pos_estimate_ned_m` is the vector written by
`get_relative_position_NED_origin`, with `z` replaced by `get_relative_position_D_origin_float`
(widened to `postype_t`) when the first call returns false and the second true;
`_vel_estimate_ned_ms` is the vector written by `get_velocity_NED`, with `z` replaced by
`get_vert_pos_rate_D` when the first call returns false or `high_vibes`, and the second returns
true. -/
def update_estimates (s : State) (est : AHRSEstimates) (high_vibes : Bool := false) : State :=
  Id.run do
  let mut pos_estimate_ned_m : Vector3p := est.relative_position_NED_origin
  if !est.relative_position_NED_origin_ok then
    match est.relative_position_D_origin_float with
    | some posD => pos_estimate_ned_m := { pos_estimate_ned_m with z := topostype posD }
    | none => pure ()
  let mut vel_estimate_ned_ms : Vector3f := est.velocity_NED
  if !est.velocity_NED_ok || high_vibes then
    match est.vert_pos_rate_D with
    | some rate_z => vel_estimate_ned_ms := { vel_estimate_ned_ms with z := rate_z }
    | none => pure ()
  return { s with _pos_estimate_ned_m := pos_estimate_ned_m,
                  _vel_estimate_ned_ms := vel_estimate_ned_ms }

/-- `calculate_overspeed_gain()`, `AC_PosControl.cpp:1673-1687`. -/
def calculate_overspeed_gain (s : State) : ftype :=
  if s._vel_desired_ned_ms.z > s._vel_max_down_ms && !is_zero s._vel_max_down_ms then
    POSCONTROL_OVERSPEED_GAIN_U * s._vel_desired_ned_ms.z / s._vel_max_down_ms
  else if s._vel_desired_ned_ms.z < -s._vel_max_up_ms && !is_zero s._vel_max_up_ms then
    -POSCONTROL_OVERSPEED_GAIN_U * s._vel_desired_ned_ms.z / s._vel_max_up_ms
  else 1.0

/-- `terrain_scaler_D_m(pos_terrain_d_m, terrain_margin_m)`, `AC_PosControl.cpp:433-440`. The
error is formed in `postype_t` and narrowed to the `float` local (:438). -/
def terrain_scaler_D_m (s : State) (pos_terrain_d_m terrain_margin_m : ftype) : ftype :=
  if is_zero terrain_margin_m then 1.0
  else
    let pos_offset_error_d_m : ftype := tofloat (s._pos_estimate_ned_m.z -
      (s._pos_target_ned_m.z + topostype (pos_terrain_d_m - s._pos_terrain_d_m)))
    constrain_float (1.0 - (pos_offset_error_d_m.abs - 0.5 * terrain_margin_m) /
      (0.5 * terrain_margin_m)) 0.01 1.0

/-- `input_pos_NED_m(pos_ned_m, pos_terrain_target_d_m, terrain_margin_m)`,
`AC_PosControl.cpp:386-429`. Not on the default Auto path; see the header for the argument order
of `kinematic_limit` at :410, mirrored as written. -/
def input_pos_NED_m (s : State) (pos_ned_m : Vector3p) (pos_terrain_target_d_m terrain_margin_m : ftype) :
    State := Id.run do
  -- Terrain following velocity scalar must be calculated before we remove the position offset
  let offset_d_scalar := terrain_scaler_D_m s pos_terrain_target_d_m terrain_margin_m
  let mut s := set_pos_terrain_target_D_m s pos_terrain_target_d_m
  -- calculated increased maximum acceleration and jerk if over speed
  let overspeed_gain := calculate_overspeed_gain s
  let accel_max_d_mss := s._accel_max_d_mss * overspeed_gain
  let jerk_max_d_msss := s._jerk_max_d_msss * overspeed_gain
  let (pos_ne, vel_ne) := update_pos_vel_accel_xy s._pos_desired_ned_m.xy s._vel_desired_ned_ms.xy
    s._accel_desired_ned_mss.xy s._dt_s s._limit_vector_ned.xy (AC_P_2D.get_error s._p_pos_ne_m)
    (AC_PID_2D.get_error s._pid_vel_ne_m)
  s := { s with _pos_desired_ned_m := s._pos_desired_ned_m.set_xy pos_ne,
                _vel_desired_ned_ms := s._vel_desired_ned_ms.set_xy vel_ne }
  -- adjust desired altitude if motors have not hit their limits
  let (pos_d, vel_d) := update_pos_vel_accel s._pos_desired_ned_m.z s._vel_desired_ned_ms.z
    s._accel_desired_ned_mss.z s._dt_s s._limit_vector_ned.z (AC_P_1D.get_error s._p_pos_d_m)
    (AC_PID_Basic.get_error s._pid_vel_d_m)
  s := { s with _pos_desired_ned_m := { s._pos_desired_ned_m with z := pos_d },
                _vel_desired_ned_ms := { s._vel_desired_ned_ms with z := vel_d } }
  -- calculate the horizontal and vertical velocity limits to travel directly to the destination
  let mut vel_max_ne_ms : ftype := 0.0
  let mut vel_max_d_ms : ftype := 0.0
  let mut travel_dir_unit : Vector3f := (pos_ned_m - s._pos_desired_ned_m).tofloat
  if is_positive travel_dir_unit.length_squared then
    travel_dir_unit := travel_dir_unit.normalize
    let travel_dir_unit_ne_length := travel_dir_unit.xy.length
    -- :410, as written: (max_xy, max_z_neg, max_z_pos) := (_vel_max_ne_ms, _vel_max_up_ms, _vel_max_down_ms)
    let vel_max_ms := kinematic_limit travel_dir_unit s._vel_max_ne_ms s._vel_max_up_ms s._vel_max_down_ms
    vel_max_ne_ms := vel_max_ms * travel_dir_unit_ne_length
    vel_max_d_ms := (vel_max_ms * travel_dir_unit.z).abs
  -- reduce speed if we are reaching the edge of our vertical buffer
  vel_max_ne_ms := vel_max_ne_ms * offset_d_scalar
  let vel_ne_ms : Vector2f := {}
  let accel_ne_mss : Vector2f := {}
  let accel_desired_ne := shape_pos_vel_accel_xy pos_ned_m.xy vel_ne_ms accel_ne_mss
    s._pos_desired_ned_m.xy s._vel_desired_ned_ms.xy s._accel_desired_ned_mss.xy
    vel_max_ne_ms s._accel_max_ne_mss s._jerk_max_ne_msss s._dt_s false
  s := { s with _accel_desired_ned_mss := s._accel_desired_ned_mss.set_xy accel_desired_ne }
  -- `float pos_d_m = pos_ned_m.z;` narrows (:423)
  let pos_d_m : ftype := tofloat pos_ned_m.z
  let accel_desired_d := shape_pos_vel_accel (topostype pos_d_m) 0 0
    s._pos_desired_ned_m.z s._vel_desired_ned_ms.z s._accel_desired_ned_mss.z
    (-vel_max_d_ms) vel_max_d_ms
    (-accel_max_d_mss) (constrain_float accel_max_d_mss 0.0 7.5)
    jerk_max_d_msss s._dt_s false
  s := { s with _accel_desired_ned_mss := { s._accel_desired_ned_mss with z := accel_desired_d } }
  return s

/-- `NE_set_max_speed_accel_m(speed_ne_ms, accel_ne_mss)`, `AC_PosControl.cpp:458-479`. -/
def NE_set_max_speed_accel_m (p : Params) (s : State) (att : AttitudeControlInputs)
    (speed_ne_ms accel_ne_mss : ftype) : State := Id.run do
  let mut s := { s with _vel_max_ne_ms := speed_ne_ms.abs }
  s := { s with _accel_max_ne_mss := accel_ne_mss.abs }
  -- ensure the horizontal jerk is less than the vehicle is capable of
  let jerk_max_msss := MIN att.get_ang_vel_roll_max_rads att.get_ang_vel_pitch_max_rads * GRAVITY_MSS
  let snap_max_mssss := MIN att.get_accel_roll_max_radss att.get_accel_pitch_max_radss * GRAVITY_MSS
  -- get specified jerk limit
  s := { s with _jerk_max_ne_msss := p.PSC_NE_JERK }
  -- limit maximum jerk based on maximum angular rate
  if is_positive jerk_max_msss && att.get_bf_feedforward then
    s := { s with _jerk_max_ne_msss := MIN s._jerk_max_ne_msss jerk_max_msss }
  -- limit maximum jerk to maximum possible average jerk based on angular acceleration
  if is_positive snap_max_mssss && att.get_bf_feedforward then
    let jerk := MIN (0.5 * safe_sqrt (s._accel_max_ne_mss * snap_max_mssss)) s._jerk_max_ne_msss
    s := { s with _jerk_max_ne_msss := jerk }
  return s

/-- `NE_set_correction_speed_accel_m(speed_ne_ms, accel_ne_mss)`, `AC_PosControl.cpp:493-497`. -/
def NE_set_correction_speed_accel_m (p : Params) (s : State) (speed_ne_ms accel_ne_mss : ftype) :
    State :=
  -- limits that are not positive are ignored
  { s with _p_pos_ne_m := AC_P_2D.set_limits p._p_pos_ne_m s._p_pos_ne_m speed_ne_ms accel_ne_mss 0.0 }

/-- `D_set_max_speed_accel_m(decent_speed_max_ms, climb_speed_max_ms, accel_max_d_mss)`,
`AC_PosControl.cpp:806-827`. -/
def D_set_max_speed_accel_m (p : Params) (s : State)
    (decent_speed_max_ms climb_speed_max_ms accel_max_d_mss : ftype) : State := Id.run do
  let mut s := s
  -- sanity check and update
  if !is_zero decent_speed_max_ms then
    s := { s with _vel_max_down_ms := decent_speed_max_ms.abs }
  if !is_zero climb_speed_max_ms then
    s := { s with _vel_max_up_ms := climb_speed_max_ms.abs }
  if !is_zero accel_max_d_mss then
    s := { s with _accel_max_d_mss := accel_max_d_mss.abs }
  -- ensure the vertical Jerk is not limited by the filters in the Z acceleration PID object
  s := { s with _jerk_max_d_msss := p.PSC_D_JERK }
  let pacc := pid_accel_d_m_params p s
  if is_positive (AC_PID.filt_T_hz pacc) then
    let jerk := MIN s._jerk_max_d_msss
      (MIN GRAVITY_MSS s._accel_max_d_mss * (M_2PI * AC_PID.filt_T_hz pacc) / 5.0)
    s := { s with _jerk_max_d_msss := jerk }
  if is_positive (AC_PID.filt_E_hz pacc) then
    let jerk := MIN s._jerk_max_d_msss
      (MIN GRAVITY_MSS s._accel_max_d_mss * (M_2PI * AC_PID.filt_E_hz pacc) / 5.0)
    s := { s with _jerk_max_d_msss := jerk }
  return s

/-- `D_set_correction_speed_accel_m(decent_speed_max_ms, climb_speed_max_ms, accel_max_d_mss)`,
`AC_PosControl.cpp:841-845`. -/
def D_set_correction_speed_accel_m (p : Params) (s : State)
    (decent_speed_max_ms climb_speed_max_ms accel_max_d_mss : ftype) : State :=
  -- define maximum position error and maximum first and second differential limits
  let p_pos_d_m := AC_P_1D.set_limits p._p_pos_d_m s._p_pos_d_m (-decent_speed_max_ms.abs)
    climb_speed_max_ms.abs accel_max_d_mss.abs 0.0
  { s with _p_pos_d_m := p_pos_d_m }

/-- `set_pos_vel_accel_NED_m(pos_ned_m, vel_ned_ms, accel_ned_mss)`, `AC_PosControl.cpp:1183-1188`. -/
def set_pos_vel_accel_NED_m (s : State) (pos_ned_m : Vector3p) (vel_ned_ms accel_ned_mss : Vector3f) :
    State :=
  { s with _pos_desired_ned_m := pos_ned_m, _vel_desired_ned_ms := vel_ned_ms,
           _accel_desired_ned_mss := accel_ned_mss }

/-- `set_pos_vel_accel_NE_m(pos_ne_m, vel_ne_ms, accel_ne_mss)`, `AC_PosControl.cpp:1192-1197`. -/
def set_pos_vel_accel_NE_m (s : State) (pos_ne_m : Vector2p) (vel_ne_ms accel_ne_mss : Vector2f) :
    State :=
  { s with _pos_desired_ned_m := s._pos_desired_ned_m.set_xy pos_ne_m,
           _vel_desired_ned_ms := s._vel_desired_ned_ms.set_xy vel_ne_ms,
           _accel_desired_ned_mss := s._accel_desired_ned_mss.set_xy accel_ne_mss }

/-- `lean_angles_rad_to_accel_NED_mss(att_target_euler_rad)`, `AC_PosControl.cpp:1200-1215`. -/
def lean_angles_rad_to_accel_NED_mss (att_target_euler_rad : Vector3f) : Vector3f :=
  -- rotate our roll, pitch angles into lat/lon frame
  let sin_roll := att_target_euler_rad.x.sin
  let cos_roll := att_target_euler_rad.x.cos
  let sin_pitch := att_target_euler_rad.y.sin
  let cos_pitch := att_target_euler_rad.y.cos
  let sin_yaw := att_target_euler_rad.z.sin
  let cos_yaw := att_target_euler_rad.z.cos
  ⟨GRAVITY_MSS * (-cos_yaw * sin_pitch * cos_roll - sin_yaw * sin_roll) / MAX (cos_roll * cos_pitch) 0.1,
   GRAVITY_MSS * (-sin_yaw * sin_pitch * cos_roll + cos_yaw * sin_roll) / MAX (cos_roll * cos_pitch) 0.1,
   -GRAVITY_MSS⟩

/-- `lean_angles_to_accel_NE_mss(accel_n_mss, accel_e_mss)`, `AC_PosControl.cpp:1628-1637`; returns
`(accel_n_mss, accel_e_mss)`. -/
def lean_angles_to_accel_NE_mss (ahrs : AHRSInputs) (att : AttitudeControlInputs) : ftype × ftype :=
  -- rotate our roll, pitch angles into lat/lon frame
  let att_target_euler_rad := { att.get_att_target_euler_rad with z := ahrs.yaw }
  let accel_ne_mss := lean_angles_rad_to_accel_NED_mss att_target_euler_rad
  (accel_ne_mss.x, accel_ne_mss.y)

/-- `accel_NE_mss_to_lean_angles_rad(accel_n_mss, accel_e_mss, roll_target_rad, pitch_target_rad)`,
`AC_PosControl.cpp:1615-1625`; returns `(roll_target_rad, pitch_target_rad)`. -/
def accel_NE_mss_to_lean_angles_rad (ahrs : AHRSInputs) (accel_n_mss accel_e_mss : ftype) :
    ftype × ftype :=
  -- rotate accelerations into body forward-right frame
  let accel_forward_mss := accel_n_mss * ahrs.cos_yaw + accel_e_mss * ahrs.sin_yaw
  let accel_right_mss := -accel_n_mss * ahrs.sin_yaw + accel_e_mss * ahrs.cos_yaw
  -- update angle targets that will be passed to stabilize controller
  let pitch_target_rad := accel_mss_to_angle_rad (-accel_forward_mss)
  let cos_pitch_target := pitch_target_rad.cos
  let roll_target_rad := accel_mss_to_angle_rad (accel_right_mss * cos_pitch_target)
  (roll_target_rad, pitch_target_rad)

/-- `calculate_yaw_and_rate_yaw()`, `AC_PosControl.cpp:1641-1670`. -/
def calculate_yaw_and_rate_yaw (s : State) (att : AttitudeControlInputs) : State := Id.run do
  -- Calculate the turn rate
  let mut turn_rate_rads : ftype := 0.0
  let vel_desired_length_ne_ms := s._vel_desired_ned_ms.xy.length
  if is_positive vel_desired_length_ne_ms then
    -- Project acceleration vector into velocity direction to extract forward acceleration component
    let accel_forward_mss := (s._accel_desired_ned_mss.x * s._vel_desired_ned_ms.x +
      s._accel_desired_ned_mss.y * s._vel_desired_ned_ms.y) / vel_desired_length_ne_ms
    -- Subtract forward component to isolate turn acceleration perpendicular to velocity vector
    let accel_turn_ne_mss : Vector2f := s._accel_desired_ned_mss.xy -
      s._vel_desired_ned_ms.xy * accel_forward_mss / vel_desired_length_ne_ms
    -- Compute turn rate from lateral acceleration and velocity (centripetal formula)
    let accel_turn_length_ne_mss := accel_turn_ne_mss.length
    turn_rate_rads := accel_turn_length_ne_mss / vel_desired_length_ne_ms
    -- Determine turn direction: positive = clockwise (right)
    if (accel_turn_ne_mss.y * s._vel_desired_ned_ms.x - accel_turn_ne_mss.x * s._vel_desired_ned_ms.y) < 0.0 then
      turn_rate_rads := -turn_rate_rads
  -- If vehicle is moving significantly, align yaw to velocity vector and apply computed turn rate
  if vel_desired_length_ne_ms > s._vel_max_ne_ms * 0.05 then
    return { s with _yaw_target_rad := s._vel_desired_ned_ms.xy.angle,
                    _yaw_rate_target_rads := turn_rate_rads }
  -- If motion is too slow, retain last yaw target from attitude controller
  return { s with _yaw_target_rad := att.get_att_target_euler_rad.z, _yaw_rate_target_rads := 0 }

/-! ### Terrain and offsets -/

/-- `init_terrain()`, `AC_PosControl.cpp:1220-1231`. -/
def init_terrain (s : State) : State :=
  { s with _pos_terrain_target_d_m := 0.0, _pos_terrain_d_m := 0.0, _vel_terrain_d_ms := 0.0,
           _accel_terrain_d_mss := 0.0 }

/-- `init_pos_terrain_D_m(pos_terrain_d_m)`, `AC_PosControl.cpp:1243-1248`. -/
def init_pos_terrain_D_m (s : State) (pos_terrain_d_m : ftype) : State :=
  let s := { s with _pos_desired_ned_m := { s._pos_desired_ned_m with
    z := s._pos_desired_ned_m.z - topostype (pos_terrain_d_m - s._pos_terrain_d_m) } }
  { s with _pos_terrain_target_d_m := pos_terrain_d_m, _pos_terrain_d_m := pos_terrain_d_m }

/-- `update_terrain()`, `AC_PosControl.cpp:1596-1612`. -/
def update_terrain (s : State) : State := Id.run do
  -- update position, velocity, acceleration offsets for this iteration
  let pos_terrain_d_m : postype := topostype s._pos_terrain_d_m
  let (pos_terrain_d_m, vel_terrain_d_ms) := update_pos_vel_accel pos_terrain_d_m s._vel_terrain_d_ms
    s._accel_terrain_d_mss s._dt_s (MIN s._limit_vector_ned.z 0.0) (AC_P_1D.get_error s._p_pos_d_m)
    (AC_PID_Basic.get_error s._pid_vel_d_m)
  let mut s := { s with _vel_terrain_d_ms := vel_terrain_d_ms }
  s := { s with _pos_terrain_d_m := tofloat pos_terrain_d_m }
  -- input shape horizontal position, velocity and acceleration offsets
  let accel_terrain_d_mss := shape_pos_vel_accel (topostype s._pos_terrain_target_d_m) 0.0 0.0
    (topostype s._pos_terrain_d_m) s._vel_terrain_d_ms s._accel_terrain_d_mss
    (-get_max_speed_up_ms s) (get_max_speed_down_ms s)
    (-D_get_max_accel_mss s) (D_get_max_accel_mss s)
    s._jerk_max_d_msss s._dt_s false
  return { s with _accel_terrain_d_mss := accel_terrain_d_mss }

/-- `NE_init_offsets()`, `AC_PosControl.cpp:1254-1272`. -/
def NE_init_offsets (s : State) (clock : Clock) : State := Id.run do
  let mut s := s
  -- check for offset target timeout
  let now_ms := clock.millis
  if now_ms - s._posvelaccel_offset_target_ne_ms > POSCONTROL_POSVELACCEL_OFFSET_TARGET_TIMEOUT_MS then
    s := { s with
      _pos_offset_target_ned_m := s._pos_offset_target_ned_m.set_xy s._pos_offset_target_ned_m.xy.zero,
      _vel_offset_target_ned_ms := s._vel_offset_target_ned_ms.set_xy s._vel_offset_target_ned_ms.xy.zero,
      _accel_offset_target_ned_mss :=
        s._accel_offset_target_ned_mss.set_xy s._accel_offset_target_ned_mss.xy.zero }
  -- set position, velocity and acceleration offsets to target
  s := { s with _pos_offset_ned_m := s._pos_offset_ned_m.set_xy s._pos_offset_target_ned_m.xy }
  s := { s with _vel_offset_ned_ms := s._vel_offset_ned_ms.set_xy s._vel_offset_target_ned_ms.xy }
  s := { s with _accel_offset_ned_mss := s._accel_offset_ned_mss.set_xy s._accel_offset_target_ned_mss.xy }
  return s

/-- `D_init_offsets()`, `AC_PosControl.cpp:1275-1293`. -/
def D_init_offsets (s : State) (clock : Clock) : State := Id.run do
  let mut s := s
  -- check for offset target timeout
  let now_ms := clock.millis
  if now_ms - s._posvelaccel_offset_target_d_ms > POSCONTROL_POSVELACCEL_OFFSET_TARGET_TIMEOUT_MS then
    s := { s with
      _pos_offset_target_ned_m := { s._pos_offset_target_ned_m with z := 0.0 },
      _vel_offset_target_ned_ms := { s._vel_offset_target_ned_ms with z := 0.0 },
      _accel_offset_target_ned_mss := { s._accel_offset_target_ned_mss with z := 0.0 } }
  -- set position, velocity and acceleration offsets to target
  s := { s with _pos_offset_ned_m := { s._pos_offset_ned_m with z := s._pos_offset_target_ned_m.z } }
  s := { s with _vel_offset_ned_ms := { s._vel_offset_ned_ms with z := s._vel_offset_target_ned_ms.z } }
  s := { s with _accel_offset_ned_mss :=
    { s._accel_offset_ned_mss with z := s._accel_offset_target_ned_mss.z } }
  return s

/-- `set_posvelaccel_offset_target_NE_m(...)`, `AC_PosControl.cpp:1342-1355`. -/
def set_posvelaccel_offset_target_NE_m (s : State) (clock : Clock) (pos_offset_target_ne_m : Vector2p)
    (vel_offset_target_ne_ms accel_offset_target_ne_mss : Vector2f) : State :=
  { s with _pos_offset_target_ned_m := s._pos_offset_target_ned_m.set_xy pos_offset_target_ne_m,
           _vel_offset_target_ned_ms := s._vel_offset_target_ned_ms.set_xy vel_offset_target_ne_ms,
           _accel_offset_target_ned_mss :=
             s._accel_offset_target_ned_mss.set_xy accel_offset_target_ne_mss,
           _posvelaccel_offset_target_ne_ms := clock.millis }

/-- `set_posvelaccel_offset_target_D_m(...)`, `AC_PosControl.cpp:1358-1371`; the `float`
position is widened into the `postype_t` member. -/
def set_posvelaccel_offset_target_D_m (s : State) (clock : Clock)
    (pos_offset_target_d_m vel_offset_target_d_ms accel_offset_target_d_mss : ftype) : State :=
  { s with _pos_offset_target_ned_m := { s._pos_offset_target_ned_m with z := topostype pos_offset_target_d_m },
           _vel_offset_target_ned_ms := { s._vel_offset_target_ned_ms with z := vel_offset_target_d_ms },
           _accel_offset_target_ned_mss :=
             { s._accel_offset_target_ned_mss with z := accel_offset_target_d_mss },
           _posvelaccel_offset_target_d_ms := clock.millis }

/-- `NE_update_offsets()`, `AC_PosControl.cpp:644-663`. -/
def NE_update_offsets (s : State) (clock : Clock) : State := Id.run do
  let mut s := s
  -- Check if NE offset targets have timed out
  let now_ms := clock.millis
  if now_ms - s._posvelaccel_offset_target_ne_ms > POSCONTROL_POSVELACCEL_OFFSET_TARGET_TIMEOUT_MS then
    s := { s with
      _pos_offset_target_ned_m := s._pos_offset_target_ned_m.set_xy s._pos_offset_target_ned_m.xy.zero,
      _vel_offset_target_ned_ms := s._vel_offset_target_ned_ms.set_xy s._vel_offset_target_ned_ms.xy.zero,
      _accel_offset_target_ned_mss :=
        s._accel_offset_target_ned_mss.set_xy s._accel_offset_target_ned_mss.xy.zero }
  -- Advance offset target kinematic state (position, velocity, accel)
  let (pos_t, vel_t) := update_pos_vel_accel_xy s._pos_offset_target_ned_m.xy
    s._vel_offset_target_ned_ms.xy s._accel_offset_target_ned_mss.xy s._dt_s {} {} {}
  s := { s with _pos_offset_target_ned_m := s._pos_offset_target_ned_m.set_xy pos_t,
                _vel_offset_target_ned_ms := s._vel_offset_target_ned_ms.set_xy vel_t }
  let (pos_o, vel_o) := update_pos_vel_accel_xy s._pos_offset_ned_m.xy s._vel_offset_ned_ms.xy
    s._accel_offset_ned_mss.xy s._dt_s s._limit_vector_ned.xy (AC_P_2D.get_error s._p_pos_ne_m)
    (AC_PID_2D.get_error s._pid_vel_ne_m)
  s := { s with _pos_offset_ned_m := s._pos_offset_ned_m.set_xy pos_o,
                _vel_offset_ned_ms := s._vel_offset_ned_ms.set_xy vel_o }
  -- Shape the offset path from current to target using jerk-limited smoothing
  let accel_o := shape_pos_vel_accel_xy s._pos_offset_target_ned_m.xy s._vel_offset_target_ned_ms.xy
    s._accel_offset_target_ned_mss.xy s._pos_offset_ned_m.xy s._vel_offset_ned_ms.xy
    s._accel_offset_ned_mss.xy s._vel_max_ne_ms s._accel_max_ne_mss s._jerk_max_ne_msss s._dt_s false
  return { s with _accel_offset_ned_mss := s._accel_offset_ned_mss.set_xy accel_o }

/-- `D_update_offsets()`, `AC_PosControl.cpp:1039-1066`. -/
def D_update_offsets (s : State) (clock : Clock) : State := Id.run do
  let mut s := s
  -- Check if vertical offset targets have timed out
  let now_ms := clock.millis
  if now_ms - s._posvelaccel_offset_target_d_ms > POSCONTROL_POSVELACCEL_OFFSET_TARGET_TIMEOUT_MS then
    s := { s with
      _pos_offset_target_ned_m := { s._pos_offset_target_ned_m with z := 0.0 },
      _vel_offset_target_ned_ms := { s._vel_offset_target_ned_ms with z := 0.0 },
      _accel_offset_target_ned_mss := { s._accel_offset_target_ned_mss with z := 0.0 } }
  -- Advance current offset state using PID-derived feedback and vertical limits
  let p_offset_d_m : postype := s._pos_offset_ned_m.z
  let (p_offset_d_m, vel_o) := update_pos_vel_accel p_offset_d_m s._vel_offset_ned_ms.z
    s._accel_offset_ned_mss.z s._dt_s (MIN s._limit_vector_ned.z 0.0)
    (AC_P_1D.get_error s._p_pos_d_m) (AC_PID_Basic.get_error s._pid_vel_d_m)
  s := { s with _vel_offset_ned_ms := { s._vel_offset_ned_ms with z := vel_o } }
  s := { s with _pos_offset_ned_m := { s._pos_offset_ned_m with z := p_offset_d_m } }
  -- Shape offset trajectory (position/velocity/acceleration) using jerk-limited smoothing
  let accel_o := shape_pos_vel_accel s._pos_offset_target_ned_m.z s._vel_offset_target_ned_ms.z
    s._accel_offset_target_ned_mss.z s._pos_offset_ned_m.z s._vel_offset_ned_ms.z
    s._accel_offset_ned_mss.z (-get_max_speed_up_ms s) (get_max_speed_down_ms s)
    (-D_get_max_accel_mss s) (D_get_max_accel_mss s) s._jerk_max_d_msss s._dt_s false
  s := { s with _accel_offset_ned_mss := { s._accel_offset_ned_mss with z := accel_o } }
  -- Update target state forward in time with assumed zero velocity/acceleration targets
  let p_offset_d_m : postype := s._pos_offset_target_ned_m.z
  let (p_offset_d_m, vel_t) := update_pos_vel_accel p_offset_d_m s._vel_offset_target_ned_ms.z
    s._accel_offset_target_ned_mss.z s._dt_s 0.0 0.0 0.0
  s := { s with _vel_offset_target_ned_ms := { s._vel_offset_target_ned_ms with z := vel_t } }
  s := { s with _pos_offset_target_ned_m := { s._pos_offset_target_ned_m with z := p_offset_d_m } }
  return s

/-! ### Stopping points -/

/-- `get_stopping_point_NE_m(stopping_point_ne_m)`, `AC_PosControl.cpp:1382-1410`; returns the
point written. -/
def get_stopping_point_NE_m (p : Params) (s : State) : Vector2p := Id.run do
  -- Start from estimated NE position with offset removed
  let mut stopping_point_ne_m : Vector2p := s._pos_estimate_ned_m.xy
  stopping_point_ne_m := stopping_point_ne_m - s._pos_offset_ned_m.xy
  let mut vel_estimate_ne_ms : Vector2f := s._vel_estimate_ned_ms.xy
  vel_estimate_ne_ms := vel_estimate_ne_ms - s._vel_offset_ned_ms.xy
  -- Compute velocity magnitude
  let speed_ne_ms := vel_estimate_ne_ms.length
  if !is_positive speed_ne_ms then
    return stopping_point_ne_m
  -- Use current P gain and max accel to estimate stopping distance
  let kP := AC_P_2D.kP p._p_pos_ne_m
  let stopping_dist_m := stopping_distance (constrain_float speed_ne_ms 0.0 s._vel_max_ne_ms) kP
    s._accel_max_ne_mss
  if !is_positive stopping_dist_m then
    return stopping_point_ne_m
  -- Project stopping distance along current velocity direction
  let stopping_time_s := stopping_dist_m / speed_ne_ms
  stopping_point_ne_m := stopping_point_ne_m + (vel_estimate_ne_ms * stopping_time_s).topostype
  return stopping_point_ne_m

/-- `get_stopping_point_D_m(stopping_point_d_m)`, `AC_PosControl.cpp:1413-1429`; returns the
point written. `float curr_pos_d_m = _pos_estimate_ned_m.z;` narrows, and
`curr_pos_d_m -= _pos_offset_ned_m.z` is evaluated in `double` and narrowed back. -/
def get_stopping_point_D_m (p : Params) (s : State) : postype :=
  let curr_pos_d_m : ftype := tofloat s._pos_estimate_ned_m.z
  let curr_pos_d_m : ftype := tofloat (topostype curr_pos_d_m - s._pos_offset_ned_m.z)
  let curr_vel_d_ms : ftype := s._vel_estimate_ned_ms.z
  let curr_vel_d_ms : ftype := curr_vel_d_ms - s._vel_offset_ned_ms.z
  -- If controller is unconfigured or disabled, return current position
  if !is_positive (AC_P_1D.kP p._p_pos_d_m) || !is_positive s._accel_max_d_mss then
    topostype curr_pos_d_m
  else
    -- Estimate stopping point using current velocity, P gain, and max vertical acceleration
    topostype (curr_pos_d_m + constrain_float (stopping_distance curr_vel_d_ms (AC_P_1D.kP p._p_pos_d_m)
      s._accel_max_d_mss) (-POSCONTROL_STOPPING_DIST_UP_MAX_M) POSCONTROL_STOPPING_DIST_DOWN_MAX_M)

/-! ### Lateral controller -/

/-- `NE_init_controller()`, `AC_PosControl.cpp:544-586`. -/
def NE_init_controller (p : Params) (s : State) (ahrs : AHRSInputs) (att : AttitudeControlInputs)
    (clock : Clock) : State := Id.run do
  -- initialise offsets to target offsets and ensure offset targets are zero if they have not been updated.
  let mut s := NE_init_offsets s clock
  -- set roll, pitch lean angle targets to current attitude
  let att_target_euler_rad := att.get_att_target_euler_rad
  s := { s with _roll_target_rad := att_target_euler_rad.x }
  s := { s with _pitch_target_rad := att_target_euler_rad.y }
  s := { s with _yaw_target_rad := att_target_euler_rad.z }
  s := { s with _yaw_rate_target_rads := 0.0 }
  s := { s with _angle_max_override_rad := 0.0 }
  s := { s with _pos_target_ned_m := s._pos_target_ned_m.set_xy s._pos_estimate_ned_m.xy }
  s := { s with _pos_desired_ned_m :=
    s._pos_desired_ned_m.set_xy (s._pos_target_ned_m.xy - s._pos_offset_ned_m.xy) }
  s := { s with _vel_target_ned_ms := s._vel_target_ned_ms.set_xy s._vel_estimate_ned_ms.xy }
  s := { s with _vel_desired_ned_ms :=
    s._vel_desired_ned_ms.set_xy (s._vel_target_ned_ms.xy - s._vel_offset_ned_ms.xy) }
  -- Set desired acceleration to zero because raw acceleration is prone to noise
  s := { s with _accel_desired_ned_mss := s._accel_desired_ned_mss.set_xy s._accel_desired_ned_mss.xy.zero }
  if !NE_is_active s clock then
    let (accel_n_mss, accel_e_mss) := lean_angles_to_accel_NE_mss ahrs att
    s := { s with _accel_target_ned_mss := { s._accel_target_ned_mss with x := accel_n_mss, y := accel_e_mss } }
  -- limit acceleration using maximum lean angles
  let angle_max_rad := MIN att.get_althold_lean_angle_max_rad (get_lean_angle_max_rad p s att)
  let accel_max_mss := angle_rad_to_accel_mss angle_max_rad
  s := { s with _accel_target_ned_mss :=
    s._accel_target_ned_mss.set_xy (s._accel_target_ned_mss.xy.limit_length accel_max_mss).1 }
  -- initialise I terms from lean angles
  s := { s with _pid_vel_ne_m := AC_PID_2D.reset_filter s._pid_vel_ne_m }
  -- initialise the I term to (_accel_target_ned_mss - _accel_desired_ned_mss)
  let pid_vel_ne_m := AC_PID_2D.set_integrator p._pid_vel_ne_m s._pid_vel_ne_m
    (s._accel_target_ned_mss.xy - s._vel_target_ned_ms.xy * AC_PID_2D.ff p._pid_vel_ne_m)
  s := { s with _pid_vel_ne_m := pid_vel_ne_m }
  -- initialise z_controller time out
  s := { s with _last_update_ne_ticks := clock.ticks32 }
  return s

/-- `NE_init_controller_stopping_point()`, `AC_PosControl.cpp:502-510`. -/
def NE_init_controller_stopping_point (p : Params) (s : State) (ahrs : AHRSInputs)
    (att : AttitudeControlInputs) (clock : Clock) : State :=
  let s := NE_init_controller p s ahrs att clock
  let s := { s with _pos_desired_ned_m := s._pos_desired_ned_m.set_xy (get_stopping_point_NE_m p s) }
  let s := { s with _pos_target_ned_m :=
    s._pos_target_ned_m.set_xy (s._pos_desired_ned_m.xy + s._pos_offset_ned_m.xy) }
  let s := { s with _vel_desired_ned_ms := s._vel_desired_ned_ms.set_xy s._vel_desired_ned_ms.xy.zero }
  { s with _accel_desired_ned_mss := s._accel_desired_ned_mss.set_xy s._accel_desired_ned_mss.xy.zero }

/-- `NE_update_controller()`, `AC_PosControl.cpp:697-788`. -/
def NE_update_controller (p : Params) (s : State) (ahrs : AHRSInputs) (att : AttitudeControlInputs)
    (clock : Clock) : State := Id.run do
  let mut s := s
  -- (NE_handle_ekf_reset left out, see header)
  -- Check for position control time out
  if !NE_is_active s clock then
    s := NE_init_controller p s ahrs att clock
  s := { s with _last_update_ne_ticks := clock.ticks32 }
  -- the estimator might require scaling down of control
  let ahrsControlScaleXY := ahrs.get_control_gain_scaler_XY
  -- Update lateral position, velocity, and acceleration offsets using path shaping
  s := NE_update_offsets s clock
  -- Position Controller
  -- Combine position target with active NE offset to get absolute target
  s := { s with _pos_target_ned_m :=
    s._pos_target_ned_m.set_xy (s._pos_desired_ned_m.xy + s._pos_offset_ned_m.xy) }
  -- determine the combined position of the actual position and the disturbance from system ID
  -- mode (`_disturb_pos_ne_m` is zero, see header)
  let _disturb_pos_ne_m : Vector2f := {}
  let mut comb_pos_ne_m : Vector2p := s._pos_estimate_ned_m.xy
  comb_pos_ne_m := comb_pos_ne_m + _disturb_pos_ne_m.topostype
  -- Run P controller to compute velocity setpoint from position error
  let (p_pos_ne_m, pos_target_ne_m, vel_target_ne_ms) :=
    AC_P_2D.update_all p._p_pos_ne_m s._p_pos_ne_m s._pos_target_ned_m.xy comb_pos_ne_m
  s := { s with _p_pos_ne_m := p_pos_ne_m,
                _pos_target_ned_m := s._pos_target_ned_m.set_xy pos_target_ne_m }
  s := { s with _pos_desired_ned_m :=
    s._pos_desired_ned_m.set_xy (s._pos_target_ned_m.xy - s._pos_offset_ned_m.xy) }
  -- Velocity Controller
  -- Apply AHRS scaling (e.g. for optical flow noise compensation)
  let mut vel_target_ne_ms : Vector2f := vel_target_ne_ms
  vel_target_ne_ms := vel_target_ne_ms * ahrsControlScaleXY
  vel_target_ne_ms := vel_target_ne_ms * s._ne_control_scale_factor
  s := { s with _vel_target_ned_ms := s._vel_target_ned_ms.set_xy vel_target_ne_ms }
  let vel_target_ne := s._vel_target_ned_ms.xy + (s._vel_desired_ned_ms.xy + s._vel_offset_ned_ms.xy)
  s := { s with _vel_target_ned_ms := s._vel_target_ned_ms.set_xy vel_target_ne }
  -- determine the combined velocity of the actual velocity and the disturbance from system ID
  -- mode (`_disturb_vel_ne_ms` is zero, see header)
  let _disturb_vel_ne_ms : Vector2f := {}
  let mut comb_vel_ne_ms : Vector2f := s._vel_estimate_ned_ms.xy
  comb_vel_ne_ms := comb_vel_ne_ms + _disturb_vel_ne_ms
  -- Run velocity PID controller and scale result for control authority
  let (pid_vel_ne_m, accel_target_ne_mss) := AC_PID_2D.update_all p._pid_vel_ne_m s._pid_vel_ne_m
    s._vel_target_ned_ms.xy comb_vel_ne_ms s._dt_s s._limit_vector_ned.xy
  s := { s with _pid_vel_ne_m := pid_vel_ne_m }
  -- Acceleration Controller
  -- Apply AHRS scaling again to correct for measurement distortions
  let mut accel_target_ne_mss : Vector2f := accel_target_ne_mss
  accel_target_ne_mss := accel_target_ne_mss * ahrsControlScaleXY
  accel_target_ne_mss := accel_target_ne_mss * s._ne_control_scale_factor
  s := { s with _ne_control_scale_factor := 1.0 }
  -- pass the correction acceleration to the target acceleration output
  s := { s with _accel_target_ned_mss := s._accel_target_ned_mss.set_xy accel_target_ne_mss }
  let accel_target_ne :=
    s._accel_target_ned_mss.xy + (s._accel_desired_ned_mss.xy + s._accel_offset_ned_mss.xy)
  s := { s with _accel_target_ned_mss := s._accel_target_ned_mss.set_xy accel_target_ne }
  -- limit acceleration using maximum lean angles
  let angle_max_rad := MIN att.get_althold_lean_angle_max_rad (get_lean_angle_max_rad p s att)
  let accel_max_mss := angle_rad_to_accel_mss angle_max_rad
  -- Save unbounded target for use in "limited" check (not unit-consistent with z!)
  s := { s with _limit_vector_ned := s._limit_vector_ned.set_xy s._accel_target_ned_mss.xy }
  -- Normalise desired velocity by max speed for the cross-track reference (guard zero max speed).
  let mut vel_norm_ne : Vector2f := {}
  if is_positive s._vel_max_ne_ms then
    vel_norm_ne := s._vel_desired_ned_ms.xy / s._vel_max_ne_ms
  let (accel_limited, limited) := limit_accel_xy vel_norm_ne s._accel_target_ned_mss.xy accel_max_mss
  s := { s with _accel_target_ned_mss := s._accel_target_ned_mss.set_xy accel_limited }
  if !limited then
    -- _accel_target_ned_mss was not limited so we can zero the xy limit vector
    s := { s with _limit_vector_ned := s._limit_vector_ned.set_xy s._limit_vector_ned.xy.zero }
  -- Convert acceleration to roll/pitch angle targets (used by attitude controller)
  let (roll_target_rad, pitch_target_rad) :=
    accel_NE_mss_to_lean_angles_rad ahrs s._accel_target_ned_mss.x s._accel_target_ned_mss.y
  s := { s with _roll_target_rad := roll_target_rad, _pitch_target_rad := pitch_target_rad }
  -- Update yaw and yaw rate targets to match heading of motion
  s := calculate_yaw_and_rate_yaw s att
  -- (reset of the system ID disturbances left out: they are zero)
  return s

/-! ### Vertical controller -/

/-- `D_init_controller()`, `AC_PosControl.cpp:895-929`. Reads `_attitude_control.get_throttle_in()`
and `_motors.get_throttle_hover()`. -/
def D_init_controller (p : Params) (s : State) (ahrs : AHRSInputs) (motors : AP_Motors.Inputs)
    (att : AttitudeControlInputs) (clock : Clock) : State := Id.run do
  -- initialise terrain targets and offsets to zero
  let mut s := init_terrain s
  -- initialise offsets to target offsets and ensure offset targets are zero if they have not been updated.
  s := D_init_offsets s clock
  s := { s with _pos_target_ned_m := { s._pos_target_ned_m with z := s._pos_estimate_ned_m.z } }
  s := { s with _pos_desired_ned_m :=
    { s._pos_desired_ned_m with z := s._pos_target_ned_m.z - s._pos_offset_ned_m.z } }
  s := { s with _vel_target_ned_ms := { s._vel_target_ned_ms with z := s._vel_estimate_ned_ms.z } }
  s := { s with _vel_desired_ned_ms :=
    { s._vel_desired_ned_ms with z := s._vel_target_ned_ms.z - s._vel_offset_ned_ms.z } }
  -- Reset I term of velocity PID
  s := { s with _pid_vel_d_m := AC_PID_Basic.reset_filter s._pid_vel_d_m }
  s := { s with _pid_vel_d_m := AC_PID_Basic.set_integrator p._pid_vel_d_m s._pid_vel_d_m 0.0 }
  s := { s with _accel_target_ned_mss := { s._accel_target_ned_mss with
    z := constrain_float (get_estimated_accel_D_mss ahrs) (-s._accel_max_d_mss) s._accel_max_d_mss } }
  s := { s with _accel_desired_ned_mss := { s._accel_desired_ned_mss with
    z := s._accel_target_ned_mss.z - (s._accel_offset_ned_mss.z + s._accel_terrain_d_mss) } }
  s := { s with _pid_accel_d_m := AC_PID.reset_filter s._pid_accel_d_m }
  -- Set acceleration PID I term based on the current throttle
  let pacc := pid_accel_d_m_params p s
  let pid_accel_d_m := AC_PID.set_integrator pacc s._pid_accel_d_m
    (-(att.get_throttle_in - AP_Motors.get_throttle_hover motors)
      - AC_PID.kP pacc * (s._accel_target_ned_mss.z - get_estimated_accel_D_mss ahrs)
      - AC_PID.ff pacc * s._accel_target_ned_mss.z)
  s := { s with _pid_accel_d_m := pid_accel_d_m }
  -- (D_init_ekf_reset left out, see header)
  -- initialise z_controller time out
  s := { s with _last_update_d_ticks := clock.ticks32 }
  return s

/-- `D_init_controller_stopping_point()`, `AC_PosControl.cpp:868-877`. -/
def D_init_controller_stopping_point (p : Params) (s : State) (ahrs : AHRSInputs)
    (motors : AP_Motors.Inputs) (att : AttitudeControlInputs) (clock : Clock) : State :=
  let s := D_init_controller p s ahrs motors att clock
  let s := { s with _pos_desired_ned_m := { s._pos_desired_ned_m with z := get_stopping_point_D_m p s } }
  let s := { s with _pos_target_ned_m :=
    { s._pos_target_ned_m with z := s._pos_desired_ned_m.z + s._pos_offset_ned_m.z } }
  let s := { s with _vel_desired_ned_ms := { s._vel_desired_ned_ms with z := 0.0 } }
  { s with _accel_desired_ned_mss := { s._accel_desired_ned_mss with z := 0.0 } }

/-- `D_update_controller()`, `AC_PosControl.cpp:1079-1162`. Returns the new state and the call
`_attitude_control.set_throttle_out(-thrust_d_norm, true, POSCONTROL_THROTTLE_CUTOFF_FREQ_HZ)`
(:1145) that the C++ makes. Reads `_motors.limit.throttle_lower/upper` and
`_motors.get_throttle_hover()` from `motors`; `att` is read only if the controller re-initialises
(`get_throttle_in()` in `D_init_controller`). `_vibe_comp_enabled` is false (header). -/
def D_update_controller (p : Params) (s : State) (ahrs : AHRSInputs) (motors : AP_Motors.Inputs)
    (att : AttitudeControlInputs) (clock : Clock) : State × SetThrottleOut := Id.run do
  let mut s := s
  -- (D_handle_ekf_reset left out, see header)
  -- Check for z_controller time out
  if !D_is_active s clock then
    s := D_init_controller p s ahrs motors att clock
  s := { s with _last_update_d_ticks := clock.ticks32 }
  -- Update vertical offset targets and terrain estimate
  s := D_update_offsets s clock
  s := update_terrain s
  -- Position Controller
  -- Combine desired + offset + terrain for final position target
  s := { s with _pos_target_ned_m := { s._pos_target_ned_m with
    z := s._pos_desired_ned_m.z + s._pos_offset_ned_m.z + topostype s._pos_terrain_d_m } }
  -- P controller: convert position error to velocity target
  let (p_pos_d_m, pos_target_d_m, vel_target_d_ms) :=
    AC_P_1D.update_all p._p_pos_d_m s._p_pos_d_m s._pos_target_ned_m.z s._pos_estimate_ned_m.z
  s := { s with _p_pos_d_m := p_pos_d_m,
                _pos_target_ned_m := { s._pos_target_ned_m with z := pos_target_d_m } }
  s := { s with _vel_target_ned_ms := { s._vel_target_ned_ms with z := vel_target_d_ms } }
  s := { s with _vel_target_ned_ms := { s._vel_target_ned_ms with
    z := s._vel_target_ned_ms.z * ahrs.get_control_gain_scaler_Z } }
  s := { s with _pos_desired_ned_m := { s._pos_desired_ned_m with
    z := s._pos_target_ned_m.z - (s._pos_offset_ned_m.z + topostype s._pos_terrain_d_m) } }
  -- add feed forward component
  s := { s with _vel_target_ned_ms := { s._vel_target_ned_ms with
    z := s._vel_target_ned_ms.z + (s._vel_desired_ned_ms.z + s._vel_offset_ned_ms.z + s._vel_terrain_d_ms) } }
  -- Velocity Controller
  -- PID controller: convert velocity error to acceleration
  let (pid_vel_d_m, accel_target_d_mss) := AC_PID_Basic.update_all p._pid_vel_d_m s._pid_vel_d_m
    s._vel_target_ned_ms.z s._vel_estimate_ned_ms.z s._dt_s motors.limit.throttle_lower
    motors.limit.throttle_upper
  s := { s with _pid_vel_d_m := pid_vel_d_m }
  s := { s with _accel_target_ned_mss := { s._accel_target_ned_mss with z := accel_target_d_mss } }
  s := { s with _accel_target_ned_mss := { s._accel_target_ned_mss with
    z := s._accel_target_ned_mss.z * ahrs.get_control_gain_scaler_Z } }
  -- add feed forward component
  s := { s with _accel_target_ned_mss := { s._accel_target_ned_mss with
    z := s._accel_target_ned_mss.z +
      (s._accel_desired_ned_mss.z + s._accel_offset_ned_mss.z + s._accel_terrain_d_mss) } }
  -- Acceleration Controller
  -- Gravity-compensated vertical acceleration measurement (positive = up)
  let estimated_accel_d_mss := get_estimated_accel_D_mss ahrs
  -- Ensure integrator can produce enough thrust to overcome hover throttle
  if AP_Motors.get_throttle_hover motors > AC_PID.imax (pid_accel_d_m_params p s) then
    s := { s with _pid_accel_d_m_kimax :=
      (AC_PID.set_imax (pid_accel_d_m_params p s) (AP_Motors.get_throttle_hover motors)).IMAX }
  -- Standard PID update using vertical acceleration error (`_vibe_comp_enabled` false)
  let (pid_accel_d_m, thrust_d_norm) := AC_PID.update_all (pid_accel_d_m_params p s) s._pid_accel_d_m
    s._accel_target_ned_mss.z estimated_accel_d_mss s._dt_s
    (motors.limit.throttle_lower || motors.limit.throttle_upper)
  s := { s with _pid_accel_d_m := pid_accel_d_m }
  -- Include FF contribution to reduce delay
  let mut thrust_d_norm : ftype := thrust_d_norm
  thrust_d_norm := thrust_d_norm + AC_PID.get_ff s._pid_accel_d_m
  thrust_d_norm := thrust_d_norm - AP_Motors.get_throttle_hover motors
  -- Actuator commands
  -- Send final throttle output to attitude controller (includes angle boost)
  let out : SetThrottleOut :=
    { throttle_in := -thrust_d_norm, apply_angle_boost := true,
      filt_cutoff := POSCONTROL_THROTTLE_CUTOFF_FREQ_HZ }
  -- Check for vertical controller health
  -- Update health indicator based on error magnitude vs configured speed range
  let error_ratio := AC_PID_Basic.get_error s._pid_vel_d_m / s._vel_max_down_ms
  s := { s with _vel_d_control_ratio := s._vel_d_control_ratio + s._dt_s * 0.1 * (0.5 - error_ratio) }
  s := { s with _vel_d_control_ratio := constrain_float s._vel_d_control_ratio 0.0 2.0 }
  -- set vertical component of the limit vector
  if motors.limit.throttle_upper then
    s := { s with _limit_vector_ned := { s._limit_vector_ned with z := -1.0 } }
  else if motors.limit.throttle_lower then
    s := { s with _limit_vector_ned := { s._limit_vector_ned with z := 1.0 } }
  else
    s := { s with _limit_vector_ned := { s._limit_vector_ned with z := 0.0 } }
  return (s, out)

/-- `get_thrust_vector()`, `AC_PosControl.cpp:1374-1379`: the target acceleration with its
vertical component replaced by `-GRAVITY_MSS`. -/
def get_thrust_vector (s : State) : Vector3f :=
  let accel_target_ned_mss := get_accel_target_NED_mss s
  { accel_target_ned_mss with z := -GRAVITY_MSS }

end AC_PosControl
