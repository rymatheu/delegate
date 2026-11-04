import Copter.Parameters
import Copter.AHRS

/-!
# `Copter.State`: the vehicle object

The members of ArduCopter's `Copter` object (`ArduCopter/Copter.h`) that the ported Auto-mode
loop uses: the library objects (`motors`, `attitude_control`, `pos_control`, `wp_nav`), the
static `Mode::auto_yaw` (`mode.h:311-410`, `autoyaw.cpp:3`), the `ModeAuto` members on the
waypoint path (`mode.h`, class `ModeAuto`) with the mission (`AP_Mission`, reduced to a list of
`MAV_CMD_NAV_WAYPOINT` items), the scheduler clock (`AP_Scheduler`: `_tick_counter32`,
`_last_loop_time_s`, and the HAL microsecond clock), and the AHRS view of the tick.

Also the environment records the libraries read, built from the current states with the C++
getter definitions: `attInputs` (what `AC_PosControl` and `AC_WPNav` read from
`_attitude_control`), `clock`, `wpEnv`.
-/

namespace Copter

open AP_Math

/-- `AP_Scheduler` and HAL time. -/
structure Scheduler where
  /-- `_tick_counter32` (`AP_Scheduler.h:125`), incremented by `tick()` before the tasks run
  (`AP_Scheduler.cpp:377`). -/
  ticks32 : UInt32 := 0
  /-- `AP_HAL::micros64()` at the sample of the current tick: the sum of the loop times. -/
  micros : Nat := 0
  /-- `_last_loop_time_s` (`AP_Scheduler.cpp:360-364`): `(sample_time_us - _loop_timer_start_us)
  * 1.0e-6`, a `float`. -/
  last_loop_time_s : ftype := 0.0
deriving Repr

/-- `AutoYaw::Mode` (`mode.h:317-329`), the modes reachable on the ported path: the
`WP_YAW_BEHAVIOR` defaults (`autoyaw.cpp:37-58`) and `HOLD` after the mission
(`ModeAuto::loiter_start`). `ROI`, `FIXED`, `RESET_TO_ARMED_YAW`, `ANGLE_RATE`, `RATE`, `CIRCLE`,
`PILOT_RATE`, `WEATHERVANE` are entered only by DO commands, other modes, the pilot or the
weathervane, none of which is ported. -/
inductive AutoYawMode where
  | HOLD
  | LOOK_AT_NEXT_WP
  | LOOK_AHEAD
deriving Repr, DecidableEq

/-- The members of `Mode::AutoYaw` (`mode.h:372-410`) on the ported path. -/
structure AutoYaw where
  /-- `_mode` (`mode.h:373`, initialised to `LOOK_AT_NEXT_WP`). -/
  _mode : AutoYawMode := .LOOK_AT_NEXT_WP
  _yaw_angle_rad : ftype := 0.0
  _yaw_rate_rads : ftype := 0.0
  _look_ahead_yaw_rad : ftype := 0.0
  _pilot_yaw_rate_rads : ftype := 0.0
deriving Repr

/-- `ModeAuto::SubMode` (`mode.h`), the submodes reachable with a waypoint-only mission. -/
inductive SubMode where
  | STARTING
  | WP
  | LOITER
deriving Repr, DecidableEq

/-- `AP_Mission::mission_state` (`AP_Mission.h`). -/
inductive MissionState where
  | MISSION_STOPPED
  | MISSION_RUNNING
  | MISSION_COMPLETE
deriving Repr, DecidableEq

/-- `AP_Mission::Mission_Command`, reduced to `MAV_CMD_NAV_WAYPOINT` with the location as a NED
vector from the EKF origin (`Location` is not ported). -/
structure MissionCommand where
  /-- `index` in the stored mission; 0 is home, so the first item is 1
  (`AP_MISSION_FIRST_REAL_COMMAND`). -/
  index : Nat
  /-- `p1`: the loiter time at the waypoint, s (0 for the run). -/
  p1 : UInt16 := 0
  /-- `content.location`, as NED m from the EKF origin. -/
  location : Vector3p
deriving Repr

/-- The `AP_Mission` members the waypoint path uses. -/
structure Mission where
  state : MissionState := .MISSION_STOPPED
  /-- `_nav_cmd` (`index == AP_MISSION_CMD_INDEX_NONE` is `none`). -/
  nav_cmd : Option MissionCommand := none
  /-- `_flags.nav_cmd_loaded`. -/
  nav_cmd_loaded : Bool := false
deriving Repr

/-- The `ModeAuto` members on the waypoint path. -/
structure ModeAutoState where
  /-- `_mode`, the submode. -/
  _mode : SubMode := .STARTING
  /-- `waiting_to_start`. -/
  waiting_to_start : Bool := false
  /-- `loiter_time` (ms). -/
  loiter_time : UInt32 := 0
  /-- `loiter_time_max` (s). -/
  loiter_time_max : UInt16 := 0
  mission : Mission := {}
deriving Repr

/-- The vehicle. -/
structure State where
  scheduler : Scheduler := {}
  /-- The AHRS view of the current tick (`read_AHRS`). -/
  ahrs : AHRS.View := {}
  /-- `AP_InertialSensor`: the gyro published by `ins.update()` this tick. -/
  ins_gyro : Vector3f := {}
  motors : AP_MotorsMatrix.State
  attitude_control : AC_AttitudeControl_Multi.State := {}
  pos_control : AC_PosControl.State
  wp_nav : AC_WPNav.State
  auto_yaw : AutoYaw := {}
  mode_auto : ModeAutoState := {}
  /-- Whether the harness has switched the vehicle into Auto (`Copter::set_mode`), see
  `Copter.Loop`. -/
  in_auto : Bool := false
  /-- The actuator outputs of the last `motors_output`, slots 0..3. -/
  actuators : Vector ftype 4 := #v[0.0, 0.0, 0.0, 0.0]

/-- The objects as constructed at boot (each library's constructor and `init`). -/
def State.init (p : Parameters) : State :=
  { motors := AP_MotorsMatrix.init p.mot,
    pos_control := AC_PosControl.init p.psc,
    wp_nav := AC_WPNav.init p.wpnav }

/-- The clock as `AC_PosControl` and `AC_WPNav` read it: `ticks32()` and `millis()`. -/
def State.clock (s : State) : AC_PosControl.Clock :=
  { ticks32 := s.scheduler.ticks32, millis := UInt32.ofNat (s.scheduler.micros / 1000) }

/-- `AP_HAL::millis()`. -/
def State.millis (s : State) : UInt32 := UInt32.ofNat (s.scheduler.micros / 1000)

/-- What `AC_PosControl` and `AC_WPNav` read from `_attitude_control`, with the getter
definitions of `AC_AttitudeControl.h` (`:91-139`, `:330-345`, `:396-429`). -/
def attInputs (p : Parameters) (a : AC_AttitudeControl_Multi.State) : AC_PosControl.AttitudeControlInputs :=
  let ap := p.att.toParams
  { get_att_target_euler_rad := AC_AttitudeControl.get_att_target_euler_rad a.toState,
    get_althold_lean_angle_max_rad := AC_AttitudeControl.get_althold_lean_angle_max_rad a.toState,
    lean_angle_max_rad := AC_AttitudeControl.lean_angle_max_rad ap,
    get_throttle_in := AC_AttitudeControl.get_throttle_in a.toState,
    get_ang_vel_roll_max_rads := AC_AttitudeControl.get_ang_vel_roll_max_rads ap,
    get_ang_vel_pitch_max_rads := AC_AttitudeControl.get_ang_vel_pitch_max_rads ap,
    get_accel_roll_max_radss := AC_AttitudeControl.get_accel_roll_max_radss ap,
    get_accel_pitch_max_radss := AC_AttitudeControl.get_accel_pitch_max_radss ap,
    get_bf_feedforward := AC_AttitudeControl.get_bf_feedforward ap }

/-- The environment of the `AC_WPNav` calls, from the current vehicle state. -/
def State.wpEnv (p : Parameters) (s : State) : AC_WPNav.Env :=
  { ahrs := s.ahrs.posInputs, att := attInputs p s.attitude_control,
    att_input_tc := AC_AttitudeControl.get_input_tc p.att.toParams,
    motors := s.motors.toInputs, clock := s.clock }

end Copter
