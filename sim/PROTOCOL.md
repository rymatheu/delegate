# The copter vehicles: lock-step protocol

The two vehicles, `copter_lean` (`lean/VehicleMain.lean` over `lean/Vehicle.lean`, the Lean
translations of ArduPilot's classes) and `copter_ref` (`ardupilot/vehicle/copter_ref.cpp`, the same
classes compiled unmodified), both built by `ardupilot/vehicle/build.sh`, run one ArduCopter 400 Hz
tick in Auto per input line, over standard input and output, and flush after every line. The format
is fixed.

## Input: one line per tick, 17 whitespace-separated numbers

    x y z  vx vy vz  ax ay az  q1 q2 q3 q4  p q r  dt

| field | meaning | unit | read as |
|---|---|---|---|
| `x y z` | NED position from the EKF origin | m | `double` (`postype_t` in SITL) |
| `vx vy vz` | NED velocity | m/s | `float` |
| `ax ay az` | earth-frame specific force, NED, as `AP_AHRS::get_accel_ef()` returns it: `0 0 -9.80665` at rest; the controller adds `GRAVITY_MSS` to `az` | m/s² | `float` |
| `q1 q2 q3 q4` | body-to-NED attitude quaternion in ArduPilot's convention (`AP_AHRS::get_quat_body_to_ned`), `q1` the scalar part | | `float` |
| `p q r` | body rates (`get_gyro_latest`), body frame forward-right-down | rad/s | `float` |
| `dt` | period of this tick; rounded to whole microseconds, must be positive (400 Hz: `0.0025`) | s | microseconds |

Each decimal is rounded once, directly to the target format.

## Output: one line per input line

    m1 m2 m3 m4

The actuator values in [0, 1] (`AP_MotorsMulticopter::_actuator`: after the thrust curve, spin
range and slew, before the PWM conversion) of ArduPilot motor slots 0..3 of the quad X frame
(`AP_MotorsMatrix::setup_quad_matrix`, `MOTOR_FRAME_TYPE_X`, `AP_MotorsMatrix.cpp:581-588`).
Angle: direction of the motor arm from the nose, degrees, positive clockwise seen from above.
Spin: direction of the propeller seen from above.

| slot | output | angle | position | spin | yaw factor |
|---|---|---|---|---|---|
| 0 | `SERVO1` (motor 1) | +45 | front right | CCW | +1 |
| 1 | `SERVO2` (motor 2) | -135 | rear left | CCW | +1 |
| 2 | `SERVO3` (motor 3) | -45 | front left | CW | -1 |
| 3 | `SERVO4` (motor 4) | +135 | rear right | CW | -1 |

With `--trace` each line continues with 18 numbers: the navigator target as `AC_PosControl` holds
it after the tick, position (3, NED m, `get_pos_desired_NED_m`), velocity (3,
`get_vel_desired_NED_ms`), acceleration (3, `_accel_desired_ned_mss`); the thrust vector (3,
`get_thrust_vector()`, `(a_N, a_E, -GRAVITY_MSS)`); the attitude target Euler angles (3, rad, roll
pitch yaw, `get_att_target_euler_rad()`); the body-rate targets (3, rad/s, `rate_bf_targets()`,
consumed by the next tick's rate controller). The position equals what `AC_WPNav` sent unless a
position controller moved it by its error clamp.

With `--bits` each line continues with ` |` and the bit patterns, in hex, of the numbers printed
before it (`float` as 8 digits, the three position targets as 16-digit `double`s): equal text after
`|` means equal bits, also for the sign of zero, which the exact decimals drop.

A line that does not parse is reported on standard error and answered with zeros (4, or 22 with
`--trace`); the state does not advance. Blank lines are ignored.

## Timing

Everything on one line is the sample of one tick. Within the tick the order is ArduCopter's
fast-task order: rate controller (this tick's gyro, the previous tick's rate target), motors
output (the previous tick's throttle), AHRS and inertial estimates, then Auto mode (navigator,
position and attitude controllers), whose outputs act on the next tick. The one-tick delay comes
from this order.

## Options

- `--params FILE`: overrides, one per line, `NAME VALUE` with ArduPilot parameter names at commit
  802db19de1 (`ATC_RAT_RLL_P 0.15`, `WP_SPD 8`, `MOT_THST_HOVER 0.42`, ...; a comma may separate
  name and value; `#` starts a comment). The names are those of the classes' var_info tables under
  ArduCopter's prefixes `ATC_`, `PSC`, `MOT_`, `WP_` (`ArduCopter/Parameters.cpp`), set as
  `AP_Param::set_value` sets them. Harness values that are not parameters of these classes:
  `WP_YAW_BEHAVIOR` (0: hold the heading, 1 or 2: look at the next waypoint; default 2),
  `PILOT_Y_RATE_TC` and `ACRO_RP_RATE_TC` (default 0), and two run values, `run.air_density_ratio`
  (default 1) and `run.start_hover` (default 1, see below). `waypoint N E D` appends a mission item
  (a waypoint, NED m from the EKF origin); if any waypoint is given the built-in mission is
  replaced; `mission.clear` drops the waypoints collected so far. Repeatable, read in order.
- `--set "NAME VALUE"`: one more override line, applied after the files; repeatable.
- `--exact`: every number is printed as the exact decimal expansion of its binary value.
  Otherwise numbers print with six decimals (`%.6f`).
- `--print-params`: print every parameter (`NAME VALUE`, exact), the harness values and the
  mission, then exit.
- `--trace`: append the 18 trace numbers.
- `--bits`: append ` |` and the bit patterns of the printed numbers.

Defaults: ArduPilot's code defaults, except `MOT_HOVER_LEARN 0`, `MOT_THST_HOVER 0.39`,
`ATC_RAT_YAW_P 0.3`, `ATC_RAT_YAW_I 0.02` (SITL's `copter.parm`), and `MOT_BAT_VOLT_MAX 0`
(the code default, which SITL's `copter.parm` changes). Built-in mission: `waypoint 0 0 -5`,
`waypoint 10 0 -5`, `waypoint 10 10 -5`.

## Initial condition

The vehicle is armed and flying. With the first sample, before the first tick, the attitude
target is set to the sample's attitude (`relax_attitude_controllers`) and, with
`run.start_hover 1`, the vehicle is taken to be hovering at `MOT_THST_HOVER`
(`set_throttle_out(hover)` and the motors' throttle filter at that value). On the first tick the
vehicle switches into Auto (`ModeAuto::init`: the navigator starts from the stopping point), and
the mission starts: each waypoint is the destination of AC_WPNav (`set_wp_destination_NED_m`),
the next one its next destination (`set_wp_destination_next_NED_m`), and the mission advances when
AC_WPNav reports the destination reached (`ModeAuto::do_nav_wp`, `verify_nav_wp`). An empty mission
is refused. After the last waypoint the vehicle holds its stopping point (`ModeAuto::exit_mission`
→ `loiter_start`, AutoYaw HOLD).

## The AHRS

The input line is the AHRS estimate. Both vehicles derive the AHRS view from it as
`AP_AHRS_View::update` does for `ROTATION_NONE` without pitch trim: the rotation matrix of the
quaternion (`QuaternionT::rotation_matrix`), its Euler angles (`Matrix3::to_euler`) and their sines
and cosines (`AP_AHRS::calc_trig`); `copter_lean` runs the translation of these two functions,
`copter_ref` the AHRS stub of `ardupilot/stubs/AP_AHRS`, which does the same with the compiled
AP_Math. As in that stub, the attitude controller reads the estimate's quaternion itself.
