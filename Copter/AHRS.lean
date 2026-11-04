import AC_AttitudeControl

/-!
# `Copter.AHRS`: the sensor and estimator readings of one tick

The AHRS and the inertial sensors are not ported; they are the environment. One tick's readings
arrive as `Sample` (one input line of the `copter` executable, see `Copter/PROTOCOL.md`) and are
turned into what the controllers read from `AP_AHRS_View` (Copter's `ahrs_view`, created with
`ROTATION_NONE`, `ArduCopter/system.cpp`) and from `AP::ahrs()`:

- `get_quat_body_to_ned` is the sample's quaternion itself (the protocol defines it as that
  value). In ArduPilot the view returns `from_rotation_matrix(rot_body_to_ned)`
  (`AP_AHRS_View.h:55-57`), i.e. the EKF quaternion after a round trip through the matrix; the
  two agree to rounding.
- `rot_body_to_ned` is `Quaternion.rotation_matrix` of the sample's quaternion
  (`quaternion.cpp:58-80`). In ArduPilot it is the EKF's own matrix; same remark.
- `roll`, `pitch`, `yaw` are `rot_body_to_ned.to_euler` (`AP_AHRS_View::update`,
  `AP_AHRS_View.cpp:65`), and the trigonometric values are `AP_AHRS::calc_trig`
  (`AP_AHRS_Backend.cpp:93-135`), both ported here.
- `get_gyro_latest` is the sample's body rates. With `ROTATION_NONE` the view multiplies by the
  identity `rot_view` (`AP_AHRS_View.cpp:79-81`); that product is not formed (it only turns a
  `-0` component into `+0`).
- `get_accel_ef` is the sample's earth-frame specific force, `(0, 0, -GRAVITY_MSS)` at rest.
- `get_relative_position_NED_origin`, `get_relative_position_D_origin_float`, `get_velocity_NED`,
  `get_vert_pos_rate_D` (read by `AC_PosControl::update_estimates`) all succeed and return the
  sample's position, its `z` narrowed to `float`, its velocity and its `vz`.
- `get_control_gain_scaler_XY/Z` are 1 (no optical flow).

Not one to one: `AP_AHRS_View::update` also computes `roll_sensor` etc. (centidegrees, logging);
left out.
-/

namespace Copter.AHRS

open AP_Math

/-- One tick's sensor and estimator readings (one input line). -/
structure Sample where
  /-- NED position from the EKF origin, m (`postype_t`). -/
  pos : Vector3p
  /-- NED velocity, m/s. -/
  vel : Vector3f
  /-- Earth-frame specific force `get_accel_ef()`, NED, m/s². -/
  accel_ef : Vector3f
  /-- Body-to-NED attitude, `q1` scalar. -/
  quat : Quaternion
  /-- Body rates `get_gyro_latest()`, rad/s. -/
  gyro : Vector3f
  /-- Loop time in whole microseconds (the scheduler measures `uint32_t` microseconds). -/
  dt_us : Nat
deriving Repr

/-- `AP_AHRS::calc_trig(rot, cr, cp, cy, sr, sp, sy)` (`AP_AHRS_Backend.cpp:93-135`); returns
`(cos_roll, cos_pitch, cos_yaw, sin_roll, sin_pitch, sin_yaw)`. The C++ leaves `sr` unwritten when
`cp` is zero and then overwrites it in the fallback, which is always taken in that case; so the
initial value of `sr` here does not matter. -/
def calc_trig (rot : Matrix3f) : ftype × ftype × ftype × ftype × ftype × ftype := Id.run do
  let mut yaw_vector : Vector2f := ⟨rot.a.x, rot.b.x⟩
  if yaw_vector.x.abs > 0 || yaw_vector.y.abs > 0 then
    yaw_vector := yaw_vector.normalize
  let mut sy := constrain_float yaw_vector.y (-1.0) 1.0
  let mut cy := constrain_float yaw_vector.x (-1.0) 1.0
  -- sanity checks
  if yaw_vector.is_inf || yaw_vector.is_nan then
    sy := 0.0
    cy := 1.0
  let cx2 := rot.c.x * rot.c.x
  let mut cp : ftype := 0
  let mut cr : ftype := 0
  if cx2 ≥ 1.0 then
    cp := 0
    cr := 1.0
  else
    cp := safe_sqrt (1 - cx2)
    cr := rot.c.z / cp
  cp := constrain_float cp 0.0 1.0
  cr := constrain_float cr (-1.0) 1.0
  let sp := -rot.c.x
  let mut sr : ftype := 0
  if !is_zero cp then
    sr := rot.c.y / cp
  if is_zero cp || cr.isInf || cr.isNaN || sr.isInf || sr.isNaN then
    let (r, _p, _y) := rot.to_euler
    cr := r.cos
    sr := r.sin
  return (cr, cp, cy, sr, sp, sy)

/-- What the controllers read from `AP_AHRS_View` and `AP::ahrs()` on one tick. -/
structure View where
  quat_body_to_ned : Quaternion := {}
  rot_body_to_ned : Matrix3f := {}
  roll : ftype := 0
  pitch : ftype := 0
  yaw : ftype := 0
  cos_roll : ftype := 1
  cos_pitch : ftype := 1
  cos_yaw : ftype := 1
  sin_roll : ftype := 0
  sin_pitch : ftype := 0
  sin_yaw : ftype := 0
  gyro_latest : Vector3f := {}
  accel_ef : Vector3f := {}
  pos_ned : Vector3p := {}
  vel_ned : Vector3f := {}
deriving Repr

/-- `AP_AHRS::update` and `AP_AHRS_View::update` (`AP_AHRS_View.cpp:56-76`) on a sample. -/
def update (smp : Sample) : View :=
  let rot := smp.quat.rotation_matrix
  let (roll, pitch, yaw) := rot.to_euler
  let (cr, cp, cy, sr, sp, sy) := calc_trig rot
  { quat_body_to_ned := smp.quat, rot_body_to_ned := rot, roll, pitch, yaw,
    cos_roll := cr, cos_pitch := cp, cos_yaw := cy, sin_roll := sr, sin_pitch := sp, sin_yaw := sy,
    gyro_latest := smp.gyro, accel_ef := smp.accel_ef, pos_ned := smp.pos, vel_ned := smp.vel }

/-- `AC_PosControl`'s view of the AHRS. -/
def View.posInputs (v : View) : AC_PosControl.AHRSInputs :=
  { cos_yaw := v.cos_yaw, sin_yaw := v.sin_yaw, yaw := v.yaw, get_accel_ef := v.accel_ef }

/-- What `AC_PosControl::update_estimates` reads (header). -/
def View.estimates (v : View) : AC_PosControl.AHRSEstimates :=
  { relative_position_NED_origin := v.pos_ned, relative_position_NED_origin_ok := true,
    relative_position_D_origin_float := some (tofloat v.pos_ned.z),
    velocity_NED := v.vel_ned, velocity_NED_ok := true, vert_pos_rate_D := some v.vel_ned.z }

end Copter.AHRS
