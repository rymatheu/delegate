import AC_AttitudeControl.AC_AttitudeControl_Multi

/-!
# Spot check for the `AC_AttitudeControl` / `AC_AttitudeControl_Multi` port

Runs a few 400 Hz ticks in ArduCopter's order (`Copter.cpp:115-136`, `Attitude.cpp:10-24`,
`mode_auto.cpp:1134-1154`): `set_dt_s`, `rate_controller_run` (consuming the rate target stored on
the previous tick), `rate_controller_target_reset`, then `set_throttle_out` (as called by
`AC_PosControl::D_update_controller`) and `input_thrust_vector_heading`. Prints every value with its
bit pattern.

1. Level body at rest, thrust vector `(0, 0, -g)`, heading 0 (both `Angle_And_Rate` and
   `Rate_Only`): every rate target, shaped acceleration and rate PID output should be zero.
2. Tilted thrust vector with the body still level: nonzero targets, and nonzero rate PID outputs
   one tick later.
3. From a fresh state, one tick each: body rolled 45° (thrust error between 30° and 60°, the
   feed-forward fade of `attitude_controller_run_quat`), body rolled 70° (above 60°, yaw rate
   taken from the gyro), and body yawed 90° from the heading (the yaw error cap of
   `thrust_heading_rotation_angles` rewrites `_attitude_target` to 45° from the body).

Run with `lake env lean --run AC_AttitudeControl/AttitudeCheck.lean` after
`lake build AC_AttitudeControl.AC_AttitudeControl_Multi`. Not imported by `AC_AttitudeControl.lean`.
-/

open AP_Math
open AC_AttitudeControl (HeadingCommand HeadingMode)

namespace AC_AttitudeControl.AttitudeCheck

def hex (n : Nat) : String :=
  let s := String.ofList (Nat.toDigits 16 n)
  "0x" ++ String.ofList (List.replicate (8 - s.length) '0') ++ s

def f (x : Float32) : String := s!"{x} [{hex x.toBits.toNat}]"
def v3 (v : Vector3f) : String := s!"({f v.x}, {f v.y}, {f v.z})"
def q (q : Quaternion) : String := s!"({f q.q1}, {f q.q2}, {f q.q3}, {f q.q4})"

/-- One main-loop tick. `gyro` and `attitude_body` are this tick's AHRS samples. -/
def tick (p : AC_AttitudeControl_Multi.Params) (s : AC_AttitudeControl_Multi.State) (m : AP_Motors.Inputs)
    (dt : ftype) (gyro : Vector3f) (attitude_body : Quaternion) (thrust_vector : Vector3f)
    (heading : HeadingCommand) : AC_AttitudeControl_Multi.State × AP_Motors.Inputs :=
  -- run_rate_controller_main (Attitude.cpp:10-24)
  let s := AC_AttitudeControl_Multi.set_dt_s s dt
  let (s, m) := AC_AttitudeControl_Multi.rate_controller_run p s m 0.0 gyro
  let s := AC_AttitudeControl_Multi.rate_controller_target_reset s
  -- AC_PosControl::D_update_controller -> set_throttle_out(thr, true, POSCONTROL_THROTTLE_CUTOFF_FREQ_HZ)
  let (s, m) := AC_AttitudeControl_Multi.set_throttle_out p s m 1.0 1.0 0.35 true 2.0
  -- ModeAuto::wp_run -> input_thrust_vector_heading
  let s := AC_AttitudeControl_Multi.input_thrust_vector_heading p s attitude_body thrust_vector heading
  (s, m)

def print_tick (k : Nat) (s : AC_AttitudeControl_Multi.State) (m : AP_Motors.Inputs) : IO Unit := do
  IO.println s!"tick {k}"
  IO.println s!"  motors roll/pitch/yaw in  {f m._roll_in} {f m._pitch_in} {f m._yaw_in}"
  IO.println s!"  motors roll/pitch/yaw ff  {f m._roll_in_ff} {f m._pitch_in_ff} {f m._yaw_in_ff}"
  IO.println s!"  motors throttle_in {f m._throttle_in}  throttle_avg_max {f m._throttle_avg_max}"
  IO.println s!"  _attitude_target       {q s._attitude_target}"
  IO.println s!"  _ang_vel_target_rads   {v3 s._ang_vel_target_rads}"
  IO.println s!"  _ang_accel_target_rads {v3 s._ang_accel_target_rads}"
  IO.println s!"  _euler_rate_target_rads {v3 s._euler_rate_target_rads}"
  IO.println s!"  _ang_vel_body_rads     {v3 s._ang_vel_body_rads}"
  IO.println s!"  _thrust_angle_rad {f s._thrust_angle_rad}  _thrust_error_angle_rad {f s._thrust_error_angle_rad}"
  IO.println s!"  _feedforward_scalar {f s._feedforward_scalar}  _angle_boost {f s._angle_boost}"

def run (label : String) (s : AC_AttitudeControl_Multi.State) (m : AP_Motors.Inputs) (n : Nat)
    (thrust_vector : Vector3f) (heading : HeadingCommand) (attitude_body : Quaternion := {}) :
    IO (AC_AttitudeControl_Multi.State × AP_Motors.Inputs) := do
  IO.println s!"== {label}"
  let p : AC_AttitudeControl_Multi.Params := {}
  let dt : ftype := 0.0025
  let gyro : Vector3f := {}
  let mut s := s
  let mut m := m
  for k in [0:n] do
    let (s', m') := tick p s m dt gyro attitude_body thrust_vector heading
    s := s'
    m := m'
    print_tick k s m
  return (s, m)

end AC_AttitudeControl.AttitudeCheck

open AC_AttitudeControl.AttitudeCheck in
def main : IO Unit := do
  let s0 : AC_AttitudeControl_Multi.State := {}
  let m0 : AP_Motors.Inputs := { _throttle_thrust_max := 1.0 }
  let hover : Vector3f := ⟨0.0, 0.0, -GRAVITY_MSS⟩
  let (s, m) ← run "level, thrust (0,0,-g), Angle_And_Rate heading 0 rate 0" s0 m0 3 hover
    { yaw_angle_rad := 0.0, yaw_rate_rads := 0.0, heading_mode := .Angle_And_Rate }
  let (s, m) ← run "level, thrust (0,0,-g), Rate_Only rate 0" s m 2 hover
    { yaw_angle_rad := 0.0, yaw_rate_rads := 0.0, heading_mode := .Rate_Only }
  let tilted : Vector3f := ⟨1.0, 0.5, -GRAVITY_MSS⟩
  let _ ← run "level body, thrust (1, 0.5, -g), Angle_And_Rate heading 0" s m 4 tilted
    { yaw_angle_rad := 0.0, yaw_rate_rads := 0.0, heading_mode := .Angle_And_Rate }
  -- branch coverage from a fresh state: thrust error between 30 and 60 deg (feed-forward fade),
  -- above 60 deg (yaw rate taken from the gyro), and a large heading error (yaw cap rewrites the target)
  let _ ← run "body rolled 45 deg, thrust (0,0,-g) (fade branch)" s0 m0 1 hover
    { yaw_angle_rad := 0.0, yaw_rate_rads := 0.0, heading_mode := .Angle_And_Rate }
    (Quaternion.from_euler (radians 45.0) 0.0 0.0)
  let _ ← run "body rolled 70 deg, thrust (0,0,-g) (gyro yaw branch)" s0 m0 1 hover
    { yaw_angle_rad := 0.0, yaw_rate_rads := 0.0, heading_mode := .Angle_And_Rate }
    (Quaternion.from_euler (radians 70.0) 0.0 0.0)
  let _ ← run "level body, body yaw 90 deg, heading 0 (yaw error cap)" s0 m0 1 hover
    { yaw_angle_rad := 0.0, yaw_rate_rads := 0.0, heading_mode := .Angle_And_Rate }
    (Quaternion.from_euler 0.0 0.0 (radians 90.0))
  return ()
