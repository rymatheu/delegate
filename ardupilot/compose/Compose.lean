import Copter_lib

/-!
# Per-tick composition of the translated classes (ardupilot/compose/compose.sh)

The controllers of the World translation `Copter_lib` (AP_MotorsMatrix, AC_AttitudeControl_Multi,
AC_PosControl; cpp2lean `--world`, `ardupilot/translate_copter.sh`), driven for one 400 Hz tick the
way the reference harness that recorded `ardupilot/data/oracle-nosincos.txt` drives the compiled
classes: scheduler loop time, rate controller, motors output, AHRS view, estimates, the first
tick's entry into Auto (the calls of `AC_WPNav::wp_and_spline_init_m` into AC_PosControl), the
navigator's targets from the recorded trace, the position controllers, AutoYaw LOOK_AT_NEXT_WP,
the attitude controller. Everything here is harness; the controllers are the translation,
unchanged, and their calls into each other (the attitude controller into the motors, the position
controller into the attitude controller) are translated calls on the World's objects. What the
harness sets is the boundary: each object's `Inputs` (`'inp`), from the environment line.

Input: the lines of `compose_env` (the per-tick environment, hex). Output: per tick the 22 numbers
of the oracle's output after `|` (actuators, position/velocity/acceleration targets, thrust
vector, attitude target Euler angles, body-rate targets), as hex bit patterns.
-/

open FloatLib.Floats (Binary32 Binary64)

namespace Compose

def hexNat (s : String) : Nat :=
  s.foldl (fun n c => n * 16 + (if c.isDigit then c.toNat - '0'.toNat else c.toLower.toNat - 'a'.toNat + 10)) 0
def f32 (s : String) : Binary32 := Binary32.ofBits (hexNat s).toUInt32
def f64 (s : String) : Binary64 := Binary64.ofBits (hexNat s).toUInt64
def hex (width : Nat) (n : Nat) : String :=
  let d := String.ofList (Nat.toDigits 16 n)
  String.ofList (List.replicate (width - d.length) '0') ++ d
def h32 (x : Binary32) : String := hex 8 (Binary32.toBits x).toNat
def h64 (x : Binary64) : String := hex 16 (Binary64.toBits x).toNat

/-- One environment line (compose_env.cpp). -/
structure Env where
  dt_us : UInt64
  gyro : Array Binary32
  view : Array Binary32      -- q1 q2 q3 q4 roll pitch yaw cos_roll cos_pitch cos_yaw sin_roll sin_pitch sin_yaw
  pos : Array Binary64
  vel : Array Binary32
  acc : Array Binary32
  npos : Array Binary64
  nvel : Array Binary32
  nacc : Array Binary32

def Env.parse (line : String) : Env :=
  let t := (((line.trimAscii.toString).splitOn " ").filter (· ≠ "")).toArray
  let fs (a b : Nat) := ((t.extract a b).map f32)
  let ds (a b : Nat) := ((t.extract a b).map f64)
  { dt_us := (t[0]!.toNat?.getD 0).toUInt64, gyro := fs 1 4, view := fs 4 17, pos := ds 17 20,
    vel := fs 20 23, acc := fs 23 26, npos := ds 26 29, nvel := fs 29 32, nacc := fs 32 35 }

/-- The harness's world: the controllers' World, the scheduler, the clock, the AHRS view and sample. -/
structure World where
  c : Copter_lib.World
  ticks32 : UInt32 := 0
  micros : UInt64 := 0
  last_loop_time_s : Binary32 := 0
  gyro : Array Binary32 := #[0, 0, 0]
  view : Array Binary32 := #[1, 0, 0, 0, 0, 0, 0, 1, 1, 1, 0, 0, 0]
  pos : Array Binary64 := #[0, 0, 0]
  vel : Array Binary32 := #[0, 0, 0]
  acc : Array Binary32 := #[0, 0, 0]
  in_auto : Bool := false
  /-- AutoYaw's mode: LOOK_AT_NEXT_WP until the navigator's mission completes (ModeAuto::loiter_start,
  tick `--hold-from` of the oracle), HOLD after. -/
  hold : Bool := false

/-- `AP_HAL::millis()` and `AP_HAL::micros()` of the harness's HAL (ardupilot/stubs/oracle_env.cpp). -/
def World.millis (w : World) : UInt32 := (w.micros / 1000).toUInt32
def World.micros32 (w : World) : UInt32 := w.micros.toUInt32

/-- The controllers' boundary inputs (their `'inp` fields): the AHRS view and the AHRS stub's
answers for the line, the scheduler's loop time, the HAL clock. -/
def setInputs (w : World) : World :=
  let v := w.view
  let clk : Copter_lib.AC_PID.Inputs := { _slew_limiter := { millis := w.millis } }
  let one : Binary32 := Binary32.ofBits 0x3f800000 /- 1.0 -/
  { w with c := { w.c with
      attitude_control'inp := { get_quat_body_to_ned_q := { q1 := v[0]!, q2 := v[1]!, q3 := v[2]!, q4 := v[3]! }, yaw := v[6]!,
                                get_filtered_loop_time := w.last_loop_time_s, cos_pitch := v[8]!, cos_roll := v[7]!, micros64 := w.micros,
                                get_gyro_latest := { x := w.gyro[0]!, y := w.gyro[1]!, z := w.gyro[2]! },
                                _pid_rate_roll := clk, _pid_rate_pitch := clk, _pid_rate_yaw := clk },
      pos_control'inp := { get_relative_position_NED_origin_vec := { x := w.pos[0]!, y := w.pos[1]!, z := w.pos[2]! },
                           get_relative_position_NED_origin := true,
                           get_relative_position_D_origin_float_posD := Binary64.toBinary32 w.pos[2]!, get_relative_position_D_origin_float := true,
                           get_velocity_NED_vec := { x := w.vel[0]!, y := w.vel[1]!, z := w.vel[2]! }, get_velocity_NED := true,
                           get_vert_pos_rate_D_velocity := w.vel[2]!, get_vert_pos_rate_D := true,
                           millis := w.millis, ticks32 := w.ticks32, yaw := v[6]!, get_position_NE_reset_count := 0,
                           has_good_timing := true, get_control_gain_scaler_XY := one, cos_yaw := v[9]!, sin_yaw := v[12]!,
                           get_accel_ef := { x := w.acc[0]!, y := w.acc[1]!, z := w.acc[2]! },
                           get_position_D_reset_count := 0, get_control_gain_scaler_Z := one, _pid_accel_d_m := clk },
      motors'inp := { micros := w.micros32, thr_lin := { get_air_density_ratio := one } } } }

/-- `attitude_control.set_throttle_out(...)` on the World. -/
def setThrottleOut (w : World) (thr : Binary32) (boost : Bool) (cutoff : Binary32) : World :=
  let c := w.c
  let (s, c) := Copter_lib.AC_AttitudeControl_Multi.set_throttle_out c.attitude_control'p c.attitude_control c c.attitude_control'inp thr boost cutoff
  { w with c := { c with attitude_control := s } }

/-- Construction and parameters (the reference harness: the code defaults, SITL's run deviations,
then sim/params/copter-cf2x.txt and copter-course-speed.txt), boot, and the takeover on the first
sample. -/
def start (e0 : Env) : World := Id.run do
  let c := Copter_lib.World.init
  let mp := c.motors'p
  let ap := c.attitude_control'p
  -- ATC_RAT_YAW_P 0.3, ATC_RAT_YAW_I 0.02, MOT_HOVER_LEARN 0, MOT_THST_HOVER 0.39, MOT_BAT_VOLT_MAX 0
  let ap := { ap with _pid_rate_yaw._kp := (0.3 : Binary32), _pid_rate_yaw._ki := (0.02 : Binary32) }
  let mp := { mp with _throttle_hover_learn := (0 : Int8), _throttle_hover := (0.39 : Binary32),
                      thr_lin.batt_voltage_max := (0.0 : Binary32) }
  -- copter-cf2x.txt: MOT_THST_EXPO 0, MOT_SPIN_MIN 0, MOT_SPIN_MAX 1, MOT_BAT_VOLT_MAX 0,
  -- MOT_HOVER_LEARN 0, MOT_THST_HOVER 0.4444 (copter-course-speed.txt: WP_SPD 1, WP_ACC 1.5)
  let mp := { mp with thr_lin.curve_expo := (0.0 : Binary32), thr_lin.spin_min := (0.0 : Binary32),
                      thr_lin.spin_max := (1.0 : Binary32), thr_lin.batt_voltage_max := (0.0 : Binary32),
                      _throttle_hover_learn := (0 : Int8), _throttle_hover := (0.4444 : Binary32) }
  -- boot: init(QUAD, X), armed, interlocked, THROTTLE_UNLIMITED
  let (ms, _) := Copter_lib.AP_MotorsMatrix.init_motor_frame_class_motor_frame_type c.motors #[] .MOTOR_FRAME_QUAD .MOTOR_FRAME_TYPE_X
  let (ms, _) := Copter_lib.AP_MotorsMatrix.armed_bool ms #[] true
  let ms := Copter_lib.AP_MotorsMatrix.set_interlock ms true
  let ms := Copter_lib.AP_MotorsMatrix.set_desired_spool_state ms .THROTTLE_UNLIMITED
  let ms := { ms with _spool_state := .THROTTLE_UNLIMITED }
  let mut w : World := { c := { c with motors'p := mp, motors := ms, attitude_control'p := ap } }
  -- takeover: the view of the first sample, relax, hover throttle, the throttle filter preset
  w := setInputs { w with gyro := e0.gyro, view := e0.view, pos := e0.pos, vel := e0.vel, acc := e0.acc }
  w := { w with c := { w.c with attitude_control := Copter_lib.AC_AttitudeControl_Multi.relax_attitude_controllers_void w.c.attitude_control w.c.attitude_control'inp } }
  let hover := Copter_lib.AP_MotorsMatrix.get_throttle_hover w.c.motors'p
  w := setThrottleOut w hover true (2.0 : Binary32)
  let ms := w.c.motors
  w := { w with c := { w.c with motors := { ms with _throttle_filter := Copter_lib.LowPassFilterFloat.reset_float ms._throttle_filter ms._throttle_in } } }
  return w

/-- One tick (the reference harness's loop body); returns the world and the tick's 22 output values.
`hold`: the tick is the one at which the mission completes and AutoYaw switches to HOLD. -/
def tick (w : World) (e : Env) (hold : Bool) : World × String := Id.run do
  let mut w := w
  -- scheduler_loop
  let first := w.ticks32 == 0
  w := { w with ticks32 := w.ticks32 + 1, micros := w.micros + e.dt_us,
                last_loop_time_s := if first then (1.0 : Binary32) / (400.0 : Binary32) else UInt64.toBinary32 e.dt_us * (1.0e-6 : Binary32) }
  -- AP_InertialSensor::update: the tick's gyro
  w := setInputs { w with gyro := e.gyro }
  -- run_rate_controller_main
  let t := w.last_loop_time_s
  let mut c := w.c
  c := { c with pos_control := Copter_lib.AC_PosControl.set_dt_s c.pos_control t,
                attitude_control := Copter_lib.AC_AttitudeControl_Multi.set_dt_s c.attitude_control t,
                motors := Copter_lib.AP_MotorsMatrix.set_dt_s c.motors t }
  let (s, c') := Copter_lib.AC_AttitudeControl_Multi.rate_controller_run c.attitude_control'p c.attitude_control c c.attitude_control'inp
  c := { c' with attitude_control := s }
  c := { c with attitude_control := Copter_lib.AC_AttitudeControl_Multi.rate_controller_target_reset c.attitude_control }
  -- motors_output_main
  let (mp, ms, _) := Copter_lib.AP_MotorsMatrix.output c.motors'p c.motors #[] c.motors'inp
  c := { c with motors'p := mp, motors := ms }
  let act := (List.range 4).map (fun i => ms._actuator[i]!)
  -- read_AHRS, read_inertia
  w := setInputs { w with c, view := e.view, pos := e.pos, vel := e.vel, acc := e.acc }
  c := w.c
  c := { c with pos_control := Copter_lib.AC_PosControl.update_estimates c.pos_control c.pos_control'inp false }
  -- the first tick: ModeAuto::init -> wp_and_spline_init_m's calls into AC_PosControl, rate time constants
  if !w.in_auto then
    let wp_accel : Binary32 := 1.5        -- WP_ACC (copter-course-speed.txt), positive
    let wp_speed : Binary32 := 1.0        -- MAX(WP_SPD, 0.01) = MAX(1, 0.01)
    let pp := c.pos_control'p
    let inp := c.pos_control'inp
    c := { c with pos_control := Copter_lib.AC_PosControl.D_init_controller_stopping_point pp c.pos_control c inp }
    c := { c with pos_control := Copter_lib.AC_PosControl.NE_init_controller_stopping_point pp c.pos_control c inp }
    c := { c with pos_control := Copter_lib.AC_PosControl.NE_set_max_speed_accel_m pp c.pos_control c wp_speed wp_accel }
    c := { c with pos_control := Copter_lib.AC_PosControl.NE_set_correction_speed_accel_m pp c.pos_control wp_speed wp_accel }
    -- fabsf(WP_SPD_DN) = 1.5, WP_SPD_UP = 2.5, WP_ACC_Z = 1 (AC_WPNav defaults)
    c := { c with pos_control := Copter_lib.AC_PosControl.D_set_max_speed_accel_m pp c.pos_control 1.5 2.5 1.0 }
    c := { c with pos_control := Copter_lib.AC_PosControl.D_set_correction_speed_accel_m pp c.pos_control 1.5 2.5 1.0 }
    c := { c with attitude_control := Copter_lib.AC_AttitudeControl_Multi.set_roll_pitch_rate_tc c.attitude_control 0.0 }
    c := { c with attitude_control := Copter_lib.AC_AttitudeControl_Multi.set_yaw_rate_tc c.attitude_control 0.0 }
    w := { w with in_auto := true }
  -- ModeAuto::wp_run with the navigator's targets
  c := { c with pos_control := Copter_lib.AC_PosControl.set_pos_terrain_target_D_m c.pos_control 0.0 }
  c := { c with pos_control := Copter_lib.AC_PosControl.set_pos_vel_accel_NED_m c.pos_control { x := e.npos[0]!, y := e.npos[1]!, z := e.npos[2]! }
                       { x := e.nvel[0]!, y := e.nvel[1]!, z := e.nvel[2]! } { x := e.nacc[0]!, y := e.nacc[1]!, z := e.nacc[2]! } }
  c := { c with pos_control := Copter_lib.AC_PosControl.NE_update_controller c.pos_control'p c.pos_control c c.pos_control'inp }
  let (pp, ps, c') := Copter_lib.AC_PosControl.D_update_controller c.pos_control'p c.pos_control c c.pos_control'inp
  c := { c' with pos_control'p := pp, pos_control := ps }
  w := { w with c }
  -- ModeAuto::loiter_start -> auto_yaw.set_mode(HOLD) at the tick the mission completes
  if hold && !w.hold then
    w := { w with hold := true }
  -- AutoYaw: LOOK_AT_NEXT_WP, the position controller's yaw and rate, Angle_And_Rate; HOLD, the
  -- attitude target's yaw, rate 0, Rate_Only (autoyaw.cpp:378-417)
  let heading : Copter_lib.AC_AttitudeControl.HeadingCommand :=
    if w.hold then
      { yaw_angle_rad := (Copter_lib.AC_AttitudeControl_Multi.get_att_target_euler_rad c.attitude_control).z, yaw_rate_rads := 0.0, heading_mode := .Rate_Only }
    else
      { yaw_angle_rad := Copter_lib.AC_PosControl.get_yaw_rad c.pos_control, yaw_rate_rads := Copter_lib.AC_PosControl.get_yaw_rate_rads c.pos_control, heading_mode := .Angle_And_Rate }
  let tv := Copter_lib.AC_PosControl.get_thrust_vector c.pos_control
  c := { c with attitude_control := Copter_lib.AC_AttitudeControl_Multi.input_thrust_vector_heading c.attitude_control'p c.attitude_control c.attitude_control'inp tv heading }
  w := { w with c }
  -- output: the 22 values of the oracle's line, after `|`
  let pd := Copter_lib.AC_PosControl.get_pos_desired_NED_m c.pos_control
  let vd := Copter_lib.AC_PosControl.get_vel_desired_NED_ms c.pos_control
  let ad := c.pos_control._accel_desired_ned_mss
  let tv := Copter_lib.AC_PosControl.get_thrust_vector c.pos_control
  let eu := Copter_lib.AC_AttitudeControl_Multi.get_att_target_euler_rad c.attitude_control
  let rb := Copter_lib.AC_AttitudeControl_Multi.rate_bf_targets c.attitude_control
  let out := act.map h32 ++ [h64 pd.x, h64 pd.y, h64 pd.z] ++
    ([vd.x, vd.y, vd.z, ad.x, ad.y, ad.z, tv.x, tv.y, tv.z, eu.x, eu.y, eu.z, rb.x, rb.y, rb.z].map h32)
  return (w, " ".intercalate out)

partial def loop (h : IO.FS.Stream) (out : IO.FS.Stream) (holdFrom : Nat) (n : Nat) (w : Option World) : IO Unit := do
  let line ← h.getLine
  if line.trimAscii.isEmpty then return
  let e := Env.parse line
  let w0 := w.getD (start e)
  let (w1, s) := tick w0 e (n + 1 == holdFrom)
  out.putStrLn s
  loop h out holdFrom (n + 1) (some w1)

end Compose

/-- `compose [HOLD_FROM]`: the tick (1-based) at which AutoYaw switches to HOLD (oracle --hold-from;
6618 for the recorded flight); 0 for never. -/
def main (args : List String) : IO Unit := do
  let holdFrom := (args.head?.bind String.toNat?).getD 0
  Compose.loop (← IO.getStdin) (← IO.getStdout) holdFrom 0 none
