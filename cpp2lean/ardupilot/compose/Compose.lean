import AC_Attitude_lib
import AC_PosControl_lib
import AP_Motors_lib

/-!
# Per-tick composition of the translated classes (ardupilot/compose/compose.sh)

The three translations, `AP_Motors_lib` (AP_MotorsMatrix), `AC_Attitude_lib`
(AC_AttitudeControl_Multi) and `AC_PosControl_lib` (AC_PosControl), wired for one 400 Hz tick the
way the reference harness that recorded `ardupilot/data/oracle-nosincos.txt` wires the compiled
classes: scheduler loop time, rate controller, motors output, AHRS view, estimates, the
first tick's entry into Auto (the calls of `AC_WPNav::wp_and_spline_init_m` into AC_PosControl),
the navigator's targets from the recorded trace, the position controllers, AutoYaw
LOOK_AT_NEXT_WP, the attitude controller. Everything here is harness; the controllers are the
translations, unchanged.

The objects exchange values only through the translations' boundaries:
- what a class reads from another object is its `Inputs` record, filled from the other object's
  translated state by the other translation's own getters (`AP_MotorsMatrix.get_throttle_hover`,
  `AC_AttitudeControl_Multi.get_att_target_euler_rad`, ...) or from the environment line;
- the attitude controller's writes into the motors (`Outputs`, the last value of each setter's
  argument) start from the motors' stored values and are written back through the AP_Motors
  translation's setters after each call (a setter not called rewrites the value it stored, which
  leaves the motors unchanged);
- the position controller's call `set_throttle_out` (an `Output` event, `--output-log`) is made on
  the attitude controller, in order, after the call that produced it.

Input: the lines of `compose_env` (the per-tick environment, hex). Output: per tick the 22 numbers
of the oracle's output after `|` (actuators, position/velocity/acceleration targets, thrust
vector, attitude target Euler angles, body-rate targets), as hex bit patterns.
-/

namespace Compose

def hexNat (s : String) : Nat :=
  s.foldl (fun n c => n * 16 + (if c.isDigit then c.toNat - '0'.toNat else c.toLower.toNat - 'a'.toNat + 10)) 0
def f32 (s : String) : Float32 := Float32.ofBits (hexNat s).toUInt32
def f64 (s : String) : Float := Float.ofBits (hexNat s).toUInt64
def hex (width : Nat) (n : Nat) : String :=
  let d := String.ofList (Nat.toDigits 16 n)
  String.ofList (List.replicate (width - d.length) '0') ++ d
def h32 (x : Float32) : String := hex 8 x.toBits.toNat
def h64 (x : Float) : String := hex 16 x.toBits.toNat

/-- One environment line (compose_env.cpp). -/
structure Env where
  dt_us : UInt64
  gyro : Array Float32
  view : Array Float32      -- q1 q2 q3 q4 roll pitch yaw cos_roll cos_pitch cos_yaw sin_roll sin_pitch sin_yaw
  pos : Array Float
  vel : Array Float32
  acc : Array Float32
  npos : Array Float
  nvel : Array Float32
  nacc : Array Float32

def Env.parse (line : String) : Env :=
  let t := (((line.trimAscii.toString).splitOn " ").filter (· ≠ "")).toArray
  let fs (a b : Nat) := ((t.extract a b).map f32)
  let ds (a b : Nat) := ((t.extract a b).map f64)
  { dt_us := (t[0]!.toNat?.getD 0).toUInt64, gyro := fs 1 4, view := fs 4 17, pos := ds 17 20,
    vel := fs 20 23, acc := fs 23 26, npos := ds 26 29, nvel := fs 29 32, nacc := fs 32 35 }

/-- The harness's world: the three objects, the scheduler, the clock, the AHRS view and sample. -/
structure World where
  mp : AP_Motors_lib.AP_MotorsMatrix.Params
  ms : AP_Motors_lib.AP_MotorsMatrix.State
  ap : AC_Attitude_lib.AC_AttitudeControl_Multi.Params
  as : AC_Attitude_lib.AC_AttitudeControl_Multi.State
  pp : AC_PosControl_lib.AC_PosControl.Params
  ps : AC_PosControl_lib.AC_PosControl.State
  ticks32 : UInt32 := 0
  micros : UInt64 := 0
  last_loop_time_s : Float32 := 0
  gyro : Array Float32 := #[0, 0, 0]
  view : Array Float32 := #[1, 0, 0, 0, 0, 0, 0, 1, 1, 1, 0, 0, 0]
  pos : Array Float := #[0, 0, 0]
  vel : Array Float32 := #[0, 0, 0]
  acc : Array Float32 := #[0, 0, 0]
  in_auto : Bool := false
  /-- AutoYaw's mode: LOOK_AT_NEXT_WP until the navigator's mission completes (ModeAuto::loiter_start,
  tick `--hold-from` of the oracle), HOLD after. -/
  hold : Bool := false

/-- `AP_HAL::millis()` and `AP_HAL::micros()` of the harness's HAL (ardupilot/stubs/oracle_env.cpp). -/
def World.millis (w : World) : UInt32 := (w.micros / 1000).toUInt32
def World.micros32 (w : World) : UInt32 := w.micros.toUInt32

/-- What AC_AttitudeControl_Multi reads from the AHRS view, the motors, the scheduler and the HAL. -/
def attInputs (w : World) : AC_Attitude_lib.AC_AttitudeControl_Multi.Inputs :=
  let v := w.view
  let ms := w.ms
  let clk : AC_Attitude_lib.AC_PID.Inputs := { _slew_limiter := { millis := w.millis } }
  { get_quat_body_to_ned_q := { q1 := v[0]!, q2 := v[1]!, q3 := v[2]!, q4 := v[3]! }, yaw := v[6]!,
    get_filtered_loop_time := w.last_loop_time_s,
    get_throttle_hover := AP_Motors_lib.AP_MotorsMatrix.get_throttle_hover w.mp, get_throttle_thrust_max := AP_Motors_lib.AP_MotorsMatrix.get_throttle_thrust_max ms,
    cos_pitch := v[8]!, cos_roll := v[7]!, get_throttle_slew_rate := AP_Motors_lib.AP_MotorsMatrix.get_throttle_slew_rate ms,
    get_throttle := AP_Motors_lib.AP_MotorsMatrix.get_throttle ms, get_throttle_out := AP_Motors_lib.AP_MotorsMatrix.get_throttle_out ms, micros64 := w.micros,
    limit_roll := ms.limit.roll, limit_pitch := ms.limit.pitch, limit_yaw := ms.limit.yaw,
    get_gyro_latest := { x := w.gyro[0]!, y := w.gyro[1]!, z := w.gyro[2]! },
    _pid_rate_roll := clk, _pid_rate_pitch := clk, _pid_rate_yaw := clk }

/-- The motors' stored values of what the attitude controller writes (the `Outputs` before a call). -/
def attOutputs (ms : AP_Motors_lib.AP_MotorsMatrix.State) : AC_Attitude_lib.AC_AttitudeControl_Multi.Outputs :=
  { set_throttle_filter_cutoff := ms._throttle_filter.cutoff_freq, set_throttle := ms._throttle_in,
    set_throttle_avg_max := ms._throttle_avg_max, set_roll := ms._roll_in, set_roll_ff := ms._roll_in_ff,
    set_pitch := ms._pitch_in, set_pitch_ff := ms._pitch_in_ff, set_yaw := ms._yaw_in, set_yaw_ff := ms._yaw_in_ff }

/-- The attitude controller's writes, through the AP_Motors translation's setters. -/
def applyAtt (ms : AP_Motors_lib.AP_MotorsMatrix.State) (o : AC_Attitude_lib.AC_AttitudeControl_Multi.Outputs) : AP_Motors_lib.AP_MotorsMatrix.State :=
  let ms := AP_Motors_lib.AP_MotorsMatrix.set_throttle_filter_cutoff ms o.set_throttle_filter_cutoff
  let ms := AP_Motors_lib.AP_MotorsMatrix.set_throttle ms o.set_throttle
  let ms := AP_Motors_lib.AP_MotorsMatrix.set_throttle_avg_max ms o.set_throttle_avg_max
  let ms := AP_Motors_lib.AP_MotorsMatrix.set_roll ms o.set_roll
  let ms := AP_Motors_lib.AP_MotorsMatrix.set_roll_ff ms o.set_roll_ff
  let ms := AP_Motors_lib.AP_MotorsMatrix.set_pitch ms o.set_pitch
  let ms := AP_Motors_lib.AP_MotorsMatrix.set_pitch_ff ms o.set_pitch_ff
  let ms := AP_Motors_lib.AP_MotorsMatrix.set_yaw ms o.set_yaw
  AP_Motors_lib.AP_MotorsMatrix.set_yaw_ff ms o.set_yaw_ff

/-- An attitude-controller call that writes the motors: run it on the motors' stored values and
write its outputs back. -/
def withMotors (w : World) (f : AC_Attitude_lib.AC_AttitudeControl_Multi.Outputs → AC_Attitude_lib.AC_AttitudeControl_Multi.State × AC_Attitude_lib.AC_AttitudeControl_Multi.Outputs) : World :=
  let (as, o) := f (attOutputs w.ms)
  { w with as, ms := applyAtt w.ms o }

/-- What AC_PosControl reads from the AHRS (the view and AP::ahrs(), the oracle's stub), the
motors, the attitude controller, the scheduler, SITL and the HAL. -/
def posInputs (w : World) : AC_PosControl_lib.AC_PosControl.Inputs :=
  let v := w.view
  let ap := w.ap
  let as := w.as
  let e := AC_Attitude_lib.AC_AttitudeControl_Multi.get_att_target_euler_rad as
  { get_relative_position_NED_origin_vec := { x := w.pos[0]!, y := w.pos[1]!, z := w.pos[2]! },
    get_relative_position_NED_origin := true,
    get_relative_position_D_origin_float_posD := w.pos[2]!.toFloat32, get_relative_position_D_origin_float := true,
    get_velocity_NED_vec := { x := w.vel[0]!, y := w.vel[1]!, z := w.vel[2]! }, get_velocity_NED := true,
    get_vert_pos_rate_D_velocity := w.vel[2]!, get_vert_pos_rate_D := true,
    get_ang_vel_roll_max_rads := AC_Attitude_lib.AC_AttitudeControl_Multi.get_ang_vel_roll_max_rads ap, get_ang_vel_pitch_max_rads := AC_Attitude_lib.AC_AttitudeControl_Multi.get_ang_vel_pitch_max_rads ap,
    get_accel_roll_max_radss := AC_Attitude_lib.AC_AttitudeControl_Multi.get_accel_roll_max_radss ap, get_accel_pitch_max_radss := AC_Attitude_lib.AC_AttitudeControl_Multi.get_accel_pitch_max_radss ap,
    get_bf_feedforward := AC_Attitude_lib.AC_AttitudeControl_Multi.get_bf_feedforward ap, millis := w.millis,
    get_att_target_euler_rad := { x := e.x, y := e.y, z := e.z }, ticks32 := w.ticks32, yaw := v[6]!,
    get_althold_lean_angle_max_rad := AC_Attitude_lib.AC_AttitudeControl_Multi.get_althold_lean_angle_max_rad as, lean_angle_max_rad := AC_Attitude_lib.AC_AttitudeControl_Multi.lean_angle_max_rad ap,
    get_position_NE_reset_count := 0, has_good_timing := true, get_control_gain_scaler_XY := 1.0,
    cos_yaw := v[9]!, sin_yaw := v[12]!, get_accel_ef := { x := w.acc[0]!, y := w.acc[1]!, z := w.acc[2]! },
    get_throttle_in := AC_Attitude_lib.AC_AttitudeControl_Multi.get_throttle_in as, get_throttle_hover := AP_Motors_lib.AP_MotorsMatrix.get_throttle_hover w.mp,
    get_position_D_reset_count := 0, get_control_gain_scaler_Z := 1.0,
    limit_throttle_lower := w.ms.limit.throttle_lower, limit_throttle_upper := w.ms.limit.throttle_upper,
    _pid_accel_d_m := { _slew_limiter := { millis := w.millis } } }

/-- The position controller's calls into the attitude controller, in order. -/
def applyPos (w : World) (evs : AC_PosControl_lib.Outputs) : World := Id.run do
  let mut w := w
  for ev in evs do
    match ev with
    | .set_throttle_out thr boost cutoff =>
      let inp := attInputs w
      let ap := w.ap
      w := withMotors w (fun o => AC_Attitude_lib.AC_AttitudeControl_Multi.set_throttle_out ap w.as o inp thr boost cutoff)
  return w

/-- The motors' inputs on the oracle's HAL: the clock, no digital outputs or boost channel, the
stub's air density ratio 1 (`run.air_density_ratio`). -/
def motorsInputs (w : World) : AP_Motors_lib.AP_MotorsMatrix.Inputs :=
  { micros := w.micros32, thr_lin := { get_air_density_ratio := 1.0 } }

/-- Construction and parameters (the reference harness: the code defaults, SITL's run deviations,
then sim/params/copter-cf2x.txt and copter-course-speed.txt), boot, and the takeover on the first
sample. -/
def start (e0 : Env) : World := Id.run do
  let (mp, ms) := AP_Motors_lib.AP_MotorsMatrix.construct 400
  let (ap, as) := AC_Attitude_lib.AC_AttitudeControl_Multi.init
  let (pp, ps) := AC_PosControl_lib.AC_PosControl.init
  -- ATC_RAT_YAW_P 0.3, ATC_RAT_YAW_I 0.02, MOT_HOVER_LEARN 0, MOT_THST_HOVER 0.39, MOT_BAT_VOLT_MAX 0
  let ap := { ap with _pid_rate_yaw._kp := (0.3 : Float32), _pid_rate_yaw._ki := (0.02 : Float32) }
  let mp := { mp with _throttle_hover_learn := (0 : Int8), _throttle_hover := (0.39 : Float32),
                      thr_lin.batt_voltage_max := (0.0 : Float32) }
  -- copter-cf2x.txt: MOT_THST_EXPO 0, MOT_SPIN_MIN 0, MOT_SPIN_MAX 1, MOT_BAT_VOLT_MAX 0,
  -- MOT_HOVER_LEARN 0, MOT_THST_HOVER 0.4444 (copter-course-speed.txt: WP_SPD 1, WP_ACC 1.5)
  let mp := { mp with thr_lin.curve_expo := (0.0 : Float32), thr_lin.spin_min := (0.0 : Float32),
                      thr_lin.spin_max := (1.0 : Float32), thr_lin.batt_voltage_max := (0.0 : Float32),
                      _throttle_hover_learn := (0 : Int8), _throttle_hover := (0.4444 : Float32) }
  -- boot: init(QUAD, X), armed, interlocked, THROTTLE_UNLIMITED
  let (ms, _) := AP_Motors_lib.AP_MotorsMatrix.init_motor_frame_class_motor_frame_type ms #[] .MOTOR_FRAME_QUAD .MOTOR_FRAME_TYPE_X
  let (ms, _) := AP_Motors_lib.AP_MotorsMatrix.armed_bool ms #[] true
  let ms := AP_Motors_lib.AP_MotorsMatrix.set_interlock ms true
  let ms := AP_Motors_lib.AP_MotorsMatrix.set_desired_spool_state ms .THROTTLE_UNLIMITED
  let ms := { ms with _spool_state := .THROTTLE_UNLIMITED }
  let mut w : World := { mp, ms, ap, as, pp, ps }
  -- takeover: the view of the first sample, relax, hover throttle, the throttle filter preset
  w := { w with gyro := e0.gyro, view := e0.view, pos := e0.pos, vel := e0.vel, acc := e0.acc }
  w := { w with as := AC_Attitude_lib.AC_AttitudeControl_Multi.relax_attitude_controllers_void w.as (attInputs w) }
  let hover := AP_Motors_lib.AP_MotorsMatrix.get_throttle_hover w.mp
  let inp := attInputs w
  w := withMotors w (fun o => AC_Attitude_lib.AC_AttitudeControl_Multi.set_throttle_out w.ap w.as o inp hover true (2.0 : Float32))
  w := { w with ms := { w.ms with _throttle_filter := AP_Motors_lib.LowPassFilterFloat.reset_float w.ms._throttle_filter w.ms._throttle_in } }
  return w

/-- One tick (the reference harness's loop body); returns the world and the tick's 22 output values.
`hold`: the tick is the one at which the mission completes and AutoYaw switches to HOLD. -/
def tick (w : World) (e : Env) (hold : Bool) : World × String := Id.run do
  let mut w := w
  -- scheduler_loop
  let first := w.ticks32 == 0
  w := { w with ticks32 := w.ticks32 + 1, micros := w.micros + e.dt_us,
                last_loop_time_s := if first then (1.0 : Float32) / (400.0 : Float32) else e.dt_us.toFloat32 * (1.0e-6 : Float32) }
  -- AP_InertialSensor::update: the tick's gyro
  w := { w with gyro := e.gyro }
  -- run_rate_controller_main
  let t := w.last_loop_time_s
  w := { w with ps := AC_PosControl_lib.AC_PosControl.set_dt_s w.ps t, as := AC_Attitude_lib.AC_AttitudeControl_Multi.set_dt_s w.as t, ms := AP_Motors_lib.AP_MotorsMatrix.set_dt_s w.ms t }
  let inp := attInputs w
  let ap := w.ap
  w := withMotors w (fun o => AC_Attitude_lib.AC_AttitudeControl_Multi.rate_controller_run ap w.as o inp)
  w := { w with as := AC_Attitude_lib.AC_AttitudeControl_Multi.rate_controller_target_reset w.as }
  -- motors_output_main
  let (mp, ms, _) := AP_Motors_lib.AP_MotorsMatrix.output w.mp w.ms #[] (motorsInputs w)
  w := { w with mp, ms }
  let act := (List.range 4).map (fun i => w.ms._actuator[i]!)
  -- read_AHRS, read_inertia
  w := { w with view := e.view, pos := e.pos, vel := e.vel, acc := e.acc }
  w := { w with ps := AC_PosControl_lib.AC_PosControl.update_estimates w.ps (posInputs w) false }
  -- the first tick: ModeAuto::init -> wp_and_spline_init_m's calls into AC_PosControl, rate time constants
  if !w.in_auto then
    let wp_accel : Float32 := 1.5        -- WP_ACC (copter-course-speed.txt), positive
    let wp_speed : Float32 := 1.0        -- MAX(WP_SPD, 0.01) = MAX(1, 0.01)
    w := { w with ps := AC_PosControl_lib.AC_PosControl.D_init_controller_stopping_point w.pp w.ps (posInputs w) }
    w := { w with ps := AC_PosControl_lib.AC_PosControl.NE_init_controller_stopping_point w.pp w.ps (posInputs w) }
    w := { w with ps := AC_PosControl_lib.AC_PosControl.NE_set_max_speed_accel_m w.pp w.ps (posInputs w) wp_speed wp_accel }
    w := { w with ps := AC_PosControl_lib.AC_PosControl.NE_set_correction_speed_accel_m w.pp w.ps wp_speed wp_accel }
    -- fabsf(WP_SPD_DN) = 1.5, WP_SPD_UP = 2.5, WP_ACC_Z = 1 (AC_WPNav defaults)
    w := { w with ps := AC_PosControl_lib.AC_PosControl.D_set_max_speed_accel_m w.pp w.ps 1.5 2.5 1.0 }
    w := { w with ps := AC_PosControl_lib.AC_PosControl.D_set_correction_speed_accel_m w.pp w.ps 1.5 2.5 1.0 }
    w := { w with as := AC_Attitude_lib.AC_AttitudeControl_Multi.set_roll_pitch_rate_tc w.as 0.0, in_auto := true }
    w := { w with as := AC_Attitude_lib.AC_AttitudeControl_Multi.set_yaw_rate_tc w.as 0.0 }
  -- ModeAuto::wp_run with the navigator's targets
  w := { w with ps := AC_PosControl_lib.AC_PosControl.set_pos_terrain_target_D_m w.ps 0.0 }
  w := { w with ps := AC_PosControl_lib.AC_PosControl.set_pos_vel_accel_NED_m w.ps { x := e.npos[0]!, y := e.npos[1]!, z := e.npos[2]! }
                       { x := e.nvel[0]!, y := e.nvel[1]!, z := e.nvel[2]! } { x := e.nacc[0]!, y := e.nacc[1]!, z := e.nacc[2]! } }
  w := { w with ps := AC_PosControl_lib.AC_PosControl.NE_update_controller w.pp w.ps (posInputs w) }
  let (pp, ps, evs) := AC_PosControl_lib.AC_PosControl.D_update_controller w.pp w.ps #[] (posInputs w)
  w := { w with pp, ps }
  w := applyPos w evs
  -- ModeAuto::loiter_start -> auto_yaw.set_mode(HOLD) at the tick the mission completes
  if hold && !w.hold then
    w := { w with hold := true }
  -- AutoYaw: LOOK_AT_NEXT_WP, the position controller's yaw and rate, Angle_And_Rate; HOLD, the
  -- attitude target's yaw, rate 0, Rate_Only (autoyaw.cpp:378-417)
  let heading : AC_Attitude_lib.AC_AttitudeControl.HeadingCommand :=
    if w.hold then
      { yaw_angle_rad := (AC_Attitude_lib.AC_AttitudeControl_Multi.get_att_target_euler_rad w.as).z, yaw_rate_rads := 0.0, heading_mode := .Rate_Only }
    else
      { yaw_angle_rad := AC_PosControl_lib.AC_PosControl.get_yaw_rad w.ps, yaw_rate_rads := AC_PosControl_lib.AC_PosControl.get_yaw_rate_rads w.ps, heading_mode := .Angle_And_Rate }
  let tv := AC_PosControl_lib.AC_PosControl.get_thrust_vector w.ps
  w := { w with as := AC_Attitude_lib.AC_AttitudeControl_Multi.input_thrust_vector_heading w.ap w.as (attInputs w) { x := tv.x, y := tv.y, z := tv.z } heading }
  -- output: the 22 values of the oracle's line, after `|`
  let pd := AC_PosControl_lib.AC_PosControl.get_pos_desired_NED_m w.ps
  let vd := AC_PosControl_lib.AC_PosControl.get_vel_desired_NED_ms w.ps
  let ad := w.ps._accel_desired_ned_mss
  let tv := AC_PosControl_lib.AC_PosControl.get_thrust_vector w.ps
  let eu := AC_Attitude_lib.AC_AttitudeControl_Multi.get_att_target_euler_rad w.as
  let rb := AC_Attitude_lib.AC_AttitudeControl_Multi.rate_bf_targets w.as
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
