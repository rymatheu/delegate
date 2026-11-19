import AC_Attitude_lib
import AC_PosControl_lib
import AP_Motors_lib
import AC_WPNav_lib
import AHRS_View_lib
import VehicleParams

/-!
# The Lean vehicle (executable `copter_lean`, `VehicleMain.lean`)

The translations of AP_MotorsMatrix (`AP_Motors_lib`), AC_AttitudeControl_Multi (`AC_Attitude_lib`),
AC_PosControl (`AC_PosControl_lib`), AC_WPNav (`AC_WPNav_lib`) and the AHRS view derivation
(`AHRS_View_lib`: AP_AHRS_View::update with AP_AHRS::calc_trig), wired for one 400 Hz tick of Auto
mode per input line of the lock-step protocol (sim/PROTOCOL.md).

Everything here is harness; the classes are the translations, unchanged. It is the harness of
`ardupilot/vehicle/copter_ref.cpp`, which drives the compiled C++ classes, function by function in
the same order and with the same names: the protocol, the parameters by ArduPilot name
(`VehicleParams`, generated from the translations' var_info tables), construction, boot and
takeover, the tick, and the mission harness written from ArduCopter's C++ (each function marked with
the file and lines it mirrors).

The objects exchange values only through the translations' boundaries, as `Compose.lean` does:
- what a class reads from another object is its `Inputs`, filled from the other objects' translated
  state by their own getters (or from the input line: the AHRS estimate);
- the attitude controller's writes into the motors (`Outputs`, the last value of each setter) start
  from the motors' stored values and are written back through the motors' setters;
- the position controller's `set_throttle_out` events are made on the attitude controller, in order;
- the navigator's calls into the position controller are `Output` events, made on it in order after
  the call; its reads of the position controller are live (`--boundary-live`): a read is evaluated on
  the position controller as the events logged so far in the call have left it (`replayPos`).
The AHRS estimate of the line is the boundary of the view: the view's rotation matrix input is the
estimate quaternion's `rotation_matrix` (as the EKF's dcm), its gyro the line's gyro. As in the
reference vehicle's AHRS stub, the attitude controller reads the estimate's quaternion itself
(`get_quat_body_to_ned`; the real view converts its matrix back with `from_rotation_matrix`).
-/

namespace Vehicle

-- ---------------------------------------------------------------------------------------------
-- Text: hex, exact decimals, six decimals, decimal input

def hex (width : Nat) (n : Nat) : String :=
  let d := String.ofList (Nat.toDigits 16 n)
  String.ofList (List.replicate (width - d.length) '0') ++ d
def h32 (x : Float32) : String := hex 8 x.toBits.toNat
def h64 (x : Float) : String := hex 16 x.toBits.toNat

/-- The exact value of a finite double: (negative, m, e) with |x| = m * 2^e. -/
def decompose (x : Float) : Bool × Nat × Int :=
  let b := x.toBits.toNat
  let neg := b >>> 63 == 1
  let ex := (b >>> 52) % 2048
  let fr := b % (2 ^ 52)
  if ex == 0 then (neg, fr, -1074) else (neg, fr + 2 ^ 52, (ex : Int) - 1075)

/-- `copter_ref.cpp` `exact_decimal`: the exact decimal expansion, no exponent, trailing zeros
dropped, the sign of zero dropped (`%.1100f` of Apple's printf, trimmed). -/
def exactDecimal (x : Float) : String :=
  if x.isNaN then "nan" else if x.isInf then (if x < 0 then "-inf" else "inf") else if x == 0 then "0" else
  let (neg, m, e) := decompose x
  let sgn := if neg then "-" else ""
  if e ≥ 0 then sgn ++ toString (m * 2 ^ e.toNat) else
  let k := (-e).toNat
  let digits := toString (m * 5 ^ k)
  let padded := String.ofList (List.replicate (k + 1 - min (k + 1) digits.length) '0') ++ digits
  let ip := padded.take (padded.length - k)
  let fp := (padded.drop (padded.length - k)).toString
  let fpt := String.ofList ((fp.toList.reverse.dropWhile (· == '0')).reverse)
  sgn ++ ip.toString ++ (if fpt.isEmpty then "" else "." ++ fpt)

/-- `copter_ref.cpp` `six_decimals`: `%.6f`, rounded to nearest, ties to even, of the exact value. -/
def sixDecimals (x : Float) : String :=
  if x.isNaN then "nan" else if x.isInf then (if x < 0 then "-inf" else "inf") else
  let (neg, m, e) := decompose x
  let num := m * 10 ^ 6 * 2 ^ (if e ≥ 0 then e.toNat else 0)
  let den := 2 ^ (if e < 0 then (-e).toNat else 0)
  let q := num / den
  let r := num % den
  let q := if 2 * r > den || (2 * r == den && q % 2 == 1) then q + 1 else q
  let s := toString q
  let s := String.ofList (List.replicate (7 - min 7 s.length) '0') ++ s
  (if neg then "-" else "") ++ (s.take (s.length - 6)).toString ++ "." ++ (s.drop (s.length - 6)).toString

/-- A decimal token as (negative, mantissa, decimal exponent), or none. -/
def parseDecimal (t : String) : Option (Bool × Nat × Int) := Id.run do
  let cs := t.toList
  let (neg, cs) := match cs with
    | '-' :: r => (true, r)
    | '+' :: r => (false, r)
    | r => (false, r)
  let mut m : Nat := 0
  let mut e : Int := 0
  let mut dot := false
  let mut nd := 0
  let mut rest := cs
  while true do
    match rest with
    | c :: r =>
      if c.isDigit then
        m := m * 10 + (c.toNat - '0'.toNat)
        nd := nd + 1
        if dot then e := e - 1
        rest := r
      else if c == '.' && !dot then
        dot := true
        rest := r
      else break
    | [] => break
  if nd == 0 then return none
  match rest with
  | [] => return some (neg, m, e)
  | c :: r =>
    if c == 'e' || c == 'E' then
      let s := String.ofList r
      match s.toInt? with
      | some x => return some (neg, m, e + x)
      | none => return none
    else return none

/-- strtod: correctly rounded (Lean's `OfScientific Float` is). -/
def toF64 (t : String) : Option Float :=
  (parseDecimal t).map fun (neg, m, e) =>
    let v : Float := if e ≥ 0 then OfScientific.ofScientific m false e.toNat else OfScientific.ofScientific m true (-e).toNat
    if neg then -v else v

/-- strtof: correctly rounded, once (Lean's `OfScientific Float32` is). -/
def toF32 (t : String) : Option Float32 :=
  (parseDecimal t).map fun (neg, m, e) =>
    let v : Float32 := if e ≥ 0 then OfScientific.ofScientific m false e.toNat else OfScientific.ofScientific m true (-e).toNat
    if neg then -v else v

/-- `copter_ref.cpp` `to_micros`: seconds to whole microseconds, half up, from the exact decimal. -/
def toMicros (t : String) : Option UInt64 :=
  match parseDecimal t with
  | none => none
  | some (neg, m, e) =>
    if neg && m != 0 then none else
    let e6 := e + 6
    if e6 ≥ 0 then some (m * 10 ^ e6.toNat).toUInt64
    else let q := 10 ^ (-e6).toNat; some ((2 * m + q) / (2 * q)).toUInt64

/-- One input line (sim/PROTOCOL.md): position (double), velocity, specific force, quaternion, gyro, dt. -/
structure Sample where
  pos : AC_PosControl_lib.Vector3p.State
  vel : AC_PosControl_lib.Vector3f.State
  acc : AC_PosControl_lib.Vector3f.State
  quat : AC_Attitude_lib.Quaternion.State
  gyro : AC_Attitude_lib.Vector3f.State
  dt_us : UInt64

/-- `copter_ref.cpp` `parse_sample`. -/
def parseSample (line : String) : Option Sample := do
  let w := ((line.splitOn " ").map (·.trimAscii.toString)).filter (· ≠ "") |>.toArray
  if w.size != 17 then none
  let d (i : Nat) := toF64 w[i]!
  let f (i : Nat) := toF32 w[i]!
  let dt ← toMicros w[16]!
  if dt == 0 then none
  return { pos := { x := ← d 0, y := ← d 1, z := ← d 2 }, vel := { x := ← f 3, y := ← f 4, z := ← f 5 },
           acc := { x := ← f 6, y := ← f 7, z := ← f 8 }, quat := { q1 := ← f 9, q2 := ← f 10, q3 := ← f 11, q4 := ← f 12 },
           gyro := { x := ← f 13, y := ← f 14, z := ← f 15 }, dt_us := dt }

-- ---------------------------------------------------------------------------------------------
-- Harness values that are not parameters of the classes (copter_ref.cpp `HarnessParams`)

structure HarnessParams where
  WP_YAW_BEHAVIOR : Int := 2
  PILOT_Y_RATE_TC : Float32 := 0.0
  ACRO_RP_RATE_TC : Float32 := 0.0
  air_density_ratio : Float32 := 1.0
  start_hover : Int := 1

/-- `copter_ref.cpp` `set_harness_param`. -/
def setHarnessParam (h : HarnessParams) (name : String) (v : Float32) : Option HarnessParams :=
  if name == "WP_YAW_BEHAVIOR" then some { h with WP_YAW_BEHAVIOR := (Float32.toInt32 v).toInt }
  else if name == "PILOT_Y_RATE_TC" then some { h with PILOT_Y_RATE_TC := v }
  else if name == "ACRO_RP_RATE_TC" then some { h with ACRO_RP_RATE_TC := v }
  else if name == "run.air_density_ratio" then some { h with air_density_ratio := v }
  else if name == "run.start_hover" then some { h with start_hover := (Float32.toInt32 v).toInt }
  else none

-- ---------------------------------------------------------------------------------------------
-- The mission harness's state (copter_ref.cpp `Auto`)

inductive SubMode where | STARTING | WP | LOITER
deriving DecidableEq, Inhabited
inductive YawMode where | HOLD | LOOK_AT_NEXT_WP
deriving DecidableEq, Inhabited
inductive MissionState where | STOPPED | RUNNING | COMPLETE
deriving DecidableEq, Inhabited

structure Auto where
  mode : SubMode := .STARTING
  waiting_to_start : Bool := false
  loiter_time : UInt32 := 0
  loiter_time_max : UInt16 := 0
  yaw_mode : YawMode := .HOLD
  yaw_angle_rad : Float32 := 0.0
  yaw_rate_rads : Float32 := 0.0
  state : MissionState := .STOPPED
  nav_index : Int := -1
  nav_cmd_loaded : Bool := false

-- ---------------------------------------------------------------------------------------------
-- The world: the objects, the scheduler and clock, the AHRS sample, the mission

structure World where
  mp : AP_Motors_lib.AP_MotorsMatrix.Params
  ms : AP_Motors_lib.AP_MotorsMatrix.State
  ap : AC_Attitude_lib.AC_AttitudeControl_Multi.Params
  as : AC_Attitude_lib.AC_AttitudeControl_Multi.State
  pp : AC_PosControl_lib.AC_PosControl.Params
  ps : AC_PosControl_lib.AC_PosControl.State
  wpp : AC_WPNav_lib.AC_WPNav.Params
  wps : AC_WPNav_lib.AC_WPNav.State
  vs : AHRS_View_lib.AP_AHRS_View.State
  h : HarnessParams := {}
  mission : Array AC_WPNav_lib.Vector3p.State := #[]
  au : Auto := {}
  in_auto : Bool := false
  ticks32 : UInt32 := 0
  micros : UInt64 := 0
  last_loop_time_s : Float32 := 0
  sample : Sample := { pos := {}, vel := {}, acc := {}, quat := {}, gyro := {}, dt_us := 0 }

/-- `AP_HAL::millis()` of the HAL stub (ardupilot/stubs/oracle_env.cpp): micros / 1000. -/
def World.millis (w : World) : UInt32 := (w.micros / 1000).toUInt32
def World.micros32 (w : World) : UInt32 := w.micros.toUInt32

/-- What the AHRS view reads from the AHRS: the estimate's rotation (its quaternion's rotation
matrix, AP_Math's `QuaternionT<float>::rotation_matrix`) and its gyro. -/
def viewInputs (w : World) : AHRS_View_lib.AP_AHRS_View.Inputs :=
  let q := w.sample.quat
  let g := w.sample.gyro
  { get_rotation_body_to_ned := AHRS_View_lib.Quaternion.rotation_matrix_Matrix3f { q1 := q.q1, q2 := q.q2, q3 := q.q3, q4 := q.q4 } {},
    get_gyro := { x := g.x, y := g.y, z := g.z } }

/-- `AP_AHRS_View::update` (the translation) on the current sample. -/
def viewUpdate (w : World) : World :=
  { w with vs := AHRS_View_lib.AP_AHRS_View.update w.vs (viewInputs w) }

/-- What AC_AttitudeControl_Multi reads from the AHRS view, the motors, the scheduler and the HAL. -/
def attInputs (w : World) : AC_Attitude_lib.AC_AttitudeControl_Multi.Inputs :=
  let v := w.vs
  let ms := w.ms
  let clk : AC_Attitude_lib.AC_PID.Inputs := { _slew_limiter := { millis := w.millis } }
  { get_quat_body_to_ned_q := w.sample.quat, yaw := v.yaw,
    get_filtered_loop_time := w.last_loop_time_s,
    get_throttle_hover := AP_Motors_lib.AP_MotorsMatrix.get_throttle_hover w.mp, get_throttle_thrust_max := AP_Motors_lib.AP_MotorsMatrix.get_throttle_thrust_max ms,
    cos_pitch := v.trig.cos_pitch, cos_roll := v.trig.cos_roll, get_throttle_slew_rate := AP_Motors_lib.AP_MotorsMatrix.get_throttle_slew_rate ms,
    get_throttle := AP_Motors_lib.AP_MotorsMatrix.get_throttle ms, get_throttle_out := AP_Motors_lib.AP_MotorsMatrix.get_throttle_out ms, micros64 := w.micros,
    limit_roll := ms.limit.roll, limit_pitch := ms.limit.pitch, limit_yaw := ms.limit.yaw,
    get_gyro_latest := w.sample.gyro,
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

/-- What AC_PosControl reads from the AHRS (the view and AP::ahrs(), the stub's answers), the
motors, the attitude controller, the scheduler, SITL and the HAL. -/
def posInputs (w : World) : AC_PosControl_lib.AC_PosControl.Inputs :=
  let v := w.vs
  let ap := w.ap
  let as := w.as
  let e := AC_Attitude_lib.AC_AttitudeControl_Multi.get_att_target_euler_rad as
  let smp := w.sample
  { get_relative_position_NED_origin_vec := smp.pos,
    get_relative_position_NED_origin := true,
    get_relative_position_D_origin_float_posD := smp.pos.z.toFloat32, get_relative_position_D_origin_float := true,
    get_velocity_NED_vec := smp.vel, get_velocity_NED := true,
    get_vert_pos_rate_D_velocity := smp.vel.z, get_vert_pos_rate_D := true,
    get_ang_vel_roll_max_rads := AC_Attitude_lib.AC_AttitudeControl_Multi.get_ang_vel_roll_max_rads ap, get_ang_vel_pitch_max_rads := AC_Attitude_lib.AC_AttitudeControl_Multi.get_ang_vel_pitch_max_rads ap,
    get_accel_roll_max_radss := AC_Attitude_lib.AC_AttitudeControl_Multi.get_accel_roll_max_radss ap, get_accel_pitch_max_radss := AC_Attitude_lib.AC_AttitudeControl_Multi.get_accel_pitch_max_radss ap,
    get_bf_feedforward := AC_Attitude_lib.AC_AttitudeControl_Multi.get_bf_feedforward ap, millis := w.millis,
    get_att_target_euler_rad := { x := e.x, y := e.y, z := e.z }, ticks32 := w.ticks32, yaw := v.yaw,
    get_althold_lean_angle_max_rad := AC_Attitude_lib.AC_AttitudeControl_Multi.get_althold_lean_angle_max_rad as, lean_angle_max_rad := AC_Attitude_lib.AC_AttitudeControl_Multi.lean_angle_max_rad ap,
    get_position_NE_reset_count := 0, has_good_timing := true, get_control_gain_scaler_XY := 1.0,
    cos_yaw := v.trig.cos_yaw, sin_yaw := v.trig.sin_yaw, get_accel_ef := smp.acc,
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

/-- The motors' inputs on the HAL stub: the clock, no digital outputs or boost channel, the AHRS
stub's air density ratio. -/
def motorsInputs (w : World) : AP_Motors_lib.AP_MotorsMatrix.Inputs :=
  { micros := w.micros32, thr_lin := { get_air_density_ratio := w.h.air_density_ratio } }

def p3 (v : AC_WPNav_lib.Vector3p.State) : AC_PosControl_lib.Vector3p.State := { x := v.x, y := v.y, z := v.z }
def f3 (v : AC_WPNav_lib.Vector3f.State) : AC_PosControl_lib.Vector3f.State := { x := v.x, y := v.y, z := v.z }
def wp3 (v : AC_PosControl_lib.Vector3p.State) : AC_WPNav_lib.Vector3p.State := { x := v.x, y := v.y, z := v.z }
def wf3 (v : AC_PosControl_lib.Vector3f.State) : AC_WPNav_lib.Vector3f.State := { x := v.x, y := v.y, z := v.z }

/-- The navigator's calls into the position controller (its `Output` events), made in order on the
position controller's translation. -/
def replayPos (w : World) (log : AC_WPNav_lib.Outputs) : World := Id.run do
  let mut w := w
  for ev in log do
    let pp := w.pp
    let inp := posInputs w
    match ev with
    | .init_pos_terrain_D_m d => w := { w with ps := AC_PosControl_lib.AC_PosControl.init_pos_terrain_D_m w.ps d }
    | .D_init_controller_stopping_point => w := { w with ps := AC_PosControl_lib.AC_PosControl.D_init_controller_stopping_point pp w.ps inp }
    | .NE_init_controller_stopping_point => w := { w with ps := AC_PosControl_lib.AC_PosControl.NE_init_controller_stopping_point pp w.ps inp }
    | .NE_set_max_speed_accel_m v a => w := { w with ps := AC_PosControl_lib.AC_PosControl.NE_set_max_speed_accel_m pp w.ps inp v a }
    | .NE_set_correction_speed_accel_m v a => w := { w with ps := AC_PosControl_lib.AC_PosControl.NE_set_correction_speed_accel_m pp w.ps v a }
    | .D_set_max_speed_accel_m dn up a => w := { w with ps := AC_PosControl_lib.AC_PosControl.D_set_max_speed_accel_m pp w.ps dn up a }
    | .D_set_correction_speed_accel_m dn up a => w := { w with ps := AC_PosControl_lib.AC_PosControl.D_set_correction_speed_accel_m pp w.ps dn up a }
    | .set_pos_terrain_target_D_m d => w := { w with ps := AC_PosControl_lib.AC_PosControl.set_pos_terrain_target_D_m w.ps d }
    | .set_pos_vel_accel_NED_m pos vel acc => w := { w with ps := AC_PosControl_lib.AC_PosControl.set_pos_vel_accel_NED_m w.ps (p3 pos) (f3 vel) (f3 acc) }
    | .NE_update_controller => w := { w with ps := AC_PosControl_lib.AC_PosControl.NE_update_controller pp w.ps inp }
  return w

/-- What AC_WPNav reads: the attitude controller's getters and the clock, and the position
controller's getters, live: evaluated after the events the call has logged so far. -/
def wpInputs (w : World) : AC_WPNav_lib.AC_WPNav.Inputs :=
  let ap := w.ap
  let pc (log : AC_WPNav_lib.Outputs) := replayPos w log
  { get_ang_vel_roll_max_rads := AC_Attitude_lib.AC_AttitudeControl_Multi.get_ang_vel_roll_max_rads ap,
    get_ang_vel_pitch_max_rads := AC_Attitude_lib.AC_AttitudeControl_Multi.get_ang_vel_pitch_max_rads ap,
    get_input_tc := AC_Attitude_lib.AC_AttitudeControl_Multi.get_input_tc ap,
    get_accel_roll_max_radss := AC_Attitude_lib.AC_AttitudeControl_Multi.get_accel_roll_max_radss ap,
    get_accel_pitch_max_radss := AC_Attitude_lib.AC_AttitudeControl_Multi.get_accel_pitch_max_radss ap,
    get_stopping_point_NE_m_stopping_point_ne_m := fun log =>
      let w' := pc log
      let v := AC_PosControl_lib.AC_PosControl.get_stopping_point_NE_m w'.pp w'.ps {}
      { x := v.x, y := v.y },
    get_stopping_point_D_m_stopping_point_d_m := fun log =>
      let w' := pc log
      AC_PosControl_lib.AC_PosControl.get_stopping_point_D_m w'.pp w'.ps 0.0,
    millis := w.millis,
    NE_get_max_speed_ms := fun log => AC_PosControl_lib.AC_PosControl.NE_get_max_speed_ms (pc log).ps,
    get_max_speed_up_ms := fun log => AC_PosControl_lib.AC_PosControl.get_max_speed_up_ms (pc log).ps,
    get_max_speed_down_ms := fun log => AC_PosControl_lib.AC_PosControl.get_max_speed_down_ms (pc log).ps,
    D_get_max_accel_mss := fun log => AC_PosControl_lib.AC_PosControl.D_get_max_accel_mss (pc log).ps,
    get_vel_desired_NED_ms := fun log => wf3 (AC_PosControl_lib.AC_PosControl.get_vel_desired_NED_ms (pc log).ps),
    get_vel_offset_D_ms := fun log => AC_PosControl_lib.AC_PosControl.get_vel_offset_D_ms (pc log).ps,
    get_pos_estimate_NED_m := fun log => wp3 (AC_PosControl_lib.AC_PosControl.get_pos_estimate_NED_m (pc log).ps),
    terrain_scaler_D_m := fun log a b => AC_PosControl_lib.AC_PosControl.terrain_scaler_D_m (pc log).ps a b,
    get_pos_offset_NED_m := fun log => wp3 (AC_PosControl_lib.AC_PosControl.get_pos_offset_NED_m (pc log).ps),
    get_pos_error_NED_m := fun log => wf3 (AC_PosControl_lib.AC_PosControl.get_pos_error_NED_m (pc log).ps),
    get_vel_estimate_NED_ms := fun log => wf3 (AC_PosControl_lib.AC_PosControl.get_vel_estimate_NED_ms (pc log).ps),
    NE_get_pos_p_kP := fun log => (pc log).pp._p_pos_ne_m._kp,
    get_shaping_jerk_NE_msss := fun log => AC_PosControl_lib.AC_PosControl.get_shaping_jerk_NE_msss (pc log).pp,
    get_dt_s := fun log => AC_PosControl_lib.AC_PosControl.get_dt_s (pc log).ps,
    NE_get_max_accel_mss := fun log => AC_PosControl_lib.AC_PosControl.NE_get_max_accel_mss (pc log).ps,
    get_roll_rad := fun log => AC_PosControl_lib.AC_PosControl.get_roll_rad (pc log).ps,
    get_pitch_rad := fun log => AC_PosControl_lib.AC_PosControl.get_pitch_rad (pc log).ps,
    get_yaw_rad := fun log => AC_PosControl_lib.AC_PosControl.get_yaw_rad (pc log).ps,
    get_thrust_vector := fun log => wf3 (AC_PosControl_lib.AC_PosControl.get_thrust_vector (pc log).ps),
    crosstrack_error_m := fun log => AC_PosControl_lib.AC_PosControl.crosstrack_error_m (pc log).ps }

/-- After a navigator call: its parameters and state, and its calls into the position controller,
made in order. -/
def afterWP (w : World) (wpp : AC_WPNav_lib.AC_WPNav.Params) (wps : AC_WPNav_lib.AC_WPNav.State) (log : AC_WPNav_lib.Outputs) : World :=
  replayPos { w with wpp, wps } log

-- ---------------------------------------------------------------------------------------------
-- The mission harness (copter_ref.cpp, same functions in the same order)

/-- autoyaw.cpp:36-58 AutoYaw::default_mode(rtl = false) -/
def auto_yaw_default_mode (w : World) : YawMode :=
  if w.h.WP_YAW_BEHAVIOR == 0 then .HOLD else .LOOK_AT_NEXT_WP

/-- autoyaw.cpp:60-113 AutoYaw::set_mode -/
def auto_yaw_set_mode (w : World) (yaw_mode : YawMode) : World := Id.run do
  if w.au.yaw_mode == yaw_mode then
    return w
  let mut w := { w with au.yaw_mode := yaw_mode }
  if yaw_mode == .HOLD then
    w := { w with au.yaw_angle_rad := (AC_Attitude_lib.AC_AttitudeControl_Multi.get_att_target_euler_rad w.as).z }
  return w

/-- autoyaw.cpp:234-323 AutoYaw::yaw_rad -/
def auto_yaw_yaw_rad (w : World) : World × Float32 :=
  let a := if w.au.yaw_mode == .HOLD then (AC_Attitude_lib.AC_AttitudeControl_Multi.get_att_target_euler_rad w.as).z
           else AC_PosControl_lib.AC_PosControl.get_yaw_rad w.ps
  ({ w with au.yaw_angle_rad := a }, a)

/-- autoyaw.cpp:325-354 AutoYaw::rate_rads -/
def auto_yaw_rate_rads (w : World) : World × Float32 :=
  let r := if w.au.yaw_mode == .HOLD then (0.0 : Float32) else AC_PosControl_lib.AC_PosControl.get_yaw_rate_rads w.ps
  ({ w with au.yaw_rate_rads := r }, r)

/-- autoyaw.cpp:356-401 AutoYaw::get_heading (no RC input: no pilot yaw) -/
def auto_yaw_get_heading (w : World) : World × AC_Attitude_lib.AC_AttitudeControl.HeadingCommand :=
  let (w, a) := auto_yaw_yaw_rad w
  let (w, r) := auto_yaw_rate_rads w
  (w, { yaw_angle_rad := a, yaw_rate_rads := r, heading_mode := if w.au.yaw_mode == .HOLD then .Rate_Only else .Angle_And_Rate })

/-- mode_auto.cpp:465-500 ModeAuto::wp_start (with the NED destination: set_wp_destination_NED_m) -/
def wp_start (w : World) (dest : AC_WPNav_lib.Vector3p.State) : World × Bool := Id.run do
  let mut w := w
  if !(AC_WPNav_lib.AC_WPNav.is_active w.wps (wpInputs w)) then
    let stopping_point_ned_m : AC_WPNav_lib.Vector3p.State := AC_WPNav_lib.Vector3p.init_void
    let (wpp, wps, log) := AC_WPNav_lib.AC_WPNav.wp_and_spline_init_m w.wpp w.wps #[] (wpInputs w) 0.0 stopping_point_ned_m
    w := afterWP w wpp wps log
  let (wpp, wps, log, ok) := AC_WPNav_lib.AC_WPNav.set_wp_destination_NED_m w.wpp w.wps #[] (wpInputs w) dest
  w := afterWP w wpp wps log
  if !ok then
    return (w, false)
  w := auto_yaw_set_mode w (auto_yaw_default_mode w)
  w := { w with au.mode := .WP }
  return (w, true)

/-- mode_auto.cpp:1623-1676 ModeAuto::set_next_wp (the next command a waypoint) -/
def set_next_wp (w : World) (index : Nat) : World × Bool :=
  if index + 1 ≥ w.mission.size then (w, true) else
  let (wps, ok) := AC_WPNav_lib.AC_WPNav.set_wp_destination_next_NED_m w.wpp w.wps #[] (wpInputs w) w.mission[index + 1]!
  ({ w with wps }, ok)

/-- mode_auto.cpp:1578-1620 ModeAuto::do_nav_wp -/
def do_nav_wp (w : World) (index : Nat) : World := Id.run do
  let (w, ok) := wp_start w w.mission[index]!
  if !ok then
    return w
  let w := { w with au.loiter_time := 0, au.loiter_time_max := 0 }
  return (set_next_wp w index).1

/-- mode_auto.cpp:2297-2321 ModeAuto::verify_nav_wp -/
def verify_nav_wp (w : World) : World × Bool := Id.run do
  if !(AC_WPNav_lib.AC_WPNav.reached_wp_destination w.wps) then
    return (w, false)
  let mut w := w
  if w.au.loiter_time == 0 then
    w := { w with au.loiter_time := w.millis }
  if ((w.millis - w.au.loiter_time) / 1000) ≥ w.au.loiter_time_max.toUInt32 then
    return (w, true)
  return (w, false)

/-- mode_auto.cpp:374-395 ModeAuto::loiter_start -/
def loiter_start (w : World) : World × Bool :=
  let stopping_point_ned_m := AC_WPNav_lib.AC_WPNav.get_wp_stopping_point_NED_m #[] (wpInputs w) AC_WPNav_lib.Vector3p.init_void
  let (wpp, wps, log, _) := AC_WPNav_lib.AC_WPNav.set_wp_destination_NED_m w.wpp w.wps #[] (wpInputs w) stopping_point_ned_m
  let w := afterWP w wpp wps log
  let w := auto_yaw_set_mode w .HOLD
  ({ w with au.mode := .LOITER }, true)

/-- AP_Mission.cpp:2142-2152 AP_Mission::complete -> mode_auto.cpp:904-919 ModeAuto::exit_mission (not landed) -/
def mission_complete (w : World) : World :=
  (loiter_start { w with au.state := .COMPLETE }).1

/-- AP_Mission.cpp:2157-2240 AP_Mission::advance_current_nav_cmd (only navigation commands) -/
def mission_advance (w : World) : World × Bool :=
  if w.au.state != .RUNNING || w.au.nav_cmd_loaded then (w, false) else
  let index : Int := if w.au.nav_index < 0 then 0 else w.au.nav_index + 1
  if index ≥ w.mission.size then (w, false) else
  let w := { w with au.nav_index := index }
  let w := do_nav_wp w index.toNat
  ({ w with au.nav_cmd_loaded := true }, true)

/-- AP_Mission.cpp:109-119 AP_Mission::start -/
def mission_start (w : World) : World :=
  let w := { w with au.state := .RUNNING, au.nav_index := -1, au.nav_cmd_loaded := false }
  let (w, ok) := mission_advance w
  if !ok then mission_complete w else w

/-- AP_Mission.cpp:310-345 AP_Mission::update (navigation commands) -/
def mission_update (w : World) : World := Id.run do
  if w.au.state != .RUNNING || w.mission.isEmpty then
    return w
  if !w.au.nav_cmd_loaded || w.au.nav_index < 0 then
    let (w, ok) := mission_advance w
    if !ok then
      return mission_complete w
    return w
  let (w, done) := verify_nav_wp w
  if done then
    let w := { w with au.nav_cmd_loaded := false }
    let (w, ok) := mission_advance w
    if !ok then
      return mission_complete w
    return w
  return w

/-- mode_auto.cpp:23-80 ModeAuto::init -/
def auto_init (w : World) : World :=
  let w := { w with au.mode := .STARTING }
  let (wpp, wps, log) := AC_WPNav_lib.AC_WPNav.wp_and_spline_init_m w.wpp w.wps #[] (wpInputs w)
  let w := afterWP w wpp wps log
  { w with au.waiting_to_start := true }

/-- mode_auto.cpp:1134-1153 ModeAuto::wp_run (also loiter_run, :1194-1198) -/
def wp_run (w : World) : World := Id.run do
  let mut w := w
  w := { w with ms := AP_Motors_lib.AP_MotorsMatrix.set_desired_spool_state w.ms .THROTTLE_UNLIMITED }
  let (wps, log, _) := AC_WPNav_lib.AC_WPNav.update_wpnav w.wpp w.wps #[] (wpInputs w)
  w := afterWP w w.wpp wps log
  let (pp, ps, evs) := AC_PosControl_lib.AC_PosControl.D_update_controller w.pp w.ps #[] (posInputs w)
  w := { w with pp, ps }
  w := applyPos w evs
  let tv := AC_PosControl_lib.AC_PosControl.get_thrust_vector w.ps
  let (w', heading) := auto_yaw_get_heading w
  w := w'
  w := { w with as := AC_Attitude_lib.AC_AttitudeControl_Multi.input_thrust_vector_heading w.ap w.as (attInputs w) { x := tv.x, y := tv.y, z := tv.z } heading }
  return w

/-- mode_auto.cpp:91-150 ModeAuto::run (the EKF origin is always known) -/
def auto_run (w : World) : World :=
  let w := if w.au.waiting_to_start then { mission_start w with au.waiting_to_start := false } else mission_update w
  wp_run w

-- ---------------------------------------------------------------------------------------------
-- One tick (copter_ref.cpp `tick`)

/-- The tick; returns the world and the four actuators read after the motors output. -/
def tick (w : World) (smp : Sample) : World × Array Float32 := Id.run do
  let mut w := w
  -- AP_Scheduler::loop (AP_Scheduler.cpp:348-377): tick counter, loop time
  let first_tick := w.ticks32 == 0
  w := { w with ticks32 := w.ticks32 + 1, micros := w.micros + smp.dt_us,
                last_loop_time_s := if first_tick then (1.0 : Float32) / (400.0 : Float32) else smp.dt_us.toFloat32 * (1.0e-6 : Float32) }
  -- AP_InertialSensor::update: the tick's gyro
  w := { w with sample.gyro := smp.gyro }
  -- Copter::run_rate_controller_main (Attitude.cpp:10-24)
  let t := w.last_loop_time_s
  w := { w with ps := AC_PosControl_lib.AC_PosControl.set_dt_s w.ps t, as := AC_Attitude_lib.AC_AttitudeControl_Multi.set_dt_s w.as t,
                ms := AP_Motors_lib.AP_MotorsMatrix.set_dt_s w.ms t }
  let inp := attInputs w
  let ap := w.ap
  w := withMotors w (fun o => AC_Attitude_lib.AC_AttitudeControl_Multi.rate_controller_run ap w.as o inp)
  w := { w with as := AC_Attitude_lib.AC_AttitudeControl_Multi.rate_controller_target_reset w.as }
  -- Copter::motors_output_main -> AP_MotorsMulticopter::output
  let (mp, ms, _) := AP_Motors_lib.AP_MotorsMatrix.output w.mp w.ms #[] (motorsInputs w)
  w := { w with mp, ms }
  let act := #[w.ms._actuator[0]!, w.ms._actuator[1]!, w.ms._actuator[2]!, w.ms._actuator[3]!]
  -- Copter::read_AHRS: the sample, the view's update
  w := { w with sample := { smp with gyro := w.sample.gyro } }
  w := viewUpdate w
  -- Copter::read_inertia
  w := { w with ps := AC_PosControl_lib.AC_PosControl.update_estimates w.ps (posInputs w) false }
  -- on the first tick: Copter::set_mode(AUTO) -> ModeAuto::init, then the rate time constants (mode.cpp:465-469)
  if !w.in_auto then
    w := auto_init w
    w := { w with as := AC_Attitude_lib.AC_AttitudeControl_Multi.set_roll_pitch_rate_tc w.as w.h.ACRO_RP_RATE_TC }
    w := { w with as := AC_Attitude_lib.AC_AttitudeControl_Multi.set_yaw_rate_tc w.as w.h.PILOT_Y_RATE_TC, in_auto := true }
  -- Copter::update_flight_mode (mode.cpp:502-513): not landed; ModeAuto moves the vehicle on an EKF reset
  w := { w with as := AC_Attitude_lib.AC_AttitudeControl_Multi.landed_gain_reduction w.ap w.as false }
  w := { w with ps := AC_PosControl_lib.AC_PosControl.set_reset_handling_method w.ps .MoveVehicle }
  w := auto_run w
  return (w, act)

/-- The 18 trace numbers after the tick (sim/PROTOCOL.md), as doubles, with their bit patterns. -/
def traceValues (w : World) : Array Float × Array String :=
  let pd := AC_PosControl_lib.AC_PosControl.get_pos_desired_NED_m w.ps
  let vd := AC_PosControl_lib.AC_PosControl.get_vel_desired_NED_ms w.ps
  let ad := w.ps._accel_desired_ned_mss
  let tv := AC_PosControl_lib.AC_PosControl.get_thrust_vector w.ps
  let eu := AC_Attitude_lib.AC_AttitudeControl_Multi.get_att_target_euler_rad w.as
  let rb := AC_Attitude_lib.AC_AttitudeControl_Multi.rate_bf_targets w.as
  let fs := #[vd.x, vd.y, vd.z, ad.x, ad.y, ad.z, tv.x, tv.y, tv.z, eu.x, eu.y, eu.z, rb.x, rb.y, rb.z]
  (#[pd.x, pd.y, pd.z] ++ fs.map Float32.toFloat, #[h64 pd.x, h64 pd.y, h64 pd.z] ++ fs.map h32)

-- ---------------------------------------------------------------------------------------------
-- Construction, parameters, boot, takeover (copter_ref.cpp `main`)

/-- Construction (zero-filled objects and their constructors), the run deviations from the code
defaults, the parameter lines (`NAME VALUE`, `waypoint N E D`, `mission.clear`). -/
def construct (lines : List String) : Except String World := do
  let (mp, ms) := AP_Motors_lib.AP_MotorsMatrix.construct 400
  let (ap, as) := AC_Attitude_lib.AC_AttitudeControl_Multi.init
  let (pp, ps) := AC_PosControl_lib.AC_PosControl.init
  let (wpp, wps) := AC_WPNav_lib.AC_WPNav.init
  let vs := AHRS_View_lib.AP_AHRS_View.init
  let mut all : VehicleParams.All := { atc := ap, psc := pp, mot := mp, wp := wpp }
  let dev (a : VehicleParams.All) (n : String) (v : Float32) : VehicleParams.All := (VehicleParams.set a n v).getD a
  -- run deviations from the code defaults (SITL's copter.parm:5-6, :71; MOT_BAT_VOLT_MAX's code default)
  all := dev all "ATC_RAT_YAW_P" 0.3
  all := dev all "ATC_RAT_YAW_I" 0.02
  all := dev all "MOT_HOVER_LEARN" 0
  all := dev all "MOT_THST_HOVER" 0.39
  all := dev all "MOT_BAT_VOLT_MAX" 0.0
  let mut h : HarnessParams := {}
  -- the built-in mission (sim/PROTOCOL.md)
  let mut mission : Array AC_WPNav_lib.Vector3p.State := #[{ x := 0, y := 0, z := -5 }, { x := 10, y := 0, z := -5 }, { x := 10, y := 10, z := -5 }]
  let mut given := false
  for line0 in lines do
    let line := ((line0.splitOn "#").head!).replace "," " "
    let w := ((line.splitOn " ").map (·.trimAscii.toString)).filter (· ≠ "") |>.toArray
    if w.isEmpty then continue
    if w[0]! == "mission.clear" then
      mission := #[]
      given := true
      continue
    if w[0]! == "waypoint" then
      if w.size < 4 then throw s!"expected waypoint N E D: {line0}"
      if !given then
        mission := #[]
        given := true
      let c (i : Nat) := (toF64 w[i]!).getD 0
      mission := mission.push { x := c 1, y := c 2, z := c 3 }
      continue
    if w.size != 2 then throw s!"expected NAME VALUE: {line0}"
    let v := (toF32 w[1]!).getD 0
    match VehicleParams.set all w[0]! v with
    | some a => all := a
    | none =>
      match setHarnessParam h w[0]! v with
      | some h' => h := h'
      | none => throw s!"unknown parameter {w[0]!}"
  return { mp := all.mot, ms, ap := all.atc, as, pp := all.psc, ps, wpp := all.wp, wps, vs, h, mission }

/-- The parameters as `--print-params` prints them. -/
def paramLines (w : World) : List String :=
  let all : VehicleParams.All := { atc := w.ap, psc := w.pp, mot := w.mp, wp := w.wpp }
  (VehicleParams.names.toList.map fun n => s!"{n} {exactDecimal ((VehicleParams.get all n).getD 0).toFloat}") ++
  [s!"WP_YAW_BEHAVIOR {w.h.WP_YAW_BEHAVIOR}", s!"PILOT_Y_RATE_TC {exactDecimal w.h.PILOT_Y_RATE_TC.toFloat}",
   s!"ACRO_RP_RATE_TC {exactDecimal w.h.ACRO_RP_RATE_TC.toFloat}", s!"run.air_density_ratio {exactDecimal w.h.air_density_ratio.toFloat}",
   s!"run.start_hover {w.h.start_hover}"] ++
  (w.mission.toList.map fun p => s!"waypoint {exactDecimal p.x} {exactDecimal p.y} {exactDecimal p.z}")

/-- Boot: AP_MotorsMatrix::init(QUAD, X) (radio.cpp:56), armed, interlocked, THROTTLE_UNLIMITED. -/
def boot (w : World) : World :=
  let (ms, _) := AP_Motors_lib.AP_MotorsMatrix.init_motor_frame_class_motor_frame_type w.ms #[] .MOTOR_FRAME_QUAD .MOTOR_FRAME_TYPE_X
  let (ms, _) := AP_Motors_lib.AP_MotorsMatrix.armed_bool ms #[] true
  let ms := AP_Motors_lib.AP_MotorsMatrix.set_interlock ms true
  let ms := AP_Motors_lib.AP_MotorsMatrix.set_desired_spool_state ms .THROTTLE_UNLIMITED
  { w with ms := { ms with _spool_state := .THROTTLE_UNLIMITED } }

/-- The takeover on the first sample: the view of the sample, relax, hover throttle. -/
def takeover (w : World) (smp : Sample) : World := Id.run do
  let mut w := { w with sample := smp }
  w := viewUpdate w
  w := { w with as := AC_Attitude_lib.AC_AttitudeControl_Multi.relax_attitude_controllers_void w.as (attInputs w) }
  if w.h.start_hover != 0 then
    let hover := AP_Motors_lib.AP_MotorsMatrix.get_throttle_hover w.mp
    let inp := attInputs w
    w := withMotors w (fun o => AC_Attitude_lib.AC_AttitudeControl_Multi.set_throttle_out w.ap w.as o inp hover true (2.0 : Float32))
    w := { w with ms := { w.ms with _throttle_filter := AP_Motors_lib.LowPassFilterFloat.reset_float w.ms._throttle_filter w.ms._throttle_in } }
  return w

end Vehicle
