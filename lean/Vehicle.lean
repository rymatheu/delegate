import Copter_lib
import AHRS_View_lib
import VehicleParams

/-!
# The Lean vehicle (executable `copter_lean`, `VehicleMain.lean`)

The translation of AP_MotorsMatrix, AC_AttitudeControl_Multi, AC_PosControl and AC_WPNav as one World
(`Copter_lib`, `ardupilot/translate_copter.sh`) and the AHRS view derivation (`AHRS_View_lib`:
AP_AHRS_View::update with AP_AHRS::calc_trig), wired for one 400 Hz tick of Auto mode per input line
of the lock-step protocol (sim/PROTOCOL.md).

Everything here is harness; the classes are the translations, unchanged. It is the harness of
`ardupilot/vehicle/copter_ref.cpp`, which drives the compiled C++ classes, function by function in
the same order and with the same names: the protocol, the parameters by ArduPilot name
(`VehicleParams`, generated from the translations' var_info tables), construction, boot and
takeover, the tick, and the mission harness written from ArduCopter's C++ (each function marked with
the file and lines it mirrors).

The four controllers are one translation (`Copter_lib`, cpp2lean `--world`, README.md "The World"):
their objects are the fields of `Copter_lib.World`, built by `World.init` as `ardupilot/unity_copter.cpp`
defines them, and their calls into each other (the navigator into the position controller, the
position controller into the attitude controller, the attitude controller into the motors) are
translated calls on those fields. What the harness provides is the boundary: each object's `Inputs`
in the World (`'inp`), set from the input line, the AHRS view and the clock before the controllers
run (`setInputs`), and the motors' HAL calls (`Output` events), which the harness discards.
The AHRS estimate of the line is the boundary of the view: the view's rotation matrix input is the
estimate quaternion's `rotation_matrix` (as the EKF's dcm), its gyro the line's gyro. As in the
reference vehicle's AHRS stub, the attitude controller reads the estimate's quaternion itself
(`get_quat_body_to_ned`; the real view converts its matrix back with `from_rotation_matrix`).
-/

open FloatLib.Floats (Binary32 Binary64)

namespace Vehicle

-- ---------------------------------------------------------------------------------------------
-- Text: hex, exact decimals, six decimals, decimal input

def hex (width : Nat) (n : Nat) : String :=
  let d := String.ofList (Nat.toDigits 16 n)
  String.ofList (List.replicate (width - d.length) '0') ++ d
def h32 (x : Binary32) : String := hex 8 (Binary32.toBits x).toNat
def h64 (x : Binary64) : String := hex 16 (Binary64.toBits x).toNat

/-- The exact value of a finite double: (negative, m, e) with |x| = m * 2^e. -/
def decompose (x : Binary64) : Bool × Nat × Int :=
  let b := (Binary64.toBits x).toNat
  let neg := b >>> 63 == 1
  let ex := (b >>> 52) % 2048
  let fr := b % (2 ^ 52)
  if ex == 0 then (neg, fr, -1074) else (neg, fr + 2 ^ 52, (ex : Int) - 1075)

/-- `copter_ref.cpp` `exact_decimal`: the exact decimal expansion, no exponent, trailing zeros
dropped, the sign of zero dropped (`%.1100f` of Apple's printf, trimmed). -/
def exactDecimal (x : Binary64) : String :=
  if Binary64.isNaN x then "nan" else if Binary64.isInf x then (if x < 0 then "-inf" else "inf") else if x == 0 then "0" else
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
def sixDecimals (x : Binary64) : String :=
  if Binary64.isNaN x then "nan" else if Binary64.isInf x then (if x < 0 then "-inf" else "inf") else
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

/-- strtod: correctly rounded (FloatLib's `OfScientific Binary64` rounds the exact rational once). -/
def toF64 (t : String) : Option Binary64 :=
  (parseDecimal t).map fun (neg, m, e) =>
    let v : Binary64 := if e ≥ 0 then OfScientific.ofScientific m false e.toNat else OfScientific.ofScientific m true (-e).toNat
    if neg then -v else v

/-- strtof: correctly rounded, once (FloatLib's `OfScientific Binary32` is). -/
def toF32 (t : String) : Option Binary32 :=
  (parseDecimal t).map fun (neg, m, e) =>
    let v : Binary32 := if e ≥ 0 then OfScientific.ofScientific m false e.toNat else OfScientific.ofScientific m true (-e).toNat
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
  pos : Copter_lib.Vector3p.State
  vel : Copter_lib.Vector3f.State
  acc : Copter_lib.Vector3f.State
  quat : Copter_lib.Quaternion.State
  gyro : Copter_lib.Vector3f.State
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
  PILOT_Y_RATE_TC : Binary32 := 0.0
  ACRO_RP_RATE_TC : Binary32 := 0.0
  air_density_ratio : Binary32 := 1.0
  start_hover : Int := 1

/-- `copter_ref.cpp` `set_harness_param`. -/
def setHarnessParam (h : HarnessParams) (name : String) (v : Binary32) : Option HarnessParams :=
  if name == "WP_YAW_BEHAVIOR" then some { h with WP_YAW_BEHAVIOR := (Binary32.toInt32 v).toInt }
  else if name == "PILOT_Y_RATE_TC" then some { h with PILOT_Y_RATE_TC := v }
  else if name == "ACRO_RP_RATE_TC" then some { h with ACRO_RP_RATE_TC := v }
  else if name == "run.air_density_ratio" then some { h with air_density_ratio := v }
  else if name == "run.start_hover" then some { h with start_hover := (Binary32.toInt32 v).toInt }
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
  yaw_angle_rad : Binary32 := 0.0
  yaw_rate_rads : Binary32 := 0.0
  state : MissionState := .STOPPED
  nav_index : Int := -1
  nav_cmd_loaded : Bool := false

-- ---------------------------------------------------------------------------------------------
-- The world: the objects, the scheduler and clock, the AHRS sample, the mission

structure World where
  c : Copter_lib.World
  vs : AHRS_View_lib.AP_AHRS_View.State
  h : HarnessParams := {}
  mission : Array Copter_lib.Vector3p.State := #[]
  au : Auto := {}
  in_auto : Bool := false
  ticks32 : UInt32 := 0
  micros : UInt64 := 0
  last_loop_time_s : Binary32 := 0
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

/-- The boundary inputs of the four controllers (their `'inp` fields in the World): the AHRS view
and the AHRS stub's answers for the sample, the scheduler's loop time, the HAL clock. -/
def setInputs (w : World) : World :=
  let v := w.vs
  let smp := w.sample
  let clk : Copter_lib.AC_PID.Inputs := { _slew_limiter := { millis := w.millis } }
  let one : Binary32 := Binary32.ofBits 0x3f800000 /- 1.0 -/
  { w with c := { w.c with
      attitude_control'inp := { get_quat_body_to_ned_q := smp.quat, yaw := v.yaw, get_filtered_loop_time := w.last_loop_time_s,
                                cos_pitch := v.trig.cos_pitch, cos_roll := v.trig.cos_roll, micros64 := w.micros,
                                get_gyro_latest := smp.gyro, _pid_rate_roll := clk, _pid_rate_pitch := clk, _pid_rate_yaw := clk },
      pos_control'inp := { get_relative_position_NED_origin_vec := smp.pos, get_relative_position_NED_origin := true,
                           get_relative_position_D_origin_float_posD := Binary64.toBinary32 smp.pos.z, get_relative_position_D_origin_float := true,
                           get_velocity_NED_vec := smp.vel, get_velocity_NED := true,
                           get_vert_pos_rate_D_velocity := smp.vel.z, get_vert_pos_rate_D := true,
                           millis := w.millis, ticks32 := w.ticks32, yaw := v.yaw, get_position_NE_reset_count := 0,
                           has_good_timing := true, get_control_gain_scaler_XY := one, cos_yaw := v.trig.cos_yaw, sin_yaw := v.trig.sin_yaw,
                           get_accel_ef := smp.acc, get_position_D_reset_count := 0, get_control_gain_scaler_Z := one,
                           _pid_accel_d_m := clk },
      motors'inp := { micros := w.micros32, thr_lin := { get_air_density_ratio := w.h.air_density_ratio } },
      wp_nav'inp := { millis := w.millis } } }

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
    w := { w with au.yaw_angle_rad := (Copter_lib.AC_AttitudeControl_Multi.get_att_target_euler_rad w.c.attitude_control).z }
  return w

/-- autoyaw.cpp:234-323 AutoYaw::yaw_rad -/
def auto_yaw_yaw_rad (w : World) : World × Binary32 :=
  let a := if w.au.yaw_mode == .HOLD then (Copter_lib.AC_AttitudeControl_Multi.get_att_target_euler_rad w.c.attitude_control).z
           else Copter_lib.AC_PosControl.get_yaw_rad w.c.pos_control
  ({ w with au.yaw_angle_rad := a }, a)

/-- autoyaw.cpp:325-354 AutoYaw::rate_rads -/
def auto_yaw_rate_rads (w : World) : World × Binary32 :=
  let r := if w.au.yaw_mode == .HOLD then (Binary32.ofBits 0x00000000 /- 0.0 -/) else Copter_lib.AC_PosControl.get_yaw_rate_rads w.c.pos_control
  ({ w with au.yaw_rate_rads := r }, r)

/-- autoyaw.cpp:356-401 AutoYaw::get_heading (no RC input: no pilot yaw) -/
def auto_yaw_get_heading (w : World) : World × Copter_lib.AC_AttitudeControl.HeadingCommand :=
  let (w, a) := auto_yaw_yaw_rad w
  let (w, r) := auto_yaw_rate_rads w
  (w, { yaw_angle_rad := a, yaw_rate_rads := r, heading_mode := if w.au.yaw_mode == .HOLD then .Rate_Only else .Angle_And_Rate })

/-- `wp_nav->wp_and_spline_init_m(speed, stopping_point)` on the World. -/
def wp_and_spline_init_m (w : World) (speed : Binary32) (stop : Copter_lib.Vector3p.State) : World :=
  let c := w.c
  let (p, s, c) := Copter_lib.AC_WPNav.wp_and_spline_init_m c.wp_nav'p c.wp_nav c c.wp_nav'inp speed stop
  { w with c := { c with wp_nav'p := p, wp_nav := s } }

/-- `wp_nav->set_wp_destination_NED_m(dest)` on the World. -/
def set_wp_destination_NED_m (w : World) (dest : Copter_lib.Vector3p.State) : World × Bool :=
  let c := w.c
  let (p, s, c, ok) := Copter_lib.AC_WPNav.set_wp_destination_NED_m c.wp_nav'p c.wp_nav c c.wp_nav'inp dest
  ({ w with c := { c with wp_nav'p := p, wp_nav := s } }, ok)

/-- mode_auto.cpp:465-500 ModeAuto::wp_start (with the NED destination: set_wp_destination_NED_m) -/
def wp_start (w : World) (dest : Copter_lib.Vector3p.State) : World × Bool := Id.run do
  let mut w := w
  if !(Copter_lib.AC_WPNav.is_active w.c.wp_nav w.c.wp_nav'inp) then
    w := wp_and_spline_init_m w (Binary32.ofBits 0x00000000 /- 0.0 -/) Copter_lib.Vector3p.init_void
  let (w', ok) := set_wp_destination_NED_m w dest
  w := w'
  if !ok then
    return (w, false)
  w := auto_yaw_set_mode w (auto_yaw_default_mode w)
  w := { w with au.mode := .WP }
  return (w, true)

/-- mode_auto.cpp:1623-1676 ModeAuto::set_next_wp (the next command a waypoint) -/
def set_next_wp (w : World) (index : Nat) : World × Bool :=
  if index + 1 ≥ w.mission.size then (w, true) else
  let c := w.c
  let (s, ok) := Copter_lib.AC_WPNav.set_wp_destination_next_NED_m c.wp_nav'p c.wp_nav c w.mission[index + 1]!
  ({ w with c := { c with wp_nav := s } }, ok)

/-- mode_auto.cpp:1578-1620 ModeAuto::do_nav_wp -/
def do_nav_wp (w : World) (index : Nat) : World := Id.run do
  let (w, ok) := wp_start w w.mission[index]!
  if !ok then
    return w
  let w := { w with au.loiter_time := 0, au.loiter_time_max := 0 }
  return (set_next_wp w index).1

/-- mode_auto.cpp:2297-2321 ModeAuto::verify_nav_wp -/
def verify_nav_wp (w : World) : World × Bool := Id.run do
  if !(Copter_lib.AC_WPNav.reached_wp_destination w.c.wp_nav) then
    return (w, false)
  let mut w := w
  if w.au.loiter_time == 0 then
    w := { w with au.loiter_time := w.millis }
  if ((w.millis - w.au.loiter_time) / 1000) ≥ w.au.loiter_time_max.toUInt32 then
    return (w, true)
  return (w, false)

/-- mode_auto.cpp:374-395 ModeAuto::loiter_start -/
def loiter_start (w : World) : World × Bool :=
  let stopping_point_ned_m := Copter_lib.AC_WPNav.get_wp_stopping_point_NED_m w.c Copter_lib.Vector3p.init_void
  let (w, _) := set_wp_destination_NED_m w stopping_point_ned_m
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
  let w := wp_and_spline_init_m w (Binary32.ofBits 0x00000000 /- 0.0f -/) Copter_lib.Vector3p.init_void
  { w with au.waiting_to_start := true }

/-- mode_auto.cpp:1134-1153 ModeAuto::wp_run (also loiter_run, :1194-1198) -/
def wp_run (w : World) : World := Id.run do
  let mut w := w
  let mut c := w.c
  c := { c with motors := Copter_lib.AP_MotorsMatrix.set_desired_spool_state c.motors .THROTTLE_UNLIMITED }
  let (s, c', _) := Copter_lib.AC_WPNav.update_wpnav c.wp_nav'p c.wp_nav c c.wp_nav'inp
  c := { c' with wp_nav := s }
  let (pp, ps, c') := Copter_lib.AC_PosControl.D_update_controller c.pos_control'p c.pos_control c c.pos_control'inp
  c := { c' with pos_control'p := pp, pos_control := ps }
  w := { w with c }
  let tv := Copter_lib.AC_PosControl.get_thrust_vector w.c.pos_control
  let (w', heading) := auto_yaw_get_heading w
  w := w'
  c := w.c
  w := { w with c := { c with attitude_control := Copter_lib.AC_AttitudeControl_Multi.input_thrust_vector_heading c.attitude_control'p c.attitude_control c.attitude_control'inp tv heading } }
  return w

/-- mode_auto.cpp:91-150 ModeAuto::run (the EKF origin is always known) -/
def auto_run (w : World) : World :=
  let w := if w.au.waiting_to_start then { mission_start w with au.waiting_to_start := false } else mission_update w
  wp_run w

-- ---------------------------------------------------------------------------------------------
-- One tick (copter_ref.cpp `tick`)

/-- The tick; returns the world and the four actuators read after the motors output. -/
def tick (w : World) (smp : Sample) : World × Array Binary32 := Id.run do
  let mut w := w
  -- AP_Scheduler::loop (AP_Scheduler.cpp:348-377): tick counter, loop time
  let first_tick := w.ticks32 == 0
  w := { w with ticks32 := w.ticks32 + 1, micros := w.micros + smp.dt_us,
                last_loop_time_s := if first_tick then (Binary32.ofBits 0x3f800000 /- 1.0 -/) / (Binary32.ofBits 0x43c80000 /- 400.0 -/) else UInt64.toBinary32 smp.dt_us * (Binary32.ofBits 0x358637bd /- 1.0e-6 -/) }
  -- AP_InertialSensor::update: the tick's gyro
  w := setInputs { w with sample.gyro := smp.gyro }
  -- Copter::run_rate_controller_main (Attitude.cpp:10-24)
  let t := w.last_loop_time_s
  let mut c := w.c
  c := { c with pos_control := Copter_lib.AC_PosControl.set_dt_s c.pos_control t,
                attitude_control := Copter_lib.AC_AttitudeControl_Multi.set_dt_s c.attitude_control t,
                motors := Copter_lib.AP_MotorsMatrix.set_dt_s c.motors t }
  let (s, c') := Copter_lib.AC_AttitudeControl_Multi.rate_controller_run c.attitude_control'p c.attitude_control c c.attitude_control'inp
  c := { c' with attitude_control := s }
  c := { c with attitude_control := Copter_lib.AC_AttitudeControl_Multi.rate_controller_target_reset c.attitude_control }
  -- Copter::motors_output_main -> AP_MotorsMulticopter::output
  let (mp, ms, _) := Copter_lib.AP_MotorsMatrix.output c.motors'p c.motors #[] c.motors'inp
  c := { c with motors'p := mp, motors := ms }
  let act := #[ms._actuator[0]!, ms._actuator[1]!, ms._actuator[2]!, ms._actuator[3]!]
  -- Copter::read_AHRS: the sample, the view's update
  w := { w with c, sample := { smp with gyro := w.sample.gyro } }
  w := setInputs (viewUpdate w)
  -- Copter::read_inertia
  c := w.c
  w := { w with c := { c with pos_control := Copter_lib.AC_PosControl.update_estimates c.pos_control c.pos_control'inp false } }
  -- on the first tick: Copter::set_mode(AUTO) -> ModeAuto::init, then the rate time constants (mode.cpp:465-469)
  if !w.in_auto then
    w := auto_init w
    c := w.c
    c := { c with attitude_control := Copter_lib.AC_AttitudeControl_Multi.set_roll_pitch_rate_tc c.attitude_control w.h.ACRO_RP_RATE_TC }
    c := { c with attitude_control := Copter_lib.AC_AttitudeControl_Multi.set_yaw_rate_tc c.attitude_control w.h.PILOT_Y_RATE_TC }
    w := { w with c, in_auto := true }
  -- Copter::update_flight_mode (mode.cpp:502-513): not landed; ModeAuto moves the vehicle on an EKF reset
  c := w.c
  c := { c with attitude_control := Copter_lib.AC_AttitudeControl_Multi.landed_gain_reduction c.attitude_control'p c.attitude_control false }
  c := { c with pos_control := Copter_lib.AC_PosControl.set_reset_handling_method c.pos_control .MoveVehicle }
  w := auto_run { w with c }
  return (w, act)

/-- The 18 trace numbers after the tick (sim/PROTOCOL.md), as doubles, with their bit patterns. -/
def traceValues (w : World) : Array Binary64 × Array String :=
  let ps := w.c.pos_control
  let pd := Copter_lib.AC_PosControl.get_pos_desired_NED_m ps
  let vd := Copter_lib.AC_PosControl.get_vel_desired_NED_ms ps
  let ad := ps._accel_desired_ned_mss
  let tv := Copter_lib.AC_PosControl.get_thrust_vector ps
  let eu := Copter_lib.AC_AttitudeControl_Multi.get_att_target_euler_rad w.c.attitude_control
  let rb := Copter_lib.AC_AttitudeControl_Multi.rate_bf_targets w.c.attitude_control
  let fs := #[vd.x, vd.y, vd.z, ad.x, ad.y, ad.z, tv.x, tv.y, tv.z, eu.x, eu.y, eu.z, rb.x, rb.y, rb.z]
  (#[pd.x, pd.y, pd.z] ++ fs.map Binary32.toBinary64, #[h64 pd.x, h64 pd.y, h64 pd.z] ++ fs.map h32)

-- ---------------------------------------------------------------------------------------------
-- Construction, parameters, boot, takeover (copter_ref.cpp `main`)

/-- Construction (zero-filled objects and their constructors: `Copter_lib.World.init`, the objects of
`ardupilot/unity_copter.cpp`), the run deviations from the code defaults, the parameter lines
(`NAME VALUE`, `waypoint N E D`, `mission.clear`). -/
def construct (lines : List String) : Except String World := do
  let c := Copter_lib.World.init
  let vs := AHRS_View_lib.AP_AHRS_View.init
  let mut all : VehicleParams.All := { atc := c.attitude_control'p, psc := c.pos_control'p, mot := c.motors'p, wp := c.wp_nav'p }
  let dev (a : VehicleParams.All) (n : String) (v : Binary32) : VehicleParams.All := (VehicleParams.set a n v).getD a
  -- run deviations from the code defaults (SITL's copter.parm:5-6, :71; MOT_BAT_VOLT_MAX's code default)
  all := dev all "ATC_RAT_YAW_P" 0.3
  all := dev all "ATC_RAT_YAW_I" 0.02
  all := dev all "MOT_HOVER_LEARN" 0
  all := dev all "MOT_THST_HOVER" 0.39
  all := dev all "MOT_BAT_VOLT_MAX" 0.0
  let mut h : HarnessParams := {}
  -- the built-in mission (sim/PROTOCOL.md)
  let mut mission : Array Copter_lib.Vector3p.State := #[{ x := 0, y := 0, z := -5 }, { x := 10, y := 0, z := -5 }, { x := 10, y := 10, z := -5 }]
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
  let c := { c with attitude_control'p := all.atc, pos_control'p := all.psc, motors'p := all.mot, wp_nav'p := all.wp }
  return { c, vs, h, mission }

/-- The parameters as `--print-params` prints them. -/
def paramLines (w : World) : List String :=
  let all : VehicleParams.All := { atc := w.c.attitude_control'p, psc := w.c.pos_control'p, mot := w.c.motors'p, wp := w.c.wp_nav'p }
  (VehicleParams.names.toList.map fun n => s!"{n} {exactDecimal (Binary32.toBinary64 ((VehicleParams.get all n).getD 0))}") ++
  [s!"WP_YAW_BEHAVIOR {w.h.WP_YAW_BEHAVIOR}", s!"PILOT_Y_RATE_TC {exactDecimal (Binary32.toBinary64 w.h.PILOT_Y_RATE_TC)}",
   s!"ACRO_RP_RATE_TC {exactDecimal (Binary32.toBinary64 w.h.ACRO_RP_RATE_TC)}", s!"run.air_density_ratio {exactDecimal (Binary32.toBinary64 w.h.air_density_ratio)}",
   s!"run.start_hover {w.h.start_hover}"] ++
  (w.mission.toList.map fun p => s!"waypoint {exactDecimal p.x} {exactDecimal p.y} {exactDecimal p.z}")

/-- Boot: AP_MotorsMatrix::init(QUAD, X) (radio.cpp:56), armed, interlocked, THROTTLE_UNLIMITED. -/
def boot (w : World) : World :=
  let c := w.c
  let (ms, _) := Copter_lib.AP_MotorsMatrix.init_motor_frame_class_motor_frame_type c.motors #[] .MOTOR_FRAME_QUAD .MOTOR_FRAME_TYPE_X
  let (ms, _) := Copter_lib.AP_MotorsMatrix.armed_bool ms #[] true
  let ms := Copter_lib.AP_MotorsMatrix.set_interlock ms true
  let ms := Copter_lib.AP_MotorsMatrix.set_desired_spool_state ms .THROTTLE_UNLIMITED
  { w with c := { c with motors := { ms with _spool_state := .THROTTLE_UNLIMITED } } }

/-- The takeover on the first sample: the view of the sample, relax, hover throttle. -/
def takeover (w : World) (smp : Sample) : World := Id.run do
  let mut w := setInputs (viewUpdate { w with sample := smp })
  let mut c := w.c
  c := { c with attitude_control := Copter_lib.AC_AttitudeControl_Multi.relax_attitude_controllers_void c.attitude_control c.attitude_control'inp }
  if w.h.start_hover != 0 then
    let hover := Copter_lib.AP_MotorsMatrix.get_throttle_hover c.motors'p
    let (s, c') := Copter_lib.AC_AttitudeControl_Multi.set_throttle_out c.attitude_control'p c.attitude_control c c.attitude_control'inp hover true (Binary32.ofBits 0x40000000 /- 2.0 -/)
    c := { c' with attitude_control := s }
    c := { c with motors := { c.motors with _throttle_filter := Copter_lib.LowPassFilterFloat.reset_float c.motors._throttle_filter c.motors._throttle_in } }
  return { w with c }

end Vehicle
