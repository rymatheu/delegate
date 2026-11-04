import AP_Motors.AP_MotorsMulticopter

/-!
# `AP_MotorsMatrix`, quad X

Mirrors, at ArduPilot 802db19de1, `libraries/AP_Motors/AP_MotorsMatrix.h:10-11`, `:85-89`,
`:144-149` and `AP_MotorsMatrix.cpp`:
- `:23-41` `init` (quad X), `:1291-1350` `setup_motors`, `:577-603` `setup_quad_matrix`
  (`MOTOR_FRAME_TYPE_X`), `:504-546` `add_motor_raw`/`add_motor`, `:549-560` `remove_motor`,
  `:562-568` `add_motors`, `:1354-1388` `normalise_rpy_factors`;
- `:207-210` `boost_ratio`, `:214-405` `output_armed_stabilizing`, `:144-184` `output_to_motors`
  (the `SPOOLING_UP`/`THROTTLE_UNLIMITED`/`SPOOLING_DOWN` case);
- `AP_MotorsMulticopter.cpp:273-304` `output`, the per-tick entry, here on the matrix state
  because it dispatches to the two virtual methods above.

Per-tick use by the Copter loop: `set_dt_s` (before the rate controller), the controller-facing
setters of `AP_Motors.Interface` on `s.toInputs`, then `output p s`, which returns the new state
and the four actuator values in [0, 1].

The environment assumptions of `AP_MotorsMulticopter` apply (armed, interlocked,
`THROTTLE_UNLIMITED`, `_thrust_boost` false). Left out, with the reason:
- every `_thrust_boost` branch of `output_armed_stabilizing` (`:285` second conjunct, `:312-326`,
  `:347` second conjunct, `:353-358`): dead while `_thrust_boost` is false. `boost_ratio` is kept,
  since its arithmetic is executed with `_thrust_boost_ratio = 0`;
- `check_for_failed_motor` (`:415-462`), called at `:404`: it writes `_thrust_rpyt_out_filt`,
  `_motor_lost_index`, `_thrust_balanced`, and may clear `_thrust_boost`; all are read only under
  `_thrust_boost`, and with four motors `number_motors >= 6` (`:451`) never holds, so
  `_thrust_balanced` stays true. Quads cannot use motor-loss handling (`:273`);
- `thrust_compensation` (`:1396-1401`): the callback is set only for tiltrotors and tiltwings;
- the `SHUT_DOWN` and `GROUND_IDLE` cases of `output_to_motors` (`:149-165`) and the PWM conversion
  (`:178-183`);
- frame classes and types other than quad X, `set_frame_class_and_type`, scripting frames,
  `set_update_rate`, `add_motor_num` (`SRV_Channels` defaults only), `_frame_class_string`,
  `_mav_type`, motor tests, `disable_yaw_torque`, `get_motor_mask`, `get_factors`.

Not one to one: motor numbers are `Fin 4`, so the C++ range check `motor_num <
AP_MOTORS_MAX_NUM_MOTORS` (`:512`, `:552`) is by type; `setup_motors` removes slots 0-3 only (slots
4-11 start disabled and are never enabled for quad X).
-/

namespace AP_MotorsMatrix

open AP_Math AP_Motors AP_MotorsMulticopter

/-- `AP_MOTORS_MATRIX_YAW_FACTOR_CW` (`AP_MotorsMatrix.h:10`), converted to `float` in `MotorDef`. -/
def AP_MOTORS_MATRIX_YAW_FACTOR_CW : ftype := -1
/-- `AP_MOTORS_MATRIX_YAW_FACTOR_CCW` (`AP_MotorsMatrix.h:11`). -/
def AP_MOTORS_MATRIX_YAW_FACTOR_CCW : ftype := 1

/-- `struct MotorDef` (`AP_MotorsMatrix.h:85-89`). -/
structure MotorDef where
  angle_degrees : ftype
  yaw_factor : ftype
  testing_order : UInt8
  deriving Repr

/-- The `AP_MotorsMatrix` members (`AP_MotorsMatrix.h:144-149`), slots 0-3. -/
structure State extends AP_MotorsMulticopter.State where
  _roll_factor : Vector ftype 4 := #v[0.0, 0.0, 0.0, 0.0]
  _pitch_factor : Vector ftype 4 := #v[0.0, 0.0, 0.0, 0.0]
  _yaw_factor : Vector ftype 4 := #v[0.0, 0.0, 0.0, 0.0]
  _throttle_factor : Vector ftype 4 := #v[0.0, 0.0, 0.0, 0.0]
  _thrust_rpyt_out : Vector ftype 4 := #v[0.0, 0.0, 0.0, 0.0]
  _test_order : Vector UInt8 4 := #v[0, 0, 0, 0]
  deriving Repr

/-! ### Frame setup -/

/-- `add_motor_raw(motor_num, roll_fac, pitch_fac, yaw_fac, testing_order, throttle_factor)`
(`AP_MotorsMatrix.cpp:504-529`). -/
def add_motor_raw (s : State) (motor_num : Fin 4) (roll_fac pitch_fac yaw_fac : ftype)
    (testing_order : UInt8) (throttle_factor : ftype := 1.0) : State :=
  if s._initialised_ok then
    -- do not allow motors to be set if the current frame type has init correctly
    s
  else
    { s with
      motor_enabled := s.motor_enabled.set motor_num true
      _roll_factor := s._roll_factor.set motor_num roll_fac
      _pitch_factor := s._pitch_factor.set motor_num pitch_fac
      _yaw_factor := s._yaw_factor.set motor_num yaw_fac
      _throttle_factor := s._throttle_factor.set motor_num throttle_factor
      _test_order := s._test_order.set motor_num testing_order }
    -- add_motor_num (SRV_Channels default only) is not ported

/-- `add_motor(motor_num, roll_factor_in_degrees, pitch_factor_in_degrees, yaw_factor,
testing_order)` (`.cpp:538-546`), the five-argument overload. -/
def add_motor_rp (s : State) (motor_num : Fin 4) (roll_factor_in_degrees pitch_factor_in_degrees yaw_factor : ftype)
    (testing_order : UInt8) : State :=
  add_motor_raw s motor_num
    (radians (roll_factor_in_degrees + 90)).cos
    (radians pitch_factor_in_degrees).cos
    yaw_factor
    testing_order

/-- `add_motor(motor_num, angle_degrees, yaw_factor, testing_order)` (`.cpp:532-535`). -/
def add_motor (s : State) (motor_num : Fin 4) (angle_degrees yaw_factor : ftype) (testing_order : UInt8) : State :=
  add_motor_rp s motor_num angle_degrees angle_degrees yaw_factor testing_order

/-- `remove_motor(motor_num)` (`.cpp:549-560`). -/
def remove_motor (s : State) (motor_num : Fin 4) : State :=
  { s with
    motor_enabled := s.motor_enabled.set motor_num false
    _roll_factor := s._roll_factor.set motor_num 0.0
    _pitch_factor := s._pitch_factor.set motor_num 0.0
    _yaw_factor := s._yaw_factor.set motor_num 0.0
    _throttle_factor := s._throttle_factor.set motor_num 0.0 }

/-- `add_motors(motors, num_motors)` (`.cpp:562-568`) for four motors. -/
def add_motors (s : State) (motors : Vector MotorDef 4) : State := Id.run do
  let mut s := s
  for i in List.finRange 4 do
    let motor := motors[i]
    s := add_motor s i motor.angle_degrees motor.yaw_factor motor.testing_order
  return s

/-- `setup_quad_matrix(MOTOR_FRAME_TYPE_X)` (`.cpp:577-603`); returns `success = true`. -/
def setup_quad_matrix (s : State) : State × Bool :=
  let motors : Vector MotorDef 4 := #v[
    {   angle_degrees := 45, yaw_factor := AP_MOTORS_MATRIX_YAW_FACTOR_CCW, testing_order := 1 },
    { angle_degrees := -135, yaw_factor := AP_MOTORS_MATRIX_YAW_FACTOR_CCW, testing_order := 3 },
    {  angle_degrees := -45, yaw_factor := AP_MOTORS_MATRIX_YAW_FACTOR_CW,  testing_order := 4 },
    {  angle_degrees := 135, yaw_factor := AP_MOTORS_MATRIX_YAW_FACTOR_CW,  testing_order := 2 }]
  (add_motors s motors, true)

/-- `normalise_rpy_factors()` (`.cpp:1354-1388`): roll, pitch and yaw factors to maximum magnitude
0.5, throttle factors to maximum 1 and minimum 0. -/
def normalise_rpy_factors (s : State) : State := Id.run do
  let mut roll_fac : ftype := 0.0
  let mut pitch_fac : ftype := 0.0
  let mut yaw_fac : ftype := 0.0
  let mut throttle_fac : ftype := 0.0
  -- find maximum roll, pitch and yaw factors
  for i in List.finRange 4 do
    if s.motor_enabled[i] then
      roll_fac := MAX roll_fac s._roll_factor[i].abs
      pitch_fac := MAX pitch_fac s._pitch_factor[i].abs
      yaw_fac := MAX yaw_fac s._yaw_factor[i].abs
      throttle_fac := MAX throttle_fac (MAX 0.0 s._throttle_factor[i])
  -- scale factors back to -0.5 to +0.5 for each axis
  let mut s := s
  for i in List.finRange 4 do
    if s.motor_enabled[i] then
      if !is_zero roll_fac then
        s := { s with _roll_factor := s._roll_factor.set i (0.5 * s._roll_factor[i] / roll_fac) }
      if !is_zero pitch_fac then
        s := { s with _pitch_factor := s._pitch_factor.set i (0.5 * s._pitch_factor[i] / pitch_fac) }
      if !is_zero yaw_fac then
        s := { s with _yaw_factor := s._yaw_factor.set i (0.5 * s._yaw_factor[i] / yaw_fac) }
      if !is_zero throttle_fac then
        s := { s with _throttle_factor := s._throttle_factor.set i (MAX 0.0 (s._throttle_factor[i] / throttle_fac)) }
  return s

/-- `setup_motors(MOTOR_FRAME_QUAD, MOTOR_FRAME_TYPE_X)` (`.cpp:1291-1350`). -/
def setup_motors (s : State) : State := Id.run do
  let mut s := s
  -- remove existing motors
  for i in List.finRange 4 do
    s := remove_motor s i
  s := { s with _initialised_ok := false }
  let (s', success) := setup_quad_matrix s
  s := s'
  -- normalise factors to magnitude 0.5
  s := normalise_rpy_factors s
  s := { s with _initialised_ok := success }
  return s

/-- The object after construction (`AP_Motors_Class.cpp:36-60`, `AP_MotorsMulticopter.cpp:265-270`,
parameters at their stored values) and `init(MOTOR_FRAME_QUAD, MOTOR_FRAME_TYPE_X)`
(`AP_MotorsMatrix.cpp:23-41`; `set_update_rate` is not ported). Members the constructors do not
set are zero, as for ArduPilot's static objects. -/
def init (p : Params) : State :=
  let s : State := {
    -- _throttle_filter.set_cutoff_frequency(0.0f); _throttle_filter.reset(0.0f);
    _throttle_filter_cutoff := 0.0
    _throttle_filter_value := 0.0
    -- limit.set_all(true)
    limit := ({} : Limit).set_all true
    _throttle_hover := p.MOT_THST_HOVER
    _throttle_limit := 1.0 }
  setup_motors s

/-! ### Per-tick output -/

/-- `boost_ratio(boost_value, normal_value)` (`.cpp:207-210`). -/
def boost_ratio (s : State) (boost_value normal_value : ftype) : ftype :=
  s._thrust_boost_ratio * boost_value + (1.0 - s._thrust_boost_ratio) * normal_value

/-- `output_armed_stabilizing()` (`.cpp:214-405`) with `_thrust_boost` false. Writes
`_thrust_rpyt_out`, `_throttle_out` and the `limit` flags (`throttle_lower` :240,
`throttle_upper` :244, :378, :388, `yaw` :331, `roll`/`pitch`/`yaw` :376). -/
def output_armed_stabilizing (p : Params) (s : State) : State := Id.run do
  let mut s := s
  -- apply voltage and air pressure compensation
  let compensation_gain := Thrust_Linearization.get_compensation_gain s.thr_lin s.air_density_ratio
  -- roll thrust input value, +/- 1.0
  let roll_thrust := (s._roll_in + s._roll_in_ff) * compensation_gain
  -- pitch thrust input value, +/- 1.0
  let pitch_thrust := (s._pitch_in + s._pitch_in_ff) * compensation_gain
  -- yaw thrust input value, +/- 1.0
  let mut yaw_thrust := (s._yaw_in + s._yaw_in_ff) * compensation_gain
  -- throttle thrust input value, 0.0 - 1.0
  let mut throttle_thrust := get_throttle s.toInputs * compensation_gain
  -- throttle thrust average maximum value, 0.0 - 1.0
  let mut throttle_avg_max := s._throttle_avg_max * compensation_gain
  -- throttle thrust maximum value, 0.0 - 1.0, If thrust boost is active then do not limit maximum thrust
  let throttle_thrust_max := boost_ratio s 1.0 (s._throttle_thrust_max * compensation_gain)

  -- sanity check throttle is above zero and below current limited throttle
  if throttle_thrust ≤ 0.0 then
    throttle_thrust := 0.0
    s := { s with limit := { s.limit with throttle_lower := true } }
  if throttle_thrust ≥ throttle_thrust_max then
    throttle_thrust := throttle_thrust_max
    s := { s with limit := { s.limit with throttle_upper := true } }

  -- ensure that throttle_avg_max is between the input throttle and the maximum throttle
  throttle_avg_max := constrain_float throttle_avg_max throttle_thrust throttle_thrust_max

  -- throttle providing maximum roll, pitch and yaw range
  let mut throttle_thrust_best_rpy := MIN 0.5 throttle_avg_max

  -- calculate amount of yaw we can fit into the throttle range
  let mut yaw_allowed : ftype := 1.0
  let mut thrust_rpyt_out := s._thrust_rpyt_out
  for i in List.finRange 4 do
    if s.motor_enabled[i] then
      -- calculate the thrust outputs for roll and pitch
      thrust_rpyt_out := thrust_rpyt_out.set i (roll_thrust * s._roll_factor[i] + pitch_thrust * s._pitch_factor[i])
      -- Check the maximum yaw control that can be used on this channel (_thrust_boost is false)
      if !is_zero s._yaw_factor[i] then
        let thrust_rp_best_throttle := throttle_thrust_best_rpy + thrust_rpyt_out[i]
        let mut motor_room : ftype := 0.0
        if is_positive (yaw_thrust * s._yaw_factor[i]) then
          -- room to upper limit
          motor_room := 1.0 - thrust_rp_best_throttle
        else
          -- room to lower limit
          motor_room := thrust_rp_best_throttle
        let motor_yaw_allowed := MAX motor_room 0.0 / s._yaw_factor[i].abs
        yaw_allowed := MIN yaw_allowed motor_yaw_allowed

  -- calculate the maximum yaw control that can be used
  let mut yaw_allowed_min : ftype := Float32.ofInt p.MOT_YAW_HEADROOM.toInt * 0.001
  -- increase yaw headroom to 50% if thrust boost enabled
  yaw_allowed_min := boost_ratio s 0.5 yaw_allowed_min
  -- Let yaw access minimum amount of head room
  yaw_allowed := MAX yaw_allowed yaw_allowed_min

  -- :312-326 (lost motor) not taken: _thrust_boost is false

  if yaw_thrust.abs > yaw_allowed then
    -- not all commanded yaw can be used
    yaw_thrust := constrain_float yaw_thrust (-yaw_allowed) yaw_allowed
    s := { s with limit := { s.limit with yaw := true } }

  -- add yaw control to thrust outputs
  let mut rpy_low : ftype := 1.0
  let mut rpy_high : ftype := -1.0
  for i in List.finRange 4 do
    if s.motor_enabled[i] then
      thrust_rpyt_out := thrust_rpyt_out.set i (thrust_rpyt_out[i] + yaw_thrust * s._yaw_factor[i])
      -- record lowest roll + pitch + yaw command
      if thrust_rpyt_out[i] < rpy_low then
        rpy_low := thrust_rpyt_out[i]
      -- record highest roll + pitch + yaw command (_thrust_boost is false)
      if thrust_rpyt_out[i] > rpy_high then
        rpy_high := thrust_rpyt_out[i]
  -- :353-358 not taken: _thrust_boost is false

  -- calculate any scaling needed to make the combined thrust outputs fit within the output range
  let mut rpy_scale : ftype := 1.0
  if rpy_high - rpy_low > 1.0 then
    rpy_scale := 1.0 / (rpy_high - rpy_low)
  if throttle_avg_max + rpy_low < 0 then
    rpy_scale := MIN rpy_scale (-throttle_avg_max / rpy_low)

  -- calculate how close the motors can come to the desired throttle
  rpy_high := rpy_high * rpy_scale
  rpy_low := rpy_low * rpy_scale
  throttle_thrust_best_rpy := -rpy_low
  let mut thr_adj := throttle_thrust - throttle_thrust_best_rpy
  if rpy_scale < 1.0 then
    -- Full range is being used by roll, pitch, and yaw.
    s := { s with limit := s.limit.set_rpy true }
    if thr_adj > 0.0 then
      s := { s with limit := { s.limit with throttle_upper := true } }
    thr_adj := 0.0
  else if thr_adj < 0.0 then
    -- Throttle can't be reduced to desired value
    thr_adj := 0.0
  else if thr_adj > 1.0 - (throttle_thrust_best_rpy + rpy_high) then
    -- Throttle can't be increased to desired value
    thr_adj := 1.0 - (throttle_thrust_best_rpy + rpy_high)
    s := { s with limit := { s.limit with throttle_upper := true } }

  -- add scaled roll, pitch, constrained yaw and throttle for each motor
  let throttle_thrust_best_plus_adj := throttle_thrust_best_rpy + thr_adj
  for i in List.finRange 4 do
    if s.motor_enabled[i] then
      thrust_rpyt_out := thrust_rpyt_out.set i ((throttle_thrust_best_plus_adj * s._throttle_factor[i]) + (rpy_scale * thrust_rpyt_out[i]))
  s := { s with _thrust_rpyt_out := thrust_rpyt_out }

  -- determine throttle thrust for harmonic notch
  -- compensation_gain can never be zero
  s := { s with _throttle_out := throttle_thrust_best_plus_adj / compensation_gain }

  -- check_for_failed_motor (:404) not ported (header)
  return s

/-- `output_to_motors()` (`.cpp:144-184`), case `THROTTLE_UNLIMITED` (`:166-175`); returns the
state and `_actuator` (the PWM conversion `:178-183` is not ported). -/
def output_to_motors (p : Params) (s : State) : State × Vector ftype 4 := Id.run do
  let mut actuator := s._actuator
  -- set motor output based on thrust requests
  for i in List.finRange 4 do
    if s.motor_enabled[i] then
      actuator := actuator.set i (set_actuator_with_slew p s.toState actuator[i] (Thrust_Linearization.thrust_to_actuator p.toParams s.thr_lin s._thrust_rpyt_out[i]))
  return ({ s with _actuator := actuator }, actuator)

/-- `AP_MotorsMulticopter::output()` (`AP_MotorsMulticopter.cpp:273-304`) on the matrix object:
the per-tick entry. Returns the new state and the four normalized actuator values. -/
def output (p : Params) (s : State) : State × Vector ftype 4 :=
  -- update throttle filter
  let s := { s with toState := update_throttle_filter s.toState }
  -- calc filtered battery voltage and lift_max
  let s := { s with thr_lin := Thrust_Linearization.update_lift_max_from_batt_voltage p.toParams s.thr_lin }
  -- run spool logic
  let s := { s with toState := output_logic p s.toState }
  -- calculate thrust
  let s := output_armed_stabilizing p s
  -- thrust_compensation(): no callback on Copter (header)
  -- convert rpy_thrust values to actuator outputs
  let (s, actuator) := output_to_motors p s
  -- output_boost_throttle(), output_rpyt(): SRV_Channels writes only
  -- update_external_limits(): ORs the zero external_limits (header); _motor_mask_override = 0
  (s, actuator)

/-- `set_dt_s` (`AP_Motors_Class.h:259`) on the matrix object. -/
def set_dt_s (s : State) (dt_s : ftype) : State := { s with toState := AP_MotorsMulticopter.set_dt_s s.toState dt_s }

/-- `update_throttle_hover(dt)` (`AP_MotorsMulticopter.cpp:561-567`) on the matrix object. -/
def update_throttle_hover (p : Params) (s : State) (dt : ftype) : State :=
  { s with toState := AP_MotorsMulticopter.update_throttle_hover p s.toState dt }

/-- `get_thrust_rpyt_out(i)` (`.cpp:1416-1422`). -/
def get_thrust_rpyt_out (s : State) (i : Fin 4) : ftype := s._thrust_rpyt_out[i]

end AP_MotorsMatrix
