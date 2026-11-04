import AP_Motors.Interface
import AP_Motors.AP_Motors_Thrust_Linearization

/-!
# `AP_MotorsMulticopter`

Mirrors, at ArduPilot 802db19de1, `libraries/AP_Motors/AP_MotorsMulticopter.h:12-26` (defaults),
`:179-237` (parameters and members) and `AP_MotorsMulticopter.cpp`:
- `:36-262` (`var_info`, the `MOT_` parameters below) and `:265-270` (constructor);
- `:348-375` `update_throttle_filter`, `:379-396` `get_current_limit_max_throttle` (reduced),
  `:484-511` `set_actuator_with_slew`, `:561-567` `update_throttle_hover`;
- `:595-631` and `:809-842` `output_logic`, reduced to the `THROTTLE_UNLIMITED` case;
- `AP_Motors_Class.h:259`, `:380` (`set_dt_s`, `_dt_s`), `AP_Motors_Class.cpp:36-60`
  (constructor: throttle filter cutoff 0 and output 0, `limit.set_all(true)`);
- `Filter/LowPassFilter.cpp:24-31`, `:119-122` (`LowPassFilter<float>::apply`), the throttle filter.

`get_throttle_hover`, `get_throttle`, `get_throttle_out`, `get_throttle_thrust_max` and
`set_throttle_avg_max` are in `AP_Motors.Interface` and act on `s.toInputs`.

Assumptions of the whole `AP_Motors` port (environment, not parameters): `armed()` and
`get_interlock()` are true; `_spool_state = _spool_desired = THROTTLE_UNLIMITED`; `_thrust_boost`
is false (Copter sets it only on detected thrust loss); no thrust compensation callback (tiltrotors
only); scripting never calls `set_external_limits`, so `external_limits` stays zero and
`update_external_limits` (`.cpp:307-317`) ORs in `false`.

Left out, with the reason:
- `output_logic` cases `SHUT_DOWN`, `GROUND_IDLE`, `SPOOLING_UP`, `SPOOLING_DOWN` (`.cpp:636-808`,
  `:844-886`) and the disarm/interlock override (`:622-625`): the spool state machine, out of scope
  by the assumption above. `set_desired_spool_state`, `output_min` likewise;
- the disarmed branch of `update_throttle_filter` (`.cpp:361-364`): `armed()` is true;
- `_throttle_slew`, `_throttle_slew_filter`, `_throttle_slew_rate` (`.cpp:366-374`): a 7-point
  derivative filter on `AP_HAL::micros()` timestamps. Its only flight consumer,
  `AC_AttitudeControl_Multi::update_throttle_gain_boost` (`AC_AttitudeControl_Multi.cpp:419-424`),
  multiplies gains by 1 at the default `ATC_THR_G_BOOST = 0`;
- the battery-current path of `get_current_limit_max_throttle` (`.cpp:398-433`): the port is the
  early exit `:391-396`, which `MOT_BAT_CURR_MAX ≤ 0` (the default) selects; `Faithful` states it;
- `actuator_spin_up_to_ground_idle` (`.cpp:515-518`): only reached in `GROUND_IDLE`;
- `output_to_pwm`, `MOT_PWM_MIN/MAX/TYPE`, `update_throttle_range`, `rc_write`,
  `output_boost_throttle`, `output_rpyt` (`SRV_Channels` writes only), ESC calibration, motor mask,
  `get_thrust`, `get_raw_motor_throttle`, arming checks, `save_params_on_disarm`, logging,
  `AP_Param` (`MOT_BOOST_SCALE`, `MOT_YAW_SV_ANGLE`, `MOT_SPOOL_TIM_DN`, `MOT_IDLE_SEC`,
  `MOT_OPTIONS`, `MOT_BAT_IDX`, `MOT_BAT_CURR_TC` are not read on this path).

`MOT_SLEW_UP_TIME`/`MOT_SLEW_DN_TIME` are ported: `set_actuator_with_slew` is the full C++ (with
both times 0 it is `constrain_float(input, 0, 1)`).
-/

namespace AP_MotorsMulticopter

open AP_Math AP_Motors

/-- `AP_MOTORS_THST_HOVER_TC` (`AP_MotorsMulticopter.h:15`). -/
def AP_MOTORS_THST_HOVER_TC : ftype := 10.0
/-- `AP_MOTORS_THST_HOVER_MIN` (`.h:16`). -/
def AP_MOTORS_THST_HOVER_MIN : ftype := 0.125
/-- `AP_MOTORS_THST_HOVER_MAX` (`.h:17`). -/
def AP_MOTORS_THST_HOVER_MAX : ftype := 0.6875

/-- `enum HoverLearn` (`.h:179-183`). -/
def HOVER_LEARN_DISABLED : Int8 := 0
def HOVER_LEARN_ONLY : Int8 := 1
def HOVER_LEARN_AND_SAVE : Int8 := 2

/-- The `MOT_` parameters read on the armed, `THROTTLE_UNLIMITED` path, with the code defaults
(`AP_MotorsMulticopter.cpp:48-234`, `.h:12-29`). The `Thrust_Linearization` ones
(`MOT_THST_EXPO`, `MOT_SPIN_MIN`, `MOT_SPIN_MAX`, `MOT_BAT_VOLT_MAX`, `MOT_BAT_VOLT_MIN`) come from
the parent structure. -/
structure Params extends Thrust_Linearization.Params where
  /-- `_yaw_headroom`, `AP_Int16` (`.cpp:48`, default `.h:12`). -/
  MOT_YAW_HEADROOM : Int16 := 200
  /-- `_batt_current_max` (`.cpp:92`, default `.h:23`). -/
  MOT_BAT_CURR_MAX : ftype := 0.0
  /-- `_spin_arm` (`.cpp:138`, default `.h:20`). Read only in `GROUND_IDLE`; unused here. -/
  MOT_SPIN_ARM : ftype := 0.10
  /-- Initial `_throttle_hover` (`.cpp:154`, default `.h:14`). The learned value lives in the
  state (`Inputs._throttle_hover`), since `update_throttle_hover` writes the parameter. -/
  MOT_THST_HOVER : ftype := 0.35
  /-- `_throttle_hover_learn`, `AP_Int8` (`.cpp:163`, default `HOVER_LEARN_AND_SAVE`). -/
  MOT_HOVER_LEARN : Int8 := 2
  /-- `_disarm_disable_pwm`, `AP_Int8` (`.cpp:170`). -/
  MOT_SAFE_DISARM : Int8 := 0
  /-- `_spool_up_time` (`.cpp:188`, default `.h:29`). -/
  MOT_SPOOL_TIME : ftype := 0.5
  /-- `_slew_up_time` (`.cpp:216`, default `.h:25`). -/
  MOT_SLEW_UP_TIME : ftype := 0.0
  /-- `_slew_dn_time` (`.cpp:225`, default `.h:25`). -/
  MOT_SLEW_DN_TIME : ftype := 0.0
  /-- `_safe_time` (`.cpp:234`, default `.h:26`). -/
  MOT_SAFE_TIME : ftype := 1.0
  deriving Repr

/-- The configuration under which the reduced functions equal the C++ (battery voltage and
current limiting off, the code defaults). -/
structure Faithful (p : Params) : Prop where
  thr_lin : Thrust_Linearization.Faithful p.toParams
  bat_curr_max_off : p.MOT_BAT_CURR_MAX ≤ 0

/-- The members of `AP_Motors` and `AP_MotorsMulticopter` used on this path beyond the
controller-facing `Inputs`. Quad X uses motor slots 0-3; slots 4-11 of the C++ arrays
(`AP_MOTORS_MAX_NUM_MOTORS = 12`) stay disabled and every loop skips them, so they are not stored. -/
structure State extends AP_Motors.Inputs where
  /-- `_dt_s` (`AP_Motors_Class.h:380`), set by `set_dt_s` from `Copter::run_rate_controller_main`
  (`Attitude.cpp:18`) before the rate controller. -/
  _dt_s : ftype := 0.0
  /-- Not a member: `AP::ahrs().get_air_density_ratio()`, read by
  `Thrust_Linearization::get_compensation_gain`. The caller writes it each tick. -/
  air_density_ratio : ftype := 1.0
  /-- `_initialised_ok` (`AP_Motors_Class.h:469`). -/
  _initialised_ok : Bool := false
  /-- `_thrust_boost_ratio` (`AP_Motors_Class.h:439`); stays 0 while `_thrust_boost` is false. -/
  _thrust_boost_ratio : ftype := 0.0
  /-- `_spin_up_ratio` (`.h:214`). -/
  _spin_up_ratio : ftype := 0.0
  /-- `_throttle_limit` (`.h:219`), 1.0 from the constructor (`.cpp:267`). -/
  _throttle_limit : ftype := 1.0
  /-- `_disarm_safe_timer` (`.h:221`). -/
  _disarm_safe_timer : ftype := 0.0
  /-- `motor_enabled` (`.h:211`), slots 0-3. -/
  motor_enabled : Vector Bool 4 := #v[false, false, false, false]
  /-- `_actuator` (`.h:227`), slots 0-3: the normalized actuator outputs in [0, 1]. -/
  _actuator : Vector ftype 4 := #v[0.0, 0.0, 0.0, 0.0]
  /-- `thr_lin` (`.h:117`). -/
  thr_lin : Thrust_Linearization.State := {}
  deriving Repr

/-- `set_dt_s` (`AP_Motors_Class.h:259`). -/
def set_dt_s (s : State) (dt_s : ftype) : State := { s with _dt_s := dt_s }

/-- `LowPassFilter<float>::apply(sample, dt)` (`LowPassFilter.cpp:119-122`) on the filter output
`output` with cutoff `cutoff_freq`, through `DigitalLPF::_apply` (`:24-31`). The `initialised`
flag is true: the `AP_Motors` constructor resets `_throttle_filter` (`AP_Motors_Class.cpp:48`) and
nothing calls the argument-less `reset()` on it. -/
def LowPassFilterFloat_apply (output cutoff_freq sample dt : ftype) : ftype :=
  let alpha := calc_lowpass_alpha_dt dt cutoff_freq
  output + (sample - output) * alpha

/-- `update_throttle_filter()` (`AP_MotorsMulticopter.cpp:348-375`), armed branch. The filter is
`Inputs._throttle_filter_value` with cutoff `Inputs._throttle_filter_cutoff`. -/
def update_throttle_filter (s : State) : State := Id.run do
  let mut s := s
  -- armed() is true (header); the disarmed reset at :361-364 is not ported
  s := { s with _throttle_filter_value := LowPassFilterFloat_apply s._throttle_filter_value s._throttle_filter_cutoff s._throttle_in s._dt_s }
  -- constrain filtered throttle
  if s._throttle_filter_value < 0.0 then
    s := { s with _throttle_filter_value := 0.0 }
  if s._throttle_filter_value > 1.0 then
    s := { s with _throttle_filter_value := 1.0 }
  -- :366-374, the throttle slew-rate detector, is not ported (header)
  return s

/-- `get_current_limit_max_throttle()` (`.cpp:379-438`), the early exit at `:391-396`
(`_throttle_limit = 1.0f; return 1.0f;`). Under `Faithful` (`MOT_BAT_CURR_MAX ≤ 0`) the C++ takes
it on every call; for `MOT_BAT_CURR_MAX > 0` this function is not the C++. -/
def get_current_limit_max_throttle (_p : Params) (s : State) : State × ftype :=
  ({ s with _throttle_limit := 1.0 }, 1.0)

/-- `output_logic()` (`.cpp:595-888`) when armed, interlocked and in `THROTTLE_UNLIMITED` with
`_spool_desired = THROTTLE_UNLIMITED` and `_thrust_boost` false (`:601-631`, then `:809-842`). -/
def output_logic (p : Params) (s : State) : State := Id.run do
  let minimum_spool_time : ftype := 0.05
  let mut s := s
  -- disarm-pwm safety window, armed() branch (:608-613)
  if p.MOT_SAFE_DISARM != 0 && s._disarm_safe_timer < p.MOT_SAFE_TIME then
    s := { s with _disarm_safe_timer := s._disarm_safe_timer + s._dt_s }
  else
    s := { s with _disarm_safe_timer := p.MOT_SAFE_TIME }
  -- :622-625 not taken (armed and interlocked)
  -- :627-631 writes the parameter back; here the effective value is recomputed each call
  let _spool_up_time := if p.MOT_SPOOL_TIME < minimum_spool_time then minimum_spool_time else p.MOT_SPOOL_TIME
  -- case SpoolState::THROTTLE_UNLIMITED (:809-842)
  let spool_step := s._dt_s / _spool_up_time
  s := { s with limit := s.limit.set_all false }
  -- :823-826 not taken (_spool_desired == THROTTLE_UNLIMITED)
  s := { s with _spin_up_ratio := 1.0 }
  let (s', throttle_max) := get_current_limit_max_throttle p s
  s := { s' with _throttle_thrust_max := throttle_max }
  -- _thrust_boost is false: the else branch of :836-840
  s := { s with _thrust_boost_ratio := MAX 0.0 (s._thrust_boost_ratio - spool_step) }
  return s

/-- `set_actuator_with_slew(actuator_output, input)` (`.cpp:484-511`): returns the new value of
`actuator_output`. -/
def set_actuator_with_slew (p : Params) (s : State) (actuator_output input : ftype) : ftype := Id.run do
  -- Output limits with no slew time applied
  let mut output_slew_limit_up : ftype := 1.0
  let mut output_slew_limit_dn : ftype := 0.0
  -- If MOT_SLEW_UP_TIME is set, calculate the highest allowed new output value, constrained 0.0~1.0
  if is_positive p.MOT_SLEW_UP_TIME then
    let output_delta_up_max := s._dt_s / (constrain_float p.MOT_SLEW_UP_TIME 0.0 0.5)
    output_slew_limit_up := constrain_float (actuator_output + output_delta_up_max) 0.0 1.0
  -- If MOT_SLEW_DN_TIME is set, calculate the lowest allowed new output value, constrained 0.0~1.0
  if is_positive p.MOT_SLEW_DN_TIME then
    let output_delta_dn_max := s._dt_s / (constrain_float p.MOT_SLEW_DN_TIME 0.0 0.5)
    output_slew_limit_dn := constrain_float (actuator_output - output_delta_dn_max) 0.0 1.0
  -- Constrain change in output to within the above limits
  return constrain_float input output_slew_limit_dn output_slew_limit_up

/-- `update_throttle_hover(dt)` (`.cpp:561-567`), called by `Copter::update_throttle_hover` at
100 Hz (`Attitude.cpp:62`, `dt = 0.01`). -/
def update_throttle_hover (p : Params) (s : State) (dt : ftype) : State :=
  if p.MOT_HOVER_LEARN != HOVER_LEARN_DISABLED then
    -- we have chosen to constrain the hover throttle to be within the range reachable by the third order expo polynomial.
    { s with _throttle_hover := constrain_float (s._throttle_hover + (dt / (dt + AP_MOTORS_THST_HOVER_TC)) * (get_throttle s.toInputs - s._throttle_hover)) AP_MOTORS_THST_HOVER_MIN AP_MOTORS_THST_HOVER_MAX }
  else
    s

end AP_MotorsMulticopter
