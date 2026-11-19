import Harness.Module

/-! # mixer: ArduCopter's quad-X motor mixer

One `AP_MotorsMatrix` (libraries/AP_Motors, with its base classes `AP_MotorsMulticopter` and
`AP_Motors` and its `Thrust_Linearization`), set up as ArduCopter sets it up for a quad X
(Copter::allocate_motors, Copter::init_rc_out, the `output_min()` at the end of
init_ardupilot), and stepped by `AP_MotorsMulticopter::output()` as Copter::motors_output calls it,
after the rate controller's `set_roll/pitch/yaw(_ff)`, the attitude controller's
`set_throttle_out` and the flight mode's `set_desired_spool_state`. The executable is built by
`ardupilot/build.sh mixer` from the real, unmodified ArduPilot sources listed in sources.txt; see
adapter.cpp for the cut and stubs.cpp for what is outside.

Parameters fixed instead of exposed (adapter.cpp says where each is set):
MOT_PWM_TYPE = 0 (normal PWM), MOT_BAT_IDX = 0, MOT_HOVER_LEARN = 2 (Copter's default; only
reached on disarm, through the hover-throttle save), MOT_BOOST_SCALE = 0 (no booster motor),
MOT_OPTIONS = 0 (resting-voltage estimate, not raw voltage), MOT_YAW_SV_ANGLE = 30 (tricopter
only), SCHED_LOOP_RATE = 400 Hz (constructor), RC_SPEED = 490 Hz, SERVO_DSHOT_ESC = 0, no
digital (DShot) outputs, SERVOn_FUNCTION = Motor n for n = 1..4, frame QUAD / X. -/

namespace Ardupilot.Modules.Mixer

open Harness Harness.Contract.Lang

def params : Schema := #[
  { name := "spin_min", type := .f32, doc := "MOT_SPIN_MIN (thr_lin.spin_min)" },
  { name := "spin_max", type := .f32, doc := "MOT_SPIN_MAX (thr_lin.spin_max)" },
  { name := "spin_arm", type := .f32, doc := "MOT_SPIN_ARM (_spin_arm)" },
  { name := "thst_expo", type := .f32, doc := "MOT_THST_EXPO (thr_lin.curve_expo)" },
  { name := "thst_hover", type := .f32, doc := "MOT_THST_HOVER (_throttle_hover)" },
  { name := "yaw_headroom", type := .i32, doc := "MOT_YAW_HEADROOM, PWM units (_yaw_headroom, int16)" },
  { name := "pwm_min", type := .i32, doc := "MOT_PWM_MIN (_pwm_min, int16)" },
  { name := "pwm_max", type := .i32, doc := "MOT_PWM_MAX (_pwm_max, int16)" },
  { name := "bat_volt_max", type := .f32, doc := "MOT_BAT_VOLT_MAX, 0 disables voltage compensation" },
  { name := "bat_volt_min", type := .f32, doc := "MOT_BAT_VOLT_MIN" },
  { name := "bat_curr_max", type := .f32, doc := "MOT_BAT_CURR_MAX, 0 disables current limiting" },
  { name := "bat_curr_tc", type := .f32, doc := "MOT_BAT_CURR_TC, s" },
  { name := "spool_time", type := .f32, doc := "MOT_SPOOL_TIME, s (_spool_up_time)" },
  { name := "spool_tim_dn", type := .f32, doc := "MOT_SPOOL_TIM_DN, s, 0 uses spool_time" },
  { name := "slew_up_time", type := .f32, doc := "MOT_SLEW_UP_TIME, s, 0 disables" },
  { name := "slew_dn_time", type := .f32, doc := "MOT_SLEW_DN_TIME, s, 0 disables" },
  { name := "safe_disarm", type := .bool, doc := "MOT_SAFE_DISARM: PWM off while disarmed" },
  { name := "safe_time", type := .f32, doc := "MOT_SAFE_TIME, s" },
  { name := "idle_sec", type := .f32, doc := "MOT_IDLE_SEC, s" },
  { name := "hover_learn", type := .i32,
    doc := "MOT_HOVER_LEARN: 0 disabled, 1 learn, 2 learn and save (_throttle_hover_learn; was \
      fixed at 2 before the composition)" }]

def input : Schema := #[
  { name := "roll", type := .f32, doc := "set_roll: rate controller's roll output" },
  { name := "pitch", type := .f32, doc := "set_pitch" },
  { name := "yaw", type := .f32, doc := "set_yaw" },
  { name := "roll_ff", type := .f32, doc := "set_roll_ff: roll PID feed-forward" },
  { name := "pitch_ff", type := .f32, doc := "set_pitch_ff" },
  { name := "yaw_ff", type := .f32, doc := "set_yaw_ff" },
  { name := "throttle", type := .f32, doc := "set_throttle (attitude controller's set_throttle_out)" },
  { name := "throttle_avg_max", type := .f32, doc := "set_throttle_avg_max (constrained to [0,1] by the setter)" },
  { name := "throttle_filter_hz", type := .f32, doc := "set_throttle_filter_cutoff, Hz" },
  { name := "dt", type := .f32, doc := "set_dt_s: last loop time, s" },
  { name := "armed", type := .bool, doc := "armed(): the arming library's decision" },
  { name := "interlock", type := .bool, doc := "set_interlock (Copter::motors_output)" },
  { name := "spool_desired", type := .u32, doc := "set_desired_spool_state: 0 shut down, 1 ground idle, 2 throttle unlimited" },
  { name := "clear_spoolup_block", type := .bool, doc := "Copter::takeoff_check clears the spool-up block (set_spoolup_block(false))" },
  { name := "now_us", type := .u32, doc := "the clock AP_HAL::micros() reads (throttle slew detector)" },
  { name := "batt_voltage", type := .f32, doc := "AP_BattMonitor::voltage(0), V" },
  { name := "batt_resting_voltage", type := .f32, doc := "AP_BattMonitor::voltage_resting_estimate(0), V" },
  { name := "batt_current", type := .f32, doc := "AP_BattMonitor::current_amps(0), A" },
  { name := "batt_current_ok", type := .bool, doc := "current_amps(0) returned true (current monitoring available)" },
  { name := "batt_resistance", type := .f32, doc := "AP_BattMonitor::get_resistance(0), ohm" },
  { name := "air_density_ratio", type := .f32, doc := "AP_AHRS::get_air_density_ratio() (1/EAS2TAS^2, from the barometer)" },
  { name := "cmd_mixer_output_min", type := .bool,
    doc := "output_min() is called (AP_Arming_Copter::arm, AP_Arming_Copter.cpp:756; failsafe.cpp:58), \
      before this step's calls: the supervisor's call of the previous tick, made after that \
      tick's motors_output" },
  { name := "cmd_mixer_set_thrust_boost", type := .bool,
    doc := "set_thrust_boost(enable) is called (crash_check.cpp:172), before this step's output()" },
  { name := "cmd_mixer_set_thrust_boost_enable", type := .bool, doc := "its argument" },
  { name := "cmd_mixer_update_throttle_hover", type := .bool,
    doc := "update_throttle_hover(dt) is called (Copter::update_throttle_hover, Attitude.cpp:62, \
      100 Hz, after the fast loop): made at the start of this step, i.e. after the previous \
      tick's output(), whose get_throttle() it reads" },
  { name := "cmd_mixer_update_throttle_hover_dt", type := .f32, doc := "its dt argument, s" }]

def output : Schema := #[
  { name := "actuator_1", type := .f32, doc := "_actuator[0]: normalized motor command after linearization and slew" },
  { name := "actuator_2", type := .f32, doc := "_actuator[1]" },
  { name := "actuator_3", type := .f32, doc := "_actuator[2]" },
  { name := "actuator_4", type := .f32, doc := "_actuator[3]" },
  { name := "pwm_1", type := .u32, doc := "PWM written for motor 1 (SRV_Channels::set_output_pwm(k_motor1, .))" },
  { name := "pwm_2", type := .u32, doc := "PWM written for motor 2" },
  { name := "pwm_3", type := .u32, doc := "PWM written for motor 3" },
  { name := "pwm_4", type := .u32, doc := "PWM written for motor 4" },
  { name := "pwm_writes", type := .u32, doc := "motor PWM writes during the step" },
  { name := "thrust_1", type := .f32, doc := "_thrust_rpyt_out[0]: mixed thrust before linearization, 0..1" },
  { name := "thrust_2", type := .f32, doc := "_thrust_rpyt_out[1]" },
  { name := "thrust_3", type := .f32, doc := "_thrust_rpyt_out[2]" },
  { name := "thrust_4", type := .f32, doc := "_thrust_rpyt_out[3]" },
  { name := "limit_roll", type := .bool, doc := "limit.roll" },
  { name := "limit_pitch", type := .bool, doc := "limit.pitch" },
  { name := "limit_yaw", type := .bool, doc := "limit.yaw" },
  { name := "limit_throttle_lower", type := .bool, doc := "limit.throttle_lower" },
  { name := "limit_throttle_upper", type := .bool, doc := "limit.throttle_upper" },
  { name := "spool_state", type := .u32, doc := "get_spool_state(): 0 shut down, 1 ground idle, 2 spooling up, 3 throttle unlimited, 4 spooling down" },
  { name := "spoolup_block", type := .bool, doc := "get_spoolup_block()" },
  { name := "throttle_filtered", type := .f32, doc := "get_throttle(): the filtered throttle the mixer used" },
  { name := "throttle_out", type := .f32, doc := "get_throttle_out(): throttle after mixing" },
  { name := "throttle_thrust_max", type := .f32, doc := "get_throttle_thrust_max(): the spool/current-limit ceiling" },
  { name := "throttle_slew_rate", type := .f32, doc := "get_throttle_slew_rate() (read by the attitude controller)" },
  { name := "lift_max", type := .f32, doc := "thr_lin.get_lift_max(): battery-voltage lift ratio" },
  { name := "compensation_gain", type := .f32, doc := "thr_lin.get_compensation_gain(): voltage and air-density gain" },
  { name := "internal_errors", type := .u32, doc := "ArduPilot internal errors raised since init" },
  { name := "throttle_hover", type := .f32,
    doc := "get_throttle_hover(): MOT_THST_HOVER as learned, constrained to [0.125, 0.6875] (read \
      by the position and attitude stages; a composite input before hover learning was added)" },
  { name := "thrust_boost", type := .bool, doc := "get_thrust_boost()" }]

/-! ### Clause builders -/

/-- `f i` for the four motors, joined by `∧`. -/
def all4 (f : String → Expr) : Expr :=
  f "1" ∧. f "2" ∧. f "3" ∧. f "4"

def act (i : String) : Expr := .var s!"actuator_{i}"
def pwm (i : String) : Expr := .var s!"pwm_{i}"
def thr (i : String) : Expr := .var s!"thrust_{i}"

/-- Assumption clauses on the inputs, as first stated (and in the second statement). -/
def assumeInputsAsFirstStated : List Clause := [
  ⟨"commands_range", abs "roll" ≤. 1 ∧. abs "pitch" ≤. 1 ∧. abs "yaw" ≤. 1⟩,
  ⟨"ff_range", abs "roll_ff" ≤. 1 ∧. abs "pitch_ff" ≤. 1 ∧. abs "yaw_ff" ≤. 1⟩,
  ⟨"throttle_range", 0 ≤. "throttle" ∧. "throttle" ≤. 1 ∧. 0 ≤. "throttle_avg_max" ∧.
      "throttle_avg_max" ≤. 1⟩,
  ⟨"throttle_filter_range", 0 ≤. "throttle_filter_hz" ∧. "throttle_filter_hz" ≤. 100⟩,
  ⟨"dt_range", 0 <. "dt" ∧. "dt" ≤. 0.02⟩,
  ⟨"spool_desired_range", "spool_desired" ≤. 2⟩,
  ⟨"air_density_range", 0 ≤. "air_density_ratio" ∧. "air_density_ratio" ≤. 2⟩]

/-- Battery readings, as first stated: bounded and non-negative. -/
def assumeBatteryAsFirstStated : Clause :=
  ⟨"battery_range", 0 ≤. "batt_voltage" ∧. "batt_voltage" ≤. 60 ∧.
      0 ≤. "batt_resting_voltage" ∧. "batt_resting_voltage" ≤. 60 ∧.
      0 ≤. "batt_current" ∧. "batt_current" ≤. 500 ∧.
      0 ≤. "batt_resistance" ∧. "batt_resistance" ≤. 1⟩

/-- The MOT_* parameter ranges ArduPilot documents (@Range in AP_MotorsMulticopter.cpp), with 0
admitted for MOT_BAT_VOLT_MAX/MIN (their default, which disables voltage compensation). No
relation between parameters is assumed. -/
def assumeParamsDocumented : List Clause := [
  ⟨"spin_min_range", 0 ≤. "spin_min" ∧. "spin_min" ≤. 0.25⟩,
  ⟨"spin_max_range", 0.9 ≤. "spin_max" ∧. "spin_max" ≤. 1⟩,
  ⟨"spin_arm_range", 0 ≤. "spin_arm" ∧. "spin_arm" ≤. 0.2⟩,
  ⟨"thst_expo_range", -1 ≤. "thst_expo" ∧. "thst_expo" ≤. 1⟩,
  ⟨"thst_hover_range", 0.125 ≤. "thst_hover" ∧. "thst_hover" ≤. 0.6875⟩,
  ⟨"yaw_headroom_range", 0 ≤. "yaw_headroom" ∧. "yaw_headroom" ≤. 500⟩,
  ⟨"pwm_min_range", 0 ≤. "pwm_min" ∧. "pwm_min" ≤. 2000⟩,
  ⟨"pwm_max_range", 0 ≤. "pwm_max" ∧. "pwm_max" ≤. 2000⟩,
  ⟨"bat_volt_max_range", "bat_volt_max" =. 0 ∨. (6 ≤. "bat_volt_max" ∧. "bat_volt_max" ≤. 53)⟩,
  ⟨"bat_volt_min_range", "bat_volt_min" =. 0 ∨. (6 ≤. "bat_volt_min" ∧. "bat_volt_min" ≤. 42)⟩,
  ⟨"bat_curr_max_range", 0 ≤. "bat_curr_max" ∧. "bat_curr_max" ≤. 200⟩,
  ⟨"bat_curr_tc_range", 0 ≤. "bat_curr_tc" ∧. "bat_curr_tc" ≤. 10⟩,
  ⟨"spool_time_range", 0.05 ≤. "spool_time" ∧. "spool_time" ≤. 2⟩,
  ⟨"spool_tim_dn_range", 0 ≤. "spool_tim_dn" ∧. "spool_tim_dn" ≤. 2⟩,
  ⟨"slew_range", 0 ≤. "slew_up_time" ∧. "slew_up_time" ≤. 0.5 ∧. 0 ≤. "slew_dn_time" ∧.
      "slew_dn_time" ≤. 0.5⟩,
  ⟨"safe_time_range", 0 ≤. "safe_time" ∧. "safe_time" ≤. 5⟩,
  ⟨"idle_sec_range", 0 ≤. "idle_sec" ∧. "idle_sec" ≤. 5⟩]

/-- The guarantee. The tolerance 1e-5 on the relational clauses covers binary32 rounding of the
mix (each thrust is at most 1, a handful of roundings each). The relational clauses are
implications `flag ∨ atom`; their margin is the atom's even where the flag makes the clause hold,
so the smallest margin a campaign reports for them can be negative without a violation. The step
does not update the hover throttle (Copter::update_throttle_hover does, outside output()), so it
is not an output. -/
def guarantee : List Clause := [
  ⟨"actuators_in_range", all4 fun i => 0 ≤. act i ∧. act i ≤. 1⟩,
  ⟨"pwm_in_range", all4 (fun i => "pwm_min" ≤. pwm i ∧. pwm i ≤. "pwm_max") ∨.
      ("safe_disarm" ∧. ¬. "armed" ∧. all4 fun i => pwm i =. 0)⟩,
  ⟨"every_motor_written", "pwm_writes" =. 4⟩,
  -- the mixed thrusts are in [0, 1] up to binary32 rounding of the rpy scaling (see
  -- guaranteeAsFirstStated); thrust_to_actuator constrains them to [0, 1] before use
  ⟨"thrusts_in_range", all4 fun i => -1e-6 ≤. thr i ∧. thr i ≤. 1 + 1e-6⟩,
  ⟨"signals_finite", finite "throttle_out" ∧. 0 ≤. "throttle_out" ∧.
      finite "throttle_slew_rate" ∧. 0 ≤. "throttle_slew_rate" ∧.
      0 ≤. "throttle_thrust_max" ∧. "throttle_thrust_max" ≤. 1⟩,
  -- output_logic forces SHUT_DOWN when disarmed or without interlock; output_to_motors then
  -- writes 0 to every actuator
  ⟨"stopped_unless_armed", ("armed" ∧. "interlock") ∨.
      ("spool_state" =. 0 ∧. all4 fun i => act i =. 0)⟩,
  -- quad X: roll factors (-½, ½, ½, -½), pitch (½, -½, ½, -½), yaw (½, ½, -½, -½) after
  -- normalise_rpy_factors, throttle factors 1. Each torque the mix produces equals the commanded
  -- one unless its limit flag is set (rpy scaling sets all three, yaw clipping sets limit.yaw):
  -- half the differential of the four thrusts is (cmd + ff) * compensation_gain.
  ⟨"roll_realized", "limit_roll" ∨.
      abs (0.5 * (thr "2" + thr "3" - thr "1" - thr "4") -
        ("roll" + "roll_ff") * "compensation_gain") ≤. 1e-5⟩,
  ⟨"pitch_realized", "limit_pitch" ∨.
      abs (0.5 * (thr "1" + thr "3" - thr "2" - thr "4") -
        ("pitch" + "pitch_ff") * "compensation_gain") ≤. 1e-5⟩,
  ⟨"yaw_realized", "limit_yaw" ∨.
      abs (0.5 * (thr "1" + thr "2" - thr "3" - thr "4") -
        ("yaw" + "yaw_ff") * "compensation_gain") ≤. 1e-5⟩,
  -- the mix never gives less collective thrust than demanded without saying so: the throttle
  -- is only lowered (thr_adj clipped, rpy scaling, the ceiling) together with limit.throttle_upper
  ⟨"collective_not_below_demand", "limit_throttle_upper" ∨.
      "throttle_filtered" * "compensation_gain" - 1e-5 ≤.
        0.25 * (thr "1" + thr "2" + thr "3" + thr "4")⟩,
  ⟨"no_internal_error", "internal_errors" =. 0⟩]

/-- The guarantee as first stated: `thrusts_in_range` exact. A flight-state scenario refuted it
(ardupilot/modules/mixer/thrust-rounding-case.json): with roll, pitch and yaw saturating, rpy_scale =
1 / (rpy_high - rpy_low) and the sum `throttle_thrust_best_plus_adj + rpy_scale * thrust`
round to 1.0000001 for one motor (and can as well round just below 0). -/
def guaranteeAsFirstStated : List Clause :=
  guarantee.map fun c => if c.name == "thrusts_in_range" then
    ⟨"thrusts_in_range", all4 fun i => 0 ≤. thr i ∧. thr i ≤. 1⟩ else c

/-- The contract as first stated: finite, bounded inputs and ArduPilot's documented parameter
ranges, each parameter on its own. Refuted; kept for the record, not used. -/
def contractAsFirstStated : Contract where
  assume := assumeInputsAsFirstStated ++ [assumeBatteryAsFirstStated] ++ assumeParamsDocumented
  guarantee := guaranteeAsFirstStated

/-- The second statement. Against the first statement, two assumption clauses are added; the
guarantee is unchanged.
* `pwm_valid`: the documented ranges let MOT_PWM_MIN exceed MOT_PWM_MAX, and then no PWM lies in
  [pwm_min, pwm_max] (output_to_pwm writes pwm_min while shut down). The clause is ArduPilot's own
  arming check, AP_MotorsMulticopter::check_mot_pwm_params (1 ≤ pwm_min < pwm_max).
* `current_positive`: with current limiting on (MOT_BAT_CURR_MAX > 0), a measured current of 0 A
  while the battery reads exactly MOT_BAT_VOLT_MIN makes get_current_limit_max_throttle compute
  `batt_current_max = MIN(MOT_BAT_CURR_MAX, 0 + 0 / R) = 0` and `0 / 0`; the NaN reaches
  `constrain_float(_throttle_limit, 0.2, 1)`, which raises an internal error on every step and
  returns 0.6, so the throttle ceiling silently becomes hover + 0.6 (1 - hover). Found by a
  scenario (ardupilot/modules/mixer/zero-current-case.json), not by the campaign, which seldom reaches the
  spooled-up states where the current limit is read. A positive current excludes it except
  when `I + (V - V_min) / R` cancels to exactly 0 and dt is so small that `dt / (dt + tc)` is 0;
  that corner is not excluded.

Refuted by the `flight` regime (seed 1, 300 x 100: no_internal_error at 67 steps; first
counterexample ardupilot/modules/mixer/current-limit-nan-case.json, case 140 step 33): MOT_BAT_CURR_MAX =
1.4e-45 (subnormal, > 0, so current limiting is on) gives `batt_current_max` = 1.4e-45 and
`batt_current_ratio = 1 A / 1.4e-45` = +∞; dt = 1.4e-45 makes `_dt_s / (_dt_s + tc)` round to 0;
`0 * (1 - ∞)` is NaN in `_throttle_limit` (AP_MotorsMulticopter.cpp:423), and
`constrain_float(_throttle_limit, 0.2, 1)` (:427) raises the internal error. Its
`commands_range` (|roll|, |pitch|, |yaw| ≤ 1) is also narrower than what ArduCopter feeds the
mixer: with ATC_RAT_*_PDMX = 0 (the default) nothing bounds the rate commands by 1. Kept for the
record, not used. -/
def contractSecond : Contract where
  assume := assumeInputsAsFirstStated ++ [assumeBatteryAsFirstStated,
      ⟨"current_positive", "bat_curr_max" =. 0 ∨. ¬. "batt_current_ok" ∨. 0 <. "batt_current"⟩] ++
    assumeParamsDocumented ++
    [⟨"pwm_valid", 1 ≤. "pwm_min" ∧. "pwm_min" <. "pwm_max"⟩]
  guarantee := guarantee

/-- Assumption clauses on the inputs, against the second statement:
* `commands_bounded`: the rate commands bounded by 1e16, not by 1. AP_Motors_Class.h documents
  set_roll/pitch/yaw as "range -1 ~ +1", but AC_AttitudeControl_Multi::rate_controller_run_dt
  passes update_all's result unclamped, and with ATC_RAT_*_PDMX = 0 (the default) nothing bounds
  it by 1; output_armed_stabilizing scales the roll/pitch/yaw thrusts into the available range and
  sets the limit flags. Tested (200 x 100, seeds 2 and 5, with and without `flight`): with
  |command| ≤ 1e4 and with |command| ≤ 1e16 every guarantee clause holds. With only finite
  commands, `thrusts_in_range`, `signals_finite`, `collective_not_below_demand` and
  `no_internal_error` fail (ardupilot/modules/mixer/command-overflow-case.json, roll = -3.4e38):
  `roll_thrust = (_roll_in + _roll_in_ff) * compensation_gain` (AP_MotorsMatrix.cpp:220)
  overflows to ±∞ and `roll_thrust * _roll_factor[i] + pitch_thrust * _pitch_factor[i]` (:281)
  is ∞ - ∞ = NaN. The mix stays finite while the three thrusts, times the gain (≤ 2.6) and
  factors (½), sum below FLT_MAX, so about 1e37 would do; 1e16 is the bound used, large enough
  for rate's guarantee `*_command_magnitude` (|command| ≤ 3.5e15 + kimax) when kimax ≤ 1.
* `dt_range`: 1e-4 ≤ dt. With it `_dt_s / (_dt_s + tc)` ≥ 1e-4 / (1e-4 + 10) > 0 for every
  MOT_BAT_CURR_TC in [0, 10], so `0 * ∞` cannot arise in get_current_limit_max_throttle, also
  when `I + (V - V_min) / R` cancels to 0 (the corner the second statement left open). This
  alone suffices: `bat_curr_max = 0 ∨ 1 ≤ bat_curr_max` would exclude the subnormal limit of the
  counterexample but not the cancellation, where `batt_current_max` is exactly 0 and the ratio
  ∞ again. ArduCopter's loop time is about 2.5e-3 s. -/
def assumeInputs : List Clause := [
  ⟨"commands_bounded", abs "roll" ≤. 1e16 ∧. abs "pitch" ≤. 1e16 ∧. abs "yaw" ≤. 1e16⟩,
  ⟨"ff_range", abs "roll_ff" ≤. 1 ∧. abs "pitch_ff" ≤. 1 ∧. abs "yaw_ff" ≤. 1⟩,
  ⟨"throttle_range", 0 ≤. "throttle" ∧. "throttle" ≤. 1 ∧. 0 ≤. "throttle_avg_max" ∧.
      "throttle_avg_max" ≤. 1⟩,
  ⟨"throttle_filter_range", 0 ≤. "throttle_filter_hz" ∧. "throttle_filter_hz" ≤. 100⟩,
  ⟨"dt_range", 0.0001 ≤. "dt" ∧. "dt" ≤. 0.02⟩,
  ⟨"spool_desired_range", "spool_desired" ≤. 2⟩,
  ⟨"air_density_range", 0 ≤. "air_density_ratio" ∧. "air_density_ratio" ≤. 2⟩]

/-- The third statement: the second statement with `assumeInputs` (wider commands,
dt ≥ 1e-4). Its `throttle_range` (0 ≤ throttle ≤ 1) is narrower than what ArduCopter feeds the
mixer (see `assumeInputsFourth`); not refuted, replaced. Kept for the record, not used. -/
def contractThird : Contract where
  assume := assumeInputs ++ [assumeBatteryAsFirstStated,
      ⟨"current_positive", "bat_curr_max" =. 0 ∨. ¬. "batt_current_ok" ∨. 0 <. "batt_current"⟩] ++
    assumeParamsDocumented ++
    [⟨"pwm_valid", 1 ≤. "pwm_min" ∧. "pwm_min" <. "pwm_max"⟩]
  guarantee := guarantee

/-- Assumption clauses on the inputs, against the third statement: `throttle_range` becomes
`throttle_finite`, any finite throttle (throttle_avg_max still in [0, 1]). AP_Motors_Class.h:198
documents set_throttle as "range 0 ~ 1", but ArduCopter does not keep it there:
AC_AttitudeControl_Multi::set_throttle_out passes get_throttle_boosted(throttle_in), which divides
by constrain(cos(tilt), 0.1, 1) (AC_AttitudeControl_Multi.cpp:388-404), and AC_PosControl's
D_update_controller hands it a collective it does not bound (`hover - (P + D + I + FF)`,
AC_PosControl.cpp:1136-1145); in stock flight the boosted throttle reaches about 1.24. The mixer
reads _throttle_in only in update_throttle_filter (AP_MotorsMulticopter.cpp:348-375), which
filters it and resets the filter state into [0, 1] at every step (:355-360); every other use reads
the filtered value (get_throttle). A finite input cannot make the filter's `(input - output) *
alpha` overflow (the output is in [0, 1] before the step), so finiteness is the whole
requirement. Which guarantee clauses survive the wider input is recorded with the campaigns in
the ledger (docs and report: all of them did). -/
def assumeInputsFourth : List Clause :=
  assumeInputs.map fun c => if c.name != "throttle_range" then c else
    ⟨"throttle_finite", finite "throttle" ∧. 0 ≤. "throttle_avg_max" ∧.
      "throttle_avg_max" ≤. 1⟩

/-- The guarantee, against the third statement: `throttle_filtered_range` added (get_throttle()
in [0, 1]: update_throttle_filter resets the filter into [0, 1] while armed and to 0 while
disarmed, AP_MotorsMulticopter.cpp:352-364), which the attitude stage assumes
(`mixer_throttle_range`). -/
def guaranteeFourth : List Clause :=
  guarantee ++ [⟨"throttle_filtered_range", 0 ≤. "throttle_filtered" ∧. "throttle_filtered" ≤. 1⟩]

/-- The vehicle code's calls added with hover learning (ArduCopter calls them on the motors
outside output()): MOT_HOVER_LEARN in its documented values, the learning step's dt a time
step. -/
def assumeCalls : List Clause := [
  ⟨"hover_learn_range", 0 ≤. "hover_learn" ∧. "hover_learn" ≤. 2⟩,
  ⟨"hover_dt_range", ¬. "cmd_mixer_update_throttle_hover" ∨.
      (0 ≤. "cmd_mixer_update_throttle_hover_dt" ∧. "cmd_mixer_update_throttle_hover_dt" ≤. 1)⟩]

/-- `throttle_hover_range`: get_throttle_hover() constrains to [AP_MOTORS_THST_HOVER_MIN, _MAX]
(AP_MotorsMulticopter.h:16-17) and update_throttle_hover constrains what it stores
(AP_MotorsMulticopter.cpp:565). -/
def guaranteeFifth : List Clause :=
  guaranteeFourth ++ [⟨"throttle_hover_range", 0.125 ≤. "throttle_hover" ∧.
    "throttle_hover" ≤. 0.6875⟩]

/-- `spool_state_enum`: the output is uint32_t(motors->get_spool_state()) (adapter.cpp:192), and
SpoolState is an enum class of the values 0 to 4 (AP_Motors_Class.h:245-251). -/
def spoolStateEnum : Clause := ⟨"spool_state_enum", "spool_state" ≤. 4⟩

/-- The fourth statement: the third with any finite throttle (`assumeInputsFourth`) and the
filtered throttle's range guaranteed. Replaced when hover learning, output_min and thrust
boost were added (`contract`); not refuted. Kept for the record, not used. -/
def contractFourth : Contract where
  assume := assumeInputsFourth ++ [assumeBatteryAsFirstStated,
      ⟨"current_positive", "bat_curr_max" =. 0 ∨. ¬. "batt_current_ok" ∨. 0 <. "batt_current"⟩] ++
    assumeParamsDocumented ++
    [⟨"pwm_valid", 1 ≤. "pwm_min" ∧. "pwm_min" <. "pwm_max"⟩]
  guarantee := guaranteeFourth

/-- The contract: the fourth statement with the vehicle code's motor calls (output_min,
set_thrust_boost, update_throttle_hover) and MOT_HOVER_LEARN as a parameter, and the hover
throttle as an output. -/
def contract : Contract where
  assume := assumeInputsFourth ++ assumeCalls ++ [assumeBatteryAsFirstStated,
      ⟨"current_positive", "bat_curr_max" =. 0 ∨. ¬. "batt_current_ok" ∨. 0 <. "batt_current"⟩] ++
    assumeParamsDocumented ++
    [⟨"pwm_valid", 1 ≤. "pwm_min" ∧. "pwm_min" <. "pwm_max"⟩]
  guarantee := guaranteeFifth ++ [spoolStateEnum]

/-! ### Regimes and coverage (they steer and measure campaigns; the contract is above) -/

/-- Flight: armed, motor interlock on, the flight mode asking for THROTTLE_UNLIMITED, the
spool-up block cleared, and the clock advancing about one 400 Hz tick (2500 us) per step. -/
def flight : Regime where
  name := "flight"
  doc := "armed and flying: what ArduCopter's motors_output sees in the air"
  clauses := [
    ⟨"armed_interlock", "armed" ∧. "interlock"⟩,
    ⟨"spool_unlimited_desired", "spool_desired" =. 2⟩,
    ⟨"spoolup_unblocked", "clear_spoolup_block" =. tt⟩]
  hints := [.increasing "now_us" 1000000 2400 2600]

/-- ArduCopter's default MOT_ parameters (libraries/AP_Motors, read only):
SPIN_MIN 0.15, SPIN_MAX 0.95, SPIN_ARM 0.10, THST_EXPO 0.65, THST_HOVER 0.35, YAW_HEADROOM 200
(AP_MotorsMulticopter.h:18, 19, 20, 13, 14, 12; var_info AP_MotorsMulticopter.cpp:129, 65, 138,
57, 154, 48); PWM_MIN 1000, PWM_MAX 2000 (.cpp:111, 120); BAT_VOLT_MAX 0, BAT_VOLT_MIN 0,
BAT_CURR_MAX 0, BAT_CURR_TC 5 (.h:21-24; .cpp:74, 83, 92, 147); SPOOL_TIME 0.5 (.h:29, .cpp:188),
SPOOL_TIM_DN 0 (.cpp:250); SLEW_UP_TIME 0, SLEW_DN_TIME 0 (.h:25; .cpp:216, 225); SAFE_DISARM 0
(.cpp:170), SAFE_TIME 1 (.h:26, .cpp:234), IDLE_SEC 0 (.cpp:259). THST_HOVER is learned in flight
(HOVER_LEARN = 2); its default is used. -/
def stockParams : List Clause := [
  ⟨"stock_spin", "spin_min" =. 0.15 ∧. "spin_max" =. 0.95 ∧. "spin_arm" =. 0.1⟩,
  ⟨"stock_thrust", "thst_expo" =. 0.65 ∧. "thst_hover" =. 0.35 ∧. "yaw_headroom" =. 200⟩,
  ⟨"stock_pwm", "pwm_min" =. 1000 ∧. "pwm_max" =. 2000⟩,
  ⟨"stock_battery", "bat_volt_max" =. 0 ∧. "bat_volt_min" =. 0 ∧. "bat_curr_max" =. 0 ∧.
      "bat_curr_tc" =. 5⟩,
  ⟨"stock_spool", "spool_time" =. 0.5 ∧. "spool_tim_dn" =. 0 ∧. "slew_up_time" =. 0 ∧.
      "slew_dn_time" =. 0⟩,
  ⟨"stock_safety", "safe_disarm" =. ff ∧. "safe_time" =. 1 ∧. "idle_sec" =. 0⟩,
  ⟨"stock_hover_learn", "hover_learn" =. 2⟩]

/-- Flight-like inputs other than the roll, pitch and yaw commands: throttle around the hover
throttle, the position controller's throttle filter (POSCONTROL_THROTTLE_CUTOFF_FREQ_HZ = 2,
AC_PosControl.h:32), dt near 1/400 s, a 6S battery under load, air density near sea level, and
flight's arming state (`flight`'s clauses). -/
def stockInputs : List Clause := [
  ⟨"stock_throttle", 0.25 ≤. "throttle" ∧. "throttle" ≤. 0.5 ∧. 0.35 ≤. "throttle_avg_max" ∧.
      "throttle_avg_max" ≤. 1 ∧. "throttle_filter_hz" =. 2⟩,
  ⟨"stock_dt", 0.0024 ≤. "dt" ∧. "dt" ≤. 0.0026⟩,
  ⟨"stock_battery_readings", 22 ≤. "batt_voltage" ∧. "batt_voltage" ≤. 25.2 ∧.
      22 ≤. "batt_resting_voltage" ∧. "batt_resting_voltage" ≤. 25.2 ∧. 5 ≤. "batt_current" ∧.
      "batt_current" ≤. 40 ∧. "batt_current_ok" ∧. 0.01 ≤. "batt_resistance" ∧.
      "batt_resistance" ≤. 0.05⟩,
  ⟨"stock_air", 0.9 ≤. "air_density_ratio" ∧. "air_density_ratio" ≤. 1.1⟩] ++ flight.clauses

/-- The stock vehicle's mixer in flight, with rate commands as in hover and gentle maneuvers
(within 0.3) and no feed-forward (the rate PIDs' FF is 0). -/
def stockFlight : Regime where
  name := "stock_flight"
  doc := "ArduCopter's default MOT_ parameters, flight-like inputs, 400 Hz"
  clauses := stockParams ++ stockInputs ++ [
    ⟨"stock_commands", abs "roll" ≤. 0.3 ∧. abs "pitch" ≤. 0.3 ∧. abs "yaw" ≤. 0.3 ∧.
      "roll_ff" =. 0 ∧. "pitch_ff" =. 0 ∧. "yaw_ff" =. 0⟩]
  hints := flight.hints

/-- The stock vehicle in flight with the throttle ArduCopter actually hands the mixer: the
attitude stage's boosted throttle (up to about 1.24 in stock flight, 10 at most) and the
position stage's unbounded collective, here between -0.5 and 1.5 (the case the third
statement's `throttle_range` excluded). -/
def stockBoosted : Regime where
  name := "stock_boosted"
  doc := "stock_flight with throttle in [-0.5, 1.5] (angle boost, unbounded collective)"
  clauses := stockParams ++ (stockInputs.map fun c => if c.name != "stock_throttle" then c else
      ⟨"stock_throttle", -0.5 ≤. "throttle" ∧. "throttle" ≤. 1.5 ∧. 0.35 ≤. "throttle_avg_max" ∧.
        "throttle_avg_max" ≤. 1 ∧. "throttle_filter_hz" =. 2⟩) ++ [
    ⟨"stock_commands", abs "roll" ≤. 0.3 ∧. abs "pitch" ≤. 0.3 ∧. abs "yaw" ≤. 0.3 ∧.
      "roll_ff" =. 0 ∧. "pitch_ff" =. 0 ∧. "yaw_ff" =. 0⟩]
  hints := flight.hints

/-- What a campaign counts: the spool state THROTTLE_UNLIMITED (3), and with no limit flag set;
throttle inputs outside [0, 1]. -/
def coverage : List Clause := [
  ⟨"throttle_above_1", 1 <. "throttle"⟩,
  ⟨"throttle_negative", "throttle" <. 0⟩,
  ⟨"unlimited_throttle_above_1", "spool_state" =. 3 ∧. 1 <. "throttle"⟩,
  ⟨"throttle_unlimited", "spool_state" =. 3⟩,
  ⟨"unlimited_no_rpy_limit", "spool_state" =. 3 ∧. ¬. "limit_roll" ∧. ¬. "limit_pitch" ∧.
      ¬. "limit_yaw"⟩,
  ⟨"unlimited_no_limit", "spool_state" =. 3 ∧. ¬. "limit_roll" ∧. ¬. "limit_pitch" ∧.
      ¬. "limit_yaw" ∧. ¬. "limit_throttle_lower" ∧. ¬. "limit_throttle_upper"⟩]

def module : Module where
  name := "mixer"
  doc := "ArduCopter's quad-X AP_MotorsMatrix stepped by output()"
  params := params
  input := input
  output := output
  contract := contract
  exe := "build/modules/mixer/mixer"
  stack := .ardupilot
  regimes := [flight, stockFlight, stockBoosted]
  coverage := coverage

end Ardupilot.Modules.Mixer
