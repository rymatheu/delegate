import Harness.Module

/-! # attitude: ArduCopter's attitude controller

One `AC_AttitudeControl_Multi` (libraries/AC_AttitudeControl, with its base `AC_AttitudeControl`
and the AP_Math code it calls: quaternions, rotation matrices, the square-root controller, the
input shaping of control.cpp), as ArduCopter builds it in Copter::allocate_motors and runs it
from Copter::update_flight_mode. The executable is built by `ardupilot/build.sh attitude` from the
real, unmodified ArduPilot sources listed in sources.txt; adapter.cpp says what one step does and
in which order, the stubs_*.cpp files (compiled through stubs.cpp) what stands in for what.

The rate PIDs are not in this stage (they are the `rate` system). The part of
`AC_AttitudeControl_Multi::rate_controller_run_dt` that is not a PID (the throttle gain boost,
the throttle/attitude mix slew, the P/D and I scales handed to the PIDs, the gyro the attitude
controller keeps) runs here, at the places in the step that adapter.cpp gives.

Stand-ins fed by input ports: the AHRS view (`AP_AHRS_View`, the real class, updated by its real
`update()` from an AP_AHRS stand-in whose rotation matrix is built from `est_roll`, `est_pitch`,
`est_yaw` by `Matrix3f::from_euler`), the motors (`AP_MotorsMatrix`, the real class, whose
throttle state is set from the mixer's outputs), and the three rate PIDs held by the class
(real `AC_PID` objects: only the yaw P gain is read, and the resets made on them are reported as
the outputs `ac_rate_*` for the `rate` stage).

Commands (`cmd_attitude_<method>`, with one field per argument) are executed in this order
within a step, which is the order of ArduCopter's fast loop and of the mode code
(adapter.cpp, module_step): set_yaw_rate_tc, set_roll_pitch_rate_tc (Copter::set_mode),
inertial_frame_reset (Copter::check_ekf_reset), landed_gain_reduction
(Copter::update_flight_mode), then the mode's calls: relax_attitude_controllers,
reset_target_and_rate, reset_yaw_target_and_rate, reset_rate_controller_I_terms,
reset_rate_controller_I_terms_smoothly, the throttle calls flagged "before the input", the
input methods (input_euler_angle_roll_pitch_euler_rate_yaw, input_euler_angle_roll_pitch_yaw,
input_rate_bf_roll_pitch_yaw, input_thrust_vector_rate_heading, input_thrust_vector_heading),
the throttle calls flagged "after the input", then set_throttle_mix_min/man/max
(Copter::update_throttle_mix, throttle_loop). The set_throttle_out calls have two sources: the
position controller (signals `pc_throttle_set`, `throttle_in`) and the mode itself (command
`cmd_attitude_set_throttle_out`); which side of the input call each falls on differs by mode,
so each has an order flag; on one side, the position controller's call comes first.

What is lost against the vehicle: AP_AHRS's rotation matrix is the EKF quaternion's
(NavEKF3_core::getRotationBodyToNED, in double on SITL); here it is rebuilt from the Euler angles
the estimator outputs, so it can differ from ArduCopter's by a few ulps per entry.

Hand-checked case: ardupilot/modules/attitude/hand-checked-case.json (a pure yaw-heading step, a relax,
a small roll demand; working in its note; `harness replay` reproduces it bit for bit). -/

namespace Ardupilot.Modules.Attitude

open Harness Harness.Contract.Lang

private def f32 (name doc : String) : Field := { name, type := .f32, doc }
private def bool (name doc : String) : Field := { name, type := .bool, doc }

def params : Schema := #[
  bool "atc_rate_ff_enab" "ATC_RATE_FF_ENAB: body-frame rate feed-forward (_rate_bf_ff_enabled)",
  bool "atc_angle_boost" "ATC_ANGLE_BOOST: angle boost (_angle_boost_enabled)",
  f32 "atc_ang_rll_p" "ATC_ANG_RLL_P: roll angle P gain (_p_angle_roll)",
  f32 "atc_ang_pit_p" "ATC_ANG_PIT_P: pitch angle P gain (_p_angle_pitch)",
  f32 "atc_ang_yaw_p" "ATC_ANG_YAW_P: yaw angle P gain (_p_angle_yaw)",
  f32 "atc_ang_lim_tc" "ATC_ANG_LIM_TC: alt-hold lean limit time constant, s (_angle_limit_tc)",
  f32 "atc_rate_r_max" "ATC_RATE_R_MAX: roll rate limit, deg/s, 0 off (_ang_vel_roll_max_degs)",
  f32 "atc_rate_p_max" "ATC_RATE_P_MAX: pitch rate limit, deg/s, 0 off",
  f32 "atc_rate_y_max" "ATC_RATE_Y_MAX: yaw rate limit, deg/s, 0 off",
  f32 "atc_input_tc" "ATC_INPUT_TC: attitude input time constant, s (_input_tc)",
  f32 "atc_land_r_mult" "ATC_LAND_R_MULT: landed roll gain multiplier (_land_roll_mult)",
  f32 "atc_land_p_mult" "ATC_LAND_P_MULT: landed pitch gain multiplier",
  f32 "atc_land_y_mult" "ATC_LAND_Y_MULT: landed yaw gain multiplier",
  f32 "atc_angle_max" "ATC_ANGLE_MAX: lean angle limit, deg (_angle_max_deg)",
  f32 "atc_rate_wpy_max" "ATC_RATE_WPY_MAX: yaw slew limit, deg/s (_rate_wp_yaw_max_degs)",
  f32 "atc_acc_y_max" "ATC_ACC_Y_MAX: yaw acceleration limit, deg/s/s, 0 off",
  f32 "atc_acc_r_max" "ATC_ACC_R_MAX: roll acceleration limit, deg/s/s, 0 off",
  f32 "atc_acc_p_max" "ATC_ACC_P_MAX: pitch acceleration limit, deg/s/s, 0 off",
  f32 "atc_thr_mix_min" "ATC_THR_MIX_MIN (_thr_mix_min)",
  f32 "atc_thr_mix_max" "ATC_THR_MIX_MAX (_thr_mix_max)",
  f32 "atc_thr_mix_man" "ATC_THR_MIX_MAN (_thr_mix_man)",
  f32 "atc_thr_g_boost"
    "ATC_THR_G_BOOST: angle P / PD boost on throttle slew (_throttle_gain_boost)",
  f32 "yaw_kp" "ATC_RAT_YAW_P, the yaw rate PID's P gain (the `rate` system's yaw_kp), read by \
    thrust_heading_rotation_angles"]

/-- `cmd_attitude_<m>` and its argument fields `cmd_attitude_<m>_<arg>`. -/
private def cmd (m doc : String) (args : List Field := []) : Array Field :=
  #[bool s!"cmd_attitude_{m}" s!"{doc} is called this tick"] ++
  (args.toArray.map fun f => { f with name := s!"cmd_attitude_{m}_{f.name}" })

def signals : Schema := #[
  f32 "dt" "time step, s: Copter::run_rate_controller_main's set_dt_s (last loop time)",
  f32 "gyro_x" "latest gyro, rad/s, body x: rate_controller_run_dt's gyro_rads (_rate_gyro_rads)",
  f32 "gyro_y" "latest gyro, rad/s, body y",
  f32 "gyro_z" "latest gyro, rad/s, body z",
  f32 "est_roll" "AHRS roll, rad: the AP_AHRS stand-in's rotation matrix is from_euler(roll, \
    pitch, yaw)",
  f32 "est_pitch" "AHRS pitch, rad",
  f32 "est_yaw" "AHRS yaw, rad",
  f32 "thrust_vec_x" "AC_PosControl::get_thrust_vector().x (NED), the thrust vector the mode \
    passes to the input_thrust_vector_* commands",
  f32 "thrust_vec_y" "get_thrust_vector().y",
  f32 "thrust_vec_z" "get_thrust_vector().z",
  f32 "throttle_in" "the throttle AC_PosControl::update_U_controller passes to \
    set_throttle_out(throttle_in, true, POSCONTROL_THROTTLE_CUTOFF_FREQ_HZ)",
  bool "pc_throttle_set" "AC_PosControl::D_update_controller ran this tick and called \
    set_throttle_out(throttle_in, pc_throttle_angle_boost, pc_throttle_cutoff_hz) (the position \
    stage's name; this input was `pc_set_throttle_out` before the stages were composed)",
  bool "pc_throttle_angle_boost" "that call's apply_angle_boost argument (true in \
    AC_PosControl.cpp's D_update_controller)",
  f32 "pc_throttle_cutoff_hz" "that call's filter_cutoff argument, Hz \
    (POSCONTROL_THROTTLE_CUTOFF_FREQ_HZ = 2 in AC_PosControl)",
  f32 "throttle_hover" "the motors' MOT_THST_HOVER (_throttle_hover; get_throttle_hover() \
    constrains it to [0.125, 0.6875])",
  f32 "throttle_filtered" "mixer: get_throttle(), the filtered throttle",
  f32 "throttle_out" "mixer: get_throttle_out()",
  f32 "throttle_slew_rate" "mixer: get_throttle_slew_rate()",
  f32 "throttle_thrust_max" "mixer: get_throttle_thrust_max()"]

def commands : Schema :=
  cmd "set_yaw_rate_tc" "set_yaw_rate_tc(input_tc) (Copter::set_mode)"
    [f32 "input_tc" "yaw rate shaping time constant, s (_rate_y_tc)"] ++
  cmd "set_roll_pitch_rate_tc" "set_roll_pitch_rate_tc(input_tc) (Copter::set_mode)"
    [f32 "input_tc" "roll/pitch rate shaping time constant, s (_rate_rp_tc)"] ++
  cmd "inertial_frame_reset" "inertial_frame_reset() (Copter::check_ekf_reset)" ++
  cmd "landed_gain_reduction" "landed_gain_reduction(landed) (Copter::update_flight_mode)"
    [bool "landed" "ap.land_complete"] ++
  cmd "relax_attitude_controllers" "relax_attitude_controllers()" ++
  cmd "reset_target_and_rate" "reset_target_and_rate(reset_rate)"
    [bool "reset_rate" "also zero the rate targets"] ++
  cmd "reset_yaw_target_and_rate" "reset_yaw_target_and_rate(reset_rate)"
    [bool "reset_rate" "also zero the yaw rate target"] ++
  cmd "reset_rate_controller_I_terms" "reset_rate_controller_I_terms()" ++
  cmd "reset_rate_controller_I_terms_smoothly" "reset_rate_controller_I_terms_smoothly()" ++
  cmd "input_euler_angle_roll_pitch_euler_rate_yaw"
    "input_euler_angle_roll_pitch_euler_rate_yaw_rad(roll, pitch, yaw_rate)"
    [f32 "roll" "euler roll angle, rad", f32 "pitch" "euler pitch angle, rad",
     f32 "yaw_rate" "euler yaw rate, rad/s"] ++
  cmd "input_euler_angle_roll_pitch_yaw"
    "input_euler_angle_roll_pitch_yaw_rad(roll, pitch, yaw, slew_yaw)"
    [f32 "roll" "euler roll angle, rad", f32 "pitch" "euler pitch angle, rad",
     f32 "yaw" "euler yaw angle, rad", bool "slew_yaw" "limit the yaw slew"] ++
  cmd "input_rate_bf_roll_pitch_yaw" "input_rate_bf_roll_pitch_yaw_rads(roll, pitch, yaw rate)"
    [f32 "roll_rate" "body roll rate, rad/s", f32 "pitch_rate" "body pitch rate, rad/s",
     f32 "yaw_rate" "body yaw rate, rad/s"] ++
  cmd "input_thrust_vector_rate_heading"
    "input_thrust_vector_rate_heading_rads(thrust_vec, heading_rate, slew_yaw)"
    [f32 "heading_rate" "heading rate, rad/s", bool "slew_yaw" "limit the yaw slew"] ++
  cmd "input_thrust_vector_heading"
    "input_thrust_vector_heading(thrust_vec, HeadingCommand{yaw_angle, yaw_rate, mode})"
    [f32 "yaw_angle" "heading, rad", f32 "yaw_rate" "heading rate, rad/s",
     { name := "heading_mode", type := .u32,
       doc := "HeadingMode: 0 Angle_Only, 1 Angle_And_Rate, 2 Rate_Only" }] ++
  #[bool "cmd_attitude_pos_throttle_after_input" "order of this tick's calls: the position \
    controller's set_throttle_out (pc_throttle_set) comes after the input method (AltHold, \
    Loiter) rather than before it (Guided, Auto, RTL, Land, ground handling)"] ++
  cmd "set_throttle_out" "set_throttle_out(throttle_in, apply_angle_boost, filter_cutoff) by the \
    mode itself (Stabilize, zero_throttle_and_relax_ac, takeoff)"
    [f32 "throttle_in" "throttle, 0..1", bool "apply_angle_boost" "apply the angle boost",
     f32 "filter_cutoff" "motors' throttle filter cutoff, Hz",
     bool "before_input" "order of this tick's calls: made before the input method (takeoff.cpp) \
       rather than after it (Stabilize, zero_throttle_and_relax_ac)"] ++
  cmd "set_throttle_mix_min" "set_throttle_mix_min() (Copter::update_throttle_mix)" ++
  cmd "set_throttle_mix_man" "set_throttle_mix_man() (Copter::update_throttle_mix)" ++
  cmd "set_throttle_mix_max" "set_throttle_mix_max(ratio) (Copter::update_throttle_mix)"
    [f32 "ratio" "AC_PosControl::get_vel_D_control_ratio()"] ++
  cmd "rate_controller_target_reset" "rate_controller_target_reset() \
    (Copter::run_rate_controller_main, Attitude.cpp:23; accepted, no effect: the step makes this \
    call itself at the place ArduCopter makes it, adapter.cpp step 7)"

/-- One `cmd_attitude_<method>_seq` (u32) per command method: the position of this call in the
supervisor's call order within the tick, counting from 1 across all stages; 0 = not sequenced.
Set commands run in increasing `_seq` (a set command with `_seq` 0 in a sequenced tick runs after
the sequenced commands that precede it in the fixed order); with every `_seq` 0, in the fixed
order of the header. The position stage's set_throttle_out (`pc_throttle_set`) runs at
`pc_throttle_seq`; in a sequenced tick the order flags `cmd_attitude_pos_throttle_after_input`
and `cmd_attitude_set_throttle_out_before_input` are not used. -/
def seqFields (cmds : Schema) : Schema :=
  (cmds.filter fun f => f.type == .bool && f.doc.endsWith "is called this tick").map fun f =>
    { name := s!"{f.name}_seq", type := .u32, doc := s!"{f.name}: call order in the tick" }

def input : Schema := signals ++
  #[{ name := "pc_throttle_seq", type := .u32,
      doc := "position: the `_seq` of its D_update_controller (0: not sequenced)" }] ++
  commands ++ seqFields commands

def output : Schema := #[
  f32 "target_x" "rate_bf_targets().x: roll rate target, rad/s, for the rate PIDs next tick",
  f32 "target_y" "rate_bf_targets().y",
  f32 "target_z" "rate_bf_targets().z",
  f32 "pd_scale_x" "_pd_scale.x the roll rate PID gets next tick (landed gain x throttle boost)",
  f32 "pd_scale_y" "_pd_scale.y",
  f32 "pd_scale_z" "_pd_scale.z",
  f32 "i_scale_x" "_i_scale.x the roll rate PID gets next tick",
  f32 "i_scale_y" "_i_scale.y",
  f32 "i_scale_z" "_i_scale.z",
  f32 "throttle" "_motors.set_throttle(.) by the last set_throttle_out (the motors' _throttle_in)",
  f32 "throttle_avg_max" "_motors.set_throttle_avg_max(.) by the last set_throttle_out \
    (after the setter's constraint to [0, 1])",
  f32 "throttle_filter_hz" "_motors.set_throttle_filter_cutoff(.) by the last set_throttle_out",
  f32 "ac_att_target_q1" "get_attitude_target_quat().q1 (scalar)",
  f32 "ac_att_target_q2" "get_attitude_target_quat().q2",
  f32 "ac_att_target_q3" "get_attitude_target_quat().q3",
  f32 "ac_att_target_q4" "get_attitude_target_quat().q4",
  f32 "ac_att_target_roll" "get_att_target_euler_rad().x",
  f32 "ac_att_target_pitch" "get_att_target_euler_rad().y",
  f32 "ac_att_target_yaw" "get_att_target_euler_rad().z",
  f32 "ac_ang_vel_target_x" "get_attitude_target_ang_vel().x: feed-forward angular velocity of \
    the target, rad/s, target frame",
  f32 "ac_ang_vel_target_y" "get_attitude_target_ang_vel().y",
  f32 "ac_ang_vel_target_z" "get_attitude_target_ang_vel().z",
  f32 "ac_ang_accel_target_x" "_ang_accel_target_rads.x, rad/s/s",
  f32 "ac_ang_accel_target_y" "_ang_accel_target_rads.y",
  f32 "ac_ang_accel_target_z" "_ang_accel_target_rads.z",
  f32 "ac_rate_ef_target_x" "get_rate_ef_target_rads().x: euler rate target, rad/s",
  f32 "ac_rate_ef_target_y" "get_rate_ef_target_rads().y",
  f32 "ac_rate_ef_target_z" "get_rate_ef_target_rads().z",
  f32 "ac_att_error_q1" "_attitude_ang_error.q1: body-to-target rotation, body frame",
  f32 "ac_att_error_q2" "_attitude_ang_error.q2",
  f32 "ac_att_error_q3" "_attitude_ang_error.q3",
  f32 "ac_att_error_q4" "_attitude_ang_error.q4",
  f32 "ac_thrust_error_angle" "_thrust_error_angle_rad (get_att_error_angle_deg() in rad)",
  f32 "ac_lean_angle" "lean_angle_rad(): _thrust_angle_rad",
  f32 "ac_lean_angle_max" "lean_angle_max_rad()",
  f32 "ac_althold_lean_angle_max" "get_althold_lean_angle_max_rad()",
  f32 "ac_angle_boost" "angle_boost()",
  f32 "ac_throttle_in" "get_throttle_in(): the last set_throttle_out argument",
  f32 "ac_throttle_mix" "get_throttle_mix(): _throttle_rpy_mix",
  bool "ac_throttle_mix_min" "is_throttle_mix_min()",
  f32 "ac_slew_yaw_max" "get_slew_yaw_max_rads()",
  f32 "ac_feedforward_scalar" "_feedforward_scalar (rate_controller_run_dt scales the yaw PID's \
    feed-forward by it)",
  bool "ac_rate_reset_i" "the rate PIDs' reset_I() was called this tick (rate stage: apply \
    before its next update_all)",
  bool "ac_rate_relax_i" "the rate PIDs' relax_integrator(0, dt, AC_ATTITUDE_RATE_RELAX_TC) was \
    called this tick",
  bool "ac_rate_reset_filter" "the rate PIDs' reset_filter() was called this tick",
  bool "ac_bf_feedforward" "get_bf_feedforward(): ATC_RATE_FF_ENAB (read by the position stage)",
  bool "ac_input_last" "an input method ran this tick and no call that sets the target \
    (relax_attitude_controllers, reset_*_target_and_rate, inertial_frame_reset) came after it \
    (always so in the fixed order)",
  { name := "ac_internal_errors", type := .u32,
    doc := "ArduPilot internal errors raised since init" }]

/-! ### Clause builders -/

private def v (n : String) : Expr := .var n
/-- degrees to radians as ArduPilot's `radians()` (x * DEG_TO_RAD, binary32). -/
private def rad (e : Expr) : Expr := e * 0.017453292

/-- `e₁ ∧ … ∧ eₙ` (`tt` when empty). -/
private def allOf : List Expr → Expr
  | [] => tt
  | [e] => e
  | e :: es => e ∧. allOf es

/-- `e₁ ∨ … ∨ eₙ` (`ff` when empty). -/
private def anyOf : List Expr → Expr
  | [] => ff
  | [e] => e
  | e :: es => e ∨. anyOf es

def finiteOutputs : Expr :=
  allOf ((output.toList.filter (·.type == .f32)).map fun f => finite (v f.name))

def inputCmds : List String :=
  ["input_euler_angle_roll_pitch_euler_rate_yaw", "input_euler_angle_roll_pitch_yaw",
   "input_rate_bf_roll_pitch_yaw", "input_thrust_vector_rate_heading",
   "input_thrust_vector_heading"]

/-- One of the input methods was called this tick. -/
def anyInput : Expr :=
  anyOf (inputCmds.map fun m => v s!"cmd_attitude_{m}")

private def sq (e : Expr) : Expr := e * e

/-! ### The assumption -/

/-- ArduPilot's documented ranges (@Range in AC_AttitudeControl.cpp and
AC_AttitudeControl_Multi.cpp; Copter's ranges where Sub's differ), each parameter on its own. -/
def assumeParams : List Clause := [
  ⟨"ang_p_range", 3 ≤. "atc_ang_rll_p" ∧. "atc_ang_rll_p" ≤. 12 ∧. 3 ≤. "atc_ang_pit_p" ∧.
      "atc_ang_pit_p" ≤. 12 ∧. 3 ≤. "atc_ang_yaw_p" ∧. "atc_ang_yaw_p" ≤. 12⟩,
  ⟨"ang_lim_tc_range", 0.5 ≤. "atc_ang_lim_tc" ∧. "atc_ang_lim_tc" ≤. 10⟩,
  ⟨"rate_max_range", 0 ≤. "atc_rate_r_max" ∧. "atc_rate_r_max" ≤. 1080 ∧. 0 ≤. "atc_rate_p_max" ∧.
      "atc_rate_p_max" ≤. 1080 ∧. 0 ≤. "atc_rate_y_max" ∧. "atc_rate_y_max" ≤. 1080⟩,
  ⟨"input_tc_range", 0 ≤. "atc_input_tc" ∧. "atc_input_tc" ≤. 1⟩,
  ⟨"land_mult_range", 0.25 ≤. "atc_land_r_mult" ∧. "atc_land_r_mult" ≤. 1 ∧.
      0.25 ≤. "atc_land_p_mult" ∧. "atc_land_p_mult" ≤. 1 ∧. 0.25 ≤. "atc_land_y_mult" ∧.
      "atc_land_y_mult" ≤. 1⟩,
  ⟨"angle_max_range", 10 ≤. "atc_angle_max" ∧. "atc_angle_max" ≤. 80⟩,
  ⟨"rate_wpy_max_range", 5 ≤. "atc_rate_wpy_max" ∧. "atc_rate_wpy_max" ≤. 180⟩,
  ⟨"acc_max_range", 0 ≤. "atc_acc_y_max" ∧. "atc_acc_y_max" ≤. 720 ∧. 0 ≤. "atc_acc_r_max" ∧.
      "atc_acc_r_max" ≤. 1800 ∧. 0 ≤. "atc_acc_p_max" ∧. "atc_acc_p_max" ≤. 1800⟩,
  ⟨"thr_mix_range", 0.1 ≤. "atc_thr_mix_min" ∧. "atc_thr_mix_min" ≤. 0.25 ∧.
      0.5 ≤. "atc_thr_mix_max" ∧. "atc_thr_mix_max" ≤. 0.9 ∧. 0.1 ≤. "atc_thr_mix_man" ∧.
      "atc_thr_mix_man" ≤. 0.9⟩,
  ⟨"thr_g_boost_range", 0 ≤. "atc_thr_g_boost" ∧. "atc_thr_g_boost" ≤. 1⟩,
  ⟨"yaw_kp_range", 0.1 ≤. "yaw_kp" ∧. "yaw_kp" ≤. 2.5⟩]

/-- The signals as first stated: bounded as their producers' contracts bound them where those
exist (the mixer's `signals_finite`), otherwise as ArduPilot's documentation and physics bound
them; the Euler angles over their whole range. -/
def assumeSignalsAsFirstStated : List Clause := [
  ⟨"dt_range", 0 <. "dt" ∧. "dt" ≤. 0.02⟩,
  ⟨"gyro_bounded", abs "gyro_x" ≤. 100 ∧. abs "gyro_y" ≤. 100 ∧. abs "gyro_z" ≤. 100⟩,
  ⟨"euler_range", abs "est_roll" ≤. 3.1415927 ∧. abs "est_pitch" ≤. 1.5707964 ∧.
      abs "est_yaw" ≤. 3.1415927⟩,
  ⟨"thrust_vec_bounded", abs "thrust_vec_x" ≤. 1000 ∧. abs "thrust_vec_y" ≤. 1000 ∧.
      abs "thrust_vec_z" ≤. 1000⟩,
  ⟨"throttle_in_range", 0 ≤. "throttle_in" ∧. "throttle_in" ≤. 1⟩,
  ⟨"hover_range", 0 ≤. "throttle_hover" ∧. "throttle_hover" ≤. 1⟩,
  ⟨"mixer_throttle_range", 0 ≤. "throttle_filtered" ∧. "throttle_filtered" ≤. 1 ∧.
      finite "throttle_out" ∧. 0 ≤. "throttle_out" ∧. finite "throttle_slew_rate" ∧.
      0 ≤. "throttle_slew_rate" ∧. 0 ≤. "throttle_thrust_max" ∧. "throttle_thrust_max" ≤. 1⟩]

/-- The command arguments as first stated. -/
def assumeCommandsAsFirstStated : List Clause := [
  ⟨"rate_tc_range", 0 ≤. "cmd_attitude_set_yaw_rate_tc_input_tc" ∧.
      "cmd_attitude_set_yaw_rate_tc_input_tc" ≤. 1 ∧.
      0 ≤. "cmd_attitude_set_roll_pitch_rate_tc_input_tc" ∧.
      "cmd_attitude_set_roll_pitch_rate_tc_input_tc" ≤. 1⟩,
  ⟨"angle_args_bounded",
      abs "cmd_attitude_input_euler_angle_roll_pitch_euler_rate_yaw_roll" ≤. 3.1415927 ∧.
      abs "cmd_attitude_input_euler_angle_roll_pitch_euler_rate_yaw_pitch" ≤. 3.1415927 ∧.
      abs "cmd_attitude_input_euler_angle_roll_pitch_yaw_roll" ≤. 3.1415927 ∧.
      abs "cmd_attitude_input_euler_angle_roll_pitch_yaw_pitch" ≤. 3.1415927 ∧.
      abs "cmd_attitude_input_euler_angle_roll_pitch_yaw_yaw" ≤. 7 ∧.
      abs "cmd_attitude_input_thrust_vector_heading_yaw_angle" ≤. 7⟩,
  ⟨"rate_args_bounded",
      abs "cmd_attitude_input_euler_angle_roll_pitch_euler_rate_yaw_yaw_rate" ≤. 20 ∧.
      abs "cmd_attitude_input_rate_bf_roll_pitch_yaw_roll_rate" ≤. 20 ∧.
      abs "cmd_attitude_input_rate_bf_roll_pitch_yaw_pitch_rate" ≤. 20 ∧.
      abs "cmd_attitude_input_rate_bf_roll_pitch_yaw_yaw_rate" ≤. 20 ∧.
      abs "cmd_attitude_input_thrust_vector_rate_heading_heading_rate" ≤. 20 ∧.
      abs "cmd_attitude_input_thrust_vector_heading_yaw_rate" ≤. 20⟩,
  ⟨"heading_mode_range", "cmd_attitude_input_thrust_vector_heading_heading_mode" ≤. 2⟩,
  ⟨"throttle_args_range", 0 ≤. "cmd_attitude_set_throttle_out_throttle_in" ∧.
      "cmd_attitude_set_throttle_out_throttle_in" ≤. 1 ∧.
      0 ≤. "cmd_attitude_set_throttle_out_filter_cutoff" ∧.
      "cmd_attitude_set_throttle_out_filter_cutoff" ≤. 100⟩,
  ⟨"mix_ratio_range", 0 ≤. "cmd_attitude_set_throttle_mix_max_ratio" ∧.
      "cmd_attitude_set_throttle_mix_max_ratio" ≤. 1⟩]

/-! ### The guarantee -/

/-- The guarantee as first stated (the clauses the brief aims for, and the ranges the consumers
`rate` and `mixer` assume). -/
def guaranteeAsFirstStated : List Clause := [
  ⟨"outputs_finite", finiteOutputs⟩,
  ⟨"no_internal_error", "ac_internal_errors" =. 0⟩,
  -- every path that sets the target normalizes it or builds it from unit quaternions
  ⟨"target_quat_unit", abs (sq (v "ac_att_target_q1") + sq (v "ac_att_target_q2") +
      sq (v "ac_att_target_q3") + sq (v "ac_att_target_q4") - 1) ≤. 1e-5⟩,
  -- ang_vel_limit in attitude_controller_run_quat, when a limit is set
  ⟨"rate_targets_limited", ("atc_rate_r_max" =. 0 ∨. abs "target_x" ≤. rad "atc_rate_r_max") ∧.
      ("atc_rate_p_max" =. 0 ∨. abs "target_y" ≤. rad "atc_rate_p_max") ∧.
      ("atc_rate_y_max" =. 0 ∨. abs "target_z" ≤. rad "atc_rate_y_max")⟩,
  ⟨"throttle_range", 0 ≤. "throttle" ∧. "throttle" ≤. 1⟩,
  ⟨"throttle_avg_max_range", 0 ≤. "throttle_avg_max" ∧. "throttle_avg_max" ≤. 1⟩,
  ⟨"throttle_filter_range", 0 ≤. "throttle_filter_hz" ∧. "throttle_filter_hz" ≤. 100⟩,
  -- landed_gain_reduction scales by a convex mix of 1 and LAND_*_MULT; the gain boost
  -- multiplies roll and pitch by constrain(THR_G_BOOST + 1, 1, 2)
  ⟨"pd_scale_range", 0 ≤. "pd_scale_x" ∧. "pd_scale_x" ≤. 1 + v "atc_thr_g_boost" ∧.
      0 ≤. "pd_scale_y" ∧. "pd_scale_y" ≤. 1 + v "atc_thr_g_boost" ∧.
      0 ≤. "pd_scale_z" ∧. "pd_scale_z" ≤. 1⟩,
  -- nothing in the covered commands scales I (scale_I_to_angle_P is not covered)
  ⟨"i_scale_one", "i_scale_x" =. 1 ∧. "i_scale_y" =. 1 ∧. "i_scale_z" =. 1⟩,
  -- with no attitude error left after an input method and no target rate, nothing is demanded
  ⟨"zero_error_zero_target", ¬. anyInput ∨.
      ¬. (abs "ac_att_error_q2" ≤. 1e-6 ∧. abs "ac_att_error_q3" ≤. 1e-6 ∧.
          abs "ac_att_error_q4" ≤. 1e-6 ∧. abs "ac_ang_vel_target_x" ≤. 1e-6 ∧.
          abs "ac_ang_vel_target_y" ≤. 1e-6 ∧. abs "ac_ang_vel_target_z" ≤. 1e-6) ∨.
      (abs "target_x" ≤. 1e-4 ∧. abs "target_y" ≤. 1e-4 ∧. abs "target_z" ≤. 1e-4)⟩,
  ⟨"lean_limits", 0.17453292 ≤. "ac_lean_angle_max" ∧. "ac_lean_angle_max" ≤. 1.3962635 ∧.
      0.17453292 ≤. "ac_althold_lean_angle_max" ∧. "ac_althold_lean_angle_max" ≤. 1.5707964⟩,
  ⟨"mix_range", 0.1 ≤. "ac_throttle_mix" ∧. "ac_throttle_mix" ≤. 5⟩,
  ⟨"angle_boost_range", abs "ac_angle_boost" ≤. 1⟩]

/-- The attitude error and target rate are small (the premise of `zero_error_zero_target`). -/
def smallError : Expr :=
  abs "ac_att_error_q2" ≤. 1e-6 ∧. abs "ac_att_error_q3" ≤. 1e-6 ∧.
    abs "ac_att_error_q4" ≤. 1e-6 ∧. abs "ac_ang_vel_target_x" ≤. 1e-6 ∧.
    abs "ac_ang_vel_target_y" ≤. 1e-6 ∧. abs "ac_ang_vel_target_z" ≤. 1e-6

/-- A bound on the magnitude of the body-frame feed-forward `rotation_target_to_body *
_ang_vel_target_rads` (attitude_controller_run_quat): a rotation keeps the norm, which is at
most the sum of the absolute components; 1e-5 relative and 1e-6 absolute cover the rounding. -/
def ffBound : Expr :=
  (abs "ac_ang_vel_target_x" + abs "ac_ang_vel_target_y" + abs "ac_ang_vel_target_z") *
    1.00001 + 0.000001

/-- With no attitude error left after an input method and no target rate, the rate targets are
the angle P gain times the thrust-error angle thrust_vector_rotation_angles computed: an
acosf(dot) of a dot product a few ulps below 1, the only error left
(AC_AttitudeControl.cpp:1076). The roll and pitch errors are the components of that correction
(norm E), the yaw error the heading residual of its inverse (at most E plus the error
quaternion's angle); sqrt_controller gives at most P times the error, and the angle P scale is
at most 1 (landed_gain_reduction; the gain boost's angle P scale is reset before the attitude
controller runs, see adapter.cpp). -/
def zeroErrorZeroTarget : Clause :=
  let bound (p : String) : Expr := v p * (v "ac_thrust_error_angle" + 0.00001) * 1.001 + 0.00001
  ⟨"zero_error_zero_target", ¬. anyInput ∨. ¬. smallError ∨.
    (abs "target_x" ≤. bound "atc_ang_rll_p" ∧. abs "target_y" ≤. bound "atc_ang_pit_p" ∧.
     abs "target_z" ≤. bound "atc_ang_yaw_p")⟩

/-- `zero_error_zero_target` as restated first, with a fixed tolerance of 0.01 rad/s. Refuted
(seed 24, 200 x 300: 1 step;
ardupilot/modules/attitude/evidence/tested/20261118T173014Z-seed24/
counterexample-zero_error_zero_target.json,
case 143 step 75): an inverted vehicle (roll pi), error quaternion (0.99999988, 0, 2.9e-11,
1.04e-8), thrust-error angle 2^-10 = 9.77e-4 from the acosf of a dot product 8 ulps below 1, yaw
angle P 12: target_z = -0.0117. -/
def zeroErrorZeroTargetSecond : Clause :=
  ⟨"zero_error_zero_target", ¬. anyInput ∨. ¬. smallError ∨.
    (abs "target_x" ≤. 0.01 ∧. abs "target_y" ≤. 0.01 ∧. abs "target_z" ≤. 0.01)⟩

/-- A rate limit ArduPilot treats as off: ang_vel_limit tests `is_zero(radians(limit))`, i.e.
|limit · DEG_TO_RAD| < FLT_EPSILON, so limits below 6.8e-6 deg/s are off, not only 0. -/
def rateOff (limit : String) : Expr := rad (v limit) <. 1.1920929e-7

/-- The guarantee. Against the first statement, three clauses are restated (each refuted
statement is kept in `guaranteeAsFirstStated`; counterexamples and causes below) and one is
added:
* `rate_targets_limited`: ATC_RATE_*_MAX limits the angle-error correction, not the sum.
  attitude_controller_run_quat (AC_AttitudeControl.cpp:1003) applies ang_vel_limit to the
  correction, then adds the feed-forward (:1013-1023), and above a thrust error of 60 degrees
  replaces the yaw target by the gyro (:1014). The feed-forward is shaped with the rate limit as
  velocity limit by the thrust-vector inputs, with Euler-converted limits by the Euler inputs, and
  with no limit by input_rate_bf_roll_pitch_yaw_rads (`0.0` at .cpp:620-622). Refuted at once
  (seed 1, 100 x 100: 7298 violations). Restated: when an input method ran this tick (it is then
  the last writer of _ang_vel_body_rads), each axis is within its limit plus the feed-forward's
  magnitude, and yaw also plus |gyro_z|.
* `throttle_range`: set_throttle_out passes get_throttle_boosted(throttle_in) to
  _motors.set_throttle (AC_AttitudeControl_Multi.cpp:371, 376); the boost factor is
  1 / constrain(cos(thrust angle), 0.1, 1) (:399-400), up to 10. Refuted (seed 1: 642 of 10000
  steps; ardupilot/modules/attitude/evidence/tested/20261118T171525Z-seed1/
  counterexample-throttle_range.json,
  lean 1.165 rad, throttle_in 0.99999994, throttle 2.5358343). ArduCopter hands the mixer
  throttles above 1 whenever it leans with a high throttle (at ANGLE_MAX 30 degrees, from
  throttle_in > 0.866); the mixer filters it and get_throttle() constrains it to [0, 1].
  Restated: 0 ≤ throttle ≤ 10 · throttle_in of the same call (`ac_throttle_in`), and throttle =
  ac_throttle_in when no boost was applied.
* `zero_error_zero_target`: the tolerance 1e-4 was too small. thrust_vector_rotation_angles takes
  the thrust error angle as acosf(constrain(dot, -1, 1)) (.cpp:1076), and a dot product one ulp
  below 1 already gives acosf(0.99999994) = 3.4527e-4 rad: an error quaternion within 1e-6 of
  identity can produce a computed thrust error of several 1e-4 rad, which the angle P (up to 12)
  turns into rate targets of a few 1e-3 rad/s (counterexample: seed 1, case 12 step 12:
  error q4 = 1.46e-11, q3 = -2.7e-10, thrust error angle 3.45e-4, target_z = 1.89e-3).
  Restated with 0.01 rad/s, which seed 24 refuted in turn (`zeroErrorZeroTargetSecond`); now
  stated relative to the computed thrust-error angle (`zeroErrorZeroTarget`).
* added `targets_bounded`: |target| ≤ 1e4 on each axis, the `rate` system's `signals_bounded`. -/
def guarantee : List Clause :=
  let ffb := ffBound
  [⟨"outputs_finite", finiteOutputs⟩,
   ⟨"no_internal_error", "ac_internal_errors" =. 0⟩,
   ⟨"target_quat_unit", abs (sq (v "ac_att_target_q1") + sq (v "ac_att_target_q2") +
      sq (v "ac_att_target_q3") + sq (v "ac_att_target_q4") - 1) ≤. 1e-5⟩,
   ⟨"targets_bounded", abs "target_x" ≤. 10000 ∧. abs "target_y" ≤. 10000 ∧.
      abs "target_z" ≤. 10000⟩,
   ⟨"rate_targets_limited", ¬. anyInput ∨.
      ((rateOff "atc_rate_r_max" ∨. abs "target_x" ≤. rad "atc_rate_r_max" * 1.00001 + ffb) ∧.
       (rateOff "atc_rate_p_max" ∨. abs "target_y" ≤. rad "atc_rate_p_max" * 1.00001 + ffb) ∧.
       (rateOff "atc_rate_y_max" ∨.
          abs "target_z" ≤. rad "atc_rate_y_max" * 1.00001 + ffb + abs "gyro_z"))⟩,
   ⟨"throttle_boosted", 0 ≤. "throttle" ∧. "throttle" ≤. v "ac_throttle_in" * 10 ∧.
      (¬. ("ac_angle_boost" =. 0) ∨. "throttle" =. "ac_throttle_in")⟩,
   ⟨"throttle_avg_max_range", 0 ≤. "throttle_avg_max" ∧. "throttle_avg_max" ≤. 1⟩,
   ⟨"throttle_filter_range", 0 ≤. "throttle_filter_hz" ∧. "throttle_filter_hz" ≤. 100⟩,
   ⟨"pd_scale_range", 0 ≤. "pd_scale_x" ∧. "pd_scale_x" ≤. 1 + v "atc_thr_g_boost" ∧.
      0 ≤. "pd_scale_y" ∧. "pd_scale_y" ≤. 1 + v "atc_thr_g_boost" ∧.
      0 ≤. "pd_scale_z" ∧. "pd_scale_z" ≤. 1⟩,
   ⟨"i_scale_one", "i_scale_x" =. 1 ∧. "i_scale_y" =. 1 ∧. "i_scale_z" =. 1⟩,
   zeroErrorZeroTarget,
   ⟨"lean_limits", 0.17453292 ≤. "ac_lean_angle_max" ∧. "ac_lean_angle_max" ≤. 1.3962635 ∧.
      0.17453292 ≤. "ac_althold_lean_angle_max" ∧. "ac_althold_lean_angle_max" ≤. 1.5707964⟩,
   ⟨"mix_range", 0.1 ≤. "ac_throttle_mix" ∧. "ac_throttle_mix" ≤. 5⟩,
   ⟨"angle_boost_range", abs "ac_angle_boost" ≤. 1⟩]

/-- The contract as first stated. Refuted; kept for the record, not used. -/
def contractAsFirstStated : Contract where
  assume := assumeParams ++ assumeSignalsAsFirstStated ++ assumeCommandsAsFirstStated
  guarantee := guaranteeAsFirstStated

/-- The second statement: the first assumption with the restated guarantee. Refuted by
`targets_bounded` (seed 1, 100 x 100: 13 steps, smallest margin -223709;
ardupilot/modules/attitude/evidence/tested/20261118T171908Z-seed1/counterexample-targets_bounded.json, case
0 step 79: target_x = -33790.5; seed 2: 31 steps, case 19 step 29: target_x = 134487.3). Cause:
gimbal lock. Both cases have est_pitch at -pi/2 (the edge of `euler_range`), and
relax_attitude_controllers sets the target to the body attitude and converts the gyro to Euler
rates with body_to_euler_derivative (AC_AttitudeControl.cpp:257), which divides by cos(pitch)
(:1338-1340) and only refuses when |cos(pitch)| < FLT_EPSILON (:1334); one ulp away from pi/2 the
Euler rates are 1e4 to 1e6 times the gyro. reset_yaw_target_and_rate converts them back with
euler_derivative_to_body (:1281) after zeroing the yaw component, which no longer cancels, and the
input method's shaping starts from that target rate. Kept for the record, not used. -/
def contractSecond : Contract where
  assume := assumeParams ++ assumeSignalsAsFirstStated ++ assumeCommandsAsFirstStated
  guarantee := guarantee

/-- The third statement's assumption: the Euler pitch of the vehicle and of the commanded
attitudes kept 5 degrees away from the vertical (85 degrees; ArduCopter's ANGLE_MAX is at most
80, and input_euler_rate_roll_pitch_yaw_rads constrains its pitch target to 85,
AC_AttitudeControl.cpp:575): see `contractSecond` for why. -/
def assumeSignalsThird : List Clause :=
  assumeSignalsAsFirstStated.map fun c => if c.name != "euler_range" then c else
    ⟨"euler_range", abs "est_roll" ≤. 3.1415927 ∧. abs "est_pitch" ≤. 1.4835298 ∧.
      abs "est_yaw" ≤. 3.1415927⟩

def assumeCommandsThird : List Clause :=
  assumeCommandsAsFirstStated.map fun c => if c.name != "angle_args_bounded" then c else
    ⟨"angle_args_bounded",
      abs "cmd_attitude_input_euler_angle_roll_pitch_euler_rate_yaw_roll" ≤. 3.1415927 ∧.
      abs "cmd_attitude_input_euler_angle_roll_pitch_euler_rate_yaw_pitch" ≤. 1.4835298 ∧.
      abs "cmd_attitude_input_euler_angle_roll_pitch_yaw_roll" ≤. 3.1415927 ∧.
      abs "cmd_attitude_input_euler_angle_roll_pitch_yaw_pitch" ≤. 1.4835298 ∧.
      abs "cmd_attitude_input_euler_angle_roll_pitch_yaw_yaw" ≤. 7 ∧.
      abs "cmd_attitude_input_thrust_vector_heading_yaw_angle" ≤. 7⟩

/-- The third statement. Passed three seeds at 100 x 100, refuted by `targets_bounded` on longer
cases (200 x 300, seeds 4 to 8: 44, 41, 8, 8 and 22 steps; smallest margin -363974, seed 4).
ardupilot/modules/attitude/evidence/tested/20261118T171948Z-seed7/counterexample-targets_bounded.json,
case 36 step 114: the thrust vector of the input_thrust_vector_* commands was (-883, 0, -1.4e-45),
horizontal, so the desired attitude is pitched 90 degrees and the conversions of the previous
paragraph run near gimbal lock; and several input methods ran in one tick, each converting the
shaped target rate between body and Euler frames at a different target attitude, so a rate of
-11484 rad/s carried over from the step before. Kept for the record, not used. -/
def contractThird : Contract where
  assume := assumeParams ++ assumeSignalsThird ++ assumeCommandsThird
  guarantee := guarantee

/-- At most one input method per tick: every flight mode's run() makes one input call (the
flows read for this module: mode.cpp, mode_*.cpp, takeoff.cpp). -/
def singleInput : Clause :=
  let cs := inputCmds.map fun m => v s!"cmd_attitude_{m}"
  let pairs := cs.zipIdx.flatMap fun (a, i) => (cs.drop (i + 1)).map fun b => ¬. (a ∧. b)
  ⟨"single_input", allOf pairs⟩

/-- The fourth statement's signals. Against the third statement:
* `thrust_vec_tilt` in place of `thrust_vec_bounded`: AC_PosControl::get_thrust_vector() is
  (accel_target.x, accel_target.y, -GRAVITY_MSS) (AC_PosControl.cpp:1374-1378) with the
  horizontal acceleration limited by the lean angle limit (at most 80 degrees, so
  |xy| ≤ 9.80665 tan 80 = 55.6); here each horizontal component at most 6 times the upward one,
  a tilt of at most atan(6 sqrt 2) = 83.3 degrees. This, with `single_input`, removes the
  counterexamples of `contractThird`; with them alone, targets reached 5510 rad/s (seeds 4 to 8,
  200 x 300, no violation of 1e4).
* `gyro_bounded` at 35 rad/s (2000 deg/s, the largest gyro range ArduPilot's IMU drivers set)
  instead of 100, and `dt_range` at 0.01 s (the `rate` system's bound) instead of 0.02: not
  forced by a counterexample; with them the largest rate target seen fell from 5510 to 1030
  (relax_attitude_controllers takes the gyro as the target rate, and update_attitude_target
  integrates it over dt). -/
def assumeSignalsFourth : List Clause :=
  assumeSignalsThird.map fun c =>
    if c.name == "gyro_bounded" then
      ⟨"gyro_bounded", abs "gyro_x" ≤. 35 ∧. abs "gyro_y" ≤. 35 ∧. abs "gyro_z" ≤. 35⟩
    else if c.name == "dt_range" then
      ⟨"dt_range", 0 <. "dt" ∧. "dt" ≤. 0.01⟩
    else if c.name == "thrust_vec_bounded" then
      ⟨"thrust_vec_tilt", "thrust_vec_z" <. 0 ∧. -1000 ≤. "thrust_vec_z" ∧.
        abs "thrust_vec_x" ≤. 1000 ∧. abs "thrust_vec_y" ≤. 1000 ∧.
        abs "thrust_vec_x" ≤. -6 * v "thrust_vec_z" ∧. abs "thrust_vec_y" ≤. -6 * v "thrust_vec_z"⟩
    else c

/-- The commands: the third statement's, and at most one input method per tick. -/
def assumeCommands : List Clause := singleInput :: assumeCommandsThird

/-- The fourth statement. Passed eleven campaigns (seeds 21 to 28, 200 x 300, and the regimes),
then refuted by `targets_bounded` on the final build's campaigns (200 x 300, seed 3: 33 steps,
target 867401 rad/s; seed 4: 11 steps, 123770;
ardupilot/modules/attitude/evidence/tested/20261118T173550Z-seed3/counterexample-targets_bounded.json, case
165 step 267). In both, dt is below FLT_EPSILON for several steps in a row:
attitude_command_model returns at once when !is_positive(dt) (AC_AttitudeControl.cpp:1110), so
the shaped target rates neither decay nor follow the input, while reset_target_and_rate(false)
and inertial_frame_reset move the target attitude under them (the pitch at the 85 degree edge),
and each later body/Euler conversion (body_to_euler_derivative, euler_derivative_to_body)
multiplies them by up to 1/cos(85 degrees) = 11.5. Kept for the record, not used. -/
def contractFourth : Contract where
  assume := assumeParams ++ assumeSignalsFourth ++ assumeCommands
  guarantee := guarantee

/-- The signals: the fourth statement's with dt at least 1e-4 s (the mixer's `dt_range`;
ArduCopter's loop time is about 2.5e-3 s, and the scheduler never reports a time step below
FLT_EPSILON). With it no campaign has refuted `targets_bounded` (seeds 1 to 14 and 24 at
200 x 300, 31 to 34 at 60 x 1000), but the largest rate targets seen are 6262 rad/s (seed 9) and
5880 (seed 5): the bound 1e4 is empirical and its margin small. No argument from the code
bounds the target rates under this assumption, because the shaped rate state is carried across
target-attitude changes (inertial_frame_reset, reset_*_and_rate with reset_rate false, every
tick in these campaigns) and multiplied by the body/Euler conversions near 85 degrees of pitch
(previous paragraph). -/
def assumeSignals : List Clause :=
  assumeSignalsFourth.map fun c => if c.name != "dt_range" then c else
    ⟨"dt_range", 0.0001 ≤. "dt" ∧. "dt" ≤. 0.01⟩

/-- The fifth statement (the stage as built alone). Not refuted; replaced when the stages
were composed. Kept for the record, not used. -/
def contractFifth : Contract where
  assume := assumeParams ++ assumeSignals ++ assumeCommands
  guarantee := guarantee

/-- The signals when composed with the position stage. Against the fifth statement:
* `throttle_in_range` widened from [0, 1] to |throttle_in| ≤ 1e15. AC_PosControl does not keep
  the collective in [0, 1] (its guarantee states `hover - (P + D + I + FF)` exactly and, since
  the composition, |throttle_in| ≤ 1e15). set_throttle_out uses throttle_in in
  update_althold_lean_angle_max (constrained to [0, 1] before acosf,
  AC_AttitudeControl_Multi.cpp:360), get_throttle_boosted (a product with factors in [0, 1] and
  [1, 10], :397-403, with _angle_boost constrained to [-1, 1]) and get_throttle_avg_max
  (constrained to [0, 1], :411); a magnitude of 1e15 cannot overflow any of them.
* `pc_throttle_cutoff_range` added: the position stage's set_throttle_out now passes its own
  filter cutoff (before the composition the adapter wrote POSCONTROL_THROTTLE_CUTOFF_FREQ_HZ);
  it goes to the motors' set_throttle_filter_cutoff and so to the output `throttle_filter_hz`,
  which the mixer assumes in [0, 100]. -/
def assumeSignalsComposed : List Clause :=
  (assumeSignals.map fun c => if c.name != "throttle_in_range" then c else
    ⟨"throttle_in_range", abs "throttle_in" ≤. 1e15⟩) ++
  [⟨"pc_throttle_cutoff_range", ¬. "pc_throttle_set" ∨.
      (0 ≤. "pc_throttle_cutoff_hz" ∧. "pc_throttle_cutoff_hz" ≤. 100)⟩]

/-- The guarantee when composed. Against the fifth statement:
* `throttle_boosted` restated for a throttle_in of either sign: |throttle| ≤ 10 |ac_throttle_in|
  (the fifth statement's `0 ≤ throttle ≤ 10 ac_throttle_in` assumed throttle_in ≥ 0; with a
  negative collective the boosted throttle is negative, get_throttle_boosted multiplies by
  factors ≥ 0). Kept on record as `throttleBoostedFifth`.
* `lean_limits` tightened by one ulp: lean_angle_max_rad() ≤ 1.3962634 (binary32
  1.39626336, radians(80) as ArduPilot computes it) instead of 1.3962635 (binary32 1.39626348),
  so that it implies the position stage's `ac_lean_range`, which uses the former.
* `ac_throttle_in_bounded` added: |ac_throttle_in| ≤ 1e15 (it is the argument of the last
  set_throttle_out, the position stage's throttle_in or the mode's own, 0 before any), for the
  position stage's `ac_throttle_range`.
* `att_target_euler_range` added: the target's roll and pitch within ±π, for the position
  stage's `ac_att_target_range`. Every write of _euler_angle_target_rad.x/.y is to_euler's
  atan2f/asinf, a command argument (bounded by `angle_args_bounded`), wrap_PI or the ±85 degree
  constraint (AC_AttitudeControl.cpp:442-443, 513-514, 574-575). First stated with the yaw as
  well (`attTargetEulerAsFirstStated`), refuted at once (seed 1, 200 x 100: 167 steps, first at
  case 11 step 22, yaw target 7): input_euler_angle_roll_pitch_yaw_rad without rate
  feed-forward stores the yaw argument as given (:522), input_euler_angle_roll_pitch_euler_rate_
  yaw_rad without it integrates the yaw rate with no wrap (:444), and
  input_euler_rate_roll_pitch_yaw_rads wraps to [0, 2π) (:576). The yaw target has no bound but
  finiteness; the position stage's assumption on it stays an open obligation. -/
def attTargetEulerAsFirstStated : Clause :=
  ⟨"att_target_euler_range", abs "ac_att_target_roll" ≤. 3.1415927 ∧.
      abs "ac_att_target_pitch" ≤. 3.1415927 ∧. abs "ac_att_target_yaw" ≤. 3.1415927⟩
def throttleBoostedFifth : Clause :=
  ⟨"throttle_boosted", 0 ≤. "throttle" ∧. "throttle" ≤. v "ac_throttle_in" * 10 ∧.
      (¬. ("ac_angle_boost" =. 0) ∨. "throttle" =. "ac_throttle_in")⟩

def guaranteeComposed : List Clause :=
  (guarantee.map fun c =>
    if c.name == "throttle_boosted" then
      ⟨"throttle_boosted", abs "throttle" ≤. abs (v "ac_throttle_in") * 10 ∧.
        (¬. ("ac_angle_boost" =. 0) ∨. "throttle" =. "ac_throttle_in")⟩
    else if c.name == "lean_limits" then
      ⟨"lean_limits", 0.17453292 ≤. "ac_lean_angle_max" ∧. "ac_lean_angle_max" ≤. 1.3962634 ∧.
        0.17453292 ≤. "ac_althold_lean_angle_max" ∧. "ac_althold_lean_angle_max" ≤. 1.5707964⟩
    else c) ++
  [⟨"ac_throttle_in_bounded", abs "ac_throttle_in" ≤. 1e15⟩,
   ⟨"att_target_euler_range", abs "ac_att_target_roll" ≤. 3.1415927 ∧.
      abs "ac_att_target_pitch" ≤. 3.1415927⟩]

/-- The parameters when composed: the angle P gains up to 30 (documented 3 to 12,
AC_AttitudeControl.cpp @Range). The X500's autotuned gains (ArduPilot's
Tools/Frame_params/Holybro-X500v2-bdshot.param, as the simulator's parameter list uses them)
are ATC_ANG_RLL_P 26.36 and ATC_ANG_PIT_P 21.22: an @Range is advice to the ground station,
not a limit the code enforces. Tested with the composed contract (see the ledger). -/
def assumeParamsComposed : List Clause :=
  assumeParams.map fun c => if c.name != "ang_p_range" then c else
    ⟨"ang_p_range", 3 ≤. "atc_ang_rll_p" ∧. "atc_ang_rll_p" ≤. 30 ∧. 3 ≤. "atc_ang_pit_p" ∧.
      "atc_ang_pit_p" ≤. 30 ∧. 3 ≤. "atc_ang_yaw_p" ∧. "atc_ang_yaw_p" ≤. 30⟩

/-- The guarantee with the supervisor's call order (`_seq`). `rate_targets_limited` and
`zero_error_zero_target` are conditioned on "an input method ran this tick", which in the fixed
order makes it the last writer of the rate targets. With random `_seq` they were refuted
(seed 11, 200 x 100: rate_targets_limited 265 steps, zero_error_zero_target 324; flight seed 12:
rate_targets_limited 3): a relax_attitude_controllers or reset_*_target_and_rate after the input
sets the target from the body attitude and the rate targets from the gyro, which no limit
bounds. Restated with `ac_input_last` (the input was the last call that set the target, always
true when an input ran in the fixed order) in place of `anyInput`. -/
def guaranteeSeq : List Clause :=
  guaranteeComposed.map fun c =>
    if c.name == "rate_targets_limited" || c.name == "zero_error_zero_target" then
      match c.expr with
      | .or _ rest => ⟨c.name, .or (¬. "ac_input_last") rest⟩
      | e => ⟨c.name, e⟩
    else c

/-- The contract. -/
def contract : Contract where
  assume := assumeParamsComposed ++ assumeSignalsComposed ++ assumeCommands
  guarantee := guaranteeSeq

/-! ### Regimes and coverage -/

/-- ArduCopter's default ATC_ parameters (libraries/AC_AttitudeControl, read only):
RATE_FF_ENAB 1 (AC_AttitudeControl.h:32, .cpp:47), ANGLE_BOOST 1 (.cpp:60), ANG_RLL/PIT/YAW_P 4.5
(.h:15, constructor .h:51-53), ANG_LIM_TC 1.0 (.h:34, .cpp:94), RATE_R/P/Y_MAX 0 (.cpp:104, 114,
124), INPUT_TC 0.1 (Copter, .cpp:16, 134), LAND_R/P/Y_MULT 1 (.cpp:141, 148, 155), ANGLE_MAX 30
(.cpp:26, 164), RATE_WPY_MAX 60 (.h:21, .cpp:173), ACC_Y_MAX 270 (.h:23, .cpp:183), ACC_R/P_MAX
1100 (.h:22, .cpp:193, 203), THR_MIX_MIN 0.1, THR_MIX_MAX 0.5, THR_MIX_MAN 0.1 (.h:37-39;
AC_AttitudeControl_Multi.cpp:311, 318, 325), THR_G_BOOST 0 (Multi.cpp:332), RAT_YAW_P 0.18
(AC_AttitudeControl_Multi.h:26). -/
def stockParams : List Clause := [
  ⟨"stock_flags", "atc_rate_ff_enab" =. tt ∧. "atc_angle_boost" =. tt⟩,
  ⟨"stock_angle_p", "atc_ang_rll_p" =. 4.5 ∧. "atc_ang_pit_p" =. 4.5 ∧. "atc_ang_yaw_p" =. 4.5⟩,
  ⟨"stock_limits", "atc_ang_lim_tc" =. 1 ∧. "atc_rate_r_max" =. 0 ∧. "atc_rate_p_max" =. 0 ∧.
      "atc_rate_y_max" =. 0 ∧. "atc_input_tc" =. 0.1 ∧. "atc_angle_max" =. 30 ∧.
      "atc_rate_wpy_max" =. 60⟩,
  ⟨"stock_land", "atc_land_r_mult" =. 1 ∧. "atc_land_p_mult" =. 1 ∧. "atc_land_y_mult" =. 1⟩,
  ⟨"stock_accel", "atc_acc_y_max" =. 270 ∧. "atc_acc_r_max" =. 1100 ∧. "atc_acc_p_max" =. 1100⟩,
  ⟨"stock_mix", "atc_thr_mix_min" =. 0.1 ∧. "atc_thr_mix_max" =. 0.5 ∧.
      "atc_thr_mix_man" =. 0.1 ∧. "atc_thr_g_boost" =. 0 ∧. "yaw_kp" =. 0.18⟩]

/-- Flight-like signals: 400 Hz, attitude within 45 degrees of level, body rates within 3 rad/s,
a thrust vector near hover (pointing up, within about 45 degrees), throttle near hover. -/
def flightSignals : List Clause := [
  ⟨"flight_dt", 0.0024 ≤. "dt" ∧. "dt" ≤. 0.0026⟩,
  ⟨"flight_attitude", abs "est_roll" ≤. 0.8 ∧. abs "est_pitch" ≤. 0.8⟩,
  ⟨"flight_gyro", abs "gyro_x" ≤. 3 ∧. abs "gyro_y" ≤. 3 ∧. abs "gyro_z" ≤. 3⟩,
  ⟨"flight_thrust", abs "thrust_vec_x" ≤. 8 ∧. abs "thrust_vec_y" ≤. 8 ∧.
      -15 ≤. "thrust_vec_z" ∧. "thrust_vec_z" ≤. -8⟩,
  ⟨"flight_throttle", 0.2 ≤. "throttle_in" ∧. "throttle_in" ≤. 0.6 ∧.
      0.2 ≤. "throttle_filtered" ∧. "throttle_filtered" ≤. 0.6 ∧. "throttle_out" ≤. 1 ∧.
      "throttle_slew_rate" ≤. 2 ∧. 0.9 ≤. "throttle_thrust_max" ∧. "throttle_hover" =. 0.35⟩,
  ⟨"flight_args", abs "cmd_attitude_input_euler_angle_roll_pitch_euler_rate_yaw_roll" ≤. 0.5 ∧.
      abs "cmd_attitude_input_euler_angle_roll_pitch_euler_rate_yaw_pitch" ≤. 0.5 ∧.
      abs "cmd_attitude_input_euler_angle_roll_pitch_yaw_roll" ≤. 0.5 ∧.
      abs "cmd_attitude_input_euler_angle_roll_pitch_yaw_pitch" ≤. 0.5 ∧.
      abs "cmd_attitude_input_euler_angle_roll_pitch_euler_rate_yaw_yaw_rate" ≤. 2 ∧.
      abs "cmd_attitude_input_rate_bf_roll_pitch_yaw_roll_rate" ≤. 2 ∧.
      abs "cmd_attitude_input_rate_bf_roll_pitch_yaw_pitch_rate" ≤. 2 ∧.
      abs "cmd_attitude_input_rate_bf_roll_pitch_yaw_yaw_rate" ≤. 2 ∧.
      abs "cmd_attitude_input_thrust_vector_rate_heading_heading_rate" ≤. 2 ∧.
      abs "cmd_attitude_input_thrust_vector_heading_yaw_rate" ≤. 2 ∧.
      0.2 ≤. "cmd_attitude_set_throttle_out_throttle_in" ∧.
      "cmd_attitude_set_throttle_out_throttle_in" ≤. 0.6⟩,
  ⟨"flight_no_resets", "cmd_attitude_relax_attitude_controllers" =. ff ∧.
      "cmd_attitude_reset_target_and_rate" =. ff ∧. "cmd_attitude_inertial_frame_reset" =. ff⟩]

/-- Flight: flight-like signals and commands with any parameters in their documented ranges. -/
def flight : Regime where
  name := "flight"
  doc := "flight-like signals and commands, 400 Hz, parameters anywhere in their ranges"
  clauses := flightSignals

/-- The stock vehicle in flight. -/
def stockFlight : Regime where
  name := "stock_flight"
  doc := "ArduCopter's default ATC_ parameters, flight-like signals and commands, 400 Hz"
  clauses := stockParams ++ flightSignals

/-- A level vehicle at rest holding a level attitude (input_euler_angle_roll_pitch_yaw with
zero angles is the only input method; resets allowed): the case `zero_error_zero_target` is
about. -/
def levelHold : Regime where
  name := "level_hold"
  doc := "level vehicle, zero gyro, input_euler_angle_roll_pitch_yaw(0, 0, 0) every tick"
  clauses := [
    ⟨"level_body", "est_roll" =. 0 ∧. "est_pitch" =. 0 ∧. "est_yaw" =. 0 ∧. "gyro_x" =. 0 ∧.
        "gyro_y" =. 0 ∧. "gyro_z" =. 0⟩,
    ⟨"level_command", "cmd_attitude_input_euler_angle_roll_pitch_yaw" =. tt ∧.
        "cmd_attitude_input_euler_angle_roll_pitch_yaw_roll" =. 0 ∧.
        "cmd_attitude_input_euler_angle_roll_pitch_yaw_pitch" =. 0 ∧.
        "cmd_attitude_input_euler_angle_roll_pitch_yaw_yaw" =. 0⟩,
    ⟨"level_only_input", "cmd_attitude_input_euler_angle_roll_pitch_euler_rate_yaw" =. ff ∧.
        "cmd_attitude_input_rate_bf_roll_pitch_yaw" =. ff ∧.
        "cmd_attitude_input_thrust_vector_rate_heading" =. ff ∧.
        "cmd_attitude_input_thrust_vector_heading" =. ff⟩]

/-- What a campaign counts. -/
def coverage : List Clause := [
  ⟨"any_input", anyInput⟩,
  ⟨"thrust_error_over_30deg", 0.5235988 <. "ac_thrust_error_angle"⟩,
  ⟨"thrust_error_over_60deg", 1.0471976 <. "ac_thrust_error_angle"⟩,
  ⟨"angle_boost_active", 0 <. abs "ac_angle_boost"⟩,
  ⟨"gain_boost_active", 1 <. "pd_scale_x"⟩,
  ⟨"landed_gain_active", "pd_scale_x" <. 1⟩,
  ⟨"mix_not_min", ¬. "ac_throttle_mix_min"⟩,
  ⟨"rate_reset_i", "ac_rate_reset_i"⟩,
  ⟨"rate_relax_i", "ac_rate_relax_i"⟩,
  ⟨"small_error", abs "ac_att_error_q2" ≤. 1e-6 ∧. abs "ac_att_error_q3" ≤. 1e-6 ∧.
      abs "ac_att_error_q4" ≤. 1e-6⟩]

def module : Module where
  name := "attitude"
  doc := "ArduCopter's AC_AttitudeControl_Multi: attitude inputs to rate targets and throttle"
  params := params
  input := input
  output := output
  contract := contract
  exe := "build/modules/attitude/attitude"
  stack := .ardupilot
  regimes := [flight, stockFlight, levelHold]
  coverage := coverage

end Ardupilot.Modules.Attitude
