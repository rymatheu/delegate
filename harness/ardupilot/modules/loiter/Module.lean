import Harness.Module

/-! # loiter: ArduCopter's loiter controller

One `AC_Loiter` (libraries/AC_WPNav/AC_Loiter.cpp), built as ArduCopter builds it
(Copter::allocate_motors, system.cpp:499-503: `AC_Loiter(*ahrs_view, *pos_control,
*attitude_control)`), with its parameters (LOIT_*) from the parameter record, stepped once per
400 Hz tick. It sits where the guidance stage sits, after the supervisor and before the position
stage. The executable is built by `ardupilot/build.sh loiter` from the real, unmodified sources in
sources.txt and local_sources.txt; adapter.cpp describes the cut and stubs_*.cpp what is outside.

AC_Loiter computes with three functions of the other controllers that return a value within the
call and depend on this tick's pilot sticks, so they cannot be signals of a stage that runs later:
* `AC_AttitudeControl::command_model_rate_predictor` (AC_Loiter.cpp:191) and
  `AC_AttitudeControl::lean_angle_max_rad` (:239, :309): AC_AttitudeControl.cpp is compiled here,
  the real file, and called on an attitude object whose parameter members are the attitude
  stage's parameters under the same names (ATC_*), so `composeAll` gives both stages one value;
* `AC_PosControl::lean_angles_rad_to_accel_NED_mss` (:180, :198): AC_PosControl.cpp is compiled
  here too, the real file, under the class name AC_PosControl_Real (pos_real.cpp), because the
  class AC_PosControl's other out-of-line methods are this stage's hand-over stand-ins.
Of those two files only these functions are in the executable (the linker removes the rest). No
control code is written here.

The calls AC_Loiter makes on the position controller are handed to the position stage, as the
guidance stage hands AC_WPNav's (outputs `lt_…`, the position stage's inputs of the same names):
* the methods the guidance stage also hands over keep its port names with `lt_` in front:
  `NE_init_controller_stopping_point` (`lt_tgt_ne_init_stopping_point`),
  `NE_set_correction_speed_accel_m` (`lt_tgt_ne_set_correction_speed_accel`, `_speed`, `_accel`),
  both at `lt_tgt_handover_seq`; `set_pos_vel_accel_NE_m` then `NE_update_controller` (update) as
  `lt_tgt_valid`, `lt_tgt_pos/vel/acc_n/e`, `lt_tgt_ne_update` at `lt_tgt_update_seq`;
* the methods guidance does not use are `lt_cmd_position_<method>[_<arg>]` with their own `_seq`:
  `NE_set_pos_error_max_m`, `set_pos_desired_NE_m`, `NE_relax_velocity_controller`,
  `NE_soften_for_landing` (the supervisor's own `cmd_position_…` of those names stay its own).
Each `_seq` is the `_seq` of the supervisor's `cmd_loiter_…` command during which the call was
made; within one command the calls keep AC_Loiter's order, which the position stage's fixed
order for these ports follows.

The position state AC_Loiter reads is the position stage's output of the previous tick
(`pc_…`), as for the guidance stage; where AC_Loiter reads a member right after its own hand-over
call changed it, the assignment of that call is applied first (stubs_posctl.cpp lists them and
the reads that stay one tick old).

The supervisor's calls (`cmd_loiter_<method>`, `_seq`, arguments): set_speed_max_NE_ms,
set_pilot_desired_acceleration_rad (clear_pilot_desired_acceleration is the inline call of it
with 0, 0), soften_for_landing, init_target_m, init_target, update. Executed in that fixed order
(ModeLoiter::run's, mode_loiter.cpp:84-161) when every `_seq` is 0, else in `_seq` order. What the
mode reads back: get_angle_max_rad (output `lt_angle_max`; the supervisor computes the same
parameter function itself), get_pilot_desired_acceleration_NE_mss (`lt_desired_accel_n/e`), and
the pass-throughs get_roll_rad, get_pitch_rad, get_thrust_vector, get_distance_to_target_m,
get_bearing_to_target_rad (AC_Loiter.h:57-100), which return the position stage's own values:
the supervisor reads them from the position stage (`pc_roll`, `pc_pitch`, `thrust_vec_*`,
`pc_pos_error_*`), and they are not repeated here.

Positions are `postype_t` = double in this build (HAL_WITH_POSTYPE_DOUBLE, SITL); they cross the
ports as binary32 (inputs widen exactly, outputs round to the nearest binary32). -/

namespace Ardupilot.Modules.Loiter

open Harness Harness.Contract.Lang

private def f (n d : String) : Field := { name := n, type := .f32, doc := d }
private def b (n d : String) : Field := { name := n, type := .bool, doc := d }
private def u (n d : String) : Field := { name := n, type := .u32, doc := d }

def params : Schema := #[
  f "loit_ang_max" "LOIT_ANG_MAX, deg; 0: 2/3 of the lean limit (_angle_max_deg)",
  f "loit_speed_ms" "LOIT_SPEED_MS, m/s (_speed_max_ne_ms)",
  f "loit_acc_max_m" "LOIT_ACC_MAX_M, m/s/s (_accel_max_ne_mss)",
  f "loit_brk_acc_m" "LOIT_BRK_ACC_M, m/s/s (_brake_accel_max_mss)",
  f "loit_brk_jrk_m" "LOIT_BRK_JRK_M, m/s/s/s (_brake_jerk_max_msss)",
  f "loit_brk_delay" "LOIT_BRK_DELAY, s (_brake_delay_s)",
  u "loit_options" "LOIT_OPTIONS bitmask (_options, AP_UInt8; bit 0 coordinated turns)",
  b "atc_rate_ff_enab" "ATC_RATE_FF_ENAB (the attitude stage's; _rate_bf_ff_enabled)",
  f "atc_rate_r_max" "ATC_RATE_R_MAX, deg/s, 0 off (_ang_vel_roll_max_degs)",
  f "atc_rate_p_max" "ATC_RATE_P_MAX, deg/s, 0 off (_ang_vel_pitch_max_degs)",
  f "atc_acc_r_max" "ATC_ACC_R_MAX, deg/s/s, 0 off (_accel_roll_max_degss)",
  f "atc_acc_p_max" "ATC_ACC_P_MAX, deg/s/s, 0 off (_accel_pitch_max_degss)",
  f "atc_input_tc" "ATC_INPUT_TC, s (_input_tc)",
  f "atc_angle_max" "ATC_ANGLE_MAX, deg (_angle_max_deg; lean_angle_max_rad)",
  f "atc_ang_rll_p" "ATC_ANG_RLL_P (_p_angle_roll; the predictor without feed-forward)",
  f "atc_ang_pit_p" "ATC_ANG_PIT_P (_p_angle_pitch)",
  f "psc_ne_vel_p" "PSC_NE_VEL_P (the position stage's _pid_vel_ne_m.kP(): the brake gain)"]

/-- A command of the supervisor: its Boolean, its arguments and its `_seq`. -/
private def cmd (m doc : String) (args : List Field) : List Field :=
  b s!"cmd_loiter_{m}" s!"AC_Loiter::{doc} is called this tick" ::
    args.map (fun a => { a with name := s!"cmd_loiter_{m}_{a.name}",
                                doc := s!"{m}: argument {a.doc}" }) ++
    [u s!"cmd_loiter_{m}_seq" s!"{m}: place in the supervisor's call order (0: not sequenced)"]

def commands : List Field :=
  cmd "set_speed_max_NE_ms" "set_speed_max_NE_ms" [f "speed" "speed_max_NE_ms, m/s"] ++
  cmd "set_pilot_desired_acceleration_rad" "set_pilot_desired_acceleration_rad"
    [f "roll" "euler_roll_angle_rad", f "pitch" "euler_pitch_angle_rad"] ++
  cmd "soften_for_landing" "soften_for_landing" [] ++
  cmd "init_target_m" "init_target_m" [f "n" "position_ne_m.x, m", f "e" "position_ne_m.y, m"] ++
  cmd "init_target" "init_target" [] ++
  cmd "update" "update" [b "avoidance_on" "avoidance_on (no effect: avoidance compiled out)"]

def signals : List Field := [
  f "dt" "AC_PosControl::get_dt_s() and AC_AttitudeControl::get_dt_s(): last loop time, s \
    (Copter::run_rate_controller_main sets both, Attitude.cpp:14-15)",
  u "now_ms" "the clock AP_HAL::millis() reads (the brake timer)",
  f "est_yaw" "AP_AHRS_View::yaw, rad (the estimator, this tick)",
  f "est_gnd_spd_limit" "AP_AHRS::get_control_ground_speed_limit_ms(), m/s (the estimator, this tick)",
  f "pc_vel_desired_n" "AC_PosControl::get_vel_desired_NED_ms().x, m/s (previous tick)",
  f "pc_vel_desired_e" "get_vel_desired_NED_ms().y",
  f "pc_pos_desired_n" "AC_PosControl::get_pos_desired_NED_m().x, m (previous tick)",
  f "pc_pos_desired_e" "get_pos_desired_NED_m().y",
  f "pc_accel_target_n" "AC_PosControl::get_accel_target_NED_mss().x, m/s/s (previous tick)",
  f "pc_accel_target_e" "get_accel_target_NED_mss().y",
  f "pc_roll" "AC_PosControl::get_roll_rad(), rad (previous tick)",
  f "pc_pitch" "AC_PosControl::get_pitch_rad(), rad (previous tick)",
  f "pc_stopping_point_n" "AC_PosControl::get_stopping_point_NE_m().x, m (previous tick)",
  f "pc_stopping_point_e" "get_stopping_point_NE_m().y",
  f "pc_lean_angle_max" "AC_PosControl::get_lean_angle_max_rad(), rad (previous tick)",
  f "ac_att_target_roll" "AC_AttitudeControl::get_att_target_euler_rad().x, rad (previous \
    tick): what NE_relax_velocity_controller copies into the roll target",
  f "ac_att_target_pitch" "get_att_target_euler_rad().y, rad"]

def input : Schema := (signals ++ commands).toArray

def output : Schema := #[
  b "lt_tgt_ne_init_stopping_point" "AC_Loiter called NE_init_controller_stopping_point",
  b "lt_tgt_ne_set_correction_speed_accel" "AC_Loiter called NE_set_correction_speed_accel_m",
  f "lt_tgt_ne_correction_speed" "its speed_ne_ms argument (last call), m/s",
  f "lt_tgt_ne_correction_accel" "its accel_ne_mss argument (last call), m/s/s",
  u "lt_tgt_handover_seq" "the `_seq` of the command during which the first of those two was \
    called (0: not sequenced)",
  b "lt_cmd_position_NE_set_pos_error_max_m" "AC_Loiter called NE_set_pos_error_max_m",
  f "lt_cmd_position_NE_set_pos_error_max_m_error_max" "its error_max_m argument, m",
  u "lt_cmd_position_NE_set_pos_error_max_m_seq" "its `_seq`",
  b "lt_cmd_position_set_pos_desired_NE_m" "AC_Loiter called set_pos_desired_NE_m",
  f "lt_cmd_position_set_pos_desired_NE_m_n" "its pos_desired_ne_m.x, m",
  f "lt_cmd_position_set_pos_desired_NE_m_e" "its pos_desired_ne_m.y, m",
  u "lt_cmd_position_set_pos_desired_NE_m_seq" "its `_seq`",
  b "lt_cmd_position_NE_relax_velocity_controller" "AC_Loiter called NE_relax_velocity_controller",
  u "lt_cmd_position_NE_relax_velocity_controller_seq" "its `_seq`",
  b "lt_cmd_position_NE_soften_for_landing" "AC_Loiter called NE_soften_for_landing",
  u "lt_cmd_position_NE_soften_for_landing_seq" "its `_seq`",
  b "lt_tgt_valid" "AC_Loiter called set_pos_vel_accel_NE_m (calc_desired_velocity)",
  b "lt_tgt_ne_update" "AC_Loiter called NE_update_controller (update)",
  u "lt_tgt_update_seq" "the `_seq` of the command during which set_pos_vel_accel_NE_m was called",
  f "lt_tgt_pos_n" "set_pos_vel_accel_NE_m: pos_ne_m.x, m (0 when not called)",
  f "lt_tgt_pos_e" "pos_ne_m.y, m",
  f "lt_tgt_vel_n" "vel_ne_ms.x, m/s",
  f "lt_tgt_vel_e" "vel_ne_ms.y, m/s",
  f "lt_tgt_acc_n" "accel_ne_mss.x, m/s/s",
  f "lt_tgt_acc_e" "accel_ne_mss.y, m/s/s",
  f "lt_angle_max" "get_angle_max_rad() after the step, rad",
  f "lt_att_lean_angle_max" "the attitude object's lean_angle_max_rad() (ATC_ANGLE_MAX), rad",
  f "lt_desired_accel_n" "get_pilot_desired_acceleration_NE_mss().x (_desired_accel_ne_mss), m/s/s",
  f "lt_desired_accel_e" "get_pilot_desired_acceleration_NE_mss().y",
  f "lt_predicted_accel_n" "_predicted_accel_ne_mss.x, m/s/s",
  f "lt_predicted_accel_e" "_predicted_accel_ne_mss.y",
  f "lt_predicted_roll" "_predicted_euler_angle_rad.x, rad",
  f "lt_predicted_pitch" "_predicted_euler_angle_rad.y, rad",
  f "lt_predicted_roll_rate" "_predicted_euler_rate.x, rad/s",
  f "lt_predicted_pitch_rate" "_predicted_euler_rate.y, rad/s",
  f "lt_predicted_roll_accel" "_predicted_euler_accel.x, rad/s/s",
  f "lt_predicted_pitch_accel" "_predicted_euler_accel.y, rad/s/s",
  f "lt_brake_accel" "_brake_accel_mss, m/s/s",
  u "lt_brake_timer_ms" "_brake_timer_ms: the clock at the last non-zero pilot request, ms",
  f "lt_speed_max" "_speed_max_ne_ms after the step (sanity-checked LOIT_SPEED_MS), m/s",
  f "lt_accel_max" "_accel_max_ne_mss after the step (sanity-checked LOIT_ACC_MAX_M), m/s/s",
  f "lt_stopping_point_n" "get_stopping_point_NE_m().x, m",
  f "lt_stopping_point_e" "get_stopping_point_NE_m().y, m",
  b "lt_update_ran" "update ran this tick",
  b "lt_update_last" "update ran and was the last command of the tick",
  b "lt_pilot_set" "set_pilot_desired_acceleration_rad ran this tick",
  b "lt_pilot_before_update" "it ran, and not after update",
  u "lt_internal_errors" "AP_InternalError count (none is raised on the step path)"]

/-! ### The contract -/

private def conj : List Expr → Expr
  | [] => .blit true
  | [e] => e
  | e :: es => e ∧. conj es

private def within (x : String) (lo hi : Expr) : Expr := lo ≤. .var x ∧. .var x ≤. hi
private def absLe (xs : List String) (c : Expr) : Expr := conj (xs.map fun x => abs (.var x) ≤. c)
private def cl (s : String) : String := s!"cmd_loiter_{s}"
private def called (m : String) (e : Expr) : Expr := ¬. .var (cl m) ∨. e
private def sq (x : Expr) : Expr := x * x
private def v (n : String) : Expr := .var n

/-- ArduPilot's documented ranges (@Range in AC_Loiter.cpp:29-94; the attitude stage's ranges for
ATC_*, its composed `ang_p_range`; the position stage's for PSC_NE_VEL_P). -/
def assumeParams : List Clause := [
  ⟨"loit_range", within "loit_ang_max" 0 45 ∧. within "loit_brk_delay" 0 2 ∧.
      within "loit_speed_ms" 0.2 35 ∧. within "loit_acc_max_m" 1 9.81 ∧.
      within "loit_brk_acc_m" 0.25 2.5 ∧. within "loit_brk_jrk_m" 5 50⟩,
  -- bit 0 (coordinated turns) reads the attitude stage's target angular velocity
  -- (AC_Loiter.cpp:202-208), which is not a port of this stage
  ⟨"no_coordinated_turn", "loit_options" =. 0⟩,
  -- with ATC_RATE_FF_ENAB off the predictor reads the attitude stage's _angle_P_scale of this
  -- tick (AC_AttitudeControl.cpp:1141-1142), set by its landed_gain_reduction, not a port
  ⟨"rate_ff_enabled", "atc_rate_ff_enab"⟩,
  ⟨"atc_range", within "atc_rate_r_max" 0 1080 ∧. within "atc_rate_p_max" 0 1080 ∧.
      within "atc_acc_r_max" 0 1800 ∧. within "atc_acc_p_max" 0 1800 ∧.
      within "atc_input_tc" 0 1 ∧. within "atc_angle_max" 10 80 ∧.
      within "atc_ang_rll_p" 3 30 ∧. within "atc_ang_pit_p" 3 30⟩,
  ⟨"psc_ne_vel_p_range", within "psc_ne_vel_p" 0.1 10⟩]

/-- The signals. -/
def assumeSignals : List Clause := [
  ⟨"dt_range", within "dt" 0.0001 0.02⟩,
  ⟨"est_yaw_range", abs "est_yaw" ≤. 3.1415927⟩,
  -- 400 from EKF3 when not relying on optical flow (AP_NavEKF3_Outputs.cpp:390), 50 from DCM
  -- (AP_AHRS_DCM.cpp:298); 0 before the estimator's boot
  ⟨"gnd_spd_limit_range", within "est_gnd_spd_limit" 0 1000⟩,
  ⟨"pc_signals_bounded", absLe ["pc_vel_desired_n", "pc_vel_desired_e", "pc_accel_target_n",
      "pc_accel_target_e"] 100 ∧. absLe ["pc_pos_desired_n", "pc_pos_desired_e"] 9000 ∧.
      absLe ["pc_stopping_point_n", "pc_stopping_point_e"] 10000 ∧.
      absLe ["pc_roll", "pc_pitch"] 3.1415927⟩,
  -- radians(PSC_ANGLE_MAX) or lean_angle_max_rad(); 0 before the position stage's first step
  ⟨"pc_lean_range", within "pc_lean_angle_max" 0 1.3962635⟩,
  ⟨"ac_att_target_range", absLe ["ac_att_target_roll", "ac_att_target_pitch"] 3.1415927⟩]

/-- The command arguments, when the command is called. The pilot's lean angles are what
get_pilot_desired_lean_angles_rad gives, limited by get_angle_max_rad() (at most 2/3 of 80 deg or
LOIT_ANG_MAX's 45 deg, below 1 rad). -/
def assumeCommands : List Clause := [
  ⟨"pilot_angles_range", called "set_pilot_desired_acceleration_rad"
      (absLe [cl "set_pilot_desired_acceleration_rad_roll",
        cl "set_pilot_desired_acceleration_rad_pitch"] 1)⟩,
  ⟨"init_target_m_range", called "init_target_m"
      (absLe [cl "init_target_m_n", cl "init_target_m_e"] 9000)⟩,
  ⟨"speed_max_range", called "set_speed_max_NE_ms" (within (cl "set_speed_max_NE_ms_speed") 0 100)⟩]

/-- Every f32 output. -/
def floatOutputs : List String := (output.toList.filter (·.type == .f32)).map (·.name)

/-- FLT_EPSILON, the threshold of is_positive and is_zero for float (AP_Math.h:68). -/
def fltEps : Expr := 1.1920929e-7

/-- |lt_tgt_vel|² -/
def tgtSpeedSq : Expr := sq "lt_tgt_vel_n" + sq "lt_tgt_vel_e"

/-- The guarantee, each clause from the code:
* `angle_max_within_position_limit`: get_angle_max_rad() is `MIN(a, p) * 2/3` or
  `MIN(radians(LOIT_ANG_MAX), p)` with p = the position stage's get_lean_angle_max_rad() ≥ 0
  (AC_Loiter.cpp:237-242): at most p (a product with 2/3 rounds to at most its exact value);
* `angle_max_two_thirds`: with LOIT_ANG_MAX not positive, at most the attitude lean limit a;
* `att_lean_from_parameter`: lean_angle_max_rad() = radians(constrain(ATC_ANGLE_MAX, 10, 80))
  (AC_AttitudeControl.cpp:1419-1422), the constraint inactive in the assumed range;
* `speed_max_floor`: _speed_max_ne_ms is set only through MAX(…, 0.2) (AC_Loiter.cpp:259, 306)
  and starts at LOIT_SPEED_MS ≥ 0.2;
* `accel_max_bounded`: sanity_check_params only lowers _accel_max_ne_mss, to at least
  g tan(10 deg) > 0 (AC_Loiter.cpp:309);
* `brake_accel_range`: _brake_accel_mss moves toward a target constrained to [0, LOIT_BRK_ACC_M]
  by at most the jerk step and never past it (AC_Loiter.cpp:355-362), from 0 (init, zeroed
  storage), up to rounding;
* `handover_constants`: init_target and init_target_m hand NE_set_correction_speed_accel_m
  (LOITER_VEL_CORRECTION_MAX_MS = 2, _accel_max_ne_mss) and NE_set_pos_error_max_m
  (LOITER_POS_CORRECTION_MAX_M = 2) (AC_Loiter.cpp:22-23, 118-119, 141-142);
* `vel_within_speed_limit`: the velocity handed is limited to
  max(min(_speed_max_ne_ms, ekf limit), 0.2) (AC_Loiter.cpp:329-330, 374-377; the avoidance
  block is compiled out), when update was the last command (a later set_speed_max_NE_ms changes
  `lt_speed_max`); squared, with a relative tolerance 1e-5 for the scaling's rounding;
* `accel_bounded`: with the pilot's angles within 1 rad (`pilot_angles_range`) and set in the
  same tick before update, the acceleration handed is lean_angles_rad_to_accel_NED_mss's (each
  component at most g (|sin p| + |sin r|) / (cos r cos p) ≤ 2 g sin 1 / cos² 1 = 56.6) minus the
  brake vector (|.| ≤ LOIT_BRK_ACC_M ≤ 2.5): at most 60 per component. Without set_pilot in the
  tick update subtracts the brake again from the last request (AC_Loiter.cpp:371);
* `pos_follows_vel`: the position handed is the previous desired position plus the handed
  velocity times dt (AC_Loiter.cpp:393-396), in double, rounded to binary32 (|pos| ≤ 9035:
  half an ulp ≤ 0.0005), when no init_target_m set the desired position in the tick;
* `stopping_point_passthrough`: get_stopping_point_NE_m is the position stage's (AC_Loiter.cpp:214-222);
* `pos_desired_from_init_target_m`: only init_target_m calls set_pos_desired_NE_m, with its
  argument (AC_Loiter.cpp:131; binary32 widened to double and back, exact);
* `no_internal_error`, `outputs_finite`. -/
def guarantee : List Clause := [
  ⟨"outputs_finite", conj (floatOutputs.map fun x => finite (.var x))⟩,
  ⟨"no_internal_error", "lt_internal_errors" =. 0⟩,
  ⟨"angle_max_within_position_limit", 0 ≤. "lt_angle_max" ∧.
      "lt_angle_max" ≤. "pc_lean_angle_max"⟩,
  ⟨"angle_max_two_thirds", fltEps ≤. "loit_ang_max" ∨.
      "lt_angle_max" ≤. "lt_att_lean_angle_max"⟩,
  ⟨"att_lean_from_parameter",
      abs (v "lt_att_lean_angle_max" - v "atc_angle_max" * 0.017453292) ≤. 0.000001⟩,
  ⟨"speed_max_floor", 0.2 ≤. "lt_speed_max"⟩,
  ⟨"accel_max_bounded", 0 <. "lt_accel_max" ∧. "lt_accel_max" ≤. "loit_acc_max_m"⟩,
  ⟨"brake_accel_range", -0.00001 ≤. "lt_brake_accel" ∧.
      "lt_brake_accel" ≤. v "loit_brk_acc_m" + 0.00001⟩,
  ⟨"handover_constants",
      (¬. "lt_tgt_ne_set_correction_speed_accel" ∨. ("lt_tgt_ne_correction_speed" =. 2 ∧.
        "lt_tgt_ne_correction_accel" =. "lt_accel_max")) ∧.
      (¬. "lt_cmd_position_NE_set_pos_error_max_m" ∨.
        "lt_cmd_position_NE_set_pos_error_max_m_error_max" =. 2)⟩,
  ⟨"vel_within_speed_limit", ¬. ("lt_tgt_valid" ∧. "lt_update_last") ∨.
      tgtSpeedSq ≤. 0.04 * 1.00001 ∨.
      (tgtSpeedSq ≤. sq "lt_speed_max" * 1.00001 ∧.
       tgtSpeedSq ≤. sq "est_gnd_spd_limit" * 1.00001)⟩,
  ⟨"accel_bounded", ¬. ("lt_tgt_valid" ∧. "lt_pilot_before_update") ∨.
      absLe ["lt_tgt_acc_n", "lt_tgt_acc_e"] 60⟩,
  ⟨"pos_follows_vel", ¬. "lt_tgt_valid" ∨. .var (cl "init_target_m") ∨.
      (abs (v "lt_tgt_pos_n" - v "pc_pos_desired_n" - v "lt_tgt_vel_n" * v "dt") ≤. 0.002 ∧.
       abs (v "lt_tgt_pos_e" - v "pc_pos_desired_e" - v "lt_tgt_vel_e" * v "dt") ≤. 0.002)⟩,
  ⟨"stopping_point_passthrough", "lt_stopping_point_n" =. "pc_stopping_point_n" ∧.
      "lt_stopping_point_e" =. "pc_stopping_point_e"⟩,
  ⟨"pos_desired_from_init_target_m", ¬. "lt_cmd_position_set_pos_desired_NE_m" ∨.
      (.var (cl "init_target_m") ∧.
       "lt_cmd_position_set_pos_desired_NE_m_n" =. .var (cl "init_target_m_n") ∧.
       "lt_cmd_position_set_pos_desired_NE_m_e" =. .var (cl "init_target_m_e"))⟩]

def contract : Contract where
  assume := assumeParams ++ assumeSignals ++ assumeCommands
  guarantee := guarantee

/-! ### Regimes and coverage -/

/-- ArduCopter's default parameters: LOIT_ (AC_Loiter.cpp:13-25, Copter), ATC_ (the attitude
stage's stockParams), PSC_NE_VEL_P 2 (the position stage's). -/
def stockParams : List Clause := [
  ⟨"stock_loit", "loit_ang_max" =. 0 ∧. "loit_speed_ms" =. 12.5 ∧. "loit_acc_max_m" =. 5 ∧.
      "loit_brk_acc_m" =. 2.5 ∧. "loit_brk_jrk_m" =. 5 ∧. "loit_brk_delay" =. 1⟩,
  ⟨"stock_loit_atc", "atc_rate_r_max" =. 0 ∧. "atc_rate_p_max" =. 0 ∧. "atc_acc_r_max" =. 1100 ∧.
      "atc_acc_p_max" =. 1100 ∧. "atc_input_tc" =. 0.1 ∧. "atc_angle_max" =. 30 ∧.
      "atc_ang_rll_p" =. 4.5 ∧. "atc_ang_pit_p" =. 4.5⟩,
  ⟨"stock_loit_psc", "psc_ne_vel_p" =. 2⟩]

/-- LOITER flying, ModeLoiter::run every tick (mode_loiter.cpp:84-181): at the first tick
(now_ms 1000) init_target, as ModeLoiter::init does; then set_pilot_desired_acceleration_rad and
update, in the fixed order; the pilot's sticks within 0.35 rad; the position stage's state near
hover. -/
def flightClauses : List Clause := [
  ⟨"loiter_run", "cmd_loiter_set_pilot_desired_acceleration_rad" ∧. ¬. .var (cl "set_speed_max_NE_ms") ∧.
      ¬. .var (cl "soften_for_landing") ∧. ¬. .var (cl "init_target_m") ∧.
      (("now_ms" ≤. 1000 ∧. .var (cl "init_target") ∧. ¬. .var (cl "update")) ∨.
       (1000 <. "now_ms" ∧. ¬. .var (cl "init_target") ∧. .var (cl "update")))⟩,
  ⟨"loiter_fixed_order", conj ((commands.filter fun x => x.name.endsWith "_seq").map
      fun x => .var x.name =. 0)⟩,
  ⟨"loiter_400hz", within "dt" 0.0024 0.0026⟩,
  ⟨"loiter_sticks", absLe [cl "set_pilot_desired_acceleration_rad_roll",
      cl "set_pilot_desired_acceleration_rad_pitch"] 0.35⟩,
  ⟨"loiter_near_hover", absLe ["pc_vel_desired_n", "pc_vel_desired_e", "pc_accel_target_n",
      "pc_accel_target_e"] 3 ∧. absLe ["pc_pos_desired_n", "pc_pos_desired_e",
      "pc_stopping_point_n", "pc_stopping_point_e"] 20 ∧.
      absLe ["pc_roll", "pc_pitch", "ac_att_target_roll", "ac_att_target_pitch"] 0.3 ∧.
      "est_gnd_spd_limit" =. 400⟩]

def hints : List Hint := [.increasing "now_ms" 1000 2 3]

def flight : Regime where
  name := "flight"
  doc := "LOITER flying (init_target at the first tick, then set_pilot_desired_acceleration_rad \
    and update every tick), documented parameter ranges, the position stage near hover"
  clauses := flightClauses
  hints := hints

def stockFlight : Regime where
  name := "stock_flight"
  doc := "as flight, with ArduCopter's default parameters and the stock lean limit"
  clauses := stockParams ++ flightClauses ++ [⟨"stock_lean", "pc_lean_angle_max" =. 0.5235988⟩]
  hints := hints

/-- What a campaign counts. -/
def coverage : List Clause := [
  ⟨"targets", "lt_tgt_valid"⟩,
  ⟨"braking", 0.001 <. "lt_brake_accel"⟩,
  ⟨"speed_limited", "lt_tgt_valid" ∧. sq "lt_speed_max" ≤. tgtSpeedSq * 1.00001⟩,
  ⟨"pilot_request", 0.01 <. abs (v "lt_desired_accel_n") + abs (v "lt_desired_accel_e")⟩,
  ⟨"init", "lt_tgt_ne_set_correction_speed_accel"⟩]

def module : Module where
  name := "loiter"
  doc := "ArduCopter's AC_Loiter, with the attitude controller's command model it calls"
  params := params
  input := input
  output := output
  contract := contract
  exe := "build/modules/loiter/loiter"
  stack := .ardupilot
  regimes := [flight, stockFlight]
  coverage := coverage

end Ardupilot.Modules.Loiter
