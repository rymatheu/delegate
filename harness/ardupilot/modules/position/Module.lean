import Harness.Module
import Harness.Compose

/-! # position: ArduCopter's position controller

One `AC_PosControl` (libraries/AC_AttitudeControl/AC_PosControl.cpp) with the controllers it owns
(`AC_P_2D` NE position, `AC_P_1D` D position, `AC_PID_2D` NE velocity, `AC_PID_Basic` D velocity,
`AC_PID` D acceleration, libraries/AC_PID) and the AP_Math shaping and square-root controller code
it calls (libraries/AP_Math/control.cpp). It is built as ArduCopter builds it
(Copter::allocate_motors: `AC_PosControl(*ahrs_view, *motors, *attitude_control)`), with its
parameters from the parameter record, and stepped once per 400 Hz tick. The executable is built by
`ardupilot/build.sh position` from the real, unmodified sources in sources.txt; see adapter.cpp for
the cut and the stubs_*.cpp files for what is outside.

One step, in this order (adapter.cpp says where each call is made in ArduCopter):
1. the scheduler tick (`AP_Scheduler::tick`), the estimator's, the attitude controller's and the
   mixer's state loaded from the input signals (stubs);
2. `set_dt_s(dt)` (Copter::run_rate_controller_main);
3. `update_estimates(high_vibes)` (Copter::read_inertia), when commanded;
4. `set_vibe_comp`, `set_reset_handling_method`;
5. the limit setters: `NE_set_max_speed_accel_m`, `NE_set_correction_speed_accel_m`,
   `NE_set_pos_error_max_m`, `D_set_max_speed_accel_m`, `D_set_correction_speed_accel_m`;
6. the initializers: `NE_init_controller`, `NE_init_controller_stopping_point`,
   `D_init_controller`, `D_init_controller_no_descent`, `D_init_controller_stopping_point`,
   `init_pos_terrain_D_m`, `set_pos_desired_NE_m`, `D_get_accel_pid().set_integrator`
   (`D_init_controller` seeds the accel PID's integrator from `get_throttle_in()`: see
   `sameTickThrottle` for which throttle that is);
6b. the guidance stage's calls of the same tick (signals `tgt_…`, added when the stages were
   composed): `D_init_controller_stopping_point`, `NE_init_controller_stopping_point`,
   `NE_set_max_speed_accel_m`, `NE_set_correction_speed_accel_m`, `D_set_max_speed_accel_m`,
   `D_set_correction_speed_accel_m`, in AC_WPNav's order (AC_WPNav.cpp:223-235);
7. the guidance signal: `set_pos_terrain_target_D_m` and `set_pos_vel_accel_NED_m`
   (AC_WPNav::update_wpnav, AC_WPNav.cpp:636), or
   `set_pos_vel_accel_NE_m` (AC_Loiter), when `tgt_valid`;
7b. the loiter stage's calls of the same tick (signals `lt_…`, added with the loiter stage):
   `NE_soften_for_landing`, `NE_set_correction_speed_accel_m`, `NE_set_pos_error_max_m`,
   `NE_init_controller_stopping_point`, `set_pos_desired_NE_m`, `NE_relax_velocity_controller`,
   `set_pos_vel_accel_NE_m` and `NE_update_controller`, in AC_Loiter's order (`loiterHandover`);
8. NE shaping: `NE_relax_velocity_controller`, `NE_soften_for_landing`, `input_vel_accel_NE_m`,
   `input_pos_vel_accel_NE_m`, `input_pos_NED_m`, `NE_stop_vel_stabilisation`,
   `NE_stop_pos_stabilisation`; then `NE_update_controller` (once, if commanded or if the guidance
   stage handed NED targets: AC_WPNav::update_wpnav's own call, AC_WPNav.cpp:741);
9. D shaping: `D_relax_controller`, `D_set_pos_target_from_climb_rate_ms`,
   `input_pos_vel_accel_D_m`, `input_vel_accel_D_m`, `D_set_alt_target_with_slew_m`; then
   `D_update_controller`, whose `set_throttle_out(...)` call is the output `throttle_in`.
The NE and D halves share no state except through `input_pos_NED_m`, so running NE before D
gives the same result as the modes that run D first (mode_land).

Where a caller's order differs from this one, a supervisor reproduces it across two ticks:
AC_WPNav::wp_and_spline_init initializes (step 6) before it sets the limits (step 5), so its
stopping points use the previous limits; ekf_check's set_vibe_comp runs after the mode in
ArduCopter, here before the updates. Arguments passed by reference and written back
(input_vel_accel_NE_m's velocity, input_pos_vel_accel_*'s position and velocity) are not returned;
GUIDED's velocity and position-velocity controllers keep them (mode_guided.cpp:809, :950).

Hidden state found in the code, and how it crosses the cut:
* the scheduler's tick counter (NE/D_is_active): one step is one tick (stubs_scheduler.cpp); an
  update with no init or update at the previous tick re-initializes and raises
  INTERNAL_ERROR(flow_of_control), counted in pc_internal_errors_flow;
* the EKF reset counts: AP_AHRS's reset trackers are stepped with the input counts as keys, so a
  change of an input count is one reset (as AP_AHRS::update_reset_counters does);
* PSC_D_ACC_IMAX is rewritten at run time: D_update_controller raises it to the hover throttle
  (AC_PosControl.cpp:1127-1129; output pc_accel_d_imax);
* _ne_control_scale_factor is reset to 1 after every NE update (never set here);
* AP_HAL::millis() (input now_ms) times out the offset targets after 3 s and is read by the
  accel PID's slew limiter (SlewLimiter::modifier, SlewLimiter.cpp:55).

Positions are `postype_t` = double in this build (HAL_WITH_POSTYPE_DOUBLE, SITL); they cross the
ports as binary32: inputs widen exactly, outputs are rounded to the nearest binary32 (below 1 m
of error at 1e7 m, 6e-5 m at 1 km). -/

namespace Ardupilot.Modules.Position

open Harness Harness.Contract.Lang

private def f (n d : String) : Field := { name := n, type := .f32, doc := d }
private def b (n d : String) : Field := { name := n, type := .bool, doc := d }
private def u (n d : String) : Field := { name := n, type := .u32, doc := d }

def params : Schema := #[
  f "psc_ne_pos_p" "PSC_NE_POS_P (_p_pos_ne_m.kP())",
  f "psc_d_pos_p" "PSC_D_POS_P (_p_pos_d_m.kP())",
  f "psc_ne_vel_p" "PSC_NE_VEL_P (_pid_vel_ne_m.kP())",
  f "psc_ne_vel_i" "PSC_NE_VEL_I",
  f "psc_ne_vel_d" "PSC_NE_VEL_D",
  f "psc_ne_vel_imax" "PSC_NE_VEL_IMAX, m/s/s",
  f "psc_ne_vel_flte" "PSC_NE_VEL_FLTE, Hz",
  f "psc_ne_vel_fltd" "PSC_NE_VEL_FLTD, Hz",
  f "psc_ne_vel_ff" "PSC_NE_VEL_FF",
  f "psc_d_vel_p" "PSC_D_VEL_P (_pid_vel_d_m.kP())",
  f "psc_d_vel_i" "PSC_D_VEL_I",
  f "psc_d_vel_d" "PSC_D_VEL_D",
  f "psc_d_vel_imax" "PSC_D_VEL_IMAX, m/s/s",
  f "psc_d_vel_flte" "PSC_D_VEL_FLTE, Hz",
  f "psc_d_vel_fltd" "PSC_D_VEL_FLTD, Hz",
  f "psc_d_vel_ff" "PSC_D_VEL_FF",
  f "psc_d_acc_p" "PSC_D_ACC_P (_pid_accel_d_m.kP())",
  f "psc_d_acc_i" "PSC_D_ACC_I",
  f "psc_d_acc_d" "PSC_D_ACC_D",
  f "psc_d_acc_imax" "PSC_D_ACC_IMAX (raised to the hover throttle at run time)",
  f "psc_d_acc_ff" "PSC_D_ACC_FF",
  f "psc_d_acc_fltt" "PSC_D_ACC_FLTT, Hz",
  f "psc_d_acc_flte" "PSC_D_ACC_FLTE, Hz",
  f "psc_d_acc_fltd" "PSC_D_ACC_FLTD, Hz",
  f "psc_d_acc_smax" "PSC_D_ACC_SMAX, slew rate limit, 0 disables",
  f "psc_d_acc_pdmx" "PSC_D_ACC_PDMX, P+D limit, 0 disables",
  f "psc_d_acc_d_ff" "PSC_D_ACC_D_FF",
  f "psc_angle_max" "PSC_ANGLE_MAX, deg; 0 uses ATC_ANGLE_MAX (_lean_angle_max_deg)",
  f "psc_ne_jerk" "PSC_NE_JERK, m/s^3 (_shaping_jerk_ne_msss)",
  f "psc_d_jerk" "PSC_D_JERK, m/s^3 (_shaping_jerk_d_msss)",
  f "atc_rate_r_max" "ATC_RATE_R_MAX, deg/s (attitude's _ang_vel_roll_max_degs)",
  f "atc_rate_p_max" "ATC_RATE_P_MAX, deg/s (_ang_vel_pitch_max_degs)",
  f "atc_acc_r_max" "ATC_ACC_R_MAX, deg/s/s (_accel_roll_max_degss)",
  f "atc_acc_p_max" "ATC_ACC_P_MAX, deg/s/s (_accel_pitch_max_degss)"]

/-- A command: its Boolean and its argument fields. -/
private def cmd (m doc : String) (args : List Field) : List Field :=
  b s!"cmd_position_{m}" s!"{doc} is called this tick" ::
    args.map fun a => { a with name := s!"cmd_position_{m}_{a.name}",
                               doc := s!"{m}: argument {a.doc}" }

def commands : List Field :=
  cmd "update_estimates" "update_estimates (Copter::read_inertia, every tick)"
    [b "high_vibes" "high_vibes"] ++
  cmd "set_vibe_comp" "set_vibe_comp (Copter::check_vibration)" [b "on" "on_off"] ++
  cmd "set_reset_handling_method" "set_reset_handling_method (Copter::set_mode)"
    [u "method" "0 MoveTarget, 1 MoveVehicle"] ++
  cmd "NE_set_max_speed_accel_m" "NE_set_max_speed_accel_m"
    [f "speed" "speed_ne_ms", f "accel" "accel_ne_mss"] ++
  cmd "NE_set_correction_speed_accel_m" "NE_set_correction_speed_accel_m"
    [f "speed" "speed_ne_ms", f "accel" "accel_ne_mss"] ++
  cmd "NE_set_pos_error_max_m" "NE_set_pos_error_max_m (AC_Loiter::init_target)"
    [f "error_max" "error_max_m"] ++
  cmd "D_set_max_speed_accel_m" "D_set_max_speed_accel_m"
    [f "down" "decent_speed_max_ms", f "up" "climb_speed_max_ms", f "accel" "accel_max_d_mss"] ++
  cmd "D_set_correction_speed_accel_m" "D_set_correction_speed_accel_m"
    [f "down" "decent_speed_max_ms", f "up" "climb_speed_max_ms", f "accel" "accel_max_d_mss"] ++
  cmd "NE_init_controller" "NE_init_controller" [] ++
  cmd "NE_init_controller_stopping_point" "NE_init_controller_stopping_point" [] ++
  cmd "D_init_controller" "D_init_controller" [] ++
  cmd "D_init_controller_no_descent" "D_init_controller_no_descent" [] ++
  cmd "D_init_controller_stopping_point" "D_init_controller_stopping_point" [] ++
  cmd "init_pos_terrain_D_m" "init_pos_terrain_D_m" [f "terrain_d" "pos_terrain_d_m"] ++
  cmd "set_pos_desired_NE_m" "set_pos_desired_NE_m (AC_Loiter::init_target_m)"
    [f "n" "pos_desired_ne_m.x", f "e" "pos_desired_ne_m.y"] ++
  cmd "D_accel_pid_set_integrator" "D_get_accel_pid().set_integrator (set_throttle_takeoff)"
    [f "i" "integrator"] ++
  cmd "NE_relax_velocity_controller" "NE_relax_velocity_controller" [] ++
  cmd "NE_soften_for_landing" "NE_soften_for_landing" [] ++
  cmd "input_vel_accel_NE_m" "input_vel_accel_NE_m"
    [f "vel_n" "vel_ne_ms.x", f "vel_e" "vel_ne_ms.y", f "accel_n" "accel_ne_mss.x",
     f "accel_e" "accel_ne_mss.y", b "limit_output" "limit_output"] ++
  cmd "input_pos_vel_accel_NE_m" "input_pos_vel_accel_NE_m"
    [f "pos_n" "pos_ne_m.x", f "pos_e" "pos_ne_m.y", f "vel_n" "vel_ne_ms.x",
     f "vel_e" "vel_ne_ms.y", f "accel_n" "accel_ne_mss.x", f "accel_e" "accel_ne_mss.y",
     b "limit_output" "limit_output"] ++
  cmd "input_pos_NED_m" "input_pos_NED_m"
    [f "pos_n" "pos_ned_m.x", f "pos_e" "pos_ned_m.y", f "pos_d" "pos_ned_m.z",
     f "terrain_d" "pos_terrain_target_d_m", f "terrain_margin" "terrain_margin_m"] ++
  cmd "NE_stop_vel_stabilisation" "NE_stop_vel_stabilisation" [] ++
  cmd "NE_stop_pos_stabilisation" "NE_stop_pos_stabilisation" [] ++
  cmd "NE_update_controller" "NE_update_controller" [] ++
  cmd "D_relax_controller" "D_relax_controller" [f "throttle" "throttle_setting"] ++
  cmd "D_set_pos_target_from_climb_rate_ms" "D_set_pos_target_from_climb_rate_ms"
    [f "climb_rate" "climb_rate_ms", b "ignore_descent_limit" "ignore_descent_limit"] ++
  cmd "input_pos_vel_accel_D_m" "input_pos_vel_accel_D_m"
    [f "pos" "pos_d_m", f "vel" "vel_d_ms", f "accel" "accel_d_mss",
     b "limit_output" "limit_output"] ++
  cmd "input_vel_accel_D_m" "input_vel_accel_D_m"
    [f "vel" "vel_d_ms", f "accel" "accel_d_mss", b "limit_output" "limit_output"] ++
  cmd "D_set_alt_target_with_slew_m" "D_set_alt_target_with_slew_m" [f "alt" "pos_u_m"] ++
  cmd "D_update_controller" "D_update_controller" []

def signals : List Field := [
  f "dt" "set_dt_s: last loop time, s (Copter::run_rate_controller_main)",
  u "now_ms" "the clock AP_HAL::millis() reads (offset-target time-outs)",
  f "est_pos_n" "AHRS position north of the EKF origin, m (active_estimates->position_NE.x)",
  f "est_pos_e" "position east, m (position_NE.y)",
  f "est_pos_d" "position down, m (position_D)",
  b "est_pos_ok" "AP_AHRS::get_relative_position_NED_origin returned true (the estimator's \
    output): stands for both position_NE_valid and position_D_valid, which the real AP_AHRS \
    keeps apart (NE from get_relative_position_NE_origin, D from _D_origin); the estimator \
    stage reports only the conjunction (before the composition: est_pos_ne_valid, \
    est_pos_d_valid)",
  f "est_vel_n" "AP_AHRS::get_velocity_NED: north, m/s",
  f "est_vel_e" "get_velocity_NED: east, m/s",
  f "est_vel_d" "get_velocity_NED: down, m/s",
  b "est_vel_ok" "get_velocity_NED returned true",
  f "est_pos_rate_d" "AP_AHRS::get_vert_pos_rate_D, m/s",
  b "est_pos_rate_d_ok" "get_vert_pos_rate_D returned true",
  f "est_accel_ef_z" "AP_AHRS::get_accel_ef().z, earth-frame specific force down, m/s/s \
    (est_accel_ef_d before the composition: renamed to the estimator stage's output)",
  f "est_yaw" "AP_AHRS_View::yaw, rad",
  f "est_cos_yaw" "AP_AHRS_View::cos_yaw() (trig.cos_yaw)",
  f "est_sin_yaw" "AP_AHRS_View::sin_yaw() (trig.sin_yaw)",
  f "est_gain_scaler_xy" "AP_AHRS::get_control_gain_scaler_XY()",
  f "est_gain_scaler_z" "AP_AHRS::get_control_gain_scaler_Z()",
  u "est_pos_ne_reset_count" "the EKF's NE position reset count (a change is a reset)",
  u "est_pos_d_reset_count" "the EKF's D position reset count (a change is a reset)",
  f "ac_att_target_roll" "AC_AttitudeControl::get_att_target_euler_rad().x, rad (previous tick)",
  f "ac_att_target_pitch" "get_att_target_euler_rad().y, rad",
  f "ac_att_target_yaw" "get_att_target_euler_rad().z, rad",
  f "ac_throttle_in" "AC_AttitudeControl::get_throttle_in() (previous tick)",
  f "ac_althold_lean_angle_max" "AC_AttitudeControl::get_althold_lean_angle_max_rad(), rad",
  f "ac_lean_angle_max" "AC_AttitudeControl::lean_angle_max_rad() (ATC_ANGLE_MAX), rad",
  b "ac_bf_feedforward" "AC_AttitudeControl::get_bf_feedforward() (ATC_RATE_FF_ENAB)",
  b "limit_throttle_lower" "AP_Motors limit.throttle_lower (mixer, previous tick)",
  b "limit_throttle_upper" "AP_Motors limit.throttle_upper (mixer, previous tick)",
  f "throttle_hover" "AP_Motors::get_throttle_hover() (MOT_THST_HOVER as learned)",
  b "tgt_valid" "guidance handed targets this tick (AC_WPNav::advance_wp_target_along_track)",
  b "tgt_ne_only" "the targets are NE only (AC_Loiter: set_pos_vel_accel_NE_m)",
  f "tgt_pos_n" "set_pos_vel_accel_NED_m: pos_ned_m.x, m",
  f "tgt_pos_e" "pos_ned_m.y, m",
  f "tgt_pos_d" "pos_ned_m.z, m",
  f "tgt_vel_n" "vel_ned_ms.x, m/s",
  f "tgt_vel_e" "vel_ned_ms.y, m/s",
  f "tgt_vel_d" "vel_ned_ms.z, m/s",
  f "tgt_acc_n" "accel_ned_mss.x, m/s/s",
  f "tgt_acc_e" "accel_ned_mss.y, m/s/s",
  f "tgt_acc_d" "accel_ned_mss.z, m/s/s",
  f "tgt_terrain_d" "set_pos_terrain_target_D_m (AC_WPNav), m down; with NED targets only"]

/-- The guidance stage's other calls on the position controller this tick (AC_WPNav's
wp_and_spline_init_m, set_speed_NE_ms, set_speed_up_ms, set_speed_down_ms), as the guidance
stage reports them: a Boolean per method (called at least once this tick) and the arguments of
its last call. Executed after the supervisor's initializers, in AC_WPNav's order
(AC_WPNav.cpp:223-235; see the step order in the header). -/
def handover : List Field := [
  b "tgt_d_init_stopping_point" "AC_WPNav called D_init_controller_stopping_point this tick",
  b "tgt_ne_init_stopping_point" "AC_WPNav called NE_init_controller_stopping_point this tick",
  b "tgt_ne_set_max_speed_accel" "AC_WPNav called NE_set_max_speed_accel_m this tick",
  f "tgt_ne_max_speed" "its speed_ne_ms argument (last call), m/s",
  f "tgt_ne_max_accel" "its accel_ne_mss argument (last call), m/s/s",
  b "tgt_ne_set_correction_speed_accel" "AC_WPNav called NE_set_correction_speed_accel_m",
  f "tgt_ne_correction_speed" "its speed_ne_ms argument, m/s",
  f "tgt_ne_correction_accel" "its accel_ne_mss argument, m/s/s",
  b "tgt_d_set_max_speed_accel" "AC_WPNav called D_set_max_speed_accel_m this tick",
  f "tgt_max_speed_down" "its decent_speed_max_ms argument, m/s",
  f "tgt_max_speed_up" "its climb_speed_max_ms argument, m/s",
  f "tgt_d_max_accel" "its accel_max_d_mss argument, m/s/s",
  b "tgt_d_set_correction_speed_accel" "AC_WPNav called D_set_correction_speed_accel_m",
  f "tgt_d_correction_speed_down" "its decent_speed_max_ms argument, m/s",
  f "tgt_d_correction_speed_up" "its climb_speed_max_ms argument, m/s",
  f "tgt_d_correction_accel" "its accel_max_d_mss argument, m/s/s"]

/-- One `cmd_position_<method>_seq` (u32) per command method: the position of this call in the supervisor's call order within the tick, counting from 1 across all stages; 0 = not sequenced (all 0: the stage's fixed order). Set commands run
in increasing `_seq` (a set command with `_seq` 0 in a sequenced tick runs after the sequenced
commands that precede it in the fixed order); with every `_seq` 0, in the fixed order of the
header. The guidance stage's hand-over (6b) runs at `tgt_handover_seq` and its targets with the
NE update (7) at `tgt_update_seq`; set_dt_s and the stand-ins' loading always come first. -/
def seqFields : List Field :=
  (commands.filter fun f => f.type == .bool && f.doc.endsWith "is called this tick").map fun f =>
    u s!"{f.name}_seq" s!"{f.name}: call order in the tick"

/-- The guidance stage's call order, for a sequenced tick. -/
def handoverSeq : List Field := [
  u "tgt_handover_seq" "guidance: the `_seq` at which its initializers and limit setters were \
    called (0: not sequenced)",
  u "tgt_update_seq" "guidance: the `_seq` of update_wpnav (set_pos_vel_accel_NED_m, \
    NE_update_controller) (0: not sequenced)"]

/-- The same-tick throttle rule. `D_init_controller` (and `D_init_controller_no_descent`,
`D_init_controller_stopping_point`, `D_relax_controller`, which call it) sets the accel PID's
integrator from `_attitude_control.get_throttle_in()` (AC_PosControl.cpp:920), the argument of
the attitude controller's last `set_throttle_out`. That is
* the supervisor's own `set_throttle_out` of this tick, `cmd_attitude_set_throttle_out_throttle_in`,
  when the supervisor called it (`cmd_attitude_set_throttle_out`) and its `_seq` is not 0 and
  precedes the initializer's `_seq` (ModeAltHold's takeoff ramp: set_throttle_out(throttle_in +
  dt/slew), then D_init_controller, takeoff.cpp:83-86);
* else this stage's own D_update_controller, if it ran earlier in the tick (the stand-in
  records its set_throttle_out, as before);
* else the attitude stage's value of the previous tick, `ac_throttle_in`.
The supervisor's call is the attitude stage's command (it executes it); here only its effect on
get_throttle_in() is reproduced, at its `_seq` (adapter.cpp, OP_SUPERVISOR_SET_THROTTLE). In a
tick with every `_seq` 0 (the fixed order) it is ignored, so the earlier evidence and cases
stand. Not reproduced: the call's update_althold_lean_angle_max (the attitude stage's state,
read here as `ac_althold_lean_angle_max` of the previous tick). Before this rule the takeoff ramp
restarted every tick: D_init seeded the integrator from the previous tick's throttle, so
ALT_HOLD on the real estimator never left the ground. -/
def sameTickThrottle : List Field := [
  b "cmd_attitude_set_throttle_out" "the supervisor called \
    AC_AttitudeControl_Multi::set_throttle_out this tick (the attitude stage's command)",
  f "cmd_attitude_set_throttle_out_throttle_in" "its throttle_in argument (get_throttle_in() \
    after it)",
  u "cmd_attitude_set_throttle_out_seq" "its place in the supervisor's call order (0: not \
    sequenced, the call is ignored here)"]

/-- The loiter stage's calls on the position controller this tick (AC_Loiter in the loiter
stage, its outputs of the same names, same tick). The methods the guidance stage also hands over
have its port names with `lt_` in front (`lt_tgt_…`, one `_seq` for the two initializing calls,
`lt_tgt_update_seq` for the targets and the NE update); the others are
`lt_cmd_position_<method>[_<arg>]` with their own `_seq` (the supervisor's `cmd_position_…` of
the same methods stay its own). Each `_seq` is that of the supervisor's loiter command during
which AC_Loiter made the call; the step runs them at that place, and calls with one `_seq` in
AC_Loiter's order: soften, correction limits, error limit, stopping-point initialization,
desired position, relax, targets and NE update (AC_Loiter.cpp:118-160, 250-253, 399; with every
`_seq` 0 this is also the fixed order, ModeLoiter::run's, mode_loiter.cpp:99-161). Fixed off where
no loiter stage is composed. -/
def loiterHandover : List Field := [
  b "lt_tgt_ne_init_stopping_point" "AC_Loiter called NE_init_controller_stopping_point this tick",
  b "lt_tgt_ne_set_correction_speed_accel" "AC_Loiter called NE_set_correction_speed_accel_m",
  f "lt_tgt_ne_correction_speed" "its speed_ne_ms argument, m/s",
  f "lt_tgt_ne_correction_accel" "its accel_ne_mss argument, m/s/s",
  u "lt_tgt_handover_seq" "loiter: the `_seq` of those two calls (0: not sequenced)",
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
  b "lt_tgt_ne_update" "AC_Loiter called NE_update_controller (update), after the targets",
  u "lt_tgt_update_seq" "loiter: the `_seq` of update (0: not sequenced)",
  f "lt_tgt_pos_n" "set_pos_vel_accel_NE_m: pos_ne_m.x, m", f "lt_tgt_pos_e" "pos_ne_m.y, m",
  f "lt_tgt_vel_n" "vel_ne_ms.x, m/s", f "lt_tgt_vel_e" "vel_ne_ms.y, m/s",
  f "lt_tgt_acc_n" "accel_ne_mss.x, m/s/s", f "lt_tgt_acc_e" "accel_ne_mss.y, m/s/s"]

def input : Schema :=
  (signals ++ handover ++ handoverSeq ++ commands ++ seqFields ++ sameTickThrottle ++
    loiterHandover).toArray

/-- The loiter-stage inputs fixed off (false, 0), for compositions without a loiter stage. -/
def loiterOffFix : List (String × Word) :=
  loiterHandover.map fun x => (x.name, match x.type with
    | .bool => Word.bool false
    | .u32 => Word.u32 0
    | _ => Word.f32 0)

def output : Schema := #[
  f "thrust_vec_x" "get_thrust_vector().x: NED accel target north, m/s/s",
  f "thrust_vec_y" "get_thrust_vector().y: accel target east, m/s/s",
  f "thrust_vec_z" "get_thrust_vector().z: -GRAVITY_MSS",
  f "throttle_in" "D_update_controller's set_throttle_out(throttle_in, ., .) argument",
  b "pc_throttle_set" "set_throttle_out was called this tick (D_update_controller ran)",
  b "pc_throttle_angle_boost" "set_throttle_out's apply_angle_boost argument",
  u "pc_throttle_seq" "the `_seq` of D_update_controller, whose set_throttle_out the attitude \
    stage executes at that place (0: not sequenced)",
  f "pc_throttle_cutoff_hz" "set_throttle_out's filt_cutoff argument, Hz",
  f "pc_pos_target_n" "_pos_target_ned_m.x, m", f "pc_pos_target_e" "_pos_target_ned_m.y",
  f "pc_pos_target_d" "_pos_target_ned_m.z",
  f "pc_pos_desired_n" "get_pos_desired_NED_m().x, m", f "pc_pos_desired_e" ".y",
  f "pc_pos_desired_d" ".z",
  f "pc_vel_target_n" "get_vel_target_NED_ms().x, m/s", f "pc_vel_target_e" ".y",
  f "pc_vel_target_d" ".z",
  f "pc_vel_desired_n" "get_vel_desired_NED_ms().x, m/s", f "pc_vel_desired_e" ".y",
  f "pc_vel_desired_d" ".z",
  f "pc_accel_target_n" "get_accel_target_NED_mss().x, m/s/s", f "pc_accel_target_e" ".y",
  f "pc_accel_target_d" ".z",
  f "pc_accel_desired_n" "_accel_desired_ned_mss.x, m/s/s", f "pc_accel_desired_e" ".y",
  f "pc_accel_desired_d" ".z",
  f "pc_pos_offset_n" "get_pos_offset_NED_m().x, m", f "pc_pos_offset_e" ".y",
  f "pc_pos_offset_d" ".z",
  f "pc_vel_offset_n" "get_vel_offset_NED_ms().x, m/s", f "pc_vel_offset_e" ".y",
  f "pc_vel_offset_d" ".z (get_vel_offset_D_ms)",
  f "pc_accel_offset_n" "get_accel_offset_NED_mss().x, m/s/s", f "pc_accel_offset_e" ".y",
  f "pc_accel_offset_d" ".z",
  f "pc_pos_terrain_d" "get_pos_terrain_D_m(), m", f "pc_vel_terrain_d" "get_vel_terrain_D_ms()",
  f "pc_pos_error_n" "get_pos_error_NED_m().x (NE P controller error), m",
  f "pc_pos_error_e" ".y", f "pc_pos_error_d" ".z (D P controller error)",
  f "pc_limit_n" "_limit_vector_ned.x (unlimited NE accel when limited, else 0)",
  f "pc_limit_e" "_limit_vector_ned.y", f "pc_limit_d" "_limit_vector_ned.z (-1, 0, 1)",
  f "pc_roll" "get_roll_rad(), rad", f "pc_pitch" "get_pitch_rad(), rad",
  f "pc_yaw" "get_yaw_rad(), rad", f "pc_yaw_rate" "get_yaw_rate_rads(), rad/s",
  -- named after the getters, as the guidance stage reads them (before the composition:
  -- pc_vel_max_ne, pc_vel_max_up, pc_vel_max_down, pc_accel_max_ne, pc_accel_max_d)
  f "pc_ne_max_speed" "NE_get_max_speed_ms(), m/s", f "pc_max_speed_up" "get_max_speed_up_ms()",
  f "pc_max_speed_down" "get_max_speed_down_ms()", f "pc_ne_max_accel" "NE_get_max_accel_mss()",
  f "pc_d_max_accel" "D_get_max_accel_mss()", f "pc_jerk_max_ne" "_jerk_max_ne_msss",
  f "pc_jerk_max_d" "_jerk_max_d_msss",
  f "pc_pos_error_max_ne" "NE_get_pos_error_max_m(), m",
  f "pc_lean_angle_max" "get_lean_angle_max_rad(), rad",
  f "pc_lean_angle" "observer: tilt of the thrust vector, accel_mss_to_angle_rad(|xy|), rad",
  f "pc_vel_d_control_ratio" "get_vel_D_control_ratio()",
  f "pc_stopping_point_n" "get_stopping_point_NE_m().x, m", f "pc_stopping_point_e" ".y",
  f "pc_stopping_point_d" "get_stopping_point_D_m(), m",
  b "pc_ne_active" "NE_is_active() as the next tick reads it before any call",
  b "pc_d_active" "D_is_active() as the next tick reads it before any call",
  b "pc_ne_updated" "NE_update_controller ran this tick (commanded, or guidance's tgt_valid)",
  b "pc_d_updated" "D_update_controller ran this tick",
  b "pc_ne_update_last" "the NE update ran and no NE call came after it this tick (always so in \
    the fixed order)",
  b "pc_d_update_last" "D_update_controller ran and no D call came after it this tick (always \
    so in the fixed order)",
  b "pc_handover_limits_last" "the guidance stage's hand-over ran and no supervisor \
    NE_/D_set_max_speed_accel_m came after it this tick (always so in the fixed order)",
  b "pc_vibe_comp" "_vibe_comp_enabled",
  f "pc_vel_ne_p_n" "NE_get_vel_pid().get_p().x", f "pc_vel_ne_p_e" "get_p().y",
  f "pc_vel_ne_i_n" "NE_get_vel_pid().get_i().x", f "pc_vel_ne_i_e" "get_i().y",
  f "pc_vel_ne_d_n" "NE_get_vel_pid().get_d().x", f "pc_vel_ne_d_e" "get_d().y",
  f "pc_vel_ne_ff_n" "NE_get_vel_pid().get_ff().x", f "pc_vel_ne_ff_e" "get_ff().y",
  f "pc_vel_d_i" "D_get_vel_pid().get_i()",
  f "pc_accel_d_p" "D_get_accel_pid().get_pid_info().P (after slew and PD scaling)",
  f "pc_accel_d_i" "get_pid_info().I", f "pc_accel_d_d" "get_pid_info().D",
  f "pc_accel_d_ff" "get_ff() = FF + DFF",
  f "pc_accel_d_imax" "D_get_accel_pid().imax() (rewritten at run time)",
  u "pc_internal_errors" "ArduPilot internal errors raised since init",
  u "pc_internal_errors_flow" "of which flow_of_control (update without init)",
  u "pc_internal_error_bits" "AP_InternalError error bits raised since init (error_t mask)",
  u "pc_internal_error_line" "line of the last internal error (__AP_LINE__)"]

/-! ### Clause builders -/

private def conj : List Expr → Expr
  | [] => tt
  | [e] => e
  | e :: es => e ∧. conj es

private def within (x : String) (lo hi : Expr) : Expr := lo ≤. .var x ∧. .var x ≤. hi
private def absLe (xs : List String) (c : Expr) : Expr := conj (xs.map fun x => abs (.var x) ≤. c)
private def cp (s : String) : String := s!"cmd_position_{s}"

/-- Every f32 output except the observer and the time-of-use-independent ones. -/
def floatOutputs : List String := (output.toList.filter (·.type == .f32)).map (·.name)

/-! ### Assumption -/

/-- ArduPilot's documented ranges (@Range in AC_PosControl.cpp var_info and
AC_AttitudeControl.cpp), widened to 0 where the default is 0 although the documented range starts
above it (PSC_D_ACC_FLTT and _FLTD default 0; PSC_NE_VEL_FF default 0). `accFilters` and
`atcLimits` are the filter and attitude-limit clauses, which the second statement changes. -/
def assumeParamsWith (accFilters atcLimits angleMax : Expr) : List Clause := [
  ⟨"pos_p_range", within "psc_ne_pos_p" 0.5 4 ∧. within "psc_d_pos_p" 0.5 4⟩,
  ⟨"ne_vel_range", within "psc_ne_vel_p" 0.1 10 ∧. within "psc_ne_vel_i" 0 10 ∧.
      within "psc_ne_vel_d" 0 1 ∧. within "psc_ne_vel_imax" 0 10 ∧.
      within "psc_ne_vel_flte" 0 100 ∧. within "psc_ne_vel_fltd" 0 100 ∧.
      within "psc_ne_vel_ff" 0 10⟩,
  ⟨"d_vel_range", within "psc_d_vel_p" 1 10 ∧. within "psc_d_vel_i" 0 10 ∧.
      within "psc_d_vel_d" 0 2 ∧. within "psc_d_vel_imax" 1 10 ∧.
      within "psc_d_vel_flte" 0 100 ∧. within "psc_d_vel_fltd" 0 100 ∧.
      within "psc_d_vel_ff" 0 2⟩,
  ⟨"d_acc_range", within "psc_d_acc_p" 0.01 0.25 ∧. within "psc_d_acc_i" 0 0.5 ∧.
      within "psc_d_acc_d" 0 0.1 ∧. within "psc_d_acc_imax" 0 1 ∧.
      within "psc_d_acc_ff" 0 0.1 ∧. accFilters ∧. within "psc_d_acc_fltd" 0 100 ∧.
      within "psc_d_acc_smax" 0 100 ∧. within "psc_d_acc_pdmx" 0 1 ∧.
      within "psc_d_acc_d_ff" 0 0.05⟩,
  ⟨"shaping_range", angleMax ∧. within "psc_ne_jerk" 1 50 ∧.
      within "psc_d_jerk" 1 50⟩,
  ⟨"atc_limits_range", atcLimits⟩]

def assumeParamsAsFirstStated : List Clause :=
  assumeParamsWith (within "psc_d_acc_fltt" 0 50 ∧. within "psc_d_acc_flte" 0 100)
    (within "atc_rate_r_max" 0 1080 ∧. within "atc_rate_p_max" 0 1080 ∧.
     within "atc_acc_r_max" 0 1800 ∧. within "atc_acc_p_max" 0 1800)
    (within "psc_angle_max" 0 45)

/-- The filter and attitude-limit clauses of the second and final statements. -/
def accFiltersOnOrOff : Expr :=
  ("psc_d_acc_fltt" =. 0 ∨. within "psc_d_acc_fltt" 1 50) ∧.
  ("psc_d_acc_flte" =. 0 ∨. within "psc_d_acc_flte" 1 100)

def atcLimitsOnOrOff : Expr :=
  ("atc_rate_r_max" =. 0 ∨. within "atc_rate_r_max" 1 1080) ∧.
  ("atc_rate_p_max" =. 0 ∨. within "atc_rate_p_max" 1 1080) ∧.
  ("atc_acc_r_max" =. 0 ∨. within "atc_acc_r_max" 1 1800) ∧.
  ("atc_acc_p_max" =. 0 ∨. within "atc_acc_p_max" 1 1800)

/-- Against the first statement: PSC_D_ACC_FLTT and _FLTE either 0 (off) or in their documented
range (1 to 50, 1 to 100 Hz), and the ATC_ rate and acceleration limits either 0 (off) or at least
1 deg/s, 1 deg/s/s. A positive value below those makes the jerk limits D_set_max_speed_accel_m and
NE_set_max_speed_accel_m derive (`MIN(GRAVITY, accel) * 2 pi FLTT / 5`, AC_PosControl.cpp:822;
`0.5 sqrt(accel * snap)`, :477) fall below FLT_EPSILON, and every input shaper then refuses them
with INTERNAL_ERROR(invalid_arg_or_result) (control.cpp:132-363). -/
def assumeParamsSecond : List Clause :=
  assumeParamsWith accFiltersOnOrOff atcLimitsOnOrOff (within "psc_angle_max" 0 45)

/-- Against the second statement, PSC_ANGLE_MAX is 0 (use ATC_ANGLE_MAX) or at least 1 deg (its
documented range is 0 to 45 in steps of 1). The second statement was refuted by the final
campaigns (seed 3, 500 x 200, case 420 step 8; regime flight seed 1, 300 x 200, case 204 step 0:
tilt 1.484 rad, unlimited): PSC_ANGLE_MAX = 6.8e-7 deg is `is_positive`, so get_lean_angle_max_rad
returns 1.2e-8 rad and the accel limit is g tan(1.2e-8) = 1.2e-7 m/s/s, which limit_accel_xy
(control.cpp:452) does not take as positive: it returns without limiting. Any PSC_ANGLE_MAX in
(FLT_EPSILON, about 7e-7) deg switches the lean-angle limit off altogether. -/
def assumeParams : List Clause :=
  assumeParamsWith accFiltersOnOrOff atcLimitsOnOrOff
    ("psc_angle_max" =. 0 ∨. within "psc_angle_max" 1 45)

/-- Bounded, physically sane signals. -/
def assumeSignals : List Clause := [
  ⟨"dt_range", within "dt" 0.0001 0.02⟩,
  ⟨"est_pos_bounded", absLe ["est_pos_n", "est_pos_e", "est_pos_d"] 10000⟩,
  ⟨"est_vel_bounded", absLe ["est_vel_n", "est_vel_e", "est_vel_d", "est_pos_rate_d"] 100⟩,
  ⟨"est_accel_bounded", abs "est_accel_ef_z" ≤. 100⟩,
  ⟨"est_yaw_range", abs "est_yaw" ≤. 3.1415927 ∧. abs "est_cos_yaw" ≤. 1 ∧.
      abs "est_sin_yaw" ≤. 1⟩,
  ⟨"est_scalers_range", within "est_gain_scaler_xy" 0 1 ∧.
      within "est_gain_scaler_z" 0 1⟩,
  ⟨"est_reset_counts_range", "est_pos_ne_reset_count" ≤. 65535 ∧.
      "est_pos_d_reset_count" ≤. 65535⟩,
  ⟨"ac_att_target_range", absLe ["ac_att_target_roll", "ac_att_target_pitch",
      "ac_att_target_yaw"] 3.1415927⟩,
  ⟨"ac_throttle_range", within "ac_throttle_in" 0 1⟩,
  -- get_althold_lean_angle_max_rad() >= 10 deg; lean_angle_max_rad() in [10, 80] deg
  ⟨"ac_lean_range", within "ac_althold_lean_angle_max" 0.17453292 1.5707964 ∧.
      within "ac_lean_angle_max" 0.17453292 1.3962634⟩,
  -- AP_MOTORS_THST_HOVER_MIN/MAX (AP_MotorsMulticopter.h:16-17)
  ⟨"hover_range", within "throttle_hover" 0.125 0.6875⟩,
  ⟨"tgt_bounded", absLe ["tgt_pos_n", "tgt_pos_e", "tgt_pos_d", "tgt_terrain_d"] 10000 ∧.
      absLe ["tgt_vel_n", "tgt_vel_e", "tgt_vel_d"] 100 ∧.
      absLe ["tgt_acc_n", "tgt_acc_e", "tgt_acc_d"] 100⟩]

/-- Command arguments: what the modes pass. `accMin` is the least maximum acceleration the
limit setters are given. -/
def assumeCommandsWith (accMin : Expr) : List Clause := [
  ⟨"reset_method_range", .var (cp "set_reset_handling_method_method") ≤. 1⟩,
  ⟨"ne_limits_args", within (cp "NE_set_max_speed_accel_m_speed") 0 100 ∧.
      within (cp "NE_set_max_speed_accel_m_accel") accMin 100 ∧.
      within (cp "NE_set_correction_speed_accel_m_speed") 0 100 ∧.
      within (cp "NE_set_correction_speed_accel_m_accel") 0 100 ∧.
      within (cp "NE_set_pos_error_max_m_error_max") 0 10000⟩,
  ⟨"d_limits_args", within (cp "D_set_max_speed_accel_m_down") 0 100 ∧.
      within (cp "D_set_max_speed_accel_m_up") 0 100 ∧.
      within (cp "D_set_max_speed_accel_m_accel") accMin 100 ∧.
      within (cp "D_set_correction_speed_accel_m_down") 0 100 ∧.
      within (cp "D_set_correction_speed_accel_m_up") 0 100 ∧.
      within (cp "D_set_correction_speed_accel_m_accel") 0 100⟩,
  ⟨"init_args", absLe [cp "init_pos_terrain_D_m_terrain_d", cp "set_pos_desired_NE_m_n",
      cp "set_pos_desired_NE_m_e"] 10000 ∧. abs (.var (cp "D_accel_pid_set_integrator_i")) ≤. 1⟩,
  ⟨"ne_input_args", absLe [cp "input_vel_accel_NE_m_vel_n", cp "input_vel_accel_NE_m_vel_e",
      cp "input_pos_vel_accel_NE_m_vel_n", cp "input_pos_vel_accel_NE_m_vel_e"] 100 ∧.
      absLe [cp "input_vel_accel_NE_m_accel_n", cp "input_vel_accel_NE_m_accel_e",
      cp "input_pos_vel_accel_NE_m_accel_n", cp "input_pos_vel_accel_NE_m_accel_e"] 100 ∧.
      absLe [cp "input_pos_vel_accel_NE_m_pos_n", cp "input_pos_vel_accel_NE_m_pos_e",
      cp "input_pos_NED_m_pos_n", cp "input_pos_NED_m_pos_e", cp "input_pos_NED_m_pos_d",
      cp "input_pos_NED_m_terrain_d"] 10000 ∧.
      within (cp "input_pos_NED_m_terrain_margin") 0 100⟩,
  ⟨"d_input_args", within (cp "D_relax_controller_throttle") 0 1 ∧.
      absLe [cp "D_set_pos_target_from_climb_rate_ms_climb_rate", cp "input_pos_vel_accel_D_m_vel",
      cp "input_vel_accel_D_m_vel"] 100 ∧.
      absLe [cp "input_pos_vel_accel_D_m_accel", cp "input_vel_accel_D_m_accel"] 100 ∧.
      absLe [cp "input_pos_vel_accel_D_m_pos", cp "D_set_alt_target_with_slew_m_alt"] 10000⟩]

def assumeCommandsAsFirstStated : List Clause := assumeCommandsWith 0

/-- Against the first statement, the maximum accelerations given to NE_ and D_set_max_speed_accel_m
are at least 0.5 m/s/s (WPNAV_ACCEL and WPNAV_ACCEL_Z, PILOT_ACCEL_Z and LOIT_ACC_MAX are at least
50 cm/s/s by their documented ranges). The first statement admitted 0 to 100. Refuted (seed 1,
100 x 100, case 1 step 27): NE_set_max_speed_accel_m(8.8, 1.2e-38) stores
_accel_max_ne_mss = 1.2e-38 (fabsf, no check, AC_PosControl.cpp:461), and the next
input_pos_vel_accel_NE_m's shape_pos_vel_accel_xy rejects accel_max <= FLT_EPSILON with
INTERNAL_ERROR(invalid_arg_or_result) (control.cpp:363), leaving the shaping undone; the same
happens with an NE_update_controller (NE_update_offsets shapes with the same limit). A zero
D acceleration is ignored by the setter (:815), a tiny positive one is not. -/
def assumeCommands : List Clause := assumeCommandsWith 0.5

/-! ### Guarantee -/

/-- The tilt of the thrust vector is within the lean-angle limit NE_update_controller applies,
`MIN(get_althold_lean_angle_max_rad(), get_lean_angle_max_rad())`, written out: the attitude
controller's altitude-hold limit, and PSC_ANGLE_MAX if positive, else ATC_ANGLE_MAX
(get_lean_angle_max_rad; the override is reset by NE_init_controller and never set here), within
`tol` rad. Stated when NE_update_controller ran this tick: the accel target is kept between
updates, and the attitude's limit can shrink meanwhile. -/
def leanWithin (positive : Expr → Expr) (tol : Expr) : Expr :=
  ¬. "pc_ne_updated" ∨.
    ("pc_lean_angle" ≤. "ac_althold_lean_angle_max" + tol ∧.
     ((¬. positive "psc_angle_max" ∧. "pc_lean_angle" ≤. "ac_lean_angle_max" + tol) ∨.
      (positive "psc_angle_max" ∧. "pc_lean_angle" ≤. "psc_angle_max" * 0.017453292 + tol)))

/-- As first stated: "PSC_ANGLE_MAX positive" read as `0 < x`, tolerance 1e-5 rad. Refuted (seed 1,
100 x 100, case 3 step 0): PSC_ANGLE_MAX = 3.9e-27 is positive, but get_lean_angle_max_rad tests
`is_positive`, which is `x >= FLT_EPSILON` (AP_Math.h:68), so the code falls back to ATC_ANGLE_MAX
(1.129 rad) and the tilt 0.1016 rad exceeded the clause's bound of 0. The statement misread the
code. -/
def leanWithinMaxAsFirstStated : Expr := leanWithin (fun x => 0 <. x) 0.00001

/-- `is_positive` as AP_Math.h:68 defines it for float: `x >= FLT_EPSILON`. -/
def isPositive (x : Expr) : Expr := 0.00000011920929 ≤. x

/-- Second statement: ArduPilot's threshold, tolerance still 1e-5 rad. Refuted (seed 1, 100 x 100,
case 54 step 1): tilt 0.4647611 rad against PSC_ANGLE_MAX = 0.4647404 rad. The unlimited accel
target was (-18.0, 1799.5) m/s/s (pc_limit_n/e) and the desired velocity (-1, 100) m/s, so
limit_accel_xy (control.cpp:449) took the cross-track branch: `accel - ref_unit * (ref_unit *
accel)` cancels a 1800 m/s/s vector down to the 4.92 m/s/s limit, and binary32 rounding of the
1800-sized terms (about 1e-4 m/s/s each) survives the cancellation: |accel| came out 4.91698
against the limit 4.91673. The excess scales with the unlimited acceleration, not with the
limit. -/
def leanWithinMaxSecond : Expr := leanWithin isPositive 0.00001

/-- The guarantee: tolerance 1e-5 rad plus 1e-7 rad per m/s/s of unlimited acceleration (the
rounding of the cancellation above is a few units of 6e-8 |accel| in m/s/s, i.e. below
2.5e-8 |accel| rad after dividing by g; 1e-7 leaves a factor 4). -/
def leanWithinMax : Expr :=
  leanWithin isPositive (0.00001 + 0.0000001 * (abs "pc_limit_n" + abs "pc_limit_e"))

/-- D_update_controller (vibration compensation off): throttle_in is the acceleration PID's
output with the hover throttle removed, exactly as AC_PosControl.cpp:1136-1145 adds it up:
`-(((P + D + I) + (FF + DFF)) - hover)` (AC_PID::update_all returns P_out + D_out + I_out). -/
def throttleFromAccelPid : Expr :=
  ¬. "pc_d_updated" ∨. "pc_vibe_comp" ∨.
    "throttle_in" =. -(("pc_accel_d_p" + "pc_accel_d_d" + "pc_accel_d_i" + "pc_accel_d_ff") -
      "throttle_hover")

/-- The brief's hover statement, as it follows from the code: when the acceleration PID's terms
are all zero the throttle is the hover throttle, and when the NE velocity PID's terms and the
desired and offset accelerations are zero, the thrust vector is level. Zero position and velocity
error with integrators at rest (the hand-checked case's step 0, the `hover` regime) make these
terms zero. -/
def hoverLevel : Expr :=
  (¬. ("pc_d_updated" ∧. ¬. "pc_vibe_comp" ∧. "pc_accel_d_p" =. 0 ∧. "pc_accel_d_i" =. 0 ∧.
      "pc_accel_d_d" =. 0 ∧. "pc_accel_d_ff" =. 0) ∨. "throttle_in" =. "throttle_hover") ∧.
  (¬. ("pc_ne_updated" ∧. conj (["pc_vel_ne_p_n", "pc_vel_ne_p_e", "pc_vel_ne_i_n",
      "pc_vel_ne_i_e", "pc_vel_ne_d_n", "pc_vel_ne_d_e", "pc_vel_ne_ff_n", "pc_vel_ne_ff_e",
      "pc_accel_desired_n", "pc_accel_desired_e", "pc_accel_offset_n",
      "pc_accel_offset_e"].map fun x => .var x =. 0)) ∨.
    ("thrust_vec_x" =. 0 ∧. "thrust_vec_y" =. 0))

/-- With the accel PID's P+D limit on (PSC_D_ACC_PDMX positive), no feed-forward (FF = D_FF = 0)
and vibration compensation off, the collective stays within the hover throttle plus or minus the
P+D limit and the integrator limit: AC_PID::update_all scales P and D so that |P + D| <= PDMX
(AC_PID.cpp, the PD sum limit), the integrator is constrained to IMAX (update_i), and IMAX is
the larger of PSC_D_ACC_IMAX and the hover throttle at that moment (AC_PosControl.cpp:1127).
Tolerance 1e-6 for the three binary32 additions. -/
def throttleBoundedByPdmx : Expr :=
  ¬. ("pc_d_updated" ∧. ¬. "pc_vibe_comp" ∧. isPositive "psc_d_acc_pdmx" ∧. "psc_d_acc_ff" =. 0 ∧.
      "psc_d_acc_d_ff" =. 0) ∨.
    abs ("throttle_in" - "throttle_hover") ≤. "psc_d_acc_pdmx" + "pc_accel_d_imax" + 0.000001

/-- The guarantee as first stated. Refuted (seed 1, 100 x 100):
* `lean_within_max` (as leanWithinMaxAsFirstStated): see there.
* `throttle_in_range`, 0 <= throttle_in <= 1 whenever D_update_controller ran: case 0 step 8 first,
  2804 of 10000 steps, down to -6.5e6. AC_PosControl does not bound the collective it hands to
  set_throttle_out: it is `hover - (P + D + I + FF + DFF)` of the accel PID (AC_PosControl.cpp:
  1136-1145), whose P term multiplies an unbounded acceleration error (the D velocity PID's output
  plus the desired acceleration, :1115-1119, no limit) and whose FF multiplies the filtered
  target. With stock parameters and near-hover inputs (regime stock_flight) it still left [0, 1]
  at 27% of steps (seed 3), driven by the random commands (position targets up to 1e4 m away).
  Not repaired by an assumption: no input range short of a settled vehicle keeps it in [0, 1].
  The consumers cope: AC_AttitudeControl_Multi::set_throttle_out passes it on unbounded, and
  AP_MotorsMulticopter::update_throttle_filter clamps the filtered throttle to [0, 1]
  (AP_MotorsMulticopter.cpp:355-360). The guarantee states what the code does instead:
  `throttle_from_accel_pid` (exact) and `throttle_bounded_by_pdmx`.
* `no_internal_error_but_flow`: under the first assumption (assumeCommandsAsFirstStated). -/
def guaranteeAsFirstStated : List Clause := [
  ⟨"outputs_finite", conj (floatOutputs.map fun x => finite (.var x))⟩,
  ⟨"thrust_z_gravity", "thrust_vec_z" =. -9.80665⟩,
  ⟨"lean_within_max", leanWithinMaxAsFirstStated⟩,
  ⟨"throttle_in_range", ¬. "pc_d_updated" ∨. within "throttle_in" 0 1⟩,
  ⟨"throttle_from_accel_pid", throttleFromAccelPid⟩,
  ⟨"hover_level", hoverLevel⟩,
  ⟨"throttle_set_by_d_update", "pc_throttle_set" =. "pc_d_updated" ∧.
      (¬. "pc_throttle_set" ∨. ("pc_throttle_angle_boost" ∧. "pc_throttle_cutoff_hz" =. 2))⟩,
  ⟨"no_internal_error_but_flow", "pc_internal_errors" =. "pc_internal_errors_flow"⟩]

def contractAsFirstStated : Contract where
  assume := assumeParamsAsFirstStated ++ assumeSignals ++ assumeCommandsAsFirstStated
  guarantee := guaranteeAsFirstStated

/-- The guarantee. Against the first statement: `lean_within_max` corrected (ArduPilot's
is_positive, and a tolerance that scales with the unlimited acceleration; see leanWithinMax*),
`throttle_in_range` dropped (refuted; see guaranteeAsFirstStated) and replaced by
`throttle_bounded_by_pdmx`, and `angles_bounded` added: after NE_update_controller the roll and
pitch targets are atanf results (AC_PosControl.cpp:1622-1624). Stated first without the
condition, it was refuted at once (seed 1, case 0 step 2): NE_init_controller copies the attitude
target, up to pi, into the roll and pitch targets (:551-552), and they stay there until the next
NE update. The flow-of-control internal error is excluded from
`no_internal_error_but_flow` on purpose: it is ArduCopter's own report that a mode ran an update
without initializing the controller at the previous tick, i.e. a supervisor obligation. -/
def guarantee : List Clause := [
  ⟨"outputs_finite", conj (floatOutputs.map fun x => finite (.var x))⟩,
  ⟨"thrust_z_gravity", "thrust_vec_z" =. -9.80665⟩,
  ⟨"lean_within_max", leanWithinMax⟩,
  ⟨"throttle_from_accel_pid", throttleFromAccelPid⟩,
  ⟨"throttle_bounded_by_pdmx", throttleBoundedByPdmx⟩,
  ⟨"hover_level", hoverLevel⟩,
  ⟨"angles_bounded", ¬. "pc_ne_updated" ∨.
      (abs "pc_roll" ≤. 1.5707964 ∧. abs "pc_pitch" ≤. 1.5707964)⟩,
  ⟨"throttle_set_by_d_update", "pc_throttle_set" =. "pc_d_updated" ∧.
      (¬. "pc_throttle_set" ∨. ("pc_throttle_angle_boost" ∧. "pc_throttle_cutoff_hz" =. 2))⟩,
  ⟨"no_internal_error_but_flow", "pc_internal_errors" =. "pc_internal_errors_flow"⟩]

/-- The contract of the stage as built alone. Not refuted; replaced when the stages were
composed. Kept for the record, not used. -/
def contractAlone : Contract where
  assume := assumeParams ++ assumeSignals ++ assumeCommands
  guarantee := guarantee

/-- The loiter stage's hand-over (`loiterHandover`), added with that stage: its targets bounded as
the guidance stage's are (`tgt_bounded`), and the arguments of its calls, when called, as the
supervisor's own commands of those methods are bounded (`ne_limits_args`, `init_args`). -/
def loiterAssume : List Clause := [
  ⟨"lt_tgt_bounded", absLe ["lt_tgt_pos_n", "lt_tgt_pos_e"] 10000 ∧.
      absLe ["lt_tgt_vel_n", "lt_tgt_vel_e"] 100 ∧. absLe ["lt_tgt_acc_n", "lt_tgt_acc_e"] 100⟩,
  ⟨"lt_handover_args",
    (¬. "lt_tgt_ne_set_correction_speed_accel" ∨. (within "lt_tgt_ne_correction_speed" 0 100 ∧.
        within "lt_tgt_ne_correction_accel" 0 100)) ∧.
    (¬. "lt_cmd_position_NE_set_pos_error_max_m" ∨.
        within "lt_cmd_position_NE_set_pos_error_max_m_error_max" 0 10000) ∧.
    (¬. "lt_cmd_position_set_pos_desired_NE_m" ∨.
        absLe ["lt_cmd_position_set_pos_desired_NE_m_n", "lt_cmd_position_set_pos_desired_NE_m_e"]
          10000)⟩]

/-- The signals when composed. Against the stage alone:
* `ac_throttle_range` widened from [0, 1] to |ac_throttle_in| ≤ 1e15: get_throttle_in() is the
  argument of the attitude controller's last set_throttle_out, i.e. this stage's own throttle_in
  of the previous tick, which is not in [0, 1] (see guaranteeAsFirstStated). D_init_controller
  is its only reader: `set_integrator(-(throttle_in - hover) - …)`, which constrains to ±IMAX
  (AC_PosControl.cpp:919-921, AC_PID.cpp:436), so a magnitude of 1e15 cannot overflow.
* `ac_att_target_range` widened for the yaw target: finite instead of within ±π. The stage only
  copies it, into _yaw_target_rad (NE_init_controller, AC_PosControl.cpp:553; the yaw update when
  slow, :1668) and out through get_yaw_rad(); no arithmetic or trigonometry reads it. The
  attitude stage's yaw target is not bounded (it accumulates, AC_AttitudeControl.cpp:444, 576),
  so the narrower statement was an open obligation of every composite.
* `est_accel_bounded` widened from 100 to 1e4 m/s/s. 100 was a physical guess, and the
  supervisor's closed-loop flight refuted it as an assumption on what the plant delivers: the
  simulator's ground contact at touchdown gives -133.6 and -207 m/s/s. The code needs only that
  the D acceleration PID's arithmetic stays finite: get_estimated_accel_D_mss() = accel_ef.z + g
  is the PID's measurement in D_update_controller (AC_PosControl.cpp:1115-1145) and is
  constrained to the D acceleration limit in D_init_controller (:912); AC_PID::update_all with
  |measurement| ≤ 1e4 and the documented gains cannot overflow (the bound `rate_pid` assumes on
  its measurement). Physical accelerometer ranges (16 g = 157 m/s/s, 32 g on some IMUs) are not
  what the code needs, and a contact spike may exceed them.
* `tgt_handover_args` added: the arguments of the guidance stage's limit setters, when called,
  as the supervisor's own limit commands are bounded (`ne_limits_args`, `d_limits_args`), except
  that a maximum acceleration down to 0.1 m/s/s is admitted (the guidance stage's
  `limits_handed_over` guarantees [0.1, 20]; the supervisor's commands keep 0.5, below which
  only values under FLT_EPSILON were refuted, see assumeCommands).
The guidance stage's update (tgt_valid with NED targets) includes AC_WPNav's own
NE_update_controller (AC_WPNav.cpp:741); the step makes one NE_update_controller at the end of
the NE phase when the supervisor commands it or the guidance stage made it (a first version
called it right after set_pos_vel_accel_NED_m and refuted `angles_bounded`: seed 1, 200 x 100,
833 steps, first at case 0 step 29, because a random NE_relax_velocity_controller command of the
same tick, made after it, re-initializes the roll and pitch targets from the attitude target; in
ArduCopter a mode running update_wpnav makes no other NE call). -/
def assumeSignalsComposed : List Clause :=
  (assumeSignals.map fun c =>
    if c.name == "ac_throttle_range" then ⟨"ac_throttle_range", abs "ac_throttle_in" ≤. 1e15⟩
    else if c.name == "ac_att_target_range" then
      ⟨"ac_att_target_range", abs "ac_att_target_roll" ≤. 3.1415927 ∧.
        abs "ac_att_target_pitch" ≤. 3.1415927 ∧. finite "ac_att_target_yaw"⟩
    else if c.name == "est_accel_bounded" then ⟨"est_accel_bounded", abs "est_accel_ef_z" ≤. 1e4⟩
    else c) ++ [
  ⟨"tgt_handover_args",
    (¬. "tgt_ne_set_max_speed_accel" ∨. (within "tgt_ne_max_speed" 0 100 ∧.
        within "tgt_ne_max_accel" 0.1 100)) ∧.
    (¬. "tgt_ne_set_correction_speed_accel" ∨. (within "tgt_ne_correction_speed" 0 100 ∧.
        within "tgt_ne_correction_accel" 0 100)) ∧.
    (¬. "tgt_d_set_max_speed_accel" ∨. (within "tgt_max_speed_down" 0 100 ∧.
        within "tgt_max_speed_up" 0 100 ∧. within "tgt_d_max_accel" 0.1 100)) ∧.
    (¬. "tgt_d_set_correction_speed_accel" ∨. (within "tgt_d_correction_speed_down" 0 100 ∧.
        within "tgt_d_correction_speed_up" 0 100 ∧. within "tgt_d_correction_accel" 0 100))⟩,
  -- the same-tick throttle (`sameTickThrottle`), when called: what `ac_throttle_range` admits
  -- for the previous tick's throttle, which it replaces as D_init_controller's reading
  ⟨"same_tick_throttle_range", ¬. "cmd_attitude_set_throttle_out" ∨.
      abs "cmd_attitude_set_throttle_out_throttle_in" ≤. 1e15⟩] ++ loiterAssume

/-- The limits after a guidance call, with "the setter ignores the argument" as `zero`. -/
def limitsFollow (zero : Expr → Expr) : Expr :=
  (¬. "tgt_ne_set_max_speed_accel" ∨. ("pc_ne_max_speed" =. abs "tgt_ne_max_speed" ∧.
      "pc_ne_max_accel" =. abs "tgt_ne_max_accel")) ∧.
  (¬. "tgt_d_set_max_speed_accel" ∨.
    ((zero "tgt_max_speed_down" ∨. "pc_max_speed_down" =. abs "tgt_max_speed_down") ∧.
     (zero "tgt_max_speed_up" ∨. "pc_max_speed_up" =. abs "tgt_max_speed_up") ∧.
     (zero "tgt_d_max_accel" ∨. "pc_d_max_accel" =. abs "tgt_d_max_accel")))

/-- `is_zero` as AP_Math.h defines it for float: |x| < FLT_EPSILON. -/
def isZeroF (x : Expr) : Expr := abs x <. 0.00000011920929

/-- `limits_follow_guidance` as first stated, with "ignored" read as `= 0`. Refuted (seed 1,
200 x 100: 17 steps, first at case 0 step 25; flight seed 2: 10 steps): D_set_max_speed_accel_m
ignores an argument that is_zero, |x| < FLT_EPSILON (AC_PosControl.cpp:809-816), not only 0;
the counterexample's descent speed 3.9e-28 was ignored. The statement misread the code; kept for
the record, not used. -/
def limitsFollowAsFirstStated : Clause :=
  ⟨"limits_follow_guidance", limitsFollow fun x => x =. 0⟩

/-- The guarantee when composed. Against the stage alone:
* `throttle_in_bounded`: |throttle_in| ≤ 1e15 (0 when D_update_controller did not run), for the
  attitude stage's `throttle_in_range`. Tested, not derived: the largest magnitude the campaigns
  saw is recorded with them.
* `lean_limit_range` (added with the loiter stage, which reads it): get_lean_angle_max_rad()
  (AC_PosControl.cpp:1170-1179) is the override if positive (only set_lean_angle_max_rad sets it,
  which no command of this stage calls, and NE_init_controller zeroes it, :555), else
  ATC_ANGLE_MAX's lean_angle_max_rad() (`ac_lean_range`: 10 to 80 deg) when PSC_ANGLE_MAX is not
  positive, else radians(PSC_ANGLE_MAX) (1 to 45 deg): within [1, 80] deg.
* `limits_follow_guidance`: after a guidance call of NE_ or D_set_max_speed_accel_m (made after
  every supervisor command that sets limits, see the step order), the limits the stage reports
  are that call's arguments as the setters store them (fabsf; a D argument that is_zero is ignored,
  AC_PosControl.cpp:458-461, 806-817): the coherence the guidance stage checks with
  `wp_limits_incoherent`. -/
def guaranteeComposed : List Clause := guarantee ++ [
  ⟨"throttle_in_bounded", abs "throttle_in" ≤. 1e15⟩,
  ⟨"limits_follow_guidance", limitsFollow isZeroF⟩,
  ⟨"lean_limit_range", within "pc_lean_angle_max" 0.0174 1.3962635⟩]

/-- The command arguments when composed: each range applies only when its method is called
this tick (`assumeCommands` bounds them at every tick, also when the method is not called, which
excludes a supervisor that leaves the arguments of an uncalled method at 0: the first closed-loop
flight failed `ne_limits_args` and `d_limits_args` at every tick after the first, a maximum
acceleration 0 < 0.5 m/s/s for a setter not called). The stage reads an argument only when its
Boolean is set (adapter.cpp), so this widens the assumption without changing what the code
sees. Not refuted; `assumeCommands` is kept for the record. -/
def assumeCommandsComposed : List Clause :=
  let called (m : String) (e : Expr) : Expr := ¬. .var (cp m) ∨. e
  [⟨"reset_method_range", called "set_reset_handling_method"
      (.var (cp "set_reset_handling_method_method") ≤. 1)⟩,
   ⟨"ne_limits_args",
      called "NE_set_max_speed_accel_m" (within (cp "NE_set_max_speed_accel_m_speed") 0 100 ∧.
        within (cp "NE_set_max_speed_accel_m_accel") 0.5 100) ∧.
      called "NE_set_correction_speed_accel_m"
        (within (cp "NE_set_correction_speed_accel_m_speed") 0 100 ∧.
         within (cp "NE_set_correction_speed_accel_m_accel") 0 100) ∧.
      called "NE_set_pos_error_max_m" (within (cp "NE_set_pos_error_max_m_error_max") 0 10000)⟩,
   ⟨"d_limits_args",
      called "D_set_max_speed_accel_m" (within (cp "D_set_max_speed_accel_m_down") 0 100 ∧.
        within (cp "D_set_max_speed_accel_m_up") 0 100 ∧.
        within (cp "D_set_max_speed_accel_m_accel") 0.5 100) ∧.
      called "D_set_correction_speed_accel_m"
        (within (cp "D_set_correction_speed_accel_m_down") 0 100 ∧.
         within (cp "D_set_correction_speed_accel_m_up") 0 100 ∧.
         within (cp "D_set_correction_speed_accel_m_accel") 0 100)⟩,
   ⟨"init_args",
      called "init_pos_terrain_D_m" (absLe [cp "init_pos_terrain_D_m_terrain_d"] 10000) ∧.
      called "set_pos_desired_NE_m"
        (absLe [cp "set_pos_desired_NE_m_n", cp "set_pos_desired_NE_m_e"] 10000) ∧.
      called "D_accel_pid_set_integrator"
        (abs (.var (cp "D_accel_pid_set_integrator_i")) ≤. 1)⟩,
   ⟨"ne_input_args",
      called "input_vel_accel_NE_m"
        (absLe [cp "input_vel_accel_NE_m_vel_n", cp "input_vel_accel_NE_m_vel_e"] 100 ∧.
         absLe [cp "input_vel_accel_NE_m_accel_n", cp "input_vel_accel_NE_m_accel_e"] 100) ∧.
      called "input_pos_vel_accel_NE_m"
        (absLe [cp "input_pos_vel_accel_NE_m_vel_n", cp "input_pos_vel_accel_NE_m_vel_e"] 100 ∧.
         absLe [cp "input_pos_vel_accel_NE_m_accel_n", cp "input_pos_vel_accel_NE_m_accel_e"] 100 ∧.
         absLe [cp "input_pos_vel_accel_NE_m_pos_n", cp "input_pos_vel_accel_NE_m_pos_e"] 10000) ∧.
      called "input_pos_NED_m"
        (absLe [cp "input_pos_NED_m_pos_n", cp "input_pos_NED_m_pos_e", cp "input_pos_NED_m_pos_d",
          cp "input_pos_NED_m_terrain_d"] 10000 ∧.
         within (cp "input_pos_NED_m_terrain_margin") 0 100)⟩,
   ⟨"d_input_args",
      called "D_relax_controller" (within (cp "D_relax_controller_throttle") 0 1) ∧.
      called "D_set_pos_target_from_climb_rate_ms"
        (absLe [cp "D_set_pos_target_from_climb_rate_ms_climb_rate"] 100) ∧.
      called "input_pos_vel_accel_D_m"
        (absLe [cp "input_pos_vel_accel_D_m_vel"] 100 ∧.
         absLe [cp "input_pos_vel_accel_D_m_accel"] 100 ∧.
         absLe [cp "input_pos_vel_accel_D_m_pos"] 10000) ∧.
      called "input_vel_accel_D_m"
        (absLe [cp "input_vel_accel_D_m_vel"] 100 ∧. absLe [cp "input_vel_accel_D_m_accel"] 100) ∧.
      called "D_set_alt_target_with_slew_m" (absLe [cp "D_set_alt_target_with_slew_m_alt"] 10000)⟩]

/-- The guarantee with the supervisor's call order (`_seq`). Every clause about the state
after an update (`lean_within_max`, `throttle_from_accel_pid`, `throttle_bounded_by_pdmx`,
`hover_level`, `angles_bounded`) and `limits_follow_guidance` were stated for the fixed order,
in which the update is the last call of its axis and the guidance hand-over follows every
supervisor limit setter. With random `_seq` they were refuted (commands regime seed 11, 200 x
100: angles_bounded 3757 steps, throttle_from_accel_pid 336, hover_level 73,
limits_follow_guidance 12; flight regime seed 12: angles_bounded 6281, throttle_from_accel_pid
638, lean_within_max 1): an NE_init_controller after the NE update copies the attitude target
into the roll and pitch targets again, a D_relax_controller or D_init_controller after the D
update moves the accel PID's integrator and info, a supervisor limit setter after the hand-over
overrides it. ArduCopter itself makes such orders (GUIDED takeoff: D_update_controller, then
the GCS's D_init_controller). Restated: each holds when the update (the hand-over) was the last
call of its axis this tick (`pc_ne_update_last`, `pc_d_update_last`, `pc_handover_limits_last`,
always true in the fixed order, so the earlier evidence is for the same statements there). -/
def guaranteeFixedOrder : List Clause := guaranteeComposed

def guaranteeSeq : List Clause :=
  guaranteeComposed.map fun c =>
    let sub (a b : String) : Clause := ⟨c.name, c.expr.mapVars fun x => if x == a then .var b
      else .var x⟩
    if c.name == "lean_within_max" || c.name == "angles_bounded" then
      sub "pc_ne_updated" "pc_ne_update_last"
    else if c.name == "throttle_from_accel_pid" || c.name == "throttle_bounded_by_pdmx" then
      sub "pc_d_updated" "pc_d_update_last"
    else if c.name == "hover_level" then
      ⟨c.name, c.expr.mapVars fun x => if x == "pc_ne_updated" then .var "pc_ne_update_last"
        else if x == "pc_d_updated" then .var "pc_d_update_last" else .var x⟩
    else if c.name == "limits_follow_guidance" then
      ⟨c.name, ¬. "pc_handover_limits_last" ∨. c.expr⟩
    else c

def contract : Contract where
  assume := assumeParams ++ assumeSignalsComposed ++ assumeCommandsComposed
  guarantee := guaranteeSeq

/-! ### Regimes and coverage -/

/-- Flight: the estimator valid, the clock advancing one 400 Hz tick per step, estimates updated
and both controllers updated every tick, as in every position-controlled mode. -/
def flightClauses : List Clause := [
  ⟨"est_valid", "est_pos_ok" ∧. "est_vel_ok" ∧.
      "est_pos_rate_d_ok"⟩,
  ⟨"every_tick", .var (cp "update_estimates") ∧. .var (cp "NE_update_controller") ∧.
      .var (cp "D_update_controller")⟩,
  ⟨"loop_dt", within "dt" 0.0024 0.0026⟩]

/-- Sampling aid for the same-tick throttle argument, as `assumeCommands` for the others:
the throttle range ArduCopter's set_throttle_out callers pass, [0, 1]. -/
def sameTickThrottleSampled : Clause :=
  ⟨"same_tick_throttle_sampled", within "cmd_attitude_set_throttle_out_throttle_in" 0 1⟩

/-- Sampling aid for the loiter stage's hand-over, as `assumeCommands` for the supervisor's: its
arguments in range whether called or not. -/
def loiterSampled : Clause :=
  ⟨"loiter_args_sampled", absLe ["lt_tgt_pos_n", "lt_tgt_pos_e", "lt_cmd_position_set_pos_desired_NE_m_n",
      "lt_cmd_position_set_pos_desired_NE_m_e"] 1000 ∧. absLe ["lt_tgt_vel_n", "lt_tgt_vel_e",
      "lt_tgt_acc_n", "lt_tgt_acc_e"] 10 ∧. within "lt_tgt_ne_correction_speed" 0 10 ∧.
      within "lt_tgt_ne_correction_accel" 0 10 ∧.
      within "lt_cmd_position_NE_set_pos_error_max_m_error_max" 0 10⟩

/-- No loiter-stage call (the flows the regimes below stood for before that stage existed). -/
def loiterOff : Clause :=
  ⟨"no_loiter", conj ((loiterHandover.filter (·.type == .bool)).map fun f => ¬. .var f.name)⟩

/-- Sampling aid: the generator draws a field from the conjuncts that mention only that field,
so the call-conditional argument ranges of `assumeCommandsComposed` leave the arguments
unbounded and almost every draw fails. Every regime therefore adds the unconditional ranges of
`assumeCommands` (a regime only steers sampling); the regime `commands` is that alone, the
campaign without a regime is empty. -/
def argsSampled : Regime where
  name := "commands"
  doc := "the contract's inputs, command arguments in range whether called or not (sampling)"
  clauses := assumeCommands ++ [sameTickThrottleSampled, loiterSampled]

def flight : Regime where
  name := "flight"
  doc := "estimates valid, update_estimates and both updates every tick, 400 Hz"
  clauses := flightClauses ++ assumeCommands ++ [sameTickThrottleSampled, loiterSampled, loiterOff]
  hints := [.increasing "now_ms" 1000 2 3]

/-- ArduCopter's default PSC_ and ATC_ parameters (AC_PosControl.cpp:53-79 for Copter, var_info
defaults :125, :136, :145; AC_AttitudeControl.cpp:104, :114, :193, :203 and
AC_ATTITUDE_CONTROL_ACCEL_RP_MAX_DEFAULT_DEGSS = 1100, AC_AttitudeControl.h:22). The PID
constructors' defaults: NE_VEL (2, 1, 0.25, FF 0, IMAX 10, FLTE 5, FLTD 5), D_VEL (5, 0, 0, FF 0,
IMAX 10, FLTE 5, FLTD 5), D_ACC (0.05, 0.1, 0, FF 0, IMAX 0.8, FLTT 0, FLTE 20, FLTD 0, SMAX 0,
D_FF 0); PDMX defaults to 0. -/
def stockParams : List Clause := [
  ⟨"stock_pos", "psc_ne_pos_p" =. 1 ∧. "psc_d_pos_p" =. 1⟩,
  ⟨"stock_ne_vel", "psc_ne_vel_p" =. 2 ∧. "psc_ne_vel_i" =. 1 ∧. "psc_ne_vel_d" =. 0.25 ∧.
      "psc_ne_vel_imax" =. 10 ∧. "psc_ne_vel_flte" =. 5 ∧. "psc_ne_vel_fltd" =. 5 ∧.
      "psc_ne_vel_ff" =. 0⟩,
  ⟨"stock_d_vel", "psc_d_vel_p" =. 5 ∧. "psc_d_vel_i" =. 0 ∧. "psc_d_vel_d" =. 0 ∧.
      "psc_d_vel_imax" =. 10 ∧. "psc_d_vel_flte" =. 5 ∧. "psc_d_vel_fltd" =. 5 ∧.
      "psc_d_vel_ff" =. 0⟩,
  ⟨"stock_d_acc", "psc_d_acc_p" =. 0.05 ∧. "psc_d_acc_i" =. 0.1 ∧. "psc_d_acc_d" =. 0 ∧.
      "psc_d_acc_imax" =. 0.8 ∧. "psc_d_acc_ff" =. 0 ∧. "psc_d_acc_fltt" =. 0 ∧.
      "psc_d_acc_flte" =. 20 ∧. "psc_d_acc_fltd" =. 0 ∧. "psc_d_acc_smax" =. 0 ∧.
      "psc_d_acc_pdmx" =. 0 ∧. "psc_d_acc_d_ff" =. 0⟩,
  ⟨"stock_shaping", "psc_angle_max" =. 0 ∧. "psc_ne_jerk" =. 5 ∧. "psc_d_jerk" =. 5⟩,
  ⟨"stock_atc", "atc_rate_r_max" =. 0 ∧. "atc_rate_p_max" =. 0 ∧. "atc_acc_r_max" =. 1100 ∧.
      "atc_acc_p_max" =. 1100⟩]

/-- Near-hover flight inputs: a level vehicle near its targets, gentle guidance targets, the
default ATC_ANGLE_MAX (30 deg) and the hover throttle at its default. -/
def stockInputs : List Clause := [
  ⟨"near_hover_est", absLe ["est_vel_n", "est_vel_e", "est_vel_d", "est_pos_rate_d"] 2 ∧.
      within "est_accel_ef_z" (-11) (-8.5) ∧. absLe ["est_pos_n", "est_pos_e", "est_pos_d"] 20⟩,
  ⟨"near_hover_att", absLe ["ac_att_target_roll", "ac_att_target_pitch"] 0.2 ∧.
      "ac_lean_angle_max" =. 0.5235988 ∧. within "ac_althold_lean_angle_max" 0.5 1 ∧.
      within "throttle_hover" 0.3 0.4⟩,
  ⟨"gentle_targets", absLe ["tgt_pos_n", "tgt_pos_e", "tgt_pos_d"] 20 ∧.
      absLe ["tgt_vel_n", "tgt_vel_e", "tgt_vel_d"] 2 ∧.
      absLe ["tgt_acc_n", "tgt_acc_e", "tgt_acc_d"] 1⟩,
  ⟨"scalers_one", "est_gain_scaler_xy" =. 1 ∧. "est_gain_scaler_z" =. 1⟩]

def stockFlight : Regime where
  name := "stock_flight"
  doc := "ArduCopter's default PSC_/ATC_ parameters, near-hover inputs, flight's clauses"
  clauses := stockParams ++ stockInputs ++ flightClauses ++ assumeCommands ++
    [sameTickThrottleSampled, loiterSampled, loiterOff]
  hints := flight.hints

/-- The command Booleans (not their Boolean arguments). -/
def commandBools : List String :=
  (commands.filter fun f => f.type == .bool && f.doc.endsWith "is called this tick").map (·.name)

/-- Hover at the target: the vehicle at the EKF origin, at rest, level, measuring exactly 1 g;
the estimates updated and both controllers updated every tick and nothing else called (the
controller starts from ArduCopter's zeroed object: targets at the origin, integrators 0). The
brief's hover statement: the thrust vector level and throttle_in the hover throttle (coverage
`level_hover`; hover_level is the clause). -/
def hover : Regime where
  name := "hover"
  doc := "at rest at the target, 1 g measured, only update_estimates and the two updates"
  clauses := flightClauses ++ assumeCommands ++ [sameTickThrottleSampled, loiterSampled, loiterOff,
    ⟨"at_rest", conj (["est_pos_n", "est_pos_e", "est_pos_d", "est_vel_n", "est_vel_e",
        "est_vel_d", "est_pos_rate_d", "est_yaw", "est_sin_yaw", "ac_att_target_roll",
        "ac_att_target_pitch", "ac_att_target_yaw"].map fun x => .var x =. 0) ∧.
        "est_accel_ef_z" =. -9.80665 ∧. "est_cos_yaw" =. 1 ∧.
        "est_gain_scaler_xy" =. 1 ∧. "est_gain_scaler_z" =. 1⟩,
    ⟨"nothing_else", conj ((commandBools.filter fun c => c != cp "update_estimates" &&
        c != cp "NE_update_controller" && c != cp "D_update_controller").map fun c => ¬. .var c) ∧.
        ¬. "tgt_valid" ∧. ¬. "limit_throttle_lower" ∧. ¬. "limit_throttle_upper" ∧.
        ¬. .var (cp "update_estimates_high_vibes") ∧.
        conj ((handover.filter (·.type == .bool)).map fun f => ¬. .var f.name)⟩]
  hints := flight.hints

/-- LOITER flying as the loiter stage hands it over: every tick update_estimates, the loiter
stage's targets and NE update, D_update_controller; nothing else on the NE axis; gentle targets;
ArduCopter's default parameters and near-hover inputs. -/
def loiter : Regime where
  name := "loiter"
  doc := "stock parameters, near hover, the loiter stage's targets and NE update every tick"
  clauses := stockParams ++ stockInputs ++ assumeCommands ++ [sameTickThrottleSampled,
    loiterSampled,
    ⟨"est_valid", "est_pos_ok" ∧. "est_vel_ok" ∧. "est_pos_rate_d_ok"⟩,
    ⟨"loop_dt", within "dt" 0.0024 0.0026⟩,
    ⟨"loiter_tick", .var (cp "update_estimates") ∧. .var (cp "D_update_controller") ∧.
        "lt_tgt_valid" ∧. "lt_tgt_ne_update" ∧. ¬. "tgt_valid" ∧.
        conj ((commandBools.filter fun c => c != cp "update_estimates" &&
          c != cp "D_update_controller" && c != cp "D_set_pos_target_from_climb_rate_ms" &&
          c != cp "D_set_max_speed_accel_m").map fun c => ¬. .var c) ∧.
        conj ((handover.filter (·.type == .bool)).map fun f => ¬. .var f.name) ∧.
        conj ((loiterHandover.filter fun f => f.type == .bool && f.name != "lt_tgt_valid" &&
          f.name != "lt_tgt_ne_update").map fun f => ¬. .var f.name)⟩,
    ⟨"gentle_loiter_targets", absLe ["lt_tgt_pos_n", "lt_tgt_pos_e"] 20 ∧.
        absLe ["lt_tgt_vel_n", "lt_tgt_vel_e"] 2 ∧. absLe ["lt_tgt_acc_n", "lt_tgt_acc_e"] 1⟩]
  hints := flight.hints

def coverage : List Clause := [
  ⟨"level_hover", "thrust_vec_x" =. 0 ∧. "thrust_vec_y" =. 0 ∧. "throttle_in" =. "throttle_hover"⟩,
  ⟨"ne_updated", "pc_ne_updated"⟩,
  ⟨"d_updated", "pc_d_updated"⟩,
  ⟨"ne_accel_limited", ¬. ("pc_limit_n" =. 0 ∧. "pc_limit_e" =. 0)⟩,
  ⟨"throttle_limit_flag", ¬. ("pc_limit_d" =. 0)⟩,
  ⟨"lean_at_limit", "pc_ne_updated" ∧. "ac_althold_lean_angle_max" ≤. "pc_lean_angle" + 0.001⟩,
  ⟨"throttle_outside_0_1", "pc_d_updated" ∧. ¬. within "throttle_in" 0 1⟩,
  ⟨"flow_error_seen", 0 <. "pc_internal_errors_flow"⟩,
  ⟨"pdmx_bound_applies", "pc_d_updated" ∧. ¬. "pc_vibe_comp" ∧. isPositive "psc_d_acc_pdmx" ∧.
      "psc_d_acc_ff" =. 0 ∧. "psc_d_acc_d_ff" =. 0⟩,
  ⟨"ekf_reset_seen", "pc_ne_updated" ∧. ¬. ("pc_pos_offset_n" =. 0 ∧. "pc_pos_offset_e" =. 0)⟩]

def module : Module where
  name := "position"
  doc := "ArduCopter's AC_PosControl with its P/PID controllers, stepped as the modes call it"
  params := params
  input := input
  output := output
  contract := contract
  exe := "build/modules/position/position"
  stack := .ardupilot
  regimes := [argsSampled, flight, stockFlight, hover, loiter]
  coverage := coverage

end Ardupilot.Modules.Position
