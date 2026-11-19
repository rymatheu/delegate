// stubs_attitude.cpp: the attitude controller.
//
// The attitude stage is its own module. AC_PosControl reads from it the attitude target
// (get_att_target_euler_rad), the throttle it was last given (get_throttle_in), the lean-angle
// limits, the body-frame feed-forward switch and its rate and acceleration limits, and writes the
// collective with set_throttle_out. HarnessAttitude (stand_ins.h) derives from the real
// AC_AttitudeControl; the out-of-line members of the base class, defined in AC_AttitudeControl.cpp
// (not compiled), are defined here.
//
//   symbol                                   why it is outside the stage, and what stands in
//   AC_AttitudeControl::_singleton, var_info static members (AC_AttitudeControl.cpp). Storage;
//                                            var_info is an empty table (parameter defaults cut).
//   AC_AttitudeControl::get_althold_lean_angle_max_rad()
//                                            the attitude stage's altitude-hold lean limit
//                                            (AC_AttitudeControl.cpp:1407). Returns the input
//                                            ac_althold_lean_angle_max (the method's value).
//   AC_AttitudeControl::lean_angle_max_rad() ATC_ANGLE_MAX, constrained (AC_AttitudeControl.cpp:1419).
//                                            Returns the input ac_lean_angle_max.
//   HarnessAttitude::set_throttle_out        pure virtual in the base; records its arguments (the
//                                            outputs throttle_in, pc_throttle_angle_boost,
//                                            pc_throttle_cutoff_hz) and sets _throttle_in, as the
//                                            real AC_AttitudeControl_Multi::set_throttle_out does
//                                            first.
//   every other virtual member of the base and the pure virtuals of HarnessAttitude, and
//   AC_AttitudeControl::relax_attitude_controllers(), AP_BoardConfig::config_error (reached from
//   the base's vtable)                       the attitude controller's own work, never called by
//                                            the position controller. Abort.
#include <AC_AttitudeControl/AC_AttitudeControl.h>
#include <AP_BoardConfig/AP_BoardConfig.h>

AC_AttitudeControl *AC_AttitudeControl::_singleton;
const AP_Param::GroupInfo AC_AttitudeControl::var_info[] = {
    AP_GROUPEND
};

float AC_AttitudeControl::get_althold_lean_angle_max_rad() const
{
    return harness_cut.althold_lean_angle_max_rad;
}

float AC_AttitudeControl::lean_angle_max_rad() const
{
    return harness_cut.lean_angle_max_rad;
}

void AC_AttitudeControl::input_quaternion(Quaternion &, Vector3f)
{
    unreachable("AC_AttitudeControl::input_quaternion");
}
void AC_AttitudeControl::input_euler_angle_roll_pitch_euler_rate_yaw_rad(float, float, float)
{
    unreachable("AC_AttitudeControl::input_euler_angle_roll_pitch_euler_rate_yaw_rad");
}
void AC_AttitudeControl::input_euler_angle_roll_pitch_yaw_rad(float, float, float, bool)
{
    unreachable("AC_AttitudeControl::input_euler_angle_roll_pitch_yaw_rad");
}
void AC_AttitudeControl::input_euler_rate_roll_pitch_yaw_rads(float, float, float)
{
    unreachable("AC_AttitudeControl::input_euler_rate_roll_pitch_yaw_rads");
}
void AC_AttitudeControl::input_rate_bf_roll_pitch_yaw_rads(float, float, float)
{
    unreachable("AC_AttitudeControl::input_rate_bf_roll_pitch_yaw_rads");
}
void AC_AttitudeControl::input_rate_bf_roll_pitch_yaw_2_rads(float, float, float)
{
    unreachable("AC_AttitudeControl::input_rate_bf_roll_pitch_yaw_2_rads");
}
void AC_AttitudeControl::input_rate_bf_roll_pitch_yaw_3_rads(float, float, float)
{
    unreachable("AC_AttitudeControl::input_rate_bf_roll_pitch_yaw_3_rads");
}
void AC_AttitudeControl::input_angle_step_bf_roll_pitch_yaw_rad(float, float, float)
{
    unreachable("AC_AttitudeControl::input_angle_step_bf_roll_pitch_yaw_rad");
}
void AC_AttitudeControl::input_rate_step_bf_roll_pitch_yaw_rads(float, float, float)
{
    unreachable("AC_AttitudeControl::input_rate_step_bf_roll_pitch_yaw_rads");
}
void AC_AttitudeControl::input_thrust_vector_rate_heading_rads(const Vector3f &, float, bool)
{
    unreachable("AC_AttitudeControl::input_thrust_vector_rate_heading_rads");
}
void AC_AttitudeControl::input_thrust_vector_heading_rad(const Vector3f &, float, float)
{
    unreachable("AC_AttitudeControl::input_thrust_vector_heading_rad");
}
void AC_AttitudeControl::relax_attitude_controllers()
{
    unreachable("AC_AttitudeControl::relax_attitude_controllers");
}

AC_PID &HarnessAttitude::get_rate_roll_pid() { unreachable("get_rate_roll_pid"); }
AC_PID &HarnessAttitude::get_rate_pitch_pid() { unreachable("get_rate_pitch_pid"); }
AC_PID &HarnessAttitude::get_rate_yaw_pid() { unreachable("get_rate_yaw_pid"); }
const AC_PID &HarnessAttitude::get_rate_roll_pid() const { unreachable("get_rate_roll_pid"); }
const AC_PID &HarnessAttitude::get_rate_pitch_pid() const { unreachable("get_rate_pitch_pid"); }
const AC_PID &HarnessAttitude::get_rate_yaw_pid() const { unreachable("get_rate_yaw_pid"); }
void HarnessAttitude::rate_controller_run() { unreachable("rate_controller_run"); }
void HarnessAttitude::update_althold_lean_angle_max(float) { unreachable("update_althold_lean_angle_max"); }

void AP_BoardConfig::config_error(const char *fmt, ...)
{
    unreachable("AP_BoardConfig::config_error");
}
