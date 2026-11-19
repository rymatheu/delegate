// stubs_attitude.cpp: the AC_AttitudeControl(_Multi) shadow (attitude stage).
//
// harness_attitude_fill writes, from the attitude stage's outputs of the previous tick, every
// field the inline getters the vehicle code calls read (measure/proxy_surface.tsv):
//   _attitude_target               ac_att_target_q1..4         get_attitude_target_quat
//   _euler_angle_target_rad        ac_att_target_roll/pitch/yaw get_att_target_euler_rad
//   _ang_vel_target_rads           ac_ang_vel_target_*          get_attitude_target_ang_vel
//   _euler_rate_target_rads        ac_rate_ef_target_*          get_rate_ef_target_rads
//   _thrust_error_angle_rad        ac_thrust_error_angle        get_att_error_angle_deg
//   _althold_lean_angle_max_rad    ac_althold_lean_angle_max    get_althold_lean_angle_max_rad
//                                                               (real body, gen/ COPY_REAL)
//   _throttle_in                   ac_throttle_in               get_throttle_in
//   _throttle_rpy_mix              ac_throttle_mix              get_throttle_mix,
//                                                               is_throttle_mix_min
// Parameters (ATC_*) are the real var_info's, same values as the attitude stage's record. Not
// filled: the rate PIDs inside (get_rate_*_pid: GCS PID tuning messages, crash_check's yaw I
// term: these read the shadow PIDs' zero state).
//
// Inline setters the vehicle code calls (they write supervisor-owned fields and log nothing):
// harness_attitude_before sets a sentinel (NaN) in each written field before the tick and
// harness_attitude_after turns a changed field into the command it stands for, placed after
// every logged call of the tick (its true place in the order is not observable):
//   _rate_y_tc                     set_yaw_rate_tc(input_tc)
//   _rate_rp_tc                    set_roll_pitch_rate_tc(input_tc)
//   _throttle_rpy_mix_desired      set_throttle_mix_min() (= ATC_THR_MIX_MIN) or
//                                  set_throttle_mix_man() (= ATC_THR_MIX_MAN)
//
// Stand-ins with their own record: input_thrust_vector_heading (the HeadingCommand
// component-wise) and input_thrust_vector_heading_rad(thrust, angle, rate), recorded as
// input_thrust_vector_heading(angle, rate, Angle_And_Rate), which the real dispatch
// (AC_AttitudeControl.cpp, input_thrust_vector_heading) turns into the same call.
#include <AC_AttitudeControl/AC_AttitudeControl_Multi.h>
#include "supervisor_shadow.h"
#include "module_records.h"

HARNESS_ADDR(AC_AttitudeControl, _attitude_target)
HARNESS_ADDR(AC_AttitudeControl, _euler_angle_target_rad)
HARNESS_ADDR(AC_AttitudeControl, _ang_vel_target_rads)
HARNESS_ADDR(AC_AttitudeControl, _euler_rate_target_rads)
HARNESS_ADDR(AC_AttitudeControl, _thrust_error_angle_rad)
HARNESS_ADDR(AC_AttitudeControl, _althold_lean_angle_max_rad)
HARNESS_ADDR(AC_AttitudeControl, _throttle_in)
HARNESS_ADDR(AC_AttitudeControl, _throttle_rpy_mix)
HARNESS_ADDR(AC_AttitudeControl, _throttle_rpy_mix_desired)
HARNESS_ADDR(AC_AttitudeControl, _rate_y_tc)
HARNESS_ADDR(AC_AttitudeControl, _rate_rp_tc)
HARNESS_ADDR(AC_AttitudeControl_Multi, _thr_mix_min)
HARNESS_ADDR(AC_AttitudeControl_Multi, _thr_mix_man)

#define AC(T, m) HARNESS_REF(T, *ac, AC_AttitudeControl, m)

static AC_AttitudeControl *ac;

void harness_attitude_fill(const Input &in)
{
    ac = AC_AttitudeControl::get_singleton();
    if (ac == nullptr) {
        return;
    }
    AC(Quaternion, _attitude_target) = Quaternion(in.ac_att_target_q1, in.ac_att_target_q2,
                                                  in.ac_att_target_q3, in.ac_att_target_q4);
    AC(Vector3f, _euler_angle_target_rad) =
        Vector3f(in.ac_att_target_roll, in.ac_att_target_pitch, in.ac_att_target_yaw);
    AC(Vector3f, _ang_vel_target_rads) =
        Vector3f(in.ac_ang_vel_target_x, in.ac_ang_vel_target_y, in.ac_ang_vel_target_z);
    AC(Vector3f, _euler_rate_target_rads) =
        Vector3f(in.ac_rate_ef_target_x, in.ac_rate_ef_target_y, in.ac_rate_ef_target_z);
    AC(float, _thrust_error_angle_rad) = in.ac_thrust_error_angle;
    AC(float, _althold_lean_angle_max_rad) = in.ac_althold_lean_angle_max;
    AC(float, _throttle_in) = in.ac_throttle_in;
    AC(float, _throttle_rpy_mix) = in.ac_throttle_mix;
}

void harness_attitude_before()
{
    if (ac == nullptr) {
        return;
    }
    AC(float, _rate_y_tc) = NAN;
    AC(float, _rate_rp_tc) = NAN;
    AC(float, _throttle_rpy_mix_desired) = NAN;
}

void harness_attitude_after()
{
    if (ac == nullptr) {
        return;
    }
    if (!isnan(AC(float, _rate_y_tc))) {
        sup_cmd_begin_named("AC_AttitudeControl::set_yaw_rate_tc", "attitude");
        sup_arg(AC(float, _rate_y_tc));
        sup_cmd_end();
    }
    if (!isnan(AC(float, _rate_rp_tc))) {
        sup_cmd_begin_named("AC_AttitudeControl::set_roll_pitch_rate_tc", "attitude");
        sup_arg(AC(float, _rate_rp_tc));
        sup_cmd_end();
    }
    const float mix = AC(float, _throttle_rpy_mix_desired);
    if (!isnan(mix)) {
        AC_AttitudeControl_Multi &m = static_cast<AC_AttitudeControl_Multi &>(*ac);
        if (is_equal(mix, HARNESS_REF(AP_Float, m, AC_AttitudeControl_Multi, _thr_mix_min).get())) {
            sup_cmd_begin_named("AC_AttitudeControl_Multi::set_throttle_mix_min", "attitude");
            sup_cmd_end();
        } else if (is_equal(mix,
                            HARNESS_REF(AP_Float, m, AC_AttitudeControl_Multi, _thr_mix_man).get())) {
            sup_cmd_begin_named("AC_AttitudeControl_Multi::set_throttle_mix_man", "attitude");
            sup_cmd_end();
        }
        // otherwise set_throttle_mix_max / set_throttle_mix_value wrote it; max is logged by its
        // own stand-in
    }
}

void AC_AttitudeControl::input_thrust_vector_heading(const Vector3f &thrust_vector,
                                                     HeadingCommand heading)
{
    sup_cmd_begin_named("AC_AttitudeControl::input_thrust_vector_heading", "attitude");
    sup_arg(thrust_vector);
    sup_arg(heading.yaw_angle_rad);
    sup_arg(heading.yaw_rate_rads);
    sup_arg(uint32_t(heading.heading_mode));
    sup_cmd_end();
}

void AC_AttitudeControl::input_thrust_vector_heading_rad(const Vector3f &thrust_vector,
                                                         float heading_angle_rad,
                                                         float heading_rate_rads)
{
    sup_cmd_begin_named("AC_AttitudeControl::input_thrust_vector_heading", "attitude");
    sup_arg(thrust_vector);
    sup_arg(heading_angle_rad);
    sup_arg(heading_rate_rads);
    sup_arg(uint32_t(HeadingMode::Angle_And_Rate));
    sup_cmd_end();
}
