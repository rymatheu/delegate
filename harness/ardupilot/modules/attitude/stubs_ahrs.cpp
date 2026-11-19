// stubs_ahrs.cpp: the AHRS behind the AHRS view, and the inertial sensors.
//
//   symbol                                   why it is outside the stage, and what stands in
//   AP_AHRS (the object AP_AHRS_View wraps)  the estimator. Zeroed storage, never
//                                            constructed: the real AP_AHRS_View::update()
//                                            reads only its inline get_rotation_body_to_ned()
//                                            (state.dcm_matrix) and get_gyro()
//                                            (state.gyro_estimate, left 0: the attitude
//                                            controller does not read the view's gyro) and
//                                            calls the real AP_AHRS::calc_trig
//                                            (AP_AHRS_Backend.cpp), which reads no member.
//                                            The adapter sets state.dcm_matrix every step
//                                            from the input ports est_roll, est_pitch,
//                                            est_yaw by the real Matrix3f::from_euler (AP_AHRS
//                                            itself takes it from the EKF's quaternion).
//   AP::ahrs()                               the AHRS singleton: the same storage. Read only
//                                            by the motors' get_compensation_gain (mixer's).
//   AP_AHRS::get_air_density_ratio           the motors' compensation gain (the mixer's). Abort.
//   AP::ins()                                the inertial sensors; only AP_AHRS::get_gyro_latest,
//                                            reached through AC_AttitudeControl_Multi::
//                                            rate_controller_run (the rate stage's), and the
//                                            attitude controller reads the gyro from
//                                            _rate_gyro_rads (AC_ATTITUDE_CONTROL_AFTER_
//                                            RATE_CONTROL is 1 for Copter). Abort.
#include <AP_AHRS/AP_AHRS.h>
#include <AP_InertialSensor/AP_InertialSensor.h>

alignas(AP_AHRS) static unsigned char ahrs_storage[sizeof(AP_AHRS)];

AP_AHRS &harness_ahrs_storage()
{
    return *reinterpret_cast<AP_AHRS *>(ahrs_storage);
}

namespace AP {
AP_AHRS &ahrs()
{
    return harness_ahrs_storage();
}
AP_InertialSensor &ins()
{
    unreachable("AP::ins");
}
}

float AP_AHRS::get_air_density_ratio(void) const
{
    unreachable("AP_AHRS::get_air_density_ratio");
}

// the private state.dcm_matrix; access is not checked in an explicit instantiation's template
// arguments
static void set_ahrs_dcm(const Matrix3f &m);
template <typename T, T M>
struct AhrsState {
    friend void set_ahrs_dcm(const Matrix3f &m) { (harness_ahrs_storage().*M).dcm_matrix = m; }
};
template struct AhrsState<decltype(&AP_AHRS::state), &AP_AHRS::state>;

void harness_set_ahrs_dcm(const Matrix3f &m)
{
    set_ahrs_dcm(m);
}

static void harness_reset_ahrs()
{
    memset(ahrs_storage, 0, sizeof ahrs_storage);
}
