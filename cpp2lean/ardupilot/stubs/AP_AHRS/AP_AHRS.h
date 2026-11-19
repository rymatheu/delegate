// ORACLE STUB: replaces libraries/AP_AHRS/AP_AHRS.h.
// Why: the real AP_AHRS is the EKF front end (it pulls in AP_InertialSensor, AP_Compass, AP_NavEKF*,
// AP_GPS, MAVLink); here the estimator is the environment, so every getter the compiled control code
// calls returns the scripted sample of the tick, as the harness defines
// the environment:
//   get_relative_position_NED_origin   -> sample position (double), returns true
//   get_relative_position_D_origin_float -> (float) sample z, returns true
//   get_velocity_NED                   -> sample velocity, returns true
//   get_vert_pos_rate_D                -> sample vz, returns true
//   get_accel_ef                       -> sample earth-frame specific force
//   get_control_gain_scaler_XY/Z       -> 1 (no optical flow)
//   get_air_density_ratio              -> run.air_density_ratio (1 for the recorded flight)
//   get_position_NE/D_reset_count, get_yaw_reset_count -> 0 (no EKF resets)
// Signatures are those of the real header (AP_AHRS.h:156, :212, :253, :263, :285, :298, :324-325,
// :361-371), and get_origin (no origin, for AC_WPNav's Location-based entry points). Nothing else of
// AP_AHRS is declared; a compile error would show any other use.
#pragma once

#include <AP_Math/AP_Math.h>
#include <SITL/SITL.h>   // the real AP_AHRS.h reaches SITL.h through AP_AHRS_SIM.h

class AP_AHRS {
public:
    // The scripted sample, written by the harness (ardupilot/vehicle/copter_ref.cpp).
    struct Sample {
        Vector3p pos_ned;       // m, NED from the EKF origin (postype_t)
        Vector3f vel_ned;       // m/s
        Vector3f accel_ef;      // m/s^2, specific force, NED
        Quaternion quat;        // body to NED
        Vector3f gyro;          // rad/s, body
        float air_density_ratio = 1.0f;
    } sample;

    float get_air_density_ratio(void) const { return sample.air_density_ratio; }
    const Vector3f &get_accel_ef() const { return sample.accel_ef; }
    bool get_velocity_NED(Vector3f &vec) const { vec = sample.vel_ned; return true; }
    bool get_relative_position_NED_origin(Vector3p &vec) const { vec = sample.pos_ned; return true; }
    bool get_relative_position_D_origin_float(float &posD) const { posD = (float)sample.pos_ned.z; return true; }
    bool get_vert_pos_rate_D(float &velocity) const { velocity = sample.vel_ned.z; return true; }
    float get_control_gain_scaler_XY() const { return 1.0f; }
    float get_control_gain_scaler_Z() const { return 1.0f; }
    uint16_t get_yaw_reset_count(void) const { return 0; }
    uint16_t get_position_NE_reset_count(void) const { return 0; }
    uint16_t get_position_D_reset_count(void) const { return 0; }
    // AP_AHRS.h:221: the EKF origin. Declared for AC_WPNav's Location-based entry points
    // (AC_WPNav.cpp:361), which the harnesses never call: no origin.
    bool get_origin(class Location &ret) const { return false; }
};

namespace AP {
    AP_AHRS &ahrs();
};
