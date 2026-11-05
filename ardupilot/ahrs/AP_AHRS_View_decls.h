// cpp2lean: the declarations that AP_AHRS_View::update (AP_AHRS_View.cpp:61-83) and AP_AHRS::calc_trig
// (AP_AHRS_Backend.cpp:93-135) need, for ardupilot/unity_ahrs_view.cpp. The real headers
// (AP_AHRS/AP_AHRS.h, AP_AHRS_View.h) reach the EKF, the INS, GPS and MAVLink, which the stub headers
// do not provide. Each declaration is the real one, cited by line (802db19de1); the classes hold only
// what the two definitions use. AP_AHRS is the boundary (its estimate is the input); AP_AHRS_View is
// translated. The constructor below only binds the AHRS (the real one, AP_AHRS_View.cpp:24-50, also
// sets rot_view, rot_view_T and y_angle for the given rotation and pitch trim, and calls update();
// for ROTATION_NONE and no trim, y_angle and _pitch_trim_deg are 0 and rot_view is not read).
#pragma once

#include <AP_Math/AP_Math.h>

class AP_AHRS {
public:
    // AP_AHRS.h:665: the estimate (body-to-NED rotation)
    const Matrix3f &get_rotation_body_to_ned(void) const;
    // AP_AHRS.h:92: the estimate (corrected gyro)
    const Vector3f &get_gyro(void) const;
    // AP_AHRS.h:823-825
    void calc_trig(const Matrix3f &rot,
                   float &cr, float &cp, float &cy,
                   float &sr, float &sp, float &sy) const;
};

class AP_AHRS_View
{
public:
    AP_AHRS_View(AP_AHRS &_ahrs) : ahrs(_ahrs) {}

    // AP_AHRS_View.h:36
    void update();

    // AP_AHRS_View.h:183-188
    float roll;
    float pitch;
    float yaw;
    int32_t roll_sensor;
    int32_t pitch_sensor;
    int32_t yaw_sensor;

private:
    // AP_AHRS_View.h:203-224 (without `const enum Rotation rotation`, which update() does not read)
    AP_AHRS &ahrs;
    Matrix3f rot_view;
    Matrix3f rot_view_T;
    Matrix3f rot_body_to_ned;
    Vector3f gyro;
    struct {
        float cos_roll;
        float cos_pitch;
        float cos_yaw;
        float sin_roll;
        float sin_pitch;
        float sin_yaw;
    } trig;
    float y_angle;
    float _pitch_trim_deg;
};
