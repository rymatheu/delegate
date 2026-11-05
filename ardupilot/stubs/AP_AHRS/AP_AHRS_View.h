// ORACLE STUB: replaces libraries/AP_AHRS/AP_AHRS_View.h (and AP_AHRS_View.cpp).
// Why: the real view copies the EKF's rotation matrix and gyro from AP_AHRS (stubbed here). The
// members and getters the control code uses keep the real names and signatures (AP_AHRS_View.h:42-157,
// :183-185); their values follow the harness's environment (the scripted sample of the tick):
//   get_quat_body_to_ned(q)  -> the sample quaternion itself (the real view returns
//                               from_rotation_matrix(rot_body_to_ned); the port defines the input as
//                               the value of this getter, so the oracle does the same)
//   rot_body_to_ned          -> sample quaternion .rotation_matrix() (AP_Math, compiled unmodified)
//   roll, pitch, yaw         -> rot_body_to_ned.to_euler() (as AP_AHRS_View::update, .cpp:65)
//   cos_/sin_ roll/pitch/yaw -> AP_AHRS::calc_trig (AP_AHRS_Backend.cpp:93-135), copied below as
//                               oracle_calc_trig, body unchanged
//   get_gyro_latest()        -> the sample gyro (ROTATION_NONE: the real view multiplies by the
//                               identity rot_view (AP_AHRS_View.cpp:86-88), which only turns -0 into +0;
//                               the port omits it too)
//   get_gyro()               -> the gyro at the last update()
//   get_accel_ef()           -> AP_AHRS::get_accel_ef()
//   reset counts             -> 0
// update() is called by the harness where Copter::read_AHRS runs (after motors output).
#pragma once

#include "AP_AHRS.h"

class AC_AttitudeControl;
class AC_PosControl;

class AP_AHRS_View
{
public:
    AP_AHRS_View(AP_AHRS &_ahrs, enum Rotation _rotation, float pitch_trim_deg=0) :
        ahrs(_ahrs), rotation(_rotation) {}

    virtual ~AP_AHRS_View() {}

    // AP_AHRS_View::update (AP_AHRS_View.cpp:56-76) for ROTATION_NONE, no pitch trim
    void update() {
        ahrs.sample.quat.rotation_matrix(rot_body_to_ned);
        gyro = ahrs.sample.gyro;
        rot_body_to_ned.to_euler(&roll, &pitch, &yaw);
        oracle_calc_trig(rot_body_to_ned, trig.cos_roll, trig.cos_pitch, trig.cos_yaw,
                         trig.sin_roll, trig.sin_pitch, trig.sin_yaw);
        quat = ahrs.sample.quat;
    }

    const Vector3f &get_gyro(void) const { return gyro; }
    Vector3f get_gyro_latest(void) const { return ahrs.sample.gyro; }
    const Matrix3f &get_rotation_body_to_ned(void) const { return rot_body_to_ned; }
    void get_quat_body_to_ned(Quaternion &q) const { q = quat; }

    float get_roll_rad() const { return roll; }
    float get_pitch_rad() const { return pitch; }
    float get_yaw_rad() const { return yaw; }

    float cos_roll() const { return trig.cos_roll; }
    float cos_pitch() const { return trig.cos_pitch; }
    float cos_yaw() const { return trig.cos_yaw; }
    float sin_roll() const { return trig.sin_roll; }
    float sin_pitch() const { return trig.sin_pitch; }
    float sin_yaw() const { return trig.sin_yaw; }

    const Vector3f &get_accel_ef(void) const { return ahrs.get_accel_ef(); }
    uint16_t get_position_NE_reset_count(void) { return ahrs.get_position_NE_reset_count(); }
    uint16_t get_position_D_reset_count(void) { return ahrs.get_position_D_reset_count(); }

    enum Rotation get_rotation(void) const { return rotation; }

    float roll;
    float pitch;
    float yaw;

private:
    // AP_AHRS::calc_trig, AP_AHRS_Backend.cpp:93-135, copied without change (only the name and
    // `static` differ: the real one is a const member of AP_AHRS).
    static void oracle_calc_trig(const Matrix3f &rot,
                                 float &cr, float &cp, float &cy,
                                 float &sr, float &sp, float &sy)
    {
        Vector2f yaw_vector(rot.a.x, rot.b.x);

        if (fabsf(yaw_vector.x) > 0 ||
            fabsf(yaw_vector.y) > 0) {
            yaw_vector.normalize();
        }
        sy = constrain_float(yaw_vector.y, -1.0f, 1.0f);
        cy = constrain_float(yaw_vector.x, -1.0f, 1.0f);

        // sanity checks
        if (yaw_vector.is_inf() || yaw_vector.is_nan()) {
            sy = 0.0f;
            cy = 1.0f;
        }

        const float cx2 = rot.c.x * rot.c.x;
        if (cx2 >= 1.0f) {
            cp = 0;
            cr = 1.0f;
        } else {
            cp = safe_sqrt(1 - cx2);
            cr = rot.c.z / cp;
        }
        cp = constrain_float(cp, 0.0f, 1.0f);
        cr = constrain_float(cr, -1.0f, 1.0f); // this relies on constrain_float() of infinity doing the right thing

        sp = -rot.c.x;

        if (!is_zero(cp)) {
            sr = rot.c.y / cp;
        }

        if (is_zero(cp) || isinf(cr) || isnan(cr) || isinf(sr) || isnan(sr)) {
            float r, p, y;
            rot.to_euler(&r, &p, &y);
            cr = cosf(r);
            sr = sinf(r);
        }
    }

    AP_AHRS &ahrs;
    enum Rotation rotation;
    Matrix3f rot_body_to_ned;
    Quaternion quat;
    Vector3f gyro;
    struct {
        float cos_roll = 1;
        float cos_pitch = 1;
        float cos_yaw = 1;
        float sin_roll = 0;
        float sin_pitch = 0;
        float sin_yaw = 0;
    } trig;
};
