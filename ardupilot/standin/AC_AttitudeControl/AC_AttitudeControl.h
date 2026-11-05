// cpp2lean difftest STAND-IN for libraries/AC_AttitudeControl/AC_AttitudeControl.h, used only when
// the difftest compiles AC_PosControl or AC_WPNav (ardupilot/AC_PosControl.json, AC_WPNav.json, through clang's -ivfsoverlay:
// AC_PosControl.h includes "AC_AttitudeControl.h" next to itself, so an include path cannot
// replace it). The attitude controller is outside the translation of AC_PosControl (--boundary
// AC_AttitudeControl): what AC_PosControl reads from it are the translation's inputs, its one call
// into it (set_throttle_out) an output. This stand-in has the declarations AC_PosControl uses, with
// the signatures of the real header (cited by line), and returns the driver's values exactly; the
// real getters compute them from parameters (radians(_ang_vel_roll_max_degs), ...), which cannot
// produce every value. set_throttle_out records the call in the output log (cpp2lean_events.h), as
// the translation's `Output.set_throttle_out` event. The includes are the real header's.
#pragma once

#include <AP_Common/AP_Common.h>
#include <AP_Param/AP_Param.h>
#include <AP_Math/AP_Math.h>
#include <AP_AHRS/AP_AHRS_View.h>
#include <AP_Motors/AP_Motors.h>
#include <AC_PID/AC_PID.h>
#include <AC_PID/AC_P.h>
#include <AP_BoardConfig/AP_BoardConfig.h>
#include "cpp2lean_events.h"   // ardupilot/ (the -I of the difftest flags)

class AC_AttitudeControl {
public:
    // the values the getters return (the driver's inputs)
    float v_accel_roll_max_radss, v_accel_pitch_max_radss, v_ang_vel_roll_max_rads, v_ang_vel_pitch_max_rads;
    bool v_bf_feedforward;
    Vector3f v_att_target_euler_rad;
    float v_throttle_in, v_althold_lean_angle_max_rad, v_lean_angle_max_rad;
    float v_input_tc;                   // AC_WPNav's read (ardupilot/AC_WPNav.json)

    float get_accel_roll_max_radss() const { return v_accel_roll_max_radss; }          // AC_AttitudeControl.h:91
    float get_accel_pitch_max_radss() const { return v_accel_pitch_max_radss; }        // :100
    float get_ang_vel_roll_max_rads() const { return v_ang_vel_roll_max_rads; }        // :118
    float get_ang_vel_pitch_max_rads() const { return v_ang_vel_pitch_max_rads; }      // :124
    float get_input_tc() const { return v_input_tc; }                                   // :139
    const Vector3f & get_att_target_euler_rad() const { return v_att_target_euler_rad; }   // :331
    bool get_bf_feedforward() { return v_bf_feedforward; }                              // :396
    virtual void set_throttle_out(float throttle_in, bool apply_angle_boost, float filt_cutoff)   // :405
    {
        cpp2lean_ev("set_throttle_out"); cpp2lean_ev_f(throttle_in); cpp2lean_ev_b(apply_angle_boost); cpp2lean_ev_f(filt_cutoff);
    }
    float get_throttle_in() const { return v_throttle_in; }                             // :408
    virtual float get_althold_lean_angle_max_rad() const { return v_althold_lean_angle_max_rad; }   // :415
    float lean_angle_max_rad() const { return v_lean_angle_max_rad; }                   // :425
    virtual ~AC_AttitudeControl() {}
};
