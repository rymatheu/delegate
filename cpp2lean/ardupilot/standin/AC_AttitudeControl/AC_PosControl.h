// cpp2lean difftest STAND-IN for libraries/AC_AttitudeControl/AC_PosControl.h, used only when the
// difftest compiles AC_WPNav (ardupilot/AC_WPNav.json, through clang's -ivfsoverlay). The position
// controller is outside the translation of AC_WPNav (--boundary AC_PosControl, --boundary-live): the
// navigator's calls into it are the translation's output events, its reads are live inputs, functions
// of the calls made so far in the member function. This stand-in has the declarations AC_WPNav uses,
// with the signatures of the real header (cited by line), records every call in the output log
// (cpp2lean_events.h) and returns, for each read, the driver's value of the line plus 0.125 times
// the number of calls recorded so far in the member function (plus 0.5 and 0.25 times the arguments of
// terrain_scaler_D_m), exactly as the Lean driver's live Inputs functions compute it. The includes are
// the real header's, except AC_PI_2D.h and the scripting configuration, which AC_WPNav does not use.
#pragma once

#include <AP_Common/AP_Common.h>
#include <AP_Param/AP_Param.h>
#include <AP_Math/AP_Math.h>
#include <AC_PID/AC_P.h>
#include <AC_PID/AC_PID.h>
#include <AC_PID/AC_P_1D.h>
#include <AC_PID/AC_P_2D.h>
#include <AC_PID/AC_PID_Basic.h>
#include <AC_PID/AC_PID_2D.h>
#include "AC_AttitudeControl.h"
#include "cpp2lean_events.h"   // ardupilot/ (the -I of the difftest flags)

// what `NE_get_pos_p()` returns: only kP() is read (AC_WPNav.cpp:589)
class AC_PosControl_P2D_standin {
public:
    float v_kP;
    float kP() const { return cpp2lean_live_f(v_kP); }          // AC_P_2D.h:39, an AP_Float converted to float
};

class AC_PosControl {
public:
    // the values the reads return before the live shift (the driver's inputs)
    float v_get_dt_s, v_get_shaping_jerk_NE_msss, v_terrain_scaler_D_m, v_NE_get_max_speed_ms, v_NE_get_max_accel_mss;
    float v_D_get_max_accel_mss, v_get_max_speed_up_ms, v_get_max_speed_down_ms, v_get_vel_offset_D_ms;
    float v_get_roll_rad, v_get_pitch_rad, v_get_yaw_rad, v_crosstrack_error_m;
    Vector3p v_get_pos_estimate_NED_m, v_get_pos_offset_NED_m;
    Vector2p v_get_stopping_point_NE_m;
    double v_get_stopping_point_D_m;
    Vector3f v_get_pos_error_NED_m, v_get_vel_estimate_NED_ms, v_get_vel_desired_NED_ms, v_get_thrust_vector;
    AC_PosControl_P2D_standin p2d;
    // the values the reference-returning reads return (one per read, as the real members are distinct)
    mutable Vector3p r_pos_estimate, r_pos_offset;
    mutable Vector3f r_vel_estimate, r_vel_desired;

    // a reference a read returned names a member that every later call into the controller may
    // change (AC_WPNav.cpp:572-575 binds `get_pos_offset_NED_m()` to a reference): each recorded call
    // recomputes the values the references name
    void refresh() const
    {
        r_pos_estimate = live3p(v_get_pos_estimate_NED_m);
        r_pos_offset = live3p(v_get_pos_offset_NED_m);
        r_vel_estimate = live3f(v_get_vel_estimate_NED_ms);
        r_vel_desired = live3f(v_get_vel_desired_NED_ms);
    }

    static Vector3f live3f(const Vector3f &v) { return Vector3f(cpp2lean_live_f(v.x), cpp2lean_live_f(v.y), cpp2lean_live_f(v.z)); }
    static Vector3p live3p(const Vector3p &v) { return Vector3p(cpp2lean_live_d(v.x), cpp2lean_live_d(v.y), cpp2lean_live_d(v.z)); }

    float get_dt_s() const { return cpp2lean_live_f(v_get_dt_s); }                                  // AC_PosControl.h:53
    float get_shaping_jerk_NE_msss() const { return cpp2lean_live_f(v_get_shaping_jerk_NE_msss); }  // :62
    float terrain_scaler_D_m(float pos_terrain_d_m, float terrain_margin_m) const                  // :79
    {
        return cpp2lean_live_f(v_terrain_scaler_D_m) + 0.5f * pos_terrain_d_m + 0.25f * terrain_margin_m;
    }
    void NE_set_max_speed_accel_m(float speed_ms, float accel_mss)                                  // :94
    {
        cpp2lean_ev("NE_set_max_speed_accel_m"); cpp2lean_ev_f(speed_ms); cpp2lean_ev_f(accel_mss); refresh();
    }
    void NE_set_correction_speed_accel_m(float speed_ms, float accel_mss)                           // :105
    {
        cpp2lean_ev("NE_set_correction_speed_accel_m"); cpp2lean_ev_f(speed_ms); cpp2lean_ev_f(accel_mss); refresh();
    }
    float NE_get_max_speed_ms() const { return cpp2lean_live_f(v_NE_get_max_speed_ms); }            // :112
    float NE_get_max_accel_mss() const { return cpp2lean_live_f(v_NE_get_max_accel_mss); }          // :115
    void NE_init_controller_stopping_point() { cpp2lean_ev("NE_init_controller_stopping_point"); refresh(); }  // :127
    void NE_update_controller() { cpp2lean_ev("NE_update_controller"); refresh(); }                            // :185
    void D_set_max_speed_accel_m(float decent_speed_max_ms, float climb_speed_max_ms, float accel_max_d_mss)        // :200
    {
        cpp2lean_ev("D_set_max_speed_accel_m"); cpp2lean_ev_f(decent_speed_max_ms); cpp2lean_ev_f(climb_speed_max_ms); cpp2lean_ev_f(accel_max_d_mss); refresh();
    }
    void D_set_correction_speed_accel_m(float decent_speed_max_ms, float climb_speed_max_ms, float accel_max_d_mss) // :211
    {
        cpp2lean_ev("D_set_correction_speed_accel_m"); cpp2lean_ev_f(decent_speed_max_ms); cpp2lean_ev_f(climb_speed_max_ms); cpp2lean_ev_f(accel_max_d_mss); refresh();
    }
    float D_get_max_accel_mss() const { return cpp2lean_live_f(v_D_get_max_accel_mss); }            // :214
    float get_max_speed_up_ms() const { return cpp2lean_live_f(v_get_max_speed_up_ms); }            // :227
    float get_max_speed_down_ms() const { return cpp2lean_live_f(v_get_max_speed_down_ms); }        // :230
    void D_init_controller_stopping_point() { cpp2lean_ev("D_init_controller_stopping_point"); refresh(); }    // :239
    void set_pos_vel_accel_NED_m(const Vector3p& pos_ned_m, const Vector3f& vel_ned_ms, const Vector3f& accel_ned_mss)   // :303
    {
        cpp2lean_ev("set_pos_vel_accel_NED_m");
        cpp2lean_ev_d(pos_ned_m.x); cpp2lean_ev_d(pos_ned_m.y); cpp2lean_ev_d(pos_ned_m.z);
        cpp2lean_ev_f(vel_ned_ms.x); cpp2lean_ev_f(vel_ned_ms.y); cpp2lean_ev_f(vel_ned_ms.z);
        cpp2lean_ev_f(accel_ned_mss.x); cpp2lean_ev_f(accel_ned_mss.y); cpp2lean_ev_f(accel_ned_mss.z);
        refresh();
    }
    const Vector3p& get_pos_estimate_NED_m() const { r_pos_estimate = live3p(v_get_pos_estimate_NED_m); return r_pos_estimate; }   // :313
    void get_stopping_point_NE_m(Vector2p &stopping_point_ne_m) const                                         // :352
    {
        stopping_point_ne_m = Vector2p(cpp2lean_live_d(v_get_stopping_point_NE_m.x), cpp2lean_live_d(v_get_stopping_point_NE_m.y));
    }
    void get_stopping_point_D_m(postype_t &stopping_point_d_m) const { stopping_point_d_m = cpp2lean_live_d(v_get_stopping_point_D_m); }   // :355
    const Vector3f get_pos_error_NED_m() const { return live3f(v_get_pos_error_NED_m); }                     // :361
    const Vector3f& get_vel_estimate_NED_ms() const { r_vel_estimate = live3f(v_get_vel_estimate_NED_ms); return r_vel_estimate; } // :377
    const Vector3f& get_vel_desired_NED_ms() const { r_vel_desired = live3f(v_get_vel_desired_NED_ms); return r_vel_desired; }   // :397
    void set_pos_terrain_target_D_m(float pos_terrain_target_d_m)                                          // :438
    {
        cpp2lean_ev("set_pos_terrain_target_D_m"); cpp2lean_ev_f(pos_terrain_target_d_m); refresh();
    }
    void init_pos_terrain_D_m(float pos_terrain_d_m) { cpp2lean_ev("init_pos_terrain_D_m"); cpp2lean_ev_f(pos_terrain_d_m); refresh(); }   // :447
    const Vector3p& get_pos_offset_NED_m() const { r_pos_offset = live3p(v_get_pos_offset_NED_m); return r_pos_offset; }     // :485
    float get_vel_offset_D_ms() const { return cpp2lean_live_f(v_get_vel_offset_D_ms); }                    // :500
    float get_roll_rad() const { return cpp2lean_live_f(v_get_roll_rad); }                                  // :508
    float get_pitch_rad() const { return cpp2lean_live_f(v_get_pitch_rad); }                                // :511
    float get_yaw_rad() const { return cpp2lean_live_f(v_get_yaw_rad); }                                    // :514
    Vector3f get_thrust_vector() const { return live3f(v_get_thrust_vector); }                              // :528
    AC_PosControl_P2D_standin& NE_get_pos_p() { return p2d; }                                               // :552
    float crosstrack_error_m() const { return cpp2lean_live_f(v_crosstrack_error_m); }                      // :599
};
