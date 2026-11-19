// stubs_posctl.cpp: the position controller, which is another stage (AC_PosControl), as AC_WPNav
// sees it from the guidance module.
//
// AC_PosControl.cpp is not compiled. The object AC_WPNav holds a reference to is zeroed storage
// (adapter.cpp); the members its inline accessors read are loaded from the input record before
// each step. Every `_pos_control.` call in AC_WPNav.cpp and AC_WPNav.h, and what it became:
//
//   call (AC_WPNav.cpp line)                        kind     became
//   get_dt_s() (735)                                inline   input dt (member _dt_s)
//   get_pos_estimate_NED_m() (575, 691, 699, 707)   inline   inputs est_pos_n/e/d (_pos_estimate_ned_m)
//   get_vel_estimate_NED_ms() (587)                 inline   inputs est_vel_n/e/d (_vel_estimate_ned_ms)
//   get_pos_estimate_U_m() (806)                    inline   terrain database branch, not reached
//   get_vel_desired_NED_ms() (399, 579)             inline   inputs pc_vel_desired_n/e/d
//   get_vel_offset_D_ms() (400, 580)                inline   input pc_vel_offset_d (_vel_offset_ned_ms.z)
//   get_pos_offset_NED_m() (572)                    inline   inputs pc_pos_offset_n/e/d
//   get_pos_error_NED_m() (586)                     inline   inputs pc_pos_error_n/e/d (the P controllers' _error)
//   NE_get_pos_p().kP() (589)                       inline   parameter psc_ne_pos_p (_p_pos_ne_m._kp)
//   get_shaping_jerk_NE_msss() (598)                inline   parameter psc_ne_jerk (_shaping_jerk_ne_msss)
//   NE_get_max_speed_ms() (232.., 420, 496, 664..)  inline   input pc_ne_max_speed, then this tick's setter
//   NE_get_max_accel_mss() (912, 1014)              inline   input pc_ne_max_accel, then this tick's setter
//   get_max_speed_up_ms(), get_max_speed_down_ms()  inline   inputs pc_max_speed_up/down, then this tick's setter
//   D_get_max_accel_mss() (302, 313, 912, 1014)     inline   input pc_d_max_accel, then this tick's setter
//   get_stopping_point_NE_m() (530, 549)            stand-in input pc_stopping_point_n/e
//   get_stopping_point_D_m() (551)                  stand-in input pc_stopping_point_d
//   terrain_scaler_D_m(0, margin) (566)             stand-in AC_PosControl.cpp:433-440 with the terrain
//                                                            offsets 0 (terrain out of scope), reading
//                                                            est_pos_d and input pc_pos_target_d
//   set_pos_terrain_target_D_m(0) (569)             inline   writes the zeroed storage; not a port (always 0)
//   init_pos_terrain_D_m (830, 834, 945, 949)       stand-in terrain branches, not reached: abort
//   D_init_controller_stopping_point() (223)        stand-in output tgt_d_init_stopping_point
//   NE_init_controller_stopping_point() (224)       stand-in output tgt_ne_init_stopping_point
//   NE_set_max_speed_accel_m (232, 289)             stand-in outputs tgt_ne_set_max_speed_accel, tgt_ne_max_speed/accel
//   NE_set_correction_speed_accel_m (233, 290)      stand-in outputs tgt_ne_set_correction_speed_accel, tgt_ne_correction_*
//   D_set_max_speed_accel_m (234, 302, 313)         stand-in outputs tgt_d_set_max_speed_accel, tgt_max_speed_down/up,
//                                                            tgt_d_max_accel
//   D_set_correction_speed_accel_m (235)            stand-in outputs tgt_d_set_correction_speed_accel, tgt_d_correction_*
//   set_pos_vel_accel_NED_m (636)                   stand-in outputs tgt_pos/vel/acc_n/e/d, tgt_valid
//   NE_update_controller() (741)                    stand-in output tgt_valid (always right after set_pos_vel_accel_NED_m)
//   get_roll_rad, get_pitch_rad, get_yaw_rad,       inline   AC_WPNav.h:318-356 pass-throughs, never called by the
//   get_thrust_vector, crosstrack_error_m                    module: position-stage signals the supervisor reads
//                                                            from the position stage directly
//
// What a stand-in stores: the speed and acceleration limits are read back by AC_WPNav within the
// same tick after it sets them (wp_and_spline_init_m sets them, then set_wp_destination_NED_m
// builds the leg from them), so the setters store what the real setters store into the members
// the getters read: NE_set_max_speed_accel_m stores fabsf of both arguments
// (AC_PosControl.cpp:460-461); D_set_max_speed_accel_m stores fabsf of each argument that is not
// zero (AC_PosControl.cpp:809-817). The jerk limits they also compute stay with the position
// stage. NE/D_init_controller_stopping_point zero the desired velocity's NE/D components
// (AC_PosControl.cpp:507-508, 873-874), which update_wpnav reads later in the same tick.
//
// Deviations from the monolithic vehicle, all from the one-tick delay of a signal:
//   - get_stopping_point_NE_m/D_m return the position stage's stopping point of the previous
//     tick; the real ones compute it at the call, from this tick's estimate and the limits in
//     force (after wp_and_spline_init_m's setters, the new ones).
//   - NE/D_init_controller_stopping_point also reset the position controller's offsets
//     (NE_init_offsets after a timeout) and its target; the module does not see the reset
//     offsets until the next tick.
#include "cut.h"

#include <stdio.h>
#include <stdlib.h>

#include <AC_AttitudeControl/AC_PosControl.h>

HarnessPosCalls harness_pos_calls;
uint32_t harness_current_seq;

// the call order of the hand-over, for a sequenced tick (cut.h)
static void note_handover()
{
    if (harness_pos_calls.handover_seq == 0) {
        harness_pos_calls.handover_seq = harness_current_seq;
    }
}
Vector3p harness_pc_stopping_point;

__attribute__((noreturn)) static void posctl_unreachable(const char *what)
{
    fprintf(stderr, "guidance: cut symbol reached: %s\n", what);
    abort();
}

void AC_PosControl::get_stopping_point_NE_m(Vector2p &stopping_point_ne_m) const
{
    stopping_point_ne_m = harness_pc_stopping_point.xy();
}

void AC_PosControl::get_stopping_point_D_m(postype_t &stopping_point_d_m) const
{
    stopping_point_d_m = harness_pc_stopping_point.z;
}

// AC_PosControl.cpp:433-440, with _pos_terrain_d_m = 0 (terrain out of scope; the adapter
// zeroes it) and _pos_target_ned_m.z loaded from pc_pos_target_d
float AC_PosControl::terrain_scaler_D_m(float pos_terrain_d_m, float terrain_margin_m) const
{
    if (is_zero(terrain_margin_m)) {
        return 1.0;
    }
    float pos_offset_error_d_m = _pos_estimate_ned_m.z - (_pos_target_ned_m.z + (pos_terrain_d_m - _pos_terrain_d_m));
    return constrain_float((1.0 - (fabsf(pos_offset_error_d_m) - 0.5 * terrain_margin_m) / (0.5 * terrain_margin_m)), 0.01, 1.0);
}

void AC_PosControl::init_pos_terrain_D_m(float pos_terrain_d_m)
{
    posctl_unreachable("AC_PosControl::init_pos_terrain_D_m (terrain)");
}

void AC_PosControl::NE_init_controller_stopping_point()
{
    note_handover();
    harness_pos_calls.ne_init_stopping_point = true;
    _vel_desired_ned_ms.xy().zero();
}

void AC_PosControl::D_init_controller_stopping_point()
{
    note_handover();
    harness_pos_calls.d_init_stopping_point = true;
    _vel_desired_ned_ms.z = 0.0f;
}

void AC_PosControl::NE_set_max_speed_accel_m(float speed_ne_ms, float accel_ne_mss)
{
    note_handover();
    harness_pos_calls.ne_set_max_speed_accel = true;
    _vel_max_ne_ms = fabsf(speed_ne_ms);
    _accel_max_ne_mss = fabsf(accel_ne_mss);
}

void AC_PosControl::NE_set_correction_speed_accel_m(float speed_ne_ms, float accel_ne_mss)
{
    note_handover();
    harness_pos_calls.ne_set_correction = true;
    harness_pos_calls.ne_correction_speed = speed_ne_ms;
    harness_pos_calls.ne_correction_accel = accel_ne_mss;
}

void AC_PosControl::D_set_max_speed_accel_m(float decent_speed_max_ms, float climb_speed_max_ms, float accel_max_d_mss)
{
    note_handover();
    harness_pos_calls.d_set_max_speed_accel = true;
    if (!is_zero(decent_speed_max_ms)) {
        _vel_max_down_ms = fabsf(decent_speed_max_ms);
    }
    if (!is_zero(climb_speed_max_ms)) {
        _vel_max_up_ms = fabsf(climb_speed_max_ms);
    }
    if (!is_zero(accel_max_d_mss)) {
        _accel_max_d_mss = fabsf(accel_max_d_mss);
    }
}

void AC_PosControl::D_set_correction_speed_accel_m(float decent_speed_max_ms, float climb_speed_max_ms, float accel_max_d_mss)
{
    note_handover();
    harness_pos_calls.d_set_correction = true;
    harness_pos_calls.d_correction_down = decent_speed_max_ms;
    harness_pos_calls.d_correction_up = climb_speed_max_ms;
    harness_pos_calls.d_correction_accel = accel_max_d_mss;
}

void AC_PosControl::set_pos_vel_accel_NED_m(const Vector3p& pos_ned_m, const Vector3f& vel_ned_ms, const Vector3f& accel_ned_mss)
{
    harness_pos_calls.update_seq = harness_current_seq;
    harness_pos_calls.set_pos_vel_accel = true;
    harness_pos_calls.pos = pos_ned_m;
    harness_pos_calls.vel = vel_ned_ms;
    harness_pos_calls.accel = accel_ned_mss;
}

void AC_PosControl::NE_update_controller()
{
    harness_pos_calls.ne_update = true;
}
