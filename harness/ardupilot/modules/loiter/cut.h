// cut.h: what adapter.cpp and the stubs share about the cut of the loiter module.
//
// AC_Loiter holds references to the position controller (AC_PosControl, the position stage) and
// the attitude controller (AC_AttitudeControl, the attitude stage) and reads the AHRS view (the
// estimator). Here:
//   * the position controller is an object in zeroed storage whose members AC_Loiter's inline
//     accessors read are loaded from the input record (the position stage's outputs of the
//     previous tick); its out-of-line methods AC_Loiter calls are the stand-ins of
//     stubs_posctl.cpp, which record the calls handed to the position stage (outputs lt_...);
//   * the attitude controller is an object in zeroed storage whose parameter members are loaded
//     from the parameter record; the functions AC_Loiter calls on it are the real ones
//     (AC_AttitudeControl.cpp is compiled);
//   * the AHRS view is zeroed storage with its member yaw loaded from est_yaw.
// No constructor of the three runs, and AC_Loiter calls no virtual method of them.
#pragma once

#include <stdint.h>

#include <AP_Math/AP_Math.h>

// Reaching a protected or private member: access is not checked on the template arguments of an
// explicit instantiation ([temp.explicit]), so Rob<Tag, &C::m> may name C::m and hands its
// pointer-to-member out through a friend found by argument-dependent lookup on Tag (as in the
// guidance module).
template <typename Tag, typename Tag::type M>
struct Rob {
    friend typename Tag::type member_ptr(Tag) { return M; }
};
#define HARNESS_MEMBER(TAG, CLASS, TYPE, MEMBER)                                                    \
    struct TAG {                                                                                   \
        typedef TYPE CLASS::*type;                                                                 \
        friend type member_ptr(TAG);                                                               \
    };                                                                                             \
    template struct Rob<TAG, &CLASS::MEMBER>

// The calls AC_Loiter hands to the position controller during one step, recorded by the stand-ins
// (stubs_posctl.cpp) and by the adapter (set_pos_desired_NE_m, an inline setter), and turned into
// the lt_ outputs. Cleared before each step. A method called more than once in the step is
// reported once: its first call's `_seq`, its last call's arguments.
struct HarnessLoiterCalls {
    // methods the guidance stage also hands over (outputs lt_tgt_..., named after its tgt_...)
    bool ne_init_stopping_point;        // NE_init_controller_stopping_point()
    bool ne_set_correction;             // NE_set_correction_speed_accel_m(speed, accel)
    float ne_correction_speed, ne_correction_accel;
    uint32_t handover_seq;              // `_seq` of the command during the first of these two
    // methods the guidance stage does not use (outputs lt_cmd_position_<method>...)
    bool ne_set_pos_error_max;          // NE_set_pos_error_max_m(error_max), inline: AC_P_2D::set_error_max
    float error_max;
    uint32_t error_max_seq;
    bool set_pos_desired_ne;            // set_pos_desired_NE_m(pos), inline (adapter.cpp)
    Vector2p pos_desired;
    uint32_t pos_desired_seq;
    bool ne_relax;                      // NE_relax_velocity_controller()
    uint32_t relax_seq;
    bool ne_soften;                     // NE_soften_for_landing()
    uint32_t soften_seq;
    // the targets of update(): set_pos_vel_accel_NE_m, then NE_update_controller (lt_tgt_valid ...)
    bool set_pos_vel_accel;
    Vector2p pos;
    Vector2f vel, accel;
    uint32_t update_seq;
    bool ne_update;                     // NE_update_controller()
};
extern HarnessLoiterCalls harness_loiter_calls;
// the `_seq` of the command the adapter is executing (0: not sequenced)
extern uint32_t harness_current_seq;

// The values the stand-ins return that are not members of AC_PosControl (stubs_posctl.cpp):
// the position stage's outputs of the previous tick.
extern Vector2p harness_pc_stopping_point;   // pc_stopping_point_n/e
extern float harness_pc_lean_angle_max;      // pc_lean_angle_max
// NE_relax_velocity_controller's post-condition read by init_target in the same call (stubs_posctl.cpp)
extern float harness_att_target_roll, harness_att_target_pitch;   // ac_att_target_roll/pitch

// The real AC_PosControl::lean_angles_rad_to_accel_NED_mss (pos_real.cpp).
Vector3f harness_real_lean_angles_rad_to_accel_NED_mss(const Vector3f &att_target_euler_rad);

// The clock (stubs_hal.cpp) and the estimator's ground-speed limit (stubs_ahrs.cpp).
extern uint32_t harness_clock_ms;
extern float harness_gnd_spd_limit;

// The internal-error reporter (stubs_misc.cpp).
void harness_reset_internal_errors();
uint32_t harness_internal_error_count();
