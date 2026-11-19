// cut.h: what adapter.cpp and the stubs share about the cut of the guidance module.
//
// The position controller (AC_PosControl) and the attitude controller (AC_AttitudeControl) are
// other stages. AC_WPNav holds references to both; here they are objects in zeroed storage whose
// members the adapter loads from the input record before each step (the signals), and whose
// non-inline methods AC_WPNav calls are stand-ins (stubs_posctl.cpp) that record the calls handed
// to the position stage. No constructor of either class runs, and no virtual method of either is
// called by AC_WPNav (a virtual call would find a null vtable pointer and crash).
#pragma once

#include <stdint.h>

#include <AP_Math/AP_Math.h>

// Reaching a protected or private member: access is not checked on the template arguments of an
// explicit instantiation ([temp.explicit]), so Rob<Tag, &C::m> may name C::m and hands its
// pointer-to-member out through a friend found by argument-dependent lookup on Tag.
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

// The calls AC_WPNav hands to the position controller during one step, recorded by the stand-ins
// in stubs_posctl.cpp and turned into the tgt_ outputs by the adapter. Cleared before each step.
struct HarnessPosCalls {
    bool ne_init_stopping_point;        // NE_init_controller_stopping_point()
    bool d_init_stopping_point;         // D_init_controller_stopping_point()
    bool ne_set_max_speed_accel;        // NE_set_max_speed_accel_m(speed, accel)
    bool ne_set_correction;             // NE_set_correction_speed_accel_m(speed, accel)
    float ne_correction_speed, ne_correction_accel;
    bool d_set_max_speed_accel;         // D_set_max_speed_accel_m(down, up, accel)
    bool d_set_correction;              // D_set_correction_speed_accel_m(down, up, accel)
    float d_correction_down, d_correction_up, d_correction_accel;
    bool set_pos_vel_accel;             // set_pos_vel_accel_NED_m(pos, vel, accel)
    Vector3p pos;
    Vector3f vel, accel;
    bool ne_update;                     // NE_update_controller()
    // the `_seq` of the command during which the first initializer or limit setter, and
    // set_pos_vel_accel_NED_m, were called (0: not sequenced); harness bookkeeping
    uint32_t handover_seq, update_seq;
};
// the `_seq` of the command the adapter is executing (0: not sequenced)
extern uint32_t harness_current_seq;
extern HarnessPosCalls harness_pos_calls;

// The values the stand-ins read that are not members of AC_PosControl (stubs_posctl.cpp).
extern Vector3p harness_pc_stopping_point;      // input pc_stopping_point_n/e/d

// The clock (stubs_hal.cpp).
extern uint32_t harness_clock_ms;

// The internal-error reporter (stubs_logging.cpp). Each error is also classified by the
// adapter's hook: raised while the navigator had never been initialized (its S-curve snap limit
// still 0, i.e. before the first wp_and_spline_init_m), or not.
void harness_reset_internal_errors();
uint32_t harness_internal_error_count();
extern bool (*harness_navigator_uninitialized)();
extern uint32_t harness_uninitialized_errors;
// ... and, of the others, those raised after the position stage returned a speed or acceleration
// limit other than the one this module handed it at the previous tick (adapter.cpp)
extern bool harness_limits_incoherent;
extern uint32_t harness_incoherent_errors;

// Lines written by ArduPilot's SITL debug printf (stubs_hal.cpp), to stderr instead of stdout.
extern uint32_t harness_printf_count;
