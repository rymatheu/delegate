// stubs_posctl.cpp: the position controller, which is another stage (AC_PosControl), as AC_Loiter
// sees it from the loiter module.
//
// The object AC_Loiter holds a reference to is zeroed storage (adapter.cpp); the members its
// inline accessors read are loaded from the input record before each step. Every `_pos_control.`
// call in AC_Loiter.cpp and what it became:
//
//   call (AC_Loiter.cpp line)                       kind     became
//   get_dt_s() (326)                                inline   input dt (member _dt_s)
//   get_accel_target_NED_mss() (148)                inline   inputs pc_accel_target_n/e (previous tick)
//   get_roll_rad(), get_pitch_rad() (149-150)       inline   inputs pc_roll, pc_pitch (previous tick), or
//                                                            NE_relax_velocity_controller's post-condition
//   get_vel_desired_NED_ms() (341)                  inline   inputs pc_vel_desired_n/e (previous tick)
//   get_pos_desired_NED_m() (393)                   inline   inputs pc_pos_desired_n/e (previous tick)
//   NE_get_vel_pid().kP() (357)                     inline   parameter psc_ne_vel_p (_pid_vel_ne_m._kp)
//   lean_angles_rad_to_accel_NED_mss (180, 198)     real     AC_PosControl.cpp:1200-1215 (pos_real.cpp)
//   get_lean_angle_max_rad() (239, 242)             stand-in input pc_lean_angle_max (the position
//                                                            stage's value, previous tick)
//   get_stopping_point_NE_m (218)                   stand-in inputs pc_stopping_point_n/e (previous tick)
//   NE_set_correction_speed_accel_m (118, 141)      stand-in outputs lt_tgt_ne_set_correction_speed_accel,
//                                                            lt_tgt_ne_correction_speed/accel
//   NE_set_pos_error_max_m (119, 142)               inline   calls AC_P_2D::set_error_max (stand-in here,
//                                                            AC_P_2D.cpp is not compiled): outputs
//                                                            lt_cmd_position_NE_set_pos_error_max_m...
//   NE_init_controller_stopping_point() (122)       stand-in output lt_tgt_ne_init_stopping_point
//   set_pos_desired_NE_m (131)                      inline   a member write; the adapter detects it
//                                                            (outputs lt_cmd_position_set_pos_desired_NE_m...)
//   NE_relax_velocity_controller() (145)            stand-in output lt_cmd_position_NE_relax_velocity_controller
//   NE_soften_for_landing() (160)                   stand-in output lt_cmd_position_NE_soften_for_landing
//   set_pos_vel_accel_NE_m (399)                    stand-in outputs lt_tgt_pos/vel/acc_n/e, lt_tgt_valid
//   NE_update_controller() (253)                    stand-in output lt_tgt_ne_update
//   NE_get_pos_p(), D_get_pos_p(), D_get_max_accel_mss() (386)
//                                                   inline   avoidance block, compiled out (flags.txt)
//
// Post-conditions: where AC_Loiter reads, later in the same step, a member that one of its own
// hand-over calls changed, the stand-in applies that call's assignment to the member, copied from
// the real method; the position stage's next output then carries the real value:
//   NE_init_controller_stopping_point: _vel_desired_ned_ms.xy() and _accel_desired_ned_mss.xy()
//     zeroed (AC_PosControl.cpp:507-508);
//   NE_relax_velocity_controller: _roll_target_rad, _pitch_target_rad = the attitude target's
//     roll and pitch (NE_init_controller, AC_PosControl.cpp:550-552), the attitude stage's
//     ac_att_target_roll/pitch of the previous tick, which the position stage's NE_init_controller
//     reads this tick; init_target reads them at AC_Loiter.cpp:149-150;
//   set_pos_vel_accel_NE_m: desired position, velocity, acceleration NE (AC_PosControl.cpp:1193-1196).
// Not applied, because the real effect is arithmetic of the position stage, not an assignment
// (deviations from the monolithic vehicle, each a one-tick-old read):
//   - init_target reads get_accel_target_NED_mss() after NE_relax_velocity_controller
//     (AC_Loiter.cpp:148): in ArduCopter the target after the relax's decay and NE_init_controller's
//     lean-angle limit (AC_PosControl.cpp:518-521, 563-571); here the previous tick's target;
//   - update after NE_soften_for_landing in the same tick (ModeLoiter::run with land_complete_maybe,
//     mode_loiter.cpp:99-101, 139/160) reads the desired position before the softening
//     (AC_PosControl.cpp:531-534); set_pos_vel_accel_NE_m then hands the unsoftened position, so the
//     softening of the NE position target is lost on those ticks (its I-term protection,
//     NE_set_externally_limited, still takes effect in the position stage);
//   - update after NE_relax_velocity_controller or NE_init_controller_stopping_point in the same
//     tick reads the desired velocity and position of the previous tick (no covered mode does both
//     in one tick: ModeLoiter::run calls init_target or update, mode_loiter.cpp:107-161);
//   - after an EKF position reset the position stage's update_estimates moves the desired position
//     earlier in the tick (AC_PosControl::handle_ekf_NE_reset); update reads it from before the move.
#include "cut.h"

#include <stdio.h>
#include <stdlib.h>

#include <AC_AttitudeControl/AC_PosControl.h>
#include <AC_PID/AC_P_2D.h>

HarnessLoiterCalls harness_loiter_calls;
uint32_t harness_current_seq;
Vector2p harness_pc_stopping_point;
float harness_pc_lean_angle_max;
float harness_att_target_roll, harness_att_target_pitch;

// the call order of the hand-over, for a sequenced tick: the first call's `_seq`
static void note_seq(uint32_t &seq, bool &called)
{
    if (!called) {
        seq = harness_current_seq;
    }
    called = true;
}

static void note_handover()
{
    HarnessLoiterCalls &c = harness_loiter_calls;
    if (!c.ne_init_stopping_point && !c.ne_set_correction) {
        c.handover_seq = harness_current_seq;
    }
}

void AC_PosControl::NE_set_correction_speed_accel_m(float speed_ne_ms, float accel_ne_mss)
{
    note_handover();
    harness_loiter_calls.ne_set_correction = true;
    harness_loiter_calls.ne_correction_speed = speed_ne_ms;
    harness_loiter_calls.ne_correction_accel = accel_ne_mss;
}

// AC_PosControl::NE_set_pos_error_max_m (inline, AC_PosControl.h:119) calls this on _p_pos_ne_m,
// the position stage's NE position P controller; no other code of this module calls it
void AC_P_2D::set_error_max(float error_max)
{
    HarnessLoiterCalls &c = harness_loiter_calls;
    note_seq(c.error_max_seq, c.ne_set_pos_error_max);
    c.error_max = error_max;
}

void AC_PosControl::NE_init_controller_stopping_point()
{
    note_handover();
    harness_loiter_calls.ne_init_stopping_point = true;
    _vel_desired_ned_ms.xy().zero();
    _accel_desired_ned_mss.xy().zero();
}

void AC_PosControl::NE_relax_velocity_controller()
{
    HarnessLoiterCalls &c = harness_loiter_calls;
    note_seq(c.relax_seq, c.ne_relax);
    _roll_target_rad = harness_att_target_roll;
    _pitch_target_rad = harness_att_target_pitch;
}

void AC_PosControl::NE_soften_for_landing()
{
    HarnessLoiterCalls &c = harness_loiter_calls;
    note_seq(c.soften_seq, c.ne_soften);
}

void AC_PosControl::set_pos_vel_accel_NE_m(const Vector2p& pos_ne_m, const Vector2f& vel_ne_ms, const Vector2f& accel_ne_mss)
{
    HarnessLoiterCalls &c = harness_loiter_calls;
    note_seq(c.update_seq, c.set_pos_vel_accel);
    c.pos = pos_ne_m;
    c.vel = vel_ne_ms;
    c.accel = accel_ne_mss;
    _pos_desired_ned_m.xy() = pos_ne_m;
    _vel_desired_ned_ms.xy() = vel_ne_ms;
    _accel_desired_ned_mss.xy() = accel_ne_mss;
}

void AC_PosControl::NE_update_controller()
{
    harness_loiter_calls.ne_update = true;
}

Vector3f AC_PosControl::lean_angles_rad_to_accel_NED_mss(const Vector3f& att_target_euler_rad) const
{
    return harness_real_lean_angles_rad_to_accel_NED_mss(att_target_euler_rad);
}

float AC_PosControl::get_lean_angle_max_rad() const
{
    return harness_pc_lean_angle_max;
}

void AC_PosControl::get_stopping_point_NE_m(Vector2p &stopping_point_ne_m) const
{
    stopping_point_ne_m = harness_pc_stopping_point;
}
