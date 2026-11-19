// stubs_position.cpp: the AC_PosControl shadow (position stage).
//
// harness_position_fill writes, before the vehicle code runs, every field an inline getter the
// vehicle code calls reads (measure/proxy_surface.tsv, stage position, reached "inline"):
//   field                          source (input)                 getters
//   _pos_estimate_ned_m            est_pos_* (same tick: Copter::  get_pos_estimate_NED_m/U_m
//   _vel_estimate_ned_ms           est_vel_*  read_inertia runs    get_vel_estimate_U_ms
//                                             update_estimates
//                                             before the mode)
//   _pos_desired_ned_m             pc_pos_desired_*               get_pos_desired_NED_m/U_m
//   _pos_target_ned_m              pc_pos_target_*                crosstrack_error_m (real body)
//   _vel_desired_ned_ms            pc_vel_desired_*               get_vel_desired_NED_ms/U_ms
//   _pos_offset_ned_m              pc_pos_offset_*                get_pos_offset_NED_m/U_m
//   _p_pos_ne_m._error, _p_pos_d_m._error   pc_pos_error_*        get_pos_error_NE_m/D_m
//   _vel_terrain_d_ms              pc_vel_terrain_d               get_vel_terrain_D_ms
//   _yaw_target_rad, _yaw_rate_target_rads   pc_yaw, pc_yaw_rate  get_yaw_rad, get_yaw_rate_rads
//   _vel_max_ne_ms, _vel_max_up_ms, _vel_max_down_ms, _accel_max_ne_mss, _accel_max_d_mss
//                                  pc_ne_max_speed, pc_max_speed_up/down, pc_ne_max_accel, pc_d_max_accel   NE_get_max_speed_ms, ...
//   _vel_d_control_ratio           pc_vel_d_control_ratio         get_vel_D_control_ratio
//   _dt_s                          dt                             (the in-out replays below)
// get_estimated_accel_U_mss reads the AHRS shadow (est_accel_ef_z). D_get_pos_p and the gains
// are parameters (real var_info, same values as the position stage's record). Not filled:
// D_get_accel_pid()'s run-time state (its integrator is set by command; its pid_info is read
// only by logging, switched off).
//
// Post-conditions applied in the tick of the command (DESIGN.md 3), copied from
// AC_PosControl.cpp:
//   NE_init_controller   _yaw_target_rad = att target yaw, _yaw_rate_target_rads = 0,
//                        _pos_desired.xy = _pos_estimate.xy - _pos_offset.xy,
//                        _vel_desired.xy = _vel_estimate.xy (velocity offset taken as 0)
//   D_init_controller    _pos_desired.z = _pos_estimate.z - _pos_offset.z,
//                        _vel_desired.z = _vel_estimate.z
//   the inits and NE/D_update_controller  NE_is_active/D_is_active true for the rest of the
//                        tick (they set _last_update_*_ticks)
// Not emulated (one tick of lag accepted): the target/accel parts of the inits, which no covered
// call site reads back in the same tick.
// In-out arguments (input_vel_accel_NE_m, input_pos_vel_accel_NE_m, input_vel_accel_D_m,
// input_pos_vel_accel_D_m): recorded as given, then advanced by the same AP_Math call the real
// method makes on them last (update_vel_accel(_xy), update_pos_vel_accel(_xy), zero limits),
// with the shadow's _dt_s.
//
// Queries answered from the position stage's outputs of the previous tick:
//   NE_is_active, D_is_active        pc_ne_active / pc_d_active, or updated this tick
//   get_stopping_point_NE_m, _D_m    pc_stopping_point_* (one tick old; ArduCopter computes it
//                                    at the call from the current state)
//   get_thrust_vector                thrust_vec_* (the attitude stage reads the wire itself)
//   get_lean_angle_max_rad           real body (gen/ COPY_REAL)
#include <AC_AttitudeControl/AC_PosControl.h>
#include <AC_PID/AC_PID.h>
#include <AP_Math/control.h>
#include "supervisor_shadow.h"
#include "module_records.h"

HARNESS_ADDR(AC_PosControl, _pos_estimate_ned_m)
HARNESS_ADDR(AC_PosControl, _vel_estimate_ned_ms)
HARNESS_ADDR(AC_PosControl, _pos_desired_ned_m)
HARNESS_ADDR(AC_PosControl, _pos_target_ned_m)
HARNESS_ADDR(AC_PosControl, _vel_desired_ned_ms)
HARNESS_ADDR(AC_PosControl, _pos_offset_ned_m)
HARNESS_ADDR(AC_PosControl, _p_pos_ne_m)
HARNESS_ADDR(AC_PosControl, _p_pos_d_m)
HARNESS_ADDR(AC_PosControl, _vel_terrain_d_ms)
HARNESS_ADDR(AC_PosControl, _yaw_target_rad)
HARNESS_ADDR(AC_PosControl, _yaw_rate_target_rads)
HARNESS_ADDR(AC_PosControl, _vel_max_ne_ms)
HARNESS_ADDR(AC_PosControl, _vel_max_up_ms)
HARNESS_ADDR(AC_PosControl, _vel_max_down_ms)
HARNESS_ADDR(AC_PosControl, _accel_max_ne_mss)
HARNESS_ADDR(AC_PosControl, _accel_max_d_mss)
HARNESS_ADDR(AC_PosControl, _vel_d_control_ratio)
HARNESS_ADDR(AC_PosControl, _dt_s)
HARNESS_ADDR(AC_P_2D, _error)
HARNESS_ADDR(AC_P_1D, _error)

#define PC(T, m) HARNESS_REF(T, *pc, AC_PosControl, m)

static AC_PosControl *pc;
static bool pc_ne_active, pc_d_active;
static Vector3f pc_thrust_vec;
static Vector2p pc_stop_ne;
static postype_t pc_stop_d;

void harness_position_fill(const Input &in)
{
    pc = AC_PosControl::get_singleton();
    pc_ne_active = in.pc_ne_active;
    pc_d_active = in.pc_d_active;
    pc_thrust_vec = Vector3f(in.thrust_vec_x, in.thrust_vec_y, in.thrust_vec_z);
    pc_stop_ne = Vector2p(in.pc_stopping_point_n, in.pc_stopping_point_e);
    pc_stop_d = in.pc_stopping_point_d;
    if (pc == nullptr) {
        return;
    }
    PC(Vector3p, _pos_estimate_ned_m) = Vector3p(in.est_pos_n, in.est_pos_e, in.est_pos_d);
    PC(Vector3f, _vel_estimate_ned_ms) = Vector3f(in.est_vel_n, in.est_vel_e, in.est_vel_d);
    PC(Vector3p, _pos_desired_ned_m) =
        Vector3p(in.pc_pos_desired_n, in.pc_pos_desired_e, in.pc_pos_desired_d);
    PC(Vector3p, _pos_target_ned_m) =
        Vector3p(in.pc_pos_target_n, in.pc_pos_target_e, in.pc_pos_target_d);
    PC(Vector3f, _vel_desired_ned_ms) =
        Vector3f(in.pc_vel_desired_n, in.pc_vel_desired_e, in.pc_vel_desired_d);
    PC(Vector3p, _pos_offset_ned_m) =
        Vector3p(in.pc_pos_offset_n, in.pc_pos_offset_e, in.pc_pos_offset_d);
    HARNESS_REF(Vector2f, PC(AC_P_2D, _p_pos_ne_m), AC_P_2D, _error) =
        Vector2f(in.pc_pos_error_n, in.pc_pos_error_e);
    HARNESS_REF(float, PC(AC_P_1D, _p_pos_d_m), AC_P_1D, _error) = in.pc_pos_error_d;
    PC(float, _vel_terrain_d_ms) = in.pc_vel_terrain_d;
    PC(float, _yaw_target_rad) = in.pc_yaw;
    PC(float, _yaw_rate_target_rads) = in.pc_yaw_rate;
    PC(float, _vel_max_ne_ms) = in.pc_ne_max_speed;
    PC(float, _vel_max_up_ms) = in.pc_max_speed_up;
    PC(float, _vel_max_down_ms) = in.pc_max_speed_down;
    PC(float, _accel_max_ne_mss) = in.pc_ne_max_accel;
    PC(float, _accel_max_d_mss) = in.pc_d_max_accel;
    PC(float, _vel_d_control_ratio) = in.pc_vel_d_control_ratio;
    PC(float, _dt_s) = in.dt;
}

bool AC_PosControl::NE_is_active() const
{
    // AC_PosControl.cpp: _last_update_ne_ticks is set by NE_update_controller and by the inits
    return pc_ne_active || sup_cmd_called("AC_PosControl::NE_update_controller") ||
           sup_cmd_called("AC_PosControl::NE_init_controller") ||
           sup_cmd_called("AC_PosControl::NE_init_controller_stopping_point");
}

bool AC_PosControl::D_is_active() const
{
    return pc_d_active || sup_cmd_called("AC_PosControl::D_update_controller") ||
           sup_cmd_called("AC_PosControl::D_init_controller") ||
           sup_cmd_called("AC_PosControl::D_init_controller_stopping_point") ||
           sup_cmd_called("AC_PosControl::D_init_controller_no_descent");
}

Vector3f AC_PosControl::get_thrust_vector() const
{
    return pc_thrust_vec;
}

void AC_PosControl::get_stopping_point_NE_m(Vector2p &stopping_point_ne_m) const
{
    stopping_point_ne_m = pc_stop_ne;
}

void AC_PosControl::get_stopping_point_D_m(postype_t &stopping_point_d_m) const
{
    stopping_point_d_m = pc_stop_d;
}

// ---- commands with a post-condition read in the same tick
void AC_PosControl::NE_init_controller()
{
    sup_cmd_begin_named("AC_PosControl::NE_init_controller", "position");
    sup_cmd_end();
    // AC_PosControl.cpp NE_init_controller: the assignments below (offsets' velocity part taken
    // as 0: _vel_offset_ned_ms is not filled)
    _yaw_target_rad = _attitude_control.get_att_target_euler_rad().z;
    _yaw_rate_target_rads = 0.0f;
    _pos_desired_ned_m.xy() = _pos_estimate_ned_m.xy() - _pos_offset_ned_m.xy();
    _vel_desired_ned_ms.xy() = _vel_estimate_ned_ms.xy();
}

void AC_PosControl::D_init_controller()
{
    sup_cmd_begin_named("AC_PosControl::D_init_controller", "position");
    sup_cmd_end();
    _pos_desired_ned_m.z = _pos_estimate_ned_m.z - _pos_offset_ned_m.z;
    _vel_desired_ned_ms.z = _vel_estimate_ned_ms.z;
}

// ---- in-out arguments
void AC_PosControl::input_vel_accel_NE_m(Vector2f &vel_ne_ms, const Vector2f &accel_ne_mss,
                                         bool limit_output)
{
    sup_cmd_begin_named("AC_PosControl::input_vel_accel_NE_m", "position");
    sup_arg(vel_ne_ms);
    sup_arg(accel_ne_mss);
    sup_arg(limit_output);
    sup_cmd_end();
    update_vel_accel_xy(vel_ne_ms, accel_ne_mss, _dt_s, Vector2f(), Vector2f());
}

void AC_PosControl::input_pos_vel_accel_NE_m(Vector2p &pos_ne_m, Vector2f &vel_ne_ms,
                                             const Vector2f &accel_ne_mss, bool limit_output)
{
    sup_cmd_begin_named("AC_PosControl::input_pos_vel_accel_NE_m", "position");
    sup_arg(pos_ne_m);
    sup_arg(vel_ne_ms);
    sup_arg(accel_ne_mss);
    sup_arg(limit_output);
    sup_cmd_end();
    update_pos_vel_accel_xy(pos_ne_m, vel_ne_ms, accel_ne_mss, _dt_s, Vector2f(), Vector2f(),
                            Vector2f());
}

void AC_PosControl::input_vel_accel_D_m(float &vel_d_ms, float accel_d_mss, bool limit_output)
{
    sup_cmd_begin_named("AC_PosControl::input_vel_accel_D_m", "position");
    sup_arg(vel_d_ms);
    sup_arg(accel_d_mss);
    sup_arg(limit_output);
    sup_cmd_end();
    update_vel_accel(vel_d_ms, accel_d_mss, _dt_s, 0.0, 0.0);
}

void AC_PosControl::input_pos_vel_accel_D_m(float &pos_d_m, float &vel_d_ms, float accel_d_mss,
                                            bool limit_output)
{
    sup_cmd_begin_named("AC_PosControl::input_pos_vel_accel_D_m", "position");
    sup_arg(pos_d_m);
    sup_arg(vel_d_ms);
    sup_arg(accel_d_mss);
    sup_arg(limit_output);
    sup_cmd_end();
    postype_t posp = pos_d_m;
    update_pos_vel_accel(posp, vel_d_ms, accel_d_mss, _dt_s, 0.0, 0.0, 0.0);
    pos_d_m = posp;
}

// AC_PID::set_integrator: the one call site in the covered flows is
// pos_control->D_get_accel_pid().set_integrator (Attitude.cpp:129, set_throttle_takeoff), which
// becomes the position stage's command D_accel_pid_set_integrator; any other PID is counted as
// unanswered.
void AC_PID::set_integrator(float i)
{
    AC_PosControl *p = AC_PosControl::get_singleton();
    if (p != nullptr && this == &p->D_get_accel_pid()) {
        sup_cmd_begin_named("AC_PosControl::D_accel_pid_set_integrator", "position");
        sup_arg(i);
        sup_cmd_end();
        return;
    }
    sup_lenient("AC_PID::set_integrator (a PID other than the position stage's D accel)");
}
