// adapter.cpp: the cut between the harness records and ArduCopter's real position controller.
//
// The object is a real AC_PosControl (with its AC_P_2D, AC_P_1D, AC_PID_2D, AC_PID_Basic and AC_PID).
// HarnessPosControl below derives from it only to read protected members for the outputs; it
// overrides nothing (AC_PosControl has no virtual methods).
//
// init, as ArduCopter does it (Copter::allocate_motors, system.cpp:454-483):
//   ahrs_view = ahrs.create_view(ROTATION_NONE)          the stand-in view (stubs_ahrs.cpp)
//   attitude_control = NEW_NOTHROW AC_AttitudeControl_Multi(*ahrs_view, *motors)
//                                                        the stand-in HarnessAttitude
//   pos_control = NEW_NOTHROW AC_PosControl(*ahrs_view, *motors, *attitude_control)
//   AP_Param::load_object_from_eeprom(pos_control, ...)  cut: every AP_Param member of the
//                                                        controller is set from the parameter record
// ArduPilot's operator new returns zeroed memory (AP_Common/c++.cpp); the objects are built in
// zeroed storage. Copter::init_ardupilot's convert_parameters (parameter conversion) and
// D_get_accel_pid().set_notch_sample_rate (no notch: PSC_D_ACC_NTF = NEF = 0) are not called.
//
// step: the order of the calls and where ArduCopter makes them is in Module.lean's header. A call
// whose Boolean is false this tick is not made. Arguments a method takes by reference and writes
// back (input_vel_accel_NE_m's vel, input_pos_vel_accel_*'s pos and vel) are passed as locals and
// the written-back values are not returned: the listed flows discard them except GUIDED's
// velocity and position-velocity controllers (mode_guided.cpp:809, :950), which keep them.
#include "module_protocol.h"

#include <new>
#include <string.h>

#include <AC_AttitudeControl/AC_PosControl.h>
#include <AP_Scheduler/AP_Scheduler.h>
#include "stand_ins.h"

// the cut, defined in stubs.cpp
void harness_reset_cut();
void harness_reset_internal_errors();
uint32_t harness_internal_error_count();
uint32_t harness_internal_error_flow_count();
AP_AHRS_View *harness_make_view();
void harness_scheduler_lookahead(bool on);

class HarnessPosControl : public AC_PosControl {
public:
    using AC_PosControl::AC_PosControl;

    void set_params(const Params &p)
    {
        _p_pos_ne_m.kP().set(p.psc_ne_pos_p);
        _p_pos_d_m.kP().set(p.psc_d_pos_p);
        _pid_vel_ne_m.kP().set(p.psc_ne_vel_p);
        _pid_vel_ne_m.kI().set(p.psc_ne_vel_i);
        _pid_vel_ne_m.kD().set(p.psc_ne_vel_d);
        _pid_vel_ne_m.set_imax(p.psc_ne_vel_imax);
        _pid_vel_ne_m.filt_E_hz().set(p.psc_ne_vel_flte);
        _pid_vel_ne_m.filt_D_hz().set(p.psc_ne_vel_fltd);
        _pid_vel_ne_m.ff().set(p.psc_ne_vel_ff);
        _pid_vel_d_m.kP().set(p.psc_d_vel_p);
        _pid_vel_d_m.kI().set(p.psc_d_vel_i);
        _pid_vel_d_m.kD().set(p.psc_d_vel_d);
        _pid_vel_d_m.set_imax(p.psc_d_vel_imax);
        _pid_vel_d_m.filt_E_hz().set(p.psc_d_vel_flte);
        _pid_vel_d_m.filt_D_hz().set(p.psc_d_vel_fltd);
        _pid_vel_d_m.ff().set(p.psc_d_vel_ff);
        _pid_accel_d_m.kP().set(p.psc_d_acc_p);
        _pid_accel_d_m.kI().set(p.psc_d_acc_i);
        _pid_accel_d_m.kD().set(p.psc_d_acc_d);
        _pid_accel_d_m.kIMAX().set(p.psc_d_acc_imax);
        _pid_accel_d_m.ff().set(p.psc_d_acc_ff);
        _pid_accel_d_m.filt_T_hz().set(p.psc_d_acc_fltt);
        _pid_accel_d_m.filt_E_hz().set(p.psc_d_acc_flte);
        _pid_accel_d_m.filt_D_hz().set(p.psc_d_acc_fltd);
        _pid_accel_d_m.slew_limit().set(p.psc_d_acc_smax);
        _pid_accel_d_m.kPDMAX().set(p.psc_d_acc_pdmx);
        _pid_accel_d_m.kDff().set(p.psc_d_acc_d_ff);
        // PSC_D_ACC_NTF, _NEF: 0 from the zeroed storage (no notch filters)
        _lean_angle_max_deg.set(p.psc_angle_max);
        _shaping_jerk_ne_msss.set(p.psc_ne_jerk);
        _shaping_jerk_d_msss.set(p.psc_d_jerk);
    }

    const Vector3f &accel_desired() const { return _accel_desired_ned_mss; }
    const Vector3f &limit_vector() const { return _limit_vector_ned; }
    float jerk_max_ne() const { return _jerk_max_ne_msss; }
    float jerk_max_d() const { return _jerk_max_d_msss; }
    bool vibe_comp() const { return _vibe_comp_enabled; }
    float lean_angle_max() const { return get_lean_angle_max_rad(); }
};

// statically allocated, zeroed before each construction (ArduPilot's NEW_NOTHROW zeroes)
alignas(HarnessMotors) static unsigned char motors_storage[sizeof(HarnessMotors)];
alignas(HarnessAttitude) static unsigned char attitude_storage[sizeof(HarnessAttitude)];
alignas(HarnessPosControl) static unsigned char pos_storage[sizeof(HarnessPosControl)];
static HarnessMotors *motors;
static HarnessAttitude *attitude;
static HarnessPosControl *pc;
static AP_AHRS_View *view;

void module_init(const Params &p)
{
    harness_reset_internal_errors();
    harness_reset_cut();   // clock, AHRS, scheduler and view storage zeroed
    view = harness_make_view();
    memset(motors_storage, 0, sizeof motors_storage);
    motors = new (motors_storage) HarnessMotors();
    memset(attitude_storage, 0, sizeof attitude_storage);
    attitude = new (attitude_storage) HarnessAttitude(*view, *motors);
    attitude->set_params(p.atc_rate_r_max, p.atc_rate_p_max, p.atc_acc_r_max, p.atc_acc_p_max);
    memset(pos_storage, 0, sizeof pos_storage);
    pc = new (pos_storage) HarnessPosControl(*view, *motors, *attitude);
    pc->set_params(p);
}

static Vector2f v2(float x, float y) { return Vector2f{x, y}; }

// --- the calls of a tick, one id each, in the fixed order (Module.lean's header). An id runs
// when its command Boolean (or, for 16 and 17, its guidance signal) is set.
enum OpId {
    OP_UPDATE_ESTIMATES, OP_SET_VIBE_COMP, OP_SET_RESET_METHOD,
    OP_NE_SET_MAX, OP_NE_SET_CORR, OP_NE_SET_POS_ERROR_MAX, OP_D_SET_MAX, OP_D_SET_CORR,
    OP_NE_INIT, OP_NE_INIT_SP, OP_D_INIT, OP_D_INIT_NO_DESCENT, OP_D_INIT_SP,
    OP_INIT_POS_TERRAIN, OP_SET_POS_DESIRED_NE, OP_SET_INTEGRATOR,
    OP_GUIDANCE_HANDOVER, OP_GUIDANCE_TARGETS,
    OP_LT_SOFTEN, OP_LT_CORR, OP_LT_ERRMAX, OP_LT_INIT_SP, OP_LT_SET_POS_DESIRED, OP_LT_RELAX,
    OP_LT_TARGETS,
    OP_NE_RELAX, OP_NE_SOFTEN, OP_INPUT_VEL_ACCEL_NE, OP_INPUT_POS_VEL_ACCEL_NE, OP_INPUT_POS_NED,
    OP_NE_STOP_VEL, OP_NE_STOP_POS, OP_NE_UPDATE,
    OP_D_RELAX, OP_D_CLIMB_RATE, OP_INPUT_POS_VEL_ACCEL_D, OP_INPUT_VEL_ACCEL_D, OP_D_ALT_SLEW,
    OP_D_UPDATE, OP_SUPERVISOR_SET_THROTTLE, OP_COUNT
};

struct SeqItem { uint32_t seq; int id; };

// Order the set calls. All `_seq` 0: the fixed order. Otherwise by `_seq`; a set call with
// `_seq` 0 takes the largest `_seq` of the calls before it in the fixed order (so it runs right
// after them), ties keep the fixed order. Returns whether the tick is sequenced.
static bool order_items(SeqItem *it, int n)
{
    bool any = false;
    for (int i = 0; i < n; i++) {
        any = any || it[i].seq != 0;
    }
    if (!any) {
        return false;
    }
    uint32_t run = 0;
    for (int i = 0; i < n; i++) {
        if (it[i].seq == 0) {
            it[i].seq = run;
        }
        if (it[i].seq > run) {
            run = it[i].seq;
        }
    }
    for (int i = 1; i < n; i++) {   // stable insertion sort by seq
        SeqItem x = it[i];
        int j = i - 1;
        while (j >= 0 && it[j].seq > x.seq) {
            it[j + 1] = it[j];
            j--;
        }
        it[j + 1] = x;
    }
    return true;
}

static bool ne_updated, guidance_ne_pending;
// whether the NE and D updates (and the guidance stage's limits) were the last calls of their
// axis this tick: a call made after an update changes the state its outputs describe
static bool ne_update_last, d_update_last, handover_limits_last;

static bool touches_ne(int id)
{
    switch (id) {
    case OP_UPDATE_ESTIMATES: case OP_NE_SET_MAX: case OP_NE_SET_CORR: case OP_NE_SET_POS_ERROR_MAX:
    case OP_NE_INIT: case OP_NE_INIT_SP: case OP_SET_POS_DESIRED_NE: case OP_GUIDANCE_HANDOVER:
    case OP_GUIDANCE_TARGETS: case OP_NE_RELAX: case OP_NE_SOFTEN: case OP_INPUT_VEL_ACCEL_NE:
    case OP_INPUT_POS_VEL_ACCEL_NE: case OP_INPUT_POS_NED: case OP_NE_STOP_VEL: case OP_NE_STOP_POS:
    case OP_LT_SOFTEN: case OP_LT_CORR: case OP_LT_ERRMAX: case OP_LT_INIT_SP:
    case OP_LT_SET_POS_DESIRED: case OP_LT_RELAX: case OP_LT_TARGETS:
        return true;
    default:
        return false;
    }
}

static bool touches_d(int id)
{
    switch (id) {
    case OP_UPDATE_ESTIMATES: case OP_SET_VIBE_COMP: case OP_D_SET_MAX: case OP_D_SET_CORR:
    case OP_D_INIT: case OP_D_INIT_NO_DESCENT: case OP_D_INIT_SP: case OP_INIT_POS_TERRAIN:
    case OP_SET_INTEGRATOR: case OP_GUIDANCE_HANDOVER: case OP_GUIDANCE_TARGETS:
    case OP_INPUT_POS_NED: case OP_D_RELAX: case OP_D_CLIMB_RATE: case OP_INPUT_POS_VEL_ACCEL_D:
    case OP_INPUT_VEL_ACCEL_D: case OP_D_ALT_SLEW:
        return true;
    default:
        return false;
    }
}

static void run_op(int id, const Input &in, bool sequenced)
{
    switch (id) {
    case OP_UPDATE_ESTIMATES:   // Copter::read_inertia
        pc->update_estimates(in.cmd_position_update_estimates_high_vibes);
        break;
    case OP_SET_VIBE_COMP:      // Copter::check_vibration (ekf_check.cpp:303, :317)
        pc->set_vibe_comp(in.cmd_position_set_vibe_comp_on);
        break;
    case OP_SET_RESET_METHOD:   // Copter::update_flight_mode (mode.cpp:516)
        pc->set_reset_handling_method(in.cmd_position_set_reset_handling_method_method == 1 ?
            AC_PosControl::EKFResetMethod::MoveVehicle : AC_PosControl::EKFResetMethod::MoveTarget);
        break;
    // 5. limits (the modes' init and run functions, AC_WPNav, AC_Loiter)
    case OP_NE_SET_MAX:
        pc->NE_set_max_speed_accel_m(in.cmd_position_NE_set_max_speed_accel_m_speed,
                                     in.cmd_position_NE_set_max_speed_accel_m_accel);
        break;
    case OP_NE_SET_CORR:
        pc->NE_set_correction_speed_accel_m(in.cmd_position_NE_set_correction_speed_accel_m_speed,
                                            in.cmd_position_NE_set_correction_speed_accel_m_accel);
        break;
    case OP_NE_SET_POS_ERROR_MAX:
        pc->NE_set_pos_error_max_m(in.cmd_position_NE_set_pos_error_max_m_error_max);
        break;
    case OP_D_SET_MAX:
        pc->D_set_max_speed_accel_m(in.cmd_position_D_set_max_speed_accel_m_down,
                                    in.cmd_position_D_set_max_speed_accel_m_up,
                                    in.cmd_position_D_set_max_speed_accel_m_accel);
        break;
    case OP_D_SET_CORR:
        pc->D_set_correction_speed_accel_m(in.cmd_position_D_set_correction_speed_accel_m_down,
                                           in.cmd_position_D_set_correction_speed_accel_m_up,
                                           in.cmd_position_D_set_correction_speed_accel_m_accel);
        break;
    // 6. initializers
    case OP_NE_INIT: pc->NE_init_controller(); break;
    case OP_NE_INIT_SP: pc->NE_init_controller_stopping_point(); break;
    case OP_D_INIT: pc->D_init_controller(); break;
    case OP_D_INIT_NO_DESCENT: pc->D_init_controller_no_descent(); break;
    case OP_D_INIT_SP: pc->D_init_controller_stopping_point(); break;
    case OP_INIT_POS_TERRAIN:
        pc->init_pos_terrain_D_m(in.cmd_position_init_pos_terrain_D_m_terrain_d);
        break;
    case OP_SET_POS_DESIRED_NE:
        pc->set_pos_desired_NE_m(Vector2p{in.cmd_position_set_pos_desired_NE_m_n,
                                          in.cmd_position_set_pos_desired_NE_m_e});
        break;
    case OP_SET_INTEGRATOR:
        pc->D_get_accel_pid().set_integrator(in.cmd_position_D_accel_pid_set_integrator_i);
        break;
    // 6b. the guidance stage's calls of this tick (signals tgt_*, AC_WPNav of the same tick), in
    // AC_WPNav's order: wp_and_spline_init_m initializes at the stopping point
    // (AC_WPNav.cpp:223-224), then sets the limits (:232-235); set_speed_NE_ms, set_speed_up_ms
    // and set_speed_down_ms set limits only (:283-313), after the initialization. A method the
    // guidance stage called more than once in the tick is reported once, with the arguments of
    // its last call, which is the state those calls leave.
    case OP_GUIDANCE_HANDOVER:
        if (in.tgt_d_init_stopping_point) {
            pc->D_init_controller_stopping_point();
        }
        if (in.tgt_ne_init_stopping_point) {
            pc->NE_init_controller_stopping_point();
        }
        if (in.tgt_ne_set_max_speed_accel) {
            pc->NE_set_max_speed_accel_m(in.tgt_ne_max_speed, in.tgt_ne_max_accel);
        }
        if (in.tgt_ne_set_correction_speed_accel) {
            pc->NE_set_correction_speed_accel_m(in.tgt_ne_correction_speed, in.tgt_ne_correction_accel);
        }
        if (in.tgt_d_set_max_speed_accel) {
            pc->D_set_max_speed_accel_m(in.tgt_max_speed_down, in.tgt_max_speed_up, in.tgt_d_max_accel);
        }
        if (in.tgt_d_set_correction_speed_accel) {
            pc->D_set_correction_speed_accel_m(in.tgt_d_correction_speed_down, in.tgt_d_correction_speed_up,
                                               in.tgt_d_correction_accel);
        }
        break;
    // 7. the guidance signal (AC_WPNav::advance_wp_target_along_track, AC_Loiter::calc_desired_velocity).
    // With NED targets (AC_WPNav) the guidance stage's update_wpnav also ran NE_update_controller
    // right after set_pos_vel_accel_NED_m (AC_WPNav.cpp:636, :741). In a sequenced tick it is made
    // here, at update_wpnav's place; in the fixed order at the end of step 8, once, also when the
    // supervisor commands it (a mode running update_wpnav makes no NE call of step 8 in between).
    case OP_GUIDANCE_TARGETS:
        if (in.tgt_ne_only) {
            pc->set_pos_vel_accel_NE_m(Vector2p{in.tgt_pos_n, in.tgt_pos_e}, v2(in.tgt_vel_n, in.tgt_vel_e),
                                       v2(in.tgt_acc_n, in.tgt_acc_e));
        } else {
            pc->set_pos_terrain_target_D_m(in.tgt_terrain_d);
            pc->set_pos_vel_accel_NED_m(Vector3p{in.tgt_pos_n, in.tgt_pos_e, in.tgt_pos_d},
                                        Vector3f{in.tgt_vel_n, in.tgt_vel_e, in.tgt_vel_d},
                                        Vector3f{in.tgt_acc_n, in.tgt_acc_e, in.tgt_acc_d});
            if (sequenced) {
                pc->NE_update_controller();
                ne_updated = true;
            } else {
                guidance_ne_pending = true;
            }
        }
        break;
    // 7b. the loiter stage's calls of this tick (signals lt_*, AC_Loiter of the same tick), each at
    // the `_seq` of the supervisor's loiter command during which AC_Loiter made it; within one
    // command in AC_Loiter's order (init_target_m: correction limits, error limit, stopping-point
    // initialization, desired position, AC_Loiter.cpp:118-131; init_target: correction limits,
    // error limit, relax, :141-145; soften_for_landing, :160; update: set_pos_vel_accel_NE_m then
    // NE_update_controller, :250-253 and :399), which this fixed order follows; with every `_seq`
    // 0, ModeLoiter::run's order (soften, then init or update, mode_loiter.cpp:99-161)
    case OP_LT_SOFTEN: pc->NE_soften_for_landing(); break;
    case OP_LT_CORR:
        pc->NE_set_correction_speed_accel_m(in.lt_tgt_ne_correction_speed, in.lt_tgt_ne_correction_accel);
        break;
    case OP_LT_ERRMAX:
        pc->NE_set_pos_error_max_m(in.lt_cmd_position_NE_set_pos_error_max_m_error_max);
        break;
    case OP_LT_INIT_SP: pc->NE_init_controller_stopping_point(); break;
    case OP_LT_SET_POS_DESIRED:
        pc->set_pos_desired_NE_m(Vector2p{in.lt_cmd_position_set_pos_desired_NE_m_n,
                                          in.lt_cmd_position_set_pos_desired_NE_m_e});
        break;
    case OP_LT_RELAX: pc->NE_relax_velocity_controller(); break;
    case OP_LT_TARGETS:
        if (in.lt_tgt_valid) {
            pc->set_pos_vel_accel_NE_m(Vector2p{in.lt_tgt_pos_n, in.lt_tgt_pos_e}, v2(in.lt_tgt_vel_n, in.lt_tgt_vel_e),
                                       v2(in.lt_tgt_acc_n, in.lt_tgt_acc_e));
        }
        if (in.lt_tgt_ne_update) {
            pc->NE_update_controller();
            ne_updated = true;
        }
        break;
    // 8. NE shaping, then the NE update
    case OP_NE_RELAX: pc->NE_relax_velocity_controller(); break;
    case OP_NE_SOFTEN: pc->NE_soften_for_landing(); break;
    case OP_INPUT_VEL_ACCEL_NE: {
        Vector2f vel = v2(in.cmd_position_input_vel_accel_NE_m_vel_n, in.cmd_position_input_vel_accel_NE_m_vel_e);
        pc->input_vel_accel_NE_m(vel, v2(in.cmd_position_input_vel_accel_NE_m_accel_n,
                                         in.cmd_position_input_vel_accel_NE_m_accel_e),
                                 in.cmd_position_input_vel_accel_NE_m_limit_output);
        break;
    }
    case OP_INPUT_POS_VEL_ACCEL_NE: {
        Vector2p pos{in.cmd_position_input_pos_vel_accel_NE_m_pos_n, in.cmd_position_input_pos_vel_accel_NE_m_pos_e};
        Vector2f vel = v2(in.cmd_position_input_pos_vel_accel_NE_m_vel_n,
                          in.cmd_position_input_pos_vel_accel_NE_m_vel_e);
        pc->input_pos_vel_accel_NE_m(pos, vel, v2(in.cmd_position_input_pos_vel_accel_NE_m_accel_n,
                                                  in.cmd_position_input_pos_vel_accel_NE_m_accel_e),
                                     in.cmd_position_input_pos_vel_accel_NE_m_limit_output);
        break;
    }
    case OP_INPUT_POS_NED:
        pc->input_pos_NED_m(Vector3p{in.cmd_position_input_pos_NED_m_pos_n, in.cmd_position_input_pos_NED_m_pos_e,
                                     in.cmd_position_input_pos_NED_m_pos_d},
                            in.cmd_position_input_pos_NED_m_terrain_d, in.cmd_position_input_pos_NED_m_terrain_margin);
        break;
    case OP_NE_STOP_VEL: pc->NE_stop_vel_stabilisation(); break;
    case OP_NE_STOP_POS: pc->NE_stop_pos_stabilisation(); break;
    case OP_NE_UPDATE:
        pc->NE_update_controller();
        ne_updated = true;
        break;
    // 9. D shaping, then the D update (which calls set_throttle_out)
    case OP_D_RELAX: pc->D_relax_controller(in.cmd_position_D_relax_controller_throttle); break;
    case OP_D_CLIMB_RATE:
        pc->D_set_pos_target_from_climb_rate_ms(in.cmd_position_D_set_pos_target_from_climb_rate_ms_climb_rate,
            in.cmd_position_D_set_pos_target_from_climb_rate_ms_ignore_descent_limit);
        break;
    case OP_INPUT_POS_VEL_ACCEL_D: {
        float pos = in.cmd_position_input_pos_vel_accel_D_m_pos;
        float vel = in.cmd_position_input_pos_vel_accel_D_m_vel;
        pc->input_pos_vel_accel_D_m(pos, vel, in.cmd_position_input_pos_vel_accel_D_m_accel,
                                    in.cmd_position_input_pos_vel_accel_D_m_limit_output);
        break;
    }
    case OP_INPUT_VEL_ACCEL_D: {
        float vel = in.cmd_position_input_vel_accel_D_m_vel;
        pc->input_vel_accel_D_m(vel, in.cmd_position_input_vel_accel_D_m_accel,
                                in.cmd_position_input_vel_accel_D_m_limit_output);
        break;
    }
    case OP_D_ALT_SLEW: pc->D_set_alt_target_with_slew_m(in.cmd_position_D_set_alt_target_with_slew_m_alt); break;
    case OP_D_UPDATE: pc->D_update_controller(); break;
    // the supervisor's AC_AttitudeControl_Multi::set_throttle_out of this tick (the attitude
    // stage's command): its effect on get_throttle_in(), which D_init_controller reads to seed the
    // accel PID's integrator (AC_PosControl.cpp:920). ModeAltHold's takeoff ramp makes the two
    // calls in that order in one tick (takeoff.cpp:83-86). Only in a sequenced tick, at its `_seq`
    // (run_ordered); otherwise get_throttle_in() is the attitude stage's value of the previous
    // tick (ac_throttle_in), as before.
    case OP_SUPERVISOR_SET_THROTTLE:
        attitude->supervisor_set_throttle_out(in.cmd_attitude_set_throttle_out_throttle_in);
        break;
    default: break;
    }
}

static void run_ordered(const Input &in)
{
#define P_ITEM(flag, seqv, opid) if (flag) { items[n].seq = (seqv); items[n].id = (opid); n++; }
    SeqItem items[OP_COUNT];
    int n = 0;
    P_ITEM(in.cmd_position_update_estimates, in.cmd_position_update_estimates_seq, OP_UPDATE_ESTIMATES)
    P_ITEM(in.cmd_position_set_vibe_comp, in.cmd_position_set_vibe_comp_seq, OP_SET_VIBE_COMP)
    P_ITEM(in.cmd_position_set_reset_handling_method, in.cmd_position_set_reset_handling_method_seq,
           OP_SET_RESET_METHOD)
    P_ITEM(in.cmd_position_NE_set_max_speed_accel_m, in.cmd_position_NE_set_max_speed_accel_m_seq, OP_NE_SET_MAX)
    P_ITEM(in.cmd_position_NE_set_correction_speed_accel_m, in.cmd_position_NE_set_correction_speed_accel_m_seq,
           OP_NE_SET_CORR)
    P_ITEM(in.cmd_position_NE_set_pos_error_max_m, in.cmd_position_NE_set_pos_error_max_m_seq,
           OP_NE_SET_POS_ERROR_MAX)
    P_ITEM(in.cmd_position_D_set_max_speed_accel_m, in.cmd_position_D_set_max_speed_accel_m_seq, OP_D_SET_MAX)
    P_ITEM(in.cmd_position_D_set_correction_speed_accel_m, in.cmd_position_D_set_correction_speed_accel_m_seq,
           OP_D_SET_CORR)
    P_ITEM(in.cmd_position_NE_init_controller, in.cmd_position_NE_init_controller_seq, OP_NE_INIT)
    P_ITEM(in.cmd_position_NE_init_controller_stopping_point, in.cmd_position_NE_init_controller_stopping_point_seq,
           OP_NE_INIT_SP)
    P_ITEM(in.cmd_position_D_init_controller, in.cmd_position_D_init_controller_seq, OP_D_INIT)
    P_ITEM(in.cmd_position_D_init_controller_no_descent, in.cmd_position_D_init_controller_no_descent_seq,
           OP_D_INIT_NO_DESCENT)
    P_ITEM(in.cmd_position_D_init_controller_stopping_point, in.cmd_position_D_init_controller_stopping_point_seq,
           OP_D_INIT_SP)
    P_ITEM(in.cmd_position_init_pos_terrain_D_m, in.cmd_position_init_pos_terrain_D_m_seq, OP_INIT_POS_TERRAIN)
    P_ITEM(in.cmd_position_set_pos_desired_NE_m, in.cmd_position_set_pos_desired_NE_m_seq, OP_SET_POS_DESIRED_NE)
    P_ITEM(in.cmd_position_D_accel_pid_set_integrator, in.cmd_position_D_accel_pid_set_integrator_seq,
           OP_SET_INTEGRATOR)
    P_ITEM(in.tgt_d_init_stopping_point || in.tgt_ne_init_stopping_point || in.tgt_ne_set_max_speed_accel ||
           in.tgt_ne_set_correction_speed_accel || in.tgt_d_set_max_speed_accel ||
           in.tgt_d_set_correction_speed_accel, in.tgt_handover_seq, OP_GUIDANCE_HANDOVER)
    P_ITEM(in.tgt_valid, in.tgt_update_seq, OP_GUIDANCE_TARGETS)
    P_ITEM(in.lt_cmd_position_NE_soften_for_landing, in.lt_cmd_position_NE_soften_for_landing_seq, OP_LT_SOFTEN)
    P_ITEM(in.lt_tgt_ne_set_correction_speed_accel, in.lt_tgt_handover_seq, OP_LT_CORR)
    P_ITEM(in.lt_cmd_position_NE_set_pos_error_max_m, in.lt_cmd_position_NE_set_pos_error_max_m_seq, OP_LT_ERRMAX)
    P_ITEM(in.lt_tgt_ne_init_stopping_point, in.lt_tgt_handover_seq, OP_LT_INIT_SP)
    P_ITEM(in.lt_cmd_position_set_pos_desired_NE_m, in.lt_cmd_position_set_pos_desired_NE_m_seq,
           OP_LT_SET_POS_DESIRED)
    P_ITEM(in.lt_cmd_position_NE_relax_velocity_controller,
           in.lt_cmd_position_NE_relax_velocity_controller_seq, OP_LT_RELAX)
    P_ITEM(in.lt_tgt_valid || in.lt_tgt_ne_update, in.lt_tgt_update_seq, OP_LT_TARGETS)
    P_ITEM(in.cmd_position_NE_relax_velocity_controller, in.cmd_position_NE_relax_velocity_controller_seq,
           OP_NE_RELAX)
    P_ITEM(in.cmd_position_NE_soften_for_landing, in.cmd_position_NE_soften_for_landing_seq, OP_NE_SOFTEN)
    P_ITEM(in.cmd_position_input_vel_accel_NE_m, in.cmd_position_input_vel_accel_NE_m_seq, OP_INPUT_VEL_ACCEL_NE)
    P_ITEM(in.cmd_position_input_pos_vel_accel_NE_m, in.cmd_position_input_pos_vel_accel_NE_m_seq,
           OP_INPUT_POS_VEL_ACCEL_NE)
    P_ITEM(in.cmd_position_input_pos_NED_m, in.cmd_position_input_pos_NED_m_seq, OP_INPUT_POS_NED)
    P_ITEM(in.cmd_position_NE_stop_vel_stabilisation, in.cmd_position_NE_stop_vel_stabilisation_seq, OP_NE_STOP_VEL)
    P_ITEM(in.cmd_position_NE_stop_pos_stabilisation, in.cmd_position_NE_stop_pos_stabilisation_seq, OP_NE_STOP_POS)
    // the NE update: commanded; in the fixed order also the guidance stage's (see OP_GUIDANCE_TARGETS)
    const int ne_slot = n;
    P_ITEM(true, in.cmd_position_NE_update_controller ? in.cmd_position_NE_update_controller_seq : 0,
           OP_NE_UPDATE)
    P_ITEM(in.cmd_position_D_relax_controller, in.cmd_position_D_relax_controller_seq, OP_D_RELAX)
    P_ITEM(in.cmd_position_D_set_pos_target_from_climb_rate_ms,
           in.cmd_position_D_set_pos_target_from_climb_rate_ms_seq, OP_D_CLIMB_RATE)
    P_ITEM(in.cmd_position_input_pos_vel_accel_D_m, in.cmd_position_input_pos_vel_accel_D_m_seq,
           OP_INPUT_POS_VEL_ACCEL_D)
    P_ITEM(in.cmd_position_input_vel_accel_D_m, in.cmd_position_input_vel_accel_D_m_seq, OP_INPUT_VEL_ACCEL_D)
    P_ITEM(in.cmd_position_D_set_alt_target_with_slew_m, in.cmd_position_D_set_alt_target_with_slew_m_seq,
           OP_D_ALT_SLEW)
    P_ITEM(in.cmd_position_D_update_controller, in.cmd_position_D_update_controller_seq, OP_D_UPDATE)
    // last in the fixed order and only with a `_seq`, so that it moves no other call: a tick in
    // which the supervisor numbers its calls places it by its `_seq` (the same-tick throttle rule,
    // Module.lean `sameTickThrottle`)
    P_ITEM(in.cmd_attitude_set_throttle_out && in.cmd_attitude_set_throttle_out_seq != 0,
           in.cmd_attitude_set_throttle_out_seq, OP_SUPERVISOR_SET_THROTTLE)
#undef P_ITEM
    (void)ne_slot;
    // the NE-update item is a placeholder: it runs only when commanded or (fixed order) pending
    ne_updated = false;
    guidance_ne_pending = false;
    ne_update_last = d_update_last = handover_limits_last = false;
    const bool sequenced = order_items(items, n);
    for (int i = 0; i < n; i++) {
        const int id = items[i].id;
        if (id == OP_NE_UPDATE) {
            if (!(in.cmd_position_NE_update_controller || (!sequenced && guidance_ne_pending))) {
                continue;
            }
        }
        run_op(id, in, sequenced);
        if (id == OP_NE_UPDATE || (sequenced && id == OP_GUIDANCE_TARGETS && !in.tgt_ne_only) ||
            (id == OP_LT_TARGETS && in.lt_tgt_ne_update)) {
            ne_update_last = true;
        } else if (touches_ne(id)) {
            ne_update_last = false;
        }
        if (id == OP_D_UPDATE) {
            d_update_last = true;
        } else if (touches_d(id)) {
            d_update_last = false;
        }
        if (id == OP_GUIDANCE_HANDOVER) {
            handover_limits_last = true;
        } else if (id == OP_NE_SET_MAX || id == OP_D_SET_MAX) {
            handover_limits_last = false;
        }
    }
}

void module_step(const Input &in, Output &out)
{
    // 1. what the controller reads outside itself this tick
    harness_cut.now_ms = in.now_ms;
    harness_cut.pos_n = in.est_pos_n;
    harness_cut.pos_e = in.est_pos_e;
    harness_cut.pos_d = in.est_pos_d;
    // the estimator stage reports one flag for NE and D (get_relative_position_NED_origin)
    harness_cut.pos_ne_valid = in.est_pos_ok;
    harness_cut.pos_d_valid = in.est_pos_ok;
    harness_cut.vel_n = in.est_vel_n;
    harness_cut.vel_e = in.est_vel_e;
    harness_cut.vel_d = in.est_vel_d;
    harness_cut.vel_valid = in.est_vel_ok;
    harness_cut.vert_pos_rate_d = in.est_pos_rate_d;
    harness_cut.vert_pos_rate_valid = in.est_pos_rate_d_ok;
    harness_cut.accel_ef_d = in.est_accel_ef_z;
    harness_cut.yaw = in.est_yaw;
    harness_cut.cos_yaw = in.est_cos_yaw;
    harness_cut.sin_yaw = in.est_sin_yaw;
    harness_cut.gain_scaler_xy = in.est_gain_scaler_xy;
    harness_cut.gain_scaler_z = in.est_gain_scaler_z;
    harness_cut.pos_ne_reset_key = uint16_t(in.est_pos_ne_reset_count);
    harness_cut.pos_d_reset_key = uint16_t(in.est_pos_d_reset_count);
    harness_cut.althold_lean_angle_max_rad = in.ac_althold_lean_angle_max;
    harness_cut.lean_angle_max_rad = in.ac_lean_angle_max;
    harness_cut.throttle_hover = in.throttle_hover;

    AP::scheduler().tick();          // AP_Scheduler::tick, once per main loop
    AP::ahrs().update();             // stand-in: the estimator's results (stubs_ahrs.cpp)
    view->update();                  // stand-in: yaw and its trigonometry
    attitude->load(in.ac_att_target_roll, in.ac_att_target_pitch, in.ac_att_target_yaw,
                   in.ac_throttle_in, in.ac_bf_feedforward);
    motors->limit.throttle_lower = in.limit_throttle_lower;
    motors->limit.throttle_upper = in.limit_throttle_upper;

    // 2. Copter::run_rate_controller_main
    pc->set_dt_s(in.dt);

    // 3.-9.: the calls of this tick, in the fixed order of Module.lean's header, or, when the
    // supervisor numbers them (`_seq`), in its call order (run_ordered)
    run_ordered(in);
    // outputs
    const Vector3f tv = pc->get_thrust_vector();
    out.thrust_vec_x = tv.x;
    out.thrust_vec_y = tv.y;
    out.thrust_vec_z = tv.z;
    out.throttle_in = attitude->throttle_set ? attitude->throttle_arg : 0.0f;
    out.pc_throttle_set = attitude->throttle_set;
    out.pc_throttle_angle_boost = attitude->throttle_set && attitude->angle_boost_arg;
    out.pc_throttle_cutoff_hz = attitude->throttle_set ? attitude->cutoff_arg : 0.0f;

    const Vector3p &pt = pc->get_pos_target_NED_m();
    out.pc_pos_target_n = float(pt.x);
    out.pc_pos_target_e = float(pt.y);
    out.pc_pos_target_d = float(pt.z);
    const Vector3p &pd = pc->get_pos_desired_NED_m();
    out.pc_pos_desired_n = float(pd.x);
    out.pc_pos_desired_e = float(pd.y);
    out.pc_pos_desired_d = float(pd.z);
    const Vector3f &vt = pc->get_vel_target_NED_ms();
    out.pc_vel_target_n = vt.x;
    out.pc_vel_target_e = vt.y;
    out.pc_vel_target_d = vt.z;
    const Vector3f &vd = pc->get_vel_desired_NED_ms();
    out.pc_vel_desired_n = vd.x;
    out.pc_vel_desired_e = vd.y;
    out.pc_vel_desired_d = vd.z;
    const Vector3f &at = pc->get_accel_target_NED_mss();
    out.pc_accel_target_n = at.x;
    out.pc_accel_target_e = at.y;
    out.pc_accel_target_d = at.z;
    const Vector3f &ad = pc->accel_desired();
    out.pc_accel_desired_n = ad.x;
    out.pc_accel_desired_e = ad.y;
    out.pc_accel_desired_d = ad.z;
    const Vector3p &po = pc->get_pos_offset_NED_m();
    out.pc_pos_offset_n = float(po.x);
    out.pc_pos_offset_e = float(po.y);
    out.pc_pos_offset_d = float(po.z);
    const Vector3f &vo = pc->get_vel_offset_NED_ms();
    out.pc_vel_offset_n = vo.x;
    out.pc_vel_offset_e = vo.y;
    out.pc_vel_offset_d = vo.z;
    const Vector3f &ao = pc->get_accel_offset_NED_mss();
    out.pc_accel_offset_n = ao.x;
    out.pc_accel_offset_e = ao.y;
    out.pc_accel_offset_d = ao.z;
    out.pc_pos_terrain_d = pc->get_pos_terrain_D_m();
    out.pc_vel_terrain_d = pc->get_vel_terrain_D_ms();
    const Vector3f pe = pc->get_pos_error_NED_m();
    out.pc_pos_error_n = pe.x;
    out.pc_pos_error_e = pe.y;
    out.pc_pos_error_d = pe.z;
    const Vector3f &lv = pc->limit_vector();
    out.pc_limit_n = lv.x;
    out.pc_limit_e = lv.y;
    out.pc_limit_d = lv.z;
    out.pc_roll = pc->get_roll_rad();
    out.pc_pitch = pc->get_pitch_rad();
    out.pc_yaw = pc->get_yaw_rad();
    out.pc_yaw_rate = pc->get_yaw_rate_rads();
    out.pc_ne_max_speed = pc->NE_get_max_speed_ms();
    out.pc_max_speed_up = pc->get_max_speed_up_ms();
    out.pc_max_speed_down = pc->get_max_speed_down_ms();
    out.pc_ne_max_accel = pc->NE_get_max_accel_mss();
    out.pc_d_max_accel = pc->D_get_max_accel_mss();
    out.pc_jerk_max_ne = pc->jerk_max_ne();
    out.pc_jerk_max_d = pc->jerk_max_d();
    out.pc_pos_error_max_ne = pc->NE_get_pos_error_max_m();
    out.pc_lean_angle_max = pc->lean_angle_max();
    // observer (not ArduPilot state): the tilt of the thrust vector (x, y, -g) from the vertical
    out.pc_lean_angle = accel_mss_to_angle_rad(Vector2f{tv.x, tv.y}.length());
    out.pc_vel_d_control_ratio = pc->get_vel_D_control_ratio();
    Vector2p sp_ne;
    pc->get_stopping_point_NE_m(sp_ne);
    postype_t sp_d;
    pc->get_stopping_point_D_m(sp_d);
    out.pc_stopping_point_n = float(sp_ne.x);
    out.pc_stopping_point_e = float(sp_ne.y);
    out.pc_stopping_point_d = float(sp_d);
    // is_active() as the next tick's mode code reads it, before any call (the scheduler one tick on)
    harness_scheduler_lookahead(true);
    out.pc_ne_active = pc->NE_is_active();
    out.pc_d_active = pc->D_is_active();
    harness_scheduler_lookahead(false);
    out.pc_ne_updated = ne_updated;
    out.pc_ne_update_last = ne_update_last;
    out.pc_d_update_last = d_update_last;
    out.pc_handover_limits_last = handover_limits_last;
    out.pc_throttle_seq = attitude->throttle_set ? in.cmd_position_D_update_controller_seq : 0;
    out.pc_d_updated = in.cmd_position_D_update_controller;
    out.pc_vibe_comp = pc->vibe_comp();
    AC_PID_2D &vne = pc->NE_get_vel_pid();
    const Vector2f vp = vne.get_p(), vi = vne.get_i(), vdd = vne.get_d(), vff = vne.get_ff();
    out.pc_vel_ne_p_n = vp.x;
    out.pc_vel_ne_p_e = vp.y;
    out.pc_vel_ne_i_n = vi.x;
    out.pc_vel_ne_i_e = vi.y;
    out.pc_vel_ne_d_n = vdd.x;
    out.pc_vel_ne_d_e = vdd.y;
    out.pc_vel_ne_ff_n = vff.x;
    out.pc_vel_ne_ff_e = vff.y;
    out.pc_vel_d_i = pc->D_get_vel_pid().get_i();
    AC_PID &acc = pc->D_get_accel_pid();
    const AP_PIDInfo &info = acc.get_pid_info();
    out.pc_accel_d_p = info.P;
    out.pc_accel_d_i = info.I;
    out.pc_accel_d_d = info.D;
    out.pc_accel_d_ff = acc.get_ff();
    out.pc_accel_d_imax = acc.imax();
    out.pc_internal_errors = harness_internal_error_count();
    out.pc_internal_errors_flow = harness_internal_error_flow_count();
    out.pc_internal_error_bits = AP::internalerror().errors();
    out.pc_internal_error_line = AP::internalerror().last_error_line();
}
