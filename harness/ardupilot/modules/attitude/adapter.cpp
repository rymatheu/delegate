// adapter.cpp: the cut between the harness records and ArduCopter's real attitude controller.
//
// The object is a real AC_AttitudeControl_Multi (base AC_AttitudeControl). HarnessAttitude below
// derives from it only to reach protected members and the two protected bookkeeping methods of
// rate_controller_run_dt; it overrides nothing, so every virtual call runs ArduPilot's code.
//
// What the class holds references to, and what stands in (the stubs_*.cpp files say why each
// symbol is outside the stage):
//   AP_AHRS_View &_ahrs   a real AP_AHRS_View (AP_AHRS_View.cpp), built as
//                         AP_AHRS::create_view builds it (ROTATION_NONE, no pitch trim) on an
//                         AP_AHRS stand-in: zeroed storage, never constructed, whose
//                         state.dcm_matrix the adapter sets every step from the estimator's
//                         Euler angles (Matrix3f::from_euler) before the view's real update()
//                         runs (Copter::read_AHRS -> AP_AHRS::update -> AP_AHRS_View::update).
//   AP_Motors &_motors    a real AP_MotorsMatrix, constructed (400 Hz) but never initialised
//                         or output; HarnessMotors writes into it, every step, the throttle
//                         state the mixer module reported (hover, filtered throttle,
//                         throttle_out, slew rate, thrust ceiling), and the outputs read back
//                         what the attitude controller set (set_throttle, set_throttle_avg_max,
//                         set_throttle_filter_cutoff).
//   the rate PIDs         _pid_rate_roll/pitch/yaw are real AC_PID members of the class. The
//                         rate controller itself is the `rate` stage; here they are stand-ins:
//                         only the yaw P gain is read (thrust_heading_rotation_angles), and what
//                         the commands do to them (reset_I, relax_integrator, reset_filter) is
//                         reported to the rate stage as the outputs ac_rate_*. To observe it,
//                         each step sets every integrator to the sentinel 1 and clears the
//                         filter-reset flag before the commands: an integrator of 0 afterwards
//                         means reset_I, any other value but 1 means relax_integrator (with
//                         dt > 0 it moves 1 by at least 7e-7).
//
// One step, in the order of ArduCopter's fast loop (Copter.cpp scheduler table) for one tick k:
//   1. Copter::run_rate_controller_main: attitude_control->set_dt_s(dt)
//   2. AC_AttitudeControl_Multi::rate_controller_run_dt, the attitude stage's share:
//      _rate_gyro_rads = gyro; update_throttle_rpy_mix() with the motors stand-in still holding
//      the mixer's output of the previous tick (motors_output runs after the rate controller).
//      update_throttle_gain_boost() also belongs here; see 7.
//   3. Copter::motors_output: the motors stand-in takes the mixer's output of this tick.
//   4. Copter::read_AHRS: the AHRS stand-in and the real view update.
//   5. Copter::check_ekf_reset, Copter::update_flight_mode and the mode's calls (the commands, in
//      the order Module.lean gives), then Copter::update_throttle_mix (throttle_loop).
//   6. Outputs: the rate targets, the motors' throttle, the controller's state.
//   7. The start of tick k+1's rate_controller_run_dt, whose result the rate PIDs use at k+1:
//      update_throttle_gain_boost() (reads the motors' slew rate after output k, which the
//      stand-in holds), then _pd_scale and _i_scale are output, then
//      Copter::run_rate_controller_main's rate_controller_target_reset() (scales back to 1,
//      sysid offsets 0).
// The first step's stand-in holds this tick's mixer values already at 2 (there is no previous
// output).
#include "module_protocol.h"

#include <new>
#include <string.h>

#include <AC_AttitudeControl/AC_AttitudeControl_Multi.h>
#include <AC_AttitudeControl/AC_PosControl.h>   // (POSCONTROL_ constants; the cutoff now comes in)
#include <AP_Motors/AP_MotorsMatrix.h>
#include <AP_AHRS/AP_AHRS_View.h>

// the cut, defined in the stubs
void harness_reset_internal_errors();
uint32_t harness_internal_error_count();
void harness_reset_cut();
AP_AHRS &harness_ahrs_storage();
void harness_set_ahrs_dcm(const Matrix3f &m);

// --- access to members the class keeps private or protected, for the stand-ins only. Access is
// not checked in an explicit instantiation's template arguments.
void harness_clear_matrix_singleton();
template <AP_MotorsMatrix **P>
struct MatrixSingleton {
    friend void harness_clear_matrix_singleton() { *P = nullptr; }
};
template struct MatrixSingleton<&AP_MotorsMatrix::_singleton>;

float &harness_pid_integrator(AC_PID &pid);
template <typename T, T M>
struct PidIntegrator {
    friend float &harness_pid_integrator(AC_PID &pid) { return pid.*M; }
};
template struct PidIntegrator<decltype(&AC_PID::_integrator), &AC_PID::_integrator>;

bool harness_pid_reset_filter_flag(AC_PID &pid);
void harness_pid_clear_reset_filter(AC_PID &pid);
template <typename T, T M>
struct PidFlags {
    friend bool harness_pid_reset_filter_flag(AC_PID &pid) { return (pid.*M)._reset_filter; }
    friend void harness_pid_clear_reset_filter(AC_PID &pid) { (pid.*M)._reset_filter = false; }
};
template struct PidFlags<decltype(&AC_PID::_flags), &AC_PID::_flags>;

// --- the motors stand-in
class HarnessMotors : public AP_MotorsMatrix {
public:
    // SCHED_LOOP_RATE default, as Copter::allocate_motors
    HarnessMotors() : AP_MotorsMatrix(400) {}

    // the mixer's state after its output of a tick, as the attitude controller reads it
    void take_mixer_output(const Input &in)
    {
        _throttle_hover.set(in.throttle_hover);          // get_throttle_hover() constrains it
        _throttle_filter.reset(in.throttle_filtered);    // get_throttle(): constrained to [0, 1]
        _throttle_out = in.throttle_out;                 // get_throttle_out()
        _throttle_slew_rate = in.throttle_slew_rate;     // get_throttle_slew_rate()
        _throttle_thrust_max = in.throttle_thrust_max;   // get_throttle_thrust_max()
    }
    float throttle_filter_cutoff() const { return _throttle_filter.get_cutoff_freq(); }
    // AP_MotorsMulticopter::get_throttle_avg_max() is compiled only for APM_BUILD_UNKNOWN
    float throttle_avg_max() const { return _throttle_avg_max; }
};

// --- the attitude controller, with access to its protected members
class HarnessAttitude : public AC_AttitudeControl_Multi {
public:
    HarnessAttitude(AP_AHRS_View &ahrs, AP_MotorsMulticopter &motors) :
        AC_AttitudeControl_Multi(ahrs, motors) {}

    // as the parameter system stores each value (AP_Param::set, no constraint)
    void set_params(const Params &p)
    {
        _rate_bf_ff_enabled.set(p.atc_rate_ff_enab ? 1 : 0);
        _angle_boost_enabled.set(p.atc_angle_boost ? 1 : 0);
        _p_angle_roll.kP().set(p.atc_ang_rll_p);
        _p_angle_pitch.kP().set(p.atc_ang_pit_p);
        _p_angle_yaw.kP().set(p.atc_ang_yaw_p);
        _angle_limit_tc.set(p.atc_ang_lim_tc);
        _ang_vel_roll_max_degs.set(p.atc_rate_r_max);
        _ang_vel_pitch_max_degs.set(p.atc_rate_p_max);
        _ang_vel_yaw_max_degs.set(p.atc_rate_y_max);
        _input_tc.set(p.atc_input_tc);
        _land_roll_mult.set(p.atc_land_r_mult);
        _land_pitch_mult.set(p.atc_land_p_mult);
        _land_yaw_mult.set(p.atc_land_y_mult);
        _angle_max_deg.set(p.atc_angle_max);
        _rate_wp_yaw_max_degs.set(p.atc_rate_wpy_max);
        _accel_yaw_max_degss.set(p.atc_acc_y_max);
        _accel_roll_max_degss.set(p.atc_acc_r_max);
        _accel_pitch_max_degss.set(p.atc_acc_p_max);
        _thr_mix_min.set(p.atc_thr_mix_min);
        _thr_mix_max.set(p.atc_thr_mix_max);
        _thr_mix_man.set(p.atc_thr_mix_man);
        _throttle_gain_boost.set(p.atc_thr_g_boost);
        // the rate PIDs' parameters the attitude controller reads: the yaw P gain only
        _pid_rate_yaw.kP().set(p.yaw_kp);
    }

    // rate_controller_run_dt's share (AC_AttitudeControl_Multi.cpp)
    void take_rate_gyro(const Vector3f &gyro) { _rate_gyro_rads = gyro; }
    void throttle_rpy_mix() { update_throttle_rpy_mix(); }
    void throttle_gain_boost() { update_throttle_gain_boost(); }

    const Vector3f &pd_scale() const { return _pd_scale; }
    const Vector3f &i_scale() const { return _i_scale; }
    const Vector3f &ang_accel_target() const { return _ang_accel_target_rads; }
    const Quaternion &att_error() const { return _attitude_ang_error; }
    float thrust_error_angle() const { return _thrust_error_angle_rad; }
    float feedforward_scalar() const { return _feedforward_scalar; }
};

// ArduCopter allocates these with NEW_NOTHROW, whose memory ArduPilot zeroes (AP_Common/c++.cpp)
alignas(HarnessMotors) static unsigned char motors_storage[sizeof(HarnessMotors)];
alignas(AP_AHRS_View) static unsigned char view_storage[sizeof(AP_AHRS_View)];
alignas(HarnessAttitude) static unsigned char attitude_storage[sizeof(HarnessAttitude)];
static HarnessMotors *motors;
static AP_AHRS_View *view;
static HarnessAttitude *ac;
static bool first_step;

void module_init(const Params &p)
{
    memset(motors_storage, 0, sizeof motors_storage);
    memset(view_storage, 0, sizeof view_storage);
    memset(attitude_storage, 0, sizeof attitude_storage);
    harness_reset_internal_errors();
    harness_reset_cut();   // AHRS stand-in zeroed, scheduler loop rate 400 Hz
    harness_clear_matrix_singleton();
    // Copter::allocate_motors: the motors, the AHRS view, the attitude controller
    motors = new (motors_storage) HarnessMotors();
    view = new (view_storage) AP_AHRS_View(harness_ahrs_storage(), ROTATION_NONE);
    ac = new (attitude_storage) HarnessAttitude(*view, *motors);
    // AP_Param::load_object_from_eeprom (cut): the parameter record
    ac->set_params(p);
    // Copter::init_ardupilot
    ac->parameter_sanity_check();
    first_step = true;
}

// the sentinel on the rate-PID stand-ins (see the header)
static AC_PID *rate_pid(int i)
{
    return i == 0 ? &ac->get_rate_roll_pid() : (i == 1 ? &ac->get_rate_pitch_pid()
                                                        : &ac->get_rate_yaw_pid());
}

static void arm_rate_pid_probe()
{
    for (int i = 0; i < 3; i++) {
        harness_pid_integrator(*rate_pid(i)) = 1.0f;
        harness_pid_clear_reset_filter(*rate_pid(i));
    }
}

// the position controller's call: AC_PosControl::D_update_controller (AC_PosControl.cpp),
// with the arguments the position stage reports it passed
static void pos_throttle(const Input &in)
{
    if (in.pc_throttle_set) {
        ac->set_throttle_out(in.throttle_in, in.pc_throttle_angle_boost, in.pc_throttle_cutoff_hz);
    }
}

// the mode's own call (Stabilize, zero_throttle_and_relax_ac, takeoff)
static void mode_throttle(const Input &in)
{
    if (in.cmd_attitude_set_throttle_out) {
        ac->set_throttle_out(in.cmd_attitude_set_throttle_out_throttle_in,
                             in.cmd_attitude_set_throttle_out_apply_angle_boost,
                             in.cmd_attitude_set_throttle_out_filter_cutoff);
    }
}

// --- the calls of a tick, one id each, in the fixed order (Module.lean's header)
enum OpId {
    OP_SET_YAW_RATE_TC, OP_SET_RP_RATE_TC, OP_INERTIAL_FRAME_RESET, OP_LANDED_GAIN_REDUCTION,
    OP_RELAX, OP_RESET_TARGET, OP_RESET_YAW_TARGET, OP_RESET_I, OP_RESET_I_SMOOTHLY,
    OP_POS_THROTTLE_BEFORE, OP_MODE_THROTTLE_BEFORE,
    OP_INPUT_EULER_RATE_YAW, OP_INPUT_EULER_YAW, OP_INPUT_RATE_BF, OP_INPUT_TV_RATE_HEADING,
    OP_INPUT_TV_HEADING,
    OP_POS_THROTTLE_AFTER, OP_MODE_THROTTLE_AFTER,
    OP_MIX_MIN, OP_MIX_MAN, OP_MIX_MAX, OP_RATE_TARGET_RESET, OP_COUNT
};

struct SeqItem { uint32_t seq; int id; };

static bool input_last;

// All `_seq` 0: the fixed order. Otherwise by `_seq`; a set call with `_seq` 0 takes the largest
// `_seq` of the calls before it in the fixed order, ties keep the fixed order.
static void order_items(SeqItem *it, int n)
{
    bool any = false;
    for (int i = 0; i < n; i++) {
        any = any || it[i].seq != 0;
    }
    if (!any) {
        return;
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
    for (int i = 1; i < n; i++) {
        SeqItem x = it[i];
        int j = i - 1;
        while (j >= 0 && it[j].seq > x.seq) {
            it[j + 1] = it[j];
            j--;
        }
        it[j + 1] = x;
    }
}

static void run_op(int id, const Input &in, const Vector3f &thrust_vec)
{
    switch (id) {
    // Copter::set_mode
    case OP_SET_YAW_RATE_TC: ac->set_yaw_rate_tc(in.cmd_attitude_set_yaw_rate_tc_input_tc); break;
    case OP_SET_RP_RATE_TC:
        ac->set_roll_pitch_rate_tc(in.cmd_attitude_set_roll_pitch_rate_tc_input_tc);
        break;
    // Copter::check_ekf_reset
    case OP_INERTIAL_FRAME_RESET: ac->inertial_frame_reset(); break;
    // Copter::update_flight_mode
    case OP_LANDED_GAIN_REDUCTION:
        ac->landed_gain_reduction(in.cmd_attitude_landed_gain_reduction_landed);
        break;
    // flightmode->run(): resets first, then the throttle and input calls
    case OP_RELAX: ac->relax_attitude_controllers(); break;
    case OP_RESET_TARGET: ac->reset_target_and_rate(in.cmd_attitude_reset_target_and_rate_reset_rate); break;
    case OP_RESET_YAW_TARGET:
        ac->reset_yaw_target_and_rate(in.cmd_attitude_reset_yaw_target_and_rate_reset_rate);
        break;
    case OP_RESET_I: ac->reset_rate_controller_I_terms(); break;
    case OP_RESET_I_SMOOTHLY: ac->reset_rate_controller_I_terms_smoothly(); break;
    case OP_POS_THROTTLE_BEFORE:
    case OP_POS_THROTTLE_AFTER:
        pos_throttle(in);
        break;
    case OP_MODE_THROTTLE_BEFORE:
    case OP_MODE_THROTTLE_AFTER:
        mode_throttle(in);
        break;
    case OP_INPUT_EULER_RATE_YAW:
        ac->input_euler_angle_roll_pitch_euler_rate_yaw_rad(
            in.cmd_attitude_input_euler_angle_roll_pitch_euler_rate_yaw_roll,
            in.cmd_attitude_input_euler_angle_roll_pitch_euler_rate_yaw_pitch,
            in.cmd_attitude_input_euler_angle_roll_pitch_euler_rate_yaw_yaw_rate);
        break;
    case OP_INPUT_EULER_YAW:
        ac->input_euler_angle_roll_pitch_yaw_rad(
            in.cmd_attitude_input_euler_angle_roll_pitch_yaw_roll,
            in.cmd_attitude_input_euler_angle_roll_pitch_yaw_pitch,
            in.cmd_attitude_input_euler_angle_roll_pitch_yaw_yaw,
            in.cmd_attitude_input_euler_angle_roll_pitch_yaw_slew_yaw);
        break;
    case OP_INPUT_RATE_BF:
        ac->input_rate_bf_roll_pitch_yaw_rads(
            in.cmd_attitude_input_rate_bf_roll_pitch_yaw_roll_rate,
            in.cmd_attitude_input_rate_bf_roll_pitch_yaw_pitch_rate,
            in.cmd_attitude_input_rate_bf_roll_pitch_yaw_yaw_rate);
        break;
    case OP_INPUT_TV_RATE_HEADING:
        ac->input_thrust_vector_rate_heading_rads(
            thrust_vec, in.cmd_attitude_input_thrust_vector_rate_heading_heading_rate,
            in.cmd_attitude_input_thrust_vector_rate_heading_slew_yaw);
        break;
    case OP_INPUT_TV_HEADING: {
        AC_AttitudeControl::HeadingCommand heading;
        heading.yaw_angle_rad = in.cmd_attitude_input_thrust_vector_heading_yaw_angle;
        heading.yaw_rate_rads = in.cmd_attitude_input_thrust_vector_heading_yaw_rate;
        switch (in.cmd_attitude_input_thrust_vector_heading_heading_mode) {
        case 0: heading.heading_mode = AC_AttitudeControl::HeadingMode::Angle_Only; break;
        case 1: heading.heading_mode = AC_AttitudeControl::HeadingMode::Angle_And_Rate; break;
        default: heading.heading_mode = AC_AttitudeControl::HeadingMode::Rate_Only; break;
        }
        ac->input_thrust_vector_heading(thrust_vec, heading);
        break;
    }
    // Copter::update_throttle_mix
    case OP_MIX_MIN: ac->set_throttle_mix_min(); break;
    case OP_MIX_MAN: ac->set_throttle_mix_man(); break;
    case OP_MIX_MAX: ac->set_throttle_mix_max(in.cmd_attitude_set_throttle_mix_max_ratio); break;
    // Copter::run_rate_controller_main's rate_controller_target_reset (Attitude.cpp:23): the
    // step makes it itself, after the next tick's rate-controller share (step 7), which is where
    // ArduCopter makes it; the command is accepted and has no further effect
    case OP_RATE_TARGET_RESET: break;
    default: break;
    }
}

static void run_ordered(const Input &in, const Vector3f &thrust_vec)
{
#define A_ITEM(flag, seqv, opid) if (flag) { items[n].seq = (seqv); items[n].id = (opid); n++; }
    SeqItem items[OP_COUNT];
    int n = 0;
    A_ITEM(in.cmd_attitude_set_yaw_rate_tc, in.cmd_attitude_set_yaw_rate_tc_seq, OP_SET_YAW_RATE_TC)
    A_ITEM(in.cmd_attitude_set_roll_pitch_rate_tc, in.cmd_attitude_set_roll_pitch_rate_tc_seq, OP_SET_RP_RATE_TC)
    A_ITEM(in.cmd_attitude_inertial_frame_reset, in.cmd_attitude_inertial_frame_reset_seq, OP_INERTIAL_FRAME_RESET)
    A_ITEM(in.cmd_attitude_landed_gain_reduction, in.cmd_attitude_landed_gain_reduction_seq,
           OP_LANDED_GAIN_REDUCTION)
    A_ITEM(in.cmd_attitude_relax_attitude_controllers, in.cmd_attitude_relax_attitude_controllers_seq, OP_RELAX)
    A_ITEM(in.cmd_attitude_reset_target_and_rate, in.cmd_attitude_reset_target_and_rate_seq, OP_RESET_TARGET)
    A_ITEM(in.cmd_attitude_reset_yaw_target_and_rate, in.cmd_attitude_reset_yaw_target_and_rate_seq,
           OP_RESET_YAW_TARGET)
    A_ITEM(in.cmd_attitude_reset_rate_controller_I_terms, in.cmd_attitude_reset_rate_controller_I_terms_seq,
           OP_RESET_I)
    A_ITEM(in.cmd_attitude_reset_rate_controller_I_terms_smoothly,
           in.cmd_attitude_reset_rate_controller_I_terms_smoothly_seq, OP_RESET_I_SMOOTHLY)
    // the order flags place the two set_throttle_out calls in the fixed order only
    A_ITEM(in.pc_throttle_set && !in.cmd_attitude_pos_throttle_after_input, in.pc_throttle_seq,
           OP_POS_THROTTLE_BEFORE)
    A_ITEM(in.cmd_attitude_set_throttle_out && in.cmd_attitude_set_throttle_out_before_input,
           in.cmd_attitude_set_throttle_out_seq, OP_MODE_THROTTLE_BEFORE)
    A_ITEM(in.cmd_attitude_input_euler_angle_roll_pitch_euler_rate_yaw,
           in.cmd_attitude_input_euler_angle_roll_pitch_euler_rate_yaw_seq, OP_INPUT_EULER_RATE_YAW)
    A_ITEM(in.cmd_attitude_input_euler_angle_roll_pitch_yaw, in.cmd_attitude_input_euler_angle_roll_pitch_yaw_seq,
           OP_INPUT_EULER_YAW)
    A_ITEM(in.cmd_attitude_input_rate_bf_roll_pitch_yaw, in.cmd_attitude_input_rate_bf_roll_pitch_yaw_seq,
           OP_INPUT_RATE_BF)
    A_ITEM(in.cmd_attitude_input_thrust_vector_rate_heading,
           in.cmd_attitude_input_thrust_vector_rate_heading_seq, OP_INPUT_TV_RATE_HEADING)
    A_ITEM(in.cmd_attitude_input_thrust_vector_heading, in.cmd_attitude_input_thrust_vector_heading_seq,
           OP_INPUT_TV_HEADING)
    A_ITEM(in.pc_throttle_set && in.cmd_attitude_pos_throttle_after_input, in.pc_throttle_seq,
           OP_POS_THROTTLE_AFTER)
    A_ITEM(in.cmd_attitude_set_throttle_out && !in.cmd_attitude_set_throttle_out_before_input,
           in.cmd_attitude_set_throttle_out_seq, OP_MODE_THROTTLE_AFTER)
    A_ITEM(in.cmd_attitude_set_throttle_mix_min, in.cmd_attitude_set_throttle_mix_min_seq, OP_MIX_MIN)
    A_ITEM(in.cmd_attitude_set_throttle_mix_man, in.cmd_attitude_set_throttle_mix_man_seq, OP_MIX_MAN)
    A_ITEM(in.cmd_attitude_set_throttle_mix_max, in.cmd_attitude_set_throttle_mix_max_seq, OP_MIX_MAX)
    A_ITEM(in.cmd_attitude_rate_controller_target_reset, in.cmd_attitude_rate_controller_target_reset_seq,
           OP_RATE_TARGET_RESET)
#undef A_ITEM
    order_items(items, n);
    input_last = false;
    for (int i = 0; i < n; i++) {
        const int id = items[i].id;
        run_op(id, in, thrust_vec);
        // an input method was the last call that set the attitude target and its rates
        if (id >= OP_INPUT_EULER_RATE_YAW && id <= OP_INPUT_TV_HEADING) {
            input_last = true;
        } else if (id == OP_INERTIAL_FRAME_RESET || id == OP_RELAX || id == OP_RESET_TARGET ||
                   id == OP_RESET_YAW_TARGET) {
            input_last = false;
        }
    }
}

void module_step(const Input &in, Output &out)
{
    // 1. Copter::run_rate_controller_main
    ac->set_dt_s(in.dt);

    // 2. rate_controller_run_dt's share; the motors stand-in holds the previous tick's output
    if (first_step) {
        motors->take_mixer_output(in);
        first_step = false;
    }
    ac->take_rate_gyro(Vector3f{in.gyro_x, in.gyro_y, in.gyro_z});
    ac->throttle_rpy_mix();

    // 3. Copter::motors_output: the mixer's output of this tick
    motors->take_mixer_output(in);

    // 4. Copter::read_AHRS
    Matrix3f dcm;
    dcm.from_euler(in.est_roll, in.est_pitch, in.est_yaw);
    harness_set_ahrs_dcm(dcm);
    view->update();

    // 5. the calls of this tick
    arm_rate_pid_probe();
    const Vector3f thrust_vec{in.thrust_vec_x, in.thrust_vec_y, in.thrust_vec_z};
    // the calls of this tick, in the fixed order of Module.lean's header, or, when the
    // supervisor numbers them (`_seq`), in its call order
    run_ordered(in, thrust_vec);

    // 6. outputs
    const Vector3f target = ac->rate_bf_targets();
    out.target_x = target.x;
    out.target_y = target.y;
    out.target_z = target.z;
    out.throttle = motors->get_throttle_in();
    out.throttle_avg_max = motors->throttle_avg_max();
    out.throttle_filter_hz = motors->throttle_filter_cutoff();
    const Quaternion q = ac->get_attitude_target_quat();
    out.ac_att_target_q1 = q.q1;
    out.ac_att_target_q2 = q.q2;
    out.ac_att_target_q3 = q.q3;
    out.ac_att_target_q4 = q.q4;
    const Vector3f &euler = ac->get_att_target_euler_rad();
    out.ac_att_target_roll = euler.x;
    out.ac_att_target_pitch = euler.y;
    out.ac_att_target_yaw = euler.z;
    const Vector3f &ang_vel = ac->get_attitude_target_ang_vel();
    out.ac_ang_vel_target_x = ang_vel.x;
    out.ac_ang_vel_target_y = ang_vel.y;
    out.ac_ang_vel_target_z = ang_vel.z;
    const Vector3f &ang_accel = ac->ang_accel_target();
    out.ac_ang_accel_target_x = ang_accel.x;
    out.ac_ang_accel_target_y = ang_accel.y;
    out.ac_ang_accel_target_z = ang_accel.z;
    const Vector3f &rate_ef = ac->get_rate_ef_target_rads();
    out.ac_rate_ef_target_x = rate_ef.x;
    out.ac_rate_ef_target_y = rate_ef.y;
    out.ac_rate_ef_target_z = rate_ef.z;
    const Quaternion &err = ac->att_error();
    out.ac_att_error_q1 = err.q1;
    out.ac_att_error_q2 = err.q2;
    out.ac_att_error_q3 = err.q3;
    out.ac_att_error_q4 = err.q4;
    out.ac_thrust_error_angle = ac->thrust_error_angle();
    out.ac_lean_angle = ac->lean_angle_rad();
    out.ac_lean_angle_max = ac->lean_angle_max_rad();
    out.ac_althold_lean_angle_max = ac->get_althold_lean_angle_max_rad();
    out.ac_angle_boost = ac->angle_boost();
    out.ac_throttle_in = ac->get_throttle_in();
    out.ac_throttle_mix = ac->get_throttle_mix();
    out.ac_throttle_mix_min = ac->is_throttle_mix_min();
    out.ac_slew_yaw_max = ac->get_slew_yaw_max_rads();
    out.ac_feedforward_scalar = ac->feedforward_scalar();
    // the rate-PID probe (the three PIDs are always reset together; the roll PID is read)
    const float i_after = harness_pid_integrator(*rate_pid(0));
    out.ac_rate_reset_i = (i_after == 0.0f);
    out.ac_rate_relax_i = (i_after != 0.0f && i_after != 1.0f);
    out.ac_rate_reset_filter = harness_pid_reset_filter_flag(*rate_pid(0));
    out.ac_bf_feedforward = ac->get_bf_feedforward();
    out.ac_input_last = input_last;

    // 7. the start of the next tick's rate_controller_run_dt, then rate_controller_target_reset
    ac->throttle_gain_boost();
    out.pd_scale_x = ac->pd_scale().x;
    out.pd_scale_y = ac->pd_scale().y;
    out.pd_scale_z = ac->pd_scale().z;
    out.i_scale_x = ac->i_scale().x;
    out.i_scale_y = ac->i_scale().y;
    out.i_scale_z = ac->i_scale().z;
    ac->rate_controller_target_reset();

    out.ac_internal_errors = harness_internal_error_count();
}
