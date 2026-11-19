// adapter.cpp: the cut between the harness records and ArduCopter's real loiter controller.
//
// The object is a real AC_Loiter (libraries/AC_WPNav/AC_Loiter.cpp). HarnessLoiter derives from it
// only to reach protected members (parameters, state for the outputs); it overrides nothing
// (AC_Loiter has no virtual methods).
//
// init (Copter::allocate_motors, system.cpp:499-503): ArduCopter allocates the controller with
// NEW_NOTHROW, whose memory ArduPilot zeroes (AP_Common/c++.cpp), and loads its parameters from
// EEPROM; here it is built in zeroed storage and every AP_Param member is set from the parameter
// record. Copter::init_ardupilot's loiter_nav->convert_parameters() (system.cpp:557) converts
// pre-4.7 parameters stored in EEPROM; with nothing stored it changes nothing, and it is not called.
//
// The other stages' objects AC_Loiter holds references to (cut.h):
//   position controller  zeroed storage, members loaded from the position stage's outputs of the
//                        previous tick; out-of-line methods are the hand-over stand-ins
//                        (stubs_posctl.cpp); lean_angles_rad_to_accel_NED_mss is the real one
//                        (pos_real.cpp).
//   attitude controller  zeroed storage, members loaded from the parameter record (ATC_*, the
//                        attitude stage's names) and its dt from the input dt; the functions
//                        AC_Loiter calls on it are real (AC_AttitudeControl.cpp):
//                        command_model_rate_predictor (with attitude_command_model and
//                        ang_vel_limit) and lean_angle_max_rad. The predictor reads, with
//                        ATC_RATE_FF_ENAB off, the angle P gains times _angle_P_scale, the attitude
//                        stage's scale of this tick (landed_gain_reduction, mode.cpp:507, runs
//                        before the mode): set to (1, 1, 1), what rate_controller_target_reset
//                        leaves (AC_AttitudeControl.cpp:295); the contract assumes ATC_RATE_FF_ENAB
//                        on (`rate_ff_enabled`), where the scale is not read.
//   AHRS view            zeroed storage, member yaw = est_yaw (AP_AHRS_View::update runs in
//                        Copter::read_AHRS, before the mode, AP_AHRS_View.cpp:61).
//
// What is left of the position and attitude controllers' code in the executable (`nm` after the
// linker's dead-strip, recorded with the build): AC_PosControl_Real::lean_angles_rad_to_accel_NED_mss;
// AC_AttitudeControl::command_model_rate_predictor, attitude_command_model, ang_vel_limit,
// lean_angle_max_rad.
//
// step:
//   1. the signals: the clock, the AHRS (ground-speed limit), the view's yaw, the position
//      controller's members (pc_ inputs), the attitude controller's dt; the recorded calls cleared
//   2. the commands that are set, in the fixed order below (the order of ArduCopter's mode code in
//      one tick: ModeLoiter::run, mode_loiter.cpp:84-161) or, when the supervisor numbers them
//      (`_seq`), in its call order
//   3. the outputs: the recorded calls (lt_tgt_..., lt_cmd_position_...), the controller's state
//      (lt_...)
//
// set_pos_desired_NE_m is an inline setter (AC_PosControl.h:322): AC_Loiter::init_target_m writes
// the position controller's _pos_desired_ned_m.xy() directly (AC_Loiter.cpp:131). The adapter
// sees the write with a sentinel: before each command except update it sets that member to NaN,
// and after it a value that is not NaN is the call's argument (recorded, and kept as the member's
// value, which is the setter's own effect); otherwise the loaded value is restored. update reads
// the member (AC_Loiter.cpp:393) and does not call the setter (AC_Loiter.cpp:247-254, 320-400), so
// it runs without the sentinel.
#include "module_protocol.h"

#include <math.h>
#include <new>
#include <string.h>

#include "cut.h"

#include <AC_WPNav/AC_Loiter.h>

void harness_reset_cut();

// --- members of the other stages' objects that the module loads (cut.h, HARNESS_MEMBER)
HARNESS_MEMBER(PcDt, AC_PosControl, float, _dt_s);
HARNESS_MEMBER(PcPosDesired, AC_PosControl, Vector3p, _pos_desired_ned_m);
HARNESS_MEMBER(PcVelDesired, AC_PosControl, Vector3f, _vel_desired_ned_ms);
HARNESS_MEMBER(PcAccelTarget, AC_PosControl, Vector3f, _accel_target_ned_mss);
HARNESS_MEMBER(PcRollTarget, AC_PosControl, float, _roll_target_rad);
HARNESS_MEMBER(PcPitchTarget, AC_PosControl, float, _pitch_target_rad);
HARNESS_MEMBER(PcVelPidNE, AC_PosControl, AC_PID_2D, _pid_vel_ne_m);
HARNESS_MEMBER(AcRateFF, AC_AttitudeControl, AP_Int8, _rate_bf_ff_enabled);
HARNESS_MEMBER(AcRateRollMax, AC_AttitudeControl, AP_Float, _ang_vel_roll_max_degs);
HARNESS_MEMBER(AcRatePitchMax, AC_AttitudeControl, AP_Float, _ang_vel_pitch_max_degs);
HARNESS_MEMBER(AcAccelRollMax, AC_AttitudeControl, AP_Float, _accel_roll_max_degss);
HARNESS_MEMBER(AcAccelPitchMax, AC_AttitudeControl, AP_Float, _accel_pitch_max_degss);
HARNESS_MEMBER(AcInputTC, AC_AttitudeControl, AP_Float, _input_tc);
HARNESS_MEMBER(AcAngleMax, AC_AttitudeControl, AP_Float, _angle_max_deg);

class HarnessLoiter : public AC_Loiter {
public:
    HarnessLoiter(const AP_AHRS_View &ahrs, AC_PosControl &pos_control, const AC_AttitudeControl &att) :
        AC_Loiter(ahrs, pos_control, att) {}

    // as the parameter system stores each value (AP_Param::set, no constraint)
    void set_params(const Params &p)
    {
        _angle_max_deg.set(p.loit_ang_max);
        _speed_max_ne_ms.set(p.loit_speed_ms);
        _accel_max_ne_mss.set(p.loit_acc_max_m);
        _brake_accel_max_mss.set(p.loit_brk_acc_m);
        _brake_jerk_max_msss.set(p.loit_brk_jrk_m);
        _brake_delay_s.set(p.loit_brk_delay);
        _options.set(uint8_t(p.loit_options));
    }

    const Vector2f &predicted_accel() const { return _predicted_accel_ne_mss; }
    const Vector2f &predicted_angle() const { return _predicted_euler_angle_rad; }
    const Vector2f &predicted_rate() const { return _predicted_euler_rate; }
    const Vector2f &predicted_ang_accel() const { return _predicted_euler_accel; }
    uint32_t brake_timer_ms() const { return _brake_timer_ms; }
    float brake_accel() const { return _brake_accel_mss; }
    float speed_max() const { return _speed_max_ne_ms; }
    float accel_max() const { return _accel_max_ne_mss; }
};

// ArduCopter's objects come from NEW_NOTHROW, whose memory ArduPilot zeroes (AP_Common/c++.cpp)
alignas(HarnessLoiter) static unsigned char loiter_storage[sizeof(HarnessLoiter)];
alignas(AC_PosControl) static unsigned char posctl_storage[sizeof(AC_PosControl)];
alignas(AC_AttitudeControl) static unsigned char attctl_storage[sizeof(AC_AttitudeControl)];
alignas(AP_AHRS_View) static unsigned char ahrs_view_storage[sizeof(AP_AHRS_View)];
static HarnessLoiter *loiter;

static AC_PosControl &posctl() { return *reinterpret_cast<AC_PosControl *>(posctl_storage); }
static AC_AttitudeControl &attctl() { return *reinterpret_cast<AC_AttitudeControl *>(attctl_storage); }
static AP_AHRS_View &ahrs_view() { return *reinterpret_cast<AP_AHRS_View *>(ahrs_view_storage); }

void module_init(const Params &p)
{
    memset(loiter_storage, 0, sizeof loiter_storage);
    memset(posctl_storage, 0, sizeof posctl_storage);
    memset(attctl_storage, 0, sizeof attctl_storage);
    memset(ahrs_view_storage, 0, sizeof ahrs_view_storage);
    harness_reset_internal_errors();
    harness_reset_cut();

    AC_PosControl &pc = posctl();
    (pc.*member_ptr(PcVelPidNE())).kP().set(p.psc_ne_vel_p);
    AC_AttitudeControl &ac = attctl();
    (ac.*member_ptr(AcRateFF())).set(p.atc_rate_ff_enab ? 1 : 0);
    (ac.*member_ptr(AcRateRollMax())).set(p.atc_rate_r_max);
    (ac.*member_ptr(AcRatePitchMax())).set(p.atc_rate_p_max);
    (ac.*member_ptr(AcAccelRollMax())).set(p.atc_acc_r_max);
    (ac.*member_ptr(AcAccelPitchMax())).set(p.atc_acc_p_max);
    (ac.*member_ptr(AcInputTC())).set(p.atc_input_tc);
    (ac.*member_ptr(AcAngleMax())).set(p.atc_angle_max);
    ac.get_angle_roll_p().kP().set(p.atc_ang_rll_p);
    ac.get_angle_pitch_p().kP().set(p.atc_ang_pit_p);
    ac.set_angle_P_scale(Vector3f{1.0f, 1.0f, 1.0f});

    loiter = new (loiter_storage) HarnessLoiter(ahrs_view(), pc, ac);
    loiter->set_params(p);
}

// the position controller's members, as the position stage left them after the previous tick
static void load_position_controller(const Input &in)
{
    AC_PosControl &pc = posctl();
    pc.*member_ptr(PcDt()) = in.dt;
    pc.*member_ptr(PcPosDesired()) = Vector3p{in.pc_pos_desired_n, in.pc_pos_desired_e, 0.0};
    pc.*member_ptr(PcVelDesired()) = Vector3f{in.pc_vel_desired_n, in.pc_vel_desired_e, 0.0f};
    pc.*member_ptr(PcAccelTarget()) = Vector3f{in.pc_accel_target_n, in.pc_accel_target_e, 0.0f};
    pc.*member_ptr(PcRollTarget()) = in.pc_roll;
    pc.*member_ptr(PcPitchTarget()) = in.pc_pitch;
    harness_pc_stopping_point = Vector2p{in.pc_stopping_point_n, in.pc_stopping_point_e};
    harness_pc_lean_angle_max = in.pc_lean_angle_max;
    harness_att_target_roll = in.ac_att_target_roll;
    harness_att_target_pitch = in.ac_att_target_pitch;
}

// --- the commands of a tick, one id each, in the fixed order: ModeLoiter::run makes
// set_pilot_desired_acceleration_rad, then soften_for_landing, then init_target or update
// (mode_loiter.cpp:90-161); ModeLoiter::init set_pilot_desired_acceleration_rad, then init_target
// (:17-19); ModePosHold and ModeZigZag init_target_m (mode_poshold.cpp:421, mode_zigzag.cpp:239);
// set_speed_max_NE_ms is the tuning knob's (tuning.cpp:214), before the mode runs.
enum OpId { OP_SPEED_MAX, OP_PILOT, OP_SOFTEN, OP_INIT_M, OP_INIT, OP_UPDATE, OP_COUNT };

struct SeqItem { uint32_t seq; int id; };

// All `_seq` 0: the fixed order. Otherwise by `_seq`; a set command with `_seq` 0 takes the
// largest `_seq` of the commands before it in the fixed order, ties keep the fixed order (as the
// guidance and position stages order theirs).
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

static void run_op(int id, const Input &in)
{
    switch (id) {
    case OP_SPEED_MAX: loiter->set_speed_max_NE_ms(in.cmd_loiter_set_speed_max_NE_ms_speed); break;
    case OP_PILOT:
        loiter->set_pilot_desired_acceleration_rad(in.cmd_loiter_set_pilot_desired_acceleration_rad_roll,
                                                   in.cmd_loiter_set_pilot_desired_acceleration_rad_pitch);
        break;
    case OP_SOFTEN: loiter->soften_for_landing(); break;
    case OP_INIT_M:
        loiter->init_target_m(Vector2p{in.cmd_loiter_init_target_m_n, in.cmd_loiter_init_target_m_e});
        break;
    case OP_INIT: loiter->init_target(); break;
    case OP_UPDATE: loiter->update(in.cmd_loiter_update_avoidance_on); break;
    default: break;
    }
}

// one command, with the sentinel for set_pos_desired_NE_m (header)
static void run_with_sentinel(int id, const Input &in)
{
    AC_PosControl &pc = posctl();
    Vector3p &pd = pc.*member_ptr(PcPosDesired());
    if (id == OP_UPDATE) {
        run_op(id, in);
        return;
    }
    const Vector3p loaded = pd;
    pd.x = pd.y = postype_t(NAN);
    run_op(id, in);
    if (isnan(pd.x) && isnan(pd.y)) {
        pd = loaded;
        return;
    }
    HarnessLoiterCalls &c = harness_loiter_calls;
    if (!c.set_pos_desired_ne) {
        c.pos_desired_seq = harness_current_seq;
    }
    c.set_pos_desired_ne = true;
    c.pos_desired = pd.xy();
}

static bool update_ran, update_last, pilot_set, pilot_before_update;

static void run_ordered(const Input &in)
{
#define L_ITEM(name, opid) if (in.cmd_loiter_##name) { items[n].seq = in.cmd_loiter_##name##_seq; items[n].id = (opid); n++; }
    SeqItem items[OP_COUNT];
    int n = 0;
    L_ITEM(set_speed_max_NE_ms, OP_SPEED_MAX)
    L_ITEM(set_pilot_desired_acceleration_rad, OP_PILOT)
    L_ITEM(soften_for_landing, OP_SOFTEN)
    L_ITEM(init_target_m, OP_INIT_M)
    L_ITEM(init_target, OP_INIT)
    L_ITEM(update, OP_UPDATE)
#undef L_ITEM
    order_items(items, n);
    update_ran = update_last = pilot_set = pilot_before_update = false;
    for (int i = 0; i < n; i++) {
        // the command's `_seq` is kept for the hand-over (an unsequenced command in a sequenced
        // tick reports the `_seq` it ran after)
        harness_current_seq = items[i].seq;
        run_with_sentinel(items[i].id, in);
        if (items[i].id == OP_PILOT) {
            pilot_set = true;
            pilot_before_update = !update_ran;
        }
        if (items[i].id == OP_UPDATE) {
            update_ran = true;
        }
        update_last = items[i].id == OP_UPDATE;
    }
    harness_current_seq = 0;
}

void module_step(const Input &in, Output &out)
{
    harness_clock_ms = in.now_ms;
    harness_gnd_spd_limit = in.est_gnd_spd_limit;
    AP::ahrs().update();                 // stand-in: the estimator's ground-speed limit (stubs_ahrs.cpp)
    ahrs_view().yaw = in.est_yaw;
    attctl().set_dt_s(in.dt);            // Copter::run_rate_controller_main (Attitude.cpp:15)
    load_position_controller(in);
    memset(&harness_loiter_calls, 0, sizeof harness_loiter_calls);

    run_ordered(in);

    // what was handed to the position controller
    const HarnessLoiterCalls &c = harness_loiter_calls;
    out.lt_tgt_ne_init_stopping_point = c.ne_init_stopping_point;
    out.lt_tgt_ne_set_correction_speed_accel = c.ne_set_correction;
    out.lt_tgt_ne_correction_speed = c.ne_correction_speed;
    out.lt_tgt_ne_correction_accel = c.ne_correction_accel;
    out.lt_tgt_handover_seq = c.handover_seq;
    out.lt_cmd_position_NE_set_pos_error_max_m = c.ne_set_pos_error_max;
    out.lt_cmd_position_NE_set_pos_error_max_m_error_max = c.error_max;
    out.lt_cmd_position_NE_set_pos_error_max_m_seq = c.error_max_seq;
    out.lt_cmd_position_set_pos_desired_NE_m = c.set_pos_desired_ne;
    out.lt_cmd_position_set_pos_desired_NE_m_n = float(c.pos_desired.x);
    out.lt_cmd_position_set_pos_desired_NE_m_e = float(c.pos_desired.y);
    out.lt_cmd_position_set_pos_desired_NE_m_seq = c.pos_desired_seq;
    out.lt_cmd_position_NE_relax_velocity_controller = c.ne_relax;
    out.lt_cmd_position_NE_relax_velocity_controller_seq = c.relax_seq;
    out.lt_cmd_position_NE_soften_for_landing = c.ne_soften;
    out.lt_cmd_position_NE_soften_for_landing_seq = c.soften_seq;
    out.lt_tgt_valid = c.set_pos_vel_accel;
    out.lt_tgt_ne_update = c.ne_update;
    out.lt_tgt_update_seq = c.update_seq;
    out.lt_tgt_pos_n = float(c.pos.x);
    out.lt_tgt_pos_e = float(c.pos.y);
    out.lt_tgt_vel_n = c.vel.x;
    out.lt_tgt_vel_e = c.vel.y;
    out.lt_tgt_acc_n = c.accel.x;
    out.lt_tgt_acc_e = c.accel.y;

    // the controller's state after the step, as the mode code reads it
    out.lt_angle_max = loiter->get_angle_max_rad();
    out.lt_att_lean_angle_max = attctl().lean_angle_max_rad();
    const Vector2f &da = loiter->get_pilot_desired_acceleration_NE_mss();
    out.lt_desired_accel_n = da.x;
    out.lt_desired_accel_e = da.y;
    out.lt_predicted_accel_n = loiter->predicted_accel().x;
    out.lt_predicted_accel_e = loiter->predicted_accel().y;
    out.lt_predicted_roll = loiter->predicted_angle().x;
    out.lt_predicted_pitch = loiter->predicted_angle().y;
    out.lt_predicted_roll_rate = loiter->predicted_rate().x;
    out.lt_predicted_pitch_rate = loiter->predicted_rate().y;
    out.lt_predicted_roll_accel = loiter->predicted_ang_accel().x;
    out.lt_predicted_pitch_accel = loiter->predicted_ang_accel().y;
    out.lt_brake_accel = loiter->brake_accel();
    out.lt_brake_timer_ms = loiter->brake_timer_ms();
    out.lt_speed_max = loiter->speed_max();
    out.lt_accel_max = loiter->accel_max();
    Vector2f sp;
    loiter->get_stopping_point_NE_m(sp);
    out.lt_stopping_point_n = sp.x;
    out.lt_stopping_point_e = sp.y;
    out.lt_update_ran = update_ran;
    out.lt_update_last = update_last;
    out.lt_pilot_set = pilot_set;
    out.lt_pilot_before_update = pilot_before_update;
    out.lt_internal_errors = harness_internal_error_count();
}
