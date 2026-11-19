// adapter.cpp: the cut between the harness records and ArduCopter's real waypoint navigator.
//
// The object is a real AC_WPNav (its S-curve and spline legs inside it). HarnessWPNav derives from
// it only to reach protected members: it overrides nothing, so every virtual call runs
// ArduPilot's code.
//
// init (Copter::allocate_motors, system.cpp:490-497): ArduCopter allocates the navigator with
// NEW_NOTHROW, whose memory ArduPilot zeroes, and then loads its parameters from EEPROM; here the
// object is built in zeroed storage and every AP_Param member it reads is set from the parameter
// record. The constructor records WP_SPD, WP_SPD_UP and WP_SPD_DN as they are at construction
// (_last_wp_speed_*: defaults, since setup_object_defaults runs before the EEPROM load), and
// update_wpnav re-applies them when they differ (AC_WPNav.cpp:716-731). The adapter sets the
// recorded values to the parameter record's, which is ArduCopter's state when the stored
// parameters equal the defaults or once that first re-application has happened; the module's
// parameters do not change during a run, so the re-application never happens.
//   WP_RFND_USE = 1 (default) is fixed: the rangefinder is never set available
//   (set_rangefinder_terrain_U_m is not called), so it is not read.
//
// The position controller and the attitude controller are other stages: zeroed storage, loaded
// from the records (cut.h, stubs_posctl.cpp). The attitude controller's members read are
// parameters (ATC_RATE_R_MAX, ATC_RATE_P_MAX, ATC_INPUT_TC, ATC_ACC_R_MAX, ATC_ACC_P_MAX). The AHRS
// view is never read by AC_WPNav (zeroed storage).
//
// step:
//   1. the signals: the clock, the position controller's members from est_ and pc_ inputs, the
//      recorded calls cleared
//   2. the commands that are set, in the order of Module.lean's doc (the order of ArduCopter's
//      mode code in one tick), then update_wpnav() if cmd_guidance_update_wpnav
//   3. the outputs: the recorded calls (tgt_), the navigator's status (wp_)
//
// AC_Loiter is not in this module. Its step calls four methods of the other two controllers that
// compute on this tick's arguments and return a value within the call: the attitude
// controller's command_model_rate_predictor and lean_angle_max_rad, and the position controller's
// lean_angles_rad_to_accel_NED_mss and get_lean_angle_max_rad (AC_Loiter.cpp:155-180, 211-220,
// 250). None of them can be a signal of the previous tick (they depend on this tick's pilot
// sticks), and standing in for them would mean copying the other stages' code into this module.
// It also runs only in LOITER (and the landing modes' repositioning), never in the same tick as
// update_wpnav, and hands the position controller only NE targets.
#include "module_protocol.h"

#include <new>
#include <string.h>

#include "cut.h"

#include <AC_WPNav/AC_WPNav.h>

// --- members of the other stages' objects that the module loads (cut.h, HARNESS_MEMBER)
HARNESS_MEMBER(PcDt, AC_PosControl, float, _dt_s);
HARNESS_MEMBER(PcShapingJerkNE, AC_PosControl, AP_Float, _shaping_jerk_ne_msss);
HARNESS_MEMBER(PcPosNE, AC_PosControl, AC_P_2D, _p_pos_ne_m);
HARNESS_MEMBER(PcPosD, AC_PosControl, AC_P_1D, _p_pos_d_m);
HARNESS_MEMBER(PcVelMaxNE, AC_PosControl, float, _vel_max_ne_ms);
HARNESS_MEMBER(PcAccelMaxNE, AC_PosControl, float, _accel_max_ne_mss);
HARNESS_MEMBER(PcVelMaxUp, AC_PosControl, float, _vel_max_up_ms);
HARNESS_MEMBER(PcVelMaxDown, AC_PosControl, float, _vel_max_down_ms);
HARNESS_MEMBER(PcAccelMaxD, AC_PosControl, float, _accel_max_d_mss);
HARNESS_MEMBER(PcPosEstimate, AC_PosControl, Vector3p, _pos_estimate_ned_m);
HARNESS_MEMBER(PcVelEstimate, AC_PosControl, Vector3f, _vel_estimate_ned_ms);
HARNESS_MEMBER(PcVelDesired, AC_PosControl, Vector3f, _vel_desired_ned_ms);
HARNESS_MEMBER(PcPosOffset, AC_PosControl, Vector3p, _pos_offset_ned_m);
HARNESS_MEMBER(PcVelOffset, AC_PosControl, Vector3f, _vel_offset_ned_ms);
HARNESS_MEMBER(PcPosTarget, AC_PosControl, Vector3p, _pos_target_ned_m);
HARNESS_MEMBER(PcPosTerrain, AC_PosControl, float, _pos_terrain_d_m);
HARNESS_MEMBER(PcPosTerrainTarget, AC_PosControl, float, _pos_terrain_target_d_m);
HARNESS_MEMBER(PNEError, AC_P_2D, Vector2f, _error);
HARNESS_MEMBER(PDError, AC_P_1D, float, _error);
HARNESS_MEMBER(AcRateRollMax, AC_AttitudeControl, AP_Float, _ang_vel_roll_max_degs);
HARNESS_MEMBER(AcRatePitchMax, AC_AttitudeControl, AP_Float, _ang_vel_pitch_max_degs);
HARNESS_MEMBER(AcInputTC, AC_AttitudeControl, AP_Float, _input_tc);
HARNESS_MEMBER(AcAccelRollMax, AC_AttitudeControl, AP_Float, _accel_roll_max_degss);
HARNESS_MEMBER(AcAccelPitchMax, AC_AttitudeControl, AP_Float, _accel_pitch_max_degss);
HARNESS_MEMBER(ScurveIsArc, SCurve, bool, is_arc_segment);
HARNESS_MEMBER(ScurveNumSegs, SCurve, uint8_t, num_segs);
HARNESS_MEMBER(ScurveVelMax, SCurve, float, vel_max);
HARNESS_MEMBER(ScurveAccelMax, SCurve, float, accel_max);

// The planned peak speed of an S-curve leg: the largest end velocity of its 23 time segments
// (SCurve::segment, an array of an unnamed struct type, so its pointer-to-member type is taken
// with decltype inside the explicit instantiation, where access is not checked). Within one
// segment the acceleration keeps its sign, so the speed lies between the segment's end values.
// A leg with fewer than 23 segments is a zero-length path (SCurve::init).
float scurve_peak_speed(const SCurve &s, struct ScurveSegmentsTag *);
template <typename T, T M>
struct RobSegments {
    friend float scurve_peak_speed(const SCurve &s, struct ScurveSegmentsTag *)
    {
        if ((s.*member_ptr(ScurveNumSegs())) != 23) {
            return 0.0f;
        }
        float peak = 0.0f;
        for (uint8_t i = 0; i < 23; i++) {
            peak = MAX(peak, (s.*M)[i].end_vel);
        }
        return peak;
    }
};
template struct RobSegments<decltype(&SCurve::segment), &SCurve::segment>;

class HarnessWPNav : public AC_WPNav {
public:
    HarnessWPNav(const AP_AHRS_View &ahrs, AC_PosControl &pos_control, const AC_AttitudeControl &att) :
        AC_WPNav(ahrs, pos_control, att) {}

    // as the parameter system stores each value (AP_Param::set, no constraint)
    void set_params(const Params &p)
    {
        _wp_speed_ms.set(p.wp_spd);
        _wp_radius_m.set(p.wp_radius_m);
        _wp_speed_up_ms.set(p.wp_spd_up);
        _wp_speed_down_ms.set(p.wp_spd_dn);
        _wp_accel_mss.set(p.wp_acc);
        _wp_accel_z_mss.set(p.wp_acc_z);
        _wp_accel_c_mss.set(p.wp_acc_cnr);
        _wp_jerk_msss.set(p.wp_jerk);
        _terrain_margin_m.set(p.wp_ter_margin);
        _rangefinder_use.set(1);
        // the WP_SPD change detector's record (see the header comment)
        _last_wp_speed_ms = _wp_speed_ms;
        _last_wp_speed_up_ms = _wp_speed_up_ms;
        _last_wp_speed_down_ms = get_default_speed_down_ms();
    }

    bool fast() const { return _flags.fast_waypoint; }
    bool leg_spline() const { return _this_leg_is_spline; }
    bool leg_arc() const { return _scurve_this_leg.*member_ptr(ScurveIsArc()); }
    bool prev_leg_finished() const { return _scurve_prev_leg.finished(); }
    float leg_peak_speed() const { return scurve_peak_speed(_scurve_this_leg, nullptr); }
    float leg_vel_max() const { return _scurve_this_leg.*member_ptr(ScurveVelMax()); }
    float leg_accel_max() const { return _scurve_this_leg.*member_ptr(ScurveAccelMax()); }
    float speed_ne() const { return _wp_desired_speed_ne_ms; }
    float offset_vel() const { return _offset_vel_ms; }
    float offset_accel() const { return _offset_accel_mss; }
    float track_dt_scalar() const { return _track_dt_scalar; }
    // calc_scurve_jerk_and_snap has never run: wp_and_spline_init_m (directly, or from a
    // destination setter's re-initialization) has not been called since construction
    bool uninitialized() const
    {
#pragma GCC diagnostic push
#pragma GCC diagnostic ignored "-Wfloat-equal"
        return _scurve_jerk_max_msss == 0.0f && _scurve_snap_max_mssss == 0.0f;
#pragma GCC diagnostic pop
    }
};

// ArduCopter's objects come from NEW_NOTHROW, whose memory ArduPilot zeroes (AP_Common/c++.cpp)
alignas(HarnessWPNav) static unsigned char wpnav_storage[sizeof(HarnessWPNav)];
alignas(AC_PosControl) static unsigned char posctl_storage[sizeof(AC_PosControl)];
alignas(AC_AttitudeControl) static unsigned char attctl_storage[sizeof(AC_AttitudeControl)];
alignas(AP_AHRS_View) static unsigned char ahrs_view_storage[sizeof(AP_AHRS_View)];
static HarnessWPNav *wpnav;

static bool navigator_uninitialized()
{
    return wpnav != nullptr && wpnav->uninitialized();
}

static AC_PosControl &posctl()
{
    return *reinterpret_cast<AC_PosControl *>(posctl_storage);
}

static AC_AttitudeControl &attctl()
{
    return *reinterpret_cast<AC_AttitudeControl *>(attctl_storage);
}

static Vector3p vec3p(float n, float e, float d)
{
    return Vector3p(n, e, d);
}

// The speed and acceleration limits handed to the position stage at the previous tick
// (tgt_ne_max_speed, tgt_ne_max_accel, tgt_max_speed_up, tgt_max_speed_down, tgt_d_max_accel). In
// ArduCopter the position controller holds what AC_WPNav set until something else sets it, and
// the flight modes that drive AC_WPNav initialize it (pushing these limits) before using it. A
// position stage that returns other limits (pc_…) is outside that use; the adapter records the
// first such tick (wp_limits_incoherent, kept until the next init) so that the contract can
// say which internal errors follow from it. Bookkeeping of the harness, not ArduPilot state.
static bool limits_handed;
static float handed_limits[5];

static void check_limits_coherent(const Input &in)
{
    const float pc[5] = {in.pc_ne_max_speed, in.pc_ne_max_accel, in.pc_max_speed_up,
                         in.pc_max_speed_down, in.pc_d_max_accel};
    if (limits_handed && memcmp(pc, handed_limits, sizeof pc) != 0) {
        harness_limits_incoherent = true;
    }
}

void module_init(const Params &p)
{
    memset(wpnav_storage, 0, sizeof wpnav_storage);
    memset(posctl_storage, 0, sizeof posctl_storage);
    memset(attctl_storage, 0, sizeof attctl_storage);
    memset(ahrs_view_storage, 0, sizeof ahrs_view_storage);
    harness_reset_internal_errors();
    harness_clock_ms = 0;
    harness_printf_count = 0;
    memset(&harness_pos_calls, 0, sizeof harness_pos_calls);
    harness_pc_stopping_point.zero();

    AC_PosControl &pc = posctl();
    (pc.*member_ptr(PcShapingJerkNE())).set(p.psc_ne_jerk);
    (pc.*member_ptr(PcPosNE())).kP().set(p.psc_ne_pos_p);
    AC_AttitudeControl &ac = attctl();
    (ac.*member_ptr(AcRateRollMax())).set(p.atc_rate_r_max);
    (ac.*member_ptr(AcRatePitchMax())).set(p.atc_rate_p_max);
    (ac.*member_ptr(AcInputTC())).set(p.atc_input_tc);
    (ac.*member_ptr(AcAccelRollMax())).set(p.atc_acc_r_max);
    (ac.*member_ptr(AcAccelPitchMax())).set(p.atc_acc_p_max);

    wpnav = new (wpnav_storage) HarnessWPNav(*reinterpret_cast<AP_AHRS_View *>(ahrs_view_storage), pc, ac);
    wpnav->set_params(p);
    harness_navigator_uninitialized = navigator_uninitialized;
    limits_handed = false;
}

// the position controller's members, as the position stage left them after the previous tick
// (pc_) and as AC_PosControl::update_estimates set them at the start of this one (est_)
static void load_position_controller(const Input &in)
{
    AC_PosControl &pc = posctl();
    pc.*member_ptr(PcDt()) = in.dt;
    pc.*member_ptr(PcPosEstimate()) = vec3p(in.est_pos_n, in.est_pos_e, in.est_pos_d);
    pc.*member_ptr(PcVelEstimate()) = Vector3f(in.est_vel_n, in.est_vel_e, in.est_vel_d);
    pc.*member_ptr(PcVelDesired()) = Vector3f(in.pc_vel_desired_n, in.pc_vel_desired_e, in.pc_vel_desired_d);
    pc.*member_ptr(PcVelOffset()) = Vector3f(0.0f, 0.0f, in.pc_vel_offset_d);
    pc.*member_ptr(PcPosOffset()) = vec3p(in.pc_pos_offset_n, in.pc_pos_offset_e, in.pc_pos_offset_d);
    (pc.*member_ptr(PcPosNE())).*member_ptr(PNEError()) = Vector2f(in.pc_pos_error_n, in.pc_pos_error_e);
    (pc.*member_ptr(PcPosD())).*member_ptr(PDError()) = in.pc_pos_error_d;
    pc.*member_ptr(PcPosTarget()) = vec3p(0.0f, 0.0f, in.pc_pos_target_d);
    pc.*member_ptr(PcPosTerrain()) = 0.0f;
    pc.*member_ptr(PcPosTerrainTarget()) = 0.0f;
    pc.*member_ptr(PcVelMaxNE()) = in.pc_ne_max_speed;
    pc.*member_ptr(PcAccelMaxNE()) = in.pc_ne_max_accel;
    pc.*member_ptr(PcVelMaxUp()) = in.pc_max_speed_up;
    pc.*member_ptr(PcVelMaxDown()) = in.pc_max_speed_down;
    pc.*member_ptr(PcAccelMaxD()) = in.pc_d_max_accel;
    harness_pc_stopping_point = vec3p(in.pc_stopping_point_n, in.pc_stopping_point_e, in.pc_stopping_point_d);
}

// --- the commands of a tick, one id each, in the fixed order (Module.lean's header)
enum OpId {
    OP_INIT, OP_SPEED_NE, OP_SPEED_UP, OP_SPEED_DOWN, OP_WP_DEST, OP_SPLINE_DEST, OP_WP_DEST_NEXT,
    OP_SPLINE_DEST_NEXT, OP_FORCE_STOP, OP_PAUSE, OP_RESUME, OP_UPDATE, OP_COUNT
};

struct SeqItem { uint32_t seq; int id; };

static bool update_last;

// All `_seq` 0: the fixed order. Otherwise by `_seq`; a set command with `_seq` 0 takes the
// largest `_seq` of the commands before it in the fixed order, ties keep the fixed order.
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

// returns update_wpnav's result (true if it did not run)
static bool run_op(int id, const Input &in)
{
    switch (id) {
    case OP_INIT:
        wpnav->wp_and_spline_init_m(in.cmd_guidance_wp_and_spline_init_m_speed_ms,
                                    vec3p(in.cmd_guidance_wp_and_spline_init_m_stopping_point_n,
                                          in.cmd_guidance_wp_and_spline_init_m_stopping_point_e,
                                          in.cmd_guidance_wp_and_spline_init_m_stopping_point_d));
        break;
    case OP_SPEED_NE: wpnav->set_speed_NE_ms(in.cmd_guidance_set_speed_NE_ms_speed_ms); break;
    case OP_SPEED_UP: wpnav->set_speed_up_ms(in.cmd_guidance_set_speed_up_ms_speed_up_ms); break;
    case OP_SPEED_DOWN: wpnav->set_speed_down_ms(in.cmd_guidance_set_speed_down_ms_speed_down_ms); break;
    case OP_WP_DEST:
        (void)wpnav->set_wp_destination_NED_m(vec3p(in.cmd_guidance_set_wp_destination_NED_m_destination_n,
                                                    in.cmd_guidance_set_wp_destination_NED_m_destination_e,
                                                    in.cmd_guidance_set_wp_destination_NED_m_destination_d),
                                              false, in.cmd_guidance_set_wp_destination_NED_m_arc_rad);
        break;
    case OP_SPLINE_DEST:
        (void)wpnav->set_spline_destination_NED_m(
            vec3p(in.cmd_guidance_set_spline_destination_NED_m_destination_n,
                  in.cmd_guidance_set_spline_destination_NED_m_destination_e,
                  in.cmd_guidance_set_spline_destination_NED_m_destination_d),
            false,
            vec3p(in.cmd_guidance_set_spline_destination_NED_m_next_destination_n,
                  in.cmd_guidance_set_spline_destination_NED_m_next_destination_e,
                  in.cmd_guidance_set_spline_destination_NED_m_next_destination_d),
            false, in.cmd_guidance_set_spline_destination_NED_m_next_is_spline);
        break;
    case OP_WP_DEST_NEXT:
        (void)wpnav->set_wp_destination_next_NED_m(
            vec3p(in.cmd_guidance_set_wp_destination_next_NED_m_destination_n,
                  in.cmd_guidance_set_wp_destination_next_NED_m_destination_e,
                  in.cmd_guidance_set_wp_destination_next_NED_m_destination_d),
            false, in.cmd_guidance_set_wp_destination_next_NED_m_arc_rad);
        break;
    case OP_SPLINE_DEST_NEXT:
        (void)wpnav->set_spline_destination_next_NED_m(
            vec3p(in.cmd_guidance_set_spline_destination_next_NED_m_next_destination_n,
                  in.cmd_guidance_set_spline_destination_next_NED_m_next_destination_e,
                  in.cmd_guidance_set_spline_destination_next_NED_m_next_destination_d),
            false,
            vec3p(in.cmd_guidance_set_spline_destination_next_NED_m_next_next_destination_n,
                  in.cmd_guidance_set_spline_destination_next_NED_m_next_next_destination_e,
                  in.cmd_guidance_set_spline_destination_next_NED_m_next_next_destination_d),
            false, in.cmd_guidance_set_spline_destination_next_NED_m_next_next_is_spline);
        break;
    case OP_FORCE_STOP: (void)wpnav->force_stop_at_next_wp(); break;
    case OP_PAUSE: wpnav->set_pause(); break;
    case OP_RESUME: wpnav->set_resume(); break;
    case OP_UPDATE: return wpnav->update_wpnav();
    default: break;
    }
    return true;
}

static bool run_ordered(const Input &in)
{
#define G_ITEM(name, opid) if (in.cmd_guidance_##name) { items[n].seq = in.cmd_guidance_##name##_seq; items[n].id = (opid); n++; }
    SeqItem items[OP_COUNT];
    int n = 0;
    G_ITEM(wp_and_spline_init_m, OP_INIT)
    G_ITEM(set_speed_NE_ms, OP_SPEED_NE)
    G_ITEM(set_speed_up_ms, OP_SPEED_UP)
    G_ITEM(set_speed_down_ms, OP_SPEED_DOWN)
    G_ITEM(set_wp_destination_NED_m, OP_WP_DEST)
    G_ITEM(set_spline_destination_NED_m, OP_SPLINE_DEST)
    G_ITEM(set_wp_destination_next_NED_m, OP_WP_DEST_NEXT)
    G_ITEM(set_spline_destination_next_NED_m, OP_SPLINE_DEST_NEXT)
    G_ITEM(force_stop_at_next_wp, OP_FORCE_STOP)
    G_ITEM(set_pause, OP_PAUSE)
    G_ITEM(set_resume, OP_RESUME)
    G_ITEM(update_wpnav, OP_UPDATE)
#undef G_ITEM
    order_items(items, n);
    bool ok = true;
    update_last = n > 0 && items[n - 1].id == OP_UPDATE;
    for (int i = 0; i < n; i++) {
        // the original `_seq` is kept for the hand-over bookkeeping: an unsequenced command in a
        // sequenced tick reports the `_seq` it ran after
        harness_current_seq = items[i].seq;
        if (!run_op(items[i].id, in)) {
            ok = false;
        }
    }
    harness_current_seq = 0;
    return ok;
}

void module_step(const Input &in, Output &out)
{
    harness_clock_ms = in.now_ms;
    check_limits_coherent(in);
    load_position_controller(in);
    memset(&harness_pos_calls, 0, sizeof harness_pos_calls);

    // the commands, in the order of ArduCopter's mode code within a tick (Module.lean's header),
    // or, when the supervisor numbers them (`_seq`), in its call order
    const bool update_ok = run_ordered(in);

    // what was handed to the position controller
    const HarnessPosCalls &c = harness_pos_calls;
    out.tgt_valid = c.set_pos_vel_accel && c.ne_update;
    out.tgt_handover_seq = c.handover_seq;
    out.tgt_update_seq = c.set_pos_vel_accel ? c.update_seq : 0;
    if (c.set_pos_vel_accel) {
        out.tgt_pos_n = float(c.pos.x);
        out.tgt_pos_e = float(c.pos.y);
        out.tgt_pos_d = float(c.pos.z);
        out.tgt_vel_n = c.vel.x;
        out.tgt_vel_e = c.vel.y;
        out.tgt_vel_d = c.vel.z;
        out.tgt_acc_n = c.accel.x;
        out.tgt_acc_e = c.accel.y;
        out.tgt_acc_d = c.accel.z;
    }
    const AC_PosControl &pc = posctl();
    out.tgt_ne_init_stopping_point = c.ne_init_stopping_point;
    out.tgt_d_init_stopping_point = c.d_init_stopping_point;
    out.tgt_ne_set_max_speed_accel = c.ne_set_max_speed_accel;
    out.tgt_ne_max_speed = pc.NE_get_max_speed_ms();
    out.tgt_ne_max_accel = pc.NE_get_max_accel_mss();
    out.tgt_ne_set_correction_speed_accel = c.ne_set_correction;
    out.tgt_ne_correction_speed = c.ne_correction_speed;
    out.tgt_ne_correction_accel = c.ne_correction_accel;
    out.tgt_d_set_max_speed_accel = c.d_set_max_speed_accel;
    out.tgt_max_speed_down = pc.get_max_speed_down_ms();
    out.tgt_max_speed_up = pc.get_max_speed_up_ms();
    out.tgt_d_max_accel = pc.D_get_max_accel_mss();
    out.tgt_d_set_correction_speed_accel = c.d_set_correction;
    out.tgt_d_correction_speed_down = c.d_correction_down;
    out.tgt_d_correction_speed_up = c.d_correction_up;
    out.tgt_d_correction_accel = c.d_correction_accel;

    // the navigator's status, as the mode code reads it after the update
    out.wp_reached = wpnav->reached_wp_destination();
    out.wp_distance = wpnav->get_wp_distance_to_destination_m();
    out.wp_bearing = wpnav->get_wp_bearing_to_destination_rad();
    out.wp_active = wpnav->is_active();
    out.wp_paused = wpnav->paused();
    out.wp_update_ok = update_ok;
    out.wp_update_last = update_last;
    const Vector3p &o = wpnav->get_wp_origin_NED_m();
    const Vector3p &d = wpnav->get_wp_destination_NED_m();
    out.wp_origin_n = float(o.x);
    out.wp_origin_e = float(o.y);
    out.wp_origin_d = float(o.z);
    out.wp_destination_n = float(d.x);
    out.wp_destination_e = float(d.y);
    out.wp_destination_d = float(d.z);
    out.wp_fast = wpnav->fast();
    out.wp_leg_spline = wpnav->leg_spline();
    out.wp_leg_arc = wpnav->leg_arc();
    out.wp_prev_leg_finished = wpnav->prev_leg_finished();
    out.wp_leg_peak_speed = wpnav->leg_peak_speed();
    out.wp_leg_vel_max = wpnav->leg_vel_max();
    out.wp_leg_accel_max = wpnav->leg_accel_max();
    out.wp_speed_ne = wpnav->speed_ne();
    out.wp_offset_vel = wpnav->offset_vel();
    out.wp_offset_accel = wpnav->offset_accel();
    out.wp_track_dt_scalar = wpnav->track_dt_scalar();
    out.wp_internal_errors = harness_internal_error_count();
    out.wp_internal_errors_uninit = harness_uninitialized_errors;
    out.wp_internal_errors_incoherent = harness_incoherent_errors;
    out.wp_limits_incoherent = harness_limits_incoherent;
    const float handed[5] = {out.tgt_ne_max_speed, out.tgt_ne_max_accel, out.tgt_max_speed_up,
                             out.tgt_max_speed_down, out.tgt_d_max_accel};
    memcpy(handed_limits, handed, sizeof handed);
    limits_handed = true;
}
