// stubs_ahrs.cpp: the estimator (AP_AHRS, its active backend's results, and the AHRS view).
//
// The estimator is its own stage; its results reach this module as the input signals est_*. They
// are loaded into the AP_AHRS object and its view by stand-ins for the two update functions the
// vehicle calls once per loop, so that the accessors AC_PosControl uses read them through
// ArduPilot's own inline code.
//
//   symbol                                   why it is outside the stage, and what stands in
//   AP::ahrs()                               the AHRS singleton. Zeroed storage (never constructed:
//                                            its members include every estimator backend).
//   AP_AHRS::update(bool)                    the estimator's update (AP_AHRS.cpp), called by the
//                                            adapter once per step. Stand-in: points
//                                            active_estimates at one Estimates record holding
//                                            est_pos_* (+ valid flags), est_vert_pos_rate_d (+ valid)
//                                            and the control gain scalers; sets state.accel_ef =
//                                            (0, 0, est_accel_ef_d) and state.velocity_NED (+ ok);
//                                            steps the NE and D position reset trackers with the
//                                            EKF's counts as keys (AP_AHRS::update_reset_counters
//                                            does the same with the backend's counts), so the
//                                            counts AC_PosControl sees change exactly when the
//                                            input counts change. Read by the inline accessors
//                                            get_relative_position_NED_origin,
//                                            get_control_gain_scaler_XY/Z, get_accel_ef,
//                                            get_position_NE/D_reset_count.
//   AP_AHRS::get_velocity_NED                out of line in AP_AHRS.cpp:2091; the same body: the
//                                            state's velocity and its ok flag (est_vel_*).
//   AP_AHRS::get_relative_position_D_origin_float
//                                            AP_AHRS.cpp:1044; the same body: position_D and its
//                                            valid flag of the active estimates.
//   AP_AHRS::get_vert_pos_rate_D             AP_AHRS.cpp:990; the same body.
//   AP_AHRS_View::AP_AHRS_View(...)          the view's constructor (AP_AHRS_View.cpp), as
//                                            Copter::init_ardupilot creates it (ROTATION_NONE, no
//                                            pitch trim). Stand-in: binds the AHRS reference; the
//                                            rotation set-up is not needed (ROTATION_NONE).
//   AP_AHRS_View::update()                   the view's update (AP_AHRS_View.cpp:61), run by
//                                            AP_AHRS::update. Stand-in: yaw = est_yaw,
//                                            trig.cos_yaw/sin_yaw = est_cos_yaw/est_sin_yaw, read by
//                                            the inline cos_yaw(), sin_yaw() and the member yaw.
#include <AP_AHRS/AP_AHRS.h>
#include <AP_AHRS/AP_AHRS_View.h>

alignas(AP_AHRS) static unsigned char ahrs_storage[sizeof(AP_AHRS)];
alignas(AP_AHRS_Backend::Estimates) static unsigned char
    estimates_storage[sizeof(AP_AHRS_Backend::Estimates)];
alignas(AP_AHRS_View) static unsigned char view_storage[sizeof(AP_AHRS_View)];

AP_AHRS &AP::ahrs()
{
    return *reinterpret_cast<AP_AHRS *>(ahrs_storage);
}

void AP_AHRS::update(bool skip_ins_update)
{
    AP_AHRS_Backend::Estimates &e = *reinterpret_cast<AP_AHRS_Backend::Estimates *>(estimates_storage);
    e.position_NE = Vector2p{harness_cut.pos_n, harness_cut.pos_e};
    e.position_NE_valid = harness_cut.pos_ne_valid;
    e.position_D = harness_cut.pos_d;
    e.position_D_valid = harness_cut.pos_d_valid;
    e.vert_pos_rate_D = harness_cut.vert_pos_rate_d;
    e.vert_pos_rate_D_valid = harness_cut.vert_pos_rate_valid;
    e.control_gain_scaler_XY = harness_cut.gain_scaler_xy;
    e.control_gain_scaler_Z = harness_cut.gain_scaler_z;
    active_estimates = &e;
    state.accel_ef = Vector3f{0.0f, 0.0f, harness_cut.accel_ef_d};
    state.velocity_NED = Vector3f{harness_cut.vel_n, harness_cut.vel_e, harness_cut.vel_d};
    state.velocity_NED_ok = harness_cut.vel_valid;
    position_NE_reset_tracker.update(harness_cut.pos_ne_reset_key);
    position_D_reset_tracker.update(harness_cut.pos_d_reset_key);
}

bool AP_AHRS::get_velocity_NED(Vector3f &vec) const
{
    vec = state.velocity_NED;
    return state.velocity_NED_ok;
}

bool AP_AHRS::get_relative_position_D_origin_float(float &posD) const
{
    postype_t tmp_posD;
    if (!get_relative_position_D_origin(tmp_posD)) {
        return false;
    }
    posD = float(tmp_posD);
    return true;
}

bool AP_AHRS::get_vert_pos_rate_D(float &velocity) const
{
    return active_estimates->get_vert_pos_rate_D(velocity);
}

AP_AHRS_View::AP_AHRS_View(AP_AHRS &_ahrs, enum Rotation _rotation, float pitch_trim_deg) :
    rotation(_rotation),
    ahrs(_ahrs)
{
    _pitch_trim_deg = pitch_trim_deg;
}

void AP_AHRS_View::update()
{
    yaw = harness_cut.yaw;
    trig.cos_yaw = harness_cut.cos_yaw;
    trig.sin_yaw = harness_cut.sin_yaw;
}

AP_AHRS_View *harness_make_view()
{
    memset(view_storage, 0, sizeof view_storage);
    return new (view_storage) AP_AHRS_View(AP::ahrs(), ROTATION_NONE, 0.0f);
}

static void harness_reset_ahrs()
{
    memset(ahrs_storage, 0, sizeof ahrs_storage);
    memset(estimates_storage, 0, sizeof estimates_storage);
}
