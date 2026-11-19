// stubs_ahrs.cpp: the AP_AHRS shadow (estimator stage): state written from the input record
// before each tick, and hand-written answers to the out-of-line queries the vehicle code makes.
//
// harness_estimator_fill writes what AP_AHRS::update() would leave behind (AP_AHRS.cpp,
// update_state and the attitude bookkeeping after it): the EKF3 backend's Estimates (attitude,
// rotation matrix, gyro, velocity, position relative to the origin, origin, health), the front
// end's `state` copy of them, roll/pitch/yaw and their trig and degree forms, and the view
// (AP_AHRS_View::update, real body below). Home is not filled: it is the supervisor's
// (set_home below; ArduCopter sets it at arming and from the ground station).
//
//   method                                   answer (real code it mirrors)
//   create_view                              real body (AP_AHRS_Backend.cpp:165)
//   AP_AHRS_View::update                     real body (AP_AHRS_View.cpp:61), on the filled state
//   healthy                                  est_healthy
//   get_quaternion                           the filled quaternion; valid iff healthy
//   get_location                             origin offset by the NED position (Location::offset),
//                                            valid iff the origin is set
//   get_origin                               est_origin_*, valid iff est_origin_set
//   get_velocity_NED, get_velocity_D         est_vel_*
//   get_relative_position_NED/NE/D_origin_float
//                                            est_pos_*, valid iff the origin is set
//   get_relative_position_D_home             real body (AP_AHRS.cpp): location's height above home
//   have_inertial_nav                        true (EKF3 is the configured backend)
//   set_home                                 real body semantics: _home, _home_is_set; recorded as
//                                            a command (the estimator uses home only for its
//                                            relative-to-home outputs, which are computed here)
//   body_to_earth2D, body_to_earth2D_p,      real bodies, copied by gen/ (COPY_REAL), on the
//   configured_backend_has_status            filled state (filter status = est_filter_status)
//   pre_arm_check                            est_prearm_ok, the estimator's own verdict
//   using_noncompass_for_yaw                 false: EK3_SRC1_YAW default is compass (constant)
//   use_compass                              true: the EKF uses the compass (constant)
//   get_error_rp, get_error_yaw              0 (DCM's error estimates, reported in the AHRS
//                                            message): PLACEHOLDER
//   get_wind                                 zero, false: PLACEHOLDER (the EKF's wind estimate)
//   airspeed_vector_TAS                      false (no airspeed sensor or estimate): constant
//   get_pos_vel_uncertainty                  false: PLACEHOLDER (EKF3::getPosVelUncertainty)
//   send_ekf_status_report                   EKF_STATUS_REPORT with est_filter_status and the
//                                            variances est_*_var (compass variance on all axes)
//   NavEKF3::getInnovations                  est_innov_* (velocity, position; others 0)
#include <AP_AHRS/AP_AHRS.h>
#include <AP_AHRS/AP_AHRS_View.h>
#include <AP_HAL/AP_HAL.h>
#include <AP_Baro/AP_Baro.h>
extern const AP_HAL::HAL &hal;
#include <AP_Mission/AP_Mission.h>
#include <GCS_MAVLink/GCS.h>
#include "supervisor_shadow.h"
#include "module_records.h"

typedef float harness_f3[3];
typedef AP_AHRS_Backend::Estimates *harness_estp;
HARNESS_PRIVATE(AP_AHRS, float, roll)
HARNESS_PRIVATE(AP_AHRS, float, pitch)
HARNESS_PRIVATE(AP_AHRS, float, yaw)
HARNESS_PRIVATE(AP_AHRS, float, _cos_roll)
HARNESS_PRIVATE(AP_AHRS, float, _cos_pitch)
HARNESS_PRIVATE(AP_AHRS, float, _cos_yaw)
HARNESS_PRIVATE(AP_AHRS, float, _sin_roll)
HARNESS_PRIVATE(AP_AHRS, float, _sin_pitch)
HARNESS_PRIVATE(AP_AHRS, float, _sin_yaw)
HARNESS_PRIVATE(AP_AHRS, harness_estp, configured_estimates)
HARNESS_PRIVATE(AP_AHRS, harness_estp, active_estimates)
HARNESS_PRIVATE(AP_AHRS, AP_AHRS_Backend::Estimates, ekf3_estimates)
HARNESS_PRIVATE(AP_AHRS, AP_AHRS_View *, _view)
HARNESS_PRIVATE(AP_AHRS, AP_AHRS_Backend *, configured_backend)
HARNESS_PRIVATE(AP_AHRS, AP_AHRS_Backend *, active_backend)
HARNESS_PRIVATE(AP_AHRS, AP_AHRS_NavEKF3, ekf3)

// the front end's anonymous `state` struct: written inside a friend of an explicit instantiation
void harness_ahrs_fill_state(AP_AHRS &a, const AP_AHRS_Backend::Estimates &e, const Location &loc,
                             bool loc_ok, const Location &origin, bool origin_ok);
template <typename T, T M>
struct HarnessAhrsState {
    friend void harness_ahrs_fill_state(AP_AHRS &a, const AP_AHRS_Backend::Estimates &e,
                                        const Location &loc, bool loc_ok, const Location &origin,
                                        bool origin_ok)
    {
        auto &s = a.*M;
        s.active_EKF_type = AP_AHRS::EKFType::THREE;
        s.configured_ekf_type = AP_AHRS::EKFType::THREE;
        s.gyro_estimate = e.gyro_estimate;
        s.dcm_matrix = e.dcm_matrix;
        s.gyro_drift = e.gyro_drift;
        s.accel_ef = e.accel_ef;
        s.quat = e.quaternion;
        s.quat_ok = e.attitude_valid;
        s.location = loc;
        s.location_ok = loc_ok;
        s.ground_speed_vec = e.velocity_NED.xy();
        s.ground_speed = e.velocity_NED.xy().length();
        s.origin = origin;
        s.origin_ok = origin_ok;
        s.velocity_NED = e.velocity_NED;
        s.velocity_NED_ok = e.velocity_NED_valid;
        s.EAS2TAS = 1.0f;
    }
};
template struct HarnessAhrsState<decltype(&AP_AHRS::state), &AP_AHRS::state>;

// AP_AHRS::calc_trig is private; reached like the fields
typedef void (AP_AHRS::*harness_calc_trig_t)(const Matrix3f &, float &, float &, float &, float &,
                                             float &, float &) const;
harness_calc_trig_t harness_mp_calc_trig();
template <harness_calc_trig_t M>
struct HarnessCalcTrig {
    friend harness_calc_trig_t harness_mp_calc_trig() { return M; }
};
template struct HarnessCalcTrig<&AP_AHRS::calc_trig>;
static void harness_ahrs_calc_trig(AP_AHRS &a, const Matrix3f &m, float &cr, float &cp, float &cy,
                                   float &sr, float &sp, float &sy)
{
    (a.*harness_mp_calc_trig())(m, cr, cp, cy, sr, sp, sy);
}

static Input est;   // this tick's input record (the estimator's fields are read)
static Location est_origin, est_location;

void harness_estimator_fill(const Input &in)
{
    est = in;
    AP_AHRS &a = AP::ahrs();
    AP_AHRS_Backend::Estimates &e = HARNESS_FIELD(a, AP_AHRS, ekf3_estimates);
    e.healthy = in.est_healthy;
    e.initialised = in.est_initialised;
    e.attitude_valid = in.est_healthy;
    e.quaternion = Quaternion(in.est_q1, in.est_q2, in.est_q3, in.est_q4);
    e.quaternion.rotation_matrix(e.dcm_matrix);
    e.dcm_matrix.to_euler(&e.roll_rad, &e.pitch_rad, &e.yaw_rad);
    e.gyro_estimate = Vector3f(in.gyro_x, in.gyro_y, in.gyro_z);
    e.gyro_drift = Vector3f(in.est_gyro_drift_x, in.est_gyro_drift_y, in.est_gyro_drift_z);
    e.accel_ef = Vector3f(in.est_accel_ef_x, in.est_accel_ef_y, in.est_accel_ef_z);
    e.velocity_NED = Vector3f(in.est_vel_n, in.est_vel_e, in.est_vel_d);
    e.velocity_NED_valid = in.est_vel_ok;
    e.velocity_NE = e.velocity_NED.xy();
    e.position_NE = Vector2p(in.est_pos_n, in.est_pos_e);
    e.position_NE_valid = in.est_pos_ok;
    e.position_D = in.est_pos_d;
    e.position_D_valid = in.est_pos_ok;
    e.configured_to_use_gps = true;
    e.filter_status.value = in.est_filter_status;
    e.filter_status_valid = true;
    e.velVar = in.est_vel_variance;
    e.posVar = in.est_pos_variance;
    e.hgtVar = in.est_hgt_variance;
    e.magVar = Vector3f(in.est_mag_variance_x, in.est_mag_variance_y, in.est_mag_variance_z);
    e.tasVar = 0;
    e.variances_valid = in.est_variances_ok;
    // the EKF3 backend object is the configured and active one (its inline methods call the
    // NavEKF3 shadow's stand-ins)
    HARNESS_FIELD(a, AP_AHRS, configured_backend) = &HARNESS_FIELD(a, AP_AHRS, ekf3);
    HARNESS_FIELD(a, AP_AHRS, active_backend) = &HARNESS_FIELD(a, AP_AHRS, ekf3);
    HARNESS_FIELD(a, AP_AHRS, configured_estimates) = &e;
    HARNESS_FIELD(a, AP_AHRS, active_estimates) = &e;

    // location = origin moved by the NED position, as the EKF's getLLH does (origin offset)
    est_origin = Location(in.est_origin_lat_e7, in.est_origin_lon_e7, in.est_origin_alt_cm,
                          Location::AltFrame::ABSOLUTE);
    est_location = est_origin;
    est_location.offset(in.est_pos_n, in.est_pos_e);
    est_location.alt = in.est_origin_alt_cm - int32_t(lroundf(in.est_pos_d * 100));
    harness_ahrs_fill_state(a, e, est_location, in.est_origin_ok && in.est_pos_ok, est_origin,
                            in.est_origin_ok);

    // the attitude bookkeeping of AP_AHRS::update
    HARNESS_FIELD(a, AP_AHRS, roll) = e.roll_rad;
    HARNESS_FIELD(a, AP_AHRS, pitch) = e.pitch_rad;
    HARNESS_FIELD(a, AP_AHRS, yaw) = e.yaw_rad;
    a.rpy_deg[0] = degrees(e.roll_rad);
    a.rpy_deg[1] = degrees(e.pitch_rad);
    a.rpy_deg[2] = wrap_360(degrees(e.yaw_rad));
    a.roll_sensor = int32_t(degrees(e.roll_rad) * 100);
    a.pitch_sensor = int32_t(degrees(e.pitch_rad) * 100);
    a.yaw_sensor = int32_t(degrees(e.yaw_rad) * 100);
    if (a.yaw_sensor < 0) {
        a.yaw_sensor += 36000;
    }
    harness_ahrs_calc_trig(a, e.dcm_matrix, HARNESS_FIELD(a, AP_AHRS, _cos_roll),
                HARNESS_FIELD(a, AP_AHRS, _cos_pitch), HARNESS_FIELD(a, AP_AHRS, _cos_yaw),
                HARNESS_FIELD(a, AP_AHRS, _sin_roll), HARNESS_FIELD(a, AP_AHRS, _sin_pitch),
                HARNESS_FIELD(a, AP_AHRS, _sin_yaw));
    AP_AHRS_View *v = HARNESS_FIELD(a, AP_AHRS, _view);
    if (v != nullptr) {
        v->update();
    }
}

AP_AHRS_View *AP_AHRS::create_view(enum Rotation rotation, float pitch_trim_deg)
{
    if (_view != nullptr) {
        // can only have one
        return nullptr;
    }
    _view = NEW_NOTHROW AP_AHRS_View(*this, rotation, pitch_trim_deg);
    return _view;
}

void AP_AHRS_View::update()
{
    rot_body_to_ned = ahrs.get_rotation_body_to_ned();
    gyro = ahrs.get_gyro();

    if (!is_zero(y_angle + _pitch_trim_deg)) {
        rot_body_to_ned = rot_body_to_ned * rot_view_T;
        gyro = rot_view * gyro;
    }

    rot_body_to_ned.to_euler(&roll, &pitch, &yaw);

    roll_sensor  = degrees(roll) * 100;
    pitch_sensor = degrees(pitch) * 100;
    yaw_sensor   = degrees(yaw) * 100;
    if (yaw_sensor < 0) {
        yaw_sensor += 36000;
    }

    ahrs.calc_trig(rot_body_to_ned,
                   trig.cos_roll, trig.cos_pitch, trig.cos_yaw,
                   trig.sin_roll, trig.sin_pitch, trig.sin_yaw);
}

bool AP_AHRS::healthy() const { return est.est_healthy; }

bool AP_AHRS::get_quaternion(Quaternion &quat) const
{
    quat = state.quat;
    return state.quat_ok;
}

bool AP_AHRS::get_location(Location &loc) const
{
    loc = est_location;
    return est.est_origin_ok && est.est_pos_ok;
}

bool AP_AHRS::get_origin(Location &ret) const
{
    ret = est_origin;
    return est.est_origin_ok;
}

bool AP_AHRS::get_velocity_NED(Vector3f &vec) const
{
    vec = Vector3f(est.est_vel_n, est.est_vel_e, est.est_vel_d);
    return est.est_vel_ok;
}

// AP_AHRS.cpp, same body
bool AP_AHRS::get_velocity_D(float &velD, bool high_vibes) const
{
    Vector3f velNED;
    if (!high_vibes && get_velocity_NED(velNED)) {
        velD = velNED.z;
        return true;
    }
    return get_vert_pos_rate_D(velD);
}

// vertical position rate: the EKF's own derivative output; here the velocity estimate
bool AP_AHRS::get_vert_pos_rate_D(float &velocity) const
{
    velocity = est.est_pos_rate_d;
    return est.est_pos_rate_d_ok;
}

bool AP_AHRS::_get_origin(Location &ret) const
{
    ret = est_origin;
    return est.est_origin_ok;
}

// AP_AHRS.cpp, same body
void AP_AHRS::get_relative_position_D_home(float &posD) const
{
    if (!_home_is_set) {
        posD = -AP::baro().get_altitude();
        return;
    }
    Location originLLH;
    postype_t originD;
    if (!get_relative_position_D_origin(originD) ||
        !_get_origin(originLLH)) {
        posD = -AP::baro().get_altitude();
        return;
    }
    posD = originD - ((originLLH.alt - _home.alt) * 0.01f);
}

// AP_AHRS_Backend.cpp:93, same body
void AP_AHRS::calc_trig(const Matrix3f &rot,
                        float &cr, float &cp, float &cy,
                        float &sr, float &sp, float &sy) const
{
    Vector2f yaw_vector(rot.a.x, rot.b.x);

    if (fabsf(yaw_vector.x) > 0 ||
        fabsf(yaw_vector.y) > 0) {
        yaw_vector.normalize();
    }
    sy = constrain_float(yaw_vector.y, -1.0f, 1.0f);
    cy = constrain_float(yaw_vector.x, -1.0f, 1.0f);

    if (yaw_vector.is_inf() || yaw_vector.is_nan()) {
        sy = 0.0f;
        cy = 1.0f;
    }

    const float cx2 = rot.c.x * rot.c.x;
    if (cx2 >= 1.0f) {
        cp = 0;
        cr = 1.0f;
    } else {
        cp = safe_sqrt(1 - cx2);
        cr = rot.c.z / cp;
    }
    cp = constrain_float(cp, 0.0f, 1.0f);
    cr = constrain_float(cr, -1.0f, 1.0f);

    sp = -rot.c.x;

    if (!is_zero(cp)) {
        sr = rot.c.y / cp;
    }

    if (is_zero(cp) || isinf(cr) || isnan(cr) || isinf(sr) || isnan(sr)) {
        float r, p, y;
        rot.to_euler(&r, &p, &y);
        cr = cosf(r);
        sr = sinf(r);
    }
}

bool AP_AHRS::get_relative_position_NED_origin_float(Vector3f &vec) const
{
    vec = Vector3f(est.est_pos_n, est.est_pos_e, est.est_pos_d);
    return est.est_pos_ok;
}

bool AP_AHRS::get_relative_position_NE_origin_float(Vector2f &posNE) const
{
    posNE = Vector2f(est.est_pos_n, est.est_pos_e);
    return est.est_pos_ok;
}

bool AP_AHRS::get_relative_position_D_origin_float(float &posD) const
{
    posD = est.est_pos_d;
    return est.est_pos_ok;
}

bool AP_AHRS::have_inertial_nav(void) const { return true; }

// AP_AHRS.cpp, same body without logging, persistent data and the mission's home copy (the
// mission is the supervisor's and gets home through AP_Mission::write_home_to_storage, kept)
bool AP_AHRS::set_home(const Location &loc)
{
    sup_cmd_begin(SUP_CMD_HAND_AHRS_SET_HOME);
    sup_arg(loc);
    sup_cmd_end();
    if (!loc.initialised()) {
        return false;
    }
    if (!loc.check_latlng()) {
        return false;
    }
    Location tmp = loc;
    if (!tmp.change_alt_frame(Location::AltFrame::ABSOLUTE)) {
        return false;
    }
    _home = tmp;
    _home_is_set = true;
    GCS_SEND_MESSAGE(MSG_HOME);
    GCS_SEND_MESSAGE(MSG_ORIGIN);
#if AP_MISSION_ENABLED
    AP::mission().write_home_to_storage();
#endif
    return true;
}

// the estimator's own verdict (est_prearm_ok: AP_AHRS::pre_arm_check(true, ...) in the
// estimator stage); its message text does not cross the boundary
bool AP_AHRS::pre_arm_check(bool requires_position, char *failure_msg, uint8_t failure_msg_len) const
{
    if (!est.est_prearm_ok) {
        hal.util->snprintf(failure_msg, failure_msg_len, "AHRS: estimator not ready");
        return false;
    }
    return true;
}

bool AP_AHRS::using_noncompass_for_yaw(void) const { return false; }
bool AP_AHRS::use_compass(void) { return true; }
float AP_AHRS::get_error_rp(void) const { return 0; }
float AP_AHRS::get_error_yaw(void) const { return 0; }
bool AP_AHRS::get_wind(Vector3f &wind) const
{
    wind.zero();
    return false;
}
bool AP_AHRS::airspeed_vector_TAS(Vector3f &vec) const { return false; }
bool AP_AHRS::get_pos_vel_uncertainty(float &pos_horiz_m, float &pos_vert_m, float &vel_m_s) const
{
    return false;
}

void AP_AHRS::send_ekf_status_report(GCS_MAVLINK &link) const
{
    const float mag = MAX(est.est_mag_variance_x, MAX(est.est_mag_variance_y, est.est_mag_variance_z));
    mavlink_msg_ekf_status_report_send(link.get_chan(), uint16_t(est.est_filter_status),
                                       est.est_vel_variance, est.est_pos_variance,
                                       est.est_pos_variance, mag, est.est_hgt_variance, 0);
}

// the estimator's innovations (est_innov_*); magnetometer, airspeed and yaw ones are not
// exported (0)
bool NavEKF3::getInnovations(Vector3f &velInnov, Vector3f &posInnov, Vector3f &magInnov,
                             float &tasInnov, float &yawInnov) const
{
    velInnov = Vector3f(est.est_innov_vel_n, est.est_innov_vel_e, est.est_innov_vel_d);
    posInnov = Vector3f(est.est_innov_pos_n, est.est_innov_pos_e, est.est_innov_pos_d);
    magInnov.zero();
    tasInnov = 0;
    yawInnov = 0;
    return est.est_innov_ok;
}

// AP_InertialSensor::get_output_banner: the IMU's text banner sent to the ground station at
// connection ("IMU0: fast sampling ..."); false (no banner): PLACEHOLDER (estimator text)
#include <AP_InertialSensor/AP_InertialSensor.h>
bool AP_InertialSensor::get_output_banner(uint8_t instance_id, char *banner, uint8_t banner_len)
{
    return false;
}
