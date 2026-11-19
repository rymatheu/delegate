// adapter.cpp: the cut between the harness records and ArduCopter's real estimation chain.
//
// The objects are the vehicle's own (AP_Vehicle.h declares them in this order): AP_GPS gps,
// AP_Baro barometer, Compass compass, AP_InertialSensor ins, AP_AHRS ahrs, plus the EKF3 that
// AP_AHRS_NavEKF3 holds as a static member and the AP_DAL singleton EKF3 creates on first use.
// Nothing derives from them; every call below is ArduPilot's code.
//
// init (every case): every object is rebuilt in zeroed storage, its parameters are set to their
// code defaults by the constructors (AP_Param::setup_object_defaults, stubs_param.cpp), then the
// parameter record and the X500's stored values are written over them as the parameter storage
// would load them (Copter::load_parameters runs before init_ardupilot). Then the boot thread is
// started: it runs the estimator's part of Copter::init_ardupilot, in ArduCopter's order:
//   barometer.init()                    init_ardupilot
//   ahrs.create_view(ROTATION_NONE)     Copter::allocate_motors (system.cpp:454), the view the
//                                       controllers are built on
//   gps.init()                          init_ardupilot ("Do GPS init")
//   compass.init()                      init_ardupilot (AP::compass().init())
//   barometer.calibrate()               init_ardupilot ("read Baro pressure at ground")
//   ahrs.init(); ahrs.set_vehicle_class(COPTER); ins.init(400); ahrs.reset()
//                                       Copter::startup_INS_ground
// These calls block in hal.scheduler->delay() while they calibrate the barometer and the gyros
// (about 1.6 s and 0.6 s of simulated time). Here a delay in the boot thread hands control back
// to the harness and waits for the steps that bring the clock past its end (stubs_hal.cpp), so
// the boot sees the samples of those steps exactly as SITL's boot sees the simulator's.
//
// step: the HAL's clock is set to t_us, the tick's samples are handed to the driver stand-ins
// (backend_*.cpp) and the HAL's timer processes run (the drivers' timers). While the boot has not
// finished, the boot thread runs until its next delay or its end, and the outputs are the boot
// state (est_booted false, every estimate 0). After it, every step is one tick of ArduCopter's
// 400 Hz loop (AP_Scheduler::loop, Copter's task table, Copter.cpp:113-260):
//   the vehicle's calls on the estimator issued after read_AHRS in the previous tick (the
//   supervisor's commands, which arrive one tick later through the harness's wiring)
//   ins.update()                        FAST_TASK_CLASS(AP_InertialSensor, &copter.ins, update)
//   ahrs.update(true)                   FAST_TASK(read_AHRS)
//   gps.update()                        SCHED_TASK_CLASS(AP_GPS, ..., update, 50, ...)
//   compass.read()                      SCHED_TASK(update_batt_compass, 10, ...)
//   barometer.update()                  SCHED_TASK(update_altitude, 10, ...) (read_barometer)
// A scheduled task runs when the ticks since its last run reach 400 / rate (AP_Scheduler::run;
// the counter starts at 0 and tick() increments it before the tasks run, so the 50 Hz task first
// runs at the 8th loop and the 10 Hz ones at the 40th); the time budget is assumed sufficient.
// Within a tick the clock does not advance: SITL's loop delays (SIM_LOOP_DELAY 0, the 1 us after
// the tasks) and wait_for_sample's wait are no-ops, the tick happens at t_us.
//
// Parameters fixed, not exposed (code defaults unless stated): every EK3_, AHRS_, INS_, COMPASS_,
// GPS_, BARO_ parameter not in the record, with the X500's stored values GPS1_TYPE 100 (the
// SITL GPS, whose stand-in is backend_gps.cpp); INS_ACCOFFS 0.001 is in the record. The vehicle:
// Copter, 400 Hz loop (SCHED_LOOP_RATE), one IMU, one barometer, one compass, one GPS (the
// plant's sensors: SIM_IMU_COUNT 1, SIM_BARO_COUNT 1, SIM_MAG1_DEVID only).
#include "module_protocol.h"

#include <new>
#include <string.h>

#include <AP_AHRS/AP_AHRS.h>
#include <AP_AHRS/AP_AHRS_NavEKF3.h>
#include <AP_AHRS/AP_AHRS_View.h>
#include <AP_Baro/AP_Baro.h>
#include <AP_Compass/AP_Compass.h>
#include <AP_DAL/AP_DAL.h>
#include <AP_GPS/AP_GPS.h>
#include <AP_InertialSensor/AP_InertialSensor.h>
#include <AP_NavEKF3/AP_NavEKF3.h>

#include "harness_cut.h"

// --- private members reached by the rule that access is not checked in the template arguments of
// an explicit instantiation (as the mixer's adapter does for AP_MotorsMatrix::_singleton)
#define HARNESS_STATIC_ACCESS(NAME, TYPE, MEMBER)                                    \
    TYPE *harness_static_##NAME();                                                    \
    template <TYPE *P> struct HarnessStatic_##NAME {                                  \
        friend TYPE *harness_static_##NAME() { return P; }                            \
    };                                                                                \
    template struct HarnessStatic_##NAME<&MEMBER>;

HARNESS_STATIC_ACCESS(ins_singleton, AP_InertialSensor *, AP_InertialSensor::_singleton)
HARNESS_STATIC_ACCESS(compass_singleton, Compass *, Compass::_singleton)
HARNESS_STATIC_ACCESS(gps_singleton, AP_GPS *, AP_GPS::_singleton)
HARNESS_STATIC_ACCESS(baro_singleton, AP_Baro *, AP_Baro::_singleton)
HARNESS_STATIC_ACCESS(ahrs_singleton, AP_AHRS *, AP_AHRS::_singleton)
HARNESS_STATIC_ACCESS(dal_singleton, AP_DAL *, AP_DAL::_singleton)
HARNESS_STATIC_ACCESS(ekf3, NavEKF3, AP_AHRS_NavEKF3::EKF3)

NavEKF3 *harness_ekf3_object()
{
    return harness_static_ekf3();
}

// AP_AHRS_NavEKF3::started (private): the EKF3 backend's InitialiseFilter has succeeded
bool &harness_ekf3_started(AP_AHRS_NavEKF3 &o);
template <bool AP_AHRS_NavEKF3::*P> struct HarnessEkf3Started {
    friend bool &harness_ekf3_started(AP_AHRS_NavEKF3 &o) { return o.*P; }
};
template struct HarnessEkf3Started<&AP_AHRS_NavEKF3::started>;

// the vehicle's objects: Copter is a static object, so they start in zeroed storage
alignas(AP_GPS) static unsigned char gps_storage[sizeof(AP_GPS)];
alignas(AP_Baro) static unsigned char baro_storage[sizeof(AP_Baro)];
alignas(Compass) static unsigned char compass_storage[sizeof(Compass)];
alignas(AP_InertialSensor) static unsigned char ins_storage[sizeof(AP_InertialSensor)];
alignas(AP_AHRS) static unsigned char ahrs_storage[sizeof(AP_AHRS)];
static AP_GPS *gps;
static AP_Baro *barometer;
static Compass *compass;
static AP_InertialSensor *ins;
static AP_AHRS *ahrs;
// Copter::allocate_motors: ahrs_view = ahrs.create_view(ROTATION_NONE) (system.cpp:454); the
// attitude controller, the position controller and the navigation libraries are constructed on
// *ahrs_view and read it, not ahrs; AP_AHRS::update refreshes it at the end of every update
static AP_AHRS_View *ahrs_view;

static uint16_t tick_counter;      // AP_Scheduler::_tick_counter
static uint32_t loop_ticks;        // the same, 32 bits, for the output est_loop_ticks
static uint16_t last_run_gps, last_run_compass, last_run_baro;   // AP_Scheduler::_last_run[i]
static bool booted;

static const uint16_t LOOP_RATE_HZ = 400;   // SCHED_LOOP_RATE default for Copter

// Copter::load_parameters: the record's values, stored under their ArduPilot names, written over
// the code defaults as AP_Param::load_all loads a stored value (stubs_param.cpp)
static void set_params(const Params &p)
{
    harness_param_load("EK3_VELNE_M_NSE", float(p.ek3_velne_m_nse));
    harness_param_load("EK3_VELD_M_NSE", float(p.ek3_veld_m_nse));
    harness_param_load("EK3_VEL_I_GATE", float(p.ek3_vel_i_gate));
    harness_param_load("EK3_POSNE_M_NSE", float(p.ek3_posne_m_nse));
    harness_param_load("EK3_POS_I_GATE", float(p.ek3_pos_i_gate));
    harness_param_load("EK3_GLITCH_RAD", float(p.ek3_glitch_rad));
    harness_param_load("EK3_ALT_M_NSE", float(p.ek3_alt_m_nse));
    harness_param_load("EK3_HGT_I_GATE", float(p.ek3_hgt_i_gate));
    harness_param_load("EK3_HGT_DELAY", float(p.ek3_hgt_delay));
    harness_param_load("EK3_MAG_M_NSE", float(p.ek3_mag_m_nse));
    harness_param_load("EK3_MAG_CAL", float(p.ek3_mag_cal));
    harness_param_load("EK3_MAG_I_GATE", float(p.ek3_mag_i_gate));
    harness_param_load("EK3_GYRO_P_NSE", float(p.ek3_gyro_p_nse));
    harness_param_load("EK3_ACC_P_NSE", float(p.ek3_acc_p_nse));
    harness_param_load("EK3_GBIAS_P_NSE", float(p.ek3_gbias_p_nse));
    harness_param_load("EK3_ABIAS_P_NSE", float(p.ek3_abias_p_nse));
    harness_param_load("EK3_MAGE_P_NSE", float(p.ek3_mage_p_nse));
    harness_param_load("EK3_MAGB_P_NSE", float(p.ek3_magb_p_nse));
    harness_param_load("EK3_GPS_CHECK", float(p.ek3_gps_check));
    harness_param_load("EK3_CHECK_SCALE", float(p.ek3_check_scale));
    harness_param_load("EK3_NOAID_M_NSE", float(p.ek3_noaid_m_nse));
    harness_param_load("EK3_YAW_M_NSE", float(p.ek3_yaw_m_nse));
    harness_param_load("EK3_YAW_I_GATE", float(p.ek3_yaw_i_gate));
    harness_param_load("EK3_TAU_OUTPUT", float(p.ek3_tau_output));
    harness_param_load("EK3_ACC_BIAS_LIM", float(p.ek3_acc_bias_lim));
    harness_param_load("EK3_MAG_EF_LIM", float(p.ek3_mag_ef_lim));
    harness_param_load("EK3_ERR_THRESH", float(p.ek3_err_thresh));
    harness_param_load("EK3_IMU_MASK", float(p.ek3_imu_mask));
    harness_param_load("AHRS_EKF_TYPE", float(p.ahrs_ekf_type));
    harness_param_load("AHRS_TRIM_X", float(p.ahrs_trim_x));
    harness_param_load("AHRS_TRIM_Y", float(p.ahrs_trim_y));
    harness_param_load("INS_GYRO_FILTER", float(p.ins_gyro_filter));
    harness_param_load("INS_ACCEL_FILTER", float(p.ins_accel_filter));
    harness_param_load("INS_GYR_CAL", float(p.ins_gyr_cal));
    harness_param_load("INS_ACCOFFS_X", float(p.ins_accoffs_x));
    harness_param_load("INS_ACCOFFS_Y", float(p.ins_accoffs_y));
    harness_param_load("INS_ACCOFFS_Z", float(p.ins_accoffs_z));
    harness_param_load("INS_GYROFFS_X", float(p.ins_gyroffs_x));
    harness_param_load("INS_GYROFFS_Y", float(p.ins_gyroffs_y));
    harness_param_load("INS_GYROFFS_Z", float(p.ins_gyroffs_z));
    harness_param_load("COMPASS_USE", float(p.compass_use));
    harness_param_load("COMPASS_AUTODEC", float(p.compass_autodec));
    harness_param_load("COMPASS_DEC", float(p.compass_dec));
    harness_param_load("GPS1_DELAY_MS", float(p.gps1_delay_ms));
}

// the boot: the estimator's part of Copter::init_ardupilot, in its order (see the head comment)
static void boot()
{
    barometer->init();
    ahrs_view = ahrs->create_view(ROTATION_NONE);   // Copter::allocate_motors
    gps->init();
    compass->init();
    barometer->calibrate();
    // Copter::startup_INS_ground
    ahrs->init();
    ahrs->set_vehicle_class(AP_AHRS::VehicleClass::COPTER);
    ins->init(LOOP_RATE_HZ);
    ahrs->reset();
}

template <typename T>
static T *rebuild(unsigned char *storage, size_t size)
{
    memset(storage, 0, size);
    return reinterpret_cast<T *>(storage);
}

void module_init(const Params &p)
{
    harness_boot_abandon();          // a boot thread of the previous case, if any, never resumes
    harness_reset_cut();             // clock 0, timer processes, stored-parameter set, errors
    tick_counter = last_run_gps = last_run_compass = last_run_baro = 0;
    loop_ticks = 0;
    booted = false;
    ahrs_view = nullptr;   // the previous case's view is abandoned with its AHRS

    // the singletons the constructors check or create
    *harness_static_ins_singleton() = nullptr;
    *harness_static_compass_singleton() = nullptr;
    *harness_static_gps_singleton() = nullptr;
    *harness_static_baro_singleton() = nullptr;
    *harness_static_ahrs_singleton() = nullptr;
    *harness_static_dal_singleton() = nullptr;   // the previous case's DAL is abandoned

    // EKF3 is a static member of AP_AHRS_NavEKF3, built before main; rebuild it in place
    NavEKF3 *ekf3 = harness_static_ekf3();
    memset((void *)ekf3, 0, sizeof(NavEKF3));
    new (ekf3) NavEKF3();

    // AP_Vehicle's members, in declaration order (AP_Vehicle.h:352-419)
    gps = new (rebuild<AP_GPS>(gps_storage, sizeof gps_storage)) AP_GPS();
    barometer = new (rebuild<AP_Baro>(baro_storage, sizeof baro_storage)) AP_Baro();
    compass = new (rebuild<Compass>(compass_storage, sizeof compass_storage)) Compass();
    ins = new (rebuild<AP_InertialSensor>(ins_storage, sizeof ins_storage)) AP_InertialSensor();
    ahrs = new (rebuild<AP_AHRS>(ahrs_storage, sizeof ahrs_storage)) AP_AHRS();

    // Copter::load_parameters: the stored values over the code defaults
    set_params(p);
    // the X500's stored value outside the record (storage-x500.txt): the SITL GPS
    harness_param_load("GPS1_TYPE", 100);

    harness_boot_start(boot);
}

// the vehicle's calls on the estimator, issued in the previous tick after read_AHRS
static void apply_commands(const Input &in)
{
    harness_set_vehicle_state(in.armed, in.likely_flying);
    if (in.cmd_estimator_set_takeoff_expected) {
        ahrs->set_takeoff_expected(in.cmd_estimator_set_takeoff_expected_b);
    }
    if (in.cmd_estimator_set_touchdown_expected) {
        ahrs->set_touchdown_expected(in.cmd_estimator_set_touchdown_expected_b);
    }
    if (in.cmd_estimator_set_home) {
        const Location loc{in.cmd_estimator_set_home_lat_e7, in.cmd_estimator_set_home_lon_e7,
                           in.cmd_estimator_set_home_alt_cm, Location::AltFrame::ABSOLUTE};
        (void)ahrs->set_home(loc);   // Copter::set_home reports a false return as a failure
    }
    if (in.cmd_estimator_reset_height_datum) {
        ahrs->resetHeightDatum();
    }
    if (in.cmd_estimator_request_yaw_reset) {
        ahrs->request_yaw_reset();
    }
    // Copter::update_ekf_terrain_height_stable (baro_ground_effect.cpp:29-39): the real call; it
    // passes the state to EKF3 (setTerrainHgtStable) only when it changes (AP_AHRS.cpp:1809-1830)
    if (in.cmd_estimator_set_terrain_hgt_stable) {
        ahrs->set_terrain_hgt_stable(in.cmd_estimator_set_terrain_hgt_stable_stable);
    }
}

// a scheduled task of rate_hz is due (AP_Scheduler::run, with time always available)
static bool due(uint16_t &last_run, uint16_t rate_hz)
{
    const uint16_t dt = tick_counter - last_run;
    if (dt < LOOP_RATE_HZ / rate_hz) {
        return false;
    }
    last_run = tick_counter;
    return true;
}

static void read_outputs(Output &out)
{
    out.est_booted = booted;
    out.est_loop_ticks = loop_ticks;
    out.est_config_error = harness_config_error();
    out.est_internal_errors = harness_internal_error_count();
    if (!booted) {
        return;   // every other field 0 (the protocol zeroes the record)
    }
    // what the controllers read, from the view (identical rotation)
    const AP_AHRS_View &view = *ahrs_view;
    const Vector3f g = view.get_gyro_latest();
    out.gyro_x = g.x; out.gyro_y = g.y; out.gyro_z = g.z;
    Quaternion q;
    view.get_quat_body_to_ned(q);
    out.est_q1 = q.q1; out.est_q2 = q.q2; out.est_q3 = q.q3; out.est_q4 = q.q4;
    out.est_roll = view.get_roll_rad();
    out.est_pitch = view.get_pitch_rad();
    out.est_yaw = view.get_yaw_rad();
    out.est_sin_yaw = view.sin_yaw();
    out.est_cos_yaw = view.cos_yaw();
    out.est_cos_roll = view.cos_roll();
    out.est_cos_pitch = view.cos_pitch();
    Vector3p pos;
    out.est_pos_ok = ahrs->get_relative_position_NED_origin(pos);
    if (out.est_pos_ok) {
        out.est_pos_n = float(pos.x); out.est_pos_e = float(pos.y); out.est_pos_d = float(pos.z);
    }
    Vector3f vel;
    out.est_vel_ok = ahrs->get_velocity_NED(vel);
    if (out.est_vel_ok) {
        out.est_vel_n = vel.x; out.est_vel_e = vel.y; out.est_vel_d = vel.z;
    }
    float rate_d = 0;
    out.est_pos_rate_d_ok = ahrs->get_vert_pos_rate_D(rate_d);
    out.est_pos_rate_d = out.est_pos_rate_d_ok ? rate_d : 0.0f;
    const Vector3f &eg = view.get_gyro();
    out.est_gyro_x = eg.x; out.est_gyro_y = eg.y; out.est_gyro_z = eg.z;
    const Vector3f &go = ins->get_gyro_offsets(0);
    out.est_gyro_offset_x = go.x; out.est_gyro_offset_y = go.y; out.est_gyro_offset_z = go.z;
    const Vector3f &dr = ahrs->get_gyro_drift();
    out.est_gyro_drift_x = dr.x; out.est_gyro_drift_y = dr.y; out.est_gyro_drift_z = dr.z;
    const Vector3f &a = ahrs->get_accel();
    out.est_accel_x = a.x; out.est_accel_y = a.y; out.est_accel_z = a.z;
    const Vector3f &aef = ahrs->get_accel_ef();
    out.est_accel_ef_x = aef.x; out.est_accel_ef_y = aef.y; out.est_accel_ef_z = aef.z;
    Location origin;
    out.est_origin_ok = ahrs->get_origin(origin);
    if (out.est_origin_ok) {
        out.est_origin_lat_e7 = origin.lat;
        out.est_origin_lon_e7 = origin.lng;
        out.est_origin_alt_cm = origin.alt;
    }
    out.est_home_set = ahrs->home_is_set();
    const Location &home = ahrs->get_home();
    out.est_home_lat_e7 = home.lat; out.est_home_lon_e7 = home.lng; out.est_home_alt_cm = home.alt;
    Location loc;
    out.est_loc_ok = ahrs->get_location(loc);
    if (out.est_loc_ok) {
        out.est_loc_lat_e7 = loc.lat; out.est_loc_lon_e7 = loc.lng; out.est_loc_alt_cm = loc.alt;
    }
    out.est_healthy = ahrs->healthy();
    out.est_initialised = ahrs->initialised();
    out.est_have_inertial_nav = ahrs->have_inertial_nav();
    nav_filter_status st {};
    if (ahrs->get_filter_status_for_configured_backend(st)) {
        out.est_filter_status = st.value;
    }
    out.est_ekf_attitude = st.flags.attitude;
    out.est_ekf_horiz_vel = st.flags.horiz_vel;
    out.est_ekf_vert_pos = st.flags.vert_pos;
    out.est_ekf_horiz_pos_abs = st.flags.horiz_pos_abs;
    out.est_ekf_const_pos_mode = st.flags.const_pos_mode;
    out.est_ekf_using_gps = st.flags.using_gps;
    Vector3f mag_var;
    out.est_variances_ok = ahrs->get_variances_for_configured_backend(
        out.est_vel_variance, out.est_pos_variance, out.est_hgt_variance, mag_var,
        out.est_tas_variance);
    out.est_mag_variance_x = mag_var.x;
    out.est_mag_variance_y = mag_var.y;
    out.est_mag_variance_z = mag_var.z;
    out.est_pos_ne_reset_count = ahrs->get_position_NE_reset_count();
    out.est_pos_d_reset_count = ahrs->get_position_D_reset_count();
    out.est_yaw_reset_count = ahrs->get_yaw_reset_count();
    out.est_attitude_reset_count = ahrs->get_last_attitude_reset_count();
    out.est_gain_scaler_xy = ahrs->get_control_gain_scaler_XY();
    out.est_gain_scaler_z = ahrs->get_control_gain_scaler_Z();
    out.est_gnd_spd_limit = ahrs->get_control_ground_speed_limit_ms();   // for the loiter stage
    out.air_density_ratio = ahrs->get_air_density_ratio();
    out.est_baro_alt = barometer->get_altitude();
    out.est_gps_status = uint32_t(gps->status());
    out.est_gps_num_sats = gps->num_sats();
    out.est_ekf_started = harness_ekf3_started(ahrs->ekf3);
    // added in h-sup (round 3) for the supervisor's arming checks and telemetry: what only the
    // estimator knows
    char msg[50];
    out.est_prearm_ok = ahrs->pre_arm_check(true, msg, sizeof msg);
    out.est_ins_accel_healthy = ins->get_accel_health_all();
    out.est_ins_gyro_healthy = ins->get_gyro_health_all();
    out.est_baro_healthy = barometer->all_healthy();
    out.est_gps_healthy = gps->is_healthy(0);
    out.est_gps_hdop = gps->get_hdop();
    out.est_gps_vdop = gps->get_vdop();
    const Vector3f vibe = ins->get_vibration_levels(0);
    out.est_vibe_x = vibe.x; out.est_vibe_y = vibe.y; out.est_vibe_z = vibe.z;
    out.est_accel_clip_count = ins->get_accel_clip_count(0);
    Vector3f vi, pi, mi;
    float ti = 0, yi = 0;
    out.est_innov_ok = ahrs->get_innovations(vi, pi, mi, ti, yi);
    out.est_innov_vel_n = vi.x; out.est_innov_vel_e = vi.y; out.est_innov_vel_d = vi.z;
    out.est_innov_pos_n = pi.x; out.est_innov_pos_e = pi.y; out.est_innov_pos_d = pi.z;
}

// the tick's samples, for the driver stand-ins
static void set_tick(const Input &in)
{
    HarnessTick &t = harness_tick;
    t.t_us = in.t_us;
    const float a[3][3] = {{in.imu0_ax, in.imu0_ay, in.imu0_az}, {in.imu1_ax, in.imu1_ay, in.imu1_az},
                           {in.imu2_ax, in.imu2_ay, in.imu2_az}};
    const float g[3][3] = {{in.imu0_gx, in.imu0_gy, in.imu0_gz}, {in.imu1_gx, in.imu1_gy, in.imu1_gz},
                           {in.imu2_gx, in.imu2_gy, in.imu2_gz}};
    memcpy(t.accel, a, sizeof a);
    memcpy(t.gyro, g, sizeof g);
    t.baro_fresh = in.baro_fresh;
    t.baro_pa = in.baro_pa;
    t.baro_degc = in.baro_degc;
    t.mag_fresh = in.mag_fresh;
    t.mag[0] = in.mag_x; t.mag[1] = in.mag_y; t.mag[2] = in.mag_z;
    t.gps_fresh = in.gps_fresh;
    t.gps_lat_e7 = in.gps_lat_e7;
    t.gps_lon_e7 = in.gps_lon_e7;
    t.gps_alt = in.gps_alt;
    t.gps_vel[0] = in.gps_vn; t.gps_vel[1] = in.gps_ve; t.gps_vel[2] = in.gps_vd;
}

bool harness_est_text_pop(char *buf, uint8_t &severity);   // stubs_logger.cpp
static uint32_t text_seq;

// one queued status text per tick into est_text_* (est_text_seq counts the texts handed over)
static void text_out(Output &out)
{
    char buf[51];
    uint8_t sev = 0;
    uint32_t w[13] = {};
    out.est_text_len = 0;
    if (harness_est_text_pop(buf, sev)) {
        const size_t n = strnlen(buf, 50);
        for (size_t k = 0; k < n; k++) {
            w[k / 4] |= uint32_t(uint8_t(buf[k])) << (8 * (k % 4));
        }
        text_seq++;
        out.est_text_len = uint32_t(n);
        out.est_text_severity = sev;
    }
    out.est_text_seq = text_seq;
    for (unsigned k = 0; k < 13; k++) {
        (&out.est_text_w00)[k] = w[k];
    }
}

void module_step(const Input &in, Output &out)
{
    harness_set_time(in.t_us);
    set_tick(in);
    harness_gps_receive();           // a fix waits in the GPS driver until gps.update() reads it
    harness_run_timer_processes();   // the drivers' timers take the tick's samples

    if (!booted) {
        booted = harness_boot_resume();
        read_outputs(out);
        text_out(out);
        return;
    }

    // one loop of AP_Scheduler::loop: tick(), then the tasks in Copter's table order
    tick_counter++;
    loop_ticks++;
    apply_commands(in);
    ins->update();
    ahrs->update(true);
    if (due(last_run_gps, 50)) {
        gps->update();
    }
    if (due(last_run_compass, 10)) {
        // Copter::update_batt_compass: battery.read() first (outside), then, if available,
        // set_throttle and set_voltage (motor-interference compensation, COMPASS_MOTCT 0: unused)
        if (compass->available()) {
            compass->read();
        }
    }
    if (due(last_run_baro, 10)) {
        barometer->update();   // Copter::read_barometer
    }
    read_outputs(out);
    text_out(out);
}
