/* cpp2lean reference vehicle: the estimation output (--est FILE; REFERENCE.md "Estimation output
   (Phase 3)").

   One line per protocol step, written when the step's output line is written (after the vehicle has
   run for that step, just before the next input line is consumed): the estimator's outputs (AP_AHRS,
   the primary EKF3 core, every EKF3 core's state vector and digests of its covariance, output
   predictor, IMU buffer and EKFGSF_yaw bank) and the inputs that the rest of the vehicle gives the
   estimator (the scheduler tasks that ran, the armed flag, the flying flag, home, ...), so that a
   replay of the estimator on the recorded sensor lines can be compared with the reference, step by
   step, bit for bit. Every float and double is the hexadecimal bit pattern (big-endian digit order,
   8 or 16 digits), as in the protocol.

   The probe only reads (const getters and data members); it never calls a function that changes the
   vehicle's state, so the protocol output is the same with and without --est. It reads private
   members of ArduPilot classes, so this file alone is compiled with -fno-access-control
   (reference/build.py); no ArduPilot file is changed. */

#include <AP_HAL/AP_HAL.h>
#include <AP_AHRS/AP_AHRS.h>
#include <AP_NavEKF3/AP_NavEKF3.h>
#include <AP_NavEKF3/AP_NavEKF3_core.h>
#include <AP_NavEKF/EKFGSF_yaw.h>
#include <AP_Scheduler/AP_Scheduler.h>
#include <AP_Vehicle/AP_Vehicle.h>
#include <AP_Baro/AP_Baro.h>
#include <AP_Compass/AP_Compass.h>
#include <AP_InertialSensor/AP_InertialSensor.h>
#include <AP_GPS/AP_GPS.h>
#include <AP_Motors/AP_Motors_Class.h>
#include <AP_BattMonitor/AP_BattMonitor.h>
#include "../../build/reference/ap/ArduCopter/GCS_Copter.h"
#include <stdlib.h>

#include <stdio.h>
#include <string.h>
#include <string>
#include <vector>
#include <algorithm>

#include "lockstep.h"

extern const AP_HAL::HAL& hal;

namespace EstProbe {

static FILE *f;
static std::string buf;
static bool header_done;
static std::vector<uint16_t> last_run_snap;
static uint32_t tick_snap;
static bool tick_snap_valid;

// --- formatting ---------------------------------------------------------------------------------
static void put(const char *s) { buf += s; }
static void putu(unsigned long long v) { char t[32]; snprintf(t, sizeof(t), "%llu", v); buf += t; }
static void puti(long long v) { char t[32]; snprintf(t, sizeof(t), "%lld", v); buf += t; }
static void putb(bool b) { buf += b ? '1' : '0'; }
static void putf(float x) { uint32_t u; memcpy(&u, &x, 4); char t[16]; snprintf(t, sizeof(t), "%08x", u); buf += t; }
static void putf(double x) { uint64_t u; memcpy(&u, &x, 8); char t[24]; snprintf(t, sizeof(t), "%016llx", (unsigned long long)u); buf += t; }
static void key(const char *k) { buf += ' '; buf += k; buf += '='; }
static void comma() { buf += ','; }
template <typename T> static void putv3(const Vector3<T> &v) { putf(v.x); comma(); putf(v.y); comma(); putf(v.z); }
static void putloc(const Location &l) { puti(l.lat); comma(); puti(l.lng); comma(); puti(l.alt); comma(); putu(unsigned(l.get_alt_frame())); }

// --- FNV-1a 64 over the little-endian bytes of the values, in the documented order ------------------
struct Fnv {
    uint64_t h = 0xcbf29ce484222325ULL;
    void byte(uint8_t b) { h ^= b; h *= 0x100000001b3ULL; }
    void u(uint64_t v, int n) { for (int i = 0; i < n; i++) { byte(uint8_t(v >> (8 * i))); } }
    void u8(uint8_t v) { u(v, 1); }
    void b(bool v) { u(v ? 1 : 0, 1); }
    void u32(uint32_t v) { u(v, 4); }
    void f(float x) { uint32_t w; memcpy(&w, &x, 4); u(w, 4); }
    void f(double x) { uint64_t w; memcpy(&w, &x, 8); u(w, 8); }
    template <typename T> void v3(const Vector3<T> &v) { f(v.x); f(v.y); f(v.z); }
    template <typename T> void q(const QuaternionT<T> &v) { f(v.q1); f(v.q2); f(v.q3); f(v.q4); }
};
static void putdigest(const Fnv &d) { char t[24]; snprintf(t, sizeof(t), "%016llx", (unsigned long long)d.h); buf += t; }

// the ring buffer behind an EKF_IMU_buffer_t (a private base: readable with -fno-access-control)
template <typename T> static const ekf_imu_buffer &imu_base(const EKF_IMU_buffer_t<T> &b) { return b; }

static void digest_output(Fnv &d, const NavEKF3_core::output_elements &o) { d.q(o.quat); d.v3(o.velocity); d.v3(o.position); }

// --- the scheduler's merged task table (AP_Scheduler::run's order) -------------------------------------
static const AP_Scheduler::Task *task_at(const AP_Scheduler &s, uint8_t idx)
{
    uint8_t vo = 0, co = 0;
    for (uint8_t i = 0; i < s._num_tasks; i++) {
        bool veh;
        if (vo < s._num_vehicle_tasks && co < s._num_common_tasks) {
            veh = s._vehicle_tasks[vo].priority <= s._common_tasks[co].priority;
        } else {
            veh = vo < s._num_vehicle_tasks;
        }
        const AP_Scheduler::Task &t = veh ? s._vehicle_tasks[vo++] : s._common_tasks[co++];
        if (i == idx) {
            return &t;
        }
    }
    return nullptr;
}

static void write_header(const AP_Scheduler &s)
{
    std::string h = "# tasks";
    for (uint8_t i = 0; i < s._num_tasks; i++) {
        const AP_Scheduler::Task *t = task_at(s, i);
        char tmp[160];
        snprintf(tmp, sizeof(tmp), " %u=%s@%u", unsigned(i), t ? t->name : "?", t ? unsigned(t->priority) : 0U);
        h += tmp;
    }
    h += '\n';
    fwrite(h.data(), 1, h.size(), f);
}

bool open(const char *path)
{
    f = fopen(path, "w");
    return f != nullptr;
}

bool enabled() { return f != nullptr; }

void close()
{
    if (f != nullptr) {
        fflush(f);
    }
}

// state of the line being run: recorded when the line is consumed
static bool line_init;
static int line_where;

void consumed(bool init, int where)
{
    line_init = init;
    line_where = where;
}

// the sensor stand-ins' events of the step being run (est_input.h)
static uint32_t line_events;
void event(uint8_t ev) { line_events |= ev; }

// the parameters of the estimator's World as the vehicle holds them (the first line: after AP_Param::load_all, before
// the front ends' init): the front ends', NavEKF3's and its source selection's; `# params` and `object.member=value` in
// each object's var_info order
static void write_params()
{
    std::string h = "# params";
    char t[160];
    auto f32 = [&](const char *name, float v) { uint32_t u; memcpy(&u, &v, 4); snprintf(t, sizeof(t), " %s=%08x", name, u); h += t; };
    auto i64 = [&](const char *name, long long v) { snprintf(t, sizeof(t), " %s=%lld", name, v); h += t; };
    char nm[120];
    const AP_Baro &b = AP::baro();
    for (uint8_t i = 0; i < BARO_MAX_INSTANCES; i++) {
        snprintf(nm, sizeof(nm), "barometer.sensors[%u].ground_pressure", unsigned(i)); f32(nm, b.sensors[i].ground_pressure.get());
        snprintf(nm, sizeof(nm), "barometer.sensors[%u].bus_id", unsigned(i)); i64(nm, b.sensors[i].bus_id.get());
    }
    f32("barometer._alt_offset", b._alt_offset.get());
    f32("barometer._field_elevation", b._field_elevation.get());
    i64("barometer._primary_baro", b._primary_baro.get());
    i64("barometer._ext_bus", b._ext_bus.get());
    f32("barometer._specific_gravity", b._specific_gravity.get());
    f32("barometer._user_ground_temperature", b._user_ground_temperature.get());
    i64("barometer._filter_range", b._filter_range.get());
    f32("barometer._alt_error_max", b._alt_error_max.get());
    i64("barometer._options", b._options.get());
    const Compass &c = AP::compass();
    i64("compass._enabled", c._enabled.get());
    i64("compass._learn", c._learn.get());
    f32("compass._declination", c._declination.get());
    i64("compass._auto_declination", c._auto_declination.get());
    i64("compass._motor_comp_type", c._motor_comp_type.get());
    i64("compass._rotate_auto", c._rotate_auto.get());
    for (uint8_t i = 0; i < COMPASS_MAX_INSTANCES; i++) {
        const Compass::mag_state &m = c._state._priv_instance[i];
        snprintf(nm, sizeof(nm), "compass._state._priv_instance[%u].", unsigned(i));
        std::string pre = nm;
        i64((pre + "external").c_str(), m.external.get());
        i64((pre + "orientation").c_str(), m.orientation.get());
        const Vector3f *vs[] = {&m.offset.get(), &m.diagonals.get(), &m.offdiagonals.get(), &m.motor_compensation.get()};
        const char *vn[] = {"offset", "diagonals", "offdiagonals", "motor_compensation"};
        for (uint8_t k = 0; k < 4; k++) {
            f32((pre + vn[k] + ".x").c_str(), vs[k]->x);
            f32((pre + vn[k] + ".y").c_str(), vs[k]->y);
            f32((pre + vn[k] + ".z").c_str(), vs[k]->z);
        }
        f32((pre + "scale_factor").c_str(), m.scale_factor.get());
        i64((pre + "dev_id").c_str(), m.dev_id.get());
    }
    for (uint8_t i = 0; i < COMPASS_MAX_INSTANCES; i++) {
        snprintf(nm, sizeof(nm), "compass._use_for_yaw._priv_instance[%u]", unsigned(i)); i64(nm, c._use_for_yaw._priv_instance[i].get());
        snprintf(nm, sizeof(nm), "compass._priority_did_stored_list._priv_instance[%u]", unsigned(i)); i64(nm, c._priority_did_stored_list._priv_instance[i].get());
    }
    for (uint8_t i = 0; i < COMPASS_MAX_UNREG_DEV; i++) {
        snprintf(nm, sizeof(nm), "compass.extra_dev_id[%u]", unsigned(i)); i64(nm, c.extra_dev_id[i].get());
    }
    i64("compass._offset_max", c._offset_max.get());
    i64("compass._driver_type_mask", c._driver_type_mask.get());
    i64("compass._filter_range", c._filter_range.get());
    i64("compass._options", c._options.get());
#if COMPASS_MOT_ENABLED
    i64("compass._per_motor.enable", c._per_motor.enable.get());
    f32("compass._per_motor.expo", c._per_motor.expo.get());
#endif
    // AP_InertialSensor and AP_GPS (README.md "Phase 3: AP_InertialSensor, AP_GPS and AP_NavEKF_Source"), in var_info order
    auto v3 = [&](const std::string &name, const Vector3f &v) { f32((name + ".x").c_str(), v.x); f32((name + ".y").c_str(), v.y); f32((name + ".z").c_str(), v.z); };
    const AP_InertialSensor &ins = AP::ins();
    for (uint8_t i = 0; i < INS_MAX_INSTANCES - INS_AUX_INSTANCES; i++) {
        snprintf(nm, sizeof(nm), "[%u]", unsigned(i));
        const std::string ix = nm;
        v3("ins._gyro_offset_old_param" + ix, ins._gyro_offset_old_param[i].get());
        v3("ins._accel_scale_old_param" + ix, ins._accel_scale_old_param[i].get());
        v3("ins._accel_offset_old_param" + ix, ins._accel_offset_old_param[i].get());
        i64(("ins._use_old_param" + ix).c_str(), ins._use_old_param[i].get());
        v3("ins._accel_pos_old_param" + ix, ins._accel_pos_old_param[i].get());
        i64(("ins._gyro_id_old_param" + ix).c_str(), ins._gyro_id_old_param[i].get());
        i64(("ins._accel_id_old_param" + ix).c_str(), ins._accel_id_old_param[i].get());
    }
    i64("ins._gyro_filter_cutoff", ins._gyro_filter_cutoff.get());
    i64("ins._accel_filter_cutoff", ins._accel_filter_cutoff.get());
    f32("ins._still_threshold", ins._still_threshold.get());
    i64("ins._gyro_cal_timing", ins._gyro_cal_timing.get());
    i64("ins._trim_option", ins._trim_option.get());
    i64("ins._acc_body_aligned", ins._acc_body_aligned.get());
    i64("ins._fast_sampling_mask", ins._fast_sampling_mask.get());
    i64("ins._enable_mask", ins._enable_mask.get());
    i64("ins._fast_sampling_rate", ins._fast_sampling_rate.get());
    i64("ins.raw_logging_options", ins.raw_logging_options.get());
    const AP_GPS &g = AP::gps();
    i64("gps._navfilter", g._navfilter.get());
    i64("gps._auto_switch", g._auto_switch.get());
    i64("gps._sbas_mode", int(g._sbas_mode.get()));
    i64("gps._min_elevation", g._min_elevation.get());
    i64("gps._inject_to", g._inject_to.get());
    i64("gps._sbp_logmask", g._sbp_logmask.get());
    i64("gps._raw_data", g._raw_data.get());
    i64("gps._save_config", g._save_config.get());
    i64("gps._auto_config", g._auto_config.get());
    i64("gps._blend_mask", g._blend_mask.get());
    i64("gps._driver_options", g._driver_options.get());
    i64("gps._primary", g._primary.get());
    for (uint8_t i = 0; i < GPS_MAX_INSTANCES; i++) {
        snprintf(nm, sizeof(nm), "gps.params[%u].", unsigned(i));
        const std::string pre = nm;
        const AP_GPS::Params &gp = g.params[i];
        i64((pre + "type").c_str(), int(gp.type.get()));
        i64((pre + "gnss_mode").c_str(), gp.gnss_mode.get());
        i64((pre + "rate_ms").c_str(), gp.rate_ms.get());
        v3(pre + "antenna_offset", gp.antenna_offset.get());
        i64((pre + "delay_ms").c_str(), gp.delay_ms.get());
        i64((pre + "com_port").c_str(), gp.com_port.get());
    }
    // NavEKF3 (README.md "Phase 3: the estimator World and the EKF3 replay"): every parameter of its var_info and
    // var_info2, in table order, then those of its source selection `sources` (AP_NavEKF_Source)
    const NavEKF3 &ekf = AP_AHRS_NavEKF3::EKF3;
    i64("EKF3._enable", (long long)ekf._enable.get());
    f32("EKF3._gpsHorizVelNoise", ekf._gpsHorizVelNoise.get());
    f32("EKF3._gpsVertVelNoise", ekf._gpsVertVelNoise.get());
    i64("EKF3._gpsVelInnovGate", (long long)ekf._gpsVelInnovGate.get());
    f32("EKF3._gpsHorizPosNoise", ekf._gpsHorizPosNoise.get());
    i64("EKF3._gpsPosInnovGate", (long long)ekf._gpsPosInnovGate.get());
    i64("EKF3._gpsGlitchRadiusMax", (long long)ekf._gpsGlitchRadiusMax.get());
    f32("EKF3._baroAltNoise", ekf._baroAltNoise.get());
    i64("EKF3._hgtInnovGate", (long long)ekf._hgtInnovGate.get());
    i64("EKF3._hgtDelay_ms", (long long)ekf._hgtDelay_ms.get());
    f32("EKF3._magNoise", ekf._magNoise.get());
    i64("EKF3._magCal", (long long)ekf._magCal.get());
    i64("EKF3._magInnovGate", (long long)ekf._magInnovGate.get());
    f32("EKF3._easNoise", ekf._easNoise.get());
    i64("EKF3._tasInnovGate", (long long)ekf._tasInnovGate.get());
    f32("EKF3._rngNoise", ekf._rngNoise.get());
    i64("EKF3._rngInnovGate", (long long)ekf._rngInnovGate.get());
    f32("EKF3._maxFlowRate", ekf._maxFlowRate.get());
    f32("EKF3._flowNoise", ekf._flowNoise.get());
    i64("EKF3._flowInnovGate", (long long)ekf._flowInnovGate.get());
    i64("EKF3._flowDelay_ms", (long long)ekf._flowDelay_ms.get());
    f32("EKF3._gyrNoise", ekf._gyrNoise.get());
    f32("EKF3._accNoise", ekf._accNoise.get());
    f32("EKF3._gyroBiasProcessNoise", ekf._gyroBiasProcessNoise.get());
    f32("EKF3._accelBiasProcessNoise", ekf._accelBiasProcessNoise.get());
    f32("EKF3._windVelProcessNoise", ekf._windVelProcessNoise.get());
    f32("EKF3._wndVarHgtRateScale", ekf._wndVarHgtRateScale.get());
    i64("EKF3._gpsCheck", (long long)ekf._gpsCheck.get());
    i64("EKF3._imuMask", (long long)ekf._imuMask.get());
    i64("EKF3._gpsCheckScaler", (long long)ekf._gpsCheckScaler.get());
    f32("EKF3._noaidHorizNoise", ekf._noaidHorizNoise.get());
    i64("EKF3._betaMask", (long long)ekf._betaMask.get());
    f32("EKF3._yawNoise", ekf._yawNoise.get());
    i64("EKF3._yawInnovGate", (long long)ekf._yawInnovGate.get());
    i64("EKF3._tauVelPosOutput", (long long)ekf._tauVelPosOutput.get());
    f32("EKF3._magEarthProcessNoise", ekf._magEarthProcessNoise.get());
    f32("EKF3._magBodyProcessNoise", ekf._magBodyProcessNoise.get());
    i64("EKF3._useRngSwHgt", (long long)ekf._useRngSwHgt.get());
    f32("EKF3._terrGradMax", ekf._terrGradMax.get());
    f32("EKF3._rngBcnNoise", ekf._rngBcnNoise.get());
    i64("EKF3._rngBcnInnovGate", (long long)ekf._rngBcnInnovGate.get());
    i64("EKF3._rngBcnDelay_ms", (long long)ekf._rngBcnDelay_ms.get());
    f32("EKF3._useRngSwSpd", ekf._useRngSwSpd.get());
    f32("EKF3._accBiasLim", ekf._accBiasLim.get());
    i64("EKF3._magMask", (long long)ekf._magMask.get());
    i64("EKF3._originHgtMode", (long long)ekf._originHgtMode.get());
    f32("EKF3._visOdmVelErrMin", ekf._visOdmVelErrMin.get());
    f32("EKF3._visOdmVelErrMax", ekf._visOdmVelErrMax.get());
    f32("EKF3._wencOdmVelErr", ekf._wencOdmVelErr.get());
    i64("EKF3._flowUse", (long long)ekf._flowUse.get());
    f32("EKF3._hrt_filt_freq", ekf._hrt_filt_freq.get());
    i64("EKF3._mag_ef_limit", (long long)ekf._mag_ef_limit.get());
    i64("EKF3._gsfRunMask", (long long)ekf._gsfRunMask.get());
    i64("EKF3._gsfUseMask", (long long)ekf._gsfUseMask.get());
    f32("EKF3._flowNavGainHgt", ekf._flowNavGainHgt.get());
    i64("EKF3._gsfResetMaxCount", (long long)ekf._gsfResetMaxCount.get());
    f32("EKF3._err_thresh", ekf._err_thresh.get());
    i64("EKF3._affinity", (long long)ekf._affinity.get());
    f32("EKF3._ballisticCoef_x", ekf._ballisticCoef_x.get());
    f32("EKF3._ballisticCoef_y", ekf._ballisticCoef_y.get());
    f32("EKF3._dragObsNoise", ekf._dragObsNoise.get());
    f32("EKF3._momentumDragCoef", ekf._momentumDragCoef.get());
    f32("EKF3._ognmTestScaleFactor", ekf._ognmTestScaleFactor.get());
    f32("EKF3._baroGndEffectDeadZone", ekf._baroGndEffectDeadZone.get());
    i64("EKF3._primary_core", (long long)ekf._primary_core.get());
    i64("EKF3._log_level", (long long)ekf._log_level.get());
    f32("EKF3._gpsVAccThreshold", ekf._gpsVAccThreshold.get());
    i64("EKF3._options", (long long)ekf._options.get());
    for (uint8_t i = 0; i < AP_NAKEKF_SOURCE_SET_MAX; i++) {
        snprintf(nm, sizeof(nm), "EKF3.sources._source_set[%u].", unsigned(i));
        const std::string pre = nm;
        i64((pre + "posxy").c_str(), int(ekf.sources._source_set[i].posxy.get()));
        i64((pre + "velxy").c_str(), int(ekf.sources._source_set[i].velxy.get()));
        i64((pre + "posz").c_str(), int(ekf.sources._source_set[i].posz.get()));
        i64((pre + "velz").c_str(), int(ekf.sources._source_set[i].velz.get()));
        i64((pre + "yaw").c_str(), int(ekf.sources._source_set[i].yaw.get()));
    }
    i64("EKF3.sources._options", ekf.sources._options.get());
    // AP_AHRS (README.md "Phase 3: AP_AHRS in the estimator World, the full estimation replay"): every parameter of its
    // var_info, in table order (its DCM backend's parameters are references to these)
    const AP_AHRS &ah = AP::ahrs();
    f32("ahrs.gps_gain", ah.gps_gain.get());
    i64("ahrs._gps_use", (long long)int8_t(ah._gps_use.get()));
    f32("ahrs._kp_yaw", ah._kp_yaw.get());
    f32("ahrs._kp", ah._kp.get());
    i64("ahrs._wind_max", (long long)ah._wind_max.get());
    v3("ahrs._trim", ah._trim.get());
    i64("ahrs._board_orientation", (long long)ah._board_orientation.get());
    f32("ahrs.beta", ah.beta.get());
    i64("ahrs._gps_minsats", (long long)ah._gps_minsats.get());
    i64("ahrs._ekf_type", (long long)int8_t(ah._ekf_type.get()));
    i64("ahrs._options", (long long)ah._options.get());
    f32("ahrs._origin_lat", ah._origin_lat.get());
    f32("ahrs._origin_lon", ah._origin_lon.get());
    f32("ahrs._origin_alt", ah._origin_alt.get());
    h += '\n';
    fwrite(h.data(), 1, h.size(), f);
}
static bool params_done;

// the front ends' state of the step: AP_Baro (instances; for instance 0: healthy, pressure, temperature,
// altitude, ground pressure, last update ms) and Compass (count; for instance 0: healthy, field, last update
// us, offsets, dev id); AP_InertialSensor (`ins=`: gyro and accel counts, first usable gyro and accel, calibrating,
// delta time, last update us, have sample, next and last sample us; per IMU `imu<i>=`: accel, gyro, delta angle
// with its dt and validity, delta velocity with its dt and validity, accel and gyro health, gyro calibration ok,
// gyro offsets, accel offsets) and AP_GPS (`gps=`: sensors, primary; per receiver `gps<i>=`: status, location,
// velocity, ground speed and course, hdop, vdop, satellites, the accuracies with their flags, GPS week and ms of
// week, last message and last fix ms, vertical velocity flag, lag with its flag)
static void put_front_ends()
{
    const AP_Baro &b = AP::baro();
    key("baro"); putu(b.num_instances());
    if (b.num_instances() > 0) {
        comma(); putb(b.healthy(0)); comma(); putf(b.get_pressure(0)); comma(); putf(b.get_temperature(0));
        comma(); putf(b.get_altitude(0)); comma(); putf(b.get_ground_pressure(0)); comma(); putu(b.get_last_update(0));
    }
    const Compass &c = AP::compass();
    key("mag"); putu(c.get_count());
    if (c.get_count() > 0) {
        comma(); putb(c.healthy(0)); comma(); putv3(c.get_field(0)); comma(); putu(c.last_update_usec(0));
        comma(); putv3(c.get_offsets(0)); comma(); putu(c._state._priv_instance[0].dev_id.get());
    }
    const AP_InertialSensor &ins = AP::ins();
    key("ins"); putu(ins.get_gyro_count()); comma(); putu(ins.get_accel_count()); comma(); putu(ins.get_first_usable_gyro());
    comma(); putu(ins.get_first_usable_accel()); comma(); putb(ins.calibrating()); comma(); putf(ins.get_delta_time());
    comma(); putu(ins.get_last_update_usec()); comma(); putb(ins._have_sample); comma(); putu(ins._next_sample_usec);
    comma(); putu(ins._last_sample_usec);
    const uint8_t nimu = MAX(ins.get_gyro_count(), ins.get_accel_count());
    for (uint8_t i = 0; i < nimu; i++) {
        char k[8];
        snprintf(k, sizeof(k), "imu%u", unsigned(i));
        key(k); putv3(ins.get_accel(i)); comma(); putv3(ins.get_gyro(i));
        Vector3f dang, dvel;
        float dang_dt = 0, dvel_dt = 0;
        const bool dang_ok = ins.get_delta_angle(i, dang, dang_dt);
        const bool dvel_ok = ins.get_delta_velocity(i, dvel, dvel_dt);
        comma(); putv3(dang); comma(); putf(dang_dt); comma(); putb(dang_ok);
        comma(); putv3(dvel); comma(); putf(dvel_dt); comma(); putb(dvel_ok);
        comma(); putb(ins.get_accel_health(i)); comma(); putb(ins.get_gyro_health(i)); comma(); putb(ins.gyro_calibrated_ok(i));
        comma(); putv3(ins.get_gyro_offsets(i)); comma(); putv3(ins.get_accel_offsets(i));
    }
    const AP_GPS &g = AP::gps();
    key("gps"); putu(g.num_sensors()); comma(); putu(g.primary_sensor());
    for (uint8_t i = 0; i < GPS_MAX_RECEIVERS; i++) {
        char k[8];
        snprintf(k, sizeof(k), "gps%u", unsigned(i));
        key(k); putu(unsigned(g.status(i))); comma(); putloc(g.location(i)); comma(); putv3(g.velocity(i));
        comma(); putf(g.ground_speed(i)); comma(); putf(g.ground_course(i)); comma(); putu(g.get_hdop(i)); comma(); putu(g.get_vdop(i));
        comma(); putu(g.num_sats(i));
        float hacc = 0, vacc = 0, sacc = 0, lag = 0;
        const bool hok = g.horizontal_accuracy(i, hacc), vok = g.vertical_accuracy(i, vacc), sok = g.speed_accuracy(i, sacc);
        const bool lok = g.get_lag(i, lag);
        comma(); putb(hok); comma(); putf(hacc); comma(); putb(vok); comma(); putf(vacc); comma(); putb(sok); comma(); putf(sacc);
        comma(); putu(g.time_week(i)); comma(); putu(g.time_week_ms(i)); comma(); putu(g.last_message_time_ms(i));
        comma(); putu(g.last_fix_time_ms(i)); comma(); putb(g.have_vertical_velocity(i)); comma(); putb(lok); comma(); putf(lag);
    }
}

void emit(uint64_t t_us, uint32_t delay_callbacks)
{
    // (Phase 4 GCS, diagnosis only: environment CPP2LEAN_GCS_DUMP="FROM,TO") the bytes of GCS channel 0 after the
    // step, to stderr; the --est file and the protocol output are unchanged
    static long gd_from = -1, gd_to = -1, gd_step = 0;
    static bool gd_init;
    if (!gd_init) {
        gd_init = true;
        const char *e = getenv("CPP2LEAN_GCS_DUMP");
        if (e) {
            sscanf(e, "%ld,%ld", &gd_from, &gd_to);
        }
    }
    gd_step++;
    // (Phase 4 GCS: environment CPP2LEAN_PARAM_SNAPSHOT=STEP) every parameter after the step, to stderr: the values
    // non-GCS code set since boot (calibrations, the vehicle's set_default/set_and_save) are inputs of the GCS replay
    static std::vector<long> ps_steps;
    static bool ps_init;
    if (!ps_init) {
        ps_init = true;
        const char *e = getenv("CPP2LEAN_PARAM_SNAPSHOT");     // STEP[,STEP...]
        while (e && *e) {
            ps_steps.push_back(atol(e));
            e = strchr(e, ',');
            if (e) e++;
        }
    }
    if (std::find(ps_steps.begin(), ps_steps.end(), gd_step) != ps_steps.end()) {
        AP_Param::ParamToken token {};
        enum ap_var_type type;
        for (AP_Param *vp = AP_Param::first(&token, &type); vp != nullptr; vp = AP_Param::next_scalar(&token, &type)) {
            char name[AP_MAX_NAME_SIZE + 1] {};
            vp->copy_name_token(token, name, AP_MAX_NAME_SIZE, true);
            const float v = vp->cast_to_float(type);
            uint32_t bits;
            memcpy(&bits, &v, 4);
            fprintf(stderr, "paramsnap %ld %s %d %08x\n", gd_step, name, int(type), (unsigned)bits);
        }
    }
    if (gd_step >= gd_from && gd_step <= gd_to && gcs().num_gcs() > 0) {
        const uint8_t *p = (const uint8_t *)gcs().chan(0);
        fprintf(stderr, "gcsdump %ld ", gd_step);
        for (size_t i = 0; i < sizeof(GCS_MAVLINK_Copter); i++) {
            fprintf(stderr, "%02x", p[i]);
        }
        fprintf(stderr, "\n");
    }
    if (f == nullptr) {
        return;
    }
    buf.clear();
    if (!params_done) {
        write_params();
        params_done = true;
    }
    put("t="); putu(t_us);
    key("init"); putb(line_init);
    key("in"); puti(line_where);
    key("dcb"); putu(delay_callbacks);

    // ---------------- inputs from the rest of the vehicle ----------------
    AP_Scheduler *sp = AP_Scheduler::get_singleton();
    if (sp != nullptr && sp->_last_run != nullptr && sp->_num_tasks > 0) {
        const AP_Scheduler &s = *sp;
        if (!header_done) {
            write_header(s);
            header_done = true;
            last_run_snap.assign(s._num_tasks, 0);
            for (uint8_t i = 0; i < s._num_tasks; i++) {
                last_run_snap[i] = s._last_run[i];
            }
        }
        key("tick"); putu(s._tick_counter32);
        key("tasks");
        const bool ticked = tick_snap_valid ? s._tick_counter32 != tick_snap : s._tick_counter32 != 0;
        bool first = true;
        for (uint8_t i = 0; i < s._num_tasks; i++) {
            const bool ran = ticked && (s._last_run[i] != last_run_snap[i] || s._last_run[i] == s._tick_counter);
            if (ran) {
                if (!first) {
                    comma();
                }
                putu(i);
                first = false;
            }
            last_run_snap[i] = s._last_run[i];
        }
        if (first) {
            put("-");
        }
        tick_snap = s._tick_counter32;
        tick_snap_valid = true;
    }
    key("armed"); putb(hal.util->get_soft_armed());
    const AP_Vehicle *veh = AP_Vehicle::get_singleton();
    if (veh != nullptr) {
        key("flying"); putb(veh->likely_flying); comma(); putu(veh->_last_flying_ms);
    }
    const AP_AHRS &ahrs = AP::ahrs();
    key("tkd"); putb(ahrs.takeoff_expected); comma(); putu(ahrs.takeoff_expected_start_ms); comma();
    putb(ahrs.touchdown_expected); comma(); putu(ahrs.touchdown_expected_start_ms);
    key("thgt"); putu(unsigned(ahrs.terrainHgtStableState));
    key("home"); putb(ahrs.home_is_set()); comma(); putb(ahrs.home_is_locked()); comma(); putloc(ahrs.get_home());
    key("cfg"); putu(unsigned(ahrs.get_vehicle_class())); comma(); putb(ahrs.get_fly_forward()); comma();
    putu(unsigned(ahrs.configured_ekf_type())); comma(); putu(ahrs.get_posvelyaw_source_set()); comma(); putv3(ahrs.get_trim());
    const Compass &compass = AP::compass();
    key("comp"); putf(compass._thr);
#if COMPASS_MOT_ENABLED
    comma(); putf(compass._per_motor.voltage);
#endif
    const AP_Baro &baro = AP::baro();
    key("bgnd"); putu(baro.num_instances());
    for (uint8_t i = 0; i < baro.num_instances(); i++) {
        comma(); putf(baro.get_ground_pressure(i));
    }
    comma(); putf(baro.get_baro_drift_offset());

    // ---------------- AP_AHRS outputs ----------------
    Quaternion q;
    const bool q_ok = ahrs.get_quaternion(q);
    key("q"); putb(q_ok); comma(); putf(q.q1); comma(); putf(q.q2); comma(); putf(q.q3); comma(); putf(q.q4);
    key("rpy"); putf(ahrs.get_roll_rad()); comma(); putf(ahrs.get_pitch_rad()); comma(); putf(ahrs.get_yaw_rad());
    const Matrix3f &m = ahrs.get_rotation_body_to_ned();
    key("dcm"); putv3(m.a); comma(); putv3(m.b); comma(); putv3(m.c);
    Vector3f vel;
    const bool vel_ok = ahrs.get_velocity_NED(vel);
    key("vel"); putb(vel_ok); comma(); putv3(vel);
    Vector3p pos;
    const bool pos_ok = ahrs.get_relative_position_NED_origin(pos);
    key("pos"); putb(pos_ok); comma(); putv3(pos);
    Location loc;
    const bool loc_ok = ahrs.get_location(loc);
    key("loc"); putb(loc_ok); comma(); putloc(loc);
    key("gyro"); putv3(ahrs.get_gyro());
    key("accef"); putv3(ahrs.get_accel_ef());
    key("resets"); putu(ahrs.get_last_attitude_reset_count()); comma(); putu(ahrs.get_yaw_reset_count()); comma();
    putu(ahrs.get_position_NE_reset_count()); comma(); putu(ahrs.get_position_D_reset_count());
    key("healthy"); putb(ahrs.healthy());
    key("initialised"); putb(ahrs.initialised());
    Location origin;
    const bool origin_ok = ahrs.get_origin(origin);
    key("origin"); putb(origin_ok); comma(); putloc(origin);
    key("ekf"); putu(unsigned(ahrs.active_EKF_type()));
    nav_filter_status fs {};
    const bool fs_ok = ahrs.get_filter_status_for_configured_backend(fs);
    key("fs"); putb(fs_ok); comma();
    { char t[16]; snprintf(t, sizeof(t), "%08x", unsigned(fs.value)); buf += t; }

    // ---------------- EKF3 ----------------
    const NavEKF3 &ekf = AP_AHRS_NavEKF3::EKF3;
    key("primary"); puti(ekf.getPrimaryCoreIndex());
    key("ncores"); putu(ekf.core != nullptr ? ekf.num_cores : 0);
    if (ekf.core != nullptr) {
        Vector3f gb, ab;
        ekf.getGyroBias(-1, gb);
        ekf.getAccelBias(-1, ab);
        key("gbias"); putv3(gb);
        key("abias"); putv3(ab);
        float vv = 0, pv = 0, hv = 0, tv = 0;
        Vector3f mv;
        Vector2f off;
        const bool var_ok = ekf.getVariances(vv, pv, hv, mv, tv, off);
        key("var"); putb(var_ok); comma(); putf(vv); comma(); putf(pv); comma(); putf(hv); comma(); putv3(mv);
        comma(); putf(tv); comma(); putf(off.x); comma(); putf(off.y);
        for (uint8_t c = 0; c < ekf.num_cores; c++) {
            const NavEKF3_core &k = ekf.core[c];
            char kk[16];
            // state vector
            snprintf(kk, sizeof(kk), "c%u.x", unsigned(c)); key(kk);
            for (uint8_t i = 0; i < 24; i++) {
                if (i) comma();
                putf(k.statesArray[i]);
            }
            // filter status and initialisation
            nav_filter_status cs {};
            k.getFilterStatus(cs);
            snprintf(kk, sizeof(kk), "c%u.fs", unsigned(c)); key(kk);
            { char t[16]; snprintf(t, sizeof(t), "%08x", unsigned(cs.value)); buf += t; }
            comma(); putb(k.statesInitialised);
            // covariance
            Fnv dp;
            for (uint8_t i = 0; i < 24; i++) {
                for (uint8_t j = 0; j < 24; j++) {
                    dp.f(k.Pmut[i][j]);
                }
            }
            snprintf(kk, sizeof(kk), "c%u.P", unsigned(c)); key(kk); putdigest(dp);
            // output predictor
            Fnv dout;
            digest_output(dout, k.outputDataNew);
            digest_output(dout, k.outputDataDelayed);
            dout.v3(k.delAngCorrection); dout.v3(k.velErrintegral); dout.v3(k.posErrintegral);
            dout.f(k.vertCompFiltState.pos); dout.f(k.vertCompFiltState.vel); dout.f(k.vertCompFiltState.acc);
            const ekf_imu_buffer &ob = imu_base(k.storedOutput);
            dout.u8(ob._size); dout.u8(ob._oldest); dout.u8(ob._youngest); dout.b(ob._filled);
            for (uint8_t i = 0; i < ob._size && ob.buffer != nullptr; i++) {
                NavEKF3_core::output_elements e;
                memcpy(&e, ob.get(i), sizeof(e));
                digest_output(dout, e);
            }
            snprintf(kk, sizeof(kk), "c%u.out", unsigned(c)); key(kk); putdigest(dout);
            // IMU buffer
            Fnv di;
            const ekf_imu_buffer &ib = imu_base(k.storedIMU);
            di.u8(ib._size); di.u8(ib._oldest); di.u8(ib._youngest); di.b(ib._filled);
            for (uint8_t i = 0; i < ib._size && ib.buffer != nullptr; i++) {
                NavEKF3_core::imu_elements e;
                memcpy(&e, ib.get(i), sizeof(e));
                di.v3(e.delAng); di.v3(e.delVel); di.f(e.delAngDT); di.f(e.delVelDT);
                di.u32(e.time_ms); di.u8(e.gyro_index); di.u8(e.accel_index);
            }
            snprintf(kk, sizeof(kk), "c%u.imu", unsigned(c)); key(kk); putdigest(di);
            // innovation test ratios of this core
            {
                float a = 0, b2 = 0, h2 = 0, t2 = 0;
                Vector3f mm;
                Vector2f oo;
                const bool ok = k.getVariances(a, b2, h2, mm, t2, oo);
                snprintf(kk, sizeof(kk), "c%u.var", unsigned(c)); key(kk);
                putb(ok); comma(); putf(a); comma(); putf(b2); comma(); putf(h2); comma(); putv3(mm); comma(); putf(t2);
            }
            // EKFGSF_yaw
            const EKFGSF_yaw *g = k.yawEstimator;
            if (g != nullptr) {
                ftype yaw = 0, yv = 0;
                uint8_t nclips = 0;
                const bool ok = g->getYawData(yaw, yv, &nclips);
                snprintf(kk, sizeof(kk), "c%u.gsf", unsigned(c)); key(kk);
                putb(ok); comma(); putf(yaw); comma(); putf(yv); comma(); putu(nclips);
                Fnv dg;
                dg.v3(g->delta_angle); dg.v3(g->delta_velocity); dg.f(g->angle_dt); dg.f(g->velocity_dt);
                for (uint8_t mdl = 0; mdl < N_MODELS_EKFGSF; mdl++) {
                    const auto &a = g->AHRS[mdl];
                    dg.v3(a.R.a); dg.v3(a.R.b); dg.v3(a.R.c); dg.v3(a.gyro_bias); dg.b(a.aligned);
                    dg.f(a.accel_FR[0]); dg.f(a.accel_FR[1]); dg.f(a.vel_NE[0]); dg.f(a.vel_NE[1]);
                    dg.b(a.fuse_gps); dg.f(a.accel_dt);
                }
                dg.b(g->ahrs_tilt_aligned); dg.f(g->accel_gain); dg.v3(g->ahrs_accel); dg.f(g->ahrs_accel_norm); dg.f(g->true_airspeed);
                for (uint8_t mdl = 0; mdl < N_MODELS_EKFGSF; mdl++) {
                    const auto &e = g->EKF[mdl];
                    for (uint8_t i = 0; i < 3; i++) dg.f(e.X[i]);
                    for (uint8_t i = 0; i < 3; i++) for (uint8_t j = 0; j < 3; j++) dg.f(e.P[i][j]);
                    for (uint8_t i = 0; i < 2; i++) for (uint8_t j = 0; j < 2; j++) dg.f(e.S[i][j]);
                    dg.f(e.innov[0]); dg.f(e.innov[1]);
                }
                dg.b(g->vel_fuse_running); dg.b(g->run_ekf_gsf);
                dg.f(g->GSF.yaw); dg.f(g->GSF.yaw_variance);
                for (uint8_t mdl = 0; mdl < N_MODELS_EKFGSF; mdl++) dg.f(g->GSF.weights[mdl]);
                dg.u8(g->n_clips);
                comma(); putdigest(dg);
            }
        }
    }
    put_front_ends();
    // the barometer's and compass's events (1, 2, 4) as `ev=` (as before), the IMU's (8, and later ones) as `evx=` (shifted)
    key("ev"); putu(line_events & 7);
    key("evx"); putu(line_events >> 3);
    // the vehicle's arguments of Compass::set_throttle and set_voltage (Copter::update_batt_compass, task 13:
    // `motors->get_throttle()`, `battery.voltage()` after `battery.read()`; neither changes later in the step)
    const AP_Motors *mot = AP_Motors::get_singleton();
    key("cin"); putf(mot != nullptr ? mot->get_throttle() : 0.0f); comma(); putf(AP::battery().voltage());
    line_events = 0;
    buf += '\n';
    fwrite(buf.data(), 1, buf.size(), f);
}

}  // namespace EstProbe
