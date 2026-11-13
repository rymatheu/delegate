// The boundary of the AP_AHRS translation, C++ side of its difftest (README.md, "Phase 3: AP_AHRS translated";
// ardupilot/ahrs_difftest.py): the sensor front ends, the vehicle and the HAL, as AP_DAL, NavEKF3 and AP_AHRS
// (with its DCM and EKF3 backends) read them. ardupilot/ekf3_env.cpp's boundary with AP_AHRS itself removed (it
// is the object under test: `AP::ahrs()`, `set_takeoff_expected` are the real ones) and the getters the AHRS and
// DCM read added. Each getter answers the value the difftest line gives the translation's input of that name
// (ahrs_env.h, generated): through the data member an inline getter reads (set by `ahrs_env_apply()` before
// each line), else defined here. A getter the translation reads in several objects (AP_DAL's
// `ins.get_delta_velocity(i, ...)`, DCM's) answers from one of them; the scenario gives every copy the same
// value (ardupilot/ahrs_scenario.py, by construction). The front-end objects are zero-filled storage of their
// real classes; AP_Param's defaults code is ac_pid_env.cpp's copy of AP_Param.cpp (no storage).
#include "ahrs_env.h"
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <type_traits>
#include <AP_HAL/AP_HAL.h>
#include <AP_Param/AP_Param.h>
#include <AP_InertialSensor/AP_InertialSensor.h>
#include <AP_Baro/AP_Baro.h>
#include <AP_Compass/AP_Compass.h>
#include <AP_GPS/AP_GPS.h>
#include <AP_AHRS/AP_AHRS.h>
#include <AP_AHRS/AP_AHRS_SIM.h>
#include <AP_Vehicle/AP_Vehicle.h>
#include <AP_WheelEncoder/AP_WheelEncoder.h>
#include <AP_InternalError/AP_InternalError.h>
#include <AP_Notify/AP_Notify.h>
#include <AP_Mission/AP_Mission.h>
#include <AP_BoardConfig/AP_BoardConfig.h>
#include <SITL/SITL.h>
#include <GCS_MAVLink/GCS.h>

cpp2lean_inp_AP_DAL env_dal;
cpp2lean_inp_NavEKF3 env_ekf3;
cpp2lean_inp_NavEKF3_core env_core;
cpp2lean_inp_AP_AHRS env_ahrs;
cpp2lean_out_env env_out;

static void env_fail(const char *what)
{
    fprintf(stderr, "ahrs_env: %s\n", what);
    exit(5);
}

// ---- the objects (zero-filled storage of the real classes)
#define ENV_OBJECT(T, name) alignas(T) static unsigned char name##_buf[sizeof(T)]; static T &name = *reinterpret_cast<T *>(name##_buf)
ENV_OBJECT(AP_InertialSensor, env_ins);
ENV_OBJECT(AP_Baro, env_baro);
ENV_OBJECT(Compass, env_compass);
ENV_OBJECT(AP_GPS, env_gps);
ENV_OBJECT(AP_HAL::HAL, env_hal);
ENV_OBJECT(SITL::SIM, env_sitl);
ENV_OBJECT(AP_Mission, env_mission);

// AP_Vehicle is abstract: its storage, read through its non-virtual inline getter only
alignas(AP_Vehicle) static unsigned char env_vehicle_buf[sizeof(AP_Vehicle)];
static AP_Vehicle *const env_vehicle = reinterpret_cast<AP_Vehicle *>(env_vehicle_buf);

class EnvUtil : public AP_HAL::Util {
public:
    void set_hw_rtc(uint64_t) override {}
    uint64_t get_hw_rtc() const override { return 0; }
    uint32_t available_memory(void) override { return env_dal.available_memory; }
    // AP_DAL::malloc_type (the cores' memory, AP_NavEKF3.cpp:850): zeroed memory, recorded by the driver
    void *malloc_type(size_t size, Memory_Type) override { return cpp2lean_raw_alloc(size); }
    void free_type(void *, size_t, Memory_Type) override {}
    // AP_AHRS (AP_AHRS.cpp:1795) and DCM (AP_AHRS_DCM.cpp:362) read the persistent data only after a watchdog reset
    bool was_watchdog_reset() const override { return env_ahrs.was_watchdog_reset; }
};
static EnvUtil env_util;

// the scheduler: what AP_AHRS calls on it (boost_end, delay_microseconds for the SITL loop jitter), counted
class EnvScheduler : public AP_HAL::Scheduler {
public:
    void init() override {}
    void delay(uint16_t) override { env_fail("Scheduler::delay"); }
    void delay_microseconds(uint16_t us) override { env_out.delay_microseconds = us; }
    void boost_end(void) override { env_out.boost_end_calls++; }
    void register_timer_process(AP_HAL::MemberProc) override {}
    void register_io_process(AP_HAL::MemberProc) override {}
    void register_timer_failsafe(AP_HAL::Proc, uint32_t) override {}
    void set_system_initialized() override {}
    bool is_system_initialized() override { return true; }
    void reboot(bool) override { env_fail("Scheduler::reboot"); }
    bool in_main_thread() const override { return true; }
    void call_delay_cb() override {}
    bool thread_create(AP_HAL::MemberProc, const char *, uint32_t, priority_base, int8_t) override { return false; }
};
static EnvScheduler env_scheduler;

// the HAL's pointers, set before any static constructor that reads them (AP_AHRS's, at static initialization)
__attribute__((init_priority(101))) static struct EnvHalSetup {
    EnvHalSetup() {
        auto &h = const_cast<AP_HAL::HAL &>(reinterpret_cast<const AP_HAL::HAL &>(env_hal_buf));
        h.util = &env_util;
        h.scheduler = &env_scheduler;
        h.opticalflow = nullptr;
    }
} env_hal_setup;
const AP_HAL::HAL &hal = env_hal;

namespace AP {
AP_InertialSensor &ins() { return env_ins; }
AP_Baro &baro() { return env_baro; }
Compass &compass() { return env_compass; }
AP_GPS &gps() { return env_gps; }
AP_Vehicle *vehicle() { return env_vehicle; }
AP_WheelEncoder *wheelencoder() { return nullptr; }
AP_Mission &mission() { return env_mission; }
SITL::SIM *sitl() { return &env_sitl; }
AP_InternalError &internalerror() { alignas(AP_InternalError) static unsigned char b[sizeof(AP_InternalError)]; return *reinterpret_cast<AP_InternalError *>(b); }
}
void AP_InternalError::error(const AP_InternalError::error_t, uint16_t) {}
// AP_AHRS::init with AHRS_EKF_TYPE 1 only (cpp2lean --drop AP_BoardConfig::config_error: not reached)
void AP_BoardConfig::config_error(const char *fmt, ...) { env_fail(fmt); }

// the HAL clock (boundary functions of the translation: AP_HAL::micros64, AP_HAL::micros, AP_HAL::millis)
uint64_t AP_HAL::micros64() { return env_dal.micros64; }
uint32_t AP_HAL::micros() { return env_dal.micros; }
uint32_t AP_HAL::millis() { return uint32_t(env_dal.micros64 / 1000U); }
uint64_t AP_HAL::millis64() { return env_dal.micros64 / 1000U; }
void AP_HAL::panic(const char *errormsg, ...) { env_fail(errormsg); }

// GCS: text and messages left out of the model (cpp2lean --drop GCS::send_text, GCS::send_message)
alignas(GCS) static unsigned char env_gcs_buf[sizeof(GCS)];
GCS &gcs() { return *reinterpret_cast<GCS *>(env_gcs_buf); }
void GCS::send_text(MAV_SEVERITY, const char *, ...) {}
void GCS::send_message(enum ap_message) {}

// AP_Notify's flags (AP_Notify.cpp:225): outputs of the translation (AP_AHRS.cpp:671)
struct AP_Notify::notify_flags_and_values_type AP_Notify::flags;

// AP_Mission (AP_AHRS::set_home, AP_AHRS.cpp:1787): an output, counted
void AP_Mission::write_home_to_storage() { env_out.write_home_to_storage_calls++; }

// ---- AP_AHRS_SIM (the SITL "true state" backend; AP_AHRS_SIM.cpp is not part of the translation): with
// AHRS_EKF_TYPE 3 AP_AHRS calls only get_results (cpp2lean --drop: as the real one with no SITL state, it fills
// nothing); the others answer the line (boundary inputs `sim.get_origin(ret)`, `sim.get_innovations(...)`)
void AP_AHRS_SIM::get_results(AP_AHRS_Backend::Estimates &) {}
bool AP_AHRS_SIM::synthetic_airspeed_EAS(const Estimates &, float &, AirspeedEstimateType &) { return false; }
bool AP_AHRS_SIM::get_origin(Location &ret) const { ret = env_ahrs.get_origin_ret; return env_ahrs.get_origin; }
bool AP_AHRS_SIM::get_innovations(Vector3f &velInnov, Vector3f &posInnov, Vector3f &magInnov, float &tasInnov, float &yawInnov) const
{
    velInnov = env_ahrs.get_innovations_velInnov;
    posInnov = env_ahrs.get_innovations_posInnov;
    magInnov = env_ahrs.get_innovations_magInnov;
    tasInnov = env_ahrs.get_innovations_tasInnov;
    yawInnov = env_ahrs.get_innovations_yawInnov;
    return env_ahrs.get_innovations;
}
#if AP_COMPASS_LEARN_COPY_FROM_EKF_ENABLED
bool AP_AHRS_SIM::get_mag_offsets(uint8_t, Vector3f &) const { return false; }
#endif

// ---- AP_InertialSensor: the getters defined in AP_InertialSensor.cpp
bool AP_InertialSensor::use_accel(uint8_t i) const { return i < 3 && env_dal._ins.use_accel_at[i]; }
bool AP_InertialSensor::use_gyro(uint8_t i) const { return i < 3 && env_dal._ins.use_gyro_at[i]; }
bool AP_InertialSensor::get_delta_velocity(uint8_t i, Vector3f &dv, float &dt) const
{
    if (i >= 3) return false;
    dv = env_dal._ins.get_delta_velocity_delta_velocity_at[i];
    dt = env_dal._ins.get_delta_velocity_delta_velocity_dt_at[i];
    return env_dal._ins.get_delta_velocity_at[i];
}
bool AP_InertialSensor::get_delta_angle(uint8_t i, Vector3f &da, float &dt) const
{
    if (i >= 3) return false;
    da = env_dal._ins.get_delta_angle_delta_angle_at[i];
    dt = env_dal._ins.get_delta_angle_delta_angle_dt_at[i];
    return env_dal._ins.get_delta_angle_at[i];
}
float AP_InertialSensor::get_gyro_bias_limit_rads(uint8_t i) const { return i < 3 ? env_dal._ins.get_gyro_bias_limit_rads_at[i] : 0.0f; }
float AP_InertialSensor::get_gyro_bias_init_dps(uint8_t i) const { return i < 3 ? env_dal._ins.get_gyro_bias_init_dps_at[i] : 0.0f; }
// outputs of the translation: calls counted, the instance set
void AP_InertialSensor::update(void) { env_out.ins_update_calls++; }
void AP_InertialSensor::wait_for_sample(void) { env_out.ins_wait_for_sample_calls++; }
void AP_InertialSensor::set_primary(uint8_t instance) { env_out.ins_set_primary = instance; }

// ---- AP_Baro
bool AP_Baro::healthy(uint8_t i) const { return i < 3 && env_dal._baro.healthy_at[i]; }
void AP_Baro::update_calibration() { env_out.baro_update_calibration_calls++; }
// a non-const call with a result (AP_AHRS_DCM.cpp:1487): its result an input, its calls counted
float AP_Baro::get_climb_rate(void) { env_out.baro_get_climb_rate_calls++; return env_ahrs.dcm.get_climb_rate; }

// ---- Compass
float Compass::get_declination() const { return env_dal._compass.get_declination; }
uint8_t Compass::get_num_enabled(void) const { return env_dal._compass.get_num_enabled; }
bool Compass::consistent() const { return env_dal._compass.consistent; }
bool Compass::use_for_yaw(uint8_t i) const { return i < 3 && env_dal._compass.use_for_yaw_at[i]; }
bool Compass::use_for_yaw(void) const { return env_ahrs.use_for_yaw; }
bool Compass::healthy(uint8_t i) const { return i < 3 && env_dal._compass.healthy_at[i]; }
bool Compass::have_scale_factor(uint8_t i) const { return i < 3 && env_dal._compass.have_scale_factor_at[i]; }
// a non-const call with a result (AP_AHRS_DCM.cpp:678): its result an input, its calls counted
bool Compass::read(void) { env_out.compass_read_calls++; return env_ahrs.dcm.read; }
// a const call with a non-constant argument (AP_AHRS_DCM.cpp:679, cpp2lean --site-inputs): the line's value
float Compass::calculate_heading(const Matrix3f &, uint8_t) const { return env_ahrs.dcm.calculate_heading; }

// ---- AP_GPS
uint8_t AP_GPS::num_sensors(void) const { return env_dal._gps.num_sensors; }
const Vector3f &AP_GPS::get_antenna_offset(uint8_t i) const { return env_dal._gps.get_antenna_offset_at[i < 3 ? i : 0]; }
bool AP_GPS::horizontal_accuracy(uint8_t i, float &hacc) const
{
    if (i >= 3) return false;
    hacc = env_dal._gps.horizontal_accuracy_hacc_at[i];
    return env_dal._gps.horizontal_accuracy_at[i];
}
bool AP_GPS::vertical_accuracy(uint8_t i, float &vacc) const
{
    if (i >= 3) return false;
    vacc = env_dal._gps.vertical_accuracy_vacc_at[i];
    return env_dal._gps.vertical_accuracy_at[i];
}
bool AP_GPS::speed_accuracy(uint8_t i, float &sacc) const
{
    if (i >= 3) return false;
    sacc = env_dal._gps.speed_accuracy_sacc_at[i];
    return env_dal._gps.speed_accuracy_at[i];
}
bool AP_GPS::get_lag(uint8_t i, float &lag_sec) const
{
    if (i >= 3) return false;
    lag_sec = env_dal._gps.get_lag_lag_sec_at[i];
    return env_dal._gps.get_lag_at[i];
}
bool AP_GPS::gps_yaw_deg(uint8_t i, float &yaw_deg, float &accuracy_deg, uint32_t &time_ms) const
{
    if (i >= 3) return false;
    yaw_deg = env_dal._gps.gps_yaw_deg_yaw_deg_at[i];
    accuracy_deg = env_dal._gps.gps_yaw_deg_accuracy_deg_at[i];
    time_ms = env_dal._gps.gps_yaw_deg_time_ms_at[i];
    return env_dal._gps.gps_yaw_deg_at[i];
}

// ---- AP_Param (as ac_pid_env.cpp: AP_Param.cpp's defaults code, no storage)
uint16_t AP_Param::num_param_overrides = 0;
AP_Param::param_override *AP_Param::param_overrides = nullptr;

void AP_Param::set_value(enum ap_var_type type, void *ptr, float value)
{
    switch (type) {
    case AP_PARAM_INT8:
        ((AP_Int8 *)ptr)->set(value);
        break;
    case AP_PARAM_INT16:
        ((AP_Int16 *)ptr)->set(value);
        break;
    case AP_PARAM_INT32:
        ((AP_Int32 *)ptr)->set(value);
        break;
    case AP_PARAM_FLOAT:
        ((AP_Float *)ptr)->set(value);
        break;
    default:
        break;
    }
}

void AP_Param::setup_object_defaults(const void *object_pointer, const struct GroupInfo *group_info)
{
    ptrdiff_t base = (ptrdiff_t)object_pointer;
    uint8_t type;
    for (uint8_t i=0;
         (type=group_info[i].type) != AP_PARAM_NONE;
         i++) {
        if (type <= AP_PARAM_FLOAT) {
            void *ptr = (void *)(base + group_info[i].offset);
            set_value((enum ap_var_type)type, ptr,
                      get_default_value((const AP_Param *)ptr, group_info[i]));
        } else if (type == AP_PARAM_VECTOR3F) {
            // Single default for all components
            void *ptr = (void *)(base + group_info[i].offset);
            const float default_val = get_default_value((const AP_Param *)ptr, group_info[i]);
            ((AP_Vector3f *)ptr)->set(Vector3f{default_val, default_val, default_val});
        }
    }
}

float AP_Param::get_default_value(const AP_Param *vp, const struct GroupInfo &info)
{
    for (uint16_t i=0; i<num_param_overrides; i++) {
        if (vp == param_overrides[i].object_ptr) {
            return param_overrides[i].value;
        }
    }
    if ((info.flags & AP_PARAM_FLAG_DEFAULT_POINTER) != 0) {
        return *((float*)((ptrdiff_t)vp - info.def_value_offset));
    }
    return info.def_value;
}

// ---- the values of the inline getters, through the data members they read
void ahrs_env_apply()
{
    const auto &d = env_dal;
    const auto &a = env_ahrs;
    if (d.get_loop_delta_t != d._ins.get_loop_delta_t) env_fail("AP::ins().get_loop_delta_t() given two values");
    if (d.nonnull) env_fail("AP::wheelencoder() is null in this configuration");
    // AP_InertialSensor (AP_InertialSensor.h:155-370)
    env_ins._last_update_usec = d.get_last_update_usec;
    env_ins._loop_rate = d._ins.get_loop_rate_hz;
    env_ins._first_usable_gyro = d._ins.get_first_usable_gyro;
    env_ins._loop_delta_t = d._ins.get_loop_delta_t;
    env_ins._first_usable_accel = d._ins.get_first_usable_accel;
    env_ins._accel_count = d._ins.get_accel_count;
    env_ins._gyro_count = d._ins.get_gyro_count;
    env_ins._delta_time = a.dcm.get_delta_time;
    env_ins._loop_delta_t_max = 1.0f;       // (get_delta_time() is MIN(_delta_time, _loop_delta_t_max))
    for (uint8_t i = 0; i < 3; i++) {
        env_ins._accel_pos(i).set(d._ins.get_imu_pos_offset_at[i]);
        env_ins._gyro[i] = a.ekf3.get_gyro_at[i];
        env_ins._accel[i] = a.ekf3.get_accel_at[i];
        env_ins._accel_healthy[i] = a.dcm.get_accel_health_at[i];
        env_ins._gyro_healthy[i] = a.dcm.get_accel_health_at[i];
    }
    // AP_Baro (AP_Baro.h:58-193)
    env_baro._EAS2TAS = d.get_EAS2TAS;
    env_baro._primary = d._baro.get_primary;
    env_baro._num_sensors = d._baro.num_instances;
    for (uint8_t i = 0; i < 3; i++) {
        env_baro.sensors[i].last_update_ms = d._baro.get_last_update_at[i];
        env_baro.sensors[i].altitude = d._baro.get_altitude_at[i];
    }
    // Compass (AP_Compass.h:99-390)
    env_compass._enabled.set(d._compass.available);
    env_compass.init_done = d._compass.available;
    env_compass._compass_count = d._compass.get_count;
    env_compass._auto_declination.set(d._compass.auto_declination_enabled ? 1 : 0);
    env_compass._first_usable = d._compass.get_first_usable;
    env_compass._learn.set(d._compass.learn_offsets_enabled ? Compass::LearnType::INFLIGHT : Compass::LearnType::NONE);
    for (uint8_t i = 0; i < 3; i++) {
        using ST = std::remove_reference<decltype(env_compass._get_state(Compass::Priority(0)))>::type;
        auto &st = const_cast<std::remove_const<ST>::type &>(env_compass._get_state(Compass::Priority(i)));
        st.offset.set(d._compass.get_offsets_at[i]);
        st.last_update_usec = d._compass.last_update_usec_at[i];
        st.field = d._compass.get_field_at[i];
    }
    // AP_GPS (AP_GPS.h:292-510)
    env_gps.primary_instance = d._gps.primary_sensor;
    for (uint8_t i = 0; i < 3; i++) {
        env_gps.state[i].status = d._gps.status_at[i];
        env_gps.state[i].location = d._gps.location_at[i];
        env_gps.timing[i].last_message_time_ms = d._gps.last_message_time_ms_at[i];
        env_gps.state[i].have_vertical_velocity = d._gps.have_vertical_velocity_at[i];
        env_gps.state[i].hdop = d._gps.get_hdop_at[i];
        env_gps.state[i].num_sats = d._gps.num_sats_at[i];
        env_gps.state[i].velocity = d._gps.velocity_at[i];
    }
    // the primary receiver's ground speed and course, its last fix (AP_GPS.h:382-457; the scenario has one receiver)
    env_gps.state[d._gps.primary_sensor].ground_speed = a.ground_speed;
    env_gps.state[d._gps.primary_sensor].ground_course = a.dcm.ground_course;
    env_gps.timing[d._gps.primary_sensor].last_fix_time_ms = a.dcm.last_fix_time_ms;
    // AP_Vehicle::get_time_flying_ms (AP_Vehicle.h:175): millis() - _last_flying_ms while flying
    env_vehicle->likely_flying = d.get_time_flying_ms != 0;
    env_vehicle->_last_flying_ms = AP_HAL::millis() - d.get_time_flying_ms;
    // the HAL
    env_util.soft_armed = d.get_soft_armed;
    // SITL::SIM (AP_AHRS.cpp:662): the loop jitter parameter
    env_sitl.loop_time_jitter_us.set(a.loop_time_jitter_us);
    if (a.opticalflow_set) env_fail("hal.opticalflow is null in this configuration");
}

// ---- the rest of what the translated sources call outside it
// AP_ParamT.cpp:55-61: the value set (the default's registration is AP_Param storage, outside the model)
template<> void AP_ParamTBase<uint8_t, AP_PARAM_INT8>::set_and_default(const uint8_t &v) { set(v); }
// AP_HAL/Util.cpp:46-81 (vsnprintf: the C library's; the EKF's pre-arm text, which the translation leaves out)
int AP_HAL::Util::vsnprintf(char *str, size_t size, const char *format, va_list ap) { return ::vsnprintf(str, size, format, ap); }
void AP_HAL::Util::set_soft_armed(const bool b) { soft_armed = b; }
// AP_Compass.cpp:974: the state of a compass by its priority; here the identity (one compass state per priority)
Compass::StateIndex Compass::_get_state_id(Compass::Priority priority) const { return StateIndex(uint8_t(priority)); }
// (AP_ParamTBase::set_enable, set_and_save_ifchanged: ardupilot/ahrs_env_param.cpp, a unit without their instantiations)
// AP_HAL/Util.cpp:46-53 (the pre-arm texts of AP_NavEKF_Source and AP_AHRS_NavEKF3, which the translation does not reach)
int AP_HAL::Util::snprintf(char *str, size_t size, const char *format, ...)
{
    va_list ap;
    va_start(ap, format);
    int res = vsnprintf(str, size, format, ap);
    va_end(ap);
    return res;
}
// WITH_SEMAPHORE (AP_HAL/Semaphores.cpp): one thread, nothing to take (cpp2lean --semaphores)
WithSemaphore::WithSemaphore(AP_HAL::Semaphore &mtx, uint32_t) : _mtx(mtx) {}
WithSemaphore::WithSemaphore(AP_HAL::Semaphore *mtx, uint32_t) : _mtx(*mtx) {}
WithSemaphore::~WithSemaphore() {}
// AP_HAL/Scheduler.cpp: the base class's out-of-line members (no delay callbacks in this test)
void AP_HAL::Scheduler::register_delay_callback(AP_HAL::Proc, uint16_t) {}
void AP_HAL::Scheduler::call_delay_cb() {}
