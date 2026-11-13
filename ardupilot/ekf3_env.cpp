// The boundary of the NavEKF3 translation, C++ side of its difftest (README.md, "Phase 3: AP_DAL and
// NavEKF3"; ardupilot/ekf3_difftest.py): the sensor front ends, AP_AHRS, the vehicle and the HAL, as AP_DAL
// reads them. The translation reads each of their getters as a boundary input (one field of AP_DAL's
// `Inputs`, an array for a getter with an instance argument); here each getter answers the value the
// difftest line gives that input (ekf3_env.h, generated: one field per Lean input, with its name).
// A getter that the front end implements inline in its header (reading a data member) answers through
// that data member, which `ekf3_env_apply()` sets before each call; the others are defined here. The
// front-end objects are zero-filled storage of their real classes (their constructors are not part of
// this test). AP_Param's defaults code is ac_pid_env.cpp's copy of AP_Param.cpp (no storage).
#include "ekf3_env.h"
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
#include <AP_Vehicle/AP_Vehicle.h>
#include <AP_WheelEncoder/AP_WheelEncoder.h>
#include <AP_InternalError/AP_InternalError.h>
#include <GCS_MAVLink/GCS.h>

cpp2lean_inp_AP_DAL env_dal;
cpp2lean_inp_NavEKF3 env_ekf3;
cpp2lean_inp_NavEKF3_core env_core;
cpp2lean_out_env env_out;

static void env_fail(const char *what)
{
    fprintf(stderr, "ekf3_env: %s\n", what);
    exit(5);
}

// ---- the objects (zero-filled storage of the real classes)
#define ENV_OBJECT(T, name) alignas(T) static unsigned char name##_buf[sizeof(T)]; static T &name = *reinterpret_cast<T *>(name##_buf)
ENV_OBJECT(AP_InertialSensor, env_ins);
ENV_OBJECT(AP_Baro, env_baro);
ENV_OBJECT(Compass, env_compass);
ENV_OBJECT(AP_GPS, env_gps);
ENV_OBJECT(AP_AHRS, env_ahrs);
ENV_OBJECT(AP_HAL::HAL, env_hal);

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
};
static EnvUtil env_util;
const AP_HAL::HAL &hal = env_hal;

namespace AP {
AP_InertialSensor &ins() { return env_ins; }
AP_Baro &baro() { return env_baro; }
Compass &compass() { return env_compass; }
AP_GPS &gps() { return env_gps; }
AP_AHRS &ahrs() { return env_ahrs; }
AP_Vehicle *vehicle() { return env_vehicle; }
AP_WheelEncoder *wheelencoder() { return nullptr; }
AP_InternalError &internalerror() { alignas(AP_InternalError) static unsigned char b[sizeof(AP_InternalError)]; return *reinterpret_cast<AP_InternalError *>(b); }
}
void AP_InternalError::error(const AP_InternalError::error_t, uint16_t) {}

// the HAL clock (boundary functions of the translation: AP_HAL::micros64, AP_HAL::micros)
uint64_t AP_HAL::micros64() { return env_dal.micros64; }
uint32_t AP_HAL::micros() { return env_dal.micros; }
uint32_t AP_HAL::millis() { return uint32_t(env_dal.micros64 / 1000U); }
uint64_t AP_HAL::millis64() { return env_dal.micros64 / 1000U; }
void AP_HAL::panic(const char *errormsg, ...) { env_fail(errormsg); }

// GCS_SEND_TEXT: left out of the model (cpp2lean --drop GCS::send_text); an object that sends nothing
alignas(GCS) static unsigned char env_gcs_buf[sizeof(GCS)];
GCS &gcs() { return *reinterpret_cast<GCS *>(env_gcs_buf); }
void GCS::send_text(MAV_SEVERITY, const char *, ...) {}

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

// ---- AP_Baro
bool AP_Baro::healthy(uint8_t i) const { return i < 3 && env_dal._baro.healthy_at[i]; }
void AP_Baro::update_calibration() { env_out.baro_update_calibration_calls++; }

// ---- Compass
float Compass::get_declination() const { return env_dal._compass.get_declination; }
uint8_t Compass::get_num_enabled(void) const { return env_dal._compass.get_num_enabled; }
bool Compass::consistent() const { return env_dal._compass.consistent; }
bool Compass::use_for_yaw(uint8_t i) const { return i < 3 && env_dal._compass.use_for_yaw_at[i]; }
bool Compass::healthy(uint8_t i) const { return i < 3 && env_dal._compass.healthy_at[i]; }
bool Compass::have_scale_factor(uint8_t i) const { return i < 3 && env_dal._compass.have_scale_factor_at[i]; }

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

// ---- AP_AHRS (the EKF3 core's request, AP_NavEKF3_core.cpp:888): an output of the translation
void AP_AHRS::set_takeoff_expected(bool b) { env_out.ahrs_set_takeoff_expected = b; env_out.ahrs_set_takeoff_expected_calls++; }

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
void ekf3_env_apply()
{
    static bool init;
    if (!init) {
        init = true;
        const_cast<AP_HAL::HAL &>(hal).util = &env_util;
    }
    const auto &d = env_dal;
    if (d.get_loop_delta_t != d._ins.get_loop_delta_t) env_fail("AP::ins().get_loop_delta_t() given two values");
    if (d.nonnull) env_fail("AP::wheelencoder() is null in this configuration");
    // AP_InertialSensor (AP_InertialSensor.h:189-370)
    env_ins._last_update_usec = d.get_last_update_usec;
    env_ins._loop_rate = d._ins.get_loop_rate_hz;
    env_ins._first_usable_gyro = d._ins.get_first_usable_gyro;
    env_ins._loop_delta_t = d._ins.get_loop_delta_t;
    env_ins._first_usable_accel = d._ins.get_first_usable_accel;
    env_ins._accel_count = d._ins.get_accel_count;
    env_ins._gyro_count = d._ins.get_gyro_count;
    for (uint8_t i = 0; i < 3; i++) {
        env_ins._accel_pos(i).set(d._ins.get_imu_pos_offset_at[i]);
    }
    // AP_Baro (AP_Baro.h:69-193)
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
    // AP_GPS (AP_GPS.h:292-480)
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
    // AP_AHRS (AP_AHRS.h:524-751)
    env_ahrs._home = d.get_home;
    env_ahrs._vehicle_class = AP_AHRS::VehicleClass(d.get_vehicle_class);
    env_ahrs.fly_forward = d.get_fly_forward;
    env_ahrs.takeoff_expected = d.get_takeoff_expected;
    env_ahrs.touchdown_expected = d.get_touchdown_expected;
    env_ahrs._trim.set(d.get_trim);
    env_ahrs.state.configured_ekf_type = AP_AHRS::EKFType(d.configured_ekf_type);
    env_ahrs._rotation_vehicle_body_to_autopilot_body = d.get_rotation_vehicle_body_to_autopilot_body;
    // AP_Vehicle::get_time_flying_ms (AP_Vehicle.h:175): millis() - _last_flying_ms while flying
    env_vehicle->likely_flying = d.get_time_flying_ms != 0;
    env_vehicle->_last_flying_ms = AP_HAL::millis() - d.get_time_flying_ms;
    // the HAL
    env_util.soft_armed = d.get_soft_armed;
}

// ---- the rest of what the translated sources call outside it
// AP_ParamT.cpp:55-61: the value set (the default's registration is AP_Param storage, outside the model)
template<> void AP_ParamTBase<uint8_t, AP_PARAM_INT8>::set_and_default(const uint8_t &v) { set(v); }
// AP_HAL/Util.cpp:46-81 (vsnprintf: the C library's; the EKF's pre-arm text, which the translation leaves out)
int AP_HAL::Util::vsnprintf(char *str, size_t size, const char *format, va_list ap) { return ::vsnprintf(str, size, format, ap); }
void AP_HAL::Util::set_soft_armed(const bool b) { soft_armed = b; }
// AP_Compass.cpp:974: the state of a compass by its priority; here the identity (one compass state per priority)
Compass::StateIndex Compass::_get_state_id(Compass::Priority priority) const { return StateIndex(uint8_t(priority)); }
