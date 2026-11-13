// The C++ environment of the sensor front ends' World difftest (ardupilot/Sensors.json; README.md "Phase 3:
// sensor front ends and AP_Param"): what the front ends, the stand-ins and AP_ParamT.cpp reach outside the
// translation, compiled with the reference build's flags against the real headers.
//   - the HAL: `hal` with the scheduler stand-in (reference/hal/est_scheduler.cpp, the World's scheduler)
//     and a Util whose armed flag and watchdog flag are the line's inputs; no other driver;
//   - AP::ahrs(): the members the front ends call (`get_origin` returns the line's inputs, `resetHeightDatum`
//     is recorded in the output log), on an object that is never constructed (AP_AHRS is not linked);
//   - the effects the translation leaves out (--drop): GCS text, AP_Param::save/notify, the internal error
//     and configuration error reports, AP_HAL::panic: no effect here either;
//   - AP_Param's storage queries (AP_ParamT.cpp): nothing is in storage, except GPS1_TYPE (configured) and the inertial
//     sensor's gyro and accel ids (found by `load` per the line's inputs);
//   - AP_SerialManager::find_serial: the GPS port stand-in (est_uart) or none, per the line's inputs;
//   - AP_Notify's flags: storage only (not compared); the HAL's `set_hw_rtc` (AP_RTC) recorded in the output log.
#include <AP_HAL/AP_HAL.h>
#include <AP_AHRS/AP_AHRS.h>
#include <AP_Param/AP_Param.h>
#include <AP_InternalError/AP_InternalError.h>
#include <AP_BoardConfig/AP_BoardConfig.h>
#include <GCS_MAVLink/GCS.h>
#include <AP_Common/Location.h>
#include <AP_BattMonitor/AP_BattMonitor.h>
#include <AP_Compass/AP_Compass.h>
#include <SRV_Channel/SRV_Channel.h>
#include <AP_SerialManager/AP_SerialManager.h>
#include <AP_Notify/AP_Notify.h>
#include <AP_InertialSensor/AP_InertialSensor.h>
#include <AP_GPS/AP_GPS.h>
#include <string>
#include <new>

#include "est_scheduler.h"
#include "est_uart.h"
#include "cpp2lean_events.h"

std::string cpp2lean_events;

// the line's inputs
bool cpp2lean_watchdog_reset;
Location cpp2lean_origin;
bool cpp2lean_origin_ok;
Location cpp2lean_location;
bool cpp2lean_location_ok;
float cpp2lean_current;
bool cpp2lean_current_ok;
bool cpp2lean_find_serial[2] = {true, false};   // the first: a constant input (Sensors.json "const_inputs")

namespace {
class EnvUtil : public AP_HAL::Util {
public:
    void set_hw_rtc(uint64_t time_utc_usec) override { cpp2lean_ev("set_hw_rtc"); cpp2lean_ev_u(time_utc_usec); }
    uint64_t get_hw_rtc() const override { return 0; }
    bool was_watchdog_reset() const override { return cpp2lean_watchdog_reset; }
#ifdef CPP2LEAN_ENV_UTIL_EXTRA
    CPP2LEAN_ENV_UTIL_EXTRA     // the estimator World's difftest (ardupilot/estimation_env.cpp): AP_DAL's memory queries
#endif
};
EnvUtil env_util;
// the console (DEV_PRINTF in AP_InertialSensor's gyro calibration; the translation leaves its text out, --drop): a port
// of the GPS port stand-in's class that nothing reads, not part of the World
EstUART env_console;

class EnvHAL : public AP_HAL::HAL {
public:
    EnvHAL() : AP_HAL::HAL(nullptr, nullptr, nullptr, nullptr, nullptr, nullptr, nullptr, nullptr, nullptr, nullptr,
                           nullptr, nullptr, nullptr, nullptr, nullptr, &env_console, nullptr, nullptr, nullptr,
                           &est_scheduler, &env_util, nullptr, nullptr,
#if AP_SIM_ENABLED
                           nullptr,
#endif
#if HAL_WITH_DSP
                           nullptr,
#endif
                           nullptr) {}
    void run(int argc, char * const argv[], Callbacks *callbacks) const override {}
};
EnvHAL env_hal;
}

const AP_HAL::HAL& hal = env_hal;
const AP_HAL::HAL& AP_HAL::get_HAL() { return env_hal; }
AP_HAL::HAL& AP_HAL::get_HAL_mutable() { return env_hal; }

void cpp2lean_set_armed(bool v) { env_util.set_soft_armed(v); }

// AP_AHRS: never constructed; only these members are called (the object's storage is never read)
alignas(16) static unsigned char ahrs_storage[sizeof(AP_AHRS)];
AP_AHRS &AP::ahrs() { return *reinterpret_cast<AP_AHRS *>(ahrs_storage); }
bool AP_AHRS::get_origin(Location &ret) const { ret = cpp2lean_origin; return cpp2lean_origin_ok; }
void AP_AHRS::resetHeightDatum() { cpp2lean_ev("resetHeightDatum"); }
bool AP_AHRS::get_location(Location &loc) const { loc = cpp2lean_location; return cpp2lean_location_ok; }
void AP_AHRS::update_orientation() { cpp2lean_ev("update_orientation"); }

// AP_BattMonitor: never constructed; the current is the line's input (read for COMPASS_MOTCT 2 only)
alignas(16) static unsigned char battery_storage[sizeof(AP_BattMonitor)];
AP_BattMonitor &AP::battery() { return *reinterpret_cast<AP_BattMonitor *>(battery_storage); }
bool AP_BattMonitor::current_amps(float &current, const uint8_t instance) const { current = cpp2lean_current; return cpp2lean_current_ok; }

// AP_SerialManager (AP_InertialSensor and AP_GPS, README.md "Phase 3: AP_InertialSensor, AP_GPS and AP_NavEKF_Source"):
// never constructed; the GPS protocol's ports are the line's inputs, each the GPS port stand-in or none
alignas(16) static unsigned char serial_storage[sizeof(AP_SerialManager)];
AP_SerialManager &AP::serialmanager() { return *reinterpret_cast<AP_SerialManager *>(serial_storage); }
AP_HAL::UARTDriver *AP_SerialManager::find_serial(enum SerialProtocol protocol, uint8_t instance) const
{
    return instance < 2 && cpp2lean_find_serial[instance] ? &est_uart : nullptr;
}

// AP_Notify's flags (AP_Notify.cpp:225): the LED and buzzer state the front ends write; not linked, and not compared
// (the difftest's config "unlogged_outputs": a write to a static struct is not observable here)
struct AP_Notify::notify_flags_and_values_type AP_Notify::flags;

// SRV_Channels: only Compass_PerMotor's motor map reads it (COMPASS_PMOT_EN 1, never set here): no channel
bool SRV_Channels::find_channel(SRV_Channel::Function function, uint8_t &chan) { return false; }

// AP_Param::set_default_by_name for the names the compass stand-in sets (AP_Param.cpp:2798 finds the
// parameter by name; here the names of the translation's --param-name): not configured in storage, so set
extern Compass compass;
bool AP_Param::set_default_by_name(const char *name, float value)
{
    static const char *const names[] = {"COMPASS_SCALE", "COMPASS_SCALE2", "COMPASS_SCALE3"};
    for (uint8_t i = 0; i < 3; i++) {
        if (strcmp(name, names[i]) == 0) {
            compass._state[Compass::StateIndex(i)].scale_factor.set_default(value);
            return true;
        }
    }
    return false;
}

// GCS: text messages are left out
alignas(16) static unsigned char gcs_storage[sizeof(GCS)];
GCS &gcs() { return *reinterpret_cast<GCS *>(gcs_storage); }
void GCS::send_text(MAV_SEVERITY severity, const char *fmt, ...) {}

// the effects left out of the model (--drop)
void AP_HAL::panic(const char *errormsg, ...) {}
void AP_InternalError::error(const AP_InternalError::error_t e, uint16_t line) {}
alignas(16) static unsigned char ie_storage[sizeof(AP_InternalError)];
AP_InternalError &AP::internalerror() { return *reinterpret_cast<AP_InternalError *>(ie_storage); }
void AP_BoardConfig::config_error(const char *fmt, ...) {}

// AP_Param: storage is outside the model (nothing stored, saving and notification have no effect)
void AP_Param::save(bool force_save) {}
void AP_Param::notify() const {}
bool AP_Param::configured_in_storage(void) const { return false; }
bool AP_Param::configured_in_defaults_file(bool &read_only) const { return false; }
// GPS1_TYPE (gps.params[0].type) is configured (const input), the inertial sensor's ids are found in storage per the line
extern AP_GPS gps;
extern AP_InertialSensor ins;
bool cpp2lean_gyro_id_loaded;
bool cpp2lean_accel_id_loaded;
bool AP_Param::configured(void) const { return this == &gps.params[0].type; }
bool AP_Param::load(void)
{
    for (uint8_t i = 0; i < INS_MAX_INSTANCES - INS_AUX_INSTANCES; i++) {
        if (this == &ins._gyro_id_old_param[i]) {
            return cpp2lean_gyro_id_loaded;
        }
        if (this == &ins._accel_id_old_param[i]) {
            return cpp2lean_accel_id_loaded;
        }
    }
    return false;
}
void AP_Param::invalidate_count(void) {}
#if AP_PARAM_DEFAULTS_ENABLED
void AP_Param::add_default(AP_Param *ap, float v) {}
#endif

// AP_Param's conversions of parameters stored in old formats (AP_GPS::init): nothing is stored, nothing is converted
// (the translation leaves the calls out, --drop)
bool AP_Param::find_top_level_key_by_pointer(const void *ptr, uint16_t &key) { return false; }
void AP_Param::convert_old_parameters(uint16_t old_key, const ConversionInfoNoKey *conversion_table, uint8_t table_size, uint8_t flags) {}
bool AP_Param::_convert_parameter_width(ap_var_type old_ptype, float scale_factor, bool bitmask) { return false; }

// AccelCalibrator: the inertial sensor's accelerometer calibrators are never allocated (HAL_INS_ACCELCAL_ENABLED 0), so these
// members, called through the null pointer only where it is not null, are never called
#include <AP_AccelCal/AccelCalibrator.h>
void AccelCalibrator::new_sample(const Vector3f &delta_velocity, float dt) {}
bool AccelCalibrator::get_sample_corrected(uint8_t i, Vector3f &s) const { return false; }
void AccelCalibrator::get_calibration(Vector3f &offset, Vector3f &diag) const {}

// AP_HAL/system.h: the HAL's init (nothing to do)
void AP_HAL::init() {}

// AP_Param::setup_object_defaults and the two functions it calls, verbatim from AP_Param.cpp (802db19de1,
// lines 1501-1542 and 2685-2696; AP_Param.cpp itself needs the storage and the GCS): the defaults of the
// var_info table set in the object (no parameter overrides: no defaults file)
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

uint16_t AP_Param::num_param_overrides;
AP_Param::param_override *AP_Param::param_overrides;

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
