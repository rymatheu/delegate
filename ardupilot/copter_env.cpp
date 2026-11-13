// cpp2lean difftest environment for the World translation of the vehicle's controllers
// (ardupilot/unity_copter.cpp, ardupilot/Copter.json): the out-of-line library pieces that
// AP_MotorsMatrix, AC_AttitudeControl_Multi, AC_PosControl and AC_WPNav call into, from
// ardupilot/stubs/oracle_env.cpp (blocks marked "copied" are unchanged), with the boundary made
// observable, as in ardupilot/ap_motors_env.cpp, ac_control_env.cpp and ac_wpnav_env.cpp, which it
// merges:
//   - the boundary object of the World, `cpp2lean_ahrs_view` (unity_copter.cpp:35), the AHRS view
//     stub (ardupilot/stubs/AP_AHRS/AP_AHRS_View.h) on the AHRS stub `oracle_ahrs` (AP::ahrs());
//     the driver writes their members from the line;
//   - the clocks (AP_HAL::micros, AP_HAL::millis, AP_HAL::micros64), the scheduler's loop time and
//     tick counter, SITL's lock-step flag and AP_Param::configured() are the driver's inputs;
//   - the motors' output functions to the HAL are recorded in the output log (cpp2lean_events.h),
//     in the format of the Lean side's `Output` events: SRV_Channels::set_output_scaled /
//     set_output_pwm -> set_output_scaled / set_output_pwm events; SRV_Channels::set_aux_channel_default,
//     called only by AP_Motors::add_motor_num (AP_Motors_Class.cpp:218-225) -> the add_motor_num
//     event (rc_write, rc_write_angle, rc_set_freq are recorded by the driver's subclass of
//     AP_MotorsMatrix, ardupilot/ap_motors_driver.h; hal.rcout->set_esc_scaling, a non-virtual inline
//     setter, by the driver after update_throttle_range).
// The configuration queries return what the oracle's stubs return: no output channel masks, no
// digital outputs.

#include "cpp2lean_events.h"
#include <AP_HAL/AP_HAL.h>
#include <AP_Param/AP_Param.h>
#include <AP_AHRS/AP_AHRS.h>
#include <AP_AHRS/AP_AHRS_View.h>
#include <AP_Logger/AP_Logger.h>
#include <AP_BattMonitor/AP_BattMonitor.h>
#include <AP_Notify/AP_Notify.h>
#include <AP_InternalError/AP_InternalError.h>
#include <SRV_Channel/SRV_Channel.h>
#include <AP_BoardConfig/AP_BoardConfig.h>
#include <AP_Scheduler/AP_Scheduler.h>
#include <AP_CustomRotations/AP_CustomRotations.h>
#include <SITL/SITL.h>
#include <stdio.h>
#include <stdlib.h>
#include <stdarg.h>

std::string cpp2lean_events;
uint32_t cpp2lean_micros;           // AP_HAL::micros(): the driver's input `motors.micros`
uint32_t cpp2lean_millis;           // AP_HAL::millis(): the driver's input `pos_control.millis`
uint64_t cpp2lean_micros64;         // AP_HAL::micros64(): the driver's input `attitude_control.micros64`
bool cpp2lean_param_configured;      // AP_Param::configured(): the driver's input
uint32_t oracle_internal_errors;
uint32_t oracle_param_saves;

AP_AHRS oracle_ahrs;                 // sample (gyro, position, velocity, accel_ef, air density): the driver's inputs
AP_AHRS_View cpp2lean_ahrs_view(oracle_ahrs, ROTATION_NONE);   // the World's boundary (unity_copter.cpp:35)
static AP_Logger oracle_logger;
static AP_BattMonitor oracle_battery;
AP_Scheduler cpp2lean_scheduler;     // _last_loop_time_s, _tick_counter32: the driver's inputs
SITL::SIM cpp2lean_sitl;             // state.is_lock_step_scheduled: the driver's input
AP_AHRS &AP::ahrs() { return oracle_ahrs; }
AP_Scheduler &AP::scheduler() { return cpp2lean_scheduler; }
SITL::SIM *AP::sitl() { return &cpp2lean_sitl; }
AP_Logger &AP::logger() { return oracle_logger; }
AP_BattMonitor &AP::battery() { return oracle_battery; }

// copied: AP_Notify::flags (AP_Notify.cpp): the static flags object
struct AP_Notify::notify_flags_and_values_type AP_Notify::flags;

namespace AP_HAL {
void init() {}
uint32_t micros() { return cpp2lean_micros; }
uint32_t millis() { return cpp2lean_millis; }
uint64_t micros64() { return cpp2lean_micros64; }
uint64_t millis64() { return cpp2lean_micros / 1000; }
void panic(const char *errormsg, ...)
{
    va_list ap;
    va_start(ap, errormsg);
    fprintf(stderr, "AP_HAL::panic: ");
    vfprintf(stderr, errormsg, ap);
    fprintf(stderr, "\n");
    va_end(ap);
    abort();
}
}

// copied
class OracleRCOutput : public AP_HAL::RCOutput {
public:
    void init() override {}
    void set_freq(uint32_t chmask, uint16_t freq_hz) override {}
    uint16_t get_freq(uint8_t chan) override { return 50; }
    void enable_ch(uint8_t chan) override {}
    void disable_ch(uint8_t chan) override {}
    void write(uint8_t chan, uint16_t period_us) override {}
    void cork() override {}
    void push() override {}
    uint16_t read(uint8_t chan) override { return 0; }
    void read(uint16_t* period_us, uint8_t len) override {}
};

// copied
class OracleUtil : public AP_HAL::Util {
public:
    void set_hw_rtc(uint64_t time_utc_usec) override {}
    uint64_t get_hw_rtc() const override { return 0; }
};

// copied
class OracleHAL : public AP_HAL::HAL {
public:
    OracleHAL(AP_HAL::RCOutput *rcout, AP_HAL::Util *util) :
        AP_HAL::HAL(nullptr, nullptr, nullptr, nullptr, nullptr, nullptr, nullptr, nullptr, nullptr, nullptr,
                    nullptr, nullptr, nullptr, nullptr, nullptr, nullptr, nullptr, nullptr,
                    rcout, nullptr, util, nullptr, nullptr,
#if AP_SIM_ENABLED
                    nullptr,
#endif
#if HAL_WITH_DSP
                    nullptr,
#endif
                    nullptr) {}
    void run(int argc, char * const argv[], Callbacks* callbacks) const override {}
};

static OracleRCOutput oracle_rcout;
static OracleUtil oracle_util;
static OracleHAL oracle_hal(&oracle_rcout, &oracle_util);
const AP_HAL::HAL& hal = oracle_hal;

// copied: AP_InternalError (counts the reports)
static AP_InternalError oracle_internalerror;
AP_InternalError &AP::internalerror() { return oracle_internalerror; }
void AP_InternalError::error(const AP_InternalError::error_t e, uint16_t line)
{
    oracle_internal_errors++;
}

// copied: AP_CustomRotations (vector3.cpp:264, quaternion.cpp:386): only for ROTATION_CUSTOM_*, never reached
static AP_CustomRotations *oracle_custom_rotations;
AP_CustomRotations &AP::custom_rotations() { return *oracle_custom_rotations; }
void AP_CustomRotations::rotate(Rotation r, Vector3f &v) { AP_HAL::panic("custom rotation"); }
void AP_CustomRotations::rotate(Rotation r, Vector3d &v) { AP_HAL::panic("custom rotation"); }
void AP_CustomRotations::from_rotation(Rotation r, Quaternion &q) { AP_HAL::panic("custom rotation"); }
void AP_CustomRotations::from_rotation(Rotation r, QuaternionD &q) { AP_HAL::panic("custom rotation"); }

// copied: AP_Param (AP_Param.cpp:1501-1542, :2685-2696): defaults from the real var_info tables; no storage
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

// copied: saves to storage: RAM value already set by the caller; nothing is stored (counted)
void AP_Param::save(bool force_save) { oracle_param_saves++; }
// storage state, outside the model: the driver's input (both parameters that ask read the same value)
bool AP_Param::configured(void) const { return cpp2lean_param_configured; }
bool AP_Param::load(void) { return false; }
// AC_WPNav::convert_parameters (dropped from the translation, never called): parameter storage
void AP_Param::convert_old_parameters_scaled(const ConversionInfo *conversion_table, uint8_t table_size, float scaler, uint8_t flags) {}
#if AP_PARAM_DEFAULTS_ENABLED
void AP_Param::add_default(AP_Param *ap, float v) {}
#endif

// SRV_Channels (SRV_Channel/SRV_Channels.cpp): the static functions the motors library calls;
// as oracle_env.cpp, with the outputs recorded
SRV_Channels *SRV_Channels::_singleton = (SRV_Channels *)calloc(1, sizeof(SRV_Channels));
bool SRV_Channels::emergency_stop;
uint32_t SRV_Channels::digital_mask;     // no digital outputs (have_digital_outputs(mask) is false)
bool SRV_Channels::find_channel(SRV_Channel::Function function, uint8_t &chan) { return false; }
void SRV_Channels::set_output_pwm(SRV_Channel::Function function, uint16_t value) { cpp2lean_ev("set_output_pwm"); cpp2lean_ev_i(function); cpp2lean_ev_u(value); }
void SRV_Channels::set_output_scaled(SRV_Channel::Function function, float value) { cpp2lean_ev("set_output_scaled"); cpp2lean_ev_i(function); cpp2lean_ev_f(value); }
uint32_t SRV_Channels::get_output_channel_mask(SRV_Channel::Function function) { return 0; }
bool SRV_Channels::set_aux_channel_default(SRV_Channel::Function function, uint8_t channel) { cpp2lean_ev("add_motor_num"); cpp2lean_ev_i((int8_t)channel); return true; }
void SRV_Channels::set_angle(SRV_Channel::Function function, uint16_t angle) {}
void SRV_Channels::set_range(SRV_Channel::Function function, uint16_t range) {}

// copied: AP_BoardConfig::config_error, AP_HAL::Util::snprintf, set_soft_armed
void AP_BoardConfig::config_error(const char *fmt, ...)
{
    va_list ap;
    va_start(ap, fmt);
    fprintf(stderr, "config_error: ");
    vfprintf(stderr, fmt, ap);
    fprintf(stderr, "\n");
    va_end(ap);
    abort();
}
int AP_HAL::Util::snprintf(char* str, size_t size, const char *format, ...)
{
    va_list ap;
    va_start(ap, format);
    int res = ::vsnprintf(str, size, format, ap);
    va_end(ap);
    return res;
}
void AP_HAL::Util::set_soft_armed(const bool b)
{
    if (b != soft_armed) {
        soft_armed = b;
        last_armed_change_ms = AP_HAL::millis();
    }
}
