// ORACLE STUB (definitions): the out-of-line pieces of the libraries the control code calls into,
// replaced by minimal versions. Each block names what it replaces. Nothing here is on the control
// path's arithmetic except the AP_Param default loader (a copy of AP_Param.cpp:1501-1542 and
// :2685-2696, which only stores the var_info defaults) and the HAL clock.

#include <AP_HAL/AP_HAL.h>
#include <AP_Param/AP_Param.h>
#include <AP_AHRS/AP_AHRS.h>
#include <AP_Scheduler/AP_Scheduler.h>
#include <AP_Logger/AP_Logger.h>
#include <AP_BattMonitor/AP_BattMonitor.h>
#include <AP_Notify/AP_Notify.h>
#include <AP_InternalError/AP_InternalError.h>
#include <AP_CustomRotations/AP_CustomRotations.h>
#include <SITL/SITL.h>

#include <stdio.h>
#include <stdlib.h>
#include <stdarg.h>
#include <new>

// ---- singletons (AP::ahrs(), AP::scheduler(), ...): the environment objects of the harness
AP_AHRS oracle_ahrs;
AP_Scheduler oracle_scheduler;
static AP_Logger oracle_logger;
static AP_BattMonitor oracle_battery;
static SITL::SIM oracle_sitl;
uint32_t oracle_internal_errors;
uint32_t oracle_param_saves;

AP_AHRS &AP::ahrs() { return oracle_ahrs; }
AP_Scheduler &AP::scheduler() { return oracle_scheduler; }
AP_Logger &AP::logger() { return oracle_logger; }
AP_BattMonitor &AP::battery() { return oracle_battery; }
SITL::SIM *AP::sitl() { return &oracle_sitl; }

// AP_Notify::flags (AP_Notify.cpp): the static flags object
struct AP_Notify::notify_flags_and_values_type AP_Notify::flags;

// ---- AP_HAL (replaces AP_HAL_SITL): the clock is the sum of the loop times fed so far, as the
// Lean harness's `Scheduler.micros` (Copter/State.lean); millis = micros / 1000.
uint64_t oracle_micros;

namespace AP_HAL {
void init() {}
uint32_t micros() { return (uint32_t)oracle_micros; }
uint32_t millis() { return (uint32_t)(oracle_micros / 1000); }
uint64_t micros64() { return oracle_micros; }
uint64_t millis64() { return oracle_micros / 1000; }
uint16_t micros16() { return (uint16_t)oracle_micros; }
uint16_t millis16() { return (uint16_t)(oracle_micros / 1000); }
void panic(const char *errormsg, ...)
{
    va_list ap;
    va_start(ap, errormsg);
    fprintf(stderr, "ORACLE: AP_HAL::panic: ");
    vfprintf(stderr, errormsg, ap);
    fprintf(stderr, "\n");
    va_end(ap);
    abort();
}
}

// RCOutput: PWM output is not part of the comparison (the actuators are read before the PWM
// conversion); writes are dropped.
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

class OracleUtil : public AP_HAL::Util {
public:
    void set_hw_rtc(uint64_t time_utc_usec) override {}
    uint64_t get_hw_rtc() const override { return 0; }
};

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

// ---- AP_InternalError (AP_InternalError.cpp): count the reports, print them
static AP_InternalError oracle_internalerror;
AP_InternalError &AP::internalerror() { return oracle_internalerror; }
void AP_InternalError::error(const AP_InternalError::error_t e, uint16_t line)
{
    oracle_internal_errors++;
    fprintf(stderr, "ORACLE: INTERNAL_ERROR 0x%x at line %u\n", (unsigned)e, (unsigned)line);
}

// ---- AP_CustomRotations (vector3.cpp:264, quaternion.cpp:386): only for ROTATION_CUSTOM_*, never
// used by the control path
static AP_CustomRotations *oracle_custom_rotations;
AP_CustomRotations &AP::custom_rotations() { return *oracle_custom_rotations; }
void AP_CustomRotations::rotate(Rotation r, Vector3f &v) { AP_HAL::panic("custom rotation"); }
void AP_CustomRotations::rotate(Rotation r, Vector3d &v) { AP_HAL::panic("custom rotation"); }
void AP_CustomRotations::from_rotation(Rotation r, Quaternion &q) { AP_HAL::panic("custom rotation"); }
void AP_CustomRotations::from_rotation(Rotation r, QuaternionD &q) { AP_HAL::panic("custom rotation"); }

// ---- AP_Param (AP_Param.cpp): defaults from the real var_info tables; no storage.
// set_value, setup_object_defaults and get_default_value are copied from AP_Param.cpp:1501-1542
// and :2685-2696 without change; there are no parameter overrides from a defaults file.
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

// saves to storage: RAM value already set by the caller; nothing is stored (counted)
void AP_Param::save(bool force_save) { oracle_param_saves++; }

// ---- operator new: zero-filled, as AP_Common/c++.cpp:40-75 (ArduPilot objects rely on it)
void *operator new(size_t size) { if (size < 1) { size = 1; } return calloc(size, 1); }
void *operator new[](size_t size) { if (size < 1) { size = 1; } return calloc(size, 1); }
void *operator new(size_t size, std::nothrow_t const &) noexcept { if (size < 1) { size = 1; } return calloc(size, 1); }
void *operator new[](size_t size, std::nothrow_t const &) noexcept { if (size < 1) { size = 1; } return calloc(size, 1); }
void operator delete(void *p) noexcept { free(p); }
void operator delete[](void *p) noexcept { free(p); }
void operator delete(void *p, size_t) noexcept { free(p); }
void operator delete[](void *p, size_t) noexcept { free(p); }

// ---- SRV_Channels (SRV_Channel/SRV_Channels.cpp): servo output routing. The real header is used;
// the static functions the motors library calls are no-ops (PWM is not compared; the oracle reads
// AP_MotorsMulticopter::_actuator, as the port's protocol defines its output).
#include <SRV_Channel/SRV_Channel.h>
// AP_Motors::rc_set_freq (AP_Motors_Class.cpp:131, reached from AP_MotorsMatrix::init ->
// set_update_rate) reads _singleton->dshot_esc_type; a zero-filled object stands in for the
// constructed one (DShot type 0, PWM output only).
SRV_Channels *SRV_Channels::_singleton = (SRV_Channels *)calloc(1, sizeof(SRV_Channels));
bool SRV_Channels::emergency_stop;
bool SRV_Channels::find_channel(SRV_Channel::Function function, uint8_t &chan) { return false; }
void SRV_Channels::set_output_pwm(SRV_Channel::Function function, uint16_t value) {}
void SRV_Channels::set_output_scaled(SRV_Channel::Function function, float value) {}
uint32_t SRV_Channels::get_output_channel_mask(SRV_Channel::Function function) { return 0; }
bool SRV_Channels::set_aux_channel_default(SRV_Channel::Function function, uint8_t channel) { return true; }
void SRV_Channels::set_angle(SRV_Channel::Function function, uint16_t angle) {}
void SRV_Channels::set_range(SRV_Channel::Function function, uint16_t range) {}

// ---- AP_BoardConfig::config_error (AP_BoardConfig.cpp): fatal configuration error
#include <AP_BoardConfig/AP_BoardConfig.h>
void AP_BoardConfig::config_error(const char *fmt, ...)
{
    va_list ap;
    va_start(ap, fmt);
    fprintf(stderr, "ORACLE: config_error: ");
    vfprintf(stderr, fmt, ap);
    fprintf(stderr, "\n");
    va_end(ap);
    abort();
}

// ---- AP_HAL::Util (AP_HAL/Util.cpp): the two non-virtual members the motors library reaches
// (AP_Motors::armed -> hal.util->set_soft_armed; arming-check messages -> snprintf). The real
// Util.cpp drags in the BetterStream/printf engine; these are the same bodies without the
// watchdog persistent-data write.
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
