// stubs.cpp: what is cut from the mixer module, and what stands in for it.
//
// Every symbol defined here belongs to ArduPilot code outside the module. On the step path of
// AP_MotorsMulticopter::output() the mixer reads the clock, the battery monitor and the AHRS, and
// writes the motor PWM through SRV_Channels; each of these is an input or output port. The rest
// is reached only at init (HAL output set-up), on disarm (parameter save), or never.
//
//   symbol                                   why it is outside the module, and what stands in
//   AP_HAL::micros()                         the clock (HAL), read by the throttle slew detector
//                                            in update_throttle_filter. The input port now_us.
//   AP_HAL::micros64()                       the clock; referenced only by logging. Abort.
//   AP_HAL::panic(const char*, ...)          HAL; AP_MotorsMatrix's constructor panics if a second
//                                            mixer exists (the adapter clears the singleton
//                                            first). Prints and aborts.
//   AP_HAL::init(), hal                      the HAL object. Its only member used is rcout.
//   AP_HAL::RCOutput (hal.rcout)             the output driver. At init set_update_rate calls
//                                            set_freq, set_dshot_esc_type, set_output_mode, and
//                                            update_throttle_range calls set_esc_scaling (the real
//                                            inline code). The stand-in records nothing; its other
//                                            methods (never called by the mixer) abort.
//   SRV_Channels::set_output_pwm(fn, pwm)    the servo-output library. rc_write calls it with each
//                                            motor's PWM in output_to_motors. The stand-in keeps the
//                                            PWM per motor function k_motor1..: output ports pwm_n
//                                            and pwm_writes.
//   SRV_Channels::set_output_scaled(fn, v)   the servo-output library: the booster-throttle and the
//                                            roll/pitch/yaw/thrust pass-through functions
//                                            (output_boost_throttle, output_rpyt), outputs to other
//                                            servos. No-op.
//   SRV_Channels::set_aux_channel_default    the servo-output library: default SERVOn_FUNCTION for
//                                            each motor (add_motor_num, at init). No-op: the
//                                            mapping is SERVOn_FUNCTION = Motor n.
//   SRV_Channels::get_output_channel_mask    the servo-output library: Motor n -> channel n (the
//                                            default mapping); other functions none. Used at init
//                                            (rc_set_freq, get_motor_mask).
//   SRV_Channels::_singleton, digital_mask   the servo-output library's state: get_dshot_esc_type
//                                            (inline, init only) reads SERVO_DSHOT_ESC from the
//                                            singleton, have_digital_outputs reads digital_mask.
//                                            Zeroed storage: SERVO_DSHOT_ESC = 0, no digital
//                                            outputs.
//   SRV_Channels::find_channel, set_range,   the servo-output library; referenced only by arming
//   set_angle, get_emergency_stop            and motor-test checks and the PWM_RANGE/ANGLE types,
//                                            never called. Abort.
//   AP::battery(), AP_BattMonitor::voltage,  the battery monitor. update_lift_max_from_batt_voltage
//   ::voltage_resting_estimate,              reads the resting-voltage estimate (MOT_OPTIONS = 0),
//   ::current_amps, ::get_resistance         get_current_limit_max_throttle reads the current, the
//                                            voltage and the resistance (get_resistance is inline
//                                            and reads the monitor's private state[0].resistance,
//                                            set here). The input ports batt_*.
//   AP::ahrs(), AP_AHRS::get_air_density_ratio
//                                            the AHRS: get_compensation_gain reads the air-density
//                                            ratio (1/EAS2TAS^2) on every step. The input port
//                                            air_density_ratio.
//   AP_InternalError::error, AP::internalerror()
//                                            the internal-error reporter, as in rate_pid: keeps the
//                                            bit, count and line; skips the HAL's persistent data.
//                                            The count is the output port internal_errors.
//   AP_Param::setup_object_defaults(...)     parameter storage: defaults from var_info. No-op; the
//                                            adapter sets every AP_Param member the mixer reads.
//   AP_Param::save(bool)                     parameter storage (EEPROM). Reached on disarm:
//                                            save_params_on_disarm saves MOT_THST_HOVER
//                                            (MOT_HOVER_LEARN = 2). No-op.
//   AP_Param::configured(), set_and_default  parameter storage; only convert_pwm_min_max_param and
//                                            update_throttle_range's digital-output branch, not
//                                            reached. Abort.
//   AP_Notify::flags                         the notification library (LEDs, buzzer): armed()
//                                            writes flags.armed. Storage only; nothing reads it.
//   AP::logger(), AP_Logger::WriteBlock      logging: Log_Write, Log_Write_SPOL, not on the step
//                                            path. Abort.
#include <stdarg.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <new>

#include <AP_HAL/AP_HAL.h>
#include <AP_Param/AP_Param.h>
#include <AP_InternalError/AP_InternalError.h>
#include <AP_Motors/AP_Motors_Class.h>
#include <SRV_Channel/SRV_Channel.h>
#include <AP_BattMonitor/AP_BattMonitor.h>
#include <AP_AHRS/AP_AHRS.h>
#include <AP_Notify/AP_Notify.h>
#include <AP_Logger/AP_Logger.h>

__attribute__((noreturn)) static void unreachable(const char *what)
{
    fprintf(stderr, "mixer: cut symbol reached: %s\n", what);
    abort();
}

// --- the values the step reads outside the module, set by the adapter from the input record
uint32_t harness_clock_us;
float harness_batt_voltage;
float harness_batt_resting_voltage;
float harness_batt_current;
bool harness_batt_current_ok;
float harness_air_density_ratio;
// --- what the step writes outside the module, read by the adapter into the output record
uint16_t harness_motor_pwm[AP_MOTORS_MAX_NUM_MOTORS];
uint32_t harness_motor_pwm_writes;

// --- clock and HAL
uint32_t AP_HAL::micros()
{
    return harness_clock_us;
}

uint64_t AP_HAL::micros64()
{
    unreachable("AP_HAL::micros64");
}

void AP_HAL::panic(const char *errormsg, ...)
{
    va_list ap;
    va_start(ap, errormsg);
    vfprintf(stderr, errormsg, ap);
    va_end(ap);
    fprintf(stderr, "\n");
    abort();
}

void AP_HAL::init()
{
}

class HarnessRCOutput : public AP_HAL::RCOutput {
public:
    void init() override { unreachable("RCOutput::init"); }
    void set_freq(uint32_t chmask, uint16_t freq_hz) override {}
    uint16_t get_freq(uint8_t chan) override { unreachable("RCOutput::get_freq"); }
    void enable_ch(uint8_t chan) override { unreachable("RCOutput::enable_ch"); }
    void disable_ch(uint8_t chan) override { unreachable("RCOutput::disable_ch"); }
    void write(uint8_t chan, uint16_t period_us) override { unreachable("RCOutput::write"); }
    void cork() override { unreachable("RCOutput::cork"); }
    void push() override { unreachable("RCOutput::push"); }
    uint16_t read(uint8_t chan) override { unreachable("RCOutput::read"); }
    void read(uint16_t *period_us, uint8_t len) override { unreachable("RCOutput::read"); }
};

class HarnessHAL : public AP_HAL::HAL {
public:
    HarnessHAL(AP_HAL::RCOutput *rcout) :
        AP_HAL::HAL(nullptr, nullptr, nullptr, nullptr, nullptr, nullptr, nullptr, nullptr, nullptr,
                    nullptr, nullptr, nullptr, nullptr, nullptr, nullptr, nullptr, nullptr, nullptr,
                    rcout, nullptr, nullptr, nullptr, nullptr,
#if AP_SIM_ENABLED
                    nullptr,
#endif
#if HAL_WITH_DSP
                    nullptr,
#endif
                    nullptr) {}
    void run(int argc, char *const argv[], Callbacks *callbacks) const override { unreachable("HAL::run"); }
};

static HarnessRCOutput harness_rcout;
static HarnessHAL harness_hal(&harness_rcout);
const AP_HAL::HAL &hal = harness_hal;

// --- servo outputs
void SRV_Channels::set_output_pwm(SRV_Channel::Function function, uint16_t value)
{
    const int n = int(function) - int(SRV_Channel::k_motor1);
    if (n >= 0 && n < 8) {
        harness_motor_pwm[n] = value;
        harness_motor_pwm_writes++;
    } else {
        unreachable("SRV_Channels::set_output_pwm for a non-motor function");
    }
}

void SRV_Channels::set_output_scaled(SRV_Channel::Function function, float value)
{
}

bool SRV_Channels::set_aux_channel_default(SRV_Channel::Function function, uint8_t channel)
{
    return true;
}

uint32_t SRV_Channels::get_output_channel_mask(SRV_Channel::Function function)
{
    const int n = int(function) - int(SRV_Channel::k_motor1);
    return (n >= 0 && n < 8) ? (1U << n) : 0U;
}

alignas(SRV_Channels) static unsigned char srv_channels_storage[sizeof(SRV_Channels)];
SRV_Channels *SRV_Channels::_singleton = reinterpret_cast<SRV_Channels *>(srv_channels_storage);
uint32_t SRV_Channels::digital_mask;

bool SRV_Channels::emergency_stop;

bool SRV_Channels::find_channel(SRV_Channel::Function function, uint8_t &chan)
{
    unreachable("SRV_Channels::find_channel");
}

void SRV_Channels::set_range(SRV_Channel::Function function, uint16_t range)
{
    unreachable("SRV_Channels::set_range");
}

void SRV_Channels::set_angle(SRV_Channel::Function function, uint16_t angle)
{
    unreachable("SRV_Channels::set_angle");
}

// --- battery monitor
alignas(AP_BattMonitor) static unsigned char battery_storage[sizeof(AP_BattMonitor)];

AP_BattMonitor &AP::battery()
{
    return *reinterpret_cast<AP_BattMonitor *>(battery_storage);
}

float AP_BattMonitor::voltage(uint8_t instance) const
{
    return harness_batt_voltage;
}

float AP_BattMonitor::voltage_resting_estimate(uint8_t instance) const
{
    return harness_batt_resting_voltage;
}

bool AP_BattMonitor::current_amps(float &current, const uint8_t instance) const
{
    if (!harness_batt_current_ok) {
        return false;
    }
    current = harness_batt_current;
    return true;
}

// get_resistance(i) is inline and returns the private state[i].resistance; it is set there.
// Access is not checked in an explicit instantiation's template arguments.
typedef AP_BattMonitor::BattMonitor_State BattStates[AP_BATT_MONITOR_MAX_INSTANCES];
static void set_resistance(float r);
template <BattStates AP_BattMonitor::*S>
struct BattState {
    friend void set_resistance(float r)
    {
        (AP::battery().*S)[0].resistance = r;
    }
};
template struct BattState<&AP_BattMonitor::state>;

void harness_set_batt_resistance(float r)
{
    set_resistance(r);
}

// --- AHRS
alignas(AP_AHRS) static unsigned char ahrs_storage[sizeof(AP_AHRS)];

AP_AHRS &AP::ahrs()
{
    return *reinterpret_cast<AP_AHRS *>(ahrs_storage);
}

float AP_AHRS::get_air_density_ratio(void) const
{
    return harness_air_density_ratio;
}

// --- internal-error reporter
alignas(AP_InternalError) static unsigned char internal_error_storage[sizeof(AP_InternalError)];

void AP_InternalError::error(const AP_InternalError::error_t e, uint16_t line)
{
    internal_errors |= uint32_t(e);
    total_error_count++;
    last_line = line;
}

AP_InternalError &AP::internalerror()
{
    return *reinterpret_cast<AP_InternalError *>(internal_error_storage);
}

void harness_reset_internal_errors()
{
    memset(internal_error_storage, 0, sizeof internal_error_storage);
    new (internal_error_storage) AP_InternalError();
}

uint32_t harness_internal_error_count()
{
    return AP::internalerror().count();
}

// --- parameter storage
void AP_Param::setup_object_defaults(const void *object_pointer, const struct GroupInfo *group_info)
{
}

void AP_Param::save(bool force_save)
{
}

bool AP_Param::configured(void) const
{
    unreachable("AP_Param::configured");
}

template <>
void AP_ParamTBase<int16_t, AP_PARAM_INT16>::set_and_default(const int16_t &v)
{
    unreachable("AP_ParamTBase<int16_t>::set_and_default");
}

// --- HAL utilities: snprintf, referenced only by the arming checks
int AP_HAL::Util::snprintf(char *str, size_t size, const char *format, ...)
{
    unreachable("AP_HAL::Util::snprintf");
}

// --- notification and logging
struct AP_Notify::notify_flags_and_values_type AP_Notify::flags;

namespace AP {
AP_Logger &logger()
{
    unreachable("AP::logger");
}
}

void AP_Logger::WriteBlock(const void *pBuffer, uint16_t size)
{
    unreachable("AP_Logger::WriteBlock");
}

// --- reset of the cut's state, at every init
void harness_reset_cut()
{
    harness_clock_us = 0;
    harness_batt_voltage = 0.0f;
    harness_batt_resting_voltage = 0.0f;
    harness_batt_current = 0.0f;
    harness_batt_current_ok = false;
    harness_air_density_ratio = 0.0f;
    memset(harness_motor_pwm, 0, sizeof harness_motor_pwm);
    harness_motor_pwm_writes = 0;
    memset(battery_storage, 0, sizeof battery_storage);
    memset(ahrs_storage, 0, sizeof ahrs_storage);
    memset(srv_channels_storage, 0, sizeof srv_channels_storage);
}
