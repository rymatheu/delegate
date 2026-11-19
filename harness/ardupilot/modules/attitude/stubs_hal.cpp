// stubs_hal.cpp: the hardware abstraction layer and the scheduler.
//
//   symbol                                   why it is outside the stage, and what stands in
//   AP_HAL::panic(const char*, ...)          HAL. AP_AHRS_View's constructor panics on an
//                                            unsupported rotation (ROTATION_NONE is used).
//                                            Prints and aborts.
//   AP_HAL::millis(), micros(), micros64()   the clock. Referenced by code the step never runs:
//                                            the PID slew limiter (AC_PID::update_all, the rate
//                                            stage's), the motors' throttle filter (output(), the
//                                            mixer's), rate_controller_run_dt's gyro time stamp
//                                            and logging. Abort: nothing on the step path reads a
//                                            clock.
//   hal, AP_HAL::HAL, AP_HAL::init()         the HAL object, with no drivers (its constructor
//                                            calls AP_HAL::init(), a no-op here). Referenced only
//                                            by the motors' arming checks and output set-up (the
//                                            mixer's), never called.
//   AP_HAL::Util::snprintf                   HAL utilities; the arming checks. Abort.
//   AP::scheduler(), AP_Scheduler            the scheduler. AC_AttitudeControl_Multi's constructor
//                                            reads get_loop_rate_hz() to set the PID notch sample
//                                            rate (no notch is configured, so the value is not
//                                            used). Zeroed storage with the active loop rate set
//                                            to SCHED_LOOP_RATE's default 400 Hz, which is what
//                                            AP_Scheduler::init leaves there; with 0 the inline
//                                            getter would raise INTERNAL_ERROR(flow_of_control).
//   AP_BoardConfig::config_error             board configuration; only the base class's default
//                                            rate_controller_run_dt (overridden by the Multi
//                                            class), never called. Abort.
#include <stdarg.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <new>

#include <AP_HAL/AP_HAL.h>
#include <AP_Scheduler/AP_Scheduler.h>
#include <AP_BoardConfig/AP_BoardConfig.h>

__attribute__((noreturn)) static void unreachable(const char *what)
{
    fprintf(stderr, "attitude: cut symbol reached: %s\n", what);
    abort();
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

uint32_t AP_HAL::millis()
{
    unreachable("AP_HAL::millis");
}

uint32_t AP_HAL::micros()
{
    unreachable("AP_HAL::micros");
}

uint64_t AP_HAL::micros64()
{
    unreachable("AP_HAL::micros64");
}

void AP_HAL::init()
{
}

int AP_HAL::Util::snprintf(char *str, size_t size, const char *format, ...)
{
    unreachable("AP_HAL::Util::snprintf");
}

void AP_BoardConfig::config_error(const char *fmt, ...)
{
    unreachable("AP_BoardConfig::config_error");
}

class HarnessHAL : public AP_HAL::HAL {
public:
    HarnessHAL() :
        AP_HAL::HAL(nullptr, nullptr, nullptr, nullptr, nullptr, nullptr, nullptr, nullptr,
                    nullptr, nullptr, nullptr, nullptr, nullptr, nullptr, nullptr, nullptr,
                    nullptr, nullptr, nullptr, nullptr, nullptr, nullptr, nullptr,
#if AP_SIM_ENABLED
                    nullptr,
#endif
#if HAL_WITH_DSP
                    nullptr,
#endif
                    nullptr) {}
    void run(int argc, char *const argv[], Callbacks *callbacks) const override
    {
        unreachable("HAL::run");
    }
};
static HarnessHAL harness_hal;
const AP_HAL::HAL &hal = harness_hal;

// --- the scheduler stand-in
alignas(AP_Scheduler) static unsigned char scheduler_storage[sizeof(AP_Scheduler)];

namespace AP {
AP_Scheduler &scheduler()
{
    return *reinterpret_cast<AP_Scheduler *>(scheduler_storage);
}
}

// the private _active_loop_rate_hz; access is not checked in an explicit instantiation's
// template arguments
static void set_active_loop_rate(AP_Scheduler &s, uint16_t hz);
template <typename T, T M>
struct SchedulerLoopRate {
    friend void set_active_loop_rate(AP_Scheduler &s, uint16_t hz) { s.*M = hz; }
};
template struct SchedulerLoopRate<decltype(&AP_Scheduler::_active_loop_rate_hz),
                                  &AP_Scheduler::_active_loop_rate_hz>;

static void harness_reset_scheduler()
{
    memset(scheduler_storage, 0, sizeof scheduler_storage);
    set_active_loop_rate(AP::scheduler(), 400);
}
