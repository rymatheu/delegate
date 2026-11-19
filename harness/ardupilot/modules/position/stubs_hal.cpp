// stubs_hal.cpp: the hardware abstraction layer.
//
//   symbol                    why it is outside the stage, and what stands in
//   AP_HAL::millis()          the clock (HAL), read by the offset-target time-outs
//                             (NE/D_init_offsets, NE/D_update_offsets) and by the accel PID's
//                             slew limiter (SlewLimiter::modifier). The input port now_ms.
//   AP_HAL::panic(...)        HAL; reached by no code on the step path. Prints and aborts.
//   AP_HAL::init()            HAL start-up, referenced by the HAL object's constructor. No-op.
//   hal (AP_HAL::HAL)         the HAL object; AC_PosControl::pre_arm_checks refers to hal.util
//                             (never called). Every driver pointer is null.
#include <stdarg.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <new>

#include <AP_HAL/AP_HAL.h>
#include "stand_ins.h"

__attribute__((noreturn)) static void unreachable(const char *what)
{
    fprintf(stderr, "position: cut symbol reached: %s\n", what);
    abort();
}

HarnessCut harness_cut;

uint32_t AP_HAL::millis()
{
    return harness_cut.now_ms;
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

class HarnessHAL : public AP_HAL::HAL {
public:
    HarnessHAL() :
        AP_HAL::HAL(nullptr, nullptr, nullptr, nullptr, nullptr, nullptr, nullptr, nullptr, nullptr,
                    nullptr, nullptr, nullptr, nullptr, nullptr, nullptr, nullptr, nullptr, nullptr,
                    nullptr, nullptr, nullptr, nullptr, nullptr,
#if AP_SIM_ENABLED
                    nullptr,
#endif
#if HAL_WITH_DSP
                    nullptr,
#endif
                    nullptr) {}
    void run(int argc, char *const argv[], Callbacks *callbacks) const override { unreachable("HAL::run"); }
};

static HarnessHAL harness_hal;
const AP_HAL::HAL &hal = harness_hal;
