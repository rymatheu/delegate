// stubs_hal.cpp: the hardware abstraction layer.
//
//   symbol                    why it is outside the stage, and what stands in
//   AP_HAL::millis()          the clock (HAL), read by set_pilot_desired_acceleration_rad (the
//                             brake timer, AC_Loiter.cpp:184) and calc_desired_velocity (:356).
//                             The input port now_ms.
//   AP_HAL::panic(...)        HAL; reached by no code on the step path. Prints and aborts.
#include <stdarg.h>
#include <stdio.h>
#include <stdlib.h>

#include <AP_HAL/AP_HAL.h>
#include "cut.h"

__attribute__((noreturn)) static void unreachable(const char *what)
{
    fprintf(stderr, "loiter: cut symbol reached: %s\n", what);
    abort();
}

uint32_t harness_clock_ms;

uint32_t AP_HAL::millis()
{
    return harness_clock_ms;
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
