// stubs_hal.cpp: the hardware abstraction layer, as far as the guidance module reaches it.
//
//   symbol                      why it is outside the module, and what stands in
//   AP_HAL::millis()            the clock (HAL). AC_WPNav reads it in wp_and_spline_init_m,
//                               update_wpnav and is_active. The input port now_ms.
//   AP_HAL::micros64()          the clock; read only for the timestamp of the SCVE log message
//                               (SCurve.cpp:1052, on an invalid S-curve). Returns now_ms * 1000.
//   AP_HAL::panic(fmt, ...)     HAL; referenced by AP_Math code off the step path. Prints, aborts.
//   printf(fmt, ...)            the C library. SCurve.cpp and SplineCurve.cpp print debug lines
//                               with ::printf on the SITL board (CONFIG_HAL_BOARD == SITL) when a
//                               path is invalid (SCurve.cpp:217, 229, 434, 504, 554, 680, 953,
//                               1022, 1251-1260). Standard output carries the harness protocol, so
//                               the stand-in writes the line to standard error and counts it; each
//                               of these prints comes with an INTERNAL_ERROR (counted in
//                               wp_internal_errors) except debug()'s, which follows one.
#include "cut.h"

#include <stdarg.h>
#include <stdio.h>
#include <stdlib.h>

#include <AP_HAL/AP_HAL.h>

uint32_t harness_clock_ms;
uint32_t harness_printf_count;

uint32_t AP_HAL::millis()
{
    return harness_clock_ms;
}

uint64_t AP_HAL::micros64()
{
    return uint64_t(harness_clock_ms) * 1000U;
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

extern "C" int printf(const char *format, ...)
{
    harness_printf_count++;
    va_list ap;
    va_start(ap, format);
    fputs("guidance (ArduPilot printf): ", stderr);
    const int n = vfprintf(stderr, format, ap);
    va_end(ap);
    return n;
}
