// stubs.cpp: what is cut from the rate_pid module, and what stands in for it.
//
// Every symbol defined here belongs to ArduPilot code outside the module (the HAL, the parameter
// storage machinery, the filter-definition singleton, the notch filter, the internal-error
// reporter's HAL side). Nothing here is on the step path of update_all except the clock and the
// internal-error counter, and both are visible through the module's ports.
//
//   symbol                                   why it is outside the module, and what stands in
//   AP_HAL::millis()                         the clock (HAL). It becomes the input port now_ms.
//   AP_HAL::panic(const char*, ...)          HAL. Referenced only by AP_Math code not on the
//                                            step path; prints and aborts if reached.
//   AP_InternalError::error(error_t, u16)    the internal-error reporter. The real body records
//                                            the error bit, the count and the line, then copies
//                                            them to the HAL's persistent data. The stand-in
//                                            keeps the first three; the count is the output
//                                            port internal_errors.
//   AP::internalerror()                      the reporter singleton; one instance here.
//   AP_Param::setup_object_defaults(...)     parameter storage: loads defaults from the var_info
//                                            table. No-op; the adapter's init sets every
//                                            AP_Param member of AC_PID.
//   AP_Param::load(), AP_Param::save(bool)   parameter storage (EEPROM). Referenced only by
//                                            AC_PID::load_gains/save_gains; abort if reached.
//   AP::filters(), AP_Filters::get_filter    the filter-definition singleton (FILT* parameters).
//                                            Referenced only by set_notch_sample_rate, which the
//                                            module never calls; abort if reached.
//   NotchFilter<float>::apply, ::reset       the notch filter (its source pulls in MAVLink
//                                            logging). Called only through the notch pointers,
//                                            which stay null because NTF = NEF = 0 and
//                                            set_notch_sample_rate is never called; abort if
//                                            reached.
#include <stdarg.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <new>

#include <AP_HAL/AP_HAL.h>
#include <AP_Param/AP_Param.h>
#include <AP_InternalError/AP_InternalError.h>
#include <Filter/AP_Filter.h>
#include <Filter/NotchFilter.h>

uint32_t harness_clock_ms;

__attribute__((noreturn)) static void unreachable(const char *what)
{
    fprintf(stderr, "rate_pid: cut symbol reached: %s\n", what);
    abort();
}

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

bool AP_Param::load(void)
{
    unreachable("AP_Param::load");
}

void AP_Param::save(bool force_save)
{
    unreachable("AP_Param::save");
}

// --- filter definitions and notch filter
AP_Filters &AP::filters()
{
    unreachable("AP::filters");
}

AP_Filter *AP_Filters::get_filter(uint8_t filt_num)
{
    unreachable("AP_Filters::get_filter");
}

template <>
float NotchFilter<float>::apply(const float &sample)
{
    unreachable("NotchFilter<float>::apply");
}

template <>
void NotchFilter<float>::reset()
{
    unreachable("NotchFilter<float>::reset");
}
