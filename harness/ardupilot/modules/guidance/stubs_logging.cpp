// stubs_logging.cpp: the logger and the internal-error reporter.
//
//   symbol                                   why it is outside the module, and what stands in
//   AP::logger(), AP_Logger::Write(name, labels, units, mults, fmt, ...)
//                                            logging. SCurve::calculate_path writes one SCVE message
//                                            when it produces invalid segment times
//                                            (SCurve.cpp:1049, once per process: a function-static
//                                            `logged_scve`). No-op; the internal error raised with
//                                            it is counted.
//   AP_InternalError::error, AP::internalerror()
//                                            the internal-error reporter, as in rate_pid: keeps the
//                                            bit, count and line; skips the HAL's persistent data.
//                                            The count is the output port wp_internal_errors; the
//                                            errors raised while the navigator was uninitialized
//                                            (adapter.cpp's hook) are also counted in
//                                            wp_internal_errors_uninit, the others raised after the
//                                            position stage returned other limits than it was
//                                            handed in wp_internal_errors_incoherent.
#include "cut.h"

#include <stdio.h>
#include <string.h>
#include <new>

#include <AP_Logger/AP_Logger.h>
#include <AP_InternalError/AP_InternalError.h>

alignas(AP_Logger) static unsigned char logger_storage[sizeof(AP_Logger)];

namespace AP {
AP_Logger &logger()
{
    return *reinterpret_cast<AP_Logger *>(logger_storage);
}
}

void AP_Logger::Write(const char *name, const char *labels, const char *units, const char *mults, const char *fmt, ...)
{
}

alignas(AP_InternalError) static unsigned char internal_error_storage[sizeof(AP_InternalError)];
bool (*harness_navigator_uninitialized)();
uint32_t harness_uninitialized_errors;
bool harness_limits_incoherent;
uint32_t harness_incoherent_errors;

void AP_InternalError::error(const AP_InternalError::error_t e, uint16_t line)
{
    internal_errors |= uint32_t(e);
    total_error_count++;
    last_line = line;
    // a trace for whoever reads standard error (replays of counterexamples); not a port
    fprintf(stderr, "guidance: internal error 0x%x at line %u\n", unsigned(e), unsigned(line));
    if (harness_navigator_uninitialized != nullptr && harness_navigator_uninitialized()) {
        harness_uninitialized_errors++;
    } else if (harness_limits_incoherent) {
        harness_incoherent_errors++;
    }
}

AP_InternalError &AP::internalerror()
{
    return *reinterpret_cast<AP_InternalError *>(internal_error_storage);
}

void harness_reset_internal_errors()
{
    memset(internal_error_storage, 0, sizeof internal_error_storage);
    new (internal_error_storage) AP_InternalError();
    harness_uninitialized_errors = 0;
    harness_limits_incoherent = false;
    harness_incoherent_errors = 0;
}

uint32_t harness_internal_error_count()
{
    return AP::internalerror().count();
}
