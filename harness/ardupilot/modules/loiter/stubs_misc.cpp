// stubs_misc.cpp: the internal-error reporter.
//
//   symbol                                   why it is outside the stage, and what stands in
//   AP_InternalError::error, AP::internalerror()
//                                            the reporter (its real body also writes the HAL's
//                                            persistent data). Records bit, count and line (output
//                                            lt_internal_errors). No code on the step path raises
//                                            one; the reporter is here so that any would be seen.
#include <string.h>
#include <new>

#include <AP_InternalError/AP_InternalError.h>

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
