// stubs_misc.cpp: the internal-error reporter, logging, filter definitions.
//
//   symbol                                   why it is outside the stage, and what stands in
//   AP_InternalError::error, AP::internalerror()
//                                            the reporter (its real body also writes the HAL's
//                                            persistent data). Records bit, count and line; also
//                                            counts flow_of_control errors separately (output
//                                            pc_internal_errors_flow).
//   AP::logger(), AP_Logger::WriteBlock      logging: write_log and Write_PSCx (not called). Abort.
//   AP::filters(), AP_Filters::get_filter    filter definitions (FILT* parameters); reached only
//                                            from AC_PID::set_notch_sample_rate (not called). Abort.
//   NotchFilter<float>::apply, ::reset       the notch filter; reachable only through the accel
//                                            PID's notch pointers, which stay null (NTF = NEF = 0).
//                                            Abort.
#include <AP_InternalError/AP_InternalError.h>
#include <AP_Logger/AP_Logger.h>
#include <Filter/AP_Filter.h>
#include <Filter/NotchFilter.h>

alignas(AP_InternalError) static unsigned char internal_error_storage[sizeof(AP_InternalError)];
static uint32_t internal_error_flow_count;

void AP_InternalError::error(const AP_InternalError::error_t e, uint16_t line)
{
    internal_errors |= uint32_t(e);
    total_error_count++;
    last_line = line;
    if (e == AP_InternalError::error_t::flow_of_control) {
        internal_error_flow_count++;
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
    internal_error_flow_count = 0;
}

uint32_t harness_internal_error_count()
{
    return AP::internalerror().count();
}

uint32_t harness_internal_error_flow_count()
{
    return internal_error_flow_count;
}

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
