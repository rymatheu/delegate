// Unity translation unit for cpp2lean: ArduPilot's AP_InternalError (AP_InternalError.cpp, included
// unmodified) and the text formatter it calls through `hal.util->snprintf` (README.md, "Phase 2b").
#include <AP_InternalError/AP_InternalError.cpp>
#include <AP_HAL/utility/print_vprintf.cpp>
#include <AP_HAL/utility/ftoa_engine.cpp>
#include <AP_HAL/utility/utoa_invert.cpp>
#include <AP_HAL/Util.cpp>

extern const AP_HAL::HAL& hal;

// The test function the difftest drives: an AP_InternalError whose state is set through its object
// representation (a byte-level object, --byte-objects: errors, count and line at offsets 0, 4, 8 of
// its 12 bytes), then errors_as_string into a buffer of len bytes, and the accessors. (error(),
// which also writes `hal.util->persistent_data`, is not driven: the C++ harness does not log that
// boundary write; README.md, "Phase 2b".)
uint64_t ie_string(uint8_t buf[64], uint32_t errors, uint32_t count, uint16_t line, uint8_t len)
{
    AP_InternalError e{};
    uint8_t raw[sizeof(e)];
    memset(raw, 0, sizeof(raw));
    memcpy(raw, &errors, sizeof(errors));
    memcpy(raw + 4, &count, sizeof(count));
    memcpy(raw + 8, &line, sizeof(line));
    memcpy(&e, raw, sizeof(e));
    e.errors_as_string(buf, len % 65);
    return e.errors() ^ ((uint64_t)e.count() << 32) ^ ((uint64_t)e.last_error_line() << 48) ^ sizeof(e);
}
