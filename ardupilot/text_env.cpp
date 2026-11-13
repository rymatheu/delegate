// The C++ environment of the text formatter's difftest (ardupilot/Text.json): the HAL object that
// `hal.util->snprintf` reaches (a Util with the pure virtual members defined trivially; snprintf and
// vsnprintf are AP_HAL/Util.cpp's own, compiled in ardupilot/unity_text.cpp), and the HAL functions
// Util.cpp and AP_InternalError.cpp link against. Nothing here is on the formatter's path.
#include <AP_HAL/AP_HAL.h>
#include <stdio.h>
#include <stdlib.h>
#include <stdarg.h>

namespace AP_HAL {
void init() {}
uint32_t micros() { return 0; }
uint32_t millis() { return 0; }
uint64_t micros64() { return 0; }
uint64_t millis64() { return 0; }
uint16_t micros16() { return 0; }
uint16_t millis16() { return 0; }
void panic(const char *errormsg, ...)
{
    va_list ap;
    va_start(ap, errormsg);
    fprintf(stderr, "TEXT ENV: AP_HAL::panic: ");
    vfprintf(stderr, errormsg, ap);
    fprintf(stderr, "\n");
    va_end(ap);
    abort();
}
}

class TextUtil : public AP_HAL::Util {
public:
    void set_hw_rtc(uint64_t time_utc_usec) override {}
    uint64_t get_hw_rtc() const override { return 0; }
};

class TextHAL : public AP_HAL::HAL {
public:
    TextHAL(AP_HAL::Util *util) :
        AP_HAL::HAL(nullptr, nullptr, nullptr, nullptr, nullptr, nullptr, nullptr, nullptr, nullptr, nullptr,
                    nullptr, nullptr, nullptr, nullptr, nullptr, nullptr, nullptr, nullptr,
                    nullptr, nullptr, util, nullptr, nullptr,
#if AP_SIM_ENABLED
                    nullptr,
#endif
#if HAL_WITH_DSP
                    nullptr,
#endif
                    nullptr) {}
    void run(int argc, char * const argv[], Callbacks* callbacks) const override {}
};

static TextUtil text_util;
static TextHAL text_hal(&text_util);
const AP_HAL::HAL& hal = text_hal;
