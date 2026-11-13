// The C++ environment of StorageManager's difftest (ardupilot/StorageManager.json): the HAL object with
// the reference vehicle's storage (reference/hal/lockstep.cpp's `class Storage`, copied: a byte array
// of HAL_STORAGE_SIZE; a block that does not fit is not transferred), which `hal.storage` reaches.
#include <AP_HAL/AP_HAL.h>
#include <string.h>
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
    fprintf(stderr, "STORAGE ENV: AP_HAL::panic: ");
    vfprintf(stderr, errormsg, ap);
    fprintf(stderr, "\n");
    va_end(ap);
    abort();
}
}

class Storage : public AP_HAL::Storage {
public:
    void init() override {}
    void read_block(void *dst, uint16_t src, size_t n) override {
        if (size_t(src) + n > sizeof(buf)) {
            return;
        }
        memcpy(dst, &buf[src], n);
    }
    void write_block(uint16_t dst, const void *src, size_t n) override {
        if (size_t(dst) + n > sizeof(buf)) {
            return;
        }
        memcpy(&buf[dst], src, n);
    }
    bool healthy() override { return true; }
private:
    uint8_t buf[HAL_STORAGE_SIZE];
};

class StorageUtil : public AP_HAL::Util {
public:
    void set_hw_rtc(uint64_t time_utc_usec) override {}
    uint64_t get_hw_rtc() const override { return 0; }
};

class StorageHAL : public AP_HAL::HAL {
public:
    StorageHAL(AP_HAL::Storage *storage, AP_HAL::Util *util) :
        AP_HAL::HAL(nullptr, nullptr, nullptr, nullptr, nullptr, nullptr, nullptr, nullptr, nullptr, nullptr,
                    nullptr, nullptr, nullptr, nullptr, storage, nullptr, nullptr, nullptr,
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

static Storage storage;
static StorageUtil storage_util;
static StorageHAL storage_hal(&storage, &storage_util);
const AP_HAL::HAL& hal = storage_hal;
