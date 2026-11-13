// The C++ environment of the AP_Mission difftest (ardupilot/Mission.json; README.md "Phase 4: AP_Mission"): what
// AP_Mission.cpp reaches outside the translation, compiled with the reference build's flags of AP_Mission.cpp's unit:
//   - the HAL: the reference vehicle's lock-step storage (reference/hal/lockstep.cpp's `class Storage`, as in
//     ardupilot/storage_env.cpp: a byte array of HAL_STORAGE_SIZE; a block that does not fit is not transferred) and
//     a Util whose `soft_armed` is the line's input;
//   - AP_HAL::millis() (the line's input), AP::ahrs().get_home() (the line's input: `_home` of an AP_AHRS that is
//     never constructed, AP_AHRS is not linked), gcs().send_text (no effect: the translation leaves GCS text out);
//   - AP_Param: saving and notification have no effect (cpp2lean --drop AP_Param::save, --param-ext);
//   - the symbols of the code the translation does not reach (the execution state machine's start_command and its
//     helpers, which call into the vehicle's libraries): never called, defined to abort.
#include <AP_HAL/AP_HAL.h>
#include <AP_Param/AP_Param.h>
#include <AP_AHRS/AP_AHRS.h>
#include <GCS_MAVLink/GCS.h>
#include <AP_InternalError/AP_InternalError.h>
#include <string.h>
#include <stdio.h>
#include <stdlib.h>
#include <stdarg.h>

// the line's inputs
bool cpp2lean_armed;
uint32_t cpp2lean_millis;

namespace AP_HAL {
void init() {}
uint32_t micros() { return 0; }
uint32_t millis() { return cpp2lean_millis; }
uint64_t micros64() { return 0; }
uint64_t millis64() { return cpp2lean_millis; }
uint16_t micros16() { return 0; }
uint16_t millis16() { return 0; }
void panic(const char *errormsg, ...)
{
    va_list ap;
    va_start(ap, errormsg);
    fprintf(stderr, "MISSION ENV: AP_HAL::panic: ");
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

class MissionUtil : public AP_HAL::Util {
public:
    void set_hw_rtc(uint64_t time_utc_usec) override {}
    uint64_t get_hw_rtc() const override { return 0; }
};

class MissionHAL : public AP_HAL::HAL {
public:
    MissionHAL(AP_HAL::Storage *storage, AP_HAL::Util *util) :
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
static MissionUtil mission_util;
static MissionHAL mission_hal(&storage, &mission_util);
const AP_HAL::HAL& hal = mission_hal;

void AP_HAL::Util::set_soft_armed(const bool b) { soft_armed = b; }
void cpp2lean_set_armed(bool b) { mission_util.soft_armed = b; }

// AP::ahrs(): never constructed; only `_home` is read (get_home, inline)
alignas(16) static unsigned char ahrs_storage[sizeof(AP_AHRS)];
AP_AHRS &AP::ahrs() { return *reinterpret_cast<AP_AHRS *>(ahrs_storage); }
Location &cpp2lean_home() { return AP::ahrs()._home; }

// GCS text: no effect
alignas(16) static unsigned char gcs_storage[sizeof(GCS)];
GCS &gcs() { return *reinterpret_cast<GCS *>(gcs_storage); }
void GCS::send_text(MAV_SEVERITY severity, const char *fmt, ...) {}

// AP_Param: storage is outside the model
void AP_Param::save(bool force_save) {}
void AP_Param::notify() const {}
void AP_Param::invalidate_count(void) {}

// one thread: the mission's semaphore is never contended (the translation's --semaphores)
WithSemaphore::WithSemaphore(AP_HAL::Semaphore &mtx, uint32_t line) : _mtx(mtx) {}
WithSemaphore::~WithSemaphore() {}

// INTERNAL_ERROR (constrain_value_line on a NaN): left out of the translation (--drop AP_InternalError::error)
void AP_InternalError::error(const AP_InternalError::error_t e, uint16_t line) {}
AP_InternalError &AP::internalerror() { alignas(16) static unsigned char ie[sizeof(AP_InternalError)]; return *reinterpret_cast<AP_InternalError *>(ie); }

// AP_Param::setup_object_defaults and the two functions it calls, verbatim from AP_Param.cpp (802db19de1,
// lines 1501-1542 and 2685-2696; AP_Param.cpp itself needs the storage and the GCS): the defaults of the
// var_info table set in the object (no parameter overrides: no defaults file)
void AP_Param::set_value(enum ap_var_type type, void *ptr, float value)
{
    switch (type) {
    case AP_PARAM_INT8:
        ((AP_Int8 *)ptr)->set(value);
        break;
    case AP_PARAM_INT16:
        ((AP_Int16 *)ptr)->set(value);
        break;
    case AP_PARAM_INT32:
        ((AP_Int32 *)ptr)->set(value);
        break;
    case AP_PARAM_FLOAT:
        ((AP_Float *)ptr)->set(value);
        break;
    default:
        break;
    }
}

void AP_Param::setup_object_defaults(const void *object_pointer, const struct GroupInfo *group_info)
{
    ptrdiff_t base = (ptrdiff_t)object_pointer;
    uint8_t type;
    for (uint8_t i=0;
         (type=group_info[i].type) != AP_PARAM_NONE;
         i++) {
        if (type <= AP_PARAM_FLOAT) {
            void *ptr = (void *)(base + group_info[i].offset);
            set_value((enum ap_var_type)type, ptr,
                      get_default_value((const AP_Param *)ptr, group_info[i]));
        } else if (type == AP_PARAM_VECTOR3F) {
            // Single default for all components
            void *ptr = (void *)(base + group_info[i].offset);
            const float default_val = get_default_value((const AP_Param *)ptr, group_info[i]);
            ((AP_Vector3f *)ptr)->set(Vector3f{default_val, default_val, default_val});
        }
    }
}

uint16_t AP_Param::num_param_overrides;
AP_Param::param_override *AP_Param::param_overrides;

float AP_Param::get_default_value(const AP_Param *vp, const struct GroupInfo &info)
{
    for (uint16_t i=0; i<num_param_overrides; i++) {
        if (vp == param_overrides[i].object_ptr) {
            return param_overrides[i].value;
        }
    }
    if ((info.flags & AP_PARAM_FLAG_DEFAULT_POINTER) != 0) {
        return *((float*)((ptrdiff_t)vp - info.def_value_offset));
    }
    return info.def_value;
}
