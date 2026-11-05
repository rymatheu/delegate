// cpp2lean difftest environment for AC_PID: the out-of-line library pieces AC_PID, SlewLimiter,
// LowPassFilter and AP_Math call into, taken from ardupilot/stubs/oracle_env.cpp (blocks copied
// without change where marked), with the clock driven by the driver: AP_HAL::millis() returns
// `cpp2lean_millis`, which the class driver sets from each input line (the Lean side reads the
// same value as the input `_slew_limiter.millis`).

#include <AP_HAL/AP_HAL.h>
#include <AP_Math/AP_Math.h>
#include <AP_Param/AP_Param.h>
#include <AP_InternalError/AP_InternalError.h>
#include <stdio.h>
#include <stdlib.h>
#include <stdarg.h>

uint32_t cpp2lean_millis;
uint32_t oracle_internal_errors;
uint32_t oracle_param_saves;

namespace AP_HAL {
uint32_t millis() { return cpp2lean_millis; }
uint32_t micros() { return cpp2lean_millis * 1000U; }
void panic(const char *errormsg, ...)
{
    va_list ap;
    va_start(ap, errormsg);
    fprintf(stderr, "AP_HAL::panic: ");
    vfprintf(stderr, errormsg, ap);
    fprintf(stderr, "\n");
    va_end(ap);
    abort();
}
}

// ---- copied from ardupilot/stubs/oracle_env.cpp: AP_InternalError (counts the reports)
static AP_InternalError oracle_internalerror;
AP_InternalError &AP::internalerror() { return oracle_internalerror; }
void AP_InternalError::error(const AP_InternalError::error_t e, uint16_t line)
{
    oracle_internal_errors++;
}

// ---- copied from ardupilot/stubs/oracle_env.cpp: AP_Param (AP_Param.cpp): defaults from the real var_info tables; no storage.
// set_value, setup_object_defaults and get_default_value are copied from AP_Param.cpp:1501-1542
// and :2685-2696 without change; there are no parameter overrides from a defaults file.
uint16_t AP_Param::num_param_overrides = 0;
AP_Param::param_override *AP_Param::param_overrides = nullptr;

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

// saves to storage: RAM value already set by the caller; nothing is stored (counted)
void AP_Param::save(bool force_save) { oracle_param_saves++; }

// AP_Param::load (AP_Param.cpp): reached only from AC_PID::load_gains, which the difftest does not
// call (and which the translation leaves out: it has no effect in the model). The oracle's link
// drops it as dead code together with its callers; here it is defined so the driver links.
bool AP_Param::load(void) { return false; }
