// cpp2lean difftest environment for AC_WPNav: the out-of-line library pieces the navigator, SCurve,
// SplineCurve, AP_Math and AP_Common/Location.cpp reference, from ardupilot/stubs/oracle_env.cpp
// (blocks marked "copied" are unchanged), with the clock (AP_HAL::millis) as the driver's input. The
// position and attitude controllers are the stand-ins of ardupilot/standin/AC_AttitudeControl (header
// only); the AHRS is the stub, never read by the member functions under test.

#include "cpp2lean_events.h"
#include <AP_HAL/AP_HAL.h>
#include <AP_Param/AP_Param.h>
#include <AP_AHRS/AP_AHRS.h>
#include <AP_Logger/AP_Logger.h>
#include <AP_InternalError/AP_InternalError.h>
#include <AP_CustomRotations/AP_CustomRotations.h>
#include <stdio.h>
#include <stdlib.h>
#include <stdarg.h>

std::string cpp2lean_events;
uint32_t cpp2lean_millis;           // AP_HAL::millis(): the driver's input `millis`
bool cpp2lean_param_configured;     // AP_Param::configured()
uint32_t oracle_internal_errors;
uint32_t oracle_param_saves;

AP_AHRS oracle_ahrs;
static AP_Logger oracle_logger;
AP_AHRS &AP::ahrs() { return oracle_ahrs; }
AP_Logger &AP::logger() { return oracle_logger; }

namespace AP_HAL {
uint32_t millis() { return cpp2lean_millis; }
uint64_t micros64() { return (uint64_t)cpp2lean_millis * 1000; }
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

// copied: AP_InternalError (counts the reports)
static AP_InternalError oracle_internalerror;
AP_InternalError &AP::internalerror() { return oracle_internalerror; }
void AP_InternalError::error(const AP_InternalError::error_t e, uint16_t line)
{
    oracle_internal_errors++;
}

// copied: AP_CustomRotations (vector3.cpp:264): only for ROTATION_CUSTOM_*, never reached
static AP_CustomRotations *oracle_custom_rotations;
AP_CustomRotations &AP::custom_rotations() { return *oracle_custom_rotations; }
void AP_CustomRotations::rotate(Rotation r, Vector3f &v) { AP_HAL::panic("custom rotation"); }
void AP_CustomRotations::rotate(Rotation r, Vector3d &v) { AP_HAL::panic("custom rotation"); }
void AP_CustomRotations::from_rotation(Rotation r, Quaternion &q) { AP_HAL::panic("custom rotation"); }
void AP_CustomRotations::from_rotation(Rotation r, QuaternionD &q) { AP_HAL::panic("custom rotation"); }

// copied: AP_Param (AP_Param.cpp:1501-1542, :2685-2696): defaults from the real var_info tables; no storage
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

// copied: saves to storage: RAM value already set by the caller; nothing is stored (counted)
void AP_Param::save(bool force_save) { oracle_param_saves++; }
bool AP_Param::configured(void) const { return cpp2lean_param_configured; }
bool AP_Param::load(void) { return false; }
// AC_WPNav::convert_parameters (dropped from the translation, never called): parameter storage
void AP_Param::convert_old_parameters_scaled(const ConversionInfo *conversion_table, uint8_t table_size, float scaler, uint8_t flags) {}
#if AP_PARAM_DEFAULTS_ENABLED
void AP_Param::add_default(AP_Param *ap, float v) {}
#endif
