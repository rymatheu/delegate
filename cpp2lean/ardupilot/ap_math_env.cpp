// cpp2lean difftest environment for AP_Math: the out-of-line pieces the AP_Math sources reference,
// taken from ardupilot/stubs/oracle_env.cpp (blocks copied without change where marked).

#include <AP_HAL/AP_HAL.h>
#include <AP_Math/AP_Math.h>
#include <AP_InternalError/AP_InternalError.h>
#include <AP_CustomRotations/AP_CustomRotations.h>
#include <stdio.h>
#include <stdlib.h>
#include <stdarg.h>

uint32_t oracle_internal_errors;

namespace AP_HAL {
uint32_t millis() { return 0; }
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

// ---- copied from ardupilot/stubs/oracle_env.cpp: AP_CustomRotations (vector3.cpp:264, quaternion.cpp:386):
// only for ROTATION_CUSTOM_*, never reached by the functions under test
static AP_CustomRotations *oracle_custom_rotations;
AP_CustomRotations &AP::custom_rotations() { return *oracle_custom_rotations; }
void AP_CustomRotations::rotate(Rotation r, Vector3f &v) { AP_HAL::panic("custom rotation"); }
void AP_CustomRotations::rotate(Rotation r, Vector3d &v) { AP_HAL::panic("custom rotation"); }
void AP_CustomRotations::from_rotation(Rotation r, Quaternion &q) { AP_HAL::panic("custom rotation"); }
void AP_CustomRotations::from_rotation(Rotation r, QuaternionD &q) { AP_HAL::panic("custom rotation"); }
