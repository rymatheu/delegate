// cpp2lean difftest environment for the AHRS view (ardupilot/AHRS_View.json): the AHRS estimate the
// view reads (the driver's inputs) and the out-of-line pieces AP_Math references, from
// ardupilot/stubs/oracle_env.cpp. AP_AHRS_View::update and AP_AHRS::calc_trig themselves are the
// copies of ardupilot/ahrs, compiled in ardupilot/unity_ahrs_view.cpp.
#include "ahrs/AP_AHRS_View_decls.h"
#include <AP_InternalError/AP_InternalError.h>
#include <AP_CustomRotations/AP_CustomRotations.h>
#include <stdio.h>
#include <stdlib.h>
#include <stdarg.h>

Matrix3f ahrs_rot;      // the driver's inputs: the estimate's rotation matrix and gyro
Vector3f ahrs_gyro;
uint32_t oracle_internal_errors;

const Matrix3f &AP_AHRS::get_rotation_body_to_ned(void) const { return ahrs_rot; }
const Vector3f &AP_AHRS::get_gyro(void) const { return ahrs_gyro; }

namespace AP_HAL {
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
uint32_t millis() { return 0; }
}

// copied: AP_InternalError (counts the reports)
static AP_InternalError oracle_internalerror;
AP_InternalError &AP::internalerror() { return oracle_internalerror; }
void AP_InternalError::error(const AP_InternalError::error_t e, uint16_t line)
{
    oracle_internal_errors++;
}

// copied: AP_CustomRotations (vector3.cpp:264, quaternion.cpp:386): only for ROTATION_CUSTOM_*, never reached
static AP_CustomRotations *oracle_custom_rotations;
AP_CustomRotations &AP::custom_rotations() { return *oracle_custom_rotations; }
void AP_CustomRotations::rotate(Rotation r, Vector3f &v) { AP_HAL::panic("custom rotation"); }
void AP_CustomRotations::rotate(Rotation r, Vector3d &v) { AP_HAL::panic("custom rotation"); }
void AP_CustomRotations::from_rotation(Rotation r, Quaternion &q) { AP_HAL::panic("custom rotation"); }
void AP_CustomRotations::from_rotation(Rotation r, QuaternionD &q) { AP_HAL::panic("custom rotation"); }
