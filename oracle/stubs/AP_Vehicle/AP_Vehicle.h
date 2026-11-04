// ORACLE STUB: replaces libraries/AP_Vehicle/AP_Vehicle.h, included by AC_AttitudeControl.cpp:3.
// Why: the real header declares the whole vehicle base class (every subsystem, MAVLink). Nothing
// of it is used by AC_AttitudeControl.cpp; only the real AP_Vehicle_Type.h (APM_BUILD_TYPE) is
// needed, which is included unchanged.
#pragma once
#include <AP_Vehicle/AP_Vehicle_Type.h>
