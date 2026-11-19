// Unity translation unit for cpp2lean: the AHRS view derivation. The declarations of
// ahrs/AP_AHRS_View_decls.h, then AP_AHRS_View::update and AP_AHRS::calc_trig copied unmodified by
// ahrs/extract.py from AP_AHRS_View.cpp:61-83 and AP_AHRS_Backend.cpp:93-135 (at their line numbers),
// then the AP_Math sources they call. The C++ side of the difftest compiles the same files.
#include "ahrs/AP_AHRS_View_decls.h"
#include "ahrs/AP_AHRS_View.cpp"
#include "ahrs/AP_AHRS_Backend.cpp"
#include <AP_Math/AP_Math.cpp>
#include <AP_Math/vector2.cpp>
#include <AP_Math/vector3.cpp>
#include <AP_Math/matrix3.cpp>
#include <AP_Math/quaternion.cpp>
