// Unity translation unit for cpp2lean: ArduPilot's AP_Math sources in one translation unit, so
// clang's AST holds every definition the translation needs. The C++ side of the difftest compiles
// the same sources separately, as the reference build does.
#include <AP_Math/AP_Math.cpp>
#include <AP_Math/control.cpp>
#include <AP_Math/vector2.cpp>
#include <AP_Math/vector3.cpp>
#include <AP_Math/matrix3.cpp>
#include <AP_Math/quaternion.cpp>
#include <AP_Math/location.cpp>
// phase 2 (README.md, "Phase 2")
#include <AP_Math/matrix_alg.cpp>
#include <AP_Math/crc.cpp>
#include <AP_Math/location_double.cpp>
#include <AP_Math/div1000.h>

// The one template the AP_Math sources do not instantiate themselves (AC_WPNav.cpp:676 does, at
// float): an explicit instantiation, so that the AST holds its specialization. Nothing else is added.
template float get_horizontal_distance<float>(const Vector2<float> &origin, const Vector2<float> &destination);
