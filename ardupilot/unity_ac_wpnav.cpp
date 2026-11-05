// Unity translation unit for cpp2lean: ArduPilot's AC_WPNav and the library sources it calls
// (SCurve, SplineCurve, the shaping functions of control.cpp, AP_Math), in one translation unit, so
// clang's AST holds every definition the translation needs. AC_PosControl and AC_AttitudeControl are
// the boundary: only their headers are seen. The C++ side of the difftest compiles the same sources
// separately, as the reference build does. ardupilot/check_unity.py checks that every translated
// file preprocesses here exactly as in its own translation unit (run by translate_ac_wpnav.sh).
#include <AC_WPNav/AC_WPNav.cpp>
#include <AP_Math/SCurve.cpp>
#include <AP_Math/SplineCurve.cpp>
#include <AP_Math/AP_Math.cpp>
#include <AP_Math/control.cpp>
#include <AP_Math/vector2.cpp>
#include <AP_Math/vector3.cpp>
#include <AP_Math/location.cpp>
