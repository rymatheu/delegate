// Unity translation unit for cpp2lean: ArduPilot's AC_AttitudeControl and AC_AttitudeControl_Multi
// and the library sources they call (AC_PID, AC_P, SlewLimiter, LowPassFilter, AP_Math), in one
// translation unit, so clang's AST holds every definition the translation needs. The C++ side of
// the difftest compiles the same sources separately, as the reference build does.
// ardupilot/check_unity.py checks that every translated file preprocesses here exactly as in its
// own translation unit (run by ardupilot/translate_ac_attitude.sh).
#include <AC_AttitudeControl/AC_AttitudeControl.cpp>
#include <AC_AttitudeControl/AC_AttitudeControl_Multi.cpp>
#include <AC_PID/AC_PID.cpp>
#include <AC_PID/AC_P.cpp>
#include <Filter/SlewLimiter.cpp>
#include <Filter/LowPassFilter.cpp>
#include <AP_Math/AP_Math.cpp>
#include <AP_Math/control.cpp>
#include <AP_Math/vector2.cpp>
#include <AP_Math/vector3.cpp>
#include <AP_Math/matrix3.cpp>
#include <AP_Math/quaternion.cpp>
