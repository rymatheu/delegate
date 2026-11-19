// Unity translation unit for cpp2lean: ArduPilot's AC_PosControl and the library sources it calls
// (AC_PID, AC_P_1D, AC_P_2D, AC_PID_Basic, AC_PID_2D, SlewLimiter, LowPassFilter, AP_Math), in one
// translation unit, so clang's AST holds every definition the translation needs. The C++ side of
// the difftest compiles the same sources separately, as the reference build does.
// ardupilot/check_unity.py checks that every translated file preprocesses here exactly as in its
// own translation unit (run by ardupilot/translate_ac_poscontrol.sh).
#include <AC_AttitudeControl/AC_PosControl.cpp>
#include <AC_PID/AC_PID.cpp>
#include <AC_PID/AC_P_1D.cpp>
#include <AC_PID/AC_P_2D.cpp>
#include <AC_PID/AC_PID_Basic.cpp>
#include <AC_PID/AC_PID_2D.cpp>
#include <Filter/SlewLimiter.cpp>
#include <Filter/LowPassFilter.cpp>
#include <AP_Math/AP_Math.cpp>
#include <AP_Math/control.cpp>
#include <AP_Math/vector2.cpp>
#include <AP_Math/vector3.cpp>
