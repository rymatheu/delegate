// Unity translation unit for cpp2lean: the ArduPilot sources of the AC_PID family and what they
// call, in one translation unit, so clang's AST holds every definition the translation needs
// (the out-of-line members of SlewLimiter and Vector2, the LowPassFilter template instantiations,
// AP_Math). The C++ side of the difftest compiles the same sources separately, as
// the reference build does.
#include <AC_PID/AC_PID.cpp>
#include <AC_PID/AC_P.cpp>
#include <AC_PID/AC_P_1D.cpp>
#include <AC_PID/AC_PID_Basic.cpp>
#include <AC_PID/AC_PID_2D.cpp>
#include <AC_PID/AC_P_2D.cpp>
#include <Filter/SlewLimiter.cpp>
#include <Filter/LowPassFilter.cpp>
#include <AP_Math/AP_Math.cpp>
#include <AP_Math/control.cpp>
#include <AP_Math/vector2.cpp>
