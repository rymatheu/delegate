// The controllers of the vehicle as one World (cpp2lean --world, PORT-PLAN.md D1): AP_MotorsMatrix,
// AC_AttitudeControl_Multi, AC_PosControl, AC_WPNav, AC_Loiter and AC_Circle with the library code they
// use, and the six objects as ArduCopter's Copter::allocate_motors builds them (system.cpp:387-497: the motors, then
// the attitude controller on the AHRS view and the motors, the position controller on the view, the
// motors and the attitude controller, the navigator on the view, the position and the attitude
// controller). The AHRS view is the boundary (the stub of ardupilot/stubs, set from the input line).
// Each .cpp is included unmodified; check_unity.py checks that each preprocesses here as alone.
#include <AP_Motors/AP_Motors_Thrust_Linearization.cpp>
#include <AP_Motors/AP_Motors_Class.cpp>
#include <AP_Motors/AP_MotorsMulticopter.cpp>
#include <AP_Motors/AP_MotorsMatrix.cpp>
#include <AC_AttitudeControl/AC_AttitudeControl.cpp>
#include <AC_AttitudeControl/AC_AttitudeControl_Multi.cpp>
#include <AC_AttitudeControl/AC_PosControl.cpp>
#include <AC_WPNav/AC_WPNav.cpp>
#include <AC_WPNav/AC_Loiter.cpp>
#include <AC_WPNav/AC_Circle.cpp>
#include <AC_PID/AC_PID.cpp>
#include <AC_PID/AC_P.cpp>
#include <AC_PID/AC_P_1D.cpp>
#include <AC_PID/AC_P_2D.cpp>
#include <AC_PID/AC_PID_Basic.cpp>
#include <AC_PID/AC_PID_2D.cpp>
#include <Filter/SlewLimiter.cpp>
#include <Filter/LowPassFilter.cpp>
#include <Filter/DerivativeFilter.cpp>
#include <AP_Math/AP_Math.cpp>
#include <AP_Math/control.cpp>
#include <AP_Math/vector2.cpp>
#include <AP_Math/vector3.cpp>
#include <AP_Math/matrix3.cpp>
#include <AP_Math/quaternion.cpp>
#include <AP_Math/location.cpp>
#include <AP_Math/SCurve.cpp>
#include <AP_Math/SplineCurve.cpp>

extern AP_AHRS_View cpp2lean_ahrs_view;     // the boundary: defined by the C++ environment

AP_MotorsMatrix motors(400);
AC_AttitudeControl_Multi attitude_control(cpp2lean_ahrs_view, motors);
AC_PosControl pos_control(cpp2lean_ahrs_view, motors, attitude_control);
AC_WPNav wp_nav(cpp2lean_ahrs_view, pos_control, attitude_control);
AC_Loiter loiter_nav(cpp2lean_ahrs_view, pos_control, attitude_control);
AC_Circle circle_nav(cpp2lean_ahrs_view, pos_control);
