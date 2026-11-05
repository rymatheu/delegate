// Unity translation unit for cpp2lean: ArduPilot's AP_Motors classes (AP_Motors, AP_MotorsMulticopter,
// AP_MotorsMatrix, Thrust_Linearization) and the library sources they call, in one translation unit,
// so clang's AST holds every definition the translation needs. The C++ side of the difftest compiles
// the same sources separately, as the reference build does.
//
// The order matters: macros that one file's headers define stay defined for the files after it.
// AP_Motors_Thrust_Linearization.cpp comes first because in its own translation unit
// AP_BATTERY_ENABLED is not defined (ardupilot/stubs/AP_BattMonitor/AP_BattMonitor.h does not include
// AP_BattMonitor_config.h), while SRV_Channel.h, which the other AP_Motors files include, defines it.
// ardupilot/check_unity.py checks that every translated file preprocesses here exactly as in its
// own translation unit (run by ardupilot/translate_ap_motors.sh).
#include <AP_Motors/AP_Motors_Thrust_Linearization.cpp>
#include <AP_Motors/AP_Motors_Class.cpp>
#include <AP_Motors/AP_MotorsMulticopter.cpp>
#include <AP_Motors/AP_MotorsMatrix.cpp>
#include <Filter/LowPassFilter.cpp>
#include <Filter/DerivativeFilter.cpp>
#include <AP_Math/AP_Math.cpp>
