// The sensor front ends with the reference's sensor stand-ins and the HAL scheduler stand-in as one World
// (README.md "Phase 3: sensor front ends and AP_Param"): the front ends with their back-end bases and
// parameter groups, included unmodified with the flags of their units in the reference build, with the
// library code they call; the stand-in back ends and SITL::SIM of reference/hal/sensors*.cpp (compiled
// into copter_ref in place of the SITL back ends); the scheduler stand-in reference/hal/est_scheduler.cpp,
// whose delays consume input records and run the timer processes (the stand-ins). The objects are those
// ArduCopter holds as members of `copter` (AP_Vehicle: sitl, barometer, ...), here at file scope; `est_uart` is
// the GPS's serial port (reference/hal/est_uart.h: the lock-step HAL's SERIAL3 in the reference vehicle).
#include <AP_Baro/AP_Baro.cpp>
#include <AP_Baro/AP_Baro_Backend.cpp>
#include <AP_Baro/AP_Baro_atmosphere.cpp>
#include <AP_Compass/AP_Compass.cpp>
#define FILTER_KOEF FILTER_KOEF_compass
#include <AP_Compass/AP_Compass_Backend.cpp>
#undef FILTER_KOEF
#include <AP_Compass/Compass_PerMotor.cpp>
#include <AP_InertialSensor/AP_InertialSensor.cpp>
#include <AP_InertialSensor/AP_InertialSensor_Backend.cpp>
#include <AP_InertialSensor/AP_InertialSensor_Params.cpp>
#include <AP_GPS/AP_GPS.cpp>
#include <AP_GPS/GPS_Backend.cpp>
#include <AP_GPS/AP_GPS_Params.cpp>
#include <AP_RTC/AP_RTC.cpp>
#include <AP_RTC/JitterCorrection.cpp>
#include <Filter/LowPassFilter2p.cpp>
#include <AP_Param/AP_ParamT.cpp>
#include <AP_Common/Location.cpp>
#include <AP_Declination/AP_Declination.cpp>
#include <AP_Declination/tables.cpp>
#include <AP_HAL/Device.cpp>
#include <AP_HAL/UARTDriver.cpp>
#include <Filter/DerivativeFilter.cpp>
#include <Filter/LowPassFilter.cpp>
#include <AP_Math/AP_Math.cpp>
#include <AP_Math/vector2.cpp>
#include <AP_Math/vector3.cpp>
#include <AP_Math/matrix3.cpp>
#include <AP_Math/quaternion.cpp>
#include <AP_Math/location.cpp>
#include "sensors.cpp"
#include "sensors_baro.cpp"
#include "sensors_compass.cpp"
#include "sensors_ins.cpp"
#include "sensors_gps.cpp"
#include "est_scheduler.cpp"
#include "est_uart.cpp"

SITL::SIM sitl;
AP_Baro barometer;
Compass compass;
AP_InertialSensor ins;
AP_GPS gps;
AP_RTC rtc;
EstUART est_uart;
