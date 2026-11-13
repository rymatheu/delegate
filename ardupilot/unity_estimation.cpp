// The estimator as one World (README.md "Phase 3: the estimator World and the EKF3 replay"): the sensor front ends
// with the reference's stand-ins and the HAL scheduler stand-in (ardupilot/unity_sensors.cpp) and AP_DAL, AP_NavEKF
// (buffers, AP_NavEKF_Source, EKFGSF_yaw, the cores' common part) and AP_NavEKF3 (ardupilot/unity_ekf3.cpp), included
// unmodified with the flags of their units in the reference build (the same for all of them). AP_DAL's start_frame
// reads the front ends through AP::ins(), AP::baro(), AP::compass(), AP::gps(): here the World's objects, not inputs;
// NavEKF3's member `sources` (AP_NavEKF_Source) is translated with its parameters. The objects are those ArduCopter
// holds (members of `copter`: sitl, barometer, compass, ins, gps, rtc; `EKF3` the static member of AP_AHRS_NavEKF3),
// here at file scope; `est_uart` is the GPS's serial port stand-in. AP_AHRS, the vehicle and the HAL's other drivers
// are the boundary.
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
#include <AP_HAL/Device.cpp>
#include <AP_HAL/UARTDriver.cpp>
#include <Filter/DerivativeFilter.cpp>
#include <Filter/LowPassFilter.cpp>
// EKF_Buffer.h has no include guard: `#import` keeps it to one copy (see unity_ekf_buffer.cpp).
#import <AP_NavEKF/EKF_Buffer.h>
#include <AP_NavEKF/EKF_Buffer.cpp>
#include <AP_NavEKF/EKFGSF_yaw.cpp>
#include <AP_NavEKF/AP_NavEKF_Source.cpp>
#include <AP_NavEKF/AP_NavEKF_core_common.cpp>
#include <AP_NavEKF3/AP_NavEKF3.cpp>
#include <AP_NavEKF3/AP_NavEKF3_AirDataFusion.cpp>
#include <AP_NavEKF3/AP_NavEKF3_Control.cpp>
#include <AP_NavEKF3/AP_NavEKF3_GyroBias.cpp>
#include <AP_NavEKF3/AP_NavEKF3_MagFusion.cpp>
#include <AP_NavEKF3/AP_NavEKF3_Measurements.cpp>
#include <AP_NavEKF3/AP_NavEKF3_Outputs.cpp>
#include <AP_NavEKF3/AP_NavEKF3_PosVelFusion.cpp>
#include <AP_NavEKF3/AP_NavEKF3_VehicleStatus.cpp>
#include <AP_NavEKF3/AP_NavEKF3_core.cpp>
#include <AP_DAL/AP_DAL.cpp>
#include <AP_DAL/AP_DAL_Airspeed.cpp>
#include <AP_DAL/AP_DAL_Baro.cpp>
#include <AP_DAL/AP_DAL_Compass.cpp>
#include <AP_DAL/AP_DAL_GPS.cpp>
#include <AP_DAL/AP_DAL_InertialSensor.cpp>
#include <AP_Common/Location.cpp>
#include <AP_Declination/AP_Declination.cpp>
#include <AP_Declination/tables.cpp>
#include <AP_Math/AP_Math.cpp>
#include <AP_Math/vector2.cpp>
#include <AP_Math/vector3.cpp>
#include <AP_Math/matrix3.cpp>
#include <AP_Math/quaternion.cpp>
#include <AP_Math/location.cpp>
#include <AP_Math/control.cpp>
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
// the EKF3 front end, as AP_AHRS_NavEKF3 holds it (its static member EKF3, AP_AHRS_NavEKF3.cpp:13)
NavEKF3 EKF3;
