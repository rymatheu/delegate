// The estimator World with AP_AHRS (README.md "Phase 3: AP_AHRS in the estimator World, the full estimation replay"):
// ardupilot/unity_estimation.cpp's sensor front ends with the reference's stand-ins and the HAL scheduler stand-in,
// AP_DAL, AP_NavEKF and AP_NavEKF3, plus ardupilot/unity_ahrs.cpp's AP_AHRS, AP_AHRS_Backend, the EKF3 backend
// AP_AHRS_NavEKF3 (whose static member `NavEKF3 AP_AHRS_NavEKF3::EKF3` is the EKF3 front end), the DCM fallback
// AP_AHRS_DCM and AP_AHRS_View, all included unmodified with the flags of their units in the reference build (the same
// for all of them). The objects are those ArduCopter holds (members of `copter`: sitl, barometer, compass, ins, gps,
// rtc, ahrs; `EKF3` AP_AHRS_NavEKF3's static member), here at file scope; `est_uart` is the GPS's serial port stand-in.
// AP_DAL's, AP_Baro's and Compass's reads of AP::ahrs() are the World's `ahrs`; the AHRS's reads of AP::ins(),
// AP::baro(), AP::compass(), AP::gps() are the World's front ends. AP_AHRS_SIM (SITL's "true state" backend, used only
// with AHRS_EKF_TYPE 10), the vehicle and the HAL's other drivers are the boundary.
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
#include <AP_AHRS/AP_AHRS.cpp>
#include <AP_AHRS/AP_AHRS_Backend.cpp>
#include <AP_AHRS/AP_AHRS_DCM.cpp>
#include <AP_AHRS/AP_AHRS_NavEKF3.cpp>
#include <AP_AHRS/AP_AHRS_View.cpp>
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
// the vehicle's AHRS (AP_Vehicle.h:419: a member `ahrs` of the vehicle); the EKF3 front end is its EKF3 backend's
// static member (AP_AHRS_NavEKF3.cpp:13)
AP_AHRS ahrs;
