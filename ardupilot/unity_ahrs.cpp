// AP_AHRS with its backends (README.md, "Phase 3: AP_AHRS, and speed"): AP_AHRS, AP_AHRS_Backend, the
// EKF3 backend AP_AHRS_NavEKF3 (whose static member `NavEKF3 AP_AHRS_NavEKF3::EKF3` is the front end of
// ardupilot/unity_ekf3.cpp), the DCM fallback AP_AHRS_DCM and AP_AHRS_View (create_view), on top of AP_DAL,
// AP_NavEKF and AP_NavEKF3 as in unity_ekf3.cpp, included unmodified with the flags of AP_NavEKF3_core.cpp's
// unit in the reference build. AP_AHRS_SIM (AP_AHRS_SIM.cpp, SITL's "true state" backend, used only with
// AHRS_EKF_TYPE 10) is the boundary: its out-of-line member functions are not included.
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
// the library code they call that is defined out of line: AP_Math (as in its own translation) and
// AP_Common's Location
#include <AP_Math/AP_Math.cpp>
#include <AP_Math/vector2.cpp>
#include <AP_Math/vector3.cpp>
#include <AP_Math/matrix3.cpp>
#include <AP_Math/quaternion.cpp>
#include <AP_Math/location.cpp>
#include <AP_Math/control.cpp>
#include <AP_Common/Location.cpp>
// AP_Declination's tables (NavEKF3_core::getEarthFieldTable, AP_NavEKF3_Measurements.cpp:1547)
#include <AP_Declination/AP_Declination.cpp>
#include <AP_Declination/tables.cpp>

// the vehicle's AHRS (AP_Vehicle.h:419: a member `ahrs` of the vehicle; here a file-scope object)
AP_AHRS ahrs;
