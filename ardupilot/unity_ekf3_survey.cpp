// Survey of what the translator still rejects in the estimation pipeline (README.md, "Phase 3: EKF
// data structures"; PORT-PLAN.md section 6, Phase 3): every source of AP_NavEKF3, AP_NavEKF and AP_DAL
// in the reference build, included unmodified (`cpp2lean --keep-going`: the output is not used).
// Compiled out entirely in the reference configuration (no line survives preprocessing), so not
// included: AP_NavEKF/EKFGSF_Logging.cpp, AP_NavEKF3/AP_NavEKF3_Logging.cpp, AP_NavEKF3/AP_NavEKF3_OptFlowFusion.cpp, AP_NavEKF3/AP_NavEKF3_RngBcnFusion.cpp, AP_DAL/AP_DAL_Beacon.cpp, AP_DAL/AP_DAL_RangeFinder.cpp, AP_DAL/AP_DAL_VisualOdom.cpp.
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
