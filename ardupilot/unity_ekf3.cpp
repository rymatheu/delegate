// AP_DAL, AP_NavEKF (buffers, source selection, EKFGSF_yaw, the cores' common part) and AP_NavEKF3, included
// unmodified, with the flags of AP_NavEKF3_core.cpp's unit in the reference build (README.md, "Phase 3:
// AP_DAL and NavEKF3"). The objects as the vehicle has them: the NavEKF3 front end (in the vehicle the
// member `EKF3` of `AP_AHRS_NavEKF3` inside `AP_AHRS`; here a file-scope object), AP_DAL the heap
// singleton that `AP_DAL::get_singleton()` allocates on first use, the cores in the memory of
// `AP_DAL::malloc_type` (placement new, AP_NavEKF3.cpp:850-860), each core's EKFGSF_yaw allocated by
// `setup_core` (AP_NavEKF3_core.cpp:182). The sensor front ends, AP_AHRS, the vehicle and the HAL are
// the boundary. Compiled out entirely in the reference configuration (not included):
// AP_NavEKF/EKFGSF_Logging.cpp, AP_NavEKF3/AP_NavEKF3_Logging.cpp, AP_NavEKF3/AP_NavEKF3_OptFlowFusion.cpp,
// AP_NavEKF3/AP_NavEKF3_RngBcnFusion.cpp, AP_DAL/AP_DAL_Beacon.cpp, AP_DAL/AP_DAL_RangeFinder.cpp,
// AP_DAL/AP_DAL_VisualOdom.cpp.
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
// AP_Declination's tables (NavEKF3_core::getEarthFieldTable, AP_NavEKF3_Measurements.cpp:1547)
#include <AP_Declination/AP_Declination.cpp>
#include <AP_Declination/tables.cpp>

// the front end, as AP_AHRS_NavEKF3 holds it
NavEKF3 EKF3;
