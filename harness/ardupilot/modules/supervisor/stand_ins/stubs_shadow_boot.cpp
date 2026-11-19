// stubs_shadow_boot.cpp: the pieces of the other stages' libraries that constructing the shadows
// needs and that the generator (gen/gen_shadows.py) does not write: singleton accessors and
// constructors of nested classes. Each body is the real one, cited, unless said otherwise.
//
//   AP::ahrs, AP::ins, AP::gps, AP::baro,   the singletons the shadows' constructors register
//   AP::compass                             (AP_AHRS.cpp, AP_InertialSensor.cpp, AP_GPS.cpp,
//                                           AP_Baro.cpp, AP_Compass.cpp: same bodies)
//   (AP_GPS::Params and Compass_PerMotor: real constructors and tables, gen/ shadows)
//   Compass_PerMotor::calibration_*         compass/motor calibration (MAV_CMD_PREFLIGHT_
//                                           CALIBRATION with compassmot): not covered, aborts
//   AP::dal                                 the estimator's data abstraction layer, which the
//                                           NavEKF3 shadow's constructor binds a reference to:
//                                           zeroed storage, never used (every NavEKF3 method is
//                                           a stand-in)
//   AP_Motors::AP_Motors_limit::set_all     AP_Motors_Class.cpp:357-361 (and set_rpy,
//                                           set_throttle that it calls, 365-379)
#include <new>
#include <AP_AHRS/AP_AHRS.h>
#include <AP_InertialSensor/AP_InertialSensor.h>
#include <AP_GPS/AP_GPS.h>
#include <AP_Baro/AP_Baro.h>
#include <AP_Compass/AP_Compass.h>
#include <AP_DAL/AP_DAL.h>
#include <AP_Motors/AP_Motors_Class.h>
#include "supervisor_shadow.h"

namespace AP {
AP_AHRS &ahrs() { return *AP_AHRS::get_singleton(); }
AP_InertialSensor &ins() { return *AP_InertialSensor::get_singleton(); }
AP_GPS &gps() { return *AP_GPS::get_singleton(); }
AP_Baro &baro() { return *AP_Baro::get_singleton(); }
Compass &compass() { return *Compass::get_singleton(); }
alignas(AP_DAL) static unsigned char dal_storage[sizeof(AP_DAL)];
AP_DAL &dal() { return *reinterpret_cast<AP_DAL *>(dal_storage); }
}


void Compass_PerMotor::calibration_start() { sup_unanswered("Compass_PerMotor::calibration_start"); }
void Compass_PerMotor::calibration_update() { sup_unanswered("Compass_PerMotor::calibration_update"); }
void Compass_PerMotor::calibration_end() { sup_unanswered("Compass_PerMotor::calibration_end"); }

void AP_Motors::AP_Motors_limit::set_all(bool flag)
{
    roll = flag;
    pitch = flag;
    yaw = flag;
    throttle_lower = flag;
    throttle_upper = flag;
}

// AP::motors(): AP_Motors_Class.cpp, same body (the singleton the motors shadow's constructor
// registers)
namespace AP {
AP_Motors *motors() { return AP_Motors::get_singleton(); }
}
