// stubs_ahrs.cpp: the estimator (AP_AHRS's active estimates).
//
// The estimator is its own stage. AC_Loiter reads from it the yaw of the AHRS view (`_ahrs.yaw`,
// AC_Loiter.cpp:179, 197: a public member of the view, loaded by the adapter from est_yaw) and the
// estimator's control ground-speed limit through the AHRS singleton
// (AP::ahrs().get_control_ground_speed_limit_ms(), AC_Loiter.cpp:324; inline,
// active_estimates->control_ground_speed_limit_ms, AP_AHRS.h:322).
//
//   symbol                   why it is outside the stage, and what stands in
//   AP::ahrs()               the AHRS singleton. Zeroed storage (never constructed: its members
//                            include every estimator backend).
//   AP_AHRS::update(bool)    the estimator's update (AP_AHRS.cpp), called by the adapter once
//                            per step. Stand-in: points active_estimates at one Estimates record
//                            whose control_ground_speed_limit_ms is the input est_gnd_spd_limit
//                            (the estimator stage's AP_AHRS::get_control_ground_speed_limit_ms()
//                            of this tick).
#include <string.h>

#include <AP_AHRS/AP_AHRS.h>
#include "cut.h"

alignas(AP_AHRS) static unsigned char ahrs_storage[sizeof(AP_AHRS)];
alignas(AP_AHRS_Backend::Estimates) static unsigned char
    estimates_storage[sizeof(AP_AHRS_Backend::Estimates)];
float harness_gnd_spd_limit;

AP_AHRS &AP::ahrs()
{
    return *reinterpret_cast<AP_AHRS *>(ahrs_storage);
}

void AP_AHRS::update(bool skip_ins_update)
{
    AP_AHRS_Backend::Estimates &e = *reinterpret_cast<AP_AHRS_Backend::Estimates *>(estimates_storage);
    e.control_ground_speed_limit_ms = harness_gnd_spd_limit;
    active_estimates = &e;
}

static void harness_reset_ahrs()
{
    memset(ahrs_storage, 0, sizeof ahrs_storage);
    memset(estimates_storage, 0, sizeof estimates_storage);
}
