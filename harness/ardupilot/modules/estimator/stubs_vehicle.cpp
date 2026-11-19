// stubs_vehicle.cpp: the rest of the vehicle the estimation chain reaches for, and what stands in.
//
//   symbol                                   why it is outside the module, and what stands in
//   AP::sitl() (SITL::SIM)                   the simulator's parameter object, which the SITL
//                                            board's code consults. Zeroed storage with the fields
//                                            the estimator's front ends read: SIM_IMU_COUNT 1 and
//                                            SIM_BARO_COUNT 1 (the plant's one IMU and one
//                                            barometer; SITL's defaults are 2 and 2),
//                                            SIM_TIME_JITTER 0 (read by AP_AHRS::update). Its
//                                            presence makes AP_InertialSensor::wait_for_sample
//                                            take its normal path (AP_InertialSensor.cpp:2028).
//   AP::vehicle() (AP_Vehicle)               the vehicle: AP_DAL reads get_time_flying_ms(), which
//                                            reads likely_flying and the time it was set. Zeroed
//                                            storage; the input port likely_flying goes through
//                                            the real inline AP_Vehicle::set_likely_flying.
//   AP_InternalError::error,                 the internal-error reporter, as in rate_pid: keeps the
//   AP::internalerror()                      bit, count and line; skips the HAL's persistent data.
//                                            The count is the output port est_internal_errors.
//   AP_Notify::flags, events                 the notification library (LEDs, buzzer): written by
//                                            the AHRS, the INS and EKF3, read by nothing here.
//                                            Storage only.
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <new>

#include <AP_HAL/AP_HAL.h>
#include <AP_InternalError/AP_InternalError.h>
#include <AP_Notify/AP_Notify.h>
#include <AP_Vehicle/AP_Vehicle.h>
#include <SITL/SITL.h>

#include "harness_cut.h"

// --- the simulator's parameter object
alignas(SITL::SIM) static unsigned char sitl_storage[sizeof(SITL::SIM)];

SITL::SIM *AP::sitl()
{
    return reinterpret_cast<SITL::SIM *>(sitl_storage);
}

static void reset_sitl()
{
    memset(sitl_storage, 0, sizeof sitl_storage);
    SITL::SIM *s = AP::sitl();
    s->imu_count.set(1);
    s->baro_count.set(1);
    s->loop_time_jitter_us.set(0);
}

// --- the vehicle
alignas(AP_Vehicle) static unsigned char vehicle_storage[sizeof(AP_Vehicle)];

AP_Vehicle *AP::vehicle()
{
    return reinterpret_cast<AP_Vehicle *>(vehicle_storage);
}

void harness_set_vehicle_state_hal(bool armed);

void harness_set_vehicle_state(bool armed, bool likely_flying)
{
    harness_set_vehicle_state_hal(armed);
    AP::vehicle()->set_likely_flying(likely_flying);
}

// --- internal-error reporter
alignas(AP_InternalError) static unsigned char internal_error_storage[sizeof(AP_InternalError)];

void AP_InternalError::error(const AP_InternalError::error_t e, uint16_t line)
{
    internal_errors |= uint32_t(e);
    total_error_count++;
    last_line = line;
}

AP_InternalError &AP::internalerror()
{
    return *reinterpret_cast<AP_InternalError *>(internal_error_storage);
}

uint32_t harness_internal_error_count()
{
    return AP::internalerror().count();
}

// --- notification
struct AP_Notify::notify_flags_and_values_type AP_Notify::flags;
struct AP_Notify::notify_events_type AP_Notify::events;

// --- reset of the whole cut, at every init
void harness_reset_hal();
void harness_reset_params();
void harness_reset_ins_driver();
void harness_reset_gps_driver();

void harness_reset_cut()
{
    harness_reset_hal();
    harness_reset_params();
    harness_reset_ins_driver();
    harness_reset_gps_driver();
    reset_sitl();
    memset(vehicle_storage, 0, sizeof vehicle_storage);
    memset(internal_error_storage, 0, sizeof internal_error_storage);
    new (internal_error_storage) AP_InternalError();
    memset(&AP_Notify::flags, 0, sizeof AP_Notify::flags);
    memset(&AP_Notify::events, 0, sizeof AP_Notify::events);
    memset(&harness_tick, 0, sizeof harness_tick);
}
