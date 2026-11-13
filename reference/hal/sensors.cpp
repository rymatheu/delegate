/* cpp2lean reference vehicle: the sensor back-end stand-ins and the SITL::SIM stand-in
   (PORT-PLAN.md 3.2, D9). Compiled in place of AP_InertialSensor_SITL.cpp, AP_Baro_SITL.cpp,
   AP_Compass_SITL.cpp, AP_GPS_SITL.cpp and libraries/SITL; the class declarations are ArduPilot's own
   headers. Each back end calls the front-end entry points exactly where its SITL counterpart does, with
   the samples of the current input record (reference/hal/est_input.h: est_input() and the GPS latch,
   which the lock-step HAL lockstep.cpp and the estimator's scheduler stand-in est_scheduler.cpp both
   define) instead of the simulator's state. The same sources are compiled into copter_ref and translated
   with the front ends (README.md "Phase 3: sensor front ends and AP_Param"), one file per sensor:

     sensors.cpp           SITL::SIM, the simulator object, with the constants the back ends read
     sensors_ins.cpp  IMU  a timer process, as SITL's: per step, each of the line's k samples of IMU i
                           (the back end's registration order) through _notify_new_*_sensor_rate_sample,
                           _rotate_and_correct_* and _notify_new_*_raw_sample, time-stamped as a FIFO burst
                           of an IMU at k times the step rate; accel before gyro, as SITL
     sensors_baro.cpp      a timer process latches the line's pressure and temperature; update() copies
                           the latest sample to the front end (AP_Baro_SITL::update)
     sensors_compass.cpp   a timer process accumulates the line's field (AP_Compass_SITL::_timer); read()
                           is the back-end base's drain_accumulated_samples
     sensors_gps.cpp       read() takes the most recent GPS record not yet read and fills `state` as
                           AP_GPS_SITL::read does (the record is latched: AP_GPS::update runs at 50 Hz, a
                           record arrives on one 400 Hz step)
*/

#include <AP_HAL/AP_HAL.h>
#include <SITL/SITL.h>

// ------------------------------------------------------------------------------------------------
// SITL::SIM stand-in

namespace SITL {

SIM *SIM::_singleton = nullptr;

const AP_Param::GroupInfo SIM::var_info[] = {
    AP_GROUPEND
};

SIM::SIM()
{
    if (_singleton != nullptr) {
        AP_HAL::panic("Too many SITL instances");
    }
    _singleton = this;
    // the values of SITL's parameter defaults where they matter (SITL.cpp at 802db19de1)
    imu_count.set(1);
    baro_count.set(1);
    loop_delay.set(0);
    loop_time_jitter_us.set(0);
    on_hardware_relay_enable_mask.set(0);
    wow_pin.set(-1);
    odom_enable.set(0);
    float_exception.set(0);
    telem_baudlimit_enable.set(0);
    mag_save_ids.set(1);
    mag_devid[0].set(97539);           // SIM_MAG1_DEVID; one compass
    for (uint8_t i = 1; i < MAX_CONNECTED_MAGS; i++) {
        mag_devid[i].set(0);
    }
    for (uint8_t i = 0; i < HAL_COMPASS_MAX_SENSORS; i++) {
        mag_ofs[i].set(Vector3f(5, 13, -18));   // SIM::init()
    }
    start_time_UTC = 1767225600;       // 2026-01-01T00:00:00Z (lockstep.cpp START_UTC_S)
    state.is_lock_step_scheduled = true;
    throttle = 0;
}

bool SIM::get_mag_offsets_for_devid(uint32_t devid, Vector3f &offsets) const
{
    if (devid == 0) {
        return false;
    }
    for (uint8_t i = 0; i < ARRAY_SIZE(mag_devid); i++) {
        if (mag_devid[i] == devid && i < ARRAY_SIZE(mag_ofs)) {
            offsets = mag_ofs[i];
            return true;
        }
    }
    return false;
}

}  // namespace SITL

namespace AP {
SITL::SIM *sitl()
{
    return SITL::SIM::get_singleton();
}
}
