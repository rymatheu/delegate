// harness_cut.h: the interface between the adapter and the cut (backend_*.cpp, stubs_*.cpp).
#pragma once

#include <stdint.h>

// --- the samples of one tick, as plant_sim outputs them (sim/modules/plant_sim/Module.lean), which the
// driver stand-ins hand to the front ends (backend_*.cpp)
struct HarnessTick {
    uint32_t t_us;          // the tick's time; IMU sample s was taken at t_us - (2 - s) * 2500 / 3
    float accel[3][3];      // IMU sample s: specific force, sensor frame, m/s^2
    float gyro[3][3];       // IMU sample s: rate, sensor frame, rad/s
    bool baro_fresh;
    float baro_pa, baro_degc;
    bool mag_fresh;
    float mag[3];           // mGauss
    bool gps_fresh;
    int32_t gps_lat_e7, gps_lon_e7;
    float gps_alt, gps_vel[3];
};
extern HarnessTick harness_tick;

// --- HAL (stubs_hal.cpp)
void harness_set_time(uint32_t t_us);                // the clock: micros, millis, micros64
void harness_run_timer_processes();                  // the drivers' registered timers, once
void harness_set_vehicle_state(bool armed, bool likely_flying);
// the boot thread: start it, run it until its next delay or its end (true once it has ended),
// abandon an unfinished one (it never runs again)
void harness_boot_start(void (*boot)());
bool harness_boot_resume();
void harness_boot_abandon();
// a fatal configuration error (AP_BoardConfig::config_error) holds the boot
bool harness_config_error();

// --- the GPS driver (backend_gps.cpp): a fix of this tick arrives on its UART
void harness_gps_receive();

// --- parameter storage (stubs_param.cpp): store a value under its ArduPilot name, as
// AP_Param::load_all does for a value found in storage; aborts on an unknown name
void harness_param_load(const char *name, float value);

// --- the EKF3 object (the static AP_AHRS_NavEKF3::EKF3), for the parameter table
class NavEKF3;
NavEKF3 *harness_ekf3_object();

// --- reset of every piece of the cut's state, at init; the internal-error count
void harness_reset_cut();
uint32_t harness_internal_error_count();
