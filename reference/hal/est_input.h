/* cpp2lean reference vehicle: the input record of one lock-step step as the sensor stand-ins read it
   (reference/hal/sensors.cpp; README.md "Phase 3: sensor front ends and AP_Param").

   Both builds that contain the stand-ins define the accessors below: the reference vehicle's lock-step
   HAL (lockstep.cpp: the line just consumed from stdin) and the estimator's World (est_scheduler.cpp:
   EstScheduler's current record, which the translation runs as code of the World). The stand-ins read
   the step's samples only through them, so the same stand-in source is compiled into copter_ref and
   translated into Lean. */
#pragma once

#include <AP_Math/AP_Math.h>

static const uint8_t EST_MAX_IMUS = 2;
static const uint8_t EST_MAX_IMU_SAMPLES = 8;   // samples per IMU per step (3 in the flights: 1200 Hz)

// one input line (REFERENCE.md "Protocol"): the parts the sensor stand-ins read. Two-dimensional arrays
// are flattened: sample j of IMU i is element i * EST_MAX_IMU_SAMPLES + j.
struct EstRecord {
    uint64_t t_us;
    uint8_t imu_n[EST_MAX_IMUS];                            // samples per IMU this step (0: none)
    Vector3f accel[EST_MAX_IMUS * EST_MAX_IMU_SAMPLES];     // body-frame specific force, m/s/s (FRD)
    Vector3f gyro[EST_MAX_IMUS * EST_MAX_IMU_SAMPLES];      // body rates, rad/s (FRD)
    bool baro;
    float baro_pa;                                          // pressure (Pa)
    float baro_degc;                                        // temperature (deg C)
    bool mag;
    Vector3f mag_mgauss;                                    // body-frame field as the sensor reports it (mGauss)
    bool gps;
    double gps_lat_deg;
    double gps_lon_deg;
    double gps_alt_m;
    double gps_vn;
    double gps_ve;
    double gps_vd;
};

// the record of the step being run (a copy)
EstRecord est_input();
// time between the previous input line and the current one (us; 2500 before the second line)
uint64_t est_step_period_us();
// the sample rate the IMU stand-in registers (copter_ref --imu-rate; 1200)
uint16_t est_imu_rate_hz();
// the GPS latch of the HAL step: the most recent record with a GPS sample that AP_GPS_SITL::read has
// not taken yet (AP_GPS::update runs at 50 Hz, a record arrives on one 400 Hz step)
bool est_gps_pending();
// take the latched record (est_gps_pending() is false afterwards)
EstRecord est_gps_take();

// an event of the stand-ins for the estimation output (copter_ref --est: the `ev=` mask of the step, so that a
// replay of the front ends knows where the vehicle called them; the estimator's World: no effect)
static const uint8_t EST_EV_BARO_INIT = 1;      // AP_Baro_SITL constructed (AP_Baro::init)
static const uint8_t EST_EV_BARO_UPDATE = 2;    // AP_Baro_SITL::update (AP_Baro::update, also inside AP_Baro::calibrate)
static const uint8_t EST_EV_COMPASS_INIT = 4;   // AP_Compass_SITL constructed (Compass::init)
static const uint8_t EST_EV_INS_INIT = 8;       // AP_InertialSensor_SITL constructed (AP_InertialSensor::init)
void est_event(uint8_t ev);
