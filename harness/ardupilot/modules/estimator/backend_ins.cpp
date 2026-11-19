// backend_ins.cpp: the IMU driver, a stand-in for ArduPilot's SITL IMU driver.
//
// On the SITL board AP_InertialSensor::detect_backends creates SIM_IMU_COUNT drivers with
// AP_InertialSensor_SITL::detect (AP_InertialSensor.cpp:1224). This file defines that class's
// methods (declared in libraries/AP_InertialSensor/AP_InertialSensor_SITL.h) in place of
// AP_InertialSensor_SITL.cpp, which generates samples from the simulator's state: here the
// samples are the input record's. The calls on the front end are the SITL driver's, in its order:
//   start():        register_gyro, register_accel (instance, rate, bus id), register_timer_process
//   timer (per sample): _notify_new_accel_sensor_rate_sample, _rotate_and_correct_accel,
//                   _notify_new_accel_raw_sample(instance, accel, sample time),
//                   _publish_temperature; then the same for the gyro
//   update():       update_accel, update_gyro (publish the accumulated samples to the front end)
// Differences from the SITL driver, all because the samples come from the plant:
//   * rate 1200 Hz (the plant's three physics substeps per 400 Hz tick), not SITL's 1000 Hz;
//     sample s of the tick is stamped t_us - (2 - s) * 2500 / 3 us, rounded to the microsecond;
//   * the samples are the plant's, unchanged: no SITL noise, bias, scale, vibration or
//     orientation (SIM_ACC_*, SIM_GYR_*, SIM_IMU_ORIENT, SIM_VIB_*: the plant has its own model);
//   * temperature: 25 degC, constant (SIM_IMU_TEMP_START's default; SITL lets it drift towards
//     SIM_IMU_TEMP_END). Only the temperature calibration reads it, and INS_TCAL1_ENABLE is 0.
#include <AP_InertialSensor/AP_InertialSensor_SITL.h>
#include <AP_HAL/AP_HAL.h>

#include "harness_cut.h"

extern const AP_HAL::HAL &hal;

static const uint16_t PLANT_IMU_HZ = 1200;
static const float IMU_TEMPERATURE_DEGC = 25.0f;

uint8_t AP_InertialSensor_SITL::bus_id = 0;

AP_InertialSensor_SITL::AP_InertialSensor_SITL(AP_InertialSensor &imu, const uint16_t sample_rates[]) :
    AP_InertialSensor_Backend(imu),
    gyro_sample_hz(PLANT_IMU_HZ),
    accel_sample_hz(PLANT_IMU_HZ)
{
}

AP_InertialSensor_Backend *AP_InertialSensor_SITL::detect(AP_InertialSensor &_imu, const uint16_t sample_rates[])
{
    AP_InertialSensor_SITL *sensor = NEW_NOTHROW AP_InertialSensor_SITL(_imu, sample_rates);
    if (sensor == nullptr) {
        return nullptr;
    }
    if (!sensor->init_sensor()) {
        delete sensor;
        return nullptr;
    }
    return sensor;
}

bool AP_InertialSensor_SITL::init_sensor(void)
{
    sitl = AP::sitl();
    return sitl != nullptr;
}

void AP_InertialSensor_SITL::start()
{
    if (!_imu.register_gyro(gyro_instance, gyro_sample_hz,
                            AP_HAL::Device::make_bus_id(AP_HAL::Device::BUS_TYPE_SITL, bus_id, 1, DEVTYPE_SITL)) ||
        !_imu.register_accel(accel_instance, accel_sample_hz,
                             AP_HAL::Device::make_bus_id(AP_HAL::Device::BUS_TYPE_SITL, bus_id, 2, DEVTYPE_SITL))) {
        return;
    }
    bus_id++;
    hal.scheduler->register_timer_process(FUNCTOR_BIND_MEMBER(&AP_InertialSensor_SITL::timer_update, void));
}

bool AP_InertialSensor_SITL::update(void)
{
    update_accel(accel_instance);
    update_gyro(gyro_instance);
    return true;
}

// the driver's timer: hand the tick's three samples to the front end, oldest first
void AP_InertialSensor_SITL::timer_update(void)
{
    const HarnessTick &t = harness_tick;
    for (uint8_t s = 0; s < 3; s++) {
        const uint64_t sample_us = AP_HAL::micros64() - ((2 - s) * 2500U + 1U) / 3U;
        Vector3f accel(t.accel[s][0], t.accel[s][1], t.accel[s][2]);
        _notify_new_accel_sensor_rate_sample(accel_instance, accel);
        _rotate_and_correct_accel(accel_instance, accel);
        _notify_new_accel_raw_sample(accel_instance, accel, sample_us);
        _publish_temperature(accel_instance, IMU_TEMPERATURE_DEGC);

        Vector3f gyro(t.gyro[s][0], t.gyro[s][1], t.gyro[s][2]);
        _notify_new_gyro_sensor_rate_sample(gyro_instance, gyro);
        _rotate_and_correct_gyro(gyro_instance, gyro);
        _notify_new_gyro_raw_sample(gyro_instance, gyro, sample_us);
    }
}

// the driver's bus counter (a private static) starts at 0 in every case, as in a fresh process
static uint8_t *ins_bus_id();
template <uint8_t *P> struct InsBusId {
    friend uint8_t *ins_bus_id() { return P; }
};
template struct InsBusId<&AP_InertialSensor_SITL::bus_id>;

void harness_reset_ins_driver()
{
    *ins_bus_id() = 0;
}
