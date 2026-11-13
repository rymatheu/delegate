/* cpp2lean reference vehicle: the IMU back-end stand-in (sensors.cpp). */

#include <AP_HAL/AP_HAL.h>
#include <SITL/SITL.h>
#include <AP_InertialSensor/AP_InertialSensor_SITL.h>

#include "est_input.h"

extern const AP_HAL::HAL& hal;

// ------------------------------------------------------------------------------------------------
// IMU

uint8_t AP_InertialSensor_SITL::bus_id = 0;

AP_InertialSensor_SITL::AP_InertialSensor_SITL(AP_InertialSensor &imu, const uint16_t sample_rates[]) :
    AP_InertialSensor_Backend(imu),
    gyro_sample_hz(est_imu_rate_hz()),
    accel_sample_hz(est_imu_rate_hz())
{
    est_event(EST_EV_INS_INIT);
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

// SITL's temperature model is simulation; the stand-in reports a constant
float AP_InertialSensor_SITL::get_temperature(void)
{
    return 20.0f;
}

void AP_InertialSensor_SITL::timer_update(void)
{
    const uint8_t idx = gyro_instance;
    if (idx >= EST_MAX_IMUS) {
        return;
    }
    const EstRecord in = est_input();
    const uint8_t n = in.imu_n[idx];
    if (n == 0) {
        return;
    }
    const uint16_t base = uint16_t(idx) * EST_MAX_IMU_SAMPLES;
    // the line's n samples are equally spaced over the step that ends now, the last one now: a FIFO
    // read of an IMU sampling at n times the step rate (D6: n = 3, 1200 Hz with 400 Hz steps)
    const uint64_t now = AP_HAL::micros64();
    const uint64_t period = est_step_period_us();

    // generate_accel(): each sample through the front end's entry points, accel before gyro as SITL
    for (uint8_t j = 0; j < n; j++) {
        const uint64_t sample_us = now - (period * uint64_t(n - 1 - j)) / n;
        Vector3f accel = in.accel[base + j];
        _notify_new_accel_sensor_rate_sample(accel_instance, accel);
        _rotate_and_correct_accel(accel_instance, accel);
        _notify_new_accel_raw_sample(accel_instance, accel, sample_us);
    }
    _publish_temperature(accel_instance, get_temperature());

    // generate_gyro()
    for (uint8_t j = 0; j < n; j++) {
        const uint64_t sample_us = now - (period * uint64_t(n - 1 - j)) / n;
        Vector3f gyro = in.gyro[base + j];
        _notify_new_gyro_sensor_rate_sample(gyro_instance, gyro);
        _rotate_and_correct_gyro(gyro_instance, gyro);
        _notify_new_gyro_raw_sample(gyro_instance, gyro, sample_us);
    }
}

bool AP_InertialSensor_SITL::update(void)
{
    update_accel(accel_instance);
    update_gyro(gyro_instance);
    return true;
}
