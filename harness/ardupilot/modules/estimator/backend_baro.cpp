// backend_baro.cpp: the barometer driver, a stand-in for ArduPilot's SITL barometer driver.
//
// On the SITL board AP_Baro::init creates SIM_BARO_COUNT AP_Baro_SITL drivers (AP_Baro.cpp:628).
// This file defines that class's methods (libraries/AP_Baro/AP_Baro_SITL.h) in place of
// AP_Baro_SITL.cpp, which computes the pressure from the simulator's altitude: here the sample is
// the input record's. The calls on the front end are the SITL driver's:
//   constructor: register_sensor, set_bus_id, register_timer_process
//   timer:       takes a new sample (100 Hz in SITL; here every tick with baro_fresh)
//   update():    _copy_to_frontend(instance, pressure, temperature) when a sample is new
//   healthy:     a sample has been taken
// Differences from the SITL driver: the pressure and temperature are the plant's (1976
// atmosphere at the true altitude), with the plant's noise; no SITL drift, noise, glitch, delay,
// ground effect, wind correction or board-temperature model (SIM_BARO_*, SIM_TEMP_*).
#include <AP_Baro/AP_Baro_SITL.h>
#include <AP_HAL/AP_HAL.h>

#include "harness_cut.h"

extern const AP_HAL::HAL &hal;

AP_Baro_SITL::AP_Baro_SITL(AP_Baro &baro) :
    AP_Baro_Backend(baro),
    _sitl(AP::sitl()),
    _has_sample(false)
{
    if (_sitl != nullptr) {
        _instance = _frontend.register_sensor();
        set_bus_id(_instance, AP_HAL::Device::make_bus_id(AP_HAL::Device::BUS_TYPE_SITL, 0, _instance, DEVTYPE_BARO_SITL));
        hal.scheduler->register_timer_process(FUNCTOR_BIND(this, &AP_Baro_SITL::_timer, void));
    }
}

void AP_Baro_SITL::_timer()
{
    const HarnessTick &t = harness_tick;
    if (!t.baro_fresh) {
        return;
    }
    _last_sample_time = AP_HAL::millis();
    _recent_press = t.baro_pa;
    _recent_temp = t.baro_degc;
    _has_sample = true;
}

bool AP_Baro_SITL::healthy(uint8_t instance)
{
    return _last_sample_time != 0;
}

void AP_Baro_SITL::update(void)
{
    if (!_has_sample) {
        return;
    }

    WITH_SEMAPHORE(_sem);
    _copy_to_frontend(_instance, _recent_press, _recent_temp);
    _has_sample = false;
}
