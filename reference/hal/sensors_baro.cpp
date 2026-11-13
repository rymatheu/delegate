/* cpp2lean reference vehicle: the barometer back-end stand-in (sensors.cpp). */

#include <AP_HAL/AP_HAL.h>
#include <SITL/SITL.h>
#include <AP_Baro/AP_Baro_SITL.h>

#include "est_input.h"

extern const AP_HAL::HAL& hal;

// ------------------------------------------------------------------------------------------------
// barometer

AP_Baro_SITL::AP_Baro_SITL(AP_Baro &baro) :
    AP_Baro_Backend(baro),
    _sitl(AP::sitl()),
    _has_sample(false)
{
    est_event(EST_EV_BARO_INIT);
    if (_sitl != nullptr) {
        _instance = _frontend.register_sensor();
        set_bus_id(_instance, AP_HAL::Device::make_bus_id(AP_HAL::Device::BUS_TYPE_SITL, 0, _instance, DEVTYPE_BARO_SITL));
        hal.scheduler->register_timer_process(FUNCTOR_BIND(this, &AP_Baro_SITL::_timer, void));
    }
}

void AP_Baro_SITL::_timer()
{
    const EstRecord in = est_input();
    if (!in.baro || _instance != 0) {
        return;
    }
    WITH_SEMAPHORE(_sem);
    _recent_press = in.baro_pa;
    _recent_temp = in.baro_degc;
    _last_sample_time = AP_HAL::millis();
    _has_sample = true;
}

bool AP_Baro_SITL::healthy(uint8_t instance)
{
    return true;
}

void AP_Baro_SITL::update(void)
{
    est_event(EST_EV_BARO_UPDATE);
    if (!_has_sample) {
        return;
    }
    WITH_SEMAPHORE(_sem);
    _copy_to_frontend(_instance, _recent_press, _recent_temp);
    _has_sample = false;
}
