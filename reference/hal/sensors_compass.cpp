/* cpp2lean reference vehicle: the compass back-end stand-in (sensors.cpp). */

#include <AP_HAL/AP_HAL.h>
#include <SITL/SITL.h>
#include <AP_Compass/AP_Compass_SITL.h>

#include "est_input.h"

extern const AP_HAL::HAL& hal;

// ------------------------------------------------------------------------------------------------
// compass

AP_Compass_SITL::AP_Compass_SITL(uint8_t _sitl_instance) :
    _sitl(AP::sitl()),
    sitl_instance(_sitl_instance)
{
    est_event(EST_EV_COMPASS_INIT);
    if (sitl_instance > ARRAY_SIZE(_sitl->mag_devid)) {
        return;
    }
    const uint32_t dev_id = _sitl->mag_devid[sitl_instance];
    if (dev_id == 0) {
        return;
    }
    if (!register_compass(dev_id)) {
        return;
    }
    if (_sitl->mag_save_ids) {
        save_dev_id();
    }
    set_rotation(ROTATION_NONE);
    if (_compass.get_offsets(instance).is_zero()) {
        _compass.set_offsets(instance, _sitl->mag_ofs[sitl_instance]);
    }
    AP_Param::set_default_by_name("COMPASS_SCALE", 1);
    AP_Param::set_default_by_name("COMPASS_SCALE2", 1);
    AP_Param::set_default_by_name("COMPASS_SCALE3", 1);
    if (sitl_instance == 0) {
        set_external(true);
    }
    hal.scheduler->register_timer_process(FUNCTOR_BIND(this, &AP_Compass_SITL::_timer, void));
}

void AP_Compass_SITL::_timer()
{
    if (sitl_instance != 0) {
        return;
    }
    const EstRecord in = est_input();
    if (!in.mag) {
        return;
    }
    Vector3f field = in.mag_mgauss;
    accumulate_sample(field, 10);
}
