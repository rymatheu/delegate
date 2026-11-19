// backend_compass.cpp: the compass driver, a stand-in for ArduPilot's SITL compass driver.
//
// On the SITL board Compass::_probe_external... creates MAX_CONNECTED_MAGS AP_Compass_SITL
// drivers, one per SIM_MAGn_DEVID (AP_Compass.cpp:1370). This file defines that class's methods
// (libraries/AP_Compass/AP_Compass_SITL.h) in place of AP_Compass_SITL.cpp, which computes the
// field from the simulator's attitude: here the sample is the input record's. The calls on the
// front end are the SITL driver's constructor's and timer's:
//   constructor: register_compass(dev_id), save_dev_id (SIM_MAG_SAVE_IDS 1),
//                set_rotation(ROTATION_NONE), set_offsets to SIM_MAG1_OFS when the offsets are
//                zero, COMPASS_SCALE's default 1, set_external(true), register_timer_process
//   timer:       accumulate_sample(field, 10) for a new sample (100 Hz; here baro-like, every
//                tick with mag_fresh)
// The front end's read() drains the accumulated samples (AP_Compass_Backend).
// Differences from the SITL driver: one compass (SIM_MAG1_DEVID 97539; SIM_MAG2..8_DEVID 0, so
// the other drivers register nothing), as the plant has one; the field is the plant's (in mGauss,
// with the plant's noise), so no SITL scale, offsets, motor interference, anomaly or delay
// (SIM_MAG_*). SIM_MAG1_OFS is the plant's offsets (below); with COMPASS_OFS at its default 0,
// the constructor sets COMPASS_OFS to them, as the SITL driver does.
#include <AP_Compass/AP_Compass_SITL.h>
#include <AP_HAL/AP_HAL.h>

#include "harness_cut.h"

extern const AP_HAL::HAL &hal;

static const uint32_t SIM_MAG1_DEVID = 97539;   // SITL.cpp:837
// The offsets the plant's compass model subtracts from the field (plant_sim: "minus SITL's
// offsets"), SITL's copter.parm values (Tools/autotest/default_params/copter.parm, COMPASS_OFS_X/Y/Z
// 5, 13, -18), which a SITL run with SIM_MAG1_OFS set to them reproduces. Measured: at rest, level,
// heading north, the plant reports (210.7, 14.7, 477.6) mGauss; adding these offsets gives a
// horizontal field 7.3 deg east of north, the declination ArduPilot's table gives there.
static const Vector3f SIM_MAG1_OFS(5, 13, -18);

AP_Compass_SITL::AP_Compass_SITL(uint8_t _sitl_instance) :
    _sitl(AP::sitl()),
    sitl_instance(_sitl_instance)
{
    const uint32_t dev_id = sitl_instance == 0 ? SIM_MAG1_DEVID : 0;
    if (dev_id == 0) {
        return;
    }
    if (!register_compass(dev_id)) {
        return;
    }
    save_dev_id();      // SIM_MAG_SAVE_IDS 1
    set_rotation(ROTATION_NONE);

    if (_compass.get_offsets(instance).is_zero()) {
        _compass.set_offsets(instance, SIM_MAG1_OFS);
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
    const HarnessTick &t = harness_tick;
    if (!t.mag_fresh) {
        return;
    }
    Vector3f f(t.mag[0], t.mag[1], t.mag[2]);
    accumulate_sample(f, 10);
}
