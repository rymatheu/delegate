/* cpp2lean reference vehicle: stand-in for libraries/SITL/SIM_Compass.h. AP_Compass_SITL.h declares a
   member SITL::CompassSim; the stand-in compass back end (reference/hal/sensors.cpp) does not use it. */
#pragma once
#include <stdint.h>
namespace SITL {
class CompassSim {
public:
    CompassSim(uint8_t _instance) : instance(_instance) {}
private:
    const uint8_t instance;
};
}
