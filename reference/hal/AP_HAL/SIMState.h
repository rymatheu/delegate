/* cpp2lean reference vehicle: stand-in for libraries/AP_HAL/SIMState.h, which declares the simulator
   that runs inside a flight controller (AP_SIM_ENABLED on a hardware board; unused on the SITL board,
   where AP_HAL::HAL::simstate is null). Only the declaration of the class remains. */
#pragma once
#include <AP_HAL/AP_HAL_Namespace.h>
