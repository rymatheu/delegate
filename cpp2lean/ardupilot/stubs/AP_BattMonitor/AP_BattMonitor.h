// ORACLE STUB: replaces libraries/AP_BattMonitor/AP_BattMonitor.h.
// Why: no battery is simulated. Thrust_Linearization::update_lift_max_from_batt_voltage
// (AP_Motors_Thrust_Linearization.cpp:157-185) reads voltage_resting_estimate(); with
// MOT_BAT_VOLT_MAX = 0 it takes the early exit (lift_max = 1, batt_voltage_filt reset to 1) whatever
// the voltage, which is the port's configuration (Thrust_Linearization.Faithful). The stub returns
// 0 V. AP_MotorsMulticopter::get_current_limit_max_throttle (.cpp:379-396) calls current_amps();
// the stub reports no current sensor (false), and MOT_BAT_CURR_MAX = 0 takes the same early exit.
#pragma once
#include <stdint.h>

class AP_BattMonitor {
public:
    float voltage(uint8_t instance) const { return 0.0f; }
    float voltage_resting_estimate(uint8_t instance) const { return 0.0f; }
    bool current_amps(float &current, uint8_t instance) const WARN_IF_UNUSED { return false; }
    float get_resistance(uint8_t instance) const { return 0.0f; }
};

namespace AP {
    AP_BattMonitor &battery();
};
