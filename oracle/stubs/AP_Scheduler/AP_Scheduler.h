// ORACLE STUB: replaces libraries/AP_Scheduler/AP_Scheduler.h.
// Why: the real scheduler runs the task table on the HAL; here the harness is the loop. The getters
// the control code reads keep the real names (AP_Scheduler.h): ticks32()/ticks() (AC_PosControl
// timing checks, :585, :691, :928, :1071), get_loop_rate_hz() (AC_AttitudeControl_Multi.cpp:344,
// notch sample rate, compiled out with AP_FILTER_ENABLED 0 except the call), get_loop_period_s(),
// get_filtered_loop_time() (AC_AttitudeControl.cpp:1427-1457, logging/diagnostics only),
// get_last_loop_time_s(). The harness advances them exactly as Copter/Loop.lean `scheduler_loop`
// does: _tick_counter32 += 1 before the tasks, _last_loop_time_s = 1/400 on the first tick and
// float(dt_us) * 1.0e-6f after (AP_Scheduler.cpp:360-377).
#pragma once

#include <stdint.h>

class AP_Scheduler {
public:
    uint32_t _tick_counter32 = 0;
    uint16_t _tick_counter = 0;
    float _last_loop_time_s = 0.0f;
    uint16_t _loop_rate_hz = 400;   // SCHED_LOOP_RATE, Copter default (AP_Scheduler.cpp:43-44)

    uint32_t ticks32() const { return _tick_counter32; }
    uint16_t ticks() const { return _tick_counter; }
    uint16_t get_loop_rate_hz(void) { return _loop_rate_hz; }
    float get_loop_period_s() { return 1.0f / _loop_rate_hz; }
    float get_last_loop_time_s(void) const { return _last_loop_time_s; }
    float get_filtered_loop_time(void) const { return _last_loop_time_s; }
};

namespace AP {
    AP_Scheduler &scheduler();
};
