// cpp2lean difftest for AP_Motors: the object the C++ class driver drives. AP_Motors::rc_write,
// rc_write_angle and rc_set_freq are the HAL boundary (--boundary-call): this subclass replaces
// them (they are virtual) by recording the call, as the Lean side records an `Output` event.
// Everything else is AP_MotorsMatrix, unmodified.
#pragma once
#include "cpp2lean_events.h"
#include <AP_Motors/AP_MotorsMatrix.h>
#include <AP_Notify/AP_Notify.h>
#include <AP_AHRS/AP_AHRS.h>

class DriverMotors : public AP_MotorsMatrix {
public:
    DriverMotors(uint16_t speed_hz) : AP_MotorsMatrix(speed_hz) {}
    void rc_write(uint8_t chan, uint16_t pwm) override { cpp2lean_ev("rc_write"); cpp2lean_ev_u(chan); cpp2lean_ev_u(pwm); }
    void rc_write_angle(uint8_t chan, int16_t angle_cd) override { cpp2lean_ev("rc_write_angle"); cpp2lean_ev_u(chan); cpp2lean_ev_i(angle_cd); }
    void rc_set_freq(uint32_t mask, uint16_t freq_hz) override { cpp2lean_ev("rc_set_freq"); cpp2lean_ev_u(mask); cpp2lean_ev_u(freq_hz); }
};
