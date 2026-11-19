// stubs_motors.cpp: the mixer.
//
// The mixer is its own module. AC_PosControl reads from it the throttle limit flags
// (limit.throttle_lower/upper, set by the adapter from the mixer's outputs of the previous tick)
// and the hover throttle (get_throttle_hover). HarnessMotors (stand_ins.h) derives from the real
// AP_Motors; the out-of-line members of AP_Motors (AP_Motors_Class.cpp, not compiled) are here.
//
//   symbol                                   why it is outside the stage, and what stands in
//   AP_Motors::AP_Motors(uint16_t)           the mixer's base constructor (AP_Motors_Class.cpp:36).
//                                            Stand-in: speed and singleton only; the throttle
//                                            filters keep their default construction. limit is
//                                            set by the adapter every step.
//   AP_Motors::_singleton                    storage.
//   AP_Motors::arming_checks, motor_test_checks, rc_write, rc_write_angle, rc_set_freq
//                                            the mixer's own work (vtable entries). Abort.
//   HarnessMotors pure-virtual overrides     the mixer's own work. Abort.
//   HarnessMotors::get_throttle_hover        AP_MotorsMulticopter::get_throttle_hover(); returns the
//                                            input throttle_hover (inline, stand_ins.h).
#include <AP_Motors/AP_Motors_Class.h>

AP_Motors *AP_Motors::_singleton;

AP_Motors::AP_Motors(uint16_t speed_hz) :
    _speed_hz(speed_hz)
{
    _singleton = this;
}

bool AP_Motors::arming_checks(size_t buflen, char *buffer) const { unreachable("AP_Motors::arming_checks"); }
bool AP_Motors::motor_test_checks(size_t buflen, char *buffer) const
{
    unreachable("AP_Motors::motor_test_checks");
}
void AP_Motors::rc_write(uint8_t chan, uint16_t pwm) { unreachable("AP_Motors::rc_write"); }
void AP_Motors::rc_write_angle(uint8_t chan, int16_t angle_cd) { unreachable("AP_Motors::rc_write_angle"); }
void AP_Motors::rc_set_freq(uint32_t mask, uint16_t freq_hz) { unreachable("AP_Motors::rc_set_freq"); }

void HarnessMotors::set_desired_spool_state(enum DesiredSpoolState spool) { unreachable("set_desired_spool_state"); }
void HarnessMotors::init(motor_frame_class, motor_frame_type) { unreachable("AP_Motors::init"); }
void HarnessMotors::set_frame_class_and_type(motor_frame_class, motor_frame_type)
{
    unreachable("set_frame_class_and_type");
}
void HarnessMotors::output() { unreachable("AP_Motors::output"); }
void HarnessMotors::output_min() { unreachable("AP_Motors::output_min"); }
uint32_t HarnessMotors::get_motor_mask() { unreachable("get_motor_mask"); }
void HarnessMotors::output_armed_stabilizing() { unreachable("output_armed_stabilizing"); }
void HarnessMotors::update_throttle_filter() { unreachable("update_throttle_filter"); }
const char *HarnessMotors::_get_frame_string() const { unreachable("_get_frame_string"); }
void HarnessMotors::_output_test_seq(uint8_t, int16_t) { unreachable("_output_test_seq"); }
