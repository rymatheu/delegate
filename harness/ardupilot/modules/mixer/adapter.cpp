// adapter.cpp: the cut between the harness records and ArduCopter's real quad-X motor mixer.
//
// The object is a real AP_MotorsMatrix (AP_Motors <- AP_MotorsMulticopter <- AP_MotorsMatrix, with
// its Thrust_Linearization). HarnessMotors below derives from it only to reach protected members:
// it overrides nothing, so every virtual call runs ArduPilot's code.
//
// init builds a fresh object in zeroed storage, sets every AP_Param member the step reads from
// the parameter record (the rest to fixed values, listed below), and runs ArduCopter's set-up:
//   Copter::allocate_motors   NEW_NOTHROW AP_MotorsMatrix(scheduler.get_loop_rate_hz())  (400 Hz)
//                             AP_Param::load_object_from_eeprom (cut: the parameter record)
//   Copter::init_rc_out       init(QUAD, X); set_update_rate(RC_SPEED = 490);
//                             convert_pwm_min_max_param (not called: MOT_PWM_MIN/MAX come from
//                             the parameter record, i.e. are configured, so it would return at
//                             once); update_throttle_range()
//   Copter::init_ardupilot    output_min()
// ArduPilot's operator new returns zeroed memory (AP_Common/c++.cpp), and the constructors leave
// most members (the limit flags aside, _armed, _interlock, the actuators, the filters' state) to it.
//
// step makes the calls ArduCopter makes in one loop, then one call of output():
//   armed(armed)                        the arming library (AP_Arming_Copter::arm / disarm)
//   set_desired_spool_state(.)          the flight mode (update_flight_mode)
//   set_dt_s(dt)                        Copter::run_rate_controller_main
//   set_throttle_filter_cutoff, set_throttle, set_throttle_avg_max
//                                       AC_AttitudeControl_Multi::set_throttle_out
//   set_roll/pitch/yaw and their _ff    AC_AttitudeControl_Multi::rate_controller_run
//   set_spoolup_block(false)            Copter::takeoff_check, when clear_spoolup_block
//   set_interlock(interlock)            Copter::motors_output, just before output()
//   output()                            Mode::output_to_motors, from Copter::motors_output
//
// Parameters fixed, not exposed: MOT_PWM_TYPE 0 (normal), MOT_OPTIONS 0, MOT_BAT_IDX 0,
// MOT_BOOST_SCALE 0, MOT_YAW_SV_ANGLE 30 (tricopter only).
#include "module_protocol.h"

#include <new>
#include <string.h>

#include <AP_Motors/AP_MotorsMatrix.h>

// the cut, defined in stubs.cpp
extern uint32_t harness_clock_us;
extern float harness_batt_voltage;
extern float harness_batt_resting_voltage;
extern float harness_batt_current;
extern bool harness_batt_current_ok;
extern float harness_air_density_ratio;
extern uint16_t harness_motor_pwm[AP_MOTORS_MAX_NUM_MOTORS];
extern uint32_t harness_motor_pwm_writes;
void harness_set_batt_resistance(float r);
void harness_reset_cut();
void harness_reset_internal_errors();
uint32_t harness_internal_error_count();

// The friend ArduPilot declares in Thrust_Linearization for its own motor tests
// (AP_Motors_Thrust_Linearization.h, used by AP_Motors/examples/expo_inverse_test). Used here only
// to set thr_lin's parameters, as the parameter system would.
class AP_MotorsMulticopter_test {
public:
    static void set_params(Thrust_Linearization &t, const Params &p)
    {
        t.curve_expo.set(p.thst_expo);
        t.spin_min.set(p.spin_min);
        t.spin_max.set(p.spin_max);
        t.batt_idx.set(0);
        t.batt_voltage_max.set(p.bat_volt_max);
        t.batt_voltage_min.set(p.bat_volt_min);
    }
};

// AP_MotorsMatrix's constructor panics if its private static _singleton is set, so a second object
// in the same process (a second `init`) needs it cleared. The member is reached by the standard
// rule that access is not checked in an explicit instantiation's template arguments.
void harness_clear_matrix_singleton();
template <AP_MotorsMatrix **P>
struct MatrixSingleton {
    friend void harness_clear_matrix_singleton() { *P = nullptr; }
};
template struct MatrixSingleton<&AP_MotorsMatrix::_singleton>;

class HarnessMotors : public AP_MotorsMatrix {
public:
    HarnessMotors(uint16_t speed_hz) : AP_MotorsMatrix(speed_hz) {}

    // as the parameter system stores each value (AP_Param::set, no constraint)
    void set_params(const Params &p)
    {
        _pwm_type.set(PWMType::NORMAL);
        _options.set(0);
        _yaw_headroom.set(int16_t(p.yaw_headroom));
        _slew_up_time.set(p.slew_up_time);
        _slew_dn_time.set(p.slew_dn_time);
        _safe_time.set(p.safe_time);
        _spin_arm.set(p.spin_arm);
        _batt_current_max.set(p.bat_curr_max);
        _batt_current_time_constant.set(p.bat_curr_tc);
        _pwm_min.set(int16_t(p.pwm_min));
        _pwm_max.set(int16_t(p.pwm_max));
        _throttle_hover.set(p.thst_hover);
        _throttle_hover_learn.set(int8_t(p.hover_learn));
        _disarm_disable_pwm.set(p.safe_disarm ? 1 : 0);
        _yaw_servo_angle_max_deg.set(30.0f);
        _spool_up_time.set(p.spool_time);
        _spool_down_time.set(p.spool_tim_dn);
        _idle_time_delay_s.set(p.idle_sec);
        _boost_scale.set(0.0f);
        AP_MotorsMulticopter_test::set_params(thr_lin, p);
    }

    float actuator(uint8_t i) const { return _actuator[i]; }
    float thrust(uint8_t i) const { return _thrust_rpyt_out[i]; }
};

// ArduCopter allocates the mixer with NEW_NOTHROW, whose memory ArduPilot zeroes
alignas(HarnessMotors) static unsigned char motors_storage[sizeof(HarnessMotors)];
static HarnessMotors *motors;

void module_init(const Params &p)
{
    memset(motors_storage, 0, sizeof motors_storage);
    harness_reset_internal_errors();
    harness_reset_cut();   // clock 0, battery and air-density readings 0, PWM record cleared
    harness_clear_matrix_singleton();
    motors = new (motors_storage) HarnessMotors(400);   // SCHED_LOOP_RATE default
    motors->set_params(p);
    motors->init(AP_Motors::MOTOR_FRAME_QUAD, AP_Motors::MOTOR_FRAME_TYPE_X);
    motors->set_update_rate(490);                       // RC_SPEED default
    motors->update_throttle_range();
    motors->output_min();
}

void module_step(const Input &in, Output &out)
{
    // what the step reads outside the module
    harness_clock_us = in.now_us;                   // AP_HAL::micros(): throttle slew detector
    harness_batt_voltage = in.batt_voltage;         // AP::battery()
    harness_batt_resting_voltage = in.batt_resting_voltage;
    harness_batt_current = in.batt_current;
    harness_batt_current_ok = in.batt_current_ok;
    harness_set_batt_resistance(in.batt_resistance);
    harness_air_density_ratio = in.air_density_ratio;   // AP::ahrs()
    harness_motor_pwm_writes = 0;

    // the vehicle code's calls on the motors made after the previous tick's output()
    // (the supervisor's of the previous tick): arming's output_min (AP_Arming_Copter.cpp:756),
    // update_throttle_hover (Attitude.cpp:62), set_thrust_boost (crash_check.cpp:172)
    if (in.cmd_mixer_output_min) {
        motors->output_min();
        harness_motor_pwm_writes = 0;   // output_min's own output(); the step's output() follows
    }
    if (in.cmd_mixer_update_throttle_hover) {
        motors->update_throttle_hover(in.cmd_mixer_update_throttle_hover_dt);
    }
    if (in.cmd_mixer_set_thrust_boost) {
        motors->set_thrust_boost(in.cmd_mixer_set_thrust_boost_enable);
    }

    motors->armed(in.armed);
    motors->set_desired_spool_state(AP_Motors::DesiredSpoolState(in.spool_desired));
    motors->set_dt_s(in.dt);
    motors->set_throttle_filter_cutoff(in.throttle_filter_hz);
    motors->set_throttle(in.throttle);
    motors->set_throttle_avg_max(in.throttle_avg_max);
    motors->set_roll(in.roll);
    motors->set_roll_ff(in.roll_ff);
    motors->set_pitch(in.pitch);
    motors->set_pitch_ff(in.pitch_ff);
    motors->set_yaw(in.yaw);
    motors->set_yaw_ff(in.yaw_ff);
    if (in.clear_spoolup_block) {
        motors->set_spoolup_block(false);
    }
    motors->set_interlock(in.interlock);
    motors->output();

    out.actuator_1 = motors->actuator(0);
    out.actuator_2 = motors->actuator(1);
    out.actuator_3 = motors->actuator(2);
    out.actuator_4 = motors->actuator(3);
    out.pwm_1 = harness_motor_pwm[0];
    out.pwm_2 = harness_motor_pwm[1];
    out.pwm_3 = harness_motor_pwm[2];
    out.pwm_4 = harness_motor_pwm[3];
    out.pwm_writes = harness_motor_pwm_writes;
    out.thrust_1 = motors->thrust(0);
    out.thrust_2 = motors->thrust(1);
    out.thrust_3 = motors->thrust(2);
    out.thrust_4 = motors->thrust(3);
    out.limit_roll = motors->limit.roll;
    out.limit_pitch = motors->limit.pitch;
    out.limit_yaw = motors->limit.yaw;
    out.limit_throttle_lower = motors->limit.throttle_lower;
    out.limit_throttle_upper = motors->limit.throttle_upper;
    out.spool_state = uint32_t(motors->get_spool_state());
    out.spoolup_block = motors->get_spoolup_block();
    out.throttle_filtered = motors->get_throttle();
    out.throttle_out = motors->get_throttle_out();
    out.throttle_thrust_max = motors->get_throttle_thrust_max();
    out.throttle_slew_rate = motors->get_throttle_slew_rate();
    out.lift_max = motors->thr_lin.get_lift_max();
    out.compensation_gain = motors->thr_lin.get_compensation_gain();
    out.internal_errors = harness_internal_error_count();
    out.throttle_hover = motors->get_throttle_hover();
    out.thrust_boost = motors->get_thrust_boost();
}
