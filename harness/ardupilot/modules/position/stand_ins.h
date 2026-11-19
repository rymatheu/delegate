// stand_ins.h: the objects AC_PosControl holds references to, which belong to other stages.
//
// AC_PosControl is constructed with an AP_AHRS_View& (estimator), a const AP_Motors& (mixer) and
// an AC_AttitudeControl& (attitude). Those stages are separate modules; what the position
// controller reads from them each tick arrives as input signals and is loaded into these objects
// before the controller runs (adapter.cpp), and what it writes into them (set_throttle_out) is
// recorded and leaves as output signals. The classes below derive from ArduPilot's own base
// classes, so the inline accessors AC_PosControl calls (get_att_target_euler_rad, get_throttle_in,
// get_bf_feedforward, get_ang_vel_*_max_rads, get_accel_*_max_radss, cos_yaw, sin_yaw, limit.*)
// are ArduPilot's code reading members that hold the signal values.
#pragma once

#include <AC_AttitudeControl/AC_AttitudeControl.h>
#include <AP_Motors/AP_Motors_Class.h>
#include <AP_AHRS/AP_AHRS.h>
#include <AP_AHRS/AP_AHRS_View.h>

// The values this tick's input record carries for the stand-ins (set by the adapter, read by
// the stub bodies in stubs_*.cpp).
struct HarnessCut {
    // the clock, AP_HAL::millis()
    uint32_t now_ms;
    // estimator: what AP_AHRS::update() and AP_AHRS_View::update() would have left behind
    float pos_n, pos_e, pos_d;
    bool pos_ne_valid, pos_d_valid;
    float vel_n, vel_e, vel_d;
    bool vel_valid;
    float vert_pos_rate_d;
    bool vert_pos_rate_valid;
    float accel_ef_d;
    float yaw, cos_yaw, sin_yaw;
    float gain_scaler_xy, gain_scaler_z;
    uint16_t pos_ne_reset_key, pos_d_reset_key;
    // attitude controller
    float althold_lean_angle_max_rad;
    float lean_angle_max_rad;
    // mixer
    float throttle_hover;
};
extern HarnessCut harness_cut;

// the attitude controller (stubs_attitude.cpp defines the base class's out-of-line members)
class HarnessAttitude : public AC_AttitudeControl {
public:
    HarnessAttitude(AP_AHRS_View &ahrs, AP_Motors &motors) : AC_AttitudeControl(ahrs, motors) {}

    AC_PID &get_rate_roll_pid() override;
    AC_PID &get_rate_pitch_pid() override;
    AC_PID &get_rate_yaw_pid() override;
    const AC_PID &get_rate_roll_pid() const override;
    const AC_PID &get_rate_pitch_pid() const override;
    const AC_PID &get_rate_yaw_pid() const override;
    void rate_controller_run() override;
    void update_althold_lean_angle_max(float throttle_in) override;

    // AC_AttitudeControl_Multi::set_throttle_out stores _throttle_in first, then works on the
    // mixer (attitude stage). Here the call is recorded: its arguments are output signals.
    void set_throttle_out(float throttle_in, bool apply_angle_boost, float filt_cutoff) override
    {
        _throttle_in = throttle_in;
        throttle_set = true;
        throttle_arg = throttle_in;
        angle_boost_arg = apply_angle_boost;
        cutoff_arg = filt_cutoff;
    }

    // the supervisor's own set_throttle_out of this tick (a command of the attitude stage, which
    // executes it), at its place in the supervisor's call order: AC_AttitudeControl_Multi's
    // set_throttle_out stores _throttle_in first, so a D_init_controller after it reads this
    // value through get_throttle_in() (adapter.cpp, OP_SUPERVISOR_SET_THROTTLE). Not recorded as
    // this stage's throttle output.
    void supervisor_set_throttle_out(float throttle_in) { _throttle_in = throttle_in; }

    // the attitude stage's parameters the position controller reads (NE_set_max_speed_accel_m)
    void set_params(float rate_r_max, float rate_p_max, float acc_r_max, float acc_p_max)
    {
        _ang_vel_roll_max_degs.set(rate_r_max);
        _ang_vel_pitch_max_degs.set(rate_p_max);
        _accel_roll_max_degss.set(acc_r_max);
        _accel_pitch_max_degss.set(acc_p_max);
    }

    // the attitude stage's state at the end of the previous tick
    void load(float roll, float pitch, float yaw, float throttle_in, bool bf_feedforward)
    {
        _euler_angle_target_rad = Vector3f{roll, pitch, yaw};
        _throttle_in = throttle_in;
        _rate_bf_ff_enabled.set(bf_feedforward ? 1 : 0);
        throttle_set = false;
    }

    bool throttle_set;
    float throttle_arg;
    bool angle_boost_arg;
    float cutoff_arg;
};

// the mixer (stubs_motors.cpp defines AP_Motors' out-of-line members)
class HarnessMotors : public AP_Motors {
public:
    HarnessMotors() : AP_Motors(400) {}
    // AP_MotorsMulticopter::get_throttle_hover() as the mixer stage reports it
    float get_throttle_hover() const override { return harness_cut.throttle_hover; }
    void set_desired_spool_state(enum DesiredSpoolState spool) override;
    void init(motor_frame_class frame_class, motor_frame_type frame_type) override;
    void set_frame_class_and_type(motor_frame_class frame_class, motor_frame_type frame_type) override;
    void output() override;
    void output_min() override;
    uint32_t get_motor_mask() override;
protected:
    void output_armed_stabilizing() override;
    void update_throttle_filter() override;
    const char *_get_frame_string() const override;
    void _output_test_seq(uint8_t motor_seq, int16_t pwm) override;
};
