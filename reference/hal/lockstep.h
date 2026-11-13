/* cpp2lean reference vehicle: the lock-step HAL (PORT-PLAN.md section 3, REFERENCE.md).

   One thread. The clock is a counter that moves only when the vehicle waits (Scheduler::delay*,
   AP_InertialSensor::wait_for_sample through delay_microseconds_boost), and only by consuming one
   input line: every line is one boundary step, carrying its time stamp, the sensor samples of that
   step, the RC frame, the battery reading and the MAVLink bytes received since the previous step.
   Before consuming line k+1 the HAL writes output line k: the motor PWM pushed so far and the MAVLink
   bytes written since the previous output line. This is SITL's lock-step semantics
   (HALSITL::Scheduler::delay_microseconds -> SITL_State::wait_clock -> _fdm_input_step), with the
   simulator replaced by the input lines. */
#pragma once

#include <AP_HAL/AP_HAL.h>
#include <AP_Math/AP_Math.h>

#include "est_input.h"

namespace Lockstep {

static const uint8_t MAX_IMUS = EST_MAX_IMUS;
static const uint8_t MAX_IMU_SAMPLES = EST_MAX_IMU_SAMPLES;   // samples per IMU per step (3 in the flights: 1200 Hz)
static const uint8_t RC_CHANNELS = 16;

// the input line being processed (valid after the step that read it): the sensor part is the record the
// stand-ins read through est_input() (est_input.h), the rest is the HAL's
struct Input : EstRecord {
    bool rc;    uint16_t rc_pwm[RC_CHANNELS];      // a new RC frame this step
    float batt_v, batt_a;                          // battery voltage (V) and current (A)
};

extern Input in;
extern uint8_t num_imus;          // IMUs of the SITL::SIM stand-in (--imus, default 1)
extern uint16_t imu_rate_hz;      // sample rate the IMU stand-in registers (--imu-rate, default 1200)

// advance the clock by consuming one input line (emits the output line of the previous one first)
void step();

// time between the previous input line and the current one (us; 2500 before the second line)
uint64_t step_period_us();

}  // namespace Lockstep

// the estimation output (--est FILE, est_probe.cpp): one line per step, written after the step's output line
namespace EstProbe {
bool open(const char *path);
bool enabled();
void close();
// the line just consumed: during boot-time init (before the main loop), and the scheduler task slot
// (AP_HAL::Util::persistent_data.scheduler_task) of the wait that consumed it
void consumed(bool init, int where);
// the line of the step that ends now (clock t_us); delay_callbacks: delay callbacks run in the step
void emit(uint64_t t_us, uint32_t delay_callbacks);
// an event of the sensor stand-ins in the step (est_input.h: EST_EV_*)
void event(uint8_t ev);
}  // namespace EstProbe
