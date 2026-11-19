// adapter.cpp: px4_sim_out, PX4's actuator_motors as plant_sim's PWM inputs (see Module.lean).
// Not PX4 code: pwm_out_sim's mapping with THR_MDL_FAC = 0, PWM_MAIN_MIN/MAX/DIS = 1000/2000/1000.
#include "module_protocol.h"

#include <math.h>

static uint32_t pwm[4];

void module_init(const Params &)
{
	for (int i = 0; i < 4; i++) {
		pwm[i] = 1000;
	}
}

static uint32_t to_pwm(float u)
{
	if (!isfinite(u)) {
		return 1000;    // disarmed / stopped
	}

	u = fminf(fmaxf(u, 0.f), 1.f);
	return (uint32_t)lrintf(1000.f + 1000.f * u);
}

void module_step(const Input &in, Output &out)
{
	if (in.actuator_motors_updated) {
		pwm[0] = to_pwm(in.actuator_motors_control_0);
		pwm[1] = to_pwm(in.actuator_motors_control_1);
		pwm[2] = to_pwm(in.actuator_motors_control_2);
		pwm[3] = to_pwm(in.actuator_motors_control_3);
	}

	out.pwm0 = pwm[0];
	out.pwm1 = pwm[1];
	out.pwm2 = pwm[2];
	out.pwm3 = pwm[3];
}
