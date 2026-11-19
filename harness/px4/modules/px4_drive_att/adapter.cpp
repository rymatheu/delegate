// adapter.cpp: px4_drive_att, a TEST DRIVER (see px4/px4_test_drive.h and Module.lean): arming and
// mode over time, and a level attitude setpoint whose thrust is idle on the ground and ramps to the
// flight thrust after takeoff_s.
#include "module_protocol.h"
#include "px4_test_drive.h"

static Params prm;

void module_init(const Params &p) { prm = p; }

void module_step(const Input &in, Output &out)
{
	drive_status(prm, in.t_us, false, out);
	const float t = in.t_us * 1e-6f;
	float thrust = 0.f;

	if (t >= prm.arm_s) {
		const float r = prm.ramp_s > 0.f ? fminf(fmaxf((t - prm.takeoff_s) / prm.ramp_s, 0.f), 1.f)
				: (t >= prm.takeoff_s ? 1.f : 0.f);
		thrust = prm.idle_thrust + r * (prm.flight_thrust - prm.idle_thrust);
	}

	// level, heading yaw_sp (rotation about down): q = (cos(yaw/2), 0, 0, sin(yaw/2))
	out.vehicle_attitude_setpoint_updated = true;
	out.vehicle_attitude_setpoint_timestamp = in.t_us;
	out.vehicle_attitude_setpoint_q_d_0 = cosf(0.5f * prm.yaw_sp);
	out.vehicle_attitude_setpoint_q_d_3 = sinf(0.5f * prm.yaw_sp);
	out.vehicle_attitude_setpoint_thrust_body_2 = -thrust;
	out.vehicle_attitude_setpoint_yaw_sp_move_rate = NAN;
}
