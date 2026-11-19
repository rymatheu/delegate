// adapter.cpp: px4_drive_pos, a TEST DRIVER (see px4/px4_test_drive.h and Module.lean): arming and
// mode over time, and a position setpoint: on the ground (z = 0) until takeoff_s, then
// takeoff_alt above the start, then step_n metres north from step_s on; velocity, acceleration
// and yaw speed not set (NaN), yaw yaw_sp.
#include "module_protocol.h"
#include "px4_test_drive.h"

static Params prm;

void module_init(const Params &p) { prm = p; }

void module_step(const Input &in, Output &out)
{
	drive_status(prm, in.t_us, true, out);
	const float t = in.t_us * 1e-6f;
	out.trajectory_setpoint_updated = true;
	out.trajectory_setpoint_timestamp = in.t_us;
	out.trajectory_setpoint_position_0 = t >= prm.step_s ? prm.step_n : 0.f;
	out.trajectory_setpoint_position_1 = 0.f;
	out.trajectory_setpoint_position_2 = t >= prm.takeoff_s ? -prm.takeoff_alt : 0.f;
	out.trajectory_setpoint_velocity_0 = NAN;
	out.trajectory_setpoint_velocity_1 = NAN;
	out.trajectory_setpoint_velocity_2 = NAN;
	out.trajectory_setpoint_acceleration_0 = NAN;
	out.trajectory_setpoint_acceleration_1 = NAN;
	out.trajectory_setpoint_acceleration_2 = NAN;
	out.trajectory_setpoint_jerk_0 = NAN;
	out.trajectory_setpoint_jerk_1 = NAN;
	out.trajectory_setpoint_jerk_2 = NAN;
	out.trajectory_setpoint_yaw = prm.yaw_sp;
	out.trajectory_setpoint_yawspeed = NAN;
}
