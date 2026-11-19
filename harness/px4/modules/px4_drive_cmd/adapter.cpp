// adapter.cpp: px4_drive_cmd, a TEST DRIVER (see Module.lean): what a ground station and the
// navigator would send when commander is PX4's own. A ground station's commands on vehicle_command
// (one per tick, addressed to system 1 component 1, from 255/190, as QGroundControl sends them):
// DO_SET_MODE Auto Loiter at mode_s, COMPONENT_ARM_DISARM arm at arm_s and every 0.5 s after until
// arm_until_s (commander accepts a repeated arm as a no-op); and the navigator's loiter setpoint:
// takeoff_alt above commander's home altitude, step_n north of EKF2's origin from step_s.
#include "module_protocol.h"

#include <math.h>

static Params prm;

void module_init(const Params &p) { prm = p; }

static bool at(uint32_t t_us, float s) { return t_us >= (uint32_t)(s * 1e6f) && t_us < (uint32_t)(s * 1e6f) + 2500; }

void module_step(const Input &in, Output &out)
{
	const float t = in.t_us * 1e-6f;
	bool arm = false;

	for (float s = prm.arm_s; s <= prm.arm_until_s + 1e-3f; s += 0.5f) {
		arm = arm || at(in.t_us, s);
	}

	const bool mode = at(in.t_us, prm.mode_s);

	if (arm || mode) {
		out.vehicle_command_count = 1;
		out.vehicle_command_timestamp = in.t_us;
		out.vehicle_command_command = arm ? 400 : 176;   // COMPONENT_ARM_DISARM : DO_SET_MODE
		out.vehicle_command_param1 = 1.f;                // arm / custom mode
		out.vehicle_command_param2 = arm ? 0.f : 4.f;    // PX4 main mode AUTO
		out.vehicle_command_param3 = arm ? 0.f : 3.f;    // AUTO sub-mode LOITER
		out.vehicle_command_param5 = NAN;
		out.vehicle_command_param6 = NAN;
		out.vehicle_command_param7 = NAN;
		out.vehicle_command_target_system = 1;
		out.vehicle_command_target_component = 1;
		out.vehicle_command_source_system = 255;
		out.vehicle_command_source_component = 190;
		out.vehicle_command_from_external = true;
	}

	// the navigator's loiter setpoint, from EKF2's reference (previous tick)
	const double ref_lat = (double)in.vehicle_local_position_ref_lat + (double)in.vehicle_local_position_ref_lat_lo;
	// published once EKF2 has a global origin and commander has a home altitude
	const bool ref_ok = in.vehicle_local_position_xy_global && in.vehicle_local_position_z_global &&
			    in.home_position_valid_alt;
	const double R = 6371000.0;                       // CONSTANTS_RADIUS_OF_EARTH
	const double lat = ref_lat + (t >= prm.step_s ? (double)prm.step_n : 0.0) / R * 180.0 / M_PI;
	out.position_setpoint_triplet_updated = ref_ok;
	out.position_setpoint_triplet_timestamp = in.t_us;
	out.position_setpoint_triplet_current_timestamp = in.t_us;
	out.position_setpoint_triplet_current_valid = ref_ok;
	out.position_setpoint_triplet_current_type = 2;   // SETPOINT_TYPE_LOITER
	out.position_setpoint_triplet_current_lat = (float)lat;
	out.position_setpoint_triplet_current_lat_lo = isfinite(lat) ? (float)(lat - (double)(float)lat) : 0.f;
	out.position_setpoint_triplet_current_lon = in.vehicle_local_position_ref_lon;
	out.position_setpoint_triplet_current_lon_lo = in.vehicle_local_position_ref_lon_lo;
	out.position_setpoint_triplet_current_alt = in.home_position_alt + prm.takeoff_alt;   // above home
	out.position_setpoint_triplet_current_yaw = NAN;
	out.position_setpoint_triplet_current_acceptance_radius = 1.f;
	out.position_setpoint_triplet_current_cruising_speed = NAN;
	out.position_setpoint_triplet_current_cruising_throttle = NAN;
}
