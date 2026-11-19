// adapter.cpp: px4_drive_nav, a TEST DRIVER (see Module.lean): a ground station's commands on
// vehicle_command, one at a time, each once: arm, NAV_TAKEOFF, DO_REPOSITION, NAV_LAND, each at
// the first step at or after its time in which commander's vehicle_status of the previous tick
// was published (as navigator wants its commands).
#include "module_protocol.h"

#include <math.h>

static Params prm;
static int next_cmd;   // 0 arm, 1 takeoff, 2 reposition, 3 land, 4 done

void module_init(const Params &p) { prm = p; next_cmd = 0; }

void module_step(const Input &in, Output &out)
{
	const float t = in.t_us * 1e-6f;
	const float at[4] = {prm.arm_s, prm.takeoff_s, prm.repos_s, prm.land_s};

	if (next_cmd >= 4 || t < at[next_cmd] || !in.vehicle_status_updated) {
		return;
	}

	if (next_cmd == 2 && !in.home_position_valid_hpos) {
		return;   // a ground station repositions relative to a known home
	}

	out.vehicle_command_count = 1;
	out.vehicle_command_timestamp = in.t_us;
	out.vehicle_command_param1 = 0.f;
	out.vehicle_command_param2 = 0.f;
	out.vehicle_command_param3 = 0.f;
	out.vehicle_command_param4 = NAN;
	out.vehicle_command_param5 = NAN;
	out.vehicle_command_param6 = NAN;
	out.vehicle_command_param7 = NAN;

	switch (next_cmd) {
	case 0:
		out.vehicle_command_command = 400;   // COMPONENT_ARM_DISARM
		out.vehicle_command_param1 = 1.f;    // arm
		break;

	case 1:
		out.vehicle_command_command = 22;    // NAV_TAKEOFF at the current position, default altitude
		break;

	case 2: {
			out.vehicle_command_command = 192;   // DO_REPOSITION
			out.vehicle_command_param1 = -1.f;   // default ground speed
			out.vehicle_command_param2 = 1.f;    // MAV_DO_REPOSITION_FLAGS_CHANGE_MODE
			const double R = 6371000.0;          // CONSTANTS_RADIUS_OF_EARTH
			const double lat = (double)in.home_position_lat + (double)in.home_position_lat_lo +
					   (double)prm.repos_n / R * 180.0 / M_PI;
			const double lon = (double)in.home_position_lon + (double)in.home_position_lon_lo;
			out.vehicle_command_param5 = (float)lat;   // the slot's binary32
			out.vehicle_command_param6 = (float)lon;
			break;
		}

	default:
		out.vehicle_command_command = 21;    // NAV_LAND where it is
		break;
	}

	out.vehicle_command_target_system = 1;
	out.vehicle_command_target_component = 1;
	out.vehicle_command_source_system = 255;
	out.vehicle_command_source_component = 190;
	out.vehicle_command_from_external = true;
	next_cmd++;
}
