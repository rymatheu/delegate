// adapter.cpp: px4_drive_auto, a TEST DRIVER (see px4/px4_test_drive.h and Module.lean): what
// commander and the navigator would publish for an Auto Loiter flight. Arming and Auto Loiter
// mode over time, actuator_armed, home at EKF2's origin horizontally and at EKF2's altitude at
// arming, and the navigator's loiter setpoint: takeoff_alt above home, step_n metres north of
// EKF2's origin from step_s on. The setpoint is
// global (lat/lon in degrees, alt AMSL), made from EKF2's local-frame reference (ref_lat, ref_lon,
// ref_alt of vehicle_local_position, the previous tick) with PX4's earth radius and the
// azimuthal-equidistant projection near the origin (north offset / R).
#include "module_protocol.h"
#include "px4_test_drive.h"

static Params prm;
static float home_alt;      // EKF2's altitude (AMSL) at arming, as commander sets home
static bool home_set;

void module_init(const Params &p)
{
	prm = p;
	home_set = false;
	home_alt = 0.f;
}

void module_step(const Input &in, Output &out)
{
	drive_mode(prm, in.t_us, true, true, out);
	const float t = in.t_us * 1e-6f;
	const bool armed = t >= prm.arm_s;
	const double ref_lat = (double)in.vehicle_local_position_ref_lat + (double)in.vehicle_local_position_ref_lat_lo;
	const double ref_lon = (double)in.vehicle_local_position_ref_lon + (double)in.vehicle_local_position_ref_lon_lo;
	const bool ref_ok = in.vehicle_local_position_xy_global && in.vehicle_local_position_z_global;
	const double R = 6371000.0;                       // CONSTANTS_RADIUS_OF_EARTH
	const double north = t >= prm.step_s ? (double)prm.step_n : 0.0;
	const double lat = ref_lat + north / R * 180.0 / M_PI;

	// home altitude: EKF2's global altitude (ref_alt - z) when armed, as commander sets
	// home_position.alt from vehicle_global_position at arming; the loiter setpoint is takeoff_alt
	// above it, as the navigator's takeoff is MIS_TAKEOFF_ALT above home (not above EKF2's local
	// origin, which can sit below the ground: see px4_auto_loop)
	if (!home_set && armed && ref_ok && isfinite(in.vehicle_local_position_z)) {
		home_alt = in.vehicle_local_position_ref_alt - in.vehicle_local_position_z;
		home_set = true;
	}

	out.actuator_armed_updated = true;
	out.actuator_armed_timestamp = in.t_us;
	out.actuator_armed_armed = armed;
	out.actuator_armed_prearmed = true;
	out.actuator_armed_ready_to_arm = true;

	out.home_position_updated = ref_ok;
	out.home_position_timestamp = in.t_us;
	out.home_position_lat = in.vehicle_local_position_ref_lat;
	out.home_position_lat_lo = in.vehicle_local_position_ref_lat_lo;
	out.home_position_lon = in.vehicle_local_position_ref_lon;
	out.home_position_lon_lo = in.vehicle_local_position_ref_lon_lo;
	out.home_position_alt = home_set ? home_alt : in.vehicle_local_position_ref_alt;
	out.home_position_valid_alt = ref_ok;
	out.home_position_valid_hpos = ref_ok;
	out.home_position_valid_lpos = ref_ok;

	out.position_setpoint_triplet_updated = ref_ok;
	out.position_setpoint_triplet_timestamp = in.t_us;
	out.position_setpoint_triplet_current_timestamp = in.t_us;
	out.position_setpoint_triplet_current_valid = ref_ok;
	out.position_setpoint_triplet_current_type = 2;   // SETPOINT_TYPE_LOITER
	out.position_setpoint_triplet_current_lat = (float)lat;
	// the generator's float64 pair: value rounded, and the rest (0 for a non-finite value)
	out.position_setpoint_triplet_current_lat_lo = isfinite(lat) ? (float)(lat - (double)(float)lat) : 0.f;
	out.position_setpoint_triplet_current_lon = in.vehicle_local_position_ref_lon;
	out.position_setpoint_triplet_current_lon_lo = in.vehicle_local_position_ref_lon_lo;
	out.position_setpoint_triplet_current_alt = (home_set ? home_alt : in.vehicle_local_position_ref_alt) + prm.takeoff_alt;
	out.position_setpoint_triplet_current_yaw = NAN;
	out.position_setpoint_triplet_current_acceptance_radius = 1.f;
	out.position_setpoint_triplet_current_cruising_speed = NAN;
	out.position_setpoint_triplet_current_cruising_throttle = NAN;
	(void)ref_lon;
}
