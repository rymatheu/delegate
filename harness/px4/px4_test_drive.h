// px4_test_drive.h: the shared part of the PX4 TEST DRIVERS (px4/modules/px4_drive_att, px4_drive_pos).
// Not PX4 code and not a model of PX4: a script over time that stands in for commander (arming,
// mode), the land detector and the setpoint source, so that a closed loop around the simulator can be
// flown through a takeoff. Include after module_records.h.
#pragma once

#include <math.h>
#include <stdint.h>

// vehicle_status and vehicle_control_mode: disarmed until arm_s, armed after; in Offboard
// (nav_state 14) or, with auto_loiter, in Auto Loiter (nav_state 4, commander's flags for it,
// control_mode.cpp).
template<class Out, class P>
static void drive_mode(const P &p, uint32_t t_us, bool position_control, bool auto_loiter, Out &out)
{
	const float t = t_us * 1e-6f;
	const bool armed = t >= p.arm_s;
	out.vehicle_status_updated = true;
	out.vehicle_status_timestamp = t_us;
	out.vehicle_status_arming_state = armed ? 2 : 1;          // ARMING_STATE_ARMED : DISARMED
	out.vehicle_status_nav_state = auto_loiter ? 4 : 14;      // AUTO_LOITER : OFFBOARD
	out.vehicle_status_nav_state_user_intention = auto_loiter ? 4 : 14;
	out.vehicle_status_vehicle_type = 1;                      // VEHICLE_TYPE_ROTARY_WING
	out.vehicle_status_system_type = 2;                       // MAV_TYPE_QUADROTOR
	out.vehicle_status_system_id = 1;
	out.vehicle_status_component_id = 1;
	out.vehicle_status_armed_time = armed ? (uint32_t)(p.arm_s * 1e6f) : 0;
	out.vehicle_status_pre_flight_checks_pass = true;
	out.vehicle_status_power_input_valid = true;
	out.vehicle_status_safety_off = true;
	out.vehicle_control_mode_updated = true;
	out.vehicle_control_mode_timestamp = t_us;
	out.vehicle_control_mode_flag_armed = armed;
	out.vehicle_control_mode_flag_control_offboard_enabled = !auto_loiter;
	out.vehicle_control_mode_flag_control_auto_enabled = auto_loiter;
	out.vehicle_control_mode_flag_multicopter_position_control_enabled = position_control;
	out.vehicle_control_mode_flag_control_position_enabled = position_control;
	out.vehicle_control_mode_flag_control_velocity_enabled = position_control;
	out.vehicle_control_mode_flag_control_altitude_enabled = position_control;
	out.vehicle_control_mode_flag_control_climb_rate_enabled = position_control;
	out.vehicle_control_mode_flag_control_acceleration_enabled = position_control && !auto_loiter;
	out.vehicle_control_mode_flag_control_attitude_enabled = true;
	out.vehicle_control_mode_flag_control_rates_enabled = true;
	out.vehicle_control_mode_flag_control_allocation_enabled = true;
}

// vehicle_land_detected: landed until takeoff_s, flying after (what a land detector would say)
template<class Out, class P>
static void drive_land(const P &p, uint32_t t_us, Out &out)
{
	const float t = t_us * 1e-6f;
	const bool armed = t >= p.arm_s;
	const bool flying = t >= p.takeoff_s;
	out.vehicle_land_detected_updated = true;
	out.vehicle_land_detected_timestamp = t_us;
	out.vehicle_land_detected_landed = !flying;
	out.vehicle_land_detected_maybe_landed = !flying;
	out.vehicle_land_detected_ground_contact = !flying;
	out.vehicle_land_detected_at_rest = !armed;
	out.vehicle_land_detected_has_low_throttle = !flying;
	out.vehicle_land_detected_close_to_ground_or_skipped_check = true;
}

// the Offboard set of px4_drive_att / px4_drive_pos
template<class Out, class P>
static void drive_status(const P &p, uint32_t t_us, bool position_control, Out &out)
{
	drive_mode(p, t_us, position_control, false, out);
	drive_land(p, t_us, out);
}
