// stubs_guidance.cpp: the AC_WPNav shadow (guidance stage).
//
// harness_guidance_fill writes, from the guidance stage's outputs of the previous tick, the
// fields the inline getters the vehicle code calls read:
//   _flags.reached_destination     wp_reached        reached_wp_destination (virtual, inline)
//   _flags.fast_waypoint           wp_fast           force_stop_at_next_wp
//   _paused                        wp_paused         paused (set_pause/set_resume write it: the
//                                                    adapter turns a change into the command)
//   _destination_ned_m             wp_destination_*  get_wp_destination_NED_m, get_oa_wp_
//                                                    destination -> get_wp_destination_loc
//   _origin_ned_m                  wp_origin_*       get_wp_origin_NED_m
// Speeds and accelerations (get_default_speed_*, get_accel_D_mss, get_wp_acceleration_mss) are
// parameters (WPNAV_*, real var_info). AC_Loiter's calls are commands of the loiter stage
// (commands.txt); its readbacks are the position stage's state (AC_Loiter.h pass-throughs:
// get_roll_rad, get_pitch_rad, get_thrust_vector, get_distance_to_target_m,
// get_bearing_to_target_rad) and get_angle_max_rad = lt_angle_max, the loiter stage's value of
// the previous tick (a function of parameters and the position stage's lean limit, which the
// loiter stage computes with its own LOIT_ANG_MAX). AC_Circle has no stage: its shadow's queries
// are unanswered (counted) and CIRCLE does not fly.
//
// Commands that return a value (the real return, predicted from the shadow, and the post-condition
// the same tick reads, AC_WPNav.cpp):
//   set_wp_destination_NED_m, set_spline_destination_NED_m
//       true; _origin = _destination, _destination = destination,
//       _flags.fast_waypoint = false, _flags.reached_destination = false
//   set_wp_destination_next_NED_m, set_spline_destination_next_NED_m
//       true (also when the terrain frame differs, as the real one); _flags.fast_waypoint = true
//   force_stop_at_next_wp   _flags.fast_waypoint, then cleared (real body's first lines)
//   update_wpnav            wp_update_ok of the previous tick (false only on missing terrain;
//                           terrain is off)
// The _loc forms (set_wp_destination_loc, _next_loc, set_spline_destination_loc, _next_loc),
// get_vector_NED_m, get_wp_destination_loc, get_wp_stopping_point_NED_m and get_terrain_source
// are the real bodies (gen/ COPY_REAL): they convert with the EKF origin and call the NED forms.
// Queries: is_active = wp_active, or update_wpnav / wp_and_spline_init_m commanded this tick
// (both set _wp_last_update_ms); get_wp_distance_to_destination_m = wp_distance;
// get_wp_bearing_to_destination_rad = wp_bearing.
#include "Copter.h"
#include "supervisor_shadow.h"
#include "module_records.h"

// the vehicle's navigator (Copter::wp_nav; AC_WPNav has no singleton)
HARNESS_ADDR(Copter, wp_nav)
static AC_WPNav *wpnav() { return HARNESS_REF(AC_WPNav *, copter, Copter, wp_nav); }

HARNESS_ADDR(AC_WPNav, _flags)
HARNESS_ADDR(AC_WPNav, _paused)
HARNESS_ADDR(AC_WPNav, _destination_ned_m)
HARNESS_ADDR(AC_WPNav, _origin_ned_m)

// layout-identical to AC_WPNav::wpnav_flags (AC_WPNav.h)
struct HarnessWpnavFlags {
    uint8_t reached_destination : 1;
    uint8_t fast_waypoint : 1;
    uint8_t wp_yaw_set : 1;
};

static bool wp_active_in, wp_update_ok_in, wp_paused_in;
static float wp_distance_in, wp_bearing_in, lt_angle_max_in;

void harness_guidance_fill(const Input &in)
{
    wp_active_in = in.wp_active;
    wp_update_ok_in = in.wp_update_ok;
    wp_paused_in = in.wp_paused;
    wp_distance_in = in.wp_distance;
    wp_bearing_in = in.wp_bearing;
    lt_angle_max_in = in.lt_angle_max;
    AC_WPNav *w = wpnav();
    if (w == nullptr) {
        return;
    }
    HarnessWpnavFlags &f = HARNESS_REF(HarnessWpnavFlags, *w, AC_WPNav, _flags);
    f.reached_destination = in.wp_reached;
    f.fast_waypoint = in.wp_fast;
    HARNESS_REF(bool, *w, AC_WPNav, _paused) = in.wp_paused;
    HARNESS_REF(Vector3p, *w, AC_WPNav, _destination_ned_m) =
        Vector3p(in.wp_destination_n, in.wp_destination_e, in.wp_destination_d);
    HARNESS_REF(Vector3p, *w, AC_WPNav, _origin_ned_m) =
        Vector3p(in.wp_origin_n, in.wp_origin_e, in.wp_origin_d);
}

// set_pause / set_resume are inline setters of _paused: a change during the tick is the command
void harness_guidance_after()
{
    AC_WPNav *w = wpnav();
    if (w == nullptr) {
        return;
    }
    const bool p = HARNESS_REF(bool, *w, AC_WPNav, _paused);
    if (p != wp_paused_in) {
        sup_cmd_begin_named(p ? "AC_WPNav::set_pause" : "AC_WPNav::set_resume", "guidance");
        sup_cmd_end();
    }
}

bool AC_WPNav::set_wp_destination_NED_m(const Vector3p &destination_ned_m, bool is_terrain_alt,
                                        float arc_rad)
{
    sup_cmd_begin_named("AC_WPNav::set_wp_destination_NED_m", "guidance");
    sup_arg(destination_ned_m);
    sup_arg(is_terrain_alt);
    sup_arg(arc_rad);
    sup_cmd_end();
    _origin_ned_m = _destination_ned_m;
    _destination_ned_m = destination_ned_m;
    _flags.fast_waypoint = false;
    _flags.reached_destination = false;
    return true;
}

bool AC_WPNav::set_spline_destination_NED_m(const Vector3p &destination_ned_m, bool is_terrain_alt,
                                            const Vector3p &next_destination_ned_m,
                                            bool next_terrain_alt, bool next_is_spline)
{
    sup_cmd_begin_named("AC_WPNav::set_spline_destination_NED_m", "guidance");
    sup_arg(destination_ned_m);
    sup_arg(is_terrain_alt);
    sup_arg(next_destination_ned_m);
    sup_arg(next_terrain_alt);
    sup_arg(next_is_spline);
    sup_cmd_end();
    _origin_ned_m = _destination_ned_m;
    _destination_ned_m = destination_ned_m;
    _flags.fast_waypoint = false;
    _flags.reached_destination = false;
    return true;
}

bool AC_WPNav::set_wp_destination_next_NED_m(const Vector3p &destination_ned_m,
                                             bool is_terrain_alt, float arc_rad)
{
    sup_cmd_begin_named("AC_WPNav::set_wp_destination_next_NED_m", "guidance");
    sup_arg(destination_ned_m);
    sup_arg(is_terrain_alt);
    sup_arg(arc_rad);
    sup_cmd_end();
    if (is_terrain_alt == _is_terrain_alt) {
        _flags.fast_waypoint = true;
    }
    return true;
}

bool AC_WPNav::set_spline_destination_next_NED_m(const Vector3p &next_destination_ned_m,
                                                 bool next_is_terrain_alt,
                                                 const Vector3p &next_next_destination_ned_m,
                                                 bool next_next_is_terrain_alt,
                                                 bool next_next_is_spline)
{
    sup_cmd_begin_named("AC_WPNav::set_spline_destination_next_NED_m", "guidance");
    sup_arg(next_destination_ned_m);
    sup_arg(next_is_terrain_alt);
    sup_arg(next_next_destination_ned_m);
    sup_arg(next_next_is_terrain_alt);
    sup_arg(next_next_is_spline);
    sup_cmd_end();
    if (next_is_terrain_alt == _is_terrain_alt) {
        _flags.fast_waypoint = true;
    }
    return true;
}

bool AC_WPNav::force_stop_at_next_wp()
{
    sup_cmd_begin_named("AC_WPNav::force_stop_at_next_wp", "guidance");
    sup_cmd_end();
    if (!_flags.fast_waypoint) {
        return false;
    }
    _flags.fast_waypoint = false;
    return true;
}

bool AC_WPNav::update_wpnav()
{
    sup_cmd_begin_named("AC_WPNav::update_wpnav", "guidance");
    sup_cmd_end();
    return wp_update_ok_in;
}

bool AC_WPNav::is_active() const
{
    return wp_active_in || sup_cmd_called("AC_WPNav::update_wpnav") ||
           sup_cmd_called("AC_WPNav::wp_and_spline_init_m");
}

float AC_WPNav::get_wp_distance_to_destination_m() const
{
    return wp_distance_in;
}

// ModeLoiter::init and run, Mode::get_pilot_desired_velocity (mode.cpp:900): the pilot's lean
// limit in LOITER, from the loiter stage
float AC_Loiter::get_angle_max_rad() const
{
    return lt_angle_max_in;
}

float AC_WPNav::get_wp_bearing_to_destination_rad() const
{
    return wp_bearing_in;
}
