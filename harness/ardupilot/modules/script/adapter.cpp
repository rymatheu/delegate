// adapter.cpp: the TEST DRIVER (Module.lean). Hand-written, not ArduPilot code and not part of
// the flight stack: it issues, tick by tick, the calls ArduCopter's vehicle code makes on the
// controllers for one flight, as command ports, and the arming, spool and clock signals.
// Line numbers are ArduCopter/ files of the checkout. Calls the stages execute in their own
// fixed order (each stage's Module.lean); where ArduCopter's order within a tick differs, it is
// said below.
//
// Every tick (the fast loop, Copter.cpp:115-140):
//   read_inertia            pos_control->update_estimates(high_vibes = false)    inertia.cpp:7
//   update_flight_mode      attitude_control->landed_gain_reduction(land_complete)  mode.cpp:513
//                           pos_control->set_reset_handling_method(...)            mode.cpp:516
//                           flightmode->run()
//   throttle_loop (50 Hz)   update_throttle_mix                       land_detector.cpp:281-321
//   takeoff_check (50 Hz)   motors->set_spoolup_block(false)          takeoff_check.cpp:26, 49
//   motors_output           interlock = armed && !in_arming_delay      motors.cpp:78-99
//
// The flight:
//   t = 0       Copter::set_mode(GUIDED): ModeGuided::init -> velaccel_control_start ->
//               pva_control_start (mode_guided.cpp:360-380): NE_set_max_speed_accel_m(WP_SPD,
//               WP_ACC), NE_set_correction_speed_accel_m(same), D_set_max_speed_accel_m(WP_SPD_DN,
//               WP_SPD_UP, WP_ACC_Z), D_set_correction_speed_accel_m(same), D_init_controller,
//               NE_init_controller; then set_roll_pitch_rate_tc(ACRO_RP_RATE_TC = 0),
//               set_yaw_rate_tc(PILOT_Y_RATE_TC = 0) (mode.cpp:466-468)
//   disarmed or landed and not auto-armed: velaccel_control_run -> is_disarmed_or_landed ->
//               Mode::make_safe_ground_handling (mode_guided.cpp:837-840, mode.cpp:658-690)
//   sc_arm_ms   AP_Arming_Copter::arm: motors->armed(true), in_arming_delay for
//               ARMING_DELAY_SEC = 2 s (AP_Arming_Copter.cpp:756-779, config.h:47)
//               (motors->output_min() at :756 is not a mixer command: not issued)
//   sc_takeoff_ms  the GCS's NAV_TAKEOFF: Mode::do_user_takeoff_U_m (takeoff.cpp:18-46) ->
//               ModeGuided::do_user_takeoff_start_m (mode_guided.cpp:160-205): auto_yaw HOLD,
//               pos_control->D_init_controller(), auto_takeoff.start_m(alt above origin);
//               set_auto_armed(true). ArduCopter handles the GCS after the fast loop; here the
//               calls are made at the start of the next tick's mode code (no update between).
//   GUIDED TakeOff: takeoff_run -> _AutoTakeoff::run (takeoff.cpp:115-221), its three branches
//   takeoff complete (the run's own test, from the previous tick's position-stage outputs):
//               the GCS switches to AUTO with a one-item mission (WAYPOINT sc_leg_n, sc_leg_e,
//               at the takeoff altitude above home): Copter::set_mode -> ModeAuto::init
//               (mode_auto.cpp:23-75): wp_nav->wp_and_spline_init_m(); set_mode's rate time
//               constants; run(): mission start -> do_nav_wp -> wp_start (mode_auto.cpp:465-505:
//               wp_nav is active, so no second init) -> set_wp_destination_loc, given here in
//               NED metres from the origin (= home); auto_yaw LOOK_AT_NEXT_WP (WP_YAW_BEHAVIOR 2);
//               then wp_run (mode_auto.cpp:1134-1152)
//   AUTO WP:    mission.update -> verify_nav_wp (wp_reached, loiter time 0; mode_auto.cpp:2297)
//               -> no more items -> exit_mission -> loiter_start (mode_auto.cpp:374-394, 904-917):
//               set_wp_destination_NED_m(stopping point), auto_yaw HOLD; loiter_run = wp_run
//
// Read-backs: a value ArduCopter's mode code reads within the tick after a controller call
// (pos_control's desired position and velocity at takeoff completion, get_yaw_rad for
// LOOK_AT_NEXT_WP) is the stage's output of the previous tick here: one tick late.
// Left out: RC input (none: no pilot yaw, throttle_zero true), the land detector (land_complete
// is only cleared by the takeoff, never set again), crash and failsafe checks, the EKF reset
// checks, accel_moving in update_throttle_mix (taken false), logging and notifications.
#include "module_protocol.h"

#include <math.h>
#include <string.h>

enum Phase : uint32_t {
    DISARMED = 0, ARMED_GROUND = 1, TAKEOFF_SPOOL = 2, TAKEOFF_GROUND = 3, TAKEOFF_CLIMB = 4,
    AUTO_WP = 5, AUTO_LOITER = 6
};

static Params P;
static uint32_t tick;
static bool armed, in_arming_delay, land_complete, auto_armed;
static uint32_t arm_time_ms;
static bool takeoff_mode;       // GUIDED SubMode::TakeOff
static bool takeoff_complete;
static bool takeoff_requested;
static float takeoff_alt_m;     // auto_takeoff.complete_alt_m (above origin)
static bool auto_mode, auto_started, loiter;
static bool yaw_look_at_next_wp;

static const float GRAVITY_MSS = 9.80665f;
static const float G_DT = 0.0025f;   // scheduler loop period at 400 Hz

void module_init(const Params &p)
{
    P = p;
    tick = 0;
    armed = in_arming_delay = false;
    land_complete = true;
    auto_armed = false;
    arm_time_ms = 0;
    takeoff_mode = takeoff_complete = takeoff_requested = false;
    takeoff_alt_m = 0.0f;
    auto_mode = auto_started = loiter = false;
    yaw_look_at_next_wp = false;
}

// pva_control_start's calls (mode_guided.cpp:362-372)
static void pva_control_start(Output &o)
{
    o.cmd_position_NE_set_max_speed_accel_m = true;
    o.cmd_position_NE_set_max_speed_accel_m_speed = P.wp_spd;
    o.cmd_position_NE_set_max_speed_accel_m_accel = P.wp_acc;
    o.cmd_position_NE_set_correction_speed_accel_m = true;
    o.cmd_position_NE_set_correction_speed_accel_m_speed = P.wp_spd;
    o.cmd_position_NE_set_correction_speed_accel_m_accel = P.wp_acc;
    o.cmd_position_D_set_max_speed_accel_m = true;
    o.cmd_position_D_set_max_speed_accel_m_down = P.wp_spd_dn;
    o.cmd_position_D_set_max_speed_accel_m_up = P.wp_spd_up;
    o.cmd_position_D_set_max_speed_accel_m_accel = P.wp_acc_z;
    o.cmd_position_D_set_correction_speed_accel_m = true;
    o.cmd_position_D_set_correction_speed_accel_m_down = P.wp_spd_dn;
    o.cmd_position_D_set_correction_speed_accel_m_up = P.wp_spd_up;
    o.cmd_position_D_set_correction_speed_accel_m_accel = P.wp_acc_z;
    o.cmd_position_D_init_controller = true;
    o.cmd_position_NE_init_controller = true;
}

// Copter::set_mode's rate time constants (mode.cpp:466-468), defaults 0
static void set_mode_rate_tc(Output &o)
{
    o.cmd_attitude_set_roll_pitch_rate_tc = true;
    o.cmd_attitude_set_roll_pitch_rate_tc_input_tc = 0.0f;
    o.cmd_attitude_set_yaw_rate_tc = true;
    o.cmd_attitude_set_yaw_rate_tc_input_tc = 0.0f;
}

// Mode::make_safe_ground_handling(false) (mode.cpp:658-690)
static void make_safe_ground_handling(const Input &in, Output &o)
{
    o.spool_desired = 1;   // GROUND_IDLE
    o.cmd_attitude_reset_rate_controller_I_terms_smoothly = true;
    if (in.spool_state == 0 || in.spool_state == 1) {   // SHUT_DOWN, GROUND_IDLE
        o.cmd_attitude_reset_yaw_target_and_rate = true;
        o.cmd_attitude_reset_yaw_target_and_rate_reset_rate = true;
    }
    o.cmd_position_NE_relax_velocity_controller = true;
    o.cmd_position_NE_update_controller = true;
    o.cmd_position_D_relax_controller = true;
    o.cmd_position_D_relax_controller_throttle = 0.0f;
    o.cmd_position_D_update_controller = true;
    o.cmd_attitude_pos_throttle_after_input = false;   // D_update (set_throttle_out) first
    o.cmd_attitude_input_euler_angle_roll_pitch_euler_rate_yaw = true;
    o.cmd_attitude_input_euler_angle_roll_pitch_euler_rate_yaw_roll = 0.0f;
    o.cmd_attitude_input_euler_angle_roll_pitch_euler_rate_yaw_pitch = 0.0f;
    o.cmd_attitude_input_euler_angle_roll_pitch_euler_rate_yaw_yaw_rate = 0.0f;
}

// auto_yaw.get_heading() (autoyaw.cpp:356-391): HOLD is Rate_Only at the attitude target's yaw
// with rate 0; LOOK_AT_NEXT_WP is Angle_And_Rate at pos_control's yaw and yaw rate
static void heading(const Input &in, Output &o)
{
    o.cmd_attitude_input_thrust_vector_heading = true;
    if (yaw_look_at_next_wp) {
        o.cmd_attitude_input_thrust_vector_heading_yaw_angle = in.pc_yaw;
        o.cmd_attitude_input_thrust_vector_heading_yaw_rate = in.pc_yaw_rate;
        o.cmd_attitude_input_thrust_vector_heading_heading_mode = 1;
    } else {
        o.cmd_attitude_input_thrust_vector_heading_yaw_angle = in.ac_att_target_yaw;
        o.cmd_attitude_input_thrust_vector_heading_yaw_rate = 0.0f;
        o.cmd_attitude_input_thrust_vector_heading_heading_mode = 2;
    }
}

// _AutoTakeoff::run (takeoff.cpp:115-221), with no_nav_active false (WP_NAVALT_MIN = 0,
// start_m :233-238) and no terrain
static uint32_t auto_takeoff_run(const Input &in, Output &o)
{
    if (!armed || !auto_armed) {
        make_safe_ground_handling(in, o);
        return armed ? ARMED_GROUND : DISARMED;
    }
    o.spool_desired = 2;   // THROTTLE_UNLIMITED
    if (in.spool_state != 3) {
        o.cmd_position_NE_relax_velocity_controller = true;
        o.cmd_position_NE_update_controller = true;
        o.cmd_position_D_relax_controller = true;
        o.cmd_position_D_relax_controller_throttle = 0.0f;
        o.cmd_position_D_update_controller = true;
        o.cmd_attitude_reset_yaw_target_and_rate = true;
        o.cmd_attitude_reset_yaw_target_and_rate_reset_rate = true;
        o.cmd_attitude_reset_rate_controller_I_terms = true;
        o.cmd_attitude_pos_throttle_after_input = false;
        o.cmd_attitude_input_thrust_vector_rate_heading = true;
        o.cmd_attitude_input_thrust_vector_rate_heading_heading_rate = 0.0f;
        o.cmd_attitude_input_thrust_vector_rate_heading_slew_yaw = true;
        return TAKEOFF_SPOOL;
    }
    if (land_complete) {
        // throttle = constrain(get_throttle_in() + G_Dt / TKOFF_SLEW_TIME, 0, 1) (takeoff.cpp:149)
        float throttle = in.ac_throttle_in + G_DT / P.tkoff_slew_time;
        if (throttle < 0.0f) throttle = 0.0f;
        if (throttle > 1.0f) throttle = 1.0f;
        o.cmd_attitude_set_throttle_out = true;
        o.cmd_attitude_set_throttle_out_throttle_in = throttle;
        o.cmd_attitude_set_throttle_out_apply_angle_boost = true;
        o.cmd_attitude_set_throttle_out_filter_cutoff = 0.0f;
        o.cmd_attitude_set_throttle_out_before_input = true;
        o.cmd_position_D_init_controller = true;
        o.cmd_position_NE_relax_velocity_controller = true;
        o.cmd_position_NE_update_controller = true;
        o.cmd_attitude_reset_rate_controller_I_terms = true;
        o.cmd_attitude_input_thrust_vector_rate_heading = true;
        o.cmd_attitude_input_thrust_vector_rate_heading_heading_rate = 0.0f;
        o.cmd_attitude_input_thrust_vector_rate_heading_slew_yaw = true;
        // takeoff.cpp:158-166: the estimated upward acceleration is -(accel_ef.z + g)
        // (AC_PosControl::get_estimated_accel_U_mss), the upward velocity -vel_d
        const float accel_u = -(in.est_accel_ef_z + GRAVITY_MSS);
        const float vel_u = -in.est_vel_d;
        const float thr_max = P.tkoff_thr_max < 0.9f ? P.tkoff_thr_max : 0.9f;
        if (throttle >= thr_max || accel_u >= 0.5f * in.pc_d_max_accel ||
            vel_u >= 0.1f * in.pc_max_speed_up) {
            land_complete = false;   // copter.set_land_complete(false), effective next tick
        }
        return TAKEOFF_GROUND;
    }
    // flying: hold NE, climb to the takeoff altitude
    o.cmd_position_input_vel_accel_NE_m = true;
    o.cmd_position_input_vel_accel_NE_m_limit_output = true;
    o.cmd_position_NE_update_controller = true;
    o.cmd_position_input_pos_vel_accel_D_m = true;
    o.cmd_position_input_pos_vel_accel_D_m_pos = -takeoff_alt_m;
    o.cmd_position_input_pos_vel_accel_D_m_vel = 0.0f;
    o.cmd_position_input_pos_vel_accel_D_m_accel = 0.0f;
    o.cmd_position_input_pos_vel_accel_D_m_limit_output = true;
    o.cmd_position_D_update_controller = true;
    o.cmd_attitude_pos_throttle_after_input = false;
    heading(in, o);
    // completion (takeoff.cpp:202-210), from the previous tick's desired position and velocity
    const float stop_distance_m =
        0.5f * (0.1f * in.pc_max_speed_up) * (0.1f * in.pc_max_speed_up) / in.pc_d_max_accel;
    const bool reached_altitude = -in.pc_pos_desired_d >= takeoff_alt_m - stop_distance_m;
    const bool reached_climb_rate = -in.pc_vel_desired_d < in.pc_max_speed_up * 0.1f;
    if (reached_altitude && reached_climb_rate) {
        takeoff_complete = true;
    }
    return TAKEOFF_CLIMB;
}

// ModeAuto::wp_run (mode_auto.cpp:1134-1152); loiter_run is the same
static void wp_run(const Input &in, Output &o)
{
    o.spool_desired = 2;
    o.cmd_guidance_update_wpnav = true;
    o.cmd_position_D_update_controller = true;
    o.cmd_attitude_pos_throttle_after_input = false;
    heading(in, o);
}

void module_step(const Input &in, Output &o)
{
    memset(&o, 0, sizeof o);
    const uint32_t t_ms = in.t_us / 1000;
    o.dt = G_DT;
    o.now_us = 10000000u + in.t_us;
    o.now_ms = o.now_us / 1000;
    const bool slow_tick = (tick % 8) == 0;   // the 50 Hz tasks

    // arming (AP_Arming_Copter::arm) and the arming delay (motors.cpp:78)
    if (!armed && t_ms >= P.sc_arm_ms) {
        armed = true;
        in_arming_delay = true;
        arm_time_ms = o.now_ms;
    }
    if (in_arming_delay && (o.now_ms - arm_time_ms > 2000)) {
        in_arming_delay = false;
    }

    // mode changes and GCS commands, before this tick's run()
    if (tick == 0) {
        pva_control_start(o);   // set_mode(GUIDED) -> ModeGuided::init
        set_mode_rate_tc(o);
    }
    if (!takeoff_requested && armed && t_ms >= P.sc_takeoff_ms && land_complete) {
        takeoff_requested = true;   // do_user_takeoff_U_m's checks pass (armed, landed)
        takeoff_mode = true;
        yaw_look_at_next_wp = false;   // auto_yaw HOLD
        o.cmd_position_D_init_controller = true;
        takeoff_alt_m = P.sc_takeoff_alt;   // home = origin: above home is above origin
        auto_armed = true;
    }
    bool auto_first_tick = false;
    if (takeoff_complete && !auto_mode) {
        auto_mode = true;   // set_mode(AUTO) -> ModeAuto::init
        auto_first_tick = true;
        o.cmd_guidance_wp_and_spline_init_m = true;
        o.cmd_guidance_wp_and_spline_init_m_speed_ms = 0.0f;
        set_mode_rate_tc(o);
    }

    // update_flight_mode (mode.cpp:513-518)
    o.cmd_position_update_estimates = true;
    o.cmd_attitude_landed_gain_reduction = true;
    o.cmd_attitude_landed_gain_reduction_landed = land_complete;
    o.cmd_position_set_reset_handling_method = true;
    // MoveVehicle only in AUTO's WP submode (mode_auto.cpp:235-260, mode_guided.cpp:137-155)
    o.cmd_position_set_reset_handling_method_method = (auto_mode && !loiter) ? 1 : 0;

    uint32_t phase;
    if (auto_mode) {
        if (auto_first_tick) {
            // mission start -> do_nav_wp -> wp_start: set_wp_destination_loc
            o.cmd_guidance_set_wp_destination_NED_m = true;
            o.cmd_guidance_set_wp_destination_NED_m_destination_n = P.sc_leg_n;
            o.cmd_guidance_set_wp_destination_NED_m_destination_e = P.sc_leg_e;
            o.cmd_guidance_set_wp_destination_NED_m_destination_d = -P.sc_takeoff_alt;
            o.cmd_guidance_set_wp_destination_NED_m_arc_rad = 0.0f;
            yaw_look_at_next_wp = true;   // auto_yaw.set_mode_to_default(false)
            auto_started = true;
        } else if (!loiter && in.wp_reached) {
            // verify_nav_wp -> mission complete -> exit_mission -> loiter_start
            loiter = true;
            o.cmd_guidance_set_wp_destination_NED_m = true;
            o.cmd_guidance_set_wp_destination_NED_m_destination_n = in.pc_stopping_point_n;
            o.cmd_guidance_set_wp_destination_NED_m_destination_e = in.pc_stopping_point_e;
            o.cmd_guidance_set_wp_destination_NED_m_destination_d = in.pc_stopping_point_d;
            o.cmd_guidance_set_wp_destination_NED_m_arc_rad = 0.0f;
            yaw_look_at_next_wp = false;   // auto_yaw HOLD
        }
        wp_run(in, o);
        phase = loiter ? AUTO_LOITER : AUTO_WP;
    } else if (takeoff_mode) {
        phase = auto_takeoff_run(in, o);
    } else {
        make_safe_ground_handling(in, o);
        phase = armed ? ARMED_GROUND : DISARMED;
    }

    // throttle_loop: update_throttle_mix (land_detector.cpp:281-321), 50 Hz
    if (slow_tick) {
        if (!armed || land_complete) {
            o.cmd_attitude_set_throttle_mix_min = true;
        } else {
            const float lim = 0.2617994f;   // LAND_CHECK_LARGE_ANGLE_RAD, 15 degrees
            const bool large_angle_request = in.ac_att_target_roll * in.ac_att_target_roll +
                in.ac_att_target_pitch * in.ac_att_target_pitch > lim * lim;
            const bool large_angle_error = in.ac_thrust_error_angle * 57.29578f > 30.0f;
            const bool descent_not_demanded = -in.pc_vel_desired_d >= 0.0f;
            if (large_angle_request || large_angle_error || descent_not_demanded) {
                o.cmd_attitude_set_throttle_mix_max = true;
                o.cmd_attitude_set_throttle_mix_max_ratio = in.pc_vel_d_control_ratio;
            } else {
                o.cmd_attitude_set_throttle_mix_min = true;
            }
        }
        o.clear_spoolup_block = true;   // takeoff_check: no ESC telemetry, load adequate
    }

    o.armed = armed;
    o.interlock = armed && !in_arming_delay;
    o.sc_phase = phase;
    o.sc_land_complete = land_complete;
    o.sc_auto_armed = auto_armed;
    tick++;
}
