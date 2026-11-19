import px4.modules.px4_fmm.Ports
import px4.modules.px4_common.Common
import px4.modules.px4_pos.Module

/-! # px4_fmm: PX4's flight mode manager and flight tasks

PX4's `flight_mode_manager` module (src/modules/flight_mode_manager) with every flight task of the
px4_sitl build (Auto, Descend, Failsafe, ManualAcceleration(Slow), ManualAltitude(SmoothVel),
ManualPosition, Transition, AltitudeCruise, AutoFollowTarget, Orbit; FlightTasks_generated.cpp is
made by PX4's own generator, a `pygen` line of px4.txt) and the libraries they link (Sticks,
StickYaw, WeatherVane, CollisionPrevention, motion_planning, hysteresis, geo), real and unmodified,
PX4 v1.17.0. It is started with `flight_mode_manager start` and run by its work queue
(nav_and_controllers) on `vehicle_local_position`, at most every 20 ms
(`set_interval_us(20_ms)`, FlightModeManager.cpp:66): with a local position every 400 Hz tick it
runs at every eighth tick or so. One run picks the flight task from vehicle_status.nav_state and
the control mode flags (start_flight_task, :115-264), updates it, and publishes a trajectory
setpoint and vehicle constraints (NaN setpoints when the task fails, :338-372), and a landing
gear setpoint when it changes.

Not ported: follow_target, follow_target_estimator and the gimbal topics (read only by
AutoFollowTarget: the contract excludes nav state 19) and vehicle_attitude, obstacle_distance,
distance_sensor (read only by CollisionPrevention: the contract assumes it off, CP_DIST < 0). The
navigator's latitudes and longitudes (float64) cross the harness as binary32: about 0.4 m of
resolution at 47°, finer near 0°. -/

namespace Px4.Modules.Px4Fmm

open Harness Harness.Contract.Lang Px4.Modules.Px4Common

def piF : Expr := 3.1415927

private def lp (f : String) : String := s!"vehicle_local_position_{f}"
private def ts (f : String) : String := s!"trajectory_setpoint_{f}"
private def sp (w f : String) : String := s!"position_setpoint_triplet_{w}_{f}"

/-- The local position fields the tasks read as numbers (not NaN-checked everywhere). -/
def lpFloats : List String :=
  ["x", "y", "z", "vx", "vy", "vz", "z_deriv", "ax", "ay", "az", "delta_z", "delta_vz",
   "delta_heading", "dist_bottom", "delta_dist_bottom", "ref_alt", "eph", "epv", "evh", "evv"] ++
  arr "delta_xy" 2 ++ arr "delta_vxy" 2

/-- A setpoint's yaw may lie in [-π, 2π]: navigator copies a mission item's yaw into the triplet
unchanged (mission_block.cpp:627, `sp->yaw = item.yaw`), and MAVLink's mission manager stores an
item's param 4 as `wrap_2pi(radians(param4))` (mavlink_mission.cpp:1443), in [0, 2π); navigator's
own headings are `wrap_pi` values. The first statement, [-π, π], was not discharged: a mission
whose waypoints ask for a heading above 180 deg (the staggered formation's rear vehicle, flying
nose-backward south of 180 deg) failed it at its first such waypoint (served session,
px4/fly_gorge.sh). FlightTaskAuto takes the value as a heading target (HeadingSmoothing works on
wrap_pi of the difference), and its output yaw stays in [-π, π] (`setpoint_yaw_in_range`). -/
def twoPiF : Expr := 6.2831855

def setpointInRange (w : String) : Expr :=
  ¬. sp w "valid" ∨. (within (sp w "lat") (-90) 90 ∧. within (sp w "lon") (-180) 180 ∧.
    allOf ((["vx", "vy", "vz", "alt", "loiter_radius", "loiter_orientation", "acceptance_radius",
      "cruising_speed"].map (sp w ·)).map notInf) ∧. nanOr (sp w "yaw") (-piF) twoPiF)

def assumeInputs : List Clause := [
  ⟨"local_position_not_inf", ¬. "vehicle_local_position_updated" ∨.
      allOf ((lpFloats.map lp).map notInf)⟩,
  ⟨"heading_in_range", ¬. "vehicle_local_position_updated" ∨. within (lp "heading") (-piF) piF⟩,
  -- NaN allowed: EKF2 publishes ref_lat/ref_lon NaN until it has a global origin (EKF2.cpp:1603;
  -- found by px4_auto_loop seed 1, where the first statement, without NaN, was not discharged)
  ⟨"reference_in_range", ¬. "vehicle_local_position_updated" ∨.
      (nanOr (lp "ref_lat") (-90) 90 ∧. nanOr (lp "ref_lon") (-180) 180)⟩,
  ⟨"estimator_limits_nonneg", ¬. "vehicle_local_position_updated" ∨.
      allOf (["vxy_max", "vz_max", "hagl_min", "hagl_max_z", "hagl_max_xy"].map fun f =>
        (0 : Expr) ≤. lp f)⟩,
  ⟨"triplet_in_range", ¬. "position_setpoint_triplet_updated" ∨.
      (setpointInRange "previous" ∧. setpointInRange "current" ∧. setpointInRange "next")⟩,
  ⟨"home_in_range", ¬. "home_position_updated" ∨. (within "home_position_lat" (-90) 90 ∧.
      within "home_position_lon" (-180) 180 ∧. allOf (["alt", "x", "y", "z", "yaw"].map fun f =>
        notInf s!"home_position_{f}"))⟩,
  ⟨"sticks_in_range", ¬. "manual_control_setpoint_updated" ∨.
      allOf (["roll", "pitch", "yaw", "throttle"].map fun s =>
        within s!"manual_control_setpoint_{s}" (-1) 1)⟩,
  ⟨"velocity_limits_not_inf", ¬. "velocity_limits_updated" ∨.
      allOf (["horizontal_velocity", "vertical_velocity", "yaw_rate"].map fun f =>
        notInf s!"velocity_limits_{f}")⟩,
  ⟨"lps_not_inf", ¬. "vehicle_local_position_setpoint_updated" ∨.
      allOf (["x", "y", "z", "vx", "vy", "vz", "yaw", "yawspeed"].map fun f =>
        notInf s!"vehicle_local_position_setpoint_{f}")⟩,
  ⟨"takeoff_state_in_range", ¬. "takeoff_status_updated" ∨. "takeoff_status_takeoff_state" ≤. 5⟩,
  ⟨"command_params_not_inf", "vehicle_command_count" =. 0 ∨.
      allOf ((List.range 7).map fun i => notInf s!"vehicle_command_param{i + 1}")⟩,
  ⟨"no_follow_target", ¬. "vehicle_status_updated" ∨. ¬. ("vehicle_status_nav_state" =. 19)⟩,
  ⟨"collision_prevention_off", "CP_DIST" <. 0⟩,
  ⟨"position_not_from_future", ¬. "vehicle_local_position_updated" ∨.
      lp "timestamp" ≤. "t_us"⟩]

def guarantee : List Clause := [
  ⟨"setpoint_not_inf", allOf ((arr (ts "position") 3 ++ arr (ts "velocity") 3 ++
      arr (ts "acceleration") 3 ++ arr (ts "jerk") 3 ++ [ts "yawspeed"]).map notInf)⟩,
  ⟨"setpoint_yaw_in_range", nanOr (ts "yaw") (-piF) piF⟩,
  ⟨"constraints_nonneg", nanOr "vehicle_constraints_speed_up" 0 1000 ∧.
      nanOr "vehicle_constraints_speed_down" 0 1000⟩,
  ⟨"setpoint_stamped", ¬. "trajectory_setpoint_updated" ∨. ts "timestamp" =. "t_us"⟩,
  ⟨"setpoint_answers_position", ¬. "trajectory_setpoint_updated" ∨.
      "vehicle_local_position_updated"⟩,
  ⟨"constraints_with_setpoint", "vehicle_constraints_updated" =. "trajectory_setpoint_updated"⟩,
  ⟨"gear_in_range", (-1 : Expr) ≤. "landing_gear_landing_gear" ∧.
      "landing_gear_landing_gear" ≤. 1⟩,
  ⟨"no_px4_error", "px4_fmm_errors" =. 0⟩]

def contract : Contract where
  assume := Ports.widths ++ Ports.paramRanges ++ assumeInputs
  guarantee := guarantee

/-- The clocks advancing together, from 1 s, by one 400 Hz tick: every message is stamped with
the tick it is published at. (With independently jittered stamps a local position stamped after
the clock is older than the tasks' 500 ms timeout once the unsigned difference wraps,
FlightTask.cpp:129, and every task fails; `position_not_from_future` excludes that.) -/
def clocks : List Hint := [.increasing "t_us" 1000000 2500 2500,
  .increasing (lp "timestamp") 1000000 2500 2500,
      .increasing (lp "timestamp_sample") 1000000 2500 2500,
  .increasing "vehicle_control_mode_timestamp" 1000000 2500 2500,
  .increasing "vehicle_status_timestamp" 1000000 2500 2500,
  .increasing "position_setpoint_triplet_timestamp" 1000000 2500 2500]

/-- A slowly varying valid estimate (within 50 m and 5 m/s), its reference at 0° N 0° E. -/
def estimateHints : List Hint := Px4.Modules.Px4Pos.estimateHints ++ [
  .walk (lp "dist_bottom") 0 50 0.0125]

def estimate : List Clause := [
  ⟨"position_every_tick", "vehicle_local_position_updated" =. tt⟩,
  ⟨"estimate_valid", lp "xy_valid" ∧. lp "z_valid" ∧. lp "v_xy_valid" ∧. lp "v_z_valid" ∧.
      lp "heading_good_for_control" ∧. lp "xy_global" ∧. lp "z_global"⟩,
  ⟨"no_resets", lp "xy_reset_counter" =. 0 ∧. lp "z_reset_counter" =. 0 ∧.
      lp "vxy_reset_counter" =. 0 ∧. lp "vz_reset_counter" =. 0 ∧.
          lp "heading_reset_counter" =. 0⟩,
  ⟨"reference", lp "ref_lat" =. 0 ∧. lp "ref_lon" =. 0 ∧. lp "ref_alt" =. 0⟩,
  ⟨"no_estimator_limits", allOf (["vxy_max", "vz_max", "hagl_min", "hagl_max_z", "hagl_max_xy"].map
      fun f => lp f =. Expr.lit 0x7f800000)⟩,
  ⟨"small_accel", allOf (["ax", "ay", "az", "delta_z", "delta_vz", "delta_heading",
      "delta_dist_bottom", "eph", "epv", "evh", "evv"].map fun f => within (lp f) (-5) 5) ∧.
      allOf ((arr (lp "delta_xy") 2 ++ arr (lp "delta_vxy") 2).map fun f => within f (-5) 5)⟩]

def posctlFlags : Expr :=
  "vehicle_control_mode_flag_armed" ∧. "vehicle_control_mode_flag_control_manual_enabled" ∧.
  "vehicle_control_mode_flag_control_position_enabled" ∧.
  "vehicle_control_mode_flag_control_velocity_enabled" ∧.
  "vehicle_control_mode_flag_control_altitude_enabled" ∧.
  "vehicle_control_mode_flag_control_climb_rate_enabled" ∧.
  "vehicle_control_mode_flag_control_attitude_enabled" ∧.
  "vehicle_control_mode_flag_control_rates_enabled" ∧.
  "vehicle_control_mode_flag_control_allocation_enabled" ∧.
  "vehicle_control_mode_flag_multicopter_position_control_enabled" ∧.
  ¬. "vehicle_control_mode_flag_control_auto_enabled" ∧.
  ¬. "vehicle_control_mode_flag_control_offboard_enabled" ∧.
  ¬. "vehicle_control_mode_flag_control_acceleration_enabled" ∧.
  ¬. "vehicle_control_mode_flag_control_termination_enabled"

/-- Commander's flags for the auto modes (control_mode.cpp:86-101). -/
def autoFlags : Expr :=
  "vehicle_control_mode_flag_armed" ∧. ¬. "vehicle_control_mode_flag_control_manual_enabled" ∧.
  "vehicle_control_mode_flag_control_auto_enabled" ∧.
  "vehicle_control_mode_flag_control_position_enabled" ∧.
  "vehicle_control_mode_flag_control_velocity_enabled" ∧.
  "vehicle_control_mode_flag_control_altitude_enabled" ∧.
  "vehicle_control_mode_flag_control_climb_rate_enabled" ∧.
  "vehicle_control_mode_flag_control_attitude_enabled" ∧.
  "vehicle_control_mode_flag_control_rates_enabled" ∧.
  "vehicle_control_mode_flag_control_allocation_enabled" ∧.
  "vehicle_control_mode_flag_multicopter_position_control_enabled" ∧.
  ¬. "vehicle_control_mode_flag_control_offboard_enabled" ∧.
  ¬. "vehicle_control_mode_flag_control_acceleration_enabled" ∧.
  ¬. "vehicle_control_mode_flag_control_termination_enabled"

def statusArmed (nav : Expr) : Expr :=
  "vehicle_status_updated" ∧. "vehicle_status_vehicle_type" =. 1 ∧.
  "vehicle_status_arming_state" =. 2 ∧. "vehicle_status_nav_state" =. nav ∧.
  ¬. "vehicle_status_is_vtol" ∧. ¬. "vehicle_status_in_transition_mode"

/-- Inputs every regime keeps quiet or in range: no commands, no velocity limits, sticks in
range, airborne, takeoff done. -/
def quiet : List Clause := [
  ⟨"no_command", "vehicle_command_count" =. 0⟩,
  ⟨"no_velocity_limits", ¬. "velocity_limits_updated"⟩,
  ⟨"stick_ranges", allOf (["roll", "pitch", "yaw", "throttle"].map fun s =>
      within s!"manual_control_setpoint_{s}" (-1) 1)⟩,
  ⟨"airborne", "vehicle_land_detected_updated" ∧. ¬. "vehicle_land_detected_landed" ∧.
      ¬. "vehicle_land_detected_maybe_landed" ∧. ¬. "vehicle_land_detected_ground_contact"⟩,
  ⟨"flying", "takeoff_status_updated" ∧. "takeoff_status_takeoff_state" =. 5⟩]

/-- A loiter setpoint of the navigator near the reference (within about 55 m), at 0-50 m. -/
def loiterTriplet : List Clause := [
  ⟨"triplet_every_tick", "position_setpoint_triplet_updated" =. tt⟩,
  ⟨"current_loiter", sp "current" "valid" ∧. sp "current" "type" =. 2 ∧.
      within (sp "current" "lat") (-0.0005) 0.0005 ∧.
          within (sp "current" "lon") (-0.0005) 0.0005 ∧.
      within (sp "current" "alt") 0 50 ∧. nanOr (sp "current" "yaw") (-3) 3 ∧.
      within (sp "current" "acceptance_radius") 0.5 5 ∧. isNaN (sp "current" "cruising_speed") ∧.
      allOf (["vx", "vy", "vz", "loiter_radius", "loiter_orientation"].map fun f =>
        within (sp "current" f) (-1) 1)⟩,
  ⟨"no_previous_next", ¬. sp "previous" "valid" ∧. ¬. sp "next" "valid"⟩]

/-- Armed in Auto Loiter (nav state 4) with a valid estimate and the navigator's loiter setpoint,
any parameters. -/
def loiter : Regime where
  name := "loiter"
  doc := "armed in Auto Loiter, flying, a loiter setpoint and a valid estimate every tick"
  clauses := estimate ++ quiet ++ loiterTriplet ++ [
    ⟨"auto_flags", "vehicle_control_mode_updated" ∧. autoFlags⟩,
    ⟨"loiter_status", statusArmed 4⟩]
  hints := clocks ++ estimateHints

/-- Armed in Position mode (nav state 2), sticks within range, any parameters. -/
def posctl : Regime where
  name := "posctl"
  doc := "armed in Position mode, flying, sticks in range, a valid estimate every tick"
  clauses := estimate ++ quiet ++ [
    ⟨"manual_valid", "manual_control_setpoint_updated" ∧. "manual_control_setpoint_valid"⟩,
    ⟨"posctl_flags", "vehicle_control_mode_updated" ∧. posctlFlags⟩,
    ⟨"posctl_status", statusArmed 2⟩]
  hints := clocks ++ estimateHints

/-- PX4's defaults (with the X500's MPC_THR_HOVER 0.6) in Auto Loiter. -/
def x500Loiter : Regime where
  name := "x500_loiter"
  doc := "X500 parameters, armed in Auto Loiter at a loiter setpoint"
  clauses := (Ports.paramDefaults.filter (·.name != "default_MPC_THR_HOVER")) ++
    [⟨"x500_MPC_THR_HOVER", "MPC_THR_HOVER" =. 0.6⟩] ++ loiter.clauses
  hints := loiter.hints

def coverage : List Clause := [
  ⟨"setpoint_published", "trajectory_setpoint_updated" =. tt⟩,
  ⟨"position_setpoint", "trajectory_setpoint_updated" ∧. finite (ts "position_0")⟩,
  ⟨"velocity_setpoint", "trajectory_setpoint_updated" ∧. finite (ts "velocity_0")⟩,
  ⟨"all_nan_setpoint", "trajectory_setpoint_updated" ∧. isNaN (ts "position_2") ∧.
      isNaN (ts "velocity_2") ∧. isNaN (ts "acceleration_2")⟩]

def module : Module where
  name := "px4_fmm"
  doc := "PX4 flight_mode_manager and flight tasks (v1.17.0), unmodified, generic shim"
  params := Ports.params
  input := Ports.input
  output := Ports.output
  contract := { contract with guarantee := contract.guarantee ++ Ports.outWidths }
  exe := "build/modules/px4_fmm/px4_fmm"
  stack := .px4
  regimes := [loiter, posctl, x500Loiter]
  coverage := coverage

end Px4.Modules.Px4Fmm
