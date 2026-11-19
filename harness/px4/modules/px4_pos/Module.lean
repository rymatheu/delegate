import px4.modules.px4_pos.Ports
import px4.modules.px4_common.Common

/-! # px4_pos: PX4's multicopter position controller

PX4's `mc_pos_control` module (src/modules/mc_pos_control with its PositionControl, GotoControl
and Takeoff libraries, src/lib/hysteresis and src/lib/motion_planning headers), real and
unmodified, PX4 v1.17.0, started with `mc_pos_control start` and run by its work queue
(nav_and_controllers) whenever `vehicle_local_position` is published (SubscriptionCallbackWork-
Item, MulticopterPositionControl.hpp:102; a backup ScheduleDelayed(100 ms) also runs it, which does
nothing without a new local position). One step publishes the inputs whose flag is set; the
module then runs once: with multicopter position control enabled and a trajectory setpoint newer
than the enabling, it runs the takeoff state machine and the PID position/velocity controller
(with a fallback and a failsafe setpoint when the setpoint is invalid) and publishes an attitude
setpoint and a local position setpoint; it publishes takeoff_status when the state or the tilt
limit changes.

The module writes parameters (MulticopterPositionControl.cpp:121-247): with SYS_VEHICLE_RESP ≥ 0,
MPC_XY_VEL_ALL ≥ 0 or MPC_Z_VEL_ALL ≥ 0 it commits derived MPC_ACC_*, MPC_JERK_*, MPC_MAN_Y_*,
MPC_TILTMAX_AIR, velocity limits, MPC_TKO_SPEED and MPC_LAND_SPEED, and it clamps MPC_TILTMAX_LND,
MPC_XY_CRUISE, MPC_VEL_MAN*, MPC_Z_V_AUTO_* and MPC_THR_HOVER to other parameters. On the vehicle
the other modules see these values; here they stay in this module's parameter store
(`paramsNotRewritten` states when nothing is rewritten).

Contract, from the code (MulticopterPositionControl.cpp:376-623, PositionControl.cpp,
ControlMath.cpp): the attitude setpoint is a unit quaternion built from the thrust direction
and a finite yaw (bodyzToAttitude), its thrust is `-|thr_sp|` along body z (thrustToAttitude),
|thr_sp| at most MPC_THR_MAX by the saturation in `_velocityControl`; the yaw feed-forward is
finite or NaN; the setpoints are stamped with the clock and answer a local position. -/

namespace Px4.Modules.Px4Pos

open Harness Harness.Contract.Lang Px4.Modules.Px4Common

def piF : Expr := 3.1415927

private def lp (f : String) : String := s!"vehicle_local_position_{f}"
private def ts (f : String) : String := s!"trajectory_setpoint_{f}"
private def att (f : String) : String := s!"vehicle_attitude_setpoint_{f}"

/-- What the code reads, in the ranges the .msg files document (NaN: not set / not valid). -/
def assumeInputs : List Clause := [
  ⟨"local_position_not_inf", ¬. "vehicle_local_position_updated" ∨. allOf
      ((["x", "y", "z", "vx", "vy", "vz", "z_deriv", "delta_z", "delta_vz", "delta_heading"] ++
        arr "delta_xy" 2 ++ arr "delta_vxy" 2).map fun f => notInf (lp f))⟩,
  ⟨"heading_in_range", ¬. "vehicle_local_position_updated" ∨. within (lp "heading") (-piF) piF⟩,
  ⟨"vxy_max_nonneg", ¬. "vehicle_local_position_updated" ∨. (0 : Expr) ≤. lp "vxy_max"⟩,
  ⟨"setpoint_not_inf", ¬. "trajectory_setpoint_updated" ∨. allOf
      ((arr (ts "position") 3 ++ arr (ts "velocity") 3 ++ arr (ts "acceleration") 3 ++
        [ts "yawspeed"]).map notInf)⟩,
  ⟨"setpoint_yaw_in_range", ¬. "trajectory_setpoint_updated" ∨. nanOr (ts "yaw") (-piF) piF⟩,
  ⟨"constraints_nonneg", ¬. "vehicle_constraints_updated" ∨.
      (nanOr "vehicle_constraints_speed_up" 0 1000 ∧.
          nanOr "vehicle_constraints_speed_down" 0 1000)⟩,
  ⟨"hover_thrust_in_range", ¬. "hover_thrust_estimate_updated" ∨.
      ¬. "hover_thrust_estimate_valid" ∨.
      within "hover_thrust_estimate_hover_thrust" 0.1 0.9⟩,
  ⟨"goto_finite", ¬. "goto_setpoint_updated" ∨. (allOf ((arr "goto_setpoint_position" 3).map
      fun f => Expr.finite (Expr.var f)) ∧. within "goto_setpoint_heading" (-piF) piF ∧.
      within "goto_setpoint_max_horizontal_speed" 0 1000 ∧.
      within "goto_setpoint_max_vertical_speed" 0 1000 ∧.
      within "goto_setpoint_max_heading_rate" 0 1000)⟩]

/-- The parameter sets for which the module rewrites none of its parameters
(MulticopterPositionControl.cpp:121-247), so that every module sees the same values. -/
def paramsNotRewritten : List Clause := [
  ⟨"no_derived_params", "SYS_VEHICLE_RESP" <. 0 ∧. "MPC_XY_VEL_ALL" <. 0 ∧. "MPC_Z_VEL_ALL" <. 0⟩,
  ⟨"params_consistent", "MPC_TILTMAX_LND" ≤. "MPC_TILTMAX_AIR" ∧.
      "MPC_XY_CRUISE" ≤. "MPC_XY_VEL_MAX" ∧.
      "MPC_VEL_MANUAL" ≤. "MPC_XY_VEL_MAX" ∧. "MPC_VEL_MAN_BACK" ≤. "MPC_VEL_MANUAL" ∧.
      "MPC_VEL_MAN_SIDE" ≤. "MPC_VEL_MANUAL" ∧. "MPC_Z_V_AUTO_UP" ≤. "MPC_Z_VEL_MAX_UP" ∧.
      "MPC_Z_V_AUTO_DN" ≤. "MPC_Z_VEL_MAX_DN" ∧. "MPC_THR_MIN" ≤. "MPC_THR_HOVER" ∧.
      "MPC_THR_HOVER" ≤. "MPC_THR_MAX"⟩]

/-- The thrust bound as first stated, |thrust| ≤ MPC_THR_MAX exactly. Refuted (flight regime,
seed 3, 110 of 10000 steps, case 0 step 26: thrust 3.7e-9 beyond MPC_THR_MAX): the saturation in
`_velocityControl` (PositionControl.cpp:171-186) bounds z by `sqrtf(MPC_THR_MAX² - …)` and xy by
`sqrtf(MPC_THR_MAX² - z²)`, each rounded, and `thrustToAttitude` takes the rounded length of the
result, which can exceed MPC_THR_MAX by an ulp. The clause in `guarantee` allows a relative
1e-6 and an absolute 1e-19 (below 1.1e-19 the squares are subnormal and lose their precision:
seed 3, case 16, MPC_THR_MAX = 6.0e-23, thrust 6.5e-23). -/
def thrustMaxAsFirstStated : Clause :=
  ⟨"att_sp_thrust_max", ¬. "vehicle_attitude_setpoint_updated" ∨.
      Expr.neg (Expr.var "MPC_THR_MAX") ≤. att "thrust_body_2"⟩

def guarantee : List Clause := [
  ⟨"att_sp_unit", ¬. "vehicle_attitude_setpoint_updated" ∨. unitArr (att "q_d") 4⟩,
  ⟨"att_sp_thrust_along_z", ¬. "vehicle_attitude_setpoint_updated" ∨.
      (att "thrust_body_0" =. 0 ∧. att "thrust_body_1" =. 0 ∧. att "thrust_body_2" ≤. 0)⟩,
  ⟨"att_sp_thrust_normalized", ¬. "vehicle_attitude_setpoint_updated" ∨.
      within (att "thrust_body_2") (-1) 0⟩,
  ⟨"att_sp_thrust_max", ¬. "vehicle_attitude_setpoint_updated" ∨.
      Expr.neg (Expr.var "MPC_THR_MAX" * 1.000001 + 1e-19) ≤. att "thrust_body_2"⟩,
  ⟨"att_sp_yawrate_not_inf", ¬. "vehicle_attitude_setpoint_updated" ∨.
      notInf (att "yaw_sp_move_rate")⟩,
  ⟨"att_sp_stamped", ¬. "vehicle_attitude_setpoint_updated" ∨. att "timestamp" =. "t_us"⟩,
  ⟨"att_sp_answers_position", ¬. "vehicle_attitude_setpoint_updated" ∨.
      "vehicle_local_position_updated"⟩,
  ⟨"lps_not_inf", allOf (["x", "y", "z", "vx", "vy", "vz", "yaw", "yawspeed"].map fun f =>
      notInf s!"vehicle_local_position_setpoint_{f}")⟩,
  ⟨"takeoff_state_in_range", "takeoff_status_takeoff_state" ≤. 5⟩,
  ⟨"tilt_limit_in_range", within "takeoff_status_tilt_limit" 0 (89 * degToRad)⟩,
  ⟨"no_px4_error", "px4_pos_errors" =. 0⟩]

/-- The first statement: the documented parameter ranges and input ranges only. Refuted at the
first step of cases drawn with MPC_THR_MAX below the horizontal thrust margin MPC_THR_XY_MARG
(flight regime, seed 1, 2168 of 10000 steps; case 0: MPC_THR_MAX = 0): `_velocityControl`
computes `thrust_z_max_squared = MPC_THR_MAX² - min(|thr_xy|, MPC_THR_XY_MARG)²`, negative, and
`sqrtf` of it (PositionControl.cpp:166-170) is NaN; the thrust setpoint becomes NaN, the update,
its fallback and the failsafe all fail, and the module publishes an attitude setpoint with a NaN
quaternion and thrust. Both parameters are within their documented ranges ([0, 1] and
[0, 0.5]); nothing in PX4 relates them. Kept for the record. -/
def contractAsFirstStated : Contract where
  assume := Ports.widths ++ Ports.paramRanges ++ assumeInputs
  guarantee := guarantee

/-- The second statement, refuted (flight regime, seed 3, case 91, step 2): with MPC_VEL_NF_FRQ
> 0 and MPC_VEL_NF_BW near its documented maximum of 50 Hz, the velocity notch filter is designed
for 100 Hz (`_sample_interval_s` starts at 0.01 s and the filter is set up only when parameters
change, MulticopterPositionControl.cpp:49, 84-91), so `tanf(π·BW/fs)` (NotchFilter.hpp:271) is
taken at π/2: the coefficients are finite, so NotchFilter's check passes, but the filtered
velocity is not, the velocity and acceleration states are NaN, the setpoint and the failsafe
setpoint both fail `_inputValid`, and the module publishes an attitude setpoint whose quaternion
and yaw rate are NaN (getAttitudeSetpoint runs whether or not the last update succeeded,
:608-612, and the failsafe setpoint's yaw is NaN). The same case with BW 49.9 publishes finite
setpoints. NotchFilter::setParameters rejects a notch frequency ≥ fs/2 but not a bandwidth. -/
def contractSecond : Contract where
  assume := Ports.widths ++ Ports.paramRanges ++ assumeInputs ++ [
    ⟨"thrust_margin_fits", "MPC_THR_XY_MARG" ≤. "MPC_THR_MAX"⟩]
  guarantee := guarantee.map fun c => if c.name == "att_sp_thrust_max" then thrustMaxAsFirstStated
    else c

/-- The contract: the thrust limits leave room for the horizontal margin, the velocity notch
bandwidth stays below half of the 100 Hz the filter is designed for, and the horizontal position
gain is 0 or not so small that its products with position errors underflow.

`lps_not_inf` (added when composing: px4_fmm assumes it of vehicle_local_position_setpoint) was
refuted under the second assumption in seeds 1-3 (flight) and 1-2 (thrust_saturation), every
counterexample with MPC_XY_P ≈ 1.18e-38 (within its documented [0, 2]): the position-error
velocity `vel_sp_position` is then about 1e-36 m/s, its squared norm underflows to 0, and
ControlMath::constrainXY normalizes it (`v0.normalized() * max`, ControlMath.cpp:124-128): the
published velocity setpoint is ±∞ (the attitude setpoint stays finite: the velocity controller's
input check fails and the failsafe setpoint is used). -/
def contract : Contract where
  assume := Ports.widths ++ Ports.paramRanges ++ assumeInputs ++ [
    ⟨"thrust_margin_fits", "MPC_THR_XY_MARG" ≤. "MPC_THR_MAX"⟩,
    ⟨"notch_below_nyquist", "MPC_VEL_NF_BW" ≤. 49⟩,
    ⟨"xy_gain_not_tiny", "MPC_XY_P" =. 0 ∨. (0.01 : Expr) ≤. "MPC_XY_P"⟩]
  guarantee := guarantee

/-- The clock and the estimator's and setpoint generator's clocks advancing together. -/
def clocks : List Hint := [.increasing "t_us" 1000000 2500 2500,
  .increasing (lp "timestamp") 1000000 2500 2500,
  .increasing (lp "timestamp_sample") 1000000 2500 2500,
  .increasing "trajectory_setpoint_timestamp" 1000000 2500 2500,
  .increasing "vehicle_control_mode_timestamp" 1000000 2500 2500]

/-- A slowly varying, valid local position estimate (within 50 m, 5 m/s), heading near 0. -/
def estimateHints : List Hint := [
  .walk (lp "x") (-50) 50 0.0125, .walk (lp "y") (-50) 50 0.0125, .walk (lp "z") (-50) 0 0.0125,
  .walk (lp "vx") (-5) 5 0.01, .walk (lp "vy") (-5) 5 0.01, .walk (lp "vz") (-5) 5 0.01,
  .walk (lp "z_deriv") (-5) 5 0.01, .walk (lp "heading") (-3.1) 3.1 0.002]

def estimateValid : List Clause := [
  ⟨"position_every_tick", "vehicle_local_position_updated" =. tt⟩,
  ⟨"estimate_valid", lp "xy_valid" ∧. lp "z_valid" ∧. lp "v_xy_valid" ∧. lp "v_z_valid" ∧.
      lp "heading_good_for_control"⟩,
  ⟨"no_resets", lp "xy_reset_counter" =. 0 ∧. lp "z_reset_counter" =. 0 ∧.
      lp "vxy_reset_counter" =. 0 ∧. lp "vz_reset_counter" =. 0 ∧.
          lp "heading_reset_counter" =. 0⟩,
  ⟨"no_estimator_limit", lp "vxy_max" =. Expr.lit 0x7f800000⟩]

/-- In flight, any parameters: a valid estimate every tick, multicopter position control on and
armed, takeoff skipped (COM_THROW_EN), not landed, trajectory setpoints within 50 m, 5 m/s and
5 m/s² (each component finite or NaN). -/
def flight : Regime where
  name := "pos_flight"
  doc := "armed, position control on, takeoff skipped, a valid estimate and a setpoint every tick"
  clauses := estimateValid ++ [
    ⟨"skip_takeoff", "COM_THROW_EN" =. 1⟩,
    ⟨"position_control", "vehicle_control_mode_updated" ∧.
      "vehicle_control_mode_flag_multicopter_position_control_enabled" ∧.
      "vehicle_control_mode_flag_armed"⟩,
    ⟨"airborne", ¬. "vehicle_land_detected_landed" ∧. ¬. "vehicle_land_detected_ground_contact"⟩,
    ⟨"setpoint_every_tick", "trajectory_setpoint_updated" =. tt⟩,
    ⟨"setpoint_ranges", allOf ((arr (ts "position") 3).map fun f => nanOr f (-50) 50) ∧.
      allOf ((arr (ts "velocity") 3 ++ arr (ts "acceleration") 3).map fun f => nanOr f (-5) 5) ∧.
      nanOr (ts "yaw") (-3) 3 ∧. nanOr (ts "yawspeed") (-1) 1⟩,
    ⟨"hover_estimate_range", within "hover_thrust_estimate_hover_thrust" 0.1 0.9⟩,
    ⟨"constraint_ranges", nanOr "vehicle_constraints_speed_up" 0 5 ∧.
      nanOr "vehicle_constraints_speed_down" 0 5⟩,
    ⟨"no_goto", ¬. "goto_setpoint_updated"⟩]
  hints := clocks ++ estimateHints

/-- The X500's parameters in PX4's SITL (4001_gz_x500): PX4's defaults, MPC_THR_HOVER 0.6. -/
def x500Params : List Clause :=
  (Ports.paramDefaults.filter (·.name != "default_MPC_THR_HOVER")) ++
    [⟨"x500_MPC_THR_HOVER", "MPC_THR_HOVER" =. 0.6⟩]

/-- The X500 armed in Position mode (commander's POSCTL flags, control_mode.cpp:76-85), holding a
position setpoint near the estimate (velocity and acceleration not set), the flight task asking
for takeoff; spool-up (1 s) and the takeoff ramp (3 s) run from the first tick. -/
def x500Posctl : Regime where
  name := "x500_posctl"
  doc := "X500 parameters, armed in Position mode, a position setpoint, takeoff wanted"
  clauses := x500Params ++ estimateValid ++ [
    ⟨"posctl_flags", "vehicle_control_mode_updated" ∧. "vehicle_control_mode_flag_armed" ∧.
      "vehicle_control_mode_flag_control_manual_enabled" ∧.
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
      ¬. "vehicle_control_mode_flag_control_termination_enabled"⟩,
    ⟨"airborne", "vehicle_land_detected_updated" ∧. ¬. "vehicle_land_detected_landed" ∧.
      ¬. "vehicle_land_detected_ground_contact" ∧. ¬. "vehicle_land_detected_maybe_landed"⟩,
    ⟨"setpoint_every_tick", "trajectory_setpoint_updated" =. tt⟩,
    ⟨"position_hold", allOf ((arr (ts "velocity") 3 ++ arr (ts "acceleration") 3 ++
      [ts "yawspeed"]).map isNaN)⟩,
    ⟨"takeoff_wanted", "vehicle_constraints_updated" ∧. "vehicle_constraints_want_takeoff" ∧.
      isNaN "vehicle_constraints_speed_up" ∧. isNaN "vehicle_constraints_speed_down"⟩,
    ⟨"no_hover_estimate", ¬. "hover_thrust_estimate_updated"⟩,
    ⟨"no_goto", ¬. "goto_setpoint_updated"⟩]
  hints := clocks ++ estimateHints ++ [
    .walk (ts "position_0") (-50) 50 0.0125, .walk (ts "position_1") (-50) 50 0.0125,
    .walk (ts "position_2") (-50) 0 0.0125, .walk (ts "yaw") (-3.1) 3.1 0.002]

/-- The flight regime with MPC_THR_MAX = 1 (its default) and the horizontal margin at its
maximum, so that the thrust saturates at the normalized limit the attitude controller assumes. -/
def thrustSaturation : Regime where
  name := "thrust_saturation"
  doc := "the flight regime with MPC_THR_MAX = 1, saturating setpoints"
  clauses := flight.clauses ++ [⟨"full_thrust_range", "MPC_THR_MAX" =. 1⟩,
    ⟨"far_setpoints", allOf ((arr (ts "acceleration") 3).map fun f => within f (-5) 5)⟩]
  hints := flight.hints

def coverage : List Clause := [
  ⟨"att_sp_published", "vehicle_attitude_setpoint_updated" =. tt⟩,
  ⟨"flight_state", "takeoff_status_takeoff_state" =. 5⟩,
  ⟨"rampup_state", "takeoff_status_takeoff_state" =. 4⟩,
  ⟨"thrust_at_max", "vehicle_attitude_setpoint_updated" ∧.
      att "thrust_body_2" =. Expr.neg (Expr.var "MPC_THR_MAX")⟩,
  ⟨"thrust_between", "vehicle_attitude_setpoint_updated" ∧.
      Expr.neg (Expr.var "MPC_THR_MAX") <. att "thrust_body_2" ∧.
      att "thrust_body_2" <. Expr.neg (Expr.var "MPC_THR_MIN")⟩]

def module : Module where
  name := "px4_pos"
  doc := "PX4 mc_pos_control (v1.17.0), unmodified, behind the generic uORB shim"
  params := Ports.params
  input := Ports.input
  output := Ports.output
  contract := { contract with guarantee := contract.guarantee ++ Ports.outWidths }
  exe := "build/modules/px4_pos/px4_pos"
  stack := .px4
  regimes := [flight, x500Posctl, thrustSaturation]
  coverage := coverage

end Px4.Modules.Px4Pos
