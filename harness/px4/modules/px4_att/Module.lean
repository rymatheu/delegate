import px4.modules.px4_att.Ports
import px4.modules.px4_common.Common

/-! # px4_att: PX4's multicopter attitude controller

PX4's `mc_att_control` module (src/modules/mc_att_control with its AttitudeControl library and
src/lib/stick_yaw), real and unmodified, PX4 v1.17.0, started with `mc_att_control start` and
run by its work queue (nav_and_controllers) whenever `vehicle_attitude` is published
(SubscriptionCallbackWorkItem, mc_att_control.hpp:109). One step publishes the attitude estimate
if `vehicle_attitude_updated` (and the other topics whose flag is set); the module then runs
once: it reads the latest control mode, status, land detector, local position and setpoint, and
publishes a rate setpoint when attitude control is enabled for a hovering rotary wing.

Contract, from the code (mc_att_control_main.cpp:233-425, AttitudeControl.cpp:56-113):
* the rate setpoint is limited per axis to `math::radians(MC_xRATE_MAX)` (AttitudeControl.cpp:
  108-110) and finite when the attitude and the setpoint quaternions are unit quaternions and the
  yaw feed-forward is finite or NaN (NaN: no feed-forward, `std::isfinite` at :102);
* its thrust is the latest accepted attitude setpoint's thrust (`_thrust_setpoint_body`, :327),
  or in Manual/Stabilized the throttle curve (:136-161), within [-1, 1] when the setpoints'
  thrust is (vehicle_attitude_setpoint.msg documents [-1, 1]);
* it is stamped with the clock and answers an attitude message; it never asks for an integrator
  reset.
Autotune's rate injection (:363-372) adds to the limited rate setpoint, so the assumption excludes
autotune's excitation states (MC_AT_EN is 0 in PX4's defaults; in SITL autotune runs idle). -/

namespace Px4.Modules.Px4Att

open Harness Harness.Contract.Lang Px4.Modules.Px4Common

/-- What the code needs of its inputs. -/
def assumeInputs : List Clause := [
  ⟨"attitude_unit", ¬. "vehicle_attitude_updated" ∨. unitArr "vehicle_attitude_q" 4⟩,
  ⟨"reset_delta_unit", ¬. "vehicle_attitude_updated" ∨.
      unitArr "vehicle_attitude_delta_q_reset" 4⟩,
  ⟨"setpoint_unit", ¬. "vehicle_attitude_setpoint_updated" ∨.
      unitArr "vehicle_attitude_setpoint_q_d" 4⟩,
  ⟨"setpoint_thrust_normalized", ¬. "vehicle_attitude_setpoint_updated" ∨.
      allOf ((arr "vehicle_attitude_setpoint_thrust_body" 3).map fun f => within f (-1) 1)⟩,
  ⟨"setpoint_yawrate_not_inf", ¬. "vehicle_attitude_setpoint_updated" ∨.
      notInf "vehicle_attitude_setpoint_yaw_sp_move_rate"⟩,
  ⟨"sticks_in_range", ¬. "manual_control_setpoint_updated" ∨.
      allOf (["roll", "pitch", "yaw", "throttle"].map fun s =>
        within s!"manual_control_setpoint_{s}" (-1) 1)⟩,
  ⟨"unaided_heading_not_inf", ¬. "vehicle_local_position_updated" ∨.
      notInf "vehicle_local_position_unaided_heading"⟩,
  ⟨"hover_thrust_in_range", ¬. "hover_thrust_estimate_updated" ∨.
      ¬. "hover_thrust_estimate_valid" ∨.
      within "hover_thrust_estimate_hover_thrust" 0.1 0.9⟩,
  ⟨"autotune_not_exciting", ¬. "autotune_attitude_control_status_updated" ∨.
      allOf ([3, 6, 9, 13].map fun (s : Nat) =>
        ¬. ("autotune_attitude_control_status_state" =. Expr.lit (Float32.ofNat s).toBits))⟩]

def rateLimit (axis param : String) : Expr :=
  absLe s!"vehicle_rates_setpoint_{axis}" (Expr.var param * degToRad)

def guarantee : List Clause := [
  ⟨"rates_finite", finite "vehicle_rates_setpoint_roll" ∧. finite "vehicle_rates_setpoint_pitch" ∧.
      finite "vehicle_rates_setpoint_yaw"⟩,
  ⟨"rates_limited", rateLimit "roll" "MC_ROLLRATE_MAX" ∧. rateLimit "pitch" "MC_PITCHRATE_MAX" ∧.
      rateLimit "yaw" "MC_YAWRATE_MAX"⟩,
  ⟨"thrust_normalized", allOf ((arr "vehicle_rates_setpoint_thrust_body" 3).map fun f =>
      within f (-1) 1)⟩,
  ⟨"rates_stamped", ¬. "vehicle_rates_setpoint_updated" ∨.
      "vehicle_rates_setpoint_timestamp" =. "t_us"⟩,
  ⟨"rates_answer_attitude", ¬. "vehicle_rates_setpoint_updated" ∨. "vehicle_attitude_updated"⟩,
  ⟨"no_integral_reset", ¬. "vehicle_rates_setpoint_reset_integral"⟩,
  ⟨"no_px4_error", "px4_att_errors" =. 0⟩]

def contract : Contract where
  assume := Ports.widths ++ Ports.paramRanges ++ assumeInputs
  guarantee := guarantee

/-- The attitude estimate every 400 Hz tick, a slowly turning unit quaternion (any attitude),
with a reset delta that is a unit quaternion near identity. -/
def attitudeHints : List Hint := [
  .increasing "t_us" 1000000 2500 2500,
  .unit (arr "vehicle_attitude_q" 4) [0, 0, 0, 0] [1, 1, 1, 1] [0.01, 0.01, 0.01, 0.01],
  .unit (arr "vehicle_attitude_delta_q_reset" 4) [1, 0, 0, 0] [0, 0.1, 0.1, 0.5]
    [0, 0.01, 0.01, 0.01]]

/-- Per-field ranges within the assumption's (the sampler satisfies a clause over one field by
construction, one over several fields by rejection): normalized setpoint thrust and sticks, a
finite yaw feed-forward and unaided heading, a hover thrust estimate in range, autotune idle. -/
def inputRanges : List Clause := [
  ⟨"thrust_ranges", allOf ((arr "vehicle_attitude_setpoint_thrust_body" 3).map fun f =>
      within f (-1) 1)⟩,
  ⟨"yawrate_range", within "vehicle_attitude_setpoint_yaw_sp_move_rate" (-4) 4⟩,
  ⟨"stick_ranges", allOf (["roll", "pitch", "yaw", "throttle"].map fun s =>
      within s!"manual_control_setpoint_{s}" (-1) 1)⟩,
  ⟨"unaided_heading_range", within "vehicle_local_position_unaided_heading" (-3.2) 3.2⟩,
  ⟨"hover_thrust_range", within "hover_thrust_estimate_hover_thrust" 0.1 0.9⟩,
  ⟨"autotune_idle", "autotune_attitude_control_status_state" =. 0⟩]

/-- In flight: an attitude message every tick, attitude control enabled and armed, a rotary
wing outside a VTOL transition, an attitude setpoint (unit quaternion) every tick. -/
def flight : Regime where
  name := "att_flight"
  doc := "armed, attitude control on, attitude and attitude setpoint every 400 Hz tick"
  clauses := inputRanges ++ [
    ⟨"attitude_every_tick", "vehicle_attitude_updated" =. tt⟩,
    ⟨"setpoint_every_tick", "vehicle_attitude_setpoint_updated" =. tt⟩,
    ⟨"attitude_enabled", ¬. "vehicle_control_mode_updated" ∨.
      ("vehicle_control_mode_flag_control_attitude_enabled" ∧. "vehicle_control_mode_flag_armed")⟩,
    ⟨"rotary_wing", ¬. "vehicle_status_updated" ∨.
      ("vehicle_status_vehicle_type" =. 1 ∧. ¬. "vehicle_status_in_transition_mode")⟩]
  hints := attitudeHints ++ [.increasing "vehicle_attitude_setpoint_timestamp" 1000000 2500 2500,
    .unit (arr "vehicle_attitude_setpoint_q_d" 4) [0, 0, 0, 0] [1, 1, 1, 1] [0.01, 0.01, 0.01,
        0.01]]

/-- The parameters of the X500 in PX4's SITL (4001_gz_x500): PX4's defaults, MPC_THR_HOVER 0.6. -/
def x500Params : List Clause :=
  (Ports.paramDefaults.filter (·.name != "default_MPC_THR_HOVER")) ++
    [⟨"x500_MPC_THR_HOVER", "MPC_THR_HOVER" =. 0.6⟩]

/-- The X500 hovering in Position mode: commander's flags for POSCTL (control_mode.cpp:76-85),
armed, a near-level attitude and setpoint (tilt within about 10°, yaw near 0), thrust along -z. -/
def x500Posctl : Regime where
  name := "x500_posctl"
  doc := "X500 parameters, armed in Position mode, near-level attitude and setpoint"
  clauses := x500Params ++ inputRanges ++ [
    ⟨"attitude_every_tick", "vehicle_attitude_updated" =. tt⟩,
    ⟨"setpoint_every_tick", "vehicle_attitude_setpoint_updated" =. tt⟩,
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
    ⟨"posctl_status", "vehicle_status_updated" ∧. "vehicle_status_vehicle_type" =. 1 ∧.
      "vehicle_status_arming_state" =. 2 ∧. "vehicle_status_nav_state" =. 2 ∧.
      ¬. "vehicle_status_is_vtol" ∧. ¬. "vehicle_status_in_transition_mode"⟩,
    ⟨"vertical_thrust", "vehicle_attitude_setpoint_thrust_body_0" =. 0 ∧.
      "vehicle_attitude_setpoint_thrust_body_1" =. 0 ∧.
      within "vehicle_attitude_setpoint_thrust_body_2" (-1) 0⟩,
    ⟨"no_reset", "vehicle_attitude_quat_reset_counter" =. 0⟩,
    ⟨"no_autotune", ¬. "autotune_attitude_control_status_updated"⟩]
  hints := [.increasing "t_us" 1000000 2500 2500,
    .increasing "vehicle_attitude_setpoint_timestamp" 1000000 2500 2500,
    .unit (arr "vehicle_attitude_q" 4) [1, 0, 0, 0] [0, 0.08, 0.08, 0.08] [0, 0.002, 0.002, 0.002],
    .unit (arr "vehicle_attitude_delta_q_reset" 4) [1, 0, 0, 0] [0, 0, 0, 0] [0, 0, 0, 0],
    .unit (arr "vehicle_attitude_setpoint_q_d" 4) [1, 0, 0, 0] [0, 0.08, 0.08, 0.08]
      [0, 0.002, 0.002, 0.002]]

def coverage : List Clause := [
  ⟨"rates_published", "vehicle_rates_setpoint_updated" =. tt⟩,
  ⟨"roll_rate_at_limit", "vehicle_rates_setpoint_updated" ∧.
      abs "vehicle_rates_setpoint_roll" =. "MC_ROLLRATE_MAX" * degToRad⟩,
  ⟨"rates_below_limit", "vehicle_rates_setpoint_updated" ∧.
      abs "vehicle_rates_setpoint_roll" <. "MC_ROLLRATE_MAX" * degToRad ∧.
      abs "vehicle_rates_setpoint_pitch" <. "MC_PITCHRATE_MAX" * degToRad ∧.
      abs "vehicle_rates_setpoint_yaw" <. "MC_YAWRATE_MAX" * degToRad⟩,
  ⟨"thrust_nonzero", "vehicle_rates_setpoint_updated" ∧.
      ¬. ("vehicle_rates_setpoint_thrust_body_2" =. 0)⟩]

def module : Module where
  name := "px4_att"
  doc := "PX4 mc_att_control (v1.17.0), unmodified, behind the generic uORB shim"
  params := Ports.params
  input := Ports.input
  output := Ports.output
  contract := { contract with guarantee := contract.guarantee ++ Ports.outWidths }
  exe := "build/modules/px4_att/px4_att"
  stack := .px4
  regimes := [flight, x500Posctl]
  coverage := coverage

end Px4.Modules.Px4Att
