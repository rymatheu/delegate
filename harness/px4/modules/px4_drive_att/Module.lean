import px4.modules.px4_att.Ports

/-! # px4_drive_att: a TEST DRIVER for the attitude loop

Not PX4 code: a script over time (adapter.cpp, px4/px4_test_drive.h) standing in for commander, the
land detector and the setpoint source, so that the attitude loop around the simulator can take
off once the estimator is up. Its only input is the clock `t_us`; its outputs are px4_att's input
fields of vehicle_attitude_setpoint, vehicle_status, vehicle_control_mode and
vehicle_land_detected (taken from px4_att's generated ports, so it composes by name). Offboard,
rotary wing, rates, attitude and allocation on, position control off; disarmed until `arm_s`,
landed until `takeoff_s`; a level attitude setpoint at heading `yaw_sp`, thrust 0 while disarmed,
`idle_thrust` while armed on the ground, ramping linearly over `ramp_s` to `flight_thrust`. Why a
module and not a harness feature: a campaign draws inputs per tick at random; a scripted flight is
a source of inputs, so it is a node like the others, and the harness library stays as it is. -/

namespace Px4.Modules.Px4DriveAtt

open Harness Harness.Contract.Lang

def prefixes : List String :=
  ["vehicle_attitude_setpoint_", "vehicle_status_", "vehicle_control_mode_", "vehicle_land_detected_"]

def params : Schema := #[
  { name := "arm_s", type := .f32, doc := "arming time, s" },
  { name := "takeoff_s", type := .f32, doc := "takeoff time (landed before), s" },
  { name := "ramp_s", type := .f32, doc := "thrust ramp from idle to flight thrust, s" },
  { name := "idle_thrust", type := .f32, doc := "normalized thrust armed on the ground" },
  { name := "flight_thrust", type := .f32, doc := "normalized thrust after the ramp" },
  { name := "yaw_sp", type := .f32, doc := "heading setpoint, rad" }]

def input : Schema := #[{ name := "t_us", type := .u32, doc := "the simulator's clock, us" }]
def output : Schema := Px4.Modules.Px4Att.Ports.input.filter fun f =>
  prefixes.any (fun (p : String) => f.name.startsWith p)

def contract : Contract where
  assume := [⟨"script", 0 ≤. "arm_s" ∧. "arm_s" ≤. "takeoff_s" ∧. 0 ≤. "ramp_s" ∧. 0 ≤. "idle_thrust" ∧.
    "idle_thrust" ≤. "flight_thrust" ∧. "flight_thrust" ≤. 1 ∧. abs "yaw_sp" ≤. 3.14159⟩]
  guarantee := [
    ⟨"thrust_scripted", -1 ≤. "vehicle_attitude_setpoint_thrust_body_2" ∧.
      "vehicle_attitude_setpoint_thrust_body_2" ≤. 0⟩,
    ⟨"level", "vehicle_attitude_setpoint_q_d_1" =. 0 ∧. "vehicle_attitude_setpoint_q_d_2" =. 0⟩]

def module : Module where
  name := "px4_drive_att"
  doc := "TEST DRIVER: arming, offboard mode and a level attitude setpoint over time"
  params := params
  input := input
  output := output
  contract := contract
  exe := "build/modules/px4_drive_att/px4_drive_att"
  stack := .px4

end Px4.Modules.Px4DriveAtt
