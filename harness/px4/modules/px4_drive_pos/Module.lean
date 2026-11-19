import px4.modules.px4_att.Ports
import px4.modules.px4_pos.Ports

/-! # px4_drive_pos: a TEST DRIVER for the position loop

Not PX4 code (adapter.cpp, px4/px4_test_drive.h): the same arming, mode and land script as
px4_drive_att with position control on, and a trajectory setpoint over time instead of an attitude
setpoint: position (0, 0, 0) until `takeoff_s`, then (0, 0, -takeoff_alt), then
(step_n, 0, -takeoff_alt) from `step_s` on; velocity, acceleration, jerk and yaw speed NaN ("not
set", TrajectorySetpoint.msg), yaw `yaw_sp`. Outputs are px4_pos's trajectory_setpoint fields and
px4_att's vehicle_status, vehicle_control_mode and vehicle_land_detected fields. -/

namespace Px4.Modules.Px4DrivePos

open Harness Harness.Contract.Lang

def params : Schema := #[
  { name := "arm_s", type := .f32, doc := "arming time, s" },
  { name := "takeoff_s", type := .f32, doc := "takeoff time (landed before), s" },
  { name := "takeoff_alt", type := .f32, doc := "takeoff altitude above the start, m" },
  { name := "step_s", type := .f32, doc := "time of the step north, s" },
  { name := "step_n", type := .f32, doc := "the step north, m" },
  { name := "yaw_sp", type := .f32, doc := "heading setpoint, rad" }]

def input : Schema := #[{ name := "t_us", type := .u32, doc := "the simulator's clock, us" }]
def output : Schema :=
  (Px4.Modules.Px4Pos.Ports.input.filter fun f => f.name.startsWith "trajectory_setpoint_") ++
  (Px4.Modules.Px4Att.Ports.input.filter fun f =>
    ["vehicle_status_", "vehicle_control_mode_", "vehicle_land_detected_"].any
      (fun (p : String) => f.name.startsWith p))

def contract : Contract where
  assume := [⟨"script", 0 ≤. "arm_s" ∧. "arm_s" ≤. "takeoff_s" ∧. "takeoff_s" ≤. "step_s" ∧.
    0 ≤. "takeoff_alt" ∧. "takeoff_alt" ≤. 100 ∧. abs "step_n" ≤. 1000 ∧. abs "yaw_sp" ≤. 3.14159⟩]
  guarantee := [
    ⟨"setpoint_finite", finite "trajectory_setpoint_position_0" ∧. finite "trajectory_setpoint_position_1" ∧.
      finite "trajectory_setpoint_position_2"⟩]

def module : Module where
  name := "px4_drive_pos"
  doc := "TEST DRIVER: arming, offboard mode and a position setpoint over time"
  params := params
  input := input
  output := output
  contract := contract
  exe := "build/modules/px4_drive_pos/px4_drive_pos"
  stack := .px4

end Px4.Modules.Px4DrivePos
