import px4.modules.px4_commander.Ports

/-! # px4_drive_nav: a TEST DRIVER that is only a ground station

Not PX4 code (adapter.cpp). It sends vehicle_command messages as a ground station does, and
nothing else: no setpoint, no status, no home. Commands, from system 255 component 190 to 1/1,
each once, at the first step at or after its time at which commander's vehicle_status was
published in the previous tick (so navigator, which reads the same vehicle_status, gets the
command in a step that also brings a vehicle_status: px4_navigator's `command_paced`):
* COMPONENT_ARM_DISARM arm (400; param1 1) at `arm_s`;
* NAV_TAKEOFF (22; position and altitude NaN: PX4's takeoff at the current position,
  MIS_TAKEOFF_ALT above it) at `takeoff_s`;
* DO_REPOSITION (192; param1 -1 default speed, param2 1 = switch mode, yaw and altitude NaN: the
  current altitude) at `repos_s`, to `repos_n` m north of commander's home: latitude and
  longitude as binary32 (the command's slot carries a float64 as one binary32, so the driver
  sends the binary32 nearest the point, within 0.21 m north and 0.33 m east at the simulator's
  home, and navigator gets exactly that value);
* NAV_LAND (21; position NaN: land where it is) at `land_s`.
It reads commander's telemetry, as a ground station would: vehicle_status_updated and home
position (previous tick). -/

namespace Px4.Modules.Px4DriveNav

open Harness Harness.Contract.Lang

def params : Schema := #[
  { name := "arm_s", type := .f32, doc := "time of the arm command, s" },
  { name := "takeoff_s", type := .f32, doc := "time of the takeoff command, s" },
  { name := "repos_s", type := .f32, doc := "time of the reposition command, s" },
  { name := "repos_n", type := .f32, doc := "the reposition, m north of home" },
  { name := "land_s", type := .f32, doc := "time of the land command, s" }]

def statusFields : List String :=
  ["vehicle_status_updated", "home_position_lat", "home_position_lat_lo", "home_position_lon",
   "home_position_lon_lo", "home_position_valid_hpos"]

def input : Schema := #[{ name := "t_us", type := .u32, doc := "the simulator's clock, us" }] ++
  (Px4.Modules.Px4Commander.Ports.output.filter fun f => statusFields.contains f.name)

def output : Schema :=
  Px4.Modules.Px4Commander.Ports.input.filter fun f => f.name.startsWith "vehicle_command_"

def contract : Contract where
  assume := [⟨"script", 0 ≤. "arm_s" ∧. "arm_s" ≤. "takeoff_s" ∧. "takeoff_s" ≤. "repos_s" ∧.
    "repos_s" ≤. "land_s" ∧. abs "repos_n" ≤. 1000⟩]
  guarantee := [
    ⟨"one_command", "vehicle_command_count" ≤. 1⟩,
    ⟨"gcs_command", "vehicle_command_count" =. 0 ∨. ("vehicle_command_source_system" =. 255 ∧.
      "vehicle_command_target_system" =. 1)⟩,
    ⟨"paced", "vehicle_command_count" =. 0 ∨. "vehicle_status_updated"⟩]

def regime : Regime where
  name := "script"
  doc := "the nav loop's script (arm 12 s, takeoff 13 s, reposition 10 m north at 25 s, land \
    38 s); vehicle_status published at random ticks; home at the simulator's"
  clauses := [⟨"script", "arm_s" =. 12 ∧. "takeoff_s" =. 13 ∧. "repos_s" =. 25 ∧.
      "repos_n" =. 10 ∧. "land_s" =. 38⟩,
    ⟨"home", 38.8 ≤. "home_position_lat" ∧. "home_position_lat" ≤. 38.9 ∧.
      abs "home_position_lat_lo" ≤. 1e-6 ∧. -105.1 ≤. "home_position_lon" ∧.
      "home_position_lon" ≤. -105 ∧. abs "home_position_lon_lo" ≤. 1e-6 ∧.
      "home_position_valid_hpos" =. tt⟩]
  hints := [.increasing "t_us" 11000000 2500 2500]

def module : Module where
  name := "px4_drive_nav"
  doc := "TEST DRIVER: a ground station's commands (arm, takeoff, reposition, land), nothing else"
  params := params
  input := input
  output := output
  contract := contract
  exe := "build/modules/px4_drive_nav/px4_drive_nav"
  stack := .px4
  regimes := [regime]

end Px4.Modules.Px4DriveNav
