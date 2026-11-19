import px4.modules.px4_commander.Ports
import px4.modules.px4_fmm.Ports
import px4.modules.px4_ekf2.Ports

/-! # px4_drive_cmd: a TEST DRIVER with PX4's commander in the loop

Not PX4 code (adapter.cpp). It stands in for a ground station and for the navigator only:
vehicle_command (px4_commander's input fields, all slots; one command per tick): DO_SET_MODE
Auto Loiter (176; 1, 4, 3) at `mode_s`, COMPONENT_ARM_DISARM arm (400; 1) at `arm_s` and every
0.5 s until `arm_until_s`, from system 255 component 190 to 1/1; and the navigator's loiter
position_setpoint_triplet (px4_fmm's input fields): `takeoff_alt` above commander's home altitude
(home_position.alt, which commander sets from the global position at arming; the previous tick),
as the navigator's takeoff altitude is MIS_TAKEOFF_ALT above home, and `step_n` north of EKF2's
origin from `step_s`; while commander has no valid home, the setpoint is not published. vehicle_status,
vehicle_control_mode, actuator_armed and home_position come from PX4's commander. -/

namespace Px4.Modules.Px4DriveCmd

open Harness Harness.Contract.Lang

def params : Schema := #[
  { name := "mode_s", type := .f32, doc := "time of the DO_SET_MODE Auto Loiter command, s" },
  { name := "arm_s", type := .f32, doc := "time of the first arm command, s" },
  { name := "arm_until_s", type := .f32, doc := "arm commands every 0.5 s until this time, s" },
  { name := "takeoff_alt", type := .f32, doc := "loiter altitude above commander's home altitude, m" },
  { name := "step_s", type := .f32, doc := "time of the step north, s" },
  { name := "step_n", type := .f32, doc := "the step north, m" }]

def refFields : List String :=
  ["ref_lat", "ref_lat_lo", "ref_lon", "ref_lon_lo", "ref_alt", "xy_global", "z_global"].map
    (s!"vehicle_local_position_{·}")

def homeFields : List String := ["home_position_alt", "home_position_valid_alt"]

def input : Schema := #[{ name := "t_us", type := .u32, doc := "the simulator's clock, us" }] ++
  (Px4.Modules.Px4Ekf2.Ports.output.filter fun f => refFields.contains f.name) ++
  (Px4.Modules.Px4Commander.Ports.output.filter fun f => homeFields.contains f.name)

def output : Schema :=
  (Px4.Modules.Px4Commander.Ports.input.filter fun f => f.name.startsWith "vehicle_command_") ++
  (Px4.Modules.Px4Fmm.Ports.input.filter fun f => f.name.startsWith "position_setpoint_triplet_")

def scriptClause : Clause := ⟨"script", 0 ≤. "mode_s" ∧. "mode_s" ≤. "arm_s" ∧.
  "arm_s" ≤. "arm_until_s" ∧. "arm_until_s" ≤. "step_s" ∧. 0 ≤. "takeoff_alt" ∧.
  "takeoff_alt" ≤. 100 ∧. abs "step_n" ≤. 1000⟩

def guarantee : List Clause := [
    ⟨"one_command", "vehicle_command_count" ≤. 1⟩,
    ⟨"gcs_command", "vehicle_command_count" =. 0 ∨. ("vehicle_command_source_system" =. 255 ∧.
      "vehicle_command_target_system" =. 1)⟩]

/-- The first statement: `script` alone. Refuted by the first campaign of this module in main
(2026-11-18, `harness test px4_drive_cmd --seed 1 --cases 1 --steps 10`: the executable did not
answer the first step within 60 s). adapter.cpp walks the arm times `for (float s = arm_s;
s <= arm_until_s + 1e-3f; s += 0.5f)` at every step: with `script` alone `arm_until_s - arm_s` can
be ~10^38 s (that many iterations), and from 2^23 s on `s += 0.5f` no longer changes `s` (a loop
that never ends); `at` also converts `s * 1e6f` to uint32_t, undefined in C++ beyond 4294.97 s.
Kept for the record. -/
def contractAsFirstStated : Contract where
  assume := [scriptClause]
  guarantee := guarantee

/-- The contract: the script's times within the u32 microsecond clock (`times_in_clock`: `step_s`,
and so every earlier time, at most 4000 s), where the loop takes at most 8000 iterations and the
conversions are defined. -/
def contract : Contract where
  assume := [scriptClause, ⟨"times_in_clock", "step_s" ≤. 4000⟩]
  guarantee := guarantee

def module : Module where
  name := "px4_drive_cmd"
  doc := "TEST DRIVER: a ground station's mode and arm commands, and the navigator's loiter setpoint"
  params := params
  input := input
  output := output
  contract := contract
  exe := "build/modules/px4_drive_cmd/px4_drive_cmd"
  stack := .px4

end Px4.Modules.Px4DriveCmd
