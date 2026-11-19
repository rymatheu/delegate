import px4.modules.px4_fmm.Ports
import px4.modules.px4_land.Ports
import px4.modules.px4_ekf2.Ports

/-! # px4_drive_auto: a TEST DRIVER for an Auto Loiter flight

Not PX4 code (adapter.cpp, px4/px4_test_drive.h): it stands in for commander and the navigator,
which are not in this stack. Outputs: vehicle_status (rotary wing, Auto Loiter, disarmed until
`arm_s`), vehicle_control_mode (commander's Auto flags), actuator_armed, home_position (EKF2's
origin horizontally, EKF2's altitude at arming, as commander sets it), and the navigator's
position_setpoint_triplet: a valid loiter setpoint `takeoff_alt` above home, `step_n` m north of
EKF2's origin from `step_s` on (yaw, cruising speed NaN). A first version put the setpoint
`takeoff_alt` above EKF2's local origin (ref_alt); that origin sits 0.16-0.47 m below the ground
(px4_auto_loop), so the vehicle held 1.5 m instead of 2. The output fields
are px4_fmm's and px4_land's generated input fields; the inputs are the clock and EKF2's local-frame
reference (px4_ekf2's output fields, the previous tick), so it composes by name. The land
detector, flight mode manager, position, attitude and rate controllers are PX4's. -/

namespace Px4.Modules.Px4DriveAuto

open Harness Harness.Contract.Lang

def params : Schema := #[
  { name := "arm_s", type := .f32, doc := "arming time, s" },
  { name := "takeoff_alt", type := .f32, doc := "loiter altitude above EKF2's origin, m" },
  { name := "step_s", type := .f32, doc := "time of the step north, s" },
  { name := "step_n", type := .f32, doc := "the step north, m" }]

def refFields : List String :=
  ["ref_lat", "ref_lat_lo", "ref_lon", "ref_lon_lo", "ref_alt", "xy_global", "z_global", "z"].map
    (s!"vehicle_local_position_{·}")

def input : Schema := #[{ name := "t_us", type := .u32, doc := "the simulator's clock, us" }] ++
  Px4.Modules.Px4Ekf2.Ports.output.filter fun f => refFields.contains f.name

def output : Schema :=
  (Px4.Modules.Px4Fmm.Ports.input.filter fun f =>
    ["vehicle_status_", "vehicle_control_mode_", "position_setpoint_triplet_", "home_position_"].any
      (fun (p : String) => f.name.startsWith p)) ++
  (Px4.Modules.Px4Land.Ports.input.filter fun f => f.name.startsWith "actuator_armed_")

def scriptClause : Clause := ⟨"script", 0 ≤. "arm_s" ∧. "arm_s" ≤. "step_s" ∧.
  0 ≤. "takeoff_alt" ∧. "takeoff_alt" ≤. 100 ∧. abs "step_n" ≤. 1000⟩

def loiterSetpoint : Clause := ⟨"loiter_setpoint", ¬. "position_setpoint_triplet_updated" ∨.
  ("position_setpoint_triplet_current_type" =. 2 ∧. finite "position_setpoint_triplet_current_alt")⟩

/-- The first statement: `loiter_setpoint` under `script` alone. Refuted by the first campaign of
this module in main (2026-11-18, `harness test px4_drive_auto --seed 1 --cases 20 --steps 400`: 224
violations in 8000 steps, first at case 4, step 8): there EKF2's reference is global
(`vehicle_local_position_xy_global`, `_z_global` true) with `vehicle_local_position_ref_alt` = -inf,
and adapter.cpp writes the setpoint altitude as `ref_alt + takeoff_alt` (before arming) or
`home_alt + takeoff_alt` with `home_alt = ref_alt - z` taken at arming, so a non-finite or huge
reference gives a non-finite altitude. The driver's statement is right only for the reference
EKF2 publishes; kept for the record. -/
def contractAsFirstStated : Contract where
  assume := [scriptClause]
  guarantee := [loiterSetpoint]

/-- The contract: the first statement with EKF2's reference finite and within 10^7 m whenever it is
global (`ekf2_reference_bounded`), so `ref_alt + takeoff_alt` and `ref_alt - z + takeoff_alt` are
finite. -/
def contract : Contract where
  assume := [scriptClause,
    ⟨"ekf2_reference_bounded", ¬. ("vehicle_local_position_xy_global" ∧.
      "vehicle_local_position_z_global") ∨.
      (abs "vehicle_local_position_ref_alt" ≤. 10000000 ∧.
       abs "vehicle_local_position_z" ≤. 10000000)⟩]
  guarantee := [loiterSetpoint]

def module : Module where
  name := "px4_drive_auto"
  doc := "TEST DRIVER: commander's and the navigator's topics for an Auto Loiter flight"
  params := params
  input := input
  output := output
  contract := contract
  exe := "build/modules/px4_drive_auto/px4_drive_auto"
  stack := .px4

end Px4.Modules.Px4DriveAuto
