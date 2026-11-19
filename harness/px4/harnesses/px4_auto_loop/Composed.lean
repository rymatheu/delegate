import Harness.Compose
import px4.harnesses.px4_chain.Discharges
import px4.harnesses.px4_att_loop.Composed
import px4.modules.px4_pos.Module
import px4.modules.px4_fmm.Module
import px4.modules.px4_land.Module
import px4.modules.px4_drive_auto.Module

/-! # px4_auto_loop: PX4's flight stack with EKF2 in Auto Loiter, around the gorge simulator

`composeAll` [plant_sim, px4_drive_auto, px4_sim_in, px4_sensors, px4_rate, px4_alloc, px4_ekf2,
px4_att, px4_fmm, px4_pos, px4_land, px4_sim_out], by name, no rename. Order: px4_att_loop's
(rate_ctrl before INS0, EKF2 before the controllers it triggers), then the nav_and_controllers FIFO
as h-px4-ctl's px4_ctl established it: mc_att_control on vehicle_attitude first (EKF2.cpp:751),
then on vehicle_local_position (:807) the items in their callback-registration order, which is
rc.mc_apps' start order: flight_mode_manager, mc_pos_control, land_detector. The land detector's
vehicle_land_detected reaches every other module at the next tick (`prev`). The test driver stands
in for commander and the navigator (not in the stack): it runs after the simulator and reads EKF2's
reference at the previous tick. -/

namespace Px4.Harnesses.Px4AutoLoop

open Harness Harness.Contract.Lang

def quietTopics : List String :=
  ["manual_control_setpoint", "battery_status", "hover_thrust_estimate",
   "autotune_attitude_control_status", "failure_detector_status", "goto_setpoint",
   "velocity_limits", "failsafe_flags"]

/-- PX4's defaults with the X500 airframe's MPC_THR_HOVER = 0.60 for a module's own parameters. -/
def x500 (defaults : List Clause) : List Clause :=
  (defaults.filter (·.name != "default_MPC_THR_HOVER")) ++
    [⟨"x500_MPC_THR_HOVER", "MPC_THR_HOVER" =. 0.6⟩]

/-- The X500 in Auto Loiter: PX4's defaults, SITL sensors, the X500 airframe, EKF2 with the simulated
world's declination (4.04 deg, see px4_att_loop); disarmed on the ground until 12 s (EKF2's position
is valid from 10.5 s), then armed with the loiter setpoint 2 m above EKF2's origin, which PX4 flies
as an automatic takeoff (spool-up, takeoff ramp); from 25 s the setpoint is 10 m north. -/
def stepNorth (noise : Bool) : Regime where
  name := if noise then "x500_auto_step_noise" else "x500_auto_step"
  doc := "X500 in Auto Loiter with EKF2: armed at 12 s, loiter 2 m up, 10 m north at 25 s" ++
    (if noise then ", sensor noise" else "")
  clauses := Px4.Modules.Px4Sensors.sitlParams ++ Px4.Modules.Px4Rate.Ports.paramDefaults ++
    Px4.Modules.Px4Alloc.x500Params ++ Px4.Modules.Px4Att.x500Params ++ Px4.Modules.Px4Pos.x500Params ++
    x500 Px4.Modules.Px4Fmm.Ports.paramDefaults ++ Px4.Modules.Px4Land.x500Params ++
    Px4.Modules.Px4Pos.paramsNotRewritten ++
    (Px4.Modules.Px4Ekf2.Ports.paramDefaults.filter fun c =>
      c.name != "default_EKF2_DECL_TYPE" && c.name != "default_EKF2_MAG_DECL") ++ [
    ⟨"sim_declination", "EKF2_DECL_TYPE" =. 2 ∧. "EKF2_MAG_DECL" =. 4.04⟩,
    ⟨"noise", "noise_on" =. (if noise then tt else ff)⟩,
    ⟨"script", "arm_s" =. 12 ∧. "takeoff_alt" =. 2 ∧. "step_s" =. 25 ∧. "step_n" =. 10⟩,
    ⟨"quiet", quietTopics.foldl (fun e t => e ∧. ¬. s!"{t}_updated") tt⟩,
    ⟨"no_command", "vehicle_command_count" =. 0⟩]

/-! ### What the loop achieves against the simulator's truth

The truth in EKF2's local frame: the simulator's position (NED from its home: 38.84055560937 N,
-105.04416668583 E, 4302.00005 m AMSL, from its noise-free GPS) moved by EKF2's reference
(ref_lat, ref_lon, ref_alt), with PX4's earth radius (6371000 m: 111194.93 m per degree north,
86609.09 m per degree east at this latitude). The home latitude and longitude are written as two
binary32 numbers each (value and rest), like the float64 pairs of the ports, so the differences
are exact to well below a centimetre. Bounds, from the mechanism measured on noise seeds 101, 202
and 303 (docs in the report): EKF2's altitude error comes from PX4's baro-to-GNSS
auto-calibration step (SENS_BAR_AUTOCAL, +1.7 m at 5.45 s) and the baro bias estimate's slow
recovery from it, up to 0.49 m; its horizontal error peaks at 0.51 m during the 10 m step; the
tracking of the flight mode manager's setpoint in the hold is a few cm horizontally, and
vertically carries EKF2's altitude error. -/

def tn : Expr := "pos_n" + (((38.840557 : Expr) - "vehicle_local_position_ref_lat") +
  ((-1.4890161e-06 : Expr) - "vehicle_local_position_ref_lat_lo")) * (111194.93 : Expr)
def te : Expr := "pos_e" + (((-105.04417 : Expr) - "vehicle_local_position_ref_lon") +
  ((-1.2088596e-07 : Expr) - "vehicle_local_position_ref_lon_lo")) * (86609.09 : Expr)
def td : Expr := "pos_d" - (4302.0 : Expr) + "vehicle_local_position_ref_alt"

private def hold : Expr := (22000000 : Expr) ≤. "t_us" ∧. Expr.var "t_us" <. (25000000 : Expr)

def truthClauses : List Clause := [
  ⟨"ekf2_altitude_vs_truth", ¬. "vehicle_local_position_z_valid" ∨. ¬. "vehicle_local_position_z_global" ∨.
    abs ("vehicle_local_position_z" - td) ≤. 0.8⟩,
  ⟨"ekf2_horizontal_vs_truth", ¬. "vehicle_local_position_xy_valid" ∨.
    ¬. "vehicle_local_position_xy_global" ∨.
    (abs ("vehicle_local_position_x" - tn) ≤. 1 ∧. abs ("vehicle_local_position_y" - te) ≤. 1)⟩,
  ⟨"hold_tracks_fmm_setpoint", ¬. hold ∨.
    (abs (tn - "trajectory_setpoint_position_0") ≤. 0.5 ∧.
     abs (te - "trajectory_setpoint_position_1") ≤. 0.5 ∧.
     abs (td - "trajectory_setpoint_position_2") ≤. 0.8)⟩]

/-- The composite with `truthClauses` added to its computed guarantee. -/
def withTruth (n : Node) : Node :=
  match n with
  | .system s => .system { s with contract := { s.contract with
      guarantee := s.contract.guarantee ++ truthClauses } }
  | m => m

def system (_ : Unit := ()) : Except String Node := do
  let n ← composeAll "px4_auto_loop"
    [.module Sim.Modules.PlantSim.module, .module Px4.Modules.Px4DriveAuto.module,
     .module Px4.Modules.Px4SimIn.module, .module Px4.Modules.Px4Sensors.module,
     .module Px4.Modules.Px4Rate.module, .module Px4.Modules.Px4Alloc.module,
     .module Px4.Modules.Px4Ekf2.module, .module Px4.Modules.Px4Att.module, .module Px4.Modules.Px4Fmm.module,
     .module Px4.Modules.Px4Pos.module, .module Px4.Modules.Px4Land.module, ← Px4.Harnesses.Px4ClosedRate.simOut]
  let n := Px4.Harnesses.Chain.withGlue n
  return Px4.Harnesses.Px4ClosedRate.withImuDefaults
    (withTruth (withRegime (withRegime n (stepNorth false)) (stepNorth true)))

end Px4.Harnesses.Px4AutoLoop
