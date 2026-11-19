import Harness.Compose
import px4.harnesses.px4_chain.Discharges
import px4.harnesses.px4_att_loop.Composed
import px4.modules.px4_pos.Module
import px4.modules.px4_drive_pos.Module

/-! # px4_pos_loop: PX4's position, attitude and rate loops with EKF2, around the gorge simulator

The attitude loop of px4_att_loop with mc_position_control after mc_att_control (both on
nav_and_controllers; EKF2 publishes vehicle_attitude before vehicle_local_position, EKF2.cpp:751 and
807, so the FIFO runs att first, on the previous attitude setpoint: `prev`), and the test driver
px4_drive_pos (arming, offboard position mode, landed until takeoff, a trajectory setpoint over
time) in place of px4_drive_att. By name, no rename. -/

namespace Px4.Harnesses.Px4PosLoop

open Harness Harness.Contract.Lang

def quietTopics : List String :=
  Px4.Harnesses.Px4AttLoop.quietTopics ++ ["vehicle_constraints", "goto_setpoint"]

/-- The X500 taking off to 2 m in Offboard position control and stepping 10 m north: PX4's
defaults, SITL sensors, the X500 airframe (px4_att's and px4_pos's x500Params: MPC_THR_HOVER 0.6),
EKF2 with the simulated world's declination (4.04 deg, see px4_att_loop); armed at 2 s, landed
with the setpoint on the ground until 12 s, then 2 m up, then from 20 s 10 m north. -/
def stepNorth (noise : Bool) : Regime where
  name := if noise then "x500_step_noise" else "x500_step"
  doc := "X500, PX4 position control with EKF2: takeoff to 2 m at 12 s, 10 m north at 20 s" ++
    (if noise then ", sensor noise" else "")
  clauses := Px4.Modules.Px4Sensors.sitlParams ++ Px4.Modules.Px4Rate.Ports.paramDefaults ++
    Px4.Modules.Px4Alloc.x500Params ++ Px4.Modules.Px4Att.x500Params ++ Px4.Modules.Px4Pos.x500Params ++
    (Px4.Modules.Px4Ekf2.Ports.paramDefaults.filter fun c =>
      c.name != "default_EKF2_DECL_TYPE" && c.name != "default_EKF2_MAG_DECL") ++ [
    ⟨"sim_declination", "EKF2_DECL_TYPE" =. 2 ∧. "EKF2_MAG_DECL" =. 4.04⟩,
    ⟨"noise", "noise_on" =. (if noise then tt else ff)⟩,
    ⟨"script", "arm_s" =. 2 ∧. "takeoff_s" =. 12 ∧. "takeoff_alt" =. 2 ∧. "step_s" =. 20 ∧.
      "step_n" =. 10 ∧. "yaw_sp" =. 0⟩,
    ⟨"quiet", quietTopics.foldl (fun e t => e ∧. ¬. s!"{t}_updated") tt⟩]

def system (_ : Unit := ()) : Except String Node := do
  let n ← composeAll "px4_pos_loop"
    [.module Sim.Modules.PlantSim.module, .module Px4.Modules.Px4DrivePos.module,
     .module Px4.Modules.Px4SimIn.module, .module Px4.Modules.Px4Sensors.module,
     .module Px4.Modules.Px4Rate.module, .module Px4.Modules.Px4Alloc.module,
     .module Px4.Modules.Px4Ekf2.module, .module Px4.Modules.Px4Att.module, .module Px4.Modules.Px4Pos.module,
     ← Px4.Harnesses.Px4ClosedRate.simOut]
  let n := Px4.Harnesses.Chain.withGlue n
  return Px4.Harnesses.Px4ClosedRate.withImuDefaults
    (withRegime (withRegime n (stepNorth false)) (stepNorth true))

end Px4.Harnesses.Px4PosLoop
