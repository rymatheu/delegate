import Harness.Compose
import px4.harnesses.px4_chain.Discharges
import px4.harnesses.px4_est.Composed
import px4.modules.px4_att.Module
import px4.modules.px4_drive_att.Module

/-! # px4_att_loop: PX4's attitude loop with the real estimator, around the gorge simulator

In PX4's in-tick order (work-queue priorities, src/modules/*: rate_ctrl 0 > nav_and_controllers -13
> INS0 -14, CONFIG_WQ_*_PRIORITY in px4_boardconfig.h, and the topic that triggers each item):
the simulator; the test driver (scripted arming, mode and attitude setpoint); the sensor bridge;
PX4's sensors (VehicleAngularVelocity on rate_ctrl publishes the filtered rate, VehicleIMU on INS0
and Sensors on nav_and_controllers make sensor_combined, all inside that module's step); then on the
gyro sample the rate_ctrl queue runs mc_rate_control and control_allocator before any
lower-priority item; EKF2 (INS0, triggered by sensor_combined) publishes vehicle_attitude;
mc_att_control (nav_and_controllers, triggered by vehicle_attitude) publishes
vehicle_rates_setpoint, which the rate controller uses at the next gyro sample (`prev`); the motor
bridge. By name, no rename. -/

namespace Px4.Harnesses.Px4AttLoop

open Harness Harness.Contract.Lang

def quietTopics : List String :=
  ["manual_control_setpoint", "battery_status", "hover_thrust_estimate",
   "autotune_attitude_control_status", "failure_detector_status"]

/-- The X500 taking off under PX4's attitude control: PX4's defaults, the SITL sensor ids, the X500
airframe; EKF2 with the declination of the simulated world (EKF2_DECL_TYPE = 2 and EKF2_MAG_DECL =
4.04 deg: the simulator's field has declination 4.04 deg where PX4's WMM table gives about 8.3 deg,
so with the default PX4 holds a yaw 4.2 deg off); armed at 2 s, motors at idle thrust 0.05 on the
ground until 12 s (EKF2's local position becomes valid at 10.5 s), then the thrust ramps over 1 s to
0.65 (a first run at 0.58 did not lift off; PX4's X500 airframe sets MPC_THR_HOVER = 0.60); level attitude setpoint, heading 0. -/
def takeoff (noise : Bool) : Regime where
  name := if noise then "x500_takeoff_noise" else "x500_takeoff"
  doc := "X500, PX4 attitude control with EKF2, scripted takeoff at 12 s" ++
    (if noise then ", sensor noise" else "")
  clauses := Px4.Modules.Px4Sensors.sitlParams ++ Px4.Modules.Px4Rate.Ports.paramDefaults ++
    Px4.Modules.Px4Alloc.x500Params ++ Px4.Modules.Px4Att.x500Params ++
    (Px4.Modules.Px4Ekf2.Ports.paramDefaults.filter fun c =>
      c.name != "default_EKF2_DECL_TYPE" && c.name != "default_EKF2_MAG_DECL") ++ [
    ⟨"sim_declination", "EKF2_DECL_TYPE" =. 2 ∧. "EKF2_MAG_DECL" =. 4.04⟩,
    ⟨"noise", "noise_on" =. (if noise then tt else ff)⟩,
    ⟨"script", "arm_s" =. 2 ∧. "takeoff_s" =. 12 ∧. "ramp_s" =. 1 ∧. "idle_thrust" =. 0.05 ∧.
      "flight_thrust" =. 0.65 ∧. "yaw_sp" =. 0⟩,
    ⟨"quiet", quietTopics.foldl (fun e t => e ∧. ¬. s!"{t}_updated") tt⟩]

def system (_ : Unit := ()) : Except String Node := do
  let n ← composeAll "px4_att_loop"
    [.module Sim.Modules.PlantSim.module, .module Px4.Modules.Px4DriveAtt.module,
     .module Px4.Modules.Px4SimIn.module, .module Px4.Modules.Px4Sensors.module,
     .module Px4.Modules.Px4Rate.module, .module Px4.Modules.Px4Alloc.module,
     .module Px4.Modules.Px4Ekf2.module, .module Px4.Modules.Px4Att.module, ← Px4.Harnesses.Px4ClosedRate.simOut]
  let n := Px4.Harnesses.Chain.withGlue n
  return Px4.Harnesses.Px4ClosedRate.withImuDefaults
    (withRegime (withRegime n (takeoff false)) (takeoff true))

end Px4.Harnesses.Px4AttLoop
