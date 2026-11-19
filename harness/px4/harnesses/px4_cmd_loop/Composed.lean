import Harness.Compose
import px4.harnesses.px4_chain.Discharges
import px4.harnesses.px4_auto_loop.Composed
import px4.modules.px4_commander.Module
import px4.modules.px4_drive_cmd.Module

/-! # px4_cmd_loop: px4_auto_loop with PX4's commander

[plant_sim, px4_drive_cmd, px4_sim_in, px4_sensors, px4_rate, px4_alloc, px4_ekf2, px4_att,
px4_fmm, px4_pos, px4_land, px4_commander, px4_sim_out], by name, no rename. PX4's commander makes
vehicle_status, vehicle_control_mode, actuator_armed and home_position from the ground station's
commands and the vehicle's own topics; the test driver sends only the commands (mode, arm) and the
navigator's loiter setpoint. Commander is a task (10 ms sleep, own priority below the work queues):
it runs after the work queues of the tick, so its status reaches the controllers at the next tick
(`prev`), and it reads the land detector and the estimator of the same tick. The guarantee is
the computed one with px4_auto_loop's three clauses against the simulator's truth (same hold
window, 22-25 s: here too the arm command is at 12 s and the step at 25 s). -/

namespace Px4.Harnesses.Px4CmdLoop

open Harness Harness.Contract.Lang

/-- commander's SITL parameters (rcS), except the second and third IMU's and the second compass's
calibration ids: this vehicle has one of each, and px4_sensors assumes every calibration slot is
free or its device. -/
def commanderSets : List (String × Expr) :=
  Px4.Modules.Px4Commander.x500Sets.filter fun (n, _) =>
    !["CAL_ACC1_ID", "CAL_GYRO1_ID", "CAL_ACC2_ID", "CAL_GYRO2_ID", "CAL_MAG1_ID",
      "CAL_MAG1_PRIO"].contains n

def setNames : List String :=
  commanderSets.map (·.1) ++ Px4.Modules.Px4Sensors.sitlNames ++
    ["MPC_THR_HOVER", "EKF2_DECL_TYPE", "EKF2_MAG_DECL"]

/-- Every module's PX4 defaults, each set value once. -/
def paramClauses : List Clause :=
  let defaults := Px4.Modules.Px4Sensors.Ports.paramDefaults ++ Px4.Modules.Px4Rate.Ports.paramDefaults ++
    Px4.Modules.Px4Alloc.x500Params ++ Px4.Modules.Px4Att.Ports.paramDefaults ++
    Px4.Modules.Px4Pos.Ports.paramDefaults ++ Px4.Modules.Px4Fmm.Ports.paramDefaults ++
    Px4.Modules.Px4Land.Ports.paramDefaults ++ Px4.Modules.Px4Ekf2.Ports.paramDefaults ++
    Px4.Modules.Px4Commander.Ports.paramDefaults
  (defaults.filter fun c => !setNames.any fun n => c.name == s!"default_{n}") ++
  (Px4.Modules.Px4Sensors.sitlParams.filter fun c => !c.name.startsWith "default_") ++
  commanderSets.map (fun (n, v) => ⟨s!"x500_{n}", Expr.var n =. v⟩) ++
  [⟨"x500_MPC_THR_HOVER", "MPC_THR_HOVER" =. 0.6⟩,
   ⟨"sim_declination", "EKF2_DECL_TYPE" =. 2 ∧. "EKF2_MAG_DECL" =. 4.04⟩] ++
  Px4.Modules.Px4Pos.paramsNotRewritten

/-- The clauses of `cs` that speak only of `n`'s parameters and inputs (a regime can only steer
those; the rest are wired inside). -/
def restrict (n : Node) (cs : List Clause) : List Clause :=
  let v := n.view
  let ok := (v.params ++ v.input).toList.map (·.name)
  cs.filter fun c => c.expr.vars.all ok.contains

/-- What the stack does not make, healthy and constant (commander's healthy values for the
topics left unwired: battery, power, CPU load, the GCS link, the estimator selector), the modules
not in the stack silent, no noise or with noise. The pins of the topics the stack makes are
dropped by `restrict`: commander reads EKF2's estimator_status, estimator_status_flags and
estimator_sensor_bias and px4_sensors' sensors_status_imu, sensor_selection and vehicle_imu_status
as they are published. -/
def stepNorth (n : Node) (noise : Bool) : Regime where
  name := if noise then "x500_cmd_step_noise" else "x500_cmd_step"
  doc := "X500 with PX4's commander: Auto Loiter at 11 s, armed at 12 s, loiter 2 m up, 10 m north at 25 s" ++
    (if noise then ", sensor noise" else "")
  clauses := paramClauses ++ restrict n (
    Px4.Modules.Px4Commander.pinned Px4.Modules.Px4Commander.healthyTopics Px4.Modules.Px4Commander.healthyValues
      (["battery_status_voltage_v", "battery_status_remaining", "battery_status_current_a",
        "battery_status_current_average_a"]) ++
    (Px4.Modules.Px4Commander.groundFree.filter (·.name == "battery_charged")) ++
    Px4.Modules.Px4Commander.silent) ++ [
    ⟨"noise", "noise_on" =. (if noise then tt else ff)⟩,
    ⟨"script", "mode_s" =. 11 ∧. "arm_s" =. 12 ∧. "arm_until_s" =. 14 ∧. "takeoff_alt" =. 2 ∧.
      "step_s" =. 25 ∧. "step_n" =. 10⟩] ++
    -- one clause per topic: `restrict` drops a clause that names a wired field, and
    -- failure_detector_status and failsafe_flags are commander's outputs here (a single
    -- "quiet" conjunction over all six was dropped whole, leaving the other four free)
    restrict n (["hover_thrust_estimate", "autotune_attitude_control_status",
      "failure_detector_status", "goto_setpoint", "velocity_limits", "failsafe_flags"].map
        fun t => ⟨s!"quiet_{t}", ¬. s!"{t}_updated"⟩)
  -- the timestamps of the topics the regime pins advance with the simulator's clock (t_us is
  -- 2500 us at the first step and grows by 2500 us per step), so none is stale or from the future
  hints := (n.view.input.toList.filter fun f =>
    f.name.endsWith "_timestamp" || f.name.endsWith "_timestamp_sample").map
      fun f => Hint.increasing f.name 2500 2500 2500

def system (_ : Unit := ()) : Except String Node := do
  let n ← composeAll "px4_cmd_loop"
    [.module Sim.Modules.PlantSim.module, .module Px4.Modules.Px4DriveCmd.module,
     .module Px4.Modules.Px4SimIn.module, .module Px4.Modules.Px4Sensors.module,
     .module Px4.Modules.Px4Rate.module, .module Px4.Modules.Px4Alloc.module,
     .module Px4.Modules.Px4Ekf2.module, .module Px4.Modules.Px4Att.module, .module Px4.Modules.Px4Fmm.module,
     .module Px4.Modules.Px4Pos.module, .module Px4.Modules.Px4Land.module,
     .module Px4.Modules.Px4Commander.module, ← Px4.Harnesses.Px4ClosedRate.simOut]
  let n := Px4.Harnesses.Chain.withGlue n
  return Px4.Harnesses.Px4ClosedRate.withImuDefaults (Px4.Harnesses.Px4AutoLoop.withTruth
    (withRegime (withRegime n (stepNorth n false)) (stepNorth n true)))

end Px4.Harnesses.Px4CmdLoop
