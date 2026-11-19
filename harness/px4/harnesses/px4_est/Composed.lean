import Harness.Compose
import px4.harnesses.px4_chain.Discharges
import sim.modules.plant_sim.Module
import px4.modules.px4_sim_in.Module
import px4.modules.px4_sensors.Module
import px4.modules.px4_ekf2.Module
import px4.harnesses.px4_closed_rate.Composed

/-! # px4_est and px4_est_flying: PX4's estimator on the gorge simulator

`px4_est`: the simulator, the sensor bridge, PX4's sensors and PX4's EKF2, by name, no rename. The
motors get no command (PWM inputs of the composite, 1000 in the regimes): the X500 rests on the
gorge floor. `px4_est_flying`: the same with PX4's rate loop closed (px4_closed_rate's chain), so
that the vehicle moves while EKF2 estimates. Tracking errors are measured against plant_sim's
truth outputs from the saved cases (docs in the report). -/

namespace Px4.Harnesses.Px4Est

open Harness Harness.Contract.Lang

/-- PX4's defaults for EKF2, the SITL sensor configuration. -/
def estParams : List Clause :=
  Px4.Modules.Px4Sensors.sitlParams ++ Px4.Modules.Px4Ekf2.Ports.paramDefaults

def restQuiet (noise : Bool) : List Clause := [
  ⟨"noise", "noise_on" =. (if noise then tt else ff)⟩,
  ⟨"status", "vehicle_status_updated" ∧. "vehicle_status_vehicle_type" =. 1 ∧.
    "vehicle_status_arming_state" =. 1 ∧. ¬. "vehicle_status_is_vtol"⟩,
  ⟨"no_land_detector", ¬. "vehicle_land_detected_updated"⟩]

def atRest (noise : Bool) : Regime where
  name := if noise then "rest_noise" else "rest"
  doc := "X500 resting, motors off, PX4 defaults, SITL sensors" ++ (if noise then ", noise" else "")
  clauses := estParams ++ restQuiet noise ++ [
    ⟨"motors_off", "pwm0" =. 1000 ∧. "pwm1" =. 1000 ∧. "pwm2" =. 1000 ∧. "pwm3" =. 1000⟩]

def system (_ : Unit := ()) : Except String Node := do
  let n ← composeAll "px4_est"
    [.module Sim.Modules.PlantSim.module, .module Px4.Modules.Px4SimIn.module,
     .module Px4.Modules.Px4Sensors.module, .module Px4.Modules.Px4Ekf2.module]
  let n := Px4.Harnesses.Chain.withGlue n
  return Px4.Harnesses.Px4ClosedRate.withImuDefaults
    (withRegime (withRegime n (atRest false)) (atRest true))

def flying (noise : Bool) : Regime :=
  let h := Px4.Harnesses.Px4ClosedRate.x500Hover
  { h with name := if noise then "hover_noise" else "hover"
           doc := h.doc ++ ", EKF2 running" ++ (if noise then ", noise" else "")
           clauses := (h.clauses.filter (·.name != "no_noise")) ++ Px4.Modules.Px4Ekf2.Ports.paramDefaults ++
             [⟨"noise", "noise_on" =. (if noise then tt else ff)⟩] }

def flyingSystem (_ : Unit := ()) : Except String Node := do
  let n ← composeAll "px4_est_flying"
    [.module Sim.Modules.PlantSim.module, .module Px4.Modules.Px4SimIn.module,
     .module Px4.Modules.Px4Sensors.module, .module Px4.Modules.Px4Ekf2.module,
     .module Px4.Modules.Px4Rate.module, .module Px4.Modules.Px4Alloc.module, ← Px4.Harnesses.Px4ClosedRate.simOut]
  let n := Px4.Harnesses.Chain.withGlue n
  return Px4.Harnesses.Px4ClosedRate.withImuDefaults
    (withRegime (withRegime n (flying false)) (flying true))

end Px4.Harnesses.Px4Est
