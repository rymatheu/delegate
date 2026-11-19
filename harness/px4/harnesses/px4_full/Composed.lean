import Harness.Compose
import px4.harnesses.px4_nav_loop.Composed
import px4.modules.px4_mavlink.Module
import px4.harnesses.px4_chain.Discharges

/-! # px4_full: the PX4 stack with its ground link, no test driver

[plant_sim, px4_sim_in, px4_sensors, px4_rate, px4_alloc, px4_ekf2, px4_att, px4_mavlink,
px4_navigator, px4_fmm, px4_pos, px4_land, px4_commander, px4_merge_ack, px4_sim_out], by name,
no rename. Every command arrives as MAVLink bytes on mavlink_rx_* (the composite's only command
input): mavlink publishes vehicle_command (to commander and navigator, same tick), the mission
and every storage request of its mission manager on the mirror port (navigator's dataman, same
tick), telemetry_status (commander: the ground-station link); it reads the estimates (EKF2, same
tick), the GPS driver's sensor_gps (the simulator bridge), the vehicle's state (commander, land
detector, navigator: previous tick) and the merged acknowledgements (px4_merge_ack, previous
tick). The topics nothing in the stack makes (battery, power, CPU load, the estimator selector)
are commander's healthy constants, as in px4_cmd_loop; RC, offboard and the fixed-wing
controller's status are silent.

Regimes: the link silent (`x500_full`, `x500_full_noise`): what a campaign can check without a
ground station. Flights with a ground station run through px4/harnesses/px4_full/dev/relay.py
(`harness serve px4_full`, monitors inside). -/

namespace Px4.Harnesses.Px4Full

open Harness Harness.Contract.Lang
open Px4.Harnesses.Px4CmdLoop (restrict)

/-- The parameters: px4_nav_loop's, and mavlink's PX4 defaults of the parameters px4_nav_loop
does not speak of (mavlink serves the whole stack's store read-only, under the same names, so
every module reads the same value). A first version dropped every default of a parameter that a
non-default clause names, which dropped MPC_THR_MAX, MPC_XY_CRUISE and 13 others (they appear in
px4_pos's `params_consistent`): the relay then gave them 0, and the vehicle armed in a mission and
never took off. -/
def fullParams : List Clause :=
  let nav := Px4.Harnesses.Px4NavLoop.navParams
  let named := nav.flatMap (·.expr.vars)
  nav ++ Px4.Modules.Px4Mavlink.Ports.paramDefaults.filter fun c => !c.expr.vars.any named.contains

def silentLink (n : Node) (noise : Bool) : Regime where
  name := if noise then "x500_full_noise" else "x500_full"
  doc := "X500, the whole PX4 stack, the ground link silent" ++
    (if noise then ", sensor noise" else "")
  clauses := fullParams ++ restrict n (
    Px4.Modules.Px4Commander.pinned Px4.Modules.Px4Commander.healthyTopics
      Px4.Modules.Px4Commander.healthyValues
      (["battery_status_voltage_v", "battery_status_remaining", "battery_status_current_a",
        "battery_status_current_average_a"]) ++
    (Px4.Modules.Px4Commander.groundFree.filter (·.name == "battery_charged")) ++
    Px4.Modules.Px4Commander.silent) ++ [
    ⟨"noise", "noise_on" =. (if noise then tt else ff)⟩,
    ⟨"link_silent", "mavlink_rx_len" =. 0⟩] ++
    restrict n ((["hover_thrust_estimate", "autotune_attitude_control_status",
      "failure_detector_status", "goto_setpoint", "velocity_limits", "failsafe_flags"] ++
        Px4.Harnesses.Px4NavLoop.navQuiet).map fun t => ⟨s!"quiet_{t}", ¬. s!"{t}_updated"⟩)
  hints := (n.view.input.toList.filter fun f =>
    f.name.endsWith "_timestamp" || f.name.endsWith "_timestamp_sample").map
      fun f => Hint.increasing f.name 2500 2500 2500

def withTruth (n : Node) : Node :=
  match n with
  | .system s => .system { s with contract := { s.contract with
      guarantee := s.contract.guarantee ++
        (Px4.Harnesses.Px4AutoLoop.truthClauses.filter (·.name == "ekf2_horizontal_vs_truth")) } }
  | m => m

def system (_ : Unit := ()) : Except String Node := do
  let n ← composeAll "px4_full"
    [.module Sim.Modules.PlantSim.module, .module Px4.Modules.Px4SimIn.module,
     .module Px4.Modules.Px4Sensors.module, .module Px4.Modules.Px4Rate.module,
     .module Px4.Modules.Px4Alloc.module, .module Px4.Modules.Px4Ekf2.module,
     .module Px4.Modules.Px4Att.module, .module Px4.Modules.Px4Mavlink.module,
     .module Px4.Modules.Px4CmdWindow.module,
     .module Px4.Modules.Px4Navigator.module, .module Px4.Modules.Px4Fmm.module,
     .module Px4.Modules.Px4Pos.module, .module Px4.Modules.Px4Land.module,
     .module Px4.Modules.Px4Commander.module, .module Px4.Modules.Px4MergeAck.module,
     ← Px4.Harnesses.Px4ClosedRate.simOut]
  let n := withDischarges n (Px4.Harnesses.Chain.storage ++ Px4.Harnesses.Chain.window)
  let n := Px4.Harnesses.Chain.withGlue n
  return Px4.Harnesses.Px4ClosedRate.withImuDefaults
    (withTruth (withRegime (withRegime n (silentLink n false)) (silentLink n true)))

end Px4.Harnesses.Px4Full
