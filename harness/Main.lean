import Harness
import Harness.Cli
import ardupilot.modules.rate_pid.Module
import ardupilot.modules.mixer.Module
import ardupilot.modules.position.Module
import ardupilot.modules.estimator.Module
import ardupilot.modules.est_scenario.Module
import ardupilot.modules.attitude.Module
import ardupilot.modules.guidance.Module
import ardupilot.modules.loiter.Module
import ardupilot.modules.script.Module
import ardupilot.modules.truth_est.Module
import ardupilot.modules.supervisor.Module
import ardupilot.harnesses.rate.Harness
import ardupilot.harnesses.rate.Composed
import ardupilot.harnesses.inner_loop.Harness
import ardupilot.harnesses.inner_loop.Composed
import ardupilot.harnesses.closed_inner.Composed
import ardupilot.harnesses.est_loop.Composed
import ardupilot.harnesses.ap_ctl.Composed
import ardupilot.harnesses.ap_flight.Composed
import ardupilot.harnesses.ap_full.Composed
import ardupilot.harnesses.ap_full_ekf.Composed
import px4.modules.px4_rate.Module
import px4.modules.px4_alloc.Module
import px4.modules.px4_sensors.Module
import px4.modules.px4_sim_in.Module
import px4.modules.px4_sim_out.Module
import px4.modules.px4_ekf2.Module
import px4.modules.px4_att.Module
import px4.modules.px4_pos.Module
import px4.modules.px4_drive_att.Module
import px4.modules.px4_drive_pos.Module
import px4.modules.px4_drive_auto.Module
import px4.modules.px4_fmm.Module
import px4.modules.px4_land.Module
import px4.modules.px4_commander.Module
import px4.modules.px4_drive_cmd.Module
import px4.modules.px4_navigator.Module
import px4.modules.px4_merge_ack.Module
import px4.modules.px4_drive_nav.Module
import px4.modules.px4_mavlink.Module
import px4.modules.px4_cmd_window.Module
import px4.harnesses.px4_inner.Composed
import px4.harnesses.px4_closed_rate.Composed
import px4.harnesses.px4_est.Composed
import px4.harnesses.px4_att_loop.Composed
import px4.harnesses.px4_pos_loop.Composed
import px4.harnesses.px4_auto_loop.Composed
import px4.harnesses.px4_cmd_loop.Composed
import px4.harnesses.px4_nav_loop.Composed
import px4.harnesses.px4_full.Composed
import px4.harnesses.px4_formation.Composed
import sim.modules.plant_sim.Module
import sim.modules.plant_formation.Module
import ardupilot.harnesses.ap_formation.Composed

/-! The `harness` command: the commands of Harness/Cli.lean over a registry. Run it from the
harness directory (paths are relative to it). -/

open Harness

/-- A registry entry for a node written out. -/
def entry (n : Node) : String × (Unit → Except String Node) := (n.name, fun _ => .ok n)

/-- A registry entry for a composition, composed only when it is named (its error, if any, is
shown then): `n` is a function of `()`, a system definition `def system (_ : Unit := ()) ...`. -/
def composed (name : String) (n : Unit → Except String Node) :
    String × (Unit → Except String Node) := (name, n)

/-- The compiled top-level harness (ardupilot/Top.lean) as a module: `.lake/build/bin/top serve`
behind the launcher build/top/top_serve, with the interface and contract of the composition it
serves. Its stack is ArduPilot's (its folder is ardupilot/modules/top, for its evidence). -/
def servedTop (_ : Unit := ()) : Except String Node := do
  let n ← Ardupilot.Harnesses.InnerLoopC.system
  return .module { n.view with name := "top", exe := "build/top/top_serve", stack := .ardupilot,
                               doc := "ardupilot/Top.lean compiled, in serve mode" }

/-- The registered nodes. A new module is a folder STACK/modules/NAME with a Module.lean, a new
system a folder STACK/harnesses/NAME with a Harness.lean (or Composed.lean), STACK one of
ardupilot, px4, sim; each is imported above and listed here (tools/import_node.sh prints both
lines for a node brought in from an old-layout copy). -/
def registry : List (String × (Unit → Except String Node)) :=
  -- ArduPilot
  [entry (.module Ardupilot.Modules.RatePid.module),
   entry (.module Ardupilot.Modules.Mixer.module),
   entry (.module Ardupilot.Modules.Position.module),
   entry (.module Ardupilot.Modules.Estimator.module),
   entry (.module Ardupilot.Modules.EstScenario.module),
   entry (.module Ardupilot.Modules.Attitude.module),
   entry (.module Ardupilot.Modules.Guidance.module),
   entry (.module Ardupilot.Modules.Loiter.module),
   entry (.module Ardupilot.Modules.Script.module),
   entry (.module Ardupilot.Modules.TruthEst.module),
   entry (.module Ardupilot.Modules.Supervisor.module),
   entry (.system Ardupilot.Harnesses.Rate.system),
   entry (.system Ardupilot.Harnesses.InnerLoop.system),
   composed "rate_c" (fun _ => Ardupilot.Harnesses.RateC.system),
   composed "inner_loop_c" (fun _ => Ardupilot.Harnesses.InnerLoopC.system),
   composed "top" (fun _ => servedTop),
   composed "closed_inner" (fun _ => Ardupilot.Harnesses.ClosedInner.system),
   composed "est_loop" (fun _ => Ardupilot.Harnesses.EstLoop.system),
   composed "ap_ctl" (fun _ => Ardupilot.Harnesses.ApCtl.system),
   composed "ap_flight" (fun _ => Ardupilot.Harnesses.ApFlight.system),
   composed "ap_full" (fun _ => Ardupilot.Harnesses.ApFull.system),
   composed "ap_full_ekf" (fun _ => Ardupilot.Harnesses.ApFullEkf.system),
   composed "ap_vehicle" (fun _ => Ardupilot.Harnesses.ApFormation.vehicle),
   composed "ap_formation" (fun _ => Ardupilot.Harnesses.ApFormation.system),
   -- PX4
   entry (.module Px4.Modules.Px4Rate.module),
   entry (.module Px4.Modules.Px4Alloc.module),
   entry (.module Px4.Modules.Px4Sensors.module),
   entry (.module Px4.Modules.Px4SimIn.module),
   entry (.module Px4.Modules.Px4SimOut.module),
   entry (.module Px4.Modules.Px4Ekf2.module),
   entry (.module Px4.Modules.Px4Att.module),
   entry (.module Px4.Modules.Px4Pos.module),
   entry (.module Px4.Modules.Px4DriveAtt.module),
   entry (.module Px4.Modules.Px4DrivePos.module),
   entry (.module Px4.Modules.Px4DriveAuto.module),
   entry (.module Px4.Modules.Px4Fmm.module),
   entry (.module Px4.Modules.Px4Land.module),
   entry (.module Px4.Modules.Px4Commander.module),
   entry (.module Px4.Modules.Px4DriveCmd.module),
   entry (.module Px4.Modules.Px4Navigator.module),
   entry (.module Px4.Modules.Px4MergeAck.module),
   entry (.module Px4.Modules.Px4DriveNav.module),
   entry (.module Px4.Modules.Px4Mavlink.module),
   entry (.module Px4.Modules.Px4CmdWindow.module),
   composed "px4_inner" (fun _ => Px4.Harnesses.Px4Inner.system),
   composed "px4_closed_rate" (fun _ => Px4.Harnesses.Px4ClosedRate.system),
   composed "px4_est" (fun _ => Px4.Harnesses.Px4Est.system),
   composed "px4_est_flying" (fun _ => Px4.Harnesses.Px4Est.flyingSystem),
   composed "px4_att_loop" (fun _ => Px4.Harnesses.Px4AttLoop.system),
   composed "px4_pos_loop" (fun _ => Px4.Harnesses.Px4PosLoop.system),
   composed "px4_auto_loop" (fun _ => Px4.Harnesses.Px4AutoLoop.system),
   composed "px4_cmd_loop" (fun _ => Px4.Harnesses.Px4CmdLoop.system),
   composed "px4_nav_loop" (fun _ => Px4.Harnesses.Px4NavLoop.system),
   composed "px4_full" (fun _ => Px4.Harnesses.Px4Full.system),
   composed "px4_vehicle" (fun _ => Px4.Harnesses.Px4Formation.vehicle),
   composed "px4_formation" (fun _ => Px4.Harnesses.Px4Formation.system),
   -- the simulator, shared
   entry (.module Sim.Modules.PlantSim.module),
   entry (.module Sim.Modules.PlantFormation.module)]

/-- The composed systems by stack, for `harness list` (which does not compose them). -/
def systemStacks : List (String × Stack) :=
  (["rate_c", "inner_loop_c", "closed_inner", "est_loop", "ap_ctl", "ap_flight", "ap_full",
    "ap_full_ekf"].map (·, .ardupilot)) ++
  (["px4_inner", "px4_closed_rate", "px4_est", "px4_est_flying", "px4_att_loop", "px4_pos_loop",
    "px4_auto_loop", "px4_cmd_loop", "px4_nav_loop", "px4_full", "px4_vehicle", "px4_formation"].map (·, .px4))

/-- The `harness` command line. -/
def main (args : List String) : IO UInt32 :=
  Cli.dispatch { nodes := registry, systems := systemStacks, prog := "harness" } args
