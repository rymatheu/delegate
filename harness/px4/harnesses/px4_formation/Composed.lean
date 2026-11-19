import Harness.Compose
import px4.harnesses.px4_full.Composed
import sim.modules.plant_formation.Module

/-! # px4_formation: two PX4 stacks in one gorge

The two-vehicle system of the gorge formation scenarios (docs/11-two-vehicles.md):

    composeAll "px4_formation" [plant_formation, v1, v2]

`px4_vehicle` is px4_full without its plant: [px4_sim_in, px4_sensors, px4_rate, px4_alloc,
px4_ekf2, px4_att, px4_mavlink, px4_cmd_window, px4_navigator, px4_fmm, px4_pos, px4_land,
px4_commander, px4_merge_ack, px4_sim_out], with px4_full's discharges (navigator's storage and
command window, the generated widths and slots). px4_full's truth clause (EKF2 against the
simulator's position) reads the plant, so it is the formation's, once per vehicle
(`ekf2_horizontal_vs_truth_v1`, `_v2`). `v1` and `v2` are two instances
of it, every field prefixed `v1_` or `v2_` except the plant's clock `t_us`, which both read. PX4's
bridges read plant_sim's names, so after `inst` they read plant_formation's (`v1_imu0_ax`,
`v1_gps_lat_e7`, ...) and write its inputs (`v1_pwm0`, through `prev`, 1000 at the first tick); no
rename. Each vehicle has its own parameters, MAVLink byte ports (`vN_mavlink_rx_*`, `vN_mavlink_tx_*`)
and in-process dataman (RAM): nothing is shared between the two stacks but the clock, and nothing
on disk. The relay gives vehicle 2 `v2_MAV_SYS_ID` = 2 (px4/gorge/formation_relay.sh).

The contract adds `formationClauses` (the same two as ap_formation's), monitored at every tick (uncovered in the formal
link): `min_separation` (true positions at least 1.5 m apart) and `wall_clearance` (each vehicle at
least 0.5 m from the gorge's side surfaces, the plant's `vN_wall_clear`). The two stacks do not read
each other, so they are stepped at the same time (`concurrently`). -/

namespace Px4.Harnesses.Px4Formation

open Harness Harness.Contract.Lang

/-- One vehicle: px4_full's children after plant_sim, with px4_full's discharges and truth clause. -/
def vehicle (_ : Unit := ()) : Except String Node := do
  let n ← composeAll "px4_vehicle"
    [.module Px4.Modules.Px4SimIn.module,
     .module Px4.Modules.Px4Sensors.module, .module Px4.Modules.Px4Rate.module,
     .module Px4.Modules.Px4Alloc.module, .module Px4.Modules.Px4Ekf2.module,
     .module Px4.Modules.Px4Att.module, .module Px4.Modules.Px4Mavlink.module,
     .module Px4.Modules.Px4CmdWindow.module,
     .module Px4.Modules.Px4Navigator.module, .module Px4.Modules.Px4Fmm.module,
     .module Px4.Modules.Px4Pos.module, .module Px4.Modules.Px4Land.module,
     .module Px4.Modules.Px4Commander.module, .module Px4.Modules.Px4MergeAck.module,
     ← Px4.Harnesses.Px4ClosedRate.simOut]
  let n := withDischarges n (Px4.Harnesses.Chain.storage ++ Px4.Harnesses.Chain.window)
  return Px4.Harnesses.Chain.withGlue n

private def v (n : String) : Expr := .var n

/-- The squared distance between the two vehicles' true positions, m² (NED about the gorge origin). -/
def sep2 : Expr :=
  (v "v1_pos_n" - v "v2_pos_n") * (v "v1_pos_n" - v "v2_pos_n") +
  (v "v1_pos_e" - v "v2_pos_e") * (v "v1_pos_e" - v "v2_pos_e") +
  (v "v1_pos_d" - v "v2_pos_d") * (v "v1_pos_d" - v "v2_pos_d")

/-- What the formation is to achieve (monitored at every tick; uncovered in the link): at least
1.5 m between the vehicles (squared, 2.25 m², in binary32; the X500 spans about 0.75 m with its
propellers) and at least 0.5 m from each vehicle to the gorge's side surfaces. -/
def formationClauses : List Clause := [
  ⟨"min_separation", (2.25 : Expr) ≤. sep2⟩,
  ⟨"wall_clearance", (0.5 : Expr) ≤. v "v1_wall_clear" ∧. (0.5 : Expr) ≤. v "v2_wall_clear"⟩]

/-- The fields both instances read unprefixed: the plant's clock. -/
def shared : List String := ["t_us"]

def system (_ : Unit := ()) : Except String Node := do
  let st ← vehicle
  let n ← composeAll "px4_formation"
    [.module Sim.Modules.PlantFormation.module, ← inst st "v1" shared, ← inst st "v2" shared]
  let truth := (Px4.Harnesses.Px4AutoLoop.truthClauses.filter (·.name == "ekf2_horizontal_vs_truth")).flatMap
    fun c => ["v1", "v2"].map fun vv =>
      { (c.rename fun f => if shared.contains f then f else s!"{vv}_{f}") with name := s!"{c.name}_{vv}" }
  let n ← withGuarantee n (formationClauses ++ truth)
  return concurrently n

end Px4.Harnesses.Px4Formation
