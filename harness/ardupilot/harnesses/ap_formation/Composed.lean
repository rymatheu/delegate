import Harness.Compose
import ardupilot.harnesses.ap_full_ekf.Composed
import sim.modules.plant_formation.Module

/-! # ap_formation: two ArduCopter stacks in one gorge

The two-vehicle system of the gorge formation scenarios (docs/11-two-vehicles.md):

    composeAll "ap_formation" [plant, v1, v2]

`plant` is `plant_formation` (two X500s in one world) with each vehicle's PWM fields named as the mixer's
(`v1_pwm0` ← `v1_pwm_1`, …, as `ApFull.plant` renames plant_sim's). `v1` and `v2` are two instances of `ap_vehicle`,
the stages of `ap_full_ekf` without its plant (estimator, rate_c, mixer, supervisor, guidance, loiter, position,
attitude, with ap_full_ekf's discharge table), every field prefixed `v1_` or `v2_` except the clock (`dt`, `now_us`,
`now_ms`, and the plant's `t_us`), which both read. Each stack reads its vehicle's plant outputs of the same tick and feeds its PWM back through
`prev` (1000 at the first tick), as in ap_full_ekf. The two stacks do not read each other, so they are stepped at the
same time (`concurrently`); the records are those of stepping them one after the other.

The contract adds what the formation is to achieve, monitored at every tick (`withGuarantee`; in the formal link these
are uncovered, `OpenCover`):
* `min_separation`: the two vehicles' true positions (NED about the gorge origin, the same frame for both) at least
  1.5 m apart, as the squared distance ≥ 2.25 m² in binary32 (the X500's span is about 0.75 m with propellers);
* `wall_clearance`: each vehicle at least 0.5 m from the gorge's side surfaces (`v*_wall_clear`, the plant's
  closest-point measure of walls and rock sides, not the floor beneath). -/

namespace Ardupilot.Harnesses.ApFormation

open Harness Harness.Contract.Lang

/-- One vehicle's stack: ap_full_ekf's stages after its plant, with its discharge table except the plant's. -/
def vehicle (_ : Unit := ()) : Except String Node := do
  let n ← composeAll "ap_vehicle" [← Ardupilot.Harnesses.ApFullEkf.estimator,
    ← Ardupilot.Harnesses.RateC.system, ← Ardupilot.Harnesses.ApFull.mixer,
    ← Ardupilot.Harnesses.ApFull.supervisor, .module Ardupilot.Modules.Guidance.module,
    ← Ardupilot.Harnesses.ApFull.loiterInit, ← Ardupilot.Harnesses.ApFull.position,
    ← Ardupilot.Harnesses.ApFull.attitude]
  return withDischarges n (Ardupilot.Harnesses.ApFullEkf.estimatorDischarges ++
    [{ path := "loiter", clause := "gnd_spd_limit_range", kind := "guarantee",
       by_ := ["estimator.gnd_spd_limit_range"],
       note := "[0, 400] m/s from the estimator, same tick, within [0, 1000]" }] ++
    Ardupilot.Harnesses.ApFull.loiterDischarges ++
    Ardupilot.Harnesses.Chain.discharges (some "estimator.gyro_range") ++
    Ardupilot.Harnesses.Chain.supervised)

/-- The clock both stacks read: the driver's (`dt`, `now_us`, `now_ms`) and the plant's `t_us`. -/
def clock : List String := ["dt", "now_us", "now_ms", "t_us"]

/-- The formation plant with each vehicle's PWM inputs named as that vehicle's mixer outputs. -/
def plant (_ : Unit := ()) : Except String Node :=
  rename (.module Sim.Modules.PlantFormation.module)
    (Sim.Modules.PlantFormation.vehicles.flatMap fun v =>
      (List.range 4).map fun i => (s!"{v}_pwm{i}", s!"{v}_pwm_{i + 1}"))

private def v (n : String) : Expr := .var n

/-- The squared distance between the two vehicles, m². -/
def sep2 : Expr :=
  (v "v1_pos_n" - v "v2_pos_n") * (v "v1_pos_n" - v "v2_pos_n") +
  (v "v1_pos_e" - v "v2_pos_e") * (v "v1_pos_e" - v "v2_pos_e") +
  (v "v1_pos_d" - v "v2_pos_d") * (v "v1_pos_d" - v "v2_pos_d")

/-- What the formation is to achieve (monitored; uncovered in the link). -/
def formationClauses : List Clause := [
  ⟨"min_separation", (2.25 : Expr) ≤. sep2⟩,
  ⟨"wall_clearance", (0.5 : Expr) ≤. v "v1_wall_clear" ∧. (0.5 : Expr) ≤. v "v2_wall_clear"⟩]

/-- The estimator's `imu_range` of each vehicle, discharged by the plant's full scale and the composite's assumption
on it, as `EstLoop.imuDischarge` in ap_full_ekf. -/
def imuDischarges : List Discharge :=
  Sim.Modules.PlantFormation.vehicles.map fun vv =>
    { path := vv, clause := "imu_range", kind := "assumption",
      by_ := [s!"plant_formation.imu_full_scale_{vv}", "assume.imu_full_scale_for_estimator"],
      note := "16.3 g = 159.85 m/s/s ≤ 160; 2005 deg/s = 34.99 rad/s ≤ 35 (per vehicle)" }

def system (_ : Unit := ()) : Except String Node := do
  let st ← vehicle
  let n ← composeAll "ap_formation" [← plant, ← inst st "v1" clock, ← inst st "v2" clock]
  let n ← withAssume n [Ardupilot.Harnesses.EstLoop.imuForEstimator]
  let n ← withGuarantee n formationClauses
  return concurrently (withDischarges n imuDischarges)

end Ardupilot.Harnesses.ApFormation
