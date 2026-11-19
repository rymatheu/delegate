import Harness.Compose
import ardupilot.harnesses.ap_full.Composed
import ardupilot.modules.estimator.Module
import ardupilot.harnesses.est_loop.Composed
import ardupilot.modules.loiter.Module

/-! # ap_full_ekf: the whole stack with the real estimator

`ardupilot/harnesses/ap_full` (copied from the supervisor agent's copy h-sup) with the estimator stage
(`ardupilot/modules/estimator`, copied from h-est: the real AP_InertialSensor front end, AP_AHRS, EKF3 and
sensor front ends) in the place of the `truth_est` fixture:
`plant_sim → estimator → rate_c → mixer → supervisor → guidance → loiter → position →
attitude` (the loiter stage, AC_Loiter, added beside the guidance stage; it reads the
estimator's `est_gnd_spd_limit`). The
estimator reads the simulator's raw sensor samples of the tick and the supervisor's `armed`,
`likely_flying` (Copter::set_land_complete) and `cmd_estimator_*` commands of the previous tick;
the ground-effect hints, which the supervisor's build does not make, are fixed off (`estimator`
below). The controller stages read the estimator's output names directly (h-apctl reconciled
them). -/

namespace Ardupilot.Harnesses.ApFullEkf

open Harness

/-- The estimator with the ground-effect hints off: AP_GroundEffect (AP_AHRS::set_takeoff_ /
touchdown_expected) is switched off in the supervisor's build (AP_GROUNDEFFECT_ENABLED = 0,
ardupilot/modules/supervisor/probe/features.txt), so nothing calls them. -/
def estimator (_ : Unit := ()) : Except String Node :=
  fix (.module Ardupilot.Modules.Estimator.module)
    [("cmd_estimator_set_takeoff_expected", .bool false),
     ("cmd_estimator_set_takeoff_expected_b", .bool false),
     ("cmd_estimator_set_touchdown_expected", .bool false),
     ("cmd_estimator_set_touchdown_expected_b", .bool false)]

/-- The obligations the estimator's code-fact guarantees discharge (its `guaranteeCodeRanges`
and `outputs_finite`). Listed first: the loiter stage's `est_yaw_range`, a hypothesis in
`ApFull.loiterDischarges` (where `truth_est` reports the yaw), is discharged here. -/
def estimatorDischarges : List Discharge := [
  { path := "supervisor", clause := "estimate_finite", kind := "guarantee",
    by_ := ["estimator.outputs_finite"] },
  { path := "supervisor", clause := "est_text_range", kind := "guarantee",
    by_ := ["estimator.text_range"],
    note := "the estimator's status text (length ≤ 50, severity ≤ 7), same tick" },
  { path := "loiter", clause := "est_yaw_range", kind := "guarantee",
    by_ := ["estimator.euler_wrapped"] },
  { path := "position", clause := "est_yaw_range", kind := "guarantee",
    by_ := ["estimator.euler_wrapped", "estimator.trig_range"] },
  { path := "position", clause := "est_scalers_range", kind := "guarantee",
    by_ := ["estimator.gain_scalers_range"] },
  { path := "position", clause := "est_reset_counts_range", kind := "guarantee",
    by_ := ["estimator.reset_counts_u16"] }]

/-- The full stack with the real estimator; the simulator's IMU full scale within what the
estimator assumes (`EstLoop.imuForEstimator`), which discharges its `imu_range`. -/
def system (_ : Unit := ()) : Except String Node := do
  let n ← composeAll "ap_full_ekf" [← Ardupilot.Harnesses.ApFull.plant,
    ← estimator, ← Ardupilot.Harnesses.RateC.system,
    ← Ardupilot.Harnesses.ApFull.mixer, ← Ardupilot.Harnesses.ApFull.supervisor,
    .module Ardupilot.Modules.Guidance.module, ← Ardupilot.Harnesses.ApFull.loiterInit,
    ← Ardupilot.Harnesses.ApFull.position,
    ← Ardupilot.Harnesses.ApFull.attitude]
  let n ← withAssume n [Ardupilot.Harnesses.EstLoop.imuForEstimator]
  return withDischarges n (estimatorDischarges ++ [Ardupilot.Harnesses.EstLoop.imuDischarge,
    { path := "loiter", clause := "gnd_spd_limit_range", kind := "guarantee",
      by_ := ["estimator.gnd_spd_limit_range"],
      note := "[0, 400] m/s from the estimator, same tick, within [0, 1000]" }] ++
    Ardupilot.Harnesses.ApFull.loiterDischarges ++
    -- the chain's shared table, the gyro bounded by the estimator's gyro_range (|ω| ≤ 1e4)
    Ardupilot.Harnesses.Chain.discharges (some "estimator.gyro_range") ++
    Ardupilot.Harnesses.Chain.supervised)

end Ardupilot.Harnesses.ApFullEkf
