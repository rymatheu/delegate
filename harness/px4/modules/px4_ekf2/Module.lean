import px4.modules.px4_ekf2.Ports

/-! # px4_ekf2: PX4's EKF2, one instance

PX4's `ekf2` module (src/modules/ekf2 with its EKF library, output predictor, bias and yaw
estimators), real and unmodified, PX4 v1.17.0, single instance (SENS_IMU_MODE = 1): run by its work
queue on every `sensor_combined`, fusing the compass, baro and GPS topics of PX4's sensors module. -/

namespace Px4.Modules.Px4Ekf2

open Harness Harness.Contract.Lang

def guarantee : List Clause := [
  ⟨"attitude_unit", ¬. "vehicle_attitude_updated" ∨.
    abs ("vehicle_attitude_q_0" * "vehicle_attitude_q_0" + "vehicle_attitude_q_1" * "vehicle_attitude_q_1" +
      "vehicle_attitude_q_2" * "vehicle_attitude_q_2" + "vehicle_attitude_q_3" * "vehicle_attitude_q_3" - 1) ≤. 1e-5⟩,
  ⟨"attitude_answers_imu", ¬. "vehicle_attitude_updated" ∨. "sensor_combined_updated"⟩,
  ⟨"no_px4_error", "px4_ekf2_errors" =. 0⟩]

/-- Single instance: SENS_IMU_MODE = 1 and SENS_MAG_MODE = 1 (EKF2::task_spawn, EKF2.cpp:2784-2815).
With either at 0 EKF2 starts in multi-instance mode and task_spawn waits, in a loop of px4_usleep,
up to 30 s of hrt time for the vehicle_imu / vehicle_magnetometer instances; the shim's px4_usleep
does not advance the clock, so that start never returns (a campaign with random parameters hung at
its first such case, seed 1 case 3). Multi-instance EKF2 is outside this module. -/
def contract : Contract where
  assume := Ports.widths ++ Ports.paramRanges ++
    [⟨"single_instance", "SENS_IMU_MODE" =. 1 ∧. "SENS_MAG_MODE" =. 1⟩]
  guarantee := guarantee

def module : Module where
  name := "px4_ekf2"
  doc := "PX4 ekf2 (v1.17.0), single instance, unmodified, behind the generic uORB shim"
  params := Ports.params
  input := Ports.input
  output := Ports.output
  contract := { contract with guarantee := contract.guarantee ++ Ports.outWidths }
  exe := "build/modules/px4_ekf2/px4_ekf2"
  stack := .px4

end Px4.Modules.Px4Ekf2
