import Harness.Compose
import sim.modules.plant_sim.Module
import ardupilot.modules.est_scenario.Module
import ardupilot.modules.estimator.Module

/-! # est_loop: the estimator against the simulator's truth

`composeAll "est_loop" [plant_sim, est_scenario, estimator]`. In one tick the plant steps (the
motors at the scenario's PWM of the previous tick), the scenario reads the plant's time, and the
estimator reads the plant's sensor samples and the scenario's arming state, all by name. The
scenario (ardupilot/modules/est_scenario, a test fixture, not ArduPilot code) holds the motors off and the
vehicle disarmed, then runs all four motors at `hover_pwm`, armed and flying, from
`hover_from_us` to `hover_until_us`: the clause language cannot schedule an input over time.

The estimator's own guarantee is carried by composition; this system adds the tracking clauses,
which only this composite can state: the plant outputs the true state next to the samples.

Frames. plant_sim's position is relative to home (the gorge's origin), the estimator's to the EKF
origin, which EKF3 sets at the GPS position of the vehicle when the GPS checks pass (about 18 s
after init); the vehicle rests at the plan's start until then. So the true position relative to
the EKF origin is the plant's position minus its rest position `restN`, `restE`, `restD`
(plant_sim's position after `init`: (0.0013, 0.0002, -0.1264) m, the same in every case; the
vehicle creeps by about 2 cm on the ground over a minute, and the GPS position is rounded to
1e-7 deg, about 1 cm, both within the bounds). Down: the EKF's height datum is the barometer's
calibration at boot, the rest height.

When the tracking clauses apply (measured in the campaigns of ardupilot/harnesses/est_loop/evidence; the
times are the same with noise on and off):
* the boot ends at step 2191 (5.48 s: barometer calibration 1.6 s, gyro calibration 3.8 s);
* EKF3 starts 1 s after its first update and reports attitude at step 3727 (9.3 s);
* the origin is set at step 7042 (17.6 s);
* GPS is used (flags.using_gps) from step 18007 (45.0 s).
Before the boot every estimate output is 0 (the estimator's zero_before_boot). -/

namespace Ardupilot.Harnesses.EstLoop

open Harness Harness.Contract.Lang

private def v (n : String) : Expr := .var n

def restN : Expr := 0.0013
def restE : Expr := 0.0002
def restD : Expr := -0.1264

/-- cos(1 deg / 2): an attitude error below 1 deg. -/
def cosHalfAttBound : Expr := 0.99996192

/-- The tracking clauses. Measured worst cases (6 cases of 23,600 steps, noise off and on, at rest
and with 4 s of flight at PWM 1620 and 1640): attitude 0.40 deg, velocity 0.17 m/s, horizontal
position 0.21 m, vertical position 0.44 m. The bounds: 1 deg, 0.5 m/s, 0.75 m, 1.0 m. -/
def tracking : List Clause := [
  -- |q_est . q_true| = cos(angle / 2), the angle between the two attitudes
  ⟨"attitude_tracks", ¬. v "est_ekf_attitude" ∨.
      cosHalfAttBound ≤. abs (v "est_q1" * v "q1" + v "est_q2" * v "q2" + v "est_q3" * v "q3" +
        v "est_q4" * v "q4")⟩,
  ⟨"velocity_tracks", ¬. v "est_ekf_using_gps" ∨.
      (abs (v "est_vel_n" - v "vel_n") ≤. 0.5 ∧. abs (v "est_vel_e" - v "vel_e") ≤. 0.5 ∧.
        abs (v "est_vel_d" - v "vel_d") ≤. 0.5)⟩,
  ⟨"position_tracks", ¬. (v "est_ekf_using_gps" ∧. v "est_pos_ok") ∨.
      (abs (v "est_pos_n" - (v "pos_n" - restN)) ≤. 0.75 ∧.
        abs (v "est_pos_e" - (v "pos_e" - restE)) ≤. 0.75 ∧.
        abs (v "est_pos_d" - (v "pos_d" - restD)) ≤. 1)⟩,
  -- the mixer's assumption (ardupilot/modules/mixer: 0 ≤ air_density_ratio ≤ 2), which the estimator alone
  -- cannot promise (ardupilot/modules/estimator, guaranteeAsFirstStated): at the gorge (4302 m) the 1976
  -- atmosphere gives 0.648
  ⟨"air_density_range", 0 ≤. v "air_density_ratio" ∧. v "air_density_ratio" ≤. 2⟩]

/-- How often the tracking clauses applied. -/
def trackingCoverage : List Clause := [
  ⟨"attitude_estimated", v "est_ekf_attitude"⟩,
  ⟨"gps_aided", v "est_ekf_using_gps" ∧. v "est_pos_ok"⟩,
  ⟨"flying_aided", v "est_ekf_using_gps" ∧. v "armed"⟩]

private def stockClauses : List Clause :=
  Ardupilot.Modules.Estimator.stockParams ++ [
    ⟨"no_commands", conj (["cmd_estimator_set_takeoff_expected",
      "cmd_estimator_set_touchdown_expected", "cmd_estimator_set_home",
      "cmd_estimator_reset_height_datum", "cmd_estimator_request_yaw_reset",
      "cmd_estimator_set_terrain_hgt_stable"].map fun c =>
        ¬. v c)⟩]
where conj : List Expr → Expr
  | [] => tt
  | [e] => e
  | e :: es => e ∧. conj es

private def regime (name doc : String) (noise : Bool) (pwmLo pwmHi untilUs : Expr) : Regime where
  name := name
  doc := doc
  clauses := stockClauses ++ [
    ⟨"noise", v "noise_on" =. (if noise then tt else ff)⟩,
    ⟨"pwm", pwmLo ≤. v "hover_pwm" ∧. v "hover_pwm" ≤. pwmHi⟩,
    ⟨"flight_window", v "hover_from_us" =. 55000000 ∧. v "hover_until_us" =. untilUs⟩]

/-- The regimes: ArduCopter's defaults, no commands, noise off or on; at rest and disarmed
throughout (an empty flight window) or flying from 55 s to 59 s at a fixed PWM between 1600
(just above hover: the plant hovers at actuator 0.592, PWM 1592) and 1650 (climbing). -/
def regimes : List Regime := [
  regime "rest_quiet" "stock, at rest and disarmed, no sensor noise" false 1000 1000 55000000,
  regime "rest_noisy" "stock, at rest and disarmed, sensor noise" true 1000 1000 55000000,
  regime "hover_quiet" "stock, rest then 4 s at a fixed PWM, no sensor noise" false 1600 1650
    59000000,
  regime "hover_noisy" "stock, rest then 4 s at a fixed PWM, sensor noise" true 1600 1650
    59000000]

/-- The simulator's IMU full scale within what the estimator assumes of its samples
(`imu_range`: |specific force| ≤ 160 m/s/s, |rate| ≤ 35 rad/s): at most 16.3 g and 2005 deg/s, or
the defaults (0: 16 g, 2000 deg/s). A composite assumption on plant_sim's parameters; with it
plant_sim's guarantee `imu_full_scale` discharges `imu_range` (added 2026-11-18: before, the
simulator's contact spike at touchdown, 250 to 320 m/s/s, failed it). -/
def imuForEstimator : Clause :=
  ⟨"imu_full_scale_for_estimator", (v "imu_acc_fs_g" =. 0 ∨. v "imu_acc_fs_g" ≤. 16.3) ∧.
    (v "imu_gyro_fs_dps" =. 0 ∨. v "imu_gyro_fs_dps" ≤. 2005)⟩

/-- The discharge of the estimator's `imu_range` in a composite with plant_sim. -/
def imuDischarge : Discharge :=
  { path := "estimator", clause := "imu_range", kind := "assumption",
    by_ := ["plant_sim.imu_full_scale", "assume.imu_full_scale_for_estimator"],
    note := "16.3 g = 159.85 m/s/s ≤ 160; 2005 deg/s = 34.99 rad/s ≤ 35" }

def system (_ : Unit := ()) : Except String Node := do
  let n ← composeAll "est_loop" [.module Sim.Modules.PlantSim.module,
    .module Ardupilot.Modules.EstScenario.module, .module Ardupilot.Modules.Estimator.module]
  let n ← withAssume n [imuForEstimator]
  let n := withDischarges n [imuDischarge]
  match n with
  | .system s => return .system { s with
      doc := "the estimator against plant_sim's truth, with a scripted flight",
      contract := { s.contract with guarantee := s.contract.guarantee ++ tracking },
      regimes := s.regimes ++ regimes,
      coverage := s.coverage ++ trackingCoverage }
  | .module _ => throw "est_loop: composeAll did not return a system"

end Ardupilot.Harnesses.EstLoop
