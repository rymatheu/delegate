import px4.modules.px4_sensors.Ports

/-! # px4_sensors: PX4's sensors module

PX4's `sensors` module (src/modules/sensors and the work items it starts), real and unmodified,
PX4 v1.17.0, behind the generic shim. Raw sensor topics in (instance 0), the vehicle-level topics
the controllers and the estimator read out. -/

namespace Px4.Modules.Px4Sensors

open Harness Harness.Contract.Lang

/-- A message was published on raw-sensor topic `t` this tick: the queued sensor topics have one
slot (`<t>_count`, px4.txt `slots 1`), sensor_gps an `_updated` flag. -/
def published (t : String) : Expr :=
  if t == "sensor_gps" then Expr.var s!"{t}_updated" else (1 : Expr) ≤. Expr.var s!"{t}_count"

def guarantee : List Clause := [
  ⟨"rates_finite", ¬. "vehicle_angular_velocity_updated" ∨.
    (finite "vehicle_angular_velocity_xyz_0" ∧. finite "vehicle_angular_velocity_xyz_1" ∧.
     finite "vehicle_angular_velocity_xyz_2")⟩,
  ⟨"rates_answer_gyro", ¬. "vehicle_angular_velocity_updated" ∨. published "sensor_gyro"⟩,
  ⟨"no_px4_error", "px4_sensors_errors" =. 0⟩]

private def calOk (kind : String) (id : Nat) : Expr :=
  (List.range 3).foldl (fun e i => e ∧. calSlot kind (i + 1) id) (calSlot kind 0 id)
where calSlot (kind : String) (i id : Nat) : Expr :=
  Expr.var s!"CAL_{kind}{i}_ID" =. 0 ∨. Expr.var s!"CAL_{kind}{i}_ID" =. Expr.lit (Float32.ofNat id).toBits

/-- The first statement. Its campaign (seed 1, 100 x 100, no regime) refuted no_px4_error at 63% of
the steps: with random calibration ids in all four slots, a device whose id is in none of them gets
"no BARO calibration slots available" (sensor_calibration/Barometer.cpp, set_device_id). Kept for
the record. -/
def contractAsFirstStated : Contract where
  assume := Ports.widths ++ Ports.paramRanges ++ [
    ⟨"gyro_finite", ¬. published "sensor_gyro" ∨.
      (finite "sensor_gyro_x" ∧. finite "sensor_gyro_y" ∧. finite "sensor_gyro_z")⟩]
  guarantee := guarantee

/-- `name` contains `part`. -/
private def has (name part : String) : Bool := (name.splitOn part).length > 1

/-- The calibration parameters of IMU and compass (offsets, scales, off-diagonals, board offsets),
which PX4 documents without a range, within a physical range: offsets within 100 (rad/s, m/s²,
Gauss, or degrees for SENS_BOARD_*_OFF), scales within [0.1, 10]. -/
def calibrationPhysical : Expr :=
  let ps := (Ports.params.toList.map (·.name)).filter fun n =>
    (has n "CAL_" || has n "SENS_BOARD_") && (has n "OFF" || has n "SCALE" || has n "ODIAG")
  ps.foldl (fun e n => e ∧. (if has n "SCALE" then (0.1 : Expr) ≤. n ∧. Expr.var n ≤. 10
    else abs n ≤. 100)) tt

/-- A clause about a topic's fields, which mean something only when a message was published. -/
private def sent (t : String) (e : Expr) : Expr := ¬. published t ∨. e

private def stampsOrdered (t : String) : Expr :=
  ¬. published t ∨. Expr.var s!"{t}_timestamp_sample" ≤. Expr.var s!"{t}_timestamp"

/-- The contract. Against the first statement, as the second round of campaigns (seeds 5 and 6)
showed (each about a topic's fields when a message was published on it, since the fields of a
topic not published this tick mean nothing; px4_closed_rate seed 1 found the first version of
`sitl_devices` failing on ticks without a baro or compass message):
* the raw sensors are the SITL devices, and every calibration slot is free or holds that device (as
  after PX4's SITL start script);
* a message's sample time is not after its publication time (else "timestamp < timestamp_sample",
  voted_sensors_update.cpp);
* SENS_BOARD_ROT ≥ 0: sensor_params.c documents `@min -1`, but
  sensor_calibration/Utilities.cpp:225-229 rejects -1 ("invalid SENS_BOARD_ROT") on every sample.
  A PX4 inconsistency between the documented range and the code;
* IMU samples within 1000 rad/s and 10⁴ m/s² (seed 6 drove the integrators to ∞ − ∞ with
  samples near the binary32 maximum, giving NaN rates).
A third round (seeds 9-12) added:
* one sample per IMU message, as a simulator driver (and px4_sim_in) publishes: `samples` enters
  VehicleAngularVelocity's sample-rate estimate, and with 0 (seed 11) or 205 samples per 2.5 ms
  message (82 kHz, seed 16) its filters, designed for that rate, diverge to ∞;
* (not expressible: the contract language has no previous tick) sample times increase from one
  message to the next; random times give "timestamp error" (seeds 14, 15), so no_px4_error is
  backed only by campaigns whose regime makes the times increase (`flight`, `sitl_flight`);
* calibration offsets and scales within a physical range (`calibrationPhysical`): with
  CAL_GYRO2_ID equal to the device and CAL_GYRO2_YOFF = 3.4e38 (no documented range) the corrected
  rate is ∞ (seeds 19-21; found by resetting one parameter at a time to its default);
* healthy sensors: error_count 0 and finite readings (with a growing error count or a −∞ pressure the
  data validator declares the sensor failed and logs "BARO #0 failed: ERR CNT", seed 10: PX4
  reporting a failed sensor, which is its job). -/
def contract : Contract where
  assume := contractAsFirstStated.assume ++ [
    ⟨"calibration_physical", calibrationPhysical⟩,
    ⟨"stamps_ordered", stampsOrdered "sensor_gyro" ∧. stampsOrdered "sensor_accel" ∧.
      stampsOrdered "sensor_baro" ∧. stampsOrdered "sensor_mag" ∧. stampsOrdered "sensor_gps"⟩,
    ⟨"board_rotation_implemented", 0 ≤. "SENS_BOARD_ROT"⟩,
    ⟨"one_sample_per_message", sent "sensor_gyro" ("sensor_gyro_samples" =. 1) ∧.
      sent "sensor_accel" ("sensor_accel_samples" =. 1)⟩,
    ⟨"sensors_healthy", sent "sensor_gyro" ("sensor_gyro_error_count" =. 0) ∧.
      sent "sensor_accel" ("sensor_accel_error_count" =. 0 ∧. finite "sensor_accel_x" ∧.
        finite "sensor_accel_y" ∧. finite "sensor_accel_z") ∧.
      sent "sensor_baro" ("sensor_baro_error_count" =. 0 ∧. finite "sensor_baro_pressure" ∧.
        finite "sensor_baro_temperature") ∧.
      sent "sensor_mag" ("sensor_mag_error_count" =. 0 ∧. finite "sensor_mag_x" ∧.
        finite "sensor_mag_y" ∧. finite "sensor_mag_z")⟩,
    ⟨"imu_physical", sent "sensor_gyro" (abs "sensor_gyro_x" ≤. 1000 ∧. abs "sensor_gyro_y" ≤. 1000 ∧.
      abs "sensor_gyro_z" ≤. 1000) ∧. sent "sensor_accel" (abs "sensor_accel_x" ≤. 10000 ∧.
      abs "sensor_accel_y" ≤. 10000 ∧. abs "sensor_accel_z" ≤. 10000)⟩,
    ⟨"sitl_devices", sent "sensor_gyro" ("sensor_gyro_device_id" =. 1310988) ∧.
      sent "sensor_accel" ("sensor_accel_device_id" =. 1310988) ∧.
      sent "sensor_mag" ("sensor_mag_device_id" =. 197388) ∧.
      sent "sensor_baro" ("sensor_baro_device_id" =. 6620172)⟩,
    ⟨"calibration_slots", calOk "ACC" 1310988 ∧. calOk "GYRO" 1310988 ∧. calOk "MAG" 197388 ∧.
      calOk "BARO" 6620172⟩]
  guarantee := guarantee

/-- The parameters PX4's SITL start script sets for the simulated sensors
(ROMFS/px4fmu_common/init.d-posix/rcS:147-155: accel and gyro 0 are device 1310988, compass 0 is
197388 with priority 50), and the multicopter default IMU_GYRO_RATEMAX = 800
(init.d/rc.mc_defaults:13-15, included by the X500 airframe); PX4's defaults otherwise. -/
def sitlNames : List String :=
  ["CAL_ACC0_ID", "CAL_GYRO0_ID", "CAL_MAG0_ID", "CAL_MAG0_PRIO", "IMU_GYRO_RATEMAX"]

def sitlParams : List Clause :=
  (Ports.paramDefaults.filter fun c => !sitlNames.any (fun n => c.name == s!"default_{n}")) ++ [
    ⟨"sitl_imu_ids", "CAL_ACC0_ID" =. 1310988 ∧. "CAL_GYRO0_ID" =. 1310988⟩,
    ⟨"sitl_mag", "CAL_MAG0_ID" =. 197388 ∧. "CAL_MAG0_PRIO" =. 50⟩,
    ⟨"mc_gyro_rate", "IMU_GYRO_RATEMAX" =. 800⟩]

/-- Flight: a gyro and an accel message every 400 Hz tick from the SITL devices, the clock
advancing 2500 us per step. -/
def flight : Regime where
  name := "flight"
  doc := "IMU messages from the SITL devices every 400 Hz tick"
  clauses := [
    ⟨"imu_every_tick", "sensor_gyro_count" =. 1 ∧. "sensor_accel_count" =. 1⟩,
    -- the contract's per-message facts stated per field, so that sampling meets them directly
    ⟨"devices", "sensor_gyro_device_id" =. 1310988 ∧. "sensor_accel_device_id" =. 1310988 ∧.
      "sensor_mag_device_id" =. 197388 ∧. "sensor_baro_device_id" =. 6620172⟩,
    ⟨"one_sample", "sensor_gyro_samples" =. 1 ∧. "sensor_accel_samples" =. 1⟩,
    ⟨"no_errors", "sensor_gyro_error_count" =. 0 ∧. "sensor_accel_error_count" =. 0 ∧.
      "sensor_baro_error_count" =. 0 ∧. "sensor_mag_error_count" =. 0⟩]
  -- the clock and the IMU sample times advance together, 2500 us per step from 1 s
  hints := ["t_us", "sensor_gyro_timestamp", "sensor_gyro_timestamp_sample", "sensor_accel_timestamp",
    "sensor_accel_timestamp_sample"].map fun f => .increasing f 1000000 2500 2500

/-- SITL: PX4's defaults with the SITL calibration ids, flight's IMU messages, rates within
10 rad/s and specific force within 40 m/s². -/
def sitlFlight : Regime where
  name := "sitl_flight"
  doc := "PX4 defaults and SITL device ids, IMU every tick, moderate motion"
  clauses := sitlParams ++ flight.clauses ++ [
    ⟨"moderate_rates", abs "sensor_gyro_x" ≤. 10 ∧. abs "sensor_gyro_y" ≤. 10 ∧. abs "sensor_gyro_z" ≤. 10⟩,
    ⟨"moderate_accel", abs "sensor_accel_x" ≤. 40 ∧. abs "sensor_accel_y" ≤. 40 ∧. abs "sensor_accel_z" ≤. 40⟩]
  hints := flight.hints

def module : Module where
  name := "px4_sensors"
  doc := "PX4 sensors (v1.17.0), unmodified, behind the generic uORB shim"
  params := Ports.params
  input := Ports.input
  output := Ports.output
  contract := { contract with guarantee := contract.guarantee ++ Ports.outWidths }
  exe := "build/modules/px4_sensors/px4_sensors"
  stack := .px4
  regimes := [flight, sitlFlight]

end Px4.Modules.Px4Sensors
