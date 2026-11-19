import sim.modules.plant_sim.Module
import px4.modules.px4_sensors.Ports

/-! # px4_sim_in: the gorge simulator's sensor samples as PX4's raw sensor topics

The bridge from plant_sim's outputs to the topics PX4's simulator drivers publish and PX4's
`sensors` module reads (sensor_accel, sensor_gyro, sensor_baro, sensor_mag, sensor_gps, instance 0).
Its input fields are plant_sim's output fields of the same name; its output fields are px4_sensors'
input fields for those topics (the schemas are taken from both declarations, not retyped), so it
composes by name on both sides. adapter.cpp, hand-written: units, frames, timestamps and device ids.

* Frames: both are FRD body and NED world (plant_sim's doc; PX4's sensor messages); no rotation.
* IMU: sensor_accel and sensor_gyro carry the newest of plant_sim's three samples of the tick
  (`imu2_*`, after the last 1200 Hz substep), one message per tick (px4_sensors takes one slot of
  these queued topics, `<topic>_count` = 1), so samples 0 and 1 are dropped. Specific force in m/s² (−g on z at rest), rate in
  rad/s, as PX4's sensor_accel/sensor_gyro. samples = 1, temperature NaN (unknown, as PX4's
  simulators publish).
* Baro: Pa and °C as sensor_baro, when baro_fresh. Compass: mGauss to Gauss (/1000) as sensor_mag,
  when mag_fresh.
* GPS, when gps_fresh: latitude and longitude from int32 1e-7 deg to PX4's float64 degrees, carried as
  the pair of binary32 fields the generator makes for a float64 (value + rest); altitude AMSL in m;
  NED velocity; 3D fix, 10 satellites, eph 0.5 m, epv 0.8 m, velocity valid; ground speed and course
  from the velocity.
* Timestamps: timestamp = timestamp_sample = t_us, plant_sim's time of the state.
* Device ids: those PX4's SITL start script calibrates (ROMFS/px4fmu_common/init.d-posix/rcS:147-154):
  accel and gyro 1310988 (DRV_IMU_DEVTYPE_SIM, bus 1), compass 197388; baro 6620172, GPS 0. -/

namespace Px4.Modules.Px4SimIn

open Harness Harness.Contract.Lang

def plantFields : List String :=
  ["t_us"] ++ ((List.range 6).map fun i => s!"imu2_{["ax","ay","az","gx","gy","gz"][i]!}") ++
  ["baro_fresh", "baro_pa", "baro_degc", "mag_fresh", "mag_x", "mag_y", "mag_z", "gps_fresh",
   "gps_lat_e7", "gps_lon_e7", "gps_alt", "gps_vn", "gps_ve", "gps_vd"]

def topics : List String := ["sensor_accel_", "sensor_gyro_", "sensor_baro_", "sensor_mag_", "sensor_gps_"]

def input : Schema := Sim.Modules.PlantSim.output.filter fun f => plantFields.contains f.name
def output : Schema := Px4.Modules.Px4Sensors.Ports.input.filter fun f => topics.any (fun (p : String) => f.name.startsWith p)

def guarantee : List Clause := [
    ⟨"imu_every_tick", "sensor_accel_count" =. 1 ∧. "sensor_gyro_count" =. 1⟩,
    ⟨"gyro_is_sample", "sensor_gyro_x" =. "imu2_gx" ∧. "sensor_gyro_y" =. "imu2_gy" ∧. "sensor_gyro_z" =. "imu2_gz"⟩,
    ⟨"accel_is_sample", "sensor_accel_x" =. "imu2_ax" ∧. "sensor_accel_y" =. "imu2_ay" ∧. "sensor_accel_z" =. "imu2_az"⟩,
    ⟨"stamped", "sensor_gyro_timestamp_sample" =. "t_us" ∧. "sensor_accel_timestamp_sample" =. "t_us"⟩,
    ⟨"slow_when_fresh", (("sensor_baro_count" =. 1) =. "baro_fresh") ∧. (("sensor_mag_count" =. 1) =. "mag_fresh") ∧.
      ("sensor_gps_updated" =. "gps_fresh")⟩,
    -- mGauss / 1000 then × 1000 in binary32: two roundings of relative 2^-24 each, so within
    -- 2^-23 · 10^5 ≈ 0.012 for readings up to 10^5 mGauss
    ⟨"mag_gauss", ¬. "mag_fresh" ∨. (abs ("sensor_mag_x" * 1000 - "mag_x") ≤. 0.02 ∧.
      abs ("sensor_mag_y" * 1000 - "mag_y") ≤. 0.02 ∧. abs ("sensor_mag_z" * 1000 - "mag_z") ≤. 0.02)⟩]

private def samplesFinite : Clause :=
  ⟨"samples_finite", finite "imu2_ax" ∧. finite "imu2_ay" ∧. finite "imu2_az" ∧.
    finite "imu2_gx" ∧. finite "imu2_gy" ∧. finite "imu2_gz"⟩

/-- The first statement: `mag_gauss` with an absolute tolerance of 0.001 mGauss on the x axis and no
bound on the reading. Refuted (seeds 1 and 2, about 3% of steps): for large or non-finite readings
the two binary32 roundings exceed any absolute tolerance. Kept for the record. -/
def contractAsFirstStated : Contract where
  assume := [samplesFinite]
  guarantee := (guarantee.filter (·.name != "mag_gauss")) ++
    [⟨"mag_gauss", ¬. "mag_fresh" ∨. abs ("sensor_mag_x" * 1000 - "mag_x") ≤. 0.001⟩]

/-- The contract: compass readings within 10^5 mGauss (the Earth's field is about 250 to 650). -/
def contract : Contract where
  assume := [samplesFinite,
    ⟨"mag_physical", ¬. "mag_fresh" ∨. (abs "mag_x" ≤. 100000 ∧. abs "mag_y" ≤. 100000 ∧.
      abs "mag_z" ≤. 100000)⟩]
  guarantee := guarantee

def module : Module where
  name := "px4_sim_in"
  doc := "plant_sim's sensor samples as PX4's raw sensor topics (hand-written bridge)"
  params := #[]
  input := input
  output := output
  contract := contract
  exe := "build/modules/px4_sim_in/px4_sim_in"
  stack := .px4

end Px4.Modules.Px4SimIn
