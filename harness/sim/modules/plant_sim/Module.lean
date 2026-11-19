import Harness.Module

/-! # plant_sim: the gorge simulator's X500 as a module

The plant in the runs (docs/9-nesting.md, "The plant node"): one X500 of the repository's shared gorge simulator
(`sim/` at the repository root, `gorgesim.plant.Plant`, read only) stepped one 400 Hz vehicle tick per protocol step.
The executable is a Python program (sim/modules/plant_sim/adapter.py on py/module_protocol.py, run with sim/.venv)
that calls the simulator's own plant; `sim/modules/plant_sim/build.sh` writes its launcher and its code hash. Each
`init` resets the simulator: the X500 resting level on the gorge floor at the gorge mission's start, settled for
0.25 s with the motors off, no wind. `plant_formation` is the same simulator with two vehicles.

Frames as ArduPilot's: NED world (origin = the gorge's geographic origin, home), FRD body, quaternion body to NED with
q1 the scalar (q1 ≥ 0). The outputs of step k are the state after the tick and the sensor samples the vehicle reads
on its next tick. `wall_clear` is the harness's measure of the gorge's side surfaces (adapter.py). -/

namespace Sim.Modules.PlantSim

open Harness Harness.Contract.Lang

def params : Schema := #[
  { name := "noise_on", type := .bool, doc := "seeded Gaussian sensor noise (sensor_layer.NOISE); off: exact samples" },
  { name := "noise_seed", type := .u32, doc := "seed of the noise generator (numpy default_rng), when noise_on" },
  { name := "imu_acc_fs_g", type := .f32,
    doc := "accelerometer full scale, g (0: 16 g): the IMU specific force saturates at ± this (the harness's \
      sensor wrapper; the simulator's sensor layer does not saturate)" },
  { name := "imu_gyro_fs_dps", type := .f32,
    doc := "gyro full scale, deg/s (0: 2000 deg/s): the IMU rates saturate at ± this" }]

def input : Schema := #[
  { name := "pwm0", type := .u32, doc := "motor slot 0 (front right CCW) PWM, us; a = (PWM-1000)/1000 clipped" },
  { name := "pwm1", type := .u32, doc := "motor slot 1 (rear left CCW) PWM, us" },
  { name := "pwm2", type := .u32, doc := "motor slot 2 (front left CW) PWM, us" },
  { name := "pwm3", type := .u32, doc := "motor slot 3 (rear right CW) PWM, us" }]

private def f (n d : String) : Field := { name := n, type := .f32, doc := d }

def imuFields : List Field :=
  (List.range 3).flatMap fun s =>
    [("ax", "specific force x, m/s^2"), ("ay", "specific force y"), ("az", "specific force z"),
     ("gx", "gyro x (roll rate), rad/s"), ("gy", "gyro y"), ("gz", "gyro z")].map fun (c, d) =>
      f s!"imu{s}_{c}" s!"IMU sample after physics substep {s} of the tick, FRD body: {d}"

def output : Schema := #[
  { name := "t_us", type := .u32, doc := "simulated time of the state, us since init (2500 per step)" },
  f "pos_n" "true position north of home, m", f "pos_e" "true position east, m", f "pos_d" "true position down, m",
  f "vel_n" "true velocity north, m/s", f "vel_e" "true velocity east, m/s", f "vel_d" "true velocity down, m/s",
  f "q1" "attitude quaternion body (FRD) to NED, scalar", f "q2" "quaternion x", f "q3" "quaternion y",
  f "q4" "quaternion z",
  f "rate_p" "true body rate about FRD x, rad/s", f "rate_q" "about y", f "rate_r" "about z",
  f "thrust0" "lagged thrust of motor slot 0 / per-motor maximum (kf MAX_RPM^2)", f "thrust1" "slot 1",
  f "thrust2" "slot 2", f "thrust3" "slot 3"] ++ imuFields.toArray ++ #[
  { name := "baro_fresh", type := .bool, doc := "a barometer sample this tick (100 Hz); else baro_* are 0" },
  f "baro_pa" "static pressure, Pa (1976 atmosphere)", f "baro_degc" "temperature, degC",
  { name := "mag_fresh", type := .bool, doc := "a compass sample this tick (100 Hz); else mag_* are 0" },
  f "mag_x" "body field x, mGauss (minus SITL's offsets)", f "mag_y" "body field y", f "mag_z" "body field z",
  { name := "gps_fresh", type := .bool, doc := "a GPS sample this tick (5 Hz); else gps_* are 0" },
  { name := "gps_lat_e7", type := .i32, doc := "latitude, 1e-7 deg (the simulator's binary64 degrees, nearest)" },
  { name := "gps_lon_e7", type := .i32, doc := "longitude, 1e-7 deg (nearest)" },
  f "gps_alt" "altitude AMSL, m", f "gps_vn" "GPS velocity north, m/s", f "gps_ve" "east", f "gps_vd" "down",
  f "wall_clear" "closest distance, m, from the vehicle's collision body to the gorge's side surfaces (its points no \
    lower than 5 cm under the vehicle's center: not the floor beneath), at most 2 m; every 4th tick, held between"]

/-- Every f32 output field, for `outputs_finite`. -/
def floatOutputs : List String := (output.toList.filter (·.type == .f32)).map (·.name)

private def conj : List Expr → Expr
  | [] => tt
  | [e] => e
  | e :: es => e ∧. conj es

private def v (n : String) : Expr := .var n

/-- The IMU full scale in output units, as adapter.py computes it: binary32 `fs * unit`, the
default when `fs` is 0. -/
def fullScale (fs : String) (dflt unit : Expr) : Expr → Expr := fun x =>
  (v fs =. 0 ∧. abs x ≤. dflt * unit) ∨. (¬. (v fs =. 0) ∧. abs x ≤. v fs * unit)

/-- `imu_full_scale`: every IMU sample within the full scale (adapter.py clips them there). -/
def imuFullScale : Clause :=
  ⟨"imu_full_scale", conj ((List.range 3).flatMap fun s =>
    (["ax", "ay", "az"].map fun c => fullScale "imu_acc_fs_g" 16 9.80665 (v s!"imu{s}_{c}")) ++
    (["gx", "gy", "gz"].map fun c =>
      fullScale "imu_gyro_fs_dps" 2000 0.017453292 (v s!"imu{s}_{c}")))⟩

def contract : Contract where
  assume := [
    ⟨"pwm_range", conj ((List.range 4).flatMap fun i =>
      [(1000 : Expr) ≤. v s!"pwm{i}", v s!"pwm{i}" ≤. 2000])⟩,
    -- the full-scale ranges of ArduPilot's IMU drivers (2 to 32 g, 250 to 4000 deg/s), or 0
    ⟨"imu_full_scale_range", (v "imu_acc_fs_g" =. 0 ∨. (2 ≤. v "imu_acc_fs_g" ∧.
      v "imu_acc_fs_g" ≤. 32)) ∧. (v "imu_gyro_fs_dps" =. 0 ∨. (250 ≤. v "imu_gyro_fs_dps" ∧.
      v "imu_gyro_fs_dps" ≤. 4000))⟩]
  guarantee := [
    -- |q|^2 - 1 evaluated in binary32 on the binary32-rounded components: rounding each component (relative
    -- error u = 2^-24, so 2u on its square), each product (u) and each of the three sums (u, partial sums <= 1)
    -- moves the sum by at most 6u = 3.58e-7 from the binary64 norm, which quat_ned_frd normalizes to ~1e-16
    ⟨"quat_unit", abs (v "q1" * v "q1" + v "q2" * v "q2" + v "q3" * v "q3" + v "q4" * v "q4" - 1) ≤. 4e-7⟩,
    ⟨"thrust_range", conj ((List.range 4).flatMap fun i =>
      [(0 : Expr) ≤. v s!"thrust{i}", v s!"thrust{i}" ≤. 1])⟩,
    ⟨"outputs_finite", conj (floatOutputs.map fun n => finite (v n))⟩,
    ⟨"wall_clear_range", (0 : Expr) ≤. v "wall_clear" ∧. v "wall_clear" ≤. 2⟩,
    imuFullScale]

def module : Module where
  name := "plant_sim"
  doc := "the shared gorge simulator's X500 (gym-pybullet-drones), one 400 Hz tick per step"
  params := params
  input := input
  output := output
  contract := contract
  exe := "build/modules/plant_sim/plant_sim"
  stack := .sim

end Sim.Modules.PlantSim
