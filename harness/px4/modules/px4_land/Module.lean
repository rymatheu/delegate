import px4.modules.px4_land.Ports
import px4.modules.px4_common.Common

/-! # px4_land: PX4's multicopter land detector

PX4's `land_detector` module (src/modules/land_detector, all its detector classes compiled, the
multicopter one started: `land_detector start multicopter`, as rc.mc_apps), real and unmodified,
PX4 v1.17.0, with src/lib/hysteresis. It runs on its work queue (nav_and_controllers) whenever
`vehicle_local_position` is published (SubscriptionCallbackWorkItem, LandDetector.h:185) and, as a
backup, 50 ms after its last run (ScheduleDelayed, LandDetector.cpp:79). One run reads the latest
armed state, acceleration, angular velocity, status, thrust setpoint, hover thrust estimate,
trajectory setpoint, control mode and takeoff status, updates the freefall / ground contact /
maybe landed / landed / ground effect hysteresis, and publishes vehicle_land_detected when one of
them changed or a second has passed (LandDetector.cpp:157-185).

Parameter writes: at init it lowers LNDMC_Z_VEL_MAX to min(MPC_LAND_CRWL, MPC_LAND_SPEED)/1.2
when larger (logging an error), and on disarm after a flight it writes LND_FLIGHT_T_HI/LO. No
other module reads these.

Contract, from the code: `landed` implies `maybe_landed` (landed's input is `!armed ∨ maybe_landed`
with a false→true delay and an immediate true→false, MulticopterLandDetector.cpp:347-350,
LandDetector.h:146-148); the message is stamped with the clock. -/

namespace Px4.Modules.Px4Land

open Harness Harness.Contract.Lang Px4.Modules.Px4Common

private def ld (f : String) : String := s!"vehicle_land_detected_{f}"

def guarantee : List Clause := [
  ⟨"landed_implies_maybe_landed", ¬. ld "landed" ∨. ld "maybe_landed"⟩,
  ⟨"detected_stamped", ¬. "vehicle_land_detected_updated" ∨. ld "timestamp" =. "t_us"⟩,
  ⟨"no_px4_error", "px4_land_errors" =. 0⟩]

/-- The first statement, PX4's documented parameter ranges only. Refuted at init of every case
with LNDMC_Z_VEL_MAX > min(MPC_LAND_CRWL, MPC_LAND_SPEED) / 1.2 (seed 1: no_px4_error): the
module logs "LNDMC_Z_VEL_MAX > MPC_LAND_CRWL or MPC_LAND_SPEED, updating" with PX4_ERR and lowers
the parameter in its own store (MulticopterLandDetector.cpp:104-110). The documented ranges
allow it: LNDMC_Z_VEL_MAX, MPC_LAND_CRWL and MPC_LAND_SPEED have lower bounds only (campaign
20261118T175928Z-seed1, flight regime, case 0: LNDMC_Z_VEL_MAX = ∞, all 100 cases refuted).
Kept for the record. -/
def contractAsFirstStated : Contract where
  assume := Ports.widths ++ Ports.paramRanges
  guarantee := guarantee

def contract : Contract where
  assume := Ports.widths ++ Ports.paramRanges ++ [
    ⟨"z_vel_max_below_land_speeds", "LNDMC_Z_VEL_MAX" * 1.2 ≤. "MPC_LAND_CRWL" ∧.
      "LNDMC_Z_VEL_MAX" * 1.2 ≤. "MPC_LAND_SPEED"⟩]
  guarantee := guarantee

def clocks : List Hint := [.increasing "t_us" 1000000 2500 2500,
  .increasing "vehicle_local_position_timestamp" 1000000 2500 2500,
  .increasing "vehicle_local_position_timestamp_sample" 1000000 2500 2500,
  .increasing "vehicle_angular_velocity_timestamp_sample" 1000000 2500 2500,
  .increasing "vehicle_imu_status_timestamp" 1000000 2500 2500,
  .increasing "hover_thrust_estimate_timestamp" 1000000 2500 2500]

/-- Armed, a local position, gyro, acceleration and thrust setpoint every tick, any parameters,
inputs moderate (velocities within 5 m/s, thrust within [0, 1], gyro within 2 rad/s). -/
def flight : Regime where
  name := "land_flight"
  doc := "armed, estimates and thrust setpoint every 400 Hz tick"
  clauses := [
    ⟨"position_every_tick", "vehicle_local_position_updated" =. tt⟩,
    ⟨"armed", "actuator_armed_updated" ∧. "actuator_armed_armed"⟩,
    ⟨"sensors_every_tick", "vehicle_angular_velocity_updated" ∧. "vehicle_acceleration_updated" ∧.
      "vehicle_thrust_setpoint_updated"⟩,
    ⟨"moderate", allOf (["vx", "vy", "vz", "z_deriv"].map fun f =>
        within s!"vehicle_local_position_{f}" (-5) 5) ∧.
      within "vehicle_thrust_setpoint_xyz_2" (-1) 0 ∧.
      allOf ((arr "vehicle_angular_velocity_xyz" 3).map fun f => within f (-2) 2) ∧.
      allOf ((arr "vehicle_acceleration_xyz" 3).map fun f => within f (-15) 15) ∧.
      within "vehicle_local_position_dist_bottom" 0 50⟩]
  hints := clocks

def x500Params : List Clause :=
  (Ports.paramDefaults.filter (·.name != "default_MPC_THR_HOVER")) ++
    [⟨"x500_MPC_THR_HOVER", "MPC_THR_HOVER" =. 0.6⟩]

/-- The X500 hovering in Position mode: PX4's defaults, thrust near hover, small velocities,
gravity on the accelerometer, a slowly varying estimate. -/
def x500Hover : Regime where
  name := "x500_hover"
  doc := "X500 parameters, armed and hovering in Position mode"
  clauses := x500Params ++ flight.clauses ++ [
    ⟨"posctl", "vehicle_control_mode_updated" ∧.
        "vehicle_control_mode_flag_control_climb_rate_enabled"⟩,
    ⟨"hover_thrust", within "vehicle_thrust_setpoint_xyz_2" (-0.7) (-0.5)⟩,
    ⟨"gravity", within "vehicle_acceleration_xyz_2" (-10.5) (-9)⟩,
    ⟨"flying", "takeoff_status_updated" ∧. "takeoff_status_takeoff_state" =. 5⟩,
    ⟨"valid", "vehicle_local_position_v_z_valid" ∧. "vehicle_local_position_z_valid" ∧.
      "vehicle_local_position_v_xy_valid"⟩]
  hints := clocks ++ [
    .walk "vehicle_local_position_vx" (-2) 2 0.005, .walk "vehicle_local_position_vy" (-2) 2 0.005,
    .walk "vehicle_local_position_vz" (-1) 1 0.005,
        .walk "vehicle_local_position_z_deriv" (-1) 1 0.005]

/-- On the ground: PX4's defaults, low thrust, the vehicle at rest (velocities and rates near
zero, gravity on the accelerometer), armed or not, so that the detector goes through ground
contact, maybe landed and landed (each about LNDMC_TRIG_TIME / 3 = 0.33 s). -/
def ground : Regime where
  name := "ground"
  doc := "X500 parameters, at rest on the ground with low thrust, armed or disarmed"
  clauses := x500Params ++ [
    ⟨"position_every_tick", "vehicle_local_position_updated" =. tt⟩,
    ⟨"sensors_every_tick", "vehicle_angular_velocity_updated" ∧. "vehicle_acceleration_updated" ∧.
      "vehicle_thrust_setpoint_updated"⟩,
    ⟨"at_rest", allOf (["vx", "vy", "vz", "z_deriv"].map fun f =>
        within s!"vehicle_local_position_{f}" (-0.05) 0.05) ∧.
      allOf ((arr "vehicle_angular_velocity_xyz" 3).map fun f => within f (-0.02) 0.02) ∧.
      within "vehicle_acceleration_xyz_2" (-9.9) (-9.7) ∧.
      within "vehicle_acceleration_xyz_0" (-0.1) 0.1 ∧.
          within "vehicle_acceleration_xyz_1" (-0.1) 0.1⟩,
    ⟨"low_thrust", within "vehicle_thrust_setpoint_xyz_2" (-0.05) 0⟩,
    ⟨"valid", "vehicle_local_position_v_z_valid" ∧. "vehicle_local_position_z_valid" ∧.
      "vehicle_local_position_v_xy_valid"⟩,
    ⟨"quiet_imu", within "vehicle_imu_status_gyro_vibration_metric" 0 0.01 ∧.
      within "vehicle_imu_status_accel_vibration_metric" 0 0.5⟩]
  hints := clocks

def coverage : List Clause := [
  ⟨"detected_published", "vehicle_land_detected_updated" =. tt⟩,
  ⟨"landed", ld "landed" =. tt⟩,
  ⟨"maybe_not_landed", ld "maybe_landed" ∧. ¬. ld "landed"⟩,
  ⟨"airborne", ¬. ld "maybe_landed" ∧. ¬. ld "landed" ∧. ¬. ld "ground_contact"⟩]

def module : Module where
  name := "px4_land"
  doc := "PX4 land_detector, multicopter (v1.17.0), unmodified, behind the generic uORB shim"
  params := Ports.params
  input := Ports.input
  output := Ports.output
  contract := { contract with guarantee := contract.guarantee ++ Ports.outWidths }
  exe := "build/modules/px4_land/px4_land"
  stack := .px4
  regimes := [flight, x500Hover, ground]
  coverage := coverage

end Px4.Modules.Px4Land
