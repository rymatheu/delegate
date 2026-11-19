import px4.modules.px4_commander.Ports

/-! # px4_commander: PX4's commander, a task module

PX4's `commander` (src/modules/commander with its health and arming checks, failsafe state
machine, failure detector, mode utilities, home position and the libraries its CMakeLists.txt
links), real and unmodified, PX4 v1.17.0, started with `commander start`. It is a task module:
`Commander::task_spawn` spawns a task (px4_task_spawn_cmd) whose `run()` loops while
`!should_exit()`: one pass over the inputs, the checks (10 Hz), the mode and failsafe logic and
the commands, a publication of actuator_armed, vehicle_control_mode and vehicle_status at 2 Hz or
on any change, then `px4_usleep(10 ms)` unless vehicle_command has unread messages
(Commander.cpp:1775-1983). In the harness the task runs on its own thread, handed control by the
shim only when its sleep is over (px4/shim/tasks.cpp): with a 400 Hz step, one pass every
4 steps, at the step whose t_us reaches the deadline. `process fresh`: every case is a fresh copy
of the process (commander's static state is that of a fresh boot).

What a step runs: nothing, or one (more, while commands are queued) pass of that loop.

Contract, from the code:
* `armed_agrees`, `control_mode_armed`, `published_together`: the three status topics are
  published only in one block, one after the other, from the same state (Commander.cpp:1932-1946,
  updateControlMode at :2600-2618), so the latest messages agree: actuator_armed.armed,
  vehicle_control_mode.flag_armed and vehicle_status.arming_state = ARMED (2).
* `control_mode_of_nav_state`: the control-mode flags are those of
  mode_util::getVehicleControlMode for the published nav state (ModeUtil/control_mode.cpp:45-205),
  with flag_multicopter_position_control_enabled as Commander.cpp:2609-2614 computes it; the
  offboard state's flags depend on offboard_control_mode and only its offboard flag is stated.
* `stamped`: the status topics carry the clock of the step that published them. (First stated
  with an escape for timestamp 0, when the shim still showed start-time messages at the first
  step; kept, harmless.)
* `ids_from_params`, `control_mode_of_nav_state`, `known_states` hold from commander's first
  publication on (`noStatusYet` before it). Without that guard they failed at every step of a
  px4_sup run with an arbitrary clock (seed 1, 200 steps), after the shim stopped showing
  start-time messages: the all-zero record before any publication has arming_state 0.
  Refuted the same way, independently, in px4_cmd_loop (regime x500_cmd_step_noise, `harness
  run` seed 1, 14000 steps, 3 violations each at steps 0-2): there the clock starts at one tick
  (plant_sim's t_us = 2500), and commander's first publication is at step 3 (t_us = 10000), the
  pass after its first 10 ms sleep (Commander.cpp:1979); before it the record is all zero
  (arming_state 0, nav_state 0 with every flag off, system_id 0).
* `ids_from_params`: vehicle_status.system_id and component_id are MAV_SYS_ID and MAV_COMP_ID.
* `known_states`, `ack_result_known`: arming state 1 or 2; a nav state the code sets; ack results
  of VehicleCommandAck.msg.
* `no_px4_error`. -/

namespace Px4.Modules.Px4Commander

open Harness Harness.Contract.Lang

/-- The control-mode flags of each nav state (control_mode.cpp), as (nav state, manual, auto,
position, velocity, altitude, climb rate, attitude, rates, allocation, termination); the
attitude and rate flags of MANUAL (0) are "stabilization required", i.e. a rotary wing. -/
def modeTable : List (Nat × List Bool) := [
  (1, [true, false, false, false, true, true, true, true, true, false]),     -- ALTCTL
  (8, [true, false, false, false, true, true, true, true, true, false]),     -- ALTITUDE_CRUISE
  (2, [true, false, true, true, true, true, true, true, true, false]),       -- POSCTL
  (6, [true, false, true, true, true, true, true, true, true, false]),       -- POSITION_SLOW
  (3, [false, true, true, true, true, true, true, true, true, false]),       -- AUTO_MISSION
  (4, [false, true, true, true, true, true, true, true, true, false]),       -- AUTO_LOITER
  (5, [false, true, true, true, true, true, true, true, true, false]),       -- AUTO_RTL
  (17, [false, true, true, true, true, true, true, true, true, false]),      -- AUTO_TAKEOFF
  (18, [false, true, true, true, true, true, true, true, true, false]),      -- AUTO_LAND
  (20, [false, true, true, true, true, true, true, true, true, false]),      -- AUTO_PRECLAND
  (22, [false, true, true, true, true, true, true, true, true, false]),      -- AUTO_VTOL_TAKEOFF
  (10, [true, false, false, false, false, false, false, true, true, false]), -- ACRO
  (12, [false, true, false, false, false, true, true, true, true, false]),   -- DESCEND
  (13, [false, false, false, false, false, false, false, false, false, true]), -- TERMINATION
  (15, [true, false, false, false, false, false, true, true, true, false]),  -- STAB
  (19, [false, false, true, true, true, true, true, true, true, false]),     -- FOLLOW_TARGET
  (21, [false, false, true, true, true, true, true, true, true, false])]     -- ORBIT

private def flagNames : List String :=
  ["control_manual_enabled", "control_auto_enabled", "control_position_enabled",
   "control_velocity_enabled", "control_altitude_enabled", "control_climb_rate_enabled",
   "control_attitude_enabled", "control_rates_enabled", "control_allocation_enabled",
   "control_termination_enabled"]

private def flag (n : String) : Expr := .var s!"vehicle_control_mode_flag_{n}"

private def conj : List Expr → Expr
  | [] => tt
  | e :: es => es.foldl (· ∧. ·) e

private def natLit (n : Nat) : Expr := .lit n.toFloat.toFloat32.toBits

private def navIs (n : Nat) : Expr := "vehicle_status_nav_state" =. natLit n

private def rotary : Expr := "vehicle_status_vehicle_type" =. 1

/-- The flags of one nav state, all ten, and the offboard and acceleration flags off. -/
private def modeClause (n : Nat) (bs : List Bool) : Expr :=
  ¬. navIs n ∨. conj ((flagNames.zip bs).map (fun (f, b) => flag f =. (if b then tt else ff)) ++
    [flag "control_offboard_enabled" =. ff, flag "control_acceleration_enabled" =. ff])

/-- MANUAL: manual and allocation on, attitude and rates as "stabilization required". -/
private def manualClause : Expr :=
  ¬. navIs 0 ∨. conj [flag "control_manual_enabled" =. tt, flag "control_allocation_enabled" =. tt,
    flag "control_attitude_enabled" =. rotary, flag "control_rates_enabled" =. rotary,
    flag "control_auto_enabled" =. ff, flag "control_position_enabled" =. ff,
    flag "control_velocity_enabled" =. ff, flag "control_altitude_enabled" =. ff,
    flag "control_climb_rate_enabled" =. ff, flag "control_termination_enabled" =. ff,
    flag "control_offboard_enabled" =. ff, flag "control_acceleration_enabled" =. ff]

/-- Commander.cpp:2609-2614. -/
private def mcPositionFlag : Expr :=
  "vehicle_control_mode_flag_multicopter_position_control_enabled" =.
    (rotary ∧. (flag "control_altitude_enabled" ∨. flag "control_climb_rate_enabled" ∨.
      flag "control_position_enabled" ∨. flag "control_velocity_enabled" ∨.
      flag "control_acceleration_enabled"))

private def armedState : Expr := "vehicle_status_arming_state" =. 2

private def anyOf (x : String) (vs : List Nat) : Expr :=
  match vs with
  | [] => ff
  | v :: rest => rest.foldl (fun e w => e ∨. (Expr.var x =. natLit w)) (Expr.var x =. natLit v)

/-- Nothing published yet: the outputs are all 0 until commander's first publication in a step
(`process fresh` does not show what it published while starting, adapter.cpp). With the clock of
the regimes the first pass is at step 0; with an arbitrary clock it may not come for many steps. -/
private def noStatusYet : Expr :=
  "vehicle_status_timestamp" =. 0 ∧. "vehicle_status_arming_state" =. 0

def guarantee : List Clause := [
  ⟨"armed_agrees", "actuator_armed_armed" =. armedState⟩,
  ⟨"control_mode_armed", "vehicle_control_mode_flag_armed" =. "actuator_armed_armed"⟩,
  ⟨"published_together", "actuator_armed_updated" =. "vehicle_status_updated" ∧.
      "vehicle_control_mode_updated" =. "vehicle_status_updated"⟩,
  ⟨"control_mode_of_nav_state", noStatusYet ∨. conj (manualClause :: mcPositionFlag ::
      (¬. navIs 14 ∨. flag "control_offboard_enabled" =. tt) ::
      modeTable.map fun (n, bs) => modeClause n bs)⟩,
  ⟨"stamped", ¬. "vehicle_status_updated" ∨. "vehicle_status_timestamp" =. 0 ∨.
      ("vehicle_status_timestamp" =. "t_us" ∧. "actuator_armed_timestamp" =. "t_us" ∧.
       "vehicle_control_mode_timestamp" =. "t_us")⟩,
  ⟨"ids_from_params", noStatusYet ∨. "vehicle_status_system_id" =. "MAV_SYS_ID" ∧.
      "vehicle_status_component_id" =. "MAV_COMP_ID"⟩,
  ⟨"known_states", noStatusYet ∨. anyOf "vehicle_status_arming_state" [1, 2] ∧.
      anyOf "vehicle_status_nav_state" ([0, 1, 2, 3, 4, 5, 6, 8, 10, 12, 13, 14, 15] ++
        (List.range 14).map (· + 17))⟩,
  ⟨"ack_result_known", "vehicle_command_ack_by_px4_commander_result" ≤. 6⟩,
  ⟨"no_px4_error", "px4_commander_errors" =. 0⟩]

/-- The first statement. Its first campaign (x500_ground, seed 1, 5 x 400) refuted `no_px4_error`
in every case: "action_request lost, generation 0 -> 2" (Commander.cpp:1906-1912). action_request
has no ORB_QUEUE_LENGTH (a queue of one), commander reads it once per pass, every 10 ms, and logs
an error when the generation advanced by more than one: a second request within 10 ms overwrites
the first. Generated inputs publish it at random ticks. On the vehicle manual_control publishes it
on switch changes only. The rate (at most one per 10 ms) needs the previous ticks, which the
contract language does not have yet. -/
def contractAsFirstStated : Contract where
  assume := Ports.widths ++ Ports.paramRanges
  guarantee := guarantee

/-- What commander has to be given so that it logs no error, from the campaigns (seeds 1-3 with no
regime, 20 x 100) and the code; each clause excludes an input condition that commander reports at
error level by design:
* `no_action_request`: see `contractAsFirstStated`.
* `command_rate`: "vehicle_command lost, generation 16 -> 57" (seed 3): vehicle_command has a
  queue of 8 (ORB_QUEUE_LENGTH) and commander reads it once per 10 ms pass
  (Commander.cpp:1888-1896),
  so more than 8 commands between two passes overwrite unread ones. At most 2 per 400 Hz tick keeps
  it at 8 per 4 ticks.
* `battery_not_failing`: "Battery 1: under voltage.", "cell fault", "over temperature" (seeds 1
  and 2): a battery fault bit is reported with mavlink_log_emergency, i.e. PX4_ERR
  (batteryCheck.cpp:153-175), and so is WARNING_EMERGENCY (:247-262).
* `angular_velocity_valid`: commander logs "angular velocity no longer valid" at error level when
  vehicle_angular_velocity stops being finite or fresh, i.e. no message stamped within the last
  second (estimatorCheck.cpp:771-791). First stated as "finite and stamped within the last second"
  (`t_us - timestamp < 1e6`); refuted by the clocked regime, seed 3, case 19: a message stamped 2
  at t_us = 1000000 was valid, and stale at the next pass, 10 ms later. Now: finite and stamped
  with the step's clock. That messages keep coming at least once a second needs the previous
  ticks; cases are kept below 400 steps. -/
def assumeInputs : List Clause := [
  ⟨"no_action_request", "action_request_updated" =. ff⟩,
  ⟨"command_rate", "vehicle_command_count" ≤. 2⟩,
  ⟨"battery_not_failing", ¬. "battery_status_updated" ∨.
      ("battery_status_faults" =. 0 ∧. "battery_status_warning" ≤. 2)⟩,
  ⟨"angular_velocity_valid", ¬. "vehicle_angular_velocity_updated" ∨.
      (finite "vehicle_angular_velocity_xyz_0" ∧. finite "vehicle_angular_velocity_xyz_1" ∧.
       finite "vehicle_angular_velocity_xyz_2" ∧. "vehicle_angular_velocity_timestamp" =. "t_us")⟩]

def contract : Contract where
  assume := Ports.widths ++ Ports.paramRanges ++ assumeInputs
  guarantee := guarantee

/-! ## Regimes -/

private def num (x : Float) : Expr := .lit x.toFloat32.toBits

/-- The parameters PX4's SITL start (ROMFS init.d-posix/rcS, px4-rc.simulator) and the X500
airframe (airframes/4001_gz_x500 with rc.mc_defaults) set among commander's; the others keep PX4's
defaults. The simulated IMU and magnetometer are calibrated as rcS sets them. -/
def x500Sets : List (String × Expr) := [
  ("CAL_ACC0_ID", num 1310988), ("CAL_GYRO0_ID", num 1310988), ("CAL_ACC1_ID", num 1310996),
  ("CAL_GYRO1_ID", num 1310996), ("CAL_ACC2_ID", num 1311004), ("CAL_GYRO2_ID", num 1311004),
  ("CAL_MAG0_ID", num 197388), ("CAL_MAG0_PRIO", num 50), ("CAL_MAG1_ID", num 197644),
  ("CAL_MAG1_PRIO", num 50), ("COM_CPU_MAX", num (-1)), ("COM_RAM_MAX", num (-1)),
  ("COM_RC_IN_MODE", num 1), ("SYS_FAILURE_EN", num 1), ("COM_LOW_BAT_ACT", num 3),
  ("COM_MODE_ARM_CHK", num 1), ("SDLOG_MODE", num 1), ("MAV_TYPE", num 2), ("NAV_DLL_ACT", num 2)]

def x500Params : List Clause :=
  (Ports.paramDefaults.filter fun c => !x500Sets.any fun (n, _) => c.name == s!"default_{n}") ++
  x500Sets.map fun (n, v) => ⟨s!"x500_{n}", Expr.var n =. v⟩

/-- The topics a healthy SITL vehicle publishes every tick to commander (sensors, estimator,
land detector, battery and power simulators, a GCS link). -/
def healthyTopics : List String := [
  "sensor_accel", "sensor_gyro", "sensor_mag", "sensor_baro", "sensor_selection",
  "sensors_status_imu", "vehicle_imu_status", "vehicle_air_data", "vehicle_attitude",
  "vehicle_angular_velocity", "vehicle_acceleration", "vehicle_local_position",
  "vehicle_global_position", "vehicle_gps_position", "estimator_status", "estimator_status_flags",
  "estimator_selector_status", "estimator_sensor_bias", "vehicle_land_detected", "battery_status",
  "system_power", "cpuload", "telemetry_status"]

def imu : Float := 1310988
def mag : Float := 197388
def baro : Float := 6620172
def lat : Float := 47.397742
def lon : Float := 8.545594
def alt : Float := 488
def inf : Expr := .lit 0x7f800000
def nan : Expr := .lit 0x7fc00000

/-- The healthy values (PX4's simulated sensors at rest at the default SITL home); every other
field of these topics is 0 / false, except the free ones and the timestamps (hints). -/
def healthyValues : List (String × Expr) := [
  ("sensor_accel_count", num 1), ("sensor_accel_device_id", num imu),
  ("sensor_accel_temperature", num 25), ("sensor_accel_samples", num 1),
  ("sensor_gyro_count", num 1), ("sensor_gyro_device_id", num imu),
  ("sensor_gyro_temperature", num 25), ("sensor_gyro_samples", num 1),
  ("sensor_mag_count", num 1), ("sensor_mag_device_id", num mag),
  ("sensor_mag_temperature", num 25),
  ("sensor_baro_count", num 1), ("sensor_baro_device_id", num baro),
  ("sensor_baro_temperature", num 25),
  ("sensor_selection_accel_device_id", num imu), ("sensor_selection_gyro_device_id", num imu),
  ("sensors_status_imu_accel_device_id_primary", num imu),
  ("sensors_status_imu_accel_device_ids_0", num imu), ("sensors_status_imu_accel_healthy_0", tt),
  ("sensors_status_imu_accel_priority_0", num 50),
  ("sensors_status_imu_gyro_device_id_primary", num imu),
  ("sensors_status_imu_gyro_device_ids_0", num imu), ("sensors_status_imu_gyro_healthy_0", tt),
  ("sensors_status_imu_gyro_priority_0", num 50),
  ("vehicle_imu_status_accel_device_id", num imu), ("vehicle_imu_status_gyro_device_id", num imu),
  ("vehicle_imu_status_accel_rate_hz", num 250), ("vehicle_imu_status_gyro_rate_hz", num 250),
  ("vehicle_imu_status_accel_raw_rate_hz", num 250),
  ("vehicle_imu_status_gyro_raw_rate_hz", num 250),
  ("vehicle_imu_status_mean_accel_2", num (-9.80665)),
  ("vehicle_imu_status_temperature_accel", num 25),
  ("vehicle_imu_status_temperature_gyro", num 25),
  ("vehicle_air_data_baro_device_id", num baro), ("vehicle_air_data_baro_alt_meter", num alt),
  ("vehicle_air_data_baro_pressure_pa", num 95500),
  ("vehicle_air_data_ambient_temperature", num 25),
  ("vehicle_air_data_rho", num 1.15),
  ("vehicle_attitude_q_0", num 1), ("vehicle_acceleration_xyz_2", num (-9.80665)),
  ("vehicle_local_position_xy_valid", tt), ("vehicle_local_position_z_valid", tt),
  ("vehicle_local_position_v_xy_valid", tt), ("vehicle_local_position_v_z_valid", tt),
  ("vehicle_local_position_heading_good_for_control", tt),
  ("vehicle_local_position_xy_global", tt), ("vehicle_local_position_z_global", tt),
  ("vehicle_local_position_ref_lat", num lat), ("vehicle_local_position_ref_lon", num lon),
  ("vehicle_local_position_ref_alt", num alt), ("vehicle_local_position_evh", num 0.1),
  ("vehicle_local_position_evv", num 0.1), ("vehicle_local_position_vxy_max", inf),
  ("vehicle_local_position_vz_max", inf), ("vehicle_local_position_hagl_min", inf),
  ("vehicle_local_position_hagl_max_z", inf), ("vehicle_local_position_hagl_max_xy", inf),
  ("vehicle_global_position_lat", num lat), ("vehicle_global_position_lon", num lon),
  ("vehicle_global_position_alt_ellipsoid", num alt),
  ("vehicle_global_position_lat_lon_valid", tt), ("vehicle_global_position_alt_valid", tt),
  ("vehicle_gps_position_device_id", num 11141384), ("vehicle_gps_position_latitude_deg", num lat),
  ("vehicle_gps_position_longitude_deg", num lon),
  ("vehicle_gps_position_altitude_msl_m", num alt),
  ("vehicle_gps_position_altitude_ellipsoid_m", num alt),
  ("vehicle_gps_position_s_variance_m_s", num 0.2), ("vehicle_gps_position_fix_type", num 3),
  ("vehicle_gps_position_hdop", num 0.7), ("vehicle_gps_position_vdop", num 0.9),
  ("vehicle_gps_position_vel_ned_valid", tt), ("vehicle_gps_position_satellites_used", num 10),
  ("vehicle_gps_position_heading", nan), ("vehicle_gps_position_heading_offset", nan),
  ("vehicle_gps_position_heading_accuracy", nan),
  ("estimator_status_accel_device_id", num imu), ("estimator_status_gyro_device_id", num imu),
  ("estimator_status_baro_device_id", num baro), ("estimator_status_mag_device_id", num mag),
  ("estimator_status_mag_strength_gs", num 0.48),
  ("estimator_status_mag_strength_ref_gs", num 0.48),
  ("estimator_status_mag_inclination_deg", num 63),
  ("estimator_status_mag_inclination_ref_deg", num 63),
  ("estimator_status_flags_cs_tilt_align", tt), ("estimator_status_flags_cs_yaw_align", tt),
  ("estimator_status_flags_cs_gnss_pos", tt), ("estimator_status_flags_cs_mag_3d", tt),
  ("estimator_status_flags_cs_baro_hgt", tt), ("estimator_status_flags_cs_gnss_vel", tt),
  ("estimator_status_flags_cs_mag", tt),
  ("estimator_selector_status_instances_available", num 1),
  ("estimator_selector_status_accel_device_id", num imu),
  ("estimator_selector_status_baro_device_id", num baro),
  ("estimator_selector_status_gyro_device_id", num imu),
  ("estimator_selector_status_mag_device_id", num mag),
  ("estimator_selector_status_healthy_0", tt),
  ("estimator_sensor_bias_gyro_device_id", num imu),
  ("estimator_sensor_bias_accel_device_id", num imu),
  ("estimator_sensor_bias_mag_device_id", num mag),
  ("battery_status_connected", tt), ("battery_status_scale", num 1),
  ("battery_status_time_remaining_s", nan), ("battery_status_temperature", nan),
  ("battery_status_cell_count", num 4), ("battery_status_capacity", num 5000),
  ("battery_status_state_of_health", num 100), ("battery_status_id", num 1),
  ("battery_status_full_charge_capacity_wh", nan), ("battery_status_remaining_capacity_wh", nan),
  ("battery_status_nominal_voltage", num 14.8),
  ("system_power_voltage5v_v", num 5), ("system_power_brick_valid", num 1),
  ("system_power_servo_valid", num 1),
  ("cpuload_load", num 0.2), ("cpuload_ram_usage", num 0.3),
  ("telemetry_status_type", num 1), ("telemetry_status_mavlink_v2", tt),
  ("telemetry_status_heartbeat_type_gcs", tt)]

/-- Fields left free, with the ranges of a healthy vehicle at rest. -/
def groundFree : List Clause := [
  ⟨"accel_at_rest", abs "sensor_accel_x" ≤. 0.3 ∧. abs "sensor_accel_y" ≤. 0.3 ∧.
      -10.1 ≤. "sensor_accel_z" ∧. "sensor_accel_z" ≤. -9.5⟩,
  ⟨"gyro_at_rest", abs "sensor_gyro_x" ≤. 0.02 ∧. abs "sensor_gyro_y" ≤. 0.02 ∧.
      abs "sensor_gyro_z" ≤. 0.02⟩,
  ⟨"mag_field", 0.15 ≤. "sensor_mag_x" ∧. "sensor_mag_x" ≤. 0.25 ∧. abs "sensor_mag_y" ≤. 0.05 ∧.
      0.38 ≤. "sensor_mag_z" ∧. "sensor_mag_z" ≤. 0.48⟩,
  ⟨"baro_pressure", 95000 ≤. "sensor_baro_pressure" ∧. "sensor_baro_pressure" ≤. 96000⟩,
  ⟨"test_ratios", "estimator_status_hdg_test_ratio" ≤. 0.5 ∧.
      "estimator_status_vel_test_ratio" ≤. 0.5 ∧.
      "estimator_status_pos_test_ratio" ≤. 0.5 ∧. "estimator_status_hgt_test_ratio" ≤. 0.5 ∧.
      0 ≤. "estimator_status_hdg_test_ratio" ∧. 0 ≤. "estimator_status_vel_test_ratio" ∧.
      0 ≤. "estimator_status_pos_test_ratio" ∧. 0 ≤. "estimator_status_hgt_test_ratio"⟩,
  ⟨"accuracy", 0.1 ≤. "estimator_status_pos_horiz_accuracy" ∧.
      "estimator_status_pos_horiz_accuracy" ≤. 1 ∧. 0.1 ≤. "estimator_status_pos_vert_accuracy" ∧.
      "estimator_status_pos_vert_accuracy" ≤. 1 ∧. 0.1 ≤. "vehicle_local_position_eph" ∧.
      "vehicle_local_position_eph" ≤. 1 ∧. 0.1 ≤. "vehicle_local_position_epv" ∧.
      "vehicle_local_position_epv" ≤. 1 ∧. 0.1 ≤. "vehicle_global_position_eph" ∧.
      "vehicle_global_position_eph" ≤. 1 ∧. 0.1 ≤. "vehicle_global_position_epv" ∧.
      "vehicle_global_position_epv" ≤. 1 ∧. 0.3 ≤. "vehicle_gps_position_eph" ∧.
      "vehicle_gps_position_eph" ≤. 1 ∧. 0.3 ≤. "vehicle_gps_position_epv" ∧.
      "vehicle_gps_position_epv" ≤. 1.5⟩,
  ⟨"battery_charged", 15 ≤. "battery_status_voltage_v" ∧. "battery_status_voltage_v" ≤. 16.8 ∧.
      0.5 ≤. "battery_status_remaining" ∧. "battery_status_remaining" ≤. 1 ∧.
      0 ≤. "battery_status_current_a" ∧. "battery_status_current_a" ≤. 2 ∧.
      0 ≤. "battery_status_current_average_a" ∧. "battery_status_current_average_a" ≤. 2⟩,
  ⟨"at_home", abs "vehicle_local_position_x" ≤. 0.5 ∧. abs "vehicle_local_position_y" ≤. 0.5 ∧.
      abs "vehicle_local_position_z" ≤. 0.2 ∧. abs "vehicle_local_position_vx" ≤. 0.1 ∧.
      abs "vehicle_local_position_vy" ≤. 0.1 ∧. abs "vehicle_local_position_vz" ≤. 0.1 ∧.
      487.8 ≤. "vehicle_global_position_alt" ∧. "vehicle_global_position_alt" ≤. 488.2⟩]

private def freeNames (cs : List Clause) : List String := cs.flatMap (·.expr.vars)

private def isTime (n : String) : Bool := n.endsWith "_timestamp" || n.endsWith "_timestamp_sample"

/-- Every input field of `topics` pinned: to its value in `vals`, or 0 / false; except the fields
of `free` and the timestamps. Topic names are prefixes: a field of a topic whose name extends a
listed one (estimator_status_flags) is pinned with it. -/
private def ofTopics (topics : List String) (n : String) : Bool :=
  topics.any fun t => n.startsWith (t ++ "_")

def pinned (topics : List String) (vals : List (String × Expr)) (free : List String) :
    List Clause :=
  Ports.input.toList.filterMap fun f =>
    if !ofTopics topics f.name || free.contains f.name || isTime f.name then
      none
    else
      let v := (vals.lookup f.name).getD (if f.name.endsWith "_updated" || f.type == .bool then
        (if f.name.endsWith "_updated" then tt else ff) else num 0)
      -- NaN equals nothing: a NaN value is pinned as `x ≠ x`
      some ⟨s!"pin_{f.name}", if v == nan then ¬. (Expr.var f.name =. Expr.var f.name)
        else Expr.var f.name =. v⟩

/-- At most one command per tick, as a ground station sends them: arm or disarm (400; param1 1 or
0, param2 0..4, never the force value 21196), or a mode change (176; param1 0 or 1 = custom mode,
main modes 0-4, AUTO sub-modes 0-6), addressed to system 1, component 1, from the GCS (255, 190).
Each clause mentions one field, so the generator draws commands of every kind. -/
def gcsCommands : List Clause := [
  ⟨"one_command", "vehicle_command_count" ≤. 1⟩,
  ⟨"command_kind", anyOf "vehicle_command_command" [400, 176]⟩,
  ⟨"command_param1", anyOf "vehicle_command_param1" [0, 1]⟩,
  ⟨"command_main_mode", anyOf "vehicle_command_param2" [0, 1, 2, 3, 4]⟩,
  ⟨"command_sub_mode", anyOf "vehicle_command_param3" [0, 1, 2, 3, 4, 5, 6]⟩,
  ⟨"command_to_us", "vehicle_command_target_system" =. 1⟩,
  ⟨"command_to_autopilot", "vehicle_command_target_component" =. 1⟩,
  ⟨"command_from_gcs", "vehicle_command_source_system" =. 255⟩,
  ⟨"command_from_gcs_component", "vehicle_command_source_component" =. 190⟩,
  ⟨"command_external", "vehicle_command_from_external" =. tt⟩]

/-- The topics other modules publish that commander alone does not get in these regimes (no RC,
no offboard, no navigator, logger, allocator or magnetometer consistency check running). -/
def silentTopics : List String := ["manual_control_setpoint", "action_request",
  "offboard_control_mode", "mission_result", "navigator_status", "geofence_result",
  "actuator_motors", "logger_status", "sensor_preflight_mag"]

def silent : List Clause :=
  silentTopics.map fun t => ⟨s!"no_{t}", Expr.var s!"{t}_updated" =. ff⟩

/-- The clock and every timestamp of the healthy topics and the command: exactly one 400 Hz tick
(2500 us) per step from 1 s, so each message is stamped with the step's clock. -/
def tickHints : List Hint :=
  Hint.increasing "t_us" 1000000 2500 2500 :: ((Ports.input.toList.filter fun f =>
    isTime f.name && ofTopics ("vehicle_command" :: healthyTopics) f.name).map
      fun f => Hint.increasing f.name 1000000 2500 2500)

def groundPins : List Clause :=
  pinned healthyTopics (healthyValues ++ [("vehicle_land_detected_ground_contact", tt),
    ("vehicle_land_detected_maybe_landed", tt), ("vehicle_land_detected_landed", tt),
    ("vehicle_land_detected_at_rest", tt), ("estimator_status_flags_cs_vehicle_at_rest", tt)])
    (freeNames groundFree)

/-- A healthy X500 at rest on the ground in SITL, commanded by a ground station. -/
def x500Ground : Regime where
  name := "x500_ground"
  doc := "PX4 defaults, X500 SITL parameters, healthy sensors and estimator at rest, GCS commands"
  clauses := x500Params ++ groundPins ++ groundFree ++ gcsCommands ++ silent
  hints := tickHints

/-- In flight: the land detector and the estimator say airborne, 5-50 m above home, slow; the
ground station sends an arm command every tick (commander arms at its second pass, Commander.cpp
handle_command, and later arm commands are accepted as no-ops) and nothing else. -/
def flightFree : List Clause := groundFree.filter (·.name != "at_home") ++ [
  ⟨"airborne_near_home", abs "vehicle_local_position_x" ≤. 20 ∧.
      abs "vehicle_local_position_y" ≤. 20 ∧.
      -50 ≤. "vehicle_local_position_z" ∧. "vehicle_local_position_z" ≤. -5 ∧.
      abs "vehicle_local_position_vx" ≤. 2 ∧. abs "vehicle_local_position_vy" ≤. 2 ∧.
      abs "vehicle_local_position_vz" ≤. 1 ∧.
      493 ≤. "vehicle_global_position_alt" ∧. "vehicle_global_position_alt" ≤. 538⟩]

def flight : Regime where
  name := "flight"
  doc := "X500 SITL parameters, healthy, airborne, armed by the ground station"
  clauses := x500Params ++
    pinned healthyTopics (healthyValues ++ [("estimator_status_flags_cs_in_air", tt)])
      (freeNames flightFree) ++ flightFree ++ silent ++ [
    ⟨"arm_every_tick", "vehicle_command_count" =. 1 ∧. "vehicle_command_command" =. 400 ∧.
      "vehicle_command_param1" =. 1 ∧. "vehicle_command_param2" =. 0 ∧.
      "vehicle_command_target_system" =. 1 ∧. "vehicle_command_target_component" =. 1 ∧.
      "vehicle_command_source_system" =. 255 ∧. "vehicle_command_source_component" =. 190 ∧.
      "vehicle_command_from_external" =. tt⟩]
  hints := tickHints

/-- Any inputs the assumption allows, with the clock of a 400 Hz lockstep: t_us advances by one
tick per step. Without it (campaigns with no regime, seeds 1-3, 20 x 100) `no_px4_error` fails with
"vehicle_command lost, generation 6 -> 11": t_us is then drawn at random, so it jumps backwards,
commander's 10 ms sleep (a deadline on the clock) is not over for many steps, and the commands
queued meanwhile overflow the queue of 8. PX4's clock is monotonic; that the harness clock is
needs the previous tick, which the contract language does not have, so it is this regime's hint. -/
def clocked : Regime where
  name := "clocked"
  doc := "any inputs and parameters the assumption allows; t_us advancing 2500 us per step"
  clauses := []
  hints := [.increasing "t_us" 1000000 2500 2500]

def coverage : List Clause := [
  ⟨"armed", "actuator_armed_armed" =. tt⟩,
  ⟨"status_published", "vehicle_status_updated" =. tt⟩,
  ⟨"command_accepted", 1 ≤. "vehicle_command_ack_by_px4_commander_count" ∧.
      "vehicle_command_ack_by_px4_commander_result" =. 0⟩,
  ⟨"command_refused", 1 ≤. "vehicle_command_ack_by_px4_commander_count" ∧.
      ¬. ("vehicle_command_ack_by_px4_commander_result" =. 0)⟩,
  ⟨"not_loiter", ¬. navIs 4⟩,
  ⟨"failsafe", "vehicle_status_failsafe" =. tt⟩,
  ⟨"preflight_ok", "vehicle_status_pre_flight_checks_pass" =. tt⟩]

def module : Module where
  name := "px4_commander"
  doc := "PX4 commander (v1.17.0), unmodified: a task module run by the shim"
  params := Ports.params
  input := Ports.input
  output := Ports.output
  contract := { contract with guarantee := contract.guarantee ++ Ports.outWidths }
  exe := "build/modules/px4_commander/px4_commander"
  stack := .px4
  regimes := [x500Ground, flight, clocked]
  coverage := coverage

end Px4.Modules.Px4Commander
