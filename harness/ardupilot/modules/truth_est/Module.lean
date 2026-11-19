import Harness.Module

/-! # truth_est: the simulator's truth under the estimator's signal names (a test fixture)

Stands where the estimator stage (AP_InertialSensor, AP_AHRS, EKF3) will be: it copies the
plant's true state of the tick into the names the supervisor and the controller stages read, as
a perfect estimator would report it. It is not ArduPilot code. The names are the estimator
module's (`est_pos_ok`, `est_vel_ok`, `est_pos_rate_d`, `est_accel_ef_z`, `est_gain_scaler_xy`,
…), which the controller stages read since h-apctl reconciled them (the copy in h-sup also
produced the position stage's former names). The air-density ratio is computed from the
simulated barometer (h-apctl's change; h-sup's copy gave 1). Health and status are constant: healthy,
variances 0, a 3D GPS fix with 10 satellites, no EKF resets. The EKF origin is the parameter
record's (the simulator's NED origin is the gorge's geographic origin, home). Euler angles are
ArduPilot's to_euler of the quaternion (body FRD to NED, q1 scalar). -/

namespace Ardupilot.Modules.TruthEst

open Harness Harness.Contract.Lang

private def f (n d : String) : Field := { name := n, type := .f32, doc := d }
private def b (n d : String) : Field := { name := n, type := .bool, doc := d }
private def u (n d : String) : Field := { name := n, type := .u32, doc := d }
private def i (n d : String) : Field := { name := n, type := .i32, doc := d }

def params : Schema := #[
  i "origin_lat_e7" "EKF origin latitude, 1e-7 deg (the simulator's NED origin)",
  i "origin_lon_e7" "EKF origin longitude, 1e-7 deg",
  i "origin_alt_cm" "EKF origin altitude AMSL, cm"]

def input : Schema := #[
  f "pos_n" "plant: true position north of home, m", f "pos_e" "east", f "pos_d" "down",
  f "vel_n" "plant: true velocity north, m/s", f "vel_e" "east", f "vel_d" "down",
  f "q1" "plant: attitude quaternion body to NED, scalar", f "q2" "x", f "q3" "y", f "q4" "z",
  f "imu2_ax" "plant: last IMU sample of the tick, specific force x, m/s/s", f "imu2_ay" "y",
  f "imu2_az" "z", f "imu2_gx" "plant: last IMU sample, gyro x, rad/s", f "imu2_gy" "y",
  f "imu2_gz" "z",
  b "baro_fresh" "plant: a barometer sample this tick", f "baro_pa" "plant: pressure, Pa",
  f "baro_degc" "plant: temperature, degC"]

def output : Schema := #[
  f "gyro_x" "latest gyro x (imu2_gx), rad/s", f "gyro_y" "y", f "gyro_z" "z",
  f "est_q1" "attitude quaternion (q1)", f "est_q2" "q2", f "est_q3" "q3", f "est_q4" "q4",
  f "est_roll" "roll, rad (to_euler)", f "est_pitch" "pitch, rad", f "est_yaw" "yaw, rad",
  f "est_sin_yaw" "sin(yaw)", f "est_cos_yaw" "cos(yaw)",
  b "est_pos_ok" "position valid (true)", f "est_pos_n" "position north of the origin, m (pos_n)",
  f "est_pos_e" "east (pos_e)", f "est_pos_d" "down (pos_d)",
  b "est_vel_ok" "velocity valid (true)",
  f "est_vel_n" "velocity north, m/s", f "est_vel_e" "east", f "est_vel_d" "down",
  b "est_pos_rate_d_ok" "vertical position rate valid (true)",
  f "est_pos_rate_d" "vertical position rate down, m/s (vel_d)",
  f "est_accel_ef_x" "earth-frame specific force north, m/s/s (R * imu2_a)",
  f "est_accel_ef_y" "east", f "est_accel_ef_z" "down",
  f "est_accel_x" "IMU specific force x (imu2_ax), m/s/s", f "est_accel_y" "y",
  f "est_accel_z" "z", f "est_gyro_x" "IMU gyro x (imu2_gx), rad/s", f "est_gyro_y" "y",
  f "est_gyro_z" "z",
  f "est_gyro_drift_x" "gyro drift estimate (0)", f "est_gyro_drift_y" "0",
  f "est_gyro_drift_z" "0",
  f "est_gain_scaler_xy" "AP_AHRS::get_control_gain_scaler_XY() (1)",
  f "est_gain_scaler_z" "get_control_gain_scaler_Z() (1)",
  b "est_origin_ok" "origin set (true)", i "est_origin_lat_e7" "origin latitude (parameter)",
  i "est_origin_lon_e7" "origin longitude", i "est_origin_alt_cm" "origin altitude, cm",
  b "est_healthy" "healthy (true)", b "est_initialised" "initialised (true)",
  u "est_filter_status" "nav_filter_status: attitude, velocities, positions, predictions, \
    using GPS, GPS good, initialised (0x1A33F)",
  b "est_variances_ok" "variances valid (true)", f "est_vel_variance" "0",
  f "est_pos_variance" "0", f "est_hgt_variance" "0", f "est_mag_variance_x" "0",
  f "est_mag_variance_y" "0", f "est_mag_variance_z" "0",
  u "est_pos_ne_reset_count" "0", u "est_pos_d_reset_count" "0", u "est_yaw_reset_count" "0",
  f "est_baro_alt" "barometric altitude above home, m (-pos_d)",
  u "est_gps_status" "AP_GPS_FixType FIX_3D (3)", u "est_gps_num_sats" "10",
  f "air_density_ratio" "AP_AHRS::get_air_density_ratio(): rho / SSL_AIR_DENSITY with rho = \
    p / (ISA_GAS_CONSTANT T) from the newest barometer sample, held between samples, 1 before \
    the first",
  b "est_prearm_ok" "true", b "est_ins_accel_healthy" "true", b "est_ins_gyro_healthy" "true",
  b "est_baro_healthy" "true", b "est_gps_healthy" "true",
  u "est_gps_hdop" "100 (1.00)", u "est_gps_vdop" "100",
  f "est_vibe_x" "0", f "est_vibe_y" "0", f "est_vibe_z" "0", u "est_accel_clip_count" "0",
  b "est_innov_ok" "true", f "est_innov_vel_n" "0", f "est_innov_vel_e" "0",
  f "est_innov_vel_d" "0", f "est_innov_pos_n" "0", f "est_innov_pos_e" "0",
  f "est_innov_pos_d" "0"]

def contract : Contract where
  assume := [⟨"state_finite", finite "pos_n" ∧. finite "pos_e" ∧. finite "pos_d" ∧.
    finite "vel_n" ∧. finite "vel_e" ∧. finite "vel_d" ∧. finite "q1" ∧. finite "q2" ∧.
    finite "q3" ∧. finite "q4"⟩]
  guarantee := [⟨"copies_position", "est_pos_n" =. "pos_n" ∧. "est_pos_e" =. "pos_e" ∧.
    "est_pos_d" =. "pos_d"⟩]

def module : Module where
  name := "truth_est"
  doc := "the simulator's truth under the estimator's signal names (test fixture)"
  params := params
  input := input
  output := output
  contract := contract
  exe := "build/modules/truth_est/truth_est"
  stack := .ardupilot

end Ardupilot.Modules.TruthEst
