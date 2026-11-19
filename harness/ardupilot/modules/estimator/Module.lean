import Harness.Module

/-! # estimator: ArduCopter's estimation chain

The real front ends `AP_InertialSensor`, `AP_Baro`, `Compass`, `AP_GPS`, the `AP_AHRS` with its
DCM and EKF3 backends, `NavEKF3` (libraries/AP_NavEKF3, reading the sensors through `AP_DAL`),
set up as ArduCopter sets them up and stepped as ArduCopter steps them. Built by
`ardupilot/modules/estimator/build.sh` from the unmodified sources in sources.txt; adapter.cpp is the cut,
the backend_*.cpp files are the sensor drivers' stand-ins, the stubs_*.cpp files what else is
outside.

Boot. ArduCopter's `init_ardupilot` blocks in `delay()` while it calibrates the barometer and the
gyros; in SITL the simulator runs during those delays. Here the boot runs in its own thread from
`init`, and every `delay` waits for the steps that bring the time past its end: the first steps
of a case are the boot (`est_booted` false, every estimate output 0). Then each step is one
400 Hz loop of ArduCopter: the sensor drivers' timers (the step's samples), `ins.update()`
(the first fast task), `ahrs.update(true)` (`Copter::read_AHRS`), then the scheduler's slow
tasks when due: `gps.update()` at 50 Hz, `compass.read()` at 10 Hz (`update_batt_compass`),
`barometer.update()` at 10 Hz (`update_altitude`).

The attitude outputs (gyro_*, est_q*, est_roll/pitch/yaw, the trig values, est_gyro_*) are read
from `ahrs_view`, the AP_AHRS_View with ROTATION_NONE that ArduCopter creates in allocate_motors
and on which it constructs the attitude and position controllers and the navigation libraries;
the rest from AP_AHRS (the view forwards those). Frames and units as ArduPilot's: NED, body FRD,
m, m/s, m/s^2, rad, rad/s. -/

namespace Ardupilot.Modules.Estimator

open Harness Harness.Contract.Lang

private def f (n d : String) : Field := { name := n, type := .f32, doc := d }
private def i (n d : String) : Field := { name := n, type := .i32, doc := d }
private def u (n d : String) : Field := { name := n, type := .u32, doc := d }
private def b (n d : String) : Field := { name := n, type := .bool, doc := d }

/-! ### Parameters -/

def params : Schema := #[
  f "ek3_velne_m_nse" "EK3_VELNE_M_NSE: GPS horizontal velocity noise, m/s (_gpsHorizVelNoise)",
  f "ek3_veld_m_nse" "EK3_VELD_M_NSE: GPS vertical velocity noise, m/s (_gpsVertVelNoise)",
  i "ek3_vel_i_gate" "EK3_VEL_I_GATE: GPS velocity innovation gate, % (_gpsVelInnovGate)",
  f "ek3_posne_m_nse" "EK3_POSNE_M_NSE: GPS horizontal position noise, m (_gpsHorizPosNoise)",
  i "ek3_pos_i_gate" "EK3_POS_I_GATE: GPS position innovation gate, % (_gpsPosInnovGate)",
  i "ek3_glitch_rad" "EK3_GLITCH_RAD: GPS glitch radius, m (_gpsGlitchRadiusMax)",
  f "ek3_alt_m_nse" "EK3_ALT_M_NSE: altitude measurement noise, m (_baroAltNoise)",
  i "ek3_hgt_i_gate" "EK3_HGT_I_GATE: height innovation gate, % (_hgtInnovGate)",
  i "ek3_hgt_delay" "EK3_HGT_DELAY: height measurement delay, ms (_hgtDelay_ms)",
  f "ek3_mag_m_nse" "EK3_MAG_M_NSE: magnetometer noise, gauss (_magNoise)",
  i "ek3_mag_cal" "EK3_MAG_CAL: magnetometer calibration mode (_magCal)",
  i "ek3_mag_i_gate" "EK3_MAG_I_GATE: magnetometer innovation gate, % (_magInnovGate)",
  f "ek3_gyro_p_nse" "EK3_GYRO_P_NSE: rate gyro process noise, rad/s (_gyrNoise)",
  f "ek3_acc_p_nse" "EK3_ACC_P_NSE: accelerometer process noise, m/s^2 (_accNoise)",
  f "ek3_gbias_p_nse" "EK3_GBIAS_P_NSE: gyro bias process noise, rad/s^2 (_gyroBiasProcessNoise)",
  f "ek3_abias_p_nse" "EK3_ABIAS_P_NSE: accel bias process noise, m/s^3 (_accelBiasProcessNoise)",
  f "ek3_mage_p_nse" "EK3_MAGE_P_NSE: earth field process noise, gauss/s (_magEarthProcessNoise)",
  f "ek3_magb_p_nse" "EK3_MAGB_P_NSE: body field process noise, gauss/s (_magBodyProcessNoise)",
  i "ek3_gps_check" "EK3_GPS_CHECK: GPS preflight check bitmask (_gpsCheck)",
  i "ek3_check_scale" "EK3_CHECK_SCALE: GPS accuracy check scaler, % (_gpsCheckScaler)",
  f "ek3_noaid_m_nse" "EK3_NOAID_M_NSE: non-GPS operation position noise, m (_noaidHorizNoise)",
  f "ek3_yaw_m_nse" "EK3_YAW_M_NSE: yaw measurement noise, rad (_yawNoise)",
  i "ek3_yaw_i_gate" "EK3_YAW_I_GATE: yaw innovation gate, % (_yawInnovGate)",
  i "ek3_tau_output" "EK3_TAU_OUTPUT: output complementary filter time constant, cs",
  f "ek3_acc_bias_lim" "EK3_ACC_BIAS_LIM: accelerometer bias limit, m/s^2 (_accBiasLim)",
  i "ek3_mag_ef_lim" "EK3_MAG_EF_LIM: earth field error limit, mGauss (_mag_ef_limit)",
  f "ek3_err_thresh" "EK3_ERR_THRESH: lane relative error sensitivity (_err_thresh)",
  i "ek3_imu_mask" "EK3_IMU_MASK: IMUs that start a core (_imuMask)",
  i "ahrs_ekf_type" "AHRS_EKF_TYPE: 3 = EKF3 (_ekf_type)",
  f "ahrs_trim_x" "AHRS_TRIM_X: autopilot-to-vehicle roll trim, rad (_trim.x)",
  f "ahrs_trim_y" "AHRS_TRIM_Y: pitch trim, rad (_trim.y)",
  i "ins_gyro_filter" "INS_GYRO_FILTER: gyro low-pass cutoff, Hz, 0 off (_gyro_filter_cutoff)",
  i "ins_accel_filter" "INS_ACCEL_FILTER: accel low-pass cutoff, Hz, 0 off (_accel_filter_cutoff)",
  i "ins_gyr_cal" "INS_GYR_CAL: 0 never, 1 gyro calibration at boot (_gyro_cal_timing)",
  f "ins_accoffs_x" "INS_ACCOFFS_X: accelerometer offset, m/s^2 (_accel_offset(0).x)",
  f "ins_accoffs_y" "INS_ACCOFFS_Y (_accel_offset(0).y)",
  f "ins_accoffs_z" "INS_ACCOFFS_Z (_accel_offset(0).z)",
  f "ins_gyroffs_x" "INS_GYROFFS_X: gyro offset, rad/s (_gyro_offset(0).x; boot cal sets it)",
  f "ins_gyroffs_y" "INS_GYROFFS_Y (_gyro_offset(0).y)",
  f "ins_gyroffs_z" "INS_GYROFFS_Z (_gyro_offset(0).z)",
  i "compass_use" "COMPASS_USE: compass used for yaw (_use_for_yaw[0])",
  i "compass_autodec" "COMPASS_AUTODEC: declination from the world model table",
  f "compass_dec" "COMPASS_DEC: declination, rad, when COMPASS_AUTODEC = 0 (_declination)",
  i "gps1_delay_ms" "GPS1_DELAY_MS: GPS delay, ms, 0 uses the driver's (params[0].delay_ms)"]

/-! ### Inputs -/

def imuFields : List Field :=
  (List.range 3).flatMap fun s =>
    [("ax", "specific force x, m/s^2"), ("ay", "specific force y"), ("az", "specific force z"),
     ("gx", "rate x, rad/s"), ("gy", "rate y"), ("gz", "rate z")].map fun (c, d) =>
      f s!"imu{s}_{c}" s!"IMU sample {s} of the tick (plant_sim's), sensor frame FRD: {d}"

def input : Schema := #[
  u "t_us" "the time of the tick, us since init: the HAL clock (micros, millis, micros64)"] ++
  imuFields.toArray ++ #[
  b "baro_fresh" "a barometer sample this tick: the baro driver's timer takes it",
  f "baro_pa" "static pressure, Pa", f "baro_degc" "temperature, degC",
  b "mag_fresh" "a compass sample this tick: the compass driver's timer takes it",
  f "mag_x" "body field x, mGauss", f "mag_y" "body field y", f "mag_z" "body field z",
  b "gps_fresh" "a GPS fix this tick: the GPS driver's read() returns it",
  i "gps_lat_e7" "latitude, 1e-7 deg", i "gps_lon_e7" "longitude, 1e-7 deg",
  f "gps_alt" "altitude AMSL, m", f "gps_vn" "velocity north, m/s", f "gps_ve" "east",
  f "gps_vd" "down",
  b "armed" "hal.util->get_soft_armed(): the arming state (AP_DAL reads it for EKF3)",
  b "likely_flying" "AP_Vehicle::set_likely_flying (Copter::set_land_complete); EKF3 reads \
    AP_Vehicle::get_time_flying_ms",
  b "cmd_estimator_set_takeoff_expected" "AP_AHRS::set_takeoff_expected called this tick \
    (AP_GroundEffect, from Copter::update_ground_effect_detector)",
  b "cmd_estimator_set_takeoff_expected_b" "its argument",
  b "cmd_estimator_set_touchdown_expected" "AP_AHRS::set_touchdown_expected called this tick",
  b "cmd_estimator_set_touchdown_expected_b" "its argument",
  b "cmd_estimator_set_home" "AP_AHRS::set_home called this tick (Copter::set_home)",
  i "cmd_estimator_set_home_lat_e7" "its location: latitude, 1e-7 deg",
  i "cmd_estimator_set_home_lon_e7" "longitude, 1e-7 deg",
  i "cmd_estimator_set_home_alt_cm" "altitude, cm, absolute",
  b "cmd_estimator_reset_height_datum" "AP_AHRS::resetHeightDatum called this tick \
    (AP_Arming_Copter::arm)",
  b "cmd_estimator_request_yaw_reset" "AP_AHRS::request_yaw_reset called this tick \
    (Copter::ekf_check)",
  b "cmd_estimator_set_terrain_hgt_stable" "AP_AHRS::set_terrain_hgt_stable called this tick \
    (Copter::update_ekf_terrain_height_stable, baro_ground_effect.cpp:29-39)",
  b "cmd_estimator_set_terrain_hgt_stable_stable" "its argument"]

/-! ### Outputs -/

def output : Schema := #[
  f "gyro_x" "ahrs_view.get_gyro_latest().x (AP_AHRS_View, ROTATION_NONE: = AP_AHRS's): newest \
    filtered gyro plus the drift correction, rad/s",
  f "gyro_y" "get_gyro_latest().y", f "gyro_z" "get_gyro_latest().z",
  f "est_q1" "ahrs_view.get_quat_body_to_ned: body (FRD) to NED, scalar", f "est_q2" "x",
  f "est_q3" "y", f "est_q4" "z",
  f "est_roll" "ahrs_view.get_roll_rad()", f "est_pitch" "get_pitch_rad()",
  f "est_yaw" "get_yaw_rad()",
  f "est_sin_yaw" "ahrs_view.sin_yaw()", f "est_cos_yaw" "cos_yaw()",
  f "est_cos_roll" "cos_roll()", f "est_cos_pitch" "cos_pitch()",
  b "est_pos_ok" "get_relative_position_NED_origin returned true",
  f "est_pos_n" "get_relative_position_NED_origin: north of the EKF origin, m",
  f "est_pos_e" "east, m", f "est_pos_d" "down, m",
  b "est_vel_ok" "get_velocity_NED returned true",
  f "est_vel_n" "get_velocity_NED: north, m/s", f "est_vel_e" "east", f "est_vel_d" "down",
  b "est_pos_rate_d_ok" "get_vert_pos_rate_D returned true",
  f "est_pos_rate_d" "get_vert_pos_rate_D: rate of change of the down position, m/s",
  f "est_gyro_x" "ahrs_view.get_gyro(): drift-corrected gyro of the active IMU, rad/s",
  f "est_gyro_y" "get_gyro().y", f "est_gyro_z" "get_gyro().z",
  f "est_gyro_offset_x" "AP::ins().get_gyro_offsets(0): gyro offset (INS_GYROFFS_X, set by the \
    boot calibration when INS_GYR_CAL = 1), rad/s",
  f "est_gyro_offset_y" "get_gyro_offsets(0).y", f "est_gyro_offset_z" "get_gyro_offsets(0).z",
  f "est_gyro_drift_x" "get_gyro_drift(): estimated gyro drift (minus the EKF's bias), rad/s",
  f "est_gyro_drift_y" "get_gyro_drift().y", f "est_gyro_drift_z" "get_gyro_drift().z",
  f "est_accel_x" "AP::ins().get_accel(): filtered specific force, body, m/s^2",
  f "est_accel_y" "get_accel().y", f "est_accel_z" "get_accel().z",
  f "est_accel_ef_x" "get_accel_ef(): earth-frame acceleration (NED, includes gravity), m/s^2",
  f "est_accel_ef_y" "get_accel_ef().y", f "est_accel_ef_z" "get_accel_ef().z",
  b "est_origin_ok" "get_origin returned true",
  i "est_origin_lat_e7" "EKF origin latitude, 1e-7 deg", i "est_origin_lon_e7" "longitude",
  i "est_origin_alt_cm" "EKF origin altitude AMSL, cm",
  b "est_home_set" "home_is_set()", i "est_home_lat_e7" "get_home(): latitude, 1e-7 deg",
  i "est_home_lon_e7" "longitude", i "est_home_alt_cm" "altitude, cm",
  b "est_loc_ok" "get_location returned true", i "est_loc_lat_e7" "latitude, 1e-7 deg",
  i "est_loc_lon_e7" "longitude", i "est_loc_alt_cm" "altitude AMSL, cm",
  b "est_healthy" "AP_AHRS::healthy()", b "est_initialised" "AP_AHRS::initialised()",
  b "est_have_inertial_nav" "have_inertial_nav()",
  u "est_filter_status" "get_filter_status_for_configured_backend: nav_filter_status.value",
  b "est_ekf_attitude" "nav_filter_status.flags.attitude (0x1)",
  b "est_ekf_horiz_vel" "flags.horiz_vel (0x2)", b "est_ekf_vert_pos" "flags.vert_pos (0x20)",
  b "est_ekf_horiz_pos_abs" "flags.horiz_pos_abs (0x10)",
  b "est_ekf_const_pos_mode" "flags.const_pos_mode (0x80): no aiding, position held",
  b "est_ekf_using_gps" "flags.using_gps (0x2000)",
  b "est_variances_ok" "get_variances_for_configured_backend returned true",
  f "est_vel_variance" "its velocity test ratio", f "est_pos_variance" "position test ratio",
  f "est_hgt_variance" "height test ratio", f "est_mag_variance_x" "magnetometer test ratio x",
  f "est_mag_variance_y" "y", f "est_mag_variance_z" "z", f "est_tas_variance" "airspeed",
  u "est_pos_ne_reset_count" "get_position_NE_reset_count() (read by AC_PosControl)",
  u "est_pos_d_reset_count" "get_position_D_reset_count() (read by AC_PosControl)",
  u "est_yaw_reset_count" "get_yaw_reset_count() (read by Copter::check_ekf_reset)",
  u "est_attitude_reset_count" "get_last_attitude_reset_count() (Copter::check_ekf_reset)",
  f "est_gain_scaler_xy" "get_control_gain_scaler_XY() (read by AC_PosControl)",
  f "est_gain_scaler_z" "get_control_gain_scaler_Z() (read by AC_PosControl)",
  f "est_gnd_spd_limit" "get_control_ground_speed_limit_ms(), m/s (read by AC_Loiter; added with \
    the loiter stage)",
  f "air_density_ratio" "get_air_density_ratio(): the mixer's input of that name",
  f "est_baro_alt" "barometer.get_altitude(): altitude above the calibration point, m",
  u "est_gps_status" "gps.status(): 0 none, 1 no fix, 2 2D, 3 3D, ...",
  u "est_gps_num_sats" "gps.num_sats()",
  b "est_booted" "init_ardupilot's sensor part has finished; before it every estimate is 0",
  b "est_config_error" "AP_BoardConfig::config_error raised in the boot: ArduPilot stays in its \
    error loop, the boot never finishes",
  u "est_loop_ticks" "400 Hz loops run since the boot finished (AP_Scheduler's ticks, 32 bits)",
  b "est_ekf_started" "the EKF3 backend has started (InitialiseFilter succeeded)",
  u "est_internal_errors" "ArduPilot internal errors raised since init",
  -- added in h-sup (round 3): what only the estimator knows, for the supervisor
  b "est_prearm_ok" "AP_AHRS::pre_arm_check(true, ...): the AHRS/EKF arming verdict",
  b "est_ins_accel_healthy" "AP_InertialSensor::get_accel_health_all()",
  b "est_ins_gyro_healthy" "AP_InertialSensor::get_gyro_health_all()",
  b "est_baro_healthy" "AP_Baro::all_healthy()",
  b "est_gps_healthy" "AP_GPS::is_healthy(0)",
  u "est_gps_hdop" "AP_GPS::get_hdop() (1/100)", u "est_gps_vdop" "AP_GPS::get_vdop() (1/100)",
  f "est_vibe_x" "AP_InertialSensor::get_vibration_levels(0).x, m/s/s",
  f "est_vibe_y" "vibration y", f "est_vibe_z" "vibration z",
  u "est_accel_clip_count" "AP_InertialSensor::get_accel_clip_count(0)",
  b "est_innov_ok" "AP_AHRS::get_innovations returned true",
  f "est_innov_vel_n" "velocity innovation north, m/s", f "est_innov_vel_e" "east",
  f "est_innov_vel_d" "down",
  f "est_innov_pos_n" "position innovation north, m", f "est_innov_pos_e" "east",
  f "est_innov_pos_d" "down",
  u "est_text_seq" "status texts handed over so far (GCS::send_text of the estimator's code, one per tick)",
  u "est_text_severity" "MAV_SEVERITY of this tick's text",
  u "est_text_len" "characters of this tick's status text (0: none this tick; at most 50)"] ++
  ((List.range 13).map fun k =>
    u s!"est_text_w{if k < 10 then "0" else ""}{k}" s!"status text bytes {4*k}..{4*k+3}, little-endian").toArray

/-! ### Contract -/

private def v (n : String) : Expr := .var n

private def conj : List Expr → Expr
  | [] => tt
  | [e] => e
  | e :: es => e ∧. conj es

private def within (n : String) (lo hi : Expr) : Expr := lo ≤. v n ∧. v n ≤. hi

/-- A negative literal as one literal (`-x` in the clause language is a negation of a literal,
which the generator does not read as a bound of an integer field). -/
private def negLit (x : Float32) : Expr := .lit (-x).toBits

/-- Every f32 output field, for `outputs_finite`. -/
def floatOutputs : List String := (output.toList.filter (·.type == .f32)).map (·.name)

/-- The outputs that hold an estimate (all but the boot flag, the loop count and the error
count), zero before the boot has finished. -/
def estimateOutputs : List String :=
  floatOutputs

/-- ArduPilot's documented ranges (@Range in AP_NavEKF3.cpp, AP_AHRS.cpp,
AP_InertialSensor.cpp, AP_Compass.cpp, AP_GPS_Params.cpp), each parameter on its own, and the
values the module supports where the code allows more: AHRS_EKF_TYPE 3 (EKF3; 2 is mapped to 3
by AP_AHRS::init; the SIM and external types are compiled out, flags.txt); EK3_IMU_MASK 1 or 3
(the one IMU must start a core); INS_GYR_CAL 0 or 1. -/
def assumeParams : List Clause := [
  ⟨"ek3_noise_range", conj [within "ek3_velne_m_nse" 0.05 5, within "ek3_veld_m_nse" 0.05 5,
      within "ek3_posne_m_nse" 0.1 10, within "ek3_alt_m_nse" 0.01 100,
      within "ek3_mag_m_nse" 0.01 0.5, within "ek3_gyro_p_nse" 0.0001 0.1,
      within "ek3_acc_p_nse" 0.01 1, within "ek3_gbias_p_nse" 0.00001 0.001,
      within "ek3_abias_p_nse" 0.00001 0.02, within "ek3_mage_p_nse" 0.00001 0.01,
      within "ek3_magb_p_nse" 0.00001 0.01, within "ek3_noaid_m_nse" 0.5 50,
      within "ek3_yaw_m_nse" 0.05 1]⟩,
  ⟨"ek3_gate_range", conj [within "ek3_vel_i_gate" 100 1000, within "ek3_pos_i_gate" 100 1000,
      within "ek3_hgt_i_gate" 100 1000, within "ek3_mag_i_gate" 100 1000,
      within "ek3_yaw_i_gate" 100 1000, within "ek3_glitch_rad" 10 100]⟩,
  ⟨"ek3_other_range", conj [within "ek3_hgt_delay" 0 250, within "ek3_mag_cal" 0 7,
      within "ek3_gps_check" 0 255, within "ek3_check_scale" 50 200,
      within "ek3_tau_output" 10 50, within "ek3_acc_bias_lim" 0.5 2.5,
      within "ek3_mag_ef_lim" 0 500, within "ek3_err_thresh" 0.05 1,
      v "ek3_imu_mask" =. 1 ∨. v "ek3_imu_mask" =. 3]⟩,
  ⟨"ahrs_range", v "ahrs_ekf_type" =. 3 ∧. within "ahrs_trim_x" (-0.1745) 0.1745 ∧.
      within "ahrs_trim_y" (-0.1745) 0.1745⟩,
  ⟨"ins_range", conj [within "ins_gyro_filter" 0 256, within "ins_accel_filter" 0 256,
      within "ins_gyr_cal" 0 1, within "ins_accoffs_x" (-3.5) 3.5,
      within "ins_accoffs_y" (-3.5) 3.5, within "ins_accoffs_z" (-3.5) 3.5,
      within "ins_gyroffs_x" (-0.2) 0.2, within "ins_gyroffs_y" (-0.2) 0.2,
      within "ins_gyroffs_z" (-0.2) 0.2]⟩,
  ⟨"compass_gps_range", conj [within "compass_use" 0 1, within "compass_autodec" 0 1,
      within "compass_dec" (-3.1416) 3.1416, within "gps1_delay_ms" 0 250]⟩]

/-- The input assumption as first stated, kept for the record, not used. Composition refuted it
at once (ardupilot/harnesses/est_loop, campaign rest_quiet seed 1, case 0 step 0: discharge failure of
`baro_range`): plant_sim reports `baro_pa` = `baro_degc` = 0 when `baro_fresh` is false (and
likewise for the compass and the GPS), and 0 Pa is outside the range. The drivers read a sample
only when it is fresh (backend_baro.cpp, backend_compass.cpp, backend_gps.cpp), so the ranges
are now required of fresh samples only. The module's own first campaign (regime ticked, seed 1,
20 x 1500) had refuted `air_density_range` before (240 steps, first case 3 step 941:
air_density_ratio 2.4155): with pressures from 10 kPa to 120 kPa the barometer's calibration
(the mean of five random pressures) and a later pressure put the altitude AMSL kilometres below
sea level, where the 1976 density ratio exceeds 2 (AP_Baro::_get_EAS2TAS, AP_AHRS.cpp:2134); the
pressure and GPS altitude ranges are now narrower. A third finding (regime ticked, seed 2, 20 x
3000): the process ended with AP_HAL::panic("uninitialised location returned by _get_location"),
the SITL build's own check in AP_AHRS::update_state (AP_AHRS.cpp, under CONFIG_HAL_BOARD ==
HAL_BOARD_SITL): a GPS fix at latitude 0, longitude 0 (an edge value the generator draws) became
the EKF origin, and the location EKF3 then returned, the origin with no offset and altitude 0, is
what Location::initialised() takes for "not set". Fixes at exactly (0, 0) are now excluded
(`gps_not_null_island`).

As first stated: sensor samples within the ranges of real sensors (16 g, 2000 deg/s, pressure
from 0 to about 15 km and above sea level, 8 gauss, any position, 100 m/s); the vehicle's
commands' arguments likewise. Every f32 input is bounded, so finite. The clock is not in the
clause language (it has no previous tick): the campaigns advance t_us by 2500 us per step
(regime hints), as plant_sim does; the contract is stated for that clock. -/
def assumeInputsAsFirstStated : List Clause := [
  ⟨"imu_range", conj ((List.range 3).flatMap fun s =>
      ["ax", "ay", "az"].map (fun c => abs (v s!"imu{s}_{c}") ≤. 160) ++
      ["gx", "gy", "gz"].map (fun c => abs (v s!"imu{s}_{c}") ≤. 35))⟩,
  ⟨"baro_range", within "baro_pa" 10000 120000 ∧. within "baro_degc" (-60) 80⟩,
  ⟨"mag_range", abs (v "mag_x") ≤. 8000 ∧. abs (v "mag_y") ≤. 8000 ∧. abs (v "mag_z") ≤. 8000⟩,
  ⟨"gps_range", conj [within "gps_lat_e7" (-900000000) 900000000,
      within "gps_lon_e7" (-1800000000) 1800000000, within "gps_alt" (-500) 10000,
      abs (v "gps_vn") ≤. 100, abs (v "gps_ve") ≤. 100, abs (v "gps_vd") ≤. 100]⟩,
  -- not a fix at latitude 0, longitude 0: see assumeInputsAsFirstStated
  ⟨"gps_not_null_island", ¬. v "gps_fresh" ∨. ¬. (v "gps_lat_e7" =. 0 ∧. v "gps_lon_e7" =. 0)⟩,
  ⟨"home_range", conj [within "cmd_estimator_set_home_lat_e7" (-900000000) 900000000,
      within "cmd_estimator_set_home_lon_e7" (-1800000000) 1800000000,
      within "cmd_estimator_set_home_alt_cm" (-50000) 1000000]⟩]

/-- Sensor samples within the ranges of real sensors (16 g, 2000 deg/s, 8 gauss, any position,
100 m/s) and of the vehicle's operating altitudes (pressure from 5.5 km above to 0.6 km below sea
level, GPS altitude from -500 m to 6000 m); a stale pressure (plant_sim's 0) is allowed, a fresh
one must be in range; the vehicle's commands' arguments within ranges. The altitude ranges
keep the barometer's altitude AMSL (its altitude relative to the calibration plus the EKF
origin's altitude, AP_Baro::get_altitude_AMSL) between about -6.6 km and 12.1 km, where the 1976
atmosphere's density ratio, AP_AHRS::get_air_density_ratio, is between 0.24 and 1.8: within the
mixer's assumption (at most 2). The clock is not in the clause
language (it has no previous tick): the campaigns advance t_us by 2500 us per step (regime
hints), as plant_sim does; the contract is stated for that clock. -/
def assumeInputs : List Clause := [
  ⟨"imu_range", conj ((List.range 3).flatMap fun s =>
      ["ax", "ay", "az"].map (fun c => abs (v s!"imu{s}_{c}") ≤. 160) ++
      ["gx", "gy", "gz"].map (fun c => abs (v s!"imu{s}_{c}") ≤. 35))⟩,
  -- a stale sample is 0 in plant_sim; 0 is within every range but the pressure's
  ⟨"baro_range", (v "baro_pa" =. 0 ∨. within "baro_pa" 50000 108000) ∧.
      within "baro_degc" (-60) 80 ∧. (¬. v "baro_fresh" ∨. within "baro_pa" 50000 108000)⟩,
  ⟨"mag_range", abs (v "mag_x") ≤. 8000 ∧. abs (v "mag_y") ≤. 8000 ∧. abs (v "mag_z") ≤. 8000⟩,
  ⟨"gps_range", conj [within "gps_lat_e7" (negLit 900000000) 900000000,
      within "gps_lon_e7" (negLit 1800000000) 1800000000, within "gps_alt" (-500) 6000,
      abs (v "gps_vn") ≤. 100, abs (v "gps_ve") ≤. 100, abs (v "gps_vd") ≤. 100]⟩,
  -- not a fix at latitude 0, longitude 0: see assumeInputsAsFirstStated
  ⟨"gps_not_null_island", ¬. v "gps_fresh" ∨. ¬. (v "gps_lat_e7" =. 0 ∧. v "gps_lon_e7" =. 0)⟩,
  ⟨"home_range", conj [within "cmd_estimator_set_home_lat_e7" (negLit 900000000) 900000000,
      within "cmd_estimator_set_home_lon_e7" (negLit 1800000000) 1800000000,
      within "cmd_estimator_set_home_alt_cm" (negLit 50000) 1000000]⟩]

/-- |est_q|^2 in binary32, as written. -/
def qnorm2 : Expr :=
  v "est_q1" * v "est_q1" + v "est_q2" * v "est_q2" + v "est_q3" * v "est_q3" +
    v "est_q4" * v "est_q4"

/-- The guarantee. -/
def guarantee : List Clause := [
  ⟨"no_internal_error", v "est_internal_errors" =. 0⟩,
  ⟨"outputs_finite", conj (floatOutputs.map fun n => finite (v n))⟩,
  -- before the boot has finished nothing is estimated: every estimate output is 0 (adapter.cpp)
  ⟨"zero_before_boot", v "est_booted" ∨. conj (estimateOutputs.map fun n => v n =. 0)⟩,
  -- the view's get_quat_body_to_ned builds the quaternion from the rotation matrix (Quaternion::
  -- from_rotation_matrix): EKF3's (from its normalized quaternion) once it estimates attitude,
  -- DCM's (renormalized every update, AP_AHRS_DCM::normalize) before
  ⟨"quat_unit", ¬. v "est_booted" ∨. abs (qnorm2 - 1) ≤. 1e-4⟩,
  ⟨"quat_unit_ekf", ¬. v "est_ekf_attitude" ∨. abs (qnorm2 - 1) ≤. 1e-5⟩,
  -- AP_AHRS::get_control_ground_speed_limit_ms() (AP_AHRS.h:322): the active backend's limit,
  -- 400 from EKF3 unless it relies on optical flow (AP_NavEKF3_Outputs.cpp:383-391; no flow
  -- sensor is in this stage), 50 from DCM (AP_AHRS_DCM.cpp:298); 0 before the boot
  ⟨"gnd_spd_limit_range", 0 ≤. v "est_gnd_spd_limit" ∧. v "est_gnd_spd_limit" ≤. 400⟩,
  ⟨"yaw_trig_unit", ¬. v "est_booted" ∨.
      abs (v "est_sin_yaw" * v "est_sin_yaw" + v "est_cos_yaw" * v "est_cos_yaw" - 1) ≤. 1e-5⟩,
  -- the view's get_gyro_latest() = rot_view (the identity for ROTATION_NONE) times AP_AHRS's,
  -- ins.get_gyro(primary) + get_gyro_drift(); with INS_GYRO_FILTER 0 the
  -- low-pass filter passes the sample through (DigitalBiquadFilter::apply, cutoff 0) and the
  -- harmonic notch is off (INS_HNTCH_ENABLE 0), so get_gyro() is the tick's newest sample minus
  -- the gyro offset (_rotate_and_correct_gyro; board orientation none): one binary32
  -- subtraction and one addition, exactly as written here
  ⟨"gyro_latest_unfiltered", ¬. (1 ≤. v "est_loop_ticks" ∧. v "ins_gyro_filter" =. 0) ∨.
      conj (["x", "y", "z"].map fun a =>
        v s!"gyro_{a}" =.
          (v s!"imu2_g{a}" - v s!"est_gyro_offset_{a}") + v s!"est_gyro_drift_{a}")⟩,
  -- what the rate controller assumes of its measurement (ardupilot/modules/rate_pid: |measurement| ≤ 1e4)
  ⟨"gyro_range", abs (v "gyro_x") ≤. 1e4 ∧. abs (v "gyro_y") ≤. 1e4 ∧. abs (v "gyro_z") ≤. 1e4⟩,
  -- 1 / EAS2TAS^2 with EAS2TAS = sqrt(rho_SSL / rho), rho clamped positive
  -- (AP_Baro::get_EAS2TAS_extended); 0 before the boot
  ⟨"air_density_positive", 0 ≤. v "air_density_ratio"⟩]

/-- The guarantee as first stated: `quat_unit` with 1e-5 for every booted step, and the mixer's
assumption 0 ≤ air_density_ratio ≤ 2. Both refuted by the module's campaigns (regime ticked):
* `quat_unit`, seed 3, case 13 step 979 (ardupilot/modules/estimator/evidence/tested/
  20261118T175136Z-seed3/counterexample-quat_unit.json): |q|^2 - 1 = -1.17e-5, before EKF3
  started, from DCM's matrix after random rates up to 35 rad/s; DCM renormalizes its matrix every
  update but leaves an error of this size. Now 1e-4 before EKF3 estimates attitude and 1e-5 after
  (`quat_unit_ekf`): a weaker clause before the EKF starts, stated as such.
* `air_density_range`, seed 2, case 7 step 781 (…20261118T175132Z-seed2/
  counterexample-air_density_range.json), ratios up to 193: the barometer's altitude AMSL is its
  altitude above the calibration plus the EKF origin's altitude (AP_Baro.cpp:1012); random fixes
  and pressures put it tens of km below sea level. Keeping it within the mixer's range needs the
  barometer and the GPS to agree over time, which a clause on one tick cannot state. The module
  now guarantees only `air_density_positive`; the bound is a guarantee of ardupilot/harnesses/est_loop,
  where the plant's sensors agree, and the mixer's assumption is to be discharged there. -/
def guaranteeAsFirstStated : List Clause :=
  (guarantee.filter fun c => c.name != "quat_unit_ekf" && c.name != "air_density_positive").map
    (fun c => if c.name == "quat_unit" then
        ⟨"quat_unit", ¬. v "est_booted" ∨. abs (qnorm2 - 1) ≤. 1e-5⟩
      else c) ++
  [⟨"air_density_range", 0 ≤. v "air_density_ratio" ∧. v "air_density_ratio" ≤. 2⟩]

/-- Ranges the code itself enforces on outputs the other stages assume bounds of (paths in the
ArduPilot checkout, read only). Each holds before the boot as well (every output 0).
* `euler_wrapped`: the view's roll, pitch and yaw are Matrix3::to_euler of its rotation
  (AP_AHRS_View.cpp:71; getters AP_AHRS_View.h:63-65): roll = atan2f(c.y, c.z), yaw =
  atan2f(b.x, a.x), within ±π (3.1415927 is binary32 π), pitch = -safe_asin(c.x), within ±π/2
  (safe_asin returns ±M_PI_2 as float for |x| ≥ 1 and 0 for NaN; AP_Math.cpp:50-63;
  matrix3.cpp:49-60).
* `trig_range`: AP_AHRS::calc_trig (AP_AHRS_Backend.cpp:93-135, called at AP_AHRS_View.cpp:80;
  getters AP_AHRS_View.h:68-84) constrains sin_yaw and cos_yaw to [-1, 1] (and sets 0 and 1 on
  a NaN or infinite yaw vector), cos_pitch to [0, 1], cos_roll to [-1, 1] or, in its fallback,
  cosf of a finite roll.
* `gain_scalers_range`: the active backend's control gain scalers (AP_AHRS.h:324-325): EKF3
  sets XY to 1, or gainHgt / MAX(height, gainHgt) ≤ 1 when it relies on optical flow, and Z to 1
  (AP_NavEKF3_Outputs.cpp:383-392, AP_AHRS_NavEKF3.cpp:237-238); DCM 0.5 and 0.25
  (AP_AHRS_DCM.cpp:299-300).
* `reset_counts_u16`: the four reset counters are uint16_t (AP_AHRS.h:361-376).
Not stated here, because the code does not bound them: the gyro beyond `gyro_range` (the sample
minus a learned offset plus the drift), the earth-frame acceleration (the filtered IMU sample,
rotated, no clamp), the air-density ratio beyond positive (`guaranteeAsFirstStated`: refuted,
ratios up to 193), and position and velocity (estimates of the vehicle's motion). -/
def guaranteeCodeRanges : List Clause := [
  ⟨"euler_wrapped", abs (v "est_roll") ≤. 3.1415927 ∧. abs (v "est_pitch") ≤. 1.5707964 ∧.
      abs (v "est_yaw") ≤. 3.1415927⟩,
  ⟨"trig_range", abs (v "est_sin_yaw") ≤. 1 ∧. abs (v "est_cos_yaw") ≤. 1 ∧.
      abs (v "est_cos_roll") ≤. 1 ∧. 0 ≤. v "est_cos_pitch" ∧. v "est_cos_pitch" ≤. 1⟩,
  ⟨"gain_scalers_range", 0 ≤. v "est_gain_scaler_xy" ∧. v "est_gain_scaler_xy" ≤. 1 ∧.
      0 ≤. v "est_gain_scaler_z" ∧. v "est_gain_scaler_z" ≤. 1⟩,
  ⟨"reset_counts_u16", v "est_pos_ne_reset_count" ≤. 65535 ∧. v "est_pos_d_reset_count" ≤. 65535 ∧.
      v "est_yaw_reset_count" ≤. 65535 ∧. v "est_attitude_reset_count" ≤. 65535⟩]

def contract : Contract where
  assume := assumeParams ++ assumeInputs
  guarantee := guarantee ++ guaranteeCodeRanges ++
    [⟨"text_range", v "est_text_len" ≤. 50 ∧. v "est_text_severity" ≤. 7⟩]

/-! ### Regimes and coverage -/

/-- ArduCopter's defaults for the record's parameters (AP_NavEKF3.cpp:23-45 Copter's EK3
defines and var_info lines 184-684; AP_AHRS.cpp: AHRS_EKF_TYPE 3, AHRS_TRIM 0;
AP_InertialSensor.cpp:65-66 INS_GYRO_FILTER and INS_ACCEL_FILTER 20, INS_GYR_CAL 1;
AP_Compass.cpp:115-140 COMPASS_DEC 0, COMPASS_USE 1, COMPASS_AUTODEC 1; AP_GPS_Params.cpp:81
GPS1_DELAY_MS 0; EK3_IMU_MASK 3 (HAL_EKF_IMU_MASK_DEFAULT)), with the X500's INS_ACCOFFS 0.001
(storage-x500.txt) and INS_GYROFFS 0 (the boot calibration sets it). -/
def stockParams : List Clause := [
  ⟨"stock_ek3_noise", conj [v "ek3_velne_m_nse" =. 0.3, v "ek3_veld_m_nse" =. 0.5,
      v "ek3_posne_m_nse" =. 0.5, v "ek3_alt_m_nse" =. 2, v "ek3_mag_m_nse" =. 0.05,
      v "ek3_gyro_p_nse" =. 0.015, v "ek3_acc_p_nse" =. 0.35, v "ek3_gbias_p_nse" =. 0.001,
      v "ek3_abias_p_nse" =. 0.02, v "ek3_mage_p_nse" =. 0.001, v "ek3_magb_p_nse" =. 0.0001,
      v "ek3_noaid_m_nse" =. 10, v "ek3_yaw_m_nse" =. 0.5]⟩,
  ⟨"stock_ek3_gates", conj [v "ek3_vel_i_gate" =. 500, v "ek3_pos_i_gate" =. 500,
      v "ek3_hgt_i_gate" =. 500, v "ek3_mag_i_gate" =. 300, v "ek3_yaw_i_gate" =. 300,
      v "ek3_glitch_rad" =. 25]⟩,
  ⟨"stock_ek3_other", conj [v "ek3_hgt_delay" =. 60, v "ek3_mag_cal" =. 3,
      v "ek3_gps_check" =. 31, v "ek3_check_scale" =. 100, v "ek3_tau_output" =. 25,
      v "ek3_acc_bias_lim" =. 1, v "ek3_mag_ef_lim" =. 50, v "ek3_err_thresh" =. 0.2,
      v "ek3_imu_mask" =. 3]⟩,
  ⟨"stock_ahrs", v "ahrs_ekf_type" =. 3 ∧. v "ahrs_trim_x" =. 0 ∧. v "ahrs_trim_y" =. 0⟩,
  ⟨"stock_ins", conj [v "ins_gyro_filter" =. 20, v "ins_accel_filter" =. 20,
      v "ins_gyr_cal" =. 1, v "ins_accoffs_x" =. 0.001, v "ins_accoffs_y" =. 0.001,
      v "ins_accoffs_z" =. 0.001, v "ins_gyroffs_x" =. 0, v "ins_gyroffs_y" =. 0,
      v "ins_gyroffs_z" =. 0]⟩,
  ⟨"stock_compass_gps", conj [v "compass_use" =. 1, v "compass_autodec" =. 1,
      v "compass_dec" =. 0, v "gps1_delay_ms" =. 0]⟩]

/-- The vehicle on the ground, disarmed, no commands: what the estimator sees before arming. -/
def groundClauses : List Clause := [
  ⟨"disarmed_on_ground", ¬. v "armed" ∧. ¬. v "likely_flying"⟩,
  ⟨"no_commands", conj (["cmd_estimator_set_takeoff_expected",
      "cmd_estimator_set_touchdown_expected", "cmd_estimator_set_home",
      "cmd_estimator_reset_height_datum", "cmd_estimator_request_yaw_reset",
      "cmd_estimator_set_terrain_hgt_stable"].map fun c =>
        ¬. v c)⟩]

/-- The clock as plant_sim's: t_us starts at 2500 and advances 2500 us per step. -/
def ticking : Hint := .increasing "t_us" 2500 2500 2500

/-- Every documented parameter value, random samples, the clock ticking at 400 Hz, the boot's
gyro calibration skipped (INS_GYR_CAL 0: with random samples it would not converge and would
keep the boot for its 30 s limit), commands at random. -/
def ticked : Regime where
  name := "ticked"
  doc := "the clock advancing 2500 us per step; INS_GYR_CAL 0 so that the boot ends in ~0.7 s"
  clauses := [⟨"no_gyro_cal", v "ins_gyr_cal" =. 0⟩]
  hints := [ticking]

/-- ArduCopter's defaults but INS_GYR_CAL 0 and the low-pass gyro filter off, random samples,
the vehicle disarmed, the clock ticking: the gyro relation's regime. -/
def stockUnfiltered : Regime where
  name := "stock_unfiltered"
  doc := "stock parameters with INS_GYR_CAL 0 and INS_GYRO_FILTER 0, disarmed, 400 Hz clock"
  clauses := (stockParams.map fun c => if c.name == "stock_ins" then
      ⟨"stock_ins_unfiltered", conj [v "ins_gyro_filter" =. 0, v "ins_accel_filter" =. 20,
        v "ins_gyr_cal" =. 0, v "ins_accoffs_x" =. 0.001, v "ins_accoffs_y" =. 0.001,
        v "ins_accoffs_z" =. 0.001]⟩ else c) ++ groundClauses
  hints := [ticking]

/-- Samples like the plant's at rest at the gorge site (sim/modules/plant_sim at PWM 1000: the X500
level on the ground at 4302 m, 38.84 N 105.04 W, the contact solver's jitter in the specific
force), each drawn at random within these ranges at every step or held for a case, with the
stock parameters, the vehicle disarmed, no commands, the clock at 400 Hz: the EKF can start. -/
def plantLike : Regime where
  name := "plant_like"
  doc := "stock parameters, samples near the plant's at rest, disarmed, 400 Hz clock"
  clauses := stockParams ++ groundClauses ++ [
    ⟨"rest_imu", conj ((List.range 3).flatMap fun s =>
      [within s!"imu{s}_ax" (-1.2) 1.2, within s!"imu{s}_ay" (-1.2) 1.2,
       within s!"imu{s}_az" (-10.5) (-9), abs (v s!"imu{s}_gx") ≤. 0.03,
       abs (v s!"imu{s}_gy") ≤. 0.03, abs (v s!"imu{s}_gz") ≤. 0.03])⟩,
    ⟨"site_baro", within "baro_pa" 59250 59300 ∧. within "baro_degc" (-13.5) (-12.5)⟩,
    ⟨"site_mag", within "mag_x" 200 225 ∧. within "mag_y" 5 35 ∧. within "mag_z" 455 490⟩,
    ⟨"site_gps", conj [within "gps_lat_e7" 388405506 388405606,
      within "gps_lon_e7" (negLit 1050441717) (negLit 1050441617), within "gps_alt" 4301 4303.5,
      abs (v "gps_vn") ≤. 0.1, abs (v "gps_ve") ≤. 0.1, abs (v "gps_vd") ≤. 0.1]⟩]
  hints := [ticking]

/-- What a campaign counts. -/
def coverage : List Clause := [
  ⟨"booted", v "est_booted"⟩,
  ⟨"looping", 1 ≤. v "est_loop_ticks"⟩,
  ⟨"ekf_started", v "est_ekf_started"⟩,
  ⟨"ekf_healthy", v "est_healthy"⟩,
  ⟨"gps_3d", v "est_gps_status" =. 3⟩,
  ⟨"using_gps", v "est_ekf_using_gps"⟩]

def module : Module where
  name := "estimator"
  doc := "ArduCopter's INS, baro, compass and GPS front ends, AP_AHRS (DCM, EKF3)"
  params := params
  input := input
  output := output
  contract := contract
  exe := "build/modules/estimator/estimator"
  stack := .ardupilot
  regimes := [ticked, stockUnfiltered, plantLike]
  coverage := coverage

end Ardupilot.Modules.Estimator
