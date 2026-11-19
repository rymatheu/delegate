import Harness.Module
import ardupilot.modules.supervisor.gen.Commands

/-! # supervisor: ArduCopter's vehicle code (scoping build)

ArduCopter/*.cpp and the libraries that serve it (GCS_MAVLink, AP_Mission, AP_Arming,
RC_Channel, AP_Scheduler, AP_Param, StorageManager, AP_Vehicle, AP_Notify, AP_BattMonitor,
SRV_Channel), compiled unmodified for the SITL board with the feature switches of
ardupilot/modules/supervisor/probe/features.txt, stepped by `Copter::loop()` (AP_Scheduler with Copter's
task table at 400 Hz). The objects of the other stages that the vehicle code holds are shadows
(ardupilot/modules/supervisor/DESIGN.md): real headers, stand-in out-of-line methods, state written from
this record. Built by ardupilot/modules/supervisor/build.sh.

This is the scoping build: the ports cover booting, one tick at rest, the ground-station byte
stream and the arming and spool signals. The command fields (`cmd_<stage>_<method>…`) are
reported by the stand-ins' call log (`cmd_log_*`), not yet split into fields. -/

namespace Ardupilot.Modules.Supervisor

open Harness Harness.Contract.Lang

private def f (n d : String) : Field := { name := n, type := .f32, doc := d }
private def u (n d : String) : Field := { name := n, type := .u32, doc := d }
private def i (n d : String) : Field := { name := n, type := .i32, doc := d }
private def b (n d : String) : Field := { name := n, type := .bool, doc := d }

/-- Number of u32 words of the ground-station byte stream per tick, each direction. -/
def gcsWords : Nat := 64

private def pad2 (k : Nat) : String := if k < 10 then s!"0{k}" else s!"{k}"

private def words (pre : String) (dir : String) : List Field :=
  (List.range gcsWords).map fun k =>
    u s!"{pre}_w{pad2 k}" s!"{dir} bytes {4*k}..{4*k+3} of the tick, little-endian"

def params : Schema := #[
  u "mav_sysid" "MAV_SYSID (was SYSID_THISMAV): MAVLink system id",
  u "fltmode1" "FLTMODE1 (Copter::g.flight_mode1): mode number for switch position 1",
  u "initial_mode" "INITIAL_MODE (g.initial_mode): mode at boot (0 STABILIZE)",
  i "arming_skipchk" "ARMING_SKIPCHK (AP_Arming::checks_to_skip): checks skipped; -1 all optional",
  u "fs_thr_enable" "FS_THR_ENABLE (g.failsafe_throttle): 0 disabled",
  u "fs_gcs_enable" "FS_GCS_ENABLE (g.failsafe_gcs): 0 disabled",
  u "gps1_type" "GPS1_TYPE (estimator's AP_GPS::Params; 1 AUTO): GPS_RAW_INT is sent only if not 0",
  u "auto_options" "AUTO_OPTIONS (ModeAuto options); 2 = AllowTakeOffWithoutRaisingThrottle",
  u "rc_options" "RC_OPTIONS (RC_Channels::_options); default 32 = ARMING_CHECK_THROTTLE",
  u "wp_yaw_behavior" "WP_YAW_BEHAVIOR (g.wp_yaw_behavior): 0 never change yaw (a mission's CONDITION_YAW holds), \
    2 face the next waypoint except in RTL (ArduCopter's default)"]

/-- Three f32 fields `pre_x/y/z` (or with the given suffixes). -/
private def f3 (pre doc : String) (sfx : List String := ["x", "y", "z"]) : List Field :=
  sfx.map fun c => f s!"{pre}_{c}" s!"{doc}, {c}"

/-- The estimator's outputs this tick (ardupilot/modules/estimator of the estimator copy). -/
def estimatorIn : List Field :=
  [f "est_q1" "AP_AHRS::get_quaternion, body to NED, scalar", f "est_q2" "quaternion x",
   f "est_q3" "quaternion y", f "est_q4" "quaternion z",
   b "est_pos_ok" "position estimate valid (position_NE_valid and position_D_valid)"] ++
  f3 "est_pos" "position from the EKF origin, m" ["n", "e", "d"] ++
  [b "est_vel_ok" "AP_AHRS::get_velocity_NED returned true"] ++
  f3 "est_vel" "velocity NED, m/s" ["n", "e", "d"] ++
  [b "est_pos_rate_d_ok" "get_vert_pos_rate_D returned true",
   f "est_pos_rate_d" "AP_AHRS::get_vert_pos_rate_D, m/s",
   f "gyro_x" "AP_AHRS::get_gyro().x, rad/s", f "gyro_y" "get_gyro().y",
   f "gyro_z" "get_gyro().z"] ++
  f3 "est_accel_ef" "AP_AHRS::get_accel_ef(), m/s/s" ++
  f3 "est_gyro_drift" "AP_AHRS::get_gyro_drift(), rad/s" ++
  f3 "est_accel" "AP_InertialSensor::get_accel(), body, m/s/s" ++
  f3 "est_gyro" "AP_InertialSensor::get_gyro(), body, rad/s" ++
  [b "est_origin_ok" "AP_AHRS::get_origin returned true",
   i "est_origin_lat_e7" "EKF origin latitude, 1e-7 deg", i "est_origin_lon_e7" "longitude",
   i "est_origin_alt_cm" "EKF origin altitude AMSL, cm",
   b "est_healthy" "AP_AHRS::healthy()", b "est_initialised" "AP_AHRS::initialised()",
   u "est_filter_status" "nav_filter_status bits of the configured EKF (AP_Nav_Common.h)",
   b "est_variances_ok" "get_variances_for_configured_backend returned true",
   f "est_vel_variance" "velVar", f "est_pos_variance" "posVar", f "est_hgt_variance" "hgtVar"] ++
  f3 "est_mag_variance" "magVar" ++
  [u "est_pos_ne_reset_count" "EKF NE position reset count",
   u "est_pos_d_reset_count" "EKF D position reset count",
   u "est_yaw_reset_count" "EKF yaw reset count",
   f "est_baro_alt" "AP_Baro::get_altitude(), m above the calibration altitude",
   u "est_gps_status" "AP_GPS::status() (AP_GPS_FixType)",
   u "est_gps_num_sats" "AP_GPS::num_sats()",
   b "est_prearm_ok" "AP_AHRS::pre_arm_check verdict of the estimator",
   b "est_ins_accel_healthy" "AP_InertialSensor::get_accel_health_all()",
   b "est_ins_gyro_healthy" "AP_InertialSensor::get_gyro_health_all()",
   b "est_baro_healthy" "AP_Baro::all_healthy()", b "est_gps_healthy" "AP_GPS::is_healthy(0)",
   u "est_gps_hdop" "AP_GPS::get_hdop()", u "est_gps_vdop" "AP_GPS::get_vdop()"] ++
  f3 "est_vibe" "AP_InertialSensor::get_vibration_levels(0), m/s/s" ++
  [u "est_accel_clip_count" "AP_InertialSensor::get_accel_clip_count(0)",
   b "est_innov_ok" "AP_AHRS::get_innovations returned true"] ++
  f3 "est_innov_vel" "velocity innovations, m/s" ["n", "e", "d"] ++
  f3 "est_innov_pos" "position innovations, m" ["n", "e", "d"] ++
  [u "est_text_seq" "the estimator's status texts so far", u "est_text_severity" "this tick's text's MAV_SEVERITY",
   u "est_text_len" "this tick's text, characters (0: none)"] ++
  (List.range 13).map fun k =>
    u s!"est_text_w{if k < 10 then "0" else ""}{k}" s!"the estimator's status text, bytes {4*k}..{4*k+3}"

/-- The simulator's raw sensor samples of the tick (sim/modules/plant_sim), for the telemetry the
ground station shows (GPS_RAW_INT, SCALED_PRESSURE, the compass): held from the last fresh one. -/
def plantIn : List Field :=
  [b "gps_fresh" "plant_sim: a GPS sample this tick",
   i "gps_lat_e7" "GPS latitude, 1e-7 deg", i "gps_lon_e7" "GPS longitude, 1e-7 deg",
   f "gps_alt" "GPS altitude AMSL, m", f "gps_vn" "GPS velocity north, m/s",
   f "gps_ve" "east, m/s", f "gps_vd" "down, m/s",
   b "baro_fresh" "plant_sim: a barometer sample this tick",
   f "baro_pa" "static pressure, Pa", f "baro_degc" "temperature, degC",
   b "mag_fresh" "plant_sim: a compass sample this tick",
   f "mag_x" "body field x, mGauss", f "mag_y" "y", f "mag_z" "z"]

/-- The position stage's outputs, previous tick (ardupilot/modules/position of the integration copy). -/
def positionIn : List Field :=
  [b "pc_ne_active" "NE_is_active() as this tick reads it before any call",
   b "pc_d_active" "D_is_active() as this tick reads it before any call"] ++
  f3 "thrust_vec" "AC_PosControl::get_thrust_vector()" ++
  f3 "pc_pos_desired" "get_pos_desired_NED_m(), m" ["n", "e", "d"] ++
  f3 "pc_pos_target" "_pos_target_ned_m, m" ["n", "e", "d"] ++
  f3 "pc_vel_desired" "get_vel_desired_NED_ms(), m/s" ["n", "e", "d"] ++
  f3 "pc_pos_offset" "get_pos_offset_NED_m(), m" ["n", "e", "d"] ++
  f3 "pc_pos_error" "get_pos_error_NED_m(), m" ["n", "e", "d"] ++
  f3 "pc_stopping_point" "get_stopping_point_NE/D_m(), m" ["n", "e", "d"] ++
  [f "pc_vel_terrain_d" "get_vel_terrain_D_ms()", f "pc_yaw" "get_yaw_rad()",
   f "pc_yaw_rate" "get_yaw_rate_rads()", f "pc_ne_max_speed" "NE_get_max_speed_ms()",
   f "pc_max_speed_up" "get_max_speed_up_ms()", f "pc_max_speed_down" "get_max_speed_down_ms()",
   f "pc_ne_max_accel" "NE_get_max_accel_mss()", f "pc_d_max_accel" "D_get_max_accel_mss()",
   f "pc_vel_d_control_ratio" "get_vel_D_control_ratio()",
   f "pc_lean_angle_max" "get_lean_angle_max_rad()"]

/-- The attitude stage's outputs, previous tick. -/
def attitudeIn : List Field :=
  [f "ac_att_target_q1" "get_attitude_target_quat().q1", f "ac_att_target_q2" "q2",
   f "ac_att_target_q3" "q3", f "ac_att_target_q4" "q4"] ++
  f3 "ac_att_target" "get_att_target_euler_rad(), rad" ["roll", "pitch", "yaw"] ++
  f3 "ac_ang_vel_target" "get_attitude_target_ang_vel(), rad/s" ++
  f3 "ac_rate_ef_target" "get_rate_ef_target_rads(), rad/s" ++
  [f "ac_thrust_error_angle" "_thrust_error_angle_rad (get_att_error_angle_deg in rad)",
   f "ac_althold_lean_angle_max" "get_althold_lean_angle_max_rad(), rad",
   f "ac_throttle_in" "get_throttle_in()", f "ac_throttle_mix" "get_throttle_mix()"]

/-- The guidance stage's outputs, previous tick. -/
def guidanceIn : List Field :=
  [b "wp_reached" "AC_WPNav::reached_wp_destination()",
   f "wp_distance" "get_wp_distance_to_destination_m(), m",
   f "wp_bearing" "get_wp_bearing_to_destination_rad(), rad",
   b "wp_active" "AC_WPNav::is_active()", b "wp_paused" "AC_WPNav::paused()",
   b "wp_update_ok" "update_wpnav()'s result", b "wp_fast" "_flags.fast_waypoint"] ++
  f3 "wp_origin" "get_wp_origin_NED_m(), m" ["n", "e", "d"] ++
  f3 "wp_destination" "get_wp_destination_NED_m(), m" ["n", "e", "d"]

/-- The loiter stage's outputs, previous tick (added with that stage). -/
def loiterIn : List Field :=
  [f "lt_angle_max" "AC_Loiter::get_angle_max_rad() (the loiter stage's, from its LOIT_ANG_MAX, \
    ATC_ANGLE_MAX and the position stage's lean limit), rad"]

/-- The mixer's outputs, same tick. -/
def mixerIn : List Field :=
  [u "spool_state" "AP_Motors::get_spool_state()",
   b "spoolup_block" "AP_Motors::get_spoolup_block()",
   b "limit_roll" "AP_Motors::limit.roll", b "limit_pitch" "limit.pitch",
   b "limit_yaw" "limit.yaw", b "limit_throttle_lower" "limit.throttle_lower",
   b "limit_throttle_upper" "limit.throttle_upper",
   f "throttle_filtered" "AP_Motors::get_throttle()",
   f "throttle_out" "AP_Motors::get_throttle_out()",
   f "throttle_hover" "AP_MotorsMulticopter::get_throttle_hover() (MOT_THST_HOVER, mixer-learned)",
   b "thrust_boost" "AP_Motors::get_thrust_boost() (the mixer's state)"]

def input : Schema := (
  [f "dt" "loop period, s", u "now_ms" "AP_HAL::millis()",
   u "now_us" "AP_HAL::micros(); micros64 is now_us widened (wraps at 71 min)"] ++
  estimatorIn ++ plantIn ++ positionIn ++ attitudeIn ++ guidanceIn ++ loiterIn ++ mixerIn ++
  [u "rc_1" "RC input channel 1 PWM, us (roll), 0 = no signal",
   u "rc_2" "channel 2 (pitch)", u "rc_3" "channel 3 (throttle)", u "rc_4" "channel 4 (yaw)",
   u "rc_5" "channel 5 (flight mode switch)", u "rc_6" "channel 6", u "rc_7" "channel 7",
   u "rc_8" "channel 8",
   b "rc_fresh" "a new RC frame this tick (AP_HAL::RCInput::new_input)",
   u "gcs_rx_len" "bytes from the ground station this tick (0..256)"] ++
  words "gcs_rx" "ground-station").toArray

def output : Schema := #[
  b "armed" "AP_Motors::armed() as the arming library set it",
  b "interlock" "AP_Motors::get_interlock() as Copter::motors_output set it",
  u "spool_desired" "AP_Motors::get_desired_spool_state(): 0 shut down, 1 ground idle, 2 unlimited",
  b "clear_spoolup_block" "the vehicle code cleared the spool-up block this tick",
  u "mode" "Copter::flightmode->mode_number()",
  b "land_complete" "Copter::ap.land_complete",
  u "cmd_log_count" "stand-in command calls this tick (all stages)",
  u "cmd_log_hash" "FNV-1a hash of this tick's command log (method ids and argument bits)",
  u "sup_cmd_conflicts" "same method called twice with different arguments in one tick",
  u "gcs_rx_dropped" "ground-station bytes dropped because the receive ring was full",
  u "gcs_tx_len" "bytes to the ground station this tick (0..256)"] ++
  (words "gcs_tx" "ground-station-bound").toArray ++
  Ardupilot.Modules.Supervisor.Commands.fields.toArray ++ #[
  u "cmd_unmapped" "command calls this tick that commands.txt does not map to a field",
  b "cmd_attitude_set_throttle_out_before_input"
    "set_throttle_out was called before the tick's first input_* call (takeoff.cpp)",
  b "cmd_attitude_pos_throttle_after_input"
    "D_update_controller (whose set_throttle_out the position stage makes) came after input_*",
  b "likely_flying" "AP_Vehicle::get_likely_flying() (Copter::set_land_complete): to the estimator",
  u "poisoned_reads"
    "SUP_POISON=1: f32 outputs that carried a NaN from unfilled shadow state, since init",
  u "param_set_refused" "PARAM_SETs of another stage's parameter refused since init",
  u "sup_internal_errors" "AP_InternalError count since init (supervisor process)",
  u "sup_internal_error_bits" "AP_InternalError::errors(): the error_t bits raised since init",
  u "sup_internal_error_line" "AP_InternalError::last_error_line()",
  u "unanswered" "queries answered by a type's zero in discovery mode (SUP_LENIENT=1) since init"]

/-- Mode numbers whose code paths the stand-ins cover (Mode::Number): STABILIZE 0, ALT_HOLD 2,
AUTO 3, GUIDED 4, LOITER 5, RTL 6, LAND 9. -/
def coveredMode (n : String) : Expr :=
  n =. 0 ∨. n =. 2 ∨. n =. 3 ∨. n =. 4 ∨. n =. 5 ∨. n =. 6 ∨. n =. 9

/-- The estimator's health and validity flags all set, and a 3D GPS fix. -/
def estimatorGood : List Clause := [
  ⟨"est_flags_good", "est_healthy" =. tt ∧. "est_initialised" =. tt ∧. "est_pos_ok" =. tt ∧.
    "est_vel_ok" =. tt ∧. "est_pos_rate_d_ok" =. tt ∧. "est_origin_ok" =. tt ∧.
    "est_variances_ok" =. tt ∧. "est_filter_status" =. 0x1A33F ∧. "est_gps_status" =. 3⟩]

/-- `e₁ ∧ … ∧ eₙ`. -/
private def allOf : List Expr → Expr
  | [] => tt
  | [e] => e
  | e :: es => e ∧. allOf es

/-- Every f32 input finite: the other stages' signals are finite numbers. -/
def inputsFinite : Clause :=
  ⟨"inputs_finite",
    allOf ((input.toList.filter (·.type == .f32)).map fun x => finite (.var x.name))⟩

/-- Every f32 input of magnitude at most 1e4 (the other stages' signals are physical values:
positions within 10 km, rates, throttles; the first campaigns with unbounded values made
ArduPilot's own arithmetic overflow to NaN and raise constraining_nan, AP_Math.cpp:290). -/
def inputsBounded : Clause :=
  ⟨"inputs_bounded",
    allOf ((input.toList.filter fun x => x.type == .f32 && x.name != "baro_pa").map
      fun x => abs (.var x.name) ≤. 10000) ∧. "baro_pa" ≤. 120000 ∧. 0 ≤. "baro_pa"⟩

private def unitQuat (p : String) : Expr :=
  let c (k : Nat) : Expr := .var s!"{p}{k}"
  abs (c 1 * c 1 + c 2 * c 2 + c 3 * c 3 + c 4 * c 4 - 1) ≤. 0.001

/-- Added after the campaigns `noisy_link` seeds 1, 3 and 4 refuted `no_cmd_conflict` (seed 1:
case 7, step 1; seed 3: case 6, step 2; seed 4: case 6, step 1), all with INITIAL_MODE = 9: LAND
entered at boot, before the first step, sees no position (the estimate is not filled yet, as an
EKF is not ready at boot) and keeps ModeLand::nogps_run, which on the ground calls
make_safe_ground_handling (input_euler_angle_roll_pitch_euler_rate_yaw_rad(0, 0, 0),
mode.cpp:689) and then input_euler_angle_roll_pitch_euler_rate_yaw_rad(pilot roll, pitch, yaw
rate) (mode_land.cpp:192): one method twice in a tick with different arguments, which one
`cmd_attitude_…` record cannot carry (the second call shapes from the target the first left).
A first correction (GPS1_TYPE = 1) did not remove it (seeds 1, 3, 4 again). The guarantee stands
as stated; the assumption excludes LAND as the boot mode (LAND without position needs the
per-stage ordered queue, DESIGN.md 2). -/
def bootNotLand : Clause := ⟨"boot_not_land", ¬. ("initial_mode" =. 9)⟩

def gpsConfigured : Clause := ⟨"gps_configured", "gps1_type" =. 1⟩

/-- First statement of the spool guarantee: refuted by the full-stack AUTO flight
(`dev/fly.py auto`, step 10996): the crash check (Copter::crash_check, a fast task after
update_flight_mode) disarms in the tick after the mode asked THROTTLE_UNLIMITED, so at the end
of that tick armed is false while the stored desired state is still THROTTLE_UNLIMITED (the
mixer shuts the motors down itself, since it reads `armed`). Replaced by no_interlock_shut_down,
weaker: it no longer says anything about `armed`. -/
def disarmedShutDownAsFirstStated : Clause :=
  ⟨"disarmed_shut_down", ("armed" =. tt ∧. "interlock" =. tt) ∨. "spool_desired" =. 0⟩

def contract : Contract where
  assume := [
    inputsFinite, inputsBounded,
    -- the estimate's quaternion is a unit one once the estimator is healthy; before (boot,
    -- EKF not initialised) the estimator stage reports zeros (ap_full_ekf, step 1)
    ⟨"quaternions_unit",
      (¬. ("est_healthy" =. tt) ∨. unitQuat "est_q") ∧. unitQuat "ac_att_target_q"⟩,
    ⟨"modes_covered", coveredMode "fltmode1" ∧. coveredMode "initial_mode"⟩,
    ⟨"sysid_range", 1 ≤. "mav_sysid" ∧. "mav_sysid" ≤. 255⟩,
    ⟨"failsafe_options", "fs_thr_enable" ≤. 7 ∧. "fs_gcs_enable" ≤. 7⟩,
    ⟨"options_range", "auto_options" ≤. 15 ∧. "gps1_type" ≤. 1⟩,
    gpsConfigured, bootNotLand,
    ⟨"dt_range", 0 <. "dt" ∧. "dt" ≤. 0.01⟩,
    ⟨"gcs_rx_len_range", "gcs_rx_len" ≤. 256⟩,
    ⟨"est_text_range", "est_text_len" ≤. 50 ∧. "est_text_severity" ≤. 7⟩,
    ⟨"spool_state_range", "spool_state" ≤. 4⟩,
    ⟨"estimate_finite", finite "est_q1" ∧. finite "est_q2" ∧. finite "est_q3" ∧.
      finite "est_q4" ∧. finite "est_pos_n" ∧. finite "est_pos_e" ∧. finite "est_pos_d" ∧.
      finite "est_vel_n" ∧. finite "est_vel_e" ∧. finite "est_vel_d"⟩,
    ⟨"estimate_bounded", abs "est_pos_n" ≤. 10000 ∧. abs "est_pos_e" ≤. 10000 ∧.
      abs "est_pos_d" ≤. 10000 ∧. abs "est_vel_n" ≤. 100 ∧. abs "est_vel_e" ≤. 100 ∧.
      abs "est_vel_d" ≤. 100⟩]
  guarantee := [
    ⟨"spool_desired_range", "spool_desired" ≤. 2⟩,
    -- AP_MotorsMulticopter::set_desired_spool_state (AP_MotorsMulticopter.cpp:570-581) stores
    -- SHUT_DOWN unless armed and interlock; the interlock changes only in Copter::motors_output
    -- (motors.cpp:94-99), which runs before the mode in the tick, so after the mode's call
    -- interlock false implies SHUT_DOWN (disarmedShutDownAsFirstStated: refuted)
    ⟨"no_interlock_shut_down", "interlock" =. tt ∨. "spool_desired" =. 0⟩,
    ⟨"gcs_tx_len_range", "gcs_tx_len" ≤. 256⟩,
    ⟨"no_cmd_conflict", "sup_cmd_conflicts" =. 0⟩,
    ⟨"no_internal_error", "sup_internal_errors" =. 0⟩,
    ⟨"every_query_answered", "unanswered" =. 0⟩,
    -- the vehicle code's only call of update_throttle_hover passes the constant 0.01
    -- (ArduCopter/Attitude.cpp:62; the stand-in logs its argument, gen/out/
    -- shadow_AP_MotorsMulticopter.cpp:292-297)
    ⟨"hover_dt_constant", ¬. "cmd_mixer_update_throttle_hover" ∨.
      "cmd_mixer_update_throttle_hover_dt" =. 0.01⟩,
    -- HeadingMode is an enum class of three values (AC_AttitudeControl.h:711-715), logged as
    -- uint32_t(heading.heading_mode) (stand_ins/stubs_attitude.cpp:122); 0 when not called
    ⟨"heading_mode_enum", "cmd_attitude_input_thrust_vector_heading_heading_mode" ≤. 2⟩,
    -- the only call of set_throttle_mix_max passes pos_control->get_vel_D_control_ratio()
    -- (ArduCopter/land_detector.cpp:318), the real header's inline constrain_float(…, 0, 1)
    -- (AC_PosControl.h:595); 0 when not called
    ⟨"mix_max_ratio_range", 0 ≤. "cmd_attitude_set_throttle_mix_max_ratio" ∧.
      "cmd_attitude_set_throttle_mix_max_ratio" ≤. 1⟩]

/-- At rest on the ground, no pilot, no ground station: what the vehicle sees before arming. -/
def rest : Regime where
  name := "rest"
  doc := "estimate at rest and good, mixer shut down, no RC, no ground-station bytes, 400 Hz"
  clauses := estimatorGood ++ [
    ⟨"at_rest", "est_q1" =. 1 ∧. "est_q2" =. 0 ∧. "est_q3" =. 0 ∧. "est_q4" =. 0 ∧.
      "est_pos_n" =. 0 ∧. "est_pos_e" =. 0 ∧. "est_pos_d" =. 0 ∧. "est_vel_n" =. 0 ∧.
      "est_vel_e" =. 0 ∧. "est_vel_d" =. 0 ∧. "spool_state" =. 0 ∧. "gcs_rx_len" =. 0 ∧.
      "rc_1" =. 0 ∧. "rc_fresh" =. ff ∧. "ac_att_target_q1" =. 1 ∧.
      "ac_att_target_q2" =. 0 ∧. "ac_att_target_q3" =. 0 ∧. "ac_att_target_q4" =. 0⟩,
    ⟨"loop_dt", 0.0024 ≤. "dt" ∧. "dt" ≤. 0.0026⟩,
    ⟨"stock_supervisor", "mav_sysid" =. 1 ∧. "arming_skipchk" =. -1 ∧. "gps1_type" =. 1⟩]
  hints := [.increasing "now_ms" 1000 2 3, .increasing "now_us" 1000000 2400 2600]

/-- Flight-like signals with random ground-station bytes: the estimate good and bounded, any
mode, any MAVLink byte stream (mostly unframed noise, so the parser's resynchronization and the
message handlers' bounds are what is exercised). -/
def noisyLink : Regime where
  name := "noisy_link"
  doc := "good level estimate, random bytes from the ground station, random RC, 400 Hz"
  clauses := estimatorGood ++ [
    ⟨"loop_dt", 0.0024 ≤. "dt" ∧. "dt" ≤. 0.0026⟩,
    ⟨"level", "est_q1" =. 1 ∧. "est_q2" =. 0 ∧. "est_q3" =. 0 ∧. "est_q4" =. 0 ∧.
      "ac_att_target_q1" =. 1 ∧. "ac_att_target_q2" =. 0 ∧. "ac_att_target_q3" =. 0 ∧.
      "ac_att_target_q4" =. 0⟩,
    ⟨"near", abs "est_pos_n" ≤. 50 ∧. abs "est_pos_e" ≤. 50 ∧.
      abs "est_pos_d" ≤. 50 ∧.
      abs "est_vel_n" ≤. 5 ∧. abs "est_vel_e" ≤. 5 ∧. abs "est_vel_d" ≤. 5⟩]
  hints := [.increasing "now_ms" 1000 2 3, .increasing "now_us" 1000000 2400 2600]

def module : Module where
  name := "supervisor"
  doc := "ArduCopter's vehicle code (modes, arming, failsafes, mission, RC, MAVLink)"
  params := params
  input := input
  output := output
  contract := contract
  exe := "build/modules/supervisor/supervisor"
  stack := .ardupilot
  regimes := [rest, noisyLink]

end Ardupilot.Modules.Supervisor
