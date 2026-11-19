import ArduLean.Runtime.CFloat
import ArduLean.Estimator.libraries.GCS_MAVLink.GCS_MAVLink
import ArduLean.Estimator.mavlink.mavlink
import ArduLean.Estimator.World
import ArduLean.Estimator.libraries.AP_GPS.AP_GPS

/-!
`World`: generated items without a C++ function of their own.

Items of `lean/Estimator_lib.lean` (the estimator translation), unchanged; placed by `tools/split_modules.py` (`ArduLean/Estimator/INDEX.md`).
-/

open FloatLib.Floats (Binary32 Binary64)

set_option maxRecDepth 200000
-- AP_DAL's `const log_RISH old_RISH = _RISH;` read only by WRITE_REPLAY_BLOCK_IFCHANGED, which is `(void)old`
-- without logging (HAL_LOGGING_ENABLED 0): an unused binding, as in the C++
set_option linter.unusedVariables false

namespace Estimator_lib

/-- What the translated classes write to objects outside the translation (--boundary, --boundary-call):
one constructor per boundary function or data member written, with its arguments (--output-log). -/
inductive Output where
  /-- `AP_Param::save(bool force_save) on the parameter object named by path` (first at `AP_Param/AP_ParamT.cpp:82`). -/
  | AP_Param_save (path : String) (force_save : Bool)
  /-- `AP_Param::notify() on the parameter object named by path` (first at `AP_Baro/AP_Baro.cpp:613`). -/
  | AP_Param_notify (path : String)
  /-- `gcs().send_text(MAV_SEVERITY severity, const char *fmt, ...)` (first at `AP_Baro/AP_Baro.cpp:306`). -/
  | send_text (severity : UInt32) (fmt : String) (args : Array (Sum UInt64 String))
  /-- `est_mark(uint8_t kind, uint32_t line)` (first at `reference/hal/est_scheduler.cpp:104`). -/
  | est_mark (kind : UInt8) (line : UInt32)
  /-- `hal.console->printf(const char *fmt, ...)` (first at `AP_Compass/AP_Compass.cpp:1407`). -/
  | console_printf (fmt : String) (args : Array (Sum UInt64 String))
  /-- `AP_Notify::flags.initialising = bool` (first at `AP_InertialSensor/AP_InertialSensor.cpp:1729`). -/
  | AP_Notify_flags_initialising (initialising : Bool)
  /-- `AP_Notify::flags.gyro_calibrated = bool` (first at `AP_InertialSensor/AP_InertialSensor.cpp:1856`). -/
  | AP_Notify_flags_gyro_calibrated (gyro_calibrated : Bool)
  /-- `the text written to a `char *` parameter's buffer, for a caller outside the translation` (first at `AP_GPS/GPS_Backend.cpp:129`). -/
  | text_sink (buf : UInt64) (text : CText)
  /-- `gcs().send_text(MAV_SEVERITY severity, const char *fmt, char *buffer) after hal.util->snprintf(buffer, size, ifmt, ...)` (first at `AP_GPS/GPS_Backend.cpp:153`). -/
  | send_text_snprintf (severity : UInt32) (fmt : String) (text : CText)
  /-- `hal.util.set_hw_rtc(uint64_t time_utc_usec)` (first at `AP_RTC/AP_RTC.cpp:95`). -/
  | set_hw_rtc (time_utc_usec : UInt64)
  /-- `AP_Notify::flags.gps_status = AP_GPS_FixType` (first at `AP_GPS/AP_GPS.cpp:1089`). -/
  | AP_Notify_flags_gps_status (gps_status : AP_GPS_FixType)
  /-- `AP_Notify::flags.gps_num_sats = uint8_t` (first at `AP_GPS/AP_GPS.cpp:1090`). -/
  | AP_Notify_flags_gps_num_sats (gps_num_sats : UInt8)
  /-- `hal.util.persistent_data.roll_rad = float` (first at `AP_AHRS/AP_AHRS_DCM.cpp:315`). -/
  | hal_util_persistent_data_roll_rad (roll_rad : Binary32)
  /-- `hal.util.persistent_data.pitch_rad = float` (first at `AP_AHRS/AP_AHRS_DCM.cpp:316`). -/
  | hal_util_persistent_data_pitch_rad (pitch_rad : Binary32)
  /-- `hal.util.persistent_data.yaw_rad = float` (first at `AP_AHRS/AP_AHRS_DCM.cpp:317`). -/
  | hal_util_persistent_data_yaw_rad (yaw_rad : Binary32)
  /-- `AP_Notify::flags.gps_fusion = bool` (first at `AP_AHRS/AP_AHRS.cpp:671`). -/
  | AP_Notify_flags_gps_fusion (gps_fusion : Bool)
  /-- `AP_Notify::flags.gps_glitching = bool` (first at `AP_AHRS/AP_AHRS.cpp:672`). -/
  | AP_Notify_flags_gps_glitching (gps_glitching : Bool)
  /-- `AP_Notify::flags.have_pos_abs = bool` (first at `AP_AHRS/AP_AHRS.cpp:673`). -/
  | AP_Notify_flags_have_pos_abs (have_pos_abs : Bool)
  /-- `boundary.send_message(ap_message id)` (first at `AP_AHRS/AP_AHRS.cpp:479`). -/
  | send_message (id : ap_message)
  /-- `hal.opticalflow.push_gyro_bias(float gyro_bias_x, float gyro_bias_y)` (first at `AP_AHRS/AP_AHRS.cpp:647`). -/
  | push_gyro_bias (gyro_bias_x : Binary32) (gyro_bias_y : Binary32)
  /-- `hal.util.persistent_data.home_lat = int32_t` (first at `AP_AHRS/AP_AHRS.cpp:1781`). -/
  | hal_util_persistent_data_home_lat (home_lat : Int32)
  /-- `hal.util.persistent_data.home_lon = int32_t` (first at `AP_AHRS/AP_AHRS.cpp:1782`). -/
  | hal_util_persistent_data_home_lon (home_lon : Int32)
  /-- `hal.util.persistent_data.home_alt_cm = int32_t` (first at `AP_AHRS/AP_AHRS.cpp:1783`). -/
  | hal_util_persistent_data_home_alt_cm (home_alt_cm : Int32)
  /-- `AP::mission().write_home_to_storage()` (first at `AP_AHRS/AP_AHRS.cpp:1787`). -/
  | write_home_to_storage
  /-- `mavlink_msg_ekf_status_report_send_struct(mavlink_channel_t chan, __mavlink_ekf_status_report_t ekf_status_report)` (first at `AP_AHRS/AP_AHRS.cpp:1709`). -/
  | mavlink_msg_ekf_status_report_send_struct (chan : mavlink_channel_t) (ekf_status_report : __mavlink_ekf_status_report_t)
  /-- `mavlink_msg_gps_raw_int_send(mavlink_channel_t chan, uint64_t time_usec, uint8_t fix_type, int32_t lat, int32_t lon, int32_t alt, uint16_t eph, uint16_t epv, uint16_t vel, uint16_t cog, uint8_t satellites_visible, int32_t alt_ellipsoid, uint32_t h_acc, uint32_t v_acc, uint32_t vel_acc, uint32_t hdg_acc, uint16_t yaw)` (first at `AP_GPS/AP_GPS.cpp:1405`). -/
  | mavlink_msg_gps_raw_int_send (chan : mavlink_channel_t) (time_usec : UInt64) (fix_type : UInt8) (lat : Int32) (lon : Int32) (alt : Int32) (eph : UInt16) (epv : UInt16) (vel : UInt16) (cog : UInt16) (satellites_visible : UInt8) (alt_ellipsoid : Int32) (h_acc : UInt32) (v_acc : UInt32) (vel_acc : UInt32) (hdg_acc : UInt32) (yaw : UInt16)
  /-- `mavlink_msg_gps2_raw_send(mavlink_channel_t chan, uint64_t time_usec, uint8_t fix_type, int32_t lat, int32_t lon, int32_t alt, uint16_t eph, uint16_t epv, uint16_t vel, uint16_t cog, uint8_t satellites_visible, uint8_t dgps_numch, uint32_t dgps_age, uint16_t yaw, int32_t alt_ellipsoid, uint32_t h_acc, uint32_t v_acc, uint32_t vel_acc, uint32_t hdg_acc)` (first at `AP_GPS/AP_GPS.cpp:1446`). -/
  | mavlink_msg_gps2_raw_send (chan : mavlink_channel_t) (time_usec : UInt64) (fix_type : UInt8) (lat : Int32) (lon : Int32) (alt : Int32) (eph : UInt16) (epv : UInt16) (vel : UInt16) (cog : UInt16) (satellites_visible : UInt8) (dgps_numch : UInt8) (dgps_age : UInt32) (yaw : UInt16) (alt_ellipsoid : Int32) (h_acc : UInt32) (v_acc : UInt32) (vel_acc : UInt32) (hdg_acc : UInt32)

/-- The boundary calls of a member function, in the order the C++ makes them. -/
abbrev Outputs := Array Output

end Estimator_lib
