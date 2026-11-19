import ArduLean.Musl.atan2f
import ArduLean.Estimator.libraries.AP_Math.AP_Math
import ArduLean.Estimator.World
import ArduLean.Estimator.libraries.AP_Common.AP_Common
import ArduLean.Estimator.libraries.AP_Param.AP_Param
import ArduLean.Estimator.libraries.AP_RTC.AP_RTC

/-!
ArduPilot `libraries/AP_GPS`, part 1 of 2. Sources: `libraries/AP_GPS/AP_GPS.h`, `libraries/AP_GPS/GPS_Backend.h`, `libraries/AP_GPS/AP_GPS_FixType.h`, `libraries/AP_GPS/AP_GPS_SITL.h`, `libraries/AP_GPS/AP_GPS.cpp`, `libraries/AP_GPS/GPS_Backend.cpp`.

Items of `lean/Estimator_lib.lean` (the estimator translation), unchanged; placed by `tools/split_modules.py` (`ArduLean/Estimator/INDEX.md`).
-/

open FloatLib.Floats (Binary32 Binary64)

set_option maxRecDepth 200000
-- AP_DAL's `const log_RISH old_RISH = _RISH;` read only by WRITE_REPLAY_BLOCK_IFCHANGED, which is `(void)old`
-- without logging (HAL_LOGGING_ENABLED 0): an unused binding, as in the C++
set_option linter.unusedVariables false

namespace Estimator_lib

/-- C++ `enum class AP_GPS_FixType`, `AP_GPS/AP_GPS_FixType.h:9-19`. -/
inductive AP_GPS_FixType where
  | NO_GPS
  | NONE
  | FIX_2D
  | FIX_3D
  | DGPS
  | RTK_FLOAT
  | RTK_FIXED
  | STATIC
  | PPP
deriving DecidableEq, Inhabited

/-- The value of each enumerator of `AP_GPS_FixType` (underlying type `uint8_t`). -/
def AP_GPS_FixType.toInt : AP_GPS_FixType → UInt8
  | .NO_GPS => (0 : UInt8)
  | .NONE => (1 : UInt8)
  | .FIX_2D => (2 : UInt8)
  | .FIX_3D => (3 : UInt8)
  | .DGPS => (4 : UInt8)
  | .RTK_FLOAT => (5 : UInt8)
  | .RTK_FIXED => (6 : UInt8)
  | .STATIC => (7 : UInt8)
  | .PPP => (8 : UInt8)

/-- The enumerator of `AP_GPS_FixType` with value `v` (the C++ converts only enumerator values; any other
value gives the first enumerator, the `Inhabited` default). -/
def AP_GPS_FixType.ofInt (v : UInt8) : AP_GPS_FixType :=
  if v == (0 : UInt8) then .NO_GPS
  else if v == (1 : UInt8) then .NONE
  else if v == (2 : UInt8) then .FIX_2D
  else if v == (3 : UInt8) then .FIX_3D
  else if v == (4 : UInt8) then .DGPS
  else if v == (5 : UInt8) then .RTK_FLOAT
  else if v == (6 : UInt8) then .RTK_FIXED
  else if v == (7 : UInt8) then .STATIC
  else if v == (8 : UInt8) then .PPP
  else default

namespace AP_GPS.Params

/-- State of C++ `AP_GPS::Params` (`AP_GPS/AP_GPS.h:127-147`): its data members. -/
structure State where
  /-- `AP_Enum<GPS_Type> type` of `AP_GPS::Params` (`AP_GPS/AP_GPS.h:132`). -/
  type : AP_Enum_AP_GPS_GPS_Type.State := {}
  /-- `AP_Int16 gnss_mode` of `AP_GPS::Params` (`AP_GPS/AP_GPS.h:133`). -/
  gnss_mode : AP_ParamT_short_2.State := {}
  /-- `AP_Int16 rate_ms` of `AP_GPS::Params` (`AP_GPS/AP_GPS.h:134`). -/
  rate_ms : AP_ParamT_short_2.State := {}
  /-- `AP_Vector3f antenna_offset` of `AP_GPS::Params` (`AP_GPS/AP_GPS.h:135`). -/
  antenna_offset : AP_ParamV_Vector3_float_5.State := {}
  /-- `AP_Int16 delay_ms` of `AP_GPS::Params` (`AP_GPS/AP_GPS.h:136`). -/
  delay_ms : AP_ParamT_short_2.State := {}
  /-- `AP_Int8 com_port` of `AP_GPS::Params` (`AP_GPS/AP_GPS.h:137`). -/
  com_port : AP_ParamT_signed_char_1.State := {}
deriving Inhabited

/-- C++ `AP_GPS::Params::Params()`, `AP_GPS/AP_GPS_Params.cpp:119-122`. -/
def init : State := Id.run do
  let mut s : State := {}
  s := { s with type._value := Binary32.toInt8 (Binary32.ofBits 0x00000000 /- (float)0 -/) }
  s := { s with gnss_mode._value := Binary32.toInt16 (Binary32.ofBits 0x00000000 /- (float)0 -/) }
  s := { s with rate_ms._value := Binary32.toInt16 (Binary32.ofBits 0x43480000 /- (float)200 -/) }
  let t'1 := (Binary32.ofBits 0x00000000 /- 0 -/)
  s := { s with antenna_offset._value := ({ x := t'1, y := t'1, z := t'1 } : Vector3f.State) }
  s := { s with delay_ms._value := Binary32.toInt16 (Binary32.ofBits 0x00000000 /- (float)0 -/) }
  return s

end AP_GPS.Params

namespace AP_GPS

/-- C++ `struct AP_GPS::GPS_State`, `AP_GPS/AP_GPS.h:193-255`. -/
structure GPS_State where
  /-- `uint8_t instance` of `AP_GPS::GPS_State` (`AP_GPS/AP_GPS.h:194`). -/
  «instance» : UInt8 := (0 : UInt8)
  /-- `AP_GPS_FixType status` of `AP_GPS::GPS_State` (`AP_GPS/AP_GPS.h:197`). -/
  status : AP_GPS_FixType := AP_GPS_FixType.NO_GPS
  /-- `uint32_t time_week_ms` of `AP_GPS::GPS_State` (`AP_GPS/AP_GPS.h:198`). -/
  time_week_ms : UInt32 := (0 : UInt32)
  /-- `uint16_t time_week` of `AP_GPS::GPS_State` (`AP_GPS/AP_GPS.h:199`). -/
  time_week : UInt16 := (0 : UInt16)
  /-- `Location location` of `AP_GPS::GPS_State` (`AP_GPS/AP_GPS.h:200`). -/
  location : Location.State := {}
  /-- `float ground_speed` of `AP_GPS::GPS_State` (`AP_GPS/AP_GPS.h:201`). -/
  ground_speed : Binary32 := (Binary32.ofBits 0x00000000 /- 0.0 -/)
  /-- `float ground_course` of `AP_GPS::GPS_State` (`AP_GPS/AP_GPS.h:202`). -/
  ground_course : Binary32 := (Binary32.ofBits 0x00000000 /- 0.0 -/)
  /-- `float gps_yaw` of `AP_GPS::GPS_State` (`AP_GPS/AP_GPS.h:203`). -/
  gps_yaw : Binary32 := (Binary32.ofBits 0x00000000 /- 0.0 -/)
  /-- `uint32_t gps_yaw_time_ms` of `AP_GPS::GPS_State` (`AP_GPS/AP_GPS.h:204`). -/
  gps_yaw_time_ms : UInt32 := (0 : UInt32)
  /-- `bool gps_yaw_configured` of `AP_GPS::GPS_State` (`AP_GPS/AP_GPS.h:205`). -/
  gps_yaw_configured : Bool := false
  /-- `uint16_t hdop` of `AP_GPS::GPS_State` (`AP_GPS/AP_GPS.h:206`). -/
  hdop : UInt16 := (0 : UInt16)
  /-- `uint16_t vdop` of `AP_GPS::GPS_State` (`AP_GPS/AP_GPS.h:207`). -/
  vdop : UInt16 := (0 : UInt16)
  /-- `uint8_t num_sats` of `AP_GPS::GPS_State` (`AP_GPS/AP_GPS.h:208`). -/
  num_sats : UInt8 := (0 : UInt8)
  /-- `Vector3f velocity` of `AP_GPS::GPS_State` (`AP_GPS/AP_GPS.h:209`). -/
  velocity : Vector3f.State := {}
  /-- `float speed_accuracy` of `AP_GPS::GPS_State` (`AP_GPS/AP_GPS.h:210`). -/
  speed_accuracy : Binary32 := (Binary32.ofBits 0x00000000 /- 0.0 -/)
  /-- `float horizontal_accuracy` of `AP_GPS::GPS_State` (`AP_GPS/AP_GPS.h:211`). -/
  horizontal_accuracy : Binary32 := (Binary32.ofBits 0x00000000 /- 0.0 -/)
  /-- `float vertical_accuracy` of `AP_GPS::GPS_State` (`AP_GPS/AP_GPS.h:212`). -/
  vertical_accuracy : Binary32 := (Binary32.ofBits 0x00000000 /- 0.0 -/)
  /-- `float gps_yaw_accuracy` of `AP_GPS::GPS_State` (`AP_GPS/AP_GPS.h:213`). -/
  gps_yaw_accuracy : Binary32 := (Binary32.ofBits 0x00000000 /- 0.0 -/)
  /-- `bool have_vertical_velocity` of `AP_GPS::GPS_State` (`AP_GPS/AP_GPS.h:214`). -/
  have_vertical_velocity : Bool := false
  /-- `bool have_speed_accuracy` of `AP_GPS::GPS_State` (`AP_GPS/AP_GPS.h:215`). -/
  have_speed_accuracy : Bool := false
  /-- `bool have_horizontal_accuracy` of `AP_GPS::GPS_State` (`AP_GPS/AP_GPS.h:216`). -/
  have_horizontal_accuracy : Bool := false
  /-- `bool have_vertical_accuracy` of `AP_GPS::GPS_State` (`AP_GPS/AP_GPS.h:217`). -/
  have_vertical_accuracy : Bool := false
  /-- `bool have_gps_yaw` of `AP_GPS::GPS_State` (`AP_GPS/AP_GPS.h:218`). -/
  have_gps_yaw : Bool := false
  /-- `bool have_gps_yaw_accuracy` of `AP_GPS::GPS_State` (`AP_GPS/AP_GPS.h:219`). -/
  have_gps_yaw_accuracy : Bool := false
  /-- `float undulation` of `AP_GPS::GPS_State` (`AP_GPS/AP_GPS.h:220`). -/
  undulation : Binary32 := (Binary32.ofBits 0x00000000 /- 0.0 -/)
  /-- `bool have_undulation` of `AP_GPS::GPS_State` (`AP_GPS/AP_GPS.h:221`). -/
  have_undulation : Bool := false
  /-- `uint32_t last_gps_time_ms` of `AP_GPS::GPS_State` (`AP_GPS/AP_GPS.h:222`). -/
  last_gps_time_ms : UInt32 := (0 : UInt32)
  /-- `bool announced_detection` of `AP_GPS::GPS_State` (`AP_GPS/AP_GPS.h:223`). -/
  announced_detection : Bool := false
  /-- `uint64_t last_corrected_gps_time_us` of `AP_GPS::GPS_State` (`AP_GPS/AP_GPS.h:224`). -/
  last_corrected_gps_time_us : UInt64 := (0 : UInt64)
  /-- `bool corrected_timestamp_updated` of `AP_GPS::GPS_State` (`AP_GPS/AP_GPS.h:225`). -/
  corrected_timestamp_updated : Bool := false
  /-- `uint32_t lagged_sample_count` of `AP_GPS::GPS_State` (`AP_GPS/AP_GPS.h:226`). -/
  lagged_sample_count : UInt32 := (0 : UInt32)
  /-- `uint32_t rtk_time_week_ms` of `AP_GPS::GPS_State` (`AP_GPS/AP_GPS.h:229`). -/
  rtk_time_week_ms : UInt32 := (0 : UInt32)
  /-- `uint16_t rtk_week_number` of `AP_GPS::GPS_State` (`AP_GPS/AP_GPS.h:230`). -/
  rtk_week_number : UInt16 := (0 : UInt16)
  /-- `uint32_t rtk_age_ms` of `AP_GPS::GPS_State` (`AP_GPS/AP_GPS.h:231`). -/
  rtk_age_ms : UInt32 := (0 : UInt32)
  /-- `uint8_t rtk_num_sats` of `AP_GPS::GPS_State` (`AP_GPS/AP_GPS.h:232`). -/
  rtk_num_sats : UInt8 := (0 : UInt8)
  /-- `uint8_t rtk_baseline_coords_type` of `AP_GPS::GPS_State` (`AP_GPS/AP_GPS.h:233`). -/
  rtk_baseline_coords_type : UInt8 := (0 : UInt8)
  /-- `int32_t rtk_baseline_x_mm` of `AP_GPS::GPS_State` (`AP_GPS/AP_GPS.h:234`). -/
  rtk_baseline_x_mm : Int32 := (0 : Int32)
  /-- `int32_t rtk_baseline_y_mm` of `AP_GPS::GPS_State` (`AP_GPS/AP_GPS.h:235`). -/
  rtk_baseline_y_mm : Int32 := (0 : Int32)
  /-- `int32_t rtk_baseline_z_mm` of `AP_GPS::GPS_State` (`AP_GPS/AP_GPS.h:236`). -/
  rtk_baseline_z_mm : Int32 := (0 : Int32)
  /-- `uint32_t rtk_accuracy` of `AP_GPS::GPS_State` (`AP_GPS/AP_GPS.h:237`). -/
  rtk_accuracy : UInt32 := (0 : UInt32)
  /-- `int32_t rtk_iar_num_hypotheses` of `AP_GPS::GPS_State` (`AP_GPS/AP_GPS.h:238`). -/
  rtk_iar_num_hypotheses : Int32 := (0 : Int32)
  /-- `float relPosHeading` of `AP_GPS::GPS_State` (`AP_GPS/AP_GPS.h:241`). -/
  relPosHeading : Binary32 := (Binary32.ofBits 0x00000000 /- 0.0 -/)
  /-- `float relPosLength` of `AP_GPS::GPS_State` (`AP_GPS/AP_GPS.h:242`). -/
  relPosLength : Binary32 := (Binary32.ofBits 0x00000000 /- 0.0 -/)
  /-- `float relPosD` of `AP_GPS::GPS_State` (`AP_GPS/AP_GPS.h:243`). -/
  relPosD : Binary32 := (Binary32.ofBits 0x00000000 /- 0.0 -/)
  /-- `float accHeading` of `AP_GPS::GPS_State` (`AP_GPS/AP_GPS.h:244`). -/
  accHeading : Binary32 := (Binary32.ofBits 0x00000000 /- 0.0 -/)
  /-- `uint32_t relposheading_ts` of `AP_GPS::GPS_State` (`AP_GPS/AP_GPS.h:245`). -/
  relposheading_ts : UInt32 := (0 : UInt32)
deriving Inhabited

/-- C++ `struct AP_GPS::GPS_timing`, `AP_GPS/AP_GPS.h:671-686`. -/
structure GPS_timing where
  /-- `uint32_t last_fix_time_ms` of `AP_GPS::GPS_timing` (`AP_GPS/AP_GPS.h:673`). -/
  last_fix_time_ms : UInt32 := (0 : UInt32)
  /-- `uint32_t last_message_time_ms` of `AP_GPS::GPS_timing` (`AP_GPS/AP_GPS.h:676`). -/
  last_message_time_ms : UInt32 := (0 : UInt32)
  /-- `uint16_t delta_time_ms` of `AP_GPS::GPS_timing` (`AP_GPS/AP_GPS.h:679`). -/
  delta_time_ms : UInt16 := (0 : UInt16)
  /-- `uint8_t delayed_count` of `AP_GPS::GPS_timing` (`AP_GPS/AP_GPS.h:682`). -/
  delayed_count : UInt8 := (0 : UInt8)
  /-- `float average_delta_ms` of `AP_GPS::GPS_timing` (`AP_GPS/AP_GPS.h:685`). -/
  average_delta_ms : Binary32 := (Binary32.ofBits 0x00000000 /- 0.0 -/)
deriving Inhabited

/-- C++ `struct AP_GPS::detect_state`, `AP_GPS/AP_GPS.h:703-726`. -/
structure detect_state where
  /-- `uint32_t last_baud_change_ms` of `AP_GPS::detect_state` (`AP_GPS/AP_GPS.h:704`). -/
  last_baud_change_ms : UInt32 := (0 : UInt32)
  /-- `uint8_t current_baud` of `AP_GPS::detect_state` (`AP_GPS/AP_GPS.h:705`). -/
  current_baud : UInt8 := (0 : UInt8)
  /-- `uint32_t probe_baud` of `AP_GPS::detect_state` (`AP_GPS/AP_GPS.h:706`). -/
  probe_baud : UInt32 := (0 : UInt32)
  /-- `bool auto_detected_baud` of `AP_GPS::detect_state` (`AP_GPS/AP_GPS.h:707`). -/
  auto_detected_baud : Bool := false
deriving Inhabited

/-- C++ `struct AP_GPS::(unnamed struct at AP_GPS/AP_GPS.h:728:5)`, `AP_GPS/AP_GPS.h:728-731`. -/
structure initblob_state_t where
  /-- `const char * blob` of `AP_GPS::(unnamed struct at AP_GPS/AP_GPS.h:728:5)` (`AP_GPS/AP_GPS.h:729`). -/
  blob : String := ""
  /-- `uint16_t remaining` of `AP_GPS::(unnamed struct at AP_GPS/AP_GPS.h:728:5)` (`AP_GPS/AP_GPS.h:730`). -/
  remaining : UInt16 := (0 : UInt16)
deriving Inhabited

/-- C++ `struct AP_GPS::(unnamed struct at AP_GPS/AP_GPS.h:769:5)`, `AP_GPS/AP_GPS.h:769-772`. -/
structure rtcm_stats_t where
  /-- `uint16_t fragments_used` of `AP_GPS::(unnamed struct at AP_GPS/AP_GPS.h:769:5)` (`AP_GPS/AP_GPS.h:770`). -/
  fragments_used : UInt16 := (0 : UInt16)
  /-- `uint16_t fragments_discarded` of `AP_GPS::(unnamed struct at AP_GPS/AP_GPS.h:769:5)` (`AP_GPS/AP_GPS.h:771`). -/
  fragments_discarded : UInt16 := (0 : UInt16)
deriving Inhabited

end AP_GPS

namespace AP_GPS

/-- State of C++ `AP_GPS` (`AP_GPS/AP_GPS.h:50-837`): its data members. -/
structure State where
  /-- `Params params[3]` of `AP_GPS` (`AP_GPS/AP_GPS.h:627`). -/
  params : Array AP_GPS.Params.State := Array.replicate 3 AP_GPS.Params.init
  /-- `AP_Int8 _navfilter` of `AP_GPS` (`AP_GPS/AP_GPS.h:628`). -/
  _navfilter : AP_ParamT_signed_char_1.State := {}
  /-- `AP_Int8 _auto_switch` of `AP_GPS` (`AP_GPS/AP_GPS.h:629`). -/
  _auto_switch : AP_ParamT_signed_char_1.State := {}
  /-- `AP_Int16 _sbp_logmask` of `AP_GPS` (`AP_GPS/AP_GPS.h:630`). -/
  _sbp_logmask : AP_ParamT_short_2.State := {}
  /-- `AP_Int8 _inject_to` of `AP_GPS` (`AP_GPS/AP_GPS.h:631`). -/
  _inject_to : AP_ParamT_signed_char_1.State := {}
  /-- `uint32_t _last_instance_swap_ms` of `AP_GPS` (`AP_GPS/AP_GPS.h:632`). -/
  _last_instance_swap_ms : UInt32 := (0 : UInt32)
  /-- `AP_Enum<SBAS_Mode> _sbas_mode` of `AP_GPS` (`AP_GPS/AP_GPS.h:633`). -/
  _sbas_mode : AP_Enum_AP_GPS_SBAS_Mode.State := {}
  /-- `AP_Int8 _min_elevation` of `AP_GPS` (`AP_GPS/AP_GPS.h:634`). -/
  _min_elevation : AP_ParamT_signed_char_1.State := {}
  /-- `AP_Int8 _raw_data` of `AP_GPS` (`AP_GPS/AP_GPS.h:635`). -/
  _raw_data : AP_ParamT_signed_char_1.State := {}
  /-- `AP_Int8 _save_config` of `AP_GPS` (`AP_GPS/AP_GPS.h:636`). -/
  _save_config : AP_ParamT_signed_char_1.State := {}
  /-- `AP_Int8 _auto_config` of `AP_GPS` (`AP_GPS/AP_GPS.h:637`). -/
  _auto_config : AP_ParamT_signed_char_1.State := {}
  /-- `AP_UInt8 _blend_mask` of `AP_GPS` (`AP_GPS/AP_GPS.h:638`). -/
  _blend_mask : AP_ParamT_unsigned_char_1.State := {}
  /-- `AP_UInt16 _driver_options` of `AP_GPS` (`AP_GPS/AP_GPS.h:639`). -/
  _driver_options : AP_ParamT_unsigned_short_2.State := {}
  /-- `AP_Int8 _primary` of `AP_GPS` (`AP_GPS/AP_GPS.h:640`). -/
  _primary : AP_ParamT_signed_char_1.State := {}
  /-- `uint32_t _log_gps_bit` of `AP_GPS` (`AP_GPS/AP_GPS.h:642`). -/
  _log_gps_bit : UInt32 := Int32.toUInt32 (-(1 : Int32))
  /-- `GPS_timing timing[3]` of `AP_GPS` (`AP_GPS/AP_GPS.h:688`). -/
  timing : Array AP_GPS.GPS_timing := Array.replicate 3 {}
  /-- `GPS_State state[3]` of `AP_GPS` (`AP_GPS/AP_GPS.h:689`). -/
  state : Array AP_GPS.GPS_State := Array.replicate 3 {}
  /-- `AP_GPS_Backend * drivers[3]` of `AP_GPS` (`AP_GPS/AP_GPS.h:690`). -/
  drivers : Array WPtr := Array.replicate 3 WPtr.null
  /-- `AP_HAL::UARTDriver * _port[2]` of `AP_GPS` (`AP_GPS/AP_GPS.h:691`). -/
  _port : Array WPtr := Array.replicate 2 WPtr.null
  /-- `uint8_t primary_instance` of `AP_GPS` (`AP_GPS/AP_GPS.h:694`). -/
  primary_instance : UInt8 := (0 : UInt8)
  /-- `uint8_t num_instances` of `AP_GPS` (`AP_GPS/AP_GPS.h:697`). -/
  num_instances : UInt8 := (0 : UInt8)
  /-- `uint8_t locked_ports` of `AP_GPS` (`AP_GPS/AP_GPS.h:700`). -/
  locked_ports : UInt8 := (0 : UInt8)
  /-- `struct detect_state detect_state[2]` of `AP_GPS` (`AP_GPS/AP_GPS.h:726`). -/
  detect_state : Array AP_GPS.detect_state := Array.replicate 2 {}
  /-- `struct (unnamed struct at AP_GPS/AP_GPS.h:728:5) initblob_state[2]` of `AP_GPS` (`AP_GPS/AP_GPS.h:731`). -/
  initblob_state : Array AP_GPS.initblob_state_t := Array.replicate 2 {}
  /-- `struct (unnamed struct at AP_GPS/AP_GPS.h:769:5) rtcm_stats` of `AP_GPS` (`AP_GPS/AP_GPS.h:772`). -/
  rtcm_stats : AP_GPS.rtcm_stats_t := {}
  /-- `bool _force_disable_gps` of `AP_GPS` (`AP_GPS/AP_GPS.h:814`). -/
  _force_disable_gps : Bool := false
  /-- `bool _force_disable_gps_yaw` of `AP_GPS` (`AP_GPS/AP_GPS.h:817`). -/
  _force_disable_gps_yaw : Bool := false
deriving Inhabited

/-- Values C++ `AP_GPS` reads from objects outside the translation (--boundary): one field per distinct read, in first-use order. -/
structure Inputs where
  /-- `params[0].type.configured()` (first read at `AP_GPS/AP_GPS.cpp:314`). -/
  params_0_type_configured : Bool := false
  /-- `AP::serialmanager().find_serial(...) for each uart_idx` (first read at `AP_GPS/AP_GPS.cpp:328`). -/
  find_serial_found_SerialProtocol_GPS_at1 : Array Bool := Array.replicate 0 false
deriving Inhabited

end AP_GPS

namespace AP_GPS_SITL

/-- State of C++ `AP_GPS_SITL` (`AP_GPS/AP_GPS_SITL.h:24-38`): its data members; base classes flattened, base first: `AP_GPS_Backend`. -/
structure State where
  /-- `AP_HAL::UARTDriver * port` of `AP_GPS_Backend` (`AP_GPS/GPS_Backend.h:124`). -/
  port : WPtr := WPtr.null
  /-- `uint64_t _last_pps_time_us` of `AP_GPS_Backend` (`AP_GPS/GPS_Backend.h:129`). -/
  _last_pps_time_us : UInt64 := (0 : UInt64)
  /-- `JitterCorrection jitter_correction` of `AP_GPS_Backend` (`AP_GPS/GPS_Backend.h:130`). -/
  jitter_correction : JitterCorrection.State := {}
  /-- `uint32_t _last_itow_ms` of `AP_GPS_Backend` (`AP_GPS/GPS_Backend.h:131`). -/
  _last_itow_ms : UInt32 := (0 : UInt32)
  /-- `bool _have_itow` of `AP_GPS_Backend` (`AP_GPS/GPS_Backend.h:132`). -/
  _have_itow : Bool := false
  /-- `uint64_t _pseudo_itow` of `AP_GPS_Backend` (`AP_GPS/GPS_Backend.h:187`). -/
  _pseudo_itow : UInt64 := (0 : UInt64)
  /-- `int32_t _pseudo_itow_delta_ms` of `AP_GPS_Backend` (`AP_GPS/GPS_Backend.h:188`). -/
  _pseudo_itow_delta_ms : Int32 := (0 : Int32)
  /-- `uint32_t _last_ms` of `AP_GPS_Backend` (`AP_GPS/GPS_Backend.h:189`). -/
  _last_ms : UInt32 := (0 : UInt32)
  /-- `uint32_t _rate_ms` of `AP_GPS_Backend` (`AP_GPS/GPS_Backend.h:190`). -/
  _rate_ms : UInt32 := (0 : UInt32)
  /-- `uint32_t _last_rate_ms` of `AP_GPS_Backend` (`AP_GPS/GPS_Backend.h:191`). -/
  _last_rate_ms : UInt32 := (0 : UInt32)
  /-- `uint16_t _rate_counter` of `AP_GPS_Backend` (`AP_GPS/GPS_Backend.h:192`). -/
  _rate_counter : UInt16 := (0 : UInt16)
  /-- `uint32_t last_update_ms` of `AP_GPS_SITL` (`AP_GPS/AP_GPS_SITL.h:37`). -/
  last_update_ms : UInt32 := (0 : UInt32)
  /-- The index of the element `state` refers to: `gps.state[i]` (--ins-gps). -/
  state'i : Nat := 0
  /-- The index of the element `params` refers to: `gps.params[i]` (--ins-gps). -/
  params'i : Nat := 0
deriving Inhabited

end AP_GPS_SITL

namespace AP_GPS

/-- C++ `AP_GPS_FixType AP_GPS::status(uint8_t instance) const`, `AP_GPS/AP_GPS.h:297-302`. -/
def status_uint8_t (s : State) («instance» : UInt8) : AP_GPS_FixType := Id.run do
  if s._force_disable_gps && decide (AP_GPS_FixType.toInt s.state[UInt8.toNat «instance»]!.status > AP_GPS_FixType.toInt AP_GPS_FixType.NONE) then
    return AP_GPS_FixType.NONE
  return s.state[UInt8.toNat «instance»]!.status

/-- C++ `AP_GPS_FixType AP_GPS::status() const`, `AP_GPS/AP_GPS.h:303-305`. -/
def status_void (s : State) : AP_GPS_FixType := Id.run do
  return status_uint8_t s s.primary_instance

/-- C++ `float AP_GPS::ground_speed(uint8_t instance) const`, `AP_GPS/AP_GPS.h:382-384`. -/
def ground_speed_uint8_t (s : State) («instance» : UInt8) : Binary32 := Id.run do
  return s.state[UInt8.toNat «instance»]!.ground_speed

/-- C++ `float AP_GPS::ground_speed() const`, `AP_GPS/AP_GPS.h:385-387`. -/
def ground_speed_void (s : State) : Binary32 := Id.run do
  return ground_speed_uint8_t s s.primary_instance

end AP_GPS

namespace AP_GPS

/-- C++ `uint8_t AP_GPS::primary_sensor() const`, `AP_GPS/AP_GPS.h:292-294`. -/
def primary_sensor (s : State) : UInt8 := Id.run do
  return s.primary_instance

/-- C++ `uint8_t AP_GPS::num_sensors() const`, `AP_GPS/AP_GPS.cpp:402-410`. -/
def num_sensors (s : State) : UInt8 := Id.run do
  return s.num_instances

/-- C++ `const Vector3f & AP_GPS::get_antenna_offset(uint8_t instance) const`, `AP_GPS/AP_GPS.cpp:1754-1769`. -/
def get_antenna_offset (s : State) («instance» : UInt8) : Vector3f.State := Id.run do
  if UInt32.toInt32 (UInt8.toUInt32 «instance») ≥ ((2 : Int32) + (1 : Int32)) then
    return AP_ParamV_Vector3_float_5.op_to_Vector3_float s.params[0]!.antenna_offset
  return AP_ParamV_Vector3_float_5.op_to_Vector3_float s.params[UInt8.toNat «instance»]!.antenna_offset

/-- C++ `uint32_t AP_GPS::last_message_time_ms(uint8_t instance) const`, `AP_GPS/AP_GPS.h:461-463`. -/
def last_message_time_ms_uint8_t (s : State) («instance» : UInt8) : UInt32 := Id.run do
  return s.timing[UInt8.toNat «instance»]!.last_message_time_ms

/-- C++ `bool AP_GPS::have_vertical_velocity(uint8_t instance) const`, `AP_GPS/AP_GPS.h:477-479`. -/
def have_vertical_velocity_uint8_t (s : State) («instance» : UInt8) : Bool := Id.run do
  return s.state[UInt8.toNat «instance»]!.have_vertical_velocity

/-- C++ `bool AP_GPS::horizontal_accuracy(uint8_t instance, float & hacc) const`, `AP_GPS/AP_GPS.cpp:421-428`. -/
def horizontal_accuracy_uint8_t_float (s : State) («instance» : UInt8) (hacc : Binary32) : Binary32 × Bool := Id.run do
  let mut hacc := hacc
  if s.state[UInt8.toNat «instance»]!.have_horizontal_accuracy then
    hacc := s.state[UInt8.toNat «instance»]!.horizontal_accuracy
    return (hacc, true)
  return (hacc, false)

/-- C++ `bool AP_GPS::vertical_accuracy(uint8_t instance, float & vacc) const`, `AP_GPS/AP_GPS.cpp:430-437`. -/
def vertical_accuracy_uint8_t_float (s : State) («instance» : UInt8) (vacc : Binary32) : Binary32 × Bool := Id.run do
  let mut vacc := vacc
  if s.state[UInt8.toNat «instance»]!.have_vertical_accuracy then
    vacc := s.state[UInt8.toNat «instance»]!.vertical_accuracy
    return (vacc, true)
  return (vacc, false)

/-- C++ `bool AP_GPS::speed_accuracy(uint8_t instance, float & sacc) const`, `AP_GPS/AP_GPS.cpp:412-419`. -/
def speed_accuracy_uint8_t_float (s : State) («instance» : UInt8) (sacc : Binary32) : Binary32 × Bool := Id.run do
  let mut sacc := sacc
  if s.state[UInt8.toNat «instance»]!.have_speed_accuracy then
    sacc := s.state[UInt8.toNat «instance»]!.speed_accuracy
    return (sacc, true)
  return (sacc, false)

/-- C++ `uint16_t AP_GPS::get_hdop(uint8_t instance) const`, `AP_GPS/AP_GPS.h:435-437`. -/
def get_hdop_uint8_t (s : State) («instance» : UInt8) : UInt16 := Id.run do
  return s.state[UInt8.toNat «instance»]!.hdop

/-- C++ `uint8_t AP_GPS::num_sats(uint8_t instance) const`, `AP_GPS/AP_GPS.h:411-413`. -/
def num_sats_uint8_t (s : State) («instance» : UInt8) : UInt8 := Id.run do
  return s.state[UInt8.toNat «instance»]!.num_sats

/-- C++ `enum AP_GPS::GPS_Type`, `AP_GPS/AP_GPS.h:86-116`. -/
inductive GPS_Type where
  | GPS_TYPE_NONE
  | GPS_TYPE_AUTO
  | GPS_TYPE_UBLOX
  | GPS_TYPE_NMEA
  | GPS_TYPE_SIRF
  | GPS_TYPE_HIL
  | GPS_TYPE_SBP
  | GPS_TYPE_UAVCAN
  | GPS_TYPE_SBF
  | GPS_TYPE_GSOF
  | GPS_TYPE_ERB
  | GPS_TYPE_MAV
  | GPS_TYPE_NOVA
  | GPS_TYPE_HEMI
  | GPS_TYPE_UBLOX_RTK_BASE
  | GPS_TYPE_UBLOX_RTK_ROVER
  | GPS_TYPE_MSP
  | GPS_TYPE_ALLYSTAR
  | GPS_TYPE_EXTERNAL_AHRS
  | GPS_TYPE_UAVCAN_RTK_BASE
  | GPS_TYPE_UAVCAN_RTK_ROVER
  | GPS_TYPE_UNICORE_NMEA
  | GPS_TYPE_UNICORE_MOVINGBASE_NMEA
  | GPS_TYPE_SBF_DUAL_ANTENNA
  | GPS_TYPE_SITL
deriving DecidableEq, Inhabited

/-- The value of each enumerator of `AP_GPS::GPS_Type` (underlying type `uint32_t`). -/
def GPS_Type.toInt : GPS_Type → UInt32
  | .GPS_TYPE_NONE => (0 : UInt32)
  | .GPS_TYPE_AUTO => (1 : UInt32)
  | .GPS_TYPE_UBLOX => (2 : UInt32)
  | .GPS_TYPE_NMEA => (5 : UInt32)
  | .GPS_TYPE_SIRF => (6 : UInt32)
  | .GPS_TYPE_HIL => (7 : UInt32)
  | .GPS_TYPE_SBP => (8 : UInt32)
  | .GPS_TYPE_UAVCAN => (9 : UInt32)
  | .GPS_TYPE_SBF => (10 : UInt32)
  | .GPS_TYPE_GSOF => (11 : UInt32)
  | .GPS_TYPE_ERB => (13 : UInt32)
  | .GPS_TYPE_MAV => (14 : UInt32)
  | .GPS_TYPE_NOVA => (15 : UInt32)
  | .GPS_TYPE_HEMI => (16 : UInt32)
  | .GPS_TYPE_UBLOX_RTK_BASE => (17 : UInt32)
  | .GPS_TYPE_UBLOX_RTK_ROVER => (18 : UInt32)
  | .GPS_TYPE_MSP => (19 : UInt32)
  | .GPS_TYPE_ALLYSTAR => (20 : UInt32)
  | .GPS_TYPE_EXTERNAL_AHRS => (21 : UInt32)
  | .GPS_TYPE_UAVCAN_RTK_BASE => (22 : UInt32)
  | .GPS_TYPE_UAVCAN_RTK_ROVER => (23 : UInt32)
  | .GPS_TYPE_UNICORE_NMEA => (24 : UInt32)
  | .GPS_TYPE_UNICORE_MOVINGBASE_NMEA => (25 : UInt32)
  | .GPS_TYPE_SBF_DUAL_ANTENNA => (26 : UInt32)
  | .GPS_TYPE_SITL => (100 : UInt32)

/-- The enumerator of `AP_GPS::GPS_Type` with value `v` (the C++ converts only enumerator values; any other
value gives the first enumerator, the `Inhabited` default). -/
def GPS_Type.ofInt (v : UInt32) : GPS_Type :=
  if v == (0 : UInt32) then .GPS_TYPE_NONE
  else if v == (1 : UInt32) then .GPS_TYPE_AUTO
  else if v == (2 : UInt32) then .GPS_TYPE_UBLOX
  else if v == (5 : UInt32) then .GPS_TYPE_NMEA
  else if v == (6 : UInt32) then .GPS_TYPE_SIRF
  else if v == (7 : UInt32) then .GPS_TYPE_HIL
  else if v == (8 : UInt32) then .GPS_TYPE_SBP
  else if v == (9 : UInt32) then .GPS_TYPE_UAVCAN
  else if v == (10 : UInt32) then .GPS_TYPE_SBF
  else if v == (11 : UInt32) then .GPS_TYPE_GSOF
  else if v == (13 : UInt32) then .GPS_TYPE_ERB
  else if v == (14 : UInt32) then .GPS_TYPE_MAV
  else if v == (15 : UInt32) then .GPS_TYPE_NOVA
  else if v == (16 : UInt32) then .GPS_TYPE_HEMI
  else if v == (17 : UInt32) then .GPS_TYPE_UBLOX_RTK_BASE
  else if v == (18 : UInt32) then .GPS_TYPE_UBLOX_RTK_ROVER
  else if v == (19 : UInt32) then .GPS_TYPE_MSP
  else if v == (20 : UInt32) then .GPS_TYPE_ALLYSTAR
  else if v == (21 : UInt32) then .GPS_TYPE_EXTERNAL_AHRS
  else if v == (22 : UInt32) then .GPS_TYPE_UAVCAN_RTK_BASE
  else if v == (23 : UInt32) then .GPS_TYPE_UAVCAN_RTK_ROVER
  else if v == (24 : UInt32) then .GPS_TYPE_UNICORE_NMEA
  else if v == (25 : UInt32) then .GPS_TYPE_UNICORE_MOVINGBASE_NMEA
  else if v == (26 : UInt32) then .GPS_TYPE_SBF_DUAL_ANTENNA
  else if v == (100 : UInt32) then .GPS_TYPE_SITL
  else default

end AP_GPS

namespace AP_GPS_SITL

/-- C++ `bool AP_GPS_Backend::get_lag(float & lag) const`, `AP_GPS/GPS_Backend.h:90` (a member of `AP_GPS_Backend`, translated for `AP_GPS_SITL`). -/
def get_lag (lag : Binary32) : Binary32 × Bool := Id.run do
  let mut lag := lag
  lag := (Binary32.ofBits 0x3e4ccccd /- 0.2f -/)
  return (lag, true)

end AP_GPS_SITL

namespace AP_GPS

/-- C++ `float AP_GPS::ground_course(uint8_t instance) const`, `AP_GPS/AP_GPS.h:390-392`. -/
def ground_course_uint8_t (s : State) («instance» : UInt8) : Binary32 := Id.run do
  return s.state[UInt8.toNat «instance»]!.ground_course

/-- C++ `float AP_GPS::ground_course() const`, `AP_GPS/AP_GPS.h:393-395`. -/
def ground_course_void (s : State) : Binary32 := Id.run do
  return ground_course_uint8_t s s.primary_instance

end AP_GPS

namespace AP_GPS

/-- C++ `uint32_t AP_GPS::last_fix_time_ms(uint8_t instance) const`, `AP_GPS/AP_GPS.h:452-454`. -/
def last_fix_time_ms_uint8_t (s : State) («instance» : UInt8) : UInt32 := Id.run do
  return s.timing[UInt8.toNat «instance»]!.last_fix_time_ms

/-- C++ `uint32_t AP_GPS::last_fix_time_ms() const`, `AP_GPS/AP_GPS.h:455-457`. -/
def last_fix_time_ms_void (s : State) : UInt32 := Id.run do
  return last_fix_time_ms_uint8_t s s.primary_instance

end AP_GPS

namespace AP_GPS

/-- C++ `uint32_t AP_GPS::last_message_time_ms() const`, `AP_GPS/AP_GPS.h:464-466`. -/
def last_message_time_ms_void (s : State) : UInt32 := Id.run do
  return last_message_time_ms_uint8_t s s.primary_instance

end AP_GPS

namespace AP_GPS

/-- C++ `static const uint32_t AP_GPS::_baudrates[8]`, `AP_GPS/AP_GPS.cpp:79`. -/
def _baudrates : Array UInt32 := #[(9600 : UInt32), (115200 : UInt32), (4800 : UInt32), (19200 : UInt32), (38400 : UInt32), (57600 : UInt32), (230400 : UInt32), (460800 : UInt32)]

/-- C++ `bool AP_GPS::needs_uart(GPS_Type type) const`, `AP_GPS/AP_GPS.cpp:292-308`. -/
def needs_uart (type : AP_GPS.GPS_Type) : Bool := Id.run do
  match type with
  | .GPS_TYPE_NONE | .GPS_TYPE_HIL | .GPS_TYPE_UAVCAN | .GPS_TYPE_UAVCAN_RTK_BASE | .GPS_TYPE_UAVCAN_RTK_ROVER | .GPS_TYPE_MAV | .GPS_TYPE_MSP | .GPS_TYPE_EXTERNAL_AHRS =>
    return false
  | _ =>
    pure ()
  return true

end AP_GPS

namespace AP_GPS_SITL

/-- C++ `void AP_GPS_Backend::velocity_to_speed_course(AP_GPS::GPS_State & s)`, `AP_GPS/GPS_Backend.cpp:110-114` (a member of `AP_GPS_Backend`, translated for `AP_GPS_SITL`). -/
def velocity_to_speed_course (s' : AP_GPS.GPS_State) : AP_GPS.GPS_State := Id.run do
  let mut s' := s'
  s' := { s' with ground_course := Estimator_lib.wrap_360_float (Estimator_lib.degrees (Musl.atan2f.atan2f s'.velocity.y s'.velocity.x)) }
  s' := { s' with ground_speed := Vector2f.length (Vector3f.xy s'.velocity) }
  return s'

end AP_GPS_SITL

namespace AP_GPS_SITL

/-- C++ `bool AP_GPS_Backend::is_configured() const`, `AP_GPS/GPS_Backend.h:67` (a member of `AP_GPS_Backend`, translated for `AP_GPS_SITL`). -/
def is_configured : Bool := Id.run do
  return true

end AP_GPS_SITL

namespace AP_GPS_SITL

/-- C++ `bool AP_GPS_Backend::is_healthy() const`, `AP_GPS/GPS_Backend.h:93` (a member of `AP_GPS_Backend`, translated for `AP_GPS_SITL`). -/
def is_healthy : Bool := Id.run do
  return true

end AP_GPS_SITL

namespace AP_GPS_SITL

/-- C++ `bool AP_GPS_Backend::prepare_for_arming()`, `AP_GPS/GPS_Backend.h:104` (a member of `AP_GPS_Backend`, translated for `AP_GPS_SITL`). -/
def prepare_for_arming : Bool := Id.run do
  return true

end AP_GPS_SITL

namespace AP_GPS_SITL

/-! Not emitted, since they have no effect in the model (they write neither the state, the
parameters nor a reference parameter; e.g. they only save parameters):
- C++ `void AP_GPS_Backend::broadcast_configuration_failure_reason() const`, `AP_GPS/GPS_Backend.h:80` (a member of `AP_GPS_Backend`, translated for `AP_GPS_SITL`).
-/

end AP_GPS_SITL

end Estimator_lib
