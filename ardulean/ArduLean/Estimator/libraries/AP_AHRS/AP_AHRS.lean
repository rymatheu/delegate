import ArduLean.Musl.cosf
import ArduLean.Musl.sinf
import ArduLean.Estimator.mavlink.mavlink
import ArduLean.Estimator.libraries.AP_Math.AP_Math
import ArduLean.Estimator.World
import ArduLean.Estimator.libraries.AP_Common.AP_Common
import ArduLean.Estimator.libraries.AP_Param.AP_Param

/-!
ArduPilot `libraries/AP_AHRS`, part 1 of 4. Sources: `libraries/AP_AHRS/AP_AHRS_Backend.h`, `libraries/AP_AHRS/AP_AHRS.h`, `libraries/AP_AHRS/AP_AHRS_DCM.h`, `libraries/AP_AHRS/AP_AHRS_Backend.cpp`, `libraries/AP_AHRS/AP_AHRS_View.h`, `libraries/AP_AHRS/AP_AHRS_NavEKF3.h`, `libraries/AP_AHRS/AP_AHRS.cpp`, `libraries/AP_AHRS/AP_AHRS_SIM.h`.

Items of `lean/Estimator_lib.lean` (the estimator translation), unchanged; placed by `tools/split_modules.py` (`ArduLean/Estimator/INDEX.md`).
-/

open FloatLib.Floats (Binary32 Binary64)

set_option maxRecDepth 200000
-- AP_DAL's `const log_RISH old_RISH = _RISH;` read only by WRITE_REPLAY_BLOCK_IFCHANGED, which is `(void)old`
-- without logging (HAL_LOGGING_ENABLED 0): an unused binding, as in the C++
set_option linter.unusedVariables false

namespace Estimator_lib

namespace AP_AHRS

/-- C++ `enum class AP_AHRS::EKFType`, `AP_AHRS/AP_AHRS.h:504-520`. -/
inductive EKFType where
  | DCM
  | THREE
  | SIM
deriving DecidableEq, Inhabited

/-- The value of each enumerator of `AP_AHRS::EKFType` (underlying type `uint8_t`). -/
def EKFType.toInt : EKFType → UInt8
  | .DCM => (0 : UInt8)
  | .THREE => (3 : UInt8)
  | .SIM => (10 : UInt8)

/-- The enumerator of `AP_AHRS::EKFType` with value `v` (the C++ converts only enumerator values; any other
value gives the first enumerator, the `Inhabited` default). -/
def EKFType.ofInt (v : UInt8) : EKFType :=
  if v == (0 : UInt8) then .DCM
  else if v == (3 : UInt8) then .THREE
  else if v == (10 : UInt8) then .SIM
  else default

/-- C++ `enum class AP_AHRS::VehicleClass`, `AP_AHRS/AP_AHRS.h:744-750`. -/
inductive VehicleClass where
  | UNKNOWN
  | GROUND
  | COPTER
  | FIXED_WING
  | SUBMARINE
deriving DecidableEq, Inhabited

/-- The value of each enumerator of `AP_AHRS::VehicleClass` (underlying type `uint8_t`). -/
def VehicleClass.toInt : VehicleClass → UInt8
  | .UNKNOWN => (0 : UInt8)
  | .GROUND => (1 : UInt8)
  | .COPTER => (2 : UInt8)
  | .FIXED_WING => (3 : UInt8)
  | .SUBMARINE => (4 : UInt8)

/-- C++ `enum class AP_AHRS::TriState`, `AP_AHRS/AP_AHRS.h:854-858`. -/
inductive TriState where
  | False
  | True
  | UNKNOWN
deriving DecidableEq, Inhabited

/-- The value of each enumerator of `AP_AHRS::TriState` (underlying type `int32_t`). -/
def TriState.toInt : TriState → Int32
  | .False => (0 : Int32)
  | .True => (1 : Int32)
  | .UNKNOWN => (3 : Int32)

/-- The enumerator of `AP_AHRS::TriState` with value `v` (the C++ converts only enumerator values; any other
value gives the first enumerator, the `Inhabited` default). -/
def TriState.ofInt (v : Int32) : TriState :=
  if v == (0 : Int32) then .False
  else if v == (1 : Int32) then .True
  else if v == (3 : Int32) then .UNKNOWN
  else default

end AP_AHRS

namespace AP_AHRS_Backend

/-- C++ `enum AP_AHRS_Backend::AirspeedEstimateType`, `AP_AHRS/AP_AHRS_Backend.h:59-70`. -/
inductive AirspeedEstimateType where
  | NO_NEW_ESTIMATE
  | AIRSPEED_SENSOR
  | DCM_SYNTHETIC
  | EKF3_SYNTHETIC
  | SIM
  | DCM_FALLBACK
deriving DecidableEq, Inhabited

/-- The value of each enumerator of `AP_AHRS_Backend::AirspeedEstimateType` (underlying type `uint8_t`). -/
def AirspeedEstimateType.toInt : AirspeedEstimateType → UInt8
  | .NO_NEW_ESTIMATE => (0 : UInt8)
  | .AIRSPEED_SENSOR => (1 : UInt8)
  | .DCM_SYNTHETIC => (2 : UInt8)
  | .EKF3_SYNTHETIC => (3 : UInt8)
  | .SIM => (4 : UInt8)
  | .DCM_FALLBACK => (5 : UInt8)

end AP_AHRS_Backend

namespace AP_AHRS

/-- C++ `struct AP_AHRS::(unnamed struct at AP_AHRS/AP_AHRS.h:983:5)`, `AP_AHRS/AP_AHRS.h:983-1014`. -/
structure state_t where
  /-- `EKFType active_EKF_type` of `AP_AHRS::(unnamed struct at AP_AHRS/AP_AHRS.h:983:5)` (`AP_AHRS/AP_AHRS.h:984`). -/
  active_EKF_type : AP_AHRS.EKFType := AP_AHRS.EKFType.DCM
  /-- `EKFType configured_ekf_type` of `AP_AHRS::(unnamed struct at AP_AHRS/AP_AHRS.h:983:5)` (`AP_AHRS/AP_AHRS.h:985`). -/
  configured_ekf_type : AP_AHRS.EKFType := AP_AHRS.EKFType.DCM
  /-- `uint8_t primary_gyro` of `AP_AHRS::(unnamed struct at AP_AHRS/AP_AHRS.h:983:5)` (`AP_AHRS/AP_AHRS.h:986`). -/
  primary_gyro : UInt8 := (0 : UInt8)
  /-- `uint8_t primary_accel` of `AP_AHRS::(unnamed struct at AP_AHRS/AP_AHRS.h:983:5)` (`AP_AHRS/AP_AHRS.h:987`). -/
  primary_accel : UInt8 := (0 : UInt8)
  /-- `Vector3f gyro_estimate` of `AP_AHRS::(unnamed struct at AP_AHRS/AP_AHRS.h:983:5)` (`AP_AHRS/AP_AHRS.h:988`). -/
  gyro_estimate : Vector3f.State := {}
  /-- `Matrix3f dcm_matrix` of `AP_AHRS::(unnamed struct at AP_AHRS/AP_AHRS.h:983:5)` (`AP_AHRS/AP_AHRS.h:989`). -/
  dcm_matrix : Matrix3f.State := Matrix3f.init_void
  /-- `Vector3f gyro_drift` of `AP_AHRS::(unnamed struct at AP_AHRS/AP_AHRS.h:983:5)` (`AP_AHRS/AP_AHRS.h:990`). -/
  gyro_drift : Vector3f.State := {}
  /-- `Vector3f accel_ef` of `AP_AHRS::(unnamed struct at AP_AHRS/AP_AHRS.h:983:5)` (`AP_AHRS/AP_AHRS.h:991`). -/
  accel_ef : Vector3f.State := {}
  /-- `Vector3f accel_bias` of `AP_AHRS::(unnamed struct at AP_AHRS/AP_AHRS.h:983:5)` (`AP_AHRS/AP_AHRS.h:992`). -/
  accel_bias : Vector3f.State := {}
  /-- `float EAS2TAS` of `AP_AHRS::(unnamed struct at AP_AHRS/AP_AHRS.h:983:5)` (`AP_AHRS/AP_AHRS.h:993`). -/
  EAS2TAS : Binary32 := (Binary32.ofBits 0x00000000 /- 0.0 -/)
  /-- `bool airspeed_EAS_ok` of `AP_AHRS::(unnamed struct at AP_AHRS/AP_AHRS.h:983:5)` (`AP_AHRS/AP_AHRS.h:994`). -/
  airspeed_EAS_ok : Bool := false
  /-- `float airspeed_EAS` of `AP_AHRS::(unnamed struct at AP_AHRS/AP_AHRS.h:983:5)` (`AP_AHRS/AP_AHRS.h:995`). -/
  airspeed_EAS : Binary32 := (Binary32.ofBits 0x00000000 /- 0.0 -/)
  /-- `AirspeedEstimateType airspeed_estimate_type` of `AP_AHRS::(unnamed struct at AP_AHRS/AP_AHRS.h:983:5)` (`AP_AHRS/AP_AHRS.h:996`). -/
  airspeed_estimate_type : AP_AHRS_Backend.AirspeedEstimateType := AP_AHRS_Backend.AirspeedEstimateType.NO_NEW_ESTIMATE
  /-- `bool airspeed_TAS_ok` of `AP_AHRS::(unnamed struct at AP_AHRS/AP_AHRS.h:983:5)` (`AP_AHRS/AP_AHRS.h:997`). -/
  airspeed_TAS_ok : Bool := false
  /-- `float airspeed_TAS` of `AP_AHRS::(unnamed struct at AP_AHRS/AP_AHRS.h:983:5)` (`AP_AHRS/AP_AHRS.h:998`). -/
  airspeed_TAS : Binary32 := (Binary32.ofBits 0x00000000 /- 0.0 -/)
  /-- `Vector3f airspeed_TAS_vec` of `AP_AHRS::(unnamed struct at AP_AHRS/AP_AHRS.h:983:5)` (`AP_AHRS/AP_AHRS.h:999`). -/
  airspeed_TAS_vec : Vector3f.State := {}
  /-- `bool airspeed_TAS_vec_ok` of `AP_AHRS::(unnamed struct at AP_AHRS/AP_AHRS.h:983:5)` (`AP_AHRS/AP_AHRS.h:1000`). -/
  airspeed_TAS_vec_ok : Bool := false
  /-- `Quaternion quat` of `AP_AHRS::(unnamed struct at AP_AHRS/AP_AHRS.h:983:5)` (`AP_AHRS/AP_AHRS.h:1001`). -/
  quat : Quaternion.State := Quaternion.init_void
  /-- `bool quat_ok` of `AP_AHRS::(unnamed struct at AP_AHRS/AP_AHRS.h:983:5)` (`AP_AHRS/AP_AHRS.h:1002`). -/
  quat_ok : Bool := false
  /-- `Location location` of `AP_AHRS::(unnamed struct at AP_AHRS/AP_AHRS.h:983:5)` (`AP_AHRS/AP_AHRS.h:1003`). -/
  location : Location.State := {}
  /-- `bool location_ok` of `AP_AHRS::(unnamed struct at AP_AHRS/AP_AHRS.h:983:5)` (`AP_AHRS/AP_AHRS.h:1004`). -/
  location_ok : Bool := false
  /-- `Vector2f ground_speed_vec` of `AP_AHRS::(unnamed struct at AP_AHRS/AP_AHRS.h:983:5)` (`AP_AHRS/AP_AHRS.h:1005`). -/
  ground_speed_vec : Vector2f.State := {}
  /-- `float ground_speed` of `AP_AHRS::(unnamed struct at AP_AHRS/AP_AHRS.h:983:5)` (`AP_AHRS/AP_AHRS.h:1006`). -/
  ground_speed : Binary32 := (Binary32.ofBits 0x00000000 /- 0.0 -/)
  /-- `bool corrected_dv_valid` of `AP_AHRS::(unnamed struct at AP_AHRS/AP_AHRS.h:983:5)` (`AP_AHRS/AP_AHRS.h:1007`). -/
  corrected_dv_valid : Bool := false
  /-- `Vector3f corrected_dv` of `AP_AHRS::(unnamed struct at AP_AHRS/AP_AHRS.h:983:5)` (`AP_AHRS/AP_AHRS.h:1008`). -/
  corrected_dv : Vector3f.State := {}
  /-- `float corrected_dv_dt` of `AP_AHRS::(unnamed struct at AP_AHRS/AP_AHRS.h:983:5)` (`AP_AHRS/AP_AHRS.h:1009`). -/
  corrected_dv_dt : Binary32 := (Binary32.ofBits 0x00000000 /- 0.0 -/)
  /-- `Location origin` of `AP_AHRS::(unnamed struct at AP_AHRS/AP_AHRS.h:983:5)` (`AP_AHRS/AP_AHRS.h:1010`). -/
  origin : Location.State := {}
  /-- `bool origin_ok` of `AP_AHRS::(unnamed struct at AP_AHRS/AP_AHRS.h:983:5)` (`AP_AHRS/AP_AHRS.h:1011`). -/
  origin_ok : Bool := false
  /-- `Vector3f velocity_NED` of `AP_AHRS::(unnamed struct at AP_AHRS/AP_AHRS.h:983:5)` (`AP_AHRS/AP_AHRS.h:1012`). -/
  velocity_NED : Vector3f.State := {}
  /-- `bool velocity_NED_ok` of `AP_AHRS::(unnamed struct at AP_AHRS/AP_AHRS.h:983:5)` (`AP_AHRS/AP_AHRS.h:1013`). -/
  velocity_NED_ok : Bool := false
deriving Inhabited

/-- C++ `struct AP_AHRS::(unnamed struct at AP_AHRS/AP_AHRS.h:1051:5)`, `AP_AHRS/AP_AHRS.h:1051-1054`. -/
structure backends_and_estimates_t where
  /-- `AP_AHRS_Backend & backend` of `AP_AHRS::(unnamed struct at AP_AHRS/AP_AHRS.h:1051:5)` (`AP_AHRS/AP_AHRS.h:1052`). -/
  backend : WPtr := WPtr.null
  /-- `AP_AHRS_Backend::Estimates & estimates` of `AP_AHRS::(unnamed struct at AP_AHRS/AP_AHRS.h:1051:5)` (`AP_AHRS/AP_AHRS.h:1053`). -/
  estimates : WPtr := WPtr.null
deriving Inhabited

end AP_AHRS

namespace AP_AHRS_Backend.Estimates

/-- State of C++ `AP_AHRS_Backend::Estimates` (`AP_AHRS/AP_AHRS_Backend.h:73-283`): its data members. -/
structure State where
  /-- `bool healthy` of `AP_AHRS_Backend::Estimates` (`AP_AHRS/AP_AHRS_Backend.h:82`). -/
  healthy : Bool := false
  /-- `bool initialised` of `AP_AHRS_Backend::Estimates` (`AP_AHRS/AP_AHRS_Backend.h:85`). -/
  initialised : Bool := false
  /-- `uint16_t filter_faults` of `AP_AHRS_Backend::Estimates` (`AP_AHRS/AP_AHRS_Backend.h:90`). -/
  filter_faults : UInt16 := (0 : UInt16)
  /-- `uint8_t primary_gyro` of `AP_AHRS_Backend::Estimates` (`AP_AHRS/AP_AHRS_Backend.h:93`). -/
  primary_gyro : UInt8 := (0 : UInt8)
  /-- `bool attitude_valid` of `AP_AHRS_Backend::Estimates` (`AP_AHRS/AP_AHRS_Backend.h:97`). -/
  attitude_valid : Bool := false
  /-- `float roll_rad` of `AP_AHRS_Backend::Estimates` (`AP_AHRS/AP_AHRS_Backend.h:98`). -/
  roll_rad : Binary32 := (Binary32.ofBits 0x00000000 /- 0.0 -/)
  /-- `float pitch_rad` of `AP_AHRS_Backend::Estimates` (`AP_AHRS/AP_AHRS_Backend.h:99`). -/
  pitch_rad : Binary32 := (Binary32.ofBits 0x00000000 /- 0.0 -/)
  /-- `float yaw_rad` of `AP_AHRS_Backend::Estimates` (`AP_AHRS/AP_AHRS_Backend.h:100`). -/
  yaw_rad : Binary32 := (Binary32.ofBits 0x00000000 /- 0.0 -/)
  /-- `Matrix3f dcm_matrix` of `AP_AHRS_Backend::Estimates` (`AP_AHRS/AP_AHRS_Backend.h:101`). -/
  dcm_matrix : Matrix3f.State := Matrix3f.init_void
  /-- `Quaternion quaternion` of `AP_AHRS_Backend::Estimates` (`AP_AHRS/AP_AHRS_Backend.h:102`). -/
  quaternion : Quaternion.State := Quaternion.init_void
  /-- `uint16_t attitude_reset_count` of `AP_AHRS_Backend::Estimates` (`AP_AHRS/AP_AHRS_Backend.h:103`). -/
  attitude_reset_count : UInt16 := (0 : UInt16)
  /-- `uint16_t yaw_reset_count` of `AP_AHRS_Backend::Estimates` (`AP_AHRS/AP_AHRS_Backend.h:104`). -/
  yaw_reset_count : UInt16 := (0 : UInt16)
  /-- `bool is_vibration_affected` of `AP_AHRS_Backend::Estimates` (`AP_AHRS/AP_AHRS_Backend.h:107`). -/
  is_vibration_affected : Bool := false
  /-- `Vector3f gyro_estimate` of `AP_AHRS_Backend::Estimates` (`AP_AHRS/AP_AHRS_Backend.h:118`). -/
  gyro_estimate : Vector3f.State := {}
  /-- `Vector3f gyro_drift` of `AP_AHRS_Backend::Estimates` (`AP_AHRS/AP_AHRS_Backend.h:119`). -/
  gyro_drift : Vector3f.State := {}
  /-- `uint8_t primary_accel` of `AP_AHRS_Backend::Estimates` (`AP_AHRS/AP_AHRS_Backend.h:121`). -/
  primary_accel : UInt8 := (0 : UInt8)
  /-- `Vector3f accel_ef` of `AP_AHRS_Backend::Estimates` (`AP_AHRS/AP_AHRS_Backend.h:123`). -/
  accel_ef : Vector3f.State := {}
  /-- `Vector3f accel_bias` of `AP_AHRS_Backend::Estimates` (`AP_AHRS/AP_AHRS_Backend.h:124`). -/
  accel_bias : Vector3f.State := {}
  /-- `Vector3f velocity_NED` of `AP_AHRS_Backend::Estimates` (`AP_AHRS/AP_AHRS_Backend.h:127`). -/
  velocity_NED : Vector3f.State := {}
  /-- `bool velocity_NED_valid` of `AP_AHRS_Backend::Estimates` (`AP_AHRS/AP_AHRS_Backend.h:128`). -/
  velocity_NED_valid : Bool := false
  /-- `bool have_velocity_source` of `AP_AHRS_Backend::Estimates` (`AP_AHRS/AP_AHRS_Backend.h:134`). -/
  have_velocity_source : Bool := false
  /-- `Vector2f velocity_NE` of `AP_AHRS_Backend::Estimates` (`AP_AHRS/AP_AHRS_Backend.h:144`). -/
  velocity_NE : Vector2f.State := {}
  /-- `float vert_pos_rate_D` of `AP_AHRS_Backend::Estimates` (`AP_AHRS/AP_AHRS_Backend.h:152`). -/
  vert_pos_rate_D : Binary32 := (Binary32.ofBits 0x00000000 /- 0.0 -/)
  /-- `bool vert_pos_rate_D_valid` of `AP_AHRS_Backend::Estimates` (`AP_AHRS/AP_AHRS_Backend.h:153`). -/
  vert_pos_rate_D_valid : Bool := false
  /-- `Location location` of `AP_AHRS_Backend::Estimates` (`AP_AHRS/AP_AHRS_Backend.h:171`). -/
  location : Location.State := {}
  /-- `bool location_valid` of `AP_AHRS_Backend::Estimates` (`AP_AHRS/AP_AHRS_Backend.h:172`). -/
  location_valid : Bool := false
  /-- `bool provides_common_origin` of `AP_AHRS_Backend::Estimates` (`AP_AHRS/AP_AHRS_Backend.h:182`). -/
  provides_common_origin : Bool := false
  /-- `Vector2p position_NE` of `AP_AHRS_Backend::Estimates` (`AP_AHRS/AP_AHRS_Backend.h:185`). -/
  position_NE : Vector2p.State := {}
  /-- `bool position_NE_valid` of `AP_AHRS_Backend::Estimates` (`AP_AHRS/AP_AHRS_Backend.h:186`). -/
  position_NE_valid : Bool := false
  /-- `uint16_t position_NE_reset_count` of `AP_AHRS_Backend::Estimates` (`AP_AHRS/AP_AHRS_Backend.h:187`). -/
  position_NE_reset_count : UInt16 := (0 : UInt16)
  /-- `postype_t position_D` of `AP_AHRS_Backend::Estimates` (`AP_AHRS/AP_AHRS_Backend.h:189`). -/
  position_D : Binary64 := (Binary64.ofBits 0x0000000000000000 /- 0.0 -/)
  /-- `bool position_D_valid` of `AP_AHRS_Backend::Estimates` (`AP_AHRS/AP_AHRS_Backend.h:190`). -/
  position_D_valid : Bool := false
  /-- `uint16_t position_D_reset_count` of `AP_AHRS_Backend::Estimates` (`AP_AHRS/AP_AHRS_Backend.h:191`). -/
  position_D_reset_count : UInt16 := (0 : UInt16)
  /-- `Vector3f wind` of `AP_AHRS_Backend::Estimates` (`AP_AHRS/AP_AHRS_Backend.h:202`). -/
  wind : Vector3f.State := {}
  /-- `bool wind_valid` of `AP_AHRS_Backend::Estimates` (`AP_AHRS/AP_AHRS_Backend.h:203`). -/
  wind_valid : Bool := false
  /-- `float airspeed_EAS` of `AP_AHRS_Backend::Estimates` (`AP_AHRS/AP_AHRS_Backend.h:209`). -/
  airspeed_EAS : Binary32 := (Binary32.ofBits 0x00000000 /- 0.0 -/)
  /-- `bool airspeed_EAS_ok` of `AP_AHRS_Backend::Estimates` (`AP_AHRS/AP_AHRS_Backend.h:210`). -/
  airspeed_EAS_ok : Bool := false
  /-- `AirspeedEstimateType airspeed_estimate_type` of `AP_AHRS_Backend::Estimates` (`AP_AHRS/AP_AHRS_Backend.h:211`). -/
  airspeed_estimate_type : AP_AHRS_Backend.AirspeedEstimateType := AP_AHRS_Backend.AirspeedEstimateType.NO_NEW_ESTIMATE
  /-- `float airspeed_TAS` of `AP_AHRS_Backend::Estimates` (`AP_AHRS/AP_AHRS_Backend.h:212`). -/
  airspeed_TAS : Binary32 := (Binary32.ofBits 0x00000000 /- 0.0 -/)
  /-- `bool airspeed_TAS_ok` of `AP_AHRS_Backend::Estimates` (`AP_AHRS/AP_AHRS_Backend.h:213`). -/
  airspeed_TAS_ok : Bool := false
  /-- `bool configured_to_use_gps` of `AP_AHRS_Backend::Estimates` (`AP_AHRS/AP_AHRS_Backend.h:224`). -/
  configured_to_use_gps : Bool := false
  /-- `bool configured_to_use_gps_for_pos_XY` of `AP_AHRS_Backend::Estimates` (`AP_AHRS/AP_AHRS_Backend.h:229`). -/
  configured_to_use_gps_for_pos_XY : Bool := false
  /-- `bool using_extnav_for_yaw` of `AP_AHRS_Backend::Estimates` (`AP_AHRS/AP_AHRS_Backend.h:235`). -/
  using_extnav_for_yaw : Bool := false
  /-- `bool using_noncompass_for_yaw` of `AP_AHRS_Backend::Estimates` (`AP_AHRS/AP_AHRS_Backend.h:239`). -/
  using_noncompass_for_yaw : Bool := false
  /-- `nav_filter_status filter_status` of `AP_AHRS_Backend::Estimates` (`AP_AHRS/AP_AHRS_Backend.h:252`). -/
  filter_status : UInt32 := (0 : UInt32)
  /-- `bool filter_status_valid` of `AP_AHRS_Backend::Estimates` (`AP_AHRS/AP_AHRS_Backend.h:253`). -/
  filter_status_valid : Bool := false
  /-- `float velVar` of `AP_AHRS_Backend::Estimates` (`AP_AHRS/AP_AHRS_Backend.h:260`). -/
  velVar : Binary32 := (Binary32.ofBits 0x00000000 /- 0.0 -/)
  /-- `float posVar` of `AP_AHRS_Backend::Estimates` (`AP_AHRS/AP_AHRS_Backend.h:260`). -/
  posVar : Binary32 := (Binary32.ofBits 0x00000000 /- 0.0 -/)
  /-- `float hgtVar` of `AP_AHRS_Backend::Estimates` (`AP_AHRS/AP_AHRS_Backend.h:260`). -/
  hgtVar : Binary32 := (Binary32.ofBits 0x00000000 /- 0.0 -/)
  /-- `float tasVar` of `AP_AHRS_Backend::Estimates` (`AP_AHRS/AP_AHRS_Backend.h:260`). -/
  tasVar : Binary32 := (Binary32.ofBits 0x00000000 /- 0.0 -/)
  /-- `Vector3f magVar` of `AP_AHRS_Backend::Estimates` (`AP_AHRS/AP_AHRS_Backend.h:261`). -/
  magVar : Vector3f.State := {}
  /-- `bool variances_valid` of `AP_AHRS_Backend::Estimates` (`AP_AHRS/AP_AHRS_Backend.h:262`). -/
  variances_valid : Bool := false
  /-- `float terrain_alt_variance` of `AP_AHRS_Backend::Estimates` (`AP_AHRS/AP_AHRS_Backend.h:264`). -/
  terrain_alt_variance : Binary32 := (Binary32.ofBits 0x00000000 /- 0.0 -/)
  /-- `bool terrain_alt_variance_valid` of `AP_AHRS_Backend::Estimates` (`AP_AHRS/AP_AHRS_Backend.h:265`). -/
  terrain_alt_variance_valid : Bool := false
  /-- `float control_ground_speed_limit_ms` of `AP_AHRS_Backend::Estimates` (`AP_AHRS/AP_AHRS_Backend.h:270`). -/
  control_ground_speed_limit_ms : Binary32 := (Binary32.ofBits 0x00000000 /- 0.0 -/)
  /-- `float control_gain_scaler_XY` of `AP_AHRS_Backend::Estimates` (`AP_AHRS/AP_AHRS_Backend.h:272`). -/
  control_gain_scaler_XY : Binary32 := (Binary32.ofBits 0x00000000 /- 0.0 -/)
  /-- `float control_gain_scaler_Z` of `AP_AHRS_Backend::Estimates` (`AP_AHRS/AP_AHRS_Backend.h:273`). -/
  control_gain_scaler_Z : Binary32 := (Binary32.ofBits 0x00000000 /- 0.0 -/)
  /-- `float control_height_limit_m` of `AP_AHRS_Backend::Estimates` (`AP_AHRS/AP_AHRS_Backend.h:277`). -/
  control_height_limit_m : Binary32 := (Binary32.ofBits 0x00000000 /- 0.0 -/)
  /-- `bool control_height_limit_valid` of `AP_AHRS_Backend::Estimates` (`AP_AHRS/AP_AHRS_Backend.h:278`). -/
  control_height_limit_valid : Bool := false
  /-- `bool hagl_valid` of `AP_AHRS_Backend::Estimates` (`AP_AHRS/AP_AHRS_Backend.h:281`). -/
  hagl_valid : Bool := false
  /-- `float hagl` of `AP_AHRS_Backend::Estimates` (`AP_AHRS/AP_AHRS_Backend.h:282`). -/
  hagl : Binary32 := (Binary32.ofBits 0x00000000 /- 0.0 -/)
deriving Inhabited

end AP_AHRS_Backend.Estimates

namespace AP_AHRS_ResetCounter_unsigned_short

/-- State of C++ `AP_AHRS_ResetCounter<unsigned short>` (`AP_AHRS/AP_AHRS_Backend.h:441-467`): its data members. -/
structure State where
  /-- `unsigned short last_key` of `AP_AHRS_ResetCounter<unsigned short>` (`AP_AHRS/AP_AHRS_Backend.h:465`). -/
  last_key : UInt16 := (0 : UInt16)
  /-- `uint16_t reset_count` of `AP_AHRS_ResetCounter<unsigned short>` (`AP_AHRS/AP_AHRS_Backend.h:466`). -/
  reset_count : UInt16 := (0 : UInt16)
deriving Inhabited

end AP_AHRS_ResetCounter_unsigned_short

namespace AP_AHRS_DCM

/-- State of C++ `AP_AHRS_DCM` (`AP_AHRS/AP_AHRS_DCM.h:31-250`): its data members; base classes flattened, base first: `AP_AHRS_Backend`. -/
structure State where
  /-- `Vector3f _wind` of `AP_AHRS_Backend` (`AP_AHRS/AP_AHRS_Backend.h:391`). -/
  _wind : Vector3f.State := {}
  /-- `float _last_airspeed_TAS` of `AP_AHRS_Backend` (`AP_AHRS/AP_AHRS_Backend.h:395`). -/
  _last_airspeed_TAS : Binary32 := (Binary32.ofBits 0x00000000 /- 0.0 -/)
  /-- `Vector3f _last_fuse` of `AP_AHRS_Backend` (`AP_AHRS/AP_AHRS_Backend.h:430`). -/
  _last_fuse : Vector3f.State := {}
  /-- `Vector3f _last_vel` of `AP_AHRS_Backend` (`AP_AHRS/AP_AHRS_Backend.h:431`). -/
  _last_vel : Vector3f.State := {}
  /-- `uint32_t _last_wind_time` of `AP_AHRS_Backend` (`AP_AHRS/AP_AHRS_Backend.h:432`). -/
  _last_wind_time : UInt32 := (0 : UInt32)
  /-- `uint32_t _last_wind_estimate_ms` of `AP_AHRS_Backend` (`AP_AHRS/AP_AHRS_Backend.h:435`). -/
  _last_wind_estimate_ms : UInt32 := (0 : UInt32)
  /-- `Vector3f _accel_ef` of `AP_AHRS_DCM` (`AP_AHRS/AP_AHRS_DCM.h:126`). -/
  _accel_ef : Vector3f.State := {}
  /-- `Matrix3f _dcm_matrix` of `AP_AHRS_DCM` (`AP_AHRS/AP_AHRS_DCM.h:148`). -/
  _dcm_matrix : Matrix3f.State := Matrix3f.init_void
  /-- `Matrix3f _body_dcm_matrix` of `AP_AHRS_DCM` (`AP_AHRS/AP_AHRS_DCM.h:151`). -/
  _body_dcm_matrix : Matrix3f.State := Matrix3f.init_void
  /-- `float roll` of `AP_AHRS_DCM` (`AP_AHRS/AP_AHRS_DCM.h:155`). -/
  roll : Binary32 := (Binary32.ofBits 0x00000000 /- 0.0 -/)
  /-- `float pitch` of `AP_AHRS_DCM` (`AP_AHRS/AP_AHRS_DCM.h:156`). -/
  pitch : Binary32 := (Binary32.ofBits 0x00000000 /- 0.0 -/)
  /-- `float yaw` of `AP_AHRS_DCM` (`AP_AHRS/AP_AHRS_DCM.h:157`). -/
  yaw : Binary32 := (Binary32.ofBits 0x00000000 /- 0.0 -/)
  /-- `Vector3f _omega_P` of `AP_AHRS_DCM` (`AP_AHRS/AP_AHRS_DCM.h:159`). -/
  _omega_P : Vector3f.State := {}
  /-- `Vector3f _omega_yaw_P` of `AP_AHRS_DCM` (`AP_AHRS/AP_AHRS_DCM.h:160`). -/
  _omega_yaw_P : Vector3f.State := {}
  /-- `Vector3f _omega_I` of `AP_AHRS_DCM` (`AP_AHRS/AP_AHRS_DCM.h:161`). -/
  _omega_I : Vector3f.State := {}
  /-- `Vector3f _omega_I_sum` of `AP_AHRS_DCM` (`AP_AHRS/AP_AHRS_DCM.h:162`). -/
  _omega_I_sum : Vector3f.State := {}
  /-- `float _omega_I_sum_time` of `AP_AHRS_DCM` (`AP_AHRS/AP_AHRS_DCM.h:163`). -/
  _omega_I_sum_time : Binary32 := (Binary32.ofBits 0x00000000 /- 0.0 -/)
  /-- `Vector3f _omega` of `AP_AHRS_DCM` (`AP_AHRS/AP_AHRS_DCM.h:164`). -/
  _omega : Vector3f.State := {}
  /-- `bool have_initial_yaw` of `AP_AHRS_DCM` (`AP_AHRS/AP_AHRS_DCM.h:166`). -/
  have_initial_yaw : Bool := false
  /-- `Vector3f _ra_delay_buffer[3]` of `AP_AHRS_DCM` (`AP_AHRS/AP_AHRS_DCM.h:170`). -/
  _ra_delay_buffer : Array Vector3f.State := Array.replicate 3 {}
  /-- `float _renorm_val_sum` of `AP_AHRS_DCM` (`AP_AHRS/AP_AHRS_DCM.h:186`). -/
  _renorm_val_sum : Binary32 := (Binary32.ofBits 0x00000000 /- 0.0 -/)
  /-- `uint16_t _renorm_val_count` of `AP_AHRS_DCM` (`AP_AHRS/AP_AHRS_DCM.h:187`). -/
  _renorm_val_count : UInt16 := (0 : UInt16)
  /-- `float _error_rp` of `AP_AHRS_DCM` (`AP_AHRS/AP_AHRS_DCM.h:188`). -/
  _error_rp : Binary32 := (Binary32.ofBits 0x3f800000 /- 1.0f -/)
  /-- `float _error_yaw` of `AP_AHRS_DCM` (`AP_AHRS/AP_AHRS_DCM.h:189`). -/
  _error_yaw : Binary32 := (Binary32.ofBits 0x3f800000 /- 1.0f -/)
  /-- `uint32_t _compass_last_update` of `AP_AHRS_DCM` (`AP_AHRS/AP_AHRS_DCM.h:192`). -/
  _compass_last_update : UInt32 := (0 : UInt32)
  /-- `uint32_t _gps_last_update` of `AP_AHRS_DCM` (`AP_AHRS/AP_AHRS_DCM.h:195`). -/
  _gps_last_update : UInt32 := (0 : UInt32)
  /-- `uint32_t _last_wind_gps_ms` of `AP_AHRS_DCM` (`AP_AHRS/AP_AHRS_DCM.h:198`). -/
  _last_wind_gps_ms : UInt32 := (0 : UInt32)
  /-- `Vector3f _ra_sum[3]` of `AP_AHRS_DCM` (`AP_AHRS/AP_AHRS_DCM.h:201`). -/
  _ra_sum : Array Vector3f.State := Array.replicate 3 {}
  /-- `Vector3f _last_velocity` of `AP_AHRS_DCM` (`AP_AHRS/AP_AHRS_DCM.h:202`). -/
  _last_velocity : Vector3f.State := {}
  /-- `float _ra_deltat` of `AP_AHRS_DCM` (`AP_AHRS/AP_AHRS_DCM.h:203`). -/
  _ra_deltat : Binary32 := (Binary32.ofBits 0x00000000 /- 0.0 -/)
  /-- `uint32_t _ra_sum_start` of `AP_AHRS_DCM` (`AP_AHRS/AP_AHRS_DCM.h:204`). -/
  _ra_sum_start : UInt32 := (0 : UInt32)
  /-- `uint8_t _active_accel_instance` of `AP_AHRS_DCM` (`AP_AHRS/AP_AHRS_DCM.h:207`). -/
  _active_accel_instance : UInt8 := (0 : UInt8)
  /-- `float _last_declination` of `AP_AHRS_DCM` (`AP_AHRS/AP_AHRS_DCM.h:210`). -/
  _last_declination : Binary32 := (Binary32.ofBits 0x00000000 /- 0.0 -/)
  /-- `Vector2f _mag_earth` of `AP_AHRS_DCM` (`AP_AHRS/AP_AHRS_DCM.h:211`). -/
  _mag_earth : Vector2f.State := Vector2f.init_float2 (Binary32.ofBits 0x3f800000 /- 1 -/) (Binary32.ofBits 0x00000000 /- 0 -/)
  /-- `bool _have_gps_lock` of `AP_AHRS_DCM` (`AP_AHRS/AP_AHRS_DCM.h:214`). -/
  _have_gps_lock : Bool := false
  /-- `int32_t _last_lat` of `AP_AHRS_DCM` (`AP_AHRS/AP_AHRS_DCM.h:217`). -/
  _last_lat : Int32 := (0 : Int32)
  /-- `int32_t _last_lng` of `AP_AHRS_DCM` (`AP_AHRS/AP_AHRS_DCM.h:218`). -/
  _last_lng : Int32 := (0 : Int32)
  /-- `uint32_t _last_pos_ms` of `AP_AHRS_DCM` (`AP_AHRS/AP_AHRS_DCM.h:219`). -/
  _last_pos_ms : UInt32 := (0 : UInt32)
  /-- `float _position_offset_north` of `AP_AHRS_DCM` (`AP_AHRS/AP_AHRS_DCM.h:222`). -/
  _position_offset_north : Binary32 := (Binary32.ofBits 0x00000000 /- 0.0 -/)
  /-- `float _position_offset_east` of `AP_AHRS_DCM` (`AP_AHRS/AP_AHRS_DCM.h:223`). -/
  _position_offset_east : Binary32 := (Binary32.ofBits 0x00000000 /- 0.0 -/)
  /-- `bool _have_position` of `AP_AHRS_DCM` (`AP_AHRS/AP_AHRS_DCM.h:226`). -/
  _have_position : Bool := false
  /-- `uint32_t _last_consistent_heading` of `AP_AHRS_DCM` (`AP_AHRS/AP_AHRS_DCM.h:228`). -/
  _last_consistent_heading : UInt32 := (0 : UInt32)
  /-- `uint32_t _last_failure_ms` of `AP_AHRS_DCM` (`AP_AHRS/AP_AHRS_DCM.h:231`). -/
  _last_failure_ms : UInt32 := (0 : UInt32)
  /-- `uint32_t _last_startup_ms` of `AP_AHRS_DCM` (`AP_AHRS/AP_AHRS_DCM.h:234`). -/
  _last_startup_ms : UInt32 := (0 : UInt32)
  /-- `Location last_origin` of `AP_AHRS_DCM` (`AP_AHRS/AP_AHRS_DCM.h:237`). -/
  last_origin : Location.State := {}
  /-- `Vector2f _lp` of `AP_AHRS_DCM` (`AP_AHRS/AP_AHRS_DCM.h:241`). -/
  _lp : Vector2f.State := {}
  /-- `Vector2f _hp` of `AP_AHRS_DCM` (`AP_AHRS/AP_AHRS_DCM.h:242`). -/
  _hp : Vector2f.State := {}
  /-- `Vector2f _lastGndVelADS` of `AP_AHRS_DCM` (`AP_AHRS/AP_AHRS_DCM.h:243`). -/
  _lastGndVelADS : Vector2f.State := {}
  /-- `float _sin_yaw` of `AP_AHRS_DCM` (`AP_AHRS/AP_AHRS_DCM.h:246`). -/
  _sin_yaw : Binary32 := (Binary32.ofBits 0x00000000 /- 0.0 -/)
  /-- `float _cos_yaw` of `AP_AHRS_DCM` (`AP_AHRS/AP_AHRS_DCM.h:247`). -/
  _cos_yaw : Binary32 := (Binary32.ofBits 0x00000000 /- 0.0 -/)
  /-- `uint32_t last_log_ms` of `AP_AHRS_DCM` (`AP_AHRS/AP_AHRS_DCM.h:249`). -/
  last_log_ms : UInt32 := (0 : UInt32)
deriving Inhabited

/-- Values C++ `AP_AHRS_DCM` reads from objects outside the translation (--boundary): one field per distinct read, in first-use order. -/
structure Inputs where
  /-- `hal.util.was_watchdog_reset()` (first read at `AP_AHRS/AP_AHRS_DCM.cpp:362`). -/
  was_watchdog_reset : Bool := false
  /-- `hal.util.persistent_data.roll_rad` (first read at `AP_AHRS/AP_AHRS_DCM.cpp:364`). -/
  persistent_data_roll_rad : Binary32 := (Binary32.ofBits 0x00000000 /- 0.0 -/)
  /-- `hal.util.persistent_data.pitch_rad` (first read at `AP_AHRS/AP_AHRS_DCM.cpp:365`). -/
  persistent_data_pitch_rad : Binary32 := (Binary32.ofBits 0x00000000 /- 0.0 -/)
  /-- `hal.util.persistent_data.yaw_rad` (first read at `AP_AHRS/AP_AHRS_DCM.cpp:366`). -/
  persistent_data_yaw_rad : Binary32 := (Binary32.ofBits 0x00000000 /- 0.0 -/)
  /-- `hal.util.get_soft_armed()` (first read at `AP_AHRS/AP_AHRS_DCM.cpp:606`). -/
  get_soft_armed : Bool := false
deriving Inhabited

end AP_AHRS_DCM

namespace AP_AHRS_ResetCounter_signed_char

/-- State of C++ `AP_AHRS_ResetCounter<signed char>` (`AP_AHRS/AP_AHRS_Backend.h:441-467`): its data members. -/
structure State where
  /-- `signed char last_key` of `AP_AHRS_ResetCounter<signed char>` (`AP_AHRS/AP_AHRS_Backend.h:465`). -/
  last_key : Int8 := (0 : Int8)
  /-- `uint16_t reset_count` of `AP_AHRS_ResetCounter<signed char>` (`AP_AHRS/AP_AHRS_Backend.h:466`). -/
  reset_count : UInt16 := (0 : UInt16)
deriving Inhabited

end AP_AHRS_ResetCounter_signed_char

namespace AP_AHRS_NavEKF3

/-- State of C++ `AP_AHRS_NavEKF3` (`AP_AHRS/AP_AHRS_NavEKF3.h:29-102`): its data members; base classes flattened, base first: `AP_AHRS_Backend`. -/
structure State where
  /-- `Vector3f _wind` of `AP_AHRS_Backend` (`AP_AHRS/AP_AHRS_Backend.h:391`). -/
  _wind : Vector3f.State := {}
  /-- `float _last_airspeed_TAS` of `AP_AHRS_Backend` (`AP_AHRS/AP_AHRS_Backend.h:395`). -/
  _last_airspeed_TAS : Binary32 := (Binary32.ofBits 0x00000000 /- 0.0 -/)
  /-- `Vector3f _last_fuse` of `AP_AHRS_Backend` (`AP_AHRS/AP_AHRS_Backend.h:430`). -/
  _last_fuse : Vector3f.State := {}
  /-- `Vector3f _last_vel` of `AP_AHRS_Backend` (`AP_AHRS/AP_AHRS_Backend.h:431`). -/
  _last_vel : Vector3f.State := {}
  /-- `uint32_t _last_wind_time` of `AP_AHRS_Backend` (`AP_AHRS/AP_AHRS_Backend.h:432`). -/
  _last_wind_time : UInt32 := (0 : UInt32)
  /-- `uint32_t _last_wind_estimate_ms` of `AP_AHRS_Backend` (`AP_AHRS/AP_AHRS_Backend.h:435`). -/
  _last_wind_estimate_ms : UInt32 := (0 : UInt32)
  /-- `bool started` of `AP_AHRS_NavEKF3` (`AP_AHRS/AP_AHRS_NavEKF3.h:93`). -/
  started : Bool := false
  /-- `uint32_t start_time_ms` of `AP_AHRS_NavEKF3` (`AP_AHRS/AP_AHRS_NavEKF3.h:94`). -/
  start_time_ms : UInt32 := (0 : UInt32)
  /-- `AP_AHRS_ResetCounter<int8_t> attitude_reset_tracker` of `AP_AHRS_NavEKF3` (`AP_AHRS/AP_AHRS_NavEKF3.h:97`). -/
  attitude_reset_tracker : AP_AHRS_ResetCounter_signed_char.State := {}
  /-- `AP_AHRS_ResetCounter<uint16_t> yaw_reset_tracker` of `AP_AHRS_NavEKF3` (`AP_AHRS/AP_AHRS_NavEKF3.h:99`). -/
  yaw_reset_tracker : AP_AHRS_ResetCounter_unsigned_short.State := {}
  /-- `AP_AHRS_ResetCounter<uint16_t> position_NE_reset_tracker` of `AP_AHRS_NavEKF3` (`AP_AHRS/AP_AHRS_NavEKF3.h:100`). -/
  position_NE_reset_tracker : AP_AHRS_ResetCounter_unsigned_short.State := {}
  /-- `AP_AHRS_ResetCounter<uint16_t> position_D_reset_tracker` of `AP_AHRS_NavEKF3` (`AP_AHRS/AP_AHRS_NavEKF3.h:101`). -/
  position_D_reset_tracker : AP_AHRS_ResetCounter_unsigned_short.State := {}
deriving Inhabited

/-- C++ `AP_AHRS_Backend::AP_AHRS_Backend()`, `AP_AHRS/AP_AHRS_Backend.h:48` (a member of `AP_AHRS_Backend`, translated for `AP_AHRS_NavEKF3`). -/
def AP_AHRS_Backend.init (s : State) : State := Id.run do
  let mut s := s
  s := { s with _wind := Vector3f.init_void }
  s := { s with _last_fuse := Vector3f.init_void }
  s := { s with _last_vel := Vector3f.init_void }
  return s

/-- C++ `AP_AHRS_NavEKF3::AP_AHRS_NavEKF3()`, `AP_AHRS/AP_AHRS_NavEKF3.h:34`. -/
def init : State := Id.run do
  let mut s : State := {}
  s := AP_AHRS_Backend.init s
  return s

end AP_AHRS_NavEKF3

namespace AP_AHRS

/-- State of C++ `AP_AHRS` (`AP_AHRS/AP_AHRS.h:43-1134`): its data members. -/
structure State where
  /-- `AP_AHRS_NavEKF3 ekf3` of `AP_AHRS` (`AP_AHRS/AP_AHRS.h:77`). -/
  ekf3 : AP_AHRS_NavEKF3.State := AP_AHRS_NavEKF3.init
  /-- `float rpy_deg[3]` of `AP_AHRS` (`AP_AHRS/AP_AHRS.h:658`). -/
  rpy_deg : Array Binary32 := Array.replicate 3 (Binary32.ofBits 0x00000000 /- 0.0 -/)
  /-- `int32_t roll_sensor` of `AP_AHRS` (`AP_AHRS/AP_AHRS.h:661`). -/
  roll_sensor : Int32 := (0 : Int32)
  /-- `int32_t pitch_sensor` of `AP_AHRS` (`AP_AHRS/AP_AHRS.h:662`). -/
  pitch_sensor : Int32 := (0 : Int32)
  /-- `int32_t yaw_sensor` of `AP_AHRS` (`AP_AHRS/AP_AHRS.h:663`). -/
  yaw_sensor : Int32 := (0 : Int32)
  /-- `float roll` of `AP_AHRS` (`AP_AHRS/AP_AHRS.h:767`). -/
  roll : Binary32 := (Binary32.ofBits 0x00000000 /- 0.0 -/)
  /-- `float pitch` of `AP_AHRS` (`AP_AHRS/AP_AHRS.h:768`). -/
  pitch : Binary32 := (Binary32.ofBits 0x00000000 /- 0.0 -/)
  /-- `float yaw` of `AP_AHRS` (`AP_AHRS/AP_AHRS.h:769`). -/
  yaw : Binary32 := (Binary32.ofBits 0x00000000 /- 0.0 -/)
  /-- `AP_AHRS_View * _view` of `AP_AHRS` (`AP_AHRS/AP_AHRS.h:772`). -/
  _view : WPtr := WPtr.null
  /-- `VehicleClass _vehicle_class` of `AP_AHRS` (`AP_AHRS/AP_AHRS.h:780`). -/
  _vehicle_class : AP_AHRS.VehicleClass := AP_AHRS.VehicleClass.UNKNOWN
  /-- `AP_Int8 _wind_max` of `AP_AHRS` (`AP_AHRS/AP_AHRS.h:788`). -/
  _wind_max : AP_ParamT_signed_char_1.State := {}
  /-- `AP_Int8 _board_orientation` of `AP_AHRS` (`AP_AHRS/AP_AHRS.h:789`). -/
  _board_orientation : AP_ParamT_signed_char_1.State := {}
  /-- `AP_Enum<EKFType> _ekf_type` of `AP_AHRS` (`AP_AHRS/AP_AHRS.h:790`). -/
  _ekf_type : AP_Enum_AP_AHRS_EKFType.State := {}
  /-- `AP_Float _kp_yaw` of `AP_AHRS` (`AP_AHRS/AP_AHRS.h:796`). -/
  _kp_yaw : AP_ParamT_float_4.State := {}
  /-- `AP_Float _kp` of `AP_AHRS` (`AP_AHRS/AP_AHRS.h:797`). -/
  _kp : AP_ParamT_float_4.State := {}
  /-- `AP_Float gps_gain` of `AP_AHRS` (`AP_AHRS/AP_AHRS.h:798`). -/
  gps_gain : AP_ParamT_float_4.State := {}
  /-- `AP_Float beta` of `AP_AHRS` (`AP_AHRS/AP_AHRS.h:800`). -/
  beta : AP_ParamT_float_4.State := {}
  /-- `AP_Enum<GPSUse> _gps_use` of `AP_AHRS` (`AP_AHRS/AP_AHRS.h:802`). -/
  _gps_use : AP_Enum_GPSUse.State := {}
  /-- `AP_Int8 _gps_minsats` of `AP_AHRS` (`AP_AHRS/AP_AHRS.h:803`). -/
  _gps_minsats : AP_ParamT_signed_char_1.State := {}
  /-- `AP_Float _origin_lat` of `AP_AHRS` (`AP_AHRS/AP_AHRS.h:804`). -/
  _origin_lat : AP_ParamT_float_4.State := {}
  /-- `AP_Float _origin_lon` of `AP_AHRS` (`AP_AHRS/AP_AHRS.h:805`). -/
  _origin_lon : AP_ParamT_float_4.State := {}
  /-- `AP_Float _origin_alt` of `AP_AHRS` (`AP_AHRS/AP_AHRS.h:806`). -/
  _origin_alt : AP_ParamT_float_4.State := {}
  /-- `float _cos_roll` of `AP_AHRS` (`AP_AHRS/AP_AHRS.h:835`). -/
  _cos_roll : Binary32 := (Binary32.ofBits 0x3f800000 /- 1.0f -/)
  /-- `float _cos_pitch` of `AP_AHRS` (`AP_AHRS/AP_AHRS.h:836`). -/
  _cos_pitch : Binary32 := (Binary32.ofBits 0x3f800000 /- 1.0f -/)
  /-- `float _cos_yaw` of `AP_AHRS` (`AP_AHRS/AP_AHRS.h:837`). -/
  _cos_yaw : Binary32 := (Binary32.ofBits 0x3f800000 /- 1.0f -/)
  /-- `float _sin_roll` of `AP_AHRS` (`AP_AHRS/AP_AHRS.h:838`). -/
  _sin_roll : Binary32 := (Binary32.ofBits 0x00000000 /- 0.0 -/)
  /-- `float _sin_pitch` of `AP_AHRS` (`AP_AHRS/AP_AHRS.h:839`). -/
  _sin_pitch : Binary32 := (Binary32.ofBits 0x00000000 /- 0.0 -/)
  /-- `float _sin_yaw` of `AP_AHRS` (`AP_AHRS/AP_AHRS.h:840`). -/
  _sin_yaw : Binary32 := (Binary32.ofBits 0x00000000 /- 0.0 -/)
  /-- `uint8_t _ekf_flags` of `AP_AHRS` (`AP_AHRS/AP_AHRS.h:842`). -/
  _ekf_flags : UInt8 := (0 : UInt8)
  /-- `bool _checked_watchdog_home` of `AP_AHRS` (`AP_AHRS/AP_AHRS.h:848`). -/
  _checked_watchdog_home : Bool := false
  /-- `Location _home` of `AP_AHRS` (`AP_AHRS/AP_AHRS.h:849`). -/
  _home : Location.State := {}
  /-- `bool _home_is_set : 1` of `AP_AHRS` (`AP_AHRS/AP_AHRS.h:850`). -/
  _home_is_set : Bool := false
  /-- `bool _home_locked : 1` of `AP_AHRS` (`AP_AHRS/AP_AHRS.h:851`). -/
  _home_locked : Bool := false
  /-- `TriState terrainHgtStableState` of `AP_AHRS` (`AP_AHRS/AP_AHRS.h:860`). -/
  terrainHgtStableState : AP_AHRS.TriState := AP_AHRS.TriState.UNKNOWN
  /-- `float _AOA` of `AP_AHRS` (`AP_AHRS/AP_AHRS.h:865`). -/
  _AOA : Binary32 := (Binary32.ofBits 0x00000000 /- 0.0 -/)
  /-- `float _SSA` of `AP_AHRS` (`AP_AHRS/AP_AHRS.h:865`). -/
  _SSA : Binary32 := (Binary32.ofBits 0x00000000 /- 0.0 -/)
  /-- `uint32_t _last_AOA_update_ms` of `AP_AHRS` (`AP_AHRS/AP_AHRS.h:866`). -/
  _last_AOA_update_ms : UInt32 := (0 : UInt32)
  /-- `EKFType last_active_ekf_type` of `AP_AHRS` (`AP_AHRS/AP_AHRS.h:869`). -/
  last_active_ekf_type : AP_AHRS.EKFType := AP_AHRS.EKFType.DCM
  /-- `AP_Vector3f _trim` of `AP_AHRS` (`AP_AHRS/AP_AHRS.h:876`). -/
  _trim : AP_ParamV_Vector3_float_5.State := {}
  /-- `Vector3f _last_trim` of `AP_AHRS` (`AP_AHRS/AP_AHRS.h:879`). -/
  _last_trim : Vector3f.State := {}
  /-- `Matrix3f _rotation_autopilot_body_to_vehicle_body` of `AP_AHRS` (`AP_AHRS/AP_AHRS.h:881`). -/
  _rotation_autopilot_body_to_vehicle_body : Matrix3f.State := Matrix3f.init_void
  /-- `Matrix3f _rotation_vehicle_body_to_autopilot_body` of `AP_AHRS` (`AP_AHRS/AP_AHRS.h:882`). -/
  _rotation_vehicle_body_to_autopilot_body : Matrix3f.State := Matrix3f.init_void
  /-- `uint32_t last_orientation_update_ms` of `AP_AHRS` (`AP_AHRS/AP_AHRS.h:885`). -/
  last_orientation_update_ms : UInt32 := (0 : UInt32)
  /-- `bool takeoff_expected` of `AP_AHRS` (`AP_AHRS/AP_AHRS.h:897`). -/
  takeoff_expected : Bool := false
  /-- `uint32_t takeoff_expected_start_ms` of `AP_AHRS` (`AP_AHRS/AP_AHRS.h:898`). -/
  takeoff_expected_start_ms : UInt32 := (0 : UInt32)
  /-- `bool touchdown_expected` of `AP_AHRS` (`AP_AHRS/AP_AHRS.h:899`). -/
  touchdown_expected : Bool := false
  /-- `uint32_t touchdown_expected_start_ms` of `AP_AHRS` (`AP_AHRS/AP_AHRS.h:900`). -/
  touchdown_expected_start_ms : UInt32 := (0 : UInt32)
  /-- `bool wind_estimation_enabled` of `AP_AHRS` (`AP_AHRS/AP_AHRS.h:905`). -/
  wind_estimation_enabled : Bool := false
  /-- `bool fly_forward` of `AP_AHRS` (`AP_AHRS/AP_AHRS.h:913`). -/
  fly_forward : Bool := false
  /-- `struct (unnamed struct at AP_AHRS/AP_AHRS.h:983:5) state` of `AP_AHRS` (`AP_AHRS/AP_AHRS.h:1014`). -/
  state : AP_AHRS.state_t := {}
  /-- `AP_AHRS_DCM dcm` of `AP_AHRS` (`AP_AHRS/AP_AHRS.h:1020`). -/
  dcm : AP_AHRS_DCM.State := {}
  /-- `struct AP_AHRS_Backend::Estimates dcm_estimates` of `AP_AHRS` (`AP_AHRS/AP_AHRS.h:1021`). -/
  dcm_estimates : AP_AHRS_Backend.Estimates.State := {}
  /-- `struct AP_AHRS_Backend::Estimates ekf3_estimates` of `AP_AHRS` (`AP_AHRS/AP_AHRS.h:1024`). -/
  ekf3_estimates : AP_AHRS_Backend.Estimates.State := {}
  /-- `struct AP_AHRS_Backend::Estimates sim_estimates` of `AP_AHRS` (`AP_AHRS/AP_AHRS.h:1035`). -/
  sim_estimates : AP_AHRS_Backend.Estimates.State := {}
  /-- `struct (unnamed struct at AP_AHRS/AP_AHRS.h:1051:5) backends_and_estimates[3]` of `AP_AHRS` (`AP_AHRS/AP_AHRS.h:1054`). -/
  backends_and_estimates : Array AP_AHRS.backends_and_estimates_t := #[{ backend := WPtr.ahrs'dcm, estimates := WPtr.ahrs'dcm_estimates }, { backend := WPtr.ahrs'ekf3, estimates := WPtr.ahrs'ekf3_estimates }, { backend := WPtr.ahrs'sim, estimates := WPtr.ahrs'sim_estimates }]
  /-- `AP_UInt16 _options` of `AP_AHRS` (`AP_AHRS/AP_AHRS.h:1089`). -/
  _options : AP_ParamT_unsigned_short_2.State := {}
  /-- `bool done_common_origin` of `AP_AHRS` (`AP_AHRS/AP_AHRS.h:1092`). -/
  done_common_origin : Bool := false
  /-- `AP_AHRS_Backend * configured_backend` of `AP_AHRS` (`AP_AHRS/AP_AHRS.h:1107`). -/
  configured_backend : WPtr := WPtr.null
  /-- `AP_AHRS_Backend::Estimates * configured_estimates` of `AP_AHRS` (`AP_AHRS/AP_AHRS.h:1108`). -/
  configured_estimates : WPtr := WPtr.null
  /-- `AP_AHRS_Backend * active_backend` of `AP_AHRS` (`AP_AHRS/AP_AHRS.h:1113`). -/
  active_backend : WPtr := WPtr.null
  /-- `AP_AHRS_Backend::Estimates * active_estimates` of `AP_AHRS` (`AP_AHRS/AP_AHRS.h:1114`). -/
  active_estimates : WPtr := WPtr.null
  /-- `AP_AHRS_ResetCounter<uint16_t> attitude_reset_tracker` of `AP_AHRS` (`AP_AHRS/AP_AHRS.h:1122`). -/
  attitude_reset_tracker : AP_AHRS_ResetCounter_unsigned_short.State := {}
  /-- `AP_AHRS_ResetCounter<uint16_t> yaw_reset_tracker` of `AP_AHRS` (`AP_AHRS/AP_AHRS.h:1123`). -/
  yaw_reset_tracker : AP_AHRS_ResetCounter_unsigned_short.State := {}
  /-- `AP_AHRS_ResetCounter<uint16_t> position_NE_reset_tracker` of `AP_AHRS` (`AP_AHRS/AP_AHRS.h:1124`). -/
  position_NE_reset_tracker : AP_AHRS_ResetCounter_unsigned_short.State := {}
  /-- `AP_AHRS_ResetCounter<uint16_t> position_D_reset_tracker` of `AP_AHRS` (`AP_AHRS/AP_AHRS.h:1125`). -/
  position_D_reset_tracker : AP_AHRS_ResetCounter_unsigned_short.State := {}
  /-- `AP_AHRS_Backend::Estimates * secondary_estimates` of `AP_AHRS` (`AP_AHRS/AP_AHRS.h:1133`). -/
  secondary_estimates : WPtr := WPtr.null
deriving Inhabited

/-- Values C++ `AP_AHRS` reads from objects outside the translation (--boundary): one field per distinct read, in first-use order. -/
structure Inputs where
  /-- `hal.util.get_soft_armed()` (first read at `AP_AHRS/AP_AHRS_Backend.cpp:78`). -/
  get_soft_armed : Bool := false
  /-- `hal.util.was_watchdog_reset()` (first read at `AP_AHRS/AP_AHRS.cpp:1797`). -/
  was_watchdog_reset : Bool := false
  /-- `hal.util.persistent_data.home_lat` (first read at `AP_AHRS/AP_AHRS.cpp:1797`). -/
  persistent_data_home_lat : Int32 := (0 : Int32)
  /-- `hal.util.persistent_data.home_lon` (first read at `AP_AHRS/AP_AHRS.cpp:1797`). -/
  persistent_data_home_lon : Int32 := (0 : Int32)
  /-- `hal.util.persistent_data.home_alt_cm` (first read at `AP_AHRS/AP_AHRS.cpp:1800`). -/
  persistent_data_home_alt_cm : Int32 := (0 : Int32)
  /-- `sim.get_origin(ret) writes ret` (first read at `AP_AHRS/AP_AHRS.cpp:508`). -/
  get_origin_ret : Location.State := {}
  /-- `sim.get_origin()` (first read at `AP_AHRS/AP_AHRS.cpp:508`). -/
  get_origin : Bool := false
  /-- `hal.opticalflow_set` (first read at `AP_AHRS/AP_AHRS.cpp:645`). -/
  opticalflow_set : Bool := false
  /-- `random.random()` (first read at `AP_AHRS/AP_AHRS.cpp:664`). -/
  random : Int64 := (0 : Int64)
  /-- `sim.get_innovations(velInnov, posInnov, magInnov, tasInnov, yawInnov) writes velInnov` (first read at `AP_AHRS/AP_AHRS.h:403`). -/
  get_innovations_velInnov : Vector3f.State := {}
  /-- `sim.get_innovations(velInnov, posInnov, magInnov, tasInnov, yawInnov) writes posInnov` (first read at `AP_AHRS/AP_AHRS.h:403`). -/
  get_innovations_posInnov : Vector3f.State := {}
  /-- `sim.get_innovations(velInnov, posInnov, magInnov, tasInnov, yawInnov) writes magInnov` (first read at `AP_AHRS/AP_AHRS.h:403`). -/
  get_innovations_magInnov : Vector3f.State := {}
  /-- `sim.get_innovations(velInnov, posInnov, magInnov, tasInnov, yawInnov) writes tasInnov` (first read at `AP_AHRS/AP_AHRS.h:403`). -/
  get_innovations_tasInnov : Binary32 := (Binary32.ofBits 0x00000000 /- 0.0 -/)
  /-- `sim.get_innovations(velInnov, posInnov, magInnov, tasInnov, yawInnov) writes yawInnov` (first read at `AP_AHRS/AP_AHRS.h:403`). -/
  get_innovations_yawInnov : Binary32 := (Binary32.ofBits 0x00000000 /- 0.0 -/)
  /-- `sim.get_innovations()` (first read at `AP_AHRS/AP_AHRS.h:403`). -/
  get_innovations : Bool := false
  /-- `link.get_chan()` (first read at `AP_AHRS/AP_AHRS.cpp:1709`). -/
  get_chan : mavlink_channel_t := mavlink_channel_t.MAVLINK_COMM_0
  /-- What member `dcm` reads from the boundary. -/
  dcm : AP_AHRS_DCM.Inputs := {}
deriving Inhabited

/-- C++ `bool AP_AHRS::get_origin(Location & ret) const`, `AP_AHRS/AP_AHRS.cpp:2083-2087`. -/
def get_origin (s : State) (ret : Location.State) : Location.State × Bool := Id.run do
  let mut ret := ret
  ret := s.state.origin
  return (ret, s.state.origin_ok)

end AP_AHRS

namespace AP_AHRS_View

/-- C++ `struct AP_AHRS_View::(unnamed struct at AP_AHRS/AP_AHRS_View.h:214:5)`, `AP_AHRS/AP_AHRS_View.h:214-221`. -/
structure trig_t where
  /-- `float cos_roll` of `AP_AHRS_View::(unnamed struct at AP_AHRS/AP_AHRS_View.h:214:5)` (`AP_AHRS/AP_AHRS_View.h:215`). -/
  cos_roll : Binary32 := (Binary32.ofBits 0x00000000 /- 0.0 -/)
  /-- `float cos_pitch` of `AP_AHRS_View::(unnamed struct at AP_AHRS/AP_AHRS_View.h:214:5)` (`AP_AHRS/AP_AHRS_View.h:216`). -/
  cos_pitch : Binary32 := (Binary32.ofBits 0x00000000 /- 0.0 -/)
  /-- `float cos_yaw` of `AP_AHRS_View::(unnamed struct at AP_AHRS/AP_AHRS_View.h:214:5)` (`AP_AHRS/AP_AHRS_View.h:217`). -/
  cos_yaw : Binary32 := (Binary32.ofBits 0x00000000 /- 0.0 -/)
  /-- `float sin_roll` of `AP_AHRS_View::(unnamed struct at AP_AHRS/AP_AHRS_View.h:214:5)` (`AP_AHRS/AP_AHRS_View.h:218`). -/
  sin_roll : Binary32 := (Binary32.ofBits 0x00000000 /- 0.0 -/)
  /-- `float sin_pitch` of `AP_AHRS_View::(unnamed struct at AP_AHRS/AP_AHRS_View.h:214:5)` (`AP_AHRS/AP_AHRS_View.h:219`). -/
  sin_pitch : Binary32 := (Binary32.ofBits 0x00000000 /- 0.0 -/)
  /-- `float sin_yaw` of `AP_AHRS_View::(unnamed struct at AP_AHRS/AP_AHRS_View.h:214:5)` (`AP_AHRS/AP_AHRS_View.h:220`). -/
  sin_yaw : Binary32 := (Binary32.ofBits 0x00000000 /- 0.0 -/)
deriving Inhabited

end AP_AHRS_View

namespace AP_AHRS_View

/-- State of C++ `AP_AHRS_View` (`AP_AHRS/AP_AHRS_View.h:29-225`): its data members. -/
structure State where
  /-- `float roll` of `AP_AHRS_View` (`AP_AHRS/AP_AHRS_View.h:183`). -/
  roll : Binary32 := (Binary32.ofBits 0x00000000 /- 0.0 -/)
  /-- `float pitch` of `AP_AHRS_View` (`AP_AHRS/AP_AHRS_View.h:184`). -/
  pitch : Binary32 := (Binary32.ofBits 0x00000000 /- 0.0 -/)
  /-- `float yaw` of `AP_AHRS_View` (`AP_AHRS/AP_AHRS_View.h:185`). -/
  yaw : Binary32 := (Binary32.ofBits 0x00000000 /- 0.0 -/)
  /-- `int32_t roll_sensor` of `AP_AHRS_View` (`AP_AHRS/AP_AHRS_View.h:186`). -/
  roll_sensor : Int32 := (0 : Int32)
  /-- `int32_t pitch_sensor` of `AP_AHRS_View` (`AP_AHRS/AP_AHRS_View.h:187`). -/
  pitch_sensor : Int32 := (0 : Int32)
  /-- `int32_t yaw_sensor` of `AP_AHRS_View` (`AP_AHRS/AP_AHRS_View.h:188`). -/
  yaw_sensor : Int32 := (0 : Int32)
  /-- `const enum Rotation rotation` of `AP_AHRS_View` (`AP_AHRS/AP_AHRS_View.h:204`). -/
  rotation : Rotation := Rotation.ROTATION_NONE
  /-- `Matrix3f rot_view` of `AP_AHRS_View` (`AP_AHRS/AP_AHRS_View.h:208`). -/
  rot_view : Matrix3f.State := Matrix3f.init_void
  /-- `Matrix3f rot_view_T` of `AP_AHRS_View` (`AP_AHRS/AP_AHRS_View.h:210`). -/
  rot_view_T : Matrix3f.State := Matrix3f.init_void
  /-- `Matrix3f rot_body_to_ned` of `AP_AHRS_View` (`AP_AHRS/AP_AHRS_View.h:211`). -/
  rot_body_to_ned : Matrix3f.State := Matrix3f.init_void
  /-- `Vector3f gyro` of `AP_AHRS_View` (`AP_AHRS/AP_AHRS_View.h:212`). -/
  gyro : Vector3f.State := {}
  /-- `struct (unnamed struct at AP_AHRS/AP_AHRS_View.h:214:5) trig` of `AP_AHRS_View` (`AP_AHRS/AP_AHRS_View.h:221`). -/
  trig : AP_AHRS_View.trig_t := {}
  /-- `float y_angle` of `AP_AHRS_View` (`AP_AHRS/AP_AHRS_View.h:223`). -/
  y_angle : Binary32 := (Binary32.ofBits 0x00000000 /- 0.0 -/)
  /-- `float _pitch_trim_deg` of `AP_AHRS_View` (`AP_AHRS/AP_AHRS_View.h:224`). -/
  _pitch_trim_deg : Binary32 := (Binary32.ofBits 0x00000000 /- 0.0 -/)
deriving Inhabited

end AP_AHRS_View

/-- C++ `enum class GPSUse`, `AP_AHRS/AP_AHRS_Backend.h:37-41`. -/
inductive GPSUse where
  | Disable
  | Enable
  | EnableWithHeight
deriving DecidableEq, Inhabited

/-- The value of each enumerator of `GPSUse` (underlying type `uint8_t`). -/
def GPSUse.toInt : GPSUse → UInt8
  | .Disable => (0 : UInt8)
  | .Enable => (1 : UInt8)
  | .EnableWithHeight => (2 : UInt8)

/-- The enumerator of `GPSUse` with value `v` (the C++ converts only enumerator values; any other
value gives the first enumerator, the `Inhabited` default). -/
def GPSUse.ofInt (v : UInt8) : GPSUse :=
  if v == (0 : UInt8) then .Disable
  else if v == (1 : UInt8) then .Enable
  else if v == (2 : UInt8) then .EnableWithHeight
  else default

namespace AP_AHRS_ResetCounter_unsigned_short

/-- C++ `void AP_AHRS_ResetCounter<unsigned short>::fill(unsigned short new_key)`, `AP_AHRS/AP_AHRS_Backend.h:457-460`. -/
def fill (s : State) (new_key : UInt16) : State := Id.run do
  let mut s := s
  s := { s with last_key := new_key }
  s := { s with reset_count := s.reset_count + (1 : UInt16) }
  return s

/-- C++ `bool AP_AHRS_ResetCounter<unsigned short>::update(unsigned short new_key)`, `AP_AHRS/AP_AHRS_Backend.h:446-452`. -/
def update (s : State) (new_key : UInt16) : State × Bool := Id.run do
  let mut s := s
  if UInt32.toInt32 (UInt16.toUInt32 new_key) == UInt32.toInt32 (UInt16.toUInt32 s.last_key) then
    return (s, false)
  s := fill s new_key
  return (s, true)

end AP_AHRS_ResetCounter_unsigned_short

namespace AP_AHRS

/-- C++ `void AP_AHRS::update_reset_counters()`, `AP_AHRS/AP_AHRS.cpp:530-547`. -/
def update_reset_counters (s : State) : State := Id.run do
  let mut s := s
  if s.state.active_EKF_type != s.last_active_ekf_type then
    s := { s with attitude_reset_tracker := AP_AHRS_ResetCounter_unsigned_short.fill s.attitude_reset_tracker ((match s.active_estimates with | .ahrs'dcm_estimates => s.dcm_estimates | .ahrs'ekf3_estimates => s.ekf3_estimates | _ => s.sim_estimates) : AP_AHRS_Backend.Estimates.State).attitude_reset_count }
    s := { s with yaw_reset_tracker := AP_AHRS_ResetCounter_unsigned_short.fill s.yaw_reset_tracker ((match s.active_estimates with | .ahrs'dcm_estimates => s.dcm_estimates | .ahrs'ekf3_estimates => s.ekf3_estimates | _ => s.sim_estimates) : AP_AHRS_Backend.Estimates.State).yaw_reset_count }
    s := { s with position_NE_reset_tracker := AP_AHRS_ResetCounter_unsigned_short.fill s.position_NE_reset_tracker ((match s.active_estimates with | .ahrs'dcm_estimates => s.dcm_estimates | .ahrs'ekf3_estimates => s.ekf3_estimates | _ => s.sim_estimates) : AP_AHRS_Backend.Estimates.State).position_NE_reset_count }
    s := { s with position_D_reset_tracker := AP_AHRS_ResetCounter_unsigned_short.fill s.position_D_reset_tracker ((match s.active_estimates with | .ahrs'dcm_estimates => s.dcm_estimates | .ahrs'ekf3_estimates => s.ekf3_estimates | _ => s.sim_estimates) : AP_AHRS_Backend.Estimates.State).position_D_reset_count }
    return s
  let (t'1, _) := AP_AHRS_ResetCounter_unsigned_short.update s.attitude_reset_tracker ((match s.active_estimates with | .ahrs'dcm_estimates => s.dcm_estimates | .ahrs'ekf3_estimates => s.ekf3_estimates | _ => s.sim_estimates) : AP_AHRS_Backend.Estimates.State).attitude_reset_count
  s := { s with attitude_reset_tracker := t'1 }
  let (t'3, t'4) := AP_AHRS_ResetCounter_unsigned_short.update s.yaw_reset_tracker ((match s.active_estimates with | .ahrs'dcm_estimates => s.dcm_estimates | .ahrs'ekf3_estimates => s.ekf3_estimates | _ => s.sim_estimates) : AP_AHRS_Backend.Estimates.State).yaw_reset_count
  s := { s with yaw_reset_tracker := t'3 }
  if t'4 then
    pure ()
  let (t'5, _) := AP_AHRS_ResetCounter_unsigned_short.update s.position_NE_reset_tracker ((match s.active_estimates with | .ahrs'dcm_estimates => s.dcm_estimates | .ahrs'ekf3_estimates => s.ekf3_estimates | _ => s.sim_estimates) : AP_AHRS_Backend.Estimates.State).position_NE_reset_count
  s := { s with position_NE_reset_tracker := t'5 }
  let (t'7, _) := AP_AHRS_ResetCounter_unsigned_short.update s.position_D_reset_tracker ((match s.active_estimates with | .ahrs'dcm_estimates => s.dcm_estimates | .ahrs'ekf3_estimates => s.ekf3_estimates | _ => s.sim_estimates) : AP_AHRS_Backend.Estimates.State).position_D_reset_count
  s := { s with position_D_reset_tracker := t'7 }
  return s

end AP_AHRS

namespace AP_AHRS

/-- C++ `void AP_AHRS::update_cd_values()`, `AP_AHRS/AP_AHRS_Backend.cpp:149-160`. -/
def update_cd_values (s : State) : State := Id.run do
  let mut s := s
  s := { s with roll_sensor := Binary32.toInt32 (Estimator_lib.degrees s.roll * (Binary32.ofBits 0x42c80000 /- 100 -/)) }
  s := { s with pitch_sensor := Binary32.toInt32 (Estimator_lib.degrees s.pitch * (Binary32.ofBits 0x42c80000 /- 100 -/)) }
  s := { s with yaw_sensor := Binary32.toInt32 (Estimator_lib.degrees s.yaw * (Binary32.ofBits 0x42c80000 /- 100 -/)) }
  if s.yaw_sensor < (0 : Int32) then
    s := { s with yaw_sensor := s.yaw_sensor + (36000 : Int32) }
  s := { s with rpy_deg := s.rpy_deg.set! 0 (Estimator_lib.degrees s.roll) }
  s := { s with rpy_deg := s.rpy_deg.set! 1 (Estimator_lib.degrees s.pitch) }
  s := { s with rpy_deg := s.rpy_deg.set! 2 (Estimator_lib.wrap_360_float (Estimator_lib.degrees s.yaw)) }
  return s

end AP_AHRS

namespace AP_AHRS

/-- C++ `void AP_AHRS::calc_trig(const Matrix3f & rot, float & cr, float & cp, float & cy, float & sr, float & sp, float & sy) const`, `AP_AHRS/AP_AHRS_Backend.cpp:93-135`. -/
def calc_trig (rot : Matrix3f.State) (cr : Binary32) (cp : Binary32) (cy : Binary32) (sr : Binary32) (sp : Binary32) (sy : Binary32) : Binary32 × Binary32 × Binary32 × Binary32 × Binary32 × Binary32 := Id.run do
  let mut cr := cr
  let mut cp := cp
  let mut cy := cy
  let mut sr := sr
  let mut sp := sp
  let mut sy := sy
  let mut yaw_vector : Vector2f.State := Vector2f.init_float2 rot.a.x rot.b.x
  if decide (Binary32.abs yaw_vector.x > (Binary32.ofBits 0x00000000 /- 0 -/)) || decide (Binary32.abs yaw_vector.y > (Binary32.ofBits 0x00000000 /- 0 -/)) then
    yaw_vector := Vector2f.normalize yaw_vector
  sy := Estimator_lib.constrain_value_line_float yaw_vector.y (-(Binary32.ofBits 0x3f800000 /- 1 -/)) (Binary32.ofBits 0x3f800000 /- 1 -/) (Int32.toUInt32 (103 : Int32))
  cy := Estimator_lib.constrain_value_line_float yaw_vector.x (-(Binary32.ofBits 0x3f800000 /- 1 -/)) (Binary32.ofBits 0x3f800000 /- 1 -/) (Int32.toUInt32 (104 : Int32))
  if Vector2f.is_inf yaw_vector || Vector2f.is_nan yaw_vector then
    sy := (Binary32.ofBits 0x00000000 /- 0.0f -/)
    cy := (Binary32.ofBits 0x3f800000 /- 1.0f -/)
  let cx2 : Binary32 := rot.c.x * rot.c.x
  if cx2 ≥ (Binary32.ofBits 0x3f800000 /- 1.0f -/) then
    cp := (Binary32.ofBits 0x00000000 /- 0 -/)
    cr := (Binary32.ofBits 0x3f800000 /- 1.0f -/)
  else
    cp := Estimator_lib.safe_sqrt_float ((Binary32.ofBits 0x3f800000 /- 1 -/) - cx2)
    cr := rot.c.z / cp
  cp := Estimator_lib.constrain_value_line_float cp (Binary32.ofBits 0x00000000 /- 0 -/) (Binary32.ofBits 0x3f800000 /- 1 -/) (Int32.toUInt32 (120 : Int32))
  cr := Estimator_lib.constrain_value_line_float cr (-(Binary32.ofBits 0x3f800000 /- 1 -/)) (Binary32.ofBits 0x3f800000 /- 1 -/) (Int32.toUInt32 (121 : Int32))
  sp := -rot.c.x
  if !(Estimator_lib.is_zero_float cp) then
    sr := rot.c.y / cp
  if Estimator_lib.is_zero_float cp || Binary32.isInf cr || Binary32.isNaN cr || Binary32.isInf sr || Binary32.isNaN sr then
    let mut r : Binary32 := (Binary32.ofBits 0x00000000 /- 0.0 -/)  -- uninitialized in C++; assigned before every read
    let mut p' : Binary32 := (Binary32.ofBits 0x00000000 /- 0.0 -/)  -- uninitialized in C++; assigned before every read
    let mut y : Binary32 := (Binary32.ofBits 0x00000000 /- 0.0 -/)  -- uninitialized in C++; assigned before every read
    let (t'1, t'2, t'3) := Matrix3f.to_euler rot true r true p' true y
    r := t'1
    p' := t'2
    y := t'3
    cr := Musl.cosf.cosf r
    sr := Musl.sinf.sinf r
  return (cr, cp, cy, sr, sp, sy)

/-- C++ `const Matrix3f & AP_AHRS::get_rotation_body_to_ned() const`, `AP_AHRS/AP_AHRS.h:665`. -/
def get_rotation_body_to_ned (s : State) : Matrix3f.State := Id.run do
  return s.state.dcm_matrix

/-- C++ `void AP_AHRS::update_trig()`, `AP_AHRS/AP_AHRS_Backend.cpp:139-144`. -/
def update_trig (s : State) : State := Id.run do
  let mut s := s
  let (t'1, t'2, t'3, t'4, t'5, t'6) := calc_trig (get_rotation_body_to_ned s) s._cos_roll s._cos_pitch s._cos_yaw s._sin_roll s._sin_pitch s._sin_yaw
  s := { s with _cos_roll := t'1 }
  s := { s with _cos_pitch := t'2 }
  s := { s with _cos_yaw := t'3 }
  s := { s with _sin_roll := t'4 }
  s := { s with _sin_pitch := t'5 }
  s := { s with _sin_yaw := t'6 }
  return s

end AP_AHRS

namespace AP_AHRS_Backend.Estimates

/-- C++ `bool AP_AHRS_Backend::Estimates::get_location(Location & loc) const`, `AP_AHRS/AP_AHRS_Backend.h:174-177`. -/
def get_location (s : State) (loc : Location.State) : Location.State × Bool := Id.run do
  let mut loc := loc
  loc := s.location
  return (loc, s.location_valid)

end AP_AHRS_Backend.Estimates

namespace AP_AHRS_Backend.Estimates

/-- C++ `bool AP_AHRS_Backend::Estimates::get_quaternion(Quaternion & quat) const`, `AP_AHRS/AP_AHRS_Backend.h:113-116`. -/
def get_quaternion (s : State) (quat : Quaternion.State) : Quaternion.State × Bool := Id.run do
  let mut quat := quat
  quat := s.quaternion
  return (quat, s.attitude_valid)

/-- C++ `bool AP_AHRS_Backend::Estimates::get_velocity_NED(Vector3f & vel) const`, `AP_AHRS/AP_AHRS_Backend.h:136-142`. -/
def get_velocity_NED (s : State) (vel : Vector3f.State) : Vector3f.State × Bool := Id.run do
  let mut vel := vel
  if !s.velocity_NED_valid then
    return (vel, false)
  vel := s.velocity_NED
  return (vel, true)

end AP_AHRS_Backend.Estimates

namespace AP_AHRS_ResetCounter_signed_char

/-- C++ `void AP_AHRS_ResetCounter<signed char>::fill(signed char new_key)`, `AP_AHRS/AP_AHRS_Backend.h:457-460`. -/
def fill (s : State) (new_key : Int8) : State := Id.run do
  let mut s := s
  s := { s with last_key := new_key }
  s := { s with reset_count := s.reset_count + (1 : UInt16) }
  return s

/-- C++ `bool AP_AHRS_ResetCounter<signed char>::update(signed char new_key)`, `AP_AHRS/AP_AHRS_Backend.h:446-452`. -/
def update (s : State) (new_key : Int8) : State × Bool := Id.run do
  let mut s := s
  if Int8.toInt32 new_key == Int8.toInt32 s.last_key then
    return (s, false)
  s := fill s new_key
  return (s, true)

end AP_AHRS_ResetCounter_signed_char

namespace AP_AHRS_ResetCounter_signed_char

/-- C++ `uint16_t AP_AHRS_ResetCounter<signed char>::count() const`, `AP_AHRS/AP_AHRS_Backend.h:462`. -/
def count (s : State) : UInt16 := Id.run do
  return s.reset_count

end AP_AHRS_ResetCounter_signed_char

namespace AP_AHRS_ResetCounter_unsigned_short

/-- C++ `uint16_t AP_AHRS_ResetCounter<unsigned short>::count() const`, `AP_AHRS/AP_AHRS_Backend.h:462`. -/
def count (s : State) : UInt16 := Id.run do
  return s.reset_count

end AP_AHRS_ResetCounter_unsigned_short

/-- C++ `const char * shortname()`, `AP_AHRS/AP_AHRS_SIM.h:54`. -/
def AP_AHRS_SIM_shortname : String := Id.run do
  return "SIM"

namespace AP_AHRS_DCM

/-- C++ `bool AP_AHRS_Backend::get_innovations(Vector3f & velInnov, Vector3f & posInnov, Vector3f & magInnov, float & tasInnov, float & yawInnov) const`, `AP_AHRS/AP_AHRS_Backend.h:366-368` (a member of `AP_AHRS_Backend`, translated for `AP_AHRS_DCM`). -/
def get_innovations (velInnov : Vector3f.State) (posInnov : Vector3f.State) (magInnov : Vector3f.State) (tasInnov : Binary32) (yawInnov : Binary32) : Vector3f.State × Vector3f.State × Vector3f.State × Binary32 × Binary32 × Bool := Id.run do
  let mut velInnov := velInnov
  let mut posInnov := posInnov
  let mut magInnov := magInnov
  let mut tasInnov := tasInnov
  let mut yawInnov := yawInnov
  return (velInnov, posInnov, magInnov, tasInnov, yawInnov, false)

end AP_AHRS_DCM

namespace AP_AHRS_Backend.Estimates

/-- C++ `bool AP_AHRS_Backend::Estimates::get_vert_pos_rate_D(float & velocity) const`, `AP_AHRS/AP_AHRS_Backend.h:160-166`. -/
def get_vert_pos_rate_D (s : State) (velocity : Binary32) : Binary32 × Bool := Id.run do
  let mut velocity := velocity
  if !s.vert_pos_rate_D_valid then
    return (velocity, false)
  velocity := s.vert_pos_rate_D
  return (velocity, true)

end AP_AHRS_Backend.Estimates

namespace AP_AHRS_DCM

/-- C++ `float AP_AHRS_DCM::get_error_rp() const`, `AP_AHRS/AP_AHRS_DCM.h:71-73`. -/
def get_error_rp (s : State) : Binary32 := Id.run do
  return s._error_rp

end AP_AHRS_DCM

namespace AP_AHRS

/-- C++ `float AP_AHRS::get_error_rp() const`, `AP_AHRS/AP_AHRS.cpp:704-710`. -/
def get_error_rp (s : State) : Binary32 := Id.run do
  return AP_AHRS_DCM.get_error_rp s.dcm

end AP_AHRS

namespace AP_AHRS_DCM

/-- C++ `float AP_AHRS_DCM::get_error_yaw() const`, `AP_AHRS/AP_AHRS_DCM.h:74-76`. -/
def get_error_yaw (s : State) : Binary32 := Id.run do
  return s._error_yaw

end AP_AHRS_DCM

namespace AP_AHRS

/-- C++ `float AP_AHRS::get_error_yaw() const`, `AP_AHRS/AP_AHRS.cpp:712-718`. -/
def get_error_yaw (s : State) : Binary32 := Id.run do
  return AP_AHRS_DCM.get_error_yaw s.dcm

end AP_AHRS

namespace AP_AHRS_DCM

-- not read in the Lean: requires_position, failure_msg_len
set_option linter.unusedVariables false in
/-- C++ `bool AP_AHRS_DCM::pre_arm_check(bool requires_position, char * failure_msg, uint8_t failure_msg_len) const`, `AP_AHRS/AP_AHRS_DCM.h:82-84`. -/
def pre_arm_check (requires_position : Bool) (failure_msg_len : UInt8) : Bool := Id.run do
  return true

end AP_AHRS_DCM

namespace AP_AHRS_DCM

/-- C++ `AP_AHRS_Backend::AP_AHRS_Backend()`, `AP_AHRS/AP_AHRS_Backend.h:48` (a member of `AP_AHRS_Backend`, translated for `AP_AHRS_DCM`). -/
def AP_AHRS_Backend.init (s : State) : State := Id.run do
  let mut s := s
  s := { s with _wind := Vector3f.init_void }
  s := { s with _last_fuse := Vector3f.init_void }
  s := { s with _last_vel := Vector3f.init_void }
  return s

end AP_AHRS_DCM

namespace AP_AHRS_DCM

/-- C++ `AP_AHRS_DCM::AP_AHRS_DCM(AP_Float & kp_yaw, AP_Float & kp, AP_Float & _gps_gain, AP_Float & _beta, AP_Enum<GPSUse> & gps_use, AP_Int8 & gps_minsats)`, `AP_AHRS/AP_AHRS_DCM.h:34-49`. -/
def init (kp_yaw : AP_ParamT_float_4.State) (kp : AP_ParamT_float_4.State) (_gps_gain : AP_ParamT_float_4.State) (_beta : AP_ParamT_float_4.State) (gps_use : AP_Enum_GPSUse.State) (gps_minsats : AP_ParamT_signed_char_1.State) : State × AP_ParamT_float_4.State × AP_ParamT_float_4.State × AP_ParamT_float_4.State × AP_ParamT_float_4.State × AP_Enum_GPSUse.State × AP_ParamT_signed_char_1.State := Id.run do
  let mut s : State := {}
  let mut kp_yaw := kp_yaw
  let mut kp := kp
  let mut _gps_gain := _gps_gain
  let mut _beta := _beta
  let mut gps_use := gps_use
  let mut gps_minsats := gps_minsats
  s := AP_AHRS_Backend.init s
  s := { s with _accel_ef := Vector3f.init_void }
  s := { s with _dcm_matrix := Matrix3f.init_void }
  s := { s with _body_dcm_matrix := Matrix3f.init_void }
  s := { s with _omega_P := Vector3f.init_void }
  s := { s with _omega_yaw_P := Vector3f.init_void }
  s := { s with _omega_I := Vector3f.init_void }
  s := { s with _omega_I_sum := Vector3f.init_void }
  s := { s with _omega := Vector3f.init_void }
  s := { s with _last_velocity := Vector3f.init_void }
  s := { s with last_origin := Location.init_void }
  s := { s with _lp := Vector2f.init_void }
  s := { s with _hp := Vector2f.init_void }
  s := { s with _lastGndVelADS := Vector2f.init_void }
  s := { s with _dcm_matrix := Matrix3f.identity s._dcm_matrix }
  return (s, kp_yaw, kp, _gps_gain, _beta, gps_use, gps_minsats)

end AP_AHRS_DCM

namespace AP_AHRS_DCM

/-! Not emitted, since they have no effect in the model (they write neither the state, the
parameters nor a reference parameter; e.g. they only save parameters):
- C++ `void AP_AHRS_Backend::resetHeightDatum()`, `AP_AHRS/AP_AHRS_Backend.h:362` (a member of `AP_AHRS_Backend`, translated for `AP_AHRS_DCM`).
- C++ `void AP_AHRS_Backend::request_yaw_reset()`, `AP_AHRS/AP_AHRS_Backend.h:298` (a member of `AP_AHRS_Backend`, translated for `AP_AHRS_DCM`).
- C++ `void AP_AHRS_Backend::check_lane_switch()`, `AP_AHRS/AP_AHRS_Backend.h:295` (a member of `AP_AHRS_Backend`, translated for `AP_AHRS_DCM`).
-/

end AP_AHRS_DCM

end Estimator_lib
