import ArduLean.Runtime.CFloat
import ArduLean.Estimator.libraries.AP_Math.AP_Math
import ArduLean.Estimator.World
import ArduLean.Estimator.libraries.AP_Common.AP_Common
import ArduLean.Estimator.libraries.AP_NavEKF.AP_NavEKF
import ArduLean.Estimator.libraries.AP_NavEKF3.AP_NavEKF3
import ArduLean.Estimator.libraries.AP_Math.AP_Math_2
import ArduLean.Estimator.libraries.AP_NavEKF.AP_NavEKF_2

/-!
ArduPilot `libraries/AP_NavEKF3`, part 2 of 4. Sources: `libraries/AP_NavEKF3/AP_NavEKF3_core.h`, `libraries/AP_NavEKF3/AP_NavEKF3_Outputs.cpp`, `libraries/AP_NavEKF3/AP_NavEKF3_core.cpp`, `libraries/AP_NavEKF3/AP_NavEKF3_PosVelFusion.cpp`, `libraries/AP_NavEKF3/AP_NavEKF3.cpp`, `libraries/AP_NavEKF3/AP_NavEKF3_GyroBias.cpp`, `libraries/AP_NavEKF3/AP_NavEKF3_AirDataFusion.cpp`, `libraries/AP_NavEKF3/AP_NavEKF3_MagFusion.cpp` and 2 more.

Items of `lean/Estimator_lib.lean` (the estimator translation), unchanged; placed by `tools/split_modules.py` (`ArduLean/Estimator/INDEX.md`).
-/

open FloatLib.Floats (Binary32 Binary64)

set_option maxRecDepth 200000
-- AP_DAL's `const log_RISH old_RISH = _RISH;` read only by WRITE_REPLAY_BLOCK_IFCHANGED, which is `(void)old`
-- without logging (HAL_LOGGING_ENABLED 0): an unused binding, as in the C++
set_option linter.unusedVariables false

namespace Estimator_lib

namespace NavEKF3_core.AirspeedFusion

/-- State of C++ `NavEKF3_core::AirspeedFusion` (`AP_NavEKF3/AP_NavEKF3_core.h:1124-1139`): its data members. -/
structure State where
  /-- `EKF_obs_buffer_t<tas_elements> stored` of `NavEKF3_core::AirspeedFusion` (`AP_NavEKF3/AP_NavEKF3_core.h:1128`). -/
  stored : EKF_obs_buffer_t_NavEKF3_core_tas_elements.State := EKF_obs_buffer_t_NavEKF3_core_tas_elements.construct
  /-- `tas_elements dataNew` of `NavEKF3_core::AirspeedFusion` (`AP_NavEKF3/AP_NavEKF3_core.h:1129`). -/
  dataNew : NavEKF3_core.tas_elements := {}
  /-- `tas_elements dataDelayed` of `NavEKF3_core::AirspeedFusion` (`AP_NavEKF3/AP_NavEKF3_core.h:1130`). -/
  dataDelayed : NavEKF3_core.tas_elements := {}
  /-- `bool dataToFuse` of `NavEKF3_core::AirspeedFusion` (`AP_NavEKF3/AP_NavEKF3_core.h:1131`). -/
  dataToFuse : Bool := false
  /-- `ftype innov` of `NavEKF3_core::AirspeedFusion` (`AP_NavEKF3/AP_NavEKF3_core.h:1132`). -/
  innov : Binary64 := (Binary64.ofBits 0x0000000000000000 /- 0.0 -/)
  /-- `ftype varInnov` of `NavEKF3_core::AirspeedFusion` (`AP_NavEKF3/AP_NavEKF3_core.h:1133`). -/
  varInnov : Binary64 := (Binary64.ofBits 0x0000000000000000 /- 0.0 -/)
  /-- `ftype testRatio` of `NavEKF3_core::AirspeedFusion` (`AP_NavEKF3/AP_NavEKF3_core.h:1134`). -/
  testRatio : Binary64 := (Binary64.ofBits 0x0000000000000000 /- 0.0 -/)
  /-- `uint32_t prevStepTime_ms` of `NavEKF3_core::AirspeedFusion` (`AP_NavEKF3/AP_NavEKF3_core.h:1135`). -/
  prevStepTime_ms : UInt32 := (0 : UInt32)
  /-- `uint32_t lastPassTime_ms` of `NavEKF3_core::AirspeedFusion` (`AP_NavEKF3/AP_NavEKF3_core.h:1136`). -/
  lastPassTime_ms : UInt32 := (0 : UInt32)
  /-- `uint32_t lastFailTime_ms` of `NavEKF3_core::AirspeedFusion` (`AP_NavEKF3/AP_NavEKF3_core.h:1137`). -/
  lastFailTime_ms : UInt32 := (0 : UInt32)
  /-- `uint32_t receivedTime_ms` of `NavEKF3_core::AirspeedFusion` (`AP_NavEKF3/AP_NavEKF3_core.h:1138`). -/
  receivedTime_ms : UInt32 := (0 : UInt32)
deriving Inhabited

end NavEKF3_core.AirspeedFusion

namespace NavEKF3_core.BodyOdomFusion

/-- State of C++ `NavEKF3_core::BodyOdomFusion` (`AP_NavEKF3/AP_NavEKF3_core.h:1409-1432`): its data members. -/
structure State where
  /-- `EKF_obs_buffer_t<vel_odm_elements> stored` of `NavEKF3_core::BodyOdomFusion` (`AP_NavEKF3/AP_NavEKF3_core.h:1414`). -/
  stored : EKF_obs_buffer_t_NavEKF3_core_vel_odm_elements.State := EKF_obs_buffer_t_NavEKF3_core_vel_odm_elements.construct
  /-- `vel_odm_elements dataNew` of `NavEKF3_core::BodyOdomFusion` (`AP_NavEKF3/AP_NavEKF3_core.h:1415`). -/
  dataNew : NavEKF3_core.vel_odm_elements := {}
  /-- `vel_odm_elements dataDelayed` of `NavEKF3_core::BodyOdomFusion` (`AP_NavEKF3/AP_NavEKF3_core.h:1416`). -/
  dataDelayed : NavEKF3_core.vel_odm_elements := {}
  /-- `uint32_t lastPassTime_ms` of `NavEKF3_core::BodyOdomFusion` (`AP_NavEKF3/AP_NavEKF3_core.h:1418`). -/
  lastPassTime_ms : UInt32 := (0 : UInt32)
  /-- `Vector3 testRatio` of `NavEKF3_core::BodyOdomFusion` (`AP_NavEKF3/AP_NavEKF3_core.h:1419`). -/
  testRatio : Array Binary64 := Array.replicate 3 (Binary64.ofBits 0x0000000000000000 /- 0.0 -/)
  /-- `Vector3 varInnov` of `NavEKF3_core::BodyOdomFusion` (`AP_NavEKF3/AP_NavEKF3_core.h:1420`). -/
  varInnov : Array Binary64 := Array.replicate 3 (Binary64.ofBits 0x0000000000000000 /- 0.0 -/)
  /-- `Vector3 innov` of `NavEKF3_core::BodyOdomFusion` (`AP_NavEKF3/AP_NavEKF3_core.h:1421`). -/
  innov : Array Binary64 := Array.replicate 3 (Binary64.ofBits 0x0000000000000000 /- 0.0 -/)
  /-- `uint32_t prevFuseTime_ms` of `NavEKF3_core::BodyOdomFusion` (`AP_NavEKF3/AP_NavEKF3_core.h:1422`). -/
  prevFuseTime_ms : UInt32 := (0 : UInt32)
  /-- `uint32_t measTime_ms` of `NavEKF3_core::BodyOdomFusion` (`AP_NavEKF3/AP_NavEKF3_core.h:1423`). -/
  measTime_ms : UInt32 := (0 : UInt32)
  /-- `bool fusionDelayed` of `NavEKF3_core::BodyOdomFusion` (`AP_NavEKF3/AP_NavEKF3_core.h:1424`). -/
  fusionDelayed : Bool := false
  /-- `bool fusionActive` of `NavEKF3_core::BodyOdomFusion` (`AP_NavEKF3/AP_NavEKF3_core.h:1425`). -/
  fusionActive : Bool := false
  /-- `EKF_obs_buffer_t<wheel_odm_elements> storedWheel` of `NavEKF3_core::BodyOdomFusion` (`AP_NavEKF3/AP_NavEKF3_core.h:1429`). -/
  storedWheel : EKF_obs_buffer_t_NavEKF3_core_wheel_odm_elements.State := EKF_obs_buffer_t_NavEKF3_core_wheel_odm_elements.construct
  /-- `wheel_odm_elements wheelDataDelayed` of `NavEKF3_core::BodyOdomFusion` (`AP_NavEKF3/AP_NavEKF3_core.h:1430`). -/
  wheelDataDelayed : NavEKF3_core.wheel_odm_elements := {}
deriving Inhabited

end NavEKF3_core.BodyOdomFusion

namespace NavEKF3_core.GpsYawFusion

/-- State of C++ `NavEKF3_core::GpsYawFusion` (`AP_NavEKF3/AP_NavEKF3_core.h:1435-1449`): its data members. -/
structure State where
  /-- `uint32_t measTime_ms` of `NavEKF3_core::GpsYawFusion` (`AP_NavEKF3/AP_NavEKF3_core.h:1439`). -/
  measTime_ms : UInt32 := (0 : UInt32)
  /-- `EKF_obs_buffer_t<yaw_elements> stored` of `NavEKF3_core::GpsYawFusion` (`AP_NavEKF3/AP_NavEKF3_core.h:1440`). -/
  stored : EKF_obs_buffer_t_NavEKF3_core_yaw_elements.State := EKF_obs_buffer_t_NavEKF3_core_yaw_elements.construct
  /-- `yaw_elements dataNew` of `NavEKF3_core::GpsYawFusion` (`AP_NavEKF3/AP_NavEKF3_core.h:1441`). -/
  dataNew : NavEKF3_core.yaw_elements := {}
  /-- `yaw_elements dataDelayed` of `NavEKF3_core::GpsYawFusion` (`AP_NavEKF3/AP_NavEKF3_core.h:1442`). -/
  dataDelayed : NavEKF3_core.yaw_elements := {}
  /-- `uint32_t lastUseTime_ms` of `NavEKF3_core::GpsYawFusion` (`AP_NavEKF3/AP_NavEKF3_core.h:1444`). -/
  lastUseTime_ms : UInt32 := (0 : UInt32)
  /-- `uint32_t lastFuseTime_ms` of `NavEKF3_core::GpsYawFusion` (`AP_NavEKF3/AP_NavEKF3_core.h:1445`). -/
  lastFuseTime_ms : UInt32 := (0 : UInt32)
  /-- `bool magFallbackOk` of `NavEKF3_core::GpsYawFusion` (`AP_NavEKF3/AP_NavEKF3_core.h:1446`). -/
  magFallbackOk : Bool := false
  /-- `bool magFallbackActive` of `NavEKF3_core::GpsYawFusion` (`AP_NavEKF3/AP_NavEKF3_core.h:1447`). -/
  magFallbackActive : Bool := false
  /-- `uint8_t fallbackGoodCounter` of `NavEKF3_core::GpsYawFusion` (`AP_NavEKF3/AP_NavEKF3_core.h:1448`). -/
  fallbackGoodCounter : UInt8 := (0 : UInt8)
deriving Inhabited

end NavEKF3_core.GpsYawFusion

namespace NavEKF3_core

/-- C++ `class NavEKF3_core::DragFusion`, `AP_NavEKF3/AP_NavEKF3_core.h:1517-1531`. -/
structure DragFusion where
  /-- `uint32_t lastPassTime_ms` of `NavEKF3_core::DragFusion` (`AP_NavEKF3/AP_NavEKF3_core.h:1529`). -/
  lastPassTime_ms : UInt32 := (0 : UInt32)
  /-- `bool fusionEnabled` of `NavEKF3_core::DragFusion` (`AP_NavEKF3/AP_NavEKF3_core.h:1530`). -/
  fusionEnabled : Bool := false
deriving Inhabited

/-- C++ `class NavEKF3_core::ExternalNavFusion`, `AP_NavEKF3/AP_NavEKF3_core.h:1571-1595`. -/
structure ExternalNavFusion where
  /-- `bool useVel` of `NavEKF3_core::ExternalNavFusion` (`AP_NavEKF3/AP_NavEKF3_core.h:1594`). -/
  useVel : Bool := false
deriving Inhabited

/-- C++ `struct NavEKF3_core::(unnamed struct at AP_NavEKF3/AP_NavEKF3_core.h:1598:5)`, `AP_NavEKF3/AP_NavEKF3_core.h:1598-1618`. -/
structure faultStatus_t where
  /-- `bool bad_xmag : 1` of `NavEKF3_core::(unnamed struct at AP_NavEKF3/AP_NavEKF3_core.h:1598:5)` (`AP_NavEKF3/AP_NavEKF3_core.h:1599`). -/
  bad_xmag : Bool := false
  /-- `bool bad_ymag : 1` of `NavEKF3_core::(unnamed struct at AP_NavEKF3/AP_NavEKF3_core.h:1598:5)` (`AP_NavEKF3/AP_NavEKF3_core.h:1600`). -/
  bad_ymag : Bool := false
  /-- `bool bad_zmag : 1` of `NavEKF3_core::(unnamed struct at AP_NavEKF3/AP_NavEKF3_core.h:1598:5)` (`AP_NavEKF3/AP_NavEKF3_core.h:1601`). -/
  bad_zmag : Bool := false
  /-- `bool bad_airspeed : 1` of `NavEKF3_core::(unnamed struct at AP_NavEKF3/AP_NavEKF3_core.h:1598:5)` (`AP_NavEKF3/AP_NavEKF3_core.h:1602`). -/
  bad_airspeed : Bool := false
  /-- `bool bad_sideslip : 1` of `NavEKF3_core::(unnamed struct at AP_NavEKF3/AP_NavEKF3_core.h:1598:5)` (`AP_NavEKF3/AP_NavEKF3_core.h:1603`). -/
  bad_sideslip : Bool := false
  /-- `bool bad_nvel : 1` of `NavEKF3_core::(unnamed struct at AP_NavEKF3/AP_NavEKF3_core.h:1598:5)` (`AP_NavEKF3/AP_NavEKF3_core.h:1604`). -/
  bad_nvel : Bool := false
  /-- `bool bad_evel : 1` of `NavEKF3_core::(unnamed struct at AP_NavEKF3/AP_NavEKF3_core.h:1598:5)` (`AP_NavEKF3/AP_NavEKF3_core.h:1605`). -/
  bad_evel : Bool := false
  /-- `bool bad_dvel : 1` of `NavEKF3_core::(unnamed struct at AP_NavEKF3/AP_NavEKF3_core.h:1598:5)` (`AP_NavEKF3/AP_NavEKF3_core.h:1606`). -/
  bad_dvel : Bool := false
  /-- `bool bad_npos : 1` of `NavEKF3_core::(unnamed struct at AP_NavEKF3/AP_NavEKF3_core.h:1598:5)` (`AP_NavEKF3/AP_NavEKF3_core.h:1607`). -/
  bad_npos : Bool := false
  /-- `bool bad_epos : 1` of `NavEKF3_core::(unnamed struct at AP_NavEKF3/AP_NavEKF3_core.h:1598:5)` (`AP_NavEKF3/AP_NavEKF3_core.h:1608`). -/
  bad_epos : Bool := false
  /-- `bool bad_dpos : 1` of `NavEKF3_core::(unnamed struct at AP_NavEKF3/AP_NavEKF3_core.h:1598:5)` (`AP_NavEKF3/AP_NavEKF3_core.h:1609`). -/
  bad_dpos : Bool := false
  /-- `bool bad_yaw : 1` of `NavEKF3_core::(unnamed struct at AP_NavEKF3/AP_NavEKF3_core.h:1598:5)` (`AP_NavEKF3/AP_NavEKF3_core.h:1610`). -/
  bad_yaw : Bool := false
  /-- `bool bad_decl : 1` of `NavEKF3_core::(unnamed struct at AP_NavEKF3/AP_NavEKF3_core.h:1598:5)` (`AP_NavEKF3/AP_NavEKF3_core.h:1611`). -/
  bad_decl : Bool := false
  /-- `bool bad_xflow : 1` of `NavEKF3_core::(unnamed struct at AP_NavEKF3/AP_NavEKF3_core.h:1598:5)` (`AP_NavEKF3/AP_NavEKF3_core.h:1612`). -/
  bad_xflow : Bool := false
  /-- `bool bad_yflow : 1` of `NavEKF3_core::(unnamed struct at AP_NavEKF3/AP_NavEKF3_core.h:1598:5)` (`AP_NavEKF3/AP_NavEKF3_core.h:1613`). -/
  bad_yflow : Bool := false
  /-- `bool bad_rngbcn : 1` of `NavEKF3_core::(unnamed struct at AP_NavEKF3/AP_NavEKF3_core.h:1598:5)` (`AP_NavEKF3/AP_NavEKF3_core.h:1614`). -/
  bad_rngbcn : Bool := false
  /-- `bool bad_xvel : 1` of `NavEKF3_core::(unnamed struct at AP_NavEKF3/AP_NavEKF3_core.h:1598:5)` (`AP_NavEKF3/AP_NavEKF3_core.h:1615`). -/
  bad_xvel : Bool := false
  /-- `bool bad_yvel : 1` of `NavEKF3_core::(unnamed struct at AP_NavEKF3/AP_NavEKF3_core.h:1598:5)` (`AP_NavEKF3/AP_NavEKF3_core.h:1616`). -/
  bad_yvel : Bool := false
  /-- `bool bad_zvel : 1` of `NavEKF3_core::(unnamed struct at AP_NavEKF3/AP_NavEKF3_core.h:1598:5)` (`AP_NavEKF3/AP_NavEKF3_core.h:1617`). -/
  bad_zvel : Bool := false
deriving Inhabited

/-- State of C++ `NavEKF3_core` (`AP_NavEKF3/AP_NavEKF3_core.h:127-1742`): its data members; base classes flattened, base first: `NavEKF_core_common`. -/
structure State where
  /-- `EKFGSF_yaw * yawEstimator` of `NavEKF3_core` (`AP_NavEKF3/AP_NavEKF3_core.h:495`). -/
  yawEstimator : WPtr := WPtr.null
  /-- `class NavEKF3 * frontend` of `NavEKF3_core` (`AP_NavEKF3/AP_NavEKF3_core.h:499`). -/
  frontend : WPtr := WPtr.null
  /-- `uint8_t imu_index` of `NavEKF3_core` (`AP_NavEKF3/AP_NavEKF3_core.h:500`). -/
  imu_index : UInt8 := (0 : UInt8)
  /-- `uint8_t gyro_index_active` of `NavEKF3_core` (`AP_NavEKF3/AP_NavEKF3_core.h:501`). -/
  gyro_index_active : UInt8 := (0 : UInt8)
  /-- `uint8_t accel_index_active` of `NavEKF3_core` (`AP_NavEKF3/AP_NavEKF3_core.h:502`). -/
  accel_index_active : UInt8 := (0 : UInt8)
  /-- `uint8_t core_index` of `NavEKF3_core` (`AP_NavEKF3/AP_NavEKF3_core.h:503`). -/
  core_index : UInt8 := (0 : UInt8)
  /-- `uint8_t imu_buffer_length` of `NavEKF3_core` (`AP_NavEKF3/AP_NavEKF3_core.h:504`). -/
  imu_buffer_length : UInt8 := (0 : UInt8)
  /-- `uint8_t obs_buffer_length` of `NavEKF3_core` (`AP_NavEKF3/AP_NavEKF3_core.h:505`). -/
  obs_buffer_length : UInt8 := (0 : UInt8)
  /-- `Vector24 statesArray` of `NavEKF3_core` (`AP_NavEKF3/AP_NavEKF3_core.h:588`). -/
  statesArray : Array Binary64 := Array.replicate 24 (Binary64.ofBits 0x0000000000000000 /- 0.0 -/)
  /-- `struct (unnamed struct at AP_NavEKF3/AP_NavEKF3_core.h:700:5) inactiveBias[3]` of `NavEKF3_core` (`AP_NavEKF3/AP_NavEKF3_core.h:703`). -/
  inactiveBias : Array NavEKF3_core.inactiveBias_t := Array.replicate 3 {}
  /-- `bool statesInitialised` of `NavEKF3_core` (`AP_NavEKF3/AP_NavEKF3_core.h:1101`). -/
  statesInitialised : Bool := false
  /-- `bool magHealth` of `NavEKF3_core` (`AP_NavEKF3/AP_NavEKF3_core.h:1102`). -/
  magHealth : Bool := false
  /-- `bool velTimeout` of `NavEKF3_core` (`AP_NavEKF3/AP_NavEKF3_core.h:1103`). -/
  velTimeout : Bool := false
  /-- `bool posTimeout` of `NavEKF3_core` (`AP_NavEKF3/AP_NavEKF3_core.h:1104`). -/
  posTimeout : Bool := false
  /-- `bool hgtTimeout` of `NavEKF3_core` (`AP_NavEKF3/AP_NavEKF3_core.h:1105`). -/
  hgtTimeout : Bool := false
  /-- `bool magTimeout` of `NavEKF3_core` (`AP_NavEKF3/AP_NavEKF3_core.h:1106`). -/
  magTimeout : Bool := false
  /-- `bool tasTimeout` of `NavEKF3_core` (`AP_NavEKF3/AP_NavEKF3_core.h:1107`). -/
  tasTimeout : Bool := false
  /-- `bool dragTimeout` of `NavEKF3_core` (`AP_NavEKF3/AP_NavEKF3_core.h:1108`). -/
  dragTimeout : Bool := false
  /-- `bool badIMUdata` of `NavEKF3_core` (`AP_NavEKF3/AP_NavEKF3_core.h:1109`). -/
  badIMUdata : Bool := false
  /-- `bool velAiding` of `NavEKF3_core` (`AP_NavEKF3/AP_NavEKF3_core.h:1110`). -/
  velAiding : Bool := false
  /-- `bool waitingForGpsChecks` of `NavEKF3_core` (`AP_NavEKF3/AP_NavEKF3_core.h:1111`). -/
  waitingForGpsChecks : Bool := false
  /-- `uint32_t badIMUdata_ms` of `NavEKF3_core` (`AP_NavEKF3/AP_NavEKF3_core.h:1112`). -/
  badIMUdata_ms : UInt32 := (0 : UInt32)
  /-- `uint32_t goodIMUdata_ms` of `NavEKF3_core` (`AP_NavEKF3/AP_NavEKF3_core.h:1113`). -/
  goodIMUdata_ms : UInt32 := (0 : UInt32)
  /-- `uint32_t vertVelVarClipCounter` of `NavEKF3_core` (`AP_NavEKF3/AP_NavEKF3_core.h:1114`). -/
  vertVelVarClipCounter : UInt32 := (0 : UInt32)
  /-- `ftype gpsNoiseScaler` of `NavEKF3_core` (`AP_NavEKF3/AP_NavEKF3_core.h:1116`). -/
  gpsNoiseScaler : Binary64 := (Binary64.ofBits 0x0000000000000000 /- 0.0 -/)
  /-- `Matrix24 Pmut` of `NavEKF3_core` (`AP_NavEKF3/AP_NavEKF3_core.h:1117`). -/
  Pmut : Array Binary64 := Array.replicate 576 (Binary64.ofBits 0x0000000000000000 /- 0.0 -/)
  /-- `EKF_IMU_buffer_t<imu_elements> storedIMU` of `NavEKF3_core` (`AP_NavEKF3/AP_NavEKF3_core.h:1118`). -/
  storedIMU : EKF_IMU_buffer_t_NavEKF3_core_imu_elements.State := EKF_IMU_buffer_t_NavEKF3_core_imu_elements.construct
  /-- `EKF_obs_buffer_t<gps_elements> storedGPS` of `NavEKF3_core` (`AP_NavEKF3/AP_NavEKF3_core.h:1119`). -/
  storedGPS : EKF_obs_buffer_t_NavEKF3_core_gps_elements.State := EKF_obs_buffer_t_NavEKF3_core_gps_elements.construct
  /-- `EKF_obs_buffer_t<mag_elements> storedMag` of `NavEKF3_core` (`AP_NavEKF3/AP_NavEKF3_core.h:1120`). -/
  storedMag : EKF_obs_buffer_t_NavEKF3_core_mag_elements.State := EKF_obs_buffer_t_NavEKF3_core_mag_elements.construct
  /-- `EKF_obs_buffer_t<baro_elements> storedBaro` of `NavEKF3_core` (`AP_NavEKF3/AP_NavEKF3_core.h:1121`). -/
  storedBaro : EKF_obs_buffer_t_NavEKF3_core_baro_elements.State := EKF_obs_buffer_t_NavEKF3_core_baro_elements.construct
  /-- `class AirspeedFusion tas` of `NavEKF3_core` (`AP_NavEKF3/AP_NavEKF3_core.h:1139`). -/
  tas : NavEKF3_core.AirspeedFusion.State := {}
  /-- `EKF_IMU_buffer_t<output_elements> storedOutput` of `NavEKF3_core` (`AP_NavEKF3/AP_NavEKF3_core.h:1144`). -/
  storedOutput : EKF_IMU_buffer_t_NavEKF3_core_output_elements.State := EKF_IMU_buffer_t_NavEKF3_core_output_elements.construct
  /-- `Matrix3F prevTnb` of `NavEKF3_core` (`AP_NavEKF3/AP_NavEKF3_core.h:1145`). -/
  prevTnb : Matrix3_double.State := Matrix3_double.init_void
  /-- `ftype accNavMag` of `NavEKF3_core` (`AP_NavEKF3/AP_NavEKF3_core.h:1146`). -/
  accNavMag : Binary64 := (Binary64.ofBits 0x0000000000000000 /- 0.0 -/)
  /-- `ftype accNavMagHoriz` of `NavEKF3_core` (`AP_NavEKF3/AP_NavEKF3_core.h:1147`). -/
  accNavMagHoriz : Binary64 := (Binary64.ofBits 0x0000000000000000 /- 0.0 -/)
  /-- `Vector3F earthRateNED` of `NavEKF3_core` (`AP_NavEKF3/AP_NavEKF3_core.h:1148`). -/
  earthRateNED : Vector3p.State := {}
  /-- `ftype dtIMUavg` of `NavEKF3_core` (`AP_NavEKF3/AP_NavEKF3_core.h:1149`). -/
  dtIMUavg : Binary64 := (Binary64.ofBits 0x0000000000000000 /- 0.0 -/)
  /-- `ftype dtEkfAvg` of `NavEKF3_core` (`AP_NavEKF3/AP_NavEKF3_core.h:1150`). -/
  dtEkfAvg : Binary64 := (Binary64.ofBits 0x0000000000000000 /- 0.0 -/)
  /-- `ftype dt` of `NavEKF3_core` (`AP_NavEKF3/AP_NavEKF3_core.h:1151`). -/
  dt : Binary64 := (Binary64.ofBits 0x0000000000000000 /- 0.0 -/)
  /-- `ftype hgtRate` of `NavEKF3_core` (`AP_NavEKF3/AP_NavEKF3_core.h:1152`). -/
  hgtRate : Binary64 := (Binary64.ofBits 0x0000000000000000 /- 0.0 -/)
  /-- `bool onGround` of `NavEKF3_core` (`AP_NavEKF3/AP_NavEKF3_core.h:1153`). -/
  onGround : Bool := false
  /-- `bool prevOnGround` of `NavEKF3_core` (`AP_NavEKF3/AP_NavEKF3_core.h:1154`). -/
  prevOnGround : Bool := false
  /-- `bool inFlight` of `NavEKF3_core` (`AP_NavEKF3/AP_NavEKF3_core.h:1155`). -/
  inFlight : Bool := false
  /-- `bool prevInFlight` of `NavEKF3_core` (`AP_NavEKF3/AP_NavEKF3_core.h:1156`). -/
  prevInFlight : Bool := false
  /-- `bool manoeuvring` of `NavEKF3_core` (`AP_NavEKF3/AP_NavEKF3_core.h:1157`). -/
  manoeuvring : Bool := false
  /-- `bool fusingStationaryZeroVel` of `NavEKF3_core` (`AP_NavEKF3/AP_NavEKF3_core.h:1158`). -/
  fusingStationaryZeroVel : Bool := false
  /-- `Vector6 innovVelPos` of `NavEKF3_core` (`AP_NavEKF3/AP_NavEKF3_core.h:1159`). -/
  innovVelPos : Array Binary64 := Array.replicate 6 (Binary64.ofBits 0x0000000000000000 /- 0.0 -/)
  /-- `Vector6 varInnovVelPos` of `NavEKF3_core` (`AP_NavEKF3/AP_NavEKF3_core.h:1160`). -/
  varInnovVelPos : Array Binary64 := Array.replicate 6 (Binary64.ofBits 0x0000000000000000 /- 0.0 -/)
  /-- `Vector6 velPosObs` of `NavEKF3_core` (`AP_NavEKF3/AP_NavEKF3_core.h:1161`). -/
  velPosObs : Array Binary64 := Array.replicate 6 (Binary64.ofBits 0x0000000000000000 /- 0.0 -/)
  /-- `bool fuseVelData` of `NavEKF3_core` (`AP_NavEKF3/AP_NavEKF3_core.h:1162`). -/
  fuseVelData : Bool := false
  /-- `bool fuseVelVertData` of `NavEKF3_core` (`AP_NavEKF3/AP_NavEKF3_core.h:1163`). -/
  fuseVelVertData : Bool := false
  /-- `bool fusePosData` of `NavEKF3_core` (`AP_NavEKF3/AP_NavEKF3_core.h:1164`). -/
  fusePosData : Bool := false
  /-- `bool fuseHgtData` of `NavEKF3_core` (`AP_NavEKF3/AP_NavEKF3_core.h:1165`). -/
  fuseHgtData : Bool := false
  /-- `Vector3F innovMag` of `NavEKF3_core` (`AP_NavEKF3/AP_NavEKF3_core.h:1166`). -/
  innovMag : Vector3p.State := {}
  /-- `Vector3F varInnovMag` of `NavEKF3_core` (`AP_NavEKF3/AP_NavEKF3_core.h:1167`). -/
  varInnovMag : Vector3p.State := {}
  /-- `ftype defaultAirSpeed` of `NavEKF3_core` (`AP_NavEKF3/AP_NavEKF3_core.h:1168`). -/
  defaultAirSpeed : Binary64 := (Binary64.ofBits 0x0000000000000000 /- 0.0 -/)
  /-- `ftype defaultAirSpeedVariance` of `NavEKF3_core` (`AP_NavEKF3/AP_NavEKF3_core.h:1169`). -/
  defaultAirSpeedVariance : Binary64 := (Binary64.ofBits 0x0000000000000000 /- 0.0 -/)
  /-- `bool magFusePerformed` of `NavEKF3_core` (`AP_NavEKF3/AP_NavEKF3_core.h:1170`). -/
  magFusePerformed : Bool := false
  /-- `MagCal effectiveMagCal` of `NavEKF3_core` (`AP_NavEKF3/AP_NavEKF3_core.h:1171`). -/
  effectiveMagCal : NavEKF3_core.MagCal := NavEKF3_core.MagCal.WHEN_FLYING
  /-- `uint32_t prevBetaDragStep_ms` of `NavEKF3_core` (`AP_NavEKF3/AP_NavEKF3_core.h:1172`). -/
  prevBetaDragStep_ms : UInt32 := (0 : UInt32)
  /-- `ftype innovBeta` of `NavEKF3_core` (`AP_NavEKF3/AP_NavEKF3_core.h:1173`). -/
  innovBeta : Binary64 := (Binary64.ofBits 0x0000000000000000 /- 0.0 -/)
  /-- `uint32_t lastMagUpdate_us` of `NavEKF3_core` (`AP_NavEKF3/AP_NavEKF3_core.h:1174`). -/
  lastMagUpdate_us : UInt32 := (0 : UInt32)
  /-- `uint32_t lastMagRead_ms` of `NavEKF3_core` (`AP_NavEKF3/AP_NavEKF3_core.h:1175`). -/
  lastMagRead_ms : UInt32 := (0 : UInt32)
  /-- `Vector3F velDotNED` of `NavEKF3_core` (`AP_NavEKF3/AP_NavEKF3_core.h:1176`). -/
  velDotNED : Vector3p.State := {}
  /-- `Vector3F velDotNEDfilt` of `NavEKF3_core` (`AP_NavEKF3/AP_NavEKF3_core.h:1177`). -/
  velDotNEDfilt : Vector3p.State := {}
  /-- `uint32_t imuSampleTime_ms` of `NavEKF3_core` (`AP_NavEKF3/AP_NavEKF3_core.h:1178`). -/
  imuSampleTime_ms : UInt32 := (0 : UInt32)
  /-- `uint32_t lastBaroReceived_ms` of `NavEKF3_core` (`AP_NavEKF3/AP_NavEKF3_core.h:1179`). -/
  lastBaroReceived_ms : UInt32 := (0 : UInt32)
  /-- `uint16_t hgtRetryTime_ms` of `NavEKF3_core` (`AP_NavEKF3/AP_NavEKF3_core.h:1180`). -/
  hgtRetryTime_ms : UInt16 := (0 : UInt16)
  /-- `uint32_t lastVelPassTime_ms` of `NavEKF3_core` (`AP_NavEKF3/AP_NavEKF3_core.h:1181`). -/
  lastVelPassTime_ms : UInt32 := (0 : UInt32)
  /-- `uint32_t lastGpsPosPassTime_ms` of `NavEKF3_core` (`AP_NavEKF3/AP_NavEKF3_core.h:1182`). -/
  lastGpsPosPassTime_ms : UInt32 := (0 : UInt32)
  /-- `uint32_t lastHgtPassTime_ms` of `NavEKF3_core` (`AP_NavEKF3/AP_NavEKF3_core.h:1183`). -/
  lastHgtPassTime_ms : UInt32 := (0 : UInt32)
  /-- `uint32_t lastTimeGpsReceived_ms` of `NavEKF3_core` (`AP_NavEKF3/AP_NavEKF3_core.h:1184`). -/
  lastTimeGpsReceived_ms : UInt32 := (0 : UInt32)
  /-- `uint32_t timeAtLastAuxEKF_ms` of `NavEKF3_core` (`AP_NavEKF3/AP_NavEKF3_core.h:1185`). -/
  timeAtLastAuxEKF_ms : UInt32 := (0 : UInt32)
  /-- `uint32_t lastHealthyMagTime_ms` of `NavEKF3_core` (`AP_NavEKF3/AP_NavEKF3_core.h:1186`). -/
  lastHealthyMagTime_ms : UInt32 := (0 : UInt32)
  /-- `uint32_t last_mag_yaw_fuse_ms` of `NavEKF3_core` (`AP_NavEKF3/AP_NavEKF3_core.h:1187`). -/
  last_mag_yaw_fuse_ms : UInt32 := (0 : UInt32)
  /-- `bool allMagSensorsFailed` of `NavEKF3_core` (`AP_NavEKF3/AP_NavEKF3_core.h:1188`). -/
  allMagSensorsFailed : Bool := false
  /-- `uint32_t lastSynthYawTime_ms` of `NavEKF3_core` (`AP_NavEKF3/AP_NavEKF3_core.h:1189`). -/
  lastSynthYawTime_ms : UInt32 := (0 : UInt32)
  /-- `uint32_t ekfStartTime_ms` of `NavEKF3_core` (`AP_NavEKF3/AP_NavEKF3_core.h:1190`). -/
  ekfStartTime_ms : UInt32 := (0 : UInt32)
  /-- `Vector2F lastKnownPositionNE` of `NavEKF3_core` (`AP_NavEKF3/AP_NavEKF3_core.h:1191`). -/
  lastKnownPositionNE : Vector2p.State := {}
  /-- `float lastKnownPositionD` of `NavEKF3_core` (`AP_NavEKF3/AP_NavEKF3_core.h:1192`). -/
  lastKnownPositionD : Binary32 := (Binary32.ofBits 0x00000000 /- 0.0 -/)
  /-- `uint32_t lastLaunchAccelTime_ms` of `NavEKF3_core` (`AP_NavEKF3/AP_NavEKF3_core.h:1193`). -/
  lastLaunchAccelTime_ms : UInt32 := (0 : UInt32)
  /-- `ftype velTestRatio` of `NavEKF3_core` (`AP_NavEKF3/AP_NavEKF3_core.h:1194`). -/
  velTestRatio : Binary64 := (Binary64.ofBits 0x0000000000000000 /- 0.0 -/)
  /-- `ftype posTestRatio` of `NavEKF3_core` (`AP_NavEKF3/AP_NavEKF3_core.h:1195`). -/
  posTestRatio : Binary64 := (Binary64.ofBits 0x0000000000000000 /- 0.0 -/)
  /-- `ftype hgtTestRatio` of `NavEKF3_core` (`AP_NavEKF3/AP_NavEKF3_core.h:1196`). -/
  hgtTestRatio : Binary64 := (Binary64.ofBits 0x0000000000000000 /- 0.0 -/)
  /-- `Vector3F magTestRatio` of `NavEKF3_core` (`AP_NavEKF3/AP_NavEKF3_core.h:1197`). -/
  magTestRatio : Vector3p.State := {}
  /-- `bool inhibitWindStates` of `NavEKF3_core` (`AP_NavEKF3/AP_NavEKF3_core.h:1198`). -/
  inhibitWindStates : Bool := false
  /-- `ftype lastAirspeedEstimate` of `NavEKF3_core` (`AP_NavEKF3/AP_NavEKF3_core.h:1199`). -/
  lastAirspeedEstimate : Binary64 := (Binary64.ofBits 0x0000000000000000 /- 0.0 -/)
  /-- `bool lastAspdEstIsValid` of `NavEKF3_core` (`AP_NavEKF3/AP_NavEKF3_core.h:1200`). -/
  lastAspdEstIsValid : Bool := false
  /-- `bool windStateIsObservable` of `NavEKF3_core` (`AP_NavEKF3/AP_NavEKF3_core.h:1201`). -/
  windStateIsObservable : Bool := false
  /-- `bool treatWindStatesAsTruth` of `NavEKF3_core` (`AP_NavEKF3/AP_NavEKF3_core.h:1202`). -/
  treatWindStatesAsTruth : Bool := false
  /-- `bool windStatesAligned` of `NavEKF3_core` (`AP_NavEKF3/AP_NavEKF3_core.h:1203`). -/
  windStatesAligned : Bool := false
  /-- `bool inhibitMagStates` of `NavEKF3_core` (`AP_NavEKF3/AP_NavEKF3_core.h:1204`). -/
  inhibitMagStates : Bool := false
  /-- `bool lastInhibitMagStates` of `NavEKF3_core` (`AP_NavEKF3/AP_NavEKF3_core.h:1205`). -/
  lastInhibitMagStates : Bool := false
  /-- `bool needMagBodyVarReset` of `NavEKF3_core` (`AP_NavEKF3/AP_NavEKF3_core.h:1206`). -/
  needMagBodyVarReset : Bool := false
  /-- `bool needEarthBodyVarReset` of `NavEKF3_core` (`AP_NavEKF3/AP_NavEKF3_core.h:1207`). -/
  needEarthBodyVarReset : Bool := false
  /-- `bool inhibitDelAngBiasStates` of `NavEKF3_core` (`AP_NavEKF3/AP_NavEKF3_core.h:1208`). -/
  inhibitDelAngBiasStates : Bool := false
  /-- `bool gpsIsInUse` of `NavEKF3_core` (`AP_NavEKF3/AP_NavEKF3_core.h:1209`). -/
  gpsIsInUse : Bool := false
  /-- `Location EKF_origin` of `NavEKF3_core` (`AP_NavEKF3/AP_NavEKF3_core.h:1210`). -/
  EKF_origin : Location.State := {}
  /-- `bool validOrigin` of `NavEKF3_core` (`AP_NavEKF3/AP_NavEKF3_core.h:1212`). -/
  validOrigin : Bool := false
  /-- `ftype gpsSpdAccuracy` of `NavEKF3_core` (`AP_NavEKF3/AP_NavEKF3_core.h:1213`). -/
  gpsSpdAccuracy : Binary64 := (Binary64.ofBits 0x0000000000000000 /- 0.0 -/)
  /-- `ftype gpsPosAccuracy` of `NavEKF3_core` (`AP_NavEKF3/AP_NavEKF3_core.h:1214`). -/
  gpsPosAccuracy : Binary64 := (Binary64.ofBits 0x0000000000000000 /- 0.0 -/)
  /-- `ftype gpsHgtAccuracy` of `NavEKF3_core` (`AP_NavEKF3/AP_NavEKF3_core.h:1215`). -/
  gpsHgtAccuracy : Binary64 := (Binary64.ofBits 0x0000000000000000 /- 0.0 -/)
  /-- `uint32_t lastGpsVelFail_ms` of `NavEKF3_core` (`AP_NavEKF3/AP_NavEKF3_core.h:1216`). -/
  lastGpsVelFail_ms : UInt32 := (0 : UInt32)
  /-- `uint32_t lastGpsVelPass_ms` of `NavEKF3_core` (`AP_NavEKF3/AP_NavEKF3_core.h:1217`). -/
  lastGpsVelPass_ms : UInt32 := (0 : UInt32)
  /-- `uint32_t lastGpsAidBadTime_ms` of `NavEKF3_core` (`AP_NavEKF3/AP_NavEKF3_core.h:1218`). -/
  lastGpsAidBadTime_ms : UInt32 := (0 : UInt32)
  /-- `ftype posDownAtTakeoff` of `NavEKF3_core` (`AP_NavEKF3/AP_NavEKF3_core.h:1219`). -/
  posDownAtTakeoff : Binary64 := (Binary64.ofBits 0x0000000000000000 /- 0.0 -/)
  /-- `bool useGpsVertVel` of `NavEKF3_core` (`AP_NavEKF3/AP_NavEKF3_core.h:1220`). -/
  useGpsVertVel : Bool := false
  /-- `uint16_t yawResetCount` of `NavEKF3_core` (`AP_NavEKF3/AP_NavEKF3_core.h:1221`). -/
  yawResetCount : UInt16 := (0 : UInt16)
  /-- `bool tiltAlignComplete` of `NavEKF3_core` (`AP_NavEKF3/AP_NavEKF3_core.h:1222`). -/
  tiltAlignComplete : Bool := false
  /-- `bool yawAlignComplete` of `NavEKF3_core` (`AP_NavEKF3/AP_NavEKF3_core.h:1223`). -/
  yawAlignComplete : Bool := false
  /-- `uint8_t yawAlignGpsValidCount` of `NavEKF3_core` (`AP_NavEKF3/AP_NavEKF3_core.h:1224`). -/
  yawAlignGpsValidCount : UInt8 := (0 : UInt8)
  /-- `bool magStateInitComplete` of `NavEKF3_core` (`AP_NavEKF3/AP_NavEKF3_core.h:1225`). -/
  magStateInitComplete : Bool := false
  /-- `uint8_t stateIndexLim` of `NavEKF3_core` (`AP_NavEKF3/AP_NavEKF3_core.h:1226`). -/
  stateIndexLim : UInt8 := (0 : UInt8)
  /-- `imu_elements imuDataDelayed` of `NavEKF3_core` (`AP_NavEKF3/AP_NavEKF3_core.h:1227`). -/
  imuDataDelayed : NavEKF3_core.imu_elements := {}
  /-- `imu_elements imuDataNew` of `NavEKF3_core` (`AP_NavEKF3/AP_NavEKF3_core.h:1228`). -/
  imuDataNew : NavEKF3_core.imu_elements := {}
  /-- `imu_elements imuDataDownSampledNew` of `NavEKF3_core` (`AP_NavEKF3/AP_NavEKF3_core.h:1229`). -/
  imuDataDownSampledNew : NavEKF3_core.imu_elements := {}
  /-- `QuaternionF imuQuatDownSampleNew` of `NavEKF3_core` (`AP_NavEKF3/AP_NavEKF3_core.h:1230`). -/
  imuQuatDownSampleNew : QuaternionT_double.State := QuaternionT_double.init_void
  /-- `baro_elements baroDataNew` of `NavEKF3_core` (`AP_NavEKF3/AP_NavEKF3_core.h:1231`). -/
  baroDataNew : NavEKF3_core.baro_elements := {}
  /-- `baro_elements baroDataDelayed` of `NavEKF3_core` (`AP_NavEKF3/AP_NavEKF3_core.h:1232`). -/
  baroDataDelayed : NavEKF3_core.baro_elements := {}
  /-- `range_elements rangeDataNew` of `NavEKF3_core` (`AP_NavEKF3/AP_NavEKF3_core.h:1233`). -/
  rangeDataNew : NavEKF3_core.range_elements := {}
  /-- `range_elements rangeDataDelayed` of `NavEKF3_core` (`AP_NavEKF3/AP_NavEKF3_core.h:1234`). -/
  rangeDataDelayed : NavEKF3_core.range_elements := {}
  /-- `mag_elements magDataDelayed` of `NavEKF3_core` (`AP_NavEKF3/AP_NavEKF3_core.h:1235`). -/
  magDataDelayed : NavEKF3_core.mag_elements := {}
  /-- `gps_elements gpsDataNew` of `NavEKF3_core` (`AP_NavEKF3/AP_NavEKF3_core.h:1236`). -/
  gpsDataNew : NavEKF3_core.gps_elements := {}
  /-- `gps_elements gpsDataDelayed` of `NavEKF3_core` (`AP_NavEKF3/AP_NavEKF3_core.h:1237`). -/
  gpsDataDelayed : NavEKF3_core.gps_elements := {}
  /-- `uint8_t last_gps_idx` of `NavEKF3_core` (`AP_NavEKF3/AP_NavEKF3_core.h:1238`). -/
  last_gps_idx : UInt8 := (0 : UInt8)
  /-- `output_elements outputDataNew` of `NavEKF3_core` (`AP_NavEKF3/AP_NavEKF3_core.h:1239`). -/
  outputDataNew : NavEKF3_core.output_elements := {}
  /-- `output_elements outputDataDelayed` of `NavEKF3_core` (`AP_NavEKF3/AP_NavEKF3_core.h:1240`). -/
  outputDataDelayed : NavEKF3_core.output_elements := {}
  /-- `Vector3F delAngCorrection` of `NavEKF3_core` (`AP_NavEKF3/AP_NavEKF3_core.h:1241`). -/
  delAngCorrection : Vector3p.State := {}
  /-- `Vector3F velErrintegral` of `NavEKF3_core` (`AP_NavEKF3/AP_NavEKF3_core.h:1242`). -/
  velErrintegral : Vector3p.State := {}
  /-- `Vector3F posErrintegral` of `NavEKF3_core` (`AP_NavEKF3/AP_NavEKF3_core.h:1243`). -/
  posErrintegral : Vector3p.State := {}
  /-- `ftype badImuVelErrIntegral` of `NavEKF3_core` (`AP_NavEKF3/AP_NavEKF3_core.h:1244`). -/
  badImuVelErrIntegral : Binary64 := (Binary64.ofBits 0x0000000000000000 /- 0.0 -/)
  /-- `ftype innovYaw` of `NavEKF3_core` (`AP_NavEKF3/AP_NavEKF3_core.h:1245`). -/
  innovYaw : Binary64 := (Binary64.ofBits 0x0000000000000000 /- 0.0 -/)
  /-- `bool gpsGoodToAlign` of `NavEKF3_core` (`AP_NavEKF3/AP_NavEKF3_core.h:1246`). -/
  gpsGoodToAlign : Bool := false
  /-- `uint32_t magYawResetTimer_ms` of `NavEKF3_core` (`AP_NavEKF3/AP_NavEKF3_core.h:1247`). -/
  magYawResetTimer_ms : UInt32 := (0 : UInt32)
  /-- `bool consistentMagData` of `NavEKF3_core` (`AP_NavEKF3/AP_NavEKF3_core.h:1248`). -/
  consistentMagData : Bool := false
  /-- `bool motorsArmed` of `NavEKF3_core` (`AP_NavEKF3/AP_NavEKF3_core.h:1249`). -/
  motorsArmed : Bool := false
  /-- `bool prevMotorsArmed` of `NavEKF3_core` (`AP_NavEKF3/AP_NavEKF3_core.h:1250`). -/
  prevMotorsArmed : Bool := false
  /-- `bool posVelFusionDelayed` of `NavEKF3_core` (`AP_NavEKF3/AP_NavEKF3_core.h:1251`). -/
  posVelFusionDelayed : Bool := false
  /-- `bool airSpdFusionDelayed` of `NavEKF3_core` (`AP_NavEKF3/AP_NavEKF3_core.h:1255`). -/
  airSpdFusionDelayed : Bool := false
  /-- `bool sideSlipFusionDelayed` of `NavEKF3_core` (`AP_NavEKF3/AP_NavEKF3_core.h:1256`). -/
  sideSlipFusionDelayed : Bool := false
  /-- `bool airDataFusionWindOnly` of `NavEKF3_core` (`AP_NavEKF3/AP_NavEKF3_core.h:1257`). -/
  airDataFusionWindOnly : Bool := false
  /-- `Vector3F lastMagOffsets` of `NavEKF3_core` (`AP_NavEKF3/AP_NavEKF3_core.h:1258`). -/
  lastMagOffsets : Vector3p.State := {}
  /-- `bool lastMagOffsetsValid` of `NavEKF3_core` (`AP_NavEKF3/AP_NavEKF3_core.h:1259`). -/
  lastMagOffsetsValid : Bool := false
  /-- `Vector2F posResetNE` of `NavEKF3_core` (`AP_NavEKF3/AP_NavEKF3_core.h:1260`). -/
  posResetNE : Vector2p.State := {}
  /-- `ftype posResetD` of `NavEKF3_core` (`AP_NavEKF3/AP_NavEKF3_core.h:1261`). -/
  posResetD : Binary64 := (Binary64.ofBits 0x0000000000000000 /- 0.0 -/)
  /-- `uint16_t posNEResetCount` of `NavEKF3_core` (`AP_NavEKF3/AP_NavEKF3_core.h:1262`). -/
  posNEResetCount : UInt16 := (0 : UInt16)
  /-- `uint16_t posDResetCount` of `NavEKF3_core` (`AP_NavEKF3/AP_NavEKF3_core.h:1263`). -/
  posDResetCount : UInt16 := (0 : UInt16)
  /-- `ftype yawTestRatio` of `NavEKF3_core` (`AP_NavEKF3/AP_NavEKF3_core.h:1264`). -/
  yawTestRatio : Binary64 := (Binary64.ofBits 0x0000000000000000 /- 0.0 -/)
  /-- `QuaternionF prevQuatMagReset` of `NavEKF3_core` (`AP_NavEKF3/AP_NavEKF3_core.h:1265`). -/
  prevQuatMagReset : QuaternionT_double.State := QuaternionT_double.init_void
  /-- `ftype hgtInnovFiltState` of `NavEKF3_core` (`AP_NavEKF3/AP_NavEKF3_core.h:1266`). -/
  hgtInnovFiltState : Binary64 := (Binary64.ofBits 0x0000000000000000 /- 0.0 -/)
  /-- `uint8_t magSelectIndex` of `NavEKF3_core` (`AP_NavEKF3/AP_NavEKF3_core.h:1267`). -/
  magSelectIndex : UInt8 := (0 : UInt8)
  /-- `bool runUpdates` of `NavEKF3_core` (`AP_NavEKF3/AP_NavEKF3_core.h:1268`). -/
  runUpdates : Bool := false
  /-- `uint32_t framesSincePredict` of `NavEKF3_core` (`AP_NavEKF3/AP_NavEKF3_core.h:1269`). -/
  framesSincePredict : UInt32 := (0 : UInt32)
  /-- `uint8_t localFilterTimeStep_ms` of `NavEKF3_core` (`AP_NavEKF3/AP_NavEKF3_core.h:1270`). -/
  localFilterTimeStep_ms : UInt8 := (0 : UInt8)
  /-- `ftype posDownObsNoise` of `NavEKF3_core` (`AP_NavEKF3/AP_NavEKF3_core.h:1271`). -/
  posDownObsNoise : Binary64 := (Binary64.ofBits 0x0000000000000000 /- 0.0 -/)
  /-- `Vector3F delAngCorrected` of `NavEKF3_core` (`AP_NavEKF3/AP_NavEKF3_core.h:1272`). -/
  delAngCorrected : Vector3p.State := {}
  /-- `Vector3F delVelCorrected` of `NavEKF3_core` (`AP_NavEKF3/AP_NavEKF3_core.h:1273`). -/
  delVelCorrected : Vector3p.State := {}
  /-- `bool magFieldLearned` of `NavEKF3_core` (`AP_NavEKF3/AP_NavEKF3_core.h:1274`). -/
  magFieldLearned : Bool := false
  /-- `uint32_t wasLearningCompass_ms` of `NavEKF3_core` (`AP_NavEKF3/AP_NavEKF3_core.h:1275`). -/
  wasLearningCompass_ms : UInt32 := (0 : UInt32)
  /-- `Vector3F earthMagFieldVar` of `NavEKF3_core` (`AP_NavEKF3/AP_NavEKF3_core.h:1276`). -/
  earthMagFieldVar : Vector3p.State := {}
  /-- `Vector3F bodyMagFieldVar` of `NavEKF3_core` (`AP_NavEKF3/AP_NavEKF3_core.h:1277`). -/
  bodyMagFieldVar : Vector3p.State := {}
  /-- `bool delAngBiasLearned` of `NavEKF3_core` (`AP_NavEKF3/AP_NavEKF3_core.h:1278`). -/
  delAngBiasLearned : Bool := false
  /-- `nav_filter_status filterStatus` of `NavEKF3_core` (`AP_NavEKF3/AP_NavEKF3_core.h:1279`). -/
  filterStatus : UInt32 := (0 : UInt32)
  /-- `ftype ekfOriginHgtVar` of `NavEKF3_core` (`AP_NavEKF3/AP_NavEKF3_core.h:1280`). -/
  ekfOriginHgtVar : Binary64 := (Binary64.ofBits 0x0000000000000000 /- 0.0 -/)
  /-- `double ekfGpsRefHgt` of `NavEKF3_core` (`AP_NavEKF3/AP_NavEKF3_core.h:1281`). -/
  ekfGpsRefHgt : Binary64 := (Binary64.ofBits 0x0000000000000000 /- 0.0 -/)
  /-- `uint32_t lastOriginHgtTime_ms` of `NavEKF3_core` (`AP_NavEKF3/AP_NavEKF3_core.h:1282`). -/
  lastOriginHgtTime_ms : UInt32 := (0 : UInt32)
  /-- `Vector3F outputTrackError` of `NavEKF3_core` (`AP_NavEKF3/AP_NavEKF3_core.h:1283`). -/
  outputTrackError : Vector3p.State := {}
  /-- `Vector3F velOffsetNED` of `NavEKF3_core` (`AP_NavEKF3/AP_NavEKF3_core.h:1284`). -/
  velOffsetNED : Vector3p.State := {}
  /-- `Vector3F posOffsetNED` of `NavEKF3_core` (`AP_NavEKF3/AP_NavEKF3_core.h:1285`). -/
  posOffsetNED : Vector3p.State := {}
  /-- `uint32_t firstInitTime_ms` of `NavEKF3_core` (`AP_NavEKF3/AP_NavEKF3_core.h:1286`). -/
  firstInitTime_ms : UInt32 := (0 : UInt32)
  /-- `uint32_t lastInitFailReport_ms` of `NavEKF3_core` (`AP_NavEKF3/AP_NavEKF3_core.h:1287`). -/
  lastInitFailReport_ms : UInt32 := (0 : UInt32)
  /-- `ftype tiltErrorVariance` of `NavEKF3_core` (`AP_NavEKF3/AP_NavEKF3_core.h:1288`). -/
  tiltErrorVariance : Binary64 := (Binary64.ofBits 0x0000000000000000 /- 0.0 -/)
  /-- `struct (unnamed struct at AP_NavEKF3/AP_NavEKF3_core.h:1291:5) vertCompFiltState` of `NavEKF3_core` (`AP_NavEKF3/AP_NavEKF3_core.h:1295`). -/
  vertCompFiltState : NavEKF3_core.vertCompFiltState_t := {}
  /-- `Location gpsloc_prev` of `NavEKF3_core` (`AP_NavEKF3/AP_NavEKF3_core.h:1298`). -/
  gpsloc_prev : Location.State := {}
  /-- `uint32_t lastPreAlignGpsCheckTime_ms` of `NavEKF3_core` (`AP_NavEKF3/AP_NavEKF3_core.h:1299`). -/
  lastPreAlignGpsCheckTime_ms : UInt32 := (0 : UInt32)
  /-- `ftype gpsDriftNE` of `NavEKF3_core` (`AP_NavEKF3/AP_NavEKF3_core.h:1300`). -/
  gpsDriftNE : Binary64 := (Binary64.ofBits 0x0000000000000000 /- 0.0 -/)
  /-- `ftype gpsVertVelFilt` of `NavEKF3_core` (`AP_NavEKF3/AP_NavEKF3_core.h:1301`). -/
  gpsVertVelFilt : Binary64 := (Binary64.ofBits 0x0000000000000000 /- 0.0 -/)
  /-- `ftype gpsHorizVelFilt` of `NavEKF3_core` (`AP_NavEKF3/AP_NavEKF3_core.h:1302`). -/
  gpsHorizVelFilt : Binary64 := (Binary64.ofBits 0x0000000000000000 /- 0.0 -/)
  /-- `bool gpsSpdAccPass` of `NavEKF3_core` (`AP_NavEKF3/AP_NavEKF3_core.h:1305`). -/
  gpsSpdAccPass : Bool := false
  /-- `bool gpsVertAccPass` of `NavEKF3_core` (`AP_NavEKF3/AP_NavEKF3_core.h:1306`). -/
  gpsVertAccPass : Bool := false
  /-- `bool ekfInnovationsPass` of `NavEKF3_core` (`AP_NavEKF3/AP_NavEKF3_core.h:1307`). -/
  ekfInnovationsPass : Bool := false
  /-- `ftype sAccFilterState1` of `NavEKF3_core` (`AP_NavEKF3/AP_NavEKF3_core.h:1308`). -/
  sAccFilterState1 : Binary64 := (Binary64.ofBits 0x0000000000000000 /- 0.0 -/)
  /-- `ftype sAccFilterState2` of `NavEKF3_core` (`AP_NavEKF3/AP_NavEKF3_core.h:1309`). -/
  sAccFilterState2 : Binary64 := (Binary64.ofBits 0x0000000000000000 /- 0.0 -/)
  /-- `uint32_t lastGpsCheckTime_ms` of `NavEKF3_core` (`AP_NavEKF3/AP_NavEKF3_core.h:1310`). -/
  lastGpsCheckTime_ms : UInt32 := (0 : UInt32)
  /-- `uint32_t lastGpsInnovPassTime_ms` of `NavEKF3_core` (`AP_NavEKF3/AP_NavEKF3_core.h:1311`). -/
  lastGpsInnovPassTime_ms : UInt32 := (0 : UInt32)
  /-- `uint32_t lastGpsInnovFailTime_ms` of `NavEKF3_core` (`AP_NavEKF3/AP_NavEKF3_core.h:1312`). -/
  lastGpsInnovFailTime_ms : UInt32 := (0 : UInt32)
  /-- `uint32_t lastGpsVertAccPassTime_ms` of `NavEKF3_core` (`AP_NavEKF3/AP_NavEKF3_core.h:1313`). -/
  lastGpsVertAccPassTime_ms : UInt32 := (0 : UInt32)
  /-- `uint32_t lastGpsVertAccFailTime_ms` of `NavEKF3_core` (`AP_NavEKF3/AP_NavEKF3_core.h:1314`). -/
  lastGpsVertAccFailTime_ms : UInt32 := (0 : UInt32)
  /-- `bool gpsAccuracyGood` of `NavEKF3_core` (`AP_NavEKF3/AP_NavEKF3_core.h:1315`). -/
  gpsAccuracyGood : Bool := false
  /-- `bool gpsAccuracyGoodForAltitude` of `NavEKF3_core` (`AP_NavEKF3/AP_NavEKF3_core.h:1316`). -/
  gpsAccuracyGoodForAltitude : Bool := false
  /-- `Vector3F gpsVelInnov` of `NavEKF3_core` (`AP_NavEKF3/AP_NavEKF3_core.h:1317`). -/
  gpsVelInnov : Vector3p.State := {}
  /-- `Vector3F gpsVelVarInnov` of `NavEKF3_core` (`AP_NavEKF3/AP_NavEKF3_core.h:1318`). -/
  gpsVelVarInnov : Vector3p.State := {}
  /-- `uint32_t gpsRetrieveTime_ms` of `NavEKF3_core` (`AP_NavEKF3/AP_NavEKF3_core.h:1319`). -/
  gpsRetrieveTime_ms : UInt32 := (0 : UInt32)
  /-- `EKF_obs_buffer_t<of_elements> storedOF` of `NavEKF3_core` (`AP_NavEKF3/AP_NavEKF3_core.h:1322`). -/
  storedOF : EKF_obs_buffer_t_NavEKF3_core_of_elements.State := EKF_obs_buffer_t_NavEKF3_core_of_elements.construct
  /-- `bool flowDataValid` of `NavEKF3_core` (`AP_NavEKF3/AP_NavEKF3_core.h:1323`). -/
  flowDataValid : Bool := false
  /-- `Vector2F auxFlowObsInnov` of `NavEKF3_core` (`AP_NavEKF3/AP_NavEKF3_core.h:1324`). -/
  auxFlowObsInnov : Vector2p.State := {}
  /-- `uint32_t flowValidMeaTime_ms` of `NavEKF3_core` (`AP_NavEKF3/AP_NavEKF3_core.h:1325`). -/
  flowValidMeaTime_ms : UInt32 := (0 : UInt32)
  /-- `uint32_t rngValidMeaTime_ms` of `NavEKF3_core` (`AP_NavEKF3/AP_NavEKF3_core.h:1326`). -/
  rngValidMeaTime_ms : UInt32 := (0 : UInt32)
  /-- `uint32_t flowMeaTime_ms` of `NavEKF3_core` (`AP_NavEKF3/AP_NavEKF3_core.h:1327`). -/
  flowMeaTime_ms : UInt32 := (0 : UInt32)
  /-- `uint32_t gndHgtValidTime_ms` of `NavEKF3_core` (`AP_NavEKF3/AP_NavEKF3_core.h:1328`). -/
  gndHgtValidTime_ms : UInt32 := (0 : UInt32)
  /-- `Vector2 flowVarInnov` of `NavEKF3_core` (`AP_NavEKF3/AP_NavEKF3_core.h:1329`). -/
  flowVarInnov : Array Binary64 := Array.replicate 2 (Binary64.ofBits 0x0000000000000000 /- 0.0 -/)
  /-- `Vector2 flowInnov` of `NavEKF3_core` (`AP_NavEKF3/AP_NavEKF3_core.h:1330`). -/
  flowInnov : Array Binary64 := Array.replicate 2 (Binary64.ofBits 0x0000000000000000 /- 0.0 -/)
  /-- `uint32_t flowInnovTime_ms` of `NavEKF3_core` (`AP_NavEKF3/AP_NavEKF3_core.h:1331`). -/
  flowInnovTime_ms : UInt32 := (0 : UInt32)
  /-- `ftype terrainState` of `NavEKF3_core` (`AP_NavEKF3/AP_NavEKF3_core.h:1352`). -/
  terrainState : Binary64 := (Binary64.ofBits 0x0000000000000000 /- 0.0 -/)
  /-- `ftype prevPosN` of `NavEKF3_core` (`AP_NavEKF3/AP_NavEKF3_core.h:1353`). -/
  prevPosN : Binary64 := (Binary64.ofBits 0x0000000000000000 /- 0.0 -/)
  /-- `ftype prevPosE` of `NavEKF3_core` (`AP_NavEKF3/AP_NavEKF3_core.h:1354`). -/
  prevPosE : Binary64 := (Binary64.ofBits 0x0000000000000000 /- 0.0 -/)
  /-- `ftype varInnovRng` of `NavEKF3_core` (`AP_NavEKF3/AP_NavEKF3_core.h:1355`). -/
  varInnovRng : Binary64 := (Binary64.ofBits 0x0000000000000000 /- 0.0 -/)
  /-- `ftype innovRng` of `NavEKF3_core` (`AP_NavEKF3/AP_NavEKF3_core.h:1356`). -/
  innovRng : Binary64 := (Binary64.ofBits 0x0000000000000000 /- 0.0 -/)
  /-- `struct (unnamed struct at AP_NavEKF3/AP_NavEKF3_core.h:1357:5) flowCalSample` of `NavEKF3_core` (`AP_NavEKF3/AP_NavEKF3_core.h:1362`). -/
  flowCalSample : NavEKF3_core.flowCalSample_t := {}
  /-- `ftype hgtMea` of `NavEKF3_core` (`AP_NavEKF3/AP_NavEKF3_core.h:1371`). -/
  hgtMea : Binary64 := (Binary64.ofBits 0x0000000000000000 /- 0.0 -/)
  /-- `bool inhibitGndState` of `NavEKF3_core` (`AP_NavEKF3/AP_NavEKF3_core.h:1372`). -/
  inhibitGndState : Bool := false
  /-- `uint32_t prevFlowFuseTime_ms` of `NavEKF3_core` (`AP_NavEKF3/AP_NavEKF3_core.h:1373`). -/
  prevFlowFuseTime_ms : UInt32 := (0 : UInt32)
  /-- `Vector2 flowTestRatio` of `NavEKF3_core` (`AP_NavEKF3/AP_NavEKF3_core.h:1374`). -/
  flowTestRatio : Array Binary64 := Array.replicate 2 (Binary64.ofBits 0x0000000000000000 /- 0.0 -/)
  /-- `Vector2F auxFlowTestRatio` of `NavEKF3_core` (`AP_NavEKF3/AP_NavEKF3_core.h:1375`). -/
  auxFlowTestRatio : Vector2p.State := {}
  /-- `ftype R_LOS` of `NavEKF3_core` (`AP_NavEKF3/AP_NavEKF3_core.h:1376`). -/
  R_LOS : Binary64 := (Binary64.ofBits 0x0000000000000000 /- 0.0 -/)
  /-- `ftype auxRngTestRatio` of `NavEKF3_core` (`AP_NavEKF3/AP_NavEKF3_core.h:1377`). -/
  auxRngTestRatio : Binary64 := (Binary64.ofBits 0x0000000000000000 /- 0.0 -/)
  /-- `Vector2F flowGyroBias` of `NavEKF3_core` (`AP_NavEKF3/AP_NavEKF3_core.h:1378`). -/
  flowGyroBias : Vector2p.State := {}
  /-- `bool rangeDataToFuse` of `NavEKF3_core` (`AP_NavEKF3/AP_NavEKF3_core.h:1379`). -/
  rangeDataToFuse : Bool := false
  /-- `bool baroDataToFuse` of `NavEKF3_core` (`AP_NavEKF3/AP_NavEKF3_core.h:1380`). -/
  baroDataToFuse : Bool := false
  /-- `bool gpsDataToFuse` of `NavEKF3_core` (`AP_NavEKF3/AP_NavEKF3_core.h:1381`). -/
  gpsDataToFuse : Bool := false
  /-- `bool magDataToFuse` of `NavEKF3_core` (`AP_NavEKF3/AP_NavEKF3_core.h:1382`). -/
  magDataToFuse : Bool := false
  /-- `AidingMode PV_AidingMode` of `NavEKF3_core` (`AP_NavEKF3/AP_NavEKF3_core.h:1388`). -/
  PV_AidingMode : NavEKF3_core.AidingMode := NavEKF3_core.AidingMode.AID_ABSOLUTE
  /-- `AidingMode PV_AidingModePrev` of `NavEKF3_core` (`AP_NavEKF3/AP_NavEKF3_core.h:1389`). -/
  PV_AidingModePrev : NavEKF3_core.AidingMode := NavEKF3_core.AidingMode.AID_ABSOLUTE
  /-- `bool gndOffsetValid` of `NavEKF3_core` (`AP_NavEKF3/AP_NavEKF3_core.h:1390`). -/
  gndOffsetValid : Bool := false
  /-- `Vector3F delAngBodyOF` of `NavEKF3_core` (`AP_NavEKF3/AP_NavEKF3_core.h:1391`). -/
  delAngBodyOF : Vector3p.State := {}
  /-- `ftype delTimeOF` of `NavEKF3_core` (`AP_NavEKF3/AP_NavEKF3_core.h:1392`). -/
  delTimeOF : Binary64 := (Binary64.ofBits 0x0000000000000000 /- 0.0 -/)
  /-- `bool flowFusionActive` of `NavEKF3_core` (`AP_NavEKF3/AP_NavEKF3_core.h:1393`). -/
  flowFusionActive : Bool := false
  /-- `Vector3F accelPosOffset` of `NavEKF3_core` (`AP_NavEKF3/AP_NavEKF3_core.h:1395`). -/
  accelPosOffset : Vector3p.State := {}
  /-- `ftype baroHgtOffset` of `NavEKF3_core` (`AP_NavEKF3/AP_NavEKF3_core.h:1398`). -/
  baroHgtOffset : Binary64 := (Binary64.ofBits 0x0000000000000000 /- 0.0 -/)
  /-- `ftype rngOnGnd` of `NavEKF3_core` (`AP_NavEKF3/AP_NavEKF3_core.h:1399`). -/
  rngOnGnd : Binary64 := (Binary64.ofBits 0x0000000000000000 /- 0.0 -/)
  /-- `uint32_t lastRngMeasTime_ms` of `NavEKF3_core` (`AP_NavEKF3/AP_NavEKF3_core.h:1400`). -/
  lastRngMeasTime_ms : UInt32 := (0 : UInt32)
  /-- `bool terrainHgtStable` of `NavEKF3_core` (`AP_NavEKF3/AP_NavEKF3_core.h:1401`). -/
  terrainHgtStable : Bool := false
  /-- `class BodyOdomFusion bodyOdm` of `NavEKF3_core` (`AP_NavEKF3/AP_NavEKF3_core.h:1432`). -/
  bodyOdm : NavEKF3_core.BodyOdomFusion.State := {}
  /-- `class GpsYawFusion gpsYaw` of `NavEKF3_core` (`AP_NavEKF3/AP_NavEKF3_core.h:1449`). -/
  gpsYaw : NavEKF3_core.GpsYawFusion.State := {}
  /-- `yaw_elements yawAngDataStatic` of `NavEKF3_core` (`AP_NavEKF3/AP_NavEKF3_core.h:1451`). -/
  yawAngDataStatic : NavEKF3_core.yaw_elements := {}
  /-- `class DragFusion drag` of `NavEKF3_core` (`AP_NavEKF3/AP_NavEKF3_core.h:1531`). -/
  drag : NavEKF3_core.DragFusion := {}
  /-- `AP_NavEKF_Source::SourceZ activeHgtSource` of `NavEKF3_core` (`AP_NavEKF3/AP_NavEKF3_core.h:1534`). -/
  activeHgtSource : AP_NavEKF_Source.SourceZ := AP_NavEKF_Source.SourceZ.NONE
  /-- `AP_NavEKF_Source::SourceZ prevHgtSource` of `NavEKF3_core` (`AP_NavEKF3/AP_NavEKF3_core.h:1535`). -/
  prevHgtSource : AP_NavEKF_Source.SourceZ := AP_NavEKF_Source.SourceZ.NONE
  /-- `bool takeOffDetected` of `NavEKF3_core` (`AP_NavEKF3/AP_NavEKF3_core.h:1538`). -/
  takeOffDetected : Bool := false
  /-- `ftype rngAtStartOfFlight` of `NavEKF3_core` (`AP_NavEKF3/AP_NavEKF3_core.h:1539`). -/
  rngAtStartOfFlight : Binary64 := (Binary64.ofBits 0x0000000000000000 /- 0.0 -/)
  /-- `uint32_t timeAtArming_ms` of `NavEKF3_core` (`AP_NavEKF3/AP_NavEKF3_core.h:1540`). -/
  timeAtArming_ms : UInt32 := (0 : UInt32)
  /-- `ftype meaHgtAtTakeOff` of `NavEKF3_core` (`AP_NavEKF3/AP_NavEKF3_core.h:1543`). -/
  meaHgtAtTakeOff : Binary64 := (Binary64.ofBits 0x0000000000000000 /- 0.0 -/)
  /-- `bool finalInflightYawInit` of `NavEKF3_core` (`AP_NavEKF3/AP_NavEKF3_core.h:1546`). -/
  finalInflightYawInit : Bool := false
  /-- `uint8_t magYawAnomallyCount` of `NavEKF3_core` (`AP_NavEKF3/AP_NavEKF3_core.h:1547`). -/
  magYawAnomallyCount : UInt8 := (0 : UInt8)
  /-- `bool finalInflightMagInit` of `NavEKF3_core` (`AP_NavEKF3/AP_NavEKF3_core.h:1548`). -/
  finalInflightMagInit : Bool := false
  /-- `bool magStateResetRequest` of `NavEKF3_core` (`AP_NavEKF3/AP_NavEKF3_core.h:1549`). -/
  magStateResetRequest : Bool := false
  /-- `bool magYawResetRequest` of `NavEKF3_core` (`AP_NavEKF3/AP_NavEKF3_core.h:1550`). -/
  magYawResetRequest : Bool := false
  /-- `bool gpsYawResetRequest` of `NavEKF3_core` (`AP_NavEKF3/AP_NavEKF3_core.h:1551`). -/
  gpsYawResetRequest : Bool := false
  /-- `ftype posDownAtLastMagReset` of `NavEKF3_core` (`AP_NavEKF3/AP_NavEKF3_core.h:1552`). -/
  posDownAtLastMagReset : Binary64 := (Binary64.ofBits 0x0000000000000000 /- 0.0 -/)
  /-- `ftype yawInnovAtLastMagReset` of `NavEKF3_core` (`AP_NavEKF3/AP_NavEKF3_core.h:1553`). -/
  yawInnovAtLastMagReset : Binary64 := (Binary64.ofBits 0x0000000000000000 /- 0.0 -/)
  /-- `QuaternionF quatAtLastMagReset` of `NavEKF3_core` (`AP_NavEKF3/AP_NavEKF3_core.h:1554`). -/
  quatAtLastMagReset : QuaternionT_double.State := QuaternionT_double.init_void
  /-- `MagFuseSel magFusionSel` of `NavEKF3_core` (`AP_NavEKF3/AP_NavEKF3_core.h:1555`). -/
  magFusionSel : NavEKF3_core.MagFuseSel := NavEKF3_core.MagFuseSel.NOT_FUSING
  /-- `ftype gyro_diff` of `NavEKF3_core` (`AP_NavEKF3/AP_NavEKF3_core.h:1558`). -/
  gyro_diff : Binary64 := (Binary64.ofBits 0x0000000000000000 /- 0.0 -/)
  /-- `ftype accel_diff` of `NavEKF3_core` (`AP_NavEKF3/AP_NavEKF3_core.h:1559`). -/
  accel_diff : Binary64 := (Binary64.ofBits 0x0000000000000000 /- 0.0 -/)
  /-- `Vector3F gyro_prev` of `NavEKF3_core` (`AP_NavEKF3/AP_NavEKF3_core.h:1560`). -/
  gyro_prev : Vector3p.State := {}
  /-- `Vector3F accel_prev` of `NavEKF3_core` (`AP_NavEKF3/AP_NavEKF3_core.h:1561`). -/
  accel_prev : Vector3p.State := {}
  /-- `bool onGroundNotMoving` of `NavEKF3_core` (`AP_NavEKF3/AP_NavEKF3_core.h:1562`). -/
  onGroundNotMoving : Bool := false
  /-- `uint32_t lastMoveCheckLogTime_ms` of `NavEKF3_core` (`AP_NavEKF3/AP_NavEKF3_core.h:1563`). -/
  lastMoveCheckLogTime_ms : UInt32 := (0 : UInt32)
  /-- `bool inhibitDelVelBiasStates` of `NavEKF3_core` (`AP_NavEKF3/AP_NavEKF3_core.h:1566`). -/
  inhibitDelVelBiasStates : Bool := false
  /-- `bool dvelBiasAxisInhibit[3]` of `NavEKF3_core` (`AP_NavEKF3/AP_NavEKF3_core.h:1567`). -/
  dvelBiasAxisInhibit : Array Bool := Array.replicate 3 false
  /-- `Vector3F dvelBiasAxisVarPrev` of `NavEKF3_core` (`AP_NavEKF3/AP_NavEKF3_core.h:1568`). -/
  dvelBiasAxisVarPrev : Vector3p.State := {}
  /-- `class ExternalNavFusion extNav` of `NavEKF3_core` (`AP_NavEKF3/AP_NavEKF3_core.h:1595`). -/
  extNav : NavEKF3_core.ExternalNavFusion := {}
  /-- `struct (unnamed struct at AP_NavEKF3/AP_NavEKF3_core.h:1598:5) faultStatus` of `NavEKF3_core` (`AP_NavEKF3/AP_NavEKF3_core.h:1618`). -/
  faultStatus : NavEKF3_core.faultStatus_t := {}
  /-- `union (unnamed union at AP_NavEKF3/AP_NavEKF3_core.h:1621:5) gpsCheckStatus` of `NavEKF3_core` (`AP_NavEKF3/AP_NavEKF3_core.h:1636`). -/
  gpsCheckStatus : UInt16 := (0 : UInt16)
  /-- `char prearm_fail_string[40]` of `NavEKF3_core` (`AP_NavEKF3/AP_NavEKF3_core.h:1639`). -/
  prearm_fail_string : CText := CText.none
  /-- `bool have_table_earth_field` of `NavEKF3_core` (`AP_NavEKF3/AP_NavEKF3_core.h:1642`). -/
  have_table_earth_field : Bool := false
  /-- `Vector3F table_earth_field_ga` of `NavEKF3_core` (`AP_NavEKF3/AP_NavEKF3_core.h:1643`). -/
  table_earth_field_ga : Vector3p.State := {}
  /-- `ftype table_declination` of `NavEKF3_core` (`AP_NavEKF3/AP_NavEKF3_core.h:1644`). -/
  table_declination : Binary64 := (Binary64.ofBits 0x0000000000000000 /- 0.0 -/)
  /-- `uint32_t last_oneHz_ms` of `NavEKF3_core` (`AP_NavEKF3/AP_NavEKF3_core.h:1647`). -/
  last_oneHz_ms : UInt32 := (0 : UInt32)
  /-- `struct ekf_timing timing` of `NavEKF3_core` (`AP_NavEKF3/AP_NavEKF3_core.h:1658`). -/
  timing : ekf_timing := {}
  /-- `uint32_t last_filter_ok_ms` of `NavEKF3_core` (`AP_NavEKF3/AP_NavEKF3_core.h:1661`). -/
  last_filter_ok_ms : UInt32 := (0 : UInt32)
  /-- `uint32_t EKFGSF_yaw_reset_ms` of `NavEKF3_core` (`AP_NavEKF3/AP_NavEKF3_core.h:1687`). -/
  EKFGSF_yaw_reset_ms : UInt32 := (0 : UInt32)
  /-- `uint32_t EKFGSF_yaw_reset_request_ms` of `NavEKF3_core` (`AP_NavEKF3/AP_NavEKF3_core.h:1688`). -/
  EKFGSF_yaw_reset_request_ms : UInt32 := (0 : UInt32)
  /-- `uint8_t EKFGSF_yaw_reset_count` of `NavEKF3_core` (`AP_NavEKF3/AP_NavEKF3_core.h:1689`). -/
  EKFGSF_yaw_reset_count : UInt8 := (0 : UInt8)
  /-- `bool EKFGSF_run_filterbank` of `NavEKF3_core` (`AP_NavEKF3/AP_NavEKF3_core.h:1690`). -/
  EKFGSF_run_filterbank : Bool := false
  /-- `uint8_t EKFGSF_yaw_valid_count` of `NavEKF3_core` (`AP_NavEKF3/AP_NavEKF3_core.h:1691`). -/
  EKFGSF_yaw_valid_count : UInt8 := (0 : UInt8)
  /-- `uint32_t lastLogTime_ms` of `NavEKF3_core` (`AP_NavEKF3/AP_NavEKF3_core.h:1694`). -/
  lastLogTime_ms : UInt32 := (0 : UInt32)
  /-- `uint32_t lastUpdateTime_ms` of `NavEKF3_core` (`AP_NavEKF3/AP_NavEKF3_core.h:1695`). -/
  lastUpdateTime_ms : UInt32 := (0 : UInt32)
  /-- `uint32_t lastEkfStateVarLogTime_ms` of `NavEKF3_core` (`AP_NavEKF3/AP_NavEKF3_core.h:1696`). -/
  lastEkfStateVarLogTime_ms : UInt32 := (0 : UInt32)
  /-- `uint32_t lastTimingLogTime_ms` of `NavEKF3_core` (`AP_NavEKF3/AP_NavEKF3_core.h:1697`). -/
  lastTimingLogTime_ms : UInt32 := (0 : UInt32)
  /-- `uint8_t selected_gps` of `NavEKF3_core` (`AP_NavEKF3/AP_NavEKF3_core.h:1718`). -/
  selected_gps : UInt8 := (0 : UInt8)
  /-- `uint8_t preferred_gps` of `NavEKF3_core` (`AP_NavEKF3/AP_NavEKF3_core.h:1719`). -/
  preferred_gps : UInt8 := (0 : UInt8)
  /-- `uint8_t selected_baro` of `NavEKF3_core` (`AP_NavEKF3/AP_NavEKF3_core.h:1720`). -/
  selected_baro : UInt8 := (0 : UInt8)
  /-- `uint8_t selected_airspeed` of `NavEKF3_core` (`AP_NavEKF3/AP_NavEKF3_core.h:1721`). -/
  selected_airspeed : UInt8 := (0 : UInt8)
  /-- `AP_NavEKF_Source::SourceXY posxy_source_last` of `NavEKF3_core` (`AP_NavEKF3/AP_NavEKF3_core.h:1724`). -/
  posxy_source_last : AP_NavEKF_Source.SourceXY := AP_NavEKF_Source.SourceXY.NONE
  /-- `bool posxy_source_reset` of `NavEKF3_core` (`AP_NavEKF3/AP_NavEKF3_core.h:1725`). -/
  posxy_source_reset : Bool := false
  /-- `AP_NavEKF_Source::SourceYaw yaw_source_last` of `NavEKF3_core` (`AP_NavEKF3/AP_NavEKF3_core.h:1726`). -/
  yaw_source_last : AP_NavEKF_Source.SourceYaw := AP_NavEKF_Source.SourceYaw.NONE
  /-- `bool yaw_source_reset` of `NavEKF3_core` (`AP_NavEKF3/AP_NavEKF3_core.h:1727`). -/
  yaw_source_reset : Bool := false
deriving Inhabited

end NavEKF3_core

namespace NavEKF3

/-- C++ `bool NavEKF3::configuredToUseGPSForPosXY() const`, `AP_NavEKF3/AP_NavEKF3.cpp:1627-1634`. -/
def configuredToUseGPSForPosXY (s : State) : Bool := Id.run do
  if AP_NavEKF_Source.getPosXYSource s.sources s.primary == AP_NavEKF_Source.SourceXY.GPS then
    return true
  return false

end NavEKF3

namespace NavEKF3_core

/-- C++ `NavEKF3_core::NavEKF3_core(class NavEKF3 * _frontend, class AP_DAL & dal)`, `AP_NavEKF3/AP_NavEKF3_core.cpp:13-20`. -/
def init (_frontend : WPtr) : State := Id.run do
  let mut s : State := {}
  s := { s with frontend := _frontend }
  s := { s with storedIMU := EKF_IMU_buffer_t_NavEKF3_core_imu_elements.construct }
  s := { s with storedGPS := EKF_obs_buffer_t_NavEKF3_core_gps_elements.construct }
  s := { s with storedMag := EKF_obs_buffer_t_NavEKF3_core_mag_elements.construct }
  s := { s with storedBaro := EKF_obs_buffer_t_NavEKF3_core_baro_elements.construct }
  s := { s with storedOutput := EKF_IMU_buffer_t_NavEKF3_core_output_elements.construct }
  s := { s with prevTnb := Matrix3_double.init_void }
  s := { s with earthRateNED := Vector3p.init_void }
  s := { s with innovMag := Vector3p.init_void }
  s := { s with varInnovMag := Vector3p.init_void }
  s := { s with velDotNED := Vector3p.init_void }
  s := { s with velDotNEDfilt := Vector3p.init_void }
  s := { s with lastKnownPositionNE := Vector2p.init_void }
  s := { s with magTestRatio := Vector3p.init_void }
  s := { s with EKF_origin := Location.init_void }
  s := { s with imuQuatDownSampleNew := QuaternionT_double.init_void }
  s := { s with delAngCorrection := Vector3p.init_void }
  s := { s with velErrintegral := Vector3p.init_void }
  s := { s with posErrintegral := Vector3p.init_void }
  s := { s with lastMagOffsets := Vector3p.init_void }
  s := { s with posResetNE := Vector2p.init_void }
  s := { s with prevQuatMagReset := QuaternionT_double.init_void }
  s := { s with delAngCorrected := Vector3p.init_void }
  s := { s with delVelCorrected := Vector3p.init_void }
  s := { s with earthMagFieldVar := Vector3p.init_void }
  s := { s with bodyMagFieldVar := Vector3p.init_void }
  s := { s with filterStatus := (0 : UInt32) }
  s := { s with outputTrackError := Vector3p.init_void }
  s := { s with velOffsetNED := Vector3p.init_void }
  s := { s with posOffsetNED := Vector3p.init_void }
  s := { s with gpsloc_prev := Location.init_void }
  s := { s with gpsVelInnov := Vector3p.init_void }
  s := { s with gpsVelVarInnov := Vector3p.init_void }
  s := { s with storedOF := EKF_obs_buffer_t_NavEKF3_core_of_elements.construct }
  s := { s with auxFlowObsInnov := Vector2p.init_void }
  s := { s with auxFlowTestRatio := Vector2p.init_void }
  s := { s with flowGyroBias := Vector2p.init_void }
  s := { s with delAngBodyOF := Vector3p.init_void }
  s := { s with accelPosOffset := Vector3p.init_void }
  s := { s with quatAtLastMagReset := QuaternionT_double.init_void }
  s := { s with gyro_prev := Vector3p.init_void }
  s := { s with accel_prev := Vector3p.init_void }
  s := { s with dvelBiasAxisVarPrev := Vector3p.init_void }
  s := { s with gpsCheckStatus := (0 : UInt16) }
  s := { s with table_earth_field_ga := Vector3p.init_void }
  s := { s with firstInitTime_ms := Int32.toUInt32 (0 : Int32) }
  s := { s with lastInitFailReport_ms := Int32.toUInt32 (0 : Int32) }
  return s

end NavEKF3_core

namespace NavEKF3_core

/-- C++ `void NavEKF3_core::zeroStatesVarCov(uint8_t first, uint8_t last)`, `AP_NavEKF3/AP_NavEKF3_core.cpp:1794-1806`. -/
def zeroStatesVarCov (s : State) (first : UInt8) (last : UInt8) : State := Id.run do
  let mut s := s
  for row' in [first.toNat:last.toNat + 1] do
    let row : UInt8 := Nat.toUInt8 row'
    s := { s with Pmut := NavEKF_core_common.zero_range s.Pmut (UInt8.toNat row * 24) (Int8.toUInt8 (Int32.toInt8 (0 : Int32))) (Int8.toUInt8 (Int32.toInt8 (23 : Int32))) }
  for row' in [0:24] do
    let row : UInt8 := Nat.toUInt8 row'
    s := { s with Pmut := NavEKF_core_common.zero_range s.Pmut (UInt8.toNat row * 24) first last }
  return s

end NavEKF3_core

namespace NavEKF3_core.AirspeedFusion

/-- C++ `void NavEKF3_core::AirspeedFusion::InitialiseVariables(uint32_t now_ms)`, `AP_NavEKF3/AP_NavEKF3_AirDataFusion.cpp:10-15`. -/
def InitialiseVariables (s : State) (now_ms : UInt32) : State := Id.run do
  let mut s := s
  s := { s with prevStepTime_ms := now_ms }
  s := { s with lastPassTime_ms := Int32.toUInt32 (0 : Int32) }
  s := { s with receivedTime_ms := Int32.toUInt32 (0 : Int32) }
  return s

end NavEKF3_core.AirspeedFusion

namespace NavEKF3_core.BodyOdomFusion

/-- C++ `void NavEKF3_core::BodyOdomFusion::InitialiseVariables()`, `AP_NavEKF3/AP_NavEKF3_PosVelFusion.cpp:1483-1497`. -/
def InitialiseVariables (s : State) : State := Id.run do
  let mut s := s
  s := { s with dataNew := { time_ms := (0 : UInt32), vel := { x := (Binary64.ofBits 0x0000000000000000 /- 0.0 -/), y := (Binary64.ofBits 0x0000000000000000 /- 0.0 -/), z := (Binary64.ofBits 0x0000000000000000 /- 0.0 -/) }, velErr := (Binary64.ofBits 0x0000000000000000 /- 0.0 -/), body_offset := { x := (Binary64.ofBits 0x0000000000000000 /- 0.0 -/), y := (Binary64.ofBits 0x0000000000000000 /- 0.0 -/), z := (Binary64.ofBits 0x0000000000000000 /- 0.0 -/) }, angRate := { x := (Binary64.ofBits 0x0000000000000000 /- 0.0 -/), y := (Binary64.ofBits 0x0000000000000000 /- 0.0 -/), z := (Binary64.ofBits 0x0000000000000000 /- 0.0 -/) } } }
  s := { s with dataDelayed := { time_ms := (0 : UInt32), vel := { x := (Binary64.ofBits 0x0000000000000000 /- 0.0 -/), y := (Binary64.ofBits 0x0000000000000000 /- 0.0 -/), z := (Binary64.ofBits 0x0000000000000000 /- 0.0 -/) }, velErr := (Binary64.ofBits 0x0000000000000000 /- 0.0 -/), body_offset := { x := (Binary64.ofBits 0x0000000000000000 /- 0.0 -/), y := (Binary64.ofBits 0x0000000000000000 /- 0.0 -/), z := (Binary64.ofBits 0x0000000000000000 /- 0.0 -/) }, angRate := { x := (Binary64.ofBits 0x0000000000000000 /- 0.0 -/), y := (Binary64.ofBits 0x0000000000000000 /- 0.0 -/), z := (Binary64.ofBits 0x0000000000000000 /- 0.0 -/) } } }
  s := { s with lastPassTime_ms := Int32.toUInt32 (0 : Int32) }
  s := { s with testRatio := Array.replicate 3 (Binary64.ofBits 0x0000000000000000 /- 0.0 -/) }
  s := { s with varInnov := Array.replicate 3 (Binary64.ofBits 0x0000000000000000 /- 0.0 -/) }
  s := { s with innov := Array.replicate 3 (Binary64.ofBits 0x0000000000000000 /- 0.0 -/) }
  s := { s with prevFuseTime_ms := Int32.toUInt32 (0 : Int32) }
  s := { s with measTime_ms := Int32.toUInt32 (0 : Int32) }
  s := { s with fusionDelayed := false }
  s := { s with fusionActive := false }
  return s

end NavEKF3_core.BodyOdomFusion

namespace NavEKF3_core.GpsYawFusion

/-- C++ `void NavEKF3_core::GpsYawFusion::InitialiseVariables()`, `AP_NavEKF3/AP_NavEKF3_MagFusion.cpp:20-25`. -/
def InitialiseVariables (s : State) : State := Id.run do
  let mut s := s
  s := { s with measTime_ms := Int32.toUInt32 (0 : Int32) }
  s := { s with dataNew := { time_ms := (0 : UInt32), yawAng := (Binary64.ofBits 0x0000000000000000 /- 0.0 -/), yawAngErr := (Binary64.ofBits 0x0000000000000000 /- 0.0 -/), order := NavEKF3_core.rotationOrder.TAIT_BRYAN_321 } }
  s := { s with dataDelayed := { time_ms := (0 : UInt32), yawAng := (Binary64.ofBits 0x0000000000000000 /- 0.0 -/), yawAngErr := (Binary64.ofBits 0x0000000000000000 /- 0.0 -/), order := NavEKF3_core.rotationOrder.TAIT_BRYAN_321 } }
  return s

end NavEKF3_core.GpsYawFusion

namespace NavEKF3_core

/-- C++ `bool NavEKF3_core::getAirSpdVec(Vector3f & vel) const`, `AP_NavEKF3/AP_NavEKF3_Outputs.cpp:187-201`. -/
def getAirSpdVec (s : State) (vel : Vector3f.State) : Vector3f.State × Bool := Id.run do
  let mut vel := vel
  if UInt32.toInt32 (NavEKF3_core.AidingMode.toInt s.PV_AidingMode) == UInt32.toInt32 (NavEKF3_core.AidingMode.toInt NavEKF3_core.AidingMode.AID_NONE) then
    return (vel, false)
  vel := Vector3p.tofloat (Vector3p.op_add s.outputDataNew.velocity s.velOffsetNED)
  if !s.inhibitWindStates then
    vel := { vel with x := Binary64.toBinary32 (Binary32.toBinary64 vel.x - s.statesArray[22]!) }
    vel := { vel with y := Binary64.toBinary32 (Binary32.toBinary64 vel.y - s.statesArray[23]!) }
  let mut Tnb : Matrix3f.State := Matrix3f.init_void
  Tnb := QuaternionT_double.rotation_matrix_Matrix3f (QuaternionT_double.inverse s.outputDataNew.quat) Tnb
  vel := Matrix3f.op_mul_Vector3f Tnb vel
  return (vel, true)

end NavEKF3_core

namespace NavEKF3_core

/-- C++ `uint16_t NavEKF3_core::getYawResetCount() const`, `AP_NavEKF3/AP_NavEKF3_core.h:410`. -/
def getYawResetCount (s : State) : UInt16 := Id.run do
  return s.yawResetCount

end NavEKF3_core

namespace NavEKF3_core

/-- C++ `uint16_t NavEKF3_core::getPosNorthEastResetCount() const`, `AP_NavEKF3/AP_NavEKF3_core.h:413`. -/
def getPosNorthEastResetCount (s : State) : UInt16 := Id.run do
  return s.posNEResetCount

end NavEKF3_core

namespace NavEKF3_core

/-- C++ `uint16_t NavEKF3_core::getPosDownResetCount() const`, `AP_NavEKF3/AP_NavEKF3_core.h:416`. -/
def getPosDownResetCount (s : State) : UInt16 := Id.run do
  return s.posDResetCount

end NavEKF3_core

namespace NavEKF3

/-- C++ `void NavEKF3::updateCoreRelativeErrors()`, `AP_NavEKF3/AP_NavEKF3.cpp:1133-1146`. -/
def updateCoreRelativeErrors (s : State) : State := Id.run do
  let mut s := s
  let mut error : Binary32 := (Binary32.ofBits 0x00000000 /- 0 -/)
  let t'1 : UInt8 := Int8.toUInt8 (Int32.toInt8 (0 : Int32))
  let t'2 : Int32 := UInt32.toInt32 (UInt8.toUInt32 s.num_cores)
  for i' in [0:(t'2.toInt - (Int.ofNat t'1.toNat)).toNat] do  -- C++ loop bounded by a runtime value (--runtime-loops)
    let i : UInt8 := t'1 + Nat.toUInt8 i'
    if UInt32.toInt32 (UInt8.toUInt32 i) != UInt32.toInt32 (UInt8.toUInt32 s.primary) then
      error := s.coreErrorScores[UInt8.toNat i]! - s.coreErrorScores[UInt8.toNat s.primary]!
      if decide (error > (Binary32.ofBits 0x00000000 /- 0 -/)) || decide (error < -(Estimator_lib.MAX_AP_ParamT_float_4_float s._err_thresh (Binary32.ofBits 0x3d4ccccd /- 0.05 -/))) then
        s := { s with coreRelativeErrors := s.coreRelativeErrors.set! (UInt8.toNat i) (s.coreRelativeErrors[UInt8.toNat i]! + error) }
        s := { s with coreRelativeErrors := s.coreRelativeErrors.set! (UInt8.toNat i) (Binary64.toBinary32 (Estimator_lib.constrain_value_line_double (Binary32.toBinary64 s.coreRelativeErrors[UInt8.toNat i]!) (Binary64.ofBits 0xbff0000000000000 /- (double)-1 -/) (Binary64.ofBits 0x3ff0000000000000 /- (double)1 -/) (Int32.toUInt32 (1142 : Int32)))) }
  return s

end NavEKF3

namespace NavEKF3_core

/-- C++ `void NavEKF3_core::getFilterFaults(uint16_t & faults) const`, `AP_NavEKF3/AP_NavEKF3_Outputs.cpp:571-581`. -/
def getFilterFaults (s : State) (faults : UInt16) : UInt16 := Id.run do
  let mut faults := faults
  faults := Int16.toUInt16 (Int32.toInt16 ((if QuaternionT_double.is_nan ({ q1 := s.statesArray[0]!, q2 := s.statesArray[1]!, q3 := s.statesArray[2]!, q4 := s.statesArray[3]! } : QuaternionT_double.State) then (1 : Int32) else (0 : Int32)) * UInt32.toInt32 (UInt16.toUInt32 (Int16.toUInt16 (Int32.toInt16 (NavFilterFaultBit.toInt NavFilterFaultBit.BAD_QUATERNION)))) ||| (if Vector3p.is_nan ({ x := s.statesArray[4]!, y := s.statesArray[5]!, z := s.statesArray[6]! } : Vector3p.State) then (1 : Int32) else (0 : Int32)) * UInt32.toInt32 (UInt16.toUInt32 (Int16.toUInt16 (Int32.toInt16 (NavFilterFaultBit.toInt NavFilterFaultBit.BAD_VELOCITY)))) ||| (if s.faultStatus.bad_xmag then (1 : Int32) else (0 : Int32)) * UInt32.toInt32 (UInt16.toUInt32 (Int16.toUInt16 (Int32.toInt16 (NavFilterFaultBit.toInt NavFilterFaultBit.BAD_XMAG)))) ||| (if s.faultStatus.bad_ymag then (1 : Int32) else (0 : Int32)) * UInt32.toInt32 (UInt16.toUInt32 (Int16.toUInt16 (Int32.toInt16 (NavFilterFaultBit.toInt NavFilterFaultBit.BAD_YMAG)))) ||| (if s.faultStatus.bad_zmag then (1 : Int32) else (0 : Int32)) * UInt32.toInt32 (UInt16.toUInt32 (Int16.toUInt16 (Int32.toInt16 (NavFilterFaultBit.toInt NavFilterFaultBit.BAD_ZMAG)))) ||| (if s.faultStatus.bad_airspeed then (1 : Int32) else (0 : Int32)) * UInt32.toInt32 (UInt16.toUInt32 (Int16.toUInt16 (Int32.toInt16 (NavFilterFaultBit.toInt NavFilterFaultBit.BAD_AIRSPEED)))) ||| (if s.faultStatus.bad_sideslip then (1 : Int32) else (0 : Int32)) * UInt32.toInt32 (UInt16.toUInt32 (Int16.toUInt16 (Int32.toInt16 (NavFilterFaultBit.toInt NavFilterFaultBit.BAD_SIDESLIP)))) ||| (if !s.statesInitialised then (1 : Int32) else (0 : Int32)) * UInt32.toInt32 (UInt16.toUInt32 (Int16.toUInt16 (Int32.toInt16 (NavFilterFaultBit.toInt NavFilterFaultBit.NOT_INITIALISED))))))
  return faults

/-- C++ `bool NavEKF3_core::healthy() const`, `AP_NavEKF3/AP_NavEKF3_Outputs.cpp:11-35`. -/
def healthy (s : State) : Bool := Id.run do
  let mut faultInt : UInt16 := (0 : UInt16)  -- uninitialized in C++; assigned before every read
  faultInt := getFilterFaults s faultInt
  if UInt32.toInt32 (UInt16.toUInt32 faultInt) > (0 : Int32) then
    return false
  if decide (s.velTestRatio > (Binary64.ofBits 0x3ff0000000000000 /- 1 -/)) && decide (s.posTestRatio > (Binary64.ofBits 0x3ff0000000000000 /- 1 -/)) && decide (s.hgtTestRatio > (Binary64.ofBits 0x3ff0000000000000 /- 1 -/)) then
    return false
  if (s.imuSampleTime_ms - s.ekfStartTime_ms) < Int32.toUInt32 (1000 : Int32) then
    return false
  let horizErrSq : Binary32 := Binary64.toBinary32 (Estimator_lib.sq_double s.innovVelPos[3]! + Estimator_lib.sq_double s.innovVelPos[4]!)
  if s.onGround && (UInt32.toInt32 (NavEKF3_core.AidingMode.toInt s.PV_AidingMode) == UInt32.toInt32 (NavEKF3_core.AidingMode.toInt NavEKF3_core.AidingMode.AID_NONE)) && ((decide (horizErrSq > (Binary32.ofBits 0x3f800000 /- 1.0f -/))) || (decide (Binary64.abs s.hgtInnovFiltState > (Binary64.ofBits 0x3ff0000000000000 /- 1.0f -/)))) then
    return false
  return true

/-- C++ `bool NavEKF3_core::have_aligned_tilt() const`, `AP_NavEKF3/AP_NavEKF3_core.h:465-467`. -/
def have_aligned_tilt (s : State) : Bool := Id.run do
  return s.tiltAlignComplete

/-- C++ `bool NavEKF3_core::have_aligned_yaw() const`, `AP_NavEKF3/AP_NavEKF3_core.h:470-472`. -/
def have_aligned_yaw (s : State) : Bool := Id.run do
  return s.yawAlignComplete

end NavEKF3_core

namespace NavEKF3_core

/-- C++ `uint8_t NavEKF3_core::getFramesSincePredict() const`, `AP_NavEKF3/AP_NavEKF3_Outputs.cpp:618-621`. -/
def getFramesSincePredict (s : State) : UInt8 := Id.run do
  return UInt32.toUInt8 s.framesSincePredict

end NavEKF3_core

namespace NavEKF3_core

/-- C++ `void NavEKF3_core::bestRotationOrder(rotationOrder & order)`, `AP_NavEKF3/AP_NavEKF3_core.cpp:2176-2185`. -/
def bestRotationOrder (s : State) (order : NavEKF3_core.rotationOrder) : NavEKF3_core.rotationOrder := Id.run do
  let mut order := order
  if Binary64.abs s.prevTnb.c.x < Binary64.abs s.prevTnb.c.y then
    order := NavEKF3_core.rotationOrder.TAIT_BRYAN_321
  else
    order := NavEKF3_core.rotationOrder.TAIT_BRYAN_312
  return order

end NavEKF3_core

namespace NavEKF3_core

/-- C++ `void NavEKF3_core::CalculateVelInnovationsAndVariances(const Vector3F & velocity, ftype noise, ftype accel_scale, Vector3F & innovations, Vector3F & variances) const`, `AP_NavEKF3/AP_NavEKF3_PosVelFusion.cpp:490-501`. -/
def CalculateVelInnovationsAndVariances (s : State) (velocity : Vector3p.State) (noise : Binary64) (accel_scale : Binary64) (innovations : Vector3p.State) (variances : Vector3p.State) : Vector3p.State × Vector3p.State := Id.run do
  let mut innovations := innovations
  let mut variances := variances
  innovations := Vector3p.op_sub_Vector3p ({ x := s.statesArray[4]!, y := s.statesArray[5]!, z := s.statesArray[6]! } : Vector3p.State) velocity
  let obs_data_chk : Binary64 := Estimator_lib.sq_double (Estimator_lib.constrain_value_line_double noise (Binary64.ofBits 0x3fa999999999999a /- (double)3602879701896397/72057594037927936 -/) (Binary64.ofBits 0x4014000000000000 /- (double)5 -/) (Int32.toUInt32 (495 : Int32))) + Estimator_lib.sq_double (accel_scale * s.accNavMag)
  variances := { variances with x := s.Pmut[100]! + obs_data_chk }
  variances := { variances with y := s.Pmut[125]! + obs_data_chk }
  variances := { variances with z := s.Pmut[150]! + obs_data_chk }
  return (innovations, variances)

/-- C++ `void NavEKF3_core::ResetPositionD(ftype posD)`, `AP_NavEKF3/AP_NavEKF3_PosVelFusion.cpp:250-270`. -/
def ResetPositionD (s : State) (posD : Binary64) : State := Id.run do
  let mut s := s
  let posDOrig : Binary64 := s.statesArray[9]!
  s := { s with statesArray := s.statesArray.set! 9 posD }
  s := { s with posResetD := s.statesArray[9]! - posDOrig }
  s := { s with outputDataNew.position.z := s.outputDataNew.position.z + s.posResetD }
  s := { s with vertCompFiltState.pos := s.outputDataNew.position.z }
  s := { s with outputDataDelayed.position.z := s.outputDataDelayed.position.z + s.posResetD }
  let t'1 : UInt8 := Int8.toUInt8 (Int32.toInt8 (0 : Int32))
  let t'2 : Int32 := UInt32.toInt32 (UInt8.toUInt32 s.imu_buffer_length)
  for i' in [0:(t'2.toInt - (Int.ofNat t'1.toNat)).toNat] do  -- C++ loop bounded by a runtime value (--runtime-loops)
    let i : UInt8 := t'1 + Nat.toUInt8 i'
    s := { s with storedOutput.buffer := s.storedOutput.buffer.set! (UInt8.toNat (UInt32.toUInt8 (UInt8.toUInt32 i))) ({ s.storedOutput.buffer[UInt8.toNat (UInt32.toUInt8 (UInt8.toUInt32 i))]! with position.z := s.storedOutput.buffer[UInt8.toNat (UInt32.toUInt8 (UInt8.toUInt32 i))]!.position.z + s.posResetD }) }
  s := { s with posDResetCount := s.posDResetCount + (1 : UInt16) }
  return s

end NavEKF3_core

namespace NavEKF3_core

/-- C++ `uint8_t NavEKF3_core::getIMUIndex() const`, `AP_NavEKF3/AP_NavEKF3_core.h:427`. -/
def getIMUIndex (s : State) : UInt8 := Id.run do
  return s.gyro_index_active

end NavEKF3_core

namespace NavEKF3_core

/-- C++ `void NavEKF3_core::getQuaternion(Quaternion & quat) const`, `AP_NavEKF3/AP_NavEKF3_Outputs.cpp:162-165`. -/
def getQuaternion (s : State) (ret : Quaternion.State) : Quaternion.State := Id.run do
  let mut ret := ret
  ret := QuaternionT_double.tofloat s.outputDataNew.quat
  return ret

end NavEKF3_core

namespace NavEKF3_core

/-- C++ `void NavEKF3_core::getVelNED(Vector3f & vel) const`, `AP_NavEKF3/AP_NavEKF3_Outputs.cpp:179-183`. -/
def getVelNED (s : State) (vel : Vector3f.State) : Vector3f.State := Id.run do
  let mut vel := vel
  vel := Vector3p.tofloat (Vector3p.op_add s.outputDataNew.velocity s.velOffsetNED)
  return vel

end NavEKF3_core

namespace NavEKF3_core

/-- C++ `float NavEKF3_core::getPosDownDerivative() const`, `AP_NavEKF3/AP_NavEKF3_Outputs.cpp:218-223`. -/
def getPosDownDerivative (s : State) : Binary32 := Id.run do
  return Binary64.toBinary32 (s.vertCompFiltState.vel + s.velOffsetNED.z)

end NavEKF3_core

namespace NavEKF3_core

/-- C++ `void NavEKF3_core::getAccelBias(Vector3f & accelBias) const`, `AP_NavEKF3/AP_NavEKF3_Outputs.cpp:145-152`. -/
def getAccelBias (s : State) (accelBias : Vector3f.State) : Vector3f.State := Id.run do
  let mut accelBias := accelBias
  if !s.statesInitialised then
    accelBias := Vector3f.zero accelBias
    return accelBias
  accelBias := Vector3p.tofloat (Vector3p.op_div ({ x := s.statesArray[13]!, y := s.statesArray[14]!, z := s.statesArray[15]! } : Vector3p.State) s.dtEkfAvg)
  return accelBias

end NavEKF3_core

namespace NavEKF3_core

/-- C++ `bool NavEKF3_core::getVariances(float & velVar, float & posVar, float & hgtVar, Vector3f & magVar, float & tasVar, Vector2f & offset) const`, `AP_NavEKF3/AP_NavEKF3_Outputs.cpp:484-497`. -/
def getVariances (s : State) (velVar : Binary32) (posVar : Binary32) (hgtVar : Binary32) (magVar : Vector3f.State) (tasVar : Binary32) (offset : Vector2f.State) : Binary32 × Binary32 × Binary32 × Vector3f.State × Binary32 × Vector2f.State × Bool := Id.run do
  let mut velVar := velVar
  let mut posVar := posVar
  let mut hgtVar := hgtVar
  let mut magVar := magVar
  let mut tasVar := tasVar
  let mut offset := offset
  velVar := Binary64.toBinary32 (Binary64.sqrt s.velTestRatio)
  posVar := Binary64.toBinary32 (Binary64.sqrt s.posTestRatio)
  hgtVar := Binary64.toBinary32 (Binary64.sqrt s.hgtTestRatio)
  magVar := { magVar with x := Binary64.toBinary32 (Binary64.sqrt (Estimator_lib.MAX_double2 s.magTestRatio.x s.yawTestRatio)) }
  magVar := { magVar with y := Binary64.toBinary32 (Binary64.sqrt (Estimator_lib.MAX_double2 s.magTestRatio.y s.yawTestRatio)) }
  magVar := { magVar with z := Binary64.toBinary32 (Binary64.sqrt (Estimator_lib.MAX_double2 s.magTestRatio.z s.yawTestRatio)) }
  tasVar := Binary64.toBinary32 (Binary64.sqrt s.tas.testRatio)
  offset := Vector2p.tofloat s.posResetNE
  return (velVar, posVar, hgtVar, magVar, tasVar, offset, true)

end NavEKF3_core

namespace NavEKF3_core

/-- C++ `void NavEKF3_core::getFilterStatus(nav_filter_status & status) const`, `AP_NavEKF3/AP_NavEKF3_Outputs.cpp:584-587`. -/
def getFilterStatus (s : State) (status : UInt32) : UInt32 := Id.run do
  let mut status := status
  status := s.filterStatus
  return status

end NavEKF3_core

namespace NavEKF3_core

/-- C++ `bool NavEKF3_core::getHAGL(float & HAGL) const`, `AP_NavEKF3/AP_NavEKF3_Outputs.cpp:293-304`. -/
def getHAGL (s : State) (HAGL : Binary32) : Binary32 × Bool := Id.run do
  let mut HAGL := HAGL
  HAGL := Binary64.toBinary32 (s.terrainState - s.outputDataNew.position.z - s.posOffsetNED.z)
  return (HAGL, !s.hgtTimeout && s.gndOffsetValid && healthy s)

end NavEKF3_core

namespace NavEKF3_core

/-- C++ `bool NavEKF3_core::getWind(Vector3f & wind) const`, `AP_NavEKF3/AP_NavEKF3_Outputs.cpp:169-175`. -/
def getWind (s : State) (wind : Vector3f.State) : Vector3f.State × Bool := Id.run do
  let mut wind := wind
  wind := { wind with x := Binary64.toBinary32 s.statesArray[22]! }
  wind := { wind with y := Binary64.toBinary32 s.statesArray[23]! }
  wind := { wind with z := (Binary32.ofBits 0x00000000 /- 0.0f -/) }
  return (wind, !s.inhibitWindStates)

end NavEKF3_core

namespace NavEKF3_core

/-- C++ `bool NavEKF3_core::isVibrationAffected() const`, `AP_NavEKF3/AP_NavEKF3_core.h:477`. -/
def isVibrationAffected (s : State) : Bool := Id.run do
  return s.badIMUdata

end NavEKF3_core

namespace NavEKF3_core

/-- C++ `void NavEKF3_core::setTerrainHgtStable(bool val)`, `AP_NavEKF3/AP_NavEKF3_VehicleStatus.cpp:459-462`. -/
def setTerrainHgtStable (s : State) (val : Bool) : State := Id.run do
  let mut s := s
  s := { s with terrainHgtStable := val }
  return s

end NavEKF3_core

namespace NavEKF3_core

/-- C++ `void NavEKF3_core::EKFGSF_requestYawReset()`, `AP_NavEKF3/AP_NavEKF3_Control.cpp:899-902`. -/
def EKFGSF_requestYawReset (s : State) : State := Id.run do
  let mut s := s
  s := { s with EKFGSF_yaw_reset_request_ms := s.imuSampleTime_ms }
  return s

end NavEKF3_core

namespace NavEKF3_core

/-- C++ `bool NavEKF3_core::getInnovations(Vector3f & velInnov, Vector3f & posInnov, Vector3f & magInnov, float & tasInnov, float & yawInnov) const`, `AP_NavEKF3/AP_NavEKF3_Outputs.cpp:455-469`. -/
def getInnovations (s : State) (velInnov : Vector3f.State) (posInnov : Vector3f.State) (magInnov : Vector3f.State) (tasInnov : Binary32) (yawInnov : Binary32) : Vector3f.State × Vector3f.State × Vector3f.State × Binary32 × Binary32 × Bool := Id.run do
  let mut velInnov := velInnov
  let mut posInnov := posInnov
  let mut magInnov := magInnov
  let mut tasInnov := tasInnov
  let mut yawInnov := yawInnov
  velInnov := { velInnov with x := Binary64.toBinary32 s.innovVelPos[0]! }
  velInnov := { velInnov with y := Binary64.toBinary32 s.innovVelPos[1]! }
  velInnov := { velInnov with z := Binary64.toBinary32 s.innovVelPos[2]! }
  posInnov := { posInnov with x := Binary64.toBinary32 s.innovVelPos[3]! }
  posInnov := { posInnov with y := Binary64.toBinary32 s.innovVelPos[4]! }
  posInnov := { posInnov with z := Binary64.toBinary32 s.innovVelPos[5]! }
  magInnov := { magInnov with x := Binary64.toBinary32 ((Binary64.ofBits 0x408f400000000000 /- 1e3f -/) * s.innovMag.x) }
  magInnov := { magInnov with y := Binary64.toBinary32 ((Binary64.ofBits 0x408f400000000000 /- 1e3f -/) * s.innovMag.y) }
  magInnov := { magInnov with z := Binary64.toBinary32 ((Binary64.ofBits 0x408f400000000000 /- 1e3f -/) * s.innovMag.z) }
  tasInnov := Binary64.toBinary32 s.tas.innov
  yawInnov := Binary64.toBinary32 s.innovYaw
  return (velInnov, posInnov, magInnov, tasInnov, yawInnov, true)

end NavEKF3_core

namespace NavEKF3_core

/-- C++ `void NavEKF3_core::clearStatesInitialised()`, `AP_NavEKF3/AP_NavEKF3_core.h:489`. -/
def clearStatesInitialised (s : State) : State := Id.run do
  let mut s := s
  s := { s with statesInitialised := false }
  return s

/-- C++ `bool NavEKF3_core::isStatesInitialised() const`, `AP_NavEKF3/AP_NavEKF3_core.h:492`. -/
def isStatesInitialised (s : State) : Bool := Id.run do
  return s.statesInitialised

end NavEKF3_core

namespace NavEKF3_core

/-- C++ `bool NavEKF3_core::getPosVelUncertainty(float & pos_horiz_m, float & pos_vert_m, float & vel_m_s) const`, `AP_NavEKF3/AP_NavEKF3_Outputs.cpp:500-514`. -/
def getPosVelUncertainty (s : State) (pos_horiz_m : Binary32) (pos_vert_m : Binary32) (vel_m_s : Binary32) : Binary32 × Binary32 × Binary32 × Bool := Id.run do
  let mut pos_horiz_m := pos_horiz_m
  let mut pos_vert_m := pos_vert_m
  let mut vel_m_s := vel_m_s
  if !s.statesInitialised then
    return (pos_horiz_m, pos_vert_m, vel_m_s, false)
  pos_horiz_m := Binary64.toBinary32 (Binary64.sqrt (s.Pmut[175]! + s.Pmut[200]!))
  pos_vert_m := Binary64.toBinary32 (Binary64.sqrt s.Pmut[225]!)
  vel_m_s := Binary64.toBinary32 (Binary64.sqrt (Estimator_lib.MAX_double2 (Estimator_lib.MAX_double2 s.Pmut[100]! s.Pmut[125]!) s.Pmut[150]!))
  return (pos_horiz_m, pos_vert_m, vel_m_s, true)

end NavEKF3_core

namespace NavEKF3_core

/-- C++ `void NavEKF3_core::getMagNED(Vector3f & magNED) const`, `AP_NavEKF3/AP_NavEKF3_Outputs.cpp:410-413`. -/
def getMagNED (s : State) (magNED : Vector3f.State) : Vector3f.State := Id.run do
  let mut magNED := magNED
  magNED := Vector3p.tofloat (Vector3p.op_mul_double ({ x := s.statesArray[16]!, y := s.statesArray[17]!, z := s.statesArray[18]! } : Vector3p.State) (Binary64.ofBits 0x408f400000000000 /- 1000.0f -/))
  return magNED

end NavEKF3_core

namespace NavEKF3_core

/-- C++ `void NavEKF3_core::getMagXYZ(Vector3f & magXYZ) const`, `AP_NavEKF3/AP_NavEKF3_Outputs.cpp:416-419`. -/
def getMagXYZ (s : State) (magXYZ : Vector3f.State) : Vector3f.State := Id.run do
  let mut magXYZ := magXYZ
  magXYZ := Vector3p.tofloat (Vector3p.op_mul_double ({ x := s.statesArray[19]!, y := s.statesArray[20]!, z := s.statesArray[21]! } : Vector3p.State) (Binary64.ofBits 0x408f400000000000 /- 1000.0f -/))
  return magXYZ

end NavEKF3_core

namespace NavEKF3_core

/-- C++ `uint8_t NavEKF3_core::getActiveAirspeed() const`, `AP_NavEKF3/AP_NavEKF3_Outputs.cpp:449-452`. -/
def getActiveAirspeed (s : State) : UInt8 := Id.run do
  return s.selected_airspeed

end NavEKF3_core

namespace NavEKF3_core

/-- C++ `void NavEKF3_core::resetGyroBias()`, `AP_NavEKF3/AP_NavEKF3_GyroBias.cpp:9-17`. -/
def resetGyroBias (s : State) : State := Id.run do
  let mut s := s
  let t'1 := Vector3p.zero ({ x := s.statesArray[10]!, y := s.statesArray[11]!, z := s.statesArray[12]! } : Vector3p.State)
  s := { s with statesArray := (((s.statesArray.set! 10 t'1.x).set! 11 t'1.y).set! 12 t'1.z) }
  s := zeroStatesVarCov s (Int8.toUInt8 (Int32.toInt8 (10 : Int32))) (Int8.toUInt8 (Int32.toInt8 (12 : Int32)))
  s := { s with Pmut := s.Pmut.set! 250 (Estimator_lib.sq_double (Estimator_lib.radians_double ((Binary64.ofBits 0x3fe0000000000000 /- 0.5f -/) * s.dtIMUavg))) }
  s := { s with Pmut := s.Pmut.set! 275 (s.Pmut[250]!) }
  s := { s with Pmut := s.Pmut.set! 300 (s.Pmut[250]!) }
  return s

end NavEKF3_core

end Estimator_lib
