import ArduLean.Runtime.CFloat
import ArduLean.Estimator.libraries.AP_Math.AP_Math
import ArduLean.Estimator.World
import ArduLean.Estimator.libraries.AP_Common.AP_Common
import ArduLean.Estimator.libraries.AP_Param.AP_Param
import ArduLean.Estimator.libraries.AP_NavEKF.AP_NavEKF

/-!
ArduPilot `libraries/AP_NavEKF3`, part 1 of 4. Sources: `libraries/AP_NavEKF3/LogStructure.h`, `libraries/AP_NavEKF3/AP_NavEKF3.h`, `libraries/AP_NavEKF3/AP_NavEKF3_core.h`, `libraries/AP_NavEKF3/AP_NavEKF3_Measurements.cpp`, `libraries/AP_NavEKF3/AP_NavEKF3.cpp`, `libraries/AP_NavEKF3/AP_NavEKF3_Control.cpp`.

Items of `lean/Estimator_lib.lean` (the estimator translation), unchanged; placed by `tools/split_modules.py` (`ArduLean/Estimator/INDEX.md`).
-/

open FloatLib.Floats (Binary32 Binary64)

set_option maxRecDepth 200000
-- AP_DAL's `const log_RISH old_RISH = _RISH;` read only by WRITE_REPLAY_BLOCK_IFCHANGED, which is `(void)old`
-- without logging (HAL_LOGGING_ENABLED 0): an unused binding, as in the C++
set_option linter.unusedVariables false

namespace Estimator_lib

namespace NavEKF3

/-- C++ `struct NavEKF3::(unnamed struct at AP_NavEKF3/AP_NavEKF3.h:531:5)`, `AP_NavEKF3/AP_NavEKF3.h:531-534`. -/
structure yaw_reset_data_t where
  /-- `uint16_t count` of `NavEKF3::(unnamed struct at AP_NavEKF3/AP_NavEKF3.h:531:5)` (`AP_NavEKF3/AP_NavEKF3.h:532`). -/
  count : UInt16 := (0 : UInt16)
  /-- `uint16_t last_core_count` of `NavEKF3::(unnamed struct at AP_NavEKF3/AP_NavEKF3.h:531:5)` (`AP_NavEKF3/AP_NavEKF3.h:533`). -/
  last_core_count : UInt16 := (0 : UInt16)
deriving Inhabited

/-- C++ `struct NavEKF3::(unnamed struct at AP_NavEKF3/AP_NavEKF3.h:536:5)`, `AP_NavEKF3/AP_NavEKF3.h:536-539`. -/
structure pos_reset_data_t where
  /-- `uint16_t count` of `NavEKF3::(unnamed struct at AP_NavEKF3/AP_NavEKF3.h:536:5)` (`AP_NavEKF3/AP_NavEKF3.h:537`). -/
  count : UInt16 := (0 : UInt16)
  /-- `uint16_t last_core_count` of `NavEKF3::(unnamed struct at AP_NavEKF3/AP_NavEKF3.h:536:5)` (`AP_NavEKF3/AP_NavEKF3.h:538`). -/
  last_core_count : UInt16 := (0 : UInt16)
deriving Inhabited

/-- C++ `struct NavEKF3::(unnamed struct at AP_NavEKF3/AP_NavEKF3.h:541:5)`, `AP_NavEKF3/AP_NavEKF3.h:541-544`. -/
structure pos_down_reset_data_t where
  /-- `uint16_t count` of `NavEKF3::(unnamed struct at AP_NavEKF3/AP_NavEKF3.h:541:5)` (`AP_NavEKF3/AP_NavEKF3.h:542`). -/
  count : UInt16 := (0 : UInt16)
  /-- `uint16_t last_core_count` of `NavEKF3::(unnamed struct at AP_NavEKF3/AP_NavEKF3.h:541:5)` (`AP_NavEKF3/AP_NavEKF3.h:543`). -/
  last_core_count : UInt16 := (0 : UInt16)
deriving Inhabited

end NavEKF3

namespace NavEKF3

/-- State of C++ `NavEKF3` (`AP_NavEKF3/AP_NavEKF3.h:31-590`): its data members. -/
structure State where
  /-- `uint8_t num_cores` of `NavEKF3` (`AP_NavEKF3/AP_NavEKF3.h:386`). -/
  num_cores : UInt8 := (0 : UInt8)
  /-- `uint8_t primary` of `NavEKF3` (`AP_NavEKF3/AP_NavEKF3.h:387`). -/
  primary : UInt8 := (0 : UInt8)
  /-- `NavEKF3_core * core` of `NavEKF3` (`AP_NavEKF3/AP_NavEKF3.h:388`). -/
  core : WPtr := WPtr.null
  /-- `uint32_t _frameTimeUsec` of `NavEKF3` (`AP_NavEKF3/AP_NavEKF3.h:390`). -/
  _frameTimeUsec : UInt32 := (0 : UInt32)
  /-- `uint8_t _framesPerPrediction` of `NavEKF3` (`AP_NavEKF3/AP_NavEKF3.h:391`). -/
  _framesPerPrediction : UInt8 := (0 : UInt8)
  /-- `AP_Int8 _enable` of `NavEKF3` (`AP_NavEKF3/AP_NavEKF3.h:402`). -/
  _enable : AP_ParamT_signed_char_1.State := {}
  /-- `AP_Float _gpsHorizVelNoise` of `NavEKF3` (`AP_NavEKF3/AP_NavEKF3.h:403`). -/
  _gpsHorizVelNoise : AP_ParamT_float_4.State := {}
  /-- `AP_Float _gpsVertVelNoise` of `NavEKF3` (`AP_NavEKF3/AP_NavEKF3.h:404`). -/
  _gpsVertVelNoise : AP_ParamT_float_4.State := {}
  /-- `AP_Float _gpsHorizPosNoise` of `NavEKF3` (`AP_NavEKF3/AP_NavEKF3.h:405`). -/
  _gpsHorizPosNoise : AP_ParamT_float_4.State := {}
  /-- `AP_Float _baroAltNoise` of `NavEKF3` (`AP_NavEKF3/AP_NavEKF3.h:406`). -/
  _baroAltNoise : AP_ParamT_float_4.State := {}
  /-- `AP_Float _magNoise` of `NavEKF3` (`AP_NavEKF3/AP_NavEKF3.h:407`). -/
  _magNoise : AP_ParamT_float_4.State := {}
  /-- `AP_Float _easNoise` of `NavEKF3` (`AP_NavEKF3/AP_NavEKF3.h:408`). -/
  _easNoise : AP_ParamT_float_4.State := {}
  /-- `AP_Float _windVelProcessNoise` of `NavEKF3` (`AP_NavEKF3/AP_NavEKF3.h:409`). -/
  _windVelProcessNoise : AP_ParamT_float_4.State := {}
  /-- `AP_Float _wndVarHgtRateScale` of `NavEKF3` (`AP_NavEKF3/AP_NavEKF3.h:410`). -/
  _wndVarHgtRateScale : AP_ParamT_float_4.State := {}
  /-- `AP_Float _magEarthProcessNoise` of `NavEKF3` (`AP_NavEKF3/AP_NavEKF3.h:411`). -/
  _magEarthProcessNoise : AP_ParamT_float_4.State := {}
  /-- `AP_Float _magBodyProcessNoise` of `NavEKF3` (`AP_NavEKF3/AP_NavEKF3.h:412`). -/
  _magBodyProcessNoise : AP_ParamT_float_4.State := {}
  /-- `AP_Float _gyrNoise` of `NavEKF3` (`AP_NavEKF3/AP_NavEKF3.h:413`). -/
  _gyrNoise : AP_ParamT_float_4.State := {}
  /-- `AP_Float _accNoise` of `NavEKF3` (`AP_NavEKF3/AP_NavEKF3.h:414`). -/
  _accNoise : AP_ParamT_float_4.State := {}
  /-- `AP_Float _gyroBiasProcessNoise` of `NavEKF3` (`AP_NavEKF3/AP_NavEKF3.h:415`). -/
  _gyroBiasProcessNoise : AP_ParamT_float_4.State := {}
  /-- `AP_Float _accelBiasProcessNoise` of `NavEKF3` (`AP_NavEKF3/AP_NavEKF3.h:416`). -/
  _accelBiasProcessNoise : AP_ParamT_float_4.State := {}
  /-- `AP_Int16 _hgtDelay_ms` of `NavEKF3` (`AP_NavEKF3/AP_NavEKF3.h:417`). -/
  _hgtDelay_ms : AP_ParamT_short_2.State := {}
  /-- `AP_Int16 _gpsVelInnovGate` of `NavEKF3` (`AP_NavEKF3/AP_NavEKF3.h:418`). -/
  _gpsVelInnovGate : AP_ParamT_short_2.State := {}
  /-- `AP_Int16 _gpsPosInnovGate` of `NavEKF3` (`AP_NavEKF3/AP_NavEKF3.h:419`). -/
  _gpsPosInnovGate : AP_ParamT_short_2.State := {}
  /-- `AP_Int16 _hgtInnovGate` of `NavEKF3` (`AP_NavEKF3/AP_NavEKF3.h:420`). -/
  _hgtInnovGate : AP_ParamT_short_2.State := {}
  /-- `AP_Int16 _magInnovGate` of `NavEKF3` (`AP_NavEKF3/AP_NavEKF3.h:421`). -/
  _magInnovGate : AP_ParamT_short_2.State := {}
  /-- `AP_Int16 _tasInnovGate` of `NavEKF3` (`AP_NavEKF3/AP_NavEKF3.h:422`). -/
  _tasInnovGate : AP_ParamT_short_2.State := {}
  /-- `AP_Int8 _magCal` of `NavEKF3` (`AP_NavEKF3/AP_NavEKF3.h:423`). -/
  _magCal : AP_ParamT_signed_char_1.State := {}
  /-- `AP_Int8 _gpsGlitchRadiusMax` of `NavEKF3` (`AP_NavEKF3/AP_NavEKF3.h:424`). -/
  _gpsGlitchRadiusMax : AP_ParamT_signed_char_1.State := {}
  /-- `AP_Float _flowNoise` of `NavEKF3` (`AP_NavEKF3/AP_NavEKF3.h:425`). -/
  _flowNoise : AP_ParamT_float_4.State := {}
  /-- `AP_Int16 _flowInnovGate` of `NavEKF3` (`AP_NavEKF3/AP_NavEKF3.h:426`). -/
  _flowInnovGate : AP_ParamT_short_2.State := {}
  /-- `AP_Int8 _flowDelay_ms` of `NavEKF3` (`AP_NavEKF3/AP_NavEKF3.h:427`). -/
  _flowDelay_ms : AP_ParamT_signed_char_1.State := {}
  /-- `AP_Int16 _rngInnovGate` of `NavEKF3` (`AP_NavEKF3/AP_NavEKF3.h:428`). -/
  _rngInnovGate : AP_ParamT_short_2.State := {}
  /-- `AP_Float _maxFlowRate` of `NavEKF3` (`AP_NavEKF3/AP_NavEKF3.h:429`). -/
  _maxFlowRate : AP_ParamT_float_4.State := {}
  /-- `AP_Float _flowNavGainHgt` of `NavEKF3` (`AP_NavEKF3/AP_NavEKF3.h:430`). -/
  _flowNavGainHgt : AP_ParamT_float_4.State := {}
  /-- `AP_Float _rngNoise` of `NavEKF3` (`AP_NavEKF3/AP_NavEKF3.h:431`). -/
  _rngNoise : AP_ParamT_float_4.State := {}
  /-- `AP_UInt8 _gpsCheck` of `NavEKF3` (`AP_NavEKF3/AP_NavEKF3.h:432`). -/
  _gpsCheck : AP_ParamT_unsigned_char_1.State := {}
  /-- `AP_UInt8 _imuMask` of `NavEKF3` (`AP_NavEKF3/AP_NavEKF3.h:433`). -/
  _imuMask : AP_ParamT_unsigned_char_1.State := {}
  /-- `AP_Int16 _gpsCheckScaler` of `NavEKF3` (`AP_NavEKF3/AP_NavEKF3.h:434`). -/
  _gpsCheckScaler : AP_ParamT_short_2.State := {}
  /-- `AP_Float _noaidHorizNoise` of `NavEKF3` (`AP_NavEKF3/AP_NavEKF3.h:435`). -/
  _noaidHorizNoise : AP_ParamT_float_4.State := {}
  /-- `AP_Float _yawNoise` of `NavEKF3` (`AP_NavEKF3/AP_NavEKF3.h:436`). -/
  _yawNoise : AP_ParamT_float_4.State := {}
  /-- `AP_Int16 _yawInnovGate` of `NavEKF3` (`AP_NavEKF3/AP_NavEKF3.h:437`). -/
  _yawInnovGate : AP_ParamT_short_2.State := {}
  /-- `AP_Int8 _tauVelPosOutput` of `NavEKF3` (`AP_NavEKF3/AP_NavEKF3.h:438`). -/
  _tauVelPosOutput : AP_ParamT_signed_char_1.State := {}
  /-- `AP_Int8 _useRngSwHgt` of `NavEKF3` (`AP_NavEKF3/AP_NavEKF3.h:439`). -/
  _useRngSwHgt : AP_ParamT_signed_char_1.State := {}
  /-- `AP_Float _terrGradMax` of `NavEKF3` (`AP_NavEKF3/AP_NavEKF3.h:440`). -/
  _terrGradMax : AP_ParamT_float_4.State := {}
  /-- `AP_Float _rngBcnNoise` of `NavEKF3` (`AP_NavEKF3/AP_NavEKF3.h:441`). -/
  _rngBcnNoise : AP_ParamT_float_4.State := {}
  /-- `AP_Int16 _rngBcnInnovGate` of `NavEKF3` (`AP_NavEKF3/AP_NavEKF3.h:442`). -/
  _rngBcnInnovGate : AP_ParamT_short_2.State := {}
  /-- `AP_Int8 _rngBcnDelay_ms` of `NavEKF3` (`AP_NavEKF3/AP_NavEKF3.h:443`). -/
  _rngBcnDelay_ms : AP_ParamT_signed_char_1.State := {}
  /-- `AP_Float _useRngSwSpd` of `NavEKF3` (`AP_NavEKF3/AP_NavEKF3.h:444`). -/
  _useRngSwSpd : AP_ParamT_float_4.State := {}
  /-- `AP_Float _accBiasLim` of `NavEKF3` (`AP_NavEKF3/AP_NavEKF3.h:445`). -/
  _accBiasLim : AP_ParamT_float_4.State := {}
  /-- `AP_UInt8 _magMask` of `NavEKF3` (`AP_NavEKF3/AP_NavEKF3.h:446`). -/
  _magMask : AP_ParamT_unsigned_char_1.State := {}
  /-- `AP_UInt8 _originHgtMode` of `NavEKF3` (`AP_NavEKF3/AP_NavEKF3.h:447`). -/
  _originHgtMode : AP_ParamT_unsigned_char_1.State := {}
  /-- `AP_Float _visOdmVelErrMax` of `NavEKF3` (`AP_NavEKF3/AP_NavEKF3.h:448`). -/
  _visOdmVelErrMax : AP_ParamT_float_4.State := {}
  /-- `AP_Float _visOdmVelErrMin` of `NavEKF3` (`AP_NavEKF3/AP_NavEKF3.h:449`). -/
  _visOdmVelErrMin : AP_ParamT_float_4.State := {}
  /-- `AP_Float _wencOdmVelErr` of `NavEKF3` (`AP_NavEKF3/AP_NavEKF3.h:450`). -/
  _wencOdmVelErr : AP_ParamT_float_4.State := {}
  /-- `AP_Int8 _flowUse` of `NavEKF3` (`AP_NavEKF3/AP_NavEKF3.h:451`). -/
  _flowUse : AP_ParamT_signed_char_1.State := {}
  /-- `AP_Float _hrt_filt_freq` of `NavEKF3` (`AP_NavEKF3/AP_NavEKF3.h:452`). -/
  _hrt_filt_freq : AP_ParamT_float_4.State := {}
  /-- `AP_Int16 _mag_ef_limit` of `NavEKF3` (`AP_NavEKF3/AP_NavEKF3.h:453`). -/
  _mag_ef_limit : AP_ParamT_short_2.State := {}
  /-- `AP_UInt8 _gsfRunMask` of `NavEKF3` (`AP_NavEKF3/AP_NavEKF3.h:454`). -/
  _gsfRunMask : AP_ParamT_unsigned_char_1.State := {}
  /-- `AP_UInt8 _gsfUseMask` of `NavEKF3` (`AP_NavEKF3/AP_NavEKF3.h:455`). -/
  _gsfUseMask : AP_ParamT_unsigned_char_1.State := {}
  /-- `AP_Int8 _gsfResetMaxCount` of `NavEKF3` (`AP_NavEKF3/AP_NavEKF3.h:456`). -/
  _gsfResetMaxCount : AP_ParamT_signed_char_1.State := {}
  /-- `AP_Float _err_thresh` of `NavEKF3` (`AP_NavEKF3/AP_NavEKF3.h:457`). -/
  _err_thresh : AP_ParamT_float_4.State := {}
  /-- `AP_UInt32 _affinity` of `NavEKF3` (`AP_NavEKF3/AP_NavEKF3.h:458`). -/
  _affinity : AP_ParamT_unsigned_int_3.State := {}
  /-- `AP_Float _dragObsNoise` of `NavEKF3` (`AP_NavEKF3/AP_NavEKF3.h:459`). -/
  _dragObsNoise : AP_ParamT_float_4.State := {}
  /-- `AP_Float _ballisticCoef_x` of `NavEKF3` (`AP_NavEKF3/AP_NavEKF3.h:460`). -/
  _ballisticCoef_x : AP_ParamT_float_4.State := {}
  /-- `AP_Float _ballisticCoef_y` of `NavEKF3` (`AP_NavEKF3/AP_NavEKF3.h:461`). -/
  _ballisticCoef_y : AP_ParamT_float_4.State := {}
  /-- `AP_Float _momentumDragCoef` of `NavEKF3` (`AP_NavEKF3/AP_NavEKF3.h:462`). -/
  _momentumDragCoef : AP_ParamT_float_4.State := {}
  /-- `AP_UInt8 _betaMask` of `NavEKF3` (`AP_NavEKF3/AP_NavEKF3.h:463`). -/
  _betaMask : AP_ParamT_unsigned_char_1.State := {}
  /-- `AP_Float _ognmTestScaleFactor` of `NavEKF3` (`AP_NavEKF3/AP_NavEKF3.h:464`). -/
  _ognmTestScaleFactor : AP_ParamT_float_4.State := {}
  /-- `AP_Float _baroGndEffectDeadZone` of `NavEKF3` (`AP_NavEKF3/AP_NavEKF3.h:465`). -/
  _baroGndEffectDeadZone : AP_ParamT_float_4.State := {}
  /-- `AP_UInt8 _primary_core` of `NavEKF3` (`AP_NavEKF3/AP_NavEKF3.h:466`). -/
  _primary_core : AP_ParamT_unsigned_char_1.State := {}
  /-- `AP_Enum<LogLevel> _log_level` of `NavEKF3` (`AP_NavEKF3/AP_NavEKF3.h:467`). -/
  _log_level : AP_Enum_NavEKF3_LogLevel.State := {}
  /-- `AP_Float _gpsVAccThreshold` of `NavEKF3` (`AP_NavEKF3/AP_NavEKF3.h:468`). -/
  _gpsVAccThreshold : AP_ParamT_float_4.State := {}
  /-- `AP_UInt32 _options` of `NavEKF3` (`AP_NavEKF3/AP_NavEKF3.h:469`). -/
  _options : AP_ParamT_unsigned_int_3.State := {}
  /-- `const float gpsNEVelVarAccScale` of `NavEKF3` (`AP_NavEKF3/AP_NavEKF3.h:488`). -/
  gpsNEVelVarAccScale : Binary32 := (Binary32.ofBits 0x3d4ccccd /- 0.05f -/)
  /-- `const float gpsDVelVarAccScale` of `NavEKF3` (`AP_NavEKF3/AP_NavEKF3.h:489`). -/
  gpsDVelVarAccScale : Binary32 := (Binary32.ofBits 0x3d8f5c29 /- 0.07f -/)
  /-- `const float gpsPosVarAccScale` of `NavEKF3` (`AP_NavEKF3/AP_NavEKF3.h:490`). -/
  gpsPosVarAccScale : Binary32 := (Binary32.ofBits 0x3d4ccccd /- 0.05f -/)
  /-- `const float extNavVelVarAccScale` of `NavEKF3` (`AP_NavEKF3/AP_NavEKF3.h:491`). -/
  extNavVelVarAccScale : Binary32 := (Binary32.ofBits 0x3d4ccccd /- 0.05f -/)
  /-- `const uint16_t magDelay_ms` of `NavEKF3` (`AP_NavEKF3/AP_NavEKF3.h:492`). -/
  magDelay_ms : UInt16 := Int16.toUInt16 (Int32.toInt16 (60 : Int32))
  /-- `const uint16_t tasDelay_ms` of `NavEKF3` (`AP_NavEKF3/AP_NavEKF3.h:493`). -/
  tasDelay_ms : UInt16 := Int16.toUInt16 (Int32.toInt16 (100 : Int32))
  /-- `const uint16_t tiltDriftTimeMax_ms` of `NavEKF3` (`AP_NavEKF3/AP_NavEKF3.h:494`). -/
  tiltDriftTimeMax_ms : UInt16 := Int16.toUInt16 (Int32.toInt16 (15000 : Int32))
  /-- `const uint16_t posRetryTimeUseVel_ms` of `NavEKF3` (`AP_NavEKF3/AP_NavEKF3.h:495`). -/
  posRetryTimeUseVel_ms : UInt16 := Int16.toUInt16 (Int32.toInt16 (10000 : Int32))
  /-- `const uint16_t posRetryTimeNoVel_ms` of `NavEKF3` (`AP_NavEKF3/AP_NavEKF3.h:496`). -/
  posRetryTimeNoVel_ms : UInt16 := Int16.toUInt16 (Int32.toInt16 (7000 : Int32))
  /-- `const uint16_t hgtRetryTimeMode0_ms` of `NavEKF3` (`AP_NavEKF3/AP_NavEKF3.h:497`). -/
  hgtRetryTimeMode0_ms : UInt16 := Int16.toUInt16 (Int32.toInt16 (10000 : Int32))
  /-- `const uint16_t hgtRetryTimeMode12_ms` of `NavEKF3` (`AP_NavEKF3/AP_NavEKF3.h:498`). -/
  hgtRetryTimeMode12_ms : UInt16 := Int16.toUInt16 (Int32.toInt16 (5000 : Int32))
  /-- `const uint16_t tasRetryTime_ms` of `NavEKF3` (`AP_NavEKF3/AP_NavEKF3.h:499`). -/
  tasRetryTime_ms : UInt16 := Int16.toUInt16 (Int32.toInt16 (5000 : Int32))
  /-- `const uint16_t dragFailTimeLimit_ms` of `NavEKF3` (`AP_NavEKF3/AP_NavEKF3.h:500`). -/
  dragFailTimeLimit_ms : UInt16 := Int16.toUInt16 (Int32.toInt16 (5000 : Int32))
  /-- `const uint32_t magFailTimeLimit_ms` of `NavEKF3` (`AP_NavEKF3/AP_NavEKF3.h:501`). -/
  magFailTimeLimit_ms : UInt32 := Int32.toUInt32 (10000 : Int32)
  /-- `const float magVarRateScale` of `NavEKF3` (`AP_NavEKF3/AP_NavEKF3.h:502`). -/
  magVarRateScale : Binary32 := (Binary32.ofBits 0x3ba3d70a /- 0.005f -/)
  /-- `const float gyroBiasNoiseScaler` of `NavEKF3` (`AP_NavEKF3/AP_NavEKF3.h:503`). -/
  gyroBiasNoiseScaler : Binary32 := (Binary32.ofBits 0x40000000 /- 2.0f -/)
  /-- `const uint16_t hgtAvg_ms` of `NavEKF3` (`AP_NavEKF3/AP_NavEKF3.h:504`). -/
  hgtAvg_ms : UInt16 := Int16.toUInt16 (Int32.toInt16 (100 : Int32))
  /-- `const uint16_t betaAvg_ms` of `NavEKF3` (`AP_NavEKF3/AP_NavEKF3.h:505`). -/
  betaAvg_ms : UInt16 := Int16.toUInt16 (Int32.toInt16 (100 : Int32))
  /-- `const float covTimeStepMax` of `NavEKF3` (`AP_NavEKF3/AP_NavEKF3.h:506`). -/
  covTimeStepMax : Binary32 := (Binary32.ofBits 0x3dcccccd /- 0.1f -/)
  /-- `const float covDelAngMax` of `NavEKF3` (`AP_NavEKF3/AP_NavEKF3.h:507`). -/
  covDelAngMax : Binary32 := (Binary32.ofBits 0x3d4ccccd /- 0.05f -/)
  /-- `const float DCM33FlowMin` of `NavEKF3` (`AP_NavEKF3/AP_NavEKF3.h:508`). -/
  DCM33FlowMin : Binary32 := (Binary32.ofBits 0x3f35c28f /- 0.71f -/)
  /-- `const float fScaleFactorPnoise` of `NavEKF3` (`AP_NavEKF3/AP_NavEKF3.h:509`). -/
  fScaleFactorPnoise : Binary32 := (Binary32.ofBits 0x2edbe6ff /- 1e-10f -/)
  /-- `const uint8_t flowTimeDeltaAvg_ms` of `NavEKF3` (`AP_NavEKF3/AP_NavEKF3.h:510`). -/
  flowTimeDeltaAvg_ms : UInt8 := Int8.toUInt8 (Int32.toInt8 (100 : Int32))
  /-- `const uint32_t flowIntervalMax_ms` of `NavEKF3` (`AP_NavEKF3/AP_NavEKF3.h:511`). -/
  flowIntervalMax_ms : UInt32 := Int32.toUInt32 (100 : Int32)
  /-- `const float gndEffectBaroScaler` of `NavEKF3` (`AP_NavEKF3/AP_NavEKF3.h:512`). -/
  gndEffectBaroScaler : Binary32 := (Binary32.ofBits 0x40800000 /- 4.0f -/)
  /-- `const uint8_t gndGradientSigma` of `NavEKF3` (`AP_NavEKF3/AP_NavEKF3.h:513`). -/
  gndGradientSigma : UInt8 := Int8.toUInt8 (Int32.toInt8 (50 : Int32))
  /-- `const uint16_t fusionTimeStep_ms` of `NavEKF3` (`AP_NavEKF3/AP_NavEKF3.h:514`). -/
  fusionTimeStep_ms : UInt16 := Int16.toUInt16 (Int32.toInt16 (10 : Int32))
  /-- `const uint8_t sensorIntervalMin_ms` of `NavEKF3` (`AP_NavEKF3/AP_NavEKF3.h:515`). -/
  sensorIntervalMin_ms : UInt8 := Int8.toUInt8 (Int32.toInt8 (50 : Int32))
  /-- `const uint8_t flowIntervalMin_ms` of `NavEKF3` (`AP_NavEKF3/AP_NavEKF3.h:516`). -/
  flowIntervalMin_ms : UInt8 := Int8.toUInt8 (Int32.toInt8 (20 : Int32))
  /-- `const uint8_t extNavIntervalMin_ms` of `NavEKF3` (`AP_NavEKF3/AP_NavEKF3.h:517`). -/
  extNavIntervalMin_ms : UInt8 := Int8.toUInt8 (Int32.toInt8 (20 : Int32))
  /-- `const float maxYawEstVelInnov` of `NavEKF3` (`AP_NavEKF3/AP_NavEKF3.h:518`). -/
  maxYawEstVelInnov : Binary32 := (Binary32.ofBits 0x40000000 /- 2.0f -/)
  /-- `const uint16_t deadReckonDeclare_ms` of `NavEKF3` (`AP_NavEKF3/AP_NavEKF3.h:519`). -/
  deadReckonDeclare_ms : UInt16 := Int16.toUInt16 (Int32.toInt16 (1000 : Int32))
  /-- `const uint16_t gpsNoFixTimeout_ms` of `NavEKF3` (`AP_NavEKF3/AP_NavEKF3.h:520`). -/
  gpsNoFixTimeout_ms : UInt16 := Int16.toUInt16 (Int32.toInt16 (2000 : Int32))
  /-- `uint64_t imuSampleTime_us` of `NavEKF3` (`AP_NavEKF3/AP_NavEKF3.h:523`). -/
  imuSampleTime_us : UInt64 := (0 : UInt64)
  /-- `uint32_t lastLaneSwitch_ms` of `NavEKF3` (`AP_NavEKF3/AP_NavEKF3.h:526`). -/
  lastLaneSwitch_ms : UInt32 := (0 : UInt32)
  /-- `uint64_t lastLogWrite_us` of `NavEKF3` (`AP_NavEKF3/AP_NavEKF3.h:529`). -/
  lastLogWrite_us : UInt64 := (0 : UInt64)
  /-- `struct (unnamed struct at AP_NavEKF3/AP_NavEKF3.h:531:5) yaw_reset_data` of `NavEKF3` (`AP_NavEKF3/AP_NavEKF3.h:534`). -/
  yaw_reset_data : NavEKF3.yaw_reset_data_t := {}
  /-- `struct (unnamed struct at AP_NavEKF3/AP_NavEKF3.h:536:5) pos_reset_data` of `NavEKF3` (`AP_NavEKF3/AP_NavEKF3.h:539`). -/
  pos_reset_data : NavEKF3.pos_reset_data_t := {}
  /-- `struct (unnamed struct at AP_NavEKF3/AP_NavEKF3.h:541:5) pos_down_reset_data` of `NavEKF3` (`AP_NavEKF3/AP_NavEKF3.h:544`). -/
  pos_down_reset_data : NavEKF3.pos_down_reset_data_t := {}
  /-- `bool runCoreSelection` of `NavEKF3` (`AP_NavEKF3/AP_NavEKF3.h:549`). -/
  runCoreSelection : Bool := false
  /-- `bool coreSetupRequired[3]` of `NavEKF3` (`AP_NavEKF3/AP_NavEKF3.h:550`). -/
  coreSetupRequired : Array Bool := Array.replicate 3 false
  /-- `uint8_t coreImuIndex[3]` of `NavEKF3` (`AP_NavEKF3/AP_NavEKF3.h:551`). -/
  coreImuIndex : Array UInt8 := Array.replicate 3 (0 : UInt8)
  /-- `float coreRelativeErrors[3]` of `NavEKF3` (`AP_NavEKF3/AP_NavEKF3.h:552`). -/
  coreRelativeErrors : Array Binary32 := Array.replicate 3 (Binary32.ofBits 0x00000000 /- 0.0 -/)
  /-- `float coreErrorScores[3]` of `NavEKF3` (`AP_NavEKF3/AP_NavEKF3.h:553`). -/
  coreErrorScores : Array Binary32 := Array.replicate 3 (Binary32.ofBits 0x00000000 /- 0.0 -/)
  /-- `uint64_t coreLastTimePrimary_us[3]` of `NavEKF3` (`AP_NavEKF3/AP_NavEKF3.h:554`). -/
  coreLastTimePrimary_us : Array UInt64 := Array.replicate 3 (0 : UInt64)
  /-- `Location common_EKF_origin` of `NavEKF3` (`AP_NavEKF3/AP_NavEKF3.h:557`). -/
  common_EKF_origin : Location.State := {}
  /-- `bool common_origin_valid` of `NavEKF3` (`AP_NavEKF3/AP_NavEKF3.h:558`). -/
  common_origin_valid : Bool := false
  /-- `AP_NavEKF_Source sources` of `NavEKF3` (`AP_NavEKF3/AP_NavEKF3.h:589`). -/
  sources : AP_NavEKF_Source.State := AP_NavEKF_Source.construct
deriving Inhabited

end NavEKF3

namespace NavEKF3_core

/-- C++ `struct NavEKF3_core::gps_elements`, `AP_NavEKF3/AP_NavEKF3_core.h:608-615`. -/
structure gps_elements where
  /-- `uint32_t time_ms` of `EKF_obs_element_t` (`AP_NavEKF/EKF_Buffer.h:11`). -/
  time_ms : UInt32 := (0 : UInt32)
  /-- `int32_t lat` of `NavEKF3_core::gps_elements` (`AP_NavEKF3/AP_NavEKF3_core.h:609`). -/
  lat : Int32 := (0 : Int32)
  /-- `int32_t lng` of `NavEKF3_core::gps_elements` (`AP_NavEKF3/AP_NavEKF3_core.h:609`). -/
  lng : Int32 := (0 : Int32)
  /-- `ftype hgt` of `NavEKF3_core::gps_elements` (`AP_NavEKF3/AP_NavEKF3_core.h:610`). -/
  hgt : Binary64 := (Binary64.ofBits 0x0000000000000000 /- 0.0 -/)
  /-- `Vector3F vel` of `NavEKF3_core::gps_elements` (`AP_NavEKF3/AP_NavEKF3_core.h:611`). -/
  vel : Vector3p.State := {}
  /-- `uint8_t sensor_idx` of `NavEKF3_core::gps_elements` (`AP_NavEKF3/AP_NavEKF3_core.h:612`). -/
  sensor_idx : UInt8 := (0 : UInt8)
  /-- `bool corrected` of `NavEKF3_core::gps_elements` (`AP_NavEKF3/AP_NavEKF3_core.h:613`). -/
  corrected : Bool := false
  /-- `bool have_vz` of `NavEKF3_core::gps_elements` (`AP_NavEKF3/AP_NavEKF3_core.h:614`). -/
  have_vz : Bool := false
deriving Inhabited

end NavEKF3_core

namespace NavEKF3_core

/-- C++ `struct NavEKF3_core::mag_elements`, `AP_NavEKF3/AP_NavEKF3_core.h:617-619`. -/
structure mag_elements where
  /-- `uint32_t time_ms` of `EKF_obs_element_t` (`AP_NavEKF/EKF_Buffer.h:11`). -/
  time_ms : UInt32 := (0 : UInt32)
  /-- `Vector3F mag` of `NavEKF3_core::mag_elements` (`AP_NavEKF3/AP_NavEKF3_core.h:618`). -/
  mag : Vector3p.State := {}
deriving Inhabited

end NavEKF3_core

namespace NavEKF3_core

/-- C++ `struct NavEKF3_core::baro_elements`, `AP_NavEKF3/AP_NavEKF3_core.h:621-623`. -/
structure baro_elements where
  /-- `uint32_t time_ms` of `EKF_obs_element_t` (`AP_NavEKF/EKF_Buffer.h:11`). -/
  time_ms : UInt32 := (0 : UInt32)
  /-- `ftype hgt` of `NavEKF3_core::baro_elements` (`AP_NavEKF3/AP_NavEKF3_core.h:622`). -/
  hgt : Binary64 := (Binary64.ofBits 0x0000000000000000 /- 0.0 -/)
deriving Inhabited

end NavEKF3_core

namespace NavEKF3_core

/-- C++ `struct NavEKF3_core::of_elements`, `AP_NavEKF3/AP_NavEKF3_core.h:643-649`. -/
structure of_elements where
  /-- `uint32_t time_ms` of `EKF_obs_element_t` (`AP_NavEKF/EKF_Buffer.h:11`). -/
  time_ms : UInt32 := (0 : UInt32)
  /-- `Vector2F flowRadXY` of `NavEKF3_core::of_elements` (`AP_NavEKF3/AP_NavEKF3_core.h:644`). -/
  flowRadXY : Vector2p.State := {}
  /-- `Vector2F flowRadXYcomp` of `NavEKF3_core::of_elements` (`AP_NavEKF3/AP_NavEKF3_core.h:645`). -/
  flowRadXYcomp : Vector2p.State := {}
  /-- `Vector3F bodyRadXYZ` of `NavEKF3_core::of_elements` (`AP_NavEKF3/AP_NavEKF3_core.h:646`). -/
  bodyRadXYZ : Vector3p.State := {}
  /-- `Vector3F body_offset` of `NavEKF3_core::of_elements` (`AP_NavEKF3/AP_NavEKF3_core.h:647`). -/
  body_offset : Vector3p.State := {}
  /-- `float heightOverride` of `NavEKF3_core::of_elements` (`AP_NavEKF3/AP_NavEKF3_core.h:648`). -/
  heightOverride : Binary32 := (Binary32.ofBits 0x00000000 /- 0.0 -/)
deriving Inhabited

end NavEKF3_core

namespace NavEKF3_core

/-- C++ `struct NavEKF3_core::imu_elements`, `AP_NavEKF3/AP_NavEKF3_core.h:598-606`. -/
structure imu_elements where
  /-- `Vector3F delAng` of `NavEKF3_core::imu_elements` (`AP_NavEKF3/AP_NavEKF3_core.h:599`). -/
  delAng : Vector3p.State := {}
  /-- `Vector3F delVel` of `NavEKF3_core::imu_elements` (`AP_NavEKF3/AP_NavEKF3_core.h:600`). -/
  delVel : Vector3p.State := {}
  /-- `ftype delAngDT` of `NavEKF3_core::imu_elements` (`AP_NavEKF3/AP_NavEKF3_core.h:601`). -/
  delAngDT : Binary64 := (Binary64.ofBits 0x0000000000000000 /- 0.0 -/)
  /-- `ftype delVelDT` of `NavEKF3_core::imu_elements` (`AP_NavEKF3/AP_NavEKF3_core.h:602`). -/
  delVelDT : Binary64 := (Binary64.ofBits 0x0000000000000000 /- 0.0 -/)
  /-- `uint32_t time_ms` of `NavEKF3_core::imu_elements` (`AP_NavEKF3/AP_NavEKF3_core.h:603`). -/
  time_ms : UInt32 := (0 : UInt32)
  /-- `uint8_t gyro_index` of `NavEKF3_core::imu_elements` (`AP_NavEKF3/AP_NavEKF3_core.h:604`). -/
  gyro_index : UInt8 := (0 : UInt8)
  /-- `uint8_t accel_index` of `NavEKF3_core::imu_elements` (`AP_NavEKF3/AP_NavEKF3_core.h:605`). -/
  accel_index : UInt8 := (0 : UInt8)
deriving Inhabited

end NavEKF3_core

namespace NavEKF3_core

/-- C++ `struct NavEKF3_core::output_elements`, `AP_NavEKF3/AP_NavEKF3_core.h:592-596`. -/
structure output_elements where
  /-- `QuaternionF quat` of `NavEKF3_core::output_elements` (`AP_NavEKF3/AP_NavEKF3_core.h:593`). -/
  quat : QuaternionT_double.State := QuaternionT_double.init_void
  /-- `Vector3F velocity` of `NavEKF3_core::output_elements` (`AP_NavEKF3/AP_NavEKF3_core.h:594`). -/
  velocity : Vector3p.State := {}
  /-- `Vector3F position` of `NavEKF3_core::output_elements` (`AP_NavEKF3/AP_NavEKF3_core.h:595`). -/
  position : Vector3p.State := {}
deriving Inhabited

end NavEKF3_core

namespace NavEKF3_core

/-- C++ `enum class NavEKF3_core::MagCal`, `AP_NavEKF3/AP_NavEKF3_core.h:430-439`. -/
inductive MagCal where
  | WHEN_FLYING
  | WHEN_MANOEUVRING
  | NEVER
  | AFTER_FIRST_CLIMB
  | ALWAYS
  | GROUND_AND_INFLIGHT
deriving DecidableEq, Inhabited

/-- The value of each enumerator of `NavEKF3_core::MagCal` (underlying type `int32_t`). -/
def MagCal.toInt : MagCal → Int32
  | .WHEN_FLYING => (0 : Int32)
  | .WHEN_MANOEUVRING => (1 : Int32)
  | .NEVER => (2 : Int32)
  | .AFTER_FIRST_CLIMB => (3 : Int32)
  | .ALWAYS => (4 : Int32)
  | .GROUND_AND_INFLIGHT => (7 : Int32)

/-- The enumerator of `NavEKF3_core::MagCal` with value `v` (the C++ converts only enumerator values; any other
value gives the first enumerator, the `Inhabited` default). -/
def MagCal.ofInt (v : Int32) : MagCal :=
  if v == (0 : Int32) then .WHEN_FLYING
  else if v == (1 : Int32) then .WHEN_MANOEUVRING
  else if v == (2 : Int32) then .NEVER
  else if v == (3 : Int32) then .AFTER_FIRST_CLIMB
  else if v == (4 : Int32) then .ALWAYS
  else if v == (7 : Int32) then .GROUND_AND_INFLIGHT
  else default

/-- C++ `enum class NavEKF3_core::MagFuseSel`, `AP_NavEKF3/AP_NavEKF3_core.h:442-447`. -/
inductive MagFuseSel where
  | NOT_FUSING
  | FUSE_YAW
  | FUSE_MAG
  | FUSE_MAG_ANCHORED
deriving DecidableEq, Inhabited

/-- The value of each enumerator of `NavEKF3_core::MagFuseSel` (underlying type `int32_t`). -/
def MagFuseSel.toInt : MagFuseSel → Int32
  | .NOT_FUSING => (0 : Int32)
  | .FUSE_YAW => (1 : Int32)
  | .FUSE_MAG => (2 : Int32)
  | .FUSE_MAG_ANCHORED => (3 : Int32)

/-- C++ `struct NavEKF3_core::range_elements`, `AP_NavEKF3/AP_NavEKF3_core.h:625-628`. -/
structure range_elements where
  /-- `uint32_t time_ms` of `EKF_obs_element_t` (`AP_NavEKF/EKF_Buffer.h:11`). -/
  time_ms : UInt32 := (0 : UInt32)
  /-- `ftype rng` of `NavEKF3_core::range_elements` (`AP_NavEKF3/AP_NavEKF3_core.h:626`). -/
  rng : Binary64 := (Binary64.ofBits 0x0000000000000000 /- 0.0 -/)
  /-- `uint8_t sensor_idx` of `NavEKF3_core::range_elements` (`AP_NavEKF3/AP_NavEKF3_core.h:627`). -/
  sensor_idx : UInt8 := (0 : UInt8)
deriving Inhabited

/-- C++ `enum class NavEKF3_core::rotationOrder`, `AP_NavEKF3/AP_NavEKF3_core.h:666-669`. -/
inductive rotationOrder where
  | TAIT_BRYAN_321
  | TAIT_BRYAN_312
deriving DecidableEq, Inhabited

/-- The value of each enumerator of `NavEKF3_core::rotationOrder` (underlying type `int32_t`). -/
def rotationOrder.toInt : rotationOrder → Int32
  | .TAIT_BRYAN_321 => (0 : Int32)
  | .TAIT_BRYAN_312 => (1 : Int32)

/-- C++ `struct NavEKF3_core::yaw_elements`, `AP_NavEKF3/AP_NavEKF3_core.h:671-679`. -/
structure yaw_elements where
  /-- `uint32_t time_ms` of `EKF_obs_element_t` (`AP_NavEKF/EKF_Buffer.h:11`). -/
  time_ms : UInt32 := (0 : UInt32)
  /-- `ftype yawAng` of `NavEKF3_core::yaw_elements` (`AP_NavEKF3/AP_NavEKF3_core.h:672`). -/
  yawAng : Binary64 := (Binary64.ofBits 0x0000000000000000 /- 0.0 -/)
  /-- `ftype yawAngErr` of `NavEKF3_core::yaw_elements` (`AP_NavEKF3/AP_NavEKF3_core.h:673`). -/
  yawAngErr : Binary64 := (Binary64.ofBits 0x0000000000000000 /- 0.0 -/)
  /-- `rotationOrder order` of `NavEKF3_core::yaw_elements` (`AP_NavEKF3/AP_NavEKF3_core.h:674`). -/
  order : NavEKF3_core.rotationOrder := NavEKF3_core.rotationOrder.TAIT_BRYAN_321
deriving Inhabited

/-- C++ `struct NavEKF3_core::(unnamed struct at AP_NavEKF3/AP_NavEKF3_core.h:700:5)`, `AP_NavEKF3/AP_NavEKF3_core.h:700-703`. -/
structure inactiveBias_t where
  /-- `Vector3F gyro_bias` of `NavEKF3_core::(unnamed struct at AP_NavEKF3/AP_NavEKF3_core.h:700:5)` (`AP_NavEKF3/AP_NavEKF3_core.h:701`). -/
  gyro_bias : Vector3p.State := {}
  /-- `Vector3F accel_bias` of `NavEKF3_core::(unnamed struct at AP_NavEKF3/AP_NavEKF3_core.h:700:5)` (`AP_NavEKF3/AP_NavEKF3_core.h:702`). -/
  accel_bias : Vector3p.State := {}
deriving Inhabited

/-- C++ `struct NavEKF3_core::tas_elements`, `AP_NavEKF3/AP_NavEKF3_core.h:637-641`. -/
structure tas_elements where
  /-- `uint32_t time_ms` of `EKF_obs_element_t` (`AP_NavEKF/EKF_Buffer.h:11`). -/
  time_ms : UInt32 := (0 : UInt32)
  /-- `ftype tas` of `NavEKF3_core::tas_elements` (`AP_NavEKF3/AP_NavEKF3_core.h:638`). -/
  tas : Binary64 := (Binary64.ofBits 0x0000000000000000 /- 0.0 -/)
  /-- `ftype tasVariance` of `NavEKF3_core::tas_elements` (`AP_NavEKF3/AP_NavEKF3_core.h:639`). -/
  tasVariance : Binary64 := (Binary64.ofBits 0x0000000000000000 /- 0.0 -/)
  /-- `bool allowFusion` of `NavEKF3_core::tas_elements` (`AP_NavEKF3/AP_NavEKF3_core.h:640`). -/
  allowFusion : Bool := false
deriving Inhabited

end NavEKF3_core

namespace NavEKF3_core

/-- C++ `struct NavEKF3_core::(unnamed struct at AP_NavEKF3/AP_NavEKF3_core.h:1291:5)`, `AP_NavEKF3/AP_NavEKF3_core.h:1291-1295`. -/
structure vertCompFiltState_t where
  /-- `ftype pos` of `NavEKF3_core::(unnamed struct at AP_NavEKF3/AP_NavEKF3_core.h:1291:5)` (`AP_NavEKF3/AP_NavEKF3_core.h:1292`). -/
  pos : Binary64 := (Binary64.ofBits 0x0000000000000000 /- 0.0 -/)
  /-- `ftype vel` of `NavEKF3_core::(unnamed struct at AP_NavEKF3/AP_NavEKF3_core.h:1291:5)` (`AP_NavEKF3/AP_NavEKF3_core.h:1293`). -/
  vel : Binary64 := (Binary64.ofBits 0x0000000000000000 /- 0.0 -/)
  /-- `ftype acc` of `NavEKF3_core::(unnamed struct at AP_NavEKF3/AP_NavEKF3_core.h:1291:5)` (`AP_NavEKF3/AP_NavEKF3_core.h:1294`). -/
  acc : Binary64 := (Binary64.ofBits 0x0000000000000000 /- 0.0 -/)
deriving Inhabited

/-- C++ `struct NavEKF3_core::(unnamed struct at AP_NavEKF3/AP_NavEKF3_core.h:1357:5)`, `AP_NavEKF3/AP_NavEKF3_core.h:1357-1362`. -/
structure flowCalSample_t where
  /-- `uint32_t timestamp_ms` of `NavEKF3_core::(unnamed struct at AP_NavEKF3/AP_NavEKF3_core.h:1357:5)` (`AP_NavEKF3/AP_NavEKF3_core.h:1358`). -/
  timestamp_ms : UInt32 := (0 : UInt32)
  /-- `Vector2f flowRate` of `NavEKF3_core::(unnamed struct at AP_NavEKF3/AP_NavEKF3_core.h:1357:5)` (`AP_NavEKF3/AP_NavEKF3_core.h:1359`). -/
  flowRate : Vector2f.State := {}
  /-- `Vector2f bodyRate` of `NavEKF3_core::(unnamed struct at AP_NavEKF3/AP_NavEKF3_core.h:1357:5)` (`AP_NavEKF3/AP_NavEKF3_core.h:1360`). -/
  bodyRate : Vector2f.State := {}
  /-- `Vector2f losPred` of `NavEKF3_core::(unnamed struct at AP_NavEKF3/AP_NavEKF3_core.h:1357:5)` (`AP_NavEKF3/AP_NavEKF3_core.h:1361`). -/
  losPred : Vector2f.State := {}
deriving Inhabited

/-- C++ `enum NavEKF3_core::AidingMode`, `AP_NavEKF3/AP_NavEKF3_core.h:1383-1387`. -/
inductive AidingMode where
  | AID_ABSOLUTE
  | AID_NONE
  | AID_RELATIVE
deriving DecidableEq, Inhabited

/-- The value of each enumerator of `NavEKF3_core::AidingMode` (underlying type `uint32_t`). -/
def AidingMode.toInt : AidingMode → UInt32
  | .AID_ABSOLUTE => (0 : UInt32)
  | .AID_NONE => (1 : UInt32)
  | .AID_RELATIVE => (2 : UInt32)

/-- C++ `struct NavEKF3_core::vel_odm_elements`, `AP_NavEKF3/AP_NavEKF3_core.h:651-656`. -/
structure vel_odm_elements where
  /-- `uint32_t time_ms` of `EKF_obs_element_t` (`AP_NavEKF/EKF_Buffer.h:11`). -/
  time_ms : UInt32 := (0 : UInt32)
  /-- `Vector3F vel` of `NavEKF3_core::vel_odm_elements` (`AP_NavEKF3/AP_NavEKF3_core.h:652`). -/
  vel : Vector3p.State := {}
  /-- `ftype velErr` of `NavEKF3_core::vel_odm_elements` (`AP_NavEKF3/AP_NavEKF3_core.h:653`). -/
  velErr : Binary64 := (Binary64.ofBits 0x0000000000000000 /- 0.0 -/)
  /-- `Vector3F body_offset` of `NavEKF3_core::vel_odm_elements` (`AP_NavEKF3/AP_NavEKF3_core.h:654`). -/
  body_offset : Vector3p.State := {}
  /-- `Vector3F angRate` of `NavEKF3_core::vel_odm_elements` (`AP_NavEKF3/AP_NavEKF3_core.h:655`). -/
  angRate : Vector3p.State := {}
deriving Inhabited

end NavEKF3_core

namespace NavEKF3_core

/-- C++ `struct NavEKF3_core::wheel_odm_elements`, `AP_NavEKF3/AP_NavEKF3_core.h:658-663`. -/
structure wheel_odm_elements where
  /-- `uint32_t time_ms` of `EKF_obs_element_t` (`AP_NavEKF/EKF_Buffer.h:11`). -/
  time_ms : UInt32 := (0 : UInt32)
  /-- `ftype delAng` of `NavEKF3_core::wheel_odm_elements` (`AP_NavEKF3/AP_NavEKF3_core.h:659`). -/
  delAng : Binary64 := (Binary64.ofBits 0x0000000000000000 /- 0.0 -/)
  /-- `ftype radius` of `NavEKF3_core::wheel_odm_elements` (`AP_NavEKF3/AP_NavEKF3_core.h:660`). -/
  radius : Binary64 := (Binary64.ofBits 0x0000000000000000 /- 0.0 -/)
  /-- `Vector3F hub_offset` of `NavEKF3_core::wheel_odm_elements` (`AP_NavEKF3/AP_NavEKF3_core.h:661`). -/
  hub_offset : Vector3p.State := {}
  /-- `ftype delTime` of `NavEKF3_core::wheel_odm_elements` (`AP_NavEKF3/AP_NavEKF3_core.h:662`). -/
  delTime : Binary64 := (Binary64.ofBits 0x0000000000000000 /- 0.0 -/)
deriving Inhabited

end NavEKF3_core

namespace NavEKF3

/-- C++ `void NavEKF3::set_enable(bool enable)`, `AP_NavEKF3/AP_NavEKF3.h:323`. -/
def set_enable (s : State) (enable : Bool) : State := Id.run do
  let mut s := s
  s := { s with _enable := AP_ParamT_signed_char_1.set_enable s._enable (if enable then (1 : Int8) else (0 : Int8)) }
  return s

end NavEKF3

namespace NavEKF3

/-- C++ `void NavEKF3::resetCoreErrors()`, `AP_NavEKF3/AP_NavEKF3.cpp:1149-1154`. -/
def resetCoreErrors (s : State) : State := Id.run do
  let mut s := s
  let t'1 : UInt8 := Int8.toUInt8 (Int32.toInt8 (0 : Int32))
  let t'2 : Int32 := UInt32.toInt32 (UInt8.toUInt32 s.num_cores)
  for i' in [0:(t'2.toInt - (Int.ofNat t'1.toNat)).toNat] do  -- C++ loop bounded by a runtime value (--runtime-loops)
    let i : UInt8 := t'1 + Nat.toUInt8 i'
    s := { s with coreRelativeErrors := s.coreRelativeErrors.set! (UInt8.toNat i) (Binary32.ofBits 0x00000000 /- 0 -/) }
  return s

end NavEKF3

namespace NavEKF3_core

/-- C++ `enum NavEKF3_core::ekf_affinity`, `AP_NavEKF3/AP_NavEKF3_core.h:1700-1705`. -/
inductive ekf_affinity where
  | EKF_AFFINITY_GPS
  | EKF_AFFINITY_BARO
  | EKF_AFFINITY_MAG
  | EKF_AFFINITY_ARSP
deriving DecidableEq, Inhabited

/-- The value of each enumerator of `NavEKF3_core::ekf_affinity` (underlying type `uint32_t`). -/
def ekf_affinity.toInt : ekf_affinity → UInt32
  | .EKF_AFFINITY_GPS => (1 : UInt32)
  | .EKF_AFFINITY_BARO => (2 : UInt32)
  | .EKF_AFFINITY_MAG => (4 : UInt32)
  | .EKF_AFFINITY_ARSP => (8 : UInt32)

end NavEKF3_core

namespace NavEKF3

/-- C++ `enum class NavEKF3::Option`, `AP_NavEKF3/AP_NavEKF3.h:472-477`. -/
inductive Option where
  | JammingExpected
  | ManualLaneSwitch
  | OptflowMayUseTerrainAlt
  | AglKfForOptflow
deriving DecidableEq, Inhabited

/-- The value of each enumerator of `NavEKF3::Option` (underlying type `int32_t`). -/
def Option.toInt : Option → Int32
  | .JammingExpected => (1 : Int32)
  | .ManualLaneSwitch => (2 : Int32)
  | .OptflowMayUseTerrainAlt => (4 : Int32)
  | .AglKfForOptflow => (8 : Int32)

/-- C++ `bool NavEKF3::option_is_enabled(Option option) const`, `AP_NavEKF3/AP_NavEKF3.h:478-480`. -/
def option_is_enabled (s : State) (option : NavEKF3.Option) : Bool := Id.run do
  return (AP_ParamT_unsigned_int_3.op_to_unsigned_int s._options &&& Int32.toUInt32 (NavEKF3.Option.toInt option)) != Int32.toUInt32 (0 : Int32)

end NavEKF3

namespace NavEKF3_core

/-- C++ `bool NavEKF3_core::using_extnav_for_yaw() const`, `AP_NavEKF3/AP_NavEKF3_Control.cpp:679-687`. -/
def using_extnav_for_yaw : Bool := Id.run do
  return false

end NavEKF3_core

namespace NavEKF3

/-- C++ `uint8_t NavEKF3::get_active_source_set() const`, `AP_NavEKF3/AP_NavEKF3.cpp:1327-1330`. -/
def get_active_source_set (s : State) : UInt8 := Id.run do
  return AP_NavEKF_Source.get_active_source_set s.sources

end NavEKF3

namespace NavEKF3_core

/-! Not emitted, since they have no effect in the model (they write neither the state, the
parameters nor a reference parameter; e.g. they only save parameters):
- C++ `void NavEKF3_core::SampleDragData(const imu_elements & imu)`, `AP_NavEKF3/AP_NavEKF3_Measurements.cpp:1494-1540`.
- C++ `void NavEKF3_core::verifyTiltErrorVariance()`, `AP_NavEKF3/AP_NavEKF3_core.cpp:2190-2233`.
-/

/-- C++ `struct NavEKF3_core::state_elements`, `AP_NavEKF3/AP_NavEKF3_core.h:576-585`. -/
structure state_elements where
  /-- `QuaternionF quat` of `NavEKF3_core::state_elements` (`AP_NavEKF3/AP_NavEKF3_core.h:577`). -/
  quat : QuaternionT_double.State := QuaternionT_double.init_void
  /-- `Vector3F velocity` of `NavEKF3_core::state_elements` (`AP_NavEKF3/AP_NavEKF3_core.h:578`). -/
  velocity : Vector3p.State := {}
  /-- `Vector3F position` of `NavEKF3_core::state_elements` (`AP_NavEKF3/AP_NavEKF3_core.h:579`). -/
  position : Vector3p.State := {}
  /-- `Vector3F gyro_bias` of `NavEKF3_core::state_elements` (`AP_NavEKF3/AP_NavEKF3_core.h:580`). -/
  gyro_bias : Vector3p.State := {}
  /-- `Vector3F accel_bias` of `NavEKF3_core::state_elements` (`AP_NavEKF3/AP_NavEKF3_core.h:581`). -/
  accel_bias : Vector3p.State := {}
  /-- `Vector3F earth_magfield` of `NavEKF3_core::state_elements` (`AP_NavEKF3/AP_NavEKF3_core.h:582`). -/
  earth_magfield : Vector3p.State := {}
  /-- `Vector3F body_magfield` of `NavEKF3_core::state_elements` (`AP_NavEKF3/AP_NavEKF3_core.h:583`). -/
  body_magfield : Vector3p.State := {}
  /-- `Vector2F wind_vel` of `NavEKF3_core::state_elements` (`AP_NavEKF3/AP_NavEKF3_core.h:584`). -/
  wind_vel : Vector2p.State := {}
deriving Inhabited

/-- C++ `struct NavEKF3_core::rng_bcn_elements`, `AP_NavEKF3/AP_NavEKF3_core.h:630-635`. -/
structure rng_bcn_elements where
  /-- `uint32_t time_ms` of `EKF_obs_element_t` (`AP_NavEKF/EKF_Buffer.h:11`). -/
  time_ms : UInt32 := (0 : UInt32)
  /-- `ftype rng` of `NavEKF3_core::rng_bcn_elements` (`AP_NavEKF3/AP_NavEKF3_core.h:631`). -/
  rng : Binary64 := (Binary64.ofBits 0x0000000000000000 /- 0.0 -/)
  /-- `Vector3F beacon_posNED` of `NavEKF3_core::rng_bcn_elements` (`AP_NavEKF3/AP_NavEKF3_core.h:632`). -/
  beacon_posNED : Vector3p.State := {}
  /-- `ftype rngErr` of `NavEKF3_core::rng_bcn_elements` (`AP_NavEKF3/AP_NavEKF3_core.h:633`). -/
  rngErr : Binary64 := (Binary64.ofBits 0x0000000000000000 /- 0.0 -/)
  /-- `uint8_t beacon_ID` of `NavEKF3_core::rng_bcn_elements` (`AP_NavEKF3/AP_NavEKF3_core.h:634`). -/
  beacon_ID : UInt8 := (0 : UInt8)
deriving Inhabited

/-- C++ `struct NavEKF3_core::ext_nav_elements`, `AP_NavEKF3/AP_NavEKF3_core.h:681-686`. -/
structure ext_nav_elements where
  /-- `uint32_t time_ms` of `EKF_obs_element_t` (`AP_NavEKF/EKF_Buffer.h:11`). -/
  time_ms : UInt32 := (0 : UInt32)
  /-- `Vector3F pos` of `NavEKF3_core::ext_nav_elements` (`AP_NavEKF3/AP_NavEKF3_core.h:682`). -/
  pos : Vector3p.State := {}
  /-- `ftype posErr` of `NavEKF3_core::ext_nav_elements` (`AP_NavEKF3/AP_NavEKF3_core.h:683`). -/
  posErr : Binary64 := (Binary64.ofBits 0x0000000000000000 /- 0.0 -/)
  /-- `bool posReset` of `NavEKF3_core::ext_nav_elements` (`AP_NavEKF3/AP_NavEKF3_core.h:684`). -/
  posReset : Bool := false
  /-- `bool corrected` of `NavEKF3_core::ext_nav_elements` (`AP_NavEKF3/AP_NavEKF3_core.h:685`). -/
  corrected : Bool := false
deriving Inhabited

/-- C++ `struct NavEKF3_core::ext_nav_vel_elements`, `AP_NavEKF3/AP_NavEKF3_core.h:688-692`. -/
structure ext_nav_vel_elements where
  /-- `uint32_t time_ms` of `EKF_obs_element_t` (`AP_NavEKF/EKF_Buffer.h:11`). -/
  time_ms : UInt32 := (0 : UInt32)
  /-- `Vector3F vel` of `NavEKF3_core::ext_nav_vel_elements` (`AP_NavEKF3/AP_NavEKF3_core.h:689`). -/
  vel : Vector3p.State := {}
  /-- `ftype err` of `NavEKF3_core::ext_nav_vel_elements` (`AP_NavEKF3/AP_NavEKF3_core.h:690`). -/
  err : Binary64 := (Binary64.ofBits 0x0000000000000000 /- 0.0 -/)
  /-- `bool corrected` of `NavEKF3_core::ext_nav_vel_elements` (`AP_NavEKF3/AP_NavEKF3_core.h:691`). -/
  corrected : Bool := false
deriving Inhabited

/-- C++ `struct NavEKF3_core::drag_elements`, `AP_NavEKF3/AP_NavEKF3_core.h:694-696`. -/
structure drag_elements where
  /-- `uint32_t time_ms` of `EKF_obs_element_t` (`AP_NavEKF/EKF_Buffer.h:11`). -/
  time_ms : UInt32 := (0 : UInt32)
  /-- `Vector2f accelXY` of `NavEKF3_core::drag_elements` (`AP_NavEKF3/AP_NavEKF3_core.h:695`). -/
  accelXY : Vector2f.State := {}
deriving Inhabited

end NavEKF3_core

/-- C++ `struct log_XKF0`, `AP_NavEKF3/LogStructure.h:42-59`. -/
structure log_XKF0 where
  /-- `uint8_t head1` of `log_XKF0` (`AP_NavEKF3/LogStructure.h:43`). -/
  head1 : UInt8 := (0 : UInt8)
  /-- `uint8_t head2` of `log_XKF0` (`AP_NavEKF3/LogStructure.h:43`). -/
  head2 : UInt8 := (0 : UInt8)
  /-- `uint8_t msgid` of `log_XKF0` (`AP_NavEKF3/LogStructure.h:43`). -/
  msgid : UInt8 := (0 : UInt8)
  /-- `uint64_t time_us` of `log_XKF0` (`AP_NavEKF3/LogStructure.h:44`). -/
  time_us : UInt64 := (0 : UInt64)
  /-- `uint8_t core` of `log_XKF0` (`AP_NavEKF3/LogStructure.h:45`). -/
  core : UInt8 := (0 : UInt8)
  /-- `uint8_t ID` of `log_XKF0` (`AP_NavEKF3/LogStructure.h:46`). -/
  ID : UInt8 := (0 : UInt8)
  /-- `int16_t rng` of `log_XKF0` (`AP_NavEKF3/LogStructure.h:47`). -/
  rng : Int16 := (0 : Int16)
  /-- `int16_t innov` of `log_XKF0` (`AP_NavEKF3/LogStructure.h:48`). -/
  innov : Int16 := (0 : Int16)
  /-- `uint16_t sqrtInnovVar` of `log_XKF0` (`AP_NavEKF3/LogStructure.h:49`). -/
  sqrtInnovVar : UInt16 := (0 : UInt16)
  /-- `uint16_t testRatio` of `log_XKF0` (`AP_NavEKF3/LogStructure.h:50`). -/
  testRatio : UInt16 := (0 : UInt16)
  /-- `int16_t beaconPosN` of `log_XKF0` (`AP_NavEKF3/LogStructure.h:51`). -/
  beaconPosN : Int16 := (0 : Int16)
  /-- `int16_t beaconPosE` of `log_XKF0` (`AP_NavEKF3/LogStructure.h:52`). -/
  beaconPosE : Int16 := (0 : Int16)
  /-- `int16_t beaconPosD` of `log_XKF0` (`AP_NavEKF3/LogStructure.h:53`). -/
  beaconPosD : Int16 := (0 : Int16)
  /-- `int16_t offsetHigh` of `log_XKF0` (`AP_NavEKF3/LogStructure.h:54`). -/
  offsetHigh : Int16 := (0 : Int16)
  /-- `int16_t offsetLow` of `log_XKF0` (`AP_NavEKF3/LogStructure.h:55`). -/
  offsetLow : Int16 := (0 : Int16)
  /-- `int16_t posN` of `log_XKF0` (`AP_NavEKF3/LogStructure.h:56`). -/
  posN : Int16 := (0 : Int16)
  /-- `int16_t posE` of `log_XKF0` (`AP_NavEKF3/LogStructure.h:57`). -/
  posE : Int16 := (0 : Int16)
  /-- `int16_t posD` of `log_XKF0` (`AP_NavEKF3/LogStructure.h:58`). -/
  posD : Int16 := (0 : Int16)
deriving Inhabited

/-- C++ `struct log_XKF1`, `AP_NavEKF3/LogStructure.h:80-98`. -/
structure log_XKF1 where
  /-- `uint8_t head1` of `log_XKF1` (`AP_NavEKF3/LogStructure.h:81`). -/
  head1 : UInt8 := (0 : UInt8)
  /-- `uint8_t head2` of `log_XKF1` (`AP_NavEKF3/LogStructure.h:81`). -/
  head2 : UInt8 := (0 : UInt8)
  /-- `uint8_t msgid` of `log_XKF1` (`AP_NavEKF3/LogStructure.h:81`). -/
  msgid : UInt8 := (0 : UInt8)
  /-- `uint64_t time_us` of `log_XKF1` (`AP_NavEKF3/LogStructure.h:82`). -/
  time_us : UInt64 := (0 : UInt64)
  /-- `uint8_t core` of `log_XKF1` (`AP_NavEKF3/LogStructure.h:83`). -/
  core : UInt8 := (0 : UInt8)
  /-- `int16_t roll` of `log_XKF1` (`AP_NavEKF3/LogStructure.h:84`). -/
  roll : Int16 := (0 : Int16)
  /-- `int16_t pitch` of `log_XKF1` (`AP_NavEKF3/LogStructure.h:85`). -/
  pitch : Int16 := (0 : Int16)
  /-- `uint16_t yaw` of `log_XKF1` (`AP_NavEKF3/LogStructure.h:86`). -/
  yaw : UInt16 := (0 : UInt16)
  /-- `float velN` of `log_XKF1` (`AP_NavEKF3/LogStructure.h:87`). -/
  velN : Binary32 := (Binary32.ofBits 0x00000000 /- 0.0 -/)
  /-- `float velE` of `log_XKF1` (`AP_NavEKF3/LogStructure.h:88`). -/
  velE : Binary32 := (Binary32.ofBits 0x00000000 /- 0.0 -/)
  /-- `float velD` of `log_XKF1` (`AP_NavEKF3/LogStructure.h:89`). -/
  velD : Binary32 := (Binary32.ofBits 0x00000000 /- 0.0 -/)
  /-- `float posD_dot` of `log_XKF1` (`AP_NavEKF3/LogStructure.h:90`). -/
  posD_dot : Binary32 := (Binary32.ofBits 0x00000000 /- 0.0 -/)
  /-- `float posN` of `log_XKF1` (`AP_NavEKF3/LogStructure.h:91`). -/
  posN : Binary32 := (Binary32.ofBits 0x00000000 /- 0.0 -/)
  /-- `float posE` of `log_XKF1` (`AP_NavEKF3/LogStructure.h:92`). -/
  posE : Binary32 := (Binary32.ofBits 0x00000000 /- 0.0 -/)
  /-- `float posD` of `log_XKF1` (`AP_NavEKF3/LogStructure.h:93`). -/
  posD : Binary32 := (Binary32.ofBits 0x00000000 /- 0.0 -/)
  /-- `int16_t gyrX` of `log_XKF1` (`AP_NavEKF3/LogStructure.h:94`). -/
  gyrX : Int16 := (0 : Int16)
  /-- `int16_t gyrY` of `log_XKF1` (`AP_NavEKF3/LogStructure.h:95`). -/
  gyrY : Int16 := (0 : Int16)
  /-- `int16_t gyrZ` of `log_XKF1` (`AP_NavEKF3/LogStructure.h:96`). -/
  gyrZ : Int16 := (0 : Int16)
  /-- `int32_t originHgt` of `log_XKF1` (`AP_NavEKF3/LogStructure.h:97`). -/
  originHgt : Int32 := (0 : Int32)
deriving Inhabited

/-- C++ `struct log_XKF2`, `AP_NavEKF3/LogStructure.h:119-137`. -/
structure log_XKF2 where
  /-- `uint8_t head1` of `log_XKF2` (`AP_NavEKF3/LogStructure.h:120`). -/
  head1 : UInt8 := (0 : UInt8)
  /-- `uint8_t head2` of `log_XKF2` (`AP_NavEKF3/LogStructure.h:120`). -/
  head2 : UInt8 := (0 : UInt8)
  /-- `uint8_t msgid` of `log_XKF2` (`AP_NavEKF3/LogStructure.h:120`). -/
  msgid : UInt8 := (0 : UInt8)
  /-- `uint64_t time_us` of `log_XKF2` (`AP_NavEKF3/LogStructure.h:121`). -/
  time_us : UInt64 := (0 : UInt64)
  /-- `uint8_t core` of `log_XKF2` (`AP_NavEKF3/LogStructure.h:122`). -/
  core : UInt8 := (0 : UInt8)
  /-- `int16_t accBiasX` of `log_XKF2` (`AP_NavEKF3/LogStructure.h:123`). -/
  accBiasX : Int16 := (0 : Int16)
  /-- `int16_t accBiasY` of `log_XKF2` (`AP_NavEKF3/LogStructure.h:124`). -/
  accBiasY : Int16 := (0 : Int16)
  /-- `int16_t accBiasZ` of `log_XKF2` (`AP_NavEKF3/LogStructure.h:125`). -/
  accBiasZ : Int16 := (0 : Int16)
  /-- `int16_t windN` of `log_XKF2` (`AP_NavEKF3/LogStructure.h:126`). -/
  windN : Int16 := (0 : Int16)
  /-- `int16_t windE` of `log_XKF2` (`AP_NavEKF3/LogStructure.h:127`). -/
  windE : Int16 := (0 : Int16)
  /-- `int16_t magN` of `log_XKF2` (`AP_NavEKF3/LogStructure.h:128`). -/
  magN : Int16 := (0 : Int16)
  /-- `int16_t magE` of `log_XKF2` (`AP_NavEKF3/LogStructure.h:129`). -/
  magE : Int16 := (0 : Int16)
  /-- `int16_t magD` of `log_XKF2` (`AP_NavEKF3/LogStructure.h:130`). -/
  magD : Int16 := (0 : Int16)
  /-- `int16_t magX` of `log_XKF2` (`AP_NavEKF3/LogStructure.h:131`). -/
  magX : Int16 := (0 : Int16)
  /-- `int16_t magY` of `log_XKF2` (`AP_NavEKF3/LogStructure.h:132`). -/
  magY : Int16 := (0 : Int16)
  /-- `int16_t magZ` of `log_XKF2` (`AP_NavEKF3/LogStructure.h:133`). -/
  magZ : Int16 := (0 : Int16)
  /-- `float innovDragX` of `log_XKF2` (`AP_NavEKF3/LogStructure.h:134`). -/
  innovDragX : Binary32 := (Binary32.ofBits 0x00000000 /- 0.0 -/)
  /-- `float innovDragY` of `log_XKF2` (`AP_NavEKF3/LogStructure.h:135`). -/
  innovDragY : Binary32 := (Binary32.ofBits 0x00000000 /- 0.0 -/)
  /-- `float innovSideslip` of `log_XKF2` (`AP_NavEKF3/LogStructure.h:136`). -/
  innovSideslip : Binary32 := (Binary32.ofBits 0x00000000 /- 0.0 -/)
deriving Inhabited

/-- C++ `struct log_XKF3`, `AP_NavEKF3/LogStructure.h:157-174`. -/
structure log_XKF3 where
  /-- `uint8_t head1` of `log_XKF3` (`AP_NavEKF3/LogStructure.h:158`). -/
  head1 : UInt8 := (0 : UInt8)
  /-- `uint8_t head2` of `log_XKF3` (`AP_NavEKF3/LogStructure.h:158`). -/
  head2 : UInt8 := (0 : UInt8)
  /-- `uint8_t msgid` of `log_XKF3` (`AP_NavEKF3/LogStructure.h:158`). -/
  msgid : UInt8 := (0 : UInt8)
  /-- `uint64_t time_us` of `log_XKF3` (`AP_NavEKF3/LogStructure.h:159`). -/
  time_us : UInt64 := (0 : UInt64)
  /-- `uint8_t core` of `log_XKF3` (`AP_NavEKF3/LogStructure.h:160`). -/
  core : UInt8 := (0 : UInt8)
  /-- `int16_t innovVN` of `log_XKF3` (`AP_NavEKF3/LogStructure.h:161`). -/
  innovVN : Int16 := (0 : Int16)
  /-- `int16_t innovVE` of `log_XKF3` (`AP_NavEKF3/LogStructure.h:162`). -/
  innovVE : Int16 := (0 : Int16)
  /-- `int16_t innovVD` of `log_XKF3` (`AP_NavEKF3/LogStructure.h:163`). -/
  innovVD : Int16 := (0 : Int16)
  /-- `int16_t innovPN` of `log_XKF3` (`AP_NavEKF3/LogStructure.h:164`). -/
  innovPN : Int16 := (0 : Int16)
  /-- `int16_t innovPE` of `log_XKF3` (`AP_NavEKF3/LogStructure.h:165`). -/
  innovPE : Int16 := (0 : Int16)
  /-- `int16_t innovPD` of `log_XKF3` (`AP_NavEKF3/LogStructure.h:166`). -/
  innovPD : Int16 := (0 : Int16)
  /-- `int16_t innovMX` of `log_XKF3` (`AP_NavEKF3/LogStructure.h:167`). -/
  innovMX : Int16 := (0 : Int16)
  /-- `int16_t innovMY` of `log_XKF3` (`AP_NavEKF3/LogStructure.h:168`). -/
  innovMY : Int16 := (0 : Int16)
  /-- `int16_t innovMZ` of `log_XKF3` (`AP_NavEKF3/LogStructure.h:169`). -/
  innovMZ : Int16 := (0 : Int16)
  /-- `int16_t innovYaw` of `log_XKF3` (`AP_NavEKF3/LogStructure.h:170`). -/
  innovYaw : Int16 := (0 : Int16)
  /-- `int16_t innovVT` of `log_XKF3` (`AP_NavEKF3/LogStructure.h:171`). -/
  innovVT : Int16 := (0 : Int16)
  /-- `float rerr` of `log_XKF3` (`AP_NavEKF3/LogStructure.h:172`). -/
  rerr : Binary32 := (Binary32.ofBits 0x00000000 /- 0.0 -/)
  /-- `float errorScore` of `log_XKF3` (`AP_NavEKF3/LogStructure.h:173`). -/
  errorScore : Binary32 := (Binary32.ofBits 0x00000000 /- 0.0 -/)
deriving Inhabited

/-- C++ `struct log_XKF4`, `AP_NavEKF3/LogStructure.h:196-213`. -/
structure log_XKF4 where
  /-- `uint8_t head1` of `log_XKF4` (`AP_NavEKF3/LogStructure.h:197`). -/
  head1 : UInt8 := (0 : UInt8)
  /-- `uint8_t head2` of `log_XKF4` (`AP_NavEKF3/LogStructure.h:197`). -/
  head2 : UInt8 := (0 : UInt8)
  /-- `uint8_t msgid` of `log_XKF4` (`AP_NavEKF3/LogStructure.h:197`). -/
  msgid : UInt8 := (0 : UInt8)
  /-- `uint64_t time_us` of `log_XKF4` (`AP_NavEKF3/LogStructure.h:198`). -/
  time_us : UInt64 := (0 : UInt64)
  /-- `uint8_t core` of `log_XKF4` (`AP_NavEKF3/LogStructure.h:199`). -/
  core : UInt8 := (0 : UInt8)
  /-- `int16_t sqrtvarV` of `log_XKF4` (`AP_NavEKF3/LogStructure.h:200`). -/
  sqrtvarV : Int16 := (0 : Int16)
  /-- `int16_t sqrtvarP` of `log_XKF4` (`AP_NavEKF3/LogStructure.h:201`). -/
  sqrtvarP : Int16 := (0 : Int16)
  /-- `int16_t sqrtvarH` of `log_XKF4` (`AP_NavEKF3/LogStructure.h:202`). -/
  sqrtvarH : Int16 := (0 : Int16)
  /-- `int16_t sqrtvarM` of `log_XKF4` (`AP_NavEKF3/LogStructure.h:203`). -/
  sqrtvarM : Int16 := (0 : Int16)
  /-- `int16_t sqrtvarVT` of `log_XKF4` (`AP_NavEKF3/LogStructure.h:204`). -/
  sqrtvarVT : Int16 := (0 : Int16)
  /-- `float tiltErr` of `log_XKF4` (`AP_NavEKF3/LogStructure.h:205`). -/
  tiltErr : Binary32 := (Binary32.ofBits 0x00000000 /- 0.0 -/)
  /-- `float offsetNorth` of `log_XKF4` (`AP_NavEKF3/LogStructure.h:206`). -/
  offsetNorth : Binary32 := (Binary32.ofBits 0x00000000 /- 0.0 -/)
  /-- `float offsetEast` of `log_XKF4` (`AP_NavEKF3/LogStructure.h:207`). -/
  offsetEast : Binary32 := (Binary32.ofBits 0x00000000 /- 0.0 -/)
  /-- `uint16_t faults` of `log_XKF4` (`AP_NavEKF3/LogStructure.h:208`). -/
  faults : UInt16 := (0 : UInt16)
  /-- `uint8_t timeouts` of `log_XKF4` (`AP_NavEKF3/LogStructure.h:209`). -/
  timeouts : UInt8 := (0 : UInt8)
  /-- `uint32_t solution` of `log_XKF4` (`AP_NavEKF3/LogStructure.h:210`). -/
  solution : UInt32 := (0 : UInt32)
  /-- `uint16_t gps` of `log_XKF4` (`AP_NavEKF3/LogStructure.h:211`). -/
  gps : UInt16 := (0 : UInt16)
  /-- `int8_t primary` of `log_XKF4` (`AP_NavEKF3/LogStructure.h:212`). -/
  primary : Int8 := (0 : Int8)
deriving Inhabited

/-- C++ `struct log_XKF5`, `AP_NavEKF3/LogStructure.h:233-250`. -/
structure log_XKF5 where
  /-- `uint8_t head1` of `log_XKF5` (`AP_NavEKF3/LogStructure.h:234`). -/
  head1 : UInt8 := (0 : UInt8)
  /-- `uint8_t head2` of `log_XKF5` (`AP_NavEKF3/LogStructure.h:234`). -/
  head2 : UInt8 := (0 : UInt8)
  /-- `uint8_t msgid` of `log_XKF5` (`AP_NavEKF3/LogStructure.h:234`). -/
  msgid : UInt8 := (0 : UInt8)
  /-- `uint64_t time_us` of `log_XKF5` (`AP_NavEKF3/LogStructure.h:235`). -/
  time_us : UInt64 := (0 : UInt64)
  /-- `uint8_t core` of `log_XKF5` (`AP_NavEKF3/LogStructure.h:236`). -/
  core : UInt8 := (0 : UInt8)
  /-- `uint8_t normInnov` of `log_XKF5` (`AP_NavEKF3/LogStructure.h:237`). -/
  normInnov : UInt8 := (0 : UInt8)
  /-- `int16_t FIX` of `log_XKF5` (`AP_NavEKF3/LogStructure.h:238`). -/
  FIX : Int16 := (0 : Int16)
  /-- `int16_t FIY` of `log_XKF5` (`AP_NavEKF3/LogStructure.h:239`). -/
  FIY : Int16 := (0 : Int16)
  /-- `int16_t AFI` of `log_XKF5` (`AP_NavEKF3/LogStructure.h:240`). -/
  AFI : Int16 := (0 : Int16)
  /-- `int16_t HAGL` of `log_XKF5` (`AP_NavEKF3/LogStructure.h:241`). -/
  HAGL : Int16 := (0 : Int16)
  /-- `int16_t terrOffset` of `log_XKF5` (`AP_NavEKF3/LogStructure.h:242`). -/
  terrOffset : Int16 := (0 : Int16)
  /-- `int16_t RI` of `log_XKF5` (`AP_NavEKF3/LogStructure.h:243`). -/
  RI : Int16 := (0 : Int16)
  /-- `uint16_t meaRng` of `log_XKF5` (`AP_NavEKF3/LogStructure.h:244`). -/
  meaRng : UInt16 := (0 : UInt16)
  /-- `uint16_t errHAGL` of `log_XKF5` (`AP_NavEKF3/LogStructure.h:245`). -/
  errHAGL : UInt16 := (0 : UInt16)
  /-- `float angErr` of `log_XKF5` (`AP_NavEKF3/LogStructure.h:246`). -/
  angErr : Binary32 := (Binary32.ofBits 0x00000000 /- 0.0 -/)
  /-- `float velErr` of `log_XKF5` (`AP_NavEKF3/LogStructure.h:247`). -/
  velErr : Binary32 := (Binary32.ofBits 0x00000000 /- 0.0 -/)
  /-- `float posErr` of `log_XKF5` (`AP_NavEKF3/LogStructure.h:248`). -/
  posErr : Binary32 := (Binary32.ofBits 0x00000000 /- 0.0 -/)
  /-- `float baroOffset` of `log_XKF5` (`AP_NavEKF3/LogStructure.h:249`). -/
  baroOffset : Binary32 := (Binary32.ofBits 0x00000000 /- 0.0 -/)
deriving Inhabited

/-- C++ `struct log_XKFA`, `AP_NavEKF3/LogStructure.h:262-271`. -/
structure log_XKFA where
  /-- `uint8_t head1` of `log_XKFA` (`AP_NavEKF3/LogStructure.h:263`). -/
  head1 : UInt8 := (0 : UInt8)
  /-- `uint8_t head2` of `log_XKFA` (`AP_NavEKF3/LogStructure.h:263`). -/
  head2 : UInt8 := (0 : UInt8)
  /-- `uint8_t msgid` of `log_XKFA` (`AP_NavEKF3/LogStructure.h:263`). -/
  msgid : UInt8 := (0 : UInt8)
  /-- `uint64_t time_us` of `log_XKFA` (`AP_NavEKF3/LogStructure.h:264`). -/
  time_us : UInt64 := (0 : UInt64)
  /-- `uint8_t core` of `log_XKFA` (`AP_NavEKF3/LogStructure.h:265`). -/
  core : UInt8 := (0 : UInt8)
  /-- `float hAgl` of `log_XKFA` (`AP_NavEKF3/LogStructure.h:266`). -/
  hAgl : Binary32 := (Binary32.ofBits 0x00000000 /- 0.0 -/)
  /-- `float vAgl` of `log_XKFA` (`AP_NavEKF3/LogStructure.h:267`). -/
  vAgl : Binary32 := (Binary32.ofBits 0x00000000 /- 0.0 -/)
  /-- `float hAglStd` of `log_XKFA` (`AP_NavEKF3/LogStructure.h:268`). -/
  hAglStd : Binary32 := (Binary32.ofBits 0x00000000 /- 0.0 -/)
  /-- `float vAglStd` of `log_XKFA` (`AP_NavEKF3/LogStructure.h:269`). -/
  vAglStd : Binary32 := (Binary32.ofBits 0x00000000 /- 0.0 -/)
  /-- `uint8_t valid` of `log_XKFA` (`AP_NavEKF3/LogStructure.h:270`). -/
  valid : UInt8 := (0 : UInt8)
deriving Inhabited

/-- C++ `struct log_XKFD`, `AP_NavEKF3/LogStructure.h:283-293`. -/
structure log_XKFD where
  /-- `uint8_t head1` of `log_XKFD` (`AP_NavEKF3/LogStructure.h:284`). -/
  head1 : UInt8 := (0 : UInt8)
  /-- `uint8_t head2` of `log_XKFD` (`AP_NavEKF3/LogStructure.h:284`). -/
  head2 : UInt8 := (0 : UInt8)
  /-- `uint8_t msgid` of `log_XKFD` (`AP_NavEKF3/LogStructure.h:284`). -/
  msgid : UInt8 := (0 : UInt8)
  /-- `uint64_t time_us` of `log_XKFD` (`AP_NavEKF3/LogStructure.h:285`). -/
  time_us : UInt64 := (0 : UInt64)
  /-- `uint8_t core` of `log_XKFD` (`AP_NavEKF3/LogStructure.h:286`). -/
  core : UInt8 := (0 : UInt8)
  /-- `float velInnovX` of `log_XKFD` (`AP_NavEKF3/LogStructure.h:287`). -/
  velInnovX : Binary32 := (Binary32.ofBits 0x00000000 /- 0.0 -/)
  /-- `float velInnovY` of `log_XKFD` (`AP_NavEKF3/LogStructure.h:288`). -/
  velInnovY : Binary32 := (Binary32.ofBits 0x00000000 /- 0.0 -/)
  /-- `float velInnovZ` of `log_XKFD` (`AP_NavEKF3/LogStructure.h:289`). -/
  velInnovZ : Binary32 := (Binary32.ofBits 0x00000000 /- 0.0 -/)
  /-- `float velInnovVarX` of `log_XKFD` (`AP_NavEKF3/LogStructure.h:290`). -/
  velInnovVarX : Binary32 := (Binary32.ofBits 0x00000000 /- 0.0 -/)
  /-- `float velInnovVarY` of `log_XKFD` (`AP_NavEKF3/LogStructure.h:291`). -/
  velInnovVarY : Binary32 := (Binary32.ofBits 0x00000000 /- 0.0 -/)
  /-- `float velInnovVarZ` of `log_XKFD` (`AP_NavEKF3/LogStructure.h:292`). -/
  velInnovVarZ : Binary32 := (Binary32.ofBits 0x00000000 /- 0.0 -/)
deriving Inhabited

/-- C++ `struct log_XKT`, `AP_NavEKF3/LogStructure.h:308-321`. -/
structure log_XKT where
  /-- `uint8_t head1` of `log_XKT` (`AP_NavEKF3/LogStructure.h:309`). -/
  head1 : UInt8 := (0 : UInt8)
  /-- `uint8_t head2` of `log_XKT` (`AP_NavEKF3/LogStructure.h:309`). -/
  head2 : UInt8 := (0 : UInt8)
  /-- `uint8_t msgid` of `log_XKT` (`AP_NavEKF3/LogStructure.h:309`). -/
  msgid : UInt8 := (0 : UInt8)
  /-- `uint64_t time_us` of `log_XKT` (`AP_NavEKF3/LogStructure.h:310`). -/
  time_us : UInt64 := (0 : UInt64)
  /-- `uint8_t core` of `log_XKT` (`AP_NavEKF3/LogStructure.h:311`). -/
  core : UInt8 := (0 : UInt8)
  /-- `uint32_t timing_count` of `log_XKT` (`AP_NavEKF3/LogStructure.h:312`). -/
  timing_count : UInt32 := (0 : UInt32)
  /-- `float dtIMUavg_min` of `log_XKT` (`AP_NavEKF3/LogStructure.h:313`). -/
  dtIMUavg_min : Binary32 := (Binary32.ofBits 0x00000000 /- 0.0 -/)
  /-- `float dtIMUavg_max` of `log_XKT` (`AP_NavEKF3/LogStructure.h:314`). -/
  dtIMUavg_max : Binary32 := (Binary32.ofBits 0x00000000 /- 0.0 -/)
  /-- `float dtEKFavg_min` of `log_XKT` (`AP_NavEKF3/LogStructure.h:315`). -/
  dtEKFavg_min : Binary32 := (Binary32.ofBits 0x00000000 /- 0.0 -/)
  /-- `float dtEKFavg_max` of `log_XKT` (`AP_NavEKF3/LogStructure.h:316`). -/
  dtEKFavg_max : Binary32 := (Binary32.ofBits 0x00000000 /- 0.0 -/)
  /-- `float delAngDT_min` of `log_XKT` (`AP_NavEKF3/LogStructure.h:317`). -/
  delAngDT_min : Binary32 := (Binary32.ofBits 0x00000000 /- 0.0 -/)
  /-- `float delAngDT_max` of `log_XKT` (`AP_NavEKF3/LogStructure.h:318`). -/
  delAngDT_max : Binary32 := (Binary32.ofBits 0x00000000 /- 0.0 -/)
  /-- `float delVelDT_min` of `log_XKT` (`AP_NavEKF3/LogStructure.h:319`). -/
  delVelDT_min : Binary32 := (Binary32.ofBits 0x00000000 /- 0.0 -/)
  /-- `float delVelDT_max` of `log_XKT` (`AP_NavEKF3/LogStructure.h:320`). -/
  delVelDT_max : Binary32 := (Binary32.ofBits 0x00000000 /- 0.0 -/)
deriving Inhabited

/-- C++ `struct log_XKFM`, `AP_NavEKF3/LogStructure.h:333-342`. -/
structure log_XKFM where
  /-- `uint8_t head1` of `log_XKFM` (`AP_NavEKF3/LogStructure.h:334`). -/
  head1 : UInt8 := (0 : UInt8)
  /-- `uint8_t head2` of `log_XKFM` (`AP_NavEKF3/LogStructure.h:334`). -/
  head2 : UInt8 := (0 : UInt8)
  /-- `uint8_t msgid` of `log_XKFM` (`AP_NavEKF3/LogStructure.h:334`). -/
  msgid : UInt8 := (0 : UInt8)
  /-- `uint64_t time_us` of `log_XKFM` (`AP_NavEKF3/LogStructure.h:335`). -/
  time_us : UInt64 := (0 : UInt64)
  /-- `uint8_t core` of `log_XKFM` (`AP_NavEKF3/LogStructure.h:336`). -/
  core : UInt8 := (0 : UInt8)
  /-- `uint8_t ongroundnotmoving` of `log_XKFM` (`AP_NavEKF3/LogStructure.h:337`). -/
  ongroundnotmoving : UInt8 := (0 : UInt8)
  /-- `float gyro_length_ratio` of `log_XKFM` (`AP_NavEKF3/LogStructure.h:338`). -/
  gyro_length_ratio : Binary32 := (Binary32.ofBits 0x00000000 /- 0.0 -/)
  /-- `float accel_length_ratio` of `log_XKFM` (`AP_NavEKF3/LogStructure.h:339`). -/
  accel_length_ratio : Binary32 := (Binary32.ofBits 0x00000000 /- 0.0 -/)
  /-- `float gyro_diff_ratio` of `log_XKFM` (`AP_NavEKF3/LogStructure.h:340`). -/
  gyro_diff_ratio : Binary32 := (Binary32.ofBits 0x00000000 /- 0.0 -/)
  /-- `float accel_diff_ratio` of `log_XKFM` (`AP_NavEKF3/LogStructure.h:341`). -/
  accel_diff_ratio : Binary32 := (Binary32.ofBits 0x00000000 /- 0.0 -/)
deriving Inhabited

/-- C++ `struct log_XKQ`, `AP_NavEKF3/LogStructure.h:353-361`. -/
structure log_XKQ where
  /-- `uint8_t head1` of `log_XKQ` (`AP_NavEKF3/LogStructure.h:354`). -/
  head1 : UInt8 := (0 : UInt8)
  /-- `uint8_t head2` of `log_XKQ` (`AP_NavEKF3/LogStructure.h:354`). -/
  head2 : UInt8 := (0 : UInt8)
  /-- `uint8_t msgid` of `log_XKQ` (`AP_NavEKF3/LogStructure.h:354`). -/
  msgid : UInt8 := (0 : UInt8)
  /-- `uint64_t time_us` of `log_XKQ` (`AP_NavEKF3/LogStructure.h:355`). -/
  time_us : UInt64 := (0 : UInt64)
  /-- `uint8_t core` of `log_XKQ` (`AP_NavEKF3/LogStructure.h:356`). -/
  core : UInt8 := (0 : UInt8)
  /-- `float q1` of `log_XKQ` (`AP_NavEKF3/LogStructure.h:357`). -/
  q1 : Binary32 := (Binary32.ofBits 0x00000000 /- 0.0 -/)
  /-- `float q2` of `log_XKQ` (`AP_NavEKF3/LogStructure.h:358`). -/
  q2 : Binary32 := (Binary32.ofBits 0x00000000 /- 0.0 -/)
  /-- `float q3` of `log_XKQ` (`AP_NavEKF3/LogStructure.h:359`). -/
  q3 : Binary32 := (Binary32.ofBits 0x00000000 /- 0.0 -/)
  /-- `float q4` of `log_XKQ` (`AP_NavEKF3/LogStructure.h:360`). -/
  q4 : Binary32 := (Binary32.ofBits 0x00000000 /- 0.0 -/)
deriving Inhabited

/-- C++ `struct log_XKFS`, `AP_NavEKF3/LogStructure.h:376-388`. -/
structure log_XKFS where
  /-- `uint8_t head1` of `log_XKFS` (`AP_NavEKF3/LogStructure.h:377`). -/
  head1 : UInt8 := (0 : UInt8)
  /-- `uint8_t head2` of `log_XKFS` (`AP_NavEKF3/LogStructure.h:377`). -/
  head2 : UInt8 := (0 : UInt8)
  /-- `uint8_t msgid` of `log_XKFS` (`AP_NavEKF3/LogStructure.h:377`). -/
  msgid : UInt8 := (0 : UInt8)
  /-- `uint64_t time_us` of `log_XKFS` (`AP_NavEKF3/LogStructure.h:378`). -/
  time_us : UInt64 := (0 : UInt64)
  /-- `uint8_t core` of `log_XKFS` (`AP_NavEKF3/LogStructure.h:379`). -/
  core : UInt8 := (0 : UInt8)
  /-- `uint8_t mag_index` of `log_XKFS` (`AP_NavEKF3/LogStructure.h:380`). -/
  mag_index : UInt8 := (0 : UInt8)
  /-- `uint8_t baro_index` of `log_XKFS` (`AP_NavEKF3/LogStructure.h:381`). -/
  baro_index : UInt8 := (0 : UInt8)
  /-- `uint8_t gps_index` of `log_XKFS` (`AP_NavEKF3/LogStructure.h:382`). -/
  gps_index : UInt8 := (0 : UInt8)
  /-- `uint8_t airspeed_index` of `log_XKFS` (`AP_NavEKF3/LogStructure.h:383`). -/
  airspeed_index : UInt8 := (0 : UInt8)
  /-- `uint8_t source_set` of `log_XKFS` (`AP_NavEKF3/LogStructure.h:384`). -/
  source_set : UInt8 := (0 : UInt8)
  /-- `uint8_t gps_good_to_align` of `log_XKFS` (`AP_NavEKF3/LogStructure.h:385`). -/
  gps_good_to_align : UInt8 := (0 : UInt8)
  /-- `uint8_t wait_for_gps_checks` of `log_XKFS` (`AP_NavEKF3/LogStructure.h:386`). -/
  wait_for_gps_checks : UInt8 := (0 : UInt8)
  /-- `uint8_t mag_fusion` of `log_XKFS` (`AP_NavEKF3/LogStructure.h:387`). -/
  mag_fusion : UInt8 := (0 : UInt8)
deriving Inhabited

/-- C++ `struct log_XKTV`, `AP_NavEKF3/LogStructure.h:396-402`. -/
structure log_XKTV where
  /-- `uint8_t head1` of `log_XKTV` (`AP_NavEKF3/LogStructure.h:397`). -/
  head1 : UInt8 := (0 : UInt8)
  /-- `uint8_t head2` of `log_XKTV` (`AP_NavEKF3/LogStructure.h:397`). -/
  head2 : UInt8 := (0 : UInt8)
  /-- `uint8_t msgid` of `log_XKTV` (`AP_NavEKF3/LogStructure.h:397`). -/
  msgid : UInt8 := (0 : UInt8)
  /-- `uint64_t time_us` of `log_XKTV` (`AP_NavEKF3/LogStructure.h:398`). -/
  time_us : UInt64 := (0 : UInt64)
  /-- `uint8_t core` of `log_XKTV` (`AP_NavEKF3/LogStructure.h:399`). -/
  core : UInt8 := (0 : UInt8)
  /-- `float tvs` of `log_XKTV` (`AP_NavEKF3/LogStructure.h:400`). -/
  tvs : Binary32 := (Binary32.ofBits 0x00000000 /- 0.0 -/)
  /-- `float tvd` of `log_XKTV` (`AP_NavEKF3/LogStructure.h:401`). -/
  tvd : Binary32 := (Binary32.ofBits 0x00000000 /- 0.0 -/)
deriving Inhabited

/-- C++ `struct log_XKV`, `AP_NavEKF3/LogStructure.h:437-453`. -/
structure log_XKV where
  /-- `uint8_t head1` of `log_XKV` (`AP_NavEKF3/LogStructure.h:438`). -/
  head1 : UInt8 := (0 : UInt8)
  /-- `uint8_t head2` of `log_XKV` (`AP_NavEKF3/LogStructure.h:438`). -/
  head2 : UInt8 := (0 : UInt8)
  /-- `uint8_t msgid` of `log_XKV` (`AP_NavEKF3/LogStructure.h:438`). -/
  msgid : UInt8 := (0 : UInt8)
  /-- `uint64_t time_us` of `log_XKV` (`AP_NavEKF3/LogStructure.h:439`). -/
  time_us : UInt64 := (0 : UInt64)
  /-- `uint8_t core` of `log_XKV` (`AP_NavEKF3/LogStructure.h:440`). -/
  core : UInt8 := (0 : UInt8)
  /-- `float v00` of `log_XKV` (`AP_NavEKF3/LogStructure.h:441`). -/
  v00 : Binary32 := (Binary32.ofBits 0x00000000 /- 0.0 -/)
  /-- `float v01` of `log_XKV` (`AP_NavEKF3/LogStructure.h:442`). -/
  v01 : Binary32 := (Binary32.ofBits 0x00000000 /- 0.0 -/)
  /-- `float v02` of `log_XKV` (`AP_NavEKF3/LogStructure.h:443`). -/
  v02 : Binary32 := (Binary32.ofBits 0x00000000 /- 0.0 -/)
  /-- `float v03` of `log_XKV` (`AP_NavEKF3/LogStructure.h:444`). -/
  v03 : Binary32 := (Binary32.ofBits 0x00000000 /- 0.0 -/)
  /-- `float v04` of `log_XKV` (`AP_NavEKF3/LogStructure.h:445`). -/
  v04 : Binary32 := (Binary32.ofBits 0x00000000 /- 0.0 -/)
  /-- `float v05` of `log_XKV` (`AP_NavEKF3/LogStructure.h:446`). -/
  v05 : Binary32 := (Binary32.ofBits 0x00000000 /- 0.0 -/)
  /-- `float v06` of `log_XKV` (`AP_NavEKF3/LogStructure.h:447`). -/
  v06 : Binary32 := (Binary32.ofBits 0x00000000 /- 0.0 -/)
  /-- `float v07` of `log_XKV` (`AP_NavEKF3/LogStructure.h:448`). -/
  v07 : Binary32 := (Binary32.ofBits 0x00000000 /- 0.0 -/)
  /-- `float v08` of `log_XKV` (`AP_NavEKF3/LogStructure.h:449`). -/
  v08 : Binary32 := (Binary32.ofBits 0x00000000 /- 0.0 -/)
  /-- `float v09` of `log_XKV` (`AP_NavEKF3/LogStructure.h:450`). -/
  v09 : Binary32 := (Binary32.ofBits 0x00000000 /- 0.0 -/)
  /-- `float v10` of `log_XKV` (`AP_NavEKF3/LogStructure.h:451`). -/
  v10 : Binary32 := (Binary32.ofBits 0x00000000 /- 0.0 -/)
  /-- `float v11` of `log_XKV` (`AP_NavEKF3/LogStructure.h:452`). -/
  v11 : Binary32 := (Binary32.ofBits 0x00000000 /- 0.0 -/)
deriving Inhabited

end Estimator_lib
