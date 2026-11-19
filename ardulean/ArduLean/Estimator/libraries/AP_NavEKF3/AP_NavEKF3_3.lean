import ArduLean.Musl.asinf
import ArduLean.Musl.atan2
import ArduLean.Musl.cos
import ArduLean.Musl.sin
import ArduLean.Estimator.libraries.AP_Math.AP_Math
import ArduLean.Estimator.World
import ArduLean.Estimator.libraries.AP_Common.AP_Common
import ArduLean.Estimator.libraries.AP_Declination.AP_Declination
import ArduLean.Estimator.libraries.AP_Param.AP_Param
import ArduLean.Estimator.libraries.AP_NavEKF.AP_NavEKF
import ArduLean.Estimator.libraries.AP_GPS.AP_GPS
import ArduLean.Estimator.libraries.AP_NavEKF3.AP_NavEKF3
import ArduLean.Estimator.libraries.AP_DAL.AP_DAL
import ArduLean.Estimator.libraries.AP_Math.AP_Math_2
import ArduLean.Estimator.World_2
import ArduLean.Estimator.libraries.AP_NavEKF.AP_NavEKF_2
import ArduLean.Estimator.libraries.AP_NavEKF3.AP_NavEKF3_2
import ArduLean.Estimator.World_3

/-!
ArduPilot `libraries/AP_NavEKF3`, part 3 of 4. Sources: `libraries/AP_NavEKF3/AP_NavEKF3_core.cpp`, `libraries/AP_NavEKF3/AP_NavEKF3_PosVelFusion.cpp`, `libraries/AP_NavEKF3/AP_NavEKF3_Measurements.cpp`, `libraries/AP_NavEKF3/AP_NavEKF3.cpp`, `libraries/AP_NavEKF3/AP_NavEKF3_VehicleStatus.cpp`, `libraries/AP_NavEKF3/AP_NavEKF3_Outputs.cpp`, `libraries/AP_NavEKF3/AP_NavEKF3_Control.cpp`, `libraries/AP_NavEKF3/AP_NavEKF3_MagFusion.cpp` and 2 more.

Items of `lean/Estimator_lib.lean` (the estimator translation), unchanged; placed by `tools/split_modules.py` (`ArduLean/Estimator/INDEX.md`).
-/

open FloatLib.Floats (Binary32 Binary64)

set_option maxRecDepth 200000
-- AP_DAL's `const log_RISH old_RISH = _RISH;` read only by WRITE_REPLAY_BLOCK_IFCHANGED, which is `(void)old`
-- without logging (HAL_LOGGING_ENABLED 0): an unused binding, as in the C++
set_option linter.unusedVariables false

namespace Estimator_lib

namespace NavEKF3_core

/-- C++ `void NavEKF3_core::update_gps_selection()`, `AP_NavEKF3/AP_NavEKF3_Measurements.cpp:1192-1212`. -/
def update_gps_selection (s : State) (w : World) : State := Id.run do
  let mut s := s
  s := { s with selected_gps := AP_DAL_GPS.primary_sensor w.heap'AP_DAL[(WPtr.index w.AP_DAL'_singleton)]!._gps }
  s := { s with preferred_gps := s.selected_gps }
  if AP_ParamT_unsigned_int_3.op_to_unsigned_int w.EKF3._affinity &&& NavEKF3_core.ekf_affinity.toInt NavEKF3_core.ekf_affinity.EKF_AFFINITY_GPS != (0 : UInt32) then
    if UInt32.toInt32 (UInt8.toUInt32 s.core_index) < UInt32.toInt32 (UInt8.toUInt32 (AP_DAL_GPS.num_sensors w.heap'AP_DAL[(WPtr.index w.AP_DAL'_singleton)]!._gps)) then
      s := { s with preferred_gps := s.core_index }
    if AP_GPS_FixType.toInt (AP_DAL_GPS.status_uint8_t w.heap'AP_DAL[(WPtr.index w.AP_DAL'_singleton)]!._gps s.preferred_gps) ≥ AP_GPS_FixType.toInt AP_GPS_FixType.FIX_3D then
      s := { s with selected_gps := s.preferred_gps }
  return s

end NavEKF3_core

namespace NavEKF3_core

/-- C++ `void NavEKF3_core::tryChangeCompass(uint8_t compass_index)`, `AP_NavEKF3/AP_NavEKF3_Measurements.cpp:268-299`. -/
def tryChangeCompass_uint8_t (s : State) (w : World) (o : Outputs) (mag_index : UInt8) : State × Outputs := Id.run do
  let mut s := s
  let mut o := o
  let maxCount : UInt8 := AP_DAL_Compass.get_count w.heap'AP_DAL[(WPtr.index w.AP_DAL'_singleton)]!._compass
  if UInt32.toInt32 (UInt8.toUInt32 mag_index) ≥ UInt32.toInt32 (UInt8.toUInt32 maxCount) then
    return (s, o)
  if AP_DAL_Compass.healthy w.heap'AP_DAL[(WPtr.index w.AP_DAL'_singleton)]!._compass mag_index && AP_DAL_Compass.use_for_yaw w.heap'AP_DAL[(WPtr.index w.AP_DAL'_singleton)]!._compass mag_index && UInt32.toInt32 (UInt8.toUInt32 mag_index) != UInt32.toInt32 (UInt8.toUInt32 s.magSelectIndex) then
    s := { s with magSelectIndex := mag_index }
    o := o.push (Output.send_text (6 : UInt32) "EKF3 IMU%u switching to compass %u" #[Sum.inl (UInt32.toUInt64 (UInt8.toUInt32 s.imu_index)), Sum.inl (Int64.toUInt64 (Int32.toInt64 (UInt32.toInt32 (UInt8.toUInt32 s.magSelectIndex))))])
    s := { s with magTimeout := false }
    s := { s with lastHealthyMagTime_ms := s.imuSampleTime_ms }
    let t'1 := Vector3p.zero ({ x := s.statesArray[19]!, y := s.statesArray[20]!, z := s.statesArray[21]! } : Vector3p.State)
    s := { s with statesArray := (((s.statesArray.set! 19 t'1.x).set! 20 t'1.y).set! 21 t'1.z) }
    s := { s with storedMag := EKF_obs_buffer_t_NavEKF3_core_mag_elements.reset s.storedMag }
    s := { s with magDataToFuse := false }
    s := { s with magStateResetRequest := true }
    s := { s with magFieldLearned := false }
    s := { s with needMagBodyVarReset := true }
    return (s, o)
  return (s, o)

/-- C++ `void NavEKF3_core::update_mag_selection()`, `AP_NavEKF3/AP_NavEKF3_Measurements.cpp:1217-1235`. -/
def update_mag_selection (s : State) (w : World) (o : Outputs) : State × Outputs := Id.run do
  let mut s := s
  let mut o := o
  if AP_ParamT_unsigned_int_3.op_to_unsigned_int w.EKF3._affinity &&& NavEKF3_core.ekf_affinity.toInt NavEKF3_core.ekf_affinity.EKF_AFFINITY_MAG != (0 : UInt32) then
    if decide (UInt32.toInt32 (UInt8.toUInt32 s.core_index) < UInt32.toInt32 (UInt8.toUInt32 (AP_DAL_Compass.get_count w.heap'AP_DAL[(WPtr.index w.AP_DAL'_singleton)]!._compass))) && AP_DAL_Compass.healthy w.heap'AP_DAL[(WPtr.index w.AP_DAL'_singleton)]!._compass s.core_index && AP_DAL_Compass.use_for_yaw w.heap'AP_DAL[(WPtr.index w.AP_DAL'_singleton)]!._compass s.core_index then
      s := { s with magSelectIndex := s.core_index }
  else
    let primary_compass : UInt8 := AP_DAL_Compass.get_first_usable w.heap'AP_DAL[(WPtr.index w.AP_DAL'_singleton)]!._compass
    if !(AP_DAL.get_armed w.heap'AP_DAL[(WPtr.index w.AP_DAL'_singleton)]!) && (UInt32.toInt32 (UInt8.toUInt32 s.magSelectIndex) != UInt32.toInt32 (UInt8.toUInt32 primary_compass)) then
      let (t'1, t'2) := tryChangeCompass_uint8_t s w o primary_compass
      s := t'1
      o := t'2
  return (s, o)

end NavEKF3_core

namespace NavEKF3_core

/-- C++ `void NavEKF3_core::update_baro_selection()`, `AP_NavEKF3/AP_NavEKF3_Measurements.cpp:1240-1254`. -/
def update_baro_selection (s : State) (w : World) : State := Id.run do
  let mut s := s
  s := { s with selected_baro := AP_DAL_Baro.get_primary w.heap'AP_DAL[(WPtr.index w.AP_DAL'_singleton)]!._baro }
  if AP_ParamT_unsigned_int_3.op_to_unsigned_int w.EKF3._affinity &&& NavEKF3_core.ekf_affinity.toInt NavEKF3_core.ekf_affinity.EKF_AFFINITY_BARO != (0 : UInt32) then
    if decide (UInt32.toInt32 (UInt8.toUInt32 s.core_index) < UInt32.toInt32 (UInt8.toUInt32 (AP_DAL_Baro.num_instances w.heap'AP_DAL[(WPtr.index w.AP_DAL'_singleton)]!._baro))) && AP_DAL_Baro.healthy w.heap'AP_DAL[(WPtr.index w.AP_DAL'_singleton)]!._baro s.core_index then
      s := { s with selected_baro := s.core_index }
  return s

end NavEKF3_core

namespace NavEKF3_core

/-- C++ `bool NavEKF3_core::assume_zero_sideslip() const`, `AP_NavEKF3/AP_NavEKF3_Control.cpp:698-704`. -/
def assume_zero_sideslip (w : World) : Bool := Id.run do
  return AP_DAL.get_fly_forward w.heap'AP_DAL[(WPtr.index w.AP_DAL'_singleton)]! && AP_DAL.get_vehicle_class w.heap'AP_DAL[(WPtr.index w.AP_DAL'_singleton)]! != AP_DAL.VehicleClass.GROUND

end NavEKF3_core

namespace NavEKF3_core

/-- C++ `void NavEKF3_core::learnInactiveBiases()`, `AP_NavEKF3/AP_NavEKF3_Measurements.cpp:1322-1389`. -/
def learnInactiveBiases (s : State) (w : World) : State := Id.run do
  let mut s := s
  for i' in [0:3] do
    let i : UInt8 := Nat.toUInt8 i'
    if !(AP_DAL_InertialSensor.use_gyro w.heap'AP_DAL[(WPtr.index w.AP_DAL'_singleton)]!._ins i) then
      continue
    if UInt32.toInt32 (UInt8.toUInt32 s.gyro_index_active) == UInt32.toInt32 (UInt8.toUInt32 i) then
      s := { s with inactiveBias := s.inactiveBias.set! (UInt8.toNat i) ({ s.inactiveBias[UInt8.toNat i]! with gyro_bias := ({ x := s.statesArray[10]!, y := s.statesArray[11]!, z := s.statesArray[12]! } : Vector3p.State) }) }
    else
      let t'1 := s.gyro_index_active
      let t'2 := Vector3f.todouble w.heap'AP_DAL[(WPtr.index w.AP_DAL'_singleton)]!._ins.gyro_filtered[UInt8.toNat t'1]!
      let filtered_gyro_active : Vector3p.State := Vector3p.op_sub_Vector3p t'2 (Vector3p.op_div ({ x := s.statesArray[10]!, y := s.statesArray[11]!, z := s.statesArray[12]! } : Vector3p.State) s.dtEkfAvg)
      let t'3 := i
      let t'4 := Vector3f.todouble w.heap'AP_DAL[(WPtr.index w.AP_DAL'_singleton)]!._ins.gyro_filtered[UInt8.toNat t'3]!
      let filtered_gyro_inactive : Vector3p.State := Vector3p.op_sub_Vector3p t'4 (Vector3p.op_div s.inactiveBias[UInt8.toNat i]!.gyro_bias s.dtEkfAvg)
      let mut error : Vector3p.State := Vector3p.op_sub_Vector3p filtered_gyro_active filtered_gyro_inactive
      let bias_limit : Binary64 := Binary32.toBinary64 (Estimator_lib.radians_int32_t (5 : Int32))
      error := { error with x := Estimator_lib.constrain_value_line_double error.x (-bias_limit) bias_limit (Int32.toUInt32 (1349 : Int32)) }
      error := { error with y := Estimator_lib.constrain_value_line_double error.y (-bias_limit) bias_limit (Int32.toUInt32 (1350 : Int32)) }
      error := { error with z := Estimator_lib.constrain_value_line_double error.z (-bias_limit) bias_limit (Int32.toUInt32 (1351 : Int32)) }
      let (t'5, _) := Vector3p.op_sub_assign s.inactiveBias[UInt8.toNat i]!.gyro_bias (Vector3p.op_mul_double error ((Binary64.ofBits 0x3f1a36e2e0000000 /- 1.0e-4f -/) * s.dtEkfAvg))
      s := { s with inactiveBias := s.inactiveBias.set! (UInt8.toNat i) ({ s.inactiveBias[UInt8.toNat i]! with gyro_bias := t'5 }) }
  for i'2' in [0:3] do
    let i'2 : UInt8 := Nat.toUInt8 i'2'
    if !(AP_DAL_InertialSensor.use_accel w.heap'AP_DAL[(WPtr.index w.AP_DAL'_singleton)]!._ins i'2) then
      continue
    if UInt32.toInt32 (UInt8.toUInt32 s.accel_index_active) == UInt32.toInt32 (UInt8.toUInt32 i'2) then
      s := { s with inactiveBias := s.inactiveBias.set! (UInt8.toNat i'2) ({ s.inactiveBias[UInt8.toNat i'2]! with accel_bias := ({ x := s.statesArray[13]!, y := s.statesArray[14]!, z := s.statesArray[15]! } : Vector3p.State) }) }
    else
      let t'7 := s.accel_index_active
      let t'8 := Vector3f.todouble w.heap'AP_DAL[(WPtr.index w.AP_DAL'_singleton)]!._ins.accel_filtered[UInt8.toNat t'7]!
      let filtered_accel_active : Vector3p.State := Vector3p.op_sub_Vector3p t'8 (Vector3p.op_div ({ x := s.statesArray[13]!, y := s.statesArray[14]!, z := s.statesArray[15]! } : Vector3p.State) s.dtEkfAvg)
      let t'9 := i'2
      let t'10 := Vector3f.todouble w.heap'AP_DAL[(WPtr.index w.AP_DAL'_singleton)]!._ins.accel_filtered[UInt8.toNat t'9]!
      let filtered_accel_inactive : Vector3p.State := Vector3p.op_sub_Vector3p t'10 (Vector3p.op_div s.inactiveBias[UInt8.toNat i'2]!.accel_bias s.dtEkfAvg)
      let mut error'2 : Vector3p.State := Vector3p.op_sub_Vector3p filtered_accel_active filtered_accel_inactive
      let bias_limit'2 : Binary64 := (Binary64.ofBits 0x3ff0000000000000 /- 1.0 -/)
      error'2 := { error'2 with x := Estimator_lib.constrain_value_line_double error'2.x (-bias_limit'2) bias_limit'2 (Int32.toUInt32 (1378 : Int32)) }
      error'2 := { error'2 with y := Estimator_lib.constrain_value_line_double error'2.y (-bias_limit'2) bias_limit'2 (Int32.toUInt32 (1379 : Int32)) }
      error'2 := { error'2 with z := Estimator_lib.constrain_value_line_double error'2.z (-bias_limit'2) bias_limit'2 (Int32.toUInt32 (1380 : Int32)) }
      let (t'11, _) := Vector3p.op_sub_assign s.inactiveBias[UInt8.toNat i'2]!.accel_bias (Vector3p.op_mul_double error'2 ((Binary64.ofBits 0x3f1a36e2e0000000 /- 1.0e-4f -/) * s.dtEkfAvg))
      s := { s with inactiveBias := s.inactiveBias.set! (UInt8.toNat i'2) ({ s.inactiveBias[UInt8.toNat i'2]! with accel_bias := t'11 }) }
  return s

/-- C++ `void NavEKF3_core::updateMovementCheck()`, `AP_NavEKF3/AP_NavEKF3_Measurements.cpp:1414-1492`. -/
def updateMovementCheck (s : State) (w : World) : State := Id.run do
  let mut s := s
  if !s.onGround then
    s := { s with onGroundNotMoving := false }
    return s
  let gyro_limit : Binary64 := Binary32.toBinary64 (Estimator_lib.radians_float (Binary32.ofBits 0x40400000 /- 3.0f -/))
  let gyro_diff_limit : Binary64 := (Binary64.ofBits 0x3fc99999a0000000 /- 0.2f -/)
  let accel_limit : Binary64 := (Binary64.ofBits 0x3ff0000000000000 /- 1.0f -/)
  let accel_diff_limit : Binary64 := (Binary64.ofBits 0x4014000000000000 /- 5.0f -/)
  let hysteresis_ratio : Binary64 := (Binary64.ofBits 0x3fe6666660000000 /- 0.7f -/)
  let dtEkfAvgInv : Binary64 := (Binary64.ofBits 0x3ff0000000000000 /- 1.0f -/) / s.dtEkfAvg
  let t'1 := s.gyro_index_active
  let t'2 := Vector3f.todouble w.heap'AP_DAL[(WPtr.index w.AP_DAL'_singleton)]!._ins.gyro_filtered[UInt8.toNat t'1]!
  let gyro : Vector3p.State := Vector3p.op_sub_Vector3p t'2 (Vector3p.op_mul_double ({ x := s.statesArray[10]!, y := s.statesArray[11]!, z := s.statesArray[12]! } : Vector3p.State) dtEkfAvgInv)
  let t'3 := s.accel_index_active
  let t'4 := Vector3f.todouble w.heap'AP_DAL[(WPtr.index w.AP_DAL'_singleton)]!._ins.accel_filtered[UInt8.toNat t'3]!
  let accel : Vector3p.State := Vector3p.op_sub_Vector3p t'4 (Vector3p.op_mul_double ({ x := s.statesArray[13]!, y := s.statesArray[14]!, z := s.statesArray[15]! } : Vector3p.State) dtEkfAvgInv)
  if !s.prevOnGround then
    s := { s with gyro_prev := gyro }
    s := { s with accel_prev := accel }
    s := { s with onGroundNotMoving := false }
    s := { s with gyro_diff := gyro_diff_limit }
    s := { s with accel_diff := accel_diff_limit }
    return s
  let mut temp : Vector3p.State := Vector3p.op_mul_double (Vector3p.op_sub_Vector3p gyro s.gyro_prev) dtEkfAvgInv
  s := { s with gyro_prev := gyro }
  s := { s with gyro_diff := (Binary64.ofBits 0x3fefae1480000000 /- 0.99f -/) * s.gyro_diff + (Binary64.ofBits 0x3f847ae140000000 /- 0.01f -/) * Vector3p.length temp }
  temp := Vector3p.op_mul_double (Vector3p.op_sub_Vector3p accel s.accel_prev) dtEkfAvgInv
  s := { s with accel_prev := accel }
  s := { s with accel_diff := (Binary64.ofBits 0x3fefae1480000000 /- 0.99f -/) * s.accel_diff + (Binary64.ofBits 0x3f847ae140000000 /- 0.01f -/) * Vector3p.length temp }
  let gyro_length_ratio : Binary64 := Vector3p.length gyro / gyro_limit
  let accel_length_ratio : Binary64 := (Vector3p.length accel - (Binary64.ofBits 0x40239d0140000000 /- (double)5141509/524288 -/)) / accel_limit
  let gyro_diff_ratio : Binary64 := s.gyro_diff / gyro_diff_limit
  let accel_diff_ratio : Binary64 := s.accel_diff / accel_diff_limit
  let mut logStatusChange : Bool := false
  if s.onGroundNotMoving then
    if decide (gyro_length_ratio > Binary32.toBinary64 (AP_ParamT_float_4.op_to_float w.EKF3._ognmTestScaleFactor)) || decide (Binary64.abs accel_length_ratio > Binary32.toBinary64 (AP_ParamT_float_4.op_to_float w.EKF3._ognmTestScaleFactor)) || decide (gyro_diff_ratio > Binary32.toBinary64 (AP_ParamT_float_4.op_to_float w.EKF3._ognmTestScaleFactor)) || decide (accel_diff_ratio > Binary32.toBinary64 (AP_ParamT_float_4.op_to_float w.EKF3._ognmTestScaleFactor)) then
      s := { s with onGroundNotMoving := false }
      logStatusChange := true
  else if decide (gyro_length_ratio < Binary32.toBinary64 (AP_ParamT_float_4.op_to_float w.EKF3._ognmTestScaleFactor) * hysteresis_ratio) && decide (Binary64.abs accel_length_ratio < Binary32.toBinary64 (AP_ParamT_float_4.op_to_float w.EKF3._ognmTestScaleFactor) * hysteresis_ratio) && decide (gyro_diff_ratio < Binary32.toBinary64 (AP_ParamT_float_4.op_to_float w.EKF3._ognmTestScaleFactor) * hysteresis_ratio) && decide (accel_diff_ratio < Binary32.toBinary64 (AP_ParamT_float_4.op_to_float w.EKF3._ognmTestScaleFactor) * hysteresis_ratio) then
    s := { s with onGroundNotMoving := true }
    logStatusChange := true
  if logStatusChange || decide (s.imuSampleTime_ms - s.lastMoveCheckLogTime_ms > Int32.toUInt32 (200 : Int32)) then
    s := { s with lastMoveCheckLogTime_ms := s.imuSampleTime_ms }
  return s

end NavEKF3_core

namespace NavEKF3_core

/-- C++ `bool NavEKF3_core::readDeltaVelocity(uint8_t ins_index, Vector3F & dVel, ftype & dVel_dt)`, `AP_NavEKF3/AP_NavEKF3_Measurements.cpp:542-555`. -/
def readDeltaVelocity (w : World) (ins_index : UInt8) (dVel : Vector3p.State) (dVel_dt : Binary64) : Vector3p.State × Binary64 × Bool := Id.run do
  let mut dVel := dVel
  let mut dVel_dt := dVel_dt
  if UInt32.toInt32 (UInt8.toUInt32 ins_index) < UInt32.toInt32 (UInt8.toUInt32 (AP_DAL_InertialSensor.get_accel_count w.heap'AP_DAL[(WPtr.index w.AP_DAL'_singleton)]!._ins)) then
    let mut dVelF : Vector3f.State := Vector3f.init_void
    let mut dVel_dtF : Binary32 := (Binary32.ofBits 0x00000000 /- 0.0 -/)  -- uninitialized in C++; assigned before every read
    let (t'1, t'2, _) := AP_DAL_InertialSensor.get_delta_velocity w.heap'AP_DAL[(WPtr.index w.AP_DAL'_singleton)]!._ins ins_index dVelF dVel_dtF
    dVelF := t'1
    dVel_dtF := t'2
    dVel := Vector3f.todouble dVelF
    dVel_dt := Binary32.toBinary64 dVel_dtF
    dVel_dt := Estimator_lib.MAX_double_float dVel_dt (Binary32.ofBits 0x38d1b717 /- 1.0e-4 -/)
    return (dVel, dVel_dt, true)
  return (dVel, dVel_dt, false)

end NavEKF3_core

namespace NavEKF3_core

/-- C++ `bool NavEKF3_core::readDeltaAngle(uint8_t ins_index, Vector3F & dAng, ftype & dAng_dt)`, `AP_NavEKF3/AP_NavEKF3_Measurements.cpp:763-775`. -/
def readDeltaAngle (w : World) (ins_index : UInt8) (dAng : Vector3p.State) (dAngDT : Binary64) : Vector3p.State × Binary64 × Bool := Id.run do
  let mut dAng := dAng
  let mut dAngDT := dAngDT
  if UInt32.toInt32 (UInt8.toUInt32 ins_index) < UInt32.toInt32 (UInt8.toUInt32 (AP_DAL_InertialSensor.get_gyro_count w.heap'AP_DAL[(WPtr.index w.AP_DAL'_singleton)]!._ins)) then
    let mut dAngF : Vector3f.State := Vector3f.init_void
    let mut dAngDTF : Binary32 := (Binary32.ofBits 0x00000000 /- 0.0 -/)  -- uninitialized in C++; assigned before every read
    let (t'1, t'2, _) := AP_DAL_InertialSensor.get_delta_angle w.heap'AP_DAL[(WPtr.index w.AP_DAL'_singleton)]!._ins ins_index dAngF dAngDTF
    dAngF := t'1
    dAngDTF := t'2
    dAng := Vector3f.todouble dAngF
    dAngDT := Binary32.toBinary64 dAngDTF
    return (dAng, dAngDT, true)
  return (dAng, dAngDT, false)

end NavEKF3_core

namespace NavEKF3_core

/-- C++ `void NavEKF3_core::updateTimingStatistics()`, `AP_NavEKF3/AP_NavEKF3_Measurements.cpp:1293-1315`. -/
def updateTimingStatistics (s : State) : State := Id.run do
  let mut s := s
  if s.timing.count == Int32.toUInt32 (0 : Int32) then
    s := { s with timing.dtIMUavg_max := Binary64.toBinary32 s.dtIMUavg }
    s := { s with timing.dtIMUavg_min := Binary64.toBinary32 s.dtIMUavg }
    s := { s with timing.dtEKFavg_max := Binary64.toBinary32 s.dtEkfAvg }
    s := { s with timing.dtEKFavg_min := Binary64.toBinary32 s.dtEkfAvg }
    s := { s with timing.delAngDT_max := Binary64.toBinary32 s.imuDataDelayed.delAngDT }
    s := { s with timing.delAngDT_min := Binary64.toBinary32 s.imuDataDelayed.delAngDT }
    s := { s with timing.delVelDT_max := Binary64.toBinary32 s.imuDataDelayed.delVelDT }
    s := { s with timing.delVelDT_min := Binary64.toBinary32 s.imuDataDelayed.delVelDT }
  else
    s := { s with timing.dtIMUavg_max := Binary64.toBinary32 (Estimator_lib.MAX_float_double s.timing.dtIMUavg_max s.dtIMUavg) }
    s := { s with timing.dtIMUavg_min := Binary64.toBinary32 (Estimator_lib.MIN_float_double s.timing.dtIMUavg_min s.dtIMUavg) }
    s := { s with timing.dtEKFavg_max := Binary64.toBinary32 (Estimator_lib.MAX_float_double s.timing.dtEKFavg_max s.dtEkfAvg) }
    s := { s with timing.dtEKFavg_min := Binary64.toBinary32 (Estimator_lib.MIN_float_double s.timing.dtEKFavg_min s.dtEkfAvg) }
    s := { s with timing.delAngDT_max := Binary64.toBinary32 (Estimator_lib.MAX_float_double s.timing.delAngDT_max s.imuDataDelayed.delAngDT) }
    s := { s with timing.delAngDT_min := Binary64.toBinary32 (Estimator_lib.MIN_float_double s.timing.delAngDT_min s.imuDataDelayed.delAngDT) }
    s := { s with timing.delVelDT_max := Binary64.toBinary32 (Estimator_lib.MAX_float_double s.timing.delVelDT_max s.imuDataDelayed.delVelDT) }
    s := { s with timing.delVelDT_min := Binary64.toBinary32 (Estimator_lib.MIN_float_double s.timing.delVelDT_min s.imuDataDelayed.delVelDT) }
  s := { s with timing.count := s.timing.count + (1 : UInt32) }
  return s

/-- C++ `void NavEKF3_core::correctDeltaAngle(Vector3F & delAng, ftype delAngDT, uint8_t gyro_index)`, `AP_NavEKF3/AP_NavEKF3_core.cpp:714-717`. -/
def correctDeltaAngle (s : State) (delAng : Vector3p.State) (delAngDT : Binary64) (gyro_index : UInt8) : Vector3p.State := Id.run do
  let mut delAng := delAng
  let (t'1, _) := Vector3p.op_sub_assign delAng (Vector3p.op_mul_double s.inactiveBias[UInt8.toNat gyro_index]!.gyro_bias (delAngDT / s.dtEkfAvg))
  delAng := t'1
  return delAng

/-- C++ `void NavEKF3_core::correctDeltaVelocity(Vector3F & delVel, ftype delVelDT, uint8_t accel_index)`, `AP_NavEKF3/AP_NavEKF3_core.cpp:719-722`. -/
def correctDeltaVelocity (s : State) (delVel : Vector3p.State) (delVelDT : Binary64) (accel_index : UInt8) : Vector3p.State := Id.run do
  let mut delVel := delVel
  let (t'1, _) := Vector3p.op_sub_assign delVel (Vector3p.op_mul_double s.inactiveBias[UInt8.toNat accel_index]!.accel_bias (delVelDT / s.dtEkfAvg))
  delVel := t'1
  return delVel

/-- C++ `void NavEKF3_core::readIMUData(bool startPredictEnabled)`, `AP_NavEKF3/AP_NavEKF3_Measurements.cpp:397-538`. -/
def readIMUData (s : State) (w : World) (startPredictEnabled : Bool) : State := Id.run do
  let mut s := s
  s := { s with dtIMUavg := (Binary64.ofBits 0x3f947ae140000000 /- 0.02f -/) * Estimator_lib.constrain_value_line_double (Binary32.toBinary64 (AP_DAL_InertialSensor.get_loop_delta_t w.heap'AP_DAL[(WPtr.index w.AP_DAL'_singleton)]!._ins)) ((Binary64.ofBits 0x3fe0000000000000 /- (double)1/2 -/) * s.dtIMUavg) ((Binary64.ofBits 0x4000000000000000 /- (double)2 -/) * s.dtIMUavg) (Int32.toUInt32 (402 : Int32)) + (Binary64.ofBits 0x3fef5c2900000000 /- 0.98f -/) * s.dtIMUavg }
  s := { s with imuSampleTime_ms := UInt64.toUInt32 (w.EKF3.imuSampleTime_us / Int64.toUInt64 (Int32.toInt64 (1000 : Int32))) }
  let mut accel_active : UInt8 := (0 : UInt8)  -- uninitialized in C++; assigned before every read
  let mut gyro_active : UInt8 := (0 : UInt8)  -- uninitialized in C++; assigned before every read
  if AP_DAL_InertialSensor.use_accel w.heap'AP_DAL[(WPtr.index w.AP_DAL'_singleton)]!._ins s.imu_index then
    accel_active := s.imu_index
  else
    accel_active := AP_DAL_InertialSensor.get_first_usable_accel w.heap'AP_DAL[(WPtr.index w.AP_DAL'_singleton)]!._ins
  if AP_DAL_InertialSensor.use_gyro w.heap'AP_DAL[(WPtr.index w.AP_DAL'_singleton)]!._ins s.imu_index then
    gyro_active := s.imu_index
  else
    gyro_active := AP_DAL_InertialSensor.get_first_usable_gyro w.heap'AP_DAL[(WPtr.index w.AP_DAL'_singleton)]!._ins
  if UInt32.toInt32 (UInt8.toUInt32 gyro_active) != UInt32.toInt32 (UInt8.toUInt32 s.gyro_index_active) then
    let t'1 := s.inactiveBias[UInt8.toNat gyro_active]!.gyro_bias
    s := { s with statesArray := (((s.statesArray.set! 10 t'1.x).set! 11 t'1.y).set! 12 t'1.z) }
    s := { s with gyro_index_active := gyro_active }
  if UInt32.toInt32 (UInt8.toUInt32 accel_active) != UInt32.toInt32 (UInt8.toUInt32 s.accel_index_active) then
    let t'2 := s.inactiveBias[UInt8.toNat accel_active]!.accel_bias
    s := { s with statesArray := (((s.statesArray.set! 13 t'2.x).set! 14 t'2.y).set! 15 t'2.z) }
    s := { s with accel_index_active := accel_active }
  s := learnInactiveBiases s w
  s := updateMovementCheck s w
  let (t'3, t'4, _) := readDeltaVelocity w s.accel_index_active s.imuDataNew.delVel s.imuDataNew.delVelDT
  s := { s with imuDataNew.delVel := t'3 }
  s := { s with imuDataNew.delVelDT := t'4 }
  let t'6 := s.accel_index_active
  s := { s with accelPosOffset := Vector3f.todouble w.heap'AP_DAL[(WPtr.index w.AP_DAL'_singleton)]!._ins.pos[UInt8.toNat t'6]! }
  s := { s with imuDataNew.accel_index := s.accel_index_active }
  let (t'7, t'8, _) := readDeltaAngle w s.gyro_index_active s.imuDataNew.delAng s.imuDataNew.delAngDT
  s := { s with imuDataNew.delAng := t'7 }
  s := { s with imuDataNew.delAngDT := t'8 }
  s := { s with imuDataNew.delAngDT := Estimator_lib.MAX_double_float s.imuDataNew.delAngDT (Binary32.ofBits 0x38d1b717 /- 1.0e-4f -/) }
  s := { s with imuDataNew.gyro_index := s.gyro_index_active }
  s := { s with imuDataNew.time_ms := s.imuSampleTime_ms }
  s := { s with imuDataDownSampledNew.delAngDT := s.imuDataDownSampledNew.delAngDT + s.imuDataNew.delAngDT }
  s := { s with imuDataDownSampledNew.delVelDT := s.imuDataDownSampledNew.delVelDT + s.imuDataNew.delVelDT }
  s := { s with imuDataDownSampledNew.gyro_index := s.imuDataNew.gyro_index }
  s := { s with imuDataDownSampledNew.accel_index := s.imuDataNew.accel_index }
  s := { s with imuQuatDownSampleNew := QuaternionT_double.rotate_Vector3p s.imuQuatDownSampleNew s.imuDataNew.delAng }
  s := { s with imuQuatDownSampleNew := QuaternionT_double.normalize s.imuQuatDownSampleNew }
  let mut deltaRotMat : Matrix3_double.State := Matrix3_double.init_void
  deltaRotMat := QuaternionT_double.rotation_matrix_Matrix3_double s.imuQuatDownSampleNew deltaRotMat
  let (t'10, _) := Vector3p.op_add_assign s.imuDataDownSampledNew.delVel (Matrix3_double.op_mul_Vector3p deltaRotMat s.imuDataNew.delVel)
  s := { s with imuDataDownSampledNew.delVel := t'10 }
  s := { s with framesSincePredict := s.framesSincePredict + (1 : UInt32) }
  if (decide (s.imuDataDownSampledNew.delAngDT ≥ ((Binary64.ofBits 0x3f889374c0000000 /- (double)6442451/536870912 -/) - (s.dtIMUavg * (Binary64.ofBits 0x3fe0000000000000 /- 0.5f -/)))) && startPredictEnabled) || (decide (s.imuDataDownSampledNew.delAngDT ≥ (Binary64.ofBits 0x3f989374c0000000 /- (double)6442451/268435456 -/))) then
    s := { s with imuDataDownSampledNew.delAng := QuaternionT_double.to_axis_angle s.imuQuatDownSampleNew s.imuDataDownSampledNew.delAng }
    s := { s with imuDataDownSampledNew.time_ms := s.imuSampleTime_ms }
    s := { s with storedIMU := EKF_IMU_buffer_t_NavEKF3_core_imu_elements.push_youngest_element_imu_elements s.storedIMU s.imuDataDownSampledNew }
    let dtNow : Binary64 := Estimator_lib.constrain_value_line_double ((Binary64.ofBits 0x3fe0000000000000 /- (double)1/2 -/) * (s.imuDataDownSampledNew.delAngDT + s.imuDataDownSampledNew.delVelDT)) ((Binary64.ofBits 0x3fe0000000000000 /- (double)1/2 -/) * s.dtEkfAvg) ((Binary64.ofBits 0x4000000000000000 /- (double)2 -/) * s.dtEkfAvg) (Int32.toUInt32 (498 : Int32))
    s := { s with dtEkfAvg := (Binary64.ofBits 0x3fef5c2900000000 /- 0.98f -/) * s.dtEkfAvg + (Binary64.ofBits 0x3f947ae140000000 /- 0.02f -/) * dtNow }
    pure ()  -- C++ `SampleDragData`: no effect in the model
    s := { s with imuDataDownSampledNew.delAng := Vector3p.zero s.imuDataDownSampledNew.delAng }
    s := { s with imuDataDownSampledNew.delVel := Vector3p.zero s.imuDataDownSampledNew.delVel }
    s := { s with imuDataDownSampledNew.delAngDT := (Binary64.ofBits 0x0000000000000000 /- 0.0f -/) }
    s := { s with imuDataDownSampledNew.delVelDT := (Binary64.ofBits 0x0000000000000000 /- 0.0f -/) }
    s := { s with imuQuatDownSampleNew.q1 := (Binary64.ofBits 0x3ff0000000000000 /- 1.0f -/) }
    s := { s with imuQuatDownSampleNew.q2 := (Binary64.ofBits 0x0000000000000000 /- 0.0f -/) }
    s := { s with imuQuatDownSampleNew.q3 := s.imuQuatDownSampleNew.q2 }
    s := { s with imuQuatDownSampleNew.q4 := s.imuQuatDownSampleNew.q3 }
    s := { s with framesSincePredict := Int32.toUInt32 (0 : Int32) }
    s := { s with runUpdates := true }
    s := { s with imuDataDelayed := EKF_IMU_buffer_t_NavEKF3_core_imu_elements.get_oldest_element_void s.storedIMU }
    let minDT : Binary64 := (Binary64.ofBits 0x3fb99999a0000000 /- 0.1f -/) * s.dtEkfAvg
    s := { s with imuDataDelayed.delAngDT := Estimator_lib.MAX_double2 s.imuDataDelayed.delAngDT minDT }
    s := { s with imuDataDelayed.delVelDT := Estimator_lib.MAX_double2 s.imuDataDelayed.delVelDT minDT }
    s := updateTimingStatistics s
    s := { s with delAngCorrected := s.imuDataDelayed.delAng }
    s := { s with delVelCorrected := s.imuDataDelayed.delVel }
    s := { s with delAngCorrected := correctDeltaAngle s s.delAngCorrected s.imuDataDelayed.delAngDT s.imuDataDelayed.gyro_index }
    s := { s with delVelCorrected := correctDeltaVelocity s s.delVelCorrected s.imuDataDelayed.delVelDT s.imuDataDelayed.accel_index }
  else
    s := { s with runUpdates := false }
  return s

end NavEKF3_core

namespace NavEKF3_core

/-- C++ `void NavEKF3_core::tryChangeCompass()`, `AP_NavEKF3/AP_NavEKF3_Measurements.cpp:251-265`. -/
def tryChangeCompass_void (s : State) (w : World) (o : Outputs) : State × Outputs := Id.run do
  let mut s := s
  let mut o := o
  let maxCount : UInt8 := AP_DAL_Compass.get_count w.heap'AP_DAL[(WPtr.index w.AP_DAL'_singleton)]!._compass
  for i' in [1:maxCount.toNat] do
    let i : UInt8 := Nat.toUInt8 i'
    let mut tempIndex : UInt8 := Int8.toUInt8 (Int32.toInt8 (UInt32.toInt32 (UInt8.toUInt32 s.magSelectIndex) + UInt32.toInt32 (UInt8.toUInt32 i)))
    if UInt32.toInt32 (UInt8.toUInt32 tempIndex) ≥ UInt32.toInt32 (UInt8.toUInt32 maxCount) then
      tempIndex := Int8.toUInt8 (Int32.toInt8 (UInt32.toInt32 (UInt8.toUInt32 tempIndex) - UInt32.toInt32 (UInt8.toUInt32 maxCount)))
    let (t'1, t'2) := tryChangeCompass_uint8_t s w o tempIndex
    s := t'1
    o := t'2
  return (s, o)

/-- C++ `bool NavEKF3_core::use_compass() const`, `AP_NavEKF3/AP_NavEKF3_Control.cpp:633-644`. -/
def use_compass (s : State) (w : World) : Bool := Id.run do
  if (s.yaw_source_last != AP_NavEKF_Source.SourceYaw.COMPASS) && (s.yaw_source_last != AP_NavEKF_Source.SourceYaw.GPS_COMPASS_FALLBACK) then
    return false
  return AP_DAL_Compass.use_for_yaw w.heap'AP_DAL[(WPtr.index w.AP_DAL'_singleton)]!._compass s.magSelectIndex && !s.allMagSensorsFailed

/-- C++ `void NavEKF3_core::readMagData()`, `AP_NavEKF3/AP_NavEKF3_Measurements.cpp:302-384`. -/
def readMagData (s : State) (w : World) (o : Outputs) : State × Outputs := Id.run do
  let mut s := s
  let mut o := o
  if !(AP_DAL_Compass.available w.heap'AP_DAL[(WPtr.index w.AP_DAL'_singleton)]!._compass) then
    s := { s with allMagSensorsFailed := true }
    return (s, o)
  let maxCount : UInt8 := AP_DAL_Compass.get_count w.heap'AP_DAL[(WPtr.index w.AP_DAL'_singleton)]!._compass
  if s.allMagSensorsFailed || (s.magTimeout && assume_zero_sideslip w && decide (UInt32.toInt32 (UInt8.toUInt32 s.magSelectIndex) ≥ UInt32.toInt32 (UInt8.toUInt32 maxCount) - (1 : Int32)) && s.inFlight) then
    s := { s with allMagSensorsFailed := true }
    return (s, o)
  if AP_DAL_Compass.learn_offsets_enabled w.heap'AP_DAL[(WPtr.index w.AP_DAL'_singleton)]!._compass then
    s := { s with wasLearningCompass_ms := s.imuSampleTime_ms }
  else if s.wasLearningCompass_ms != Int32.toUInt32 (0 : Int32) && decide (s.imuSampleTime_ms - s.wasLearningCompass_ms > Int32.toUInt32 (1000 : Int32)) then
    s := { s with wasLearningCompass_ms := Int32.toUInt32 (0 : Int32) }
  if UInt32.toInt32 (UInt8.toUInt32 maxCount) > (1 : Int32) then
    let fusionTimeout : Bool := s.magTimeout && !s.onGround && decide (s.imuSampleTime_ms - s.ekfStartTime_ms > Int32.toUInt32 (30000 : Int32)) && !((AP_ParamT_unsigned_int_3.op_to_unsigned_int w.EKF3._affinity &&& NavEKF3_core.ekf_affinity.toInt NavEKF3_core.ekf_affinity.EKF_AFFINITY_MAG) != (0 : UInt32))
    let sensorTimeout : Bool := !(AP_DAL_Compass.healthy w.heap'AP_DAL[(WPtr.index w.AP_DAL'_singleton)]!._compass s.magSelectIndex) && decide (s.imuSampleTime_ms - s.lastMagRead_ms > w.EKF3.magFailTimeLimit_ms)
    if fusionTimeout || sensorTimeout then
      let (t'1, t'2) := tryChangeCompass_void s w o
      s := t'1
      o := t'2
  if use_compass s w && AP_DAL_Compass.healthy w.heap'AP_DAL[(WPtr.index w.AP_DAL'_singleton)]!._compass s.magSelectIndex && (decide ((AP_DAL_Compass.last_update_usec w.heap'AP_DAL[(WPtr.index w.AP_DAL'_singleton)]!._compass s.magSelectIndex - s.lastMagUpdate_us) > Int32.toUInt32 ((1000 : Int32) * UInt32.toInt32 (UInt8.toUInt32 w.EKF3.sensorIntervalMin_ms)))) then
    let t'3 := s.magSelectIndex
    let nowMagOffsets : Vector3p.State := Vector3f.todouble w.heap'AP_DAL[(WPtr.index w.AP_DAL'_singleton)]!._compass._RMGI[UInt8.toNat t'3]!.offsets
    let changeDetected : Bool := s.lastMagOffsetsValid && (Vector3p.op_ne nowMagOffsets s.lastMagOffsets)
    if changeDetected then
      let t'4 := Vector3p.zero ({ x := s.statesArray[19]!, y := s.statesArray[20]!, z := s.statesArray[21]! } : Vector3p.State)
      s := { s with statesArray := (((s.statesArray.set! 19 t'4.x).set! 20 t'4.y).set! 21 t'4.z) }
      s := { s with storedMag := EKF_obs_buffer_t_NavEKF3_core_mag_elements.reset s.storedMag }
      s := { s with needMagBodyVarReset := true }
    s := { s with lastMagOffsets := nowMagOffsets }
    s := { s with lastMagOffsetsValid := true }
    s := { s with lastMagUpdate_us := AP_DAL_Compass.last_update_usec w.heap'AP_DAL[(WPtr.index w.AP_DAL'_singleton)]!._compass s.magSelectIndex }
    let mut magDataNew : NavEKF3_core.mag_elements := {}
    magDataNew := { magDataNew with time_ms := s.imuSampleTime_ms - UInt16.toUInt32 w.EKF3.magDelay_ms }
    magDataNew := { magDataNew with time_ms := magDataNew.time_ms - Int32.toUInt32 (UInt32.toInt32 (UInt8.toUInt32 s.localFilterTimeStep_ms) / (2 : Int32)) }
    let t'5 := s.magSelectIndex
    let t'6 := (Vector3f.op_mul_float w.heap'AP_DAL[(WPtr.index w.AP_DAL'_singleton)]!._compass._RMGI[UInt8.toNat t'5]!.field (Binary32.ofBits 0x3a83126f /- 0.001f -/))
    magDataNew := { magDataNew with mag := Vector3f.todouble t'6 }
    s := { s with consistentMagData := AP_DAL_Compass.consistent w.heap'AP_DAL[(WPtr.index w.AP_DAL'_singleton)]!._compass }
    s := { s with storedMag := EKF_obs_buffer_t_NavEKF3_core_mag_elements.push_mag_elements s.storedMag magDataNew }
    s := { s with lastMagRead_ms := s.imuSampleTime_ms }
  return (s, o)

/-- C++ `void NavEKF3_core::calcEarthRateNED(Vector3F & omega, int32_t latitude) const`, `AP_NavEKF3/AP_NavEKF3_core.cpp:2071-2077`. -/
def calcEarthRateNED (omega : Vector3p.State) (latitude : Int32) : Vector3p.State := Id.run do
  let mut omega := omega
  let lat_rad : Binary64 := Binary32.toBinary64 (Estimator_lib.radians_float (Int32.toBinary32 latitude * (Binary32.ofBits 0x33d6bf95 /- 1.0e-7f -/)))
  omega := { omega with x := (Binary64.ofBits 0x3f131da540000000 /- (double)5011093/68719476736 -/) * Musl.cos.cos lat_rad }
  omega := { omega with y := (Binary64.ofBits 0x0000000000000000 /- 0 -/) }
  omega := { omega with z := (Binary64.ofBits 0xbf131da540000000 /- (double)-5011093/68719476736 -/) * Musl.sin.sin lat_rad }
  return omega

end NavEKF3_core

namespace NavEKF3_core

/-- C++ `ftype NavEKF3_core::MagDeclination() const`, `AP_NavEKF3/AP_NavEKF3_Measurements.cpp:1394-1406`. -/
def MagDeclination (s : State) (w : World) : Binary64 := Id.run do
  if s.have_table_earth_field && decide (Int16.toInt32 (AP_ParamT_short_2.op_to_short w.EKF3._mag_ef_limit) > (0 : Int32)) then
    return s.table_declination
  if !(use_compass s w) then
    return (Binary64.ofBits 0x0000000000000000 /- 0 -/)
  return Binary32.toBinary64 (AP_DAL_Compass.get_declination w.heap'AP_DAL[(WPtr.index w.AP_DAL'_singleton)]!._compass)

end NavEKF3_core

namespace NavEKF3_core

/-- C++ `void NavEKF3_core::ConstrainVariances()`, `AP_NavEKF3/AP_NavEKF3_core.cpp:1848-1962`. -/
def ConstrainVariances (s : State) (w : World) : State := Id.run do
  let mut s := s
  for i' in [0:4] do
    let i : UInt8 := Nat.toUInt8 i'
    s := { s with Pmut := s.Pmut.set! (UInt8.toNat i * 24 + UInt8.toNat i) (Estimator_lib.constrain_value_line_double s.Pmut[UInt8.toNat i * 24 + UInt8.toNat i]! (Binary64.ofBits 0x0000000000000000 /- (double)0 -/) (Binary64.ofBits 0x3ff0000000000000 /- (double)1 -/) (Int32.toUInt32 (1866 : Int32))) }
  for i'2' in [4:6] do
    let i'2 : UInt8 := Nat.toUInt8 i'2'
    s := { s with Pmut := s.Pmut.set! (UInt8.toNat i'2 * 24 + UInt8.toNat i'2) (Estimator_lib.constrain_value_line_double s.Pmut[UInt8.toNat i'2 * 24 + UInt8.toNat i'2]! (Binary64.ofBits 0x3f1a36e2eb1c432d /- (double)7378697629483821/73786976294838206464 -/) (Binary64.ofBits 0x408f400000000000 /- (double)1000 -/) (Int32.toUInt32 (1867 : Int32))) }
  if s.badIMUdata then
    s := { s with Pmut := s.Pmut.set! 150 (Binary64.fmax s.Pmut[150]! (Estimator_lib.sq_AP_ParamT_float_4 w.EKF3._gpsVertVelNoise)) }
    s := { s with Pmut := s.Pmut.set! 225 (Binary64.fmax s.Pmut[225]! (Estimator_lib.sq_AP_ParamT_float_4 w.EKF3._baroAltNoise)) }
  else if s.Pmut[150]! < (Binary64.ofBits 0x3f1a36e2eb1c432d /- (double)7378697629483821/73786976294838206464 -/) then
    s := { s with Pmut := s.Pmut.set! 150 (Binary64.ofBits 0x3f1a36e2eb1c432d /- (double)7378697629483821/73786976294838206464 -/) }
    s := { s with vertVelVarClipCounter := s.vertVelVarClipCounter + Binary32.toUInt32 ((Binary32.ofBits 0x3f800000 /- (float)1 -/) / (Binary32.ofBits 0x3c449ba6 /- 0.0120000001 -/)) }
    if s.vertVelVarClipCounter > (Int32.toUInt32 (5 : Int32) * Binary32.toUInt32 ((Binary32.ofBits 0x3f800000 /- (float)1 -/) / (Binary32.ofBits 0x3c449ba6 /- 0.0120000001 -/))) then
      s := zeroStatesVarCov s (Int8.toUInt8 (Int32.toInt8 (6 : Int32))) (Int8.toUInt8 (Int32.toInt8 (6 : Int32)))
      s := { s with Pmut := s.Pmut.set! 150 (Estimator_lib.sq_AP_ParamT_float_4 w.EKF3._gpsVertVelNoise) }
      s := { s with vertVelVarClipCounter := Int32.toUInt32 (0 : Int32) }
  for i'3' in [7:10] do
    let i'3 : UInt8 := Nat.toUInt8 i'3'
    s := { s with Pmut := s.Pmut.set! (UInt8.toNat i'3 * 24 + UInt8.toNat i'3) (Estimator_lib.constrain_value_line_double s.Pmut[UInt8.toNat i'3 * 24 + UInt8.toNat i'3]! (Binary64.ofBits 0x3f1a36e2eb1c432d /- (double)7378697629483821/73786976294838206464 -/) (Binary64.ofBits 0x412e848000000000 /- (double)1000000 -/) (Int32.toUInt32 (1897 : Int32))) }
  if !s.inhibitDelAngBiasStates then
    for i'4' in [10:13] do
      let i'4 : UInt8 := Nat.toUInt8 i'4'
      s := { s with Pmut := s.Pmut.set! (UInt8.toNat i'4 * 24 + UInt8.toNat i'4) (Estimator_lib.constrain_value_line_double s.Pmut[UInt8.toNat i'4 * 24 + UInt8.toNat i'4]! (Binary64.ofBits 0x0000000000000000 /- (double)0 -/) (Estimator_lib.sq_double ((Binary64.ofBits 0x3fc6666666666666 /- (double)3152519739159347/18014398509481984 -/) * s.dtEkfAvg)) (Int32.toUInt32 (1900 : Int32))) }
  else
    s := zeroStatesVarCov s (Int8.toUInt8 (Int32.toInt8 (10 : Int32))) (Int8.toUInt8 (Int32.toInt8 (12 : Int32)))
  let minSafeStateVar : Binary64 := (Binary64.ofBits 0x3e35798ee2308c3a /- 5E-9 -/)
  if !s.inhibitDelVelBiasStates then
    let mut maxStateVar : Binary64 := (Binary64.ofBits 0x0000000000000000 /- 0.0F -/)
    let mut resetRequired : Bool := false
    for stateIndex' in [13:16] do
      let stateIndex : UInt8 := Nat.toUInt8 stateIndex'
      if s.Pmut[UInt8.toNat stateIndex * 24 + UInt8.toNat stateIndex]! > maxStateVar then
        maxStateVar := s.Pmut[UInt8.toNat stateIndex * 24 + UInt8.toNat stateIndex]!
      else if s.Pmut[UInt8.toNat stateIndex * 24 + UInt8.toNat stateIndex]! < minSafeStateVar then
        resetRequired := true
    let minAllowedStateVar : Binary64 := Binary64.fmax ((Binary64.ofBits 0x3f847ae140000000 /- (double)5368709/536870912 -/) * maxStateVar) minSafeStateVar
    for stateIndex'2' in [13:16] do
      let stateIndex'2 : UInt8 := Nat.toUInt8 stateIndex'2'
      s := { s with Pmut := s.Pmut.set! (UInt8.toNat stateIndex'2 * 24 + UInt8.toNat stateIndex'2) (Estimator_lib.constrain_value_line_double s.Pmut[UInt8.toNat stateIndex'2 * 24 + UInt8.toNat stateIndex'2]! minAllowedStateVar (Estimator_lib.sq_double ((Binary64.ofBits 0x4024000000000000 /- (double)10 -/) * s.dtEkfAvg)) (Int32.toUInt32 (1923 : Int32))) }
    if resetRequired then
      s := zeroStatesVarCov s (Int8.toUInt8 (Int32.toInt8 (13 : Int32))) (Int8.toUInt8 (Int32.toInt8 (15 : Int32)))
      s := { s with Pmut := s.Pmut.set! 325 (Estimator_lib.sq_double (Binary32.toBinary64 ((Binary32.ofBits 0x3e4ccccd /- 0.200000003 -/) * AP_ParamT_float_4.op_to_float w.EKF3._accBiasLim) * s.dtEkfAvg)) }
      s := { s with Pmut := s.Pmut.set! 350 (s.Pmut[325]!) }
      s := { s with Pmut := s.Pmut.set! 375 (s.Pmut[325]!) }
      let t'1 := Vector3p.zero ({ x := s.statesArray[13]!, y := s.statesArray[14]!, z := s.statesArray[15]! } : Vector3p.State)
      s := { s with statesArray := (((s.statesArray.set! 13 t'1.x).set! 14 t'1.y).set! 15 t'1.z) }
  else
    s := zeroStatesVarCov s (Int8.toUInt8 (Int32.toInt8 (13 : Int32))) (Int8.toUInt8 (Int32.toInt8 (15 : Int32)))
    for i'5' in [0:3] do
      let i'5 : UInt8 := Nat.toUInt8 i'5'
      let stateIndex'3 : UInt8 := Int8.toUInt8 (Int32.toInt8 (UInt32.toInt32 (UInt8.toUInt32 i'5) + (13 : Int32)))
      s := { s with Pmut := s.Pmut.set! (UInt8.toNat stateIndex'3 * 24 + UInt8.toNat stateIndex'3) (Binary64.fmax s.Pmut[UInt8.toNat stateIndex'3 * 24 + UInt8.toNat stateIndex'3]! (minSafeStateVar * (Binary64.ofBits 0x4024000000000000 /- (double)10 -/))) }
  if !s.inhibitMagStates then
    for i'6' in [16:19] do
      let i'6 : UInt8 := Nat.toUInt8 i'6'
      s := { s with Pmut := s.Pmut.set! (UInt8.toNat i'6 * 24 + UInt8.toNat i'6) (Estimator_lib.constrain_value_line_double s.Pmut[UInt8.toNat i'6 * 24 + UInt8.toNat i'6]! (Binary64.ofBits 0x0000000000000000 /- (double)0 -/) (Binary64.ofBits 0x3f847ae140000000 /- (double)5368709/536870912 -/) (Int32.toUInt32 (1947 : Int32))) }
    for i'7' in [19:22] do
      let i'7 : UInt8 := Nat.toUInt8 i'7'
      s := { s with Pmut := s.Pmut.set! (UInt8.toNat i'7 * 24 + UInt8.toNat i'7) (Estimator_lib.constrain_value_line_double s.Pmut[UInt8.toNat i'7 * 24 + UInt8.toNat i'7]! (Binary64.ofBits 0x0000000000000000 /- (double)0 -/) (Binary64.ofBits 0x3f847ae140000000 /- (double)5368709/536870912 -/) (Int32.toUInt32 (1948 : Int32))) }
  else
    s := zeroStatesVarCov s (Int8.toUInt8 (Int32.toInt8 (16 : Int32))) (Int8.toUInt8 (Int32.toInt8 (21 : Int32)))
  if !s.inhibitWindStates then
    if s.treatWindStatesAsTruth then
      s := zeroStatesVarCov s (Int8.toUInt8 (Int32.toInt8 (22 : Int32))) (Int8.toUInt8 (Int32.toInt8 (23 : Int32)))
    else
      for i'8' in [22:24] do
        let i'8 : UInt8 := Nat.toUInt8 i'8'
        s := { s with Pmut := s.Pmut.set! (UInt8.toNat i'8 * 24 + UInt8.toNat i'8) (Estimator_lib.constrain_value_line_double s.Pmut[UInt8.toNat i'8 * 24 + UInt8.toNat i'8]! (Binary64.ofBits 0x0000000000000000 /- (double)0 -/) (Binary64.ofBits 0x4079000000000000 /- (double)400 -/) (Int32.toUInt32 (1957 : Int32))) }
  else
    s := zeroStatesVarCov s (Int8.toUInt8 (Int32.toInt8 (22 : Int32))) (Int8.toUInt8 (Int32.toInt8 (23 : Int32)))
  return s

/-- C++ `bool NavEKF3_core::FinishFusion(ftype innov, bool force)`, `AP_NavEKF3/AP_NavEKF3_core.cpp:1967-2001`. -/
def FinishFusion (s : State) (w : World) (innov : Binary64) (force : Bool := false) : State × Bool := Id.run do
  let mut s := s
  if !force then
    let t'1 : Int32 := (0 : Int32)
    let t'2 : Int32 := UInt32.toInt32 (UInt8.toUInt32 s.stateIndexLim)
    for s'' in [0:(t'2.toInt - t'1.toInt + 1).toNat] do  -- C++ loop bounded by a runtime value (--runtime-loops)
      let s' : Int32 := t'1 + Nat.toInt32 s''
      if w.NavEKF_core_common'KHP[Int32.toNatClampNeg s' * 24 + Int32.toNatClampNeg s']! > s.Pmut[Int32.toNatClampNeg s' * 24 + Int32.toNatClampNeg s']! then
        return (s, true)
  let t'3 : Int32 := (0 : Int32)
  let t'4 : Int32 := UInt32.toInt32 (UInt8.toUInt32 s.stateIndexLim)
  for s''2' in [0:(t'4.toInt - t'3.toInt + 1).toNat] do  -- C++ loop bounded by a runtime value (--runtime-loops)
    let s''2 : Int32 := t'3 + Nat.toInt32 s''2'
    s := { s with statesArray := s.statesArray.set! (Int32.toNatClampNeg s''2) (s.statesArray[Int32.toNatClampNeg s''2]! - w.NavEKF_core_common'Kfusion[Int32.toNatClampNeg s''2]! * innov) }
  let t'5 := QuaternionT_double.normalize ({ q1 := s.statesArray[0]!, q2 := s.statesArray[1]!, q3 := s.statesArray[2]!, q4 := s.statesArray[3]! } : QuaternionT_double.State)
  s := { s with statesArray := ((((s.statesArray.set! 0 t'5.q1).set! 1 t'5.q2).set! 2 t'5.q3).set! 3 t'5.q4) }
  let t'6 : Int32 := (0 : Int32)
  let t'7 : Int32 := UInt32.toInt32 (UInt8.toUInt32 s.stateIndexLim)
  for r' in [0:(t'7.toInt - t'6.toInt + 1).toNat] do  -- C++ loop bounded by a runtime value (--runtime-loops)
    let r : Int32 := t'6 + Nat.toInt32 r'
    let t'8 : Int32 := (0 : Int32)
    let t'9 : Int32 := r
    for c' in [0:(t'9.toInt - t'8.toInt + 1).toNat] do  -- C++ loop bounded by a runtime value (--runtime-loops)
      let c : Int32 := t'8 + Nat.toInt32 c'
      let diff : Binary64 := (Binary64.ofBits 0x3fe0000000000000 /- 0.5f -/) * (w.NavEKF_core_common'KHP[Int32.toNatClampNeg r * 24 + Int32.toNatClampNeg c]! + w.NavEKF_core_common'KHP[Int32.toNatClampNeg c * 24 + Int32.toNatClampNeg r]!)
      let res : Binary64 := s.Pmut[Int32.toNatClampNeg r * 24 + Int32.toNatClampNeg c]! - diff
      s := { s with Pmut := s.Pmut.set! (Int32.toNatClampNeg r * 24 + Int32.toNatClampNeg c) res }
      s := { s with Pmut := s.Pmut.set! (Int32.toNatClampNeg c * 24 + Int32.toNatClampNeg r) res }
  s := ConstrainVariances s w
  return (s, false)

/-- C++ `void NavEKF3_core::FuseDeclination(ftype declErr)`, `AP_NavEKF3/AP_NavEKF3_MagFusion.cpp:1268-1365`. -/
def FuseDeclination (s : State) (w : World) (declErr : Binary64) : State × World := Id.run do
  let mut s := s
  let mut w := w
  let R_DECL : Binary64 := Estimator_lib.sq_double declErr
  let magN : Binary64 := s.statesArray[16]!
  let magE : Binary64 := s.statesArray[17]!
  if magN < (Binary64.ofBits 0x3f50624de0000000 /- 1e-3f -/) then
    return (s, w)
  let HK0 : Binary64 := Estimator_lib.sq_double magE + Estimator_lib.sq_double magN
  if HK0 < (Binary64.ofBits 0x3f1a36e2e0000000 /- 1e-4f -/) then
    return (s, w)
  let HK1 : Binary64 := (Binary64.ofBits 0x3ff0000000000000 /- 1.0F -/) / HK0
  let HK2 : Binary64 := s.Pmut[400]! * magE - s.Pmut[401]! * magN
  let HK3 : Binary64 := s.Pmut[401]! * magE - s.Pmut[425]! * magN
  let HK4_denom : Binary64 := (Estimator_lib.sq_double HK0 * R_DECL + HK2 * magE - HK3 * magN)
  let mut HK4 : Binary64 := (Binary64.ofBits 0x0000000000000000 /- 0.0 -/)  -- uninitialized in C++; assigned before every read
  if Binary64.abs HK4_denom > (Binary64.ofBits 0x3eb0c6f7a0000000 /- 1e-6f -/) then
    HK4 := HK0 / HK4_denom
  else
    return (s, w)
  let mut Hfusion : Array Binary64 := Array.replicate 24 (Binary64.ofBits 0x0000000000000000 /- 0.0 -/)
  Hfusion := Hfusion.set! 16 (-HK1 * magE)
  Hfusion := Hfusion.set! 17 (HK1 * magN)
  let mut kalman_mask : UInt32 := Int32.toUInt32 (((1 : Int32) <<< (10 : Int32)) - (1 : Int32))
  if !s.inhibitDelAngBiasStates then
    kalman_mask := kalman_mask ||| Int32.toUInt32 (((1 : Int32) <<< (10 : Int32)) ||| ((1 : Int32) <<< (11 : Int32)) ||| ((1 : Int32) <<< (12 : Int32)))
  if !s.inhibitDelVelBiasStates then
    for index' in [0:3] do
      let index : UInt8 := Nat.toUInt8 index'
      let stateIndex : UInt8 := Int8.toUInt8 (Int32.toInt8 (UInt32.toInt32 (UInt8.toUInt32 index) + (13 : Int32)))
      if !s.dvelBiasAxisInhibit[UInt8.toNat index]! then
        kalman_mask := kalman_mask ||| Int32.toUInt32 ((1 : Int32) <<< UInt32.toInt32 (UInt8.toUInt32 stateIndex))
  if !s.inhibitMagStates then
    kalman_mask := kalman_mask ||| Int32.toUInt32 (((1 : Int32) <<< (16 : Int32)) ||| ((1 : Int32) <<< (17 : Int32)) ||| ((1 : Int32) <<< (18 : Int32)) ||| ((1 : Int32) <<< (19 : Int32)) ||| ((1 : Int32) <<< (20 : Int32)) ||| ((1 : Int32) <<< (21 : Int32)))
  if !s.inhibitWindStates && !s.treatWindStatesAsTruth then
    kalman_mask := kalman_mask ||| Int32.toUInt32 (((1 : Int32) <<< (22 : Int32)) ||| ((1 : Int32) <<< (23 : Int32)))
  for i' in [0:24] do
    let i : Int32 := Nat.toInt32 i'
    let mut res : Binary64 := (Binary64.ofBits 0x0000000000000000 /- 0 -/)
    if kalman_mask &&& Int32.toUInt32 ((1 : Int32) <<< i) != (0 : UInt32) then
      res := -HK4 * (s.Pmut[Int32.toNatClampNeg i * 24 + 16]! * magE - s.Pmut[Int32.toNatClampNeg i * 24 + 17]! * magN)
    w := { w with NavEKF_core_common'Kfusion := w.NavEKF_core_common'Kfusion.set! (Int32.toNatClampNeg i) res }
  let magDecAng : Binary64 := MagDeclination s w
  let mut innovation : Binary64 := Musl.atan2.atan2 magE magN - magDecAng
  if innovation > (Binary64.ofBits 0x3fe0000000000000 /- 0.5f -/) then
    innovation := (Binary64.ofBits 0x3fe0000000000000 /- 0.5f -/)
  else if innovation < (Binary64.ofBits 0xbfe0000000000000 /- -0.5f -/) then
    innovation := (Binary64.ofBits 0xbfe0000000000000 /- -0.5f -/)
  let t'1 : UInt32 := Int32.toUInt32 (0 : Int32)
  let t'2 : UInt32 := UInt8.toUInt32 s.stateIndexLim
  for i'2' in [0:((Int.ofNat t'2.toNat) - (Int.ofNat t'1.toNat) + 1).toNat] do  -- C++ loop bounded by a runtime value (--runtime-loops)
    let i'2 : UInt32 := t'1 + Nat.toUInt32 i'2'
    let t'3 : UInt32 := Int32.toUInt32 (0 : Int32)
    let t'4 : UInt32 := UInt8.toUInt32 s.stateIndexLim
    for j' in [0:((Int.ofNat t'4.toNat) - (Int.ofNat t'3.toNat) + 1).toNat] do  -- C++ loop bounded by a runtime value (--runtime-loops)
      let j : UInt32 := t'3 + Nat.toUInt32 j'
      let mut res'2 : Binary64 := (Binary64.ofBits 0x0000000000000000 /- 0 -/)
      res'2 := res'2 + (w.NavEKF_core_common'Kfusion[UInt32.toNat i'2]! * Hfusion[16]!) * s.Pmut[384 + UInt32.toNat j]!
      res'2 := res'2 + (w.NavEKF_core_common'Kfusion[UInt32.toNat i'2]! * Hfusion[17]!) * s.Pmut[408 + UInt32.toNat j]!
      w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! (UInt32.toNat i'2 * 24 + UInt32.toNat j) res'2 }
  let (t'5, t'6) := FinishFusion s w innovation false
  s := t'5
  s := { s with faultStatus.bad_decl := t'6 }
  return (s, w)

/-- C++ `void NavEKF3_core::alignMagStateDeclination()`, `AP_NavEKF3/AP_NavEKF3_MagFusion.cpp:1372-1401`. -/
def alignMagStateDeclination (s : State) (w : World) : State × World := Id.run do
  let mut s := s
  let mut w := w
  if s.magFieldLearned then
    return (s, w)
  let magDecAng : Binary64 := MagDeclination s w
  let mut initMagNED : Vector3p.State := ({ x := s.statesArray[16]!, y := s.statesArray[17]!, z := s.statesArray[18]! } : Vector3p.State)
  let magLengthNE : Binary64 := Vector2p.length (Vector3p.xy initMagNED)
  s := { s with statesArray := s.statesArray.set! 16 (magLengthNE * Musl.cos.cos magDecAng) }
  s := { s with statesArray := s.statesArray.set! 17 (magLengthNE * Musl.sin.sin magDecAng) }
  if !s.inhibitMagStates then
    let var_16 : Binary64 := s.Pmut[400]!
    let var_17 : Binary64 := s.Pmut[425]!
    s := zeroStatesVarCov s (Int8.toUInt8 (Int32.toInt8 (16 : Int32))) (Int8.toUInt8 (Int32.toInt8 (17 : Int32)))
    s := { s with Pmut := s.Pmut.set! 400 var_16 }
    s := { s with Pmut := s.Pmut.set! 425 var_17 }
    let (t'1, t'2) := FuseDeclination s w (Binary64.ofBits 0x3fb99999a0000000 /- 0.1f -/)
    w := t'2
    s := t'1
  return (s, w)

end NavEKF3_core

namespace NavEKF3_core

/-- C++ `void NavEKF3_core::getEarthFieldTable(const Location & loc)`, `AP_NavEKF3/AP_NavEKF3_Measurements.cpp:1545-1551`. -/
def getEarthFieldTable (s : State) (loc : Location.State) : State := Id.run do
  let mut s := s
  s := { s with table_earth_field_ga := Vector3f.todouble (AP_Declination.get_earth_field_ga loc) }
  s := { s with table_declination := Binary32.toBinary64 (Estimator_lib.radians_float (AP_Declination.get_declination (Int32.toBinary32 loc.lat * (Binary32.ofBits 0x33d6bf95 /- 1.0e-7 -/)) (Int32.toBinary32 loc.lng * (Binary32.ofBits 0x33d6bf95 /- 1.0e-7 -/)))) }
  s := { s with have_table_earth_field := true }
  return s

/-- C++ `void NavEKF3_core::setEarthFieldFromLocation(const Location & loc)`, `AP_NavEKF3/AP_NavEKF3_Control.cpp:707-718`. -/
def setEarthFieldFromLocation (s : State) (w : World) (loc : Location.State) : State := Id.run do
  let mut s := s
  if AP_DAL_Compass.have_scale_factor w.heap'AP_DAL[(WPtr.index w.AP_DAL'_singleton)]!._compass s.magSelectIndex && AP_DAL_Compass.auto_declination_enabled w.heap'AP_DAL[(WPtr.index w.AP_DAL'_singleton)]!._compass then
    s := getEarthFieldTable s loc
    if Int16.toInt32 (AP_ParamT_short_2.op_to_short w.EKF3._mag_ef_limit) > (0 : Int32) then
      s := { s with statesArray := (((s.statesArray.set! 16 s.table_earth_field_ga.x).set! 17 s.table_earth_field_ga.y).set! 18 s.table_earth_field_ga.z) }
  return s

/-- C++ `bool NavEKF3_core::setOriginLLH(const Location & loc)`, `AP_NavEKF3/AP_NavEKF3_Control.cpp:722-751`. -/
def setOriginLLH (s : State) (w : World) (o : Outputs) (loc : Location.State) : State × World × Outputs × Bool := Id.run do
  let mut s := s
  let mut w := w
  let mut o := o
  if s.validOrigin then
    return (s, w, o, false)
  s := { s with EKF_origin := loc }
  s := { s with ekfGpsRefHgt := (Binary64.ofBits 0x3f847ae147ae147b /- 0.01 -/) * Int32.toBinary64 s.EKF_origin.alt }
  s := { s with earthRateNED := calcEarthRateNED s.earthRateNED s.EKF_origin.lat }
  s := { s with validOrigin := true }
  if !(QuaternionT_double.is_zero ({ q1 := s.statesArray[0]!, q2 := s.statesArray[1]!, q3 := s.statesArray[2]!, q4 := s.statesArray[3]! } : QuaternionT_double.State)) then
    let (t'1, t'2) := alignMagStateDeclination s w
    w := t'2
    s := t'1
    s := setEarthFieldFromLocation s w s.EKF_origin
  o := o.push (Output.send_text (6 : UInt32) "EKF3 IMU%u origin set" #[Sum.inl (UInt32.toUInt64 (UInt8.toUInt32 s.imu_index))])
  if !w.EKF3.common_origin_valid then
    w := { w with EKF3.common_origin_valid := true }
    w := { w with EKF3.common_EKF_origin := s.EKF_origin }
  return (s, w, o, true)

end NavEKF3_core

namespace NavEKF3_core

/-- C++ `void NavEKF3_core::calcGpsGoodToAlign()`, `AP_NavEKF3/AP_NavEKF3_VehicleStatus.cpp:14-238`. -/
def calcGpsGoodToAlign (s : State) (w : World) : State := Id.run do
  let mut s := s
  if s.inFlight && !s.finalInflightYawInit && assume_zero_sideslip w && !(use_compass s w) then
    s := { s with gpsGoodToAlign := true }
    return s
  let mut checkScaler : Binary64 := (Binary64.ofBits 0x3f847ae140000000 /- 0.01f -/) * Int16.toBinary64 (AP_ParamT_short_2.op_to_short w.EKF3._gpsCheckScaler)
  if s.gpsGoodToAlign then
    checkScaler := checkScaler * (Binary64.ofBits 0x3ff4ccccc0000000 /- 1.3f -/)
  if (decide (s.magTestRatio.x ≤ (Binary64.ofBits 0x3ff0000000000000 /- 1.0f -/)) && decide (s.magTestRatio.y ≤ (Binary64.ofBits 0x3ff0000000000000 /- 1.0f -/)) && decide (s.yawTestRatio ≤ (Binary64.ofBits 0x3ff0000000000000 /- 1.0f -/))) || !s.consistentMagData then
    s := { s with magYawResetTimer_ms := s.imuSampleTime_ms }
  if (decide (s.imuSampleTime_ms - s.magYawResetTimer_ms > Int32.toUInt32 (5000 : Int32))) && !s.motorsArmed then
    s := { s with magYawResetRequest := true }
    s := { s with magYawResetTimer_ms := s.imuSampleTime_ms }
  let t'1 := s.preferred_gps
  let posFiltTimeConst : Binary64 := (Binary64.ofBits 0x4024000000000000 /- 10.0 -/)
  let deltaTime : Binary64 := Estimator_lib.constrain_value_line_double (UInt32.toBinary64 (s.imuDataDelayed.time_ms - s.lastPreAlignGpsCheckTime_ms) * (Binary64.ofBits 0x3f50624de0000000 /- (double)8589935/8589934592 -/)) (Binary64.ofBits 0x3f847ae140000000 /- (double)5368709/536870912 -/) posFiltTimeConst (Int32.toUInt32 (55 : Int32))
  s := { s with lastPreAlignGpsCheckTime_ms := s.imuDataDelayed.time_ms }
  s := { s with gpsDriftNE := s.gpsDriftNE + Location.get_distance s.gpsloc_prev w.heap'AP_DAL[(WPtr.index w.AP_DAL'_singleton)]!._gps.tmp_location[UInt8.toNat t'1]! }
  s := { s with gpsloc_prev := w.heap'AP_DAL[(WPtr.index w.AP_DAL'_singleton)]!._gps.tmp_location[UInt8.toNat t'1]! }
  s := { s with gpsDriftNE := s.gpsDriftNE * ((Binary64.ofBits 0x3ff0000000000000 /- 1.0f -/) - deltaTime / posFiltTimeConst) }
  s := { s with gpsDriftNE := Estimator_lib.MIN_double_float s.gpsDriftNE (Binary32.ofBits 0x41200000 /- 10.0f -/) }
  let gpsDriftFail : Bool := (decide (s.gpsDriftNE > (Binary64.ofBits 0x4008000000000000 /- 3.0f -/) * checkScaler)) && s.onGround && (UInt32.toInt32 (UInt8.toUInt32 (AP_ParamT_unsigned_char_1.op_to_unsigned_char w.EKF3._gpsCheck)) &&& ((1 : Int32) <<< (5 : Int32))) != (0 : Int32)
  if gpsDriftFail then
    s := { s with prearm_fail_string := (CText.fmt (40 : UInt64) "GPS drift %.1fm (needs %.1f)" #[Sum.inl (Binary64.toBits s.gpsDriftNE), Sum.inl (Binary64.toBits ((Binary64.ofBits 0x4008000000000000 /- 3.0f -/) * checkScaler))]) }
    s := { s with gpsCheckStatus := (s.gpsCheckStatus &&& ~~~((1 : UInt16) <<< 6)) ||| (if true then (1 : UInt16) <<< 6 else 0) }
  else
    s := { s with gpsCheckStatus := (s.gpsCheckStatus &&& ~~~((1 : UInt16) <<< 6)) ||| (if false then (1 : UInt16) <<< 6 else 0) }
  let mut gpsVertVelFail : Bool := false  -- uninitialized in C++; assigned before every read
  if s.gpsDataNew.have_vz && s.onGround then
    s := { s with gpsVertVelFilt := (Binary64.ofBits 0x3fb99999a0000000 /- 0.1f -/) * s.gpsDataNew.vel.z + (Binary64.ofBits 0x3fecccccc0000000 /- 0.9f -/) * s.gpsVertVelFilt }
    s := { s with gpsVertVelFilt := Estimator_lib.constrain_value_line_double s.gpsVertVelFilt (Binary64.ofBits 0xc024000000000000 /- (double)-10 -/) (Binary64.ofBits 0x4024000000000000 /- (double)10 -/) (Int32.toUInt32 (83 : Int32)) }
    gpsVertVelFail := (decide (Binary64.abs s.gpsVertVelFilt > (Binary64.ofBits 0x3fd3333340000000 /- 0.3f -/) * checkScaler)) && (UInt32.toInt32 (UInt8.toUInt32 (AP_ParamT_unsigned_char_1.op_to_unsigned_char w.EKF3._gpsCheck)) &&& ((1 : Int32) <<< (6 : Int32))) != (0 : Int32)
  else
    gpsVertVelFail := false
  if gpsVertVelFail then
    s := { s with prearm_fail_string := (CText.fmt (40 : UInt64) "GPS vertical speed %.2fm/s (needs %.2f)" #[Sum.inl (Binary64.toBits (Binary64.abs s.gpsVertVelFilt)), Sum.inl (Binary64.toBits ((Binary64.ofBits 0x3fd3333340000000 /- 0.3f -/) * checkScaler))]) }
    s := { s with gpsCheckStatus := (s.gpsCheckStatus &&& ~~~((1 : UInt16) <<< 8)) ||| (if true then (1 : UInt16) <<< 8 else 0) }
  else
    s := { s with gpsCheckStatus := (s.gpsCheckStatus &&& ~~~((1 : UInt16) <<< 8)) ||| (if false then (1 : UInt16) <<< 8 else 0) }
  let mut gpsHorizVelFail : Bool := false  -- uninitialized in C++; assigned before every read
  if s.onGround then
    s := { s with gpsHorizVelFilt := (Binary64.ofBits 0x3fb99999a0000000 /- 0.1f -/) * Vector2p.length ({ x := s.gpsDataDelayed.vel.x, y := s.gpsDataDelayed.vel.y } : Vector2p.State) + (Binary64.ofBits 0x3fecccccc0000000 /- 0.9f -/) * s.gpsHorizVelFilt }
    s := { s with gpsHorizVelFilt := Estimator_lib.constrain_value_line_double s.gpsHorizVelFilt (Binary64.ofBits 0xc024000000000000 /- (double)-10 -/) (Binary64.ofBits 0x4024000000000000 /- (double)10 -/) (Int32.toUInt32 (104 : Int32)) }
    gpsHorizVelFail := (decide (Binary64.abs s.gpsHorizVelFilt > (Binary64.ofBits 0x3fd3333340000000 /- 0.3f -/) * checkScaler)) && (UInt32.toInt32 (UInt8.toUInt32 (AP_ParamT_unsigned_char_1.op_to_unsigned_char w.EKF3._gpsCheck)) &&& ((1 : Int32) <<< (7 : Int32))) != (0 : Int32)
  else
    gpsHorizVelFail := false
  if gpsHorizVelFail then
    s := { s with prearm_fail_string := (CText.fmt (40 : UInt64) "GPS horizontal speed %.2fm/s (needs %.2f)" #[Sum.inl (Binary64.toBits s.gpsDriftNE), Sum.inl (Binary64.toBits ((Binary64.ofBits 0x3fd3333340000000 /- 0.3f -/) * checkScaler))]) }
    s := { s with gpsCheckStatus := (s.gpsCheckStatus &&& ~~~((1 : UInt16) <<< 10)) ||| (if true then (1 : UInt16) <<< 10 else 0) }
  else
    s := { s with gpsCheckStatus := (s.gpsCheckStatus &&& ~~~((1 : UInt16) <<< 10)) ||| (if false then (1 : UInt16) <<< 10 else 0) }
  let mut hAcc : Binary32 := (Binary32.ofBits 0x00000000 /- 0.0f -/)
  let mut hAccFail : Bool := false  -- uninitialized in C++; assigned before every read
  let (t'2, t'3) := AP_DAL_GPS.horizontal_accuracy_uint8_t_float w.heap'AP_DAL[(WPtr.index w.AP_DAL'_singleton)]!._gps s.preferred_gps hAcc
  hAcc := t'2
  if t'3 then
    hAccFail := (decide (Binary32.toBinary64 hAcc > (Binary64.ofBits 0x4014000000000000 /- 5.0f -/) * checkScaler)) && (UInt32.toInt32 (UInt8.toUInt32 (AP_ParamT_unsigned_char_1.op_to_unsigned_char w.EKF3._gpsCheck)) &&& ((1 : Int32) <<< (3 : Int32))) != (0 : Int32)
  else
    hAccFail := false
  if hAccFail then
    s := { s with prearm_fail_string := (CText.fmt (40 : UInt64) "GPS horiz error %.1fm (needs %.1f)" #[Sum.inl (Binary64.toBits (Binary32.toBinary64 hAcc)), Sum.inl (Binary64.toBits ((Binary64.ofBits 0x4014000000000000 /- 5.0f -/) * checkScaler))]) }
    s := { s with gpsCheckStatus := (s.gpsCheckStatus &&& ~~~((1 : UInt16) <<< 1)) ||| (if true then (1 : UInt16) <<< 1 else 0) }
  else
    s := { s with gpsCheckStatus := (s.gpsCheckStatus &&& ~~~((1 : UInt16) <<< 1)) ||| (if false then (1 : UInt16) <<< 1 else 0) }
  let mut vAcc : Binary32 := (Binary32.ofBits 0x00000000 /- 0.0f -/)
  let mut vAccFail : Bool := false
  let (t'4, t'5) := AP_DAL_GPS.vertical_accuracy_uint8_t_float w.heap'AP_DAL[(WPtr.index w.AP_DAL'_singleton)]!._gps s.preferred_gps vAcc
  vAcc := t'4
  if t'5 then
    vAccFail := (decide (Binary32.toBinary64 vAcc > (Binary64.ofBits 0x401e000000000000 /- 7.5f -/) * checkScaler)) && (UInt32.toInt32 (UInt8.toUInt32 (AP_ParamT_unsigned_char_1.op_to_unsigned_char w.EKF3._gpsCheck)) &&& ((1 : Int32) <<< (3 : Int32))) != (0 : Int32)
  if vAccFail then
    s := { s with prearm_fail_string := (CText.fmt (40 : UInt64) "GPS vert error %.1fm (needs < %.1f)" #[Sum.inl (Binary64.toBits (Binary32.toBinary64 vAcc)), Sum.inl (Binary64.toBits ((Binary64.ofBits 0x401e000000000000 /- 7.5f -/) * checkScaler))]) }
    s := { s with gpsCheckStatus := (s.gpsCheckStatus &&& ~~~((1 : UInt16) <<< 2)) ||| (if true then (1 : UInt16) <<< 2 else 0) }
  else
    s := { s with gpsCheckStatus := (s.gpsCheckStatus &&& ~~~((1 : UInt16) <<< 2)) ||| (if false then (1 : UInt16) <<< 2 else 0) }
  let gpsSpdAccFail : Bool := (decide (s.gpsSpdAccuracy > (Binary64.ofBits 0x3ff0000000000000 /- 1.0f -/) * checkScaler)) && (UInt32.toInt32 (UInt8.toUInt32 (AP_ParamT_unsigned_char_1.op_to_unsigned_char w.EKF3._gpsCheck)) &&& ((1 : Int32) <<< (2 : Int32))) != (0 : Int32)
  if gpsSpdAccFail then
    s := { s with prearm_fail_string := (CText.fmt (40 : UInt64) "GPS speed error %.1f (needs < %.1f)" #[Sum.inl (Binary64.toBits s.gpsSpdAccuracy), Sum.inl (Binary64.toBits ((Binary64.ofBits 0x3ff0000000000000 /- 1.0f -/) * checkScaler))]) }
    s := { s with gpsCheckStatus := (s.gpsCheckStatus &&& ~~~((1 : UInt16) <<< 0)) ||| (if true then (1 : UInt16) <<< 0 else 0) }
  else
    s := { s with gpsCheckStatus := (s.gpsCheckStatus &&& ~~~((1 : UInt16) <<< 0)) ||| (if false then (1 : UInt16) <<< 0 else 0) }
  let hdopFail : Bool := (decide (UInt32.toInt32 (UInt16.toUInt32 (AP_DAL_GPS.get_hdop_uint8_t w.heap'AP_DAL[(WPtr.index w.AP_DAL'_singleton)]!._gps s.preferred_gps)) > (250 : Int32))) && (UInt32.toInt32 (UInt8.toUInt32 (AP_ParamT_unsigned_char_1.op_to_unsigned_char w.EKF3._gpsCheck)) &&& ((1 : Int32) <<< (1 : Int32))) != (0 : Int32)
  if hdopFail then
    s := { s with prearm_fail_string := (CText.fmt (40 : UInt64) "GPS HDOP %.1f (needs 2.5)" #[Sum.inl (Binary64.toBits (Binary32.toBinary64 ((Binary32.ofBits 0x3c23d70a /- 0.01f -/) * Int32.toBinary32 (UInt32.toInt32 (UInt16.toUInt32 (AP_DAL_GPS.get_hdop_uint8_t w.heap'AP_DAL[(WPtr.index w.AP_DAL'_singleton)]!._gps s.preferred_gps))))))]) }
    s := { s with gpsCheckStatus := (s.gpsCheckStatus &&& ~~~((1 : UInt16) <<< 7)) ||| (if true then (1 : UInt16) <<< 7 else 0) }
  else
    s := { s with gpsCheckStatus := (s.gpsCheckStatus &&& ~~~((1 : UInt16) <<< 7)) ||| (if false then (1 : UInt16) <<< 7 else 0) }
  let numSatsFail : Bool := (decide (UInt32.toInt32 (UInt8.toUInt32 (AP_DAL_GPS.num_sats_uint8_t w.heap'AP_DAL[(WPtr.index w.AP_DAL'_singleton)]!._gps s.preferred_gps)) < (6 : Int32))) && (UInt32.toInt32 (UInt8.toUInt32 (AP_ParamT_unsigned_char_1.op_to_unsigned_char w.EKF3._gpsCheck)) &&& ((1 : Int32) <<< (0 : Int32))) != (0 : Int32)
  if numSatsFail then
    s := { s with prearm_fail_string := (CText.fmt (40 : UInt64) "GPS numsats %u (needs 6)" #[Sum.inl (Int64.toUInt64 (Int32.toInt64 (UInt32.toInt32 (UInt8.toUInt32 (AP_DAL_GPS.num_sats_uint8_t w.heap'AP_DAL[(WPtr.index w.AP_DAL'_singleton)]!._gps s.preferred_gps)))))]) }
    s := { s with gpsCheckStatus := (s.gpsCheckStatus &&& ~~~((1 : UInt16) <<< 4)) ||| (if true then (1 : UInt16) <<< 4 else 0) }
  else
    s := { s with gpsCheckStatus := (s.gpsCheckStatus &&& ~~~((1 : UInt16) <<< 4)) ||| (if false then (1 : UInt16) <<< 4 else 0) }
  let mut yawFail : Bool := false  -- uninitialized in C++; assigned before every read
  if (decide (s.magTestRatio.x > (Binary64.ofBits 0x3ff0000000000000 /- 1.0f -/)) || decide (s.magTestRatio.y > (Binary64.ofBits 0x3ff0000000000000 /- 1.0f -/)) || decide (s.yawTestRatio > (Binary64.ofBits 0x3ff0000000000000 /- 1.0f -/))) && (UInt32.toInt32 (UInt8.toUInt32 (AP_ParamT_unsigned_char_1.op_to_unsigned_char w.EKF3._gpsCheck)) &&& ((1 : Int32) <<< (4 : Int32))) != (0 : Int32) then
    yawFail := true
  else
    yawFail := false
  if yawFail then
    s := { s with prearm_fail_string := (CText.fmt (40 : UInt64) "Mag yaw error x=%.1f y=%.1f" #[Sum.inl (Binary64.toBits s.magTestRatio.x), Sum.inl (Binary64.toBits s.magTestRatio.y)]) }
    s := { s with gpsCheckStatus := (s.gpsCheckStatus &&& ~~~((1 : UInt16) <<< 3)) ||| (if true then (1 : UInt16) <<< 3 else 0) }
  else
    s := { s with gpsCheckStatus := (s.gpsCheckStatus &&& ~~~((1 : UInt16) <<< 3)) ||| (if false then (1 : UInt16) <<< 3 else 0) }
  if s.lastGpsVelFail_ms == Int32.toUInt32 (0 : Int32) then
    s := { s with prearm_fail_string := (CText.fmt (40 : UInt64) "EKF starting GPS checks" #[]) }
    s := { s with lastGpsVelFail_ms := s.imuSampleTime_ms }
  if gpsSpdAccFail || numSatsFail || hdopFail || hAccFail || vAccFail || yawFail || gpsDriftFail || gpsVertVelFail || gpsHorizVelFail then
    s := { s with lastGpsVelFail_ms := s.imuSampleTime_ms }
  else
    s := { s with lastGpsVelPass_ms := s.imuSampleTime_ms }
  if !s.gpsGoodToAlign && decide (s.imuSampleTime_ms - s.lastGpsVelFail_ms > Int32.toUInt32 (10000 : Int32)) then
    s := { s with gpsGoodToAlign := true }
  else if s.gpsGoodToAlign && decide (s.imuSampleTime_ms - s.lastGpsVelPass_ms > Int32.toUInt32 (5000 : Int32)) then
    s := { s with gpsGoodToAlign := false }
  if s.gpsGoodToAlign && s.waitingForGpsChecks then
    s := { s with waitingForGpsChecks := false }
  return s

/-- C++ `void NavEKF3_core::calcGpsGoodForFlight()`, `AP_NavEKF3/AP_NavEKF3_VehicleStatus.cpp:241-321`. -/
def calcGpsGoodForFlight (s : State) (w : World) : State := Id.run do
  let mut s := s
  let alpha1 : Binary64 := (Binary64.ofBits 0x3fc99999a0000000 /- 0.2f -/)
  let tau : Binary64 := (Binary64.ofBits 0x4024000000000000 /- 10.0f -/)
  if s.lastGpsCheckTime_ms == Int32.toUInt32 (0 : Int32) then
    s := { s with lastGpsCheckTime_ms := s.imuSampleTime_ms }
  let dtLPF : Binary64 := Binary32.toBinary64 (UInt32.toBinary32 (s.imuSampleTime_ms - s.lastGpsCheckTime_ms) * (Binary32.ofBits 0x3a83126f /- 1e-3f -/))
  s := { s with lastGpsCheckTime_ms := s.imuSampleTime_ms }
  let alpha2 : Binary64 := Estimator_lib.constrain_value_line_double (dtLPF / tau) (Binary64.ofBits 0x0000000000000000 /- (double)0 -/) (Binary64.ofBits 0x3ff0000000000000 /- (double)1 -/) (Int32.toUInt32 (255 : Int32))
  let mut gpsSpdAccRaw : Binary32 := (Binary32.ofBits 0x00000000 /- 0.0 -/)  -- uninitialized in C++; assigned before every read
  let (t'1, t'2) := AP_DAL_GPS.speed_accuracy_uint8_t_float w.heap'AP_DAL[(WPtr.index w.AP_DAL'_singleton)]!._gps s.preferred_gps gpsSpdAccRaw
  gpsSpdAccRaw := t'1
  if !t'2 then
    gpsSpdAccRaw := (Binary32.ofBits 0x00000000 /- 0.0f -/)
  s := { s with sAccFilterState1 := Estimator_lib.constrain_value_line_double (alpha1 * Binary32.toBinary64 gpsSpdAccRaw + ((Binary64.ofBits 0x3ff0000000000000 /- (double)1 -/) - alpha1) * s.sAccFilterState1) (Binary64.ofBits 0x0000000000000000 /- (double)0 -/) (Binary64.ofBits 0x4024000000000000 /- (double)10 -/) (Int32.toUInt32 (264 : Int32)) }
  s := { s with sAccFilterState2 := Estimator_lib.MAX_double2 s.sAccFilterState1 (((Binary64.ofBits 0x3ff0000000000000 /- 1.0f -/) - alpha2) * s.sAccFilterState2) }
  if s.sAccFilterState2 > (Binary64.ofBits 0x3ff8000000000000 /- 1.5f -/) then
    s := { s with gpsSpdAccPass := false }
  else if s.sAccFilterState2 < (Binary64.ofBits 0x3ff0000000000000 /- 1.0f -/) then
    s := { s with gpsSpdAccPass := true }
  let mut gpsVAccRaw : Binary32 := (Binary32.ofBits 0x00000000 /- 0.0 -/)  -- uninitialized in C++; assigned before every read
  let gpsVAccThreshold : Binary64 := AP_ParamT_float_4.op_to_double w.EKF3._gpsVAccThreshold
  if s.lastGpsVertAccFailTime_ms == Int32.toUInt32 (0 : Int32) then
    s := { s with lastGpsVertAccFailTime_ms := s.imuSampleTime_ms }
    s := { s with lastGpsVertAccPassTime_ms := s.imuSampleTime_ms }
  let (t'3, t'4) := AP_DAL_GPS.vertical_accuracy_uint8_t_float w.heap'AP_DAL[(WPtr.index w.AP_DAL'_singleton)]!._gps s.preferred_gps gpsVAccRaw
  gpsVAccRaw := t'3
  if !t'4 then
    gpsVAccRaw := Binary64.toBinary32 (gpsVAccThreshold + (Binary64.ofBits 0x3ff0000000000000 /- 1.0f -/))
  if decide (gpsVAccThreshold ≤ (Binary64.ofBits 0x0000000000000000 /- 0 -/)) || decide (Binary32.toBinary64 gpsVAccRaw < gpsVAccThreshold) then
    s := { s with lastGpsVertAccPassTime_ms := s.imuSampleTime_ms }
  else
    s := { s with lastGpsVertAccFailTime_ms := s.imuSampleTime_ms }
  if (s.imuSampleTime_ms - s.lastGpsVertAccPassTime_ms) > Int32.toUInt32 (1000 : Int32) then
    s := { s with gpsVertAccPass := false }
  else if (s.imuSampleTime_ms - s.lastGpsVertAccFailTime_ms) > Int32.toUInt32 (3000 : Int32) then
    s := { s with gpsVertAccPass := true }
  if s.lastGpsInnovFailTime_ms == Int32.toUInt32 (0 : Int32) then
    s := { s with lastGpsInnovFailTime_ms := s.imuSampleTime_ms }
    s := { s with lastGpsInnovPassTime_ms := s.imuSampleTime_ms }
  if decide (s.velTestRatio < (Binary64.ofBits 0x3ff0000000000000 /- 1.0f -/)) && decide (s.posTestRatio < (Binary64.ofBits 0x3ff0000000000000 /- 1.0f -/)) then
    s := { s with lastGpsInnovPassTime_ms := s.imuSampleTime_ms }
  else if decide (s.velTestRatio > (Binary64.ofBits 0x3fe6666660000000 /- 0.7f -/)) || decide (s.posTestRatio > (Binary64.ofBits 0x3fe6666660000000 /- 0.7f -/)) then
    s := { s with lastGpsInnovFailTime_ms := s.imuSampleTime_ms }
  if (s.imuSampleTime_ms - s.lastGpsInnovPassTime_ms) > Int32.toUInt32 (1000 : Int32) then
    s := { s with ekfInnovationsPass := false }
  else if (s.imuSampleTime_ms - s.lastGpsInnovFailTime_ms) > Int32.toUInt32 (10000 : Int32) then
    s := { s with ekfInnovationsPass := true }
  s := { s with gpsAccuracyGood := s.gpsSpdAccPass && s.ekfInnovationsPass }
  s := { s with gpsAccuracyGoodForAltitude := s.gpsAccuracyGood && s.gpsVertAccPass }
  return s

/-- C++ `void NavEKF3_core::readGpsData()`, `AP_NavEKF3/AP_NavEKF3_Measurements.cpp:562-734`. -/
def readGpsData (s : State) (w : World) (o : Outputs) : State × World × Outputs := Id.run do
  let mut s := s
  let mut w := w
  let mut o := o
  if AP_DAL_GPS.last_message_time_ms w.heap'AP_DAL[(WPtr.index w.AP_DAL'_singleton)]!._gps s.selected_gps - s.lastTimeGpsReceived_ms ≤ UInt8.toUInt32 w.EKF3.sensorIntervalMin_ms then
    return (s, w, o)
  if AP_GPS_FixType.toInt (AP_DAL_GPS.status_uint8_t w.heap'AP_DAL[(WPtr.index w.AP_DAL'_singleton)]!._gps s.selected_gps) < AP_GPS_FixType.toInt AP_GPS_FixType.FIX_3D then
    s := { s with gpsCheckStatus := (s.gpsCheckStatus &&& ~~~((1 : UInt16) <<< 9)) ||| (if true then (1 : UInt16) <<< 9 else 0) }
    s := { s with prearm_fail_string := (CText.fmt (40 : UInt64) "Waiting for 3D fix" #[]) }
    return (s, w, o)
  s := { s with gpsCheckStatus := (s.gpsCheckStatus &&& ~~~((1 : UInt16) <<< 9)) ||| (if false then (1 : UInt16) <<< 9 else 0) }
  let secondLastGpsTime_ms : UInt32 := s.lastTimeGpsReceived_ms
  s := { s with lastTimeGpsReceived_ms := AP_DAL_GPS.last_message_time_ms w.heap'AP_DAL[(WPtr.index w.AP_DAL'_singleton)]!._gps s.selected_gps }
  let mut gps_delay_sec : Binary32 := (Binary32.ofBits 0x00000000 /- 0 -/)
  let (t'1, _) := AP_DAL_GPS.get_lag_uint8_t_float w.heap'AP_DAL[(WPtr.index w.AP_DAL'_singleton)]!._gps s.selected_gps gps_delay_sec
  gps_delay_sec := t'1
  s := { s with gpsDataNew.time_ms := s.lastTimeGpsReceived_ms - Binary32.toUInt32 (gps_delay_sec * (Binary32.ofBits 0x447a0000 /- 1000.0f -/)) }
  s := { s with gpsDataNew.time_ms := s.gpsDataNew.time_ms - Int32.toUInt32 (UInt32.toInt32 (UInt8.toUInt32 s.localFilterTimeStep_ms) / (2 : Int32)) }
  s := { s with gpsDataNew.time_ms := Estimator_lib.MIN_uint32_t2 (Estimator_lib.MAX_uint32_t2 s.gpsDataNew.time_ms s.imuDataDelayed.time_ms) s.imuDataDownSampledNew.time_ms }
  s := { s with gpsDataNew.sensor_idx := s.selected_gps }
  let t'3 := s.selected_gps
  s := { s with gpsDataNew.vel := Vector3f.todouble w.heap'AP_DAL[(WPtr.index w.AP_DAL'_singleton)]!._gps._RGPJ[UInt8.toNat t'3]!.velocity }
  s := { s with gpsDataNew.have_vz := AP_DAL_GPS.have_vertical_velocity_uint8_t w.heap'AP_DAL[(WPtr.index w.AP_DAL'_singleton)]!._gps s.selected_gps }
  s := { s with gpsDataNew.corrected := false }
  let alpha : Binary64 := Estimator_lib.constrain_value_line_double (Binary32.toBinary64 ((Binary32.ofBits 0x3951b717 /- 1.99999995E-4 -/) * UInt32.toBinary32 (s.lastTimeGpsReceived_ms - secondLastGpsTime_ms))) (Binary64.ofBits 0x0000000000000000 /- (double)0 -/) (Binary64.ofBits 0x3ff0000000000000 /- (double)1 -/) (Int32.toUInt32 (613 : Int32))
  s := { s with gpsSpdAccuracy := s.gpsSpdAccuracy * ((Binary64.ofBits 0x3ff0000000000000 /- 1.0f -/) - alpha) }
  let mut gpsSpdAccRaw : Binary32 := (Binary32.ofBits 0x00000000 /- 0.0 -/)  -- uninitialized in C++; assigned before every read
  let (t'4, t'5) := AP_DAL_GPS.speed_accuracy_uint8_t_float w.heap'AP_DAL[(WPtr.index w.AP_DAL'_singleton)]!._gps s.selected_gps gpsSpdAccRaw
  gpsSpdAccRaw := t'4
  if !t'5 then
    s := { s with gpsSpdAccuracy := (Binary64.ofBits 0x0000000000000000 /- 0.0f -/) }
  else
    s := { s with gpsSpdAccuracy := Estimator_lib.MAX_double_float s.gpsSpdAccuracy gpsSpdAccRaw }
    s := { s with gpsSpdAccuracy := Estimator_lib.MIN_double_float s.gpsSpdAccuracy (Binary32.ofBits 0x42480000 /- 50.0f -/) }
    s := { s with gpsSpdAccuracy := Estimator_lib.MAX_double_AP_ParamT_float_4 s.gpsSpdAccuracy w.EKF3._gpsHorizVelNoise }
  s := { s with gpsPosAccuracy := s.gpsPosAccuracy * ((Binary64.ofBits 0x3ff0000000000000 /- 1.0f -/) - alpha) }
  let mut gpsPosAccRaw : Binary32 := (Binary32.ofBits 0x00000000 /- 0.0 -/)  -- uninitialized in C++; assigned before every read
  let (t'6, t'7) := AP_DAL_GPS.horizontal_accuracy_uint8_t_float w.heap'AP_DAL[(WPtr.index w.AP_DAL'_singleton)]!._gps s.selected_gps gpsPosAccRaw
  gpsPosAccRaw := t'6
  if !t'7 then
    s := { s with gpsPosAccuracy := (Binary64.ofBits 0x0000000000000000 /- 0.0f -/) }
  else
    s := { s with gpsPosAccuracy := Estimator_lib.MAX_double_float s.gpsPosAccuracy gpsPosAccRaw }
    s := { s with gpsPosAccuracy := Estimator_lib.MIN_double_float s.gpsPosAccuracy (Binary32.ofBits 0x42c80000 /- 100.0f -/) }
    s := { s with gpsPosAccuracy := Estimator_lib.MAX_double_AP_ParamT_float_4 s.gpsPosAccuracy w.EKF3._gpsHorizPosNoise }
  s := { s with gpsHgtAccuracy := s.gpsHgtAccuracy * ((Binary64.ofBits 0x3ff0000000000000 /- 1.0f -/) - alpha) }
  let mut gpsHgtAccRaw : Binary32 := (Binary32.ofBits 0x00000000 /- 0.0 -/)  -- uninitialized in C++; assigned before every read
  let (t'8, t'9) := AP_DAL_GPS.vertical_accuracy_uint8_t_float w.heap'AP_DAL[(WPtr.index w.AP_DAL'_singleton)]!._gps s.selected_gps gpsHgtAccRaw
  gpsHgtAccRaw := t'8
  if !t'9 then
    s := { s with gpsHgtAccuracy := (Binary64.ofBits 0x0000000000000000 /- 0.0f -/) }
  else
    s := { s with gpsHgtAccuracy := Estimator_lib.MAX_double_float s.gpsHgtAccuracy gpsHgtAccRaw }
    s := { s with gpsHgtAccuracy := Estimator_lib.MIN_double_float s.gpsHgtAccuracy (Binary32.ofBits 0x42c80000 /- 100.0f -/) }
    s := { s with gpsHgtAccuracy := Estimator_lib.MAX_double_float s.gpsHgtAccuracy ((Binary32.ofBits 0x3fc00000 /- 1.5f -/) * AP_ParamT_float_4.op_to_float w.EKF3._gpsHorizPosNoise) }
  if decide (UInt32.toInt32 (UInt8.toUInt32 (AP_DAL_GPS.num_sats_uint8_t w.heap'AP_DAL[(WPtr.index w.AP_DAL'_singleton)]!._gps s.selected_gps)) ≥ (6 : Int32)) && (UInt32.toInt32 (NavEKF3_core.AidingMode.toInt s.PV_AidingMode) == UInt32.toInt32 (NavEKF3_core.AidingMode.toInt NavEKF3_core.AidingMode.AID_ABSOLUTE)) then
    s := { s with gpsNoiseScaler := (Binary64.ofBits 0x3ff0000000000000 /- 1.0f -/) }
  else if UInt32.toInt32 (UInt8.toUInt32 (AP_DAL_GPS.num_sats_uint8_t w.heap'AP_DAL[(WPtr.index w.AP_DAL'_singleton)]!._gps s.selected_gps)) == (5 : Int32) && (UInt32.toInt32 (NavEKF3_core.AidingMode.toInt s.PV_AidingMode) == UInt32.toInt32 (NavEKF3_core.AidingMode.toInt NavEKF3_core.AidingMode.AID_ABSOLUTE)) then
    s := { s with gpsNoiseScaler := (Binary64.ofBits 0x3ff6666660000000 /- 1.4f -/) }
  else
    s := { s with gpsNoiseScaler := (Binary64.ofBits 0x4000000000000000 /- 2.0f -/) }
  if s.gpsDataNew.have_vz && AP_NavEKF_Source.useVelZSource w.EKF3.sources AP_NavEKF_Source.SourceZ.GPS s.core_index then
    s := { s with useGpsVertVel := true }
  else
    s := { s with useGpsVertVel := false }
  if NavEKF3.option_is_enabled w.EKF3 NavEKF3.Option.JammingExpected && decide ((s.lastTimeGpsReceived_ms - secondLastGpsTime_ms) > UInt16.toUInt32 w.EKF3.gpsNoFixTimeout_ms) then
    let doingBodyVelNav : Bool := (decide (s.imuSampleTime_ms - s.bodyOdm.prevFuseTime_ms < Int32.toUInt32 (1000 : Int32)))
    let doingFlowNav : Bool := (decide (s.imuSampleTime_ms - s.prevFlowFuseTime_ms < Int32.toUInt32 (1000 : Int32)))
    let canDoWindRelNav : Bool := assume_zero_sideslip w
    let canDeadReckon : Bool := ((doingFlowNav && s.gndOffsetValid) || canDoWindRelNav || doingBodyVelNav)
    if canDeadReckon then
      s := { s with waitingForGpsChecks := true }
      s := { s with lastPreAlignGpsCheckTime_ms := Int32.toUInt32 (0 : Int32) }
      s := { s with lastGpsVelFail_ms := s.imuSampleTime_ms }
      s := { s with lastGpsVelPass_ms := Int32.toUInt32 (0 : Int32) }
      s := { s with gpsGoodToAlign := false }
    else
      s := { s with waitingForGpsChecks := false }
  s := calcGpsGoodToAlign s w
  s := calcGpsGoodForFlight s w
  let t'10 := s.selected_gps
  if s.gpsGoodToAlign && !s.validOrigin then
    let mut gpsloc_fieldelevation : Location.State := w.heap'AP_DAL[(WPtr.index w.AP_DAL'_singleton)]!._gps.tmp_location[UInt8.toNat t'10]!
    if s.inFlight then
      gpsloc_fieldelevation := { gpsloc_fieldelevation with alt := gpsloc_fieldelevation.alt + Binary64.toInt32 ((Binary64.ofBits 0x4059000000000000 /- 100.0f -/) * s.statesArray[9]!) }
    let (t'11, t'12, t'13, t'14) := setOriginLLH s w o gpsloc_fieldelevation
    w := t'12
    s := t'11
    o := t'13
    if !t'14 then
      pure ()  -- C++ `AP_InternalError::error(...)`: left out (--drop)
      return (s, w, o)
    let (t'15, t'16) := alignMagStateDeclination s w
    w := t'16
    s := t'15
    s := { s with ekfGpsRefHgt := (Binary64.ofBits 0x3f847ae147ae147b /- 0.01 -/) * Int32.toBinary64 w.heap'AP_DAL[(WPtr.index w.AP_DAL'_singleton)]!._gps.tmp_location[UInt8.toNat t'10]!.alt + s.outputDataNew.position.z }
    s := { s with ekfOriginHgtVar := Estimator_lib.sq_double s.gpsHgtAccuracy }
  if s.gpsGoodToAlign && !s.have_table_earth_field then
    s := setEarthFieldFromLocation s w w.heap'AP_DAL[(WPtr.index w.AP_DAL'_singleton)]!._gps.tmp_location[UInt8.toNat t'10]!
  if s.validOrigin && !s.waitingForGpsChecks then
    s := { s with gpsDataNew.lat := w.heap'AP_DAL[(WPtr.index w.AP_DAL'_singleton)]!._gps.tmp_location[UInt8.toNat t'10]!.lat }
    s := { s with gpsDataNew.lng := w.heap'AP_DAL[(WPtr.index w.AP_DAL'_singleton)]!._gps.tmp_location[UInt8.toNat t'10]!.lng }
    if (UInt32.toInt32 (UInt8.toUInt32 (AP_ParamT_unsigned_char_1.op_to_unsigned_char w.EKF3._originHgtMode)) &&& ((1 : Int32) <<< (2 : Int32))) == (0 : Int32) then
      s := { s with gpsDataNew.hgt := ((Binary64.ofBits 0x3f847ae147ae147b /- 0.01 -/) * Int32.toBinary64 w.heap'AP_DAL[(WPtr.index w.AP_DAL'_singleton)]!._gps.tmp_location[UInt8.toNat t'10]!.alt - s.ekfGpsRefHgt) }
    else
      s := { s with gpsDataNew.hgt := Binary32.toBinary64 ((Binary32.ofBits 0x3c23d70a /- 0.01 -/) * Int32.toBinary32 (w.heap'AP_DAL[(WPtr.index w.AP_DAL'_singleton)]!._gps.tmp_location[UInt8.toNat t'10]!.alt - s.EKF_origin.alt)) }
    s := { s with storedGPS := EKF_obs_buffer_t_NavEKF3_core_gps_elements.push_gps_elements s.storedGPS s.gpsDataNew }
    s := { s with gpsIsInUse := true }
  return (s, w, o)

end NavEKF3_core

namespace NavEKF3_core

-- not read in the Lean: antOffset
set_option linter.unusedVariables false in
/-- C++ `void NavEKF3_core::writeEulerYawAngle(float yawAngle, float yawAngleErr, uint32_t timeStamp_ms, uint8_t type, const Vector3f & antOffset)`, `AP_NavEKF3/AP_NavEKF3_Measurements.cpp:1049-1079`. -/
def writeEulerYawAngle (s : State) (w : World) (yawAngle : Binary32) (yawAngleErr : Binary32) (timeStamp_ms : UInt32) (type : UInt8) (antOffset : Vector3f.State := Vector3f.init_void) : State := Id.run do
  let mut s := s
  if (decide ((timeStamp_ms - s.gpsYaw.measTime_ms) < UInt8.toUInt32 w.EKF3.sensorIntervalMin_ms)) || !s.statesInitialised then
    return s
  s := { s with gpsYaw.dataNew.yawAng := Binary32.toBinary64 yawAngle }
  s := { s with gpsYaw.dataNew.yawAngErr := Binary32.toBinary64 yawAngleErr }
  if UInt32.toInt32 (UInt8.toUInt32 type) == (2 : Int32) then
    s := { s with gpsYaw.dataNew.order := NavEKF3_core.rotationOrder.TAIT_BRYAN_321 }
  else if UInt32.toInt32 (UInt8.toUInt32 type) == (1 : Int32) then
    s := { s with gpsYaw.dataNew.order := NavEKF3_core.rotationOrder.TAIT_BRYAN_312 }
  else
    return s
  s := { s with gpsYaw.dataNew.time_ms := Estimator_lib.MAX_uint32_t2 timeStamp_ms s.imuDataDelayed.time_ms }
  s := { s with gpsYaw.stored := EKF_obs_buffer_t_NavEKF3_core_yaw_elements.push_yaw_elements s.gpsYaw.stored s.gpsYaw.dataNew }
  s := { s with gpsYaw.measTime_ms := timeStamp_ms }
  return s

/-- C++ `void NavEKF3_core::readGpsYawData()`, `AP_NavEKF3/AP_NavEKF3_Measurements.cpp:737-759`. -/
def readGpsYawData (s : State) (w : World) : State := Id.run do
  let mut s := s
  let mut yaw_deg : Binary32 := (Binary32.ofBits 0x00000000 /- 0.0 -/)  -- uninitialized in C++; assigned before every read
  let mut yaw_accuracy_deg : Binary32 := (Binary32.ofBits 0x00000000 /- 0.0 -/)  -- uninitialized in C++; assigned before every read
  let mut yaw_time_ms : UInt32 := (0 : UInt32)  -- uninitialized in C++; assigned before every read
  let mut t'5 := decide (AP_GPS_FixType.toInt (AP_DAL_GPS.status_uint8_t w.heap'AP_DAL[(WPtr.index w.AP_DAL'_singleton)]!._gps s.selected_gps) ≥ AP_GPS_FixType.toInt AP_GPS_FixType.FIX_3D)
  if t'5 then
    let (t'1, t'2, t'3, t'4) := AP_DAL_GPS.gps_yaw_deg w.heap'AP_DAL[(WPtr.index w.AP_DAL'_singleton)]!._gps s.selected_gps yaw_deg yaw_accuracy_deg yaw_time_ms
    yaw_deg := t'1
    yaw_accuracy_deg := t'2
    yaw_time_ms := t'3
    t'5 := t'4
  if t'5 && yaw_time_ms != s.gpsYaw.measTime_ms then
    let min_yaw_accuracy_deg : Binary64 := (Binary64.ofBits 0x4014000000000000 /- 5.0f -/)
    yaw_accuracy_deg := Binary64.toBinary32 (Estimator_lib.MAX_float_double yaw_accuracy_deg min_yaw_accuracy_deg)
    s := writeEulerYawAngle s w (Estimator_lib.radians_float yaw_deg) (Estimator_lib.radians_float yaw_accuracy_deg) yaw_time_ms (Int8.toUInt8 (Int32.toInt8 (2 : Int32))) Vector3f.init_void
  return s

end NavEKF3_core

namespace NavEKF3_core

/-- C++ `void NavEKF3_core::readBaroData()`, `AP_NavEKF3/AP_NavEKF3_Measurements.cpp:783-807`. -/
def readBaroData (s : State) (w : World) : State := Id.run do
  let mut s := s
  if AP_DAL_Baro.get_last_update_uint8_t w.heap'AP_DAL[(WPtr.index w.AP_DAL'_singleton)]!._baro s.selected_baro - s.lastBaroReceived_ms > UInt8.toUInt32 w.EKF3.sensorIntervalMin_ms then
    s := { s with baroDataNew.hgt := Binary32.toBinary64 (AP_DAL_Baro.get_altitude_uint8_t w.heap'AP_DAL[(WPtr.index w.AP_DAL'_singleton)]!._baro s.selected_baro) }
    s := { s with lastBaroReceived_ms := AP_DAL_Baro.get_last_update_uint8_t w.heap'AP_DAL[(WPtr.index w.AP_DAL'_singleton)]!._baro s.selected_baro }
    s := { s with baroDataNew.time_ms := s.lastBaroReceived_ms - Int32.toUInt32 (Int16.toInt32 (AP_ParamT_short_2.op_to_short w.EKF3._hgtDelay_ms)) }
    s := { s with baroDataNew.time_ms := s.baroDataNew.time_ms - Int32.toUInt32 (UInt32.toInt32 (UInt8.toUInt32 s.localFilterTimeStep_ms) / (2 : Int32)) }
    s := { s with baroDataNew.time_ms := Estimator_lib.MAX_uint32_t2 s.baroDataNew.time_ms s.imuDataDelayed.time_ms }
    s := { s with storedBaro := EKF_obs_buffer_t_NavEKF3_core_baro_elements.push_baro_elements s.storedBaro s.baroDataNew }
  return s

end NavEKF3_core

namespace NavEKF3_core

/-- C++ `void NavEKF3_core::InitialiseVariablesMag()`, `AP_NavEKF3/AP_NavEKF3_core.cpp:414-441`. -/
def InitialiseVariablesMag (s : State) (w : World) : State := Id.run do
  let mut s := s
  s := { s with lastHealthyMagTime_ms := s.imuSampleTime_ms }
  s := { s with lastMagUpdate_us := Int32.toUInt32 (0 : Int32) }
  s := { s with magYawResetTimer_ms := s.imuSampleTime_ms }
  s := { s with magTimeout := false }
  s := { s with allMagSensorsFailed := false }
  s := { s with finalInflightMagInit := false }
  s := { s with inhibitMagStates := true }
  s := { s with magSelectIndex := AP_DAL_Compass.get_first_usable w.heap'AP_DAL[(WPtr.index w.AP_DAL'_singleton)]!._compass }
  s := { s with lastMagOffsetsValid := false }
  s := { s with magStateResetRequest := false }
  s := { s with magStateInitComplete := false }
  s := { s with magYawResetRequest := false }
  s := { s with posDownAtLastMagReset := s.statesArray[9]! }
  s := { s with yawInnovAtLastMagReset := (Binary64.ofBits 0x0000000000000000 /- 0.0f -/) }
  let t'1 := QuaternionT_double.initialise ({ q1 := s.statesArray[0]!, q2 := s.statesArray[1]!, q3 := s.statesArray[2]!, q4 := s.statesArray[3]! } : QuaternionT_double.State)
  s := { s with statesArray := ((((s.statesArray.set! 0 t'1.q1).set! 1 t'1.q2).set! 2 t'1.q3).set! 3 t'1.q4) }
  s := { s with quatAtLastMagReset := ({ q1 := s.statesArray[0]!, q2 := s.statesArray[1]!, q3 := s.statesArray[2]!, q4 := s.statesArray[3]! } : QuaternionT_double.State) }
  s := { s with magFieldLearned := false }
  s := { s with storedMag := EKF_obs_buffer_t_NavEKF3_core_mag_elements.reset s.storedMag }
  s := { s with gpsYaw.stored := EKF_obs_buffer_t_NavEKF3_core_yaw_elements.reset s.gpsYaw.stored }
  s := { s with needMagBodyVarReset := false }
  s := { s with needEarthBodyVarReset := false }
  s := { s with magFusionSel := NavEKF3_core.MagFuseSel.NOT_FUSING }
  return s

/-- C++ `MagCal NavEKF3_core::effective_magCal() const`, `AP_NavEKF3/AP_NavEKF3_Control.cpp:41-58`. -/
def effective_magCal (s : State) (w : World) : NavEKF3_core.MagCal := Id.run do
  if UInt32.toInt32 (UInt8.toUInt32 (AP_ParamT_unsigned_char_1.op_to_unsigned_char w.EKF3._magMask)) &&& UInt32.toInt32 (UInt8.toUInt32 s.core_index) != (0 : Int32) then
    return NavEKF3_core.MagCal.NEVER
  let magCalParamVal : Int8 := AP_ParamT_signed_char_1.get_void w.EKF3._magCal
  if Int8.toInt32 magCalParamVal == (5 : Int32) then
    return NavEKF3_core.MagCal.NEVER
  if Int8.toInt32 magCalParamVal == (6 : Int32) then
    return NavEKF3_core.MagCal.WHEN_FLYING
  return NavEKF3_core.MagCal.ofInt (Int8.toInt32 magCalParamVal)

end NavEKF3_core

namespace NavEKF3_core

/-- C++ `void NavEKF3_core::InitialiseVariables()`, `AP_NavEKF3/AP_NavEKF3_core.cpp:198-411`. -/
def InitialiseVariables (s : State) (w : World) : State × World := Id.run do
  let mut s := s
  let mut w := w
  s := { s with localFilterTimeStep_ms := Binary32.toUInt8 ((Binary32.ofBits 0x447a0000 /- 1000 -/) * AP_DAL_InertialSensor.get_loop_delta_t w.heap'AP_DAL[(WPtr.index w.AP_DAL'_singleton)]!._ins) }
  s := { s with localFilterTimeStep_ms := Estimator_lib.MAX_uint8_t2 s.localFilterTimeStep_ms (Int8.toUInt8 (Int32.toInt8 (12 : Int32))) }
  s := { s with imuSampleTime_ms := UInt64.toUInt32 (w.EKF3.imuSampleTime_us / Int64.toUInt64 (Int32.toInt64 (1000 : Int32))) }
  s := { s with tas := NavEKF3_core.AirspeedFusion.InitialiseVariables s.tas s.imuSampleTime_ms }
  s := { s with prevBetaDragStep_ms := s.imuSampleTime_ms }
  s := { s with lastBaroReceived_ms := s.imuSampleTime_ms }
  s := { s with lastVelPassTime_ms := Int32.toUInt32 (0 : Int32) }
  s := { s with lastGpsPosPassTime_ms := Int32.toUInt32 (0 : Int32) }
  s := { s with lastHgtPassTime_ms := Int32.toUInt32 (0 : Int32) }
  s := { s with lastSynthYawTime_ms := Int32.toUInt32 (0 : Int32) }
  s := { s with lastTimeGpsReceived_ms := Int32.toUInt32 (0 : Int32) }
  s := { s with timeAtLastAuxEKF_ms := s.imuSampleTime_ms }
  s := { s with flowValidMeaTime_ms := s.imuSampleTime_ms }
  s := { s with rngValidMeaTime_ms := s.imuSampleTime_ms }
  s := { s with flowMeaTime_ms := Int32.toUInt32 (0 : Int32) }
  s := { s with prevFlowFuseTime_ms := Int32.toUInt32 (0 : Int32) }
  s := { s with gndHgtValidTime_ms := Int32.toUInt32 (0 : Int32) }
  s := { s with ekfStartTime_ms := s.imuSampleTime_ms }
  s := { s with lastGpsVelFail_ms := Int32.toUInt32 (0 : Int32) }
  s := { s with lastGpsAidBadTime_ms := Int32.toUInt32 (0 : Int32) }
  s := { s with lastPreAlignGpsCheckTime_ms := s.imuSampleTime_ms }
  s := { s with posNEResetCount := Int16.toUInt16 (Int32.toInt16 (0 : Int32)) }
  s := { s with posDResetCount := Int16.toUInt16 (Int32.toInt16 (0 : Int32)) }
  s := { s with lastRngMeasTime_ms := Int32.toUInt32 (0 : Int32) }
  s := { s with dvelBiasAxisInhibit := Array.replicate 3 false }
  s := { s with dvelBiasAxisVarPrev := Vector3p.zero s.dvelBiasAxisVarPrev }
  s := { s with gpsNoiseScaler := (Binary64.ofBits 0x3ff0000000000000 /- 1.0f -/) }
  s := { s with hgtTimeout := true }
  s := { s with tasTimeout := true }
  s := { s with dragTimeout := true }
  s := { s with badIMUdata := false }
  s := { s with badIMUdata_ms := Int32.toUInt32 (0 : Int32) }
  s := { s with goodIMUdata_ms := Int32.toUInt32 (0 : Int32) }
  s := { s with vertVelVarClipCounter := Int32.toUInt32 (0 : Int32) }
  s := { s with finalInflightYawInit := false }
  s := { s with dtIMUavg := Binary32.toBinary64 (AP_DAL_InertialSensor.get_loop_delta_t w.heap'AP_DAL[(WPtr.index w.AP_DAL'_singleton)]!._ins) }
  s := { s with dtEkfAvg := (Binary64.ofBits 0x3f889374c0000000 /- (double)6442451/536870912 -/) }
  s := { s with dt := (Binary64.ofBits 0x0000000000000000 /- 0 -/) }
  s := { s with velDotNEDfilt := Vector3p.zero s.velDotNEDfilt }
  s := { s with lastKnownPositionNE := Vector2p.zero s.lastKnownPositionNE }
  s := { s with lastKnownPositionD := (Binary32.ofBits 0x00000000 /- 0 -/) }
  s := { s with prevTnb := Matrix3_double.zero s.prevTnb }
  s := { s with Pmut := Array.replicate 576 (Binary64.ofBits 0x0000000000000000 /- 0.0 -/) }
  w := { w with NavEKF_core_common'KHP := Array.replicate 576 (Binary64.ofBits 0x0000000000000000 /- 0.0 -/) }
  s := { s with flowDataValid := false }
  s := { s with rangeDataToFuse := false }
  s := { s with terrainState := (Binary64.ofBits 0x0000000000000000 /- 0.0f -/) }
  s := { s with prevPosN := s.statesArray[7]! }
  s := { s with prevPosE := s.statesArray[8]! }
  s := { s with inhibitGndState := false }
  s := { s with flowGyroBias.x := (Binary64.ofBits 0x0000000000000000 /- 0 -/) }
  s := { s with flowGyroBias.y := (Binary64.ofBits 0x0000000000000000 /- 0 -/) }
  s := { s with PV_AidingMode := NavEKF3_core.AidingMode.AID_NONE }
  s := { s with PV_AidingModePrev := NavEKF3_core.AidingMode.AID_NONE }
  s := { s with posTimeout := true }
  s := { s with velTimeout := true }
  s := { s with velAiding := false }
  s := { s with waitingForGpsChecks := false }
  s := { s with faultStatus := { bad_xmag := false, bad_ymag := false, bad_zmag := false, bad_airspeed := false, bad_sideslip := false, bad_nvel := false, bad_evel := false, bad_dvel := false, bad_npos := false, bad_epos := false, bad_dpos := false, bad_yaw := false, bad_decl := false, bad_xflow := false, bad_yflow := false, bad_rngbcn := false, bad_xvel := false, bad_yvel := false, bad_zvel := false } }
  s := { s with hgtRate := (Binary64.ofBits 0x0000000000000000 /- 0.0f -/) }
  s := { s with onGround := true }
  s := { s with prevOnGround := true }
  s := { s with inFlight := false }
  s := { s with prevInFlight := false }
  s := { s with manoeuvring := false }
  s := { s with fusingStationaryZeroVel := false }
  s := { s with inhibitWindStates := true }
  s := { s with windStateIsObservable := false }
  s := { s with treatWindStatesAsTruth := false }
  s := { s with lastAspdEstIsValid := false }
  s := { s with windStatesAligned := false }
  s := { s with inhibitDelVelBiasStates := true }
  s := { s with inhibitDelAngBiasStates := true }
  s := { s with gndOffsetValid := false }
  s := { s with validOrigin := false }
  s := { s with gpsSpdAccuracy := (Binary64.ofBits 0x0000000000000000 /- 0.0f -/) }
  s := { s with gpsPosAccuracy := (Binary64.ofBits 0x0000000000000000 /- 0.0f -/) }
  s := { s with gpsHgtAccuracy := (Binary64.ofBits 0x0000000000000000 /- 0.0f -/) }
  s := { s with baroHgtOffset := (Binary64.ofBits 0x0000000000000000 /- 0.0f -/) }
  s := { s with rngOnGnd := (Binary64.ofBits 0x3fa99999a0000000 /- 0.05f -/) }
  s := { s with yawResetCount := Int16.toUInt16 (Int32.toInt16 (0 : Int32)) }
  s := { s with tiltErrorVariance := Binary32.toBinary64 (Estimator_lib.sq_float ((Binary32.ofBits 0x40490fdb /- (float)884279719003555/281474976710656 -/) * (Binary32.ofBits 0x40000000 /- (float)2 -/))) }
  s := { s with tiltAlignComplete := false }
  s := { s with yawAlignComplete := false }
  s := { s with yawAlignGpsValidCount := Int8.toUInt8 (Int32.toInt8 (0 : Int32)) }
  s := { s with have_table_earth_field := false }
  s := { s with stateIndexLim := Int8.toUInt8 (Int32.toInt8 (23 : Int32)) }
  s := { s with last_gps_idx := Int8.toUInt8 (Int32.toInt8 (0 : Int32)) }
  s := { s with delAngCorrection := Vector3p.zero s.delAngCorrection }
  s := { s with velErrintegral := Vector3p.zero s.velErrintegral }
  s := { s with posErrintegral := Vector3p.zero s.posErrintegral }
  s := { s with gpsGoodToAlign := false }
  s := { s with gpsIsInUse := false }
  s := { s with motorsArmed := false }
  s := { s with prevMotorsArmed := false }
  s := { s with gpsCheckStatus := (0 : UInt16) }
  s := { s with gpsSpdAccPass := false }
  s := { s with ekfInnovationsPass := false }
  s := { s with sAccFilterState1 := (Binary64.ofBits 0x0000000000000000 /- 0.0f -/) }
  s := { s with sAccFilterState2 := (Binary64.ofBits 0x0000000000000000 /- 0.0f -/) }
  s := { s with lastGpsCheckTime_ms := Int32.toUInt32 (0 : Int32) }
  s := { s with lastGpsInnovPassTime_ms := Int32.toUInt32 (0 : Int32) }
  s := { s with lastGpsInnovFailTime_ms := Int32.toUInt32 (0 : Int32) }
  s := { s with lastGpsVertAccPassTime_ms := Int32.toUInt32 (0 : Int32) }
  s := { s with lastGpsVertAccFailTime_ms := Int32.toUInt32 (0 : Int32) }
  s := { s with gpsAccuracyGood := false }
  s := { s with gpsAccuracyGoodForAltitude := false }
  s := { s with gpsloc_prev := Location.init_void }
  s := { s with gpsDriftNE := (Binary64.ofBits 0x0000000000000000 /- 0.0f -/) }
  s := { s with gpsVertVelFilt := (Binary64.ofBits 0x0000000000000000 /- 0.0f -/) }
  s := { s with gpsHorizVelFilt := (Binary64.ofBits 0x0000000000000000 /- 0.0f -/) }
  s := { s with statesArray := Array.replicate 24 (Binary64.ofBits 0x0000000000000000 /- 0.0 -/) }
  s := { s with vertCompFiltState := { pos := (Binary64.ofBits 0x0000000000000000 /- 0.0 -/), vel := (Binary64.ofBits 0x0000000000000000 /- 0.0 -/), acc := (Binary64.ofBits 0x0000000000000000 /- 0.0 -/) } }
  s := { s with posVelFusionDelayed := false }
  s := { s with flowFusionActive := false }
  s := { s with airSpdFusionDelayed := false }
  s := { s with sideSlipFusionDelayed := false }
  s := { s with airDataFusionWindOnly := false }
  s := { s with posResetNE := Vector2p.zero s.posResetNE }
  s := { s with posResetD := (Binary64.ofBits 0x0000000000000000 /- 0.0f -/) }
  s := { s with hgtInnovFiltState := (Binary64.ofBits 0x0000000000000000 /- 0.0f -/) }
  s := { s with imuDataDownSampledNew.delAng := Vector3p.zero s.imuDataDownSampledNew.delAng }
  s := { s with imuDataDownSampledNew.delVel := Vector3p.zero s.imuDataDownSampledNew.delVel }
  s := { s with imuDataDownSampledNew.delAngDT := (Binary64.ofBits 0x0000000000000000 /- 0.0f -/) }
  s := { s with imuDataDownSampledNew.delVelDT := (Binary64.ofBits 0x0000000000000000 /- 0.0f -/) }
  s := { s with imuDataDownSampledNew.gyro_index := s.gyro_index_active }
  s := { s with imuDataDownSampledNew.accel_index := s.accel_index_active }
  s := { s with runUpdates := false }
  s := { s with framesSincePredict := Int32.toUInt32 (0 : Int32) }
  s := { s with gpsYawResetRequest := false }
  s := { s with delAngBiasLearned := false }
  s := { s with filterStatus := (0 : UInt32) }
  s := { s with activeHgtSource := AP_NavEKF_Source.SourceZ.BARO }
  s := { s with prevHgtSource := s.activeHgtSource }
  s := { s with terrainHgtStable := true }
  s := { s with ekfOriginHgtVar := (Binary64.ofBits 0x0000000000000000 /- 0.0f -/) }
  s := { s with ekfGpsRefHgt := (Binary64.ofBits 0x0000000000000000 /- 0.0 -/) }
  s := { s with velOffsetNED := Vector3p.zero s.velOffsetNED }
  s := { s with posOffsetNED := Vector3p.zero s.posOffsetNED }
  s := { s with velPosObs := Array.replicate 6 (Binary64.ofBits 0x0000000000000000 /- 0.0 -/) }
  s := { s with bodyOdm := NavEKF3_core.BodyOdomFusion.InitialiseVariables s.bodyOdm }
  s := { s with gpsYaw := NavEKF3_core.GpsYawFusion.InitialiseVariables s.gpsYaw }
  s := { s with storedIMU := EKF_IMU_buffer_t_NavEKF3_core_imu_elements.reset s.storedIMU }
  s := { s with storedGPS := EKF_obs_buffer_t_NavEKF3_core_gps_elements.reset s.storedGPS }
  s := { s with storedBaro := EKF_obs_buffer_t_NavEKF3_core_baro_elements.reset s.storedBaro }
  s := { s with tas.stored := EKF_obs_buffer_t_NavEKF3_core_tas_elements.reset s.tas.stored }
  s := { s with storedOutput := EKF_IMU_buffer_t_NavEKF3_core_output_elements.reset s.storedOutput }
  s := { s with bodyOdm.stored := EKF_obs_buffer_t_NavEKF3_core_vel_odm_elements.reset s.bodyOdm.stored }
  s := { s with bodyOdm.storedWheel := EKF_obs_buffer_t_NavEKF3_core_wheel_odm_elements.reset s.bodyOdm.storedWheel }
  s := { s with prearm_fail_string := (CText.fmt (40 : UInt64) "EKF3 still initialising" #[]) }
  s := InitialiseVariablesMag s w
  s := { s with EKFGSF_yaw_reset_ms := Int32.toUInt32 (0 : Int32) }
  s := { s with EKFGSF_yaw_reset_request_ms := Int32.toUInt32 (0 : Int32) }
  s := { s with EKFGSF_yaw_reset_count := Int8.toUInt8 (Int32.toInt8 (0 : Int32)) }
  s := { s with EKFGSF_run_filterbank := false }
  s := { s with EKFGSF_yaw_valid_count := Int8.toUInt8 (Int32.toInt8 (0 : Int32)) }
  s := { s with effectiveMagCal := effective_magCal s w }
  return (s, w)

end NavEKF3_core

namespace NavEKF3_core

/-- C++ `void NavEKF3_core::CorrectGPSForAntennaOffset(gps_elements & gps_data) const`, `AP_NavEKF3/AP_NavEKF3_PosVelFusion.cpp:413-435`. -/
def CorrectGPSForAntennaOffset (s : State) (w : World) (gps_data : NavEKF3_core.gps_elements) : NavEKF3_core.gps_elements := Id.run do
  let mut gps_data := gps_data
  if gps_data.corrected then
    return gps_data
  gps_data := { gps_data with corrected := true }
  let t'1 := gps_data.sensor_idx
  let t'2 := Vector3f.todouble w.heap'AP_DAL[(WPtr.index w.AP_DAL'_singleton)]!._gps._RGPI[UInt8.toNat t'1]!.antenna_offset
  let posOffsetBody : Vector3p.State := Vector3p.op_sub_Vector3p t'2 s.accelPosOffset
  if Vector3p.is_zero posOffsetBody then
    return gps_data
  let angRate : Vector3p.State := Vector3p.op_mul_double s.imuDataDelayed.delAng ((Binary64.ofBits 0x3ff0000000000000 /- 1.0f -/) / s.imuDataDelayed.delAngDT)
  let velOffsetBody : Vector3p.State := Vector3p.op_mod angRate posOffsetBody
  let velOffsetEarth : Vector3p.State := Matrix3_double.mul_transpose s.prevTnb velOffsetBody
  let (t'3, _) := Vector3p.op_sub_assign gps_data.vel velOffsetEarth
  gps_data := { gps_data with vel := t'3 }
  let posOffsetEarth : Vector3p.State := Matrix3_double.mul_transpose s.prevTnb posOffsetBody
  let (t'5, t'6) := Location.offset_latlng gps_data.lat gps_data.lng (-posOffsetEarth.x) (-posOffsetEarth.y)
  gps_data := { gps_data with lat := t'5 }
  gps_data := { gps_data with lng := t'6 }
  gps_data := { gps_data with hgt := gps_data.hgt + posOffsetEarth.z }
  return gps_data

/-- C++ `enum class NavEKF3_core::resetDataSource`, `AP_NavEKF3/AP_NavEKF3_core.h:707-716`. -/
inductive resetDataSource where
  | DEFAULT
  | GPS
  | RNGBCN
  | FLOW
  | BARO
  | MAG
  | RNGFND
  | EXTNAV
deriving DecidableEq, Inhabited

/-- The value of each enumerator of `NavEKF3_core::resetDataSource` (underlying type `int32_t`). -/
def resetDataSource.toInt : resetDataSource → Int32
  | .DEFAULT => (0 : Int32)
  | .GPS => (1 : Int32)
  | .RNGBCN => (2 : Int32)
  | .FLOW => (3 : Int32)
  | .BARO => (4 : Int32)
  | .MAG => (5 : Int32)
  | .RNGFND => (6 : Int32)
  | .EXTNAV => (7 : Int32)

/-- C++ `void NavEKF3_core::ResetVelocity(resetDataSource velResetSource)`, `AP_NavEKF3/AP_NavEKF3_PosVelFusion.cpp:16-82`. -/
def ResetVelocity (s : State) (w : World) (velResetSource : NavEKF3_core.resetDataSource) : State := Id.run do
  let mut s := s
  let mut velResetSource := velResetSource
  if velResetSource == NavEKF3_core.resetDataSource.DEFAULT then
    match AP_NavEKF_Source.getVelXYSource w.EKF3.sources s.core_index with
    | .GPS =>
      velResetSource := NavEKF3_core.resetDataSource.GPS
    | .BEACON =>
      velResetSource := NavEKF3_core.resetDataSource.RNGBCN
    | .EXTNAV =>
      velResetSource := NavEKF3_core.resetDataSource.EXTNAV
    | .NONE | .OPTFLOW | .WHEEL_ENCODER =>
      pure ()
  s := zeroStatesVarCov s (Int8.toUInt8 (Int32.toInt8 (4 : Int32))) (Int8.toUInt8 (Int32.toInt8 (5 : Int32)))
  if UInt32.toInt32 (NavEKF3_core.AidingMode.toInt s.PV_AidingMode) != UInt32.toInt32 (NavEKF3_core.AidingMode.toInt NavEKF3_core.AidingMode.AID_ABSOLUTE) then
    let t'1 := Vector2p.zero ({ x := s.statesArray[4]!, y := s.statesArray[5]! } : Vector2p.State)
    s := { s with statesArray := ((s.statesArray.set! 4 t'1.x).set! 5 t'1.y) }
    s := { s with Pmut := s.Pmut.set! 100 (Estimator_lib.sq_AP_ParamT_float_4 w.EKF3._gpsHorizVelNoise) }
    s := { s with Pmut := s.Pmut.set! 125 (s.Pmut[100]!) }
  else
    if (decide (s.imuSampleTime_ms - s.lastTimeGpsReceived_ms < Int32.toUInt32 (250 : Int32))) && (velResetSource == NavEKF3_core.resetDataSource.DEFAULT || velResetSource == NavEKF3_core.resetDataSource.GPS) then
      let mut gps_corrected : NavEKF3_core.gps_elements := s.gpsDataNew
      gps_corrected := CorrectGPSForAntennaOffset s w gps_corrected
      s := { s with statesArray := s.statesArray.set! 4 gps_corrected.vel.x }
      s := { s with statesArray := s.statesArray.set! 5 gps_corrected.vel.y }
      s := { s with Pmut := s.Pmut.set! 100 (Estimator_lib.sq_double (Estimator_lib.MAX_AP_ParamT_float_4_double w.EKF3._gpsHorizVelNoise s.gpsSpdAccuracy)) }
      s := { s with Pmut := s.Pmut.set! 125 (s.Pmut[100]!) }
    else
      s := { s with statesArray := s.statesArray.set! 4 (Binary64.ofBits 0x0000000000000000 /- 0.0f -/) }
      s := { s with statesArray := s.statesArray.set! 5 (Binary64.ofBits 0x0000000000000000 /- 0.0f -/) }
      s := { s with Pmut := s.Pmut.set! 100 (Binary32.toBinary64 (Estimator_lib.sq_float (Binary32.ofBits 0x41c80000 /- 25.0f -/))) }
      s := { s with Pmut := s.Pmut.set! 125 (s.Pmut[100]!) }
    s := { s with velTimeout := false }
    s := { s with lastVelPassTime_ms := s.imuSampleTime_ms }
  let t'2 : UInt8 := Int8.toUInt8 (Int32.toInt8 (0 : Int32))
  let t'3 : Int32 := UInt32.toInt32 (UInt8.toUInt32 s.imu_buffer_length)
  for i' in [0:(t'3.toInt - (Int.ofNat t'2.toNat)).toNat] do  -- C++ loop bounded by a runtime value (--runtime-loops)
    let i : UInt8 := t'2 + Nat.toUInt8 i'
    s := { s with storedOutput.buffer := s.storedOutput.buffer.set! (UInt8.toNat (UInt32.toUInt8 (UInt8.toUInt32 i))) ({ s.storedOutput.buffer[UInt8.toNat (UInt32.toUInt8 (UInt8.toUInt32 i))]! with velocity.x := s.statesArray[4]! }) }
    s := { s with storedOutput.buffer := s.storedOutput.buffer.set! (UInt8.toNat (UInt32.toUInt8 (UInt8.toUInt32 i))) ({ s.storedOutput.buffer[UInt8.toNat (UInt32.toUInt8 (UInt8.toUInt32 i))]! with velocity.y := s.statesArray[5]! }) }
  s := { s with outputDataNew.velocity.x := s.statesArray[4]! }
  s := { s with outputDataNew.velocity.y := s.statesArray[5]! }
  s := { s with outputDataDelayed.velocity.x := s.statesArray[4]! }
  s := { s with outputDataDelayed.velocity.y := s.statesArray[5]! }
  return s

end NavEKF3_core

namespace NavEKF3_core

/-- C++ `void NavEKF3_core::ResetPosition(resetDataSource posResetSource)`, `AP_NavEKF3/AP_NavEKF3_PosVelFusion.cpp:85-174`. -/
def ResetPosition (s : State) (w : World) (posResetSource : NavEKF3_core.resetDataSource) : State := Id.run do
  let mut s := s
  let mut posResetSource := posResetSource
  if posResetSource == NavEKF3_core.resetDataSource.DEFAULT then
    match AP_NavEKF_Source.getPosXYSource w.EKF3.sources s.core_index with
    | .GPS =>
      posResetSource := NavEKF3_core.resetDataSource.GPS
    | .BEACON =>
      posResetSource := NavEKF3_core.resetDataSource.RNGBCN
    | .EXTNAV =>
      posResetSource := NavEKF3_core.resetDataSource.EXTNAV
    | .NONE | .OPTFLOW | .WHEEL_ENCODER =>
      pure ()
  s := { s with posResetNE.x := s.statesArray[7]! }
  s := { s with posResetNE.y := s.statesArray[8]! }
  s := zeroStatesVarCov s (Int8.toUInt8 (Int32.toInt8 (7 : Int32))) (Int8.toUInt8 (Int32.toInt8 (8 : Int32)))
  if UInt32.toInt32 (NavEKF3_core.AidingMode.toInt s.PV_AidingMode) != UInt32.toInt32 (NavEKF3_core.AidingMode.toInt NavEKF3_core.AidingMode.AID_ABSOLUTE) then
    s := { s with statesArray := s.statesArray.set! 7 s.lastKnownPositionNE.x }
    s := { s with statesArray := s.statesArray.set! 8 s.lastKnownPositionNE.y }
    s := { s with Pmut := s.Pmut.set! 200 (Estimator_lib.sq_AP_ParamT_float_4 w.EKF3._gpsHorizPosNoise) }
    s := { s with Pmut := s.Pmut.set! 175 (s.Pmut[200]!) }
  else
    if (decide (s.imuSampleTime_ms - s.lastTimeGpsReceived_ms < Int32.toUInt32 (250 : Int32))) && (posResetSource == NavEKF3_core.resetDataSource.DEFAULT || posResetSource == NavEKF3_core.resetDataSource.GPS) then
      let mut gps_corrected : NavEKF3_core.gps_elements := s.gpsDataNew
      gps_corrected := CorrectGPSForAntennaOffset s w gps_corrected
      s := { s with last_gps_idx := gps_corrected.sensor_idx }
      let gpsloc : Location.State := Location.init_int32_t3_AltFrame gps_corrected.lat gps_corrected.lng (0 : Int32) Location.AltFrame.ABSOLUTE
      let t'1 := Location.get_distance_NE_ftype s.EKF_origin gpsloc
      s := { s with statesArray := ((s.statesArray.set! 7 t'1.x).set! 8 t'1.y) }
      let tdiff : Int32 := UInt32.toInt32 (s.imuDataDelayed.time_ms - gps_corrected.time_ms)
      let (t'2, _) := Vector2p.op_add_assign ({ x := s.statesArray[7]!, y := s.statesArray[8]! } : Vector2p.State) (Vector2p.op_mul_double (Vector2p.op_mul_double (Vector3p.xy gps_corrected.vel) (Binary64.ofBits 0x3f50624dd2f1a9fc /- 0.001 -/)) (Int32.toBinary64 tdiff))
      s := { s with statesArray := ((s.statesArray.set! 7 t'2.x).set! 8 t'2.y) }
      s := { s with Pmut := s.Pmut.set! 200 (Estimator_lib.sq_double (Estimator_lib.MAX_double_AP_ParamT_float_4 s.gpsPosAccuracy w.EKF3._gpsHorizPosNoise)) }
      s := { s with Pmut := s.Pmut.set! 175 (s.Pmut[200]!) }
  let t'4 : UInt8 := Int8.toUInt8 (Int32.toInt8 (0 : Int32))
  let t'5 : Int32 := UInt32.toInt32 (UInt8.toUInt32 s.imu_buffer_length)
  for i' in [0:(t'5.toInt - (Int.ofNat t'4.toNat)).toNat] do  -- C++ loop bounded by a runtime value (--runtime-loops)
    let i : UInt8 := t'4 + Nat.toUInt8 i'
    s := { s with storedOutput.buffer := s.storedOutput.buffer.set! (UInt8.toNat (UInt32.toUInt8 (UInt8.toUInt32 i))) ({ s.storedOutput.buffer[UInt8.toNat (UInt32.toUInt8 (UInt8.toUInt32 i))]! with position.x := s.statesArray[7]! }) }
    s := { s with storedOutput.buffer := s.storedOutput.buffer.set! (UInt8.toNat (UInt32.toUInt8 (UInt8.toUInt32 i))) ({ s.storedOutput.buffer[UInt8.toNat (UInt32.toUInt8 (UInt8.toUInt32 i))]! with position.y := s.statesArray[8]! }) }
  s := { s with outputDataNew.position.x := s.statesArray[7]! }
  s := { s with outputDataNew.position.y := s.statesArray[8]! }
  s := { s with outputDataDelayed.position.x := s.statesArray[7]! }
  s := { s with outputDataDelayed.position.y := s.statesArray[8]! }
  s := { s with posResetNE.x := s.statesArray[7]! - s.posResetNE.x }
  s := { s with posResetNE.y := s.statesArray[8]! - s.posResetNE.y }
  s := { s with posNEResetCount := s.posNEResetCount + (1 : UInt16) }
  s := { s with posTimeout := false }
  s := { s with lastGpsPosPassTime_ms := s.imuSampleTime_ms }
  return s

/-- C++ `void NavEKF3_core::ResetHeight()`, `AP_NavEKF3/AP_NavEKF3_PosVelFusion.cpp:273-346`. -/
def ResetHeight (s : State) (w : World) : State := Id.run do
  let mut s := s
  s := { s with posResetD := s.statesArray[9]! }
  s := { s with statesArray := s.statesArray.set! 9 (-s.hgtMea) }
  s := { s with outputDataNew.position.z := s.statesArray[9]! }
  s := { s with outputDataDelayed.position.z := s.statesArray[9]! }
  if s.onGround then
    s := { s with terrainState := s.statesArray[9]! + s.rngOnGnd }
  else
    s := { s with terrainState := Estimator_lib.MAX_double2 (s.statesArray[9]! + s.rngOnGnd) s.terrainState }
  let t'1 : UInt8 := Int8.toUInt8 (Int32.toInt8 (0 : Int32))
  let t'2 : Int32 := UInt32.toInt32 (UInt8.toUInt32 s.imu_buffer_length)
  for i' in [0:(t'2.toInt - (Int.ofNat t'1.toNat)).toNat] do  -- C++ loop bounded by a runtime value (--runtime-loops)
    let i : UInt8 := t'1 + Nat.toUInt8 i'
    s := { s with storedOutput.buffer := s.storedOutput.buffer.set! (UInt8.toNat (UInt32.toUInt8 (UInt8.toUInt32 i))) ({ s.storedOutput.buffer[UInt8.toNat (UInt32.toUInt8 (UInt8.toUInt32 i))]! with position.z := s.statesArray[9]! }) }
  s := { s with vertCompFiltState.pos := s.statesArray[9]! }
  s := { s with posResetD := s.statesArray[9]! - s.posResetD }
  s := { s with posDResetCount := s.posDResetCount + (1 : UInt16) }
  s := { s with hgtTimeout := false }
  s := { s with lastHgtPassTime_ms := s.imuSampleTime_ms }
  s := zeroStatesVarCov s (Int8.toUInt8 (Int32.toInt8 (9 : Int32))) (Int8.toUInt8 (Int32.toInt8 (9 : Int32)))
  s := { s with Pmut := s.Pmut.set! 225 s.posDownObsNoise }
  if s.inFlight && (s.gpsIsInUse || s.badIMUdata) && AP_NavEKF_Source.useVelZSource w.EKF3.sources AP_NavEKF_Source.SourceZ.GPS s.core_index && s.gpsDataNew.have_vz && (decide (s.imuSampleTime_ms - s.gpsDataDelayed.time_ms < Int32.toUInt32 (500 : Int32))) then
    s := { s with statesArray := s.statesArray.set! 6 s.gpsDataNew.vel.z }
  else if s.onGround then
    s := { s with statesArray := s.statesArray.set! 6 (Binary64.ofBits 0x0000000000000000 /- 0.0f -/) }
  let t'3 : UInt8 := Int8.toUInt8 (Int32.toInt8 (0 : Int32))
  let t'4 : Int32 := UInt32.toInt32 (UInt8.toUInt32 s.imu_buffer_length)
  for i'2' in [0:(t'4.toInt - (Int.ofNat t'3.toNat)).toNat] do  -- C++ loop bounded by a runtime value (--runtime-loops)
    let i'2 : UInt8 := t'3 + Nat.toUInt8 i'2'
    s := { s with storedOutput.buffer := s.storedOutput.buffer.set! (UInt8.toNat (UInt32.toUInt8 (UInt8.toUInt32 i'2))) ({ s.storedOutput.buffer[UInt8.toNat (UInt32.toUInt8 (UInt8.toUInt32 i'2))]! with velocity.z := s.statesArray[6]! }) }
  s := { s with outputDataNew.velocity.z := s.statesArray[6]! }
  s := { s with outputDataDelayed.velocity.z := s.statesArray[6]! }
  s := { s with vertCompFiltState.vel := s.outputDataNew.velocity.z }
  s := zeroStatesVarCov s (Int8.toUInt8 (Int32.toInt8 (6 : Int32))) (Int8.toUInt8 (Int32.toInt8 (6 : Int32)))
  s := { s with Pmut := s.Pmut.set! 150 (Estimator_lib.sq_AP_ParamT_float_4 w.EKF3._gpsVertVelNoise) }
  s := { s with vertVelVarClipCounter := Int32.toUInt32 (0 : Int32) }
  return s

end NavEKF3_core

namespace NavEKF3_core

/-- C++ `void NavEKF3_core::calcTiltErrorVariance()`, `AP_NavEKF3/AP_NavEKF3_core.cpp:2144-2174`. -/
def calcTiltErrorVariance (s : State) : State := Id.run do
  let mut s := s
  let PS0 : Binary64 := s.statesArray[0]! * s.statesArray[1]! + s.statesArray[2]! * s.statesArray[3]!
  let PS1 : Binary64 := PS0 * s.statesArray[1]!
  let PS2 : Binary64 := Estimator_lib.sq_double s.statesArray[0]! - Estimator_lib.sq_double s.statesArray[1]! - Estimator_lib.sq_double s.statesArray[2]! + Estimator_lib.sq_double s.statesArray[3]!
  let PS3 : Binary64 := PS2 * s.statesArray[0]!
  let PS4 : Binary64 := PS0 * s.statesArray[2]!
  let PS5 : Binary64 := PS2 * s.statesArray[3]!
  let PS6 : Binary64 := PS0 * s.statesArray[3]!
  let PS7 : Binary64 := PS2 * s.statesArray[2]!
  let PS8 : Binary64 := PS0 * s.statesArray[0]!
  let PS9 : Binary64 := PS2 * s.statesArray[1]!
  let PS10 : Binary64 := s.statesArray[0]! * s.statesArray[2]! - s.statesArray[1]! * s.statesArray[3]!
  let PS11 : Binary64 := PS10 * s.statesArray[2]!
  let PS12 : Binary64 := PS10 * s.statesArray[3]!
  let PS13 : Binary64 := PS10 * s.statesArray[0]!
  let PS14 : Binary64 := PS10 * s.statesArray[1]!
  s := { s with tiltErrorVariance := (Binary64.ofBits 0x4010000000000000 /- 4 -/) * s.Pmut[0]! * Estimator_lib.sq_double ((Binary64.ofBits 0x4000000000000000 /- 2 -/) * PS8 - PS9) + (Binary64.ofBits 0x4010000000000000 /- 4 -/) * s.Pmut[25]! * Estimator_lib.sq_double ((Binary64.ofBits 0x4000000000000000 /- 2 -/) * PS1 + PS3) + (Binary64.ofBits 0x4010000000000000 /- 4 -/) * s.Pmut[50]! * Estimator_lib.sq_double ((Binary64.ofBits 0x4000000000000000 /- 2 -/) * PS4 + PS5) + (Binary64.ofBits 0x4010000000000000 /- 4 -/) * s.Pmut[75]! * Estimator_lib.sq_double ((Binary64.ofBits 0xc000000000000000 /- -2 -/) * PS6 + PS7) }
  s := { s with tiltErrorVariance := s.tiltErrorVariance + ((Binary64.ofBits 0x4010000000000000 /- 4 -/) * s.Pmut[0]! * Estimator_lib.sq_double ((Binary64.ofBits 0x4000000000000000 /- 2 -/) * PS13 - PS7) + (Binary64.ofBits 0x4010000000000000 /- 4 -/) * s.Pmut[25]! * Estimator_lib.sq_double ((Binary64.ofBits 0x4000000000000000 /- 2 -/) * PS14 - PS5) + (Binary64.ofBits 0x4010000000000000 /- 4 -/) * s.Pmut[50]! * Estimator_lib.sq_double ((Binary64.ofBits 0x4000000000000000 /- 2 -/) * PS11 + PS3) + (Binary64.ofBits 0x4010000000000000 /- 4 -/) * s.Pmut[75]! * Estimator_lib.sq_double ((Binary64.ofBits 0x4000000000000000 /- 2 -/) * PS12 + PS9)) }
  s := { s with tiltErrorVariance := s.tiltErrorVariance + ((Binary64.ofBits 0x4030000000000000 /- 16 -/) * s.Pmut[0]! * Estimator_lib.sq_double (PS14 - PS4) + (Binary64.ofBits 0x4030000000000000 /- 16 -/) * s.Pmut[25]! * Estimator_lib.sq_double (PS13 + PS6) + (Binary64.ofBits 0x4030000000000000 /- 16 -/) * s.Pmut[50]! * Estimator_lib.sq_double (-PS12 + PS8) + (Binary64.ofBits 0x4030000000000000 /- 16 -/) * s.Pmut[75]! * Estimator_lib.sq_double (PS1 + PS11)) }
  s := { s with tiltErrorVariance := Estimator_lib.constrain_value_line_double s.tiltErrorVariance (Binary64.ofBits 0x0000000000000000 /- (double)0 -/) (Binary32.toBinary64 (Estimator_lib.sq_float (Estimator_lib.radians_float (Binary32.ofBits 0x41f00000 /- 30 -/)))) (Int32.toUInt32 (2173 : Int32)) }
  return s

/-- C++ `void NavEKF3_core::CovariancePrediction(Vector3F * rotVarVecPtr)`, `AP_NavEKF3/AP_NavEKF3_core.cpp:996-1791`. -/
def CovariancePrediction (s : State) (w : World) (rotVarVecPtr'given : Bool) (rotVarVecPtr : Vector3p.State) : State × World × Vector3p.State := Id.run do
  let mut s := s
  let mut w := w
  let mut rotVarVecPtr := rotVarVecPtr
  let mut daxVar : Binary64 := (Binary64.ofBits 0x0000000000000000 /- 0.0 -/)  -- uninitialized in C++; assigned before every read
  let mut dayVar : Binary64 := (Binary64.ofBits 0x0000000000000000 /- 0.0 -/)  -- uninitialized in C++; assigned before every read
  let mut dazVar : Binary64 := (Binary64.ofBits 0x0000000000000000 /- 0.0 -/)  -- uninitialized in C++; assigned before every read
  let mut dvxVar : Binary64 := (Binary64.ofBits 0x0000000000000000 /- 0.0 -/)  -- uninitialized in C++; assigned before every read
  let mut dvyVar : Binary64 := (Binary64.ofBits 0x0000000000000000 /- 0.0 -/)  -- uninitialized in C++; assigned before every read
  let mut dvzVar : Binary64 := (Binary64.ofBits 0x0000000000000000 /- 0.0 -/)  -- uninitialized in C++; assigned before every read
  let mut dvx : Binary64 := (Binary64.ofBits 0x0000000000000000 /- 0.0 -/)  -- uninitialized in C++; assigned before every read
  let mut dvy : Binary64 := (Binary64.ofBits 0x0000000000000000 /- 0.0 -/)  -- uninitialized in C++; assigned before every read
  let mut dvz : Binary64 := (Binary64.ofBits 0x0000000000000000 /- 0.0 -/)  -- uninitialized in C++; assigned before every read
  let mut dax : Binary64 := (Binary64.ofBits 0x0000000000000000 /- 0.0 -/)  -- uninitialized in C++; assigned before every read
  let mut day : Binary64 := (Binary64.ofBits 0x0000000000000000 /- 0.0 -/)  -- uninitialized in C++; assigned before every read
  let mut daz : Binary64 := (Binary64.ofBits 0x0000000000000000 /- 0.0 -/)  -- uninitialized in C++; assigned before every read
  let mut q0 : Binary64 := (Binary64.ofBits 0x0000000000000000 /- 0.0 -/)  -- uninitialized in C++; assigned before every read
  let mut q1 : Binary64 := (Binary64.ofBits 0x0000000000000000 /- 0.0 -/)  -- uninitialized in C++; assigned before every read
  let mut q2 : Binary64 := (Binary64.ofBits 0x0000000000000000 /- 0.0 -/)  -- uninitialized in C++; assigned before every read
  let mut q3 : Binary64 := (Binary64.ofBits 0x0000000000000000 /- 0.0 -/)  -- uninitialized in C++; assigned before every read
  let mut dax_b : Binary64 := (Binary64.ofBits 0x0000000000000000 /- 0.0 -/)  -- uninitialized in C++; assigned before every read
  let mut day_b : Binary64 := (Binary64.ofBits 0x0000000000000000 /- 0.0 -/)  -- uninitialized in C++; assigned before every read
  let mut daz_b : Binary64 := (Binary64.ofBits 0x0000000000000000 /- 0.0 -/)  -- uninitialized in C++; assigned before every read
  let mut dvx_b : Binary64 := (Binary64.ofBits 0x0000000000000000 /- 0.0 -/)  -- uninitialized in C++; assigned before every read
  let mut dvy_b : Binary64 := (Binary64.ofBits 0x0000000000000000 /- 0.0 -/)  -- uninitialized in C++; assigned before every read
  let mut dvz_b : Binary64 := (Binary64.ofBits 0x0000000000000000 /- 0.0 -/)  -- uninitialized in C++; assigned before every read
  s := { s with dt := Estimator_lib.constrain_value_line_double ((Binary64.ofBits 0x3fe0000000000000 /- (double)1/2 -/) * (s.imuDataDelayed.delAngDT + s.imuDataDelayed.delVelDT)) ((Binary64.ofBits 0x3fe0000000000000 /- (double)1/2 -/) * s.dtEkfAvg) ((Binary64.ofBits 0x4000000000000000 /- (double)2 -/) * s.dtEkfAvg) (Int32.toUInt32 (1023 : Int32)) }
  let alpha : Binary64 := (Binary64.ofBits 0x3fb99999a0000000 /- 0.1f -/) * s.dt
  s := { s with hgtRate := s.hgtRate * ((Binary64.ofBits 0x3ff0000000000000 /- 1.0f -/) - alpha) - s.statesArray[6]! * alpha }
  let mut processNoiseVariance : Array Binary64 := Array.replicate 14 (Binary64.ofBits 0x0000000000000000 /- 0.0 -/)
  if !s.inhibitDelAngBiasStates then
    let dAngBiasVar : Binary64 := Estimator_lib.sq_double (Estimator_lib.sq_double s.dt * Estimator_lib.constrain_value_line_double (AP_ParamT_float_4.op_to_double w.EKF3._gyroBiasProcessNoise) (Binary64.ofBits 0x0000000000000000 /- (double)0 -/) (Binary64.ofBits 0x3ff0000000000000 /- (double)1 -/) (Int32.toUInt32 (1035 : Int32)))
    for i' in [0:3] do
      let i : UInt8 := Nat.toUInt8 i'
      processNoiseVariance := processNoiseVariance.set! (UInt8.toNat i) dAngBiasVar
  if !s.inhibitDelVelBiasStates then
    let dVelBiasVar : Binary64 := Estimator_lib.sq_double (Estimator_lib.sq_double s.dt * Estimator_lib.constrain_value_line_double (AP_ParamT_float_4.op_to_double w.EKF3._accelBiasProcessNoise) (Binary64.ofBits 0x0000000000000000 /- (double)0 -/) (Binary64.ofBits 0x3ff0000000000000 /- (double)1 -/) (Int32.toUInt32 (1041 : Int32)))
    for i'2' in [3:6] do
      let i'2 : UInt8 := Nat.toUInt8 i'2'
      processNoiseVariance := processNoiseVariance.set! (UInt8.toNat i'2) dVelBiasVar
  if !s.inhibitMagStates && s.lastInhibitMagStates then
    s := { s with needMagBodyVarReset := true }
    s := { s with needEarthBodyVarReset := true }
  if s.needMagBodyVarReset then
    s := { s with needMagBodyVarReset := false }
    s := zeroStatesVarCov s (Int8.toUInt8 (Int32.toInt8 (19 : Int32))) (Int8.toUInt8 (Int32.toInt8 (21 : Int32)))
    s := { s with Pmut := s.Pmut.set! 475 (Estimator_lib.sq_AP_ParamT_float_4 w.EKF3._magNoise) }
    s := { s with Pmut := s.Pmut.set! 500 (s.Pmut[475]!) }
    s := { s with Pmut := s.Pmut.set! 525 (s.Pmut[475]!) }
  if s.needEarthBodyVarReset then
    s := { s with needEarthBodyVarReset := false }
    s := zeroStatesVarCov s (Int8.toUInt8 (Int32.toInt8 (16 : Int32))) (Int8.toUInt8 (Int32.toInt8 (18 : Int32)))
    s := { s with Pmut := s.Pmut.set! 400 (Estimator_lib.sq_AP_ParamT_float_4 w.EKF3._magNoise) }
    s := { s with Pmut := s.Pmut.set! 425 (s.Pmut[400]!) }
    s := { s with Pmut := s.Pmut.set! 450 (s.Pmut[400]!) }
    let (t'1, t'2) := FuseDeclination s w (Binary32.toBinary64 (Estimator_lib.radians_float (Binary32.ofBits 0x41a00000 /- 20.0f -/)))
    w := t'2
    s := t'1
  if !s.inhibitMagStates then
    let magEarthVar : Binary64 := Estimator_lib.sq_double (s.dt * Estimator_lib.constrain_value_line_double (AP_ParamT_float_4.op_to_double w.EKF3._magEarthProcessNoise) (Binary64.ofBits 0x0000000000000000 /- (double)0 -/) (Binary64.ofBits 0x3ff0000000000000 /- (double)1 -/) (Int32.toUInt32 (1075 : Int32)))
    let magBodyVar : Binary64 := Estimator_lib.sq_double (s.dt * Estimator_lib.constrain_value_line_double (AP_ParamT_float_4.op_to_double w.EKF3._magBodyProcessNoise) (Binary64.ofBits 0x0000000000000000 /- (double)0 -/) (Binary64.ofBits 0x3ff0000000000000 /- (double)1 -/) (Int32.toUInt32 (1076 : Int32)))
    for i'3' in [6:9] do
      let i'3 : UInt8 := Nat.toUInt8 i'3'
      processNoiseVariance := processNoiseVariance.set! (UInt8.toNat i'3) magEarthVar
    for i'4' in [9:12] do
      let i'4 : UInt8 := Nat.toUInt8 i'4'
      processNoiseVariance := processNoiseVariance.set! (UInt8.toNat i'4) magBodyVar
  s := { s with lastInhibitMagStates := s.inhibitMagStates }
  if !s.inhibitWindStates then
    let isDragFusionDeadReckoning : Bool := (s.filterStatus >>> 18 &&& 1 != 0) && !s.dragTimeout
    let newTreatWindStatesAsTruth : Bool := isDragFusionDeadReckoning || !s.windStateIsObservable
    if newTreatWindStatesAsTruth then
      s := { s with treatWindStatesAsTruth := true }
      s := zeroStatesVarCov s (Int8.toUInt8 (Int32.toInt8 (22 : Int32))) (Int8.toUInt8 (Int32.toInt8 (23 : Int32)))
    else
      if s.treatWindStatesAsTruth then
        s := { s with treatWindStatesAsTruth := false }
        if s.windStateIsObservable then
          s := { s with Pmut := s.Pmut.set! 550 (Binary64.ofBits 0x4079000000000000 /- (double)400 -/) }
          s := { s with Pmut := s.Pmut.set! 575 (s.Pmut[550]!) }
      let mut windVelVar : Binary64 := Estimator_lib.sq_double (s.dt * Estimator_lib.constrain_value_line_double (AP_ParamT_float_4.op_to_double w.EKF3._windVelProcessNoise) (Binary64.ofBits 0x0000000000000000 /- (double)0 -/) (Binary64.ofBits 0x3ff0000000000000 /- (double)1 -/) (Int32.toUInt32 (1096 : Int32)) * ((Binary64.ofBits 0x3ff0000000000000 /- 1.0f -/) + Estimator_lib.constrain_value_line_double (AP_ParamT_float_4.op_to_double w.EKF3._wndVarHgtRateScale) (Binary64.ofBits 0x0000000000000000 /- (double)0 -/) (Binary64.ofBits 0x3ff0000000000000 /- (double)1 -/) (Int32.toUInt32 (1096 : Int32)) * Binary64.abs s.hgtRate))
      if !s.tas.dataDelayed.allowFusion then
        windVelVar := windVelVar * (Binary64.ofBits 0x4024000000000000 /- 10.0f -/)
      for i'5' in [12:14] do
        let i'5 : UInt8 := Nat.toUInt8 i'5'
        processNoiseVariance := processNoiseVariance.set! (UInt8.toNat i'5) windVelVar
  dvx := s.imuDataDelayed.delVel.x
  dvy := s.imuDataDelayed.delVel.y
  dvz := s.imuDataDelayed.delVel.z
  dax := s.imuDataDelayed.delAng.x
  day := s.imuDataDelayed.delAng.y
  daz := s.imuDataDelayed.delAng.z
  q0 := s.statesArray[0]!
  q1 := s.statesArray[1]!
  q2 := s.statesArray[2]!
  q3 := s.statesArray[3]!
  dax_b := s.statesArray[10]!
  day_b := s.statesArray[11]!
  daz_b := s.statesArray[12]!
  dvx_b := s.statesArray[13]!
  dvy_b := s.statesArray[14]!
  dvz_b := s.statesArray[15]!
  let mut quatCovResetOnly : Bool := false
  if rotVarVecPtr'given then
    let R_ef : Matrix3_double.State := Matrix3_double.init_double9 rotVarVecPtr.x (Binary64.ofBits 0x0000000000000000 /- 0.0f -/) (Binary64.ofBits 0x0000000000000000 /- 0.0f -/) (Binary64.ofBits 0x0000000000000000 /- 0.0f -/) rotVarVecPtr.y (Binary64.ofBits 0x0000000000000000 /- 0.0f -/) (Binary64.ofBits 0x0000000000000000 /- 0.0f -/) (Binary64.ofBits 0x0000000000000000 /- 0.0f -/) rotVarVecPtr.z
    let mut Tnb : Matrix3_double.State := Matrix3_double.init_void
    Tnb := QuaternionT_double.rotation_matrix_Matrix3_double (QuaternionT_double.inverse ({ q1 := s.statesArray[0]!, q2 := s.statesArray[1]!, q3 := s.statesArray[2]!, q4 := s.statesArray[3]! } : QuaternionT_double.State)) Tnb
    let R_bf : Matrix3_double.State := Matrix3_double.op_mul_Matrix3_double (Matrix3_double.op_mul_Matrix3_double Tnb R_ef) (Matrix3_double.transposed Tnb)
    daxVar := R_bf.a.x
    dayVar := R_bf.b.y
    dazVar := R_bf.c.z
    quatCovResetOnly := true
    s := zeroStatesVarCov s (Int8.toUInt8 (Int32.toInt8 (0 : Int32))) (Int8.toUInt8 (Int32.toInt8 (3 : Int32)))
  else
    let _gyrNoise : Binary64 := Estimator_lib.constrain_value_line_double (AP_ParamT_float_4.op_to_double w.EKF3._gyrNoise) (Binary64.ofBits 0x0000000000000000 /- (double)0 -/) (Binary64.ofBits 0x3ff0000000000000 /- (double)1 -/) (Int32.toUInt32 (1143 : Int32))
    dazVar := Estimator_lib.sq_double (s.dt * _gyrNoise)
    dayVar := dazVar
    daxVar := dayVar
  let _accNoise : Binary64 := if s.badIMUdata then (Binary64.ofBits 0x4014000000000000 /- (double)5 -/) else Estimator_lib.constrain_value_line_double (AP_ParamT_float_4.op_to_double w.EKF3._accNoise) (Binary64.ofBits 0x0000000000000000 /- (double)0 -/) (Binary64.ofBits 0x4014000000000000 /- (double)5 -/) (Int32.toUInt32 (1146 : Int32))
  dvzVar := Estimator_lib.sq_double (s.dt * _accNoise)
  dvyVar := dvzVar
  dvxVar := dvyVar
  if !s.inhibitDelVelBiasStates then
    for stateIndex' in [13:16] do
      let stateIndex : UInt8 := Nat.toUInt8 stateIndex'
      let index : UInt8 := Int8.toUInt8 (Int32.toInt8 (UInt32.toInt32 (UInt8.toUInt32 stateIndex) - (13 : Int32)))
      let is_bias_observable : Bool := (decide (Binary64.abs (match UInt8.toNat index with | 0 => s.prevTnb.a | 1 => s.prevTnb.b | _ => s.prevTnb.c).z > (Binary64.ofBits 0x3fe99999a0000000 /- 0.8f -/)) && s.onGroundNotMoving) || !s.onGround
      if !is_bias_observable && !s.dvelBiasAxisInhibit[UInt8.toNat index]! then
        let t'3 := s.Pmut[UInt8.toNat stateIndex * 24 + UInt8.toNat stateIndex]!
        s := (match UInt8.toNat index with | 0 => { s with dvelBiasAxisVarPrev.x := t'3 } | 1 => { s with dvelBiasAxisVarPrev.y := t'3 } | _ => { s with dvelBiasAxisVarPrev.z := t'3 })
        s := { s with dvelBiasAxisInhibit := s.dvelBiasAxisInhibit.set! (UInt8.toNat index) true }
      else if is_bias_observable && s.dvelBiasAxisInhibit[UInt8.toNat index]! then
        s := { s with Pmut := s.Pmut.set! (UInt8.toNat stateIndex * 24 + UInt8.toNat stateIndex) (match UInt8.toNat index with | 0 => s.dvelBiasAxisVarPrev.x | 1 => s.dvelBiasAxisVarPrev.y | _ => s.dvelBiasAxisVarPrev.z) }
        s := { s with dvelBiasAxisInhibit := s.dvelBiasAxisInhibit.set! (UInt8.toNat index) false }
  let PS0 : Binary64 := Estimator_lib.sq_double q1
  let PS1 : Binary64 := (Binary64.ofBits 0x3fd0000000000000 /- 0.25F -/) * daxVar
  let PS2 : Binary64 := Estimator_lib.sq_double q2
  let PS3 : Binary64 := (Binary64.ofBits 0x3fd0000000000000 /- 0.25F -/) * dayVar
  let PS4 : Binary64 := Estimator_lib.sq_double q3
  let PS5 : Binary64 := (Binary64.ofBits 0x3fd0000000000000 /- 0.25F -/) * dazVar
  let PS6 : Binary64 := (Binary64.ofBits 0x3fe0000000000000 /- 0.5F -/) * q1
  let PS7 : Binary64 := (Binary64.ofBits 0x3fe0000000000000 /- 0.5F -/) * q2
  let PS8 : Binary64 := PS7 * s.Pmut[251]!
  let PS9 : Binary64 := (Binary64.ofBits 0x3fe0000000000000 /- 0.5F -/) * q3
  let PS10 : Binary64 := PS9 * s.Pmut[252]!
  let PS11 : Binary64 := (Binary64.ofBits 0x3fe0000000000000 /- 0.5F -/) * dax - (Binary64.ofBits 0x3fe0000000000000 /- 0.5F -/) * dax_b
  let PS12 : Binary64 := (Binary64.ofBits 0x3fe0000000000000 /- 0.5F -/) * day - (Binary64.ofBits 0x3fe0000000000000 /- 0.5F -/) * day_b
  let PS13 : Binary64 := (Binary64.ofBits 0x3fe0000000000000 /- 0.5F -/) * daz - (Binary64.ofBits 0x3fe0000000000000 /- 0.5F -/) * daz_b
  let PS14 : Binary64 := PS10 - PS11 * s.Pmut[34]! - PS12 * s.Pmut[58]! - PS13 * s.Pmut[82]! + PS6 * s.Pmut[250]! + PS8 + s.Pmut[10]!
  let PS15 : Binary64 := PS6 * s.Pmut[251]!
  let PS16 : Binary64 := PS9 * s.Pmut[276]!
  let PS17 : Binary64 := -PS11 * s.Pmut[35]! - PS12 * s.Pmut[59]! - PS13 * s.Pmut[83]! + PS15 + PS16 + PS7 * s.Pmut[275]! + s.Pmut[11]!
  let PS18 : Binary64 := PS6 * s.Pmut[252]!
  let PS19 : Binary64 := PS7 * s.Pmut[276]!
  let PS20 : Binary64 := -PS11 * s.Pmut[36]! - PS12 * s.Pmut[60]! - PS13 * s.Pmut[84]! + PS18 + PS19 + PS9 * s.Pmut[300]! + s.Pmut[12]!
  let PS21 : Binary64 := PS12 * s.Pmut[26]!
  let PS22 : Binary64 := -PS13 * s.Pmut[27]!
  let PS23 : Binary64 := -PS11 * s.Pmut[25]! - PS21 + PS22 + PS6 * s.Pmut[34]! + PS7 * s.Pmut[35]! + PS9 * s.Pmut[36]! + s.Pmut[1]!
  let PS24 : Binary64 := -PS11 * s.Pmut[26]!
  let PS25 : Binary64 := PS13 * s.Pmut[51]!
  let PS26 : Binary64 := -PS12 * s.Pmut[50]! + PS24 - PS25 + PS6 * s.Pmut[58]! + PS7 * s.Pmut[59]! + PS9 * s.Pmut[60]! + s.Pmut[2]!
  let PS27 : Binary64 := PS11 * s.Pmut[27]!
  let PS28 : Binary64 := -PS12 * s.Pmut[51]!
  let PS29 : Binary64 := -PS13 * s.Pmut[75]! - PS27 + PS28 + PS6 * s.Pmut[82]! + PS7 * s.Pmut[83]! + PS9 * s.Pmut[84]! + s.Pmut[3]!
  let PS30 : Binary64 := PS11 * s.Pmut[1]!
  let PS31 : Binary64 := PS12 * s.Pmut[2]!
  let PS32 : Binary64 := PS13 * s.Pmut[3]!
  let PS33 : Binary64 := -PS30 - PS31 - PS32 + PS6 * s.Pmut[10]! + PS7 * s.Pmut[11]! + PS9 * s.Pmut[12]! + s.Pmut[0]!
  let PS34 : Binary64 := (Binary64.ofBits 0x3fe0000000000000 /- 0.5F -/) * q0
  let PS35 : Binary64 := q2 * q3
  let PS36 : Binary64 := q0 * q1
  let PS37 : Binary64 := q1 * q3
  let PS38 : Binary64 := q0 * q2
  let PS39 : Binary64 := q1 * q2
  let PS40 : Binary64 := q0 * q3
  let PS41 : Binary64 := (Binary64.ofBits 0x4000000000000000 /- 2 -/) * PS2
  let PS42 : Binary64 := (Binary64.ofBits 0x4000000000000000 /- 2 -/) * PS4 - (Binary64.ofBits 0x3ff0000000000000 /- 1 -/)
  let PS43 : Binary64 := PS41 + PS42
  let PS44 : Binary64 := -PS11 * s.Pmut[37]! - PS12 * s.Pmut[61]! - PS13 * s.Pmut[85]! + PS6 * s.Pmut[253]! + PS7 * s.Pmut[277]! + PS9 * s.Pmut[301]! + s.Pmut[13]!
  let PS45 : Binary64 := PS37 + PS38
  let PS46 : Binary64 := -PS11 * s.Pmut[39]! - PS12 * s.Pmut[63]! - PS13 * s.Pmut[87]! + PS6 * s.Pmut[255]! + PS7 * s.Pmut[279]! + PS9 * s.Pmut[303]! + s.Pmut[15]!
  let PS47 : Binary64 := (Binary64.ofBits 0x4000000000000000 /- 2 -/) * PS46
  let PS48 : Binary64 := dvy - dvy_b
  let PS49 : Binary64 := PS48 * q0
  let PS50 : Binary64 := dvz - dvz_b
  let PS51 : Binary64 := PS50 * q1
  let PS52 : Binary64 := dvx - dvx_b
  let PS53 : Binary64 := PS52 * q3
  let PS54 : Binary64 := PS49 - PS51 + (Binary64.ofBits 0x4000000000000000 /- 2 -/) * PS53
  let PS55 : Binary64 := (Binary64.ofBits 0x4000000000000000 /- 2 -/) * PS29
  let PS56 : Binary64 := -PS39 + PS40
  let PS57 : Binary64 := -PS11 * s.Pmut[38]! - PS12 * s.Pmut[62]! - PS13 * s.Pmut[86]! + PS6 * s.Pmut[254]! + PS7 * s.Pmut[278]! + PS9 * s.Pmut[302]! + s.Pmut[14]!
  let PS58 : Binary64 := (Binary64.ofBits 0x4000000000000000 /- 2 -/) * PS57
  let PS59 : Binary64 := PS48 * q2
  let PS60 : Binary64 := PS50 * q3
  let PS61 : Binary64 := PS59 + PS60
  let PS62 : Binary64 := (Binary64.ofBits 0x4000000000000000 /- 2 -/) * PS23
  let PS63 : Binary64 := PS50 * q2
  let PS64 : Binary64 := PS48 * q3
  let PS65 : Binary64 := -PS64
  let PS66 : Binary64 := PS63 + PS65
  let PS67 : Binary64 := (Binary64.ofBits 0x4000000000000000 /- 2 -/) * PS33
  let PS68 : Binary64 := PS50 * q0
  let PS69 : Binary64 := PS48 * q1
  let PS70 : Binary64 := PS52 * q2
  let PS71 : Binary64 := PS68 + PS69 - (Binary64.ofBits 0x4000000000000000 /- 2 -/) * PS70
  let PS72 : Binary64 := (Binary64.ofBits 0x4000000000000000 /- 2 -/) * PS26
  let PS73 : Binary64 := -PS11 * s.Pmut[28]! - PS12 * s.Pmut[52]! - PS13 * s.Pmut[76]! + PS6 * s.Pmut[106]! + PS7 * s.Pmut[107]! + PS9 * s.Pmut[108]! + s.Pmut[4]!
  let PS74 : Binary64 := (Binary64.ofBits 0x4000000000000000 /- 2 -/) * PS0
  let PS75 : Binary64 := PS42 + PS74
  let PS76 : Binary64 := PS39 + PS40
  let PS77 : Binary64 := (Binary64.ofBits 0x4000000000000000 /- 2 -/) * PS44
  let PS78 : Binary64 := PS51 - PS53
  let PS79 : Binary64 := -PS70
  let PS80 : Binary64 := PS68 + (Binary64.ofBits 0x4000000000000000 /- 2 -/) * PS69 + PS79
  let PS81 : Binary64 := -PS35 + PS36
  let PS82 : Binary64 := PS52 * q1
  let PS83 : Binary64 := PS60 + PS82
  let PS84 : Binary64 := PS52 * q0
  let PS85 : Binary64 := PS63 - (Binary64.ofBits 0x4000000000000000 /- 2 -/) * PS64 + PS84
  let PS86 : Binary64 := -PS11 * s.Pmut[29]! - PS12 * s.Pmut[53]! - PS13 * s.Pmut[77]! + PS6 * s.Pmut[130]! + PS7 * s.Pmut[131]! + PS9 * s.Pmut[132]! + s.Pmut[5]!
  let PS87 : Binary64 := PS41 + PS74 - (Binary64.ofBits 0x3ff0000000000000 /- 1 -/)
  let PS88 : Binary64 := PS35 + PS36
  let PS89 : Binary64 := (Binary64.ofBits 0x4000000000000000 /- 2 -/) * PS63 + PS65 + PS84
  let PS90 : Binary64 := -PS37 + PS38
  let PS91 : Binary64 := PS59 + PS82
  let PS92 : Binary64 := PS69 + PS79
  let PS93 : Binary64 := PS49 - (Binary64.ofBits 0x4000000000000000 /- 2 -/) * PS51 + PS53
  let PS94 : Binary64 := -PS11 * s.Pmut[30]! - PS12 * s.Pmut[54]! - PS13 * s.Pmut[78]! + PS6 * s.Pmut[154]! + PS7 * s.Pmut[155]! + PS9 * s.Pmut[156]! + s.Pmut[6]!
  let PS95 : Binary64 := Estimator_lib.sq_double q0
  let PS96 : Binary64 := -PS34 * s.Pmut[251]!
  let PS97 : Binary64 := PS11 * s.Pmut[11]! - PS12 * s.Pmut[83]! + PS13 * s.Pmut[59]! - PS19 + PS9 * s.Pmut[275]! + PS96 + s.Pmut[35]!
  let PS98 : Binary64 := PS13 * s.Pmut[2]!
  let PS99 : Binary64 := PS12 * s.Pmut[3]!
  let PS100 : Binary64 := PS11 * s.Pmut[0]! - PS34 * s.Pmut[10]! - PS7 * s.Pmut[12]! + PS9 * s.Pmut[11]! + PS98 - PS99 + s.Pmut[1]!
  let PS101 : Binary64 := PS11 * s.Pmut[2]!
  let PS102 : Binary64 := PS101 + PS13 * s.Pmut[50]! + PS28 - PS34 * s.Pmut[58]! - PS7 * s.Pmut[60]! + PS9 * s.Pmut[59]! + s.Pmut[26]!
  let PS103 : Binary64 := PS9 * s.Pmut[251]!
  let PS104 : Binary64 := PS7 * s.Pmut[252]!
  let PS105 : Binary64 := PS103 - PS104 + PS11 * s.Pmut[10]! - PS12 * s.Pmut[82]! + PS13 * s.Pmut[58]! - PS34 * s.Pmut[250]! + s.Pmut[34]!
  let PS106 : Binary64 := -PS34 * s.Pmut[252]!
  let PS107 : Binary64 := PS106 + PS11 * s.Pmut[12]! - PS12 * s.Pmut[84]! + PS13 * s.Pmut[60]! + PS16 - PS7 * s.Pmut[300]! + s.Pmut[36]!
  let PS108 : Binary64 := PS11 * s.Pmut[3]!
  let PS109 : Binary64 := PS108 - PS12 * s.Pmut[75]! + PS25 - PS34 * s.Pmut[82]! - PS7 * s.Pmut[84]! + PS9 * s.Pmut[83]! + s.Pmut[27]!
  let PS110 : Binary64 := PS13 * s.Pmut[26]!
  let PS111 : Binary64 := PS12 * s.Pmut[27]!
  let PS112 : Binary64 := PS110 - PS111 + PS30 - PS34 * s.Pmut[34]! - PS7 * s.Pmut[36]! + PS9 * s.Pmut[35]! + s.Pmut[25]!
  let PS113 : Binary64 := PS11 * s.Pmut[13]! - PS12 * s.Pmut[85]! + PS13 * s.Pmut[61]! - PS34 * s.Pmut[253]! - PS7 * s.Pmut[301]! + PS9 * s.Pmut[277]! + s.Pmut[37]!
  let PS114 : Binary64 := PS11 * s.Pmut[15]! - PS12 * s.Pmut[87]! + PS13 * s.Pmut[63]! - PS34 * s.Pmut[255]! - PS7 * s.Pmut[303]! + PS9 * s.Pmut[279]! + s.Pmut[39]!
  let PS115 : Binary64 := (Binary64.ofBits 0x4000000000000000 /- 2 -/) * PS114
  let PS116 : Binary64 := (Binary64.ofBits 0x4000000000000000 /- 2 -/) * PS109
  let PS117 : Binary64 := PS11 * s.Pmut[14]! - PS12 * s.Pmut[86]! + PS13 * s.Pmut[62]! - PS34 * s.Pmut[254]! - PS7 * s.Pmut[302]! + PS9 * s.Pmut[278]! + s.Pmut[38]!
  let PS118 : Binary64 := (Binary64.ofBits 0x4000000000000000 /- 2 -/) * PS117
  let PS119 : Binary64 := (Binary64.ofBits 0x4000000000000000 /- 2 -/) * PS112
  let PS120 : Binary64 := (Binary64.ofBits 0x4000000000000000 /- 2 -/) * PS100
  let PS121 : Binary64 := (Binary64.ofBits 0x4000000000000000 /- 2 -/) * PS102
  let PS122 : Binary64 := PS11 * s.Pmut[4]! - PS12 * s.Pmut[76]! + PS13 * s.Pmut[52]! - PS34 * s.Pmut[106]! - PS7 * s.Pmut[108]! + PS9 * s.Pmut[107]! + s.Pmut[28]!
  let PS123 : Binary64 := (Binary64.ofBits 0x4000000000000000 /- 2 -/) * PS113
  let PS124 : Binary64 := PS11 * s.Pmut[5]! - PS12 * s.Pmut[77]! + PS13 * s.Pmut[53]! - PS34 * s.Pmut[130]! - PS7 * s.Pmut[132]! + PS9 * s.Pmut[131]! + s.Pmut[29]!
  let PS125 : Binary64 := PS11 * s.Pmut[6]! - PS12 * s.Pmut[78]! + PS13 * s.Pmut[54]! - PS34 * s.Pmut[154]! - PS7 * s.Pmut[156]! + PS9 * s.Pmut[155]! + s.Pmut[30]!
  let PS126 : Binary64 := -PS34 * s.Pmut[276]!
  let PS127 : Binary64 := -PS10 + PS11 * s.Pmut[84]! + PS12 * s.Pmut[12]! + PS126 - PS13 * s.Pmut[36]! + PS6 * s.Pmut[300]! + s.Pmut[60]!
  let PS128 : Binary64 := PS11 * s.Pmut[75]! + PS22 - PS34 * s.Pmut[83]! + PS6 * s.Pmut[84]! - PS9 * s.Pmut[82]! + PS99 + s.Pmut[51]!
  let PS129 : Binary64 := PS13 * s.Pmut[1]!
  let PS130 : Binary64 := PS108 + PS12 * s.Pmut[0]! - PS129 - PS34 * s.Pmut[11]! + PS6 * s.Pmut[12]! - PS9 * s.Pmut[10]! + s.Pmut[2]!
  let PS131 : Binary64 := PS6 * s.Pmut[276]!
  let PS132 : Binary64 := -PS103 + PS11 * s.Pmut[83]! + PS12 * s.Pmut[11]! - PS13 * s.Pmut[35]! + PS131 - PS34 * s.Pmut[275]! + s.Pmut[59]!
  let PS133 : Binary64 := PS11 * s.Pmut[82]! + PS12 * s.Pmut[10]! - PS13 * s.Pmut[34]! + PS18 - PS9 * s.Pmut[250]! + PS96 + s.Pmut[58]!
  let PS134 : Binary64 := PS12 * s.Pmut[1]!
  let PS135 : Binary64 := -PS13 * s.Pmut[25]! + PS134 + PS27 - PS34 * s.Pmut[35]! + PS6 * s.Pmut[36]! - PS9 * s.Pmut[34]! + s.Pmut[26]!
  let PS136 : Binary64 := PS11 * s.Pmut[51]!
  let PS137 : Binary64 := -PS110 + PS136 + PS31 - PS34 * s.Pmut[59]! + PS6 * s.Pmut[60]! - PS9 * s.Pmut[58]! + s.Pmut[50]!
  let PS138 : Binary64 := PS11 * s.Pmut[85]! + PS12 * s.Pmut[13]! - PS13 * s.Pmut[37]! - PS34 * s.Pmut[277]! + PS6 * s.Pmut[301]! - PS9 * s.Pmut[253]! + s.Pmut[61]!
  let PS139 : Binary64 := PS11 * s.Pmut[87]! + PS12 * s.Pmut[15]! - PS13 * s.Pmut[39]! - PS34 * s.Pmut[279]! + PS6 * s.Pmut[303]! - PS9 * s.Pmut[255]! + s.Pmut[63]!
  let PS140 : Binary64 := (Binary64.ofBits 0x4000000000000000 /- 2 -/) * PS139
  let PS141 : Binary64 := (Binary64.ofBits 0x4000000000000000 /- 2 -/) * PS128
  let PS142 : Binary64 := PS11 * s.Pmut[86]! + PS12 * s.Pmut[14]! - PS13 * s.Pmut[38]! - PS34 * s.Pmut[278]! + PS6 * s.Pmut[302]! - PS9 * s.Pmut[254]! + s.Pmut[62]!
  let PS143 : Binary64 := (Binary64.ofBits 0x4000000000000000 /- 2 -/) * PS142
  let PS144 : Binary64 := (Binary64.ofBits 0x4000000000000000 /- 2 -/) * PS135
  let PS145 : Binary64 := (Binary64.ofBits 0x4000000000000000 /- 2 -/) * PS130
  let PS146 : Binary64 := (Binary64.ofBits 0x4000000000000000 /- 2 -/) * PS137
  let PS147 : Binary64 := PS11 * s.Pmut[76]! + PS12 * s.Pmut[4]! - PS13 * s.Pmut[28]! - PS34 * s.Pmut[107]! + PS6 * s.Pmut[108]! - PS9 * s.Pmut[106]! + s.Pmut[52]!
  let PS148 : Binary64 := (Binary64.ofBits 0x4000000000000000 /- 2 -/) * PS138
  let PS149 : Binary64 := PS11 * s.Pmut[77]! + PS12 * s.Pmut[5]! - PS13 * s.Pmut[29]! - PS34 * s.Pmut[131]! + PS6 * s.Pmut[132]! - PS9 * s.Pmut[130]! + s.Pmut[53]!
  let PS150 : Binary64 := PS11 * s.Pmut[78]! + PS12 * s.Pmut[6]! - PS13 * s.Pmut[30]! - PS34 * s.Pmut[155]! + PS6 * s.Pmut[156]! - PS9 * s.Pmut[154]! + s.Pmut[54]!
  let PS151 : Binary64 := PS106 - PS11 * s.Pmut[58]! + PS12 * s.Pmut[34]! + PS13 * s.Pmut[10]! - PS15 + PS7 * s.Pmut[250]! + s.Pmut[82]!
  let PS152 : Binary64 := PS12 * s.Pmut[25]! + PS129 + PS24 - PS34 * s.Pmut[36]! - PS6 * s.Pmut[35]! + PS7 * s.Pmut[34]! + s.Pmut[27]!
  let PS153 : Binary64 := -PS101 + PS13 * s.Pmut[0]! + PS134 - PS34 * s.Pmut[12]! - PS6 * s.Pmut[11]! + PS7 * s.Pmut[10]! + s.Pmut[3]!
  let PS154 : Binary64 := PS104 - PS11 * s.Pmut[60]! + PS12 * s.Pmut[36]! + PS13 * s.Pmut[12]! - PS131 - PS34 * s.Pmut[300]! + s.Pmut[84]!
  let PS155 : Binary64 := -PS11 * s.Pmut[59]! + PS12 * s.Pmut[35]! + PS126 + PS13 * s.Pmut[11]! - PS6 * s.Pmut[275]! + PS8 + s.Pmut[83]!
  let PS156 : Binary64 := -PS11 * s.Pmut[50]! + PS21 - PS34 * s.Pmut[60]! - PS6 * s.Pmut[59]! + PS7 * s.Pmut[58]! + PS98 + s.Pmut[51]!
  let PS157 : Binary64 := PS111 - PS136 + PS32 - PS34 * s.Pmut[84]! - PS6 * s.Pmut[83]! + PS7 * s.Pmut[82]! + s.Pmut[75]!
  let PS158 : Binary64 := -PS11 * s.Pmut[61]! + PS12 * s.Pmut[37]! + PS13 * s.Pmut[13]! - PS34 * s.Pmut[301]! - PS6 * s.Pmut[277]! + PS7 * s.Pmut[253]! + s.Pmut[85]!
  let PS159 : Binary64 := -PS11 * s.Pmut[63]! + PS12 * s.Pmut[39]! + PS13 * s.Pmut[15]! - PS34 * s.Pmut[303]! - PS6 * s.Pmut[279]! + PS7 * s.Pmut[255]! + s.Pmut[87]!
  let PS160 : Binary64 := (Binary64.ofBits 0x4000000000000000 /- 2 -/) * PS159
  let PS161 : Binary64 := (Binary64.ofBits 0x4000000000000000 /- 2 -/) * PS157
  let PS162 : Binary64 := -PS11 * s.Pmut[62]! + PS12 * s.Pmut[38]! + PS13 * s.Pmut[14]! - PS34 * s.Pmut[302]! - PS6 * s.Pmut[278]! + PS7 * s.Pmut[254]! + s.Pmut[86]!
  let PS163 : Binary64 := (Binary64.ofBits 0x4000000000000000 /- 2 -/) * PS162
  let PS164 : Binary64 := (Binary64.ofBits 0x4000000000000000 /- 2 -/) * PS152
  let PS165 : Binary64 := (Binary64.ofBits 0x4000000000000000 /- 2 -/) * PS153
  let PS166 : Binary64 := (Binary64.ofBits 0x4000000000000000 /- 2 -/) * PS156
  let PS167 : Binary64 := -PS11 * s.Pmut[52]! + PS12 * s.Pmut[28]! + PS13 * s.Pmut[4]! - PS34 * s.Pmut[108]! - PS6 * s.Pmut[107]! + PS7 * s.Pmut[106]! + s.Pmut[76]!
  let PS168 : Binary64 := (Binary64.ofBits 0x4000000000000000 /- 2 -/) * PS158
  let PS169 : Binary64 := -PS11 * s.Pmut[53]! + PS12 * s.Pmut[29]! + PS13 * s.Pmut[5]! - PS34 * s.Pmut[132]! - PS6 * s.Pmut[131]! + PS7 * s.Pmut[130]! + s.Pmut[77]!
  let PS170 : Binary64 := -PS11 * s.Pmut[54]! + PS12 * s.Pmut[30]! + PS13 * s.Pmut[6]! - PS34 * s.Pmut[156]! - PS6 * s.Pmut[155]! + PS7 * s.Pmut[154]! + s.Pmut[78]!
  let PS171 : Binary64 := (Binary64.ofBits 0x4000000000000000 /- 2 -/) * PS45
  let PS172 : Binary64 := (Binary64.ofBits 0x4000000000000000 /- 2 -/) * PS56
  let PS173 : Binary64 := (Binary64.ofBits 0x4000000000000000 /- 2 -/) * PS61
  let PS174 : Binary64 := (Binary64.ofBits 0x4000000000000000 /- 2 -/) * PS66
  let PS175 : Binary64 := (Binary64.ofBits 0x4000000000000000 /- 2 -/) * PS71
  let PS176 : Binary64 := (Binary64.ofBits 0x4000000000000000 /- 2 -/) * PS54
  let PS177 : Binary64 := -PS171 * s.Pmut[327]! + PS172 * s.Pmut[326]! + PS173 * s.Pmut[37]! + PS174 * s.Pmut[13]! + PS175 * s.Pmut[61]! - PS176 * s.Pmut[85]! + PS43 * s.Pmut[325]! + s.Pmut[109]!
  let PS178 : Binary64 := -PS171 * s.Pmut[375]! + PS172 * s.Pmut[351]! + PS173 * s.Pmut[39]! + PS174 * s.Pmut[15]! + PS175 * s.Pmut[63]! - PS176 * s.Pmut[87]! + PS43 * s.Pmut[327]! + s.Pmut[111]!
  let PS179 : Binary64 := -PS171 * s.Pmut[87]! + PS172 * s.Pmut[86]! + PS173 * s.Pmut[27]! + PS174 * s.Pmut[3]! + PS175 * s.Pmut[51]! - PS176 * s.Pmut[75]! + PS43 * s.Pmut[85]! + s.Pmut[76]!
  let PS180 : Binary64 := -PS171 * s.Pmut[351]! + PS172 * s.Pmut[350]! + PS173 * s.Pmut[38]! + PS174 * s.Pmut[14]! + PS175 * s.Pmut[62]! - PS176 * s.Pmut[86]! + PS43 * s.Pmut[326]! + s.Pmut[110]!
  let PS181 : Binary64 := -PS171 * s.Pmut[39]! + PS172 * s.Pmut[38]! + PS173 * s.Pmut[25]! + PS174 * s.Pmut[1]! + PS175 * s.Pmut[26]! - PS176 * s.Pmut[27]! + PS43 * s.Pmut[37]! + s.Pmut[28]!
  let PS182 : Binary64 := -PS171 * s.Pmut[15]! + PS172 * s.Pmut[14]! + PS173 * s.Pmut[1]! + PS174 * s.Pmut[0]! + PS175 * s.Pmut[2]! - PS176 * s.Pmut[3]! + PS43 * s.Pmut[13]! + s.Pmut[4]!
  let PS183 : Binary64 := -PS171 * s.Pmut[63]! + PS172 * s.Pmut[62]! + PS173 * s.Pmut[26]! + PS174 * s.Pmut[2]! + PS175 * s.Pmut[50]! - PS176 * s.Pmut[51]! + PS43 * s.Pmut[61]! + s.Pmut[52]!
  let PS184 : Binary64 := (Binary64.ofBits 0x4010000000000000 /- 4 -/) * dvyVar
  let PS185 : Binary64 := (Binary64.ofBits 0x4010000000000000 /- 4 -/) * dvzVar
  let PS186 : Binary64 := -PS171 * s.Pmut[111]! + PS172 * s.Pmut[110]! + PS173 * s.Pmut[28]! + PS174 * s.Pmut[4]! + PS175 * s.Pmut[52]! - PS176 * s.Pmut[76]! + PS43 * s.Pmut[109]! + s.Pmut[100]!
  let PS187 : Binary64 := (Binary64.ofBits 0x4000000000000000 /- 2 -/) * PS177
  let PS188 : Binary64 := (Binary64.ofBits 0x4000000000000000 /- 2 -/) * PS182
  let PS189 : Binary64 := (Binary64.ofBits 0x4000000000000000 /- 2 -/) * PS181
  let PS190 : Binary64 := (Binary64.ofBits 0x4000000000000000 /- 2 -/) * PS81
  let PS191 : Binary64 := (Binary64.ofBits 0x4000000000000000 /- 2 -/) * PS183
  let PS192 : Binary64 := (Binary64.ofBits 0x4000000000000000 /- 2 -/) * PS179
  let PS193 : Binary64 := (Binary64.ofBits 0x4000000000000000 /- 2 -/) * PS76
  let PS194 : Binary64 := PS43 * dvxVar
  let PS195 : Binary64 := PS75 * dvyVar
  let PS196 : Binary64 := -PS171 * s.Pmut[135]! + PS172 * s.Pmut[134]! + PS173 * s.Pmut[29]! + PS174 * s.Pmut[5]! + PS175 * s.Pmut[53]! - PS176 * s.Pmut[77]! + PS43 * s.Pmut[133]! + s.Pmut[101]!
  let PS197 : Binary64 := (Binary64.ofBits 0x4000000000000000 /- 2 -/) * PS88
  let PS198 : Binary64 := PS87 * dvzVar
  let PS199 : Binary64 := (Binary64.ofBits 0x4000000000000000 /- 2 -/) * PS90
  let PS200 : Binary64 := -PS171 * s.Pmut[159]! + PS172 * s.Pmut[158]! + PS173 * s.Pmut[30]! + PS174 * s.Pmut[6]! + PS175 * s.Pmut[54]! - PS176 * s.Pmut[78]! + PS43 * s.Pmut[157]! + s.Pmut[102]!
  let PS201 : Binary64 := (Binary64.ofBits 0x4000000000000000 /- 2 -/) * PS83
  let PS202 : Binary64 := (Binary64.ofBits 0x4000000000000000 /- 2 -/) * PS78
  let PS203 : Binary64 := (Binary64.ofBits 0x4000000000000000 /- 2 -/) * PS85
  let PS204 : Binary64 := (Binary64.ofBits 0x4000000000000000 /- 2 -/) * PS80
  let PS205 : Binary64 := PS190 * s.Pmut[351]! - PS193 * s.Pmut[326]! + PS201 * s.Pmut[62]! - PS202 * s.Pmut[14]! + PS203 * s.Pmut[86]! - PS204 * s.Pmut[38]! + PS75 * s.Pmut[350]! + s.Pmut[134]!
  let PS206 : Binary64 := PS190 * s.Pmut[327]! - PS193 * s.Pmut[325]! + PS201 * s.Pmut[61]! - PS202 * s.Pmut[13]! + PS203 * s.Pmut[85]! - PS204 * s.Pmut[37]! + PS75 * s.Pmut[326]! + s.Pmut[133]!
  let PS207 : Binary64 := PS190 * s.Pmut[15]! - PS193 * s.Pmut[13]! + PS201 * s.Pmut[2]! - PS202 * s.Pmut[0]! + PS203 * s.Pmut[3]! - PS204 * s.Pmut[1]! + PS75 * s.Pmut[14]! + s.Pmut[5]!
  let PS208 : Binary64 := PS190 * s.Pmut[39]! - PS193 * s.Pmut[37]! + PS201 * s.Pmut[26]! - PS202 * s.Pmut[1]! + PS203 * s.Pmut[27]! - PS204 * s.Pmut[25]! + PS75 * s.Pmut[38]! + s.Pmut[29]!
  let PS209 : Binary64 := PS190 * s.Pmut[375]! - PS193 * s.Pmut[327]! + PS201 * s.Pmut[63]! - PS202 * s.Pmut[15]! + PS203 * s.Pmut[87]! - PS204 * s.Pmut[39]! + PS75 * s.Pmut[351]! + s.Pmut[135]!
  let PS210 : Binary64 := PS190 * s.Pmut[63]! - PS193 * s.Pmut[61]! + PS201 * s.Pmut[50]! - PS202 * s.Pmut[2]! + PS203 * s.Pmut[51]! - PS204 * s.Pmut[26]! + PS75 * s.Pmut[62]! + s.Pmut[53]!
  let PS211 : Binary64 := PS190 * s.Pmut[87]! - PS193 * s.Pmut[85]! + PS201 * s.Pmut[51]! - PS202 * s.Pmut[3]! + PS203 * s.Pmut[75]! - PS204 * s.Pmut[27]! + PS75 * s.Pmut[86]! + s.Pmut[77]!
  let PS212 : Binary64 := (Binary64.ofBits 0x4010000000000000 /- 4 -/) * dvxVar
  let PS213 : Binary64 := PS190 * s.Pmut[135]! - PS193 * s.Pmut[133]! + PS201 * s.Pmut[53]! - PS202 * s.Pmut[5]! + PS203 * s.Pmut[77]! - PS204 * s.Pmut[29]! + PS75 * s.Pmut[134]! + s.Pmut[125]!
  let PS214 : Binary64 := (Binary64.ofBits 0x4000000000000000 /- 2 -/) * PS89
  let PS215 : Binary64 := (Binary64.ofBits 0x4000000000000000 /- 2 -/) * PS91
  let PS216 : Binary64 := (Binary64.ofBits 0x4000000000000000 /- 2 -/) * PS92
  let PS217 : Binary64 := (Binary64.ofBits 0x4000000000000000 /- 2 -/) * PS93
  let PS218 : Binary64 := PS190 * s.Pmut[159]! - PS193 * s.Pmut[157]! + PS201 * s.Pmut[54]! - PS202 * s.Pmut[6]! + PS203 * s.Pmut[78]! - PS204 * s.Pmut[30]! + PS75 * s.Pmut[158]! + s.Pmut[126]!
  let PS219 : Binary64 := -PS197 * s.Pmut[351]! + PS199 * s.Pmut[327]! - PS214 * s.Pmut[63]! + PS215 * s.Pmut[87]! + PS216 * s.Pmut[15]! + PS217 * s.Pmut[39]! + PS87 * s.Pmut[375]! + s.Pmut[159]!
  let PS220 : Binary64 := -PS197 * s.Pmut[350]! + PS199 * s.Pmut[326]! - PS214 * s.Pmut[62]! + PS215 * s.Pmut[86]! + PS216 * s.Pmut[14]! + PS217 * s.Pmut[38]! + PS87 * s.Pmut[351]! + s.Pmut[158]!
  let PS221 : Binary64 := -PS197 * s.Pmut[326]! + PS199 * s.Pmut[325]! - PS214 * s.Pmut[61]! + PS215 * s.Pmut[85]! + PS216 * s.Pmut[13]! + PS217 * s.Pmut[37]! + PS87 * s.Pmut[327]! + s.Pmut[157]!
  let PS222 : Binary64 := -PS197 * s.Pmut[158]! + PS199 * s.Pmut[157]! - PS214 * s.Pmut[54]! + PS215 * s.Pmut[78]! + PS216 * s.Pmut[6]! + PS217 * s.Pmut[30]! + PS87 * s.Pmut[159]! + s.Pmut[150]!
  w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 0 (PS0 * PS1 - PS11 * PS23 - PS12 * PS26 - PS13 * PS29 + PS14 * PS6 + PS17 * PS7 + PS2 * PS3 + PS20 * PS9 + PS33 + PS4 * PS5) }
  w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 1 (-PS1 * PS36 + PS11 * PS33 - PS12 * PS29 + PS13 * PS26 - PS14 * PS34 + PS17 * PS9 - PS20 * PS7 + PS23 + PS3 * PS35 - PS35 * PS5) }
  w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 25 (PS1 * PS95 + PS100 * PS11 + PS102 * PS13 - PS105 * PS34 - PS107 * PS7 - PS109 * PS12 + PS112 + PS2 * PS5 + PS3 * PS4 + PS9 * PS97) }
  w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 2 (-PS1 * PS37 + PS11 * PS29 + PS12 * PS33 - PS13 * PS23 - PS14 * PS9 - PS17 * PS34 + PS20 * PS6 + PS26 - PS3 * PS38 + PS37 * PS5) }
  w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 26 (PS1 * PS40 + PS100 * PS12 + PS102 - PS105 * PS9 + PS107 * PS6 + PS109 * PS11 - PS112 * PS13 - PS3 * PS40 - PS34 * PS97 - PS39 * PS5) }
  w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 50 (PS0 * PS5 + PS1 * PS4 + PS11 * PS128 + PS12 * PS130 + PS127 * PS6 - PS13 * PS135 - PS132 * PS34 - PS133 * PS9 + PS137 + PS3 * PS95) }
  w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 3 (PS1 * PS39 - PS11 * PS26 + PS12 * PS23 + PS13 * PS33 + PS14 * PS7 - PS17 * PS6 - PS20 * PS34 + PS29 - PS3 * PS39 - PS40 * PS5) }
  w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 27 (-PS1 * PS38 + PS100 * PS13 - PS102 * PS11 + PS105 * PS7 - PS107 * PS34 + PS109 + PS112 * PS12 - PS3 * PS37 + PS38 * PS5 - PS6 * PS97) }
  w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 51 (-PS1 * PS35 - PS11 * PS137 + PS12 * PS135 - PS127 * PS34 + PS128 + PS13 * PS130 - PS132 * PS6 + PS133 * PS7 + PS3 * PS36 - PS36 * PS5) }
  w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 75 (PS0 * PS3 + PS1 * PS2 - PS11 * PS156 + PS12 * PS152 + PS13 * PS153 + PS151 * PS7 - PS154 * PS34 - PS155 * PS6 + PS157 + PS5 * PS95) }
  if quatCovResetOnly then
    for row' in [0:4] do
      let row : UInt8 := Nat.toUInt8 row'
      s := { s with Pmut := s.Pmut.set! (UInt8.toNat row * 24 + UInt8.toNat row) (Estimator_lib.constrain_value_line_double w.NavEKF_core_common'KHP[UInt8.toNat row * 24 + UInt8.toNat row]! (Binary64.ofBits 0x0000000000000000 /- (double)0 -/) (Binary64.ofBits 0x3ff0000000000000 /- (double)1 -/) (Int32.toUInt32 (1421 : Int32))) }
      for column' in [0:row.toNat] do
        let column : UInt8 := Nat.toUInt8 column'
        s := { s with Pmut := s.Pmut.set! (UInt8.toNat column * 24 + UInt8.toNat row) (w.NavEKF_core_common'KHP[UInt8.toNat column * 24 + UInt8.toNat row]!) }
        s := { s with Pmut := s.Pmut.set! (UInt8.toNat row * 24 + UInt8.toNat column) (s.Pmut[UInt8.toNat column * 24 + UInt8.toNat row]!) }
    s := calcTiltErrorVariance s
    return (s, w, rotVarVecPtr)
  w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 4 (PS43 * PS44 - PS45 * PS47 - PS54 * PS55 + PS56 * PS58 + PS61 * PS62 + PS66 * PS67 + PS71 * PS72 + PS73) }
  w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 28 (PS113 * PS43 - PS115 * PS45 - PS116 * PS54 + PS118 * PS56 + PS119 * PS61 + PS120 * PS66 + PS121 * PS71 + PS122) }
  w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 52 (PS138 * PS43 - PS140 * PS45 - PS141 * PS54 + PS143 * PS56 + PS144 * PS61 + PS145 * PS66 + PS146 * PS71 + PS147) }
  w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 76 (PS158 * PS43 - PS160 * PS45 - PS161 * PS54 + PS163 * PS56 + PS164 * PS61 + PS165 * PS66 + PS166 * PS71 + PS167) }
  w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 100 (-PS171 * PS178 + PS172 * PS180 + PS173 * PS181 + PS174 * PS182 + PS175 * PS183 - PS176 * PS179 + PS177 * PS43 + PS184 * Estimator_lib.sq_double PS56 + PS185 * Estimator_lib.sq_double PS45 + PS186 + Estimator_lib.sq_double PS43 * dvxVar) }
  w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 5 (PS47 * PS81 + PS55 * PS85 + PS57 * PS75 - PS62 * PS80 - PS67 * PS78 + PS72 * PS83 - PS76 * PS77 + PS86) }
  w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 29 (PS115 * PS81 + PS116 * PS85 + PS117 * PS75 - PS119 * PS80 - PS120 * PS78 + PS121 * PS83 - PS123 * PS76 + PS124) }
  w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 53 (PS140 * PS81 + PS141 * PS85 + PS142 * PS75 - PS144 * PS80 - PS145 * PS78 + PS146 * PS83 - PS148 * PS76 + PS149) }
  w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 77 (PS160 * PS81 + PS161 * PS85 + PS162 * PS75 - PS164 * PS80 - PS165 * PS78 + PS166 * PS83 - PS168 * PS76 + PS169) }
  w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 101 (PS172 * PS195 + PS178 * PS190 + PS180 * PS75 - PS185 * PS45 * PS81 - PS187 * PS76 - PS188 * PS78 - PS189 * PS80 + PS191 * PS83 + PS192 * PS85 - PS193 * PS194 + PS196) }
  w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 125 (PS185 * Estimator_lib.sq_double PS81 + PS190 * PS209 - PS193 * PS206 + PS201 * PS210 - PS202 * PS207 + PS203 * PS211 - PS204 * PS208 + PS205 * PS75 + PS212 * Estimator_lib.sq_double PS76 + PS213 + Estimator_lib.sq_double PS75 * dvyVar) }
  w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 6 (PS46 * PS87 + PS55 * PS91 - PS58 * PS88 + PS62 * PS93 + PS67 * PS92 - PS72 * PS89 + PS77 * PS90 + PS94) }
  w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 30 (PS114 * PS87 + PS116 * PS91 - PS118 * PS88 + PS119 * PS93 + PS120 * PS92 - PS121 * PS89 + PS123 * PS90 + PS125) }
  w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 54 (PS139 * PS87 + PS141 * PS91 - PS143 * PS88 + PS144 * PS93 + PS145 * PS92 - PS146 * PS89 + PS148 * PS90 + PS150) }
  w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 78 (PS159 * PS87 + PS161 * PS91 - PS163 * PS88 + PS164 * PS93 + PS165 * PS92 - PS166 * PS89 + PS168 * PS90 + PS170) }
  w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 102 (-PS171 * PS198 + PS178 * PS87 - PS180 * PS197 - PS184 * PS56 * PS88 + PS187 * PS90 + PS188 * PS92 + PS189 * PS93 - PS191 * PS89 + PS192 * PS91 + PS194 * PS199 + PS200) }
  w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 126 (PS190 * PS198 - PS195 * PS197 - PS197 * PS205 + PS199 * PS206 + PS207 * PS216 + PS208 * PS217 + PS209 * PS87 - PS210 * PS214 + PS211 * PS215 - PS212 * PS76 * PS90 + PS218) }
  w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 150 (PS184 * Estimator_lib.sq_double PS88 - PS197 * PS220 + PS199 * PS221 + PS212 * Estimator_lib.sq_double PS90 - PS214 * (-PS197 * s.Pmut[62]! + PS199 * s.Pmut[61]! - PS214 * s.Pmut[50]! + PS215 * s.Pmut[51]! + PS216 * s.Pmut[2]! + PS217 * s.Pmut[26]! + PS87 * s.Pmut[63]! + s.Pmut[54]!) + PS215 * (-PS197 * s.Pmut[86]! + PS199 * s.Pmut[85]! - PS214 * s.Pmut[51]! + PS215 * s.Pmut[75]! + PS216 * s.Pmut[3]! + PS217 * s.Pmut[27]! + PS87 * s.Pmut[87]! + s.Pmut[78]!) + PS216 * (-PS197 * s.Pmut[14]! + PS199 * s.Pmut[13]! - PS214 * s.Pmut[2]! + PS215 * s.Pmut[3]! + PS216 * s.Pmut[0]! + PS217 * s.Pmut[1]! + PS87 * s.Pmut[15]! + s.Pmut[6]!) + PS217 * (-PS197 * s.Pmut[38]! + PS199 * s.Pmut[37]! - PS214 * s.Pmut[26]! + PS215 * s.Pmut[27]! + PS216 * s.Pmut[1]! + PS217 * s.Pmut[25]! + PS87 * s.Pmut[39]! + s.Pmut[30]!) + PS219 * PS87 + PS222 + Estimator_lib.sq_double PS87 * dvzVar) }
  w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 7 (-PS11 * s.Pmut[31]! - PS12 * s.Pmut[55]! - PS13 * s.Pmut[79]! + PS6 * s.Pmut[178]! + PS7 * s.Pmut[179]! + PS73 * s.dt + PS9 * s.Pmut[180]! + s.Pmut[7]!) }
  w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 31 (PS11 * s.Pmut[7]! - PS12 * s.Pmut[79]! + PS122 * s.dt + PS13 * s.Pmut[55]! - PS34 * s.Pmut[178]! - PS7 * s.Pmut[180]! + PS9 * s.Pmut[179]! + s.Pmut[31]!) }
  w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 55 (PS11 * s.Pmut[79]! + PS12 * s.Pmut[7]! - PS13 * s.Pmut[31]! + PS147 * s.dt - PS34 * s.Pmut[179]! + PS6 * s.Pmut[180]! - PS9 * s.Pmut[178]! + s.Pmut[55]!) }
  w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 79 (-PS11 * s.Pmut[55]! + PS12 * s.Pmut[31]! + PS13 * s.Pmut[7]! + PS167 * s.dt - PS34 * s.Pmut[180]! - PS6 * s.Pmut[179]! + PS7 * s.Pmut[178]! + s.Pmut[79]!) }
  w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 103 (-PS171 * s.Pmut[183]! + PS172 * s.Pmut[182]! + PS173 * s.Pmut[31]! + PS174 * s.Pmut[7]! + PS175 * s.Pmut[55]! - PS176 * s.Pmut[79]! + PS186 * s.dt + PS43 * s.Pmut[181]! + s.Pmut[103]!) }
  w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 127 (PS190 * s.Pmut[183]! - PS193 * s.Pmut[181]! + PS201 * s.Pmut[55]! - PS202 * s.Pmut[7]! + PS203 * s.Pmut[79]! - PS204 * s.Pmut[31]! + PS75 * s.Pmut[182]! + s.Pmut[127]! + s.dt * (PS190 * s.Pmut[111]! - PS193 * s.Pmut[109]! + PS201 * s.Pmut[52]! - PS202 * s.Pmut[4]! + PS203 * s.Pmut[76]! - PS204 * s.Pmut[28]! + PS75 * s.Pmut[110]! + s.Pmut[101]!)) }
  w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 151 (-PS197 * s.Pmut[182]! + PS199 * s.Pmut[181]! - PS214 * s.Pmut[55]! + PS215 * s.Pmut[79]! + PS216 * s.Pmut[7]! + PS217 * s.Pmut[31]! + PS87 * s.Pmut[183]! + s.Pmut[151]! + s.dt * (-PS197 * s.Pmut[110]! + PS199 * s.Pmut[109]! - PS214 * s.Pmut[52]! + PS215 * s.Pmut[76]! + PS216 * s.Pmut[4]! + PS217 * s.Pmut[28]! + PS87 * s.Pmut[111]! + s.Pmut[102]!)) }
  w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 175 (s.Pmut[103]! * s.dt + s.Pmut[175]! + s.dt * (s.Pmut[100]! * s.dt + s.Pmut[103]!)) }
  w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 8 (-PS11 * s.Pmut[32]! - PS12 * s.Pmut[56]! - PS13 * s.Pmut[80]! + PS6 * s.Pmut[202]! + PS7 * s.Pmut[203]! + PS86 * s.dt + PS9 * s.Pmut[204]! + s.Pmut[8]!) }
  w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 32 (PS11 * s.Pmut[8]! - PS12 * s.Pmut[80]! + PS124 * s.dt + PS13 * s.Pmut[56]! - PS34 * s.Pmut[202]! - PS7 * s.Pmut[204]! + PS9 * s.Pmut[203]! + s.Pmut[32]!) }
  w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 56 (PS11 * s.Pmut[80]! + PS12 * s.Pmut[8]! - PS13 * s.Pmut[32]! + PS149 * s.dt - PS34 * s.Pmut[203]! + PS6 * s.Pmut[204]! - PS9 * s.Pmut[202]! + s.Pmut[56]!) }
  w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 80 (-PS11 * s.Pmut[56]! + PS12 * s.Pmut[32]! + PS13 * s.Pmut[8]! + PS169 * s.dt - PS34 * s.Pmut[204]! - PS6 * s.Pmut[203]! + PS7 * s.Pmut[202]! + s.Pmut[80]!) }
  w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 104 (-PS171 * s.Pmut[207]! + PS172 * s.Pmut[206]! + PS173 * s.Pmut[32]! + PS174 * s.Pmut[8]! + PS175 * s.Pmut[56]! - PS176 * s.Pmut[80]! + PS196 * s.dt + PS43 * s.Pmut[205]! + s.Pmut[104]!) }
  w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 128 (PS190 * s.Pmut[207]! - PS193 * s.Pmut[205]! + PS201 * s.Pmut[56]! - PS202 * s.Pmut[8]! + PS203 * s.Pmut[80]! - PS204 * s.Pmut[32]! + PS213 * s.dt + PS75 * s.Pmut[206]! + s.Pmut[128]!) }
  w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 152 (-PS197 * s.Pmut[206]! + PS199 * s.Pmut[205]! - PS214 * s.Pmut[56]! + PS215 * s.Pmut[80]! + PS216 * s.Pmut[8]! + PS217 * s.Pmut[32]! + PS87 * s.Pmut[207]! + s.Pmut[152]! + s.dt * (-PS197 * s.Pmut[134]! + PS199 * s.Pmut[133]! - PS214 * s.Pmut[53]! + PS215 * s.Pmut[77]! + PS216 * s.Pmut[5]! + PS217 * s.Pmut[29]! + PS87 * s.Pmut[135]! + s.Pmut[126]!)) }
  w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 176 (s.Pmut[104]! * s.dt + s.Pmut[176]! + s.dt * (s.Pmut[101]! * s.dt + s.Pmut[127]!)) }
  w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 200 (s.Pmut[128]! * s.dt + s.Pmut[200]! + s.dt * (s.Pmut[125]! * s.dt + s.Pmut[128]!)) }
  w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 9 (-PS11 * s.Pmut[33]! - PS12 * s.Pmut[57]! - PS13 * s.Pmut[81]! + PS6 * s.Pmut[226]! + PS7 * s.Pmut[227]! + PS9 * s.Pmut[228]! + PS94 * s.dt + s.Pmut[9]!) }
  w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 33 (PS11 * s.Pmut[9]! - PS12 * s.Pmut[81]! + PS125 * s.dt + PS13 * s.Pmut[57]! - PS34 * s.Pmut[226]! - PS7 * s.Pmut[228]! + PS9 * s.Pmut[227]! + s.Pmut[33]!) }
  w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 57 (PS11 * s.Pmut[81]! + PS12 * s.Pmut[9]! - PS13 * s.Pmut[33]! + PS150 * s.dt - PS34 * s.Pmut[227]! + PS6 * s.Pmut[228]! - PS9 * s.Pmut[226]! + s.Pmut[57]!) }
  w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 81 (-PS11 * s.Pmut[57]! + PS12 * s.Pmut[33]! + PS13 * s.Pmut[9]! + PS170 * s.dt - PS34 * s.Pmut[228]! - PS6 * s.Pmut[227]! + PS7 * s.Pmut[226]! + s.Pmut[81]!) }
  w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 105 (-PS171 * s.Pmut[231]! + PS172 * s.Pmut[230]! + PS173 * s.Pmut[33]! + PS174 * s.Pmut[9]! + PS175 * s.Pmut[57]! - PS176 * s.Pmut[81]! + PS200 * s.dt + PS43 * s.Pmut[229]! + s.Pmut[105]!) }
  w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 129 (PS190 * s.Pmut[231]! - PS193 * s.Pmut[229]! + PS201 * s.Pmut[57]! - PS202 * s.Pmut[9]! + PS203 * s.Pmut[81]! - PS204 * s.Pmut[33]! + PS218 * s.dt + PS75 * s.Pmut[230]! + s.Pmut[129]!) }
  w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 153 (-PS197 * s.Pmut[230]! + PS199 * s.Pmut[229]! - PS214 * s.Pmut[57]! + PS215 * s.Pmut[81]! + PS216 * s.Pmut[9]! + PS217 * s.Pmut[33]! + PS222 * s.dt + PS87 * s.Pmut[231]! + s.Pmut[153]!) }
  w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 177 (s.Pmut[105]! * s.dt + s.Pmut[177]! + s.dt * (s.Pmut[102]! * s.dt + s.Pmut[151]!)) }
  w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 201 (s.Pmut[129]! * s.dt + s.Pmut[201]! + s.dt * (s.Pmut[126]! * s.dt + s.Pmut[152]!)) }
  w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 225 (s.Pmut[153]! * s.dt + s.Pmut[225]! + s.dt * (s.Pmut[150]! * s.dt + s.Pmut[153]!)) }
  if UInt32.toInt32 (UInt8.toUInt32 s.stateIndexLim) > (9 : Int32) then
    w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 10 PS14 }
    w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 34 PS105 }
    w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 58 PS133 }
    w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 82 PS151 }
    w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 106 (-PS171 * s.Pmut[255]! + PS172 * s.Pmut[254]! + PS173 * s.Pmut[34]! + PS174 * s.Pmut[10]! + PS175 * s.Pmut[58]! - PS176 * s.Pmut[82]! + PS43 * s.Pmut[253]! + s.Pmut[106]!) }
    w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 130 (PS190 * s.Pmut[255]! - PS193 * s.Pmut[253]! + PS201 * s.Pmut[58]! - PS202 * s.Pmut[10]! + PS203 * s.Pmut[82]! - PS204 * s.Pmut[34]! + PS75 * s.Pmut[254]! + s.Pmut[130]!) }
    w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 154 (-PS197 * s.Pmut[254]! + PS199 * s.Pmut[253]! - PS214 * s.Pmut[58]! + PS215 * s.Pmut[82]! + PS216 * s.Pmut[10]! + PS217 * s.Pmut[34]! + PS87 * s.Pmut[255]! + s.Pmut[154]!) }
    w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 178 (s.Pmut[106]! * s.dt + s.Pmut[178]!) }
    w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 202 (s.Pmut[130]! * s.dt + s.Pmut[202]!) }
    w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 226 (s.Pmut[154]! * s.dt + s.Pmut[226]!) }
    w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 250 (s.Pmut[250]!) }
    w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 11 PS17 }
    w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 35 PS97 }
    w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 59 PS132 }
    w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 83 PS155 }
    w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 107 (-PS171 * s.Pmut[279]! + PS172 * s.Pmut[278]! + PS173 * s.Pmut[35]! + PS174 * s.Pmut[11]! + PS175 * s.Pmut[59]! - PS176 * s.Pmut[83]! + PS43 * s.Pmut[277]! + s.Pmut[107]!) }
    w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 131 (PS190 * s.Pmut[279]! - PS193 * s.Pmut[277]! + PS201 * s.Pmut[59]! - PS202 * s.Pmut[11]! + PS203 * s.Pmut[83]! - PS204 * s.Pmut[35]! + PS75 * s.Pmut[278]! + s.Pmut[131]!) }
    w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 155 (-PS197 * s.Pmut[278]! + PS199 * s.Pmut[277]! - PS214 * s.Pmut[59]! + PS215 * s.Pmut[83]! + PS216 * s.Pmut[11]! + PS217 * s.Pmut[35]! + PS87 * s.Pmut[279]! + s.Pmut[155]!) }
    w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 179 (s.Pmut[107]! * s.dt + s.Pmut[179]!) }
    w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 203 (s.Pmut[131]! * s.dt + s.Pmut[203]!) }
    w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 227 (s.Pmut[155]! * s.dt + s.Pmut[227]!) }
    w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 251 (s.Pmut[251]!) }
    w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 275 (s.Pmut[275]!) }
    w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 12 PS20 }
    w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 36 PS107 }
    w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 60 PS127 }
    w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 84 PS154 }
    w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 108 (-PS171 * s.Pmut[303]! + PS172 * s.Pmut[302]! + PS173 * s.Pmut[36]! + PS174 * s.Pmut[12]! + PS175 * s.Pmut[60]! - PS176 * s.Pmut[84]! + PS43 * s.Pmut[301]! + s.Pmut[108]!) }
    w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 132 (PS190 * s.Pmut[303]! - PS193 * s.Pmut[301]! + PS201 * s.Pmut[60]! - PS202 * s.Pmut[12]! + PS203 * s.Pmut[84]! - PS204 * s.Pmut[36]! + PS75 * s.Pmut[302]! + s.Pmut[132]!) }
    w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 156 (-PS197 * s.Pmut[302]! + PS199 * s.Pmut[301]! - PS214 * s.Pmut[60]! + PS215 * s.Pmut[84]! + PS216 * s.Pmut[12]! + PS217 * s.Pmut[36]! + PS87 * s.Pmut[303]! + s.Pmut[156]!) }
    w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 180 (s.Pmut[108]! * s.dt + s.Pmut[180]!) }
    w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 204 (s.Pmut[132]! * s.dt + s.Pmut[204]!) }
    w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 228 (s.Pmut[156]! * s.dt + s.Pmut[228]!) }
    w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 252 (s.Pmut[252]!) }
    w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 276 (s.Pmut[276]!) }
    w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 300 (s.Pmut[300]!) }
    if UInt32.toInt32 (UInt8.toUInt32 s.stateIndexLim) > (12 : Int32) then
      w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 13 PS44 }
      w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 37 PS113 }
      w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 61 PS138 }
      w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 85 PS158 }
      w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 109 PS177 }
      w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 133 PS206 }
      w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 157 PS221 }
      w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 181 (s.Pmut[109]! * s.dt + s.Pmut[181]!) }
      w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 205 (s.Pmut[133]! * s.dt + s.Pmut[205]!) }
      w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 229 (s.Pmut[157]! * s.dt + s.Pmut[229]!) }
      w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 253 (s.Pmut[253]!) }
      w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 277 (s.Pmut[277]!) }
      w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 301 (s.Pmut[301]!) }
      w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 325 (s.Pmut[325]!) }
      w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 14 PS57 }
      w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 38 PS117 }
      w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 62 PS142 }
      w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 86 PS162 }
      w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 110 PS180 }
      w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 134 PS205 }
      w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 158 PS220 }
      w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 182 (s.Pmut[110]! * s.dt + s.Pmut[182]!) }
      w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 206 (s.Pmut[134]! * s.dt + s.Pmut[206]!) }
      w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 230 (s.Pmut[158]! * s.dt + s.Pmut[230]!) }
      w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 254 (s.Pmut[254]!) }
      w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 278 (s.Pmut[278]!) }
      w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 302 (s.Pmut[302]!) }
      w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 326 (s.Pmut[326]!) }
      w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 350 (s.Pmut[350]!) }
      w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 15 PS46 }
      w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 39 PS114 }
      w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 63 PS139 }
      w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 87 PS159 }
      w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 111 PS178 }
      w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 135 PS209 }
      w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 159 PS219 }
      w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 183 (s.Pmut[111]! * s.dt + s.Pmut[183]!) }
      w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 207 (s.Pmut[135]! * s.dt + s.Pmut[207]!) }
      w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 231 (s.Pmut[159]! * s.dt + s.Pmut[231]!) }
      w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 255 (s.Pmut[255]!) }
      w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 279 (s.Pmut[279]!) }
      w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 303 (s.Pmut[303]!) }
      w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 327 (s.Pmut[327]!) }
      w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 351 (s.Pmut[351]!) }
      w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 375 (s.Pmut[375]!) }
      if UInt32.toInt32 (UInt8.toUInt32 s.stateIndexLim) > (15 : Int32) then
        w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 16 (-PS11 * s.Pmut[40]! - PS12 * s.Pmut[64]! - PS13 * s.Pmut[88]! + PS6 * s.Pmut[256]! + PS7 * s.Pmut[280]! + PS9 * s.Pmut[304]! + s.Pmut[16]!) }
        w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 40 (PS11 * s.Pmut[16]! - PS12 * s.Pmut[88]! + PS13 * s.Pmut[64]! - PS34 * s.Pmut[256]! - PS7 * s.Pmut[304]! + PS9 * s.Pmut[280]! + s.Pmut[40]!) }
        w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 64 (PS11 * s.Pmut[88]! + PS12 * s.Pmut[16]! - PS13 * s.Pmut[40]! - PS34 * s.Pmut[280]! + PS6 * s.Pmut[304]! - PS9 * s.Pmut[256]! + s.Pmut[64]!) }
        w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 88 (-PS11 * s.Pmut[64]! + PS12 * s.Pmut[40]! + PS13 * s.Pmut[16]! - PS34 * s.Pmut[304]! - PS6 * s.Pmut[280]! + PS7 * s.Pmut[256]! + s.Pmut[88]!) }
        w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 112 (-PS171 * s.Pmut[376]! + PS172 * s.Pmut[352]! + PS173 * s.Pmut[40]! + PS174 * s.Pmut[16]! + PS175 * s.Pmut[64]! - PS176 * s.Pmut[88]! + PS43 * s.Pmut[328]! + s.Pmut[112]!) }
        w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 136 (PS190 * s.Pmut[376]! - PS193 * s.Pmut[328]! + PS201 * s.Pmut[64]! - PS202 * s.Pmut[16]! + PS203 * s.Pmut[88]! - PS204 * s.Pmut[40]! + PS75 * s.Pmut[352]! + s.Pmut[136]!) }
        w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 160 (-PS197 * s.Pmut[352]! + PS199 * s.Pmut[328]! - PS214 * s.Pmut[64]! + PS215 * s.Pmut[88]! + PS216 * s.Pmut[16]! + PS217 * s.Pmut[40]! + PS87 * s.Pmut[376]! + s.Pmut[160]!) }
        w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 184 (s.Pmut[112]! * s.dt + s.Pmut[184]!) }
        w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 208 (s.Pmut[136]! * s.dt + s.Pmut[208]!) }
        w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 232 (s.Pmut[160]! * s.dt + s.Pmut[232]!) }
        w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 256 (s.Pmut[256]!) }
        w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 280 (s.Pmut[280]!) }
        w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 304 (s.Pmut[304]!) }
        w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 328 (s.Pmut[328]!) }
        w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 352 (s.Pmut[352]!) }
        w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 376 (s.Pmut[376]!) }
        w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 400 (s.Pmut[400]!) }
        w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 17 (-PS11 * s.Pmut[41]! - PS12 * s.Pmut[65]! - PS13 * s.Pmut[89]! + PS6 * s.Pmut[257]! + PS7 * s.Pmut[281]! + PS9 * s.Pmut[305]! + s.Pmut[17]!) }
        w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 41 (PS11 * s.Pmut[17]! - PS12 * s.Pmut[89]! + PS13 * s.Pmut[65]! - PS34 * s.Pmut[257]! - PS7 * s.Pmut[305]! + PS9 * s.Pmut[281]! + s.Pmut[41]!) }
        w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 65 (PS11 * s.Pmut[89]! + PS12 * s.Pmut[17]! - PS13 * s.Pmut[41]! - PS34 * s.Pmut[281]! + PS6 * s.Pmut[305]! - PS9 * s.Pmut[257]! + s.Pmut[65]!) }
        w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 89 (-PS11 * s.Pmut[65]! + PS12 * s.Pmut[41]! + PS13 * s.Pmut[17]! - PS34 * s.Pmut[305]! - PS6 * s.Pmut[281]! + PS7 * s.Pmut[257]! + s.Pmut[89]!) }
        w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 113 (-PS171 * s.Pmut[377]! + PS172 * s.Pmut[353]! + PS173 * s.Pmut[41]! + PS174 * s.Pmut[17]! + PS175 * s.Pmut[65]! - PS176 * s.Pmut[89]! + PS43 * s.Pmut[329]! + s.Pmut[113]!) }
        w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 137 (PS190 * s.Pmut[377]! - PS193 * s.Pmut[329]! + PS201 * s.Pmut[65]! - PS202 * s.Pmut[17]! + PS203 * s.Pmut[89]! - PS204 * s.Pmut[41]! + PS75 * s.Pmut[353]! + s.Pmut[137]!) }
        w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 161 (-PS197 * s.Pmut[353]! + PS199 * s.Pmut[329]! - PS214 * s.Pmut[65]! + PS215 * s.Pmut[89]! + PS216 * s.Pmut[17]! + PS217 * s.Pmut[41]! + PS87 * s.Pmut[377]! + s.Pmut[161]!) }
        w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 185 (s.Pmut[113]! * s.dt + s.Pmut[185]!) }
        w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 209 (s.Pmut[137]! * s.dt + s.Pmut[209]!) }
        w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 233 (s.Pmut[161]! * s.dt + s.Pmut[233]!) }
        w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 257 (s.Pmut[257]!) }
        w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 281 (s.Pmut[281]!) }
        w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 305 (s.Pmut[305]!) }
        w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 329 (s.Pmut[329]!) }
        w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 353 (s.Pmut[353]!) }
        w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 377 (s.Pmut[377]!) }
        w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 401 (s.Pmut[401]!) }
        w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 425 (s.Pmut[425]!) }
        w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 18 (-PS11 * s.Pmut[42]! - PS12 * s.Pmut[66]! - PS13 * s.Pmut[90]! + PS6 * s.Pmut[258]! + PS7 * s.Pmut[282]! + PS9 * s.Pmut[306]! + s.Pmut[18]!) }
        w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 42 (PS11 * s.Pmut[18]! - PS12 * s.Pmut[90]! + PS13 * s.Pmut[66]! - PS34 * s.Pmut[258]! - PS7 * s.Pmut[306]! + PS9 * s.Pmut[282]! + s.Pmut[42]!) }
        w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 66 (PS11 * s.Pmut[90]! + PS12 * s.Pmut[18]! - PS13 * s.Pmut[42]! - PS34 * s.Pmut[282]! + PS6 * s.Pmut[306]! - PS9 * s.Pmut[258]! + s.Pmut[66]!) }
        w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 90 (-PS11 * s.Pmut[66]! + PS12 * s.Pmut[42]! + PS13 * s.Pmut[18]! - PS34 * s.Pmut[306]! - PS6 * s.Pmut[282]! + PS7 * s.Pmut[258]! + s.Pmut[90]!) }
        w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 114 (-PS171 * s.Pmut[378]! + PS172 * s.Pmut[354]! + PS173 * s.Pmut[42]! + PS174 * s.Pmut[18]! + PS175 * s.Pmut[66]! - PS176 * s.Pmut[90]! + PS43 * s.Pmut[330]! + s.Pmut[114]!) }
        w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 138 (PS190 * s.Pmut[378]! - PS193 * s.Pmut[330]! + PS201 * s.Pmut[66]! - PS202 * s.Pmut[18]! + PS203 * s.Pmut[90]! - PS204 * s.Pmut[42]! + PS75 * s.Pmut[354]! + s.Pmut[138]!) }
        w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 162 (-PS197 * s.Pmut[354]! + PS199 * s.Pmut[330]! - PS214 * s.Pmut[66]! + PS215 * s.Pmut[90]! + PS216 * s.Pmut[18]! + PS217 * s.Pmut[42]! + PS87 * s.Pmut[378]! + s.Pmut[162]!) }
        w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 186 (s.Pmut[114]! * s.dt + s.Pmut[186]!) }
        w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 210 (s.Pmut[138]! * s.dt + s.Pmut[210]!) }
        w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 234 (s.Pmut[162]! * s.dt + s.Pmut[234]!) }
        w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 258 (s.Pmut[258]!) }
        w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 282 (s.Pmut[282]!) }
        w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 306 (s.Pmut[306]!) }
        w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 330 (s.Pmut[330]!) }
        w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 354 (s.Pmut[354]!) }
        w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 378 (s.Pmut[378]!) }
        w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 402 (s.Pmut[402]!) }
        w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 426 (s.Pmut[426]!) }
        w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 450 (s.Pmut[450]!) }
        w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 19 (-PS11 * s.Pmut[43]! - PS12 * s.Pmut[67]! - PS13 * s.Pmut[91]! + PS6 * s.Pmut[259]! + PS7 * s.Pmut[283]! + PS9 * s.Pmut[307]! + s.Pmut[19]!) }
        w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 43 (PS11 * s.Pmut[19]! - PS12 * s.Pmut[91]! + PS13 * s.Pmut[67]! - PS34 * s.Pmut[259]! - PS7 * s.Pmut[307]! + PS9 * s.Pmut[283]! + s.Pmut[43]!) }
        w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 67 (PS11 * s.Pmut[91]! + PS12 * s.Pmut[19]! - PS13 * s.Pmut[43]! - PS34 * s.Pmut[283]! + PS6 * s.Pmut[307]! - PS9 * s.Pmut[259]! + s.Pmut[67]!) }
        w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 91 (-PS11 * s.Pmut[67]! + PS12 * s.Pmut[43]! + PS13 * s.Pmut[19]! - PS34 * s.Pmut[307]! - PS6 * s.Pmut[283]! + PS7 * s.Pmut[259]! + s.Pmut[91]!) }
        w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 115 (-PS171 * s.Pmut[379]! + PS172 * s.Pmut[355]! + PS173 * s.Pmut[43]! + PS174 * s.Pmut[19]! + PS175 * s.Pmut[67]! - PS176 * s.Pmut[91]! + PS43 * s.Pmut[331]! + s.Pmut[115]!) }
        w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 139 (PS190 * s.Pmut[379]! - PS193 * s.Pmut[331]! + PS201 * s.Pmut[67]! - PS202 * s.Pmut[19]! + PS203 * s.Pmut[91]! - PS204 * s.Pmut[43]! + PS75 * s.Pmut[355]! + s.Pmut[139]!) }
        w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 163 (-PS197 * s.Pmut[355]! + PS199 * s.Pmut[331]! - PS214 * s.Pmut[67]! + PS215 * s.Pmut[91]! + PS216 * s.Pmut[19]! + PS217 * s.Pmut[43]! + PS87 * s.Pmut[379]! + s.Pmut[163]!) }
        w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 187 (s.Pmut[115]! * s.dt + s.Pmut[187]!) }
        w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 211 (s.Pmut[139]! * s.dt + s.Pmut[211]!) }
        w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 235 (s.Pmut[163]! * s.dt + s.Pmut[235]!) }
        w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 259 (s.Pmut[259]!) }
        w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 283 (s.Pmut[283]!) }
        w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 307 (s.Pmut[307]!) }
        w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 331 (s.Pmut[331]!) }
        w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 355 (s.Pmut[355]!) }
        w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 379 (s.Pmut[379]!) }
        w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 403 (s.Pmut[403]!) }
        w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 427 (s.Pmut[427]!) }
        w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 451 (s.Pmut[451]!) }
        w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 475 (s.Pmut[475]!) }
        w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 20 (-PS11 * s.Pmut[44]! - PS12 * s.Pmut[68]! - PS13 * s.Pmut[92]! + PS6 * s.Pmut[260]! + PS7 * s.Pmut[284]! + PS9 * s.Pmut[308]! + s.Pmut[20]!) }
        w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 44 (PS11 * s.Pmut[20]! - PS12 * s.Pmut[92]! + PS13 * s.Pmut[68]! - PS34 * s.Pmut[260]! - PS7 * s.Pmut[308]! + PS9 * s.Pmut[284]! + s.Pmut[44]!) }
        w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 68 (PS11 * s.Pmut[92]! + PS12 * s.Pmut[20]! - PS13 * s.Pmut[44]! - PS34 * s.Pmut[284]! + PS6 * s.Pmut[308]! - PS9 * s.Pmut[260]! + s.Pmut[68]!) }
        w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 92 (-PS11 * s.Pmut[68]! + PS12 * s.Pmut[44]! + PS13 * s.Pmut[20]! - PS34 * s.Pmut[308]! - PS6 * s.Pmut[284]! + PS7 * s.Pmut[260]! + s.Pmut[92]!) }
        w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 116 (-PS171 * s.Pmut[380]! + PS172 * s.Pmut[356]! + PS173 * s.Pmut[44]! + PS174 * s.Pmut[20]! + PS175 * s.Pmut[68]! - PS176 * s.Pmut[92]! + PS43 * s.Pmut[332]! + s.Pmut[116]!) }
        w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 140 (PS190 * s.Pmut[380]! - PS193 * s.Pmut[332]! + PS201 * s.Pmut[68]! - PS202 * s.Pmut[20]! + PS203 * s.Pmut[92]! - PS204 * s.Pmut[44]! + PS75 * s.Pmut[356]! + s.Pmut[140]!) }
        w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 164 (-PS197 * s.Pmut[356]! + PS199 * s.Pmut[332]! - PS214 * s.Pmut[68]! + PS215 * s.Pmut[92]! + PS216 * s.Pmut[20]! + PS217 * s.Pmut[44]! + PS87 * s.Pmut[380]! + s.Pmut[164]!) }
        w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 188 (s.Pmut[116]! * s.dt + s.Pmut[188]!) }
        w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 212 (s.Pmut[140]! * s.dt + s.Pmut[212]!) }
        w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 236 (s.Pmut[164]! * s.dt + s.Pmut[236]!) }
        w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 260 (s.Pmut[260]!) }
        w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 284 (s.Pmut[284]!) }
        w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 308 (s.Pmut[308]!) }
        w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 332 (s.Pmut[332]!) }
        w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 356 (s.Pmut[356]!) }
        w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 380 (s.Pmut[380]!) }
        w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 404 (s.Pmut[404]!) }
        w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 428 (s.Pmut[428]!) }
        w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 452 (s.Pmut[452]!) }
        w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 476 (s.Pmut[476]!) }
        w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 500 (s.Pmut[500]!) }
        w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 21 (-PS11 * s.Pmut[45]! - PS12 * s.Pmut[69]! - PS13 * s.Pmut[93]! + PS6 * s.Pmut[261]! + PS7 * s.Pmut[285]! + PS9 * s.Pmut[309]! + s.Pmut[21]!) }
        w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 45 (PS11 * s.Pmut[21]! - PS12 * s.Pmut[93]! + PS13 * s.Pmut[69]! - PS34 * s.Pmut[261]! - PS7 * s.Pmut[309]! + PS9 * s.Pmut[285]! + s.Pmut[45]!) }
        w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 69 (PS11 * s.Pmut[93]! + PS12 * s.Pmut[21]! - PS13 * s.Pmut[45]! - PS34 * s.Pmut[285]! + PS6 * s.Pmut[309]! - PS9 * s.Pmut[261]! + s.Pmut[69]!) }
        w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 93 (-PS11 * s.Pmut[69]! + PS12 * s.Pmut[45]! + PS13 * s.Pmut[21]! - PS34 * s.Pmut[309]! - PS6 * s.Pmut[285]! + PS7 * s.Pmut[261]! + s.Pmut[93]!) }
        w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 117 (-PS171 * s.Pmut[381]! + PS172 * s.Pmut[357]! + PS173 * s.Pmut[45]! + PS174 * s.Pmut[21]! + PS175 * s.Pmut[69]! - PS176 * s.Pmut[93]! + PS43 * s.Pmut[333]! + s.Pmut[117]!) }
        w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 141 (PS190 * s.Pmut[381]! - PS193 * s.Pmut[333]! + PS201 * s.Pmut[69]! - PS202 * s.Pmut[21]! + PS203 * s.Pmut[93]! - PS204 * s.Pmut[45]! + PS75 * s.Pmut[357]! + s.Pmut[141]!) }
        w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 165 (-PS197 * s.Pmut[357]! + PS199 * s.Pmut[333]! - PS214 * s.Pmut[69]! + PS215 * s.Pmut[93]! + PS216 * s.Pmut[21]! + PS217 * s.Pmut[45]! + PS87 * s.Pmut[381]! + s.Pmut[165]!) }
        w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 189 (s.Pmut[117]! * s.dt + s.Pmut[189]!) }
        w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 213 (s.Pmut[141]! * s.dt + s.Pmut[213]!) }
        w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 237 (s.Pmut[165]! * s.dt + s.Pmut[237]!) }
        w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 261 (s.Pmut[261]!) }
        w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 285 (s.Pmut[285]!) }
        w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 309 (s.Pmut[309]!) }
        w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 333 (s.Pmut[333]!) }
        w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 357 (s.Pmut[357]!) }
        w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 381 (s.Pmut[381]!) }
        w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 405 (s.Pmut[405]!) }
        w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 429 (s.Pmut[429]!) }
        w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 453 (s.Pmut[453]!) }
        w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 477 (s.Pmut[477]!) }
        w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 501 (s.Pmut[501]!) }
        w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 525 (s.Pmut[525]!) }
        if UInt32.toInt32 (UInt8.toUInt32 s.stateIndexLim) > (21 : Int32) then
          w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 22 (-PS11 * s.Pmut[46]! - PS12 * s.Pmut[70]! - PS13 * s.Pmut[94]! + PS6 * s.Pmut[262]! + PS7 * s.Pmut[286]! + PS9 * s.Pmut[310]! + s.Pmut[22]!) }
          w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 46 (PS11 * s.Pmut[22]! - PS12 * s.Pmut[94]! + PS13 * s.Pmut[70]! - PS34 * s.Pmut[262]! - PS7 * s.Pmut[310]! + PS9 * s.Pmut[286]! + s.Pmut[46]!) }
          w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 70 (PS11 * s.Pmut[94]! + PS12 * s.Pmut[22]! - PS13 * s.Pmut[46]! - PS34 * s.Pmut[286]! + PS6 * s.Pmut[310]! - PS9 * s.Pmut[262]! + s.Pmut[70]!) }
          w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 94 (-PS11 * s.Pmut[70]! + PS12 * s.Pmut[46]! + PS13 * s.Pmut[22]! - PS34 * s.Pmut[310]! - PS6 * s.Pmut[286]! + PS7 * s.Pmut[262]! + s.Pmut[94]!) }
          w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 118 (-PS171 * s.Pmut[382]! + PS172 * s.Pmut[358]! + PS173 * s.Pmut[46]! + PS174 * s.Pmut[22]! + PS175 * s.Pmut[70]! - PS176 * s.Pmut[94]! + PS43 * s.Pmut[334]! + s.Pmut[118]!) }
          w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 142 (PS190 * s.Pmut[382]! - PS193 * s.Pmut[334]! + PS201 * s.Pmut[70]! - PS202 * s.Pmut[22]! + PS203 * s.Pmut[94]! - PS204 * s.Pmut[46]! + PS75 * s.Pmut[358]! + s.Pmut[142]!) }
          w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 166 (-PS197 * s.Pmut[358]! + PS199 * s.Pmut[334]! - PS214 * s.Pmut[70]! + PS215 * s.Pmut[94]! + PS216 * s.Pmut[22]! + PS217 * s.Pmut[46]! + PS87 * s.Pmut[382]! + s.Pmut[166]!) }
          w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 190 (s.Pmut[118]! * s.dt + s.Pmut[190]!) }
          w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 214 (s.Pmut[142]! * s.dt + s.Pmut[214]!) }
          w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 238 (s.Pmut[166]! * s.dt + s.Pmut[238]!) }
          w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 262 (s.Pmut[262]!) }
          w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 286 (s.Pmut[286]!) }
          w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 310 (s.Pmut[310]!) }
          w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 334 (s.Pmut[334]!) }
          w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 358 (s.Pmut[358]!) }
          w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 382 (s.Pmut[382]!) }
          w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 406 (s.Pmut[406]!) }
          w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 430 (s.Pmut[430]!) }
          w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 454 (s.Pmut[454]!) }
          w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 478 (s.Pmut[478]!) }
          w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 502 (s.Pmut[502]!) }
          w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 526 (s.Pmut[526]!) }
          w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 550 (s.Pmut[550]!) }
          w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 23 (-PS11 * s.Pmut[47]! - PS12 * s.Pmut[71]! - PS13 * s.Pmut[95]! + PS6 * s.Pmut[263]! + PS7 * s.Pmut[287]! + PS9 * s.Pmut[311]! + s.Pmut[23]!) }
          w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 47 (PS11 * s.Pmut[23]! - PS12 * s.Pmut[95]! + PS13 * s.Pmut[71]! - PS34 * s.Pmut[263]! - PS7 * s.Pmut[311]! + PS9 * s.Pmut[287]! + s.Pmut[47]!) }
          w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 71 (PS11 * s.Pmut[95]! + PS12 * s.Pmut[23]! - PS13 * s.Pmut[47]! - PS34 * s.Pmut[287]! + PS6 * s.Pmut[311]! - PS9 * s.Pmut[263]! + s.Pmut[71]!) }
          w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 95 (-PS11 * s.Pmut[71]! + PS12 * s.Pmut[47]! + PS13 * s.Pmut[23]! - PS34 * s.Pmut[311]! - PS6 * s.Pmut[287]! + PS7 * s.Pmut[263]! + s.Pmut[95]!) }
          w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 119 (-PS171 * s.Pmut[383]! + PS172 * s.Pmut[359]! + PS173 * s.Pmut[47]! + PS174 * s.Pmut[23]! + PS175 * s.Pmut[71]! - PS176 * s.Pmut[95]! + PS43 * s.Pmut[335]! + s.Pmut[119]!) }
          w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 143 (PS190 * s.Pmut[383]! - PS193 * s.Pmut[335]! + PS201 * s.Pmut[71]! - PS202 * s.Pmut[23]! + PS203 * s.Pmut[95]! - PS204 * s.Pmut[47]! + PS75 * s.Pmut[359]! + s.Pmut[143]!) }
          w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 167 (-PS197 * s.Pmut[359]! + PS199 * s.Pmut[335]! - PS214 * s.Pmut[71]! + PS215 * s.Pmut[95]! + PS216 * s.Pmut[23]! + PS217 * s.Pmut[47]! + PS87 * s.Pmut[383]! + s.Pmut[167]!) }
          w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 191 (s.Pmut[119]! * s.dt + s.Pmut[191]!) }
          w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 215 (s.Pmut[143]! * s.dt + s.Pmut[215]!) }
          w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 239 (s.Pmut[167]! * s.dt + s.Pmut[239]!) }
          w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 263 (s.Pmut[263]!) }
          w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 287 (s.Pmut[287]!) }
          w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 311 (s.Pmut[311]!) }
          w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 335 (s.Pmut[335]!) }
          w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 359 (s.Pmut[359]!) }
          w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 383 (s.Pmut[383]!) }
          w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 407 (s.Pmut[407]!) }
          w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 431 (s.Pmut[431]!) }
          w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 455 (s.Pmut[455]!) }
          w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 479 (s.Pmut[479]!) }
          w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 503 (s.Pmut[503]!) }
          w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 527 (s.Pmut[527]!) }
          w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 551 (s.Pmut[551]!) }
          w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! 575 (s.Pmut[575]!) }
  if UInt32.toInt32 (UInt8.toUInt32 s.stateIndexLim) > (9 : Int32) then
    let t'4 : UInt8 := Int8.toUInt8 (Int32.toInt8 (10 : Int32))
    let t'5 : Int32 := UInt32.toInt32 (UInt8.toUInt32 s.stateIndexLim)
    for i'6' in [0:(t'5.toInt - (Int.ofNat t'4.toNat) + 1).toNat] do  -- C++ loop bounded by a runtime value (--runtime-loops)
      let i'6 : UInt8 := t'4 + Nat.toUInt8 i'6'
      w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! (UInt8.toNat i'6 * 24 + UInt8.toNat i'6) (w.NavEKF_core_common'KHP[UInt8.toNat i'6 * 24 + UInt8.toNat i'6]! + processNoiseVariance[Int32.toNatClampNeg (UInt32.toInt32 (UInt8.toUInt32 i'6) - (10 : Int32))]!) }
  if (s.Pmut[175]! + s.Pmut[200]!) > (Binary64.ofBits 0x40c3880000000000 /- 1e4f -/) then
    for i'7' in [7:9] do
      let i'7 : UInt8 := Nat.toUInt8 i'7'
      let t'6 : UInt8 := Int8.toUInt8 (Int32.toInt8 (0 : Int32))
      let t'7 : Int32 := UInt32.toInt32 (UInt8.toUInt32 s.stateIndexLim)
      for j' in [0:(t'7.toInt - (Int.ofNat t'6.toNat) + 1).toNat] do  -- C++ loop bounded by a runtime value (--runtime-loops)
        let j : UInt8 := t'6 + Nat.toUInt8 j'
        w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! (UInt8.toNat i'7 * 24 + UInt8.toNat j) (s.Pmut[UInt8.toNat i'7 * 24 + UInt8.toNat j]!) }
        w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! (UInt8.toNat j * 24 + UInt8.toNat i'7) (s.Pmut[UInt8.toNat j * 24 + UInt8.toNat i'7]!) }
  let t'8 : UInt8 := Int8.toUInt8 (Int32.toInt8 (0 : Int32))
  let t'9 : Int32 := UInt32.toInt32 (UInt8.toUInt32 s.stateIndexLim)
  for row'2' in [0:(t'9.toInt - (Int.ofNat t'8.toNat) + 1).toNat] do  -- C++ loop bounded by a runtime value (--runtime-loops)
    let row'2 : UInt8 := t'8 + Nat.toUInt8 row'2'
    s := { s with Pmut := s.Pmut.set! (UInt8.toNat row'2 * 24 + UInt8.toNat row'2) (w.NavEKF_core_common'KHP[UInt8.toNat row'2 * 24 + UInt8.toNat row'2]!) }
    for column'2' in [0:row'2.toNat] do
      let column'2 : UInt8 := Nat.toUInt8 column'2'
      s := { s with Pmut := s.Pmut.set! (UInt8.toNat column'2 * 24 + UInt8.toNat row'2) (w.NavEKF_core_common'KHP[UInt8.toNat column'2 * 24 + UInt8.toNat row'2]!) }
      s := { s with Pmut := s.Pmut.set! (UInt8.toNat row'2 * 24 + UInt8.toNat column'2) (s.Pmut[UInt8.toNat column'2 * 24 + UInt8.toNat row'2]!) }
  if !s.inhibitDelVelBiasStates then
    for index'2' in [0:3] do
      let index'2 : UInt8 := Nat.toUInt8 index'2'
      let stateIndex'2 : UInt8 := Int8.toUInt8 (Int32.toInt8 (UInt32.toInt32 (UInt8.toUInt32 index'2) + (13 : Int32)))
      if s.dvelBiasAxisInhibit[UInt8.toNat index'2]! then
        s := zeroStatesVarCov s stateIndex'2 stateIndex'2
        s := { s with Pmut := s.Pmut.set! (UInt8.toNat stateIndex'2 * 24 + UInt8.toNat stateIndex'2) (match UInt8.toNat index'2 with | 0 => s.dvelBiasAxisVarPrev.x | 1 => s.dvelBiasAxisVarPrev.y | _ => s.dvelBiasAxisVarPrev.z) }
  s := ConstrainVariances s w
  if s.vertVelVarClipCounter > Int32.toUInt32 (0 : Int32) then
    s := { s with vertVelVarClipCounter := s.vertVelVarClipCounter - (1 : UInt32) }
  s := calcTiltErrorVariance s
  pure ()  -- C++ `verifyTiltErrorVariance`: no effect in the model
  return (s, w, rotVarVecPtr)

end NavEKF3_core

namespace NavEKF3_core

/-- C++ `bool NavEKF3_core::getOriginLLH(Location & loc) const`, `AP_NavEKF3/AP_NavEKF3_Outputs.cpp:397-407`. -/
def getOriginLLH (s : State) (w : World) (loc : Location.State) : Location.State × Bool := Id.run do
  let mut loc := loc
  if s.validOrigin then
    loc := w.EKF3.common_EKF_origin
    if (UInt32.toInt32 (UInt8.toUInt32 (AP_ParamT_unsigned_char_1.op_to_unsigned_char w.EKF3._originHgtMode)) &&& ((1 : Int32) <<< (2 : Int32))) == (0 : Int32) then
      loc := { loc with alt := Binary32.toInt32 ((Binary32.ofBits 0x42c80000 /- 100.0f -/) * Binary64.toBinary32 s.ekfGpsRefHgt) }
  return (loc, s.validOrigin)

end NavEKF3_core

namespace NavEKF3

/-- C++ `bool NavEKF3::getOriginLLH(Location & loc) const`, `AP_NavEKF3/AP_NavEKF3.cpp:1448-1458`. -/
def getOriginLLH (s : State) (w : World) (loc : Location.State) : World × Location.State × Bool := Id.run do
  let mut w := w
  let mut loc := loc
  if !(s.core != WPtr.null) then
    return (w, loc, false)
  if s.common_origin_valid then
    loc := s.common_EKF_origin
    return (w, loc, true)
  w := { w with EKF3 := s }  -- this object's state into the World: the call reaches it
  let (t'1, t'2) := NavEKF3_core.getOriginLLH w.heap'NavEKF3_core[((WPtr.index s.core) + (UInt8.toNat s.primary))]! w loc
  loc := t'1
  return (w, loc, t'2)

end NavEKF3

namespace NavEKF3

/-- C++ `bool NavEKF3::setOriginLLH(const Location & loc)`, `AP_NavEKF3/AP_NavEKF3.cpp:1464-1483`. -/
def setOriginLLH (s : State) (w : World) (o : Outputs) (loc : Location.State) : State × World × Outputs × Bool := Id.run do
  let mut s := s
  let mut w := w
  let mut o := o
  let t'1 := w.heap'AP_DAL[(WPtr.index w.AP_DAL'_singleton)]!  -- the object out of its slot for the call (--swap-out)
  w := { w with heap'AP_DAL := w.heap'AP_DAL.set! (WPtr.index w.AP_DAL'_singleton) default }
  w := { w with heap'AP_DAL := w.heap'AP_DAL.set! (WPtr.index w.AP_DAL'_singleton) (AP_DAL.log_SetOriginLLH3 t'1 loc) }
  if !(s.core != WPtr.null) then
    return (s, w, o, false)
  if s.common_origin_valid then
    o := o.push (Output.send_text (4 : UInt32) "EKF3: origin already set" #[])
    return (s, w, o, false)
  let mut ret : Bool := false
  let t'2 : UInt8 := Int8.toUInt8 (Int32.toInt8 (0 : Int32))
  let t'3 : Int32 := UInt32.toInt32 (UInt8.toUInt32 s.num_cores)
  for i' in [0:(t'3.toInt - (Int.ofNat t'2.toNat)).toNat] do  -- C++ loop bounded by a runtime value (--runtime-loops)
    let i : UInt8 := t'2 + Nat.toUInt8 i'
    w := { w with EKF3 := s }  -- this object's state into the World: the call reaches it
    let t'4 := w.heap'NavEKF3_core[((WPtr.index s.core) + (UInt8.toNat i))]!  -- the object out of its slot for the call (--swap-out)
    w := { w with heap'NavEKF3_core := w.heap'NavEKF3_core.set! ((WPtr.index s.core) + (UInt8.toNat i)) default }
    let (t'5, t'6, t'7, t'8) := NavEKF3_core.setOriginLLH t'4 w o loc
    w := t'6
    w := { w with heap'NavEKF3_core := w.heap'NavEKF3_core.set! ((WPtr.index s.core) + (UInt8.toNat i)) t'5 }
    o := t'7
    s := w.EKF3  -- this object's state as the call left it
    ret := (if ret then (1 : Int32) else (0 : Int32)) ||| (if t'8 then (1 : Int32) else (0 : Int32)) != (0 : Int32)
  return (s, w, o, ret)

end NavEKF3

namespace NavEKF3

/-- C++ `bool NavEKF3::getAirSpdVec(Vector3f & vel) const`, `AP_NavEKF3/AP_NavEKF3.cpp:1268-1274`. -/
def getAirSpdVec (s : State) (w : World) (vel : Vector3f.State) : Vector3f.State × Bool := Id.run do
  let mut vel := vel
  if (s.core != WPtr.null) then
    let (t'1, t'2) := NavEKF3_core.getAirSpdVec w.heap'NavEKF3_core[((WPtr.index s.core) + (UInt8.toNat s.primary))]! vel
    vel := t'1
    return (vel, t'2)
  return (vel, false)

end NavEKF3

namespace NavEKF3

/-- C++ `void NavEKF3::updateLaneSwitchYawResetData(uint8_t new_primary)`, `AP_NavEKF3/AP_NavEKF3.cpp:1912-1919`. -/
def updateLaneSwitchYawResetData (s : State) (w : World) (new_primary : UInt8) : State := Id.run do
  let mut s := s
  s := { s with yaw_reset_data.last_core_count := NavEKF3_core.getYawResetCount w.heap'NavEKF3_core[((WPtr.index s.core) + (UInt8.toNat new_primary))]! }
  s := { s with yaw_reset_data.count := s.yaw_reset_data.count + (1 : UInt16) }
  return s

end NavEKF3

namespace NavEKF3

/-- C++ `void NavEKF3::updateLaneSwitchPosResetData(uint8_t new_primary)`, `AP_NavEKF3/AP_NavEKF3.cpp:1922-1930`. -/
def updateLaneSwitchPosResetData (s : State) (w : World) (new_primary : UInt8) : State := Id.run do
  let mut s := s
  s := { s with pos_reset_data.last_core_count := NavEKF3_core.getPosNorthEastResetCount w.heap'NavEKF3_core[((WPtr.index s.core) + (UInt8.toNat new_primary))]! }
  s := { s with pos_reset_data.count := s.pos_reset_data.count + (1 : UInt16) }
  return s

end NavEKF3

namespace NavEKF3

/-- C++ `bool NavEKF3::coreBetterScore(uint8_t new_core, uint8_t current_core) const`, `AP_NavEKF3/AP_NavEKF3.cpp:912-932`. -/
def coreBetterScore (s : State) (w : World) (new_core : UInt8) (current_core : UInt8) : Bool := Id.run do
  if !(NavEKF3_core.healthy w.heap'NavEKF3_core[((WPtr.index s.core) + (UInt8.toNat new_core))]!) then
    return false
  if (if NavEKF3_core.have_aligned_tilt w.heap'NavEKF3_core[((WPtr.index s.core) + (UInt8.toNat new_core))]! then (1 : Int32) else (0 : Int32)) != (if NavEKF3_core.have_aligned_tilt w.heap'NavEKF3_core[((WPtr.index s.core) + (UInt8.toNat current_core))]! then (1 : Int32) else (0 : Int32)) then
    return NavEKF3_core.have_aligned_tilt w.heap'NavEKF3_core[((WPtr.index s.core) + (UInt8.toNat new_core))]!
  if (if NavEKF3_core.have_aligned_yaw w.heap'NavEKF3_core[((WPtr.index s.core) + (UInt8.toNat new_core))]! then (1 : Int32) else (0 : Int32)) != (if NavEKF3_core.have_aligned_yaw w.heap'NavEKF3_core[((WPtr.index s.core) + (UInt8.toNat current_core))]! then (1 : Int32) else (0 : Int32)) then
    return NavEKF3_core.have_aligned_yaw w.heap'NavEKF3_core[((WPtr.index s.core) + (UInt8.toNat new_core))]!
  return decide (s.coreRelativeErrors[UInt8.toNat new_core]! < s.coreRelativeErrors[UInt8.toNat current_core]!)

end NavEKF3

namespace NavEKF3_core

/-- C++ `ftype NavEKF3_core::getGyroBiasLimit() const`, `AP_NavEKF3/AP_NavEKF3_GyroBias.cpp:30-33`. -/
def getGyroBiasLimit (s : State) (w : World) : Binary64 := Id.run do
  return Binary32.toBinary64 (AP_DAL_InertialSensor.get_gyro_bias_limit w.heap'AP_DAL[(WPtr.index w.AP_DAL'_singleton)]!._ins s.imu_index)

/-- C++ `void NavEKF3_core::MagTableConstrain()`, `AP_NavEKF3/AP_NavEKF3_core.cpp:2004-2017`. -/
def MagTableConstrain (s : State) (w : World) : State := Id.run do
  let mut s := s
  let limit_ga : Binary64 := Binary32.toBinary64 (Int32.toBinary32 (Int16.toInt32 (AP_ParamT_short_2.op_to_short w.EKF3._mag_ef_limit)) * (Binary32.ofBits 0x3a83126f /- 0.001f -/))
  s := { s with statesArray := s.statesArray.set! 16 (Estimator_lib.constrain_value_line_double s.statesArray[16]! (s.table_earth_field_ga.x - limit_ga) (s.table_earth_field_ga.x + limit_ga) (Int32.toUInt32 (2010 : Int32))) }
  s := { s with statesArray := s.statesArray.set! 17 (Estimator_lib.constrain_value_line_double s.statesArray[17]! (s.table_earth_field_ga.y - limit_ga) (s.table_earth_field_ga.y + limit_ga) (Int32.toUInt32 (2013 : Int32))) }
  s := { s with statesArray := s.statesArray.set! 18 (Estimator_lib.constrain_value_line_double s.statesArray[18]! (s.table_earth_field_ga.z - limit_ga) (s.table_earth_field_ga.z + limit_ga) (Int32.toUInt32 (2016 : Int32))) }
  return s

end NavEKF3_core

namespace NavEKF3_core

/-- C++ `void NavEKF3_core::ConstrainStates()`, `AP_NavEKF3/AP_NavEKF3_core.cpp:2020-2068`. -/
def ConstrainStates (s : State) (w : World) : State := Id.run do
  let mut s := s
  for i' in [0:4] do
    let i : UInt8 := Nat.toUInt8 i'
    s := { s with statesArray := s.statesArray.set! (UInt8.toNat i) (Estimator_lib.constrain_value_line_double s.statesArray[UInt8.toNat i]! (Binary64.ofBits 0xbff0000000000000 /- (double)-1 -/) (Binary64.ofBits 0x3ff0000000000000 /- (double)1 -/) (Int32.toUInt32 (2040 : Int32))) }
  for i'2' in [4:7] do
    let i'2 : UInt8 := Nat.toUInt8 i'2'
    s := { s with statesArray := s.statesArray.set! (UInt8.toNat i'2) (Estimator_lib.constrain_value_line_double s.statesArray[UInt8.toNat i'2]! (Binary64.ofBits 0xc07f400000000000 /- (double)-500 -/) (Binary64.ofBits 0x407f400000000000 /- (double)500 -/) (Int32.toUInt32 (2042 : Int32))) }
  for i'3' in [7:9] do
    let i'3 : UInt8 := Nat.toUInt8 i'3'
    s := { s with statesArray := s.statesArray.set! (UInt8.toNat i'3) (Estimator_lib.constrain_value_line_double s.statesArray[UInt8.toNat i'3]! (Binary64.ofBits 0xc187d78400000000 /- (double)-50000000 -/) (Binary64.ofBits 0x4187d78400000000 /- (double)50000000 -/) (Int32.toUInt32 (2044 : Int32))) }
  s := { s with statesArray := s.statesArray.set! 9 (Estimator_lib.constrain_value_line_double s.statesArray[9]! (Binary64.ofBits 0xc0e3880000000000 /- (double)-40000 -/) (Binary64.ofBits 0x40c3880000000000 /- (double)10000 -/) (Int32.toUInt32 (2046 : Int32))) }
  let gyro_bias_limit : Binary64 := getGyroBiasLimit s w
  for i'4' in [10:13] do
    let i'4 : UInt8 := Nat.toUInt8 i'4'
    s := { s with statesArray := s.statesArray.set! (UInt8.toNat i'4) (Estimator_lib.constrain_value_line_double s.statesArray[UInt8.toNat i'4]! (-gyro_bias_limit * s.dtEkfAvg) (gyro_bias_limit * s.dtEkfAvg) (Int32.toUInt32 (2049 : Int32))) }
  for i'5' in [13:16] do
    let i'5 : UInt8 := Nat.toUInt8 i'5'
    s := { s with statesArray := s.statesArray.set! (UInt8.toNat i'5) (Estimator_lib.constrain_value_line_double s.statesArray[UInt8.toNat i'5]! (Binary32.toBinary64 (AP_ParamT_float_4.op_sub_void w.EKF3._accBiasLim) * s.dtEkfAvg) (Binary32.toBinary64 (AP_ParamT_float_4.op_to_float w.EKF3._accBiasLim) * s.dtEkfAvg) (Int32.toUInt32 (2051 : Int32))) }
  if decide (Int16.toInt32 (AP_ParamT_short_2.op_to_short w.EKF3._mag_ef_limit) ≤ (0 : Int32)) || !s.have_table_earth_field then
    for i'6' in [16:19] do
      let i'6 : UInt8 := Nat.toUInt8 i'6'
      s := { s with statesArray := s.statesArray.set! (UInt8.toNat i'6) (Estimator_lib.constrain_value_line_double s.statesArray[UInt8.toNat i'6]! (Binary64.ofBits 0xbff0000000000000 /- (double)-1 -/) (Binary64.ofBits 0x3ff0000000000000 /- (double)1 -/) (Int32.toUInt32 (2055 : Int32))) }
  else
    s := MagTableConstrain s w
  for i'7' in [19:22] do
    let i'7 : UInt8 := Nat.toUInt8 i'7'
    s := { s with statesArray := s.statesArray.set! (UInt8.toNat i'7) (Estimator_lib.constrain_value_line_double s.statesArray[UInt8.toNat i'7]! (Binary64.ofBits 0xbfe0000000000000 /- (double)-1/2 -/) (Binary64.ofBits 0x3fe0000000000000 /- (double)1/2 -/) (Int32.toUInt32 (2061 : Int32))) }
  for i'8' in [22:24] do
    let i'8 : UInt8 := Nat.toUInt8 i'8'
    s := { s with statesArray := s.statesArray.set! (UInt8.toNat i'8) (Estimator_lib.constrain_value_line_double s.statesArray[UInt8.toNat i'8]! (Binary64.ofBits 0xc059000000000000 /- (double)-100 -/) (Binary64.ofBits 0x4059000000000000 /- (double)100 -/) (Int32.toUInt32 (2063 : Int32))) }
  if !s.inhibitGndState then
    s := { s with terrainState := Estimator_lib.MAX_double2 s.terrainState (s.statesArray[9]! + s.rngOnGnd) }
  return s

/-- C++ `void NavEKF3_core::UpdateStrapdownEquationsNED()`, `AP_NavEKF3/AP_NavEKF3_core.cpp:731-793`. -/
def UpdateStrapdownEquationsNED (s : State) (w : World) : State := Id.run do
  let mut s := s
  let t'1 := QuaternionT_double.rotate_Vector3p ({ q1 := s.statesArray[0]!, q2 := s.statesArray[1]!, q3 := s.statesArray[2]!, q4 := s.statesArray[3]! } : QuaternionT_double.State) (Vector3p.op_sub_Vector3p s.delAngCorrected (Vector3p.op_mul_double (Matrix3_double.op_mul_Vector3p s.prevTnb s.earthRateNED) s.imuDataDelayed.delAngDT))
  s := { s with statesArray := ((((s.statesArray.set! 0 t'1.q1).set! 1 t'1.q2).set! 2 t'1.q3).set! 3 t'1.q4) }
  let t'2 := QuaternionT_double.normalize ({ q1 := s.statesArray[0]!, q2 := s.statesArray[1]!, q3 := s.statesArray[2]!, q4 := s.statesArray[3]! } : QuaternionT_double.State)
  s := { s with statesArray := ((((s.statesArray.set! 0 t'2.q1).set! 1 t'2.q2).set! 2 t'2.q3).set! 3 t'2.q4) }
  let mut delVelNav : Vector3p.State := Vector3p.init_void
  delVelNav := Matrix3_double.mul_transpose s.prevTnb s.delVelCorrected
  delVelNav := { delVelNav with z := delVelNav.z + (Binary64.ofBits 0x40239d0140000000 /- (double)5141509/524288 -/) * s.imuDataDelayed.delVelDT }
  s := { s with prevTnb := QuaternionT_double.rotation_matrix_Matrix3_double (QuaternionT_double.inverse ({ q1 := s.statesArray[0]!, q2 := s.statesArray[1]!, q3 := s.statesArray[2]!, q4 := s.statesArray[3]! } : QuaternionT_double.State)) s.prevTnb }
  s := { s with velDotNED := Vector3p.op_div delVelNav s.imuDataDelayed.delVelDT }
  s := { s with velDotNEDfilt := Vector3p.op_add (Vector3p.op_mul_double s.velDotNED (Binary64.ofBits 0x3fa99999a0000000 /- 0.05f -/)) (Vector3p.op_mul_double s.velDotNEDfilt (Binary64.ofBits 0x3fee666660000000 /- 0.95f -/)) }
  s := { s with accNavMag := Vector3p.length s.velDotNEDfilt }
  s := { s with accNavMagHoriz := Vector2p.length ({ x := s.velDotNEDfilt.x, y := s.velDotNEDfilt.y } : Vector2p.State) }
  if (UInt32.toInt32 (NavEKF3_core.AidingMode.toInt s.PV_AidingMode) == UInt32.toInt32 (NavEKF3_core.AidingMode.toInt NavEKF3_core.AidingMode.AID_NONE)) && (decide (s.accNavMagHoriz > (Binary64.ofBits 0x4014000000000000 /- 5.0f -/))) then
    let gain : Binary64 := (Binary64.ofBits 0x4014000000000000 /- 5.0f -/) / s.accNavMagHoriz
    delVelNav := { delVelNav with x := delVelNav.x * gain }
    delVelNav := { delVelNav with y := delVelNav.y * gain }
  let lastVelocity : Vector3p.State := ({ x := s.statesArray[4]!, y := s.statesArray[5]!, z := s.statesArray[6]! } : Vector3p.State)
  let (t'3, _) := Vector3p.op_add_assign ({ x := s.statesArray[4]!, y := s.statesArray[5]!, z := s.statesArray[6]! } : Vector3p.State) delVelNav
  s := { s with statesArray := (((s.statesArray.set! 4 t'3.x).set! 5 t'3.y).set! 6 t'3.z) }
  let (t'5, _) := Vector3p.op_add_assign ({ x := s.statesArray[7]!, y := s.statesArray[8]!, z := s.statesArray[9]! } : Vector3p.State) (Vector3p.op_mul_double (Vector3p.op_add ({ x := s.statesArray[4]!, y := s.statesArray[5]!, z := s.statesArray[6]! } : Vector3p.State) lastVelocity) (s.imuDataDelayed.delVelDT * (Binary64.ofBits 0x3fe0000000000000 /- 0.5f -/)))
  s := { s with statesArray := (((s.statesArray.set! 7 t'5.x).set! 8 t'5.y).set! 9 t'5.z) }
  let (t'7, _) := Vector3p.op_add_assign s.delAngBodyOF s.delAngCorrected
  s := { s with delAngBodyOF := t'7 }
  s := { s with delTimeOF := s.delTimeOF + s.imuDataDelayed.delAngDT }
  s := ConstrainStates s w
  return s

end NavEKF3_core

namespace NavEKF3_core

/-- C++ `void NavEKF3_core::runYawEstimatorPrediction()`, `AP_NavEKF3/AP_NavEKF3_Control.cpp:836-856`. -/
def runYawEstimatorPrediction (s : State) (w : World) : World := Id.run do
  let mut w := w
  if s.yawEstimator == WPtr.null then
    return w
  if AP_NavEKF_Source.getPosXYSource w.EKF3.sources s.core_index != AP_NavEKF_Source.SourceXY.GPS || !(AP_NavEKF_Source.useVelXYSource w.EKF3.sources AP_NavEKF_Source.SourceXY.GPS s.core_index) then
    return w
  let mut trueAirspeed : Binary64 := (Binary64.ofBits 0x0000000000000000 /- 0.0 -/)  -- uninitialized in C++; assigned before every read
  if s.tas.dataDelayed.allowFusion && assume_zero_sideslip w then
    trueAirspeed := Estimator_lib.MAX_double_float s.tas.dataDelayed.tas (Binary32.ofBits 0x00000000 /- 0.0f -/)
  else
    trueAirspeed := (Binary64.ofBits 0x0000000000000000 /- 0.0f -/)
  let t'1 := w.heap'EKFGSF_yaw[(WPtr.index s.yawEstimator)]!  -- the object out of its slot for the call (--swap-out)
  w := { w with heap'EKFGSF_yaw := w.heap'EKFGSF_yaw.set! (WPtr.index s.yawEstimator) default }
  w := { w with heap'EKFGSF_yaw := w.heap'EKFGSF_yaw.set! (WPtr.index s.yawEstimator) (EKFGSF_yaw.update t'1 s.imuDataDelayed.delAng s.imuDataDelayed.delVel s.imuDataDelayed.delAngDT s.imuDataDelayed.delVelDT s.EKFGSF_run_filterbank trueAirspeed) }
  return w

end NavEKF3_core

namespace NavEKF3_core

/-- C++ `bool NavEKF3_core::EKFGSF_getYaw(ftype & yaw, ftype & yawVariance) const`, `AP_NavEKF3/AP_NavEKF3_MagFusion.cpp:1545-1561`. -/
def EKFGSF_getYaw (s : State) (w : World) (yaw : Binary64) (yawVariance : Binary64) : Binary64 × Binary64 × Bool := Id.run do
  let mut yaw := yaw
  let mut yawVariance := yawVariance
  if s.yawEstimator == WPtr.null then
    return (yaw, yawVariance, false)
  let mut velInnovLength : Binary64 := (Binary64.ofBits 0x0000000000000000 /- 0.0 -/)  -- uninitialized in C++; assigned before every read
  let (t'1, t'2, _, t'3) := EKFGSF_yaw.getYawData w.heap'EKFGSF_yaw[(WPtr.index s.yawEstimator)]! yaw yawVariance false (0 : UInt8)
  yaw := t'1
  yawVariance := t'2
  let mut t'7 := t'3 && Estimator_lib.is_positive_double yawVariance && decide (yawVariance < Binary32.toBinary64 (Estimator_lib.sq_float (Estimator_lib.radians_float (Binary32.ofBits 0x41700000 /- 15 -/))))
  if t'7 then
    let mut t'6 := assume_zero_sideslip w
    if !t'6 then
      let (t'4, t'5) := EKFGSF_yaw.getVelInnovLength w.heap'EKFGSF_yaw[(WPtr.index s.yawEstimator)]! velInnovLength
      velInnovLength := t'4
      t'6 := (t'5 && decide (velInnovLength < Binary32.toBinary64 w.EKF3.maxYawEstVelInnov))
    t'7 := t'6
  if t'7 then
    return (yaw, yawVariance, true)
  return (yaw, yawVariance, false)

/-- C++ `void NavEKF3_core::recordYawResetsCompleted()`, `AP_NavEKF3/AP_NavEKF3_Control.cpp:754-762`. -/
def recordYawResetsCompleted (s : State) : State := Id.run do
  let mut s := s
  s := { s with gpsYawResetRequest := false }
  s := { s with magYawResetRequest := false }
  s := { s with yawAlignComplete := true }
  if s.inFlight then
    s := { s with finalInflightYawInit := true }
  return s

end NavEKF3_core

namespace NavEKF3_core

/-- C++ `void NavEKF3_core::StoreQuatRotate(const QuaternionF & deltaQuat)`, `AP_NavEKF3/AP_NavEKF3_core.cpp:1836-1844`. -/
def StoreQuatRotate (s : State) (deltaQuat : QuaternionT_double.State) : State := Id.run do
  let mut s := s
  s := { s with outputDataNew.quat := QuaternionT_double.op_mul_QuaternionT_double s.outputDataNew.quat deltaQuat }
  let t'1 : UInt8 := Int8.toUInt8 (Int32.toInt8 (0 : Int32))
  let t'2 : Int32 := UInt32.toInt32 (UInt8.toUInt32 s.imu_buffer_length)
  for i' in [0:(t'2.toInt - (Int.ofNat t'1.toNat)).toNat] do  -- C++ loop bounded by a runtime value (--runtime-loops)
    let i : UInt8 := t'1 + Nat.toUInt8 i'
    s := { s with storedOutput.buffer := s.storedOutput.buffer.set! (UInt8.toNat (UInt32.toUInt8 (UInt8.toUInt32 i))) ({ s.storedOutput.buffer[UInt8.toNat (UInt32.toUInt8 (UInt8.toUInt32 i))]! with quat := QuaternionT_double.op_mul_QuaternionT_double s.storedOutput.buffer[UInt8.toNat (UInt32.toUInt8 (UInt8.toUInt32 i))]!.quat deltaQuat }) }
  s := { s with outputDataDelayed.quat := QuaternionT_double.op_mul_QuaternionT_double s.outputDataDelayed.quat deltaQuat }
  return s

/-- C++ `void NavEKF3_core::resetQuatStateYawOnly(ftype yaw, ftype yawVariance, rotationOrder order)`, `AP_NavEKF3/AP_NavEKF3_MagFusion.cpp:1563-1600`. -/
def resetQuatStateYawOnly (s : State) (w : World) (yaw : Binary64) (yawVariance : Binary64) (order : NavEKF3_core.rotationOrder) : State × World := Id.run do
  let mut s := s
  let mut w := w
  let quatBeforeReset : QuaternionT_double.State := ({ q1 := s.statesArray[0]!, q2 := s.statesArray[1]!, q3 := s.statesArray[2]!, q4 := s.statesArray[3]! } : QuaternionT_double.State)
  s := { s with prevTnb := QuaternionT_double.rotation_matrix_Matrix3_double (QuaternionT_double.inverse ({ q1 := s.statesArray[0]!, q2 := s.statesArray[1]!, q3 := s.statesArray[2]!, q4 := s.statesArray[3]! } : QuaternionT_double.State)) s.prevTnb }
  let mut eulerAngles : Vector3p.State := Vector3p.init_void
  if order == NavEKF3_core.rotationOrder.TAIT_BRYAN_321 then
    let (t'1, t'2, t'3) := QuaternionT_double.to_euler_double3 ({ q1 := s.statesArray[0]!, q2 := s.statesArray[1]!, q3 := s.statesArray[2]!, q4 := s.statesArray[3]! } : QuaternionT_double.State) eulerAngles.x eulerAngles.y eulerAngles.z
    eulerAngles := { eulerAngles with x := t'1 }
    eulerAngles := { eulerAngles with y := t'2 }
    eulerAngles := { eulerAngles with z := t'3 }
    let t'4 := QuaternionT_double.from_euler_double3 ({ q1 := s.statesArray[0]!, q2 := s.statesArray[1]!, q3 := s.statesArray[2]!, q4 := s.statesArray[3]! } : QuaternionT_double.State) eulerAngles.x eulerAngles.y yaw
    s := { s with statesArray := ((((s.statesArray.set! 0 t'4.q1).set! 1 t'4.q2).set! 2 t'4.q3).set! 3 t'4.q4) }
  else if order == NavEKF3_core.rotationOrder.TAIT_BRYAN_312 then
    eulerAngles := QuaternionT_double.to_vector312 ({ q1 := s.statesArray[0]!, q2 := s.statesArray[1]!, q3 := s.statesArray[2]!, q4 := s.statesArray[3]! } : QuaternionT_double.State)
    let t'5 := QuaternionT_double.from_vector312 ({ q1 := s.statesArray[0]!, q2 := s.statesArray[1]!, q3 := s.statesArray[2]!, q4 := s.statesArray[3]! } : QuaternionT_double.State) eulerAngles.x eulerAngles.y yaw
    s := { s with statesArray := ((((s.statesArray.set! 0 t'5.q1).set! 1 t'5.q2).set! 2 t'5.q3).set! 3 t'5.q4) }
  else
    return (s, w)
  s := { s with prevTnb := QuaternionT_double.rotation_matrix_Matrix3_double (QuaternionT_double.inverse ({ q1 := s.statesArray[0]!, q2 := s.statesArray[1]!, q3 := s.statesArray[2]!, q4 := s.statesArray[3]! } : QuaternionT_double.State)) s.prevTnb }
  let quat_delta : QuaternionT_double.State := QuaternionT_double.op_div ({ q1 := s.statesArray[0]!, q2 := s.statesArray[1]!, q3 := s.statesArray[2]!, q4 := s.statesArray[3]! } : QuaternionT_double.State) quatBeforeReset
  s := StoreQuatRotate s quat_delta
  let mut angleErrVarVec : Vector3p.State := Vector3p.init_double3 ((Binary64.ofBits 0x3fe0000000000000 /- 0.5 -/) * s.tiltErrorVariance) ((Binary64.ofBits 0x3fe0000000000000 /- 0.5 -/) * s.tiltErrorVariance) yawVariance
  let (t'6, t'7, t'8) := CovariancePrediction s w true angleErrVarVec
  w := t'7
  s := t'6
  angleErrVarVec := t'8
  s := { s with yawResetCount := s.yawResetCount + (1 : UInt16) }
  s := recordYawResetsCompleted s
  return (s, w)

/-- C++ `bool NavEKF3_core::EKFGSF_resetMainFilterYaw(bool emergency_reset)`, `AP_NavEKF3/AP_NavEKF3_MagFusion.cpp:1488-1542`. -/
def EKFGSF_resetMainFilterYaw (s : State) (w : World) (o : Outputs) (emergency_reset : Bool) : State × World × Outputs × Bool := Id.run do
  let mut s := s
  let mut w := w
  let mut o := o
  if (s.yawEstimator == WPtr.null) || !((UInt8.toUInt32 (AP_ParamT_unsigned_char_1.op_to_unsigned_char w.EKF3._gsfUseMask) &&& ((1 : UInt32) <<< Int32.toUInt32 (UInt32.toInt32 (UInt8.toUInt32 s.core_index)))) != (0 : UInt32)) then
    return (s, w, o, false)
  if emergency_reset && (decide (UInt32.toInt32 (UInt8.toUInt32 s.EKFGSF_yaw_reset_count) ≥ Int8.toInt32 (AP_ParamT_signed_char_1.op_to_signed_char w.EKF3._gsfResetMaxCount))) then
    return (s, w, o, false)
  let mut yawEKFGSF : Binary64 := (Binary64.ofBits 0x0000000000000000 /- 0.0 -/)  -- uninitialized in C++; assigned before every read
  let mut yawVarianceEKFGSF : Binary64 := (Binary64.ofBits 0x0000000000000000 /- 0.0 -/)  -- uninitialized in C++; assigned before every read
  let (t'1, t'2, t'3) := EKFGSF_getYaw s w yawEKFGSF yawVarianceEKFGSF
  yawEKFGSF := t'1
  yawVarianceEKFGSF := t'2
  if t'3 then
    let mut order : NavEKF3_core.rotationOrder := NavEKF3_core.rotationOrder.TAIT_BRYAN_321  -- uninitialized in C++; assigned before every read
    order := bestRotationOrder s order
    let (t'4, t'5) := resetQuatStateYawOnly s w yawEKFGSF yawVarianceEKFGSF order
    w := t'5
    s := t'4
    s := { s with EKFGSF_yaw_reset_request_ms := Int32.toUInt32 (0 : Int32) }
    s := { s with EKFGSF_yaw_reset_ms := s.imuSampleTime_ms }
    s := { s with EKFGSF_yaw_reset_count := s.EKFGSF_yaw_reset_count + (1 : UInt8) }
    if (s.yaw_source_last == AP_NavEKF_Source.SourceYaw.GSF) || !(use_compass s w) || (UInt32.toInt32 (UInt8.toUInt32 (AP_DAL_Compass.get_num_enabled w.heap'AP_DAL[(WPtr.index w.AP_DAL'_singleton)]!._compass)) == (0 : Int32)) then
      o := o.push (Output.send_text (6 : UInt32) "EKF3 IMU%u yaw aligned using GPS" #[Sum.inl (UInt32.toUInt64 (UInt8.toUInt32 s.imu_index))])
    else
      o := o.push (Output.send_text (4 : UInt32) "EKF3 IMU%u emergency yaw reset" #[Sum.inl (UInt32.toUInt64 (UInt8.toUInt32 s.imu_index))])
    if emergency_reset then
      s := { s with allMagSensorsFailed := true }
    s := recordYawResetsCompleted s
    s := ResetVelocity s w NavEKF3_core.resetDataSource.DEFAULT
    s := ResetPosition s w NavEKF3_core.resetDataSource.DEFAULT
    s := { s with velTestRatio := (Binary64.ofBits 0x0000000000000000 /- 0.0f -/) }
    s := { s with posTestRatio := (Binary64.ofBits 0x0000000000000000 /- 0.0f -/) }
    return (s, w, o, true)
  return (s, w, o, false)

/-- C++ `void NavEKF3_core::realignYawGPS(bool emergency_reset)`, `AP_NavEKF3/AP_NavEKF3_MagFusion.cpp:155-221`. -/
def realignYawGPS (s : State) (w : World) (o : Outputs) (emergency_reset : Bool) : State × World × Outputs := Id.run do
  let mut s := s
  let mut w := w
  let mut o := o
  let mut eulerAngles : Vector3p.State := Vector3p.init_void
  let (t'1, t'2, t'3) := QuaternionT_double.to_euler_double3 ({ q1 := s.statesArray[0]!, q2 := s.statesArray[1]!, q3 := s.statesArray[2]!, q4 := s.statesArray[3]! } : QuaternionT_double.State) eulerAngles.x eulerAngles.y eulerAngles.z
  eulerAngles := { eulerAngles with x := t'1 }
  eulerAngles := { eulerAngles with y := t'2 }
  eulerAngles := { eulerAngles with z := t'3 }
  if Vector2p.length_squared ({ x := s.gpsDataDelayed.vel.x, y := s.gpsDataDelayed.vel.y } : Vector2p.State) > Binary32.toBinary64 (Estimator_lib.sq_float (Binary32.ofBits 0x3f800000 /- 1 -/)) then
    let velYaw : Binary64 := Musl.atan2.atan2 s.statesArray[5]! s.statesArray[4]!
    let gpsCourseYaw : Binary64 := Musl.atan2.atan2 s.gpsDataDelayed.vel.y s.gpsDataDelayed.vel.x
    let yawErr : Binary64 := Estimator_lib.MAX_double2 (Binary64.abs (Estimator_lib.wrap_PI_double (gpsCourseYaw - velYaw))) (Binary64.abs (Estimator_lib.wrap_PI_double (gpsCourseYaw - eulerAngles.z)))
    let badMagYaw : Bool := ((decide (yawErr > (Binary64.ofBits 0x3fe921ff20000000 /- 0.7854f -/))) && (decide (s.velTestRatio > (Binary64.ofBits 0x3ff0000000000000 /- 1.0f -/))) && (UInt32.toInt32 (NavEKF3_core.AidingMode.toInt s.PV_AidingMode) == UInt32.toInt32 (NavEKF3_core.AidingMode.toInt NavEKF3_core.AidingMode.AID_ABSOLUTE))) || !s.yawAlignComplete
    let gpsVelAcc : Binary64 := Binary64.fmax s.gpsSpdAccuracy (AP_ParamT_float_4.op_to_double w.EKF3._gpsHorizVelNoise)
    let gps_yaw_variance : Binary64 := Binary32.toBinary64 (Estimator_lib.sq_float (Musl.asinf.asinf (Estimator_lib.constrain_value_line_float (Binary64.toBinary32 (gpsVelAcc / Vector2p.length ({ x := s.gpsDataDelayed.vel.x, y := s.gpsDataDelayed.vel.y } : Vector2p.State))) (-(Binary32.ofBits 0x3f800000 /- 1 -/)) (Binary32.ofBits 0x3f800000 /- 1 -/) (Int32.toUInt32 (176 : Int32)))))
    if gps_yaw_variance < Binary32.toBinary64 (Estimator_lib.sq_float (Estimator_lib.radians_float (Binary32.ofBits 0x41700000 /- 15 -/))) then
      s := { s with yawAlignGpsValidCount := s.yawAlignGpsValidCount + (1 : UInt8) }
    else
      s := { s with yawAlignGpsValidCount := Int8.toUInt8 (Int32.toInt8 (0 : Int32)) }
    if badMagYaw then
      let useGSF : Bool := !(assume_zero_sideslip w) || (s.yaw_source_last == AP_NavEKF_Source.SourceYaw.GSF)
      let mut t'8 := useGSF
      if t'8 then
        let (t'4, t'5, t'6, t'7) := EKFGSF_resetMainFilterYaw s w o emergency_reset
        w := t'5
        s := t'4
        o := t'6
        t'8 := t'7
      if t'8 then
        return (s, w, o)
      if UInt32.toInt32 (UInt8.toUInt32 s.yawAlignGpsValidCount) ≥ (5 : Int32) then
        s := { s with yawAlignGpsValidCount := Int8.toUInt8 (Int32.toInt8 (0 : Int32)) }
        let mut order : NavEKF3_core.rotationOrder := NavEKF3_core.rotationOrder.TAIT_BRYAN_321  -- uninitialized in C++; assigned before every read
        order := bestRotationOrder s order
        let (t'9, t'10) := resetQuatStateYawOnly s w gpsCourseYaw gps_yaw_variance order
        w := t'10
        s := t'9
        s := ResetVelocity s w NavEKF3_core.resetDataSource.GPS
        s := ResetPosition s w NavEKF3_core.resetDataSource.GPS
        o := o.push (Output.send_text (6 : UInt32) "EKF3 IMU%u yaw aligned to GPS velocity" #[Sum.inl (UInt32.toUInt64 (UInt8.toUInt32 s.imu_index))])
        if use_compass s w then
          s := { s with magStateResetRequest := true }
          s := { s with allMagSensorsFailed := false }
    else if UInt32.toInt32 (UInt8.toUInt32 s.yawAlignGpsValidCount) ≥ (5 : Int32) then
      s := { s with yawAlignGpsValidCount := Int8.toUInt8 (Int32.toInt8 (0 : Int32)) }
      s := recordYawResetsCompleted s
  else
    s := { s with yawAlignGpsValidCount := Int8.toUInt8 (Int32.toInt8 (0 : Int32)) }
  return (s, w, o)

end NavEKF3_core

namespace NavEKF3_core

/-- C++ `void NavEKF3_core::calcFiltBaroOffset()`, `AP_NavEKF3/AP_NavEKF3_Measurements.cpp:812-816`. -/
def calcFiltBaroOffset (s : State) : State := Id.run do
  let mut s := s
  s := { s with baroHgtOffset := s.baroHgtOffset + (Binary64.ofBits 0x3fb99999a0000000 /- 0.1f -/) * Estimator_lib.constrain_value_line_double (s.baroDataDelayed.hgt + s.statesArray[9]! - s.baroHgtOffset) (Binary64.ofBits 0xc014000000000000 /- (double)-5 -/) (Binary64.ofBits 0x4014000000000000 /- (double)5 -/) (Int32.toUInt32 (815 : Int32)) }
  return s

/-- C++ `void NavEKF3_core::correctEkfOriginHeight()`, `AP_NavEKF3/AP_NavEKF3_Measurements.cpp:819-857`. -/
def correctEkfOriginHeight (s : State) : State := Id.run do
  let mut s := s
  let deltaTime : Binary64 := Estimator_lib.constrain_value_line_double (Binary32.toBinary64 ((Binary32.ofBits 0x3a83126f /- 0.00100000005 -/) * UInt32.toBinary32 (s.imuDataDelayed.time_ms - s.lastOriginHgtTime_ms))) (Binary64.ofBits 0x0000000000000000 /- (double)0 -/) (Binary64.ofBits 0x3ff0000000000000 /- (double)1 -/) (Int32.toUInt32 (824 : Int32))
  if s.activeHgtSource == AP_NavEKF_Source.SourceZ.BARO then
    let baroDriftRate : Binary64 := (Binary64.ofBits 0x3fa999999999999a /- 0.05 -/)
    s := { s with ekfOriginHgtVar := s.ekfOriginHgtVar + Estimator_lib.sq_double (baroDriftRate * deltaTime) }
  else if s.activeHgtSource == AP_NavEKF_Source.SourceZ.RANGEFINDER then
    let maxTerrGrad : Binary64 := (Binary64.ofBits 0x3fd0000000000000 /- 0.25 -/)
    s := { s with ekfOriginHgtVar := s.ekfOriginHgtVar + Estimator_lib.sq_double (maxTerrGrad * Vector2p.length ({ x := s.statesArray[4]!, y := s.statesArray[5]! } : Vector2p.State) * deltaTime) }
  else
    return s
  s := { s with lastOriginHgtTime_ms := s.imuDataDelayed.time_ms }
  let originHgtObsVar : Binary64 := Estimator_lib.sq_double s.gpsHgtAccuracy + s.Pmut[225]!
  let gain : Binary64 := s.ekfOriginHgtVar / (s.ekfOriginHgtVar + originHgtObsVar)
  let innovation : Binary64 := -s.statesArray[9]! - s.gpsDataDelayed.hgt
  let ratio : Binary64 := Estimator_lib.sq_double innovation / (s.ekfOriginHgtVar + originHgtObsVar)
  if decide (ratio < (Binary64.ofBits 0x4039000000000000 /- 25.0f -/)) && s.gpsAccuracyGood then
    s := { s with ekfGpsRefHgt := s.ekfGpsRefHgt - (gain * innovation) }
    s := { s with ekfOriginHgtVar := s.ekfOriginHgtVar - Estimator_lib.MAX_double_float (gain * s.ekfOriginHgtVar) (Binary32.ofBits 0x00000000 /- 0.0f -/) }
  return s

/-- C++ `void NavEKF3_core::selectHeightForFusion()`, `AP_NavEKF3/AP_NavEKF3_PosVelFusion.cpp:1223-1464`. -/
def selectHeightForFusion (s : State) (w : World) : State := Id.run do
  let mut s := s
  s := readBaroData s w
  let (t'1, t'2, t'3) := EKF_obs_buffer_t_NavEKF3_core_baro_elements.recall_baro_elements_uint32_t s.storedBaro s.baroDataDelayed s.imuDataDelayed.time_ms
  s := { s with storedBaro := t'1 }
  s := { s with baroDataDelayed := t'2 }
  s := { s with baroDataToFuse := t'3 }
  let rangeFinderDataIsFresh : Bool := (decide (s.imuSampleTime_ms - s.rngValidMeaTime_ms < Int32.toUInt32 (500 : Int32)))
  if (AP_NavEKF_Source.getPosZSource w.EKF3.sources s.core_index == AP_NavEKF_Source.SourceZ.NONE) then
    s := { s with activeHgtSource := AP_NavEKF_Source.SourceZ.NONE }
  else if AP_NavEKF_Source.getPosZSource w.EKF3.sources s.core_index == AP_NavEKF_Source.SourceZ.BARO then
    s := { s with activeHgtSource := AP_NavEKF_Source.SourceZ.BARO }
  else if (AP_NavEKF_Source.getPosZSource w.EKF3.sources s.core_index == AP_NavEKF_Source.SourceZ.GPS) && (decide ((s.imuSampleTime_ms - s.lastTimeGpsReceived_ms) < Int32.toUInt32 (500 : Int32))) && s.validOrigin && s.gpsAccuracyGood then
    s := { s with activeHgtSource := AP_NavEKF_Source.SourceZ.GPS }
  let lostRngHgt : Bool := ((s.activeHgtSource == AP_NavEKF_Source.SourceZ.RANGEFINDER) && !rangeFinderDataIsFresh)
  let lostGpsHgt : Bool := ((s.activeHgtSource == AP_NavEKF_Source.SourceZ.GPS) && (decide ((s.imuSampleTime_ms - s.lastTimeGpsReceived_ms) > Int32.toUInt32 (2000 : Int32)) || !s.gpsAccuracyGoodForAltitude))
  let fallback_to_baro : Bool := lostRngHgt || lostGpsHgt
  if fallback_to_baro then
    s := { s with activeHgtSource := AP_NavEKF_Source.SourceZ.BARO }
  let baroInGndEffect : Bool := (AP_DAL.get_takeoff_expected w.heap'AP_DAL[(WPtr.index w.AP_DAL'_singleton)]! || AP_DAL.get_touchdown_expected w.heap'AP_DAL[(WPtr.index w.AP_DAL'_singleton)]!) && !(assume_zero_sideslip w)
  if s.baroDataToFuse then
    if s.activeHgtSource != AP_NavEKF_Source.SourceZ.BARO && !baroInGndEffect then
      s := calcFiltBaroOffset s
    if !(AP_DAL.get_takeoff_expected w.heap'AP_DAL[(WPtr.index w.AP_DAL'_singleton)]!) then
      let gndHgtFiltTC : Binary64 := (Binary64.ofBits 0x3fe0000000000000 /- 0.5 -/)
      let dtBaro : Binary64 := Binary32.toBinary64 (Int32.toBinary32 (UInt32.toInt32 (UInt16.toUInt32 w.EKF3.hgtAvg_ms)) * (Binary32.ofBits 0x3a83126f /- 1.0e-3 -/))
      let alpha : Binary64 := Estimator_lib.constrain_value_line_double (dtBaro / (dtBaro + gndHgtFiltTC)) (Binary64.ofBits 0x0000000000000000 /- (double)0 -/) (Binary64.ofBits 0x3ff0000000000000 /- (double)1 -/) (Int32.toUInt32 (1353 : Int32))
      s := { s with meaHgtAtTakeOff := s.meaHgtAtTakeOff + (s.baroDataDelayed.hgt - s.meaHgtAtTakeOff) * alpha }
  if s.gpsDataToFuse && (((UInt32.toInt32 (UInt8.toUInt32 (AP_ParamT_unsigned_char_1.op_to_unsigned_char w.EKF3._originHgtMode)) &&& ((1 : Int32) <<< (0 : Int32))) != (0 : Int32) && (s.activeHgtSource == AP_NavEKF_Source.SourceZ.BARO)) || ((UInt32.toInt32 (UInt8.toUInt32 (AP_ParamT_unsigned_char_1.op_to_unsigned_char w.EKF3._originHgtMode)) &&& ((1 : Int32) <<< (1 : Int32))) != (0 : Int32) && (s.activeHgtSource == AP_NavEKF_Source.SourceZ.RANGEFINDER))) then
    s := correctEkfOriginHeight s
  if s.rangeDataToFuse && (s.activeHgtSource == AP_NavEKF_Source.SourceZ.RANGEFINDER) then
    if s.prevTnb.c.z ≥ (Binary64.ofBits 0x3fe6666666666666 /- 0.7 -/) then
      s := { s with hgtMea := Estimator_lib.MAX_double2 (s.rangeDataDelayed.rng * s.prevTnb.c.z) s.rngOnGnd }
      s := { s with hgtMea := s.hgtMea - s.terrainState }
      if UInt32.toInt32 (UInt8.toUInt32 (AP_ParamT_unsigned_char_1.op_to_unsigned_char w.EKF3._originHgtMode)) &&& ((1 : Int32) <<< (1 : Int32)) != (0 : Int32) && UInt32.toInt32 (UInt8.toUInt32 (AP_ParamT_unsigned_char_1.op_to_unsigned_char w.EKF3._originHgtMode)) &&& ((1 : Int32) <<< (2 : Int32)) != (0 : Int32) then
        s := { s with hgtMea := s.hgtMea + Binary32.toBinary64 (Binary64.toBinary32 (s.ekfGpsRefHgt - (Binary64.ofBits 0x3f847ae147ae147b /- 0.01 -/) * Int32.toBinary64 s.EKF_origin.alt)) }
      s := { s with velPosObs := s.velPosObs.set! 5 (-s.hgtMea) }
      s := { s with fuseHgtData := true }
      s := { s with posDownObsNoise := Estimator_lib.sq_double (Estimator_lib.constrain_value_line_double (AP_ParamT_float_4.op_to_double w.EKF3._rngNoise) (Binary64.ofBits 0x3fb99999a0000000 /- (double)13421773/134217728 -/) (Binary64.ofBits 0x4024000000000000 /- (double)10 -/) (Int32.toUInt32 (1394 : Int32))) }
      s := { s with posDownObsNoise := s.posDownObsNoise + Estimator_lib.sq_double (s.rangeDataDelayed.rng * Binary32.toBinary64 (AP_ParamT_float_4.op_to_float w.EKF3._terrGradMax)) * Estimator_lib.MAX_float_double (Binary32.ofBits 0x00000000 /- 0.0f -/) ((Binary64.ofBits 0x3ff0000000000000 /- 1.0f -/) - Estimator_lib.sq_double s.prevTnb.c.z) }
    else
      s := { s with fuseHgtData := false }
  else if s.gpsDataToFuse && (s.activeHgtSource == AP_NavEKF_Source.SourceZ.GPS) then
    s := { s with hgtMea := s.gpsDataDelayed.hgt }
    s := { s with velPosObs := s.velPosObs.set! 5 (-s.hgtMea) }
    s := { s with fuseHgtData := true }
    if s.gpsHgtAccuracy > (Binary64.ofBits 0x0000000000000000 /- 0.0f -/) then
      s := { s with posDownObsNoise := Estimator_lib.sq_double (Estimator_lib.constrain_value_line_double s.gpsHgtAccuracy (Binary32.toBinary64 ((Binary32.ofBits 0x3fc00000 /- 1.5 -/) * AP_ParamT_float_4.op_to_float w.EKF3._gpsHorizPosNoise)) (Binary64.ofBits 0x4059000000000000 /- (double)100 -/) (Int32.toUInt32 (1409 : Int32))) }
    else
      s := { s with posDownObsNoise := Estimator_lib.sq_double (Estimator_lib.constrain_value_line_double (Binary32.toBinary64 ((Binary32.ofBits 0x3fc00000 /- 1.5 -/) * AP_ParamT_float_4.op_to_float w.EKF3._gpsHorizPosNoise)) (Binary64.ofBits 0x3fb99999a0000000 /- (double)13421773/134217728 -/) (Binary64.ofBits 0x4024000000000000 /- (double)10 -/) (Int32.toUInt32 (1411 : Int32))) }
  else if s.baroDataToFuse && (s.activeHgtSource == AP_NavEKF_Source.SourceZ.BARO) then
    s := { s with hgtMea := s.baroDataDelayed.hgt - s.baroHgtOffset }
    if UInt32.toInt32 (UInt8.toUInt32 (AP_ParamT_unsigned_char_1.op_to_unsigned_char w.EKF3._originHgtMode)) &&& ((1 : Int32) <<< (0 : Int32)) != (0 : Int32) && UInt32.toInt32 (UInt8.toUInt32 (AP_ParamT_unsigned_char_1.op_to_unsigned_char w.EKF3._originHgtMode)) &&& ((1 : Int32) <<< (2 : Int32)) != (0 : Int32) then
      s := { s with hgtMea := s.hgtMea + Binary32.toBinary64 (Binary64.toBinary32 (s.ekfGpsRefHgt - (Binary64.ofBits 0x3f847ae147ae147b /- 0.01 -/) * Int32.toBinary64 s.EKF_origin.alt)) }
    s := { s with fuseHgtData := true }
    s := { s with posDownObsNoise := Estimator_lib.sq_double (Estimator_lib.constrain_value_line_double (AP_ParamT_float_4.op_to_double w.EKF3._baroAltNoise) (Binary64.ofBits 0x3f847ae140000000 /- (double)5368709/536870912 -/) (Binary64.ofBits 0x4059000000000000 /- (double)100 -/) (Int32.toUInt32 (1423 : Int32))) }
    if AP_DAL.get_takeoff_expected w.heap'AP_DAL[(WPtr.index w.AP_DAL'_singleton)]! || AP_DAL.get_touchdown_expected w.heap'AP_DAL[(WPtr.index w.AP_DAL'_singleton)]! then
      s := { s with posDownObsNoise := s.posDownObsNoise * Binary32.toBinary64 w.EKF3.gndEffectBaroScaler }
    s := { s with velPosObs := s.velPosObs.set! 5 (-s.hgtMea) }
  else if (s.activeHgtSource == AP_NavEKF_Source.SourceZ.NONE && decide (s.imuSampleTime_ms - s.lastHgtPassTime_ms > Int32.toUInt32 (70 : Int32))) then
    s := { s with hgtMea := (Binary64.ofBits 0x0000000000000000 /- 0.0f -/) }
    s := { s with fuseHgtData := true }
    s := { s with velPosObs := s.velPosObs.set! 5 (-s.hgtMea) }
    if s.onGround then
      s := { s with posDownObsNoise := Binary32.toBinary64 (Estimator_lib.sq_float (Binary32.ofBits 0x40000000 /- 2.0f -/)) }
    else
      s := { s with posDownObsNoise := Estimator_lib.sq_double (Estimator_lib.constrain_value_line_double (AP_ParamT_float_4.op_to_double w.EKF3._baroAltNoise) (Binary64.ofBits 0x4000000000000000 /- (double)2 -/) (Binary64.ofBits 0x4059000000000000 /- (double)100 -/) (Int32.toUInt32 (1439 : Int32))) }
  else
    s := { s with fuseHgtData := false }
  if (s.activeHgtSource != s.prevHgtSource) && s.fuseHgtData then
    s := { s with prevHgtSource := s.activeHgtSource }
    if s.activeHgtSource != AP_NavEKF_Source.SourceZ.BARO || !baroInGndEffect then
      s := ResetPositionD s (-s.hgtMea)
  s := { s with hgtRetryTime_ms := if ((s.useGpsVertVel || s.extNav.useVel) && !s.velTimeout) then w.EKF3.hgtRetryTimeMode0_ms else w.EKF3.hgtRetryTimeMode12_ms }
  if decide (s.imuSampleTime_ms - s.lastHgtPassTime_ms > UInt16.toUInt32 s.hgtRetryTime_ms) || (s.badIMUdata && (decide (s.imuSampleTime_ms - s.goodIMUdata_ms > Int32.toUInt32 (1000 : Int32)))) then
    s := { s with hgtTimeout := true }
  else
    s := { s with hgtTimeout := false }
  return s

/-- C++ `void NavEKF3_core::ResetPositionNE(ftype posN, ftype posE)`, `AP_NavEKF3/AP_NavEKF3_PosVelFusion.cpp:220-244`. -/
def ResetPositionNE (s : State) (posN : Binary64) (posE : Binary64) : State := Id.run do
  let mut s := s
  let posOrig : Vector3p.State := ({ x := s.statesArray[7]!, y := s.statesArray[8]!, z := s.statesArray[9]! } : Vector3p.State)
  s := { s with statesArray := s.statesArray.set! 7 posN }
  s := { s with statesArray := s.statesArray.set! 8 posE }
  s := { s with posResetNE.x := s.statesArray[7]! - posOrig.x }
  s := { s with posResetNE.y := s.statesArray[8]! - posOrig.y }
  let t'1 : UInt8 := Int8.toUInt8 (Int32.toInt8 (0 : Int32))
  let t'2 : Int32 := UInt32.toInt32 (UInt8.toUInt32 s.imu_buffer_length)
  for i' in [0:(t'2.toInt - (Int.ofNat t'1.toNat)).toNat] do  -- C++ loop bounded by a runtime value (--runtime-loops)
    let i : UInt8 := t'1 + Nat.toUInt8 i'
    s := { s with storedOutput.buffer := s.storedOutput.buffer.set! (UInt8.toNat (UInt32.toUInt8 (UInt8.toUInt32 i))) ({ s.storedOutput.buffer[UInt8.toNat (UInt32.toUInt8 (UInt8.toUInt32 i))]! with position.x := s.storedOutput.buffer[UInt8.toNat (UInt32.toUInt8 (UInt8.toUInt32 i))]!.position.x + s.posResetNE.x }) }
    s := { s with storedOutput.buffer := s.storedOutput.buffer.set! (UInt8.toNat (UInt32.toUInt8 (UInt8.toUInt32 i))) ({ s.storedOutput.buffer[UInt8.toNat (UInt32.toUInt8 (UInt8.toUInt32 i))]! with position.y := s.storedOutput.buffer[UInt8.toNat (UInt32.toUInt8 (UInt8.toUInt32 i))]!.position.y + s.posResetNE.y }) }
  s := { s with outputDataNew.position.x := s.outputDataNew.position.x + s.posResetNE.x }
  s := { s with outputDataNew.position.y := s.outputDataNew.position.y + s.posResetNE.y }
  s := { s with outputDataDelayed.position.x := s.outputDataDelayed.position.x + s.posResetNE.x }
  s := { s with outputDataDelayed.position.y := s.outputDataDelayed.position.y + s.posResetNE.y }
  s := { s with posNEResetCount := s.posNEResetCount + (1 : UInt16) }
  return s

end NavEKF3_core

namespace NavEKF3_core

/-- C++ `void NavEKF3_core::runYawEstimatorCorrection()`, `AP_NavEKF3/AP_NavEKF3_Control.cpp:858-895`. -/
def runYawEstimatorCorrection (s : State) (w : World) (o : Outputs) : State × World × Outputs := Id.run do
  let mut s := s
  let mut w := w
  let mut o := o
  if s.yawEstimator == WPtr.null then
    return (s, w, o)
  if AP_NavEKF_Source.getPosXYSource w.EKF3.sources s.core_index != AP_NavEKF_Source.SourceXY.GPS || !(AP_NavEKF_Source.useVelXYSource w.EKF3.sources AP_NavEKF_Source.SourceXY.GPS s.core_index) then
    return (s, w, o)
  if s.EKFGSF_run_filterbank then
    if s.gpsDataToFuse then
      let gpsVelNE : Vector2p.State := Vector2p.init_double2 s.gpsDataDelayed.vel.x s.gpsDataDelayed.vel.y
      let gpsVelAcc : Binary64 := Binary64.fmax s.gpsSpdAccuracy (AP_ParamT_float_4.op_to_double w.EKF3._gpsHorizVelNoise)
      let t'1 := w.heap'EKFGSF_yaw[(WPtr.index s.yawEstimator)]!  -- the object out of its slot for the call (--swap-out)
      w := { w with heap'EKFGSF_yaw := w.heap'EKFGSF_yaw.set! (WPtr.index s.yawEstimator) default }
      w := { w with heap'EKFGSF_yaw := w.heap'EKFGSF_yaw.set! (WPtr.index s.yawEstimator) (EKFGSF_yaw.fuseVelData t'1 gpsVelNE gpsVelAcc) }
      let mut gsfYaw : Binary64 := (Binary64.ofBits 0x0000000000000000 /- 0.0 -/)  -- uninitialized in C++; assigned before every read
      let mut gsfYawVariance : Binary64 := (Binary64.ofBits 0x0000000000000000 /- 0.0 -/)  -- uninitialized in C++; assigned before every read
      let (t'2, t'3, t'4) := EKFGSF_getYaw s w gsfYaw gsfYawVariance
      gsfYaw := t'2
      gsfYawVariance := t'3
      if t'4 then
        if UInt32.toInt32 (UInt8.toUInt32 s.EKFGSF_yaw_valid_count) < (5 : Int32) then
          s := { s with EKFGSF_yaw_valid_count := s.EKFGSF_yaw_valid_count + (1 : UInt8) }
      else
        s := { s with EKFGSF_yaw_valid_count := Int8.toUInt8 (Int32.toInt8 (0 : Int32)) }
    if decide (s.EKFGSF_yaw_reset_request_ms > Int32.toUInt32 (0 : Int32)) && decide (s.imuSampleTime_ms - s.EKFGSF_yaw_reset_request_ms < Int32.toUInt32 (5000 : Int32)) then
      let (t'5, t'6, t'7, _) := EKFGSF_resetMainFilterYaw s w o true
      w := t'6
      s := t'5
      o := t'7
  else
    s := { s with EKFGSF_yaw_valid_count := Int8.toUInt8 (Int32.toInt8 (0 : Int32)) }
  return (s, w, o)

end NavEKF3_core

namespace NavEKF3_core

/-- C++ `void NavEKF3_core::FuseBodyVel()`, `AP_NavEKF3/AP_NavEKF3_PosVelFusion.cpp:1505-2074`. -/
def FuseBodyVel (s : State) (w : World) (o : Outputs) : State × World × Outputs := Id.run do
  let mut s := s
  let mut w := w
  let mut o := o
  let mut H_VEL : Array Binary64 := Array.replicate 24 (Binary64.ofBits 0x0000000000000000 /- 0.0 -/)  -- uninitialized in C; every element is written before it is read
  let mut bodyVelPred : Vector3p.State := Vector3p.init_void
  let q0 : Binary64 := s.statesArray[0]!
  let q1 : Binary64 := s.statesArray[1]!
  let q2 : Binary64 := s.statesArray[2]!
  let q3 : Binary64 := s.statesArray[3]!
  let vn : Binary64 := s.statesArray[4]!
  let ve : Binary64 := s.statesArray[5]!
  let vd : Binary64 := s.statesArray[6]!
  for obsIndex' in [0:3] do
    let obsIndex : UInt8 := Nat.toUInt8 obsIndex'
    bodyVelPred := (Matrix3_double.op_mul_Vector3p s.prevTnb ({ x := s.statesArray[4]!, y := s.statesArray[5]!, z := s.statesArray[6]! } : Vector3p.State))
    let posOffsetBody : Vector3p.State := Vector3p.op_sub_Vector3p s.bodyOdm.dataDelayed.body_offset s.accelPosOffset
    if s.imuDataDelayed.delAngDT > (Binary64.ofBits 0x3f50624de0000000 /- 0.001f -/) then
      let (t'1, _) := Vector3p.op_add_assign bodyVelPred (Vector3p.op_mod (Vector3p.op_mul_double s.imuDataDelayed.delAng ((Binary64.ofBits 0x3ff0000000000000 /- 1.0f -/) / s.imuDataDelayed.delAngDT)) posOffsetBody)
      bodyVelPred := t'1
    if UInt32.toInt32 (UInt8.toUInt32 obsIndex) == (0 : Int32) then
      H_VEL := H_VEL.set! 0 (q2 * vd * (Binary64.ofBits 0xc000000000000000 /- -2.0f -/) + q3 * ve * (Binary64.ofBits 0x4000000000000000 /- 2.0f -/) + q0 * vn * (Binary64.ofBits 0x4000000000000000 /- 2.0f -/))
      H_VEL := H_VEL.set! 1 (q3 * vd * (Binary64.ofBits 0x4000000000000000 /- 2.0f -/) + q2 * ve * (Binary64.ofBits 0x4000000000000000 /- 2.0f -/) + q1 * vn * (Binary64.ofBits 0x4000000000000000 /- 2.0f -/))
      H_VEL := H_VEL.set! 2 (q0 * vd * (Binary64.ofBits 0xc000000000000000 /- -2.0f -/) + q1 * ve * (Binary64.ofBits 0x4000000000000000 /- 2.0f -/) - q2 * vn * (Binary64.ofBits 0x4000000000000000 /- 2.0f -/))
      H_VEL := H_VEL.set! 3 (q1 * vd * (Binary64.ofBits 0x4000000000000000 /- 2.0f -/) + q0 * ve * (Binary64.ofBits 0x4000000000000000 /- 2.0f -/) - q3 * vn * (Binary64.ofBits 0x4000000000000000 /- 2.0f -/))
      H_VEL := H_VEL.set! 4 (q0 * q0 + q1 * q1 - q2 * q2 - q3 * q3)
      H_VEL := H_VEL.set! 5 (q0 * q3 * (Binary64.ofBits 0x4000000000000000 /- 2.0f -/) + q1 * q2 * (Binary64.ofBits 0x4000000000000000 /- 2.0f -/))
      H_VEL := H_VEL.set! 6 (q0 * q2 * (Binary64.ofBits 0xc000000000000000 /- -2.0f -/) + q1 * q3 * (Binary64.ofBits 0x4000000000000000 /- 2.0f -/))
      for index' in [7:24] do
        let index : UInt8 := Nat.toUInt8 index'
        H_VEL := H_VEL.set! (UInt8.toNat index) (Binary64.ofBits 0x0000000000000000 /- 0.0f -/)
      let R_VEL : Binary64 := Estimator_lib.sq_double s.bodyOdm.dataDelayed.velErr
      let t2 : Binary64 := q0 * q3 * (Binary64.ofBits 0x4000000000000000 /- 2.0f -/)
      let t3 : Binary64 := q1 * q2 * (Binary64.ofBits 0x4000000000000000 /- 2.0f -/)
      let t4 : Binary64 := t2 + t3
      let t5 : Binary64 := q0 * q0
      let t6 : Binary64 := q1 * q1
      let t7 : Binary64 := q2 * q2
      let t8 : Binary64 := q3 * q3
      let t9 : Binary64 := t5 + t6 - t7 - t8
      let t10 : Binary64 := q0 * q2 * (Binary64.ofBits 0x4000000000000000 /- 2.0f -/)
      let t25 : Binary64 := q1 * q3 * (Binary64.ofBits 0x4000000000000000 /- 2.0f -/)
      let t11 : Binary64 := t10 - t25
      let t12 : Binary64 := q3 * ve * (Binary64.ofBits 0x4000000000000000 /- 2.0f -/)
      let t13 : Binary64 := q0 * vn * (Binary64.ofBits 0x4000000000000000 /- 2.0f -/)
      let t26 : Binary64 := q2 * vd * (Binary64.ofBits 0x4000000000000000 /- 2.0f -/)
      let t14 : Binary64 := t12 + t13 - t26
      let t15 : Binary64 := q3 * vd * (Binary64.ofBits 0x4000000000000000 /- 2.0f -/)
      let t16 : Binary64 := q2 * ve * (Binary64.ofBits 0x4000000000000000 /- 2.0f -/)
      let t17 : Binary64 := q1 * vn * (Binary64.ofBits 0x4000000000000000 /- 2.0f -/)
      let t18 : Binary64 := t15 + t16 + t17
      let t19 : Binary64 := q0 * vd * (Binary64.ofBits 0x4000000000000000 /- 2.0f -/)
      let t20 : Binary64 := q2 * vn * (Binary64.ofBits 0x4000000000000000 /- 2.0f -/)
      let t27 : Binary64 := q1 * ve * (Binary64.ofBits 0x4000000000000000 /- 2.0f -/)
      let t21 : Binary64 := t19 + t20 - t27
      let t22 : Binary64 := q1 * vd * (Binary64.ofBits 0x4000000000000000 /- 2.0f -/)
      let t23 : Binary64 := q0 * ve * (Binary64.ofBits 0x4000000000000000 /- 2.0f -/)
      let t28 : Binary64 := q3 * vn * (Binary64.ofBits 0x4000000000000000 /- 2.0f -/)
      let t24 : Binary64 := t22 + t23 - t28
      let t29 : Binary64 := s.Pmut[0]! * t14
      let t30 : Binary64 := s.Pmut[25]! * t18
      let t31 : Binary64 := s.Pmut[101]! * t9
      let t32 : Binary64 := s.Pmut[125]! * t4
      let t33 : Binary64 := s.Pmut[5]! * t14
      let t34 : Binary64 := s.Pmut[29]! * t18
      let t35 : Binary64 := s.Pmut[77]! * t24
      let t79 : Binary64 := s.Pmut[149]! * t11
      let t80 : Binary64 := s.Pmut[53]! * t21
      let t36 : Binary64 := t31 + t32 + t33 + t34 + t35 - t79 - t80
      let t37 : Binary64 := t4 * t36
      let t38 : Binary64 := s.Pmut[102]! * t9
      let t39 : Binary64 := s.Pmut[126]! * t4
      let t40 : Binary64 := s.Pmut[6]! * t14
      let t41 : Binary64 := s.Pmut[30]! * t18
      let t42 : Binary64 := s.Pmut[78]! * t24
      let t81 : Binary64 := s.Pmut[150]! * t11
      let t82 : Binary64 := s.Pmut[54]! * t21
      let t43 : Binary64 := t38 + t39 + t40 + t41 + t42 - t81 - t82
      let t44 : Binary64 := s.Pmut[96]! * t9
      let t45 : Binary64 := s.Pmut[120]! * t4
      let t46 : Binary64 := s.Pmut[24]! * t18
      let t47 : Binary64 := s.Pmut[72]! * t24
      let t84 : Binary64 := s.Pmut[144]! * t11
      let t85 : Binary64 := s.Pmut[48]! * t21
      let t48 : Binary64 := t29 + t44 + t45 + t46 + t47 - t84 - t85
      let t49 : Binary64 := t14 * t48
      let t50 : Binary64 := s.Pmut[97]! * t9
      let t51 : Binary64 := s.Pmut[121]! * t4
      let t52 : Binary64 := s.Pmut[1]! * t14
      let t53 : Binary64 := s.Pmut[73]! * t24
      let t86 : Binary64 := s.Pmut[145]! * t11
      let t87 : Binary64 := s.Pmut[49]! * t21
      let t54 : Binary64 := t30 + t50 + t51 + t52 + t53 - t86 - t87
      let t55 : Binary64 := t18 * t54
      let t56 : Binary64 := s.Pmut[98]! * t9
      let t57 : Binary64 := s.Pmut[122]! * t4
      let t58 : Binary64 := s.Pmut[2]! * t14
      let t59 : Binary64 := s.Pmut[26]! * t18
      let t60 : Binary64 := s.Pmut[74]! * t24
      let t78 : Binary64 := s.Pmut[50]! * t21
      let t88 : Binary64 := s.Pmut[146]! * t11
      let t61 : Binary64 := t56 + t57 + t58 + t59 + t60 - t78 - t88
      let t62 : Binary64 := s.Pmut[99]! * t9
      let t63 : Binary64 := s.Pmut[123]! * t4
      let t64 : Binary64 := s.Pmut[3]! * t14
      let t65 : Binary64 := s.Pmut[27]! * t18
      let t66 : Binary64 := s.Pmut[75]! * t24
      let t90 : Binary64 := s.Pmut[147]! * t11
      let t91 : Binary64 := s.Pmut[51]! * t21
      let t67 : Binary64 := t62 + t63 + t64 + t65 + t66 - t90 - t91
      let t68 : Binary64 := t24 * t67
      let t69 : Binary64 := s.Pmut[100]! * t9
      let t70 : Binary64 := s.Pmut[124]! * t4
      let t71 : Binary64 := s.Pmut[4]! * t14
      let t72 : Binary64 := s.Pmut[28]! * t18
      let t73 : Binary64 := s.Pmut[76]! * t24
      let t92 : Binary64 := s.Pmut[148]! * t11
      let t93 : Binary64 := s.Pmut[52]! * t21
      let t74 : Binary64 := t69 + t70 + t71 + t72 + t73 - t92 - t93
      let t75 : Binary64 := t9 * t74
      let t83 : Binary64 := t11 * t43
      let t89 : Binary64 := t21 * t61
      let mut t76 : Binary64 := R_VEL + t37 + t49 + t55 + t68 + t75 - t83 - t89
      let mut t77 : Binary64 := (Binary64.ofBits 0x0000000000000000 /- 0.0 -/)  -- uninitialized in C++; assigned before every read
      if t76 > R_VEL then
        t77 := (Binary64.ofBits 0x3ff0000000000000 /- 1.0f -/) / t76
        s := { s with faultStatus.bad_xvel := false }
      else
        t76 := R_VEL
        t77 := (Binary64.ofBits 0x3ff0000000000000 /- 1.0f -/) / R_VEL
        s := { s with faultStatus.bad_xvel := true }
        return (s, w, o)
      s := { s with bodyOdm.varInnov := s.bodyOdm.varInnov.set! 0 t76 }
      s := { s with bodyOdm.innov := s.bodyOdm.innov.set! 0 (bodyVelPred.x - s.bodyOdm.dataDelayed.vel.x) }
      w := { w with NavEKF_core_common'Kfusion := w.NavEKF_core_common'Kfusion.set! 0 (t77 * (t29 + s.Pmut[5]! * t4 + s.Pmut[4]! * t9 - s.Pmut[6]! * t11 + s.Pmut[1]! * t18 - s.Pmut[2]! * t21 + s.Pmut[3]! * t24)) }
      w := { w with NavEKF_core_common'Kfusion := w.NavEKF_core_common'Kfusion.set! 1 (t77 * (t30 + s.Pmut[29]! * t4 + s.Pmut[28]! * t9 + s.Pmut[24]! * t14 - s.Pmut[30]! * t11 - s.Pmut[26]! * t21 + s.Pmut[27]! * t24)) }
      w := { w with NavEKF_core_common'Kfusion := w.NavEKF_core_common'Kfusion.set! 2 (t77 * (-t78 + s.Pmut[53]! * t4 + s.Pmut[52]! * t9 + s.Pmut[48]! * t14 - s.Pmut[54]! * t11 + s.Pmut[49]! * t18 + s.Pmut[51]! * t24)) }
      w := { w with NavEKF_core_common'Kfusion := w.NavEKF_core_common'Kfusion.set! 3 (t77 * (t66 + s.Pmut[77]! * t4 + s.Pmut[76]! * t9 + s.Pmut[72]! * t14 - s.Pmut[78]! * t11 + s.Pmut[73]! * t18 - s.Pmut[74]! * t21)) }
      w := { w with NavEKF_core_common'Kfusion := w.NavEKF_core_common'Kfusion.set! 4 (t77 * (t69 + s.Pmut[101]! * t4 + s.Pmut[96]! * t14 - s.Pmut[102]! * t11 + s.Pmut[97]! * t18 - s.Pmut[98]! * t21 + s.Pmut[99]! * t24)) }
      w := { w with NavEKF_core_common'Kfusion := w.NavEKF_core_common'Kfusion.set! 5 (t77 * (t32 + s.Pmut[124]! * t9 + s.Pmut[120]! * t14 - s.Pmut[126]! * t11 + s.Pmut[121]! * t18 - s.Pmut[122]! * t21 + s.Pmut[123]! * t24)) }
      w := { w with NavEKF_core_common'Kfusion := w.NavEKF_core_common'Kfusion.set! 6 (t77 * (-t81 + s.Pmut[149]! * t4 + s.Pmut[148]! * t9 + s.Pmut[144]! * t14 + s.Pmut[145]! * t18 - s.Pmut[146]! * t21 + s.Pmut[147]! * t24)) }
      let mut kalman_mask : UInt32 := Int32.toUInt32 (((1 : Int32) <<< (7 : Int32)) ||| ((1 : Int32) <<< (8 : Int32)) ||| ((1 : Int32) <<< (9 : Int32)))
      if !s.inhibitDelAngBiasStates then
        kalman_mask := kalman_mask ||| Int32.toUInt32 (((1 : Int32) <<< (10 : Int32)) ||| ((1 : Int32) <<< (11 : Int32)) ||| ((1 : Int32) <<< (12 : Int32)))
      if !s.inhibitDelVelBiasStates && !s.badIMUdata then
        for index'2' in [0:3] do
          let index'2 : UInt8 := Nat.toUInt8 index'2'
          let stateIndex : UInt8 := Int8.toUInt8 (Int32.toInt8 (UInt32.toInt32 (UInt8.toUInt32 index'2) + (13 : Int32)))
          if !s.dvelBiasAxisInhibit[UInt8.toNat index'2]! then
            kalman_mask := kalman_mask ||| Int32.toUInt32 ((1 : Int32) <<< UInt32.toInt32 (UInt8.toUInt32 stateIndex))
      if !s.inhibitMagStates then
        kalman_mask := kalman_mask ||| Int32.toUInt32 (((1 : Int32) <<< (16 : Int32)) ||| ((1 : Int32) <<< (17 : Int32)) ||| ((1 : Int32) <<< (18 : Int32)) ||| ((1 : Int32) <<< (19 : Int32)) ||| ((1 : Int32) <<< (20 : Int32)) ||| ((1 : Int32) <<< (21 : Int32)))
      if !s.inhibitWindStates && !s.treatWindStatesAsTruth then
        kalman_mask := kalman_mask ||| Int32.toUInt32 (((1 : Int32) <<< (22 : Int32)) ||| ((1 : Int32) <<< (23 : Int32)))
      for i' in [7:24] do
        let i : Int32 := Nat.toInt32 i'
        let mut res : Binary64 := (Binary64.ofBits 0x0000000000000000 /- 0 -/)
        if kalman_mask &&& Int32.toUInt32 ((1 : Int32) <<< i) != (0 : UInt32) then
          res := t77 * (s.Pmut[Int32.toNatClampNeg i * 24 + 5]! * t4 + s.Pmut[Int32.toNatClampNeg i * 24 + 4]! * t9 + s.Pmut[Int32.toNatClampNeg i * 24]! * t14 - s.Pmut[Int32.toNatClampNeg i * 24 + 6]! * t11 + s.Pmut[Int32.toNatClampNeg i * 24 + 1]! * t18 - s.Pmut[Int32.toNatClampNeg i * 24 + 2]! * t21 + s.Pmut[Int32.toNatClampNeg i * 24 + 3]! * t24)
        w := { w with NavEKF_core_common'Kfusion := w.NavEKF_core_common'Kfusion.set! (Int32.toNatClampNeg i) res }
    else if UInt32.toInt32 (UInt8.toUInt32 obsIndex) == (1 : Int32) then
      H_VEL := H_VEL.set! 0 (q1 * vd * (Binary64.ofBits 0x4000000000000000 /- 2.0f -/) + q0 * ve * (Binary64.ofBits 0x4000000000000000 /- 2.0f -/) - q3 * vn * (Binary64.ofBits 0x4000000000000000 /- 2.0f -/))
      H_VEL := H_VEL.set! 1 (q0 * vd * (Binary64.ofBits 0x4000000000000000 /- 2.0f -/) - q1 * ve * (Binary64.ofBits 0x4000000000000000 /- 2.0f -/) + q2 * vn * (Binary64.ofBits 0x4000000000000000 /- 2.0f -/))
      H_VEL := H_VEL.set! 2 (q3 * vd * (Binary64.ofBits 0x4000000000000000 /- 2.0f -/) + q2 * ve * (Binary64.ofBits 0x4000000000000000 /- 2.0f -/) + q1 * vn * (Binary64.ofBits 0x4000000000000000 /- 2.0f -/))
      H_VEL := H_VEL.set! 3 (q2 * vd * (Binary64.ofBits 0x4000000000000000 /- 2.0f -/) - q3 * ve * (Binary64.ofBits 0x4000000000000000 /- 2.0f -/) - q0 * vn * (Binary64.ofBits 0x4000000000000000 /- 2.0f -/))
      H_VEL := H_VEL.set! 4 (q0 * q3 * (Binary64.ofBits 0xc000000000000000 /- -2.0f -/) + q1 * q2 * (Binary64.ofBits 0x4000000000000000 /- 2.0f -/))
      H_VEL := H_VEL.set! 5 (q0 * q0 - q1 * q1 + q2 * q2 - q3 * q3)
      H_VEL := H_VEL.set! 6 (q0 * q1 * (Binary64.ofBits 0x4000000000000000 /- 2.0f -/) + q2 * q3 * (Binary64.ofBits 0x4000000000000000 /- 2.0f -/))
      for index'3' in [7:24] do
        let index'3 : UInt8 := Nat.toUInt8 index'3'
        H_VEL := H_VEL.set! (UInt8.toNat index'3) (Binary64.ofBits 0x0000000000000000 /- 0.0f -/)
      let R_VEL'2 : Binary64 := Estimator_lib.sq_double s.bodyOdm.dataDelayed.velErr
      let t2'2 : Binary64 := q0 * q3 * (Binary64.ofBits 0x4000000000000000 /- 2.0f -/)
      let t9'2 : Binary64 := q1 * q2 * (Binary64.ofBits 0x4000000000000000 /- 2.0f -/)
      let t3'2 : Binary64 := t2'2 - t9'2
      let t4'2 : Binary64 := q0 * q0
      let t5'2 : Binary64 := q1 * q1
      let t6'2 : Binary64 := q2 * q2
      let t7'2 : Binary64 := q3 * q3
      let t8'2 : Binary64 := t4'2 - t5'2 + t6'2 - t7'2
      let t10'2 : Binary64 := q0 * q1 * (Binary64.ofBits 0x4000000000000000 /- 2.0f -/)
      let t11'2 : Binary64 := q2 * q3 * (Binary64.ofBits 0x4000000000000000 /- 2.0f -/)
      let t12'2 : Binary64 := t10'2 + t11'2
      let t13'2 : Binary64 := q1 * vd * (Binary64.ofBits 0x4000000000000000 /- 2.0f -/)
      let t14'2 : Binary64 := q0 * ve * (Binary64.ofBits 0x4000000000000000 /- 2.0f -/)
      let t26'2 : Binary64 := q3 * vn * (Binary64.ofBits 0x4000000000000000 /- 2.0f -/)
      let t15'2 : Binary64 := t13'2 + t14'2 - t26'2
      let t16'2 : Binary64 := q0 * vd * (Binary64.ofBits 0x4000000000000000 /- 2.0f -/)
      let t17'2 : Binary64 := q2 * vn * (Binary64.ofBits 0x4000000000000000 /- 2.0f -/)
      let t27'2 : Binary64 := q1 * ve * (Binary64.ofBits 0x4000000000000000 /- 2.0f -/)
      let t18'2 : Binary64 := t16'2 + t17'2 - t27'2
      let t19'2 : Binary64 := q3 * vd * (Binary64.ofBits 0x4000000000000000 /- 2.0f -/)
      let t20'2 : Binary64 := q2 * ve * (Binary64.ofBits 0x4000000000000000 /- 2.0f -/)
      let t21'2 : Binary64 := q1 * vn * (Binary64.ofBits 0x4000000000000000 /- 2.0f -/)
      let t22'2 : Binary64 := t19'2 + t20'2 + t21'2
      let t23'2 : Binary64 := q3 * ve * (Binary64.ofBits 0x4000000000000000 /- 2.0f -/)
      let t24'2 : Binary64 := q0 * vn * (Binary64.ofBits 0x4000000000000000 /- 2.0f -/)
      let t28'2 : Binary64 := q2 * vd * (Binary64.ofBits 0x4000000000000000 /- 2.0f -/)
      let t25'2 : Binary64 := t23'2 + t24'2 - t28'2
      let t29'2 : Binary64 := s.Pmut[0]! * t15'2
      let t30'2 : Binary64 := s.Pmut[25]! * t18'2
      let t31'2 : Binary64 := s.Pmut[124]! * t8'2
      let t32'2 : Binary64 := s.Pmut[148]! * t12'2
      let t33'2 : Binary64 := s.Pmut[4]! * t15'2
      let t34'2 : Binary64 := s.Pmut[28]! * t18'2
      let t35'2 : Binary64 := s.Pmut[52]! * t22'2
      let t78'2 : Binary64 := s.Pmut[100]! * t3'2
      let t79'2 : Binary64 := s.Pmut[76]! * t25'2
      let t36'2 : Binary64 := t31'2 + t32'2 + t33'2 + t34'2 + t35'2 - t78'2 - t79'2
      let t37'2 : Binary64 := s.Pmut[126]! * t8'2
      let t38'2 : Binary64 := s.Pmut[150]! * t12'2
      let t39'2 : Binary64 := s.Pmut[6]! * t15'2
      let t40'2 : Binary64 := s.Pmut[30]! * t18'2
      let t41'2 : Binary64 := s.Pmut[54]! * t22'2
      let t81'2 : Binary64 := s.Pmut[102]! * t3'2
      let t82'2 : Binary64 := s.Pmut[78]! * t25'2
      let t42'2 : Binary64 := t37'2 + t38'2 + t39'2 + t40'2 + t41'2 - t81'2 - t82'2
      let t43'2 : Binary64 := t12'2 * t42'2
      let t44'2 : Binary64 := s.Pmut[120]! * t8'2
      let t45'2 : Binary64 := s.Pmut[144]! * t12'2
      let t46'2 : Binary64 := s.Pmut[24]! * t18'2
      let t47'2 : Binary64 := s.Pmut[48]! * t22'2
      let t83'2 : Binary64 := s.Pmut[96]! * t3'2
      let t84'2 : Binary64 := s.Pmut[72]! * t25'2
      let t48'2 : Binary64 := t29'2 + t44'2 + t45'2 + t46'2 + t47'2 - t83'2 - t84'2
      let t49'2 : Binary64 := t15'2 * t48'2
      let t50'2 : Binary64 := s.Pmut[121]! * t8'2
      let t51'2 : Binary64 := s.Pmut[145]! * t12'2
      let t52'2 : Binary64 := s.Pmut[1]! * t15'2
      let t53'2 : Binary64 := s.Pmut[49]! * t22'2
      let t85'2 : Binary64 := s.Pmut[97]! * t3'2
      let t86'2 : Binary64 := s.Pmut[73]! * t25'2
      let t54'2 : Binary64 := t30'2 + t50'2 + t51'2 + t52'2 + t53'2 - t85'2 - t86'2
      let t55'2 : Binary64 := t18'2 * t54'2
      let t56'2 : Binary64 := s.Pmut[122]! * t8'2
      let t57'2 : Binary64 := s.Pmut[146]! * t12'2
      let t58'2 : Binary64 := s.Pmut[2]! * t15'2
      let t59'2 : Binary64 := s.Pmut[26]! * t18'2
      let t60'2 : Binary64 := s.Pmut[50]! * t22'2
      let t87'2 : Binary64 := s.Pmut[98]! * t3'2
      let t88'2 : Binary64 := s.Pmut[74]! * t25'2
      let t61'2 : Binary64 := t56'2 + t57'2 + t58'2 + t59'2 + t60'2 - t87'2 - t88'2
      let t62'2 : Binary64 := t22'2 * t61'2
      let t63'2 : Binary64 := s.Pmut[123]! * t8'2
      let t64'2 : Binary64 := s.Pmut[147]! * t12'2
      let t65'2 : Binary64 := s.Pmut[3]! * t15'2
      let t66'2 : Binary64 := s.Pmut[27]! * t18'2
      let t67'2 : Binary64 := s.Pmut[51]! * t22'2
      let t89'2 : Binary64 := s.Pmut[99]! * t3'2
      let t90'2 : Binary64 := s.Pmut[75]! * t25'2
      let t68'2 : Binary64 := t63'2 + t64'2 + t65'2 + t66'2 + t67'2 - t89'2 - t90'2
      let t69'2 : Binary64 := s.Pmut[125]! * t8'2
      let t70'2 : Binary64 := s.Pmut[149]! * t12'2
      let t71'2 : Binary64 := s.Pmut[5]! * t15'2
      let t72'2 : Binary64 := s.Pmut[29]! * t18'2
      let t73'2 : Binary64 := s.Pmut[53]! * t22'2
      let t92'2 : Binary64 := s.Pmut[101]! * t3'2
      let t93'2 : Binary64 := s.Pmut[77]! * t25'2
      let t74'2 : Binary64 := t69'2 + t70'2 + t71'2 + t72'2 + t73'2 - t92'2 - t93'2
      let t75'2 : Binary64 := t8'2 * t74'2
      let t80'2 : Binary64 := t3'2 * t36'2
      let t91'2 : Binary64 := t25'2 * t68'2
      let mut t76'2 : Binary64 := R_VEL'2 + t43'2 + t49'2 + t55'2 + t62'2 + t75'2 - t80'2 - t91'2
      let mut t77'2 : Binary64 := (Binary64.ofBits 0x0000000000000000 /- 0.0 -/)  -- uninitialized in C++; assigned before every read
      if t76'2 > R_VEL'2 then
        t77'2 := (Binary64.ofBits 0x3ff0000000000000 /- 1.0f -/) / t76'2
        s := { s with faultStatus.bad_yvel := false }
      else
        t76'2 := R_VEL'2
        t77'2 := (Binary64.ofBits 0x3ff0000000000000 /- 1.0f -/) / R_VEL'2
        s := { s with faultStatus.bad_yvel := true }
        return (s, w, o)
      s := { s with bodyOdm.varInnov := s.bodyOdm.varInnov.set! 1 t76'2 }
      s := { s with bodyOdm.innov := s.bodyOdm.innov.set! 1 (bodyVelPred.y - s.bodyOdm.dataDelayed.vel.y) }
      w := { w with NavEKF_core_common'Kfusion := w.NavEKF_core_common'Kfusion.set! 0 (t77'2 * (t29'2 - s.Pmut[4]! * t3'2 + s.Pmut[5]! * t8'2 + s.Pmut[6]! * t12'2 + s.Pmut[1]! * t18'2 + s.Pmut[2]! * t22'2 - s.Pmut[3]! * t25'2)) }
      w := { w with NavEKF_core_common'Kfusion := w.NavEKF_core_common'Kfusion.set! 1 (t77'2 * (t30'2 - s.Pmut[28]! * t3'2 + s.Pmut[29]! * t8'2 + s.Pmut[24]! * t15'2 + s.Pmut[30]! * t12'2 + s.Pmut[26]! * t22'2 - s.Pmut[27]! * t25'2)) }
      w := { w with NavEKF_core_common'Kfusion := w.NavEKF_core_common'Kfusion.set! 2 (t77'2 * (t60'2 - s.Pmut[52]! * t3'2 + s.Pmut[53]! * t8'2 + s.Pmut[48]! * t15'2 + s.Pmut[54]! * t12'2 + s.Pmut[49]! * t18'2 - s.Pmut[51]! * t25'2)) }
      w := { w with NavEKF_core_common'Kfusion := w.NavEKF_core_common'Kfusion.set! 3 (t77'2 * (-t90'2 - s.Pmut[76]! * t3'2 + s.Pmut[77]! * t8'2 + s.Pmut[72]! * t15'2 + s.Pmut[78]! * t12'2 + s.Pmut[73]! * t18'2 + s.Pmut[74]! * t22'2)) }
      w := { w with NavEKF_core_common'Kfusion := w.NavEKF_core_common'Kfusion.set! 4 (t77'2 * (-t78'2 + s.Pmut[101]! * t8'2 + s.Pmut[96]! * t15'2 + s.Pmut[102]! * t12'2 + s.Pmut[97]! * t18'2 + s.Pmut[98]! * t22'2 - s.Pmut[99]! * t25'2)) }
      w := { w with NavEKF_core_common'Kfusion := w.NavEKF_core_common'Kfusion.set! 5 (t77'2 * (t69'2 - s.Pmut[124]! * t3'2 + s.Pmut[120]! * t15'2 + s.Pmut[126]! * t12'2 + s.Pmut[121]! * t18'2 + s.Pmut[122]! * t22'2 - s.Pmut[123]! * t25'2)) }
      w := { w with NavEKF_core_common'Kfusion := w.NavEKF_core_common'Kfusion.set! 6 (t77'2 * (t38'2 - s.Pmut[148]! * t3'2 + s.Pmut[149]! * t8'2 + s.Pmut[144]! * t15'2 + s.Pmut[145]! * t18'2 + s.Pmut[146]! * t22'2 - s.Pmut[147]! * t25'2)) }
      let mut kalman_mask'2 : UInt32 := Int32.toUInt32 (((1 : Int32) <<< (7 : Int32)) ||| ((1 : Int32) <<< (8 : Int32)) ||| ((1 : Int32) <<< (9 : Int32)))
      if !s.inhibitDelAngBiasStates then
        kalman_mask'2 := kalman_mask'2 ||| Int32.toUInt32 (((1 : Int32) <<< (10 : Int32)) ||| ((1 : Int32) <<< (11 : Int32)) ||| ((1 : Int32) <<< (12 : Int32)))
      if !s.inhibitDelVelBiasStates && !s.badIMUdata then
        for index'4' in [0:3] do
          let index'4 : UInt8 := Nat.toUInt8 index'4'
          let stateIndex'2 : UInt8 := Int8.toUInt8 (Int32.toInt8 (UInt32.toInt32 (UInt8.toUInt32 index'4) + (13 : Int32)))
          if !s.dvelBiasAxisInhibit[UInt8.toNat index'4]! then
            kalman_mask'2 := kalman_mask'2 ||| Int32.toUInt32 ((1 : Int32) <<< UInt32.toInt32 (UInt8.toUInt32 stateIndex'2))
      if !s.inhibitMagStates then
        kalman_mask'2 := kalman_mask'2 ||| Int32.toUInt32 (((1 : Int32) <<< (16 : Int32)) ||| ((1 : Int32) <<< (17 : Int32)) ||| ((1 : Int32) <<< (18 : Int32)) ||| ((1 : Int32) <<< (19 : Int32)) ||| ((1 : Int32) <<< (20 : Int32)) ||| ((1 : Int32) <<< (21 : Int32)))
      if !s.inhibitWindStates && !s.treatWindStatesAsTruth then
        kalman_mask'2 := kalman_mask'2 ||| Int32.toUInt32 (((1 : Int32) <<< (22 : Int32)) ||| ((1 : Int32) <<< (23 : Int32)))
      for i'2' in [7:24] do
        let i'2 : Int32 := Nat.toInt32 i'2'
        let mut res'2 : Binary64 := (Binary64.ofBits 0x0000000000000000 /- 0 -/)
        if kalman_mask'2 &&& Int32.toUInt32 ((1 : Int32) <<< i'2) != (0 : UInt32) then
          res'2 := t77'2 * (-s.Pmut[Int32.toNatClampNeg i'2 * 24 + 4]! * t3'2 + s.Pmut[Int32.toNatClampNeg i'2 * 24 + 5]! * t8'2 + s.Pmut[Int32.toNatClampNeg i'2 * 24]! * t15'2 + s.Pmut[Int32.toNatClampNeg i'2 * 24 + 6]! * t12'2 + s.Pmut[Int32.toNatClampNeg i'2 * 24 + 1]! * t18'2 + s.Pmut[Int32.toNatClampNeg i'2 * 24 + 2]! * t22'2 - s.Pmut[Int32.toNatClampNeg i'2 * 24 + 3]! * t25'2)
        w := { w with NavEKF_core_common'Kfusion := w.NavEKF_core_common'Kfusion.set! (Int32.toNatClampNeg i'2) res'2 }
    else if UInt32.toInt32 (UInt8.toUInt32 obsIndex) == (2 : Int32) then
      H_VEL := H_VEL.set! 0 (q0 * vd * (Binary64.ofBits 0x4000000000000000 /- 2.0f -/) - q1 * ve * (Binary64.ofBits 0x4000000000000000 /- 2.0f -/) + q2 * vn * (Binary64.ofBits 0x4000000000000000 /- 2.0f -/))
      H_VEL := H_VEL.set! 1 (q1 * vd * (Binary64.ofBits 0xc000000000000000 /- -2.0f -/) - q0 * ve * (Binary64.ofBits 0x4000000000000000 /- 2.0f -/) + q3 * vn * (Binary64.ofBits 0x4000000000000000 /- 2.0f -/))
      H_VEL := H_VEL.set! 2 (q2 * vd * (Binary64.ofBits 0xc000000000000000 /- -2.0f -/) + q3 * ve * (Binary64.ofBits 0x4000000000000000 /- 2.0f -/) + q0 * vn * (Binary64.ofBits 0x4000000000000000 /- 2.0f -/))
      H_VEL := H_VEL.set! 3 (q3 * vd * (Binary64.ofBits 0x4000000000000000 /- 2.0f -/) + q2 * ve * (Binary64.ofBits 0x4000000000000000 /- 2.0f -/) + q1 * vn * (Binary64.ofBits 0x4000000000000000 /- 2.0f -/))
      H_VEL := H_VEL.set! 4 (q0 * q2 * (Binary64.ofBits 0x4000000000000000 /- 2.0f -/) + q1 * q3 * (Binary64.ofBits 0x4000000000000000 /- 2.0f -/))
      H_VEL := H_VEL.set! 5 (q0 * q1 * (Binary64.ofBits 0xc000000000000000 /- -2.0f -/) + q2 * q3 * (Binary64.ofBits 0x4000000000000000 /- 2.0f -/))
      H_VEL := H_VEL.set! 6 (q0 * q0 - q1 * q1 - q2 * q2 + q3 * q3)
      for index'5' in [7:24] do
        let index'5 : UInt8 := Nat.toUInt8 index'5'
        H_VEL := H_VEL.set! (UInt8.toNat index'5) (Binary64.ofBits 0x0000000000000000 /- 0.0f -/)
      let R_VEL'3 : Binary64 := Estimator_lib.sq_double s.bodyOdm.dataDelayed.velErr
      let t2'3 : Binary64 := q0 * q2 * (Binary64.ofBits 0x4000000000000000 /- 2.0f -/)
      let t3'3 : Binary64 := q1 * q3 * (Binary64.ofBits 0x4000000000000000 /- 2.0f -/)
      let t4'3 : Binary64 := t2'3 + t3'3
      let t5'3 : Binary64 := q0 * q0
      let t6'3 : Binary64 := q1 * q1
      let t7'3 : Binary64 := q2 * q2
      let t8'3 : Binary64 := q3 * q3
      let t9'3 : Binary64 := t5'3 - t6'3 - t7'3 + t8'3
      let t10'3 : Binary64 := q0 * q1 * (Binary64.ofBits 0x4000000000000000 /- 2.0f -/)
      let t25'3 : Binary64 := q2 * q3 * (Binary64.ofBits 0x4000000000000000 /- 2.0f -/)
      let t11'3 : Binary64 := t10'3 - t25'3
      let t12'3 : Binary64 := q0 * vd * (Binary64.ofBits 0x4000000000000000 /- 2.0f -/)
      let t13'3 : Binary64 := q2 * vn * (Binary64.ofBits 0x4000000000000000 /- 2.0f -/)
      let t26'3 : Binary64 := q1 * ve * (Binary64.ofBits 0x4000000000000000 /- 2.0f -/)
      let t14'3 : Binary64 := t12'3 + t13'3 - t26'3
      let t15'3 : Binary64 := q1 * vd * (Binary64.ofBits 0x4000000000000000 /- 2.0f -/)
      let t16'3 : Binary64 := q0 * ve * (Binary64.ofBits 0x4000000000000000 /- 2.0f -/)
      let t27'3 : Binary64 := q3 * vn * (Binary64.ofBits 0x4000000000000000 /- 2.0f -/)
      let t17'3 : Binary64 := t15'3 + t16'3 - t27'3
      let t18'3 : Binary64 := q3 * ve * (Binary64.ofBits 0x4000000000000000 /- 2.0f -/)
      let t19'3 : Binary64 := q0 * vn * (Binary64.ofBits 0x4000000000000000 /- 2.0f -/)
      let t28'3 : Binary64 := q2 * vd * (Binary64.ofBits 0x4000000000000000 /- 2.0f -/)
      let t20'3 : Binary64 := t18'3 + t19'3 - t28'3
      let t21'3 : Binary64 := q3 * vd * (Binary64.ofBits 0x4000000000000000 /- 2.0f -/)
      let t22'3 : Binary64 := q2 * ve * (Binary64.ofBits 0x4000000000000000 /- 2.0f -/)
      let t23'3 : Binary64 := q1 * vn * (Binary64.ofBits 0x4000000000000000 /- 2.0f -/)
      let t24'3 : Binary64 := t21'3 + t22'3 + t23'3
      let t29'3 : Binary64 := s.Pmut[0]! * t14'3
      let t30'3 : Binary64 := s.Pmut[148]! * t9'3
      let t31'3 : Binary64 := s.Pmut[100]! * t4'3
      let t32'3 : Binary64 := s.Pmut[4]! * t14'3
      let t33'3 : Binary64 := s.Pmut[52]! * t20'3
      let t34'3 : Binary64 := s.Pmut[76]! * t24'3
      let t78'3 : Binary64 := s.Pmut[124]! * t11'3
      let t79'3 : Binary64 := s.Pmut[28]! * t17'3
      let t35'3 : Binary64 := t30'3 + t31'3 + t32'3 + t33'3 + t34'3 - t78'3 - t79'3
      let t36'3 : Binary64 := t4'3 * t35'3
      let t37'3 : Binary64 := s.Pmut[149]! * t9'3
      let t38'3 : Binary64 := s.Pmut[101]! * t4'3
      let t39'3 : Binary64 := s.Pmut[5]! * t14'3
      let t40'3 : Binary64 := s.Pmut[53]! * t20'3
      let t41'3 : Binary64 := s.Pmut[77]! * t24'3
      let t80'3 : Binary64 := s.Pmut[125]! * t11'3
      let t81'3 : Binary64 := s.Pmut[29]! * t17'3
      let t42'3 : Binary64 := t37'3 + t38'3 + t39'3 + t40'3 + t41'3 - t80'3 - t81'3
      let t43'3 : Binary64 := s.Pmut[144]! * t9'3
      let t44'3 : Binary64 := s.Pmut[96]! * t4'3
      let t45'3 : Binary64 := s.Pmut[48]! * t20'3
      let t46'3 : Binary64 := s.Pmut[72]! * t24'3
      let t83'3 : Binary64 := s.Pmut[120]! * t11'3
      let t84'3 : Binary64 := s.Pmut[24]! * t17'3
      let t47'3 : Binary64 := t29'3 + t43'3 + t44'3 + t45'3 + t46'3 - t83'3 - t84'3
      let t48'3 : Binary64 := t14'3 * t47'3
      let t49'3 : Binary64 := s.Pmut[145]! * t9'3
      let t50'3 : Binary64 := s.Pmut[97]! * t4'3
      let t51'3 : Binary64 := s.Pmut[1]! * t14'3
      let t52'3 : Binary64 := s.Pmut[49]! * t20'3
      let t53'3 : Binary64 := s.Pmut[73]! * t24'3
      let t85'3 : Binary64 := s.Pmut[121]! * t11'3
      let t86'3 : Binary64 := s.Pmut[25]! * t17'3
      let t54'3 : Binary64 := t49'3 + t50'3 + t51'3 + t52'3 + t53'3 - t85'3 - t86'3
      let t55'3 : Binary64 := s.Pmut[146]! * t9'3
      let t56'3 : Binary64 := s.Pmut[98]! * t4'3
      let t57'3 : Binary64 := s.Pmut[2]! * t14'3
      let t58'3 : Binary64 := s.Pmut[50]! * t20'3
      let t59'3 : Binary64 := s.Pmut[74]! * t24'3
      let t88'3 : Binary64 := s.Pmut[122]! * t11'3
      let t89'3 : Binary64 := s.Pmut[26]! * t17'3
      let t60'3 : Binary64 := t55'3 + t56'3 + t57'3 + t58'3 + t59'3 - t88'3 - t89'3
      let t61'3 : Binary64 := t20'3 * t60'3
      let t62'3 : Binary64 := s.Pmut[147]! * t9'3
      let t63'3 : Binary64 := s.Pmut[99]! * t4'3
      let t64'3 : Binary64 := s.Pmut[3]! * t14'3
      let t65'3 : Binary64 := s.Pmut[51]! * t20'3
      let t66'3 : Binary64 := s.Pmut[75]! * t24'3
      let t90'3 : Binary64 := s.Pmut[123]! * t11'3
      let t91'3 : Binary64 := s.Pmut[27]! * t17'3
      let t67'3 : Binary64 := t62'3 + t63'3 + t64'3 + t65'3 + t66'3 - t90'3 - t91'3
      let t68'3 : Binary64 := t24'3 * t67'3
      let t69'3 : Binary64 := s.Pmut[150]! * t9'3
      let t70'3 : Binary64 := s.Pmut[102]! * t4'3
      let t71'3 : Binary64 := s.Pmut[6]! * t14'3
      let t72'3 : Binary64 := s.Pmut[54]! * t20'3
      let t73'3 : Binary64 := s.Pmut[78]! * t24'3
      let t92'3 : Binary64 := s.Pmut[126]! * t11'3
      let t93'3 : Binary64 := s.Pmut[30]! * t17'3
      let t74'3 : Binary64 := t69'3 + t70'3 + t71'3 + t72'3 + t73'3 - t92'3 - t93'3
      let t75'3 : Binary64 := t9'3 * t74'3
      let t82'3 : Binary64 := t11'3 * t42'3
      let t87'3 : Binary64 := t17'3 * t54'3
      let mut t76'3 : Binary64 := R_VEL'3 + t36'3 + t48'3 + t61'3 + t68'3 + t75'3 - t82'3 - t87'3
      let mut t77'3 : Binary64 := (Binary64.ofBits 0x0000000000000000 /- 0.0 -/)  -- uninitialized in C++; assigned before every read
      if t76'3 > R_VEL'3 then
        t77'3 := (Binary64.ofBits 0x3ff0000000000000 /- 1.0f -/) / t76'3
        s := { s with faultStatus.bad_zvel := false }
      else
        t76'3 := R_VEL'3
        t77'3 := (Binary64.ofBits 0x3ff0000000000000 /- 1.0f -/) / R_VEL'3
        s := { s with faultStatus.bad_zvel := true }
        return (s, w, o)
      s := { s with bodyOdm.varInnov := s.bodyOdm.varInnov.set! 2 t76'3 }
      s := { s with bodyOdm.innov := s.bodyOdm.innov.set! 2 (bodyVelPred.z - s.bodyOdm.dataDelayed.vel.z) }
      w := { w with NavEKF_core_common'Kfusion := w.NavEKF_core_common'Kfusion.set! 0 (t77'3 * (t29'3 + s.Pmut[4]! * t4'3 + s.Pmut[6]! * t9'3 - s.Pmut[5]! * t11'3 - s.Pmut[1]! * t17'3 + s.Pmut[2]! * t20'3 + s.Pmut[3]! * t24'3)) }
      w := { w with NavEKF_core_common'Kfusion := w.NavEKF_core_common'Kfusion.set! 1 (t77'3 * (s.Pmut[28]! * t4'3 + s.Pmut[24]! * t14'3 + s.Pmut[30]! * t9'3 - s.Pmut[29]! * t11'3 - s.Pmut[25]! * t17'3 + s.Pmut[26]! * t20'3 + s.Pmut[27]! * t24'3)) }
      w := { w with NavEKF_core_common'Kfusion := w.NavEKF_core_common'Kfusion.set! 2 (t77'3 * (t58'3 + s.Pmut[52]! * t4'3 + s.Pmut[48]! * t14'3 + s.Pmut[54]! * t9'3 - s.Pmut[53]! * t11'3 - s.Pmut[49]! * t17'3 + s.Pmut[51]! * t24'3)) }
      w := { w with NavEKF_core_common'Kfusion := w.NavEKF_core_common'Kfusion.set! 3 (t77'3 * (t66'3 + s.Pmut[76]! * t4'3 + s.Pmut[72]! * t14'3 + s.Pmut[78]! * t9'3 - s.Pmut[77]! * t11'3 - s.Pmut[73]! * t17'3 + s.Pmut[74]! * t20'3)) }
      w := { w with NavEKF_core_common'Kfusion := w.NavEKF_core_common'Kfusion.set! 4 (t77'3 * (t31'3 + s.Pmut[96]! * t14'3 + s.Pmut[102]! * t9'3 - s.Pmut[101]! * t11'3 - s.Pmut[97]! * t17'3 + s.Pmut[98]! * t20'3 + s.Pmut[99]! * t24'3)) }
      w := { w with NavEKF_core_common'Kfusion := w.NavEKF_core_common'Kfusion.set! 5 (t77'3 * (-t80'3 + s.Pmut[124]! * t4'3 + s.Pmut[120]! * t14'3 + s.Pmut[126]! * t9'3 - s.Pmut[121]! * t17'3 + s.Pmut[122]! * t20'3 + s.Pmut[123]! * t24'3)) }
      w := { w with NavEKF_core_common'Kfusion := w.NavEKF_core_common'Kfusion.set! 6 (t77'3 * (t69'3 + s.Pmut[148]! * t4'3 + s.Pmut[144]! * t14'3 - s.Pmut[149]! * t11'3 - s.Pmut[145]! * t17'3 + s.Pmut[146]! * t20'3 + s.Pmut[147]! * t24'3)) }
      let mut kalman_mask'3 : UInt32 := Int32.toUInt32 (((1 : Int32) <<< (7 : Int32)) ||| ((1 : Int32) <<< (8 : Int32)) ||| ((1 : Int32) <<< (9 : Int32)))
      if !s.inhibitDelAngBiasStates then
        kalman_mask'3 := kalman_mask'3 ||| Int32.toUInt32 (((1 : Int32) <<< (10 : Int32)) ||| ((1 : Int32) <<< (11 : Int32)) ||| ((1 : Int32) <<< (12 : Int32)))
      if !s.inhibitDelVelBiasStates && !s.badIMUdata then
        for index'6' in [0:3] do
          let index'6 : UInt8 := Nat.toUInt8 index'6'
          let stateIndex'3 : UInt8 := Int8.toUInt8 (Int32.toInt8 (UInt32.toInt32 (UInt8.toUInt32 index'6) + (13 : Int32)))
          if !s.dvelBiasAxisInhibit[UInt8.toNat index'6]! then
            kalman_mask'3 := kalman_mask'3 ||| Int32.toUInt32 ((1 : Int32) <<< UInt32.toInt32 (UInt8.toUInt32 stateIndex'3))
      if !s.inhibitMagStates then
        kalman_mask'3 := kalman_mask'3 ||| Int32.toUInt32 (((1 : Int32) <<< (16 : Int32)) ||| ((1 : Int32) <<< (17 : Int32)) ||| ((1 : Int32) <<< (18 : Int32)) ||| ((1 : Int32) <<< (19 : Int32)) ||| ((1 : Int32) <<< (20 : Int32)) ||| ((1 : Int32) <<< (21 : Int32)))
      if !s.inhibitWindStates && !s.treatWindStatesAsTruth then
        kalman_mask'3 := kalman_mask'3 ||| Int32.toUInt32 (((1 : Int32) <<< (22 : Int32)) ||| ((1 : Int32) <<< (23 : Int32)))
      for i'3' in [7:24] do
        let i'3 : Int32 := Nat.toInt32 i'3'
        let mut res'3 : Binary64 := (Binary64.ofBits 0x0000000000000000 /- 0 -/)
        if kalman_mask'3 &&& Int32.toUInt32 ((1 : Int32) <<< i'3) != (0 : UInt32) then
          res'3 := t77'3 * (s.Pmut[Int32.toNatClampNeg i'3 * 24 + 4]! * t4'3 + s.Pmut[Int32.toNatClampNeg i'3 * 24]! * t14'3 + s.Pmut[Int32.toNatClampNeg i'3 * 24 + 6]! * t9'3 - s.Pmut[Int32.toNatClampNeg i'3 * 24 + 5]! * t11'3 - s.Pmut[Int32.toNatClampNeg i'3 * 24 + 1]! * t17'3 + s.Pmut[Int32.toNatClampNeg i'3 * 24 + 2]! * t20'3 + s.Pmut[Int32.toNatClampNeg i'3 * 24 + 3]! * t24'3)
        w := { w with NavEKF_core_common'Kfusion := w.NavEKF_core_common'Kfusion.set! (Int32.toNatClampNeg i'3) res'3 }
    else
      return (s, w, o)
    s := { s with bodyOdm.testRatio := s.bodyOdm.testRatio.set! (UInt8.toNat obsIndex) (Estimator_lib.sq_double s.bodyOdm.innov[UInt8.toNat obsIndex]! / (Binary32.toBinary64 (Estimator_lib.sq_float (Binary32.ofBits 0x40a00000 /- 5.0f -/)) * s.bodyOdm.varInnov[UInt8.toNat obsIndex]!)) }
    if s.bodyOdm.testRatio[UInt8.toNat obsIndex]! < (Binary64.ofBits 0x3ff0000000000000 /- 1.0f -/) then
      s := { s with bodyOdm.prevFuseTime_ms := s.imuSampleTime_ms }
      if !s.bodyOdm.fusionActive then
        s := { s with bodyOdm.fusionActive := true }
        o := o.push (Output.send_text (6 : UInt32) "EKF3 IMU%u fusing odometry" #[Sum.inl (UInt32.toUInt64 (UInt8.toUInt32 s.imu_index))])
      let t'3 : UInt32 := Int32.toUInt32 (0 : Int32)
      let t'4 : UInt32 := UInt8.toUInt32 s.stateIndexLim
      for i'4' in [0:((Int.ofNat t'4.toNat) - (Int.ofNat t'3.toNat) + 1).toNat] do  -- C++ loop bounded by a runtime value (--runtime-loops)
        let i'4 : UInt32 := t'3 + Nat.toUInt32 i'4'
        let t'5 : UInt32 := Int32.toUInt32 (0 : Int32)
        let t'6 : UInt32 := UInt8.toUInt32 s.stateIndexLim
        for j' in [0:((Int.ofNat t'6.toNat) - (Int.ofNat t'5.toNat) + 1).toNat] do  -- C++ loop bounded by a runtime value (--runtime-loops)
          let j : UInt32 := t'5 + Nat.toUInt32 j'
          let mut res'4 : Binary64 := (Binary64.ofBits 0x0000000000000000 /- 0 -/)
          res'4 := res'4 + (w.NavEKF_core_common'Kfusion[UInt32.toNat i'4]! * H_VEL[0]!) * s.Pmut[UInt32.toNat j]!
          res'4 := res'4 + (w.NavEKF_core_common'Kfusion[UInt32.toNat i'4]! * H_VEL[1]!) * s.Pmut[24 + UInt32.toNat j]!
          res'4 := res'4 + (w.NavEKF_core_common'Kfusion[UInt32.toNat i'4]! * H_VEL[2]!) * s.Pmut[48 + UInt32.toNat j]!
          res'4 := res'4 + (w.NavEKF_core_common'Kfusion[UInt32.toNat i'4]! * H_VEL[3]!) * s.Pmut[72 + UInt32.toNat j]!
          res'4 := res'4 + (w.NavEKF_core_common'Kfusion[UInt32.toNat i'4]! * H_VEL[4]!) * s.Pmut[96 + UInt32.toNat j]!
          res'4 := res'4 + (w.NavEKF_core_common'Kfusion[UInt32.toNat i'4]! * H_VEL[5]!) * s.Pmut[120 + UInt32.toNat j]!
          res'4 := res'4 + (w.NavEKF_core_common'Kfusion[UInt32.toNat i'4]! * H_VEL[6]!) * s.Pmut[144 + UInt32.toNat j]!
          w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! (UInt32.toNat i'4 * 24 + UInt32.toNat j) res'4 }
      let (t'7, t'8) := FinishFusion s w s.bodyOdm.innov[UInt8.toNat obsIndex]! false
      s := t'7
      if t'8 then
        if UInt32.toInt32 (UInt8.toUInt32 obsIndex) == (0 : Int32) then
          s := { s with faultStatus.bad_xvel := true }
        else if UInt32.toInt32 (UInt8.toUInt32 obsIndex) == (1 : Int32) then
          s := { s with faultStatus.bad_yvel := true }
        else if UInt32.toInt32 (UInt8.toUInt32 obsIndex) == (2 : Int32) then
          s := { s with faultStatus.bad_zvel := true }
  return (s, w, o)

/-- C++ `void NavEKF3_core::SelectBodyOdomFusion()`, `AP_NavEKF3/AP_NavEKF3_PosVelFusion.cpp:2079-2129`. -/
def SelectBodyOdomFusion (s : State) (w : World) (o : Outputs) : State × World × Outputs := Id.run do
  let mut s := s
  let mut w := w
  let mut o := o
  if s.magFusePerformed && (decide (s.dtIMUavg < (Binary64.ofBits 0x3f747ae140000000 /- 0.005f -/))) && !s.bodyOdm.fusionDelayed then
    s := { s with bodyOdm.fusionDelayed := true }
    return (s, w, o)
  else
    s := { s with bodyOdm.fusionDelayed := false }
  let (t'1, t'2, t'3) := EKF_obs_buffer_t_NavEKF3_core_vel_odm_elements.recall_vel_odm_elements_uint32_t s.bodyOdm.stored s.bodyOdm.dataDelayed s.imuDataDelayed.time_ms
  s := { s with bodyOdm.stored := t'1 }
  s := { s with bodyOdm.dataDelayed := t'2 }
  let bodyOdomDataToFuse : Bool := t'3
  if bodyOdomDataToFuse && AP_NavEKF_Source.useVelXYSource w.EKF3.sources AP_NavEKF_Source.SourceXY.EXTNAV s.core_index then
    let (t'4, t'5, t'6) := FuseBodyVel s w o
    w := t'5
    s := t'4
    o := t'6
  let (t'7, t'8, t'9) := EKF_obs_buffer_t_NavEKF3_core_wheel_odm_elements.recall_wheel_odm_elements_uint32_t s.bodyOdm.storedWheel s.bodyOdm.wheelDataDelayed s.imuDataDelayed.time_ms
  s := { s with bodyOdm.storedWheel := t'7 }
  s := { s with bodyOdm.wheelDataDelayed := t'8 }
  let wheelOdomDataToFuse : Bool := t'9
  if wheelOdomDataToFuse && AP_NavEKF_Source.useVelXYSource w.EKF3.sources AP_NavEKF_Source.SourceXY.WHEEL_ENCODER s.core_index then
    if s.bodyOdm.wheelDataDelayed.delTime > (Binary64.ofBits 0x3f889374c0000000 /- (double)6442451/536870912 -/) then
      let fwdSpd : Binary64 := s.bodyOdm.wheelDataDelayed.delAng * s.bodyOdm.wheelDataDelayed.radius * ((Binary64.ofBits 0x3ff0000000000000 /- 1.0f -/) / s.bodyOdm.wheelDataDelayed.delTime)
      let mut unitVec : Vector3p.State := Vector3p.init_void
      unitVec := { unitVec with x := s.prevTnb.a.x }
      unitVec := { unitVec with y := s.prevTnb.a.y }
      unitVec := { unitVec with z := (Binary64.ofBits 0x0000000000000000 /- 0.0f -/) }
      unitVec := Vector3p.normalize unitVec
      let velNED : Vector3p.State := Vector3p.op_mul_double unitVec fwdSpd
      s := { s with bodyOdm.dataDelayed.vel := Matrix3_double.op_mul_Vector3p s.prevTnb velNED }
      s := { s with bodyOdm.dataDelayed.body_offset := s.bodyOdm.wheelDataDelayed.hub_offset }
      s := { s with bodyOdm.dataDelayed.velErr := Binary32.toBinary64 (AP_ParamT_float_4.get_void w.EKF3._wencOdmVelErr) }
      let (t'10, t'11, t'12) := FuseBodyVel s w o
      w := t'11
      s := t'10
      o := t'12
  return (s, w, o)

end NavEKF3_core

namespace NavEKF3

/-- C++ `bool NavEKF3::healthy() const`, `AP_NavEKF3/AP_NavEKF3.cpp:1166-1172`. -/
def healthy (s : State) (w : World) : Bool := Id.run do
  if !(s.core != WPtr.null) then
    return false
  return NavEKF3_core.healthy w.heap'NavEKF3_core[((WPtr.index s.core) + (UInt8.toNat s.primary))]!

end NavEKF3

namespace NavEKF3

/-- C++ `int8_t NavEKF3::getPrimaryCoreIMUIndex() const`, `AP_NavEKF3/AP_NavEKF3.cpp:1228-1234`. -/
def getPrimaryCoreIMUIndex (s : State) (w : World) : Int8 := Id.run do
  if !(s.core != WPtr.null) then
    return Int32.toInt8 (-(1 : Int32))
  return UInt8.toInt8 (NavEKF3_core.getIMUIndex w.heap'NavEKF3_core[((WPtr.index s.core) + (UInt8.toNat s.primary))]!)

end NavEKF3

namespace NavEKF3

/-- C++ `void NavEKF3::getQuaternion(Quaternion & quat) const`, `AP_NavEKF3/AP_NavEKF3.cpp:1543-1548`. -/
def getQuaternion (s : State) (w : World) (quat : Quaternion.State) : Quaternion.State := Id.run do
  let mut quat := quat
  if (s.core != WPtr.null) then
    quat := NavEKF3_core.getQuaternion w.heap'NavEKF3_core[((WPtr.index s.core) + (UInt8.toNat s.primary))]! quat
  return quat

end NavEKF3

namespace NavEKF3_core

/-- C++ `void NavEKF3_core::getRotationBodyToNED(Matrix3f & mat) const`, `AP_NavEKF3/AP_NavEKF3_Outputs.cpp:155-159`. -/
def getRotationBodyToNED (s : State) (w : World) (mat : Matrix3f.State) : Matrix3f.State := Id.run do
  let mut mat := mat
  mat := QuaternionT_double.rotation_matrix_Matrix3f s.outputDataNew.quat mat
  mat := Matrix3f.op_mul_Matrix3f mat (AP_DAL.get_rotation_vehicle_body_to_autopilot_body w.heap'AP_DAL[(WPtr.index w.AP_DAL'_singleton)]!)
  return mat

end NavEKF3_core

namespace NavEKF3

/-- C++ `void NavEKF3::getRotationBodyToNED(Matrix3f & mat) const`, `AP_NavEKF3/AP_NavEKF3.cpp:1524-1529`. -/
def getRotationBodyToNED (s : State) (w : World) (mat : Matrix3f.State) : Matrix3f.State := Id.run do
  let mut mat := mat
  if (s.core != WPtr.null) then
    mat := NavEKF3_core.getRotationBodyToNED w.heap'NavEKF3_core[((WPtr.index s.core) + (UInt8.toNat s.primary))]! w mat
  return mat

end NavEKF3

namespace NavEKF3_core

/-- C++ `void NavEKF3_core::getEulerAngles(Vector3f & eulers) const`, `AP_NavEKF3/AP_NavEKF3_Outputs.cpp:128-132`. -/
def getEulerAngles (s : State) (w : World) (euler : Vector3f.State) : Vector3f.State := Id.run do
  let mut euler := euler
  euler := QuaternionT_double.to_euler_Vector3f s.outputDataNew.quat euler
  euler := Vector3f.op_sub_Vector3f euler (AP_DAL.get_trim w.heap'AP_DAL[(WPtr.index w.AP_DAL'_singleton)]!)
  return euler

end NavEKF3_core

namespace NavEKF3

/-- C++ `void NavEKF3::getEulerAngles(Vector3f & eulers) const`, `AP_NavEKF3/AP_NavEKF3.cpp:1516-1521`. -/
def getEulerAngles (s : State) (w : World) (eulers : Vector3f.State) : Vector3f.State := Id.run do
  let mut eulers := eulers
  if (s.core != WPtr.null) then
    eulers := NavEKF3_core.getEulerAngles w.heap'NavEKF3_core[((WPtr.index s.core) + (UInt8.toNat s.primary))]! w eulers
  return eulers

end NavEKF3

namespace NavEKF3

/-- C++ `void NavEKF3::getVelNED(Vector3f & vel) const`, `AP_NavEKF3/AP_NavEKF3.cpp:1259-1264`. -/
def getVelNED (s : State) (w : World) (vel : Vector3f.State) : Vector3f.State := Id.run do
  let mut vel := vel
  if (s.core != WPtr.null) then
    vel := NavEKF3_core.getVelNED w.heap'NavEKF3_core[((WPtr.index s.core) + (UInt8.toNat s.primary))]! vel
  return vel

end NavEKF3

namespace NavEKF3_core

/-- C++ `bool NavEKF3_core::getPosNE(Vector2p & posNE) const`, `AP_NavEKF3/AP_NavEKF3_Outputs.cpp:227-264`. -/
def getPosNE (s : State) (w : World) (posNE : Vector2p.State) : Vector2p.State × Bool := Id.run do
  let mut posNE := posNE
  if UInt32.toInt32 (NavEKF3_core.AidingMode.toInt s.PV_AidingMode) != UInt32.toInt32 (NavEKF3_core.AidingMode.toInt NavEKF3_core.AidingMode.AID_NONE) then
    posNE := Vector2p.op_add (Vector2p.op_add (Vector2p.todouble ({ x := s.outputDataNew.position.x, y := s.outputDataNew.position.y } : Vector2p.State)) (Vector2p.todouble ({ x := s.posOffsetNED.x, y := s.posOffsetNED.y } : Vector2p.State))) (Location.get_distance_NE_postype w.EKF3.common_EKF_origin s.EKF_origin)
    return (posNE, true)
  else
    if s.validOrigin then
      if AP_GPS_FixType.toInt (AP_DAL_GPS.status_uint8_t w.heap'AP_DAL[(WPtr.index w.AP_DAL'_singleton)]!._gps s.selected_gps) ≥ AP_GPS_FixType.toInt AP_GPS_FixType.FIX_2D then
        let t'1 := s.selected_gps
        posNE := Location.get_distance_NE_postype w.EKF3.common_EKF_origin w.heap'AP_DAL[(WPtr.index w.AP_DAL'_singleton)]!._gps.tmp_location[UInt8.toNat t'1]!
        return (posNE, false)
      else
        posNE := Vector2p.todouble ({ x := s.outputDataNew.position.x, y := s.outputDataNew.position.y } : Vector2p.State)
        return (posNE, false)
    else
      posNE := Vector2p.zero posNE
      return (posNE, false)

end NavEKF3_core

namespace NavEKF3

/-- C++ `bool NavEKF3::getPosNE(Vector2p & posNE) const`, `AP_NavEKF3/AP_NavEKF3.cpp:1239-1245`. -/
def getPosNE (s : State) (w : World) (posNE : Vector2p.State) : World × Vector2p.State × Bool := Id.run do
  let mut w := w
  let mut posNE := posNE
  if !(s.core != WPtr.null) then
    return (w, posNE, false)
  w := { w with EKF3 := s }  -- this object's state into the World: the call reaches it
  let (t'1, t'2) := NavEKF3_core.getPosNE w.heap'NavEKF3_core[((WPtr.index s.core) + (UInt8.toNat s.primary))]! w posNE
  posNE := t'1
  return (w, posNE, t'2)

end NavEKF3

namespace NavEKF3_core

/-- C++ `bool NavEKF3_core::getPosD_local(postype_t & posD) const`, `AP_NavEKF3/AP_NavEKF3_Outputs.cpp:268-275`. -/
def getPosD_local (s : State) (posD : Binary64) : Binary64 × Bool := Id.run do
  let mut posD := posD
  posD := s.outputDataNew.position.z + s.posOffsetNED.z
  return (posD, (s.filterStatus >>> 5 &&& 1 != 0))

/-- C++ `bool NavEKF3_core::getPosD(postype_t & posD) const`, `AP_NavEKF3/AP_NavEKF3_Outputs.cpp:279-290`. -/
def getPosD (s : State) (w : World) (posD : Binary64) : Binary64 × Bool := Id.run do
  let mut posD := posD
  let (t'1, t'2) := getPosD_local s posD
  posD := t'1
  let ret : Bool := t'2
  let mut local_origin : Location.State := Location.init_void
  let (t'3, t'4) := getOriginLLH s w local_origin
  local_origin := t'3
  if t'4 then
    posD := posD + Binary32.toBinary64 (Int32.toBinary32 (w.EKF3.common_EKF_origin.alt - local_origin.alt) * (Binary32.ofBits 0x3c23d70a /- 0.01 -/))
  return (posD, ret)

end NavEKF3_core

namespace NavEKF3

/-- C++ `bool NavEKF3::getPosD(postype_t & posD) const`, `AP_NavEKF3/AP_NavEKF3.cpp:1250-1256`. -/
def getPosD (s : State) (w : World) (posD : Binary64) : World × Binary64 × Bool := Id.run do
  let mut w := w
  let mut posD := posD
  if !(s.core != WPtr.null) then
    return (w, posD, false)
  w := { w with EKF3 := s }  -- this object's state into the World: the call reaches it
  let (t'1, t'2) := NavEKF3_core.getPosD w.heap'NavEKF3_core[((WPtr.index s.core) + (UInt8.toNat s.primary))]! w posD
  posD := t'1
  return (w, posD, t'2)

end NavEKF3

namespace NavEKF3

/-- C++ `void NavEKF3::getAccelBias(int8_t instance, Vector3f & accelBias) const`, `AP_NavEKF3/AP_NavEKF3.cpp:1318-1324`. -/
def getAccelBias (s : State) (w : World) («instance» : Int8) (accelBias : Vector3f.State) : Vector3f.State := Id.run do
  let mut «instance» := «instance»
  let mut accelBias := accelBias
  if decide (Int8.toInt32 «instance» < (0 : Int32)) || decide (Int8.toInt32 «instance» ≥ UInt32.toInt32 (UInt8.toUInt32 s.num_cores)) then
    «instance» := UInt8.toInt8 s.primary
  if (s.core != WPtr.null) then
    accelBias := NavEKF3_core.getAccelBias w.heap'NavEKF3_core[((WPtr.index s.core) + (Int8.toNatClampNeg «instance»))]! accelBias
  return accelBias

end NavEKF3

namespace NavEKF3

/-- C++ `bool NavEKF3::getVariances(float & velVar, float & posVar, float & hgtVar, Vector3f & magVar, float & tasVar, Vector2f & offset) const`, `AP_NavEKF3/AP_NavEKF3.cpp:1561-1568`. -/
def getVariances (s : State) (w : World) (velVar : Binary32) (posVar : Binary32) (hgtVar : Binary32) (magVar : Vector3f.State) (tasVar : Binary32) (offset : Vector2f.State) : Binary32 × Binary32 × Binary32 × Vector3f.State × Binary32 × Vector2f.State × Bool := Id.run do
  let mut velVar := velVar
  let mut posVar := posVar
  let mut hgtVar := hgtVar
  let mut magVar := magVar
  let mut tasVar := tasVar
  let mut offset := offset
  if s.core == WPtr.null then
    return (velVar, posVar, hgtVar, magVar, tasVar, offset, false)
  let (t'1, t'2, t'3, t'4, t'5, t'6, t'7) := NavEKF3_core.getVariances w.heap'NavEKF3_core[((WPtr.index s.core) + (UInt8.toNat s.primary))]! velVar posVar hgtVar magVar tasVar offset
  velVar := t'1
  posVar := t'2
  hgtVar := t'3
  magVar := t'4
  tasVar := t'5
  offset := t'6
  return (velVar, posVar, hgtVar, magVar, tasVar, offset, t'7)

end NavEKF3

namespace NavEKF3

/-- C++ `void NavEKF3::getFilterStatus(nav_filter_status & status) const`, `AP_NavEKF3/AP_NavEKF3.cpp:1837-1844`. -/
def getFilterStatus (s : State) (w : World) (status : UInt32) : UInt32 := Id.run do
  let mut status := status
  if (s.core != WPtr.null) then
    status := NavEKF3_core.getFilterStatus w.heap'NavEKF3_core[((WPtr.index s.core) + (UInt8.toNat s.primary))]! status
  else
    status := (0 : UInt32)
  return status

/-- C++ `void NavEKF3::getFilterFaults(uint16_t & faults) const`, `AP_NavEKF3/AP_NavEKF3.cpp:1825-1832`. -/
def getFilterFaults (s : State) (w : World) (faults : UInt16) : UInt16 := Id.run do
  let mut faults := faults
  if (s.core != WPtr.null) then
    faults := NavEKF3_core.getFilterFaults w.heap'NavEKF3_core[((WPtr.index s.core) + (UInt8.toNat s.primary))]! faults
  else
    faults := Int16.toUInt16 (Int32.toInt16 (0 : Int32))
  return faults

end NavEKF3

namespace NavEKF3_core

/-- C++ `bool NavEKF3_core::getGPSLLH(Location & loc) const`, `AP_NavEKF3/AP_NavEKF3_Outputs.cpp:363-371`. -/
def getGPSLLH (s : State) (w : World) (loc : Location.State) : Location.State × Bool := Id.run do
  let mut loc := loc
  if AP_GPS_FixType.toInt (AP_DAL_GPS.status_uint8_t w.heap'AP_DAL[(WPtr.index w.AP_DAL'_singleton)]!._gps s.selected_gps) ≥ AP_GPS_FixType.toInt AP_GPS_FixType.FIX_3D then
    loc := AP_DAL_GPS.location_uint8_t w.heap'AP_DAL[(WPtr.index w.AP_DAL'_singleton)]!._gps s.selected_gps
    return (loc, true)
  return (loc, false)

/-- C++ `bool NavEKF3_core::getLLH(Location & loc) const`, `AP_NavEKF3/AP_NavEKF3_Outputs.cpp:311-361`. -/
def getLLH (s : State) (w : World) (loc : Location.State) : Location.State × Bool := Id.run do
  let mut loc := loc
  let mut origin : Location.State := Location.init_void
  let pos_from_GPS : Bool := (AP_NavEKF_Source.getPosXYSource w.EKF3.sources s.core_index == AP_NavEKF_Source.SourceXY.GPS) && !s.waitingForGpsChecks
  let (t'1, t'2) := getOriginLLH s w origin
  origin := t'1
  if t'2 then
    let mut posD : Binary64 := (Binary64.ofBits 0x0000000000000000 /- 0.0 -/)  -- uninitialized in C++; assigned before every read
    let (t'3, t'4) := getPosD_local s posD
    posD := t'3
    if t'4 && UInt32.toInt32 (NavEKF3_core.AidingMode.toInt s.PV_AidingMode) != UInt32.toInt32 (NavEKF3_core.AidingMode.toInt NavEKF3_core.AidingMode.AID_NONE) then
      loc := Location.set_alt_cm loc (Binary64.toInt32 (Int32.toBinary64 origin.alt - posD * (Binary64.ofBits 0x4059000000000000 /- 100.0 -/))) Location.AltFrame.ABSOLUTE
      if (s.filterStatus >>> 4 &&& 1 != 0) || (s.filterStatus >>> 3 &&& 1 != 0) || s.waitingForGpsChecks then
        loc := { loc with lat := s.EKF_origin.lat }
        loc := { loc with lng := s.EKF_origin.lng }
        loc := Location.offset_double2 loc (s.outputDataNew.position.x + s.posOffsetNED.x) (s.outputDataNew.position.y + s.posOffsetNED.y)
        return (loc, true)
      else
        let mut t'7 := pos_from_GPS
        if t'7 then
          let (t'5, t'6) := getGPSLLH s w loc
          loc := t'5
          t'7 := t'6
        if t'7 then
          return (loc, true)
        else
          loc := { loc with lat := s.EKF_origin.lat }
          loc := { loc with lng := s.EKF_origin.lng }
          loc := Location.offset_double2 loc (s.outputDataNew.position.x + s.posOffsetNED.x) (s.outputDataNew.position.y + s.posOffsetNED.y)
          return (loc, false)
    else
      let mut t'10 := pos_from_GPS
      if t'10 then
        let (t'8, t'9) := getGPSLLH s w loc
        loc := t'8
        t'10 := t'9
      if t'10 then
        return (loc, true)
      else
        loc := { loc with lat := s.EKF_origin.lat }
        loc := { loc with lng := s.EKF_origin.lng }
        loc := Location.offset_double2 loc (s.lastKnownPositionNE.x + s.posOffsetNED.x) (s.lastKnownPositionNE.y + s.posOffsetNED.y)
        loc := { loc with alt := Binary32.toInt32 (Int32.toBinary32 s.EKF_origin.alt - s.lastKnownPositionD * (Binary32.ofBits 0x42c80000 /- 100.0 -/)) }
        return (loc, false)
  else
    let mut t'13 := pos_from_GPS
    if t'13 then
      let (t'11, t'12) := getGPSLLH s w loc
      loc := t'11
      t'13 := t'12
    return (loc, t'13)

end NavEKF3_core

namespace NavEKF3

/-- C++ `bool NavEKF3::getLLH(Location & loc) const`, `AP_NavEKF3/AP_NavEKF3.cpp:1437-1443`. -/
def getLLH (s : State) (w : World) (loc : Location.State) : World × Location.State × Bool := Id.run do
  let mut w := w
  let mut loc := loc
  if !(s.core != WPtr.null) then
    return (w, loc, false)
  w := { w with EKF3 := s }  -- this object's state into the World: the call reaches it
  let (t'1, t'2) := NavEKF3_core.getLLH w.heap'NavEKF3_core[((WPtr.index s.core) + (UInt8.toNat s.primary))]! w loc
  loc := t'1
  return (w, loc, t'2)

end NavEKF3

namespace NavEKF3

/-- C++ `bool NavEKF3::getHAGL(float & HAGL) const`, `AP_NavEKF3/AP_NavEKF3.cpp:1507-1513`. -/
def getHAGL (s : State) (w : World) (HAGL : Binary32) : Binary32 × Bool := Id.run do
  let mut HAGL := HAGL
  if !(s.core != WPtr.null) then
    return (HAGL, false)
  let (t'1, t'2) := NavEKF3_core.getHAGL w.heap'NavEKF3_core[((WPtr.index s.core) + (UInt8.toNat s.primary))]! HAGL
  HAGL := t'1
  return (HAGL, t'2)

end NavEKF3

namespace NavEKF3

/-- C++ `bool NavEKF3::getWind(Vector3f & wind) const`, `AP_NavEKF3/AP_NavEKF3.cpp:1380-1386`. -/
def getWind (s : State) (w : World) (wind : Vector3f.State) : Vector3f.State × Bool := Id.run do
  let mut wind := wind
  if s.core == WPtr.null then
    return (wind, false)
  let (t'1, t'2) := NavEKF3_core.getWind w.heap'NavEKF3_core[((WPtr.index s.core) + (UInt8.toNat s.primary))]! wind
  wind := t'1
  return (wind, t'2)

end NavEKF3

namespace NavEKF3_core

/-- C++ `bool NavEKF3_core::getHeightControlLimit(float & height) const`, `AP_NavEKF3/AP_NavEKF3_Outputs.cpp:93-124`. -/
def getHeightControlLimit (s : State) (w : World) (height : Binary32) : Binary32 × Bool := Id.run do
  let mut height := height
  if AP_NavEKF_Source.useVelXYSource w.EKF3.sources AP_NavEKF_Source.SourceXY.OPTFLOW s.core_index && (UInt32.toInt32 (NavEKF3_core.AidingMode.toInt s.PV_AidingMode) == UInt32.toInt32 (NavEKF3_core.AidingMode.toInt NavEKF3_core.AidingMode.AID_RELATIVE)) && s.flowDataValid then
    return (height, false)
  else
    return (height, false)

end NavEKF3_core

namespace NavEKF3

/-- C++ `bool NavEKF3::getHeightControlLimit(float & height) const`, `AP_NavEKF3/AP_NavEKF3.cpp:1858-1864`. -/
def getHeightControlLimit (s : State) (w : World) (height : Binary32) : World × Binary32 × Bool := Id.run do
  let mut w := w
  let mut height := height
  if !(s.core != WPtr.null) then
    return (w, height, false)
  w := { w with EKF3 := s }  -- this object's state into the World: the call reaches it
  let (t'1, t'2) := NavEKF3_core.getHeightControlLimit w.heap'NavEKF3_core[((WPtr.index s.core) + (UInt8.toNat s.primary))]! w height
  height := t'1
  return (w, height, t'2)

end NavEKF3

namespace NavEKF3_core

/-- C++ `void NavEKF3_core::getEkfControlLimits(float & ekfGndSpdLimit, float & ekfNavVelGainScaler) const`, `AP_NavEKF3/AP_NavEKF3_Outputs.cpp:375-393`. -/
def getEkfControlLimits (s : State) (w : World) (ekfGndSpdLimit : Binary32) (ekfNavVelGainScaler : Binary32) : Binary32 × Binary32 := Id.run do
  let mut ekfGndSpdLimit := ekfGndSpdLimit
  let mut ekfNavVelGainScaler := ekfNavVelGainScaler
  let relyingOnFlowData : Bool := (decide (s.imuSampleTime_ms - s.bodyOdm.prevFuseTime_ms > Int32.toUInt32 (1000 : Int32))) && (decide (s.imuSampleTime_ms - s.flowValidMeaTime_ms ≤ Int32.toUInt32 (10000 : Int32)))
  if UInt32.toInt32 (NavEKF3_core.AidingMode.toInt s.PV_AidingMode) == UInt32.toInt32 (NavEKF3_core.AidingMode.toInt NavEKF3_core.AidingMode.AID_RELATIVE) && relyingOnFlowData then
    ekfGndSpdLimit := Binary64.toBinary32 (Binary32.toBinary64 (Estimator_lib.MAX_float2 (AP_ParamT_float_4.op_to_float w.EKF3._maxFlowRate - (Binary32.ofBits 0x3f800000 /- 1.0f -/)) (Binary32.ofBits 0x00000000 /- 0.0f -/)) * Estimator_lib.MAX_double2 (s.terrainState - s.statesArray[9]!) s.rngOnGnd)
    let gainHgt : Binary64 := Binary32.toBinary64 (Estimator_lib.MAX_float2 (AP_ParamT_float_4.get_void w.EKF3._flowNavGainHgt) (Binary32.ofBits 0x3f800000 /- 1.0f -/))
    ekfNavVelGainScaler := Binary64.toBinary32 (gainHgt / Estimator_lib.MAX_double2 (s.terrainState - s.statesArray[9]!) gainHgt)
  else
    ekfGndSpdLimit := (Binary32.ofBits 0x43c80000 /- 400.0f -/)
    ekfNavVelGainScaler := (Binary32.ofBits 0x3f800000 /- 1.0f -/)
  return (ekfGndSpdLimit, ekfNavVelGainScaler)

end NavEKF3_core

namespace NavEKF3

/-- C++ `void NavEKF3::getEkfControlLimits(float & ekfGndSpdLimit, float & ekfNavVelGainScaler) const`, `AP_NavEKF3/AP_NavEKF3.cpp:1368-1376`. -/
def getEkfControlLimits (s : State) (w : World) (ekfGndSpdLimit : Binary32) (ekfNavVelGainScaler : Binary32) : World × Binary32 × Binary32 := Id.run do
  let mut w := w
  let mut ekfGndSpdLimit := ekfGndSpdLimit
  let mut ekfNavVelGainScaler := ekfNavVelGainScaler
  if (s.core != WPtr.null) then
    w := { w with EKF3 := s }  -- this object's state into the World: the call reaches it
    let (t'1, t'2) := NavEKF3_core.getEkfControlLimits w.heap'NavEKF3_core[((WPtr.index s.core) + (UInt8.toNat s.primary))]! w ekfGndSpdLimit ekfNavVelGainScaler
    ekfGndSpdLimit := t'1
    ekfNavVelGainScaler := t'2
  else
    ekfGndSpdLimit := (Binary32.ofBits 0x43c80000 /- 400.0f -/)
    ekfNavVelGainScaler := (Binary32.ofBits 0x3f800000 /- 1.0f -/)
  return (w, ekfGndSpdLimit, ekfNavVelGainScaler)

end NavEKF3

namespace NavEKF3_core

/-- C++ `bool NavEKF3_core::getTerrainAltVariance(float & terrain_alt_variance) const`, `AP_NavEKF3/AP_NavEKF3_Outputs.cpp:590-603`. -/
def getTerrainAltVariance (s : State) (w : World) (temp : Binary32) : Binary32 × Bool := Id.run do
  let mut temp := temp
  if ((decide (Int8.toInt32 (AP_ParamT_signed_char_1.op_to_signed_char w.EKF3._useRngSwHgt) > (0 : Int32))) && s.activeHgtSource == AP_NavEKF_Source.SourceZ.RANGEFINDER) || (UInt32.toInt32 (NavEKF3_core.AidingMode.toInt s.PV_AidingMode) == UInt32.toInt32 (NavEKF3_core.AidingMode.toInt NavEKF3_core.AidingMode.AID_RELATIVE) && s.flowDataValid) then
    temp := Binary64.toBinary32 (Binary64.sqrt s.auxRngTestRatio)
  else
    temp := (Binary32.ofBits 0x00000000 /- 0 -/)
  return (temp, true)

end NavEKF3_core

namespace NavEKF3

/-- C++ `bool NavEKF3::getTerrainAltVariance(float & terrain_alt_variance) const`, `AP_NavEKF3/AP_NavEKF3.cpp:1847-1853`. -/
def getTerrainAltVariance (s : State) (w : World) (terrainAltVar : Binary32) : World × Binary32 × Bool := Id.run do
  let mut w := w
  let mut terrainAltVar := terrainAltVar
  if (s.core != WPtr.null) then
    w := { w with EKF3 := s }  -- this object's state into the World: the call reaches it
    let (t'1, t'2) := NavEKF3_core.getTerrainAltVariance w.heap'NavEKF3_core[((WPtr.index s.core) + (UInt8.toNat s.primary))]! w terrainAltVar
    terrainAltVar := t'1
    return (w, terrainAltVar, t'2)
  return (w, terrainAltVar, false)

end NavEKF3

namespace NavEKF3

/-- C++ `bool NavEKF3::isVibrationAffected() const`, `AP_NavEKF3/AP_NavEKF3.cpp:1970-1976`. -/
def isVibrationAffected (s : State) (w : World) : Bool := Id.run do
  if (s.core != WPtr.null) then
    return NavEKF3_core.isVibrationAffected w.heap'NavEKF3_core[((WPtr.index s.core) + (UInt8.toNat s.primary))]!
  return false

end NavEKF3

namespace NavEKF3

/-- C++ `bool NavEKF3::using_extnav_for_yaw() const`, `AP_NavEKF3/AP_NavEKF3.cpp:1609-1615`. -/
def using_extnav_for_yaw (s : State) (w : World) : Bool := Id.run do
  if !(s.core != WPtr.null) then
    return false
  return NavEKF3_core.using_extnav_for_yaw

end NavEKF3

namespace NavEKF3

/-- C++ `void NavEKF3::setTerrainHgtStable(bool val)`, `AP_NavEKF3/AP_NavEKF3.cpp:1798-1812`. -/
def setTerrainHgtStable (s : State) (w : World) (val : Bool) : World := Id.run do
  let mut w := w
  if val then
    let t'1 := w.heap'AP_DAL[(WPtr.index w.AP_DAL'_singleton)]!  -- the object out of its slot for the call (--swap-out)
    w := { w with heap'AP_DAL := w.heap'AP_DAL.set! (WPtr.index w.AP_DAL'_singleton) default }
    w := { w with heap'AP_DAL := w.heap'AP_DAL.set! (WPtr.index w.AP_DAL'_singleton) (AP_DAL.log_event3 t'1 AP_DAL.Event.setTerrainHgtStable) }
  else
    let t'2 := w.heap'AP_DAL[(WPtr.index w.AP_DAL'_singleton)]!  -- the object out of its slot for the call (--swap-out)
    w := { w with heap'AP_DAL := w.heap'AP_DAL.set! (WPtr.index w.AP_DAL'_singleton) default }
    w := { w with heap'AP_DAL := w.heap'AP_DAL.set! (WPtr.index w.AP_DAL'_singleton) (AP_DAL.log_event3 t'2 AP_DAL.Event.unsetTerrainHgtStable) }
  if (s.core != WPtr.null) then
    let t'3 : UInt8 := Int8.toUInt8 (Int32.toInt8 (0 : Int32))
    let t'4 : Int32 := UInt32.toInt32 (UInt8.toUInt32 s.num_cores)
    for i' in [0:(t'4.toInt - (Int.ofNat t'3.toNat)).toNat] do  -- C++ loop bounded by a runtime value (--runtime-loops)
      let i : UInt8 := t'3 + Nat.toUInt8 i'
      let t'5 := w.heap'NavEKF3_core[((WPtr.index s.core) + (UInt8.toNat i))]!  -- the object out of its slot for the call (--swap-out)
      w := { w with heap'NavEKF3_core := w.heap'NavEKF3_core.set! ((WPtr.index s.core) + (UInt8.toNat i)) default }
      w := { w with heap'NavEKF3_core := w.heap'NavEKF3_core.set! ((WPtr.index s.core) + (UInt8.toNat i)) (NavEKF3_core.setTerrainHgtStable t'5 val) }
  return w

end NavEKF3

namespace NavEKF3

/-- C++ `void NavEKF3::requestYawReset()`, `AP_NavEKF3/AP_NavEKF3.cpp:1108-1115`. -/
def requestYawReset (s : State) (w : World) : World := Id.run do
  let mut w := w
  let t'1 := w.heap'AP_DAL[(WPtr.index w.AP_DAL'_singleton)]!  -- the object out of its slot for the call (--swap-out)
  w := { w with heap'AP_DAL := w.heap'AP_DAL.set! (WPtr.index w.AP_DAL'_singleton) default }
  w := { w with heap'AP_DAL := w.heap'AP_DAL.set! (WPtr.index w.AP_DAL'_singleton) (AP_DAL.log_event3 t'1 AP_DAL.Event.requestYawReset) }
  let t'2 : UInt8 := Int8.toUInt8 (Int32.toInt8 (0 : Int32))
  let t'3 : Int32 := UInt32.toInt32 (UInt8.toUInt32 s.num_cores)
  for i' in [0:(t'3.toInt - (Int.ofNat t'2.toNat)).toNat] do  -- C++ loop bounded by a runtime value (--runtime-loops)
    let i : UInt8 := t'2 + Nat.toUInt8 i'
    let t'4 := w.heap'NavEKF3_core[((WPtr.index s.core) + (UInt8.toNat i))]!  -- the object out of its slot for the call (--swap-out)
    w := { w with heap'NavEKF3_core := w.heap'NavEKF3_core.set! ((WPtr.index s.core) + (UInt8.toNat i)) default }
    w := { w with heap'NavEKF3_core := w.heap'NavEKF3_core.set! ((WPtr.index s.core) + (UInt8.toNat i)) (NavEKF3_core.EKFGSF_requestYawReset t'4) }
  return w

end NavEKF3

namespace NavEKF3

/-- C++ `bool NavEKF3::getInnovations(Vector3f & velInnov, Vector3f & posInnov, Vector3f & magInnov, float & tasInnov, float & yawInnov) const`, `AP_NavEKF3/AP_NavEKF3.cpp:1551-1558`. -/
def getInnovations (s : State) (w : World) (velInnov : Vector3f.State) (posInnov : Vector3f.State) (magInnov : Vector3f.State) (tasInnov : Binary32) (yawInnov : Binary32) : Vector3f.State × Vector3f.State × Vector3f.State × Binary32 × Binary32 × Bool := Id.run do
  let mut velInnov := velInnov
  let mut posInnov := posInnov
  let mut magInnov := magInnov
  let mut tasInnov := tasInnov
  let mut yawInnov := yawInnov
  if s.core == WPtr.null then
    return (velInnov, posInnov, magInnov, tasInnov, yawInnov, false)
  let (t'1, t'2, t'3, t'4, t'5, t'6) := NavEKF3_core.getInnovations w.heap'NavEKF3_core[((WPtr.index s.core) + (UInt8.toNat s.primary))]! velInnov posInnov magInnov tasInnov yawInnov
  velInnov := t'1
  posInnov := t'2
  magInnov := t'3
  tasInnov := t'4
  yawInnov := t'5
  return (velInnov, posInnov, magInnov, tasInnov, yawInnov, t'6)

end NavEKF3

namespace NavEKF3

/-- C++ `void NavEKF3::setPosVelYawSourceSet(uint8_t source_set_idx)`, `AP_NavEKF3/AP_NavEKF3.cpp:1157-1163`. -/
def setPosVelYawSourceSet (s : State) (w : World) (source_set_idx : UInt8) : State × World := Id.run do
  let mut s := s
  let mut w := w
  if UInt32.toInt32 (UInt8.toUInt32 source_set_idx) < (3 : Int32) then
    let t'1 := w.heap'AP_DAL[(WPtr.index w.AP_DAL'_singleton)]!  -- the object out of its slot for the call (--swap-out)
    w := { w with heap'AP_DAL := w.heap'AP_DAL.set! (WPtr.index w.AP_DAL'_singleton) default }
    w := { w with heap'AP_DAL := w.heap'AP_DAL.set! (WPtr.index w.AP_DAL'_singleton) (AP_DAL.log_event3 t'1 (AP_DAL.Event.ofInt (Int8.toUInt8 (Int32.toInt8 (UInt32.toInt32 (UInt8.toUInt32 (AP_DAL.Event.toInt AP_DAL.Event.setSourceSet0)) + UInt32.toInt32 (UInt8.toUInt32 source_set_idx)))))) }
  s := { s with sources := AP_NavEKF_Source.setPosVelYawSourceSet s.sources (AP_NavEKF_Source.SourceSetSelection.ofInt source_set_idx) }
  return (s, w)

end NavEKF3

namespace NavEKF3

/-- C++ `bool NavEKF3::use_compass() const`, `AP_NavEKF3/AP_NavEKF3.cpp:1591-1597`. -/
def use_compass (s : State) (w : World) : Bool := Id.run do
  if !(s.core != WPtr.null) then
    return false
  return NavEKF3_core.use_compass w.heap'NavEKF3_core[((WPtr.index s.core) + (UInt8.toNat s.primary))]! w

end NavEKF3

namespace NavEKF3

/-- C++ `bool NavEKF3::getPosVelUncertainty(float & pos_horiz_m, float & pos_vert_m, float & vel_m_s) const`, `AP_NavEKF3/AP_NavEKF3.cpp:1571-1577`. -/
def getPosVelUncertainty (s : State) (w : World) (pos_horiz_m : Binary32) (pos_vert_m : Binary32) (vel_m_s : Binary32) : Binary32 × Binary32 × Binary32 × Bool := Id.run do
  let mut pos_horiz_m := pos_horiz_m
  let mut pos_vert_m := pos_vert_m
  let mut vel_m_s := vel_m_s
  if s.core == WPtr.null then
    return (pos_horiz_m, pos_vert_m, vel_m_s, false)
  let (t'1, t'2, t'3, t'4) := NavEKF3_core.getPosVelUncertainty w.heap'NavEKF3_core[((WPtr.index s.core) + (UInt8.toNat s.primary))]! pos_horiz_m pos_vert_m vel_m_s
  pos_horiz_m := t'1
  pos_vert_m := t'2
  vel_m_s := t'3
  return (pos_horiz_m, pos_vert_m, vel_m_s, t'4)

end NavEKF3

namespace NavEKF3

/-- C++ `uint8_t NavEKF3::activeCores() const`, `AP_NavEKF3/AP_NavEKF3.h:44-46`. -/
def activeCores (s : State) : UInt8 := Id.run do
  return s.num_cores

/-- C++ `void NavEKF3::getQuaternionBodyToNED(int8_t instance, Quaternion & quat) const`, `AP_NavEKF3/AP_NavEKF3.cpp:1532-1540`. -/
def getQuaternionBodyToNED (s : State) (w : World) («instance» : Int8) (quat : Quaternion.State) : Quaternion.State := Id.run do
  let mut «instance» := «instance»
  let mut quat := quat
  if decide (Int8.toInt32 «instance» < (0 : Int32)) || decide (Int8.toInt32 «instance» ≥ UInt32.toInt32 (UInt8.toUInt32 s.num_cores)) then
    «instance» := UInt8.toInt8 s.primary
  if (s.core != WPtr.null) then
    let mut mat : Matrix3f.State := Matrix3f.init_void
    mat := NavEKF3_core.getRotationBodyToNED w.heap'NavEKF3_core[((WPtr.index s.core) + (Int8.toNatClampNeg «instance»))]! w mat
    quat := Quaternion.from_rotation_matrix quat mat
  return quat

end NavEKF3

namespace NavEKF3_core

/-- C++ `const char * NavEKF3_core::prearm_failure_reason() const`, `AP_NavEKF3/AP_NavEKF3_Outputs.cpp:606-613`. -/
def prearm_failure_reason (s : State) : CText := Id.run do
  if s.gpsGoodToAlign then
    return CText.null
  return s.prearm_fail_string

/-- C++ `bool NavEKF3_core::pre_arm_check(bool requires_position, char * failure_msg, uint8_t failure_msg_len) const`, `AP_NavEKF3/AP_NavEKF3_Outputs.cpp:42-60`. -/
def pre_arm_check (s : State) (w : World) (requires_position : Bool) (failure_msg : CText) (failure_msg_len : UInt8) : CText × Bool := Id.run do
  let mut failure_msg := failure_msg
  if requires_position then
    let max_vel_innovation : Binary32 := (Binary32.ofBits 0x40000000 /- 2.0 -/)
    let hvel_innovation : Binary32 := Binary32.sqrt (Binary64.toBinary32 (Estimator_lib.sq_double s.innovVelPos[0]! + Estimator_lib.sq_double s.innovVelPos[1]!))
    if s.onGround && UInt32.toInt32 (NavEKF3_core.AidingMode.toInt s.PV_AidingMode) == UInt32.toInt32 (NavEKF3_core.AidingMode.toInt NavEKF3_core.AidingMode.AID_ABSOLUTE) && AP_NavEKF_Source.useVelXYSource w.EKF3.sources AP_NavEKF_Source.SourceXY.GPS s.core_index && decide (hvel_innovation > max_vel_innovation) then
      failure_msg := (CText.fmt (UInt8.toUInt64 failure_msg_len) "EKF3[%u] vel error %.1f" #[Sum.inl (UInt32.toUInt64 (UInt8.toUInt32 s.core_index + Int32.toUInt32 (1 : Int32))), Sum.inl (Binary64.toBits (Binary32.toBinary64 hvel_innovation))])
      return (failure_msg, false)
  return (failure_msg, true)

end NavEKF3_core

namespace NavEKF3

/-- C++ `void NavEKF3::getMagNED(Vector3f & magNED) const`, `AP_NavEKF3/AP_NavEKF3.cpp:1389-1394`. -/
def getMagNED (s : State) (w : World) (magNED : Vector3f.State) : Vector3f.State := Id.run do
  let mut magNED := magNED
  if (s.core != WPtr.null) then
    magNED := NavEKF3_core.getMagNED w.heap'NavEKF3_core[((WPtr.index s.core) + (UInt8.toNat s.primary))]! magNED
  return magNED

end NavEKF3

namespace NavEKF3

/-- C++ `void NavEKF3::getMagXYZ(Vector3f & magXYZ) const`, `AP_NavEKF3/AP_NavEKF3.cpp:1397-1402`. -/
def getMagXYZ (s : State) (w : World) (magXYZ : Vector3f.State) : Vector3f.State := Id.run do
  let mut magXYZ := magXYZ
  if (s.core != WPtr.null) then
    magXYZ := NavEKF3_core.getMagXYZ w.heap'NavEKF3_core[((WPtr.index s.core) + (UInt8.toNat s.primary))]! magXYZ
  return magXYZ

end NavEKF3

namespace NavEKF3_core

/-- C++ `bool NavEKF3_core::getMagOffsets(uint8_t mag_idx, Vector3f & magOffsets) const`, `AP_NavEKF3/AP_NavEKF3_Outputs.cpp:423-445`. -/
def getMagOffsets (s : State) (w : World) (mag_idx : UInt8) (magOffsets : Vector3f.State) : Vector3f.State × Bool := Id.run do
  let mut magOffsets := magOffsets
  if !(AP_DAL_Compass.available w.heap'AP_DAL[(WPtr.index w.AP_DAL'_singleton)]!._compass) then
    return (magOffsets, false)
  let maxMagVar : Binary32 := (Binary32.ofBits 0x36a7c5ac /- 5E-6f -/)
  let variancesConverged : Bool := (decide (s.Pmut[475]! < Binary32.toBinary64 maxMagVar)) && (decide (s.Pmut[500]! < Binary32.toBinary64 maxMagVar)) && (decide (s.Pmut[525]! < Binary32.toBinary64 maxMagVar))
  if (UInt32.toInt32 (UInt8.toUInt32 mag_idx) == UInt32.toInt32 (UInt8.toUInt32 s.magSelectIndex)) && s.finalInflightMagInit && !s.inhibitMagStates && AP_DAL_Compass.healthy w.heap'AP_DAL[(WPtr.index w.AP_DAL'_singleton)]!._compass s.magSelectIndex && variancesConverged then
    let t'1 := s.magSelectIndex
    magOffsets := Vector3f.op_sub_Vector3f w.heap'AP_DAL[(WPtr.index w.AP_DAL'_singleton)]!._compass._RMGI[UInt8.toNat t'1]!.offsets (Vector3f.op_mul_float (Vector3p.tofloat ({ x := s.statesArray[19]!, y := s.statesArray[20]!, z := s.statesArray[21]! } : Vector3p.State)) (Binary32.ofBits 0x447a0000 /- 1000.0 -/))
    return (magOffsets, true)
  else
    magOffsets := AP_DAL_Compass.get_offsets w.heap'AP_DAL[(WPtr.index w.AP_DAL'_singleton)]!._compass s.magSelectIndex
    return (magOffsets, false)

end NavEKF3_core

namespace NavEKF3

/-- C++ `bool NavEKF3::getMagOffsets(uint8_t mag_idx, Vector3f & magOffsets) const`, `AP_NavEKF3/AP_NavEKF3.cpp:1416-1431`. -/
def getMagOffsets (s : State) (w : World) (mag_idx : UInt8) (magOffsets : Vector3f.State) : Vector3f.State × Bool := Id.run do
  let mut magOffsets := magOffsets
  if !(s.core != WPtr.null) then
    return (magOffsets, false)
  let (t'1, t'2) := NavEKF3_core.getMagOffsets w.heap'NavEKF3_core[((WPtr.index s.core) + (UInt8.toNat s.primary))]! w mag_idx magOffsets
  magOffsets := t'1
  if t'2 then
    return (magOffsets, true)
  for i' in [0:s.num_cores.toNat] do
    let i : UInt8 := Nat.toUInt8 i'
    let (t'3, t'4) := NavEKF3_core.getMagOffsets w.heap'NavEKF3_core[((WPtr.index s.core) + (UInt8.toNat i))]! w mag_idx magOffsets
    magOffsets := t'3
    if t'4 then
      return (magOffsets, true)
  return (magOffsets, false)

end NavEKF3

namespace NavEKF3

/-- C++ `uint8_t NavEKF3::getActiveAirspeed() const`, `AP_NavEKF3/AP_NavEKF3.cpp:1405-1412`. -/
def getActiveAirspeed (s : State) (w : World) : UInt8 := Id.run do
  if (s.core != WPtr.null) then
    return NavEKF3_core.getActiveAirspeed w.heap'NavEKF3_core[((WPtr.index s.core) + (UInt8.toNat s.primary))]!
  else
    return Int8.toUInt8 (Int32.toInt8 (255 : Int32))

end NavEKF3

end Estimator_lib
