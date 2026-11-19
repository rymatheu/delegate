import ArduLean.Musl.asin
import ArduLean.Musl.atan2
import ArduLean.Musl.cos
import ArduLean.Musl.sin
import ArduLean.Estimator.mavlink.mavlink
import ArduLean.Estimator.libraries.AP_Math.AP_Math
import ArduLean.Estimator.World
import ArduLean.Estimator.libraries.AP_Common.AP_Common
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
import ArduLean.Estimator.libraries.AP_NavEKF3.AP_NavEKF3_3
import ArduLean.Estimator.libraries.AP_DAL.AP_DAL_2
import ArduLean.Estimator.libraries.AP_NavEKF.AP_NavEKF_3

/-!
ArduPilot `libraries/AP_NavEKF3`, part 4 of 4. Sources: `libraries/AP_NavEKF3/AP_NavEKF3_core.cpp`, `libraries/AP_NavEKF3/AP_NavEKF3.cpp`, `libraries/AP_NavEKF3/AP_NavEKF3_PosVelFusion.cpp`, `libraries/AP_NavEKF3/AP_NavEKF3_Measurements.cpp`, `libraries/AP_NavEKF3/AP_NavEKF3_Control.cpp`, `libraries/AP_NavEKF3/AP_NavEKF3_MagFusion.cpp`, `libraries/AP_NavEKF3/AP_NavEKF3_GyroBias.cpp`, `libraries/AP_NavEKF3/AP_NavEKF3_Outputs.cpp`.

Items of `lean/Estimator_lib.lean` (the estimator translation), unchanged; placed by `tools/split_modules.py` (`ArduLean/Estimator/INDEX.md`).
-/

open FloatLib.Floats (Binary32 Binary64)

set_option maxRecDepth 200000
-- AP_DAL's `const log_RISH old_RISH = _RISH;` read only by WRITE_REPLAY_BLOCK_IFCHANGED, which is `(void)old`
-- without logging (HAL_LOGGING_ENABLED 0): an unused binding, as in the C++
set_option linter.unusedVariables false

namespace Estimator_lib

namespace NavEKF3_core

/-- C++ `bool NavEKF3_core::resetHeightDatum()`, `AP_NavEKF3/AP_NavEKF3_PosVelFusion.cpp:350-408`. -/
def resetHeightDatum (s : State) (w : World) (o : Outputs) : State × World × Outputs × Bool := Id.run do
  let mut s := s
  let mut w := w
  let mut o := o
  if s.activeHgtSource == AP_NavEKF_Source.SourceZ.RANGEFINDER || !s.onGround then
    return (s, w, o, false)
  let oldHgt : Binary64 := -s.statesArray[9]!
  let (t'1, t'2) := AP_DAL_Baro.update_calibration w o
  w := t'1
  o := t'2
  s := { s with storedBaro := EKF_obs_buffer_t_NavEKF3_core_baro_elements.reset s.storedBaro }
  s := { s with statesArray := s.statesArray.set! 9 (Binary64.ofBits 0x0000000000000000 /- 0.0f -/) }
  s := { s with statesArray := s.statesArray.set! 6 (Binary64.ofBits 0x0000000000000000 /- 0.0f -/) }
  let t'3 : UInt8 := Int8.toUInt8 (Int32.toInt8 (0 : Int32))
  let t'4 : Int32 := UInt32.toInt32 (UInt8.toUInt32 s.imu_buffer_length)
  for i' in [0:(t'4.toInt - (Int.ofNat t'3.toNat)).toNat] do  -- C++ loop bounded by a runtime value (--runtime-loops)
    let i : UInt8 := t'3 + Nat.toUInt8 i'
    s := { s with storedOutput.buffer := s.storedOutput.buffer.set! (UInt8.toNat (UInt32.toUInt8 (UInt8.toUInt32 i))) ({ s.storedOutput.buffer[UInt8.toNat (UInt32.toUInt8 (UInt8.toUInt32 i))]! with position.z := s.statesArray[9]! }) }
    s := { s with storedOutput.buffer := s.storedOutput.buffer.set! (UInt8.toNat (UInt32.toUInt8 (UInt8.toUInt32 i))) ({ s.storedOutput.buffer[UInt8.toNat (UInt32.toUInt8 (UInt8.toUInt32 i))]! with velocity.z := s.statesArray[6]! }) }
  s := { s with outputDataDelayed.position.z := s.statesArray[9]! }
  s := { s with outputDataNew.position.z := s.outputDataDelayed.position.z }
  s := { s with outputDataDelayed.velocity.z := s.statesArray[6]! }
  s := { s with outputDataNew.velocity.z := s.outputDataDelayed.velocity.z }
  s := { s with vertCompFiltState.vel := s.outputDataNew.velocity.z }
  s := { s with baroHgtOffset := (Binary64.ofBits 0x0000000000000000 /- 0.0f -/) }
  if s.validOrigin then
    if !s.gpsGoodToAlign then
      s := { s with EKF_origin.alt := s.EKF_origin.alt + Binary64.toInt32 ((Binary64.ofBits 0x4059000000000000 /- 100.0f -/) * oldHgt) }
    else
      s := { s with EKF_origin := Location.copy_alt_from s.EKF_origin (AP_DAL_GPS.location_void w.heap'AP_DAL[(WPtr.index w.AP_DAL'_singleton)]!._gps) }
    s := { s with ekfGpsRefHgt := (Binary64.ofBits 0x3f847ae147ae147b /- 0.01 -/) * Int32.toBinary64 s.EKF_origin.alt }
  s := { s with terrainState := (Binary64.ofBits 0x0000000000000000 /- 0 -/) }
  return (s, w, o, true)

end NavEKF3_core

namespace NavEKF3

/-- C++ `bool NavEKF3::resetHeightDatum()`, `AP_NavEKF3/AP_NavEKF3.cpp:1349-1364`. -/
def resetHeightDatum (s : State) (w : World) (o : Outputs) : World × Outputs × Bool := Id.run do
  let mut w := w
  let mut o := o
  let t'1 := w.heap'AP_DAL[(WPtr.index w.AP_DAL'_singleton)]!  -- the object out of its slot for the call (--swap-out)
  w := { w with heap'AP_DAL := w.heap'AP_DAL.set! (WPtr.index w.AP_DAL'_singleton) default }
  w := { w with heap'AP_DAL := w.heap'AP_DAL.set! (WPtr.index w.AP_DAL'_singleton) (AP_DAL.log_event3 t'1 AP_DAL.Event.resetHeightDatum) }
  let mut status : Bool := true
  if (s.core != WPtr.null) then
    let t'2 : UInt8 := Int8.toUInt8 (Int32.toInt8 (0 : Int32))
    let t'3 : Int32 := UInt32.toInt32 (UInt8.toUInt32 s.num_cores)
    for i' in [0:(t'3.toInt - (Int.ofNat t'2.toNat)).toNat] do  -- C++ loop bounded by a runtime value (--runtime-loops)
      let i : UInt8 := t'2 + Nat.toUInt8 i'
      let t'4 := w.heap'NavEKF3_core[((WPtr.index s.core) + (UInt8.toNat i))]!  -- the object out of its slot for the call (--swap-out)
      w := { w with heap'NavEKF3_core := w.heap'NavEKF3_core.set! ((WPtr.index s.core) + (UInt8.toNat i)) default }
      let (t'5, t'6, t'7, t'8) := NavEKF3_core.resetHeightDatum t'4 w o
      w := t'6
      w := { w with heap'NavEKF3_core := w.heap'NavEKF3_core.set! ((WPtr.index s.core) + (UInt8.toNat i)) t'5 }
      o := t'7
      if !t'8 then
        status := false
  else
    status := false
  return (w, o, status)

end NavEKF3

namespace NavEKF3_core

/-- C++ `bool NavEKF3_core::setup_core(uint8_t _imu_index, uint8_t _core_index)`, `AP_NavEKF3/AP_NavEKF3_core.cpp:23-190`. -/
def setup_core (s : State) (w : World) (o : Outputs) (_imu_index : UInt8) (_core_index : UInt8) : State × World × Outputs × Bool := Id.run do
  let mut s := s
  let mut w := w
  let mut o := o
  s := { s with imu_index := _imu_index }
  s := { s with gyro_index_active := s.imu_index }
  s := { s with accel_index_active := s.imu_index }
  s := { s with core_index := _core_index }
  if UInt32.toInt32 (UInt16.toUInt32 (AP_DAL_InertialSensor.get_loop_rate_hz w.heap'AP_DAL[(WPtr.index w.AP_DAL'_singleton)]!._ins)) > (0 : Int32) then
    s := { s with dtEkfAvg := Binary32.toBinary64 ((Binary32.ofBits 0x3f800000 /- 1.0f -/) / Int32.toBinary32 (UInt32.toInt32 (UInt16.toUInt32 (AP_DAL_InertialSensor.get_loop_rate_hz w.heap'AP_DAL[(WPtr.index w.AP_DAL'_singleton)]!._ins)))) }
    s := { s with dtEkfAvg := Estimator_lib.MAX_double_float s.dtEkfAvg (Binary32.ofBits 0x3c449ba6 /- 0.0120000001 -/) }
  else
    return (s, w, o, false)
  let mut maxTimeDelay_ms : UInt16 := Estimator_lib.MAX_AP_ParamT_short_2_uint16_t w.EKF3._hgtDelay_ms (Estimator_lib.MAX_AP_ParamT_signed_char_1_uint16_t w.EKF3._flowDelay_ms (Estimator_lib.MAX_AP_ParamT_signed_char_1_uint16_t w.EKF3._rngBcnDelay_ms (Estimator_lib.MAX_uint16_t2 w.EKF3.magDelay_ms (Int16.toUInt16 (Int32.toInt16 (12 : Int32))))))
  let (t'1, t'2) := AP_NavEKF_Source.usingGPS w.EKF3.sources w s.core_index
  w := t'1
  if t'2 then
    let mut gps_delay_sec : Binary32 := (Binary32.ofBits 0x00000000 /- 0 -/)
    let (t'3, t'4) := AP_DAL_GPS.get_lag_uint8_t_float w.heap'AP_DAL[(WPtr.index w.AP_DAL'_singleton)]!._gps s.selected_gps gps_delay_sec
    gps_delay_sec := t'3
    if !t'4 then
      let now : UInt32 := AP_DAL.millis w.heap'AP_DAL[(WPtr.index w.AP_DAL'_singleton)]!
      if now - s.lastInitFailReport_ms > Int32.toUInt32 (10000 : Int32) then
        s := { s with lastInitFailReport_ms := now }
        let mut severity : MAV_SEVERITY := MAV_SEVERITY.MAV_SEVERITY_INFO
        if now > Int32.toUInt32 (30000 : Int32) then
          severity := MAV_SEVERITY.MAV_SEVERITY_ERROR
        else if now > Int32.toUInt32 (15000 : Int32) then
          severity := MAV_SEVERITY.MAV_SEVERITY_WARNING
        o := o.push (Output.send_text (MAV_SEVERITY.toInt severity) "EKF3 waiting for GPS config data" #[])
      return (s, w, o, false)
    maxTimeDelay_ms := Int16.toUInt16 (Int32.toInt16 (Estimator_lib.MAX_uint16_t_int32_t maxTimeDelay_ms (Estimator_lib.MIN_uint16_t_int32_t (Binary32.toUInt16 (gps_delay_sec * (Binary32.ofBits 0x447a0000 /- 1000.0f -/))) (250 : Int32))))
  let airspeed : WPtr := AP_DAL.airspeed w.heap'AP_DAL[(WPtr.index w.AP_DAL'_singleton)]!
  if airspeed != WPtr.null && decide (UInt32.toInt32 (UInt8.toUInt32 (AP_DAL_Airspeed.get_num_sensors w.heap'AP_DAL_Airspeed[(WPtr.index airspeed)]!)) > (0 : Int32)) then
    maxTimeDelay_ms := Estimator_lib.MAX_uint16_t2 maxTimeDelay_ms w.EKF3.tasDelay_ms
  s := { s with imu_buffer_length := Int8.toUInt8 (Int32.toInt8 ((UInt32.toInt32 (UInt16.toUInt32 maxTimeDelay_ms) / UInt32.toInt32 (UInt16.toUInt32 (Int16.toUInt16 (Int32.toInt16 (12 : Int32))))) + (1 : Int32))) }
  let ekf_delay_ms : UInt16 := Int16.toUInt16 (Int32.toInt16 (UInt32.toInt32 (UInt16.toUInt32 maxTimeDelay_ms) + Binary64.toInt32 (Binary64.ceil (UInt16.toBinary64 maxTimeDelay_ms * (Binary64.ofBits 0x3fe0000000000000 /- (double)1/2 -/)))))
  s := { s with obs_buffer_length := Int8.toUInt8 (Int32.toInt8 ((UInt32.toInt32 (UInt16.toUInt32 ekf_delay_ms) / UInt32.toInt32 (UInt8.toUInt32 w.EKF3.sensorIntervalMin_ms)) + (1 : Int32))) }
  s := { s with obs_buffer_length := Estimator_lib.MIN_uint8_t2 s.obs_buffer_length s.imu_buffer_length }
  let flow_buffer_length : UInt8 := Int8.toUInt8 (Int32.toInt8 (Estimator_lib.MIN_int32_t_uint8_t ((UInt32.toInt32 (UInt16.toUInt32 ekf_delay_ms) / UInt32.toInt32 (UInt8.toUInt32 w.EKF3.flowIntervalMin_ms)) + (1 : Int32)) s.imu_buffer_length))
  let (t'5, t'6) := EKF_obs_buffer_t_NavEKF3_core_gps_elements.init s.storedGPS s.obs_buffer_length
  s := { s with storedGPS := t'5 }
  if !t'6 then
    return (s, w, o, false)
  let (t'7, t'8) := EKF_obs_buffer_t_NavEKF3_core_mag_elements.init s.storedMag s.obs_buffer_length
  s := { s with storedMag := t'7 }
  if !t'8 then
    return (s, w, o, false)
  let (t'9, t'10) := EKF_obs_buffer_t_NavEKF3_core_baro_elements.init s.storedBaro s.obs_buffer_length
  s := { s with storedBaro := t'9 }
  if !t'10 then
    return (s, w, o, false)
  let mut t'13 := (AP_DAL.airspeed w.heap'AP_DAL[(WPtr.index w.AP_DAL'_singleton)]! != WPtr.null)
  if t'13 then
    let (t'11, t'12) := EKF_obs_buffer_t_NavEKF3_core_tas_elements.init s.tas.stored s.obs_buffer_length
    s := { s with tas.stored := t'11 }
    t'13 := !t'12
  if t'13 then
    return (s, w, o, false)
  let mut t'16 := AP_DAL.opticalflow_enabled w.heap'AP_DAL[(WPtr.index w.AP_DAL'_singleton)]!
  if t'16 then
    let (t'14, t'15) := EKF_obs_buffer_t_NavEKF3_core_of_elements.init s.storedOF flow_buffer_length
    s := { s with storedOF := t'14 }
    t'16 := !t'15
  if t'16 then
    return (s, w, o, false)
  let mut t'19 := AP_NavEKF_Source.ext_nav_enabled w.EKF3.sources
  if t'19 then
    let (t'17, t'18) := EKF_obs_buffer_t_NavEKF3_core_vel_odm_elements.init s.bodyOdm.stored s.obs_buffer_length
    s := { s with bodyOdm.stored := t'17 }
    t'19 := !t'18
  if t'19 then
    return (s, w, o, false)
  let mut t'22 := AP_NavEKF_Source.wheel_encoder_enabled w.EKF3.sources
  if t'22 then
    let (t'20, t'21) := EKF_obs_buffer_t_NavEKF3_core_wheel_odm_elements.init s.bodyOdm.storedWheel s.imu_buffer_length
    s := { s with bodyOdm.storedWheel := t'20 }
    t'22 := !t'21
  if t'22 then
    return (s, w, o, false)
  let mut t'25 := AP_NavEKF_Source.gps_yaw_enabled w.EKF3.sources
  if t'25 then
    let (t'23, t'24) := EKF_obs_buffer_t_NavEKF3_core_yaw_elements.init s.gpsYaw.stored s.obs_buffer_length
    s := { s with gpsYaw.stored := t'23 }
    t'25 := !t'24
  if t'25 then
    return (s, w, o, false)
  let (t'26, t'27) := EKF_IMU_buffer_t_NavEKF3_core_imu_elements.init_uint8_t s.storedIMU s.imu_buffer_length
  s := { s with storedIMU := t'26 }
  if !t'27 then
    return (s, w, o, false)
  let (t'28, t'29) := EKF_IMU_buffer_t_NavEKF3_core_output_elements.init_uint8_t s.storedOutput s.imu_buffer_length
  s := { s with storedOutput := t'28 }
  if !t'29 then
    return (s, w, o, false)
  if (s.yawEstimator == WPtr.null) && (UInt8.toUInt32 (AP_ParamT_unsigned_char_1.op_to_unsigned_char w.EKF3._gsfRunMask) &&& ((1 : UInt32) <<< Int32.toUInt32 (UInt32.toInt32 (UInt8.toUInt32 s.core_index)))) != (0 : UInt32) then
    if UInt32.toUInt64 (AP_DAL.available_memory w.heap'AP_DAL[(WPtr.index w.AP_DAL'_singleton)]!) < (1712 : UInt64) + Int64.toUInt64 (Int32.toInt64 (1024 : Int32)) then
      o := o.push (Output.send_text (2 : UInt32) "EKF3 IMU%u GSF: not enough memory" #[Sum.inl (UInt32.toUInt64 (UInt8.toUInt32 s.imu_index))])
      return (s, w, o, false)
    let t'30 := EKFGSF_yaw.init
    let t'31 := w.heap'EKFGSF_yaw.size
    w := { w with heap'EKFGSF_yaw := w.heap'EKFGSF_yaw.push t'30 }
    s := { s with yawEstimator := (WPtr.heap'EKFGSF_yaw t'31) }
    if s.yawEstimator == WPtr.null then
      o := o.push (Output.send_text (2 : UInt32) "EKF3 IMU%uGSF: allocation failed" #[Sum.inl (UInt32.toUInt64 (UInt8.toUInt32 s.imu_index))])
      return (s, w, o, false)
  return (s, w, o, true)

end NavEKF3_core

namespace NavEKF3_core

/-- C++ `void NavEKF3_core::update_airspeed_selection()`, `AP_NavEKF3/AP_NavEKF3_Measurements.cpp:1259-1277`. -/
def update_airspeed_selection (s : State) (w : World) : State := Id.run do
  let mut s := s
  let arsp : WPtr := AP_DAL.airspeed w.heap'AP_DAL[(WPtr.index w.AP_DAL'_singleton)]!
  if arsp == WPtr.null then
    return s
  s := { s with selected_airspeed := AP_DAL_Airspeed.get_primary w.heap'AP_DAL_Airspeed[(WPtr.index arsp)]! }
  if AP_ParamT_unsigned_int_3.op_to_unsigned_int w.EKF3._affinity &&& NavEKF3_core.ekf_affinity.toInt NavEKF3_core.ekf_affinity.EKF_AFFINITY_ARSP != (0 : UInt32) then
    if decide (UInt32.toInt32 (UInt8.toUInt32 s.core_index) < UInt32.toInt32 (UInt8.toUInt32 (AP_DAL_Airspeed.get_num_sensors w.heap'AP_DAL_Airspeed[(WPtr.index arsp)]!))) && AP_DAL_Airspeed.healthy_uint8_t w.heap'AP_DAL_Airspeed[(WPtr.index arsp)]! s.core_index && AP_DAL_Airspeed.use_uint8_t w.heap'AP_DAL_Airspeed[(WPtr.index arsp)]! s.core_index then
      s := { s with selected_airspeed := s.core_index }
  return s

/-- C++ `void NavEKF3_core::update_sensor_selection()`, `AP_NavEKF3/AP_NavEKF3_Measurements.cpp:1282-1288`. -/
def update_sensor_selection (s : State) (w : World) (o : Outputs) : State × Outputs := Id.run do
  let mut s := s
  let mut o := o
  s := update_gps_selection s w
  let (t'1, t'2) := update_mag_selection s w o
  s := t'1
  o := t'2
  s := update_baro_selection s w
  s := update_airspeed_selection s w
  return (s, o)

end NavEKF3_core

namespace NavEKF3_core

/-- C++ `ftype NavEKF3_core::InitialGyroBiasUncertainty() const`, `AP_NavEKF3/AP_NavEKF3_GyroBias.cpp:22-25`. -/
def InitialGyroBiasUncertainty (s : State) (w : World) : Binary64 := Id.run do
  return Binary32.toBinary64 (AP_DAL_InertialSensor.get_gyro_bias_init_dps w.heap'AP_DAL[(WPtr.index w.AP_DAL'_singleton)]!._ins s.imu_index)

/-- C++ `void NavEKF3_core::CovarianceInit()`, `AP_NavEKF3/AP_NavEKF3_core.cpp:561-607`. -/
def CovarianceInit (s : State) (w : World) : State × World := Id.run do
  let mut s := s
  let mut w := w
  s := { s with Pmut := Array.replicate 576 (Binary64.ofBits 0x0000000000000000 /- 0.0 -/) }
  let mut rot_vec_var : Vector3p.State := Vector3p.init_void
  rot_vec_var := { rot_vec_var with z := Binary32.toBinary64 (Estimator_lib.sq_float (Binary32.ofBits 0x3dcccccd /- 0.1f -/)) }
  rot_vec_var := { rot_vec_var with y := rot_vec_var.z }
  rot_vec_var := { rot_vec_var with x := rot_vec_var.y }
  let (t'1, t'2, t'3) := CovariancePrediction s w true rot_vec_var
  w := t'2
  s := t'1
  rot_vec_var := t'3
  s := { s with Pmut := s.Pmut.set! 100 (Estimator_lib.sq_AP_ParamT_float_4 w.EKF3._gpsHorizVelNoise) }
  s := { s with Pmut := s.Pmut.set! 125 (s.Pmut[100]!) }
  s := { s with Pmut := s.Pmut.set! 150 (Estimator_lib.sq_AP_ParamT_float_4 w.EKF3._gpsVertVelNoise) }
  s := { s with Pmut := s.Pmut.set! 175 (Estimator_lib.sq_AP_ParamT_float_4 w.EKF3._gpsHorizPosNoise) }
  s := { s with Pmut := s.Pmut.set! 200 (s.Pmut[175]!) }
  s := { s with Pmut := s.Pmut.set! 225 (Estimator_lib.sq_AP_ParamT_float_4 w.EKF3._baroAltNoise) }
  s := { s with Pmut := s.Pmut.set! 250 (Estimator_lib.sq_double (Estimator_lib.radians_double (InitialGyroBiasUncertainty s w * s.dtEkfAvg))) }
  s := { s with Pmut := s.Pmut.set! 275 (s.Pmut[250]!) }
  s := { s with Pmut := s.Pmut.set! 300 (s.Pmut[250]!) }
  s := { s with Pmut := s.Pmut.set! 325 (Estimator_lib.sq_double (Binary32.toBinary64 ((Binary32.ofBits 0x3e4ccccd /- 0.200000003 -/) * AP_ParamT_float_4.op_to_float w.EKF3._accBiasLim) * s.dtEkfAvg)) }
  s := { s with Pmut := s.Pmut.set! 350 (s.Pmut[325]!) }
  s := { s with Pmut := s.Pmut.set! 375 (s.Pmut[325]!) }
  s := { s with Pmut := s.Pmut.set! 400 (Estimator_lib.sq_AP_ParamT_float_4 w.EKF3._magNoise) }
  s := { s with Pmut := s.Pmut.set! 425 (s.Pmut[400]!) }
  s := { s with Pmut := s.Pmut.set! 450 (s.Pmut[400]!) }
  s := { s with Pmut := s.Pmut.set! 475 (Estimator_lib.sq_AP_ParamT_float_4 w.EKF3._magNoise) }
  s := { s with Pmut := s.Pmut.set! 500 (s.Pmut[475]!) }
  s := { s with Pmut := s.Pmut.set! 525 (s.Pmut[475]!) }
  s := { s with Pmut := s.Pmut.set! 550 (Binary64.ofBits 0x0000000000000000 /- 0.0f -/) }
  s := { s with Pmut := s.Pmut.set! 575 (s.Pmut[550]!) }
  return (s, w)

/-- C++ `void NavEKF3_core::StoreOutputReset()`, `AP_NavEKF3/AP_NavEKF3_core.cpp:1809-1822`. -/
def StoreOutputReset (s : State) : State := Id.run do
  let mut s := s
  s := { s with outputDataNew.quat := ({ q1 := s.statesArray[0]!, q2 := s.statesArray[1]!, q3 := s.statesArray[2]!, q4 := s.statesArray[3]! } : QuaternionT_double.State) }
  s := { s with outputDataNew.velocity := ({ x := s.statesArray[4]!, y := s.statesArray[5]!, z := s.statesArray[6]! } : Vector3p.State) }
  s := { s with outputDataNew.position := ({ x := s.statesArray[7]!, y := s.statesArray[8]!, z := s.statesArray[9]! } : Vector3p.State) }
  let t'1 : UInt8 := Int8.toUInt8 (Int32.toInt8 (0 : Int32))
  let t'2 : Int32 := UInt32.toInt32 (UInt8.toUInt32 s.imu_buffer_length)
  for i' in [0:(t'2.toInt - (Int.ofNat t'1.toNat)).toNat] do  -- C++ loop bounded by a runtime value (--runtime-loops)
    let i : UInt8 := t'1 + Nat.toUInt8 i'
    s := { s with storedOutput.buffer := s.storedOutput.buffer.set! (UInt8.toNat (UInt32.toUInt8 (UInt8.toUInt32 i))) s.outputDataNew }
  s := { s with outputDataDelayed := s.outputDataNew }
  s := { s with vertCompFiltState.pos := s.statesArray[9]! }
  s := { s with vertCompFiltState.vel := s.statesArray[6]! }
  return s

/-- C++ `bool NavEKF3_core::InitialiseFilterBootstrap()`, `AP_NavEKF3/AP_NavEKF3_core.cpp:451-558`. -/
def InitialiseFilterBootstrap (s : State) (w : World) (o : Outputs) : State × World × Outputs × Bool := Id.run do
  let mut s := s
  let mut w := w
  let mut o := o
  let (t'1, t'2) := update_sensor_selection s w o
  s := t'1
  o := t'2
  if assume_zero_sideslip w && decide (AP_GPS_FixType.toInt (AP_DAL_GPS.status_uint8_t w.heap'AP_DAL[(WPtr.index w.AP_DAL'_singleton)]!._gps s.preferred_gps) < AP_GPS_FixType.toInt AP_GPS_FixType.FIX_3D) then
    s := { s with prearm_fail_string := (CText.fmt (40 : UInt64) "EKF3 init failure: No GPS lock" #[]) }
    s := { s with statesInitialised := false }
    return (s, w, o, false)
  s := readIMUData s w false
  let (t'3, t'4) := readMagData s w o
  s := t'3
  o := t'4
  let (t'5, t'6, t'7) := readGpsData s w o
  w := t'6
  s := t'5
  o := t'7
  s := readGpsYawData s w
  s := readBaroData s w
  if s.statesInitialised then
    return (s, w, o, EKF_IMU_buffer_t_NavEKF3_core_imu_elements.is_filled s.storedIMU)
  if s.firstInitTime_ms == Int32.toUInt32 (0 : Int32) then
    s := { s with firstInitTime_ms := s.imuSampleTime_ms }
    return (s, w, o, false)
  else if s.imuSampleTime_ms - s.firstInitTime_ms < Int32.toUInt32 (1000 : Int32) then
    return (s, w, o, false)
  let (t'8, t'9) := InitialiseVariables s w
  w := t'9
  s := t'8
  let mut initAccVec : Vector3p.State := Vector3p.init_void
  let t'10 := s.accel_index_active
  initAccVec := Vector3f.todouble w.heap'AP_DAL[(WPtr.index w.AP_DAL'_singleton)]!._ins.accel_filtered[UInt8.toNat t'10]!
  let mut pitch : Binary64 := (Binary64.ofBits 0x0000000000000000 /- 0 -/)
  let mut roll : Binary64 := (Binary64.ofBits 0x0000000000000000 /- 0 -/)
  if Vector3p.length initAccVec > (Binary64.ofBits 0x3f50624de0000000 /- 0.001f -/) then
    initAccVec := Vector3p.normalize initAccVec
    pitch := Musl.asin.asin initAccVec.x
    roll := Musl.atan2.atan2 (-initAccVec.y) (-initAccVec.z)
  let t'11 := QuaternionT_double.from_euler_double3 ({ q1 := s.statesArray[0]!, q2 := s.statesArray[1]!, q3 := s.statesArray[2]!, q4 := s.statesArray[3]! } : QuaternionT_double.State) roll pitch (Binary64.ofBits 0x0000000000000000 /- 0.0f -/)
  s := { s with statesArray := ((((s.statesArray.set! 0 t'11.q1).set! 1 t'11.q2).set! 2 t'11.q3).set! 3 t'11.q4) }
  let t'12 := Vector3p.zero ({ x := s.statesArray[4]!, y := s.statesArray[5]!, z := s.statesArray[6]! } : Vector3p.State)
  s := { s with statesArray := (((s.statesArray.set! 4 t'12.x).set! 5 t'12.y).set! 6 t'12.z) }
  let t'13 := Vector3p.zero ({ x := s.statesArray[7]!, y := s.statesArray[8]!, z := s.statesArray[9]! } : Vector3p.State)
  s := { s with statesArray := (((s.statesArray.set! 7 t'13.x).set! 8 t'13.y).set! 9 t'13.z) }
  let t'14 := Vector3p.zero ({ x := s.statesArray[10]!, y := s.statesArray[11]!, z := s.statesArray[12]! } : Vector3p.State)
  s := { s with statesArray := (((s.statesArray.set! 10 t'14.x).set! 11 t'14.y).set! 12 t'14.z) }
  let t'15 := Vector3p.zero ({ x := s.statesArray[13]!, y := s.statesArray[14]!, z := s.statesArray[15]! } : Vector3p.State)
  s := { s with statesArray := (((s.statesArray.set! 13 t'15.x).set! 14 t'15.y).set! 15 t'15.z) }
  let t'16 := Vector2p.zero ({ x := s.statesArray[22]!, y := s.statesArray[23]! } : Vector2p.State)
  s := { s with statesArray := ((s.statesArray.set! 22 t'16.x).set! 23 t'16.y) }
  let t'17 := Vector3p.zero ({ x := s.statesArray[16]!, y := s.statesArray[17]!, z := s.statesArray[18]! } : Vector3p.State)
  s := { s with statesArray := (((s.statesArray.set! 16 t'17.x).set! 17 t'17.y).set! 18 t'17.z) }
  let t'18 := Vector3p.zero ({ x := s.statesArray[19]!, y := s.statesArray[20]!, z := s.statesArray[21]! } : Vector3p.State)
  s := { s with statesArray := (((s.statesArray.set! 19 t'18.x).set! 20 t'18.y).set! 21 t'18.z) }
  s := ResetVelocity s w NavEKF3_core.resetDataSource.DEFAULT
  s := ResetPosition s w NavEKF3_core.resetDataSource.DEFAULT
  s := ResetHeight s w
  s := { s with posxy_source_last := AP_NavEKF_Source.getPosXYSource w.EKF3.sources s.core_index }
  let (t'19, t'20) := AP_NavEKF_Source.getYawSource w.EKF3.sources w s.core_index
  w := t'19
  s := { s with yaw_source_last := t'20 }
  s := { s with earthRateNED := calcEarthRateNED s.earthRateNED w.heap'AP_DAL[(WPtr.index w.AP_DAL'_singleton)]!._home.lat }
  let (t'21, t'22) := CovarianceInit s w
  w := t'22
  s := t'21
  s := StoreOutputReset s
  s := { s with statesInitialised := true }
  for i' in [0:3] do
    let i : UInt8 := Nat.toUInt8 i'
    s := { s with inactiveBias := s.inactiveBias.set! (UInt8.toNat i) ({ s.inactiveBias[UInt8.toNat i]! with gyro_bias := Vector3p.zero s.inactiveBias[UInt8.toNat i]!.gyro_bias }) }
    s := { s with inactiveBias := s.inactiveBias.set! (UInt8.toNat i) ({ s.inactiveBias[UInt8.toNat i]! with accel_bias := Vector3p.zero s.inactiveBias[UInt8.toNat i]!.accel_bias }) }
  if Location.initialised w.EKF3.common_EKF_origin then
    let (t'23, t'24, t'25, _) := setOriginLLH s w o w.EKF3.common_EKF_origin
    w := t'24
    s := t'23
    o := t'25
  o := o.push (Output.send_text (6 : UInt32) "EKF3 IMU%u initialised" #[Sum.inl (UInt32.toUInt64 (UInt8.toUInt32 s.imu_index))])
  return (s, w, o, false)

end NavEKF3_core

namespace NavEKF3

/-- C++ `bool NavEKF3::InitialiseFilter()`, `AP_NavEKF3/AP_NavEKF3.cpp:792-906`. -/
def InitialiseFilter (s : State) (w : World) (o : Outputs) : State × World × Outputs × Bool := Id.run do
  let mut s := s
  let mut w := w
  let mut o := o
  if Int8.toInt32 (AP_ParamT_signed_char_1.op_to_signed_char s._enable) == (0 : Int32) || UInt32.toInt32 (UInt8.toUInt32 (AP_ParamT_unsigned_char_1.op_to_unsigned_char s._imuMask)) == (0 : Int32) then
    return (s, w, o, false)
  let t'1 := w.heap'AP_DAL[(WPtr.index w.AP_DAL'_singleton)]!  -- the object out of its slot for the call (--swap-out)
  w := { w with heap'AP_DAL := w.heap'AP_DAL.set! (WPtr.index w.AP_DAL'_singleton) default }
  let (t'2, t'3) := AP_DAL.start_frame t'1 w w.heap'AP_DAL'inp AP_DAL.FrameType.InitialiseFilterEKF3
  w := t'3
  w := { w with heap'AP_DAL := w.heap'AP_DAL.set! (WPtr.index w.AP_DAL'_singleton) t'2 }
  s := { s with imuSampleTime_us := AP_DAL.micros64 w.heap'AP_DAL[(WPtr.index w.AP_DAL'_singleton)]! }
  let loop_rate : Binary32 := UInt16.toBinary32 (AP_DAL_InertialSensor.get_loop_rate_hz w.heap'AP_DAL[(WPtr.index w.AP_DAL'_singleton)]!._ins)
  if !(Estimator_lib.is_positive_float loop_rate) then
    return (s, w, o, false)
  s := { s with _frameTimeUsec := Binary32.toUInt32 ((Binary32.ofBits 0x49742400 /- 1e6 -/) / loop_rate) }
  s := { s with _framesPerPrediction := Binary32.toUInt8 ((Binary32.ofBits 0x3c449ba6 /- 0.0120000001 -/) / (UInt32.toBinary32 s._frameTimeUsec * (Binary32.ofBits 0x358637bd /- 1.0e-6 -/)) + (Binary32.ofBits 0x3f000000 /- 0.5 -/)) }
  if s.core == WPtr.null then
    let mask : UInt8 := UInt32.toUInt8 (((1 : UInt32) <<< Int32.toUInt32 (UInt32.toInt32 (UInt8.toUInt32 (AP_DAL_InertialSensor.get_accel_count w.heap'AP_DAL[(WPtr.index w.AP_DAL'_singleton)]!._ins)))) - Int32.toUInt32 (1 : Int32))
    s := { s with _imuMask := AP_ParamT_unsigned_char_1.set_and_default s._imuMask (Int8.toUInt8 (Int32.toInt8 (UInt32.toInt32 (UInt8.toUInt32 (AP_ParamT_unsigned_char_1.get_void s._imuMask)) &&& UInt32.toInt32 (UInt8.toUInt32 mask)))) }
    for i' in [0:3] do
      let i : UInt8 := Nat.toUInt8 i'
      s := { s with coreSetupRequired := s.coreSetupRequired.set! (UInt8.toNat i) false }
      s := { s with coreImuIndex := s.coreImuIndex.set! (UInt8.toNat i) (Int8.toUInt8 (Int32.toInt8 (0 : Int32))) }
    s := { s with num_cores := Int8.toUInt8 (Int32.toInt8 (0 : Int32)) }
    for i'2' in [0:3] do
      let i'2 : UInt8 := Nat.toUInt8 i'2'
      if UInt8.toUInt32 (AP_ParamT_unsigned_char_1.op_to_unsigned_char s._imuMask) &&& ((1 : UInt32) <<< Int32.toUInt32 (UInt32.toInt32 (UInt8.toUInt32 i'2))) != (0 : UInt32) then
        s := { s with coreSetupRequired := s.coreSetupRequired.set! (UInt8.toNat s.num_cores) true }
        s := { s with coreImuIndex := s.coreImuIndex.set! (UInt8.toNat s.num_cores) i'2 }
        s := { s with num_cores := s.num_cores + (1 : UInt8) }
    if UInt32.toUInt64 (AP_DAL.available_memory w.heap'AP_DAL[(WPtr.index w.AP_DAL'_singleton)]!) < (8496 : UInt64) * UInt8.toUInt64 s.num_cores + Int64.toUInt64 (Int32.toInt64 (4096 : Int32)) then
      o := o.push (Output.send_text (2 : UInt32) "EKF3 not enough memory" #[])
      s := { s with _enable := AP_ParamT_signed_char_1.set s._enable (Int32.toInt8 (0 : Int32)) }
      s := { s with num_cores := Int8.toUInt8 (Int32.toInt8 (0 : Int32)) }
      return (s, w, o, false)
    let t'4 := w.heap'NavEKF3_core.size
    w := { w with heap'NavEKF3_core := w.heap'NavEKF3_core ++ Array.replicate (UInt64.toNat (UInt8.toUInt64 s.num_cores)) ({} : NavEKF3_core.State) }  -- C++ `(NavEKF3_core*)dal.malloc_type(sizeof(NavEKF3_core)*num_cores, AP_DAL::MemoryType::FAST)`: k slots, constructed by placement new
    s := { s with core := (WPtr.heap'NavEKF3_core t'4) }
    if s.core == WPtr.null then
      s := { s with _enable := AP_ParamT_signed_char_1.set s._enable (Int32.toInt8 (0 : Int32)) }
      s := { s with num_cores := Int8.toUInt8 (Int32.toInt8 (0 : Int32)) }
      o := o.push (Output.send_text (2 : UInt32) "EKF3 allocation failed" #[])
      return (s, w, o, false)
    let t'5 : UInt8 := Int8.toUInt8 (Int32.toInt8 (0 : Int32))
    let t'6 : Int32 := UInt32.toInt32 (UInt8.toUInt32 s.num_cores)
    for i'3' in [0:(t'6.toInt - (Int.ofNat t'5.toNat)).toNat] do  -- C++ loop bounded by a runtime value (--runtime-loops)
      let i'3 : UInt8 := t'5 + Nat.toUInt8 i'3'
      let t'7 := NavEKF3_core.init WPtr.EKF3
      w := { w with heap'NavEKF3_core := w.heap'NavEKF3_core.set! ((WPtr.index s.core) + (UInt8.toNat i'3)) t'7 }
  let mut core_setup_success : Bool := true
  let t'8 : UInt8 := Int8.toUInt8 (Int32.toInt8 (0 : Int32))
  let t'9 : Int32 := UInt32.toInt32 (UInt8.toUInt32 s.num_cores)
  for core_index' in [0:(t'9.toInt - (Int.ofNat t'8.toNat)).toNat] do  -- C++ loop bounded by a runtime value (--runtime-loops)
    let core_index : UInt8 := t'8 + Nat.toUInt8 core_index'
    if s.coreSetupRequired[UInt8.toNat core_index]! then
      w := { w with EKF3 := s }  -- this object's state into the World: the call reaches it
      let t'10 := w.heap'NavEKF3_core[((WPtr.index s.core) + (UInt8.toNat core_index))]!  -- the object out of its slot for the call (--swap-out)
      w := { w with heap'NavEKF3_core := w.heap'NavEKF3_core.set! ((WPtr.index s.core) + (UInt8.toNat core_index)) default }
      let (t'11, t'12, t'13, t'14) := NavEKF3_core.setup_core t'10 w o s.coreImuIndex[UInt8.toNat core_index]! core_index
      w := t'12
      w := { w with heap'NavEKF3_core := w.heap'NavEKF3_core.set! ((WPtr.index s.core) + (UInt8.toNat core_index)) t'11 }
      o := t'13
      s := w.EKF3  -- this object's state as the call left it
      s := { s with coreSetupRequired := s.coreSetupRequired.set! (UInt8.toNat core_index) (!t'14) }
      if s.coreSetupRequired[UInt8.toNat core_index]! then
        core_setup_success := false
  if !core_setup_success then
    return (s, w, o, false)
  s := resetCoreErrors s
  s := { s with primary := Int8.toUInt8 (Int32.toInt8 (if UInt32.toInt32 (UInt8.toUInt32 (AP_ParamT_unsigned_char_1.op_to_unsigned_char s._primary_core)) < UInt32.toInt32 (UInt8.toUInt32 s.num_cores) then UInt32.toInt32 (UInt8.toUInt32 (AP_ParamT_unsigned_char_1.op_to_unsigned_char s._primary_core)) else (0 : Int32))) }
  s := { s with common_origin_valid := false }
  let mut ret : Bool := true
  let t'15 : UInt8 := Int8.toUInt8 (Int32.toInt8 (0 : Int32))
  let t'16 : Int32 := UInt32.toInt32 (UInt8.toUInt32 s.num_cores)
  for i'4' in [0:(t'16.toInt - (Int.ofNat t'15.toNat)).toNat] do  -- C++ loop bounded by a runtime value (--runtime-loops)
    let i'4 : UInt8 := t'15 + Nat.toUInt8 i'4'
    w := { w with EKF3 := s }  -- this object's state into the World: the call reaches it
    let t'17 := w.heap'NavEKF3_core[((WPtr.index s.core) + (UInt8.toNat i'4))]!  -- the object out of its slot for the call (--swap-out)
    w := { w with heap'NavEKF3_core := w.heap'NavEKF3_core.set! ((WPtr.index s.core) + (UInt8.toNat i'4)) default }
    let (t'18, t'19, t'20, t'21) := NavEKF3_core.InitialiseFilterBootstrap t'17 w o
    w := t'19
    w := { w with heap'NavEKF3_core := w.heap'NavEKF3_core.set! ((WPtr.index s.core) + (UInt8.toNat i'4)) t'18 }
    o := t'20
    s := w.EKF3  -- this object's state as the call left it
    ret := (if ret then (1 : Int32) else (0 : Int32)) &&& (if t'21 then (1 : Int32) else (0 : Int32)) != (0 : Int32)
  s := { s with coreLastTimePrimary_us := Array.replicate 3 (0 : UInt64) }
  s := { s with yaw_reset_data := { count := (0 : UInt16), last_core_count := (0 : UInt16) } }
  s := { s with pos_reset_data := { count := (0 : UInt16), last_core_count := (0 : UInt16) } }
  s := { s with pos_down_reset_data := { count := (0 : UInt16), last_core_count := (0 : UInt16) } }
  return (s, w, o, ret)

end NavEKF3

namespace NavEKF3

/-- C++ `void NavEKF3::updateLaneSwitchPosDownResetData(uint8_t new_primary)`, `AP_NavEKF3/AP_NavEKF3.cpp:1935-1943`. -/
def updateLaneSwitchPosDownResetData (s : State) (w : World) (new_primary : UInt8) : State := Id.run do
  let mut s := s
  s := { s with pos_down_reset_data.last_core_count := NavEKF3_core.getPosDownResetCount w.heap'NavEKF3_core[((WPtr.index s.core) + (UInt8.toNat new_primary))]! }
  s := { s with pos_down_reset_data.count := s.pos_down_reset_data.count + (1 : UInt16) }
  return s

/-- C++ `void NavEKF3::switchLane(uint8_t new_lane_index)`, `AP_NavEKF3/AP_NavEKF3.cpp:1092-1106`. -/
def switchLane (s : State) (w : World) (o : Outputs) (new_lane_index : UInt8) : State × Outputs := Id.run do
  let mut s := s
  let mut o := o
  if UInt32.toInt32 (UInt8.toUInt32 new_lane_index) ≥ UInt32.toInt32 (UInt8.toUInt32 s.num_cores) then
    return (s, o)
  if UInt32.toInt32 (UInt8.toUInt32 new_lane_index) != UInt32.toInt32 (UInt8.toUInt32 s.primary) then
    s := updateLaneSwitchYawResetData s w new_lane_index
    s := updateLaneSwitchPosResetData s w new_lane_index
    s := updateLaneSwitchPosDownResetData s w new_lane_index
    s := { s with primary := new_lane_index }
    s := { s with lastLaneSwitch_ms := AP_DAL.millis w.heap'AP_DAL[(WPtr.index w.AP_DAL'_singleton)]! }
    o := o.push (Output.send_text (2 : UInt32) "EKF3 lane switch %u" #[Sum.inl (Int64.toUInt64 (Int32.toInt64 (UInt32.toInt32 (UInt8.toUInt32 s.primary))))])
  return (s, o)

end NavEKF3

namespace NavEKF3_core

/-- C++ `float NavEKF3_core::errorScore() const`, `AP_NavEKF3/AP_NavEKF3_Outputs.cpp:64-88`. -/
def errorScore (s : State) (w : World) : Binary32 := Id.run do
  let mut score : Binary32 := (Binary32.ofBits 0x00000000 /- 0.0f -/)
  if s.tiltAlignComplete && s.yawAlignComplete then
    score := Binary64.toBinary32 (Estimator_lib.MAX_float_double score ((Binary64.ofBits 0x3fe0000000000000 /- 0.5f -/) * (s.velTestRatio + s.posTestRatio)))
    score := Binary64.toBinary32 (Estimator_lib.MAX_float_double score s.hgtTestRatio)
    if assume_zero_sideslip w then
      let arsp : WPtr := AP_DAL.airspeed w.heap'AP_DAL[(WPtr.index w.AP_DAL'_singleton)]!
      if arsp != WPtr.null && decide (UInt32.toInt32 (UInt8.toUInt32 (AP_DAL_Airspeed.get_num_sensors w.heap'AP_DAL_Airspeed[(WPtr.index arsp)]!)) ≥ (2 : Int32)) && (AP_ParamT_unsigned_int_3.op_to_unsigned_int w.EKF3._affinity &&& NavEKF3_core.ekf_affinity.toInt NavEKF3_core.ekf_affinity.EKF_AFFINITY_ARSP) != (0 : UInt32) then
        score := Binary64.toBinary32 (Estimator_lib.MAX_float_double score ((Binary64.ofBits 0x3fd3333340000000 /- 0.3f -/) * s.tas.testRatio))
    if AP_ParamT_unsigned_int_3.op_to_unsigned_int w.EKF3._affinity &&& NavEKF3_core.ekf_affinity.toInt NavEKF3_core.ekf_affinity.EKF_AFFINITY_MAG != (0 : UInt32) then
      score := Binary64.toBinary32 (Estimator_lib.MAX_float_double score ((Binary64.ofBits 0x3fd3333340000000 /- 0.3f -/) * (s.magTestRatio.x + s.magTestRatio.y + s.magTestRatio.z)))
  return score

end NavEKF3_core

namespace NavEKF3

/-- C++ `float NavEKF3::updateCoreErrorScores()`, `AP_NavEKF3/AP_NavEKF3.cpp:1120-1126`. -/
def updateCoreErrorScores (s : State) (w : World) : State × World × Binary32 := Id.run do
  let mut s := s
  let mut w := w
  let t'1 : UInt8 := Int8.toUInt8 (Int32.toInt8 (0 : Int32))
  let t'2 : Int32 := UInt32.toInt32 (UInt8.toUInt32 s.num_cores)
  for i' in [0:(t'2.toInt - (Int.ofNat t'1.toNat)).toNat] do  -- C++ loop bounded by a runtime value (--runtime-loops)
    let i : UInt8 := t'1 + Nat.toUInt8 i'
    w := { w with EKF3 := s }  -- this object's state into the World: the call reaches it
    s := { s with coreErrorScores := s.coreErrorScores.set! (UInt8.toNat i) (NavEKF3_core.errorScore w.heap'NavEKF3_core[((WPtr.index s.core) + (UInt8.toNat i))]! w) }
  return (s, w, s.coreErrorScores[UInt8.toNat s.primary]!)

end NavEKF3

namespace NavEKF3_core

/-- C++ `void NavEKF3_core::getGyroBias(Vector3f & gyroBias) const`, `AP_NavEKF3/AP_NavEKF3_Outputs.cpp:135-142`. -/
def getGyroBias (s : State) (gyroBias : Vector3f.State) : Vector3f.State := Id.run do
  let mut gyroBias := gyroBias
  if s.dtEkfAvg < (Binary64.ofBits 0x3eb0c6f7a0000000 /- 1e-6f -/) then
    gyroBias := Vector3f.zero gyroBias
    return gyroBias
  gyroBias := Vector3p.tofloat (Vector3p.op_div ({ x := s.statesArray[10]!, y := s.statesArray[11]!, z := s.statesArray[12]! } : Vector3p.State) s.dtEkfAvg)
  return gyroBias

/-- C++ `void NavEKF3_core::detectFlight()`, `AP_NavEKF3/AP_NavEKF3_VehicleStatus.cpp:324-453`. -/
def detectFlight (s : State) (w : World) : State × World := Id.run do
  let mut s := s
  let mut w := w
  if assume_zero_sideslip w then
    let gndSpdSq : Binary64 := Estimator_lib.sq_double s.gpsDataNew.vel.x + Estimator_lib.sq_double s.gpsDataNew.vel.y
    let mut highGndSpd : Bool := false
    let mut highAirSpd : Bool := false
    let mut largeHgtChange : Bool := false
    let arsp : WPtr := AP_DAL.airspeed w.heap'AP_DAL[(WPtr.index w.AP_DAL'_singleton)]!
    if (arsp != WPtr.null) && AP_DAL_Airspeed.healthy_uint8_t w.heap'AP_DAL_Airspeed[(WPtr.index arsp)]! s.selected_airspeed && AP_DAL_Airspeed.use_uint8_t w.heap'AP_DAL_Airspeed[(WPtr.index arsp)]! s.selected_airspeed then
      if AP_DAL_Airspeed.get_airspeed_uint8_t w.heap'AP_DAL_Airspeed[(WPtr.index arsp)]! s.selected_airspeed * AP_DAL.get_EAS2TAS w.heap'AP_DAL[(WPtr.index w.AP_DAL'_singleton)]! > (Binary32.ofBits 0x41200000 /- 10.0f -/) then
        highAirSpd := true
    let gndSpdThresholdSq : Binary64 := Binary32.toBinary64 (Estimator_lib.sq_float (Binary32.ofBits 0x40a00000 /- 5.0f -/))
    if gndSpdSq > gndSpdThresholdSq + Estimator_lib.sq_double s.gpsSpdAccuracy then
      highGndSpd := true
    if Binary64.abs s.hgtMea > (Binary64.ofBits 0x4024000000000000 /- 10.0f -/) then
      largeHgtChange := true
    if s.motorsArmed then
      s := { s with onGround := false }
      if highGndSpd && (AP_DAL.get_takeoff_expected w.heap'AP_DAL[(WPtr.index w.AP_DAL'_singleton)]! || highAirSpd || largeHgtChange) then
        s := { s with inFlight := true }
    else
      s := { s with onGround := true }
      s := { s with inFlight := false }
  else
    if s.motorsArmed then
      s := { s with onGround := false }
    else
      s := { s with inFlight := false }
      s := { s with onGround := true }
    if !s.onGround then
      if (s.statesArray[9]! - s.posDownAtTakeoff) < (Binary64.ofBits 0xbff8000000000000 /- -1.5f -/) then
        s := { s with inFlight := true }
      if (s.rangeDataNew.rng - s.rngAtStartOfFlight) > (Binary64.ofBits 0x3fe0000000000000 /- 0.5f -/) then
        s := { s with inFlight := true }
      if AP_DAL.get_time_flying_ms w.heap'AP_DAL[(WPtr.index w.AP_DAL'_singleton)]! > Int32.toUInt32 (5000 : Int32) then
        s := { s with inFlight := true }
  if s.onGround then
    s := { s with posDownAtTakeoff := s.statesArray[9]! }
    s := { s with rngAtStartOfFlight := s.rangeDataNew.rng }
    if s.magStateInitComplete then
      s := { s with posDownAtLastMagReset := s.statesArray[9]! }
      s := { s with quatAtLastMagReset := ({ q1 := s.statesArray[0]!, q2 := s.statesArray[1]!, q3 := s.statesArray[2]!, q4 := s.statesArray[3]! } : QuaternionT_double.State) }
      s := { s with yawInnovAtLastMagReset := s.innovYaw }
  if (!s.prevOnGround && s.onGround) || !s.gpsSpdAccPass then
    s := { s with EKFGSF_run_filterbank := false }
  else if s.yawEstimator != WPtr.null && !s.EKFGSF_run_filterbank && (s.inFlight || AP_DAL.get_takeoff_expected w.heap'AP_DAL[(WPtr.index w.AP_DAL'_singleton)]!) && s.gpsSpdAccPass then
    s := { s with EKFGSF_yaw_reset_ms := Int32.toUInt32 (0 : Int32) }
    s := { s with EKFGSF_yaw_reset_request_ms := Int32.toUInt32 (0 : Int32) }
    s := { s with EKFGSF_yaw_reset_count := Int8.toUInt8 (Int32.toInt8 (0 : Int32)) }
    s := { s with EKFGSF_yaw_valid_count := Int8.toUInt8 (Int32.toInt8 (0 : Int32)) }
    s := { s with EKFGSF_run_filterbank := true }
    let mut gyroBias : Vector3f.State := Vector3f.init_void
    gyroBias := getGyroBias s gyroBias
    let t'1 := w.heap'EKFGSF_yaw[(WPtr.index s.yawEstimator)]!  -- the object out of its slot for the call (--swap-out)
    w := { w with heap'EKFGSF_yaw := w.heap'EKFGSF_yaw.set! (WPtr.index s.yawEstimator) default }
    let (t'2, t'3) := EKFGSF_yaw.setGyroBias t'1 gyroBias
    w := { w with heap'EKFGSF_yaw := w.heap'EKFGSF_yaw.set! (WPtr.index s.yawEstimator) t'2 }
    gyroBias := t'3
  s := { s with prevOnGround := s.onGround }
  s := { s with prevInFlight := s.inFlight }
  return (s, w)

end NavEKF3_core

namespace NavEKF3_core

/-- C++ `void NavEKF3_core::updateStateIndexLim()`, `AP_NavEKF3/AP_NavEKF3_Control.cpp:199-218`. -/
def updateStateIndexLim (s : State) : State := Id.run do
  let mut s := s
  if s.inhibitWindStates then
    if s.inhibitMagStates then
      if s.inhibitDelVelBiasStates then
        if s.inhibitDelAngBiasStates then
          s := { s with stateIndexLim := Int8.toUInt8 (Int32.toInt8 (9 : Int32)) }
        else
          s := { s with stateIndexLim := Int8.toUInt8 (Int32.toInt8 (12 : Int32)) }
      else
        s := { s with stateIndexLim := Int8.toUInt8 (Int32.toInt8 (15 : Int32)) }
    else
      s := { s with stateIndexLim := Int8.toUInt8 (Int32.toInt8 (21 : Int32)) }
  else
    s := { s with stateIndexLim := Int8.toUInt8 (Int32.toInt8 (23 : Int32)) }
  return s

/-- C++ `bool NavEKF3_core::useAirspeed() const`, `AP_NavEKF3/AP_NavEKF3_Control.cpp:537-541`. -/
def useAirspeed (s : State) (w : World) : Bool := Id.run do
  let airspeed : WPtr := AP_DAL.airspeed w.heap'AP_DAL[(WPtr.index w.AP_DAL'_singleton)]!
  return airspeed != WPtr.null && AP_DAL_Airspeed.healthy_uint8_t w.heap'AP_DAL_Airspeed[(WPtr.index airspeed)]! s.selected_airspeed && AP_DAL_Airspeed.use_uint8_t w.heap'AP_DAL_Airspeed[(WPtr.index airspeed)]! s.selected_airspeed

/-- C++ `void NavEKF3_core::setWindMagStateLearningMode()`, `AP_NavEKF3/AP_NavEKF3_Control.cpp:62-195`. -/
def setWindMagStateLearningMode (s : State) (w : World) : State × World := Id.run do
  let mut s := s
  let mut w := w
  let recentGpsYawFusion : Bool := (s.yaw_source_last == AP_NavEKF_Source.SourceYaw.GPS || s.yaw_source_last == AP_NavEKF_Source.SourceYaw.GPS_COMPASS_FALLBACK) && s.gpsYaw.lastFuseTime_ms != Int32.toUInt32 (0 : Int32) && decide (s.imuSampleTime_ms - s.gpsYaw.lastFuseTime_ms < Int32.toUInt32 (5000 : Int32))
  let yawInitialised : Bool := recentGpsYawFusion || s.finalInflightYawInit
  let canEstimateWind : Bool := ((yawInitialised && s.drag.fusionEnabled) || assume_zero_sideslip w) && !s.onGround && UInt32.toInt32 (NavEKF3_core.AidingMode.toInt s.PV_AidingMode) != UInt32.toInt32 (NavEKF3_core.AidingMode.toInt NavEKF3_core.AidingMode.AID_NONE)
  if !s.inhibitWindStates && !canEstimateWind then
    s := { s with inhibitWindStates := true }
    s := { s with lastAspdEstIsValid := false }
    s := updateStateIndexLim s
  else if s.inhibitWindStates && canEstimateWind && (decide (Estimator_lib.sq_double s.statesArray[4]! + Estimator_lib.sq_double s.statesArray[5]! > Binary32.toBinary64 (Estimator_lib.sq_float (Binary32.ofBits 0x40a00000 /- 5.0f -/))) || s.drag.fusionEnabled) then
    s := { s with inhibitWindStates := false }
    s := updateStateIndexLim s
    if s.yawAlignComplete && assume_zero_sideslip w then
      let mut tempEuler : Vector3p.State := Vector3p.init_void
      let (t'1, t'2, t'3) := QuaternionT_double.to_euler_double3 ({ q1 := s.statesArray[0]!, q2 := s.statesArray[1]!, q3 := s.statesArray[2]!, q4 := s.statesArray[3]! } : QuaternionT_double.State) tempEuler.x tempEuler.y tempEuler.z
      tempEuler := { tempEuler with x := t'1 }
      tempEuler := { tempEuler with y := t'2 }
      tempEuler := { tempEuler with z := t'3 }
      let mut trueAirspeedVariance : Binary64 := (Binary64.ofBits 0x0000000000000000 /- 0.0 -/)  -- uninitialized in C++; assigned before every read
      let haveAirspeedMeasurement : Bool := (s.tas.dataDelayed.allowFusion && (decide (s.imuDataDelayed.time_ms - s.tas.dataDelayed.time_ms < Int32.toUInt32 (500 : Int32))) && useAirspeed s w)
      if haveAirspeedMeasurement then
        trueAirspeedVariance := Estimator_lib.constrain_value_line_double s.tas.dataDelayed.tasVariance (Binary64.ofBits 0x3fd0000000000000 /- (double)1/4 -/) (Binary64.ofBits 0x4079000000000000 /- (double)400 -/) (Int32.toUInt32 (90 : Int32))
        let windSpeed : Binary64 := Binary64.sqrt (Estimator_lib.sq_double s.statesArray[4]! + Estimator_lib.sq_double s.statesArray[5]!) - s.tas.dataDelayed.tas
        s := { s with statesArray := s.statesArray.set! 22 (windSpeed * Musl.cos.cos tempEuler.z) }
        s := { s with statesArray := s.statesArray.set! 23 (windSpeed * Musl.sin.sin tempEuler.z) }
      else
        trueAirspeedVariance := (Binary64.ofBits 0x4079000000000000 /- (double)400 -/)
      s := zeroStatesVarCov s (Int8.toUInt8 (Int32.toInt8 (22 : Int32))) (Int8.toUInt8 (Int32.toInt8 (23 : Int32)))
      s := { s with Pmut := s.Pmut.set! 575 trueAirspeedVariance }
      s := { s with Pmut := s.Pmut.set! 550 (s.Pmut[575]!) }
      s := { s with windStatesAligned := true }
    else
      s := zeroStatesVarCov s (Int8.toUInt8 (Int32.toInt8 (22 : Int32))) (Int8.toUInt8 (Int32.toInt8 (23 : Int32)))
      for index' in [22:24] do
        let index : UInt8 := Nat.toUInt8 index'
        s := { s with Pmut := s.Pmut.set! (UInt8.toNat index * 24 + UInt8.toNat index) (Binary64.ofBits 0x4079000000000000 /- (double)400 -/) }
  s := { s with manoeuvring := decide (s.accNavMagHoriz > (Binary64.ofBits 0x3fe0000000000000 /- 0.5f -/)) }
  let magCalRequested : Bool := ((s.effectiveMagCal == NavEKF3_core.MagCal.WHEN_FLYING) && s.inFlight) || ((s.effectiveMagCal == NavEKF3_core.MagCal.WHEN_MANOEUVRING) && s.manoeuvring) || ((s.effectiveMagCal == NavEKF3_core.MagCal.AFTER_FIRST_CLIMB) && s.finalInflightYawInit && s.finalInflightMagInit) || (s.effectiveMagCal == NavEKF3_core.MagCal.ALWAYS) || ((s.effectiveMagCal == NavEKF3_core.MagCal.GROUND_AND_INFLIGHT) && (!s.inFlight || (s.finalInflightYawInit && s.finalInflightMagInit)))
  let magCalDenied : Bool := !(use_compass s w) || (s.effectiveMagCal == NavEKF3_core.MagCal.NEVER) || (s.onGround && s.effectiveMagCal != NavEKF3_core.MagCal.ALWAYS && s.effectiveMagCal != NavEKF3_core.MagCal.GROUND_AND_INFLIGHT)
  let setMagInhibit : Bool := !magCalRequested || magCalDenied
  if !s.inhibitMagStates && setMagInhibit then
    s := { s with inhibitMagStates := true }
    s := updateStateIndexLim s
  else if s.inhibitMagStates && !setMagInhibit then
    s := { s with inhibitMagStates := false }
    s := updateStateIndexLim s
    if s.magFieldLearned then
      s := { s with Pmut := s.Pmut.set! 400 s.earthMagFieldVar.x }
      s := { s with Pmut := s.Pmut.set! 425 s.earthMagFieldVar.y }
      s := { s with Pmut := s.Pmut.set! 450 s.earthMagFieldVar.z }
      s := { s with Pmut := s.Pmut.set! 475 s.bodyMagFieldVar.x }
      s := { s with Pmut := s.Pmut.set! 500 s.bodyMagFieldVar.y }
      s := { s with Pmut := s.Pmut.set! 525 s.bodyMagFieldVar.z }
    else
      for index'2' in [16:22] do
        let index'2 : UInt8 := Nat.toUInt8 index'2'
        s := { s with Pmut := s.Pmut.set! (UInt8.toNat index'2 * 24 + UInt8.toNat index'2) (Estimator_lib.sq_AP_ParamT_float_4 w.EKF3._magNoise) }
      let (t'4, t'5) := alignMagStateDeclination s w
      w := t'5
      s := t'4
    if !s.magStateInitComplete || (!s.finalInflightMagInit && s.inFlight) then
      s := { s with magYawResetRequest := true }
  if s.tiltAlignComplete && s.inhibitDelVelBiasStates then
    s := { s with inhibitDelVelBiasStates := false }
    s := updateStateIndexLim s
    s := { s with Pmut := s.Pmut.set! 325 (Estimator_lib.sq_double (Binary32.toBinary64 ((Binary32.ofBits 0x3e4ccccd /- 0.200000003 -/) * AP_ParamT_float_4.op_to_float w.EKF3._accBiasLim) * s.dtEkfAvg)) }
    s := { s with Pmut := s.Pmut.set! 350 (s.Pmut[325]!) }
    s := { s with Pmut := s.Pmut.set! 375 (s.Pmut[325]!) }
  if s.tiltAlignComplete && s.inhibitDelAngBiasStates then
    s := { s with inhibitDelAngBiasStates := false }
    s := updateStateIndexLim s
    s := { s with Pmut := s.Pmut.set! 250 (Estimator_lib.sq_double (Estimator_lib.radians_double (InitialGyroBiasUncertainty s w * s.dtEkfAvg))) }
    s := { s with Pmut := s.Pmut.set! 275 (s.Pmut[250]!) }
    s := { s with Pmut := s.Pmut.set! 300 (s.Pmut[250]!) }
  if s.onGround then
    s := { s with finalInflightYawInit := false }
    s := { s with finalInflightMagInit := false }
    s := { s with magFieldLearned := false }
  s := updateStateIndexLim s
  return (s, w)

/-- C++ `void NavEKF3_core::checkAttitudeAlignmentStatus()`, `AP_NavEKF3/AP_NavEKF3_Control.cpp:517-534`. -/
def checkAttitudeAlignmentStatus (s : State) (w : World) (o : Outputs) : State × Outputs := Id.run do
  let mut s := s
  let mut o := o
  if !s.tiltAlignComplete then
    if s.tiltErrorVariance < Binary32.toBinary64 (Estimator_lib.sq_float (Estimator_lib.radians_float (Binary32.ofBits 0x40a00000 /- 5.0 -/))) then
      s := { s with tiltAlignComplete := true }
      o := o.push (Output.send_text (6 : UInt32) "EKF3 IMU%u tilt alignment complete" #[Sum.inl (UInt32.toUInt64 (UInt8.toUInt32 s.imu_index))])
  if !s.yawAlignComplete && s.tiltAlignComplete && use_compass s w then
    s := { s with magYawResetRequest := true }
  return (s, o)

end NavEKF3_core

namespace NavEKF3_core

/-- C++ `void NavEKF3_core::setYawSource()`, `AP_NavEKF3/AP_NavEKF3_Control.cpp:221-236`. -/
def setYawSource (s : State) (w : World) : State × World := Id.run do
  let mut s := s
  let mut w := w
  let (t'1, t'2) := AP_NavEKF_Source.getYawSource w.EKF3.sources w s.core_index
  w := t'1
  let mut yaw_source : AP_NavEKF_Source.SourceYaw := t'2
  if s.wasLearningCompass_ms > Int32.toUInt32 (0 : Int32) then
    if yaw_source == AP_NavEKF_Source.SourceYaw.COMPASS then
      yaw_source := AP_NavEKF_Source.SourceYaw.NONE
    else if yaw_source == AP_NavEKF_Source.SourceYaw.GPS_COMPASS_FALLBACK then
      yaw_source := AP_NavEKF_Source.SourceYaw.GPS
  if yaw_source != s.yaw_source_last then
    s := { s with yaw_source_last := yaw_source }
    s := { s with yaw_source_reset := true }
  return (s, w)

/-- C++ `bool NavEKF3_core::recentYawFusion() const`, `AP_NavEKF3/AP_NavEKF3_Control.cpp:647-661`. -/
def recentYawFusion (s : State) : Bool := Id.run do
  if s.gpsYaw.lastFuseTime_ms != Int32.toUInt32 (0 : Int32) && decide (s.imuSampleTime_ms - s.gpsYaw.lastFuseTime_ms < Int32.toUInt32 (5000 : Int32)) then
    return true
  if s.last_mag_yaw_fuse_ms != Int32.toUInt32 (0 : Int32) && decide (s.imuSampleTime_ms - s.last_mag_yaw_fuse_ms < Int32.toUInt32 (5000 : Int32)) then
    return true
  return false

/-- C++ `void NavEKF3_core::checkGyroCalStatus()`, `AP_NavEKF3/AP_NavEKF3_Control.cpp:765-783`. -/
def checkGyroCalStatus (s : State) (w : World) : State := Id.run do
  let mut s := s
  let delAngBiasVarMax : Binary64 := Estimator_lib.sq_double (Estimator_lib.radians_double ((Binary64.ofBits 0x3fc3333333333333 /- 0.15 -/) * s.dtEkfAvg))
  if !(recentYawFusion s) || (!(use_compass s w) && (s.yaw_source_last != AP_NavEKF_Source.SourceYaw.GPS) && (s.yaw_source_last != AP_NavEKF_Source.SourceYaw.GPS_COMPASS_FALLBACK) && (s.yaw_source_last != AP_NavEKF_Source.SourceYaw.EXTNAV)) then
    let delAngBiasVarVec : Vector3p.State := Vector3p.init_double3 s.Pmut[250]! s.Pmut[275]! s.Pmut[300]!
    let temp : Vector3p.State := Matrix3_double.op_mul_Vector3p s.prevTnb delAngBiasVarVec
    s := { s with delAngBiasLearned := (decide (Binary64.abs temp.x < delAngBiasVarMax)) && (decide (Binary64.abs temp.y < delAngBiasVarMax)) }
  else
    s := { s with delAngBiasLearned := (decide (s.Pmut[250]! ≤ delAngBiasVarMax)) && (decide (s.Pmut[275]! ≤ delAngBiasVarMax)) && (decide (s.Pmut[300]! ≤ delAngBiasVarMax)) }
  return s

/-- C++ `bool NavEKF3_core::readyToUseGPS() const`, `AP_NavEKF3/AP_NavEKF3_Control.cpp:595-602`. -/
def readyToUseGPS (s : State) (w : World) : Bool := Id.run do
  if AP_NavEKF_Source.getPosXYSource w.EKF3.sources s.core_index != AP_NavEKF_Source.SourceXY.GPS then
    return false
  return s.validOrigin && s.tiltAlignComplete && s.yawAlignComplete && (s.delAngBiasLearned || assume_zero_sideslip w) && s.gpsGoodToAlign && s.gpsDataToFuse

/-- C++ `bool NavEKF3_core::readyToUseRangeBeacon() const`, `AP_NavEKF3/AP_NavEKF3_Control.cpp:605-616`. -/
def readyToUseRangeBeacon : Bool := Id.run do
  return false

/-- C++ `bool NavEKF3_core::readyToUseExtNav() const`, `AP_NavEKF3/AP_NavEKF3_Control.cpp:619-630`. -/
def readyToUseExtNav : Bool := Id.run do
  return false

end NavEKF3_core

namespace NavEKF3_core

/-- C++ `bool NavEKF3_core::readyToUseBodyOdm() const`, `AP_NavEKF3/AP_NavEKF3_Control.cpp:569-592`. -/
def readyToUseBodyOdm (s : State) (w : World) : Bool := Id.run do
  if !(AP_NavEKF_Source.useVelXYSource w.EKF3.sources AP_NavEKF_Source.SourceXY.EXTNAV s.core_index) && !(AP_NavEKF_Source.useVelXYSource w.EKF3.sources AP_NavEKF_Source.SourceXY.WHEEL_ENCODER s.core_index) then
    return false
  let visoDataGood : Bool := (decide (s.imuSampleTime_ms - s.bodyOdm.measTime_ms < Int32.toUInt32 (200 : Int32))) && (decide (s.bodyOdm.dataNew.velErr < (Binary64.ofBits 0x3ff0000000000000 /- 1.0f -/)))
  let wencDataGood : Bool := (decide (s.imuDataDelayed.time_ms - s.bodyOdm.wheelDataDelayed.time_ms < Int32.toUInt32 (200 : Int32)))
  return (visoDataGood || wencDataGood) && s.tiltAlignComplete && s.delAngBiasLearned

/-- C++ `void NavEKF3_core::setAidingMode()`, `AP_NavEKF3/AP_NavEKF3_Control.cpp:239-513`. -/
def setAidingMode (s : State) (w : World) (o : Outputs) : State × World × Outputs := Id.run do
  let mut s := s
  let mut w := w
  let mut o := o
  let mut posResetSource : NavEKF3_core.resetDataSource := NavEKF3_core.resetDataSource.DEFAULT
  let mut velResetSource : NavEKF3_core.resetDataSource := NavEKF3_core.resetDataSource.DEFAULT
  s := { s with PV_AidingModePrev := s.PV_AidingMode }
  let (t'1, t'2) := setYawSource s w
  w := t'2
  s := t'1
  s := checkGyroCalStatus s w
  if s.yaw_source_last == AP_NavEKF_Source.SourceYaw.NONE && !s.motorsArmed && s.onGround && UInt32.toInt32 (NavEKF3_core.AidingMode.toInt s.PV_AidingMode) == UInt32.toInt32 (NavEKF3_core.AidingMode.toInt NavEKF3_core.AidingMode.AID_ABSOLUTE) then
    s := { s with PV_AidingMode := NavEKF3_core.AidingMode.AID_NONE }
    s := { s with yawAlignComplete := false }
    s := { s with yawAlignGpsValidCount := Int8.toUInt8 (Int32.toInt8 (0 : Int32)) }
    s := { s with finalInflightYawInit := false }
    s := ResetVelocity s w NavEKF3_core.resetDataSource.DEFAULT
    s := ResetPosition s w NavEKF3_core.resetDataSource.DEFAULT
    s := ResetHeight s w
    for row' in [0:4] do
      let row : UInt8 := Nat.toUInt8 row'
      for col' in [4:24] do
        let col : UInt8 := Nat.toUInt8 col'
        s := { s with Pmut := s.Pmut.set! (UInt8.toNat row * 24 + UInt8.toNat col) (Binary64.ofBits 0x0000000000000000 /- 0.0f -/) }
    for col'2' in [0:4] do
      let col'2 : UInt8 := Nat.toUInt8 col'2'
      for row'2' in [4:24] do
        let row'2 : UInt8 := Nat.toUInt8 row'2'
        s := { s with Pmut := s.Pmut.set! (UInt8.toNat row'2 * 24 + UInt8.toNat col'2) (Binary64.ofBits 0x0000000000000000 /- 0.0f -/) }
    let mut oldBiasVariance : Array Binary64 := Array.replicate 6 (Binary64.ofBits 0x0000000000000000 /- 0.0 -/)  -- uninitialized in C; every element is written before it is read
    for row'3' in [0:6] do
      let row'3 : UInt8 := Nat.toUInt8 row'3'
      oldBiasVariance := oldBiasVariance.set! (UInt8.toNat row'3) (s.Pmut[Int32.toNatClampNeg (UInt32.toInt32 (UInt8.toUInt32 row'3) + (10 : Int32)) * 24 + Int32.toNatClampNeg (UInt32.toInt32 (UInt8.toUInt32 row'3) + (10 : Int32))]!)
    s := zeroStatesVarCov s (Int8.toUInt8 (Int32.toInt8 (10 : Int32))) (Int8.toUInt8 (Int32.toInt8 (15 : Int32)))
    for row'4' in [0:6] do
      let row'4 : UInt8 := Nat.toUInt8 row'4'
      s := { s with Pmut := s.Pmut.set! (Int32.toNatClampNeg (UInt32.toInt32 (UInt8.toUInt32 row'4) + (10 : Int32)) * 24 + Int32.toNatClampNeg (UInt32.toInt32 (UInt8.toUInt32 row'4) + (10 : Int32))) (oldBiasVariance[UInt8.toNat row'4]!) }
  match s.PV_AidingMode with
  | .AID_NONE =>
    if readyToUseGPS s w || readyToUseRangeBeacon || readyToUseExtNav then
      s := { s with PV_AidingMode := NavEKF3_core.AidingMode.AID_ABSOLUTE }
    else if readyToUseBodyOdm s w then
      s := { s with PV_AidingMode := NavEKF3_core.AidingMode.AID_RELATIVE }
  | .AID_RELATIVE =>
    let flowFusionTimeout : Bool := (decide ((s.imuSampleTime_ms - s.prevFlowFuseTime_ms) > Int32.toUInt32 (5000 : Int32)))
    let bodyOdmFusionTimeout : Bool := (decide ((s.imuSampleTime_ms - s.bodyOdm.prevFuseTime_ms) > Int32.toUInt32 (5000 : Int32)))
    if readyToUseGPS s w || readyToUseRangeBeacon || readyToUseExtNav then
      s := { s with PV_AidingMode := NavEKF3_core.AidingMode.AID_ABSOLUTE }
    else if flowFusionTimeout && bodyOdmFusionTimeout then
      s := { s with PV_AidingMode := NavEKF3_core.AidingMode.AID_NONE }
  | .AID_ABSOLUTE =>
    let minTestTime_ms : UInt16 := Estimator_lib.MIN_uint16_t2 w.EKF3.tiltDriftTimeMax_ms (Estimator_lib.MIN_uint16_t2 w.EKF3.posRetryTimeNoVel_ms w.EKF3.posRetryTimeUseVel_ms)
    let optFlowUsed : Bool := (decide (s.imuSampleTime_ms - s.prevFlowFuseTime_ms ≤ UInt16.toUInt32 minTestTime_ms))
    let bodyOdmUsed : Bool := (decide (s.imuSampleTime_ms - s.bodyOdm.prevFuseTime_ms ≤ UInt16.toUInt32 minTestTime_ms))
    let airSpdUsed : Bool := (decide (s.imuSampleTime_ms - s.tas.lastPassTime_ms ≤ UInt16.toUInt32 minTestTime_ms))
    let dragUsed : Bool := (decide (s.imuSampleTime_ms - s.drag.lastPassTime_ms ≤ UInt16.toUInt32 minTestTime_ms))
    let rngBcnUsed : Bool := false
    let posUsed : Bool := (decide (s.imuSampleTime_ms - s.lastGpsPosPassTime_ms ≤ UInt16.toUInt32 minTestTime_ms))
    let gpsVelUsed : Bool := (decide (s.imuSampleTime_ms - s.lastVelPassTime_ms ≤ UInt16.toUInt32 minTestTime_ms))
    let attAiding : Bool := posUsed || gpsVelUsed || optFlowUsed || airSpdUsed || dragUsed || rngBcnUsed || bodyOdmUsed
    s := { s with velAiding := posUsed || gpsVelUsed || optFlowUsed || airSpdUsed || dragUsed || rngBcnUsed || bodyOdmUsed }
    s := { s with windStateIsObservable := !s.inhibitWindStates && (posUsed || gpsVelUsed || optFlowUsed || rngBcnUsed || bodyOdmUsed) }
    if s.windStateIsObservable then
      s := { s with lastAirspeedEstimate := Vector3p.length (Vector3p.op_sub_Vector3p ({ x := s.statesArray[4]!, y := s.statesArray[5]!, z := s.statesArray[6]! } : Vector3p.State) (Vector3p.init_double3 s.statesArray[22]! s.statesArray[23]! (Binary64.ofBits 0x0000000000000000 /- 0.0F -/))) }
      s := { s with lastAspdEstIsValid := true }
    let posAiding : Bool := posUsed || rngBcnUsed
    let mut attAidLossCritical : Bool := false
    if !attAiding then
      attAidLossCritical := (decide (s.imuSampleTime_ms - s.prevFlowFuseTime_ms > UInt16.toUInt32 w.EKF3.tiltDriftTimeMax_ms)) && (decide (s.imuSampleTime_ms - s.tas.lastPassTime_ms > UInt16.toUInt32 w.EKF3.tiltDriftTimeMax_ms)) && (decide (s.imuSampleTime_ms - s.lastGpsPosPassTime_ms > UInt16.toUInt32 w.EKF3.tiltDriftTimeMax_ms)) && (decide (s.imuSampleTime_ms - s.lastVelPassTime_ms > UInt16.toUInt32 w.EKF3.tiltDriftTimeMax_ms))
    let mut posAidLossCritical : Bool := false
    if !posAiding then
      let mut maxLossTime_ms : UInt16 := (0 : UInt16)  -- uninitialized in C++; assigned before every read
      if !s.velAiding then
        maxLossTime_ms := w.EKF3.posRetryTimeNoVel_ms
      else
        maxLossTime_ms := w.EKF3.posRetryTimeUseVel_ms
      posAidLossCritical := (decide (s.imuSampleTime_ms - s.lastGpsPosPassTime_ms > UInt16.toUInt32 maxLossTime_ms))
    if attAidLossCritical then
      s := { s with PV_AidingMode := NavEKF3_core.AidingMode.AID_NONE }
      s := { s with posTimeout := true }
      s := { s with velTimeout := true }
      s := { s with tasTimeout := true }
      s := { s with dragTimeout := true }
      s := { s with gpsIsInUse := false }
    else if posAidLossCritical then
      s := { s with posTimeout := true }
      s := { s with velTimeout := !optFlowUsed && !gpsVelUsed && !bodyOdmUsed }
      s := { s with gpsIsInUse := false }
  if UInt32.toInt32 (NavEKF3_core.AidingMode.toInt s.PV_AidingMode) != UInt32.toInt32 (NavEKF3_core.AidingMode.toInt s.PV_AidingModePrev) then
    match s.PV_AidingMode with
    | .AID_NONE =>
      o := o.push (Output.send_text (4 : UInt32) "EKF3 IMU%u stopped aiding" #[Sum.inl (UInt32.toUInt64 (UInt8.toUInt32 s.imu_index))])
      s := { s with posTimeout := true }
      s := { s with velTimeout := true }
      s := { s with velTestRatio := (Binary64.ofBits 0x0000000000000000 /- 0.0f -/) }
      s := { s with posTestRatio := (Binary64.ofBits 0x0000000000000000 /- 0.0f -/) }
      s := { s with lastKnownPositionNE.x := s.statesArray[7]! }
      s := { s with lastKnownPositionNE.y := s.statesArray[8]! }
      s := { s with meaHgtAtTakeOff := s.baroDataDelayed.hgt }
      s := { s with statesArray := s.statesArray.set! 9 (-s.meaHgtAtTakeOff) }
      s := { s with lastKnownPositionD := Binary64.toBinary32 s.statesArray[9]! }
      s := { s with flowFusionActive := false }
      s := { s with bodyOdm.fusionActive := false }
    | .AID_RELATIVE =>
      o := o.push (Output.send_text (6 : UInt32) "EKF3 IMU%u started relative aiding" #[Sum.inl (UInt32.toUInt64 (UInt8.toUInt32 s.imu_index))])
      if readyToUseBodyOdm s w then
        s := { s with bodyOdm.lastPassTime_ms := s.imuSampleTime_ms }
        s := { s with bodyOdm.prevFuseTime_ms := s.imuSampleTime_ms }
      s := { s with posTimeout := true }
      s := { s with velTimeout := true }
    | .AID_ABSOLUTE =>
      if readyToUseGPS s w then
        posResetSource := NavEKF3_core.resetDataSource.GPS
        velResetSource := NavEKF3_core.resetDataSource.GPS
        o := o.push (Output.send_text (6 : UInt32) "EKF3 IMU%u is using GPS" #[Sum.inl (UInt32.toUInt64 (UInt8.toUInt32 s.imu_index))])
      s := { s with posTimeout := false }
      s := { s with velTimeout := false }
      s := { s with lastGpsPosPassTime_ms := s.imuSampleTime_ms }
      s := { s with lastVelPassTime_ms := s.imuSampleTime_ms }
    s := ResetVelocity s w velResetSource
    s := ResetPosition s w posResetSource
  return (s, w, o)

/-- C++ `void NavEKF3_core::controlFilterModes()`, `AP_NavEKF3/AP_NavEKF3_Control.cpp:12-36`. -/
def controlFilterModes (s : State) (w : World) (o : Outputs) : State × World × Outputs := Id.run do
  let mut s := s
  let mut w := w
  let mut o := o
  s := { s with prevMotorsArmed := s.motorsArmed }
  s := { s with motorsArmed := AP_DAL.get_armed w.heap'AP_DAL[(WPtr.index w.AP_DAL'_singleton)]! }
  if s.motorsArmed && !s.prevMotorsArmed then
    s := { s with timeAtArming_ms := s.imuSampleTime_ms }
  let (t'1, t'2) := detectFlight s w
  w := t'2
  s := t'1
  let (t'3, t'4) := setWindMagStateLearningMode s w
  w := t'4
  s := t'3
  let (t'5, t'6) := checkAttitudeAlignmentStatus s w o
  s := t'5
  o := t'6
  let (t'7, t'8, t'9) := setAidingMode s w o
  w := t'8
  s := t'7
  o := t'9
  return (s, w, o)

end NavEKF3_core

namespace NavEKF3_core

/-- C++ `bool NavEKF3_core::buildTbnZeroYaw(rotationOrder order, Matrix3F & Tbn, ftype * yawAng) const`, `AP_NavEKF3/AP_NavEKF3_MagFusion.cpp:228-251`. -/
def buildTbnZeroYaw (s : State) (order : NavEKF3_core.rotationOrder) (Tbn : Matrix3_double.State) (yawAng'given : Bool) (yawAng : Binary64) : Matrix3_double.State × Binary64 × Bool := Id.run do
  let mut Tbn := Tbn
  let mut yawAng := yawAng
  match order with
  | .TAIT_BRYAN_321 =>
    let mut euler321 : Vector3p.State := Vector3p.init_void
    let (t'1, t'2, t'3) := QuaternionT_double.to_euler_double3 ({ q1 := s.statesArray[0]!, q2 := s.statesArray[1]!, q3 := s.statesArray[2]!, q4 := s.statesArray[3]! } : QuaternionT_double.State) euler321.x euler321.y euler321.z
    euler321 := { euler321 with x := t'1 }
    euler321 := { euler321 with y := t'2 }
    euler321 := { euler321 with z := t'3 }
    Tbn := Matrix3_double.from_euler Tbn euler321.x euler321.y (Binary64.ofBits 0x0000000000000000 /- 0.0f -/)
    if yawAng'given then
      yawAng := euler321.z
    return (Tbn, yawAng, true)
  | .TAIT_BRYAN_312 =>
    let euler312 : Vector3p.State := QuaternionT_double.to_vector312 ({ q1 := s.statesArray[0]!, q2 := s.statesArray[1]!, q3 := s.statesArray[2]!, q4 := s.statesArray[3]! } : QuaternionT_double.State)
    Tbn := Matrix3_double.from_euler312 Tbn euler312.x euler312.y (Binary64.ofBits 0x0000000000000000 /- 0.0f -/)
    if yawAng'given then
      yawAng := euler312.z
    return (Tbn, yawAng, true)

/-- C++ `enum class NavEKF3_core::yawFusionMethod`, `AP_NavEKF3/AP_NavEKF3_core.h:719-726`. -/
inductive yawFusionMethod where
  | MAGNETOMETER
  | GPS
  | GSF
  | STATIC
  | PREDICTED
  | EXTNAV
deriving DecidableEq, Inhabited

/-- The value of each enumerator of `NavEKF3_core::yawFusionMethod` (underlying type `int32_t`). -/
def yawFusionMethod.toInt : yawFusionMethod → Int32
  | .MAGNETOMETER => (0 : Int32)
  | .GPS => (1 : Int32)
  | .GSF => (2 : Int32)
  | .STATIC => (3 : Int32)
  | .PREDICTED => (4 : Int32)
  | .EXTNAV => (5 : Int32)

/-- C++ `bool NavEKF3_core::fuseEulerYaw(yawFusionMethod method)`, `AP_NavEKF3/AP_NavEKF3_MagFusion.cpp:965-1262`. -/
def fuseEulerYaw (s : State) (w : World) (method : NavEKF3_core.yawFusionMethod) : State × World × Bool := Id.run do
  let mut s := s
  let mut w := w
  let mut gsfYaw : Binary64 := (Binary64.ofBits 0x0000000000000000 /- 0.0 -/)  -- uninitialized in C++; assigned before every read
  let mut gsfYawVariance : Binary64 := (Binary64.ofBits 0x0000000000000000 /- 0.0 -/)  -- uninitialized in C++; assigned before every read
  if method == NavEKF3_core.yawFusionMethod.GSF then
    let (t'1, t'2, t'3) := EKFGSF_getYaw s w gsfYaw gsfYawVariance
    gsfYaw := t'1
    gsfYawVariance := t'2
    if !t'3 then
      return (s, w, false)
  let mut R_YAW : Binary64 := (Binary64.ofBits 0x0000000000000000 /- 0.0 -/)  -- uninitialized in C++; assigned before every read
  match method with
  | .GPS =>
    R_YAW := Estimator_lib.sq_double s.gpsYaw.dataDelayed.yawAngErr
  | .GSF =>
    R_YAW := gsfYawVariance
  | .STATIC =>
    R_YAW := Estimator_lib.sq_double s.yawAngDataStatic.yawAngErr
  | _ =>
    R_YAW := Estimator_lib.sq_AP_ParamT_float_4 w.EKF3._yawNoise
  let mut order : NavEKF3_core.rotationOrder := NavEKF3_core.rotationOrder.TAIT_BRYAN_321  -- uninitialized in C++; assigned before every read
  match method with
  | .GPS =>
    order := s.gpsYaw.dataDelayed.order
  | .STATIC =>
    order := s.yawAngDataStatic.order
  | _ =>
    order := if Binary64.abs s.prevTnb.a.z < Binary64.abs s.prevTnb.b.z then NavEKF3_core.rotationOrder.TAIT_BRYAN_321 else NavEKF3_core.rotationOrder.TAIT_BRYAN_312
  let mut yawAngPredicted : Binary64 := (Binary64.ofBits 0x0000000000000000 /- 0.0 -/)  -- uninitialized in C++; assigned before every read
  let mut H_YAW : Array Binary64 := Array.replicate 4 (Binary64.ofBits 0x0000000000000000 /- 0.0 -/)  -- uninitialized in C; every element is written before it is read
  let mut Tbn_zeroYaw : Matrix3_double.State := Matrix3_double.init_void
  if order == NavEKF3_core.rotationOrder.TAIT_BRYAN_321 then
    let mut canUseA : Bool := false
    let SA0 : Binary64 := (Binary64.ofBits 0x4000000000000000 /- 2 -/) * s.statesArray[3]!
    let SA1 : Binary64 := (Binary64.ofBits 0x4000000000000000 /- 2 -/) * s.statesArray[2]!
    let SA2 : Binary64 := SA0 * s.statesArray[0]! + SA1 * s.statesArray[1]!
    let SA3 : Binary64 := Estimator_lib.sq_double s.statesArray[0]! + Estimator_lib.sq_double s.statesArray[1]! - Estimator_lib.sq_double s.statesArray[2]! - Estimator_lib.sq_double s.statesArray[3]!
    let mut SA4 : Binary64 := (Binary64.ofBits 0x0000000000000000 /- 0.0 -/)  -- uninitialized in C++; assigned before every read
    let mut SA5_inv : Binary64 := (Binary64.ofBits 0x0000000000000000 /- 0.0 -/)  -- uninitialized in C++; assigned before every read
    if Estimator_lib.is_positive_double (Estimator_lib.sq_double SA3) then
      SA4 := (Binary64.ofBits 0x3ff0000000000000 /- 1.0F -/) / Estimator_lib.sq_double SA3
      SA5_inv := Estimator_lib.sq_double SA2 * SA4 + (Binary64.ofBits 0x3ff0000000000000 /- 1 -/)
      canUseA := Estimator_lib.is_positive_double (Binary64.abs SA5_inv)
    let mut canUseB : Bool := false
    let SB0 : Binary64 := (Binary64.ofBits 0x4000000000000000 /- 2 -/) * s.statesArray[0]!
    let SB1 : Binary64 := (Binary64.ofBits 0x4000000000000000 /- 2 -/) * s.statesArray[1]!
    let SB2 : Binary64 := SB0 * s.statesArray[3]! + SB1 * s.statesArray[2]!
    let SB4 : Binary64 := Estimator_lib.sq_double s.statesArray[0]! + Estimator_lib.sq_double s.statesArray[1]! - Estimator_lib.sq_double s.statesArray[2]! - Estimator_lib.sq_double s.statesArray[3]!
    let mut SB3 : Binary64 := (Binary64.ofBits 0x0000000000000000 /- 0.0 -/)  -- uninitialized in C++; assigned before every read
    let mut SB5_inv : Binary64 := (Binary64.ofBits 0x0000000000000000 /- 0.0 -/)  -- uninitialized in C++; assigned before every read
    if Estimator_lib.is_positive_double (Estimator_lib.sq_double SB2) then
      SB3 := (Binary64.ofBits 0x3ff0000000000000 /- 1.0F -/) / Estimator_lib.sq_double SB2
      SB5_inv := SB3 * Estimator_lib.sq_double SB4 + (Binary64.ofBits 0x3ff0000000000000 /- 1 -/)
      canUseB := Estimator_lib.is_positive_double (Binary64.abs SB5_inv)
    if canUseA && (!canUseB || decide (Binary64.abs SA5_inv ≥ Binary64.abs SB5_inv)) then
      let SA5 : Binary64 := (Binary64.ofBits 0x3ff0000000000000 /- 1.0F -/) / SA5_inv
      let SA6 : Binary64 := (Binary64.ofBits 0x3ff0000000000000 /- 1.0F -/) / SA3
      let SA7 : Binary64 := SA2 * SA4
      let SA8 : Binary64 := (Binary64.ofBits 0x4000000000000000 /- 2 -/) * SA7
      let SA9 : Binary64 := (Binary64.ofBits 0x4000000000000000 /- 2 -/) * SA6
      H_YAW := H_YAW.set! 0 (SA5 * (SA0 * SA6 - SA8 * s.statesArray[0]!))
      H_YAW := H_YAW.set! 1 (SA5 * (SA1 * SA6 - SA8 * s.statesArray[1]!))
      H_YAW := H_YAW.set! 2 (SA5 * (SA1 * SA7 + SA9 * s.statesArray[1]!))
      H_YAW := H_YAW.set! 3 (SA5 * (SA0 * SA7 + SA9 * s.statesArray[0]!))
    else if canUseB && (!canUseA || decide (Binary64.abs SB5_inv > Binary64.abs SA5_inv)) then
      let SB5 : Binary64 := (Binary64.ofBits 0x3ff0000000000000 /- 1.0F -/) / SB5_inv
      let SB6 : Binary64 := (Binary64.ofBits 0x3ff0000000000000 /- 1.0F -/) / SB2
      let SB7 : Binary64 := SB3 * SB4
      let SB8 : Binary64 := (Binary64.ofBits 0x4000000000000000 /- 2 -/) * SB7
      let SB9 : Binary64 := (Binary64.ofBits 0x4000000000000000 /- 2 -/) * SB6
      H_YAW := H_YAW.set! 0 (-SB5 * (SB0 * SB6 - SB8 * s.statesArray[3]!))
      H_YAW := H_YAW.set! 1 (-SB5 * (SB1 * SB6 - SB8 * s.statesArray[2]!))
      H_YAW := H_YAW.set! 2 (-SB5 * (-SB1 * SB7 - SB9 * s.statesArray[2]!))
      H_YAW := H_YAW.set! 3 (-SB5 * (-SB0 * SB7 - SB9 * s.statesArray[3]!))
    else
      return (s, w, false)
    let (t'4, t'5, t'6) := buildTbnZeroYaw s order Tbn_zeroYaw true yawAngPredicted
    Tbn_zeroYaw := t'4
    yawAngPredicted := t'5
    if !t'6 then
      return (s, w, false)
  else if order == NavEKF3_core.rotationOrder.TAIT_BRYAN_312 then
    let mut canUseA'2 : Bool := false
    let SA0'2 : Binary64 := (Binary64.ofBits 0x4000000000000000 /- 2 -/) * s.statesArray[3]!
    let SA1'2 : Binary64 := (Binary64.ofBits 0x4000000000000000 /- 2 -/) * s.statesArray[2]!
    let SA2'2 : Binary64 := SA0'2 * s.statesArray[0]! - SA1'2 * s.statesArray[1]!
    let SA3'2 : Binary64 := Estimator_lib.sq_double s.statesArray[0]! - Estimator_lib.sq_double s.statesArray[1]! + Estimator_lib.sq_double s.statesArray[2]! - Estimator_lib.sq_double s.statesArray[3]!
    let mut SA4'2 : Binary64 := (Binary64.ofBits 0x0000000000000000 /- 0.0 -/)  -- uninitialized in C++; assigned before every read
    let mut SA5_inv'2 : Binary64 := (Binary64.ofBits 0x0000000000000000 /- 0.0 -/)  -- uninitialized in C++; assigned before every read
    if Estimator_lib.is_positive_double (Estimator_lib.sq_double SA3'2) then
      SA4'2 := (Binary64.ofBits 0x3ff0000000000000 /- 1.0F -/) / Estimator_lib.sq_double SA3'2
      SA5_inv'2 := Estimator_lib.sq_double SA2'2 * SA4'2 + (Binary64.ofBits 0x3ff0000000000000 /- 1 -/)
      canUseA'2 := Estimator_lib.is_positive_double (Binary64.abs SA5_inv'2)
    let mut canUseB'2 : Bool := false
    let SB0'2 : Binary64 := (Binary64.ofBits 0x4000000000000000 /- 2 -/) * s.statesArray[0]!
    let SB1'2 : Binary64 := (Binary64.ofBits 0x4000000000000000 /- 2 -/) * s.statesArray[1]!
    let SB2'2 : Binary64 := -SB0'2 * s.statesArray[3]! + SB1'2 * s.statesArray[2]!
    let SB4'2 : Binary64 := -(Estimator_lib.sq_double s.statesArray[0]!) + Estimator_lib.sq_double s.statesArray[1]! - Estimator_lib.sq_double s.statesArray[2]! + Estimator_lib.sq_double s.statesArray[3]!
    let mut SB3'2 : Binary64 := (Binary64.ofBits 0x0000000000000000 /- 0.0 -/)  -- uninitialized in C++; assigned before every read
    let mut SB5_inv'2 : Binary64 := (Binary64.ofBits 0x0000000000000000 /- 0.0 -/)  -- uninitialized in C++; assigned before every read
    if Estimator_lib.is_positive_double (Estimator_lib.sq_double SB2'2) then
      SB3'2 := (Binary64.ofBits 0x3ff0000000000000 /- 1.0F -/) / Estimator_lib.sq_double SB2'2
      SB5_inv'2 := SB3'2 * Estimator_lib.sq_double SB4'2 + (Binary64.ofBits 0x3ff0000000000000 /- 1 -/)
      canUseB'2 := Estimator_lib.is_positive_double (Binary64.abs SB5_inv'2)
    if canUseA'2 && (!canUseB'2 || decide (Binary64.abs SA5_inv'2 ≥ Binary64.abs SB5_inv'2)) then
      let SA5'2 : Binary64 := (Binary64.ofBits 0x3ff0000000000000 /- 1.0F -/) / SA5_inv'2
      let SA6'2 : Binary64 := (Binary64.ofBits 0x3ff0000000000000 /- 1.0F -/) / SA3'2
      let SA7'2 : Binary64 := SA2'2 * SA4'2
      let SA8'2 : Binary64 := (Binary64.ofBits 0x4000000000000000 /- 2 -/) * SA7'2
      let SA9'2 : Binary64 := (Binary64.ofBits 0x4000000000000000 /- 2 -/) * SA6'2
      H_YAW := H_YAW.set! 0 (SA5'2 * (SA0'2 * SA6'2 - SA8'2 * s.statesArray[0]!))
      H_YAW := H_YAW.set! 1 (SA5'2 * (-SA1'2 * SA6'2 + SA8'2 * s.statesArray[1]!))
      H_YAW := H_YAW.set! 2 (SA5'2 * (-SA1'2 * SA7'2 - SA9'2 * s.statesArray[1]!))
      H_YAW := H_YAW.set! 3 (SA5'2 * (SA0'2 * SA7'2 + SA9'2 * s.statesArray[0]!))
    else if canUseB'2 && (!canUseA'2 || decide (Binary64.abs SB5_inv'2 > Binary64.abs SA5_inv'2)) then
      let SB5'2 : Binary64 := (Binary64.ofBits 0x3ff0000000000000 /- 1.0F -/) / SB5_inv'2
      let SB6'2 : Binary64 := (Binary64.ofBits 0x3ff0000000000000 /- 1.0F -/) / SB2'2
      let SB7'2 : Binary64 := SB3'2 * SB4'2
      let SB8'2 : Binary64 := (Binary64.ofBits 0x4000000000000000 /- 2 -/) * SB7'2
      let SB9'2 : Binary64 := (Binary64.ofBits 0x4000000000000000 /- 2 -/) * SB6'2
      H_YAW := H_YAW.set! 0 (-SB5'2 * (-SB0'2 * SB6'2 + SB8'2 * s.statesArray[3]!))
      H_YAW := H_YAW.set! 1 (-SB5'2 * (SB1'2 * SB6'2 - SB8'2 * s.statesArray[2]!))
      H_YAW := H_YAW.set! 2 (-SB5'2 * (-SB1'2 * SB7'2 - SB9'2 * s.statesArray[2]!))
      H_YAW := H_YAW.set! 3 (-SB5'2 * (SB0'2 * SB7'2 + SB9'2 * s.statesArray[3]!))
    else
      return (s, w, false)
    let (t'7, t'8, t'9) := buildTbnZeroYaw s order Tbn_zeroYaw true yawAngPredicted
    Tbn_zeroYaw := t'7
    yawAngPredicted := t'8
    if !t'9 then
      return (s, w, false)
  else
    return (s, w, false)
  match method with
  | .MAGNETOMETER =>
    let magMeasNED : Vector3p.State := Matrix3_double.op_mul_Vector3p Tbn_zeroYaw s.magDataDelayed.mag
    let yawAngMeasured : Binary64 := Estimator_lib.wrap_PI_double (-(Musl.atan2.atan2 magMeasNED.y magMeasNED.x) + MagDeclination s w)
    s := { s with innovYaw := Estimator_lib.wrap_PI_double (yawAngPredicted - yawAngMeasured) }
  | .GPS =>
    s := { s with innovYaw := Estimator_lib.wrap_PI_double (yawAngPredicted - s.gpsYaw.dataDelayed.yawAng) }
  | .STATIC =>
    s := { s with innovYaw := Estimator_lib.wrap_PI_double (yawAngPredicted - s.yawAngDataStatic.yawAng) }
  | .GSF =>
    s := { s with innovYaw := Estimator_lib.wrap_PI_double (yawAngPredicted - gsfYaw) }
  | _ =>
    s := { s with innovYaw := (Binary64.ofBits 0x0000000000000000 /- 0.0f -/) }
  let mut PH : Array Binary64 := Array.replicate 4 (Binary64.ofBits 0x0000000000000000 /- 0.0 -/)  -- uninitialized in C; every element is written before it is read
  let mut varInnov : Binary64 := R_YAW
  for rowIndex' in [0:4] do
    let rowIndex : UInt8 := Nat.toUInt8 rowIndex'
    PH := PH.set! (UInt8.toNat rowIndex) (Binary64.ofBits 0x0000000000000000 /- 0.0f -/)
    for colIndex' in [0:4] do
      let colIndex : UInt8 := Nat.toUInt8 colIndex'
      PH := PH.set! (UInt8.toNat rowIndex) (PH[UInt8.toNat rowIndex]! + s.Pmut[UInt8.toNat rowIndex * 24 + UInt8.toNat colIndex]! * H_YAW[UInt8.toNat colIndex]!)
    varInnov := varInnov + H_YAW[UInt8.toNat rowIndex]! * PH[UInt8.toNat rowIndex]!
  let mut varInnovInv : Binary64 := (Binary64.ofBits 0x0000000000000000 /- 0.0 -/)  -- uninitialized in C++; assigned before every read
  if varInnov ≥ R_YAW then
    varInnovInv := (Binary64.ofBits 0x3ff0000000000000 /- 1.0f -/) / varInnov
    s := { s with faultStatus.bad_yaw := false }
  else
    let (t'10, t'11) := CovarianceInit s w
    w := t'11
    s := t'10
    s := { s with faultStatus.bad_yaw := true }
    return (s, w, false)
  let t'12 : UInt8 := Int8.toUInt8 (Int32.toInt8 (0 : Int32))
  let t'13 : Int32 := UInt32.toInt32 (UInt8.toUInt32 s.stateIndexLim)
  for rowIndex'2' in [0:(t'13.toInt - (Int.ofNat t'12.toNat) + 1).toNat] do  -- C++ loop bounded by a runtime value (--runtime-loops)
    let rowIndex'2 : UInt8 := t'12 + Nat.toUInt8 rowIndex'2'
    w := { w with NavEKF_core_common'Kfusion := w.NavEKF_core_common'Kfusion.set! (UInt8.toNat rowIndex'2) (Binary64.ofBits 0x0000000000000000 /- 0.0f -/) }
    for colIndex'2' in [0:4] do
      let colIndex'2 : UInt8 := Nat.toUInt8 colIndex'2'
      w := { w with NavEKF_core_common'Kfusion := w.NavEKF_core_common'Kfusion.set! (UInt8.toNat rowIndex'2) (w.NavEKF_core_common'Kfusion[UInt8.toNat rowIndex'2]! + s.Pmut[UInt8.toNat rowIndex'2 * 24 + UInt8.toNat colIndex'2]! * H_YAW[UInt8.toNat colIndex'2]!) }
    w := { w with NavEKF_core_common'Kfusion := w.NavEKF_core_common'Kfusion.set! (UInt8.toNat rowIndex'2) (w.NavEKF_core_common'Kfusion[UInt8.toNat rowIndex'2]! * varInnovInv) }
  s := { s with yawTestRatio := Estimator_lib.sq_double s.innovYaw / (Estimator_lib.sq_double (Estimator_lib.MAX_double_float ((Binary64.ofBits 0x3f847ae140000000 /- 0.01f -/) * Int16.toBinary64 (AP_ParamT_short_2.op_to_short w.EKF3._yawInnovGate)) (Binary32.ofBits 0x3f800000 /- 1.0f -/)) * varInnov) }
  if s.yawTestRatio > (Binary64.ofBits 0x3ff0000000000000 /- 1.0f -/) then
    s := { s with magHealth := false }
    if s.inFlight then
      return (s, w, false)
  else
    s := { s with magHealth := true }
  let t'14 : UInt32 := Int32.toUInt32 (0 : Int32)
  let t'15 : UInt32 := UInt8.toUInt32 s.stateIndexLim
  for i' in [0:((Int.ofNat t'15.toNat) - (Int.ofNat t'14.toNat) + 1).toNat] do  -- C++ loop bounded by a runtime value (--runtime-loops)
    let i : UInt32 := t'14 + Nat.toUInt32 i'
    let t'16 : UInt32 := Int32.toUInt32 (0 : Int32)
    let t'17 : UInt32 := UInt8.toUInt32 s.stateIndexLim
    for j' in [0:((Int.ofNat t'17.toNat) - (Int.ofNat t'16.toNat) + 1).toNat] do  -- C++ loop bounded by a runtime value (--runtime-loops)
      let j : UInt32 := t'16 + Nat.toUInt32 j'
      let mut res : Binary64 := (Binary64.ofBits 0x0000000000000000 /- 0 -/)
      res := res + (w.NavEKF_core_common'Kfusion[UInt32.toNat i]! * H_YAW[0]!) * s.Pmut[UInt32.toNat j]!
      res := res + (w.NavEKF_core_common'Kfusion[UInt32.toNat i]! * H_YAW[1]!) * s.Pmut[24 + UInt32.toNat j]!
      res := res + (w.NavEKF_core_common'Kfusion[UInt32.toNat i]! * H_YAW[2]!) * s.Pmut[48 + UInt32.toNat j]!
      res := res + (w.NavEKF_core_common'Kfusion[UInt32.toNat i]! * H_YAW[3]!) * s.Pmut[72 + UInt32.toNat j]!
      w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! (UInt32.toNat i * 24 + UInt32.toNat j) res }
  let innovFusion : Binary64 := Estimator_lib.constrain_value_line_double s.innovYaw (Binary64.ofBits 0xbfe0000000000000 /- (double)-1/2 -/) (Binary64.ofBits 0x3fe0000000000000 /- (double)1/2 -/) (Int32.toUInt32 (1257 : Int32))
  let (t'18, t'19) := FinishFusion s w innovFusion false
  s := t'18
  s := { s with faultStatus.bad_yaw := t'19 }
  return (s, w, true)

/-- C++ `void NavEKF3_core::alignYawAngle(const yaw_elements & yawAngData)`, `AP_NavEKF3/AP_NavEKF3_MagFusion.cpp:322-329`. -/
def alignYawAngle (s : State) (w : World) (o : Outputs) (yawAngData : NavEKF3_core.yaw_elements) : State × World × Outputs := Id.run do
  let mut s := s
  let mut w := w
  let mut o := o
  let (t'1, t'2) := resetQuatStateYawOnly s w yawAngData.yawAng (Estimator_lib.sq_double (Estimator_lib.MAX_double_float yawAngData.yawAngErr (Binary32.ofBits 0x3c23d70a /- 1.0e-2 -/))) yawAngData.order
  w := t'2
  s := t'1
  o := o.push (Output.send_text (6 : UInt32) "EKF3 IMU%u yaw aligned" #[Sum.inl (UInt32.toUInt64 (UInt8.toUInt32 s.imu_index))])
  return (s, w, o)

/-- C++ `bool NavEKF3_core::learnMagBiasFromGPS()`, `AP_NavEKF3/AP_NavEKF3_MagFusion.cpp:1423-1485`. -/
def learnMagBiasFromGPS (s : State) : State × Bool := Id.run do
  let mut s := s
  if !s.have_table_earth_field then
    return (s, false)
  if !s.inFlight then
    return (s, false)
  let mut mag_data : NavEKF3_core.mag_elements := {}
  let (t'1, t'2, t'3) := EKF_obs_buffer_t_NavEKF3_core_mag_elements.recall_mag_elements_uint32_t s.storedMag mag_data s.imuDataDelayed.time_ms
  s := { s with storedMag := t'1 }
  mag_data := t'2
  if !t'3 then
    return (s, false)
  let mut quat : QuaternionT_double.State := ({ q1 := s.statesArray[0]!, q2 := s.statesArray[1]!, q3 := s.statesArray[2]!, q4 := s.statesArray[3]! } : QuaternionT_double.State)
  if s.gpsYaw.dataDelayed.order == NavEKF3_core.rotationOrder.TAIT_BRYAN_321 then
    let mut euler321 : Vector3p.State := Vector3p.init_void
    let (t'4, t'5, t'6) := QuaternionT_double.to_euler_double3 quat euler321.x euler321.y euler321.z
    euler321 := { euler321 with x := t'4 }
    euler321 := { euler321 with y := t'5 }
    euler321 := { euler321 with z := t'6 }
    quat := QuaternionT_double.from_euler_double3 quat euler321.x euler321.y s.gpsYaw.dataDelayed.yawAng
  else if s.gpsYaw.dataDelayed.order == NavEKF3_core.rotationOrder.TAIT_BRYAN_312 then
    let euler312 : Vector3p.State := QuaternionT_double.to_vector312 quat
    quat := QuaternionT_double.from_vector312 quat euler312.x euler312.y s.gpsYaw.dataDelayed.yawAng
  else
    return (s, false)
  let mut dcm : Matrix3_double.State := Matrix3_double.init_void
  dcm := QuaternionT_double.rotation_matrix_Matrix3_double quat dcm
  let expected_body_field : Vector3p.State := Matrix3_double.op_mul_Vector3p (Matrix3_double.transposed dcm) s.table_earth_field_ga
  let err : Vector3p.State := Vector3p.op_add (Vector3p.op_sub_Vector3p expected_body_field mag_data.mag) ({ x := s.statesArray[19]!, y := s.statesArray[20]!, z := s.statesArray[21]! } : Vector3p.State)
  let (t'7, _) := Vector3p.op_sub_assign ({ x := s.statesArray[19]!, y := s.statesArray[20]!, z := s.statesArray[21]! } : Vector3p.State) (Vector3p.op_mul_double err (Binary64.ofBits 0x3f747ae140000000 /- (double)5368709/1073741824 -/))
  s := { s with statesArray := (((s.statesArray.set! 19 t'7.x).set! 20 t'7.y).set! 21 t'7.z) }
  let err_length : Binary64 := Vector3p.length err
  let fallback_count_threshold : UInt8 := Int8.toUInt8 (Int32.toInt8 (50 : Int32))
  if err_length > (Binary64.ofBits 0x3f947ae140000000 /- (double)5368709/268435456 -/) then
    s := { s with gpsYaw.fallbackGoodCounter := Int8.toUInt8 (Int32.toInt8 (0 : Int32)) }
  else if UInt32.toInt32 (UInt8.toUInt32 s.gpsYaw.fallbackGoodCounter) < UInt32.toInt32 (UInt8.toUInt32 fallback_count_threshold) then
    s := { s with gpsYaw.fallbackGoodCounter := s.gpsYaw.fallbackGoodCounter + (1 : UInt8) }
  let ok : Bool := decide (UInt32.toInt32 (UInt8.toUInt32 s.gpsYaw.fallbackGoodCounter) ≥ UInt32.toInt32 (UInt8.toUInt32 fallback_count_threshold))
  if ok then
    s := { s with lastHealthyMagTime_ms := s.imuSampleTime_ms }
  return (s, ok)

end NavEKF3_core

namespace NavEKF3_core

/-- C++ `void NavEKF3_core::setYawFromMag()`, `AP_NavEKF3/AP_NavEKF3_core.cpp:2080-2112`. -/
def setYawFromMag (s : State) (w : World) (o : Outputs) : State × World × Outputs := Id.run do
  let mut s := s
  let mut w := w
  let mut o := o
  if !(use_compass s w) then
    return (s, w, o)
  let (t'1, t'2) := readMagData s w o
  s := t'1
  o := t'2
  let mut order : NavEKF3_core.rotationOrder := NavEKF3_core.rotationOrder.TAIT_BRYAN_321  -- uninitialized in C++; assigned before every read
  order := bestRotationOrder s order
  let mut eulerAngles : Vector3p.State := Vector3p.init_void
  let mut Tbn_zeroYaw : Matrix3_double.State := Matrix3_double.init_void
  if order == NavEKF3_core.rotationOrder.TAIT_BRYAN_321 then
    eulerAngles := QuaternionT_double.to_euler_Vector3p ({ q1 := s.statesArray[0]!, q2 := s.statesArray[1]!, q3 := s.statesArray[2]!, q4 := s.statesArray[3]! } : QuaternionT_double.State) eulerAngles
    Tbn_zeroYaw := Matrix3_double.from_euler Tbn_zeroYaw eulerAngles.x eulerAngles.y (Binary64.ofBits 0x0000000000000000 /- 0.0f -/)
  else if order == NavEKF3_core.rotationOrder.TAIT_BRYAN_312 then
    eulerAngles := QuaternionT_double.to_vector312 ({ q1 := s.statesArray[0]!, q2 := s.statesArray[1]!, q3 := s.statesArray[2]!, q4 := s.statesArray[3]! } : QuaternionT_double.State)
    Tbn_zeroYaw := Matrix3_double.from_euler312 Tbn_zeroYaw eulerAngles.x eulerAngles.y (Binary64.ofBits 0x0000000000000000 /- 0.0f -/)
  else
    return (s, w, o)
  let magMeasNED : Vector3p.State := Matrix3_double.op_mul_Vector3p Tbn_zeroYaw s.magDataDelayed.mag
  let yawAngMeasured : Binary64 := Estimator_lib.wrap_PI_double (-(Musl.atan2.atan2 magMeasNED.y magMeasNED.x) + MagDeclination s w)
  let (t'3, t'4) := resetQuatStateYawOnly s w yawAngMeasured (Binary32.toBinary64 (Estimator_lib.sq_float (Estimator_lib.MAX_AP_ParamT_float_4_float w.EKF3._yawNoise (Binary32.ofBits 0x3c23d70a /- 1.0e-2f -/)))) order
  w := t'4
  s := t'3
  return (s, w, o)

/-- C++ `void NavEKF3_core::recordMagReset()`, `AP_NavEKF3/AP_NavEKF3_MagFusion.cpp:1404-1416`. -/
def recordMagReset (s : State) : State := Id.run do
  let mut s := s
  s := { s with magStateResetRequest := false }
  s := { s with magStateInitComplete := true }
  if s.inFlight then
    s := { s with finalInflightMagInit := true }
  s := { s with posDownAtLastMagReset := s.statesArray[9]! }
  s := { s with quatAtLastMagReset := ({ q1 := s.statesArray[0]!, q2 := s.statesArray[1]!, q3 := s.statesArray[2]!, q4 := s.statesArray[3]! } : QuaternionT_double.State) }
  s := { s with yawInnovAtLastMagReset := s.innovYaw }
  return s

/-- C++ `void NavEKF3_core::resetMagFieldStates()`, `AP_NavEKF3/AP_NavEKF3_core.cpp:2115-2141`. -/
def resetMagFieldStates (s : State) (w : World) : State × World := Id.run do
  let mut s := s
  let mut w := w
  s := { s with prevTnb := QuaternionT_double.rotation_matrix_Matrix3_double (QuaternionT_double.inverse ({ q1 := s.statesArray[0]!, q2 := s.statesArray[1]!, q3 := s.statesArray[2]!, q4 := s.statesArray[3]! } : QuaternionT_double.State)) s.prevTnb }
  if s.have_table_earth_field && decide (Int16.toInt32 (AP_ParamT_short_2.op_to_short w.EKF3._mag_ef_limit) > (0 : Int32)) then
    s := { s with statesArray := (((s.statesArray.set! 16 s.table_earth_field_ga.x).set! 17 s.table_earth_field_ga.y).set! 18 s.table_earth_field_ga.z) }
  else
    let t'1 := Matrix3_double.op_mul_Vector3p (Matrix3_double.transposed s.prevTnb) s.magDataDelayed.mag
    s := { s with statesArray := (((s.statesArray.set! 16 t'1.x).set! 17 t'1.y).set! 18 t'1.z) }
  let (t'2, t'3) := alignMagStateDeclination s w
  w := t'3
  s := t'2
  s := zeroStatesVarCov s (Int8.toUInt8 (Int32.toInt8 (18 : Int32))) (Int8.toUInt8 (Int32.toInt8 (21 : Int32)))
  s := { s with Pmut := s.Pmut.set! 450 (Estimator_lib.sq_AP_ParamT_float_4 w.EKF3._magNoise) }
  s := { s with Pmut := s.Pmut.set! 475 (s.Pmut[450]!) }
  s := { s with Pmut := s.Pmut.set! 500 (s.Pmut[450]!) }
  s := { s with Pmut := s.Pmut.set! 525 (s.Pmut[450]!) }
  s := recordMagReset s
  return (s, w)

/-- C++ `void NavEKF3_core::controlMagYawReset()`, `AP_NavEKF3/AP_NavEKF3_MagFusion.cpp:32-151`. -/
def controlMagYawReset (s : State) (w : World) (o : Outputs) : State × World × Outputs := Id.run do
  let mut s := s
  let mut w := w
  let mut o := o
  if assume_zero_sideslip w && (!s.finalInflightYawInit || !s.yawAlignComplete) && s.inFlight then
    s := { s with gpsYawResetRequest := true }
    return (s, w, o)
  else
    s := { s with gpsYawResetRequest := false }
  let mut deltaRotVecTemp : Vector3p.State := Vector3p.init_void
  let mut deltaQuatTemp : QuaternionT_double.State := QuaternionT_double.init_void
  let mut flightResetAllowed : Bool := false
  let mut initialResetAllowed : Bool := false
  if !s.finalInflightYawInit then
    deltaQuatTemp := QuaternionT_double.op_div ({ q1 := s.statesArray[0]!, q2 := s.statesArray[1]!, q3 := s.statesArray[2]!, q4 := s.statesArray[3]! } : QuaternionT_double.State) s.prevQuatMagReset
    s := { s with prevQuatMagReset := ({ q1 := s.statesArray[0]!, q2 := s.statesArray[1]!, q3 := s.statesArray[2]!, q4 := s.statesArray[3]! } : QuaternionT_double.State) }
    deltaRotVecTemp := QuaternionT_double.to_axis_angle deltaQuatTemp deltaRotVecTemp
    let angRateOK : Bool := decide (Vector3p.length deltaRotVecTemp < (Binary64.ofBits 0x3fc6560420000000 /- 0.1745f -/))
    initialResetAllowed := angRateOK && s.tiltAlignComplete
    flightResetAllowed := angRateOK && !s.onGround
  if s.onGround then
    s := { s with magYawAnomallyCount := Int8.toUInt8 (Int32.toInt8 (0 : Int32)) }
  let mut finalResetRequest : Bool := false
  let mut interimResetRequest : Bool := false
  if flightResetAllowed && !(assume_zero_sideslip w) then
    finalResetRequest := decide ((s.statesArray[9]! - s.posDownAtTakeoff) < (Binary64.ofBits 0xc004000000000000 /- (double)-5/2 -/))
    let hgtIncreasing : Bool := decide ((s.posDownAtLastMagReset - s.statesArray[9]!) > (Binary64.ofBits 0x3fe0000000000000 /- 0.5f -/))
    let yawInnovIncrease : Binary64 := Binary64.abs s.innovYaw - Binary64.abs s.yawInnovAtLastMagReset
    let yawInnovIncreasing : Bool := decide (yawInnovIncrease > (Binary64.ofBits 0x3fd0000000000000 /- 0.25f -/))
    deltaQuatTemp := QuaternionT_double.op_div s.quatAtLastMagReset ({ q1 := s.statesArray[0]!, q2 := s.statesArray[1]!, q3 := s.statesArray[2]!, q4 := s.statesArray[3]! } : QuaternionT_double.State)
    deltaRotVecTemp := QuaternionT_double.to_axis_angle deltaQuatTemp deltaRotVecTemp
    let largeAngleChange : Bool := decide (Vector3p.length deltaRotVecTemp > yawInnovIncrease)
    interimResetRequest := !s.finalInflightYawInit && !finalResetRequest && (decide (UInt32.toInt32 (UInt8.toUInt32 s.magYawAnomallyCount) < (2 : Int32))) && hgtIncreasing && yawInnovIncreasing && !largeAngleChange
  let initialResetRequest : Bool := initialResetAllowed && !s.yawAlignComplete
  s := { s with magYawResetRequest := s.magYawResetRequest || initialResetRequest || interimResetRequest || finalResetRequest }
  if s.magYawResetRequest && use_compass s w then
    if !s.yawAlignComplete then
      o := o.push (Output.send_text (6 : UInt32) "EKF3 IMU%u MAG%u initial yaw alignment complete" #[Sum.inl (UInt32.toUInt64 (UInt8.toUInt32 s.imu_index)), Sum.inl (UInt32.toUInt64 (UInt8.toUInt32 s.magSelectIndex))])
    let (t'1, t'2, t'3) := setYawFromMag s w o
    w := t'2
    s := t'1
    o := t'3
    if finalResetRequest then
      o := o.push (Output.send_text (6 : UInt32) "EKF3 IMU%u MAG%u in-flight yaw alignment complete" #[Sum.inl (UInt32.toUInt64 (UInt8.toUInt32 s.imu_index)), Sum.inl (UInt32.toUInt64 (UInt8.toUInt32 s.magSelectIndex))])
    else if interimResetRequest then
      s := { s with magYawAnomallyCount := s.magYawAnomallyCount + (1 : UInt8) }
      o := o.push (Output.send_text (4 : UInt32) "EKF3 IMU%u MAG%u ground mag anomaly, yaw re-aligned" #[Sum.inl (UInt32.toUInt64 (UInt8.toUInt32 s.imu_index)), Sum.inl (UInt32.toUInt64 (UInt8.toUInt32 s.magSelectIndex))])
    if interimResetRequest then
      s := { s with finalInflightYawInit := false }
      s := { s with finalInflightMagInit := false }
    if !s.magFieldLearned then
      let (t'4, t'5) := resetMagFieldStates s w
      w := t'5
      s := t'4
  if s.magStateResetRequest then
    let (t'6, t'7) := resetMagFieldStates s w
    w := t'7
    s := t'6
  return (s, w, o)

/-- C++ `void NavEKF3_core::FuseMagnetometer()`, `AP_NavEKF3/AP_NavEKF3_MagFusion.cpp:615-958`. -/
def FuseMagnetometer (s : State) (w : World) : State × World := Id.run do
  let mut s := s
  let mut w := w
  let q0 : Binary64 := s.statesArray[0]!
  let q1 : Binary64 := s.statesArray[1]!
  let q2 : Binary64 := s.statesArray[2]!
  let q3 : Binary64 := s.statesArray[3]!
  let magN : Binary64 := s.statesArray[16]!
  let magE : Binary64 := s.statesArray[17]!
  let magD : Binary64 := s.statesArray[18]!
  let magXbias : Binary64 := s.statesArray[19]!
  let magYbias : Binary64 := s.statesArray[20]!
  let magZbias : Binary64 := s.statesArray[21]!
  let DCM : Matrix3_double.State := Matrix3_double.init_double9 (q0 * q0 + q1 * q1 - q2 * q2 - q3 * q3) ((Binary64.ofBits 0x4000000000000000 /- 2.0f -/) * (q1 * q2 + q0 * q3)) ((Binary64.ofBits 0x4000000000000000 /- 2.0f -/) * (q1 * q3 - q0 * q2)) ((Binary64.ofBits 0x4000000000000000 /- 2.0f -/) * (q1 * q2 - q0 * q3)) (q0 * q0 - q1 * q1 + q2 * q2 - q3 * q3) ((Binary64.ofBits 0x4000000000000000 /- 2.0f -/) * (q2 * q3 + q0 * q1)) ((Binary64.ofBits 0x4000000000000000 /- 2.0f -/) * (q1 * q3 + q0 * q2)) ((Binary64.ofBits 0x4000000000000000 /- 2.0f -/) * (q2 * q3 - q0 * q1)) (q0 * q0 - q1 * q1 - q2 * q2 + q3 * q3)
  let MagPred : Vector3p.State := Vector3p.init_double3 (DCM.a.x * magN + DCM.a.y * magE + DCM.a.z * magD + magXbias) (DCM.b.x * magN + DCM.b.y * magE + DCM.b.z * magD + magYbias) (DCM.c.x * magN + DCM.c.y * magE + DCM.c.z * magD + magZbias)
  s := { s with innovMag := Vector3p.op_sub_Vector3p MagPred s.magDataDelayed.mag }
  let R_MAG : Binary64 := Estimator_lib.sq_double (Estimator_lib.constrain_value_line_double (AP_ParamT_float_4.op_to_double w.EKF3._magNoise) (Binary64.ofBits 0x3f847ae140000000 /- (double)5368709/536870912 -/) (Binary64.ofBits 0x3fe0000000000000 /- (double)1/2 -/) (Int32.toUInt32 (661 : Int32))) + Estimator_lib.sq_double (Binary32.toBinary64 w.EKF3.magVarRateScale * Vector3p.length s.imuDataDelayed.delAng / s.imuDataDelayed.delAngDT)
  let SH_MAG : Array Binary64 := #[(Binary64.ofBits 0x4000000000000000 /- 2.0f -/) * magD * q3 + (Binary64.ofBits 0x4000000000000000 /- 2.0f -/) * magE * q2 + (Binary64.ofBits 0x4000000000000000 /- 2.0f -/) * magN * q1, (Binary64.ofBits 0x4000000000000000 /- 2.0f -/) * magD * q0 - (Binary64.ofBits 0x4000000000000000 /- 2.0f -/) * magE * q1 + (Binary64.ofBits 0x4000000000000000 /- 2.0f -/) * magN * q2, (Binary64.ofBits 0x4000000000000000 /- 2.0f -/) * magD * q1 + (Binary64.ofBits 0x4000000000000000 /- 2.0f -/) * magE * q0 - (Binary64.ofBits 0x4000000000000000 /- 2.0f -/) * magN * q3, Estimator_lib.sq_double q3, Estimator_lib.sq_double q2, Estimator_lib.sq_double q1, Estimator_lib.sq_double q0, (Binary64.ofBits 0x4000000000000000 /- 2.0f -/) * magN * q0, (Binary64.ofBits 0x4000000000000000 /- 2.0f -/) * magE * q3]
  s := { s with varInnovMag.x := (s.Pmut[475]! + R_MAG + s.Pmut[43]! * SH_MAG[0]! - s.Pmut[67]! * SH_MAG[1]! + s.Pmut[91]! * SH_MAG[2]! - s.Pmut[403]! * (SH_MAG[3]! + SH_MAG[4]! - SH_MAG[5]! - SH_MAG[6]!) + ((Binary64.ofBits 0x4000000000000000 /- 2.0f -/) * q0 * q3 + (Binary64.ofBits 0x4000000000000000 /- 2.0f -/) * q1 * q2) * (s.Pmut[473]! + s.Pmut[41]! * SH_MAG[0]! - s.Pmut[65]! * SH_MAG[1]! + s.Pmut[89]! * SH_MAG[2]! - s.Pmut[401]! * (SH_MAG[3]! + SH_MAG[4]! - SH_MAG[5]! - SH_MAG[6]!) + s.Pmut[425]! * ((Binary64.ofBits 0x4000000000000000 /- 2.0f -/) * q0 * q3 + (Binary64.ofBits 0x4000000000000000 /- 2.0f -/) * q1 * q2) - s.Pmut[449]! * ((Binary64.ofBits 0x4000000000000000 /- 2.0f -/) * q0 * q2 - (Binary64.ofBits 0x4000000000000000 /- 2.0f -/) * q1 * q3) + s.Pmut[17]! * (SH_MAG[7]! + SH_MAG[8]! - (Binary64.ofBits 0x4000000000000000 /- 2.0f -/) * magD * q2)) - ((Binary64.ofBits 0x4000000000000000 /- 2.0f -/) * q0 * q2 - (Binary64.ofBits 0x4000000000000000 /- 2.0f -/) * q1 * q3) * (s.Pmut[474]! + s.Pmut[42]! * SH_MAG[0]! - s.Pmut[66]! * SH_MAG[1]! + s.Pmut[90]! * SH_MAG[2]! - s.Pmut[402]! * (SH_MAG[3]! + SH_MAG[4]! - SH_MAG[5]! - SH_MAG[6]!) + s.Pmut[426]! * ((Binary64.ofBits 0x4000000000000000 /- 2.0f -/) * q0 * q3 + (Binary64.ofBits 0x4000000000000000 /- 2.0f -/) * q1 * q2) - s.Pmut[450]! * ((Binary64.ofBits 0x4000000000000000 /- 2.0f -/) * q0 * q2 - (Binary64.ofBits 0x4000000000000000 /- 2.0f -/) * q1 * q3) + s.Pmut[18]! * (SH_MAG[7]! + SH_MAG[8]! - (Binary64.ofBits 0x4000000000000000 /- 2.0f -/) * magD * q2)) + (SH_MAG[7]! + SH_MAG[8]! - (Binary64.ofBits 0x4000000000000000 /- 2.0f -/) * magD * q2) * (s.Pmut[456]! + s.Pmut[24]! * SH_MAG[0]! - s.Pmut[48]! * SH_MAG[1]! + s.Pmut[72]! * SH_MAG[2]! - s.Pmut[384]! * (SH_MAG[3]! + SH_MAG[4]! - SH_MAG[5]! - SH_MAG[6]!) + s.Pmut[408]! * ((Binary64.ofBits 0x4000000000000000 /- 2.0f -/) * q0 * q3 + (Binary64.ofBits 0x4000000000000000 /- 2.0f -/) * q1 * q2) - s.Pmut[432]! * ((Binary64.ofBits 0x4000000000000000 /- 2.0f -/) * q0 * q2 - (Binary64.ofBits 0x4000000000000000 /- 2.0f -/) * q1 * q3) + s.Pmut[0]! * (SH_MAG[7]! + SH_MAG[8]! - (Binary64.ofBits 0x4000000000000000 /- 2.0f -/) * magD * q2)) + s.Pmut[427]! * ((Binary64.ofBits 0x4000000000000000 /- 2.0f -/) * q0 * q3 + (Binary64.ofBits 0x4000000000000000 /- 2.0f -/) * q1 * q2) - s.Pmut[451]! * ((Binary64.ofBits 0x4000000000000000 /- 2.0f -/) * q0 * q2 - (Binary64.ofBits 0x4000000000000000 /- 2.0f -/) * q1 * q3) + SH_MAG[0]! * (s.Pmut[457]! + s.Pmut[25]! * SH_MAG[0]! - s.Pmut[49]! * SH_MAG[1]! + s.Pmut[73]! * SH_MAG[2]! - s.Pmut[385]! * (SH_MAG[3]! + SH_MAG[4]! - SH_MAG[5]! - SH_MAG[6]!) + s.Pmut[409]! * ((Binary64.ofBits 0x4000000000000000 /- 2.0f -/) * q0 * q3 + (Binary64.ofBits 0x4000000000000000 /- 2.0f -/) * q1 * q2) - s.Pmut[433]! * ((Binary64.ofBits 0x4000000000000000 /- 2.0f -/) * q0 * q2 - (Binary64.ofBits 0x4000000000000000 /- 2.0f -/) * q1 * q3) + s.Pmut[1]! * (SH_MAG[7]! + SH_MAG[8]! - (Binary64.ofBits 0x4000000000000000 /- 2.0f -/) * magD * q2)) - SH_MAG[1]! * (s.Pmut[458]! + s.Pmut[26]! * SH_MAG[0]! - s.Pmut[50]! * SH_MAG[1]! + s.Pmut[74]! * SH_MAG[2]! - s.Pmut[386]! * (SH_MAG[3]! + SH_MAG[4]! - SH_MAG[5]! - SH_MAG[6]!) + s.Pmut[410]! * ((Binary64.ofBits 0x4000000000000000 /- 2.0f -/) * q0 * q3 + (Binary64.ofBits 0x4000000000000000 /- 2.0f -/) * q1 * q2) - s.Pmut[434]! * ((Binary64.ofBits 0x4000000000000000 /- 2.0f -/) * q0 * q2 - (Binary64.ofBits 0x4000000000000000 /- 2.0f -/) * q1 * q3) + s.Pmut[2]! * (SH_MAG[7]! + SH_MAG[8]! - (Binary64.ofBits 0x4000000000000000 /- 2.0f -/) * magD * q2)) + SH_MAG[2]! * (s.Pmut[459]! + s.Pmut[27]! * SH_MAG[0]! - s.Pmut[51]! * SH_MAG[1]! + s.Pmut[75]! * SH_MAG[2]! - s.Pmut[387]! * (SH_MAG[3]! + SH_MAG[4]! - SH_MAG[5]! - SH_MAG[6]!) + s.Pmut[411]! * ((Binary64.ofBits 0x4000000000000000 /- 2.0f -/) * q0 * q3 + (Binary64.ofBits 0x4000000000000000 /- 2.0f -/) * q1 * q2) - s.Pmut[435]! * ((Binary64.ofBits 0x4000000000000000 /- 2.0f -/) * q0 * q2 - (Binary64.ofBits 0x4000000000000000 /- 2.0f -/) * q1 * q3) + s.Pmut[3]! * (SH_MAG[7]! + SH_MAG[8]! - (Binary64.ofBits 0x4000000000000000 /- 2.0f -/) * magD * q2)) - (SH_MAG[3]! + SH_MAG[4]! - SH_MAG[5]! - SH_MAG[6]!) * (s.Pmut[472]! + s.Pmut[40]! * SH_MAG[0]! - s.Pmut[64]! * SH_MAG[1]! + s.Pmut[88]! * SH_MAG[2]! - s.Pmut[400]! * (SH_MAG[3]! + SH_MAG[4]! - SH_MAG[5]! - SH_MAG[6]!) + s.Pmut[424]! * ((Binary64.ofBits 0x4000000000000000 /- 2.0f -/) * q0 * q3 + (Binary64.ofBits 0x4000000000000000 /- 2.0f -/) * q1 * q2) - s.Pmut[448]! * ((Binary64.ofBits 0x4000000000000000 /- 2.0f -/) * q0 * q2 - (Binary64.ofBits 0x4000000000000000 /- 2.0f -/) * q1 * q3) + s.Pmut[16]! * (SH_MAG[7]! + SH_MAG[8]! - (Binary64.ofBits 0x4000000000000000 /- 2.0f -/) * magD * q2)) + s.Pmut[19]! * (SH_MAG[7]! + SH_MAG[8]! - (Binary64.ofBits 0x4000000000000000 /- 2.0f -/) * magD * q2)) }
  if s.varInnovMag.x ≥ R_MAG then
    s := { s with faultStatus.bad_xmag := false }
  else
    let (t'1, t'2) := CovarianceInit s w
    w := t'2
    s := t'1
    s := { s with faultStatus.bad_xmag := true }
    return (s, w)
  s := { s with varInnovMag.y := (s.Pmut[500]! + R_MAG + s.Pmut[20]! * SH_MAG[2]! + s.Pmut[44]! * SH_MAG[1]! + s.Pmut[68]! * SH_MAG[0]! - s.Pmut[428]! * (SH_MAG[3]! - SH_MAG[4]! + SH_MAG[5]! - SH_MAG[6]!) - ((Binary64.ofBits 0x4000000000000000 /- 2.0f -/) * q0 * q3 - (Binary64.ofBits 0x4000000000000000 /- 2.0f -/) * q1 * q2) * (s.Pmut[496]! + s.Pmut[16]! * SH_MAG[2]! + s.Pmut[40]! * SH_MAG[1]! + s.Pmut[64]! * SH_MAG[0]! - s.Pmut[424]! * (SH_MAG[3]! - SH_MAG[4]! + SH_MAG[5]! - SH_MAG[6]!) - s.Pmut[400]! * ((Binary64.ofBits 0x4000000000000000 /- 2.0f -/) * q0 * q3 - (Binary64.ofBits 0x4000000000000000 /- 2.0f -/) * q1 * q2) + s.Pmut[448]! * ((Binary64.ofBits 0x4000000000000000 /- 2.0f -/) * q0 * q1 + (Binary64.ofBits 0x4000000000000000 /- 2.0f -/) * q2 * q3) - s.Pmut[88]! * (SH_MAG[7]! + SH_MAG[8]! - (Binary64.ofBits 0x4000000000000000 /- 2.0f -/) * magD * q2)) + ((Binary64.ofBits 0x4000000000000000 /- 2.0f -/) * q0 * q1 + (Binary64.ofBits 0x4000000000000000 /- 2.0f -/) * q2 * q3) * (s.Pmut[498]! + s.Pmut[18]! * SH_MAG[2]! + s.Pmut[42]! * SH_MAG[1]! + s.Pmut[66]! * SH_MAG[0]! - s.Pmut[426]! * (SH_MAG[3]! - SH_MAG[4]! + SH_MAG[5]! - SH_MAG[6]!) - s.Pmut[402]! * ((Binary64.ofBits 0x4000000000000000 /- 2.0f -/) * q0 * q3 - (Binary64.ofBits 0x4000000000000000 /- 2.0f -/) * q1 * q2) + s.Pmut[450]! * ((Binary64.ofBits 0x4000000000000000 /- 2.0f -/) * q0 * q1 + (Binary64.ofBits 0x4000000000000000 /- 2.0f -/) * q2 * q3) - s.Pmut[90]! * (SH_MAG[7]! + SH_MAG[8]! - (Binary64.ofBits 0x4000000000000000 /- 2.0f -/) * magD * q2)) - (SH_MAG[7]! + SH_MAG[8]! - (Binary64.ofBits 0x4000000000000000 /- 2.0f -/) * magD * q2) * (s.Pmut[483]! + s.Pmut[3]! * SH_MAG[2]! + s.Pmut[27]! * SH_MAG[1]! + s.Pmut[51]! * SH_MAG[0]! - s.Pmut[411]! * (SH_MAG[3]! - SH_MAG[4]! + SH_MAG[5]! - SH_MAG[6]!) - s.Pmut[387]! * ((Binary64.ofBits 0x4000000000000000 /- 2.0f -/) * q0 * q3 - (Binary64.ofBits 0x4000000000000000 /- 2.0f -/) * q1 * q2) + s.Pmut[435]! * ((Binary64.ofBits 0x4000000000000000 /- 2.0f -/) * q0 * q1 + (Binary64.ofBits 0x4000000000000000 /- 2.0f -/) * q2 * q3) - s.Pmut[75]! * (SH_MAG[7]! + SH_MAG[8]! - (Binary64.ofBits 0x4000000000000000 /- 2.0f -/) * magD * q2)) - s.Pmut[404]! * ((Binary64.ofBits 0x4000000000000000 /- 2.0f -/) * q0 * q3 - (Binary64.ofBits 0x4000000000000000 /- 2.0f -/) * q1 * q2) + s.Pmut[452]! * ((Binary64.ofBits 0x4000000000000000 /- 2.0f -/) * q0 * q1 + (Binary64.ofBits 0x4000000000000000 /- 2.0f -/) * q2 * q3) + SH_MAG[2]! * (s.Pmut[480]! + s.Pmut[0]! * SH_MAG[2]! + s.Pmut[24]! * SH_MAG[1]! + s.Pmut[48]! * SH_MAG[0]! - s.Pmut[408]! * (SH_MAG[3]! - SH_MAG[4]! + SH_MAG[5]! - SH_MAG[6]!) - s.Pmut[384]! * ((Binary64.ofBits 0x4000000000000000 /- 2.0f -/) * q0 * q3 - (Binary64.ofBits 0x4000000000000000 /- 2.0f -/) * q1 * q2) + s.Pmut[432]! * ((Binary64.ofBits 0x4000000000000000 /- 2.0f -/) * q0 * q1 + (Binary64.ofBits 0x4000000000000000 /- 2.0f -/) * q2 * q3) - s.Pmut[72]! * (SH_MAG[7]! + SH_MAG[8]! - (Binary64.ofBits 0x4000000000000000 /- 2.0f -/) * magD * q2)) + SH_MAG[1]! * (s.Pmut[481]! + s.Pmut[1]! * SH_MAG[2]! + s.Pmut[25]! * SH_MAG[1]! + s.Pmut[49]! * SH_MAG[0]! - s.Pmut[409]! * (SH_MAG[3]! - SH_MAG[4]! + SH_MAG[5]! - SH_MAG[6]!) - s.Pmut[385]! * ((Binary64.ofBits 0x4000000000000000 /- 2.0f -/) * q0 * q3 - (Binary64.ofBits 0x4000000000000000 /- 2.0f -/) * q1 * q2) + s.Pmut[433]! * ((Binary64.ofBits 0x4000000000000000 /- 2.0f -/) * q0 * q1 + (Binary64.ofBits 0x4000000000000000 /- 2.0f -/) * q2 * q3) - s.Pmut[73]! * (SH_MAG[7]! + SH_MAG[8]! - (Binary64.ofBits 0x4000000000000000 /- 2.0f -/) * magD * q2)) + SH_MAG[0]! * (s.Pmut[482]! + s.Pmut[2]! * SH_MAG[2]! + s.Pmut[26]! * SH_MAG[1]! + s.Pmut[50]! * SH_MAG[0]! - s.Pmut[410]! * (SH_MAG[3]! - SH_MAG[4]! + SH_MAG[5]! - SH_MAG[6]!) - s.Pmut[386]! * ((Binary64.ofBits 0x4000000000000000 /- 2.0f -/) * q0 * q3 - (Binary64.ofBits 0x4000000000000000 /- 2.0f -/) * q1 * q2) + s.Pmut[434]! * ((Binary64.ofBits 0x4000000000000000 /- 2.0f -/) * q0 * q1 + (Binary64.ofBits 0x4000000000000000 /- 2.0f -/) * q2 * q3) - s.Pmut[74]! * (SH_MAG[7]! + SH_MAG[8]! - (Binary64.ofBits 0x4000000000000000 /- 2.0f -/) * magD * q2)) - (SH_MAG[3]! - SH_MAG[4]! + SH_MAG[5]! - SH_MAG[6]!) * (s.Pmut[497]! + s.Pmut[17]! * SH_MAG[2]! + s.Pmut[41]! * SH_MAG[1]! + s.Pmut[65]! * SH_MAG[0]! - s.Pmut[425]! * (SH_MAG[3]! - SH_MAG[4]! + SH_MAG[5]! - SH_MAG[6]!) - s.Pmut[401]! * ((Binary64.ofBits 0x4000000000000000 /- 2.0f -/) * q0 * q3 - (Binary64.ofBits 0x4000000000000000 /- 2.0f -/) * q1 * q2) + s.Pmut[449]! * ((Binary64.ofBits 0x4000000000000000 /- 2.0f -/) * q0 * q1 + (Binary64.ofBits 0x4000000000000000 /- 2.0f -/) * q2 * q3) - s.Pmut[89]! * (SH_MAG[7]! + SH_MAG[8]! - (Binary64.ofBits 0x4000000000000000 /- 2.0f -/) * magD * q2)) - s.Pmut[92]! * (SH_MAG[7]! + SH_MAG[8]! - (Binary64.ofBits 0x4000000000000000 /- 2.0f -/) * magD * q2)) }
  if s.varInnovMag.y ≥ R_MAG then
    s := { s with faultStatus.bad_ymag := false }
  else
    let (t'3, t'4) := CovarianceInit s w
    w := t'4
    s := t'3
    s := { s with faultStatus.bad_ymag := true }
    return (s, w)
  s := { s with varInnovMag.z := (s.Pmut[525]! + R_MAG + s.Pmut[21]! * SH_MAG[1]! - s.Pmut[45]! * SH_MAG[2]! + s.Pmut[93]! * SH_MAG[0]! + s.Pmut[453]! * (SH_MAG[3]! - SH_MAG[4]! - SH_MAG[5]! + SH_MAG[6]!) + ((Binary64.ofBits 0x4000000000000000 /- 2.0f -/) * q0 * q2 + (Binary64.ofBits 0x4000000000000000 /- 2.0f -/) * q1 * q3) * (s.Pmut[520]! + s.Pmut[16]! * SH_MAG[1]! - s.Pmut[40]! * SH_MAG[2]! + s.Pmut[88]! * SH_MAG[0]! + s.Pmut[448]! * (SH_MAG[3]! - SH_MAG[4]! - SH_MAG[5]! + SH_MAG[6]!) + s.Pmut[400]! * ((Binary64.ofBits 0x4000000000000000 /- 2.0f -/) * q0 * q2 + (Binary64.ofBits 0x4000000000000000 /- 2.0f -/) * q1 * q3) - s.Pmut[424]! * ((Binary64.ofBits 0x4000000000000000 /- 2.0f -/) * q0 * q1 - (Binary64.ofBits 0x4000000000000000 /- 2.0f -/) * q2 * q3) + s.Pmut[64]! * (SH_MAG[7]! + SH_MAG[8]! - (Binary64.ofBits 0x4000000000000000 /- 2.0f -/) * magD * q2)) - ((Binary64.ofBits 0x4000000000000000 /- 2.0f -/) * q0 * q1 - (Binary64.ofBits 0x4000000000000000 /- 2.0f -/) * q2 * q3) * (s.Pmut[521]! + s.Pmut[17]! * SH_MAG[1]! - s.Pmut[41]! * SH_MAG[2]! + s.Pmut[89]! * SH_MAG[0]! + s.Pmut[449]! * (SH_MAG[3]! - SH_MAG[4]! - SH_MAG[5]! + SH_MAG[6]!) + s.Pmut[401]! * ((Binary64.ofBits 0x4000000000000000 /- 2.0f -/) * q0 * q2 + (Binary64.ofBits 0x4000000000000000 /- 2.0f -/) * q1 * q3) - s.Pmut[425]! * ((Binary64.ofBits 0x4000000000000000 /- 2.0f -/) * q0 * q1 - (Binary64.ofBits 0x4000000000000000 /- 2.0f -/) * q2 * q3) + s.Pmut[65]! * (SH_MAG[7]! + SH_MAG[8]! - (Binary64.ofBits 0x4000000000000000 /- 2.0f -/) * magD * q2)) + (SH_MAG[7]! + SH_MAG[8]! - (Binary64.ofBits 0x4000000000000000 /- 2.0f -/) * magD * q2) * (s.Pmut[506]! + s.Pmut[2]! * SH_MAG[1]! - s.Pmut[26]! * SH_MAG[2]! + s.Pmut[74]! * SH_MAG[0]! + s.Pmut[434]! * (SH_MAG[3]! - SH_MAG[4]! - SH_MAG[5]! + SH_MAG[6]!) + s.Pmut[386]! * ((Binary64.ofBits 0x4000000000000000 /- 2.0f -/) * q0 * q2 + (Binary64.ofBits 0x4000000000000000 /- 2.0f -/) * q1 * q3) - s.Pmut[410]! * ((Binary64.ofBits 0x4000000000000000 /- 2.0f -/) * q0 * q1 - (Binary64.ofBits 0x4000000000000000 /- 2.0f -/) * q2 * q3) + s.Pmut[50]! * (SH_MAG[7]! + SH_MAG[8]! - (Binary64.ofBits 0x4000000000000000 /- 2.0f -/) * magD * q2)) + s.Pmut[405]! * ((Binary64.ofBits 0x4000000000000000 /- 2.0f -/) * q0 * q2 + (Binary64.ofBits 0x4000000000000000 /- 2.0f -/) * q1 * q3) - s.Pmut[429]! * ((Binary64.ofBits 0x4000000000000000 /- 2.0f -/) * q0 * q1 - (Binary64.ofBits 0x4000000000000000 /- 2.0f -/) * q2 * q3) + SH_MAG[1]! * (s.Pmut[504]! + s.Pmut[0]! * SH_MAG[1]! - s.Pmut[24]! * SH_MAG[2]! + s.Pmut[72]! * SH_MAG[0]! + s.Pmut[432]! * (SH_MAG[3]! - SH_MAG[4]! - SH_MAG[5]! + SH_MAG[6]!) + s.Pmut[384]! * ((Binary64.ofBits 0x4000000000000000 /- 2.0f -/) * q0 * q2 + (Binary64.ofBits 0x4000000000000000 /- 2.0f -/) * q1 * q3) - s.Pmut[408]! * ((Binary64.ofBits 0x4000000000000000 /- 2.0f -/) * q0 * q1 - (Binary64.ofBits 0x4000000000000000 /- 2.0f -/) * q2 * q3) + s.Pmut[48]! * (SH_MAG[7]! + SH_MAG[8]! - (Binary64.ofBits 0x4000000000000000 /- 2.0f -/) * magD * q2)) - SH_MAG[2]! * (s.Pmut[505]! + s.Pmut[1]! * SH_MAG[1]! - s.Pmut[25]! * SH_MAG[2]! + s.Pmut[73]! * SH_MAG[0]! + s.Pmut[433]! * (SH_MAG[3]! - SH_MAG[4]! - SH_MAG[5]! + SH_MAG[6]!) + s.Pmut[385]! * ((Binary64.ofBits 0x4000000000000000 /- 2.0f -/) * q0 * q2 + (Binary64.ofBits 0x4000000000000000 /- 2.0f -/) * q1 * q3) - s.Pmut[409]! * ((Binary64.ofBits 0x4000000000000000 /- 2.0f -/) * q0 * q1 - (Binary64.ofBits 0x4000000000000000 /- 2.0f -/) * q2 * q3) + s.Pmut[49]! * (SH_MAG[7]! + SH_MAG[8]! - (Binary64.ofBits 0x4000000000000000 /- 2.0f -/) * magD * q2)) + SH_MAG[0]! * (s.Pmut[507]! + s.Pmut[3]! * SH_MAG[1]! - s.Pmut[27]! * SH_MAG[2]! + s.Pmut[75]! * SH_MAG[0]! + s.Pmut[435]! * (SH_MAG[3]! - SH_MAG[4]! - SH_MAG[5]! + SH_MAG[6]!) + s.Pmut[387]! * ((Binary64.ofBits 0x4000000000000000 /- 2.0f -/) * q0 * q2 + (Binary64.ofBits 0x4000000000000000 /- 2.0f -/) * q1 * q3) - s.Pmut[411]! * ((Binary64.ofBits 0x4000000000000000 /- 2.0f -/) * q0 * q1 - (Binary64.ofBits 0x4000000000000000 /- 2.0f -/) * q2 * q3) + s.Pmut[51]! * (SH_MAG[7]! + SH_MAG[8]! - (Binary64.ofBits 0x4000000000000000 /- 2.0f -/) * magD * q2)) + (SH_MAG[3]! - SH_MAG[4]! - SH_MAG[5]! + SH_MAG[6]!) * (s.Pmut[522]! + s.Pmut[18]! * SH_MAG[1]! - s.Pmut[42]! * SH_MAG[2]! + s.Pmut[90]! * SH_MAG[0]! + s.Pmut[450]! * (SH_MAG[3]! - SH_MAG[4]! - SH_MAG[5]! + SH_MAG[6]!) + s.Pmut[402]! * ((Binary64.ofBits 0x4000000000000000 /- 2.0f -/) * q0 * q2 + (Binary64.ofBits 0x4000000000000000 /- 2.0f -/) * q1 * q3) - s.Pmut[426]! * ((Binary64.ofBits 0x4000000000000000 /- 2.0f -/) * q0 * q1 - (Binary64.ofBits 0x4000000000000000 /- 2.0f -/) * q2 * q3) + s.Pmut[66]! * (SH_MAG[7]! + SH_MAG[8]! - (Binary64.ofBits 0x4000000000000000 /- 2.0f -/) * magD * q2)) + s.Pmut[69]! * (SH_MAG[7]! + SH_MAG[8]! - (Binary64.ofBits 0x4000000000000000 /- 2.0f -/) * magD * q2)) }
  if s.varInnovMag.z ≥ R_MAG then
    s := { s with faultStatus.bad_zmag := false }
  else
    let (t'5, t'6) := CovarianceInit s w
    w := t'6
    s := t'5
    s := { s with faultStatus.bad_zmag := true }
    return (s, w)
  for i' in [0:3] do
    let i : UInt8 := Nat.toUInt8 i'
    let t'7 := Estimator_lib.sq_double (match UInt8.toNat i with | 0 => s.innovMag.x | 1 => s.innovMag.y | _ => s.innovMag.z) / (Estimator_lib.sq_double (Estimator_lib.MAX_double_float ((Binary64.ofBits 0x3f847ae140000000 /- 0.01f -/) * Int16.toBinary64 (AP_ParamT_short_2.op_to_short w.EKF3._magInnovGate)) (Binary32.ofBits 0x3f800000 /- 1.0f -/)) * (match UInt8.toNat i with | 0 => s.varInnovMag.x | 1 => s.varInnovMag.y | _ => s.varInnovMag.z))
    s := (match UInt8.toNat i with | 0 => { s with magTestRatio.x := t'7 } | 1 => { s with magTestRatio.y := t'7 } | _ => { s with magTestRatio.z := t'7 })
  s := { s with magHealth := (decide (s.magTestRatio.x < (Binary64.ofBits 0x3ff0000000000000 /- 1.0f -/)) && decide (s.magTestRatio.y < (Binary64.ofBits 0x3ff0000000000000 /- 1.0f -/)) && decide (s.magTestRatio.z < (Binary64.ofBits 0x3ff0000000000000 /- 1.0f -/))) }
  if !s.magHealth then
    return (s, w)
  let mut H_MAG : Array Binary64 := Array.replicate 24 (Binary64.ofBits 0x0000000000000000 /- 0.0 -/)  -- uninitialized in C; every element is written before it is read
  let mut H_MAG_unit_index : Int32 := (0 : Int32)  -- uninitialized in C++; assigned before every read
  for obsIndex' in [0:3] do
    let obsIndex : UInt8 := Nat.toUInt8 obsIndex'
    if UInt32.toInt32 (UInt8.toUInt32 obsIndex) == (0 : Int32) then
      let t'8 : UInt8 := Int8.toUInt8 (Int32.toInt8 (0 : Int32))
      let t'9 : Int32 := UInt32.toInt32 (UInt8.toUInt32 s.stateIndexLim)
      for i'2' in [0:(t'9.toInt - (Int.ofNat t'8.toNat) + 1).toNat] do  -- C++ loop bounded by a runtime value (--runtime-loops)
        let i'2 : UInt8 := t'8 + Nat.toUInt8 i'2'
        H_MAG := H_MAG.set! (UInt8.toNat i'2) (Binary64.ofBits 0x0000000000000000 /- 0.0f -/)
      H_MAG := H_MAG.set! 0 (SH_MAG[7]! + SH_MAG[8]! - (Binary64.ofBits 0x4000000000000000 /- 2.0f -/) * magD * q2)
      H_MAG := H_MAG.set! 1 (SH_MAG[0]!)
      H_MAG := H_MAG.set! 2 (-SH_MAG[1]!)
      H_MAG := H_MAG.set! 3 (SH_MAG[2]!)
      H_MAG := H_MAG.set! 16 (SH_MAG[5]! - SH_MAG[4]! - SH_MAG[3]! + SH_MAG[6]!)
      H_MAG := H_MAG.set! 17 ((Binary64.ofBits 0x4000000000000000 /- 2.0f -/) * q0 * q3 + (Binary64.ofBits 0x4000000000000000 /- 2.0f -/) * q1 * q2)
      H_MAG := H_MAG.set! 18 ((Binary64.ofBits 0x4000000000000000 /- 2.0f -/) * q1 * q3 - (Binary64.ofBits 0x4000000000000000 /- 2.0f -/) * q0 * q2)
      H_MAG := H_MAG.set! 19 (Binary64.ofBits 0x3ff0000000000000 /- 1.0f -/)
      H_MAG := H_MAG.set! 20 (Binary64.ofBits 0x0000000000000000 /- 0.0f -/)
      H_MAG := H_MAG.set! 21 (Binary64.ofBits 0x0000000000000000 /- 0.0f -/)
      H_MAG_unit_index := (19 : Int32)
      let SK_MX : Array Binary64 := #[(Binary64.ofBits 0x3ff0000000000000 /- 1.0f -/) / s.varInnovMag.x, SH_MAG[3]! + SH_MAG[4]! - SH_MAG[5]! - SH_MAG[6]!, SH_MAG[7]! + SH_MAG[8]! - (Binary64.ofBits 0x4000000000000000 /- 2.0f -/) * magD * q2, (Binary64.ofBits 0x4000000000000000 /- 2.0f -/) * q0 * q2 - (Binary64.ofBits 0x4000000000000000 /- 2.0f -/) * q1 * q3, (Binary64.ofBits 0x4000000000000000 /- 2.0f -/) * q0 * q3 + (Binary64.ofBits 0x4000000000000000 /- 2.0f -/) * q1 * q2]
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
      for i'3' in [0:24] do
        let i'3 : Int32 := Nat.toInt32 i'3'
        let mut res : Binary64 := (Binary64.ofBits 0x0000000000000000 /- 0 -/)
        if kalman_mask &&& Int32.toUInt32 ((1 : Int32) <<< i'3) != (0 : UInt32) then
          res := SK_MX[0]! * (s.Pmut[Int32.toNatClampNeg i'3 * 24 + 19]! + s.Pmut[Int32.toNatClampNeg i'3 * 24 + 1]! * SH_MAG[0]! - s.Pmut[Int32.toNatClampNeg i'3 * 24 + 2]! * SH_MAG[1]! + s.Pmut[Int32.toNatClampNeg i'3 * 24 + 3]! * SH_MAG[2]! + s.Pmut[Int32.toNatClampNeg i'3 * 24]! * SK_MX[2]! - s.Pmut[Int32.toNatClampNeg i'3 * 24 + 16]! * SK_MX[1]! + s.Pmut[Int32.toNatClampNeg i'3 * 24 + 17]! * SK_MX[4]! - s.Pmut[Int32.toNatClampNeg i'3 * 24 + 18]! * SK_MX[3]!)
        w := { w with NavEKF_core_common'Kfusion := w.NavEKF_core_common'Kfusion.set! (Int32.toNatClampNeg i'3) res }
      s := { s with magFusePerformed := true }
    else if UInt32.toInt32 (UInt8.toUInt32 obsIndex) == (1 : Int32) then
      let t'10 : UInt8 := Int8.toUInt8 (Int32.toInt8 (0 : Int32))
      let t'11 : Int32 := UInt32.toInt32 (UInt8.toUInt32 s.stateIndexLim)
      for i'4' in [0:(t'11.toInt - (Int.ofNat t'10.toNat) + 1).toNat] do  -- C++ loop bounded by a runtime value (--runtime-loops)
        let i'4 : UInt8 := t'10 + Nat.toUInt8 i'4'
        H_MAG := H_MAG.set! (UInt8.toNat i'4) (Binary64.ofBits 0x0000000000000000 /- 0.0f -/)
      H_MAG := H_MAG.set! 0 (SH_MAG[2]!)
      H_MAG := H_MAG.set! 1 (SH_MAG[1]!)
      H_MAG := H_MAG.set! 2 (SH_MAG[0]!)
      H_MAG := H_MAG.set! 3 ((Binary64.ofBits 0x4000000000000000 /- 2.0f -/) * magD * q2 - SH_MAG[8]! - SH_MAG[7]!)
      H_MAG := H_MAG.set! 16 ((Binary64.ofBits 0x4000000000000000 /- 2.0f -/) * q1 * q2 - (Binary64.ofBits 0x4000000000000000 /- 2.0f -/) * q0 * q3)
      H_MAG := H_MAG.set! 17 (SH_MAG[4]! - SH_MAG[3]! - SH_MAG[5]! + SH_MAG[6]!)
      H_MAG := H_MAG.set! 18 ((Binary64.ofBits 0x4000000000000000 /- 2.0f -/) * q0 * q1 + (Binary64.ofBits 0x4000000000000000 /- 2.0f -/) * q2 * q3)
      H_MAG := H_MAG.set! 19 (Binary64.ofBits 0x0000000000000000 /- 0.0f -/)
      H_MAG := H_MAG.set! 20 (Binary64.ofBits 0x3ff0000000000000 /- 1.0f -/)
      H_MAG := H_MAG.set! 21 (Binary64.ofBits 0x0000000000000000 /- 0.0f -/)
      H_MAG_unit_index := (20 : Int32)
      let SK_MY : Array Binary64 := #[(Binary64.ofBits 0x3ff0000000000000 /- 1.0f -/) / s.varInnovMag.y, SH_MAG[3]! - SH_MAG[4]! + SH_MAG[5]! - SH_MAG[6]!, SH_MAG[7]! + SH_MAG[8]! - (Binary64.ofBits 0x4000000000000000 /- 2.0f -/) * magD * q2, (Binary64.ofBits 0x4000000000000000 /- 2.0f -/) * q0 * q3 - (Binary64.ofBits 0x4000000000000000 /- 2.0f -/) * q1 * q2, (Binary64.ofBits 0x4000000000000000 /- 2.0f -/) * q0 * q1 + (Binary64.ofBits 0x4000000000000000 /- 2.0f -/) * q2 * q3]
      let mut kalman_mask'2 : UInt32 := Int32.toUInt32 (((1 : Int32) <<< (10 : Int32)) - (1 : Int32))
      if !s.inhibitDelAngBiasStates then
        kalman_mask'2 := kalman_mask'2 ||| Int32.toUInt32 (((1 : Int32) <<< (10 : Int32)) ||| ((1 : Int32) <<< (11 : Int32)) ||| ((1 : Int32) <<< (12 : Int32)))
      if !s.inhibitDelVelBiasStates then
        for index'2' in [0:3] do
          let index'2 : UInt8 := Nat.toUInt8 index'2'
          let stateIndex'2 : UInt8 := Int8.toUInt8 (Int32.toInt8 (UInt32.toInt32 (UInt8.toUInt32 index'2) + (13 : Int32)))
          if !s.dvelBiasAxisInhibit[UInt8.toNat index'2]! then
            kalman_mask'2 := kalman_mask'2 ||| Int32.toUInt32 ((1 : Int32) <<< UInt32.toInt32 (UInt8.toUInt32 stateIndex'2))
      if !s.inhibitMagStates then
        kalman_mask'2 := kalman_mask'2 ||| Int32.toUInt32 (((1 : Int32) <<< (16 : Int32)) ||| ((1 : Int32) <<< (17 : Int32)) ||| ((1 : Int32) <<< (18 : Int32)) ||| ((1 : Int32) <<< (19 : Int32)) ||| ((1 : Int32) <<< (20 : Int32)) ||| ((1 : Int32) <<< (21 : Int32)))
      if !s.inhibitWindStates && !s.treatWindStatesAsTruth then
        kalman_mask'2 := kalman_mask'2 ||| Int32.toUInt32 (((1 : Int32) <<< (22 : Int32)) ||| ((1 : Int32) <<< (23 : Int32)))
      for i'5' in [0:24] do
        let i'5 : Int32 := Nat.toInt32 i'5'
        let mut res'2 : Binary64 := (Binary64.ofBits 0x0000000000000000 /- 0 -/)
        if kalman_mask'2 &&& Int32.toUInt32 ((1 : Int32) <<< i'5) != (0 : UInt32) then
          res'2 := SK_MY[0]! * (s.Pmut[Int32.toNatClampNeg i'5 * 24 + 20]! + s.Pmut[Int32.toNatClampNeg i'5 * 24]! * SH_MAG[2]! + s.Pmut[Int32.toNatClampNeg i'5 * 24 + 1]! * SH_MAG[1]! + s.Pmut[Int32.toNatClampNeg i'5 * 24 + 2]! * SH_MAG[0]! - s.Pmut[Int32.toNatClampNeg i'5 * 24 + 3]! * SK_MY[2]! - s.Pmut[Int32.toNatClampNeg i'5 * 24 + 17]! * SK_MY[1]! - s.Pmut[Int32.toNatClampNeg i'5 * 24 + 16]! * SK_MY[3]! + s.Pmut[Int32.toNatClampNeg i'5 * 24 + 18]! * SK_MY[4]!)
        w := { w with NavEKF_core_common'Kfusion := w.NavEKF_core_common'Kfusion.set! (Int32.toNatClampNeg i'5) res'2 }
      s := { s with magFusePerformed := true }
    else if UInt32.toInt32 (UInt8.toUInt32 obsIndex) == (2 : Int32) then
      let t'12 : UInt8 := Int8.toUInt8 (Int32.toInt8 (0 : Int32))
      let t'13 : Int32 := UInt32.toInt32 (UInt8.toUInt32 s.stateIndexLim)
      for i'6' in [0:(t'13.toInt - (Int.ofNat t'12.toNat) + 1).toNat] do  -- C++ loop bounded by a runtime value (--runtime-loops)
        let i'6 : UInt8 := t'12 + Nat.toUInt8 i'6'
        H_MAG := H_MAG.set! (UInt8.toNat i'6) (Binary64.ofBits 0x0000000000000000 /- 0.0f -/)
      H_MAG := H_MAG.set! 0 (SH_MAG[1]!)
      H_MAG := H_MAG.set! 1 (-SH_MAG[2]!)
      H_MAG := H_MAG.set! 2 (SH_MAG[7]! + SH_MAG[8]! - (Binary64.ofBits 0x4000000000000000 /- 2.0f -/) * magD * q2)
      H_MAG := H_MAG.set! 3 (SH_MAG[0]!)
      H_MAG := H_MAG.set! 16 ((Binary64.ofBits 0x4000000000000000 /- 2.0f -/) * q0 * q2 + (Binary64.ofBits 0x4000000000000000 /- 2.0f -/) * q1 * q3)
      H_MAG := H_MAG.set! 17 ((Binary64.ofBits 0x4000000000000000 /- 2.0f -/) * q2 * q3 - (Binary64.ofBits 0x4000000000000000 /- 2.0f -/) * q0 * q1)
      H_MAG := H_MAG.set! 18 (SH_MAG[3]! - SH_MAG[4]! - SH_MAG[5]! + SH_MAG[6]!)
      H_MAG := H_MAG.set! 19 (Binary64.ofBits 0x0000000000000000 /- 0.0f -/)
      H_MAG := H_MAG.set! 20 (Binary64.ofBits 0x0000000000000000 /- 0.0f -/)
      H_MAG := H_MAG.set! 21 (Binary64.ofBits 0x3ff0000000000000 /- 1.0f -/)
      H_MAG_unit_index := (21 : Int32)
      let SK_MZ : Array Binary64 := #[(Binary64.ofBits 0x3ff0000000000000 /- 1.0f -/) / s.varInnovMag.z, SH_MAG[3]! - SH_MAG[4]! - SH_MAG[5]! + SH_MAG[6]!, SH_MAG[7]! + SH_MAG[8]! - (Binary64.ofBits 0x4000000000000000 /- 2.0f -/) * magD * q2, (Binary64.ofBits 0x4000000000000000 /- 2.0f -/) * q0 * q1 - (Binary64.ofBits 0x4000000000000000 /- 2.0f -/) * q2 * q3, (Binary64.ofBits 0x4000000000000000 /- 2.0f -/) * q0 * q2 + (Binary64.ofBits 0x4000000000000000 /- 2.0f -/) * q1 * q3]
      let mut kalman_mask'3 : UInt32 := Int32.toUInt32 (((1 : Int32) <<< (10 : Int32)) - (1 : Int32))
      if !s.inhibitDelAngBiasStates then
        kalman_mask'3 := kalman_mask'3 ||| Int32.toUInt32 (((1 : Int32) <<< (10 : Int32)) ||| ((1 : Int32) <<< (11 : Int32)) ||| ((1 : Int32) <<< (12 : Int32)))
      if !s.inhibitDelVelBiasStates then
        for index'3' in [0:3] do
          let index'3 : UInt8 := Nat.toUInt8 index'3'
          let stateIndex'3 : UInt8 := Int8.toUInt8 (Int32.toInt8 (UInt32.toInt32 (UInt8.toUInt32 index'3) + (13 : Int32)))
          if !s.dvelBiasAxisInhibit[UInt8.toNat index'3]! then
            kalman_mask'3 := kalman_mask'3 ||| Int32.toUInt32 ((1 : Int32) <<< UInt32.toInt32 (UInt8.toUInt32 stateIndex'3))
      if !s.inhibitMagStates then
        kalman_mask'3 := kalman_mask'3 ||| Int32.toUInt32 (((1 : Int32) <<< (16 : Int32)) ||| ((1 : Int32) <<< (17 : Int32)) ||| ((1 : Int32) <<< (18 : Int32)) ||| ((1 : Int32) <<< (19 : Int32)) ||| ((1 : Int32) <<< (20 : Int32)) ||| ((1 : Int32) <<< (21 : Int32)))
      if !s.inhibitWindStates && !s.treatWindStatesAsTruth then
        kalman_mask'3 := kalman_mask'3 ||| Int32.toUInt32 (((1 : Int32) <<< (22 : Int32)) ||| ((1 : Int32) <<< (23 : Int32)))
      for i'7' in [0:24] do
        let i'7 : Int32 := Nat.toInt32 i'7'
        let mut res'3 : Binary64 := (Binary64.ofBits 0x0000000000000000 /- 0 -/)
        if kalman_mask'3 &&& Int32.toUInt32 ((1 : Int32) <<< i'7) != (0 : UInt32) then
          res'3 := SK_MZ[0]! * (s.Pmut[Int32.toNatClampNeg i'7 * 24 + 21]! + s.Pmut[Int32.toNatClampNeg i'7 * 24]! * SH_MAG[1]! - s.Pmut[Int32.toNatClampNeg i'7 * 24 + 1]! * SH_MAG[2]! + s.Pmut[Int32.toNatClampNeg i'7 * 24 + 3]! * SH_MAG[0]! + s.Pmut[Int32.toNatClampNeg i'7 * 24 + 2]! * SK_MZ[2]! + s.Pmut[Int32.toNatClampNeg i'7 * 24 + 18]! * SK_MZ[1]! + s.Pmut[Int32.toNatClampNeg i'7 * 24 + 16]! * SK_MZ[4]! - s.Pmut[Int32.toNatClampNeg i'7 * 24 + 17]! * SK_MZ[3]!)
        w := { w with NavEKF_core_common'Kfusion := w.NavEKF_core_common'Kfusion.set! (Int32.toNatClampNeg i'7) res'3 }
      s := { s with magFusePerformed := true }
    let t'14 : UInt32 := Int32.toUInt32 (0 : Int32)
    let t'15 : UInt32 := UInt8.toUInt32 s.stateIndexLim
    for i'8' in [0:((Int.ofNat t'15.toNat) - (Int.ofNat t'14.toNat) + 1).toNat] do  -- C++ loop bounded by a runtime value (--runtime-loops)
      let i'8 : UInt32 := t'14 + Nat.toUInt32 i'8'
      let t'16 : UInt32 := Int32.toUInt32 (0 : Int32)
      let t'17 : UInt32 := UInt8.toUInt32 s.stateIndexLim
      for j' in [0:((Int.ofNat t'17.toNat) - (Int.ofNat t'16.toNat) + 1).toNat] do  -- C++ loop bounded by a runtime value (--runtime-loops)
        let j : UInt32 := t'16 + Nat.toUInt32 j'
        let mut res'4 : Binary64 := (Binary64.ofBits 0x0000000000000000 /- 0 -/)
        res'4 := res'4 + (w.NavEKF_core_common'Kfusion[UInt32.toNat i'8]! * H_MAG[0]!) * s.Pmut[UInt32.toNat j]!
        res'4 := res'4 + (w.NavEKF_core_common'Kfusion[UInt32.toNat i'8]! * H_MAG[1]!) * s.Pmut[24 + UInt32.toNat j]!
        res'4 := res'4 + (w.NavEKF_core_common'Kfusion[UInt32.toNat i'8]! * H_MAG[2]!) * s.Pmut[48 + UInt32.toNat j]!
        res'4 := res'4 + (w.NavEKF_core_common'Kfusion[UInt32.toNat i'8]! * H_MAG[3]!) * s.Pmut[72 + UInt32.toNat j]!
        res'4 := res'4 + (w.NavEKF_core_common'Kfusion[UInt32.toNat i'8]! * H_MAG[16]!) * s.Pmut[384 + UInt32.toNat j]!
        res'4 := res'4 + (w.NavEKF_core_common'Kfusion[UInt32.toNat i'8]! * H_MAG[17]!) * s.Pmut[408 + UInt32.toNat j]!
        res'4 := res'4 + (w.NavEKF_core_common'Kfusion[UInt32.toNat i'8]! * H_MAG[18]!) * s.Pmut[432 + UInt32.toNat j]!
        res'4 := res'4 + w.NavEKF_core_common'Kfusion[UInt32.toNat i'8]! * s.Pmut[Int32.toNatClampNeg H_MAG_unit_index * 24 + UInt32.toNat j]!
        w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! (UInt32.toNat i'8 * 24 + UInt32.toNat j) res'4 }
    let (t'18, t'19) := FinishFusion s w (match UInt8.toNat obsIndex with | 0 => s.innovMag.x | 1 => s.innovMag.y | _ => s.innovMag.z) false
    s := t'18
    if !t'19 then
      if s.have_table_earth_field && decide (Int16.toInt32 (AP_ParamT_short_2.op_to_short w.EKF3._mag_ef_limit) > (0 : Int32)) then
        s := MagTableConstrain s w
    else
      if UInt32.toInt32 (UInt8.toUInt32 obsIndex) == (0 : Int32) then
        s := { s with faultStatus.bad_xmag := true }
      else if UInt32.toInt32 (UInt8.toUInt32 obsIndex) == (1 : Int32) then
        s := { s with faultStatus.bad_ymag := true }
      else if UInt32.toInt32 (UInt8.toUInt32 obsIndex) == (2 : Int32) then
        s := { s with faultStatus.bad_zmag := true }
      let (t'20, t'21) := CovarianceInit s w
      w := t'21
      s := t'20
      return (s, w)
  s := { s with last_mag_yaw_fuse_ms := s.imuSampleTime_ms }
  return (s, w)

/-- C++ `void NavEKF3_core::SelectMagFusion()`, `AP_NavEKF3/AP_NavEKF3_MagFusion.cpp:336-608`. -/
def SelectMagFusion (s : State) (w : World) (o : Outputs) : State × World × Outputs := Id.run do
  let mut s := s
  let mut w := w
  let mut o := o
  s := { s with magFusePerformed := false }
  if !s.onGroundNotMoving then
    if Binary64.abs s.prevTnb.a.z < Binary64.abs s.prevTnb.b.z then
      s := { s with yawAngDataStatic.order := NavEKF3_core.rotationOrder.TAIT_BRYAN_321 }
      s := { s with yawAngDataStatic.yawAng := Musl.atan2.atan2 s.prevTnb.a.y s.prevTnb.a.x }
    else
      s := { s with yawAngDataStatic.order := NavEKF3_core.rotationOrder.TAIT_BRYAN_312 }
      s := { s with yawAngDataStatic.yawAng := Musl.atan2.atan2 (-s.prevTnb.b.x) s.prevTnb.b.y }
    s := { s with yawAngDataStatic.yawAngErr := Binary32.toBinary64 (Estimator_lib.MAX_AP_ParamT_float_4_float w.EKF3._yawNoise (Binary32.ofBits 0x3d4ccccd /- 0.05f -/)) }
    s := { s with yawAngDataStatic.time_ms := s.imuDataDelayed.time_ms }
  if (s.yaw_source_last == AP_NavEKF_Source.SourceYaw.GSF) || (!(use_compass s w) && s.yaw_source_last != AP_NavEKF_Source.SourceYaw.GPS && s.yaw_source_last != AP_NavEKF_Source.SourceYaw.GPS_COMPASS_FALLBACK && s.yaw_source_last != AP_NavEKF_Source.SourceYaw.EXTNAV) then
    if (!s.yawAlignComplete || s.yaw_source_reset) && ((s.yaw_source_last != AP_NavEKF_Source.SourceYaw.GSF) || (decide (UInt32.toInt32 (UInt8.toUInt32 s.EKFGSF_yaw_valid_count) ≥ (5 : Int32)))) then
      let (t'1, t'2, t'3) := realignYawGPS s w o false
      w := t'2
      s := t'1
      o := t'3
      s := { s with yaw_source_reset := false }
    else
      s := { s with yaw_source_reset := false }
    if s.imuSampleTime_ms - s.lastSynthYawTime_ms > Int32.toUInt32 (140 : Int32) then
      let mut gsfYaw : Binary64 := (Binary64.ofBits 0x0000000000000000 /- 0.0 -/)  -- uninitialized in C++; assigned before every read
      let mut gsfYawVariance : Binary64 := (Binary64.ofBits 0x0000000000000000 /- 0.0 -/)  -- uninitialized in C++; assigned before every read
      let mut t'7 := s.yawAlignComplete && (s.yaw_source_last == AP_NavEKF_Source.SourceYaw.GSF)
      if t'7 then
        let (t'4, t'5, t'6) := EKFGSF_getYaw s w gsfYaw gsfYawVariance
        gsfYaw := t'4
        gsfYawVariance := t'5
        t'7 := t'6
      let mut t'11 := t'7 && !(assume_zero_sideslip w)
      if t'11 then
        let (t'8, t'9, t'10) := fuseEulerYaw s w NavEKF3_core.yawFusionMethod.GSF
        w := t'9
        s := t'8
        t'11 := t'10
      let didUseEKFGSF : Bool := t'11
      if !didUseEKFGSF then
        if s.onGroundNotMoving then
          let (t'12, t'13, _) := fuseEulerYaw s w NavEKF3_core.yawFusionMethod.STATIC
          w := t'13
          s := t'12
        else if s.onGround || UInt32.toInt32 (NavEKF3_core.AidingMode.toInt s.PV_AidingMode) == UInt32.toInt32 (NavEKF3_core.AidingMode.toInt NavEKF3_core.AidingMode.AID_NONE) || (decide (s.Pmut[0]! + s.Pmut[25]! + s.Pmut[50]! + s.Pmut[75]! > (Binary64.ofBits 0x3f847ae140000000 /- 0.01f -/))) then
          let (t'15, t'16, _) := fuseEulerYaw s w NavEKF3_core.yawFusionMethod.PREDICTED
          w := t'16
          s := t'15
      s := { s with magTestRatio := Vector3p.zero s.magTestRatio }
      s := { s with yawTestRatio := (Binary64.ofBits 0x0000000000000000 /- 0.0f -/) }
      s := { s with lastSynthYawTime_ms := s.imuSampleTime_ms }
    return (s, w, o)
  if s.yaw_source_last == AP_NavEKF_Source.SourceYaw.GPS || s.yaw_source_last == AP_NavEKF_Source.SourceYaw.GPS_COMPASS_FALLBACK then
    let mut have_fused_gps_yaw : Bool := false
    let (t'18, t'19, t'20) := EKF_obs_buffer_t_NavEKF3_core_yaw_elements.recall_yaw_elements_uint32_t s.gpsYaw.stored s.gpsYaw.dataDelayed s.imuDataDelayed.time_ms
    s := { s with gpsYaw.stored := t'18 }
    s := { s with gpsYaw.dataDelayed := t'19 }
    if t'20 then
      if s.tiltAlignComplete && (!s.yawAlignComplete || s.yaw_source_reset) then
        let (t'21, t'22, t'23) := alignYawAngle s w o s.gpsYaw.dataDelayed
        w := t'22
        s := t'21
        o := t'23
        s := { s with yaw_source_reset := false }
        have_fused_gps_yaw := true
        s := { s with lastSynthYawTime_ms := s.imuSampleTime_ms }
        s := { s with gpsYaw.lastFuseTime_ms := s.imuSampleTime_ms }
        s := recordYawResetsCompleted s
      else if s.tiltAlignComplete && s.yawAlignComplete then
        let (t'24, t'25, t'26) := fuseEulerYaw s w NavEKF3_core.yawFusionMethod.GPS
        w := t'25
        s := t'24
        have_fused_gps_yaw := t'26 && !s.faultStatus.bad_yaw
        if have_fused_gps_yaw then
          s := { s with gpsYaw.lastFuseTime_ms := s.imuSampleTime_ms }
      s := { s with gpsYaw.lastUseTime_ms := s.imuSampleTime_ms }
    else if s.tiltAlignComplete && !s.yawAlignComplete then
      if s.imuSampleTime_ms - s.lastSynthYawTime_ms > Int32.toUInt32 (140 : Int32) then
        s := { s with gpsYaw.dataDelayed.yawAngErr := Binary32.toBinary64 (Estimator_lib.MAX_AP_ParamT_float_4_float w.EKF3._yawNoise (Binary32.ofBits 0x3d4ccccd /- 0.05f -/)) }
        if !s.onGroundNotMoving then
          let (t'27, t'28, _) := fuseEulerYaw s w NavEKF3_core.yawFusionMethod.PREDICTED
          w := t'28
          s := t'27
        else
          let (t'30, t'31, _) := fuseEulerYaw s w NavEKF3_core.yawFusionMethod.STATIC
          w := t'31
          s := t'30
        s := { s with lastSynthYawTime_ms := s.imuSampleTime_ms }
    else if s.tiltAlignComplete && s.yawAlignComplete && s.onGround && decide (s.imuSampleTime_ms - s.gpsYaw.lastFuseTime_ms > Int32.toUInt32 (10000 : Int32)) then
      s := { s with yaw_source_reset := true }
    if s.yaw_source_last == AP_NavEKF_Source.SourceYaw.GPS then
      return (s, w, o)
    let (t'33, t'34) := readMagData s w o
    s := t'33
    o := t'34
    if have_fused_gps_yaw then
      if s.gpsYaw.magFallbackActive then
        s := { s with gpsYaw.magFallbackActive := false }
        o := o.push (Output.send_text (6 : UInt32) "EKF3 IMU%u yaw external" #[Sum.inl (UInt32.toUInt64 (UInt8.toUInt32 s.imu_index))])
      let (t'35, t'36) := learnMagBiasFromGPS s
      s := t'35
      s := { s with gpsYaw.magFallbackOk := t'36 }
      return (s, w, o)
    if s.imuSampleTime_ms - s.gpsYaw.lastUseTime_ms < Int32.toUInt32 (10000 : Int32) then
      return (s, w, o)
    if !s.gpsYaw.magFallbackOk then
      return (s, w, o)
    if !s.inFlight then
      return (s, w, o)
    if !s.gpsYaw.magFallbackActive then
      s := { s with gpsYaw.magFallbackActive := true }
      o := o.push (Output.send_text (6 : UInt32) "EKF3 IMU%u yaw fallback active" #[Sum.inl (UInt32.toUInt64 (UInt8.toUInt32 s.imu_index))])
  if s.magHealth then
    s := { s with magTimeout := false }
    s := { s with lastHealthyMagTime_ms := s.imuSampleTime_ms }
  else if decide ((s.imuSampleTime_ms - s.lastHealthyMagTime_ms) > w.EKF3.magFailTimeLimit_ms) && use_compass s w then
    s := { s with magTimeout := true }
  if s.yaw_source_last != AP_NavEKF_Source.SourceYaw.GPS_COMPASS_FALLBACK then
    let (t'37, t'38) := readMagData s w o
    s := t'37
    o := t'38
  let (t'39, t'40, t'41) := EKF_obs_buffer_t_NavEKF3_core_mag_elements.recall_mag_elements_uint32_t s.storedMag s.magDataDelayed s.imuDataDelayed.time_ms
  s := { s with storedMag := t'39 }
  s := { s with magDataDelayed := t'40 }
  s := { s with magDataToFuse := t'41 }
  if s.magDataToFuse then
    if s.yaw_source_reset && (s.yaw_source_last == AP_NavEKF_Source.SourceYaw.COMPASS || s.yaw_source_last == AP_NavEKF_Source.SourceYaw.GPS_COMPASS_FALLBACK) then
      s := { s with magYawResetRequest := true }
      s := { s with yaw_source_reset := false }
    let (t'42, t'43, t'44) := controlMagYawReset s w o
    w := t'43
    s := t'42
    o := t'44
  let dataReady : Bool := (s.magDataToFuse && s.statesInitialised && use_compass s w && s.yawAlignComplete)
  if dataReady then
    if s.inhibitMagStates || s.magStateResetRequest || !s.magStateInitComplete then
      s := { s with magFusionSel := NavEKF3_core.MagFuseSel.FUSE_YAW }
      let (t'45, t'46, t'47) := fuseEulerYaw s w NavEKF3_core.yawFusionMethod.MAGNETOMETER
      w := t'46
      s := t'45
      if t'47 && !s.faultStatus.bad_yaw then
        s := { s with last_mag_yaw_fuse_ms := s.imuSampleTime_ms }
      s := { s with magTestRatio := Vector3p.zero s.magTestRatio }
    else
      s := { s with magFusionSel := NavEKF3_core.MagFuseSel.FUSE_MAG }
      let mut yawAnchored : Bool := false
      if s.onGroundNotMoving && s.effectiveMagCal == NavEKF3_core.MagCal.GROUND_AND_INFLIGHT then
        let (t'48, t'49, t'50) := fuseEulerYaw s w NavEKF3_core.yawFusionMethod.MAGNETOMETER
        w := t'49
        s := t'48
        yawAnchored := t'50
        if yawAnchored && !s.faultStatus.bad_yaw then
          s := { s with magFusionSel := NavEKF3_core.MagFuseSel.FUSE_MAG_ANCHORED }
          s := { s with last_mag_yaw_fuse_ms := s.imuSampleTime_ms }
      if UInt32.toInt32 (NavEKF3_core.AidingMode.toInt s.PV_AidingMode) != UInt32.toInt32 (NavEKF3_core.AidingMode.toInt NavEKF3_core.AidingMode.AID_ABSOLUTE) || (decide (Int16.toInt32 (AP_ParamT_short_2.op_to_short w.EKF3._mag_ef_limit) > (0 : Int32)) && s.have_table_earth_field) then
        let (t'51, t'52) := FuseDeclination s w (Binary64.ofBits 0x3fd5c28f60000000 /- 0.34f -/)
        w := t'52
        s := t'51
      let (t'53, t'54) := FuseMagnetometer s w
      w := t'54
      s := t'53
      if !yawAnchored then
        s := { s with yawTestRatio := (Binary64.ofBits 0x0000000000000000 /- 0.0f -/) }
  if !s.magFieldLearned && s.finalInflightMagInit then
    s := { s with magFieldLearned := (decide (s.Pmut[400]! < Binary32.toBinary64 (Estimator_lib.sq_float (Binary32.ofBits 0x3c23d70a /- 0.01f -/)))) && (decide (s.Pmut[425]! < Binary32.toBinary64 (Estimator_lib.sq_float (Binary32.ofBits 0x3c23d70a /- 0.01f -/)))) && (decide (s.Pmut[450]! < Binary32.toBinary64 (Estimator_lib.sq_float (Binary32.ofBits 0x3c23d70a /- 0.01f -/)))) }
  if s.magFieldLearned && !s.inhibitMagStates then
    s := { s with earthMagFieldVar.x := s.Pmut[400]! }
    s := { s with earthMagFieldVar.y := s.Pmut[425]! }
    s := { s with earthMagFieldVar.z := s.Pmut[450]! }
    s := { s with bodyMagFieldVar.x := s.Pmut[475]! }
    s := { s with bodyMagFieldVar.y := s.Pmut[500]! }
    s := { s with bodyMagFieldVar.z := s.Pmut[525]! }
  return (s, w, o)

end NavEKF3_core

namespace NavEKF3_core

/-- C++ `void NavEKF3_core::FuseVelPosNED()`, `AP_NavEKF3/AP_NavEKF3_PosVelFusion.cpp:750-1216`. -/
def FuseVelPosNED (s : State) (w : World) : State × World := Id.run do
  let mut s := s
  let mut w := w
  let mut fuseData : Array Bool := Array.replicate 6 false
  let mut stateIndex : UInt8 := (0 : UInt8)  -- uninitialized in C++; assigned before every read
  let mut R_OBS : Array Binary64 := Array.replicate 6 (Binary64.ofBits 0x0000000000000000 /- 0.0 -/)  -- uninitialized in C; every element is written before it is read
  let mut R_OBS_DATA_CHECKS : Array Binary64 := Array.replicate 6 (Binary64.ofBits 0x0000000000000000 /- 0.0 -/)  -- uninitialized in C; every element is written before it is read
  let mut SK : Binary64 := (Binary64.ofBits 0x0000000000000000 /- 0.0 -/)  -- uninitialized in C++; assigned before every read
  if s.fuseVelData || s.fuseVelVertData || s.fusePosData || s.fuseHgtData then
    if UInt32.toInt32 (NavEKF3_core.AidingMode.toInt s.PV_AidingMode) == UInt32.toInt32 (NavEKF3_core.AidingMode.toInt NavEKF3_core.AidingMode.AID_NONE) then
      if s.fusingStationaryZeroVel then
        R_OBS := R_OBS.set! 0 (Binary32.toBinary64 (Estimator_lib.sq_float (Estimator_lib.MIN_AP_ParamT_float_4_float w.EKF3._noaidHorizNoise (Binary32.ofBits 0x3f800000 /- 1.0f -/))))
      else if s.tiltAlignComplete && s.motorsArmed then
        R_OBS := R_OBS.set! 0 (Estimator_lib.sq_double (Estimator_lib.constrain_value_line_double (AP_ParamT_float_4.op_to_double w.EKF3._noaidHorizNoise) (Binary64.ofBits 0x3fe0000000000000 /- (double)1/2 -/) (Binary64.ofBits 0x4049000000000000 /- (double)50 -/) (Int32.toUInt32 (781 : Int32))))
      else
        R_OBS := R_OBS.set! 0 (Binary32.toBinary64 (Estimator_lib.sq_float (Binary32.ofBits 0x3f000000 /- 0.5f -/)))
      R_OBS := R_OBS.set! 1 (R_OBS[0]!)
      R_OBS := R_OBS.set! 2 (R_OBS[0]!)
      R_OBS := R_OBS.set! 3 (R_OBS[0]!)
      R_OBS := R_OBS.set! 4 (R_OBS[0]!)
      for i' in [0:3] do
        let i : UInt8 := Nat.toUInt8 i'
        R_OBS_DATA_CHECKS := R_OBS_DATA_CHECKS.set! (UInt8.toNat i) (R_OBS[UInt8.toNat i]!)
    else if s.fusingStationaryZeroVel then
      R_OBS := R_OBS.set! 0 (Binary32.toBinary64 (Estimator_lib.sq_float (Binary32.ofBits 0x3f800000 /- 1.0f -/)))
      R_OBS := R_OBS.set! 1 (R_OBS[0]!)
      R_OBS := R_OBS.set! 2 (R_OBS[0]!)
      for i'2' in [0:3] do
        let i'2 : UInt8 := Nat.toUInt8 i'2'
        R_OBS_DATA_CHECKS := R_OBS_DATA_CHECKS.set! (UInt8.toNat i'2) (R_OBS[UInt8.toNat i'2]!)
      if s.gpsPosAccuracy > (Binary64.ofBits 0x0000000000000000 /- 0.0f -/) then
        R_OBS := R_OBS.set! 3 (Estimator_lib.sq_double (Estimator_lib.constrain_value_line_double s.gpsPosAccuracy (AP_ParamT_float_4.op_to_double w.EKF3._gpsHorizPosNoise) (Binary64.ofBits 0x4059000000000000 /- (double)100 -/) (Int32.toUInt32 (809 : Int32))))
      else
        R_OBS := R_OBS.set! 3 (Estimator_lib.sq_double (Estimator_lib.constrain_value_line_double (AP_ParamT_float_4.op_to_double w.EKF3._gpsHorizPosNoise) (Binary64.ofBits 0x3fb99999a0000000 /- (double)13421773/134217728 -/) (Binary64.ofBits 0x4024000000000000 /- (double)10 -/) (Int32.toUInt32 (811 : Int32))))
      R_OBS := R_OBS.set! 4 (R_OBS[3]!)
    else
      if s.gpsSpdAccuracy > (Binary64.ofBits 0x0000000000000000 /- 0.0f -/) then
        R_OBS := R_OBS.set! 0 (Estimator_lib.sq_double (Estimator_lib.constrain_value_line_double s.gpsSpdAccuracy (AP_ParamT_float_4.op_to_double w.EKF3._gpsHorizVelNoise) (Binary64.ofBits 0x4049000000000000 /- (double)50 -/) (Int32.toUInt32 (823 : Int32))))
        R_OBS := R_OBS.set! 2 (Estimator_lib.sq_double (Estimator_lib.constrain_value_line_double s.gpsSpdAccuracy (AP_ParamT_float_4.op_to_double w.EKF3._gpsVertVelNoise) (Binary64.ofBits 0x4049000000000000 /- (double)50 -/) (Int32.toUInt32 (824 : Int32))))
      else
        R_OBS := R_OBS.set! 0 (Estimator_lib.sq_double (Estimator_lib.constrain_value_line_double (AP_ParamT_float_4.op_to_double w.EKF3._gpsHorizVelNoise) (Binary64.ofBits 0x3fa99999a0000000 /- (double)13421773/268435456 -/) (Binary64.ofBits 0x4014000000000000 /- (double)5 -/) (Int32.toUInt32 (827 : Int32))) + Estimator_lib.sq_double (Binary32.toBinary64 w.EKF3.gpsNEVelVarAccScale * s.accNavMag))
        R_OBS := R_OBS.set! 2 (Estimator_lib.sq_double (Estimator_lib.constrain_value_line_double (AP_ParamT_float_4.op_to_double w.EKF3._gpsVertVelNoise) (Binary64.ofBits 0x3fa99999a0000000 /- (double)13421773/268435456 -/) (Binary64.ofBits 0x4014000000000000 /- (double)5 -/) (Int32.toUInt32 (828 : Int32))) + Estimator_lib.sq_double (Binary32.toBinary64 w.EKF3.gpsDVelVarAccScale * s.accNavMag))
      R_OBS := R_OBS.set! 1 (R_OBS[0]!)
      if s.gpsPosAccuracy > (Binary64.ofBits 0x0000000000000000 /- 0.0f -/) then
        R_OBS := R_OBS.set! 3 (Estimator_lib.sq_double (Estimator_lib.constrain_value_line_double s.gpsPosAccuracy (AP_ParamT_float_4.op_to_double w.EKF3._gpsHorizPosNoise) (Binary64.ofBits 0x4059000000000000 /- (double)100 -/) (Int32.toUInt32 (838 : Int32))))
      else
        let posErr : Binary64 := Binary32.toBinary64 w.EKF3.gpsPosVarAccScale * s.accNavMag
        R_OBS := R_OBS.set! 3 (Estimator_lib.sq_double (Estimator_lib.constrain_value_line_double (AP_ParamT_float_4.op_to_double w.EKF3._gpsHorizPosNoise) (Binary64.ofBits 0x3fb99999a0000000 /- (double)13421773/134217728 -/) (Binary64.ofBits 0x4024000000000000 /- (double)10 -/) (Int32.toUInt32 (842 : Int32))) + Estimator_lib.sq_double posErr)
      R_OBS := R_OBS.set! 4 (R_OBS[3]!)
      let mut obs_data_chk : Binary64 := (Binary64.ofBits 0x0000000000000000 /- 0.0 -/)  -- uninitialized in C++; assigned before every read
      obs_data_chk := Estimator_lib.sq_double (Estimator_lib.constrain_value_line_double (AP_ParamT_float_4.op_to_double w.EKF3._gpsHorizVelNoise) (Binary64.ofBits 0x3fa99999a0000000 /- (double)13421773/268435456 -/) (Binary64.ofBits 0x4014000000000000 /- (double)5 -/) (Int32.toUInt32 (855 : Int32))) + Estimator_lib.sq_double (Binary32.toBinary64 w.EKF3.gpsNEVelVarAccScale * s.accNavMag)
      R_OBS_DATA_CHECKS := R_OBS_DATA_CHECKS.set! 2 obs_data_chk
      R_OBS_DATA_CHECKS := R_OBS_DATA_CHECKS.set! 1 (R_OBS_DATA_CHECKS[2]!)
      R_OBS_DATA_CHECKS := R_OBS_DATA_CHECKS.set! 0 (R_OBS_DATA_CHECKS[1]!)
    R_OBS := R_OBS.set! 5 s.posDownObsNoise
    for i'3' in [3:6] do
      let i'3 : UInt8 := Nat.toUInt8 i'3'
      R_OBS_DATA_CHECKS := R_OBS_DATA_CHECKS.set! (UInt8.toNat i'3) (R_OBS[UInt8.toNat i'3]!)
    let fuse_gps_vz : Bool := AP_NavEKF_Source.useVelZSource w.EKF3.sources AP_NavEKF_Source.SourceZ.GPS s.core_index && s.gpsDataDelayed.have_vz
    if fuse_gps_vz && s.fuseVelVertData && (AP_NavEKF_Source.getPosZSource w.EKF3.sources s.core_index != AP_NavEKF_Source.SourceZ.GPS) then
      let hgtErr : Binary64 := s.statesArray[9]! - s.velPosObs[5]!
      let velDErr : Binary64 := s.statesArray[6]! - s.velPosObs[2]!
      let timeSinceLastBadIMU_ms : UInt32 := s.imuSampleTime_ms - s.badIMUdata_ms
      let mut R_gain : Binary32 := (Binary32.ofBits 0x00000000 /- 0.0 -/)  -- uninitialized in C++; assigned before every read
      if timeSinceLastBadIMU_ms > Int32.toUInt32 ((10000 : Int32) * (2 : Int32)) then
        R_gain := (Binary32.ofBits 0x41100000 /- 9.0F -/)
      else if timeSinceLastBadIMU_ms > Int32.toUInt32 (((10000 : Int32) * (3 : Int32)) / (2 : Int32)) then
        R_gain := (Binary32.ofBits 0x40800000 /- 4.0F -/)
      else
        R_gain := (Binary32.ofBits 0x3f800000 /- 1.0F -/)
      if (decide (hgtErr * velDErr > (Binary64.ofBits 0x0000000000000000 /- 0.0f -/))) && (decide (Estimator_lib.sq_double hgtErr > Binary32.toBinary64 R_gain * R_OBS[5]!)) && (decide (Estimator_lib.sq_double velDErr > Binary32.toBinary64 R_gain * R_OBS[2]!)) then
        s := { s with badIMUdata_ms := s.imuSampleTime_ms }
      else
        s := { s with goodIMUdata_ms := s.imuSampleTime_ms }
      if timeSinceLastBadIMU_ms < Int32.toUInt32 (10000 : Int32) then
        s := { s with badIMUdata := true }
        s := { s with statesArray := s.statesArray.set! 6 s.gpsDataDelayed.vel.z }
      else
        s := { s with badIMUdata := false }
    if s.fusePosData then
      s := { s with innovVelPos := s.innovVelPos.set! 3 (s.statesArray[7]! - s.velPosObs[3]!) }
      s := { s with innovVelPos := s.innovVelPos.set! 4 (s.statesArray[8]! - s.velPosObs[4]!) }
      s := { s with varInnovVelPos := s.varInnovVelPos.set! 3 (s.Pmut[175]! + R_OBS_DATA_CHECKS[3]!) }
      s := { s with varInnovVelPos := s.varInnovVelPos.set! 4 (s.Pmut[200]! + R_OBS_DATA_CHECKS[4]!) }
      let maxPosInnov2 : Binary64 := Estimator_lib.sq_double (Estimator_lib.MAX_double_float ((Binary64.ofBits 0x3f847ae147ae147b /- 0.01 -/) * Int16.toBinary64 (AP_ParamT_short_2.op_to_short w.EKF3._gpsPosInnovGate)) (Binary32.ofBits 0x3f800000 /- 1.0 -/)) * (s.varInnovVelPos[3]! + s.varInnovVelPos[4]!)
      s := { s with posTestRatio := (Estimator_lib.sq_double s.innovVelPos[3]! + Estimator_lib.sq_double s.innovVelPos[4]!) / maxPosInnov2 }
      let mut posCheckPassed : Bool := false
      if decide (s.posTestRatio < (Binary64.ofBits 0x3ff0000000000000 /- 1.0f -/)) || (UInt32.toInt32 (NavEKF3_core.AidingMode.toInt s.PV_AidingMode) == UInt32.toInt32 (NavEKF3_core.AidingMode.toInt NavEKF3_core.AidingMode.AID_NONE)) then
        posCheckPassed := true
        s := { s with lastGpsPosPassTime_ms := s.imuSampleTime_ms }
      else if (decide (Int8.toInt32 (AP_ParamT_signed_char_1.op_to_signed_char w.EKF3._gpsGlitchRadiusMax) ≤ (0 : Int32))) && (UInt32.toInt32 (NavEKF3_core.AidingMode.toInt s.PV_AidingMode) != UInt32.toInt32 (NavEKF3_core.AidingMode.toInt NavEKF3_core.AidingMode.AID_NONE)) then
        s := { s with lastGpsPosPassTime_ms := s.imuSampleTime_ms }
        s := { s with varInnovVelPos := s.varInnovVelPos.set! 3 (s.varInnovVelPos[3]! * s.posTestRatio) }
        s := { s with varInnovVelPos := s.varInnovVelPos.set! 4 (s.varInnovVelPos[4]! * s.posTestRatio) }
        posCheckPassed := true
        s := { s with lastGpsPosPassTime_ms := s.imuSampleTime_ms }
      if posCheckPassed || s.posTimeout || s.badIMUdata then
        let posVarianceIsTooLarge : Bool := (decide (Int8.toInt32 (AP_ParamT_signed_char_1.op_to_signed_char w.EKF3._gpsGlitchRadiusMax) > (0 : Int32))) && decide ((s.Pmut[200]! + s.Pmut[175]!) > Estimator_lib.sq_double (Int8.toBinary64 (AP_ParamT_signed_char_1.op_to_signed_char w.EKF3._gpsGlitchRadiusMax)))
        if (s.posTimeout || posVarianceIsTooLarge) && (!s.velAiding || s.gpsGoodToAlign) then
          s := ResetPosition s w NavEKF3_core.resetDataSource.DEFAULT
          s := { s with fusePosData := false }
          s := zeroStatesVarCov s (Int8.toUInt8 (Int32.toInt8 (7 : Int32))) (Int8.toUInt8 (Int32.toInt8 (8 : Int32)))
          s := { s with Pmut := s.Pmut.set! 175 (Estimator_lib.sq_double (Binary32.toBinary64 ((Binary32.ofBits 0x3f000000 /- 0.5f -/) * Int32.toBinary32 (Int8.toInt32 (AP_ParamT_signed_char_1.op_to_signed_char w.EKF3._gpsGlitchRadiusMax))))) }
          s := { s with Pmut := s.Pmut.set! 200 (s.Pmut[175]!) }
          s := { s with posTestRatio := (Binary64.ofBits 0x0000000000000000 /- 0.0f -/) }
          if s.velTimeout then
            s := ResetVelocity s w NavEKF3_core.resetDataSource.DEFAULT
            s := { s with fuseVelData := false }
            s := { s with velTestRatio := (Binary64.ofBits 0x0000000000000000 /- 0.0f -/) }
      else
        s := { s with fusePosData := false }
    if s.fuseVelData then
      let mut imax : UInt8 := Int8.toUInt8 (Int32.toInt8 (2 : Int32))
      let fuse_extnav_vz : Bool := AP_NavEKF_Source.useVelZSource w.EKF3.sources AP_NavEKF_Source.SourceZ.EXTNAV s.core_index && s.extNav.useVel
      if (UInt32.toInt32 (NavEKF3_core.AidingMode.toInt s.PV_AidingMode) != UInt32.toInt32 (NavEKF3_core.AidingMode.toInt NavEKF3_core.AidingMode.AID_ABSOLUTE) || !fuse_gps_vz) && !fuse_extnav_vz then
        imax := Int8.toUInt8 (Int32.toInt8 (1 : Int32))
      let mut innovVelSumSq : Binary64 := (Binary64.ofBits 0x0000000000000000 /- 0 -/)
      let mut varVelSum : Binary64 := (Binary64.ofBits 0x0000000000000000 /- 0 -/)
      for i'4' in [0:imax.toNat + 1] do
        let i'4 : UInt8 := Nat.toUInt8 i'4'
        stateIndex := Int8.toUInt8 (Int32.toInt8 (UInt32.toInt32 (UInt8.toUInt32 i'4) + (4 : Int32)))
        let innovation : Binary32 := Binary64.toBinary32 (s.statesArray[4 + UInt8.toNat i'4]! - s.velPosObs[UInt8.toNat i'4]!)
        innovVelSumSq := innovVelSumSq + Binary32.toBinary64 (Estimator_lib.sq_float innovation)
        s := { s with varInnovVelPos := s.varInnovVelPos.set! (UInt8.toNat i'4) (s.Pmut[UInt8.toNat stateIndex * 24 + UInt8.toNat stateIndex]! + R_OBS_DATA_CHECKS[UInt8.toNat i'4]!) }
        varVelSum := varVelSum + s.varInnovVelPos[UInt8.toNat i'4]!
      s := { s with velTestRatio := innovVelSumSq / (varVelSum * Estimator_lib.sq_double (Estimator_lib.MAX_double_float ((Binary64.ofBits 0x3f847ae147ae147b /- 0.01 -/) * Int16.toBinary64 (AP_ParamT_short_2.op_to_short w.EKF3._gpsVelInnovGate)) (Binary32.ofBits 0x3f800000 /- 1.0 -/))) }
      let mut velCheckPassed : Bool := false
      if s.velTestRatio < (Binary64.ofBits 0x3ff0000000000000 /- 1.0 -/) then
        velCheckPassed := true
        s := { s with lastVelPassTime_ms := s.imuSampleTime_ms }
      else if Int8.toInt32 (AP_ParamT_signed_char_1.op_to_signed_char w.EKF3._gpsGlitchRadiusMax) ≤ (0 : Int32) then
        s := { s with lastGpsPosPassTime_ms := s.imuSampleTime_ms }
        for i'5' in [0:imax.toNat + 1] do
          let i'5 : UInt8 := Nat.toUInt8 i'5'
          s := { s with varInnovVelPos := s.varInnovVelPos.set! (UInt8.toNat i'5) (s.varInnovVelPos[UInt8.toNat i'5]! * s.velTestRatio) }
        velCheckPassed := true
        s := { s with lastVelPassTime_ms := s.imuSampleTime_ms }
      if velCheckPassed || s.velTimeout || s.badIMUdata then
        if UInt32.toInt32 (NavEKF3_core.AidingMode.toInt s.PV_AidingMode) == UInt32.toInt32 (NavEKF3_core.AidingMode.toInt NavEKF3_core.AidingMode.AID_ABSOLUTE) && s.velTimeout then
          s := ResetVelocity s w NavEKF3_core.resetDataSource.DEFAULT
          s := { s with fuseVelData := false }
          s := { s with velTestRatio := (Binary64.ofBits 0x0000000000000000 /- 0.0f -/) }
      else
        s := { s with fuseVelData := false }
    if s.fuseHgtData then
      s := { s with innovVelPos := s.innovVelPos.set! 5 (s.statesArray[9]! - s.velPosObs[5]!) }
      s := { s with varInnovVelPos := s.varInnovVelPos.set! 5 (s.Pmut[225]! + R_OBS_DATA_CHECKS[5]!) }
      s := { s with hgtTestRatio := Estimator_lib.sq_double s.innovVelPos[5]! / (Estimator_lib.sq_double (Estimator_lib.MAX_double_float ((Binary64.ofBits 0x3f847ae147ae147b /- 0.01 -/) * Int16.toBinary64 (AP_ParamT_short_2.op_to_short w.EKF3._hgtInnovGate)) (Binary32.ofBits 0x3f800000 /- 1.0 -/)) * s.varInnovVelPos[5]!) }
      let onGroundNotNavigating : Bool := (UInt32.toInt32 (NavEKF3_core.AidingMode.toInt s.PV_AidingMode) == UInt32.toInt32 (NavEKF3_core.AidingMode.toInt NavEKF3_core.AidingMode.AID_NONE)) && s.onGround
      let maxTestRatio : Binary32 := if onGroundNotNavigating then (Binary32.ofBits 0x40400000 /- 3.0f -/) else (Binary32.ofBits 0x3f800000 /- 1.0f -/)
      let mut hgtCheckPassed : Bool := false
      if s.hgtTestRatio < Binary32.toBinary64 maxTestRatio then
        hgtCheckPassed := true
        s := { s with lastHgtPassTime_ms := s.imuSampleTime_ms }
      else if (decide (Int8.toInt32 (AP_ParamT_signed_char_1.op_to_signed_char w.EKF3._gpsGlitchRadiusMax) ≤ (0 : Int32))) && !onGroundNotNavigating && (s.activeHgtSource == AP_NavEKF_Source.SourceZ.GPS) then
        s := { s with lastGpsPosPassTime_ms := s.imuSampleTime_ms }
        s := { s with varInnovVelPos := s.varInnovVelPos.set! 5 (s.varInnovVelPos[5]! * s.hgtTestRatio) }
        hgtCheckPassed := true
        s := { s with lastHgtPassTime_ms := s.imuSampleTime_ms }
      if hgtCheckPassed || s.hgtTimeout || s.badIMUdata then
        if s.onGround then
          let dtBaro : Binary64 := Binary32.toBinary64 (UInt32.toBinary32 (s.imuSampleTime_ms - s.lastHgtPassTime_ms) * (Binary32.ofBits 0x3a83126f /- 1.0e-3 -/))
          let hgtInnovFiltTC : Binary64 := (Binary64.ofBits 0x4000000000000000 /- 2.0 -/)
          let alpha : Binary64 := Estimator_lib.constrain_value_line_double (dtBaro / (dtBaro + hgtInnovFiltTC)) (Binary64.ofBits 0x0000000000000000 /- (double)0 -/) (Binary64.ofBits 0x3ff0000000000000 /- (double)1 -/) (Int32.toUInt32 (1054 : Int32))
          s := { s with hgtInnovFiltState := s.hgtInnovFiltState + (s.innovVelPos[5]! - s.hgtInnovFiltState) * alpha }
        else
          s := { s with hgtInnovFiltState := (Binary64.ofBits 0x0000000000000000 /- 0.0f -/) }
        if s.hgtTimeout then
          s := ResetHeight s w
          s := { s with fuseHgtData := false }
      else
        s := { s with fuseHgtData := false }
    if s.fuseVelData then
      fuseData := fuseData.set! 0 true
      fuseData := fuseData.set! 1 true
      if s.fuseVelVertData || s.fusingStationaryZeroVel then
        fuseData := fuseData.set! 2 true
    if s.fusePosData then
      fuseData := fuseData.set! 3 true
      fuseData := fuseData.set! 4 true
    if s.fuseHgtData then
      fuseData := fuseData.set! 5 true
    for obsIndex' in [0:6] do
      let obsIndex : UInt8 := Nat.toUInt8 obsIndex'
      if fuseData[UInt8.toNat obsIndex]! then
        stateIndex := Int8.toUInt8 (Int32.toInt8 ((4 : Int32) + UInt32.toInt32 (UInt8.toUInt32 obsIndex)))
        if UInt32.toInt32 (UInt8.toUInt32 obsIndex) ≤ (2 : Int32) then
          s := { s with innovVelPos := s.innovVelPos.set! (UInt8.toNat obsIndex) (s.statesArray[4 + UInt8.toNat obsIndex]! - s.velPosObs[UInt8.toNat obsIndex]!) }
          if AP_NavEKF_Source.useVelXYSource w.EKF3.sources AP_NavEKF_Source.SourceXY.GPS s.core_index then
            R_OBS := R_OBS.set! (UInt8.toNat obsIndex) (R_OBS[UInt8.toNat obsIndex]! * Estimator_lib.sq_double s.gpsNoiseScaler)
        else if UInt32.toInt32 (UInt8.toUInt32 obsIndex) == (3 : Int32) || UInt32.toInt32 (UInt8.toUInt32 obsIndex) == (4 : Int32) then
          s := { s with innovVelPos := s.innovVelPos.set! (UInt8.toNat obsIndex) (s.statesArray[7 + UInt8.toNat (Int8.toUInt8 (Int32.toInt8 (UInt32.toInt32 (UInt8.toUInt32 obsIndex) - (3 : Int32))))]! - s.velPosObs[UInt8.toNat obsIndex]!) }
          if AP_NavEKF_Source.getPosXYSource w.EKF3.sources s.core_index == AP_NavEKF_Source.SourceXY.GPS then
            R_OBS := R_OBS.set! (UInt8.toNat obsIndex) (R_OBS[UInt8.toNat obsIndex]! * Estimator_lib.sq_double s.gpsNoiseScaler)
        else if UInt32.toInt32 (UInt8.toUInt32 obsIndex) == (5 : Int32) then
          s := { s with innovVelPos := s.innovVelPos.set! (UInt8.toNat obsIndex) (s.statesArray[7 + UInt8.toNat (Int8.toUInt8 (Int32.toInt8 (UInt32.toInt32 (UInt8.toUInt32 obsIndex) - (3 : Int32))))]! - s.velPosObs[UInt8.toNat obsIndex]!) }
          let gndMaxBaroErr : Binary64 := Binary32.toBinary64 (Estimator_lib.MAX_AP_ParamT_float_4_float w.EKF3._baroGndEffectDeadZone (Binary32.ofBits 0x00000000 /- 0.0 -/))
          let gndBaroInnovFloor : Binary64 := (Binary64.ofBits 0xbfe0000000000000 /- -0.5 -/)
          if (AP_DAL.get_touchdown_expected w.heap'AP_DAL[(WPtr.index w.AP_DAL'_singleton)]! || AP_DAL.get_takeoff_expected w.heap'AP_DAL[(WPtr.index w.AP_DAL'_singleton)]!) && s.activeHgtSource == AP_NavEKF_Source.SourceZ.BARO then
            s := { s with innovVelPos := s.innovVelPos.set! 5 (s.innovVelPos[5]! + Estimator_lib.constrain_value_line_double (-s.innovVelPos[5]! + gndBaroInnovFloor) (Binary64.ofBits 0x0000000000000000 /- (double)0 -/) (gndBaroInnovFloor + gndMaxBaroErr) (Int32.toUInt32 (1119 : Int32))) }
        s := { s with varInnovVelPos := s.varInnovVelPos.set! (UInt8.toNat obsIndex) (s.Pmut[UInt8.toNat stateIndex * 24 + UInt8.toNat stateIndex]! + R_OBS[UInt8.toNat obsIndex]!) }
        SK := (Binary64.ofBits 0x3ff0000000000000 /- 1.0f -/) / s.varInnovVelPos[UInt8.toNat obsIndex]!
        let mut kalman_mask : UInt32 := Int32.toUInt32 (((1 : Int32) <<< (10 : Int32)) - (1 : Int32))
        if !s.inhibitDelAngBiasStates then
          for i'6' in [10:13] do
            let i'6 : UInt8 := Nat.toUInt8 i'6'
            let mut poorObservability : Bool := false
            if UInt32.toInt32 (NavEKF3_core.AidingMode.toInt s.PV_AidingMode) == UInt32.toInt32 (NavEKF3_core.AidingMode.toInt NavEKF3_core.AidingMode.AID_NONE) then
              let axisIndex : UInt8 := Int8.toUInt8 (Int32.toInt8 (UInt32.toInt32 (UInt8.toUInt32 i'6) - (10 : Int32)))
              if UInt32.toInt32 (UInt8.toUInt32 axisIndex) == (0 : Int32) then
                poorObservability := decide (Binary64.abs s.prevTnb.a.z > (Binary64.ofBits 0x3fe6a09e667f3bcd /- (double)6369051672525773/9007199254740992 -/))
              else if UInt32.toInt32 (UInt8.toUInt32 axisIndex) == (1 : Int32) then
                poorObservability := decide (Binary64.abs s.prevTnb.b.z > (Binary64.ofBits 0x3fe6a09e667f3bcd /- (double)6369051672525773/9007199254740992 -/))
              else
                poorObservability := decide (Binary64.abs s.prevTnb.c.z > (Binary64.ofBits 0x3fe6a09e667f3bcd /- (double)6369051672525773/9007199254740992 -/))
            if !poorObservability then
              kalman_mask := kalman_mask ||| Int32.toUInt32 ((1 : Int32) <<< UInt32.toInt32 (UInt8.toUInt32 i'6))
        let horizInhibit : Bool := UInt32.toInt32 (NavEKF3_core.AidingMode.toInt s.PV_AidingMode) == UInt32.toInt32 (NavEKF3_core.AidingMode.toInt NavEKF3_core.AidingMode.AID_NONE) && UInt32.toInt32 (UInt8.toUInt32 obsIndex) != (2 : Int32) && UInt32.toInt32 (UInt8.toUInt32 obsIndex) != (5 : Int32)
        if !horizInhibit && !s.inhibitDelVelBiasStates && !s.badIMUdata then
          for i'7' in [13:16] do
            let i'7 : UInt8 := Nat.toUInt8 i'7'
            if !s.dvelBiasAxisInhibit[Int32.toNatClampNeg (UInt32.toInt32 (UInt8.toUInt32 i'7) - (13 : Int32))]! then
              kalman_mask := kalman_mask ||| Int32.toUInt32 ((1 : Int32) <<< UInt32.toInt32 (UInt8.toUInt32 i'7))
        if !s.inhibitMagStates then
          kalman_mask := kalman_mask ||| Int32.toUInt32 (((1 : Int32) <<< (16 : Int32)) ||| ((1 : Int32) <<< (17 : Int32)) ||| ((1 : Int32) <<< (18 : Int32)) ||| ((1 : Int32) <<< (19 : Int32)) ||| ((1 : Int32) <<< (20 : Int32)) ||| ((1 : Int32) <<< (21 : Int32)))
        if !s.inhibitWindStates && !s.treatWindStatesAsTruth then
          kalman_mask := kalman_mask ||| Int32.toUInt32 (((1 : Int32) <<< (22 : Int32)) ||| ((1 : Int32) <<< (23 : Int32)))
        for i'8' in [0:24] do
          let i'8 : Int32 := Nat.toInt32 i'8'
          let mut res : Binary64 := (Binary64.ofBits 0x0000000000000000 /- 0 -/)
          if kalman_mask &&& Int32.toUInt32 ((1 : Int32) <<< i'8) != (0 : UInt32) then
            res := s.Pmut[Int32.toNatClampNeg i'8 * 24 + UInt8.toNat stateIndex]! * SK
          w := { w with NavEKF_core_common'Kfusion := w.NavEKF_core_common'Kfusion.set! (Int32.toNatClampNeg i'8) res }
        let mut Hfusion : Array Binary64 := Array.replicate 24 (Binary64.ofBits 0x0000000000000000 /- 0.0 -/)  -- uninitialized in C; every element is written before it is read
        Hfusion := Hfusion.set! (UInt8.toNat stateIndex) (Binary64.ofBits 0x3ff0000000000000 /- 1 -/)
        let t'1 : UInt32 := Int32.toUInt32 (0 : Int32)
        let t'2 : UInt32 := UInt8.toUInt32 s.stateIndexLim
        for i'9' in [0:((Int.ofNat t'2.toNat) - (Int.ofNat t'1.toNat) + 1).toNat] do  -- C++ loop bounded by a runtime value (--runtime-loops)
          let i'9 : UInt32 := t'1 + Nat.toUInt32 i'9'
          let t'3 : UInt32 := Int32.toUInt32 (0 : Int32)
          let t'4 : UInt32 := UInt8.toUInt32 s.stateIndexLim
          for j' in [0:((Int.ofNat t'4.toNat) - (Int.ofNat t'3.toNat) + 1).toNat] do  -- C++ loop bounded by a runtime value (--runtime-loops)
            let j : UInt32 := t'3 + Nat.toUInt32 j'
            let mut res'2 : Binary64 := (Binary64.ofBits 0x0000000000000000 /- 0 -/)
            res'2 := res'2 + (w.NavEKF_core_common'Kfusion[UInt32.toNat i'9]! * Hfusion[UInt8.toNat stateIndex]!) * s.Pmut[UInt8.toNat stateIndex * 24 + UInt32.toNat j]!
            w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! (UInt32.toNat i'9 * 24 + UInt32.toNat j) res'2 }
        let (t'5, t'6) := FinishFusion s w s.innovVelPos[UInt8.toNat obsIndex]! false
        s := t'5
        let fault : Bool := t'6
        if UInt32.toInt32 (UInt8.toUInt32 obsIndex) == (0 : Int32) then
          s := { s with faultStatus.bad_nvel := fault }
        else if UInt32.toInt32 (UInt8.toUInt32 obsIndex) == (1 : Int32) then
          s := { s with faultStatus.bad_evel := fault }
        else if UInt32.toInt32 (UInt8.toUInt32 obsIndex) == (2 : Int32) then
          s := { s with faultStatus.bad_dvel := fault }
        else if UInt32.toInt32 (UInt8.toUInt32 obsIndex) == (3 : Int32) then
          s := { s with faultStatus.bad_npos := fault }
        else if UInt32.toInt32 (UInt8.toUInt32 obsIndex) == (4 : Int32) then
          s := { s with faultStatus.bad_epos := fault }
        else if UInt32.toInt32 (UInt8.toUInt32 obsIndex) == (5 : Int32) then
          s := { s with faultStatus.bad_dpos := fault }
  return (s, w)

/-- C++ `void NavEKF3_core::SelectVelPosFusion()`, `AP_NavEKF3/AP_NavEKF3_PosVelFusion.cpp:507-747`. -/
def SelectVelPosFusion (s : State) (w : World) (o : Outputs) : State × World × Outputs := Id.run do
  let mut s := s
  let mut w := w
  let mut o := o
  if s.magFusePerformed && decide (s.dtIMUavg < (Binary64.ofBits 0x3f747ae140000000 /- 0.005f -/)) && !s.posVelFusionDelayed then
    s := { s with posVelFusionDelayed := true }
    return (s, w, o)
  else
    s := { s with posVelFusionDelayed := false }
  let (t'1, t'2, t'3) := readGpsData s w o
  w := t'2
  s := t'1
  o := t'3
  s := readGpsYawData s w
  let (t'4, t'5, t'6) := EKF_obs_buffer_t_NavEKF3_core_gps_elements.recall_gps_elements_uint32_t s.storedGPS s.gpsDataDelayed s.imuDataDelayed.time_ms
  s := { s with storedGPS := t'4 }
  s := { s with gpsDataDelayed := t'5 }
  s := { s with gpsDataToFuse := t'6 && !s.waitingForGpsChecks }
  if s.gpsDataToFuse then
    s := { s with gpsDataDelayed := CorrectGPSForAntennaOffset s w s.gpsDataDelayed }
    let (t'7, t'8) := CalculateVelInnovationsAndVariances s s.gpsDataDelayed.vel (Binary32.toBinary64 (AP_ParamT_float_4.get_void w.EKF3._gpsHorizVelNoise)) (Binary32.toBinary64 w.EKF3.gpsNEVelVarAccScale) s.gpsVelInnov s.gpsVelVarInnov
    s := { s with gpsVelInnov := t'7 }
    s := { s with gpsVelVarInnov := t'8 }
    s := { s with gpsRetrieveTime_ms := AP_DAL.millis w.heap'AP_DAL[(WPtr.index w.AP_DAL'_singleton)]! }
  let posxy_source : AP_NavEKF_Source.SourceXY := AP_NavEKF_Source.getPosXYSource w.EKF3.sources s.core_index
  if posxy_source != s.posxy_source_last then
    s := { s with posxy_source_reset := (posxy_source != AP_NavEKF_Source.SourceXY.NONE) }
    s := { s with posxy_source_last := posxy_source }
  s := { s with fusePosData := false }
  s := { s with fuseVelData := false }
  if s.gpsDataToFuse && (UInt32.toInt32 (NavEKF3_core.AidingMode.toInt s.PV_AidingMode) == UInt32.toInt32 (NavEKF3_core.AidingMode.toInt NavEKF3_core.AidingMode.AID_ABSOLUTE)) && (posxy_source == AP_NavEKF_Source.SourceXY.GPS) then
    s := { s with fuseVelData := AP_NavEKF_Source.useVelXYSource w.EKF3.sources AP_NavEKF_Source.SourceXY.GPS s.core_index }
    s := { s with fuseVelVertData := AP_NavEKF_Source.useVelZSource w.EKF3.sources AP_NavEKF_Source.SourceZ.GPS s.core_index && s.useGpsVertVel }
    s := { s with fusePosData := true }
    if s.fuseVelData then
      s := { s with velPosObs := s.velPosObs.set! 0 s.gpsDataDelayed.vel.x }
      s := { s with velPosObs := s.velPosObs.set! 1 s.gpsDataDelayed.vel.y }
    if s.fuseVelVertData then
      s := { s with velPosObs := s.velPosObs.set! 2 s.gpsDataDelayed.vel.z }
    let gpsloc : Location.State := Location.init_int32_t3_AltFrame s.gpsDataDelayed.lat s.gpsDataDelayed.lng (0 : Int32) Location.AltFrame.ABSOLUTE
    let posxy : Vector2p.State := Location.get_distance_NE_ftype s.EKF_origin gpsloc
    s := { s with velPosObs := s.velPosObs.set! 3 posxy.x }
    s := { s with velPosObs := s.velPosObs.set! 4 posxy.y }
  if s.gpsYawResetRequest then
    let (t'9, t'10, t'11) := realignYawGPS s w o false
    w := t'10
    s := t'9
    o := t'11
  s := selectHeightForFusion s w
  if s.gpsDataToFuse && (UInt32.toInt32 (NavEKF3_core.AidingMode.toInt s.PV_AidingMode) == UInt32.toInt32 (NavEKF3_core.AidingMode.toInt NavEKF3_core.AidingMode.AID_ABSOLUTE)) && (posxy_source == AP_NavEKF_Source.SourceXY.GPS) && (UInt32.toInt32 (UInt8.toUInt32 s.gpsDataDelayed.sensor_idx) != UInt32.toInt32 (UInt8.toUInt32 s.last_gps_idx) || s.posxy_source_reset) then
    s := { s with posxy_source_reset := false }
    s := { s with last_gps_idx := s.gpsDataDelayed.sensor_idx }
    let gpsloc'2 : Location.State := Location.init_int32_t3_AltFrame s.gpsDataDelayed.lat s.gpsDataDelayed.lng (0 : Int32) Location.AltFrame.ABSOLUTE
    let posxy'2 : Vector2p.State := Location.get_distance_NE_ftype s.EKF_origin gpsloc'2
    s := ResetPositionNE s posxy'2.x posxy'2.y
    if s.activeHgtSource == AP_NavEKF_Source.SourceZ.GPS then
      s := ResetPositionD s (-s.hgtMea)
  s := { s with fusingStationaryZeroVel := false }
  if s.fuseHgtData && UInt32.toInt32 (NavEKF3_core.AidingMode.toInt s.PV_AidingMode) == UInt32.toInt32 (NavEKF3_core.AidingMode.toInt NavEKF3_core.AidingMode.AID_NONE) then
    if assume_zero_sideslip w && s.tiltAlignComplete && s.motorsArmed then
      s := { s with fusePosData := false }
      s := { s with velPosObs := s.velPosObs.set! 0 (Binary64.ofBits 0x0000000000000000 /- 0.0f -/) }
      s := { s with velPosObs := s.velPosObs.set! 1 (Binary64.ofBits 0x0000000000000000 /- 0.0f -/) }
      s := { s with velPosObs := s.velPosObs.set! 2 (s.statesArray[6]!) }
      let mut resetVelNE : Bool := !s.prevMotorsArmed
      if s.imuDataDelayed.delVel.x > (Binary64.ofBits 0x4025931b00000000 /- (double)1413915/131072 -/) * s.imuDataDelayed.delVelDT then
        s := { s with lastLaunchAccelTime_ms := s.imuSampleTime_ms }
        s := { s with fuseVelData := false }
        s := { s with fuseVelVertData := false }
        resetVelNE := true
      else if s.lastLaunchAccelTime_ms != Int32.toUInt32 (0 : Int32) && decide ((s.imuSampleTime_ms - s.lastLaunchAccelTime_ms) < Int32.toUInt32 (10000 : Int32)) then
        s := { s with fuseVelData := false }
        s := { s with fuseVelVertData := false }
        resetVelNE := true
      else
        s := { s with fuseVelData := true }
        s := { s with fuseVelVertData := true }
      if resetVelNE then
        s := { s with statesArray := s.statesArray.set! 4 (Binary64.ofBits 0x0000000000000000 /- 0.0f -/) }
        s := { s with statesArray := s.statesArray.set! 5 (Binary64.ofBits 0x0000000000000000 /- 0.0f -/) }
    else
      s := { s with fusePosData := true }
      let onGroundNotFlying : Bool := s.onGroundNotMoving
      if onGroundNotFlying && s.tiltAlignComplete then
        s := { s with fuseVelData := true }
        s := { s with fusingStationaryZeroVel := true }
        s := { s with velPosObs := s.velPosObs.set! 0 (Binary64.ofBits 0x0000000000000000 /- 0.0f -/) }
        s := { s with velPosObs := s.velPosObs.set! 1 (Binary64.ofBits 0x0000000000000000 /- 0.0f -/) }
        s := { s with velPosObs := s.velPosObs.set! 2 (Binary64.ofBits 0x0000000000000000 /- 0.0f -/) }
      else
        s := { s with fuseVelData := false }
      s := { s with velPosObs := s.velPosObs.set! 3 s.lastKnownPositionNE.x }
      s := { s with velPosObs := s.velPosObs.set! 4 s.lastKnownPositionNE.y }
  let onGroundNotFlying'2 : Bool := s.onGroundNotMoving
  if s.fuseHgtData && UInt32.toInt32 (NavEKF3_core.AidingMode.toInt s.PV_AidingMode) != UInt32.toInt32 (NavEKF3_core.AidingMode.toInt NavEKF3_core.AidingMode.AID_NONE) && onGroundNotFlying'2 then
    let velAidTimeout_ms : UInt32 := Int32.toUInt32 (1000 : Int32)
    let haveRecentGpsVel : Bool := (decide (s.imuSampleTime_ms - s.lastVelPassTime_ms < velAidTimeout_ms))
    let haveRecentFlowVel : Bool := false
    let haveRecentBodyVel : Bool := (decide (s.imuSampleTime_ms - s.bodyOdm.prevFuseTime_ms < velAidTimeout_ms))
    if !haveRecentGpsVel && !haveRecentFlowVel && !haveRecentBodyVel then
      s := { s with fuseVelData := true }
      s := { s with fusingStationaryZeroVel := true }
      s := { s with velPosObs := s.velPosObs.set! 0 (Binary64.ofBits 0x0000000000000000 /- 0.0f -/) }
      s := { s with velPosObs := s.velPosObs.set! 1 (Binary64.ofBits 0x0000000000000000 /- 0.0f -/) }
      s := { s with velPosObs := s.velPosObs.set! 2 (Binary64.ofBits 0x0000000000000000 /- 0.0f -/) }
  if s.fuseVelData || s.fuseVelVertData || s.fusePosData || s.fuseHgtData then
    let (t'12, t'13) := FuseVelPosNED s w
    w := t'13
    s := t'12
    s := { s with fuseVelData := false }
    s := { s with fuseVelVertData := false }
    s := { s with fuseHgtData := false }
    s := { s with fusePosData := false }
  return (s, w, o)

end NavEKF3_core

namespace NavEKF3_core

/-- C++ `void NavEKF3_core::readAirSpdData()`, `AP_NavEKF3/AP_NavEKF3_Measurements.cpp:864-924`. -/
def readAirSpdData (s : State) (w : World) : State := Id.run do
  let mut s := s
  let EAS2TAS : Binary32 := AP_DAL.get_EAS2TAS w.heap'AP_DAL[(WPtr.index w.AP_DAL'_singleton)]!
  if useAirspeed s w then
    let airspeed : WPtr := AP_DAL.airspeed w.heap'AP_DAL[(WPtr.index w.AP_DAL'_singleton)]!
    if (airspeed != WPtr.null) && decide ((AP_DAL_Airspeed.last_update_ms_uint8_t w.heap'AP_DAL_Airspeed[(WPtr.index airspeed)]! s.selected_airspeed - s.tas.receivedTime_ms) > UInt8.toUInt32 w.EKF3.sensorIntervalMin_ms) then
      s := { s with tas.dataNew.allowFusion := AP_DAL_Airspeed.healthy_uint8_t w.heap'AP_DAL_Airspeed[(WPtr.index airspeed)]! s.selected_airspeed && AP_DAL_Airspeed.use_uint8_t w.heap'AP_DAL_Airspeed[(WPtr.index airspeed)]! s.selected_airspeed }
      if s.tas.dataNew.allowFusion then
        s := { s with tas.dataNew.tas := Binary32.toBinary64 (AP_DAL_Airspeed.get_airspeed_uint8_t w.heap'AP_DAL_Airspeed[(WPtr.index airspeed)]! s.selected_airspeed * EAS2TAS) }
        s := { s with tas.receivedTime_ms := AP_DAL_Airspeed.last_update_ms_uint8_t w.heap'AP_DAL_Airspeed[(WPtr.index airspeed)]! s.selected_airspeed }
        s := { s with tas.dataNew.time_ms := s.tas.receivedTime_ms - UInt16.toUInt32 w.EKF3.tasDelay_ms }
        s := { s with tas.dataNew.tasVariance := Binary32.toBinary64 (Estimator_lib.sq_float (Estimator_lib.MAX_float2 (AP_ParamT_float_4.op_to_float w.EKF3._easNoise * EAS2TAS) (Binary32.ofBits 0x3f000000 /- 0.5f -/))) }
        s := { s with tas.dataNew.time_ms := s.tas.dataNew.time_ms - Int32.toUInt32 (UInt32.toInt32 (UInt8.toUInt32 s.localFilterTimeStep_ms) / (2 : Int32)) }
        s := { s with tas.stored := EKF_obs_buffer_t_NavEKF3_core_tas_elements.push_tas_elements s.tas.stored s.tas.dataNew }
    let (t'1, t'2, t'3) := EKF_obs_buffer_t_NavEKF3_core_tas_elements.recall_tas_elements_uint32_t s.tas.stored s.tas.dataDelayed s.imuDataDelayed.time_ms
    s := { s with tas.stored := t'1 }
    s := { s with tas.dataDelayed := t'2 }
    s := { s with tas.dataToFuse := t'3 }
  else if assume_zero_sideslip w then
    if Estimator_lib.is_positive_double s.defaultAirSpeed then
      if s.imuDataDelayed.time_ms - s.tas.prevStepTime_ms > Int32.toUInt32 (200 : Int32) then
        s := { s with tas.dataDelayed.tas := s.defaultAirSpeed * Binary32.toBinary64 EAS2TAS }
        s := { s with tas.dataDelayed.tasVariance := Estimator_lib.MAX_double_float s.defaultAirSpeedVariance (Estimator_lib.sq_float (Estimator_lib.MAX_AP_ParamT_float_4_float w.EKF3._easNoise (Binary32.ofBits 0x3f000000 /- 0.5f -/))) }
        s := { s with tas.dataToFuse := true }
        s := { s with tas.dataDelayed.allowFusion := true }
        s := { s with tas.dataDelayed.time_ms := s.imuDataDelayed.time_ms }
      else
        s := { s with tas.dataToFuse := false }
        s := { s with tas.dataDelayed.allowFusion := false }
    else if s.lastAspdEstIsValid && !s.windStateIsObservable then
      if s.lastAspdEstIsValid && decide (s.imuDataDelayed.time_ms - s.tas.prevStepTime_ms > Int32.toUInt32 (200 : Int32)) then
        s := { s with tas.dataDelayed.tas := s.lastAirspeedEstimate }
        s := { s with tas.dataDelayed.tasVariance := Estimator_lib.sq_double (Estimator_lib.MAX_float_double (Estimator_lib.MAX_AP_ParamT_float_4_float w.EKF3._easNoise (Binary32.ofBits 0x3f000000 /- 0.5f -/)) ((Binary64.ofBits 0x3fe0000000000000 /- 0.5f -/) * s.lastAirspeedEstimate)) }
        s := { s with tas.dataToFuse := true }
        s := { s with tas.dataDelayed.allowFusion := true }
        s := { s with tas.dataDelayed.time_ms := s.imuDataDelayed.time_ms }
      else
        s := { s with tas.dataToFuse := false }
        s := { s with tas.dataDelayed.allowFusion := false }
  else
    s := { s with tas.dataToFuse := false }
    s := { s with tas.dataDelayed.allowFusion := false }
  return s

/-- C++ `void NavEKF3_core::FuseAirspeed()`, `AP_NavEKF3/AP_NavEKF3_AirDataFusion.cpp:30-151`. -/
def FuseAirspeed (s : State) (w : World) : State × World := Id.run do
  let mut s := s
  let mut w := w
  let mut SH_TAS : Array Binary64 := Array.replicate 3 (Binary64.ofBits 0x0000000000000000 /- 0.0 -/)  -- uninitialized in C; every element is written before it is read
  let mut SK_TAS : Array Binary64 := Array.replicate 2 (Binary64.ofBits 0x0000000000000000 /- 0.0 -/)  -- uninitialized in C; every element is written before it is read
  let mut H_TAS : Array Binary64 := Array.replicate 24 (Binary64.ofBits 0x0000000000000000 /- 0.0 -/)
  let vn : Binary64 := s.statesArray[4]!
  let ve : Binary64 := s.statesArray[5]!
  let vd : Binary64 := s.statesArray[6]!
  let vwn : Binary64 := s.statesArray[22]!
  let vwe : Binary64 := s.statesArray[23]!
  let VtasPred : Binary64 := Estimator_lib.norm_double3 (ve - vwe) (vn - vwn) vd
  if VtasPred > (Binary64.ofBits 0x3ff0000000000000 /- 1.0f -/) then
    s := { s with tas.innov := VtasPred - s.tas.dataDelayed.tas }
    SH_TAS := SH_TAS.set! 0 ((Binary64.ofBits 0x3ff0000000000000 /- 1.0f -/) / VtasPred)
    SH_TAS := SH_TAS.set! 1 ((SH_TAS[0]! * ((Binary64.ofBits 0x4000000000000000 /- 2.0f -/) * ve - (Binary64.ofBits 0x4000000000000000 /- 2.0f -/) * vwe)) * (Binary64.ofBits 0x3fe0000000000000 /- 0.5f -/))
    SH_TAS := SH_TAS.set! 2 ((SH_TAS[0]! * ((Binary64.ofBits 0x4000000000000000 /- 2.0f -/) * vn - (Binary64.ofBits 0x4000000000000000 /- 2.0f -/) * vwn)) * (Binary64.ofBits 0x3fe0000000000000 /- 0.5f -/))
    H_TAS := H_TAS.set! 4 (SH_TAS[2]!)
    H_TAS := H_TAS.set! 5 (SH_TAS[1]!)
    H_TAS := H_TAS.set! 6 (vd * SH_TAS[0]!)
    H_TAS := H_TAS.set! 22 (-SH_TAS[2]!)
    H_TAS := H_TAS.set! 23 (-SH_TAS[1]!)
    let temp : Binary64 := (s.tas.dataDelayed.tasVariance + SH_TAS[2]! * (s.Pmut[100]! * SH_TAS[2]! + s.Pmut[124]! * SH_TAS[1]! - s.Pmut[532]! * SH_TAS[2]! - s.Pmut[556]! * SH_TAS[1]! + s.Pmut[148]! * vd * SH_TAS[0]!) + SH_TAS[1]! * (s.Pmut[101]! * SH_TAS[2]! + s.Pmut[125]! * SH_TAS[1]! - s.Pmut[533]! * SH_TAS[2]! - s.Pmut[557]! * SH_TAS[1]! + s.Pmut[149]! * vd * SH_TAS[0]!) - SH_TAS[2]! * (s.Pmut[118]! * SH_TAS[2]! + s.Pmut[142]! * SH_TAS[1]! - s.Pmut[550]! * SH_TAS[2]! - s.Pmut[574]! * SH_TAS[1]! + s.Pmut[166]! * vd * SH_TAS[0]!) - SH_TAS[1]! * (s.Pmut[119]! * SH_TAS[2]! + s.Pmut[143]! * SH_TAS[1]! - s.Pmut[551]! * SH_TAS[2]! - s.Pmut[575]! * SH_TAS[1]! + s.Pmut[167]! * vd * SH_TAS[0]!) + vd * SH_TAS[0]! * (s.Pmut[102]! * SH_TAS[2]! + s.Pmut[126]! * SH_TAS[1]! - s.Pmut[534]! * SH_TAS[2]! - s.Pmut[558]! * SH_TAS[1]! + s.Pmut[150]! * vd * SH_TAS[0]!))
    if temp ≥ s.tas.dataDelayed.tasVariance then
      SK_TAS := SK_TAS.set! 0 ((Binary64.ofBits 0x3ff0000000000000 /- 1.0f -/) / temp)
      s := { s with faultStatus.bad_airspeed := false }
    else
      let (t'1, t'2) := CovarianceInit s w
      w := t'2
      s := t'1
      s := { s with faultStatus.bad_airspeed := true }
      return (s, w)
    SK_TAS := SK_TAS.set! 1 (SH_TAS[1]!)
    let mut kalman_mask : UInt32 := Int32.toUInt32 (0 : Int32)
    if s.tas.dataDelayed.allowFusion && !s.airDataFusionWindOnly then
      kalman_mask := Int32.toUInt32 (((1 : Int32) <<< (10 : Int32)) - (1 : Int32))
    if s.tas.dataDelayed.allowFusion && !s.inhibitDelAngBiasStates && !s.airDataFusionWindOnly then
      kalman_mask := kalman_mask ||| Int32.toUInt32 (((1 : Int32) <<< (10 : Int32)) ||| ((1 : Int32) <<< (11 : Int32)) ||| ((1 : Int32) <<< (12 : Int32)))
    if s.tas.dataDelayed.allowFusion && !s.inhibitDelVelBiasStates && !s.airDataFusionWindOnly then
      for index' in [0:3] do
        let index : UInt8 := Nat.toUInt8 index'
        let stateIndex : UInt8 := Int8.toUInt8 (Int32.toInt8 (UInt32.toInt32 (UInt8.toUInt32 index) + (13 : Int32)))
        if !s.dvelBiasAxisInhibit[UInt8.toNat index]! then
          kalman_mask := kalman_mask ||| Int32.toUInt32 ((1 : Int32) <<< UInt32.toInt32 (UInt8.toUInt32 stateIndex))
    if s.tas.dataDelayed.allowFusion && !s.inhibitMagStates && !s.airDataFusionWindOnly then
      kalman_mask := kalman_mask ||| Int32.toUInt32 (((1 : Int32) <<< (16 : Int32)) ||| ((1 : Int32) <<< (17 : Int32)) ||| ((1 : Int32) <<< (18 : Int32)) ||| ((1 : Int32) <<< (19 : Int32)) ||| ((1 : Int32) <<< (20 : Int32)) ||| ((1 : Int32) <<< (21 : Int32)))
    if s.tas.dataDelayed.allowFusion && !s.inhibitWindStates && !s.treatWindStatesAsTruth then
      kalman_mask := kalman_mask ||| Int32.toUInt32 (((1 : Int32) <<< (22 : Int32)) ||| ((1 : Int32) <<< (23 : Int32)))
    for i' in [0:24] do
      let i : Int32 := Nat.toInt32 i'
      let mut res : Binary64 := (Binary64.ofBits 0x0000000000000000 /- 0 -/)
      if kalman_mask &&& Int32.toUInt32 ((1 : Int32) <<< i) != (0 : UInt32) then
        res := SK_TAS[0]! * (s.Pmut[Int32.toNatClampNeg i * 24 + 4]! * SH_TAS[2]! - s.Pmut[Int32.toNatClampNeg i * 24 + 22]! * SH_TAS[2]! + s.Pmut[Int32.toNatClampNeg i * 24 + 5]! * SK_TAS[1]! - s.Pmut[Int32.toNatClampNeg i * 24 + 23]! * SK_TAS[1]! + s.Pmut[Int32.toNatClampNeg i * 24 + 6]! * vd * SH_TAS[0]!)
      w := { w with NavEKF_core_common'Kfusion := w.NavEKF_core_common'Kfusion.set! (Int32.toNatClampNeg i) res }
    s := { s with tas.varInnov := (Binary64.ofBits 0x3ff0000000000000 /- 1.0f -/) / SK_TAS[0]! }
    s := { s with tas.testRatio := Estimator_lib.sq_double s.tas.innov / (Estimator_lib.sq_double (Estimator_lib.MAX_double_float ((Binary64.ofBits 0x3f847ae140000000 /- 0.01f -/) * Int16.toBinary64 (AP_ParamT_short_2.op_to_short w.EKF3._tasInnovGate)) (Binary32.ofBits 0x3f800000 /- 1.0f -/)) * s.tas.varInnov) }
    let isConsistent : Bool := (decide (s.tas.testRatio < (Binary64.ofBits 0x3ff0000000000000 /- 1.0f -/))) || s.badIMUdata
    s := { s with tasTimeout := decide ((s.imuSampleTime_ms - s.tas.lastPassTime_ms) > UInt16.toUInt32 w.EKF3.tasRetryTime_ms) }
    if !isConsistent then
      s := { s with tas.lastFailTime_ms := s.imuSampleTime_ms }
    else
      s := { s with tas.lastFailTime_ms := Int32.toUInt32 (0 : Int32) }
    if s.tas.dataDelayed.allowFusion && (isConsistent || (s.tasTimeout && s.posTimeout)) then
      s := { s with tas.lastPassTime_ms := s.imuSampleTime_ms }
      let t'3 : UInt32 := Int32.toUInt32 (0 : Int32)
      let t'4 : UInt32 := UInt8.toUInt32 s.stateIndexLim
      for i'2' in [0:((Int.ofNat t'4.toNat) - (Int.ofNat t'3.toNat) + 1).toNat] do  -- C++ loop bounded by a runtime value (--runtime-loops)
        let i'2 : UInt32 := t'3 + Nat.toUInt32 i'2'
        let t'5 : UInt32 := Int32.toUInt32 (0 : Int32)
        let t'6 : UInt32 := UInt8.toUInt32 s.stateIndexLim
        for j' in [0:((Int.ofNat t'6.toNat) - (Int.ofNat t'5.toNat) + 1).toNat] do  -- C++ loop bounded by a runtime value (--runtime-loops)
          let j : UInt32 := t'5 + Nat.toUInt32 j'
          let mut res'2 : Binary64 := (Binary64.ofBits 0x0000000000000000 /- 0 -/)
          res'2 := res'2 + (w.NavEKF_core_common'Kfusion[UInt32.toNat i'2]! * H_TAS[4]!) * s.Pmut[96 + UInt32.toNat j]!
          res'2 := res'2 + (w.NavEKF_core_common'Kfusion[UInt32.toNat i'2]! * H_TAS[5]!) * s.Pmut[120 + UInt32.toNat j]!
          res'2 := res'2 + (w.NavEKF_core_common'Kfusion[UInt32.toNat i'2]! * H_TAS[6]!) * s.Pmut[144 + UInt32.toNat j]!
          res'2 := res'2 + (w.NavEKF_core_common'Kfusion[UInt32.toNat i'2]! * H_TAS[22]!) * s.Pmut[528 + UInt32.toNat j]!
          res'2 := res'2 + (w.NavEKF_core_common'Kfusion[UInt32.toNat i'2]! * H_TAS[23]!) * s.Pmut[552 + UInt32.toNat j]!
          w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! (UInt32.toNat i'2 * 24 + UInt32.toNat j) res'2 }
      let (t'7, _) := FinishFusion s w s.tas.innov true
      s := t'7
  return (s, w)

/-- C++ `void NavEKF3_core::SelectTasFusion()`, `AP_NavEKF3/AP_NavEKF3_AirDataFusion.cpp:154-176`. -/
def SelectTasFusion (s : State) (w : World) : State × World := Id.run do
  let mut s := s
  let mut w := w
  if s.magFusePerformed && decide (s.dtIMUavg < (Binary64.ofBits 0x3f747ae140000000 /- 0.005f -/)) && !s.airSpdFusionDelayed then
    s := { s with airSpdFusionDelayed := true }
    return (s, w)
  else
    s := { s with airSpdFusionDelayed := false }
  s := readAirSpdData s w
  if s.tas.dataToFuse && s.statesInitialised && !s.inhibitWindStates then
    let (t'1, t'2) := FuseAirspeed s w
    w := t'2
    s := t'1
    s := { s with tas.dataToFuse := false }
    s := { s with tas.prevStepTime_ms := s.imuSampleTime_ms }
  return (s, w)

/-- C++ `bool NavEKF3_core::using_noncompass_for_yaw() const`, `AP_NavEKF3/AP_NavEKF3_Control.cpp:664-676`. -/
def using_noncompass_for_yaw (s : State) (w : World) : Bool := Id.run do
  if s.yaw_source_last == AP_NavEKF_Source.SourceYaw.GPS || s.yaw_source_last == AP_NavEKF_Source.SourceYaw.GPS_COMPASS_FALLBACK || s.yaw_source_last == AP_NavEKF_Source.SourceYaw.GSF || !(use_compass s w) then
    return decide (s.imuSampleTime_ms - s.gpsYaw.lastUseTime_ms < Int32.toUInt32 (5000 : Int32)) || decide (s.imuSampleTime_ms - s.lastSynthYawTime_ms < Int32.toUInt32 (5000 : Int32))
  return false

/-- C++ `void NavEKF3_core::FuseSideslip()`, `AP_NavEKF3/AP_NavEKF3_AirDataFusion.cpp:235-382`. -/
def FuseSideslip (s : State) (w : World) : State × World := Id.run do
  let mut s := s
  let mut w := w
  let R_BETA : Binary64 := (Binary64.ofBits 0x3f9eb851e0000000 /- 0.03f -/)
  let mut SH_BETA : Array Binary64 := Array.replicate 13 (Binary64.ofBits 0x0000000000000000 /- 0.0 -/)  -- uninitialized in C; every element is written before it is read
  let mut SK_BETA : Array Binary64 := Array.replicate 8 (Binary64.ofBits 0x0000000000000000 /- 0.0 -/)  -- uninitialized in C; every element is written before it is read
  let mut vel_rel_wind : Vector3p.State := Vector3p.init_void
  let mut H_BETA : Array Binary64 := Array.replicate 24 (Binary64.ofBits 0x0000000000000000 /- 0.0 -/)  -- uninitialized in C; every element is written before it is read
  let q0 : Binary64 := s.statesArray[0]!
  let q1 : Binary64 := s.statesArray[1]!
  let q2 : Binary64 := s.statesArray[2]!
  let q3 : Binary64 := s.statesArray[3]!
  let vn : Binary64 := s.statesArray[4]!
  let ve : Binary64 := s.statesArray[5]!
  let vd : Binary64 := s.statesArray[6]!
  let vwn : Binary64 := s.statesArray[22]!
  let vwe : Binary64 := s.statesArray[23]!
  vel_rel_wind := { vel_rel_wind with x := vn - vwn }
  vel_rel_wind := { vel_rel_wind with y := ve - vwe }
  vel_rel_wind := { vel_rel_wind with z := vd }
  vel_rel_wind := Matrix3_double.op_mul_Vector3p s.prevTnb vel_rel_wind
  if vel_rel_wind.x > (Binary64.ofBits 0x4014000000000000 /- 5.0f -/) then
    SH_BETA := SH_BETA.set! 0 ((vn - vwn) * (Estimator_lib.sq_double q0 + Estimator_lib.sq_double q1 - Estimator_lib.sq_double q2 - Estimator_lib.sq_double q3) - vd * ((Binary64.ofBits 0x4000000000000000 /- 2 -/) * q0 * q2 - (Binary64.ofBits 0x4000000000000000 /- 2 -/) * q1 * q3) + (ve - vwe) * ((Binary64.ofBits 0x4000000000000000 /- 2 -/) * q0 * q3 + (Binary64.ofBits 0x4000000000000000 /- 2 -/) * q1 * q2))
    if Binary64.abs SH_BETA[0]! ≤ (Binary64.ofBits 0x3e112e0be0000000 /- 1e-9f -/) then
      s := { s with faultStatus.bad_sideslip := true }
      return (s, w)
    else
      s := { s with faultStatus.bad_sideslip := false }
    SH_BETA := SH_BETA.set! 1 ((ve - vwe) * (Estimator_lib.sq_double q0 - Estimator_lib.sq_double q1 + Estimator_lib.sq_double q2 - Estimator_lib.sq_double q3) + vd * ((Binary64.ofBits 0x4000000000000000 /- 2 -/) * q0 * q1 + (Binary64.ofBits 0x4000000000000000 /- 2 -/) * q2 * q3) - (vn - vwn) * ((Binary64.ofBits 0x4000000000000000 /- 2 -/) * q0 * q3 - (Binary64.ofBits 0x4000000000000000 /- 2 -/) * q1 * q2))
    SH_BETA := SH_BETA.set! 2 (vn - vwn)
    SH_BETA := SH_BETA.set! 3 (ve - vwe)
    SH_BETA := SH_BETA.set! 4 ((Binary64.ofBits 0x3ff0000000000000 /- 1 -/) / Estimator_lib.sq_double SH_BETA[0]!)
    SH_BETA := SH_BETA.set! 5 ((Binary64.ofBits 0x3ff0000000000000 /- 1 -/) / SH_BETA[0]!)
    SH_BETA := SH_BETA.set! 6 (SH_BETA[5]! * (Estimator_lib.sq_double q0 - Estimator_lib.sq_double q1 + Estimator_lib.sq_double q2 - Estimator_lib.sq_double q3))
    SH_BETA := SH_BETA.set! 7 (Estimator_lib.sq_double q0 + Estimator_lib.sq_double q1 - Estimator_lib.sq_double q2 - Estimator_lib.sq_double q3)
    SH_BETA := SH_BETA.set! 8 ((Binary64.ofBits 0x4000000000000000 /- 2 -/) * q0 * SH_BETA[3]! - (Binary64.ofBits 0x4000000000000000 /- 2 -/) * q3 * SH_BETA[2]! + (Binary64.ofBits 0x4000000000000000 /- 2 -/) * q1 * vd)
    SH_BETA := SH_BETA.set! 9 ((Binary64.ofBits 0x4000000000000000 /- 2 -/) * q0 * SH_BETA[2]! + (Binary64.ofBits 0x4000000000000000 /- 2 -/) * q3 * SH_BETA[3]! - (Binary64.ofBits 0x4000000000000000 /- 2 -/) * q2 * vd)
    SH_BETA := SH_BETA.set! 10 ((Binary64.ofBits 0x4000000000000000 /- 2 -/) * q2 * SH_BETA[2]! - (Binary64.ofBits 0x4000000000000000 /- 2 -/) * q1 * SH_BETA[3]! + (Binary64.ofBits 0x4000000000000000 /- 2 -/) * q0 * vd)
    SH_BETA := SH_BETA.set! 11 ((Binary64.ofBits 0x4000000000000000 /- 2 -/) * q1 * SH_BETA[2]! + (Binary64.ofBits 0x4000000000000000 /- 2 -/) * q2 * SH_BETA[3]! + (Binary64.ofBits 0x4000000000000000 /- 2 -/) * q3 * vd)
    SH_BETA := SH_BETA.set! 12 ((Binary64.ofBits 0x4000000000000000 /- 2 -/) * q0 * q3)
    H_BETA := H_BETA.set! 0 (SH_BETA[5]! * SH_BETA[8]! - SH_BETA[1]! * SH_BETA[4]! * SH_BETA[9]!)
    H_BETA := H_BETA.set! 1 (SH_BETA[5]! * SH_BETA[10]! - SH_BETA[1]! * SH_BETA[4]! * SH_BETA[11]!)
    H_BETA := H_BETA.set! 2 (SH_BETA[5]! * SH_BETA[11]! + SH_BETA[1]! * SH_BETA[4]! * SH_BETA[10]!)
    H_BETA := H_BETA.set! 3 (-SH_BETA[5]! * SH_BETA[9]! - SH_BETA[1]! * SH_BETA[4]! * SH_BETA[8]!)
    H_BETA := H_BETA.set! 4 (-SH_BETA[5]! * (SH_BETA[12]! - (Binary64.ofBits 0x4000000000000000 /- 2 -/) * q1 * q2) - SH_BETA[1]! * SH_BETA[4]! * SH_BETA[7]!)
    H_BETA := H_BETA.set! 5 (SH_BETA[6]! - SH_BETA[1]! * SH_BETA[4]! * (SH_BETA[12]! + (Binary64.ofBits 0x4000000000000000 /- 2 -/) * q1 * q2))
    H_BETA := H_BETA.set! 6 (SH_BETA[5]! * ((Binary64.ofBits 0x4000000000000000 /- 2 -/) * q0 * q1 + (Binary64.ofBits 0x4000000000000000 /- 2 -/) * q2 * q3) + SH_BETA[1]! * SH_BETA[4]! * ((Binary64.ofBits 0x4000000000000000 /- 2 -/) * q0 * q2 - (Binary64.ofBits 0x4000000000000000 /- 2 -/) * q1 * q3))
    for i' in [7:22] do
      let i : UInt8 := Nat.toUInt8 i'
      H_BETA := H_BETA.set! (UInt8.toNat i) (Binary64.ofBits 0x0000000000000000 /- 0.0f -/)
    H_BETA := H_BETA.set! 22 (SH_BETA[5]! * (SH_BETA[12]! - (Binary64.ofBits 0x4000000000000000 /- 2 -/) * q1 * q2) + SH_BETA[1]! * SH_BETA[4]! * SH_BETA[7]!)
    H_BETA := H_BETA.set! 23 (SH_BETA[1]! * SH_BETA[4]! * (SH_BETA[12]! + (Binary64.ofBits 0x4000000000000000 /- 2 -/) * q1 * q2) - SH_BETA[6]!)
    let temp : Binary64 := (R_BETA - (SH_BETA[5]! * (SH_BETA[12]! - (Binary64.ofBits 0x4000000000000000 /- 2 -/) * q1 * q2) + SH_BETA[1]! * SH_BETA[4]! * SH_BETA[7]!) * (s.Pmut[532]! * (SH_BETA[5]! * (SH_BETA[12]! - (Binary64.ofBits 0x4000000000000000 /- 2 -/) * q1 * q2) + SH_BETA[1]! * SH_BETA[4]! * SH_BETA[7]!) - s.Pmut[100]! * (SH_BETA[5]! * (SH_BETA[12]! - (Binary64.ofBits 0x4000000000000000 /- 2 -/) * q1 * q2) + SH_BETA[1]! * SH_BETA[4]! * SH_BETA[7]!) + s.Pmut[124]! * (SH_BETA[6]! - SH_BETA[1]! * SH_BETA[4]! * (SH_BETA[12]! + (Binary64.ofBits 0x4000000000000000 /- 2 -/) * q1 * q2)) - s.Pmut[556]! * (SH_BETA[6]! - SH_BETA[1]! * SH_BETA[4]! * (SH_BETA[12]! + (Binary64.ofBits 0x4000000000000000 /- 2 -/) * q1 * q2)) + s.Pmut[4]! * (SH_BETA[5]! * SH_BETA[8]! - SH_BETA[1]! * SH_BETA[4]! * SH_BETA[9]!) + s.Pmut[28]! * (SH_BETA[5]! * SH_BETA[10]! - SH_BETA[1]! * SH_BETA[4]! * SH_BETA[11]!) + s.Pmut[52]! * (SH_BETA[5]! * SH_BETA[11]! + SH_BETA[1]! * SH_BETA[4]! * SH_BETA[10]!) - s.Pmut[76]! * (SH_BETA[5]! * SH_BETA[9]! + SH_BETA[1]! * SH_BETA[4]! * SH_BETA[8]!) + s.Pmut[148]! * (SH_BETA[5]! * ((Binary64.ofBits 0x4000000000000000 /- 2 -/) * q0 * q1 + (Binary64.ofBits 0x4000000000000000 /- 2 -/) * q2 * q3) + SH_BETA[1]! * SH_BETA[4]! * ((Binary64.ofBits 0x4000000000000000 /- 2 -/) * q0 * q2 - (Binary64.ofBits 0x4000000000000000 /- 2 -/) * q1 * q3))) + (SH_BETA[5]! * (SH_BETA[12]! - (Binary64.ofBits 0x4000000000000000 /- 2 -/) * q1 * q2) + SH_BETA[1]! * SH_BETA[4]! * SH_BETA[7]!) * (s.Pmut[550]! * (SH_BETA[5]! * (SH_BETA[12]! - (Binary64.ofBits 0x4000000000000000 /- 2 -/) * q1 * q2) + SH_BETA[1]! * SH_BETA[4]! * SH_BETA[7]!) - s.Pmut[118]! * (SH_BETA[5]! * (SH_BETA[12]! - (Binary64.ofBits 0x4000000000000000 /- 2 -/) * q1 * q2) + SH_BETA[1]! * SH_BETA[4]! * SH_BETA[7]!) + s.Pmut[142]! * (SH_BETA[6]! - SH_BETA[1]! * SH_BETA[4]! * (SH_BETA[12]! + (Binary64.ofBits 0x4000000000000000 /- 2 -/) * q1 * q2)) - s.Pmut[574]! * (SH_BETA[6]! - SH_BETA[1]! * SH_BETA[4]! * (SH_BETA[12]! + (Binary64.ofBits 0x4000000000000000 /- 2 -/) * q1 * q2)) + s.Pmut[22]! * (SH_BETA[5]! * SH_BETA[8]! - SH_BETA[1]! * SH_BETA[4]! * SH_BETA[9]!) + s.Pmut[46]! * (SH_BETA[5]! * SH_BETA[10]! - SH_BETA[1]! * SH_BETA[4]! * SH_BETA[11]!) + s.Pmut[70]! * (SH_BETA[5]! * SH_BETA[11]! + SH_BETA[1]! * SH_BETA[4]! * SH_BETA[10]!) - s.Pmut[94]! * (SH_BETA[5]! * SH_BETA[9]! + SH_BETA[1]! * SH_BETA[4]! * SH_BETA[8]!) + s.Pmut[166]! * (SH_BETA[5]! * ((Binary64.ofBits 0x4000000000000000 /- 2 -/) * q0 * q1 + (Binary64.ofBits 0x4000000000000000 /- 2 -/) * q2 * q3) + SH_BETA[1]! * SH_BETA[4]! * ((Binary64.ofBits 0x4000000000000000 /- 2 -/) * q0 * q2 - (Binary64.ofBits 0x4000000000000000 /- 2 -/) * q1 * q3))) + (SH_BETA[6]! - SH_BETA[1]! * SH_BETA[4]! * (SH_BETA[12]! + (Binary64.ofBits 0x4000000000000000 /- 2 -/) * q1 * q2)) * (s.Pmut[533]! * (SH_BETA[5]! * (SH_BETA[12]! - (Binary64.ofBits 0x4000000000000000 /- 2 -/) * q1 * q2) + SH_BETA[1]! * SH_BETA[4]! * SH_BETA[7]!) - s.Pmut[101]! * (SH_BETA[5]! * (SH_BETA[12]! - (Binary64.ofBits 0x4000000000000000 /- 2 -/) * q1 * q2) + SH_BETA[1]! * SH_BETA[4]! * SH_BETA[7]!) + s.Pmut[125]! * (SH_BETA[6]! - SH_BETA[1]! * SH_BETA[4]! * (SH_BETA[12]! + (Binary64.ofBits 0x4000000000000000 /- 2 -/) * q1 * q2)) - s.Pmut[557]! * (SH_BETA[6]! - SH_BETA[1]! * SH_BETA[4]! * (SH_BETA[12]! + (Binary64.ofBits 0x4000000000000000 /- 2 -/) * q1 * q2)) + s.Pmut[5]! * (SH_BETA[5]! * SH_BETA[8]! - SH_BETA[1]! * SH_BETA[4]! * SH_BETA[9]!) + s.Pmut[29]! * (SH_BETA[5]! * SH_BETA[10]! - SH_BETA[1]! * SH_BETA[4]! * SH_BETA[11]!) + s.Pmut[53]! * (SH_BETA[5]! * SH_BETA[11]! + SH_BETA[1]! * SH_BETA[4]! * SH_BETA[10]!) - s.Pmut[77]! * (SH_BETA[5]! * SH_BETA[9]! + SH_BETA[1]! * SH_BETA[4]! * SH_BETA[8]!) + s.Pmut[149]! * (SH_BETA[5]! * ((Binary64.ofBits 0x4000000000000000 /- 2 -/) * q0 * q1 + (Binary64.ofBits 0x4000000000000000 /- 2 -/) * q2 * q3) + SH_BETA[1]! * SH_BETA[4]! * ((Binary64.ofBits 0x4000000000000000 /- 2 -/) * q0 * q2 - (Binary64.ofBits 0x4000000000000000 /- 2 -/) * q1 * q3))) - (SH_BETA[6]! - SH_BETA[1]! * SH_BETA[4]! * (SH_BETA[12]! + (Binary64.ofBits 0x4000000000000000 /- 2 -/) * q1 * q2)) * (s.Pmut[551]! * (SH_BETA[5]! * (SH_BETA[12]! - (Binary64.ofBits 0x4000000000000000 /- 2 -/) * q1 * q2) + SH_BETA[1]! * SH_BETA[4]! * SH_BETA[7]!) - s.Pmut[119]! * (SH_BETA[5]! * (SH_BETA[12]! - (Binary64.ofBits 0x4000000000000000 /- 2 -/) * q1 * q2) + SH_BETA[1]! * SH_BETA[4]! * SH_BETA[7]!) + s.Pmut[143]! * (SH_BETA[6]! - SH_BETA[1]! * SH_BETA[4]! * (SH_BETA[12]! + (Binary64.ofBits 0x4000000000000000 /- 2 -/) * q1 * q2)) - s.Pmut[575]! * (SH_BETA[6]! - SH_BETA[1]! * SH_BETA[4]! * (SH_BETA[12]! + (Binary64.ofBits 0x4000000000000000 /- 2 -/) * q1 * q2)) + s.Pmut[23]! * (SH_BETA[5]! * SH_BETA[8]! - SH_BETA[1]! * SH_BETA[4]! * SH_BETA[9]!) + s.Pmut[47]! * (SH_BETA[5]! * SH_BETA[10]! - SH_BETA[1]! * SH_BETA[4]! * SH_BETA[11]!) + s.Pmut[71]! * (SH_BETA[5]! * SH_BETA[11]! + SH_BETA[1]! * SH_BETA[4]! * SH_BETA[10]!) - s.Pmut[95]! * (SH_BETA[5]! * SH_BETA[9]! + SH_BETA[1]! * SH_BETA[4]! * SH_BETA[8]!) + s.Pmut[167]! * (SH_BETA[5]! * ((Binary64.ofBits 0x4000000000000000 /- 2 -/) * q0 * q1 + (Binary64.ofBits 0x4000000000000000 /- 2 -/) * q2 * q3) + SH_BETA[1]! * SH_BETA[4]! * ((Binary64.ofBits 0x4000000000000000 /- 2 -/) * q0 * q2 - (Binary64.ofBits 0x4000000000000000 /- 2 -/) * q1 * q3))) + (SH_BETA[5]! * SH_BETA[8]! - SH_BETA[1]! * SH_BETA[4]! * SH_BETA[9]!) * (s.Pmut[528]! * (SH_BETA[5]! * (SH_BETA[12]! - (Binary64.ofBits 0x4000000000000000 /- 2 -/) * q1 * q2) + SH_BETA[1]! * SH_BETA[4]! * SH_BETA[7]!) - s.Pmut[96]! * (SH_BETA[5]! * (SH_BETA[12]! - (Binary64.ofBits 0x4000000000000000 /- 2 -/) * q1 * q2) + SH_BETA[1]! * SH_BETA[4]! * SH_BETA[7]!) + s.Pmut[120]! * (SH_BETA[6]! - SH_BETA[1]! * SH_BETA[4]! * (SH_BETA[12]! + (Binary64.ofBits 0x4000000000000000 /- 2 -/) * q1 * q2)) - s.Pmut[552]! * (SH_BETA[6]! - SH_BETA[1]! * SH_BETA[4]! * (SH_BETA[12]! + (Binary64.ofBits 0x4000000000000000 /- 2 -/) * q1 * q2)) + s.Pmut[0]! * (SH_BETA[5]! * SH_BETA[8]! - SH_BETA[1]! * SH_BETA[4]! * SH_BETA[9]!) + s.Pmut[24]! * (SH_BETA[5]! * SH_BETA[10]! - SH_BETA[1]! * SH_BETA[4]! * SH_BETA[11]!) + s.Pmut[48]! * (SH_BETA[5]! * SH_BETA[11]! + SH_BETA[1]! * SH_BETA[4]! * SH_BETA[10]!) - s.Pmut[72]! * (SH_BETA[5]! * SH_BETA[9]! + SH_BETA[1]! * SH_BETA[4]! * SH_BETA[8]!) + s.Pmut[144]! * (SH_BETA[5]! * ((Binary64.ofBits 0x4000000000000000 /- 2 -/) * q0 * q1 + (Binary64.ofBits 0x4000000000000000 /- 2 -/) * q2 * q3) + SH_BETA[1]! * SH_BETA[4]! * ((Binary64.ofBits 0x4000000000000000 /- 2 -/) * q0 * q2 - (Binary64.ofBits 0x4000000000000000 /- 2 -/) * q1 * q3))) + (SH_BETA[5]! * SH_BETA[10]! - SH_BETA[1]! * SH_BETA[4]! * SH_BETA[11]!) * (s.Pmut[529]! * (SH_BETA[5]! * (SH_BETA[12]! - (Binary64.ofBits 0x4000000000000000 /- 2 -/) * q1 * q2) + SH_BETA[1]! * SH_BETA[4]! * SH_BETA[7]!) - s.Pmut[97]! * (SH_BETA[5]! * (SH_BETA[12]! - (Binary64.ofBits 0x4000000000000000 /- 2 -/) * q1 * q2) + SH_BETA[1]! * SH_BETA[4]! * SH_BETA[7]!) + s.Pmut[121]! * (SH_BETA[6]! - SH_BETA[1]! * SH_BETA[4]! * (SH_BETA[12]! + (Binary64.ofBits 0x4000000000000000 /- 2 -/) * q1 * q2)) - s.Pmut[553]! * (SH_BETA[6]! - SH_BETA[1]! * SH_BETA[4]! * (SH_BETA[12]! + (Binary64.ofBits 0x4000000000000000 /- 2 -/) * q1 * q2)) + s.Pmut[1]! * (SH_BETA[5]! * SH_BETA[8]! - SH_BETA[1]! * SH_BETA[4]! * SH_BETA[9]!) + s.Pmut[25]! * (SH_BETA[5]! * SH_BETA[10]! - SH_BETA[1]! * SH_BETA[4]! * SH_BETA[11]!) + s.Pmut[49]! * (SH_BETA[5]! * SH_BETA[11]! + SH_BETA[1]! * SH_BETA[4]! * SH_BETA[10]!) - s.Pmut[73]! * (SH_BETA[5]! * SH_BETA[9]! + SH_BETA[1]! * SH_BETA[4]! * SH_BETA[8]!) + s.Pmut[145]! * (SH_BETA[5]! * ((Binary64.ofBits 0x4000000000000000 /- 2 -/) * q0 * q1 + (Binary64.ofBits 0x4000000000000000 /- 2 -/) * q2 * q3) + SH_BETA[1]! * SH_BETA[4]! * ((Binary64.ofBits 0x4000000000000000 /- 2 -/) * q0 * q2 - (Binary64.ofBits 0x4000000000000000 /- 2 -/) * q1 * q3))) + (SH_BETA[5]! * SH_BETA[11]! + SH_BETA[1]! * SH_BETA[4]! * SH_BETA[10]!) * (s.Pmut[530]! * (SH_BETA[5]! * (SH_BETA[12]! - (Binary64.ofBits 0x4000000000000000 /- 2 -/) * q1 * q2) + SH_BETA[1]! * SH_BETA[4]! * SH_BETA[7]!) - s.Pmut[98]! * (SH_BETA[5]! * (SH_BETA[12]! - (Binary64.ofBits 0x4000000000000000 /- 2 -/) * q1 * q2) + SH_BETA[1]! * SH_BETA[4]! * SH_BETA[7]!) + s.Pmut[122]! * (SH_BETA[6]! - SH_BETA[1]! * SH_BETA[4]! * (SH_BETA[12]! + (Binary64.ofBits 0x4000000000000000 /- 2 -/) * q1 * q2)) - s.Pmut[554]! * (SH_BETA[6]! - SH_BETA[1]! * SH_BETA[4]! * (SH_BETA[12]! + (Binary64.ofBits 0x4000000000000000 /- 2 -/) * q1 * q2)) + s.Pmut[2]! * (SH_BETA[5]! * SH_BETA[8]! - SH_BETA[1]! * SH_BETA[4]! * SH_BETA[9]!) + s.Pmut[26]! * (SH_BETA[5]! * SH_BETA[10]! - SH_BETA[1]! * SH_BETA[4]! * SH_BETA[11]!) + s.Pmut[50]! * (SH_BETA[5]! * SH_BETA[11]! + SH_BETA[1]! * SH_BETA[4]! * SH_BETA[10]!) - s.Pmut[74]! * (SH_BETA[5]! * SH_BETA[9]! + SH_BETA[1]! * SH_BETA[4]! * SH_BETA[8]!) + s.Pmut[146]! * (SH_BETA[5]! * ((Binary64.ofBits 0x4000000000000000 /- 2 -/) * q0 * q1 + (Binary64.ofBits 0x4000000000000000 /- 2 -/) * q2 * q3) + SH_BETA[1]! * SH_BETA[4]! * ((Binary64.ofBits 0x4000000000000000 /- 2 -/) * q0 * q2 - (Binary64.ofBits 0x4000000000000000 /- 2 -/) * q1 * q3))) - (SH_BETA[5]! * SH_BETA[9]! + SH_BETA[1]! * SH_BETA[4]! * SH_BETA[8]!) * (s.Pmut[531]! * (SH_BETA[5]! * (SH_BETA[12]! - (Binary64.ofBits 0x4000000000000000 /- 2 -/) * q1 * q2) + SH_BETA[1]! * SH_BETA[4]! * SH_BETA[7]!) - s.Pmut[99]! * (SH_BETA[5]! * (SH_BETA[12]! - (Binary64.ofBits 0x4000000000000000 /- 2 -/) * q1 * q2) + SH_BETA[1]! * SH_BETA[4]! * SH_BETA[7]!) + s.Pmut[123]! * (SH_BETA[6]! - SH_BETA[1]! * SH_BETA[4]! * (SH_BETA[12]! + (Binary64.ofBits 0x4000000000000000 /- 2 -/) * q1 * q2)) - s.Pmut[555]! * (SH_BETA[6]! - SH_BETA[1]! * SH_BETA[4]! * (SH_BETA[12]! + (Binary64.ofBits 0x4000000000000000 /- 2 -/) * q1 * q2)) + s.Pmut[3]! * (SH_BETA[5]! * SH_BETA[8]! - SH_BETA[1]! * SH_BETA[4]! * SH_BETA[9]!) + s.Pmut[27]! * (SH_BETA[5]! * SH_BETA[10]! - SH_BETA[1]! * SH_BETA[4]! * SH_BETA[11]!) + s.Pmut[51]! * (SH_BETA[5]! * SH_BETA[11]! + SH_BETA[1]! * SH_BETA[4]! * SH_BETA[10]!) - s.Pmut[75]! * (SH_BETA[5]! * SH_BETA[9]! + SH_BETA[1]! * SH_BETA[4]! * SH_BETA[8]!) + s.Pmut[147]! * (SH_BETA[5]! * ((Binary64.ofBits 0x4000000000000000 /- 2 -/) * q0 * q1 + (Binary64.ofBits 0x4000000000000000 /- 2 -/) * q2 * q3) + SH_BETA[1]! * SH_BETA[4]! * ((Binary64.ofBits 0x4000000000000000 /- 2 -/) * q0 * q2 - (Binary64.ofBits 0x4000000000000000 /- 2 -/) * q1 * q3))) + (SH_BETA[5]! * ((Binary64.ofBits 0x4000000000000000 /- 2 -/) * q0 * q1 + (Binary64.ofBits 0x4000000000000000 /- 2 -/) * q2 * q3) + SH_BETA[1]! * SH_BETA[4]! * ((Binary64.ofBits 0x4000000000000000 /- 2 -/) * q0 * q2 - (Binary64.ofBits 0x4000000000000000 /- 2 -/) * q1 * q3)) * (s.Pmut[534]! * (SH_BETA[5]! * (SH_BETA[12]! - (Binary64.ofBits 0x4000000000000000 /- 2 -/) * q1 * q2) + SH_BETA[1]! * SH_BETA[4]! * SH_BETA[7]!) - s.Pmut[102]! * (SH_BETA[5]! * (SH_BETA[12]! - (Binary64.ofBits 0x4000000000000000 /- 2 -/) * q1 * q2) + SH_BETA[1]! * SH_BETA[4]! * SH_BETA[7]!) + s.Pmut[126]! * (SH_BETA[6]! - SH_BETA[1]! * SH_BETA[4]! * (SH_BETA[12]! + (Binary64.ofBits 0x4000000000000000 /- 2 -/) * q1 * q2)) - s.Pmut[558]! * (SH_BETA[6]! - SH_BETA[1]! * SH_BETA[4]! * (SH_BETA[12]! + (Binary64.ofBits 0x4000000000000000 /- 2 -/) * q1 * q2)) + s.Pmut[6]! * (SH_BETA[5]! * SH_BETA[8]! - SH_BETA[1]! * SH_BETA[4]! * SH_BETA[9]!) + s.Pmut[30]! * (SH_BETA[5]! * SH_BETA[10]! - SH_BETA[1]! * SH_BETA[4]! * SH_BETA[11]!) + s.Pmut[54]! * (SH_BETA[5]! * SH_BETA[11]! + SH_BETA[1]! * SH_BETA[4]! * SH_BETA[10]!) - s.Pmut[78]! * (SH_BETA[5]! * SH_BETA[9]! + SH_BETA[1]! * SH_BETA[4]! * SH_BETA[8]!) + s.Pmut[150]! * (SH_BETA[5]! * ((Binary64.ofBits 0x4000000000000000 /- 2 -/) * q0 * q1 + (Binary64.ofBits 0x4000000000000000 /- 2 -/) * q2 * q3) + SH_BETA[1]! * SH_BETA[4]! * ((Binary64.ofBits 0x4000000000000000 /- 2 -/) * q0 * q2 - (Binary64.ofBits 0x4000000000000000 /- 2 -/) * q1 * q3))))
    if temp ≥ R_BETA then
      SK_BETA := SK_BETA.set! 0 ((Binary64.ofBits 0x3ff0000000000000 /- 1.0f -/) / temp)
      s := { s with faultStatus.bad_sideslip := false }
    else
      let (t'1, t'2) := CovarianceInit s w
      w := t'2
      s := t'1
      s := { s with faultStatus.bad_sideslip := true }
      return (s, w)
    SK_BETA := SK_BETA.set! 1 (SH_BETA[5]! * (SH_BETA[12]! - (Binary64.ofBits 0x4000000000000000 /- 2 -/) * q1 * q2) + SH_BETA[1]! * SH_BETA[4]! * SH_BETA[7]!)
    SK_BETA := SK_BETA.set! 2 (SH_BETA[6]! - SH_BETA[1]! * SH_BETA[4]! * (SH_BETA[12]! + (Binary64.ofBits 0x4000000000000000 /- 2 -/) * q1 * q2))
    SK_BETA := SK_BETA.set! 3 (SH_BETA[5]! * ((Binary64.ofBits 0x4000000000000000 /- 2 -/) * q0 * q1 + (Binary64.ofBits 0x4000000000000000 /- 2 -/) * q2 * q3) + SH_BETA[1]! * SH_BETA[4]! * ((Binary64.ofBits 0x4000000000000000 /- 2 -/) * q0 * q2 - (Binary64.ofBits 0x4000000000000000 /- 2 -/) * q1 * q3))
    SK_BETA := SK_BETA.set! 4 (SH_BETA[5]! * SH_BETA[10]! - SH_BETA[1]! * SH_BETA[4]! * SH_BETA[11]!)
    SK_BETA := SK_BETA.set! 5 (SH_BETA[5]! * SH_BETA[8]! - SH_BETA[1]! * SH_BETA[4]! * SH_BETA[9]!)
    SK_BETA := SK_BETA.set! 6 (SH_BETA[5]! * SH_BETA[11]! + SH_BETA[1]! * SH_BETA[4]! * SH_BETA[10]!)
    SK_BETA := SK_BETA.set! 7 (SH_BETA[5]! * SH_BETA[9]! + SH_BETA[1]! * SH_BETA[4]! * SH_BETA[8]!)
    let mut kalman_mask : UInt32 := Int32.toUInt32 (0 : Int32)
    if !s.airDataFusionWindOnly then
      kalman_mask := Int32.toUInt32 (((1 : Int32) <<< (10 : Int32)) - (1 : Int32))
    if !s.inhibitDelAngBiasStates && !s.airDataFusionWindOnly then
      kalman_mask := kalman_mask ||| Int32.toUInt32 (((1 : Int32) <<< (10 : Int32)) ||| ((1 : Int32) <<< (11 : Int32)) ||| ((1 : Int32) <<< (12 : Int32)))
    if !s.inhibitDelVelBiasStates && !s.airDataFusionWindOnly then
      for index' in [0:3] do
        let index : UInt8 := Nat.toUInt8 index'
        let stateIndex : UInt8 := Int8.toUInt8 (Int32.toInt8 (UInt32.toInt32 (UInt8.toUInt32 index) + (13 : Int32)))
        if !s.dvelBiasAxisInhibit[UInt8.toNat index]! then
          kalman_mask := kalman_mask ||| Int32.toUInt32 ((1 : Int32) <<< UInt32.toInt32 (UInt8.toUInt32 stateIndex))
    if !s.inhibitMagStates && !s.airDataFusionWindOnly then
      kalman_mask := kalman_mask ||| Int32.toUInt32 (((1 : Int32) <<< (16 : Int32)) ||| ((1 : Int32) <<< (17 : Int32)) ||| ((1 : Int32) <<< (18 : Int32)) ||| ((1 : Int32) <<< (19 : Int32)) ||| ((1 : Int32) <<< (20 : Int32)) ||| ((1 : Int32) <<< (21 : Int32)))
    if !s.inhibitWindStates && !s.treatWindStatesAsTruth then
      kalman_mask := kalman_mask ||| Int32.toUInt32 (((1 : Int32) <<< (22 : Int32)) ||| ((1 : Int32) <<< (23 : Int32)))
    for i'2' in [0:24] do
      let i'2 : Int32 := Nat.toInt32 i'2'
      let mut res : Binary64 := (Binary64.ofBits 0x0000000000000000 /- 0 -/)
      if kalman_mask &&& Int32.toUInt32 ((1 : Int32) <<< i'2) != (0 : UInt32) then
        res := SK_BETA[0]! * (s.Pmut[Int32.toNatClampNeg i'2 * 24]! * SK_BETA[5]! + s.Pmut[Int32.toNatClampNeg i'2 * 24 + 1]! * SK_BETA[4]! - s.Pmut[Int32.toNatClampNeg i'2 * 24 + 4]! * SK_BETA[1]! + s.Pmut[Int32.toNatClampNeg i'2 * 24 + 5]! * SK_BETA[2]! + s.Pmut[Int32.toNatClampNeg i'2 * 24 + 2]! * SK_BETA[6]! + s.Pmut[Int32.toNatClampNeg i'2 * 24 + 6]! * SK_BETA[3]! - s.Pmut[Int32.toNatClampNeg i'2 * 24 + 3]! * SK_BETA[7]! + s.Pmut[Int32.toNatClampNeg i'2 * 24 + 22]! * SK_BETA[1]! - s.Pmut[Int32.toNatClampNeg i'2 * 24 + 23]! * SK_BETA[2]!)
      w := { w with NavEKF_core_common'Kfusion := w.NavEKF_core_common'Kfusion.set! (Int32.toNatClampNeg i'2) res }
    s := { s with innovBeta := Estimator_lib.constrain_value_line_double (vel_rel_wind.y / vel_rel_wind.x) (Binary64.ofBits 0xbfe0000000000000 /- (double)-1/2 -/) (Binary64.ofBits 0x3fe0000000000000 /- (double)1/2 -/) (Int32.toUInt32 (357 : Int32)) }
    let t'3 : UInt32 := Int32.toUInt32 (0 : Int32)
    let t'4 : UInt32 := UInt8.toUInt32 s.stateIndexLim
    for i'3' in [0:((Int.ofNat t'4.toNat) - (Int.ofNat t'3.toNat) + 1).toNat] do  -- C++ loop bounded by a runtime value (--runtime-loops)
      let i'3 : UInt32 := t'3 + Nat.toUInt32 i'3'
      let t'5 : UInt32 := Int32.toUInt32 (0 : Int32)
      let t'6 : UInt32 := UInt8.toUInt32 s.stateIndexLim
      for j' in [0:((Int.ofNat t'6.toNat) - (Int.ofNat t'5.toNat) + 1).toNat] do  -- C++ loop bounded by a runtime value (--runtime-loops)
        let j : UInt32 := t'5 + Nat.toUInt32 j'
        let mut res'2 : Binary64 := (Binary64.ofBits 0x0000000000000000 /- 0 -/)
        res'2 := res'2 + (w.NavEKF_core_common'Kfusion[UInt32.toNat i'3]! * H_BETA[0]!) * s.Pmut[UInt32.toNat j]!
        res'2 := res'2 + (w.NavEKF_core_common'Kfusion[UInt32.toNat i'3]! * H_BETA[1]!) * s.Pmut[24 + UInt32.toNat j]!
        res'2 := res'2 + (w.NavEKF_core_common'Kfusion[UInt32.toNat i'3]! * H_BETA[2]!) * s.Pmut[48 + UInt32.toNat j]!
        res'2 := res'2 + (w.NavEKF_core_common'Kfusion[UInt32.toNat i'3]! * H_BETA[3]!) * s.Pmut[72 + UInt32.toNat j]!
        res'2 := res'2 + (w.NavEKF_core_common'Kfusion[UInt32.toNat i'3]! * H_BETA[4]!) * s.Pmut[96 + UInt32.toNat j]!
        res'2 := res'2 + (w.NavEKF_core_common'Kfusion[UInt32.toNat i'3]! * H_BETA[5]!) * s.Pmut[120 + UInt32.toNat j]!
        res'2 := res'2 + (w.NavEKF_core_common'Kfusion[UInt32.toNat i'3]! * H_BETA[6]!) * s.Pmut[144 + UInt32.toNat j]!
        res'2 := res'2 + (w.NavEKF_core_common'Kfusion[UInt32.toNat i'3]! * H_BETA[22]!) * s.Pmut[528 + UInt32.toNat j]!
        res'2 := res'2 + (w.NavEKF_core_common'Kfusion[UInt32.toNat i'3]! * H_BETA[23]!) * s.Pmut[552 + UInt32.toNat j]!
        w := { w with NavEKF_core_common'KHP := w.NavEKF_core_common'KHP.set! (UInt32.toNat i'3 * 24 + UInt32.toNat j) res'2 }
    let (t'7, _) := FinishFusion s w s.innovBeta true
    s := t'7
  return (s, w)

/-- C++ `void NavEKF3_core::SelectBetaDragFusion()`, `AP_NavEKF3/AP_NavEKF3_AirDataFusion.cpp:183-228`. -/
def SelectBetaDragFusion (s : State) (w : World) : State × World := Id.run do
  let mut s := s
  let mut w := w
  if s.magFusePerformed && decide (s.dtIMUavg < (Binary64.ofBits 0x3f747ae140000000 /- 0.005f -/)) && !s.sideSlipFusionDelayed then
    s := { s with sideSlipFusionDelayed := true }
    return (s, w)
  else
    s := { s with sideSlipFusionDelayed := false }
  let f_timeTrigger : Bool := (decide ((s.imuSampleTime_ms - s.prevBetaDragStep_ms) ≥ UInt16.toUInt32 w.EKF3.betaAvg_ms))
  let is_dead_reckoning : Bool := (decide ((s.imuSampleTime_ms - s.lastGpsPosPassTime_ms) > UInt16.toUInt32 w.EKF3.deadReckonDeclare_ms)) && (decide ((s.imuSampleTime_ms - s.lastVelPassTime_ms) > UInt16.toUInt32 w.EKF3.deadReckonDeclare_ms))
  let noYawSensor : Bool := !(use_compass s w) && !(using_noncompass_for_yaw s w)
  let f_required : Bool := (noYawSensor && (UInt32.toInt32 (UInt8.toUInt32 (AP_ParamT_unsigned_char_1.op_to_unsigned_char w.EKF3._betaMask)) &&& ((1 : Int32) <<< (1 : Int32))) != (0 : Int32)) || is_dead_reckoning
  let f_beta_feasible : Bool := (assume_zero_sideslip w && !s.inhibitWindStates)
  if f_beta_feasible && f_timeTrigger then
    if f_required || (UInt32.toInt32 (UInt8.toUInt32 (AP_ParamT_unsigned_char_1.op_to_unsigned_char w.EKF3._betaMask)) &&& ((1 : Int32) <<< (0 : Int32))) != (0 : Int32) then
      s := { s with airDataFusionWindOnly := false }
    else
      s := { s with airDataFusionWindOnly := true }
    let (t'1, t'2) := FuseSideslip s w
    w := t'2
    s := t'1
    s := { s with prevBetaDragStep_ms := s.imuSampleTime_ms }
  return (s, w)

/-- C++ `void NavEKF3_core::updateFilterStatus()`, `AP_NavEKF3/AP_NavEKF3_Control.cpp:786-834`. -/
def updateFilterStatus (s : State) (w : World) : State := Id.run do
  let mut s := s
  let mut status : UInt32 := (0 : UInt32)
  status := Int32.toUInt32 (0 : Int32)
  let doingBodyVelNav : Bool := (UInt32.toInt32 (NavEKF3_core.AidingMode.toInt s.PV_AidingMode) != UInt32.toInt32 (NavEKF3_core.AidingMode.toInt NavEKF3_core.AidingMode.AID_NONE)) && (decide (s.imuSampleTime_ms - s.bodyOdm.prevFuseTime_ms < Int32.toUInt32 (5000 : Int32)))
  let doingFlowNav : Bool := (UInt32.toInt32 (NavEKF3_core.AidingMode.toInt s.PV_AidingMode) != UInt32.toInt32 (NavEKF3_core.AidingMode.toInt NavEKF3_core.AidingMode.AID_NONE)) && s.flowDataValid
  let doingWindRelNav : Bool := (!s.tasTimeout && assume_zero_sideslip w) || !s.dragTimeout
  let doingNormalGpsNav : Bool := !s.posTimeout && (UInt32.toInt32 (NavEKF3_core.AidingMode.toInt s.PV_AidingMode) == UInt32.toInt32 (NavEKF3_core.AidingMode.toInt NavEKF3_core.AidingMode.AID_ABSOLUTE))
  let someVertRefData : Bool := (!s.velTimeout && (s.useGpsVertVel || s.extNav.useVel)) || !s.hgtTimeout
  let someHorizRefData : Bool := !(s.velTimeout && s.posTimeout && s.tasTimeout && s.dragTimeout) || doingFlowNav || doingBodyVelNav
  let filterHealthy : Bool := healthy s && s.tiltAlignComplete && (s.yawAlignComplete || (!(use_compass s w) && (UInt32.toInt32 (NavEKF3_core.AidingMode.toInt s.PV_AidingMode) != UInt32.toInt32 (NavEKF3_core.AidingMode.toInt NavEKF3_core.AidingMode.AID_ABSOLUTE))))
  let hgtNotAccurate : Bool := (AP_NavEKF_Source.getPosZSource w.EKF3.sources s.core_index == AP_NavEKF_Source.SourceZ.GPS) && !s.validOrigin
  status := (status &&& ~~~((1 : UInt32) <<< 0)) ||| (if !(QuaternionT_double.is_nan ({ q1 := s.statesArray[0]!, q2 := s.statesArray[1]!, q3 := s.statesArray[2]!, q4 := s.statesArray[3]! } : QuaternionT_double.State)) && filterHealthy then (1 : UInt32) <<< 0 else 0)
  status := (status &&& ~~~((1 : UInt32) <<< 1)) ||| (if someHorizRefData && filterHealthy then (1 : UInt32) <<< 1 else 0)
  status := (status &&& ~~~((1 : UInt32) <<< 2)) ||| (if someVertRefData && filterHealthy then (1 : UInt32) <<< 2 else 0)
  let optflow_gnd_offset : Bool := s.gndOffsetValid
  status := (status &&& ~~~((1 : UInt32) <<< 3)) ||| (if ((doingFlowNav && optflow_gnd_offset) || doingWindRelNav || doingNormalGpsNav || doingBodyVelNav) && filterHealthy then (1 : UInt32) <<< 3 else 0)
  status := (status &&& ~~~((1 : UInt32) <<< 4)) ||| (if doingNormalGpsNav && filterHealthy then (1 : UInt32) <<< 4 else 0)
  status := (status &&& ~~~((1 : UInt32) <<< 5)) ||| (if !s.hgtTimeout && filterHealthy && !hgtNotAccurate then (1 : UInt32) <<< 5 else 0)
  status := (status &&& ~~~((1 : UInt32) <<< 6)) ||| (if s.gndOffsetValid && filterHealthy then (1 : UInt32) <<< 6 else 0)
  status := (status &&& ~~~((1 : UInt32) <<< 7)) ||| (if (UInt32.toInt32 (NavEKF3_core.AidingMode.toInt s.PV_AidingMode) == UInt32.toInt32 (NavEKF3_core.AidingMode.toInt NavEKF3_core.AidingMode.AID_NONE)) && filterHealthy then (1 : UInt32) <<< 7 else 0)
  status := (status &&& ~~~((1 : UInt32) <<< 8)) ||| (if (status >>> 3 &&& 1 != 0) then (1 : UInt32) <<< 8 else 0)
  status := (status &&& ~~~((1 : UInt32) <<< 9)) ||| (if (status >>> 4 &&& 1 != 0) then (1 : UInt32) <<< 9 else 0)
  status := (status &&& ~~~((1 : UInt32) <<< 10)) ||| (if s.takeOffDetected then (1 : UInt32) <<< 10 else 0)
  status := (status &&& ~~~((1 : UInt32) <<< 11)) ||| (if AP_DAL.get_takeoff_expected w.heap'AP_DAL[(WPtr.index w.AP_DAL'_singleton)]! then (1 : UInt32) <<< 11 else 0)
  status := (status &&& ~~~((1 : UInt32) <<< 12)) ||| (if AP_DAL.get_touchdown_expected w.heap'AP_DAL[(WPtr.index w.AP_DAL'_singleton)]! then (1 : UInt32) <<< 12 else 0)
  status := (status &&& ~~~((1 : UInt32) <<< 13)) ||| (if (decide ((s.imuSampleTime_ms - s.lastGpsPosPassTime_ms) < Int32.toUInt32 (4000 : Int32))) && (UInt32.toInt32 (NavEKF3_core.AidingMode.toInt s.PV_AidingMode) == UInt32.toInt32 (NavEKF3_core.AidingMode.toInt NavEKF3_core.AidingMode.AID_ABSOLUTE)) then (1 : UInt32) <<< 13 else 0)
  status := (status &&& ~~~((1 : UInt32) <<< 14)) ||| (if !s.gpsAccuracyGood && (UInt32.toInt32 (NavEKF3_core.AidingMode.toInt s.PV_AidingMode) == UInt32.toInt32 (NavEKF3_core.AidingMode.toInt NavEKF3_core.AidingMode.AID_ABSOLUTE)) && (AP_NavEKF_Source.getPosXYSource w.EKF3.sources s.core_index == AP_NavEKF_Source.SourceXY.GPS) then (1 : UInt32) <<< 14 else 0)
  status := (status &&& ~~~((1 : UInt32) <<< 15)) ||| (if s.gpsGoodToAlign then (1 : UInt32) <<< 15 else 0)
  status := (status &&& ~~~((1 : UInt32) <<< 17)) ||| (if s.tas.lastFailTime_ms != Int32.toUInt32 (0 : Int32) && decide ((s.imuSampleTime_ms - s.tas.lastFailTime_ms) < Int32.toUInt32 (1000 : Int32)) && decide ((s.imuSampleTime_ms - s.tas.lastPassTime_ms) > Int32.toUInt32 (3000 : Int32)) then (1 : UInt32) <<< 17 else 0)
  status := (status &&& ~~~((1 : UInt32) <<< 16)) ||| (if (status >>> 16 &&& 1 != 0) || healthy s then (1 : UInt32) <<< 16 else 0)
  status := (status &&& ~~~((1 : UInt32) <<< 18)) ||| (if (UInt32.toInt32 (NavEKF3_core.AidingMode.toInt s.PV_AidingMode) != UInt32.toInt32 (NavEKF3_core.AidingMode.toInt NavEKF3_core.AidingMode.AID_NONE)) && doingWindRelNav && !((doingFlowNav && s.gndOffsetValid) || doingNormalGpsNav || doingBodyVelNav) then (1 : UInt32) <<< 18 else 0)
  s := { s with filterStatus := status }
  return s

/-- C++ `void NavEKF3_core::moveEKFOrigin()`, `AP_NavEKF3/AP_NavEKF3_core.cpp:2241-2262`. -/
def moveEKFOrigin (s : State) (w : World) : State := Id.run do
  let mut s := s
  if !w.EKF3.common_origin_valid || !(s.filterStatus >>> 13 &&& 1 != 0) then
    return s
  let mut loc : Location.State := s.EKF_origin
  loc := Location.offset_double2 loc s.statesArray[7]! s.statesArray[8]!
  let diffNE : Vector2p.State := Location.get_distance_NE_ftype loc s.EKF_origin
  s := { s with EKF_origin := loc }
  let (t'1, _) := Vector2p.op_add_assign ({ x := s.statesArray[7]!, y := s.statesArray[8]! } : Vector2p.State) diffNE
  s := { s with statesArray := ((s.statesArray.set! 7 t'1.x).set! 8 t'1.y) }
  let (t'3, _) := Vector2p.op_add_assign ({ x := s.outputDataNew.position.x, y := s.outputDataNew.position.y } : Vector2p.State) diffNE
  s := { s with outputDataNew.position.x := t'3.x, outputDataNew.position.y := t'3.y }
  let (t'5, _) := Vector2p.op_add_assign ({ x := s.outputDataDelayed.position.x, y := s.outputDataDelayed.position.y } : Vector2p.State) diffNE
  s := { s with outputDataDelayed.position.x := t'5.x, outputDataDelayed.position.y := t'5.y }
  let t'7 : UInt32 := Int32.toUInt32 (0 : Int32)
  let t'8 : UInt32 := UInt8.toUInt32 s.imu_buffer_length
  for index' in [0:((Int.ofNat t'8.toNat) - (Int.ofNat t'7.toNat)).toNat] do  -- C++ loop bounded by a runtime value (--runtime-loops)
    let index : UInt32 := t'7 + Nat.toUInt32 index'
    let (t'9, _) := Vector2p.op_add_assign ({ x := s.storedOutput.buffer[UInt8.toNat (UInt32.toUInt8 index)]!.position.x, y := s.storedOutput.buffer[UInt8.toNat (UInt32.toUInt8 index)]!.position.y } : Vector2p.State) diffNE
    s := { s with storedOutput.buffer := s.storedOutput.buffer.set! (UInt8.toNat (UInt32.toUInt8 index)) ({ s.storedOutput.buffer[UInt8.toNat (UInt32.toUInt8 index)]! with position.x := t'9.x, position.y := t'9.y }) }
  return s

/-- C++ `void NavEKF3_core::checkUpdateEarthField()`, `AP_NavEKF3/AP_NavEKF3_Measurements.cpp:1556-1563`. -/
def checkUpdateEarthField (s : State) : State := Id.run do
  let mut s := s
  if s.have_table_earth_field && (s.filterStatus >>> 13 &&& 1 != 0) then
    let mut loc : Location.State := s.EKF_origin
    loc := Location.offset_double2 loc s.statesArray[7]! s.statesArray[8]!
    s := getEarthFieldTable s loc
  return s

end NavEKF3_core

namespace NavEKF3_core

/-- C++ `void NavEKF3_core::calcOutputStates()`, `AP_NavEKF3/AP_NavEKF3_core.cpp:807-987`. -/
def calcOutputStates (s : State) (w : World) : State × World := Id.run do
  let mut s := s
  let mut w := w
  let mut delAngNewCorrected : Vector3p.State := s.imuDataNew.delAng
  let mut delVelNewCorrected : Vector3p.State := s.imuDataNew.delVel
  delAngNewCorrected := correctDeltaAngle s delAngNewCorrected s.imuDataNew.delAngDT s.imuDataNew.gyro_index
  delVelNewCorrected := correctDeltaVelocity s delVelNewCorrected s.imuDataNew.delVelDT s.imuDataNew.accel_index
  let delAng : Vector3p.State := Vector3p.op_add delAngNewCorrected s.delAngCorrection
  let mut deltaQuat : QuaternionT_double.State := QuaternionT_double.init_void
  deltaQuat := QuaternionT_double.from_axis_angle_Vector3p deltaQuat delAng
  let (t'1, _) := QuaternionT_double.op_mul_assign s.outputDataNew.quat deltaQuat
  s := { s with outputDataNew.quat := t'1 }
  s := { s with outputDataNew.quat := QuaternionT_double.normalize s.outputDataNew.quat }
  let mut Tbn_temp : Matrix3_double.State := Matrix3_double.init_void
  Tbn_temp := QuaternionT_double.rotation_matrix_Matrix3_double s.outputDataNew.quat Tbn_temp
  let mut delVelNav : Vector3p.State := Matrix3_double.op_mul_Vector3p Tbn_temp delVelNewCorrected
  delVelNav := { delVelNav with z := delVelNav.z + (Binary64.ofBits 0x40239d0140000000 /- (double)5141509/524288 -/) * s.imuDataNew.delVelDT }
  let lastVelocity : Vector3p.State := s.outputDataNew.velocity
  let (t'3, _) := Vector3p.op_add_assign s.outputDataNew.velocity delVelNav
  s := { s with outputDataNew.velocity := t'3 }
  let CompFiltOmega : Binary64 := (Binary64.ofBits 0x401921fb60000000 /- (double)13176795/2097152 -/) * Estimator_lib.constrain_value_line_double (AP_ParamT_float_4.op_to_double w.EKF3._hrt_filt_freq) (Binary64.ofBits 0x3fb99999a0000000 /- (double)13421773/134217728 -/) (Binary64.ofBits 0x403e000000000000 /- (double)30 -/) (Int32.toUInt32 (849 : Int32))
  let omega2 : Binary64 := CompFiltOmega * CompFiltOmega
  let pos_err : Binary64 := Estimator_lib.constrain_value_line_double (s.outputDataNew.position.z - s.vertCompFiltState.pos) (Binary64.ofBits 0xc0f86a0000000000 /- (double)-100000 -/) (Binary64.ofBits 0x40f86a0000000000 /- (double)100000 -/) (Int32.toUInt32 (851 : Int32))
  let integ1_input : Binary64 := pos_err * omega2 * CompFiltOmega * s.imuDataNew.delVelDT
  s := { s with vertCompFiltState.acc := s.vertCompFiltState.acc + integ1_input }
  let integ2_input : Binary64 := delVelNav.z + (s.vertCompFiltState.acc + pos_err * omega2 * (Binary64.ofBits 0x4008000000000000 /- 3.0f -/)) * s.imuDataNew.delVelDT
  s := { s with vertCompFiltState.vel := s.vertCompFiltState.vel + integ2_input }
  let integ3_input : Binary64 := (s.vertCompFiltState.vel + pos_err * CompFiltOmega * (Binary64.ofBits 0x4008000000000000 /- 3.0f -/)) * s.imuDataNew.delVelDT
  s := { s with vertCompFiltState.pos := s.vertCompFiltState.pos + integ3_input }
  let (t'5, _) := Vector3p.op_add_assign s.outputDataNew.position (Vector3p.op_mul_double (Vector3p.op_add s.outputDataNew.velocity lastVelocity) (s.imuDataNew.delVelDT * (Binary64.ofBits 0x3fe0000000000000 /- 0.5f -/)))
  s := { s with outputDataNew.position := t'5 }
  if !(Vector3p.is_zero s.accelPosOffset) then
    let t'7 := s.gyro_index_active
    let angRate : Vector3p.State := Vector3f.todouble w.heap'AP_DAL[(WPtr.index w.AP_DAL'_singleton)]!._ins.gyro_filtered[UInt8.toNat t'7]!
    let velBodyRelIMU : Vector3p.State := Vector3p.op_mod angRate (Vector3p.op_sub_void s.accelPosOffset)
    s := { s with velOffsetNED := Matrix3_double.op_mul_Vector3p Tbn_temp velBodyRelIMU }
    s := { s with posOffsetNED := Matrix3_double.op_mul_Vector3p Tbn_temp (Vector3p.op_sub_void s.accelPosOffset) }
  else
    s := { s with velOffsetNED := Vector3p.zero s.velOffsetNED }
    s := { s with posOffsetNED := Vector3p.zero s.posOffsetNED }
  if !s.inFlight && !(AP_DAL.get_takeoff_expected w.heap'AP_DAL[(WPtr.index w.AP_DAL'_singleton)]!) && assume_zero_sideslip w then
    let launchDelVel : Binary64 := s.imuDataNew.delVel.x + (Binary64.ofBits 0x40239d0140000000 /- (double)5141509/524288 -/) * s.imuDataNew.delVelDT * Tbn_temp.c.x
    if launchDelVel > (Binary64.ofBits 0x40239d0140000000 /- (double)5141509/524288 -/) * s.imuDataNew.delVelDT then
      w := AP_DAL.set_takeoff_expected w
  if s.runUpdates then
    s := { s with storedOutput.buffer := s.storedOutput.buffer.set! (UInt8.toNat (UInt32.toUInt8 (UInt8.toUInt32 (EKF_IMU_buffer_t_NavEKF3_core_imu_elements.get_youngest_index_void s.storedIMU)))) s.outputDataNew }
    s := { s with outputDataDelayed := EKF_IMU_buffer_t_NavEKF3_core_output_elements.op_index s.storedOutput (UInt8.toUInt32 (EKF_IMU_buffer_t_NavEKF3_core_imu_elements.get_oldest_index_void s.storedIMU)) }
    let mut quatErr : QuaternionT_double.State := QuaternionT_double.op_div ({ q1 := s.statesArray[0]!, q2 := s.statesArray[1]!, q3 := s.statesArray[2]!, q4 := s.statesArray[3]! } : QuaternionT_double.State) s.outputDataDelayed.quat
    quatErr := QuaternionT_double.normalize quatErr
    let mut deltaAngErr : Vector3p.State := Vector3p.init_void
    let mut scaler : Binary64 := (Binary64.ofBits 0x0000000000000000 /- 0.0 -/)  -- uninitialized in C++; assigned before every read
    if quatErr.q1 ≥ (Binary64.ofBits 0x0000000000000000 /- 0.0f -/) then
      scaler := (Binary64.ofBits 0x4000000000000000 /- 2.0f -/)
    else
      scaler := (Binary64.ofBits 0xc000000000000000 /- -2.0f -/)
    deltaAngErr := { deltaAngErr with x := scaler * quatErr.q2 }
    deltaAngErr := { deltaAngErr with y := scaler * quatErr.q3 }
    deltaAngErr := { deltaAngErr with z := scaler * quatErr.q4 }
    let mut timeDelay : Binary64 := (Binary64.ofBits 0x3f50624de0000000 /- 1e-3f -/) * UInt32.toBinary64 (s.imuDataNew.time_ms - s.imuDataDelayed.time_ms)
    timeDelay := Estimator_lib.MAX_double2 timeDelay s.dtIMUavg
    let errorGain : Binary64 := (Binary64.ofBits 0x3fe0000000000000 /- 0.5f -/) / timeDelay
    s := { s with delAngCorrection := Vector3p.op_mul_double (Vector3p.op_mul_double deltaAngErr errorGain) s.dtIMUavg }
    let velErr : Vector3p.State := (Vector3p.op_sub_Vector3p ({ x := s.statesArray[4]!, y := s.statesArray[5]!, z := s.statesArray[6]! } : Vector3p.State) s.outputDataDelayed.velocity)
    let posErr : Vector3p.State := (Vector3p.op_sub_Vector3p ({ x := s.statesArray[7]!, y := s.statesArray[8]!, z := s.statesArray[9]! } : Vector3p.State) s.outputDataDelayed.position)
    if s.badIMUdata then
      s := { s with badImuVelErrIntegral := s.badImuVelErrIntegral + (s.statesArray[6]! - s.outputDataNew.velocity.z) }
    else
      s := { s with badImuVelErrIntegral := s.velErrintegral.z }
    s := { s with outputTrackError.x := Vector3p.length deltaAngErr }
    s := { s with outputTrackError.y := Vector3p.length velErr }
    s := { s with outputTrackError.z := Vector3p.length posErr }
    let tauPosVel : Binary64 := Estimator_lib.constrain_value_line_double ((Binary64.ofBits 0x3f847ae140000000 /- (double)5368709/536870912 -/) * Int8.toBinary64 (AP_ParamT_signed_char_1.op_to_signed_char w.EKF3._tauVelPosOutput)) (Binary64.ofBits 0x3fb99999a0000000 /- (double)13421773/134217728 -/) (Binary64.ofBits 0x3fe0000000000000 /- (double)1/2 -/) (Int32.toUInt32 (946 : Int32))
    let velPosGain : Binary64 := s.dtEkfAvg / Estimator_lib.constrain_value_line_double tauPosVel s.dtEkfAvg (Binary64.ofBits 0x4024000000000000 /- (double)10 -/) (Int32.toUInt32 (949 : Int32))
    let (t'8, _) := Vector3p.op_add_assign s.posErrintegral posErr
    s := { s with posErrintegral := t'8 }
    let (t'10, _) := Vector3p.op_add_assign s.velErrintegral velErr
    s := { s with velErrintegral := t'10 }
    let posCorrection : Vector3p.State := Vector3p.op_add (Vector3p.op_mul_double posErr velPosGain) (Vector3p.op_mul_double (Vector3p.op_mul_double s.posErrintegral (Estimator_lib.sq_double velPosGain)) (Binary64.ofBits 0x3fb99999a0000000 /- 0.1F -/))
    let mut velCorrection : Vector3p.State := Vector3p.init_void
    velCorrection := { velCorrection with x := velErr.x * velPosGain + s.velErrintegral.x * Estimator_lib.sq_double velPosGain * (Binary64.ofBits 0x3fb99999a0000000 /- 0.1F -/) }
    velCorrection := { velCorrection with y := velErr.y * velPosGain + s.velErrintegral.y * Estimator_lib.sq_double velPosGain * (Binary64.ofBits 0x3fb99999a0000000 /- 0.1F -/) }
    if s.badIMUdata then
      velCorrection := { velCorrection with z := velErr.z * velPosGain + s.badImuVelErrIntegral * Estimator_lib.sq_double velPosGain * (Binary64.ofBits 0x3fb1eb8520000000 /- 0.07F -/) }
      s := { s with velErrintegral.z := s.badImuVelErrIntegral }
    else
      velCorrection := { velCorrection with z := velErr.z * velPosGain + s.velErrintegral.z * Estimator_lib.sq_double velPosGain * (Binary64.ofBits 0x3fb99999a0000000 /- 0.1F -/) }
    let mut outputStates : NavEKF3_core.output_elements := {}
    let t'12 : UInt32 := Int32.toUInt32 (0 : Int32)
    let t'13 : UInt32 := UInt8.toUInt32 s.imu_buffer_length
    for index' in [0:((Int.ofNat t'13.toNat) - (Int.ofNat t'12.toNat)).toNat] do  -- C++ loop bounded by a runtime value (--runtime-loops)
      let index : UInt32 := t'12 + Nat.toUInt32 index'
      outputStates := EKF_IMU_buffer_t_NavEKF3_core_output_elements.op_index s.storedOutput index
      let (t'14, _) := Vector3p.op_add_assign outputStates.velocity velCorrection
      outputStates := { outputStates with velocity := t'14 }
      let (t'16, _) := Vector3p.op_add_assign outputStates.position posCorrection
      outputStates := { outputStates with position := t'16 }
      s := { s with storedOutput.buffer := s.storedOutput.buffer.set! (UInt8.toNat (UInt32.toUInt8 index)) outputStates }
    s := { s with outputDataNew := EKF_IMU_buffer_t_NavEKF3_core_output_elements.op_index s.storedOutput (UInt8.toUInt32 (EKF_IMU_buffer_t_NavEKF3_core_imu_elements.get_youngest_index_void s.storedIMU)) }
  return (s, w)

/-- C++ `void NavEKF3_core::UpdateFilter(bool predict)`, `AP_NavEKF3/AP_NavEKF3_core.cpp:613-712`. -/
def UpdateFilter (s : State) (w : World) (o : Outputs) (predict : Bool) : State × World × Outputs := Id.run do
  let mut s := s
  let mut w := w
  let mut o := o
  if !s.statesInitialised then
    return (s, w, o)
  w := fill_scratch_variables w
  let (t'1, t'2) := update_sensor_selection s w o
  s := t'1
  o := t'2
  let (t'3, t'4, t'5) := controlFilterModes s w o
  w := t'4
  s := t'3
  o := t'5
  s := readIMUData s w predict
  if s.runUpdates then
    s := UpdateStrapdownEquationsNED s w
    let (t'6, t'7, _) := CovariancePrediction s w false {}
    w := t'7
    s := t'6
    w := runYawEstimatorPrediction s w
    let (t'8, t'9, t'10) := SelectMagFusion s w o
    w := t'9
    s := t'8
    o := t'10
    let (t'11, t'12, t'13) := SelectVelPosFusion s w o
    w := t'12
    s := t'11
    o := t'13
    let (t'14, t'15, t'16) := runYawEstimatorCorrection s w o
    w := t'15
    s := t'14
    o := t'16
    let (t'17, t'18, t'19) := SelectBodyOdomFusion s w o
    w := t'18
    s := t'17
    o := t'19
    let (t'20, t'21) := SelectTasFusion s w
    w := t'21
    s := t'20
    let (t'22, t'23) := SelectBetaDragFusion s w
    w := t'23
    s := t'22
    s := updateFilterStatus s w
    if s.imuSampleTime_ms - s.last_oneHz_ms ≥ Int32.toUInt32 (1000 : Int32) then
      s := { s with last_oneHz_ms := s.imuSampleTime_ms }
      s := moveEKFOrigin s w
      s := checkUpdateEarthField s
  let (t'24, t'25) := calcOutputStates s w
  w := t'25
  s := t'24
  if s.filterStatus != Int32.toUInt32 (0 : Int32) then
    s := { s with last_filter_ok_ms := AP_DAL.millis w.heap'AP_DAL[(WPtr.index w.AP_DAL'_singleton)]! }
  if s.filterStatus == Int32.toUInt32 (0 : Int32) && s.last_filter_ok_ms != Int32.toUInt32 (0 : Int32) && decide (AP_DAL.millis w.heap'AP_DAL[(WPtr.index w.AP_DAL'_singleton)]! - s.last_filter_ok_ms > Int32.toUInt32 (5000 : Int32)) && !(AP_DAL.get_armed w.heap'AP_DAL[(WPtr.index w.AP_DAL'_singleton)]!) then
    o := o.push (Output.send_text (4 : UInt32) "EKF3 IMU%u forced reset" #[Sum.inl (UInt32.toUInt64 (UInt8.toUInt32 s.imu_index))])
    s := { s with last_filter_ok_ms := Int32.toUInt32 (0 : Int32) }
    s := { s with statesInitialised := false }
    let (t'26, t'27, t'28, _) := InitialiseFilterBootstrap s w o
    w := t'27
    s := t'26
    o := t'28
  return (s, w, o)

end NavEKF3_core

namespace NavEKF3

/-- C++ `void NavEKF3::UpdateFilter()`, `AP_NavEKF3/AP_NavEKF3.cpp:938-1049`. -/
def UpdateFilter (s : State) (w : World) (o : Outputs) : State × World × Outputs := Id.run do
  let mut s := s
  let mut w := w
  let mut o := o
  let t'1 := w.heap'AP_DAL[(WPtr.index w.AP_DAL'_singleton)]!  -- the object out of its slot for the call (--swap-out)
  w := { w with heap'AP_DAL := w.heap'AP_DAL.set! (WPtr.index w.AP_DAL'_singleton) default }
  let (t'2, t'3) := AP_DAL.start_frame t'1 w w.heap'AP_DAL'inp AP_DAL.FrameType.UpdateFilterEKF3
  w := t'3
  w := { w with heap'AP_DAL := w.heap'AP_DAL.set! (WPtr.index w.AP_DAL'_singleton) t'2 }
  if !(s.core != WPtr.null) then
    return (s, w, o)
  s := { s with imuSampleTime_us := AP_DAL.micros64 w.heap'AP_DAL[(WPtr.index w.AP_DAL'_singleton)]! }
  let t'4 : UInt8 := Int8.toUInt8 (Int32.toInt8 (0 : Int32))
  let t'5 : Int32 := UInt32.toInt32 (UInt8.toUInt32 s.num_cores)
  for i' in [0:(t'5.toInt - (Int.ofNat t'4.toNat)).toNat] do  -- C++ loop bounded by a runtime value (--runtime-loops)
    let i : UInt8 := t'4 + Nat.toUInt8 i'
    let mut allow_state_prediction : Bool := true
    let mut t'9 := decide (UInt32.toInt32 (UInt8.toUInt32 (NavEKF3_core.getFramesSincePredict w.heap'NavEKF3_core[((WPtr.index s.core) + (UInt8.toNat i))]!)) < (UInt32.toInt32 (UInt8.toUInt32 s._framesPerPrediction) + (3 : Int32)))
    if t'9 then
      let t'6 := w.heap'AP_DAL[(WPtr.index w.AP_DAL'_singleton)]!  -- the object out of its slot for the call (--swap-out)
      w := { w with heap'AP_DAL := w.heap'AP_DAL.set! (WPtr.index w.AP_DAL'_singleton) default }
      let (t'7, t'8) := AP_DAL.ekf_low_time_remaining t'6 w AP_DAL.EKFType.EKF3 i
      w := { w with heap'AP_DAL := w.heap'AP_DAL.set! (WPtr.index w.AP_DAL'_singleton) t'7 }
      t'9 := t'8
    if t'9 then
      allow_state_prediction := false
    w := { w with EKF3 := s }  -- this object's state into the World: the call reaches it
    let t'10 := w.heap'NavEKF3_core[((WPtr.index s.core) + (UInt8.toNat i))]!  -- the object out of its slot for the call (--swap-out)
    w := { w with heap'NavEKF3_core := w.heap'NavEKF3_core.set! ((WPtr.index s.core) + (UInt8.toNat i)) default }
    let (t'11, t'12, t'13) := NavEKF3_core.UpdateFilter t'10 w o allow_state_prediction
    w := t'12
    w := { w with heap'NavEKF3_core := w.heap'NavEKF3_core.set! ((WPtr.index s.core) + (UInt8.toNat i)) t'11 }
    o := t'13
    s := w.EKF3  -- this object's state as the call left it
  if !s.runCoreSelection then
    pure ()  -- C++ `static uint64_t lastUnhealthyTime_us = 0`: a World field (a static local)
    if !(NavEKF3_core.healthy w.heap'NavEKF3_core[((WPtr.index s.core) + (UInt8.toNat s.primary))]!) || w.NavEKF3_UpdateFilter'lastUnhealthyTime_us == Int64.toUInt64 (Int32.toInt64 (0 : Int32)) then
      w := { w with NavEKF3_UpdateFilter'lastUnhealthyTime_us := s.imuSampleTime_us }
    s := { s with runCoreSelection := decide (UInt64.toBinary32 (s.imuSampleTime_us - w.NavEKF3_UpdateFilter'lastUnhealthyTime_us) > (Binary32.ofBits 0x4b189680 /- 1E7 -/)) }
  let user_primary : UInt8 := Int8.toUInt8 (Int32.toInt8 (if UInt32.toInt32 (UInt8.toUInt32 (AP_ParamT_unsigned_char_1.op_to_unsigned_char s._primary_core)) < UInt32.toInt32 (UInt8.toUInt32 s.num_cores) then UInt32.toInt32 (UInt8.toUInt32 (AP_ParamT_unsigned_char_1.op_to_unsigned_char s._primary_core)) else (0 : Int32)))
  let mut lane_switching_enabled : Bool := true
  if option_is_enabled s NavEKF3.Option.ManualLaneSwitch then
    lane_switching_enabled := false
    if UInt32.toInt32 (UInt8.toUInt32 s.primary) != UInt32.toInt32 (UInt8.toUInt32 user_primary) then
      let (t'14, t'15) := switchLane s w o user_primary
      s := t'14
      o := t'15
  let armed : Bool := AP_DAL.get_armed w.heap'AP_DAL[(WPtr.index w.AP_DAL'_singleton)]!
  if s.runCoreSelection && armed && lane_switching_enabled then
    let (t'16, t'17, t'18) := updateCoreErrorScores s w
    w := t'17
    s := t'16
    let primaryErrorScore : Binary32 := t'18
    s := updateCoreRelativeErrors s
    let mut betterCore : Bool := false
    let mut altCoreAvailable : Bool := false
    let mut newPrimaryIndex : UInt8 := s.primary
    let t'19 : UInt8 := Int8.toUInt8 (Int32.toInt8 (0 : Int32))
    let t'20 : Int32 := UInt32.toInt32 (UInt8.toUInt32 s.num_cores)
    for coreIndex' in [0:(t'20.toInt - (Int.ofNat t'19.toNat)).toNat] do  -- C++ loop bounded by a runtime value (--runtime-loops)
      let coreIndex : UInt8 := t'19 + Nat.toUInt8 coreIndex'
      if UInt32.toInt32 (UInt8.toUInt32 coreIndex) != UInt32.toInt32 (UInt8.toUInt32 s.primary) then
        let altCoreError : Binary32 := s.coreRelativeErrors[UInt8.toNat coreIndex]!
        altCoreAvailable := coreBetterScore s w coreIndex newPrimaryIndex && decide (UInt64.toBinary32 (s.imuSampleTime_us - s.coreLastTimePrimary_us[UInt8.toNat coreIndex]!) > (Binary32.ofBits 0x4b189680 /- 1E7 -/))
        if altCoreAvailable then
          betterCore := decide (altCoreError ≤ -(Binary32.ofBits 0x3f000000 /- (float)1/2 -/))
          betterCore := (if betterCore then (1 : Int32) else (0 : Int32)) ||| (if NavEKF3_core.have_aligned_yaw w.heap'NavEKF3_core[((WPtr.index s.core) + (UInt8.toNat coreIndex))]! && !(NavEKF3_core.have_aligned_yaw w.heap'NavEKF3_core[((WPtr.index s.core) + (UInt8.toNat s.primary))]!) then (1 : Int32) else (0 : Int32)) != (0 : Int32)
          newPrimaryIndex := coreIndex
    altCoreAvailable := UInt32.toInt32 (UInt8.toUInt32 newPrimaryIndex) != UInt32.toInt32 (UInt8.toUInt32 s.primary)
    if altCoreAvailable && (decide (primaryErrorScore > (Binary32.ofBits 0x3f800000 /- 1.0f -/)) || !(NavEKF3_core.healthy w.heap'NavEKF3_core[((WPtr.index s.core) + (UInt8.toNat s.primary))]!) || betterCore) then
      let (t'21, t'22) := switchLane s w o newPrimaryIndex
      s := t'21
      o := t'22
      s := resetCoreErrors s
      s := { s with coreLastTimePrimary_us := s.coreLastTimePrimary_us.set! (UInt8.toNat s.primary) s.imuSampleTime_us }
  if UInt32.toInt32 (UInt8.toUInt32 s.primary) != UInt32.toInt32 (UInt8.toUInt32 user_primary) && NavEKF3_core.healthy w.heap'NavEKF3_core[((WPtr.index s.core) + (UInt8.toNat user_primary))]! && !armed then
    s := { s with primary := user_primary }
  pure ()  -- C++ `align_inactive_sources`: no effect in the model
  return (s, w, o)

/-- C++ `int8_t NavEKF3::getPrimaryCoreIndex() const`, `AP_NavEKF3/AP_NavEKF3.cpp:1218-1224`. -/
def getPrimaryCoreIndex (s : State) : Int8 := Id.run do
  if !(s.core != WPtr.null) then
    return Int32.toInt8 (-(1 : Int32))
  return UInt8.toInt8 s.primary

/-- C++ `uint16_t NavEKF3::getYawResetCount()`, `AP_NavEKF3/AP_NavEKF3.cpp:1898-1909`. -/
def getYawResetCount (s : State) (w : World) : State × UInt16 := Id.run do
  let mut s := s
  if !(s.core != WPtr.null) then
    return (s, Int16.toUInt16 (Int32.toInt16 (0 : Int32)))
  let core_count : UInt16 := NavEKF3_core.getYawResetCount w.heap'NavEKF3_core[((WPtr.index s.core) + (UInt8.toNat s.primary))]!
  if UInt32.toInt32 (UInt16.toUInt32 core_count) != UInt32.toInt32 (UInt16.toUInt32 s.yaw_reset_data.last_core_count) then
    s := { s with yaw_reset_data.last_core_count := core_count }
    s := { s with yaw_reset_data.count := s.yaw_reset_data.count + (1 : UInt16) }
  return (s, s.yaw_reset_data.count)

/-- C++ `uint16_t NavEKF3::getPosNorthEastResetCount()`, `AP_NavEKF3/AP_NavEKF3.cpp:1868-1879`. -/
def getPosNorthEastResetCount (s : State) (w : World) : State × UInt16 := Id.run do
  let mut s := s
  if !(s.core != WPtr.null) then
    return (s, Int16.toUInt16 (Int32.toInt16 (0 : Int32)))
  let core_count : UInt16 := NavEKF3_core.getPosNorthEastResetCount w.heap'NavEKF3_core[((WPtr.index s.core) + (UInt8.toNat s.primary))]!
  if UInt32.toInt32 (UInt16.toUInt32 core_count) != UInt32.toInt32 (UInt16.toUInt32 s.pos_reset_data.last_core_count) then
    s := { s with pos_reset_data.last_core_count := core_count }
    s := { s with pos_reset_data.count := s.pos_reset_data.count + (1 : UInt16) }
  return (s, s.pos_reset_data.count)

/-- C++ `uint16_t NavEKF3::getPosDownResetCount()`, `AP_NavEKF3/AP_NavEKF3.cpp:1883-1894`. -/
def getPosDownResetCount (s : State) (w : World) : State × UInt16 := Id.run do
  let mut s := s
  if !(s.core != WPtr.null) then
    return (s, Int16.toUInt16 (Int32.toInt16 (0 : Int32)))
  let core_count : UInt16 := NavEKF3_core.getPosDownResetCount w.heap'NavEKF3_core[((WPtr.index s.core) + (UInt8.toNat s.primary))]!
  if UInt32.toInt32 (UInt16.toUInt32 core_count) != UInt32.toInt32 (UInt16.toUInt32 s.pos_down_reset_data.last_core_count) then
    s := { s with pos_down_reset_data.last_core_count := core_count }
    s := { s with pos_down_reset_data.count := s.pos_down_reset_data.count + (1 : UInt16) }
  return (s, s.pos_down_reset_data.count)

end NavEKF3

namespace NavEKF3

/-- C++ `float NavEKF3::getPosDownDerivative() const`, `AP_NavEKF3/AP_NavEKF3.cpp:1299-1306`. -/
def getPosDownDerivative (s : State) (w : World) : Binary32 := Id.run do
  if (s.core != WPtr.null) then
    return NavEKF3_core.getPosDownDerivative w.heap'NavEKF3_core[((WPtr.index s.core) + (UInt8.toNat s.primary))]!
  return (Binary32.ofBits 0x00000000 /- 0.0f -/)

/-- C++ `void NavEKF3::getGyroBias(int8_t instance, Vector3f & gyroBias) const`, `AP_NavEKF3/AP_NavEKF3.cpp:1309-1315`. -/
def getGyroBias (s : State) (w : World) («instance» : Int8) (gyroBias : Vector3f.State) : Vector3f.State := Id.run do
  let mut «instance» := «instance»
  let mut gyroBias := gyroBias
  if decide (Int8.toInt32 «instance» < (0 : Int32)) || decide (Int8.toInt32 «instance» ≥ UInt32.toInt32 (UInt8.toUInt32 s.num_cores)) then
    «instance» := UInt8.toInt8 s.primary
  if (s.core != WPtr.null) then
    gyroBias := NavEKF3_core.getGyroBias w.heap'NavEKF3_core[((WPtr.index s.core) + (Int8.toNatClampNeg «instance»))]! gyroBias
  return gyroBias

end NavEKF3

namespace NavEKF3_core

/-- C++ `bool NavEKF3_core::using_gps() const`, `AP_NavEKF3/AP_NavEKF3_Control.cpp:690-693`. -/
def using_gps (s : State) (w : World) : World × Bool := Id.run do
  let mut w := w
  let (t'1, t'2) := AP_NavEKF_Source.usingGPS w.EKF3.sources w s.core_index
  w := t'1
  return (w, t'2)

end NavEKF3_core

namespace NavEKF3

/-- C++ `bool NavEKF3::using_gps() const`, `AP_NavEKF3/AP_NavEKF3.cpp:1618-1624`. -/
def using_gps (s : State) (w : World) : State × World × Bool := Id.run do
  let mut s := s
  let mut w := w
  if !(s.core != WPtr.null) then
    return (s, w, false)
  w := { w with EKF3 := s }  -- this object's state into the World: the call reaches it
  let (t'1, t'2) := NavEKF3_core.using_gps w.heap'NavEKF3_core[((WPtr.index s.core) + (UInt8.toNat s.primary))]! w
  w := t'1
  s := w.EKF3  -- this object's state as the call left it
  return (s, w, t'2)

/-- C++ `bool NavEKF3::using_noncompass_for_yaw() const`, `AP_NavEKF3/AP_NavEKF3.cpp:1600-1606`. -/
def using_noncompass_for_yaw (s : State) (w : World) : Bool := Id.run do
  if !(s.core != WPtr.null) then
    return false
  return NavEKF3_core.using_noncompass_for_yaw w.heap'NavEKF3_core[((WPtr.index s.core) + (UInt8.toNat s.primary))]! w

end NavEKF3

namespace NavEKF3

/-- C++ `void NavEKF3::checkLaneSwitch()`, `AP_NavEKF3/AP_NavEKF3.cpp:1057-1089`. -/
def checkLaneSwitch (s : State) (w : World) (o : Outputs) : State × World × Outputs := Id.run do
  let mut s := s
  let mut w := w
  let mut o := o
  let t'1 := w.heap'AP_DAL[(WPtr.index w.AP_DAL'_singleton)]!  -- the object out of its slot for the call (--swap-out)
  w := { w with heap'AP_DAL := w.heap'AP_DAL.set! (WPtr.index w.AP_DAL'_singleton) default }
  w := { w with heap'AP_DAL := w.heap'AP_DAL.set! (WPtr.index w.AP_DAL'_singleton) (AP_DAL.log_event3 t'1 AP_DAL.Event.checkLaneSwitch) }
  if option_is_enabled s NavEKF3.Option.ManualLaneSwitch then
    return (s, w, o)
  let now : UInt32 := AP_DAL.millis w.heap'AP_DAL[(WPtr.index w.AP_DAL'_singleton)]!
  if s.lastLaneSwitch_ms != Int32.toUInt32 (0 : Int32) && decide (now - s.lastLaneSwitch_ms < Int32.toUInt32 (5000 : Int32)) then
    return (s, w, o)
  w := { w with EKF3 := s }  -- this object's state into the World: the call reaches it
  let primaryErrorScore : Binary32 := NavEKF3_core.errorScore w.heap'NavEKF3_core[((WPtr.index s.core) + (UInt8.toNat s.primary))]! w
  let mut lowestErrorScore : Binary32 := primaryErrorScore
  let mut newPrimaryIndex : UInt8 := s.primary
  let t'2 : UInt8 := Int8.toUInt8 (Int32.toInt8 (0 : Int32))
  let t'3 : Int32 := UInt32.toInt32 (UInt8.toUInt32 s.num_cores)
  for coreIndex' in [0:(t'3.toInt - (Int.ofNat t'2.toNat)).toNat] do  -- C++ loop bounded by a runtime value (--runtime-loops)
    let coreIndex : UInt8 := t'2 + Nat.toUInt8 coreIndex'
    if UInt32.toInt32 (UInt8.toUInt32 coreIndex) != UInt32.toInt32 (UInt8.toUInt32 s.primary) then
      let altCoreAvailable : Bool := NavEKF3_core.healthy w.heap'NavEKF3_core[((WPtr.index s.core) + (UInt8.toNat coreIndex))]! && NavEKF3_core.have_aligned_yaw w.heap'NavEKF3_core[((WPtr.index s.core) + (UInt8.toNat coreIndex))]! && NavEKF3_core.have_aligned_tilt w.heap'NavEKF3_core[((WPtr.index s.core) + (UInt8.toNat coreIndex))]!
      w := { w with EKF3 := s }  -- this object's state into the World: the call reaches it
      let altErrorScore : Binary32 := NavEKF3_core.errorScore w.heap'NavEKF3_core[((WPtr.index s.core) + (UInt8.toNat coreIndex))]! w
      if altCoreAvailable && decide (altErrorScore < lowestErrorScore) && decide (altErrorScore < (Binary32.ofBits 0x3f666666 /- 0.9 -/)) then
        newPrimaryIndex := coreIndex
        lowestErrorScore := altErrorScore
  let (t'4, t'5) := switchLane s w o newPrimaryIndex
  s := t'4
  o := t'5
  return (s, w, o)

end NavEKF3

namespace NavEKF3

/-- C++ `bool NavEKF3::InitialiseFilterBootstrap()`, `AP_NavEKF3/AP_NavEKF3.cpp:1991-2014`. -/
def InitialiseFilterBootstrap (s : State) (w : World) (o : Outputs) : State × World × Outputs × Bool := Id.run do
  let mut s := s
  let mut w := w
  let mut o := o
  if !(s.core != WPtr.null) then
    return (s, w, o, false)
  let mut ret : Bool := true
  let t'1 : UInt8 := Int8.toUInt8 (Int32.toInt8 (0 : Int32))
  let t'2 : Int32 := UInt32.toInt32 (UInt8.toUInt32 s.num_cores)
  for i' in [0:(t'2.toInt - (Int.ofNat t'1.toNat)).toNat] do  -- C++ loop bounded by a runtime value (--runtime-loops)
    let i : UInt8 := t'1 + Nat.toUInt8 i'
    let t'3 := w.heap'NavEKF3_core[((WPtr.index s.core) + (UInt8.toNat i))]!  -- the object out of its slot for the call (--swap-out)
    w := { w with heap'NavEKF3_core := w.heap'NavEKF3_core.set! ((WPtr.index s.core) + (UInt8.toNat i)) default }
    w := { w with heap'NavEKF3_core := w.heap'NavEKF3_core.set! ((WPtr.index s.core) + (UInt8.toNat i)) (NavEKF3_core.clearStatesInitialised t'3) }
    w := { w with EKF3 := s }  -- this object's state into the World: the call reaches it
    let t'4 := w.heap'NavEKF3_core[((WPtr.index s.core) + (UInt8.toNat i))]!  -- the object out of its slot for the call (--swap-out)
    w := { w with heap'NavEKF3_core := w.heap'NavEKF3_core.set! ((WPtr.index s.core) + (UInt8.toNat i)) default }
    let (t'5, t'6, t'7, _) := NavEKF3_core.InitialiseFilterBootstrap t'4 w o
    w := t'6
    w := { w with heap'NavEKF3_core := w.heap'NavEKF3_core.set! ((WPtr.index s.core) + (UInt8.toNat i)) t'5 }
    o := t'7
    s := w.EKF3  -- this object's state as the call left it
    if !(NavEKF3_core.isStatesInitialised w.heap'NavEKF3_core[((WPtr.index s.core) + (UInt8.toNat i))]!) then
      ret := false
  return (s, w, o, ret)

end NavEKF3

namespace NavEKF3

/-- C++ `bool NavEKF3::pre_arm_check(bool requires_position, char * failure_msg, uint8_t failure_msg_len) const`, `AP_NavEKF3/AP_NavEKF3.cpp:1176-1214`. -/
def pre_arm_check (s : State) (w : World) (requires_position : Bool) (failure_msg : CText) (failure_msg_len : UInt8) : World × CText × Bool := Id.run do
  let mut w := w
  let mut failure_msg := failure_msg
  let (t'1, t'2, t'3) := AP_NavEKF_Source.pre_arm_check s.sources w requires_position failure_msg failure_msg_len
  w := t'1
  failure_msg := t'2
  if !t'3 then
    return (w, failure_msg, false)
  let magCalParamVal : Int8 := AP_ParamT_signed_char_1.get_void s._magCal
  for i' in [0:s.num_cores.toNat] do
    let i : UInt8 := Nat.toUInt8 i'
    let (t'4, t'5) := AP_NavEKF_Source.getYawSource s.sources w i
    w := t'4
    let yaw_source : AP_NavEKF_Source.SourceYaw := t'5
    if ((Int8.toInt32 magCalParamVal == (5 : Int32)) || (Int8.toInt32 magCalParamVal == (6 : Int32))) && (yaw_source != AP_NavEKF_Source.SourceYaw.GPS) then
      failure_msg := (CText.fmt (UInt8.toUInt64 failure_msg_len) "EK3_MAG_CAL and EK3_SRC1_YAW inconsistent" #[])
      return (w, failure_msg, false)
  if !(s.core != WPtr.null) then
    failure_msg := (CText.fmt (UInt8.toUInt64 failure_msg_len) "no EKF3 cores" #[])
    return (w, failure_msg, false)
  for i'2' in [0:s.num_cores.toNat] do
    let i'2 : UInt8 := Nat.toUInt8 i'2'
    if !(NavEKF3_core.healthy w.heap'NavEKF3_core[((WPtr.index s.core) + (UInt8.toNat i'2))]!) then
      let failure : CText := (NavEKF3_core.prearm_failure_reason w.heap'NavEKF3_core[((WPtr.index s.core) + (UInt8.toNat i'2))]!)
      if !(CText.isNull failure) then
        failure_msg := (CText.text (UInt8.toUInt64 failure_msg_len) failure #[])
      else
        failure_msg := (CText.fmt (UInt8.toUInt64 failure_msg_len) "EKF3 core %d unhealthy" #[Sum.inl (Int64.toUInt64 (Int32.toInt64 (UInt32.toInt32 (UInt8.toUInt32 i'2))))])
      return (w, failure_msg, false)
    w := { w with EKF3 := s }  -- this object's state into the World: the call reaches it
    let (t'6, t'7) := NavEKF3_core.pre_arm_check w.heap'NavEKF3_core[((WPtr.index s.core) + (UInt8.toNat i'2))]! w requires_position failure_msg failure_msg_len
    failure_msg := t'6
    if !t'7 then
      return (w, failure_msg, false)
  return (w, failure_msg, true)

end NavEKF3

namespace NavEKF3

/-- C++ `void NavEKF3::resetGyroBias()`, `AP_NavEKF3/AP_NavEKF3.cpp:1333-1342`. -/
def resetGyroBias (s : State) (w : World) : World := Id.run do
  let mut w := w
  let t'1 := w.heap'AP_DAL[(WPtr.index w.AP_DAL'_singleton)]!  -- the object out of its slot for the call (--swap-out)
  w := { w with heap'AP_DAL := w.heap'AP_DAL.set! (WPtr.index w.AP_DAL'_singleton) default }
  w := { w with heap'AP_DAL := w.heap'AP_DAL.set! (WPtr.index w.AP_DAL'_singleton) (AP_DAL.log_event3 t'1 AP_DAL.Event.resetGyroBias) }
  if (s.core != WPtr.null) then
    let t'2 : UInt8 := Int8.toUInt8 (Int32.toInt8 (0 : Int32))
    let t'3 : Int32 := UInt32.toInt32 (UInt8.toUInt32 s.num_cores)
    for i' in [0:(t'3.toInt - (Int.ofNat t'2.toNat)).toNat] do  -- C++ loop bounded by a runtime value (--runtime-loops)
      let i : UInt8 := t'2 + Nat.toUInt8 i'
      let t'4 := w.heap'NavEKF3_core[((WPtr.index s.core) + (UInt8.toNat i))]!  -- the object out of its slot for the call (--swap-out)
      w := { w with heap'NavEKF3_core := w.heap'NavEKF3_core.set! ((WPtr.index s.core) + (UInt8.toNat i)) default }
      w := { w with heap'NavEKF3_core := w.heap'NavEKF3_core.set! ((WPtr.index s.core) + (UInt8.toNat i)) (NavEKF3_core.resetGyroBias t'4) }
  return w

/-- C++ `NavEKF3::NavEKF3()`, `AP_NavEKF3/AP_NavEKF3.cpp:783-788`. -/
def init (w : World) : State × World := Id.run do
  let mut s : State := {}
  let mut w := w
  let (t'1, t'2) := AP_DAL.get_singleton w
  w := t'1
  let t'3 := (WPtr.index t'2)
  s := { s with common_EKF_origin := Location.init_void }
  s := { s with sources := AP_NavEKF_Source.construct }
  s := { s with _enable._value := Binary32.toInt8 (Binary32.ofBits 0x3f800000 /- (float)1 -/) }
  s := { s with _gpsHorizVelNoise._value := (Binary32.ofBits 0x3e99999a /- 0.300000012 -/) }
  s := { s with _gpsVertVelNoise._value := (Binary32.ofBits 0x3f000000 /- 0.5 -/) }
  s := { s with _gpsVelInnovGate._value := Binary32.toInt16 (Binary32.ofBits 0x43fa0000 /- (float)500 -/) }
  s := { s with _gpsHorizPosNoise._value := (Binary32.ofBits 0x3f000000 /- 0.5 -/) }
  s := { s with _gpsPosInnovGate._value := Binary32.toInt16 (Binary32.ofBits 0x43fa0000 /- (float)500 -/) }
  s := { s with _gpsGlitchRadiusMax._value := Binary32.toInt8 (Binary32.ofBits 0x41c80000 /- (float)25 -/) }
  s := { s with _baroAltNoise._value := (Binary32.ofBits 0x40000000 /- 2 -/) }
  s := { s with _hgtInnovGate._value := Binary32.toInt16 (Binary32.ofBits 0x43fa0000 /- (float)500 -/) }
  s := { s with _hgtDelay_ms._value := Binary32.toInt16 (Binary32.ofBits 0x42700000 /- (float)60 -/) }
  s := { s with _magNoise._value := (Binary32.ofBits 0x3d4ccccd /- 0.0500000007 -/) }
  s := { s with _magCal._value := Binary32.toInt8 (Binary32.ofBits 0x40400000 /- (float)3 -/) }
  s := { s with _magInnovGate._value := Binary32.toInt16 (Binary32.ofBits 0x43960000 /- (float)300 -/) }
  s := { s with _easNoise._value := (Binary32.ofBits 0x3fb33333 /- 1.39999998 -/) }
  s := { s with _tasInnovGate._value := Binary32.toInt16 (Binary32.ofBits 0x43c80000 /- (float)400 -/) }
  s := { s with _rngNoise._value := (Binary32.ofBits 0x3f000000 /- 0.5 -/) }
  s := { s with _rngInnovGate._value := Binary32.toInt16 (Binary32.ofBits 0x43fa0000 /- (float)500 -/) }
  s := { s with _maxFlowRate._value := (Binary32.ofBits 0x40200000 /- 2.5 -/) }
  s := { s with _flowNoise._value := (Binary32.ofBits 0x3e800000 /- 0.25 -/) }
  s := { s with _flowInnovGate._value := Binary32.toInt16 (Binary32.ofBits 0x43960000 /- (float)300 -/) }
  s := { s with _flowDelay_ms._value := Binary32.toInt8 (Binary32.ofBits 0x41200000 /- (float)10 -/) }
  s := { s with _gyrNoise._value := (Binary32.ofBits 0x3c75c28f /- 0.0149999997 -/) }
  s := { s with _accNoise._value := (Binary32.ofBits 0x3eb33333 /- 0.349999994 -/) }
  s := { s with _gyroBiasProcessNoise._value := (Binary32.ofBits 0x3a83126f /- 0.00100000005 -/) }
  s := { s with _accelBiasProcessNoise._value := (Binary32.ofBits 0x3ca3d70a /- 0.0199999996 -/) }
  s := { s with _windVelProcessNoise._value := (Binary32.ofBits 0x3e4ccccd /- (float)3602879701896397/18014398509481984 -/) }
  s := { s with _wndVarHgtRateScale._value := (Binary32.ofBits 0x3f800000 /- 1 -/) }
  s := { s with _gpsCheck._value := Int8.toUInt8 (Binary32.toInt8 (Binary32.ofBits 0x41f80000 /- (float)31 -/)) }
  s := { s with _imuMask._value := Int8.toUInt8 (Binary32.toInt8 (Binary32.ofBits 0x40400000 /- (float)3 -/)) }
  s := { s with _gpsCheckScaler._value := Binary32.toInt16 (Binary32.ofBits 0x42c80000 /- (float)100 -/) }
  s := { s with _noaidHorizNoise._value := (Binary32.ofBits 0x41200000 /- 10 -/) }
  s := { s with _betaMask._value := Int8.toUInt8 (Binary32.toInt8 (Binary32.ofBits 0x00000000 /- (float)0 -/)) }
  s := { s with _yawNoise._value := (Binary32.ofBits 0x3f000000 /- 0.5 -/) }
  s := { s with _yawInnovGate._value := Binary32.toInt16 (Binary32.ofBits 0x43960000 /- (float)300 -/) }
  s := { s with _tauVelPosOutput._value := Binary32.toInt8 (Binary32.ofBits 0x41c80000 /- (float)25 -/) }
  s := { s with _magEarthProcessNoise._value := (Binary32.ofBits 0x3a83126f /- 0.00100000005 -/) }
  s := { s with _magBodyProcessNoise._value := (Binary32.ofBits 0x38d1b717 /- 9.99999974E-5 -/) }
  s := { s with _useRngSwHgt._value := Binary32.toInt8 (Binary32.ofBits 0xbf800000 /- (float)-1 -/) }
  s := { s with _terrGradMax._value := (Binary32.ofBits 0x3dcccccd /- 0.100000001 -/) }
  s := { s with _rngBcnNoise._value := (Binary32.ofBits 0x3f800000 /- 1 -/) }
  s := { s with _rngBcnInnovGate._value := Binary32.toInt16 (Binary32.ofBits 0x43fa0000 /- (float)500 -/) }
  s := { s with _rngBcnDelay_ms._value := Binary32.toInt8 (Binary32.ofBits 0x42480000 /- (float)50 -/) }
  s := { s with _useRngSwSpd._value := (Binary32.ofBits 0x40000000 /- 2 -/) }
  s := { s with _accBiasLim._value := (Binary32.ofBits 0x3f800000 /- 1 -/) }
  s := { s with _magMask._value := Int8.toUInt8 (Binary32.toInt8 (Binary32.ofBits 0x00000000 /- (float)0 -/)) }
  s := { s with _originHgtMode._value := Int8.toUInt8 (Binary32.toInt8 (Binary32.ofBits 0x00000000 /- (float)0 -/)) }
  s := { s with _visOdmVelErrMin._value := (Binary32.ofBits 0x3dcccccd /- 0.100000001 -/) }
  s := { s with _visOdmVelErrMax._value := (Binary32.ofBits 0x3f666666 /- 0.899999976 -/) }
  s := { s with _wencOdmVelErr._value := (Binary32.ofBits 0x3dcccccd /- 0.100000001 -/) }
  s := { s with _flowUse._value := Binary32.toInt8 (Binary32.ofBits 0x3f800000 /- (float)1 -/) }
  s := { s with _hrt_filt_freq._value := (Binary32.ofBits 0x40000000 /- 2 -/) }
  s := { s with _mag_ef_limit._value := Binary32.toInt16 (Binary32.ofBits 0x42480000 /- (float)50 -/) }
  s := { s with _gsfRunMask._value := Int8.toUInt8 (Binary32.toInt8 (Binary32.ofBits 0x40400000 /- (float)3 -/)) }
  s := { s with _gsfUseMask._value := Int8.toUInt8 (Binary32.toInt8 (Binary32.ofBits 0x40400000 /- (float)3 -/)) }
  s := { s with _flowNavGainHgt._value := (Binary32.ofBits 0x40800000 /- 4 -/) }
  s := { s with _gsfResetMaxCount._value := Binary32.toInt8 (Binary32.ofBits 0x40000000 /- (float)2 -/) }
  s := { s with _err_thresh._value := (Binary32.ofBits 0x3e4ccccd /- (float)3602879701896397/18014398509481984 -/) }
  s := { s with _affinity._value := Int32.toUInt32 (Binary32.toInt32 (Binary32.ofBits 0x00000000 /- (float)0 -/)) }
  s := { s with _ballisticCoef_x._value := (Binary32.ofBits 0x00000000 /- 0 -/) }
  s := { s with _ballisticCoef_y._value := (Binary32.ofBits 0x00000000 /- 0 -/) }
  s := { s with _dragObsNoise._value := (Binary32.ofBits 0x3f000000 /- 0.5 -/) }
  s := { s with _momentumDragCoef._value := (Binary32.ofBits 0x00000000 /- 0 -/) }
  s := { s with _ognmTestScaleFactor._value := (Binary32.ofBits 0x40000000 /- 2 -/) }
  s := { s with _baroGndEffectDeadZone._value := (Binary32.ofBits 0x40800000 /- 4 -/) }
  s := { s with _primary_core._value := Int8.toUInt8 (Binary32.toInt8 (Binary32.ofBits 0x00000000 /- (float)0 -/)) }
  s := { s with _log_level._value := Binary32.toInt8 (Binary32.ofBits 0x00000000 /- (float)0 -/) }
  s := { s with _gpsVAccThreshold._value := (Binary32.ofBits 0x00000000 /- 0 -/) }
  s := { s with _options._value := Int32.toUInt32 (Binary32.toInt32 (Binary32.ofBits 0x00000000 /- (float)0 -/)) }
  return (s, w)

/-- C++ `enum class NavEKF3::LogLevel`, `AP_NavEKF3/AP_NavEKF3.h:394-399`. -/
inductive LogLevel where
  | ALL
  | XKF4
  | XKF4_GSF
  | NONE
deriving DecidableEq, Inhabited

/-- The value of each enumerator of `NavEKF3::LogLevel` (underlying type `int32_t`). -/
def LogLevel.toInt : LogLevel → Int32
  | .ALL => (0 : Int32)
  | .XKF4 => (1 : Int32)
  | .XKF4_GSF => (2 : Int32)
  | .NONE => (3 : Int32)

end NavEKF3

end Estimator_lib
