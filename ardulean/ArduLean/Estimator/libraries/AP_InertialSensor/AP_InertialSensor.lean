import ArduLean.Runtime.CFloat
import ArduLean.Estimator.libraries.AP_Math.AP_Math
import ArduLean.Estimator.World
import ArduLean.Estimator.libraries.Filter.Filter
import ArduLean.Estimator.libraries.AP_Param.AP_Param

/-!
ArduPilot `libraries/AP_InertialSensor`, part 1 of 3. Sources: `libraries/AP_InertialSensor/AP_InertialSensor.h`, `libraries/AP_InertialSensor/AP_InertialSensor_Backend.h`, `libraries/AP_InertialSensor/AP_InertialSensor.cpp`, `libraries/AP_InertialSensor/AP_InertialSensor_SITL.h`, `libraries/AP_InertialSensor/AP_InertialSensor_Backend.cpp`.

Items of `lean/Estimator_lib.lean` (the estimator translation), unchanged; placed by `tools/split_modules.py` (`ArduLean/Estimator/INDEX.md`).
-/

open FloatLib.Floats (Binary32 Binary64)

set_option maxRecDepth 200000
-- AP_DAL's `const log_RISH old_RISH = _RISH;` read only by WRITE_REPLAY_BLOCK_IFCHANGED, which is `(void)old`
-- without logging (HAL_LOGGING_ENABLED 0): an unused binding, as in the C++
set_option linter.unusedVariables false

namespace Estimator_lib

namespace AP_InertialSensor

/-- C++ `struct AP_InertialSensor::(unnamed struct at AP_InertialSensor/AP_InertialSensor.h:380:5)`, `AP_InertialSensor/AP_InertialSensor.h:380-383`. -/
structure uart_t where
  /-- `uint16_t counter` of `AP_InertialSensor::(unnamed struct at AP_InertialSensor/AP_InertialSensor.h:380:5)` (`AP_InertialSensor/AP_InertialSensor.h:381`). -/
  counter : UInt16 := (0 : UInt16)
  /-- `AP_HAL::UARTDriver * imu_out_uart` of `AP_InertialSensor::(unnamed struct at AP_InertialSensor/AP_InertialSensor.h:380:5)` (`AP_InertialSensor/AP_InertialSensor.h:382`). -/
  imu_out_uart : WPtr := WPtr.null
deriving Inhabited

/-- C++ `struct AP_InertialSensor::PeakHoldState`, `AP_InertialSensor/AP_InertialSensor.h:775-778`. -/
structure PeakHoldState where
  /-- `float accel_peak_hold_neg_x` of `AP_InertialSensor::PeakHoldState` (`AP_InertialSensor/AP_InertialSensor.h:776`). -/
  accel_peak_hold_neg_x : Binary32 := (Binary32.ofBits 0x00000000 /- 0.0 -/)
  /-- `uint32_t accel_peak_hold_neg_x_age` of `AP_InertialSensor::PeakHoldState` (`AP_InertialSensor/AP_InertialSensor.h:777`). -/
  accel_peak_hold_neg_x_age : UInt32 := (0 : UInt32)
deriving Inhabited

end AP_InertialSensor

namespace AP_InertialSensor

/-- State of C++ `AP_InertialSensor` (`AP_InertialSensor/AP_InertialSensor.h:98-896`): its data members; base classes flattened, base first: `AP_AccelCal_Client`. -/
structure State where
  /-- `uint32_t last_accel_cal_ms` of `AP_InertialSensor` (`AP_InertialSensor/AP_InertialSensor.h:363`). -/
  last_accel_cal_ms : UInt32 := (0 : UInt32)
  /-- `struct (unnamed struct at AP_InertialSensor/AP_InertialSensor.h:380:5) uart` of `AP_InertialSensor` (`AP_InertialSensor/AP_InertialSensor.h:383`). -/
  uart : AP_InertialSensor.uart_t := {}
  /-- `AP_InertialSensor_Backend * _backends[6]` of `AP_InertialSensor` (`AP_InertialSensor/AP_InertialSensor.h:565`). -/
  _backends : Array WPtr := Array.replicate 6 WPtr.null
  /-- `uint8_t _gyro_count` of `AP_InertialSensor` (`AP_InertialSensor/AP_InertialSensor.h:570`). -/
  _gyro_count : UInt8 := (0 : UInt8)
  /-- `uint8_t _accel_count` of `AP_InertialSensor` (`AP_InertialSensor/AP_InertialSensor.h:571`). -/
  _accel_count : UInt8 := (0 : UInt8)
  /-- `uint8_t _backend_count` of `AP_InertialSensor` (`AP_InertialSensor/AP_InertialSensor.h:572`). -/
  _backend_count : UInt8 := (0 : UInt8)
  /-- `uint16_t _loop_rate` of `AP_InertialSensor` (`AP_InertialSensor/AP_InertialSensor.h:575`). -/
  _loop_rate : UInt16 := (0 : UInt16)
  /-- `float _loop_delta_t` of `AP_InertialSensor` (`AP_InertialSensor/AP_InertialSensor.h:576`). -/
  _loop_delta_t : Binary32 := (Binary32.ofBits 0x00000000 /- 0.0 -/)
  /-- `float _loop_delta_t_max` of `AP_InertialSensor` (`AP_InertialSensor/AP_InertialSensor.h:577`). -/
  _loop_delta_t_max : Binary32 := (Binary32.ofBits 0x00000000 /- 0.0 -/)
  /-- `Vector3f _accel[3]` of `AP_InertialSensor` (`AP_InertialSensor/AP_InertialSensor.h:580`). -/
  _accel : Array Vector3f.State := Array.replicate 3 {}
  /-- `Vector3f _delta_velocity[3]` of `AP_InertialSensor` (`AP_InertialSensor/AP_InertialSensor.h:581`). -/
  _delta_velocity : Array Vector3f.State := Array.replicate 3 {}
  /-- `float _delta_velocity_dt[3]` of `AP_InertialSensor` (`AP_InertialSensor/AP_InertialSensor.h:582`). -/
  _delta_velocity_dt : Array Binary32 := Array.replicate 3 (Binary32.ofBits 0x00000000 /- 0.0 -/)
  /-- `bool _delta_velocity_valid[3]` of `AP_InertialSensor` (`AP_InertialSensor/AP_InertialSensor.h:583`). -/
  _delta_velocity_valid : Array Bool := Array.replicate 3 false
  /-- `Vector3f _delta_velocity_acc[3]` of `AP_InertialSensor` (`AP_InertialSensor/AP_InertialSensor.h:585`). -/
  _delta_velocity_acc : Array Vector3f.State := Array.replicate 3 {}
  /-- `float _delta_velocity_acc_dt[3]` of `AP_InertialSensor` (`AP_InertialSensor/AP_InertialSensor.h:587`). -/
  _delta_velocity_acc_dt : Array Binary32 := Array.replicate 3 (Binary32.ofBits 0x00000000 /- 0.0 -/)
  /-- `LowPassFilter2pVector3f _accel_filter[3]` of `AP_InertialSensor` (`AP_InertialSensor/AP_InertialSensor.h:590`). -/
  _accel_filter : Array LowPassFilter2p_Vector3_float.State := Array.replicate 3 LowPassFilter2p_Vector3_float.init_void
  /-- `LowPassFilter2pVector3f _gyro_filter[3]` of `AP_InertialSensor` (`AP_InertialSensor/AP_InertialSensor.h:591`). -/
  _gyro_filter : Array LowPassFilter2p_Vector3_float.State := Array.replicate 3 LowPassFilter2p_Vector3_float.init_void
  /-- `Vector3f _accel_filtered[3]` of `AP_InertialSensor` (`AP_InertialSensor/AP_InertialSensor.h:592`). -/
  _accel_filtered : Array Vector3f.State := Array.replicate 3 {}
  /-- `Vector3f _gyro_filtered[3]` of `AP_InertialSensor` (`AP_InertialSensor/AP_InertialSensor.h:593`). -/
  _gyro_filtered : Array Vector3f.State := Array.replicate 3 {}
  /-- `bool _new_accel_data[3]` of `AP_InertialSensor` (`AP_InertialSensor/AP_InertialSensor.h:605`). -/
  _new_accel_data : Array Bool := Array.replicate 3 false
  /-- `bool _new_gyro_data[3]` of `AP_InertialSensor` (`AP_InertialSensor/AP_InertialSensor.h:606`). -/
  _new_gyro_data : Array Bool := Array.replicate 3 false
  /-- `Vector3f _gyro[3]` of `AP_InertialSensor` (`AP_InertialSensor/AP_InertialSensor.h:609`). -/
  _gyro : Array Vector3f.State := Array.replicate 3 {}
  /-- `Vector3f _delta_angle[3]` of `AP_InertialSensor` (`AP_InertialSensor/AP_InertialSensor.h:610`). -/
  _delta_angle : Array Vector3f.State := Array.replicate 3 {}
  /-- `float _delta_angle_dt[3]` of `AP_InertialSensor` (`AP_InertialSensor/AP_InertialSensor.h:611`). -/
  _delta_angle_dt : Array Binary32 := Array.replicate 3 (Binary32.ofBits 0x00000000 /- 0.0 -/)
  /-- `bool _delta_angle_valid[3]` of `AP_InertialSensor` (`AP_InertialSensor/AP_InertialSensor.h:612`). -/
  _delta_angle_valid : Array Bool := Array.replicate 3 false
  /-- `float _delta_angle_acc_dt[3]` of `AP_InertialSensor` (`AP_InertialSensor/AP_InertialSensor.h:614`). -/
  _delta_angle_acc_dt : Array Binary32 := Array.replicate 3 (Binary32.ofBits 0x00000000 /- 0.0 -/)
  /-- `Vector3f _delta_angle_acc[3]` of `AP_InertialSensor` (`AP_InertialSensor/AP_InertialSensor.h:615`). -/
  _delta_angle_acc : Array Vector3f.State := Array.replicate 3 {}
  /-- `Vector3f _last_delta_angle[3]` of `AP_InertialSensor` (`AP_InertialSensor/AP_InertialSensor.h:616`). -/
  _last_delta_angle : Array Vector3f.State := Array.replicate 3 {}
  /-- `Vector3f _last_raw_gyro[3]` of `AP_InertialSensor` (`AP_InertialSensor/AP_InertialSensor.h:617`). -/
  _last_raw_gyro : Array Vector3f.State := Array.replicate 3 {}
  /-- `uint8_t _accel_sensor_rate_sampling_enabled` of `AP_InertialSensor` (`AP_InertialSensor/AP_InertialSensor.h:620`). -/
  _accel_sensor_rate_sampling_enabled : UInt8 := (0 : UInt8)
  /-- `uint8_t _gyro_sensor_rate_sampling_enabled` of `AP_InertialSensor` (`AP_InertialSensor/AP_InertialSensor.h:621`). -/
  _gyro_sensor_rate_sampling_enabled : UInt8 := (0 : UInt8)
  /-- `uint16_t _accel_raw_sampling_multiplier[3]` of `AP_InertialSensor` (`AP_InertialSensor/AP_InertialSensor.h:624`). -/
  _accel_raw_sampling_multiplier : Array UInt16 := Array.replicate 3 (0 : UInt16)
  /-- `uint16_t _gyro_raw_sampling_multiplier[3]` of `AP_InertialSensor` (`AP_InertialSensor/AP_InertialSensor.h:625`). -/
  _gyro_raw_sampling_multiplier : Array UInt16 := Array.replicate 3 (0 : UInt16)
  /-- `AP_UInt32 _accel_id_old_param[3]` of `AP_InertialSensor` (`AP_InertialSensor/AP_InertialSensor.h:629`). -/
  _accel_id_old_param : Array AP_ParamT_unsigned_int_3.State := Array.replicate 3 {}
  /-- `AP_UInt32 _gyro_id_old_param[3]` of `AP_InertialSensor` (`AP_InertialSensor/AP_InertialSensor.h:630`). -/
  _gyro_id_old_param : Array AP_ParamT_unsigned_int_3.State := Array.replicate 3 {}
  /-- `AP_Vector3f _accel_scale_old_param[3]` of `AP_InertialSensor` (`AP_InertialSensor/AP_InertialSensor.h:633`). -/
  _accel_scale_old_param : Array AP_ParamV_Vector3_float_5.State := Array.replicate 3 {}
  /-- `AP_Vector3f _accel_offset_old_param[3]` of `AP_InertialSensor` (`AP_InertialSensor/AP_InertialSensor.h:634`). -/
  _accel_offset_old_param : Array AP_ParamV_Vector3_float_5.State := Array.replicate 3 {}
  /-- `AP_Vector3f _gyro_offset_old_param[3]` of `AP_InertialSensor` (`AP_InertialSensor/AP_InertialSensor.h:635`). -/
  _gyro_offset_old_param : Array AP_ParamV_Vector3_float_5.State := Array.replicate 3 {}
  /-- `AP_Vector3f _accel_pos_old_param[3]` of `AP_InertialSensor` (`AP_InertialSensor/AP_InertialSensor.h:638`). -/
  _accel_pos_old_param : Array AP_ParamV_Vector3_float_5.State := Array.replicate 3 {}
  /-- `float _accel_raw_sample_rates[3]` of `AP_InertialSensor` (`AP_InertialSensor/AP_InertialSensor.h:672`). -/
  _accel_raw_sample_rates : Array Binary32 := Array.replicate 3 (Binary32.ofBits 0x00000000 /- 0.0 -/)
  /-- `float _gyro_raw_sample_rates[3]` of `AP_InertialSensor` (`AP_InertialSensor/AP_InertialSensor.h:673`). -/
  _gyro_raw_sample_rates : Array Binary32 := Array.replicate 3 (Binary32.ofBits 0x00000000 /- 0.0 -/)
  /-- `uint8_t _accel_over_sampling[3]` of `AP_InertialSensor` (`AP_InertialSensor/AP_InertialSensor.h:676`). -/
  _accel_over_sampling : Array UInt8 := Array.replicate 3 (0 : UInt8)
  /-- `uint8_t _gyro_over_sampling[3]` of `AP_InertialSensor` (`AP_InertialSensor/AP_InertialSensor.h:677`). -/
  _gyro_over_sampling : Array UInt8 := Array.replicate 3 (0 : UInt8)
  /-- `uint64_t _accel_last_sample_us[3]` of `AP_InertialSensor` (`AP_InertialSensor/AP_InertialSensor.h:681`). -/
  _accel_last_sample_us : Array UInt64 := Array.replicate 3 (0 : UInt64)
  /-- `uint64_t _gyro_last_sample_us[3]` of `AP_InertialSensor` (`AP_InertialSensor/AP_InertialSensor.h:682`). -/
  _gyro_last_sample_us : Array UInt64 := Array.replicate 3 (0 : UInt64)
  /-- `uint16_t _sample_accel_count[3]` of `AP_InertialSensor` (`AP_InertialSensor/AP_InertialSensor.h:685`). -/
  _sample_accel_count : Array UInt16 := Array.replicate 3 (0 : UInt16)
  /-- `uint32_t _sample_accel_start_us[3]` of `AP_InertialSensor` (`AP_InertialSensor/AP_InertialSensor.h:686`). -/
  _sample_accel_start_us : Array UInt32 := Array.replicate 3 (0 : UInt32)
  /-- `uint16_t _sample_gyro_count[3]` of `AP_InertialSensor` (`AP_InertialSensor/AP_InertialSensor.h:687`). -/
  _sample_gyro_count : Array UInt16 := Array.replicate 3 (0 : UInt16)
  /-- `uint32_t _sample_gyro_start_us[3]` of `AP_InertialSensor` (`AP_InertialSensor/AP_InertialSensor.h:688`). -/
  _sample_gyro_start_us : Array UInt32 := Array.replicate 3 (0 : UInt32)
  /-- `float _temperature[3]` of `AP_InertialSensor` (`AP_InertialSensor/AP_InertialSensor.h:691`). -/
  _temperature : Array Binary32 := Array.replicate 3 (Binary32.ofBits 0x00000000 /- 0.0 -/)
  /-- `AP_Int16 _accel_filter_cutoff` of `AP_InertialSensor` (`AP_InertialSensor/AP_InertialSensor.h:694`). -/
  _accel_filter_cutoff : AP_ParamT_short_2.State := {}
  /-- `AP_Int16 _gyro_filter_cutoff` of `AP_InertialSensor` (`AP_InertialSensor/AP_InertialSensor.h:695`). -/
  _gyro_filter_cutoff : AP_ParamT_short_2.State := {}
  /-- `AP_Int8 _gyro_cal_timing` of `AP_InertialSensor` (`AP_InertialSensor/AP_InertialSensor.h:696`). -/
  _gyro_cal_timing : AP_ParamT_signed_char_1.State := {}
  /-- `AP_Int8 _use_old_param[3]` of `AP_InertialSensor` (`AP_InertialSensor/AP_InertialSensor.h:699`). -/
  _use_old_param : Array AP_ParamT_signed_char_1.State := Array.replicate 3 {}
  /-- `AP_UInt8 _fast_sampling_mask` of `AP_InertialSensor` (`AP_InertialSensor/AP_InertialSensor.h:703`). -/
  _fast_sampling_mask : AP_ParamT_unsigned_char_1.State := {}
  /-- `AP_UInt8 _fast_sampling_rate` of `AP_InertialSensor` (`AP_InertialSensor/AP_InertialSensor.h:706`). -/
  _fast_sampling_rate : AP_ParamT_unsigned_char_1.State := {}
  /-- `AP_UInt8 _enable_mask` of `AP_InertialSensor` (`AP_InertialSensor/AP_InertialSensor.h:709`). -/
  _enable_mask : AP_ParamT_unsigned_char_1.State := {}
  /-- `enum Rotation _board_orientation` of `AP_InertialSensor` (`AP_InertialSensor/AP_InertialSensor.h:712`). -/
  _board_orientation : Rotation := Rotation.ROTATION_NONE
  /-- `enum Rotation _gyro_orientation[3]` of `AP_InertialSensor` (`AP_InertialSensor/AP_InertialSensor.h:715`). -/
  _gyro_orientation : Array Rotation := Array.replicate 3 Rotation.ROTATION_NONE
  /-- `enum Rotation _accel_orientation[3]` of `AP_InertialSensor` (`AP_InertialSensor/AP_InertialSensor.h:716`). -/
  _accel_orientation : Array Rotation := Array.replicate 3 Rotation.ROTATION_NONE
  /-- `bool _gyro_cal_ok[3]` of `AP_InertialSensor` (`AP_InertialSensor/AP_InertialSensor.h:719`). -/
  _gyro_cal_ok : Array Bool := Array.replicate 3 false
  /-- `bool _accel_id_ok[3]` of `AP_InertialSensor` (`AP_InertialSensor/AP_InertialSensor.h:720`). -/
  _accel_id_ok : Array Bool := Array.replicate 3 false
  /-- `uint8_t _first_usable_gyro` of `AP_InertialSensor` (`AP_InertialSensor/AP_InertialSensor.h:723`). -/
  _first_usable_gyro : UInt8 := (0 : UInt8)
  /-- `uint8_t _first_usable_accel` of `AP_InertialSensor` (`AP_InertialSensor/AP_InertialSensor.h:724`). -/
  _first_usable_accel : UInt8 := (0 : UInt8)
  /-- `uint8_t _primary` of `AP_InertialSensor` (`AP_InertialSensor/AP_InertialSensor.h:727`). -/
  _primary : UInt8 := (0 : UInt8)
  /-- `uint8_t _gyro_wait_mask` of `AP_InertialSensor` (`AP_InertialSensor/AP_InertialSensor.h:731`). -/
  _gyro_wait_mask : UInt8 := (0 : UInt8)
  /-- `uint8_t _accel_wait_mask` of `AP_InertialSensor` (`AP_InertialSensor/AP_InertialSensor.h:732`). -/
  _accel_wait_mask : UInt8 := (0 : UInt8)
  /-- `uint32_t _log_raw_bit` of `AP_InertialSensor` (`AP_InertialSensor/AP_InertialSensor.h:735`). -/
  _log_raw_bit : UInt32 := (0 : UInt32)
  /-- `bool _have_sample : 1` of `AP_InertialSensor` (`AP_InertialSensor/AP_InertialSensor.h:738`). -/
  _have_sample : Bool := false
  /-- `bool _backends_detected : 1` of `AP_InertialSensor` (`AP_InertialSensor/AP_InertialSensor.h:740`). -/
  _backends_detected : Bool := false
  /-- `bool _calibrating_accel` of `AP_InertialSensor` (`AP_InertialSensor/AP_InertialSensor.h:743`). -/
  _calibrating_accel : Bool := false
  /-- `bool _calibrating_gyro` of `AP_InertialSensor` (`AP_InertialSensor/AP_InertialSensor.h:744`). -/
  _calibrating_gyro : Bool := false
  /-- `bool _trimming_accel` of `AP_InertialSensor` (`AP_InertialSensor/AP_InertialSensor.h:745`). -/
  _trimming_accel : Bool := false
  /-- `float _delta_time` of `AP_InertialSensor` (`AP_InertialSensor/AP_InertialSensor.h:748`). -/
  _delta_time : Binary32 := (Binary32.ofBits 0x00000000 /- 0.0 -/)
  /-- `uint32_t _last_sample_usec` of `AP_InertialSensor` (`AP_InertialSensor/AP_InertialSensor.h:751`). -/
  _last_sample_usec : UInt32 := (0 : UInt32)
  /-- `uint32_t _next_sample_usec` of `AP_InertialSensor` (`AP_InertialSensor/AP_InertialSensor.h:754`). -/
  _next_sample_usec : UInt32 := (0 : UInt32)
  /-- `uint32_t _sample_period_usec` of `AP_InertialSensor` (`AP_InertialSensor/AP_InertialSensor.h:757`). -/
  _sample_period_usec : UInt32 := (0 : UInt32)
  /-- `uint32_t _last_update_usec` of `AP_InertialSensor` (`AP_InertialSensor/AP_InertialSensor.h:760`). -/
  _last_update_usec : UInt32 := (0 : UInt32)
  /-- `bool _gyro_healthy[3]` of `AP_InertialSensor` (`AP_InertialSensor/AP_InertialSensor.h:763`). -/
  _gyro_healthy : Array Bool := Array.replicate 3 false
  /-- `bool _accel_healthy[3]` of `AP_InertialSensor` (`AP_InertialSensor/AP_InertialSensor.h:764`). -/
  _accel_healthy : Array Bool := Array.replicate 3 false
  /-- `uint32_t _accel_error_count[3]` of `AP_InertialSensor` (`AP_InertialSensor/AP_InertialSensor.h:766`). -/
  _accel_error_count : Array UInt32 := Array.replicate 3 (0 : UInt32)
  /-- `uint32_t _gyro_error_count[3]` of `AP_InertialSensor` (`AP_InertialSensor/AP_InertialSensor.h:767`). -/
  _gyro_error_count : Array UInt32 := Array.replicate 3 (0 : UInt32)
  /-- `uint32_t _accel_clip_count[3]` of `AP_InertialSensor` (`AP_InertialSensor/AP_InertialSensor.h:770`). -/
  _accel_clip_count : Array UInt32 := Array.replicate 3 (0 : UInt32)
  /-- `LowPassFilterVector3f _accel_vibe_floor_filter[3]` of `AP_InertialSensor` (`AP_InertialSensor/AP_InertialSensor.h:771`). -/
  _accel_vibe_floor_filter : Array LowPassFilter_Vector3_float.State := Array.replicate 3 LowPassFilter_Vector3_float.init_void
  /-- `LowPassFilterVector3f _accel_vibe_filter[3]` of `AP_InertialSensor` (`AP_InertialSensor/AP_InertialSensor.h:772`). -/
  _accel_vibe_filter : Array LowPassFilter_Vector3_float.State := Array.replicate 3 LowPassFilter_Vector3_float.init_void
  /-- `struct PeakHoldState _peak_hold_state` of `AP_InertialSensor` (`AP_InertialSensor/AP_InertialSensor.h:778`). -/
  _peak_hold_state : AP_InertialSensor.PeakHoldState := {}
  /-- `AP_Float _still_threshold` of `AP_InertialSensor` (`AP_InertialSensor/AP_InertialSensor.h:781`). -/
  _still_threshold : AP_ParamT_float_4.State := {}
  /-- `AP_Int8 _acc_body_aligned` of `AP_InertialSensor` (`AP_InertialSensor/AP_InertialSensor.h:784`). -/
  _acc_body_aligned : AP_ParamT_signed_char_1.State := {}
  /-- `AP_Int8 _trim_option` of `AP_InertialSensor` (`AP_InertialSensor/AP_InertialSensor.h:785`). -/
  _trim_option : AP_ParamT_signed_char_1.State := {}
  /-- `AP_AccelCal * _acal` of `AP_InertialSensor` (`AP_InertialSensor/AP_InertialSensor.h:788`). -/
  _acal : WPtr := WPtr.null
  /-- `AccelCalibrator * _accel_calibrator` of `AP_InertialSensor` (`AP_InertialSensor/AP_InertialSensor.h:790`). -/
  _accel_calibrator : WPtr := WPtr.null
  /-- `Vector3f _trim_rad` of `AP_InertialSensor` (`AP_InertialSensor/AP_InertialSensor.h:799`). -/
  _trim_rad : Vector3f.State := {}
  /-- `bool _new_trim` of `AP_InertialSensor` (`AP_InertialSensor/AP_InertialSensor.h:800`). -/
  _new_trim : Bool := false
  /-- `bool _accel_cal_requires_reboot` of `AP_InertialSensor` (`AP_InertialSensor/AP_InertialSensor.h:802`). -/
  _accel_cal_requires_reboot : Bool := false
  /-- `uint32_t _accel_startup_error_count[3]` of `AP_InertialSensor` (`AP_InertialSensor/AP_InertialSensor.h:805`). -/
  _accel_startup_error_count : Array UInt32 := Array.replicate 3 (0 : UInt32)
  /-- `uint32_t _gyro_startup_error_count[3]` of `AP_InertialSensor` (`AP_InertialSensor/AP_InertialSensor.h:806`). -/
  _gyro_startup_error_count : Array UInt32 := Array.replicate 3 (0 : UInt32)
  /-- `bool _startup_error_counts_set` of `AP_InertialSensor` (`AP_InertialSensor/AP_InertialSensor.h:807`). -/
  _startup_error_counts_set : Bool := false
  /-- `uint32_t _startup_ms` of `AP_InertialSensor` (`AP_InertialSensor/AP_InertialSensor.h:808`). -/
  _startup_ms : UInt32 := (0 : UInt32)
  /-- `AP_UInt16 raw_logging_options` of `AP_InertialSensor` (`AP_InertialSensor/AP_InertialSensor.h:863`). -/
  raw_logging_options : AP_ParamT_unsigned_short_2.State := {}
  /-- `bool fast_rate_buffer_enabled` of `AP_InertialSensor` (`AP_InertialSensor/AP_InertialSensor.h:870`). -/
  fast_rate_buffer_enabled : Bool := false
  /-- `uint8_t _first_onboard_imu_instance` of `AP_InertialSensor` (`AP_InertialSensor/AP_InertialSensor.h:895`). -/
  _first_onboard_imu_instance : UInt8 := (0 : UInt8)
deriving Inhabited

/-- Values C++ `AP_InertialSensor` reads from objects outside the translation (--boundary): one field per distinct read, in first-use order. -/
structure Inputs where
  /-- `_gyro_id(_gyro_count).load()` (first read at `AP_InertialSensor/AP_InertialSensor.cpp:768`). -/
  gyro_id__gyro_count_loaded : Bool := false
  /-- `_accel_id(_accel_count).load()` (first read at `AP_InertialSensor/AP_InertialSensor.cpp:836`). -/
  accel_id__accel_count_loaded : Bool := false
  /-- `hal.util.was_watchdog_reset()` (first read at `AP_InertialSensor/AP_InertialSensor.cpp:2732`). -/
  was_watchdog_reset : Bool := false
deriving Inhabited

end AP_InertialSensor

namespace AP_InertialSensor_SITL

/-- State of C++ `AP_InertialSensor_SITL` (`AP_InertialSensor/AP_InertialSensor_SITL.h:15-63`): its data members; base classes flattened, base first: `AP_InertialSensor_Backend`. -/
structure State where
  /-- `float _clip_limit` of `AP_InertialSensor_Backend` (`AP_InertialSensor/AP_InertialSensor_Backend.h:194`). -/
  _clip_limit : Binary32 := ((Binary32.ofBits 0x41800000 /- 16.0f -/) - (Binary32.ofBits 0x3f000000 /- 0.5f -/)) * (Binary32.ofBits 0x411ce80a /- 9.80665016 -/)
  /-- `uint8_t gyro_instance` of `AP_InertialSensor_Backend` (`AP_InertialSensor/AP_InertialSensor_Backend.h:198`). -/
  gyro_instance : UInt8 := Int8.toUInt8 (Int32.toInt8 ((3 : Int32) + (0 : Int32)))
  /-- `uint8_t accel_instance` of `AP_InertialSensor_Backend` (`AP_InertialSensor/AP_InertialSensor_Backend.h:199`). -/
  accel_instance : UInt8 := Int8.toUInt8 (Int32.toInt8 ((3 : Int32) + (0 : Int32)))
  /-- `bool is_primary` of `AP_InertialSensor_Backend` (`AP_InertialSensor/AP_InertialSensor_Backend.h:200`). -/
  is_primary : Bool := true
  /-- `uint32_t last_primary_update_us` of `AP_InertialSensor_Backend` (`AP_InertialSensor/AP_InertialSensor_Backend.h:201`). -/
  last_primary_update_us : UInt32 := (0 : UInt32)
  /-- `int16_t _id` of `AP_InertialSensor_Backend` (`AP_InertialSensor/AP_InertialSensor_Backend.h:309`). -/
  _id : Int16 := Int32.toInt16 (-(1 : Int32))
  /-- `uint16_t _last_accel_filter_hz` of `AP_InertialSensor_Backend` (`AP_InertialSensor/AP_InertialSensor_Backend.h:336`). -/
  _last_accel_filter_hz : UInt16 := (0 : UInt16)
  /-- `uint16_t _last_gyro_filter_hz` of `AP_InertialSensor_Backend` (`AP_InertialSensor/AP_InertialSensor_Backend.h:337`). -/
  _last_gyro_filter_hz : UInt16 := (0 : UInt16)
  /-- `SITL::SIM * sitl` of `AP_InertialSensor_SITL` (`AP_InertialSensor/AP_InertialSensor_SITL.h:44`). -/
  sitl : WPtr := WPtr.null
  /-- `const uint16_t gyro_sample_hz` of `AP_InertialSensor_SITL` (`AP_InertialSensor/AP_InertialSensor_SITL.h:46`). -/
  gyro_sample_hz : UInt16 := (0 : UInt16)
  /-- `const uint16_t accel_sample_hz` of `AP_InertialSensor_SITL` (`AP_InertialSensor/AP_InertialSensor_SITL.h:47`). -/
  accel_sample_hz : UInt16 := (0 : UInt16)
  /-- `uint64_t next_gyro_sample` of `AP_InertialSensor_SITL` (`AP_InertialSensor/AP_InertialSensor_SITL.h:49`). -/
  next_gyro_sample : UInt64 := (0 : UInt64)
  /-- `uint64_t next_accel_sample` of `AP_InertialSensor_SITL` (`AP_InertialSensor/AP_InertialSensor_SITL.h:50`). -/
  next_accel_sample : UInt64 := (0 : UInt64)
  /-- `uint64_t flightaxis_imu_frame_num` of `AP_InertialSensor_SITL` (`AP_InertialSensor/AP_InertialSensor_SITL.h:51`). -/
  flightaxis_imu_frame_num : UInt64 := (0 : UInt64)
  /-- `float gyro_time` of `AP_InertialSensor_SITL` (`AP_InertialSensor/AP_InertialSensor_SITL.h:52`). -/
  gyro_time : Binary32 := (Binary32.ofBits 0x00000000 /- 0.0 -/)
  /-- `float accel_time` of `AP_InertialSensor_SITL` (`AP_InertialSensor/AP_InertialSensor_SITL.h:53`). -/
  accel_time : Binary32 := (Binary32.ofBits 0x00000000 /- 0.0 -/)
  /-- `float gyro_motor_phase[32]` of `AP_InertialSensor_SITL` (`AP_InertialSensor/AP_InertialSensor_SITL.h:54`). -/
  gyro_motor_phase : Array Binary32 := Array.replicate 32 (Binary32.ofBits 0x00000000 /- 0.0 -/)
  /-- `float accel_motor_phase[32]` of `AP_InertialSensor_SITL` (`AP_InertialSensor/AP_InertialSensor_SITL.h:55`). -/
  accel_motor_phase : Array Binary32 := Array.replicate 32 (Binary32.ofBits 0x00000000 /- 0.0 -/)
  /-- `uint32_t temp_start_ms` of `AP_InertialSensor_SITL` (`AP_InertialSensor/AP_InertialSensor_SITL.h:56`). -/
  temp_start_ms : UInt32 := (0 : UInt32)
  /-- `int gyro_fd` of `AP_InertialSensor_SITL` (`AP_InertialSensor/AP_InertialSensor_SITL.h:58`). -/
  gyro_fd : Int32 := -(1 : Int32)
  /-- `int accel_fd` of `AP_InertialSensor_SITL` (`AP_InertialSensor/AP_InertialSensor_SITL.h:59`). -/
  accel_fd : Int32 := -(1 : Int32)
deriving Inhabited

/-- Values C++ `AP_InertialSensor_SITL` reads from objects outside the translation (--boundary): one field per distinct read, in first-use order. -/
structure Inputs where
  /-- `hal.util.get_soft_armed()` (first read at `AP_InertialSensor/AP_InertialSensor_Backend.cpp:72`). -/
  get_soft_armed : Bool := false
  /-- `hal.opticalflow_set` (first read at `AP_InertialSensor/AP_InertialSensor_Backend.cpp:342`). -/
  opticalflow_set : Bool := false
deriving Inhabited

end AP_InertialSensor_SITL

namespace AP_InertialSensor

/-- C++ `void AP_InertialSensor::set_board_orientation(enum Rotation orientation)`, `AP_InertialSensor/AP_InertialSensor.h:272-274`. -/
def set_board_orientation (s : State) (orientation : Rotation) : State := Id.run do
  let mut s := s
  s := { s with _board_orientation := orientation }
  return s

end AP_InertialSensor

namespace AP_InertialSensor

/-- C++ `uint8_t AP_InertialSensor::get_accel_count() const`, `AP_InertialSensor/AP_InertialSensor.h:199`. -/
def get_accel_count (s : State) : UInt8 := Id.run do
  return Int8.toUInt8 (Int32.toInt8 (Estimator_lib.MIN_int32_t_uint8_t ((3 : Int32) + (0 : Int32)) s._accel_count))

/-- C++ `uint8_t AP_InertialSensor::get_gyro_count() const`, `AP_InertialSensor/AP_InertialSensor.h:189`. -/
def get_gyro_count (s : State) : UInt8 := Id.run do
  return Int8.toUInt8 (Int32.toInt8 (Estimator_lib.MIN_int32_t_uint8_t ((3 : Int32) + (0 : Int32)) s._gyro_count))

/-- C++ `uint16_t AP_InertialSensor::get_loop_rate_hz() const`, `AP_InertialSensor/AP_InertialSensor.h:277`. -/
def get_loop_rate_hz (s : State) : UInt16 := Id.run do
  return s._loop_rate

/-- C++ `float AP_InertialSensor::get_loop_delta_t() const`, `AP_InertialSensor/AP_InertialSensor.h:280`. -/
def get_loop_delta_t (s : State) : Binary32 := Id.run do
  return s._loop_delta_t

/-- C++ `uint8_t AP_InertialSensor::get_first_usable_gyro() const`, `AP_InertialSensor/AP_InertialSensor.h:285`. -/
def get_first_usable_gyro (s : State) : UInt8 := Id.run do
  return s._first_usable_gyro

/-- C++ `uint8_t AP_InertialSensor::get_first_usable_accel() const`, `AP_InertialSensor/AP_InertialSensor.h:284`. -/
def get_first_usable_accel (s : State) : UInt8 := Id.run do
  return s._first_usable_accel

/-- C++ `bool AP_InertialSensor::get_accel_health(uint8_t instance) const`, `AP_InertialSensor/AP_InertialSensor.h:195`. -/
def get_accel_health_uint8_t (s : State) («instance» : UInt8) : Bool := Id.run do
  return if UInt32.toInt32 (UInt8.toUInt32 «instance») < UInt32.toInt32 (UInt8.toUInt32 s._accel_count) then s._accel_healthy[UInt8.toNat «instance»]! else false

/-- C++ `bool AP_InertialSensor::use_accel(uint8_t instance) const`, `AP_InertialSensor/AP_InertialSensor.cpp:1699-1706`. -/
def use_accel (s : State) («instance» : UInt8) : Bool := Id.run do
  if UInt32.toInt32 (UInt8.toUInt32 «instance») ≥ ((3 : Int32) + (0 : Int32)) then
    return false
  let mut t'3 := get_accel_health_uint8_t s «instance»
  if t'3 then
    let t'1 := «instance»
    let t'2 := t'1
    t'3 := AP_ParamT_signed_char_1.op_to_signed_char s._use_old_param[UInt8.toNat t'2]! != (0 : Int8)
  return t'3

/-- C++ `bool AP_InertialSensor::get_gyro_health(uint8_t instance) const`, `AP_InertialSensor/AP_InertialSensor.h:185`. -/
def get_gyro_health_uint8_t (s : State) («instance» : UInt8) : Bool := Id.run do
  return if UInt32.toInt32 (UInt8.toUInt32 «instance») < UInt32.toInt32 (UInt8.toUInt32 s._gyro_count) then s._gyro_healthy[UInt8.toNat «instance»]! else false

/-- C++ `bool AP_InertialSensor::use_gyro(uint8_t instance) const`, `AP_InertialSensor/AP_InertialSensor.cpp:1493-1500`. -/
def use_gyro (s : State) («instance» : UInt8) : Bool := Id.run do
  if UInt32.toInt32 (UInt8.toUInt32 «instance») ≥ ((3 : Int32) + (0 : Int32)) then
    return false
  let mut t'3 := get_gyro_health_uint8_t s «instance»
  if t'3 then
    let t'1 := «instance»
    let t'2 := t'1
    t'3 := AP_ParamT_signed_char_1.op_to_signed_char s._use_old_param[UInt8.toNat t'2]! != (0 : Int8)
  return t'3

/-- C++ `float AP_InertialSensor::get_delta_time() const`, `AP_InertialSensor/AP_InertialSensor.h:253`. -/
def get_delta_time (s : State) : Binary32 := Id.run do
  return Estimator_lib.MIN_float2 s._delta_time s._loop_delta_t_max

/-- C++ `bool AP_InertialSensor::get_delta_velocity(uint8_t i, Vector3f & delta_velocity, float & delta_velocity_dt) const`, `AP_InertialSensor/AP_InertialSensor.cpp:2194-2211`. -/
def get_delta_velocity_uint8_t_Vector3f_float (s : State) (i : UInt8) (delta_velocity : Vector3f.State) (delta_velocity_dt : Binary32) : Vector3f.State × Binary32 × Bool := Id.run do
  let mut delta_velocity := delta_velocity
  let mut delta_velocity_dt := delta_velocity_dt
  if s._delta_velocity_valid[UInt8.toNat i]! then
    delta_velocity_dt := s._delta_velocity_dt[UInt8.toNat i]!
  else
    delta_velocity_dt := get_delta_time s
  delta_velocity_dt := Estimator_lib.MIN_float2 delta_velocity_dt s._loop_delta_t_max
  if s._delta_velocity_valid[UInt8.toNat i]! then
    delta_velocity := s._delta_velocity[UInt8.toNat i]!
    return (delta_velocity, delta_velocity_dt, true)
  else if get_accel_health_uint8_t s i then
    let t'1 := i
    delta_velocity := Vector3f.op_mul_float s._accel[UInt8.toNat t'1]! (get_delta_time s)
    return (delta_velocity, delta_velocity_dt, true)
  return (delta_velocity, delta_velocity_dt, false)

/-- C++ `bool AP_InertialSensor::get_delta_angle(uint8_t i, Vector3f & delta_angle, float & delta_angle_dt) const`, `AP_InertialSensor/AP_InertialSensor.cpp:2170-2189`. -/
def get_delta_angle_uint8_t_Vector3f_float (s : State) (i : UInt8) (delta_angle : Vector3f.State) (delta_angle_dt : Binary32) : Vector3f.State × Binary32 × Bool := Id.run do
  let mut delta_angle := delta_angle
  let mut delta_angle_dt := delta_angle_dt
  if s._delta_angle_valid[UInt8.toNat i]! && decide (s._delta_angle_dt[UInt8.toNat i]! > (Binary32.ofBits 0x00000000 /- 0 -/)) then
    delta_angle_dt := s._delta_angle_dt[UInt8.toNat i]!
  else
    delta_angle_dt := get_delta_time s
  delta_angle_dt := Estimator_lib.MIN_float2 delta_angle_dt s._loop_delta_t_max
  if s._delta_angle_valid[UInt8.toNat i]! then
    delta_angle := s._delta_angle[UInt8.toNat i]!
    return (delta_angle, delta_angle_dt, true)
  else if get_gyro_health_uint8_t s i then
    let t'1 := i
    delta_angle := Vector3f.op_mul_float s._gyro[UInt8.toNat t'1]! (get_delta_time s)
    return (delta_angle, delta_angle_dt, true)
  return (delta_angle, delta_angle_dt, false)

end AP_InertialSensor

namespace AP_InertialSensor_SITL

/-- C++ `uint8_t AP_InertialSensor_Backend::get_gyro_instance() const`, `AP_InertialSensor/AP_InertialSensor_Backend.h:124-126` (a member of `AP_InertialSensor_Backend`, translated for `AP_InertialSensor_SITL`). -/
def get_gyro_instance (s : State) : UInt8 := Id.run do
  return s.gyro_instance

end AP_InertialSensor_SITL

namespace AP_InertialSensor_SITL

/-- C++ `float AP_InertialSensor_Backend::gyro_bias_limit_rads() const`, `AP_InertialSensor/AP_InertialSensor_Backend.h:115-117` (a member of `AP_InertialSensor_Backend`, translated for `AP_InertialSensor_SITL`). -/
def gyro_bias_limit_rads : Binary32 := Id.run do
  return (Binary32.ofBits 0x3f000000 /- 0.5f -/)

end AP_InertialSensor_SITL

namespace AP_InertialSensor_SITL

/-- C++ `float AP_InertialSensor_Backend::gyro_bias_init_dps() const`, `AP_InertialSensor/AP_InertialSensor_Backend.h:120-122` (a member of `AP_InertialSensor_Backend`, translated for `AP_InertialSensor_SITL`). -/
def gyro_bias_init_dps : Binary32 := Id.run do
  return (Binary32.ofBits 0x40200000 /- 2.5f -/)

end AP_InertialSensor_SITL

namespace AP_InertialSensor

/-- C++ `uint32_t AP_InertialSensor::get_last_update_usec() const`, `AP_InertialSensor/AP_InertialSensor.h:370`. -/
def get_last_update_usec (s : State) : UInt32 := Id.run do
  return s._last_update_usec

end AP_InertialSensor

namespace AP_InertialSensor

/-- C++ `void AP_InertialSensor::set_primary(uint8_t instance)`, `AP_InertialSensor/AP_InertialSensor.cpp:1905-1908`. -/
def set_primary (s : State) («instance» : UInt8) : State := Id.run do
  let mut s := s
  s := { s with _primary := «instance» }
  return s

end AP_InertialSensor

namespace AP_InertialSensor

/-- C++ `bool AP_InertialSensor::get_delta_angle(Vector3f & delta_angle, float & delta_angle_dt) const`, `AP_InertialSensor/AP_InertialSensor.h:167-169`. -/
def get_delta_angle_Vector3f_float (s : State) (delta_angle : Vector3f.State) (delta_angle_dt : Binary32) : Vector3f.State × Binary32 × Bool := Id.run do
  let mut delta_angle := delta_angle
  let mut delta_angle_dt := delta_angle_dt
  let (t'1, t'2, t'3) := get_delta_angle_uint8_t_Vector3f_float s s._first_usable_gyro delta_angle delta_angle_dt
  delta_angle := t'1
  delta_angle_dt := t'2
  return (delta_angle, delta_angle_dt, t'3)

/-- C++ `const Vector3f & AP_InertialSensor::get_gyro(uint8_t i) const`, `AP_InertialSensor/AP_InertialSensor.h:158`. -/
def get_gyro_uint8_t (s : State) (i : UInt8) : Vector3f.State := Id.run do
  return s._gyro[UInt8.toNat i]!

/-- C++ `const Vector3f & AP_InertialSensor::get_gyro() const`, `AP_InertialSensor/AP_InertialSensor.h:159`. -/
def get_gyro_void (s : State) : Vector3f.State := Id.run do
  return get_gyro_uint8_t s s._first_usable_gyro

end AP_InertialSensor

namespace AP_InertialSensor

/-- C++ `bool AP_InertialSensor::get_accel_health() const`, `AP_InertialSensor/AP_InertialSensor.h:196`. -/
def get_accel_health_void (s : State) : Bool := Id.run do
  return get_accel_health_uint8_t s s._first_usable_accel

/-- C++ `bool AP_InertialSensor::get_gyro_health() const`, `AP_InertialSensor/AP_InertialSensor.h:186`. -/
def get_gyro_health_void (s : State) : Bool := Id.run do
  return get_gyro_health_uint8_t s s._first_usable_gyro

/-- C++ `bool AP_InertialSensor::healthy() const`, `AP_InertialSensor/AP_InertialSensor.h:282`. -/
def healthy (s : State) : Bool := Id.run do
  return get_gyro_health_void s && get_accel_health_void s

/-- C++ `float AP_InertialSensor::get_gyro_drift_rate() const`, `AP_InertialSensor/AP_InertialSensor.h:257`. -/
def get_gyro_drift_rate : Binary32 := Id.run do
  return Estimator_lib.radians_float ((Binary32.ofBits 0x3f000000 /- 0.5f -/) / (Binary32.ofBits 0x42700000 /- 60 -/))

end AP_InertialSensor

namespace AP_InertialSensor

/-- C++ `bool AP_InertialSensor::_add_backend(AP_InertialSensor_Backend * backend)`, `AP_InertialSensor/AP_InertialSensor.cpp:1122-1133`. -/
def _add_backend (s : State) (backend : WPtr) : State × Bool := Id.run do
  let mut s := s
  if !(backend != WPtr.null) then
    return (s, false)
  if UInt32.toInt32 (UInt8.toUInt32 s._backend_count) == (2 : Int32) * ((3 : Int32) + (0 : Int32)) then
    pure ()  -- C++ `AP_HAL::panic(...)`: left out (--drop)
  let t'1 := s._backend_count
  s := { s with _backend_count := s._backend_count + (1 : UInt8) }
  s := { s with _backends := s._backends.set! (UInt8.toNat t'1) backend }
  return (s, true)

end AP_InertialSensor

namespace AP_InertialSensor_SITL

/-- C++ `AP_InertialSensor_Backend::AP_InertialSensor_Backend(AP_InertialSensor & imu)`, `AP_InertialSensor/AP_InertialSensor_Backend.cpp:23-26` (a member of `AP_InertialSensor_Backend`, translated for `AP_InertialSensor_SITL`). -/
def AP_InertialSensor_Backend.init (s : State) : State := Id.run do
  let mut s := s
  return s

end AP_InertialSensor_SITL

namespace AP_InertialSensor_Backend

/-- C++ `enum AP_InertialSensor_Backend::DevTypes`, `AP_InertialSensor/AP_InertialSensor_Backend.h:140-184`. -/
inductive DevTypes where
  | DEVTYPE_BMI160
  | DEVTYPE_L3G4200D
  | DEVTYPE_ACC_LSM303D
  | DEVTYPE_ACC_BMA180
  | DEVTYPE_ACC_MPU6000
  | DEVTYPE_ACC_MPU9250
  | DEVTYPE_ACC_IIS328DQ
  | DEVTYPE_ACC_LSM9DS1
  | DEVTYPE_GYR_MPU6000
  | DEVTYPE_GYR_L3GD20
  | DEVTYPE_GYR_MPU9250
  | DEVTYPE_GYR_I3G4250D
  | DEVTYPE_GYR_LSM9DS1
  | DEVTYPE_INS_ICM20789
  | DEVTYPE_INS_ICM20689
  | DEVTYPE_INS_BMI055
  | DEVTYPE_SITL
  | DEVTYPE_INS_BMI088
  | DEVTYPE_INS_ICM20948
  | DEVTYPE_INS_ICM20648
  | DEVTYPE_INS_ICM20649
  | DEVTYPE_INS_ICM20602
  | DEVTYPE_INS_ICM20601
  | DEVTYPE_INS_ADIS1647X
  | DEVTYPE_SERIAL
  | DEVTYPE_INS_ICM40609
  | DEVTYPE_INS_ICM42688
  | DEVTYPE_INS_ICM42605
  | DEVTYPE_INS_ICM40605
  | DEVTYPE_INS_IIM42652
  | DEVTYPE_BMI270
  | DEVTYPE_INS_BMI085
  | DEVTYPE_INS_ICM42670
  | DEVTYPE_INS_ICM45686
  | DEVTYPE_INS_SCHA63T
  | DEVTYPE_INS_IIM42653
  | DEVTYPE_INS_LSM6DSV16X
  | DEVTYPE_INS_ASM330
  | DEVTYPE_INS_ADIS16607
  | DEVTYPE_INS_ZEROONE_FPGA_SCH16T
  | DEVTYPE_INS_LSM6DSV32X
  | DEVTYPE_INS_LSM6DSK320X
  | DEVTYPE_INS_ICM56686
deriving DecidableEq, Inhabited

/-- The value of each enumerator of `AP_InertialSensor_Backend::DevTypes` (underlying type `uint32_t`). -/
def DevTypes.toInt : DevTypes → UInt32
  | .DEVTYPE_BMI160 => (9 : UInt32)
  | .DEVTYPE_L3G4200D => (16 : UInt32)
  | .DEVTYPE_ACC_LSM303D => (17 : UInt32)
  | .DEVTYPE_ACC_BMA180 => (18 : UInt32)
  | .DEVTYPE_ACC_MPU6000 => (19 : UInt32)
  | .DEVTYPE_ACC_MPU9250 => (22 : UInt32)
  | .DEVTYPE_ACC_IIS328DQ => (23 : UInt32)
  | .DEVTYPE_ACC_LSM9DS1 => (24 : UInt32)
  | .DEVTYPE_GYR_MPU6000 => (33 : UInt32)
  | .DEVTYPE_GYR_L3GD20 => (34 : UInt32)
  | .DEVTYPE_GYR_MPU9250 => (36 : UInt32)
  | .DEVTYPE_GYR_I3G4250D => (37 : UInt32)
  | .DEVTYPE_GYR_LSM9DS1 => (38 : UInt32)
  | .DEVTYPE_INS_ICM20789 => (39 : UInt32)
  | .DEVTYPE_INS_ICM20689 => (40 : UInt32)
  | .DEVTYPE_INS_BMI055 => (41 : UInt32)
  | .DEVTYPE_SITL => (42 : UInt32)
  | .DEVTYPE_INS_BMI088 => (43 : UInt32)
  | .DEVTYPE_INS_ICM20948 => (44 : UInt32)
  | .DEVTYPE_INS_ICM20648 => (45 : UInt32)
  | .DEVTYPE_INS_ICM20649 => (46 : UInt32)
  | .DEVTYPE_INS_ICM20602 => (47 : UInt32)
  | .DEVTYPE_INS_ICM20601 => (48 : UInt32)
  | .DEVTYPE_INS_ADIS1647X => (49 : UInt32)
  | .DEVTYPE_SERIAL => (50 : UInt32)
  | .DEVTYPE_INS_ICM40609 => (51 : UInt32)
  | .DEVTYPE_INS_ICM42688 => (52 : UInt32)
  | .DEVTYPE_INS_ICM42605 => (53 : UInt32)
  | .DEVTYPE_INS_ICM40605 => (54 : UInt32)
  | .DEVTYPE_INS_IIM42652 => (55 : UInt32)
  | .DEVTYPE_BMI270 => (56 : UInt32)
  | .DEVTYPE_INS_BMI085 => (57 : UInt32)
  | .DEVTYPE_INS_ICM42670 => (58 : UInt32)
  | .DEVTYPE_INS_ICM45686 => (59 : UInt32)
  | .DEVTYPE_INS_SCHA63T => (60 : UInt32)
  | .DEVTYPE_INS_IIM42653 => (61 : UInt32)
  | .DEVTYPE_INS_LSM6DSV16X => (62 : UInt32)
  | .DEVTYPE_INS_ASM330 => (63 : UInt32)
  | .DEVTYPE_INS_ADIS16607 => (64 : UInt32)
  | .DEVTYPE_INS_ZEROONE_FPGA_SCH16T => (65 : UInt32)
  | .DEVTYPE_INS_LSM6DSV32X => (66 : UInt32)
  | .DEVTYPE_INS_LSM6DSK320X => (67 : UInt32)
  | .DEVTYPE_INS_ICM56686 => (68 : UInt32)

end AP_InertialSensor_Backend

namespace AP_InertialSensor_SITL

-- not read in the Lean: banner_len
set_option linter.unusedVariables false in
/-- C++ `bool AP_InertialSensor_Backend::get_output_banner(char * banner, uint8_t banner_len)`, `AP_InertialSensor/AP_InertialSensor_Backend.h:91` (a member of `AP_InertialSensor_Backend`, translated for `AP_InertialSensor_SITL`). -/
def get_output_banner (banner_len : UInt8) : Bool := Id.run do
  return false

end AP_InertialSensor_SITL

namespace AP_InertialSensor

/-- C++ `AP_InertialSensor::AP_InertialSensor()`, `AP_InertialSensor/AP_InertialSensor.cpp:713-733`. -/
def construct : State := Id.run do
  let mut s : State := {}
  s := { s with _board_orientation := Rotation.ROTATION_NONE }
  s := { s with _log_raw_bit := Int32.toUInt32 (-(1 : Int32)) }
  s := { s with _trim_rad := Vector3f.init_void }
  if false /- C++ `_singleton` -/ then
    pure ()  -- C++ `AP_HAL::panic(...)`: left out (--drop)
  pure ()  -- C++ `_singleton = this`: the pointer is the class's one World object (--world)
  let t'1 := (Binary32.ofBits 0x00000000 /- (float)0 -/)
  s := { s with _gyro_offset_old_param := s._gyro_offset_old_param.set! 0 ({ s._gyro_offset_old_param[0]! with _value := ({ x := t'1, y := t'1, z := t'1 } : Vector3f.State) }) }
  let t'2 := (Binary32.ofBits 0x00000000 /- (float)0 -/)
  s := { s with _gyro_offset_old_param := s._gyro_offset_old_param.set! 1 ({ s._gyro_offset_old_param[1]! with _value := ({ x := t'2, y := t'2, z := t'2 } : Vector3f.State) }) }
  let t'3 := (Binary32.ofBits 0x00000000 /- (float)0 -/)
  s := { s with _gyro_offset_old_param := s._gyro_offset_old_param.set! 2 ({ s._gyro_offset_old_param[2]! with _value := ({ x := t'3, y := t'3, z := t'3 } : Vector3f.State) }) }
  let t'4 := (Binary32.ofBits 0x3f800000 /- (float)1 -/)
  s := { s with _accel_scale_old_param := s._accel_scale_old_param.set! 0 ({ s._accel_scale_old_param[0]! with _value := ({ x := t'4, y := t'4, z := t'4 } : Vector3f.State) }) }
  let t'5 := (Binary32.ofBits 0x00000000 /- (float)0 -/)
  s := { s with _accel_offset_old_param := s._accel_offset_old_param.set! 0 ({ s._accel_offset_old_param[0]! with _value := ({ x := t'5, y := t'5, z := t'5 } : Vector3f.State) }) }
  let t'6 := (Binary32.ofBits 0x3f800000 /- (float)1 -/)
  s := { s with _accel_scale_old_param := s._accel_scale_old_param.set! 1 ({ s._accel_scale_old_param[1]! with _value := ({ x := t'6, y := t'6, z := t'6 } : Vector3f.State) }) }
  let t'7 := (Binary32.ofBits 0x00000000 /- (float)0 -/)
  s := { s with _accel_offset_old_param := s._accel_offset_old_param.set! 1 ({ s._accel_offset_old_param[1]! with _value := ({ x := t'7, y := t'7, z := t'7 } : Vector3f.State) }) }
  let t'8 := (Binary32.ofBits 0x3f800000 /- (float)1 -/)
  s := { s with _accel_scale_old_param := s._accel_scale_old_param.set! 2 ({ s._accel_scale_old_param[2]! with _value := ({ x := t'8, y := t'8, z := t'8 } : Vector3f.State) }) }
  let t'9 := (Binary32.ofBits 0x00000000 /- (float)0 -/)
  s := { s with _accel_offset_old_param := s._accel_offset_old_param.set! 2 ({ s._accel_offset_old_param[2]! with _value := ({ x := t'9, y := t'9, z := t'9 } : Vector3f.State) }) }
  s := { s with _gyro_filter_cutoff._value := Binary32.toInt16 (Binary32.ofBits 0x41a00000 /- (float)20 -/) }
  s := { s with _accel_filter_cutoff._value := Binary32.toInt16 (Binary32.ofBits 0x41a00000 /- (float)20 -/) }
  s := { s with _use_old_param := s._use_old_param.set! 0 ({ s._use_old_param[0]! with _value := Binary32.toInt8 (Binary32.ofBits 0x3f800000 /- (float)1 -/) }) }
  s := { s with _use_old_param := s._use_old_param.set! 1 ({ s._use_old_param[1]! with _value := Binary32.toInt8 (Binary32.ofBits 0x3f800000 /- (float)1 -/) }) }
  s := { s with _use_old_param := s._use_old_param.set! 2 ({ s._use_old_param[2]! with _value := Binary32.toInt8 (Binary32.ofBits 0x3f800000 /- (float)1 -/) }) }
  s := { s with _still_threshold._value := (Binary32.ofBits 0x40200000 /- 2.5 -/) }
  s := { s with _gyro_cal_timing._value := Binary32.toInt8 (Binary32.ofBits 0x3f800000 /- (float)1 -/) }
  s := { s with _trim_option._value := Binary32.toInt8 (Binary32.ofBits 0x3f800000 /- (float)1 -/) }
  s := { s with _acc_body_aligned._value := Binary32.toInt8 (Binary32.ofBits 0x40000000 /- (float)2 -/) }
  let t'10 := (Binary32.ofBits 0x00000000 /- 0 -/)
  s := { s with _accel_pos_old_param := s._accel_pos_old_param.set! 0 ({ s._accel_pos_old_param[0]! with _value := ({ x := t'10, y := t'10, z := t'10 } : Vector3f.State) }) }
  let t'11 := (Binary32.ofBits 0x00000000 /- 0 -/)
  s := { s with _accel_pos_old_param := s._accel_pos_old_param.set! 1 ({ s._accel_pos_old_param[1]! with _value := ({ x := t'11, y := t'11, z := t'11 } : Vector3f.State) }) }
  let t'12 := (Binary32.ofBits 0x00000000 /- 0 -/)
  s := { s with _accel_pos_old_param := s._accel_pos_old_param.set! 2 ({ s._accel_pos_old_param[2]! with _value := ({ x := t'12, y := t'12, z := t'12 } : Vector3f.State) }) }
  s := { s with _gyro_id_old_param := s._gyro_id_old_param.set! 0 ({ s._gyro_id_old_param[0]! with _value := Int32.toUInt32 (Binary32.toInt32 (Binary32.ofBits 0x00000000 /- (float)0 -/)) }) }
  s := { s with _gyro_id_old_param := s._gyro_id_old_param.set! 1 ({ s._gyro_id_old_param[1]! with _value := Int32.toUInt32 (Binary32.toInt32 (Binary32.ofBits 0x00000000 /- (float)0 -/)) }) }
  s := { s with _gyro_id_old_param := s._gyro_id_old_param.set! 2 ({ s._gyro_id_old_param[2]! with _value := Int32.toUInt32 (Binary32.toInt32 (Binary32.ofBits 0x00000000 /- (float)0 -/)) }) }
  s := { s with _accel_id_old_param := s._accel_id_old_param.set! 0 ({ s._accel_id_old_param[0]! with _value := Int32.toUInt32 (Binary32.toInt32 (Binary32.ofBits 0x00000000 /- (float)0 -/)) }) }
  s := { s with _accel_id_old_param := s._accel_id_old_param.set! 1 ({ s._accel_id_old_param[1]! with _value := Int32.toUInt32 (Binary32.toInt32 (Binary32.ofBits 0x00000000 /- (float)0 -/)) }) }
  s := { s with _accel_id_old_param := s._accel_id_old_param.set! 2 ({ s._accel_id_old_param[2]! with _value := Int32.toUInt32 (Binary32.toInt32 (Binary32.ofBits 0x00000000 /- (float)0 -/)) }) }
  s := { s with _fast_sampling_mask._value := Int8.toUInt8 (Binary32.toInt8 (Binary32.ofBits 0x3f800000 /- (float)1 -/)) }
  s := { s with _enable_mask._value := Int8.toUInt8 (Binary32.toInt8 (Binary32.ofBits 0x42fe0000 /- (float)127 -/)) }
  s := { s with _fast_sampling_rate._value := Int8.toUInt8 (Binary32.toInt8 (Binary32.ofBits 0x00000000 /- (float)0 -/)) }
  s := { s with raw_logging_options._value := Int16.toUInt16 (Binary32.toInt16 (Binary32.ofBits 0x00000000 /- (float)0 -/)) }
  for i' in [0:3] do
    let i : UInt8 := Nat.toUInt8 i'
    s := { s with _gyro_cal_ok := s._gyro_cal_ok.set! (UInt8.toNat i) true }
  for i'2' in [0:3] do
    let i'2 : UInt8 := Nat.toUInt8 i'2'
    s := { s with _accel_vibe_floor_filter := s._accel_vibe_floor_filter.set! (UInt8.toNat i'2) (LowPassFilter_Vector3_float.set_cutoff_frequency s._accel_vibe_floor_filter[UInt8.toNat i'2]! (Binary32.ofBits 0x40a00000 /- 5 -/)) }
    s := { s with _accel_vibe_filter := s._accel_vibe_filter.set! (UInt8.toNat i'2) (LowPassFilter_Vector3_float.set_cutoff_frequency s._accel_vibe_filter[UInt8.toNat i'2]! (Binary32.ofBits 0x40000000 /- 2 -/)) }
  return s

end AP_InertialSensor

namespace AP_InertialSensor_SITL

/-! Not emitted, since they have no effect in the model (they write neither the state, the
parameters nor a reference parameter; e.g. they only save parameters):
- C++ `void AP_InertialSensor_Backend::_notify_new_accel_sensor_rate_sample(uint8_t instance, const Vector3f & accel)`, `AP_InertialSensor/AP_InertialSensor_Backend.cpp:727-740` (a member of `AP_InertialSensor_Backend`, translated for `AP_InertialSensor_SITL`).
- C++ `void AP_InertialSensor_Backend::log_accel_raw(uint8_t instance, const uint64_t sample_us, const Vector3f & accel)`, `AP_InertialSensor/AP_InertialSensor_Backend.cpp:757-775` (a member of `AP_InertialSensor_Backend`, translated for `AP_InertialSensor_SITL`).
- C++ `void AP_InertialSensor_Backend::_notify_new_gyro_sensor_rate_sample(uint8_t instance, const Vector3f & gyro)`, `AP_InertialSensor/AP_InertialSensor_Backend.cpp:742-755` (a member of `AP_InertialSensor_Backend`, translated for `AP_InertialSensor_SITL`).
- C++ `void AP_InertialSensor_Backend::save_gyro_window(const uint8_t instance, const Vector3f & gyro, uint8_t phase)`, `AP_InertialSensor/AP_InertialSensor_Backend.cpp:205-226` (a member of `AP_InertialSensor_Backend`, translated for `AP_InertialSensor_SITL`).
- C++ `void AP_InertialSensor_Backend::log_gyro_raw(uint8_t instance, const uint64_t sample_us, const Vector3f & raw_gyro, const Vector3f & filtered_gyro)`, `AP_InertialSensor/AP_InertialSensor_Backend.cpp:485-527` (a member of `AP_InertialSensor_Backend`, translated for `AP_InertialSensor_SITL`).
- C++ `void AP_InertialSensor_Backend::set_primary(bool _is_primary)`, `AP_InertialSensor/AP_InertialSensor_Backend.h:333` (a member of `AP_InertialSensor_Backend`, translated for `AP_InertialSensor_SITL`).
- C++ `void AP_InertialSensor_Backend::accumulate()`, `AP_InertialSensor/AP_InertialSensor_Backend.h:68` (a member of `AP_InertialSensor_Backend`, translated for `AP_InertialSensor_SITL`).
-/

end AP_InertialSensor_SITL

end Estimator_lib
