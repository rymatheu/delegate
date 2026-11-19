import ArduLean.Runtime.CFloat
import ArduLean.Estimator.libraries.AP_AccelCal.AP_AccelCal
import ArduLean.Estimator.libraries.AP_HAL.AP_HAL
import ArduLean.Estimator.libraries.AP_Math.AP_Math
import ArduLean.Estimator.World
import ArduLean.Estimator.libraries.Filter.Filter
import ArduLean.Estimator.libraries.AP_Param.AP_Param
import ArduLean.Estimator.libraries.SITL.SITL
import ArduLean.Estimator.libraries.AP_InertialSensor.AP_InertialSensor
import ArduLean.Estimator.World_2
import ArduLean.Estimator.World_3

/-!
ArduPilot `libraries/AP_InertialSensor`, part 2 of 3. Sources: `libraries/AP_InertialSensor/AP_InertialSensor_Backend.cpp`, `libraries/AP_InertialSensor/AP_InertialSensor.cpp`, `libraries/AP_InertialSensor/AP_InertialSensor_Backend.h`.

Items of `lean/Estimator_lib.lean` (the estimator translation), unchanged; placed by `tools/split_modules.py` (`ArduLean/Estimator/INDEX.md`).
-/

open FloatLib.Floats (Binary32 Binary64)

set_option maxRecDepth 200000
-- AP_DAL's `const log_RISH old_RISH = _RISH;` read only by WRITE_REPLAY_BLOCK_IFCHANGED, which is `(void)old`
-- without logging (HAL_LOGGING_ENABLED 0): an unused binding, as in the C++
set_option linter.unusedVariables false

namespace Estimator_lib

namespace AP_InertialSensor_SITL

/-- C++ `void AP_InertialSensor_Backend::_rotate_and_correct_accel(uint8_t instance, Vector3f & accel)`, `AP_InertialSensor/AP_InertialSensor_Backend.cpp:112-153` (a member of `AP_InertialSensor_Backend`, translated for `AP_InertialSensor_SITL`). -/
def _rotate_and_correct_accel (w : World) («instance» : UInt8) (accel : Vector3f.State) : Vector3f.State := Id.run do
  let mut accel := accel
  accel := Vector3f.rotate accel w.ins._accel_orientation[UInt8.toNat «instance»]!
  if !w.ins._calibrating_accel && (w.ins._acal == WPtr.null) then
    let t'1 := «instance»
    let (t'2, _) := Vector3f.op_sub_assign accel (AP_ParamV_Vector3_float_5.op_to_Vector3_float w.ins._accel_offset_old_param[UInt8.toNat t'1]!)
    accel := t'2
    let t'4 := «instance»
    accel := { accel with x := accel.x * w.ins._accel_scale_old_param[UInt8.toNat t'4]!._value.x }
    accel := { accel with y := accel.y * w.ins._accel_scale_old_param[UInt8.toNat t'4]!._value.y }
    accel := { accel with z := accel.z * w.ins._accel_scale_old_param[UInt8.toNat t'4]!._value.z }
  accel := Vector3f.rotate accel w.ins._board_orientation
  return accel

/-- C++ `float AP_InertialSensor_Backend::get_clip_limit() const`, `AP_InertialSensor/AP_InertialSensor_Backend.h:88` (a member of `AP_InertialSensor_Backend`, translated for `AP_InertialSensor_SITL`). -/
def get_clip_limit (s : State) : Binary32 := Id.run do
  return s._clip_limit

end AP_InertialSensor_SITL

namespace AP_InertialSensor

/-- C++ `void AP_InertialSensor::calc_vibration_and_clipping(uint8_t instance, const Vector3f & accel, float dt)`, `AP_InertialSensor/AP_InertialSensor.cpp:2229-2253`. -/
def calc_vibration_and_clipping (s : State) (w : World) («instance» : UInt8) (accel : Vector3f.State) (dt : Binary32) : State := Id.run do
  let mut s := s
  if s._backends[UInt8.toNat «instance»]! == WPtr.null then
    return s
  let t'2 := Binary32.abs accel.x
  let t'1 := (WPtr.index s._backends[UInt8.toNat «instance»]!)
  let mut t'5 := decide (t'2 > AP_InertialSensor_SITL.get_clip_limit w.heap'AP_InertialSensor_SITL[t'1]!)
  if !t'5 then
    let t'4 := Binary32.abs accel.y
    let t'3 := (WPtr.index s._backends[UInt8.toNat «instance»]!)
    t'5 := decide (t'4 > AP_InertialSensor_SITL.get_clip_limit w.heap'AP_InertialSensor_SITL[t'3]!)
  let mut t'8 := t'5
  if !t'8 then
    let t'7 := Binary32.abs accel.z
    let t'6 := (WPtr.index s._backends[UInt8.toNat «instance»]!)
    t'8 := decide (t'7 > AP_InertialSensor_SITL.get_clip_limit w.heap'AP_InertialSensor_SITL[t'6]!)
  if t'8 then
    s := { s with _accel_clip_count := s._accel_clip_count.set! (UInt8.toNat «instance») (s._accel_clip_count[UInt8.toNat «instance»]! + (1 : UInt32)) }
  if UInt32.toInt32 (UInt8.toUInt32 «instance») < ((3 : Int32) + (0 : Int32)) then
    let (t'9, t'10) := LowPassFilter_Vector3_float.apply s._accel_vibe_floor_filter[UInt8.toNat «instance»]! accel dt
    s := { s with _accel_vibe_floor_filter := s._accel_vibe_floor_filter.set! (UInt8.toNat «instance») t'9 }
    let accel_filt : Vector3f.State := t'10
    let mut accel_diff : Vector3f.State := (Vector3f.op_sub_Vector3f accel accel_filt)
    accel_diff := { accel_diff with x := accel_diff.x * accel_diff.x }
    accel_diff := { accel_diff with y := accel_diff.y * accel_diff.y }
    accel_diff := { accel_diff with z := accel_diff.z * accel_diff.z }
    let (t'11, _) := LowPassFilter_Vector3_float.apply s._accel_vibe_filter[UInt8.toNat «instance»]! accel_diff dt
    s := { s with _accel_vibe_filter := s._accel_vibe_filter.set! (UInt8.toNat «instance») t'11 }
  return s

/-- C++ `void AP_InertialSensor::set_accel_peak_hold(uint8_t instance, const Vector3f & accel)`, `AP_InertialSensor/AP_InertialSensor.cpp:2256-2270`. -/
def set_accel_peak_hold (s : State) (w : World) («instance» : UInt8) (accel : Vector3f.State) : State := Id.run do
  let mut s := s
  if UInt32.toInt32 (UInt8.toUInt32 «instance») != UInt32.toInt32 (UInt8.toUInt32 s._first_usable_accel) then
    return s
  let now : UInt32 := Estimator_lib.millis w
  if decide (accel.x < s._peak_hold_state.accel_peak_hold_neg_x) || decide (s._peak_hold_state.accel_peak_hold_neg_x_age ≤ now) then
    s := { s with _peak_hold_state.accel_peak_hold_neg_x := accel.x }
    s := { s with _peak_hold_state.accel_peak_hold_neg_x_age := now + Int32.toUInt32 (500 : Int32) }
  return s

end AP_InertialSensor

namespace AP_InertialSensor_SITL

/-- C++ `bool AP_InertialSensor_Backend::sensors_converging() const`, `AP_InertialSensor/AP_InertialSensor_Backend.cpp:70-73` (a member of `AP_InertialSensor_Backend`, translated for `AP_InertialSensor_SITL`). -/
def sensors_converging (w : World) (inp : Inputs) : Bool := Id.run do
  return decide (Estimator_lib.millis64 w < Int64.toUInt64 (Int32.toInt64 (30000 : Int32))) && !inp.get_soft_armed

/-- C++ `void AP_InertialSensor_Backend::_update_sensor_rate(uint16_t & count, uint32_t & start_us, float & rate_hz) const`, `AP_InertialSensor/AP_InertialSensor_Backend.cpp:82-110` (a member of `AP_InertialSensor_Backend`, translated for `AP_InertialSensor_SITL`). -/
def _update_sensor_rate (w : World) (inp : Inputs) (count : UInt16) (start_us : UInt32) (rate_hz : Binary32) : UInt16 × UInt32 × Binary32 := Id.run do
  let mut count := count
  let mut start_us := start_us
  let mut rate_hz := rate_hz
  let now : UInt32 := Estimator_lib.micros w
  if start_us == Int32.toUInt32 (0 : Int32) then
    count := Int16.toUInt16 (Int32.toInt16 (0 : Int32))
    start_us := now
  else
    count := count + (1 : UInt16)
    if UInt32.toUInt64 (now - start_us) > (1000000 : UInt64) then
      let mut observed_rate_hz : Binary32 := Int32.toBinary32 (UInt32.toInt32 (UInt16.toUInt32 count)) * (Binary32.ofBits 0x49742400 /- 1.0e6f -/) / UInt32.toBinary32 (now - start_us)
      let mut filter_constant : Binary32 := (Binary32.ofBits 0x3f7ae148 /- 0.98f -/)
      let mut upper_limit : Binary32 := (Binary32.ofBits 0x3f866666 /- 1.05f -/)
      let mut lower_limit : Binary32 := (Binary32.ofBits 0x3f733333 /- 0.95f -/)
      if sensors_converging w inp then
        filter_constant := (Binary32.ofBits 0x3f4ccccd /- 0.8f -/)
        upper_limit := (Binary32.ofBits 0x40000000 /- 2.0f -/)
        lower_limit := (Binary32.ofBits 0x3f000000 /- 0.5f -/)
      observed_rate_hz := Estimator_lib.constrain_value_line_float observed_rate_hz (rate_hz * lower_limit) (rate_hz * upper_limit) (Int32.toUInt32 (104 : Int32))
      rate_hz := filter_constant * rate_hz + ((Binary32.ofBits 0x3f800000 /- 1 -/) - filter_constant) * observed_rate_hz
      count := Int16.toUInt16 (Int32.toInt16 (0 : Int32))
      start_us := now
  return (count, start_us, rate_hz)

end AP_InertialSensor_SITL

namespace AP_InertialSensor_SITL

-- not read in the Lean: fsync_set
set_option linter.unusedVariables false in
/-- C++ `void AP_InertialSensor_Backend::_notify_new_accel_raw_sample(uint8_t instance, const Vector3f & accel, uint64_t sample_us, bool fsync_set)`, `AP_InertialSensor/AP_InertialSensor_Backend.cpp:559-647` (a member of `AP_InertialSensor_Backend`, translated for `AP_InertialSensor_SITL`). -/
def _notify_new_accel_raw_sample (s : State) (w : World) (inp : Inputs) (self' : WPtr) («instance» : UInt8) (accel : Vector3f.State) (sample_us : UInt64 := Int64.toUInt64 (Int32.toInt64 (0 : Int32))) (fsync_set : Bool := false) : World := Id.run do
  let mut w := w
  let mut sample_us := sample_us
  pure ()  -- C++ `if (has_been_killed(instance))`: false (every overrider the call can reach returns `false`; --ins-gps)
  let mut dt : Binary32 := (Binary32.ofBits 0x00000000 /- 0.0 -/)  -- uninitialized in C++; assigned before every read
  let (t'1, t'2, t'3) := _update_sensor_rate w inp w.ins._sample_accel_count[UInt8.toNat «instance»]! w.ins._sample_accel_start_us[UInt8.toNat «instance»]! w.ins._accel_raw_sample_rates[UInt8.toNat «instance»]!
  w := { w with ins._sample_accel_count := w.ins._sample_accel_count.set! (UInt8.toNat «instance») t'1 }
  w := { w with ins._sample_accel_start_us := w.ins._sample_accel_start_us.set! (UInt8.toNat «instance») t'2 }
  w := { w with ins._accel_raw_sample_rates := w.ins._accel_raw_sample_rates.set! (UInt8.toNat «instance») t'3 }
  let last_sample_us : UInt64 := w.ins._accel_last_sample_us[UInt8.toNat «instance»]!
  if sample_us != Int64.toUInt64 (Int32.toInt64 (0 : Int32)) && w.ins._accel_last_sample_us[UInt8.toNat «instance»]! != Int64.toUInt64 (Int32.toInt64 (0 : Int32)) then
    dt := UInt64.toBinary32 (sample_us - w.ins._accel_last_sample_us[UInt8.toNat «instance»]!) * (Binary32.ofBits 0x358637bd /- 1.0e-6f -/)
    w := { w with ins._accel_last_sample_us := w.ins._accel_last_sample_us.set! (UInt8.toNat «instance») sample_us }
  else
    if w.ins._accel_raw_sample_rates[UInt8.toNat «instance»]! < (Binary32.ofBits 0x42200000 /- 40 -/) then
      if sample_us != Int64.toUInt64 (Int32.toInt64 (0 : Int32)) then
        w := { w with ins._accel_last_sample_us := w.ins._accel_last_sample_us.set! (UInt8.toNat «instance») sample_us }
      return w
    dt := (Binary32.ofBits 0x3f800000 /- 1.0f -/) / w.ins._accel_raw_sample_rates[UInt8.toNat «instance»]!
    w := { w with ins._accel_last_sample_us := w.ins._accel_last_sample_us.set! (UInt8.toNat «instance») (Estimator_lib.micros64 w) }
    sample_us := w.ins._accel_last_sample_us[UInt8.toNat «instance»]!
  w := { w with heap'AP_InertialSensor_SITL := w.heap'AP_InertialSensor_SITL.set! (WPtr.index self') s }  -- this object's state into the World: the call reaches it
  let t'4 := w.ins  -- the object out of the World for the call (--swap-out)
  w := { w with ins := default }
  w := { w with ins := AP_InertialSensor.calc_vibration_and_clipping t'4 w «instance» accel dt }
  pure ()  -- C++ `_getsem25`: a semaphore, which does nothing here (one thread, --semaphores)
  if sample_us - last_sample_us > UInt32.toUInt64 (100000 : UInt32) then
    w := { w with ins._delta_velocity_acc := w.ins._delta_velocity_acc.set! (UInt8.toNat «instance») (Vector3f.zero w.ins._delta_velocity_acc[UInt8.toNat «instance»]!) }
    w := { w with ins._delta_velocity_acc_dt := w.ins._delta_velocity_acc_dt.set! (UInt8.toNat «instance») (Binary32.ofBits 0x00000000 /- 0 -/) }
    dt := (Binary32.ofBits 0x00000000 /- 0 -/)
  let (t'5, _) := Vector3f.op_add_assign w.ins._delta_velocity_acc[UInt8.toNat «instance»]! (Vector3f.op_mul_float accel dt)
  w := { w with ins._delta_velocity_acc := w.ins._delta_velocity_acc.set! (UInt8.toNat «instance») t'5 }
  w := { w with ins._delta_velocity_acc_dt := w.ins._delta_velocity_acc_dt.set! (UInt8.toNat «instance») (w.ins._delta_velocity_acc_dt[UInt8.toNat «instance»]! + dt) }
  let (t'7, t'8) := LowPassFilter2p_Vector3_float.apply w.ins._accel_filter[UInt8.toNat «instance»]! accel
  w := { w with ins._accel_filter := w.ins._accel_filter.set! (UInt8.toNat «instance») t'7 }
  w := { w with ins._accel_filtered := w.ins._accel_filtered.set! (UInt8.toNat «instance») t'8 }
  if Vector3f.is_nan w.ins._accel_filtered[UInt8.toNat «instance»]! || Vector3f.is_inf w.ins._accel_filtered[UInt8.toNat «instance»]! then
    w := { w with ins._accel_filter := w.ins._accel_filter.set! (UInt8.toNat «instance») (LowPassFilter2p_Vector3_float.reset_void w.ins._accel_filter[UInt8.toNat «instance»]!) }
  w := { w with ins := AP_InertialSensor.set_accel_peak_hold w.ins w «instance» w.ins._accel_filtered[UInt8.toNat «instance»]! }
  w := { w with ins._new_accel_data := w.ins._new_accel_data.set! (UInt8.toNat «instance») true }
  pure ()  -- C++ `log_accel_raw`: no effect in the model
  return w

/-- C++ `void AP_InertialSensor_Backend::_publish_temperature(uint8_t instance, float temperature)`, `AP_InertialSensor/AP_InertialSensor_Backend.cpp:792-815` (a member of `AP_InertialSensor_Backend`, translated for `AP_InertialSensor_SITL`). -/
def _publish_temperature (w : World) («instance» : UInt8) (temperature : Binary32) : World := Id.run do
  let mut w := w
  if UInt32.toInt32 (UInt8.toUInt32 «instance») ≥ ((3 : Int32) + (0 : Int32)) then
    return w
  pure ()  -- C++ `if (has_been_killed(instance))`: false (every overrider the call can reach returns `false`; --ins-gps)
  w := { w with ins._temperature := w.ins._temperature.set! (UInt8.toNat «instance») temperature }
  return w

/-- C++ `float AP_InertialSensor_SITL::get_temperature()`, `reference/hal/sensors_ins.cpp:56-59`. -/
def get_temperature : Binary32 := Id.run do
  return (Binary32.ofBits 0x41a00000 /- 20.0f -/)

/-- C++ `void AP_InertialSensor_Backend::_rotate_and_correct_gyro(uint8_t instance, Vector3f & gyro)`, `AP_InertialSensor/AP_InertialSensor_Backend.cpp:155-182` (a member of `AP_InertialSensor_Backend`, translated for `AP_InertialSensor_SITL`). -/
def _rotate_and_correct_gyro (w : World) («instance» : UInt8) (gyro : Vector3f.State) : Vector3f.State := Id.run do
  let mut gyro := gyro
  gyro := Vector3f.rotate gyro w.ins._gyro_orientation[UInt8.toNat «instance»]!
  if !w.ins._calibrating_gyro then
    let t'1 := «instance»
    let (t'2, _) := Vector3f.op_sub_assign gyro (AP_ParamV_Vector3_float_5.op_to_Vector3_float w.ins._gyro_offset_old_param[UInt8.toNat t'1]!)
    gyro := t'2
    gyro := Vector3f.rotate gyro w.ins._board_orientation
  return gyro

-- not read in the Lean: filter_phase
set_option linter.unusedVariables false in
/-- C++ `Vector3f AP_InertialSensor_Backend::apply_gyro_filters(const uint8_t instance, const Vector3f & gyro)`, `AP_InertialSensor/AP_InertialSensor_Backend.cpp:231-292` (a member of `AP_InertialSensor_Backend`, translated for `AP_InertialSensor_SITL`). -/
def apply_gyro_filters (w : World) («instance» : UInt8) (gyro : Vector3f.State) : World × Vector3f.State := Id.run do
  let mut w := w
  let mut filter_phase : UInt8 := Int8.toUInt8 (Int32.toInt8 (0 : Int32))
  pure ()  -- C++ `save_gyro_window`: no effect in the model
  let mut gyro_filtered : Vector3f.State := gyro
  let (t'1, t'2) := LowPassFilter2p_Vector3_float.apply w.ins._gyro_filter[UInt8.toNat «instance»]! gyro_filtered
  w := { w with ins._gyro_filter := w.ins._gyro_filter.set! (UInt8.toNat «instance») t'1 }
  gyro_filtered := t'2
  if Vector3f.is_nan gyro_filtered || Vector3f.is_inf gyro_filtered then
    w := { w with ins._gyro_filter := w.ins._gyro_filter.set! (UInt8.toNat «instance») (LowPassFilter2p_Vector3_float.reset_void w.ins._gyro_filter[UInt8.toNat «instance»]!) }
    gyro_filtered := w.ins._gyro_filtered[UInt8.toNat «instance»]!
  w := { w with ins._gyro_filtered := w.ins._gyro_filtered.set! (UInt8.toNat «instance») gyro_filtered }
  return (w, gyro_filtered)

end AP_InertialSensor_SITL

namespace AP_InertialSensor_SITL

/-- C++ `void AP_InertialSensor_Backend::update_primary()`, `AP_InertialSensor/AP_InertialSensor_Backend.cpp:850-863` (a member of `AP_InertialSensor_Backend`, translated for `AP_InertialSensor_SITL`). -/
def update_primary (s : State) (w : World) : State := Id.run do
  let mut s := s
  let is_new_primary : Bool := (UInt32.toInt32 (UInt8.toUInt32 s.gyro_instance) == UInt32.toInt32 (UInt8.toUInt32 w.ins._primary))
  let now_us : UInt32 := Estimator_lib.micros w
  if (if s.is_primary then (1 : Int32) else (0 : Int32)) != (if is_new_primary then (1 : Int32) else (0 : Int32)) || Estimator_lib.timeout_expired s.last_primary_update_us now_us (200000 : UInt64) then
    pure ()  -- C++ `set_primary`: no effect in the model
    s := { s with is_primary := is_new_primary }
    s := { s with last_primary_update_us := now_us }
  return s

end AP_InertialSensor_SITL

namespace AP_InertialSensor_SITL

/-- C++ `void AP_InertialSensor_Backend::_notify_new_gyro_raw_sample(uint8_t instance, const Vector3f & accel, uint64_t sample_us)`, `AP_InertialSensor/AP_InertialSensor_Backend.cpp:294-394` (a member of `AP_InertialSensor_Backend`, translated for `AP_InertialSensor_SITL`). -/
def _notify_new_gyro_raw_sample (s : State) (w : World) (inp : Inputs) («instance» : UInt8) (gyro : Vector3f.State) (sample_us : UInt64 := Int64.toUInt64 (Int32.toInt64 (0 : Int32))) : State × World := Id.run do
  let mut s := s
  let mut w := w
  let mut sample_us := sample_us
  pure ()  -- C++ `if (has_been_killed(instance))`: false (every overrider the call can reach returns `false`; --ins-gps)
  let mut dt : Binary32 := (Binary32.ofBits 0x00000000 /- 0.0 -/)  -- uninitialized in C++; assigned before every read
  let (t'1, t'2, t'3) := _update_sensor_rate w inp w.ins._sample_gyro_count[UInt8.toNat «instance»]! w.ins._sample_gyro_start_us[UInt8.toNat «instance»]! w.ins._gyro_raw_sample_rates[UInt8.toNat «instance»]!
  w := { w with ins._sample_gyro_count := w.ins._sample_gyro_count.set! (UInt8.toNat «instance») t'1 }
  w := { w with ins._sample_gyro_start_us := w.ins._sample_gyro_start_us.set! (UInt8.toNat «instance») t'2 }
  w := { w with ins._gyro_raw_sample_rates := w.ins._gyro_raw_sample_rates.set! (UInt8.toNat «instance») t'3 }
  let last_sample_us : UInt64 := w.ins._gyro_last_sample_us[UInt8.toNat «instance»]!
  if sample_us != Int64.toUInt64 (Int32.toInt64 (0 : Int32)) && w.ins._gyro_last_sample_us[UInt8.toNat «instance»]! != Int64.toUInt64 (Int32.toInt64 (0 : Int32)) then
    dt := UInt64.toBinary32 (sample_us - w.ins._gyro_last_sample_us[UInt8.toNat «instance»]!) * (Binary32.ofBits 0x358637bd /- 1.0e-6f -/)
    w := { w with ins._gyro_last_sample_us := w.ins._gyro_last_sample_us.set! (UInt8.toNat «instance») sample_us }
  else
    if w.ins._gyro_raw_sample_rates[UInt8.toNat «instance»]! < (Binary32.ofBits 0x42200000 /- 40 -/) then
      if sample_us != Int64.toUInt64 (Int32.toInt64 (0 : Int32)) then
        w := { w with ins._gyro_last_sample_us := w.ins._gyro_last_sample_us.set! (UInt8.toNat «instance») sample_us }
      return (s, w)
    dt := (Binary32.ofBits 0x3f800000 /- 1.0f -/) / w.ins._gyro_raw_sample_rates[UInt8.toNat «instance»]!
    w := { w with ins._gyro_last_sample_us := w.ins._gyro_last_sample_us.set! (UInt8.toNat «instance») (Estimator_lib.micros64 w) }
    sample_us := w.ins._gyro_last_sample_us[UInt8.toNat «instance»]!
  if inp.opticalflow_set then
    pure ()  -- C++ `OpticalFlow::push_gyro(...)`: left out (--drop)
  let mut delta_angle : Vector3f.State := Vector3f.op_mul_float (Vector3f.op_mul_float (Vector3f.op_add gyro w.ins._last_raw_gyro[UInt8.toNat «instance»]!) (Binary32.ofBits 0x3f000000 /- 0.5f -/)) dt
  let mut delta_coning : Vector3f.State := (Vector3f.op_add w.ins._delta_angle_acc[UInt8.toNat «instance»]! (Vector3f.op_mul_float w.ins._last_delta_angle[UInt8.toNat «instance»]! ((Binary32.ofBits 0x3f800000 /- 1.0f -/) / (Binary32.ofBits 0x40c00000 /- 6.0f -/))))
  delta_coning := Vector3f.op_mod delta_coning delta_angle
  let (t'4, _) := Vector3f.op_mul_assign_float delta_coning (Binary32.ofBits 0x3f000000 /- 0.5f -/)
  delta_coning := t'4
  let mut gyro_filtered : Vector3f.State := Vector3f.init_void
  pure ()  -- C++ `_getsem23`: a semaphore, which does nothing here (one thread, --semaphores)
  if sample_us - last_sample_us > UInt32.toUInt64 (100000 : UInt32) then
    w := { w with ins._delta_angle_acc := w.ins._delta_angle_acc.set! (UInt8.toNat «instance») (Vector3f.zero w.ins._delta_angle_acc[UInt8.toNat «instance»]!) }
    w := { w with ins._delta_angle_acc_dt := w.ins._delta_angle_acc_dt.set! (UInt8.toNat «instance») (Binary32.ofBits 0x00000000 /- 0 -/) }
    dt := (Binary32.ofBits 0x00000000 /- 0 -/)
    delta_angle := Vector3f.zero delta_angle
  let (t'6, _) := Vector3f.op_add_assign w.ins._delta_angle_acc[UInt8.toNat «instance»]! (Vector3f.op_add delta_angle delta_coning)
  w := { w with ins._delta_angle_acc := w.ins._delta_angle_acc.set! (UInt8.toNat «instance») t'6 }
  w := { w with ins._delta_angle_acc_dt := w.ins._delta_angle_acc_dt.set! (UInt8.toNat «instance») (w.ins._delta_angle_acc_dt[UInt8.toNat «instance»]! + dt) }
  w := { w with ins._last_delta_angle := w.ins._last_delta_angle.set! (UInt8.toNat «instance») delta_angle }
  w := { w with ins._last_raw_gyro := w.ins._last_raw_gyro.set! (UInt8.toNat «instance») gyro }
  let (t'8, t'9) := apply_gyro_filters w «instance» gyro
  w := t'8
  gyro_filtered := t'9
  w := { w with ins._new_gyro_data := w.ins._new_gyro_data.set! (UInt8.toNat «instance») true }
  pure ()  -- C++ `log_gyro_raw`: no effect in the model
  s := update_primary s w
  return (s, w)

end AP_InertialSensor_SITL

namespace AP_InertialSensor_SITL

/-- C++ `void AP_InertialSensor_SITL::timer_update()`, `reference/hal/sensors_ins.cpp:61-96`. -/
def timer_update (s : State) (w : World) (inp : Inputs) (self' : WPtr) : State × World := Id.run do
  let mut s := s
  let mut w := w
  let idx : UInt8 := s.gyro_instance
  if UInt32.toInt32 (UInt8.toUInt32 idx) ≥ UInt32.toInt32 (UInt8.toUInt32 Estimator_lib.EST_MAX_IMUS) then
    return (s, w)
  let «in» : EstRecord := Estimator_lib.est_input w
  let n : UInt8 := «in».imu_n[UInt8.toNat idx]!
  if UInt32.toInt32 (UInt8.toUInt32 n) == (0 : Int32) then
    return (s, w)
  let base : UInt16 := Int16.toUInt16 (Int32.toInt16 (UInt32.toInt32 (UInt16.toUInt32 (UInt8.toUInt16 idx)) * UInt32.toInt32 (UInt8.toUInt32 Estimator_lib.EST_MAX_IMU_SAMPLES)))
  let now : UInt64 := Estimator_lib.micros64 w
  let period : UInt64 := Estimator_lib.est_step_period_us w
  for j' in [0:n.toNat] do
    let j : UInt8 := Nat.toUInt8 j'
    let sample_us : UInt64 := now - (period * Int64.toUInt64 (Int32.toInt64 (UInt32.toInt32 (UInt8.toUInt32 n) - (1 : Int32) - UInt32.toInt32 (UInt8.toUInt32 j)))) / UInt8.toUInt64 n
    let mut accel : Vector3f.State := «in».accel[Int32.toNatClampNeg (UInt32.toInt32 (UInt16.toUInt32 base) + UInt32.toInt32 (UInt8.toUInt32 j))]!
    pure ()  -- C++ `_notify_new_accel_sensor_rate_sample`: no effect in the model
    accel := _rotate_and_correct_accel w s.accel_instance accel
    w := _notify_new_accel_raw_sample s w inp self' s.accel_instance accel sample_us false
  w := _publish_temperature w s.accel_instance (get_temperature)
  for j'2' in [0:n.toNat] do
    let j'2 : UInt8 := Nat.toUInt8 j'2'
    let sample_us'2 : UInt64 := now - (period * Int64.toUInt64 (Int32.toInt64 (UInt32.toInt32 (UInt8.toUInt32 n) - (1 : Int32) - UInt32.toInt32 (UInt8.toUInt32 j'2)))) / UInt8.toUInt64 n
    let mut gyro : Vector3f.State := «in».gyro[Int32.toNatClampNeg (UInt32.toInt32 (UInt16.toUInt32 base) + UInt32.toInt32 (UInt8.toUInt32 j'2))]!
    pure ()  -- C++ `_notify_new_gyro_sensor_rate_sample`: no effect in the model
    gyro := _rotate_and_correct_gyro w s.gyro_instance gyro
    let (t'1, t'2) := _notify_new_gyro_raw_sample s w inp s.gyro_instance gyro sample_us'2
    w := t'2
    s := t'1
  return (s, w)

end AP_InertialSensor_SITL

namespace AP_InertialSensor_SITL

/-- C++ `void AP_InertialSensor_Backend::_publish_accel(uint8_t instance, const Vector3f & accel)`, `AP_InertialSensor/AP_InertialSensor_Backend.cpp:532-557` (a member of `AP_InertialSensor_Backend`, translated for `AP_InertialSensor_SITL`). -/
def _publish_accel (w : World) («instance» : UInt8) (accel : Vector3f.State) : World := Id.run do
  let mut w := w
  pure ()  -- C++ `if (has_been_killed(instance))`: false (every overrider the call can reach returns `false`; --ins-gps)
  w := { w with ins._accel := w.ins._accel.set! (UInt8.toNat «instance») accel }
  w := { w with ins._accel_healthy := w.ins._accel_healthy.set! (UInt8.toNat «instance») true }
  w := { w with ins._delta_velocity := w.ins._delta_velocity.set! (UInt8.toNat «instance») (w.ins._delta_velocity_acc[UInt8.toNat «instance»]!) }
  w := { w with ins._delta_velocity_dt := w.ins._delta_velocity_dt.set! (UInt8.toNat «instance») (w.ins._delta_velocity_acc_dt[UInt8.toNat «instance»]!) }
  w := { w with ins._delta_velocity_valid := w.ins._delta_velocity_valid.set! (UInt8.toNat «instance») true }
  w := { w with ins._delta_velocity_acc := w.ins._delta_velocity_acc.set! (UInt8.toNat «instance») (Vector3f.zero w.ins._delta_velocity_acc[UInt8.toNat «instance»]!) }
  w := { w with ins._delta_velocity_acc_dt := w.ins._delta_velocity_acc_dt.set! (UInt8.toNat «instance») (Binary32.ofBits 0x00000000 /- 0 -/) }
  let mut t'1 := w.ins._accel_calibrator != WPtr.null
  if t'1 then
    pure ()  -- C++ `_imu._accel_calibrator->get_status(...)`: not reached (a pointer to `AccelCalibrator`, of which the World has no object, is null)
    t'1 := UInt32.toInt32 (accel_cal_status_t.toInt accel_cal_status_t.ACCEL_CAL_NOT_STARTED) == UInt32.toInt32 (accel_cal_status_t.toInt accel_cal_status_t.ACCEL_CAL_COLLECTING_SAMPLE)
  if t'1 then
    let mut cal_sample : Vector3f.State := w.ins._delta_velocity[UInt8.toNat «instance»]!
    cal_sample := Vector3f.rotate_inverse cal_sample w.ins._board_orientation
    pure ()  -- C++ `_imu._accel_calibrator->new_sample(...)`: not reached (a pointer to `AccelCalibrator`, of which the World has no object, is null)
  return w

end AP_InertialSensor_SITL

namespace AP_InertialSensor_SITL

/-- C++ `uint16_t AP_InertialSensor_Backend::_accel_filter_cutoff() const`, `AP_InertialSensor/AP_InertialSensor_Backend.h:312` (a member of `AP_InertialSensor_Backend`, translated for `AP_InertialSensor_SITL`). -/
def _accel_filter_cutoff (w : World) : UInt16 := Id.run do
  return Int16.toUInt16 (AP_ParamT_short_2.op_to_short w.ins._accel_filter_cutoff)

/-- C++ `float AP_InertialSensor_Backend::_accel_raw_sample_rate(uint8_t instance) const`, `AP_InertialSensor/AP_InertialSensor_Backend.h:278-280` (a member of `AP_InertialSensor_Backend`, translated for `AP_InertialSensor_SITL`). -/
def _accel_raw_sample_rate (w : World) («instance» : UInt8) : Binary32 := Id.run do
  return w.ins._accel_raw_sample_rates[UInt8.toNat «instance»]!

end AP_InertialSensor_SITL

namespace AP_InertialSensor_SITL

/-- C++ `void AP_InertialSensor_Backend::update_accel_filters(uint8_t instance)`, `AP_InertialSensor/AP_InertialSensor_Backend.cpp:924-935` (a member of `AP_InertialSensor_Backend`, translated for `AP_InertialSensor_SITL`). -/
def update_accel_filters (s : State) (w : World) («instance» : UInt8) : State × World := Id.run do
  let mut s := s
  let mut w := w
  if UInt32.toInt32 (UInt8.toUInt32 «instance») ≥ ((3 : Int32) + (0 : Int32)) then
    return (s, w)
  if UInt32.toInt32 (UInt16.toUInt32 s._last_accel_filter_hz) != UInt32.toInt32 (UInt16.toUInt32 (_accel_filter_cutoff w)) then
    w := { w with ins._accel_filter := w.ins._accel_filter.set! (UInt8.toNat «instance») (LowPassFilter2p_Vector3_float.set_cutoff_frequency w.ins._accel_filter[UInt8.toNat «instance»]! (_accel_raw_sample_rate w «instance») (UInt16.toBinary32 (_accel_filter_cutoff w))) }
    s := { s with _last_accel_filter_hz := _accel_filter_cutoff w }
  return (s, w)

/-- C++ `void AP_InertialSensor_Backend::update_accel(uint8_t instance)`, `AP_InertialSensor/AP_InertialSensor_Backend.cpp:897-919` (a member of `AP_InertialSensor_Backend`, translated for `AP_InertialSensor_SITL`). -/
def update_accel (s : State) (w : World) («instance» : UInt8) : State × World := Id.run do
  let mut s := s
  let mut w := w
  pure ()  -- C++ `_getsem28`: a semaphore, which does nothing here (one thread, --semaphores)
  if UInt32.toInt32 (UInt8.toUInt32 «instance») ≥ ((3 : Int32) + (0 : Int32)) then
    return (s, w)
  pure ()  -- C++ `if (has_been_killed(instance))`: false (every overrider the call can reach returns `false`; --ins-gps)
  if w.ins._new_accel_data[UInt8.toNat «instance»]! then
    w := _publish_accel w «instance» w.ins._accel_filtered[UInt8.toNat «instance»]!
    w := { w with ins._new_accel_data := w.ins._new_accel_data.set! (UInt8.toNat «instance») false }
  else
    w := { w with ins._accel_healthy := w.ins._accel_healthy.set! (UInt8.toNat «instance») false }
  let (t'1, t'2) := update_accel_filters s w «instance»
  w := t'2
  s := t'1
  return (s, w)

/-- C++ `void AP_InertialSensor_Backend::_publish_gyro(uint8_t instance, const Vector3f & gyro)`, `AP_InertialSensor/AP_InertialSensor_Backend.cpp:187-202` (a member of `AP_InertialSensor_Backend`, translated for `AP_InertialSensor_SITL`). -/
def _publish_gyro (w : World) («instance» : UInt8) (gyro : Vector3f.State) : World := Id.run do
  let mut w := w
  pure ()  -- C++ `if (has_been_killed(instance))`: false (every overrider the call can reach returns `false`; --ins-gps)
  w := { w with ins._gyro := w.ins._gyro.set! (UInt8.toNat «instance») gyro }
  w := { w with ins._gyro_healthy := w.ins._gyro_healthy.set! (UInt8.toNat «instance») true }
  w := { w with ins._delta_angle := w.ins._delta_angle.set! (UInt8.toNat «instance») (w.ins._delta_angle_acc[UInt8.toNat «instance»]!) }
  w := { w with ins._delta_angle_dt := w.ins._delta_angle_dt.set! (UInt8.toNat «instance») (w.ins._delta_angle_acc_dt[UInt8.toNat «instance»]!) }
  w := { w with ins._delta_angle_valid := w.ins._delta_angle_valid.set! (UInt8.toNat «instance») true }
  w := { w with ins._delta_angle_acc := w.ins._delta_angle_acc.set! (UInt8.toNat «instance») (Vector3f.zero w.ins._delta_angle_acc[UInt8.toNat «instance»]!) }
  w := { w with ins._delta_angle_acc_dt := w.ins._delta_angle_acc_dt.set! (UInt8.toNat «instance») (Binary32.ofBits 0x00000000 /- 0 -/) }
  return w

/-- C++ `float AP_InertialSensor_Backend::_gyro_raw_sample_rate(uint8_t instance) const`, `AP_InertialSensor/AP_InertialSensor_Backend.h:289-291` (a member of `AP_InertialSensor_Backend`, translated for `AP_InertialSensor_SITL`). -/
def _gyro_raw_sample_rate (w : World) («instance» : UInt8) : Binary32 := Id.run do
  return w.ins._gyro_raw_sample_rates[UInt8.toNat «instance»]!

/-- C++ `uint16_t AP_InertialSensor_Backend::_gyro_filter_cutoff() const`, `AP_InertialSensor/AP_InertialSensor_Backend.h:315` (a member of `AP_InertialSensor_Backend`, translated for `AP_InertialSensor_SITL`). -/
def _gyro_filter_cutoff (w : World) : UInt16 := Id.run do
  return Int16.toUInt16 (AP_ParamT_short_2.op_to_short w.ins._gyro_filter_cutoff)

/-- C++ `void AP_InertialSensor_Backend::update_gyro_filters(uint8_t instance)`, `AP_InertialSensor/AP_InertialSensor_Backend.cpp:868-892` (a member of `AP_InertialSensor_Backend`, translated for `AP_InertialSensor_SITL`). -/
def update_gyro_filters (s : State) (w : World) (inp : Inputs) («instance» : UInt8) : State × World := Id.run do
  let mut s := s
  let mut w := w
  if UInt32.toInt32 (UInt8.toUInt32 «instance») ≥ ((3 : Int32) + (0 : Int32)) then
    return (s, w)
  let gyro_rate : Binary32 := _gyro_raw_sample_rate w «instance»
  if UInt32.toInt32 (UInt16.toUInt32 s._last_gyro_filter_hz) != UInt32.toInt32 (UInt16.toUInt32 (_gyro_filter_cutoff w)) || sensors_converging w inp then
    w := { w with ins._gyro_filter := w.ins._gyro_filter.set! (UInt8.toNat «instance») (LowPassFilter2p_Vector3_float.set_cutoff_frequency w.ins._gyro_filter[UInt8.toNat «instance»]! gyro_rate (UInt16.toBinary32 (_gyro_filter_cutoff w))) }
    s := { s with _last_gyro_filter_hz := _gyro_filter_cutoff w }
  return (s, w)

/-- C++ `void AP_InertialSensor_Backend::update_gyro(uint8_t instance)`, `AP_InertialSensor/AP_InertialSensor_Backend.cpp:820-848` (a member of `AP_InertialSensor_Backend`, translated for `AP_InertialSensor_SITL`). -/
def update_gyro (s : State) (w : World) (inp : Inputs) («instance» : UInt8) : State × World := Id.run do
  let mut s := s
  let mut w := w
  pure ()  -- C++ `_getsem27`: a semaphore, which does nothing here (one thread, --semaphores)
  if UInt32.toInt32 (UInt8.toUInt32 «instance») ≥ ((3 : Int32) + (0 : Int32)) then
    return (s, w)
  pure ()  -- C++ `if (has_been_killed(instance))`: false (every overrider the call can reach returns `false`; --ins-gps)
  if w.ins._new_gyro_data[UInt8.toNat «instance»]! then
    w := _publish_gyro w «instance» w.ins._gyro_filtered[UInt8.toNat «instance»]!
    w := { w with ins._new_gyro_data := w.ins._new_gyro_data.set! (UInt8.toNat «instance») false }
  else
    w := { w with ins._gyro_healthy := w.ins._gyro_healthy.set! (UInt8.toNat «instance») false }
  let (t'1, t'2) := update_gyro_filters s w inp «instance»
  w := t'2
  s := t'1
  return (s, w)

/-- C++ `bool AP_InertialSensor_SITL::update()`, `reference/hal/sensors_ins.cpp:98-103`. -/
def update (s : State) (w : World) (inp : Inputs) : State × World × Bool := Id.run do
  let mut s := s
  let mut w := w
  let (t'1, t'2) := update_accel s w s.accel_instance
  w := t'2
  s := t'1
  let (t'3, t'4) := update_gyro s w inp s.gyro_instance
  w := t'4
  s := t'3
  return (s, w, true)

end AP_InertialSensor_SITL

namespace AP_InertialSensor

/-- C++ `const AP_InertialSensor_Backend * AP_InertialSensor::_find_gyro_backend(uint8_t instance) const`, `AP_InertialSensor/AP_InertialSensor.cpp:1503-1511`. -/
def _find_gyro_backend (s : State) (w : World) («instance» : UInt8) : WPtr := Id.run do
  for i' in [0:s._backend_count.toNat] do
    let i : UInt8 := Nat.toUInt8 i'
    let mut t'2 := s._backends[UInt8.toNat i]! != WPtr.null
    if t'2 then
      let t'1 := (WPtr.index s._backends[UInt8.toNat i]!)
      t'2 := UInt32.toInt32 (UInt8.toUInt32 (AP_InertialSensor_SITL.get_gyro_instance w.heap'AP_InertialSensor_SITL[t'1]!)) == UInt32.toInt32 (UInt8.toUInt32 «instance»)
    if t'2 then
      return s._backends[UInt8.toNat i]!
  return WPtr.null

end AP_InertialSensor

namespace AP_InertialSensor

/-- C++ `float AP_InertialSensor::get_gyro_bias_limit_rads(uint8_t instance) const`, `AP_InertialSensor/AP_InertialSensor.cpp:1513-1521`. -/
def get_gyro_bias_limit_rads (s : State) (w : World) («instance» : UInt8) : Binary32 := Id.run do
  let backend : WPtr := _find_gyro_backend s w «instance»
  if backend == WPtr.null then
    return (Binary32.ofBits 0x3f000000 /- 0.5f -/)
  return AP_InertialSensor_SITL.gyro_bias_limit_rads

end AP_InertialSensor

namespace AP_InertialSensor

/-- C++ `float AP_InertialSensor::get_gyro_bias_init_dps(uint8_t instance) const`, `AP_InertialSensor/AP_InertialSensor.cpp:1523-1530`. -/
def get_gyro_bias_init_dps (s : State) (w : World) («instance» : UInt8) : Binary32 := Id.run do
  let backend : WPtr := _find_gyro_backend s w «instance»
  if backend == WPtr.null then
    return (Binary32.ofBits 0x40200000 /- 2.5f -/)
  return AP_InertialSensor_SITL.gyro_bias_init_dps

/-- C++ `const Vector3f & AP_InertialSensor::get_imu_pos_offset(uint8_t instance) const`, `AP_InertialSensor/AP_InertialSensor.h:231-233`. -/
def get_imu_pos_offset_uint8_t (s : State) («instance» : UInt8) : Vector3f.State := Id.run do
  let t'1 := «instance»
  let t'2 := t'1
  return AP_ParamV_Vector3_float_5.op_to_Vector3_float s._accel_pos_old_param[UInt8.toNat t'2]!

end AP_InertialSensor

namespace AP_InertialSensor_SITL

/-- C++ `AP_InertialSensor_SITL::AP_InertialSensor_SITL(AP_InertialSensor & imu, const uint16_t * sample_rates)`, `reference/hal/sensors_ins.cpp:16-22`. -/
def init (w : World) : State × World := Id.run do
  let mut s : State := {}
  let mut w := w
  s := AP_InertialSensor_Backend.init s
  s := { s with gyro_sample_hz := Estimator_lib.est_imu_rate_hz w }
  s := { s with accel_sample_hz := Estimator_lib.est_imu_rate_hz w }
  w := Estimator_lib.est_event w Estimator_lib.EST_EV_INS_INIT
  return (s, w)

/-- C++ `bool AP_InertialSensor_SITL::init_sensor()`, `reference/hal/sensors_ins.cpp:37-41`. -/
def init_sensor (s : State) : State × Bool := Id.run do
  let mut s := s
  s := { s with sitl := WPtr.sitl }
  return (s, s.sitl != WPtr.null)

/-- C++ `static AP_InertialSensor_Backend * AP_InertialSensor_SITL::detect(AP_InertialSensor & _imu, const uint16_t * sample_rates)`, `reference/hal/sensors_ins.cpp:24-35`. -/
def detect (w : World) : World × WPtr := Id.run do
  let mut w := w
  let (t'1, t'2) := AP_InertialSensor_SITL.init w
  w := t'2
  let t'3 := w.heap'AP_InertialSensor_SITL.size
  w := { w with heap'AP_InertialSensor_SITL := w.heap'AP_InertialSensor_SITL.push t'1 }
  let mut sensor : WPtr := (WPtr.heap'AP_InertialSensor_SITL t'3)
  if sensor == WPtr.null then
    return (w, WPtr.null)
  let t'4 := w.heap'AP_InertialSensor_SITL[(WPtr.index sensor)]!  -- the object out of its slot for the call (--swap-out)
  w := { w with heap'AP_InertialSensor_SITL := w.heap'AP_InertialSensor_SITL.set! (WPtr.index sensor) default }
  let (t'5, t'6) := AP_InertialSensor_SITL.init_sensor t'4
  w := { w with heap'AP_InertialSensor_SITL := w.heap'AP_InertialSensor_SITL.set! (WPtr.index sensor) t'5 }
  if !t'6 then
    pure ()  -- C++ `delete sensor`: the object's slot is left as it is (nothing refers to it again)
    return (w, WPtr.null)
  return (w, sensor)

end AP_InertialSensor_SITL

namespace AP_InertialSensor

/-- C++ `void AP_InertialSensor::detect_backends()`, `AP_InertialSensor/AP_InertialSensor.cpp:1138-1310`. -/
def detect_backends (s : State) (w : World) : State × World := Id.run do
  let mut s := s
  let mut w := w
  if s._backends_detected then
    return (s, w)
  s := { s with _backends_detected := true }
  let mut probe_count : UInt8 := Int8.toUInt8 (Int32.toInt8 (0 : Int32))
  let enable_mask : UInt8 := AP_ParamT_unsigned_char_1.op_to_unsigned_char s._enable_mask
  let mut found_mask : UInt8 := Int8.toUInt8 (Int32.toInt8 (0 : Int32))
  let mut i : UInt8 := Int8.toUInt8 (Int32.toInt8 (0 : Int32))
  for _ in [0:2^64] do  -- C loop without a constant trip count (--general-loops)
    if !(decide (UInt32.toInt32 (UInt8.toUInt32 i) < Int8.toInt32 (AP_ParamT_signed_char_1.op_to_signed_char w.sitl.imu_count))) then break
    for _ in [0:1] do
      let mut t'5 := (((1 : UInt32) <<< Int32.toUInt32 (UInt32.toInt32 (UInt8.toUInt32 probe_count))) &&& UInt8.toUInt32 enable_mask) != (0 : UInt32)
      if t'5 then
        let (t'1, t'2) := AP_InertialSensor_SITL.detect w
        w := t'1
        let (t'3, t'4) := _add_backend s t'2
        s := t'3
        t'5 := t'4
      if t'5 then
        found_mask := UInt32.toUInt8 (UInt8.toUInt32 found_mask ||| ((1 : UInt32) <<< Int32.toUInt32 (UInt32.toInt32 (UInt8.toUInt32 probe_count))))
      probe_count := probe_count + (1 : UInt8)
    i := i + (1 : UInt8)
  return (s, w)

/-- C++ `bool AP_InertialSensor::register_gyro(uint8_t & instance, uint16_t raw_sample_rate_hz, uint32_t id)`, `AP_InertialSensor/AP_InertialSensor.cpp:749-788`. -/
def register_gyro (s : State) (o : Outputs) (inp : Inputs) («instance» : UInt8) (raw_sample_rate_hz : UInt16) (id : UInt32) : State × Outputs × UInt8 × Bool := Id.run do
  let mut s := s
  let mut o := o
  let mut «instance» := «instance»
  if UInt32.toInt32 (UInt8.toUInt32 s._gyro_count) == ((3 : Int32) + (0 : Int32)) then
    o := o.push (Output.send_text (4 : UInt32) "Failed to register gyro id %u" #[Sum.inl (UInt32.toUInt64 id)])
    return (s, o, «instance», false)
  let mut instance_to_check : UInt8 := Int8.toUInt8 (Int32.toInt8 (0 : Int32))
  for _ in [0:2^64] do  -- C loop without a constant trip count (--general-loops)
    if !(decide (UInt32.toInt32 (UInt8.toUInt32 instance_to_check) < UInt32.toInt32 (UInt8.toUInt32 s._gyro_count))) then break
    let t'1 := instance_to_check
    if AP_ParamT_unsigned_int_3.op_to_unsigned_int s._gyro_id_old_param[UInt8.toNat t'1]! == id then
      return (s, o, «instance», false)
    instance_to_check := instance_to_check + (1 : UInt8)
  s := { s with _gyro_raw_sample_rates := s._gyro_raw_sample_rates.set! (UInt8.toNat s._gyro_count) (UInt16.toBinary32 raw_sample_rate_hz) }
  s := { s with _gyro_over_sampling := s._gyro_over_sampling.set! (UInt8.toNat s._gyro_count) (Int8.toUInt8 (Int32.toInt8 (1 : Int32))) }
  s := { s with _gyro_raw_sampling_multiplier := s._gyro_raw_sampling_multiplier.set! (UInt8.toNat s._gyro_count) (Binary32.toUInt16 ((Binary32.ofBits 0x46fffe00 /- (float)32767 -/) / Estimator_lib.radians_int32_t (2000 : Int32))) }
  let t'2 := s._gyro_count
  let saved : Bool := inp.gyro_id__gyro_count_loaded
  let mut t'4 := saved
  if t'4 then
    let t'3 := s._gyro_count
    t'4 := AP_ParamT_unsigned_int_3.op_to_unsigned_int s._gyro_id_old_param[UInt8.toNat t'3]! != id
  if t'4 then
    s := { s with _gyro_cal_ok := s._gyro_cal_ok.set! (UInt8.toNat s._gyro_count) false }
  let t'5 := s._gyro_count
  s := { s with _gyro_id_old_param := s._gyro_id_old_param.set! (UInt8.toNat t'5) (AP_ParamT_unsigned_int_3.set s._gyro_id_old_param[UInt8.toNat t'5]! id) }
  if !saved then
    let t'6 := s._gyro_count
    o := o.push (Output.AP_Param_save ("ins._gyro_id_old_param[" ++ (toString (UInt8.toNat t'6)) ++ "]") false)
  let t'7 := s._gyro_count
  s := { s with _gyro_count := s._gyro_count + (1 : UInt8) }
  «instance» := t'7
  return (s, o, «instance», true)

/-- C++ `bool AP_InertialSensor::register_accel(uint8_t & instance, uint16_t raw_sample_rate_hz, uint32_t id)`, `AP_InertialSensor/AP_InertialSensor.cpp:817-859`. -/
def register_accel (s : State) (o : Outputs) (inp : Inputs) («instance» : UInt8) (raw_sample_rate_hz : UInt16) (id : UInt32) : State × Outputs × UInt8 × Bool := Id.run do
  let mut s := s
  let mut o := o
  let mut «instance» := «instance»
  if UInt32.toInt32 (UInt8.toUInt32 s._accel_count) == ((3 : Int32) + (0 : Int32)) then
    o := o.push (Output.send_text (4 : UInt32) "Failed to register accel id %u" #[Sum.inl (UInt32.toUInt64 id)])
    return (s, o, «instance», false)
  let mut instance_to_check : UInt8 := Int8.toUInt8 (Int32.toInt8 (0 : Int32))
  for _ in [0:2^64] do  -- C loop without a constant trip count (--general-loops)
    if !(decide (UInt32.toInt32 (UInt8.toUInt32 instance_to_check) < UInt32.toInt32 (UInt8.toUInt32 s._accel_count))) then break
    let t'1 := instance_to_check
    if AP_ParamT_unsigned_int_3.op_to_unsigned_int s._accel_id_old_param[UInt8.toNat t'1]! == id then
      return (s, o, «instance», false)
    instance_to_check := instance_to_check + (1 : UInt8)
  s := { s with _accel_raw_sample_rates := s._accel_raw_sample_rates.set! (UInt8.toNat s._accel_count) (UInt16.toBinary32 raw_sample_rate_hz) }
  s := { s with _accel_over_sampling := s._accel_over_sampling.set! (UInt8.toNat s._accel_count) (Int8.toUInt8 (Int32.toInt8 (1 : Int32))) }
  s := { s with _accel_raw_sampling_multiplier := s._accel_raw_sampling_multiplier.set! (UInt8.toNat s._accel_count) (Binary32.toUInt16 ((Binary32.ofBits 0x46fffe00 /- (float)32767 -/) / ((Binary32.ofBits 0x41800000 /- 16 -/) * (Binary32.ofBits 0x411ce80a /- 9.80665016 -/)))) }
  let t'2 := s._accel_count
  let saved : Bool := inp.accel_id__accel_count_loaded
  if !saved then
    s := { s with _accel_id_ok := s._accel_id_ok.set! (UInt8.toNat s._accel_count) false }
  else
    let t'3 := s._accel_count
    if AP_ParamT_unsigned_int_3.op_to_unsigned_int s._accel_id_old_param[UInt8.toNat t'3]! != id then
      s := { s with _accel_id_ok := s._accel_id_ok.set! (UInt8.toNat s._accel_count) false }
    else
      s := { s with _accel_id_ok := s._accel_id_ok.set! (UInt8.toNat s._accel_count) true }
  let t'4 := s._accel_count
  s := { s with _accel_id_old_param := s._accel_id_old_param.set! (UInt8.toNat t'4) (AP_ParamT_unsigned_int_3.set s._accel_id_old_param[UInt8.toNat t'4]! id) }
  s := { s with _accel_id_ok := s._accel_id_ok.set! (UInt8.toNat s._accel_count) true }
  let t'5 := s._accel_count
  o := o.push (Output.AP_Param_save ("ins._accel_id_old_param[" ++ (toString (UInt8.toNat t'5)) ++ "]") false)
  let t'6 := s._accel_count
  s := { s with _accel_count := s._accel_count + (1 : UInt8) }
  «instance» := t'6
  return (s, o, «instance», true)

end AP_InertialSensor

namespace AP_InertialSensor_SITL

/-- C++ `void AP_InertialSensor_SITL::start()`, `reference/hal/sensors_ins.cpp:43-53`. -/
def start (s : State) (w : World) (o : Outputs) (self' : WPtr) : State × World × Outputs := Id.run do
  let mut s := s
  let mut w := w
  let mut o := o
  let t'1 := w.ins  -- the object out of the World for the call (--swap-out)
  w := { w with ins := default }
  let (t'2, t'3, t'4, t'5) := AP_InertialSensor.register_gyro t'1 o w.ins'inp s.gyro_instance s.gyro_sample_hz (AP_HAL.Device.make_bus_id Device.BusType.BUS_TYPE_SITL w.AP_InertialSensor_SITL'bus_id (Int8.toUInt8 (Int32.toInt8 (1 : Int32))) (UInt32.toUInt8 (AP_InertialSensor_Backend.DevTypes.toInt AP_InertialSensor_Backend.DevTypes.DEVTYPE_SITL)))
  w := { w with ins := t'2 }
  o := t'3
  s := { s with gyro_instance := t'4 }
  let mut t'11 := !t'5
  if !t'11 then
    let t'6 := w.ins  -- the object out of the World for the call (--swap-out)
    w := { w with ins := default }
    let (t'7, t'8, t'9, t'10) := AP_InertialSensor.register_accel t'6 o w.ins'inp s.accel_instance s.accel_sample_hz (AP_HAL.Device.make_bus_id Device.BusType.BUS_TYPE_SITL w.AP_InertialSensor_SITL'bus_id (Int8.toUInt8 (Int32.toInt8 (2 : Int32))) (UInt32.toUInt8 (AP_InertialSensor_Backend.DevTypes.toInt AP_InertialSensor_Backend.DevTypes.DEVTYPE_SITL)))
    w := { w with ins := t'7 }
    o := t'8
    s := { s with accel_instance := t'9 }
    t'11 := !t'10
  if t'11 then
    return (s, w, o)
  w := { w with AP_InertialSensor_SITL'bus_id := w.AP_InertialSensor_SITL'bus_id + (1 : UInt8) }
  let t'12 := w.est_scheduler  -- the object out of the World for the call (--swap-out)
  w := { w with est_scheduler := default }
  w := { w with est_scheduler := EstScheduler.register_timer_process t'12 (WFun.AP_InertialSensor_SITL_timer_update self') }
  return (s, w, o)

end AP_InertialSensor_SITL

namespace AP_InertialSensor

/-- C++ `void AP_InertialSensor::_start_backends()`, `AP_InertialSensor/AP_InertialSensor.cpp:865-887`. -/
def _start_backends (s : State) (w : World) (o : Outputs) : State × World × Outputs := Id.run do
  let mut s := s
  let mut w := w
  let mut o := o
  let (t'1, t'2) := detect_backends s w
  w := t'2
  s := t'1
  let t'3 : UInt8 := Int8.toUInt8 (Int32.toInt8 (0 : Int32))
  let t'4 : Int32 := UInt32.toInt32 (UInt8.toUInt32 s._backend_count)
  for i' in [0:(t'4.toInt - (Int.ofNat t'3.toNat)).toNat] do  -- C++ loop bounded by a runtime value (--runtime-loops)
    let i : UInt8 := t'3 + Nat.toUInt8 i'
    let t'5 := (WPtr.index s._backends[UInt8.toNat i]!)
    w := { w with ins := s }  -- this object's state into the World: the call reaches it
    let t'6 := w.heap'AP_InertialSensor_SITL[t'5]!  -- the object out of its slot for the call (--swap-out)
    w := { w with heap'AP_InertialSensor_SITL := w.heap'AP_InertialSensor_SITL.set! t'5 default }
    let (t'7, t'8, t'9) := AP_InertialSensor_SITL.start t'6 w o (WPtr.heap'AP_InertialSensor_SITL t'5)
    w := t'8
    w := { w with heap'AP_InertialSensor_SITL := w.heap'AP_InertialSensor_SITL.set! t'5 t'7 }
    o := t'9
    s := w.ins  -- this object's state as the call left it
  let t'10 : UInt8 := get_accel_count s
  let t'11 : Int32 := ((3 : Int32) + (0 : Int32))
  for i'2' in [0:(t'11.toInt - (Int.ofNat t'10.toNat)).toNat] do  -- C++ loop bounded by a runtime value (--runtime-loops)
    let i'2 : UInt8 := t'10 + Nat.toUInt8 i'2'
    let t'12 := i'2
    s := { s with _accel_id_old_param := s._accel_id_old_param.set! (UInt8.toNat t'12) (AP_ParamT_unsigned_int_3.set s._accel_id_old_param[UInt8.toNat t'12]! (Int32.toUInt32 (0 : Int32))) }
  let t'13 : UInt8 := get_gyro_count s
  let t'14 : Int32 := ((3 : Int32) + (0 : Int32))
  for i'3' in [0:(t'14.toInt - (Int.ofNat t'13.toNat)).toNat] do  -- C++ loop bounded by a runtime value (--runtime-loops)
    let i'3 : UInt8 := t'13 + Nat.toUInt8 i'3'
    let t'15 := i'3
    s := { s with _gyro_id_old_param := s._gyro_id_old_param.set! (UInt8.toNat t'15) (AP_ParamT_unsigned_int_3.set s._gyro_id_old_param[UInt8.toNat t'15]! (Int32.toUInt32 (0 : Int32))) }
  return (s, w, o)

/-- C++ `enum AP_InertialSensor::Gyro_Calibration_Timing`, `AP_InertialSensor/AP_InertialSensor.h:111-114`. -/
inductive Gyro_Calibration_Timing where
  | GYRO_CAL_NEVER
  | GYRO_CAL_STARTUP_ONLY
deriving DecidableEq, Inhabited

/-- The value of each enumerator of `AP_InertialSensor::Gyro_Calibration_Timing` (underlying type `uint32_t`). -/
def Gyro_Calibration_Timing.toInt : Gyro_Calibration_Timing → UInt32
  | .GYRO_CAL_NEVER => (0 : UInt32)
  | .GYRO_CAL_STARTUP_ONLY => (1 : UInt32)

/-- The enumerator of `AP_InertialSensor::Gyro_Calibration_Timing` with value `v` (the C++ converts only enumerator values; any other
value gives the first enumerator, the `Inhabited` default). -/
def Gyro_Calibration_Timing.ofInt (v : UInt32) : Gyro_Calibration_Timing :=
  if v == (0 : UInt32) then .GYRO_CAL_NEVER
  else if v == (1 : UInt32) then .GYRO_CAL_STARTUP_ONLY
  else default

/-- C++ `Gyro_Calibration_Timing AP_InertialSensor::gyro_calibration_timing()`, `AP_InertialSensor/AP_InertialSensor.cpp:2730-2736`. -/
def gyro_calibration_timing (s : State) (inp : Inputs) : AP_InertialSensor.Gyro_Calibration_Timing := Id.run do
  if inp.was_watchdog_reset then
    return AP_InertialSensor.Gyro_Calibration_Timing.GYRO_CAL_NEVER
  return AP_InertialSensor.Gyro_Calibration_Timing.ofInt (Int32.toUInt32 (Int8.toInt32 (AP_ParamT_signed_char_1.get_void s._gyro_cal_timing)))

/-- C++ `bool AP_InertialSensor::calibrating() const`, `AP_InertialSensor/AP_InertialSensor.cpp:2295-2306`. -/
def calibrating (s : State) : Bool := Id.run do
  if s._calibrating_accel || s._calibrating_gyro || s._trimming_accel then
    return true
  return false

end AP_InertialSensor

namespace AP_InertialSensor_SITL

/-- C++ `uint16_t AP_InertialSensor_Backend::get_gyro_backend_rate_hz() const`, `AP_InertialSensor/AP_InertialSensor_Backend.h:106-111` (a member of `AP_InertialSensor_Backend`, translated for `AP_InertialSensor_SITL`). -/
def get_gyro_backend_rate_hz (s : State) (w : World) : UInt16 := Id.run do
  if UInt32.toInt32 (UInt8.toUInt32 s.gyro_instance) ≥ ((3 : Int32) + (0 : Int32)) then
    return Int16.toUInt16 (Int32.toInt16 (0 : Int32))
  return Binary32.toUInt16 (_gyro_raw_sample_rate w s.gyro_instance)

end AP_InertialSensor_SITL

namespace AP_InertialSensor

/-- C++ `bool AP_InertialSensor::pre_arm_check_gyro_backend_rate_hz(char * fail_msg, uint16_t fail_msg_len) const`, `AP_InertialSensor/AP_InertialSensor.cpp:1472-1490`. -/
def pre_arm_check_gyro_backend_rate_hz (s : State) (w : World) (fail_msg : CText) (fail_msg_len : UInt16) : World × CText × Bool := Id.run do
  let mut w := w
  let mut fail_msg := fail_msg
  let gyro_count : UInt8 := get_gyro_count s
  let threshold : Binary32 := (Binary32.ofBits 0x3fe66666 /- 1.8 -/) * Int32.toBinary32 (UInt32.toInt32 (UInt16.toUInt32 s._loop_rate))
  for i' in [0:gyro_count.toNat] do
    let i : UInt8 := Nat.toUInt8 i'
    let t'1 := i
    let t'2 := t'1
    if !(AP_ParamT_signed_char_1.op_to_signed_char s._use_old_param[UInt8.toNat t'2]! != (0 : Int8)) || s._backends[UInt8.toNat i]! == WPtr.null then
      continue
    let t'3 := (WPtr.index s._backends[UInt8.toNat i]!)
    w := { w with ins := s }  -- this object's state into the World: the call reaches it
    let rate_hz : UInt16 := AP_InertialSensor_SITL.get_gyro_backend_rate_hz w.heap'AP_InertialSensor_SITL[t'3]! w
    let mut t'6 := decide (Int32.toBinary32 (UInt32.toInt32 (UInt16.toUInt32 rate_hz)) < threshold)
    if t'6 then
      let t'4 := i
      let t'5 := t'4
      t'6 := (UInt32.toInt32 (UInt8.toUInt32 (AP_HAL.Device.devid_get_devtype (AP_ParamT_unsigned_int_3.op_to_unsigned_int s._gyro_id_old_param[UInt8.toNat t'5]!))) != UInt32.toInt32 (AP_InertialSensor_Backend.DevTypes.toInt AP_InertialSensor_Backend.DevTypes.DEVTYPE_SERIAL))
    if t'6 then
      fail_msg := (CText.fmt (UInt16.toUInt64 fail_msg_len) "Gyro %d rate %dHz < loop rate*1.8 %dHz" #[Sum.inl (Int64.toUInt64 (Int32.toInt64 (UInt32.toInt32 (UInt8.toUInt32 i)))), Sum.inl (Int64.toUInt64 (Int32.toInt64 (UInt32.toInt32 (UInt16.toUInt32 rate_hz)))), Sum.inl (Int64.toUInt64 (Int32.toInt64 (Binary32.toInt32 threshold)))])
      return (w, fail_msg, false)
  return (w, fail_msg, true)

end AP_InertialSensor

namespace AP_InertialSensor

/-- C++ `bool AP_InertialSensor::get_output_banner(uint8_t instance_id, char * banner, uint8_t banner_len)`, `AP_InertialSensor/AP_InertialSensor.cpp:1395-1402`. -/
def get_output_banner (s : State) (w : World) (backend_id : UInt8) (banner : CText) (banner_len : UInt8) : CText × Bool := Id.run do
  let mut banner := banner
  if decide (UInt32.toInt32 (UInt8.toUInt32 backend_id) ≥ (2 : Int32) * ((3 : Int32) + (0 : Int32))) || s._backends[UInt8.toNat backend_id]! == WPtr.null then
    return (banner, false)
  let t'1 := (WPtr.index s._backends[UInt8.toNat backend_id]!)
  return (banner, AP_InertialSensor_SITL.get_output_banner banner_len)

end AP_InertialSensor

end Estimator_lib
