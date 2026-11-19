import ArduLean.Musl.atan2f
import ArduLean.Estimator.libraries.AP_Math.AP_Math
import ArduLean.Estimator.World
import ArduLean.Estimator.libraries.AP_Common.AP_Common
import ArduLean.Estimator.libraries.AP_Param.AP_Param
import ArduLean.Estimator.libraries.SITL.SITL
import ArduLean.Estimator.libraries.AP_Compass.AP_Compass
import ArduLean.Estimator.World_2
import ArduLean.Estimator.libraries.AP_Common.AP_Common_2
import ArduLean.Estimator.libraries.AP_Param.AP_Param_2
import ArduLean.Estimator.libraries.AP_Compass.AP_Compass_2
import ArduLean.Estimator.World_3
import ArduLean.Estimator.libraries.AP_Param.AP_Param_3

/-!
ArduPilot `libraries/AP_Compass`, part 3 of 4. Sources: `libraries/AP_Compass/AP_Compass_Backend.cpp`, `libraries/AP_Compass/AP_Compass.h`, `libraries/AP_Compass/AP_Compass.cpp`.

Items of `lean/Estimator_lib.lean` (the estimator translation), unchanged; placed by `tools/split_modules.py` (`ArduLean/Estimator/INDEX.md`).
-/

open FloatLib.Floats (Binary32 Binary64)

set_option maxRecDepth 200000
-- AP_DAL's `const log_RISH old_RISH = _RISH;` read only by WRITE_REPLAY_BLOCK_IFCHANGED, which is `(void)old`
-- without logging (HAL_LOGGING_ENABLED 0): an unused binding, as in the C++
set_option linter.unusedVariables false

namespace Estimator_lib

namespace Compass

/-- C++ `bool Compass::use_for_yaw(uint8_t i) const`, `AP_Compass/AP_Compass.cpp:1969-1979`. -/
def use_for_yaw_uint8_t (s : State) (i : UInt8) : Bool := Id.run do
  if !(available s) then
    return false
  let t'1 := typesafe_index_unsigned_char_TAG_Priority.init i
  return AP_ParamT_signed_char_1.op_to_signed_char s._use_for_yaw._priv_instance[UInt8.toNat (typesafe_index_unsigned_char_TAG_Priority.get_int t'1)]! != (0 : Int8) && AP_Enum_Compass_LearnType.op_to_Compass_LearnType s._learn != Compass.LearnType.INFLIGHT

/-- C++ `bool Compass::use_for_yaw() const`, `AP_Compass/AP_Compass.cpp:1962-1966`. -/
def use_for_yaw_void (s : State) : Bool := Id.run do
  return healthy_uint8_t s s._first_usable && use_for_yaw_uint8_t s s._first_usable

end Compass

namespace AP_Compass_SITL

/-- C++ `void AP_Compass_Backend::rotate_field(Vector3f & mag)`, `AP_Compass/AP_Compass_Backend.cpp:19-57` (a member of `AP_Compass_Backend`, translated for `AP_Compass_SITL`). -/
def rotate_field (s : State) (w : World) (mag : Vector3f.State) : Vector3f.State := Id.run do
  let mut mag := mag
  let t'1 := typesafe_index_unsigned_char_TAG_StateIndex.init s.«instance»
  if UInt32.toInt32 (UInt8.toUInt32 (Rotation.toInt Rotation.ROTATION_NONE)) != UInt32.toInt32 (UInt8.toUInt32 (Rotation.toInt Rotation.ROTATION_NONE)) then
    mag := Vector3f.rotate mag Rotation.ROTATION_NONE
  mag := Vector3f.rotate mag w.compass._state._priv_instance[UInt8.toNat (typesafe_index_unsigned_char_TAG_StateIndex.get_int t'1)]!.rotation
  if !(AP_ParamT_signed_char_1.op_to_signed_char w.compass._state._priv_instance[UInt8.toNat (typesafe_index_unsigned_char_TAG_StateIndex.get_int t'1)]!.external != (0 : Int8)) then
    mag := Vector3f.rotate mag w.compass._board_orientation
  else
    mag := Vector3f.rotate mag (Rotation.ofInt (Int8.toUInt8 (AP_ParamT_signed_char_1.get_void w.compass._state._priv_instance[UInt8.toNat (typesafe_index_unsigned_char_TAG_StateIndex.get_int t'1)]!.orientation)))
  return mag

end AP_Compass_SITL

namespace AP_Compass_SITL

/-- C++ `void AP_Compass_Backend::correct_field(Vector3f & mag)`, `AP_Compass/AP_Compass_Backend.cpp:74-135` (a member of `AP_Compass_Backend`, translated for `AP_Compass_SITL`). -/
def correct_field (s : State) (w : World) (inp : Inputs) (mag : Vector3f.State) : World × Vector3f.State := Id.run do
  let mut w := w
  let mut mag := mag
  let t'1 := typesafe_index_unsigned_char_TAG_StateIndex.init s.«instance»
  let (t'2, _) := Vector3f.op_add_assign mag w.compass._state._priv_instance[UInt8.toNat (typesafe_index_unsigned_char_TAG_StateIndex.get_int t'1)]!.offset._value
  mag := t'2
  if Compass.have_scale_factor w.compass s.«instance» then
    let (t'4, _) := Vector3f.op_mul_assign_float mag (AP_ParamT_float_4.op_to_float w.compass._state._priv_instance[UInt8.toNat (typesafe_index_unsigned_char_TAG_StateIndex.get_int t'1)]!.scale_factor)
    mag := t'4
  if !(Vector3f.is_zero w.compass._state._priv_instance[UInt8.toNat (typesafe_index_unsigned_char_TAG_StateIndex.get_int t'1)]!.diagonals._value) then
    let mat : Matrix3f.State := Matrix3f.init_float9 w.compass._state._priv_instance[UInt8.toNat (typesafe_index_unsigned_char_TAG_StateIndex.get_int t'1)]!.diagonals._value.x w.compass._state._priv_instance[UInt8.toNat (typesafe_index_unsigned_char_TAG_StateIndex.get_int t'1)]!.offdiagonals._value.x w.compass._state._priv_instance[UInt8.toNat (typesafe_index_unsigned_char_TAG_StateIndex.get_int t'1)]!.offdiagonals._value.y w.compass._state._priv_instance[UInt8.toNat (typesafe_index_unsigned_char_TAG_StateIndex.get_int t'1)]!.offdiagonals._value.x w.compass._state._priv_instance[UInt8.toNat (typesafe_index_unsigned_char_TAG_StateIndex.get_int t'1)]!.diagonals._value.y w.compass._state._priv_instance[UInt8.toNat (typesafe_index_unsigned_char_TAG_StateIndex.get_int t'1)]!.offdiagonals._value.z w.compass._state._priv_instance[UInt8.toNat (typesafe_index_unsigned_char_TAG_StateIndex.get_int t'1)]!.offdiagonals._value.y w.compass._state._priv_instance[UInt8.toNat (typesafe_index_unsigned_char_TAG_StateIndex.get_int t'1)]!.offdiagonals._value.z w.compass._state._priv_instance[UInt8.toNat (typesafe_index_unsigned_char_TAG_StateIndex.get_int t'1)]!.diagonals._value.z
    mag := Matrix3f.op_mul_Vector3f mat mag
  w := { w with compass._state._priv_instance := w.compass._state._priv_instance.set! (UInt8.toNat (typesafe_index_unsigned_char_TAG_StateIndex.get_int t'1)) ({ w.compass._state._priv_instance[UInt8.toNat (typesafe_index_unsigned_char_TAG_StateIndex.get_int t'1)]! with motor_offset := Vector3f.zero w.compass._state._priv_instance[UInt8.toNat (typesafe_index_unsigned_char_TAG_StateIndex.get_int t'1)]!.motor_offset }) }
  if Compass_PerMotor.enabled w.compass._per_motor && UInt32.toInt32 (UInt8.toUInt32 s.«instance») == (0 : Int32) then
    let (t'6, t'7) := Compass_PerMotor.compensate w.compass._per_motor w.compass'inp._per_motor w.compass._state._priv_instance[UInt8.toNat (typesafe_index_unsigned_char_TAG_StateIndex.get_int t'1)]!.motor_offset
    w := { w with compass._per_motor := t'6 }
    w := { w with compass._state._priv_instance := w.compass._state._priv_instance.set! (UInt8.toNat (typesafe_index_unsigned_char_TAG_StateIndex.get_int t'1)) ({ w.compass._state._priv_instance[UInt8.toNat (typesafe_index_unsigned_char_TAG_StateIndex.get_int t'1)]! with motor_offset := t'7 }) }
  else if Int8.toInt32 (AP_ParamT_signed_char_1.op_to_signed_char w.compass._motor_comp_type) == (1 : Int32) then
    w := { w with compass._state._priv_instance := w.compass._state._priv_instance.set! (UInt8.toNat (typesafe_index_unsigned_char_TAG_StateIndex.get_int t'1)) ({ w.compass._state._priv_instance[UInt8.toNat (typesafe_index_unsigned_char_TAG_StateIndex.get_int t'1)]! with motor_offset := Vector3f.op_mul_float w.compass._state._priv_instance[UInt8.toNat (typesafe_index_unsigned_char_TAG_StateIndex.get_int t'1)]!.motor_compensation._value w.compass._thr }) }
  else if Int8.toInt32 (AP_ParamT_signed_char_1.op_to_signed_char w.compass._motor_comp_type) == (2 : Int32) then
    let mut current : Binary32 := (Binary32.ofBits 0x00000000 /- 0.0 -/)  -- uninitialized in C++; assigned before every read
    current := inp.current_amps_current
    if inp.current_amps_0 then
      w := { w with compass._state._priv_instance := w.compass._state._priv_instance.set! (UInt8.toNat (typesafe_index_unsigned_char_TAG_StateIndex.get_int t'1)) ({ w.compass._state._priv_instance[UInt8.toNat (typesafe_index_unsigned_char_TAG_StateIndex.get_int t'1)]! with motor_offset := Vector3f.op_mul_float w.compass._state._priv_instance[UInt8.toNat (typesafe_index_unsigned_char_TAG_StateIndex.get_int t'1)]!.motor_compensation._value current }) }
  let (t'8, _) := Vector3f.op_add_assign mag w.compass._state._priv_instance[UInt8.toNat (typesafe_index_unsigned_char_TAG_StateIndex.get_int t'1)]!.motor_offset
  mag := t'8
  return (w, mag)

end AP_Compass_SITL

namespace AP_Compass_SITL

/-- C++ `bool AP_Compass_Backend::field_ok(const Vector3f & field)`, `AP_Compass/AP_Compass_Backend.cpp:261-294` (a member of `AP_Compass_Backend`, translated for `AP_Compass_SITL`). -/
def field_ok (s : State) (w : World) (field : Vector3f.State) : State × Bool := Id.run do
  let mut s := s
  if Vector3f.is_inf field || Vector3f.is_nan field then
    return (s, false)
  let range : Binary32 := UInt8.toBinary32 (Compass.get_filter_range w.compass)
  if range ≤ (Binary32.ofBits 0x00000000 /- 0 -/) then
    return (s, true)
  let length : Binary32 := Vector3f.length field
  if Estimator_lib.is_zero_float s._mean_field_length then
    s := { s with _mean_field_length := length }
    return (s, true)
  let mut ret : Bool := true
  let d : Binary32 := Binary32.abs (s._mean_field_length - length) / (s._mean_field_length + length)
  let mut koeff : Binary32 := Estimator_lib.FILTER_KOEF_compass
  if d * (Binary32.ofBits 0x43480000 /- 200.0f -/) > range then
    ret := false
    koeff := koeff / (d * (Binary32.ofBits 0x41200000 /- 10.0f -/))
    s := { s with _error_count := s._error_count + (1 : UInt32) }
  s := { s with _mean_field_length := s._mean_field_length * ((Binary32.ofBits 0x3f800000 /- 1 -/) - koeff) + length * koeff }
  return (s, ret)

end AP_Compass_SITL

namespace AP_Compass_SITL

/-- C++ `void AP_Compass_Backend::accumulate_sample(Vector3f & field, uint32_t max_samples)`, `AP_Compass/AP_Compass_Backend.cpp:137-162` (a member of `AP_Compass_Backend`, translated for `AP_Compass_SITL`). -/
def accumulate_sample (s : State) (w : World) (inp : Inputs) (field : Vector3f.State) (max_samples : UInt32 := Int32.toUInt32 (10 : Int32)) : State × World × Vector3f.State := Id.run do
  let mut s := s
  let mut w := w
  let mut field := field
  field := rotate_field s w field
  pure ()  -- C++ `publish_raw_field`: no effect in the model
  let (t'1, t'2) := correct_field s w inp field
  w := t'1
  field := t'2
  let (t'3, t'4) := field_ok s w field
  s := t'3
  if !t'4 then
    return (s, w, field)
  pure ()  -- C++ `_getsem19`: a semaphore, which does nothing here (one thread, --semaphores)
  let t'5 := typesafe_index_unsigned_char_TAG_StateIndex.init s.«instance»
  let (t'6, _) := Vector3f.op_add_assign w.compass._state._priv_instance[UInt8.toNat (typesafe_index_unsigned_char_TAG_StateIndex.get_int t'5)]!.accum field
  w := { w with compass._state._priv_instance := w.compass._state._priv_instance.set! (UInt8.toNat (typesafe_index_unsigned_char_TAG_StateIndex.get_int t'5)) ({ w.compass._state._priv_instance[UInt8.toNat (typesafe_index_unsigned_char_TAG_StateIndex.get_int t'5)]! with accum := t'6 }) }
  w := { w with compass._state._priv_instance := w.compass._state._priv_instance.set! (UInt8.toNat (typesafe_index_unsigned_char_TAG_StateIndex.get_int t'5)) ({ w.compass._state._priv_instance[UInt8.toNat (typesafe_index_unsigned_char_TAG_StateIndex.get_int t'5)]! with accum_count := w.compass._state._priv_instance[UInt8.toNat (typesafe_index_unsigned_char_TAG_StateIndex.get_int t'5)]!.accum_count + (1 : UInt32) }) }
  if max_samples != (0 : UInt32) && decide (w.compass._state._priv_instance[UInt8.toNat (typesafe_index_unsigned_char_TAG_StateIndex.get_int t'5)]!.accum_count ≥ max_samples) then
    w := { w with compass._state._priv_instance := w.compass._state._priv_instance.set! (UInt8.toNat (typesafe_index_unsigned_char_TAG_StateIndex.get_int t'5)) ({ w.compass._state._priv_instance[UInt8.toNat (typesafe_index_unsigned_char_TAG_StateIndex.get_int t'5)]! with accum_count := w.compass._state._priv_instance[UInt8.toNat (typesafe_index_unsigned_char_TAG_StateIndex.get_int t'5)]!.accum_count / Int32.toUInt32 (2 : Int32) }) }
    let (t'8, _) := Vector3f.op_div_assign w.compass._state._priv_instance[UInt8.toNat (typesafe_index_unsigned_char_TAG_StateIndex.get_int t'5)]!.accum (Binary32.ofBits 0x40000000 /- 2 -/)
    w := { w with compass._state._priv_instance := w.compass._state._priv_instance.set! (UInt8.toNat (typesafe_index_unsigned_char_TAG_StateIndex.get_int t'5)) ({ w.compass._state._priv_instance[UInt8.toNat (typesafe_index_unsigned_char_TAG_StateIndex.get_int t'5)]! with accum := t'8 }) }
  return (s, w, field)

/-- C++ `void AP_Compass_SITL::_timer()`, `reference/hal/sensors_compass.cpp:45-56`. -/
def _timer (s : State) (w : World) (inp : Inputs) : State × World := Id.run do
  let mut s := s
  let mut w := w
  if UInt32.toInt32 (UInt8.toUInt32 s.sitl_instance) != (0 : Int32) then
    return (s, w)
  let «in» : EstRecord := Estimator_lib.est_input w
  if !«in».mag then
    return (s, w)
  let mut field : Vector3f.State := «in».mag_mgauss
  let (t'1, t'2, t'3) := accumulate_sample s w inp field (Int32.toUInt32 (10 : Int32))
  w := t'2
  s := t'1
  field := t'3
  return (s, w)

end AP_Compass_SITL

namespace Compass

/-- C++ `const Vector3f & Compass::get_offsets(uint8_t i) const`, `AP_Compass/AP_Compass.h:207`. -/
def get_offsets_uint8_t (s : State) (i : UInt8) : Vector3f.State := Id.run do
  let t'1 := typesafe_index_unsigned_char_TAG_Priority.init i
  let t'2 := _get_state_id s t'1
  return AP_ParamV_Vector3_float_5.op_to_Vector3_float s._state._priv_instance[UInt8.toNat (typesafe_index_unsigned_char_TAG_StateIndex.get_int t'2)]!.offset

/-- C++ `uint8_t Compass::get_count() const`, `AP_Compass/AP_Compass.h:140`. -/
def get_count (s : State) : UInt8 := Id.run do
  return s._compass_count

/-- C++ `const Vector3f & Compass::get_field(uint8_t i) const`, `AP_Compass/AP_Compass.h:146`. -/
def get_field_uint8_t (s : State) (i : UInt8) : Vector3f.State := Id.run do
  let t'1 := typesafe_index_unsigned_char_TAG_Priority.init i
  let t'2 := _get_state_id s t'1
  return s._state._priv_instance[UInt8.toNat (typesafe_index_unsigned_char_TAG_StateIndex.get_int t'2)]!.field

/-- C++ `uint32_t Compass::last_update_usec(uint8_t i) const`, `AP_Compass/AP_Compass.h:325`. -/
def last_update_usec_uint8_t (s : State) (i : UInt8) : UInt32 := Id.run do
  let t'1 := typesafe_index_unsigned_char_TAG_Priority.init i
  let t'2 := _get_state_id s t'1
  return s._state._priv_instance[UInt8.toNat (typesafe_index_unsigned_char_TAG_StateIndex.get_int t'2)]!.last_update_usec

/-- C++ `bool Compass::learn_offsets_enabled() const`, `AP_Compass/AP_Compass.h:219`. -/
def learn_offsets_enabled (s : State) : Bool := Id.run do
  return AP_Enum_Compass_LearnType.op_to_Compass_LearnType s._learn == Compass.LearnType.INFLIGHT

/-- C++ `uint8_t Compass::get_num_enabled() const`, `AP_Compass/AP_Compass.cpp:1985-1997`. -/
def get_num_enabled (s : State) : UInt8 := Id.run do
  if UInt32.toInt32 (UInt8.toUInt32 (get_count s)) == (0 : Int32) then
    return Int8.toUInt8 (Int32.toInt8 (0 : Int32))
  let mut count : UInt8 := Int8.toUInt8 (Int32.toInt8 (0 : Int32))
  for i' in [0:3] do
    let i : UInt8 := Nat.toUInt8 i'
    if use_for_yaw_uint8_t s i then
      count := count + (1 : UInt8)
  return count

/-- C++ `uint8_t Compass::get_first_usable() const`, `AP_Compass/AP_Compass.h:390`. -/
def get_first_usable (s : State) : UInt8 := Id.run do
  return s._first_usable

end Compass

namespace Compass

/-- C++ `float Compass::get_declination() const`, `AP_Compass/AP_Compass.cpp:2009-2013`. -/
def get_declination (s : State) : Binary32 := Id.run do
  return AP_ParamT_float_4.get_void s._declination

/-- C++ `const Vector3f & Compass::get_field() const`, `AP_Compass/AP_Compass.h:147`. -/
def get_field_void (s : State) : Vector3f.State := Id.run do
  return get_field_uint8_t s s._first_usable

end Compass

namespace Compass

/-- C++ `bool Compass::consistent() const`, `AP_Compass/AP_Compass.cpp:2172-2209`. -/
def consistent (s : State) : Bool := Id.run do
  let primary_mag_field : Vector3f.State := get_field_void s
  let primary_mag_field_xy : Vector2f.State := Vector3f.xy primary_mag_field
  let mut i : UInt8 := Int8.toUInt8 (Int32.toInt8 (0 : Int32))
  let mut t'7 := true
  for _ in [0:2^64] do  -- C loop without a constant trip count (--general-loops)
    if t'7 then
      t'7 := false
    else
      i := i + (1 : UInt8)
    if !(decide (UInt32.toInt32 (UInt8.toUInt32 i) < UInt32.toInt32 (UInt8.toUInt32 (get_count s)))) then break
    if !(use_for_yaw_uint8_t s i) then
      continue
    let mag_field : Vector3f.State := get_field_uint8_t s i
    let mag_field_xy : Vector2f.State := Vector3f.xy mag_field
    if Vector2f.is_zero mag_field_xy then
      return false
    let xyz_ang_diff : Binary32 := Vector3f.angle mag_field primary_mag_field
    if xyz_ang_diff > Estimator_lib.radians_float (Binary32.ofBits 0x42b40000 /- 90 -/) then
      return false
    let xy_ang_diff : Binary32 := Vector2f.angle_Vector2f mag_field_xy primary_mag_field_xy
    if xy_ang_diff > Estimator_lib.radians_float (Binary32.ofBits 0x42700000 /- 60 -/) then
      return false
    let xy_len_diff : Binary32 := Vector2f.length (Vector2f.op_sub_Vector2f primary_mag_field_xy mag_field_xy)
    if xy_len_diff > (Binary32.ofBits 0x43480000 /- 200 -/) then
      return false
  return true

/-- C++ `bool Compass::auto_declination_enabled() const`, `AP_Compass/AP_Compass.h:241`. -/
def auto_declination_enabled (s : State) : Bool := Id.run do
  return Int8.toInt32 (AP_ParamT_signed_char_1.op_to_signed_char s._auto_declination) != (0 : Int32)

end Compass

namespace AP_Compass_SITL

/-- C++ `void AP_Compass_Backend::publish_filtered_field(const Vector3f & mag)`, `AP_Compass/AP_Compass_Backend.cpp:188-196` (a member of `AP_Compass_Backend`, translated for `AP_Compass_SITL`). -/
def publish_filtered_field (s : State) (w : World) (mag : Vector3f.State) : World := Id.run do
  let mut w := w
  let t'1 := typesafe_index_unsigned_char_TAG_StateIndex.init s.«instance»
  w := { w with compass._state._priv_instance := w.compass._state._priv_instance.set! (UInt8.toNat (typesafe_index_unsigned_char_TAG_StateIndex.get_int t'1)) ({ w.compass._state._priv_instance[UInt8.toNat (typesafe_index_unsigned_char_TAG_StateIndex.get_int t'1)]! with field := mag }) }
  w := { w with compass._state._priv_instance := w.compass._state._priv_instance.set! (UInt8.toNat (typesafe_index_unsigned_char_TAG_StateIndex.get_int t'1)) ({ w.compass._state._priv_instance[UInt8.toNat (typesafe_index_unsigned_char_TAG_StateIndex.get_int t'1)]! with last_update_ms := Estimator_lib.millis w }) }
  w := { w with compass._state._priv_instance := w.compass._state._priv_instance.set! (UInt8.toNat (typesafe_index_unsigned_char_TAG_StateIndex.get_int t'1)) ({ w.compass._state._priv_instance[UInt8.toNat (typesafe_index_unsigned_char_TAG_StateIndex.get_int t'1)]! with last_update_usec := Estimator_lib.micros w }) }
  return w

end AP_Compass_SITL

namespace AP_Compass_SITL

/-- C++ `void AP_Compass_Backend::drain_accumulated_samples(const Vector3f * scale)`, `AP_Compass/AP_Compass_Backend.cpp:164-183` (a member of `AP_Compass_Backend`, translated for `AP_Compass_SITL`). -/
def drain_accumulated_samples (s : State) (w : World) (scaling'given : Bool) (scaling : Vector3f.State) : World := Id.run do
  let mut w := w
  pure ()  -- C++ `_getsem20`: a semaphore, which does nothing here (one thread, --semaphores)
  let t'1 := typesafe_index_unsigned_char_TAG_StateIndex.init s.«instance»
  if w.compass._state._priv_instance[UInt8.toNat (typesafe_index_unsigned_char_TAG_StateIndex.get_int t'1)]!.accum_count == Int32.toUInt32 (0 : Int32) then
    return w
  if scaling'given then
    let (t'2, _) := Vector3f.op_mul_assign_Vector3f w.compass._state._priv_instance[UInt8.toNat (typesafe_index_unsigned_char_TAG_StateIndex.get_int t'1)]!.accum scaling
    w := { w with compass._state._priv_instance := w.compass._state._priv_instance.set! (UInt8.toNat (typesafe_index_unsigned_char_TAG_StateIndex.get_int t'1)) ({ w.compass._state._priv_instance[UInt8.toNat (typesafe_index_unsigned_char_TAG_StateIndex.get_int t'1)]! with accum := t'2 }) }
  let (t'4, _) := Vector3f.op_div_assign w.compass._state._priv_instance[UInt8.toNat (typesafe_index_unsigned_char_TAG_StateIndex.get_int t'1)]!.accum (UInt32.toBinary32 w.compass._state._priv_instance[UInt8.toNat (typesafe_index_unsigned_char_TAG_StateIndex.get_int t'1)]!.accum_count)
  w := { w with compass._state._priv_instance := w.compass._state._priv_instance.set! (UInt8.toNat (typesafe_index_unsigned_char_TAG_StateIndex.get_int t'1)) ({ w.compass._state._priv_instance[UInt8.toNat (typesafe_index_unsigned_char_TAG_StateIndex.get_int t'1)]! with accum := t'4 }) }
  w := publish_filtered_field s w w.compass._state._priv_instance[UInt8.toNat (typesafe_index_unsigned_char_TAG_StateIndex.get_int t'1)]!.accum
  w := { w with compass._state._priv_instance := w.compass._state._priv_instance.set! (UInt8.toNat (typesafe_index_unsigned_char_TAG_StateIndex.get_int t'1)) ({ w.compass._state._priv_instance[UInt8.toNat (typesafe_index_unsigned_char_TAG_StateIndex.get_int t'1)]! with accum := Vector3f.zero w.compass._state._priv_instance[UInt8.toNat (typesafe_index_unsigned_char_TAG_StateIndex.get_int t'1)]!.accum }) }
  w := { w with compass._state._priv_instance := w.compass._state._priv_instance.set! (UInt8.toNat (typesafe_index_unsigned_char_TAG_StateIndex.get_int t'1)) ({ w.compass._state._priv_instance[UInt8.toNat (typesafe_index_unsigned_char_TAG_StateIndex.get_int t'1)]! with accum_count := Int32.toUInt32 (0 : Int32) }) }
  return w

/-- C++ `void AP_Compass_Backend::read()`, `AP_Compass/AP_Compass_Backend.h:45-47` (a member of `AP_Compass_Backend`, translated for `AP_Compass_SITL`). -/
def read (s : State) (w : World) : World := Id.run do
  let mut w := w
  w := drain_accumulated_samples s w false {}
  return w

end AP_Compass_SITL

namespace Compass

/-- C++ `float Compass::calculate_heading(const Matrix3f & dcm_matrix, uint8_t i) const`, `AP_Compass/AP_Compass.cpp:2018-2070`. -/
def calculate_heading_Matrix3f_uint8_t (s : State) (dcm_matrix : Matrix3f.State) (i : UInt8) : Binary32 := Id.run do
  let cos_pitch_sq : Binary32 := (Binary32.ofBits 0x3f800000 /- 1.0f -/) - (dcm_matrix.c.x * dcm_matrix.c.x)
  let field : Vector3f.State := get_field_uint8_t s i
  let headY : Binary32 := field.y * dcm_matrix.c.z - field.z * dcm_matrix.c.y
  let headX : Binary32 := field.x * cos_pitch_sq - dcm_matrix.c.x * (field.y * dcm_matrix.c.y + field.z * dcm_matrix.c.z)
  let heading : Binary32 := Estimator_lib.constrain_value_line_float (Musl.atan2f.atan2f (-headY) headX) (-(Binary32.ofBits 0x40490fdb /- (float)884279719003555/281474976710656 -/)) (Binary32.ofBits 0x40490fdb /- (float)884279719003555/281474976710656 -/) (Int32.toUInt32 (2066 : Int32))
  return Estimator_lib.wrap_PI_float (heading + AP_ParamT_float_4.op_to_float s._declination)

/-- C++ `float Compass::calculate_heading(const Matrix3f & dcm_matrix) const`, `AP_Compass/AP_Compass.h:107-109`. -/
def calculate_heading_Matrix3f (s : State) (dcm_matrix : Matrix3f.State) : Binary32 := Id.run do
  return calculate_heading_Matrix3f_uint8_t s dcm_matrix s._first_usable

end Compass

namespace AP_Compass_SITL

/-- C++ `void AP_Compass_Backend::set_dev_id(uint32_t dev_id)`, `AP_Compass/AP_Compass_Backend.cpp:220-224` (a member of `AP_Compass_Backend`, translated for `AP_Compass_SITL`). -/
def set_dev_id (s : State) (w : World) (o : Outputs) (dev_id : UInt32) : World × Outputs := Id.run do
  let mut w := w
  let mut o := o
  let t'1 := typesafe_index_unsigned_char_TAG_StateIndex.init s.«instance»
  let (t'2, t'3) := AP_ParamT_unsigned_int_3.set_and_notify w.compass._state._priv_instance[UInt8.toNat (typesafe_index_unsigned_char_TAG_StateIndex.get_int t'1)]!.dev_id o ("compass._state._priv_instance[" ++ (toString (UInt8.toNat (typesafe_index_unsigned_char_TAG_StateIndex.get_int t'1))) ++ "].dev_id") dev_id
  w := { w with compass._state._priv_instance := w.compass._state._priv_instance.set! (UInt8.toNat (typesafe_index_unsigned_char_TAG_StateIndex.get_int t'1)) ({ w.compass._state._priv_instance[UInt8.toNat (typesafe_index_unsigned_char_TAG_StateIndex.get_int t'1)]! with dev_id := t'2 }) }
  o := t'3
  let t'4 := typesafe_index_unsigned_char_TAG_StateIndex.init s.«instance»
  w := { w with compass._state._priv_instance := w.compass._state._priv_instance.set! (UInt8.toNat (typesafe_index_unsigned_char_TAG_StateIndex.get_int t'4)) ({ w.compass._state._priv_instance[UInt8.toNat (typesafe_index_unsigned_char_TAG_StateIndex.get_int t'4)]! with detected_dev_id := dev_id }) }
  return (w, o)

/-- C++ `bool AP_Compass_Backend::register_compass(uint32_t dev_id)`, `AP_Compass/AP_Compass_Backend.cpp:208-215` (a member of `AP_Compass_Backend`, translated for `AP_Compass_SITL`). -/
def register_compass (s : State) (w : World) (o : Outputs) (dev_id : UInt32) : State × World × Outputs × Bool := Id.run do
  let mut s := s
  let mut w := w
  let mut o := o
  let t'1 := w.compass  -- the object out of the World for the call (--swap-out)
  w := { w with compass := default }
  let (t'2, t'3, t'4, t'5) := Compass.register_compass t'1 o dev_id s.«instance»
  w := { w with compass := t'2 }
  o := t'3
  s := { s with «instance» := t'4 }
  if !t'5 then
    return (s, w, o, false)
  let (t'6, t'7) := set_dev_id s w o dev_id
  w := t'6
  o := t'7
  return (s, w, o, true)

/-- C++ `void AP_Compass_Backend::save_dev_id()`, `AP_Compass/AP_Compass_Backend.cpp:229-232` (a member of `AP_Compass_Backend`, translated for `AP_Compass_SITL`). -/
def save_dev_id (s : State) (o : Outputs) : Outputs := Id.run do
  let mut o := o
  let t'1 := typesafe_index_unsigned_char_TAG_StateIndex.init s.«instance»
  o := o.push (Output.AP_Param_save ("compass._state._priv_instance[" ++ (toString (UInt8.toNat (typesafe_index_unsigned_char_TAG_StateIndex.get_int t'1))) ++ "].dev_id") false)
  return o

/-- C++ `void AP_Compass_Backend::set_rotation(enum Rotation rotation)`, `AP_Compass/AP_Compass_Backend.cpp:250-253` (a member of `AP_Compass_Backend`, translated for `AP_Compass_SITL`). -/
def set_rotation (s : State) (w : World) (rotation : Rotation) : World := Id.run do
  let mut w := w
  let t'1 := typesafe_index_unsigned_char_TAG_StateIndex.init s.«instance»
  w := { w with compass._state._priv_instance := w.compass._state._priv_instance.set! (UInt8.toNat (typesafe_index_unsigned_char_TAG_StateIndex.get_int t'1)) ({ w.compass._state._priv_instance[UInt8.toNat (typesafe_index_unsigned_char_TAG_StateIndex.get_int t'1)]! with rotation := rotation }) }
  return w

end AP_Compass_SITL

namespace AP_Compass_SITL

/-- C++ `void AP_Compass_Backend::set_external(bool external)`, `AP_Compass/AP_Compass_Backend.cpp:237-242` (a member of `AP_Compass_Backend`, translated for `AP_Compass_SITL`). -/
def set_external (s : State) (w : World) (o : Outputs) (external : Bool) : World × Outputs := Id.run do
  let mut w := w
  let mut o := o
  let t'1 := typesafe_index_unsigned_char_TAG_StateIndex.init s.«instance»
  if Int8.toInt32 (AP_ParamT_signed_char_1.op_to_signed_char w.compass._state._priv_instance[UInt8.toNat (typesafe_index_unsigned_char_TAG_StateIndex.get_int t'1)]!.external) != (2 : Int32) then
    let t'2 := typesafe_index_unsigned_char_TAG_StateIndex.init s.«instance»
    let (t'3, t'4) := AP_ParamT_signed_char_1.set_and_notify w.compass._state._priv_instance[UInt8.toNat (typesafe_index_unsigned_char_TAG_StateIndex.get_int t'2)]!.external o ("compass._state._priv_instance[" ++ (toString (UInt8.toNat (typesafe_index_unsigned_char_TAG_StateIndex.get_int t'2))) ++ "].external") (if external then (1 : Int8) else (0 : Int8))
    w := { w with compass._state._priv_instance := w.compass._state._priv_instance.set! (UInt8.toNat (typesafe_index_unsigned_char_TAG_StateIndex.get_int t'2)) ({ w.compass._state._priv_instance[UInt8.toNat (typesafe_index_unsigned_char_TAG_StateIndex.get_int t'2)]! with external := t'3 }) }
    o := t'4
  return (w, o)

end AP_Compass_SITL

namespace AP_Compass_SITL

/-- C++ `AP_Compass_SITL::AP_Compass_SITL(uint8_t sitl_instance)`, `reference/hal/sensors_compass.cpp:14-43`. -/
def init (w : World) (o : Outputs) (self' : WPtr) (_sitl_instance : UInt8) : State × World × Outputs := Id.run do
  let mut s : State := {}
  let mut w := w
  let mut o := o
  s := AP_Compass_Backend.init s
  s := { s with _sitl := WPtr.sitl }
  s := { s with sitl_instance := _sitl_instance }
  s := { s with _compass_sim := SITL.CompassSim.init s.sitl_instance }
  w := Estimator_lib.est_event w Estimator_lib.EST_EV_COMPASS_INIT
  if UInt8.toUInt64 s.sitl_instance > (8 : UInt64) then
    return (s, w, o)
  let dev_id : UInt32 := AP_ParamT_unsigned_int_3.op_to_unsigned_int w.sitl.mag_devid[UInt8.toNat s.sitl_instance]!
  if dev_id == Int32.toUInt32 (0 : Int32) then
    return (s, w, o)
  let (t'1, t'2, t'3, t'4) := register_compass s w o dev_id
  w := t'2
  s := t'1
  o := t'3
  if !t'4 then
    return (s, w, o)
  if AP_ParamT_signed_char_1.op_to_signed_char w.sitl.mag_save_ids != (0 : Int8) then
    o := save_dev_id s o
  w := set_rotation s w Rotation.ROTATION_NONE
  if Vector3f.is_zero (Compass.get_offsets_uint8_t w.compass s.«instance») then
    let t'5 := w.compass  -- the object out of the World for the call (--swap-out)
    w := { w with compass := default }
    w := { w with compass := Compass.set_offsets t'5 s.«instance» (AP_ParamV_Vector3_float_5.op_to_Vector3_float w.sitl.mag_ofs[UInt8.toNat s.sitl_instance]!) }
  -- C++ `AP_Param::set_default_by_name("COMPASS_SCALE", ...)`: not configured in storage (outside the model): set
  w := { w with compass._state._priv_instance := w.compass._state._priv_instance.set! 0 ({ w.compass._state._priv_instance[0]! with scale_factor._value := (Binary32.ofBits 0x3f800000 /- 1 -/) }) }
  -- C++ `AP_Param::set_default_by_name("COMPASS_SCALE2", ...)`: not configured in storage (outside the model): set
  w := { w with compass._state._priv_instance := w.compass._state._priv_instance.set! 1 ({ w.compass._state._priv_instance[1]! with scale_factor._value := (Binary32.ofBits 0x3f800000 /- 1 -/) }) }
  -- C++ `AP_Param::set_default_by_name("COMPASS_SCALE3", ...)`: not configured in storage (outside the model): set
  w := { w with compass._state._priv_instance := w.compass._state._priv_instance.set! 2 ({ w.compass._state._priv_instance[2]! with scale_factor._value := (Binary32.ofBits 0x3f800000 /- 1 -/) }) }
  if UInt32.toInt32 (UInt8.toUInt32 s.sitl_instance) == (0 : Int32) then
    let (t'6, t'7) := set_external s w o true
    w := t'6
    o := t'7
  let t'8 := w.est_scheduler  -- the object out of the World for the call (--swap-out)
  w := { w with est_scheduler := default }
  w := { w with est_scheduler := EstScheduler.register_timer_process t'8 (WFun.AP_Compass_SITL__timer self') }
  return (s, w, o)

end AP_Compass_SITL

namespace Compass

/-- C++ `void Compass::set_voltage(float voltage)`, `AP_Compass/AP_Compass.h:311-313`. -/
def set_voltage (s : State) (voltage : Binary32) : State := Id.run do
  let mut s := s
  s := { s with _per_motor := Compass_PerMotor.set_voltage s._per_motor voltage }
  return s

/-- C++ `const Vector3f & Compass::get_offsets() const`, `AP_Compass/AP_Compass.h:208`. -/
def get_offsets_void (s : State) : Vector3f.State := Id.run do
  return get_offsets_uint8_t s s._first_usable

/-- C++ `uint16_t Compass::get_offsets_max() const`, `AP_Compass/AP_Compass.h:363-365`. -/
def get_offsets_max (s : State) : UInt16 := Id.run do
  return AP_ParamT_unsigned_short_2.op_to_unsigned_short s._offset_max

end Compass

namespace Compass

/-- C++ `void Compass::set_learn_type(LearnType type, bool save)`, `AP_Compass/AP_Compass.h:354-360`. -/
def set_learn_type (s : State) (o : Outputs) (type : Compass.LearnType) (save : Bool) : State × Outputs := Id.run do
  let mut s := s
  let mut o := o
  if save then
    let (t'1, t'2) := AP_Enum_Compass_LearnType.set_and_save_LearnType s._learn o "compass._learn" type
    s := { s with _learn := t'1 }
    o := t'2
  else
    s := { s with _learn := AP_Enum_Compass_LearnType.set_LearnType s._learn type }
  return (s, o)

/-- C++ `void Compass::set_log_bit(uint32_t log_bit)`, `AP_Compass/AP_Compass.h:190`. -/
def set_log_bit (s : State) (log_bit : UInt32) : State := Id.run do
  let mut s := s
  s := { s with _log_bit := log_bit }
  return s

end Compass

end Estimator_lib
