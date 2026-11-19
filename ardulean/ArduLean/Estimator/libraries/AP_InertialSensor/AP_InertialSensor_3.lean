import ArduLean.Runtime.CFloat
import ArduLean.Estimator.libraries.AP_HAL.AP_HAL
import ArduLean.Estimator.libraries.AP_Math.AP_Math
import ArduLean.Estimator.World
import ArduLean.Estimator.libraries.Filter.Filter
import ArduLean.Estimator.libraries.AP_Param.AP_Param
import ArduLean.Estimator.libraries.AP_InertialSensor.AP_InertialSensor
import ArduLean.Estimator.World_2
import ArduLean.Estimator.libraries.AP_Param.AP_Param_2
import ArduLean.Estimator.World_3
import ArduLean.Estimator.libraries.AP_InertialSensor.AP_InertialSensor_2
import ArduLean.Estimator.World_4

/-!
ArduPilot `libraries/AP_InertialSensor`, part 3 of 3. Sources: `libraries/AP_InertialSensor/AP_InertialSensor.cpp`.

Items of `lean/Estimator_lib.lean` (the estimator translation), unchanged; placed by `tools/split_modules.py` (`ArduLean/Estimator/INDEX.md`).
-/

open FloatLib.Floats (Binary32 Binary64)

set_option maxRecDepth 200000
-- AP_DAL's `const log_RISH old_RISH = _RISH;` read only by WRITE_REPLAY_BLOCK_IFCHANGED, which is `(void)old`
-- without logging (HAL_LOGGING_ENABLED 0): an unused binding, as in the C++
set_option linter.unusedVariables false

namespace Estimator_lib

namespace AP_InertialSensor

-- not read in the Lean: goto'check_sample
set_option linter.unusedVariables false in
/-- C++ `void AP_InertialSensor::wait_for_sample()`, `AP_InertialSensor/AP_InertialSensor.cpp:2025-2164`. -/
def wait_for_sample (s : State) (w : World) (o : Outputs) : State × World × Outputs := Id.run do
  let mut s := s
  let mut w := w
  let mut o := o
  let mut goto'check_sample : Bool := false
  let sitl' : WPtr := WPtr.sitl
  if sitl' == WPtr.null then
    w := { w with ins := s }  -- this object's state into the World: the call reaches it
    let t'1 := w.est_scheduler  -- the object out of the World for the call (--swap-out)
    w := { w with est_scheduler := default }
    let (t'2, t'3, t'4) := EstScheduler.delay_microseconds t'1 w o (Int16.toUInt16 (Int32.toInt16 (1000 : Int32)))
    w := t'3
    w := { w with est_scheduler := t'2 }
    o := t'4
    s := w.ins  -- this object's state as the call left it
    return (s, w, o)
  if s._have_sample then
    return (s, w, o)
  let mut now : UInt32 := Estimator_lib.micros w
  for _ in [0:1] do
    if s._next_sample_usec == Int32.toUInt32 (0 : Int32) && decide (s._delta_time ≤ (Binary32.ofBits 0x00000000 /- 0 -/)) then
      s := { s with _last_sample_usec := now - s._sample_period_usec }
      s := { s with _next_sample_usec := now + s._sample_period_usec }
      goto'check_sample := true
      break
    if s._next_sample_usec - now ≤ s._sample_period_usec then
      let wait_usec : UInt32 := s._next_sample_usec - now
      w := { w with ins := s }  -- this object's state into the World: the call reaches it
      let t'5 := w.est_scheduler  -- the object out of the World for the call (--swap-out)
      w := { w with est_scheduler := default }
      let (t'6, t'7, t'8) := EstScheduler.delay_microseconds_boost t'5 w o (UInt32.toUInt16 wait_usec)
      w := t'7
      w := { w with est_scheduler := t'6 }
      o := t'8
      s := w.ins  -- this object's state as the call left it
      let now2 : UInt32 := Estimator_lib.micros w
      if now2 + Int32.toUInt32 (100 : Int32) < s._next_sample_usec then
        pure ()
      if now2 > s._next_sample_usec + Int32.toUInt32 (400 : Int32) then
        pure ()
      s := { s with _next_sample_usec := s._next_sample_usec + s._sample_period_usec }
    else if now - s._next_sample_usec < s._sample_period_usec / Int32.toUInt32 (8 : Int32) then
      s := { s with _next_sample_usec := s._next_sample_usec + s._sample_period_usec }
    else
      s := { s with _next_sample_usec := now + s._sample_period_usec }
  let mut gyro_available_mask : UInt8 := Int8.toUInt8 (Int32.toInt8 (0 : Int32))
  let mut accel_available_mask : UInt8 := Int8.toUInt8 (Int32.toInt8 (0 : Int32))
  let mut wait_counter : UInt32 := Int32.toUInt32 (0 : Int32)
  let wait_per_loop : UInt8 := Int8.toUInt8 (Int32.toInt8 (100 : Int32))
  let wait_counter_limit : UInt8 := UInt32.toUInt8 (Binary32.toUInt32 (s._loop_delta_t * (Binary32.ofBits 0x49742400 /- 1.0e6 -/)) / Int32.toUInt32 ((3 : Int32) * UInt32.toInt32 (UInt8.toUInt32 wait_per_loop)))
  for _ in [0:2^64] do  -- C loop without a constant trip count (--general-loops)
    if !true then break
    let t'9 : UInt8 := Int8.toUInt8 (Int32.toInt8 (0 : Int32))
    let t'10 : Int32 := UInt32.toInt32 (UInt8.toUInt32 s._backend_count)
    for i' in [0:(t'10.toInt - (Int.ofNat t'9.toNat)).toNat] do  -- C++ loop bounded by a runtime value (--runtime-loops)
      let i : UInt8 := t'9 + Nat.toUInt8 i'
      let t'11 := (WPtr.index s._backends[UInt8.toNat i]!)
      pure ()  -- C++ `accumulate`: no effect in the model
    let mut i'2 : UInt8 := Int8.toUInt8 (Int32.toInt8 (0 : Int32))
    for _ in [0:2^64] do  -- C loop without a constant trip count (--general-loops)
      if !(decide (UInt32.toInt32 (UInt8.toUInt32 i'2) < UInt32.toInt32 (UInt8.toUInt32 s._gyro_count))) then break
      if s._new_gyro_data[UInt8.toNat i'2]! then
        let imask : UInt8 := UInt32.toUInt8 ((1 : UInt32) <<< Int32.toUInt32 (UInt32.toInt32 (UInt8.toUInt32 i'2)))
        gyro_available_mask := Int8.toUInt8 (Int32.toInt8 (UInt32.toInt32 (UInt8.toUInt32 gyro_available_mask) ||| UInt32.toInt32 (UInt8.toUInt32 imask)))
        let t'12 := i'2
        if AP_ParamT_signed_char_1.op_to_signed_char s._use_old_param[UInt8.toNat t'12]! != (0 : Int8) then
          s := { s with _gyro_wait_mask := Int8.toUInt8 (Int32.toInt8 (UInt32.toInt32 (UInt8.toUInt32 s._gyro_wait_mask) ||| UInt32.toInt32 (UInt8.toUInt32 imask))) }
        else
          s := { s with _gyro_wait_mask := Int8.toUInt8 (Int32.toInt8 (UInt32.toInt32 (UInt8.toUInt32 s._gyro_wait_mask) &&& ~~~(UInt32.toInt32 (UInt8.toUInt32 imask)))) }
      i'2 := i'2 + (1 : UInt8)
    let mut i'3 : UInt8 := Int8.toUInt8 (Int32.toInt8 (0 : Int32))
    for _ in [0:2^64] do  -- C loop without a constant trip count (--general-loops)
      if !(decide (UInt32.toInt32 (UInt8.toUInt32 i'3) < UInt32.toInt32 (UInt8.toUInt32 s._accel_count))) then break
      if s._new_accel_data[UInt8.toNat i'3]! then
        let imask'2 : UInt8 := UInt32.toUInt8 ((1 : UInt32) <<< Int32.toUInt32 (UInt32.toInt32 (UInt8.toUInt32 i'3)))
        accel_available_mask := Int8.toUInt8 (Int32.toInt8 (UInt32.toInt32 (UInt8.toUInt32 accel_available_mask) ||| UInt32.toInt32 (UInt8.toUInt32 imask'2)))
        let t'13 := i'3
        if AP_ParamT_signed_char_1.op_to_signed_char s._use_old_param[UInt8.toNat t'13]! != (0 : Int8) then
          s := { s with _accel_wait_mask := Int8.toUInt8 (Int32.toInt8 (UInt32.toInt32 (UInt8.toUInt32 s._accel_wait_mask) ||| UInt32.toInt32 (UInt8.toUInt32 imask'2))) }
        else
          s := { s with _accel_wait_mask := Int8.toUInt8 (Int32.toInt8 (UInt32.toInt32 (UInt8.toUInt32 s._accel_wait_mask) &&& ~~~(UInt32.toInt32 (UInt8.toUInt32 imask'2)))) }
      i'3 := i'3 + (1 : UInt8)
    if wait_counter < UInt8.toUInt32 wait_counter_limit then
      if gyro_available_mask != (0 : UInt8) && ((UInt32.toInt32 (UInt8.toUInt32 gyro_available_mask) &&& UInt32.toInt32 (UInt8.toUInt32 s._gyro_wait_mask)) == UInt32.toInt32 (UInt8.toUInt32 s._gyro_wait_mask)) && accel_available_mask != (0 : UInt8) && ((UInt32.toInt32 (UInt8.toUInt32 accel_available_mask) &&& UInt32.toInt32 (UInt8.toUInt32 s._accel_wait_mask)) == UInt32.toInt32 (UInt8.toUInt32 s._accel_wait_mask)) then
        break
    else
      if gyro_available_mask != (0 : UInt8) && accel_available_mask != (0 : UInt8) then
        s := { s with _gyro_wait_mask := Int8.toUInt8 (Int32.toInt8 (UInt32.toInt32 (UInt8.toUInt32 s._gyro_wait_mask) &&& UInt32.toInt32 (UInt8.toUInt32 gyro_available_mask))) }
        s := { s with _accel_wait_mask := Int8.toUInt8 (Int32.toInt8 (UInt32.toInt32 (UInt8.toUInt32 s._accel_wait_mask) &&& UInt32.toInt32 (UInt8.toUInt32 accel_available_mask))) }
        break
    w := { w with ins := s }  -- this object's state into the World: the call reaches it
    let t'14 := w.est_scheduler  -- the object out of the World for the call (--swap-out)
    w := { w with est_scheduler := default }
    let (t'15, t'16, t'17) := EstScheduler.delay_microseconds_boost t'14 w o (UInt8.toUInt16 wait_per_loop)
    w := t'16
    w := { w with est_scheduler := t'15 }
    o := t'17
    s := w.ins  -- this object's state as the call left it
    wait_counter := wait_counter + (1 : UInt32)
  now := Estimator_lib.micros w
  s := { s with _delta_time := UInt32.toBinary32 (now - s._last_sample_usec) * (Binary32.ofBits 0x358637bd /- 1.0e-6f -/) }
  s := { s with _last_sample_usec := now }
  s := { s with _have_sample := true }
  return (s, w, o)

end AP_InertialSensor

namespace AP_InertialSensor

/-- C++ `void AP_InertialSensor::update()`, `AP_InertialSensor/AP_InertialSensor.cpp:1913-2010`. -/
def update (s : State) (w : World) (o : Outputs) : State × World × Outputs := Id.run do
  let mut s := s
  let mut w := w
  let mut o := o
  let (t'1, t'2, t'3) := wait_for_sample s w o
  w := t'2
  s := t'1
  o := t'3
  for i' in [0:3] do
    let i : UInt8 := Nat.toUInt8 i'
    s := { s with _delta_velocity_valid := s._delta_velocity_valid.set! (UInt8.toNat i) false }
    s := { s with _delta_angle_valid := s._delta_angle_valid.set! (UInt8.toNat i) false }
  let t'4 : UInt8 := Int8.toUInt8 (Int32.toInt8 (0 : Int32))
  let t'5 : Int32 := UInt32.toInt32 (UInt8.toUInt32 s._backend_count)
  for i'2' in [0:(t'5.toInt - (Int.ofNat t'4.toNat)).toNat] do  -- C++ loop bounded by a runtime value (--runtime-loops)
    let i'2 : UInt8 := t'4 + Nat.toUInt8 i'2'
    let t'6 := (WPtr.index s._backends[UInt8.toNat i'2]!)
    w := { w with ins := s }  -- this object's state into the World: the call reaches it
    let t'7 := w.heap'AP_InertialSensor_SITL[t'6]!  -- the object out of its slot for the call (--swap-out)
    w := { w with heap'AP_InertialSensor_SITL := w.heap'AP_InertialSensor_SITL.set! t'6 default }
    let (t'8, t'9, _) := AP_InertialSensor_SITL.update t'7 w w.heap'AP_InertialSensor_SITL'inp
    w := t'9
    w := { w with heap'AP_InertialSensor_SITL := w.heap'AP_InertialSensor_SITL.set! t'6 t'8 }
    s := w.ins  -- this object's state as the call left it
  if !s._startup_error_counts_set then
    for i'3' in [0:3] do
      let i'3 : UInt8 := Nat.toUInt8 i'3'
      s := { s with _accel_startup_error_count := s._accel_startup_error_count.set! (UInt8.toNat i'3) (s._accel_error_count[UInt8.toNat i'3]!) }
      s := { s with _gyro_startup_error_count := s._gyro_startup_error_count.set! (UInt8.toNat i'3) (s._gyro_error_count[UInt8.toNat i'3]!) }
    if s._startup_ms == Int32.toUInt32 (0 : Int32) then
      s := { s with _startup_ms := Estimator_lib.millis w }
    else if Estimator_lib.millis w - s._startup_ms > Int32.toUInt32 (2000 : Int32) then
      s := { s with _startup_error_counts_set := true }
  for i'4' in [0:3] do
    let i'4 : UInt8 := Nat.toUInt8 i'4'
    if s._accel_error_count[UInt8.toNat i'4]! < s._accel_startup_error_count[UInt8.toNat i'4]! then
      s := { s with _accel_startup_error_count := s._accel_startup_error_count.set! (UInt8.toNat i'4) (s._accel_error_count[UInt8.toNat i'4]!) }
    if s._gyro_error_count[UInt8.toNat i'4]! < s._gyro_startup_error_count[UInt8.toNat i'4]! then
      s := { s with _gyro_startup_error_count := s._gyro_startup_error_count.set! (UInt8.toNat i'4) (s._gyro_error_count[UInt8.toNat i'4]!) }
  let mut have_zero_accel_error_count : Bool := false
  let mut have_zero_gyro_error_count : Bool := false
  for i'5' in [0:3] do
    let i'5 : UInt8 := Nat.toUInt8 i'5'
    if s._accel_healthy[UInt8.toNat i'5]! && decide (s._accel_error_count[UInt8.toNat i'5]! ≤ s._accel_startup_error_count[UInt8.toNat i'5]!) then
      have_zero_accel_error_count := true
    if s._gyro_healthy[UInt8.toNat i'5]! && decide (s._gyro_error_count[UInt8.toNat i'5]! ≤ s._gyro_startup_error_count[UInt8.toNat i'5]!) then
      have_zero_gyro_error_count := true
  for i'6' in [0:3] do
    let i'6 : UInt8 := Nat.toUInt8 i'6'
    if s._gyro_healthy[UInt8.toNat i'6]! && decide (s._gyro_error_count[UInt8.toNat i'6]! > s._gyro_startup_error_count[UInt8.toNat i'6]!) && have_zero_gyro_error_count then
      s := { s with _gyro_healthy := s._gyro_healthy.set! (UInt8.toNat i'6) false }
    if s._accel_healthy[UInt8.toNat i'6]! && decide (s._accel_error_count[UInt8.toNat i'6]! > s._accel_startup_error_count[UInt8.toNat i'6]!) && have_zero_accel_error_count then
      s := { s with _accel_healthy := s._accel_healthy.set! (UInt8.toNat i'6) false }
  for i'7' in [0:3] do
    let i'7 : UInt8 := Nat.toUInt8 i'7'
    let mut t'12 := s._gyro_healthy[UInt8.toNat i'7]!
    if t'12 then
      let t'11 := i'7
      t'12 := AP_ParamT_signed_char_1.op_to_signed_char s._use_old_param[UInt8.toNat t'11]! != (0 : Int8)
    if t'12 then
      s := { s with _first_usable_gyro := i'7 }
      break
  for i'8' in [0:3] do
    let i'8 : UInt8 := Nat.toUInt8 i'8'
    let mut t'14 := s._accel_healthy[UInt8.toNat i'8]!
    if t'14 then
      let t'13 := i'8
      t'14 := AP_ParamT_signed_char_1.op_to_signed_char s._use_old_param[UInt8.toNat t'13]! != (0 : Int8)
    if t'14 then
      s := { s with _first_usable_accel := i'8 }
      break
  s := { s with _last_update_usec := Estimator_lib.micros w }
  s := { s with _have_sample := false }
  if (s.uart.imu_out_uart != WPtr.null) then
    pure ()  -- C++ `AP_InertialSensor::send_uart_data(...)`: left out (--drop)
  return (s, w, o)

/-- C++ `const Vector3f & AP_InertialSensor::get_accel(uint8_t i) const`, `AP_InertialSensor/AP_InertialSensor.h:181`. -/
def get_accel_uint8_t (s : State) (i : UInt8) : Vector3f.State := Id.run do
  return s._accel[UInt8.toNat i]!

/-- C++ `const Vector3f & AP_InertialSensor::get_accel() const`, `AP_InertialSensor/AP_InertialSensor.h:182`. -/
def get_accel_void (s : State) : Vector3f.State := Id.run do
  return get_accel_uint8_t s s._first_usable_accel

end AP_InertialSensor

namespace AP_InertialSensor

-- not read in the Lean: c, _getdelay21
set_option linter.unusedVariables false in
/-- C++ `void AP_InertialSensor::_init_gyro()`, `AP_InertialSensor/AP_InertialSensor.cpp:1708-1857`. -/
def _init_gyro (s : State) (w : World) (o : Outputs) : State × World × Outputs := Id.run do
  let mut s := s
  let mut w := w
  let mut o := o
  let num_gyros : UInt8 := Int8.toUInt8 (Int32.toInt8 (Estimator_lib.MIN_uint8_t_int32_t (get_gyro_count s) ((3 : Int32) + (0 : Int32))))
  let mut last_average : Array Vector3f.State := Array.replicate 3 {}  -- each element default-constructed (zero)
  let mut best_avg : Array Vector3f.State := Array.replicate 3 {}  -- each element default-constructed (zero)
  let mut new_gyro_offset : Array Vector3f.State := Array.replicate 3 {}  -- each element default-constructed (zero)
  let mut best_diff : Array Binary32 := Array.replicate 3 (Binary32.ofBits 0x00000000 /- 0.0 -/)  -- uninitialized in C; every element is written before it is read
  let mut converged : Array Bool := Array.replicate 3 false  -- uninitialized in C; every element is written before it is read
  if calibrating s then
    return (s, w, o)
  s := { s with _calibrating_gyro := true }
  o := o.push (Output.AP_Notify_flags_initialising true)
  for _ in [0:1] do
    o := o.push (Output.console_printf "Init Gyro" #[])
  for k' in [0:num_gyros.toNat] do
    let k : UInt8 := Nat.toUInt8 k'
    let t'1 := k
    s := { s with _gyro_offset_old_param := s._gyro_offset_old_param.set! (UInt8.toNat t'1) (AP_ParamV_Vector3_float_5.set s._gyro_offset_old_param[UInt8.toNat t'1]! Vector3f.init_void) }
    new_gyro_offset := new_gyro_offset.set! (UInt8.toNat k) (Vector3f.zero new_gyro_offset[UInt8.toNat k]!)
    best_diff := best_diff.set! (UInt8.toNat k) (-(Binary32.ofBits 0x3f800000 /- 1.f -/))
    last_average := last_average.set! (UInt8.toNat k) (Vector3f.zero last_average[UInt8.toNat k]!)
    converged := converged.set! (UInt8.toNat k) false
  for _ in [0:5] do
    w := { w with ins := s }  -- this object's state into the World: the call reaches it
    let t'2 := w.est_scheduler  -- the object out of the World for the call (--swap-out)
    w := { w with est_scheduler := default }
    let (t'3, t'4, t'5) := EstScheduler.delay t'2 w o (Int16.toUInt16 (Int32.toInt16 (5 : Int32)))
    w := t'4
    w := { w with est_scheduler := t'3 }
    o := t'5
    s := w.ins  -- this object's state as the call left it
    let (t'6, t'7, t'8) := update s w o
    w := t'7
    s := t'6
    o := t'8
  let mut num_converged : UInt8 := Int8.toUInt8 (Int32.toInt8 (0 : Int32))
  let mut j : Int16 := Int32.toInt16 (0 : Int32)
  let mut t'19 := true
  for _ in [0:2^64] do  -- C loop without a constant trip count (--general-loops)
    if t'19 then
      t'19 := false
    else
      j := j + (1 : Int16)
    if !(decide (Int16.toInt32 j ≤ (30 : Int32) * (4 : Int32)) && decide (UInt32.toInt32 (UInt8.toUInt32 num_converged) < UInt32.toInt32 (UInt8.toUInt32 num_gyros))) then break
    let mut gyro_sum : Array Vector3f.State := Array.replicate 3 {}  -- each element default-constructed (zero)
    let mut gyro_avg : Array Vector3f.State := Array.replicate 3 {}  -- each element default-constructed (zero)
    let mut gyro_diff : Array Vector3f.State := Array.replicate 3 {}  -- each element default-constructed (zero)
    let mut accel_start : Vector3f.State := Vector3f.init_void
    let mut diff_norm : Array Binary32 := Array.replicate 3 (Binary32.ofBits 0x00000000 /- 0.0 -/)  -- uninitialized in C; every element is written before it is read
    let mut i : UInt8 := (0 : UInt8)  -- uninitialized in C++; assigned before every read
    let _getdelay21 : ExpectDelay.State := ExpectDelay.init (Int32.toUInt32 (1000 : Int32))
    diff_norm := Array.replicate 3 (Binary32.ofBits 0x00000000 /- 0.0 -/)
    for _ in [0:1] do
      o := o.push (Output.console_printf "*" #[])
    for k'2' in [0:num_gyros.toNat] do
      let k'2 : UInt8 := Nat.toUInt8 k'2'
      gyro_sum := gyro_sum.set! (UInt8.toNat k'2) (Vector3f.zero gyro_sum[UInt8.toNat k'2]!)
    accel_start := get_accel_uint8_t s (Int8.toUInt8 (Int32.toInt8 (0 : Int32)))
    i := Int8.toUInt8 (Int32.toInt8 (0 : Int32))
    for _ in [0:2^64] do  -- C loop without a constant trip count (--general-loops)
      if !(decide (UInt32.toInt32 (UInt8.toUInt32 i) < (50 : Int32))) then break
      let (t'9, t'10, t'11) := update s w o
      w := t'10
      s := t'9
      o := t'11
      for k'3' in [0:num_gyros.toNat] do
        let k'3 : UInt8 := Nat.toUInt8 k'3'
        let (t'12, _) := Vector3f.op_add_assign gyro_sum[UInt8.toNat k'3]! (get_gyro_uint8_t s k'3)
        gyro_sum := gyro_sum.set! (UInt8.toNat k'3) t'12
      w := { w with ins := s }  -- this object's state into the World: the call reaches it
      let t'14 := w.est_scheduler  -- the object out of the World for the call (--swap-out)
      w := { w with est_scheduler := default }
      let (t'15, t'16, t'17) := EstScheduler.delay t'14 w o (Int16.toUInt16 (Int32.toInt16 (5 : Int32)))
      w := t'16
      w := { w with est_scheduler := t'15 }
      o := t'17
      s := w.ins  -- this object's state as the call left it
      i := i + (1 : UInt8)
    let t'18 := Int8.toUInt8 (Int32.toInt8 (0 : Int32))
    let accel_diff : Vector3f.State := Vector3f.op_sub_Vector3f s._accel[UInt8.toNat t'18]! accel_start
    if Vector3f.length accel_diff > (Binary32.ofBits 0x3e4ccccd /- 0.2f -/) then
      continue
    for k'4' in [0:num_gyros.toNat] do
      let k'4 : UInt8 := Nat.toUInt8 k'4'
      gyro_avg := gyro_avg.set! (UInt8.toNat k'4) (Vector3f.op_div gyro_sum[UInt8.toNat k'4]! (UInt8.toBinary32 i))
      gyro_diff := gyro_diff.set! (UInt8.toNat k'4) (Vector3f.op_sub_Vector3f last_average[UInt8.toNat k'4]! gyro_avg[UInt8.toNat k'4]!)
      diff_norm := diff_norm.set! (UInt8.toNat k'4) (Vector3f.length gyro_diff[UInt8.toNat k'4]!)
    for k'5' in [0:num_gyros.toNat] do
      let k'5 : UInt8 := Nat.toUInt8 k'5'
      if best_diff[UInt8.toNat k'5]! < (Binary32.ofBits 0x00000000 /- 0 -/) then
        best_diff := best_diff.set! (UInt8.toNat k'5) (diff_norm[UInt8.toNat k'5]!)
        best_avg := best_avg.set! (UInt8.toNat k'5) (gyro_avg[UInt8.toNat k'5]!)
      else if Vector3f.length gyro_diff[UInt8.toNat k'5]! < Estimator_lib.radians_float (Binary32.ofBits 0x3dcccccd /- 0.100000001 -/) then
        last_average := last_average.set! (UInt8.toNat k'5) (Vector3f.op_add (Vector3f.op_mul_float gyro_avg[UInt8.toNat k'5]! (Binary32.ofBits 0x3f000000 /- 0.5f -/)) (Vector3f.op_mul_float last_average[UInt8.toNat k'5]! (Binary32.ofBits 0x3f000000 /- 0.5f -/)))
        if !converged[UInt8.toNat k'5]! || decide (Vector3f.length last_average[UInt8.toNat k'5]! < Vector3f.length new_gyro_offset[UInt8.toNat k'5]!) then
          new_gyro_offset := new_gyro_offset.set! (UInt8.toNat k'5) (last_average[UInt8.toNat k'5]!)
        if !converged[UInt8.toNat k'5]! then
          converged := converged.set! (UInt8.toNat k'5) true
          num_converged := num_converged + (1 : UInt8)
      else if diff_norm[UInt8.toNat k'5]! < best_diff[UInt8.toNat k'5]! then
        best_diff := best_diff.set! (UInt8.toNat k'5) (diff_norm[UInt8.toNat k'5]!)
        best_avg := best_avg.set! (UInt8.toNat k'5) (Vector3f.op_add (Vector3f.op_mul_float gyro_avg[UInt8.toNat k'5]! (Binary32.ofBits 0x3f000000 /- 0.5f -/)) (Vector3f.op_mul_float last_average[UInt8.toNat k'5]! (Binary32.ofBits 0x3f000000 /- 0.5f -/)))
      last_average := last_average.set! (UInt8.toNat k'5) (gyro_avg[UInt8.toNat k'5]!)
  for _ in [0:1] do
    o := o.push (Output.console_printf "\x0a" #[])
  for k'6' in [0:num_gyros.toNat] do
    let k'6 : UInt8 := Nat.toUInt8 k'6'
    if !converged[UInt8.toNat k'6]! then
      for _ in [0:1] do
        o := o.push (Output.console_printf "gyro[%u] did not converge: diff=%f dps (expected < %f)\x0a" #[Sum.inl (UInt32.toUInt64 (UInt8.toUInt32 k'6)), Sum.inl (Binary64.toBits (Binary32.toBinary64 (Estimator_lib.degrees best_diff[UInt8.toNat k'6]!))), Sum.inl (Binary64.toBits (Binary64.ofBits 0x3fb99999a0000000 /- (double)13421773/134217728 -/))])
      let t'20 := k'6
      s := { s with _gyro_offset_old_param := s._gyro_offset_old_param.set! (UInt8.toNat t'20) (AP_ParamV_Vector3_float_5.set s._gyro_offset_old_param[UInt8.toNat t'20]! best_avg[UInt8.toNat k'6]!) }
      s := { s with _gyro_cal_ok := s._gyro_cal_ok.set! (UInt8.toNat k'6) false }
    else
      s := { s with _gyro_cal_ok := s._gyro_cal_ok.set! (UInt8.toNat k'6) true }
      let t'21 := k'6
      s := { s with _gyro_offset_old_param := s._gyro_offset_old_param.set! (UInt8.toNat t'21) (AP_ParamV_Vector3_float_5.set s._gyro_offset_old_param[UInt8.toNat t'21]! new_gyro_offset[UInt8.toNat k'6]!) }
  s := { s with _calibrating_gyro := false }
  o := o.push (Output.AP_Notify_flags_initialising false)
  o := o.push (Output.AP_Notify_flags_gyro_calibrated true)
  return (s, w, o)

end AP_InertialSensor

namespace AP_InertialSensor

/-- C++ `void AP_InertialSensor::_save_gyro_calibration()`, `AP_InertialSensor/AP_InertialSensor.cpp:1860-1876`. -/
def _save_gyro_calibration (s : State) (o : Outputs) : State × Outputs := Id.run do
  let mut s := s
  let mut o := o
  let mut i : UInt8 := Int8.toUInt8 (Int32.toInt8 (0 : Int32))
  for _ in [0:2^64] do  -- C loop without a constant trip count (--general-loops)
    if !(decide (UInt32.toInt32 (UInt8.toUInt32 i) < UInt32.toInt32 (UInt8.toUInt32 s._gyro_count))) then break
    let t'1 := i
    o := o.push (Output.AP_Param_save ("ins._gyro_offset_old_param[" ++ (toString (UInt8.toNat t'1)) ++ "]") false)
    let t'2 := i
    o := o.push (Output.AP_Param_save ("ins._gyro_id_old_param[" ++ (toString (UInt8.toNat t'2)) ++ "]") false)
    i := i + (1 : UInt8)
  let t'3 : UInt8 := s._gyro_count
  let t'4 : Int32 := ((3 : Int32) + (0 : Int32))
  for i'2' in [0:(t'4.toInt - (Int.ofNat t'3.toNat)).toNat] do  -- C++ loop bounded by a runtime value (--runtime-loops)
    let i'2 : UInt8 := t'3 + Nat.toUInt8 i'2'
    let t'5 := i'2
    let (t'6, t'7) := AP_ParamV_Vector3_float_5.set_and_save s._gyro_offset_old_param[UInt8.toNat t'5]! o ("ins._gyro_offset_old_param[" ++ (toString (UInt8.toNat t'5)) ++ "]") Vector3f.init_void
    s := { s with _gyro_offset_old_param := s._gyro_offset_old_param.set! (UInt8.toNat t'5) t'6 }
    o := t'7
    let t'8 := i'2
    let (t'9, t'10) := AP_ParamT_unsigned_int_3.set_and_save s._gyro_id_old_param[UInt8.toNat t'8]! o ("ins._gyro_id_old_param[" ++ (toString (UInt8.toNat t'8)) ++ "]") (Int32.toUInt32 (0 : Int32))
    s := { s with _gyro_id_old_param := s._gyro_id_old_param.set! (UInt8.toNat t'8) t'9 }
    o := t'10
  return (s, o)

/-- C++ `void AP_InertialSensor::init_gyro()`, `AP_InertialSensor/AP_InertialSensor.cpp:1385-1392`. -/
def init_gyro (s : State) (w : World) (o : Outputs) : State × World × Outputs := Id.run do
  let mut s := s
  let mut w := w
  let mut o := o
  let (t'1, t'2, t'3) := _init_gyro s w o
  w := t'2
  s := t'1
  o := t'3
  let (t'4, t'5) := _save_gyro_calibration s o
  s := t'4
  o := t'5
  return (s, w, o)

/-- C++ `void AP_InertialSensor::init(uint16_t sample_rate_hz)`, `AP_InertialSensor/AP_InertialSensor.cpp:947-1120`. -/
def init (s : State) (w : World) (o : Outputs) (inp : Inputs) (loop_rate : UInt16) : State × World × Outputs := Id.run do
  let mut s := s
  let mut w := w
  let mut o := o
  s := { s with _loop_rate := loop_rate }
  s := { s with _loop_delta_t := (Binary32.ofBits 0x3f800000 /- 1.0f -/) / Int32.toBinary32 (UInt32.toInt32 (UInt16.toUInt32 loop_rate)) }
  s := { s with _loop_delta_t_max := (Binary32.ofBits 0x41200000 /- 10 -/) * s._loop_delta_t }
  if UInt32.toInt32 (UInt8.toUInt32 s._gyro_count) == (0 : Int32) && UInt32.toInt32 (UInt8.toUInt32 s._accel_count) == (0 : Int32) then
    let (t'1, t'2, t'3) := _start_backends s w o
    w := t'2
    s := t'1
    o := t'3
  if UInt32.toInt32 (AP_InertialSensor.Gyro_Calibration_Timing.toInt (gyro_calibration_timing s inp)) != UInt32.toInt32 (AP_InertialSensor.Gyro_Calibration_Timing.toInt AP_InertialSensor.Gyro_Calibration_Timing.GYRO_CAL_NEVER) && decide (UInt32.toInt32 (UInt8.toUInt32 s._gyro_count) > (0 : Int32)) then
    let (t'4, t'5, t'6) := init_gyro s w o
    w := t'5
    s := t'4
    o := t'6
  s := { s with _sample_period_usec := UInt64.toUInt32 (Int64.toUInt64 (Int32.toInt64 (1000 : Int32)) * (1000 : UInt64) / UInt16.toUInt64 s._loop_rate) }
  s := { s with _delta_time := (Binary32.ofBits 0x00000000 /- 0 -/) }
  s := { s with _next_sample_usec := Int32.toUInt32 (0 : Int32) }
  s := { s with _last_sample_usec := Int32.toUInt32 (0 : Int32) }
  s := { s with _have_sample := false }
  let fft_enabled : Bool := false
  let mut sensors_used : UInt8 := Int8.toUInt8 (Int32.toInt8 (0 : Int32))
  for i' in [0:3] do
    let i : UInt8 := Nat.toUInt8 i'
    let t'7 := i
    sensors_used := Int8.toUInt8 (Int32.toInt8 (UInt32.toInt32 (UInt8.toUInt32 sensors_used) + Int8.toInt32 (AP_ParamT_signed_char_1.op_to_signed_char s._use_old_param[UInt8.toNat t'7]!)))
  return (s, w, o)

/-- C++ `bool AP_InertialSensor::get_delta_velocity(Vector3f & delta_velocity, float & delta_velocity_dt) const`, `AP_InertialSensor/AP_InertialSensor.h:173-175`. -/
def get_delta_velocity_Vector3f_float (s : State) (delta_velocity : Vector3f.State) (delta_velocity_dt : Binary32) : Vector3f.State × Binary32 × Bool := Id.run do
  let mut delta_velocity := delta_velocity
  let mut delta_velocity_dt := delta_velocity_dt
  let (t'1, t'2, t'3) := get_delta_velocity_uint8_t_Vector3f_float s s._first_usable_accel delta_velocity delta_velocity_dt
  delta_velocity := t'1
  delta_velocity_dt := t'2
  return (delta_velocity, delta_velocity_dt, t'3)

/-- C++ `const Vector3f & AP_InertialSensor::get_imu_pos_offset() const`, `AP_InertialSensor/AP_InertialSensor.h:234-236`. -/
def get_imu_pos_offset_void (s : State) : Vector3f.State := Id.run do
  let t'1 := s._first_usable_accel
  let t'2 := t'1
  return AP_ParamV_Vector3_float_5.op_to_Vector3_float s._accel_pos_old_param[UInt8.toNat t'2]!

/-- C++ `bool AP_InertialSensor::get_accel_health_all() const`, `AP_InertialSensor/AP_InertialSensor.cpp:1533-1542`. -/
def get_accel_health_all (s : State) : Bool := Id.run do
  let mut i : UInt8 := Int8.toUInt8 (Int32.toInt8 (0 : Int32))
  for _ in [0:2^64] do  -- C loop without a constant trip count (--general-loops)
    if !(decide (UInt32.toInt32 (UInt8.toUInt32 i) < UInt32.toInt32 (UInt8.toUInt32 (get_accel_count s)))) then break
    if !(get_accel_health_uint8_t s i) then
      return false
    i := i + (1 : UInt8)
  return (decide (UInt32.toInt32 (UInt8.toUInt32 (get_accel_count s)) > (0 : Int32)))

/-- C++ `bool AP_InertialSensor::get_gyro_health_all() const`, `AP_InertialSensor/AP_InertialSensor.cpp:1414-1423`. -/
def get_gyro_health_all (s : State) : Bool := Id.run do
  let mut i : UInt8 := Int8.toUInt8 (Int32.toInt8 (0 : Int32))
  for _ in [0:2^64] do  -- C loop without a constant trip count (--general-loops)
    if !(decide (UInt32.toInt32 (UInt8.toUInt32 i) < UInt32.toInt32 (UInt8.toUInt32 (get_gyro_count s)))) then break
    if !(get_gyro_health_uint8_t s i) then
      return false
    i := i + (1 : UInt8)
  return (decide (UInt32.toInt32 (UInt8.toUInt32 (get_gyro_count s)) > (0 : Int32)))

end AP_InertialSensor

namespace AP_InertialSensor

/-- C++ `Vector3f AP_InertialSensor::get_vibration_levels(uint8_t instance) const`, `AP_InertialSensor/AP_InertialSensor.cpp:2273-2283`. -/
def get_vibration_levels_uint8_t (s : State) («instance» : UInt8) : Vector3f.State := Id.run do
  let mut vibe : Vector3f.State := Vector3f.init_void
  if UInt32.toInt32 (UInt8.toUInt32 «instance») < ((3 : Int32) + (0 : Int32)) then
    vibe := LowPassFilter_Vector3_float.get s._accel_vibe_filter[UInt8.toNat «instance»]!
    vibe := { vibe with x := Estimator_lib.safe_sqrt_float vibe.x }
    vibe := { vibe with y := Estimator_lib.safe_sqrt_float vibe.y }
    vibe := { vibe with z := Estimator_lib.safe_sqrt_float vibe.z }
  return vibe

/-- C++ `Vector3f AP_InertialSensor::get_vibration_levels() const`, `AP_InertialSensor/AP_InertialSensor.h:312`. -/
def get_vibration_levels_void (s : State) : Vector3f.State := Id.run do
  return get_vibration_levels_uint8_t s s._first_usable_accel

/-- C++ `uint32_t AP_InertialSensor::get_accel_clip_count(uint8_t instance) const`, `AP_InertialSensor/AP_InertialSensor.cpp:1405-1411`. -/
def get_accel_clip_count (s : State) («instance» : UInt8) : UInt32 := Id.run do
  if UInt32.toInt32 (UInt8.toUInt32 «instance») ≥ UInt32.toInt32 (UInt8.toUInt32 (get_accel_count s)) then
    return Int32.toUInt32 (0 : Int32)
  return s._accel_clip_count[UInt8.toNat «instance»]!

/-- C++ `float AP_InertialSensor::get_accel_peak_hold_neg_x() const`, `AP_InertialSensor/AP_InertialSensor.h:329`. -/
def get_accel_peak_hold_neg_x (s : State) : Binary32 := Id.run do
  return s._peak_hold_state.accel_peak_hold_neg_x

/-- C++ `bool AP_InertialSensor::gyro_calibrated_ok(uint8_t instance) const`, `AP_InertialSensor/AP_InertialSensor.h:190`. -/
def gyro_calibrated_ok (s : State) («instance» : UInt8) : Bool := Id.run do
  return s._gyro_cal_ok[UInt8.toNat «instance»]!

/-- C++ `bool AP_InertialSensor::gyro_calibrated_ok_all() const`, `AP_InertialSensor/AP_InertialSensor.cpp:1455-1469`. -/
def gyro_calibrated_ok_all (s : State) : Bool := Id.run do
  let mut i : UInt8 := Int8.toUInt8 (Int32.toInt8 (0 : Int32))
  for _ in [0:2^64] do  -- C loop without a constant trip count (--general-loops)
    if !(decide (UInt32.toInt32 (UInt8.toUInt32 i) < UInt32.toInt32 (UInt8.toUInt32 (get_gyro_count s)))) then break
    if !(gyro_calibrated_ok s i) then
      return false
    i := i + (1 : UInt8)
  let t'1 : UInt8 := get_gyro_count s
  let t'2 : Int32 := ((3 : Int32) + (0 : Int32))
  for i'2' in [0:(t'2.toInt - (Int.ofNat t'1.toNat)).toNat] do  -- C++ loop bounded by a runtime value (--runtime-loops)
    let i'2 : UInt8 := t'1 + Nat.toUInt8 i'2'
    let t'3 := i'2
    let t'4 := t'3
    if AP_ParamT_unsigned_int_3.op_to_unsigned_int s._gyro_id_old_param[UInt8.toNat t'4]! != Int32.toUInt32 (0 : Int32) then
      return false
  return (decide (UInt32.toInt32 (UInt8.toUInt32 (get_gyro_count s)) > (0 : Int32)))

/-- C++ `const Vector3f & AP_InertialSensor::get_gyro_offsets(uint8_t i) const`, `AP_InertialSensor/AP_InertialSensor.h:162`. -/
def get_gyro_offsets_uint8_t (s : State) (i : UInt8) : Vector3f.State := Id.run do
  let t'1 := i
  let t'2 := t'1
  return AP_ParamV_Vector3_float_5.op_to_Vector3_float s._gyro_offset_old_param[UInt8.toNat t'2]!

/-- C++ `const Vector3f & AP_InertialSensor::get_gyro_offsets() const`, `AP_InertialSensor/AP_InertialSensor.h:163`. -/
def get_gyro_offsets_void (s : State) : Vector3f.State := Id.run do
  return get_gyro_offsets_uint8_t s s._first_usable_gyro

/-- C++ `const Vector3f & AP_InertialSensor::get_accel_offsets(uint8_t i) const`, `AP_InertialSensor/AP_InertialSensor.h:223`. -/
def get_accel_offsets_uint8_t (s : State) (i : UInt8) : Vector3f.State := Id.run do
  let t'1 := i
  let t'2 := t'1
  return AP_ParamV_Vector3_float_5.op_to_Vector3_float s._accel_offset_old_param[UInt8.toNat t'2]!

/-- C++ `const Vector3f & AP_InertialSensor::get_accel_offsets() const`, `AP_InertialSensor/AP_InertialSensor.h:224`. -/
def get_accel_offsets_void (s : State) : Vector3f.State := Id.run do
  return get_accel_offsets_uint8_t s s._first_usable_accel

/-- C++ `bool AP_InertialSensor::accel_cal_requires_reboot() const`, `AP_InertialSensor/AP_InertialSensor.h:367`. -/
def accel_cal_requires_reboot (s : State) : Bool := Id.run do
  return s._accel_cal_requires_reboot

/-- C++ `bool AP_InertialSensor::accel_calibrated_ok_all() const`, `AP_InertialSensor/AP_InertialSensor.cpp:1659-1696`. -/
def accel_calibrated_ok_all (s : State) : Bool := Id.run do
  let mut i : UInt8 := Int8.toUInt8 (Int32.toInt8 (0 : Int32))
  for _ in [0:2^64] do  -- C loop without a constant trip count (--general-loops)
    if !(decide (UInt32.toInt32 (UInt8.toUInt32 i) < UInt32.toInt32 (UInt8.toUInt32 (get_accel_count s)))) then break
    if !s._accel_id_ok[UInt8.toNat i]! then
      return false
    let t'3 := i
    let t'4 := t'3
    if Vector3f.is_zero s._accel_offset_old_param[UInt8.toNat t'4]!._value then
      return false
    let t'7 := i
    let t'8 := t'7
    if Vector3f.is_zero s._accel_scale_old_param[UInt8.toNat t'8]!._value then
      return false
    i := i + (1 : UInt8)
  let t'9 : UInt8 := get_accel_count s
  let t'10 : Int32 := ((3 : Int32) + (0 : Int32))
  for i'2' in [0:(t'10.toInt - (Int.ofNat t'9.toNat)).toNat] do  -- C++ loop bounded by a runtime value (--runtime-loops)
    let i'2 : UInt8 := t'9 + Nat.toUInt8 i'2'
    let t'11 := i'2
    let t'12 := t'11
    if AP_ParamT_unsigned_int_3.op_to_unsigned_int s._accel_id_old_param[UInt8.toNat t'12]! != Int32.toUInt32 (0 : Int32) then
      return false
  if UInt32.toInt32 (UInt8.toUInt32 (get_accel_count s)) < ((3 : Int32) + (0 : Int32)) then
    let t'13 : UInt8 := get_accel_count s
    let t'14 : Int32 := ((3 : Int32) + (0 : Int32))
    for i'3' in [0:(t'14.toInt - (Int.ofNat t'13.toNat)).toNat] do  -- C++ loop bounded by a runtime value (--runtime-loops)
      let i'3 : UInt8 := t'13 + Nat.toUInt8 i'3'
      let t'17 := i'3
      let t'18 := t'17
      let scaling : Vector3f.State := AP_ParamV_Vector3_float_5.get_void s._accel_scale_old_param[UInt8.toNat t'18]!
      let have_scaling : Bool := (!(Estimator_lib.is_zero_float scaling.x) && !(Estimator_lib.is_equal_float2 scaling.x (Binary32.ofBits 0x3f800000 /- 1.0f -/))) || (!(Estimator_lib.is_zero_float scaling.y) && !(Estimator_lib.is_equal_float2 scaling.y (Binary32.ofBits 0x3f800000 /- 1.0f -/))) || (!(Estimator_lib.is_zero_float scaling.z) && !(Estimator_lib.is_equal_float2 scaling.z (Binary32.ofBits 0x3f800000 /- 1.0f -/)))
      let t'21 := i'3
      let t'22 := t'21
      let have_offsets : Bool := !(Vector3f.is_zero s._accel_offset_old_param[UInt8.toNat t'22]!._value)
      if have_scaling || have_offsets then
        return false
  return true

/-- C++ `bool AP_InertialSensor::accels_consistent(float accel_error_threshold) const`, `AP_InertialSensor/AP_InertialSensor.cpp:1545-1581`. -/
def accels_consistent (s : State) (accel_error_threshold : Binary32) : Bool := Id.run do
  let accel_count : UInt8 := get_accel_count s
  if UInt32.toInt32 (UInt8.toUInt32 accel_count) ≤ (1 : Int32) then
    return true
  let prime_accel_vec : Vector3f.State := get_accel_void s
  for i' in [0:accel_count.toNat] do
    let i : UInt8 := Nat.toUInt8 i'
    if !(use_accel s i) then
      continue
    let accel_vec : Vector3f.State := get_accel_uint8_t s i
    let mut vec_diff : Vector3f.State := Vector3f.op_sub_Vector3f accel_vec prime_accel_vec
    let mut threshold : Binary32 := accel_error_threshold
    if UInt32.toInt32 (UInt8.toUInt32 i) ≥ (2 : Int32) then
      threshold := threshold * (Binary32.ofBits 0x40400000 /- 3 -/)
    vec_diff := { vec_diff with z := vec_diff.z * (Binary32.ofBits 0x3f000000 /- 0.5f -/) }
    if Vector3f.length vec_diff > threshold then
      return false
  return true

/-- C++ `bool AP_InertialSensor::gyros_consistent(uint8_t threshold) const`, `AP_InertialSensor/AP_InertialSensor.cpp:1427-1452`. -/
def gyros_consistent (s : State) (threshold : UInt8) : Bool := Id.run do
  let gyro_count : UInt8 := get_gyro_count s
  if UInt32.toInt32 (UInt8.toUInt32 gyro_count) ≤ (1 : Int32) then
    return true
  let prime_gyro_vec : Vector3f.State := get_gyro_void s
  for i' in [0:gyro_count.toNat] do
    let i : UInt8 := Nat.toUInt8 i'
    if !(use_gyro s i) then
      continue
    let gyro_vec : Vector3f.State := get_gyro_uint8_t s i
    let vec_diff : Vector3f.State := Vector3f.op_sub_Vector3f gyro_vec prime_gyro_vec
    if Vector3f.length vec_diff > Estimator_lib.radians_int32_t (UInt32.toInt32 (UInt8.toUInt32 threshold)) then
      return false
  return true

/-- C++ `void AP_InertialSensor::set_log_raw_bit(uint32_t log_raw_bit)`, `AP_InertialSensor/AP_InertialSensor.h:302`. -/
def set_log_raw_bit (s : State) (log_raw_bit : UInt32) : State := Id.run do
  let mut s := s
  s := { s with _log_raw_bit := log_raw_bit }
  return s

/-- C++ `bool AP_InertialSensor::temperature_cal_running() const`, `AP_InertialSensor/AP_InertialSensor.cpp:2309-2319`. -/
def temperature_cal_running : Bool := Id.run do
  return false

/-- C++ `float AP_InertialSensor::get_temperature(uint8_t instance) const`, `AP_InertialSensor/AP_InertialSensor.h:248`. -/
def get_temperature (s : State) («instance» : UInt8) : Binary32 := Id.run do
  return s._temperature[UInt8.toNat «instance»]!

end AP_InertialSensor

end Estimator_lib
