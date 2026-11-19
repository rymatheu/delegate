import ArduLean.Musl.atan2f
import ArduLean.Musl.cosf
import ArduLean.Musl.sinf
import ArduLean.Estimator.libraries.AP_Math.AP_Math
import ArduLean.Estimator.World
import ArduLean.Estimator.libraries.AP_Common.AP_Common
import ArduLean.Estimator.libraries.AP_Param.AP_Param
import ArduLean.Estimator.libraries.SITL.SITL
import ArduLean.Estimator.libraries.AP_GPS.AP_GPS
import ArduLean.Estimator.libraries.AP_InertialSensor.AP_InertialSensor
import ArduLean.Estimator.libraries.AP_AHRS.AP_AHRS
import ArduLean.Estimator.libraries.AP_Baro.AP_Baro
import ArduLean.Estimator.World_2
import ArduLean.Estimator.libraries.AP_Param.AP_Param_2
import ArduLean.Estimator.libraries.AP_Compass.AP_Compass_2
import ArduLean.Estimator.World_3
import ArduLean.Estimator.libraries.AP_Compass.AP_Compass_3
import ArduLean.Estimator.libraries.AP_GPS.AP_GPS_2
import ArduLean.Estimator.libraries.AP_AHRS.AP_AHRS_2
import ArduLean.Estimator.World_4
import ArduLean.Estimator.libraries.AP_InertialSensor.AP_InertialSensor_3
import ArduLean.Estimator.libraries.AP_AHRS.AP_AHRS_3
import ArduLean.Estimator.libraries.AP_Compass.AP_Compass_4

/-!
ArduPilot `libraries/AP_AHRS`, part 4 of 4. Sources: `libraries/AP_AHRS/AP_AHRS_DCM.cpp`, `libraries/AP_AHRS/AP_AHRS.cpp`.

Items of `lean/Estimator_lib.lean` (the estimator translation), unchanged; placed by `tools/split_modules.py` (`ArduLean/Estimator/INDEX.md`).
-/

open FloatLib.Floats (Binary32 Binary64)

set_option maxRecDepth 200000
-- AP_DAL's `const log_RISH old_RISH = _RISH;` read only by WRITE_REPLAY_BLOCK_IFCHANGED, which is `(void)old`
-- without logging (HAL_LOGGING_ENABLED 0): an unused binding, as in the C++
set_option linter.unusedVariables false

namespace Estimator_lib

namespace AP_AHRS_DCM

/-- C++ `void AP_AHRS_DCM::drift_correction_yaw()`, `AP_AHRS/AP_AHRS_DCM.cpp:650-774`. -/
def drift_correction_yaw (s : State) (w : World) (inp : Inputs) : State × World := Id.run do
  let mut s := s
  let mut w := w
  let mut new_value : Bool := false
  let mut yaw_error : Binary32 := (Binary32.ofBits 0x00000000 /- 0.0 -/)  -- uninitialized in C++; assigned before every read
  let mut yaw_deltat : Binary32 := (Binary32.ofBits 0x00000000 /- 0.0f -/)
  let (t'1, t'2) := use_compass s w
  s := t'1
  if t'2 then
    if Compass.last_update_usec_void w.compass != s._compass_last_update then
      yaw_deltat := UInt32.toBinary32 (Compass.last_update_usec_void w.compass - s._compass_last_update) * (Binary32.ofBits 0x358637bd /- 1.0e-6f -/)
      s := { s with _compass_last_update := Compass.last_update_usec_void w.compass }
      let mut t'7 := !s.have_initial_yaw
      if t'7 then
        let t'3 := w.compass  -- the object out of the World for the call (--swap-out)
        w := { w with compass := default }
        let (t'4, t'5, t'6) := Compass.read t'3 w
        w := t'5
        w := { w with compass := t'4 }
        t'7 := t'6
      if t'7 then
        let heading : Binary32 := Compass.calculate_heading_Matrix3f w.compass s._dcm_matrix
        s := { s with _dcm_matrix := Matrix3f.from_euler s._dcm_matrix s.roll s.pitch heading }
        s := { s with _omega_yaw_P := Vector3f.zero s._omega_yaw_P }
        s := { s with have_initial_yaw := true }
      new_value := true
      let (t'8, t'9) := yaw_error_compass s w
      s := t'8
      yaw_error := t'9
      s := { s with _gps_last_update := AP_GPS.last_fix_time_ms_void w.gps }
  else if AP_AHRS.get_fly_forward w.ahrs && have_gps w then
    if AP_GPS.last_fix_time_ms_void w.gps != s._gps_last_update && decide (AP_GPS.ground_speed_void w.gps ≥ (Binary32.ofBits 0x40400000 /- (float)3 -/)) then
      yaw_deltat := UInt32.toBinary32 (AP_GPS.last_fix_time_ms_void w.gps - s._gps_last_update) * (Binary32.ofBits 0x3a83126f /- 1.0e-3f -/)
      s := { s with _gps_last_update := AP_GPS.last_fix_time_ms_void w.gps }
      new_value := true
      let gps_course_rad : Binary32 := Estimator_lib.radians_float (AP_GPS.ground_course_void w.gps)
      let yaw_error_rad : Binary32 := Estimator_lib.wrap_PI_float (gps_course_rad - s.yaw)
      yaw_error := Musl.sinf.sinf yaw_error_rad
      if !s.have_initial_yaw || decide (yaw_deltat > (Binary32.ofBits 0x41a00000 /- 20 -/)) || (decide (AP_GPS.ground_speed_void w.gps ≥ (Binary32.ofBits 0x41100000 /- (float)9 -/)) && decide (Binary32.abs yaw_error_rad ≥ (Binary32.ofBits 0x3f860419 /- 1.047f -/))) then
        s := { s with _dcm_matrix := Matrix3f.from_euler s._dcm_matrix s.roll s.pitch gps_course_rad }
        s := { s with _omega_yaw_P := Vector3f.zero s._omega_yaw_P }
        s := { s with have_initial_yaw := true }
        yaw_error := (Binary32.ofBits 0x00000000 /- 0 -/)
  if !new_value then
    let (t'10, _) := Vector3f.op_mul_assign_float s._omega_yaw_P (Binary32.ofBits 0x3f7851ec /- 0.97f -/)
    s := { s with _omega_yaw_P := t'10 }
    return (s, w)
  let error_z : Binary32 := s._dcm_matrix.c.z * yaw_error
  let spin_rate : Binary32 := Vector3f.length s._omega
  if AP_ParamT_float_4.op_to_float w.ahrs._kp_yaw < (Binary32.ofBits 0x3d4ccccd /- 0.0500000007 -/) then
    w := { w with ahrs._kp_yaw := AP_ParamT_float_4.set w.ahrs._kp_yaw (Binary32.ofBits 0x3d4ccccd /- 0.0500000007 -/) }
  s := { s with _omega_yaw_P.z := error_z * _P_gain spin_rate * AP_ParamT_float_4.op_to_float w.ahrs._kp_yaw * _yaw_gain s }
  if use_fast_gains s w inp then
    s := { s with _omega_yaw_P.z := s._omega_yaw_P.z * (Binary32.ofBits 0x41000000 /- 8 -/) }
  if decide (yaw_deltat < (Binary32.ofBits 0x40000000 /- 2.0f -/)) && decide (spin_rate < Estimator_lib.radians_int32_t (20 : Int32)) then
    s := { s with _omega_I_sum.z := s._omega_I_sum.z + error_z * _ki_yaw * yaw_deltat }
  s := { s with _error_yaw := (Binary32.ofBits 0x3f4ccccd /- 0.8f -/) * s._error_yaw + (Binary32.ofBits 0x3e4ccccd /- 0.2f -/) * Binary32.abs yaw_error }
  return (s, w)

/-- C++ `bool AP_AHRS_DCM::should_correct_centrifugal() const`, `AP_AHRS/AP_AHRS_DCM.cpp:799-806`. -/
def should_correct_centrifugal (inp : Inputs) : Bool := Id.run do
  return inp.get_soft_armed

/-- C++ `Vector3f AP_AHRS_DCM::ra_delayed(uint8_t instance, const Vector3f & ra)`, `AP_AHRS/AP_AHRS_DCM.cpp:781-792`. -/
def ra_delayed (s : State) («instance» : UInt8) (ra : Vector3f.State) : State × Vector3f.State := Id.run do
  let mut s := s
  let ret : Vector3f.State := s._ra_delay_buffer[UInt8.toNat «instance»]!
  s := { s with _ra_delay_buffer := s._ra_delay_buffer.set! (UInt8.toNat «instance») ra }
  if Vector3f.is_zero ret then
    return (s, ra)
  return (s, ret)

/-- C++ `static const float AP_AHRS_DCM::_ki`, `AP_AHRS/AP_AHRS_DCM.h:122`. -/
def _ki : Binary32 := (Binary32.ofBits 0x3c0e8a72 /- 0.0087f -/)

end AP_AHRS_DCM

namespace AP_AHRS_DCM

/-- C++ `void AP_AHRS_DCM::drift_correction(float deltat)`, `AP_AHRS/AP_AHRS_DCM.cpp:817-1128`. -/
def drift_correction (s : State) (w : World) (o : Outputs) (inp : Inputs) (deltat : Binary32) : State × World × Outputs := Id.run do
  let mut s := s
  let mut w := w
  let mut o := o
  let mut velocity : Vector3f.State := Vector3f.init_void
  let mut last_correction_time : UInt32 := (0 : UInt32)  -- uninitialized in C++; assigned before every read
  let (t'1, t'2) := drift_correction_yaw s w inp
  w := t'2
  s := t'1
  let mut i : UInt8 := Int8.toUInt8 (Int32.toInt8 (0 : Int32))
  for _ in [0:2^64] do  -- C loop without a constant trip count (--general-loops)
    if !(decide (UInt32.toInt32 (UInt8.toUInt32 i) < UInt32.toInt32 (UInt8.toUInt32 (AP_InertialSensor.get_accel_count w.ins)))) then break
    if AP_InertialSensor.use_accel w.ins i then
      let mut delta_velocity : Vector3f.State := Vector3f.init_void
      let mut delta_velocity_dt : Binary32 := (Binary32.ofBits 0x00000000 /- 0.0 -/)  -- uninitialized in C++; assigned before every read
      let (t'3, t'4, _) := AP_InertialSensor.get_delta_velocity_uint8_t_Vector3f_float w.ins i delta_velocity delta_velocity_dt
      delta_velocity := t'3
      delta_velocity_dt := t'4
      if delta_velocity_dt > (Binary32.ofBits 0x00000000 /- 0 -/) then
        let accel_ef : Vector3f.State := Matrix3f.op_mul_Vector3f s._dcm_matrix (Vector3f.op_div delta_velocity delta_velocity_dt)
        let (t'6, _) := Vector3f.op_add_assign s._ra_sum[UInt8.toNat i]! (Vector3f.op_mul_float accel_ef deltat)
        s := { s with _ra_sum := s._ra_sum.set! (UInt8.toNat i) t'6 }
    i := i + (1 : UInt8)
  s := { s with _accel_ef := Matrix3f.op_mul_Vector3f s._dcm_matrix (AP_InertialSensor.get_accel_void w.ins) }
  s := { s with _ra_deltat := s._ra_deltat + deltat }
  let fly_forward : Bool := AP_AHRS.get_fly_forward w.ahrs
  if !(have_gps w) || decide (AP_GPS_FixType.toInt (AP_GPS.status_void w.gps) < AP_GPS_FixType.toInt AP_GPS_FixType.FIX_3D) || decide (UInt32.toInt32 (UInt8.toUInt32 (AP_GPS.num_sats_void w.gps)) < Int8.toInt32 (AP_ParamT_signed_char_1.op_to_signed_char w.ahrs._gps_minsats)) then
    if s._ra_deltat < (Binary32.ofBits 0x3e4ccccd /- 0.2f -/) then
      return (s, w, o)
    let airspeed_TAS : Binary32 := s._last_airspeed_TAS
    velocity := Vector3f.op_mul_float (Matrix3f.colx s._dcm_matrix) airspeed_TAS
    let (t'8, _) := Vector3f.op_add_assign velocity s._wind
    velocity := t'8
    last_correction_time := Estimator_lib.millis w
    s := { s with _have_gps_lock := false }
  else
    if AP_GPS.last_fix_time_ms_void w.gps == s._ra_sum_start then
      return (s, w, o)
    velocity := AP_GPS.velocity_void w.gps
    last_correction_time := AP_GPS.last_fix_time_ms_void w.gps
    if (if s._have_gps_lock then (1 : Int32) else (0 : Int32)) == (if false then (1 : Int32) else (0 : Int32)) then
      s := { s with _last_velocity := velocity }
    s := { s with _have_gps_lock := true }
    let mut airspeed : Vector3f.State := Vector3f.op_sub_Vector3f velocity s._wind
    airspeed := Matrix3f.mul_transpose s._body_dcm_matrix airspeed
    s := { s with _last_airspeed_TAS := Estimator_lib.MAX_float_int32_t airspeed.x (0 : Int32) }
  if have_gps w then
    s := { s with _last_lat := (AP_GPS.location_void w.gps).lat }
    s := { s with _last_lng := (AP_GPS.location_void w.gps).lng }
    s := { s with _last_pos_ms := Estimator_lib.millis w }
    s := { s with _position_offset_north := (Binary32.ofBits 0x00000000 /- 0 -/) }
    s := { s with _position_offset_east := (Binary32.ofBits 0x00000000 /- 0 -/) }
    s := { s with _have_position := true }
  else
    s := { s with _position_offset_north := s._position_offset_north + velocity.x * s._ra_deltat }
    s := { s with _position_offset_east := s._position_offset_east + velocity.y * s._ra_deltat }
  if s._ra_sum_start == Int32.toUInt32 (0 : Int32) then
    s := { s with _ra_sum_start := last_correction_time }
    s := { s with _last_velocity := velocity }
    return (s, w, o)
  let mut GA_e : Vector3f.State := Vector3f.init_float3 (Binary32.ofBits 0x00000000 /- 0.0f -/) (Binary32.ofBits 0x00000000 /- 0.0f -/) (-(Binary32.ofBits 0x3f800000 /- 1.0f -/))
  if s._ra_deltat ≤ (Binary32.ofBits 0x00000000 /- 0 -/) then
    return (s, w, o)
  let mut using_gps_corrections : Bool := false
  let ra_scale : Binary32 := (Binary32.ofBits 0x3f800000 /- 1.0f -/) / (s._ra_deltat * (Binary32.ofBits 0x411ce80a /- 9.80665016 -/))
  if should_correct_centrifugal inp && (s._have_gps_lock || fly_forward) then
    let v_scale : Binary32 := AP_ParamT_float_4.get_void w.ahrs.gps_gain * ra_scale
    let vdelta : Vector3f.State := Vector3f.op_mul_float (Vector3f.op_sub_Vector3f velocity s._last_velocity) v_scale
    let (t'10, _) := Vector3f.op_add_assign GA_e vdelta
    GA_e := t'10
    GA_e := Vector3f.normalize GA_e
    if Vector3f.is_inf GA_e then
      s := { s with _last_failure_ms := Estimator_lib.millis w }
      return (s, w, o)
    using_gps_corrections := true
  let mut error : Array Vector3f.State := Array.replicate 3 {}  -- each element default-constructed (zero)
  let mut error_dirn : Array Binary32 := Array.replicate 3 (Binary32.ofBits 0x00000000 /- 0.0 -/)  -- uninitialized in C; every element is written before it is read
  let mut GA_b : Array Vector3f.State := Array.replicate 3 {}  -- each element default-constructed (zero)
  let mut besti : Int8 := Int32.toInt8 (-(1 : Int32))
  let mut best_error : Binary32 := (Binary32.ofBits 0x00000000 /- 0 -/)
  let mut i'2 : UInt8 := Int8.toUInt8 (Int32.toInt8 (0 : Int32))
  let mut t'16 := true
  for _ in [0:2^64] do  -- C loop without a constant trip count (--general-loops)
    if t'16 then
      t'16 := false
    else
      i'2 := i'2 + (1 : UInt8)
    if !(decide (UInt32.toInt32 (UInt8.toUInt32 i'2) < UInt32.toInt32 (UInt8.toUInt32 (AP_InertialSensor.get_accel_count w.ins)))) then break
    if !(AP_InertialSensor.get_accel_health_uint8_t w.ins i'2) then
      continue
    let (t'12, _) := Vector3f.op_mul_assign_float s._ra_sum[UInt8.toNat i'2]! ra_scale
    s := { s with _ra_sum := s._ra_sum.set! (UInt8.toNat i'2) t'12 }
    if using_gps_corrections then
      let (t'14, t'15) := ra_delayed s i'2 s._ra_sum[UInt8.toNat i'2]!
      s := t'14
      GA_b := GA_b.set! (UInt8.toNat i'2) t'15
    else
      GA_b := GA_b.set! (UInt8.toNat i'2) (s._ra_sum[UInt8.toNat i'2]!)
    if Vector3f.is_zero GA_b[UInt8.toNat i'2]! then
      continue
    GA_b := GA_b.set! (UInt8.toNat i'2) (Vector3f.normalize GA_b[UInt8.toNat i'2]!)
    if Vector3f.is_inf GA_b[UInt8.toNat i'2]! then
      continue
    error := error.set! (UInt8.toNat i'2) (Vector3f.op_mod GA_b[UInt8.toNat i'2]! GA_e)
    error_dirn := error_dirn.set! (UInt8.toNat i'2) (Vector3f.op_mul_Vector3f GA_b[UInt8.toNat i'2]! GA_e)
    let error_length : Binary32 := Vector3f.length error[UInt8.toNat i'2]!
    if Int8.toInt32 besti == -(1 : Int32) || decide (error_length < best_error) then
      besti := UInt8.toInt8 i'2
      best_error := error_length
    if error_dirn[Int8.toNatClampNeg besti]! < (Binary32.ofBits 0x00000000 /- 0.0f -/) then
      best_error := (Binary32.ofBits 0x3f800000 /- 1.0f -/)
  if Int8.toInt32 besti == -(1 : Int32) then
    s := { s with _last_failure_ms := Estimator_lib.millis w }
    return (s, w, o)
  s := { s with _active_accel_instance := Int8.toUInt8 besti }
  let (t'17, t'18) := use_compass s w
  s := t'17
  if t'18 then
    if have_gps w && Estimator_lib.is_equal_float2 (AP_ParamT_float_4.get_void w.ahrs.gps_gain) (Binary32.ofBits 0x3f800000 /- 1.0f -/) then
      error := error.set! (Int8.toNatClampNeg besti) ({ error[Int8.toNatClampNeg besti]! with z := error[Int8.toNatClampNeg besti]!.z * Musl.sinf.sinf (Binary32.abs s.roll) })
    else
      error := error.set! (Int8.toNatClampNeg besti) ({ error[Int8.toNatClampNeg besti]! with z := (Binary32.ofBits 0x00000000 /- 0 -/) })
  if !(AP_InertialSensor.healthy w.ins) then
    error := error.set! (Int8.toNatClampNeg besti) (Vector3f.zero error[Int8.toNatClampNeg besti]!)
  else
    error := error.set! (Int8.toNatClampNeg besti) (Matrix3f.mul_transpose s._dcm_matrix error[Int8.toNatClampNeg besti]!)
  if Vector3f.is_nan error[Int8.toNatClampNeg besti]! || Vector3f.is_inf error[Int8.toNatClampNeg besti]! then
    let (t'19, t'20, t'21) := check_matrix s w o inp
    w := t'20
    s := t'19
    o := t'21
    s := { s with _last_failure_ms := Estimator_lib.millis w }
    return (s, w, o)
  s := { s with _error_rp := (Binary32.ofBits 0x3f4ccccd /- 0.8f -/) * s._error_rp + (Binary32.ofBits 0x3e4ccccd /- 0.2f -/) * best_error }
  let spin_rate : Binary32 := Vector3f.length s._omega
  if AP_ParamT_float_4.op_to_float w.ahrs._kp < (Binary32.ofBits 0x3d4ccccd /- 0.0500000007 -/) then
    w := { w with ahrs._kp := AP_ParamT_float_4.set w.ahrs._kp (Binary32.ofBits 0x3d4ccccd /- 0.0500000007 -/) }
  s := { s with _omega_P := Vector3f.op_mul_float (Vector3f.op_mul_float error[Int8.toNatClampNeg besti]! (_P_gain spin_rate)) (AP_ParamT_float_4.op_to_float w.ahrs._kp) }
  if use_fast_gains s w inp then
    let (t'22, _) := Vector3f.op_mul_assign_float s._omega_P (Binary32.ofBits 0x41000000 /- 8 -/)
    s := { s with _omega_P := t'22 }
  if fly_forward && decide (AP_GPS_FixType.toInt (AP_GPS.status_void w.gps) ≥ AP_GPS_FixType.toInt AP_GPS_FixType.FIX_2D) && decide (AP_GPS.ground_speed_void w.gps < (Binary32.ofBits 0x40400000 /- (float)3 -/)) && decide ((AP_InertialSensor.get_accel_void w.ins).x ≥ (Binary32.ofBits 0x40e00000 /- 7 -/)) && decide (s.pitch > Estimator_lib.radians_int32_t (-(30 : Int32))) && decide (s.pitch < Estimator_lib.radians_int32_t (30 : Int32)) then
    let (t'24, _) := Vector3f.op_mul_assign_float s._omega_P (Binary32.ofBits 0x3f000000 /- 0.5f -/)
    s := { s with _omega_P := t'24 }
  if spin_rate < Estimator_lib.radians_int32_t (20 : Int32) then
    let (t'26, _) := Vector3f.op_add_assign s._omega_I_sum (Vector3f.op_mul_float (Vector3f.op_mul_float error[Int8.toNatClampNeg besti]! _ki) s._ra_deltat)
    s := { s with _omega_I_sum := t'26 }
    s := { s with _omega_I_sum_time := s._omega_I_sum_time + s._ra_deltat }
  if s._omega_I_sum_time ≥ (Binary32.ofBits 0x40a00000 /- 5 -/) then
    let change_limit : Binary32 := AP_InertialSensor.get_gyro_drift_rate * s._omega_I_sum_time
    s := { s with _omega_I_sum.x := Estimator_lib.constrain_value_line_float s._omega_I_sum.x (-change_limit) change_limit (Int32.toUInt32 (1113 : Int32)) }
    s := { s with _omega_I_sum.y := Estimator_lib.constrain_value_line_float s._omega_I_sum.y (-change_limit) change_limit (Int32.toUInt32 (1114 : Int32)) }
    s := { s with _omega_I_sum.z := Estimator_lib.constrain_value_line_float s._omega_I_sum.z (-change_limit) change_limit (Int32.toUInt32 (1115 : Int32)) }
    let (t'28, _) := Vector3f.op_add_assign s._omega_I s._omega_I_sum
    s := { s with _omega_I := t'28 }
    s := { s with _omega_I_sum := Vector3f.zero s._omega_I_sum }
    s := { s with _omega_I_sum_time := (Binary32.ofBits 0x00000000 /- 0 -/) }
  s := { s with _ra_sum := Array.replicate 3 { x := (Binary32.ofBits 0x00000000 /- 0.0 -/), y := (Binary32.ofBits 0x00000000 /- 0.0 -/), z := (Binary32.ofBits 0x00000000 /- 0.0 -/) } }
  s := { s with _ra_deltat := (Binary32.ofBits 0x00000000 /- 0 -/) }
  s := { s with _ra_sum_start := last_correction_time }
  s := { s with _last_velocity := velocity }
  return (s, w, o)

/-- C++ `void AP_AHRS_DCM::backup_attitude()`, `AP_AHRS/AP_AHRS_DCM.cpp:312-318`. -/
def backup_attitude (s : State) (o : Outputs) : Outputs := Id.run do
  let mut o := o
  o := o.push (Output.hal_util_persistent_data_roll_rad s.roll)
  o := o.push (Output.hal_util_persistent_data_pitch_rad s.pitch)
  o := o.push (Output.hal_util_persistent_data_yaw_rad s.yaw)
  return o

/-- C++ `void AP_AHRS_Backend::estimate_wind(const Vector3f & velocity, const Vector3f & fuselageDirection)`, `AP_AHRS/AP_AHRS_DCM.cpp:1142-1218` (a member of `AP_AHRS_Backend`, translated for `AP_AHRS_DCM`). -/
def estimate_wind_Vector3f2 (s : State) (w : World) (velocity : Vector3f.State) (fuselageDirection : Vector3f.State) : State := Id.run do
  let mut s := s
  if !(AP_AHRS.get_wind_estimation_enabled w.ahrs) then
    return s
  let now : UInt32 := Estimator_lib.millis w
  if now - s._last_wind_estimate_ms < Int32.toUInt32 (100 : Int32) then
    return s
  s := { s with _last_wind_estimate_ms := now }
  let fuselageDirectionDiff : Vector3f.State := Vector3f.op_sub_Vector3f fuselageDirection s._last_fuse
  if now - s._last_wind_time > Int32.toUInt32 (10000 : Int32) then
    s := { s with _last_wind_time := now }
    s := { s with _last_fuse := fuselageDirection }
    s := { s with _last_vel := velocity }
    return s
  let diff_length : Binary32 := Vector3f.length fuselageDirectionDiff
  if diff_length > (Binary32.ofBits 0x3e4ccccd /- 0.2f -/) then
    let velocityDiff : Vector3f.State := Vector3f.op_sub_Vector3f velocity s._last_vel
    let V : Binary32 := Vector3f.length velocityDiff / diff_length
    let fuselageDirectionSum : Vector3f.State := Vector3f.op_add fuselageDirection s._last_fuse
    let velocitySum : Vector3f.State := Vector3f.op_add velocity s._last_vel
    s := { s with _last_fuse := fuselageDirection }
    s := { s with _last_vel := velocity }
    let theta : Binary32 := Musl.atan2f.atan2f velocityDiff.y velocityDiff.x - Musl.atan2f.atan2f fuselageDirectionDiff.y fuselageDirectionDiff.x
    let sintheta : Binary32 := Musl.sinf.sinf theta
    let costheta : Binary32 := Musl.cosf.cosf theta
    let mut wind : Vector3f.State := Vector3f.init_float3 (velocitySum.x - V * (costheta * fuselageDirectionSum.x - sintheta * fuselageDirectionSum.y)) (velocitySum.y - V * (sintheta * fuselageDirectionSum.x + costheta * fuselageDirectionSum.y)) (velocitySum.z - V * fuselageDirectionSum.z)
    let (t'1, _) := Vector3f.op_mul_assign_float wind (Binary32.ofBits 0x3f000000 /- 0.5f -/)
    wind := t'1
    if Vector3f.length wind < Vector3f.length s._wind + (Binary32.ofBits 0x41a00000 /- 20 -/) then
      s := { s with _wind := Vector3f.op_add (Vector3f.op_mul_float s._wind (Binary32.ofBits 0x3f733333 /- 0.95f -/)) (Vector3f.op_mul_float wind (Binary32.ofBits 0x3d4ccccd /- 0.05f -/)) }
    s := { s with _last_wind_time := now }
    return s
  return s

/-- C++ `void AP_AHRS_DCM::estimate_wind()`, `AP_AHRS/AP_AHRS_DCM.cpp:1132-1135`. -/
def estimate_wind_void (s : State) (w : World) : State := Id.run do
  let mut s := s
  s := estimate_wind_Vector3f2 s w s._last_velocity (Matrix3f.colx s._body_dcm_matrix)
  return s

end AP_AHRS_DCM

namespace AP_AHRS_DCM

/-- C++ `void AP_AHRS_DCM::update()`, `AP_AHRS/AP_AHRS_DCM.cpp:73-167`. -/
def update (s : State) (w : World) (o : Outputs) (inp : Inputs) : State × World × Outputs := Id.run do
  let mut s := s
  let mut w := w
  let mut o := o
  let delta_t : Binary32 := AP_InertialSensor.get_delta_time w.ins
  if delta_t > (Binary32.ofBits 0x3e4ccccd /- 0.2f -/) then
    s := { s with _ra_sum := Array.replicate 3 { x := (Binary32.ofBits 0x00000000 /- 0.0 -/), y := (Binary32.ofBits 0x00000000 /- 0.0 -/), z := (Binary32.ofBits 0x00000000 /- 0.0 -/) } }
    s := { s with _ra_deltat := (Binary32.ofBits 0x00000000 /- 0 -/) }
    return (s, w, o)
  s := matrix_update s w
  let (t'1, t'2, t'3) := normalize s w o inp
  w := t'2
  s := t'1
  o := t'3
  let (t'4, t'5, t'6) := drift_correction s w o inp delta_t
  w := t'5
  s := t'4
  o := t'6
  let (t'7, t'8, t'9) := check_matrix s w o inp
  w := t'8
  s := t'7
  o := t'9
  s := { s with _body_dcm_matrix := Matrix3f.op_mul_Matrix3f s._dcm_matrix (AP_AHRS.get_rotation_vehicle_body_to_autopilot_body w.ahrs) }
  let (t'10, t'11, t'12) := Matrix3f.to_euler s._body_dcm_matrix true s.roll true s.pitch true s.yaw
  s := { s with roll := t'10 }
  s := { s with pitch := t'11 }
  s := { s with yaw := t'12 }
  s := { s with _cos_yaw := Musl.cosf.cosf s.yaw }
  s := { s with _sin_yaw := Musl.sinf.sinf s.yaw }
  o := backup_attitude s o
  for _ in [0:1] do
    let (t'13, t'14) := AP_AHRS.get_origin w.ahrs s.last_origin
    s := { s with last_origin := t'13 }
    if t'14 then
      pure ()
  if AP_GPS_FixType.toInt (AP_GPS.status_void w.gps) ≥ AP_GPS_FixType.toInt AP_GPS_FixType.FIX_3D then
    let last_gps_ms : UInt32 := AP_GPS.last_message_time_ms_void w.gps
    if last_gps_ms != s._last_wind_gps_ms then
      s := { s with _last_wind_gps_ms := last_gps_ms }
      s := estimate_wind_void s w
  return (s, w, o)

/-- C++ `bool AP_AHRS_DCM::get_velocity_NED(Vector3f & vec) const`, `AP_AHRS/AP_AHRS_DCM.cpp:1405-1413`. -/
def get_velocity_NED (w : World) (vec : Vector3f.State) : Vector3f.State × Bool := Id.run do
  let mut vec := vec
  if AP_GPS_FixType.toInt (AP_GPS.status_void w.gps) < AP_GPS_FixType.toInt AP_GPS_FixType.FIX_3D then
    return (vec, false)
  vec := AP_GPS.velocity_void w.gps
  return (vec, true)

/-- C++ `bool AP_AHRS_Backend::airspeed_TAS(bool have_velocity_source, float & airspeed_ret) const`, `AP_AHRS/AP_AHRS_Backend.h:329-335` (a member of `AP_AHRS_Backend`, translated for `AP_AHRS_DCM`). -/
def airspeed_TAS (s : State) (w : World) (have_velocity_source : Bool) (airspeed_ret : Binary32) : Binary32 × Bool := Id.run do
  let mut airspeed_ret := airspeed_ret
  let (t'1, t'2) := airspeed_EAS s w have_velocity_source airspeed_ret
  airspeed_ret := t'1
  if !t'2 then
    return (airspeed_ret, false)
  airspeed_ret := airspeed_ret * AP_AHRS_Backend.get_EAS2TAS w
  return (airspeed_ret, true)

end AP_AHRS_DCM

namespace AP_AHRS_DCM

/-- C++ `Vector2f AP_AHRS_DCM::groundspeed_vector()`, `AP_AHRS/AP_AHRS_DCM.cpp:1416-1476`. -/
def groundspeed_vector (s : State) (w : World) : State × Vector2f.State := Id.run do
  let mut s := s
  let mut gndVelADS : Vector2f.State := Vector2f.init_void
  let mut gndVelGPS : Vector2f.State := Vector2f.init_void
  let mut airspeed : Binary32 := (Binary32.ofBits 0x00000000 /- 0 -/)
  let (t'1, t'2) := airspeed_TAS s w (have_gps w) airspeed
  airspeed := t'1
  let gotAirspeed : Bool := t'2
  let gotGPS : Bool := (decide (AP_GPS_FixType.toInt (AP_GPS.status_void w.gps) ≥ AP_GPS_FixType.toInt AP_GPS_FixType.FIX_2D))
  if gotAirspeed then
    let airspeed_vector : Vector2f.State := Vector2f.init_float2 (s._cos_yaw * airspeed) (s._sin_yaw * airspeed)
    gndVelADS := Vector2f.op_add airspeed_vector (Vector3f.xy s._wind)
  if gotGPS then
    let cog : Binary32 := Estimator_lib.radians_float (AP_GPS.ground_course_void w.gps)
    gndVelGPS := Vector2f.op_mul_float (Vector2f.init_float2 (Musl.cosf.cosf cog) (Musl.sinf.sinf cog)) (AP_GPS.ground_speed_void w.gps)
  if gotAirspeed && gotGPS then
    let alpha : Binary32 := (Binary32.ofBits 0x3f800000 /- 1.0f -/) - AP_ParamT_float_4.op_to_float w.ahrs.beta
    s := { s with _lp := Vector2f.op_add (Vector2f.op_mul_float gndVelGPS (AP_ParamT_float_4.op_to_float w.ahrs.beta)) (Vector2f.op_mul_float s._lp alpha) }
    s := { s with _hp := Vector2f.op_add (Vector2f.op_sub_Vector2f gndVelADS s._lastGndVelADS) (Vector2f.op_mul_float s._hp alpha) }
    s := { s with _lastGndVelADS := gndVelADS }
    return (s, Vector2f.op_add s._hp s._lp)
  if gotAirspeed && !gotGPS then
    return (s, gndVelADS)
  if !gotAirspeed && gotGPS then
    return (s, gndVelGPS)
  if airspeed > (Binary32.ofBits 0x00000000 /- 0 -/) then
    let mut ret : Vector2f.State := Vector2f.init_float2 s._cos_yaw s._sin_yaw
    let (t'3, _) := Vector2f.op_mul_assign ret airspeed
    ret := t'3
    let (t'5, _) := Vector2f.op_add_assign ret (Vector3f.xy s._wind)
    ret := t'5
    return (s, ret)
  return (s, Vector2f.init_float2 (Binary32.ofBits 0x00000000 /- 0.0f -/) (Binary32.ofBits 0x00000000 /- 0.0f -/))

end AP_AHRS_DCM

namespace AP_AHRS_DCM

/-- C++ `bool AP_AHRS_DCM::get_vert_pos_rate_D(float & velocity) const`, `AP_AHRS/AP_AHRS_DCM.cpp:1480-1491`. -/
def get_vert_pos_rate_D (w : World) (velocity : Binary32) : World × Binary32 × Bool := Id.run do
  let mut w := w
  let mut velocity := velocity
  let mut velned : Vector3f.State := Vector3f.init_void
  let (t'1, t'2) := get_velocity_NED w velned
  velned := t'1
  if t'2 then
    velocity := velned.z
    return (w, velocity, true)
  else if AP_Baro.healthy_void w.barometer then
    let t'3 := w.barometer  -- the object out of the World for the call (--swap-out)
    w := { w with barometer := default }
    let (t'4, t'5) := AP_Baro.get_climb_rate t'3
    w := { w with barometer := t'4 }
    velocity := -t'5
    return (w, velocity, true)
  return (w, velocity, false)

end AP_AHRS_DCM

namespace AP_AHRS_DCM

/-- C++ `void AP_AHRS_DCM::get_results(Estimates & results)`, `AP_AHRS/AP_AHRS_DCM.cpp:172-307`. -/
def get_results (s : State) (w : World) (results : AP_AHRS_Backend.Estimates.State) : State × World × AP_AHRS_Backend.Estimates.State := Id.run do
  let mut s := s
  let mut w := w
  let mut results := results
  let now_ms : UInt32 := Estimator_lib.millis w
  results := { results with initialised := true }
  results := { results with healthy := (s._last_failure_ms == Int32.toUInt32 (0 : Int32) || decide (now_ms - s._last_failure_ms > Int32.toUInt32 (5000 : Int32))) }
  results := { results with primary_gyro := AP_InertialSensor.get_first_usable_gyro w.ins }
  results := { results with primary_accel := AP_InertialSensor.get_first_usable_accel w.ins }
  results := { results with roll_rad := s.roll }
  results := { results with pitch_rad := s.pitch }
  results := { results with yaw_rad := s.yaw }
  results := { results with dcm_matrix := s._body_dcm_matrix }
  results := { results with quaternion := Quaternion.from_rotation_matrix results.quaternion s._dcm_matrix }
  results := { results with quaternion := Quaternion.rotate_Vector3f results.quaternion (Vector3f.op_sub_void w.ahrs._trim._value) }
  results := { results with attitude_valid := true }
  results := { results with gyro_estimate := s._omega }
  results := { results with gyro_drift := s._omega_I }
  results := { results with accel_ef := s._accel_ef }
  let (t'1, t'2) := get_velocity_NED w results.velocity_NED
  results := { results with velocity_NED := t'1 }
  results := { results with velocity_NED_valid := t'2 }
  results := { results with have_velocity_source := have_gps w }
  let (t'3, t'4) := groundspeed_vector s w
  s := t'3
  results := { results with velocity_NE := t'4 }
  let (t'5, t'6, t'7) := get_vert_pos_rate_D w results.vert_pos_rate_D
  w := t'5
  results := { results with vert_pos_rate_D := t'6 }
  results := { results with vert_pos_rate_D_valid := t'7 }
  let (t'8, t'9) := get_location s w results.location
  results := { results with location := t'8 }
  results := { results with location_valid := t'9 }
  let mut origin : Location.State := Location.init_void
  let (t'10, t'11) := get_origin s w origin
  origin := t'10
  if t'11 && results.location_valid then
    let posNED : Vector3p.State := Location.get_distance_NED_postype origin results.location
    results := { results with position_NE := Vector3p.xy posNED }
    results := { results with position_NE_valid := true }
    results := { results with position_D := posNED.z }
    results := { results with position_D_valid := true }
  results := { results with wind := s._wind }
  results := { results with wind_valid := true }
  results := { results with configured_to_use_gps := AP_Enum_GPSUse.op_to_GPSUse w.ahrs._gps_use != GPSUse.Disable }
  results := { results with configured_to_use_gps_for_pos_XY := AP_Enum_GPSUse.op_to_GPSUse w.ahrs._gps_use != GPSUse.Disable }
  results := { results with control_ground_speed_limit_ms := (Binary32.ofBits 0x42480000 /- 50.0 -/) }
  results := { results with control_gain_scaler_XY := (Binary32.ofBits 0x3f000000 /- 0.5 -/) }
  results := { results with control_gain_scaler_Z := (Binary32.ofBits 0x3e800000 /- 0.25 -/) }
  results := fill_airspeed_estimate s w results
  return (s, w, results)

/-- C++ `const char * AP_AHRS_DCM::shortname() const`, `AP_AHRS/AP_AHRS_DCM.h:54`. -/
def shortname : String := Id.run do
  return "DCM"

end AP_AHRS_DCM

namespace AP_AHRS

/-- C++ `void AP_AHRS::update(bool skip_ins_update)`, `AP_AHRS/AP_AHRS.cpp:550-667`. -/
def update (s : State) (w : World) (o : Outputs) (inp : Inputs) (skip_ins_update : Bool := false) : State × World × Outputs := Id.run do
  let mut s := s
  let mut w := w
  let mut o := o
  let (t'1, t'2) := update_orientation s w inp
  w := t'2
  s := t'1
  if !skip_ins_update then
    let t'3 := w.ins  -- the object out of the World for the call (--swap-out)
    w := { w with ins := default }
    let (t'4, t'5, t'6) := AP_InertialSensor.update t'3 w o
    w := t'5
    w := { w with ins := t'4 }
    o := t'6
  pure ()  -- C++ `_getsem32`: a semaphore, which does nothing here (one thread, --semaphores)
  if !s._checked_watchdog_home then
    let (t'7, t'8) := load_watchdog_home s o inp
    s := t'7
    o := t'8
    s := { s with _checked_watchdog_home := true }
  pure ()  -- C++ `boost_end`: no effect in the model
  s := update_trim_rotation_matrices s
  s := update_flags s w
  let t'9 := s.configured_backend
  match t'9 with
  | .ahrs'ekf3 =>  -- C++ `ahrs.ekf3`
      w := { w with ahrs := s }  -- this object's state into the World: the call reaches it
      let (t'10, t'11, t'12) := AP_AHRS_NavEKF3.update s.ekf3 w o
      w := t'11
      s := w.ahrs  -- this object's state as the call left it
      s := { s with ekf3 := t'10 }
      o := t'12
  | .ahrs'dcm =>  -- C++ `ahrs.dcm`
      w := { w with ahrs := s }  -- this object's state into the World: the call reaches it
      let (t'13, t'14, t'15) := AP_AHRS_DCM.update s.dcm w o inp.dcm
      w := t'14
      s := w.ahrs  -- this object's state as the call left it
      s := { s with dcm := t'13 }
      o := t'15
  | .ahrs'sim =>  -- C++ `ahrs.sim`
      pure ()  -- C++ `AP_AHRS_SIM::update`: an empty body
  | _ => pure ()  -- (no other object: undefined in C++)
  let t'16 := ({} : AP_AHRS_Backend.Estimates.State)
  s := (match s.configured_estimates with | .ahrs'dcm_estimates => { s with dcm_estimates := t'16 } | .ahrs'ekf3_estimates => { s with ekf3_estimates := t'16 } | _ => { s with sim_estimates := t'16 })
  let t'17 := s.configured_backend
  match t'17 with
  | .ahrs'ekf3 =>  -- C++ `ahrs.ekf3`
      w := { w with ahrs := s }  -- this object's state into the World: the call reaches it
      let (t'18, t'19) := AP_AHRS_NavEKF3.get_results s.ekf3 w ((match s.configured_estimates with | .ahrs'dcm_estimates => s.dcm_estimates | .ahrs'ekf3_estimates => s.ekf3_estimates | _ => s.sim_estimates) : AP_AHRS_Backend.Estimates.State)
      w := t'18
      s := w.ahrs  -- this object's state as the call left it
      s := (match s.configured_estimates with | .ahrs'dcm_estimates => { s with dcm_estimates := t'19 } | .ahrs'ekf3_estimates => { s with ekf3_estimates := t'19 } | _ => { s with sim_estimates := t'19 })
  | .ahrs'dcm =>  -- C++ `ahrs.dcm`
      w := { w with ahrs := s }  -- this object's state into the World: the call reaches it
      let (t'20, t'21, t'22) := AP_AHRS_DCM.get_results s.dcm w ((match s.configured_estimates with | .ahrs'dcm_estimates => s.dcm_estimates | .ahrs'ekf3_estimates => s.ekf3_estimates | _ => s.sim_estimates) : AP_AHRS_Backend.Estimates.State)
      w := t'21
      s := w.ahrs  -- this object's state as the call left it
      s := { s with dcm := t'20 }
      s := (match s.configured_estimates with | .ahrs'dcm_estimates => { s with dcm_estimates := t'22 } | .ahrs'ekf3_estimates => { s with ekf3_estimates := t'22 } | _ => { s with sim_estimates := t'22 })
  | .ahrs'sim =>  -- C++ `ahrs.sim`
      pure ()  -- C++ `AP_AHRS_SIM::get_results(...)`: left out (--drop)
  | _ => pure ()  -- (no other object: undefined in C++)
  let (t'23, t'24, t'25) := try_set_common_origin s w o inp s.configured_backend s.configured_estimates
  w := t'24
  s := t'23
  o := t'25
  for t'26 in [0:3] do
    if s.backends_and_estimates[t'26]!.backend == s.configured_backend then
      continue
    let t'27 := s.backends_and_estimates[t'26]!.backend
    match t'27 with
    | .ahrs'ekf3 =>  -- C++ `ahrs.ekf3`
        w := { w with ahrs := s }  -- this object's state into the World: the call reaches it
        let (t'28, t'29, t'30) := AP_AHRS_NavEKF3.update s.ekf3 w o
        w := t'29
        s := w.ahrs  -- this object's state as the call left it
        s := { s with ekf3 := t'28 }
        o := t'30
    | .ahrs'dcm =>  -- C++ `ahrs.dcm`
        w := { w with ahrs := s }  -- this object's state into the World: the call reaches it
        let (t'31, t'32, t'33) := AP_AHRS_DCM.update s.dcm w o inp.dcm
        w := t'32
        s := w.ahrs  -- this object's state as the call left it
        s := { s with dcm := t'31 }
        o := t'33
    | .ahrs'sim =>  -- C++ `ahrs.sim`
        pure ()  -- C++ `AP_AHRS_SIM::update`: an empty body
    | _ => pure ()  -- (no other object: undefined in C++)
    let t'34 := s.backends_and_estimates[t'26]!.estimates
    let t'35 := ({} : AP_AHRS_Backend.Estimates.State)
    s := (match t'34 with | .ahrs'dcm_estimates => { s with dcm_estimates := t'35 } | .ahrs'ekf3_estimates => { s with ekf3_estimates := t'35 } | _ => { s with sim_estimates := t'35 })
    let t'36 := s.backends_and_estimates[t'26]!.backend
    match t'36 with
    | .ahrs'ekf3 =>  -- C++ `ahrs.ekf3`
        let t'37 := s.backends_and_estimates[t'26]!.estimates
        w := { w with ahrs := s }  -- this object's state into the World: the call reaches it
        let (t'38, t'39) := AP_AHRS_NavEKF3.get_results s.ekf3 w ((match t'37 with | .ahrs'dcm_estimates => s.dcm_estimates | .ahrs'ekf3_estimates => s.ekf3_estimates | _ => s.sim_estimates) : AP_AHRS_Backend.Estimates.State)
        w := t'38
        s := w.ahrs  -- this object's state as the call left it
        s := (match t'37 with | .ahrs'dcm_estimates => { s with dcm_estimates := t'39 } | .ahrs'ekf3_estimates => { s with ekf3_estimates := t'39 } | _ => { s with sim_estimates := t'39 })
    | .ahrs'dcm =>  -- C++ `ahrs.dcm`
        let t'40 := s.backends_and_estimates[t'26]!.estimates
        w := { w with ahrs := s }  -- this object's state into the World: the call reaches it
        let (t'41, t'42, t'43) := AP_AHRS_DCM.get_results s.dcm w ((match t'40 with | .ahrs'dcm_estimates => s.dcm_estimates | .ahrs'ekf3_estimates => s.ekf3_estimates | _ => s.sim_estimates) : AP_AHRS_Backend.Estimates.State)
        w := t'42
        s := w.ahrs  -- this object's state as the call left it
        s := { s with dcm := t'41 }
        s := (match t'40 with | .ahrs'dcm_estimates => { s with dcm_estimates := t'43 } | .ahrs'ekf3_estimates => { s with ekf3_estimates := t'43 } | _ => { s with sim_estimates := t'43 })
    | .ahrs'sim =>  -- C++ `ahrs.sim`
        pure ()  -- C++ `AP_AHRS_SIM::get_results(...)`: left out (--drop)
    | _ => pure ()  -- (no other object: undefined in C++)
    let (t'44, t'45, t'46) := try_set_common_origin s w o inp s.backends_and_estimates[t'26]!.backend s.backends_and_estimates[t'26]!.estimates
    w := t'45
    s := t'44
    o := t'46
  let (t'47, t'48) := fallback_synthetic_airspeed_EAS s w s.ekf3_estimates
  w := t'47
  s := { s with ekf3_estimates := t'48 }
  s := update_configured_ekf_type s
  s := update_active_EKF_type s w inp
  s := update_secondary_backend_pointers s
  o := update_notify_from_filter_status o ((match s.active_estimates with | .ahrs'dcm_estimates => s.dcm_estimates | .ahrs'ekf3_estimates => s.ekf3_estimates | _ => s.sim_estimates) : AP_AHRS_Backend.Estimates.State).filter_status
  s := update_reset_counters s
  if s.state.active_EKF_type != s.last_active_ekf_type then
    s := { s with last_active_ekf_type := s.state.active_EKF_type }
    let t'51 := "AHRS: %s active"
    let t'49 := s.active_backend
    let mut t'50 : String := ""
    match t'49 with
    | .ahrs'ekf3 =>  -- C++ `ahrs.ekf3`
        t'50 := AP_AHRS_NavEKF3.shortname
    | .ahrs'dcm =>  -- C++ `ahrs.dcm`
        t'50 := AP_AHRS_DCM.shortname
    | .ahrs'sim =>  -- C++ `ahrs.sim`
        t'50 := Estimator_lib.AP_AHRS_SIM_shortname
    | _ => pure ()  -- (no other object: undefined in C++)
    o := o.push (Output.send_text (6 : UInt32) t'51 #[Sum.inr t'50])
  let (t'52, t'53, t'54) := update_state s w o inp
  w := t'53
  s := t'52
  o := t'54
  if inp.opticalflow_set then
    o := o.push (Output.push_gyro_bias s.state.gyro_drift.x s.state.gyro_drift.y)
  if s._view != WPtr.null then
    w := { w with ahrs := s }  -- this object's state into the World: the call reaches it
    let t'55 := w.heap'AP_AHRS_View[(WPtr.index s._view)]!  -- the object out of its slot for the call (--swap-out)
    w := { w with heap'AP_AHRS_View := w.heap'AP_AHRS_View.set! (WPtr.index s._view) default }
    w := { w with heap'AP_AHRS_View := w.heap'AP_AHRS_View.set! (WPtr.index s._view) (AP_AHRS_View.update t'55 w) }
    s := w.ahrs  -- this object's state as the call left it
  pure ()  -- C++ `update_AOA_SSA`: no effect in the model
  let sitl' : WPtr := WPtr.sitl
  if Int16.toInt32 (AP_ParamT_short_2.op_to_short w.sitl.loop_time_jitter_us) > (0 : Int32) then
    let t'56 := w.est_scheduler  -- the object out of the World for the call (--swap-out)
    w := { w with est_scheduler := default }
    let (t'57, t'58, t'59) := EstScheduler.delay_microseconds t'56 w o (Int16.toUInt16 (Int64.toInt16 (inp.random % Int16.toInt64 (AP_ParamT_short_2.op_to_short w.sitl.loop_time_jitter_us))))
    w := t'58
    w := { w with est_scheduler := t'57 }
    o := t'59
  return (s, w, o)

end AP_AHRS

end Estimator_lib
