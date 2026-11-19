import ArduLean.Musl.atan2f
import ArduLean.Musl.cosf
import ArduLean.Musl.sinf
import ArduLean.Estimator.libraries.GCS_MAVLink.GCS_MAVLink
import ArduLean.Estimator.libraries.AP_Math.AP_Math
import ArduLean.Estimator.World
import ArduLean.Estimator.libraries.AP_Common.AP_Common
import ArduLean.Estimator.libraries.AP_Param.AP_Param
import ArduLean.Estimator.libraries.AP_NavEKF.AP_NavEKF
import ArduLean.Estimator.libraries.AP_GPS.AP_GPS
import ArduLean.Estimator.libraries.AP_InertialSensor.AP_InertialSensor
import ArduLean.Estimator.libraries.AP_NavEKF3.AP_NavEKF3
import ArduLean.Estimator.libraries.AP_AHRS.AP_AHRS
import ArduLean.Estimator.World_2
import ArduLean.Estimator.libraries.AP_Param.AP_Param_2
import ArduLean.Estimator.libraries.AP_NavEKF3.AP_NavEKF3_2
import ArduLean.Estimator.World_3
import ArduLean.Estimator.libraries.AP_Compass.AP_Compass_3
import ArduLean.Estimator.libraries.AP_NavEKF3.AP_NavEKF3_3
import ArduLean.Estimator.libraries.AP_AHRS.AP_AHRS_2
import ArduLean.Estimator.libraries.AP_Common.AP_Common_3
import ArduLean.Estimator.libraries.AP_InertialSensor.AP_InertialSensor_3
import ArduLean.Estimator.libraries.AP_NavEKF3.AP_NavEKF3_4

/-!
ArduPilot `libraries/AP_AHRS`, part 3 of 4. Sources: `libraries/AP_AHRS/AP_AHRS.cpp`, `libraries/AP_AHRS/AP_AHRS_DCM.cpp`, `libraries/AP_AHRS/AP_AHRS_NavEKF3.cpp`, `libraries/AP_AHRS/AP_AHRS.h`, `libraries/AP_AHRS/AP_AHRS_NavEKF3.h`, `libraries/AP_AHRS/AP_AHRS_View.h`.

Items of `lean/Estimator_lib.lean` (the estimator translation), unchanged; placed by `tools/split_modules.py` (`ArduLean/Estimator/INDEX.md`).
-/

open FloatLib.Floats (Binary32 Binary64)

set_option maxRecDepth 200000
-- AP_DAL's `const log_RISH old_RISH = _RISH;` read only by WRITE_REPLAY_BLOCK_IFCHANGED, which is `(void)old`
-- without logging (HAL_LOGGING_ENABLED 0): an unused binding, as in the C++
set_option linter.unusedVariables false

namespace Estimator_lib

namespace AP_AHRS_NavEKF3

/-- C++ `void AP_AHRS_NavEKF3::resetHeightDatum()`, `AP_AHRS/AP_AHRS_NavEKF3.h:71-73`. -/
def resetHeightDatum (w : World) (o : Outputs) : World × Outputs := Id.run do
  let mut w := w
  let mut o := o
  let (t'1, t'2, _) := NavEKF3.resetHeightDatum w.EKF3 w o
  w := t'1
  o := t'2
  return (w, o)

end AP_AHRS_NavEKF3

namespace AP_AHRS

/-- C++ `void AP_AHRS::resetHeightDatum()`, `AP_AHRS/AP_AHRS.cpp:1631-1639`. -/
def resetHeightDatum (s : State) (w : World) (o : Outputs) : World × Outputs := Id.run do
  let mut w := w
  let mut o := o
  pure ()  -- C++ `_getsem35`: a semaphore, which does nothing here (one thread, --semaphores)
  for t'1 in [0:3] do
    let t'2 := s.backends_and_estimates[t'1]!.backend
    match t'2 with
    | .ahrs'ekf3 =>  -- C++ `ahrs.ekf3`
        let (t'3, t'4) := AP_AHRS_NavEKF3.resetHeightDatum w o
        w := t'3
        o := t'4
    | .ahrs'dcm =>  -- C++ `ahrs.dcm`
        pure ()  -- C++ `resetHeightDatum`: no effect in the model
    | .ahrs'sim =>  -- C++ `ahrs.sim`
        pure ()  -- C++ `AP_AHRS_Backend::resetHeightDatum`: an empty body
    | _ => pure ()  -- (no other object: undefined in C++)
  return (w, o)

/-- C++ `bool AP_AHRS::get_location(Location & loc) const`, `AP_AHRS/AP_AHRS.cpp:2029-2033`. -/
def get_location (s : State) (loc : Location.State) : Location.State × Bool := Id.run do
  let mut loc := loc
  loc := s.state.location
  return (loc, s.state.location_ok)

end AP_AHRS

namespace AP_AHRS_DCM

/-- C++ `void AP_AHRS_DCM::reset(bool recover_eulers)`, `AP_AHRS/AP_AHRS_DCM.cpp:350-410`. -/
def reset_bool (s : State) (w : World) (o : Outputs) (inp : Inputs) (recover_eulers : Bool) : State × World × Outputs := Id.run do
  let mut s := s
  let mut w := w
  let mut o := o
  s := { s with _omega_I := Vector3f.zero s._omega_I }
  s := { s with _omega_P := Vector3f.zero s._omega_P }
  s := { s with _omega_yaw_P := Vector3f.zero s._omega_yaw_P }
  s := { s with _omega := Vector3f.zero s._omega }
  if inp.was_watchdog_reset && decide (Estimator_lib.millis w < Int32.toUInt32 (10000 : Int32)) then
    s := { s with roll := inp.persistent_data_roll_rad }
    s := { s with pitch := inp.persistent_data_pitch_rad }
    s := { s with yaw := inp.persistent_data_yaw_rad }
    s := { s with _dcm_matrix := Matrix3f.from_euler s._dcm_matrix s.roll s.pitch s.yaw }
    o := o.push (Output.send_text (6 : UInt32) "Restored watchdog attitude %.0f %.0f %.0f" #[Sum.inl (Binary64.toBits (Binary32.toBinary64 (Estimator_lib.degrees s.roll))), Sum.inl (Binary64.toBits (Binary32.toBinary64 (Estimator_lib.degrees s.pitch))), Sum.inl (Binary64.toBits (Binary32.toBinary64 (Estimator_lib.degrees s.yaw)))])
  else if recover_eulers && !(Binary32.isNaN s.roll) && !(Binary32.isNaN s.pitch) && !(Binary32.isNaN s.yaw) then
    s := { s with _dcm_matrix := Matrix3f.from_euler s._dcm_matrix s.roll s.pitch s.yaw }
  else
    let mut initAccVec : Vector3f.State := AP_InertialSensor.get_accel_void w.ins
    let mut counter : UInt8 := Int8.toUInt8 (Int32.toInt8 (0 : Int32))
    for _ in [0:2^64] do  -- C loop without a constant trip count (--general-loops)
      let mut t'2 := (decide (Vector3f.length initAccVec < (Binary32.ofBits 0x41100000 /- 9.0f -/)) || decide (Vector3f.length initAccVec > (Binary32.ofBits 0x41300000 /- 11 -/)))
      if t'2 then
        let t'1 := counter
        counter := counter + (1 : UInt8)
        t'2 := decide (UInt32.toInt32 (UInt8.toUInt32 t'1) < (20 : Int32))
      if !t'2 then break
      let t'3 := w.ins  -- the object out of the World for the call (--swap-out)
      w := { w with ins := default }
      let (t'4, t'5, t'6) := AP_InertialSensor.wait_for_sample t'3 w o
      w := t'5
      w := { w with ins := t'4 }
      o := t'6
      let t'7 := w.ins  -- the object out of the World for the call (--swap-out)
      w := { w with ins := default }
      let (t'8, t'9, t'10) := AP_InertialSensor.update t'7 w o
      w := t'9
      w := { w with ins := t'8 }
      o := t'10
      initAccVec := AP_InertialSensor.get_accel_void w.ins
    if Vector3f.length initAccVec > (Binary32.ofBits 0x40a00000 /- 5.0f -/) then
      s := { s with pitch := Musl.atan2f.atan2f initAccVec.x (Estimator_lib.norm_float2 initAccVec.y initAccVec.z) }
      s := { s with roll := Musl.atan2f.atan2f (-initAccVec.y) (-initAccVec.z) }
    else
      s := { s with roll := (Binary32.ofBits 0x00000000 /- 0.0f -/) }
      s := { s with pitch := (Binary32.ofBits 0x00000000 /- 0.0f -/) }
    s := { s with _dcm_matrix := Matrix3f.from_euler s._dcm_matrix s.roll s.pitch (Binary32.ofBits 0x00000000 /- 0 -/) }
  s := { s with _cos_yaw := Musl.cosf.cosf s.yaw }
  s := { s with _sin_yaw := Musl.sinf.sinf s.yaw }
  s := { s with _last_startup_ms := Estimator_lib.millis w }
  return (s, w, o)

/-- C++ `void AP_AHRS_DCM::reset()`, `AP_AHRS/AP_AHRS_DCM.h:63`. -/
def reset_void (s : State) (w : World) (o : Outputs) (inp : Inputs) : State × World × Outputs := Id.run do
  let mut s := s
  let mut w := w
  let mut o := o
  let (t'1, t'2, t'3) := reset_bool s w o inp false
  w := t'2
  s := t'1
  o := t'3
  return (s, w, o)

end AP_AHRS_DCM

namespace AP_AHRS_NavEKF3

/-- C++ `void AP_AHRS_NavEKF3::reset()`, `AP_AHRS/AP_AHRS_NavEKF3.h:43-48`. -/
def reset (s : State) (w : World) (o : Outputs) : State × World × Outputs := Id.run do
  let mut s := s
  let mut w := w
  let mut o := o
  if !s.started then
    return (s, w, o)
  let t'1 := w.EKF3  -- the object out of the World for the call (--swap-out)
  w := { w with EKF3 := default }
  let (t'2, t'3, t'4, t'5) := NavEKF3.InitialiseFilter t'1 w o
  w := t'3
  w := { w with EKF3 := t'2 }
  o := t'4
  s := { s with started := t'5 }
  return (s, w, o)

end AP_AHRS_NavEKF3

namespace AP_AHRS

/-- C++ `void AP_AHRS::reset()`, `AP_AHRS/AP_AHRS.cpp:676-684`. -/
def reset (s : State) (w : World) (o : Outputs) (inp : Inputs) : State × World × Outputs := Id.run do
  let mut s := s
  let mut w := w
  let mut o := o
  pure ()  -- C++ `_getsem33`: a semaphore, which does nothing here (one thread, --semaphores)
  for t'1 in [0:3] do
    let t'2 := s.backends_and_estimates[t'1]!.backend
    match t'2 with
    | .ahrs'ekf3 =>  -- C++ `ahrs.ekf3`
        w := { w with ahrs := s }  -- this object's state into the World: the call reaches it
        let (t'3, t'4, t'5) := AP_AHRS_NavEKF3.reset s.ekf3 w o
        w := t'4
        s := w.ahrs  -- this object's state as the call left it
        s := { s with ekf3 := t'3 }
        o := t'5
    | .ahrs'dcm =>  -- C++ `ahrs.dcm`
        let (t'6, t'7, t'8) := AP_AHRS_DCM.reset_void s.dcm w o inp.dcm
        w := t'7
        s := { s with dcm := t'6 }
        o := t'8
    | .ahrs'sim =>  -- C++ `ahrs.sim`
        pure ()  -- C++ `AP_AHRS_SIM::reset`: an empty body
    | _ => pure ()  -- (no other object: undefined in C++)
  return (s, w, o)

/-- C++ `void AP_AHRS::load_watchdog_home()`, `AP_AHRS/AP_AHRS.cpp:1794-1805`. -/
def load_watchdog_home (s : State) (o : Outputs) (inp : Inputs) : State × Outputs := Id.run do
  let mut s := s
  let mut o := o
  if inp.was_watchdog_reset && (inp.persistent_data_home_lat != (0 : Int32) || inp.persistent_data_home_lon != (0 : Int32)) then
    s := { s with _home.lat := inp.persistent_data_home_lat }
    s := { s with _home.lng := inp.persistent_data_home_lon }
    s := { s with _home := Location.set_alt_cm s._home inp.persistent_data_home_alt_cm Location.AltFrame.ABSOLUTE }
    s := { s with _home_is_set := true }
    s := { s with _home_locked := true }
    o := o.push (Output.send_text (6 : UInt32) "Restored watchdog home" #[])
  return (s, o)

end AP_AHRS

namespace AP_AHRS_DCM

/-- C++ `void AP_AHRS_DCM::matrix_update()`, `AP_AHRS/AP_AHRS_DCM.cpp:321-343`. -/
def matrix_update (s : State) (w : World) : State := Id.run do
  let mut s := s
  let mut delta_angle : Vector3f.State := Vector3f.init_void
  let mut dangle_dt : Binary32 := (Binary32.ofBits 0x00000000 /- 0.0 -/)  -- uninitialized in C++; assigned before every read
  let (t'1, t'2, t'3) := AP_InertialSensor.get_delta_angle_Vector3f_float w.ins delta_angle dangle_dt
  delta_angle := t'1
  dangle_dt := t'2
  if t'3 && decide (dangle_dt > (Binary32.ofBits 0x00000000 /- 0 -/)) then
    s := { s with _omega := Vector3f.op_div delta_angle dangle_dt }
    let (t'4, _) := Vector3f.op_add_assign s._omega s._omega_I
    s := { s with _omega := t'4 }
    s := { s with _dcm_matrix := Matrix3f.rotate s._dcm_matrix (Vector3f.op_mul_float (Vector3f.op_add (Vector3f.op_add s._omega s._omega_P) s._omega_yaw_P) dangle_dt) }
  s := { s with _omega := Vector3f.op_add (AP_InertialSensor.get_gyro_void w.ins) s._omega_I }
  return s

/-- C++ `bool AP_AHRS_DCM::renorm(const Vector3f & a, Vector3f & result)`, `AP_AHRS/AP_AHRS_DCM.cpp:448-490`. -/
def renorm (s : State) (a : Vector3f.State) (result : Vector3f.State) : State × Vector3f.State × Bool := Id.run do
  let mut s := s
  let mut result := result
  let renorm_val : Binary32 := (Binary32.ofBits 0x3f800000 /- 1.0f -/) / Vector3f.length a
  s := { s with _renorm_val_sum := s._renorm_val_sum + renorm_val }
  s := { s with _renorm_val_count := s._renorm_val_count + (1 : UInt16) }
  if !(decide (renorm_val < (Binary32.ofBits 0x40000000 /- 2.0f -/)) && decide (renorm_val > (Binary32.ofBits 0x3f000000 /- 0.5f -/))) then
    if !(decide (renorm_val < (Binary32.ofBits 0x49742400 /- 1.0e6f -/)) && decide (renorm_val > (Binary32.ofBits 0x358637bd /- 1.0e-6f -/))) then
      return (s, result, false)
  result := Vector3f.op_mul_float a renorm_val
  return (s, result, true)

/-- C++ `void AP_AHRS_DCM::normalize()`, `AP_AHRS/AP_AHRS_DCM.cpp:502-519`. -/
def normalize (s : State) (w : World) (o : Outputs) (inp : Inputs) : State × World × Outputs := Id.run do
  let mut s := s
  let mut w := w
  let mut o := o
  let error : Binary32 := Vector3f.op_mul_Vector3f s._dcm_matrix.a s._dcm_matrix.b
  let t0 : Vector3f.State := Vector3f.op_sub_Vector3f s._dcm_matrix.a (Vector3f.op_mul_float s._dcm_matrix.b ((Binary32.ofBits 0x3f000000 /- 0.5f -/) * error))
  let t1 : Vector3f.State := Vector3f.op_sub_Vector3f s._dcm_matrix.b (Vector3f.op_mul_float s._dcm_matrix.a ((Binary32.ofBits 0x3f000000 /- 0.5f -/) * error))
  let t2 : Vector3f.State := Vector3f.op_mod t0 t1
  let (t'1, t'2, t'3) := renorm s t0 s._dcm_matrix.a
  s := t'1
  s := { s with _dcm_matrix.a := t'2 }
  let mut t'7 := !t'3
  if !t'7 then
    let (t'4, t'5, t'6) := renorm s t1 s._dcm_matrix.b
    s := t'4
    s := { s with _dcm_matrix.b := t'5 }
    t'7 := !t'6
  let mut t'11 := t'7
  if !t'11 then
    let (t'8, t'9, t'10) := renorm s t2 s._dcm_matrix.c
    s := t'8
    s := { s with _dcm_matrix.c := t'9 }
    t'11 := !t'10
  if t'11 then
    s := { s with _last_failure_ms := Estimator_lib.millis w }
    let (t'12, t'13, t'14) := reset_bool s w o inp true
    w := t'13
    s := t'12
    o := t'14
  return (s, w, o)

end AP_AHRS_DCM

namespace AP_AHRS_DCM

/-- C++ `void AP_AHRS_DCM::check_matrix()`, `AP_AHRS/AP_AHRS_DCM.cpp:415-444`. -/
def check_matrix (s : State) (w : World) (o : Outputs) (inp : Inputs) : State × World × Outputs := Id.run do
  let mut s := s
  let mut w := w
  let mut o := o
  if Matrix3f.is_nan s._dcm_matrix then
    let (t'1, t'2, t'3) := reset_bool s w o inp true
    w := t'2
    s := t'1
    o := t'3
    return (s, w, o)
  if !(decide (s._dcm_matrix.c.x < (Binary32.ofBits 0x3f800000 /- 1.0f -/)) && decide (s._dcm_matrix.c.x > -(Binary32.ofBits 0x3f800000 /- 1.0f -/))) then
    let (t'4, t'5, t'6) := normalize s w o inp
    w := t'5
    s := t'4
    o := t'6
    if Matrix3f.is_nan s._dcm_matrix || decide (Binary32.abs s._dcm_matrix.c.x > (Binary32.ofBits 0x41200000 /- 10.0 -/)) then
      let (t'7, t'8, t'9) := reset_bool s w o inp true
      w := t'8
      s := t'7
      o := t'9
  return (s, w, o)

/-- C++ `bool AP_AHRS_DCM::have_gps() const`, `AP_AHRS/AP_AHRS_DCM.cpp:588-594`. -/
def have_gps (w : World) : Bool := Id.run do
  if AP_Enum_GPSUse.op_to_GPSUse w.ahrs._gps_use == GPSUse.Disable || decide (AP_GPS_FixType.toInt (AP_GPS.status_void w.gps) ≤ AP_GPS_FixType.toInt AP_GPS_FixType.NONE) then
    return false
  return true

end AP_AHRS_DCM

namespace AP_AHRS_DCM

/-- C++ `bool AP_AHRS_DCM::use_compass()`, `AP_AHRS/AP_AHRS_DCM.cpp:611-645`. -/
def use_compass (s : State) (w : World) : State × Bool := Id.run do
  let mut s := s
  if !(Compass.use_for_yaw_void w.compass) then
    return (s, false)
  if !(AP_AHRS.get_fly_forward w.ahrs) || !(have_gps w) then
    return (s, true)
  if AP_GPS.ground_speed_void w.gps < (Binary32.ofBits 0x40400000 /- (float)3 -/) then
    return (s, true)
  let error : Binary32 := Binary32.abs (Estimator_lib.wrap_180_float (Estimator_lib.degrees s.yaw - AP_GPS.ground_course_void w.gps))
  if decide (error > (Binary32.ofBits 0x42340000 /- 45 -/)) && decide (Vector2f.length ({ x := s._wind.x, y := s._wind.y } : Vector2f.State) < AP_GPS.ground_speed_void w.gps * (Binary32.ofBits 0x3f4ccccd /- 0.8f -/)) then
    if Estimator_lib.millis w - s._last_consistent_heading > Int32.toUInt32 (2000 : Int32) then
      return (s, false)
  else
    s := { s with _last_consistent_heading := Estimator_lib.millis w }
  return (s, true)

/-- C++ `float AP_AHRS_DCM::_P_gain(float spin_rate)`, `AP_AHRS/AP_AHRS_DCM.cpp:556-566`. -/
def _P_gain (spin_rate : Binary32) : Binary32 := Id.run do
  if spin_rate < Estimator_lib.radians_int32_t (50 : Int32) then
    return (Binary32.ofBits 0x3f800000 /- 1.0f -/)
  if spin_rate > Estimator_lib.radians_int32_t (500 : Int32) then
    return (Binary32.ofBits 0x41200000 /- 10.0f -/)
  return spin_rate / Estimator_lib.radians_int32_t (50 : Int32)

/-- C++ `bool AP_AHRS_DCM::use_fast_gains() const`, `AP_AHRS/AP_AHRS_DCM.cpp:604-607`. -/
def use_fast_gains (s : State) (w : World) (inp : Inputs) : Bool := Id.run do
  return !inp.get_soft_armed && decide ((Estimator_lib.millis w - s._last_startup_ms) < (20000 : UInt32))

end AP_AHRS_DCM

namespace AP_AHRS_NavEKF3

/-- C++ `bool AP_AHRS_NavEKF3::start()`, `AP_AHRS/AP_AHRS_NavEKF3.cpp:15-43`. -/
def start (s : State) (w : World) (o : Outputs) : State × World × Outputs × Bool := Id.run do
  let mut s := s
  let mut w := w
  let mut o := o
  let now_ms : UInt32 := Estimator_lib.millis w
  if s.start_time_ms == Int32.toUInt32 (0 : Int32) then
    s := { s with start_time_ms := now_ms }
  if now_ms - s.start_time_ms ≤ Int32.toUInt32 (1000 : Int32) then
    return (s, w, o, false)
  let t'1 := w.EKF3  -- the object out of the World for the call (--swap-out)
  w := { w with EKF3 := default }
  let (t'2, t'3, t'4, t'5) := NavEKF3.InitialiseFilter t'1 w o
  w := t'3
  w := { w with EKF3 := t'2 }
  o := t'4
  return (s, w, o, t'5)

end AP_AHRS_NavEKF3

namespace AP_AHRS_NavEKF3

/-- C++ `void AP_AHRS_NavEKF3::update()`, `AP_AHRS/AP_AHRS_NavEKF3.cpp:45-68`. -/
def update (s : State) (w : World) (o : Outputs) : State × World × Outputs := Id.run do
  let mut s := s
  let mut w := w
  let mut o := o
  if !s.started then
    let (t'1, t'2, t'3, t'4) := start s w o
    w := t'2
    s := t'1
    o := t'3
    s := { s with started := t'4 }
  if !s.started then
    return (s, w, o)
  let t'5 := w.EKF3  -- the object out of the World for the call (--swap-out)
  w := { w with EKF3 := default }
  let (t'6, t'7, t'8) := NavEKF3.UpdateFilter t'5 w o
  w := t'7
  w := { w with EKF3 := t'6 }
  o := t'8
  let primary_core : Int8 := NavEKF3.getPrimaryCoreIndex w.EKF3
  let (t'9, t'10) := AP_AHRS_ResetCounter_signed_char.update s.attitude_reset_tracker primary_core
  s := { s with attitude_reset_tracker := t'9 }
  if t'10 then
    o := o.push (Output.send_text (4 : UInt32) "EKF3 primary changed:%d" #[Sum.inl (UInt32.toUInt64 (Int32.toUInt32 (Int8.toInt32 primary_core)))])
  let t'11 := w.EKF3  -- the object out of the World for the call (--swap-out)
  w := { w with EKF3 := default }
  let (t'12, t'13) := NavEKF3.getYawResetCount t'11 w
  w := { w with EKF3 := t'12 }
  let (t'14, _) := AP_AHRS_ResetCounter_unsigned_short.update s.yaw_reset_tracker t'13
  s := { s with yaw_reset_tracker := t'14 }
  let t'16 := w.EKF3  -- the object out of the World for the call (--swap-out)
  w := { w with EKF3 := default }
  let (t'17, t'18) := NavEKF3.getPosNorthEastResetCount t'16 w
  w := { w with EKF3 := t'17 }
  let (t'19, _) := AP_AHRS_ResetCounter_unsigned_short.update s.position_NE_reset_tracker t'18
  s := { s with position_NE_reset_tracker := t'19 }
  let t'21 := w.EKF3  -- the object out of the World for the call (--swap-out)
  w := { w with EKF3 := default }
  let (t'22, t'23) := NavEKF3.getPosDownResetCount t'21 w
  w := { w with EKF3 := t'22 }
  let (t'24, _) := AP_AHRS_ResetCounter_unsigned_short.update s.position_D_reset_tracker t'23
  s := { s with position_D_reset_tracker := t'24 }
  return (s, w, o)

end AP_AHRS_NavEKF3

namespace AP_AHRS_NavEKF3

/-- C++ `void AP_AHRS_NavEKF3::get_results(Estimates & results)`, `AP_AHRS/AP_AHRS_NavEKF3.cpp:70-244`. -/
def get_results (s : State) (w : World) (results : AP_AHRS_Backend.Estimates.State) : World × AP_AHRS_Backend.Estimates.State := Id.run do
  let mut w := w
  let mut results := results
  let now_ms : UInt32 := Estimator_lib.millis w
  results := { results with initialised := (s.started && (decide (now_ms - s.start_time_ms > Int32.toUInt32 (20000 : Int32)))) }
  results := { results with healthy := s.started && NavEKF3.healthy w.EKF3 w }
  let ek3_primary_gyro : Int8 := NavEKF3.getPrimaryCoreIMUIndex w.EKF3 w
  if Int8.toInt32 ek3_primary_gyro == -(1 : Int32) then
    results := { results with primary_gyro := AP_InertialSensor.get_first_usable_gyro w.ins }
  else
    results := { results with primary_gyro := Int8.toUInt8 ek3_primary_gyro }
  let mut drift : Vector3f.State := Vector3f.init_void
  drift := NavEKF3.getGyroBias w.EKF3 w (Int32.toInt8 (-(1 : Int32))) drift
  results := { results with gyro_drift := Vector3f.op_sub_void drift }
  let t'1 := results.primary_gyro
  results := { results with gyro_estimate := Vector3f.op_add w.ins._gyro[UInt8.toNat t'1]! results.gyro_drift }
  results := { results with dcm_matrix := NavEKF3.getRotationBodyToNED w.EKF3 w results.dcm_matrix }
  let mut eulers : Vector3f.State := Vector3f.init_void
  eulers := NavEKF3.getEulerAngles w.EKF3 w eulers
  results := { results with roll_rad := eulers.x }
  results := { results with pitch_rad := eulers.y }
  results := { results with yaw_rad := eulers.z }
  results := { results with quaternion := NavEKF3.getQuaternion w.EKF3 w results.quaternion }
  results := { results with quaternion := Quaternion.rotate_Vector3f results.quaternion (Vector3f.op_sub_void w.ahrs._trim._value) }
  results := { results with attitude_valid := s.started }
  results := { results with attitude_reset_count := AP_AHRS_ResetCounter_signed_char.count s.attitude_reset_tracker }
  results := { results with yaw_reset_count := AP_AHRS_ResetCounter_unsigned_short.count s.yaw_reset_tracker }
  results := { results with is_vibration_affected := NavEKF3.isVibrationAffected w.EKF3 w }
  let ek3_primary_accel : Int8 := NavEKF3.getPrimaryCoreIMUIndex w.EKF3 w
  if Int8.toInt32 ek3_primary_accel == -(1 : Int32) then
    results := { results with primary_accel := AP_InertialSensor.get_first_usable_accel w.ins }
  else
    results := { results with primary_accel := Int8.toUInt8 ek3_primary_accel }
  results := { results with accel_bias := NavEKF3.getAccelBias w.EKF3 w (Int32.toInt8 (-(1 : Int32))) results.accel_bias }
  let mut accel : Vector3f.State := AP_InertialSensor.get_accel_uint8_t w.ins results.primary_accel
  let (t'2, _) := Vector3f.op_sub_assign accel results.accel_bias
  accel := t'2
  results := { results with accel_ef := Matrix3f.op_mul_Vector3f (Matrix3f.op_mul_Matrix3f results.dcm_matrix (AP_AHRS.get_rotation_autopilot_body_to_vehicle_body w.ahrs)) accel }
  results := { results with velocity_NED := NavEKF3.getVelNED w.EKF3 w results.velocity_NED }
  results := { results with velocity_NED_valid := true }
  results := { results with vert_pos_rate_D := NavEKF3.getPosDownDerivative w.EKF3 w }
  results := { results with vert_pos_rate_D_valid := true }
  results := { results with velocity_NE := Vector3f.xy results.velocity_NED }
  let (t'4, t'5, t'6) := NavEKF3.getLLH w.EKF3 w results.location
  w := t'4
  results := { results with location := t'5 }
  results := { results with location_valid := t'6 }
  results := { results with provides_common_origin := true }
  let (t'7, t'8, t'9) := NavEKF3.getPosNE w.EKF3 w results.position_NE
  w := t'7
  results := { results with position_NE := t'8 }
  results := { results with position_NE_valid := t'9 }
  results := { results with position_NE_reset_count := AP_AHRS_ResetCounter_unsigned_short.count s.position_NE_reset_tracker }
  let (t'10, t'11, t'12) := NavEKF3.getPosD w.EKF3 w results.position_D
  w := t'10
  results := { results with position_D := t'11 }
  results := { results with position_D_valid := t'12 }
  results := { results with position_D_reset_count := AP_AHRS_ResetCounter_unsigned_short.count s.position_D_reset_tracker }
  let (t'13, t'14) := NavEKF3.getHAGL w.EKF3 w results.hagl
  results := { results with hagl := t'13 }
  results := { results with hagl_valid := t'14 }
  let (t'15, t'16) := NavEKF3.getWind w.EKF3 w results.wind
  results := { results with wind := t'15 }
  results := { results with wind_valid := t'16 }
  let t'17 := w.EKF3  -- the object out of the World for the call (--swap-out)
  w := { w with EKF3 := default }
  let (t'18, t'19, t'20) := NavEKF3.using_gps t'17 w
  w := t'19
  w := { w with EKF3 := t'18 }
  results := { results with configured_to_use_gps := t'20 }
  results := { results with configured_to_use_gps_for_pos_XY := NavEKF3.configuredToUseGPSForPosXY w.EKF3 }
  results := { results with using_extnav_for_yaw := NavEKF3.using_extnav_for_yaw w.EKF3 w }
  results := { results with using_noncompass_for_yaw := NavEKF3.using_noncompass_for_yaw w.EKF3 w }
  results := { results with filter_status := NavEKF3.getFilterStatus w.EKF3 w results.filter_status }
  results := { results with filter_status_valid := true }
  results := { results with filter_faults := NavEKF3.getFilterFaults w.EKF3 w results.filter_faults }
  let mut offset : Vector2f.State := Vector2f.init_void
  let (t'21, t'22, t'23, t'24, t'25, t'26, t'27) := NavEKF3.getVariances w.EKF3 w results.velVar results.posVar results.hgtVar results.magVar results.tasVar offset
  results := { results with velVar := t'21 }
  results := { results with posVar := t'22 }
  results := { results with hgtVar := t'23 }
  results := { results with magVar := t'24 }
  results := { results with tasVar := t'25 }
  offset := t'26
  results := { results with variances_valid := t'27 }
  let (t'28, t'29, t'30) := NavEKF3.getTerrainAltVariance w.EKF3 w results.terrain_alt_variance
  w := t'28
  results := { results with terrain_alt_variance := t'29 }
  results := { results with terrain_alt_variance_valid := t'30 }
  let (t'31, t'32, t'33) := NavEKF3.getEkfControlLimits w.EKF3 w results.control_ground_speed_limit_ms results.control_gain_scaler_XY
  w := t'31
  results := { results with control_ground_speed_limit_ms := t'32 }
  results := { results with control_gain_scaler_XY := t'33 }
  results := { results with control_gain_scaler_Z := (Binary32.ofBits 0x3f800000 /- 1 -/) }
  let (t'34, t'35, t'36) := NavEKF3.getHeightControlLimit w.EKF3 w results.control_height_limit_m
  w := t'34
  results := { results with control_height_limit_m := t'35 }
  results := { results with control_height_limit_valid := t'36 }
  results := fill_airspeed_estimate w results
  return (w, results)

/-- C++ `const char * AP_AHRS_NavEKF3::shortname() const`, `AP_AHRS/AP_AHRS_NavEKF3.h:36`. -/
def shortname : String := Id.run do
  return "EKF3"

end AP_AHRS_NavEKF3

namespace AP_AHRS

/-- C++ `bool AP_AHRS::set_home(const Location & loc)`, `AP_AHRS/AP_AHRS.cpp:1744-1791`. -/
def set_home (s : State) (w : World) (o : Outputs) (loc : Location.State) : State × World × Outputs × Bool := Id.run do
  let mut s := s
  let mut w := w
  let mut o := o
  pure ()  -- C++ `_getsem36`: a semaphore, which does nothing here (one thread, --semaphores)
  if !(Location.initialised loc) then
    return (s, w, o, false)
  if !(Location.check_latlng loc) then
    return (s, w, o, false)
  let mut tmp : Location.State := loc
  w := { w with ahrs := s }  -- this object's state into the World: the call reaches it
  let (t'1, t'2) := Location.change_alt_frame tmp w Location.AltFrame.ABSOLUTE
  tmp := t'1
  if !t'2 then
    return (s, w, o, false)
  s := { s with _home := tmp }
  s := { s with _home_is_set := true }
  o := o.push (Output.send_message ap_message.MSG_HOME)
  o := o.push (Output.send_message ap_message.MSG_ORIGIN)
  o := o.push (Output.hal_util_persistent_data_home_lat loc.lat)
  o := o.push (Output.hal_util_persistent_data_home_lon loc.lng)
  o := o.push (Output.hal_util_persistent_data_home_alt_cm loc.alt)
  o := o.push (Output.write_home_to_storage)
  return (s, w, o, true)

/-- C++ `void AP_AHRS::lock_home()`, `AP_AHRS/AP_AHRS.h:598-600`. -/
def lock_home (s : State) : State := Id.run do
  let mut s := s
  s := { s with _home_locked := true }
  return s

end AP_AHRS

namespace AP_AHRS_NavEKF3

/-- C++ `void AP_AHRS_NavEKF3::check_lane_switch()`, `AP_AHRS/AP_AHRS_NavEKF3.h:77-79`. -/
def check_lane_switch (w : World) (o : Outputs) : World × Outputs := Id.run do
  let mut w := w
  let mut o := o
  let t'1 := w.EKF3  -- the object out of the World for the call (--swap-out)
  w := { w with EKF3 := default }
  let (t'2, t'3, t'4) := NavEKF3.checkLaneSwitch t'1 w o
  w := t'3
  w := { w with EKF3 := t'2 }
  o := t'4
  return (w, o)

end AP_AHRS_NavEKF3

namespace AP_AHRS

/-- C++ `void AP_AHRS::check_lane_switch()`, `AP_AHRS/AP_AHRS.h:467-469`. -/
def check_lane_switch (s : State) (w : World) (o : Outputs) : World × Outputs := Id.run do
  let mut w := w
  let mut o := o
  let t'1 := s.active_backend
  match t'1 with
  | .ahrs'ekf3 =>  -- C++ `ahrs.ekf3`
      let (t'2, t'3) := AP_AHRS_NavEKF3.check_lane_switch w o
      w := t'2
      o := t'3
  | .ahrs'dcm =>  -- C++ `ahrs.dcm`
      pure ()  -- C++ `check_lane_switch`: no effect in the model
  | .ahrs'sim =>  -- C++ `ahrs.sim`
      pure ()  -- C++ `AP_AHRS_Backend::check_lane_switch`: an empty body
  | _ => pure ()  -- (no other object: undefined in C++)
  return (w, o)

/-- C++ `bool AP_AHRS::get_quaternion(Quaternion & quat) const`, `AP_AHRS/AP_AHRS.cpp:2076-2080`. -/
def get_quaternion (s : State) (quat : Quaternion.State) : Quaternion.State × Bool := Id.run do
  let mut quat := quat
  quat := s.state.quat
  return (quat, s.state.quat_ok)

/-- C++ `float AP_AHRS::get_roll_rad() const`, `AP_AHRS/AP_AHRS.h:628`. -/
def get_roll_rad (s : State) : Binary32 := Id.run do
  return s.roll

/-- C++ `float AP_AHRS::get_pitch_rad() const`, `AP_AHRS/AP_AHRS.h:629`. -/
def get_pitch_rad (s : State) : Binary32 := Id.run do
  return s.pitch

/-- C++ `float AP_AHRS::get_yaw_rad() const`, `AP_AHRS/AP_AHRS.h:630`. -/
def get_yaw_rad (s : State) : Binary32 := Id.run do
  return s.yaw

/-- C++ `bool AP_AHRS::get_velocity_NED(Vector3f & vec) const`, `AP_AHRS/AP_AHRS.cpp:2091-2095`. -/
def get_velocity_NED (s : State) (vec : Vector3f.State) : Vector3f.State × Bool := Id.run do
  let mut vec := vec
  vec := s.state.velocity_NED
  return (vec, s.state.velocity_NED_ok)

/-- C++ `bool AP_AHRS::get_relative_position_NED_origin(Vector3p & vec) const`, `AP_AHRS/AP_AHRS.h:263-267`. -/
def get_relative_position_NED_origin (s : State) (vec : Vector3p.State) : Vector3p.State × Bool := Id.run do
  let mut vec := vec
  let t'1 := ((match s.active_estimates with | .ahrs'dcm_estimates => s.dcm_estimates | .ahrs'ekf3_estimates => s.ekf3_estimates | _ => s.sim_estimates) : AP_AHRS_Backend.Estimates.State).position_NE
  vec := { vec with x := t'1.x, y := t'1.y }
  vec := { vec with z := ((match s.active_estimates with | .ahrs'dcm_estimates => s.dcm_estimates | .ahrs'ekf3_estimates => s.ekf3_estimates | _ => s.sim_estimates) : AP_AHRS_Backend.Estimates.State).position_D }
  return (vec, (((match s.active_estimates with | .ahrs'dcm_estimates => s.dcm_estimates | .ahrs'ekf3_estimates => s.ekf3_estimates | _ => s.sim_estimates) : AP_AHRS_Backend.Estimates.State).position_NE_valid && ((match s.active_estimates with | .ahrs'dcm_estimates => s.dcm_estimates | .ahrs'ekf3_estimates => s.ekf3_estimates | _ => s.sim_estimates) : AP_AHRS_Backend.Estimates.State).position_D_valid))

/-- C++ `const Vector3f & AP_AHRS::get_accel_ef() const`, `AP_AHRS/AP_AHRS.h:212-214`. -/
def get_accel_ef (s : State) : Vector3f.State := Id.run do
  return s.state.accel_ef

/-- C++ `uint16_t AP_AHRS::get_last_attitude_reset_count() const`, `AP_AHRS/AP_AHRS.h:376-378`. -/
def get_last_attitude_reset_count (s : State) : UInt16 := Id.run do
  return AP_AHRS_ResetCounter_unsigned_short.count s.attitude_reset_tracker

/-- C++ `uint16_t AP_AHRS::get_yaw_reset_count() const`, `AP_AHRS/AP_AHRS.h:361-363`. -/
def get_yaw_reset_count (s : State) : UInt16 := Id.run do
  return AP_AHRS_ResetCounter_unsigned_short.count s.yaw_reset_tracker

/-- C++ `uint16_t AP_AHRS::get_position_NE_reset_count() const`, `AP_AHRS/AP_AHRS.h:366-368`. -/
def get_position_NE_reset_count (s : State) : UInt16 := Id.run do
  return AP_AHRS_ResetCounter_unsigned_short.count s.position_NE_reset_tracker

/-- C++ `uint16_t AP_AHRS::get_position_D_reset_count() const`, `AP_AHRS/AP_AHRS.h:371-373`. -/
def get_position_D_reset_count (s : State) : UInt16 := Id.run do
  return AP_AHRS_ResetCounter_unsigned_short.count s.position_D_reset_tracker

/-- C++ `bool AP_AHRS::healthy() const`, `AP_AHRS/AP_AHRS.cpp:1386-1398`. -/
def healthy (s : State) : Bool := Id.run do
  if !((match s.configured_estimates with | .ahrs'dcm_estimates => s.dcm_estimates | .ahrs'ekf3_estimates => s.ekf3_estimates | _ => s.sim_estimates) : AP_AHRS_Backend.Estimates.State).healthy then
    return false
  if s.configured_backend != s.active_backend then
    return false
  return true

/-- C++ `bool AP_AHRS::initialised() const`, `AP_AHRS/AP_AHRS.h:335-337`. -/
def initialised (s : State) : Bool := Id.run do
  return ((match s.configured_estimates with | .ahrs'dcm_estimates => s.dcm_estimates | .ahrs'ekf3_estimates => s.ekf3_estimates | _ => s.sim_estimates) : AP_AHRS_Backend.Estimates.State).initialised

/-- C++ `bool AP_AHRS::get_filter_status_for_configured_backend(nav_filter_status & status) const`, `AP_AHRS/AP_AHRS.h:347-350`. -/
def get_filter_status_for_configured_backend (s : State) (status : UInt32) : UInt32 × Bool := Id.run do
  let mut status := status
  status := ((match s.configured_estimates with | .ahrs'dcm_estimates => s.dcm_estimates | .ahrs'ekf3_estimates => s.ekf3_estimates | _ => s.sim_estimates) : AP_AHRS_Backend.Estimates.State).filter_status
  return (status, ((match s.configured_estimates with | .ahrs'dcm_estimates => s.dcm_estimates | .ahrs'ekf3_estimates => s.ekf3_estimates | _ => s.sim_estimates) : AP_AHRS_Backend.Estimates.State).filter_status_valid)

end AP_AHRS

namespace AP_AHRS

/-- C++ `bool AP_AHRS::configured_backend_has_status(Status status) const`, `AP_AHRS/AP_AHRS.cpp:353-359`. -/
def configured_backend_has_status (s : State) (status : NavFilterStatusBit) : Bool := Id.run do
  let mut filter_status : UInt32 := (0 : UInt32)
  let (t'1, t'2) := get_filter_status_for_configured_backend s filter_status
  filter_status := t'1
  if !t'2 then
    return false
  return (filter_status &&& Int32.toUInt32 (NavFilterStatusBit.toInt status)) != Int32.toUInt32 (0 : Int32)

/-- C++ `bool AP_AHRS::get_variances_for_configured_backend(float & velVar, float & posVar, float & hgtVar, Vector3f & magVar, float & tasVar) const`, `AP_AHRS/AP_AHRS.h:415-422`. -/
def get_variances_for_configured_backend (s : State) (velVar : Binary32) (posVar : Binary32) (hgtVar : Binary32) (magVar : Vector3f.State) (tasVar : Binary32) : Binary32 × Binary32 × Binary32 × Vector3f.State × Binary32 × Bool := Id.run do
  let mut velVar := velVar
  let mut posVar := posVar
  let mut hgtVar := hgtVar
  let mut magVar := magVar
  let mut tasVar := tasVar
  velVar := ((match s.configured_estimates with | .ahrs'dcm_estimates => s.dcm_estimates | .ahrs'ekf3_estimates => s.ekf3_estimates | _ => s.sim_estimates) : AP_AHRS_Backend.Estimates.State).velVar
  posVar := ((match s.configured_estimates with | .ahrs'dcm_estimates => s.dcm_estimates | .ahrs'ekf3_estimates => s.ekf3_estimates | _ => s.sim_estimates) : AP_AHRS_Backend.Estimates.State).posVar
  hgtVar := ((match s.configured_estimates with | .ahrs'dcm_estimates => s.dcm_estimates | .ahrs'ekf3_estimates => s.ekf3_estimates | _ => s.sim_estimates) : AP_AHRS_Backend.Estimates.State).hgtVar
  magVar := ((match s.configured_estimates with | .ahrs'dcm_estimates => s.dcm_estimates | .ahrs'ekf3_estimates => s.ekf3_estimates | _ => s.sim_estimates) : AP_AHRS_Backend.Estimates.State).magVar
  tasVar := ((match s.configured_estimates with | .ahrs'dcm_estimates => s.dcm_estimates | .ahrs'ekf3_estimates => s.ekf3_estimates | _ => s.sim_estimates) : AP_AHRS_Backend.Estimates.State).tasVar
  return (velVar, posVar, hgtVar, magVar, tasVar, ((match s.configured_estimates with | .ahrs'dcm_estimates => s.dcm_estimates | .ahrs'ekf3_estimates => s.ekf3_estimates | _ => s.sim_estimates) : AP_AHRS_Backend.Estimates.State).variances_valid)

/-- C++ `bool AP_AHRS::home_is_locked() const`, `AP_AHRS/AP_AHRS.h:601-603`. -/
def home_is_locked (s : State) : Bool := Id.run do
  return s._home_locked

end AP_AHRS

namespace AP_AHRS

/-- C++ `bool AP_AHRS::get_vert_pos_rate_D(float & velocity) const`, `AP_AHRS/AP_AHRS.cpp:990-993`. -/
def get_vert_pos_rate_D (s : State) (velocity : Binary32) : Binary32 × Bool := Id.run do
  let mut velocity := velocity
  let t'1 := s.active_estimates
  let mut t'8 : Bool := false
  match t'1 with
  | .ahrs'dcm_estimates =>  -- C++ `ahrs.dcm_estimates`
      let (t'2, t'3) := AP_AHRS_Backend.Estimates.get_vert_pos_rate_D s.dcm_estimates velocity
      velocity := t'2
      t'8 := t'3
  | .ahrs'ekf3_estimates =>  -- C++ `ahrs.ekf3_estimates`
      let (t'4, t'5) := AP_AHRS_Backend.Estimates.get_vert_pos_rate_D s.ekf3_estimates velocity
      velocity := t'4
      t'8 := t'5
  | .ahrs'sim_estimates =>  -- C++ `ahrs.sim_estimates`
      let (t'6, t'7) := AP_AHRS_Backend.Estimates.get_vert_pos_rate_D s.sim_estimates velocity
      velocity := t'6
      t'8 := t'7
  | _ => pure ()  -- (no other object: undefined in C++)
  return (velocity, t'8)

/-- C++ `bool AP_AHRS::get_velocity_D(float & velD, bool high_vibes) const`, `AP_AHRS/AP_AHRS.cpp:978-986`. -/
def get_velocity_D (s : State) (velD : Binary32) (high_vibes : Bool := false) : Binary32 × Bool := Id.run do
  let mut velD := velD
  let mut velNED : Vector3f.State := Vector3f.init_void
  let mut t'3 := !high_vibes
  if t'3 then
    let (t'1, t'2) := get_velocity_NED s velNED
    velNED := t'1
    t'3 := t'2
  if t'3 then
    velD := velNED.z
    return (velD, true)
  let (t'4, t'5) := get_vert_pos_rate_D s velD
  velD := t'4
  return (velD, t'5)

/-- C++ `float AP_AHRS::get_control_gain_scaler_Z() const`, `AP_AHRS/AP_AHRS.h:325`. -/
def get_control_gain_scaler_Z (s : State) : Binary32 := Id.run do
  return ((match s.active_estimates with | .ahrs'dcm_estimates => s.dcm_estimates | .ahrs'ekf3_estimates => s.ekf3_estimates | _ => s.sim_estimates) : AP_AHRS_Backend.Estimates.State).control_gain_scaler_Z

/-- C++ `float AP_AHRS::get_control_gain_scaler_XY() const`, `AP_AHRS/AP_AHRS.h:324`. -/
def get_control_gain_scaler_XY (s : State) : Binary32 := Id.run do
  return ((match s.active_estimates with | .ahrs'dcm_estimates => s.dcm_estimates | .ahrs'ekf3_estimates => s.ekf3_estimates | _ => s.sim_estimates) : AP_AHRS_Backend.Estimates.State).control_gain_scaler_XY

/-- C++ `float AP_AHRS::get_control_ground_speed_limit_ms() const`, `AP_AHRS/AP_AHRS.h:322`. -/
def get_control_ground_speed_limit_ms (s : State) : Binary32 := Id.run do
  return ((match s.active_estimates with | .ahrs'dcm_estimates => s.dcm_estimates | .ahrs'ekf3_estimates => s.ekf3_estimates | _ => s.sim_estimates) : AP_AHRS_Backend.Estimates.State).control_ground_speed_limit_ms

/-- C++ `float AP_AHRS::get_EAS2TAS() const`, `AP_AHRS/AP_AHRS.cpp:2125-2131`. -/
def get_EAS2TAS (s : State) : Binary32 := Id.run do
  if Estimator_lib.is_positive_float s.state.EAS2TAS then
    return s.state.EAS2TAS
  return (Binary32.ofBits 0x3f800000 /- 1.0 -/)

/-- C++ `float AP_AHRS::get_air_density_ratio() const`, `AP_AHRS/AP_AHRS.cpp:2134-2138`. -/
def get_air_density_ratio (s : State) : Binary32 := Id.run do
  let eas2tas : Binary32 := get_EAS2TAS s
  return (Binary32.ofBits 0x3f800000 /- 1.0 -/) / Estimator_lib.sq_float eas2tas

/-- C++ `Vector2f AP_AHRS::body_to_earth2D(const Vector2f & bf) const`, `AP_AHRS/AP_AHRS_Backend.cpp:244-248`. -/
def body_to_earth2D (s : State) (bf : Vector2f.State) : Vector2f.State := Id.run do
  return Vector2f.init_float2 (bf.x * s._cos_yaw - bf.y * s._sin_yaw) (bf.x * s._sin_yaw + bf.y * s._cos_yaw)

end AP_AHRS

namespace AP_AHRS

/-- C++ `bool AP_AHRS::reset_configured_backend()`, `AP_AHRS/AP_AHRS.cpp:1906-1921`. -/
def reset_configured_backend (s : State) (w : World) (o : Outputs) : World × Outputs × Bool := Id.run do
  let mut w := w
  let mut o := o
  match configured_ekf_type s with
  | .THREE =>
    let t'1 := w.EKF3  -- the object out of the World for the call (--swap-out)
    w := { w with EKF3 := default }
    let (t'2, t'3, t'4, t'5) := NavEKF3.InitialiseFilterBootstrap t'1 w o
    w := t'3
    w := { w with EKF3 := t'2 }
    o := t'4
    return (w, o, t'5)
  | _ =>
    pure ()
  return (w, o, false)

end AP_AHRS

namespace AP_AHRS

/-- C++ `bool AP_AHRS::use_compass()`, `AP_AHRS/AP_AHRS.cpp:843-857`. -/
def use_compass (s : State) (w : World) : State × World × Bool := Id.run do
  let mut s := s
  let mut w := w
  let t'1 := s.active_backend
  let mut t'4 : Bool := false
  match t'1 with
  | .ahrs'ekf3 =>  -- C++ `ahrs.ekf3`
      t'4 := AP_AHRS_NavEKF3.use_compass w
  | .ahrs'dcm =>  -- C++ `ahrs.dcm`
      w := { w with ahrs := s }  -- this object's state into the World: the call reaches it
      let (t'2, t'3) := AP_AHRS_DCM.use_compass s.dcm w
      s := { s with dcm := t'2 }
      t'4 := t'3
  | .ahrs'sim =>  -- C++ `ahrs.sim`
      pure ()  -- C++ `AP_AHRS_SIM::use_compass`: returns a constant
      t'4 := true
  | _ => pure ()  -- (no other object: undefined in C++)
  return (s, w, t'4)

/-- C++ `uint8_t AP_AHRS::get_primary_gyro_index() const`, `AP_AHRS/AP_AHRS.h:464`. -/
def get_primary_gyro_index (s : State) : UInt8 := Id.run do
  return s.state.primary_gyro

/-- C++ `Vector3f AP_AHRS::get_gyro_latest() const`, `AP_AHRS/AP_AHRS_Backend.cpp:31-35`. -/
def get_gyro_latest (s : State) (w : World) : Vector3f.State := Id.run do
  let primary_gyro : UInt8 := get_primary_gyro_index s
  let t'1 := primary_gyro
  return Vector3f.op_add w.ins._gyro[UInt8.toNat t'1]! (get_gyro_drift s)

/-- C++ `bool AP_AHRS::airspeed_vector_TAS(Vector3f & vec) const`, `AP_AHRS/AP_AHRS.cpp:2069-2073`. -/
def airspeed_vector_TAS (s : State) (vec : Vector3f.State) : Vector3f.State × Bool := Id.run do
  let mut vec := vec
  vec := s.state.airspeed_TAS_vec
  return (vec, s.state.airspeed_TAS_vec_ok)

end AP_AHRS

namespace AP_AHRS

/-- C++ `bool AP_AHRS::get_pos_vel_uncertainty(float & pos_horiz_m, float & pos_vert_m, float & vel_m_s) const`, `AP_AHRS/AP_AHRS.cpp:1838-1848`. -/
def get_pos_vel_uncertainty (s : State) (w : World) (pos_horiz_m : Binary32) (pos_vert_m : Binary32) (vel_m_s : Binary32) : Binary32 × Binary32 × Binary32 × Bool := Id.run do
  let mut pos_horiz_m := pos_horiz_m
  let mut pos_vert_m := pos_vert_m
  let mut vel_m_s := vel_m_s
  match active_EKF_type s with
  | .THREE =>
    let (t'1, t'2, t'3, t'4) := NavEKF3.getPosVelUncertainty w.EKF3 w pos_horiz_m pos_vert_m vel_m_s
    pos_horiz_m := t'1
    pos_vert_m := t'2
    vel_m_s := t'3
    return (pos_horiz_m, pos_vert_m, vel_m_s, t'4)
  | _ =>
    return (pos_horiz_m, pos_vert_m, vel_m_s, false)

/-- C++ `bool AP_AHRS::get_relative_position_NED_origin_float(Vector3f & vec) const`, `AP_AHRS/AP_AHRS.cpp:995-1003`. -/
def get_relative_position_NED_origin_float (s : State) (vec : Vector3f.State) : Vector3f.State × Bool := Id.run do
  let mut vec := vec
  let mut tmp_posNED : Vector3p.State := Vector3p.init_void
  let (t'1, t'2) := get_relative_position_NED_origin s tmp_posNED
  tmp_posNED := t'1
  if !t'2 then
    return (vec, false)
  vec := Vector3p.tofloat tmp_posNED
  return (vec, true)

/-- C++ `const AP_AHRS_Backend::Estimates * AP_AHRS::get_secondary_estimates() const`, `AP_AHRS/AP_AHRS.h:202-204`. -/
def get_secondary_estimates (s : State) : WPtr := Id.run do
  return s.secondary_estimates

/-- C++ `bool AP_AHRS::get_wind(Vector3f & wind) const`, `AP_AHRS/AP_AHRS.cpp:2036-2040`. -/
def get_wind (s : State) (wind : Vector3f.State) : Vector3f.State × Bool := Id.run do
  let mut wind := wind
  wind := ((match s.active_estimates with | .ahrs'dcm_estimates => s.dcm_estimates | .ahrs'ekf3_estimates => s.ekf3_estimates | _ => s.sim_estimates) : AP_AHRS_Backend.Estimates.State).wind
  return (wind, ((match s.active_estimates with | .ahrs'dcm_estimates => s.dcm_estimates | .ahrs'ekf3_estimates => s.ekf3_estimates | _ => s.sim_estimates) : AP_AHRS_Backend.Estimates.State).wind_valid)

/-- C++ `float AP_AHRS::get_yaw_deg() const`, `AP_AHRS/AP_AHRS.h:635`. -/
def get_yaw_deg (s : State) : Binary32 := Id.run do
  return s.rpy_deg[2]!

/-- C++ `float AP_AHRS::groundspeed() const`, `AP_AHRS/AP_AHRS.h:210`. -/
def groundspeed (s : State) : Binary32 := Id.run do
  return s.state.ground_speed

end AP_AHRS

namespace AP_AHRS

/-- C++ `bool AP_AHRS::attitudes_consistent(char * failure_msg, const uint8_t failure_msg_len) const`, `AP_AHRS/AP_AHRS.cpp:1531-1626`. -/
def attitudes_consistent (s : State) (w : World) (failure_msg : CText) (failure_msg_len : UInt8) : CText × Bool := Id.run do
  let mut failure_msg := failure_msg
  let mut primary_quat : Quaternion.State := Quaternion.init_void
  primary_quat := get_quat_body_to_ned s primary_quat
  let check_yaw : Bool := Compass.use_for_yaw_void w.compass
  let mut total_ekf_cores : UInt8 := Int8.toUInt8 (Int32.toInt8 (0 : Int32))
  if configured_ekf_type s == AP_AHRS.EKFType.THREE || active_EKF_type s == AP_AHRS.EKFType.THREE then
    let mut i : UInt8 := Int8.toUInt8 (Int32.toInt8 (0 : Int32))
    for _ in [0:2^64] do  -- C loop without a constant trip count (--general-loops)
      if !(decide (UInt32.toInt32 (UInt8.toUInt32 i) < UInt32.toInt32 (UInt8.toUInt32 (NavEKF3.activeCores w.EKF3)))) then break
      let mut ekf3_quat : Quaternion.State := Quaternion.init_void
      ekf3_quat := NavEKF3.getQuaternionBodyToNED w.EKF3 w (UInt8.toInt8 i) ekf3_quat
      let rp_diff_rad : Binary32 := Quaternion.roll_pitch_difference primary_quat ekf3_quat
      if rp_diff_rad > Estimator_lib.radians_int32_t (10 : Int32) then
        failure_msg := set_failure_inconsistent_message "EKF3" "Roll/Pitch" rp_diff_rad failure_msg failure_msg_len
        return (failure_msg, false)
      let mut angle_diff : Vector3f.State := Vector3f.init_void
      angle_diff := Quaternion.to_axis_angle (Quaternion.angular_difference primary_quat ekf3_quat) angle_diff
      let yaw_diff : Binary32 := Binary32.abs angle_diff.z
      if check_yaw && (decide (yaw_diff > Estimator_lib.radians_int32_t (20 : Int32))) then
        failure_msg := set_failure_inconsistent_message "EKF3" "Yaw" yaw_diff failure_msg failure_msg_len
        return (failure_msg, false)
      i := i + (1 : UInt8)
    total_ekf_cores := Int8.toUInt8 (Int32.toInt8 (UInt32.toInt32 (UInt8.toUInt32 total_ekf_cores) + UInt32.toInt32 (UInt8.toUInt32 (NavEKF3.activeCores w.EKF3))))
  if !(always_use_EKF s) || (UInt32.toInt32 (UInt8.toUInt32 total_ekf_cores) == (1 : Int32)) then
    let mut dcm_quat : Quaternion.State := Quaternion.init_void
    dcm_quat := Quaternion.from_rotation_matrix dcm_quat (get_DCM_rotation_body_to_ned s)
    let rp_diff_rad'2 : Binary32 := Quaternion.roll_pitch_difference primary_quat dcm_quat
    if rp_diff_rad'2 > Estimator_lib.radians_int32_t (10 : Int32) then
      failure_msg := set_failure_inconsistent_message "DCM" "Roll/Pitch" rp_diff_rad'2 failure_msg failure_msg_len
      return (failure_msg, false)
    let mut using_noncompass_for_yaw : Bool := false
    using_noncompass_for_yaw := (configured_ekf_type s == AP_AHRS.EKFType.THREE) && NavEKF3.using_noncompass_for_yaw w.EKF3 w
    if !(always_use_EKF s) && !using_noncompass_for_yaw then
      let mut angle_diff'2 : Vector3f.State := Vector3f.init_void
      angle_diff'2 := Quaternion.to_axis_angle (Quaternion.angular_difference primary_quat dcm_quat) angle_diff'2
      let yaw_diff'2 : Binary32 := Binary32.abs angle_diff'2.z
      if check_yaw && (decide (yaw_diff'2 > Estimator_lib.radians_int32_t (20 : Int32))) then
        failure_msg := set_failure_inconsistent_message "DCM" "Yaw" yaw_diff'2 failure_msg failure_msg_len
        return (failure_msg, false)
  return (failure_msg, true)

end AP_AHRS

namespace AP_AHRS_NavEKF3

/-- C++ `bool AP_AHRS_NavEKF3::pre_arm_check(bool requires_position, char * failure_msg, uint8_t failure_msg_len) const`, `AP_AHRS/AP_AHRS_NavEKF3.cpp:275-282`. -/
def pre_arm_check (s : State) (w : World) (requires_position : Bool) (failure_msg : CText) (failure_msg_len : UInt8) : World × CText × Bool := Id.run do
  let mut w := w
  let mut failure_msg := failure_msg
  if !s.started then
    failure_msg := (CText.fmt (UInt8.toUInt64 failure_msg_len) "EKF3 not started" #[])
    return (w, failure_msg, false)
  let (t'1, t'2, t'3) := NavEKF3.pre_arm_check w.EKF3 w requires_position failure_msg failure_msg_len
  w := t'1
  failure_msg := t'2
  return (w, failure_msg, t'3)

end AP_AHRS_NavEKF3

namespace AP_AHRS

/-- C++ `bool AP_AHRS::pre_arm_check(bool requires_position, char * failure_msg, uint8_t failure_msg_len) const`, `AP_AHRS/AP_AHRS.cpp:1402-1434`. -/
def pre_arm_check (s : State) (w : World) (requires_position : Bool) (failure_msg : CText) (failure_msg_len : UInt8) : World × CText × Bool := Id.run do
  let mut w := w
  let mut failure_msg := failure_msg
  let mut ret : Bool := true
  if !(healthy s) then
    failure_msg := (CText.fmt (UInt8.toUInt64 failure_msg_len) "Not healthy" #[])
    ret := false
  let (t'1, t'2) := attitudes_consistent s w failure_msg failure_msg_len
  failure_msg := t'1
  if !t'2 then
    return (w, failure_msg, false)
  if Int8.toInt32 (AP_Enum_AP_AHRS_EKFType.op_to_signed_char s._ekf_type) != Int8.toInt32 (UInt8.toInt8 (AP_AHRS.EKFType.toInt (configured_ekf_type s))) || (configured_ekf_type s != active_EKF_type s && Compass.use_for_yaw_void w.compass) then
    failure_msg := (CText.fmt (UInt8.toUInt64 failure_msg_len) "not using configured AHRS type" #[])
    return (w, failure_msg, false)
  let t'3 := s.configured_backend
  let mut t'7 : Bool := false
  match t'3 with
  | .ahrs'ekf3 =>  -- C++ `ahrs.ekf3`
      let (t'4, t'5, t'6) := AP_AHRS_NavEKF3.pre_arm_check s.ekf3 w requires_position failure_msg failure_msg_len
      w := t'4
      failure_msg := t'5
      t'7 := t'6
  | .ahrs'dcm =>  -- C++ `ahrs.dcm`
      t'7 := AP_AHRS_DCM.pre_arm_check requires_position failure_msg_len
  | .ahrs'sim =>  -- C++ `ahrs.sim`
      pure ()  -- C++ `AP_AHRS_SIM::pre_arm_check`: returns a constant
      t'7 := true
  | _ => pure ()  -- (no other object: undefined in C++)
  return (w, failure_msg, (t'7 && ret))

/-- C++ `bool AP_AHRS::active_backend_configured_to_use_gps() const`, `AP_AHRS/AP_AHRS.h:499`. -/
def active_backend_configured_to_use_gps (s : State) : Bool := Id.run do
  return ((match s.active_estimates with | .ahrs'dcm_estimates => s.dcm_estimates | .ahrs'ekf3_estimates => s.ekf3_estimates | _ => s.sim_estimates) : AP_AHRS_Backend.Estimates.State).configured_to_use_gps

/-- C++ `Vector2p AP_AHRS::body_to_earth2D_p(const Vector2p & bf) const`, `AP_AHRS/AP_AHRS_Backend.cpp:251-255`. -/
def body_to_earth2D_p (s : State) (bf : Vector2p.State) : Vector2p.State := Id.run do
  return Vector2p.init_double2 (bf.x * Binary32.toBinary64 s._cos_yaw - bf.y * Binary32.toBinary64 s._sin_yaw) (bf.x * Binary32.toBinary64 s._sin_yaw + bf.y * Binary32.toBinary64 s._cos_yaw)

end AP_AHRS

namespace AP_AHRS_View

/-- C++ `float AP_AHRS_View::cos_yaw() const`, `AP_AHRS/AP_AHRS_View.h:74-76`. -/
def cos_yaw (s : State) : Binary32 := Id.run do
  return s.trig.cos_yaw

/-- C++ `float AP_AHRS_View::sin_yaw() const`, `AP_AHRS/AP_AHRS_View.h:83-85`. -/
def sin_yaw (s : State) : Binary32 := Id.run do
  return s.trig.sin_yaw

/-- C++ `float AP_AHRS_View::cos_pitch() const`, `AP_AHRS/AP_AHRS_View.h:71-73`. -/
def cos_pitch (s : State) : Binary32 := Id.run do
  return s.trig.cos_pitch

/-- C++ `float AP_AHRS_View::cos_roll() const`, `AP_AHRS/AP_AHRS_View.h:68-70`. -/
def cos_roll (s : State) : Binary32 := Id.run do
  return s.trig.cos_roll

/-- C++ `uint16_t AP_AHRS_View::get_position_D_reset_count()`, `AP_AHRS/AP_AHRS_View.h:156-158`. -/
def get_position_D_reset_count (w : World) : UInt16 := Id.run do
  return AP_AHRS.get_position_D_reset_count w.ahrs

/-- C++ `uint16_t AP_AHRS_View::get_position_NE_reset_count()`, `AP_AHRS/AP_AHRS_View.h:152-154`. -/
def get_position_NE_reset_count (w : World) : UInt16 := Id.run do
  return AP_AHRS.get_position_NE_reset_count w.ahrs

/-- C++ `void AP_AHRS_View::get_quat_body_to_ned(Quaternion & quat) const`, `AP_AHRS/AP_AHRS_View.h:55-57`. -/
def get_quat_body_to_ned (s : State) (quat : Quaternion.State) : Quaternion.State := Id.run do
  let mut quat := quat
  quat := Quaternion.from_rotation_matrix quat s.rot_body_to_ned
  return quat

/-- C++ `const Vector3f & AP_AHRS_View::get_accel_ef() const`, `AP_AHRS/AP_AHRS_View.h:148-150`. -/
def get_accel_ef (w : World) : Vector3f.State := Id.run do
  return AP_AHRS.get_accel_ef w.ahrs

/-- C++ `Vector3f AP_AHRS_View::get_gyro_latest() const`, `AP_AHRS/AP_AHRS_View.cpp:86-88`. -/
def get_gyro_latest (s : State) (w : World) : Vector3f.State := Id.run do
  return Matrix3f.op_mul_Vector3f s.rot_view (AP_AHRS.get_gyro_latest w.ahrs w)

end AP_AHRS_View

end Estimator_lib
