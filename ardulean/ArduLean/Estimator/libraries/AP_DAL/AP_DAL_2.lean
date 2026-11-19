import ArduLean.Runtime.CFloat
import ArduLean.Estimator.libraries.AP_Math.AP_Math
import ArduLean.Estimator.World
import ArduLean.Estimator.libraries.AP_Common.AP_Common
import ArduLean.Estimator.libraries.AP_GPS.AP_GPS
import ArduLean.Estimator.libraries.AP_InertialSensor.AP_InertialSensor
import ArduLean.Estimator.libraries.AP_AHRS.AP_AHRS
import ArduLean.Estimator.libraries.AP_Baro.AP_Baro
import ArduLean.Estimator.libraries.AP_DAL.AP_DAL
import ArduLean.Estimator.World_2
import ArduLean.Estimator.libraries.AP_Compass.AP_Compass_2
import ArduLean.Estimator.World_3
import ArduLean.Estimator.libraries.AP_Compass.AP_Compass_3
import ArduLean.Estimator.libraries.AP_GPS.AP_GPS_2
import ArduLean.Estimator.libraries.AP_InertialSensor.AP_InertialSensor_2
import ArduLean.Estimator.libraries.AP_AHRS.AP_AHRS_2
import ArduLean.Estimator.libraries.AP_Baro.AP_Baro_3

/-!
ArduPilot `libraries/AP_DAL`, part 2 of 2. Sources: `libraries/AP_DAL/AP_DAL.cpp`, `libraries/AP_DAL/AP_DAL.h`, `libraries/AP_DAL/AP_DAL_GPS.cpp`, `libraries/AP_DAL/AP_DAL_InertialSensor.cpp`, `libraries/AP_DAL/AP_DAL_Baro.cpp`, `libraries/AP_DAL/AP_DAL_Compass.cpp`.

Items of `lean/Estimator_lib.lean` (the estimator translation), unchanged; placed by `tools/split_modules.py` (`ArduLean/Estimator/INDEX.md`).
-/

open FloatLib.Floats (Binary32 Binary64)

set_option maxRecDepth 200000
-- AP_DAL's `const log_RISH old_RISH = _RISH;` read only by WRITE_REPLAY_BLOCK_IFCHANGED, which is `(void)old`
-- without logging (HAL_LOGGING_ENABLED 0): an unused binding, as in the C++
set_option linter.unusedVariables false

namespace Estimator_lib

namespace AP_DAL_Baro

/-- C++ `void AP_DAL_Baro::update_calibration()`, `AP_DAL/AP_DAL_Baro.cpp:33-36`. -/
def update_calibration (w : World) (o : Outputs) : World × Outputs := Id.run do
  let mut w := w
  let mut o := o
  let t'1 := w.barometer  -- the object out of the World for the call (--swap-out)
  w := { w with barometer := default }
  let (t'2, t'3) := AP_Baro.update_calibration t'1 w o
  w := { w with barometer := t'2 }
  o := t'3
  return (w, o)

end AP_DAL_Baro

namespace AP_DAL_Baro

/-- C++ `void AP_DAL_Baro::start_frame()`, `AP_DAL/AP_DAL_Baro.cpp:13-30`. -/
def start_frame (s : State) (w : World) : State := Id.run do
  let mut s := s
  let old_RBRH : log_RBRH := s._RBRH
  s := { s with _RBRH.primary := AP_Baro.get_primary w.barometer }
  s := { s with _RBRH.num_instances := AP_Baro.num_instances w.barometer }
  for _ in [0:1] do
    pure ()
  let t'1 : UInt8 := Int8.toUInt8 (Int32.toInt8 (0 : Int32))
  let t'2 : Int32 := UInt32.toInt32 (UInt8.toUInt32 s._RBRH.num_instances)
  for i' in [0:(t'2.toInt - (Int.ofNat t'1.toNat)).toNat] do  -- C++ loop bounded by a runtime value (--runtime-loops)
    let i : UInt8 := t'1 + Nat.toUInt8 i'
    let old : log_RBRI := s._RBRI[UInt8.toNat i]!
    s := { s with _RBRI := s._RBRI.set! (UInt8.toNat i) ({ s._RBRI[UInt8.toNat i]! with last_update_ms := AP_Baro.get_last_update_uint8_t w.barometer i }) }
    s := { s with _RBRI := s._RBRI.set! (UInt8.toNat i) ({ s._RBRI[UInt8.toNat i]! with healthy := AP_Baro.healthy_uint8_t w.barometer i }) }
    s := { s with _RBRI := s._RBRI.set! (UInt8.toNat i) ({ s._RBRI[UInt8.toNat i]! with altitude := AP_Baro.get_altitude_uint8_t w.barometer i }) }
    for _ in [0:1] do
      pure ()
  return s

end AP_DAL_Baro

namespace AP_DAL_Compass

/-- C++ `void AP_DAL_Compass::start_frame()`, `AP_DAL/AP_DAL_Compass.cpp:15-43`. -/
def start_frame (s : State) (w : World) : State := Id.run do
  let mut s := s
  let old : log_RMGH := s._RMGH
  s := { s with _RMGH.available := Compass.available w.compass }
  s := { s with _RMGH.count := Compass.get_count w.compass }
  s := { s with _RMGH.auto_declination_enabled := Compass.auto_declination_enabled w.compass }
  s := { s with _RMGH.declination := Compass.get_declination w.compass }
  s := { s with _RMGH.num_enabled := Compass.get_num_enabled w.compass }
  s := { s with _RMGH.consistent := Compass.consistent w.compass }
  s := { s with _RMGH.first_usable := Compass.get_first_usable w.compass }
  s := { s with _RMGH.learn_offsets_enabled := Compass.learn_offsets_enabled w.compass }
  for _ in [0:1] do
    pure ()
  let t'1 : UInt8 := Int8.toUInt8 (Int32.toInt8 (0 : Int32))
  let t'2 : Int32 := UInt32.toInt32 (UInt8.toUInt32 s._RMGH.count)
  for i' in [0:(t'2.toInt - (Int.ofNat t'1.toNat)).toNat] do  -- C++ loop bounded by a runtime value (--runtime-loops)
    let i : UInt8 := t'1 + Nat.toUInt8 i'
    let old_RMGI : log_RMGI := s._RMGI[UInt8.toNat i]!
    s := { s with _RMGI := s._RMGI.set! (UInt8.toNat i) ({ s._RMGI[UInt8.toNat i]! with use_for_yaw := Compass.use_for_yaw_uint8_t w.compass i }) }
    s := { s with _RMGI := s._RMGI.set! (UInt8.toNat i) ({ s._RMGI[UInt8.toNat i]! with healthy := Compass.healthy_uint8_t w.compass i }) }
    s := { s with _RMGI := s._RMGI.set! (UInt8.toNat i) ({ s._RMGI[UInt8.toNat i]! with offsets := Compass.get_offsets_uint8_t w.compass i }) }
    s := { s with _RMGI := s._RMGI.set! (UInt8.toNat i) ({ s._RMGI[UInt8.toNat i]! with have_scale_factor := Compass.have_scale_factor w.compass i }) }
    s := { s with _RMGI := s._RMGI.set! (UInt8.toNat i) ({ s._RMGI[UInt8.toNat i]! with last_update_usec := Compass.last_update_usec_uint8_t w.compass i }) }
    s := { s with _RMGI := s._RMGI.set! (UInt8.toNat i) ({ s._RMGI[UInt8.toNat i]! with field := Compass.get_field_uint8_t w.compass i }) }
    for _ in [0:1] do
      pure ()
  return s

end AP_DAL_Compass

namespace AP_DAL_GPS

/-- C++ `void AP_DAL_GPS::start_frame()`, `AP_DAL/AP_DAL_GPS.cpp:19-79`. -/
def start_frame (s : State) (w : World) : State := Id.run do
  let mut s := s
  let old_RGPH : log_RGPH := s._RGPH
  s := { s with _RGPH.primary_sensor := AP_GPS.primary_sensor w.gps }
  s := { s with _RGPH.num_sensors := AP_GPS.num_sensors w.gps }
  for _ in [0:1] do
    pure ()
  for i' in [0:3] do
    let i : UInt8 := Nat.toUInt8 i'
    let old_RGPI : log_RGPI := s._RGPI[UInt8.toNat i]!
    let old_RGPJ : log_RGPJ := s._RGPJ[UInt8.toNat i]!
    s := { s with _RGPI := s._RGPI.set! (UInt8.toNat i) ({ s._RGPI[UInt8.toNat i]! with status := AP_GPS_FixType.toInt (AP_GPS.status_uint8_t w.gps i) }) }
    s := { s with _RGPI := s._RGPI.set! (UInt8.toNat i) ({ s._RGPI[UInt8.toNat i]! with antenna_offset := AP_GPS.get_antenna_offset w.gps i }) }
    let t'1 := i
    s := { s with _RGPJ := s._RGPJ.set! (UInt8.toNat i) ({ s._RGPJ[UInt8.toNat i]! with last_message_time_ms := AP_GPS.last_message_time_ms_uint8_t w.gps i }) }
    s := { s with _RGPJ := s._RGPJ.set! (UInt8.toNat i) ({ s._RGPJ[UInt8.toNat i]! with lat := w.gps.state[UInt8.toNat t'1]!.location.lat }) }
    s := { s with _RGPJ := s._RGPJ.set! (UInt8.toNat i) ({ s._RGPJ[UInt8.toNat i]! with lng := w.gps.state[UInt8.toNat t'1]!.location.lng }) }
    s := { s with _RGPJ := s._RGPJ.set! (UInt8.toNat i) ({ s._RGPJ[UInt8.toNat i]! with alt := w.gps.state[UInt8.toNat t'1]!.location.alt }) }
    s := { s with _RGPI := s._RGPI.set! (UInt8.toNat i) ({ s._RGPI[UInt8.toNat i]! with have_vertical_velocity := (if AP_GPS.have_vertical_velocity_uint8_t w.gps i then (1 : UInt8) else (0 : UInt8)) &&& (1 : UInt8) }) }
    let (t'2, t'3) := AP_GPS.horizontal_accuracy_uint8_t_float w.gps i s._RGPJ[UInt8.toNat i]!.hacc
    s := { s with _RGPJ := s._RGPJ.set! (UInt8.toNat i) ({ s._RGPJ[UInt8.toNat i]! with hacc := t'2 }) }
    s := { s with _RGPI := s._RGPI.set! (UInt8.toNat i) ({ s._RGPI[UInt8.toNat i]! with horizontal_accuracy_returncode := (if t'3 then (1 : UInt8) else (0 : UInt8)) &&& (1 : UInt8) }) }
    let (t'4, t'5) := AP_GPS.vertical_accuracy_uint8_t_float w.gps i s._RGPJ[UInt8.toNat i]!.vacc
    s := { s with _RGPJ := s._RGPJ.set! (UInt8.toNat i) ({ s._RGPJ[UInt8.toNat i]! with vacc := t'4 }) }
    s := { s with _RGPI := s._RGPI.set! (UInt8.toNat i) ({ s._RGPI[UInt8.toNat i]! with vertical_accuracy_returncode := (if t'5 then (1 : UInt8) else (0 : UInt8)) &&& (1 : UInt8) }) }
    s := { s with _RGPJ := s._RGPJ.set! (UInt8.toNat i) ({ s._RGPJ[UInt8.toNat i]! with hdop := AP_GPS.get_hdop_uint8_t w.gps i }) }
    s := { s with _RGPI := s._RGPI.set! (UInt8.toNat i) ({ s._RGPI[UInt8.toNat i]! with num_sats := AP_GPS.num_sats_uint8_t w.gps i }) }
    let (t'6, t'7) := AP_GPS.get_lag_uint8_t_float w.gps w i s._RGPI[UInt8.toNat i]!.lag_sec
    s := { s with _RGPI := s._RGPI.set! (UInt8.toNat i) ({ s._RGPI[UInt8.toNat i]! with lag_sec := t'6 }) }
    s := { s with _RGPI := s._RGPI.set! (UInt8.toNat i) ({ s._RGPI[UInt8.toNat i]! with get_lag_returncode := (if t'7 then (1 : UInt8) else (0 : UInt8)) &&& (1 : UInt8) }) }
    s := { s with _RGPJ := s._RGPJ.set! (UInt8.toNat i) ({ s._RGPJ[UInt8.toNat i]! with velocity := AP_GPS.velocity_uint8_t w.gps i }) }
    let (t'8, t'9) := AP_GPS.speed_accuracy_uint8_t_float w.gps i s._RGPJ[UInt8.toNat i]!.sacc
    s := { s with _RGPJ := s._RGPJ.set! (UInt8.toNat i) ({ s._RGPJ[UInt8.toNat i]! with sacc := t'8 }) }
    s := { s with _RGPI := s._RGPI.set! (UInt8.toNat i) ({ s._RGPI[UInt8.toNat i]! with speed_accuracy_returncode := (if t'9 then (1 : UInt8) else (0 : UInt8)) &&& (1 : UInt8) }) }
    let (t'10, t'11, t'12, t'13) := AP_GPS.gps_yaw_deg_uint8_t_float2_uint32_t w.gps w i s._RGPJ[UInt8.toNat i]!.yaw_deg s._RGPJ[UInt8.toNat i]!.yaw_accuracy_deg s._RGPJ[UInt8.toNat i]!.yaw_deg_time_ms
    s := { s with _RGPJ := s._RGPJ.set! (UInt8.toNat i) ({ s._RGPJ[UInt8.toNat i]! with yaw_deg := t'10 }) }
    s := { s with _RGPJ := s._RGPJ.set! (UInt8.toNat i) ({ s._RGPJ[UInt8.toNat i]! with yaw_accuracy_deg := t'11 }) }
    s := { s with _RGPJ := s._RGPJ.set! (UInt8.toNat i) ({ s._RGPJ[UInt8.toNat i]! with yaw_deg_time_ms := t'12 }) }
    s := { s with _RGPI := s._RGPI.set! (UInt8.toNat i) ({ s._RGPI[UInt8.toNat i]! with gps_yaw_deg_returncode := (if t'13 then (1 : UInt8) else (0 : UInt8)) &&& (1 : UInt8) }) }
    for _ in [0:1] do
      pure ()
    for _ in [0:1] do
      pure ()
    s := { s with tmp_location := s.tmp_location.set! (UInt8.toNat i) (Location.init_int32_t3_AltFrame s._RGPJ[UInt8.toNat i]!.lat s._RGPJ[UInt8.toNat i]!.lng s._RGPJ[UInt8.toNat i]!.alt Location.AltFrame.ABSOLUTE) }
  return s

end AP_DAL_GPS

namespace AP_DAL_InertialSensor

/-- C++ `void AP_DAL_InertialSensor::start_frame()`, `AP_DAL/AP_DAL_InertialSensor.cpp:20-65`. -/
def start_frame (s : State) (w : World) : State := Id.run do
  let mut s := s
  let old_RISH : log_RISH := s._RISH
  s := { s with _RISH.loop_rate_hz := AP_InertialSensor.get_loop_rate_hz w.ins }
  s := { s with _RISH.first_usable_gyro := AP_InertialSensor.get_first_usable_gyro w.ins }
  s := { s with _RISH.loop_delta_t := AP_InertialSensor.get_loop_delta_t w.ins }
  s := { s with _RISH.first_usable_accel := AP_InertialSensor.get_first_usable_accel w.ins }
  s := { s with _RISH.accel_count := AP_InertialSensor.get_accel_count w.ins }
  s := { s with _RISH.gyro_count := AP_InertialSensor.get_gyro_count w.ins }
  for _ in [0:1] do
    pure ()
  for i' in [0:3] do
    let i : UInt8 := Nat.toUInt8 i'
    let old_RISI : log_RISI := s._RISI[UInt8.toNat i]!
    s := { s with _RISI := s._RISI.set! (UInt8.toNat i) ({ s._RISI[UInt8.toNat i]! with use_accel := (if AP_InertialSensor.use_accel w.ins i then (1 : UInt8) else (0 : UInt8)) &&& (1 : UInt8) }) }
    if s._RISI[UInt8.toNat i]!.use_accel != (0 : UInt8) then
      let (t'1, t'2, t'3) := AP_InertialSensor.get_delta_velocity_uint8_t_Vector3f_float w.ins i s._RISI[UInt8.toNat i]!.delta_velocity s._RISI[UInt8.toNat i]!.delta_velocity_dt
      s := { s with _RISI := s._RISI.set! (UInt8.toNat i) ({ s._RISI[UInt8.toNat i]! with delta_velocity := t'1 }) }
      s := { s with _RISI := s._RISI.set! (UInt8.toNat i) ({ s._RISI[UInt8.toNat i]! with delta_velocity_dt := t'2 }) }
      s := { s with _RISI := s._RISI.set! (UInt8.toNat i) ({ s._RISI[UInt8.toNat i]! with get_delta_velocity_ret := (if t'3 then (1 : UInt8) else (0 : UInt8)) &&& (1 : UInt8) }) }
    s := { s with _RISI := s._RISI.set! (UInt8.toNat i) ({ s._RISI[UInt8.toNat i]! with use_gyro := (if AP_InertialSensor.use_gyro w.ins i then (1 : UInt8) else (0 : UInt8)) &&& (1 : UInt8) }) }
    if s._RISI[UInt8.toNat i]!.use_gyro != (0 : UInt8) then
      let (t'4, t'5, t'6) := AP_InertialSensor.get_delta_angle_uint8_t_Vector3f_float w.ins i s._RISI[UInt8.toNat i]!.delta_angle s._RISI[UInt8.toNat i]!.delta_angle_dt
      s := { s with _RISI := s._RISI.set! (UInt8.toNat i) ({ s._RISI[UInt8.toNat i]! with delta_angle := t'4 }) }
      s := { s with _RISI := s._RISI.set! (UInt8.toNat i) ({ s._RISI[UInt8.toNat i]! with delta_angle_dt := t'5 }) }
      s := { s with _RISI := s._RISI.set! (UInt8.toNat i) ({ s._RISI[UInt8.toNat i]! with get_delta_angle_ret := (if t'6 then (1 : UInt8) else (0 : UInt8)) &&& (1 : UInt8) }) }
    s := update_filtered s i
    for _ in [0:1] do
      pure ()
    let old_RISJ : log_RISJ := s._RISJ[UInt8.toNat i]!
    s := { s with _RISJ := s._RISJ.set! (UInt8.toNat i) ({ s._RISJ[UInt8.toNat i]! with gyro_bias_limit := AP_InertialSensor.get_gyro_bias_limit_rads w.ins w i }) }
    s := { s with _RISJ := s._RISJ.set! (UInt8.toNat i) ({ s._RISJ[UInt8.toNat i]! with gyro_bias_init_dps := AP_InertialSensor.get_gyro_bias_init_dps w.ins w i }) }
    for _ in [0:1] do
      pure ()
    s := { s with pos := s.pos.set! (UInt8.toNat i) (AP_InertialSensor.get_imu_pos_offset_uint8_t w.ins i) }
  return s

end AP_DAL_InertialSensor

namespace AP_DAL

/-- C++ `void AP_DAL::start_frame(FrameType frametype)`, `AP_DAL/AP_DAL.cpp:25-120`. -/
def start_frame (s : State) (w : World) (inp : Inputs) (frametype : AP_DAL.FrameType) : State × World := Id.run do
  let mut s := s
  let mut w := w
  if !s.init_done then
    s := init_sensors s
  let imu_us : UInt32 := AP_InertialSensor.get_last_update_usec w.ins
  if s._last_imu_time_us == imu_us then
    s := { s with _RFRF.frame_types := Int8.toUInt8 (Int32.toInt8 (UInt32.toInt32 (UInt8.toUInt32 s._RFRF.frame_types) ||| UInt32.toInt32 (UInt8.toUInt32 (AP_DAL.FrameType.toInt frametype)))) }
    return (s, w)
  s := { s with _last_imu_time_us := imu_us }
  s := end_frame s
  s := { s with _RFRF.frame_types := AP_DAL.FrameType.toInt frametype }
  s := { s with _RFRH.time_flying_ms := inp.get_time_flying_ms }
  s := { s with _RFRH.time_us := Estimator_lib.micros64 w }
  for _ in [0:1] do
    pure ()
  let old : log_RFRN := s._RFRN
  s := { s with _RFRN.armed := (if inp.get_soft_armed then (1 : UInt8) else (0 : UInt8)) &&& (1 : UInt8) }
  s := { s with _home := AP_AHRS.get_home w.ahrs }
  s := { s with _RFRN.lat := s._home.lat }
  s := { s with _RFRN.lng := s._home.lng }
  s := { s with _RFRN.alt := s._home.alt }
  s := { s with _RFRN.EAS2TAS := AP_Baro.get_EAS2TAS w.barometer }
  s := { s with _RFRN.vehicle_class := AP_AHRS.VehicleClass.toInt (AP_AHRS.get_vehicle_class w.ahrs) }
  s := { s with _RFRN.fly_forward := (if AP_AHRS.get_fly_forward w.ahrs then (1 : UInt8) else (0 : UInt8)) &&& (1 : UInt8) }
  s := { s with _RFRN.takeoff_expected := (if AP_AHRS.get_takeoff_expected w.ahrs then (1 : UInt8) else (0 : UInt8)) &&& (1 : UInt8) }
  s := { s with _RFRN.touchdown_expected := (if AP_AHRS.get_touchdown_expected w.ahrs then (1 : UInt8) else (0 : UInt8)) &&& (1 : UInt8) }
  s := { s with _RFRN.available_memory := inp.available_memory }
  s := { s with _RFRN.ahrs_trim := AP_AHRS.get_trim w.ahrs }
  s := { s with _RFRN.wheelencoder_enabled := (if inp.nonnull && (decide (UInt32.toInt32 (UInt8.toUInt32 inp.num_sensors) > (0 : Int32))) then (1 : UInt8) else (0 : UInt8)) &&& (1 : UInt8) }
  s := { s with _RFRN.ekf_type := Int8.toUInt8 (UInt8.toInt8 (AP_AHRS.EKFType.toInt (AP_AHRS.configured_ekf_type w.ahrs))) }
  for _ in [0:1] do
    pure ()
  s := { s with _rotation_vehicle_body_to_autopilot_body := AP_AHRS.get_rotation_vehicle_body_to_autopilot_body w.ahrs }
  s := { s with _ins := AP_DAL_InertialSensor.start_frame s._ins w }
  s := { s with _baro := AP_DAL_Baro.start_frame s._baro w }
  s := { s with _gps := AP_DAL_GPS.start_frame s._gps w }
  s := { s with _compass := AP_DAL_Compass.start_frame s._compass w }
  if (s._airspeed != WPtr.null) then
    pure ()  -- C++ `start_frame`: no effect in the model
  s := { s with _micros := UInt64.toUInt32 s._RFRH.time_us }
  s := { s with _millis := UInt64.toUInt32 (s._RFRH.time_us / (1000 : UInt64)) }
  w := { w with AP_DAL'force_write := false }
  return (s, w)

/-- C++ `uint64_t AP_DAL::micros64() const`, `AP_DAL/AP_DAL.h:89`. -/
def micros64 (s : State) : UInt64 := Id.run do
  return s._RFRH.time_us

/-- C++ `uint32_t AP_DAL::available_memory() const`, `AP_DAL/AP_DAL.h:133`. -/
def available_memory (s : State) : UInt32 := Id.run do
  return s._RFRN.available_memory + Int32.toUInt32 (10240 : Int32)

end AP_DAL

namespace AP_DAL

/-- C++ `uint32_t AP_DAL::millis() const`, `AP_DAL/AP_DAL.h:91`. -/
def millis (s : State) : UInt32 := Id.run do
  return s._millis

/-- C++ `AP_DAL_Airspeed * AP_DAL::airspeed()`, `AP_DAL/AP_DAL.h:162-164`. -/
def airspeed (s : State) : WPtr := Id.run do
  return s._airspeed

/-- C++ `bool AP_DAL::opticalflow_enabled() const`, `AP_DAL/AP_DAL.h:223-225`. -/
def opticalflow_enabled (s : State) : Bool := Id.run do
  return s._RFRN.opticalflow_enabled != (0 : UInt8)

end AP_DAL

namespace AP_DAL

/-- C++ `AP_DAL::AP_DAL()`, `AP_DAL/AP_DAL.h:78`. -/
def init : State := Id.run do
  let mut s : State := {}
  s := { s with _rotation_vehicle_body_to_autopilot_body := Matrix3f.init_void }
  s := { s with _home := Location.init_void }
  s := { s with _ins := AP_DAL_InertialSensor.init }
  s := { s with _baro := AP_DAL_Baro.init }
  s := { s with _gps := AP_DAL_GPS.init }
  s := { s with _compass := AP_DAL_Compass.init }
  return s

/-- C++ `static AP_DAL * AP_DAL::get_singleton()`, `AP_DAL/AP_DAL.h:80-85`. -/
def get_singleton (w : World) : World × WPtr := Id.run do
  let mut w := w
  if !(w.AP_DAL'_singleton != WPtr.null) then
    let t'1 := AP_DAL.init
    let t'2 := w.heap'AP_DAL.size
    w := { w with heap'AP_DAL := w.heap'AP_DAL.push t'1 }
    w := { w with AP_DAL'_singleton := (WPtr.heap'AP_DAL t'2) }
  return (w, w.AP_DAL'_singleton)

end AP_DAL

namespace AP_DAL

/-- C++ `enum class AP_DAL::EKFType`, `AP_DAL/AP_DAL.h:116-119`. -/
inductive EKFType where
  | EKF2
  | EKF3
deriving DecidableEq, Inhabited

/-- The value of each enumerator of `AP_DAL::EKFType` (underlying type `uint8_t`). -/
def EKFType.toInt : EKFType → UInt8
  | .EKF2 => (0 : UInt8)
  | .EKF3 => (1 : UInt8)

/-- C++ `bool AP_DAL::ekf_low_time_remaining(EKFType etype, uint8_t core)`, `AP_DAL/AP_DAL.cpp:327-345`. -/
def ekf_low_time_remaining (s : State) (w : World) (etype : AP_DAL.EKFType) (core : UInt8) : State × Bool := Id.run do
  let mut s := s
  let mask : UInt8 := UInt32.toUInt8 ((1 : UInt32) <<< Int32.toUInt32 (UInt32.toInt32 (UInt8.toUInt32 core) + (UInt32.toInt32 (UInt8.toUInt32 (AP_DAL.EKFType.toInt etype)) * (4 : Int32))))
  if UInt32.toBinary32 (Estimator_lib.micros w - AP_InertialSensor.get_last_update_usec w.ins) * (Binary32.ofBits 0x358637bd /- 1.0e-6 -/) > AP_InertialSensor.get_loop_delta_t w.ins * (Binary32.ofBits 0x3ea8f5c3 /- 0.33 -/) then
    s := { s with _RFRF.core_slow := Int8.toUInt8 (Int32.toInt8 (UInt32.toInt32 (UInt8.toUInt32 s._RFRF.core_slow) ||| UInt32.toInt32 (UInt8.toUInt32 mask))) }
  else
    s := { s with _RFRF.core_slow := Int8.toUInt8 (Int32.toInt8 (UInt32.toInt32 (UInt8.toUInt32 s._RFRF.core_slow) &&& ~~~(UInt32.toInt32 (UInt8.toUInt32 mask)))) }
  return (s, (UInt32.toInt32 (UInt8.toUInt32 s._RFRF.core_slow) &&& UInt32.toInt32 (UInt8.toUInt32 mask)) != (0 : Int32))

end AP_DAL

namespace AP_DAL

/-- C++ `void AP_DAL::set_takeoff_expected()`, `AP_DAL/AP_DAL.cpp:123-129`. -/
def set_takeoff_expected (w : World) : World := Id.run do
  let mut w := w
  let t'1 := w.ahrs  -- the object out of the World for the call (--swap-out)
  w := { w with ahrs := default }
  w := { w with ahrs := AP_AHRS.set_takeoff_expected t'1 w true }
  return w

end AP_DAL

end Estimator_lib
