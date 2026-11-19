import ArduLean.Runtime.CFloat
import ArduLean.Estimator.libraries.AP_Math.AP_Math
import ArduLean.Estimator.World
import ArduLean.Estimator.libraries.AP_Common.AP_Common
import ArduLean.Estimator.libraries.AP_GPS.AP_GPS

/-!
ArduPilot `libraries/AP_DAL`, part 1 of 2. Sources: `libraries/AP_DAL/LogStructure.h`, `libraries/AP_DAL/AP_DAL.h`, `libraries/AP_DAL/AP_DAL_GPS.h`, `libraries/AP_DAL/AP_DAL_InertialSensor.h`, `libraries/AP_DAL/AP_DAL_Compass.h`, `libraries/AP_DAL/AP_DAL.cpp`, `libraries/AP_DAL/AP_DAL_Airspeed.h`, `libraries/AP_DAL/AP_DAL_Baro.h` and 2 more.

Items of `lean/Estimator_lib.lean` (the estimator translation), unchanged; placed by `tools/split_modules.py` (`ArduLean/Estimator/INDEX.md`).
-/

open FloatLib.Floats (Binary32 Binary64)

set_option maxRecDepth 200000
-- AP_DAL's `const log_RISH old_RISH = _RISH;` read only by WRITE_REPLAY_BLOCK_IFCHANGED, which is `(void)old`
-- without logging (HAL_LOGGING_ENABLED 0): an unused binding, as in the C++
set_option linter.unusedVariables false

namespace Estimator_lib

/-- C++ `struct log_RBRH`, `AP_DAL/LogStructure.h:239-243`. -/
structure log_RBRH where
  /-- `uint8_t primary` of `log_RBRH` (`AP_DAL/LogStructure.h:240`). -/
  primary : UInt8 := (0 : UInt8)
  /-- `uint8_t num_instances` of `log_RBRH` (`AP_DAL/LogStructure.h:241`). -/
  num_instances : UInt8 := (0 : UInt8)
  /-- `uint8_t _end` of `log_RBRH` (`AP_DAL/LogStructure.h:242`). -/
  _end : UInt8 := (0 : UInt8)
deriving Inhabited

/-- C++ `struct log_RBRI`, `AP_DAL/LogStructure.h:251-257`. -/
structure log_RBRI where
  /-- `uint32_t last_update_ms` of `log_RBRI` (`AP_DAL/LogStructure.h:252`). -/
  last_update_ms : UInt32 := (0 : UInt32)
  /-- `float altitude` of `log_RBRI` (`AP_DAL/LogStructure.h:253`). -/
  altitude : Binary32 := (Binary32.ofBits 0x00000000 /- 0.0 -/)
  /-- `bool healthy` of `log_RBRI` (`AP_DAL/LogStructure.h:254`). -/
  healthy : Bool := false
  /-- `uint8_t instance` of `log_RBRI` (`AP_DAL/LogStructure.h:255`). -/
  «instance» : UInt8 := (0 : UInt8)
  /-- `uint8_t _end` of `log_RBRI` (`AP_DAL/LogStructure.h:256`). -/
  _end : UInt8 := (0 : UInt8)
deriving Inhabited

namespace AP_DAL_Baro

/-- State of C++ `AP_DAL_Baro` (`AP_DAL/AP_DAL_Baro.h:7-52`): its data members. -/
structure State where
  /-- `struct log_RBRH _RBRH` of `AP_DAL_Baro` (`AP_DAL/AP_DAL_Baro.h:50`). -/
  _RBRH : log_RBRH := {}
  /-- `struct log_RBRI _RBRI[3]` of `AP_DAL_Baro` (`AP_DAL/AP_DAL_Baro.h:51`). -/
  _RBRI : Array log_RBRI := Array.replicate 3 {}
deriving Inhabited

/-- C++ `AP_DAL_Baro::AP_DAL_Baro()`, `AP_DAL/AP_DAL_Baro.cpp:6-11`. -/
def init : State := Id.run do
  let mut s : State := {}
  for i' in [0:3] do
    let i : UInt8 := Nat.toUInt8 i'
    s := { s with _RBRI := s._RBRI.set! (UInt8.toNat i) ({ s._RBRI[UInt8.toNat i]! with «instance» := i }) }
  return s

end AP_DAL_Baro

/-- C++ `struct log_RMGH`, `AP_DAL/LogStructure.h:410-420`. -/
structure log_RMGH where
  /-- `float declination` of `log_RMGH` (`AP_DAL/LogStructure.h:411`). -/
  declination : Binary32 := (Binary32.ofBits 0x00000000 /- 0.0 -/)
  /-- `bool available` of `log_RMGH` (`AP_DAL/LogStructure.h:412`). -/
  available : Bool := false
  /-- `uint8_t count` of `log_RMGH` (`AP_DAL/LogStructure.h:413`). -/
  count : UInt8 := (0 : UInt8)
  /-- `bool auto_declination_enabled` of `log_RMGH` (`AP_DAL/LogStructure.h:414`). -/
  auto_declination_enabled : Bool := false
  /-- `uint8_t num_enabled` of `log_RMGH` (`AP_DAL/LogStructure.h:415`). -/
  num_enabled : UInt8 := (0 : UInt8)
  /-- `bool learn_offsets_enabled` of `log_RMGH` (`AP_DAL/LogStructure.h:416`). -/
  learn_offsets_enabled : Bool := false
  /-- `bool consistent` of `log_RMGH` (`AP_DAL/LogStructure.h:417`). -/
  consistent : Bool := false
  /-- `uint8_t first_usable` of `log_RMGH` (`AP_DAL/LogStructure.h:418`). -/
  first_usable : UInt8 := (0 : UInt8)
  /-- `uint8_t _end` of `log_RMGH` (`AP_DAL/LogStructure.h:419`). -/
  _end : UInt8 := (0 : UInt8)
deriving Inhabited

/-- C++ `struct log_RMGI`, `AP_DAL/LogStructure.h:435-444`. -/
structure log_RMGI where
  /-- `uint32_t last_update_usec` of `log_RMGI` (`AP_DAL/LogStructure.h:436`). -/
  last_update_usec : UInt32 := (0 : UInt32)
  /-- `Vector3f offsets` of `log_RMGI` (`AP_DAL/LogStructure.h:437`). -/
  offsets : Vector3f.State := {}
  /-- `Vector3f field` of `log_RMGI` (`AP_DAL/LogStructure.h:438`). -/
  field : Vector3f.State := {}
  /-- `bool use_for_yaw` of `log_RMGI` (`AP_DAL/LogStructure.h:439`). -/
  use_for_yaw : Bool := false
  /-- `bool healthy` of `log_RMGI` (`AP_DAL/LogStructure.h:440`). -/
  healthy : Bool := false
  /-- `bool have_scale_factor` of `log_RMGI` (`AP_DAL/LogStructure.h:441`). -/
  have_scale_factor : Bool := false
  /-- `uint8_t instance` of `log_RMGI` (`AP_DAL/LogStructure.h:442`). -/
  «instance» : UInt8 := (0 : UInt8)
  /-- `uint8_t _end` of `log_RMGI` (`AP_DAL/LogStructure.h:443`). -/
  _end : UInt8 := (0 : UInt8)
deriving Inhabited

namespace AP_DAL_Compass

/-- State of C++ `AP_DAL_Compass` (`AP_DAL/AP_DAL_Compass.h:7-77`): its data members. -/
structure State where
  /-- `struct log_RMGH _RMGH` of `AP_DAL_Compass` (`AP_DAL/AP_DAL_Compass.h:75`). -/
  _RMGH : log_RMGH := {}
  /-- `struct log_RMGI _RMGI[3]` of `AP_DAL_Compass` (`AP_DAL/AP_DAL_Compass.h:76`). -/
  _RMGI : Array log_RMGI := Array.replicate 3 {}
deriving Inhabited

/-- C++ `AP_DAL_Compass::AP_DAL_Compass()`, `AP_DAL/AP_DAL_Compass.cpp:8-13`. -/
def init : State := Id.run do
  let mut s : State := {}
  for i' in [0:3] do
    let i : UInt8 := Nat.toUInt8 i'
    s := { s with _RMGI := s._RMGI.set! (UInt8.toNat i) ({ s._RMGI[UInt8.toNat i]! with «instance» := i }) }
  return s

end AP_DAL_Compass

/-- C++ `struct log_RGPH`, `AP_DAL/LogStructure.h:294-298`. -/
structure log_RGPH where
  /-- `uint8_t num_sensors` of `log_RGPH` (`AP_DAL/LogStructure.h:295`). -/
  num_sensors : UInt8 := (0 : UInt8)
  /-- `uint8_t primary_sensor` of `log_RGPH` (`AP_DAL/LogStructure.h:296`). -/
  primary_sensor : UInt8 := (0 : UInt8)
  /-- `uint8_t _end` of `log_RGPH` (`AP_DAL/LogStructure.h:297`). -/
  _end : UInt8 := (0 : UInt8)
deriving Inhabited

/-- C++ `struct log_RGPI`, `AP_DAL/LogStructure.h:311-324`. -/
structure log_RGPI where
  /-- `Vector3f antenna_offset` of `log_RGPI` (`AP_DAL/LogStructure.h:312`). -/
  antenna_offset : Vector3f.State := {}
  /-- `float lag_sec` of `log_RGPI` (`AP_DAL/LogStructure.h:313`). -/
  lag_sec : Binary32 := (Binary32.ofBits 0x00000000 /- 0.0 -/)
  /-- `uint8_t have_vertical_velocity : 1` of `log_RGPI` (`AP_DAL/LogStructure.h:314`). -/
  have_vertical_velocity : UInt8 := (0 : UInt8)
  /-- `uint8_t horizontal_accuracy_returncode : 1` of `log_RGPI` (`AP_DAL/LogStructure.h:315`). -/
  horizontal_accuracy_returncode : UInt8 := (0 : UInt8)
  /-- `uint8_t vertical_accuracy_returncode : 1` of `log_RGPI` (`AP_DAL/LogStructure.h:316`). -/
  vertical_accuracy_returncode : UInt8 := (0 : UInt8)
  /-- `uint8_t get_lag_returncode : 1` of `log_RGPI` (`AP_DAL/LogStructure.h:317`). -/
  get_lag_returncode : UInt8 := (0 : UInt8)
  /-- `uint8_t speed_accuracy_returncode : 1` of `log_RGPI` (`AP_DAL/LogStructure.h:318`). -/
  speed_accuracy_returncode : UInt8 := (0 : UInt8)
  /-- `uint8_t gps_yaw_deg_returncode : 1` of `log_RGPI` (`AP_DAL/LogStructure.h:319`). -/
  gps_yaw_deg_returncode : UInt8 := (0 : UInt8)
  /-- `uint8_t status` of `log_RGPI` (`AP_DAL/LogStructure.h:320`). -/
  status : UInt8 := (0 : UInt8)
  /-- `uint8_t num_sats` of `log_RGPI` (`AP_DAL/LogStructure.h:321`). -/
  num_sats : UInt8 := (0 : UInt8)
  /-- `uint8_t instance` of `log_RGPI` (`AP_DAL/LogStructure.h:322`). -/
  «instance» : UInt8 := (0 : UInt8)
  /-- `uint8_t _end` of `log_RGPI` (`AP_DAL/LogStructure.h:323`). -/
  _end : UInt8 := (0 : UInt8)
deriving Inhabited

/-- C++ `struct log_RGPJ`, `AP_DAL/LogStructure.h:343-358`. -/
structure log_RGPJ where
  /-- `uint32_t last_message_time_ms` of `log_RGPJ` (`AP_DAL/LogStructure.h:344`). -/
  last_message_time_ms : UInt32 := (0 : UInt32)
  /-- `Vector3f velocity` of `log_RGPJ` (`AP_DAL/LogStructure.h:345`). -/
  velocity : Vector3f.State := {}
  /-- `float sacc` of `log_RGPJ` (`AP_DAL/LogStructure.h:346`). -/
  sacc : Binary32 := (Binary32.ofBits 0x00000000 /- 0.0 -/)
  /-- `float yaw_deg` of `log_RGPJ` (`AP_DAL/LogStructure.h:347`). -/
  yaw_deg : Binary32 := (Binary32.ofBits 0x00000000 /- 0.0 -/)
  /-- `float yaw_accuracy_deg` of `log_RGPJ` (`AP_DAL/LogStructure.h:348`). -/
  yaw_accuracy_deg : Binary32 := (Binary32.ofBits 0x00000000 /- 0.0 -/)
  /-- `uint32_t yaw_deg_time_ms` of `log_RGPJ` (`AP_DAL/LogStructure.h:349`). -/
  yaw_deg_time_ms : UInt32 := (0 : UInt32)
  /-- `int32_t lat` of `log_RGPJ` (`AP_DAL/LogStructure.h:350`). -/
  lat : Int32 := (0 : Int32)
  /-- `int32_t lng` of `log_RGPJ` (`AP_DAL/LogStructure.h:351`). -/
  lng : Int32 := (0 : Int32)
  /-- `int32_t alt` of `log_RGPJ` (`AP_DAL/LogStructure.h:352`). -/
  alt : Int32 := (0 : Int32)
  /-- `float hacc` of `log_RGPJ` (`AP_DAL/LogStructure.h:353`). -/
  hacc : Binary32 := (Binary32.ofBits 0x00000000 /- 0.0 -/)
  /-- `float vacc` of `log_RGPJ` (`AP_DAL/LogStructure.h:354`). -/
  vacc : Binary32 := (Binary32.ofBits 0x00000000 /- 0.0 -/)
  /-- `uint16_t hdop` of `log_RGPJ` (`AP_DAL/LogStructure.h:355`). -/
  hdop : UInt16 := (0 : UInt16)
  /-- `uint8_t instance` of `log_RGPJ` (`AP_DAL/LogStructure.h:356`). -/
  «instance» : UInt8 := (0 : UInt8)
  /-- `uint8_t _end` of `log_RGPJ` (`AP_DAL/LogStructure.h:357`). -/
  _end : UInt8 := (0 : UInt8)
deriving Inhabited

namespace AP_DAL_GPS

/-- State of C++ `AP_DAL_GPS` (`AP_DAL/AP_DAL_GPS.h:7-151`): its data members. -/
structure State where
  /-- `struct log_RGPH _RGPH` of `AP_DAL_GPS` (`AP_DAL/AP_DAL_GPS.h:143`). -/
  _RGPH : log_RGPH := {}
  /-- `struct log_RGPI _RGPI[3]` of `AP_DAL_GPS` (`AP_DAL/AP_DAL_GPS.h:144`). -/
  _RGPI : Array log_RGPI := Array.replicate 3 {}
  /-- `struct log_RGPJ _RGPJ[3]` of `AP_DAL_GPS` (`AP_DAL/AP_DAL_GPS.h:145`). -/
  _RGPJ : Array log_RGPJ := Array.replicate 3 {}
  /-- `Location tmp_location[3]` of `AP_DAL_GPS` (`AP_DAL/AP_DAL_GPS.h:150`). -/
  tmp_location : Array Location.State := Array.replicate 3 {}
deriving Inhabited

/-- C++ `AP_DAL_GPS::AP_DAL_GPS()`, `AP_DAL/AP_DAL_GPS.cpp:6-17`. -/
def init : State := Id.run do
  let mut s : State := {}
  for i' in [0:3] do
    let i : UInt8 := Nat.toUInt8 i'
    s := { s with _RGPI := s._RGPI.set! (UInt8.toNat i) ({ s._RGPI[UInt8.toNat i]! with «instance» := i }) }
    s := { s with _RGPJ := s._RGPJ.set! (UInt8.toNat i) ({ s._RGPJ[UInt8.toNat i]! with «instance» := i }) }
  return s

end AP_DAL_GPS

/-- C++ `struct log_RISH`, `AP_DAL/LogStructure.h:123-131`. -/
structure log_RISH where
  /-- `uint16_t loop_rate_hz` of `log_RISH` (`AP_DAL/LogStructure.h:124`). -/
  loop_rate_hz : UInt16 := (0 : UInt16)
  /-- `uint8_t first_usable_gyro` of `log_RISH` (`AP_DAL/LogStructure.h:125`). -/
  first_usable_gyro : UInt8 := (0 : UInt8)
  /-- `uint8_t first_usable_accel` of `log_RISH` (`AP_DAL/LogStructure.h:126`). -/
  first_usable_accel : UInt8 := (0 : UInt8)
  /-- `float loop_delta_t` of `log_RISH` (`AP_DAL/LogStructure.h:127`). -/
  loop_delta_t : Binary32 := (Binary32.ofBits 0x00000000 /- 0.0 -/)
  /-- `uint8_t accel_count` of `log_RISH` (`AP_DAL/LogStructure.h:128`). -/
  accel_count : UInt8 := (0 : UInt8)
  /-- `uint8_t gyro_count` of `log_RISH` (`AP_DAL/LogStructure.h:129`). -/
  gyro_count : UInt8 := (0 : UInt8)
  /-- `uint8_t _end` of `log_RISH` (`AP_DAL/LogStructure.h:130`). -/
  _end : UInt8 := (0 : UInt8)
deriving Inhabited

/-- C++ `struct log_RISI`, `AP_DAL/LogStructure.h:145-156`. -/
structure log_RISI where
  /-- `Vector3f delta_velocity` of `log_RISI` (`AP_DAL/LogStructure.h:146`). -/
  delta_velocity : Vector3f.State := {}
  /-- `Vector3f delta_angle` of `log_RISI` (`AP_DAL/LogStructure.h:147`). -/
  delta_angle : Vector3f.State := {}
  /-- `float delta_velocity_dt` of `log_RISI` (`AP_DAL/LogStructure.h:148`). -/
  delta_velocity_dt : Binary32 := (Binary32.ofBits 0x00000000 /- 0.0 -/)
  /-- `float delta_angle_dt` of `log_RISI` (`AP_DAL/LogStructure.h:149`). -/
  delta_angle_dt : Binary32 := (Binary32.ofBits 0x00000000 /- 0.0 -/)
  /-- `uint8_t use_accel : 1` of `log_RISI` (`AP_DAL/LogStructure.h:150`). -/
  use_accel : UInt8 := (0 : UInt8)
  /-- `uint8_t use_gyro : 1` of `log_RISI` (`AP_DAL/LogStructure.h:151`). -/
  use_gyro : UInt8 := (0 : UInt8)
  /-- `uint8_t get_delta_velocity_ret : 1` of `log_RISI` (`AP_DAL/LogStructure.h:152`). -/
  get_delta_velocity_ret : UInt8 := (0 : UInt8)
  /-- `uint8_t get_delta_angle_ret : 1` of `log_RISI` (`AP_DAL/LogStructure.h:153`). -/
  get_delta_angle_ret : UInt8 := (0 : UInt8)
  /-- `uint8_t instance` of `log_RISI` (`AP_DAL/LogStructure.h:154`). -/
  «instance» : UInt8 := (0 : UInt8)
  /-- `uint8_t _end` of `log_RISI` (`AP_DAL/LogStructure.h:155`). -/
  _end : UInt8 := (0 : UInt8)
deriving Inhabited

/-- C++ `struct log_RISJ`, `AP_DAL/LogStructure.h:163-168`. -/
structure log_RISJ where
  /-- `float gyro_bias_limit` of `log_RISJ` (`AP_DAL/LogStructure.h:164`). -/
  gyro_bias_limit : Binary32 := (Binary32.ofBits 0x00000000 /- 0.0 -/)
  /-- `float gyro_bias_init_dps` of `log_RISJ` (`AP_DAL/LogStructure.h:165`). -/
  gyro_bias_init_dps : Binary32 := (Binary32.ofBits 0x00000000 /- 0.0 -/)
  /-- `uint8_t instance` of `log_RISJ` (`AP_DAL/LogStructure.h:166`). -/
  «instance» : UInt8 := (0 : UInt8)
  /-- `uint8_t _end` of `log_RISJ` (`AP_DAL/LogStructure.h:167`). -/
  _end : UInt8 := (0 : UInt8)
deriving Inhabited

namespace AP_DAL_InertialSensor

/-- State of C++ `AP_DAL_InertialSensor` (`AP_DAL/AP_DAL_InertialSensor.h:7-81`): its data members. -/
structure State where
  /-- `struct log_RISH _RISH` of `AP_DAL_InertialSensor` (`AP_DAL/AP_DAL_InertialSensor.h:67`). -/
  _RISH : log_RISH := {}
  /-- `struct log_RISI _RISI[3]` of `AP_DAL_InertialSensor` (`AP_DAL/AP_DAL_InertialSensor.h:68`). -/
  _RISI : Array log_RISI := Array.replicate 3 {}
  /-- `struct log_RISJ _RISJ[3]` of `AP_DAL_InertialSensor` (`AP_DAL/AP_DAL_InertialSensor.h:69`). -/
  _RISJ : Array log_RISJ := Array.replicate 3 {}
  /-- `float alpha` of `AP_DAL_InertialSensor` (`AP_DAL/AP_DAL_InertialSensor.h:70`). -/
  alpha : Binary32 := (Binary32.ofBits 0x00000000 /- 0.0 -/)
  /-- `Vector3f pos[3]` of `AP_DAL_InertialSensor` (`AP_DAL/AP_DAL_InertialSensor.h:73`). -/
  pos : Array Vector3f.State := Array.replicate 3 {}
  /-- `Vector3f gyro_filtered[3]` of `AP_DAL_InertialSensor` (`AP_DAL/AP_DAL_InertialSensor.h:75`). -/
  gyro_filtered : Array Vector3f.State := Array.replicate 3 {}
  /-- `Vector3f accel_filtered[3]` of `AP_DAL_InertialSensor` (`AP_DAL/AP_DAL_InertialSensor.h:76`). -/
  accel_filtered : Array Vector3f.State := Array.replicate 3 {}
  /-- `uint8_t _primary_gyro` of `AP_DAL_InertialSensor` (`AP_DAL/AP_DAL_InertialSensor.h:78`). -/
  _primary_gyro : UInt8 := (0 : UInt8)
deriving Inhabited

/-- C++ `AP_DAL_InertialSensor::AP_DAL_InertialSensor()`, `AP_DAL/AP_DAL_InertialSensor.cpp:6-18`. -/
def init : State := Id.run do
  let mut s : State := {}
  for i' in [0:3] do
    let i : UInt8 := Nat.toUInt8 i'
    s := { s with _RISI := s._RISI.set! (UInt8.toNat i) ({ s._RISI[UInt8.toNat i]! with «instance» := i }) }
  for i'2' in [0:3] do
    let i'2 : UInt8 := Nat.toUInt8 i'2'
    s := { s with _RISJ := s._RISJ.set! (UInt8.toNat i'2) ({ s._RISJ[UInt8.toNat i'2]! with «instance» := i'2 }) }
    s := { s with _RISJ := s._RISJ.set! (UInt8.toNat i'2) ({ s._RISJ[UInt8.toNat i'2]! with gyro_bias_limit := (Binary32.ofBits 0x3f000000 /- 0.5f -/) }) }
    s := { s with _RISJ := s._RISJ.set! (UInt8.toNat i'2) ({ s._RISJ[UInt8.toNat i'2]! with gyro_bias_init_dps := (Binary32.ofBits 0x40200000 /- 2.5f -/) }) }
  return s

end AP_DAL_InertialSensor

/-- C++ `struct log_RFRH`, `AP_DAL/LogStructure.h:63-67`. -/
structure log_RFRH where
  /-- `uint64_t time_us` of `log_RFRH` (`AP_DAL/LogStructure.h:64`). -/
  time_us : UInt64 := (0 : UInt64)
  /-- `uint32_t time_flying_ms` of `log_RFRH` (`AP_DAL/LogStructure.h:65`). -/
  time_flying_ms : UInt32 := (0 : UInt32)
  /-- `uint8_t _end` of `log_RFRH` (`AP_DAL/LogStructure.h:66`). -/
  _end : UInt8 := (0 : UInt8)
deriving Inhabited

/-- C++ `struct log_RFRF`, `AP_DAL/LogStructure.h:74-78`. -/
structure log_RFRF where
  /-- `uint8_t frame_types` of `log_RFRF` (`AP_DAL/LogStructure.h:75`). -/
  frame_types : UInt8 := (0 : UInt8)
  /-- `uint8_t core_slow` of `log_RFRF` (`AP_DAL/LogStructure.h:76`). -/
  core_slow : UInt8 := (0 : UInt8)
  /-- `uint8_t _end` of `log_RFRF` (`AP_DAL/LogStructure.h:77`). -/
  _end : UInt8 := (0 : UInt8)
deriving Inhabited

/-- C++ `struct log_RFRN`, `AP_DAL/LogStructure.h:95-113`. -/
structure log_RFRN where
  /-- `int32_t lat` of `log_RFRN` (`AP_DAL/LogStructure.h:96`). -/
  lat : Int32 := (0 : Int32)
  /-- `int32_t lng` of `log_RFRN` (`AP_DAL/LogStructure.h:97`). -/
  lng : Int32 := (0 : Int32)
  /-- `int32_t alt` of `log_RFRN` (`AP_DAL/LogStructure.h:98`). -/
  alt : Int32 := (0 : Int32)
  /-- `float EAS2TAS` of `log_RFRN` (`AP_DAL/LogStructure.h:99`). -/
  EAS2TAS : Binary32 := (Binary32.ofBits 0x00000000 /- 0.0 -/)
  /-- `uint32_t available_memory` of `log_RFRN` (`AP_DAL/LogStructure.h:100`). -/
  available_memory : UInt32 := (0 : UInt32)
  /-- `Vector3f ahrs_trim` of `log_RFRN` (`AP_DAL/LogStructure.h:101`). -/
  ahrs_trim : Vector3f.State := {}
  /-- `uint8_t vehicle_class` of `log_RFRN` (`AP_DAL/LogStructure.h:102`). -/
  vehicle_class : UInt8 := (0 : UInt8)
  /-- `uint8_t ekf_type` of `log_RFRN` (`AP_DAL/LogStructure.h:103`). -/
  ekf_type : UInt8 := (0 : UInt8)
  /-- `uint8_t armed : 1` of `log_RFRN` (`AP_DAL/LogStructure.h:104`). -/
  armed : UInt8 := (0 : UInt8)
  /-- `uint8_t unused : 1` of `log_RFRN` (`AP_DAL/LogStructure.h:105`). -/
  unused : UInt8 := (0 : UInt8)
  /-- `uint8_t fly_forward : 1` of `log_RFRN` (`AP_DAL/LogStructure.h:106`). -/
  fly_forward : UInt8 := (0 : UInt8)
  /-- `uint8_t ahrs_airspeed_sensor_enabled_unused : 1` of `log_RFRN` (`AP_DAL/LogStructure.h:107`). -/
  ahrs_airspeed_sensor_enabled_unused : UInt8 := (0 : UInt8)
  /-- `uint8_t opticalflow_enabled : 1` of `log_RFRN` (`AP_DAL/LogStructure.h:108`). -/
  opticalflow_enabled : UInt8 := (0 : UInt8)
  /-- `uint8_t wheelencoder_enabled : 1` of `log_RFRN` (`AP_DAL/LogStructure.h:109`). -/
  wheelencoder_enabled : UInt8 := (0 : UInt8)
  /-- `uint8_t takeoff_expected : 1` of `log_RFRN` (`AP_DAL/LogStructure.h:110`). -/
  takeoff_expected : UInt8 := (0 : UInt8)
  /-- `uint8_t touchdown_expected : 1` of `log_RFRN` (`AP_DAL/LogStructure.h:111`). -/
  touchdown_expected : UInt8 := (0 : UInt8)
  /-- `uint8_t _end` of `log_RFRN` (`AP_DAL/LogStructure.h:112`). -/
  _end : UInt8 := (0 : UInt8)
deriving Inhabited

/-- C++ `struct log_ROFH`, `AP_DAL/LogStructure.h:516-524`. -/
structure log_ROFH where
  /-- `Vector2f rawFlowRates` of `log_ROFH` (`AP_DAL/LogStructure.h:517`). -/
  rawFlowRates : Vector2f.State := {}
  /-- `Vector2f rawGyroRates` of `log_ROFH` (`AP_DAL/LogStructure.h:518`). -/
  rawGyroRates : Vector2f.State := {}
  /-- `uint32_t msecFlowMeas` of `log_ROFH` (`AP_DAL/LogStructure.h:519`). -/
  msecFlowMeas : UInt32 := (0 : UInt32)
  /-- `Vector3f posOffset` of `log_ROFH` (`AP_DAL/LogStructure.h:520`). -/
  posOffset : Vector3f.State := {}
  /-- `float heightOverride` of `log_ROFH` (`AP_DAL/LogStructure.h:521`). -/
  heightOverride : Binary32 := (Binary32.ofBits 0x00000000 /- 0.0 -/)
  /-- `uint8_t rawFlowQuality` of `log_ROFH` (`AP_DAL/LogStructure.h:522`). -/
  rawFlowQuality : UInt8 := (0 : UInt8)
  /-- `uint8_t _end` of `log_ROFH` (`AP_DAL/LogStructure.h:523`). -/
  _end : UInt8 := (0 : UInt8)
deriving Inhabited

/-- C++ `struct log_REPH`, `AP_DAL/LogStructure.h:540-549`. -/
structure log_REPH where
  /-- `Vector3f pos` of `log_REPH` (`AP_DAL/LogStructure.h:541`). -/
  pos : Vector3f.State := {}
  /-- `Quaternion quat` of `log_REPH` (`AP_DAL/LogStructure.h:542`). -/
  quat : Quaternion.State := Quaternion.init_void
  /-- `float posErr` of `log_REPH` (`AP_DAL/LogStructure.h:543`). -/
  posErr : Binary32 := (Binary32.ofBits 0x00000000 /- 0.0 -/)
  /-- `float angErr` of `log_REPH` (`AP_DAL/LogStructure.h:544`). -/
  angErr : Binary32 := (Binary32.ofBits 0x00000000 /- 0.0 -/)
  /-- `uint32_t timeStamp_ms` of `log_REPH` (`AP_DAL/LogStructure.h:545`). -/
  timeStamp_ms : UInt32 := (0 : UInt32)
  /-- `uint32_t resetTime_ms` of `log_REPH` (`AP_DAL/LogStructure.h:546`). -/
  resetTime_ms : UInt32 := (0 : UInt32)
  /-- `uint16_t delay_ms` of `log_REPH` (`AP_DAL/LogStructure.h:547`). -/
  delay_ms : UInt16 := (0 : UInt16)
  /-- `uint8_t _end` of `log_REPH` (`AP_DAL/LogStructure.h:548`). -/
  _end : UInt8 := (0 : UInt8)
deriving Inhabited

/-- C++ `struct log_RSLL`, `AP_DAL/LogStructure.h:557-563`. -/
structure log_RSLL where
  /-- `int32_t lat` of `log_RSLL` (`AP_DAL/LogStructure.h:558`). -/
  lat : Int32 := (0 : Int32)
  /-- `int32_t lng` of `log_RSLL` (`AP_DAL/LogStructure.h:559`). -/
  lng : Int32 := (0 : Int32)
  /-- `float posAccSD` of `log_RSLL` (`AP_DAL/LogStructure.h:560`). -/
  posAccSD : Binary32 := (Binary32.ofBits 0x00000000 /- 0.0 -/)
  /-- `uint32_t timestamp_ms` of `log_RSLL` (`AP_DAL/LogStructure.h:561`). -/
  timestamp_ms : UInt32 := (0 : UInt32)
  /-- `uint8_t _end` of `log_RSLL` (`AP_DAL/LogStructure.h:562`). -/
  _end : UInt8 := (0 : UInt8)
deriving Inhabited

/-- C++ `struct log_REVH`, `AP_DAL/LogStructure.h:573-579`. -/
structure log_REVH where
  /-- `Vector3f vel` of `log_REVH` (`AP_DAL/LogStructure.h:574`). -/
  vel : Vector3f.State := {}
  /-- `float err` of `log_REVH` (`AP_DAL/LogStructure.h:575`). -/
  err : Binary32 := (Binary32.ofBits 0x00000000 /- 0.0 -/)
  /-- `uint32_t timeStamp_ms` of `log_REVH` (`AP_DAL/LogStructure.h:576`). -/
  timeStamp_ms : UInt32 := (0 : UInt32)
  /-- `uint16_t delay_ms` of `log_REVH` (`AP_DAL/LogStructure.h:577`). -/
  delay_ms : UInt16 := (0 : UInt16)
  /-- `uint8_t _end` of `log_REVH` (`AP_DAL/LogStructure.h:578`). -/
  _end : UInt8 := (0 : UInt8)
deriving Inhabited

/-- C++ `struct log_RWOH`, `AP_DAL/LogStructure.h:590-597`. -/
structure log_RWOH where
  /-- `float delAng` of `log_RWOH` (`AP_DAL/LogStructure.h:591`). -/
  delAng : Binary32 := (Binary32.ofBits 0x00000000 /- 0.0 -/)
  /-- `float delTime` of `log_RWOH` (`AP_DAL/LogStructure.h:592`). -/
  delTime : Binary32 := (Binary32.ofBits 0x00000000 /- 0.0 -/)
  /-- `uint32_t timeStamp_ms` of `log_RWOH` (`AP_DAL/LogStructure.h:593`). -/
  timeStamp_ms : UInt32 := (0 : UInt32)
  /-- `Vector3f posOffset` of `log_RWOH` (`AP_DAL/LogStructure.h:594`). -/
  posOffset : Vector3f.State := {}
  /-- `float radius` of `log_RWOH` (`AP_DAL/LogStructure.h:595`). -/
  radius : Binary32 := (Binary32.ofBits 0x00000000 /- 0.0 -/)
  /-- `uint8_t _end` of `log_RWOH` (`AP_DAL/LogStructure.h:596`). -/
  _end : UInt8 := (0 : UInt8)
deriving Inhabited

/-- C++ `struct log_RBOH`, `AP_DAL/LogStructure.h:614-623`. -/
structure log_RBOH where
  /-- `float quality` of `log_RBOH` (`AP_DAL/LogStructure.h:615`). -/
  quality : Binary32 := (Binary32.ofBits 0x00000000 /- 0.0 -/)
  /-- `Vector3f delPos` of `log_RBOH` (`AP_DAL/LogStructure.h:616`). -/
  delPos : Vector3f.State := {}
  /-- `Vector3f delAng` of `log_RBOH` (`AP_DAL/LogStructure.h:617`). -/
  delAng : Vector3f.State := {}
  /-- `float delTime` of `log_RBOH` (`AP_DAL/LogStructure.h:618`). -/
  delTime : Binary32 := (Binary32.ofBits 0x00000000 /- 0.0 -/)
  /-- `uint32_t timeStamp_ms` of `log_RBOH` (`AP_DAL/LogStructure.h:619`). -/
  timeStamp_ms : UInt32 := (0 : UInt32)
  /-- `Vector3f posOffset` of `log_RBOH` (`AP_DAL/LogStructure.h:620`). -/
  posOffset : Vector3f.State := {}
  /-- `uint16_t delay_ms` of `log_RBOH` (`AP_DAL/LogStructure.h:621`). -/
  delay_ms : UInt16 := (0 : UInt16)
  /-- `uint8_t _end` of `log_RBOH` (`AP_DAL/LogStructure.h:622`). -/
  _end : UInt8 := (0 : UInt8)
deriving Inhabited

/-- C++ `struct log_RTER`, `AP_DAL/LogStructure.h:628-631`. -/
structure log_RTER where
  /-- `float alt_m` of `log_RTER` (`AP_DAL/LogStructure.h:629`). -/
  alt_m : Binary32 := (Binary32.ofBits 0x00000000 /- 0.0 -/)
  /-- `uint8_t _end` of `log_RTER` (`AP_DAL/LogStructure.h:630`). -/
  _end : UInt8 := (0 : UInt8)
deriving Inhabited

namespace AP_DAL

/-- State of C++ `AP_DAL` (`AP_DAL/AP_DAL.h:38-421`): its data members. -/
structure State where
  /-- `struct log_RFRH _RFRH` of `AP_DAL` (`AP_DAL/AP_DAL.h:377`). -/
  _RFRH : log_RFRH := {}
  /-- `struct log_RFRF _RFRF` of `AP_DAL` (`AP_DAL/AP_DAL.h:378`). -/
  _RFRF : log_RFRF := {}
  /-- `struct log_RFRN _RFRN` of `AP_DAL` (`AP_DAL/AP_DAL.h:379`). -/
  _RFRN : log_RFRN := {}
  /-- `struct log_ROFH _ROFH` of `AP_DAL` (`AP_DAL/AP_DAL.h:382`). -/
  _ROFH : log_ROFH := {}
  /-- `struct log_REPH _REPH` of `AP_DAL` (`AP_DAL/AP_DAL.h:383`). -/
  _REPH : log_REPH := {}
  /-- `struct log_REVH _REVH` of `AP_DAL` (`AP_DAL/AP_DAL.h:384`). -/
  _REVH : log_REVH := {}
  /-- `struct log_RWOH _RWOH` of `AP_DAL` (`AP_DAL/AP_DAL.h:385`). -/
  _RWOH : log_RWOH := {}
  /-- `struct log_RBOH _RBOH` of `AP_DAL` (`AP_DAL/AP_DAL.h:386`). -/
  _RBOH : log_RBOH := {}
  /-- `struct log_RSLL _RSLL` of `AP_DAL` (`AP_DAL/AP_DAL.h:387`). -/
  _RSLL : log_RSLL := {}
  /-- `struct log_RTER _RTER` of `AP_DAL` (`AP_DAL/AP_DAL.h:388`). -/
  _RTER : log_RTER := {}
  /-- `uint32_t _micros` of `AP_DAL` (`AP_DAL/AP_DAL.h:391`). -/
  _micros : UInt32 := (0 : UInt32)
  /-- `uint32_t _millis` of `AP_DAL` (`AP_DAL/AP_DAL.h:392`). -/
  _millis : UInt32 := (0 : UInt32)
  /-- `Matrix3f _rotation_vehicle_body_to_autopilot_body` of `AP_DAL` (`AP_DAL/AP_DAL.h:394`). -/
  _rotation_vehicle_body_to_autopilot_body : Matrix3f.State := Matrix3f.init_void
  /-- `Location _home` of `AP_DAL` (`AP_DAL/AP_DAL.h:395`). -/
  _home : Location.State := {}
  /-- `uint32_t _last_imu_time_us` of `AP_DAL` (`AP_DAL/AP_DAL.h:396`). -/
  _last_imu_time_us : UInt32 := (0 : UInt32)
  /-- `AP_DAL_InertialSensor _ins` of `AP_DAL` (`AP_DAL/AP_DAL.h:398`). -/
  _ins : AP_DAL_InertialSensor.State := AP_DAL_InertialSensor.init
  /-- `AP_DAL_Baro _baro` of `AP_DAL` (`AP_DAL/AP_DAL.h:399`). -/
  _baro : AP_DAL_Baro.State := AP_DAL_Baro.init
  /-- `AP_DAL_GPS _gps` of `AP_DAL` (`AP_DAL/AP_DAL.h:400`). -/
  _gps : AP_DAL_GPS.State := AP_DAL_GPS.init
  /-- `AP_DAL_Compass _compass` of `AP_DAL` (`AP_DAL/AP_DAL.h:404`). -/
  _compass : AP_DAL_Compass.State := AP_DAL_Compass.init
  /-- `AP_DAL_Airspeed * _airspeed` of `AP_DAL` (`AP_DAL/AP_DAL.h:405`). -/
  _airspeed : WPtr := WPtr.null
  /-- `bool ekf2_init_done` of `AP_DAL` (`AP_DAL/AP_DAL.h:416`). -/
  ekf2_init_done : Bool := false
  /-- `bool ekf3_init_done` of `AP_DAL` (`AP_DAL/AP_DAL.h:417`). -/
  ekf3_init_done : Bool := false
  /-- `bool init_done` of `AP_DAL` (`AP_DAL/AP_DAL.h:420`). -/
  init_done : Bool := false
deriving Inhabited

/-- Values C++ `AP_DAL` reads from objects outside the translation (--boundary): one field per distinct read, in first-use order. -/
structure Inputs where
  /-- `AP::vehicle().get_time_flying_ms()` (first read at `AP_DAL/AP_DAL.cpp:56`). -/
  get_time_flying_ms : UInt32 := (0 : UInt32)
  /-- `hal.util.get_soft_armed()` (first read at `AP_DAL/AP_DAL.cpp:65`). -/
  get_soft_armed : Bool := false
  /-- `hal.util.available_memory()` (first read at `AP_DAL/AP_DAL.cpp:79`). -/
  available_memory : UInt32 := (0 : UInt32)
  /-- `AP::wheelencoder() != nullptr` (first read at `AP_DAL/AP_DAL.cpp:84`). -/
  nonnull : Bool := false
  /-- `AP::wheelencoder().num_sensors()` (first read at `AP_DAL/AP_DAL.cpp:84`). -/
  num_sensors : UInt8 := (0 : UInt8)
deriving Inhabited

/-- C++ `void AP_DAL::end_frame()`, `AP_DAL/AP_DAL.cpp:180-186`. -/
def end_frame (s : State) : State := Id.run do
  let mut s := s
  if UInt32.toInt32 (UInt8.toUInt32 s._RFRF.frame_types) != (0 : Int32) then
    for _ in [0:1] do
      pure ()
    s := { s with _RFRF.frame_types := Int8.toUInt8 (Int32.toInt8 (0 : Int32)) }
  return s

/-- C++ `enum class AP_DAL::Event`, `AP_DAL/AP_DAL.h:50-67`. -/
inductive Event where
  | resetGyroBias
  | resetHeightDatum
  | setTerrainHgtStable
  | unsetTerrainHgtStable
  | requestYawReset
  | checkLaneSwitch
  | setSourceSet0
  | setSourceSet1
  | setSourceSet2
deriving DecidableEq, Inhabited

/-- The value of each enumerator of `AP_DAL::Event` (underlying type `uint8_t`). -/
def Event.toInt : Event → UInt8
  | .resetGyroBias => (0 : UInt8)
  | .resetHeightDatum => (1 : UInt8)
  | .setTerrainHgtStable => (9 : UInt8)
  | .unsetTerrainHgtStable => (10 : UInt8)
  | .requestYawReset => (11 : UInt8)
  | .checkLaneSwitch => (12 : UInt8)
  | .setSourceSet0 => (13 : UInt8)
  | .setSourceSet1 => (14 : UInt8)
  | .setSourceSet2 => (15 : UInt8)

/-- The enumerator of `AP_DAL::Event` with value `v` (the C++ converts only enumerator values; any other
value gives the first enumerator, the `Inhabited` default). -/
def Event.ofInt (v : UInt8) : Event :=
  if v == (0 : UInt8) then .resetGyroBias
  else if v == (1 : UInt8) then .resetHeightDatum
  else if v == (9 : UInt8) then .setTerrainHgtStable
  else if v == (10 : UInt8) then .unsetTerrainHgtStable
  else if v == (11 : UInt8) then .requestYawReset
  else if v == (12 : UInt8) then .checkLaneSwitch
  else if v == (13 : UInt8) then .setSourceSet0
  else if v == (14 : UInt8) then .setSourceSet1
  else if v == (15 : UInt8) then .setSourceSet2
  else default

end AP_DAL

/-- C++ `struct log_REV2`, `AP_DAL/LogStructure.h:174-177`. -/
structure log_REV2 where
  /-- `uint8_t event` of `log_REV2` (`AP_DAL/LogStructure.h:175`). -/
  event : UInt8 := (0 : UInt8)
  /-- `uint8_t _end` of `log_REV2` (`AP_DAL/LogStructure.h:176`). -/
  _end : UInt8 := (0 : UInt8)
deriving Inhabited

namespace AP_DAL

/-- C++ `void AP_DAL::log_event3(Event event)`, `AP_DAL/AP_DAL.cpp:223-232`. -/
def log_event3 (s : State) (event : AP_DAL.Event) : State := Id.run do
  let mut s := s
  s := end_frame s
  let pkt : log_REV2 := { event := AP_DAL.Event.toInt event, _end := (0 : UInt8) }
  for _ in [0:1] do
    pure ()
  return s

end AP_DAL

/-- C++ `struct log_RASH`, `AP_DAL/LogStructure.h:378-382`. -/
structure log_RASH where
  /-- `uint8_t num_sensors` of `log_RASH` (`AP_DAL/LogStructure.h:379`). -/
  num_sensors : UInt8 := (0 : UInt8)
  /-- `uint8_t primary` of `log_RASH` (`AP_DAL/LogStructure.h:380`). -/
  primary : UInt8 := (0 : UInt8)
  /-- `uint8_t _end` of `log_RASH` (`AP_DAL/LogStructure.h:381`). -/
  _end : UInt8 := (0 : UInt8)
deriving Inhabited

/-- C++ `struct log_RASI`, `AP_DAL/LogStructure.h:391-398`. -/
structure log_RASI where
  /-- `float airspeed` of `log_RASI` (`AP_DAL/LogStructure.h:392`). -/
  airspeed : Binary32 := (Binary32.ofBits 0x00000000 /- 0.0 -/)
  /-- `uint32_t last_update_ms` of `log_RASI` (`AP_DAL/LogStructure.h:393`). -/
  last_update_ms : UInt32 := (0 : UInt32)
  /-- `bool healthy` of `log_RASI` (`AP_DAL/LogStructure.h:394`). -/
  healthy : Bool := false
  /-- `bool use` of `log_RASI` (`AP_DAL/LogStructure.h:395`). -/
  use : Bool := false
  /-- `uint8_t instance` of `log_RASI` (`AP_DAL/LogStructure.h:396`). -/
  «instance» : UInt8 := (0 : UInt8)
  /-- `uint8_t _end` of `log_RASI` (`AP_DAL/LogStructure.h:397`). -/
  _end : UInt8 := (0 : UInt8)
deriving Inhabited

namespace AP_DAL_Airspeed

/-- State of C++ `AP_DAL_Airspeed` (`AP_DAL/AP_DAL_Airspeed.h:7-63`): its data members. -/
structure State where
  /-- `struct log_RASH _RASH` of `AP_DAL_Airspeed` (`AP_DAL/AP_DAL_Airspeed.h:61`). -/
  _RASH : log_RASH := {}
  /-- `struct log_RASI _RASI[2]` of `AP_DAL_Airspeed` (`AP_DAL/AP_DAL_Airspeed.h:62`). -/
  _RASI : Array log_RASI := Array.replicate 2 {}
deriving Inhabited

end AP_DAL_Airspeed

namespace AP_DAL_GPS

/-- C++ `const Location & AP_DAL_GPS::location(uint8_t instance) const`, `AP_DAL/AP_DAL_GPS.h:18-20`. -/
def location_uint8_t (s : State) («instance» : UInt8) : Location.State := Id.run do
  return s.tmp_location[UInt8.toNat «instance»]!

/-- C++ `const Location & AP_DAL_GPS::location() const`, `AP_DAL/AP_DAL_GPS.h:100-102`. -/
def location_void (s : State) : Location.State := Id.run do
  return location_uint8_t s s._RGPH.primary_sensor

end AP_DAL_GPS

namespace AP_DAL

/-- C++ `void AP_DAL::init_sensors()`, `AP_DAL/AP_DAL.cpp:134-174`. -/
def init_sensors (s : State) : State := Id.run do
  let mut s := s
  s := { s with init_done := true }
  let alloc_failed : Bool := false
  if alloc_failed then
    pure ()  -- C++ `AP_BoardConfig::allocation_error(...)`: left out (--drop)
  return s

/-- C++ `enum class AP_DAL::FrameType`, `AP_DAL/AP_DAL.h:41-48`. -/
inductive FrameType where
  | InitialiseFilterEKF2
  | UpdateFilterEKF2
  | InitialiseFilterEKF3
  | UpdateFilterEKF3
  | LogWriteEKF2
  | LogWriteEKF3
deriving DecidableEq, Inhabited

/-- The value of each enumerator of `AP_DAL::FrameType` (underlying type `uint8_t`). -/
def FrameType.toInt : FrameType → UInt8
  | .InitialiseFilterEKF2 => (1 : UInt8)
  | .UpdateFilterEKF2 => (2 : UInt8)
  | .InitialiseFilterEKF3 => (4 : UInt8)
  | .UpdateFilterEKF3 => (8 : UInt8)
  | .LogWriteEKF2 => (16 : UInt8)
  | .LogWriteEKF3 => (32 : UInt8)

end AP_DAL

namespace AP_DAL_InertialSensor

/-- C++ `float AP_DAL_InertialSensor::get_loop_delta_t() const`, `AP_DAL/AP_DAL_InertialSensor.h:47`. -/
def get_loop_delta_t (s : State) : Binary32 := Id.run do
  return s._RISH.loop_delta_t

end AP_DAL_InertialSensor

namespace AP_DAL_InertialSensor

/-- C++ `void AP_DAL_InertialSensor::update_filtered(uint8_t i)`, `AP_DAL/AP_DAL_InertialSensor.cpp:68-82`. -/
def update_filtered (s : State) (i : UInt8) : State := Id.run do
  let mut s := s
  if !(Estimator_lib.is_positive_float s.alpha) then
    let cutoff_hz : Binary32 := (Binary32.ofBits 0x41200000 /- 10.0 -/)
    s := { s with alpha := Estimator_lib.calc_lowpass_alpha_dt (get_loop_delta_t s) cutoff_hz }
  if Estimator_lib.is_positive_float s._RISI[UInt8.toNat i]!.delta_angle_dt then
    let (t'1, _) := Vector3f.op_add_assign s.gyro_filtered[UInt8.toNat i]! (Vector3f.op_mul_float (Vector3f.op_sub_Vector3f (Vector3f.op_div s._RISI[UInt8.toNat i]!.delta_angle s._RISI[UInt8.toNat i]!.delta_angle_dt) s.gyro_filtered[UInt8.toNat i]!) s.alpha)
    s := { s with gyro_filtered := s.gyro_filtered.set! (UInt8.toNat i) t'1 }
  if Estimator_lib.is_positive_float s._RISI[UInt8.toNat i]!.delta_velocity_dt then
    let (t'3, _) := Vector3f.op_add_assign s.accel_filtered[UInt8.toNat i]! (Vector3f.op_mul_float (Vector3f.op_sub_Vector3f (Vector3f.op_div s._RISI[UInt8.toNat i]!.delta_velocity s._RISI[UInt8.toNat i]!.delta_velocity_dt) s.accel_filtered[UInt8.toNat i]!) s.alpha)
    s := { s with accel_filtered := s.accel_filtered.set! (UInt8.toNat i) t'3 }
  return s

end AP_DAL_InertialSensor

namespace AP_DAL_InertialSensor

/-- C++ `uint16_t AP_DAL_InertialSensor::get_loop_rate_hz() const`, `AP_DAL/AP_DAL_InertialSensor.h:13`. -/
def get_loop_rate_hz (s : State) : UInt16 := Id.run do
  return s._RISH.loop_rate_hz

/-- C++ `uint8_t AP_DAL_InertialSensor::get_accel_count() const`, `AP_DAL/AP_DAL_InertialSensor.h:20`. -/
def get_accel_count (s : State) : UInt8 := Id.run do
  return s._RISH.accel_count

end AP_DAL_InertialSensor

namespace AP_DAL_Airspeed

/-- C++ `uint8_t AP_DAL_Airspeed::get_num_sensors() const`, `AP_DAL/AP_DAL_Airspeed.h:42`. -/
def get_num_sensors (s : State) : UInt8 := Id.run do
  return s._RASH.num_sensors

end AP_DAL_Airspeed

namespace AP_DAL_GPS

/-- C++ `bool AP_DAL_GPS::get_lag(uint8_t instance, float & lag_sec) const`, `AP_DAL/AP_DAL_GPS.h:61-64`. -/
def get_lag_uint8_t_float (s : State) («instance» : UInt8) (lag_sec : Binary32) : Binary32 × Bool := Id.run do
  let mut lag_sec := lag_sec
  lag_sec := s._RGPI[UInt8.toNat «instance»]!.lag_sec
  return (lag_sec, s._RGPI[UInt8.toNat «instance»]!.get_lag_returncode != (0 : UInt8))

end AP_DAL_GPS

namespace AP_DAL_Compass

/-- C++ `uint8_t AP_DAL_Compass::get_num_enabled() const`, `AP_DAL/AP_DAL_Compass.h:44`. -/
def get_num_enabled (s : State) : UInt8 := Id.run do
  return s._RMGH.num_enabled

end AP_DAL_Compass

namespace AP_DAL_GPS

/-- C++ `AP_GPS_FixType AP_DAL_GPS::status(uint8_t sensor_id) const`, `AP_DAL/AP_DAL_GPS.h:12-14`. -/
def status_uint8_t (s : State) (sensor_id : UInt8) : AP_GPS_FixType := Id.run do
  return AP_GPS_FixType.ofInt s._RGPI[UInt8.toNat sensor_id]!.status

end AP_DAL_GPS

namespace AP_DAL_GPS

/-- C++ `uint8_t AP_DAL_GPS::primary_sensor() const`, `AP_DAL/AP_DAL_GPS.h:95-97`. -/
def primary_sensor (s : State) : UInt8 := Id.run do
  return s._RGPH.primary_sensor

/-- C++ `uint8_t AP_DAL_GPS::num_sensors() const`, `AP_DAL/AP_DAL_GPS.h:91-93`. -/
def num_sensors (s : State) : UInt8 := Id.run do
  return s._RGPH.num_sensors

end AP_DAL_GPS

namespace AP_DAL

/-- C++ `bool AP_DAL::get_armed() const`, `AP_DAL/AP_DAL.h:125`. -/
def get_armed (s : State) : Bool := Id.run do
  return s._RFRN.armed != (0 : UInt8)

end AP_DAL

namespace AP_DAL_Compass

/-- C++ `uint8_t AP_DAL_Compass::get_count() const`, `AP_DAL/AP_DAL_Compass.h:31-33`. -/
def get_count (s : State) : UInt8 := Id.run do
  return s._RMGH.count

/-- C++ `bool AP_DAL_Compass::healthy(uint8_t i) const`, `AP_DAL/AP_DAL_Compass.h:15-17`. -/
def healthy (s : State) (i : UInt8) : Bool := Id.run do
  return s._RMGI[UInt8.toNat i]!.healthy

/-- C++ `bool AP_DAL_Compass::use_for_yaw(uint8_t i) const`, `AP_DAL/AP_DAL_Compass.h:11-13`. -/
def use_for_yaw (s : State) (i : UInt8) : Bool := Id.run do
  return s._RMGI[UInt8.toNat i]!.use_for_yaw

/-- C++ `uint8_t AP_DAL_Compass::get_first_usable() const`, `AP_DAL/AP_DAL_Compass.h:59`. -/
def get_first_usable (s : State) : UInt8 := Id.run do
  return s._RMGH.first_usable

end AP_DAL_Compass

namespace AP_DAL_Baro

/-- C++ `uint8_t AP_DAL_Baro::get_primary() const`, `AP_DAL/AP_DAL_Baro.h:10-12`. -/
def get_primary (s : State) : UInt8 := Id.run do
  return s._RBRH.primary

/-- C++ `uint8_t AP_DAL_Baro::num_instances() const`, `AP_DAL/AP_DAL_Baro.h:13-15`. -/
def num_instances (s : State) : UInt8 := Id.run do
  return s._RBRH.num_instances

/-- C++ `bool AP_DAL_Baro::healthy(uint8_t sensor_id) const`, `AP_DAL/AP_DAL_Baro.h:16-18`. -/
def healthy (s : State) (sensor_id : UInt8) : Bool := Id.run do
  return s._RBRI[UInt8.toNat sensor_id]!.healthy

end AP_DAL_Baro

namespace AP_DAL_Airspeed

/-- C++ `uint8_t AP_DAL_Airspeed::get_primary() const`, `AP_DAL/AP_DAL_Airspeed.h:45`. -/
def get_primary (s : State) : UInt8 := Id.run do
  return s._RASH.primary

/-- C++ `bool AP_DAL_Airspeed::healthy(uint8_t i) const`, `AP_DAL/AP_DAL_Airspeed.h:13-15`. -/
def healthy_uint8_t (s : State) (i : UInt8) : Bool := Id.run do
  return s._RASI[UInt8.toNat i]!.healthy

/-- C++ `bool AP_DAL_Airspeed::use(uint8_t i) const`, `AP_DAL/AP_DAL_Airspeed.h:22-24`. -/
def use_uint8_t (s : State) (i : UInt8) : Bool := Id.run do
  return s._RASI[UInt8.toNat i]!.use

end AP_DAL_Airspeed

namespace AP_DAL

/-- C++ `bool AP_DAL::get_fly_forward() const`, `AP_DAL/AP_DAL.h:189-191`. -/
def get_fly_forward (s : State) : Bool := Id.run do
  return s._RFRN.fly_forward != (0 : UInt8)

/-- C++ `enum class AP_DAL::VehicleClass`, `AP_DAL/AP_DAL.h:70-76`. -/
inductive VehicleClass where
  | UNKNOWN
  | GROUND
  | COPTER
  | FIXED_WING
  | SUBMARINE
deriving DecidableEq, Inhabited

/-- The value of each enumerator of `AP_DAL::VehicleClass` (underlying type `uint8_t`). -/
def VehicleClass.toInt : VehicleClass → UInt8
  | .UNKNOWN => (0 : UInt8)
  | .GROUND => (1 : UInt8)
  | .COPTER => (2 : UInt8)
  | .FIXED_WING => (3 : UInt8)
  | .SUBMARINE => (4 : UInt8)

/-- The enumerator of `AP_DAL::VehicleClass` with value `v` (the C++ converts only enumerator values; any other
value gives the first enumerator, the `Inhabited` default). -/
def VehicleClass.ofInt (v : UInt8) : VehicleClass :=
  if v == (0 : UInt8) then .UNKNOWN
  else if v == (1 : UInt8) then .GROUND
  else if v == (2 : UInt8) then .COPTER
  else if v == (3 : UInt8) then .FIXED_WING
  else if v == (4 : UInt8) then .SUBMARINE
  else default

/-- C++ `VehicleClass AP_DAL::get_vehicle_class() const`, `AP_DAL/AP_DAL.h:185-187`. -/
def get_vehicle_class (s : State) : AP_DAL.VehicleClass := Id.run do
  return AP_DAL.VehicleClass.ofInt s._RFRN.vehicle_class

end AP_DAL

namespace AP_DAL_InertialSensor

/-- C++ `bool AP_DAL_InertialSensor::use_accel(uint8_t instance) const`, `AP_DAL/AP_DAL_InertialSensor.h:23`. -/
def use_accel (s : State) («instance» : UInt8) : Bool := Id.run do
  return s._RISI[UInt8.toNat «instance»]!.use_accel != (0 : UInt8)

/-- C++ `uint8_t AP_DAL_InertialSensor::get_first_usable_accel() const`, `AP_DAL/AP_DAL_InertialSensor.h:21`. -/
def get_first_usable_accel (s : State) : UInt8 := Id.run do
  return s._RISH.first_usable_accel

/-- C++ `bool AP_DAL_InertialSensor::use_gyro(uint8_t instance) const`, `AP_DAL/AP_DAL_InertialSensor.h:35`. -/
def use_gyro (s : State) («instance» : UInt8) : Bool := Id.run do
  return s._RISI[UInt8.toNat «instance»]!.use_gyro != (0 : UInt8)

/-- C++ `uint8_t AP_DAL_InertialSensor::get_first_usable_gyro() const`, `AP_DAL/AP_DAL_InertialSensor.h:33`. -/
def get_first_usable_gyro (s : State) : UInt8 := Id.run do
  return s._RISH.first_usable_gyro

end AP_DAL_InertialSensor

namespace AP_DAL_InertialSensor

/-- C++ `bool AP_DAL_InertialSensor::get_delta_velocity(uint8_t i, Vector3f & delta_velocity, float & delta_velocity_dt) const`, `AP_DAL/AP_DAL_InertialSensor.h:25-29`. -/
def get_delta_velocity (s : State) (i : UInt8) (delta_velocity : Vector3f.State) (delta_velocity_dt : Binary32) : Vector3f.State × Binary32 × Bool := Id.run do
  let mut delta_velocity := delta_velocity
  let mut delta_velocity_dt := delta_velocity_dt
  delta_velocity := s._RISI[UInt8.toNat i]!.delta_velocity
  delta_velocity_dt := s._RISI[UInt8.toNat i]!.delta_velocity_dt
  return (delta_velocity, delta_velocity_dt, s._RISI[UInt8.toNat i]!.get_delta_velocity_ret != (0 : UInt8))

end AP_DAL_InertialSensor

namespace AP_DAL_InertialSensor

/-- C++ `uint8_t AP_DAL_InertialSensor::get_gyro_count() const`, `AP_DAL/AP_DAL_InertialSensor.h:32`. -/
def get_gyro_count (s : State) : UInt8 := Id.run do
  return s._RISH.gyro_count

/-- C++ `bool AP_DAL_InertialSensor::get_delta_angle(uint8_t i, Vector3f & delta_angle, float & delta_angle_dt) const`, `AP_DAL/AP_DAL_InertialSensor.h:40-44`. -/
def get_delta_angle (s : State) (i : UInt8) (delta_angle : Vector3f.State) (delta_angle_dt : Binary32) : Vector3f.State × Binary32 × Bool := Id.run do
  let mut delta_angle := delta_angle
  let mut delta_angle_dt := delta_angle_dt
  delta_angle := s._RISI[UInt8.toNat i]!.delta_angle
  delta_angle_dt := s._RISI[UInt8.toNat i]!.delta_angle_dt
  return (delta_angle, delta_angle_dt, s._RISI[UInt8.toNat i]!.get_delta_angle_ret != (0 : UInt8))

end AP_DAL_InertialSensor

namespace AP_DAL_Compass

/-- C++ `bool AP_DAL_Compass::available() const`, `AP_DAL/AP_DAL_Compass.h:39-41`. -/
def available (s : State) : Bool := Id.run do
  return s._RMGH.available

/-- C++ `bool AP_DAL_Compass::learn_offsets_enabled() const`, `AP_DAL/AP_DAL_Compass.h:47`. -/
def learn_offsets_enabled (s : State) : Bool := Id.run do
  return s._RMGH.learn_offsets_enabled

/-- C++ `uint32_t AP_DAL_Compass::last_update_usec(uint8_t i) const`, `AP_DAL/AP_DAL_Compass.h:50`. -/
def last_update_usec (s : State) (i : UInt8) : UInt32 := Id.run do
  return s._RMGI[UInt8.toNat i]!.last_update_usec

/-- C++ `bool AP_DAL_Compass::consistent() const`, `AP_DAL/AP_DAL_Compass.h:56`. -/
def consistent (s : State) : Bool := Id.run do
  return s._RMGH.consistent

end AP_DAL_Compass

namespace AP_DAL_Compass

/-- C++ `float AP_DAL_Compass::get_declination() const`, `AP_DAL/AP_DAL_Compass.h:35-37`. -/
def get_declination (s : State) : Binary32 := Id.run do
  return s._RMGH.declination

end AP_DAL_Compass

namespace AP_DAL_Compass

/-- C++ `bool AP_DAL_Compass::have_scale_factor(uint8_t i) const`, `AP_DAL/AP_DAL_Compass.h:23-25`. -/
def have_scale_factor (s : State) (i : UInt8) : Bool := Id.run do
  return s._RMGI[UInt8.toNat i]!.have_scale_factor

/-- C++ `bool AP_DAL_Compass::auto_declination_enabled() const`, `AP_DAL/AP_DAL_Compass.h:27-29`. -/
def auto_declination_enabled (s : State) : Bool := Id.run do
  return s._RMGH.auto_declination_enabled

end AP_DAL_Compass

namespace AP_DAL_GPS

/-- C++ `uint32_t AP_DAL_GPS::last_message_time_ms(uint8_t instance) const`, `AP_DAL/AP_DAL_GPS.h:50-52`. -/
def last_message_time_ms (s : State) («instance» : UInt8) : UInt32 := Id.run do
  return s._RGPJ[UInt8.toNat «instance»]!.last_message_time_ms

/-- C++ `bool AP_DAL_GPS::have_vertical_velocity(uint8_t instance) const`, `AP_DAL/AP_DAL_GPS.h:21-23`. -/
def have_vertical_velocity_uint8_t (s : State) («instance» : UInt8) : Bool := Id.run do
  return s._RGPI[UInt8.toNat «instance»]!.have_vertical_velocity != (0 : UInt8)

/-- C++ `bool AP_DAL_GPS::speed_accuracy(uint8_t instance, float & sacc) const`, `AP_DAL/AP_DAL_GPS.h:76-79`. -/
def speed_accuracy_uint8_t_float (s : State) («instance» : UInt8) (sacc : Binary32) : Binary32 × Bool := Id.run do
  let mut sacc := sacc
  sacc := s._RGPJ[UInt8.toNat «instance»]!.sacc
  return (sacc, s._RGPI[UInt8.toNat «instance»]!.speed_accuracy_returncode != (0 : UInt8))

/-- C++ `bool AP_DAL_GPS::horizontal_accuracy(uint8_t instance, float & hacc) const`, `AP_DAL/AP_DAL_GPS.h:27-30`. -/
def horizontal_accuracy_uint8_t_float (s : State) («instance» : UInt8) (hacc : Binary32) : Binary32 × Bool := Id.run do
  let mut hacc := hacc
  hacc := s._RGPJ[UInt8.toNat «instance»]!.hacc
  return (hacc, s._RGPI[UInt8.toNat «instance»]!.horizontal_accuracy_returncode != (0 : UInt8))

/-- C++ `bool AP_DAL_GPS::vertical_accuracy(uint8_t instance, float & vacc) const`, `AP_DAL/AP_DAL_GPS.h:35-38`. -/
def vertical_accuracy_uint8_t_float (s : State) («instance» : UInt8) (vacc : Binary32) : Binary32 × Bool := Id.run do
  let mut vacc := vacc
  vacc := s._RGPJ[UInt8.toNat «instance»]!.vacc
  return (vacc, s._RGPI[UInt8.toNat «instance»]!.vertical_accuracy_returncode != (0 : UInt8))

/-- C++ `uint8_t AP_DAL_GPS::num_sats(uint8_t instance) const`, `AP_DAL/AP_DAL_GPS.h:54-56`. -/
def num_sats_uint8_t (s : State) («instance» : UInt8) : UInt8 := Id.run do
  return s._RGPI[UInt8.toNat «instance»]!.num_sats

end AP_DAL_GPS

namespace AP_DAL_GPS

/-- C++ `uint16_t AP_DAL_GPS::get_hdop(uint8_t instance) const`, `AP_DAL/AP_DAL_GPS.h:43-45`. -/
def get_hdop_uint8_t (s : State) («instance» : UInt8) : UInt16 := Id.run do
  return s._RGPJ[UInt8.toNat «instance»]!.hdop

end AP_DAL_GPS

namespace AP_DAL_GPS

/-- C++ `bool AP_DAL_GPS::gps_yaw_deg(uint8_t instance, float & yaw_deg, float & accuracy_deg, uint32_t & time_ms) const`, `AP_DAL/AP_DAL_GPS.h:84-89`. -/
def gps_yaw_deg (s : State) («instance» : UInt8) (yaw_deg : Binary32) (accuracy_deg : Binary32) (time_ms : UInt32) : Binary32 × Binary32 × UInt32 × Bool := Id.run do
  let mut yaw_deg := yaw_deg
  let mut accuracy_deg := accuracy_deg
  let mut time_ms := time_ms
  yaw_deg := s._RGPJ[UInt8.toNat «instance»]!.yaw_deg
  accuracy_deg := s._RGPJ[UInt8.toNat «instance»]!.yaw_accuracy_deg
  time_ms := s._RGPJ[UInt8.toNat «instance»]!.yaw_deg_time_ms
  return (yaw_deg, accuracy_deg, time_ms, s._RGPI[UInt8.toNat «instance»]!.gps_yaw_deg_returncode != (0 : UInt8))

end AP_DAL_GPS

namespace AP_DAL_Baro

/-- C++ `uint32_t AP_DAL_Baro::get_last_update(uint8_t sensor_id) const`, `AP_DAL/AP_DAL_Baro.h:19-21`. -/
def get_last_update_uint8_t (s : State) (sensor_id : UInt8) : UInt32 := Id.run do
  return s._RBRI[UInt8.toNat sensor_id]!.last_update_ms

/-- C++ `float AP_DAL_Baro::get_altitude(uint8_t sensor_id) const`, `AP_DAL/AP_DAL_Baro.h:25-27`. -/
def get_altitude_uint8_t (s : State) (sensor_id : UInt8) : Binary32 := Id.run do
  return s._RBRI[UInt8.toNat sensor_id]!.altitude

end AP_DAL_Baro

namespace AP_DAL_InertialSensor

/-- C++ `float AP_DAL_InertialSensor::get_gyro_bias_init_dps(uint8_t instance) const`, `AP_DAL/AP_DAL_InertialSensor.h:37`. -/
def get_gyro_bias_init_dps (s : State) («instance» : UInt8) : Binary32 := Id.run do
  return s._RISJ[UInt8.toNat «instance»]!.gyro_bias_init_dps

end AP_DAL_InertialSensor

/-- C++ `struct log_RSO2`, `AP_DAL/LogStructure.h:184-189`. -/
structure log_RSO2 where
  /-- `int32_t lat` of `log_RSO2` (`AP_DAL/LogStructure.h:185`). -/
  lat : Int32 := (0 : Int32)
  /-- `int32_t lng` of `log_RSO2` (`AP_DAL/LogStructure.h:186`). -/
  lng : Int32 := (0 : Int32)
  /-- `int32_t alt` of `log_RSO2` (`AP_DAL/LogStructure.h:187`). -/
  alt : Int32 := (0 : Int32)
  /-- `uint8_t _end` of `log_RSO2` (`AP_DAL/LogStructure.h:188`). -/
  _end : UInt8 := (0 : UInt8)
deriving Inhabited

namespace AP_DAL

/-- C++ `void AP_DAL::log_SetOriginLLH3(const Location & loc)`, `AP_DAL/AP_DAL.cpp:234-245`. -/
def log_SetOriginLLH3 (s : State) (loc : Location.State) : State := Id.run do
  let mut s := s
  s := end_frame s
  let pkt : log_RSO2 := { lat := loc.lat, lng := loc.lng, alt := loc.alt, _end := (0 : UInt8) }
  for _ in [0:1] do
    pure ()
  return s

end AP_DAL

namespace AP_DAL

/-- C++ `float AP_DAL::get_EAS2TAS() const`, `AP_DAL/AP_DAL.h:181-183`. -/
def get_EAS2TAS (s : State) : Binary32 := Id.run do
  return s._RFRN.EAS2TAS

/-- C++ `bool AP_DAL::get_takeoff_expected() const`, `AP_DAL/AP_DAL.h:193-195`. -/
def get_takeoff_expected (s : State) : Bool := Id.run do
  return s._RFRN.takeoff_expected != (0 : UInt8)

/-- C++ `uint32_t AP_DAL::get_time_flying_ms() const`, `AP_DAL/AP_DAL.h:219-221`. -/
def get_time_flying_ms (s : State) : UInt32 := Id.run do
  return s._RFRH.time_flying_ms

end AP_DAL

namespace AP_DAL_Airspeed

/-- C++ `float AP_DAL_Airspeed::get_airspeed(uint8_t i) const`, `AP_DAL/AP_DAL_Airspeed.h:30-32`. -/
def get_airspeed_uint8_t (s : State) (i : UInt8) : Binary32 := Id.run do
  return s._RASI[UInt8.toNat i]!.airspeed

end AP_DAL_Airspeed

namespace AP_DAL_InertialSensor

/-- C++ `float AP_DAL_InertialSensor::get_gyro_bias_limit(uint8_t instance) const`, `AP_DAL/AP_DAL_InertialSensor.h:36`. -/
def get_gyro_bias_limit (s : State) («instance» : UInt8) : Binary32 := Id.run do
  return s._RISJ[UInt8.toNat «instance»]!.gyro_bias_limit

end AP_DAL_InertialSensor

namespace AP_DAL

/-- C++ `bool AP_DAL::get_touchdown_expected() const`, `AP_DAL/AP_DAL.h:197-199`. -/
def get_touchdown_expected (s : State) : Bool := Id.run do
  return s._RFRN.touchdown_expected != (0 : UInt8)

end AP_DAL

namespace AP_DAL_Airspeed

/-- C++ `uint32_t AP_DAL_Airspeed::last_update_ms(uint8_t i) const`, `AP_DAL/AP_DAL_Airspeed.h:38`. -/
def last_update_ms_uint8_t (s : State) (i : UInt8) : UInt32 := Id.run do
  return s._RASI[UInt8.toNat i]!.last_update_ms

end AP_DAL_Airspeed

namespace AP_DAL

/-- C++ `const Matrix3f & AP_DAL::get_rotation_vehicle_body_to_autopilot_body() const`, `AP_DAL/AP_DAL.h:209-211`. -/
def get_rotation_vehicle_body_to_autopilot_body (s : State) : Matrix3f.State := Id.run do
  return s._rotation_vehicle_body_to_autopilot_body

end AP_DAL

namespace AP_DAL

/-- C++ `const Vector3f & AP_DAL::get_trim() const`, `AP_DAL/AP_DAL.h:205-207`. -/
def get_trim (s : State) : Vector3f.State := Id.run do
  return s._RFRN.ahrs_trim

end AP_DAL

namespace AP_DAL

/-- C++ `bool AP_DAL::wheelencoder_enabled() const`, `AP_DAL/AP_DAL.h:227-229`. -/
def wheelencoder_enabled (s : State) : Bool := Id.run do
  return s._RFRN.wheelencoder_enabled != (0 : UInt8)

end AP_DAL

namespace AP_DAL

/-- C++ `enum class AP_DAL::RFRNFlags`, `AP_DAL/AP_DAL.h:104-113`. -/
inductive RFRNFlags where
  | ARMED
  | UNUSED
  | FLY_FORWARD
  | AHRS_AIRSPEED_SENSOR_ENABLED_UNUSED
  | OPTICALFLOW_ENABLED
  | WHEELENCODER_ENABLED
  | TAKEOFF_EXPECTED
  | TOUCHDOWN_EXPECTED
deriving DecidableEq, Inhabited

/-- The value of each enumerator of `AP_DAL::RFRNFlags` (underlying type `int32_t`). -/
def RFRNFlags.toInt : RFRNFlags → Int32
  | .ARMED => (1 : Int32)
  | .UNUSED => (2 : Int32)
  | .FLY_FORWARD => (4 : Int32)
  | .AHRS_AIRSPEED_SENSOR_ENABLED_UNUSED => (8 : Int32)
  | .OPTICALFLOW_ENABLED => (16 : Int32)
  | .WHEELENCODER_ENABLED => (32 : Int32)
  | .TAKEOFF_EXPECTED => (64 : Int32)
  | .TOUCHDOWN_EXPECTED => (128 : Int32)

/-- C++ `enum class AP_DAL::MemoryType`, `AP_DAL/AP_DAL.h:145-148`. -/
inductive MemoryType where
  | DMA_SAFE
  | FAST
deriving DecidableEq, Inhabited

/-- The value of each enumerator of `AP_DAL::MemoryType` (underlying type `uint8_t`). -/
def MemoryType.toInt : MemoryType → UInt8
  | .DMA_SAFE => (0 : UInt8)
  | .FAST => (1 : UInt8)

end AP_DAL

namespace AP_DAL_Airspeed

/-! Not emitted, since they have no effect in the model (they write neither the state, the
parameters nor a reference parameter; e.g. they only save parameters):
- C++ `void AP_DAL_Airspeed::start_frame()`, `AP_DAL/AP_DAL_Airspeed.cpp:15-35`.
-/

end AP_DAL_Airspeed

namespace AP_DAL_Compass

/-- C++ `const Vector3f & AP_DAL_Compass::get_offsets(uint8_t i) const`, `AP_DAL/AP_DAL_Compass.h:19-21`. -/
def get_offsets (s : State) (i : UInt8) : Vector3f.State := Id.run do
  return s._RMGI[UInt8.toNat i]!.offsets

end AP_DAL_Compass

/-- C++ `struct log_RWA2`, `AP_DAL/LogStructure.h:195-199`. -/
structure log_RWA2 where
  /-- `float airspeed` of `log_RWA2` (`AP_DAL/LogStructure.h:196`). -/
  airspeed : Binary32 := (Binary32.ofBits 0x00000000 /- 0.0 -/)
  /-- `float uncertainty` of `log_RWA2` (`AP_DAL/LogStructure.h:197`). -/
  uncertainty : Binary32 := (Binary32.ofBits 0x00000000 /- 0.0 -/)
  /-- `uint8_t _end` of `log_RWA2` (`AP_DAL/LogStructure.h:198`). -/
  _end : UInt8 := (0 : UInt8)
deriving Inhabited

/-- C++ `struct log_REY3`, `AP_DAL/LogStructure.h:227-233`. -/
structure log_REY3 where
  /-- `float yawangle` of `log_REY3` (`AP_DAL/LogStructure.h:228`). -/
  yawangle : Binary32 := (Binary32.ofBits 0x00000000 /- 0.0 -/)
  /-- `float yawangleerr` of `log_REY3` (`AP_DAL/LogStructure.h:229`). -/
  yawangleerr : Binary32 := (Binary32.ofBits 0x00000000 /- 0.0 -/)
  /-- `uint32_t timestamp_ms` of `log_REY3` (`AP_DAL/LogStructure.h:230`). -/
  timestamp_ms : UInt32 := (0 : UInt32)
  /-- `uint8_t type` of `log_REY3` (`AP_DAL/LogStructure.h:231`). -/
  type : UInt8 := (0 : UInt8)
  /-- `uint8_t _end` of `log_REY3` (`AP_DAL/LogStructure.h:232`). -/
  _end : UInt8 := (0 : UInt8)
deriving Inhabited

/-- C++ `struct log_RRNH`, `AP_DAL/LogStructure.h:264-270`. -/
structure log_RRNH where
  /-- `float ground_clearance` of `log_RRNH` (`AP_DAL/LogStructure.h:266`). -/
  ground_clearance : Binary32 := (Binary32.ofBits 0x00000000 /- 0.0 -/)
  /-- `float max_distance` of `log_RRNH` (`AP_DAL/LogStructure.h:267`). -/
  max_distance : Binary32 := (Binary32.ofBits 0x00000000 /- 0.0 -/)
  /-- `uint8_t num_sensors` of `log_RRNH` (`AP_DAL/LogStructure.h:268`). -/
  num_sensors : UInt8 := (0 : UInt8)
  /-- `uint8_t _end` of `log_RRNH` (`AP_DAL/LogStructure.h:269`). -/
  _end : UInt8 := (0 : UInt8)
deriving Inhabited

/-- C++ `struct log_RRNI`, `AP_DAL/LogStructure.h:281-288`. -/
structure log_RRNI where
  /-- `Vector3f pos_offset` of `log_RRNI` (`AP_DAL/LogStructure.h:282`). -/
  pos_offset : Vector3f.State := {}
  /-- `float distance` of `log_RRNI` (`AP_DAL/LogStructure.h:283`). -/
  distance : Binary32 := (Binary32.ofBits 0x00000000 /- 0.0 -/)
  /-- `uint8_t orientation` of `log_RRNI` (`AP_DAL/LogStructure.h:284`). -/
  orientation : UInt8 := (0 : UInt8)
  /-- `uint8_t status` of `log_RRNI` (`AP_DAL/LogStructure.h:285`). -/
  status : UInt8 := (0 : UInt8)
  /-- `uint8_t instance` of `log_RRNI` (`AP_DAL/LogStructure.h:286`). -/
  «instance» : UInt8 := (0 : UInt8)
  /-- `uint8_t _end` of `log_RRNI` (`AP_DAL/LogStructure.h:287`). -/
  _end : UInt8 := (0 : UInt8)
deriving Inhabited

/-- C++ `struct log_RBCH`, `AP_DAL/LogStructure.h:457-468`. -/
structure log_RBCH where
  /-- `Vector3f vehicle_position_ned` of `log_RBCH` (`AP_DAL/LogStructure.h:458`). -/
  vehicle_position_ned : Vector3f.State := {}
  /-- `float accuracy_estimate` of `log_RBCH` (`AP_DAL/LogStructure.h:459`). -/
  accuracy_estimate : Binary32 := (Binary32.ofBits 0x00000000 /- 0.0 -/)
  /-- `int32_t origin_lat` of `log_RBCH` (`AP_DAL/LogStructure.h:460`). -/
  origin_lat : Int32 := (0 : Int32)
  /-- `int32_t origin_lng` of `log_RBCH` (`AP_DAL/LogStructure.h:461`). -/
  origin_lng : Int32 := (0 : Int32)
  /-- `int32_t origin_alt` of `log_RBCH` (`AP_DAL/LogStructure.h:462`). -/
  origin_alt : Int32 := (0 : Int32)
  /-- `uint8_t get_vehicle_position_ned_returncode : 1` of `log_RBCH` (`AP_DAL/LogStructure.h:463`). -/
  get_vehicle_position_ned_returncode : UInt8 := (0 : UInt8)
  /-- `uint8_t get_origin_returncode : 1` of `log_RBCH` (`AP_DAL/LogStructure.h:464`). -/
  get_origin_returncode : UInt8 := (0 : UInt8)
  /-- `uint8_t enabled : 1` of `log_RBCH` (`AP_DAL/LogStructure.h:465`). -/
  enabled : UInt8 := (0 : UInt8)
  /-- `uint8_t count` of `log_RBCH` (`AP_DAL/LogStructure.h:466`). -/
  count : UInt8 := (0 : UInt8)
  /-- `uint8_t _end` of `log_RBCH` (`AP_DAL/LogStructure.h:467`). -/
  _end : UInt8 := (0 : UInt8)
deriving Inhabited

/-- C++ `struct log_RBCI`, `AP_DAL/LogStructure.h:479-486`. -/
structure log_RBCI where
  /-- `uint32_t last_update_ms` of `log_RBCI` (`AP_DAL/LogStructure.h:480`). -/
  last_update_ms : UInt32 := (0 : UInt32)
  /-- `Vector3f position` of `log_RBCI` (`AP_DAL/LogStructure.h:481`). -/
  position : Vector3f.State := {}
  /-- `float distance` of `log_RBCI` (`AP_DAL/LogStructure.h:482`). -/
  distance : Binary32 := (Binary32.ofBits 0x00000000 /- 0.0 -/)
  /-- `uint8_t healthy` of `log_RBCI` (`AP_DAL/LogStructure.h:483`). -/
  healthy : UInt8 := (0 : UInt8)
  /-- `uint8_t instance` of `log_RBCI` (`AP_DAL/LogStructure.h:484`). -/
  «instance» : UInt8 := (0 : UInt8)
  /-- `uint8_t _end` of `log_RBCI` (`AP_DAL/LogStructure.h:485`). -/
  _end : UInt8 := (0 : UInt8)
deriving Inhabited

/-- C++ `struct log_RVOH`, `AP_DAL/LogStructure.h:496-502`. -/
structure log_RVOH where
  /-- `Vector3f pos_offset` of `log_RVOH` (`AP_DAL/LogStructure.h:497`). -/
  pos_offset : Vector3f.State := {}
  /-- `uint32_t delay_ms` of `log_RVOH` (`AP_DAL/LogStructure.h:498`). -/
  delay_ms : UInt32 := (0 : UInt32)
  /-- `uint8_t healthy` of `log_RVOH` (`AP_DAL/LogStructure.h:499`). -/
  healthy : UInt8 := (0 : UInt8)
  /-- `bool enabled` of `log_RVOH` (`AP_DAL/LogStructure.h:500`). -/
  enabled : Bool := false
  /-- `uint8_t _end` of `log_RVOH` (`AP_DAL/LogStructure.h:501`). -/
  _end : UInt8 := (0 : UInt8)
deriving Inhabited

end Estimator_lib
