import ArduLean.Musl.atan2
import ArduLean.Musl.cos
import ArduLean.Musl.expf
import ArduLean.Musl.sin
import ArduLean.Estimator.libraries.AP_Math.AP_Math
import ArduLean.Estimator.libraries.AP_Param.AP_Param

/-!
ArduPilot `libraries/AP_NavEKF`, part 1 of 3. Sources: `libraries/AP_NavEKF/EKFGSF_yaw.cpp`, `libraries/AP_NavEKF/AP_NavEKF_Source.h`, `libraries/AP_NavEKF/AP_Nav_Common.h`, `libraries/AP_NavEKF/EKFGSF_yaw.h`, `libraries/AP_NavEKF/LogStructure.h`, `libraries/AP_NavEKF/AP_NavEKF_Source.cpp`, `libraries/AP_NavEKF/AP_NavEKF_core_common.h`, `libraries/AP_NavEKF/EKF_Buffer.h`.

Items of `lean/Estimator_lib.lean` (the estimator translation), unchanged; placed by `tools/split_modules.py` (`ArduLean/Estimator/INDEX.md`).
-/

open FloatLib.Floats (Binary32 Binary64)

set_option maxRecDepth 200000
-- AP_DAL's `const log_RISH old_RISH = _RISH;` read only by WRITE_REPLAY_BLOCK_IFCHANGED, which is `(void)old`
-- without logging (HAL_LOGGING_ENABLED 0): an unused binding, as in the C++
set_option linter.unusedVariables false

namespace Estimator_lib

namespace AP_NavEKF_Source

/-- C++ `struct AP_NavEKF_Source::SourceSet`, `AP_NavEKF/AP_NavEKF_Source.h:135-141`. -/
structure SourceSet where
  /-- `AP_Enum<SourceXY> posxy` of `AP_NavEKF_Source::SourceSet` (`AP_NavEKF/AP_NavEKF_Source.h:136`). -/
  posxy : AP_Enum_AP_NavEKF_Source_SourceXY.State := {}
  /-- `AP_Enum<SourceXY> velxy` of `AP_NavEKF_Source::SourceSet` (`AP_NavEKF/AP_NavEKF_Source.h:137`). -/
  velxy : AP_Enum_AP_NavEKF_Source_SourceXY.State := {}
  /-- `AP_Enum<SourceZ> posz` of `AP_NavEKF_Source::SourceSet` (`AP_NavEKF/AP_NavEKF_Source.h:138`). -/
  posz : AP_Enum_AP_NavEKF_Source_SourceZ.State := {}
  /-- `AP_Enum<SourceZ> velz` of `AP_NavEKF_Source::SourceSet` (`AP_NavEKF/AP_NavEKF_Source.h:139`). -/
  velz : AP_Enum_AP_NavEKF_Source_SourceZ.State := {}
  /-- `AP_Enum<SourceYaw> yaw` of `AP_NavEKF_Source::SourceSet` (`AP_NavEKF/AP_NavEKF_Source.h:140`). -/
  yaw : AP_Enum_AP_NavEKF_Source_SourceYaw.State := {}
deriving Inhabited

/-- State of C++ `AP_NavEKF_Source` (`AP_NavEKF/AP_NavEKF_Source.h:7-150`): its data members. -/
structure State where
  /-- `struct SourceSet _source_set[3]` of `AP_NavEKF_Source` (`AP_NavEKF/AP_NavEKF_Source.h:141`). -/
  _source_set : Array AP_NavEKF_Source.SourceSet := Array.replicate 3 {}
  /-- `AP_UInt16 _options` of `AP_NavEKF_Source` (`AP_NavEKF/AP_NavEKF_Source.h:146`). -/
  _options : AP_ParamT_unsigned_short_2.State := {}
  /-- `uint8_t active_source_set` of `AP_NavEKF_Source` (`AP_NavEKF/AP_NavEKF_Source.h:148`). -/
  active_source_set : UInt8 := (0 : UInt8)
  /-- `bool _configured` of `AP_NavEKF_Source` (`AP_NavEKF/AP_NavEKF_Source.h:149`). -/
  _configured : Bool := false
deriving Inhabited

/-- C++ `enum class AP_NavEKF_Source::SourceXY`, `AP_NavEKF/AP_NavEKF_Source.h:17-26`. -/
inductive SourceXY where
  | NONE
  | GPS
  | BEACON
  | OPTFLOW
  | EXTNAV
  | WHEEL_ENCODER
deriving DecidableEq, Inhabited

/-- The value of each enumerator of `AP_NavEKF_Source::SourceXY` (underlying type `uint8_t`). -/
def SourceXY.toInt : SourceXY → UInt8
  | .NONE => (0 : UInt8)
  | .GPS => (3 : UInt8)
  | .BEACON => (4 : UInt8)
  | .OPTFLOW => (5 : UInt8)
  | .EXTNAV => (6 : UInt8)
  | .WHEEL_ENCODER => (7 : UInt8)

/-- The enumerator of `AP_NavEKF_Source::SourceXY` with value `v` (the C++ converts only enumerator values; any other
value gives the first enumerator, the `Inhabited` default). -/
def SourceXY.ofInt (v : UInt8) : SourceXY :=
  if v == (0 : UInt8) then .NONE
  else if v == (3 : UInt8) then .GPS
  else if v == (4 : UInt8) then .BEACON
  else if v == (5 : UInt8) then .OPTFLOW
  else if v == (6 : UInt8) then .EXTNAV
  else if v == (7 : UInt8) then .WHEEL_ENCODER
  else default

/-- C++ `enum class AP_NavEKF_Source::SourceZ`, `AP_NavEKF/AP_NavEKF_Source.h:28-37`. -/
inductive SourceZ where
  | NONE
  | BARO
  | RANGEFINDER
  | GPS
  | BEACON
  | EXTNAV
deriving DecidableEq, Inhabited

/-- The value of each enumerator of `AP_NavEKF_Source::SourceZ` (underlying type `uint8_t`). -/
def SourceZ.toInt : SourceZ → UInt8
  | .NONE => (0 : UInt8)
  | .BARO => (1 : UInt8)
  | .RANGEFINDER => (2 : UInt8)
  | .GPS => (3 : UInt8)
  | .BEACON => (4 : UInt8)
  | .EXTNAV => (6 : UInt8)

/-- The enumerator of `AP_NavEKF_Source::SourceZ` with value `v` (the C++ converts only enumerator values; any other
value gives the first enumerator, the `Inhabited` default). -/
def SourceZ.ofInt (v : UInt8) : SourceZ :=
  if v == (0 : UInt8) then .NONE
  else if v == (1 : UInt8) then .BARO
  else if v == (2 : UInt8) then .RANGEFINDER
  else if v == (3 : UInt8) then .GPS
  else if v == (4 : UInt8) then .BEACON
  else if v == (6 : UInt8) then .EXTNAV
  else default

/-- C++ `enum class AP_NavEKF_Source::SourceYaw`, `AP_NavEKF/AP_NavEKF_Source.h:39-46`. -/
inductive SourceYaw where
  | NONE
  | COMPASS
  | GPS
  | GPS_COMPASS_FALLBACK
  | EXTNAV
  | GSF
deriving DecidableEq, Inhabited

/-- The value of each enumerator of `AP_NavEKF_Source::SourceYaw` (underlying type `uint8_t`). -/
def SourceYaw.toInt : SourceYaw → UInt8
  | .NONE => (0 : UInt8)
  | .COMPASS => (1 : UInt8)
  | .GPS => (2 : UInt8)
  | .GPS_COMPASS_FALLBACK => (3 : UInt8)
  | .EXTNAV => (6 : UInt8)
  | .GSF => (8 : UInt8)

/-- The enumerator of `AP_NavEKF_Source::SourceYaw` with value `v` (the C++ converts only enumerator values; any other
value gives the first enumerator, the `Inhabited` default). -/
def SourceYaw.ofInt (v : UInt8) : SourceYaw :=
  if v == (0 : UInt8) then .NONE
  else if v == (1 : UInt8) then .COMPASS
  else if v == (2 : UInt8) then .GPS
  else if v == (3 : UInt8) then .GPS_COMPASS_FALLBACK
  else if v == (6 : UInt8) then .EXTNAV
  else if v == (8 : UInt8) then .GSF
  else default

/-- C++ `AP_NavEKF_Source::AP_NavEKF_Source()`, `AP_NavEKF/AP_NavEKF_Source.cpp:146-149`. -/
def construct : State := Id.run do
  let mut s : State := {}
  s := { s with _source_set := s._source_set.set! 0 ({ s._source_set[0]! with posxy._value := Binary32.toInt8 (Int8.toBinary32 (UInt8.toInt8 (AP_NavEKF_Source.SourceXY.toInt AP_NavEKF_Source.SourceXY.GPS))) }) }
  s := { s with _source_set := s._source_set.set! 0 ({ s._source_set[0]! with velxy._value := Binary32.toInt8 (Int8.toBinary32 (UInt8.toInt8 (AP_NavEKF_Source.SourceXY.toInt AP_NavEKF_Source.SourceXY.GPS))) }) }
  s := { s with _source_set := s._source_set.set! 0 ({ s._source_set[0]! with posz._value := Binary32.toInt8 (Int8.toBinary32 (UInt8.toInt8 (AP_NavEKF_Source.SourceZ.toInt AP_NavEKF_Source.SourceZ.BARO))) }) }
  s := { s with _source_set := s._source_set.set! 0 ({ s._source_set[0]! with velz._value := Binary32.toInt8 (Int8.toBinary32 (UInt8.toInt8 (AP_NavEKF_Source.SourceZ.toInt AP_NavEKF_Source.SourceZ.GPS))) }) }
  s := { s with _source_set := s._source_set.set! 0 ({ s._source_set[0]! with yaw._value := Binary32.toInt8 (Int8.toBinary32 (UInt8.toInt8 (AP_NavEKF_Source.SourceYaw.toInt AP_NavEKF_Source.SourceYaw.COMPASS))) }) }
  s := { s with _source_set := s._source_set.set! 1 ({ s._source_set[1]! with posxy._value := Binary32.toInt8 (Int8.toBinary32 (UInt8.toInt8 (AP_NavEKF_Source.SourceXY.toInt AP_NavEKF_Source.SourceXY.NONE))) }) }
  s := { s with _source_set := s._source_set.set! 1 ({ s._source_set[1]! with velxy._value := Binary32.toInt8 (Int8.toBinary32 (UInt8.toInt8 (AP_NavEKF_Source.SourceXY.toInt AP_NavEKF_Source.SourceXY.NONE))) }) }
  s := { s with _source_set := s._source_set.set! 1 ({ s._source_set[1]! with posz._value := Binary32.toInt8 (Int8.toBinary32 (UInt8.toInt8 (AP_NavEKF_Source.SourceZ.toInt AP_NavEKF_Source.SourceZ.BARO))) }) }
  s := { s with _source_set := s._source_set.set! 1 ({ s._source_set[1]! with velz._value := Binary32.toInt8 (Int8.toBinary32 (UInt8.toInt8 (AP_NavEKF_Source.SourceZ.toInt AP_NavEKF_Source.SourceZ.NONE))) }) }
  s := { s with _source_set := s._source_set.set! 1 ({ s._source_set[1]! with yaw._value := Binary32.toInt8 (Int8.toBinary32 (UInt8.toInt8 (AP_NavEKF_Source.SourceYaw.toInt AP_NavEKF_Source.SourceYaw.NONE))) }) }
  s := { s with _source_set := s._source_set.set! 2 ({ s._source_set[2]! with posxy._value := Binary32.toInt8 (Int8.toBinary32 (UInt8.toInt8 (AP_NavEKF_Source.SourceXY.toInt AP_NavEKF_Source.SourceXY.NONE))) }) }
  s := { s with _source_set := s._source_set.set! 2 ({ s._source_set[2]! with velxy._value := Binary32.toInt8 (Int8.toBinary32 (UInt8.toInt8 (AP_NavEKF_Source.SourceXY.toInt AP_NavEKF_Source.SourceXY.NONE))) }) }
  s := { s with _source_set := s._source_set.set! 2 ({ s._source_set[2]! with posz._value := Binary32.toInt8 (Int8.toBinary32 (UInt8.toInt8 (AP_NavEKF_Source.SourceZ.toInt AP_NavEKF_Source.SourceZ.BARO))) }) }
  s := { s with _source_set := s._source_set.set! 2 ({ s._source_set[2]! with velz._value := Binary32.toInt8 (Int8.toBinary32 (UInt8.toInt8 (AP_NavEKF_Source.SourceZ.toInt AP_NavEKF_Source.SourceZ.NONE))) }) }
  s := { s with _source_set := s._source_set.set! 2 ({ s._source_set[2]! with yaw._value := Binary32.toInt8 (Int8.toBinary32 (UInt8.toInt8 (AP_NavEKF_Source.SourceYaw.toInt AP_NavEKF_Source.SourceYaw.NONE))) }) }
  s := { s with _options._value := Int16.toUInt16 (Binary32.toInt16 (Binary32.ofBits 0x00000000 /- (float)0 -/)) }
  return s

end AP_NavEKF_Source

/-- C++ `struct ekf_timing`, `AP_NavEKF/AP_Nav_Common.h:111-121`. -/
structure ekf_timing where
  /-- `uint32_t count` of `ekf_timing` (`AP_NavEKF/AP_Nav_Common.h:112`). -/
  count : UInt32 := (0 : UInt32)
  /-- `float dtIMUavg_min` of `ekf_timing` (`AP_NavEKF/AP_Nav_Common.h:113`). -/
  dtIMUavg_min : Binary32 := (Binary32.ofBits 0x00000000 /- 0.0 -/)
  /-- `float dtIMUavg_max` of `ekf_timing` (`AP_NavEKF/AP_Nav_Common.h:114`). -/
  dtIMUavg_max : Binary32 := (Binary32.ofBits 0x00000000 /- 0.0 -/)
  /-- `float dtEKFavg_min` of `ekf_timing` (`AP_NavEKF/AP_Nav_Common.h:115`). -/
  dtEKFavg_min : Binary32 := (Binary32.ofBits 0x00000000 /- 0.0 -/)
  /-- `float dtEKFavg_max` of `ekf_timing` (`AP_NavEKF/AP_Nav_Common.h:116`). -/
  dtEKFavg_max : Binary32 := (Binary32.ofBits 0x00000000 /- 0.0 -/)
  /-- `float delAngDT_max` of `ekf_timing` (`AP_NavEKF/AP_Nav_Common.h:117`). -/
  delAngDT_max : Binary32 := (Binary32.ofBits 0x00000000 /- 0.0 -/)
  /-- `float delAngDT_min` of `ekf_timing` (`AP_NavEKF/AP_Nav_Common.h:118`). -/
  delAngDT_min : Binary32 := (Binary32.ofBits 0x00000000 /- 0.0 -/)
  /-- `float delVelDT_max` of `ekf_timing` (`AP_NavEKF/AP_Nav_Common.h:119`). -/
  delVelDT_max : Binary32 := (Binary32.ofBits 0x00000000 /- 0.0 -/)
  /-- `float delVelDT_min` of `ekf_timing` (`AP_NavEKF/AP_Nav_Common.h:120`). -/
  delVelDT_min : Binary32 := (Binary32.ofBits 0x00000000 /- 0.0 -/)
deriving Inhabited

namespace EKFGSF_yaw

/-- C++ `struct EKFGSF_yaw::ahrs_struct`, `AP_NavEKF/EKFGSF_yaw.h:75-83`. -/
structure ahrs_struct where
  /-- `Matrix3F R` of `EKFGSF_yaw::ahrs_struct` (`AP_NavEKF/EKFGSF_yaw.h:76`). -/
  R : Matrix3_double.State := Matrix3_double.init_void
  /-- `Vector3F gyro_bias` of `EKFGSF_yaw::ahrs_struct` (`AP_NavEKF/EKFGSF_yaw.h:77`). -/
  gyro_bias : Vector3p.State := {}
  /-- `bool aligned` of `EKFGSF_yaw::ahrs_struct` (`AP_NavEKF/EKFGSF_yaw.h:78`). -/
  aligned : Bool := false
  /-- `ftype accel_FR[2]` of `EKFGSF_yaw::ahrs_struct` (`AP_NavEKF/EKFGSF_yaw.h:79`). -/
  accel_FR : Array Binary64 := Array.replicate 2 (Binary64.ofBits 0x0000000000000000 /- 0.0 -/)
  /-- `ftype vel_NE[2]` of `EKFGSF_yaw::ahrs_struct` (`AP_NavEKF/EKFGSF_yaw.h:80`). -/
  vel_NE : Array Binary64 := Array.replicate 2 (Binary64.ofBits 0x0000000000000000 /- 0.0 -/)
  /-- `bool fuse_gps` of `EKFGSF_yaw::ahrs_struct` (`AP_NavEKF/EKFGSF_yaw.h:81`). -/
  fuse_gps : Bool := false
  /-- `ftype accel_dt` of `EKFGSF_yaw::ahrs_struct` (`AP_NavEKF/EKFGSF_yaw.h:82`). -/
  accel_dt : Binary64 := (Binary64.ofBits 0x0000000000000000 /- 0.0 -/)
deriving Inhabited

/-- C++ `struct EKFGSF_yaw::EKF_struct`, `AP_NavEKF/EKFGSF_yaw.h:105-110`. -/
structure EKF_struct where
  /-- `ftype X[3]` of `EKFGSF_yaw::EKF_struct` (`AP_NavEKF/EKFGSF_yaw.h:106`). -/
  X : Array Binary64 := Array.replicate 3 (Binary64.ofBits 0x0000000000000000 /- 0.0 -/)
  /-- `ftype P[3][3]` of `EKFGSF_yaw::EKF_struct` (`AP_NavEKF/EKFGSF_yaw.h:107`). -/
  P : Array Binary64 := Array.replicate 9 (Binary64.ofBits 0x0000000000000000 /- 0.0 -/)
  /-- `ftype S[2][2]` of `EKFGSF_yaw::EKF_struct` (`AP_NavEKF/EKFGSF_yaw.h:108`). -/
  S : Array Binary64 := Array.replicate 4 (Binary64.ofBits 0x0000000000000000 /- 0.0 -/)
  /-- `ftype innov[2]` of `EKFGSF_yaw::EKF_struct` (`AP_NavEKF/EKFGSF_yaw.h:109`). -/
  innov : Array Binary64 := Array.replicate 2 (Binary64.ofBits 0x0000000000000000 /- 0.0 -/)
deriving Inhabited

/-- C++ `struct EKFGSF_yaw::GSF_struct`, `AP_NavEKF/EKFGSF_yaw.h:131-135`. -/
structure GSF_struct where
  /-- `ftype yaw` of `EKFGSF_yaw::GSF_struct` (`AP_NavEKF/EKFGSF_yaw.h:132`). -/
  yaw : Binary64 := (Binary64.ofBits 0x0000000000000000 /- 0.0 -/)
  /-- `ftype yaw_variance` of `EKFGSF_yaw::GSF_struct` (`AP_NavEKF/EKFGSF_yaw.h:133`). -/
  yaw_variance : Binary64 := (Binary64.ofBits 0x0000000000000000 /- 0.0 -/)
  /-- `ftype weights[5]` of `EKFGSF_yaw::GSF_struct` (`AP_NavEKF/EKFGSF_yaw.h:134`). -/
  weights : Array Binary64 := Array.replicate 5 (Binary64.ofBits 0x0000000000000000 /- 0.0 -/)
deriving Inhabited

/-- State of C++ `EKFGSF_yaw` (`AP_NavEKF/EKFGSF_yaw.h:12-145`): its data members. -/
structure State where
  /-- `const ftype EKFGSF_gyroNoise` of `EKFGSF_yaw` (`AP_NavEKF/EKFGSF_yaw.h:62`). -/
  EKFGSF_gyroNoise : Binary64 := (Binary64.ofBits 0x3fb999999999999a /- 1.0e-1 -/)
  /-- `const ftype EKFGSF_accelNoise` of `EKFGSF_yaw` (`AP_NavEKF/EKFGSF_yaw.h:63`). -/
  EKFGSF_accelNoise : Binary64 := (Binary64.ofBits 0x4000000000000000 /- 2.0 -/)
  /-- `const ftype EKFGSF_tiltGain` of `EKFGSF_yaw` (`AP_NavEKF/EKFGSF_yaw.h:64`). -/
  EKFGSF_tiltGain : Binary64 := (Binary64.ofBits 0x3fc999999999999a /- 0.2 -/)
  /-- `const ftype EKFGSF_gyroBiasGain` of `EKFGSF_yaw` (`AP_NavEKF/EKFGSF_yaw.h:65`). -/
  EKFGSF_gyroBiasGain : Binary64 := (Binary64.ofBits 0x3fa47ae147ae147b /- 0.04 -/)
  /-- `const ftype EKFGSF_accelFiltRatio` of `EKFGSF_yaw` (`AP_NavEKF/EKFGSF_yaw.h:66`). -/
  EKFGSF_accelFiltRatio : Binary64 := (Binary64.ofBits 0x4024000000000000 /- 10.0 -/)
  /-- `Vector3F delta_angle` of `EKFGSF_yaw` (`AP_NavEKF/EKFGSF_yaw.h:71`). -/
  delta_angle : Vector3p.State := {}
  /-- `Vector3F delta_velocity` of `EKFGSF_yaw` (`AP_NavEKF/EKFGSF_yaw.h:72`). -/
  delta_velocity : Vector3p.State := {}
  /-- `ftype angle_dt` of `EKFGSF_yaw` (`AP_NavEKF/EKFGSF_yaw.h:73`). -/
  angle_dt : Binary64 := (Binary64.ofBits 0x0000000000000000 /- 0.0 -/)
  /-- `ftype velocity_dt` of `EKFGSF_yaw` (`AP_NavEKF/EKFGSF_yaw.h:74`). -/
  velocity_dt : Binary64 := (Binary64.ofBits 0x0000000000000000 /- 0.0 -/)
  /-- `ahrs_struct AHRS[5]` of `EKFGSF_yaw` (`AP_NavEKF/EKFGSF_yaw.h:84`). -/
  AHRS : Array EKFGSF_yaw.ahrs_struct := Array.replicate 5 {}
  /-- `bool ahrs_tilt_aligned` of `EKFGSF_yaw` (`AP_NavEKF/EKFGSF_yaw.h:85`). -/
  ahrs_tilt_aligned : Bool := false
  /-- `ftype accel_gain` of `EKFGSF_yaw` (`AP_NavEKF/EKFGSF_yaw.h:86`). -/
  accel_gain : Binary64 := (Binary64.ofBits 0x0000000000000000 /- 0.0 -/)
  /-- `Vector3F ahrs_accel` of `EKFGSF_yaw` (`AP_NavEKF/EKFGSF_yaw.h:87`). -/
  ahrs_accel : Vector3p.State := {}
  /-- `ftype ahrs_accel_norm` of `EKFGSF_yaw` (`AP_NavEKF/EKFGSF_yaw.h:88`). -/
  ahrs_accel_norm : Binary64 := (Binary64.ofBits 0x0000000000000000 /- 0.0 -/)
  /-- `ftype true_airspeed` of `EKFGSF_yaw` (`AP_NavEKF/EKFGSF_yaw.h:89`). -/
  true_airspeed : Binary64 := (Binary64.ofBits 0x0000000000000000 /- 0.0 -/)
  /-- `EKF_struct EKF[5]` of `EKFGSF_yaw` (`AP_NavEKF/EKFGSF_yaw.h:111`). -/
  EKF : Array EKFGSF_yaw.EKF_struct := Array.replicate 5 {}
  /-- `bool vel_fuse_running` of `EKFGSF_yaw` (`AP_NavEKF/EKFGSF_yaw.h:112`). -/
  vel_fuse_running : Bool := false
  /-- `bool run_ekf_gsf` of `EKFGSF_yaw` (`AP_NavEKF/EKFGSF_yaw.h:113`). -/
  run_ekf_gsf : Bool := false
  /-- `GSF_struct GSF` of `EKFGSF_yaw` (`AP_NavEKF/EKFGSF_yaw.h:136`). -/
  GSF : EKFGSF_yaw.GSF_struct := {}
  /-- `uint8_t n_clips` of `EKFGSF_yaw` (`AP_NavEKF/EKFGSF_yaw.h:144`). -/
  n_clips : UInt8 := (0 : UInt8)
deriving Inhabited

end EKFGSF_yaw

namespace AP_NavEKF_Source

/-- C++ `enum class AP_NavEKF_Source::SourceOptions`, `AP_NavEKF/AP_NavEKF_Source.h:49-54`. -/
inductive SourceOptions where
  | FUSE_ALL_VELOCITIES
  | ALIGN_EXTNAV_POS_WHEN_USING_OPTFLOW
  | SRC_PER_CORE
deriving DecidableEq, Inhabited

/-- The value of each enumerator of `AP_NavEKF_Source::SourceOptions` (underlying type `int32_t`). -/
def SourceOptions.toInt : SourceOptions → Int32
  | .FUSE_ALL_VELOCITIES => (1 : Int32)
  | .ALIGN_EXTNAV_POS_WHEN_USING_OPTFLOW => (2 : Int32)
  | .SRC_PER_CORE => (8 : Int32)

end AP_NavEKF_Source

namespace AP_NavEKF_Source

/-- C++ `bool AP_NavEKF_Source::option_is_set(SourceOptions option) const`, `AP_NavEKF/AP_NavEKF_Source.h:144`. -/
def option_is_set (s : State) (option : AP_NavEKF_Source.SourceOptions) : Bool := Id.run do
  return (UInt32.toInt32 (UInt16.toUInt32 (AP_ParamT_unsigned_short_2.get_void s._options)) &&& Int16.toInt32 (Int32.toInt16 (AP_NavEKF_Source.SourceOptions.toInt option))) != (0 : Int32)

/-- C++ `uint8_t AP_NavEKF_Source::getActiveSourceSet(uint8_t core_index) const`, `AP_NavEKF/AP_NavEKF_Source.h:66-76`. -/
def getActiveSourceSet (s : State) (core_index : UInt8) : UInt8 := Id.run do
  if option_is_set s AP_NavEKF_Source.SourceOptions.SRC_PER_CORE then
    if UInt32.toInt32 (UInt8.toUInt32 core_index) ≥ (3 : Int32) then
      return s.active_source_set
    return core_index
  return s.active_source_set

end AP_NavEKF_Source

namespace AP_NavEKF_Source

/-- C++ `bool AP_NavEKF_Source::gps_yaw_enabled() const`, `AP_NavEKF/AP_NavEKF_Source.cpp:600-611`. -/
def gps_yaw_enabled (s : State) : Bool := Id.run do
  for i' in [0:3] do
    let i : UInt8 := Nat.toUInt8 i'
    let yaw : AP_NavEKF_Source.SourceYaw := AP_NavEKF_Source.SourceYaw.ofInt (Int8.toUInt8 (AP_Enum_AP_NavEKF_Source_SourceYaw.get_void s._source_set[UInt8.toNat i]!.yaw))
    if yaw == AP_NavEKF_Source.SourceYaw.GPS || yaw == AP_NavEKF_Source.SourceYaw.GPS_COMPASS_FALLBACK then
      return true
  return false

end AP_NavEKF_Source

namespace EKFGSF_yaw

/-- C++ `EKFGSF_yaw::EKFGSF_yaw()`, `AP_NavEKF/EKFGSF_yaw.cpp:28`. -/
def init : State := Id.run do
  let mut s : State := {}
  s := { s with delta_angle := Vector3p.init_void }
  s := { s with delta_velocity := Vector3p.init_void }
  s := { s with ahrs_accel := Vector3p.init_void }
  return s

end EKFGSF_yaw

namespace NavEKF_core_common

/-- C++ `static void NavEKF_core_common::zero_range(ftype * v, uint8_t n1, uint8_t n2)`, `AP_NavEKF/AP_NavEKF_core_common.h:52-54`. -/
def zero_range (v : Array Binary64) (v'o : Nat) (n1 n2 : UInt8) : (Array Binary64) := Id.run do
  let mut v := v
  for t'1 in [0:((Int64.toUInt64 (Int32.toInt64 ((1 : Int32) + (UInt32.toInt32 (UInt8.toUInt32 n2) - UInt32.toInt32 (UInt8.toUInt32 n1))))).toNat)] do  -- C++ `memset` of k elements
    v := v.set! (v'o + UInt8.toNat n1 + t'1) (Binary64.ofBits 0x0000000000000000 /- 0.0 -/)
  return v

end NavEKF_core_common

/-- C++ `enum class NavFilterFaultBit`, `AP_NavEKF/AP_Nav_Common.h:78-87`. -/
inductive NavFilterFaultBit where
  | BAD_QUATERNION
  | BAD_VELOCITY
  | BAD_XMAG
  | BAD_YMAG
  | BAD_ZMAG
  | BAD_AIRSPEED
  | BAD_SIDESLIP
  | NOT_INITIALISED
deriving DecidableEq, Inhabited

/-- The value of each enumerator of `NavFilterFaultBit` (underlying type `int32_t`). -/
def NavFilterFaultBit.toInt : NavFilterFaultBit → Int32
  | .BAD_QUATERNION => (1 : Int32)
  | .BAD_VELOCITY => (2 : Int32)
  | .BAD_XMAG => (4 : Int32)
  | .BAD_YMAG => (8 : Int32)
  | .BAD_ZMAG => (16 : Int32)
  | .BAD_AIRSPEED => (32 : Int32)
  | .BAD_SIDESLIP => (64 : Int32)
  | .NOT_INITIALISED => (128 : Int32)

namespace EKFGSF_yaw

/-- C++ `void EKFGSF_yaw::setGyroBias(Vector3f & gyroBias)`, `AP_NavEKF/EKFGSF_yaw.cpp:663-668`. -/
def setGyroBias (s : State) (gyroBias : Vector3f.State) : State × Vector3f.State := Id.run do
  let mut s := s
  let mut gyroBias := gyroBias
  for mdl_idx' in [0:5] do
    let mdl_idx : UInt8 := Nat.toUInt8 mdl_idx'
    s := { s with AHRS := s.AHRS.set! (UInt8.toNat mdl_idx) ({ s.AHRS[UInt8.toNat mdl_idx]! with gyro_bias := Vector3f.todouble gyroBias }) }
  return (s, gyroBias)

end EKFGSF_yaw

namespace EKFGSF_yaw

/-- C++ `void EKFGSF_yaw::alignTilt()`, `AP_NavEKF/EKFGSF_yaw.cpp:251-288`. -/
def alignTilt (s : State) : State := Id.run do
  let mut s := s
  let mut down_in_bf : Vector3p.State := Vector3p.op_sub_void s.delta_velocity
  down_in_bf := Vector3p.normalize down_in_bf
  let i_vec_bf : Vector3p.State := Vector3p.init_double3 (Binary64.ofBits 0x3ff0000000000000 /- 1.0f -/) (Binary64.ofBits 0x0000000000000000 /- 0.0f -/) (Binary64.ofBits 0x0000000000000000 /- 0.0f -/)
  let mut north_in_bf : Vector3p.State := Vector3p.op_sub_Vector3p i_vec_bf (Vector3p.op_mul_double down_in_bf (Vector3p.op_mul_Vector3p i_vec_bf down_in_bf))
  north_in_bf := Vector3p.normalize north_in_bf
  let east_in_bf : Vector3p.State := Vector3p.op_mod down_in_bf north_in_bf
  let mut R : Matrix3_double.State := Matrix3_double.init_void
  for col' in [0:3] do
    let col : UInt8 := Nat.toUInt8 col'
    let t'1 := (match UInt8.toNat col with | 0 => north_in_bf.x | 1 => north_in_bf.y | _ => north_in_bf.z)
    R := (match UInt8.toNat col with | 0 => { R with a.x := t'1 } | 1 => { R with a.y := t'1 } | _ => { R with a.z := t'1 })
    let t'2 := (match UInt8.toNat col with | 0 => east_in_bf.x | 1 => east_in_bf.y | _ => east_in_bf.z)
    R := (match UInt8.toNat col with | 0 => { R with b.x := t'2 } | 1 => { R with b.y := t'2 } | _ => { R with b.z := t'2 })
    let t'3 := (match UInt8.toNat col with | 0 => down_in_bf.x | 1 => down_in_bf.y | _ => down_in_bf.z)
    R := (match UInt8.toNat col with | 0 => { R with c.x := t'3 } | 1 => { R with c.y := t'3 } | _ => { R with c.z := t'3 })
  for mdl_idx' in [0:5] do
    let mdl_idx : UInt8 := Nat.toUInt8 mdl_idx'
    s := { s with AHRS := s.AHRS.set! (UInt8.toNat mdl_idx) ({ s.AHRS[UInt8.toNat mdl_idx]! with R := R }) }
    s := { s with AHRS := s.AHRS.set! (UInt8.toNat mdl_idx) ({ s.AHRS[UInt8.toNat mdl_idx]! with aligned := true }) }
  return s

/-- C++ `Matrix3F EKFGSF_yaw::updateRotMat(const Matrix3F & R, const Vector3F & g) const`, `AP_NavEKF/EKFGSF_yaw.cpp:607-633`. -/
def updateRotMat (R : Matrix3_double.State) (g : Vector3p.State) : Matrix3_double.State := Id.run do
  let mut ret : Matrix3_double.State := R
  ret := { ret with a.x := ret.a.x + (R.a.y * g.z - R.a.z * g.y) }
  ret := { ret with a.y := ret.a.y + (R.a.z * g.x - R.a.x * g.z) }
  ret := { ret with a.z := ret.a.z + (R.a.x * g.y - R.a.y * g.x) }
  ret := { ret with b.x := ret.b.x + (R.b.y * g.z - R.b.z * g.y) }
  ret := { ret with b.y := ret.b.y + (R.b.z * g.x - R.b.x * g.z) }
  ret := { ret with b.z := ret.b.z + (R.b.x * g.y - R.b.y * g.x) }
  ret := { ret with c.x := ret.c.x + (R.c.y * g.z - R.c.z * g.y) }
  ret := { ret with c.y := ret.c.y + (R.c.z * g.x - R.c.x * g.z) }
  ret := { ret with c.z := ret.c.z + (R.c.x * g.y - R.c.y * g.x) }
  let mut rowLengthSq : Binary64 := (Binary64.ofBits 0x0000000000000000 /- 0.0 -/)  -- uninitialized in C++; assigned before every read
  for r' in [0:3] do
    let r : UInt8 := Nat.toUInt8 r'
    rowLengthSq := (match UInt8.toNat r with | 0 => ret.a | 1 => ret.b | _ => ret.c).x * (match UInt8.toNat r with | 0 => ret.a | 1 => ret.b | _ => ret.c).x + (match UInt8.toNat r with | 0 => ret.a | 1 => ret.b | _ => ret.c).y * (match UInt8.toNat r with | 0 => ret.a | 1 => ret.b | _ => ret.c).y + (match UInt8.toNat r with | 0 => ret.a | 1 => ret.b | _ => ret.c).z * (match UInt8.toNat r with | 0 => ret.a | 1 => ret.b | _ => ret.c).z
    if Estimator_lib.is_positive_double rowLengthSq then
      let rowLengthInv : Binary64 := (Binary64.ofBits 0x3ff8000000000000 /- 1.5f -/) - (Binary64.ofBits 0x3fe0000000000000 /- 0.5f -/) * rowLengthSq
      let (t'1, _) := Vector3p.op_mul_assign_double (match UInt8.toNat r with | 0 => ret.a | 1 => ret.b | _ => ret.c) rowLengthInv
      ret := (match UInt8.toNat r with | 0 => { ret with a := t'1 } | 1 => { ret with b := t'1 } | _ => { ret with c := t'1 })
  return ret

/-- C++ `void EKFGSF_yaw::predictAHRS(const uint8_t mdl_idx)`, `AP_NavEKF/EKFGSF_yaw.cpp:194-249`. -/
def predictAHRS (s : State) (mdl_idx : UInt8) : State := Id.run do
  let mut s := s
  let k : Vector3p.State := Vector3p.init_double3 s.AHRS[UInt8.toNat mdl_idx]!.R.c.x s.AHRS[UInt8.toNat mdl_idx]!.R.c.y s.AHRS[UInt8.toNat mdl_idx]!.R.c.z
  let ang_rate_delayed_raw : Vector3p.State := Vector3p.op_div s.delta_angle s.angle_dt
  let mut tilt_error_gyro_correction : Vector3p.State := Vector3p.init_void
  if s.accel_gain > (Binary64.ofBits 0x0000000000000000 /- 0.0f -/) then
    let mut accel : Vector3p.State := s.ahrs_accel
    if Estimator_lib.is_positive_double s.true_airspeed then
      let centripetal_accel_vec_bf : Vector3p.State := Vector3p.init_double3 (Binary64.ofBits 0x0000000000000000 /- 0.0f -/) (ang_rate_delayed_raw.z * s.true_airspeed) (-ang_rate_delayed_raw.y * s.true_airspeed)
      let (t'1, _) := Vector3p.op_sub_assign accel centripetal_accel_vec_bf
      accel := t'1
    tilt_error_gyro_correction := Vector3p.op_mul_double (Vector3p.op_mod k accel) (s.accel_gain / s.ahrs_accel_norm)
  let gyro_bias_limit : Binary64 := Binary32.toBinary64 (Estimator_lib.radians_float (Binary32.ofBits 0x40a00000 /- 5.0f -/))
  let spinRate_squared : Binary64 := Vector3p.length_squared ang_rate_delayed_raw
  if spinRate_squared < Binary32.toBinary64 (Estimator_lib.sq_float (Binary32.ofBits 0x3e333333 /- 0.175f -/)) then
    let (t'3, _) := Vector3p.op_sub_assign s.AHRS[UInt8.toNat mdl_idx]!.gyro_bias (Vector3p.op_mul_double tilt_error_gyro_correction (s.EKFGSF_gyroBiasGain * s.angle_dt))
    s := { s with AHRS := s.AHRS.set! (UInt8.toNat mdl_idx) ({ s.AHRS[UInt8.toNat mdl_idx]! with gyro_bias := t'3 }) }
    if Vector3p.is_nan s.AHRS[UInt8.toNat mdl_idx]!.gyro_bias then
      s := { s with AHRS := s.AHRS.set! (UInt8.toNat mdl_idx) ({ s.AHRS[UInt8.toNat mdl_idx]! with gyro_bias := Vector3p.zero s.AHRS[UInt8.toNat mdl_idx]!.gyro_bias }) }
    for i' in [0:3] do
      let i : UInt8 := Nat.toUInt8 i'
      let t'5 := Estimator_lib.constrain_value_line_double (match UInt8.toNat i with | 0 => s.AHRS[UInt8.toNat mdl_idx]!.gyro_bias.x | 1 => s.AHRS[UInt8.toNat mdl_idx]!.gyro_bias.y | _ => s.AHRS[UInt8.toNat mdl_idx]!.gyro_bias.z) (-gyro_bias_limit) gyro_bias_limit (Int32.toUInt32 (241 : Int32))
      s := (match UInt8.toNat i with | 0 => { s with AHRS := s.AHRS.set! (UInt8.toNat mdl_idx) ({ s.AHRS[UInt8.toNat mdl_idx]! with gyro_bias.x := t'5 }) } | 1 => { s with AHRS := s.AHRS.set! (UInt8.toNat mdl_idx) ({ s.AHRS[UInt8.toNat mdl_idx]! with gyro_bias.y := t'5 }) } | _ => { s with AHRS := s.AHRS.set! (UInt8.toNat mdl_idx) ({ s.AHRS[UInt8.toNat mdl_idx]! with gyro_bias.z := t'5 }) })
  let ahrs_delta_angle : Vector3p.State := Vector3p.op_add s.delta_angle (Vector3p.op_mul_double (Vector3p.op_sub_Vector3p tilt_error_gyro_correction s.AHRS[UInt8.toNat mdl_idx]!.gyro_bias) s.angle_dt)
  s := { s with AHRS := s.AHRS.set! (UInt8.toNat mdl_idx) ({ s.AHRS[UInt8.toNat mdl_idx]! with R := updateRotMat s.AHRS[UInt8.toNat mdl_idx]!.R ahrs_delta_angle }) }
  return s

/-- C++ `void EKFGSF_yaw::forceSymmetry(const uint8_t mdl_idx)`, `AP_NavEKF/EKFGSF_yaw.cpp:596-604`. -/
def forceSymmetry (s : State) (mdl_idx : UInt8) : State := Id.run do
  let mut s := s
  let P01 : Binary64 := (Binary64.ofBits 0x3fe0000000000000 /- 0.5f -/) * (s.EKF[UInt8.toNat mdl_idx]!.P[1]! + s.EKF[UInt8.toNat mdl_idx]!.P[3]!)
  let P02 : Binary64 := (Binary64.ofBits 0x3fe0000000000000 /- 0.5f -/) * (s.EKF[UInt8.toNat mdl_idx]!.P[2]! + s.EKF[UInt8.toNat mdl_idx]!.P[6]!)
  let P12 : Binary64 := (Binary64.ofBits 0x3fe0000000000000 /- 0.5f -/) * (s.EKF[UInt8.toNat mdl_idx]!.P[5]! + s.EKF[UInt8.toNat mdl_idx]!.P[7]!)
  let t'1 := UInt8.toNat mdl_idx
  let t'2 := s.EKF
  s := { s with EKF := #[] }
  let t'3 := t'2[t'1]!
  let t'2 := t'2.set! t'1 default
  let t'4 := t'3.P
  let t'3 := { t'3 with P := #[] }
  let t'3 := { t'3 with P := t'4.set! 3 P01 }
  s := { s with EKF := t'2.set! t'1 t'3 }
  let t'5 := s.EKF[UInt8.toNat mdl_idx]!.P[3]!
  let t'6 := UInt8.toNat mdl_idx
  let t'7 := s.EKF
  s := { s with EKF := #[] }
  let t'8 := t'7[t'6]!
  let t'7 := t'7.set! t'6 default
  let t'9 := t'8.P
  let t'8 := { t'8 with P := #[] }
  let t'8 := { t'8 with P := t'9.set! 1 t'5 }
  s := { s with EKF := t'7.set! t'6 t'8 }
  let t'10 := UInt8.toNat mdl_idx
  let t'11 := s.EKF
  s := { s with EKF := #[] }
  let t'12 := t'11[t'10]!
  let t'11 := t'11.set! t'10 default
  let t'13 := t'12.P
  let t'12 := { t'12 with P := #[] }
  let t'12 := { t'12 with P := t'13.set! 6 P02 }
  s := { s with EKF := t'11.set! t'10 t'12 }
  let t'14 := s.EKF[UInt8.toNat mdl_idx]!.P[6]!
  let t'15 := UInt8.toNat mdl_idx
  let t'16 := s.EKF
  s := { s with EKF := #[] }
  let t'17 := t'16[t'15]!
  let t'16 := t'16.set! t'15 default
  let t'18 := t'17.P
  let t'17 := { t'17 with P := #[] }
  let t'17 := { t'17 with P := t'18.set! 2 t'14 }
  s := { s with EKF := t'16.set! t'15 t'17 }
  let t'19 := UInt8.toNat mdl_idx
  let t'20 := s.EKF
  s := { s with EKF := #[] }
  let t'21 := t'20[t'19]!
  let t'20 := t'20.set! t'19 default
  let t'22 := t'21.P
  let t'21 := { t'21 with P := #[] }
  let t'21 := { t'21 with P := t'22.set! 7 P12 }
  s := { s with EKF := t'20.set! t'19 t'21 }
  let t'23 := s.EKF[UInt8.toNat mdl_idx]!.P[7]!
  let t'24 := UInt8.toNat mdl_idx
  let t'25 := s.EKF
  s := { s with EKF := #[] }
  let t'26 := t'25[t'24]!
  let t'25 := t'25.set! t'24 default
  let t'27 := t'26.P
  let t'26 := { t'26 with P := #[] }
  let t'26 := { t'26 with P := t'27.set! 5 t'23 }
  s := { s with EKF := t'25.set! t'24 t'26 }
  return s

/-- C++ `void EKFGSF_yaw::predict(const uint8_t mdl_idx)`, `AP_NavEKF/EKFGSF_yaw.cpp:318-394`. -/
def predict (s : State) (mdl_idx : UInt8) : State := Id.run do
  let mut s := s
  s := predictAHRS s mdl_idx
  if !s.vel_fuse_running then
    return s
  if Binary64.abs s.AHRS[UInt8.toNat mdl_idx]!.R.c.x < Binary64.abs s.AHRS[UInt8.toNat mdl_idx]!.R.c.y then
    let t'1 := Musl.atan2.atan2 s.AHRS[UInt8.toNat mdl_idx]!.R.b.x s.AHRS[UInt8.toNat mdl_idx]!.R.a.x
    let t'2 := UInt8.toNat mdl_idx
    let t'3 := s.EKF
    s := { s with EKF := #[] }
    let t'4 := t'3[t'2]!
    let t'3 := t'3.set! t'2 default
    let t'5 := t'4.X
    let t'4 := { t'4 with X := #[] }
    let t'4 := { t'4 with X := t'5.set! 2 t'1 }
    s := { s with EKF := t'3.set! t'2 t'4 }
  else
    let t'6 := Musl.atan2.atan2 (-s.AHRS[UInt8.toNat mdl_idx]!.R.a.y) s.AHRS[UInt8.toNat mdl_idx]!.R.b.y
    let t'7 := UInt8.toNat mdl_idx
    let t'8 := s.EKF
    s := { s with EKF := #[] }
    let t'9 := t'8[t'7]!
    let t'8 := t'8.set! t'7 default
    let t'10 := t'9.X
    let t'9 := { t'9 with X := #[] }
    let t'9 := { t'9 with X := t'10.set! 2 t'6 }
    s := { s with EKF := t'8.set! t'7 t'9 }
  let del_vel_NED : Vector3p.State := Matrix3_double.op_mul_Vector3p s.AHRS[UInt8.toNat mdl_idx]!.R s.delta_velocity
  let dvx : Binary64 := del_vel_NED.x * Musl.cos.cos s.EKF[UInt8.toNat mdl_idx]!.X[2]! + del_vel_NED.y * Musl.sin.sin s.EKF[UInt8.toNat mdl_idx]!.X[2]!
  let dvy : Binary64 := -del_vel_NED.x * Musl.sin.sin s.EKF[UInt8.toNat mdl_idx]!.X[2]! + del_vel_NED.y * Musl.cos.cos s.EKF[UInt8.toNat mdl_idx]!.X[2]!
  let t'11 := s.EKF[UInt8.toNat mdl_idx]!.X[0]! + del_vel_NED.x
  let t'12 := UInt8.toNat mdl_idx
  let t'13 := s.EKF
  s := { s with EKF := #[] }
  let t'14 := t'13[t'12]!
  let t'13 := t'13.set! t'12 default
  let t'15 := t'14.X
  let t'14 := { t'14 with X := #[] }
  let t'14 := { t'14 with X := t'15.set! 0 t'11 }
  s := { s with EKF := t'13.set! t'12 t'14 }
  let t'16 := s.EKF[UInt8.toNat mdl_idx]!.X[1]! + del_vel_NED.y
  let t'17 := UInt8.toNat mdl_idx
  let t'18 := s.EKF
  s := { s with EKF := #[] }
  let t'19 := t'18[t'17]!
  let t'18 := t'18.set! t'17 default
  let t'20 := t'19.X
  let t'19 := { t'19 with X := #[] }
  let t'19 := { t'19 with X := t'20.set! 1 t'16 }
  s := { s with EKF := t'18.set! t'17 t'19 }
  let P00 : Binary64 := s.EKF[UInt8.toNat mdl_idx]!.P[0]!
  let P01 : Binary64 := s.EKF[UInt8.toNat mdl_idx]!.P[1]!
  let P02 : Binary64 := s.EKF[UInt8.toNat mdl_idx]!.P[2]!
  let P10 : Binary64 := s.EKF[UInt8.toNat mdl_idx]!.P[3]!
  let P11 : Binary64 := s.EKF[UInt8.toNat mdl_idx]!.P[4]!
  let P12 : Binary64 := s.EKF[UInt8.toNat mdl_idx]!.P[5]!
  let P20 : Binary64 := s.EKF[UInt8.toNat mdl_idx]!.P[6]!
  let P21 : Binary64 := s.EKF[UInt8.toNat mdl_idx]!.P[7]!
  let P22 : Binary64 := s.EKF[UInt8.toNat mdl_idx]!.P[8]!
  let dvxVar : Binary64 := Estimator_lib.sq_double (s.EKFGSF_accelNoise * s.velocity_dt)
  let dvyVar : Binary64 := dvxVar
  let dazVar : Binary64 := Estimator_lib.sq_double (s.EKFGSF_gyroNoise * s.angle_dt)
  let t2 : Binary64 := Musl.sin.sin s.EKF[UInt8.toNat mdl_idx]!.X[2]!
  let t3 : Binary64 := Musl.cos.cos s.EKF[UInt8.toNat mdl_idx]!.X[2]!
  let t4 : Binary64 := dvy * t3
  let t5 : Binary64 := dvx * t2
  let t6 : Binary64 := t4 + t5
  let t8 : Binary64 := P22 * t6
  let t7 : Binary64 := P02 - t8
  let t9 : Binary64 := dvx * t3
  let t11 : Binary64 := dvy * t2
  let t10 : Binary64 := t9 - t11
  let t12 : Binary64 := dvxVar * t2 * t3
  let t13 : Binary64 := t2 * t2
  let t14 : Binary64 := t3 * t3
  let t15 : Binary64 := P22 * t10
  let t16 : Binary64 := P12 + t15
  let min_var : Binary64 := (Binary64.ofBits 0x3eb0c6f7a0000000 /- 1e-6f -/)
  let t'21 := Binary64.fmax (P00 - P20 * t6 + dvxVar * t14 + dvyVar * t13 - t6 * t7) min_var
  let t'22 := UInt8.toNat mdl_idx
  let t'23 := s.EKF
  s := { s with EKF := #[] }
  let t'24 := t'23[t'22]!
  let t'23 := t'23.set! t'22 default
  let t'25 := t'24.P
  let t'24 := { t'24 with P := #[] }
  let t'24 := { t'24 with P := t'25.set! 0 t'21 }
  s := { s with EKF := t'23.set! t'22 t'24 }
  let t'26 := P01 + t12 - P21 * t6 + t7 * t10 - dvyVar * t2 * t3
  let t'27 := UInt8.toNat mdl_idx
  let t'28 := s.EKF
  s := { s with EKF := #[] }
  let t'29 := t'28[t'27]!
  let t'28 := t'28.set! t'27 default
  let t'30 := t'29.P
  let t'29 := { t'29 with P := #[] }
  let t'29 := { t'29 with P := t'30.set! 1 t'26 }
  s := { s with EKF := t'28.set! t'27 t'29 }
  let t'31 := UInt8.toNat mdl_idx
  let t'32 := s.EKF
  s := { s with EKF := #[] }
  let t'33 := t'32[t'31]!
  let t'32 := t'32.set! t'31 default
  let t'34 := t'33.P
  let t'33 := { t'33 with P := #[] }
  let t'33 := { t'33 with P := t'34.set! 2 t7 }
  s := { s with EKF := t'32.set! t'31 t'33 }
  let t'35 := P10 + t12 + P20 * t10 - t6 * t16 - dvyVar * t2 * t3
  let t'36 := UInt8.toNat mdl_idx
  let t'37 := s.EKF
  s := { s with EKF := #[] }
  let t'38 := t'37[t'36]!
  let t'37 := t'37.set! t'36 default
  let t'39 := t'38.P
  let t'38 := { t'38 with P := #[] }
  let t'38 := { t'38 with P := t'39.set! 3 t'35 }
  s := { s with EKF := t'37.set! t'36 t'38 }
  let t'40 := Binary64.fmax (P11 + P21 * t10 + dvxVar * t13 + dvyVar * t14 + t10 * t16) min_var
  let t'41 := UInt8.toNat mdl_idx
  let t'42 := s.EKF
  s := { s with EKF := #[] }
  let t'43 := t'42[t'41]!
  let t'42 := t'42.set! t'41 default
  let t'44 := t'43.P
  let t'43 := { t'43 with P := #[] }
  let t'43 := { t'43 with P := t'44.set! 4 t'40 }
  s := { s with EKF := t'42.set! t'41 t'43 }
  let t'45 := UInt8.toNat mdl_idx
  let t'46 := s.EKF
  s := { s with EKF := #[] }
  let t'47 := t'46[t'45]!
  let t'46 := t'46.set! t'45 default
  let t'48 := t'47.P
  let t'47 := { t'47 with P := #[] }
  let t'47 := { t'47 with P := t'48.set! 5 t16 }
  s := { s with EKF := t'46.set! t'45 t'47 }
  let t'49 := P20 - t8
  let t'50 := UInt8.toNat mdl_idx
  let t'51 := s.EKF
  s := { s with EKF := #[] }
  let t'52 := t'51[t'50]!
  let t'51 := t'51.set! t'50 default
  let t'53 := t'52.P
  let t'52 := { t'52 with P := #[] }
  let t'52 := { t'52 with P := t'53.set! 6 t'49 }
  s := { s with EKF := t'51.set! t'50 t'52 }
  let t'54 := P21 + t15
  let t'55 := UInt8.toNat mdl_idx
  let t'56 := s.EKF
  s := { s with EKF := #[] }
  let t'57 := t'56[t'55]!
  let t'56 := t'56.set! t'55 default
  let t'58 := t'57.P
  let t'57 := { t'57 with P := #[] }
  let t'57 := { t'57 with P := t'58.set! 7 t'54 }
  s := { s with EKF := t'56.set! t'55 t'57 }
  let t'59 := Binary64.fmax (P22 + dazVar) min_var
  let t'60 := UInt8.toNat mdl_idx
  let t'61 := s.EKF
  s := { s with EKF := #[] }
  let t'62 := t'61[t'60]!
  let t'61 := t'61.set! t'60 default
  let t'63 := t'62.P
  let t'62 := { t'62 with P := #[] }
  let t'62 := { t'62 with P := t'63.set! 8 t'59 }
  s := { s with EKF := t'61.set! t'60 t'62 }
  s := forceSymmetry s mdl_idx
  return s

/-- C++ `void EKFGSF_yaw::update(const Vector3F & delAng, const Vector3F & delVel, const ftype delAngDT, const ftype delVelDT, bool runEKF, ftype TAS)`, `AP_NavEKF/EKFGSF_yaw.cpp:30-134`. -/
def update (s : State) (delAng : Vector3p.State) (delVel : Vector3p.State) (delAngDT : Binary64) (delVelDT : Binary64) (runEKF : Bool) (TAS : Binary64) : State := Id.run do
  let mut s := s
  s := { s with delta_angle := delAng }
  s := { s with delta_velocity := delVel }
  s := { s with angle_dt := delAngDT }
  s := { s with velocity_dt := delVelDT }
  s := { s with run_ekf_gsf := runEKF }
  s := { s with true_airspeed := TAS }
  let filter_coef : Binary64 := Binary64.fmin (s.EKFGSF_accelFiltRatio * delVelDT * s.EKFGSF_tiltGain) (Binary32.toBinary64 (Binary32.ofBits 0x3f800000 /- 1 -/))
  let accel : Vector3p.State := Vector3p.op_div delVel (Binary64.fmax delVelDT (Binary32.toBinary64 (Binary32.ofBits 0x3a83126f /- 0.00100000005 -/)))
  s := { s with ahrs_accel := Vector3p.op_add (Vector3p.op_mul_double s.ahrs_accel ((Binary64.ofBits 0x3ff0000000000000 /- 1.0f -/) - filter_coef)) (Vector3p.op_mul_double accel filter_coef) }
  if !s.ahrs_tilt_aligned then
    let accel_norm_sq : Binary64 := Vector3p.length_squared accel
    let upper_accel_limit : Binary64 := (Binary64.ofBits 0x4025931b00000000 /- (double)1413915/131072 -/)
    let lower_accel_limit : Binary64 := (Binary64.ofBits 0x4021a6e780000000 /- (double)2313679/262144 -/)
    let ok_to_align : Bool := (decide (accel_norm_sq > lower_accel_limit * lower_accel_limit) && decide (accel_norm_sq < upper_accel_limit * upper_accel_limit))
    if ok_to_align then
      s := alignTilt s
      s := { s with ahrs_tilt_aligned := true }
      s := { s with ahrs_accel := accel }
    return s
  s := { s with ahrs_accel_norm := Vector3p.length s.ahrs_accel }
  let EKFGSF_ahrs_ng : Binary64 := s.ahrs_accel_norm / (Binary64.ofBits 0x40239d0140000000 /- (double)5141509/524288 -/)
  if EKFGSF_ahrs_ng > (Binary64.ofBits 0x3ff0000000000000 /- 1.0f -/) then
    if Estimator_lib.is_positive_double s.true_airspeed then
      s := { s with accel_gain := s.EKFGSF_tiltGain * Estimator_lib.sq_double (Estimator_lib.MAX_double_float ((Binary64.ofBits 0x4000000000000000 /- 2.0f -/) - EKFGSF_ahrs_ng) (Binary32.ofBits 0x00000000 /- 0.0f -/)) }
    else if EKFGSF_ahrs_ng ≤ (Binary64.ofBits 0x3ff8000000000000 /- 1.5f -/) then
      s := { s with accel_gain := s.EKFGSF_tiltGain * Estimator_lib.sq_double ((Binary64.ofBits 0x4008000000000000 /- 3.0f -/) - (Binary64.ofBits 0x4000000000000000 /- 2.0f -/) * EKFGSF_ahrs_ng) }
    else
      s := { s with accel_gain := (Binary64.ofBits 0x0000000000000000 /- 0.0f -/) }
  else if EKFGSF_ahrs_ng > (Binary64.ofBits 0x3fe0000000000000 /- 0.5f -/) then
    s := { s with accel_gain := s.EKFGSF_tiltGain * Estimator_lib.sq_double ((Binary64.ofBits 0x4000000000000000 /- 2.0f -/) * EKFGSF_ahrs_ng - (Binary64.ofBits 0x3ff0000000000000 /- 1.0f -/)) }
  else
    s := { s with accel_gain := (Binary64.ofBits 0x0000000000000000 /- 0.0f -/) }
  for mdl_idx' in [0:5] do
    let mdl_idx : UInt8 := Nat.toUInt8 mdl_idx'
    s := predict s mdl_idx
  if s.vel_fuse_running && !s.run_ekf_gsf then
    s := { s with vel_fuse_running := false }
  let mut yaw_vector : Vector2p.State := Vector2p.init_void
  for mdl_idx'2' in [0:5] do
    let mdl_idx'2 : UInt8 := Nat.toUInt8 mdl_idx'2'
    yaw_vector := { yaw_vector with x := yaw_vector.x + s.GSF.weights[UInt8.toNat mdl_idx'2]! * Musl.cos.cos s.EKF[UInt8.toNat mdl_idx'2]!.X[2]! }
    yaw_vector := { yaw_vector with y := yaw_vector.y + s.GSF.weights[UInt8.toNat mdl_idx'2]! * Musl.sin.sin s.EKF[UInt8.toNat mdl_idx'2]!.X[2]! }
  s := { s with GSF.yaw := Musl.atan2.atan2 yaw_vector.y yaw_vector.x }
  s := { s with GSF.yaw_variance := (Binary64.ofBits 0x0000000000000000 /- 0.0f -/) }
  for mdl_idx'3' in [0:5] do
    let mdl_idx'3 : UInt8 := Nat.toUInt8 mdl_idx'3'
    let yawDelta : Binary64 := Estimator_lib.wrap_PI_double (s.EKF[UInt8.toNat mdl_idx'3]!.X[2]! - s.GSF.yaw)
    s := { s with GSF.yaw_variance := s.GSF.yaw_variance + s.GSF.weights[UInt8.toNat mdl_idx'3]! * (s.EKF[UInt8.toNat mdl_idx'3]!.P[8]! + Estimator_lib.sq_double yawDelta) }
  return s

end EKFGSF_yaw

namespace EKFGSF_yaw

/-- C++ `bool EKFGSF_yaw::getYawData(ftype & yaw, ftype & yawVariance, uint8_t * n_clips) const`, `AP_NavEKF/EKFGSF_yaw.cpp:638-649`. -/
def getYawData (s : State) (yaw : Binary64) (yawVariance : Binary64) (_n_clips'given : Bool) (_n_clips : UInt8) : Binary64 × Binary64 × UInt8 × Bool := Id.run do
  let mut yaw := yaw
  let mut yawVariance := yawVariance
  let mut _n_clips := _n_clips
  if !s.vel_fuse_running then
    return (yaw, yawVariance, _n_clips, false)
  yaw := s.GSF.yaw
  yawVariance := s.GSF.yaw_variance
  if _n_clips'given then
    _n_clips := s.n_clips
  return (yaw, yawVariance, _n_clips, true)

/-- C++ `bool EKFGSF_yaw::getVelInnovLength(ftype & velInnovLength) const`, `AP_NavEKF/EKFGSF_yaw.cpp:651-661`. -/
def getVelInnovLength (s : State) (velInnovLength : Binary64) : Binary64 × Bool := Id.run do
  let mut velInnovLength := velInnovLength
  if !s.vel_fuse_running then
    return (velInnovLength, false)
  velInnovLength := (Binary64.ofBits 0x0000000000000000 /- 0.0f -/)
  for mdl_idx' in [0:5] do
    let mdl_idx : UInt8 := Nat.toUInt8 mdl_idx'
    velInnovLength := velInnovLength + s.GSF.weights[UInt8.toNat mdl_idx]! * Binary64.sqrt (Estimator_lib.sq_double s.EKF[UInt8.toNat mdl_idx]!.innov[0]! + Estimator_lib.sq_double s.EKF[UInt8.toNat mdl_idx]!.innov[1]!)
  return (velInnovLength, true)

end EKFGSF_yaw

namespace EKFGSF_yaw

/-- C++ `void EKFGSF_yaw::resetEKFGSF()`, `AP_NavEKF/EKFGSF_yaw.cpp:546-565`. -/
def resetEKFGSF (s : State) : State := Id.run do
  let mut s := s
  s := { s with GSF := { yaw := (Binary64.ofBits 0x0000000000000000 /- 0.0 -/), yaw_variance := (Binary64.ofBits 0x0000000000000000 /- 0.0 -/), weights := Array.replicate 5 (Binary64.ofBits 0x0000000000000000 /- 0.0 -/) } }
  s := { s with vel_fuse_running := false }
  s := { s with run_ekf_gsf := false }
  s := { s with EKF := Array.replicate 5 { X := Array.replicate 3 (Binary64.ofBits 0x0000000000000000 /- 0.0 -/), P := Array.replicate 9 (Binary64.ofBits 0x0000000000000000 /- 0.0 -/), S := Array.replicate 4 (Binary64.ofBits 0x0000000000000000 /- 0.0 -/), innov := Array.replicate 2 (Binary64.ofBits 0x0000000000000000 /- 0.0 -/) } }
  let yaw_increment : Binary64 := (Binary64.ofBits 0x401921fb60000000 /- (double)13176795/2097152 -/) / (Binary64.ofBits 0x4014000000000000 /- (double)5 -/)
  for mdl_idx' in [0:5] do
    let mdl_idx : UInt8 := Nat.toUInt8 mdl_idx'
    let t'1 := (Binary64.ofBits 0xc00921fb60000000 /- (double)-13176795/4194304 -/) + ((Binary64.ofBits 0x3fe0000000000000 /- 0.5f -/) * yaw_increment) + (UInt8.toBinary64 mdl_idx * yaw_increment)
    let t'2 := UInt8.toNat mdl_idx
    let t'3 := s.EKF
    s := { s with EKF := #[] }
    let t'4 := t'3[t'2]!
    let t'3 := t'3.set! t'2 default
    let t'5 := t'4.X
    let t'4 := { t'4 with X := #[] }
    let t'4 := { t'4 with X := t'5.set! 2 t'1 }
    s := { s with EKF := t'3.set! t'2 t'4 }
    s := { s with GSF.weights := s.GSF.weights.set! (UInt8.toNat mdl_idx) ((Binary64.ofBits 0x3ff0000000000000 /- 1.0f -/) / (Binary64.ofBits 0x4014000000000000 /- (double)5 -/)) }
    s := { s with GSF.yaw_variance := Estimator_lib.sq_double ((Binary64.ofBits 0x3fe0000000000000 /- 0.5f -/) * yaw_increment) }
    let t'6 := UInt8.toNat mdl_idx
    let t'7 := s.EKF
    s := { s with EKF := #[] }
    let t'8 := t'7[t'6]!
    let t'7 := t'7.set! t'6 default
    let t'9 := t'8.P
    let t'8 := { t'8 with P := #[] }
    let t'8 := { t'8 with P := t'9.set! 8 s.GSF.yaw_variance }
    s := { s with EKF := t'7.set! t'6 t'8 }
  return s

end EKFGSF_yaw

namespace EKFGSF_yaw

/-- C++ `void EKFGSF_yaw::alignYaw()`, `AP_NavEKF/EKFGSF_yaw.cpp:290-315`. -/
def alignYaw (s : State) : State := Id.run do
  let mut s := s
  for mdl_idx' in [0:5] do
    let mdl_idx : UInt8 := Nat.toUInt8 mdl_idx'
    if Binary64.abs s.AHRS[UInt8.toNat mdl_idx]!.R.c.x < Binary64.abs s.AHRS[UInt8.toNat mdl_idx]!.R.c.y then
      let mut roll : Binary64 := (Binary64.ofBits 0x0000000000000000 /- 0.0 -/)  -- uninitialized in C++; assigned before every read
      let mut pitch : Binary64 := (Binary64.ofBits 0x0000000000000000 /- 0.0 -/)  -- uninitialized in C++; assigned before every read
      let mut yaw : Binary64 := (Binary64.ofBits 0x0000000000000000 /- 0.0 -/)  -- uninitialized in C++; assigned before every read
      let (t'1, t'2, t'3) := Matrix3_double.to_euler s.AHRS[UInt8.toNat mdl_idx]!.R true roll true pitch true yaw
      roll := t'1
      pitch := t'2
      yaw := t'3
      yaw := Estimator_lib.wrap_PI_double s.EKF[UInt8.toNat mdl_idx]!.X[2]!
      s := { s with AHRS := s.AHRS.set! (UInt8.toNat mdl_idx) ({ s.AHRS[UInt8.toNat mdl_idx]! with R := Matrix3_double.from_euler s.AHRS[UInt8.toNat mdl_idx]!.R roll pitch yaw }) }
    else
      let mut euler312 : Vector3p.State := Matrix3_double.to_euler312 s.AHRS[UInt8.toNat mdl_idx]!.R
      euler312 := { euler312 with z := Estimator_lib.wrap_PI_double s.EKF[UInt8.toNat mdl_idx]!.X[2]! }
      s := { s with AHRS := s.AHRS.set! (UInt8.toNat mdl_idx) ({ s.AHRS[UInt8.toNat mdl_idx]! with R := Matrix3_double.from_euler312 s.AHRS[UInt8.toNat mdl_idx]!.R euler312.x euler312.y euler312.z }) }
  return s

/-- C++ `bool EKFGSF_yaw::correct(const uint8_t mdl_idx, const Vector2F & vel, const ftype velObsVar)`, `AP_NavEKF/EKFGSF_yaw.cpp:398-544`. -/
def correct (s : State) (mdl_idx : UInt8) (vel : Vector2p.State) (velObsVar : Binary64) : State × Bool := Id.run do
  let mut s := s
  let t'1 := s.EKF[UInt8.toNat mdl_idx]!.X[0]! - vel.x
  let t'2 := UInt8.toNat mdl_idx
  let t'3 := s.EKF
  s := { s with EKF := #[] }
  let t'4 := t'3[t'2]!
  let t'3 := t'3.set! t'2 default
  let t'5 := t'4.innov
  let t'4 := { t'4 with innov := #[] }
  let t'4 := { t'4 with innov := t'5.set! 0 t'1 }
  s := { s with EKF := t'3.set! t'2 t'4 }
  let t'6 := s.EKF[UInt8.toNat mdl_idx]!.X[1]! - vel.y
  let t'7 := UInt8.toNat mdl_idx
  let t'8 := s.EKF
  s := { s with EKF := #[] }
  let t'9 := t'8[t'7]!
  let t'8 := t'8.set! t'7 default
  let t'10 := t'9.innov
  let t'9 := { t'9 with innov := #[] }
  let t'9 := { t'9 with innov := t'10.set! 1 t'6 }
  s := { s with EKF := t'8.set! t'7 t'9 }
  let P00 : Binary64 := s.EKF[UInt8.toNat mdl_idx]!.P[0]!
  let P01 : Binary64 := s.EKF[UInt8.toNat mdl_idx]!.P[1]!
  let P02 : Binary64 := s.EKF[UInt8.toNat mdl_idx]!.P[2]!
  let P10 : Binary64 := s.EKF[UInt8.toNat mdl_idx]!.P[3]!
  let P11 : Binary64 := s.EKF[UInt8.toNat mdl_idx]!.P[4]!
  let P12 : Binary64 := s.EKF[UInt8.toNat mdl_idx]!.P[5]!
  let P20 : Binary64 := s.EKF[UInt8.toNat mdl_idx]!.P[6]!
  let P21 : Binary64 := s.EKF[UInt8.toNat mdl_idx]!.P[7]!
  let P22 : Binary64 := s.EKF[UInt8.toNat mdl_idx]!.P[8]!
  let t'11 := P00 + velObsVar
  let t'12 := UInt8.toNat mdl_idx
  let t'13 := s.EKF
  s := { s with EKF := #[] }
  let t'14 := t'13[t'12]!
  let t'13 := t'13.set! t'12 default
  let t'15 := t'14.S
  let t'14 := { t'14 with S := #[] }
  let t'14 := { t'14 with S := t'15.set! 0 t'11 }
  s := { s with EKF := t'13.set! t'12 t'14 }
  let t'16 := P11 + velObsVar
  let t'17 := UInt8.toNat mdl_idx
  let t'18 := s.EKF
  s := { s with EKF := #[] }
  let t'19 := t'18[t'17]!
  let t'18 := t'18.set! t'17 default
  let t'20 := t'19.S
  let t'19 := { t'19 with S := #[] }
  let t'19 := { t'19 with S := t'20.set! 3 t'16 }
  s := { s with EKF := t'18.set! t'17 t'19 }
  let t'21 := UInt8.toNat mdl_idx
  let t'22 := s.EKF
  s := { s with EKF := #[] }
  let t'23 := t'22[t'21]!
  let t'22 := t'22.set! t'21 default
  let t'24 := t'23.S
  let t'23 := { t'23 with S := #[] }
  let t'23 := { t'23 with S := t'24.set! 1 P01 }
  s := { s with EKF := t'22.set! t'21 t'23 }
  let t'25 := UInt8.toNat mdl_idx
  let t'26 := s.EKF
  s := { s with EKF := #[] }
  let t'27 := t'26[t'25]!
  let t'26 := t'26.set! t'25 default
  let t'28 := t'27.S
  let t'27 := { t'27 with S := #[] }
  let t'27 := { t'27 with S := t'28.set! 2 P10 }
  s := { s with EKF := t'26.set! t'25 t'27 }
  let mut S_det_inv : Binary64 := (s.EKF[UInt8.toNat mdl_idx]!.S[0]! * s.EKF[UInt8.toNat mdl_idx]!.S[3]! - s.EKF[UInt8.toNat mdl_idx]!.S[1]! * s.EKF[UInt8.toNat mdl_idx]!.S[2]!)
  let mut innov_comp_scale_factor : Binary64 := (Binary64.ofBits 0x3ff0000000000000 /- 1.0f -/)
  if Binary64.abs S_det_inv > (Binary64.ofBits 0x3eb0c6f7a0000000 /- 1E-6f -/) then
    S_det_inv := (Binary64.ofBits 0x3ff0000000000000 /- 1.0f -/) / S_det_inv
    let S_inv_NN : Binary64 := s.EKF[UInt8.toNat mdl_idx]!.S[3]! * S_det_inv
    let S_inv_EE : Binary64 := s.EKF[UInt8.toNat mdl_idx]!.S[0]! * S_det_inv
    let S_inv_NE : Binary64 := s.EKF[UInt8.toNat mdl_idx]!.S[1]! * S_det_inv
    let test_ratio : Binary64 := s.EKF[UInt8.toNat mdl_idx]!.innov[0]! * (s.EKF[UInt8.toNat mdl_idx]!.innov[0]! * S_inv_NN + s.EKF[UInt8.toNat mdl_idx]!.innov[1]! * S_inv_NE) + s.EKF[UInt8.toNat mdl_idx]!.innov[1]! * (s.EKF[UInt8.toNat mdl_idx]!.innov[0]! * S_inv_NE + s.EKF[UInt8.toNat mdl_idx]!.innov[1]! * S_inv_EE)
    if test_ratio > (Binary64.ofBits 0x4039000000000000 /- 25.0f -/) then
      innov_comp_scale_factor := Binary64.sqrt ((Binary64.ofBits 0x4039000000000000 /- (double)25 -/) / test_ratio)
  else
    return (s, false)
  let t2 : Binary64 := P00 * velObsVar
  let t3 : Binary64 := P11 * velObsVar
  let t4 : Binary64 := velObsVar * velObsVar
  let t5 : Binary64 := P00 * P11
  let t9 : Binary64 := P01 * P10
  let t6 : Binary64 := t2 + t3 + t4 + t5 - t9
  let mut t7 : Binary64 := (Binary64.ofBits 0x0000000000000000 /- 0.0 -/)  -- uninitialized in C++; assigned before every read
  if Binary64.abs t6 > (Binary64.ofBits 0x3eb0c6f7a0000000 /- 1e-6f -/) then
    t7 := (Binary64.ofBits 0x3ff0000000000000 /- 1.0f -/) / t6
  else
    return (s, false)
  let t8 : Binary64 := P11 + velObsVar
  let t10 : Binary64 := P00 + velObsVar
  let mut K : Array Binary64 := Array.replicate 6 (Binary64.ofBits 0x0000000000000000 /- 0.0 -/)  -- uninitialized in C; every element is written before it is read
  K := K.set! 0 (-P01 * P10 * t7 + P00 * t7 * t8)
  K := K.set! 1 (-P00 * P01 * t7 + P01 * t7 * t10)
  K := K.set! 2 (-P10 * P11 * t7 + P10 * t7 * t8)
  K := K.set! 3 (-P01 * P10 * t7 + P11 * t7 * t10)
  K := K.set! 4 (-P10 * P21 * t7 + P20 * t7 * t8)
  K := K.set! 5 (-P01 * P20 * t7 + P21 * t7 * t10)
  let t11 : Binary64 := P00 * P01 * t7
  let t15 : Binary64 := P01 * t7 * t10
  let t12 : Binary64 := t11 - t15
  let t13 : Binary64 := P01 * P10 * t7
  let t16 : Binary64 := P00 * t7 * t8
  let t14 : Binary64 := t13 - t16
  let t17 : Binary64 := t8 * t12
  let t18 : Binary64 := P01 * t14
  let t19 : Binary64 := t17 + t18
  let t20 : Binary64 := t10 * t14
  let t21 : Binary64 := P10 * t12
  let t22 : Binary64 := t20 + t21
  let t27 : Binary64 := P11 * t7 * t10
  let t23 : Binary64 := t13 - t27
  let t24 : Binary64 := P10 * P11 * t7
  let t26 : Binary64 := P10 * t7 * t8
  let t25 : Binary64 := t24 - t26
  let t28 : Binary64 := t8 * t23
  let t29 : Binary64 := P01 * t25
  let t30 : Binary64 := t28 + t29
  let t31 : Binary64 := t10 * t25
  let t32 : Binary64 := P10 * t23
  let t33 : Binary64 := t31 + t32
  let t34 : Binary64 := P01 * P20 * t7
  let t38 : Binary64 := P21 * t7 * t10
  let t35 : Binary64 := t34 - t38
  let t36 : Binary64 := P10 * P21 * t7
  let t39 : Binary64 := P20 * t7 * t8
  let t37 : Binary64 := t36 - t39
  let t40 : Binary64 := t8 * t35
  let t41 : Binary64 := P01 * t37
  let t42 : Binary64 := t40 + t41
  let t43 : Binary64 := t10 * t37
  let t44 : Binary64 := P10 * t35
  let t45 : Binary64 := t43 + t44
  let min_var : Binary64 := (Binary64.ofBits 0x3eb0c6f7a0000000 /- 1e-6f -/)
  let t'29 := Binary64.fmax (P00 - t12 * t19 - t14 * t22) min_var
  let t'30 := UInt8.toNat mdl_idx
  let t'31 := s.EKF
  s := { s with EKF := #[] }
  let t'32 := t'31[t'30]!
  let t'31 := t'31.set! t'30 default
  let t'33 := t'32.P
  let t'32 := { t'32 with P := #[] }
  let t'32 := { t'32 with P := t'33.set! 0 t'29 }
  s := { s with EKF := t'31.set! t'30 t'32 }
  let t'34 := P01 - t19 * t23 - t22 * t25
  let t'35 := UInt8.toNat mdl_idx
  let t'36 := s.EKF
  s := { s with EKF := #[] }
  let t'37 := t'36[t'35]!
  let t'36 := t'36.set! t'35 default
  let t'38 := t'37.P
  let t'37 := { t'37 with P := #[] }
  let t'37 := { t'37 with P := t'38.set! 1 t'34 }
  s := { s with EKF := t'36.set! t'35 t'37 }
  let t'39 := P02 - t19 * t35 - t22 * t37
  let t'40 := UInt8.toNat mdl_idx
  let t'41 := s.EKF
  s := { s with EKF := #[] }
  let t'42 := t'41[t'40]!
  let t'41 := t'41.set! t'40 default
  let t'43 := t'42.P
  let t'42 := { t'42 with P := #[] }
  let t'42 := { t'42 with P := t'43.set! 2 t'39 }
  s := { s with EKF := t'41.set! t'40 t'42 }
  let t'44 := P10 - t12 * t30 - t14 * t33
  let t'45 := UInt8.toNat mdl_idx
  let t'46 := s.EKF
  s := { s with EKF := #[] }
  let t'47 := t'46[t'45]!
  let t'46 := t'46.set! t'45 default
  let t'48 := t'47.P
  let t'47 := { t'47 with P := #[] }
  let t'47 := { t'47 with P := t'48.set! 3 t'44 }
  s := { s with EKF := t'46.set! t'45 t'47 }
  let t'49 := Binary64.fmax (P11 - t23 * t30 - t25 * t33) min_var
  let t'50 := UInt8.toNat mdl_idx
  let t'51 := s.EKF
  s := { s with EKF := #[] }
  let t'52 := t'51[t'50]!
  let t'51 := t'51.set! t'50 default
  let t'53 := t'52.P
  let t'52 := { t'52 with P := #[] }
  let t'52 := { t'52 with P := t'53.set! 4 t'49 }
  s := { s with EKF := t'51.set! t'50 t'52 }
  let t'54 := P12 - t30 * t35 - t33 * t37
  let t'55 := UInt8.toNat mdl_idx
  let t'56 := s.EKF
  s := { s with EKF := #[] }
  let t'57 := t'56[t'55]!
  let t'56 := t'56.set! t'55 default
  let t'58 := t'57.P
  let t'57 := { t'57 with P := #[] }
  let t'57 := { t'57 with P := t'58.set! 5 t'54 }
  s := { s with EKF := t'56.set! t'55 t'57 }
  let t'59 := P20 - t12 * t42 - t14 * t45
  let t'60 := UInt8.toNat mdl_idx
  let t'61 := s.EKF
  s := { s with EKF := #[] }
  let t'62 := t'61[t'60]!
  let t'61 := t'61.set! t'60 default
  let t'63 := t'62.P
  let t'62 := { t'62 with P := #[] }
  let t'62 := { t'62 with P := t'63.set! 6 t'59 }
  s := { s with EKF := t'61.set! t'60 t'62 }
  let t'64 := P21 - t23 * t42 - t25 * t45
  let t'65 := UInt8.toNat mdl_idx
  let t'66 := s.EKF
  s := { s with EKF := #[] }
  let t'67 := t'66[t'65]!
  let t'66 := t'66.set! t'65 default
  let t'68 := t'67.P
  let t'67 := { t'67 with P := #[] }
  let t'67 := { t'67 with P := t'68.set! 7 t'64 }
  s := { s with EKF := t'66.set! t'65 t'67 }
  let t'69 := Binary64.fmax (P22 - t35 * t42 - t37 * t45) min_var
  let t'70 := UInt8.toNat mdl_idx
  let t'71 := s.EKF
  s := { s with EKF := #[] }
  let t'72 := t'71[t'70]!
  let t'71 := t'71.set! t'70 default
  let t'73 := t'72.P
  let t'72 := { t'72 with P := #[] }
  let t'72 := { t'72 with P := t'73.set! 8 t'69 }
  s := { s with EKF := t'71.set! t'70 t'72 }
  s := forceSymmetry s mdl_idx
  let yaw_prev : Binary64 := s.EKF[UInt8.toNat mdl_idx]!.X[2]!
  for obs_index' in [0:2] do
    let obs_index : UInt8 := Nat.toUInt8 obs_index'
    for row' in [0:3] do
      let row : UInt32 := Nat.toUInt32 row'
      let t'74 := s.EKF[UInt8.toNat mdl_idx]!.X[UInt32.toNat row]! - K[UInt32.toNat row * 2 + UInt8.toNat obs_index]! * s.EKF[UInt8.toNat mdl_idx]!.innov[UInt8.toNat obs_index]! * innov_comp_scale_factor
      let t'75 := UInt8.toNat mdl_idx
      let t'76 := s.EKF
      s := { s with EKF := #[] }
      let t'77 := t'76[t'75]!
      let t'76 := t'76.set! t'75 default
      let t'78 := UInt32.toNat row
      let t'79 := t'77.X
      let t'77 := { t'77 with X := #[] }
      let t'77 := { t'77 with X := t'79.set! t'78 t'74 }
      s := { s with EKF := t'76.set! t'75 t'77 }
  let yaw_delta : Binary64 := s.EKF[UInt8.toNat mdl_idx]!.X[2]! - yaw_prev
  let cos_yaw : Binary64 := Musl.cos.cos yaw_delta
  let sin_yaw : Binary64 := Musl.sin.sin yaw_delta
  let mut R_prev : Array Binary64 := Array.replicate 6 (Binary64.ofBits 0x0000000000000000 /- 0.0 -/)  -- uninitialized in C; every element is written before it is read
  let t'80 := s.AHRS[UInt8.toNat mdl_idx]!.R
  R_prev := #[t'80.a.x, t'80.a.y, t'80.a.z, t'80.b.x, t'80.b.y, t'80.b.z]
  s := { s with AHRS := s.AHRS.set! (UInt8.toNat mdl_idx) ({ s.AHRS[UInt8.toNat mdl_idx]! with R.a.x := R_prev[0]! * cos_yaw - R_prev[3]! * sin_yaw }) }
  s := { s with AHRS := s.AHRS.set! (UInt8.toNat mdl_idx) ({ s.AHRS[UInt8.toNat mdl_idx]! with R.a.y := R_prev[1]! * cos_yaw - R_prev[4]! * sin_yaw }) }
  s := { s with AHRS := s.AHRS.set! (UInt8.toNat mdl_idx) ({ s.AHRS[UInt8.toNat mdl_idx]! with R.a.z := R_prev[2]! * cos_yaw - R_prev[5]! * sin_yaw }) }
  s := { s with AHRS := s.AHRS.set! (UInt8.toNat mdl_idx) ({ s.AHRS[UInt8.toNat mdl_idx]! with R.b.x := R_prev[0]! * sin_yaw + R_prev[3]! * cos_yaw }) }
  s := { s with AHRS := s.AHRS.set! (UInt8.toNat mdl_idx) ({ s.AHRS[UInt8.toNat mdl_idx]! with R.b.y := R_prev[1]! * sin_yaw + R_prev[4]! * cos_yaw }) }
  s := { s with AHRS := s.AHRS.set! (UInt8.toNat mdl_idx) ({ s.AHRS[UInt8.toNat mdl_idx]! with R.b.z := R_prev[2]! * sin_yaw + R_prev[5]! * cos_yaw }) }
  return (s, true)

/-- C++ `ftype EKFGSF_yaw::gaussianDensity(const uint8_t mdl_idx) const`, `AP_NavEKF/EKFGSF_yaw.cpp:568-594`. -/
def gaussianDensity (s : State) (mdl_idx : UInt8) : Binary64 := Id.run do
  let t2 : Binary64 := s.EKF[UInt8.toNat mdl_idx]!.S[0]! * s.EKF[UInt8.toNat mdl_idx]!.S[3]!
  let t5 : Binary64 := s.EKF[UInt8.toNat mdl_idx]!.S[1]! * s.EKF[UInt8.toNat mdl_idx]!.S[2]!
  let t3 : Binary64 := t2 - t5
  let t4 : Binary64 := (Binary64.ofBits 0x3ff0000000000000 /- 1.0f -/) / Estimator_lib.MAX_double_float t3 (Binary32.ofBits 0x2b8cbccc /- 1e-12f -/)
  let mut invMat : Array Binary64 := Array.replicate 4 (Binary64.ofBits 0x0000000000000000 /- 0.0 -/)  -- uninitialized in C; every element is written before it is read
  invMat := invMat.set! 0 (t4 * s.EKF[UInt8.toNat mdl_idx]!.S[3]!)
  invMat := invMat.set! 3 (t4 * s.EKF[UInt8.toNat mdl_idx]!.S[0]!)
  invMat := invMat.set! 1 (-t4 * s.EKF[UInt8.toNat mdl_idx]!.S[1]!)
  invMat := invMat.set! 2 (-t4 * s.EKF[UInt8.toNat mdl_idx]!.S[2]!)
  let mut tempVec : Array Binary64 := Array.replicate 2 (Binary64.ofBits 0x0000000000000000 /- 0.0 -/)  -- uninitialized in C; every element is written before it is read
  tempVec := tempVec.set! 0 (invMat[0]! * s.EKF[UInt8.toNat mdl_idx]!.innov[0]! + invMat[1]! * s.EKF[UInt8.toNat mdl_idx]!.innov[1]!)
  tempVec := tempVec.set! 1 (invMat[2]! * s.EKF[UInt8.toNat mdl_idx]!.innov[0]! + invMat[3]! * s.EKF[UInt8.toNat mdl_idx]!.innov[1]!)
  let mut normDist : Binary64 := tempVec[0]! * s.EKF[UInt8.toNat mdl_idx]!.innov[0]! + tempVec[1]! * s.EKF[UInt8.toNat mdl_idx]!.innov[1]!
  normDist := Binary32.toBinary64 (Musl.expf.expf (Binary64.toBinary32 ((Binary64.ofBits 0xbfe0000000000000 /- -0.5f -/) * normDist)))
  normDist := normDist * (Binary64.sqrt t4 / (Binary64.ofBits 0x401921fb60000000 /- (double)13176795/2097152 -/))
  return normDist

/-- C++ `void EKFGSF_yaw::fuseVelData(const Vector2F & vel, const ftype velAcc)`, `AP_NavEKF/EKFGSF_yaw.cpp:136-192`. -/
def fuseVelData (s : State) (vel : Vector2p.State) (velAcc : Binary64) : State := Id.run do
  let mut s := s
  let velObsVar : Binary64 := Estimator_lib.sq_double (Binary64.fmax velAcc (Binary32.toBinary64 (Binary32.ofBits 0x3f000000 /- 0.5 -/)))
  if s.run_ekf_gsf then
    if !s.vel_fuse_running then
      s := resetEKFGSF s
      for mdl_idx' in [0:5] do
        let mdl_idx : UInt8 := Nat.toUInt8 mdl_idx'
        let t'1 := UInt8.toNat mdl_idx
        let t'2 := s.EKF
        s := { s with EKF := #[] }
        let t'3 := t'2[t'1]!
        let t'2 := t'2.set! t'1 default
        let t'4 := t'3.X
        let t'3 := { t'3 with X := #[] }
        let t'3 := { t'3 with X := t'4.set! 0 vel.x }
        s := { s with EKF := t'2.set! t'1 t'3 }
        let t'5 := UInt8.toNat mdl_idx
        let t'6 := s.EKF
        s := { s with EKF := #[] }
        let t'7 := t'6[t'5]!
        let t'6 := t'6.set! t'5 default
        let t'8 := t'7.X
        let t'7 := { t'7 with X := #[] }
        let t'7 := { t'7 with X := t'8.set! 1 vel.y }
        s := { s with EKF := t'6.set! t'5 t'7 }
        let t'9 := UInt8.toNat mdl_idx
        let t'10 := s.EKF
        s := { s with EKF := #[] }
        let t'11 := t'10[t'9]!
        let t'10 := t'10.set! t'9 default
        let t'12 := t'11.P
        let t'11 := { t'11 with P := #[] }
        let t'11 := { t'11 with P := t'12.set! 0 velObsVar }
        s := { s with EKF := t'10.set! t'9 t'11 }
        let t'13 := UInt8.toNat mdl_idx
        let t'14 := s.EKF
        s := { s with EKF := #[] }
        let t'15 := t'14[t'13]!
        let t'14 := t'14.set! t'13 default
        let t'16 := t'15.P
        let t'15 := { t'15 with P := #[] }
        let t'15 := { t'15 with P := t'16.set! 4 velObsVar }
        s := { s with EKF := t'14.set! t'13 t'15 }
      s := alignYaw s
      s := { s with vel_fuse_running := true }
    else
      let mut total_w : Binary64 := (Binary64.ofBits 0x0000000000000000 /- 0.0f -/)
      let mut newWeight : Array Binary64 := Array.replicate 5 (Binary64.ofBits 0x0000000000000000 /- 0.0 -/)  -- uninitialized in C; every element is written before it is read
      let mut state_update_failed : Bool := false
      for mdl_idx'2' in [0:5] do
        let mdl_idx'2 : UInt8 := Nat.toUInt8 mdl_idx'2'
        let (t'17, t'18) := correct s mdl_idx'2 vel velObsVar
        s := t'17
        if !t'18 then
          state_update_failed := true
      if !state_update_failed then
        let min_weight : Binary64 := (Binary64.ofBits 0x3ee4f8b580000000 /- 1e-5f -/)
        s := { s with n_clips := Int8.toUInt8 (Int32.toInt8 (0 : Int32)) }
        for mdl_idx'3' in [0:5] do
          let mdl_idx'3 : UInt8 := Nat.toUInt8 mdl_idx'3'
          newWeight := newWeight.set! (UInt8.toNat mdl_idx'3) (gaussianDensity s mdl_idx'3 * s.GSF.weights[UInt8.toNat mdl_idx'3]!)
          if newWeight[UInt8.toNat mdl_idx'3]! < min_weight then
            s := { s with n_clips := s.n_clips + (1 : UInt8) }
            newWeight := newWeight.set! (UInt8.toNat mdl_idx'3) min_weight
          total_w := total_w + newWeight[UInt8.toNat mdl_idx'3]!
        if s.vel_fuse_running && decide (UInt8.toUInt32 s.n_clips < (5 : UInt32)) then
          let total_w_inv : Binary64 := (Binary64.ofBits 0x3ff0000000000000 /- 1.0f -/) / total_w
          for mdl_idx'4' in [0:5] do
            let mdl_idx'4 : UInt8 := Nat.toUInt8 mdl_idx'4'
            s := { s with GSF.weights := s.GSF.weights.set! (UInt8.toNat mdl_idx'4) (newWeight[UInt8.toNat mdl_idx'4]! * total_w_inv) }
        else
          s := resetEKFGSF s
  return s

end EKFGSF_yaw

/-- C++ `enum class NavFilterStatusBit`, `AP_NavEKF/AP_Nav_Common.h:26-46`. -/
inductive NavFilterStatusBit where
  | ATTITUDE_VALID
  | HORIZ_VEL
  | VERT_VEL
  | HORIZ_POS_REL
  | HORIZ_POS_ABS
  | VERT_POS
  | TERRAIN_ALT
  | CONST_POS_MODE
  | PRED_HORIZ_POS_REL
  | PRED_HORIZ_POS_ABS
  | TAKEOFF_DETECTED
  | TAKEOFF_EXPECTED
  | TOUCHDOWN_EXPECTED
  | USING_GPS
  | GPS_GLITCHING
  | GPS_QUALITY_GOOD
  | INITALIZED
  | REJECTING_AIRSPEED
  | DEAD_RECKONING
deriving DecidableEq, Inhabited

/-- The value of each enumerator of `NavFilterStatusBit` (underlying type `int32_t`). -/
def NavFilterStatusBit.toInt : NavFilterStatusBit → Int32
  | .ATTITUDE_VALID => (1 : Int32)
  | .HORIZ_VEL => (2 : Int32)
  | .VERT_VEL => (4 : Int32)
  | .HORIZ_POS_REL => (8 : Int32)
  | .HORIZ_POS_ABS => (16 : Int32)
  | .VERT_POS => (32 : Int32)
  | .TERRAIN_ALT => (64 : Int32)
  | .CONST_POS_MODE => (128 : Int32)
  | .PRED_HORIZ_POS_REL => (256 : Int32)
  | .PRED_HORIZ_POS_ABS => (512 : Int32)
  | .TAKEOFF_DETECTED => (1024 : Int32)
  | .TAKEOFF_EXPECTED => (2048 : Int32)
  | .TOUCHDOWN_EXPECTED => (4096 : Int32)
  | .USING_GPS => (8192 : Int32)
  | .GPS_GLITCHING => (16384 : Int32)
  | .GPS_QUALITY_GOOD => (32768 : Int32)
  | .INITALIZED => (65536 : Int32)
  | .REJECTING_AIRSPEED => (131072 : Int32)
  | .DEAD_RECKONING => (262144 : Int32)

namespace AP_NavEKF_Source

/-- C++ `uint8_t AP_NavEKF_Source::get_active_source_set() const`, `AP_NavEKF/AP_NavEKF_Source.cpp:594-597`. -/
def get_active_source_set (s : State) : UInt8 := Id.run do
  return s.active_source_set

end AP_NavEKF_Source

namespace AP_NavEKF_Source

/-- C++ `enum class AP_NavEKF_Source::SourceSetSelection`, `AP_NavEKF/AP_NavEKF_Source.h:56-60`. -/
inductive SourceSetSelection where
  | PRIMARY
  | SECONDARY
  | TERTIARY
deriving DecidableEq, Inhabited

/-- The value of each enumerator of `AP_NavEKF_Source::SourceSetSelection` (underlying type `uint8_t`). -/
def SourceSetSelection.toInt : SourceSetSelection → UInt8
  | .PRIMARY => (0 : UInt8)
  | .SECONDARY => (1 : UInt8)
  | .TERTIARY => (2 : UInt8)

/-- The enumerator of `AP_NavEKF_Source::SourceSetSelection` with value `v` (the C++ converts only enumerator values; any other
value gives the first enumerator, the `Inhabited` default). -/
def SourceSetSelection.ofInt (v : UInt8) : SourceSetSelection :=
  if v == (0 : UInt8) then .PRIMARY
  else if v == (1 : UInt8) then .SECONDARY
  else if v == (2 : UInt8) then .TERTIARY
  else default

/-- C++ `void AP_NavEKF_Source::setPosVelYawSourceSet(SourceSetSelection source_set_idx)`, `AP_NavEKF/AP_NavEKF_Source.cpp:152-166`. -/
def setPosVelYawSourceSet (s : State) (source_set_idx : AP_NavEKF_Source.SourceSetSelection) : State := Id.run do
  let mut s := s
  if UInt32.toInt32 (UInt8.toUInt32 (AP_NavEKF_Source.SourceSetSelection.toInt source_set_idx)) < (3 : Int32) then
    s := { s with active_source_set := AP_NavEKF_Source.SourceSetSelection.toInt source_set_idx }
  return s

end AP_NavEKF_Source

namespace AP_NavEKF_Source

/-! Not emitted, since they have no effect in the model (they write neither the state, the
parameters nor a reference parameter; e.g. they only save parameters):
- C++ `void AP_NavEKF_Source::align_inactive_sources()`, `AP_NavEKF/AP_NavEKF_Source.cpp:251-327`.
-/

end AP_NavEKF_Source

/-- C++ `struct EKF_obs_element_t`, `AP_NavEKF/EKF_Buffer.h:9-12`. -/
structure EKF_obs_element_t where
  /-- `uint32_t time_ms` of `EKF_obs_element_t` (`AP_NavEKF/EKF_Buffer.h:11`). -/
  time_ms : UInt32 := (0 : UInt32)
deriving Inhabited

/-- C++ `struct log_KY0`, `AP_NavEKF/LogStructure.h:21-37`. -/
structure log_KY0 where
  /-- `uint8_t head1` of `log_KY0` (`AP_NavEKF/LogStructure.h:22`). -/
  head1 : UInt8 := (0 : UInt8)
  /-- `uint8_t head2` of `log_KY0` (`AP_NavEKF/LogStructure.h:22`). -/
  head2 : UInt8 := (0 : UInt8)
  /-- `uint8_t msgid` of `log_KY0` (`AP_NavEKF/LogStructure.h:22`). -/
  msgid : UInt8 := (0 : UInt8)
  /-- `uint64_t time_us` of `log_KY0` (`AP_NavEKF/LogStructure.h:23`). -/
  time_us : UInt64 := (0 : UInt64)
  /-- `uint8_t core` of `log_KY0` (`AP_NavEKF/LogStructure.h:24`). -/
  core : UInt8 := (0 : UInt8)
  /-- `float yaw_composite` of `log_KY0` (`AP_NavEKF/LogStructure.h:25`). -/
  yaw_composite : Binary32 := (Binary32.ofBits 0x00000000 /- 0.0 -/)
  /-- `float yaw_composite_variance` of `log_KY0` (`AP_NavEKF/LogStructure.h:26`). -/
  yaw_composite_variance : Binary32 := (Binary32.ofBits 0x00000000 /- 0.0 -/)
  /-- `float yaw0` of `log_KY0` (`AP_NavEKF/LogStructure.h:27`). -/
  yaw0 : Binary32 := (Binary32.ofBits 0x00000000 /- 0.0 -/)
  /-- `float yaw1` of `log_KY0` (`AP_NavEKF/LogStructure.h:28`). -/
  yaw1 : Binary32 := (Binary32.ofBits 0x00000000 /- 0.0 -/)
  /-- `float yaw2` of `log_KY0` (`AP_NavEKF/LogStructure.h:29`). -/
  yaw2 : Binary32 := (Binary32.ofBits 0x00000000 /- 0.0 -/)
  /-- `float yaw3` of `log_KY0` (`AP_NavEKF/LogStructure.h:30`). -/
  yaw3 : Binary32 := (Binary32.ofBits 0x00000000 /- 0.0 -/)
  /-- `float yaw4` of `log_KY0` (`AP_NavEKF/LogStructure.h:31`). -/
  yaw4 : Binary32 := (Binary32.ofBits 0x00000000 /- 0.0 -/)
  /-- `float wgt0` of `log_KY0` (`AP_NavEKF/LogStructure.h:32`). -/
  wgt0 : Binary32 := (Binary32.ofBits 0x00000000 /- 0.0 -/)
  /-- `float wgt1` of `log_KY0` (`AP_NavEKF/LogStructure.h:33`). -/
  wgt1 : Binary32 := (Binary32.ofBits 0x00000000 /- 0.0 -/)
  /-- `float wgt2` of `log_KY0` (`AP_NavEKF/LogStructure.h:34`). -/
  wgt2 : Binary32 := (Binary32.ofBits 0x00000000 /- 0.0 -/)
  /-- `float wgt3` of `log_KY0` (`AP_NavEKF/LogStructure.h:35`). -/
  wgt3 : Binary32 := (Binary32.ofBits 0x00000000 /- 0.0 -/)
  /-- `float wgt4` of `log_KY0` (`AP_NavEKF/LogStructure.h:36`). -/
  wgt4 : Binary32 := (Binary32.ofBits 0x00000000 /- 0.0 -/)
deriving Inhabited

/-- C++ `struct log_KY1`, `AP_NavEKF/LogStructure.h:54-68`. -/
structure log_KY1 where
  /-- `uint8_t head1` of `log_KY1` (`AP_NavEKF/LogStructure.h:55`). -/
  head1 : UInt8 := (0 : UInt8)
  /-- `uint8_t head2` of `log_KY1` (`AP_NavEKF/LogStructure.h:55`). -/
  head2 : UInt8 := (0 : UInt8)
  /-- `uint8_t msgid` of `log_KY1` (`AP_NavEKF/LogStructure.h:55`). -/
  msgid : UInt8 := (0 : UInt8)
  /-- `uint64_t time_us` of `log_KY1` (`AP_NavEKF/LogStructure.h:56`). -/
  time_us : UInt64 := (0 : UInt64)
  /-- `uint8_t core` of `log_KY1` (`AP_NavEKF/LogStructure.h:57`). -/
  core : UInt8 := (0 : UInt8)
  /-- `float ivn0` of `log_KY1` (`AP_NavEKF/LogStructure.h:58`). -/
  ivn0 : Binary32 := (Binary32.ofBits 0x00000000 /- 0.0 -/)
  /-- `float ivn1` of `log_KY1` (`AP_NavEKF/LogStructure.h:59`). -/
  ivn1 : Binary32 := (Binary32.ofBits 0x00000000 /- 0.0 -/)
  /-- `float ivn2` of `log_KY1` (`AP_NavEKF/LogStructure.h:60`). -/
  ivn2 : Binary32 := (Binary32.ofBits 0x00000000 /- 0.0 -/)
  /-- `float ivn3` of `log_KY1` (`AP_NavEKF/LogStructure.h:61`). -/
  ivn3 : Binary32 := (Binary32.ofBits 0x00000000 /- 0.0 -/)
  /-- `float ivn4` of `log_KY1` (`AP_NavEKF/LogStructure.h:62`). -/
  ivn4 : Binary32 := (Binary32.ofBits 0x00000000 /- 0.0 -/)
  /-- `float ive0` of `log_KY1` (`AP_NavEKF/LogStructure.h:63`). -/
  ive0 : Binary32 := (Binary32.ofBits 0x00000000 /- 0.0 -/)
  /-- `float ive1` of `log_KY1` (`AP_NavEKF/LogStructure.h:64`). -/
  ive1 : Binary32 := (Binary32.ofBits 0x00000000 /- 0.0 -/)
  /-- `float ive2` of `log_KY1` (`AP_NavEKF/LogStructure.h:65`). -/
  ive2 : Binary32 := (Binary32.ofBits 0x00000000 /- 0.0 -/)
  /-- `float ive3` of `log_KY1` (`AP_NavEKF/LogStructure.h:66`). -/
  ive3 : Binary32 := (Binary32.ofBits 0x00000000 /- 0.0 -/)
  /-- `float ive4` of `log_KY1` (`AP_NavEKF/LogStructure.h:67`). -/
  ive4 : Binary32 := (Binary32.ofBits 0x00000000 /- 0.0 -/)
deriving Inhabited

end Estimator_lib
