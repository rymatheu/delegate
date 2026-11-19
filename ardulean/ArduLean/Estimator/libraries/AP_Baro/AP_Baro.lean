import ArduLean.Musl.logf
import ArduLean.Musl.powf
import ArduLean.Estimator.libraries.AP_Math.AP_Math
import ArduLean.Estimator.World
import ArduLean.Estimator.libraries.Filter.Filter
import ArduLean.Estimator.libraries.AP_Param.AP_Param

/-!
ArduPilot `libraries/AP_Baro`, part 1 of 4. Sources: `libraries/AP_Baro/AP_Baro.h`, `libraries/AP_Baro/AP_Baro_atmosphere.cpp`, `libraries/AP_Baro/AP_Baro_Backend.h`, `libraries/AP_Baro/AP_Baro.cpp`, `libraries/AP_Baro/AP_Baro_SITL.h`.

Items of `lean/Estimator_lib.lean` (the estimator translation), unchanged; placed by `tools/split_modules.py` (`ArduLean/Estimator/INDEX.md`).
-/

open FloatLib.Floats (Binary32 Binary64)

set_option maxRecDepth 200000
-- AP_DAL's `const log_RISH old_RISH = _RISH;` read only by WRITE_REPLAY_BLOCK_IFCHANGED, which is `(void)old`
-- without logging (HAL_LOGGING_ENABLED 0): an unused binding, as in the C++
set_option linter.unusedVariables false

namespace Estimator_lib

namespace AP_Baro

/-- C++ `enum AP_Baro::baro_type_t`, `AP_Baro/AP_Baro.h:45-48`. -/
inductive baro_type_t where
  | BARO_TYPE_AIR
  | BARO_TYPE_WATER
deriving DecidableEq, Inhabited

/-- The value of each enumerator of `AP_Baro::baro_type_t` (underlying type `uint32_t`). -/
def baro_type_t.toInt : baro_type_t → UInt32
  | .BARO_TYPE_AIR => (0 : UInt32)
  | .BARO_TYPE_WATER => (1 : UInt32)

/-- C++ `struct AP_Baro::(unnamed struct at AP_Baro/AP_Baro.h:289:5)`, `AP_Baro/AP_Baro.h:289-312`. -/
structure sensors_t where
  /-- `uint32_t last_update_ms` of `AP_Baro::(unnamed struct at AP_Baro/AP_Baro.h:289:5)` (`AP_Baro/AP_Baro.h:290`). -/
  last_update_ms : UInt32 := (0 : UInt32)
  /-- `uint32_t last_change_ms` of `AP_Baro::(unnamed struct at AP_Baro/AP_Baro.h:289:5)` (`AP_Baro/AP_Baro.h:291`). -/
  last_change_ms : UInt32 := (0 : UInt32)
  /-- `float pressure` of `AP_Baro::(unnamed struct at AP_Baro/AP_Baro.h:289:5)` (`AP_Baro/AP_Baro.h:292`). -/
  pressure : Binary32 := (Binary32.ofBits 0x00000000 /- 0.0 -/)
  /-- `float temperature` of `AP_Baro::(unnamed struct at AP_Baro/AP_Baro.h:289:5)` (`AP_Baro/AP_Baro.h:293`). -/
  temperature : Binary32 := (Binary32.ofBits 0x00000000 /- 0.0 -/)
  /-- `float altitude` of `AP_Baro::(unnamed struct at AP_Baro/AP_Baro.h:289:5)` (`AP_Baro/AP_Baro.h:294`). -/
  altitude : Binary32 := (Binary32.ofBits 0x00000000 /- 0.0 -/)
  /-- `AP_Float ground_pressure` of `AP_Baro::(unnamed struct at AP_Baro/AP_Baro.h:289:5)` (`AP_Baro/AP_Baro.h:295`). -/
  ground_pressure : AP_ParamT_float_4.State := {}
  /-- `float p_correction` of `AP_Baro::(unnamed struct at AP_Baro/AP_Baro.h:289:5)` (`AP_Baro/AP_Baro.h:296`). -/
  p_correction : Binary32 := (Binary32.ofBits 0x00000000 /- 0.0 -/)
  /-- `baro_type_t type` of `AP_Baro::(unnamed struct at AP_Baro/AP_Baro.h:289:5)` (`AP_Baro/AP_Baro.h:297`). -/
  type : AP_Baro.baro_type_t := AP_Baro.baro_type_t.BARO_TYPE_AIR
  /-- `bool healthy` of `AP_Baro::(unnamed struct at AP_Baro/AP_Baro.h:289:5)` (`AP_Baro/AP_Baro.h:298`). -/
  healthy : Bool := false
  /-- `bool alt_ok` of `AP_Baro::(unnamed struct at AP_Baro/AP_Baro.h:289:5)` (`AP_Baro/AP_Baro.h:299`). -/
  alt_ok : Bool := false
  /-- `bool calibrated` of `AP_Baro::(unnamed struct at AP_Baro/AP_Baro.h:289:5)` (`AP_Baro/AP_Baro.h:300`). -/
  calibrated : Bool := false
  /-- `AP_UInt32 bus_id` of `AP_Baro::(unnamed struct at AP_Baro/AP_Baro.h:289:5)` (`AP_Baro/AP_Baro.h:301`). -/
  bus_id : AP_ParamT_unsigned_int_3.State := {}
deriving Inhabited

end AP_Baro

namespace AP_Baro

/-- State of C++ `AP_Baro` (`AP_Baro/AP_Baro.h:27-397`): its data members. -/
structure State where
  /-- `uint8_t _num_drivers` of `AP_Baro` (`AP_Baro/AP_Baro.h:240`). -/
  _num_drivers : UInt8 := (0 : UInt8)
  /-- `AP_Baro_Backend * drivers[3]` of `AP_Baro` (`AP_Baro/AP_Baro.h:241`). -/
  drivers : Array WPtr := Array.replicate 3 WPtr.null
  /-- `uint8_t _num_sensors` of `AP_Baro` (`AP_Baro/AP_Baro.h:244`). -/
  _num_sensors : UInt8 := (0 : UInt8)
  /-- `uint8_t _primary` of `AP_Baro` (`AP_Baro/AP_Baro.h:247`). -/
  _primary : UInt8 := (0 : UInt8)
  /-- `uint32_t _log_baro_bit` of `AP_Baro` (`AP_Baro/AP_Baro.h:249`). -/
  _log_baro_bit : UInt32 := Int32.toUInt32 (-(1 : Int32))
  /-- `bool init_done` of `AP_Baro` (`AP_Baro/AP_Baro.h:251`). -/
  init_done : Bool := false
  /-- `uint8_t msp_instance_mask` of `AP_Baro` (`AP_Baro/AP_Baro.h:253`). -/
  msp_instance_mask : UInt8 := (0 : UInt8)
  /-- `struct (unnamed struct at AP_Baro/AP_Baro.h:289:5) sensors[3]` of `AP_Baro` (`AP_Baro/AP_Baro.h:312`). -/
  sensors : Array AP_Baro.sensors_t := Array.replicate 3 {}
  /-- `AP_Float _alt_offset` of `AP_Baro` (`AP_Baro/AP_Baro.h:314`). -/
  _alt_offset : AP_ParamT_float_4.State := {}
  /-- `float _alt_offset_active` of `AP_Baro` (`AP_Baro/AP_Baro.h:315`). -/
  _alt_offset_active : Binary32 := (Binary32.ofBits 0x00000000 /- 0.0 -/)
  /-- `float _EAS2TAS` of `AP_Baro` (`AP_Baro/AP_Baro.h:316`). -/
  _EAS2TAS : Binary32 := (Binary32.ofBits 0x3f800000 /- 1.0 -/)
  /-- `AP_Float _field_elevation` of `AP_Baro` (`AP_Baro/AP_Baro.h:323`). -/
  _field_elevation : AP_ParamT_float_4.State := {}
  /-- `float _field_elevation_active` of `AP_Baro` (`AP_Baro/AP_Baro.h:324`). -/
  _field_elevation_active : Binary32 := (Binary32.ofBits 0x00000000 /- 0.0 -/)
  /-- `uint32_t _field_elevation_last_ms` of `AP_Baro` (`AP_Baro/AP_Baro.h:325`). -/
  _field_elevation_last_ms : UInt32 := (0 : UInt32)
  /-- `AP_Int8 _primary_baro` of `AP_Baro` (`AP_Baro/AP_Baro.h:326`). -/
  _primary_baro : AP_ParamT_signed_char_1.State := {}
  /-- `AP_Int8 _ext_bus` of `AP_Baro` (`AP_Baro/AP_Baro.h:327`). -/
  _ext_bus : AP_ParamT_signed_char_1.State := {}
  /-- `float _external_temperature` of `AP_Baro` (`AP_Baro/AP_Baro.h:328`). -/
  _external_temperature : Binary32 := (Binary32.ofBits 0x00000000 /- 0.0 -/)
  /-- `uint32_t _last_external_temperature_ms` of `AP_Baro` (`AP_Baro/AP_Baro.h:329`). -/
  _last_external_temperature_ms : UInt32 := (0 : UInt32)
  /-- `DerivativeFilterFloat_Size7 _climb_rate_filter` of `AP_Baro` (`AP_Baro/AP_Baro.h:330`). -/
  _climb_rate_filter : DerivativeFilterFloat_Size7.State := DerivativeFilterFloat_Size7.init
  /-- `AP_Float _specific_gravity` of `AP_Baro` (`AP_Baro/AP_Baro.h:331`). -/
  _specific_gravity : AP_ParamT_float_4.State := {}
  /-- `AP_Float _user_ground_temperature` of `AP_Baro` (`AP_Baro/AP_Baro.h:332`). -/
  _user_ground_temperature : AP_ParamT_float_4.State := {}
  /-- `float _guessed_ground_temperature` of `AP_Baro` (`AP_Baro/AP_Baro.h:333`). -/
  _guessed_ground_temperature : Binary32 := (Binary32.ofBits 0x00000000 /- 0.0 -/)
  /-- `uint32_t _last_notify_ms` of `AP_Baro` (`AP_Baro/AP_Baro.h:336`). -/
  _last_notify_ms : UInt32 := (0 : UInt32)
  /-- `AP_Int8 _filter_range` of `AP_Baro` (`AP_Baro/AP_Baro.h:358`). -/
  _filter_range : AP_ParamT_signed_char_1.State := {}
  /-- `AP_UInt32 _baro_probe_ext` of `AP_Baro` (`AP_Baro/AP_Baro.h:359`). -/
  _baro_probe_ext : AP_ParamT_unsigned_int_3.State := {}
  /-- `AP_Float _alt_error_max` of `AP_Baro` (`AP_Baro/AP_Baro.h:362`). -/
  _alt_error_max : AP_ParamT_float_4.State := {}
  /-- `AP_UInt16 _options` of `AP_Baro` (`AP_Baro/AP_Baro.h:365`). -/
  _options : AP_ParamT_unsigned_short_2.State := {}
deriving Inhabited

/-- Values C++ `AP_Baro` reads from objects outside the translation (--boundary): one field per distinct read, in first-use order. -/
structure Inputs where
  /-- `hal.util.was_watchdog_reset()` (first read at `AP_Baro/AP_Baro.cpp:305`). -/
  was_watchdog_reset : Bool := false
  /-- `hal.util.get_soft_armed()` (first read at `AP_Baro/AP_Baro.cpp:1005`). -/
  get_soft_armed : Bool := false
deriving Inhabited

/-- C++ `bool AP_Baro::healthy(uint8_t instance) const`, `AP_Baro/AP_Baro.cpp:988-994`. -/
def healthy_uint8_t (s : State) («instance» : UInt8) : Bool := Id.run do
  if UInt32.toInt32 (UInt8.toUInt32 «instance») ≥ (3 : Int32) then
    return false
  return s.sensors[UInt8.toNat «instance»]!.healthy && s.sensors[UInt8.toNat «instance»]!.alt_ok && s.sensors[UInt8.toNat «instance»]!.calibrated

/-- C++ `float AP_Baro::get_altitude(uint8_t instance) const`, `AP_Baro/AP_Baro.h:103`. -/
def get_altitude_uint8_t (s : State) («instance» : UInt8) : Binary32 := Id.run do
  return s.sensors[UInt8.toNat «instance»]!.altitude

/-- C++ `float AP_Baro::get_altitude_AMSL(uint8_t instance) const`, `AP_Baro/AP_Baro.h:106`. -/
def get_altitude_AMSL_uint8_t (s : State) («instance» : UInt8) : Binary32 := Id.run do
  return get_altitude_uint8_t s «instance» + s._field_elevation_active

/-- C++ `float AP_Baro::get_altitude_AMSL() const`, `AP_Baro/AP_Baro.h:107`. -/
def get_altitude_AMSL_void (s : State) : Binary32 := Id.run do
  return get_altitude_AMSL_uint8_t s s._primary

end AP_Baro

/-- C++ `const float radius_earth`, `AP_Baro/AP_Baro_atmosphere.cpp:73`. -/
def radius_earth : Binary32 := (Binary32.ofBits 0x4ac1fe3c /- 6356.766E3 -/)

namespace AP_Baro

/-- C++ `static float AP_Baro::geopotential_alt_to_geometric(float alt)`, `AP_Baro/AP_Baro_atmosphere.cpp:126-129`. -/
def geopotential_alt_to_geometric (alt : Binary32) : Binary32 := Id.run do
  return (Estimator_lib.radius_earth * alt) / (Estimator_lib.radius_earth - alt)

end AP_Baro

/-- C++ `const float R_specific`, `AP_Baro/AP_Baro_atmosphere.cpp:74`. -/
def R_specific : Binary32 := (Binary32.ofBits 0x438f86cb /- 287.053072 -/)

/-- C++ `struct (unnamed struct at AP_Baro/AP_Baro_atmosphere.cpp:76:14)`, `AP_Baro/AP_Baro_atmosphere.cpp:76-82`. -/
structure atmospheric_1976_consts_t where
  /-- `float amsl_m` of `(unnamed struct at AP_Baro/AP_Baro_atmosphere.cpp:76:14)` (`AP_Baro/AP_Baro_atmosphere.cpp:77`). -/
  amsl_m : Binary32 := (Binary32.ofBits 0x00000000 /- 0.0 -/)
  /-- `float temp_K` of `(unnamed struct at AP_Baro/AP_Baro_atmosphere.cpp:76:14)` (`AP_Baro/AP_Baro_atmosphere.cpp:78`). -/
  temp_K : Binary32 := (Binary32.ofBits 0x00000000 /- 0.0 -/)
  /-- `float pressure_Pa` of `(unnamed struct at AP_Baro/AP_Baro_atmosphere.cpp:76:14)` (`AP_Baro/AP_Baro_atmosphere.cpp:79`). -/
  pressure_Pa : Binary32 := (Binary32.ofBits 0x00000000 /- 0.0 -/)
  /-- `float density` of `(unnamed struct at AP_Baro/AP_Baro_atmosphere.cpp:76:14)` (`AP_Baro/AP_Baro_atmosphere.cpp:80`). -/
  density : Binary32 := (Binary32.ofBits 0x00000000 /- 0.0 -/)
  /-- `float temp_lapse` of `(unnamed struct at AP_Baro/AP_Baro_atmosphere.cpp:76:14)` (`AP_Baro/AP_Baro_atmosphere.cpp:81`). -/
  temp_lapse : Binary32 := (Binary32.ofBits 0x00000000 /- 0.0 -/)
deriving Inhabited

/-- C++ `const struct (unnamed struct at AP_Baro/AP_Baro_atmosphere.cpp:76:14) atmospheric_1976_consts[8]`, `AP_Baro/AP_Baro_atmosphere.cpp:76-91`. -/
def atmospheric_1976_consts : Array atmospheric_1976_consts_t := #[{ amsl_m := (Binary32.ofBits 0xc59c4000 /- -5000 -/), temp_K := (Binary32.ofBits 0x43a05333 /- 320.650 -/), pressure_Pa := (Binary32.ofBits 0x482d85c0 /- 177687 -/), density := (Binary32.ofBits 0x3ff7198b /- 1.930467 -/), temp_lapse := -(Binary32.ofBits 0x3bd4fdf4 /- 6.5E-3 -/) }, { amsl_m := (Binary32.ofBits 0x462be000 /- 11000 -/), temp_K := (Binary32.ofBits 0x4358a666 /- 216.650 -/), pressure_Pa := (Binary32.ofBits 0x46b0d033 /- 22632.1 -/), density := (Binary32.ofBits 0x3eba5376 /- 0.363918 -/), temp_lapse := (Binary32.ofBits 0x00000000 /- 0 -/) }, { amsl_m := (Binary32.ofBits 0x469c4000 /- 20000 -/), temp_K := (Binary32.ofBits 0x4358a666 /- 216.650 -/), pressure_Pa := (Binary32.ofBits 0x45ab171f /- 5474.89 -/), density := (Binary32.ofBits 0x3db44ba4 /- 8.80349E-2 -/), temp_lapse := (Binary32.ofBits 0x3a83126f /- 1E-3 -/) }, { amsl_m := (Binary32.ofBits 0x46fa0000 /- 32000 -/), temp_K := (Binary32.ofBits 0x4364a666 /- 228.650 -/), pressure_Pa := (Binary32.ofBits 0x44590137 /- 868.019 -/), density := (Binary32.ofBits 0x3c58adac /- 1.32250E-2 -/), temp_lapse := (Binary32.ofBits 0x3b378034 /- 2.8E-3 -/) }, { amsl_m := (Binary32.ofBits 0x47379800 /- 47000 -/), temp_K := (Binary32.ofBits 0x43875333 /- 270.650 -/), pressure_Pa := (Binary32.ofBits 0x42ddcfdf /- 110.906 -/), density := (Binary32.ofBits 0x3abb1bf5 /- 1.42753E-3 -/), temp_lapse := (Binary32.ofBits 0x00000000 /- 0 -/) }, { amsl_m := (Binary32.ofBits 0x47473800 /- 51000 -/), temp_K := (Binary32.ofBits 0x43875333 /- 270.650 -/), pressure_Pa := (Binary32.ofBits 0x4285e0b8 /- 66.9389 -/), density := (Binary32.ofBits 0x3a61dd66 /- 8.61606E-4 -/), temp_lapse := -(Binary32.ofBits 0x3b378034 /- 2.8E-3 -/) }, { amsl_m := (Binary32.ofBits 0x478aac00 /- 71000 -/), temp_K := (Binary32.ofBits 0x4356a666 /- 214.650 -/), pressure_Pa := (Binary32.ofBits 0x407d35fc /- 3.95642 -/), density := (Binary32.ofBits 0x3886a905 /- 6.42110E-5 -/), temp_lapse := -(Binary32.ofBits 0x3b03126f /- 2.0E-3 -/) }, { amsl_m := (Binary32.ofBits 0x47a5ba00 /- 84852 -/), temp_K := (Binary32.ofBits 0x433af22d /- 186.946 -/), pressure_Pa := (Binary32.ofBits 0x3ebf2baa /- 0.37338 -/), density := (Binary32.ofBits 0x36e977bc /- 6.95788E-6 -/), temp_lapse := (Binary32.ofBits 0x00000000 /- 0 -/) }]

/-- C++ `uint8_t find_atmosphere_layer_by_pressure(float pressure)`, `AP_Baro/AP_Baro_atmosphere.cpp:111-122`. -/
def find_atmosphere_layer_by_pressure (pressure : Binary32) : UInt8 := Id.run do
  for idx' in [1:8] do
    let idx : UInt8 := Nat.toUInt8 idx'
    if atmospheric_1976_consts[UInt8.toNat idx]!.pressure_Pa < pressure then
      return Int8.toUInt8 (Int32.toInt8 (UInt32.toInt32 (UInt8.toUInt32 idx) - (1 : Int32)))
  return UInt64.toUInt8 ((8 : UInt64) - Int64.toUInt64 (Int32.toInt64 (1 : Int32)))

namespace AP_Baro

/-- C++ `float AP_Baro::get_altitude_from_pressure(float pressure) const`, `AP_Baro/AP_Baro_atmosphere.cpp:160-182`. -/
def get_altitude_from_pressure (s : State) (pressure : Binary32) : Binary32 := Id.run do
  let idx : UInt8 := Estimator_lib.find_atmosphere_layer_by_pressure pressure
  let pressure_ratio : Binary32 := pressure / Estimator_lib.atmospheric_1976_consts[UInt8.toNat idx]!.pressure_Pa
  if !(Estimator_lib.is_positive_float pressure_ratio) then
    pure ()  -- C++ `AP_InternalError::error(...)`: left out (--drop)
    return get_altitude_AMSL_void s
  let mut alt : Binary32 := (Binary32.ofBits 0x00000000 /- 0.0 -/)  -- uninitialized in C++; assigned before every read
  let temp_slope : Binary32 := Estimator_lib.atmospheric_1976_consts[UInt8.toNat idx]!.temp_lapse
  if Estimator_lib.is_zero_float temp_slope then
    let fac : Binary32 := -(Estimator_lib.atmospheric_1976_consts[UInt8.toNat idx]!.temp_K * Estimator_lib.R_specific) / (Binary32.ofBits 0x411ce80a /- 9.80665016 -/)
    alt := Estimator_lib.atmospheric_1976_consts[UInt8.toNat idx]!.amsl_m + fac * Musl.logf.logf pressure_ratio
  else
    let fac'2 : Binary32 := -(temp_slope * Estimator_lib.R_specific) / (Binary32.ofBits 0x411ce80a /- 9.80665016 -/)
    alt := Estimator_lib.atmospheric_1976_consts[UInt8.toNat idx]!.amsl_m + (Estimator_lib.atmospheric_1976_consts[UInt8.toNat idx]!.temp_K / Estimator_lib.atmospheric_1976_consts[UInt8.toNat idx]!.temp_lapse) * (Musl.powf.powf pressure_ratio fac'2 - (Binary32.ofBits 0x3f800000 /- 1 -/))
  return geopotential_alt_to_geometric alt

/-- C++ `float AP_Baro::get_altitude_difference(float base_pressure, float pressure) const`, `AP_Baro/AP_Baro_atmosphere.cpp:263-272`. -/
def get_altitude_difference (s : State) (base_pressure : Binary32) (pressure : Binary32) : Binary32 := Id.run do
  let alt1 : Binary32 := get_altitude_from_pressure s base_pressure
  let alt2 : Binary32 := get_altitude_from_pressure s pressure
  return alt2 - alt1

end AP_Baro

namespace AP_Baro

/-- C++ `float AP_Baro::get_sealevel_pressure(float pressure, float altitude) const`, `AP_Baro/AP_Baro_atmosphere.cpp:335-358`. -/
def get_sealevel_pressure (s : State) (pressure : Binary32) (altitude : Binary32) : Binary32 := Id.run do
  let min_pressure : Binary32 := (Binary32.ofBits 0x3c23d70a /- 0.01 -/)
  let max_pressure : Binary32 := (Binary32.ofBits 0x49742400 /- 1e6 -/)
  let mut p0 : Binary32 := pressure
  let mut count : UInt16 := Int16.toUInt16 (Int32.toInt16 (20 : Int32))
  for _ in [0:2^64] do  -- C loop without a constant trip count (--general-loops)
    let t'1 := count
    count := count - (1 : UInt16)
    if !(t'1 != (0 : UInt16)) then break
    let delta : Binary32 := (Binary32.ofBits 0x3dcccccd /- 0.1 -/)
    let err1 : Binary32 := get_altitude_difference s p0 pressure - altitude
    let err2 : Binary32 := get_altitude_difference s (p0 + delta) pressure - altitude
    let dalt : Binary32 := err2 - err1
    if Binary32.abs err1 < (Binary32.ofBits 0x3c23d70a /- 0.01 -/) then
      break
    p0 := p0 - err1 * delta / dalt
    p0 := Estimator_lib.constrain_value_line_float p0 min_pressure max_pressure (Int32.toUInt32 (355 : Int32))
  return p0

/-- C++ `float AP_Baro::get_pressure(uint8_t instance) const`, `AP_Baro/AP_Baro.h:73`. -/
def get_pressure_uint8_t (s : State) («instance» : UInt8) : Binary32 := Id.run do
  return s.sensors[UInt8.toNat «instance»]!.pressure

/-- C++ `float AP_Baro::get_temperature(uint8_t instance) const`, `AP_Baro/AP_Baro.h:84`. -/
def get_temperature_uint8_t (s : State) («instance» : UInt8) : Binary32 := Id.run do
  return s.sensors[UInt8.toNat «instance»]!.temperature

end AP_Baro

namespace AP_Baro_SITL

/-- C++ `struct AP_Baro_SITL::readings_baro`, `AP_Baro/AP_Baro_SITL.h:32-35`. -/
structure readings_baro where
  /-- `uint32_t time` of `AP_Baro_SITL::readings_baro` (`AP_Baro/AP_Baro_SITL.h:33`). -/
  time : UInt32 := (0 : UInt32)
  /-- `float data` of `AP_Baro_SITL::readings_baro` (`AP_Baro/AP_Baro_SITL.h:34`). -/
  data : Binary32 := (Binary32.ofBits 0x00000000 /- 0.0 -/)
deriving Inhabited

end AP_Baro_SITL

namespace AP_Baro

/-- C++ `float AP_Baro::get_EAS2TAS() const`, `AP_Baro/AP_Baro.h:149`. -/
def get_EAS2TAS (s : State) : Binary32 := Id.run do
  return s._EAS2TAS

end AP_Baro

namespace AP_Baro

/-- C++ `uint32_t AP_Baro::get_last_update(uint8_t instance) const`, `AP_Baro/AP_Baro.h:171`. -/
def get_last_update_uint8_t (s : State) («instance» : UInt8) : UInt32 := Id.run do
  return s.sensors[UInt8.toNat «instance»]!.last_update_ms

/-- C++ `uint8_t AP_Baro::num_instances() const`, `AP_Baro/AP_Baro.h:193`. -/
def num_instances (s : State) : UInt8 := Id.run do
  return s._num_sensors

/-- C++ `uint8_t AP_Baro::get_primary() const`, `AP_Baro/AP_Baro.h:69`. -/
def get_primary (s : State) : UInt8 := Id.run do
  return s._primary

end AP_Baro

namespace AP_Baro

/-- C++ `bool AP_Baro::healthy() const`, `AP_Baro/AP_Baro.h:58`. -/
def healthy_void (s : State) : Bool := Id.run do
  return healthy_uint8_t s s._primary

end AP_Baro

namespace AP_Baro

/-- C++ `float AP_Baro::get_climb_rate()`, `AP_Baro/AP_Baro.cpp:424-429`. -/
def get_climb_rate (s : State) : State × Binary32 := Id.run do
  let mut s := s
  let (t'1, t'2) := DerivativeFilterFloat_Size7.slope s._climb_rate_filter
  s := { s with _climb_rate_filter := t'1 }
  return (s, t'2 * (Binary32.ofBits 0x447a0000 /- 1.0e3f -/))

end AP_Baro

namespace AP_Baro

/-- C++ `float AP_Baro::get_altitude() const`, `AP_Baro/AP_Baro.h:102`. -/
def get_altitude_void (s : State) : Binary32 := Id.run do
  return get_altitude_uint8_t s s._primary

end AP_Baro

namespace AP_Baro

/-- C++ `bool AP_Baro::_add_backend(AP_Baro_Backend * backend)`, `AP_Baro/AP_Baro.cpp:486-496`. -/
def _add_backend (s : State) (backend : WPtr) : State × Bool := Id.run do
  let mut s := s
  if !(backend != WPtr.null) then
    return (s, false)
  if UInt8.toUInt64 s._num_drivers ≥ (3 : UInt64) then
    pure ()  -- C++ `AP_HAL::panic(...)`: left out (--drop)
  let t'1 := s._num_drivers
  s := { s with _num_drivers := s._num_drivers + (1 : UInt8) }
  s := { s with drivers := s.drivers.set! (UInt8.toNat t'1) backend }
  return (s, true)

/-- C++ `uint8_t AP_Baro::register_sensor()`, `AP_Baro/AP_Baro.cpp:1076-1082`. -/
def register_sensor (s : State) : State × UInt8 := Id.run do
  let mut s := s
  if UInt8.toUInt64 s._num_sensors ≥ (3 : UInt64) then
    pure ()  -- C++ `AP_HAL::panic(...)`: left out (--drop)
  let t'1 := s._num_sensors
  s := { s with _num_sensors := s._num_sensors + (1 : UInt8) }
  return (s, t'1)

end AP_Baro

namespace AP_Baro_Backend

/-- C++ `enum AP_Baro_Backend::DevTypes`, `AP_Baro/AP_Baro_Backend.h:35-60`. -/
inductive DevTypes where
  | DEVTYPE_BARO_SITL
  | DEVTYPE_BARO_BMP085
  | DEVTYPE_BARO_BMP280
  | DEVTYPE_BARO_BMP388
  | DEVTYPE_BARO_DPS280
  | DEVTYPE_BARO_DPS310
  | DEVTYPE_BARO_FBM320
  | DEVTYPE_BARO_ICM20789
  | DEVTYPE_BARO_KELLERLD
  | DEVTYPE_BARO_LPS2XH
  | DEVTYPE_BARO_MS5611
  | DEVTYPE_BARO_SPL06
  | DEVTYPE_BARO_UAVCAN
  | DEVTYPE_BARO_MSP
  | DEVTYPE_BARO_ICP101XX
  | DEVTYPE_BARO_ICP201XX
  | DEVTYPE_BARO_MS5607
  | DEVTYPE_BARO_MS5837_30BA
  | DEVTYPE_BARO_MS5637
  | DEVTYPE_BARO_BMP390
  | DEVTYPE_BARO_BMP581
  | DEVTYPE_BARO_SPA06
  | DEVTYPE_BARO_AUAV
  | DEVTYPE_BARO_MS5837_02BA
deriving DecidableEq, Inhabited

/-- The value of each enumerator of `AP_Baro_Backend::DevTypes` (underlying type `uint32_t`). -/
def DevTypes.toInt : DevTypes → UInt32
  | .DEVTYPE_BARO_SITL => (1 : UInt32)
  | .DEVTYPE_BARO_BMP085 => (2 : UInt32)
  | .DEVTYPE_BARO_BMP280 => (3 : UInt32)
  | .DEVTYPE_BARO_BMP388 => (4 : UInt32)
  | .DEVTYPE_BARO_DPS280 => (5 : UInt32)
  | .DEVTYPE_BARO_DPS310 => (6 : UInt32)
  | .DEVTYPE_BARO_FBM320 => (7 : UInt32)
  | .DEVTYPE_BARO_ICM20789 => (8 : UInt32)
  | .DEVTYPE_BARO_KELLERLD => (9 : UInt32)
  | .DEVTYPE_BARO_LPS2XH => (10 : UInt32)
  | .DEVTYPE_BARO_MS5611 => (11 : UInt32)
  | .DEVTYPE_BARO_SPL06 => (12 : UInt32)
  | .DEVTYPE_BARO_UAVCAN => (13 : UInt32)
  | .DEVTYPE_BARO_MSP => (14 : UInt32)
  | .DEVTYPE_BARO_ICP101XX => (15 : UInt32)
  | .DEVTYPE_BARO_ICP201XX => (16 : UInt32)
  | .DEVTYPE_BARO_MS5607 => (17 : UInt32)
  | .DEVTYPE_BARO_MS5837_30BA => (18 : UInt32)
  | .DEVTYPE_BARO_MS5637 => (19 : UInt32)
  | .DEVTYPE_BARO_BMP390 => (20 : UInt32)
  | .DEVTYPE_BARO_BMP581 => (21 : UInt32)
  | .DEVTYPE_BARO_SPA06 => (22 : UInt32)
  | .DEVTYPE_BARO_AUAV => (23 : UInt32)
  | .DEVTYPE_BARO_MS5837_02BA => (24 : UInt32)

end AP_Baro_Backend

/-- C++ `uint8_t find_atmosphere_layer_by_altitude(float alt_m)`, `AP_Baro/AP_Baro_atmosphere.cpp:96-106`. -/
def find_atmosphere_layer_by_altitude (alt_m : Binary32) : UInt8 := Id.run do
  for idx' in [1:8] do
    let idx : UInt8 := Nat.toUInt8 idx'
    if alt_m < atmospheric_1976_consts[UInt8.toNat idx]!.amsl_m then
      return Int8.toUInt8 (Int32.toInt8 (UInt32.toInt32 (UInt8.toUInt32 idx) - (1 : Int32)))
  return UInt64.toUInt8 ((8 : UInt64) - Int64.toUInt64 (Int32.toInt64 (1 : Int32)))

end Estimator_lib
