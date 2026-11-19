import ArduLean.Runtime.CFloat
import ArduLean.Estimator.libraries.AP_Math.AP_Math
import ArduLean.Estimator.libraries.AP_Common.AP_Common
import ArduLean.Estimator.libraries.AP_Param.AP_Param

/-!
ArduPilot `libraries/SITL`. Sources: `libraries/SITL/SITL.h`.

Items of `lean/Estimator_lib.lean` (the estimator translation), unchanged; placed by `tools/split_modules.py` (`ArduLean/Estimator/INDEX.md`).
-/

open FloatLib.Floats (Binary32 Binary64)

set_option maxRecDepth 200000
-- AP_DAL's `const log_RISH old_RISH = _RISH;` read only by WRITE_REPLAY_BLOCK_IFCHANGED, which is `(void)old`
-- without logging (HAL_LOGGING_ENABLED 0): an unused binding, as in the C++
set_option linter.unusedVariables false

namespace Estimator_lib

namespace SITL.CompassSim

/-- State of C++ `SITL::CompassSim` (`reference/hal/SITL/SIM_Compass.h:6-11`): its data members. -/
structure State where
  /-- `const uint8_t instance` of `SITL::CompassSim` (`reference/hal/SITL/SIM_Compass.h:10`). -/
  «instance» : UInt8 := (0 : UInt8)
deriving Inhabited

end SITL.CompassSim

namespace SITL

/-- C++ `struct SITL::sitl_fdm`, `reference/hal/SITL/SITL.h:26-45`. -/
structure sitl_fdm where
  /-- `uint64_t timestamp_us` of `SITL::sitl_fdm` (`reference/hal/SITL/SITL.h:27`). -/
  timestamp_us : UInt64 := (0 : UInt64)
  /-- `uint64_t flightaxis_imu_frame_num` of `SITL::sitl_fdm` (`reference/hal/SITL/SITL.h:28`). -/
  flightaxis_imu_frame_num : UInt64 := (0 : UInt64)
  /-- `Location home` of `SITL::sitl_fdm` (`reference/hal/SITL/SITL.h:29`). -/
  home : Location.State := {}
  /-- `double latitude` of `SITL::sitl_fdm` (`reference/hal/SITL/SITL.h:30`). -/
  latitude : Binary64 := (Binary64.ofBits 0x0000000000000000 /- 0.0 -/)
  /-- `double longitude` of `SITL::sitl_fdm` (`reference/hal/SITL/SITL.h:30`). -/
  longitude : Binary64 := (Binary64.ofBits 0x0000000000000000 /- 0.0 -/)
  /-- `double altitude` of `SITL::sitl_fdm` (`reference/hal/SITL/SITL.h:31`). -/
  altitude : Binary64 := (Binary64.ofBits 0x0000000000000000 /- 0.0 -/)
  /-- `double heading` of `SITL::sitl_fdm` (`reference/hal/SITL/SITL.h:32`). -/
  heading : Binary64 := (Binary64.ofBits 0x0000000000000000 /- 0.0 -/)
  /-- `double speedN` of `SITL::sitl_fdm` (`reference/hal/SITL/SITL.h:33`). -/
  speedN : Binary64 := (Binary64.ofBits 0x0000000000000000 /- 0.0 -/)
  /-- `double speedE` of `SITL::sitl_fdm` (`reference/hal/SITL/SITL.h:33`). -/
  speedE : Binary64 := (Binary64.ofBits 0x0000000000000000 /- 0.0 -/)
  /-- `double speedD` of `SITL::sitl_fdm` (`reference/hal/SITL/SITL.h:33`). -/
  speedD : Binary64 := (Binary64.ofBits 0x0000000000000000 /- 0.0 -/)
  /-- `double xAccel` of `SITL::sitl_fdm` (`reference/hal/SITL/SITL.h:34`). -/
  xAccel : Binary64 := (Binary64.ofBits 0x0000000000000000 /- 0.0 -/)
  /-- `double yAccel` of `SITL::sitl_fdm` (`reference/hal/SITL/SITL.h:34`). -/
  yAccel : Binary64 := (Binary64.ofBits 0x0000000000000000 /- 0.0 -/)
  /-- `double zAccel` of `SITL::sitl_fdm` (`reference/hal/SITL/SITL.h:34`). -/
  zAccel : Binary64 := (Binary64.ofBits 0x0000000000000000 /- 0.0 -/)
  /-- `double rollRate` of `SITL::sitl_fdm` (`reference/hal/SITL/SITL.h:35`). -/
  rollRate : Binary64 := (Binary64.ofBits 0x0000000000000000 /- 0.0 -/)
  /-- `double pitchRate` of `SITL::sitl_fdm` (`reference/hal/SITL/SITL.h:35`). -/
  pitchRate : Binary64 := (Binary64.ofBits 0x0000000000000000 /- 0.0 -/)
  /-- `double yawRate` of `SITL::sitl_fdm` (`reference/hal/SITL/SITL.h:35`). -/
  yawRate : Binary64 := (Binary64.ofBits 0x0000000000000000 /- 0.0 -/)
  /-- `double rollDeg` of `SITL::sitl_fdm` (`reference/hal/SITL/SITL.h:36`). -/
  rollDeg : Binary64 := (Binary64.ofBits 0x0000000000000000 /- 0.0 -/)
  /-- `double pitchDeg` of `SITL::sitl_fdm` (`reference/hal/SITL/SITL.h:36`). -/
  pitchDeg : Binary64 := (Binary64.ofBits 0x0000000000000000 /- 0.0 -/)
  /-- `double yawDeg` of `SITL::sitl_fdm` (`reference/hal/SITL/SITL.h:36`). -/
  yawDeg : Binary64 := (Binary64.ofBits 0x0000000000000000 /- 0.0 -/)
  /-- `Quaternion quaternion` of `SITL::sitl_fdm` (`reference/hal/SITL/SITL.h:37`). -/
  quaternion : Quaternion.State := Quaternion.init_void
  /-- `double airspeed` of `SITL::sitl_fdm` (`reference/hal/SITL/SITL.h:38`). -/
  airspeed : Binary64 := (Binary64.ofBits 0x0000000000000000 /- 0.0 -/)
  /-- `Vector3f velocity_air_bf` of `SITL::sitl_fdm` (`reference/hal/SITL/SITL.h:39`). -/
  velocity_air_bf : Vector3f.State := {}
  /-- `double battery_voltage` of `SITL::sitl_fdm` (`reference/hal/SITL/SITL.h:40`). -/
  battery_voltage : Binary64 := (Binary64.ofBits 0x0000000000000000 /- 0.0 -/)
  /-- `double battery_current` of `SITL::sitl_fdm` (`reference/hal/SITL/SITL.h:41`). -/
  battery_current : Binary64 := (Binary64.ofBits 0x0000000000000000 /- 0.0 -/)
  /-- `bool is_lock_step_scheduled` of `SITL::sitl_fdm` (`reference/hal/SITL/SITL.h:42`). -/
  is_lock_step_scheduled : Bool := false
  /-- `Vector3f wind_ef` of `SITL::sitl_fdm` (`reference/hal/SITL/SITL.h:43`). -/
  wind_ef : Vector3f.State := {}
  /-- `float height_agl` of `SITL::sitl_fdm` (`reference/hal/SITL/SITL.h:44`). -/
  height_agl : Binary32 := (Binary32.ofBits 0x00000000 /- 0.0 -/)
deriving Inhabited

end SITL

namespace SITL.SIM

/-- C++ `struct SITL::SIM::(unnamed struct at reference/hal/SITL/SITL.h:78:5)`, `reference/hal/SITL/SITL.h:78-82`. -/
structure sim_ahrs_offset_t where
  /-- `AP_Float roll` of `SITL::SIM::(unnamed struct at reference/hal/SITL/SITL.h:78:5)` (`reference/hal/SITL/SITL.h:79`). -/
  roll : AP_ParamT_float_4.State := {}
  /-- `AP_Float pitch` of `SITL::SIM::(unnamed struct at reference/hal/SITL/SITL.h:78:5)` (`reference/hal/SITL/SITL.h:80`). -/
  pitch : AP_ParamT_float_4.State := {}
  /-- `AP_Float yaw` of `SITL::SIM::(unnamed struct at reference/hal/SITL/SITL.h:78:5)` (`reference/hal/SITL/SITL.h:81`). -/
  yaw : AP_ParamT_float_4.State := {}
deriving Inhabited

/-- State of C++ `SITL::SIM` (`reference/hal/SITL/SITL.h:47-90`): its data members. -/
structure State where
  /-- `struct sitl_fdm state` of `SITL::SIM` (`reference/hal/SITL/SITL.h:59`). -/
  state : SITL.sitl_fdm := {}
  /-- `float throttle` of `SITL::SIM` (`reference/hal/SITL/SITL.h:60`). -/
  throttle : Binary32 := (Binary32.ofBits 0x00000000 /- 0.0 -/)
  /-- `AP_Int8 imu_count` of `SITL::SIM` (`reference/hal/SITL/SITL.h:63`). -/
  imu_count : AP_ParamT_signed_char_1.State := {}
  /-- `AP_Int8 baro_count` of `SITL::SIM` (`reference/hal/SITL/SITL.h:64`). -/
  baro_count : AP_ParamT_signed_char_1.State := {}
  /-- `AP_Int32 loop_delay` of `SITL::SIM` (`reference/hal/SITL/SITL.h:65`). -/
  loop_delay : AP_ParamT_int_3.State := {}
  /-- `AP_Int16 loop_time_jitter_us` of `SITL::SIM` (`reference/hal/SITL/SITL.h:66`). -/
  loop_time_jitter_us : AP_ParamT_short_2.State := {}
  /-- `AP_Int16 on_hardware_relay_enable_mask` of `SITL::SIM` (`reference/hal/SITL/SITL.h:67`). -/
  on_hardware_relay_enable_mask : AP_ParamT_short_2.State := {}
  /-- `AP_Int8 wow_pin` of `SITL::SIM` (`reference/hal/SITL/SITL.h:68`). -/
  wow_pin : AP_ParamT_signed_char_1.State := {}
  /-- `AP_Int8 odom_enable` of `SITL::SIM` (`reference/hal/SITL/SITL.h:69`). -/
  odom_enable : AP_ParamT_signed_char_1.State := {}
  /-- `AP_Int8 float_exception` of `SITL::SIM` (`reference/hal/SITL/SITL.h:70`). -/
  float_exception : AP_ParamT_signed_char_1.State := {}
  /-- `AP_Int8 telem_baudlimit_enable` of `SITL::SIM` (`reference/hal/SITL/SITL.h:71`). -/
  telem_baudlimit_enable : AP_ParamT_signed_char_1.State := {}
  /-- `AP_Int8 mag_save_ids` of `SITL::SIM` (`reference/hal/SITL/SITL.h:72`). -/
  mag_save_ids : AP_ParamT_signed_char_1.State := {}
  /-- `AP_UInt32 mag_devid[8]` of `SITL::SIM` (`reference/hal/SITL/SITL.h:73`). -/
  mag_devid : Array AP_ParamT_unsigned_int_3.State := Array.replicate 8 {}
  /-- `AP_Vector3f mag_ofs[3]` of `SITL::SIM` (`reference/hal/SITL/SITL.h:74`). -/
  mag_ofs : Array AP_ParamV_Vector3_float_5.State := Array.replicate 3 {}
  /-- `time_t start_time_UTC` of `SITL::SIM` (`reference/hal/SITL/SITL.h:75`). -/
  start_time_UTC : Int64 := (0 : Int64)
  /-- `AP_Vector3f accel_bias[3]` of `SITL::SIM` (`reference/hal/SITL/SITL.h:76`). -/
  accel_bias : Array AP_ParamV_Vector3_float_5.State := Array.replicate 3 {}
  /-- `struct (unnamed struct at reference/hal/SITL/SITL.h:78:5) sim_ahrs_offset` of `SITL::SIM` (`reference/hal/SITL/SITL.h:82`). -/
  sim_ahrs_offset : SITL.SIM.sim_ahrs_offset_t := {}
deriving Inhabited

end SITL.SIM

namespace SITL.CompassSim

/-- C++ `SITL::CompassSim::CompassSim(uint8_t _instance)`, `reference/hal/SITL/SIM_Compass.h:8`. -/
def init (_instance : UInt8) : State := Id.run do
  let mut s : State := {}
  s := { s with «instance» := _instance }
  return s

end SITL.CompassSim

namespace SITL.SIM

/-- C++ `SITL::SIM::SIM()`, `reference/hal/sensors.cpp:38-65`. -/
def init : State := Id.run do
  let mut s : State := {}
  if false /- C++ `_singleton != nullptr` -/ then
    pure ()  -- C++ `AP_HAL::panic(...)`: left out (--drop)
  pure ()  -- C++ `_singleton = this`: the pointer is the class's one World object (--world)
  s := { s with imu_count := AP_ParamT_signed_char_1.set s.imu_count (Int32.toInt8 (1 : Int32)) }
  s := { s with baro_count := AP_ParamT_signed_char_1.set s.baro_count (Int32.toInt8 (1 : Int32)) }
  s := { s with loop_delay := AP_ParamT_int_3.set s.loop_delay (0 : Int32) }
  s := { s with loop_time_jitter_us := AP_ParamT_short_2.set s.loop_time_jitter_us (Int32.toInt16 (0 : Int32)) }
  s := { s with on_hardware_relay_enable_mask := AP_ParamT_short_2.set s.on_hardware_relay_enable_mask (Int32.toInt16 (0 : Int32)) }
  s := { s with wow_pin := AP_ParamT_signed_char_1.set s.wow_pin (Int32.toInt8 (-(1 : Int32))) }
  s := { s with odom_enable := AP_ParamT_signed_char_1.set s.odom_enable (Int32.toInt8 (0 : Int32)) }
  s := { s with float_exception := AP_ParamT_signed_char_1.set s.float_exception (Int32.toInt8 (0 : Int32)) }
  s := { s with telem_baudlimit_enable := AP_ParamT_signed_char_1.set s.telem_baudlimit_enable (Int32.toInt8 (0 : Int32)) }
  s := { s with mag_save_ids := AP_ParamT_signed_char_1.set s.mag_save_ids (Int32.toInt8 (1 : Int32)) }
  s := { s with mag_devid := s.mag_devid.set! 0 (AP_ParamT_unsigned_int_3.set s.mag_devid[0]! (Int32.toUInt32 (97539 : Int32))) }
  for i' in [1:8] do
    let i : UInt8 := Nat.toUInt8 i'
    s := { s with mag_devid := s.mag_devid.set! (UInt8.toNat i) (AP_ParamT_unsigned_int_3.set s.mag_devid[UInt8.toNat i]! (Int32.toUInt32 (0 : Int32))) }
  for i'2' in [0:3] do
    let i'2 : UInt8 := Nat.toUInt8 i'2'
    s := { s with mag_ofs := s.mag_ofs.set! (UInt8.toNat i'2) (AP_ParamV_Vector3_float_5.set s.mag_ofs[UInt8.toNat i'2]! (Vector3f.init_float3 (Binary32.ofBits 0x40a00000 /- 5 -/) (Binary32.ofBits 0x41500000 /- 13 -/) (Binary32.ofBits 0xc1900000 /- -18 -/))) }
  s := { s with start_time_UTC := Int32.toInt64 (1767225600 : Int32) }
  s := { s with state.is_lock_step_scheduled := true }
  s := { s with throttle := (Binary32.ofBits 0x00000000 /- 0 -/) }
  return s

end SITL.SIM

end Estimator_lib
