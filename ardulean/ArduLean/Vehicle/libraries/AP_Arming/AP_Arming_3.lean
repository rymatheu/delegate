import ArduLean.Runtime.Bridge
import ArduLean.Vehicle.libraries.AP_Math.AP_Math
import ArduLean.Vehicle.libraries.StorageManager.StorageManager
import ArduLean.Vehicle.libraries.AP_Param.AP_Param
import ArduLean.Vehicle.libraries.AP_Mission.AP_Mission
import ArduLean.Vehicle.libraries.AP_BoardConfig.AP_BoardConfig
import ArduLean.Vehicle.libraries.RC_Channel.RC_Channel
import ArduLean.Vehicle.libraries.AP_Arming.AP_Arming
import ArduLean.Vehicle.ArduCopter.ArduCopter
import ArduLean.Vehicle.libraries.AP_Common.AP_Common
import ArduLean.Vehicle.libraries.GCS_MAVLink.GCS_MAVLink
import ArduLean.Vehicle.libraries.AP_BattMonitor.AP_BattMonitor
import ArduLean.Vehicle.libraries.AP_Vehicle.AP_Vehicle
import ArduLean.Vehicle.libraries.AP_CANManager.AP_CANManager
import ArduLean.Vehicle.libraries.AP_Scheduler.AP_Scheduler
import ArduLean.Vehicle.libraries.SRV_Channel.SRV_Channel
import ArduLean.Vehicle.libraries.AP_HAL.AP_HAL_2
import ArduLean.Vehicle.libraries.AP_Mission.AP_Mission_2
import ArduLean.Vehicle.libraries.AP_InternalError.AP_InternalError
import ArduLean.Vehicle.libraries.RC_Channel.RC_Channel_2
import ArduLean.Vehicle.ArduCopter.ArduCopter_2
import ArduLean.Vehicle.libraries.AP_SerialManager.AP_SerialManager
import ArduLean.Vehicle.libraries.GCS_MAVLink.GCS_MAVLink_2
import ArduLean.Vehicle.libraries.AP_BattMonitor.AP_BattMonitor_2
import ArduLean.Vehicle.World

/-!
ArduPilot `libraries/AP_Arming`, part 3 of 3. Sources: `libraries/AP_Arming/AP_Arming.cpp`.

Items of `lean/Vehicle_lib.lean` (the vehicle translation), unchanged; placed by `tools/split_modules.py` (`ArduLean/Vehicle/INDEX.md`).
-/

open FloatLib.Floats (Binary32 Binary64)

set_option linter.unusedVariables false
set_option linter.unreachableTactic false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false

namespace Vehicle_lib

/-- C++ `AP_Arming::disarm : bool (const AP_Arming::Method, bool)`, `AP_Arming.cpp:1974-2032`. -/
def AP_Arming.disarm.body (fp : UInt64) (this : UInt64) (method : Int32) (do_disarm_checks : Bool) : PMem.M Bool := do
  let mut method := method
  let mut do_disarm_checks := do_disarm_checks
  let t'1 ← PMem.ldB (this + 35)
  if !t'1 then
    return false
  if (method == (0 : Int32)) then
    let t'2 ← rc
    let t'3 ← RC_Channels.get_throttle_channel t'2
    let t'4 ← RC_Channel.get_control_in t'3
    if (decide ((Int16.toInt32 (t'4)) > (0 : Int32))) then
      return false
    let t'5 ← AP_Arming.get_rudder_arming_type this
    if (t'5 != (2 : Int32)) then
      let t'6 ← gcs
      GCS.send_text t'6 (6 : UInt32) (0x1a73a : UInt64) /- "Disarm: rudder disarm disabled" -/ (fp + 0)
      return false
  PMem.stB (this + 35) false
  PMem.stI32 (this + 44) method
  let t'7 ← AP_BoardConfig.get_singleton
  let mut board_cfg : UInt64 := t'7
  let mut sc'9 := (board_cfg != (0 : UInt64))
  if sc'9 then
    let t'8 ← AP_BoardConfig.get_safety_button_options board_cfg
    sc'9 := ((UInt32.toInt32 (UInt16.toUInt32 (t'8))) &&& (UInt32.toInt32 ((8 : UInt32)))) != (0 : Int32)
  if sc'9 then
    let t'10 ← PMem.ldU64 ((0xba88 : UInt64) /- &hal -/ + 72)
    let t'11 ← PMem.halDev "AP_HAL::RCOutput::force_safety_on" t'10 #[]
    discard <| pure ((t'11 != 0))
  return true

def AP_Arming.disarm (this : UInt64) (method : Int32) (do_disarm_checks : Bool) : PMem.M Bool := do
  let fp ← PMem.enter 8
  let r ← AP_Arming.disarm.body fp this method do_disarm_checks
  PMem.leave fp
  return r

/-- C++ `AP_Arming::send_arm_disarm_statustext : void (const char *) const`, `AP_Arming.cpp:2043-2049`. -/
def AP_Arming.send_arm_disarm_statustext.body (fp : UInt64) (this : UInt64) (str : UInt64) : PMem.M Unit := do
  let mut str := str
  let t'1 ← AP_Arming.option_enabled this (2 : Int32)
  if t'1 then
    return ()
  PMem.stU64 (fp + 0) str
  let t'2 ← gcs
  GCS.send_text t'2 (6 : UInt32) (0x13fd2 : UInt64) /- "%s" -/ (fp + 0)
  return ()

def AP_Arming.send_arm_disarm_statustext (this : UInt64) (str : UInt64) : PMem.M Unit := do
  let fp ← PMem.enter 8
  let r ← AP_Arming.send_arm_disarm_statustext.body fp this str
  PMem.leave fp
  return r

/-- C++ `AP_Arming::check_failed : void (bool, const char *, ...) const`, `AP_Arming.cpp:370-392`. -/
def AP_Arming.check_failed'2.body (fp : UInt64) (this : UInt64) (report : Bool) (fmt : UInt64) (va' : UInt64) : PMem.M Unit := do
  let mut report := report
  PMem.stU64 (fp + 0) fmt
  if !report then
    return ()
  let mut metafmt : UInt64 := (0x1a177 : UInt64) /- "PreArm: %s" -/
  let t'1 ← PMem.ldB (this + 68)
  if t'1 then
    let t'2 := (0x1a182 : UInt64) /- "Arm: %s" -/
    metafmt := t'2
  let t'3 ← PMem.ldU64 (fp + 0)
  PMem.stU64 (fp + 64) t'3
  let t'4 ← AP_HAL.Util.snprintf (0 : UInt64) (fp + 8) (51 : UInt64) metafmt (fp + 64)
  discard <| pure (t'4)
  PMem.stU64 (fp + 72) va'
  let t'5 ← PMem.ldU64 (fp + 72)
  let t'6 ← gcs
  GCS.send_textv t'6 (2 : UInt32) (fp + 8) t'5
  return ()

def AP_Arming.check_failed'2 (this : UInt64) (report : Bool) (fmt : UInt64) (va' : UInt64) : PMem.M Unit := do
  let fp ← PMem.enter 80
  let r ← AP_Arming.check_failed'2.body fp this report fmt va'
  PMem.leave fp
  return r

/-- C++ `AP_Arming::check_failed : void (const AP_Arming::Check, bool, const char *, ...) const`, `AP_Arming.cpp:341-368`. -/
def AP_Arming.check_failed.body (fp : UInt64) (this : UInt64) (check : Int32) (report : Bool) (fmt : UInt64) (va' : UInt64) : PMem.M Unit := do
  let mut check := check
  let mut report := report
  PMem.stU64 (fp + 0) fmt
  if !report then
    return ()
  let mut metafmt : UInt64 := (0x1a177 : UInt64) /- "PreArm: %s" -/
  let t'1 ← PMem.ldB (this + 68)
  if t'1 then
    let t'2 := (0x1a182 : UInt64) /- "Arm: %s" -/
    metafmt := t'2
  let t'3 ← PMem.ldU64 (fp + 0)
  PMem.stU64 (fp + 64) t'3
  let t'4 ← AP_HAL.Util.snprintf (0 : UInt64) (fp + 8) (51 : UInt64) metafmt (fp + 64)
  discard <| pure (t'4)
  let mut severity : UInt32 := (2 : UInt32)
  let t'5 ← AP_Arming.check_enabled this check
  if !t'5 then
    severity := (7 : UInt32)
  PMem.stU64 (fp + 72) va'
  let t'6 ← PMem.ldU64 (fp + 72)
  let t'7 ← gcs
  GCS.send_textv t'7 severity (fp + 8) t'6
  return ()

def AP_Arming.check_failed (this : UInt64) (check : Int32) (report : Bool) (fmt : UInt64) (va' : UInt64) : PMem.M Unit := do
  let fp ← PMem.enter 80
  let r ← AP_Arming.check_failed.body fp this check report fmt va'
  PMem.leave fp
  return r

/-- C++ `AP_Arming::rc_in_calibration_check : bool (bool)`, `AP_Arming.cpp:921-928`. -/
def AP_Arming.rc_in_calibration_check.body (fp : UInt64) (this : UInt64) (report : Bool) : PMem.M Bool := do
  let mut report := report
  let t'1 ← rc
  let t'2 ← RC_Channels.calibrating t'1
  if t'2 then
    AP_Arming.check_failed this (64 : Int32) report (0x1a461 : UInt64) /- "RC calibrating" -/ (fp + 0)
    return false
  return true

def AP_Arming.rc_in_calibration_check (this : UInt64) (report : Bool) : PMem.M Bool := do
  let fp ← PMem.enter 8
  let r ← AP_Arming.rc_in_calibration_check.body fp this report
  PMem.leave fp
  return r

/-- C++ `AP_Arming::serial_protocol_checks : bool (bool)`, `AP_Arming.cpp:1670-1682`. -/
def AP_Arming.serial_protocol_checks.body (fp : UInt64) (this : UInt64) (display_failure : Bool) : PMem.M Bool := do
  let mut display_failure := display_failure
  let t'1 ← AP.serialmanager
  let t'2 ← AP_SerialManager.have_serial t'1 (23 : Int32) (Int8.toUInt8 (Int32.toInt8 ((1 : Int32))))
  if t'2 then
    AP_Arming.check_failed'2 this display_failure (0x1a6b0 : UInt64) /- "Multiple SERIAL ports configured for RC input" -/ (fp + 0)
    return false
  let t'3 ← AP.serialmanager
  let t'4 ← AP_SerialManager.pre_arm_checks t'3 (fp + 8) (UInt64.toUInt8 (((100 : UInt64) / (1 : UInt64))))
  if !t'4 then
    PMem.stU64 (fp + 112) (fp + 8)
    AP_Arming.check_failed'2 this display_failure (0x13fd2 : UInt64) /- "%s" -/ (fp + 112)
    return false
  return true

def AP_Arming.serial_protocol_checks (this : UInt64) (display_failure : Bool) : PMem.M Bool := do
  let fp ← PMem.enter 120
  let r ← AP_Arming.serial_protocol_checks.body fp this display_failure
  PMem.leave fp
  return r

/-- C++ `AP_Arming::mandatory_checks : bool (bool)`, `AP_Arming.cpp:1886-1895`. -/
def AP_Arming.mandatory_checks (this : UInt64) (report : Bool) : PMem.M Bool := do
  let mut report := report
  let mut ret : Bool := true
  let t'1 ← AP_Arming.rc_in_calibration_check this report
  let t'2 := (ret && ((if t'1 then (1 : Int32) else (0 : Int32)) != (0 : Int32)))
  ret := t'2
  let t'3 ← AP_Arming.serial_protocol_checks this report
  let t'4 := (ret && ((if t'3 then (1 : Int32) else (0 : Int32)) != (0 : Int32)))
  ret := t'4
  return ret

/-- C++ `AP_Arming::disarm_switch_checks : bool (bool) const`, `AP_Arming.cpp:2118-2128`. -/
def AP_Arming.disarm_switch_checks.body (fp : UInt64) (this : UInt64) (display_failure : Bool) : PMem.M Bool := do
  let mut display_failure := display_failure
  let t'1 ← rc
  let t'2 ← RC_Channels.find_channel_for_option t'1 (81 : Int32)
  let mut chan : UInt64 := t'2
  let mut sc'4 := (chan != (0 : UInt64))
  if sc'4 then
    let t'3 ← RC_Channel.get_aux_switch_pos chan
    sc'4 := (t'3 == (2 : UInt8))
  if sc'4 then
    AP_Arming.check_failed'2 this display_failure (0x1a784 : UInt64) /- "Disarm Switch on" -/ (fp + 0)
    return false
  return true

def AP_Arming.disarm_switch_checks (this : UInt64) (display_failure : Bool) : PMem.M Bool := do
  let fp ← PMem.enter 8
  let r ← AP_Arming.disarm_switch_checks.body fp this display_failure
  PMem.leave fp
  return r

/-- C++ `AP_Arming::hardware_safety_check : bool (bool)`, `AP_Arming.cpp:803-815`. -/
def AP_Arming.hardware_safety_check.body (fp : UInt64) (this : UInt64) (report : Bool) : PMem.M Bool := do
  let mut report := report
  let t'1 ← AP_Arming.check_enabled this (2048 : Int32)
  if t'1 then
    let t'2 ← PMem.ldU64 ((0xba88 : UInt64) /- &hal -/ + 88)
    let t'3 ← PMem.halDev "AP_HAL::Util::safety_switch_state" t'2 #[]
    if ((UInt32.toInt32 (UInt8.toUInt32 ((UInt64.toUInt8 (t'3))))) == (UInt32.toInt32 (UInt8.toUInt32 ((1 : UInt8))))) then
      AP_Arming.check_failed this (2048 : Int32) report (0x13bc3 : UInt64) /- "Safety Switch" -/ (fp + 0)
      return false
  return true

def AP_Arming.hardware_safety_check (this : UInt64) (report : Bool) : PMem.M Bool := do
  let fp ← PMem.enter 8
  let r ← AP_Arming.hardware_safety_check.body fp this report
  PMem.leave fp
  return r

/-- C++ `AP_Arming::barometer_checks : bool (bool)`, `AP_Arming.cpp:394-414`. -/
def AP_Arming.barometer_checks.body (fp : UInt64) (this : UInt64) (report : Bool) : PMem.M Bool := do
  let mut report := report
  let t'1 ← VehicleBridge.sitl'0
  let t'2 ← AP_ParamT'signed_char_1.operator_const_signed_char__ (t'1 + 245)
  let t'3 ← PMem.ldI8 t'2
  if ((Int8.toInt32 (t'3)) == (0 : Int32)) then
    return true
  let t'4 ← AP_Arming.check_enabled this (2 : Int32)
  if t'4 then
    let t'5 ← VehicleBridge.baro'0
    let t'6 ← VehicleBridge.AP_Baro.arming_checks'2 t'5 (51 : UInt64) (fp + 0)
    worldOutputs'drain
    if !t'6 then
      PMem.stU64 (fp + 56) (fp + 0)
      AP_Arming.check_failed this (2 : Int32) report (0x1a18a : UInt64) /- "Baro: %s" -/ (fp + 56)
      return false
  return true

def AP_Arming.barometer_checks (this : UInt64) (report : Bool) : PMem.M Bool := do
  let fp ← PMem.enter 64
  let r ← AP_Arming.barometer_checks.body fp this report
  PMem.leave fp
  return r

/-- C++ `AP_Arming::ins_checks : bool (bool)`, `AP_Arming.cpp:510-608`. -/
def AP_Arming.ins_checks.body (fp : UInt64) (this : UInt64) (report : Bool) : PMem.M Bool := do
  let mut report := report
  let t'1 ← AP_Arming.check_enabled this (16 : Int32)
  if t'1 then
    let t'2 ← VehicleBridge.ins'0
    let ins : UInt64 := t'2
    let t'3 ← VehicleBridge.AP_InertialSensor.get_gyro_health_all'0 ins
    if !t'3 then
      AP_Arming.check_failed this (16 : Int32) report (0x1a193 : UInt64) /- "Gyros not healthy" -/ (fp + 0)
      return false
    let t'4 ← VehicleBridge.AP_InertialSensor.gyro_calibrated_ok_all'0 ins
    if !t'4 then
      AP_Arming.check_failed this (16 : Int32) report (0x1a1a5 : UInt64) /- "Gyros not calibrated" -/ (fp + 8)
      return false
    let t'5 ← VehicleBridge.AP_InertialSensor.get_accel_health_all'0 ins
    if !t'5 then
      AP_Arming.check_failed this (16 : Int32) report (0x1a1ba : UInt64) /- "Accels not healthy" -/ (fp + 16)
      return false
    let t'6 ← VehicleBridge.AP_InertialSensor.accel_calibrated_ok_all'0 ins
    if !t'6 then
      AP_Arming.check_failed this (16 : Int32) report (0x1a1cd : UInt64) /- "3D Accel calibration needed" -/ (fp + 24)
      return false
    let t'7 ← VehicleBridge.AP_InertialSensor.accel_cal_requires_reboot'0 ins
    if t'7 then
      AP_Arming.check_failed this (16 : Int32) report (0x1a1e9 : UInt64) /- "Accels calibrated requires reboot" -/ (fp + 32)
      return false
    let mut run_imu_consistency_check : Bool := true
    if (run_imu_consistency_check && (decide ((10000 : Int32) > (0 : Int32)))) then
      let t'8 ← AP_Arming.ins_accels_consistent this ins
      let mut accels_consistent : Bool := t'8
      let t'9 ← AP_Arming.ins_gyros_consistent this ins
      let mut gyros_consistent : Bool := t'9
      if !accels_consistent then
        AP_Arming.check_failed this (16 : Int32) report (0x1a20b : UInt64) /- "Accels inconsistent" -/ (fp + 40)
        return false
      if !gyros_consistent then
        AP_Arming.check_failed this (16 : Int32) report (0x1a21f : UInt64) /- "Gyros inconsistent" -/ (fp + 48)
        return false
    let t'10 ← VehicleBridge.AP_InertialSensor.temperature_cal_running'0 ins
    if t'10 then
      AP_Arming.check_failed this (16 : Int32) report (0x1a232 : UInt64) /- "temperature cal running" -/ (fp + 56)
      return false
    let t'11 ← VehicleBridge.AP_InertialSensor.pre_arm_check_gyro_backend_rate_hz'2 ins (fp + 64) (UInt64.toUInt16 (((51 : UInt64) / (1 : UInt64))))
    worldOutputs'drain
    if !t'11 then
      PMem.stU64 (fp + 120) (fp + 64)
      AP_Arming.check_failed this (16 : Int32) report (0x13fd2 : UInt64) /- "%s" -/ (fp + 120)
      return false
  return true

def AP_Arming.ins_checks (this : UInt64) (report : Bool) : PMem.M Bool := do
  let fp ← PMem.enter 128
  let r ← AP_Arming.ins_checks.body fp this report
  PMem.leave fp
  return r

/-- C++ `AP_Arming::compass_checks : bool (bool)`, `AP_Arming.cpp:611-699`. -/
def AP_Arming.compass_checks.body (fp : UInt64) (this : UInt64) (report : Bool) : PMem.M Bool := do
  let mut report := report
  let t'1 ← VehicleBridge.compass'0
  let _compass : UInt64 := t'1
  let t'2 ← AP_Arming.check_enabled this (4 : Int32)
  if t'2 then
    let t'3 ← VehicleBridge.Compass.use_for_yaw'1 _compass (Int8.toUInt8 (Int32.toInt8 ((0 : Int32))))
    if !t'3 then
      return true
    let t'4 ← VehicleBridge.Compass.healthy'0 _compass
    if !t'4 then
      let t'5 ← VehicleBridge.Compass.get_first_usable'0 _compass
      PMem.stU64 (fp + 0) (Int64.toUInt64 (Int32.toInt64 (((UInt32.toInt32 (UInt8.toUInt32 (t'5))) + (1 : Int32)))))
      AP_Arming.check_failed this (4 : Int32) report (0x13b84 : UInt64) /- "Compass %d not healthy" -/ (fp + 0)
      return false
    let t'6 ← VehicleBridge.Compass.configured'2 _compass (fp + 8) (UInt64.toUInt8 (((100 : UInt64) / (1 : UInt64))))
    if !t'6 then
      PMem.stU64 (fp + 112) (fp + 8)
      AP_Arming.check_failed this (4 : Int32) report (0x13fd2 : UInt64) /- "%s" -/ (fp + 112)
      return false
    VehicleBridge.Compass.get_offsets'0 _compass (fp + 136)
    let t'7 := (fp + 136)
    Vector3'float.Vector3'4 (fp + 120) t'7
    let t'8 ← Vector3'float.length (fp + 120)
    let t'9 ← VehicleBridge.Compass.get_offsets_max'0 _compass
    if (decide (t'8 > (Int32.toBinary32 ((UInt32.toInt32 (UInt16.toUInt32 (t'9))))))) then
      AP_Arming.check_failed this (4 : Int32) report (0x1a24a : UInt64) /- "Compass offsets too high" -/ (fp + 152)
      return false
    VehicleBridge.Compass.get_field'0 _compass (fp + 160)
    let t'10 := (fp + 160)
    let t'11 ← Vector3'float.length t'10
    let mut mag_field : Binary32 := t'11
    if ((decide (mag_field > (Int32.toBinary32 ((875 : Int32))))) || (decide (mag_field < (Int32.toBinary32 ((185 : Int32)))))) then
      PMem.stU64 (fp + 176) (Binary64.toBits (Binary32.toBinary64 (mag_field)))
      PMem.stU64 (fp + 184) (Int64.toUInt64 (Int32.toInt64 ((875 : Int32))))
      PMem.stU64 (fp + 192) (Int64.toUInt64 (Int32.toInt64 ((185 : Int32))))
      AP_Arming.check_failed this (4 : Int32) report (0x1a263 : UInt64) /- "Check mag field: %4.0f, max %d, min %d" -/ (fp + 176)
      return false
    let t'12 ← VehicleBridge.Compass.consistent'0 _compass
    if !t'12 then
      AP_Arming.check_failed this (4 : Int32) report (0x1a28a : UInt64) /- "Compasses inconsistent" -/ (fp + 200)
      return false
    Location.Location (fp + 208)
    let t'13 ← VehicleBridge.ahrs'0
    let ahrs : UInt64 := t'13
    let t'14 ← AP_ParamT'short_2.operator_const_short__ (this + 32)
    let t'15 ← PMem.ldI16 t'14
    let mut sc'17 := (decide ((Int16.toInt32 (t'15)) > (0 : Int32)))
    if sc'17 then
      let t'16 ← VehicleBridge.AP_AHRS.use_compass'0 ahrs
      sc'17 := t'16
    let mut sc'19 := sc'17
    if sc'19 then
      let t'18 ← VehicleBridge.AP_AHRS.get_location'1 ahrs (fp + 208)
      sc'19 := t'18
    if sc'19 then
      VehicleBridge.AP_AHRS.get_rotation_body_to_ned'0 ahrs (fp + 240)
      let t'20 := (fp + 240)
      VehicleBridge.Compass.get_field'0 _compass (fp + 280)
      let t'21 := (fp + 280)
      Matrix3'float.operator_ t'20 (fp + 296) t'21
      let t'22 := (fp + 296)
      Vector3'float.Vector3'3 (fp + 224) t'22
      VehicleBridge.AP_Declination.get_earth_field_ga'1 (fp + 328) (fp + 208)
      let t'23 := (fp + 328)
      Vector3'float.operator_ t'23 (fp + 344) (Binary64.toBinary32 ((Binary64.ofBits 0x408f400000000000 /- 1000 -/)))
      let t'24 := (fp + 344)
      Vector3'float.Vector3'3 (fp + 312) t'24
      Vector3'float.operator_'2 (fp + 224) (fp + 376) (fp + 312)
      let t'25 := (fp + 376)
      Vector3'float.Vector3'3 (fp + 360) t'25
      let t'26 ← PMem.ldF32 (fp + 360)
      PMem.stF32 (fp + 388) (Binary32.abs t'26)
      let t'27 ← PMem.ldF32 ((fp + 360) + 4)
      PMem.stF32 (fp + 392) (Binary32.abs t'27)
      let t'28 ← MAX'float_float (fp + 388) (fp + 392)
      let t'29 ← PMem.ldF32 t'28
      let t'30 ← AP_ParamT'short_2.operator_const_short__ (this + 32)
      let t'31 ← PMem.ldI16 t'30
      if (decide (t'29 > (Int32.toBinary32 ((Int16.toInt32 (t'31)))))) then
        let t'32 ← PMem.ldF32 (fp + 360)
        PMem.stF32 (fp + 416) (Binary32.abs t'32)
        let t'33 ← PMem.ldF32 ((fp + 360) + 4)
        PMem.stF64 (fp + 424) (Binary32.toBinary64 ((Binary32.abs t'33)))
        let t'34 ← MAX'float_double (fp + 416) (fp + 424)
        PMem.stU64 (fp + 400) (Binary64.toBits t'34)
        let t'35 ← AP_ParamT'short_2.operator_const_short__ (this + 32)
        let t'36 ← PMem.ldI16 t'35
        PMem.stU64 (fp + 408) (Int64.toUInt64 (Int32.toInt64 ((Int16.toInt32 (t'36)))))
        AP_Arming.check_failed this (4 : Int32) report (0x1a2a1 : UInt64) /- "Check mag field (xy diff:%.0f>%d)" -/ (fp + 400)
        return false
      let t'37 ← PMem.ldF32 ((fp + 360) + 8)
      let t'38 ← AP_ParamT'short_2.operator_const_short__ (this + 32)
      let t'39 ← PMem.ldI16 t'38
      if (decide ((Binary32.abs t'37) > ((Int32.toBinary32 ((Int16.toInt32 (t'39)))) * (Binary64.toBinary32 ((Binary64.ofBits 0x4000000000000000 /- 2 -/)))))) then
        let t'40 ← PMem.ldF32 ((fp + 360) + 8)
        PMem.stU64 (fp + 432) (Binary64.toBits (Binary32.toBinary64 ((Binary32.abs t'40))))
        let t'41 ← AP_ParamT'short_2.operator_const_short__ (this + 32)
        let t'42 ← PMem.ldI16 t'41
        PMem.stU64 (fp + 440) (Int64.toUInt64 (Int32.toInt64 (((Int16.toInt32 (t'42)) * (2 : Int32)))))
        AP_Arming.check_failed this (4 : Int32) report (0x1a2c3 : UInt64) /- "Check mag field (z diff:%.0f>%d)" -/ (fp + 432)
        return false
  return true

def AP_Arming.compass_checks (this : UInt64) (report : Bool) : PMem.M Bool := do
  let fp ← PMem.enter 448
  let r ← AP_Arming.compass_checks.body fp this report
  PMem.leave fp
  return r

/-- C++ `AP_Arming::gps_checks : bool (bool)`, `AP_Arming.cpp:702-785`. -/
def AP_Arming.gps_checks.body (fp : UInt64) (this : UInt64) (report : Bool) : PMem.M Bool := do
  let mut report := report
  let t'1 ← VehicleBridge.gps'0
  let gps : UInt64 := t'1
  let t'2 ← AP_Arming.check_enabled this (8 : Int32)
  if t'2 then
    let t'3 ← VehicleBridge.gps'0
    let t'4 ← VehicleBridge.AP_GPS.pre_arm_checks'2 t'3 (fp + 0) (UInt64.toUInt16 (((100 : UInt64) / (1 : UInt64))))
    worldOutputs'drain
    if !t'4 then
      let t'5 ← PMem.ldI8 ((fp + 0) + ((Int32.toInt64 ((0 : Int32))) * 1).toUInt64)
      if ((Int8.toInt32 (t'5)) != (Int8.toInt32 ((0 : Int8)))) then
        PMem.stU64 (fp + 104) (fp + 0)
        AP_Arming.check_failed this (8 : Int32) report (0x13fd2 : UInt64) /- "%s" -/ (fp + 104)
      return false
    let mut i : UInt8 := Int8.toUInt8 (Int32.toInt8 ((0 : Int32)))
    let mut first'6 := true
    for _ in PMem.loopFuel do
      if !first'6 then
        let t'7 := i
        let t'8 := (t'7 + 1)
        i := t'8
        pure ()
      first'6 := false
      let t'9 ← VehicleBridge.AP_GPS.num_sensors'0 gps
      if !((decide ((UInt32.toInt32 (UInt8.toUInt32 (i))) < (UInt32.toInt32 (UInt8.toUInt32 (t'9)))))) then break
      let t'10 ← VehicleBridge.AP_GPS.get_type'1 gps i
      if ((UInt32.toInt32 (t'10)) == (UInt32.toInt32 ((0 : UInt32)))) then
        let t'11 ← VehicleBridge.AP_GPS.primary_sensor'0 gps
        if ((UInt32.toInt32 (UInt8.toUInt32 (t'11))) == (UInt32.toInt32 (UInt8.toUInt32 (i)))) then
          PMem.stU64 (fp + 112) (Int64.toUInt64 (Int32.toInt64 (((UInt32.toInt32 (UInt8.toUInt32 (i))) + (1 : Int32)))))
          AP_Arming.check_failed this (8 : Int32) report (0x1a2e4 : UInt64) /- "GPS %i: primary but TYPE 0" -/ (fp + 112)
          return false
        continue
      let t'12 ← VehicleBridge.AP_GPS.status'1 gps i
      if (decide (t'12 < (3 : UInt8))) then
        PMem.stU64 (fp + 120) (Int64.toUInt64 (Int32.toInt64 (((UInt32.toInt32 (UInt8.toUInt32 (i))) + (1 : Int32)))))
        AP_Arming.check_failed this (8 : Int32) report (0x1a2ff : UInt64) /- "GPS %i: Bad fix" -/ (fp + 120)
        return false
      let t'13 ← VehicleBridge.AP_GPS.is_healthy'1 gps i
      if !t'13 then
        PMem.stU64 (fp + 128) (Int64.toUInt64 (Int32.toInt64 (((UInt32.toInt32 (UInt8.toUInt32 (i))) + (1 : Int32)))))
        AP_Arming.check_failed this (8 : Int32) report (0x1a30f : UInt64) /- "GPS %i: not healthy" -/ (fp + 128)
        return false
    let t'14 ← VehicleBridge.ahrs'0
    let t'15 ← VehicleBridge.AP_AHRS.home_is_set'0 t'14
    if !t'15 then
      AP_Arming.check_failed this (8 : Int32) report (0x1a323 : UInt64) /- "AHRS: waiting for home" -/ (fp + 136)
      return false
    let t'16 ← VehicleBridge.AP_GPS.all_consistent'1 gps (fp + 144)
    if !t'16 then
      let t'17 ← PMem.ldF32 (fp + 144)
      PMem.stU64 (fp + 152) (Binary64.toBits (Binary32.toBinary64 (t'17)))
      AP_Arming.check_failed this (8 : Int32) report (0x1a33a : UInt64) /- "GPS positions differ by %4.1fm" -/ (fp + 152)
      return false
    let t'18 ← VehicleBridge.AP_GPS.num_sensors'0 gps
    if (decide ((UInt32.toInt32 (UInt8.toUInt32 (t'18))) > (0 : Int32))) then
      VehicleBridge.AP_GPS.location'0 gps (fp + 176)
      let t'19 := (fp + 176)
      discard <| PMem.memcpy (fp + 160) t'19 16
      Location.Location (fp + 192)
      let t'20 ← VehicleBridge.ahrs'0
      let t'21 ← VehicleBridge.AP_AHRS.get_location'1 t'20 (fp + 192)
      if t'21 then
        let t'22 ← Location.get_distance (fp + 160) (fp + 192)
        let mut distance : Binary32 := Binary64.toBinary32 (t'22)
        if (decide (distance > (Int32.toBinary32 ((10 : Int32))))) then
          PMem.stU64 (fp + 208) (Binary64.toBits (Binary32.toBinary64 (distance)))
          AP_Arming.check_failed this (8 : Int32) report (0x1a359 : UInt64) /- "GPS and AHRS differ by %4.1fm" -/ (fp + 208)
          return false
  let t'23 ← AP_Arming.check_enabled this (4096 : Int32)
  if t'23 then
    let t'24 ← VehicleBridge.AP_GPS.first_unconfigured_gps'1 gps (fp + 216)
    if t'24 then
      let t'25 ← PMem.ldU8 (fp + 216)
      PMem.stU64 (fp + 224) (Int64.toUInt64 (Int32.toInt64 (((UInt32.toInt32 (UInt8.toUInt32 (t'25))) + (1 : Int32)))))
      AP_Arming.check_failed this (4096 : Int32) report (0x1a377 : UInt64) /- "GPS %d still configuring this GPS" -/ (fp + 224)
      if report then
        VehicleBridge.AP_GPS.broadcast_first_configuration_failure_reason'0 gps
        worldOutputs'drain
      return false
  return true

def AP_Arming.gps_checks (this : UInt64) (report : Bool) : PMem.M Bool := do
  let fp ← PMem.enter 232
  let r ← AP_Arming.gps_checks.body fp this report
  PMem.leave fp
  return r

/-- C++ `AP_Arming::battery_checks : bool (bool)`, `AP_Arming.cpp:789-800`. -/
def AP_Arming.battery_checks.body (fp : UInt64) (this : UInt64) (report : Bool) : PMem.M Bool := do
  let mut report := report
  let t'1 ← AP_Arming.check_enabled this (256 : Int32)
  if t'1 then
    let t'2 ← AP.battery
    let t'3 ← AP_BattMonitor.arming_checks t'2 (51 : UInt64) (fp + 0)
    if !t'3 then
      PMem.stU64 (fp + 56) (fp + 0)
      AP_Arming.check_failed this (256 : Int32) report (0x13fd2 : UInt64) /- "%s" -/ (fp + 56)
      return false
  return true

def AP_Arming.battery_checks (this : UInt64) (report : Bool) : PMem.M Bool := do
  let fp ← PMem.enter 64
  let r ← AP_Arming.battery_checks.body fp this report
  PMem.leave fp
  return r

/-- C++ `AP_Arming::rc_checks_copter_sub : bool (const bool, const RC_Channel **) const`, `AP_Arming.cpp:2067-2092`. -/
def AP_Arming.rc_checks_copter_sub.body (fp : UInt64) (this : UInt64) (display_failure : Bool) (channels : UInt64) : PMem.M Bool := do
  let mut display_failure := display_failure
  let mut channels := channels
  let t'1 ← AP_Arming.check_enabled this (64 : Int32)
  if !t'1 then
    return true
  let mut ret : Bool := true
  PMem.stU64 ((fp + 0) + 0) (0x1a399 : UInt64) /- "Roll" -/
  PMem.stU64 ((fp + 0) + 8) (0x1a39e : UInt64) /- "Pitch" -/
  PMem.stU64 ((fp + 0) + 16) (0x139ab : UInt64) /- "Throttle" -/
  PMem.stU64 ((fp + 0) + 24) (0x163e3 : UInt64) /- "Yaw" -/
  let mut i : UInt8 := Int8.toUInt8 (Int32.toInt8 ((0 : Int32)))
  let mut first'2 := true
  for _ in PMem.loopFuel do
    if !first'2 then
      let t'3 := i
      let t'4 := (t'3 + 1)
      i := t'4
      pure ()
    first'2 := false
    if !((decide ((UInt8.toUInt64 (i)) < ((32 : UInt64) / (8 : UInt64))))) then break
    let t'5 ← PMem.ldU64 (channels + ((UInt64.toInt64 (UInt8.toUInt64 (i))) * 8).toUInt64)
    let mut channel : UInt64 := t'5
    let t'6 ← PMem.ldU64 ((fp + 0) + ((UInt64.toInt64 (UInt8.toUInt64 (i))) * 8).toUInt64)
    let mut channel_name : UInt64 := t'6
    let t'7 ← RC_Channel.get_radio_min channel
    if (decide ((Int16.toInt32 (t'7)) > (UInt32.toInt32 (UInt16.toUInt32 ((1300 : UInt16)))))) then
      PMem.stU64 (fp + 32) channel_name
      AP_Arming.check_failed this (64 : Int32) display_failure (0x1a759 : UInt64) /- "%s radio min too high" -/ (fp + 32)
      ret := false
    let t'8 ← RC_Channel.get_radio_max channel
    if (decide ((Int16.toInt32 (t'8)) < (UInt32.toInt32 (UInt16.toUInt32 ((1700 : UInt16)))))) then
      PMem.stU64 (fp + 40) channel_name
      AP_Arming.check_failed this (64 : Int32) display_failure (0x1a76f : UInt64) /- "%s radio max too low" -/ (fp + 40)
      ret := false
  return ret

def AP_Arming.rc_checks_copter_sub (this : UInt64) (display_failure : Bool) (channels : UInt64) : PMem.M Bool := do
  let fp ← PMem.enter 48
  let r ← AP_Arming.rc_checks_copter_sub.body fp this display_failure channels
  PMem.leave fp
  return r

/-- C++ `AP_Arming::rc_calibration_checks : bool (bool)`, `AP_Arming.cpp:895-919`. -/
def AP_Arming.rc_calibration_checks.body (fp : UInt64) (this : UInt64) (report : Bool) : PMem.M Bool := do
  let mut report := report
  let mut check_passed : Bool := true
  let t'1 ← RC_Channels.get_valid_channel_count
  let mut num_channels : UInt8 := t'1
  for i'2 in [0:16] do
    let i : UInt8 := UInt8.ofNat i'2
    let t'3 ← rc
    let t'4 ← RC_Channels_Copter.channel t'3 i
    let mut c : UInt64 := t'4
    if (c == (0 : UInt64)) then
      continue
    let mut sc'6 := (decide ((UInt32.toInt32 (UInt8.toUInt32 (i))) ≥ (UInt32.toInt32 (UInt8.toUInt32 (num_channels)))))
    if sc'6 then
      let t'5 ← RC_Channel.has_override c
      sc'6 := !t'5
    if sc'6 then
      continue
    let t'7 ← RC_Channel.get_radio_trim c
    let mut trim : UInt16 := Int16.toUInt16 (t'7)
    let t'8 ← RC_Channel.get_radio_min c
    if (decide ((Int16.toInt32 (t'8)) > (UInt32.toInt32 (UInt16.toUInt32 (trim))))) then
      PMem.stU64 (fp + 0) (Int64.toUInt64 (Int32.toInt64 (((UInt32.toInt32 (UInt8.toUInt32 (i))) + (1 : Int32)))))
      PMem.stU64 (fp + 8) (Int64.toUInt64 (Int32.toInt64 (((UInt32.toInt32 (UInt8.toUInt32 (i))) + (1 : Int32)))))
      AP_Arming.check_failed this (64 : Int32) report (0x1a41e : UInt64) /- "RC%d_MIN is greater than RC%d_TRIM" -/ (fp + 0)
      check_passed := false
    let t'9 ← RC_Channel.get_radio_max c
    if (decide ((Int16.toInt32 (t'9)) < (UInt32.toInt32 (UInt16.toUInt32 (trim))))) then
      PMem.stU64 (fp + 16) (Int64.toUInt64 (Int32.toInt64 (((UInt32.toInt32 (UInt8.toUInt32 (i))) + (1 : Int32)))))
      PMem.stU64 (fp + 24) (Int64.toUInt64 (Int32.toInt64 (((UInt32.toInt32 (UInt8.toUInt32 (i))) + (1 : Int32)))))
      AP_Arming.check_failed this (64 : Int32) report (0x1a441 : UInt64) /- "RC%d_MAX is less than RC%d_TRIM" -/ (fp + 16)
      check_passed := false
  return check_passed

def AP_Arming.rc_calibration_checks (this : UInt64) (report : Bool) : PMem.M Bool := do
  let fp ← PMem.enter 32
  let r ← AP_Arming.rc_calibration_checks.body fp this report
  PMem.leave fp
  return r

/-- C++ `AP_Arming::rc_option_checks : bool (bool)`, `AP_Arming.cpp:877-893`. -/
def AP_Arming.rc_option_checks.body (fp : UInt64) (this : UInt64) (report : Bool) : PMem.M Bool := do
  let mut report := report
  let t'1 ← AP_Arming.check_enabled this (64 : Int32)
  if !t'1 then
    return true
  let mut check_passed : Bool := true
  let t'2 ← rc
  let t'3 ← RC_Channels.duplicate_options_exist t'2
  if t'3 then
    AP_Arming.check_failed this (32 : Int32) report (0x1a3db : UInt64) /- "Duplicate Aux Switch Options" -/ (fp + 0)
    check_passed := false
  let t'4 ← rc
  let t'5 ← RC_Channels.flight_mode_channel_conflicts_with_rc_option t'4
  if t'5 then
    let t'6 ← rc
    let t'7 ← RC_Channels_Copter.flight_mode_channel_number t'6
    PMem.stU64 (fp + 8) (Int64.toUInt64 (Int32.toInt64 ((Int8.toInt32 (t'7)))))
    AP_Arming.check_failed this (32 : Int32) report (0x1a3f8 : UInt64) /- "Mode channel and RC%d_OPTION conflict" -/ (fp + 8)
    check_passed := false
  return check_passed

def AP_Arming.rc_option_checks (this : UInt64) (report : Bool) : PMem.M Bool := do
  let fp ← PMem.enter 16
  let r ← AP_Arming.rc_option_checks.body fp this report
  PMem.leave fp
  return r

/-- C++ `AP_Arming::mission_checks : bool (bool)`, `AP_Arming.cpp:949-1035`. -/
def AP_Arming.mission_checks.body (fp : UInt64) (this : UInt64) (report : Bool) : PMem.M Bool := do
  let mut report := report
  let t'1 ← AP.mission
  let mission : UInt64 := t'1
  let t'2 ← AP_Arming.check_enabled this (16384 : Int32)
  let mut sc'5 := t'2
  if sc'5 then
    let t'3 ← AP_ParamT'unsigned_int_3.operator_const_unsigned_int__ (this + 24)
    let t'4 ← PMem.ldU32 t'3
    sc'5 := t'4 != (0 : UInt32)
  if sc'5 then
    PMem.stU32 (((fp + 0) + 0) + 0) (1 : UInt32)
    PMem.stU32 (((fp + 0) + 0) + 4) (21 : UInt32)
    PMem.stU64 (((fp + 0) + 0) + 8) (0x1a482 : UInt64) /- "land" -/
    PMem.stU32 (((fp + 0) + 16) + 0) (2 : UInt32)
    PMem.stU32 (((fp + 0) + 16) + 4) (85 : UInt32)
    PMem.stU64 (((fp + 0) + 16) + 8) (0x1a487 : UInt64) /- "vtol land" -/
    PMem.stU32 (((fp + 0) + 32) + 0) (4 : UInt32)
    PMem.stU32 (((fp + 0) + 32) + 4) (189 : UInt32)
    PMem.stU64 (((fp + 0) + 32) + 8) (0x1a491 : UInt64) /- "do land start" -/
    PMem.stU32 (((fp + 0) + 48) + 0) (8 : UInt32)
    PMem.stU32 (((fp + 0) + 48) + 4) (22 : UInt32)
    PMem.stU64 (((fp + 0) + 48) + 8) (0x1a49f : UInt64) /- "takeoff" -/
    PMem.stU32 (((fp + 0) + 64) + 0) (16 : UInt32)
    PMem.stU32 (((fp + 0) + 64) + 4) (84 : UInt32)
    PMem.stU64 (((fp + 0) + 64) + 8) (0x1a4a7 : UInt64) /- "vtol takeoff" -/
    PMem.stU32 (((fp + 0) + 80) + 0) (64 : UInt32)
    PMem.stU32 (((fp + 0) + 80) + 4) (20 : UInt32)
    PMem.stU64 (((fp + 0) + 80) + 8) (0x14c9a : UInt64) /- "RTL" -/
    let mut i : UInt8 := Int8.toUInt8 (Int32.toInt8 ((0 : Int32)))
    let mut first'6 := true
    for _ in PMem.loopFuel do
      if !first'6 then
        let t'7 := i
        let t'8 := (t'7 + 1)
        i := t'8
        pure ()
      first'6 := false
      if !((decide ((UInt8.toUInt64 (i)) < ((96 : UInt64) / (16 : UInt64))))) then break
      let t'9 ← AP_ParamT'unsigned_int_3.operator_const_unsigned_int__ (this + 24)
      let t'10 ← PMem.ldU32 t'9
      let t'11 ← PMem.ldU32 ((fp + 0) + ((UInt64.toInt64 (UInt8.toUInt64 (i))) * 16).toUInt64)
      if (t'10 &&& t'11) != (0 : UInt32) then
        let t'12 ← PMem.ldU32 (((fp + 0) + ((UInt64.toInt64 (UInt8.toUInt64 (i))) * 16).toUInt64) + 4)
        let t'13 ← AP_Mission.contains_item mission t'12
        if !t'13 then
          let t'14 ← PMem.ldU64 (((fp + 0) + ((UInt64.toInt64 (UInt8.toUInt64 (i))) * 16).toUInt64) + 8)
          PMem.stU64 (fp + 96) t'14
          AP_Arming.check_failed this (16384 : Int32) report (0x1a4b4 : UInt64) /- "Missing mission item: %s" -/ (fp + 96)
          return false
    let t'15 ← AP_ParamT'unsigned_int_3.operator_const_unsigned_int__ (this + 24)
    let t'16 ← PMem.ldU32 t'15
    if (t'16 &&& (32 : UInt32)) != (0 : UInt32) then
      AP_Arming.check_failed this (16384 : Int32) report (0x1a4cd : UInt64) /- "No rally library present" -/ (fp + 104)
      return false
  let t'17 ← AP_Arming.check_enabled this (16384 : Int32)
  if t'17 then
    let t'18 ← AP_Mission.num_commands mission
    let mut num_commands : UInt16 := t'18
    for i'2'19 in [1:num_commands.toNat] do
      let i'2 : UInt16 := UInt16.ofNat i'2'19
      let t'20 ← AP_Mission.get_command_id mission i'2
      let t'21 ← AP_Mission.is_takeoff_type_cmd mission t'20
      if !t'21 then
        continue
      AP_Mission.Mission_Command.Mission_Command (fp + 112)
      let t'22 ← AP_Mission.read_cmd_from_storage mission i'2 (fp + 112)
      if !t'22 then
        continue
      let t'23 ← PMem.ldI32 (((fp + 112) + 8) + 4)
      if (t'23 == (0 : Int32)) then
        AP_Arming.check_failed this (16384 : Int32) report (0x1a4e6 : UInt64) /- "Mission: Zero takeoff altitude" -/ (fp + 144)
        return false
  let t'24 ← AP_Arming.check_enabled this (16384 : Int32)
  let mut sc'28 := t'24
  if sc'28 then
    let t'25 ← AP_Mission.failed_sdcard_storage mission
    let mut sc'27 := t'25
    if !sc'27 then
      let t'26 ← StorageManager.storage_failed
      sc'27 := t'26
    sc'28 := sc'27
  if sc'28 then
    PMem.stU64 (fp + 152) (0x173b2 : UInt64) /- "mission.stg" -/
    AP_Arming.check_failed this (16384 : Int32) report (0x1a505 : UInt64) /- "Failed to open %s" -/ (fp + 152)
    return false
  let t'29 ← AP.vehicle
  let t'30 ← Copter.current_mode_requires_mission t'29
  let mut sc'32 := t'30
  if sc'32 then
    let t'31 ← AP_Mission.present mission
    sc'32 := !t'31
  if sc'32 then
    AP_Arming.check_failed this (16384 : Int32) report (0x1a517 : UInt64) /- "Mode requires mission" -/ (fp + 160)
    return false
  return true

def AP_Arming.mission_checks (this : UInt64) (report : Bool) : PMem.M Bool := do
  let fp ← PMem.enter 168
  let r ← AP_Arming.mission_checks.body fp this report
  PMem.leave fp
  return r

/-- C++ `AP_Arming::servo_checks : bool (bool) const`, `AP_Arming.cpp:1058-1109`. -/
def AP_Arming.servo_checks.body (fp : UInt64) (this : UInt64) (report : Bool) : PMem.M Bool := do
  let mut report := report
  let mut check_passed : Bool := true
  for i'1 in [0:32] do
    let i : UInt8 := UInt8.ofNat i'1
    let t'2 ← SRV_Channels.srv_channel i
    let mut c : UInt64 := t'2
    let mut sc'4 := (c == (0 : UInt64))
    if !sc'4 then
      let t'3 ← SRV_Channel.get_function c
      sc'4 := (decide (t'3 ≤ (0 : Int32)))
    if sc'4 then
      continue
    let t'5 ← SRV_Channel.get_trim c
    let mut trim : UInt16 := t'5
    let t'6 ← SRV_Channel.get_output_min c
    if (decide ((UInt32.toInt32 (UInt16.toUInt32 (t'6))) > (UInt32.toInt32 (UInt16.toUInt32 (trim))))) then
      PMem.stU64 (fp + 0) (Int64.toUInt64 (Int32.toInt64 (((UInt32.toInt32 (UInt8.toUInt32 (i))) + (1 : Int32)))))
      PMem.stU64 (fp + 8) (Int64.toUInt64 (Int32.toInt64 (((UInt32.toInt32 (UInt8.toUInt32 (i))) + (1 : Int32)))))
      AP_Arming.check_failed'2 this report (0x1a52d : UInt64) /- "SERVO%d_MIN is greater than SERVO%d_TRIM" -/ (fp + 0)
      check_passed := false
    let t'7 ← SRV_Channel.get_output_max c
    if (decide ((UInt32.toInt32 (UInt16.toUInt32 (t'7))) < (UInt32.toInt32 (UInt16.toUInt32 (trim))))) then
      PMem.stU64 (fp + 16) (Int64.toUInt64 (Int32.toInt64 (((UInt32.toInt32 (UInt8.toUInt32 (i))) + (1 : Int32)))))
      PMem.stU64 (fp + 24) (Int64.toUInt64 (Int32.toInt64 (((UInt32.toInt32 (UInt8.toUInt32 (i))) + (1 : Int32)))))
      AP_Arming.check_failed'2 this report (0x1a556 : UInt64) /- "SERVO%d_MAX is less than SERVO%d_TRIM" -/ (fp + 16)
      check_passed := false
    let t'8 ← SRV_Channels.get_disabled_channel_mask
    if (t'8 &&& ((1 : UInt32) <<< (Int32.toUInt32 ((UInt32.toInt32 (UInt8.toUInt32 (i))))))) != (0 : UInt32) then
      let t'9 ← SRV_Channel.get_function c
      let mut ch_function : Int32 := t'9
      let t'10 ← SRV_Channel.is_motor ch_function
      let mut sc'12 := t'10
      if !sc'12 then
        let t'11 ← SRV_Channel.should_e_stop ch_function
        sc'12 := t'11
      let mut disabled_ok : Bool := (((sc'12 || ((decide (ch_function ≥ (120 : Int32))) && (decide (ch_function ≤ (123 : Int32))))) || ((decide (ch_function ≥ (129 : Int32))) && (decide (ch_function ≤ (132 : Int32))))) || ((decide (ch_function ≥ (94 : Int32))) && (decide (ch_function ≤ (109 : Int32)))))
      if !disabled_ok then
        PMem.stU64 (fp + 32) (Int64.toUInt64 (Int32.toInt64 (((UInt32.toInt32 (UInt8.toUInt32 (i))) + (1 : Int32)))))
        PMem.stU64 (fp + 40) (UInt32.toUInt64 ((Int32.toUInt32 (ch_function))))
        AP_Arming.check_failed'2 this report (0x1a57c : UInt64) /- "SERVO%u_FUNCTION=%u on disabled channel" -/ (fp + 32)
        check_passed := false
  return check_passed

def AP_Arming.servo_checks (this : UInt64) (report : Bool) : PMem.M Bool := do
  let fp ← PMem.enter 48
  let r ← AP_Arming.servo_checks.body fp this report
  PMem.leave fp
  return r

/-- C++ `AP_Arming::board_voltage_checks : bool (bool)`, `AP_Arming.cpp:1111-1137`. -/
def AP_Arming.board_voltage_checks.body (fp : UInt64) (this : UInt64) (report : Bool) : PMem.M Bool := do
  let mut report := report
  let t'1 ← AP_Arming.check_enabled this (128 : Int32)
  if t'1 then
    let t'2 ← PMem.ldU64 ((0xba88 : UInt64) /- &hal -/ + 32)
    let t'3 ← PMem.halDev "AP_HAL::AnalogIn::board_voltage" t'2 #[]
    let mut bus_voltage : Binary32 := (Binary32.ofBits t'3.toUInt32)
    let t'4 ← AP_BoardConfig.get_minimum_board_voltage
    let mut vbus_min : Binary32 := t'4
    if ((decide (bus_voltage < vbus_min)) || (decide (bus_voltage > (Binary32.ofBits 0x40b9999a /- 580000019/100000000 -/)))) then
      PMem.stU64 (fp + 0) (Binary64.toBits (Binary32.toBinary64 (bus_voltage)))
      PMem.stU64 (fp + 8) (Binary64.toBits (Binary32.toBinary64 (vbus_min)))
      PMem.stU64 (fp + 16) (Binary64.toBits (Binary32.toBinary64 ((Binary32.ofBits 0x40b9999a /- 580000019/100000000 -/))))
      AP_Arming.check_failed this (128 : Int32) report (0x1a5a4 : UInt64) /- "Board (%1.1fv) out of range %1.1f-%1.1fv" -/ (fp + 0)
      return false
    let t'5 ← AP_BoardConfig.get_minimum_servo_voltage
    let mut vservo_min : Binary32 := t'5
    let t'6 ← is_positive'float vservo_min
    if t'6 then
      let t'7 ← PMem.ldU64 ((0xba88 : UInt64) /- &hal -/ + 32)
      let t'8 ← PMem.halDev "AP_HAL::AnalogIn::servorail_voltage" t'7 #[]
      let mut servo_voltage : Binary32 := (Binary32.ofBits t'8.toUInt32)
      if (decide (servo_voltage < vservo_min)) then
        PMem.stU64 (fp + 24) (Binary64.toBits (Binary32.toBinary64 (servo_voltage)))
        PMem.stU64 (fp + 32) (Binary64.toBits (Binary32.toBinary64 (vservo_min)))
        AP_Arming.check_failed this (128 : Int32) report (0x1a5cd : UInt64) /- "Servo voltage to low (%1.2fv < %1.2fv)" -/ (fp + 24)
        return false
  return true

def AP_Arming.board_voltage_checks (this : UInt64) (report : Bool) : PMem.M Bool := do
  let fp ← PMem.enter 40
  let r ← AP_Arming.board_voltage_checks.body fp this report
  PMem.leave fp
  return r

/-- C++ `AP_Arming::blending_auto_switch_checks : bool (bool)`, `AP_Arming.cpp:1850-1859`. -/
def AP_Arming.blending_auto_switch_checks.body (fp : UInt64) (this : UInt64) (report : Bool) : PMem.M Bool := do
  let mut report := report
  let t'1 ← VehicleBridge.gps'0
  let t'2 ← VehicleBridge.AP_GPS.get_auto_switch_type'0 t'1
  if ((UInt32.toInt32 (UInt8.toUInt32 (t'2))) == (2 : Int32)) then
    if report then
      AP_Arming.check_failed this (8 : Int32) true (0x1a6f7 : UInt64) /- "GPS_AUTO_SWITCH==2 but no blending" -/ (fp + 0)
    return false
  return true

def AP_Arming.blending_auto_switch_checks (this : UInt64) (report : Bool) : PMem.M Bool := do
  let fp ← PMem.enter 8
  let r ← AP_Arming.blending_auto_switch_checks.body fp this report
  PMem.leave fp
  return r

/-- C++ `AP_Arming::system_checks : bool (bool)`, `AP_Arming.cpp:1162-1256`. -/
def AP_Arming.system_checks.body (fp : UInt64) (this : UInt64) (report : Bool) : PMem.M Bool := do
  let mut report := report
  let t'1 ← AP_Arming.check_enabled this (8192 : Int32)
  if t'1 then
    let t'2 ← PMem.ldU64 ((0xba88 : UInt64) /- &hal -/ + 40)
    let t'3 ← PMem.halDev "AP_HAL::Storage::healthy" t'2 #[]
    if !(t'3 != 0) then
      AP_Arming.check_failed this (8192 : Int32) report (0x1a5f4 : UInt64) /- "Param storage failed" -/ (fp + 56)
      return false
    let t'4 ← AP_Param.get_eeprom_full
    if t'4 then
      AP_Arming.check_failed this (32 : Int32) report (0x1a609 : UInt64) /- "parameter storage full" -/ (fp + 64)
      return false
    let t'5 ← AP.scheduler
    let t'6 ← AP_Scheduler.get_filtered_loop_rate_hz t'5
    let mut actual_loop_rate : Binary32 := t'6
    let t'7 ← AP.scheduler
    let t'8 ← AP_Scheduler.get_loop_rate_hz t'7
    let mut expected_loop_rate : UInt16 := t'8
    let mut loop_rate_pct : Binary32 := (actual_loop_rate / (Int32.toBinary32 ((UInt32.toInt32 (UInt16.toUInt32 (expected_loop_rate))))))
    if (decide (loop_rate_pct < (Binary64.toBinary32 ((Binary64.ofBits 0x3feccccccccccccd /- 45000000000000001/50000000000000000 -/))))) then
      PMem.stU64 (fp + 72) (UInt32.toUInt64 ((Binary32.toUInt32 (actual_loop_rate))))
      PMem.stU64 (fp + 80) (UInt32.toUInt64 ((UInt16.toUInt32 (expected_loop_rate))))
      AP_Arming.check_failed this (8192 : Int32) report (0x1a620 : UInt64) /- "Main loop slow (%uHz < %uHz)" -/ (fp + 72)
      return false
  let t'9 := (0 : UInt64)
  let t'10 ← AP_InternalError.errors t'9
  if (t'10 != (Int32.toUInt32 ((0 : Int32)))) then
    let t'11 := (0 : UInt64)
    AP_InternalError.errors_as_string t'11 (fp + 0) (UInt64.toUInt16 (((51 : UInt64) / (1 : UInt64))))
    let t'12 := (0 : UInt64)
    let t'13 ← AP_InternalError.errors t'12
    PMem.stU64 (fp + 88) (UInt32.toUInt64 (t'13))
    let t'14 := (0 : UInt64)
    let t'15 ← AP_InternalError.last_error_line t'14
    PMem.stU64 (fp + 96) (Int64.toUInt64 (Int32.toInt64 ((UInt32.toInt32 (UInt16.toUInt32 (t'15))))))
    PMem.stU64 (fp + 104) (fp + 0)
    AP_Arming.check_failed'2 this report (0x1a63d : UInt64) /- "Internal errors 0x%x l:%u %s" -/ (fp + 88)
    return false
  let t'16 ← PMem.ldU64 ((0xba88 : UInt64) /- &hal -/ + 56)
  let t'17 ← PMem.halDev "AP_HAL::GPIO::arming_checks" t'16 #[(51 : UInt64), (fp + 0)]
  if !(t'17 != 0) then
    PMem.stU64 (fp + 112) (fp + 0)
    AP_Arming.check_failed'2 this report (0x13fd2 : UInt64) /- "%s" -/ (fp + 112)
    return false
  let t'18 ← AP_Arming.check_enabled this (32 : Int32)
  if t'18 then
    let t'19 ← AP_Arming.blending_auto_switch_checks this report
    if !t'19 then
      return false
  return true

def AP_Arming.system_checks (this : UInt64) (report : Bool) : PMem.M Bool := do
  let fp ← PMem.enter 120
  let r ← AP_Arming.system_checks.body fp this report
  PMem.leave fp
  return r

/-- C++ `AP_Arming::terrain_checks : bool (bool) const`, `AP_Arming.cpp:1275-1310`. -/
def AP_Arming.terrain_checks.body (fp : UInt64) (this : UInt64) (report : Bool) : PMem.M Bool := do
  let mut report := report
  let t'1 ← AP_Arming.check_enabled this (32 : Int32)
  if !t'1 then
    return true
  let t'2 ← AP_Arming_Copter.terrain_database_required this
  if !t'2 then
    return true
  AP_Arming.check_failed this (32 : Int32) report (0x1a65a : UInt64) /- "terrain required but disabled" -/ (fp + 0)
  return false

def AP_Arming.terrain_checks (this : UInt64) (report : Bool) : PMem.M Bool := do
  let fp ← PMem.enter 8
  let r ← AP_Arming.terrain_checks.body fp this report
  PMem.leave fp
  return r

/-- C++ `AP_Arming::can_checks : bool (bool)`, `AP_Arming.cpp:1332-1391`. -/
def AP_Arming.can_checks.body (fp : UInt64) (this : UInt64) (report : Bool) : PMem.M Bool := do
  let mut report := report
  let t'1 ← AP_Arming.check_enabled this (8192 : Int32)
  if t'1 then
    discard <| pure ((fp + 0))
    let t'2 ← AP.can
    let t'3 ← AP_CANManager.get_num_drivers t'2
    let mut num_drivers : UInt8 := t'3
    for i'4 in [0:num_drivers.toNat] do
      let i : UInt8 := UInt8.ofNat i'4
      for _ in [0:1] do
        let t'5 ← AP.can
        let t'6 ← AP_CANManager.get_driver_type t'5 i
        let sw'7 := t'6
        if sw'7 == (4 : UInt8) then
          AP_Arming.check_failed this (8192 : Int32) report (0x1a678 : UInt64) /- "PiccoloCAN not enabled" -/ (fp + 104)
          return false
          break
          break
          let mut j : UInt8 := i
          let mut first'8 := true
          for _ in PMem.loopFuel do
            if !first'8 then
              let t'9 := j
              let t'10 := (t'9 - 1)
              j := t'10
              pure ()
            first'8 := false
            if !(j != (0 : UInt8)) then break
            let t'11 ← AP.can
            let t'12 ← AP_CANManager.get_driver_type t'11 i
            let t'13 ← AP.can
            let t'14 ← AP_CANManager.get_driver_type t'13 (Int8.toUInt8 (Int32.toInt8 (((UInt32.toInt32 (UInt8.toUInt32 (j))) - (1 : Int32)))))
            if (t'12 == t'14) then
              AP_Arming.check_failed this (8192 : Int32) report (0x1a68f : UInt64) /- "Same rfnd on different CAN ports" -/ (fp + 112)
              return false
          break
        else if sw'7 == (1 : UInt8) then
          break
          let mut j'2 : UInt8 := i
          let mut first'15 := true
          for _ in PMem.loopFuel do
            if !first'15 then
              let t'16 := j'2
              let t'17 := (t'16 - 1)
              j'2 := t'17
              pure ()
            first'15 := false
            if !(j'2 != (0 : UInt8)) then break
            let t'18 ← AP.can
            let t'19 ← AP_CANManager.get_driver_type t'18 i
            let t'20 ← AP.can
            let t'21 ← AP_CANManager.get_driver_type t'20 (Int8.toUInt8 (Int32.toInt8 (((UInt32.toInt32 (UInt8.toUInt32 (j'2))) - (1 : Int32)))))
            if (t'19 == t'21) then
              AP_Arming.check_failed this (8192 : Int32) report (0x1a68f : UInt64) /- "Same rfnd on different CAN ports" -/ (fp + 120)
              return false
          break
        else if sw'7 == (7 : UInt8) || sw'7 == (13 : UInt8) || sw'7 == (14 : UInt8) || sw'7 == (11 : UInt8) then
          let mut j'3 : UInt8 := i
          let mut first'22 := true
          for _ in PMem.loopFuel do
            if !first'22 then
              let t'23 := j'3
              let t'24 := (t'23 - 1)
              j'3 := t'24
              pure ()
            first'22 := false
            if !(j'3 != (0 : UInt8)) then break
            let t'25 ← AP.can
            let t'26 ← AP_CANManager.get_driver_type t'25 i
            let t'27 ← AP.can
            let t'28 ← AP_CANManager.get_driver_type t'27 (Int8.toUInt8 (Int32.toInt8 (((UInt32.toInt32 (UInt8.toUInt32 (j'3))) - (1 : Int32)))))
            if (t'26 == t'28) then
              AP_Arming.check_failed this (8192 : Int32) report (0x1a68f : UInt64) /- "Same rfnd on different CAN ports" -/ (fp + 128)
              return false
          break
        else if sw'7 == (6 : UInt8) || sw'7 == (0 : UInt8) || sw'7 == (10 : UInt8) || sw'7 == (12 : UInt8) || sw'7 == (8 : UInt8) then
          pure ()
        else
          pure ()
  return true

def AP_Arming.can_checks (this : UInt64) (report : Bool) : PMem.M Bool := do
  let fp ← PMem.enter 136
  let r ← AP_Arming.can_checks.body fp this report
  PMem.leave fp
  return r

/-- C++ `AP_Arming::estop_checks : bool (bool)`, `AP_Arming.cpp:1685-1704`. -/
def AP_Arming.estop_checks.body (fp : UInt64) (this : UInt64) (display_failure : Bool) : PMem.M Bool := do
  let mut display_failure := display_failure
  let t'1 ← SRV_Channels.get_emergency_stop
  if !t'1 then
    return true
  let t'2 ← rc
  let t'3 ← RC_Channels.find_channel_for_option t'2 (165 : Int32)
  let mut chan : UInt64 := t'3
  if (chan != (0 : UInt64)) then
    let t'4 ← RC_Channel.get_aux_switch_pos chan
    if (t'4 == (0 : UInt8)) then
      return true
  AP_Arming.check_failed'2 this display_failure (0x1a6de : UInt64) /- "Motors Emergency Stopped" -/ (fp + 0)
  return false

def AP_Arming.estop_checks (this : UInt64) (display_failure : Bool) : PMem.M Bool := do
  let fp ← PMem.enter 8
  let r ← AP_Arming.estop_checks.body fp this display_failure
  PMem.leave fp
  return r

/-- C++ `AP_Arming::rc_arm_checks : bool (AP_Arming::Method)`, `AP_Arming.cpp:818-874`. -/
def AP_Arming.rc_arm_checks.body (fp : UInt64) (this : UInt64) (method : Int32) : PMem.M Bool := do
  let mut method := method
  let t'1 ← rc
  let t'2 ← RC_Channels_Copter.has_valid_input t'1
  if !t'2 then
    return true
  let t'3 ← rc
  let t'4 ← RC_Channels.last_input_ms t'3
  let mut last_input_ms : UInt32 := t'4
  if ((last_input_ms == (Int32.toUInt32 ((0 : Int32)))) || (decide (((((← PMem.clock) / 1000).toUInt32) - last_input_ms) > (Int32.toUInt32 ((1000 : Int32)))))) then
    return true
  let t'5 ← AP_Arming.rc_option_checks this true
  let mut check_passed : Bool := t'5
  let t'6 ← rc
  let t'7 ← RC_Channels.option_is_enabled t'6 (64 : Int32)
  if !t'7 then
    PMem.stU64 (((fp + 0) + 0) + 0) (0x1a399 : UInt64) /- "Roll" -/
    let t'8 ← rc
    let t'9 ← RC_Channels.get_roll_channel t'8
    PMem.stU64 (((fp + 0) + 0) + 8) t'9
    PMem.stU64 (((fp + 0) + 16) + 0) (0x1a39e : UInt64) /- "Pitch" -/
    let t'10 ← rc
    let t'11 ← RC_Channels.get_pitch_channel t'10
    PMem.stU64 (((fp + 0) + 16) + 8) t'11
    PMem.stU64 (((fp + 0) + 32) + 0) (0x163e3 : UInt64) /- "Yaw" -/
    let t'12 ← rc
    let t'13 ← RC_Channels.get_yaw_channel t'12
    PMem.stU64 (((fp + 0) + 32) + 8) t'13
    let __range2 : UInt64 := (fp + 0)
    let mut __begin2 : UInt64 := __range2
    let mut __end2 : UInt64 := (__range2 + ((3 : Int64) * 16).toUInt64)
    let mut first'14 := true
    for _ in PMem.loopFuel do
      if !first'14 then
        let t'15 := (__begin2 + 16)
        __begin2 := t'15
        pure ()
      first'14 := false
      if !((__begin2 != __end2)) then break
      let channel_to_check : UInt64 := __begin2
      let t'16 ← PMem.ldU64 (channel_to_check + 8)
      let mut c : UInt64 := t'16
      let t'17 ← RC_Channel.get_control_in c
      if ((Int16.toInt32 (t'17)) != (0 : Int32)) then
        let mut sc'20 := (method != (0 : Int32))
        if !sc'20 then
          let t'18 ← rc
          let t'19 ← RC_Channels_Copter.get_arming_channel t'18
          sc'20 := (c != t'19)
        if sc'20 then
          let t'21 ← PMem.ldU64 channel_to_check
          PMem.stU64 (fp + 48) t'21
          let t'22 ← RC_Channel.ch c
          PMem.stU64 (fp + 56) (Int64.toUInt64 (Int32.toInt64 ((UInt32.toInt32 (UInt8.toUInt32 (t'22))))))
          AP_Arming.check_failed this (64 : Int32) true (0x1a3a4 : UInt64) /- "%s (RC%d) is not neutral" -/ (fp + 48)
          check_passed := false
  let t'23 ← rc
  let t'24 ← RC_Channels_Copter.arming_check_throttle t'23
  if t'24 then
    let t'25 ← rc
    let t'26 ← RC_Channels.get_throttle_channel t'25
    let mut c'2 : UInt64 := t'26
    let t'27 ← RC_Channel.get_control_in c'2
    if ((Int16.toInt32 (t'27)) != (0 : Int32)) then
      PMem.stU64 (fp + 64) (0x139ab : UInt64) /- "Throttle" -/
      let t'28 ← RC_Channel.ch c'2
      PMem.stU64 (fp + 72) (Int64.toUInt64 (Int32.toInt64 ((UInt32.toInt32 (UInt8.toUInt32 (t'28))))))
      AP_Arming.check_failed this (64 : Int32) true (0x1a3a4 : UInt64) /- "%s (RC%d) is not neutral" -/ (fp + 64)
      check_passed := false
    let t'29 ← rc
    let t'30 ← RC_Channels.find_channel_for_option t'29 (209 : Int32)
    c'2 := t'30
    if (c'2 != (0 : UInt64)) then
      let t'31 ← RC_Channel.percent_input c'2
      let mut fwd_thr : UInt8 := t'31
      if (decide ((UInt32.toInt32 (UInt8.toUInt32 (fwd_thr))) > (2 : Int32))) then
        AP_Arming.check_failed this (64 : Int32) true (0x1a3bd : UInt64) /- "VTOL Fwd Throttle is not zero" -/ (fp + 80)
        check_passed := false
  return check_passed

def AP_Arming.rc_arm_checks (this : UInt64) (method : Int32) : PMem.M Bool := do
  let fp ← PMem.enter 88
  let r ← AP_Arming.rc_arm_checks.body fp this method
  PMem.leave fp
  return r

/-- C++ `AP_Arming::arm_checks : bool (AP_Arming::Method)`, `AP_Arming.cpp:1802-1847`. -/
def AP_Arming.arm_checks.body (fp : UInt64) (this : UInt64) (method : Int32) : PMem.M Bool := do
  let mut method := method
  let t'1 ← AP_Arming.check_enabled this (64 : Int32)
  if t'1 then
    let t'2 ← AP_Arming.rc_arm_checks this method
    if !t'2 then
      return false
  let t'3 ← SRV_Channels.get_emergency_stop
  if t'3 then
    AP_Arming.check_failed'2 this true (0x1a6de : UInt64) /- "Motors Emergency Stopped" -/ (fp + 0)
    return false
  let t'4 ← AP_Arming.check_enabled this (4096 : Int32)
  if t'4 then
    let t'5 ← VehicleBridge.gps'0
    let t'6 ← VehicleBridge.AP_GPS.prepare_for_arming'0 t'5
    if !t'6 then
      return false
  return true

def AP_Arming.arm_checks (this : UInt64) (method : Int32) : PMem.M Bool := do
  let fp ← PMem.enter 8
  let r ← AP_Arming.arm_checks.body fp this method
  PMem.leave fp
  return r

end Vehicle_lib
