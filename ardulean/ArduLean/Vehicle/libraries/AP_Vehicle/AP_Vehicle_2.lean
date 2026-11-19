import ArduLean.Runtime.Hal
import ArduLean.Vehicle.libraries.AP_Math.AP_Math
import ArduLean.Vehicle.libraries.StorageManager.StorageManager
import ArduLean.Vehicle.libraries.AP_Param.AP_Param
import ArduLean.Vehicle.libraries.AP_BoardConfig.AP_BoardConfig
import ArduLean.Vehicle.libraries.AP_Notify.AP_Notify
import ArduLean.Vehicle.libraries.AP_Common.AP_Common
import ArduLean.Vehicle.libraries.GCS_MAVLink.GCS_MAVLink
import ArduLean.Vehicle.libraries.AP_CANManager.AP_CANManager
import ArduLean.Vehicle.libraries.AP_Scheduler.AP_Scheduler
import ArduLean.Vehicle.libraries.AP_Param.AP_Param_2
import ArduLean.Vehicle.ArduCopter.ArduCopter_2
import ArduLean.Vehicle.libraries.AP_SerialManager.AP_SerialManager
import ArduLean.Vehicle.libraries.GCS_MAVLink.GCS_MAVLink_2

/-!
ArduPilot `libraries/AP_Vehicle`, part 2 of 2. Sources: `libraries/AP_Vehicle/AP_Vehicle.cpp`, `libraries/AP_Vehicle/AP_Vehicle.h`, `libraries/AP_Vehicle/Parameters.cpp`.

Items of `lean/Vehicle_lib.lean` (the vehicle translation), unchanged; placed by `tools/split_modules.py` (`ArduLean/Vehicle/INDEX.md`).
-/

open FloatLib.Floats (Binary32 Binary64)

set_option linter.unusedVariables false
set_option linter.unreachableTactic false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false

namespace Vehicle_lib

/-- C++ `AP_Vehicle::notify_no_such_mode : void (uint8_t)`, `AP_Vehicle.cpp:962-966`. -/
def AP_Vehicle.notify_no_such_mode.body (fp : UInt64) (this : UInt64) (mode_number : UInt8) : PMem.M Unit := do
  let mut mode_number := mode_number
  PMem.stU64 (fp + 0) (Int64.toUInt64 (Int32.toInt64 ((UInt32.toInt32 (UInt8.toUInt32 (mode_number))))))
  let t'1 ← gcs
  GCS.send_text t'1 (4 : UInt32) (0x18683 : UInt64) /- "No such mode %u" -/ (fp + 0)
  return ()

def AP_Vehicle.notify_no_such_mode (this : UInt64) (mode_number : UInt8) : PMem.M Unit := do
  let fp ← PMem.enter 8
  let r ← AP_Vehicle.notify_no_such_mode.body fp this mode_number
  PMem.leave fp
  return r

/-- C++ `AP_Vehicle::load_parameters : void (AP_Int16 &, const uint16_t)`, `Parameters.cpp:12-36`. -/
def AP_Vehicle.load_parameters.body (fp : UInt64) (this : UInt64) (format_version : UInt64) (expected_format_version : UInt16) : PMem.M Unit := do
  let mut expected_format_version := expected_format_version
  let t'1 ← AP_Param.load format_version
  let mut sc'4 := !t'1
  if !sc'4 then
    let t'2 ← AP_ParamT'short_2.operator_const_short__ format_version
    let t'3 ← PMem.ldI16 t'2
    sc'4 := ((Int16.toInt32 (t'3)) != (UInt32.toInt32 (UInt16.toUInt32 (expected_format_version))))
  if sc'4 then
    let t'5 ← PMem.ldU64 ((0xba88 : UInt64) /- &hal -/ + 48)
    discard <| PMem.halDev "AP_HAL::BetterStream::printf" t'5 #[(0x18506 : UInt64) /- "Firmware change: erasing EEPROM...\n" -/]
    StorageManager.erase
    PMem.unreached "AP_Param::erase_all"
    PMem.stI16 (fp + 0) (UInt16.toInt16 (expected_format_version))
    AP_ParamTBase'short_2.set_and_save format_version (fp + 0)
    let t'6 ← PMem.ldU64 ((0xba88 : UInt64) /- &hal -/ + 48)
    discard <| PMem.halDev "AP_HAL::BetterStream::printf" t'6 #[(0x1852a : UInt64) /- "done.\n" -/]
  PMem.stI16 (fp + 2) (UInt16.toInt16 (expected_format_version))
  AP_ParamTBase'short_2.set_default format_version (fp + 2)
  let t'7 ← AP_Param.load_all
  discard <| pure (t'7)
  let t'8 ← gcs
  GCS.convert_parameters t'8
  return ()

def AP_Vehicle.load_parameters (this : UInt64) (format_version : UInt64) (expected_format_version : UInt16) : PMem.M Unit := do
  let fp ← PMem.enter 4
  let r ← AP_Vehicle.load_parameters.body fp this format_version expected_format_version
  PMem.leave fp
  return r

/-- C++ `AP_Vehicle::send_watchdog_reset_statustext : void ()`, `AP_Vehicle.cpp:784-807`. -/
def AP_Vehicle.send_watchdog_reset_statustext.body (fp : UInt64) (this : UInt64) : PMem.M Unit := do
  let t'1 ← PMem.ldU64 ((0xba88 : UInt64) /- &hal -/ + 88)
  let t'2 ← PMem.halDev "AP_HAL::Util::was_watchdog_reset" t'1 #[]
  if !(t'2 != 0) then
    return ()
  let t'3 ← PMem.ldU64 ((0xba88 : UInt64) /- &hal -/ + 88)
  let pd : UInt64 := (t'3 + 84)
  discard <| pure (pd)
  let t'4 ← PMem.ldI8 (pd + 72)
  PMem.stU64 (fp + 0) (Int64.toUInt64 (Int32.toInt64 ((Int8.toInt32 (t'4)))))
  let t'5 ← PMem.ldU16 (pd + 62)
  PMem.stU64 (fp + 8) (Int64.toUInt64 (Int32.toInt64 ((UInt32.toInt32 (UInt16.toUInt32 (t'5))))))
  let t'6 ← PMem.ldU16 (pd + 64)
  PMem.stU64 (fp + 16) (Int64.toUInt64 (Int32.toInt64 ((UInt32.toInt32 (UInt16.toUInt32 (t'6))))))
  let t'7 ← PMem.ldU8 (pd + 66)
  PMem.stU64 (fp + 24) (Int64.toUInt64 (Int32.toInt64 ((UInt32.toInt32 (UInt8.toUInt32 (t'7))))))
  let t'8 ← PMem.ldU32 (pd + 24)
  PMem.stU64 (fp + 32) (UInt32.toUInt64 (t'8))
  let t'9 ← PMem.ldU8 (pd + 67)
  PMem.stU64 (fp + 40) (Int64.toUInt64 (Int32.toInt64 ((UInt32.toInt32 (UInt8.toUInt32 (t'9))))))
  let t'10 ← PMem.ldU32 (pd + 32)
  PMem.stU64 (fp + 48) (UInt32.toUInt64 (t'10))
  let t'11 ← PMem.ldU32 (pd + 28)
  PMem.stU64 (fp + 56) (UInt32.toUInt64 (t'11))
  let t'12 ← PMem.ldU16 (pd + 58)
  PMem.stU64 (fp + 64) (Int64.toUInt64 (Int32.toInt64 ((UInt32.toInt32 (UInt16.toUInt32 (t'12))))))
  let t'13 ← PMem.ldU16 (pd + 60)
  PMem.stU64 (fp + 72) (Int64.toUInt64 (Int32.toInt64 ((UInt32.toInt32 (UInt16.toUInt32 (t'13))))))
  let t'14 ← PMem.ldU32 (pd + 36)
  PMem.stU64 (fp + 80) (UInt32.toUInt64 (t'14))
  let t'15 ← PMem.ldU16 (pd + 40)
  PMem.stU64 (fp + 88) (UInt32.toUInt64 ((UInt16.toUInt32 (t'15))))
  PMem.stU64 (fp + 96) (pd + 68)
  let t'16 ← gcs
  GCS.send_text t'16 (2 : UInt32) (0x18635 : UInt64) /- "WDG: T%d SL%u FL%u FT%u FA%x FTP%u FLR%x FICSR%u MM%u MC%u IE%u IEC%u TN:%.4s" -/ (fp + 0)
  return ()

def AP_Vehicle.send_watchdog_reset_statustext (this : UInt64) : PMem.M Unit := do
  let fp ← PMem.enter 104
  let r ← AP_Vehicle.send_watchdog_reset_statustext.body fp this
  PMem.leave fp
  return r

/-- C++ `AP_Vehicle::one_Hz_update : void ()`, `AP_Vehicle.cpp:1091-1141`. -/
def AP_Vehicle.one_Hz_update (this : UInt64) : PMem.M Unit := do
  let t'1 := (this + 6760)
  let t'2 ← PMem.ldU8 t'1
  let t'3 := (t'2 + 1)
  PMem.stU8 t'1 t'3
  let t'4 ← PMem.ldU8 (this + 6760)
  if (((UInt8.toUInt32 (t'4)) % (10 : UInt32)) == (Int32.toUInt32 ((0 : Int32)))) then
    pure ()
  let t'5 ← PMem.ldU8 (this + 6760)
  if (((UInt8.toUInt32 (t'5)) % (30 : UInt32)) == (Int32.toUInt32 ((0 : Int32)))) then
    pure ()
  let t'6 ← Copter.get_available_mode_enabled_mask this
  let mut available_mode_enabled_mask : UInt32 := t'6
  let t'7 ← PMem.ldU32 (this + 6752)
  if (available_mode_enabled_mask != t'7) then
    let t'8 ← PMem.ldU32 (this + 6752)
    if (t'8 != (Int32.toUInt32 ((0 : Int32)))) then
      let t'9 ← gcs
      GCS.available_modes_changed t'9
    PMem.stU32 (this + 6752) available_mode_enabled_mask
  return ()

/-- C++ `AP_Vehicle::AP_Vehicle : void ()`, `AP_Vehicle.h:102-108`. -/
def AP_Vehicle.AP_Vehicle (this : UInt64) : PMem.M Unit := do
  AP_HAL.HAL.Callbacks.Callbacks this
  AP_BoardConfig.AP_BoardConfig (this + 8)
  AP_CANManager.AP_CANManager (this + 96)
  AP_Scheduler.AP_Scheduler (this + 208)
  -- gps: constructed by the estimator World
  -- barometer: constructed by the estimator World
  -- compass: constructed by the estimator World
  -- ins: constructed by the estimator World
  AP_SerialManager.AP_SerialManager (this + 3848)
  AP_Notify.AP_Notify (this + 3992)
  -- ahrs: constructed by the estimator World
  PMem.stU8 (this + 6352) (0 : UInt8)
  Location.Location ((this + 6360) + 16)
  QuaternionT'float.QuaternionT ((this + 6360) + 160)
  Vector3'float.Vector3'2 ((this + 6360) + 184)
  Vector3'float.Vector3'2 ((this + 6360) + 220)
  AP_Param.AP_Param'2 ((this + 6360) + 244)
  AP_Param.AP_Param'2 ((this + 6360) + 245)
  AP_Param.AP_Param'2 ((this + 6360) + 248)
  AP_Param.AP_Param'2 ((this + 6360) + 252)
  AP_Param.AP_Param'2 ((this + 6360) + 254)
  AP_Param.AP_Param'2 ((this + 6360) + 256)
  AP_Param.AP_Param'2 ((this + 6360) + 257)
  AP_Param.AP_Param'2 ((this + 6360) + 258)
  AP_Param.AP_Param'2 ((this + 6360) + 259)
  AP_Param.AP_Param'2 ((this + 6360) + 260)
  AP_Param.AP_Param'2 ((this + 6360) + 264)
  AP_Param.AP_Param'2 ((this + 6360) + 268)
  AP_Param.AP_Param'2 ((this + 6360) + 272)
  AP_Param.AP_Param'2 ((this + 6360) + 276)
  AP_Param.AP_Param'2 ((this + 6360) + 280)
  AP_Param.AP_Param'2 ((this + 6360) + 284)
  AP_Param.AP_Param'2 ((this + 6360) + 288)
  AP_Param.AP_Param'2 ((this + 6360) + 292)
  AP_Param.AP_Param'2 ((this + 6360) + 296)
  Vector3'float.Vector3'2 ((this + 6360) + 296)
  AP_Param.AP_Param'2 ((this + 6360) + 308)
  Vector3'float.Vector3'2 ((this + 6360) + 308)
  AP_Param.AP_Param'2 ((this + 6360) + 320)
  Vector3'float.Vector3'2 ((this + 6360) + 320)
  AP_Param.AP_Param'2 ((this + 6360) + 344)
  Vector3'float.Vector3'2 ((this + 6360) + 344)
  AP_Param.AP_Param'2 ((this + 6360) + 356)
  Vector3'float.Vector3'2 ((this + 6360) + 356)
  AP_Param.AP_Param'2 ((this + 6360) + 368)
  Vector3'float.Vector3'2 ((this + 6360) + 368)
  AP_Param.AP_Param'2 ((this + 6360) + 380)
  AP_Param.AP_Param'2 (((this + 6360) + 380) + 4)
  AP_Param.AP_Param'2 (((this + 6360) + 380) + 8)
  AP_Param.AP_Param'2 (this + 6756)
  let t'1 ← PMem.ldU64 (0xdf18 : UInt64) /- &AP_Vehicle::_singleton -/
  if (t'1 != 0) then
    pure ()
  AP_Param.setup_object_defaults this (0x5720 : UInt64) /- &AP_Vehicle::var_info -/
  PMem.stU64 (0xdf18 : UInt64) /- &AP_Vehicle::_singleton -/ this
  return ()

end Vehicle_lib
