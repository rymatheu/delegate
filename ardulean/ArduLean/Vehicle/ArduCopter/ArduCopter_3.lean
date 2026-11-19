import ArduLean.Runtime.Bridge
import ArduLean.Vehicle.libraries.AP_NavEKF.AP_NavEKF
import ArduLean.Vehicle.libraries.AP_Math.AP_Math
import ArduLean.Vehicle.libraries.AP_HAL.AP_HAL
import ArduLean.Vehicle.libraries.Filter.Filter
import ArduLean.Vehicle.libraries.AP_Param.AP_Param
import ArduLean.Vehicle.libraries.AC_PID.AC_PID
import ArduLean.Vehicle.libraries.AC_AttitudeControl.AC_AttitudeControl
import ArduLean.Vehicle.libraries.AC_WPNav.AC_WPNav
import ArduLean.Vehicle.libraries.AP_SurfaceDistance.AP_SurfaceDistance
import ArduLean.Vehicle.libraries.AP_Mission.AP_Mission
import ArduLean.Vehicle.libraries.AP_BoardConfig.AP_BoardConfig
import ArduLean.Vehicle.libraries.RC_Channel.RC_Channel
import ArduLean.Vehicle.libraries.AP_Arming.AP_Arming
import ArduLean.Vehicle.ArduCopter.ArduCopter
import ArduLean.Vehicle.Dispatch
import ArduLean.Vehicle.libraries.AP_Motors.AP_Motors
import ArduLean.Vehicle.libraries.AP_Common.AP_Common
import ArduLean.Vehicle.libraries.AP_BattMonitor.AP_BattMonitor
import ArduLean.Vehicle.libraries.AP_Vehicle.AP_Vehicle
import ArduLean.Vehicle.mavlink.mavlink
import ArduLean.Vehicle.libraries.AP_RCMapper.AP_RCMapper
import ArduLean.Vehicle.libraries.AP_Scheduler.AP_Scheduler
import ArduLean.Vehicle.libraries.SRV_Channel.SRV_Channel
import ArduLean.Vehicle.libraries.AP_Math.AP_Math_2
import ArduLean.Vehicle.libraries.Filter.Filter_2
import ArduLean.Vehicle.libraries.AP_Param.AP_Param_2
import ArduLean.Vehicle.libraries.AC_AttitudeControl.AC_AttitudeControl_2
import ArduLean.Vehicle.libraries.AC_WPNav.AC_WPNav_2
import ArduLean.Vehicle.libraries.AP_Mission.AP_Mission_2
import ArduLean.Vehicle.libraries.RC_Channel.RC_Channel_2
import ArduLean.Vehicle.ArduCopter.ArduCopter_2
import ArduLean.Vehicle.Dispatch_2
import ArduLean.Vehicle.libraries.AP_Motors.AP_Motors_2
import ArduLean.Vehicle.libraries.GCS_MAVLink.GCS_MAVLink_2
import ArduLean.Vehicle.libraries.AP_Vehicle.AP_Vehicle_2
import ArduLean.Vehicle.libraries.AP_Mission.AP_Mission_3
import ArduLean.Vehicle.World
import ArduLean.Vehicle.libraries.AP_BoardConfig.AP_BoardConfig_2
import ArduLean.Vehicle.libraries.AP_Arming.AP_Arming_3

/-!
ArduPilot `ArduCopter`, part 3 of 3. Sources: `ArduCopter/AP_Arming_Copter.cpp`, `ArduCopter/mode_auto.cpp`, `ArduCopter/crash_check.cpp`, `ArduCopter/GCS_MAVLink_Copter.cpp`, `ArduCopter/mode_rtl.cpp`, `ArduCopter/mode.cpp`, `ArduCopter/events.cpp`, `ArduCopter/land_detector.cpp` and 21 more.

Items of `lean/Vehicle_lib.lean` (the vehicle translation), unchanged; placed by `tools/split_modules.py` (`ArduLean/Vehicle/INDEX.md`).
-/

open FloatLib.Floats (Binary32 Binary64)

set_option linter.unusedVariables false
set_option linter.unreachableTactic false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false

namespace Vehicle_lib

/-- C++ `GCS_MAVLINK_Copter::handle_message_set_position_target_global_int : void (const mavlink_message_t &)`, `GCS_MAVLink_Copter.cpp:1079-1176`. -/
def GCS_MAVLINK_Copter.handle_message_set_position_target_global_int.body (fp : UInt64) (this : UInt64) (msg : UInt64) : PMem.M Unit := do
  __mavlink_set_position_target_global_int_t.__mavlink_set_position_target_global_int_t (fp + 0)
  mavlink_msg_set_position_target_global_int_decode msg (fp + 0)
  let t'1 ← PMem.ldU64 ((0x86d8 : UInt64) /- &copter -/ + 9488)
  let t'2 ← vcall'Mode'in_guided_mode'11 t'1
  if !t'2 then
    return ()
  let t'3 ← PMem.ldU16 ((fp + 0) + 48)
  let mut pos_ignore : Bool := ((UInt16.toUInt32 (t'3)) &&& (7 : UInt32)) != (0 : UInt32)
  let t'4 ← PMem.ldU16 ((fp + 0) + 48)
  let mut vel_ignore : Bool := ((UInt16.toUInt32 (t'4)) &&& (56 : UInt32)) != (0 : UInt32)
  let t'5 ← PMem.ldU16 ((fp + 0) + 48)
  let mut acc_ignore : Bool := ((UInt16.toUInt32 (t'5)) &&& (448 : UInt32)) != (0 : UInt32)
  let t'6 ← PMem.ldU16 ((fp + 0) + 48)
  let mut yaw_ignore : Bool := ((UInt16.toUInt32 (t'6)) &&& (1024 : UInt32)) != (0 : UInt32)
  let t'7 ← PMem.ldU16 ((fp + 0) + 48)
  let mut yaw_rate_ignore : Bool := ((UInt16.toUInt32 (t'7)) &&& (2048 : UInt32)) != (0 : UInt32)
  let t'8 ← PMem.ldU16 ((fp + 0) + 48)
  let mut force_set : Bool := ((UInt16.toUInt32 (t'8)) &&& (512 : UInt32)) != (0 : UInt32)
  if (force_set && (!acc_ignore)) then
    ModeGuided.hold_position ((0x86d8 : UInt64) /- &copter -/ + 12520)
    return ()
  Location.Location (fp + 56)
  if !pos_ignore then
    let t'9 ← PMem.ldI32 ((fp + 0) + 4)
    let t'10 ← PMem.ldI32 ((fp + 0) + 8)
    let t'11 ← check_latlng t'9 t'10
    if !t'11 then
      ModeGuided.hold_position ((0x86d8 : UInt64) /- &copter -/ + 12520)
      return ()
    let t'12 ← PMem.ldU8 ((fp + 0) + 52)
    let t'13 ← GCS_MAVLINK.mavlink_coordinate_frame_to_location_alt_frame this (UInt8.toUInt32 (t'12)) (fp + 72)
    if !t'13 then
      ModeGuided.hold_position ((0x86d8 : UInt64) /- &copter -/ + 12520)
      return ()
    let t'14 ← PMem.ldI32 ((fp + 0) + 4)
    let t'15 ← PMem.ldI32 ((fp + 0) + 8)
    let t'16 ← PMem.ldF32 ((fp + 0) + 12)
    let t'17 ← PMem.ldI32 (fp + 72)
    Location.Location'3 (fp + 80) t'14 t'15 (Binary32.toInt32 ((t'16 * (Int32.toBinary32 ((100 : Int32)))))) t'17
    discard <| PMem.memcpy (fp + 56) (fp + 80) 16
    discard <| pure ((fp + 56))
  Vector3'float.Vector3'2 (fp + 96)
  if !vel_ignore then
    let t'18 ← PMem.ldF32 ((fp + 0) + 16)
    let t'19 ← PMem.ldF32 ((fp + 0) + 20)
    let t'20 ← PMem.ldF32 ((fp + 0) + 24)
    Vector3'float.Vector3 (fp + 112) t'18 t'19 t'20
    discard <| PMem.memcpy (fp + 96) (fp + 112) 12
    discard <| pure ((fp + 96))
    let t'21 ← GCS_MAVLINK_Copter.sane_vel_or_acc_vector this (fp + 96)
    if !t'21 then
      ModeGuided.hold_position ((0x86d8 : UInt64) /- &copter -/ + 12520)
      return ()
  Vector3'float.Vector3'2 (fp + 128)
  if !acc_ignore then
    let t'22 ← PMem.ldF32 ((fp + 0) + 28)
    let t'23 ← PMem.ldF32 ((fp + 0) + 32)
    let t'24 ← PMem.ldF32 ((fp + 0) + 36)
    Vector3'float.Vector3 (fp + 144) t'22 t'23 t'24
    discard <| PMem.memcpy (fp + 128) (fp + 144) 12
    discard <| pure ((fp + 128))
  let mut yaw_rad : Binary32 := (Binary32.ofBits 0x00000000 /- 0 -/)
  let mut yaw_rate_rads : Binary32 := (Binary32.ofBits 0x00000000 /- 0 -/)
  if !yaw_ignore then
    let t'25 ← PMem.ldF32 ((fp + 0) + 40)
    yaw_rad := t'25
  if !yaw_rate_ignore then
    let t'26 ← PMem.ldF32 ((fp + 0) + 44)
    yaw_rate_rads := t'26
  if ((!pos_ignore) && (!vel_ignore)) then
    let t'27 ← Location.get_alt_frame (fp + 56)
    if (t'27 == (3 : Int32)) then
      ModeGuided.hold_position ((0x86d8 : UInt64) /- &copter -/ + 12520)
      return ()
    Vector3'double.Vector3 (fp + 160)
    let t'28 ← Location.get_vector_from_origin_NED_m'Vector3_double (fp + 56) (fp + 160)
    if !t'28 then
      ModeGuided.hold_position ((0x86d8 : UInt64) /- &copter -/ + 12520)
      return ()
    let t'29 ← ModeGuided.set_pos_vel_NED_m ((0x86d8 : UInt64) /- &copter -/ + 12520) (fp + 160) (fp + 96) (!yaw_ignore) yaw_rad (!yaw_rate_ignore) yaw_rate_rads false
    discard <| pure (t'29)
  else
    if (pos_ignore && (!vel_ignore)) then
      ModeGuided.set_vel_accel_NED_m ((0x86d8 : UInt64) /- &copter -/ + 12520) (fp + 96) (fp + 128) (!yaw_ignore) yaw_rad (!yaw_rate_ignore) yaw_rate_rads false true
    else
      if ((pos_ignore && vel_ignore) && (!acc_ignore)) then
        ModeGuided.set_accel_NED_mss ((0x86d8 : UInt64) /- &copter -/ + 12520) (fp + 128) (!yaw_ignore) yaw_rad (!yaw_rate_ignore) yaw_rate_rads false true
      else
        if (((!pos_ignore) && vel_ignore) && acc_ignore) then
          let t'30 ← ModeGuided.set_destination ((0x86d8 : UInt64) /- &copter -/ + 12520) (fp + 56) (!yaw_ignore) yaw_rad (!yaw_rate_ignore) yaw_rate_rads false
          discard <| pure (t'30)
        else
          ModeGuided.hold_position ((0x86d8 : UInt64) /- &copter -/ + 12520)
  return ()

def GCS_MAVLINK_Copter.handle_message_set_position_target_global_int (this : UInt64) (msg : UInt64) : PMem.M Unit := do
  let fp ← PMem.enter 184
  let r ← GCS_MAVLINK_Copter.handle_message_set_position_target_global_int.body fp this msg
  PMem.leave fp
  return r

/-- C++ `Copter::mode_change_failed : void (const Mode *, const char *)`, `mode.cpp:175-183`. -/
def Copter.mode_change_failed.body (fp : UInt64) (this : UInt64) (mode : UInt64) (reason : UInt64) : PMem.M Unit := do
  let mut mode := mode
  let mut reason := reason
  let t'1 ← vcall'Mode'name'8 mode
  PMem.stU64 (fp + 0) t'1
  PMem.stU64 (fp + 8) reason
  let t'2 ← Copter.gcs this
  GCS.send_text t'2 (4 : UInt32) (0x14874 : UInt64) /- "Mode change to %s failed: %s" -/ (fp + 0)
  let t'3 ← PMem.ldB (((0x86d8 : UInt64) /- &copter -/ + 9448) + 13)
  if t'3 then
    let t'4 := Int32.toUInt32 ((1 : Int32))
    PMem.stBits (0xce38 : UInt64) /- &AP_Notify::events -/ 2 1 (UInt32.toUInt64 (t'4))
  return ()

def Copter.mode_change_failed (this : UInt64) (mode : UInt64) (reason : UInt64) : PMem.M Unit := do
  let fp ← PMem.enter 16
  let r ← Copter.mode_change_failed.body fp this mode reason
  PMem.leave fp
  return r

/-- C++ `Copter::set_simple_mode : void (SimpleMode)`, `AP_State.cpp:22-43`. -/
def Copter.set_simple_mode.body (fp : UInt64) (this : UInt64) (b : Int32) : PMem.M Unit := do
  let mut b := b
  let t'1 ← PMem.ldI32 (this + 9552)
  if (t'1 != b) then
    let sw'2 := b
    if sw'2 == (0 : Int32) then
      let t'3 ← Copter.gcs this
      GCS.send_text t'3 (6 : UInt32) (0x13bf0 : UInt64) /- "SIMPLE mode off" -/ (fp + 0)
    else if sw'2 == (1 : Int32) then
      let t'4 ← Copter.gcs this
      GCS.send_text t'4 (6 : UInt32) (0x13c00 : UInt64) /- "SIMPLE mode on" -/ (fp + 8)
    else if sw'2 == (2 : Int32) then
      Copter.update_super_simple_bearing this true
      let t'5 ← Copter.gcs this
      GCS.send_text t'5 (6 : UInt32) (0x13c0f : UInt64) /- "SUPERSIMPLE mode on" -/ (fp + 16)
    else
      pure ()
    PMem.stI32 (this + 9552) b
  return ()

def Copter.set_simple_mode (this : UInt64) (b : Int32) : PMem.M Unit := do
  let fp ← PMem.enter 24
  let r ← Copter.set_simple_mode.body fp this b
  PMem.leave fp
  return r

/-- C++ `Copter::AHRSTrimming::save_trim : void ()`, `RC_Channel_Copter.cpp:734-756`. -/
def Copter.AHRSTrimming.save_trim.body (fp : UInt64) (this : UInt64) : PMem.M Unit := do
  PMem.stF32 (fp + 0) (Binary64.toBinary32 ((Binary64.ofBits 0x0000000000000000 /- 0 -/)))
  PMem.stF32 (fp + 8) (Binary64.toBinary32 ((Binary64.ofBits 0x0000000000000000 /- 0 -/)))
  let t'1 ← PMem.ldU64 ((0x86d8 : UInt64) /- &copter -/ + 11168)
  let t'2 ← AC_AttitudeControl.lean_angle_max_rad t'1
  let t'3 ← PMem.ldU64 ((0x86d8 : UInt64) /- &copter -/ + 11168)
  let t'4 ← AC_AttitudeControl.get_althold_lean_angle_max_rad t'3
  let t'5 ← PMem.ldU64 ((0x86d8 : UInt64) /- &copter -/ + 9488)
  Mode.get_pilot_desired_lean_angles_rad t'5 (fp + 0) (fp + 8) t'2 t'4
  let t'6 ← PMem.ldF32 (fp + 0)
  let t'7 ← PMem.ldF32 (fp + 8)
  let t'8 ← VehicleBridge.ahrs'0
  VehicleBridge.AP_AHRS.add_trim'3 t'8 t'6 t'7 true
  worldOutputs'drain
  let t'9 ← Copter.gcs (0x86d8 : UInt64) /- &copter -/
  GCS.send_text t'9 (6 : UInt32) (0x14448 : UInt64) /- "Trim saved" -/ (fp + 16)
  return ()

def Copter.AHRSTrimming.save_trim (this : UInt64) : PMem.M Unit := do
  let fp ← PMem.enter 24
  let r ← Copter.AHRSTrimming.save_trim.body fp this
  PMem.leave fp
  return r

mutual

/-- C++ `Copter::set_land_complete : void (bool)`, `land_detector.cpp:207-263`. -/
def Copter.set_land_complete'rec (rec'depth : Nat) (this : UInt64) (b : Bool) : PMem.M Unit := do
  let rec'd + 1 := rec'depth | PMem.depthOut
  let mut b := b
  let t'1 ← PMem.ldB ((this + 9448) + 7)
  if ((if t'1 then (1 : Int32) else (0 : Int32)) == (if b then (1 : Int32) else (0 : Int32))) then
    return ()
  let t'2 := Int32.toUInt32 ((0 : Int32))
  PMem.stU32 (0xce20 : UInt64) /- &land_detector_count -/ t'2
  PMem.stB ((this + 9448) + 7) b
  AP_Vehicle.set_likely_flying this (!b)
  if !b then
    return ()
  let t'3 ← AP_ParamT'unsigned_short_2.operator_const_unsigned_short__ ((this + 6776) + 8)
  let t'4 ← PMem.ldU16 t'3
  if (((UInt32.toInt32 (UInt16.toUInt32 (t'4))) &&& ((1 : Int32) <<< (2 : Int32))) == (0 : Int32)) then
    return ()
  let t'5 ← PMem.ldU64 (this + 9528)
  let t'6 ← AP_Motors.armed t'5
  if !t'6 then
    return ()
  let t'7 ← PMem.ldU64 (this + 9488)
  let t'8 ← vcall'Mode'has_manual_throttle'3 t'7
  if t'8 then
    return ()
  let t'9 ← PMem.ldU64 (this + 9488)
  let t'10 ← vcall'Mode'allows_arming'4 t'9 (32 : Int32)
  if !t'10 then
    return ()
  let t'11 ← AP_Arming_Copter.disarm'rec rec'd (this + 8768) (13 : Int32) true
  discard <| pure (t'11)
  return ()

/-- C++ `AP_Arming_Copter::disarm : bool (const AP_Arming::Method, bool)`, `AP_Arming_Copter.cpp:789-843`. -/
def AP_Arming_Copter.disarm'rec (rec'depth : Nat) (this : UInt64) (method : Int32) (do_disarm_checks : Bool) : PMem.M Bool := do
  let rec'd + 1 := rec'depth | PMem.depthOut
  let mut method := method
  let mut do_disarm_checks := do_disarm_checks
  let t'1 ← PMem.ldU64 ((0x86d8 : UInt64) /- &copter -/ + 9528)
  let t'2 ← AP_Motors.armed t'1
  if !t'2 then
    return true
  let mut sc'4 := do_disarm_checks
  if sc'4 then
    let t'3 ← AP_Arming.method_is_GCS method
    sc'4 := t'3
  let mut sc'6 := sc'4
  if sc'6 then
    let t'5 ← PMem.ldB (((0x86d8 : UInt64) /- &copter -/ + 9448) + 7)
    sc'6 := !t'5
  if sc'6 then
    return false
  if (method == (0 : Int32)) then
    let t'7 ← PMem.ldU64 ((0x86d8 : UInt64) /- &copter -/ + 9488)
    let t'8 ← vcall'Mode'has_manual_throttle'3 t'7
    let mut sc'10 := !t'8
    if sc'10 then
      let t'9 ← PMem.ldB (((0x86d8 : UInt64) /- &copter -/ + 9448) + 7)
      sc'10 := !t'9
    if sc'10 then
      return false
  let t'11 ← AP_Arming.disarm this method do_disarm_checks
  if !t'11 then
    return false
  AP_Arming.send_arm_disarm_statustext this (0x13bdf : UInt64) /- "Disarming motors" -/
  Copter.set_land_complete'rec rec'd (0x86d8 : UInt64) /- &copter -/ true
  Copter.set_land_complete_maybe (0x86d8 : UInt64) /- &copter -/ true
  let t'12 ← PMem.ldU64 ((0x86d8 : UInt64) /- &copter -/ + 9528)
  AP_Motors.armed'2 t'12 false
  AP_Mission.reset (((0x86d8 : UInt64) /- &copter -/ + 11368) + 112)
  let t'13 ← PMem.ldU64 ((0xba88 : UInt64) /- &hal -/ + 88)
  discard <| PMem.halDev "AP_HAL::Util::set_soft_armed" t'13 #[(if false then (1 : UInt64) else 0)]
  PMem.stB (((0x86d8 : UInt64) /- &copter -/ + 9448) + 21) false
  return true

end

/-- `Copter.set_land_complete'rec` with the depth of its recursive component (64). -/
def Copter.set_land_complete (this : UInt64) (b : Bool) : PMem.M Unit :=
  Copter.set_land_complete'rec 64 this b

/-- `AP_Arming_Copter.disarm'rec` with the depth of its recursive component (64). -/
def AP_Arming_Copter.disarm (this : UInt64) (method : Int32) (do_disarm_checks : Bool) : PMem.M Bool :=
  AP_Arming_Copter.disarm'rec 64 this method do_disarm_checks

/-- C++ `AP_Arming_Copter::mandatory_position_checks : bool (bool)`, `AP_Arming_Copter.cpp:444-516`. -/
def AP_Arming_Copter.mandatory_position_checks.body (fp : UInt64) (this : UInt64) (display_failure : Bool) : PMem.M Bool := do
  let mut display_failure := display_failure
  let t'1 ← PMem.ldU64 ((0x86d8 : UInt64) /- &copter -/ + 9488)
  let t'2 ← vcall'Mode'requires_position'5 t'1
  let mut mode_requires_position : Bool := t'2
  let t'3 ← VehicleBridge.ahrs'0
  let ahrs : UInt64 := t'3
  let t'4 ← VehicleBridge.AP_AHRS.pre_arm_check'3 ahrs mode_requires_position (fp + 0) (UInt64.toUInt8 ((100 : UInt64)))
  worldOutputs'drain
  if !t'4 then
    PMem.stU64 (fp + 104) (fp + 0)
    AP_Arming.check_failed'2 this display_failure (0x13af2 : UInt64) /- "AHRS: %s" -/ (fp + 104)
    return false
  let mut fence_requires_position : Bool := false
  let mut sc'6 := mode_requires_position
  if !sc'6 then
    let t'5 ← AP_Enum'AP_Arming_RequireLocation.operator_const_AP_Arming.RequireLocation (this + 34)
    sc'6 := (t'5 == (1 : UInt8))
  if sc'6 then
    let t'7 ← Copter.position_ok (0x86d8 : UInt64) /- &copter -/
    if !t'7 then
      AP_Arming.check_failed'2 this display_failure (0x13afb : UInt64) /- "Need Position Estimate" -/ (fp + 112)
      return false
  else
    if fence_requires_position then
      let t'8 ← Copter.position_ok (0x86d8 : UInt64) /- &copter -/
      if !t'8 then
        AP_Arming.check_failed'2 this display_failure (0x1b050 : UInt64) /- "Fence enabled, need position estimate" -/ (fp + 120)
        return false
    else
      return true
  nav_filter_status.nav_filter_status (fp + 128)
  let t'9 ← VehicleBridge.AP_AHRS.get_filter_status_for_configured_backend'1 ahrs (fp + 128)
  if t'9 then
    let t'10 ← PMem.ldBits (fp + 128) 14 1
    if (t'10 != 0) then
      AP_Arming.check_failed'2 this display_failure (0x13b12 : UInt64) /- "GPS glitching" -/ (fp + 136)
      return false
  let t'11 ← AP_ParamT'float_4.operator_const_float__'1 (((0x86d8 : UInt64) /- &copter -/ + 6776) + 56)
  let t'12 ← PMem.ldF32 t'11
  if (decide (t'12 > (Binary32.ofBits 0x00000000 /- 0 -/))) then
    Vector3'float.Vector3'2 (fp + 176)
    let t'13 ← VehicleBridge.AP_AHRS.get_variances_for_configured_backend'5 ahrs (fp + 144) (fp + 152) (fp + 160) (fp + 176) (fp + 168)
    discard <| pure (t'13)
    PMem.stU64 (((fp + 192) + 0) + 0) (0x13b20 : UInt64) /- "compass" -/
    let t'14 ← Vector3'float.length (fp + 176)
    PMem.stF32 (((fp + 192) + 0) + 8) t'14
    PMem.stU64 (((fp + 192) + 16) + 0) (0x13b28 : UInt64) /- "position" -/
    let t'15 ← PMem.ldF32 (fp + 152)
    PMem.stF32 (((fp + 192) + 16) + 8) t'15
    PMem.stU64 (((fp + 192) + 32) + 0) (0x13b31 : UInt64) /- "velocity" -/
    let t'16 ← PMem.ldF32 (fp + 144)
    PMem.stF32 (((fp + 192) + 32) + 8) t'16
    PMem.stU64 (((fp + 192) + 48) + 0) (0x13b3a : UInt64) /- "height" -/
    let t'17 ← PMem.ldF32 (fp + 160)
    PMem.stF32 (((fp + 192) + 48) + 8) t'17
    let __range2 : UInt64 := (fp + 192)
    let mut __begin2 : UInt64 := __range2
    let mut __end2 : UInt64 := (__range2 + ((4 : Int64) * 16).toUInt64)
    let mut first'18 := true
    for _ in PMem.loopFuel do
      if !first'18 then
        let t'19 := (__begin2 + 16)
        __begin2 := t'19
        pure ()
      first'18 := false
      if !((__begin2 != __end2)) then break
      let variance : UInt64 := __begin2
      let t'20 ← PMem.ldF32 (variance + 8)
      let t'21 ← AP_ParamT'float_4.operator_const_float__'1 (((0x86d8 : UInt64) /- &copter -/ + 6776) + 56)
      let t'22 ← PMem.ldF32 t'21
      if (decide (t'20 < t'22)) then
        continue
      let t'23 ← PMem.ldU64 variance
      PMem.stU64 (fp + 256) t'23
      AP_Arming.check_failed'2 this display_failure (0x13b41 : UInt64) /- "EKF %s variance" -/ (fp + 256)
      return false
  return true

def AP_Arming_Copter.mandatory_position_checks (this : UInt64) (display_failure : Bool) : PMem.M Bool := do
  let fp ← PMem.enter 264
  let r ← AP_Arming_Copter.mandatory_position_checks.body fp this display_failure
  PMem.leave fp
  return r

/-- C++ `AP_Arming_Copter::alt_checks : bool (bool)`, `AP_Arming_Copter.cpp:551-560`. -/
def AP_Arming_Copter.alt_checks.body (fp : UInt64) (this : UInt64) (display_failure : Bool) : PMem.M Bool := do
  let mut display_failure := display_failure
  let t'1 ← PMem.ldU64 ((0x86d8 : UInt64) /- &copter -/ + 9488)
  let t'2 ← vcall'Mode'has_manual_throttle'3 t'1
  let mut sc'4 := !t'2
  if sc'4 then
    let t'3 ← Copter.ekf_alt_ok (0x86d8 : UInt64) /- &copter -/
    sc'4 := !t'3
  if sc'4 then
    AP_Arming.check_failed'2 this display_failure (0x13b61 : UInt64) /- "Need Alt Estimate" -/ (fp + 0)
    return false
  return true

def AP_Arming_Copter.alt_checks (this : UInt64) (display_failure : Bool) : PMem.M Bool := do
  let fp ← PMem.enter 8
  let r ← AP_Arming_Copter.alt_checks.body fp this display_failure
  PMem.leave fp
  return r

/-- C++ `AP_Arming_Copter::mandatory_checks : bool (bool)`, `AP_Arming_Copter.cpp:654-666`. -/
def AP_Arming_Copter.mandatory_checks (this : UInt64) (display_failure : Bool) : PMem.M Bool := do
  let mut display_failure := display_failure
  let t'1 ← AP_Arming_Copter.mandatory_position_checks this display_failure
  let mut result : Bool := t'1
  PMem.stB ((0xccc0 : UInt64) /- &AP_Notify::flags -/ + 7) result
  let t'2 ← AP_Arming_Copter.alt_checks this display_failure
  if !t'2 then
    result := false
  let t'3 ← AP_Arming.mandatory_checks this display_failure
  return ((if result then (1 : Int32) else (0 : Int32)) &&& (if t'3 then (1 : Int32) else (0 : Int32))) != (0 : Int32)

/-- C++ `AP_Arming_Copter::parameter_checks : bool (bool)`, `AP_Arming_Copter.cpp:203-317`. -/
def AP_Arming_Copter.parameter_checks.body (fp : UInt64) (this : UInt64) (display_failure : Bool) : PMem.M Bool := do
  let mut display_failure := display_failure
  let t'1 ← AP_Arming.check_enabled this (32 : Int32)
  if t'1 then
    let t'2 ← AP_ParamT'signed_char_1.operator_const_signed_char__ (((0x86d8 : UInt64) /- &copter -/ + 6776) + 26)
    let t'3 ← PMem.ldI8 t'2
    if t'3 != (0 : Int8) then
      let t'4 ← PMem.ldU64 ((0x86d8 : UInt64) /- &copter -/ + 8616)
      let t'5 ← RC_Channel.get_radio_min t'4
      let t'6 ← AP_ParamT'unsigned_short_2.operator_const_unsigned_short__ (((0x86d8 : UInt64) /- &copter -/ + 6776) + 28)
      let t'7 ← PMem.ldU16 t'6
      let mut sc'10 := (decide ((Int16.toInt32 (t'5)) ≤ ((UInt32.toInt32 (UInt16.toUInt32 (t'7))) + (10 : Int32))))
      if !sc'10 then
        let t'8 ← AP_ParamT'unsigned_short_2.operator_const_unsigned_short__ (((0x86d8 : UInt64) /- &copter -/ + 6776) + 28)
        let t'9 ← PMem.ldU16 t'8
        sc'10 := (decide ((UInt32.toInt32 (UInt16.toUInt32 (t'9))) < (910 : Int32)))
      if sc'10 then
        AP_Arming.check_failed this (32 : Int32) display_failure (0x13a0b : UInt64) /- "Check FS_THR_VALUE" -/ (fp + 0)
        return false
    let t'11 ← AP_Enum'Parameters_FS_GCS_Action.operator_const_Parameters.FS_GCS_Action (((0x86d8 : UInt64) /- &copter -/ + 6776) + 21)
    if (t'11 == (2 : Int32)) then
      AP_Arming.check_failed this (32 : Int32) display_failure (0x13a1e : UInt64) /- "FS_GCS_ENABLE=2 removed, see FS_OPTIONS" -/ (fp + 8)
    let t'12 ← AP_ParamT'float_4.operator_const_float__'1 (((0x86d8 : UInt64) /- &copter -/ + 6840) + 1636)
    let t'13 ← PMem.ldF32 t'12
    if (decide (t'13 ≤ (Int32.toBinary32 ((0 : Int32))))) then
      AP_Arming.check_failed this (32 : Int32) display_failure (0x13a46 : UInt64) /- "Check PILOT_SPD_UP" -/ (fp + 16)
      return false
    let t'14 ← AP_ParamTBase'signed_char_1.get (((0x86d8 : UInt64) /- &copter -/ + 6840) + 12)
    let t'15 ← PMem.ldI8 t'14
    let sw'16 := Int8.toInt32 (t'15)
    if sw'16 == (13 : Int32) || sw'16 == (11 : Int32) || sw'16 == (6 : Int32) then
      AP_Arming.check_failed this (32 : Int32) display_failure (0x13a59 : UInt64) /- "Invalid MultiCopter FRAME_CLASS" -/ (fp + 24)
      return false
    else
      pure ()
    let t'17 ← ModeRTL.get_alt_type ((0x86d8 : UInt64) /- &copter -/ + 12888)
    if (t'17 == (1 : Int8)) then
      let mut failure_template : UInt64 := (0x13a79 : UInt64) /- "RTL_ALT_TYPE is above-terrain but %s" -/
      let t'18 ← PMem.ldU64 ((0x86d8 : UInt64) /- &copter -/ + 11192)
      let t'19 ← AC_WPNav.get_terrain_source t'18
      let sw'20 := t'19
      if sw'20 == (0 : Int32) then
        PMem.stU64 (fp + 32) (0x13a9e : UInt64) /- "no terrain data" -/
        AP_Arming.check_failed this (32 : Int32) display_failure failure_template (fp + 32)
        return false
      else if sw'20 == (1 : Int32) then
        PMem.stU64 (fp + 40) (0x13aae : UInt64) /- "rangefinder not in firmware" -/
        AP_Arming.check_failed this (32 : Int32) display_failure failure_template (fp + 40)
      else if sw'20 == (2 : Int32) then
        pure ()
      else
        pure ()
    let t'21 ← PMem.ldU64 ((0x86d8 : UInt64) /- &copter -/ + 11184)
    let t'22 ← AC_PosControl.pre_arm_checks t'21 (0x13aca : UInt64) /- "PSC" -/ (fp + 48) (UInt64.toUInt8 (((100 : UInt64) / (1 : UInt64))))
    if !t'22 then
      PMem.stU64 (fp + 152) (fp + 48)
      AP_Arming.check_failed this (32 : Int32) display_failure (0x13ace : UInt64) /- "Bad parameter: %s" -/ (fp + 152)
      return false
    let t'23 ← PMem.ldU64 ((0x86d8 : UInt64) /- &copter -/ + 11168)
    let t'24 ← AC_AttitudeControl.pre_arm_checks t'23 (0x13ae0 : UInt64) /- "ATC" -/ (fp + 48) (UInt64.toUInt8 (((100 : UInt64) / (1 : UInt64))))
    if !t'24 then
      PMem.stU64 (fp + 160) (fp + 48)
      AP_Arming.check_failed this (32 : Int32) display_failure (0x13ace : UInt64) /- "Bad parameter: %s" -/ (fp + 160)
      return false
  return true

def AP_Arming_Copter.parameter_checks (this : UInt64) (display_failure : Bool) : PMem.M Bool := do
  let fp ← PMem.enter 168
  let r ← AP_Arming_Copter.parameter_checks.body fp this display_failure
  PMem.leave fp
  return r

/-- C++ `AP_Arming_Copter::gcs_failsafe_check : bool (bool)`, `AP_Arming_Copter.cpp:519-526`. -/
def AP_Arming_Copter.gcs_failsafe_check.body (fp : UInt64) (this : UInt64) (display_failure : Bool) : PMem.M Bool := do
  let mut display_failure := display_failure
  let t'1 ← PMem.ldBits ((0x86d8 : UInt64) /- &copter -/ + 9508) 73 1
  if (UInt64.toUInt8 (t'1)) != (0 : UInt8) then
    AP_Arming.check_failed'2 this display_failure (0x13b51 : UInt64) /- "GCS failsafe on" -/ (fp + 0)
    return false
  return true

def AP_Arming_Copter.gcs_failsafe_check (this : UInt64) (display_failure : Bool) : PMem.M Bool := do
  let fp ← PMem.enter 8
  let r ← AP_Arming_Copter.gcs_failsafe_check.body fp this display_failure
  PMem.leave fp
  return r

/-- C++ `AP_Arming_Copter::rc_throttle_failsafe_checks : bool (bool) const`, `AP_Arming_Copter.cpp:89-125`. -/
def AP_Arming_Copter.rc_throttle_failsafe_checks.body (fp : UInt64) (this : UInt64) (display_failure : Bool) : PMem.M Bool := do
  let mut display_failure := display_failure
  let t'1 ← AP_Arming.check_enabled this (64 : Int32)
  if !t'1 then
    return true
  let t'2 ← AP_Enum'Parameters_FS_THR_Action.operator_const_Parameters.FS_THR_Action (((0x86d8 : UInt64) /- &copter -/ + 6776) + 26)
  if (t'2 == (0 : Int32)) then
    return true
  let mut rc_item : UInt64 := (0x139ab : UInt64) /- "Throttle" -/
  let t'3 ← rc
  let t'4 ← RC_Channels.has_had_rc_receiver t'3
  let mut sc'7 := !t'4
  if sc'7 then
    let t'5 ← rc
    let t'6 ← RC_Channels.has_had_rc_override t'5
    sc'7 := !t'6
  if sc'7 then
    AP_Arming.check_failed this (64 : Int32) display_failure (0x139b4 : UInt64) /- "RC not found" -/ (fp + 0)
    return false
  let t'8 ← PMem.ldU64 ((0x86d8 : UInt64) /- &copter -/ + 8616)
  let t'9 ← RC_Channel.get_radio_in t'8
  let t'10 ← AP_ParamT'unsigned_short_2.operator_const_unsigned_short__ (((0x86d8 : UInt64) /- &copter -/ + 6776) + 28)
  let t'11 ← PMem.ldU16 t'10
  if (decide ((Int16.toInt32 (t'9)) ≤ (UInt32.toInt32 (UInt16.toUInt32 (t'11))))) then
    PMem.stU64 (fp + 8) rc_item
    AP_Arming.check_failed this (64 : Int32) display_failure (0x139c1 : UInt64) /- "%s below failsafe" -/ (fp + 8)
    return false
  return true

def AP_Arming_Copter.rc_throttle_failsafe_checks (this : UInt64) (display_failure : Bool) : PMem.M Bool := do
  let fp ← PMem.enter 16
  let r ← AP_Arming_Copter.rc_throttle_failsafe_checks.body fp this display_failure
  PMem.leave fp
  return r

/-- C++ `AP_Arming_Copter::barometer_checks : bool (bool)`, `AP_Arming_Copter.cpp:127-151`. -/
def AP_Arming_Copter.barometer_checks.body (fp : UInt64) (this : UInt64) (display_failure : Bool) : PMem.M Bool := do
  let mut display_failure := display_failure
  let t'1 ← AP_Arming.barometer_checks this display_failure
  if !t'1 then
    return false
  let mut ret : Bool := true
  let t'2 ← AP_Arming.check_enabled this (2 : Int32)
  if t'2 then
    let t'3 ← VehicleBridge.ahrs'0
    let ahrs : UInt64 := t'3
    let t'4 ← VehicleBridge.AP_AHRS.configured_backend_has_status'1 ahrs (256 : Int32)
    let mut sc'6 := !t'4
    if sc'6 then
      let t'5 ← VehicleBridge.AP_AHRS.configured_backend_has_status'1 ahrs (512 : Int32)
      sc'6 := t'5
    let mut using_baro_ref : Bool := sc'6
    PMem.stF32 (fp + 0) (Int32.toBinary32 ((0 : Int32)))
    for _ in [0:1] do
      let mut __unique_name___COUNTER__ : Bool := default  -- uninitialized in C
      let t'7 ← VehicleBridge.ahrs'0
      let t'8 ← VehicleBridge.AP_AHRS.get_relative_position_D_origin_float'1 t'7 (fp + 0)
      __unique_name___COUNTER__ := t'8
    if using_baro_ref then
      let t'9 ← PMem.ldF32 (fp + 0)
      let t'10 ← PMem.ldF32 ((0x86d8 : UInt64) /- &copter -/ + 11112)
      if (decide ((Binary32.abs ((-t'9) - t'10)) > (Binary64.toBinary32 ((Binary64.ofBits 0x3ff0000000000000 /- 1 -/))))) then
        AP_Arming.check_failed this (2 : Int32) display_failure (0x139d3 : UInt64) /- "Altitude disparity" -/ (fp + 8)
        ret := false
  return ret

def AP_Arming_Copter.barometer_checks (this : UInt64) (display_failure : Bool) : PMem.M Bool := do
  let fp ← PMem.enter 16
  let r ← AP_Arming_Copter.barometer_checks.body fp this display_failure
  PMem.leave fp
  return r

/-- C++ `AP_Arming_Copter::ins_checks : bool (bool)`, `AP_Arming_Copter.cpp:153-167`. -/
def AP_Arming_Copter.ins_checks.body (fp : UInt64) (this : UInt64) (display_failure : Bool) : PMem.M Bool := do
  let mut display_failure := display_failure
  let t'1 ← AP_Arming.ins_checks this display_failure
  let mut ret : Bool := t'1
  let t'2 ← AP_Arming.check_enabled this (16 : Int32)
  if t'2 then
    let t'3 ← AP_Arming_Copter.pre_arm_ekf_attitude_check this
    if !t'3 then
      AP_Arming.check_failed this (16 : Int32) display_failure (0x139e6 : UInt64) /- "EKF attitude is bad" -/ (fp + 0)
      ret := false
  return ret

def AP_Arming_Copter.ins_checks (this : UInt64) (display_failure : Bool) : PMem.M Bool := do
  let fp ← PMem.enter 8
  let r ← AP_Arming_Copter.ins_checks.body fp this display_failure
  PMem.leave fp
  return r

/-- C++ `AP_Arming_Copter::gps_checks : bool (bool)`, `AP_Arming_Copter.cpp:355-404`. -/
def AP_Arming_Copter.gps_checks.body (fp : UInt64) (this : UInt64) (display_failure : Bool) : PMem.M Bool := do
  let mut display_failure := display_failure
  let mut fence_requires_position : Bool := false
  let t'1 ← PMem.ldU64 ((0x86d8 : UInt64) /- &copter -/ + 9488)
  let t'2 ← vcall'Mode'requires_position'5 t'1
  let mut sc'4 := (t'2 || fence_requires_position)
  if !sc'4 then
    let t'3 ← PMem.ldI32 ((0x86d8 : UInt64) /- &copter -/ + 9552)
    sc'4 := (t'3 == (2 : Int32))
  let mut mode_requires_position : Bool := sc'4
  let t'5 ← VehicleBridge.ahrs'0
  let t'6 ← VehicleBridge.AP_AHRS.active_backend_configured_to_use_gps'0 t'5
  let mut mode_requires_gps : Bool := (t'6 && mode_requires_position)
  if mode_requires_gps then
    let t'7 ← AP_Arming.gps_checks this display_failure
    if !t'7 then
      PMem.stB ((0xccc0 : UInt64) /- &AP_Notify::flags -/ + 7) false
      return false
  let t'8 ← AP_Arming_Copter.mandatory_position_checks this display_failure
  if !t'8 then
    PMem.stB ((0xccc0 : UInt64) /- &AP_Notify::flags -/ + 7) false
    return false
  if !mode_requires_gps then
    PMem.stB ((0xccc0 : UInt64) /- &AP_Notify::flags -/ + 7) true
    return true
  let t'9 ← AP_Arming.check_enabled this (8 : Int32)
  if !t'9 then
    PMem.stB ((0xccc0 : UInt64) /- &AP_Notify::flags -/ + 7) true
    return true
  let t'10 ← VehicleBridge.AP_GPS.num_sensors'0 ((0x86d8 : UInt64) /- &copter -/ + 384)
  let mut sc'14 := (decide ((UInt32.toInt32 (UInt8.toUInt32 (t'10))) > (0 : Int32)))
  if sc'14 then
    let t'11 ← VehicleBridge.AP_GPS.get_hdop'0 ((0x86d8 : UInt64) /- &copter -/ + 384)
    let t'12 ← AP_ParamT'short_2.operator_const_short__ (((0x86d8 : UInt64) /- &copter -/ + 6776) + 22)
    let t'13 ← PMem.ldI16 t'12
    sc'14 := (decide ((UInt32.toInt32 (UInt16.toUInt32 (t'11))) > (Int16.toInt32 (t'13))))
  if sc'14 then
    AP_Arming.check_failed this (8 : Int32) display_failure (0x13ae4 : UInt64) /- "High GPS HDOP" -/ (fp + 0)
    PMem.stB ((0xccc0 : UInt64) /- &AP_Notify::flags -/ + 7) false
    return false
  PMem.stB ((0xccc0 : UInt64) /- &AP_Notify::flags -/ + 7) true
  return true

def AP_Arming_Copter.gps_checks (this : UInt64) (display_failure : Bool) : PMem.M Bool := do
  let fp ← PMem.enter 8
  let r ← AP_Arming_Copter.gps_checks.body fp this display_failure
  PMem.leave fp
  return r

/-- C++ `AP_Arming_Copter::rc_calibration_checks : bool (bool)`, `AP_Arming_Copter.cpp:338-352`. -/
def AP_Arming_Copter.rc_calibration_checks.body (fp : UInt64) (this : UInt64) (display_failure : Bool) : PMem.M Bool := do
  let mut display_failure := display_failure
  let t'1 ← PMem.ldU64 ((0x86d8 : UInt64) /- &copter -/ + 8600)
  PMem.stU64 ((fp + 0) + 0) t'1
  let t'2 ← PMem.ldU64 ((0x86d8 : UInt64) /- &copter -/ + 8608)
  PMem.stU64 ((fp + 0) + 8) t'2
  let t'3 ← PMem.ldU64 ((0x86d8 : UInt64) /- &copter -/ + 8616)
  PMem.stU64 ((fp + 0) + 16) t'3
  let t'4 ← PMem.ldU64 ((0x86d8 : UInt64) /- &copter -/ + 8624)
  PMem.stU64 ((fp + 0) + 24) t'4
  let t'5 ← AP_Arming.rc_checks_copter_sub this display_failure (fp + 0)
  let t'6 ← AP_Arming.rc_calibration_checks this display_failure
  let t'7 := ((if t'5 then (1 : Int32) else (0 : Int32)) &&& (if t'6 then (1 : Int32) else (0 : Int32))) != (0 : Int32)
  PMem.stB (((0x86d8 : UInt64) /- &copter -/ + 9448) + 3) t'7
  let t'8 ← PMem.ldB (((0x86d8 : UInt64) /- &copter -/ + 9448) + 3)
  return t'8

def AP_Arming_Copter.rc_calibration_checks (this : UInt64) (display_failure : Bool) : PMem.M Bool := do
  let fp ← PMem.enter 32
  let r ← AP_Arming_Copter.rc_calibration_checks.body fp this display_failure
  PMem.leave fp
  return r

/-- C++ `AP_Arming_Copter::board_voltage_checks : bool (bool)`, `AP_Arming_Copter.cpp:169-184`. -/
def AP_Arming_Copter.board_voltage_checks.body (fp : UInt64) (this : UInt64) (display_failure : Bool) : PMem.M Bool := do
  let mut display_failure := display_failure
  let t'1 ← AP_Arming.board_voltage_checks this display_failure
  if !t'1 then
    return false
  let t'2 ← AP_Arming.check_enabled this (128 : Int32)
  if t'2 then
    let t'3 ← AP_BattMonitor.has_failsafed ((0x86d8 : UInt64) /- &copter -/ + 9584)
    if t'3 then
      AP_Arming.check_failed this (128 : Int32) display_failure (0x139fa : UInt64) /- "Battery failsafe" -/ (fp + 0)
      return false
  return true

def AP_Arming_Copter.board_voltage_checks (this : UInt64) (display_failure : Bool) : PMem.M Bool := do
  let fp ← PMem.enter 8
  let r ← AP_Arming_Copter.board_voltage_checks.body fp this display_failure
  PMem.leave fp
  return r

/-- C++ `AP_Arming_Copter::arm_checks : bool (AP_Arming::Method)`, `AP_Arming_Copter.cpp:565-651`. -/
def AP_Arming_Copter.arm_checks.body (fp : UInt64) (this : UInt64) (method : Int32) : PMem.M Bool := do
  let mut method := method
  let t'1 ← VehicleBridge.ahrs'0
  let ahrs : UInt64 := t'1
  let t'2 ← VehicleBridge.AP_AHRS.healthy'0 ahrs
  if !t'2 then
    AP_Arming.check_failed'2 this true (0x13b73 : UInt64) /- "AHRS not healthy" -/ (fp + 0)
    return false
  let t'3 ← AP_Arming.check_enabled this (4 : Int32)
  let mut sc'5 := t'3
  if sc'5 then
    let t'4 ← VehicleBridge.AP_AHRS.using_noncompass_for_yaw'0 ahrs
    sc'5 := !t'4
  if sc'5 then
    let t'6 ← VehicleBridge.compass'0
    let _compass : UInt64 := t'6
    let t'7 ← VehicleBridge.Compass.healthy'0 _compass
    if !t'7 then
      let t'8 ← VehicleBridge.Compass.get_first_usable'0 _compass
      PMem.stU64 (fp + 8) (Int64.toUInt64 (Int32.toInt64 (((UInt32.toInt32 (UInt8.toUInt32 (t'8))) + (1 : Int32)))))
      AP_Arming.check_failed'2 this true (0x13b84 : UInt64) /- "Compass %d not healthy" -/ (fp + 8)
      return false
  let t'9 ← PMem.ldU64 ((0x86d8 : UInt64) /- &copter -/ + 9488)
  let t'10 ← vcall'Mode'allows_arming'4 t'9 method
  if !t'10 then
    let t'11 ← PMem.ldU64 ((0x86d8 : UInt64) /- &copter -/ + 9488)
    let t'12 ← vcall'Mode'name'8 t'11
    PMem.stU64 (fp + 16) t'12
    AP_Arming.check_failed'2 this true (0x13b9b : UInt64) /- "%s mode not armable" -/ (fp + 16)
    return false
  let t'13 ← AP_Arming.should_skip_all_checks this
  if t'13 then
    return true
  let t'14 ← AP_Arming.check_enabled this (16 : Int32)
  if t'14 then
    let t'15 ← VehicleBridge.AP_AHRS.cos_roll'0 ahrs
    let t'16 ← VehicleBridge.AP_AHRS.cos_pitch'0 ahrs
    let t'17 ← PMem.ldU64 ((0x86d8 : UInt64) /- &copter -/ + 11168)
    let t'18 ← AC_AttitudeControl.lean_angle_max_rad t'17
    if (decide ((Musl.acosf.acosf (t'15 * t'16)) > t'18)) then
      AP_Arming.check_failed this (16 : Int32) true (0x13baf : UInt64) /- "Leaning" -/ (fp + 24)
      return false
  let t'19 ← AP_Arming.check_enabled this (64 : Int32)
  if t'19 then
    let mut rc_item : UInt64 := (0x139ab : UInt64) /- "Throttle" -/
    let t'20 ← AP_Arming.method_is_GCS method
    let mut sc'23 := (t'20 || (method == (4 : Int32)))
    if sc'23 then
      let t'21 ← PMem.ldU64 ((0x86d8 : UInt64) /- &copter -/ + 9488)
      let t'22 ← vcall'Mode'allows_GCS_or_SCR_arming_with_throttle_high'27 t'21
      sc'23 := t'22
    if !sc'23 then
      let t'24 ← Copter.get_pilot_desired_climb_rate_ms (0x86d8 : UInt64) /- &copter -/
      if (decide (t'24 > (Binary32.ofBits 0x00000000 /- 0 -/))) then
        PMem.stU64 (fp + 32) rc_item
        AP_Arming.check_failed this (64 : Int32) true (0x13bb7 : UInt64) /- "%s too high" -/ (fp + 32)
        return false
      let t'25 ← PMem.ldU64 ((0x86d8 : UInt64) /- &copter -/ + 9488)
      let t'26 ← vcall'Mode'has_manual_throttle'3 t'25
      let mut sc'29 := t'26
      if !sc'29 then
        let t'27 ← PMem.ldU64 ((0x86d8 : UInt64) /- &copter -/ + 9488)
        let t'28 ← vcall'Mode'mode_number'1 t'27
        sc'29 := (t'28 == (11 : UInt8))
      let mut sc'32 := sc'29
      if sc'32 then
        let t'30 ← PMem.ldU64 ((0x86d8 : UInt64) /- &copter -/ + 8616)
        let t'31 ← RC_Channel.get_control_in t'30
        sc'32 := (decide ((Int16.toInt32 (t'31)) > (0 : Int32)))
      if sc'32 then
        PMem.stU64 (fp + 40) rc_item
        AP_Arming.check_failed this (64 : Int32) true (0x13bb7 : UInt64) /- "%s too high" -/ (fp + 40)
        return false
  let t'33 ← PMem.ldU64 ((0xba88 : UInt64) /- &hal -/ + 88)
  let t'34 ← PMem.halDev "AP_HAL::Util::safety_switch_state" t'33 #[]
  if ((UInt32.toInt32 (UInt8.toUInt32 ((UInt64.toUInt8 (t'34))))) == (UInt32.toInt32 (UInt8.toUInt32 ((1 : UInt8))))) then
    AP_Arming.check_failed'2 this true (0x13bc3 : UInt64) /- "Safety Switch" -/ (fp + 48)
    return false
  let t'35 ← AP_Arming.arm_checks this method
  return t'35

def AP_Arming_Copter.arm_checks (this : UInt64) (method : Int32) : PMem.M Bool := do
  let fp ← PMem.enter 56
  let r ← AP_Arming_Copter.arm_checks.body fp this method
  PMem.leave fp
  return r

/-- C++ `Copter::set_home : bool (const Location &, bool)`, `commands.cpp:58-78`. -/
def Copter.set_home.body (fp : UInt64) (this : UInt64) (loc : UInt64) (lock : Bool) : PMem.M Bool := do
  let mut lock := lock
  Location.Location (fp + 0)
  let t'1 ← VehicleBridge.AP_AHRS.get_origin'1 (this + 4080) (fp + 0)
  if !t'1 then
    return false
  let t'2 ← VehicleBridge.AP_AHRS.set_home'1 (this + 4080) loc
  worldOutputs'drain
  if !t'2 then
    return false
  if lock then
    VehicleBridge.AP_AHRS.lock_home'0 (this + 4080)
  return true

def Copter.set_home (this : UInt64) (loc : UInt64) (lock : Bool) : PMem.M Bool := do
  let fp ← PMem.enter 16
  let r ← Copter.set_home.body fp this loc lock
  PMem.leave fp
  return r

/-- C++ `Copter::set_home_to_current_location : bool (bool)`, `commands.cpp:40-54`. -/
def Copter.set_home_to_current_location.body (fp : UInt64) (this : UInt64) (lock : Bool) : PMem.M Bool := do
  let mut lock := lock
  Location.Location (fp + 0)
  let t'1 ← VehicleBridge.AP_AHRS.get_location'1 (this + 4080) (fp + 0)
  if t'1 then
    let t'2 ← Copter.set_home this (fp + 0) lock
    if !t'2 then
      return false
    return true
  return false

def Copter.set_home_to_current_location (this : UInt64) (lock : Bool) : PMem.M Bool := do
  let fp ← PMem.enter 16
  let r ← Copter.set_home_to_current_location.body fp this lock
  PMem.leave fp
  return r

/-- C++ `ModeRTL::restart_without_terrain : void ()`, `mode_rtl.cpp:108-117`. -/
def ModeRTL.restart_without_terrain.body (fp : UInt64) (this : UInt64) : PMem.M Unit := do
  PMem.stB (this + 204) false
  PMem.stU8 (this + 128) (0 : UInt8)
  PMem.stB (this + 129) true
  let t'1 ← Mode.gcs this
  GCS.send_text t'1 (2 : UInt32) (0x14bc0 : UInt64) /- "Restarting RTL - Terrain data missing" -/ (fp + 0)
  return ()

def ModeRTL.restart_without_terrain (this : UInt64) : PMem.M Unit := do
  let fp ← PMem.enter 8
  let r ← ModeRTL.restart_without_terrain.body fp this
  PMem.leave fp
  return r

/-- C++ `ModeAuto::get_spline_from_cmd : bool (const AP_Mission::Mission_Command &, const Location &, Location &, Location &, bool &)`, `mode_auto.cpp:1891-1912`. -/
def ModeAuto.get_spline_from_cmd.body (fp : UInt64) (this : UInt64) (cmd : UInt64) (default_loc : UInt64) (dest_loc : UInt64) (next_dest_loc : UInt64) (next_dest_loc_is_spline : UInt64) : PMem.M Bool := do
  let t'1 ← ModeAuto.get_loc_from_cmd this cmd default_loc dest_loc
  if !t'1 then
    return false
  AP_Mission.Mission_Command.Mission_Command (fp + 0)
  let t'2 ← PMem.ldU16 (cmd + 4)
  let mut sc'5 := ((UInt32.toInt32 (UInt16.toUInt32 (t'2))) == (0 : Int32))
  if sc'5 then
    let t'3 ← PMem.ldU16 cmd
    let t'4 ← AP_Mission.get_next_nav_cmd (this + 112) (Int16.toUInt16 (Int32.toInt16 (((UInt32.toInt32 (UInt16.toUInt32 (t'3))) + (1 : Int32))))) (fp + 0)
    sc'5 := t'4
  let mut sc'8 := sc'5
  if sc'8 then
    let t'6 ← PMem.ldU16 ((fp + 0) + 2)
    let t'7 ← AP_Mission.cmd_has_location t'6
    sc'8 := t'7
  if sc'8 then
    let t'9 ← ModeAuto.get_loc_from_cmd this (fp + 0) dest_loc next_dest_loc
    if !t'9 then
      return false
    let t'10 ← PMem.ldU16 ((fp + 0) + 2)
    let t'11 := ((UInt32.toInt32 (UInt16.toUInt32 (t'10))) == (UInt32.toInt32 ((82 : UInt32))))
    PMem.stB next_dest_loc_is_spline t'11
  else
    discard <| PMem.memcpy next_dest_loc dest_loc 16
    discard <| pure (next_dest_loc)
    PMem.stB next_dest_loc_is_spline false
  return true

def ModeAuto.get_spline_from_cmd (this : UInt64) (cmd : UInt64) (default_loc : UInt64) (dest_loc : UInt64) (next_dest_loc : UInt64) (next_dest_loc_is_spline : UInt64) : PMem.M Bool := do
  let fp ← PMem.enter 28
  let r ← ModeAuto.get_spline_from_cmd.body fp this cmd default_loc dest_loc next_dest_loc next_dest_loc_is_spline
  PMem.leave fp
  return r

/-- C++ `ModeAuto::set_next_wp : bool (const AP_Mission::Mission_Command &, const Location &)`, `mode_auto.cpp:1623-1688`. -/
def ModeAuto.set_next_wp.body (fp : UInt64) (this : UInt64) (current_cmd : UInt64) (default_loc : UInt64) : PMem.M Bool := do
  let t'1 ← PMem.ldU16 (current_cmd + 4)
  let mut sc'5 := (decide ((UInt32.toInt32 (UInt16.toUInt32 (t'1))) > (0 : Int32)))
  if sc'5 then
    let t'2 ← PMem.ldU16 (current_cmd + 2)
    let mut sc'4 := ((UInt32.toInt32 (UInt16.toUInt32 (t'2))) == (UInt32.toInt32 ((16 : UInt32))))
    if !sc'4 then
      let t'3 ← PMem.ldU16 (current_cmd + 2)
      sc'4 := ((UInt32.toInt32 (UInt16.toUInt32 (t'3))) == (UInt32.toInt32 ((82 : UInt32))))
    sc'5 := sc'4
  if sc'5 then
    return true
  AP_Mission.Mission_Command.Mission_Command (fp + 0)
  let t'6 ← PMem.ldU16 current_cmd
  let t'7 ← AP_Mission.get_next_nav_cmd (this + 112) (Int16.toUInt16 (Int32.toInt16 (((UInt32.toInt32 (UInt16.toUInt32 (t'6))) + (1 : Int32))))) (fp + 0)
  if !t'7 then
    return true
  let t'8 ← PMem.ldU16 ((fp + 0) + 2)
  let sw'9 := UInt32.toInt32 (UInt16.toUInt32 (t'8))
  if sw'9 == (85 : Int32) || sw'9 == (21 : Int32) then
    PMem.stI32 (((fp + 0) + 8) + 4) (0 : Int32)
    Location.Location (fp + 32)
    Location.Location (fp + 48)
    let t'10 ← ModeAuto.get_loc_from_cmd this current_cmd default_loc (fp + 32)
    let mut sc'12 := !t'10
    if !sc'12 then
      let t'11 ← ModeAuto.get_loc_from_cmd this (fp + 0) (fp + 32) (fp + 48)
      sc'12 := !t'11
    if sc'12 then
      return false
    let t'13 ← PMem.ldU64 (this + 24)
    let t'14 ← PMem.ldU64 t'13
    let t'15 ← AC_WPNav.set_wp_destination_next_loc t'14 (fp + 48) (Binary64.toBinary32 ((Binary64.ofBits 0x0000000000000000 /- 0 -/)))
    return t'15
    Location.Location (fp + 64)
    Location.Location (fp + 80)
    let t'16 ← ModeAuto.get_spline_from_cmd this (fp + 0) default_loc (fp + 64) (fp + 80) (fp + 96)
    if !t'16 then
      return false
    let t'17 ← PMem.ldB (fp + 96)
    let t'18 ← PMem.ldU64 (this + 24)
    let t'19 ← PMem.ldU64 t'18
    let t'20 ← AC_WPNav.set_spline_destination_next_loc t'19 (fp + 64) (fp + 80) t'17
    return t'20
    Location.Location (fp + 104)
    Location.Location (fp + 120)
    let t'21 ← ModeAuto.get_loc_from_cmd this current_cmd default_loc (fp + 104)
    let mut sc'23 := !t'21
    if !sc'23 then
      let t'22 ← ModeAuto.get_loc_from_cmd this (fp + 0) (fp + 104) (fp + 120)
      sc'23 := !t'22
    if sc'23 then
      return false
    let t'24 ← AP_Mission.Mission_Command.get_arc_angle_rad (fp + 0)
    let mut arc_angle_rad : Binary32 := t'24
    let t'25 ← PMem.ldU64 (this + 24)
    let t'26 ← PMem.ldU64 t'25
    let t'27 ← AC_WPNav.set_wp_destination_next_loc t'26 (fp + 120) arc_angle_rad
    return t'27
  else if sw'9 == (16 : Int32) || sw'9 == (17 : Int32) || sw'9 == (19 : Int32) then
    Location.Location (fp + 136)
    Location.Location (fp + 152)
    let t'28 ← ModeAuto.get_loc_from_cmd this current_cmd default_loc (fp + 136)
    let mut sc'30 := !t'28
    if !sc'30 then
      let t'29 ← ModeAuto.get_loc_from_cmd this (fp + 0) (fp + 136) (fp + 152)
      sc'30 := !t'29
    if sc'30 then
      return false
    let t'31 ← PMem.ldU64 (this + 24)
    let t'32 ← PMem.ldU64 t'31
    let t'33 ← AC_WPNav.set_wp_destination_next_loc t'32 (fp + 152) (Binary64.toBinary32 ((Binary64.ofBits 0x0000000000000000 /- 0 -/)))
    return t'33
    Location.Location (fp + 168)
    Location.Location (fp + 184)
    let t'34 ← ModeAuto.get_spline_from_cmd this (fp + 0) default_loc (fp + 168) (fp + 184) (fp + 200)
    if !t'34 then
      return false
    let t'35 ← PMem.ldB (fp + 200)
    let t'36 ← PMem.ldU64 (this + 24)
    let t'37 ← PMem.ldU64 t'36
    let t'38 ← AC_WPNav.set_spline_destination_next_loc t'37 (fp + 168) (fp + 184) t'35
    return t'38
    Location.Location (fp + 208)
    Location.Location (fp + 224)
    let t'39 ← ModeAuto.get_loc_from_cmd this current_cmd default_loc (fp + 208)
    let mut sc'41 := !t'39
    if !sc'41 then
      let t'40 ← ModeAuto.get_loc_from_cmd this (fp + 0) (fp + 208) (fp + 224)
      sc'41 := !t'40
    if sc'41 then
      return false
    let t'42 ← AP_Mission.Mission_Command.get_arc_angle_rad (fp + 0)
    let mut arc_angle_rad'2 : Binary32 := t'42
    let t'43 ← PMem.ldU64 (this + 24)
    let t'44 ← PMem.ldU64 t'43
    let t'45 ← AC_WPNav.set_wp_destination_next_loc t'44 (fp + 224) arc_angle_rad'2
    return t'45
  else if sw'9 == (82 : Int32) then
    Location.Location (fp + 240)
    Location.Location (fp + 256)
    let t'46 ← ModeAuto.get_spline_from_cmd this (fp + 0) default_loc (fp + 240) (fp + 256) (fp + 272)
    if !t'46 then
      return false
    let t'47 ← PMem.ldB (fp + 272)
    let t'48 ← PMem.ldU64 (this + 24)
    let t'49 ← PMem.ldU64 t'48
    let t'50 ← AC_WPNav.set_spline_destination_next_loc t'49 (fp + 240) (fp + 256) t'47
    return t'50
    Location.Location (fp + 280)
    Location.Location (fp + 296)
    let t'51 ← ModeAuto.get_loc_from_cmd this current_cmd default_loc (fp + 280)
    let mut sc'53 := !t'51
    if !sc'53 then
      let t'52 ← ModeAuto.get_loc_from_cmd this (fp + 0) (fp + 280) (fp + 296)
      sc'53 := !t'52
    if sc'53 then
      return false
    let t'54 ← AP_Mission.Mission_Command.get_arc_angle_rad (fp + 0)
    let mut arc_angle_rad'3 : Binary32 := t'54
    let t'55 ← PMem.ldU64 (this + 24)
    let t'56 ← PMem.ldU64 t'55
    let t'57 ← AC_WPNav.set_wp_destination_next_loc t'56 (fp + 296) arc_angle_rad'3
    return t'57
  else if sw'9 == (36 : Int32) then
    Location.Location (fp + 312)
    Location.Location (fp + 328)
    let t'58 ← ModeAuto.get_loc_from_cmd this current_cmd default_loc (fp + 312)
    let mut sc'60 := !t'58
    if !sc'60 then
      let t'59 ← ModeAuto.get_loc_from_cmd this (fp + 0) (fp + 312) (fp + 328)
      sc'60 := !t'59
    if sc'60 then
      return false
    let t'61 ← AP_Mission.Mission_Command.get_arc_angle_rad (fp + 0)
    let mut arc_angle_rad'4 : Binary32 := t'61
    let t'62 ← PMem.ldU64 (this + 24)
    let t'63 ← PMem.ldU64 t'62
    let t'64 ← AC_WPNav.set_wp_destination_next_loc t'63 (fp + 328) arc_angle_rad'4
    return t'64
  else if sw'9 == (18 : Int32) || sw'9 == (20 : Int32) || sw'9 == (84 : Int32) || sw'9 == (22 : Int32) then
    pure ()
  else
    pure ()
  return true

def ModeAuto.set_next_wp (this : UInt64) (current_cmd : UInt64) (default_loc : UInt64) : PMem.M Bool := do
  let fp ← PMem.enter 344
  let r ← ModeAuto.set_next_wp.body fp this current_cmd default_loc
  PMem.leave fp
  return r

/-- C++ `ModeAuto::do_nav_delay : void (const AP_Mission::Mission_Command &)`, `mode_auto.cpp:1936-1952`. -/
def ModeAuto.do_nav_delay.body (fp : UInt64) (this : UInt64) (cmd : UInt64) : PMem.M Unit := do
  let t'1 := ((← PMem.clock) / 1000).toUInt32
  PMem.stU32 (this + 844) t'1
  let t'2 ← PMem.ldF32 (cmd + 8)
  if (decide (t'2 > (Int32.toBinary32 ((0 : Int32))))) then
    let t'3 ← PMem.ldF32 (cmd + 8)
    let t'4 := Binary32.toUInt32 ((t'3 * (Int32.toBinary32 ((1000 : Int32)))))
    PMem.stU32 (this + 840) t'4
  else
    let t'5 ← PMem.ldI8 ((cmd + 8) + 4)
    let t'6 ← PMem.ldI8 ((cmd + 8) + 5)
    let t'7 ← PMem.ldI8 ((cmd + 8) + 6)
    let t'8 ← VehicleBridge.rtc'0
    let t'9 ← VehicleBridge.AP_RTC.get_time_utc'4 t'8 (Int8.toInt32 (t'5)) (Int8.toInt32 (t'6)) (Int8.toInt32 (t'7)) (0 : Int32)
    PMem.stU32 (this + 840) t'9
  let t'10 ← PMem.ldU32 (this + 840)
  PMem.stU64 (fp + 0) (UInt32.toUInt64 ((t'10 / (Int32.toUInt32 ((1000 : Int32))))))
  let t'11 ← Mode.gcs this
  GCS.send_text t'11 (6 : UInt32) (0x14a93 : UInt64) /- "Delaying %u sec" -/ (fp + 0)
  return ()

def ModeAuto.do_nav_delay (this : UInt64) (cmd : UInt64) : PMem.M Unit := do
  let fp ← PMem.enter 8
  let r ← ModeAuto.do_nav_delay.body fp this cmd
  PMem.leave fp
  return r

/-- C++ `ModeAuto::do_set_home : void (const AP_Mission::Mission_Command &)`, `mode_auto.cpp:2038-2049`. -/
def ModeAuto.do_set_home (this : UInt64) (cmd : UInt64) : PMem.M Unit := do
  let t'1 ← PMem.ldU16 (cmd + 4)
  let mut sc'3 := ((UInt32.toInt32 (UInt16.toUInt32 (t'1))) == (1 : Int32))
  if !sc'3 then
    let t'2 ← Location.initialised (cmd + 8)
    sc'3 := !t'2
  if sc'3 then
    let t'4 ← Copter.set_home_to_current_location (0x86d8 : UInt64) /- &copter -/ false
    if !t'4 then
      pure ()
  else
    let t'5 ← Copter.set_home (0x86d8 : UInt64) /- &copter -/ (cmd + 8) false
    if !t'5 then
      pure ()
  return ()

/-- C++ `Mode::get_pilot_desired_throttle : float () const`, `mode.cpp:978-1003`. -/
def Mode.get_pilot_desired_throttle (this : UInt64) : PMem.M Binary32 := do
  let t'1 ← Copter.get_throttle_mid (0x86d8 : UInt64) /- &copter -/
  let mut mid_stick : Int16 := t'1
  if (decide ((Int16.toInt32 (mid_stick)) ≤ (0 : Int32))) then
    let t'2 := Int32.toInt16 ((500 : Int32))
    mid_stick := t'2
  let t'3 ← PMem.ldU64 (this + 88)
  let t'4 ← PMem.ldU64 t'3
  let t'5 ← RC_Channel.get_control_in t'4
  let mut throttle_control : Int16 := t'5
  let t'6 ← constrain_int16 throttle_control (Int32.toInt16 ((0 : Int32))) (Int32.toInt16 ((1000 : Int32)))
  throttle_control := t'6
  let mut throttle_in : Binary32 := default  -- uninitialized in C
  if (decide ((Int16.toInt32 (throttle_control)) < (Int16.toInt32 (mid_stick)))) then
    let t'7 := (((Int16.toBinary32 (throttle_control)) * (Binary32.ofBits 0x3f000000 /- 1/2 -/)) / (Int16.toBinary32 (mid_stick)))
    throttle_in := t'7
  else
    let t'8 := ((Binary32.ofBits 0x3f000000 /- 1/2 -/) + (((Int32.toBinary32 (((Int16.toInt32 (throttle_control)) - (Int16.toInt32 (mid_stick))))) * (Binary32.ofBits 0x3f000000 /- 1/2 -/)) / (Int32.toBinary32 (((1000 : Int32) - (Int16.toInt32 (mid_stick)))))))
    throttle_in := t'8
  let t'9 ← vcall'Mode'throttle_hover'9 this
  let mut thr_mid : Binary32 := t'9
  let t'10 ← constrain_value_line'float ((-(thr_mid - (Binary32.ofBits 0x3f000000 /- 1/2 -/))) / (Binary32.ofBits 0x3ec00000 /- 3/8 -/)) (-(Binary32.ofBits 0x3f000000 /- 1/2 -/)) (Binary32.ofBits 0x3f800000 /- 1 -/) (Int32.toUInt32 ((999 : Int32)))
  let mut expo : Binary32 := t'10
  let mut throttle_out : Binary32 := ((throttle_in * ((Binary32.ofBits 0x3f800000 /- 1 -/) - expo)) + (((expo * throttle_in) * throttle_in) * throttle_in))
  return throttle_out

/-- C++ `Mode::_TakeOff::stop : void ()`, `takeoff.cpp:60-68`. -/
def Mode._TakeOff.stop (this : UInt64) : PMem.M Unit := do
  PMem.stB this false
  let t'1 ← PMem.ldU64 ((0x86d8 : UInt64) /- &copter -/ + 11168)
  let t'2 ← AC_AttitudeControl.get_throttle_in t'1
  let t'3 ← Copter.get_non_takeoff_throttle (0x86d8 : UInt64) /- &copter -/
  if (decide (t'2 > t'3)) then
    Copter.set_land_complete (0x86d8 : UInt64) /- &copter -/ false
  return ()

/-- C++ `Mode::takeoff_stop : void ()`, `AP_Common.h:163-?`. -/
def Mode.takeoff_stop  : PMem.M Unit := do
  Mode._TakeOff.stop (0xede8 : UInt64) /- &Mode::takeoff -/
  return ()

/-- C++ `Copter::exit_mode : void (Mode *&, Mode *&)`, `mode.cpp:516-546`. -/
def Copter.exit_mode (this : UInt64) (old_flightmode : UInt64) (new_flightmode : UInt64) : PMem.M Unit := do
  let t'1 ← PMem.ldU64 old_flightmode
  let t'2 ← vcall'Mode'has_manual_throttle'3 t'1
  let mut sc'5 := t'2
  if sc'5 then
    let t'3 ← PMem.ldU64 new_flightmode
    let t'4 ← vcall'Mode'has_manual_throttle'3 t'3
    sc'5 := !t'4
  let mut sc'8 := sc'5
  if sc'8 then
    let t'6 ← PMem.ldU64 (this + 9528)
    let t'7 ← AP_Motors.armed t'6
    sc'8 := t'7
  let mut sc'10 := sc'8
  if sc'10 then
    let t'9 ← PMem.ldB ((this + 9448) + 7)
    sc'10 := !t'9
  if sc'10 then
    Copter.set_accel_throttle_I_from_pilot_throttle this
  Mode.takeoff_stop
  let t'11 ← PMem.ldU64 old_flightmode
  vcall'Mode'exit'10 t'11
  return ()

/-- C++ `ModeAuto::init : bool (bool)`, `mode_auto.cpp:23-74`. -/
def ModeAuto.init.body (fp : UInt64) (this : UInt64) (ignore_checks : Bool) : PMem.M Bool := do
  let mut ignore_checks := ignore_checks
  PMem.stB (this + 861) false
  let t'1 ← AP_Mission.present (this + 112)
  if (t'1 || ignore_checks) then
    let t'2 ← PMem.ldU64 (this + 64)
    let t'3 ← PMem.ldU64 t'2
    let t'4 ← AP_Motors.armed t'3
    let mut sc'6 := t'4
    if sc'6 then
      let t'5 ← PMem.ldB (((0x86d8 : UInt64) /- &copter -/ + 9448) + 7)
      sc'6 := t'5
    let mut sc'8 := sc'6
    if sc'8 then
      let t'7 ← AP_Mission.starts_with_takeoff_cmd (this + 112)
      sc'8 := !t'7
    if sc'8 then
      let t'9 ← Mode.gcs this
      GCS.send_text t'9 (2 : UInt32) (0x1491b : UInt64) /- "Auto: Missing Takeoff Cmd" -/ (fp + 0)
      return false
    PMem.stU8 (this + 820) (0 : UInt8)
    let t'10 ← Mode.AutoYaw.mode (0xeb78 : UInt64) /- &Mode::auto_yaw -/
    if (t'10 == (2 : Int32)) then
      Mode.AutoYaw.set_mode (0xeb78 : UInt64) /- &Mode::auto_yaw -/ (0 : Int32)
    Vector3'double.Vector3 (fp + 32)
    Vector3'double.Vector3'2 (fp + 8) (fp + 32)
    let t'11 ← PMem.ldU64 (this + 24)
    let t'12 ← PMem.ldU64 t'11
    AC_WPNav.wp_and_spline_init_m t'12 (Binary32.ofBits 0x00000000 /- 0 -/) (fp + 8)
    PMem.stF32 ((fp + 56) + 0) (Int32.toBinary32 ((0 : Int32)))
    PMem.stF32 ((fp + 56) + 4) (Int32.toBinary32 ((0 : Int32)))
    PMem.stF32 ((fp + 56) + 8) (Int32.toBinary32 ((0 : Int32)))
    discard <| PMem.memcpy (this + 880) (fp + 56) 12
    discard <| pure ((this + 880))
    discard <| PMem.memset ((fp + 72) + 0) 0 4
    discard <| PMem.memset ((fp + 72) + 4) 0 4
    discard <| PMem.memset ((fp + 72) + 8) 0 2
    discard <| PMem.memset ((fp + 72) + 12) 0 4
    discard <| PMem.memset ((fp + 72) + 16) 0 4
    discard <| PMem.memcpy (this + 892) (fp + 72) 20
    discard <| pure ((this + 892))
    PMem.stB (this + 860) true
    for _ in [0:1] do
      let t'13 ← AP_Mission_ChangeDetector.check_for_mission_change (this + 728)
      if t'13 then
        pure ()
    ModeGuided.limit_clear ((0x86d8 : UInt64) /- &copter -/ + 12520)
    PMem.stB (((0x86d8 : UInt64) /- &copter -/ + 9448) + 19) false
    return true
  else
    return false

def ModeAuto.init (this : UInt64) (ignore_checks : Bool) : PMem.M Bool := do
  let fp ← PMem.enter 92
  let r ← ModeAuto.init.body fp this ignore_checks
  PMem.leave fp
  return r

/-- C++ `GCS_MAVLINK_Copter::handle_MAV_CMD_DO_CHANGE_SPEED : MAV_RESULT (const mavlink_command_int_t &)`, `GCS_MAVLink_Copter.cpp:633-662`. -/
def GCS_MAVLINK_Copter.handle_MAV_CMD_DO_CHANGE_SPEED (this : UInt64) (packet : UInt64) : PMem.M UInt32 := do
  let t'1 ← PMem.ldF32 (packet + 4)
  let t'2 ← is_positive'float t'1
  if !t'2 then
    return (2 : UInt32)
  let t'3 ← PMem.ldF32 (packet + 4)
  let mut speed_ms : Binary32 := t'3
  let mut success : Bool := false
  let t'4 ← PMem.ldF32 packet
  let sw'5 := UInt32.toInt32 ((Binary32.toUInt32 (t'4)))
  if sw'5 == (4 : Int32) then
    return (2 : UInt32)
  else if sw'5 == (0 : Int32) || sw'5 == (1 : Int32) then
    let t'6 ← PMem.ldU64 ((0x86d8 : UInt64) /- &copter -/ + 9488)
    let t'7 ← vcall'Mode'set_speed_NE_ms'19 t'6 speed_ms
    success := t'7
  else if sw'5 == (2 : Int32) then
    let t'8 ← PMem.ldU64 ((0x86d8 : UInt64) /- &copter -/ + 9488)
    let t'9 ← vcall'Mode'set_speed_up_ms'20 t'8 speed_ms
    success := t'9
  else if sw'5 == (3 : Int32) then
    let t'10 ← PMem.ldU64 ((0x86d8 : UInt64) /- &copter -/ + 9488)
    let t'11 ← vcall'Mode'set_speed_down_ms'21 t'10 speed_ms
    success := t'11
  else
    pure ()
  let mut c'12 : UInt32 := default
  if success then
    c'12 := (0 : UInt32)
  else
    c'12 := (4 : UInt32)
  return c'12

/-- C++ `GCS_MAVLINK_Copter::handle_command_pause_continue : MAV_RESULT (const mavlink_command_int_t &)`, `GCS_MAVLink_Copter.cpp:815-835`. -/
def GCS_MAVLINK_Copter.handle_command_pause_continue.body (fp : UInt64) (this : UInt64) (packet : UInt64) : PMem.M UInt32 := do
  let t'1 ← PMem.ldF32 packet
  if ((UInt32.toInt32 (UInt8.toUInt32 ((Binary32.toUInt8 (t'1))))) == (0 : Int32)) then
    let t'2 ← PMem.ldU64 ((0x86d8 : UInt64) /- &copter -/ + 9488)
    let t'3 ← vcall'Mode'pause'22 t'2
    if t'3 then
      return (0 : UInt32)
    GCS_MAVLINK.send_text this (6 : UInt32) (0x13ff8 : UInt64) /- "Failed to pause" -/ (fp + 0)
    return (4 : UInt32)
  let t'4 ← PMem.ldF32 packet
  if ((UInt32.toInt32 (UInt8.toUInt32 ((Binary32.toUInt8 (t'4))))) == (1 : Int32)) then
    let t'5 ← PMem.ldU64 ((0x86d8 : UInt64) /- &copter -/ + 9488)
    let t'6 ← vcall'Mode'resume'23 t'5
    if t'6 then
      return (0 : UInt32)
    GCS_MAVLINK.send_text this (6 : UInt32) (0x14008 : UInt64) /- "Failed to resume" -/ (fp + 8)
    return (4 : UInt32)
  return (2 : UInt32)

def GCS_MAVLINK_Copter.handle_command_pause_continue (this : UInt64) (packet : UInt64) : PMem.M UInt32 := do
  let fp ← PMem.enter 16
  let r ← GCS_MAVLINK_Copter.handle_command_pause_continue.body fp this packet
  PMem.leave fp
  return r

/-- C++ `Mode::do_user_takeoff_U_m : bool (float, bool)`, `takeoff.cpp:18-48`. -/
def Mode.do_user_takeoff_U_m (this : UInt64) (takeoff_alt_m : Binary32) (must_navigate : Bool) : PMem.M Bool := do
  let mut takeoff_alt_m := takeoff_alt_m
  let mut must_navigate := must_navigate
  let t'1 ← PMem.ldU64 ((0x86d8 : UInt64) /- &copter -/ + 9528)
  let t'2 ← AP_Motors.armed t'1
  if !t'2 then
    return false
  let t'3 ← PMem.ldB (((0x86d8 : UInt64) /- &copter -/ + 9448) + 7)
  if !t'3 then
    return false
  let t'4 ← vcall'Mode'has_user_takeoff'24 this must_navigate
  if !t'4 then
    return false
  let t'5 ← PMem.ldI32 (((0x86d8 : UInt64) /- &copter -/ + 11148) + 4)
  if (decide (takeoff_alt_m ≤ ((Int32.toBinary32 (t'5)) * (Binary64.toBinary32 ((Binary64.ofBits 0x3f847ae147ae147b /- 1/100 -/)))))) then
    return false
  let t'6 ← PMem.ldU64 (this + 64)
  let t'7 ← PMem.ldU64 t'6
  let t'8 ← AP_Motors.get_interlock t'7
  let mut sc'10 := !t'8
  if sc'10 then
    let t'9 ← PMem.ldB (((0x86d8 : UInt64) /- &copter -/ + 9448) + 18)
    sc'10 := t'9
  if sc'10 then
    return false
  let t'11 ← vcall'Mode'do_user_takeoff_start_m'25 this takeoff_alt_m
  if !t'11 then
    return false
  Copter.set_auto_armed (0x86d8 : UInt64) /- &copter -/ true
  return true

/-- C++ `GCS_MAVLINK_Copter::handle_MAV_CMD_NAV_TAKEOFF : MAV_RESULT (const mavlink_command_int_t &)`, `GCS_MAVLink_Copter.cpp:580-599`. -/
def GCS_MAVLINK_Copter.handle_MAV_CMD_NAV_TAKEOFF (this : UInt64) (packet : UInt64) : PMem.M UInt32 := do
  let t'1 ← PMem.ldU8 (packet + 32)
  if ((UInt32.toInt32 (UInt8.toUInt32 (t'1))) != (UInt32.toInt32 ((3 : UInt32)))) then
    return (2 : UInt32)
  let t'2 ← PMem.ldF32 (packet + 24)
  let mut takeoff_alt_m : Binary32 := t'2
  let t'3 ← PMem.ldF32 (packet + 8)
  let mut must_navigate : Bool := (((Binary32.toUInt32 (t'3)) &&& (1 : UInt32)) == (Int32.toUInt32 ((0 : Int32))))
  let t'4 ← PMem.ldU64 ((0x86d8 : UInt64) /- &copter -/ + 9488)
  let t'5 ← Mode.do_user_takeoff_U_m t'4 takeoff_alt_m must_navigate
  if !t'5 then
    return (4 : UInt32)
  return (0 : UInt32)

/-- C++ `GCS_MAVLINK_Copter::get_target_location : bool (Location &) const`, `GCS_MAVLink_Copter.cpp:109-112`. -/
def GCS_MAVLINK_Copter.get_target_location (this : UInt64) (target : UInt64) : PMem.M Bool := do
  let t'1 ← PMem.ldU64 ((0x86d8 : UInt64) /- &copter -/ + 9488)
  let t'2 ← vcall'Mode'get_wp'16 t'1 target
  return t'2

/-- C++ `GCS_MAVLINK_Copter::landed_state : MAV_LANDED_STATE () const`, `GCS_MAVLink_Copter.cpp:1245-1257`. -/
def GCS_MAVLINK_Copter.landed_state (this : UInt64) : PMem.M UInt32 := do
  let t'1 ← PMem.ldB (((0x86d8 : UInt64) /- &copter -/ + 9448) + 7)
  if t'1 then
    return (1 : UInt32)
  let t'2 ← PMem.ldU64 ((0x86d8 : UInt64) /- &copter -/ + 9488)
  let t'3 ← vcall'Mode'is_landing'15 t'2
  if t'3 then
    return (4 : UInt32)
  let t'4 ← PMem.ldU64 ((0x86d8 : UInt64) /- &copter -/ + 9488)
  let t'5 ← vcall'Mode'is_taking_off'17 t'4
  if t'5 then
    return (3 : UInt32)
  return (2 : UInt32)

/-- C++ `GCS_Copter::new_gcs_mavlink_backend : GCS_MAVLINK_Copter *(AP_HAL::UARTDriver &)`, `GCS.h:42-44`. -/
def GCS_Copter.new_gcs_mavlink_backend (this : UInt64) (uart : UInt64) : PMem.M UInt64 := do
  let t'1 ← PMem.alloc 880
  GCS_MAVLINK.GCS_MAVLINK t'1 uart
  return t'1

/-- C++ `Copter::load_parameters : void ()`, `Parameters.cpp:1271-1384`. -/
def Copter.load_parameters.body (fp : UInt64) (this : UInt64) : PMem.M Unit := do
  AP_Vehicle.load_parameters this (this + 6776) (120 : UInt16)
  AP_Param.convert_g2_objects (this + 6840) (0xbfa0 : UInt64) /- &Copter::load_parameters(...)::g2_conversions -/ (UInt64.toUInt8 (((0 : UInt64) / (24 : UInt64))))
  AP_Param.convert_toplevel_objects (0xbfa8 : UInt64) /- &Copter::load_parameters(...)::toplevel_conversions -/ (UInt64.toUInt8 (((24 : UInt64) / (24 : UInt64))))
  PMem.stU16 (((fp + 0) + 0) + 0) (UInt32.toUInt16 ((112 : UInt32)))
  PMem.stU32 (((fp + 0) + 0) + 4) (Int32.toUInt32 ((0 : Int32)))
  PMem.stU32 (((fp + 0) + 0) + 8) (2 : UInt32)
  PMem.stU64 (((fp + 0) + 0) + 16) (0x1435d : UInt64) /- "MAV_SYSID" -/
  PMem.stU16 (((fp + 0) + 24) + 0) (UInt32.toUInt16 ((113 : UInt32)))
  PMem.stU32 (((fp + 0) + 24) + 4) (Int32.toUInt32 ((0 : Int32)))
  PMem.stU32 (((fp + 0) + 24) + 8) (2 : UInt32)
  PMem.stU64 (((fp + 0) + 24) + 16) (0x14367 : UInt64) /- "MAV_GCS_SYSID" -/
  PMem.stU16 (((fp + 0) + 48) + 0) (UInt32.toUInt16 ((6 : UInt32)))
  PMem.stU32 (((fp + 0) + 48) + 4) (Int32.toUInt32 ((11 : Int32)))
  PMem.stU32 (((fp + 0) + 48) + 8) (1 : UInt32)
  PMem.stU64 (((fp + 0) + 48) + 16) (0x14375 : UInt64) /- "MAV_OPTIONS" -/
  PMem.stU16 (((fp + 0) + 72) + 0) (UInt32.toUInt16 ((115 : UInt32)))
  PMem.stU32 (((fp + 0) + 72) + 4) (Int32.toUInt32 ((0 : Int32)))
  PMem.stU32 (((fp + 0) + 72) + 8) (1 : UInt32)
  PMem.stU64 (((fp + 0) + 72) + 16) (0x14381 : UInt64) /- "MAV_TELEM_DELAY" -/
  AP_Param.convert_old_parameters ((fp + 0) + ((Int32.toInt64 ((0 : Int32))) * 24).toUInt64) (UInt64.toUInt8 (((96 : UInt64) / (24 : UInt64)))) (Int8.toUInt8 (Int32.toInt8 ((0 : Int32))))
  ModeRTL.convert_params ((0x86d8 : UInt64) /- &copter -/ + 12888)
  ModeLand.convert_params ((0x86d8 : UInt64) /- &copter -/ + 12640)
  AP_Param.convert_old_parameters_scaled (0xbfc0 : UInt64) /- &Copter::load_parameters(...)::pilot_conversion_info -/ (UInt64.toUInt8 (((96 : UInt64) / (24 : UInt64)))) (Binary64.toBinary32 ((Binary64.ofBits 0x3f847ae147ae147b /- 1/100 -/))) (Int8.toUInt8 (Int32.toInt8 ((0 : Int32))))
  AP_Param.set_frame_type_flags (Int16.toUInt16 (Int32.toInt16 (((1 : Int32) <<< (0 : Int32)))))
  return ()

def Copter.load_parameters (this : UInt64) : PMem.M Unit := do
  let fp ← PMem.enter 96
  let r ← Copter.load_parameters.body fp this
  PMem.leave fp
  return r

/-- C++ `Copter::init_rc_out : void ()`, `radio.cpp:54-89`. -/
def Copter.init_rc_out (this : UInt64) : PMem.M Unit := do
  let t'1 ← AP_ParamTBase'signed_char_1.get ((this + 6840) + 12)
  let t'2 ← PMem.ldI8 t'1
  let t'3 ← AP_ParamTBase'signed_char_1.get ((this + 6776) + 49)
  let t'4 ← PMem.ldI8 t'3
  let t'5 ← PMem.ldU64 (this + 9528)
  AP_MotorsMatrix.init t'5 (Int32.toUInt32 (Int8.toInt32 (t'2))) (Int32.toUInt32 (Int8.toInt32 (t'4)))
  let t'6 ← AP.srv
  SRV_Channels.enable_aux_servos t'6
  let t'7 ← AP_ParamT'short_2.operator_const_short__ ((this + 6776) + 62)
  let t'8 ← PMem.ldI16 t'7
  let t'9 ← PMem.ldU64 (this + 9528)
  AP_MotorsMatrix.set_update_rate t'9 (Int16.toUInt16 (t'8))
  let t'10 ← PMem.ldU64 (this + 8616)
  let t'11 ← RC_Channel.configured t'10
  if t'11 then
    let t'12 ← PMem.ldU64 (this + 8616)
    let t'13 ← RC_Channel.get_radio_min t'12
    let t'14 ← PMem.ldU64 (this + 8616)
    let t'15 ← RC_Channel.get_radio_max t'14
    let t'16 ← PMem.ldU64 (this + 9528)
    AP_MotorsMulticopter.convert_pwm_min_max_param t'16 t'13 t'15
  else
    let t'17 ← PMem.ldU64 (this + 9528)
    AP_MotorsMulticopter.convert_pwm_min_max_param t'17 (Int32.toInt16 ((1000 : Int32))) (Int32.toInt16 ((2000 : Int32)))
  let t'18 ← PMem.ldU64 (this + 9528)
  AP_MotorsMulticopter.update_throttle_range t'18
  SRV_Channels.update_aux_servo_function
  let t'19 ← PMem.ldU64 ((0x86d8 : UInt64) /- &copter -/ + 9528)
  let t'20 ← AP_MotorsMatrix.get_motor_mask t'19
  let mut safety_ignore_mask : UInt16 := UInt32.toUInt16 (((~~~t'20) &&& (Int32.toUInt32 ((16383 : Int32)))))
  AP_BoardConfig.set_default_safety_ignore_mask (this + 8) (UInt16.toUInt32 (safety_ignore_mask))
  return ()

/-- C++ `Copter::failsafe_radio_off_event : void ()`, `events.cpp:82-88`. -/
def Copter.failsafe_radio_off_event.body (fp : UInt64) (this : UInt64) : PMem.M Unit := do
  let t'1 ← Copter.gcs this
  GCS.send_text t'1 (4 : UInt32) (0x146d7 : UInt64) /- "Radio Failsafe Cleared" -/ (fp + 0)
  return ()

def Copter.failsafe_radio_off_event (this : UInt64) : PMem.M Unit := do
  let fp ← PMem.enter 8
  let r ← Copter.failsafe_radio_off_event.body fp this
  PMem.leave fp
  return r

/-- C++ `Copter::announce_failsafe : void (const char *, const char *)`, `events.cpp:90-97`. -/
def Copter.announce_failsafe.body (fp : UInt64) (this : UInt64) (type' : UInt64) (action_undertaken : UInt64) : PMem.M Unit := do
  let mut type' := type'
  let mut action_undertaken := action_undertaken
  if (action_undertaken != (0 : UInt64)) then
    PMem.stU64 (fp + 0) type'
    PMem.stU64 (fp + 8) action_undertaken
    let t'1 ← Copter.gcs this
    GCS.send_text t'1 (4 : UInt32) (0x146ee : UInt64) /- "%s Failsafe - %s" -/ (fp + 0)
  else
    PMem.stU64 (fp + 16) type'
    let t'2 ← Copter.gcs this
    GCS.send_text t'2 (4 : UInt32) (0x146ff : UInt64) /- "%s Failsafe" -/ (fp + 16)
  return ()

def Copter.announce_failsafe (this : UInt64) (type' : UInt64) (action_undertaken : UInt64) : PMem.M Unit := do
  let fp ← PMem.enter 24
  let r ← Copter.announce_failsafe.body fp this type' action_undertaken
  PMem.leave fp
  return r

/-- C++ `Copter::esc_calibration_setup : void ()`, `esc_calibration.cpp:153-185`. -/
def Copter.esc_calibration_setup.body (fp : UInt64) (this : UInt64) : PMem.M Unit := do
  PMem.stI8 (fp + 0) (UInt8.toInt8 ((0 : UInt8)))
  AP_ParamTBase'signed_char_1.set_and_save ((this + 6776) + 48) (fp + 0)
  let t'1 ← PMem.ldU64 (this + 9528)
  let t'2 ← AP_Motors.is_normal_pwm_type t'1
  if t'2 then
    let t'3 ← AP_ParamT'short_2.operator_const_short__ ((this + 6776) + 62)
    let t'4 ← PMem.ldI16 t'3
    let t'5 ← PMem.ldU64 (this + 9528)
    AP_MotorsMatrix.set_update_rate t'5 (Int16.toUInt16 (t'4))
  else
    let t'6 ← PMem.ldU64 (this + 9528)
    AP_MotorsMatrix.set_update_rate t'6 (Int16.toUInt16 (Int32.toInt16 ((50 : Int32))))
  AP_BoardConfig.init_safety (this + 8)
  let mut tstart : UInt32 := Int32.toUInt32 ((0 : Int32))
  for _ in PMem.loopFuel do
    let t'7 ← PMem.ldU64 ((0xba88 : UInt64) /- &hal -/ + 88)
    let t'8 ← PMem.halDev "AP_HAL::Util::safety_switch_state" t'7 #[]
    if !(((UInt32.toInt32 (UInt8.toUInt32 ((UInt64.toUInt8 (t'8))))) == (UInt32.toInt32 (UInt8.toUInt32 ((1 : UInt8)))))) then break
    let mut tnow : UInt32 := ((← PMem.clock) / 1000).toUInt32
    if (decide ((tnow - tstart) ≥ (Int32.toUInt32 ((5000 : Int32))))) then
      let t'9 ← Copter.gcs this
      GCS.send_text t'9 (6 : UInt32) (0x14659 : UInt64) /- "ESC calibration: Push safety switch" -/ (fp + 8)
      tstart := tnow
    Copter.esc_calibration_notify this
    let t'10 ← PMem.ldU64 ((0xba88 : UInt64) /- &hal -/ + 80)
    discard <| PMem.hal "AP_HAL::Scheduler::delay" t'10 #[(UInt16.toUInt64 ((Int16.toUInt16 (Int32.toInt16 ((3 : Int32))))))]
  let t'11 ← PMem.ldU64 (this + 9528)
  AP_Motors.armed'2 t'11 true
  let t'12 ← PMem.ldU64 (this + 9528)
  let t'13 ← AP_MotorsMatrix.get_motor_mask t'12
  SRV_Channels.enable_by_mask t'13
  let t'14 ← PMem.ldU64 ((0xba88 : UInt64) /- &hal -/ + 88)
  discard <| PMem.halDev "AP_HAL::Util::set_soft_armed" t'14 #[(if true then (1 : UInt64) else 0)]
  return ()

def Copter.esc_calibration_setup (this : UInt64) : PMem.M Unit := do
  let fp ← PMem.enter 16
  let r ← Copter.esc_calibration_setup.body fp this
  PMem.leave fp
  return r

/-- C++ `Copter::esc_calibration_auto : void ()`, `esc_calibration.cpp:107-140`. -/
def Copter.esc_calibration_auto.body (fp : UInt64) (this : UInt64) : PMem.M Unit := do
  let t'1 ← Copter.gcs this
  GCS.send_text t'1 (6 : UInt32) (0x14637 : UInt64) /- "ESC calibration: Auto calibration" -/ (fp + 0)
  Copter.esc_calibration_setup this
  let t'2 ← AP.srv
  let srv : UInt64 := t'2
  SRV_Channels.cork srv
  let t'3 ← PMem.ldU64 (this + 9528)
  AP_MotorsMulticopter.set_throttle_passthrough_for_esc_calibration t'3 (Binary32.ofBits 0x3f800000 /- 1 -/)
  SRV_Channels.push srv
  let mut tstart : UInt32 := ((← PMem.clock) / 1000).toUInt32
  for _ in PMem.loopFuel do
    if !((decide (((((← PMem.clock) / 1000).toUInt32) - tstart) < (Int32.toUInt32 ((5000 : Int32)))))) then break
    SRV_Channels.cork srv
    let t'4 ← PMem.ldU64 (this + 9528)
    AP_MotorsMulticopter.set_throttle_passthrough_for_esc_calibration t'4 (Binary32.ofBits 0x3f800000 /- 1 -/)
    SRV_Channels.push srv
    Copter.esc_calibration_notify this
    let t'5 ← PMem.ldU64 ((0xba88 : UInt64) /- &hal -/ + 80)
    discard <| PMem.hal "AP_HAL::Scheduler::delay" t'5 #[(UInt16.toUInt64 ((Int16.toUInt16 (Int32.toInt16 ((3 : Int32))))))]
  for _ in PMem.loopFuel do
    if !((1 : Int32) != (0 : Int32)) then break
    SRV_Channels.cork srv
    let t'6 ← PMem.ldU64 (this + 9528)
    AP_MotorsMulticopter.set_throttle_passthrough_for_esc_calibration t'6 (Binary32.ofBits 0x00000000 /- 0 -/)
    SRV_Channels.push srv
    Copter.esc_calibration_notify this
    let t'7 ← PMem.ldU64 ((0xba88 : UInt64) /- &hal -/ + 80)
    discard <| PMem.hal "AP_HAL::Scheduler::delay" t'7 #[(UInt16.toUInt64 ((Int16.toUInt16 (Int32.toInt16 ((3 : Int32))))))]
  return ()

def Copter.esc_calibration_auto (this : UInt64) : PMem.M Unit := do
  let fp ← PMem.enter 8
  let r ← Copter.esc_calibration_auto.body fp this
  PMem.leave fp
  return r

/-- C++ `Copter::startup_INS_ground : void ()`, `system.cpp:201-212`. -/
def Copter.startup_INS_ground (this : UInt64) : PMem.M Unit := do
  VehicleBridge.AP_AHRS.init'0 (this + 4080)
  VehicleBridge.AP_AHRS.set_vehicle_class'1 (this + 4080) (2 : UInt8)
  let t'1 ← AP_Scheduler.get_loop_rate_hz (this + 208)
  VehicleBridge.AP_InertialSensor.init'1 (this + 2344) t'1
  worldOutputs'drain
  VehicleBridge.AP_AHRS.reset'0 (this + 4080)
  worldOutputs'drain
  return ()

/-- C++ `Copter::motor_test_stop : void ()`, `motor_test.cpp:194-225`. -/
def Copter.motor_test_stop.body (fp : UInt64) (this : UInt64) : PMem.M Unit := do
  let t'1 ← PMem.ldB ((this + 9448) + 12)
  if !t'1 then
    return ()
  let t'2 ← Copter.gcs this
  GCS.send_text t'2 (6 : UInt32) (0x14d32 : UInt64) /- "finished motor test" -/ (fp + 0)
  let t'3 ← PMem.ldU64 (this + 9528)
  AP_Motors.armed'2 t'3 false
  let t'4 ← PMem.ldU64 ((0xba88 : UInt64) /- &hal -/ + 88)
  discard <| PMem.halDev "AP_HAL::Util::set_soft_armed" t'4 #[(if false then (1 : UInt64) else 0)]
  let t'5 := Int32.toUInt32 ((0 : Int32))
  PMem.stU32 (0x13638 : UInt64) /- &motor_test_start_ms -/ t'5
  let t'6 := Int32.toUInt32 ((0 : Int32))
  PMem.stU32 (0x13640 : UInt64) /- &motor_test_timeout_ms -/ t'6
  let t'7 ← AP_Param.load ((this + 6776) + 26)
  discard <| pure (t'7)
  let t'8 ← AP_Param.load ((this + 6776) + 21)
  discard <| pure (t'8)
  let t'9 ← AP_Param.load ((this + 6776) + 52)
  discard <| pure (t'9)
  let t'10 ← PMem.ldU8 (0x13658 : UInt64) /- &motor_test_throttle_type -/
  if ((UInt32.toInt32 (UInt8.toUInt32 (t'10))) == (UInt32.toInt32 ((3 : UInt32)))) then
    VehicleBridge.Compass.per_motor_calibration_end'0 (this + 1512)
  PMem.stB ((0xccc0 : UInt64) /- &AP_Notify::flags -/ + 9) false
  PMem.stB ((this + 9448) + 12) false
  return ()

def Copter.motor_test_stop (this : UInt64) : PMem.M Unit := do
  let fp ← PMem.enter 8
  let r ← Copter.motor_test_stop.body fp this
  PMem.leave fp
  return r

/-- C++ `Copter::motor_test_output : void ()`, `motor_test.cpp:19-96`. -/
def Copter.motor_test_output.body (fp : UInt64) (this : UInt64) : PMem.M Unit := do
  let t'1 ← PMem.ldB ((this + 9448) + 12)
  if !t'1 then
    return ()
  ExpectDelay.ExpectDelay (fp + 0) (Int32.toUInt32 ((2000 : Int32)))
  let mut now : UInt32 := ((← PMem.clock) / 1000).toUInt32
  let t'2 ← PMem.ldU32 (0x13638 : UInt64) /- &motor_test_start_ms -/
  let t'3 ← PMem.ldU32 (0x13640 : UInt64) /- &motor_test_timeout_ms -/
  if (decide ((now - t'2) ≥ t'3)) then
    let t'4 ← PMem.ldU8 (0x13648 : UInt64) /- &motor_test_count -/
    if (decide ((UInt32.toInt32 (UInt8.toUInt32 (t'4))) > (1 : Int32))) then
      let t'5 ← PMem.ldU32 (0x13638 : UInt64) /- &motor_test_start_ms -/
      let t'6 ← PMem.ldU32 (0x13640 : UInt64) /- &motor_test_timeout_ms -/
      if (decide ((UInt32.toBinary32 ((now - t'5))) < ((UInt32.toBinary32 (t'6)) * (Binary64.toBinary32 ((Binary64.ofBits 0x3ff8000000000000 /- 3/2 -/)))))) then
        let t'7 ← PMem.ldU64 (this + 9528)
        AP_MotorsMulticopter.output_min t'7
      else
        let t'8 := (0x13650 : UInt64) /- &motor_test_seq -/
        let t'9 ← PMem.ldU8 t'8
        let t'10 := (t'9 + 1)
        PMem.stU8 t'8 t'10
        let t'11 := (0x13648 : UInt64) /- &motor_test_count -/
        let t'12 ← PMem.ldU8 t'11
        let t'13 := (t'12 - 1)
        PMem.stU8 t'11 t'13
        PMem.stU32 (0x13638 : UInt64) /- &motor_test_start_ms -/ now
        let t'14 ← PMem.ldU64 (this + 9528)
        let t'15 ← AP_Motors.armed t'14
        if !t'15 then
          let t'16 ← PMem.ldU64 (this + 9528)
          AP_Motors.armed'2 t'16 true
          let t'17 ← PMem.ldU64 ((0xba88 : UInt64) /- &hal -/ + 88)
          discard <| PMem.halDev "AP_HAL::Util::set_soft_armed" t'17 #[(if true then (1 : UInt64) else 0)]
      return ()
    Copter.motor_test_stop this
  else
    let mut pwm : Int16 := Int32.toInt16 ((0 : Int32))
    let t'18 ← PMem.ldU8 (0x13658 : UInt64) /- &motor_test_throttle_type -/
    let sw'19 := UInt32.toInt32 (UInt8.toUInt32 (t'18))
    if sw'19 == (3 : Int32) then
      let t'20 ← AP_BattMonitor.voltage'2 (this + 9584)
      VehicleBridge.Compass.set_voltage'1 (this + 1512) t'20
      VehicleBridge.Compass.per_motor_calibration_update'0 (this + 1512)
      let t'21 ← PMem.ldF32 (0x13660 : UInt64) /- &motor_test_throttle_value -/
      if (decide (t'21 ≤ (Int32.toBinary32 ((100 : Int32))))) then
        let t'22 ← PMem.ldU64 (this + 9528)
        let t'23 ← AP_MotorsMulticopter.get_pwm_output_min t'22
        let mut pwm_min : Int16 := t'23
        let t'24 ← PMem.ldU64 (this + 9528)
        let t'25 ← AP_MotorsMulticopter.get_pwm_output_max t'24
        let mut pwm_max : Int16 := t'25
        let t'26 ← PMem.ldF32 (0x13660 : UInt64) /- &motor_test_throttle_value -/
        let t'27 := Binary32.toInt16 (((Int32.toBinary32 ((Int16.toInt32 (pwm_min)))) + (((Int32.toBinary32 (((Int16.toInt32 (pwm_max)) - (Int16.toInt32 (pwm_min))))) * t'26) * (Binary32.ofBits 0x3c23d70a /- 999999977/100000000000 -/))))
        pwm := t'27
    else if sw'19 == (0 : Int32) then
      let t'28 ← PMem.ldF32 (0x13660 : UInt64) /- &motor_test_throttle_value -/
      if (decide (t'28 ≤ (Int32.toBinary32 ((100 : Int32))))) then
        let t'29 ← PMem.ldU64 (this + 9528)
        let t'30 ← AP_MotorsMulticopter.get_pwm_output_min t'29
        let mut pwm_min'2 : Int16 := t'30
        let t'31 ← PMem.ldU64 (this + 9528)
        let t'32 ← AP_MotorsMulticopter.get_pwm_output_max t'31
        let mut pwm_max'2 : Int16 := t'32
        let t'33 ← PMem.ldF32 (0x13660 : UInt64) /- &motor_test_throttle_value -/
        let t'34 := Binary32.toInt16 (((Int32.toBinary32 ((Int16.toInt32 (pwm_min'2)))) + (((Int32.toBinary32 (((Int16.toInt32 (pwm_max'2)) - (Int16.toInt32 (pwm_min'2))))) * t'33) * (Binary32.ofBits 0x3c23d70a /- 999999977/100000000000 -/))))
        pwm := t'34
    else if sw'19 == (1 : Int32) then
      let t'35 ← PMem.ldF32 (0x13660 : UInt64) /- &motor_test_throttle_value -/
      let t'36 := Binary32.toInt16 (t'35)
      pwm := t'36
    else if sw'19 == (2 : Int32) then
      let t'37 ← PMem.ldU64 (this + 8616)
      let t'38 ← RC_Channel.get_radio_in t'37
      pwm := t'38
    else
      Copter.motor_test_stop this
      return ()
    if ((decide ((Int16.toInt32 (pwm)) < (UInt32.toInt32 (UInt16.toUInt32 ((800 : UInt16)))))) || (decide ((Int16.toInt32 (pwm)) > (UInt32.toInt32 (UInt16.toUInt32 ((2200 : UInt16))))))) then
      Copter.motor_test_stop this
      return ()
    let t'39 ← PMem.ldU8 (0x13650 : UInt64) /- &motor_test_seq -/
    let t'40 ← PMem.ldU64 (this + 9528)
    let t'41 ← AP_Motors.output_test_seq t'40 t'39 pwm
    if !t'41 then
      let t'42 ← Copter.gcs this
      GCS.send_text t'42 (6 : UInt32) (0x14cb2 : UInt64) /- "Motor Test: cancelled" -/ (fp + 8)
      Copter.motor_test_stop this
  return ()

def Copter.motor_test_output (this : UInt64) : PMem.M Unit := do
  let fp ← PMem.enter 16
  let r ← Copter.motor_test_output.body fp this
  PMem.leave fp
  return r

/-- C++ `Copter::compassmot_output : void ()`, `compassmot.cpp:286-297`. -/
def Copter.compassmot_output (this : UInt64) : PMem.M Unit := do
  let t'1 ← PMem.ldU64 (this + 9528)
  let t'2 ← AP_Motors.armed t'1
  if !t'2 then
    let t'3 ← PMem.ldU64 (this + 9528)
    AP_MotorsMulticopter.output_min t'3
    return ()
  let t'4 ← PMem.ldU64 (this + 8616)
  let t'5 ← RC_Channel.get_control_in t'4
  let t'6 ← PMem.ldU64 (this + 9528)
  AP_MotorsMulticopter.set_throttle_passthrough_for_esc_calibration t'6 ((Int32.toBinary32 ((Int16.toInt32 (t'5)))) * (Binary32.ofBits 0x3a83126f /- 20000001/20000000000 -/))
  return ()

/-- C++ `Mode::output_to_motors : void ()`, `mode.cpp:1017-1020`. -/
def Mode.output_to_motors (this : UInt64) : PMem.M Unit := do
  let t'1 ← PMem.ldU64 (this + 64)
  let t'2 ← PMem.ldU64 t'1
  AP_MotorsMulticopter.output t'2
  return ()

/-- C++ `Copter::read_AHRS : void ()`, `Copter.cpp:882-886`. -/
def Copter.read_AHRS (this : UInt64) : PMem.M Unit := do
  VehicleBridge.AP_AHRS.update'1 (this + 4080) true (AP_Vehicle.get_time_flying_ms (0x86d8 : UInt64) /- &copter -/)
  worldOutputs'drain
  return ()

/-- C++ `Mode::_TakeOff::do_pilot_takeoff_ms : void (float)`, `takeoff.cpp:74-111`. -/
def Mode._TakeOff.do_pilot_takeoff_ms.body (fp : UInt64) (this : UInt64) (pilot_climb_rate_ms : Binary32) : PMem.M Unit := do
  let mut pilot_climb_rate_ms := pilot_climb_rate_ms
  let t'1 ← PMem.ldB this
  if !t'1 then
    return ()
  let t'2 ← PMem.ldB (((0x86d8 : UInt64) /- &copter -/ + 9448) + 7)
  if t'2 then
    let t'3 ← PMem.ldU64 ((0x86d8 : UInt64) /- &copter -/ + 11168)
    let t'4 ← AC_AttitudeControl.get_throttle_in t'3
    let t'5 ← PMem.ldF32 ((0x86d8 : UInt64) /- &copter -/ + 376)
    let t'6 ← AP_ParamT'float_4.operator_const_float__'1 (((0x86d8 : UInt64) /- &copter -/ + 6840) + 1720)
    let t'7 ← PMem.ldF32 t'6
    let t'8 ← constrain_value_line'float (t'4 + (t'5 / t'7)) (Binary64.toBinary32 ((Binary64.ofBits 0x0000000000000000 /- 0 -/))) (Binary64.toBinary32 ((Binary64.ofBits 0x3ff0000000000000 /- 1 -/))) (Int32.toUInt32 ((83 : Int32)))
    let mut throttle_norm : Binary32 := t'8
    let t'9 ← PMem.ldU64 ((0x86d8 : UInt64) /- &copter -/ + 11168)
    AC_AttitudeControl_Multi.set_throttle_out t'9 throttle_norm true (Binary64.toBinary32 ((Binary64.ofBits 0x0000000000000000 /- 0 -/)))
    let t'10 ← PMem.ldU64 ((0x86d8 : UInt64) /- &copter -/ + 11184)
    AC_PosControl.D_init_controller t'10
    PMem.stF32 (fp + 0) (Binary64.toBinary32 ((Binary64.ofBits 0x3feccccccccccccd /- 45000000000000001/50000000000000000 -/)))
    let t'11 ← MIN'AP_ParamT_float_AP_PARAM_FLOAT_float (((0x86d8 : UInt64) /- &copter -/ + 6840) + 1724) (fp + 0)
    let t'12 ← PMem.ldF32 t'11
    let mut sc'17 := (decide (throttle_norm ≥ t'12))
    if !sc'17 then
      let t'13 ← PMem.ldU64 ((0x86d8 : UInt64) /- &copter -/ + 11184)
      let t'14 ← AC_PosControl.get_estimated_accel_U_mss t'13
      let t'15 ← PMem.ldU64 ((0x86d8 : UInt64) /- &copter -/ + 11184)
      let t'16 ← AC_PosControl.D_get_max_accel_mss t'15
      sc'17 := (decide (t'14 ≥ ((Binary64.toBinary32 ((Binary64.ofBits 0x3fe0000000000000 /- 1/2 -/))) * t'16)))
    let mut sc'25 := sc'17
    if !sc'25 then
      let t'18 ← PMem.ldU64 ((0x86d8 : UInt64) /- &copter -/ + 11184)
      let t'19 ← AC_PosControl.get_vel_estimate_U_ms t'18
      let t'20 ← PMem.ldU64 ((0x86d8 : UInt64) /- &copter -/ + 11184)
      let t'21 ← AC_PosControl.get_max_speed_up_ms t'20
      let t'22 ← PMem.ldU64 ((0x86d8 : UInt64) /- &copter -/ + 11184)
      let t'23 ← AC_PosControl.get_max_speed_up_ms t'22
      let t'24 ← constrain_value_line'float pilot_climb_rate_ms (t'21 * (Binary64.toBinary32 ((Binary64.ofBits 0x3fb999999999999a /- 10000000000000001/100000000000000000 -/)))) (t'23 * (Binary64.toBinary32 ((Binary64.ofBits 0x3fe0000000000000 /- 1/2 -/)))) (Int32.toUInt32 ((89 : Int32)))
      sc'25 := (decide (t'19 ≥ t'24))
    let mut sc'35 := sc'25
    if !sc'35 then
      let t'26 ← PMem.ldF32 (this + 8)
      let t'27 ← PMem.ldF32 (this + 4)
      let t'28 ← is_positive'float (t'26 - t'27)
      let mut sc'34 := t'28
      if sc'34 then
        let t'29 ← PMem.ldU64 ((0x86d8 : UInt64) /- &copter -/ + 11184)
        let t'30 ← AC_PosControl.get_pos_estimate_U_m t'29
        let t'31 ← PMem.ldF32 (this + 4)
        let t'32 ← PMem.ldF32 (this + 8)
        let t'33 ← PMem.ldF32 (this + 4)
        sc'34 := (decide ((t'30 - t'31) > ((Binary64.toBinary32 ((Binary64.ofBits 0x3fe0000000000000 /- 1/2 -/))) * (t'32 - t'33))))
      sc'35 := sc'34
    if sc'35 then
      Copter.set_land_complete (0x86d8 : UInt64) /- &copter -/ false
  else
    let t'36 ← PMem.ldF32 (this + 8)
    PMem.stF32 (fp + 8) (-t'36)
    PMem.stF32 (fp + 16) (-pilot_climb_rate_ms)
    let t'37 ← PMem.ldU64 ((0x86d8 : UInt64) /- &copter -/ + 11184)
    AC_PosControl.input_pos_vel_accel_D_m t'37 (fp + 8) (fp + 16) (Binary64.toBinary32 ((Binary64.ofBits 0x0000000000000000 /- 0 -/))) true
    let t'38 ← is_negative'float pilot_climb_rate_ms
    let mut sc'44 := t'38
    if !sc'44 then
      let t'39 ← PMem.ldF32 (this + 8)
      let t'40 ← PMem.ldF32 (this + 4)
      let t'41 ← PMem.ldU64 ((0x86d8 : UInt64) /- &copter -/ + 11184)
      let t'42 ← AC_PosControl.get_pos_desired_U_m t'41
      let t'43 ← PMem.ldF32 (this + 4)
      sc'44 := (decide (((t'39 - t'40) * (Binary32.ofBits 0x3f7fbe77 /- 249750003/250000000 -/)) < (t'42 - t'43)))
    if sc'44 then
      Mode._TakeOff.stop this
  return ()

def Mode._TakeOff.do_pilot_takeoff_ms (this : UInt64) (pilot_climb_rate_ms : Binary32) : PMem.M Unit := do
  let fp ← PMem.enter 20
  let r ← Mode._TakeOff.do_pilot_takeoff_ms.body fp this pilot_climb_rate_ms
  PMem.leave fp
  return r

/-- C++ `ModeAltHold::run : void ()`, `mode_althold.cpp:27-101`. -/
def ModeAltHold.run.body (fp : UInt64) (this : UInt64) : PMem.M Unit := do
  let t'1 ← Mode.get_pilot_speed_dn_ms this
  let t'2 ← Mode.get_pilot_speed_up_ms this
  let t'3 ← Mode.get_pilot_accel_D_mss this
  let t'4 ← PMem.ldU64 (this + 40)
  let t'5 ← PMem.ldU64 t'4
  AC_PosControl.D_set_max_speed_accel_m t'5 t'1 t'2 t'3
  let t'6 ← PMem.ldU64 (this + 56)
  let t'7 ← PMem.ldU64 t'6
  let t'8 ← AC_AttitudeControl.lean_angle_max_rad t'7
  let t'9 ← PMem.ldU64 (this + 56)
  let t'10 ← PMem.ldU64 t'9
  let t'11 ← AC_AttitudeControl.get_althold_lean_angle_max_rad t'10
  Mode.get_pilot_desired_lean_angles_rad this (fp + 0) (fp + 8) t'8 t'11
  let t'12 ← Mode.get_pilot_desired_yaw_rate_rads this
  let mut target_yaw_rate_rads : Binary32 := t'12
  let t'13 ← Mode.get_pilot_desired_climb_rate_ms this
  let mut target_climb_rate_ms : Binary32 := t'13
  let t'14 ← Mode.get_alt_hold_state_D_ms this target_climb_rate_ms
  let mut althold_state : Int32 := t'14
  let sw'15 := althold_state
  if sw'15 == (0 : Int32) then
    let t'16 ← PMem.ldU64 (this + 56)
    let t'17 ← PMem.ldU64 t'16
    AC_AttitudeControl.reset_rate_controller_I_terms t'17
    let t'18 ← PMem.ldU64 (this + 56)
    let t'19 ← PMem.ldU64 t'18
    AC_AttitudeControl.reset_yaw_target_and_rate t'19 false
    let t'20 ← PMem.ldU64 (this + 40)
    let t'21 ← PMem.ldU64 t'20
    AC_PosControl.D_relax_controller t'21 (Binary32.ofBits 0x00000000 /- 0 -/)
  else if sw'15 == (2 : Int32) then
    let t'22 ← PMem.ldU64 (this + 56)
    let t'23 ← PMem.ldU64 t'22
    AC_AttitudeControl.reset_yaw_target_and_rate t'23 true
    let t'24 ← PMem.ldU64 (this + 56)
    let t'25 ← PMem.ldU64 t'24
    AC_AttitudeControl.reset_rate_controller_I_terms_smoothly t'25
    let t'26 ← PMem.ldU64 (this + 40)
    let t'27 ← PMem.ldU64 t'26
    AC_PosControl.D_relax_controller t'27 (Binary32.ofBits 0x00000000 /- 0 -/)
  else if sw'15 == (3 : Int32) then
    let t'28 ← PMem.ldU64 (this + 56)
    let t'29 ← PMem.ldU64 t'28
    AC_AttitudeControl.reset_rate_controller_I_terms_smoothly t'29
    let t'30 ← PMem.ldU64 (this + 40)
    let t'31 ← PMem.ldU64 t'30
    AC_PosControl.D_relax_controller t'31 (Binary32.ofBits 0x00000000 /- 0 -/)
  else if sw'15 == (1 : Int32) then
    let t'32 ← Mode._TakeOff.running (0xede8 : UInt64) /- &Mode::takeoff -/
    if !t'32 then
      let t'33 ← PMem.ldU64 (this + 16)
      let t'34 ← AP_ParamT'float_4.operator_const_float__'1 (t'33 + 1644)
      let t'35 ← PMem.ldF32 t'34
      let t'36 ← constrain_value_line'float t'35 (Binary64.toBinary32 ((Binary64.ofBits 0x0000000000000000 /- 0 -/))) (Binary64.toBinary32 ((Binary64.ofBits 0x4024000000000000 /- 10 -/))) (Int32.toUInt32 ((66 : Int32)))
      Mode._TakeOff.start_m (0xede8 : UInt64) /- &Mode::takeoff -/ t'36
    let t'37 ← Mode.get_avoidance_adjusted_climbrate_ms this target_climb_rate_ms
    target_climb_rate_ms := t'37
    Mode._TakeOff.do_pilot_takeoff_ms (0xede8 : UInt64) /- &Mode::takeoff -/ target_climb_rate_ms
  else if sw'15 == (4 : Int32) then
    let t'38 ← Mode.get_avoidance_adjusted_climbrate_ms this target_climb_rate_ms
    target_climb_rate_ms := t'38
    let t'39 ← PMem.ldU64 (this + 40)
    let t'40 ← PMem.ldU64 t'39
    AC_PosControl.D_set_pos_target_from_climb_rate_ms t'40 target_climb_rate_ms false
  else
    pure ()
  let t'41 ← PMem.ldF32 (fp + 0)
  let t'42 ← PMem.ldF32 (fp + 8)
  let t'43 ← PMem.ldU64 (this + 56)
  let t'44 ← PMem.ldU64 t'43
  AC_AttitudeControl.input_euler_angle_roll_pitch_euler_rate_yaw_rad t'44 t'41 t'42 target_yaw_rate_rads
  let t'45 ← PMem.ldU64 (this + 40)
  let t'46 ← PMem.ldU64 t'45
  AC_PosControl.D_update_controller t'46
  return ()

def ModeAltHold.run (this : UInt64) : PMem.M Unit := do
  let fp ← PMem.enter 12
  let r ← ModeAltHold.run.body fp this
  PMem.leave fp
  return r

/-- C++ `ModeAuto::verify_nav_wp : bool (const AP_Mission::Mission_Command &)`, `mode_auto.cpp:2297-2323`. -/
def ModeAuto.verify_nav_wp.body (fp : UInt64) (this : UInt64) (cmd : UInt64) : PMem.M Bool := do
  let t'1 ← PMem.ldU64 ((0x86d8 : UInt64) /- &copter -/ + 11192)
  let t'2 ← AC_WPNav.reached_wp_destination t'1
  if !t'2 then
    return false
  let t'3 ← PMem.ldU32 (this + 824)
  if (t'3 == (Int32.toUInt32 ((0 : Int32)))) then
    let t'4 := ((← PMem.clock) / 1000).toUInt32
    PMem.stU32 (this + 824) t'4
    let t'5 ← PMem.ldU16 (this + 822)
    if (decide ((UInt32.toInt32 (UInt16.toUInt32 (t'5))) > (0 : Int32))) then
      let t'6 := Int32.toUInt32 ((1 : Int32))
      PMem.stBits (0xce38 : UInt64) /- &AP_Notify::events -/ 8 1 (UInt32.toUInt64 (t'6))
  let t'7 ← PMem.ldU32 (this + 824)
  let t'8 ← PMem.ldU16 (this + 822)
  if (decide ((((((← PMem.clock) / 1000).toUInt32) - t'7) / (Int32.toUInt32 ((1000 : Int32)))) ≥ (UInt16.toUInt32 (t'8)))) then
    let t'9 ← PMem.ldU16 (this + 822)
    if ((UInt32.toInt32 (UInt16.toUInt32 (t'9))) == (0 : Int32)) then
      let t'10 := Int32.toUInt32 ((1 : Int32))
      PMem.stBits (0xce38 : UInt64) /- &AP_Notify::events -/ 8 1 (UInt32.toUInt64 (t'10))
    let t'11 ← PMem.ldU16 cmd
    PMem.stU64 (fp + 0) (Int64.toUInt64 (Int32.toInt64 ((UInt32.toInt32 (UInt16.toUInt32 (t'11))))))
    let t'12 ← Mode.gcs this
    GCS.send_text t'12 (6 : UInt32) (0x14aa3 : UInt64) /- "Reached command #%i" -/ (fp + 0)
    return true
  return false

def ModeAuto.verify_nav_wp (this : UInt64) (cmd : UInt64) : PMem.M Bool := do
  let fp ← PMem.enter 8
  let r ← ModeAuto.verify_nav_wp.body fp this cmd
  PMem.leave fp
  return r

/-- C++ `ModeAuto::verify_loiter_time : bool (const AP_Mission::Mission_Command &)`, `mode_auto.cpp:2225-2244`. -/
def ModeAuto.verify_loiter_time.body (fp : UInt64) (this : UInt64) (cmd : UInt64) : PMem.M Bool := do
  let t'1 ← PMem.ldU64 ((0x86d8 : UInt64) /- &copter -/ + 11192)
  let t'2 ← AC_WPNav.reached_wp_destination t'1
  if !t'2 then
    return false
  let t'3 ← PMem.ldU32 (this + 824)
  if (t'3 == (Int32.toUInt32 ((0 : Int32)))) then
    let t'4 := ((← PMem.clock) / 1000).toUInt32
    PMem.stU32 (this + 824) t'4
  let t'5 ← PMem.ldU32 (this + 824)
  let t'6 ← PMem.ldU16 (this + 822)
  if (decide ((((((← PMem.clock) / 1000).toUInt32) - t'5) / (Int32.toUInt32 ((1000 : Int32)))) ≥ (UInt16.toUInt32 (t'6)))) then
    let t'7 ← PMem.ldU16 cmd
    PMem.stU64 (fp + 0) (Int64.toUInt64 (Int32.toInt64 ((UInt32.toInt32 (UInt16.toUInt32 (t'7))))))
    let t'8 ← Mode.gcs this
    GCS.send_text t'8 (6 : UInt32) (0x14aa3 : UInt64) /- "Reached command #%i" -/ (fp + 0)
    return true
  return false

def ModeAuto.verify_loiter_time (this : UInt64) (cmd : UInt64) : PMem.M Bool := do
  let fp ← PMem.enter 8
  let r ← ModeAuto.verify_loiter_time.body fp this cmd
  PMem.leave fp
  return r

/-- C++ `ModeAuto::verify_spline_wp : bool (const AP_Mission::Mission_Command &)`, `mode_auto.cpp:2362-2380`. -/
def ModeAuto.verify_spline_wp.body (fp : UInt64) (this : UInt64) (cmd : UInt64) : PMem.M Bool := do
  let t'1 ← PMem.ldU64 ((0x86d8 : UInt64) /- &copter -/ + 11192)
  let t'2 ← AC_WPNav.reached_wp_destination t'1
  if !t'2 then
    return false
  let t'3 ← PMem.ldU32 (this + 824)
  if (t'3 == (Int32.toUInt32 ((0 : Int32)))) then
    let t'4 := ((← PMem.clock) / 1000).toUInt32
    PMem.stU32 (this + 824) t'4
  let t'5 ← PMem.ldU32 (this + 824)
  let t'6 ← PMem.ldU16 (this + 822)
  if (decide ((((((← PMem.clock) / 1000).toUInt32) - t'5) / (Int32.toUInt32 ((1000 : Int32)))) ≥ (UInt16.toUInt32 (t'6)))) then
    let t'7 ← PMem.ldU16 cmd
    PMem.stU64 (fp + 0) (Int64.toUInt64 (Int32.toInt64 ((UInt32.toInt32 (UInt16.toUInt32 (t'7))))))
    let t'8 ← Mode.gcs this
    GCS.send_text t'8 (6 : UInt32) (0x14aa3 : UInt64) /- "Reached command #%i" -/ (fp + 0)
    return true
  return false

def ModeAuto.verify_spline_wp (this : UInt64) (cmd : UInt64) : PMem.M Bool := do
  let fp ← PMem.enter 8
  let r ← ModeAuto.verify_spline_wp.body fp this cmd
  PMem.leave fp
  return r

/-- C++ `Mode::land_run_vertical_control : void (bool)`, `mode.cpp:713-778`. -/
def Mode.land_run_vertical_control.body (fp : UInt64) (this : UInt64) (pause_descent : Bool) : PMem.M Unit := do
  let mut pause_descent := pause_descent
  let mut climb_rate_ms : Binary32 := Int32.toBinary32 ((0 : Int32))
  let mut ignore_descent_limit : Bool := false
  if !pause_descent then
    let t'1 ← ModeLand.get_land_alt_low_m ((0x86d8 : UInt64) /- &copter -/ + 12640)
    PMem.stF32 (fp + 0) t'1
    PMem.stI32 (fp + 4) (1 : Int32)
    let t'2 ← MAX'float_int (fp + 0) (fp + 4)
    let t'3 ← vcall'Mode'get_alt_above_ground_m'34 this
    let mut sc'5 := (decide (t'2 > t'3))
    if !sc'5 then
      let t'4 ← PMem.ldB (((0x86d8 : UInt64) /- &copter -/ + 9448) + 14)
      sc'5 := t'4
    ignore_descent_limit := sc'5
    let t'6 ← ModeLand.get_land_speed_high_ms ((0x86d8 : UInt64) /- &copter -/ + 12640)
    let mut land_speed_high_ms : Binary32 := t'6
    if (decide (land_speed_high_ms > (Int32.toBinary32 ((0 : Int32))))) then
      PMem.stF32 (fp + 8) land_speed_high_ms
    else
      let t'7 ← PMem.ldU64 (this + 40)
      let t'8 ← PMem.ldU64 t'7
      let t'9 ← AC_PosControl.get_max_speed_down_ms t'8
      PMem.stF32 (fp + 8) t'9
    let t'10 ← ModeLand.get_land_speed_ms ((0x86d8 : UInt64) /- &copter -/ + 12640)
    let mut land_speed_ms : Binary32 := t'10
    PMem.stF32 (fp + 12) (Binary32.abs land_speed_ms)
    let t'11 ← MAX'float_float (fp + 8) (fp + 12)
    let t'12 ← PMem.ldF32 t'11
    PMem.stF32 (fp + 8) t'12
    PMem.stI32 (fp + 16) (1 : Int32)
    let t'13 ← MAX'float_int (fp + 0) (fp + 16)
    let t'14 ← vcall'Mode'get_alt_above_ground_m'34 this
    let t'15 ← PMem.ldU64 (this + 40)
    let t'16 ← PMem.ldU64 t'15
    let t'17 ← AC_PosControl.D_get_pos_p t'16
    let t'18 ← AC_P_1D.kP t'17
    let t'19 ← AP_ParamT'float_4.operator_const_float__'1 t'18
    let t'20 ← PMem.ldF32 t'19
    let t'21 ← PMem.ldU64 (this + 40)
    let t'22 ← PMem.ldU64 t'21
    let t'23 ← AC_PosControl.D_get_max_accel_mss t'22
    let t'24 ← PMem.ldU64 (this + 104)
    let t'25 ← PMem.ldF32 t'24
    let t'26 ← sqrt_controller (t'13 - t'14) t'20 t'23 t'25
    climb_rate_ms := t'26
    let t'27 ← PMem.ldF32 (fp + 8)
    let t'28 ← constrain_value_line'float climb_rate_ms (-t'27) (-(Binary32.abs land_speed_ms)) (Int32.toUInt32 ((739 : Int32)))
    climb_rate_ms := t'28
  let t'29 ← PMem.ldU64 (this + 40)
  let t'30 ← PMem.ldU64 t'29
  AC_PosControl.D_set_pos_target_from_climb_rate_ms t'30 climb_rate_ms ignore_descent_limit
  let t'31 ← PMem.ldU64 (this + 40)
  let t'32 ← PMem.ldU64 t'31
  AC_PosControl.D_update_controller t'32
  return ()

def Mode.land_run_vertical_control (this : UInt64) (pause_descent : Bool) : PMem.M Unit := do
  let fp ← PMem.enter 20
  let r ← Mode.land_run_vertical_control.body fp this pause_descent
  PMem.leave fp
  return r

/-- C++ `ModeRTL::compute_return_target : void ()`, `mode_rtl.cpp:493-609`. -/
def ModeRTL.compute_return_target.body (fp : UInt64) (this : UInt64) : PMem.M Unit := do
  let t'1 ← PMem.ldU64 (this + 48)
  VehicleBridge.AP_AHRS.get_home'0 t'1 (fp + 0)
  let t'2 := (fp + 0)
  discard <| PMem.memcpy ((this + 132) + 32) t'2 16
  discard <| pure (((this + 132) + 32))
  let t'3 ← PMem.ldU64 (this + 40)
  let t'4 ← PMem.ldU64 t'3
  let t'5 ← AC_PosControl.get_pos_offset_U_m t'4
  let mut pos_offset_u_m : Binary32 := t'5
  let t'6 ← PMem.ldI32 (((0x86d8 : UInt64) /- &copter -/ + 11148) + 4)
  PMem.stF32 (fp + 16) (((Int32.toBinary32 (t'6)) * (Binary64.toBinary32 ((Binary64.ofBits 0x3f847ae147ae147b /- 1/100 -/)))) - pos_offset_u_m)
  let mut alt_type : Int32 := (0 : Int32)
  let t'7 ← PMem.ldB (this + 204)
  let mut sc'9 := t'7
  if sc'9 then
    let t'8 ← ModeRTL.get_alt_type this
    sc'9 := (t'8 == (1 : Int8))
  if sc'9 then
    let t'10 ← PMem.ldU64 (this + 24)
    let t'11 ← PMem.ldU64 t'10
    let t'12 ← AC_WPNav.get_terrain_source t'11
    let sw'13 := t'12
    if sw'13 == (0 : Int32) then
      alt_type := (0 : Int32)
      let t'14 ← Mode.gcs this
      GCS.send_text t'14 (2 : UInt32) (0x14c11 : UInt64) /- "RTL: no terrain data, using alt-above-home" -/ (fp + 24)
    else if sw'13 == (1 : Int32) then
      alt_type := (1 : Int32)
    else if sw'13 == (2 : Int32) then
      alt_type := (2 : Int32)
    else
      pure ()
  if (alt_type == (1 : Int32)) then
    let t'15 ← Copter.get_rangefinder_height_interpolated_m (0x86d8 : UInt64) /- &copter -/ (fp + 16)
    if t'15 then
      let t'16 ← PMem.ldF32 (fp + 16)
      let t'17 := (t'16 - pos_offset_u_m)
      PMem.stF32 (fp + 16) t'17
      let t'18 ← PMem.ldF32 (fp + 16)
      PMem.stF32 (fp + 36) (Binary32.ofBits 0x00000000 /- 0 -/)
      let t'19 ← AP_ParamTBase'float_4.get (this + 124)
      let t'20 ← MAX'float_float (fp + 36) t'19
      let t'21 ← PMem.ldF32 t'20
      PMem.stF32 (fp + 32) (t'18 + t'21)
      let t'22 ← AP_ParamTBase'float_4.get (this + 112)
      PMem.stF32 (fp + 40) (Binary64.toBinary32 ((Binary64.ofBits 0x3fd3333333333333 /- 29999999999999999/100000000000000000 -/)))
      let t'23 ← MAX'float_float t'22 (fp + 40)
      let t'24 ← MAX'float_float (fp + 32) t'23
      let t'25 ← PMem.ldF32 t'24
      Location.set_alt_m ((this + 132) + 32) t'25 (3 : Int32)
    else
      alt_type := (0 : Int32)
      let t'26 ← Mode.gcs this
      GCS.send_text t'26 (2 : UInt32) (0x14c3c : UInt64) /- "RTL: rangefinder unhealthy, using alt-above-home" -/ (fp + 48)
  if (alt_type == (2 : Int32)) then
    let t'27 ← Location.get_alt_m ((0x86d8 : UInt64) /- &copter -/ + 11148) (3 : Int32) (fp + 56)
    let mut sc'29 := t'27
    if sc'29 then
      let t'28 ← Location.change_alt_frame ((this + 132) + 32) (3 : Int32)
      sc'29 := t'28
    if sc'29 then
      let t'30 ← PMem.ldF32 (fp + 56)
      let t'31 := (t'30 - pos_offset_u_m)
      PMem.stF32 (fp + 16) t'31
    else
      alt_type := (0 : Int32)
      let t'32 ← Mode.gcs this
      GCS.send_text t'32 (2 : UInt32) (0x14c11 : UInt64) /- "RTL: no terrain data, using alt-above-home" -/ (fp + 64)
  if (alt_type == (0 : Int32)) then
    let t'33 ← Location.change_alt_frame ((this + 132) + 32) (1 : Int32)
    if !t'33 then
      Location.set_alt_m ((this + 132) + 32) (Int32.toBinary32 ((0 : Int32))) (1 : Int32)
      let t'34 ← Mode.gcs this
      GCS.send_text t'34 (4 : UInt32) (0x14c6d : UInt64) /- "RTL: unexpected error calculating target alt" -/ (fp + 72)
  PMem.stI32 (fp + 84) (0 : Int32)
  let t'35 ← MAX'int_int (((this + 132) + 32) + 4) (fp + 84)
  let t'36 ← PMem.ldI32 t'35
  PMem.stF32 (fp + 80) ((Int32.toBinary32 (t'36)) * (Binary64.toBinary32 ((Binary64.ofBits 0x3f847ae147ae147b /- 1/100 -/))))
  PMem.stF32 (fp + 92) (Binary64.toBinary32 ((Binary64.ofBits 0x3fd3333333333333 /- 29999999999999999/100000000000000000 -/)))
  let t'37 ← PMem.ldF32 (fp + 16)
  PMem.stF32 (fp + 100) (Binary32.ofBits 0x00000000 /- 0 -/)
  let t'38 ← AP_ParamTBase'float_4.get (this + 124)
  let t'39 ← MAX'float_float (fp + 100) t'38
  let t'40 ← PMem.ldF32 t'39
  PMem.stF32 (fp + 96) (t'37 + t'40)
  let t'41 ← MAX'float_float (fp + 92) (fp + 96)
  let t'42 ← PMem.ldF32 t'41
  PMem.stF32 (fp + 88) t'42
  let t'43 ← AP_ParamTBase'float_4.get (this + 112)
  let t'44 ← MAX'float_float t'43 (fp + 88)
  let t'45 ← MAX'float_float (fp + 80) t'44
  let t'46 ← PMem.ldF32 t'45
  PMem.stF32 (fp + 80) t'46
  let t'47 ← Location.get_distance ((this + 132) + 32) (this + 132)
  let mut rtl_return_dist_m : Binary32 := Binary64.toBinary32 (t'47)
  let t'48 ← PMem.ldU64 (this + 8)
  let t'49 ← AP_ParamT'float_4.operator_const_float__'1 (t'48 + 12)
  let t'50 ← PMem.ldF32 t'49
  if (decide (t'50 ≥ (Binary32.ofBits 0x3f000000 /- 1/2 -/))) then
    let t'51 ← PMem.ldU64 (this + 8)
    let t'52 ← AP_ParamT'float_4.operator_const_float__'1 (t'51 + 12)
    let t'53 ← PMem.ldF32 t'52
    PMem.stF32 (fp + 104) (rtl_return_dist_m * t'53)
    let t'54 ← MAX'float_float (fp + 104) (fp + 88)
    let t'55 ← MIN'float_float (fp + 80) t'54
    let t'56 ← PMem.ldF32 t'55
    PMem.stF32 (fp + 80) t'56
  let t'57 ← PMem.ldF32 (fp + 80)
  let mut c'58 : Int32 := default
  if (alt_type == (0 : Int32)) then
    c'58 := (1 : Int32)
  else
    c'58 := (3 : Int32)
  Location.set_alt_m ((this + 132) + 32) t'57 c'58
  let t'59 ← PMem.ldF32 (fp + 16)
  PMem.stF32 (fp + 108) (t'59 * (Binary64.toBinary32 ((Binary64.ofBits 0x4059000000000000 /- 100 -/))))
  let t'60 ← MAX'int_float (((this + 132) + 32) + 4) (fp + 108)
  let t'61 := Binary32.toInt32 (t'60)
  PMem.stI32 (((this + 132) + 32) + 4) t'61
  return ()

def ModeRTL.compute_return_target (this : UInt64) : PMem.M Unit := do
  let fp ← PMem.enter 112
  let r ← ModeRTL.compute_return_target.body fp this
  PMem.leave fp
  return r

/-- C++ `ModeRTL::build_path : void ()`, `mode_rtl.cpp:469-489`. -/
def ModeRTL.build_path.body (fp : UInt64) (this : UInt64) : PMem.M Unit := do
  Mode.get_stopping_point this (fp + 0)
  let t'1 := (fp + 0)
  discard <| PMem.memcpy (this + 132) t'1 16
  discard <| pure ((this + 132))
  let t'2 ← Location.change_alt_frame (this + 132) (1 : Int32)
  discard <| pure (t'2)
  ModeRTL.compute_return_target this
  let t'3 ← PMem.ldI32 ((this + 132) + 8)
  let t'4 ← PMem.ldI32 ((this + 132) + 12)
  let t'5 ← PMem.ldI32 (((this + 132) + 32) + 4)
  let t'6 ← Location.get_alt_frame ((this + 132) + 32)
  Location.Location'3 (fp + 16) t'3 t'4 t'5 t'6
  discard <| PMem.memcpy ((this + 132) + 16) (fp + 16) 16
  discard <| pure (((this + 132) + 16))
  let t'7 ← PMem.ldI32 (((this + 132) + 32) + 8)
  let t'8 ← PMem.ldI32 (((this + 132) + 32) + 12)
  let t'9 ← AP_ParamTBase'float_4.get (this + 120)
  let t'10 ← PMem.ldF32 t'9
  Location.Location'3 (fp + 32) t'7 t'8 (Binary32.toInt32 ((t'10 * (Int32.toBinary32 ((100 : Int32)))))) (1 : Int32)
  discard <| PMem.memcpy ((this + 132) + 48) (fp + 32) 16
  discard <| pure (((this + 132) + 48))
  let t'11 ← Location.change_alt_frame ((this + 132) + 48) (2 : Int32)
  discard <| pure (t'11)
  let t'12 ← AP_ParamTBase'float_4.get (this + 120)
  let t'13 ← PMem.ldF32 t'12
  let t'14 := (decide (t'13 ≤ (Int32.toBinary32 ((0 : Int32)))))
  PMem.stB ((this + 132) + 64) t'14
  return ()

def ModeRTL.build_path (this : UInt64) : PMem.M Unit := do
  let fp ← PMem.enter 48
  let r ← ModeRTL.build_path.body fp this
  PMem.leave fp
  return r

/-- C++ `Mode::set_land_complete : void (bool)`, `mode.cpp:1137-1140`. -/
def Mode.set_land_complete (this : UInt64) (b : Bool) : PMem.M Unit := do
  let mut b := b
  Copter.set_land_complete (0x86d8 : UInt64) /- &copter -/ b
  return ()

/-- C++ `ModeGuided::angle_control_run : void ()`, `mode_guided.cpp:978-1044`. -/
def ModeGuided.angle_control_run.body (fp : UInt64) (this : UInt64) : PMem.M Unit := do
  PMem.stF32 (fp + 0) (Binary32.ofBits 0x00000000 /- 0 -/)
  let t'1 ← PMem.ldB ((0x12e00 : UInt64) /- &guided_angle_state -/ + 40)
  if !t'1 then
    let t'2 ← PMem.ldF32 ((0x12e00 : UInt64) /- &guided_angle_state -/ + 32)
    let t'3 ← PMem.ldU64 (this + 24)
    let t'4 ← PMem.ldU64 t'3
    let t'5 ← AC_WPNav.get_default_speed_down_ms t'4
    let t'6 ← PMem.ldU64 (this + 24)
    let t'7 ← PMem.ldU64 t'6
    let t'8 ← AC_WPNav.get_default_speed_up_ms t'7
    let t'9 ← constrain_value_line'float t'2 (-t'5) t'8 (Int32.toUInt32 ((983 : Int32)))
    PMem.stF32 (fp + 0) t'9
    let t'10 ← PMem.ldF32 (fp + 0)
    let t'11 ← Mode.get_avoidance_adjusted_climbrate_ms this t'10
    PMem.stF32 (fp + 0) t'11
  let mut tnow : UInt32 := ((← PMem.clock) / 1000).toUInt32
  let t'12 ← PMem.ldU32 (0x12e00 : UInt64) /- &guided_angle_state -/
  let t'13 ← ModeGuided.get_timeout_ms this
  if (decide ((tnow - t'12) > t'13)) then
    let t'14 ← PMem.ldU64 (this + 56)
    let t'15 ← PMem.ldU64 t'14
    let t'16 ← AC_AttitudeControl.get_att_target_euler_rad t'15
    let t'17 ← PMem.ldF32 (t'16 + 8)
    Vector3'float.Vector3 (fp + 8) (Binary64.toBinary32 ((Binary64.ofBits 0x0000000000000000 /- 0 -/))) (Binary64.toBinary32 ((Binary64.ofBits 0x0000000000000000 /- 0 -/))) t'17
    QuaternionT'float.from_euler ((0x12e00 : UInt64) /- &guided_angle_state -/ + 4) (fp + 8)
    Vector3'float.zero ((0x12e00 : UInt64) /- &guided_angle_state -/ + 20)
    let t'18 := (Binary32.ofBits 0x00000000 /- 0 -/)
    PMem.stF32 (fp + 0) t'18
    let t'19 ← PMem.ldB ((0x12e00 : UInt64) /- &guided_angle_state -/ + 40)
    if t'19 then
      let t'20 ← PMem.ldU64 (this + 40)
      let t'21 ← PMem.ldU64 t'20
      AC_PosControl.D_init_controller t'21
      PMem.stB ((0x12e00 : UInt64) /- &guided_angle_state -/ + 40) false
  let t'22 ← PMem.ldB ((0x12e00 : UInt64) /- &guided_angle_state -/ + 40)
  let mut c'23 : Binary32 := default
  if t'22 then
    let t'24 ← PMem.ldF32 ((0x12e00 : UInt64) /- &guided_angle_state -/ + 36)
    c'23 := t'24
  else
    let t'25 ← PMem.ldF32 (fp + 0)
    c'23 := t'25
  let t'26 ← is_positive'float c'23
  let mut positive_thrust_or_climbrate : Bool := t'26
  let t'27 ← PMem.ldU64 (this + 64)
  let t'28 ← PMem.ldU64 t'27
  let t'29 ← AP_Motors.armed t'28
  if (t'29 && positive_thrust_or_climbrate) then
    Copter.set_auto_armed (0x86d8 : UInt64) /- &copter -/ true
  let t'30 ← PMem.ldU64 (this + 64)
  let t'31 ← PMem.ldU64 t'30
  let t'32 ← AP_Motors.armed t'31
  let mut sc'34 := !t'32
  if !sc'34 then
    let t'33 ← PMem.ldB (((0x86d8 : UInt64) /- &copter -/ + 9448) + 5)
    sc'34 := !t'33
  let mut sc'36 := sc'34
  if !sc'36 then
    let t'35 ← PMem.ldB (((0x86d8 : UInt64) /- &copter -/ + 9448) + 7)
    sc'36 := (t'35 && (!positive_thrust_or_climbrate))
  if sc'36 then
    let t'37 ← Copter.is_tradheli (0x86d8 : UInt64) /- &copter -/
    let mut sc'41 := t'37
    if sc'41 then
      let t'38 ← PMem.ldU64 (this + 64)
      let t'39 ← PMem.ldU64 t'38
      let t'40 ← AP_Motors.get_interlock t'39
      sc'41 := t'40
    Mode.make_safe_ground_handling this sc'41
    return ()
  let t'42 ← PMem.ldB (((0x86d8 : UInt64) /- &copter -/ + 9448) + 7)
  if (t'42 && positive_thrust_or_climbrate) then
    Mode.zero_throttle_and_relax_ac this false
    let t'43 ← PMem.ldU64 (this + 64)
    let t'44 ← PMem.ldU64 t'43
    AP_MotorsMulticopter.set_desired_spool_state t'44 (2 : UInt8)
    let t'45 ← PMem.ldU64 (this + 64)
    let t'46 ← PMem.ldU64 t'45
    let t'47 ← AP_Motors.get_spool_state t'46
    if (t'47 == (3 : UInt8)) then
      Mode.set_land_complete this false
      let t'48 ← PMem.ldU64 (this + 40)
      let t'49 ← PMem.ldU64 t'48
      AC_PosControl.D_init_controller t'49
    return ()
  let t'50 ← PMem.ldU64 (this + 64)
  let t'51 ← PMem.ldU64 t'50
  AP_MotorsMulticopter.set_desired_spool_state t'51 (2 : UInt8)
  let t'52 ← QuaternionT'float.is_zero ((0x12e00 : UInt64) /- &guided_angle_state -/ + 4)
  if t'52 then
    let t'53 ← PMem.ldF32 ((0x12e00 : UInt64) /- &guided_angle_state -/ + 20)
    let t'54 ← PMem.ldF32 (((0x12e00 : UInt64) /- &guided_angle_state -/ + 20) + 4)
    let t'55 ← PMem.ldF32 (((0x12e00 : UInt64) /- &guided_angle_state -/ + 20) + 8)
    let t'56 ← PMem.ldU64 (this + 56)
    let t'57 ← PMem.ldU64 t'56
    AC_AttitudeControl.input_rate_bf_roll_pitch_yaw_rads t'57 t'53 t'54 t'55
  else
    Vector3'float.Vector3'4 (fp + 24) ((0x12e00 : UInt64) /- &guided_angle_state -/ + 20)
    let t'58 ← PMem.ldU64 (this + 56)
    let t'59 ← PMem.ldU64 t'58
    AC_AttitudeControl.input_quaternion t'59 ((0x12e00 : UInt64) /- &guided_angle_state -/ + 4) (fp + 24)
  let t'60 ← PMem.ldB ((0x12e00 : UInt64) /- &guided_angle_state -/ + 40)
  if t'60 then
    let t'61 ← PMem.ldF32 ((0x12e00 : UInt64) /- &guided_angle_state -/ + 36)
    let t'62 ← AP_ParamT'float_4.operator_const_float__'1 (((0x86d8 : UInt64) /- &copter -/ + 6776) + 4)
    let t'63 ← PMem.ldF32 t'62
    let t'64 ← PMem.ldU64 (this + 56)
    let t'65 ← PMem.ldU64 t'64
    AC_AttitudeControl_Multi.set_throttle_out t'65 t'61 true t'63
  else
    let t'66 ← PMem.ldF32 (fp + 0)
    let t'67 ← PMem.ldU64 (this + 40)
    let t'68 ← PMem.ldU64 t'67
    AC_PosControl.D_set_pos_target_from_climb_rate_ms t'68 t'66 false
    let t'69 ← PMem.ldU64 (this + 40)
    let t'70 ← PMem.ldU64 t'69
    AC_PosControl.D_update_controller t'70
  return ()

def ModeGuided.angle_control_run (this : UInt64) : PMem.M Unit := do
  let fp ← PMem.enter 36
  let r ← ModeGuided.angle_control_run.body fp this
  PMem.leave fp
  return r

/-- C++ `ModeLoiter::run : void ()`, `mode_loiter.cpp:77-181`. -/
def ModeLoiter.run.body (fp : UInt64) (this : UInt64) : PMem.M Unit := do
  let mut target_yaw_rate_rads : Binary32 := (Binary32.ofBits 0x00000000 /- 0 -/)
  let mut target_climb_rate_ms : Binary32 := (Binary32.ofBits 0x00000000 /- 0 -/)
  let t'1 ← Mode.get_pilot_speed_dn_ms this
  let t'2 ← Mode.get_pilot_speed_up_ms this
  let t'3 ← Mode.get_pilot_accel_D_mss this
  let t'4 ← PMem.ldU64 (this + 40)
  let t'5 ← PMem.ldU64 t'4
  AC_PosControl.D_set_max_speed_accel_m t'5 t'1 t'2 t'3
  let t'6 ← PMem.ldU64 (this + 32)
  let t'7 ← PMem.ldU64 t'6
  let t'8 ← AC_Loiter.get_angle_max_rad t'7
  let t'9 ← PMem.ldU64 (this + 56)
  let t'10 ← PMem.ldU64 t'9
  let t'11 ← AC_AttitudeControl.get_althold_lean_angle_max_rad t'10
  Mode.get_pilot_desired_lean_angles_rad this (fp + 0) (fp + 8) t'8 t'11
  let t'12 ← PMem.ldF32 (fp + 0)
  let t'13 ← PMem.ldF32 (fp + 8)
  let t'14 ← PMem.ldU64 (this + 32)
  let t'15 ← PMem.ldU64 t'14
  AC_Loiter.set_pilot_desired_acceleration_rad t'15 t'12 t'13
  let t'16 ← Mode.get_pilot_desired_yaw_rate_rads this
  target_yaw_rate_rads := t'16
  let t'17 ← Mode.get_pilot_desired_climb_rate_ms this
  target_climb_rate_ms := t'17
  let t'18 ← PMem.ldB (((0x86d8 : UInt64) /- &copter -/ + 9448) + 14)
  if t'18 then
    let t'19 ← PMem.ldU64 (this + 32)
    let t'20 ← PMem.ldU64 t'19
    AC_Loiter.soften_for_landing t'20
  let t'21 ← Mode.get_alt_hold_state_D_ms this target_climb_rate_ms
  let mut loiter_state : Int32 := t'21
  let sw'22 := loiter_state
  if sw'22 == (0 : Int32) then
    let t'23 ← PMem.ldU64 (this + 56)
    let t'24 ← PMem.ldU64 t'23
    AC_AttitudeControl.reset_rate_controller_I_terms t'24
    let t'25 ← PMem.ldU64 (this + 56)
    let t'26 ← PMem.ldU64 t'25
    AC_AttitudeControl.reset_yaw_target_and_rate t'26 true
    let t'27 ← PMem.ldU64 (this + 40)
    let t'28 ← PMem.ldU64 t'27
    AC_PosControl.D_relax_controller t'28 (Binary32.ofBits 0x00000000 /- 0 -/)
    let t'29 ← PMem.ldU64 (this + 32)
    let t'30 ← PMem.ldU64 t'29
    AC_Loiter.init_target t'30
  else if sw'22 == (2 : Int32) then
    let t'31 ← PMem.ldU64 (this + 56)
    let t'32 ← PMem.ldU64 t'31
    AC_AttitudeControl.reset_yaw_target_and_rate t'32 true
    let t'33 ← PMem.ldU64 (this + 56)
    let t'34 ← PMem.ldU64 t'33
    AC_AttitudeControl.reset_rate_controller_I_terms_smoothly t'34
    let t'35 ← PMem.ldU64 (this + 32)
    let t'36 ← PMem.ldU64 t'35
    AC_Loiter.init_target t'36
    let t'37 ← PMem.ldU64 (this + 40)
    let t'38 ← PMem.ldU64 t'37
    AC_PosControl.D_relax_controller t'38 (Binary32.ofBits 0x00000000 /- 0 -/)
  else if sw'22 == (3 : Int32) then
    let t'39 ← PMem.ldU64 (this + 56)
    let t'40 ← PMem.ldU64 t'39
    AC_AttitudeControl.reset_rate_controller_I_terms_smoothly t'40
    let t'41 ← PMem.ldU64 (this + 32)
    let t'42 ← PMem.ldU64 t'41
    AC_Loiter.init_target t'42
    let t'43 ← PMem.ldU64 (this + 40)
    let t'44 ← PMem.ldU64 t'43
    AC_PosControl.D_relax_controller t'44 (Binary32.ofBits 0x00000000 /- 0 -/)
  else if sw'22 == (1 : Int32) then
    let t'45 ← Mode._TakeOff.running (0xede8 : UInt64) /- &Mode::takeoff -/
    if !t'45 then
      let t'46 ← PMem.ldU64 (this + 16)
      let t'47 ← AP_ParamT'float_4.operator_const_float__'1 (t'46 + 1644)
      let t'48 ← PMem.ldF32 t'47
      let t'49 ← constrain_value_line'float t'48 (Binary64.toBinary32 ((Binary64.ofBits 0x0000000000000000 /- 0 -/))) (Binary64.toBinary32 ((Binary64.ofBits 0x4024000000000000 /- 10 -/))) (Int32.toUInt32 ((129 : Int32)))
      Mode._TakeOff.start_m (0xede8 : UInt64) /- &Mode::takeoff -/ t'49
    let t'50 ← Mode.get_avoidance_adjusted_climbrate_ms this target_climb_rate_ms
    target_climb_rate_ms := t'50
    Mode._TakeOff.do_pilot_takeoff_ms (0xede8 : UInt64) /- &Mode::takeoff -/ target_climb_rate_ms
    let t'51 ← PMem.ldU64 (this + 32)
    let t'52 ← PMem.ldU64 t'51
    AC_Loiter.update t'52 true
  else if sw'22 == (4 : Int32) then
    let t'53 ← PMem.ldU64 (this + 32)
    let t'54 ← PMem.ldU64 t'53
    AC_Loiter.update t'54 true
    let t'55 ← Mode.get_avoidance_adjusted_climbrate_ms this target_climb_rate_ms
    target_climb_rate_ms := t'55
    let t'56 ← PMem.ldU64 (this + 40)
    let t'57 ← PMem.ldU64 t'56
    AC_PosControl.D_set_pos_target_from_climb_rate_ms t'57 target_climb_rate_ms false
  else
    pure ()
  let t'58 ← PMem.ldU64 (this + 32)
  let t'59 ← PMem.ldU64 t'58
  AC_Loiter.get_thrust_vector t'59 (fp + 16)
  let t'60 := (fp + 16)
  let t'61 ← PMem.ldU64 (this + 56)
  let t'62 ← PMem.ldU64 t'61
  AC_AttitudeControl.input_thrust_vector_rate_heading_rads t'62 t'60 target_yaw_rate_rads false
  let t'63 ← PMem.ldU64 (this + 40)
  let t'64 ← PMem.ldU64 t'63
  AC_PosControl.D_update_controller t'64
  return ()

def ModeLoiter.run (this : UInt64) : PMem.M Unit := do
  let fp ← PMem.enter 28
  let r ← ModeLoiter.run.body fp this
  PMem.leave fp
  return r

/-- C++ `ModeStabilize::run : void ()`, `mode_stabilize.cpp:9-61`. -/
def ModeStabilize.run.body (fp : UInt64) (this : UInt64) : PMem.M Unit := do
  let t'1 ← PMem.ldU64 (this + 56)
  let t'2 ← PMem.ldU64 t'1
  let t'3 ← AC_AttitudeControl.lean_angle_max_rad t'2
  let t'4 ← PMem.ldU64 (this + 56)
  let t'5 ← PMem.ldU64 t'4
  let t'6 ← AC_AttitudeControl.lean_angle_max_rad t'5
  Mode.get_pilot_desired_lean_angles_rad this (fp + 0) (fp + 8) t'3 t'6
  let t'7 ← Mode.get_pilot_desired_yaw_rate_rads this
  let mut target_yaw_rate_rads : Binary32 := t'7
  let t'8 ← PMem.ldB (((0x86d8 : UInt64) /- &copter -/ + 9448) + 15)
  if t'8 then
    let t'9 ← PMem.ldU64 (this + 64)
    let t'10 ← PMem.ldU64 t'9
    AP_MotorsMulticopter.set_desired_spool_state t'10 (1 : UInt8)
  else
    let t'11 ← PMem.ldU64 (this + 64)
    let t'12 ← PMem.ldU64 t'11
    AP_MotorsMulticopter.set_desired_spool_state t'12 (2 : UInt8)
  let t'13 ← Mode.get_pilot_desired_throttle this
  let mut pilot_desired_throttle : Binary32 := t'13
  let t'14 ← PMem.ldU64 (this + 64)
  let t'15 ← PMem.ldU64 t'14
  let t'16 ← AP_Motors.get_spool_state t'15
  let sw'17 := t'16
  if sw'17 == (0 : UInt8) then
    let t'18 ← PMem.ldU64 (this + 56)
    let t'19 ← PMem.ldU64 t'18
    AC_AttitudeControl.reset_yaw_target_and_rate t'19 true
    let t'20 ← PMem.ldU64 (this + 56)
    let t'21 ← PMem.ldU64 t'20
    AC_AttitudeControl.reset_rate_controller_I_terms t'21
    let t'22 := (Binary32.ofBits 0x00000000 /- 0 -/)
    pilot_desired_throttle := t'22
  else if sw'17 == (1 : UInt8) then
    let t'23 ← PMem.ldU64 (this + 56)
    let t'24 ← PMem.ldU64 t'23
    AC_AttitudeControl.reset_yaw_target_and_rate t'24 true
    let t'25 ← PMem.ldU64 (this + 56)
    let t'26 ← PMem.ldU64 t'25
    AC_AttitudeControl.reset_rate_controller_I_terms_smoothly t'26
    let t'27 := (Binary32.ofBits 0x00000000 /- 0 -/)
    pilot_desired_throttle := t'27
  else if sw'17 == (3 : UInt8) then
    let t'28 ← PMem.ldU64 (this + 64)
    let t'29 ← PMem.ldU64 t'28
    let t'30 ← PMem.ldB ((t'29 + 8) + 3)
    if !t'30 then
      Mode.set_land_complete this false
  else if sw'17 == (2 : UInt8) || sw'17 == (4 : UInt8) then
    pure ()
  else
    pure ()
  let t'31 ← PMem.ldF32 (fp + 0)
  let t'32 ← PMem.ldF32 (fp + 8)
  let t'33 ← PMem.ldU64 (this + 56)
  let t'34 ← PMem.ldU64 t'33
  AC_AttitudeControl.input_euler_angle_roll_pitch_euler_rate_yaw_rad t'34 t'31 t'32 target_yaw_rate_rads
  let t'35 ← PMem.ldU64 (this + 8)
  let t'36 ← AP_ParamT'float_4.operator_const_float__'1 (t'35 + 4)
  let t'37 ← PMem.ldF32 t'36
  let t'38 ← PMem.ldU64 (this + 56)
  let t'39 ← PMem.ldU64 t'38
  AC_AttitudeControl_Multi.set_throttle_out t'39 pilot_desired_throttle true t'37
  return ()

def ModeStabilize.run (this : UInt64) : PMem.M Unit := do
  let fp ← PMem.enter 12
  let r ← ModeStabilize.run.body fp this
  PMem.leave fp
  return r

/-- C++ `Copter::set_home_to_current_location_inflight : void ()`, `commands.cpp:23-37`. -/
def Copter.set_home_to_current_location_inflight.body (fp : UInt64) (this : UInt64) : PMem.M Unit := do
  Location.Location (fp + 0)
  Location.Location (fp + 16)
  let t'1 ← VehicleBridge.AP_AHRS.get_location'1 (this + 4080) (fp + 0)
  let mut sc'3 := t'1
  if sc'3 then
    let t'2 ← VehicleBridge.AP_AHRS.get_origin'1 (this + 4080) (fp + 16)
    sc'3 := t'2
  if sc'3 then
    Location.copy_alt_from (fp + 0) (fp + 16)
    let t'4 ← Copter.set_home this (fp + 0) false
    if !t'4 then
      return ()
  return ()

def Copter.set_home_to_current_location_inflight (this : UInt64) : PMem.M Unit := do
  let fp ← PMem.enter 32
  let r ← Copter.set_home_to_current_location_inflight.body fp this
  PMem.leave fp
  return r

/-- C++ `Copter::update_home_from_EKF : void ()`, `commands.cpp:4-20`. -/
def Copter.update_home_from_EKF (this : UInt64) : PMem.M Unit := do
  let t'1 ← VehicleBridge.AP_AHRS.home_is_set'0 (this + 4080)
  if t'1 then
    return ()
  let t'2 ← PMem.ldU64 (this + 9528)
  let t'3 ← AP_Motors.armed t'2
  if t'3 then
    Copter.set_home_to_current_location_inflight this
  else
    let t'4 ← Copter.set_home_to_current_location this false
    if !t'4 then
      pure ()
  return ()

/-- C++ `Copter::update_land_detector : void ()`, `land_detector.cpp:37-173`. -/
def Copter.update_land_detector.body (fp : UInt64) (this : UInt64) : PMem.M Unit := do
  let t'1 ← PMem.ldU64 (this + 9528)
  let t'2 ← AP_Motors.armed t'1
  if !t'2 then
    Copter.set_land_complete this true
  else
    let t'3 ← PMem.ldB ((this + 9448) + 7)
    if t'3 then
      let t'4 ← PMem.ldU64 (this + 9488)
      let t'5 ← vcall'Mode'is_taking_off'17 t'4
      let mut sc'9 := !t'5
      if sc'9 then
        let t'6 ← PMem.ldU64 (this + 9528)
        let t'7 ← AP_Motors.get_throttle_out t'6
        let t'8 ← Copter.get_non_takeoff_throttle this
        sc'9 := (decide (t'7 > t'8))
      let mut sc'12 := sc'9
      if sc'12 then
        let t'10 ← PMem.ldU64 (this + 9528)
        let t'11 ← AP_Motors.get_spool_state t'10
        sc'12 := (t'11 == (3 : UInt8))
      if sc'12 then
        Copter.set_land_complete this false
    else
      let t'13 ← PMem.ldB (this + 11229)
      if t'13 then
        let t'14 := Int32.toUInt32 ((0 : Int32))
        PMem.stU32 (0xce20 : UInt64) /- &land_detector_count -/ t'14
      else
        let mut land_trigger_sec : Binary32 := (Binary32.ofBits 0x3f800000 /- 1 -/)
        let t'15 ← PMem.ldU64 (this + 9528)
        let t'16 ← PMem.ldB ((t'15 + 8) + 3)
        let mut motor_at_lower_limit : Bool := t'16
        let t'17 ← PMem.ldU64 (this + 11168)
        let t'18 ← AC_AttitudeControl_Multi.is_throttle_mix_min t'17
        let mut throttle_mix_at_min : Bool := t'18
        let t'19 ← PMem.ldU64 (this + 9488)
        let t'20 ← vcall'Mode'has_manual_throttle'3 t'19
        let mut sc'22 := t'20
        if sc'22 then
          let t'21 ← Copter.air_mode_active this
          sc'22 := t'21
        if sc'22 then
          let t'23 := (Binary32.ofBits 0x40400000 /- 3 -/)
          land_trigger_sec := t'23
          throttle_mix_at_min := true
        let mut land_detector_scalar : UInt8 := Int8.toUInt8 (Int32.toInt8 ((1 : Int32)))
        let t'24 ← PMem.ldU64 (this + 11168)
        let t'25 ← AC_AttitudeControl.get_att_target_euler_rad t'24
        let angle_target_rad : UInt64 := t'25
        let t'26 ← Vector3'float.xy angle_target_rad
        let t'27 ← Vector2'float.length_squared t'26
        let t'28 ← radians (Binary32.ofBits 0x41700000 /- 15 -/)
        let t'29 ← sq t'28
        let mut large_angle_request : Bool := (decide (t'27 > t'29))
        let t'30 ← PMem.ldU64 (this + 11168)
        let t'31 ← AC_AttitudeControl.get_att_error_angle_deg t'30
        let mut angle_error : Binary32 := t'31
        let mut large_angle_error : Bool := (decide (angle_error > (Binary32.ofBits 0x41f00000 /- 30 -/)))
        let t'32 ← DigitalLPF'Vector3_float.get (this + 11116)
        let t'33 ← Vector3'float.length t'32
        let mut accel_stationary : Bool := (decide (t'33 ≤ ((Binary32.ofBits 0x3f800000 /- 1 -/) * (Int32.toBinary32 ((UInt32.toInt32 (UInt8.toUInt32 (land_detector_scalar))))))))
        PMem.stF32 (fp + 0) (Int32.toBinary32 ((0 : Int32)))
        for _ in [0:1] do
          let mut __unique_name___COUNTER__ : Bool := default  -- uninitialized in C
          let t'34 ← PMem.ldB ((0x86d8 : UInt64) /- &copter -/ + 8852)
          let t'35 ← VehicleBridge.ahrs'0
          let t'36 ← VehicleBridge.AP_AHRS.get_velocity_D'2 t'35 (fp + 0) t'34
          __unique_name___COUNTER__ := t'36
        let t'37 ← PMem.ldF32 (fp + 0)
        let mut descent_rate_low : Bool := (decide ((Binary32.abs t'37) < ((Binary32.ofBits 0x3f800000 /- 1 -/) * (Int32.toBinary32 ((UInt32.toInt32 (UInt8.toUInt32 (land_detector_scalar))))))))
        let t'38 ← Copter.rangefinder_alt_ok this
        let mut sc'41 := !t'38
        if !sc'41 then
          let t'39 ← DigitalLPF'float.get ((this + 8632) + 20)
          let t'40 ← PMem.ldF32 t'39
          sc'41 := (decide (t'40 < (Binary64.toBinary32 ((Binary64.ofBits 0x4000000000000000 /- 2 -/)))))
        let mut rangefinder_check : Bool := sc'41
        let mut WoW_check : Bool := true
        if (((((((motor_at_lower_limit && throttle_mix_at_min) && (!large_angle_request)) && (!large_angle_error)) && accel_stationary) && descent_rate_low) && rangefinder_check) && WoW_check) then
          let t'42 ← PMem.ldU32 (0xce20 : UInt64) /- &land_detector_count -/
          let t'43 ← AP_Scheduler.get_loop_rate_hz (this + 208)
          if (decide ((UInt32.toBinary32 (t'42)) < (land_trigger_sec * (Int32.toBinary32 ((UInt32.toInt32 (UInt16.toUInt32 (t'43)))))))) then
            let t'44 := (0xce20 : UInt64) /- &land_detector_count -/
            let t'45 ← PMem.ldU32 t'44
            let t'46 := (t'45 + 1)
            PMem.stU32 t'44 t'46
          else
            Copter.set_land_complete this true
        else
          let t'47 := Int32.toUInt32 ((0 : Int32))
          PMem.stU32 (0xce20 : UInt64) /- &land_detector_count -/ t'47
  let t'48 ← PMem.ldB ((this + 9448) + 7)
  let mut sc'51 := t'48
  if !sc'51 then
    let t'49 ← PMem.ldU32 (0xce20 : UInt64) /- &land_detector_count -/
    let t'50 ← AP_Scheduler.get_loop_rate_hz (this + 208)
    sc'51 := (decide ((UInt32.toBinary32 (t'49)) ≥ ((Binary32.ofBits 0x3e4ccccd /- 200000003/1000000000 -/) * (Int32.toBinary32 ((UInt32.toInt32 (UInt16.toUInt32 (t'50))))))))
  Copter.set_land_complete_maybe this sc'51
  return ()

def Copter.update_land_detector (this : UInt64) : PMem.M Unit := do
  let fp ← PMem.enter 4
  let r ← Copter.update_land_detector.body fp this
  PMem.leave fp
  return r

/-- C++ `Copter::crash_check : void ()`, `crash_check.cpp:22-97`. -/
def Copter.crash_check.body (fp : UInt64) (this : UInt64) : PMem.M Unit := do
  let t'1 ← PMem.ldU64 (this + 9528)
  let t'2 ← AP_Motors.armed t'1
  let mut sc'4 := !t'2
  if !sc'4 then
    let t'3 ← PMem.ldB ((this + 9448) + 7)
    sc'4 := t'3
  let mut sc'7 := sc'4
  if !sc'7 then
    let t'5 ← AP_ParamT'signed_char_1.operator_const_signed_char__ ((this + 6776) + 53)
    let t'6 ← PMem.ldI8 t'5
    sc'7 := ((Int8.toInt32 (t'6)) == (0 : Int32))
  if sc'7 then
    let t'8 := Int16.toUInt16 (Int32.toInt16 ((0 : Int32)))
    PMem.stU16 (0x135e0 : UInt64) /- &Copter::crash_check(...)::crash_counter -/ t'8
    return ()
  let t'9 ← PMem.ldB (this + 11229)
  if t'9 then
    let t'10 := Int16.toUInt16 (Int32.toInt16 ((0 : Int32)))
    PMem.stU16 (0x135e0 : UInt64) /- &Copter::crash_check(...)::crash_counter -/ t'10
    return ()
  let t'11 ← Copter.get_force_flying this
  let mut sc'14 := t'11
  if sc'14 then
    let t'12 ← PMem.ldU64 (this + 9488)
    let t'13 ← vcall'Mode'is_landing'15 t'12
    sc'14 := !t'13
  if sc'14 then
    let t'15 := Int16.toUInt16 (Int32.toInt16 ((0 : Int32)))
    PMem.stU16 (0x135e0 : UInt64) /- &Copter::crash_check(...)::crash_counter -/ t'15
    return ()
  let t'16 ← PMem.ldU64 (this + 9488)
  let t'17 ← vcall'Mode'crash_check_enabled'31 t'16
  if !t'17 then
    let t'18 := Int16.toUInt16 (Int32.toInt16 ((0 : Int32)))
    PMem.stU16 (0x135e0 : UInt64) /- &Copter::crash_check(...)::crash_counter -/ t'18
    return ()
  let t'19 ← DigitalLPF'Vector3_float.get (this + 11116)
  let t'20 ← Vector3'float.length t'19
  let mut filtered_acc : Binary32 := t'20
  if (decide (filtered_acc ≥ (Binary32.ofBits 0x40400000 /- 3 -/))) then
    let t'21 := Int16.toUInt16 (Int32.toInt16 ((0 : Int32)))
    PMem.stU16 (0x135e0 : UInt64) /- &Copter::crash_check(...)::crash_counter -/ t'21
    return ()
  let t'22 ← VehicleBridge.AP_AHRS.cos_roll'0 (this + 4080)
  let t'23 ← VehicleBridge.AP_AHRS.cos_pitch'0 (this + 4080)
  let t'24 ← degrees (Musl.acosf.acosf (t'22 * t'23))
  let mut lean_angle_deg : Binary32 := t'24
  if (decide (lean_angle_deg ≤ (Binary32.ofBits 0x41700000 /- 15 -/))) then
    let t'25 := Int16.toUInt16 (Int32.toInt16 ((0 : Int32)))
    PMem.stU16 (0x135e0 : UInt64) /- &Copter::crash_check(...)::crash_counter -/ t'25
    return ()
  let t'26 ← PMem.ldU64 (this + 11168)
  let t'27 ← AC_AttitudeControl.get_att_error_angle_deg t'26
  let mut angle_error : Binary32 := t'27
  if (decide (angle_error ≤ (Binary32.ofBits 0x41f00000 /- 30 -/))) then
    let t'28 := Int16.toUInt16 (Int32.toInt16 ((0 : Int32)))
    PMem.stU16 (0x135e0 : UInt64) /- &Copter::crash_check(...)::crash_counter -/ t'28
    return ()
  Vector3'float.Vector3'2 (fp + 0)
  let t'29 ← VehicleBridge.AP_AHRS.get_velocity_NED'1 (this + 4080) (fp + 0)
  let mut sc'31 := t'29
  if sc'31 then
    let t'30 ← Vector3'float.length (fp + 0)
    sc'31 := (decide (t'30 ≥ (Binary32.ofBits 0x41200000 /- 10 -/)))
  if sc'31 then
    let t'32 := Int16.toUInt16 (Int32.toInt16 ((0 : Int32)))
    PMem.stU16 (0x135e0 : UInt64) /- &Copter::crash_check(...)::crash_counter -/ t'32
    return ()
  let t'33 := (0x135e0 : UInt64) /- &Copter::crash_check(...)::crash_counter -/
  let t'34 ← PMem.ldU16 t'33
  let t'35 := (t'34 + 1)
  PMem.stU16 t'33 t'35
  let t'36 ← PMem.ldU16 (0x135e0 : UInt64) /- &Copter::crash_check(...)::crash_counter -/
  let t'37 ← AP_Scheduler.get_loop_rate_hz (this + 208)
  if (decide ((UInt32.toInt32 (UInt16.toUInt32 (t'36))) ≥ ((2 : Int32) * (UInt32.toInt32 (UInt16.toUInt32 (t'37)))))) then
    PMem.stU64 (fp + 16) (Binary64.toBits (Binary32.toBinary64 (angle_error)))
    PMem.stU64 (fp + 24) (Binary64.toBits (Binary32.toBinary64 ((Binary32.ofBits 0x41f00000 /- 30 -/))))
    PMem.stU64 (fp + 32) (Binary64.toBits (Binary32.toBinary64 (filtered_acc)))
    PMem.stU64 (fp + 40) (Binary64.toBits (Binary32.toBinary64 ((Binary32.ofBits 0x40400000 /- 3 -/))))
    let t'38 ← Copter.gcs this
    GCS.send_text t'38 (0 : UInt32) (0x144dc : UInt64) /- "Crash: Disarming: AngErr=%.0f>%.0f, Accel=%.1f<%.1f" -/ (fp + 16)
    let t'39 ← AP_Arming_Copter.disarm ((0x86d8 : UInt64) /- &copter -/ + 8768) (12 : Int32) true
    discard <| pure (t'39)
  return ()

def Copter.crash_check (this : UInt64) : PMem.M Unit := do
  let fp ← PMem.enter 48
  let r ← Copter.crash_check.body fp this
  PMem.leave fp
  return r

/-- C++ `Copter::thrust_loss_check : void ()`, `crash_check.cpp:100-181`. -/
def Copter.thrust_loss_check.body (fp : UInt64) (this : UInt64) : PMem.M Unit := do
  let t'1 ← Copter.option_is_enabled (0x86d8 : UInt64) /- &copter -/ (1 : UInt32)
  if t'1 then
    return ()
  let t'2 ← PMem.ldU64 (this + 9528)
  let t'3 ← AP_Motors.get_thrust_boost t'2
  if t'3 then
    return ()
  let t'4 ← PMem.ldU64 (this + 9528)
  let t'5 ← AP_Motors.armed t'4
  let mut sc'7 := !t'5
  if !sc'7 then
    let t'6 ← PMem.ldB ((this + 9448) + 7)
    sc'7 := t'6
  if sc'7 then
    let t'8 := Int16.toUInt16 (Int32.toInt16 ((0 : Int32)))
    PMem.stU16 (0x135e8 : UInt64) /- &Copter::thrust_loss_check(...)::thrust_loss_counter -/ t'8
    return ()
  let t'9 ← PMem.ldB (this + 11229)
  if t'9 then
    return ()
  let t'10 ← PMem.ldU64 (this + 11168)
  let t'11 ← AC_AttitudeControl.get_att_target_euler_rad t'10
  let angle_target_rad : UInt64 := t'11
  let t'12 ← Vector3'float.xy angle_target_rad
  let t'13 ← Vector2'float.length_squared t'12
  let t'14 ← radians (Binary64.toBinary32 ((Binary64.ofBits 0x402e000000000000 /- 15 -/)))
  let t'15 ← sq t'14
  if (decide (t'13 > t'15)) then
    let t'16 := Int16.toUInt16 (Int32.toInt16 ((0 : Int32)))
    PMem.stU16 (0x135e8 : UInt64) /- &Copter::thrust_loss_check(...)::thrust_loss_counter -/ t'16
    return ()
  let t'17 ← PMem.ldU64 (this + 11168)
  let t'18 ← AC_AttitudeControl.get_throttle_in t'17
  let mut sc'21 := (decide (t'18 < (Binary32.ofBits 0x3f666666 /- 112499997/125000000 -/)))
  if sc'21 then
    let t'19 ← PMem.ldU64 (this + 9528)
    let t'20 ← PMem.ldB ((t'19 + 8) + 4)
    sc'21 := !t'20
  if sc'21 then
    let t'22 := Int16.toUInt16 (Int32.toInt16 ((0 : Int32)))
    PMem.stU16 (0x135e8 : UInt64) /- &Copter::thrust_loss_check(...)::thrust_loss_counter -/ t'22
    return ()
  let t'23 ← PMem.ldU64 (this + 11168)
  let t'24 ← AC_AttitudeControl.get_throttle_in t'23
  if (decide (t'24 < (Binary32.ofBits 0x3e800000 /- 1/4 -/))) then
    let t'25 := Int16.toUInt16 (Int32.toInt16 ((0 : Int32)))
    PMem.stU16 (0x135e8 : UInt64) /- &Copter::thrust_loss_check(...)::thrust_loss_counter -/ t'25
    return ()
  PMem.stF32 (fp + 0) (Int32.toBinary32 ((0 : Int32)))
  let t'26 ← PMem.ldB (this + 8852)
  let t'27 ← VehicleBridge.ahrs'0
  let t'28 ← VehicleBridge.AP_AHRS.get_velocity_D'2 t'27 (fp + 0) t'26
  let mut sc'31 := !t'28
  if !sc'31 then
    let t'29 ← PMem.ldF32 (fp + 0)
    let t'30 ← is_positive'float t'29
    sc'31 := !t'30
  if sc'31 then
    let t'32 := Int16.toUInt16 (Int32.toInt16 ((0 : Int32)))
    PMem.stU16 (0x135e8 : UInt64) /- &Copter::thrust_loss_check(...)::thrust_loss_counter -/ t'32
    return ()
  let t'33 ← PMem.ldU64 (this + 11168)
  let t'34 ← AC_AttitudeControl.get_att_error_angle_deg t'33
  let mut angle_error : Binary32 := t'34
  if (decide (angle_error ≥ (Binary32.ofBits 0x41f00000 /- 30 -/))) then
    let t'35 := Int16.toUInt16 (Int32.toInt16 ((0 : Int32)))
    PMem.stU16 (0x135e8 : UInt64) /- &Copter::thrust_loss_check(...)::thrust_loss_counter -/ t'35
    return ()
  let t'36 := (0x135e8 : UInt64) /- &Copter::thrust_loss_check(...)::thrust_loss_counter -/
  let t'37 ← PMem.ldU16 t'36
  let t'38 := (t'37 + 1)
  PMem.stU16 t'36 t'38
  let t'39 ← PMem.ldU16 (0x135e8 : UInt64) /- &Copter::thrust_loss_check(...)::thrust_loss_counter -/
  let t'40 ← AP_Scheduler.get_loop_rate_hz (this + 208)
  if (decide ((UInt32.toInt32 (UInt16.toUInt32 (t'39))) ≥ ((1 : Int32) * (UInt32.toInt32 (UInt16.toUInt32 (t'40)))))) then
    let t'41 := Int16.toUInt16 (Int32.toInt16 ((0 : Int32)))
    PMem.stU16 (0x135e8 : UInt64) /- &Copter::thrust_loss_check(...)::thrust_loss_counter -/ t'41
    let t'42 ← PMem.ldU64 (this + 9528)
    let t'43 ← AP_MotorsMatrix.get_lost_motor t'42
    PMem.stU64 (fp + 8) (Int64.toUInt64 (Int32.toInt64 (((UInt32.toInt32 (UInt8.toUInt32 (t'43))) + (1 : Int32)))))
    let t'44 ← Copter.gcs this
    GCS.send_text t'44 (0 : UInt32) (0x14510 : UInt64) /- "Potential Thrust Loss (%d)" -/ (fp + 8)
    let t'45 ← PMem.ldU64 (this + 9528)
    AP_Motors.set_thrust_boost t'45 true
  return ()

def Copter.thrust_loss_check (this : UInt64) : PMem.M Unit := do
  let fp ← PMem.enter 16
  let r ← Copter.thrust_loss_check.body fp this
  PMem.leave fp
  return r

/-- C++ `Copter::yaw_imbalance_check : void ()`, `crash_check.cpp:184-232`. -/
def Copter.yaw_imbalance_check.body (fp : UInt64) (this : UInt64) : PMem.M Unit := do
  let t'1 ← Copter.option_is_enabled (0x86d8 : UInt64) /- &copter -/ (2 : UInt32)
  if t'1 then
    return ()
  let t'2 ← PMem.ldU64 (this + 11168)
  let t'3 ← AC_AttitudeControl_Multi.get_rate_yaw_pid t'2
  let t'4 ← AC_PID.kI t'3
  discard <| PMem.memcpy (fp + 0) t'4 4
  let t'5 ← is_positive'AP_ParamT_float_AP_PARAM_FLOAT (fp + 0)
  if !t'5 then
    return ()
  let t'6 ← PMem.ldU64 (this + 9528)
  let t'7 ← AP_Motors.get_thrust_boost t'6
  if t'7 then
    PMem.stF32 (fp + 4) (Binary32.ofBits 0x00000000 /- 0 -/)
    DigitalLPF'float.reset (this + 11232) (fp + 4)
    return ()
  let t'8 ← PMem.ldU64 (this + 9528)
  let t'9 ← AP_Motors.armed t'8
  let mut sc'11 := !t'9
  if !sc'11 then
    let t'10 ← PMem.ldB ((this + 9448) + 7)
    sc'11 := t'10
  if sc'11 then
    PMem.stF32 (fp + 8) (Binary32.ofBits 0x00000000 /- 0 -/)
    DigitalLPF'float.reset (this + 11232) (fp + 8)
    return ()
  let t'12 ← PMem.ldB (this + 11229)
  if t'12 then
    PMem.stF32 (fp + 12) (Binary32.ofBits 0x00000000 /- 0 -/)
    DigitalLPF'float.reset (this + 11232) (fp + 12)
    return ()
  let t'13 ← PMem.ldU64 (this + 11168)
  let t'14 ← AC_AttitudeControl_Multi.get_rate_yaw_pid t'13
  let t'15 ← AC_PID.get_pid_info t'14
  let t'16 ← PMem.ldF32 (t'15 + 16)
  PMem.stF32 (fp + 16) t'16
  let t'17 ← PMem.ldU64 (this + 11168)
  let t'18 ← AC_AttitudeControl_Multi.get_rate_yaw_pid t'17
  let t'19 ← AC_PID.get_pid_info t'18
  let t'20 ← LowPassFilter'float.apply (this + 11232) (t'19 + 16) (this + 376)
  let mut I : Binary32 := (Binary32.abs t'20)
  let t'21 ← PMem.ldF32 (fp + 16)
  if (decide (I > (Binary32.abs t'21))) then
    DigitalLPF'float.reset (this + 11232) (fp + 16)
  let t'22 ← PMem.ldU64 (this + 11168)
  let t'23 ← AC_AttitudeControl_Multi.get_rate_yaw_pid t'22
  let t'24 ← AC_PID.imax t'23
  let mut I_max : Binary32 := t'24
  let t'25 ← is_positive'float I_max
  let mut sc'29 := t'25
  if sc'29 then
    let mut sc'28 := (decide (I > ((Binary32.ofBits 0x3f400000 /- 3/4 -/) * I_max)))
    if !sc'28 then
      let t'26 ← PMem.ldF32 (fp + 16)
      let t'27 ← is_equal'float_float t'26 I_max
      sc'28 := t'27
    sc'29 := sc'28
  if sc'29 then
    let mut now : UInt32 := ((← PMem.clock) / 1000).toUInt32
    let t'30 ← PMem.ldU32 (this + 11244)
    if (decide ((now - t'30) > (Int32.toUInt32 ((10000 : Int32))))) then
      PMem.stU32 (this + 11244) now
      PMem.stU64 (fp + 24) (Binary64.toBits (Binary32.toBinary64 ((I * (Int32.toBinary32 ((100 : Int32)))))))
      let t'31 ← Copter.gcs this
      GCS.send_text t'31 (0 : UInt32) (0x1452b : UInt64) /- "Yaw Imbalance %0.0f%%" -/ (fp + 24)
  return ()

def Copter.yaw_imbalance_check (this : UInt64) : PMem.M Unit := do
  let fp ← PMem.enter 32
  let r ← Copter.yaw_imbalance_check.body fp this
  PMem.leave fp
  return r

/-- C++ `Copter::update_land_and_crash_detectors : void ()`, `land_detector.cpp:16-33`. -/
def Copter.update_land_and_crash_detectors.body (fp : UInt64) (this : UInt64) : PMem.M Unit := do
  VehicleBridge.AP_AHRS.get_accel_ef'0 (this + 4080) (fp + 16)
  let t'1 := (fp + 16)
  Vector3'float.Vector3'4 (fp + 0) t'1
  let t'2 := ((fp + 0) + 8)
  let t'3 ← PMem.ldF32 t'2
  let t'4 := (t'3 + (Binary32.ofBits 0x411ce80a /- 122583127/12500000 -/))
  PMem.stF32 t'2 t'4
  let t'5 ← AP_Scheduler.get_loop_period_s (this + 208)
  PMem.stF32 (fp + 28) t'5
  LowPassFilter'Vector3_float.apply (this + 11116) (fp + 32) (fp + 0) (fp + 28)
  discard <| pure ((fp + 32))
  Copter.update_land_detector this
  Copter.crash_check this
  Copter.thrust_loss_check this
  Copter.yaw_imbalance_check this
  return ()

def Copter.update_land_and_crash_detectors (this : UInt64) : PMem.M Unit := do
  let fp ← PMem.enter 44
  let r ← Copter.update_land_and_crash_detectors.body fp this
  PMem.leave fp
  return r

/-- C++ `Copter::update_ekf_terrain_height_stable : void ()`, `baro_ground_effect.cpp:29-39`. -/
def Copter.update_ekf_terrain_height_stable (this : UInt64) : PMem.M Unit := do
  let t'1 ← Copter.position_ok this
  let mut sc'3 := !t'1
  if sc'3 then
    let t'2 ← Copter.ekf_has_relative_position this
    sc'3 := !t'2
  if sc'3 then
    VehicleBridge.AP_AHRS.set_terrain_hgt_stable'1 (this + 4080) false
    return ()
  let t'4 ← PMem.ldU64 (this + 9488)
  let t'5 ← vcall'Mode'is_taking_off'17 t'4
  let mut sc'8 := t'5
  if !sc'8 then
    let t'6 ← PMem.ldU64 (this + 9488)
    let t'7 ← vcall'Mode'is_landing'15 t'6
    sc'8 := t'7
  VehicleBridge.AP_AHRS.set_terrain_hgt_stable'1 (this + 4080) sc'8
  return ()

/-- C++ `Copter::throttle_loop : void ()`, `Copter.cpp:595-616`. -/
def Copter.throttle_loop (this : UInt64) : PMem.M Unit := do
  Copter.update_throttle_mix this
  Copter.update_auto_armed this
  Copter.update_ekf_terrain_height_stable this
  return ()

/-- C++ `Copter::auto_disarm_check : void ()`, `motors.cpp:11-58`. -/
def Copter.auto_disarm_check (this : UInt64) : PMem.M Unit := do
  let mut tnow_ms : UInt32 := ((← PMem.clock) / 1000).toUInt32
  let t'1 ← AP_ParamT'signed_char_1.operator_const_signed_char__ ((this + 6776) + 50)
  let t'2 ← PMem.ldI8 t'1
  let t'3 ← constrain_int16 (Int8.toInt16 (t'2)) (Int32.toInt16 ((0 : Int32))) (Int32.toInt16 ((127 : Int32)))
  let mut disarm_delay_ms : UInt32 := Int32.toUInt32 (((1000 : Int32) * (Int16.toInt32 (t'3))))
  let t'4 ← PMem.ldU64 (this + 9528)
  let t'5 ← AP_Motors.armed t'4
  let mut sc'8 := ((!t'5) || (disarm_delay_ms == (Int32.toUInt32 ((0 : Int32)))))
  if !sc'8 then
    let t'6 ← PMem.ldU64 (this + 9488)
    let t'7 ← vcall'Mode'mode_number'1 t'6
    sc'8 := (t'7 == (18 : UInt8))
  if sc'8 then
    PMem.stU32 (0x134c0 : UInt64) /- &auto_disarm_begin -/ tnow_ms
    return ()
  let t'9 ← PMem.ldU64 (this + 9528)
  let t'10 ← AP_Motors.get_desired_spool_state t'9
  let mut sc'13 := (decide (t'10 > (1 : UInt8)))
  if !sc'13 then
    let t'11 ← PMem.ldU64 (this + 9528)
    let t'12 ← AP_Motors.get_spool_state t'11
    sc'13 := (decide (t'12 > (1 : UInt8)))
  if sc'13 then
    PMem.stU32 (0x134c0 : UInt64) /- &auto_disarm_begin -/ tnow_ms
    return ()
  let t'14 ← PMem.ldB ((this + 9448) + 18)
  let mut sc'17 := t'14
  if sc'17 then
    let t'15 ← PMem.ldU64 (this + 9528)
    let t'16 ← AP_Motors.get_interlock t'15
    sc'17 := !t'16
  let mut sc'19 := sc'17
  if !sc'19 then
    let t'18 ← SRV_Channels.get_emergency_stop
    sc'19 := t'18
  if sc'19 then
    let t'20 := (disarm_delay_ms / (Int32.toUInt32 ((2 : Int32))))
    disarm_delay_ms := t'20
  else
    let t'21 ← AP_ParamT'unsigned_short_2.operator_const_unsigned_short__ ((this + 6776) + 8)
    let t'22 ← PMem.ldU16 t'21
    let mut sprung_throttle_stick : Bool := (((UInt32.toInt32 (UInt16.toUInt32 (t'22))) &&& ((1 : Int32) <<< (0 : Int32))) != (0 : Int32))
    let mut thr_low : Bool := default  -- uninitialized in C
    let t'23 ← PMem.ldU64 (this + 9488)
    let t'24 ← vcall'Mode'has_manual_throttle'3 t'23
    if (t'24 || (!sprung_throttle_stick)) then
      let t'25 ← PMem.ldB ((this + 9448) + 15)
      thr_low := t'25
    else
      let t'26 ← Copter.get_throttle_mid this
      let t'27 ← AP_ParamT'short_2.operator_const_short__ ((this + 6776) + 30)
      let t'28 ← PMem.ldI16 t'27
      let mut deadband_top : Binary32 := Int32.toBinary32 (((Int16.toInt32 (t'26)) + (Int16.toInt32 (t'28))))
      let t'29 ← PMem.ldU64 (this + 8616)
      let t'30 ← RC_Channel.get_control_in t'29
      let t'31 := (decide ((Int32.toBinary32 ((Int16.toInt32 (t'30)))) ≤ deadband_top))
      thr_low := t'31
    let mut sc'33 := !thr_low
    if !sc'33 then
      let t'32 ← PMem.ldB ((this + 9448) + 7)
      sc'33 := !t'32
    if sc'33 then
      PMem.stU32 (0x134c0 : UInt64) /- &auto_disarm_begin -/ tnow_ms
  let t'34 ← PMem.ldU32 (0x134c0 : UInt64) /- &auto_disarm_begin -/
  if (decide ((tnow_ms - t'34) ≥ disarm_delay_ms)) then
    let t'35 ← AP_Arming_Copter.disarm (this + 8768) (17 : Int32) true
    discard <| pure (t'35)
    PMem.stU32 (0x134c0 : UInt64) /- &auto_disarm_begin -/ tnow_ms
  return ()

/-- C++ `Copter::read_barometer : void ()`, `sensors.cpp:4-9`. -/
def Copter.read_barometer (this : UInt64) : PMem.M Unit := do
  VehicleBridge.AP_Baro.update'0 (this + 1200)
  worldOutputs'drain
  let t'1 ← VehicleBridge.AP_Baro.get_altitude'0 (this + 1200)
  PMem.stF32 (this + 11112) t'1
  return ()

/-- C++ `Copter::update_altitude : void ()`, `Copter.cpp:889-907`. -/
def Copter.update_altitude (this : UInt64) : PMem.M Unit := do
  Copter.read_barometer this
  return ()

/-- C++ `Copter::failsafe_gcs_off_event : void ()`, `events.cpp:236-240`. -/
def Copter.failsafe_gcs_off_event.body (fp : UInt64) (this : UInt64) : PMem.M Unit := do
  let t'1 ← Copter.gcs this
  GCS.send_text t'1 (4 : UInt32) (0x14753 : UInt64) /- "GCS Failsafe Cleared" -/ (fp + 0)
  return ()

def Copter.failsafe_gcs_off_event (this : UInt64) : PMem.M Unit := do
  let fp ← PMem.enter 8
  let r ← Copter.failsafe_gcs_off_event.body fp this
  PMem.leave fp
  return r

/-- C++ `Copter::one_hz_loop : void ()`, `Copter.cpp:779-834`. -/
def Copter.one_hz_loop (this : UInt64) : PMem.M Unit := do
  let t'1 ← PMem.ldU64 (this + 9528)
  let t'2 ← AP_Motors.armed t'1
  if !t'2 then
    Copter.update_using_interlock this
    let t'3 ← AP_ParamTBase'signed_char_1.get ((this + 6840) + 12)
    let t'4 ← PMem.ldI8 t'3
    let t'5 ← AP_ParamTBase'signed_char_1.get ((this + 6776) + 49)
    let t'6 ← PMem.ldI8 t'5
    let t'7 ← PMem.ldU64 (this + 9528)
    AP_MotorsMatrix.set_frame_class_and_type t'7 (Int32.toUInt32 (Int8.toInt32 (t'4))) (Int32.toUInt32 (Int8.toInt32 (t'6)))
    let t'8 ← PMem.ldU64 (this + 9528)
    AP_MotorsMulticopter.update_throttle_range t'8
  let t'9 ← AP.srv
  SRV_Channels.enable_aux_servos t'9
  let t'10 ← PMem.ldB ((this + 9448) + 7)
  let t'11 := !t'10
  PMem.stB ((0xccc0 : UInt64) /- &AP_Notify::flags -/ + 5) t'11
  let t'12 ← PMem.ldB (this + 13209)
  if !t'12 then
    let t'13 ← AP.scheduler
    let t'14 ← AP_Scheduler.get_filtered_loop_rate_hz t'13
    let t'15 ← PMem.ldU64 (this + 11168)
    AC_AttitudeControl_Multi.set_notch_sample_rate t'15 t'14
  let t'16 ← AP.scheduler
  let t'17 ← AP_Scheduler.get_filtered_loop_rate_hz t'16
  let t'18 ← PMem.ldU64 (this + 11184)
  let t'19 ← AC_PosControl.D_get_accel_pid t'18
  AC_PID.set_notch_sample_rate t'19 t'17
  return ()

/-- C++ `Copter::failsafe_ekf_off_event : void ()`, `ekf_check.cpp:219-232`. -/
def Copter.failsafe_ekf_off_event.body (fp : UInt64) (this : UInt64) : PMem.M Unit := do
  let t'1 ← PMem.ldBits (this + 9508) 74 1
  if !((UInt64.toUInt8 (t'1)) != (0 : UInt8)) then
    return ()
  let t'2 := if false then (1 : UInt8) else (0 : UInt8)
  PMem.stBits (this + 9508) 74 1 (UInt8.toUInt64 (t'2))
  let t'3 ← PMem.ldB ((0xccc0 : UInt64) /- &AP_Notify::flags -/ + 13)
  if t'3 then
    PMem.stB ((0xccc0 : UInt64) /- &AP_Notify::flags -/ + 13) false
    let t'4 ← Copter.gcs this
    GCS.send_text t'4 (2 : UInt32) (0x1459e : UInt64) /- "EKF Failsafe Cleared" -/ (fp + 0)
  return ()

def Copter.failsafe_ekf_off_event (this : UInt64) : PMem.M Unit := do
  let fp ← PMem.enter 8
  let r ← Copter.failsafe_ekf_off_event.body fp this
  PMem.leave fp
  return r

/-- C++ `Copter::check_vibration : void ()`, `ekf_check.cpp:266-325`. -/
def Copter.check_vibration.body (fp : UInt64) (this : UInt64) : PMem.M Unit := do
  let mut now : UInt32 := ((← PMem.clock) / 1000).toUInt32
  let mut innovation_checks_valid : Bool := true
  Vector3'float.Vector3'2 (fp + 0)
  Vector3'float.Vector3'2 (fp + 16)
  Vector3'float.Vector3'2 (fp + 32)
  let t'1 ← VehicleBridge.AP_AHRS.get_innovations'5 (this + 4080) (fp + 0) (fp + 16) (fp + 32) (fp + 48) (fp + 56)
  if !t'1 then
    innovation_checks_valid := false
  let t'2 ← PMem.ldF32 ((fp + 0) + 8)
  let t'3 ← is_positive'float t'2
  let mut sc'6 := t'3
  if sc'6 then
    let t'4 ← PMem.ldF32 ((fp + 16) + 8)
    let t'5 ← is_positive'float t'4
    sc'6 := t'5
  let mut innov_velD_posD_positive : Bool := sc'6
  let t'7 ← PMem.ldB (this + 8888)
  if !t'7 then
    innovation_checks_valid := false
  let t'8 ← VehicleBridge.AP_AHRS.is_vibration_affected'0 (this + 4080)
  let mut is_vibration_affected : Bool := t'8
  let mut sc'11 := (innovation_checks_valid && innov_velD_posD_positive)
  if sc'11 then
    let t'9 ← DigitalLPF'float.get (this + 8876)
    let t'10 ← PMem.ldF32 t'9
    sc'11 := (decide (t'10 > (Binary32.ofBits 0x3f800000 /- 1 -/)))
  let mut bad_vibe_detected : Bool := (sc'11 || is_vibration_affected)
  let t'12 ← AP_ParamT'signed_char_1.operator_const_signed_char__ ((this + 6840) + 1648)
  let t'13 ← PMem.ldI8 t'12
  let mut sc'16 := (((Int8.toInt32 (t'13)) == (1 : Int32)) && bad_vibe_detected)
  if sc'16 then
    let t'14 ← PMem.ldU64 (this + 9528)
    let t'15 ← AP_Motors.armed t'14
    sc'16 := t'15
  let mut sc'19 := sc'16
  if sc'19 then
    let t'17 ← PMem.ldU64 (this + 9488)
    let t'18 ← vcall'Mode'has_manual_throttle'3 t'17
    sc'19 := !t'18
  let mut do_bad_vibe_actions : Bool := sc'19
  let t'20 ← PMem.ldB (this + 8852)
  if !t'20 then
    if !do_bad_vibe_actions then
      PMem.stU32 ((this + 8852) + 4) now
    let t'21 ← PMem.ldU32 ((this + 8852) + 4)
    if (decide ((now - t'21) > (Int32.toUInt32 ((1000 : Int32))))) then
      let t'22 := Int32.toUInt32 ((0 : Int32))
      PMem.stU32 ((this + 8852) + 8) t'22
      PMem.stB (this + 8852) true
      let t'23 ← PMem.ldU64 (this + 11184)
      AC_PosControl.set_vibe_comp t'23 true
      let t'24 ← Copter.gcs this
      GCS.send_text t'24 (2 : UInt32) (0x145b3 : UInt64) /- "Vibration compensation ON" -/ (fp + 64)
  else
    if do_bad_vibe_actions then
      PMem.stU32 ((this + 8852) + 8) now
    let t'25 ← PMem.ldU32 ((this + 8852) + 8)
    if (decide ((now - t'25) > (Int32.toUInt32 ((15000 : Int32))))) then
      let t'26 := Int32.toUInt32 ((0 : Int32))
      PMem.stU32 ((this + 8852) + 4) t'26
      PMem.stB (this + 8852) false
      let t'27 ← PMem.ldU64 (this + 11184)
      AC_PosControl.set_vibe_comp t'27 false
      let t'28 := Int32.toUInt32 ((0 : Int32))
      PMem.stU32 ((this + 8852) + 8) t'28
      let t'29 ← Copter.gcs this
      GCS.send_text t'29 (2 : UInt32) (0x145cd : UInt64) /- "Vibration compensation OFF" -/ (fp + 72)
  return ()

def Copter.check_vibration (this : UInt64) : PMem.M Unit := do
  let fp ← PMem.enter 80
  let r ← Copter.check_vibration.body fp this
  PMem.leave fp
  return r

/-- C++ `Copter::gpsglitch_check : void ()`, `events.cpp:310-325`. -/
def Copter.gpsglitch_check.body (fp : UInt64) (this : UInt64) : PMem.M Unit := do
  let t'1 ← VehicleBridge.ahrs'0
  let t'2 ← VehicleBridge.AP_AHRS.configured_backend_has_status'1 t'1 (16384 : Int32)
  let mut gps_glitching : Bool := t'2
  let t'3 ← PMem.ldB ((this + 9448) + 17)
  if ((if t'3 then (1 : Int32) else (0 : Int32)) != (if gps_glitching then (1 : Int32) else (0 : Int32))) then
    PMem.stB ((this + 9448) + 17) gps_glitching
    if gps_glitching then
      let t'4 ← Copter.gcs this
      GCS.send_text t'4 (2 : UInt32) (0x147ac : UInt64) /- "GPS Glitch or Compass error" -/ (fp + 0)
    else
      let t'5 ← Copter.gcs this
      GCS.send_text t'5 (2 : UInt32) (0x147c8 : UInt64) /- "Glitch cleared" -/ (fp + 8)
  return ()

def Copter.gpsglitch_check (this : UInt64) : PMem.M Unit := do
  let fp ← PMem.enter 16
  let r ← Copter.gpsglitch_check.body fp this
  PMem.leave fp
  return r

/-- C++ `Copter::takeoff_check : void ()`, `takeoff_check.cpp:8-62`. -/
def Copter.takeoff_check.body (fp : UInt64) (this : UInt64) : PMem.M Unit := do
  let mut now_ms : UInt32 := ((← PMem.clock) / 1000).toUInt32
  let t'1 ← PMem.ldU64 (this + 9528)
  let t'2 ← AP_Motors.get_spoolup_block t'1
  if !t'2 then
    PMem.stU32 (this + 8896) now_ms
    return ()
  let t'3 ← PMem.ldB ((this + 9448) + 7)
  if !t'3 then
    let t'4 ← PMem.ldU64 (this + 9528)
    AP_Motors.set_spoolup_block t'4 false
    return ()
  let mut motor_check_passed : Bool := true
  let mut load_adequate : Bool := true
  let t'5 ← PMem.ldU64 ((0xba88 : UInt64) /- &hal -/ + 88)
  let t'6 ← PMem.halDev "AP_HAL::Util::get_system_load" t'5 #[(fp + 0), (fp + 8)]
  if (t'6 != 0) then
    let t'7 ← PMem.ldF32 (fp + 0)
    let mut sc'9 := (decide (t'7 > (Binary32.ofBits 0x42be0000 /- 95 -/)))
    if !sc'9 then
      let t'8 ← PMem.ldF32 (fp + 8)
      sc'9 := (decide (t'8 > (Binary32.ofBits 0x42c70000 /- 199/2 -/)))
    if sc'9 then
      load_adequate := false
  if (motor_check_passed && load_adequate) then
    let t'10 ← PMem.ldU64 (this + 9528)
    AP_Motors.set_spoolup_block t'10 false
    return ()
  let t'11 ← PMem.ldU32 (this + 8896)
  if (decide ((now_ms - t'11) > (Int32.toUInt32 ((2000 : Int32))))) then
    PMem.stU32 (this + 8896) now_ms
    let mut prefix_str : UInt64 := (0x14dcd : UInt64) /- "Takeoff blocked:" -/
    if !load_adequate then
      PMem.stU64 (fp + 16) prefix_str
      let t'12 ← PMem.ldF32 (fp + 0)
      PMem.stU64 (fp + 24) (Binary64.toBits (Binary32.toBinary64 (t'12)))
      let t'13 ← Copter.gcs this
      GCS.send_text t'13 (2 : UInt32) (0x14dde : UInt64) /- "%s CPU overload (%4.1f%%)" -/ (fp + 16)
  return ()

def Copter.takeoff_check (this : UInt64) : PMem.M Unit := do
  let fp ← PMem.enter 32
  let r ← Copter.takeoff_check.body fp this
  PMem.leave fp
  return r

/-- C++ `Copter::lost_vehicle_check : void ()`, `motors.cpp:132-157`. -/
def Copter.lost_vehicle_check.body (fp : UInt64) (this : UInt64) : PMem.M Unit := do
  let t'1 ← rc
  let t'2 ← RC_Channels.find_channel_for_option t'1 (30 : Int32)
  if (t'2 != 0) then
    return ()
  let t'3 ← PMem.ldB ((this + 9448) + 15)
  let mut sc'6 := t'3
  if sc'6 then
    let t'4 ← PMem.ldU64 (this + 9528)
    let t'5 ← AP_Motors.armed t'4
    sc'6 := !t'5
  let mut sc'9 := sc'6
  if sc'9 then
    let t'7 ← PMem.ldU64 (this + 8600)
    let t'8 ← RC_Channel.get_control_in t'7
    sc'9 := (decide ((Int16.toInt32 (t'8)) > (4000 : Int32)))
  let mut sc'12 := sc'9
  if sc'12 then
    let t'10 ← PMem.ldU64 (this + 8608)
    let t'11 ← RC_Channel.get_control_in t'10
    sc'12 := (decide ((Int16.toInt32 (t'11)) > (4000 : Int32)))
  if sc'12 then
    let t'13 ← PMem.ldU8 (0x135c8 : UInt64) /- &Copter::lost_vehicle_check(...)::soundalarm_counter -/
    if (decide ((UInt32.toInt32 (UInt8.toUInt32 (t'13))) ≥ (10 : Int32))) then
      let t'14 ← PMem.ldB ((0xccc0 : UInt64) /- &AP_Notify::flags -/ + 23)
      if ((if t'14 then (1 : Int32) else (0 : Int32)) == (if false then (1 : Int32) else (0 : Int32))) then
        PMem.stB ((0xccc0 : UInt64) /- &AP_Notify::flags -/ + 23) true
        let t'15 ← Copter.gcs this
        GCS.send_text t'15 (5 : UInt32) (0x14d46 : UInt64) /- "Locate Copter alarm" -/ (fp + 0)
    else
      let t'16 := (0x135c8 : UInt64) /- &Copter::lost_vehicle_check(...)::soundalarm_counter -/
      let t'17 ← PMem.ldU8 t'16
      let t'18 := (t'17 + 1)
      PMem.stU8 t'16 t'18
  else
    let t'19 := Int8.toUInt8 (Int32.toInt8 ((0 : Int32)))
    PMem.stU8 (0x135c8 : UInt64) /- &Copter::lost_vehicle_check(...)::soundalarm_counter -/ t'19
    let t'20 ← PMem.ldB ((0xccc0 : UInt64) /- &AP_Notify::flags -/ + 23)
    if ((if t'20 then (1 : Int32) else (0 : Int32)) == (if true then (1 : Int32) else (0 : Int32))) then
      PMem.stB ((0xccc0 : UInt64) /- &AP_Notify::flags -/ + 23) false
  return ()

def Copter.lost_vehicle_check (this : UInt64) : PMem.M Unit := do
  let fp ← PMem.enter 8
  let r ← Copter.lost_vehicle_check.body fp this
  PMem.leave fp
  return r

/-- C++ `Copter::failsafe_check : void ()`, `failsafe.cpp:35-72`. -/
def Copter.failsafe_check (this : UInt64) : PMem.M Unit := do
  let mut tnow : UInt32 := (← PMem.clock).toUInt32
  let t'1 ← AP_Scheduler.ticks (this + 208)
  let mut ticks : UInt16 := t'1
  let t'2 ← PMem.ldU16 (0xeb50 : UInt64) /- &failsafe_last_ticks -/
  if ((UInt32.toInt32 (UInt16.toUInt32 (ticks))) != (UInt32.toInt32 (UInt16.toUInt32 (t'2)))) then
    PMem.stU16 (0xeb50 : UInt64) /- &failsafe_last_ticks -/ ticks
    PMem.stU32 (0xce30 : UInt64) /- &failsafe_last_timestamp -/ tnow
    let t'3 ← PMem.ldB (0xeb58 : UInt64) /- &in_failsafe -/
    if t'3 then
      PMem.stB (0xeb58 : UInt64) /- &in_failsafe -/ false
    return ()
  let t'4 ← PMem.ldB (0xeb58 : UInt64) /- &in_failsafe -/
  let mut sc'6 := !t'4
  if sc'6 then
    let t'5 ← PMem.ldB (0xce28 : UInt64) /- &failsafe_enabled -/
    sc'6 := t'5
  let mut sc'8 := sc'6
  if sc'8 then
    let t'7 ← PMem.ldU32 (0xce30 : UInt64) /- &failsafe_last_timestamp -/
    sc'8 := (decide ((tnow - t'7) > (Int32.toUInt32 ((2000000 : Int32)))))
  if sc'8 then
    PMem.stB (0xeb58 : UInt64) /- &in_failsafe -/ true
    let t'9 ← PMem.ldU64 (this + 9528)
    let t'10 ← AP_Motors.armed t'9
    if t'10 then
      let t'11 ← PMem.ldU64 (this + 9528)
      AP_MotorsMulticopter.output_min t'11
  let t'12 ← PMem.ldB (0xce28 : UInt64) /- &failsafe_enabled -/
  let mut sc'14 := t'12
  if sc'14 then
    let t'13 ← PMem.ldB (0xeb58 : UInt64) /- &in_failsafe -/
    sc'14 := t'13
  let mut sc'16 := sc'14
  if sc'16 then
    let t'15 ← PMem.ldU32 (0xce30 : UInt64) /- &failsafe_last_timestamp -/
    sc'16 := (decide ((tnow - t'15) > (Int32.toUInt32 ((1000000 : Int32)))))
  if sc'16 then
    PMem.stU32 (0xce30 : UInt64) /- &failsafe_last_timestamp -/ tnow
    let t'17 ← PMem.ldU64 (this + 9528)
    let t'18 ← AP_Motors.armed t'17
    if t'18 then
      let t'19 ← PMem.ldU64 (this + 9528)
      AP_Motors.armed'2 t'19 false
      let t'20 ← PMem.ldU64 (this + 9528)
      AP_MotorsMulticopter.output t'20
  return ()

/-- C++ `Copter::Copter : void ()`, `Copter.cpp:955-966`. -/
def Copter.Copter.body (fp : UInt64) (this : UInt64) : PMem.M Unit := do
  AP_Vehicle.AP_Vehicle this
  Parameters.Parameters (this + 6776)
  ParametersG2.ParametersG2 (this + 6840)
  AP_SurfaceDistance.AP_SurfaceDistance (this + 8632) (25 : UInt8) (UInt32.toUInt8 ((0 : UInt32))) ((this + 6840) + 1712)
  AP_SurfaceDistance.AP_SurfaceDistance (this + 8696) (24 : UInt8) (UInt32.toUInt8 ((1 : UInt32))) ((this + 6840) + 1712)
  AP_Arming_Copter.AP_Arming_Copter (this + 8768)
  AP_ExternalControl_Copter.AP_ExternalControl_Copter (this + 8840)
  PMem.stF32 (fp + 0) (Binary32.ofBits 0x40a00000 /- 5 -/)
  LowPassFilter'float.LowPassFilter'2 (this + 8864) (fp + 0)
  PMem.stF32 (fp + 4) (Binary32.ofBits 0x40a00000 /- 5 -/)
  LowPassFilter'float.LowPassFilter'2 (this + 8876) (fp + 4)
  GCS_Copter.GCS_Copter (this + 8904)
  PMem.stU64 (this + 9488) (this + 13096)
  RCMapper.RCMapper (this + 9496)
  PMem.stF32 (this + 9556) (Binary32.ofBits 0x3f800000 /- 1 -/)
  PMem.stF32 (this + 9568) (Binary64.toBinary32 ((Binary64.ofBits 0x3ff0000000000000 /- 1 -/)))
  PMem.stU64 (fp + 24) this
  PMem.stU64 (fp + 32) (0x7e000060 : UInt64)
  let t'1 := (fp + 24)
  Functor'void_const_char_const_signed_char.Functor (fp + 8) t'1
  AP_BattMonitor.AP_BattMonitor (this + 9584) (Int32.toUInt32 (((1 : Int32) <<< (9 : Int32)))) (fp + 8) (0x138e0 : UInt64) /- &Copter::_failsafe_priorities -/
  PMem.stF32 (fp + 40) (Binary32.ofBits 0x3f800000 /- 1 -/)
  LowPassFilter'Vector3_float.LowPassFilter (this + 11116) (fp + 40)
  PMem.stF32 (fp + 44) (Binary32.ofBits 0x3f800000 /- 1 -/)
  LowPassFilter'float.LowPassFilter'2 (this + 11136) (fp + 44)
  Location.Location (this + 11148)
  AP_Param.AP_Param (this + 11228) (0x1000 : UInt64) /- &Copter::var_info -/
  Copter.AHRSTrimming.AHRSTrimming (this + 11230)
  PMem.stF32 (fp + 48) (Binary32.ofBits 0x3d4ccccd /- 500000007/10000000000 -/)
  LowPassFilter'float.LowPassFilter'2 (this + 11232) (fp + 48)
  Mode.Mode (this + 11256)
  Mode.Mode (this + 11368)
  PMem.stU64 (fp + 72) (this + 11368)
  PMem.stU64 (fp + 80) (0x7e000070 : UInt64)
  let t'2 := (fp + 72)
  Functor'bool_const_AP_Mission_Mission_Command.Functor (fp + 56) t'2
  PMem.stU64 (fp + 104) (this + 11368)
  PMem.stU64 (fp + 112) (0x7e000080 : UInt64)
  let t'3 := (fp + 104)
  Functor'bool_const_AP_Mission_Mission_Command.Functor (fp + 88) t'3
  PMem.stU64 (fp + 136) (this + 11368)
  PMem.stU64 (fp + 144) (0x7e000090 : UInt64)
  let t'4 := (fp + 136)
  Functor'void.Functor'2 (fp + 120) t'4
  AP_Mission.AP_Mission ((this + 11368) + 112) (fp + 56) (fp + 88) (fp + 120)
  AP_Mission.Mission_Command.Mission_Command (((this + 11368) + 728) + 8)
  AP_Mission.Mission_Command.Mission_Command (((this + 11368) + 728) + 36)
  AP_Mission.Mission_Command.Mission_Command (((this + 11368) + 728) + 64)
  PMem.stU8 ((this + 11368) + 820) (0 : UInt8)
  PMem.stBits ((this + 11368) + 828) 0 1 (if (1 : Int32) != (0 : Int32) then (1 : UInt64) else 0)
  PMem.stBits ((this + 11368) + 828) 1 1 (if (1 : Int32) != (0 : Int32) then (1 : UInt64) else 0)
  PMem.stBits ((this + 11368) + 828) 2 1 (if (1 : Int32) != (0 : Int32) then (1 : UInt64) else 0)
  PMem.stI32 ((this + 11368) + 856) (0 : Int32)
  Mode.Mode (this + 12280)
  Mode.Mode (this + 12400)
  PMem.stB ((this + 12400) + 112) false
  Mode.Mode (this + 12520)
  PMem.stU8 ((this + 12520) + 112) (Int8.toUInt8 (Int32.toInt8 ((0 : Int32))))
  ModeLand.ModeLand (this + 12640)
  Mode.Mode (this + 12776)
  ModeRTL.ModeRTL (this + 12888)
  Mode.Mode (this + 13096)
  return ()

def Copter.Copter (this : UInt64) : PMem.M Unit := do
  let fp ← PMem.enter 152
  let r ← Copter.Copter.body fp this
  PMem.leave fp
  return r

end Vehicle_lib
