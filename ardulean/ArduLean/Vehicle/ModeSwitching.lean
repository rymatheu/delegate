import ArduLean.Runtime.Bridge
import ArduLean.Vehicle.libraries.AP_Math.AP_Math
import ArduLean.Vehicle.libraries.Filter.Filter
import ArduLean.Vehicle.libraries.AP_Param.AP_Param
import ArduLean.Vehicle.libraries.AC_PID.AC_PID
import ArduLean.Vehicle.libraries.AC_AttitudeControl.AC_AttitudeControl
import ArduLean.Vehicle.libraries.AC_WPNav.AC_WPNav
import ArduLean.Vehicle.libraries.AP_Mission.AP_Mission
import ArduLean.Vehicle.libraries.RC_Channel.RC_Channel
import ArduLean.Vehicle.libraries.AP_Arming.AP_Arming
import ArduLean.Vehicle.ArduCopter.ArduCopter
import ArduLean.Vehicle.Dispatch
import ArduLean.Vehicle.libraries.AP_Motors.AP_Motors
import ArduLean.Vehicle.libraries.AP_Common.AP_Common
import ArduLean.Vehicle.libraries.GCS_MAVLink.GCS_MAVLink
import ArduLean.Vehicle.libraries.AP_BattMonitor.AP_BattMonitor
import ArduLean.Vehicle.libraries.AP_Vehicle.AP_Vehicle
import ArduLean.Vehicle.mavlink.mavlink
import ArduLean.Vehicle.libraries.SRV_Channel.SRV_Channel
import ArduLean.Vehicle.libraries.AP_Math.AP_Math_2
import ArduLean.Vehicle.libraries.Filter.Filter_2
import ArduLean.Vehicle.libraries.AP_Param.AP_Param_2
import ArduLean.Vehicle.libraries.AC_AttitudeControl.AC_AttitudeControl_2
import ArduLean.Vehicle.libraries.AC_WPNav.AC_WPNav_2
import ArduLean.Vehicle.libraries.AP_Mission.AP_Mission_2
import ArduLean.Vehicle.libraries.RC_Channel.RC_Channel_2
import ArduLean.Vehicle.ArduCopter.ArduCopter_2
import ArduLean.Vehicle.libraries.AP_Motors.AP_Motors_2
import ArduLean.Vehicle.libraries.GCS_MAVLink.GCS_MAVLink_2
import ArduLean.Vehicle.libraries.AP_BattMonitor.AP_BattMonitor_2
import ArduLean.Vehicle.libraries.AP_Vehicle.AP_Vehicle_2
import ArduLean.Vehicle.libraries.AP_Mission.AP_Mission_3
import ArduLean.Vehicle.World
import ArduLean.Vehicle.ArduCopter.ArduCopter_3
import ArduLean.Vehicle.Dispatch_3
import ArduLean.Vehicle.Arming

/-!
Cross-library module `ModeSwitching`: mode changes: Copter::set_mode and the recursive component around it (mode entry, mission command start, failsafe events, RC auxiliary functions), the mission's callbacks, the battery failsafe. It belongs to the top of the call graph, where ArduPilot's libraries call each other in a cycle, so it cannot be cut by library. Largest functions: `Copter.set_mode`, `_AutoTakeoff.run`, `RC_Channel.do_aux_function`, `GCS_MAVLINK.handle_command_int_packet`, `ModeAuto.loiter_to_alt_run`, `Copter.ekf_check`, `AP_BattMonitor.check_failsafes`, `Copter.failsafe_gcs_on_event`, `ModeRTL.descent_run`, `ModeAuto.circle_start`. Sources: `ArduCopter/events.cpp`, `ArduCopter/mode_auto.cpp`, `libraries/GCS_MAVLink/GCS_Common.cpp`, `libraries/RC_Channel/RC_Channel.cpp`, `ArduCopter/mode_rtl.cpp`, `libraries/AP_HAL/utility/functor.h`, `libraries/AP_Mission/AP_Mission.cpp`, `ArduCopter/takeoff.cpp` and 16 more.

Items of `lean/Vehicle_lib.lean` (the vehicle translation), unchanged; placed by `tools/split_modules.py` (`ArduLean/Vehicle/INDEX.md`).
-/

open FloatLib.Floats (Binary32 Binary64)

set_option linter.unusedVariables false
set_option linter.unreachableTactic false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false

namespace Vehicle_lib

/-- C++ `RC_Channel::do_aux_function_armdisarm : void (const AuxSwitchPos)`, `RC_Channel.cpp:1070-1084`. -/
def RC_Channel.do_aux_function_armdisarm (this : UInt64) (ch_flag : UInt8) : PMem.M Unit := do
  let mut ch_flag := ch_flag
  let sw'1 := ch_flag
  if sw'1 == (2 : UInt8) then
    let t'2 ← AP.arming
    let t'3 ← AP_Arming_Copter.arm t'2 (2 : Int32) true
    discard <| pure (t'3)
  else if sw'1 == (1 : UInt8) then
    pure ()
  else if sw'1 == (0 : UInt8) then
    let t'4 ← AP.arming
    let t'5 ← AP_Arming_Copter.disarm t'4 (2 : Int32) true
    discard <| pure (t'5)
  else
    pure ()
  return ()

/-- C++ `RC_Channel::do_aux_function : bool (const AuxFuncTrigger &)`, `RC_Channel.cpp:1503-2044`. -/
def RC_Channel.do_aux_function.body (fp : UInt64) (this : UInt64) (trigger : UInt64) : PMem.M Bool := do
  let ch_option : UInt64 := trigger
  let ch_flag : UInt64 := (trigger + 4)
  for _ in [0:1] do
    let t'1 ← PMem.ldI32 ch_option
    let sw'2 := t'1
    if sw'2 == (46 : Int32) then
      let t'3 ← PMem.ldU8 ch_flag
      RC_Channel.do_aux_function_rc_override_enable this t'3
    else if sw'2 == (40 : Int32) then
      let t'4 ← PMem.ldU8 ch_flag
      RC_Channel.do_aux_function_avoid_proximity this t'4
    else if sw'2 == (58 : Int32) then
      let t'5 ← PMem.ldU8 ch_flag
      RC_Channel.do_aux_function_clear_wp this t'5
    else if sw'2 == (24 : Int32) then
      let t'6 ← PMem.ldU8 ch_flag
      RC_Channel.do_aux_function_mission_reset this t'6
    else if sw'2 == (162 : Int32) then
      let t'7 ← PMem.ldU8 ch_flag
      RC_Channel.do_aux_function_fft_notch_tune this t'7
    else if sw'2 == (172 : Int32) then
      let t'8 ← PMem.ldU8 ch_flag
      if (t'8 != (1 : UInt8)) then
        let t'9 ← PMem.ldU8 ch_flag
        let t'10 ← AP.battery
        AP_BattMonitor.set_powered_state_to_all t'10 (t'9 == (2 : UInt8))
    else if sw'2 == (30 : Int32) then
      let t'11 ← PMem.ldU8 ch_flag
      RC_Channel.do_aux_function_lost_vehicle_sound this t'11
    else if sw'2 == (153 : Int32) then
      let t'12 ← PMem.ldU8 ch_flag
      RC_Channel.do_aux_function_armdisarm this t'12
    else if sw'2 == (81 : Int32) then
      let t'13 ← PMem.ldU8 ch_flag
      if (t'13 == (2 : UInt8)) then
        let t'14 ← AP.arming
        let t'15 ← AP_Arming_Copter.disarm t'14 (2 : Int32) true
        discard <| pure (t'15)
    else if sw'2 == (62 : Int32) then
      let t'16 ← PMem.ldU8 ch_flag
      if (t'16 == (2 : UInt8)) then
        let t'17 ← VehicleBridge.compass'0
        let compass : UInt64 := t'17
        VehicleBridge.Compass.set_learn_type'2 compass (3 : Int32) false
        worldOutputs'drain
    else if sw'2 == (65 : Int32) then
      let t'18 ← PMem.ldU8 ch_flag
      let t'19 ← VehicleBridge.gps'0
      VehicleBridge.AP_GPS.force_disable'1 t'19 (t'18 == (2 : UInt8))
    else if sw'2 == (105 : Int32) then
      let t'20 ← PMem.ldU8 ch_flag
      let t'21 ← VehicleBridge.gps'0
      VehicleBridge.AP_GPS.set_force_disable_yaw'1 t'21 (t'20 == (2 : UInt8))
    else if sw'2 == (31 : Int32) then
      for _ in [0:1] do
        let t'22 ← PMem.ldU8 ch_flag
        let sw'23 := t'22
        if sw'23 == (2 : UInt8) then
          SRV_Channels.set_emergency_stop true
          break
        else if sw'23 == (1 : UInt8) then
          pure ()
        else if sw'23 == (0 : UInt8) then
          SRV_Channels.set_emergency_stop false
          break
        else
          pure ()
    else if sw'2 == (90 : Int32) then
      let mut source_set : UInt8 := (0 : UInt8)
      let t'24 ← PMem.ldU8 ch_flag
      let sw'25 := t'24
      if sw'25 == (0 : UInt8) then
        source_set := (0 : UInt8)
      else if sw'25 == (1 : UInt8) then
        source_set := (1 : UInt8)
      else if sw'25 == (2 : UInt8) then
        source_set := (2 : UInt8)
      else
        pure ()
      let t'26 ← VehicleBridge.ahrs'0
      VehicleBridge.AP_AHRS.set_posvelyaw_source_set'1 t'26 source_set
      PMem.stU64 (fp + 0) (Int64.toUInt64 (Int32.toInt64 (((UInt32.toInt32 (UInt8.toUInt32 (source_set))) + (1 : Int32)))))
      let t'27 ← gcs
      GCS.send_text t'27 (6 : UInt32) (0x18e5e : UInt64) /- "Using EKF Source Set %u" -/ (fp + 0)
      break
      let t'28 ← PMem.ldU8 ch_flag
      let sw'29 := t'28
      if sw'29 == (2 : UInt8) then
        SRV_Channels.set_emergency_stop false
        let t'30 ← AP.arming
        let t'31 ← AP_Arming_Copter.arm t'30 (2 : Int32) true
        discard <| pure (t'31)
      else if sw'29 == (1 : UInt8) then
        SRV_Channels.set_emergency_stop false
      else if sw'29 == (0 : UInt8) then
        SRV_Channels.set_emergency_stop true
      else
        pure ()
      break
      let t'32 ← VehicleBridge.ahrs'0
      VehicleBridge.AP_AHRS.check_lane_switch'0 t'32
      worldOutputs'drain
    else if sw'2 == (165 : Int32) then
      let t'33 ← PMem.ldU8 ch_flag
      let sw'34 := t'33
      if sw'34 == (2 : UInt8) then
        SRV_Channels.set_emergency_stop false
        let t'35 ← AP.arming
        let t'36 ← AP_Arming_Copter.arm t'35 (2 : Int32) true
        discard <| pure (t'36)
      else if sw'34 == (1 : UInt8) then
        SRV_Channels.set_emergency_stop false
      else if sw'34 == (0 : UInt8) then
        SRV_Channels.set_emergency_stop true
      else
        pure ()
      break
      let t'37 ← VehicleBridge.ahrs'0
      VehicleBridge.AP_AHRS.check_lane_switch'0 t'37
      worldOutputs'drain
    else if sw'2 == (103 : Int32) then
      let t'38 ← VehicleBridge.ahrs'0
      VehicleBridge.AP_AHRS.check_lane_switch'0 t'38
      worldOutputs'drain
    else if sw'2 == (104 : Int32) then
      let t'39 ← VehicleBridge.ahrs'0
      VehicleBridge.AP_AHRS.request_yaw_reset'0 t'39
    else if sw'2 == (187 : Int32) then
      let t'40 ← PMem.ldU8 ch_flag
      if (t'40 == (2 : UInt8)) then
        if (← get).armed then
          let t'41 ← gcs
          GCS.send_text t'41 (4 : UInt32) (0x18e76 : UInt64) /- "EKF reset ignored: vehicle armed" -/ (fp + 8)
        else
          let t'42 ← VehicleBridge.ahrs'0
          let t'43 ← VehicleBridge.AP_AHRS.reset_configured_backend'0 t'42
          worldOutputs'drain
          if t'43 then
            let t'44 ← gcs
            GCS.send_text t'44 (6 : UInt32) (0x18e97 : UInt64) /- "EKF bootstrap reset performed" -/ (fp + 16)
          else
            let t'45 ← gcs
            GCS.send_text t'45 (4 : UInt32) (0x18eb5 : UInt64) /- "EKF bootstrap reset failed" -/ (fp + 24)
    else if sw'2 == (112 : Int32) then
      break
    else
      let t'46 ← PMem.ldI32 ch_option
      PMem.stU64 (fp + 32) (UInt32.toUInt64 ((Int32.toUInt32 (t'46))))
      let t'47 ← gcs
      GCS.send_text t'47 (6 : UInt32) (0x18ed0 : UInt64) /- "Invalid channel option (%u)" -/ (fp + 32)
      return false
  return true

def RC_Channel.do_aux_function (this : UInt64) (trigger : UInt64) : PMem.M Bool := do
  let fp ← PMem.enter 40
  let r ← RC_Channel.do_aux_function.body fp this trigger
  PMem.leave fp
  return r

mutual

/-- C++ `Copter::set_mode : bool (Mode::Number, ModeReason)`, `mode.cpp:318-486`. -/
def Copter.set_mode.body'rec (rec'depth : Nat) (fp : UInt64) (this : UInt64) (mode : UInt8) (reason : UInt8) : PMem.M Bool := do
  let rec'd + 1 := rec'depth | PMem.depthOut
  let mut mode := mode
  let mut reason := reason
  let t'1 ← PMem.ldU8 (this + 11248)
  let mut last_reason : UInt8 := t'1
  PMem.stU8 (this + 11248) reason
  let t'2 ← PMem.ldU64 (this + 9488)
  let t'3 ← vcall'Mode'mode_number'1 t'2
  if (mode == t'3) then
    PMem.stU8 (this + 6352) reason
    if ((reason == (26 : UInt8)) && (mode == (0 : UInt8))) then
      let t'4 ← AC_CommandModel.get_rate_tc ((this + 6840) + 1656)
      let t'5 ← PMem.ldU64 (this + 11168)
      AC_AttitudeControl.set_yaw_rate_tc t'5 t'4
    let t'6 ← PMem.ldB (((0x86d8 : UInt64) /- &copter -/ + 9448) + 13)
    if (t'6 && (reason != last_reason)) then
      let t'7 := Int32.toUInt32 ((1 : Int32))
      PMem.stBits (0xce38 : UInt64) /- &AP_Notify::events -/ 1 1 (UInt32.toUInt64 (t'7))
    return true
  let mut sc'9 := (reason == (2 : UInt8))
  if sc'9 then
    let t'8 ← Copter.gcs_mode_enabled this mode
    sc'9 := !t'8
  if sc'9 then
    let t'10 ← Copter.mode_from_mode_num this mode
    let mut new_flightmode : UInt64 := t'10
    if (new_flightmode == (0 : UInt64)) then
      AP_Vehicle.notify_no_such_mode this mode
    else
      Copter.mode_change_failed this new_flightmode (0x14891 : UInt64) /- "GCS entry disabled (FLTMODE_GCSBLOCK)" -/
    return false
  if (mode == (27 : UInt8)) then
    let t'11 ← ModeAuto.return_path_or_jump_to_landing_sequence_auto_RTL'rec rec'd (this + 11368) reason
    return t'11
  let t'12 ← Copter.mode_from_mode_num this mode
  PMem.stU64 (fp + 0) t'12
  let t'13 ← PMem.ldU64 (fp + 0)
  if (t'13 == (0 : UInt64)) then
    AP_Vehicle.notify_no_such_mode this mode
    return false
  let t'14 ← PMem.ldU64 (this + 9528)
  let t'15 ← AP_Motors.armed t'14
  let mut ignore_checks : Bool := !t'15
  let t'16 ← PMem.ldU64 (fp + 0)
  let t'17 ← vcall'Mode'has_manual_throttle'3 t'16
  let mut user_throttle : Bool := t'17
  let mut sc'19 := !ignore_checks
  if sc'19 then
    let t'18 ← PMem.ldB ((this + 9448) + 7)
    sc'19 := t'18
  let mut sc'22 := (sc'19 && user_throttle)
  if sc'22 then
    let t'20 ← PMem.ldU64 ((0x86d8 : UInt64) /- &copter -/ + 9488)
    let t'21 ← vcall'Mode'has_manual_throttle'3 t'20
    sc'22 := !t'21
  let mut sc'26 := sc'22
  if sc'26 then
    let t'23 ← PMem.ldU64 (fp + 0)
    let t'24 ← Mode.get_pilot_desired_throttle t'23
    let t'25 ← Copter.get_non_takeoff_throttle (0x86d8 : UInt64) /- &copter -/
    sc'26 := (decide (t'24 > t'25))
  if sc'26 then
    let t'27 ← PMem.ldU64 (fp + 0)
    Copter.mode_change_failed this t'27 (0x148b7 : UInt64) /- "throttle too high" -/
    return false
  let mut sc'30 := !ignore_checks
  if sc'30 then
    let t'28 ← PMem.ldU64 (fp + 0)
    let t'29 ← vcall'Mode'requires_position'5 t'28
    sc'30 := t'29
  let mut sc'32 := sc'30
  if sc'32 then
    let t'31 ← Copter.position_ok (0x86d8 : UInt64) /- &copter -/
    sc'32 := !t'31
  if sc'32 then
    let t'33 ← PMem.ldU64 (fp + 0)
    Copter.mode_change_failed this t'33 (0x148c9 : UInt64) /- "requires position" -/
    return false
  let mut sc'35 := !ignore_checks
  if sc'35 then
    let t'34 ← Copter.ekf_alt_ok (0x86d8 : UInt64) /- &copter -/
    sc'35 := !t'34
  let mut sc'38 := sc'35
  if sc'38 then
    let t'36 ← PMem.ldU64 (this + 9488)
    let t'37 ← vcall'Mode'has_manual_throttle'3 t'36
    sc'38 := t'37
  let mut sc'41 := sc'38
  if sc'41 then
    let t'39 ← PMem.ldU64 (fp + 0)
    let t'40 ← vcall'Mode'has_manual_throttle'3 t'39
    sc'41 := !t'40
  if sc'41 then
    let t'42 ← PMem.ldU64 (fp + 0)
    Copter.mode_change_failed this t'42 (0x148db : UInt64) /- "need alt estimate" -/
    return false
  let t'43 ← rc
  let t'44 ← RC_Channels_Copter.in_rc_failsafe t'43
  let mut sc'47 := t'44
  if sc'47 then
    let t'45 ← PMem.ldU64 (fp + 0)
    let t'46 ← vcall'Mode'allows_entry_in_rc_failsafe'6 t'45
    sc'47 := !t'46
  if sc'47 then
    let t'48 ← PMem.ldU64 (fp + 0)
    Copter.mode_change_failed this t'48 (0x148ed : UInt64) /- "in RC failsafe" -/
    return false
  let t'49 ← PMem.ldU64 (fp + 0)
  let t'50 ← vcall'Mode'init'7 t'49 ignore_checks
  if !t'50 then
    let t'51 ← PMem.ldU64 (fp + 0)
    Copter.mode_change_failed this t'51 (0x148fc : UInt64) /- "init failed" -/
    return false
  Copter.exit_mode this (this + 9488) (fp + 0)
  let t'52 ← PMem.ldU64 (fp + 0)
  PMem.stU64 (this + 9488) t'52
  PMem.stU8 (this + 6352) reason
  let t'53 ← Copter.gcs this
  GCS.send_message t'53 (0 : UInt8)
  let t'54 ← AC_CommandModel.get_rate_tc ((this + 6840) + 1656)
  let t'55 ← PMem.ldU64 (this + 11168)
  AC_AttitudeControl.set_yaw_rate_tc t'55 t'54
  Copter.notify_flight_mode this
  let t'56 ← PMem.ldB (((0x86d8 : UInt64) /- &copter -/ + 9448) + 13)
  if t'56 then
    let t'57 := Int32.toUInt32 ((1 : Int32))
    PMem.stBits (0xce38 : UInt64) /- &AP_Notify::events -/ 1 1 (UInt32.toUInt64 (t'57))
  return true

def Copter.set_mode'rec (rec'depth : Nat) (this : UInt64) (mode : UInt8) (reason : UInt8) : PMem.M Bool := do
  let rec'd + 1 := rec'depth | PMem.depthOut
  let fp ← PMem.enter 8
  let r ← Copter.set_mode.body'rec rec'd fp this mode reason
  PMem.leave fp
  return r

/-- C++ `ModeAuto::return_path_or_jump_to_landing_sequence_auto_RTL : bool (ModeReason)`, `mode_auto.cpp:298-312`. -/
def ModeAuto.return_path_or_jump_to_landing_sequence_auto_RTL.body'rec (rec'depth : Nat) (fp : UInt64) (this : UInt64) (reason : UInt8) : PMem.M Bool := do
  let rec'd + 1 := rec'depth | PMem.depthOut
  let mut reason := reason
  Mode.get_stopping_point this (fp + 16)
  let t'1 := (fp + 16)
  Location.Location'2 (fp + 0) t'1
  let t'2 ← AP_Mission.jump_to_closest_mission_leg'rec rec'd (this + 112) (fp + 0)
  let mut sc'4 := !t'2
  if sc'4 then
    let t'3 ← AP_Mission.jump_to_landing_sequence'rec rec'd (this + 112) (fp + 0)
    sc'4 := !t'3
  if sc'4 then
    let t'5 ← PMem.ldB (((0x86d8 : UInt64) /- &copter -/ + 9448) + 13)
    if t'5 then
      let t'6 := Int32.toUInt32 ((1 : Int32))
      PMem.stBits (0xce38 : UInt64) /- &AP_Notify::events -/ 2 1 (UInt32.toUInt64 (t'6))
    let t'7 ← Mode.gcs this
    GCS.send_text t'7 (4 : UInt32) (0x149ff : UInt64) /- "Mode change to AUTO RTL failed: No return path or landing sequence found" -/ (fp + 32)
    return false
  let t'8 ← ModeAuto.enter_auto_rtl'rec rec'd this reason
  return t'8

def ModeAuto.return_path_or_jump_to_landing_sequence_auto_RTL'rec (rec'depth : Nat) (this : UInt64) (reason : UInt8) : PMem.M Bool := do
  let rec'd + 1 := rec'depth | PMem.depthOut
  let fp ← PMem.enter 40
  let r ← ModeAuto.return_path_or_jump_to_landing_sequence_auto_RTL.body'rec rec'd fp this reason
  PMem.leave fp
  return r

/-- C++ `RC_Channels::reset_mode_switch : void ()`, `RC_Channels.cpp:278-285`. -/
def RC_Channels.reset_mode_switch'rec (rec'depth : Nat) (this : UInt64) : PMem.M Unit := do
  let rec'd + 1 := rec'depth | PMem.depthOut
  let t'1 ← RC_Channels.flight_mode_channel this
  let mut c : UInt64 := t'1
  if (c == (0 : UInt64)) then
    return ()
  RC_Channel.reset_mode_switch'rec rec'd c
  return ()

/-- C++ `AP_Mission::jump_to_closest_mission_leg : bool (const Location &)`, `AP_Mission.cpp:2594-2644`. -/
def AP_Mission.jump_to_closest_mission_leg.body'rec (rec'depth : Nat) (fp : UInt64) (this : UInt64) (current_loc : UInt64) : PMem.M Bool := do
  let rec'd + 1 := rec'depth | PMem.depthOut
  let t'1 ← PMem.ldU32 (this + 4)
  if ((UInt32.toInt32 (t'1)) == (UInt32.toInt32 ((1 : UInt32)))) then
    let t'2 ← PMem.ldB ((this + 4) + 7)
    if t'2 then
      let t'3 ← gcs
      GCS.send_text t'3 (6 : UInt32) (0x174ac : UInt64) /- "Landing sequence active" -/ (fp + 0)
      return true
    else
      let t'4 ← PMem.ldB ((this + 4) + 9)
      if t'4 then
        let t'5 ← gcs
        GCS.send_text t'5 (6 : UInt32) (0x174c4 : UInt64) /- "Return path active" -/ (fp + 8)
        return true
  let mut landing_start_index : UInt16 := Int16.toUInt16 (Int32.toInt16 ((0 : Int32)))
  let mut min_distance : Binary32 := Int32.toBinary32 ((-(1 : Int32)))
  PMem.stU16 (fp + 16) (Int16.toUInt16 (Int32.toInt16 ((1000 : Int32))))
  let mut i : UInt16 := Int16.toUInt16 (Int32.toInt16 ((1 : Int32)))
  let mut first'6 := true
  for _ in PMem.loopFuel do
    if !first'6 then
      let t'7 := i
      let t'8 := (t'7 + 1)
      i := t'8
      pure ()
    first'6 := false
    let t'9 ← AP_Mission.num_commands this
    if !((decide ((UInt32.toInt32 (UInt16.toUInt32 (i))) < (UInt32.toInt32 (UInt16.toUInt32 (t'9)))))) then break
    let t'10 ← AP_Mission.get_command_id this i
    if ((UInt32.toInt32 (UInt16.toUInt32 (t'10))) == (UInt32.toInt32 (UInt16.toUInt32 ((UInt32.toUInt16 ((188 : UInt32))))))) then
      let t'11 ← AP_Mission.distance_to_mission_leg this i (fp + 16) (fp + 32) (fp + 24) current_loc
      let mut sc'14 := t'11
      if sc'14 then
        let mut sc'13 := (decide (min_distance < (Int32.toBinary32 ((0 : Int32)))))
        if !sc'13 then
          let t'12 ← PMem.ldF32 (fp + 32)
          sc'13 := (decide (t'12 ≤ min_distance))
        sc'14 := sc'13
      if sc'14 then
        let t'15 ← PMem.ldF32 (fp + 32)
        min_distance := t'15
        let t'16 ← PMem.ldU16 (fp + 24)
        landing_start_index := t'16
      let t'17 ← PMem.ldU16 (fp + 16)
      if ((UInt32.toInt32 (UInt16.toUInt32 (t'17))) == (0 : Int32)) then
        break
  let mut sc'19 := ((UInt32.toInt32 (UInt16.toUInt32 (landing_start_index))) != (0 : Int32))
  if sc'19 then
    let t'18 ← AP_Mission.set_current_cmd'rec rec'd this landing_start_index
    sc'19 := t'18
  if sc'19 then
    let t'20 ← AP_Mission.state this
    if ((UInt32.toInt32 (t'20)) == (UInt32.toInt32 ((0 : UInt32)))) then
      AP_Mission.resume'rec rec'd this
    let t'21 ← gcs
    GCS.send_text t'21 (6 : UInt32) (0x174d7 : UInt64) /- "Return path started" -/ (fp + 40)
    PMem.stB ((this + 4) + 9) true
    return true
  return false

def AP_Mission.jump_to_closest_mission_leg'rec (rec'depth : Nat) (this : UInt64) (current_loc : UInt64) : PMem.M Bool := do
  let rec'd + 1 := rec'depth | PMem.depthOut
  let fp ← PMem.enter 48
  let r ← AP_Mission.jump_to_closest_mission_leg.body'rec rec'd fp this current_loc
  PMem.leave fp
  return r

/-- C++ `AP_Mission::jump_to_landing_sequence : bool (const Location &)`, `AP_Mission.cpp:2573-2589`. -/
def AP_Mission.jump_to_landing_sequence.body'rec (rec'depth : Nat) (fp : UInt64) (this : UInt64) (current_loc : UInt64) : PMem.M Bool := do
  let rec'd + 1 := rec'depth | PMem.depthOut
  let t'1 ← AP_Mission.get_landing_sequence_start this current_loc
  let mut land_idx : UInt16 := t'1
  let mut sc'3 := ((UInt32.toInt32 (UInt16.toUInt32 (land_idx))) != (0 : Int32))
  if sc'3 then
    let t'2 ← AP_Mission.set_current_cmd'rec rec'd this land_idx
    sc'3 := t'2
  if sc'3 then
    let t'4 ← AP_Mission.state this
    if ((UInt32.toInt32 (t'4)) == (UInt32.toInt32 ((0 : UInt32)))) then
      AP_Mission.resume'rec rec'd this
    let t'5 ← gcs
    GCS.send_text t'5 (6 : UInt32) (0x17474 : UInt64) /- "Landing sequence start" -/ (fp + 0)
    return true
  let t'6 ← gcs
  GCS.send_text t'6 (4 : UInt32) (0x1748b : UInt64) /- "Unable to start landing sequence" -/ (fp + 8)
  return false

def AP_Mission.jump_to_landing_sequence'rec (rec'depth : Nat) (this : UInt64) (current_loc : UInt64) : PMem.M Bool := do
  let rec'd + 1 := rec'depth | PMem.depthOut
  let fp ← PMem.enter 16
  let r ← AP_Mission.jump_to_landing_sequence.body'rec rec'd fp this current_loc
  PMem.leave fp
  return r

/-- C++ `ModeAuto::enter_auto_rtl : bool (ModeReason)`, `mode_auto.cpp:315-343`. -/
def ModeAuto.enter_auto_rtl'rec (rec'depth : Nat) (this : UInt64) (reason : UInt8) : PMem.M Bool := do
  let rec'd + 1 := rec'depth | PMem.depthOut
  let mut reason := reason
  AP_Mission.set_force_resume (this + 112) true
  let t'1 ← PMem.ldU64 ((0x86d8 : UInt64) /- &copter -/ + 9488)
  let mut sc'3 := (t'1 == this)
  if !sc'3 then
    let t'2 ← Mode.set_mode'rec rec'd this (3 : UInt8) reason
    sc'3 := t'2
  if sc'3 then
    PMem.stB (this + 861) true
    let t'4 ← PMem.ldB (((0x86d8 : UInt64) /- &copter -/ + 9448) + 13)
    if t'4 then
      let t'5 := Int32.toUInt32 ((1 : Int32))
      PMem.stBits (0xce38 : UInt64) /- &AP_Notify::events -/ 1 1 (UInt32.toUInt64 (t'5))
    return true
  AP_Mission.set_force_resume (this + 112) false
  let t'6 ← PMem.ldB (((0x86d8 : UInt64) /- &copter -/ + 9448) + 13)
  if t'6 then
    let t'7 := Int32.toUInt32 ((1 : Int32))
    PMem.stBits (0xce38 : UInt64) /- &AP_Notify::events -/ 2 1 (UInt32.toUInt64 (t'7))
  return false

/-- C++ `RC_Channel::reset_mode_switch : void ()`, `RC_Channel.cpp:604-609`. -/
def RC_Channel.reset_mode_switch'rec (rec'depth : Nat) (this : UInt64) : PMem.M Unit := do
  let rec'd + 1 := rec'depth | PMem.depthOut
  let t'1 := Int32.toInt8 ((-(1 : Int32)))
  PMem.stI8 ((this + 40) + 1) t'1
  let t'2 := Int32.toInt8 ((-(1 : Int32)))
  PMem.stI8 (this + 40) t'2
  RC_Channel.read_mode_switch'rec rec'd this
  return ()

/-- C++ `AP_Mission::set_current_cmd : bool (uint16_t)`, `AP_Mission.cpp:608-706`. -/
def AP_Mission.set_current_cmd.body'rec (rec'depth : Nat) (fp : UInt64) (this : UInt64) (index : UInt16) : PMem.M Bool := do
  let rec'd + 1 := rec'depth | PMem.depthOut
  let mut index := index
  PMem.stB ((this + 4) + 7) false
  PMem.stB ((this + 4) + 9) false
  AP_Mission.Mission_Command.Mission_Command (fp + 0)
  let t'1 ← AP_Mission.read_cmd_from_storage this index (fp + 0)
  if t'1 then
    let t'2 ← PMem.ldU16 ((fp + 0) + 2)
    let sw'3 := UInt32.toInt32 (UInt16.toUInt32 (t'2))
    if sw'3 == (189 : Int32) then
      PMem.stB ((this + 4) + 7) true
    else if sw'3 == (188 : Int32) then
      PMem.stB ((this + 4) + 9) true
    else
      pure ()
  AP_Mission.reset_wp_history this
  let t'4 ← AP_ParamT'short_2.operator_const_short__ (this + 80)
  let t'5 ← PMem.ldI16 t'4
  let mut sc'8 := (decide ((UInt16.toUInt32 (index)) ≥ (Int32.toUInt32 (Int16.toInt32 (t'5)))))
  if !sc'8 then
    let t'6 ← AP_ParamT'short_2.operator_const_short__ (this + 80)
    let t'7 ← PMem.ldI16 t'6
    sc'8 := ((Int16.toInt32 (t'7)) == (1 : Int32))
  if sc'8 then
    return false
  let t'9 := Int16.toUInt16 (Int32.toInt16 ((65535 : Int32)))
  PMem.stU16 (this + 116) t'9
  PMem.stB ((this + 4) + 5) false
  PMem.stB ((this + 4) + 6) false
  PMem.stB ((this + 4) + 4) false
  let mut sc'11 := ((UInt32.toInt32 (UInt16.toUInt32 (index))) == (0 : Int32))
  if !sc'11 then
    let t'10 ← PMem.ldU32 (this + 4)
    sc'11 := ((UInt32.toInt32 (t'10)) == (UInt32.toInt32 ((2 : UInt32))))
  if sc'11 then
    let t'12 := Int16.toUInt16 (Int32.toInt16 ((0 : Int32)))
    PMem.stU16 (this + 172) t'12
    let t'13 := Int16.toUInt16 (Int32.toInt16 ((65535 : Int32)))
    PMem.stU16 (this + 174) t'13
    let t'14 := Int16.toUInt16 (Int32.toInt16 ((65535 : Int32)))
    PMem.stU16 (this + 176) t'14
    AP_Mission.init_jump_tracking this
    if ((UInt32.toInt32 (UInt16.toUInt32 (index))) == (0 : Int32)) then
      let t'15 := Int16.toUInt16 (Int32.toInt16 ((1 : Int32)))
      index := t'15
  let t'16 ← PMem.ldU32 (this + 4)
  if ((UInt32.toInt32 (t'16)) != (UInt32.toInt32 ((1 : UInt32)))) then
    for _ in PMem.loopFuel do
      let t'17 ← PMem.ldB ((this + 4) + 4)
      if !(!t'17) then break
      let t'18 ← AP_Mission.get_next_cmd this index (fp + 0) true true
      if !t'18 then
        let t'19 := Int16.toUInt16 (Int32.toInt16 ((65535 : Int32)))
        PMem.stU16 (this + 88) t'19
        return false
      let t'20 ← AP_Mission.is_nav_cmd (fp + 0)
      if t'20 then
        discard <| PMem.memcpy (this + 88) (fp + 0) 28
        discard <| pure ((this + 88))
        PMem.stB ((this + 4) + 4) true
      else
        let t'21 ← PMem.ldB ((this + 4) + 5)
        if !t'21 then
          discard <| PMem.memcpy (this + 116) (fp + 0) 28
          discard <| pure ((this + 116))
          PMem.stB ((this + 4) + 5) true
      let t'22 ← PMem.ldU16 (fp + 0)
      let t'23 := Int16.toUInt16 (Int32.toInt16 (((UInt32.toInt32 (UInt16.toUInt32 (t'22))) + (1 : Int32))))
      index := t'23
    let t'24 ← PMem.ldB ((this + 4) + 5)
    if !t'24 then
      PMem.stB ((this + 4) + 6) true
    PMem.stU32 (this + 4) (0 : UInt32)
    return true
  let t'25 ← AP_Mission.advance_current_nav_cmd'rec rec'd this index
  if !t'25 then
    AP_Mission.complete'rec rec'd this
    return false
  return true

def AP_Mission.set_current_cmd'rec (rec'depth : Nat) (this : UInt64) (index : UInt16) : PMem.M Bool := do
  let rec'd + 1 := rec'depth | PMem.depthOut
  let fp ← PMem.enter 28
  let r ← AP_Mission.set_current_cmd.body'rec rec'd fp this index
  PMem.leave fp
  return r

/-- C++ `AP_Mission::resume : void ()`, `AP_Mission.cpp:130-191`. -/
def AP_Mission.resume.body'rec (rec'depth : Nat) (fp : UInt64) (this : UInt64) : PMem.M Unit := do
  let rec'd + 1 := rec'depth | PMem.depthOut
  let t'1 ← PMem.ldU32 (this + 4)
  if ((UInt32.toInt32 (t'1)) == (UInt32.toInt32 ((2 : UInt32)))) then
    AP_Mission.start'rec rec'd this
    return ()
  let t'2 ← PMem.ldU32 (this + 4)
  if ((UInt32.toInt32 (t'2)) == (UInt32.toInt32 ((0 : UInt32)))) then
    PMem.stU32 (this + 4) (1 : UInt32)
    let t'3 ← PMem.ldU16 (this + 88)
    if ((UInt32.toInt32 (UInt16.toUInt32 (t'3))) == (65535 : Int32)) then
      AP_Mission.start'rec rec'd this
      return ()
  let t'4 ← PMem.ldU16 (this + 88)
  let t'5 ← AP_Mission.read_cmd_from_storage this t'4 (this + 88)
  if !t'5 then
    AP_Mission.start'rec rec'd this
    return ()
  let t'6 ← PMem.ldU16 (this + 86)
  let mut sc'8 := (decide ((UInt32.toInt32 (UInt16.toUInt32 (t'6))) > (0 : Int32)))
  if sc'8 then
    let t'7 ← PMem.ldU16 ((this + 16) + ((Int32.toInt64 (((7 : Int32) - (2 : Int32)))) * 2).toUInt64)
    sc'8 := ((UInt32.toInt32 (UInt16.toUInt32 (t'7))) != (65535 : Int32))
  if sc'8 then
    AP_Mission.Mission_Command.Mission_Command (fp + 0)
    let t'9 ← PMem.ldB ((this + 4) + 8)
    let mut sc'11 := !t'9
    if sc'11 then
      let t'10 ← AP_Mission.calc_rewind_pos this (fp + 0)
      sc'11 := t'10
    if sc'11 then
      discard <| PMem.memcpy (this + 144) (fp + 0) 28
      discard <| pure ((this + 144))
    let t'12 ← PMem.ldU16 (this + 144)
    let mut sc'14 := ((UInt32.toInt32 (UInt16.toUInt32 (t'12))) != (65535 : Int32))
    if sc'14 then
      let t'13 ← AP_Mission.start_command'rec rec'd this (this + 144)
      sc'14 := t'13
    if sc'14 then
      discard <| PMem.memcpy (this + 88) (this + 144) 28
      discard <| pure ((this + 88))
      PMem.stB ((this + 4) + 4) true
      PMem.stB ((this + 4) + 8) true
      return ()
  let t'15 ← PMem.ldB ((this + 4) + 5)
  let mut sc'17 := t'15
  if sc'17 then
    let t'16 ← PMem.ldU16 (this + 116)
    sc'17 := ((UInt32.toInt32 (UInt16.toUInt32 (t'16))) != (65535 : Int32))
  if sc'17 then
    let t'18 ← PMem.ldU16 (this + 116)
    let t'19 ← AP_Mission.set_current_cmd'rec rec'd this t'18
    discard <| pure (t'19)
  else
    let t'20 ← PMem.ldB ((this + 4) + 4)
    if t'20 then
      let t'21 ← PMem.ldU16 (this + 88)
      let t'22 ← AP_Mission.set_current_cmd'rec rec'd this t'21
      discard <| pure (t'22)
  return ()

def AP_Mission.resume'rec (rec'depth : Nat) (this : UInt64) : PMem.M Unit := do
  let rec'd + 1 := rec'depth | PMem.depthOut
  let fp ← PMem.enter 28
  let r ← AP_Mission.resume.body'rec rec'd fp this
  PMem.leave fp
  return r

/-- C++ `Mode::set_mode : bool (Mode::Number, ModeReason)`, `mode.cpp:1131-1134`. -/
def Mode.set_mode'rec (rec'depth : Nat) (this : UInt64) (mode : UInt8) (reason : UInt8) : PMem.M Bool := do
  let rec'd + 1 := rec'depth | PMem.depthOut
  let mut mode := mode
  let mut reason := reason
  let t'1 ← Copter.set_mode'rec rec'd (0x86d8 : UInt64) /- &copter -/ mode reason
  return t'1

/-- C++ `RC_Channel::read_mode_switch : void ()`, `RC_Channel.cpp:641-648`. -/
def RC_Channel.read_mode_switch.body'rec (rec'depth : Nat) (fp : UInt64) (this : UInt64) : PMem.M Unit := do
  let rec'd + 1 := rec'depth | PMem.depthOut
  let t'1 ← RC_Channel.read_6pos_switch this (fp + 0)
  if t'1 then
    let t'2 ← PMem.ldI8 (fp + 0)
    RC_Channel_Copter.mode_switch_changed'rec rec'd this t'2
  return ()

def RC_Channel.read_mode_switch'rec (rec'depth : Nat) (this : UInt64) : PMem.M Unit := do
  let rec'd + 1 := rec'depth | PMem.depthOut
  let fp ← PMem.enter 1
  let r ← RC_Channel.read_mode_switch.body'rec rec'd fp this
  PMem.leave fp
  return r

/-- C++ `AP_Mission::advance_current_nav_cmd : bool (uint16_t)`, `AP_Mission.cpp:2157-2254`. -/
def AP_Mission.advance_current_nav_cmd.body'rec (rec'depth : Nat) (fp : UInt64) (this : UInt64) (starting_index : UInt16) : PMem.M Bool := do
  let rec'd + 1 := rec'depth | PMem.depthOut
  let mut starting_index := starting_index
  let t'1 ← PMem.ldU32 (this + 4)
  if ((UInt32.toInt32 (t'1)) != (UInt32.toInt32 ((1 : UInt32)))) then
    return false
  let t'2 ← PMem.ldB ((this + 4) + 4)
  if t'2 then
    return false
  let t'3 := Int16.toUInt16 (Int32.toInt16 ((65535 : Int32)))
  PMem.stU16 (this + 116) t'3
  PMem.stB ((this + 4) + 5) false
  PMem.stB ((this + 4) + 6) false
  let mut c'4 : Int32 := default
  if (decide ((UInt32.toInt32 (UInt16.toUInt32 (starting_index))) > (0 : Int32))) then
    c'4 := ((UInt32.toInt32 (UInt16.toUInt32 (starting_index))) - (1 : Int32))
  else
    let t'5 ← PMem.ldU16 (this + 88)
    c'4 := UInt32.toInt32 (UInt16.toUInt32 (t'5))
  let mut cmd_index : UInt16 := Int16.toUInt16 (Int32.toInt16 (c'4))
  if ((UInt32.toInt32 (UInt16.toUInt32 (cmd_index))) == (65535 : Int32)) then
    let t'6 := Int16.toUInt16 (Int32.toInt16 ((1 : Int32)))
    cmd_index := t'6
  else
    let t'7 := cmd_index
    let t'8 := (t'7 + 1)
    cmd_index := t'8
  let mut max_loops : UInt8 := Int8.toUInt8 (Int32.toInt8 ((255 : Int32)))
  for _ in PMem.loopFuel do
    let t'9 ← PMem.ldB ((this + 4) + 4)
    let mut sc'12 := !t'9
    if sc'12 then
      let t'10 := max_loops
      let t'11 := (t'10 - 1)
      max_loops := t'11
      sc'12 := (decide ((UInt32.toInt32 (UInt8.toUInt32 (t'10))) > (0 : Int32)))
    if !(sc'12) then break
    AP_Mission.Mission_Command.Mission_Command (fp + 0)
    let t'13 ← AP_Mission.get_next_cmd this cmd_index (fp + 0) true true
    if !t'13 then
      return false
    let t'14 ← AP_Mission.is_nav_cmd (fp + 0)
    if t'14 then
      let t'15 ← PMem.ldU16 ((this + 88) + 2)
      PMem.stU16 (this + 172) t'15
      let t'16 ← PMem.ldU16 (this + 88)
      PMem.stU16 (this + 174) t'16
      let t'17 ← PMem.ldI32 (((fp + 0) + 8) + 8)
      let mut sc'19 := (t'17 == (0 : Int32))
      if sc'19 then
        let t'18 ← PMem.ldI32 (((fp + 0) + 8) + 12)
        sc'19 := (t'18 == (0 : Int32))
      if !sc'19 then
        let t'20 ← PMem.ldU16 (this + 88)
        PMem.stU16 (this + 176) t'20
      discard <| PMem.memcpy (this + 88) (fp + 0) 28
      discard <| pure ((this + 88))
      let t'21 ← AP_Mission.start_command'rec rec'd this (this + 88)
      if t'21 then
        PMem.stB ((this + 4) + 4) true
        let t'22 ← PMem.ldU16 this
        let mut sc'24 := (decide ((UInt32.toInt32 (UInt16.toUInt32 (t'22))) > (0 : Int32)))
        if sc'24 then
          let t'23 ← PMem.ldU16 this
          sc'24 := (decide ((UInt32.toInt32 (UInt16.toUInt32 (t'23))) < (65535 : Int32)))
        if sc'24 then
          let t'25 ← PMem.ldU16 this
          let t'26 := (t'25 + 1)
          PMem.stU16 this t'26
      let t'27 ← PMem.ldU16 (this + 86)
      let mut sc'29 := (decide ((UInt32.toInt32 (UInt16.toUInt32 (t'27))) > (0 : Int32)))
      if sc'29 then
        let t'28 ← PMem.ldB ((this + 4) + 8)
        sc'29 := !t'28
      let mut sc'31 := sc'29
      if sc'31 then
        let t'30 ← PMem.ldU16 (this + 88)
        sc'31 := ((UInt32.toInt32 (UInt16.toUInt32 (t'30))) != (65535 : Int32))
      let mut sc'35 := sc'31
      if sc'35 then
        let t'32 ← PMem.ldI32 (((this + 88) + 8) + 8)
        let mut sc'34 := (t'32 == (0 : Int32))
        if sc'34 then
          let t'33 ← PMem.ldI32 (((this + 88) + 8) + 12)
          sc'34 := (t'33 == (0 : Int32))
        sc'35 := !sc'34
      if sc'35 then
        for i'36 in [0:6] do
          let i : UInt8 := UInt8.ofNat i'36
          let t'37 ← PMem.ldU16 ((this + 16) + ((Int32.toInt64 (((UInt32.toInt32 (UInt8.toUInt32 (i))) + (1 : Int32)))) * 2).toUInt64)
          PMem.stU16 ((this + 16) + ((UInt64.toInt64 (UInt8.toUInt64 (i))) * 2).toUInt64) t'37
        let t'38 ← PMem.ldU16 (this + 88)
        PMem.stU16 ((this + 16) + ((Int32.toInt64 (((7 : Int32) - (1 : Int32)))) * 2).toUInt64) t'38
      let t'39 ← PMem.ldB ((this + 4) + 8)
      let mut sc'42 := t'39
      if sc'42 then
        let t'40 ← PMem.ldU16 (this + 88)
        let t'41 ← PMem.ldU16 ((this + 16) + ((Int32.toInt64 (((7 : Int32) - (1 : Int32)))) * 2).toUInt64)
        sc'42 := ((UInt32.toInt32 (UInt16.toUInt32 (t'40))) == (UInt32.toInt32 (UInt16.toUInt32 (t'41))))
      if sc'42 then
        let t'43 ← gcs
        GCS.send_text t'43 (6 : UInt32) (0x1741b : UInt64) /- "Mission: Returned to interrupted WP" -/ (fp + 32)
        PMem.stB ((this + 4) + 8) false
    else
      let t'44 ← PMem.ldB ((this + 4) + 5)
      if !t'44 then
        discard <| PMem.memcpy (this + 116) (fp + 0) 28
        discard <| pure ((this + 116))
        PMem.stB ((this + 4) + 5) true
        let t'45 ← AP_Mission.start_command'rec rec'd this (this + 116)
        discard <| pure (t'45)
    let t'46 ← PMem.ldU16 (fp + 0)
    let t'47 := Int16.toUInt16 (Int32.toInt16 (((UInt32.toInt32 (UInt16.toUInt32 (t'46))) + (1 : Int32))))
    cmd_index := t'47
  if ((UInt32.toInt32 (UInt8.toUInt32 (max_loops))) == (0 : Int32)) then
    return false
  let t'48 ← PMem.ldB ((this + 4) + 5)
  if !t'48 then
    PMem.stB ((this + 4) + 6) true
  return true

def AP_Mission.advance_current_nav_cmd'rec (rec'depth : Nat) (this : UInt64) (starting_index : UInt16) : PMem.M Bool := do
  let rec'd + 1 := rec'depth | PMem.depthOut
  let fp ← PMem.enter 40
  let r ← AP_Mission.advance_current_nav_cmd.body'rec rec'd fp this starting_index
  PMem.leave fp
  return r

/-- C++ `AP_Mission::complete : void ()`, `AP_Mission.cpp:2142-2151`. -/
def AP_Mission.complete'rec (rec'depth : Nat) (this : UInt64) : PMem.M Unit := do
  let rec'd + 1 := rec'depth | PMem.depthOut
  PMem.stU32 (this + 4) (2 : UInt32)
  PMem.stB ((this + 4) + 7) false
  PMem.stB ((this + 4) + 9) false
  Functor'void.operator__'at'AP_Mission'_mission_complete_fn'rec rec'd (this + 64)
  return ()

/-- C++ `AP_Mission::start : void ()`, `AP_Mission.cpp:109-120`. -/
def AP_Mission.start'rec (rec'depth : Nat) (this : UInt64) : PMem.M Unit := do
  let rec'd + 1 := rec'depth | PMem.depthOut
  PMem.stU32 (this + 4) (1 : UInt32)
  AP_Mission.reset this
  let t'1 ← AP_Mission.advance_current_nav_cmd'rec rec'd this (Int16.toUInt16 (Int32.toInt16 ((0 : Int32))))
  if !t'1 then
    AP_Mission.complete'rec rec'd this
  return ()

/-- C++ `AP_Mission::start_command : bool (const Mission_Command &)`, `AP_Mission.cpp:405-501`. -/
def AP_Mission.start_command.body'rec (rec'depth : Nat) (fp : UInt64) (this : UInt64) (cmd : UInt64) : PMem.M Bool := do
  let rec'd + 1 := rec'depth | PMem.depthOut
  let t'1 ← PMem.ldU16 (cmd + 2)
  let t'2 ← AP_Mission.is_landing_type_cmd this t'1
  let mut sc'4 := t'2
  if !sc'4 then
    let t'3 ← PMem.ldU16 (cmd + 2)
    sc'4 := ((UInt32.toInt32 (UInt16.toUInt32 (t'3))) == (UInt32.toInt32 ((189 : UInt32))))
  if sc'4 then
    PMem.stB ((this + 4) + 7) true
  else
    let t'5 ← PMem.ldU16 (cmd + 2)
    if ((UInt32.toInt32 (UInt16.toUInt32 (t'5))) == (UInt32.toInt32 ((188 : UInt32)))) then
      PMem.stB ((this + 4) + 9) true
    else
      let t'6 ← PMem.ldU16 (cmd + 2)
      let t'7 ← AP_Mission.is_takeoff_type_cmd this t'6
      if t'7 then
        PMem.stB ((this + 4) + 7) false
        PMem.stB ((this + 4) + 9) false
  let t'8 ← PMem.ldU16 (cmd + 2)
  let sw'9 := UInt32.toInt32 (UInt16.toUInt32 (t'8))
  if sw'9 == (177 : Int32) || sw'9 == (600 : Int32) || sw'9 == (601 : Int32) then
    let t'10 ← PMem.ldU16 cmd
    PMem.stU64 (fp + 0) (Int64.toUInt64 (Int32.toInt64 ((UInt32.toInt32 (UInt16.toUInt32 (t'10))))))
    let t'11 ← AP_Mission.Mission_Command.type cmd
    PMem.stU64 (fp + 8) t'11
    let t'12 ← PMem.ldU16 (cmd + 4)
    PMem.stU64 (fp + 16) (UInt32.toUInt64 ((UInt16.toUInt32 (t'12))))
    let t'13 ← gcs
    GCS.send_text t'13 (6 : UInt32) (0x173cf : UInt64) /- "Mission: %u %s %u" -/ (fp + 0)
  else
    let t'14 ← PMem.ldU16 cmd
    PMem.stU64 (fp + 24) (Int64.toUInt64 (Int32.toInt64 ((UInt32.toInt32 (UInt16.toUInt32 (t'14))))))
    let t'15 ← AP_Mission.Mission_Command.type cmd
    PMem.stU64 (fp + 32) t'15
    let t'16 ← gcs
    GCS.send_text t'16 (6 : UInt32) (0x173e1 : UInt64) /- "Mission: %u %s" -/ (fp + 24)
  let t'17 ← PMem.ldU16 (cmd + 2)
  let sw'18 := UInt32.toInt32 (UInt16.toUInt32 (t'17))
  if sw'18 == (218 : Int32) then
    let t'19 ← AP_Mission.start_command_do_aux_function'rec rec'd this cmd
    return t'19
  else if sw'18 == (208 : Int32) then
    let t'20 ← AP_Mission.start_command_parachute this cmd
    return t'20
  else if sw'18 == (217 : Int32) then
    let t'21 ← AP_Mission.start_command_do_scripting this cmd
    return t'21
  else if sw'18 == (216 : Int32) then
    let t'22 ← AP_Mission.start_command_do_sprayer this cmd
    return t'22
  else if sw'18 == (215 : Int32) then
    let t'23 ← AP_Mission.command_do_set_repeat_dist this cmd
    return t'23
  else if sw'18 == (1000 : Int32) then
    let t'24 ← AP_Mission.start_command_do_gimbal_manager_pitchyaw this cmd
    return t'24
  else if sw'18 == (195 : Int32) || sw'18 == (197 : Int32) then
    let t'25 ← PMem.ldU16 (cmd + 4)
    let mut c'26 : Bool := default
    if ((UInt32.toInt32 (UInt16.toUInt32 (t'25))) == (0 : Int32)) then
      let t'27 ← Functor'bool_const_AP_Mission_Mission_Command.operator__'at'AP_Mission'_cmd_start_fn'rec rec'd (this + 32) cmd
      c'26 := t'27
    else
      let t'28 ← AP_Mission.start_command_do_set_roi this cmd
      c'26 := t'28
    return c'26
  else if sw'18 == (196 : Int32) then
    let t'29 ← AP_Mission.start_command_do_set_roi_wpnext_offset this cmd
    return t'29
  else if sw'18 == (600 : Int32) then
    let t'30 ← PMem.ldU16 (cmd + 8)
    PMem.stU16 (this + 2) t'30
    let t'31 := Int16.toUInt16 (Int32.toInt16 ((1 : Int32)))
    PMem.stU16 this t'31
    let t'32 ← Functor'bool_const_AP_Mission_Mission_Command.operator__'at'AP_Mission'_cmd_start_fn'rec rec'd (this + 32) cmd
    return t'32
  else
    let t'33 ← Functor'bool_const_AP_Mission_Mission_Command.operator__'at'AP_Mission'_cmd_start_fn'rec rec'd (this + 32) cmd
    return t'33

def AP_Mission.start_command'rec (rec'depth : Nat) (this : UInt64) (cmd : UInt64) : PMem.M Bool := do
  let rec'd + 1 := rec'depth | PMem.depthOut
  let fp ← PMem.enter 40
  let r ← AP_Mission.start_command.body'rec rec'd fp this cmd
  PMem.leave fp
  return r

/-- C++ `RC_Channel::run_aux_function : bool (AUX_FUNC, AuxSwitchPos, AuxFuncTrigger::Source, uint16_t)`, `RC_Channel.cpp:1458-1501`. -/
def RC_Channel.run_aux_function.body'rec (rec'depth : Nat) (fp : UInt64) (this : UInt64) (ch_option : Int32) (pos : UInt8) (source : UInt8) (source_index : UInt16) : PMem.M Bool := do
  let rec'd + 1 := rec'depth | PMem.depthOut
  let mut ch_option := ch_option
  let mut pos := pos
  let mut source := source
  let mut source_index := source_index
  PMem.stI32 ((fp + 0) + 0) ch_option
  PMem.stU8 ((fp + 0) + 4) pos
  PMem.stU8 ((fp + 0) + 5) source
  PMem.stU16 ((fp + 0) + 6) source_index
  let t'1 ← RC_Channel_Copter.do_aux_function'rec rec'd this (fp + 0)
  let mut ret : Bool := t'1
  return ret

def RC_Channel.run_aux_function'rec (rec'depth : Nat) (this : UInt64) (ch_option : Int32) (pos : UInt8) (source : UInt8) (source_index : UInt16) : PMem.M Bool := do
  let rec'd + 1 := rec'depth | PMem.depthOut
  let fp ← PMem.enter 8
  let r ← RC_Channel.run_aux_function.body'rec rec'd fp this ch_option pos source source_index
  PMem.leave fp
  return r

/-- C++ `RC_Channel_Copter::mode_switch_changed : void (modeswitch_pos_t)`, `RC_Channel_Copter.cpp:17-38`. -/
def RC_Channel_Copter.mode_switch_changed.body'rec (rec'depth : Nat) (fp : UInt64) (this : UInt64) (new_pos : Int8) : PMem.M Unit := do
  let rec'd + 1 := rec'depth | PMem.depthOut
  PMem.stI8 (fp + 0) new_pos
  let t'1 ← PMem.ldI8 (fp + 0)
  let mut sc'3 := (decide ((Int8.toInt32 (t'1)) < (0 : Int32)))
  if !sc'3 then
    let t'2 ← PMem.ldI8 (fp + 0)
    sc'3 := (decide ((UInt8.toUInt64 ((Int8.toUInt8 (t'2)))) ≥ ((6 : UInt64) / (1 : UInt64))))
  if sc'3 then
    return ()
  let t'4 ← PMem.ldI8 (fp + 0)
  let t'5 ← AP_ParamTBase'signed_char_1.get ((((0x86d8 : UInt64) /- &copter -/ + 6776) + 32) + ((Int8.toInt64 (t'4)) * 1).toUInt64)
  let t'6 ← PMem.ldI8 t'5
  let t'7 ← Copter.set_mode'rec rec'd (0x86d8 : UInt64) /- &copter -/ (Int8.toUInt8 (t'6)) (1 : UInt8)
  if !t'7 then
    return ()
  let t'8 ← rc
  let t'9 ← RC_Channels.find_channel_for_option t'8 (3 : Int32)
  let mut sc'12 := !(t'9 != 0)
  if sc'12 then
    let t'10 ← rc
    let t'11 ← RC_Channels.find_channel_for_option t'10 (13 : Int32)
    sc'12 := !(t'11 != 0)
  if sc'12 then
    let t'13 ← AP_ParamT'unsigned_char_1.operator_const_unsigned_char__ (((0x86d8 : UInt64) /- &copter -/ + 6776) + 24)
    let t'14 ← PMem.ldU8 t'13
    let t'15 ← PMem.ldI8 (fp + 0)
    if (((UInt8.toUInt32 (t'14)) &&& ((1 : UInt32) <<< (Int32.toUInt32 ((Int8.toInt32 (t'15)))))) != (Int32.toUInt32 ((0 : Int32)))) then
      Copter.set_simple_mode (0x86d8 : UInt64) /- &copter -/ (2 : Int32)
    else
      let t'16 ← AP_ParamT'unsigned_char_1.operator_const_unsigned_char__ (((0x86d8 : UInt64) /- &copter -/ + 6776) + 38)
      let t'17 ← PMem.ldU8 t'16
      let t'18 ← PMem.ldI8 (fp + 0)
      let mut c'19 : Int32 := default
      if (((UInt8.toUInt32 (t'17)) &&& ((1 : UInt32) <<< (Int32.toUInt32 ((Int8.toInt32 (t'18)))))) != (Int32.toUInt32 ((0 : Int32)))) then
        c'19 := (1 : Int32)
      else
        c'19 := (0 : Int32)
      Copter.set_simple_mode (0x86d8 : UInt64) /- &copter -/ c'19
  return ()

def RC_Channel_Copter.mode_switch_changed'rec (rec'depth : Nat) (this : UInt64) (new_pos : Int8) : PMem.M Unit := do
  let rec'd + 1 := rec'depth | PMem.depthOut
  let fp ← PMem.enter 1
  let r ← RC_Channel_Copter.mode_switch_changed.body'rec rec'd fp this new_pos
  PMem.leave fp
  return r

/-- C++ `Copter::set_mode_land_with_pause : void (ModeReason)`, `mode_land.cpp:212-219`. -/
def Copter.set_mode_land_with_pause'rec (rec'depth : Nat) (this : UInt64) (reason : UInt8) : PMem.M Unit := do
  let rec'd + 1 := rec'depth | PMem.depthOut
  let mut reason := reason
  let t'1 ← Copter.set_mode'rec rec'd this (9 : UInt8) reason
  discard <| pure (t'1)
  ModeLand.set_land_pause (this + 12640) true
  let t'2 := Int32.toUInt32 ((1 : Int32))
  PMem.stBits (0xce38 : UInt64) /- &AP_Notify::events -/ 3 1 (UInt32.toUInt64 (t'2))
  return ()

/-- C++ `Copter::set_mode_RTL_or_land_with_pause : void (ModeReason)`, `events.cpp:389-400`. -/
def Copter.set_mode_RTL_or_land_with_pause'rec (rec'depth : Nat) (this : UInt64) (reason : UInt8) : PMem.M Unit := do
  let rec'd + 1 := rec'depth | PMem.depthOut
  let mut reason := reason
  let t'1 ← Copter.set_mode'rec rec'd this (6 : UInt8) reason
  if t'1 then
    let t'2 := Int32.toUInt32 ((1 : Int32))
    PMem.stBits (0xce38 : UInt64) /- &AP_Notify::events -/ 3 1 (UInt32.toUInt64 (t'2))
    return ()
  Copter.set_mode_land_with_pause'rec rec'd this reason
  return ()

/-- C++ `AP_Mission::start_command_do_aux_function : bool (const AP_Mission::Mission_Command &)`, `AP_Mission_Commands.cpp:20-37`. -/
def AP_Mission.start_command_do_aux_function'rec (rec'depth : Nat) (this : UInt64) (cmd : UInt64) : PMem.M Bool := do
  let rec'd + 1 := rec'depth | PMem.depthOut
  let t'1 ← PMem.ldU16 (cmd + 8)
  let mut function : Int32 := UInt32.toInt32 (UInt16.toUInt32 (t'1))
  let t'2 ← PMem.ldU8 ((cmd + 8) + 2)
  let mut pos : UInt8 := t'2
  let sw'3 := pos
  if sw'3 == (2 : UInt8) || sw'3 == (1 : UInt8) || sw'3 == (0 : UInt8) then
    pure ()
  else
    return false
  let t'4 ← PMem.ldU16 cmd
  let t'5 ← rc
  let t'6 ← RC_Channels.run_aux_function'rec rec'd t'5 function pos (4 : UInt8) t'4
  discard <| pure (t'6)
  return true

/-- C++ `RC_Channel_Copter::do_aux_function : bool (const AuxFuncTrigger &)`, `RC_Channel_Copter.cpp:182-701`. -/
def RC_Channel_Copter.do_aux_function.body'rec (rec'depth : Nat) (fp : UInt64) (this : UInt64) (trigger : UInt64) : PMem.M Bool := do
  let rec'd + 1 := rec'depth | PMem.depthOut
  let ch_option : UInt64 := trigger
  let ch_flag : UInt64 := (trigger + 4)
  for _ in [0:1] do
    let t'1 ← PMem.ldI32 ch_option
    let sw'2 := t'1
    if sw'2 == (2 : Int32) then
      let t'3 ← PMem.ldU8 ch_flag
      if (t'3 == (2 : UInt8)) then
        let t'4 ← Copter.set_mode'rec rec'd (0x86d8 : UInt64) /- &copter -/ (14 : UInt8) (53 : UInt8)
        discard <| pure (t'4)
      else
        pure ()
    else if sw'2 == (3 : Int32) then
      let t'5 ← PMem.ldU8 ch_flag
      let mut c'6 : Int32 := default
      if (t'5 == (0 : UInt8)) then
        c'6 := (0 : Int32)
      else
        c'6 := (1 : Int32)
      Copter.set_simple_mode (0x86d8 : UInt64) /- &copter -/ c'6
    else if sw'2 == (13 : Int32) then
      let mut newmode : Int32 := (0 : Int32)
      let t'7 ← PMem.ldU8 ch_flag
      let sw'8 := t'7
      if sw'8 == (0 : UInt8) then
        pure ()
      else if sw'8 == (1 : UInt8) then
        newmode := (1 : Int32)
      else if sw'8 == (2 : UInt8) then
        newmode := (2 : Int32)
      else
        pure ()
      Copter.set_simple_mode (0x86d8 : UInt64) /- &copter -/ newmode
      break
      let t'9 ← PMem.ldU8 ch_flag
      RC_Channel_Copter.do_aux_function_change_mode'rec rec'd this (6 : UInt8) t'9
    else if sw'2 == (4 : Int32) then
      let t'10 ← PMem.ldU8 ch_flag
      RC_Channel_Copter.do_aux_function_change_mode'rec rec'd this (6 : UInt8) t'10
    else if sw'2 == (5 : Int32) then
      let t'11 ← PMem.ldU8 ch_flag
      let mut sc'14 := (t'11 == (2 : UInt8))
      if sc'14 then
        let t'12 ← PMem.ldU64 ((0x86d8 : UInt64) /- &copter -/ + 9488)
        let t'13 ← vcall'Mode'allows_save_trim'26 t'12
        sc'14 := t'13
      let mut sc'17 := sc'14
      if sc'17 then
        let t'15 ← PMem.ldU64 ((0x86d8 : UInt64) /- &copter -/ + 8616)
        let t'16 ← RC_Channel.get_control_in t'15
        sc'17 := ((Int16.toInt32 (t'16)) == (0 : Int32))
      if sc'17 then
        Copter.AHRSTrimming.save_trim ((0x86d8 : UInt64) /- &copter -/ + 11230)
    else if sw'2 == (7 : Int32) then
      let t'18 ← PMem.ldU8 ch_flag
      if (t'18 == (2 : UInt8)) then
        let t'19 ← PMem.ldU64 ((0x86d8 : UInt64) /- &copter -/ + 9488)
        let mut sc'22 := (t'19 == ((0x86d8 : UInt64) /- &copter -/ + 11368))
        if !sc'22 then
          let t'20 ← PMem.ldU64 ((0x86d8 : UInt64) /- &copter -/ + 9528)
          let t'21 ← AP_Motors.armed t'20
          sc'22 := !t'21
        if sc'22 then
          break
        let t'23 ← AP_Mission.present (((0x86d8 : UInt64) /- &copter -/ + 11368) + 112)
        let mut sc'26 := !t'23
        if sc'26 then
          let t'24 ← PMem.ldU64 ((0x86d8 : UInt64) /- &copter -/ + 8616)
          let t'25 ← RC_Channel.get_control_in t'24
          sc'26 := ((Int16.toInt32 (t'25)) == (0 : Int32))
        if sc'26 then
          break
        discard <| PMem.memset ((fp + 0) + 0) 0 2
        discard <| PMem.memset ((fp + 0) + 2) 0 2
        discard <| PMem.memset ((fp + 0) + 4) 0 2
        AP_Mission.Content.Content ((fp + 0) + 8)
        discard <| PMem.memset ((fp + 0) + 24) 0 1
        let t'27 ← AP_Mission.present (((0x86d8 : UInt64) /- &copter -/ + 11368) + 112)
        if !t'27 then
          let t'28 := UInt32.toUInt16 ((22 : UInt32))
          PMem.stU16 ((fp + 0) + 2) t'28
          PMem.stI32 (fp + 28) (100 : Int32)
          let t'29 ← MAX'int_int (((0x86d8 : UInt64) /- &copter -/ + 11148) + 4) (fp + 28)
          let t'30 ← PMem.ldI32 t'29
          PMem.stI32 (((fp + 0) + 8) + 4) t'30
          let t'31 ← AP_Mission.add_cmd (((0x86d8 : UInt64) /- &copter -/ + 11368) + 112) (fp + 0)
          if t'31 then
            pure ()
        discard <| PMem.memcpy ((fp + 0) + 8) ((0x86d8 : UInt64) /- &copter -/ + 11148) 16
        discard <| pure (((fp + 0) + 8))
        let t'32 ← PMem.ldU64 ((0x86d8 : UInt64) /- &copter -/ + 8616)
        let t'33 ← RC_Channel.get_control_in t'32
        if (decide ((Int16.toInt32 (t'33)) > (0 : Int32))) then
          let t'34 := UInt32.toUInt16 ((16 : UInt32))
          PMem.stU16 ((fp + 0) + 2) t'34
        else
          let t'35 := UInt32.toUInt16 ((21 : UInt32))
          PMem.stU16 ((fp + 0) + 2) t'35
        let t'36 ← AP_Mission.add_cmd (((0x86d8 : UInt64) /- &copter -/ + 11368) + 112) (fp + 0)
        if t'36 then
          pure ()
    else if sw'2 == (16 : Int32) then
      let t'37 ← PMem.ldU8 ch_flag
      RC_Channel_Copter.do_aux_function_change_mode'rec rec'd this (3 : UInt8) t'37
    else if sw'2 == (18 : Int32) then
      let t'38 ← PMem.ldU8 ch_flag
      RC_Channel_Copter.do_aux_function_change_mode'rec rec'd this (9 : UInt8) t'38
    else if sw'2 == (55 : Int32) then
      let t'39 ← PMem.ldU8 ch_flag
      RC_Channel_Copter.do_aux_function_change_mode'rec rec'd this (4 : UInt8) t'39
    else if sw'2 == (56 : Int32) then
      let t'40 ← PMem.ldU8 ch_flag
      RC_Channel_Copter.do_aux_function_change_mode'rec rec'd this (5 : UInt8) t'40
    else if sw'2 == (57 : Int32) then
      let t'41 ← PMem.ldU8 ch_flag
      RC_Channel_Copter.do_aux_function_change_mode'rec rec'd this (23 : UInt8) t'41
    else if sw'2 == (25 : Int32) then
      let t'42 ← PMem.ldU8 ch_flag
      let t'43 ← PMem.ldU64 ((0x86d8 : UInt64) /- &copter -/ + 11168)
      AC_AttitudeControl.bf_feedforward t'43 (t'42 == (2 : UInt8))
    else if sw'2 == (26 : Int32) then
      let t'44 ← PMem.ldU8 ch_flag
      let t'45 ← PMem.ldU64 ((0x86d8 : UInt64) /- &copter -/ + 11168)
      AC_AttitudeControl.accel_limiting t'45 (t'44 == (2 : UInt8))
    else if sw'2 == (32 : Int32) then
      let t'46 ← PMem.ldU8 ch_flag
      let mut sc'48 := (t'46 == (2 : UInt8))
      if !sc'48 then
        let t'47 ← PMem.ldU8 ch_flag
        sc'48 := (t'47 == (1 : UInt8))
      PMem.stB (((0x86d8 : UInt64) /- &copter -/ + 9448) + 20) sc'48
    else if sw'2 == (33 : Int32) then
      let t'49 ← PMem.ldU8 ch_flag
      RC_Channel_Copter.do_aux_function_change_mode'rec rec'd this (17 : UInt8) t'49
    else if sw'2 == (68 : Int32) then
      let t'50 ← PMem.ldU8 ch_flag
      RC_Channel_Copter.do_aux_function_change_mode'rec rec'd this (0 : UInt8) t'50
    else if sw'2 == (70 : Int32) then
      let t'51 ← PMem.ldU8 ch_flag
      RC_Channel_Copter.do_aux_function_change_mode'rec rec'd this (2 : UInt8) t'51
    else if sw'2 == (72 : Int32) then
      let t'52 ← PMem.ldU8 ch_flag
      RC_Channel_Copter.do_aux_function_change_mode'rec rec'd this (7 : UInt8) t'52
    else if sw'2 == (76 : Int32) then
      let t'53 ← PMem.ldU8 ch_flag
      let sw'54 := t'53
      if sw'54 == (2 : UInt8) then
        PMem.stB ((0x86d8 : UInt64) /- &copter -/ + 11229) true
        let t'55 ← gcs
        GCS.send_text t'55 (6 : UInt32) (0x143f7 : UInt64) /- "Stand By Enabled" -/ (fp + 32)
      else
        PMem.stB ((0x86d8 : UInt64) /- &copter -/ + 11229) false
        let t'56 ← gcs
        GCS.send_text t'56 (6 : UInt32) (0x14408 : UInt64) /- "Stand By Disabled" -/ (fp + 40)
      break
      let t'57 ← PMem.ldU8 ch_flag
      let sw'58 := t'57
      if sw'58 == (2 : UInt8) then
        let t'59 ← PMem.ldU64 ((0x86d8 : UInt64) /- &copter -/ + 9488)
        let t'60 ← vcall'Mode'pause'22 t'59
        if !t'60 then
          let t'61 ← gcs
          GCS.send_text t'61 (4 : UInt32) (0x1441a : UInt64) /- "Flight Mode Pause failed" -/ (fp + 48)
      else if sw'58 == (1 : UInt8) then
        pure ()
      else if sw'58 == (0 : UInt8) then
        let t'62 ← PMem.ldU64 ((0x86d8 : UInt64) /- &copter -/ + 9488)
        let t'63 ← vcall'Mode'resume'23 t'62
        discard <| pure (t'63)
      else
        pure ()
    else if sw'2 == (178 : Int32) then
      let t'64 ← PMem.ldU8 ch_flag
      let sw'65 := t'64
      if sw'65 == (2 : UInt8) then
        let t'66 ← PMem.ldU64 ((0x86d8 : UInt64) /- &copter -/ + 9488)
        let t'67 ← vcall'Mode'pause'22 t'66
        if !t'67 then
          let t'68 ← gcs
          GCS.send_text t'68 (4 : UInt32) (0x1441a : UInt64) /- "Flight Mode Pause failed" -/ (fp + 56)
      else if sw'65 == (1 : UInt8) then
        pure ()
      else if sw'65 == (0 : UInt8) then
        let t'69 ← PMem.ldU64 ((0x86d8 : UInt64) /- &copter -/ + 9488)
        let t'70 ← vcall'Mode'resume'23 t'69
        discard <| pure (t'70)
      else
        pure ()
    else if sw'2 == (84 : Int32) then
      let t'71 ← PMem.ldU8 ch_flag
      RC_Channel_Copter.do_aux_function_change_air_mode this t'71
    else if sw'2 == (159 : Int32) then
      let t'72 ← PMem.ldU8 ch_flag
      RC_Channel_Copter.do_aux_function_change_force_flying this t'72
    else if sw'2 == (99 : Int32) then
      let t'73 ← PMem.ldU8 ch_flag
      RC_Channel_Copter.do_aux_function_change_mode'rec rec'd this (27 : UInt8) t'73
    else if sw'2 == (152 : Int32) then
      let t'74 ← PMem.ldU8 ch_flag
      if (t'74 == (2 : UInt8)) then
        Copter.init_simple_bearing (0x86d8 : UInt64) /- &copter -/
        let t'75 ← gcs
        GCS.send_text t'75 (6 : UInt32) (0x14433 : UInt64) /- "Simple heading reset" -/ (fp + 64)
    else if sw'2 == (154 : Int32) then
      let t'76 ← PMem.ldU8 ch_flag
      RC_Channel.do_aux_function_armdisarm this t'76
      let t'77 ← AP_Arming.is_armed ((0x86d8 : UInt64) /- &copter -/ + 8768)
      if t'77 then
        PMem.stB (((0x86d8 : UInt64) /- &copter -/ + 9448) + 25) true
    else
      let t'78 ← RC_Channel.do_aux_function this trigger
      return t'78
  return true

def RC_Channel_Copter.do_aux_function'rec (rec'depth : Nat) (this : UInt64) (trigger : UInt64) : PMem.M Bool := do
  let rec'd + 1 := rec'depth | PMem.depthOut
  let fp ← PMem.enter 72
  let r ← RC_Channel_Copter.do_aux_function.body'rec rec'd fp this trigger
  PMem.leave fp
  return r

/-- C++ `RC_Channels::run_aux_function : bool (RC_Channel::AUX_FUNC, RC_Channel::AuxSwitchPos, RC_Channel::AuxFuncTrigger::Source, uint16_t)`, `RC_Channel.h:731-733`. -/
def RC_Channels.run_aux_function'rec (rec'depth : Nat) (this : UInt64) (ch_option : Int32) (pos : UInt8) (source : UInt8) (source_index : UInt16) : PMem.M Bool := do
  let rec'd + 1 := rec'depth | PMem.depthOut
  let mut ch_option := ch_option
  let mut pos := pos
  let mut source := source
  let mut source_index := source_index
  let t'1 ← RC_Channels_Copter.channel this (Int8.toUInt8 (Int32.toInt8 ((0 : Int32))))
  let t'2 ← RC_Channel.run_aux_function'rec rec'd t'1 ch_option pos source source_index
  return t'2

/-- C++ `RC_Channel_Copter::do_aux_function_change_mode : void (const Mode::Number, const AuxSwitchPos)`, `RC_Channel_Copter.cpp:163-179`. -/
def RC_Channel_Copter.do_aux_function_change_mode'rec (rec'depth : Nat) (this : UInt64) (mode : UInt8) (ch_flag : UInt8) : PMem.M Unit := do
  let rec'd + 1 := rec'depth | PMem.depthOut
  let mut mode := mode
  let mut ch_flag := ch_flag
  for _ in [0:1] do
    let sw'1 := ch_flag
    if sw'1 == (2 : UInt8) then
      let t'2 ← Copter.set_mode'rec rec'd (0x86d8 : UInt64) /- &copter -/ mode (53 : UInt8)
      discard <| pure (t'2)
      break
      let t'3 ← PMem.ldU64 ((0x86d8 : UInt64) /- &copter -/ + 9488)
      let t'4 ← vcall'Mode'mode_number'1 t'3
      if (t'4 == mode) then
        let t'5 ← rc
        RC_Channels.reset_mode_switch'rec rec'd t'5
    else
      let t'6 ← PMem.ldU64 ((0x86d8 : UInt64) /- &copter -/ + 9488)
      let t'7 ← vcall'Mode'mode_number'1 t'6
      if (t'7 == mode) then
        let t'8 ← rc
        RC_Channels.reset_mode_switch'rec rec'd t'8
  return ()

/-- C++ `Copter::failsafe_ekf_event : void ()`, `ekf_check.cpp:166-216`. -/
def Copter.failsafe_ekf_event.body'rec (rec'depth : Nat) (fp : UInt64) (this : UInt64) : PMem.M Unit := do
  let rec'd + 1 := rec'depth | PMem.depthOut
  let t'1 := if true then (1 : UInt8) else (0 : UInt8)
  PMem.stBits (this + 9508) 74 1 (UInt8.toUInt64 (t'1))
  let t'2 ← PMem.ldU64 (this + 9528)
  let t'3 ← AP_Motors.armed t'2
  if !t'3 then
    return ()
  PMem.stB ((0xccc0 : UInt64) /- &AP_Notify::flags -/ + 13) true
  let t'4 ← AP_Enum'Parameters_FS_EKF_Action.operator_const_Parameters.FS_EKF_Action ((this + 6776) + 52)
  let mut report_only : Bool := (t'4 == (0 : Int32))
  let t'5 ← Copter.landing_with_GPS this
  let mut landing_with_position : Bool := t'5
  if (landing_with_position && (!report_only)) then
    ModeLand.do_not_use_GPS (this + 12640)
  let t'6 ← PMem.ldU64 ((0x86d8 : UInt64) /- &copter -/ + 9488)
  let t'7 ← vcall'Mode'requires_position'5 t'6
  let mut sc'9 := !t'7
  if sc'9 then
    let t'8 ← AP_Enum'Parameters_FS_EKF_Action.operator_const_Parameters.FS_EKF_Action ((this + 6776) + 52)
    sc'9 := (t'8 != (3 : Int32))
  let mut no_action_in_current_mode : Bool := sc'9
  if ((report_only || landing_with_position) || no_action_in_current_mode) then
    let t'10 ← Copter.gcs this
    GCS.send_text t'10 (2 : UInt32) (0x14570 : UInt64) /- "EKF Failsafe" -/ (fp + 0)
    return ()
  let t'11 ← AP_Enum'Parameters_FS_EKF_Action.operator_const_Parameters.FS_EKF_Action ((this + 6776) + 52)
  let sw'12 := t'11
  if sw'12 == (0 : Int32) then
    pure ()
  else if sw'12 == (2 : Int32) then
    let t'13 ← PMem.ldBits (this + 9508) 72 1
    let mut sc'15 := (UInt64.toUInt8 (t'13)) != (0 : UInt8)
    if !sc'15 then
      let t'14 ← Copter.set_mode'rec rec'd this (2 : UInt8) (6 : UInt8)
      sc'15 := !t'14
    if sc'15 then
      Copter.set_mode_land_with_pause'rec rec'd this (6 : UInt8)
  else if sw'12 == (1 : Int32) || sw'12 == (3 : Int32) then
    Copter.set_mode_land_with_pause'rec rec'd this (6 : UInt8)
  else
    Copter.set_mode_land_with_pause'rec rec'd this (6 : UInt8)
  let t'16 ← PMem.ldU64 (this + 9488)
  let t'17 ← vcall'Mode'name'8 t'16
  PMem.stU64 (fp + 8) t'17
  let t'18 ← Copter.gcs this
  GCS.send_text t'18 (2 : UInt32) (0x1457d : UInt64) /- "EKF Failsafe: changed to %s Mode" -/ (fp + 8)
  return ()

def Copter.failsafe_ekf_event'rec (rec'depth : Nat) (this : UInt64) : PMem.M Unit := do
  let rec'd + 1 := rec'depth | PMem.depthOut
  let fp ← PMem.enter 16
  let r ← Copter.failsafe_ekf_event.body'rec rec'd fp this
  PMem.leave fp
  return r

/-- C++ `Copter::failsafe_terrain_on_event : void ()`, `events.cpp:281-307`. -/
def Copter.failsafe_terrain_on_event.body'rec (rec'depth : Nat) (fp : UInt64) (this : UInt64) : PMem.M Unit := do
  let rec'd + 1 := rec'depth | PMem.depthOut
  let t'1 := if true then (1 : UInt8) else (0 : UInt8)
  PMem.stBits (this + 9508) 75 1 (UInt8.toUInt64 (t'1))
  let t'2 ← PMem.ldU64 (this + 11192)
  let t'3 ← AC_WPNav.get_terrain_source t'2
  let sw'4 := t'3
  if sw'4 == (2 : Int32) then
    PMem.stU64 (fp + 0) (0x1477d : UInt64) /- "data missing" -/
    let t'5 ← Copter.gcs this
    GCS.send_text t'5 (2 : UInt32) (0x14768 : UInt64) /- "Failsafe: Terrain %s" -/ (fp + 0)
  else if sw'4 == (1 : Int32) then
    PMem.stU64 (fp + 8) (0x1478a : UInt64) /- "Rangefinder Unhealthy" -/
    let t'6 ← Copter.gcs this
    GCS.send_text t'6 (2 : UInt32) (0x14768 : UInt64) /- "Failsafe: Terrain %s" -/ (fp + 8)
  else if sw'4 == (0 : Int32) then
    PMem.stU64 (fp + 16) (0x147a0 : UInt64) /- "Unavailable" -/
    let t'7 ← Copter.gcs this
    GCS.send_text t'7 (2 : UInt32) (0x14768 : UInt64) /- "Failsafe: Terrain %s" -/ (fp + 16)
  else
    pure ()
  let t'8 ← Copter.should_disarm_on_failsafe this
  if t'8 then
    let t'9 ← AP_Arming_Copter.disarm (this + 8768) (21 : Int32) true
    discard <| pure (t'9)
  else
    let t'10 ← PMem.ldU64 (this + 9488)
    let t'11 ← vcall'Mode'mode_number'1 t'10
    if (t'11 == (6 : UInt8)) then
      ModeRTL.restart_without_terrain (this + 12888)
    else
      Copter.set_mode_RTL_or_land_with_pause'rec rec'd this (11 : UInt8)
  return ()

def Copter.failsafe_terrain_on_event'rec (rec'depth : Nat) (this : UInt64) : PMem.M Unit := do
  let rec'd + 1 := rec'depth | PMem.depthOut
  let fp ← PMem.enter 24
  let r ← Copter.failsafe_terrain_on_event.body'rec rec'd fp this
  PMem.leave fp
  return r

/-- C++ `ModeAuto::start_command : bool (const AP_Mission::Mission_Command &)`, `mode_auto.cpp:765-901`. -/
def ModeAuto.start_command'rec (rec'depth : Nat) (this : UInt64) (cmd : UInt64) : PMem.M Bool := do
  let rec'd + 1 := rec'depth | PMem.depthOut
  let t'1 ← PMem.ldU16 (cmd + 2)
  let sw'2 := UInt32.toInt32 (UInt16.toUInt32 (t'1))
  if sw'2 == (84 : Int32) || sw'2 == (22 : Int32) then
    ModeAuto.do_takeoff'rec rec'd this cmd
  else if sw'2 == (16 : Int32) || sw'2 == (36 : Int32) then
    ModeAuto.do_nav_wp'rec rec'd this cmd
  else if sw'2 == (85 : Int32) || sw'2 == (21 : Int32) then
    ModeAuto.do_land'rec rec'd this cmd
  else if sw'2 == (17 : Int32) then
    let t'3 ← ModeAuto.do_loiter_unlimited'rec rec'd this cmd
    discard <| pure (t'3)
  else if sw'2 == (18 : Int32) then
    ModeAuto.do_circle'rec rec'd this cmd
  else if sw'2 == (19 : Int32) then
    ModeAuto.do_loiter_time'rec rec'd this cmd
  else if sw'2 == (31 : Int32) then
    ModeAuto.do_loiter_to_alt'rec rec'd this cmd
  else if sw'2 == (20 : Int32) then
    ModeAuto.do_RTL'rec rec'd this
  else if sw'2 == (82 : Int32) then
    ModeAuto.do_spline_wp'rec rec'd this cmd
  else if sw'2 == (92 : Int32) then
    ModeAuto.do_nav_guided_enable'rec rec'd this cmd
  else if sw'2 == (93 : Int32) then
    ModeAuto.do_nav_delay this cmd
  else if sw'2 == (42703 : Int32) then
    ModeAuto.do_nav_attitude_time'rec rec'd this cmd
  else if sw'2 == (112 : Int32) then
    ModeAuto.do_wait_delay this cmd
  else if sw'2 == (114 : Int32) then
    ModeAuto.do_within_distance this cmd
  else if sw'2 == (115 : Int32) then
    ModeAuto.do_yaw this cmd
  else if sw'2 == (178 : Int32) then
    ModeAuto.do_change_speed this cmd
  else if sw'2 == (179 : Int32) then
    ModeAuto.do_set_home this cmd
  else if sw'2 == (195 : Int32) || sw'2 == (197 : Int32) || sw'2 == (201 : Int32) then
    ModeAuto.do_roi this cmd
  else if sw'2 == (222 : Int32) then
    ModeAuto.do_guided_limits this cmd
  else if sw'2 == (188 : Int32) || sw'2 == (189 : Int32) then
    pure ()
  else
    return false
  return true

/-- C++ `ModeAuto::exit_mission : void ()`, `mode_auto.cpp:904-918`. -/
def ModeAuto.exit_mission'rec (rec'depth : Nat) (this : UInt64) : PMem.M Unit := do
  let rec'd + 1 := rec'depth | PMem.depthOut
  let t'1 := Int32.toUInt32 ((1 : Int32))
  PMem.stBits (0xce38 : UInt64) /- &AP_Notify::events -/ 7 1 (UInt32.toUInt64 (t'1))
  let t'2 ← PMem.ldB (((0x86d8 : UInt64) /- &copter -/ + 9448) + 7)
  if !t'2 then
    let t'3 ← ModeAuto.loiter_start'rec rec'd this
    if !t'3 then
      let t'4 ← Mode.set_mode'rec rec'd this (9 : UInt8) (8 : UInt8)
      discard <| pure (t'4)
  else
    let t'5 ← AP_Arming_Copter.disarm ((0x86d8 : UInt64) /- &copter -/ + 8768) (14 : Int32) true
    discard <| pure (t'5)
  return ()

/-- C++ `ModeAuto::do_takeoff : void (const AP_Mission::Mission_Command &)`, `mode_auto.cpp:1540-1544`. -/
def ModeAuto.do_takeoff'rec (rec'depth : Nat) (this : UInt64) (cmd : UInt64) : PMem.M Unit := do
  let rec'd + 1 := rec'depth | PMem.depthOut
  ModeAuto.takeoff_start'rec rec'd this (cmd + 8)
  return ()

/-- C++ `ModeAuto::do_nav_wp : void (const AP_Mission::Mission_Command &)`, `mode_auto.cpp:1578-1616`. -/
def ModeAuto.do_nav_wp.body'rec (rec'depth : Nat) (fp : UInt64) (this : UInt64) (cmd : UInt64) : PMem.M Unit := do
  let rec'd + 1 := rec'depth | PMem.depthOut
  discard <| PMem.memcpy (fp + 0) ((0x86d8 : UInt64) /- &copter -/ + 11148) 16
  ModeAuto.subtract_pos_offsets this (fp + 0)
  let t'1 ← PMem.ldU64 (this + 24)
  let t'2 ← PMem.ldU64 t'1
  let t'3 ← AC_WPNav.is_active t'2
  let mut sc'7 := t'3
  if sc'7 then
    let t'4 ← PMem.ldU64 (this + 24)
    let t'5 ← PMem.ldU64 t'4
    let t'6 ← AC_WPNav.reached_wp_destination t'5
    sc'7 := t'6
  if sc'7 then
    let t'8 ← PMem.ldU64 (this + 24)
    let t'9 ← PMem.ldU64 t'8
    let t'10 ← AC_WPNav.get_wp_destination_loc t'9 (fp + 0)
    if !t'10 then
      pure ()
  Location.Location (fp + 16)
  let t'11 ← ModeAuto.get_loc_from_cmd this cmd (fp + 0) (fp + 16)
  let mut sc'13 := !t'11
  if !sc'13 then
    let t'12 ← ModeAuto.wp_start'rec rec'd this (fp + 16)
    sc'13 := !t'12
  if sc'13 then
    Copter.failsafe_terrain_on_event'rec rec'd (0x86d8 : UInt64) /- &copter -/
    return ()
  let t'14 := Int32.toUInt32 ((0 : Int32))
  PMem.stU32 (this + 824) t'14
  let t'15 ← PMem.ldU16 (cmd + 2)
  if ((UInt32.toInt32 (UInt16.toUInt32 (t'15))) == (UInt32.toInt32 ((36 : UInt32)))) then
    let t'16 := Int16.toUInt16 (Int32.toInt16 ((0 : Int32)))
    PMem.stU16 (this + 822) t'16
  else
    let t'17 ← PMem.ldU16 (cmd + 4)
    PMem.stU16 (this + 822) t'17
  let t'18 ← ModeAuto.set_next_wp this cmd (fp + 16)
  if !t'18 then
    Copter.failsafe_terrain_on_event'rec rec'd (0x86d8 : UInt64) /- &copter -/
    return ()
  return ()

def ModeAuto.do_nav_wp'rec (rec'depth : Nat) (this : UInt64) (cmd : UInt64) : PMem.M Unit := do
  let rec'd + 1 := rec'depth | PMem.depthOut
  let fp ← PMem.enter 32
  let r ← ModeAuto.do_nav_wp.body'rec rec'd fp this cmd
  PMem.leave fp
  return r

/-- C++ `ModeAuto::do_land : void (const AP_Mission::Mission_Command &)`, `mode_auto.cpp:1691-1722`. -/
def ModeAuto.do_land.body'rec (rec'depth : Nat) (fp : UInt64) (this : UInt64) (cmd : UInt64) : PMem.M Unit := do
  let rec'd + 1 := rec'depth | PMem.depthOut
  let t'1 ← PMem.ldI32 ((cmd + 8) + 8)
  let mut sc'3 := (t'1 != (0 : Int32))
  if !sc'3 then
    let t'2 ← PMem.ldI32 ((cmd + 8) + 12)
    sc'3 := (t'2 != (0 : Int32))
  if sc'3 then
    PMem.stI32 (this + 856) (0 : Int32)
    discard <| PMem.memcpy (fp + 0) ((0x86d8 : UInt64) /- &copter -/ + 11148) 16
    ModeAuto.subtract_pos_offsets this (fp + 0)
    discard <| PMem.memcpy (fp + 16) cmd 28
    PMem.stI32 (((fp + 16) + 8) + 4) (0 : Int32)
    Location.Location (fp + 48)
    let t'4 ← ModeAuto.get_loc_from_cmd this (fp + 16) (fp + 0) (fp + 48)
    let mut sc'6 := !t'4
    if !sc'6 then
      let t'5 ← ModeAuto.wp_start'rec rec'd this (fp + 48)
      sc'6 := !t'5
    if sc'6 then
      Copter.failsafe_terrain_on_event'rec rec'd (0x86d8 : UInt64) /- &copter -/
      return ()
  else
    PMem.stI32 (this + 856) (1 : Int32)
    ModeAuto.land_start'rec rec'd this
  return ()

def ModeAuto.do_land'rec (rec'depth : Nat) (this : UInt64) (cmd : UInt64) : PMem.M Unit := do
  let rec'd + 1 := rec'depth | PMem.depthOut
  let fp ← PMem.enter 64
  let r ← ModeAuto.do_land.body'rec rec'd fp this cmd
  PMem.leave fp
  return r

/-- C++ `ModeAuto::do_loiter_unlimited : bool (const AP_Mission::Mission_Command &)`, `mode_auto.cpp:1726-1751`. -/
def ModeAuto.do_loiter_unlimited.body'rec (rec'depth : Nat) (fp : UInt64) (this : UInt64) (cmd : UInt64) : PMem.M Bool := do
  let rec'd + 1 := rec'depth | PMem.depthOut
  discard <| PMem.memcpy (fp + 0) ((0x86d8 : UInt64) /- &copter -/ + 11148) 16
  ModeAuto.subtract_pos_offsets this (fp + 0)
  let t'1 ← PMem.ldU64 (this + 24)
  let t'2 ← PMem.ldU64 t'1
  let t'3 ← AC_WPNav.is_active t'2
  let mut sc'7 := t'3
  if sc'7 then
    let t'4 ← PMem.ldU64 (this + 24)
    let t'5 ← PMem.ldU64 t'4
    let t'6 ← AC_WPNav.reached_wp_destination t'5
    sc'7 := t'6
  if sc'7 then
    let t'8 ← PMem.ldU64 (this + 24)
    let t'9 ← PMem.ldU64 t'8
    let t'10 ← AC_WPNav.get_wp_destination_loc t'9 (fp + 0)
    if !t'10 then
      pure ()
  Location.Location (fp + 16)
  let t'11 ← ModeAuto.get_loc_from_cmd this cmd (fp + 0) (fp + 16)
  let mut sc'13 := !t'11
  if !sc'13 then
    let t'12 ← ModeAuto.wp_start'rec rec'd this (fp + 16)
    sc'13 := !t'12
  if sc'13 then
    Copter.failsafe_terrain_on_event'rec rec'd (0x86d8 : UInt64) /- &copter -/
    return false
  return true

def ModeAuto.do_loiter_unlimited'rec (rec'depth : Nat) (this : UInt64) (cmd : UInt64) : PMem.M Bool := do
  let rec'd + 1 := rec'depth | PMem.depthOut
  let fp ← PMem.enter 32
  let r ← ModeAuto.do_loiter_unlimited.body'rec rec'd fp this cmd
  PMem.leave fp
  return r

/-- C++ `ModeAuto::do_circle : void (const AP_Mission::Mission_Command &)`, `mode_auto.cpp:1754-1785`. -/
def ModeAuto.do_circle.body'rec (rec'depth : Nat) (fp : UInt64) (this : UInt64) (cmd : UInt64) : PMem.M Unit := do
  let rec'd + 1 := rec'depth | PMem.depthOut
  discard <| PMem.memcpy (fp + 0) ((0x86d8 : UInt64) /- &copter -/ + 11148) 16
  ModeAuto.subtract_pos_offsets this (fp + 0)
  Location.Location (fp + 16)
  let t'1 ← ModeAuto.get_loc_from_cmd this cmd (fp + 0) (fp + 16)
  if !t'1 then
    Copter.failsafe_terrain_on_event'rec rec'd (0x86d8 : UInt64) /- &copter -/
    return ()
  let t'2 ← PMem.ldU16 (cmd + 4)
  let mut radius_m : UInt16 := UInt8.toUInt16 ((Int8.toUInt8 (Int32.toInt8 (((UInt32.toInt32 (UInt16.toUInt32 (t'2))) >>> (8 : Int32))))))
  let t'3 ← PMem.ldU16 (cmd + 2)
  let mut sc'5 := ((UInt32.toInt32 (UInt16.toUInt32 (t'3))) == (UInt32.toInt32 ((18 : UInt32))))
  if sc'5 then
    let t'4 ← PMem.ldU8 (cmd + 24)
    sc'5 := ((UInt8.toUInt32 (t'4)) &&& ((1 : UInt32) <<< (Int32.toUInt32 ((0 : Int32))))) != (0 : UInt32)
  if sc'5 then
    let t'6 := (radius_m * (Int16.toUInt16 (Int32.toInt16 ((10 : Int32)))))
    radius_m := t'6
  let t'7 ← PMem.ldBits (cmd + 8) 1 1
  let mut circle_direction_ccw : Bool := (UInt64.toUInt8 (t'7)) != (0 : UInt8)
  let mut c'8 : Binary32 := default
  if circle_direction_ccw then
    c'8 := -(Binary32.ofBits 0x3f800000 /- 1 -/)
  else
    c'8 := (Binary32.ofBits 0x3f800000 /- 1 -/)
  let t'9 ← AP_Mission.Mission_Command.get_loiter_turns cmd
  let t'10 := (c'8 * t'9)
  PMem.stF32 (this + 892) t'10
  ModeAuto.circle_movetoedge_start'rec rec'd this (fp + 16) (UInt16.toBinary32 (radius_m))
  return ()

def ModeAuto.do_circle'rec (rec'depth : Nat) (this : UInt64) (cmd : UInt64) : PMem.M Unit := do
  let rec'd + 1 := rec'depth | PMem.depthOut
  let fp ← PMem.enter 32
  let r ← ModeAuto.do_circle.body'rec rec'd fp this cmd
  PMem.leave fp
  return r

/-- C++ `ModeAuto::do_loiter_time : void (const AP_Mission::Mission_Command &)`, `mode_auto.cpp:1789-1799`. -/
def ModeAuto.do_loiter_time'rec (rec'depth : Nat) (this : UInt64) (cmd : UInt64) : PMem.M Unit := do
  let rec'd + 1 := rec'depth | PMem.depthOut
  let t'1 ← ModeAuto.do_loiter_unlimited'rec rec'd this cmd
  if !t'1 then
    return ()
  let t'2 := Int32.toUInt32 ((0 : Int32))
  PMem.stU32 (this + 824) t'2
  let t'3 ← PMem.ldU16 (cmd + 4)
  PMem.stU16 (this + 822) t'3
  return ()

/-- C++ `ModeAuto::do_loiter_to_alt : void (const AP_Mission::Mission_Command &)`, `mode_auto.cpp:1803-1835`. -/
def ModeAuto.do_loiter_to_alt.body'rec (rec'depth : Nat) (fp : UInt64) (this : UInt64) (cmd : UInt64) : PMem.M Unit := do
  let rec'd + 1 := rec'depth | PMem.depthOut
  let t'1 ← ModeAuto.do_loiter_unlimited'rec rec'd this cmd
  if !t'1 then
    return ()
  discard <| PMem.memcpy (fp + 0) (cmd + 8) 16
  let t'2 ← PMem.ldI32 ((fp + 0) + 8)
  let mut sc'4 := (t'2 == (0 : Int32))
  if sc'4 then
    let t'3 ← PMem.ldI32 ((fp + 0) + 12)
    sc'4 := (t'3 == (0 : Int32))
  if sc'4 then
    let t'5 ← PMem.ldI32 (((0x86d8 : UInt64) /- &copter -/ + 11148) + 8)
    PMem.stI32 ((fp + 0) + 8) t'5
    let t'6 ← PMem.ldI32 (((0x86d8 : UInt64) /- &copter -/ + 11148) + 12)
    PMem.stI32 ((fp + 0) + 12) t'6
  let t'7 ← Location.get_alt_m (fp + 0) (1 : Int32) ((this + 828) + 8)
  if !t'7 then
    PMem.stBits (this + 828) 0 1 (if true then (1 : UInt64) else 0)
    PMem.stBits (this + 828) 2 1 (if true then (1 : UInt64) else 0)
    let t'8 ← Mode.gcs this
    GCS.send_text t'8 (6 : UInt32) (0x14a7e : UInt64) /- "bad do_loiter_to_alt" -/ (fp + 16)
    return ()
  PMem.stBits (this + 828) 0 1 (if false then (1 : UInt64) else 0)
  PMem.stBits (this + 828) 1 1 (if false then (1 : UInt64) else 0)
  PMem.stBits (this + 828) 2 1 (if false then (1 : UInt64) else 0)
  let t'9 := Int32.toBinary32 ((0 : Int32))
  PMem.stF32 ((this + 828) + 4) t'9
  let t'10 ← PMem.ldU64 (this + 24)
  let t'11 ← PMem.ldU64 t'10
  let t'12 ← AC_WPNav.get_default_speed_down_ms t'11
  let t'13 ← PMem.ldU64 (this + 24)
  let t'14 ← PMem.ldU64 t'13
  let t'15 ← AC_WPNav.get_default_speed_up_ms t'14
  let t'16 ← PMem.ldU64 (this + 24)
  let t'17 ← PMem.ldU64 t'16
  let t'18 ← AC_WPNav.get_accel_D_mss t'17
  let t'19 ← PMem.ldU64 (this + 40)
  let t'20 ← PMem.ldU64 t'19
  AC_PosControl.D_set_max_speed_accel_m t'20 t'12 t'15 t'18
  let t'21 ← PMem.ldU64 (this + 24)
  let t'22 ← PMem.ldU64 t'21
  let t'23 ← AC_WPNav.get_default_speed_down_ms t'22
  let t'24 ← PMem.ldU64 (this + 24)
  let t'25 ← PMem.ldU64 t'24
  let t'26 ← AC_WPNav.get_default_speed_up_ms t'25
  let t'27 ← PMem.ldU64 (this + 24)
  let t'28 ← PMem.ldU64 t'27
  let t'29 ← AC_WPNav.get_accel_D_mss t'28
  let t'30 ← PMem.ldU64 (this + 40)
  let t'31 ← PMem.ldU64 t'30
  AC_PosControl.D_set_correction_speed_accel_m t'31 t'23 t'26 t'29
  ModeAuto.set_submode'rec rec'd this (9 : UInt8)
  return ()

def ModeAuto.do_loiter_to_alt'rec (rec'depth : Nat) (this : UInt64) (cmd : UInt64) : PMem.M Unit := do
  let rec'd + 1 := rec'depth | PMem.depthOut
  let fp ← PMem.enter 24
  let r ← ModeAuto.do_loiter_to_alt.body'rec rec'd fp this cmd
  PMem.leave fp
  return r

/-- C++ `ModeAuto::do_RTL : void ()`, `mode_auto.cpp:2130-2134`. -/
def ModeAuto.do_RTL'rec (rec'depth : Nat) (this : UInt64) : PMem.M Unit := do
  let rec'd + 1 := rec'depth | PMem.depthOut
  ModeAuto.rtl_start'rec rec'd this
  return ()

/-- C++ `ModeAuto::do_spline_wp : void (const AP_Mission::Mission_Command &)`, `mode_auto.cpp:1838-1886`. -/
def ModeAuto.do_spline_wp.body'rec (rec'depth : Nat) (fp : UInt64) (this : UInt64) (cmd : UInt64) : PMem.M Unit := do
  let rec'd + 1 := rec'depth | PMem.depthOut
  discard <| PMem.memcpy (fp + 0) ((0x86d8 : UInt64) /- &copter -/ + 11148) 16
  ModeAuto.subtract_pos_offsets this (fp + 0)
  let t'1 ← PMem.ldU64 (this + 24)
  let t'2 ← PMem.ldU64 t'1
  let t'3 ← AC_WPNav.is_active t'2
  let mut sc'7 := t'3
  if sc'7 then
    let t'4 ← PMem.ldU64 (this + 24)
    let t'5 ← PMem.ldU64 t'4
    let t'6 ← AC_WPNav.reached_wp_destination t'5
    sc'7 := t'6
  if sc'7 then
    let t'8 ← PMem.ldU64 (this + 24)
    let t'9 ← PMem.ldU64 t'8
    let t'10 ← AC_WPNav.get_wp_destination_loc t'9 (fp + 0)
    if !t'10 then
      pure ()
  Location.Location (fp + 16)
  Location.Location (fp + 32)
  let t'11 ← ModeAuto.get_spline_from_cmd this cmd (fp + 0) (fp + 16) (fp + 32) (fp + 48)
  if !t'11 then
    Copter.failsafe_terrain_on_event'rec rec'd (0x86d8 : UInt64) /- &copter -/
    return ()
  let t'12 ← PMem.ldB (fp + 48)
  let t'13 ← PMem.ldU64 (this + 24)
  let t'14 ← PMem.ldU64 t'13
  let t'15 ← AC_WPNav.set_spline_destination_loc t'14 (fp + 16) (fp + 32) t'12
  if !t'15 then
    Copter.failsafe_terrain_on_event'rec rec'd (0x86d8 : UInt64) /- &copter -/
    return ()
  let t'16 := Int32.toUInt32 ((0 : Int32))
  PMem.stU32 (this + 824) t'16
  let t'17 ← PMem.ldU16 (cmd + 4)
  PMem.stU16 (this + 822) t'17
  let t'18 ← ModeAuto.set_next_wp this cmd (fp + 16)
  if !t'18 then
    Copter.failsafe_terrain_on_event'rec rec'd (0x86d8 : UInt64) /- &copter -/
    return ()
  let t'19 ← Mode.AutoYaw.mode (0xeb78 : UInt64) /- &Mode::auto_yaw -/
  let mut sc'23 := (t'19 != (2 : Int32))
  if sc'23 then
    let t'20 ← Mode.AutoYaw.mode (0xeb78 : UInt64) /- &Mode::auto_yaw -/
    let mut sc'22 := (t'20 == (3 : Int32))
    if sc'22 then
      let t'21 ← AP_Enum'Parameters_WPYawBehavior.operator_const_Parameters.WPYawBehavior (((0x86d8 : UInt64) /- &copter -/ + 6776) + 25)
      sc'22 := (t'21 == (0 : Int32))
    sc'23 := !sc'22
  if sc'23 then
    Mode.AutoYaw.set_mode_to_default (0xeb78 : UInt64) /- &Mode::auto_yaw -/ false
  ModeAuto.set_submode'rec rec'd this (2 : UInt8)
  return ()

def ModeAuto.do_spline_wp'rec (rec'depth : Nat) (this : UInt64) (cmd : UInt64) : PMem.M Unit := do
  let rec'd + 1 := rec'depth | PMem.depthOut
  let fp ← PMem.enter 49
  let r ← ModeAuto.do_spline_wp.body'rec rec'd fp this cmd
  PMem.leave fp
  return r

/-- C++ `ModeAuto::do_nav_guided_enable : void (const AP_Mission::Mission_Command &)`, `mode_auto.cpp:1916-1922`. -/
def ModeAuto.do_nav_guided_enable'rec (rec'depth : Nat) (this : UInt64) (cmd : UInt64) : PMem.M Unit := do
  let rec'd + 1 := rec'depth | PMem.depthOut
  let t'1 ← PMem.ldU16 (cmd + 4)
  if (decide ((UInt32.toInt32 (UInt16.toUInt32 (t'1))) > (0 : Int32))) then
    ModeAuto.nav_guided_start'rec rec'd this
  return ()

/-- C++ `ModeAuto::do_nav_attitude_time : void (const AP_Mission::Mission_Command &)`, `mode_auto.cpp:1978-1987`. -/
def ModeAuto.do_nav_attitude_time'rec (rec'depth : Nat) (this : UInt64) (cmd : UInt64) : PMem.M Unit := do
  let rec'd + 1 := rec'depth | PMem.depthOut
  let t'1 ← PMem.ldI16 ((cmd + 8) + 2)
  PMem.stI16 (this + 864) t'1
  let t'2 ← PMem.ldI8 ((cmd + 8) + 4)
  PMem.stI8 ((this + 864) + 2) t'2
  let t'3 ← PMem.ldI16 ((cmd + 8) + 5)
  PMem.stI16 ((this + 864) + 4) t'3
  let t'4 ← PMem.ldI16 ((cmd + 8) + 7)
  let t'5 := Int16.toBinary32 (t'4)
  PMem.stF32 ((this + 864) + 8) t'5
  let t'6 := ((← PMem.clock) / 1000).toUInt32
  PMem.stU32 ((this + 864) + 12) t'6
  ModeAuto.set_submode'rec rec'd this (11 : UInt8)
  return ()

/-- C++ `ModeAuto::loiter_start : bool ()`, `mode_auto.cpp:374-395`. -/
def ModeAuto.loiter_start.body'rec (rec'depth : Nat) (fp : UInt64) (this : UInt64) : PMem.M Bool := do
  let rec'd + 1 := rec'depth | PMem.depthOut
  let t'1 ← Copter.position_ok (0x86d8 : UInt64) /- &copter -/
  if !t'1 then
    return false
  Vector3'double.Vector3 (fp + 0)
  let t'2 ← PMem.ldU64 (this + 24)
  let t'3 ← PMem.ldU64 t'2
  AC_WPNav.get_wp_stopping_point_NED_m t'3 (fp + 0)
  let t'4 ← PMem.ldU64 (this + 24)
  let t'5 ← PMem.ldU64 t'4
  let t'6 ← AC_WPNav.set_wp_destination_NED_m t'5 (fp + 0) false (Binary64.toBinary32 ((Binary64.ofBits 0x0000000000000000 /- 0 -/)))
  discard <| pure (t'6)
  Mode.AutoYaw.set_mode (0xeb78 : UInt64) /- &Mode::auto_yaw -/ (0 : Int32)
  ModeAuto.set_submode'rec rec'd this (8 : UInt8)
  return true

def ModeAuto.loiter_start'rec (rec'depth : Nat) (this : UInt64) : PMem.M Bool := do
  let rec'd + 1 := rec'depth | PMem.depthOut
  let fp ← PMem.enter 24
  let r ← ModeAuto.loiter_start.body'rec rec'd fp this
  PMem.leave fp
  return r

/-- C++ `ModeAuto::takeoff_start : void (const Location &)`, `mode_auto.cpp:410-462`. -/
def ModeAuto.takeoff_start.body'rec (rec'depth : Nat) (fp : UInt64) (this : UInt64) (dest_loc : UInt64) : PMem.M Unit := do
  let rec'd + 1 := rec'depth | PMem.depthOut
  let t'1 ← Location.initialised ((0x86d8 : UInt64) /- &copter -/ + 11148)
  if !t'1 then
    return ()
  let mut alt_target_terrain : Bool := false
  let t'2 ← PMem.ldU64 (this + 40)
  let t'3 ← PMem.ldU64 t'2
  let t'4 ← AC_PosControl.get_pos_estimate_U_m t'3
  let mut current_alt_m : Binary32 := t'4
  let t'5 ← Location.get_alt_frame dest_loc
  let mut sc'9 := (t'5 == (3 : Int32))
  if sc'9 then
    let t'6 ← PMem.ldU64 (this + 24)
    let t'7 ← PMem.ldU64 t'6
    let t'8 ← AC_WPNav.get_terrain_U_m t'7 (fp + 8)
    sc'9 := t'8
  if sc'9 then
    let t'10 ← PMem.ldF32 (fp + 8)
    let t'11 := (current_alt_m - t'10)
    current_alt_m := t'11
    let t'12 ← PMem.ldI32 (dest_loc + 4)
    let t'13 := ((Int32.toBinary32 (t'12)) * (Binary64.toBinary32 ((Binary64.ofBits 0x3f847ae147ae147b /- 1/100 -/))))
    PMem.stF32 (fp + 0) t'13
    alt_target_terrain := true
  else
    discard <| PMem.memcpy (fp + 16) dest_loc 16
    let t'14 ← PMem.ldI32 (((0x86d8 : UInt64) /- &copter -/ + 11148) + 8)
    PMem.stI32 ((fp + 16) + 8) t'14
    let t'15 ← PMem.ldI32 (((0x86d8 : UInt64) /- &copter -/ + 11148) + 12)
    PMem.stI32 ((fp + 16) + 12) t'15
    let t'16 ← Location.get_alt_m (fp + 16) (2 : Int32) (fp + 0)
    if !t'16 then
      let t'17 ← PMem.ldI32 ((fp + 16) + 4)
      let t'18 := (current_alt_m + ((Int32.toBinary32 (t'17)) * (Binary64.toBinary32 ((Binary64.ofBits 0x3f847ae147ae147b /- 1/100 -/)))))
      PMem.stF32 (fp + 0) t'18
  let t'19 ← PMem.ldB (((0x86d8 : UInt64) /- &copter -/ + 9448) + 7)
  let mut c'20 : Binary32 := default
  if t'19 then
    c'20 := Binary64.toBinary32 ((Binary64.ofBits 0x3ff0000000000000 /- 1 -/))
  else
    c'20 := Binary64.toBinary32 ((Binary64.ofBits 0x0000000000000000 /- 0 -/))
  PMem.stF32 (fp + 32) (current_alt_m + c'20)
  let t'21 ← MAX'float_float (fp + 0) (fp + 32)
  let t'22 ← PMem.ldF32 t'21
  PMem.stF32 (fp + 0) t'22
  Mode.AutoYaw.set_mode (0xeb78 : UInt64) /- &Mode::auto_yaw -/ (0 : Int32)
  let t'23 ← PMem.ldU64 (this + 40)
  let t'24 ← PMem.ldU64 t'23
  AC_PosControl.D_init_controller t'24
  let t'25 ← PMem.ldF32 (fp + 0)
  _AutoTakeoff.start_m (0x131b0 : UInt64) /- &Mode::auto_takeoff -/ t'25 alt_target_terrain
  ModeAuto.set_submode'rec rec'd this (1 : UInt8)
  return ()

def ModeAuto.takeoff_start'rec (rec'depth : Nat) (this : UInt64) (dest_loc : UInt64) : PMem.M Unit := do
  let rec'd + 1 := rec'depth | PMem.depthOut
  let fp ← PMem.enter 36
  let r ← ModeAuto.takeoff_start.body'rec rec'd fp this dest_loc
  PMem.leave fp
  return r

/-- C++ `ModeAuto::wp_start : bool (const Location &)`, `mode_auto.cpp:465-502`. -/
def ModeAuto.wp_start.body'rec (rec'depth : Nat) (fp : UInt64) (this : UInt64) (dest_loc : UInt64) : PMem.M Bool := do
  let rec'd + 1 := rec'depth | PMem.depthOut
  let t'1 ← PMem.ldU64 (this + 24)
  let t'2 ← PMem.ldU64 t'1
  let t'3 ← AC_WPNav.is_active t'2
  if !t'3 then
    Vector3'double.Vector3 (fp + 0)
    let t'4 ← PMem.ldU8 (this + 820)
    if (t'4 == (1 : UInt8)) then
      Vector3'double.Vector3 (fp + 24)
      let t'5 ← _AutoTakeoff.get_completion_pos_ned_m (0x131b0 : UInt64) /- &Mode::auto_takeoff -/ (fp + 24)
      if t'5 then
        discard <| PMem.memcpy (fp + 0) (fp + 24) 24
        discard <| pure ((fp + 0))
    let t'6 ← PMem.ldF32 (this + 880)
    let t'7 ← is_positive'float t'6
    let mut c'8 : Binary32 := default
    if t'7 then
      let t'9 ← PMem.ldF32 (this + 880)
      c'8 := t'9
    else
      c'8 := Int32.toBinary32 ((0 : Int32))
    let mut des_speed_xy_ms : Binary32 := c'8
    Vector3'double.Vector3'4 (fp + 48) (fp + 0)
    let t'10 ← PMem.ldU64 (this + 24)
    let t'11 ← PMem.ldU64 t'10
    AC_WPNav.wp_and_spline_init_m t'11 des_speed_xy_ms (fp + 48)
    let t'12 ← PMem.ldF32 ((this + 880) + 4)
    let t'13 ← is_positive'float t'12
    if t'13 then
      let t'14 ← PMem.ldF32 ((this + 880) + 4)
      let t'15 ← PMem.ldU64 (this + 24)
      let t'16 ← PMem.ldU64 t'15
      AC_WPNav.set_speed_up_ms t'16 t'14
    let t'17 ← PMem.ldF32 ((this + 880) + 8)
    let t'18 ← is_positive'float t'17
    if t'18 then
      let t'19 ← PMem.ldF32 ((this + 880) + 8)
      let t'20 ← PMem.ldU64 (this + 24)
      let t'21 ← PMem.ldU64 t'20
      AC_WPNav.set_speed_down_ms t'21 t'19
  let t'22 ← PMem.ldU64 (this + 24)
  let t'23 ← PMem.ldU64 t'22
  let t'24 ← AC_WPNav.set_wp_destination_loc t'23 dest_loc (Binary64.toBinary32 ((Binary64.ofBits 0x0000000000000000 /- 0 -/)))
  if !t'24 then
    return false
  let t'25 ← Mode.AutoYaw.mode (0xeb78 : UInt64) /- &Mode::auto_yaw -/
  let mut sc'29 := (t'25 != (2 : Int32))
  if sc'29 then
    let t'26 ← Mode.AutoYaw.mode (0xeb78 : UInt64) /- &Mode::auto_yaw -/
    let mut sc'28 := (t'26 == (3 : Int32))
    if sc'28 then
      let t'27 ← AP_Enum'Parameters_WPYawBehavior.operator_const_Parameters.WPYawBehavior (((0x86d8 : UInt64) /- &copter -/ + 6776) + 25)
      sc'28 := (t'27 == (0 : Int32))
    sc'29 := !sc'28
  if sc'29 then
    Mode.AutoYaw.set_mode_to_default (0xeb78 : UInt64) /- &Mode::auto_yaw -/ false
  ModeAuto.set_submode'rec rec'd this (2 : UInt8)
  return true

def ModeAuto.wp_start'rec (rec'depth : Nat) (this : UInt64) (dest_loc : UInt64) : PMem.M Bool := do
  let rec'd + 1 := rec'depth | PMem.depthOut
  let fp ← PMem.enter 72
  let r ← ModeAuto.wp_start.body'rec rec'd fp this dest_loc
  PMem.leave fp
  return r

/-- C++ `ModeAuto::land_start : void ()`, `mode_auto.cpp:505-541`. -/
def ModeAuto.land_start'rec (rec'depth : Nat) (this : UInt64) : PMem.M Unit := do
  let rec'd + 1 := rec'depth | PMem.depthOut
  let t'1 ← PMem.ldU64 (this + 24)
  let t'2 ← PMem.ldU64 t'1
  let t'3 ← AC_WPNav.get_default_speed_NE_ms t'2
  let t'4 ← PMem.ldU64 (this + 24)
  let t'5 ← PMem.ldU64 t'4
  let t'6 ← AC_WPNav.get_wp_acceleration_mss t'5
  let t'7 ← PMem.ldU64 (this + 40)
  let t'8 ← PMem.ldU64 t'7
  AC_PosControl.NE_set_max_speed_accel_m t'8 t'3 t'6
  let t'9 ← PMem.ldU64 (this + 24)
  let t'10 ← PMem.ldU64 t'9
  let t'11 ← AC_WPNav.get_default_speed_NE_ms t'10
  let t'12 ← PMem.ldU64 (this + 24)
  let t'13 ← PMem.ldU64 t'12
  let t'14 ← AC_WPNav.get_wp_acceleration_mss t'13
  let t'15 ← PMem.ldU64 (this + 40)
  let t'16 ← PMem.ldU64 t'15
  AC_PosControl.NE_set_correction_speed_accel_m t'16 t'11 t'14
  let t'17 ← PMem.ldU64 (this + 40)
  let t'18 ← PMem.ldU64 t'17
  let t'19 ← AC_PosControl.NE_is_active t'18
  if !t'19 then
    let t'20 ← PMem.ldU64 (this + 40)
    let t'21 ← PMem.ldU64 t'20
    AC_PosControl.NE_init_controller t'21
  let t'22 ← PMem.ldU64 (this + 24)
  let t'23 ← PMem.ldU64 t'22
  let t'24 ← AC_WPNav.get_default_speed_down_ms t'23
  let t'25 ← PMem.ldU64 (this + 24)
  let t'26 ← PMem.ldU64 t'25
  let t'27 ← AC_WPNav.get_default_speed_up_ms t'26
  let t'28 ← PMem.ldU64 (this + 24)
  let t'29 ← PMem.ldU64 t'28
  let t'30 ← AC_WPNav.get_accel_D_mss t'29
  let t'31 ← PMem.ldU64 (this + 40)
  let t'32 ← PMem.ldU64 t'31
  AC_PosControl.D_set_max_speed_accel_m t'32 t'24 t'27 t'30
  let t'33 ← PMem.ldU64 (this + 24)
  let t'34 ← PMem.ldU64 t'33
  let t'35 ← AC_WPNav.get_default_speed_down_ms t'34
  let t'36 ← PMem.ldU64 (this + 24)
  let t'37 ← PMem.ldU64 t'36
  let t'38 ← AC_WPNav.get_default_speed_up_ms t'37
  let t'39 ← PMem.ldU64 (this + 24)
  let t'40 ← PMem.ldU64 t'39
  let t'41 ← AC_WPNav.get_accel_D_mss t'40
  let t'42 ← PMem.ldU64 (this + 40)
  let t'43 ← PMem.ldU64 t'42
  AC_PosControl.D_set_correction_speed_accel_m t'43 t'35 t'38 t'41
  let t'44 ← PMem.ldU64 (this + 40)
  let t'45 ← PMem.ldU64 t'44
  let t'46 ← AC_PosControl.D_is_active t'45
  if !t'46 then
    let t'47 ← PMem.ldU64 (this + 40)
    let t'48 ← PMem.ldU64 t'47
    AC_PosControl.D_init_controller t'48
  Mode.AutoYaw.set_mode (0xeb78 : UInt64) /- &Mode::auto_yaw -/ (0 : Int32)
  PMem.stB (((0x86d8 : UInt64) /- &copter -/ + 9448) + 19) false
  PMem.stB (((0x86d8 : UInt64) /- &copter -/ + 9448) + 26) false
  ModeAuto.set_submode'rec rec'd this (3 : UInt8)
  return ()

/-- C++ `ModeAuto::circle_movetoedge_start : void (const Location &, float)`, `mode_auto.cpp:545-589`. -/
def ModeAuto.circle_movetoedge_start.body'rec (rec'depth : Nat) (fp : UInt64) (this : UInt64) (circle_center : UInt64) (radius_m : Binary32) : PMem.M Unit := do
  let rec'd + 1 := rec'depth | PMem.depthOut
  let mut radius_m := radius_m
  let t'1 ← PMem.ldU64 ((0x86d8 : UInt64) /- &copter -/ + 11208)
  AC_Circle.set_center t'1 circle_center
  let t'2 ← PMem.ldU64 ((0x86d8 : UInt64) /- &copter -/ + 11208)
  AC_Circle.set_radius_m t'2 radius_m
  let t'3 ← is_positive'float radius_m
  let mut c'4 : Binary32 := default
  if t'3 then
    let t'5 ← PMem.ldU64 ((0x86d8 : UInt64) /- &copter -/ + 11208)
    let t'6 ← AC_Circle.get_radius_m t'5
    c'4 := t'6
  else
    c'4 := (Binary32.ofBits 0x00000000 /- 0 -/)
  PMem.stF32 ((this + 892) + 4) c'4
  Vector3'double.Vector3 (fp + 0)
  let t'7 ← PMem.ldU64 ((0x86d8 : UInt64) /- &copter -/ + 11208)
  AC_Circle.get_closest_point_on_circle_NED_m t'7 (fp + 0) (fp + 24)
  let t'8 ← PMem.ldU64 ((0x86d8 : UInt64) /- &copter -/ + 11208)
  let t'9 ← AC_Circle.center_is_terrain_alt t'8
  let t'10 ← PMem.ldU64 (this + 24)
  let t'11 ← PMem.ldU64 t'10
  let t'12 ← AC_WPNav.set_wp_destination_NED_m t'11 (fp + 0) t'9 (Binary64.toBinary32 ((Binary64.ofBits 0x0000000000000000 /- 0 -/)))
  if !t'12 then
    Copter.failsafe_terrain_on_event'rec rec'd (0x86d8 : UInt64) /- &copter -/
  let t'13 ← PMem.ldU64 (this + 40)
  let t'14 ← PMem.ldU64 t'13
  let t'15 ← AC_PosControl.get_pos_estimate_NED_m t'14
  let t'16 ← Vector3'double.xy t'15
  Vector2'double.tofloat t'16 (fp + 32)
  let t'17 := (fp + 32)
  let t'18 ← PMem.ldU64 ((0x86d8 : UInt64) /- &copter -/ + 11208)
  let t'19 ← AC_Circle.get_center_NED_m t'18
  let t'20 ← Vector3'double.xy t'19
  Vector2'double.tofloat t'20 (fp + 40)
  let t'21 := (fp + 40)
  let t'22 ← get_horizontal_distance'float t'17 t'21
  let mut dist_to_center_m : Binary32 := t'22
  let t'23 ← Mode.AutoYaw.mode (0xeb78 : UInt64) /- &Mode::auto_yaw -/
  if (t'23 != (2 : Int32)) then
    let t'24 ← PMem.ldF32 ((this + 892) + 4)
    if ((decide (dist_to_center_m > t'24)) && (decide (dist_to_center_m > (Binary64.toBinary32 ((Binary64.ofBits 0x4014000000000000 /- 5 -/)))))) then
      Mode.AutoYaw.set_mode_to_default (0xeb78 : UInt64) /- &Mode::auto_yaw -/ false
    else
      Mode.AutoYaw.set_mode (0xeb78 : UInt64) /- &Mode::auto_yaw -/ (0 : Int32)
  ModeAuto.set_submode'rec rec'd this (5 : UInt8)
  return ()

def ModeAuto.circle_movetoedge_start'rec (rec'depth : Nat) (this : UInt64) (circle_center : UInt64) (radius_m : Binary32) : PMem.M Unit := do
  let rec'd + 1 := rec'depth | PMem.depthOut
  let fp ← PMem.enter 48
  let r ← ModeAuto.circle_movetoedge_start.body'rec rec'd fp this circle_center radius_m
  PMem.leave fp
  return r

/-- C++ `ModeAuto::set_submode : void (SubMode)`, `mode_auto.cpp:194-212`. -/
def ModeAuto.set_submode'rec (rec'depth : Nat) (this : UInt64) (new_submode : UInt8) : PMem.M Unit := do
  let rec'd + 1 := rec'depth | PMem.depthOut
  let mut new_submode := new_submode
  let t'1 ← PMem.ldU8 (this + 820)
  if (new_submode == t'1) then
    return ()
  let t'2 ← PMem.ldU8 (this + 820)
  let mut old_submode : UInt8 := t'2
  PMem.stU8 (this + 820) new_submode
  if (old_submode == (11 : UInt8)) then
    Copter.failsafe_ekf_recheck'rec rec'd (0x86d8 : UInt64) /- &copter -/
  return ()

/-- C++ `ModeAuto::rtl_start : void ()`, `mode_auto.cpp:398-407`. -/
def ModeAuto.rtl_start'rec (rec'depth : Nat) (this : UInt64) : PMem.M Unit := do
  let rec'd + 1 := rec'depth | PMem.depthOut
  let t'1 ← ModeRTL.init ((0x86d8 : UInt64) /- &copter -/ + 12888) true
  if t'1 then
    ModeAuto.set_submode'rec rec'd this (4 : UInt8)
  else
    pure ()
  return ()

/-- C++ `ModeAuto::nav_guided_start : void ()`, `mode_auto.cpp:658-672`. -/
def ModeAuto.nav_guided_start'rec (rec'depth : Nat) (this : UInt64) : PMem.M Unit := do
  let rec'd + 1 := rec'depth | PMem.depthOut
  let t'1 ← ModeGuided.init ((0x86d8 : UInt64) /- &copter -/ + 12520) true
  if !t'1 then
    return ()
  ModeGuided.limit_init_time_and_pos ((0x86d8 : UInt64) /- &copter -/ + 12520)
  ModeAuto.set_submode'rec rec'd this (7 : UInt8)
  return ()

/-- C++ `Copter::failsafe_ekf_recheck : void ()`, `ekf_check.cpp:236-245`. -/
def Copter.failsafe_ekf_recheck'rec (rec'depth : Nat) (this : UInt64) : PMem.M Unit := do
  let rec'd + 1 := rec'depth | PMem.depthOut
  let t'1 ← PMem.ldBits (this + 9508) 74 1
  if !((UInt64.toUInt8 (t'1)) != (0 : UInt8)) then
    return ()
  Copter.failsafe_ekf_event'rec rec'd this
  return ()

/-- Calls through a function pointer of type `void (void *)` at one call site of the Functor's operator: the functions the Functor objects read there can hold (1 of 37; the Functor values of AP_Mission::_mission_complete_fn). -/
def fnptr'0'at'AP_Mission'_mission_complete_fn'rec (rec'depth : Nat) (f : UInt64) (a0 : UInt64) : PMem.M Unit := do
  let rec'd + 1 := rec'depth | PMem.depthOut
  if f == 0x7e000090 then  -- ModeAuto::exit_mission (FUNCTOR_BIND_MEMBER)
    ModeAuto.exit_mission'rec rec'd a0
  else
    PMem.unreached "function pointer void (void *)"
    return ()

/-- (at the call sites reading AP_Mission::_mission_complete_fn) C++ `Functor<void>::operator() : void () const`, `functor.h:52-55`. -/
def Functor'void.operator__'at'AP_Mission'_mission_complete_fn'rec (rec'depth : Nat) (this : UInt64) : PMem.M Unit := do
  let rec'd + 1 := rec'depth | PMem.depthOut
  let t'1 ← PMem.ldU64 (this + 8)
  let t'2 ← PMem.ldU64 this
  fnptr'0'at'AP_Mission'_mission_complete_fn'rec rec'd t'1 t'2
  return ()

/-- Calls through a function pointer of type `bool (void *, const AP_Mission::Mission_Command &)` at one call site of the Functor's operator: the functions the Functor objects read there can hold (1 of 2; the Functor values of AP_Mission::_cmd_start_fn). -/
def fnptr'3'at'AP_Mission'_cmd_start_fn'rec (rec'depth : Nat) (f : UInt64) (a0 : UInt64) (a1 : UInt64) : PMem.M Bool := do
  let rec'd + 1 := rec'depth | PMem.depthOut
  if f == 0x7e000070 then  -- ModeAuto::start_command (FUNCTOR_BIND_MEMBER)
    ModeAuto.start_command'rec rec'd a0 a1
  else
    PMem.unreached "function pointer bool (void *, const AP_Mission::Mission_Command &)"
    return default

/-- (at the call sites reading AP_Mission::_cmd_start_fn) C++ `Functor<bool, const AP_Mission::Mission_Command &>::operator() : bool (const AP_Mission::Mission_Command &) const`, `functor.h:52-55`. -/
def Functor'bool_const_AP_Mission_Mission_Command.operator__'at'AP_Mission'_cmd_start_fn'rec (rec'depth : Nat) (this : UInt64) (args : UInt64) : PMem.M Bool := do
  let rec'd + 1 := rec'depth | PMem.depthOut
  let t'1 ← PMem.ldU64 (this + 8)
  let t'2 ← PMem.ldU64 this
  let t'3 ← fnptr'3'at'AP_Mission'_cmd_start_fn'rec rec'd t'1 t'2 args
  return t'3

end

/-- `Copter.set_mode.body'rec` with the depth of its recursive component (300). -/
def Copter.set_mode.body (fp : UInt64) (this : UInt64) (mode : UInt8) (reason : UInt8) : PMem.M Bool :=
  Copter.set_mode.body'rec 300 fp this mode reason

/-- `Copter.set_mode'rec` with the depth of its recursive component (300). -/
def Copter.set_mode (this : UInt64) (mode : UInt8) (reason : UInt8) : PMem.M Bool :=
  Copter.set_mode'rec 300 this mode reason

/-- `ModeAuto.return_path_or_jump_to_landing_sequence_auto_RTL.body'rec` with the depth of its recursive component (300). -/
def ModeAuto.return_path_or_jump_to_landing_sequence_auto_RTL.body (fp : UInt64) (this : UInt64) (reason : UInt8) : PMem.M Bool :=
  ModeAuto.return_path_or_jump_to_landing_sequence_auto_RTL.body'rec 300 fp this reason

/-- `ModeAuto.return_path_or_jump_to_landing_sequence_auto_RTL'rec` with the depth of its recursive component (300). -/
def ModeAuto.return_path_or_jump_to_landing_sequence_auto_RTL (this : UInt64) (reason : UInt8) : PMem.M Bool :=
  ModeAuto.return_path_or_jump_to_landing_sequence_auto_RTL'rec 300 this reason

/-- `RC_Channels.reset_mode_switch'rec` with the depth of its recursive component (300). -/
def RC_Channels.reset_mode_switch (this : UInt64) : PMem.M Unit :=
  RC_Channels.reset_mode_switch'rec 300 this

/-- `AP_Mission.jump_to_closest_mission_leg.body'rec` with the depth of its recursive component (300). -/
def AP_Mission.jump_to_closest_mission_leg.body (fp : UInt64) (this : UInt64) (current_loc : UInt64) : PMem.M Bool :=
  AP_Mission.jump_to_closest_mission_leg.body'rec 300 fp this current_loc

/-- `AP_Mission.jump_to_closest_mission_leg'rec` with the depth of its recursive component (300). -/
def AP_Mission.jump_to_closest_mission_leg (this : UInt64) (current_loc : UInt64) : PMem.M Bool :=
  AP_Mission.jump_to_closest_mission_leg'rec 300 this current_loc

/-- `AP_Mission.jump_to_landing_sequence.body'rec` with the depth of its recursive component (300). -/
def AP_Mission.jump_to_landing_sequence.body (fp : UInt64) (this : UInt64) (current_loc : UInt64) : PMem.M Bool :=
  AP_Mission.jump_to_landing_sequence.body'rec 300 fp this current_loc

/-- `AP_Mission.jump_to_landing_sequence'rec` with the depth of its recursive component (300). -/
def AP_Mission.jump_to_landing_sequence (this : UInt64) (current_loc : UInt64) : PMem.M Bool :=
  AP_Mission.jump_to_landing_sequence'rec 300 this current_loc

/-- `ModeAuto.enter_auto_rtl'rec` with the depth of its recursive component (300). -/
def ModeAuto.enter_auto_rtl (this : UInt64) (reason : UInt8) : PMem.M Bool :=
  ModeAuto.enter_auto_rtl'rec 300 this reason

/-- `RC_Channel.reset_mode_switch'rec` with the depth of its recursive component (300). -/
def RC_Channel.reset_mode_switch (this : UInt64) : PMem.M Unit :=
  RC_Channel.reset_mode_switch'rec 300 this

/-- `AP_Mission.set_current_cmd.body'rec` with the depth of its recursive component (300). -/
def AP_Mission.set_current_cmd.body (fp : UInt64) (this : UInt64) (index : UInt16) : PMem.M Bool :=
  AP_Mission.set_current_cmd.body'rec 300 fp this index

/-- `AP_Mission.set_current_cmd'rec` with the depth of its recursive component (300). -/
def AP_Mission.set_current_cmd (this : UInt64) (index : UInt16) : PMem.M Bool :=
  AP_Mission.set_current_cmd'rec 300 this index

/-- `AP_Mission.resume.body'rec` with the depth of its recursive component (300). -/
def AP_Mission.resume.body (fp : UInt64) (this : UInt64) : PMem.M Unit :=
  AP_Mission.resume.body'rec 300 fp this

/-- `AP_Mission.resume'rec` with the depth of its recursive component (300). -/
def AP_Mission.resume (this : UInt64) : PMem.M Unit :=
  AP_Mission.resume'rec 300 this

/-- `Mode.set_mode'rec` with the depth of its recursive component (300). -/
def Mode.set_mode (this : UInt64) (mode : UInt8) (reason : UInt8) : PMem.M Bool :=
  Mode.set_mode'rec 300 this mode reason

/-- `RC_Channel.read_mode_switch.body'rec` with the depth of its recursive component (300). -/
def RC_Channel.read_mode_switch.body (fp : UInt64) (this : UInt64) : PMem.M Unit :=
  RC_Channel.read_mode_switch.body'rec 300 fp this

/-- `RC_Channel.read_mode_switch'rec` with the depth of its recursive component (300). -/
def RC_Channel.read_mode_switch (this : UInt64) : PMem.M Unit :=
  RC_Channel.read_mode_switch'rec 300 this

/-- `AP_Mission.advance_current_nav_cmd.body'rec` with the depth of its recursive component (300). -/
def AP_Mission.advance_current_nav_cmd.body (fp : UInt64) (this : UInt64) (starting_index : UInt16) : PMem.M Bool :=
  AP_Mission.advance_current_nav_cmd.body'rec 300 fp this starting_index

/-- `AP_Mission.advance_current_nav_cmd'rec` with the depth of its recursive component (300). -/
def AP_Mission.advance_current_nav_cmd (this : UInt64) (starting_index : UInt16) : PMem.M Bool :=
  AP_Mission.advance_current_nav_cmd'rec 300 this starting_index

/-- `AP_Mission.complete'rec` with the depth of its recursive component (300). -/
def AP_Mission.complete (this : UInt64) : PMem.M Unit :=
  AP_Mission.complete'rec 300 this

/-- `AP_Mission.start'rec` with the depth of its recursive component (300). -/
def AP_Mission.start (this : UInt64) : PMem.M Unit :=
  AP_Mission.start'rec 300 this

/-- `AP_Mission.start_command.body'rec` with the depth of its recursive component (300). -/
def AP_Mission.start_command.body (fp : UInt64) (this : UInt64) (cmd : UInt64) : PMem.M Bool :=
  AP_Mission.start_command.body'rec 300 fp this cmd

/-- `AP_Mission.start_command'rec` with the depth of its recursive component (300). -/
def AP_Mission.start_command (this : UInt64) (cmd : UInt64) : PMem.M Bool :=
  AP_Mission.start_command'rec 300 this cmd

/-- `RC_Channel.run_aux_function.body'rec` with the depth of its recursive component (300). -/
def RC_Channel.run_aux_function.body (fp : UInt64) (this : UInt64) (ch_option : Int32) (pos : UInt8) (source : UInt8) (source_index : UInt16) : PMem.M Bool :=
  RC_Channel.run_aux_function.body'rec 300 fp this ch_option pos source source_index

/-- `RC_Channel.run_aux_function'rec` with the depth of its recursive component (300). -/
def RC_Channel.run_aux_function (this : UInt64) (ch_option : Int32) (pos : UInt8) (source : UInt8) (source_index : UInt16) : PMem.M Bool :=
  RC_Channel.run_aux_function'rec 300 this ch_option pos source source_index

/-- `RC_Channel_Copter.mode_switch_changed.body'rec` with the depth of its recursive component (300). -/
def RC_Channel_Copter.mode_switch_changed.body (fp : UInt64) (this : UInt64) (new_pos : Int8) : PMem.M Unit :=
  RC_Channel_Copter.mode_switch_changed.body'rec 300 fp this new_pos

/-- `RC_Channel_Copter.mode_switch_changed'rec` with the depth of its recursive component (300). -/
def RC_Channel_Copter.mode_switch_changed (this : UInt64) (new_pos : Int8) : PMem.M Unit :=
  RC_Channel_Copter.mode_switch_changed'rec 300 this new_pos

/-- `Copter.set_mode_land_with_pause'rec` with the depth of its recursive component (300). -/
def Copter.set_mode_land_with_pause (this : UInt64) (reason : UInt8) : PMem.M Unit :=
  Copter.set_mode_land_with_pause'rec 300 this reason

/-- `Copter.set_mode_RTL_or_land_with_pause'rec` with the depth of its recursive component (300). -/
def Copter.set_mode_RTL_or_land_with_pause (this : UInt64) (reason : UInt8) : PMem.M Unit :=
  Copter.set_mode_RTL_or_land_with_pause'rec 300 this reason

/-- `AP_Mission.start_command_do_aux_function'rec` with the depth of its recursive component (300). -/
def AP_Mission.start_command_do_aux_function (this : UInt64) (cmd : UInt64) : PMem.M Bool :=
  AP_Mission.start_command_do_aux_function'rec 300 this cmd

/-- `RC_Channel_Copter.do_aux_function.body'rec` with the depth of its recursive component (300). -/
def RC_Channel_Copter.do_aux_function.body (fp : UInt64) (this : UInt64) (trigger : UInt64) : PMem.M Bool :=
  RC_Channel_Copter.do_aux_function.body'rec 300 fp this trigger

/-- `RC_Channel_Copter.do_aux_function'rec` with the depth of its recursive component (300). -/
def RC_Channel_Copter.do_aux_function (this : UInt64) (trigger : UInt64) : PMem.M Bool :=
  RC_Channel_Copter.do_aux_function'rec 300 this trigger

/-- `RC_Channels.run_aux_function'rec` with the depth of its recursive component (300). -/
def RC_Channels.run_aux_function (this : UInt64) (ch_option : Int32) (pos : UInt8) (source : UInt8) (source_index : UInt16) : PMem.M Bool :=
  RC_Channels.run_aux_function'rec 300 this ch_option pos source source_index

/-- `RC_Channel_Copter.do_aux_function_change_mode'rec` with the depth of its recursive component (300). -/
def RC_Channel_Copter.do_aux_function_change_mode (this : UInt64) (mode : UInt8) (ch_flag : UInt8) : PMem.M Unit :=
  RC_Channel_Copter.do_aux_function_change_mode'rec 300 this mode ch_flag

/-- `Copter.failsafe_ekf_event.body'rec` with the depth of its recursive component (300). -/
def Copter.failsafe_ekf_event.body (fp : UInt64) (this : UInt64) : PMem.M Unit :=
  Copter.failsafe_ekf_event.body'rec 300 fp this

/-- `Copter.failsafe_ekf_event'rec` with the depth of its recursive component (300). -/
def Copter.failsafe_ekf_event (this : UInt64) : PMem.M Unit :=
  Copter.failsafe_ekf_event'rec 300 this

/-- `Copter.failsafe_terrain_on_event.body'rec` with the depth of its recursive component (300). -/
def Copter.failsafe_terrain_on_event.body (fp : UInt64) (this : UInt64) : PMem.M Unit :=
  Copter.failsafe_terrain_on_event.body'rec 300 fp this

/-- `Copter.failsafe_terrain_on_event'rec` with the depth of its recursive component (300). -/
def Copter.failsafe_terrain_on_event (this : UInt64) : PMem.M Unit :=
  Copter.failsafe_terrain_on_event'rec 300 this

/-- `ModeAuto.start_command'rec` with the depth of its recursive component (300). -/
def ModeAuto.start_command (this : UInt64) (cmd : UInt64) : PMem.M Bool :=
  ModeAuto.start_command'rec 300 this cmd

/-- `ModeAuto.exit_mission'rec` with the depth of its recursive component (300). -/
def ModeAuto.exit_mission (this : UInt64) : PMem.M Unit :=
  ModeAuto.exit_mission'rec 300 this

/-- `ModeAuto.do_takeoff'rec` with the depth of its recursive component (300). -/
def ModeAuto.do_takeoff (this : UInt64) (cmd : UInt64) : PMem.M Unit :=
  ModeAuto.do_takeoff'rec 300 this cmd

/-- `ModeAuto.do_nav_wp.body'rec` with the depth of its recursive component (300). -/
def ModeAuto.do_nav_wp.body (fp : UInt64) (this : UInt64) (cmd : UInt64) : PMem.M Unit :=
  ModeAuto.do_nav_wp.body'rec 300 fp this cmd

/-- `ModeAuto.do_nav_wp'rec` with the depth of its recursive component (300). -/
def ModeAuto.do_nav_wp (this : UInt64) (cmd : UInt64) : PMem.M Unit :=
  ModeAuto.do_nav_wp'rec 300 this cmd

/-- `ModeAuto.do_land.body'rec` with the depth of its recursive component (300). -/
def ModeAuto.do_land.body (fp : UInt64) (this : UInt64) (cmd : UInt64) : PMem.M Unit :=
  ModeAuto.do_land.body'rec 300 fp this cmd

/-- `ModeAuto.do_land'rec` with the depth of its recursive component (300). -/
def ModeAuto.do_land (this : UInt64) (cmd : UInt64) : PMem.M Unit :=
  ModeAuto.do_land'rec 300 this cmd

/-- `ModeAuto.do_loiter_unlimited.body'rec` with the depth of its recursive component (300). -/
def ModeAuto.do_loiter_unlimited.body (fp : UInt64) (this : UInt64) (cmd : UInt64) : PMem.M Bool :=
  ModeAuto.do_loiter_unlimited.body'rec 300 fp this cmd

/-- `ModeAuto.do_loiter_unlimited'rec` with the depth of its recursive component (300). -/
def ModeAuto.do_loiter_unlimited (this : UInt64) (cmd : UInt64) : PMem.M Bool :=
  ModeAuto.do_loiter_unlimited'rec 300 this cmd

/-- `ModeAuto.do_circle.body'rec` with the depth of its recursive component (300). -/
def ModeAuto.do_circle.body (fp : UInt64) (this : UInt64) (cmd : UInt64) : PMem.M Unit :=
  ModeAuto.do_circle.body'rec 300 fp this cmd

/-- `ModeAuto.do_circle'rec` with the depth of its recursive component (300). -/
def ModeAuto.do_circle (this : UInt64) (cmd : UInt64) : PMem.M Unit :=
  ModeAuto.do_circle'rec 300 this cmd

/-- `ModeAuto.do_loiter_time'rec` with the depth of its recursive component (300). -/
def ModeAuto.do_loiter_time (this : UInt64) (cmd : UInt64) : PMem.M Unit :=
  ModeAuto.do_loiter_time'rec 300 this cmd

/-- `ModeAuto.do_loiter_to_alt.body'rec` with the depth of its recursive component (300). -/
def ModeAuto.do_loiter_to_alt.body (fp : UInt64) (this : UInt64) (cmd : UInt64) : PMem.M Unit :=
  ModeAuto.do_loiter_to_alt.body'rec 300 fp this cmd

/-- `ModeAuto.do_loiter_to_alt'rec` with the depth of its recursive component (300). -/
def ModeAuto.do_loiter_to_alt (this : UInt64) (cmd : UInt64) : PMem.M Unit :=
  ModeAuto.do_loiter_to_alt'rec 300 this cmd

/-- `ModeAuto.do_RTL'rec` with the depth of its recursive component (300). -/
def ModeAuto.do_RTL (this : UInt64) : PMem.M Unit :=
  ModeAuto.do_RTL'rec 300 this

/-- `ModeAuto.do_spline_wp.body'rec` with the depth of its recursive component (300). -/
def ModeAuto.do_spline_wp.body (fp : UInt64) (this : UInt64) (cmd : UInt64) : PMem.M Unit :=
  ModeAuto.do_spline_wp.body'rec 300 fp this cmd

/-- `ModeAuto.do_spline_wp'rec` with the depth of its recursive component (300). -/
def ModeAuto.do_spline_wp (this : UInt64) (cmd : UInt64) : PMem.M Unit :=
  ModeAuto.do_spline_wp'rec 300 this cmd

/-- `ModeAuto.do_nav_guided_enable'rec` with the depth of its recursive component (300). -/
def ModeAuto.do_nav_guided_enable (this : UInt64) (cmd : UInt64) : PMem.M Unit :=
  ModeAuto.do_nav_guided_enable'rec 300 this cmd

/-- `ModeAuto.do_nav_attitude_time'rec` with the depth of its recursive component (300). -/
def ModeAuto.do_nav_attitude_time (this : UInt64) (cmd : UInt64) : PMem.M Unit :=
  ModeAuto.do_nav_attitude_time'rec 300 this cmd

/-- `ModeAuto.loiter_start.body'rec` with the depth of its recursive component (300). -/
def ModeAuto.loiter_start.body (fp : UInt64) (this : UInt64) : PMem.M Bool :=
  ModeAuto.loiter_start.body'rec 300 fp this

/-- `ModeAuto.loiter_start'rec` with the depth of its recursive component (300). -/
def ModeAuto.loiter_start (this : UInt64) : PMem.M Bool :=
  ModeAuto.loiter_start'rec 300 this

/-- `ModeAuto.takeoff_start.body'rec` with the depth of its recursive component (300). -/
def ModeAuto.takeoff_start.body (fp : UInt64) (this : UInt64) (dest_loc : UInt64) : PMem.M Unit :=
  ModeAuto.takeoff_start.body'rec 300 fp this dest_loc

/-- `ModeAuto.takeoff_start'rec` with the depth of its recursive component (300). -/
def ModeAuto.takeoff_start (this : UInt64) (dest_loc : UInt64) : PMem.M Unit :=
  ModeAuto.takeoff_start'rec 300 this dest_loc

/-- `ModeAuto.wp_start.body'rec` with the depth of its recursive component (300). -/
def ModeAuto.wp_start.body (fp : UInt64) (this : UInt64) (dest_loc : UInt64) : PMem.M Bool :=
  ModeAuto.wp_start.body'rec 300 fp this dest_loc

/-- `ModeAuto.wp_start'rec` with the depth of its recursive component (300). -/
def ModeAuto.wp_start (this : UInt64) (dest_loc : UInt64) : PMem.M Bool :=
  ModeAuto.wp_start'rec 300 this dest_loc

/-- `ModeAuto.land_start'rec` with the depth of its recursive component (300). -/
def ModeAuto.land_start (this : UInt64) : PMem.M Unit :=
  ModeAuto.land_start'rec 300 this

/-- `ModeAuto.circle_movetoedge_start.body'rec` with the depth of its recursive component (300). -/
def ModeAuto.circle_movetoedge_start.body (fp : UInt64) (this : UInt64) (circle_center : UInt64) (radius_m : Binary32) : PMem.M Unit :=
  ModeAuto.circle_movetoedge_start.body'rec 300 fp this circle_center radius_m

/-- `ModeAuto.circle_movetoedge_start'rec` with the depth of its recursive component (300). -/
def ModeAuto.circle_movetoedge_start (this : UInt64) (circle_center : UInt64) (radius_m : Binary32) : PMem.M Unit :=
  ModeAuto.circle_movetoedge_start'rec 300 this circle_center radius_m

/-- `ModeAuto.set_submode'rec` with the depth of its recursive component (300). -/
def ModeAuto.set_submode (this : UInt64) (new_submode : UInt8) : PMem.M Unit :=
  ModeAuto.set_submode'rec 300 this new_submode

/-- `ModeAuto.rtl_start'rec` with the depth of its recursive component (300). -/
def ModeAuto.rtl_start (this : UInt64) : PMem.M Unit :=
  ModeAuto.rtl_start'rec 300 this

/-- `ModeAuto.nav_guided_start'rec` with the depth of its recursive component (300). -/
def ModeAuto.nav_guided_start (this : UInt64) : PMem.M Unit :=
  ModeAuto.nav_guided_start'rec 300 this

/-- `Copter.failsafe_ekf_recheck'rec` with the depth of its recursive component (300). -/
def Copter.failsafe_ekf_recheck (this : UInt64) : PMem.M Unit :=
  Copter.failsafe_ekf_recheck'rec 300 this

/-- `fnptr'0'at'AP_Mission'_mission_complete_fn'rec` with the depth of its recursive component (300). -/
def fnptr'0'at'AP_Mission'_mission_complete_fn (f : UInt64) (a0 : UInt64) : PMem.M Unit :=
  fnptr'0'at'AP_Mission'_mission_complete_fn'rec 300 f a0

/-- `Functor'void.operator__'at'AP_Mission'_mission_complete_fn'rec` with the depth of its recursive component (300). -/
def Functor'void.operator__'at'AP_Mission'_mission_complete_fn (this : UInt64) : PMem.M Unit :=
  Functor'void.operator__'at'AP_Mission'_mission_complete_fn'rec 300 this

/-- `fnptr'3'at'AP_Mission'_cmd_start_fn'rec` with the depth of its recursive component (300). -/
def fnptr'3'at'AP_Mission'_cmd_start_fn (f : UInt64) (a0 : UInt64) (a1 : UInt64) : PMem.M Bool :=
  fnptr'3'at'AP_Mission'_cmd_start_fn'rec 300 f a0 a1

/-- `Functor'bool_const_AP_Mission_Mission_Command.operator__'at'AP_Mission'_cmd_start_fn'rec` with the depth of its recursive component (300). -/
def Functor'bool_const_AP_Mission_Mission_Command.operator__'at'AP_Mission'_cmd_start_fn (this : UInt64) (args : UInt64) : PMem.M Bool :=
  Functor'bool_const_AP_Mission_Mission_Command.operator__'at'AP_Mission'_cmd_start_fn'rec 300 this args

/-- C++ `Copter::set_mode : bool (const uint8_t, const ModeReason)`, `mode.cpp:488-498`. -/
def Copter.set_mode'2.body (fp : UInt64) (this : UInt64) (new_mode : UInt8) (reason : UInt8) : PMem.M Bool := do
  PMem.stU8 (fp + 0) new_mode
  let mut reason := reason
  let t'1 ← PMem.ldU8 (fp + 0)
  let t'2 ← Copter.set_mode (0x86d8 : UInt64) /- &copter -/ t'1 reason
  return t'2

def Copter.set_mode'2 (this : UInt64) (new_mode : UInt8) (reason : UInt8) : PMem.M Bool := do
  let fp ← PMem.enter 1
  let r ← Copter.set_mode'2.body fp this new_mode reason
  PMem.leave fp
  return r

/-- C++ `GCS_MAVLINK::_set_mode_common : MAV_RESULT (const uint8_t, const uint32_t)`, `GCS_Common.cpp:2904-2938`. -/
def GCS_MAVLINK._set_mode_common (this : UInt64) (_base_mode : UInt8) (_custom_mode : UInt32) : PMem.M UInt32 := do
  let mut _base_mode := _base_mode
  let mut _custom_mode := _custom_mode
  if (((UInt32.toInt32 (UInt8.toUInt32 (_base_mode))) &&& (UInt32.toInt32 ((1 : UInt32)))) != (0 : Int32)) then
    let t'1 ← AP.vehicle
    let t'2 ← Copter.set_mode'2 t'1 (UInt32.toUInt8 (_custom_mode)) (2 : UInt8)
    if !t'2 then
      return (4 : UInt32)
    return (0 : UInt32)
  if ((UInt32.toInt32 (UInt8.toUInt32 (_base_mode))) == (UInt32.toInt32 ((128 : UInt32)))) then
    if (_custom_mode == (Int32.toUInt32 ((0 : Int32)))) then
      let t'3 ← PMem.ldU64 ((0xba88 : UInt64) /- &hal -/ + 72)
      discard <| PMem.halDev "AP_HAL::RCOutput::force_safety_off" t'3 #[]
      return (0 : UInt32)
    if (_custom_mode == (Int32.toUInt32 ((1 : Int32)))) then
      let t'4 ← PMem.ldU64 ((0xba88 : UInt64) /- &hal -/ + 72)
      let t'5 ← PMem.halDev "AP_HAL::RCOutput::force_safety_on" t'4 #[]
      if (t'5 != 0) then
        return (0 : UInt32)
      return (4 : UInt32)
    return (2 : UInt32)
  return (2 : UInt32)

/-- C++ `GCS_MAVLINK::handle_set_mode : void (const mavlink_message_t &)`, `GCS_Common.cpp:2890-2899`. -/
def GCS_MAVLINK.handle_set_mode.body (fp : UInt64) (this : UInt64) (msg : UInt64) : PMem.M Unit := do
  __mavlink_set_mode_t.__mavlink_set_mode_t (fp + 0)
  mavlink_msg_set_mode_decode msg (fp + 0)
  let t'1 ← PMem.ldU8 ((fp + 0) + 5)
  let mut _base_mode : UInt8 := t'1
  let t'2 ← PMem.ldU32 (fp + 0)
  let mut _custom_mode : UInt32 := t'2
  let t'3 ← GCS_MAVLINK._set_mode_common this _base_mode _custom_mode
  discard <| pure (t'3)
  return ()

def GCS_MAVLINK.handle_set_mode (this : UInt64) (msg : UInt64) : PMem.M Unit := do
  let fp ← PMem.enter 6
  let r ← GCS_MAVLINK.handle_set_mode.body fp this msg
  PMem.leave fp
  return r

/-- C++ `GCS_MAVLINK::handle_mission_set_current : void (AP_Mission &, const mavlink_message_t &)`, `GCS_Common.cpp:752-777`. -/
def GCS_MAVLINK.handle_mission_set_current.body (fp : UInt64) (this : UInt64) (mission : UInt64) (msg : UInt64) : PMem.M Unit := do
  __mavlink_mission_set_current_t.__mavlink_mission_set_current_t (fp + 0)
  mavlink_msg_mission_set_current_decode msg (fp + 0)
  let t'1 ← PMem.ldU16 (fp + 0)
  let t'2 ← AP_Mission.set_current_cmd mission t'1
  if t'2 then
    let t'3 ← PMem.ldU32 (this + 40)
    let t'4 ← comm_get_txspace t'3
    let t'5 ← PMem.ldU32 (this + 40)
    let t'6 ← GCS_MAVLINK.packet_overhead_chan t'5
    let mut c'7 : Bool := default
    if (decide ((UInt16.toUInt32 (t'4)) ≥ (Int32.toUInt32 (((UInt32.toInt32 (UInt8.toUInt32 (t'6))) + (6 : Int32)))))) then
      c'7 := true
    else
      let t'8 ← PMem.ldU32 (this + 40)
      gcs_out_of_space_to_send t'8
      c'7 := false
    if c'7 then
      let t'9 ← PMem.ldU16 (fp + 0)
      GCS_MAVLINK.send_mission_current this mission t'9
    else
      GCS_MAVLINK.send_message this (11 : UInt8)
  return ()

def GCS_MAVLINK.handle_mission_set_current (this : UInt64) (mission : UInt64) (msg : UInt64) : PMem.M Unit := do
  let fp ← PMem.enter 4
  let r ← GCS_MAVLINK.handle_mission_set_current.body fp this mission msg
  PMem.leave fp
  return r

/-- C++ `GCS_MAVLINK::handle_common_mission_message : void (const mavlink_message_t &)`, `GCS_Common.cpp:4648-4705`. -/
def GCS_MAVLINK.handle_common_mission_message (this : UInt64) (msg : UInt64) : PMem.M Unit := do
  for _ in [0:1] do
    let t'1 ← PMem.ldBits msg 104 24
    let sw'2 := UInt32.toInt32 ((UInt64.toUInt32 (t'1)))
    if sw'2 == (38 : Int32) then
      GCS_MAVLINK.handle_mission_write_partial_list this msg
      break
      GCS_MAVLINK.handle_mission_item this msg
    else if sw'2 == (39 : Int32) || sw'2 == (73 : Int32) then
      GCS_MAVLINK.handle_mission_item this msg
    else if sw'2 == (51 : Int32) then
      GCS_MAVLINK.handle_mission_request_int this msg
    else if sw'2 == (40 : Int32) then
      GCS_MAVLINK.handle_mission_request this msg
    else if sw'2 == (41 : Int32) then
      let t'3 ← AP.mission
      GCS_MAVLINK.handle_mission_set_current this t'3 msg
    else if sw'2 == (43 : Int32) then
      GCS_MAVLINK.handle_mission_request_list this msg
      break
      GCS_MAVLINK.handle_mission_count this msg
      break
      GCS_MAVLINK.handle_mission_clear_all this msg
      break
    else if sw'2 == (44 : Int32) then
      GCS_MAVLINK.handle_mission_count this msg
      break
      GCS_MAVLINK.handle_mission_clear_all this msg
      break
    else if sw'2 == (45 : Int32) then
      GCS_MAVLINK.handle_mission_clear_all this msg
      break
    else if sw'2 == (47 : Int32) then
      pure ()
    else
      pure ()
  return ()

/-- C++ `GCS_MAVLINK_Copter::handle_command_int_do_reposition : MAV_RESULT (const mavlink_command_int_t &)`, `GCS_MAVLink_Copter.cpp:431-468`. -/
def GCS_MAVLINK_Copter.handle_command_int_do_reposition.body (fp : UInt64) (this : UInt64) (packet : UInt64) : PMem.M UInt32 := do
  let t'1 ← PMem.ldF32 (packet + 4)
  let mut change_modes : Bool := (((Binary32.toInt32 (t'1)) &&& (UInt32.toInt32 ((1 : UInt32)))) == (UInt32.toInt32 ((1 : UInt32))))
  let t'2 ← PMem.ldU64 ((0x86d8 : UInt64) /- &copter -/ + 9488)
  let t'3 ← vcall'Mode'in_guided_mode'11 t'2
  if ((!t'3) && (!change_modes)) then
    return (2 : UInt32)
  Location.Location (fp + 0)
  let t'4 ← GCS_MAVLINK.location_from_command_t this packet (fp + 0)
  if !t'4 then
    return (2 : UInt32)
  let t'5 ← Location.sanitize (fp + 0) ((0x86d8 : UInt64) /- &copter -/ + 11148)
  if t'5 then
    return (2 : UInt32)
  let t'6 ← ModeGuided.set_destination ((0x86d8 : UInt64) /- &copter -/ + 12520) (fp + 0) false (Int32.toBinary32 ((0 : Int32))) false (Int32.toBinary32 ((0 : Int32))) false
  if !t'6 then
    return (4 : UInt32)
  let t'7 ← PMem.ldU64 ((0x86d8 : UInt64) /- &copter -/ + 9488)
  let t'8 ← vcall'Mode'in_guided_mode'11 t'7
  if !t'8 then
    let t'9 ← Copter.set_mode (0x86d8 : UInt64) /- &copter -/ (4 : UInt8) (2 : UInt8)
    if !t'9 then
      return (4 : UInt32)
    let t'10 ← ModeGuided.set_destination ((0x86d8 : UInt64) /- &copter -/ + 12520) (fp + 0) false (Int32.toBinary32 ((0 : Int32))) false (Int32.toBinary32 ((0 : Int32))) false
    if !t'10 then
      return (4 : UInt32)
  return (0 : UInt32)

def GCS_MAVLINK_Copter.handle_command_int_do_reposition (this : UInt64) (packet : UInt64) : PMem.M UInt32 := do
  let fp ← PMem.enter 16
  let r ← GCS_MAVLINK_Copter.handle_command_int_do_reposition.body fp this packet
  PMem.leave fp
  return r

/-- C++ `AP_Mission::start_or_resume : void ()`, `AP_Mission.cpp:249-257`. -/
def AP_Mission.start_or_resume (this : UInt64) : PMem.M Unit := do
  let t'1 ← AP_ParamT'signed_char_1.operator_const_signed_char__ (this + 84)
  let t'2 ← PMem.ldI8 t'1
  let mut sc'4 := ((Int8.toInt32 (t'2)) == (1 : Int32))
  if sc'4 then
    let t'3 ← PMem.ldB (this + 85)
    sc'4 := !t'3
  if sc'4 then
    AP_Mission.start this
  else
    AP_Mission.resume this
    PMem.stB (this + 85) false
  return ()

/-- C++ `GCS_MAVLINK_Copter::handle_MAV_CMD_MISSION_START : MAV_RESULT (const mavlink_command_int_t &)`, `GCS_MAVLink_Copter.cpp:665-679`. -/
def GCS_MAVLINK_Copter.handle_MAV_CMD_MISSION_START (this : UInt64) (packet : UInt64) : PMem.M UInt32 := do
  let t'1 ← PMem.ldF32 packet
  let t'2 ← is_zero t'1
  let mut sc'5 := !t'2
  if !sc'5 then
    let t'3 ← PMem.ldF32 (packet + 4)
    let t'4 ← is_zero t'3
    sc'5 := !t'4
  if sc'5 then
    return (2 : UInt32)
  let t'6 ← Copter.set_mode (0x86d8 : UInt64) /- &copter -/ (3 : UInt8) (2 : UInt8)
  if t'6 then
    Copter.set_auto_armed (0x86d8 : UInt64) /- &copter -/ true
    let t'7 ← AP_Mission.state (((0x86d8 : UInt64) /- &copter -/ + 11368) + 112)
    if ((UInt32.toInt32 (t'7)) != (UInt32.toInt32 ((1 : UInt32)))) then
      AP_Mission.start_or_resume (((0x86d8 : UInt64) /- &copter -/ + 11368) + 112)
    return (0 : UInt32)
  return (4 : UInt32)

/-- C++ `ModeAuto::return_path_start_auto_RTL : bool (ModeReason)`, `mode_auto.cpp:282-295`. -/
def ModeAuto.return_path_start_auto_RTL.body (fp : UInt64) (this : UInt64) (reason : UInt8) : PMem.M Bool := do
  let mut reason := reason
  Mode.get_stopping_point this (fp + 0)
  let t'1 := (fp + 0)
  let t'2 ← AP_Mission.jump_to_closest_mission_leg (this + 112) t'1
  if !t'2 then
    let t'3 ← PMem.ldB (((0x86d8 : UInt64) /- &copter -/ + 9448) + 13)
    if t'3 then
      let t'4 := Int32.toUInt32 ((1 : Int32))
      PMem.stBits (0xce38 : UInt64) /- &AP_Notify::events -/ 2 1 (UInt32.toUInt64 (t'4))
    let t'5 ← Mode.gcs this
    GCS.send_text t'5 (4 : UInt32) (0x149ca : UInt64) /- "Mode change to AUTO RTL failed: No return path found" -/ (fp + 16)
    return false
  let t'6 ← ModeAuto.enter_auto_rtl this reason
  return t'6

def ModeAuto.return_path_start_auto_RTL (this : UInt64) (reason : UInt8) : PMem.M Bool := do
  let fp ← PMem.enter 24
  let r ← ModeAuto.return_path_start_auto_RTL.body fp this reason
  PMem.leave fp
  return r

/-- C++ `ModeAuto::jump_to_landing_sequence_auto_RTL : bool (ModeReason)`, `mode_auto.cpp:266-279`. -/
def ModeAuto.jump_to_landing_sequence_auto_RTL.body (fp : UInt64) (this : UInt64) (reason : UInt8) : PMem.M Bool := do
  let mut reason := reason
  Mode.get_stopping_point this (fp + 0)
  let t'1 := (fp + 0)
  let t'2 ← AP_Mission.jump_to_landing_sequence (this + 112) t'1
  if !t'2 then
    let t'3 ← PMem.ldB (((0x86d8 : UInt64) /- &copter -/ + 9448) + 13)
    if t'3 then
      let t'4 := Int32.toUInt32 ((1 : Int32))
      PMem.stBits (0xce38 : UInt64) /- &AP_Notify::events -/ 2 1 (UInt32.toUInt64 (t'4))
    let t'5 ← Mode.gcs this
    GCS.send_text t'5 (4 : UInt32) (0x14990 : UInt64) /- "Mode change to AUTO RTL failed: No landing sequence found" -/ (fp + 16)
    return false
  let t'6 ← ModeAuto.enter_auto_rtl this reason
  return t'6

def ModeAuto.jump_to_landing_sequence_auto_RTL (this : UInt64) (reason : UInt8) : PMem.M Bool := do
  let fp ← PMem.enter 24
  let r ← ModeAuto.jump_to_landing_sequence_auto_RTL.body fp this reason
  PMem.leave fp
  return r

/-- C++ `GCS_MAVLINK::handle_command_do_set_mission_current : MAV_RESULT (const mavlink_command_int_t &)`, `GCS_Common.cpp:4947-4990`. -/
def GCS_MAVLINK.handle_command_do_set_mission_current (this : UInt64) (packet : UInt64) : PMem.M UInt32 := do
  let t'1 ← AP.mission
  let mission : UInt64 := t'1
  let t'2 ← PMem.ldF32 packet
  let t'3 ← is_equal'float_float t'2 (-(Binary32.ofBits 0x3f800000 /- 1 -/))
  let mut sc'5 := t'3
  if !sc'5 then
    let t'4 ← PMem.ldF32 packet
    sc'5 := (decide (t'4 ≥ (Int32.toBinary32 ((0 : Int32)))))
  if sc'5 then
    pure ()
  else
    return (2 : UInt32)
  let t'6 ← PMem.ldF32 packet
  if (decide (t'6 ≥ (Int32.toBinary32 ((0 : Int32))))) then
    let t'7 ← PMem.ldF32 packet
    let mut seq : UInt32 := Binary32.toUInt32 (t'7)
    let mut sc'9 := (decide (seq > (Int32.toUInt32 ((32767 : Int32)))))
    if !sc'9 then
      let t'8 ← AP_Mission.is_valid_index mission (UInt32.toUInt16 (seq))
      sc'9 := !t'8
    if sc'9 then
      return (4 : UInt32)
  let t'10 ← PMem.ldF32 (packet + 4)
  let t'11 ← is_equal'float_float t'10 (Binary32.ofBits 0x3f800000 /- 1 -/)
  let mut reset_and_restart : Bool := t'11
  if reset_and_restart then
    AP_Mission.reset_jump_counters mission
  let t'12 ← PMem.ldF32 packet
  if (decide (t'12 ≥ (Int32.toBinary32 ((0 : Int32))))) then
    let t'13 ← PMem.ldF32 packet
    let mut seq'2 : UInt32 := Binary32.toUInt32 (t'13)
    let t'14 ← AP_Mission.set_current_cmd mission (UInt32.toUInt16 (seq'2))
    if !t'14 then
      return (4 : UInt32)
  let mut sc'16 := reset_and_restart
  if sc'16 then
    let t'15 ← PMem.ldF32 packet
    sc'16 := (decide (t'15 ≥ (Int32.toBinary32 ((0 : Int32)))))
  if sc'16 then
    AP_Mission.resume mission
  GCS_MAVLINK.send_message this (11 : UInt8)
  return (0 : UInt32)

/-- C++ `GCS_MAVLINK::handle_command_do_set_mode : MAV_RESULT (const mavlink_command_int_t &)`, `GCS_Common.cpp:5034-5040`. -/
def GCS_MAVLINK.handle_command_do_set_mode (this : UInt64) (packet : UInt64) : PMem.M UInt32 := do
  let t'1 ← PMem.ldF32 packet
  let mut _base_mode : UInt8 := Binary32.toUInt8 (t'1)
  let t'2 ← PMem.ldF32 (packet + 4)
  let mut _custom_mode : UInt32 := Binary32.toUInt32 (t'2)
  let t'3 ← GCS_MAVLINK._set_mode_common this _base_mode _custom_mode
  return t'3

/-- C++ `GCS_MAVLINK::handle_command_component_arm_disarm : MAV_RESULT (const mavlink_command_int_t &)`, `GCS_Common.cpp:5182-5208`. -/
def GCS_MAVLINK.handle_command_component_arm_disarm (this : UInt64) (packet : UInt64) : PMem.M UInt32 := do
  let t'1 ← PMem.ldF32 packet
  let t'2 ← is_equal'float_float t'1 (Binary32.ofBits 0x3f800000 /- 1 -/)
  if t'2 then
    let t'3 ← AP.arming
    let t'4 ← AP_Arming.is_armed t'3
    if t'4 then
      return (0 : UInt32)
    let t'5 ← PMem.ldF32 (packet + 4)
    let t'6 ← is_equal'float_float t'5 (Binary32.ofBits 0x453ad000 /- 2989 -/)
    let mut sc'9 := !t'6
    if sc'9 then
      let t'7 ← PMem.ldF32 (packet + 4)
      let t'8 ← is_equal'float_float t'7 (Binary32.ofBits 0x46a59800 /- 21196 -/)
      sc'9 := !t'8
    let mut do_arming_checks : Bool := sc'9
    let t'10 ← AP.arming
    let t'11 ← AP_Arming_Copter.arm t'10 (1 : Int32) do_arming_checks
    if t'11 then
      return (0 : UInt32)
    return (4 : UInt32)
  let t'12 ← PMem.ldF32 packet
  let t'13 ← is_zero t'12
  if t'13 then
    let t'14 ← AP.arming
    let t'15 ← AP_Arming.is_armed t'14
    if !t'15 then
      return (0 : UInt32)
    let t'16 ← PMem.ldF32 (packet + 4)
    let t'17 ← is_equal'float_float t'16 (Binary32.ofBits 0x46a59800 /- 21196 -/)
    let mut forced : Bool := t'17
    let t'18 ← AP.arming
    let t'19 ← AP_Arming_Copter.disarm t'18 (1 : Int32) (!forced)
    if t'19 then
      return (0 : UInt32)
    return (4 : UInt32)
  return (3 : UInt32)

/-- C++ `GCS_MAVLINK::handle_command_int_packet : MAV_RESULT (const mavlink_command_int_t &, const mavlink_message_t &)`, `GCS_Common.cpp:5654-5888`. -/
def GCS_MAVLINK.handle_command_int_packet.body (fp : UInt64) (this : UInt64) (packet : UInt64) (msg : UInt64) : PMem.M UInt32 := do
  let t'1 ← PMem.ldU16 (packet + 28)
  let sw'2 := UInt32.toInt32 (UInt16.toUInt32 (t'1))
  if sw'2 == (42651 : Int32) then
    PMem.unreached "GCS_MAVLINK::handle_command_battery_reset"
    return (default : UInt32)
  else if sw'2 == (32000 : Int32) then
    PMem.unreached "GCS_MAVLINK::handle_can_forward"
    return (default : UInt32)
  else if sw'2 == (42700 : Int32) then
    PMem.unreached "GCS_MAVLINK::handle_command_debug_trap"
    return (default : UInt32)
  else if sw'2 == (611 : Int32) then
    PMem.unreached "GCS_MAVLINK::handle_command_do_set_global_origin"
    return (default : UInt32)
  else if sw'2 == (218 : Int32) then
    PMem.unreached "GCS_MAVLINK::handle_command_do_aux_function"
    return (default : UInt32)
  else if sw'2 == (185 : Int32) then
    PMem.unreached "GCS_MAVLINK::handle_flight_termination"
    return (default : UInt32)
  else if sw'2 == (601 : Int32) then
    PMem.unreached "GCS_MAVLINK::handle_command_do_jump_tag"
    return (default : UInt32)
  else if sw'2 == (224 : Int32) then
    let t'3 ← GCS_MAVLINK.handle_command_do_set_mission_current this packet
    return t'3
  else if sw'2 == (176 : Int32) then
    let t'4 ← GCS_MAVLINK.handle_command_do_set_mode this packet
    return t'4
  else if sw'2 == (197 : Int32) || sw'2 == (195 : Int32) then
    let t'5 ← GCS_MAVLINK.handle_command_do_set_roi_location this packet
    return t'5
  else if sw'2 == (201 : Int32) then
    let t'6 ← GCS_MAVLINK.handle_command_do_set_roi this packet
    return t'6
  else if sw'2 == (42428 : Int32) then
    GCS_MAVLINK_Copter.send_banner this
    return (0 : UInt32)
  else if sw'2 == (179 : Int32) then
    PMem.unreached "GCS_MAVLINK::handle_command_do_set_home"
    return (default : UInt32)
  else if sw'2 == (43003 : Int32) then
    PMem.unreached "GCS_MAVLINK::handle_command_int_external_position_estimate"
    return (default : UInt32)
  else if sw'2 == (43004 : Int32) then
    PMem.unreached "GCS_MAVLINK::handle_command_int_external_wind_estimate"
    return (default : UInt32)
  else if sw'2 == (400 : Int32) then
    let t'7 ← GCS_MAVLINK.handle_command_component_arm_disarm this packet
    return t'7
  else if sw'2 == (410 : Int32) then
    let t'8 ← GCS_MAVLINK.handle_command_get_home_position this packet
    return t'8
  else if sw'2 == (241 : Int32) then
    PMem.unreached "GCS_MAVLINK::handle_command_preflight_calibration"
    return (default : UInt32)
  else if sw'2 == (245 : Int32) then
    let t'9 ← PMem.ldF32 packet
    let mut sc'11 := ((UInt32.toInt32 (UInt8.toUInt32 ((Binary32.toUInt8 (t'9))))) == (UInt32.toInt32 ((2 : UInt32))))
    if !sc'11 then
      let t'10 ← PMem.ldF32 packet
      sc'11 := ((UInt32.toInt32 (UInt8.toUInt32 ((Binary32.toUInt8 (t'10))))) == (UInt32.toInt32 ((4 : UInt32))))
    if sc'11 then
      PMem.unreached "AP_Param::erase_all"
      GCS_MAVLINK.send_text this (4 : UInt32) (0x18b4d : UInt64) /- "All parameters reset, reboot board" -/ (fp + 0)
      return (0 : UInt32)
    return (2 : UInt32)
  else if sw'2 == (246 : Int32) then
    PMem.unreached "GCS_MAVLINK::handle_preflight_reboot"
    return (default : UInt32)
  else if sw'2 == (5300 : Int32) then
    PMem.unreached "GCS_MAVLINK::handle_do_set_safety_switch_state"
    return (default : UInt32)
  else if sw'2 == (520 : Int32) then
    let t'12 ← GCS_MAVLINK.handle_command_request_autopilot_capabilities this packet
    return t'12
  else if sw'2 == (401 : Int32) then
    let t'13 ← GCS_MAVLINK.handle_command_run_prearm_checks this packet
    return t'13
  else if sw'2 == (42007 : Int32) then
    PMem.unreached "GCS_MAVLINK::handle_command_set_ekf_source_set"
    return (default : UInt32)
  else if sw'2 == (526 : Int32) then
    PMem.unreached "GCS_MAVLINK::handle_command_storage_format"
    return (default : UInt32)
  else if sw'2 == (511 : Int32) then
    let t'14 ← GCS_MAVLINK.handle_command_set_message_interval this packet
    return t'14
  else if sw'2 == (510 : Int32) then
    PMem.unreached "GCS_MAVLINK::handle_command_get_message_interval"
    return (default : UInt32)
  else if sw'2 == (512 : Int32) then
    let t'15 ← GCS_MAVLINK.handle_command_request_message this packet
    return t'15
  else
    pure ()
  return (3 : UInt32)

def GCS_MAVLINK.handle_command_int_packet (this : UInt64) (packet : UInt64) (msg : UInt64) : PMem.M UInt32 := do
  let fp ← PMem.enter 8
  let r ← GCS_MAVLINK.handle_command_int_packet.body fp this packet msg
  PMem.leave fp
  return r

/-- C++ `RC_Channel::init_aux_function : void (const AUX_FUNC, const AuxSwitchPos)`, `RC_Channel.cpp:679-854`. -/
def RC_Channel.init_aux_function.body (fp : UInt64) (this : UInt64) (ch_option : Int32) (ch_flag : UInt8) : PMem.M Unit := do
  let mut ch_option := ch_option
  let mut ch_flag := ch_flag
  let sw'1 := ch_option
  if sw'1 == (153 : Int32) || sw'1 == (154 : Int32) || sw'1 == (172 : Int32) || sw'1 == (58 : Int32) || sw'1 == (62 : Int32) || sw'1 == (81 : Int32) || sw'1 == (0 : Int32) || sw'1 == (30 : Int32) || sw'1 == (103 : Int32) || sw'1 == (104 : Int32) || sw'1 == (187 : Int32) || sw'1 == (90 : Int32) || sw'1 == (161 : Int32) then
    pure ()
  else if sw'1 == (40 : Int32) || sw'1 == (65 : Int32) || sw'1 == (105 : Int32) || sw'1 == (24 : Int32) || sw'1 == (31 : Int32) || sw'1 == (46 : Int32) || sw'1 == (162 : Int32) || sw'1 == (165 : Int32) || sw'1 == (112 : Int32) then
    let t'2 ← PMem.ldU8 (this + 10)
    let t'3 ← RC_Channel.run_aux_function this ch_option ch_flag (0 : UInt8) (UInt8.toUInt16 (t'2))
    discard <| pure (t'3)
  else
    let t'4 ← PMem.ldU8 (this + 10)
    PMem.stU64 (fp + 0) (UInt32.toUInt64 ((Int32.toUInt32 (((UInt32.toInt32 (UInt8.toUInt32 (t'4))) + (1 : Int32))))))
    PMem.stU64 (fp + 8) (UInt32.toUInt64 ((Int32.toUInt32 (ch_option))))
    let t'5 ← gcs
    GCS.send_text t'5 (4 : UInt32) (0x18d17 : UInt64) /- "Failed to init: RC%u_OPTION: %u" -/ (fp + 0)
  return ()

def RC_Channel.init_aux_function (this : UInt64) (ch_option : Int32) (ch_flag : UInt8) : PMem.M Unit := do
  let fp ← PMem.enter 16
  let r ← RC_Channel.init_aux_function.body fp this ch_option ch_flag
  PMem.leave fp
  return r

/-- C++ `RC_Channel_Copter::init_aux_function : void (const AUX_FUNC, const AuxSwitchPos)`, `RC_Channel_Copter.cpp:72-159`. -/
def RC_Channel_Copter.init_aux_function (this : UInt64) (ch_option : Int32) (ch_flag : UInt8) : PMem.M Unit := do
  let mut ch_option := ch_option
  let mut ch_flag := ch_flag
  let sw'1 := ch_option
  if sw'1 == (70 : Int32) || sw'1 == (16 : Int32) || sw'1 == (17 : Int32) || sw'1 == (180 : Int32) || sw'1 == (33 : Int32) || sw'1 == (72 : Int32) || sw'1 == (73 : Int32) || sw'1 == (2 : Int32) || sw'1 == (71 : Int32) || sw'1 == (57 : Int32) || sw'1 == (55 : Int32) || sw'1 == (18 : Int32) || sw'1 == (56 : Int32) || sw'1 == (69 : Int32) || sw'1 == (12 : Int32) || sw'1 == (4 : Int32) || sw'1 == (5 : Int32) || sw'1 == (7 : Int32) || sw'1 == (42 : Int32) || sw'1 == (68 : Int32) || sw'1 == (37 : Int32) || sw'1 == (47 : Int32) || sw'1 == (48 : Int32) || sw'1 == (49 : Int32) || sw'1 == (60 : Int32) || sw'1 == (83 : Int32) || sw'1 == (61 : Int32) || sw'1 == (52 : Int32) || sw'1 == (99 : Int32) || sw'1 == (151 : Int32) || sw'1 == (152 : Int32) || sw'1 == (154 : Int32) || sw'1 == (161 : Int32) || sw'1 == (178 : Int32) then
    pure ()
  else if sw'1 == (14 : Int32) || sw'1 == (26 : Int32) || sw'1 == (25 : Int32) || sw'1 == (43 : Int32) || sw'1 == (32 : Int32) || sw'1 == (39 : Int32) || sw'1 == (3 : Int32) || sw'1 == (76 : Int32) || sw'1 == (13 : Int32) || sw'1 == (75 : Int32) || sw'1 == (84 : Int32) || sw'1 == (159 : Int32) || sw'1 == (109 : Int32) || sw'1 == (160 : Int32) then
    RC_Channel.init_aux_function this ch_option ch_flag
  else
    RC_Channel.init_aux_function this ch_option ch_flag
  return ()

/-- C++ `RC_Channels::rudder_arm_disarm_check : void ()`, `RC_Channels.cpp:456-516`. -/
def RC_Channels.rudder_arm_disarm_check (this : UInt64) : PMem.M Unit := do
  let t'1 ← AP.arming
  let t'2 ← AP_Arming.get_rudder_arming_type t'1
  if (t'2 == (0 : Int32)) then
    return ()
  let t'3 ← RC_Channels_Copter.get_arming_channel this
  let mut channel : UInt64 := t'3
  if (channel == (0 : UInt64)) then
    return ()
  let t'4 ← RC_Channel.get_control_in channel
  let mut control_in : Int16 := t'4
  let t'5 ← PMem.iabs (Int16.toInt32 (control_in))
  let mut abs_control_in : Int32 := t'5
  if (abs_control_in == (0 : Int32)) then
    PMem.stB (this + 44) true
  if (decide (abs_control_in ≤ (4000 : Int32))) then
    let t'6 := Int32.toUInt32 ((0 : Int32))
    PMem.stU32 (this + 40) t'6
    return ()
  let t'7 ← RC_Channels_Copter.arming_check_throttle this
  if (t'7 && (decide ((Int16.toInt32 (control_in)) > (4000 : Int32)))) then
    let t'8 ← rc
    let t'9 ← RC_Channels.get_throttle_channel t'8
    let c : UInt64 := t'9
    let t'10 ← RC_Channel.get_control_in c
    if ((Int16.toInt32 (t'10)) != (0 : Int32)) then
      let t'11 := Int32.toUInt32 ((0 : Int32))
      PMem.stU32 (this + 40) t'11
      return ()
  let mut now : UInt32 := ((← PMem.clock) / 1000).toUInt32
  let t'12 ← PMem.ldU32 (this + 40)
  if (t'12 == (Int32.toUInt32 ((0 : Int32)))) then
    PMem.stU32 (this + 40) now
    return ()
  let t'13 ← PMem.ldU32 (this + 40)
  if (decide ((now - t'13) < (Int32.toUInt32 ((3000 : Int32))))) then
    return ()
  let t'14 := Int32.toUInt32 ((0 : Int32))
  PMem.stU32 (this + 40) t'14
  if (decide ((Int16.toInt32 (control_in)) > (4000 : Int32))) then
    let t'15 ← AP.arming
    let t'16 ← AP_Arming_Copter.arm t'15 (0 : Int32) true
    discard <| pure (t'16)
    PMem.stB (this + 44) false
  else
    let t'17 ← AP.arming
    let t'18 ← AP_Arming.get_rudder_arming_type t'17
    if (t'18 == (2 : Int32)) then
      let t'19 ← AP.arming
      let t'20 ← AP_Arming_Copter.disarm t'19 (0 : Int32) true
      discard <| pure (t'20)
  return ()

/-- C++ `RC_Channels::read_input : bool ()`, `RC_Channels.cpp:89-120`. -/
def RC_Channels.read_input.body (fp : UInt64) (this : UInt64) : PMem.M Bool := do
  let t'1 ← PMem.ldU64 ((0xba88 : UInt64) /- &hal -/ + 64)
  let t'2 ← PMem.halDev "AP_HAL::RCInput::new_input" t'1 #[]
  let mut sc'5 := (t'2 != 0)
  if sc'5 then
    let t'3 ← rc
    let t'4 ← RC_Channels.option_is_enabled t'3 (1 : Int32)
    sc'5 := !t'4
  if sc'5 then
    PMem.stB (this + 13) true
  else
    let t'6 ← PMem.ldB (this + 12)
    if !t'6 then
      return false
  PMem.stB (this + 36) true
  PMem.stB (this + 12) false
  let t'7 := ((← PMem.clock) / 1000).toUInt32
  PMem.stU32 (this + 8) t'7
  let mut success : Bool := false
  for i'8 in [0:16] do
    let i : UInt8 := UInt8.ofNat i'8
    let t'9 ← RC_Channels_Copter.channel this i
    let t'10 ← RC_Channel.update t'9
    let t'11 := (success || ((if t'10 then (1 : Int32) else (0 : Int32)) != (0 : Int32)))
    success := t'11
  if success then
    RC_Channels.rudder_arm_disarm_check this
    let t'12 ← RC_Channels.should_ignore_overrides this
    if t'12 then
      RC_Channels.set_gcs_overrides_enabled this false
      let t'13 ← gcs
      GCS.send_text t'13 (5 : UInt32) (0x18cd3 : UInt64) /- "RC overrides cleared by pilot input" -/ (fp + 0)
  return success

def RC_Channels.read_input (this : UInt64) : PMem.M Bool := do
  let fp ← PMem.enter 8
  let r ← RC_Channels.read_input.body fp this
  PMem.leave fp
  return r

/-- C++ `Copter::set_mode_SmartRTL_or_RTL : void (ModeReason)`, `events.cpp:419-431`. -/
def Copter.set_mode_SmartRTL_or_RTL.body (fp : UInt64) (this : UInt64) (reason : UInt8) : PMem.M Unit := do
  let mut reason := reason
  let t'1 ← Copter.gcs this
  GCS.send_text t'1 (4 : UInt32) (0x1482d : UInt64) /- "SmartRTL Unavailable, Trying RTL Mode" -/ (fp + 0)
  Copter.set_mode_RTL_or_land_with_pause this reason
  return ()

def Copter.set_mode_SmartRTL_or_RTL (this : UInt64) (reason : UInt8) : PMem.M Unit := do
  let fp ← PMem.enter 8
  let r ← Copter.set_mode_SmartRTL_or_RTL.body fp this reason
  PMem.leave fp
  return r

/-- C++ `Copter::set_mode_SmartRTL_or_land_with_pause : void (ModeReason)`, `events.cpp:404-415`. -/
def Copter.set_mode_SmartRTL_or_land_with_pause.body (fp : UInt64) (this : UInt64) (reason : UInt8) : PMem.M Unit := do
  let mut reason := reason
  let t'1 ← Copter.gcs this
  GCS.send_text t'1 (4 : UInt32) (0x14807 : UInt64) /- "SmartRTL Unavailable, Using Land Mode" -/ (fp + 0)
  Copter.set_mode_land_with_pause this reason
  return ()

def Copter.set_mode_SmartRTL_or_land_with_pause (this : UInt64) (reason : UInt8) : PMem.M Unit := do
  let fp ← PMem.enter 8
  let r ← Copter.set_mode_SmartRTL_or_land_with_pause.body fp this reason
  PMem.leave fp
  return r

/-- C++ `Copter::set_mode_auto_do_land_start_or_RTL : void (ModeReason)`, `events.cpp:435-446`. -/
def Copter.set_mode_auto_do_land_start_or_RTL.body (fp : UInt64) (this : UInt64) (reason : UInt8) : PMem.M Unit := do
  let mut reason := reason
  let t'1 ← Copter.set_mode this (27 : UInt8) reason
  if t'1 then
    let t'2 := Int32.toUInt32 ((1 : Int32))
    PMem.stBits (0xce38 : UInt64) /- &AP_Notify::events -/ 3 1 (UInt32.toUInt64 (t'2))
    return ()
  let t'3 ← Copter.gcs this
  GCS.send_text t'3 (4 : UInt32) (0x14853 : UInt64) /- "Trying RTL Mode" -/ (fp + 0)
  Copter.set_mode_RTL_or_land_with_pause this reason
  return ()

def Copter.set_mode_auto_do_land_start_or_RTL (this : UInt64) (reason : UInt8) : PMem.M Unit := do
  let fp ← PMem.enter 8
  let r ← Copter.set_mode_auto_do_land_start_or_RTL.body fp this reason
  PMem.leave fp
  return r

/-- C++ `Copter::set_mode_brake_or_land_with_pause : void (ModeReason)`, `events.cpp:450-461`. -/
def Copter.set_mode_brake_or_land_with_pause.body (fp : UInt64) (this : UInt64) (reason : UInt8) : PMem.M Unit := do
  let mut reason := reason
  let t'1 ← Copter.set_mode this (17 : UInt8) reason
  if t'1 then
    let t'2 := Int32.toUInt32 ((1 : Int32))
    PMem.stBits (0xce38 : UInt64) /- &AP_Notify::events -/ 3 1 (UInt32.toUInt64 (t'2))
    return ()
  let t'3 ← Copter.gcs this
  GCS.send_text t'3 (4 : UInt32) (0x14863 : UInt64) /- "Trying Land Mode" -/ (fp + 0)
  Copter.set_mode_land_with_pause this reason
  return ()

def Copter.set_mode_brake_or_land_with_pause (this : UInt64) (reason : UInt8) : PMem.M Unit := do
  let fp ← PMem.enter 8
  let r ← Copter.set_mode_brake_or_land_with_pause.body fp this reason
  PMem.leave fp
  return r

/-- C++ `Copter::do_failsafe_action : void (FailsafeAction, ModeReason)`, `events.cpp:485-524`. -/
def Copter.do_failsafe_action (this : UInt64) (action : UInt8) (reason : UInt8) : PMem.M Unit := do
  let mut action := action
  let mut reason := reason
  for _ in [0:1] do
    let sw'1 := action
    if sw'1 == (0 : UInt8) then
      return ()
    else if sw'1 == (1 : UInt8) then
      Copter.set_mode_land_with_pause this reason
    else if sw'1 == (2 : UInt8) then
      Copter.set_mode_RTL_or_land_with_pause this reason
    else if sw'1 == (3 : UInt8) then
      Copter.set_mode_SmartRTL_or_RTL this reason
    else if sw'1 == (4 : UInt8) then
      Copter.set_mode_SmartRTL_or_land_with_pause this reason
    else if sw'1 == (5 : UInt8) then
      let t'2 ← AP_Arming_Copter.disarm (this + 8768) (20 : Int32) true
      discard <| pure (t'2)
      break
      Copter.set_mode_auto_do_land_start_or_RTL this reason
    else if sw'1 == (6 : UInt8) then
      Copter.set_mode_auto_do_land_start_or_RTL this reason
    else if sw'1 == (7 : UInt8) then
      Copter.set_mode_brake_or_land_with_pause this reason
    else
      pure ()
  return ()

/-- C++ `Copter::failsafe_radio_on_event : void ()`, `events.cpp:13-79`. -/
def Copter.failsafe_radio_on_event (this : UInt64) : PMem.M Unit := do
  let mut desired_action : UInt8 := default  -- uninitialized in C
  let t'1 ← AP_Enum'Parameters_FS_THR_Action.operator_const_Parameters.FS_THR_Action ((this + 6776) + 26)
  let sw'2 := t'1
  if sw'2 == (0 : Int32) then
    desired_action := (0 : UInt8)
  else if sw'2 == (1 : Int32) || sw'2 == (2 : Int32) then
    desired_action := (2 : UInt8)
  else if sw'2 == (4 : Int32) then
    desired_action := (3 : UInt8)
  else if sw'2 == (5 : Int32) then
    desired_action := (4 : UInt8)
  else if sw'2 == (3 : Int32) then
    desired_action := (1 : UInt8)
  else if sw'2 == (6 : Int32) then
    desired_action := (6 : UInt8)
  else if sw'2 == (7 : Int32) then
    desired_action := (7 : UInt8)
  else
    desired_action := (1 : UInt8)
  let t'3 ← Copter.should_disarm_on_failsafe this
  if t'3 then
    Copter.announce_failsafe this (0x1467d : UInt64) /- "Radio" -/ (0x14683 : UInt64) /- "Disarming" -/
    let t'4 ← AP_Arming_Copter.disarm (this + 8768) (16 : Int32) true
    discard <| pure (t'4)
    desired_action := (0 : UInt8)
  else
    let t'5 ← PMem.ldU64 (this + 9488)
    let t'6 ← vcall'Mode'is_landing'15 t'5
    let mut sc'10 := t'6
    if sc'10 then
      let t'7 ← AP_BattMonitor.has_failsafed (this + 9584)
      let mut sc'9 := t'7
      if sc'9 then
        let t'8 ← AP_BattMonitor.get_highest_failsafe_priority (this + 9584)
        sc'9 := (decide ((Int8.toInt32 (t'8)) ≤ (1 : Int32)))
      sc'10 := sc'9
    if sc'10 then
      Copter.announce_failsafe this (0x1468d : UInt64) /- "Radio + Battery" -/ (0x1469d : UInt64) /- "Continuing Landing" -/
      desired_action := (1 : UInt8)
    else
      let t'11 ← PMem.ldU64 (this + 9488)
      let t'12 ← vcall'Mode'is_landing'15 t'11
      let mut sc'14 := t'12
      if sc'14 then
        let t'13 ← Copter.failsafe_option this (8 : Int32)
        sc'14 := t'13
      if sc'14 then
        Copter.announce_failsafe this (0x1467d : UInt64) /- "Radio" -/ (0x1469d : UInt64) /- "Continuing Landing" -/
        desired_action := (1 : UInt8)
      else
        let t'15 ← PMem.ldU64 (this + 9488)
        let t'16 ← vcall'Mode'mode_number'1 t'15
        let mut sc'18 := (t'16 == (3 : UInt8))
        if sc'18 then
          let t'17 ← Copter.failsafe_option this (1 : Int32)
          sc'18 := t'17
        if sc'18 then
          Copter.announce_failsafe this (0x1467d : UInt64) /- "Radio" -/ (0x146b0 : UInt64) /- "Continuing Auto" -/
          desired_action := (0 : UInt8)
        else
          let t'19 ← PMem.ldU64 (this + 9488)
          let t'20 ← vcall'Mode'in_guided_mode'11 t'19
          let mut sc'22 := t'20
          if sc'22 then
            let t'21 ← Copter.failsafe_option this (4 : Int32)
            sc'22 := t'21
          if sc'22 then
            Copter.announce_failsafe this (0x1467d : UInt64) /- "Radio" -/ (0x146c0 : UInt64) /- "Continuing Guided Mode" -/
            desired_action := (0 : UInt8)
          else
            Copter.announce_failsafe this (0x1467d : UInt64) /- "Radio" -/ (0 : UInt64)
  Copter.do_failsafe_action this desired_action (3 : UInt8)
  return ()

/-- C++ `Copter::set_failsafe_radio : void (bool)`, `AP_State.cpp:46-69`. -/
def Copter.set_failsafe_radio (this : UInt64) (b : Bool) : PMem.M Unit := do
  let mut b := b
  let t'1 ← PMem.ldBits (this + 9508) 72 1
  if ((UInt32.toInt32 (UInt8.toUInt32 ((UInt64.toUInt8 (t'1))))) != (if b then (1 : Int32) else (0 : Int32))) then
    let t'2 := if b then (1 : UInt8) else (0 : UInt8)
    PMem.stBits (this + 9508) 72 1 (UInt8.toUInt64 (t'2))
    let t'3 ← PMem.ldBits (this + 9508) 72 1
    if ((UInt32.toInt32 (UInt8.toUInt32 ((UInt64.toUInt8 (t'3))))) == (if false then (1 : Int32) else (0 : Int32))) then
      Copter.failsafe_radio_off_event this
    else
      Copter.failsafe_radio_on_event this
    PMem.stB ((0xccc0 : UInt64) /- &AP_Notify::flags -/ + 10) b
  return ()

/-- C++ `Copter::set_throttle_and_failsafe : void (uint16_t)`, `radio.cpp:136-172`. -/
def Copter.set_throttle_and_failsafe (this : UInt64) (throttle_pwm : UInt16) : PMem.M Unit := do
  let mut throttle_pwm := throttle_pwm
  let t'1 ← AP_Enum'Parameters_FS_THR_Action.operator_const_Parameters.FS_THR_Action ((this + 6776) + 26)
  if (t'1 == (0 : Int32)) then
    Copter.set_failsafe_radio this false
    return ()
  let t'2 ← AP_ParamT'unsigned_short_2.operator_const_unsigned_short__ ((this + 6776) + 28)
  let t'3 ← PMem.ldU16 t'2
  if (decide ((UInt32.toInt32 (UInt16.toUInt32 (throttle_pwm))) ≤ (UInt32.toInt32 (UInt16.toUInt32 (t'3))))) then
    let t'4 ← PMem.ldBits (this + 9508) 72 1
    let mut sc'10 := (UInt64.toUInt8 (t'4)) != (0 : UInt8)
    if !sc'10 then
      let t'5 ← rc
      let t'6 ← RC_Channels.has_ever_seen_rc_input t'5
      let mut sc'9 := t'6
      if !sc'9 then
        let t'7 ← PMem.ldU64 (this + 9528)
        let t'8 ← AP_Motors.armed t'7
        sc'9 := t'8
      sc'10 := !sc'9
    if sc'10 then
      return ()
    let t'11 := ((this + 9508) + 8)
    let t'12 ← PMem.ldI8 t'11
    let t'13 := (t'12 + 1)
    PMem.stI8 t'11 t'13
    let t'14 ← PMem.ldI8 ((this + 9508) + 8)
    if (decide ((Int8.toInt32 (t'14)) ≥ (3 : Int32))) then
      let t'15 := Int32.toInt8 ((3 : Int32))
      PMem.stI8 ((this + 9508) + 8) t'15
      Copter.set_failsafe_radio this true
  else
    let t'16 := ((this + 9508) + 8)
    let t'17 ← PMem.ldI8 t'16
    let t'18 := (t'17 - 1)
    PMem.stI8 t'16 t'18
    let t'19 ← PMem.ldI8 ((this + 9508) + 8)
    if (decide ((Int8.toInt32 (t'19)) ≤ (0 : Int32))) then
      let t'20 := Int32.toInt8 ((0 : Int32))
      PMem.stI8 ((this + 9508) + 8) t'20
      let t'21 ← PMem.ldBits (this + 9508) 72 1
      if (UInt64.toUInt8 (t'21)) != (0 : UInt8) then
        Copter.set_failsafe_radio this false
  return ()

/-- C++ `Copter::read_radio : void ()`, `radio.cpp:92-133`. -/
def Copter.read_radio.body (fp : UInt64) (this : UInt64) : PMem.M Unit := do
  let mut tnow_ms : UInt32 := ((← PMem.clock) / 1000).toUInt32
  let t'1 ← rc
  let t'2 ← RC_Channels.read_input t'1
  if t'2 then
    let t'3 ← PMem.ldU64 (this + 8616)
    let t'4 ← RC_Channel.get_radio_in t'3
    Copter.set_throttle_and_failsafe this (Int16.toUInt16 (t'4))
    let t'5 ← PMem.ldU64 (this + 8616)
    let t'6 ← RC_Channel.get_control_in t'5
    Copter.set_throttle_zero_flag this t'6
    Copter.radio_passthrough_to_motors this
    let t'7 ← PMem.ldU32 (this + 11220)
    PMem.stF32 (fp + 0) ((UInt32.toBinary32 ((tnow_ms - t'7))) * (Binary32.ofBits 0x3a83126f /- 20000001/20000000000 -/))
    let t'8 ← PMem.ldU64 (this + 8616)
    let t'9 ← RC_Channel.get_control_in t'8
    PMem.stF32 (fp + 4) (Int16.toBinary32 (t'9))
    let t'10 ← LowPassFilter'float.apply (this + 11136) (fp + 4) (fp + 0)
    discard <| pure (t'10)
    PMem.stU32 (this + 11220) tnow_ms
    return ()
  let t'11 ← PMem.ldBits (this + 9508) 72 1
  if (UInt64.toUInt8 (t'11)) != (0 : UInt8) then
    return ()
  let t'12 ← PMem.ldU32 (this + 11220)
  let mut elapsed_ms : UInt32 := (tnow_ms - t'12)
  let t'13 ← rc
  let t'14 ← RC_Channels.get_fs_timeout_ms t'13
  if (decide (elapsed_ms < t'14)) then
    return ()
  let t'15 ← AP_ParamT'signed_char_1.operator_const_signed_char__ ((this + 6776) + 26)
  let t'16 ← PMem.ldI8 t'15
  if !(t'16 != (0 : Int8)) then
    return ()
  let t'17 ← rc
  let t'18 ← RC_Channels.has_ever_seen_rc_input t'17
  let mut sc'21 := !t'18
  if sc'21 then
    let t'19 ← PMem.ldU64 (this + 9528)
    let t'20 ← AP_Motors.armed t'19
    sc'21 := !t'20
  if sc'21 then
    return ()
  Copter.set_failsafe_radio this true
  return ()

def Copter.read_radio (this : UInt64) : PMem.M Unit := do
  let fp ← PMem.enter 8
  let r ← Copter.read_radio.body fp this
  PMem.leave fp
  return r

/-- C++ `Copter::esc_calibration_passthrough : void ()`, `esc_calibration.cpp:78-104`. -/
def Copter.esc_calibration_passthrough.body (fp : UInt64) (this : UInt64) : PMem.M Unit := do
  let t'1 ← Copter.gcs this
  GCS.send_text t'1 (6 : UInt32) (0x14607 : UInt64) /- "ESC calibration: Passing pilot throttle to ESCs" -/ (fp + 0)
  Copter.esc_calibration_setup this
  for _ in PMem.loopFuel do
    if !((1 : Int32) != (0 : Int32)) then break
    Copter.esc_calibration_notify this
    Copter.read_radio this
    let t'2 ← PMem.ldU64 ((0xba88 : UInt64) /- &hal -/ + 80)
    discard <| PMem.hal "AP_HAL::Scheduler::delay" t'2 #[(UInt16.toUInt64 ((Int16.toUInt16 (Int32.toInt16 ((3 : Int32))))))]
    let t'3 ← AP.srv
    let srv : UInt64 := t'3
    SRV_Channels.cork srv
    let t'4 ← PMem.ldU64 (this + 8616)
    let t'5 ← RC_Channel.get_control_in t'4
    let t'6 ← PMem.ldU64 (this + 9528)
    AP_MotorsMulticopter.set_throttle_passthrough_for_esc_calibration t'6 ((Int32.toBinary32 ((Int16.toInt32 (t'5)))) * (Binary32.ofBits 0x3a83126f /- 20000001/20000000000 -/))
    SRV_Channels.push srv
  return ()

def Copter.esc_calibration_passthrough (this : UInt64) : PMem.M Unit := do
  let fp ← PMem.enter 8
  let r ← Copter.esc_calibration_passthrough.body fp this
  PMem.leave fp
  return r

/-- C++ `Copter::esc_calibration_startup_check : void ()`, `esc_calibration.cpp:10-75`. -/
def Copter.esc_calibration_startup_check.body (fp : UInt64) (this : UInt64) : PMem.M Unit := do
  let t'1 ← PMem.ldU64 (this + 9528)
  let t'2 ← AP_Motors.is_brushed_pwm_type t'1
  if t'2 then
    return ()
  let mut i : UInt8 := Int8.toUInt8 (Int32.toInt8 ((0 : Int32)))
  for _ in PMem.loopFuel do
    let t'3 := i
    let t'4 := (t'3 + 1)
    i := t'4
    let mut sc'6 := (decide ((UInt32.toInt32 (UInt8.toUInt32 (t'3))) < (100 : Int32)))
    if sc'6 then
      let t'5 ← PMem.ldU32 (this + 11220)
      sc'6 := (t'5 == (Int32.toUInt32 ((0 : Int32))))
    if !(sc'6) then break
    let t'7 ← PMem.ldU64 ((0xba88 : UInt64) /- &hal -/ + 80)
    discard <| PMem.hal "AP_HAL::Scheduler::delay" t'7 #[(UInt16.toUInt64 ((Int16.toUInt16 (Int32.toInt16 ((20 : Int32))))))]
    Copter.read_radio this
  let t'8 ← AP_Arming_Copter.rc_calibration_checks (this + 8768) true
  if !t'8 then
    let t'9 ← AP_ParamT'signed_char_1.operator_const_signed_char__ ((this + 6776) + 48)
    let t'10 ← PMem.ldI8 t'9
    let mut sc'13 := ((Int8.toInt32 (t'10)) != (UInt32.toInt32 (UInt8.toUInt32 ((0 : UInt8)))))
    if sc'13 then
      let t'11 ← AP_ParamT'signed_char_1.operator_const_signed_char__ ((this + 6776) + 48)
      let t'12 ← PMem.ldI8 t'11
      sc'13 := ((Int8.toInt32 (t'12)) != (UInt32.toInt32 (UInt8.toUInt32 ((9 : UInt8)))))
    if sc'13 then
      PMem.stI8 (fp + 0) (UInt8.toInt8 ((0 : UInt8)))
      AP_ParamTBase'signed_char_1.set_and_save ((this + 6776) + 48) (fp + 0)
    return ()
  let t'14 ← AP_ParamT'signed_char_1.operator_const_signed_char__ ((this + 6776) + 48)
  let t'15 ← PMem.ldI8 t'14
  let sw'16 := Int8.toInt32 (t'15)
  if sw'16 == (0 : Int32) then
    let t'17 ← PMem.ldU64 (this + 8616)
    let t'18 ← RC_Channel.get_control_in t'17
    if (decide ((Int16.toInt32 (t'18)) ≥ (950 : Int32))) then
      PMem.stI8 (fp + 1) (UInt8.toInt8 ((1 : UInt8)))
      AP_ParamTBase'signed_char_1.set_and_save ((this + 6776) + 48) (fp + 1)
      let t'19 ← Copter.gcs this
      GCS.send_text t'19 (2 : UInt32) (0x145e8 : UInt64) /- "ESC calibration: Restart board" -/ (fp + 8)
      PMem.stB ((0xccc0 : UInt64) /- &AP_Notify::flags -/ + 9) true
      for _ in PMem.loopFuel do
        if !((1 : Int32) != (0 : Int32)) then break
        let t'20 ← PMem.ldU64 ((0xba88 : UInt64) /- &hal -/ + 80)
        discard <| PMem.hal "AP_HAL::Scheduler::delay" t'20 #[(UInt16.toUInt64 ((Int16.toUInt16 (Int32.toInt16 ((5 : Int32))))))]
  else if sw'16 == (1 : Int32) then
    let t'21 ← PMem.ldU64 (this + 8616)
    let t'22 ← RC_Channel.get_control_in t'21
    if (decide ((Int16.toInt32 (t'22)) ≥ (950 : Int32))) then
      Copter.esc_calibration_passthrough this
  else if sw'16 == (2 : Int32) then
    Copter.esc_calibration_passthrough this
  else if sw'16 == (3 : Int32) then
    Copter.esc_calibration_auto this
  else if sw'16 == (9 : Int32) then
    pure ()
  else
    pure ()
  let t'23 ← AP_ParamT'signed_char_1.operator_const_signed_char__ ((this + 6776) + 48)
  let t'24 ← PMem.ldI8 t'23
  if ((Int8.toInt32 (t'24)) != (UInt32.toInt32 (UInt8.toUInt32 ((9 : UInt8))))) then
    PMem.stI8 (fp + 16) (UInt8.toInt8 ((0 : UInt8)))
    AP_ParamTBase'signed_char_1.set_and_save ((this + 6776) + 48) (fp + 16)
  return ()

def Copter.esc_calibration_startup_check (this : UInt64) : PMem.M Unit := do
  let fp ← PMem.enter 17
  let r ← Copter.esc_calibration_startup_check.body fp this
  PMem.leave fp
  return r

/-- C++ `Functor<void>::method_wrapper : void (void *)`, `functor.h:85-89`. -/
def Functor'void.method_wrapper'AP_InertialSensor_update (obj : UInt64) : PMem.M Unit := do
  let mut obj := obj
  let mut t : UInt64 := obj
  VehicleBridge.AP_InertialSensor.update'0 t
  worldOutputs'drain
  return ()

/-- C++ `Functor<void>::method_wrapper : void (void *)`, `functor.h:85-89`. -/
def Functor'void.method_wrapper'Copter_run_rate_controller_main (obj : UInt64) : PMem.M Unit := do
  let mut obj := obj
  let mut t : UInt64 := obj
  Copter.run_rate_controller_main t
  return ()

/-- C++ `Functor<void>::method_wrapper : void (void *)`, `functor.h:85-89`. -/
def Functor'void.method_wrapper'Copter_motors_output_main (obj : UInt64) : PMem.M Unit := do
  let mut obj := obj
  let mut t : UInt64 := obj
  Copter.motors_output_main t
  return ()

/-- C++ `Functor<void>::method_wrapper : void (void *)`, `functor.h:85-89`. -/
def Functor'void.method_wrapper'Copter_read_AHRS (obj : UInt64) : PMem.M Unit := do
  let mut obj := obj
  let mut t : UInt64 := obj
  Copter.read_AHRS t
  return ()

/-- C++ `Functor<void>::method_wrapper : void (void *)`, `functor.h:85-89`. -/
def Functor'void.method_wrapper'Copter_read_inertia (obj : UInt64) : PMem.M Unit := do
  let mut obj := obj
  let mut t : UInt64 := obj
  Copter.read_inertia t
  return ()

/-- C++ `AP_Mission::restart_current_nav_cmd : bool ()`, `AP_Mission.cpp:710-724`. -/
def AP_Mission.restart_current_nav_cmd (this : UInt64) : PMem.M Bool := do
  let t'1 ← PMem.ldU32 (this + 4)
  if ((UInt32.toInt32 (t'1)) != (UInt32.toInt32 ((1 : UInt32)))) then
    return false
  let t'2 ← AP_Mission.get_current_nav_index this
  let mut nav_cmd_index : UInt16 := t'2
  let mut sc'4 := ((UInt32.toInt32 (UInt16.toUInt32 (nav_cmd_index))) == (0 : Int32))
  if !sc'4 then
    let t'3 ← AP_Mission.num_commands this
    sc'4 := (decide ((UInt32.toInt32 (UInt16.toUInt32 (nav_cmd_index))) ≥ (UInt32.toInt32 (UInt16.toUInt32 (t'3)))))
  if sc'4 then
    return false
  let t'5 ← PMem.ldU16 (this + 88)
  let t'6 ← AP_Mission.set_current_cmd this t'5
  return t'6

/-- C++ `ModeAuto::verify_land : bool ()`, `mode_auto.cpp:2155-2195`. -/
def ModeAuto.verify_land (this : UInt64) : PMem.M Bool := do
  let mut retval : Bool := false
  let t'1 ← PMem.ldI32 (this + 856)
  let sw'2 := t'1
  if sw'2 == (0 : Int32) then
    let t'3 ← PMem.ldU64 ((0x86d8 : UInt64) /- &copter -/ + 11192)
    let t'4 ← AC_WPNav.reached_wp_destination t'3
    if t'4 then
      ModeAuto.land_start this
      PMem.stI32 (this + 856) (1 : Int32)
  else if sw'2 == (1 : Int32) then
    let t'5 ← PMem.ldB (((0x86d8 : UInt64) /- &copter -/ + 9448) + 7)
    let mut sc'9 := t'5
    if sc'9 then
      let t'6 ← PMem.ldU64 (this + 64)
      let t'7 ← PMem.ldU64 t'6
      let t'8 ← AP_Motors.get_spool_state t'7
      sc'9 := (t'8 == (1 : UInt8))
    retval := sc'9
    let mut sc'11 := retval
    if sc'11 then
      let t'10 ← AP_Mission.continue_after_land_check_for_takeoff (this + 112)
      sc'11 := !t'10
    let mut sc'14 := sc'11
    if sc'14 then
      let t'12 ← PMem.ldU64 ((0x86d8 : UInt64) /- &copter -/ + 9528)
      let t'13 ← AP_Motors.armed t'12
      sc'14 := t'13
    if sc'14 then
      let t'15 ← AP_Arming_Copter.disarm ((0x86d8 : UInt64) /- &copter -/ + 8768) (13 : Int32) true
      discard <| pure (t'15)
      retval := false
  else
    retval := true
  return retval

/-- C++ `ModeAuto::circle_start : void ()`, `mode_auto.cpp:595-654`. -/
def ModeAuto.circle_start.body (fp : UInt64) (this : UInt64) : PMem.M Unit := do
  let t'1 ← PMem.ldF32 ((this + 892) + 4)
  let t'2 ← is_positive'float t'1
  if !t'2 then
    let t'3 ← PMem.ldU64 ((0x86d8 : UInt64) /- &copter -/ + 11208)
    let t'4 ← AC_Circle.get_rate_degs t'3
    let mut rate_degs : Binary32 := t'4
    let t'5 ← PMem.ldU64 (this + 56)
    let t'6 ← PMem.ldU64 t'5
    let t'7 ← AC_AttitudeControl.get_slew_yaw_max_rads t'6
    PMem.stF32 (fp + 0) t'7
    let t'8 ← is_positive'float (Binary32.abs rate_degs)
    let mut c'9 : Binary32 := default
    if t'8 then
      let t'10 ← radians (Binary32.abs rate_degs)
      PMem.stF32 (fp + 4) t'10
      let t'11 ← MIN'float_float (fp + 4) (fp + 0)
      let t'12 ← PMem.ldF32 t'11
      c'9 := t'12
    else
      let t'13 ← PMem.ldF32 (fp + 0)
      c'9 := t'13
    let mut rate_rads : Binary32 := c'9
    let t'14 ← Mode.AutoYaw.mode (0xeb78 : UInt64) /- &Mode::auto_yaw -/
    if (t'14 != (2 : Int32)) then
      let t'15 ← PMem.ldF32 (this + 892)
      let t'16 ← is_negative'float rate_degs
      let mut c'17 : Int32 := default
      if t'16 then
        c'17 := -(1 : Int32)
      else
        c'17 := (1 : Int32)
      Mode.AutoYaw.set_fixed_yaw_rad (0xeb78 : UInt64) /- &Mode::auto_yaw -/ ((Binary32.abs t'15) * ((Binary64.toBinary32 ((Binary64.ofBits 0x400921fb54442d18 /- 31415926535897931/10000000000000000 -/))) * (Int32.toBinary32 ((2 : Int32))))) rate_rads (Int32.toInt8 (c'17)) true
    let t'18 := ((← PMem.clock) / 1000).toUInt32
    PMem.stU32 ((this + 892) + 12) t'18
    PMem.stF32 ((this + 892) + 16) rate_rads
    let t'19 ← PMem.ldF32 (this + 892)
    PMem.stU64 (fp + 8) (Binary64.toBits (Binary32.toBinary64 ((Binary32.abs t'19))))
    let t'20 ← Mode.gcs this
    GCS.send_text t'20 (6 : UInt32) (0x14a48 : UInt64) /- "Mission: circling %.1f turns" -/ (fp + 8)
    ModeAuto.set_submode this (6 : UInt8)
    return ()
  let t'21 := Int16.toUInt16 (Int32.toInt16 ((0 : Int32)))
  PMem.stU16 ((this + 892) + 8) t'21
  let t'22 ← PMem.ldU64 ((0x86d8 : UInt64) /- &copter -/ + 11208)
  let t'23 ← AC_Circle.get_center_NED_m t'22
  Vector3'double.Vector3'4 (fp + 16) t'23
  let t'24 ← PMem.ldU64 ((0x86d8 : UInt64) /- &copter -/ + 11208)
  let t'25 ← AC_Circle.center_is_terrain_alt t'24
  let mut is_terrain_alt : Bool := t'25
  let t'26 ← Vector3'double.xy (fp + 16)
  Vector2'double.tofloat t'26 (fp + 40)
  let t'27 := (fp + 40)
  let t'28 ← PMem.ldF32 (this + 892)
  let t'29 ← PMem.ldF64 ((fp + 16) + 16)
  let t'30 ← PMem.ldU64 (this + 24)
  let t'31 ← PMem.ldU64 t'30
  let t'32 ← AC_WPNav.set_circle_destination_NED_m t'31 t'27 t'28 (Binary64.toBinary32 (t'29)) is_terrain_alt
  if !t'32 then
    Copter.failsafe_terrain_on_event (0x86d8 : UInt64) /- &copter -/
    return ()
  let t'33 ← PMem.ldF32 (this + 892)
  PMem.stU64 (fp + 48) (Binary64.toBits (Binary32.toBinary64 ((Binary32.abs t'33))))
  let t'34 ← Mode.gcs this
  GCS.send_text t'34 (6 : UInt32) (0x14a48 : UInt64) /- "Mission: circling %.1f turns" -/ (fp + 48)
  let t'35 ← Mode.AutoYaw.mode (0xeb78 : UInt64) /- &Mode::auto_yaw -/
  if (t'35 != (2 : Int32)) then
    Mode.AutoYaw.set_mode (0xeb78 : UInt64) /- &Mode::auto_yaw -/ (8 : Int32)
  ModeAuto.set_submode this (6 : UInt8)
  return ()

def ModeAuto.circle_start (this : UInt64) : PMem.M Unit := do
  let fp ← PMem.enter 56
  let r ← ModeAuto.circle_start.body fp this
  PMem.leave fp
  return r

/-- C++ `ModeAuto::verify_circle : bool (const AP_Mission::Mission_Command &)`, `mode_auto.cpp:2326-2359`. -/
def ModeAuto.verify_circle.body (fp : UInt64) (this : UInt64) (cmd : UInt64) : PMem.M Bool := do
  let t'1 ← PMem.ldU8 (this + 820)
  if (t'1 == (5 : UInt8)) then
    let t'2 ← PMem.ldU64 ((0x86d8 : UInt64) /- &copter -/ + 11192)
    let t'3 ← AC_WPNav.reached_wp_destination t'2
    if t'3 then
      ModeAuto.circle_start this
    return false
  let t'4 ← PMem.ldF32 ((this + 892) + 4)
  let t'5 ← is_positive'float t'4
  if !t'5 then
    let t'6 ← PMem.ldF32 ((this + 892) + 16)
    let t'7 ← PMem.ldU32 ((this + 892) + 12)
    let mut angle_swept_rad : Binary32 := ((t'6 * (UInt32.toBinary32 (((((← PMem.clock) / 1000).toUInt32) - t'7)))) * (Binary64.toBinary32 ((Binary64.ofBits 0x3f50624dd2f1a9fc /- 1/1000 -/))))
    let t'8 ← PMem.ldF32 (this + 892)
    return (decide (angle_swept_rad ≥ ((Binary32.abs t'8) * ((Binary64.toBinary32 ((Binary64.ofBits 0x400921fb54442d18 /- 31415926535897931/10000000000000000 -/))) * (Int32.toBinary32 ((2 : Int32)))))))
  let t'9 ← PMem.ldU64 ((0x86d8 : UInt64) /- &copter -/ + 11192)
  let t'10 ← AC_WPNav.get_circle_angle_covered_rad t'9
  let mut turns_done : UInt16 := Binary32.toUInt16 ((t'10 / ((Binary64.toBinary32 ((Binary64.ofBits 0x400921fb54442d18 /- 31415926535897931/10000000000000000 -/))) * (Int32.toBinary32 ((2 : Int32))))))
  let t'11 ← PMem.ldU16 ((this + 892) + 8)
  if (decide ((UInt32.toInt32 (UInt16.toUInt32 (turns_done))) > (UInt32.toInt32 (UInt16.toUInt32 (t'11))))) then
    PMem.stU16 ((this + 892) + 8) turns_done
    PMem.stU64 (fp + 0) (UInt32.toUInt64 ((UInt16.toUInt32 (turns_done))))
    let t'12 ← PMem.ldF32 (this + 892)
    PMem.stU64 (fp + 8) (Binary64.toBits (Binary32.toBinary64 ((Binary32.abs t'12))))
    let t'13 ← Mode.gcs this
    GCS.send_text t'13 (6 : UInt32) (0x14ab7 : UInt64) /- "Mission: circled %u/%.1f turns" -/ (fp + 0)
  let t'14 ← PMem.ldU64 ((0x86d8 : UInt64) /- &copter -/ + 11192)
  let t'15 ← AC_WPNav.reached_wp_destination t'14
  return t'15

def ModeAuto.verify_circle (this : UInt64) (cmd : UInt64) : PMem.M Bool := do
  let fp ← PMem.enter 16
  let r ← ModeAuto.verify_circle.body fp this cmd
  PMem.leave fp
  return r

/-- C++ `ModeAuto::verify_command : bool (const AP_Mission::Mission_Command &)`, `mode_auto.cpp:989-1118`. -/
def ModeAuto.verify_command.body (fp : UInt64) (this : UInt64) (cmd : UInt64) : PMem.M Bool := do
  let t'1 ← PMem.ldU64 ((0x86d8 : UInt64) /- &copter -/ + 9488)
  if (t'1 != ((0x86d8 : UInt64) /- &copter -/ + 11368)) then
    return false
  let mut cmd_complete : Bool := false
  let t'2 ← PMem.ldU16 (cmd + 2)
  let sw'3 := UInt32.toInt32 (UInt16.toUInt32 (t'2))
  if sw'3 == (84 : Int32) || sw'3 == (22 : Int32) then
    let t'4 ← ModeAuto.verify_takeoff this
    cmd_complete := t'4
  else if sw'3 == (16 : Int32) || sw'3 == (36 : Int32) then
    let t'5 ← ModeAuto.verify_nav_wp this cmd
    cmd_complete := t'5
  else if sw'3 == (85 : Int32) || sw'3 == (21 : Int32) then
    let t'6 ← ModeAuto.verify_land this
    cmd_complete := t'6
  else if sw'3 == (17 : Int32) then
    let t'7 ← ModeAuto.verify_loiter_unlimited this
    cmd_complete := t'7
  else if sw'3 == (18 : Int32) then
    let t'8 ← ModeAuto.verify_circle this cmd
    cmd_complete := t'8
  else if sw'3 == (19 : Int32) then
    let t'9 ← ModeAuto.verify_loiter_time this cmd
    cmd_complete := t'9
  else if sw'3 == (31 : Int32) then
    let t'10 ← ModeAuto.verify_loiter_to_alt this
    return t'10
  else if sw'3 == (20 : Int32) then
    let t'11 ← ModeAuto.verify_RTL this
    cmd_complete := t'11
  else if sw'3 == (82 : Int32) then
    let t'12 ← ModeAuto.verify_spline_wp this cmd
    cmd_complete := t'12
  else if sw'3 == (92 : Int32) then
    let t'13 ← ModeAuto.verify_nav_guided_enable this cmd
    cmd_complete := t'13
  else if sw'3 == (93 : Int32) then
    let t'14 ← ModeAuto.verify_nav_delay this cmd
    cmd_complete := t'14
  else if sw'3 == (42703 : Int32) then
    let t'15 ← ModeAuto.verify_nav_attitude_time this cmd
    cmd_complete := t'15
  else if sw'3 == (112 : Int32) then
    let t'16 ← ModeAuto.verify_wait_delay this
    cmd_complete := t'16
  else if sw'3 == (114 : Int32) then
    let t'17 ← ModeAuto.verify_within_distance this
    cmd_complete := t'17
  else if sw'3 == (115 : Int32) then
    let t'18 ← ModeAuto.verify_yaw this
    cmd_complete := t'18
  else if sw'3 == (178 : Int32) || sw'3 == (179 : Int32) || sw'3 == (195 : Int32) || sw'3 == (197 : Int32) || sw'3 == (201 : Int32) || sw'3 == (222 : Int32) || sw'3 == (188 : Int32) || sw'3 == (189 : Int32) then
    cmd_complete := true
  else
    let t'19 ← PMem.ldU16 (cmd + 2)
    PMem.stU64 (fp + 0) (Int64.toUInt64 (Int32.toInt64 ((UInt32.toInt32 (UInt16.toUInt32 (t'19))))))
    let t'20 ← Mode.gcs this
    GCS.send_text t'20 (4 : UInt32) (0x14a65 : UInt64) /- "Skipping invalid cmd #%i" -/ (fp + 0)
    cmd_complete := true
  if cmd_complete then
    let t'21 ← PMem.ldU16 cmd
    let t'22 ← Mode.gcs this
    GCS.send_mission_item_reached_message t'22 t'21
  return cmd_complete

def ModeAuto.verify_command (this : UInt64) (cmd : UInt64) : PMem.M Bool := do
  let fp ← PMem.enter 8
  let r ← ModeAuto.verify_command.body fp this cmd
  PMem.leave fp
  return r

/-- Calls through a function pointer of type `bool (void *, const AP_Mission::Mission_Command &)` at one call site of the Functor's operator: the functions the Functor objects read there can hold (1 of 2; the Functor values of AP_Mission::_cmd_verify_fn). -/
def fnptr'3'at'AP_Mission'_cmd_verify_fn (f : UInt64) (a0 : UInt64) (a1 : UInt64) : PMem.M Bool := do
  if f == 0x7e000080 then  -- ModeAuto::verify_command (FUNCTOR_BIND_MEMBER)
    ModeAuto.verify_command a0 a1
  else
    PMem.unreached "function pointer bool (void *, const AP_Mission::Mission_Command &)"
    return default

/-- (at the call sites reading AP_Mission::_cmd_verify_fn) C++ `Functor<bool, const AP_Mission::Mission_Command &>::operator() : bool (const AP_Mission::Mission_Command &) const`, `functor.h:52-55`. -/
def Functor'bool_const_AP_Mission_Mission_Command.operator__'at'AP_Mission'_cmd_verify_fn (this : UInt64) (args : UInt64) : PMem.M Bool := do
  let t'1 ← PMem.ldU64 (this + 8)
  let t'2 ← PMem.ldU64 this
  let t'3 ← fnptr'3'at'AP_Mission'_cmd_verify_fn t'1 t'2 args
  return t'3

/-- C++ `AP_Mission::verify_command : bool (const Mission_Command &)`, `AP_Mission.cpp:368-403`. -/
def AP_Mission.verify_command (this : UInt64) (cmd : UInt64) : PMem.M Bool := do
  let t'1 ← PMem.ldU16 (cmd + 2)
  let sw'2 := UInt32.toInt32 (UInt16.toUInt32 (t'1))
  if sw'2 == (183 : Int32) || sw'2 == (181 : Int32) || sw'2 == (184 : Int32) || sw'2 == (182 : Int32) || sw'2 == (202 : Int32) || sw'2 == (203 : Int32) || sw'2 == (206 : Int32) || sw'2 == (196 : Int32) || sw'2 == (208 : Int32) || sw'2 == (217 : Int32) || sw'2 == (216 : Int32) || sw'2 == (218 : Int32) || sw'2 == (215 : Int32) || sw'2 == (1000 : Int32) || sw'2 == (600 : Int32) || sw'2 == (2000 : Int32) || sw'2 == (2001 : Int32) || sw'2 == (531 : Int32) || sw'2 == (532 : Int32) || sw'2 == (534 : Int32) || sw'2 == (2500 : Int32) || sw'2 == (2501 : Int32) then
    return true
  else
    let t'3 ← Functor'bool_const_AP_Mission_Mission_Command.operator__'at'AP_Mission'_cmd_verify_fn (this + 48) cmd
    return t'3

/-- C++ `AP_Mission::advance_current_do_cmd : void ()`, `AP_Mission.cpp:2258-2286`. -/
def AP_Mission.advance_current_do_cmd.body (fp : UInt64) (this : UInt64) : PMem.M Unit := do
  let t'1 ← PMem.ldU32 (this + 4)
  let mut sc'3 := ((UInt32.toInt32 (t'1)) != (UInt32.toInt32 ((1 : UInt32))))
  if !sc'3 then
    let t'2 ← PMem.ldB ((this + 4) + 6)
    sc'3 := t'2
  if sc'3 then
    return ()
  let t'4 ← PMem.ldU16 (this + 116)
  let mut cmd_index : UInt16 := t'4
  if ((UInt32.toInt32 (UInt16.toUInt32 (cmd_index))) == (65535 : Int32)) then
    let t'5 := Int16.toUInt16 (Int32.toInt16 ((1 : Int32)))
    cmd_index := t'5
  else
    let t'6 ← PMem.ldU16 (this + 116)
    let t'7 := Int16.toUInt16 (Int32.toInt16 (((UInt32.toInt32 (UInt16.toUInt32 (t'6))) + (1 : Int32))))
    cmd_index := t'7
  AP_Mission.Mission_Command.Mission_Command (fp + 0)
  let t'8 ← AP_Mission.get_next_do_cmd this cmd_index (fp + 0)
  if !t'8 then
    PMem.stB ((this + 4) + 6) true
    return ()
  discard <| PMem.memcpy (this + 116) (fp + 0) 28
  discard <| pure ((this + 116))
  PMem.stB ((this + 4) + 5) true
  let t'9 ← AP_Mission.start_command this (this + 116)
  discard <| pure (t'9)
  return ()

def AP_Mission.advance_current_do_cmd (this : UInt64) : PMem.M Unit := do
  let fp ← PMem.enter 28
  let r ← AP_Mission.advance_current_do_cmd.body fp this
  PMem.leave fp
  return r

/-- C++ `AP_Mission::update : void ()`, `AP_Mission.cpp:310-360`. -/
def AP_Mission.update (this : UInt64) : PMem.M Unit := do
  let t'1 ← PMem.ldU32 (this + 4)
  let mut sc'4 := ((UInt32.toInt32 (t'1)) != (UInt32.toInt32 ((1 : UInt32))))
  if !sc'4 then
    let t'2 ← AP_ParamT'short_2.operator_const_short__ (this + 80)
    let t'3 ← PMem.ldI16 t'2
    sc'4 := ((Int16.toInt32 (t'3)) == (0 : Int32))
  if sc'4 then
    return ()
  AP_Mission.update_exit_position this
  let t'5 ← PMem.ldU32 (this + 600)
  let t'6 ← PMem.ldU32 (this + 596)
  if (t'5 != t'6) then
    let t'7 ← PMem.ldU32 (this + 596)
    PMem.stU32 (this + 600) t'7
    AP_Mission.on_mission_timestamp_change this
  let t'8 ← PMem.ldU16 (this + 88)
  let t'9 ← PMem.ldU64 ((0xba88 : UInt64) /- &hal -/ + 88)
  PMem.stU16 ((t'9 + 8) + 56) t'8
  let t'10 ← PMem.ldB ((this + 4) + 4)
  let mut sc'12 := !t'10
  if !sc'12 then
    let t'11 ← PMem.ldU16 (this + 88)
    sc'12 := ((UInt32.toInt32 (UInt16.toUInt32 (t'11))) == (65535 : Int32))
  if sc'12 then
    let t'13 ← AP_Mission.advance_current_nav_cmd this (Int16.toUInt16 (Int32.toInt16 ((0 : Int32))))
    if !t'13 then
      AP_Mission.complete this
      return ()
  else
    let t'14 ← AP_Mission.verify_command this (this + 88)
    if t'14 then
      PMem.stB ((this + 4) + 4) false
      let t'15 ← AP_Mission.advance_current_nav_cmd this (Int16.toUInt16 (Int32.toInt16 ((0 : Int32))))
      if !t'15 then
        AP_Mission.complete this
        return ()
  let t'16 ← PMem.ldB ((this + 4) + 5)
  if !t'16 then
    AP_Mission.advance_current_do_cmd this
  else
    let t'17 ← AP_Mission.verify_command this (this + 116)
    if t'17 then
      PMem.stB ((this + 4) + 5) false
  return ()

/-- C++ `_AutoTakeoff::run : void ()`, `takeoff.cpp:115-222`. -/
def _AutoTakeoff.run.body (fp : UInt64) (this : UInt64) : PMem.M Unit := do
  let g2 : UInt64 := ((0x86d8 : UInt64) /- &copter -/ + 6840)
  let wp_nav : UInt64 := ((0x86d8 : UInt64) /- &copter -/ + 11192)
  let t'1 ← PMem.ldU64 ((0x86d8 : UInt64) /- &copter -/ + 9528)
  let mut motors : UInt64 := t'1
  let t'2 ← PMem.ldU64 ((0x86d8 : UInt64) /- &copter -/ + 11184)
  let mut pos_control : UInt64 := t'2
  let t'3 ← PMem.ldU64 ((0x86d8 : UInt64) /- &copter -/ + 11168)
  let mut attitude_control : UInt64 := t'3
  let t'4 ← AP_Motors.armed motors
  let mut sc'6 := !t'4
  if !sc'6 then
    let t'5 ← PMem.ldB (((0x86d8 : UInt64) /- &copter -/ + 9448) + 5)
    sc'6 := !t'5
  if sc'6 then
    let t'7 ← Copter.is_tradheli (0x86d8 : UInt64) /- &copter -/
    let mut sc'9 := t'7
    if sc'9 then
      let t'8 ← AP_Motors.get_interlock motors
      sc'9 := t'8
    let t'10 ← PMem.ldU64 ((0x86d8 : UInt64) /- &copter -/ + 9488)
    Mode.make_safe_ground_handling t'10 sc'9
    let t'11 ← AC_PosControl.get_pos_estimate_U_m pos_control
    let t'12 ← AP_ParamT'float_4.operator_const_float__'1 g2
    let t'13 ← PMem.ldF32 t'12
    let t'14 := (t'11 + t'13)
    PMem.stF32 (this + 4) t'14
    return ()
  PMem.stF32 (fp + 0) (Binary32.ofBits 0x00000000 /- 0 -/)
  let t'15 ← PMem.ldB (this + 12)
  let mut sc'18 := t'15
  if sc'18 then
    let t'16 ← PMem.ldU64 wp_nav
    let t'17 ← AC_WPNav.get_terrain_U_m t'16 (fp + 0)
    sc'18 := !t'17
  if sc'18 then
    Copter.failsafe_terrain_on_event (0x86d8 : UInt64) /- &copter -/
    return ()
  AP_MotorsMulticopter.set_desired_spool_state motors (2 : UInt8)
  let t'19 ← AP_Motors.get_spool_state motors
  if (t'19 != (3 : UInt8)) then
    AC_PosControl.NE_relax_velocity_controller pos_control
    AC_PosControl.NE_update_controller pos_control
    AC_PosControl.D_relax_controller pos_control (Binary32.ofBits 0x00000000 /- 0 -/)
    AC_PosControl.D_update_controller pos_control
    AC_AttitudeControl.reset_yaw_target_and_rate attitude_control true
    AC_AttitudeControl.reset_rate_controller_I_terms attitude_control
    AC_PosControl.get_thrust_vector pos_control (fp + 8)
    let t'20 := (fp + 8)
    AC_AttitudeControl.input_thrust_vector_rate_heading_rads attitude_control t'20 (Binary64.toBinary32 ((Binary64.ofBits 0x0000000000000000 /- 0 -/))) true
    let t'21 ← AC_PosControl.get_pos_estimate_U_m pos_control
    let t'22 ← AP_ParamT'float_4.operator_const_float__'1 g2
    let t'23 ← PMem.ldF32 t'22
    let t'24 := (t'21 + t'23)
    PMem.stF32 (this + 4) t'24
    return ()
  let t'25 ← PMem.ldB (((0x86d8 : UInt64) /- &copter -/ + 9448) + 7)
  if t'25 then
    let t'26 ← PMem.ldU64 ((0x86d8 : UInt64) /- &copter -/ + 11168)
    let t'27 ← AC_AttitudeControl.get_throttle_in t'26
    let t'28 ← PMem.ldF32 ((0x86d8 : UInt64) /- &copter -/ + 376)
    let t'29 ← AP_ParamT'float_4.operator_const_float__'1 (((0x86d8 : UInt64) /- &copter -/ + 6840) + 1720)
    let t'30 ← PMem.ldF32 t'29
    let t'31 ← constrain_value_line'float (t'27 + (t'28 / t'30)) (Binary64.toBinary32 ((Binary64.ofBits 0x0000000000000000 /- 0 -/))) (Binary64.toBinary32 ((Binary64.ofBits 0x3ff0000000000000 /- 1 -/))) (Int32.toUInt32 ((161 : Int32)))
    let mut throttle : Binary32 := t'31
    let t'32 ← PMem.ldU64 ((0x86d8 : UInt64) /- &copter -/ + 11168)
    AC_AttitudeControl_Multi.set_throttle_out t'32 throttle true (Binary64.toBinary32 ((Binary64.ofBits 0x0000000000000000 /- 0 -/)))
    let t'33 ← PMem.ldU64 ((0x86d8 : UInt64) /- &copter -/ + 11184)
    AC_PosControl.D_init_controller t'33
    AC_PosControl.NE_relax_velocity_controller pos_control
    AC_PosControl.NE_update_controller pos_control
    AC_AttitudeControl.reset_rate_controller_I_terms attitude_control
    AC_PosControl.get_thrust_vector pos_control (fp + 24)
    let t'34 := (fp + 24)
    AC_AttitudeControl.input_thrust_vector_rate_heading_rads attitude_control t'34 (Binary64.toBinary32 ((Binary64.ofBits 0x0000000000000000 /- 0 -/))) true
    PMem.stF32 (fp + 36) (Binary64.toBinary32 ((Binary64.ofBits 0x3feccccccccccccd /- 45000000000000001/50000000000000000 -/)))
    let t'35 ← MIN'AP_ParamT_float_AP_PARAM_FLOAT_float (((0x86d8 : UInt64) /- &copter -/ + 6840) + 1724) (fp + 36)
    let t'36 ← PMem.ldF32 t'35
    let mut sc'41 := (decide (throttle ≥ t'36))
    if !sc'41 then
      let t'37 ← PMem.ldU64 ((0x86d8 : UInt64) /- &copter -/ + 11184)
      let t'38 ← AC_PosControl.get_estimated_accel_U_mss t'37
      let t'39 ← PMem.ldU64 ((0x86d8 : UInt64) /- &copter -/ + 11184)
      let t'40 ← AC_PosControl.D_get_max_accel_mss t'39
      sc'41 := (decide (t'38 ≥ ((Binary64.toBinary32 ((Binary64.ofBits 0x3fe0000000000000 /- 1/2 -/))) * t'40)))
    let mut sc'46 := sc'41
    if !sc'46 then
      let t'42 ← PMem.ldU64 ((0x86d8 : UInt64) /- &copter -/ + 11184)
      let t'43 ← AC_PosControl.get_vel_estimate_U_ms t'42
      let t'44 ← PMem.ldU64 ((0x86d8 : UInt64) /- &copter -/ + 11184)
      let t'45 ← AC_PosControl.get_max_speed_up_ms t'44
      sc'46 := (decide (t'43 ≥ ((Binary64.toBinary32 ((Binary64.ofBits 0x3fb999999999999a /- 10000000000000001/100000000000000000 -/))) * t'45)))
    let mut sc'51 := sc'46
    if !sc'51 then
      let t'47 ← PMem.ldB (this + 1)
      let mut sc'50 := t'47
      if sc'50 then
        let t'48 ← AC_PosControl.get_pos_estimate_U_m pos_control
        let t'49 ← PMem.ldF32 (this + 4)
        sc'50 := (decide (t'48 ≥ t'49))
      sc'51 := sc'50
    if sc'51 then
      Copter.set_land_complete (0x86d8 : UInt64) /- &copter -/ false
    return ()
  let t'52 ← PMem.ldB (this + 1)
  if t'52 then
    let t'53 ← AC_PosControl.get_pos_estimate_U_m pos_control
    let t'54 ← PMem.ldF32 (this + 4)
    if (decide (t'53 ≥ t'54)) then
      PMem.stB (this + 1) false
    AC_PosControl.NE_relax_velocity_controller pos_control
  else
    Vector2'float.Vector2 (fp + 40)
    Vector2'float.Vector2 (fp + 48)
    AC_PosControl.input_vel_accel_NE_m pos_control (fp + 40) (fp + 48) true
  AC_PosControl.NE_update_controller pos_control
  let t'55 ← PMem.ldF32 (this + 8)
  let t'56 ← PMem.ldF32 (fp + 0)
  PMem.stF32 (fp + 56) (-(t'55 + t'56))
  PMem.stF32 (fp + 64) (Binary64.toBinary32 ((Binary64.ofBits 0x0000000000000000 /- 0 -/)))
  let t'57 ← PMem.ldU64 ((0x86d8 : UInt64) /- &copter -/ + 11184)
  AC_PosControl.input_pos_vel_accel_D_m t'57 (fp + 56) (fp + 64) (Binary64.toBinary32 ((Binary64.ofBits 0x0000000000000000 /- 0 -/))) true
  AC_PosControl.D_update_controller pos_control
  AC_PosControl.get_thrust_vector pos_control (fp + 72)
  let t'58 := (fp + 72)
  let t'59 ← PMem.ldU64 ((0x86d8 : UInt64) /- &copter -/ + 9488)
  Mode.AutoYaw.get_heading (0xeb78 : UInt64) /- &Mode::auto_yaw -/ (fp + 104)
  let t'60 := (fp + 104)
  AC_AttitudeControl.HeadingCommand.HeadingCommand'2 (fp + 88) t'60
  AC_AttitudeControl.input_thrust_vector_heading attitude_control t'58 (fp + 88)
  let mut vel_threshold_fraction : Binary32 := Binary64.toBinary32 ((Binary64.ofBits 0x3fb999999999999a /- 10000000000000001/100000000000000000 -/))
  let t'61 ← PMem.ldU64 ((0x86d8 : UInt64) /- &copter -/ + 11184)
  let t'62 ← AC_PosControl.get_max_speed_up_ms t'61
  let t'63 ← sq (vel_threshold_fraction * t'62)
  let t'64 ← PMem.ldU64 ((0x86d8 : UInt64) /- &copter -/ + 11184)
  let t'65 ← AC_PosControl.D_get_max_accel_mss t'64
  let mut stop_distance_m : Binary32 := (((Binary64.toBinary32 ((Binary64.ofBits 0x3fe0000000000000 /- 1/2 -/))) * t'63) / t'65)
  let t'66 ← PMem.ldU64 ((0x86d8 : UInt64) /- &copter -/ + 11184)
  let t'67 ← AC_PosControl.get_pos_desired_U_m t'66
  let t'68 ← PMem.ldF32 (fp + 56)
  let mut reached_altitude : Bool := (decide (t'67 ≥ ((-t'68) - stop_distance_m)))
  let t'69 ← PMem.ldU64 ((0x86d8 : UInt64) /- &copter -/ + 11184)
  let t'70 ← AC_PosControl.get_vel_desired_U_ms t'69
  let t'71 ← PMem.ldU64 ((0x86d8 : UInt64) /- &copter -/ + 11184)
  let t'72 ← AC_PosControl.get_max_speed_up_ms t'71
  let mut reached_climb_rate : Bool := (decide (t'70 < (t'72 * vel_threshold_fraction)))
  let t'73 := (reached_altitude && reached_climb_rate)
  PMem.stB this t'73
  let t'74 ← PMem.ldB this
  if t'74 then
    PMem.stB (this + 1) false
    let t'75 ← PMem.ldU64 ((0x86d8 : UInt64) /- &copter -/ + 11184)
    let t'76 ← AC_PosControl.get_pos_desired_NED_m t'75
    let _complete_pos_ned_m : UInt64 := t'76
    let t'77 ← PMem.ldF64 _complete_pos_ned_m
    let t'78 ← PMem.ldF64 (_complete_pos_ned_m + 8)
    let t'79 ← PMem.ldF32 (fp + 56)
    Vector3'double.Vector3'3 (fp + 120) t'77 t'78 (Binary32.toBinary64 (t'79))
    discard <| PMem.memcpy (this + 16) (fp + 120) 24
    discard <| pure ((this + 16))
  return ()

def _AutoTakeoff.run (this : UInt64) : PMem.M Unit := do
  let fp ← PMem.enter 144
  let r ← _AutoTakeoff.run.body fp this
  PMem.leave fp
  return r

/-- C++ `ModeAuto::takeoff_run : void ()`, `mode_auto.cpp:1122-1130`. -/
def ModeAuto.takeoff_run (this : UInt64) : PMem.M Unit := do
  let t'1 ← ModeAuto.option_is_enabled this (2 : Int32)
  if t'1 then
    Copter.set_auto_armed (0x86d8 : UInt64) /- &copter -/ true
  _AutoTakeoff.run (0x131b0 : UInt64) /- &Mode::auto_takeoff -/
  return ()

/-- C++ `Mode::land_run_horizontal_control : void ()`, `mode.cpp:780-857`. -/
def Mode.land_run_horizontal_control.body (fp : UInt64) (this : UInt64) : PMem.M Unit := do
  Vector2'float.Vector2 (fp + 0)
  let t'1 ← PMem.ldB (((0x86d8 : UInt64) /- &copter -/ + 9448) + 14)
  if t'1 then
    let t'2 ← PMem.ldU64 (this + 40)
    let t'3 ← PMem.ldU64 t'2
    AC_PosControl.NE_soften_for_landing t'3
  let t'4 ← rc
  let t'5 ← RC_Channels_Copter.has_valid_input t'4
  if t'5 then
    let t'6 ← PMem.ldU64 (this + 8)
    let t'7 ← AP_ParamT'unsigned_short_2.operator_const_unsigned_short__ (t'6 + 8)
    let t'8 ← PMem.ldU16 t'7
    let mut sc'11 := (((UInt32.toInt32 (UInt16.toUInt32 (t'8))) &&& ((1 : Int32) <<< (1 : Int32))) != (0 : Int32))
    if sc'11 then
      let t'9 ← DigitalLPF'float.get ((0x86d8 : UInt64) /- &copter -/ + 11136)
      let t'10 ← PMem.ldF32 t'9
      sc'11 := (decide (t'10 > (Int32.toBinary32 ((700 : Int32)))))
    if sc'11 then
      let t'12 ← Mode.set_mode this (5 : UInt8) (9 : UInt8)
      if !t'12 then
        let t'13 ← Mode.set_mode this (2 : UInt8) (9 : UInt8)
        discard <| pure (t'13)
    let t'14 ← PMem.ldU64 (this + 8)
    let t'15 ← AP_ParamT'signed_char_1.operator_const_signed_char__ (t'14 + 51)
    let t'16 ← PMem.ldI8 t'15
    if t'16 != (0 : Int8) then
      let t'17 ← PMem.ldU64 (this + 24)
      let t'18 ← PMem.ldU64 t'17
      let t'19 ← AC_WPNav.get_wp_acceleration_mss t'18
      let mut max_pilot_vel_ms : Binary32 := (t'19 * (Binary64.toBinary32 ((Binary64.ofBits 0x3fe0000000000000 /- 1/2 -/))))
      Mode.get_pilot_desired_velocity this (fp + 8) max_pilot_vel_ms
      let t'20 := (fp + 8)
      discard <| PMem.memcpy (fp + 0) t'20 8
      discard <| pure ((fp + 0))
      let t'21 ← Vector2'float.is_zero (fp + 0)
      if !t'21 then
        let t'22 ← PMem.ldB (((0x86d8 : UInt64) /- &copter -/ + 9448) + 19)
        if !t'22 then
          pure ()
        PMem.stB (((0x86d8 : UInt64) /- &copter -/ + 9448) + 19) true
  PMem.stB (((0x86d8 : UInt64) /- &copter -/ + 9448) + 26) false
  let t'23 ← PMem.ldB (((0x86d8 : UInt64) /- &copter -/ + 9448) + 26)
  if !t'23 then
    Vector2'float.Vector2 (fp + 16)
    let t'24 ← PMem.ldU64 (this + 40)
    let t'25 ← PMem.ldU64 t'24
    AC_PosControl.input_vel_accel_NE_m t'25 (fp + 0) (fp + 16) true
  let t'26 ← PMem.ldU64 (this + 40)
  let t'27 ← PMem.ldU64 t'26
  AC_PosControl.NE_update_controller t'27
  let t'28 ← PMem.ldU64 (this + 40)
  let t'29 ← PMem.ldU64 t'28
  AC_PosControl.get_thrust_vector t'29 (fp + 40)
  let t'30 := (fp + 40)
  Vector3'float.Vector3'3 (fp + 24) t'30
  Mode.AutoYaw.get_heading (0xeb78 : UInt64) /- &Mode::auto_yaw -/ (fp + 72)
  let t'31 := (fp + 72)
  AC_AttitudeControl.HeadingCommand.HeadingCommand'2 (fp + 56) t'31
  let t'32 ← PMem.ldU64 (this + 56)
  let t'33 ← PMem.ldU64 t'32
  AC_AttitudeControl.input_thrust_vector_heading t'33 (fp + 24) (fp + 56)
  return ()

def Mode.land_run_horizontal_control (this : UInt64) : PMem.M Unit := do
  let fp ← PMem.enter 84
  let r ← Mode.land_run_horizontal_control.body fp this
  PMem.leave fp
  return r

/-- C++ `Mode::land_run_horiz_and_vert_control : void (bool)`, `AP_Common.h:228-231`. -/
def Mode.land_run_horiz_and_vert_control (this : UInt64) (pause_descent : Bool) : PMem.M Unit := do
  let mut pause_descent := pause_descent
  Mode.land_run_horizontal_control this
  Mode.land_run_vertical_control this pause_descent
  return ()

/-- C++ `Mode::land_run_normal_or_precland : void (bool)`, `mode.cpp:861-876`. -/
def Mode.land_run_normal_or_precland (this : UInt64) (pause_descent : Bool) : PMem.M Unit := do
  let mut pause_descent := pause_descent
  Mode.land_run_horiz_and_vert_control this pause_descent
  return ()

/-- C++ `ModeAuto::land_run : void ()`, `mode_auto.cpp:1158-1172`. -/
def ModeAuto.land_run (this : UInt64) : PMem.M Unit := do
  let t'1 ← Mode.is_disarmed_or_landed this
  if t'1 then
    Mode.make_safe_ground_handling this false
    return ()
  let t'2 ← PMem.ldU64 (this + 64)
  let t'3 ← PMem.ldU64 t'2
  AP_MotorsMulticopter.set_desired_spool_state t'3 (2 : UInt8)
  Mode.land_run_normal_or_precland this false
  return ()

/-- C++ `ModeRTL::climb_start : void ()`, `mode_rtl.cpp:230-243`. -/
def ModeRTL.climb_start.body (fp : UInt64) (this : UInt64) : PMem.M Unit := do
  let t'1 ← PMem.ldU64 (this + 24)
  let t'2 ← PMem.ldU64 t'1
  let t'3 ← AC_WPNav.set_wp_destination_loc t'2 ((this + 132) + 16) (Binary64.toBinary32 ((Binary64.ofBits 0x0000000000000000 /- 0 -/)))
  let mut sc'7 := !t'3
  if !sc'7 then
    let t'4 ← PMem.ldU64 (this + 24)
    let t'5 ← PMem.ldU64 t'4
    let t'6 ← AC_WPNav.set_wp_destination_next_loc t'5 ((this + 132) + 32) (Binary64.toBinary32 ((Binary64.ofBits 0x0000000000000000 /- 0 -/)))
    sc'7 := !t'6
  if sc'7 then
    let t'8 ← Mode.gcs this
    GCS.send_text t'8 (2 : UInt32) (0x14be6 : UInt64) /- "RTL: unexpected error setting climb target" -/ (fp + 0)
    let t'9 ← Copter.set_mode (0x86d8 : UInt64) /- &copter -/ (9 : UInt8) (11 : UInt8)
    discard <| pure (t'9)
    return ()
  Mode.AutoYaw.set_mode (0xeb78 : UInt64) /- &Mode::auto_yaw -/ (0 : Int32)
  return ()

def ModeRTL.climb_start (this : UInt64) : PMem.M Unit := do
  let fp ← PMem.enter 8
  let r ← ModeRTL.climb_start.body fp this
  PMem.leave fp
  return r

/-- C++ `ModeRTL::set_submode : void (SubMode)`, `mode_rtl.cpp:197-227`. -/
def ModeRTL.set_submode (this : UInt64) (submode : UInt8) : PMem.M Unit := do
  let mut submode := submode
  PMem.stU8 (this + 128) submode
  PMem.stB (this + 129) false
  let t'1 := ((← PMem.clock) / 1000).toUInt32
  PMem.stU32 (this + 200) t'1
  let sw'2 := submode
  if sw'2 == (0 : UInt8) then
    pure ()
  else if sw'2 == (1 : UInt8) then
    ModeRTL.climb_start this
  else if sw'2 == (2 : UInt8) then
    let t'3 ← ModeRTL.return_start this
    if !t'3 then
      ModeRTL.restart_without_terrain this
  else if sw'2 == (3 : UInt8) then
    ModeRTL.hold_at_return_point_start this
  else if sw'2 == (4 : UInt8) then
    ModeRTL.descent_start this
  else if sw'2 == (5 : UInt8) then
    ModeRTL.land_start this
  else
    pure ()
  return ()

/-- C++ `ModeRTL::advance_state : void ()`, `mode_rtl.cpp:173-194`. -/
def ModeRTL.advance_state (this : UInt64) : PMem.M Unit := do
  let t'1 ← PMem.ldU8 (this + 128)
  let sw'2 := t'1
  if sw'2 == (0 : UInt8) then
    ModeRTL.build_path this
    ModeRTL.set_submode this (1 : UInt8)
  else if sw'2 == (1 : UInt8) then
    ModeRTL.set_submode this (2 : UInt8)
  else if sw'2 == (2 : UInt8) then
    ModeRTL.set_submode this (3 : UInt8)
  else if sw'2 == (3 : UInt8) then
    let t'3 ← PMem.ldB ((this + 132) + 64)
    let mut sc'5 := t'3
    if !sc'5 then
      let t'4 ← PMem.ldBits ((0x86d8 : UInt64) /- &copter -/ + 9508) 72 1
      sc'5 := (UInt64.toUInt8 (t'4)) != (0 : UInt8)
    let mut c'6 : UInt8 := default
    if sc'5 then
      c'6 := (5 : UInt8)
    else
      c'6 := (4 : UInt8)
    ModeRTL.set_submode this c'6
  else if sw'2 == (4 : UInt8) || sw'2 == (5 : UInt8) then
    pure ()
  else
    pure ()
  return ()

/-- C++ `ModeRTL::descent_run : void ()`, `mode_rtl.cpp:348-401`. -/
def ModeRTL.descent_run.body (fp : UInt64) (this : UInt64) : PMem.M Unit := do
  Vector2'float.Vector2 (fp + 0)
  let t'1 ← Mode.is_disarmed_or_landed this
  if t'1 then
    Mode.make_safe_ground_handling this false
    return ()
  let t'2 ← rc
  let t'3 ← RC_Channels_Copter.has_valid_input t'2
  if t'3 then
    let t'4 ← PMem.ldU64 (this + 8)
    let t'5 ← AP_ParamT'unsigned_short_2.operator_const_unsigned_short__ (t'4 + 8)
    let t'6 ← PMem.ldU16 t'5
    let mut sc'9 := (((UInt32.toInt32 (UInt16.toUInt32 (t'6))) &&& ((1 : Int32) <<< (1 : Int32))) != (0 : Int32))
    if sc'9 then
      let t'7 ← DigitalLPF'float.get ((0x86d8 : UInt64) /- &copter -/ + 11136)
      let t'8 ← PMem.ldF32 t'7
      sc'9 := (decide (t'8 > (Int32.toBinary32 ((700 : Int32)))))
    if sc'9 then
      let t'10 ← Copter.set_mode (0x86d8 : UInt64) /- &copter -/ (5 : UInt8) (9 : UInt8)
      if !t'10 then
        let t'11 ← Copter.set_mode (0x86d8 : UInt64) /- &copter -/ (2 : UInt8) (9 : UInt8)
        discard <| pure (t'11)
    let t'12 ← PMem.ldU64 (this + 8)
    let t'13 ← AP_ParamT'signed_char_1.operator_const_signed_char__ (t'12 + 51)
    let t'14 ← PMem.ldI8 t'13
    if t'14 != (0 : Int8) then
      let t'15 ← PMem.ldU64 (this + 24)
      let t'16 ← PMem.ldU64 t'15
      let t'17 ← AC_WPNav.get_wp_acceleration_mss t'16
      Mode.get_pilot_desired_velocity this (fp + 8) (t'17 * (Binary64.toBinary32 ((Binary64.ofBits 0x3fe0000000000000 /- 1/2 -/))))
      let t'18 := (fp + 8)
      discard <| PMem.memcpy (fp + 0) t'18 8
      discard <| pure ((fp + 0))
      let t'19 ← Vector2'float.is_zero (fp + 0)
      if !t'19 then
        let t'20 ← PMem.ldB (((0x86d8 : UInt64) /- &copter -/ + 9448) + 19)
        if !t'20 then
          pure ()
        PMem.stB (((0x86d8 : UInt64) /- &copter -/ + 9448) + 19) true
  let t'21 ← PMem.ldU64 (this + 64)
  let t'22 ← PMem.ldU64 t'21
  AP_MotorsMulticopter.set_desired_spool_state t'22 (2 : UInt8)
  Vector2'float.Vector2 (fp + 16)
  let t'23 ← PMem.ldU64 (this + 40)
  let t'24 ← PMem.ldU64 t'23
  AC_PosControl.input_vel_accel_NE_m t'24 (fp + 0) (fp + 16) true
  let t'25 ← PMem.ldU64 (this + 40)
  let t'26 ← PMem.ldU64 t'25
  AC_PosControl.NE_update_controller t'26
  let t'27 ← PMem.ldI32 (((this + 132) + 48) + 4)
  let t'28 ← PMem.ldU64 (this + 40)
  let t'29 ← PMem.ldU64 t'28
  AC_PosControl.D_set_alt_target_with_slew_m t'29 ((Int32.toBinary32 (t'27)) * (Binary64.toBinary32 ((Binary64.ofBits 0x3f847ae147ae147b /- 1/100 -/))))
  let t'30 ← PMem.ldU64 (this + 40)
  let t'31 ← PMem.ldU64 t'30
  AC_PosControl.D_update_controller t'31
  let t'32 ← PMem.ldU64 (this + 40)
  let t'33 ← PMem.ldU64 t'32
  AC_PosControl.get_thrust_vector t'33 (fp + 24)
  let t'34 := (fp + 24)
  Mode.AutoYaw.get_heading (0xeb78 : UInt64) /- &Mode::auto_yaw -/ (fp + 56)
  let t'35 := (fp + 56)
  AC_AttitudeControl.HeadingCommand.HeadingCommand'2 (fp + 40) t'35
  let t'36 ← PMem.ldU64 (this + 56)
  let t'37 ← PMem.ldU64 t'36
  AC_AttitudeControl.input_thrust_vector_heading t'37 t'34 (fp + 40)
  let t'38 ← PMem.ldI32 (((this + 132) + 48) + 4)
  let t'39 ← PMem.ldU64 (this + 40)
  let t'40 ← PMem.ldU64 t'39
  let t'41 ← AC_PosControl.get_pos_estimate_U_m t'40
  let t'42 := (decide ((Binary32.abs (((Int32.toBinary32 (t'38)) * (Binary64.toBinary32 ((Binary64.ofBits 0x3f847ae147ae147b /- 1/100 -/)))) - t'41)) < (Binary64.toBinary32 ((Binary64.ofBits 0x3fc999999999999a /- 20000000000000001/100000000000000000 -/)))))
  PMem.stB (this + 129) t'42
  return ()

def ModeRTL.descent_run (this : UInt64) : PMem.M Unit := do
  let fp ← PMem.enter 68
  let r ← ModeRTL.descent_run.body fp this
  PMem.leave fp
  return r

/-- C++ `ModeRTL::land_run : void (bool)`, `mode_rtl.cpp:446-467`. -/
def ModeRTL.land_run (this : UInt64) (disarm_on_land : Bool) : PMem.M Unit := do
  let mut disarm_on_land := disarm_on_land
  let t'1 ← PMem.ldB (((0x86d8 : UInt64) /- &copter -/ + 9448) + 7)
  PMem.stB (this + 129) t'1
  let mut sc'3 := disarm_on_land
  if sc'3 then
    let t'2 ← PMem.ldB (((0x86d8 : UInt64) /- &copter -/ + 9448) + 7)
    sc'3 := t'2
  let mut sc'7 := sc'3
  if sc'7 then
    let t'4 ← PMem.ldU64 (this + 64)
    let t'5 ← PMem.ldU64 t'4
    let t'6 ← AP_Motors.get_spool_state t'5
    sc'7 := (t'6 == (1 : UInt8))
  if sc'7 then
    let t'8 ← AP_Arming_Copter.disarm ((0x86d8 : UInt64) /- &copter -/ + 8768) (13 : Int32) true
    discard <| pure (t'8)
  let t'9 ← Mode.is_disarmed_or_landed this
  if t'9 then
    Mode.make_safe_ground_handling this false
    return ()
  let t'10 ← PMem.ldU64 (this + 64)
  let t'11 ← PMem.ldU64 t'10
  AP_MotorsMulticopter.set_desired_spool_state t'11 (2 : UInt8)
  Mode.land_run_normal_or_precland this false
  return ()

/-- C++ `ModeRTL::run : void (bool)`, `mode_rtl.cpp:132-170`. -/
def ModeRTL.run'2 (this : UInt64) (disarm_on_land : Bool) : PMem.M Unit := do
  let mut disarm_on_land := disarm_on_land
  let t'1 ← PMem.ldU64 (this + 64)
  let t'2 ← PMem.ldU64 t'1
  let t'3 ← AP_Motors.armed t'2
  if !t'3 then
    return ()
  let t'4 ← PMem.ldB (this + 129)
  if t'4 then
    ModeRTL.advance_state this
  let t'5 ← PMem.ldU8 (this + 128)
  let sw'6 := t'5
  if sw'6 == (0 : UInt8) then
    ModeRTL.climb_return_run this
    PMem.stB (this + 129) true
  else if sw'6 == (1 : UInt8) || sw'6 == (2 : UInt8) then
    ModeRTL.climb_return_run this
  else if sw'6 == (3 : UInt8) then
    ModeRTL.hold_at_return_point_run this
  else if sw'6 == (4 : UInt8) then
    ModeRTL.descent_run this
  else if sw'6 == (5 : UInt8) then
    ModeRTL.land_run this disarm_on_land
  else
    pure ()
  return ()

/-- C++ `ModeAuto::rtl_run : void ()`, `mode_auto.cpp:1176-1180`. -/
def ModeAuto.rtl_run (this : UInt64) : PMem.M Unit := do
  ModeRTL.run'2 ((0x86d8 : UInt64) /- &copter -/ + 12888) false
  return ()

/-- C++ `ModeGuided::takeoff_run : void ()`, `mode_guided.cpp:718-731`. -/
def ModeGuided.takeoff_run (this : UInt64) : PMem.M Unit := do
  _AutoTakeoff.run (0x131b0 : UInt64) /- &Mode::auto_takeoff -/
  let t'1 ← PMem.ldB (0x131b0 : UInt64) /- &Mode::auto_takeoff -/
  let mut sc'3 := t'1
  if sc'3 then
    let t'2 ← PMem.ldB (0x131d8 : UInt64) /- &ModeGuided::takeoff_complete -/
    sc'3 := !t'2
  if sc'3 then
    PMem.stB (0x131d8 : UInt64) /- &ModeGuided::takeoff_complete -/ true
  return ()

/-- C++ `ModeGuided::pos_control_run : void ()`, `mode_guided.cpp:735-785`. -/
def ModeGuided.pos_control_run.body (fp : UInt64) (this : UInt64) : PMem.M Unit := do
  let t'1 ← Mode.is_disarmed_or_landed this
  if t'1 then
    let t'2 ← Copter.is_tradheli (0x86d8 : UInt64) /- &copter -/
    let mut sc'6 := t'2
    if sc'6 then
      let t'3 ← PMem.ldU64 (this + 64)
      let t'4 ← PMem.ldU64 t'3
      let t'5 ← AP_Motors.get_interlock t'4
      sc'6 := t'5
    Mode.make_safe_ground_handling this sc'6
    return ()
  PMem.stF32 (fp + 0) (Binary32.ofBits 0x00000000 /- 0 -/)
  let t'7 ← PMem.ldB (0x12e50 : UInt64) /- &guided_is_terrain_alt -/
  let mut sc'11 := t'7
  if sc'11 then
    let t'8 ← PMem.ldU64 (this + 24)
    let t'9 ← PMem.ldU64 t'8
    let t'10 ← AC_WPNav.get_terrain_D_m t'9 (fp + 0)
    sc'11 := !t'10
  if sc'11 then
    Copter.failsafe_terrain_on_event (0x86d8 : UInt64) /- &copter -/
    return ()
  let t'12 ← PMem.ldU64 (this + 64)
  let t'13 ← PMem.ldU64 t'12
  AP_MotorsMulticopter.set_desired_spool_state t'13 (2 : UInt8)
  Vector3'float.zero (0xebb8 : UInt64) /- &guided_accel_target_ned_mss -/
  Vector3'float.zero (0xeba8 : UInt64) /- &guided_vel_target_ned_ms -/
  let t'14 ← PMem.ldU32 (0x12e30 : UInt64) /- &update_time_ms -/
  let t'15 ← ModeGuided.get_timeout_ms this
  if (decide (((((← PMem.clock) / 1000).toUInt32) - t'14) > t'15)) then
    let t'16 ← Mode.AutoYaw.mode (0xeb78 : UInt64) /- &Mode::auto_yaw -/
    let mut sc'18 := (t'16 == (7 : Int32))
    if !sc'18 then
      let t'17 ← Mode.AutoYaw.mode (0xeb78 : UInt64) /- &Mode::auto_yaw -/
      sc'18 := (t'17 == (6 : Int32))
    if sc'18 then
      Mode.AutoYaw.set_mode (0xeb78 : UInt64) /- &Mode::auto_yaw -/ (0 : Int32)
  let mut terrain_margin_m : Binary32 := Binary64.toBinary32 ((Binary64.ofBits 0x0000000000000000 /- 0 -/))
  let t'19 ← PMem.ldB (0x12e50 : UInt64) /- &guided_is_terrain_alt -/
  if t'19 then
    let t'20 ← PMem.ldU64 ((0x86d8 : UInt64) /- &copter -/ + 11192)
    let t'21 ← AC_WPNav.get_terrain_margin_m t'20
    PMem.stF32 (fp + 4) t'21
    let t'22 ← PMem.ldF64 ((0x12e38 : UInt64) /- &guided_pos_target_ned_m -/ + 16)
    PMem.stF64 (fp + 8) ((Binary64.ofBits 0x3fe0000000000000 /- 1/2 -/) * (Binary64.abs t'22))
    let t'23 ← MIN'float_double (fp + 4) (fp + 8)
    let t'24 := Binary64.toBinary32 (t'23)
    terrain_margin_m := t'24
  let t'25 ← PMem.ldF32 (fp + 0)
  let t'26 ← PMem.ldU64 (this + 40)
  let t'27 ← PMem.ldU64 t'26
  AC_PosControl.input_pos_NED_m t'27 (0x12e38 : UInt64) /- &guided_pos_target_ned_m -/ t'25 terrain_margin_m
  let t'28 ← PMem.ldU64 (this + 40)
  let t'29 ← PMem.ldU64 t'28
  AC_PosControl.NE_update_controller t'29
  let t'30 ← PMem.ldU64 (this + 40)
  let t'31 ← PMem.ldU64 t'30
  AC_PosControl.D_update_controller t'31
  let t'32 ← PMem.ldU64 (this + 40)
  let t'33 ← PMem.ldU64 t'32
  AC_PosControl.get_thrust_vector t'33 (fp + 16)
  let t'34 := (fp + 16)
  Mode.AutoYaw.get_heading (0xeb78 : UInt64) /- &Mode::auto_yaw -/ (fp + 48)
  let t'35 := (fp + 48)
  AC_AttitudeControl.HeadingCommand.HeadingCommand'2 (fp + 32) t'35
  let t'36 ← PMem.ldU64 (this + 56)
  let t'37 ← PMem.ldU64 t'36
  AC_AttitudeControl.input_thrust_vector_heading t'37 t'34 (fp + 32)
  return ()

def ModeGuided.pos_control_run (this : UInt64) : PMem.M Unit := do
  let fp ← PMem.enter 60
  let r ← ModeGuided.pos_control_run.body fp this
  PMem.leave fp
  return r

/-- C++ `ModeGuided::run : void ()`, `mode_guided.cpp:64-110`. -/
def ModeGuided.run (this : UInt64) : PMem.M Unit := do
  let t'1 ← PMem.ldB (this + 117)
  if t'1 then
    ModeGuided.pause_control_run this
    return ()
  let t'2 ← PMem.ldI32 (this + 112)
  let sw'3 := t'2
  if sw'3 == (0 : Int32) then
    ModeGuided.takeoff_run this
  else if sw'3 == (1 : Int32) then
    ModeGuided.wp_control_run this
    let t'4 ← PMem.ldB (this + 116)
    let mut sc'8 := t'4
    if sc'8 then
      let t'5 ← PMem.ldU64 (this + 24)
      let t'6 ← PMem.ldU64 t'5
      let t'7 ← AC_WPNav.reached_wp_destination t'6
      sc'8 := t'7
    if sc'8 then
      PMem.stB (this + 116) false
      let t'9 ← Mode.gcs this
      GCS.send_mission_item_reached_message t'9 (Int16.toUInt16 (Int32.toInt16 ((0 : Int32))))
  else if sw'3 == (2 : Int32) then
    ModeGuided.pos_control_run this
  else if sw'3 == (5 : Int32) then
    ModeGuided.accel_control_run this
  else if sw'3 == (4 : Int32) then
    ModeGuided.velaccel_control_run this
  else if sw'3 == (3 : Int32) then
    ModeGuided.posvelaccel_control_run this
  else if sw'3 == (6 : Int32) then
    ModeGuided.angle_control_run this
  else
    pure ()
  return ()

/-- C++ `ModeAuto::nav_guided_run : void ()`, `mode_auto.cpp:1185-1189`. -/
def ModeAuto.nav_guided_run (this : UInt64) : PMem.M Unit := do
  ModeGuided.run ((0x86d8 : UInt64) /- &copter -/ + 12520)
  return ()

/-- C++ `ModeAuto::loiter_to_alt_run : void ()`, `mode_auto.cpp:1202-1264`. -/
def ModeAuto.loiter_to_alt_run (this : UInt64) : PMem.M Unit := do
  let t'1 ← Mode.is_disarmed_or_landed this
  let mut sc'5 := t'1
  if !sc'5 then
    let t'2 ← PMem.ldU64 (this + 64)
    let t'3 ← PMem.ldU64 t'2
    let t'4 ← AP_Motors.get_interlock t'3
    sc'5 := !t'4
  if sc'5 then
    Mode.make_safe_ground_handling this false
    return ()
  let t'6 ← PMem.ldBits (this + 828) 0 1
  if !(t'6 != 0) then
    let t'7 ← PMem.ldU64 (this + 24)
    let t'8 ← PMem.ldU64 t'7
    let t'9 ← AC_WPNav.reached_wp_destination_NE t'8
    PMem.stBits (this + 828) 0 1 (if t'9 then (1 : UInt64) else 0)
    let t'10 ← PMem.ldBits (this + 828) 0 1
    if !(t'10 != 0) then
      ModeAuto.wp_run this
      return ()
  let t'11 ← PMem.ldBits (this + 828) 1 1
  if !(t'11 != 0) then
    let t'12 ← PMem.ldU64 (this + 24)
    let t'13 ← PMem.ldU64 t'12
    let t'14 ← AC_WPNav.get_default_speed_NE_ms t'13
    let t'15 ← PMem.ldU64 (this + 24)
    let t'16 ← PMem.ldU64 t'15
    let t'17 ← AC_WPNav.get_wp_acceleration_mss t'16
    let t'18 ← PMem.ldU64 (this + 40)
    let t'19 ← PMem.ldU64 t'18
    AC_PosControl.NE_set_max_speed_accel_m t'19 t'14 t'17
    let t'20 ← PMem.ldU64 (this + 24)
    let t'21 ← PMem.ldU64 t'20
    let t'22 ← AC_WPNav.get_default_speed_NE_ms t'21
    let t'23 ← PMem.ldU64 (this + 24)
    let t'24 ← PMem.ldU64 t'23
    let t'25 ← AC_WPNav.get_wp_acceleration_mss t'24
    let t'26 ← PMem.ldU64 (this + 40)
    let t'27 ← PMem.ldU64 t'26
    AC_PosControl.NE_set_correction_speed_accel_m t'27 t'22 t'25
    let t'28 ← PMem.ldU64 (this + 40)
    let t'29 ← PMem.ldU64 t'28
    let t'30 ← AC_PosControl.NE_is_active t'29
    if !t'30 then
      let t'31 ← PMem.ldU64 (this + 40)
      let t'32 ← PMem.ldU64 t'31
      AC_PosControl.NE_init_controller t'32
    PMem.stBits (this + 828) 1 1 (if true then (1 : UInt64) else 0)
  let t'33 ← PMem.ldI32 (((0x86d8 : UInt64) /- &copter -/ + 11148) + 4)
  let t'34 ← PMem.ldF32 ((this + 828) + 8)
  let mut alt_error_m : Binary32 := (((Int32.toBinary32 (t'33)) * (Binary64.toBinary32 ((Binary64.ofBits 0x3f847ae147ae147b /- 1/100 -/)))) - t'34)
  if (decide ((Binary32.abs alt_error_m) < (Binary64.toBinary32 ((Binary64.ofBits 0x3fa999999999999a /- 50000000000000003/1000000000000000000 -/))))) then
    PMem.stBits (this + 828) 2 1 (if true then (1 : UInt64) else 0)
  else
    let t'35 ← PMem.ldF32 ((this + 828) + 4)
    if (decide ((alt_error_m * t'35) < (Int32.toBinary32 ((0 : Int32))))) then
      PMem.stBits (this + 828) 2 1 (if true then (1 : UInt64) else 0)
  PMem.stF32 ((this + 828) + 4) alt_error_m
  Mode.land_run_horizontal_control this
  let t'36 ← PMem.ldU64 (this + 40)
  let t'37 ← PMem.ldU64 t'36
  let t'38 ← AC_PosControl.D_get_pos_p t'37
  let t'39 ← AC_P_1D.kP t'38
  let t'40 ← AP_ParamT'float_4.operator_const_float__'1 t'39
  let t'41 ← PMem.ldF32 t'40
  let t'42 ← PMem.ldU64 (this + 40)
  let t'43 ← PMem.ldU64 t'42
  let t'44 ← AC_PosControl.D_get_max_accel_mss t'43
  let t'45 ← PMem.ldU64 (this + 104)
  let t'46 ← PMem.ldF32 t'45
  let t'47 ← sqrt_controller (-alt_error_m) t'41 t'44 t'46
  let mut target_climb_rate_ms : Binary32 := t'47
  let t'48 ← PMem.ldU64 (this + 40)
  let t'49 ← PMem.ldU64 t'48
  let t'50 ← AC_PosControl.get_max_speed_down_ms t'49
  let t'51 ← PMem.ldU64 (this + 40)
  let t'52 ← PMem.ldU64 t'51
  let t'53 ← AC_PosControl.get_max_speed_up_ms t'52
  let t'54 ← constrain_value_line'float target_climb_rate_ms (-t'50) t'53 (Int32.toUInt32 ((1250 : Int32)))
  target_climb_rate_ms := t'54
  let t'55 ← Mode.get_avoidance_adjusted_climbrate_ms this target_climb_rate_ms
  target_climb_rate_ms := t'55
  let t'56 ← PMem.ldU64 (this + 40)
  let t'57 ← PMem.ldU64 t'56
  AC_PosControl.D_set_pos_target_from_climb_rate_ms t'57 target_climb_rate_ms false
  let t'58 ← PMem.ldU64 (this + 40)
  let t'59 ← PMem.ldU64 t'58
  AC_PosControl.D_update_controller t'59
  return ()

/-- C++ `ModeAuto::run : void ()`, `mode_auto.cpp:91-184`. -/
def ModeAuto.run.body (fp : UInt64) (this : UInt64) : PMem.M Unit := do
  let t'1 ← PMem.ldB (this + 860)
  if t'1 then
    Location.Location (fp + 0)
    let t'2 ← VehicleBridge.AP_AHRS.get_origin'1 ((0x86d8 : UInt64) /- &copter -/ + 4080) (fp + 0)
    if t'2 then
      AP_Mission.start_or_resume (this + 112)
      PMem.stB (this + 860) false
      for _ in [0:1] do
        let t'3 ← AP_Mission_ChangeDetector.check_for_mission_change (this + 728)
        if t'3 then
          pure ()
  else
    let t'4 ← AP_Mission_ChangeDetector.check_for_mission_change (this + 728)
    if t'4 then
      let t'5 ← AP_Mission.state (this + 112)
      let mut sc'7 := ((UInt32.toInt32 (t'5)) == (UInt32.toInt32 ((1 : UInt32))))
      if sc'7 then
        let t'6 ← PMem.ldU8 (this + 820)
        sc'7 := (t'6 == (2 : UInt8))
      if sc'7 then
        let t'8 ← AP_Mission.restart_current_nav_cmd (this + 112)
        if t'8 then
          let t'9 ← Mode.gcs this
          GCS.send_text t'9 (2 : UInt32) (0x14935 : UInt64) /- "Auto mission changed, restarted command" -/ (fp + 16)
        else
          let t'10 ← Mode.gcs this
          GCS.send_text t'10 (2 : UInt32) (0x1495d : UInt64) /- "Auto mission changed but failed to restart command" -/ (fp + 24)
    AP_Mission.update (this + 112)
  let t'11 ← PMem.ldU8 (this + 820)
  let sw'12 := t'11
  if sw'12 == (0 : UInt8) then
    ModeAuto.loiter_run this
  else if sw'12 == (1 : UInt8) then
    ModeAuto.takeoff_run this
  else if sw'12 == (2 : UInt8) || sw'12 == (5 : UInt8) || sw'12 == (6 : UInt8) then
    ModeAuto.wp_run this
  else if sw'12 == (3 : UInt8) then
    ModeAuto.land_run this
  else if sw'12 == (4 : UInt8) then
    ModeAuto.rtl_run this
  else if sw'12 == (7 : UInt8) || sw'12 == (10 : UInt8) then
    ModeAuto.nav_guided_run this
  else if sw'12 == (8 : UInt8) then
    ModeAuto.loiter_run this
  else if sw'12 == (9 : UInt8) then
    ModeAuto.loiter_to_alt_run this
  else if sw'12 == (11 : UInt8) then
    ModeAuto.nav_attitude_time_run this
  else
    pure ()
  let t'13 ← AP_Mission.get_in_landing_sequence_flag (this + 112)
  let mut sc'15 := t'13
  if !sc'15 then
    let t'14 ← AP_Mission.get_in_return_path_flag (this + 112)
    sc'15 := t'14
  let mut sc'17 := sc'15
  if !sc'17 then
    let t'16 ← AP_Mission.state (this + 112)
    sc'17 := ((UInt32.toInt32 (t'16)) == (UInt32.toInt32 ((2 : UInt32))))
  let mut auto_rtl_active : Bool := sc'17
  let t'18 ← PMem.ldB (this + 861)
  if (t'18 && (!auto_rtl_active)) then
    PMem.stB (this + 861) false
  return ()

def ModeAuto.run (this : UInt64) : PMem.M Unit := do
  let fp ← PMem.enter 32
  let r ← ModeAuto.run.body fp this
  PMem.leave fp
  return r

/-- C++ `ModeBrake::run : void ()`, `mode_brake.cpp:35-70`. -/
def ModeBrake.run.body (fp : UInt64) (this : UInt64) : PMem.M Unit := do
  let t'1 ← Mode.is_disarmed_or_landed this
  if t'1 then
    Mode.make_safe_ground_handling this false
    let t'2 ← PMem.ldU64 (this + 40)
    let t'3 ← PMem.ldU64 t'2
    AC_PosControl.D_relax_controller t'3 (Binary32.ofBits 0x00000000 /- 0 -/)
    return ()
  let t'4 ← PMem.ldU64 (this + 64)
  let t'5 ← PMem.ldU64 t'4
  AP_MotorsMulticopter.set_desired_spool_state t'5 (2 : UInt8)
  let t'6 ← PMem.ldB (((0x86d8 : UInt64) /- &copter -/ + 9448) + 14)
  if t'6 then
    let t'7 ← PMem.ldU64 (this + 40)
    let t'8 ← PMem.ldU64 t'7
    AC_PosControl.NE_soften_for_landing t'8
  Vector2'float.Vector2 (fp + 0)
  Vector2'float.Vector2 (fp + 8)
  let t'9 ← PMem.ldU64 (this + 40)
  let t'10 ← PMem.ldU64 t'9
  AC_PosControl.input_vel_accel_NE_m t'10 (fp + 0) (fp + 8) true
  let t'11 ← PMem.ldU64 (this + 40)
  let t'12 ← PMem.ldU64 t'11
  AC_PosControl.NE_update_controller t'12
  let t'13 ← PMem.ldU64 (this + 40)
  let t'14 ← PMem.ldU64 t'13
  AC_PosControl.get_thrust_vector t'14 (fp + 16)
  let t'15 := (fp + 16)
  let t'16 ← PMem.ldU64 (this + 56)
  let t'17 ← PMem.ldU64 t'16
  AC_AttitudeControl.input_thrust_vector_rate_heading_rads t'17 t'15 (Binary32.ofBits 0x00000000 /- 0 -/) true
  let t'18 ← PMem.ldU64 (this + 40)
  let t'19 ← PMem.ldU64 t'18
  AC_PosControl.D_set_pos_target_from_climb_rate_ms t'19 (Binary32.ofBits 0x00000000 /- 0 -/) false
  let t'20 ← PMem.ldU64 (this + 40)
  let t'21 ← PMem.ldU64 t'20
  AC_PosControl.D_update_controller t'21
  let t'22 ← PMem.ldU32 (this + 116)
  let mut sc'25 := (t'22 != (Int32.toUInt32 ((0 : Int32))))
  if sc'25 then
    let t'23 ← PMem.ldU32 (this + 112)
    let t'24 ← PMem.ldU32 (this + 116)
    sc'25 := (decide (((((← PMem.clock) / 1000).toUInt32) - t'23) ≥ t'24))
  if sc'25 then
    let t'26 ← Copter.set_mode (0x86d8 : UInt64) /- &copter -/ (5 : UInt8) (12 : UInt8)
    if !t'26 then
      let t'27 ← Copter.set_mode (0x86d8 : UInt64) /- &copter -/ (2 : UInt8) (12 : UInt8)
      discard <| pure (t'27)
  return ()

def ModeBrake.run (this : UInt64) : PMem.M Unit := do
  let fp ← PMem.enter 28
  let r ← ModeBrake.run.body fp this
  PMem.leave fp
  return r

/-- C++ `ModeLand::gps_run : void ()`, `mode_land.cpp:124-146`. -/
def ModeLand.gps_run (this : UInt64) : PMem.M Unit := do
  let t'1 ← PMem.ldB (((0x86d8 : UInt64) /- &copter -/ + 9448) + 7)
  let mut sc'5 := t'1
  if sc'5 then
    let t'2 ← PMem.ldU64 (this + 64)
    let t'3 ← PMem.ldU64 t'2
    let t'4 ← AP_Motors.get_spool_state t'3
    sc'5 := (t'4 == (1 : UInt8))
  if sc'5 then
    let t'6 ← AP_Arming_Copter.disarm ((0x86d8 : UInt64) /- &copter -/ + 8768) (13 : Int32) true
    discard <| pure (t'6)
  let t'7 ← Mode.is_disarmed_or_landed this
  if t'7 then
    Mode.make_safe_ground_handling this false
  else
    let t'8 ← PMem.ldU64 (this + 64)
    let t'9 ← PMem.ldU64 t'8
    AP_MotorsMulticopter.set_desired_spool_state t'9 (2 : UInt8)
    let t'10 ← PMem.ldB (this + 132)
    let mut sc'12 := t'10
    if sc'12 then
      let t'11 ← PMem.ldU32 (this + 128)
      sc'12 := (decide (((((← PMem.clock) / 1000).toUInt32) - t'11) ≥ (Int32.toUInt32 ((4000 : Int32)))))
    if sc'12 then
      PMem.stB (this + 132) false
    let t'13 ← PMem.ldB (this + 132)
    Mode.land_run_normal_or_precland this t'13
  return ()

/-- C++ `ModeLand::nogps_run : void ()`, `mode_land.cpp:151-193`. -/
def ModeLand.nogps_run.body (fp : UInt64) (this : UInt64) : PMem.M Unit := do
  PMem.stF32 (fp + 0) (Binary32.ofBits 0x00000000 /- 0 -/)
  PMem.stF32 (fp + 8) (Binary32.ofBits 0x00000000 /- 0 -/)
  let t'1 ← rc
  let t'2 ← RC_Channels_Copter.has_valid_input t'1
  if t'2 then
    let t'3 ← PMem.ldU64 (this + 8)
    let t'4 ← AP_ParamT'unsigned_short_2.operator_const_unsigned_short__ (t'3 + 8)
    let t'5 ← PMem.ldU16 t'4
    let mut sc'8 := (((UInt32.toInt32 (UInt16.toUInt32 (t'5))) &&& ((1 : Int32) <<< (1 : Int32))) != (0 : Int32))
    if sc'8 then
      let t'6 ← DigitalLPF'float.get ((0x86d8 : UInt64) /- &copter -/ + 11136)
      let t'7 ← PMem.ldF32 t'6
      sc'8 := (decide (t'7 > (Int32.toBinary32 ((700 : Int32)))))
    if sc'8 then
      let t'9 ← Copter.set_mode (0x86d8 : UInt64) /- &copter -/ (2 : UInt8) (9 : UInt8)
      discard <| pure (t'9)
    let t'10 ← PMem.ldU64 (this + 8)
    let t'11 ← AP_ParamT'signed_char_1.operator_const_signed_char__ (t'10 + 51)
    let t'12 ← PMem.ldI8 t'11
    if t'12 != (0 : Int8) then
      let t'13 ← PMem.ldU64 (this + 56)
      let t'14 ← PMem.ldU64 t'13
      let t'15 ← AC_AttitudeControl.lean_angle_max_rad t'14
      let t'16 ← PMem.ldU64 (this + 56)
      let t'17 ← PMem.ldU64 t'16
      let t'18 ← AC_AttitudeControl.get_althold_lean_angle_max_rad t'17
      Mode.get_pilot_desired_lean_angles_rad this (fp + 0) (fp + 8) t'15 t'18
  let t'19 ← PMem.ldB (((0x86d8 : UInt64) /- &copter -/ + 9448) + 7)
  let mut sc'23 := t'19
  if sc'23 then
    let t'20 ← PMem.ldU64 (this + 64)
    let t'21 ← PMem.ldU64 t'20
    let t'22 ← AP_Motors.get_spool_state t'21
    sc'23 := (t'22 == (1 : UInt8))
  if sc'23 then
    let t'24 ← AP_Arming_Copter.disarm ((0x86d8 : UInt64) /- &copter -/ + 8768) (13 : Int32) true
    discard <| pure (t'24)
  let t'25 ← Mode.is_disarmed_or_landed this
  if t'25 then
    Mode.make_safe_ground_handling this false
  else
    let t'26 ← PMem.ldU64 (this + 64)
    let t'27 ← PMem.ldU64 t'26
    AP_MotorsMulticopter.set_desired_spool_state t'27 (2 : UInt8)
    let t'28 ← PMem.ldB (this + 132)
    let mut sc'30 := t'28
    if sc'30 then
      let t'29 ← PMem.ldU32 (this + 128)
      sc'30 := (decide (((((← PMem.clock) / 1000).toUInt32) - t'29) ≥ (Int32.toUInt32 ((4000 : Int32)))))
    if sc'30 then
      PMem.stB (this + 132) false
    let t'31 ← PMem.ldB (this + 132)
    Mode.land_run_vertical_control this t'31
  let t'32 ← PMem.ldF32 (fp + 0)
  let t'33 ← PMem.ldF32 (fp + 8)
  Mode.AutoYaw.get_heading (0xeb78 : UInt64) /- &Mode::auto_yaw -/ (fp + 16)
  let t'34 := (fp + 16)
  let t'35 ← PMem.ldF32 (t'34 + 4)
  let t'36 ← PMem.ldU64 (this + 56)
  let t'37 ← PMem.ldU64 t'36
  AC_AttitudeControl.input_euler_angle_roll_pitch_euler_rate_yaw_rad t'37 t'32 t'33 t'35
  return ()

def ModeLand.nogps_run (this : UInt64) : PMem.M Unit := do
  let fp ← PMem.enter 28
  let r ← ModeLand.nogps_run.body fp this
  PMem.leave fp
  return r

/-- C++ `ModeLand::run : void ()`, `mode_land.cpp:112-119`. -/
def ModeLand.run (this : UInt64) : PMem.M Unit := do
  let t'1 ← PMem.ldB (this + 112)
  if t'1 then
    ModeLand.gps_run this
  else
    ModeLand.nogps_run this
  return ()

/-- C++ `ModeRTL::run : void ()`, `mode.h:1519-1521`. -/
def ModeRTL.run (this : UInt64) : PMem.M Unit := do
  ModeRTL.run'2 this true
  return ()

/-- Virtual calls of `Mode::run()` through a `Mode *`: by the object's address, over the member objects of `copter` whose class derives from Mode (9), each arm the final overrider of its class. -/
def vcall'Mode'run'29 (this : UInt64) : PMem.M Unit := do
  if this == ((0x86d8 : UInt64) /- &copter -/ + 11256) then  -- copter.ModeAltHold
    ModeAltHold.run this
  else if this == ((0x86d8 : UInt64) /- &copter -/ + 11368) then  -- copter.ModeAuto
    ModeAuto.run this
  else if this == ((0x86d8 : UInt64) /- &copter -/ + 12280) then  -- copter.ModeBrake
    ModeBrake.run this
  else if this == ((0x86d8 : UInt64) /- &copter -/ + 12400) then  -- copter.ModeCircle
    ModeCircle.run this
  else if this == ((0x86d8 : UInt64) /- &copter -/ + 12520) then  -- copter.ModeGuided
    ModeGuided.run this
  else if this == ((0x86d8 : UInt64) /- &copter -/ + 12640) then  -- copter.ModeLand
    ModeLand.run this
  else if this == ((0x86d8 : UInt64) /- &copter -/ + 12776) then  -- copter.ModeLoiter
    ModeLoiter.run this
  else if this == ((0x86d8 : UInt64) /- &copter -/ + 12888) then  -- copter.ModeRTL
    ModeRTL.run this
  else if this == ((0x86d8 : UInt64) /- &copter -/ + 13096) then  -- copter.ModeStabilize
    ModeStabilize.run this
  else
    PMem.unreached "virtual Mode::run on an object outside copter"
    return ()

/-- C++ `Functor<void>::method_wrapper : void (void *)`, `functor.h:85-89`. -/
def Functor'void.method_wrapper'Copter_update_home_from_EKF (obj : UInt64) : PMem.M Unit := do
  let mut obj := obj
  let mut t : UInt64 := obj
  Copter.update_home_from_EKF t
  return ()

/-- C++ `Functor<void>::method_wrapper : void (void *)`, `functor.h:85-89`. -/
def Functor'void.method_wrapper'Copter_update_land_and_crash_detectors (obj : UInt64) : PMem.M Unit := do
  let mut obj := obj
  let mut t : UInt64 := obj
  Copter.update_land_and_crash_detectors t
  return ()

/-- C++ `Functor<void>::method_wrapper : void (void *)`, `functor.h:85-89`. -/
def Functor'void.method_wrapper'Copter_update_rangefinder_terrain_offset (obj : UInt64) : PMem.M Unit := do
  let mut obj := obj
  let mut t : UInt64 := obj
  Copter.update_rangefinder_terrain_offset t
  return ()

/-- C++ `RC_Channels::read_mode_switch : void ()`, `RC_Channels.cpp:287-298`. -/
def RC_Channels.read_mode_switch (this : UInt64) : PMem.M Unit := do
  let t'1 ← RC_Channels_Copter.has_valid_input this
  if !t'1 then
    return ()
  let t'2 ← RC_Channels.flight_mode_channel this
  let mut c : UInt64 := t'2
  if (c == (0 : UInt64)) then
    return ()
  RC_Channel.read_mode_switch c
  return ()

/-- C++ `Copter::rc_loop : void ()`, `Copter.cpp:585-591`. -/
def Copter.rc_loop (this : UInt64) : PMem.M Unit := do
  Copter.read_radio this
  let t'1 ← rc
  RC_Channels.read_mode_switch t'1
  return ()

/-- C++ `Functor<void>::method_wrapper : void (void *)`, `functor.h:85-89`. -/
def Functor'void.method_wrapper'Copter_throttle_loop (obj : UInt64) : PMem.M Unit := do
  let mut obj := obj
  let mut t : UInt64 := obj
  Copter.throttle_loop t
  return ()

/-- C++ `Functor<void>::method_wrapper : void (void *)`, `functor.h:85-89`. -/
def Functor'void.method_wrapper'AP_GPS_update (obj : UInt64) : PMem.M Unit := do
  let mut obj := obj
  let mut t : UInt64 := obj
  VehicleBridge.AP_GPS.update'0 t
  worldOutputs'drain
  return ()

/-- C++ `Copter::handle_battery_failsafe : void (const char *, const int8_t)`, `events.cpp:99-123`. -/
def Copter.handle_battery_failsafe (this : UInt64) (type_str : UInt64) (action : Int8) : PMem.M Unit := do
  let mut type_str := type_str
  let mut action := action
  let mut desired_action : UInt8 := Int8.toUInt8 (action)
  let t'1 ← Copter.should_disarm_on_failsafe this
  if (t'1 && (desired_action != (0 : UInt8))) then
    let t'2 ← AP_Arming_Copter.disarm (this + 8768) (7 : Int32) true
    discard <| pure (t'2)
    desired_action := (0 : UInt8)
    Copter.announce_failsafe this (0x1470b : UInt64) /- "Battery" -/ (0x14683 : UInt64) /- "Disarming" -/
  else
    let t'3 ← PMem.ldU64 (this + 9488)
    let t'4 ← vcall'Mode'is_landing'15 t'3
    let mut sc'6 := t'4
    if sc'6 then
      let t'5 ← Copter.failsafe_option this (8 : Int32)
      sc'6 := t'5
    if (sc'6 && (desired_action != (0 : UInt8))) then
      desired_action := (1 : UInt8)
      Copter.announce_failsafe this (0x1470b : UInt64) /- "Battery" -/ (0x1469d : UInt64) /- "Continuing Landing" -/
    else
      Copter.announce_failsafe this (0x1470b : UInt64) /- "Battery" -/ (0 : UInt64)
  Copter.do_failsafe_action this desired_action (4 : UInt8)
  return ()

/-- Calls through a function pointer of type `void (void *, const char *, const signed char)` at one call site of the Functor's operator: the functions the Functor objects read there can hold (1 of 1; the Functor values of AP_BattMonitor::_battery_failsafe_handler_fn). -/
def fnptr'4'at'AP_BattMonitor'_battery_failsafe_handler_fn (f : UInt64) (a0 : UInt64) (a1 : UInt64) (a2 : Int8) : PMem.M Unit := do
  if f == 0x7e000060 then  -- Copter::handle_battery_failsafe (FUNCTOR_BIND_MEMBER)
    Copter.handle_battery_failsafe a0 a1 a2
  else
    PMem.unreached "function pointer void (void *, const char *, const signed char)"
    return ()

/-- (at the call sites reading AP_BattMonitor::_battery_failsafe_handler_fn) C++ `Functor<void, const char *, const signed char>::operator() : void (const char *, const signed char) const`, `functor.h:52-55`. -/
def Functor'void_const_char_const_signed_char.operator__'at'AP_BattMonitor'_battery_failsafe_handler_fn (this : UInt64) (args : UInt64) (args'2 : Int8) : PMem.M Unit := do
  let mut args := args
  let mut args'2 := args'2
  let t'1 ← PMem.ldU64 (this + 8)
  let t'2 ← PMem.ldU64 this
  fnptr'4'at'AP_BattMonitor'_battery_failsafe_handler_fn t'1 t'2 args args'2
  return ()

/-- C++ `AP_BattMonitor::check_failsafes : void ()`, `AP_BattMonitor.cpp:933-994`. -/
def AP_BattMonitor.check_failsafes.body (fp : UInt64) (this : UInt64) : PMem.M Unit := do
  if (← get).armed then
    let mut i : UInt8 := Int8.toUInt8 (Int32.toInt8 ((0 : Int32)))
    let mut first'1 := true
    for _ in PMem.loopFuel do
      if !first'1 then
        let t'2 := i
        let t'3 := (t'2 + 1)
        i := t'3
        pure ()
      first'1 := false
      let t'4 ← PMem.ldU8 (this + 1492)
      if !((decide ((UInt32.toInt32 (UInt8.toUInt32 (i))) < (UInt32.toInt32 (UInt8.toUInt32 (t'4)))))) then break
      let t'5 ← PMem.ldU64 ((this + 1416) + ((UInt64.toInt64 (UInt8.toUInt64 (i))) * 8).toUInt64)
      if (t'5 == (0 : UInt64)) then
        continue
      let t'6 ← PMem.ldU64 ((this + 1416) + ((UInt64.toInt64 (UInt8.toUInt64 (i))) * 8).toUInt64)
      let t'7 ← AP_BattMonitor_Backend.update_failsafes t'6
      let mut type' : UInt8 := t'7
      let t'8 ← PMem.ldU8 (((this + 408) + ((UInt64.toInt64 (UInt8.toUInt64 (i))) * 112).toUInt64) + 72)
      if (decide (type' ≤ t'8)) then
        continue
      let mut action : Int8 := Int32.toInt8 ((0 : Int32))
      let mut type_str : UInt64 := (0 : UInt64)
      let sw'9 := type'
      if sw'9 == (0 : UInt8) then
        continue
        let t'10 := Int32.toInt8 ((0 : Int32))
        action := t'10
        let t'11 := (0x16794 : UInt64) /- "missing, last:" -/
        type_str := t'11
      else if sw'9 == (1 : UInt8) then
        let t'12 := Int32.toInt8 ((0 : Int32))
        action := t'12
        let t'13 := (0x16794 : UInt64) /- "missing, last:" -/
        type_str := t'13
      else if sw'9 == (2 : UInt8) then
        let t'14 ← AP_ParamT'signed_char_1.operator_const_signed_char__ (((this + 8) + ((UInt64.toInt64 (UInt8.toUInt64 (i))) * 44).toUInt64) + 41)
        let t'15 ← PMem.ldI8 t'14
        action := t'15
        let t'16 := (0x167a3 : UInt64) /- "low" -/
        type_str := t'16
      else if sw'9 == (3 : UInt8) then
        let t'17 ← AP_ParamT'signed_char_1.operator_const_signed_char__ (((this + 8) + ((UInt64.toInt64 (UInt8.toUInt64 (i))) * 44).toUInt64) + 42)
        let t'18 ← PMem.ldI8 t'17
        action := t'18
        let t'19 := (0x167a7 : UInt64) /- "critical" -/
        type_str := t'19
      else
        pure ()
      PMem.stU64 (fp + 0) (Int64.toUInt64 (Int32.toInt64 (((UInt32.toInt32 (UInt8.toUInt32 (i))) + (1 : Int32)))))
      PMem.stU64 (fp + 8) type_str
      let t'20 ← AP_BattMonitor.voltage this i
      PMem.stU64 (fp + 16) (Binary64.toBits (Binary32.toBinary64 (t'20)))
      let t'21 ← PMem.ldF32 (((this + 408) + ((UInt64.toInt64 (UInt8.toUInt64 (i))) * 112).toUInt64) + 36)
      PMem.stU64 (fp + 24) (Binary64.toBits (Binary32.toBinary64 (t'21)))
      let t'22 ← gcs
      GCS.send_text t'22 (4 : UInt32) (0x167b0 : UInt64) /- "Battery %d is %s %.2fV used %.0f mAh" -/ (fp + 0)
      PMem.stB (this + 1521) true
      PMem.stB ((0xccc0 : UInt64) /- &AP_Notify::flags -/ + 11) true
      PMem.stU8 (((this + 408) + ((UInt64.toInt64 (UInt8.toUInt64 (i))) * 112).toUInt64) + 72) type'
      let mut priority : Int8 := Int32.toInt8 ((0 : Int32))
      let t'23 ← PMem.ldU64 (this + 1512)
      if (t'23 != (0 : UInt64)) then
        for _ in PMem.loopFuel do
          let t'24 ← PMem.ldU64 (this + 1512)
          let t'25 ← PMem.ldI8 (t'24 + ((Int8.toInt64 (priority)) * 1).toUInt64)
          if !(((Int8.toInt32 (t'25)) != (-(1 : Int32)))) then break
          let t'26 ← PMem.ldU64 (this + 1512)
          let t'27 ← PMem.ldI8 (t'26 + ((Int8.toInt64 (priority)) * 1).toUInt64)
          if ((Int8.toInt32 (t'27)) == (Int8.toInt32 (action))) then
            break
          let t'28 := priority
          let t'29 := (t'28 + 1)
          priority := t'29
      let t'30 ← PMem.ldI8 (this + 1520)
      if (decide ((Int8.toInt32 (priority)) ≤ (Int8.toInt32 (t'30)))) then
        Functor'void_const_char_const_signed_char.operator__'at'AP_BattMonitor'_battery_failsafe_handler_fn (this + 1496) type_str action
        PMem.stI8 (this + 1520) priority
  return ()

def AP_BattMonitor.check_failsafes (this : UInt64) : PMem.M Unit := do
  let fp ← PMem.enter 32
  let r ← AP_BattMonitor.check_failsafes.body fp this
  PMem.leave fp
  return r

/-- C++ `AP_BattMonitor::read : void ()`, `AP_BattMonitor.cpp:777-822`. -/
def AP_BattMonitor.read (this : UInt64) : PMem.M Unit := do
  let mut now_ms : UInt32 := ((← PMem.clock) / 1000).toUInt32
  let mut i : UInt8 := Int8.toUInt8 (Int32.toInt8 ((0 : Int32)))
  let mut first'1 := true
  for _ in PMem.loopFuel do
    if !first'1 then
      let t'2 := i
      let t'3 := (t'2 + 1)
      i := t'3
      pure ()
    first'1 := false
    let t'4 ← PMem.ldU8 (this + 1492)
    if !((decide ((UInt32.toInt32 (UInt8.toUInt32 (i))) < (UInt32.toInt32 (UInt8.toUInt32 (t'4)))))) then break
    let t'5 ← PMem.ldU64 ((this + 1416) + ((UInt64.toInt64 (UInt8.toUInt64 (i))) * 8).toUInt64)
    if (t'5 == (0 : UInt64)) then
      continue
    let t'6 ← AP_BattMonitor.allocated_type this i
    let t'7 ← AP_BattMonitor.configured_type this i
    if (t'6 != t'7) then
      continue
    let t'8 ← AP_BattMonitor.configured_type this i
    if (t'8 == (0 : Int32)) then
      continue
    let t'9 ← PMem.ldU64 ((this + 1416) + ((UInt64.toInt64 (UInt8.toUInt64 (i))) * 8).toUInt64)
    AP_BattMonitor_Analog.read t'9
    let t'10 ← PMem.ldU64 ((this + 1416) + ((UInt64.toInt64 (UInt8.toUInt64 (i))) * 8).toUInt64)
    AP_BattMonitor_Backend.update_resistance_estimate t'10
    let t'11 ← PMem.ldB (((this + 408) + ((UInt64.toInt64 (UInt8.toUInt64 (i))) * 112).toUInt64) + 73)
    if t'11 then
      PMem.stU32 (((this + 408) + ((UInt64.toInt64 (UInt8.toUInt64 (i))) * 112).toUInt64) + 76) now_ms
  AP_BattMonitor.check_failsafes this
  AP_BattMonitor.checkPoweringOff this
  return ()

/-- C++ `RC_Channel::read_aux : bool ()`, `RC_Channel.cpp:997-1043`. -/
def RC_Channel.read_aux.body (fp : UInt64) (this : UInt64) : PMem.M Bool := do
  let t'1 ← AP_ParamTBase'short_2.get (this + 8)
  let t'2 ← PMem.ldI16 t'1
  let mut _option : Int32 := Int16.toInt32 (t'2)
  if (_option == (0 : Int32)) then
    return false
  let t'3 ← RC_Channel.read_3pos_switch this (fp + 0)
  if !t'3 then
    return false
  let t'4 ← PMem.ldB ((this + 40) + 8)
  if !t'4 then
    PMem.stB ((this + 40) + 8) true
    let t'5 ← AP_ParamTBase'short_2.get (this + 8)
    let t'6 ← PMem.ldI16 t'5
    let t'7 ← RC_Channel.init_position_on_first_radio_read this (Int16.toInt32 (t'6))
    if t'7 then
      let t'8 ← PMem.ldU8 (fp + 0)
      let t'9 := UInt8.toInt8 (t'8)
      PMem.stI8 ((this + 40) + 1) t'9
      let t'10 ← PMem.ldU8 (fp + 0)
      let t'11 := UInt8.toInt8 (t'10)
      PMem.stI8 (this + 40) t'11
  let t'12 ← PMem.ldU8 (fp + 0)
  let t'13 ← RC_Channel.debounce_completed this (UInt8.toInt8 (t'12))
  if !t'13 then
    return false
  let t'14 ← RC_Channel.string_for_aux_function this _option
  let mut aux_string : UInt64 := t'14
  if (aux_string != (0 : UInt64)) then
    let t'15 ← PMem.ldU8 (this + 10)
    PMem.stU64 (fp + 8) (Int64.toUInt64 (Int32.toInt64 (((UInt32.toInt32 (UInt8.toUInt32 (t'15))) + (1 : Int32)))))
    PMem.stU64 (fp + 16) aux_string
    let t'16 ← PMem.ldU8 (fp + 0)
    let t'17 ← RC_Channel.string_for_aux_pos this t'16
    PMem.stU64 (fp + 24) t'17
    let t'18 ← gcs
    GCS.send_text t'18 (6 : UInt32) (0x18e52 : UInt64) /- "RC%i: %s %s" -/ (fp + 8)
  let t'19 ← PMem.ldU8 (fp + 0)
  let t'20 ← PMem.ldU8 (this + 10)
  let t'21 ← RC_Channel.run_aux_function this _option t'19 (1 : UInt8) (UInt8.toUInt16 (t'20))
  discard <| pure (t'21)
  return true

def RC_Channel.read_aux (this : UInt64) : PMem.M Bool := do
  let fp ← PMem.enter 32
  let r ← RC_Channel.read_aux.body fp this
  PMem.leave fp
  return r

/-- C++ `RC_Channels::read_aux_all : void ()`, `RC_Channels.cpp:219-240`. -/
def RC_Channels.read_aux_all (this : UInt64) : PMem.M Unit := do
  let t'1 ← RC_Channels_Copter.has_valid_input this
  if !t'1 then
    return ()
  let mut need_log : Bool := false
  for i'2 in [0:16] do
    let i : UInt8 := UInt8.ofNat i'2
    let t'3 ← RC_Channels_Copter.channel this i
    let mut c : UInt64 := t'3
    if (c == (0 : UInt64)) then
      continue
    let t'4 ← RC_Channel.read_aux c
    let t'5 := (need_log || ((if t'4 then (1 : Int32) else (0 : Int32)) != (0 : Int32)))
    need_log := t'5
  return ()

/-- C++ `Functor<void>::method_wrapper : void (void *)`, `functor.h:85-89`. -/
def Functor'void.method_wrapper'Copter_auto_disarm_check (obj : UInt64) : PMem.M Unit := do
  let mut obj := obj
  let mut t : UInt64 := obj
  Copter.auto_disarm_check t
  return ()

/-- C++ `Functor<void>::method_wrapper : void (void *)`, `functor.h:85-89`. -/
def Functor'void.method_wrapper'Copter_update_altitude (obj : UInt64) : PMem.M Unit := do
  let mut obj := obj
  let mut t : UInt64 := obj
  Copter.update_altitude t
  return ()

/-- C++ `Functor<void>::method_wrapper : void (void *)`, `functor.h:85-89`. -/
def Functor'void.method_wrapper'Copter_run_nav_updates (obj : UInt64) : PMem.M Unit := do
  let mut obj := obj
  let mut t : UInt64 := obj
  Copter.run_nav_updates t
  return ()

/-- C++ `Functor<void>::method_wrapper : void (void *)`, `functor.h:85-89`. -/
def Functor'void.method_wrapper'Copter_update_throttle_hover (obj : UInt64) : PMem.M Unit := do
  let mut obj := obj
  let mut t : UInt64 := obj
  Copter.update_throttle_hover t
  return ()

/-- C++ `Copter::failsafe_gcs_on_event : void ()`, `events.cpp:163-233`. -/
def Copter.failsafe_gcs_on_event (this : UInt64) : PMem.M Unit := do
  RC_Channels.clear_overrides
  let mut desired_action : UInt8 := default  -- uninitialized in C
  let t'1 ← AP_Enum'Parameters_FS_GCS_Action.operator_const_Parameters.FS_GCS_Action ((this + 6776) + 21)
  let sw'2 := t'1
  if sw'2 == (0 : Int32) then
    desired_action := (0 : UInt8)
  else if sw'2 == (1 : Int32) || sw'2 == (2 : Int32) then
    desired_action := (2 : UInt8)
  else if sw'2 == (3 : Int32) then
    desired_action := (3 : UInt8)
  else if sw'2 == (4 : Int32) then
    desired_action := (4 : UInt8)
  else if sw'2 == (5 : Int32) then
    desired_action := (1 : UInt8)
  else if sw'2 == (6 : Int32) then
    desired_action := (6 : UInt8)
  else if sw'2 == (7 : Int32) then
    desired_action := (7 : UInt8)
  else
    desired_action := (2 : UInt8)
  let t'3 ← PMem.ldU64 (this + 9528)
  let t'4 ← AP_Motors.armed t'3
  if !t'4 then
    desired_action := (0 : UInt8)
    Copter.announce_failsafe this (0x14713 : UInt64) /- "GCS" -/ (0 : UInt64)
  else
    let t'5 ← Copter.should_disarm_on_failsafe this
    if t'5 then
      let t'6 ← AP_Arming_Copter.disarm (this + 8768) (18 : Int32) true
      discard <| pure (t'6)
      desired_action := (0 : UInt8)
      Copter.announce_failsafe this (0x14713 : UInt64) /- "GCS" -/ (0x14683 : UInt64) /- "Disarming" -/
    else
      let t'7 ← PMem.ldU64 (this + 9488)
      let t'8 ← vcall'Mode'is_landing'15 t'7
      let mut sc'12 := t'8
      if sc'12 then
        let t'9 ← AP_BattMonitor.has_failsafed (this + 9584)
        let mut sc'11 := t'9
        if sc'11 then
          let t'10 ← AP_BattMonitor.get_highest_failsafe_priority (this + 9584)
          sc'11 := (decide ((Int8.toInt32 (t'10)) ≤ (1 : Int32)))
        sc'12 := sc'11
      if sc'12 then
        Copter.announce_failsafe this (0x14717 : UInt64) /- "GCS + Battery" -/ (0x1469d : UInt64) /- "Continuing Landing" -/
        desired_action := (1 : UInt8)
      else
        let t'13 ← PMem.ldU64 (this + 9488)
        let t'14 ← vcall'Mode'is_landing'15 t'13
        let mut sc'16 := t'14
        if sc'16 then
          let t'15 ← Copter.failsafe_option this (8 : Int32)
          sc'16 := t'15
        if sc'16 then
          Copter.announce_failsafe this (0x14713 : UInt64) /- "GCS" -/ (0x1469d : UInt64) /- "Continuing Landing" -/
          desired_action := (1 : UInt8)
        else
          let t'17 ← PMem.ldU64 (this + 9488)
          let t'18 ← vcall'Mode'mode_number'1 t'17
          let mut sc'20 := (t'18 == (3 : UInt8))
          if sc'20 then
            let t'19 ← Copter.failsafe_option this (2 : Int32)
            sc'20 := t'19
          if sc'20 then
            Copter.announce_failsafe this (0x14713 : UInt64) /- "GCS" -/ (0x14725 : UInt64) /- "Continuing Auto Mode" -/
            desired_action := (0 : UInt8)
          else
            let t'21 ← Copter.failsafe_option this (16 : Int32)
            let mut sc'24 := t'21
            if sc'24 then
              let t'22 ← PMem.ldU64 (this + 9488)
              let t'23 ← vcall'Mode'is_autopilot'0 t'22
              sc'24 := !t'23
            if sc'24 then
              Copter.announce_failsafe this (0x14713 : UInt64) /- "GCS" -/ (0x1473a : UInt64) /- "Continuing Pilot Control" -/
              desired_action := (0 : UInt8)
            else
              Copter.announce_failsafe this (0x14713 : UInt64) /- "GCS" -/ (0 : UInt64)
  Copter.do_failsafe_action this desired_action (5 : UInt8)
  return ()

/-- C++ `Copter::failsafe_gcs_check : void ()`, `events.cpp:126-160`. -/
def Copter.failsafe_gcs_check (this : UInt64) : PMem.M Unit := do
  let t'1 ← AP_Enum'Parameters_FS_GCS_Action.operator_const_Parameters.FS_GCS_Action ((this + 6776) + 21)
  if (t'1 == (0 : Int32)) then
    return ()
  let t'2 ← Copter.gcs this
  let t'3 ← GCS.sysid_mygcs_last_seen_time_ms t'2
  let mut gcs_last_seen_ms : UInt32 := t'3
  if (gcs_last_seen_ms == (Int32.toUInt32 ((0 : Int32)))) then
    return ()
  let mut last_gcs_update_ms : UInt32 := ((((← PMem.clock) / 1000).toUInt32) - gcs_last_seen_ms)
  let t'4 ← AP_ParamT'float_4.operator_const_float__'1 ((this + 6840) + 1688)
  let t'5 ← PMem.ldF32 t'4
  let t'6 ← constrain_value_line'float (t'5 * (Binary32.ofBits 0x447a0000 /- 1000 -/)) (Binary32.ofBits 0x00000000 /- 0 -/) (UInt32.toBinary32 ((4294967295 : UInt32))) (Int32.toUInt32 ((141 : Int32)))
  let mut gcs_timeout_ms : UInt32 := Binary32.toUInt32 (t'6)
  let mut sc'8 := (decide (last_gcs_update_ms < gcs_timeout_ms))
  if sc'8 then
    let t'7 ← PMem.ldBits (this + 9508) 73 1
    sc'8 := (UInt64.toUInt8 (t'7)) != (0 : UInt8)
  if sc'8 then
    Copter.set_failsafe_gcs this false
    Copter.failsafe_gcs_off_event this
  else
    let mut sc'10 := (decide (last_gcs_update_ms < gcs_timeout_ms))
    if sc'10 then
      let t'9 ← PMem.ldBits (this + 9508) 73 1
      sc'10 := !((UInt64.toUInt8 (t'9)) != (0 : UInt8))
    if sc'10 then
      pure ()
    else
      let mut sc'12 := (decide (last_gcs_update_ms > gcs_timeout_ms))
      if sc'12 then
        let t'11 ← PMem.ldBits (this + 9508) 73 1
        sc'12 := (UInt64.toUInt8 (t'11)) != (0 : UInt8)
      if sc'12 then
        pure ()
      else
        let mut sc'14 := (decide (last_gcs_update_ms > gcs_timeout_ms))
        if sc'14 then
          let t'13 ← PMem.ldBits (this + 9508) 73 1
          sc'14 := !((UInt64.toUInt8 (t'13)) != (0 : UInt8))
        if sc'14 then
          Copter.set_failsafe_gcs this true
          Copter.failsafe_gcs_on_event this
  return ()

/-- C++ `Copter::failsafe_terrain_check : void ()`, `events.cpp:243-258`. -/
def Copter.failsafe_terrain_check (this : UInt64) : PMem.M Unit := do
  let t'1 ← PMem.ldU32 ((this + 9508) + 4)
  let t'2 ← PMem.ldU32 (this + 9508)
  let mut timeout : Bool := (decide ((t'1 - t'2) > (Int32.toUInt32 ((5000 : Int32)))))
  let mut sc'5 := timeout
  if sc'5 then
    let t'3 ← PMem.ldU64 (this + 9488)
    let t'4 ← vcall'Mode'requires_terrain_failsafe'32 t'3
    sc'5 := t'4
  let mut trigger_event : Bool := sc'5
  let t'6 ← PMem.ldBits (this + 9508) 75 1
  if ((if trigger_event then (1 : Int32) else (0 : Int32)) != (UInt32.toInt32 (UInt8.toUInt32 ((UInt64.toUInt8 (t'6)))))) then
    if trigger_event then
      Copter.failsafe_terrain_on_event this
    else
      let t'7 := if false then (1 : UInt8) else (0 : UInt8)
      PMem.stBits (this + 9508) 75 1 (UInt8.toUInt64 (t'7))
  return ()

/-- C++ `Copter::failsafe_deadreckon_check : void ()`, `events.cpp:328-385`. -/
def Copter.failsafe_deadreckon_check.body (fp : UInt64) (this : UInt64) : PMem.M Unit := do
  let mut dr_prefix_str : UInt64 := (0x147d7 : UInt64) /- "Dead Reckoning" -/
  let t'1 ← VehicleBridge.ahrs'0
  let t'2 ← VehicleBridge.AP_AHRS.configured_backend_has_status'1 t'1 (262144 : Int32)
  let mut ekf_dead_reckoning : Bool := t'2
  let mut now_ms : UInt32 := ((← PMem.clock) / 1000).toUInt32
  let t'3 ← PMem.ldB (this + 9520)
  if ((if t'3 then (1 : Int32) else (0 : Int32)) != (if ekf_dead_reckoning then (1 : Int32) else (0 : Int32))) then
    PMem.stB (this + 9520) ekf_dead_reckoning
    let t'4 ← PMem.ldB (this + 9520)
    if t'4 then
      PMem.stU32 ((this + 9520) + 4) now_ms
      PMem.stU64 (fp + 0) dr_prefix_str
      let t'5 ← Copter.gcs this
      GCS.send_text t'5 (2 : UInt32) (0x147e6 : UInt64) /- "%s started" -/ (fp + 0)
    else
      let t'6 := Int32.toUInt32 ((0 : Int32))
      PMem.stU32 ((this + 9520) + 4) t'6
      PMem.stB ((this + 9520) + 1) false
      PMem.stU64 (fp + 8) dr_prefix_str
      let t'7 ← Copter.gcs this
      GCS.send_text t'7 (2 : UInt32) (0x147f1 : UInt64) /- "%s stopped" -/ (fp + 8)
  let t'8 ← PMem.ldB (this + 9520)
  let mut sc'10 := t'8
  if sc'10 then
    let t'9 ← PMem.ldB ((this + 9520) + 1)
    sc'10 := !t'9
  if sc'10 then
    let t'11 ← AP_ParamT'short_2.operator_const_short__ ((this + 6840) + 1706)
    let t'12 ← PMem.ldI16 t'11
    let t'13 ← constrain_value_line'float ((Int32.toBinary32 ((Int16.toInt32 (t'12)))) * (Binary32.ofBits 0x447a0000 /- 1000 -/)) (Binary32.ofBits 0x00000000 /- 0 -/) (UInt32.toBinary32 ((4294967295 : UInt32))) (Int32.toUInt32 ((352 : Int32)))
    let mut dr_timeout_ms : UInt32 := Binary32.toUInt32 (t'13)
    let t'14 ← PMem.ldU32 ((this + 9520) + 4)
    if (decide ((now_ms - t'14) > dr_timeout_ms)) then
      PMem.stB ((this + 9520) + 1) true
      PMem.stU64 (fp + 16) dr_prefix_str
      let t'15 ← Copter.gcs this
      GCS.send_text t'15 (2 : UInt32) (0x147fc : UInt64) /- "%s timeout" -/ (fp + 16)
  let t'16 ← AP_ParamT'signed_char_1.operator_const_signed_char__ ((this + 6840) + 1705)
  let t'17 ← PMem.ldI8 t'16
  if (decide ((Int8.toInt32 (t'17)) ≤ (0 : Int32))) then
    let t'18 := if false then (1 : UInt8) else (0 : UInt8)
    PMem.stBits (this + 9508) 77 1 (UInt8.toUInt64 (t'18))
    return ()
  let t'19 ← PMem.ldBits (this + 9508) 77 1
  if ((UInt32.toInt32 (UInt8.toUInt32 ((UInt64.toUInt8 (t'19))))) != (if ekf_dead_reckoning then (1 : Int32) else (0 : Int32))) then
    let t'20 := if ekf_dead_reckoning then (1 : UInt8) else (0 : UInt8)
    PMem.stBits (this + 9508) 77 1 (UInt8.toUInt64 (t'20))
    let t'21 ← PMem.ldBits (this + 9508) 77 1
    let mut sc'24 := (UInt64.toUInt8 (t'21)) != (0 : UInt8)
    if sc'24 then
      let t'22 ← PMem.ldU64 ((0x86d8 : UInt64) /- &copter -/ + 9488)
      let t'23 ← vcall'Mode'requires_position'5 t'22
      sc'24 := t'23
    if sc'24 then
      let t'25 ← Copter.should_disarm_on_failsafe this
      if t'25 then
        let t'26 ← AP_Arming_Copter.disarm (this + 8768) (33 : Int32) true
        discard <| pure (t'26)
        return ()
      let t'27 ← AP_ParamTBase'signed_char_1.get ((this + 6840) + 1705)
      let t'28 ← PMem.ldI8 t'27
      Copter.do_failsafe_action this (Int8.toUInt8 (t'28)) (50 : UInt8)
  return ()

def Copter.failsafe_deadreckon_check (this : UInt64) : PMem.M Unit := do
  let fp ← PMem.enter 24
  let r ← Copter.failsafe_deadreckon_check.body fp this
  PMem.leave fp
  return r

/-- C++ `Copter::three_hz_loop : void ()`, `Copter.cpp:741-759`. -/
def Copter.three_hz_loop (this : UInt64) : PMem.M Unit := do
  Copter.failsafe_gcs_check this
  Copter.failsafe_terrain_check this
  Copter.failsafe_deadreckon_check this
  Copter.low_alt_avoidance this
  return ()

/-- C++ `Functor<void>::method_wrapper : void (void *)`, `functor.h:85-89`. -/
def Functor'void.method_wrapper'Copter_three_hz_loop (obj : UInt64) : PMem.M Unit := do
  let mut obj := obj
  let mut t : UInt64 := obj
  Copter.three_hz_loop t
  return ()

/-- C++ `Functor<void>::method_wrapper : void (void *)`, `functor.h:85-89`. -/
def Functor'void.method_wrapper'Copter_one_hz_loop (obj : UInt64) : PMem.M Unit := do
  let mut obj := obj
  let mut t : UInt64 := obj
  Copter.one_hz_loop t
  return ()

/-- C++ `Copter::ekf_check : void ()`, `ekf_check.cpp:30-111`. -/
def Copter.ekf_check.body (fp : UInt64) (this : UInt64) : PMem.M Unit := do
  Location.Location (fp + 0)
  let t'1 ← VehicleBridge.AP_AHRS.get_origin'1 (this + 4080) (fp + 0)
  if !t'1 then
    return ()
  let t'2 ← AP_ParamT'float_4.operator_const_float__'1 ((this + 6776) + 56)
  let t'3 ← PMem.ldF32 t'2
  if (decide (t'3 ≤ (Binary32.ofBits 0x00000000 /- 0 -/))) then
    let t'4 := Int8.toUInt8 (Int32.toInt8 ((0 : Int32)))
    PMem.stU8 (0x134c8 : UInt64) /- &ekf_check_state -/ t'4
    PMem.stB ((0x134c8 : UInt64) /- &ekf_check_state -/ + 1) false
    let t'5 ← PMem.ldB ((0x134c8 : UInt64) /- &ekf_check_state -/ + 1)
    PMem.stB ((0xccc0 : UInt64) /- &AP_Notify::flags -/ + 15) t'5
    Copter.failsafe_ekf_off_event this
    return ()
  let t'6 ← Copter.ekf_over_threshold this
  let mut over_threshold : Bool := t'6
  let t'7 ← Copter.ekf_has_relative_position this
  let mut sc'9 := t'7
  if !sc'9 then
    let t'8 ← Copter.ekf_has_absolute_position this
    sc'9 := t'8
  let mut has_position : Bool := sc'9
  let mut checks_passed : Bool := ((!over_threshold) && has_position)
  let t'10 := ((0x134c8 : UInt64) /- &ekf_check_state -/ + 2)
  let t'11 ← PMem.ldB t'10
  let t'12 := (t'11 || ((if checks_passed then (1 : Int32) else (0 : Int32)) != (0 : Int32)))
  PMem.stB t'10 t'12
  let t'13 ← PMem.ldB ((0x134c8 : UInt64) /- &ekf_check_state -/ + 2)
  if !t'13 then
    return ()
  if !checks_passed then
    let t'14 ← PMem.ldB ((0x134c8 : UInt64) /- &ekf_check_state -/ + 1)
    if !t'14 then
      let t'15 := (0x134c8 : UInt64) /- &ekf_check_state -/
      let t'16 ← PMem.ldU8 t'15
      let t'17 := (t'16 + 1)
      PMem.stU8 t'15 t'17
      let t'18 ← PMem.ldU8 (0x134c8 : UInt64) /- &ekf_check_state -/
      if (((UInt32.toInt32 (UInt8.toUInt32 (t'18))) == ((10 : Int32) - (2 : Int32))) && over_threshold) then
        VehicleBridge.AP_AHRS.request_yaw_reset'0 (this + 4080)
      let t'19 ← PMem.ldU8 (0x134c8 : UInt64) /- &ekf_check_state -/
      if ((UInt32.toInt32 (UInt8.toUInt32 (t'19))) == ((10 : Int32) - (1 : Int32))) then
        VehicleBridge.AP_AHRS.check_lane_switch'0 (this + 4080)
        worldOutputs'drain
      let t'20 ← PMem.ldU8 (0x134c8 : UInt64) /- &ekf_check_state -/
      if (decide ((UInt32.toInt32 (UInt8.toUInt32 (t'20))) ≥ (10 : Int32))) then
        let t'21 := Int8.toUInt8 (Int32.toInt8 ((10 : Int32)))
        PMem.stU8 (0x134c8 : UInt64) /- &ekf_check_state -/ t'21
        PMem.stB ((0x134c8 : UInt64) /- &ekf_check_state -/ + 1) true
        let t'22 ← PMem.ldU32 ((0x134c8 : UInt64) /- &ekf_check_state -/ + 4)
        if (decide (((((← PMem.clock) / 1000).toUInt32) - t'22) > (Int32.toUInt32 (((30 : Int32) * (1000 : Int32)))))) then
          let mut c'23 : UInt64 := default
          if over_threshold then
            c'23 := (0x14552 : UInt64) /- "over thresholds" -/
          else
            c'23 := (0x14562 : UInt64) /- "position lost" -/
          PMem.stU64 (fp + 16) c'23
          let t'24 ← Copter.gcs this
          GCS.send_text t'24 (2 : UInt32) (0x14541 : UInt64) /- "EKF variance: %s" -/ (fp + 16)
          let t'25 := ((← PMem.clock) / 1000).toUInt32
          PMem.stU32 ((0x134c8 : UInt64) /- &ekf_check_state -/ + 4) t'25
        Copter.failsafe_ekf_event this
  else
    let t'26 ← PMem.ldU8 (0x134c8 : UInt64) /- &ekf_check_state -/
    if (decide ((UInt32.toInt32 (UInt8.toUInt32 (t'26))) > (0 : Int32))) then
      let t'27 := (0x134c8 : UInt64) /- &ekf_check_state -/
      let t'28 ← PMem.ldU8 t'27
      let t'29 := (t'28 - 1)
      PMem.stU8 t'27 t'29
      let t'30 ← PMem.ldB ((0x134c8 : UInt64) /- &ekf_check_state -/ + 1)
      let mut sc'32 := t'30
      if sc'32 then
        let t'31 ← PMem.ldU8 (0x134c8 : UInt64) /- &ekf_check_state -/
        sc'32 := ((UInt32.toInt32 (UInt8.toUInt32 (t'31))) == (0 : Int32))
      if sc'32 then
        PMem.stB ((0x134c8 : UInt64) /- &ekf_check_state -/ + 1) false
        Copter.failsafe_ekf_off_event this
  let t'33 ← PMem.ldB ((0x134c8 : UInt64) /- &ekf_check_state -/ + 1)
  PMem.stB ((0xccc0 : UInt64) /- &AP_Notify::flags -/ + 15) t'33
  return ()

def Copter.ekf_check (this : UInt64) : PMem.M Unit := do
  let fp ← PMem.enter 24
  let r ← Copter.ekf_check.body fp this
  PMem.leave fp
  return r

/-- C++ `Functor<void>::method_wrapper : void (void *)`, `functor.h:85-89`. -/
def Functor'void.method_wrapper'Copter_ekf_check (obj : UInt64) : PMem.M Unit := do
  let mut obj := obj
  let mut t : UInt64 := obj
  Copter.ekf_check t
  return ()

/-- C++ `Functor<void>::method_wrapper : void (void *)`, `functor.h:85-89`. -/
def Functor'void.method_wrapper'Copter_check_vibration (obj : UInt64) : PMem.M Unit := do
  let mut obj := obj
  let mut t : UInt64 := obj
  Copter.check_vibration t
  return ()

/-- C++ `Functor<void>::method_wrapper : void (void *)`, `functor.h:85-89`. -/
def Functor'void.method_wrapper'Copter_gpsglitch_check (obj : UInt64) : PMem.M Unit := do
  let mut obj := obj
  let mut t : UInt64 := obj
  Copter.gpsglitch_check t
  return ()

/-- C++ `Functor<void>::method_wrapper : void (void *)`, `functor.h:85-89`. -/
def Functor'void.method_wrapper'Copter_takeoff_check (obj : UInt64) : PMem.M Unit := do
  let mut obj := obj
  let mut t : UInt64 := obj
  Copter.takeoff_check t
  return ()

/-- C++ `Functor<void>::method_wrapper : void (void *)`, `functor.h:85-89`. -/
def Functor'void.method_wrapper'Copter_lost_vehicle_check (obj : UInt64) : PMem.M Unit := do
  let mut obj := obj
  let mut t : UInt64 := obj
  Copter.lost_vehicle_check t
  return ()

/-- C++ `Functor<void>::method_wrapper : void (void *)`, `functor.h:85-89`. -/
def Functor'void.method_wrapper'GCS_update_send (obj : UInt64) : PMem.M Unit := do
  let mut obj := obj
  let mut t : UInt64 := obj
  GCS.update_send t
  return ()

/-- C++ `failsafe_check_static : void ()`, `system.cpp:11-14`. -/
def failsafe_check_static  : PMem.M Unit := do
  Copter.failsafe_check (0x86d8 : UInt64) /- &copter -/
  return ()

/-- Calls through a function pointer of type `bool (void *, const AP_Mission::Mission_Command &)`: the functions whose address the program takes with this type (0). -/
def fnptr'3 (f : UInt64) (a0 : UInt64) (a1 : UInt64) : PMem.M Bool := do
  if f == 0x7e000070 then  -- ModeAuto::start_command (FUNCTOR_BIND_MEMBER)
    ModeAuto.start_command a0 a1
  else if f == 0x7e000080 then  -- ModeAuto::verify_command (FUNCTOR_BIND_MEMBER)
    ModeAuto.verify_command a0 a1
  else
    PMem.unreached "function pointer bool (void *, const AP_Mission::Mission_Command &)"
    return default

/-- C++ `Functor<bool, const AP_Mission::Mission_Command &>::operator() : bool (const AP_Mission::Mission_Command &) const`, `functor.h:52-55`. -/
def Functor'bool_const_AP_Mission_Mission_Command.operator__ (this : UInt64) (args : UInt64) : PMem.M Bool := do
  let t'1 ← PMem.ldU64 (this + 8)
  let t'2 ← PMem.ldU64 this
  let t'3 ← fnptr'3 t'1 t'2 args
  return t'3

/-- Calls through a function pointer of type `void (void *, const char *, const signed char)`: the functions whose address the program takes with this type (0). -/
def fnptr'4 (f : UInt64) (a0 : UInt64) (a1 : UInt64) (a2 : Int8) : PMem.M Unit := do
  if f == 0x7e000060 then  -- Copter::handle_battery_failsafe (FUNCTOR_BIND_MEMBER)
    Copter.handle_battery_failsafe a0 a1 a2
  else
    PMem.unreached "function pointer void (void *, const char *, const signed char)"
    return ()

/-- C++ `Functor<void, const char *, const signed char>::operator() : void (const char *, const signed char) const`, `functor.h:52-55`. -/
def Functor'void_const_char_const_signed_char.operator__ (this : UInt64) (args : UInt64) (args'2 : Int8) : PMem.M Unit := do
  let mut args := args
  let mut args'2 := args'2
  let t'1 ← PMem.ldU64 (this + 8)
  let t'2 ← PMem.ldU64 this
  fnptr'4 t'1 t'2 args args'2
  return ()

end Vehicle_lib
