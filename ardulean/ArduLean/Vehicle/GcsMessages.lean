import ArduLean.Runtime.Bridge
import ArduLean.Vehicle.libraries.Filter.Filter
import ArduLean.Vehicle.libraries.AP_Param.AP_Param
import ArduLean.Vehicle.libraries.AC_AttitudeControl.AC_AttitudeControl
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
import ArduLean.Vehicle.libraries.AP_Scheduler.AP_Scheduler
import ArduLean.Vehicle.libraries.SRV_Channel.SRV_Channel
import ArduLean.Vehicle.libraries.AP_GPS.AP_GPS
import ArduLean.Vehicle.libraries.AC_AttitudeControl.AC_AttitudeControl_2
import ArduLean.Vehicle.libraries.AP_Arming.AP_Arming_2
import ArduLean.Vehicle.ArduCopter.ArduCopter_2
import ArduLean.Vehicle.libraries.AP_SerialManager.AP_SerialManager
import ArduLean.Vehicle.libraries.AP_Motors.AP_Motors_2
import ArduLean.Vehicle.libraries.GCS_MAVLink.GCS_MAVLink_2
import ArduLean.Vehicle.libraries.AP_Vehicle.AP_Vehicle_2
import ArduLean.Vehicle.libraries.AP_Mission.AP_Mission_3
import ArduLean.Vehicle.World
import ArduLean.Vehicle.libraries.AP_BoardConfig.AP_BoardConfig_2
import ArduLean.Vehicle.ArduCopter.ArduCopter_3
import ArduLean.Vehicle.libraries.GCS_MAVLink.GCS_MAVLink_3
import ArduLean.Vehicle.Arming
import ArduLean.Vehicle.ModeSwitching

/-!
Cross-library module `GcsMessages`: GCS message handling: GCS_MAVLINK::handle_message with GCS_MAVLINK_Copter's overrides, COMMAND_LONG and COMMAND_INT, update_receive; and the vehicle's setup (Copter::init_ardupilot, AP_Vehicle::setup). It belongs to the top of the call graph, where ArduPilot's libraries call each other in a cycle, so it cannot be cut by library. Largest functions: `GCS_MAVLINK.update_receive`, `GCS_MAVLINK.handle_message`, `GCS_MAVLINK_Copter.handle_command_int_packet`, `Copter.init_ardupilot`, `AP_Vehicle.setup`, `GCS_MAVLINK.handle_command_int`, `GCS_MAVLINK.handle_command_long`, `GCS_MAVLINK.try_command_long_as_command_int`, `Copter.update_flight_mode`, `GCS.update_receive`. Sources: `libraries/GCS_MAVLink/GCS_Common.cpp`, `ArduCopter/GCS_MAVLink_Copter.cpp`, `libraries/AP_Vehicle/AP_Vehicle.cpp`, `ArduCopter/system.cpp`, `libraries/RC_Channel/RC_Channels.cpp`, `ArduCopter/mode.cpp`, `libraries/RC_Channel/RC_Channel.cpp`, `ArduCopter/Copter.cpp`.

Items of `lean/Vehicle_lib.lean` (the vehicle translation), unchanged; placed by `tools/split_modules.py` (`ArduLean/Vehicle/INDEX.md`).
-/

open FloatLib.Floats (Binary32 Binary64)

set_option linter.unusedVariables false
set_option linter.unreachableTactic false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false

namespace Vehicle_lib

/-- C++ `GCS_MAVLINK_Copter::handle_command_int_packet : MAV_RESULT (const mavlink_command_int_t &, const mavlink_message_t &)`, `GCS_MAVLink_Copter.cpp:470-557`. -/
def GCS_MAVLINK_Copter.handle_command_int_packet (this : UInt64) (packet : UInt64) (msg : UInt64) : PMem.M UInt32 := do
  let t'1 ← PMem.ldU16 (packet + 28)
  let sw'2 := UInt32.toInt32 (UInt16.toUInt32 (t'1))
  if sw'2 == (115 : Int32) then
    let t'3 ← GCS_MAVLINK_Copter.handle_MAV_CMD_CONDITION_YAW this packet
    return t'3
  else if sw'2 == (178 : Int32) then
    let t'4 ← GCS_MAVLINK_Copter.handle_MAV_CMD_DO_CHANGE_SPEED this packet
    return t'4
  else if sw'2 == (192 : Int32) then
    let t'5 ← GCS_MAVLINK_Copter.handle_command_int_do_reposition this packet
    return t'5
  else if sw'2 == (193 : Int32) then
    let t'6 ← GCS_MAVLINK_Copter.handle_command_pause_continue this packet
    return t'6
  else if sw'2 == (209 : Int32) then
    PMem.unreached "GCS_MAVLINK_Copter::handle_MAV_CMD_DO_MOTOR_TEST"
    return (default : UInt32)
  else if sw'2 == (22 : Int32) || sw'2 == (84 : Int32) then
    let t'7 ← GCS_MAVLINK_Copter.handle_MAV_CMD_NAV_TAKEOFF this packet
    return t'7
  else if sw'2 == (42003 : Int32) then
    PMem.unreached "GCS_MAVLINK_Copter::handle_MAV_CMD_SOLO_BTN_PAUSE_CLICK"
    return (default : UInt32)
  else if sw'2 == (42002 : Int32) then
    PMem.unreached "GCS_MAVLINK_Copter::handle_MAV_CMD_SOLO_BTN_FLY_HOLD"
    return (default : UInt32)
  else if sw'2 == (42001 : Int32) then
    PMem.unreached "GCS_MAVLINK_Copter::handle_MAV_CMD_SOLO_BTN_FLY_CLICK"
    return (default : UInt32)
  else if sw'2 == (300 : Int32) then
    let t'8 ← GCS_MAVLINK_Copter.handle_MAV_CMD_MISSION_START this packet
    return t'8
  else if sw'2 == (17 : Int32) then
    let t'9 ← Copter.set_mode (0x86d8 : UInt64) /- &copter -/ (5 : UInt8) (2 : UInt8)
    if !t'9 then
      return (4 : UInt32)
    return (0 : UInt32)
  else if sw'2 == (20 : Int32) then
    let t'10 ← Copter.set_mode (0x86d8 : UInt64) /- &copter -/ (6 : UInt8) (2 : UInt8)
    if !t'10 then
      return (4 : UInt32)
    return (0 : UInt32)
  else if sw'2 == (85 : Int32) || sw'2 == (21 : Int32) then
    let t'11 ← Copter.set_mode (0x86d8 : UInt64) /- &copter -/ (9 : UInt8) (2 : UInt8)
    if !t'11 then
      return (4 : UInt32)
    return (0 : UInt32)
  else if sw'2 == (188 : Int32) then
    let t'12 ← ModeAuto.return_path_start_auto_RTL ((0x86d8 : UInt64) /- &copter -/ + 11368) (2 : UInt8)
    if t'12 then
      return (0 : UInt32)
    return (4 : UInt32)
  else if sw'2 == (189 : Int32) then
    let t'13 ← ModeAuto.jump_to_landing_sequence_auto_RTL ((0x86d8 : UInt64) /- &copter -/ + 11368) (2 : UInt8)
    if t'13 then
      return (0 : UInt32)
    return (4 : UInt32)
  else
    let t'14 ← GCS_MAVLINK.handle_command_int_packet this packet msg
    return t'14

/-- C++ `GCS_MAVLINK::try_command_long_as_command_int : MAV_RESULT (const mavlink_command_long_t &, const mavlink_message_t &)`, `GCS_Common.cpp:5301-5331`. -/
def GCS_MAVLINK.try_command_long_as_command_int.body (fp : UInt64) (this : UInt64) (packet : UInt64) (msg : UInt64) : PMem.M UInt32 := do
  let t'1 ← PMem.ldU16 (packet + 28)
  let t'2 ← GCS_MAVLINK_Copter.command_int_only this (UInt16.toUInt32 (t'1))
  if t'2 then
    return (8 : UInt32)
  PMem.stU32 (fp + 0) (3 : UInt32)
  let t'3 ← PMem.ldU16 (packet + 28)
  let t'4 ← GCS_MAVLINK.command_long_stores_location (UInt16.toUInt32 (t'3))
  if t'4 then
    let t'5 ← PMem.ldU16 (packet + 28)
    let t'6 ← GCS_MAVLINK.mav_frame_for_command_long this (fp + 0) (UInt16.toUInt32 (t'5))
    if !t'6 then
      return (8 : UInt32)
  __mavlink_command_int_t.__mavlink_command_int_t (fp + 8)
  let t'7 ← PMem.ldU32 (fp + 0)
  GCS_MAVLINK.convert_COMMAND_LONG_to_COMMAND_INT this packet (fp + 8) t'7
  let t'8 ← GCS_MAVLINK_Copter.handle_command_int_packet this (fp + 8) msg
  return t'8

def GCS_MAVLINK.try_command_long_as_command_int (this : UInt64) (packet : UInt64) (msg : UInt64) : PMem.M UInt32 := do
  let fp ← PMem.enter 43
  let r ← GCS_MAVLINK.try_command_long_as_command_int.body fp this packet msg
  PMem.leave fp
  return r

/-- C++ `GCS_MAVLINK::handle_command_long : void (const mavlink_message_t &)`, `GCS_Common.cpp:5367-5402`. -/
def GCS_MAVLINK.handle_command_long.body (fp : UInt64) (this : UInt64) (msg : UInt64) : PMem.M Unit := do
  __mavlink_command_long_t.__mavlink_command_long_t (fp + 0)
  mavlink_msg_command_long_decode msg (fp + 0)
  let t'1 ← PMem.ldU16 ((fp + 0) + 28)
  let t'2 ← PMem.ldU64 ((0xba88 : UInt64) /- &hal -/ + 88)
  PMem.stU16 ((t'2 + 8) + 60) t'1
  let t'3 ← GCS_MAVLINK.try_command_long_as_command_int this (fp + 0) msg
  let mut result : UInt32 := t'3
  let t'4 ← PMem.ldU32 (this + 40)
  let t'5 ← PMem.ldU16 ((fp + 0) + 28)
  let t'6 ← camera_command_result_param2'mavlink_command_long_t (fp + 0) result
  let t'7 ← PMem.ldU32 (msg + 8)
  let t'8 ← PMem.ldU8 (msg + 12)
  mavlink_msg_command_ack_send t'4 t'5 (UInt32.toUInt8 (result)) (Int8.toUInt8 (Int32.toInt8 ((0 : Int32)))) (UInt32.toInt32 (UInt8.toUInt32 (t'6))) t'7 t'8
  let t'9 := Int16.toUInt16 (Int32.toInt16 ((0 : Int32)))
  let t'10 ← PMem.ldU64 ((0xba88 : UInt64) /- &hal -/ + 88)
  PMem.stU16 ((t'10 + 8) + 60) t'9
  return ()

def GCS_MAVLINK.handle_command_long (this : UInt64) (msg : UInt64) : PMem.M Unit := do
  let fp ← PMem.enter 33
  let r ← GCS_MAVLINK.handle_command_long.body fp this msg
  PMem.leave fp
  return r

/-- C++ `GCS_MAVLINK::handle_command_int : void (const mavlink_message_t &)`, `GCS_Common.cpp:5890-5922`. -/
def GCS_MAVLINK.handle_command_int.body (fp : UInt64) (this : UInt64) (msg : UInt64) : PMem.M Unit := do
  __mavlink_command_int_t.__mavlink_command_int_t (fp + 0)
  mavlink_msg_command_int_decode msg (fp + 0)
  let t'1 ← PMem.ldU16 ((fp + 0) + 28)
  let t'2 ← PMem.ldU64 ((0xba88 : UInt64) /- &hal -/ + 88)
  PMem.stU16 ((t'2 + 8) + 60) t'1
  let t'3 ← GCS_MAVLINK_Copter.handle_command_int_packet this (fp + 0) msg
  let mut result : UInt32 := t'3
  let t'4 ← PMem.ldU32 (this + 40)
  let t'5 ← PMem.ldU16 ((fp + 0) + 28)
  let t'6 ← camera_command_result_param2'mavlink_command_int_t (fp + 0) result
  let t'7 ← PMem.ldU32 (msg + 8)
  let t'8 ← PMem.ldU8 (msg + 12)
  mavlink_msg_command_ack_send t'4 t'5 (UInt32.toUInt8 (result)) (Int8.toUInt8 (Int32.toInt8 ((0 : Int32)))) (UInt32.toInt32 (UInt8.toUInt32 (t'6))) t'7 t'8
  let t'9 := Int16.toUInt16 (Int32.toInt16 ((0 : Int32)))
  let t'10 ← PMem.ldU64 ((0xba88 : UInt64) /- &hal -/ + 88)
  PMem.stU16 ((t'10 + 8) + 60) t'9
  return ()

def GCS_MAVLINK.handle_command_int (this : UInt64) (msg : UInt64) : PMem.M Unit := do
  let fp ← PMem.enter 35
  let r ← GCS_MAVLINK.handle_command_int.body fp this msg
  PMem.leave fp
  return r

/-- C++ `GCS_MAVLINK::handle_message : void (const mavlink_message_t &)`, `GCS_Common.cpp:4283-4629`. -/
def GCS_MAVLINK.handle_message (this : UInt64) (msg : UInt64) : PMem.M Unit := do
  for _ in [0:1] do
    let t'1 ← PMem.ldBits msg 104 24
    let sw'2 := UInt32.toInt32 ((UInt64.toUInt32 (t'1)))
    if sw'2 == (0 : Int32) then
      GCS_MAVLINK.handle_heartbeat this msg
      break
      PMem.unreached "GCS_MAVLINK::handle_command_ack"
      break
      GCS_MAVLINK.handle_setup_signing this msg
    else if sw'2 == (77 : Int32) then
      PMem.unreached "GCS_MAVLINK::handle_command_ack"
      break
      GCS_MAVLINK.handle_setup_signing this msg
    else if sw'2 == (256 : Int32) then
      GCS_MAVLINK.handle_setup_signing this msg
    else if sw'2 == (21 : Int32) || sw'2 == (23 : Int32) || sw'2 == (20 : Int32) then
      GCS_MAVLINK.handle_common_param_message this msg
    else if sw'2 == (48 : Int32) then
      PMem.unreached "GCS_MAVLINK::handle_set_gps_global_origin"
    else if sw'2 == (111 : Int32) then
      GCS_MAVLINK.handle_timesync this msg
    else if sw'2 == (11 : Int32) then
      GCS_MAVLINK.handle_set_mode this msg
    else if sw'2 == (183 : Int32) then
      PMem.unreached "GCS_MAVLINK::handle_send_autopilot_version"
    else if sw'2 == (38 : Int32) || sw'2 == (43 : Int32) || sw'2 == (44 : Int32) || sw'2 == (45 : Int32) || sw'2 == (39 : Int32) || sw'2 == (73 : Int32) || sw'2 == (51 : Int32) || sw'2 == (40 : Int32) || sw'2 == (47 : Int32) || sw'2 == (41 : Int32) then
      GCS_MAVLINK.handle_common_mission_message this msg
    else if sw'2 == (76 : Int32) then
      GCS_MAVLINK.handle_command_long this msg
    else if sw'2 == (75 : Int32) then
      GCS_MAVLINK.handle_command_int this msg
    else if sw'2 == (22 : Int32) then
      PMem.unreached "GCS_MAVLINK::handle_param_value"
    else if sw'2 == (166 : Int32) || sw'2 == (109 : Int32) then
      PMem.unreached "GCS_MAVLINK::handle_radio_status"
    else if sw'2 == (233 : Int32) || sw'2 == (232 : Int32) || sw'2 == (123 : Int32) then
      let t'3 ← PMem.ldU32 (this + 40)
      let t'4 ← VehicleBridge.gps'0
      VehicleBridge.AP_GPS.handle_msg'2 t'4 t'3 msg
    else if sw'2 == (253 : Int32) then
      PMem.unreached "GCS_MAVLINK::handle_statustext"
    else if sw'2 == (186 : Int32) then
      PMem.unreached "handle_led_control"
    else if sw'2 == (69 : Int32) then
      PMem.unreached "GCS_MAVLINK::handle_manual_control"
    else if sw'2 == (258 : Int32) then
      PMem.unreached "handle_play_tune"
    else if sw'2 == (66 : Int32) then
      let t'5 ← GCS_MAVLINK.option_enabled this (4 : UInt16)
      if t'5 then
        break
      GCS_MAVLINK.handle_request_data_stream this msg
    else if sw'2 == (172 : Int32) then
      PMem.unreached "GCS_MAVLINK::handle_data_packet"
    else if sw'2 == (2 : Int32) then
      GCS_MAVLINK.handle_system_time_message this msg
    else if sw'2 == (70 : Int32) then
      PMem.unreached "GCS_MAVLINK::handle_rc_channels_override"
    else if sw'2 == (132 : Int32) then
      PMem.unreached "GCS_MAVLINK::handle_distance_sensor"
    else if sw'2 == (149 : Int32) then
      PMem.unreached "GCS_MAVLINK::handle_landing_target"
    else if sw'2 == (251 : Int32) then
      PMem.unreached "GCS_MAVLINK::handle_named_value"
    else if sw'2 == (386 : Int32) || sw'2 == (387 : Int32) then
      PMem.unreached "GCS_MAVLINK::handle_can_frame"
    else if sw'2 == (388 : Int32) then
      PMem.unreached "handle_can_filter_modify"
    else
      pure ()
  return ()

/-- C++ `GCS_MAVLINK_Copter::handle_message : void (const mavlink_message_t &)`, `GCS_MAVLink_Copter.cpp:1179-1204`. -/
def GCS_MAVLINK_Copter.handle_message (this : UInt64) (msg : UInt64) : PMem.M Unit := do
  let t'1 ← PMem.ldBits msg 104 24
  let sw'2 := UInt32.toInt32 ((UInt64.toUInt32 (t'1)))
  if sw'2 == (82 : Int32) then
    GCS_MAVLINK_Copter.handle_message_set_attitude_target this msg
  else if sw'2 == (84 : Int32) then
    GCS_MAVLINK_Copter.handle_message_set_position_target_local_ned this msg
  else if sw'2 == (86 : Int32) then
    GCS_MAVLINK_Copter.handle_message_set_position_target_global_int this msg
  else
    GCS_MAVLINK.handle_message this msg
  return ()

/-- C++ `GCS_MAVLINK::raw_packetReceived : void (uint8_t, const mavlink_status_t &, const mavlink_message_t &)`, `GCS_Common.cpp:1884-1925`. -/
def GCS_MAVLINK.raw_packetReceived (this : UInt64) (framing_status : UInt8) (status : UInt64) (msg : UInt64) : PMem.M Unit := do
  let mut framing_status := framing_status
  if ((UInt32.toInt32 (UInt8.toUInt32 (framing_status))) == (UInt32.toInt32 ((1 : UInt32)))) then
    GCS_MAVLINK_Copter.packetReceived this status msg
  let t'1 ← MAVLink_routing.check_and_forward (0xc740 : UInt64) /- &GCS_MAVLINK::routing -/ framing_status this msg
  if !t'1 then
    return ()
  let t'2 ← PMem.ldBits msg 104 24
  if ((UInt32.toInt32 ((UInt64.toUInt32 (t'2)))) == (33 : Int32)) then
    pure ()
  let t'3 ← GCS_MAVLINK.accept_packet this status msg
  if !t'3 then
    return ()
  GCS_MAVLINK_Copter.handle_message this msg
  return ()

/-- C++ `GCS_MAVLINK::update_receive : void (uint32_t)`, `GCS_Common.cpp:1927-2103`. -/
def GCS_MAVLINK.update_receive.body (fp : UInt64) (this : UInt64) (max_time_us : UInt32) : PMem.M Unit := do
  let mut max_time_us := max_time_us
  let t'1 ← GCS_MAVLINK.locked this
  if t'1 then
    return ()
  __mavlink_message.__mavlink_message (fp + 0)
  __mavlink_status.__mavlink_status (fp + 304)
  let mut tstart_us : UInt32 := (← PMem.clock).toUInt32
  let mut now_ms : UInt32 := ((← PMem.clock) / 1000).toUInt32
  let t'2 := Int16.toUInt16 (Int32.toInt16 ((0 : Int32)))
  PMem.stU16 ((fp + 304) + 14) t'2
  let t'3 ← PMem.ldU64 (this + 480)
  let t'4 ← PMem.uartAvailable t'3
  let mut nbytes : UInt16 := UInt32.toUInt16 (t'4)
  for i'5 in [0:nbytes.toNat] do
    let i : UInt16 := UInt16.ofNat i'5
    let t'6 ← PMem.ldU64 (this + 480)
    let t'7 ← PMem.uartRead t'6
    let mut c : UInt8 := Int8.toUInt8 (Int16.toInt8 (t'7))
    let mut protocol_timeout : UInt32 := Int32.toUInt32 ((4000 : Int32))
    let mut sc'9 := false
    if sc'9 then
      let t'8 ← PMem.ldU32 ((this + 776) + 16)
      sc'9 := (decide ((now_ms - t'8) > protocol_timeout))
    if sc'9 then
      if false then
        PMem.stU32 ((this + 776) + 20) now_ms
        let t'10 ← PMem.ldU32 (this + 40)
        PMem.stB ((0xbf70 : UInt64) /- &gcs_alternative_active -/ + ((UInt64.toInt64 (UInt32.toUInt64 (t'10))) * 1).toUInt64) true
      let t'11 ← PMem.ldU32 ((this + 776) + 20)
      if (decide ((now_ms - t'11) ≤ protocol_timeout)) then
        continue
    let mut parsed_packet : Bool := false
    let t'12 ← GCS_MAVLINK.channel_buffer this
    let t'13 ← GCS_MAVLINK.channel_status this
    let t'14 ← mavlink_frame_char_buffer t'12 t'13 c (fp + 0) (fp + 304)
    let mut framing : UInt8 := t'14
    if ((UInt32.toInt32 (UInt8.toUInt32 (framing))) != (UInt32.toInt32 ((0 : UInt32)))) then
      let t'15 ← PMem.ldBits (fp + 0) 104 24
      let t'16 := UInt32.toUInt16 ((UInt64.toUInt32 (t'15)))
      let t'17 ← PMem.ldU64 ((0xba88 : UInt64) /- &hal -/ + 88)
      PMem.stU16 ((t'17 + 8) + 58) t'16
      GCS_MAVLINK.raw_packetReceived this framing (fp + 304) (fp + 0)
      if ((UInt32.toInt32 (UInt8.toUInt32 (framing))) == (UInt32.toInt32 ((1 : UInt32)))) then
        parsed_packet := true
        let t'18 ← PMem.ldU32 (this + 40)
        PMem.stB ((0xbf70 : UInt64) /- &gcs_alternative_active -/ + ((UInt64.toInt64 (UInt32.toUInt64 (t'18))) * 1).toUInt64) false
        PMem.stU32 ((this + 776) + 16) now_ms
      let t'19 := Int16.toUInt16 (Int32.toInt16 ((0 : Int32)))
      let t'20 ← PMem.ldU64 ((0xba88 : UInt64) /- &hal -/ + 88)
      PMem.stU16 ((t'20 + 8) + 58) t'19
    if (parsed_packet || (((UInt32.toInt32 (UInt16.toUInt32 (i))) % (100 : Int32)) == (0 : Int32))) then
      if (decide ((((← PMem.clock).toUInt32) - tstart_us) > max_time_us)) then
        break
  let mut tnow : UInt32 := ((← PMem.clock) / 1000).toUInt32
  let t'21 ← PMem.ldU32 ((this + 72) + 16)
  let t'22 ← PMem.ldU16 ((this + 72) + 20)
  let mut sc'24 := (decide ((tnow - t'21) > (UInt16.toUInt32 (t'22))))
  if sc'24 then
    let t'23 ← GCS_MAVLINK.is_private this
    sc'24 := !t'23
  let mut sc'26 := sc'24
  if sc'26 then
    let t'25 ← GCS_MAVLINK.option_enabled this (16 : UInt16)
    sc'26 := !t'25
  if sc'26 then
    let t'27 ← PMem.ldU32 (this + 40)
    let t'28 ← comm_get_txspace t'27
    let t'29 ← PMem.ldU32 (this + 40)
    let t'30 ← GCS_MAVLINK.packet_overhead_chan t'29
    let mut c'31 : Bool := default
    if (decide ((UInt16.toUInt32 (t'28)) ≥ (Int32.toUInt32 (((UInt32.toInt32 (UInt8.toUInt32 (t'30))) + (16 : Int32)))))) then
      c'31 := true
    else
      let t'32 ← PMem.ldU32 (this + 40)
      gcs_out_of_space_to_send t'32
      c'31 := false
    if c'31 then
      GCS_MAVLINK.send_timesync this
      PMem.stU32 ((this + 72) + 16) tnow
  return ()

def GCS_MAVLINK.update_receive (this : UInt64) (max_time_us : UInt32) : PMem.M Unit := do
  let fp ← PMem.enter 344
  let r ← GCS_MAVLINK.update_receive.body fp this max_time_us
  PMem.leave fp
  return r

/-- C++ `GCS::update_receive : void ()`, `GCS_Common.cpp:2795-2802`. -/
def GCS.update_receive (this : UInt64) : PMem.M Unit := do
  let mut i : UInt8 := Int8.toUInt8 (Int32.toInt8 ((0 : Int32)))
  let mut first'1 := true
  for _ in PMem.loopFuel do
    if !first'1 then
      let t'2 := i
      let t'3 := (t'2 + 1)
      i := t'3
      pure ()
    first'1 := false
    let t'4 ← GCS.num_gcs this
    if !((decide ((UInt32.toInt32 (UInt8.toUInt32 (i))) < (UInt32.toInt32 (UInt8.toUInt32 (t'4)))))) then break
    let t'5 ← GCS_Copter.chan this i
    GCS_MAVLINK.update_receive t'5 (Int32.toUInt32 ((1000 : Int32)))
  -- GCS::update_passthru: dropped (configuration)
  return ()

/-- C++ `RC_Channel::init_aux : void ()`, `RC_Channel.cpp:2046-2054`. -/
def RC_Channel.init_aux.body (fp : UInt64) (this : UInt64) : PMem.M Unit := do
  let t'1 ← RC_Channel.read_3pos_switch this (fp + 0)
  if !t'1 then
    PMem.stU8 (fp + 0) (0 : UInt8)
  let t'2 ← AP_ParamTBase'short_2.get (this + 8)
  let t'3 ← PMem.ldI16 t'2
  let t'4 ← PMem.ldU8 (fp + 0)
  RC_Channel_Copter.init_aux_function this (Int16.toInt32 (t'3)) t'4
  return ()

def RC_Channel.init_aux (this : UInt64) : PMem.M Unit := do
  let fp ← PMem.enter 1
  let r ← RC_Channel.init_aux.body fp this
  PMem.leave fp
  return r

/-- C++ `RC_Channels::init_aux_all : void ()`, `RC_Channels.cpp:242-252`. -/
def RC_Channels.init_aux_all (this : UInt64) : PMem.M Unit := do
  for i'1 in [0:16] do
    let i : UInt8 := UInt8.ofNat i'1
    let t'2 ← RC_Channels_Copter.channel this i
    let mut c : UInt64 := t'2
    if (c == (0 : UInt64)) then
      continue
    RC_Channel.init_aux c
  RC_Channels.reset_mode_switch this
  return ()

/-- C++ `RC_Channels::init : void ()`, `RC_Channels.cpp:55-63`. -/
def RC_Channels.init (this : UInt64) : PMem.M Unit := do
  for i'1 in [0:16] do
    let i : UInt8 := UInt8.ofNat i'1
    let t'2 ← RC_Channels_Copter.channel this i
    PMem.stU8 (t'2 + 10) i
  RC_Channels.init_aux_all this
  return ()

/-- C++ `Copter::init_ardupilot : void ()`, `system.cpp:16-195`. -/
def Copter.init_ardupilot (this : UInt64) : PMem.M Unit := do
  Copter.notify_flight_mode this
  AP_BattMonitor.init (this + 9584)
  VehicleBridge.AP_Baro.init'0 (this + 1200)
  worldOutputs'drain
  let t'1 ← Copter.gcs this
  GCS.setup_uarts t'1
  Copter.update_using_interlock this
  Copter.init_rc_in this
  Copter.allocate_motors this
  let t'2 ← rc
  RC_Channels.init t'2
  Copter.init_rc_out this
  Copter.esc_calibration_startup_check this
  PMem.stB ((this + 9448) + 22) true
  let t'3 ← PMem.ldU64 ((0xba88 : UInt64) /- &hal -/ + 80)
  discard <| PMem.halDev "AP_HAL::Scheduler::register_timer_failsafe" t'3 #[(0x7f000010 : UInt64), (UInt32.toUInt64 ((Int32.toUInt32 ((1000 : Int32)))))]
  VehicleBridge.AP_GPS.set_log_gps_bit'1 (this + 384) (Int32.toUInt32 (((1 : Int32) <<< (2 : Int32))))
  VehicleBridge.AP_GPS.init'0 (this + 384) (AP_GPS.convert_parameters (this + 384))
  let t'4 ← VehicleBridge.compass'0
  VehicleBridge.Compass.set_log_bit'1 t'4 (Int32.toUInt32 (((1 : Int32) <<< (13 : Int32))))
  let t'5 ← VehicleBridge.compass'0
  VehicleBridge.Compass.init'0 t'5
  worldOutputs'drain
  let t'6 ← PMem.ldU64 (this + 11168)
  AC_AttitudeControl_Multi.parameter_sanity_check t'6
  VehicleBridge.AP_Baro.set_log_baro_bit'1 (this + 1200) (Int32.toUInt32 (((1 : Int32) <<< (7 : Int32))))
  VehicleBridge.AP_Baro.calibrate'1 (this + 1200) true
  worldOutputs'drain
  AP_Mission.init ((this + 11368) + 112)
  Copter.startup_INS_ground this
  Copter.set_land_complete this true
  Copter.set_land_complete_maybe this true
  Copter.failsafe_enable this
  VehicleBridge.AP_InertialSensor.set_log_raw_bit'1 (this + 2344) (UInt64.toUInt32 (((1 : UInt64) <<< (Int64.toUInt64 (Int32.toInt64 ((19 : Int32)))))))
  let t'7 ← PMem.ldU64 (this + 9528)
  AP_MotorsMulticopter.output_min t'7
  let t'8 ← AP_ParamTBase'signed_char_1.get ((this + 6776) + 40)
  let t'9 ← PMem.ldI8 t'8
  let t'10 ← Copter.set_mode this (Int8.toUInt8 (t'9)) (26 : UInt8)
  if !t'10 then
    let t'11 ← Copter.set_mode this (0 : UInt8) (33 : UInt8)
    discard <| pure (t'11)
  let t'12 ← AP_ParamT'float_4.operator_const_float__'1 ((this + 6840) + 1728)
  LowPassFilter'float.set_cutoff_frequency (this + 8864) t'12
  let t'13 ← AP_ParamT'float_4.operator_const_float__'1 ((this + 6840) + 1728)
  LowPassFilter'float.set_cutoff_frequency (this + 8876) t'13
  PMem.stB ((this + 9448) + 13) true
  return ()

/-- C++ `AP_Vehicle::setup : void ()`, `AP_Vehicle.cpp:315-575`. -/
def AP_Vehicle.setup.body (fp : UInt64) (this : UInt64) : PMem.M Unit := do
  AP_Param.setup_sketch_defaults
  AP_SerialManager.init_console (this + 3848)
  for _ in [0:1] do
    let t'1 ← PMem.ldU64 ((0xba88 : UInt64) /- &hal -/ + 48)
    let t'2 ← AP.fwversion
    let t'3 ← PMem.ldU64 (t'2 + 24)
    let t'4 ← PMem.ldU64 ((0xba88 : UInt64) /- &hal -/ + 88)
    let t'5 ← PMem.halDev "AP_HAL::Util::available_memory" t'4 #[]
    discard <| PMem.halDev "AP_HAL::BetterStream::printf" t'1 #[(0x18549 : UInt64) /- "\n\nInit %s\n\nFree RAM: %u\n" -/, t'3, (UInt32.toUInt64 ((UInt64.toUInt32 (t'5))))]
  AP_Param.check_var_info
  Copter.load_parameters this
  Copter.get_scheduler_tasks this (fp + 0) (fp + 8) (fp + 16)
  let t'6 ← PMem.ldU64 (fp + 0)
  let t'7 ← PMem.ldU8 (fp + 8)
  let t'8 ← PMem.ldU32 (fp + 16)
  let t'9 ← AP.scheduler
  AP_Scheduler.init t'9 t'6 t'7 t'8
  let t'10 ← AP_Scheduler.get_loop_period_s (this + 208)
  PMem.stF32 (this + 376) t'10
  AP_Vehicle.set_control_channels this
  let t'11 ← gcs
  GCS.init t'11
  AP_SerialManager.init (this + 3848)
  let t'12 ← gcs
  GCS.setup_console t'12
  let t'13 ← PMem.ldU64 ((0xba88 : UInt64) /- &hal -/ + 80)
  discard <| PMem.halDev "AP_HAL::Scheduler::register_delay_callback" t'13 #[(0x7f000000 : UInt64), (UInt16.toUInt64 ((Int16.toUInt16 (Int32.toInt16 ((5 : Int32))))))]
  AP_BoardConfig.init (this + 8)
  Copter.init_ardupilot this
  let t'14 ← AP.srv
  SRV_Channels.init t'14 (Int32.toUInt32 ((0 : Int32))) (0 : UInt32)
  AP_Vehicle.send_watchdog_reset_statustext this
  let t'15 ← AP.arming
  AP_Arming.init t'15
  AP_Param.invalidate_count
  let t'16 ← gcs
  GCS.send_text t'16 (6 : UInt32) (0x18562 : UInt64) /- "ArduPilot Ready" -/ (fp + 24)
  return ()

def AP_Vehicle.setup (this : UInt64) : PMem.M Unit := do
  let fp ← PMem.enter 32
  let r ← AP_Vehicle.setup.body fp this
  PMem.leave fp
  return r

/-- C++ `Copter::update_flight_mode : void ()`, `mode.cpp:502-513`. -/
def Copter.update_flight_mode (this : UInt64) : PMem.M Unit := do
  let t'1 ← PMem.ldB (((0x86d8 : UInt64) /- &copter -/ + 9448) + 7)
  let t'2 ← PMem.ldU64 (this + 11168)
  AC_AttitudeControl.landed_gain_reduction t'2 t'1
  let t'3 ← PMem.ldU64 (this + 9488)
  let t'4 ← vcall'Mode'move_vehicle_on_ekf_reset'28 t'3
  let mut c'5 : UInt8 := default
  if t'4 then
    c'5 := (1 : UInt8)
  else
    c'5 := (0 : UInt8)
  let t'6 ← PMem.ldU64 (this + 11184)
  AC_PosControl.set_reset_handling_method t'6 c'5
  let t'7 ← PMem.ldU64 (this + 9488)
  vcall'Mode'run'29 t'7
  return ()

/-- C++ `Copter::update_batt_compass : void ()`, `Copter.cpp:620-631`. -/
def Copter.update_batt_compass (this : UInt64) : PMem.M Unit := do
  AP_BattMonitor.read (this + 9584)
  let t'1 ← VehicleBridge.compass'0
  let t'2 ← VehicleBridge.Compass.available'0 t'1
  if t'2 then
    let t'3 ← PMem.ldU64 (this + 9528)
    let t'4 ← AP_Motors.get_throttle t'3
    VehicleBridge.Compass.set_throttle'1 (this + 1512) t'4
    let t'5 ← AP_BattMonitor.voltage'2 (this + 9584)
    VehicleBridge.Compass.set_voltage'1 (this + 1512) t'5
    let t'6 ← VehicleBridge.Compass.read'0 (this + 1512)
    discard <| pure (t'6)
  return ()

/-- C++ `AP_Vehicle::update_arming : void ()`, `AP_Vehicle.cpp:1082-1085`. -/
def AP_Vehicle.update_arming (this : UInt64) : PMem.M Unit := do
  let t'1 ← AP.arming
  AP_Arming.update t'1
  return ()

end Vehicle_lib
