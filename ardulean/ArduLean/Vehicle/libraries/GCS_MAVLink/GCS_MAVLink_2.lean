import ArduLean.Runtime.Bridge
import ArduLean.Vehicle.libraries.AP_RTC.AP_RTC
import ArduLean.Vehicle.libraries.AP_Math.AP_Math
import ArduLean.Vehicle.libraries.AP_HAL.AP_HAL
import ArduLean.Vehicle.libraries.AP_Param.AP_Param
import ArduLean.Vehicle.libraries.AP_Mission.AP_Mission
import ArduLean.Vehicle.libraries.AP_BoardConfig.AP_BoardConfig
import ArduLean.Vehicle.libraries.RC_Channel.RC_Channel
import ArduLean.Vehicle.libraries.AP_Arming.AP_Arming
import ArduLean.Vehicle.ArduCopter.ArduCopter
import ArduLean.Vehicle.libraries.AP_Notify.AP_Notify
import ArduLean.Vehicle.libraries.AP_Common.AP_Common
import ArduLean.Vehicle.libraries.GCS_MAVLink.GCS_MAVLink
import ArduLean.Vehicle.libraries.AP_BattMonitor.AP_BattMonitor
import ArduLean.Vehicle.libraries.AP_Vehicle.AP_Vehicle
import ArduLean.Vehicle.mavlink.mavlink
import ArduLean.Vehicle.libraries.AP_Scheduler.AP_Scheduler
import ArduLean.Vehicle.libraries.SRV_Channel.SRV_Channel
import ArduLean.Vehicle.libraries.AP_HAL.AP_HAL_2
import ArduLean.Vehicle.libraries.AP_Param.AP_Param_2
import ArduLean.Vehicle.libraries.AP_Mission.AP_Mission_2
import ArduLean.Vehicle.libraries.AP_InternalError.AP_InternalError
import ArduLean.Vehicle.libraries.RC_Channel.RC_Channel_2
import ArduLean.Vehicle.ArduCopter.ArduCopter_2
import ArduLean.Vehicle.libraries.AP_SerialManager.AP_SerialManager
import ArduLean.Vehicle.Dispatch_2

/-!
ArduPilot `libraries/GCS_MAVLink`, part 2 of 3. Sources: `libraries/GCS_MAVLink/GCS_Common.cpp`, `libraries/GCS_MAVLink/MissionItemProtocol.cpp`, `libraries/GCS_MAVLink/GCS_Param.cpp`, `libraries/GCS_MAVLink/MAVLink_routing.cpp`, `libraries/GCS_MAVLink/GCS.cpp`, `libraries/GCS_MAVLink/MissionItemProtocol_Waypoints.cpp`, `libraries/GCS_MAVLink/GCS_MAVLink.cpp`, `libraries/GCS_MAVLink/GCS_Signing.cpp`.

Items of `lean/Vehicle_lib.lean` (the vehicle translation), unchanged; placed by `tools/split_modules.py` (`ArduLean/Vehicle/INDEX.md`).
-/

open FloatLib.Floats (Binary32 Binary64)

set_option linter.unusedVariables false
set_option linter.unreachableTactic false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false

namespace Vehicle_lib

/-- C++ `GCS_MAVLINK::send_message : void (const char *, const mavlink_msg_entry_t *)`, `mavlink_msg_mission_ack.h:252-262`. -/
def GCS_MAVLINK.send_message'2 (this : UInt64) (pkt : UInt64) (entry : UInt64) : PMem.M Unit := do
  let mut pkt := pkt
  let mut entry := entry
  let t'1 ← PMem.ldU8 (entry + 6)
  let t'2 ← GCS_MAVLINK.check_payload_size this (UInt8.toUInt16 (t'1))
  if !t'2 then
    return ()
  let t'3 ← PMem.ldU32 (this + 40)
  let t'4 ← PMem.ldU32 entry
  let t'5 ← PMem.ldU8 (entry + 5)
  let t'6 ← PMem.ldU8 (entry + 6)
  let t'7 ← PMem.ldU8 (entry + 4)
  _mav_finalize_message_chan_send t'3 t'4 pkt t'5 t'6 t'7
  return ()

/-- C++ `GCS::send_to_active_channels : void (uint32_t, const char *)`, `GCS.cpp:321-343`. -/
def GCS.send_to_active_channels (this : UInt64) (msgid : UInt32) (pkt : UInt64) : PMem.M Unit := do
  let mut msgid := msgid
  let mut pkt := pkt
  let t'1 ← mavlink_get_msg_entry msgid
  let mut entry : UInt64 := t'1
  if (entry == (0 : UInt64)) then
    return ()
  let mut i : UInt8 := Int8.toUInt8 (Int32.toInt8 ((0 : Int32)))
  let mut first'2 := true
  for _ in PMem.loopFuel do
    if !first'2 then
      let t'3 := i
      let t'4 := (t'3 + 1)
      i := t'4
      pure ()
    first'2 := false
    let t'5 ← GCS.num_gcs this
    if !((decide ((UInt32.toInt32 (UInt8.toUInt32 (i))) < (UInt32.toInt32 (UInt8.toUInt32 (t'5)))))) then break
    let t'6 ← GCS_Copter.chan this i
    let c : UInt64 := t'6
    let t'7 ← GCS_MAVLINK.is_private c
    let mut sc'9 := t'7
    if !sc'9 then
      let t'8 ← GCS_MAVLINK.option_enabled c (16 : UInt16)
      sc'9 := t'8
    if sc'9 then
      continue
    let t'10 ← GCS_MAVLINK.is_active c
    if !t'10 then
      continue
    GCS_MAVLINK.send_message'2 c pkt entry
  return ()

/-- C++ `GCS::send_parameter_value : void (const char *, ap_var_type, float)`, `GCS_Param.cpp:349-369`. -/
def GCS.send_parameter_value.body (fp : UInt64) (this : UInt64) (param_name : UInt64) (param_type : UInt32) (param_value : Binary32) : PMem.M Unit := do
  let mut param_name := param_name
  let mut param_type := param_type
  let mut param_value := param_value
  discard <| PMem.memset ((fp + 0) + 0) 0 4
  discard <| PMem.memset ((fp + 0) + 4) 0 2
  discard <| PMem.memset ((fp + 0) + 6) 0 2
  discard <| PMem.memset ((fp + 0) + 8) 0 16
  discard <| PMem.memset ((fp + 0) + 24) 0 1
  PMem.stU64 (fp + 32) ((16 : UInt64) / (1 : UInt64))
  let t'1 ← PMem.strlen param_name
  PMem.stU64 (fp + 40) t'1
  let t'2 ← MIN'unsigned_long_unsigned_long (fp + 32) (fp + 40)
  let t'3 ← PMem.ldU64 t'2
  let mut to_copy : UInt8 := UInt64.toUInt8 (t'3)
  let t'4 ← PMem.memcpy ((fp + 0) + 8) param_name (UInt8.toUInt64 (to_copy))
  discard <| pure (t'4)
  PMem.stF32 (fp + 0) param_value
  let t'5 ← GCS_MAVLINK.mav_param_type param_type
  let t'6 := UInt32.toUInt8 (t'5)
  PMem.stU8 ((fp + 0) + 24) t'6
  let t'7 ← AP_Param.count_parameters
  PMem.stU16 ((fp + 0) + 4) t'7
  let t'8 := Int16.toUInt16 (Int32.toInt16 ((-(1 : Int32))))
  PMem.stU16 ((fp + 0) + 6) t'8
  let t'9 ← gcs
  GCS.send_to_active_channels t'9 (Int32.toUInt32 ((22 : Int32))) (fp + 0)
  return ()

def GCS.send_parameter_value (this : UInt64) (param_name : UInt64) (param_type : UInt32) (param_value : Binary32) : PMem.M Unit := do
  let fp ← PMem.enter 48
  let r ← GCS.send_parameter_value.body fp this param_name param_type param_value
  PMem.leave fp
  return r

/-- C++ `MAVLink_routing::get_targets : void (const mavlink_message_t &, int64_t &, int16_t &)`, `MAVLink_routing.cpp:472-487`. -/
def MAVLink_routing.get_targets (this : UInt64) (msg : UInt64) (sysid : UInt64) (compid : UInt64) : PMem.M Unit := do
  let t'1 ← PMem.ldBits msg 104 24
  let t'2 ← mavlink_get_msg_entry (UInt64.toUInt32 (t'1))
  let mut msg_entry : UInt64 := t'2
  let t'3 ← PMem.ldU8 (msg + 4)
  let mut targetted : Bool := (((UInt32.toInt32 (UInt8.toUInt32 (t'3))) &&& (4 : Int32)) != (0 : Int32))
  if ((msg_entry == (0 : UInt64)) && (!targetted)) then
    return ()
  let mut sc'6 := targetted
  if !sc'6 then
    let mut sc'5 := (msg_entry != (0 : UInt64))
    if sc'5 then
      let t'4 ← PMem.ldU8 (msg_entry + 7)
      sc'5 := ((UInt32.toInt32 (UInt8.toUInt32 (t'4))) &&& (1 : Int32)) != (0 : Int32)
    sc'6 := sc'5
  if sc'6 then
    let t'7 ← mavlink_msg_get_target_sysid msg msg_entry
    let t'8 := UInt64.toInt64 (UInt32.toUInt64 (t'7))
    PMem.stI64 sysid t'8
  let mut sc'11 := targetted
  if !sc'11 then
    let mut sc'10 := (msg_entry != (0 : UInt64))
    if sc'10 then
      let t'9 ← PMem.ldU8 (msg_entry + 7)
      sc'10 := ((UInt32.toInt32 (UInt8.toUInt32 (t'9))) &&& (2 : Int32)) != (0 : Int32)
    sc'11 := sc'10
  if sc'11 then
    let t'12 ← mavlink_msg_get_target_compid msg msg_entry
    let t'13 := UInt16.toInt16 (UInt8.toUInt16 (t'12))
    PMem.stI16 compid t'13
  return ()

/-- C++ `MAVLink_routing::forward : bool (GCS_MAVLINK &, const mavlink_message_t &)`, `MAVLink_routing.cpp:174-265`. -/
def MAVLink_routing.forward.body (fp : UInt64) (this : UInt64) (in_link : UInt64) (msg : UInt64) : PMem.M Bool := do
  PMem.stI64 (fp + 0) (Int32.toInt64 ((-(1 : Int32))))
  PMem.stI16 (fp + 8) (Int32.toInt16 ((-(1 : Int32))))
  MAVLink_routing.get_targets this msg (fp + 0) (fp + 8)
  let t'1 ← PMem.ldI64 (fp + 0)
  let mut sc'3 := (t'1 == (Int32.toInt64 ((0 : Int32))))
  if !sc'3 then
    let t'2 ← PMem.ldI64 (fp + 0)
    sc'3 := (t'2 == (Int32.toInt64 ((-(1 : Int32)))))
  let mut broadcast_system : Bool := sc'3
  let t'4 ← PMem.ldI16 (fp + 8)
  let mut sc'6 := ((Int16.toInt32 (t'4)) == (0 : Int32))
  if !sc'6 then
    let t'5 ← PMem.ldI16 (fp + 8)
    sc'6 := ((Int16.toInt32 (t'5)) == (-(1 : Int32)))
  let mut broadcast_component : Bool := sc'6
  let mut sc'9 := broadcast_system
  if !sc'9 then
    let t'7 ← PMem.ldI64 (fp + 0)
    let t'8 ← PMem.ldU32 (0xbc50 : UInt64) /- &mavlink_system -/
    sc'9 := (t'7 == (UInt64.toInt64 (UInt32.toUInt64 (t'8))))
  let mut match_system : Bool := sc'9
  let mut sc'13 := match_system
  if sc'13 then
    let mut sc'12 := broadcast_component
    if !sc'12 then
      let t'10 ← PMem.ldI16 (fp + 8)
      let t'11 ← PMem.ldU8 ((0xbc50 : UInt64) /- &mavlink_system -/ + 4)
      sc'12 := ((Int16.toInt32 (t'10)) == (UInt32.toInt32 (UInt8.toUInt32 (t'11))))
    sc'13 := sc'12
  let mut match_component : Bool := sc'13
  let mut process_locally : Bool := (match_system && match_component)
  let t'14 ← GCS_MAVLINK.is_private in_link
  let mut from_private_channel : Bool := t'14
  let mut should_process_locally : Bool := from_private_channel
  if should_process_locally then
    return process_locally
  let t'15 ← GCS_MAVLINK.option_enabled in_link (16 : UInt16)
  if (t'15 && (broadcast_system || broadcast_component)) then
    return (process_locally || broadcast_system)
  if ((process_locally && (!broadcast_system)) && (!broadcast_component)) then
    return true
  let mut forwarded : Bool := false
  let t'16 ← PMem.memset (fp + 16) (0 : Int32) (16 : UInt64)
  discard <| pure (t'16)
  let mut i : UInt8 := Int8.toUInt8 (Int32.toInt8 ((0 : Int32)))
  let mut first'17 := true
  for _ in PMem.loopFuel do
    if !first'17 then
      let t'18 := i
      let t'19 := (t'18 + 1)
      i := t'19
      pure ()
    first'17 := false
    let t'20 ← PMem.ldU8 this
    if !((decide ((UInt32.toInt32 (UInt8.toUInt32 (i))) < (UInt32.toInt32 (UInt8.toUInt32 (t'20)))))) then break
    let t'21 ← PMem.ldU32 (((this + 4) + ((UInt64.toInt64 (UInt8.toUInt64 (i))) * 16).toUInt64) + 8)
    let t'22 ← gcs
    let t'23 ← GCS_Copter.chan t'22 (UInt32.toUInt8 (t'21))
    let mut out_link : UInt64 := t'23
    if (out_link == (0 : UInt64)) then
      continue
    let t'24 ← GCS_MAVLINK.option_enabled out_link (16 : UInt16)
    if (t'24 && (broadcast_system || broadcast_component)) then
      continue
    let t'25 ← GCS_MAVLINK.is_private out_link
    let mut sc'27 := t'25
    if !sc'27 then
      let t'26 ← GCS_MAVLINK.option_enabled out_link (16 : UInt16)
      sc'27 := t'26
    let mut sc'33 := sc'27
    if sc'33 then
      let t'28 ← PMem.ldI64 (fp + 0)
      let t'29 ← PMem.ldU32 ((this + 4) + ((UInt64.toInt64 (UInt8.toUInt64 (i))) * 16).toUInt64)
      let mut sc'32 := (t'28 != (UInt64.toInt64 (UInt32.toUInt64 (t'29))))
      if !sc'32 then
        let t'30 ← PMem.ldI16 (fp + 8)
        let t'31 ← PMem.ldU8 (((this + 4) + ((UInt64.toInt64 (UInt8.toUInt64 (i))) * 16).toUInt64) + 4)
        sc'32 := ((Int16.toInt32 (t'30)) != (UInt32.toInt32 (UInt8.toUInt32 (t'31))))
      sc'33 := sc'32
    if sc'33 then
      continue
    let mut sc'40 := broadcast_system
    if !sc'40 then
      let t'34 ← PMem.ldI64 (fp + 0)
      let t'35 ← PMem.ldU32 ((this + 4) + ((UInt64.toInt64 (UInt8.toUInt64 (i))) * 16).toUInt64)
      let mut sc'39 := (t'34 == (UInt64.toInt64 (UInt32.toUInt64 (t'35))))
      if sc'39 then
        let mut sc'38 := broadcast_component
        if !sc'38 then
          let t'36 ← PMem.ldI16 (fp + 8)
          let t'37 ← PMem.ldU8 (((this + 4) + ((UInt64.toInt64 (UInt8.toUInt64 (i))) * 16).toUInt64) + 4)
          sc'38 := ((Int16.toInt32 (t'36)) == (UInt32.toInt32 (UInt8.toUInt32 (t'37))))
        sc'39 := (sc'38 || (!match_system))
      sc'40 := sc'39
    if sc'40 then
      let mut sc'43 := (in_link != out_link)
      if sc'43 then
        let t'41 ← PMem.ldU32 (((this + 4) + ((UInt64.toInt64 (UInt8.toUInt64 (i))) * 16).toUInt64) + 8)
        let t'42 ← PMem.ldB ((fp + 16) + ((UInt64.toInt64 (UInt32.toUInt64 (t'41))) * 1).toUInt64)
        sc'43 := !t'42
      if sc'43 then
        let t'44 ← PMem.ldU8 (msg + 3)
        let t'45 ← GCS_MAVLINK.check_payload_size out_link (UInt8.toUInt16 (t'44))
        if t'45 then
          let t'46 ← PMem.ldU32 (((this + 4) + ((UInt64.toInt64 (UInt8.toUInt64 (i))) * 16).toUInt64) + 8)
          _mavlink_resend_uart t'46 msg
        let t'47 ← PMem.ldU32 (((this + 4) + ((UInt64.toInt64 (UInt8.toUInt64 (i))) * 16).toUInt64) + 8)
        PMem.stB ((fp + 16) + ((UInt64.toInt64 (UInt32.toUInt64 (t'47))) * 1).toUInt64) true
        forwarded := true
  if (((!forwarded) && match_system) || broadcast_system) then
    process_locally := true
  return process_locally

def MAVLink_routing.forward (this : UInt64) (in_link : UInt64) (msg : UInt64) : PMem.M Bool := do
  let fp ← PMem.enter 32
  let r ← MAVLink_routing.forward.body fp this in_link msg
  PMem.leave fp
  return r

/-- C++ `MAVLink_routing::learn_route : void (GCS_MAVLINK &, const mavlink_message_t &)`, `MAVLink_routing.cpp:365-410`. -/
def MAVLink_routing.learn_route (this : UInt64) (in_link : UInt64) (msg : UInt64) : PMem.M Unit := do
  let mut i : UInt8 := default  -- uninitialized in C
  let t'1 ← PMem.ldU32 (msg + 8)
  if (t'1 == (Int32.toUInt32 ((0 : Int32)))) then
    return ()
  let t'2 ← PMem.ldU32 (msg + 8)
  let t'3 ← PMem.ldU32 (0xbc50 : UInt64) /- &mavlink_system -/
  let mut sc'6 := (t'2 == t'3)
  if sc'6 then
    let t'4 ← PMem.ldU8 (msg + 12)
    let t'5 ← PMem.ldU8 ((0xbc50 : UInt64) /- &mavlink_system -/ + 4)
    sc'6 := ((UInt32.toInt32 (UInt8.toUInt32 (t'4))) == (UInt32.toInt32 (UInt8.toUInt32 (t'5))))
  if sc'6 then
    return ()
  let t'7 ← PMem.ldU32 (msg + 8)
  let t'8 ← PMem.ldU32 (0xbc50 : UInt64) /- &mavlink_system -/
  let mut sc'10 := (t'7 == t'8)
  if sc'10 then
    let t'9 ← PMem.ldU8 (msg + 12)
    sc'10 := ((UInt32.toInt32 (UInt8.toUInt32 (t'9))) == (UInt32.toInt32 ((0 : UInt32))))
  if sc'10 then
    return ()
  let t'11 ← GCS_MAVLINK.get_chan in_link
  let mut in_channel : UInt32 := t'11
  let t'12 := Int8.toUInt8 (Int32.toInt8 ((0 : Int32)))
  i := t'12
  let mut first'13 := true
  for _ in PMem.loopFuel do
    if !first'13 then
      let t'14 := i
      let t'15 := (t'14 + 1)
      i := t'15
      pure ()
    first'13 := false
    let t'16 ← PMem.ldU8 this
    if !((decide ((UInt32.toInt32 (UInt8.toUInt32 (i))) < (UInt32.toInt32 (UInt8.toUInt32 (t'16)))))) then break
    let t'17 ← PMem.ldU32 ((this + 4) + ((UInt64.toInt64 (UInt8.toUInt64 (i))) * 16).toUInt64)
    let t'18 ← PMem.ldU32 (msg + 8)
    let mut sc'21 := (t'17 == t'18)
    if sc'21 then
      let t'19 ← PMem.ldU8 (((this + 4) + ((UInt64.toInt64 (UInt8.toUInt64 (i))) * 16).toUInt64) + 4)
      let t'20 ← PMem.ldU8 (msg + 12)
      sc'21 := ((UInt32.toInt32 (UInt8.toUInt32 (t'19))) == (UInt32.toInt32 (UInt8.toUInt32 (t'20))))
    let mut sc'23 := sc'21
    if sc'23 then
      let t'22 ← PMem.ldU32 (((this + 4) + ((UInt64.toInt64 (UInt8.toUInt64 (i))) * 16).toUInt64) + 8)
      sc'23 := ((UInt32.toInt32 (t'22)) == (UInt32.toInt32 (in_channel)))
    if sc'23 then
      let t'24 ← PMem.ldU8 (((this + 4) + ((UInt64.toInt64 (UInt8.toUInt64 (i))) * 16).toUInt64) + 12)
      let mut sc'26 := ((UInt32.toInt32 (UInt8.toUInt32 (t'24))) == (0 : Int32))
      if sc'26 then
        let t'25 ← PMem.ldBits msg 104 24
        sc'26 := ((UInt32.toInt32 ((UInt64.toUInt32 (t'25)))) == (0 : Int32))
      if sc'26 then
        let t'27 ← mavlink_msg_heartbeat_get_type msg
        PMem.stU8 (((this + 4) + ((UInt64.toInt64 (UInt8.toUInt64 (i))) * 16).toUInt64) + 12) t'27
      break
  let t'28 ← PMem.ldU8 this
  if (((UInt32.toInt32 (UInt8.toUInt32 (i))) == (UInt32.toInt32 (UInt8.toUInt32 (t'28)))) && (decide ((UInt32.toInt32 (UInt8.toUInt32 (i))) < (20 : Int32)))) then
    let t'29 ← PMem.ldU32 (msg + 8)
    PMem.stU32 ((this + 4) + ((UInt64.toInt64 (UInt8.toUInt64 (i))) * 16).toUInt64) t'29
    let t'30 ← PMem.ldU8 (msg + 12)
    PMem.stU8 (((this + 4) + ((UInt64.toInt64 (UInt8.toUInt64 (i))) * 16).toUInt64) + 4) t'30
    PMem.stU32 (((this + 4) + ((UInt64.toInt64 (UInt8.toUInt64 (i))) * 16).toUInt64) + 8) in_channel
    let t'31 ← PMem.ldBits msg 104 24
    if ((UInt32.toInt32 ((UInt64.toUInt32 (t'31)))) == (0 : Int32)) then
      let t'32 ← mavlink_msg_heartbeat_get_type msg
      PMem.stU8 (((this + 4) + ((UInt64.toInt64 (UInt8.toUInt64 (i))) * 16).toUInt64) + 12) t'32
    let t'33 ← PMem.ldU8 this
    let t'34 := (t'33 + 1)
    PMem.stU8 this t'34
  return ()

/-- C++ `MAVLink_routing::handle_heartbeat : void (GCS_MAVLINK &, const mavlink_message_t &)`, `MAVLink_routing.cpp:418-464`. -/
def MAVLink_routing.handle_heartbeat (this : UInt64) (link : UInt64) (msg : UInt64) : PMem.M Unit := do
  let t'1 ← GCS_MAVLINK.active_channel_mask
  let t'2 ← GCS_MAVLINK.private_channel_mask
  let mut mask : UInt16 := UInt32.toUInt16 ((t'1 &&& (~~~t'2)))
  let t'3 ← GCS_MAVLINK.get_chan link
  let mut in_channel : UInt32 := t'3
  let t'4 := (mask &&& (UInt32.toUInt16 ((~~~((1 : UInt32) <<< (Int32.toUInt32 (((UInt32.toInt32 (in_channel)) - (UInt32.toInt32 ((0 : UInt32)))))))))))
  mask := t'4
  let t'5 ← PMem.ldU8 (this + 324)
  let t'6 := (mask &&& (Int16.toUInt16 (Int32.toInt16 ((~~~(UInt32.toInt32 (UInt8.toUInt32 (t'5))))))))
  mask := t'6
  let mut i : UInt8 := Int8.toUInt8 (Int32.toInt8 ((0 : Int32)))
  let mut first'7 := true
  for _ in PMem.loopFuel do
    if !first'7 then
      let t'8 := i
      let t'9 := (t'8 + 1)
      i := t'9
      pure ()
    first'7 := false
    let t'10 ← PMem.ldU8 this
    if !((decide ((UInt32.toInt32 (UInt8.toUInt32 (i))) < (UInt32.toInt32 (UInt8.toUInt32 (t'10)))))) then break
    let t'11 ← PMem.ldU32 ((this + 4) + ((UInt64.toInt64 (UInt8.toUInt64 (i))) * 16).toUInt64)
    let t'12 ← PMem.ldU32 (msg + 8)
    let mut sc'15 := (t'11 == t'12)
    if sc'15 then
      let t'13 ← PMem.ldU8 (((this + 4) + ((UInt64.toInt64 (UInt8.toUInt64 (i))) * 16).toUInt64) + 4)
      let t'14 ← PMem.ldU8 (msg + 12)
      sc'15 := ((UInt32.toInt32 (UInt8.toUInt32 (t'13))) == (UInt32.toInt32 (UInt8.toUInt32 (t'14))))
    if sc'15 then
      let t'16 ← PMem.ldU32 (((this + 4) + ((UInt64.toInt64 (UInt8.toUInt64 (i))) * 16).toUInt64) + 8)
      let t'17 := (mask &&& (UInt32.toUInt16 ((~~~((1 : UInt32) <<< (Int32.toUInt32 (((UInt32.toInt32 (t'16)) - (UInt32.toInt32 ((0 : UInt32)))))))))))
      mask := t'17
  if ((UInt32.toInt32 (UInt16.toUInt32 (mask))) == (0 : Int32)) then
    return ()
  for i'2'18 in [0:16] do
    let i'2 : UInt8 := UInt8.ofNat i'2'18
    if ((UInt16.toUInt32 (mask)) &&& ((1 : UInt32) <<< (Int32.toUInt32 ((UInt32.toInt32 (UInt8.toUInt32 (i'2))))))) != (0 : UInt32) then
      let mut channel : UInt32 := Int32.toUInt32 (((UInt32.toInt32 ((0 : UInt32))) + (UInt32.toInt32 (UInt8.toUInt32 (i'2)))))
      let t'19 ← gcs
      let t'20 ← GCS_Copter.chan t'19 (UInt32.toUInt8 (channel))
      let mut out_link : UInt64 := t'20
      let mut sc'22 := (out_link == (0 : UInt64))
      if !sc'22 then
        let t'21 ← GCS_MAVLINK.option_enabled out_link (16 : UInt16)
        sc'22 := t'21
      if sc'22 then
        continue
      let t'23 ← comm_get_txspace channel
      let t'24 ← PMem.ldU8 (msg + 3)
      let t'25 ← GCS_MAVLINK.packet_overhead_chan channel
      if (decide ((UInt32.toInt32 (UInt16.toUInt32 (t'23))) ≥ ((UInt32.toInt32 (UInt16.toUInt32 ((UInt8.toUInt16 (t'24))))) + (UInt32.toInt32 (UInt8.toUInt32 (t'25)))))) then
        _mavlink_resend_uart channel msg
  return ()

/-- C++ `MAVLink_routing::check_and_forward : bool (uint8_t, GCS_MAVLINK &, const mavlink_message_t &)`, `MAVLink_routing.cpp:97-172`. -/
def MAVLink_routing.check_and_forward (this : UInt64) (framing_status : UInt8) (in_link : UInt64) (msg : UInt64) : PMem.M Bool := do
  let mut framing_status := framing_status
  let t'1 ← PMem.ldU32 (msg + 8)
  let t'2 ← PMem.ldU32 (0xbc50 : UInt64) /- &mavlink_system -/
  let mut sc'5 := (t'1 == t'2)
  if sc'5 then
    let t'3 ← PMem.ldU8 (msg + 12)
    let t'4 ← PMem.ldU8 ((0xbc50 : UInt64) /- &mavlink_system -/ + 4)
    sc'5 := ((UInt32.toInt32 (UInt8.toUInt32 (t'3))) == (UInt32.toInt32 (UInt8.toUInt32 (t'4))))
  if sc'5 then
    return false
  let sw'6 := UInt32.toInt32 (UInt8.toUInt32 (framing_status))
  if sw'6 == (1 : Int32) then
    pure ()
  else if sw'6 == (2 : Int32) then
    let t'7 ← GCS_MAVLINK.option_enabled in_link (8 : UInt16)
    let mut sc'9 := t'7
    if sc'9 then
      let t'8 ← PMem.ldBits msg 104 24
      sc'9 := ((UInt32.toInt32 ((UInt64.toUInt32 (t'8)))) != (166 : Int32))
    let mut sc'11 := sc'9
    if sc'11 then
      let t'10 ← PMem.ldBits msg 104 24
      sc'11 := ((UInt32.toInt32 ((UInt64.toUInt32 (t'10)))) != (109 : Int32))
    let mut sc'13 := sc'11
    if sc'13 then
      let t'12 ← PMem.ldBits msg 104 24
      sc'13 := ((UInt32.toInt32 ((UInt64.toUInt32 (t'12)))) != (246 : Int32))
    if sc'13 then
      let t'14 ← MAVLink_routing.forward this in_link msg
      discard <| pure (t'14)
    return false
  else if sw'6 == (3 : Int32) then
    return false
  else
    return false
  MAVLink_routing.learn_route this in_link msg
  let t'15 ← PMem.ldBits msg 104 24
  let mut sc'17 := ((UInt32.toInt32 ((UInt64.toUInt32 (t'15)))) == (166 : Int32))
  if !sc'17 then
    let t'16 ← PMem.ldBits msg 104 24
    sc'17 := ((UInt32.toInt32 ((UInt64.toUInt32 (t'16)))) == (109 : Int32))
  if sc'17 then
    return true
  let t'18 ← GCS_MAVLINK.is_private in_link
  let mut from_private_channel : Bool := t'18
  let t'19 ← PMem.ldBits msg 104 24
  if ((UInt32.toInt32 ((UInt64.toUInt32 (t'19)))) == (0 : Int32)) then
    let mut sc'21 := !from_private_channel
    if sc'21 then
      let t'20 ← GCS_MAVLINK.option_enabled in_link (16 : UInt16)
      sc'21 := !t'20
    if sc'21 then
      MAVLink_routing.handle_heartbeat this in_link msg
    return true
  let t'22 ← MAVLink_routing.forward this in_link msg
  return t'22

/-- C++ `GCS_MAVLINK::service_statustext : void ()`, `GCS_Common.cpp:2685-2728`. -/
def GCS_MAVLINK.service_statustext (this : UInt64) : PMem.M Unit := do
  let t'1 ← gcs
  let t'2 ← GCS.statustext_queue t'1
  let _statustext_queue : UInt64 := t'2
  let t'3 ← PMem.ldU32 (this + 40)
  let mut chan_bit : UInt32 := ((1 : UInt32) <<< (Int32.toUInt32 ((UInt32.toInt32 (t'3)))))
  let t'4 ← PMem.ldU32 (this + 40)
  let t'5 ← GCS_MAVLINK.packet_overhead_chan t'4
  let mut payload_size : UInt16 := UInt32.toUInt16 ((Int32.toUInt32 (((UInt32.toInt32 (UInt8.toUInt32 (t'5))) + (54 : Int32)))))
  let mut idx : UInt8 := Int8.toUInt8 (Int32.toInt8 ((0 : Int32)))
  let mut first'6 := true
  for _ in PMem.loopFuel do
    first'6 := false
    let t'7 ← ObjectArray'GCS_statustext_t.available _statustext_queue
    if !((decide ((UInt32.toInt32 (UInt8.toUInt32 (idx))) < (UInt32.toInt32 (UInt16.toUInt32 (t'7)))))) then break
    let t'8 ← GCS_MAVLINK.txspace this
    if (decide ((UInt32.toInt32 (UInt16.toUInt32 (t'8))) < (UInt32.toInt32 (UInt16.toUInt32 (payload_size))))) then
      break
    let t'9 ← ObjectArray'GCS_statustext_t.operator__ _statustext_queue (UInt8.toUInt16 (idx))
    let mut statustext : UInt64 := t'9
    if (statustext == (0 : UInt64)) then
      break
    let t'10 ← PMem.ldU32 (statustext + 60)
    if (t'10 &&& chan_bit) != (0 : UInt32) then
      let t'11 ← PMem.ldU32 (this + 40)
      let t'12 ← PMem.ldU8 statustext
      let t'13 ← PMem.ldU16 (statustext + 51)
      let t'14 ← PMem.ldU8 (statustext + 53)
      mavlink_msg_statustext_send t'11 t'12 (statustext + 1) t'13 t'14
      let t'15 := (statustext + 60)
      let t'16 ← PMem.ldU32 t'15
      let t'17 := (t'16 &&& (~~~chan_bit))
      PMem.stU32 t'15 t'17
      let t'18 ← PMem.ldU32 (statustext + 60)
      if (t'18 == (Int32.toUInt32 ((0 : Int32)))) then
        let t'19 ← ObjectArray'GCS_statustext_t.remove _statustext_queue (UInt8.toUInt16 (idx))
        discard <| pure (t'19)
        continue
    let t'20 := idx
    let t'21 := (t'20 + 1)
    idx := t'21
  return ()

/-- C++ `GCS::service_statustext : void ()`, `GCS_Common.cpp:2632-2649`. -/
def GCS.service_statustext (this : UInt64) : PMem.M Unit := do
  let t'1 ← ObjectArray'GCS_statustext_t.is_empty (this + 440)
  if t'1 then
    return ()
  let t'2 ← PMem.ldU8 (this + 536)
  let mut i : UInt8 := t'2
  let mut first'3 := true
  for _ in PMem.loopFuel do
    if !first'3 then
      let t'4 := i
      let t'5 := (t'4 + 1)
      i := t'5
      pure ()
    first'3 := false
    let t'6 ← GCS.num_gcs this
    if !((decide ((UInt32.toInt32 (UInt8.toUInt32 (i))) < (UInt32.toInt32 (UInt8.toUInt32 (t'6)))))) then break
    let t'7 ← GCS_Copter.chan this i
    GCS_MAVLINK.service_statustext t'7
  let mut i'2 : UInt8 := Int8.toUInt8 (Int32.toInt8 ((0 : Int32)))
  let mut first'8 := true
  for _ in PMem.loopFuel do
    if !first'8 then
      let t'9 := i'2
      let t'10 := (t'9 + 1)
      i'2 := t'10
      pure ()
    first'8 := false
    let t'11 ← PMem.ldU8 (this + 536)
    if !((decide ((UInt32.toInt32 (UInt8.toUInt32 (i'2))) < (UInt32.toInt32 (UInt8.toUInt32 (t'11)))))) then break
    let t'12 ← GCS_Copter.chan this i'2
    GCS_MAVLINK.service_statustext t'12
  GCS.StatusTextQueue.prune (this + 440)
  return ()

/-- C++ `GCS::send_textv : void (MAV_SEVERITY, const char *, va_list, mavlink_channel_mask_t)`, `GCS_Common.cpp:2524-2630`. -/
def GCS.send_textv'2.body (fp : UInt64) (this : UInt64) (severity : UInt32) (fmt : UInt64) (arg_list : UInt64) (dest_bitmask : UInt32) : PMem.M Unit := do
  let mut severity := severity
  let mut fmt := fmt
  let mut arg_list := arg_list
  let mut dest_bitmask := dest_bitmask
  for _ in [0:1] do
    let t'1 ← AP_HAL.Util.vsnprintf (0 : UInt64) (this + 175) (257 : UInt64) fmt arg_list
    discard <| pure (t'1)
    let t'2 ← PMem.memcpy (fp + 0) (this + 175) (((51 : UInt64) / (1 : UInt64)) - (Int64.toUInt64 (Int32.toInt64 ((1 : Int32)))))
    discard <| pure (t'2)
    discard <| PMem.memset (((fp + 56) + 0) + 0) 0 1
    discard <| PMem.memset (((fp + 56) + 0) + 1) 0 50
    discard <| PMem.memset (((fp + 56) + 0) + 51) 0 2
    discard <| PMem.memset (((fp + 56) + 0) + 53) 0 1
    discard <| PMem.memset ((fp + 56) + 56) 0 2
    discard <| PMem.memset ((fp + 56) + 60) 0 4
    let t'3 ← PMem.ldB (this + 473)
    if t'3 then
      let t'4 ← GCS.statustext_send_channel_mask this
      PMem.stU32 ((fp + 56) + 60) t'4
    else
      let t'5 ← PMem.ldU8 (this + 28)
      let t'6 := Int32.toUInt32 ((((1 : Int32) <<< (UInt32.toInt32 (UInt8.toUInt32 (t'5)))) - (1 : Int32)))
      PMem.stU32 ((fp + 56) + 60) t'6
    let t'7 := ((fp + 56) + 60)
    let t'8 ← PMem.ldU32 t'7
    let t'9 := (t'8 &&& dest_bitmask)
    PMem.stU32 t'7 t'9
    let t'10 ← PMem.ldU32 ((fp + 56) + 60)
    if !(t'10 != (0 : UInt32)) then
      break
    let t'11 := ((← PMem.clock) / 1000).toUInt16
    PMem.stU16 ((fp + 56) + 56) t'11
    let t'12 := UInt32.toUInt8 (severity)
    PMem.stU8 (fp + 56) t'12
    let t'13 ← PMem.strlen (this + 175)
    if (decide (t'13 > (50 : UInt64))) then
      let t'14 := (0xdf10 : UInt64) /- &GCS::send_textv(...)::msgid -/
      let t'15 ← PMem.ldU16 t'14
      let t'16 := (t'15 + 1)
      PMem.stU16 t'14 t'16
      let t'17 ← PMem.ldU16 (0xdf10 : UInt64) /- &GCS::send_textv(...)::msgid -/
      if ((UInt32.toInt32 (UInt16.toUInt32 (t'17))) == (0 : Int32)) then
        let t'18 := Int16.toUInt16 (Int32.toInt16 ((1 : Int32)))
        PMem.stU16 (0xdf10 : UInt64) /- &GCS::send_textv(...)::msgid -/ t'18
      let t'19 ← PMem.ldU16 (0xdf10 : UInt64) /- &GCS::send_textv(...)::msgid -/
      PMem.stU16 ((fp + 56) + 51) t'19
    let mut remainder : UInt64 := (this + 175)
    let mut i : UInt8 := Int8.toUInt8 (Int32.toInt8 ((0 : Int32)))
    let mut first'20 := true
    for _ in PMem.loopFuel do
      if !first'20 then
        let t'21 := i
        let t'22 := (t'21 + 1)
        i := t'22
        pure ()
      first'20 := false
      if !((decide ((UInt32.toInt32 (UInt8.toUInt32 (i))) < (UInt32.toInt32 (UInt8.toUInt32 ((30 : UInt8))))))) then break
      PMem.stU8 ((fp + 56) + 53) i
      let t'23 ← PMem.strlen remainder
      PMem.stU64 (fp + 120) t'23
      PMem.stU64 (fp + 128) (50 : UInt64)
      let t'24 ← MIN'unsigned_long_unsigned_long (fp + 128) (fp + 120)
      let t'25 ← PMem.ldU64 t'24
      let mut n : UInt16 := UInt64.toUInt16 (t'25)
      if (((UInt32.toInt32 (UInt8.toUInt32 (i))) == ((UInt32.toInt32 (UInt8.toUInt32 ((30 : UInt8)))) - (1 : Int32))) && ((UInt16.toUInt64 (n)) == (50 : UInt64))) then
        let t'26 := (n - (Int16.toUInt16 (Int32.toInt16 ((1 : Int32)))))
        n := t'26
      let t'27 ← PMem.memset ((fp + 56) + 1) (Int8.toInt32 ((0 : Int8))) (50 : UInt64)
      discard <| pure (t'27)
      let t'28 ← PMem.memcpy ((fp + 56) + 1) remainder (UInt16.toUInt64 (n))
      discard <| pure (t'28)
      let t'29 ← ObjectArray'GCS_statustext_t.push_force (this + 440) (fp + 56)
      discard <| pure (t'29)
      let t'30 := (remainder + ((UInt64.toInt64 (UInt16.toUInt64 (n))) * 1).toUInt64)
      remainder := t'30
      let t'31 ← PMem.ldU64 (fp + 120)
      let mut sc'33 := (decide (t'31 < (50 : UInt64)))
      if !sc'33 then
        let t'32 ← PMem.ldU16 ((fp + 56) + 51)
        sc'33 := ((UInt32.toInt32 (UInt16.toUInt32 (t'32))) == (0 : Int32))
      if sc'33 then
        break
  let t'34 ← AP_Notify.get_singleton
  let mut notify : UInt64 := t'34
  if (notify != 0) then
    AP_Notify.send_text notify (fp + 0)
  let t'35 ← GCS_Copter.vehicle_initialised this
  if !t'35 then
    GCS.service_statustext this
  return ()

def GCS.send_textv'2 (this : UInt64) (severity : UInt32) (fmt : UInt64) (arg_list : UInt64) (dest_bitmask : UInt32) : PMem.M Unit := do
  let fp ← PMem.enter 136
  let r ← GCS.send_textv'2.body fp this severity fmt arg_list dest_bitmask
  PMem.leave fp
  return r

/-- C++ `GCS::send_textv : void (MAV_SEVERITY, const char *, va_list)`, `GCS.cpp:301-311`. -/
def GCS.send_textv (this : UInt64) (severity : UInt32) (fmt : UInt64) (arg_list : UInt64) : PMem.M Unit := do
  let mut severity := severity
  let mut fmt := fmt
  let mut arg_list := arg_list
  let t'1 ← GCS.statustext_send_channel_mask this
  let mut mask : UInt32 := t'1
  let t'2 ← PMem.ldB (this + 473)
  if !t'2 then
    let t'3 ← PMem.ldU8 (this + 28)
    let t'4 := Int32.toUInt32 ((((1 : Int32) <<< (UInt32.toInt32 (UInt8.toUInt32 (t'3)))) - (1 : Int32)))
    mask := t'4
  GCS.send_textv'2 this severity fmt arg_list mask
  return ()

/-- C++ `GCS::send_text : void (MAV_SEVERITY, const char *, ...)`, `GCS.cpp:313-319`. -/
def GCS.send_text.body (fp : UInt64) (this : UInt64) (severity : UInt32) (fmt : UInt64) (va' : UInt64) : PMem.M Unit := do
  let mut severity := severity
  PMem.stU64 (fp + 0) fmt
  PMem.stU64 (fp + 8) va'
  let t'1 ← PMem.ldU64 (fp + 0)
  let t'2 ← PMem.ldU64 (fp + 8)
  GCS.send_textv this severity t'1 t'2
  return ()

def GCS.send_text (this : UInt64) (severity : UInt32) (fmt : UInt64) (va' : UInt64) : PMem.M Unit := do
  let fp ← PMem.enter 16
  let r ← GCS.send_text.body fp this severity fmt va'
  PMem.leave fp
  return r

/-- C++ `GCS_MAVLINK::mavlink_coordinate_frame_to_location_alt_frame : bool (const MAV_FRAME, Location::AltFrame &)`, `GCS_Common.cpp:7564-7585`. -/
def GCS_MAVLINK.mavlink_coordinate_frame_to_location_alt_frame.body (fp : UInt64) (this : UInt64) (coordinate_frame : UInt32) (frame : UInt64) : PMem.M Bool := do
  let mut coordinate_frame := coordinate_frame
  let sw'1 := UInt32.toInt32 (coordinate_frame)
  if sw'1 == (3 : Int32) || sw'1 == (6 : Int32) then
    PMem.stI32 frame (1 : Int32)
    return true
  else if sw'1 == (10 : Int32) || sw'1 == (11 : Int32) then
    PMem.stI32 frame (3 : Int32)
    return true
  else if sw'1 == (0 : Int32) || sw'1 == (5 : Int32) then
    PMem.stI32 frame (0 : Int32)
    return true
  else
    PMem.stU64 (fp + 0) (Int64.toUInt64 (Int32.toInt64 ((UInt32.toInt32 (coordinate_frame)))))
    let t'2 ← gcs
    GCS.send_text t'2 (6 : UInt32) (0x18c27 : UInt64) /- "Unknown mavlink coordinate frame %u" -/ (fp + 0)
    return false

def GCS_MAVLINK.mavlink_coordinate_frame_to_location_alt_frame (this : UInt64) (coordinate_frame : UInt32) (frame : UInt64) : PMem.M Bool := do
  let fp ← PMem.enter 8
  let r ← GCS_MAVLINK.mavlink_coordinate_frame_to_location_alt_frame.body fp this coordinate_frame frame
  PMem.leave fp
  return r

/-- C++ `GCS_MAVLINK::handle_setup_signing : void (const mavlink_message_t &) const`, `GCS_Signing.cpp:277-280`. -/
def GCS_MAVLINK.handle_setup_signing.body (fp : UInt64) (this : UInt64) (msg : UInt64) : PMem.M Unit := do
  let t'1 ← gcs
  GCS.send_text t'1 (4 : UInt32) (0x18833 : UInt64) /- "Signing is not enabled in this firmware" -/ (fp + 0)
  return ()

def GCS_MAVLINK.handle_setup_signing (this : UInt64) (msg : UInt64) : PMem.M Unit := do
  let fp ← PMem.enter 8
  let r ← GCS_MAVLINK.handle_setup_signing.body fp this msg
  PMem.leave fp
  return r

/-- C++ `GCS_MAVLINK::send_text : void (MAV_SEVERITY, const char *, ...) const`, `GCS_Common.cpp:874-880`. -/
def GCS_MAVLINK.send_text.body (fp : UInt64) (this : UInt64) (severity : UInt32) (fmt : UInt64) (va' : UInt64) : PMem.M Unit := do
  let mut severity := severity
  PMem.stU64 (fp + 0) fmt
  PMem.stU64 (fp + 8) va'
  let t'1 ← PMem.ldU64 (fp + 0)
  let t'2 ← PMem.ldU64 (fp + 8)
  let t'3 ← PMem.ldU32 (this + 40)
  let t'4 ← gcs
  GCS.send_textv'2 t'4 severity t'1 t'2 (Int32.toUInt32 (((1 : Int32) <<< (UInt32.toInt32 (t'3)))))
  return ()

def GCS_MAVLINK.send_text (this : UInt64) (severity : UInt32) (fmt : UInt64) (va' : UInt64) : PMem.M Unit := do
  let fp ← PMem.enter 16
  let r ← GCS_MAVLINK.send_text.body fp this severity fmt va'
  PMem.leave fp
  return r

/-- C++ `GCS_MAVLINK::send_param_error : void (const mavlink_message_t &, const mavlink_param_set_t &, MAV_PARAM_ERROR)`, `GCS_Param.cpp:430-445`. -/
def GCS_MAVLINK.send_param_error.body (fp : UInt64) (this : UInt64) (msg : UInt64) (param_set : UInt64) (error : UInt32) : PMem.M Unit := do
  let mut error := error
  let t'1 ← PMem.ldU32 (this + 40)
  let t'2 ← comm_get_txspace t'1
  let t'3 ← PMem.ldU32 (this + 40)
  let t'4 ← GCS_MAVLINK.packet_overhead_chan t'3
  let mut c'5 : Bool := default
  if (decide ((UInt16.toUInt32 (t'2)) ≥ (Int32.toUInt32 (((UInt32.toInt32 (UInt8.toUInt32 (t'4))) + (21 : Int32)))))) then
    c'5 := true
  else
    let t'6 ← PMem.ldU32 (this + 40)
    gcs_out_of_space_to_send t'6
    c'5 := false
  if !c'5 then
    return ()
  let t'7 ← strncpy_noterm (fp + 0) (param_set + 6) ((16 : UInt64) / (1 : UInt64))
  discard <| pure (t'7)
  let t'8 ← PMem.ldU32 (this + 40)
  let t'9 ← PMem.ldU32 (msg + 8)
  let t'10 ← PMem.ldU8 (msg + 12)
  mavlink_msg_param_error_send t'8 t'9 t'10 (fp + 0) (Int32.toInt16 ((-(1 : Int32)))) (UInt32.toUInt8 (error))
  return ()

def GCS_MAVLINK.send_param_error (this : UInt64) (msg : UInt64) (param_set : UInt64) (error : UInt32) : PMem.M Unit := do
  let fp ← PMem.enter 16
  let r ← GCS_MAVLINK.send_param_error.body fp this msg param_set error
  PMem.leave fp
  return r

/-- C++ `GCS_MAVLINK::send_parameter_value : void (const char *, ap_var_type, float)`, `GCS_Param.cpp:332-344`. -/
def GCS_MAVLINK.send_parameter_value (this : UInt64) (param_name : UInt64) (param_type : UInt32) (param_value : Binary32) : PMem.M Unit := do
  let mut param_name := param_name
  let mut param_type := param_type
  let mut param_value := param_value
  let t'1 ← PMem.ldU32 (this + 40)
  let t'2 ← comm_get_txspace t'1
  let t'3 ← PMem.ldU32 (this + 40)
  let t'4 ← GCS_MAVLINK.packet_overhead_chan t'3
  let mut c'5 : Bool := default
  if (decide ((UInt16.toUInt32 (t'2)) ≥ (Int32.toUInt32 (((UInt32.toInt32 (UInt8.toUInt32 (t'4))) + (25 : Int32)))))) then
    c'5 := true
  else
    let t'6 ← PMem.ldU32 (this + 40)
    gcs_out_of_space_to_send t'6
    c'5 := false
  if !c'5 then
    return ()
  let t'7 ← PMem.ldU32 (this + 40)
  let t'8 ← GCS_MAVLINK.mav_param_type param_type
  let t'9 ← AP_Param.count_parameters
  mavlink_msg_param_value_send t'7 param_name param_value (UInt32.toUInt8 (t'8)) t'9 (Int16.toUInt16 (Int32.toInt16 ((-(1 : Int32)))))
  return ()

/-- C++ `GCS_MAVLINK::handle_param_set : void (const mavlink_message_t &)`, `GCS_Param.cpp:265-330`. -/
def GCS_MAVLINK.handle_param_set.body (fp : UInt64) (this : UInt64) (msg : UInt64) : PMem.M Unit := do
  __mavlink_param_set_t.__mavlink_param_set_t (fp + 0)
  mavlink_msg_param_set_decode msg (fp + 0)
  let mut vp : UInt64 := default  -- uninitialized in C
  let t'1 ← PMem.strncpy (fp + 32) ((fp + 0) + 6) (Int64.toUInt64 (Int32.toInt64 ((16 : Int32))))
  discard <| pure (t'1)
  let t'2 := Int32.toInt8 ((0 : Int32))
  PMem.stI8 ((fp + 32) + ((Int32.toInt64 ((16 : Int32))) * 1).toUInt64) t'2
  PMem.stU16 (fp + 56) (Int16.toUInt16 (Int32.toInt16 ((0 : Int32))))
  let t'3 ← AP_Param.find (fp + 32) (fp + 24) (fp + 56)
  vp := t'3
  if (vp == (0 : UInt64)) then
    GCS_MAVLINK.send_param_error this msg (fp + 0) (1 : UInt32)
    return ()
  let t'4 ← PMem.ldF32 (fp + 0)
  let mut sc'6 := (Binary32.isNaN t'4)
  if !sc'6 then
    let t'5 ← PMem.ldF32 (fp + 0)
    sc'6 := (Binary32.isInf t'5)
  if sc'6 then
    GCS_MAVLINK.send_param_error this msg (fp + 0) (2 : UInt32)
    return ()
  let t'7 ← PMem.ldU32 (fp + 24)
  let t'8 ← AP_Param.cast_to_float vp t'7
  let mut old_value : Binary32 := t'8
  let t'9 ← PMem.ldU16 (fp + 56)
  let t'10 ← AP_Param.allow_set_via_mavlink vp t'9
  if !t'10 then
    let t'11 ← gcs
    let t'12 ← GCS.get_allow_param_set t'11
    if t'12 then
      PMem.stU64 (fp + 64) (fp + 32)
      let t'13 ← gcs
      GCS.send_text t'13 (4 : UInt32) (0x1881b : UInt64) /- "Param write denied (%s)" -/ (fp + 64)
      GCS_MAVLINK.send_param_error this msg (fp + 0) (3 : UInt32)
    let t'14 ← PMem.ldU32 (fp + 24)
    GCS_MAVLINK.send_parameter_value this (fp + 32) t'14 old_value
    return ()
  let t'15 ← PMem.ldF32 (fp + 0)
  let t'16 ← PMem.ldU32 (fp + 24)
  AP_Param.set_float vp t'15 t'16
  let t'17 ← PMem.ldF32 (fp + 0)
  let t'18 ← is_equal'float_float t'17 old_value
  let mut force_save : Bool := !t'18
  AP_Param.save vp force_save
  let mut sc'20 := force_save
  if sc'20 then
    let t'19 ← PMem.ldU16 (fp + 56)
    sc'20 := ((UInt32.toInt32 (UInt16.toUInt32 (t'19))) &&& ((1 : Int32) <<< (2 : Int32))) != (0 : Int32)
  if sc'20 then
    AP_Param.invalidate_count
  return ()

def GCS_MAVLINK.handle_param_set (this : UInt64) (msg : UInt64) : PMem.M Unit := do
  let fp ← PMem.enter 72
  let r ← GCS_MAVLINK.handle_param_set.body fp this msg
  PMem.leave fp
  return r

/-- C++ `GCS_MAVLINK::handle_param_request_read : void (const mavlink_message_t &)`, `GCS_Param.cpp:225-263`. -/
def GCS_MAVLINK.handle_param_request_read.body (fp : UInt64) (this : UInt64) (msg : UInt64) : PMem.M Unit := do
  let t'1 ← ObjectBuffer'GCS_MAVLINK_pending_param_request.space (0xbee8 : UInt64) /- &GCS_MAVLINK::param_requests -/
  if (t'1 == (Int32.toUInt32 ((0 : Int32)))) then
    return ()
  __mavlink_param_request_read_t.__mavlink_param_request_read_t (fp + 0)
  mavlink_msg_param_request_read_decode msg (fp + 0)
  let t'2 ← PMem.ldU32 (0xc888 : UInt64) /- &GCS_MAVLINK::reserve_param_space_start_ms -/
  let mut saved_reserve_param_space_start_ms : UInt32 := t'2
  let t'3 := Int32.toUInt32 ((0 : Int32))
  PMem.stU32 (0xc888 : UInt64) /- &GCS_MAVLINK::reserve_param_space_start_ms -/ t'3
  let t'4 ← PMem.ldU32 (this + 40)
  let t'5 ← comm_get_txspace t'4
  let t'6 ← PMem.ldU32 (this + 40)
  let t'7 ← GCS_MAVLINK.packet_overhead_chan t'6
  let mut c'8 : Bool := default
  if (decide ((UInt16.toUInt32 (t'5)) ≥ (Int32.toUInt32 (((UInt32.toInt32 (UInt8.toUInt32 (t'7))) + (25 : Int32)))))) then
    c'8 := true
  else
    let t'9 ← PMem.ldU32 (this + 40)
    gcs_out_of_space_to_send t'9
    c'8 := false
  if !c'8 then
    let t'10 := ((← PMem.clock) / 1000).toUInt32
    PMem.stU32 (0xc888 : UInt64) /- &GCS_MAVLINK::reserve_param_space_start_ms -/ t'10
  else
    PMem.stU32 (0xc888 : UInt64) /- &GCS_MAVLINK::reserve_param_space_start_ms -/ saved_reserve_param_space_start_ms
  GCS_MAVLINK.pending_param_request.pending_param_request (fp + 24)
  let t'11 ← PMem.ldU32 (msg + 8)
  PMem.stU32 ((fp + 24) + 24) t'11
  let t'12 ← PMem.ldU8 (msg + 12)
  PMem.stU8 ((fp + 24) + 28) t'12
  let t'13 ← PMem.ldU32 (this + 40)
  PMem.stU32 (fp + 24) t'13
  let t'14 ← PMem.ldI16 (fp + 0)
  PMem.stI16 ((fp + 24) + 4) t'14
  PMem.stU64 (fp + 56) (16 : UInt64)
  PMem.stU64 (fp + 64) (17 : UInt64)
  let t'15 ← MIN'unsigned_long_unsigned_long (fp + 56) (fp + 64)
  let t'16 ← PMem.ldU64 t'15
  let t'17 ← PMem.memcpy ((fp + 24) + 6) ((fp + 0) + 4) t'16
  discard <| pure (t'17)
  let t'18 := Int32.toInt8 ((0 : Int32))
  PMem.stI8 (((fp + 24) + 6) + ((Int32.toInt64 ((16 : Int32))) * 1).toUInt64) t'18
  let t'19 ← ObjectBuffer'GCS_MAVLINK_pending_param_request.push (0xbee8 : UInt64) /- &GCS_MAVLINK::param_requests -/ (fp + 24)
  discard <| pure (t'19)
  let t'20 ← PMem.ldB (0x130c8 : UInt64) /- &GCS_MAVLINK::param_timer_registered -/
  if !t'20 then
    PMem.stB (0x130c8 : UInt64) /- &GCS_MAVLINK::param_timer_registered -/ true
    let t'21 ← PMem.ldU64 ((0xba88 : UInt64) /- &hal -/ + 80)
    PMem.stU64 (fp + 88) this
    PMem.stU64 (fp + 96) (0x7e000010 : UInt64)
    let t'22 := (fp + 88)
    Functor'void.Functor'2 (fp + 72) t'22
    discard <| PMem.halDev "AP_HAL::Scheduler::register_io_process" t'21 #[(fp + 72)]
  return ()

def GCS_MAVLINK.handle_param_request_read (this : UInt64) (msg : UInt64) : PMem.M Unit := do
  let fp ← PMem.enter 104
  let r ← GCS_MAVLINK.handle_param_request_read.body fp this msg
  PMem.leave fp
  return r

/-- C++ `GCS_MAVLINK::handle_timesync : void (const mavlink_message_t &)`, `GCS_Common.cpp:3674-3733`. -/
def GCS_MAVLINK.handle_timesync.body (fp : UInt64) (this : UInt64) (msg : UInt64) : PMem.M Unit := do
  __mavlink_timesync_t.__mavlink_timesync_t (fp + 0)
  mavlink_msg_timesync_decode msg (fp + 0)
  let t'1 ← PMem.ldI64 (fp + 0)
  if (t'1 != (Int32.toInt64 ((0 : Int32)))) then
    let t'2 ← PMem.ldI64 ((fp + 0) + 8)
    let t'3 ← PMem.ldI64 (this + 72)
    if (t'2 != t'3) then
      return ()
    return ()
  let t'4 ← PMem.ldU32 (this + 40)
  let t'5 ← comm_get_txspace t'4
  let t'6 ← PMem.ldU32 (this + 40)
  let t'7 ← GCS_MAVLINK.packet_overhead_chan t'6
  let mut c'8 : Bool := default
  if (decide ((UInt16.toUInt32 (t'5)) ≥ (Int32.toUInt32 (((UInt32.toInt32 (UInt8.toUInt32 (t'7))) + (16 : Int32)))))) then
    c'8 := true
  else
    let t'9 ← PMem.ldU32 (this + 40)
    gcs_out_of_space_to_send t'9
    c'8 := false
  if !c'8 then
    return ()
  __mavlink_timesync_t.__mavlink_timesync_t (fp + 16)
  let t'10 ← GCS_MAVLINK.timesync_receive_timestamp_ns this
  let t'11 := UInt64.toInt64 (t'10)
  PMem.stI64 (fp + 16) t'11
  let t'12 ← PMem.ldI64 ((fp + 0) + 8)
  PMem.stI64 ((fp + 16) + 8) t'12
  let t'13 ← PMem.ldU32 (this + 40)
  let t'14 ← PMem.ldI64 (fp + 16)
  let t'15 ← PMem.ldI64 ((fp + 16) + 8)
  mavlink_msg_timesync_send t'13 t'14 t'15
  return ()

def GCS_MAVLINK.handle_timesync (this : UInt64) (msg : UInt64) : PMem.M Unit := do
  let fp ← PMem.enter 32
  let r ← GCS_MAVLINK.handle_timesync.body fp this msg
  PMem.leave fp
  return r

/-- C++ `GCS_MAVLINK::send_mission_ack : void (const mavlink_message_t &, MAV_MISSION_TYPE, MAV_MISSION_RESULT) const`, `AP_Common.h:221-230`. -/
def GCS_MAVLINK.send_mission_ack (this : UInt64) (msg : UInt64) (mission_type : UInt32) (result : UInt32) : PMem.M Unit := do
  let mut mission_type := mission_type
  let mut result := result
  let t'1 ← PMem.ldU32 (this + 40)
  let t'2 ← comm_get_txspace t'1
  let t'3 ← PMem.ldU32 (this + 40)
  let t'4 ← GCS_MAVLINK.packet_overhead_chan t'3
  let mut c'5 : Bool := default
  if (decide ((UInt16.toUInt32 (t'2)) ≥ (Int32.toUInt32 (((UInt32.toInt32 (UInt8.toUInt32 (t'4))) + (4 : Int32)))))) then
    c'5 := true
  else
    let t'6 ← PMem.ldU32 (this + 40)
    gcs_out_of_space_to_send t'6
    c'5 := false
  if !c'5 then
    return ()
  let t'7 ← PMem.ldU32 (this + 40)
  let t'8 ← PMem.ldU32 (msg + 8)
  let t'9 ← PMem.ldU8 (msg + 12)
  mavlink_msg_mission_ack_send t'7 t'8 t'9 (UInt32.toUInt8 (result)) (UInt32.toUInt8 (mission_type))
  return ()

/-- C++ `MissionItemProtocol::send_mission_ack : void (const GCS_MAVLINK &, const mavlink_message_t &, MAV_MISSION_RESULT) const`, `MissionItemProtocol.cpp:341-351`. -/
def MissionItemProtocol.send_mission_ack (this : UInt64) (_link : UInt64) (msg : UInt64) (result : UInt32) : PMem.M Unit := do
  let mut result := result
  let t'1 ← GCS_MAVLINK.get_chan _link
  let t'2 ← comm_get_txspace t'1
  let t'3 ← GCS_MAVLINK.get_chan _link
  let t'4 ← GCS_MAVLINK.packet_overhead_chan t'3
  let mut c'5 : Bool := default
  if (decide ((UInt16.toUInt32 (t'2)) ≥ (Int32.toUInt32 (((UInt32.toInt32 (UInt8.toUInt32 (t'4))) + (4 : Int32)))))) then
    c'5 := true
  else
    let t'6 ← GCS_MAVLINK.get_chan _link
    gcs_out_of_space_to_send t'6
    c'5 := false
  if !c'5 then
    return ()
  let t'7 ← GCS_MAVLINK.get_chan _link
  let t'8 ← PMem.ldU32 (msg + 8)
  let t'9 ← PMem.ldU8 (msg + 12)
  let t'10 ← MissionItemProtocol_Waypoints.mission_type this
  mavlink_msg_mission_ack_send t'7 t'8 t'9 (UInt32.toUInt8 (result)) (UInt32.toUInt8 (t'10))
  return ()

/-- C++ `MissionItemProtocol::mavlink2_requirement_met : bool (const GCS_MAVLINK &, const mavlink_message_t &) const`, `MissionItemProtocol.cpp:41-53`. -/
def MissionItemProtocol.mavlink2_requirement_met.body (fp : UInt64) (this : UInt64) (_link : UInt64) (msg : UInt64) : PMem.M Bool := do
  let t'1 ← MissionItemProtocol_Waypoints.mission_type this
  if ((UInt32.toInt32 (t'1)) == (UInt32.toInt32 ((0 : UInt32)))) then
    return true
  let t'2 ← GCS_MAVLINK.sending_mavlink1 _link
  if !t'2 then
    return true
  let t'3 ← gcs
  GCS.send_text t'3 (4 : UInt32) (0x18882 : UInt64) /- "Need mavlink2 for item transfer" -/ (fp + 0)
  MissionItemProtocol.send_mission_ack this _link msg (3 : UInt32)
  return false

def MissionItemProtocol.mavlink2_requirement_met (this : UInt64) (_link : UInt64) (msg : UInt64) : PMem.M Bool := do
  let fp ← PMem.enter 8
  let r ← MissionItemProtocol.mavlink2_requirement_met.body fp this _link msg
  PMem.leave fp
  return r

/-- C++ `MissionItemProtocol::handle_mission_write_partial_list : void (GCS_MAVLINK &, const mavlink_message_t &, const mavlink_mission_write_partial_list_t &)`, `MissionItemProtocol.cpp:228-262`. -/
def MissionItemProtocol.handle_mission_write_partial_list.body (fp : UInt64) (this : UInt64) (_link : UInt64) (msg : UInt64) (packet : UInt64) : PMem.M Unit := do
  let t'1 ← MissionItemProtocol.mavlink2_requirement_met this _link msg
  if !t'1 then
    return ()
  let t'2 ← PMem.ldB (this + 8)
  if t'2 then
    MissionItemProtocol.send_mission_ack this _link msg (14 : UInt32)
    return ()
  let t'3 ← PMem.ldI16 packet
  let t'4 ← MissionItemProtocol_Waypoints.item_count this
  let mut sc'7 := (decide ((Int32.toUInt32 (Int16.toInt32 (t'3))) > (UInt16.toUInt32 (t'4))))
  if !sc'7 then
    let t'5 ← PMem.ldI16 (packet + 2)
    let t'6 ← MissionItemProtocol_Waypoints.item_count this
    sc'7 := (decide ((Int32.toUInt32 (Int16.toInt32 (t'5))) > (UInt16.toUInt32 (t'6))))
  let mut sc'10 := sc'7
  if !sc'10 then
    let t'8 ← PMem.ldI16 (packet + 2)
    let t'9 ← PMem.ldI16 packet
    sc'10 := (decide ((Int16.toInt32 (t'8)) < (Int16.toInt32 (t'9))))
  if sc'10 then
    let t'11 ← gcs
    GCS.send_text t'11 (4 : UInt32) (0x1891f : UInt64) /- "Flight plan update rejected" -/ (fp + 0)
    MissionItemProtocol.send_mission_ack this _link msg (1 : UInt32)
    return ()
  let t'12 ← MissionItemProtocol.allocate_update_resources this
  let mut ret_alloc : UInt32 := t'12
  if ((UInt32.toInt32 (ret_alloc)) != (UInt32.toInt32 ((0 : UInt32)))) then
    MissionItemProtocol.send_mission_ack this _link msg ret_alloc
    return ()
  let t'13 ← PMem.ldI16 packet
  let t'14 ← PMem.ldI16 (packet + 2)
  MissionItemProtocol.init_send_requests this _link msg t'13 t'14
  return ()

def MissionItemProtocol.handle_mission_write_partial_list (this : UInt64) (_link : UInt64) (msg : UInt64) (packet : UInt64) : PMem.M Unit := do
  let fp ← PMem.enter 8
  let r ← MissionItemProtocol.handle_mission_write_partial_list.body fp this _link msg packet
  PMem.leave fp
  return r

/-- C++ `GCS_MAVLINK::handle_mission_write_partial_list : void (const mavlink_message_t &)`, `GCS_Common.cpp:831-843`. -/
def GCS_MAVLINK.handle_mission_write_partial_list.body (fp : UInt64) (this : UInt64) (msg : UInt64) : PMem.M Unit := do
  __mavlink_mission_write_partial_list_t.__mavlink_mission_write_partial_list_t (fp + 0)
  mavlink_msg_mission_write_partial_list_decode msg (fp + 0)
  let t'1 ← PMem.ldU8 ((fp + 0) + 6)
  let t'2 ← gcs
  let t'3 ← GCS.get_prot_for_mission_type t'2 (UInt8.toUInt32 (t'1))
  let mut use_prot : UInt64 := t'3
  if (use_prot == (0 : UInt64)) then
    let t'4 ← PMem.ldU8 ((fp + 0) + 6)
    GCS_MAVLINK.send_mission_ack this msg (UInt8.toUInt32 (t'4)) (3 : UInt32)
    return ()
  MissionItemProtocol.handle_mission_write_partial_list use_prot this msg (fp + 0)
  return ()

def GCS_MAVLINK.handle_mission_write_partial_list (this : UInt64) (msg : UInt64) : PMem.M Unit := do
  let fp ← PMem.enter 7
  let r ← GCS_MAVLINK.handle_mission_write_partial_list.body fp this msg
  PMem.leave fp
  return r

/-- C++ `MissionItemProtocol::send_mission_item_warning : void ()`, `MissionItemProtocol.cpp:219-226`. -/
def MissionItemProtocol.send_mission_item_warning.body (fp : UInt64) (this : UInt64) : PMem.M Unit := do
  let t'1 ← PMem.ldB (this + 47)
  if t'1 then
    return ()
  PMem.stB (this + 47) true
  let t'2 ← gcs
  GCS.send_text t'2 (4 : UInt32) (0x188ec : UInt64) /- "got MISSION_ITEM; GCS should send MISSION_ITEM_INT" -/ (fp + 0)
  return ()

def MissionItemProtocol.send_mission_item_warning (this : UInt64) : PMem.M Unit := do
  let fp ← PMem.enter 8
  let r ← MissionItemProtocol.send_mission_item_warning.body fp this
  PMem.leave fp
  return r

/-- C++ `MissionItemProtocol::queued_request_send : void ()`, `MissionItemProtocol.cpp:357-377`. -/
def MissionItemProtocol.queued_request_send (this : UInt64) : PMem.M Unit := do
  let t'1 ← PMem.ldB (this + 8)
  if !t'1 then
    return ()
  let t'2 ← PMem.ldU16 (this + 26)
  let t'3 ← PMem.ldU16 (this + 24)
  if (decide ((UInt32.toInt32 (UInt16.toUInt32 (t'2))) > (UInt32.toInt32 (UInt16.toUInt32 (t'3))))) then
    return ()
  let t'4 ← PMem.ldU64 (this + 16)
  if (t'4 == (0 : UInt64)) then
    return ()
  let t'5 ← PMem.ldU64 (this + 16)
  let t'6 ← GCS_MAVLINK.get_chan t'5
  let t'7 ← comm_get_txspace t'6
  let t'8 ← PMem.ldU64 (this + 16)
  let t'9 ← GCS_MAVLINK.get_chan t'8
  let t'10 ← GCS_MAVLINK.packet_overhead_chan t'9
  let mut c'11 : Bool := default
  if (decide ((UInt16.toUInt32 (t'7)) ≥ (Int32.toUInt32 (((UInt32.toInt32 (UInt8.toUInt32 (t'10))) + (5 : Int32)))))) then
    c'11 := true
  else
    let t'12 ← PMem.ldU64 (this + 16)
    let t'13 ← GCS_MAVLINK.get_chan t'12
    gcs_out_of_space_to_send t'13
    c'11 := false
  if !c'11 then
    return ()
  let t'14 ← PMem.ldU64 (this + 16)
  let t'15 ← GCS_MAVLINK.get_chan t'14
  let t'16 ← PMem.ldU32 (this + 28)
  let t'17 ← PMem.ldU8 (this + 32)
  let t'18 ← PMem.ldU16 (this + 26)
  let t'19 ← MissionItemProtocol_Waypoints.mission_type this
  mavlink_msg_mission_request_send t'15 t'16 t'17 t'18 (UInt32.toUInt8 (t'19))
  let t'20 := ((← PMem.clock) / 1000).toUInt32
  PMem.stU32 (this + 40) t'20
  return ()

/-- C++ `MissionItemProtocol::send_mission_ack : void (const mavlink_message_t &, MAV_MISSION_RESULT) const`, `MissionItemProtocol.cpp:332-340`. -/
def MissionItemProtocol.send_mission_ack'2 (this : UInt64) (msg : UInt64) (result : UInt32) : PMem.M Unit := do
  let mut result := result
  let t'1 ← PMem.ldU64 (this + 16)
  if (t'1 == (0 : UInt64)) then
    return ()
  let t'2 ← PMem.ldU64 (this + 16)
  MissionItemProtocol.send_mission_ack this t'2 msg result
  return ()

/-- C++ `MissionItemProtocol_Waypoints::replace_item : MAV_MISSION_RESULT (const mavlink_mission_item_int_t &)`, `MissionItemProtocol_Waypoints.cpp:102-121`. -/
def MissionItemProtocol_Waypoints.replace_item.body (fp : UInt64) (this : UInt64) (mission_item_int : UInt64) : PMem.M UInt32 := do
  discard <| PMem.memset ((fp + 0) + 0) 0 2
  discard <| PMem.memset ((fp + 0) + 2) 0 2
  discard <| PMem.memset ((fp + 0) + 4) 0 2
  AP_Mission.Content.Content ((fp + 0) + 8)
  discard <| PMem.memset ((fp + 0) + 24) 0 1
  let t'1 ← AP_Mission.mavlink_int_to_mission_cmd mission_item_int (fp + 0)
  let mut res : UInt32 := t'1
  if ((UInt32.toInt32 (res)) != (UInt32.toInt32 ((0 : UInt32)))) then
    return res
  let t'2 ← PMem.ldU16 ((fp + 0) + 2)
  if ((UInt32.toInt32 (UInt16.toUInt32 (t'2))) == (UInt32.toInt32 ((177 : UInt32)))) then
    let t'3 ← PMem.ldU16 ((fp + 0) + 8)
    let t'4 ← MissionItemProtocol_Waypoints.item_count this
    let mut sc'7 := (decide ((UInt32.toInt32 (UInt16.toUInt32 (t'3))) ≥ (UInt32.toInt32 (UInt16.toUInt32 (t'4)))))
    if sc'7 then
      let t'5 ← PMem.ldU16 ((fp + 0) + 8)
      let t'6 ← PMem.ldU16 (this + 24)
      sc'7 := (decide ((UInt32.toInt32 (UInt16.toUInt32 (t'5))) > (UInt32.toInt32 (UInt16.toUInt32 (t'6)))))
    let mut sc'9 := sc'7
    if !sc'9 then
      let t'8 ← PMem.ldU16 ((fp + 0) + 8)
      sc'9 := ((UInt32.toInt32 (UInt16.toUInt32 (t'8))) == (0 : Int32))
    if sc'9 then
      return (1 : UInt32)
  let t'10 ← PMem.ldU16 (fp + 0)
  let t'11 ← PMem.ldU64 (this + 48)
  let t'12 ← AP_Mission.replace_cmd t'11 t'10 (fp + 0)
  if !t'12 then
    return (1 : UInt32)
  return (0 : UInt32)

def MissionItemProtocol_Waypoints.replace_item (this : UInt64) (mission_item_int : UInt64) : PMem.M UInt32 := do
  let fp ← PMem.enter 28
  let r ← MissionItemProtocol_Waypoints.replace_item.body fp this mission_item_int
  PMem.leave fp
  return r

/-- C++ `MissionItemProtocol_Waypoints::append_item : MAV_MISSION_RESULT (const mavlink_mission_item_int_t &)`, `MissionItemProtocol_Waypoints.cpp:31-51`. -/
def MissionItemProtocol_Waypoints.append_item.body (fp : UInt64) (this : UInt64) (mission_item_int : UInt64) : PMem.M UInt32 := do
  discard <| PMem.memset ((fp + 0) + 0) 0 2
  discard <| PMem.memset ((fp + 0) + 2) 0 2
  discard <| PMem.memset ((fp + 0) + 4) 0 2
  AP_Mission.Content.Content ((fp + 0) + 8)
  discard <| PMem.memset ((fp + 0) + 24) 0 1
  let t'1 ← AP_Mission.mavlink_int_to_mission_cmd mission_item_int (fp + 0)
  let mut res : UInt32 := t'1
  if ((UInt32.toInt32 (res)) != (UInt32.toInt32 ((0 : UInt32)))) then
    return res
  let t'2 ← PMem.ldU16 ((fp + 0) + 2)
  if ((UInt32.toInt32 (UInt16.toUInt32 (t'2))) == (UInt32.toInt32 ((177 : UInt32)))) then
    let t'3 ← PMem.ldU16 ((fp + 0) + 8)
    let t'4 ← MissionItemProtocol_Waypoints.item_count this
    let mut sc'7 := (decide ((UInt32.toInt32 (UInt16.toUInt32 (t'3))) ≥ (UInt32.toInt32 (UInt16.toUInt32 (t'4)))))
    if sc'7 then
      let t'5 ← PMem.ldU16 ((fp + 0) + 8)
      let t'6 ← PMem.ldU16 (this + 24)
      sc'7 := (decide ((UInt32.toInt32 (UInt16.toUInt32 (t'5))) > (UInt32.toInt32 (UInt16.toUInt32 (t'6)))))
    let mut sc'9 := sc'7
    if !sc'9 then
      let t'8 ← PMem.ldU16 ((fp + 0) + 8)
      sc'9 := ((UInt32.toInt32 (UInt16.toUInt32 (t'8))) == (0 : Int32))
    if sc'9 then
      return (1 : UInt32)
  let t'10 ← PMem.ldU64 (this + 48)
  let t'11 ← AP_Mission.add_cmd t'10 (fp + 0)
  if !t'11 then
    return (1 : UInt32)
  return (0 : UInt32)

def MissionItemProtocol_Waypoints.append_item (this : UInt64) (mission_item_int : UInt64) : PMem.M UInt32 := do
  let fp ← PMem.enter 28
  let r ← MissionItemProtocol_Waypoints.append_item.body fp this mission_item_int
  PMem.leave fp
  return r

/-- C++ `MissionItemProtocol_Waypoints::complete : MAV_MISSION_RESULT (const GCS_MAVLINK &)`, `MissionItemProtocol_Waypoints.cpp:58-65`. -/
def MissionItemProtocol_Waypoints.complete.body (fp : UInt64) (this : UInt64) (_link : UInt64) : PMem.M UInt32 := do
  GCS_MAVLINK.send_text _link (6 : UInt32) (0x1893b : UInt64) /- "Flight plan received" -/ (fp + 0)
  return (0 : UInt32)

def MissionItemProtocol_Waypoints.complete (this : UInt64) (_link : UInt64) : PMem.M UInt32 := do
  let fp ← PMem.enter 8
  let r ← MissionItemProtocol_Waypoints.complete.body fp this _link
  PMem.leave fp
  return r

/-- C++ `MissionItemProtocol::transfer_is_complete : void (const GCS_MAVLINK &, const mavlink_message_t &)`, `MissionItemProtocol.cpp:323-330`. -/
def MissionItemProtocol.transfer_is_complete (this : UInt64) (_link : UInt64) (msg : UInt64) : PMem.M Unit := do
  let t'1 ← MissionItemProtocol_Waypoints.complete this _link
  let mut result : UInt32 := t'1
  MissionItemProtocol.send_mission_ack this _link msg result
  MissionItemProtocol.free_upload_resources this
  PMem.stB (this + 8) false
  PMem.stU64 (this + 16) (0 : UInt64)
  return ()

/-- C++ `MissionItemProtocol::handle_mission_item : void (const mavlink_message_t &, const mavlink_mission_item_int_t &)`, `MissionItemProtocol.cpp:264-321`. -/
def MissionItemProtocol.handle_mission_item (this : UInt64) (msg : UInt64) (cmd : UInt64) : PMem.M Unit := do
  let t'1 ← PMem.ldU64 (this + 16)
  if (t'1 == (0 : UInt64)) then
    return ()
  let t'2 ← PMem.ldU16 (cmd + 28)
  let t'3 ← PMem.ldU16 (this + 26)
  if ((UInt32.toInt32 (UInt16.toUInt32 (t'2))) != (UInt32.toInt32 (UInt16.toUInt32 (t'3)))) then
    MissionItemProtocol.send_mission_ack'2 this msg (13 : UInt32)
    return ()
  let t'4 ← PMem.ldU32 (msg + 8)
  let t'5 ← PMem.ldU32 (this + 28)
  if (t'4 != t'5) then
    MissionItemProtocol.send_mission_ack'2 this msg (14 : UInt32)
    return ()
  let t'6 ← PMem.ldU8 (msg + 12)
  let t'7 ← PMem.ldU8 (this + 32)
  if ((UInt32.toInt32 (UInt8.toUInt32 (t'6))) != (UInt32.toInt32 (UInt8.toUInt32 (t'7)))) then
    MissionItemProtocol.send_mission_ack'2 this msg (14 : UInt32)
    return ()
  let t'8 ← MissionItemProtocol_Waypoints.item_count this
  let mut _item_count : UInt16 := t'8
  let mut result : UInt32 := default  -- uninitialized in C
  let t'9 ← PMem.ldU16 (cmd + 28)
  if (decide ((UInt32.toInt32 (UInt16.toUInt32 (t'9))) < (UInt32.toInt32 (UInt16.toUInt32 (_item_count))))) then
    let t'10 ← MissionItemProtocol_Waypoints.replace_item this cmd
    result := t'10
  else
    let t'11 ← PMem.ldU16 (cmd + 28)
    if ((UInt32.toInt32 (UInt16.toUInt32 (t'11))) == (UInt32.toInt32 (UInt16.toUInt32 (_item_count)))) then
      let t'12 ← MissionItemProtocol_Waypoints.append_item this cmd
      result := t'12
    else
      result := (1 : UInt32)
  if ((UInt32.toInt32 (result)) != (UInt32.toInt32 ((0 : UInt32)))) then
    MissionItemProtocol.send_mission_ack'2 this msg result
    PMem.stB (this + 8) false
    PMem.stU64 (this + 16) (0 : UInt64)
    MissionItemProtocol.free_upload_resources this
    return ()
  let t'13 := ((← PMem.clock) / 1000).toUInt32
  PMem.stU32 (this + 36) t'13
  let t'14 := (this + 26)
  let t'15 ← PMem.ldU16 t'14
  let t'16 := (t'15 + 1)
  PMem.stU16 t'14 t'16
  let t'17 ← PMem.ldU16 (this + 26)
  let t'18 ← PMem.ldU16 (this + 24)
  if (decide ((UInt32.toInt32 (UInt16.toUInt32 (t'17))) > (UInt32.toInt32 (UInt16.toUInt32 (t'18))))) then
    let t'19 ← PMem.ldU64 (this + 16)
    MissionItemProtocol.transfer_is_complete this t'19 msg
    return ()
  let t'20 ← PMem.ldU64 (this + 16)
  let t'21 ← GCS_MAVLINK.get_chan t'20
  let t'22 ← comm_get_txspace t'21
  let t'23 ← PMem.ldU64 (this + 16)
  let t'24 ← GCS_MAVLINK.get_chan t'23
  let t'25 ← GCS_MAVLINK.packet_overhead_chan t'24
  let mut c'26 : Bool := default
  if (decide ((UInt16.toUInt32 (t'22)) ≥ (Int32.toUInt32 (((UInt32.toInt32 (UInt8.toUInt32 (t'25))) + (5 : Int32)))))) then
    c'26 := true
  else
    let t'27 ← PMem.ldU64 (this + 16)
    let t'28 ← GCS_MAVLINK.get_chan t'27
    gcs_out_of_space_to_send t'28
    c'26 := false
  if c'26 then
    MissionItemProtocol.queued_request_send this
  else
    let t'29 ← MissionItemProtocol_Waypoints.next_item_ap_message_id this
    let t'30 ← PMem.ldU64 (this + 16)
    GCS_MAVLINK.send_message t'30 t'29
  return ()

/-- C++ `GCS_MAVLINK::handle_mission_item : void (const mavlink_message_t &)`, `GCS_Common.cpp:957-1033`. -/
def GCS_MAVLINK.handle_mission_item.body (fp : UInt64) (this : UInt64) (msg : UInt64) : PMem.M Unit := do
  __mavlink_mission_item_int_t.__mavlink_mission_item_int_t (fp + 0)
  let mut send_mission_item_warning : Bool := false
  let t'1 ← PMem.ldBits msg 104 24
  if ((UInt32.toInt32 ((UInt64.toUInt32 (t'1)))) == (39 : Int32)) then
    __mavlink_mission_item_t.__mavlink_mission_item_t (fp + 40)
    mavlink_msg_mission_item_decode msg (fp + 40)
    let t'2 ← AP_Mission.convert_MISSION_ITEM_to_MISSION_ITEM_INT (fp + 40) (fp + 0)
    let mut ret : UInt32 := t'2
    if ((UInt32.toInt32 (ret)) != (UInt32.toInt32 ((0 : UInt32)))) then
      let t'3 ← PMem.ldU8 ((fp + 0) + 37)
      let mut type' : UInt32 := UInt8.toUInt32 (t'3)
      GCS_MAVLINK.send_mission_ack this msg type' ret
      return ()
    send_mission_item_warning := true
  else
    mavlink_msg_mission_item_int_decode msg (fp + 0)
  let t'4 ← PMem.ldU8 ((fp + 0) + 37)
  let mut type''2 : UInt32 := UInt8.toUInt32 (t'4)
  let t'5 ← PMem.ldU8 ((fp + 0) + 35)
  let mut current : UInt8 := t'5
  if (((UInt32.toInt32 (type''2)) == (UInt32.toInt32 ((0 : UInt32)))) && (((UInt32.toInt32 (UInt8.toUInt32 (current))) == (2 : Int32)) || ((UInt32.toInt32 (UInt8.toUInt32 (current))) == (3 : Int32)))) then
    discard <| PMem.memset ((fp + 80) + 0) 0 2
    discard <| PMem.memset ((fp + 80) + 2) 0 2
    discard <| PMem.memset ((fp + 80) + 4) 0 2
    AP_Mission.Content.Content ((fp + 80) + 8)
    discard <| PMem.memset ((fp + 80) + 24) 0 1
    let t'6 ← AP_Mission.mavlink_int_to_mission_cmd (fp + 0) (fp + 80)
    let mut result : UInt32 := t'6
    if ((UInt32.toInt32 (result)) != (UInt32.toInt32 ((0 : UInt32)))) then
      GCS_MAVLINK.send_mission_ack this msg (0 : UInt32) result
      return ()
    if ((UInt32.toInt32 (UInt8.toUInt32 (current))) == (2 : Int32)) then
      let t'7 ← GCS_MAVLINK_Copter.handle_guided_request this (fp + 80)
      let mut c'8 : UInt32 := default
      if t'7 then
        c'8 := (0 : UInt32)
      else
        c'8 := (1 : UInt32)
      result := c'8
    else
      if ((UInt32.toInt32 (UInt8.toUInt32 (current))) == (3 : Int32)) then
        GCS_MAVLINK.handle_change_alt_request this ((fp + 80) + 8)
        result := (0 : UInt32)
    GCS_MAVLINK.send_mission_ack this msg (0 : UInt32) result
    return ()
  let t'9 ← gcs
  let t'10 ← GCS.get_prot_for_mission_type t'9 type''2
  let mut prot : UInt64 := t'10
  if (prot == (0 : UInt64)) then
    GCS_MAVLINK.send_mission_ack this msg type''2 (3 : UInt32)
    return ()
  if send_mission_item_warning then
    MissionItemProtocol.send_mission_item_warning prot
  let t'11 ← PMem.ldB (prot + 8)
  if !t'11 then
    GCS_MAVLINK.send_mission_ack this msg type''2 (1 : UInt32)
    return ()
  MissionItemProtocol.handle_mission_item prot msg (fp + 0)
  return ()

def GCS_MAVLINK.handle_mission_item (this : UInt64) (msg : UInt64) : PMem.M Unit := do
  let fp ← PMem.enter 108
  let r ← GCS_MAVLINK.handle_mission_item.body fp this msg
  PMem.leave fp
  return r

/-- C++ `MissionItemProtocol_Waypoints::get_item : MAV_MISSION_RESULT (uint16_t, mavlink_mission_item_int_t &)`, `MissionItemProtocol_Waypoints.cpp:67-92`. -/
def MissionItemProtocol_Waypoints.get_item.body (fp : UInt64) (this : UInt64) (seq : UInt16) (ret_packet : UInt64) : PMem.M UInt32 := do
  let mut seq := seq
  let mut sc'3 := ((UInt32.toInt32 (UInt16.toUInt32 (seq))) != (0 : Int32))
  if sc'3 then
    let t'1 ← PMem.ldU64 (this + 48)
    let t'2 ← AP_Mission.num_commands t'1
    sc'3 := (decide ((UInt32.toInt32 (UInt16.toUInt32 (seq))) ≥ (UInt32.toInt32 (UInt16.toUInt32 (t'2)))))
  if sc'3 then
    return (13 : UInt32)
  AP_Mission.Mission_Command.Mission_Command (fp + 0)
  let t'4 ← PMem.ldU64 (this + 48)
  let t'5 ← AP_Mission.read_cmd_from_storage t'4 seq (fp + 0)
  if !t'5 then
    return (1 : UInt32)
  let t'6 ← AP_Mission.mission_cmd_to_mavlink_int (fp + 0) ret_packet
  if !t'6 then
    return (1 : UInt32)
  let t'7 := UInt32.toUInt8 ((0 : UInt32))
  PMem.stU8 (ret_packet + 37) t'7
  let t'8 ← PMem.ldU16 ((fp + 0) + 2)
  let t'9 ← PMem.ldU64 (this + 48)
  let t'10 ← AP_Mission.get_current_nav_cmd t'9
  let t'11 ← PMem.ldU16 t'10
  if ((UInt32.toInt32 (UInt16.toUInt32 (t'8))) == (UInt32.toInt32 (UInt16.toUInt32 (t'11)))) then
    let t'12 := Int8.toUInt8 (Int32.toInt8 ((1 : Int32)))
    PMem.stU8 (ret_packet + 35) t'12
  return (0 : UInt32)

def MissionItemProtocol_Waypoints.get_item (this : UInt64) (seq : UInt16) (ret_packet : UInt64) : PMem.M UInt32 := do
  let fp ← PMem.enter 28
  let r ← MissionItemProtocol_Waypoints.get_item.body fp this seq ret_packet
  PMem.leave fp
  return r

/-- C++ `GCS_MAVLINK::send_message_target : void (uint32_t, const char *, uint32_t)`, `GCS_MAVLink.cpp:84-100`. -/
def GCS_MAVLINK.send_message_target (this : UInt64) (msgid : UInt32) (pkt : UInt64) (target_sysid : UInt32) : PMem.M Unit := do
  let mut msgid := msgid
  let mut pkt := pkt
  let mut target_sysid := target_sysid
  let t'1 ← mavlink_get_msg_entry msgid
  let mut entry : UInt64 := t'1
  if (entry == (0 : UInt64)) then
    return ()
  let t'2 ← PMem.ldU8 (entry + 6)
  let t'3 ← GCS_MAVLINK.check_payload_size this (UInt8.toUInt16 (t'2))
  if !t'3 then
    return ()
  let t'4 ← PMem.ldU32 (this + 40)
  let t'5 ← PMem.ldU32 entry
  let t'6 ← PMem.ldU8 (entry + 5)
  let t'7 ← PMem.ldU8 (entry + 6)
  let t'8 ← PMem.ldU8 (entry + 4)
  _mav_finalize_message_chan_send_target t'4 t'5 pkt t'6 t'7 t'8 target_sysid
  return ()

/-- C++ `MissionItemProtocol::handle_mission_request_int : void (GCS_MAVLINK &, const mavlink_mission_request_int_t &, const mavlink_message_t &)`, `MissionItemProtocol.cpp:142-180`. -/
def MissionItemProtocol.handle_mission_request_int.body (fp : UInt64) (this : UInt64) (_link : UInt64) (packet : UInt64) (msg : UInt64) : PMem.M Unit := do
  let t'1 ← MissionItemProtocol.mavlink2_requirement_met this _link msg
  if !t'1 then
    return ()
  let t'2 ← PMem.ldB (this + 8)
  if t'2 then
    MissionItemProtocol.send_mission_ack this _link msg (14 : UInt32)
    return ()
  __mavlink_mission_item_int_t.__mavlink_mission_item_int_t (fp + 0)
  let t'3 ← PMem.ldU16 packet
  let t'4 ← MissionItemProtocol_Waypoints.get_item this t'3 (fp + 0)
  let mut result_code : UInt32 := t'4
  if ((UInt32.toInt32 (result_code)) != (UInt32.toInt32 ((0 : UInt32)))) then
    if ((UInt32.toInt32 (result_code)) == (UInt32.toInt32 ((13 : UInt32)))) then
      let t'5 ← GCS_MAVLINK.get_chan _link
      let mut chan : UInt32 := t'5
      let t'6 ← comm_get_txspace chan
      let t'7 ← GCS_MAVLINK.packet_overhead_chan chan
      let mut c'8 : Bool := default
      if (decide ((UInt16.toUInt32 (t'6)) ≥ (Int32.toUInt32 (((UInt32.toInt32 (UInt8.toUInt32 (t'7))) + (5 : Int32)))))) then
        c'8 := true
      else
        gcs_out_of_space_to_send chan
        c'8 := false
      if c'8 then
        let t'9 ← PMem.ldU32 (msg + 8)
        let t'10 ← PMem.ldU8 (msg + 12)
        let t'11 ← MissionItemProtocol_Waypoints.item_count this
        let t'12 ← MissionItemProtocol_Waypoints.mission_type this
        mavlink_msg_mission_count_send chan t'9 t'10 t'11 (UInt32.toUInt8 (t'12))
    MissionItemProtocol.send_mission_ack this _link msg result_code
    return ()
  let t'13 ← PMem.ldU32 (msg + 8)
  let t'14 ← mavlink_msg_target_field t'13
  PMem.stU8 ((fp + 0) + 32) t'14
  let t'15 ← PMem.ldU8 (msg + 12)
  PMem.stU8 ((fp + 0) + 33) t'15
  let t'16 ← PMem.ldU32 (msg + 8)
  GCS_MAVLINK.send_message_target _link (Int32.toUInt32 ((73 : Int32))) (fp + 0) t'16
  return ()

def MissionItemProtocol.handle_mission_request_int (this : UInt64) (_link : UInt64) (packet : UInt64) (msg : UInt64) : PMem.M Unit := do
  let fp ← PMem.enter 38
  let r ← MissionItemProtocol.handle_mission_request_int.body fp this _link packet msg
  PMem.leave fp
  return r

/-- C++ `GCS_MAVLINK::handle_mission_request_int : void (const mavlink_message_t &)`, `GCS_Common.cpp:671-682`. -/
def GCS_MAVLINK.handle_mission_request_int.body (fp : UInt64) (this : UInt64) (msg : UInt64) : PMem.M Unit := do
  __mavlink_mission_request_int_t.__mavlink_mission_request_int_t (fp + 0)
  mavlink_msg_mission_request_int_decode msg (fp + 0)
  let t'1 ← PMem.ldU8 ((fp + 0) + 4)
  let t'2 ← gcs
  let t'3 ← GCS.get_prot_for_mission_type t'2 (UInt8.toUInt32 (t'1))
  let mut prot : UInt64 := t'3
  if (prot == (0 : UInt64)) then
    return ()
  MissionItemProtocol.handle_mission_request_int prot this (fp + 0) msg
  return ()

def GCS_MAVLINK.handle_mission_request_int (this : UInt64) (msg : UInt64) : PMem.M Unit := do
  let fp ← PMem.enter 5
  let r ← GCS_MAVLINK.handle_mission_request_int.body fp this msg
  PMem.leave fp
  return r

/-- C++ `MissionItemProtocol::handle_mission_request : void (GCS_MAVLINK &, const mavlink_mission_request_t &, const mavlink_message_t &)`, `MissionItemProtocol.cpp:183-216`. -/
def MissionItemProtocol.handle_mission_request.body (fp : UInt64) (this : UInt64) (_link : UInt64) (packet : UInt64) (msg : UInt64) : PMem.M Unit := do
  let t'1 ← MissionItemProtocol.mavlink2_requirement_met this _link msg
  if !t'1 then
    return ()
  __mavlink_mission_item_int_t.__mavlink_mission_item_int_t (fp + 0)
  let t'2 ← PMem.ldU16 packet
  let t'3 ← MissionItemProtocol_Waypoints.get_item this t'2 (fp + 0)
  let mut ret : UInt32 := t'3
  if ((UInt32.toInt32 (ret)) != (UInt32.toInt32 ((0 : UInt32)))) then
    MissionItemProtocol.send_mission_ack this _link msg ret
    return ()
  let t'4 ← PMem.ldU32 (msg + 8)
  let t'5 ← mavlink_msg_target_field t'4
  PMem.stU8 ((fp + 0) + 32) t'5
  let t'6 ← PMem.ldU8 (msg + 12)
  PMem.stU8 ((fp + 0) + 33) t'6
  discard <| PMem.memset ((fp + 40) + 0) 0 4
  discard <| PMem.memset ((fp + 40) + 4) 0 4
  discard <| PMem.memset ((fp + 40) + 8) 0 4
  discard <| PMem.memset ((fp + 40) + 12) 0 4
  discard <| PMem.memset ((fp + 40) + 16) 0 4
  discard <| PMem.memset ((fp + 40) + 20) 0 4
  discard <| PMem.memset ((fp + 40) + 24) 0 4
  discard <| PMem.memset ((fp + 40) + 28) 0 2
  discard <| PMem.memset ((fp + 40) + 30) 0 2
  discard <| PMem.memset ((fp + 40) + 32) 0 1
  discard <| PMem.memset ((fp + 40) + 33) 0 1
  discard <| PMem.memset ((fp + 40) + 34) 0 1
  discard <| PMem.memset ((fp + 40) + 35) 0 1
  discard <| PMem.memset ((fp + 40) + 36) 0 1
  discard <| PMem.memset ((fp + 40) + 37) 0 1
  let t'7 ← AP_Mission.convert_MISSION_ITEM_INT_to_MISSION_ITEM (fp + 0) (fp + 40)
  ret := t'7
  if ((UInt32.toInt32 (ret)) != (UInt32.toInt32 ((0 : UInt32)))) then
    MissionItemProtocol.send_mission_ack this _link msg ret
    return ()
  let t'8 ← PMem.ldB (this + 46)
  if !t'8 then
    PMem.stB (this + 46) true
    let t'9 ← gcs
    GCS.send_text t'9 (4 : UInt32) (0x188be : UInt64) /- "got MISSION_REQUEST; use MISSION_REQUEST_INT!" -/ (fp + 80)
  let t'10 ← PMem.ldU32 (msg + 8)
  GCS_MAVLINK.send_message_target _link (Int32.toUInt32 ((39 : Int32))) (fp + 40) t'10
  return ()

def MissionItemProtocol.handle_mission_request (this : UInt64) (_link : UInt64) (packet : UInt64) (msg : UInt64) : PMem.M Unit := do
  let fp ← PMem.enter 88
  let r ← MissionItemProtocol.handle_mission_request.body fp this _link packet msg
  PMem.leave fp
  return r

/-- C++ `GCS_MAVLINK::handle_mission_request : void (const mavlink_message_t &)`, `GCS_Common.cpp:685-696`. -/
def GCS_MAVLINK.handle_mission_request.body (fp : UInt64) (this : UInt64) (msg : UInt64) : PMem.M Unit := do
  __mavlink_mission_request_t.__mavlink_mission_request_t (fp + 0)
  mavlink_msg_mission_request_decode msg (fp + 0)
  let t'1 ← PMem.ldU8 ((fp + 0) + 4)
  let t'2 ← gcs
  let t'3 ← GCS.get_prot_for_mission_type t'2 (UInt8.toUInt32 (t'1))
  let mut prot : UInt64 := t'3
  if (prot == (0 : UInt64)) then
    return ()
  MissionItemProtocol.handle_mission_request prot this (fp + 0) msg
  return ()

def GCS_MAVLINK.handle_mission_request (this : UInt64) (msg : UInt64) : PMem.M Unit := do
  let fp ← PMem.enter 5
  let r ← GCS_MAVLINK.handle_mission_request.body fp this msg
  PMem.leave fp
  return r

/-- C++ `GCS_MAVLINK::send_mission_current : void (const class AP_Mission &, uint16_t)`, `GCS_Common.cpp:720-740`. -/
def GCS_MAVLINK.send_mission_current (this : UInt64) (mission : UInt64) (seq : UInt16) : PMem.M Unit := do
  let mut seq := seq
  let t'1 ← AP_Mission.num_commands mission
  let mut num_commands : UInt16 := t'1
  if (decide ((UInt32.toInt32 (UInt16.toUInt32 (num_commands))) > (0 : Int32))) then
    let t'2 := (num_commands - (Int16.toUInt16 (Int32.toInt16 ((1 : Int32)))))
    num_commands := t'2
  let t'3 ← AP.vehicle
  let t'4 ← Copter.current_mode_requires_mission t'3
  let mut c'5 : Int32 := default
  if t'4 then
    c'5 := (1 : Int32)
  else
    c'5 := (0 : Int32)
  let mut mission_mode : UInt8 := Int8.toUInt8 (Int32.toInt8 (c'5))
  let t'6 ← PMem.ldU32 (this + 40)
  let t'7 ← GCS_MAVLINK_Copter.mission_state this mission
  mavlink_msg_mission_current_send t'6 seq num_commands (UInt32.toUInt8 (t'7)) mission_mode
  return ()

/-- C++ `MissionItemProtocol::handle_mission_request_list : void (const GCS_MAVLINK &, const mavlink_mission_request_list_t &, const mavlink_message_t &)`, `MissionItemProtocol.cpp:116-140`. -/
def MissionItemProtocol.handle_mission_request_list (this : UInt64) (_link : UInt64) (packet : UInt64) (msg : UInt64) : PMem.M Unit := do
  let t'1 ← MissionItemProtocol.mavlink2_requirement_met this _link msg
  if !t'1 then
    return ()
  let t'2 ← PMem.ldB (this + 8)
  if t'2 then
    MissionItemProtocol.send_mission_ack this _link msg (14 : UInt32)
    return ()
  let t'3 ← GCS_MAVLINK.get_chan _link
  let t'4 ← comm_get_txspace t'3
  let t'5 ← GCS_MAVLINK.get_chan _link
  let t'6 ← GCS_MAVLINK.packet_overhead_chan t'5
  let mut c'7 : Bool := default
  if (decide ((UInt16.toUInt32 (t'4)) ≥ (Int32.toUInt32 (((UInt32.toInt32 (UInt8.toUInt32 (t'6))) + (5 : Int32)))))) then
    c'7 := true
  else
    let t'8 ← GCS_MAVLINK.get_chan _link
    gcs_out_of_space_to_send t'8
    c'7 := false
  if !c'7 then
    return ()
  let t'9 ← GCS_MAVLINK.get_chan _link
  let t'10 ← PMem.ldU32 (msg + 8)
  let t'11 ← PMem.ldU8 (msg + 12)
  let t'12 ← MissionItemProtocol_Waypoints.item_count this
  let t'13 ← MissionItemProtocol_Waypoints.mission_type this
  mavlink_msg_mission_count_send t'9 t'10 t'11 t'12 (UInt32.toUInt8 (t'13))
  return ()

/-- C++ `GCS_MAVLINK::handle_mission_request_list : void (const mavlink_message_t &)`, `GCS_Common.cpp:649-666`. -/
def GCS_MAVLINK.handle_mission_request_list.body (fp : UInt64) (this : UInt64) (msg : UInt64) : PMem.M Unit := do
  __mavlink_mission_request_list_t.__mavlink_mission_request_list_t (fp + 0)
  mavlink_msg_mission_request_list_decode msg (fp + 0)
  let t'1 ← PMem.ldU8 ((fp + 0) + 2)
  let t'2 ← gcs
  let t'3 ← GCS.get_prot_for_mission_type t'2 (UInt8.toUInt32 (t'1))
  let mut prot : UInt64 := t'3
  if (prot == (0 : UInt64)) then
    let t'4 ← PMem.ldU32 (this + 40)
    let t'5 ← PMem.ldU32 (msg + 8)
    let t'6 ← PMem.ldU8 (msg + 12)
    let t'7 ← PMem.ldU8 ((fp + 0) + 2)
    mavlink_msg_mission_ack_send t'4 t'5 t'6 (UInt32.toUInt8 ((3 : UInt32))) t'7
    return ()
  MissionItemProtocol.handle_mission_request_list prot this (fp + 0) msg
  return ()

def GCS_MAVLINK.handle_mission_request_list (this : UInt64) (msg : UInt64) : PMem.M Unit := do
  let fp ← PMem.enter 3
  let r ← GCS_MAVLINK.handle_mission_request_list.body fp this msg
  PMem.leave fp
  return r

/-- C++ `MissionItemProtocol::cancel_upload : bool (const GCS_MAVLINK &, const mavlink_message_t &)`, `MissionItemProtocol.cpp:57-76`. -/
def MissionItemProtocol.cancel_upload (this : UInt64) (_link : UInt64) (msg : UInt64) : PMem.M Bool := do
  let t'1 ← PMem.ldB (this + 8)
  if t'1 then
    let t'2 ← PMem.ldU32 (msg + 8)
    let t'3 ← PMem.ldU32 (this + 28)
    let mut sc'6 := (t'2 != t'3)
    if !sc'6 then
      let t'4 ← PMem.ldU8 (msg + 12)
      let t'5 ← PMem.ldU8 (this + 32)
      sc'6 := ((UInt32.toInt32 (UInt8.toUInt32 (t'4))) != (UInt32.toInt32 (UInt8.toUInt32 (t'5))))
    if sc'6 then
      MissionItemProtocol.send_mission_ack this _link msg (14 : UInt32)
      return false
    MissionItemProtocol.free_upload_resources this
    PMem.stB (this + 8) false
    PMem.stU64 (this + 16) (0 : UInt64)
  return true

/-- C++ `MissionItemProtocol_Waypoints::truncate : void (const mavlink_mission_count_t &)`, `MissionItemProtocol_Waypoints.cpp:128-132`. -/
def MissionItemProtocol_Waypoints.truncate (this : UInt64) (packet : UInt64) : PMem.M Unit := do
  let t'1 ← PMem.ldU16 packet
  let t'2 ← PMem.ldU64 (this + 48)
  AP_Mission.truncate t'2 t'1
  return ()

/-- C++ `MissionItemProtocol::handle_mission_count : void (GCS_MAVLINK &, const mavlink_mission_count_t &, const mavlink_message_t &)`, `MissionItemProtocol.cpp:78-114`. -/
def MissionItemProtocol.handle_mission_count.body (fp : UInt64) (this : UInt64) (_link : UInt64) (packet : UInt64) (msg : UInt64) : PMem.M Unit := do
  let t'1 ← MissionItemProtocol.mavlink2_requirement_met this _link msg
  if !t'1 then
    return ()
  let t'2 ← MissionItemProtocol.cancel_upload this _link msg
  if !t'2 then
    return ()
  let t'3 ← PMem.ldU16 packet
  let t'4 ← MissionItemProtocol_Waypoints.max_items this
  if (decide ((UInt32.toInt32 (UInt16.toUInt32 (t'3))) > (UInt32.toInt32 (UInt16.toUInt32 (t'4))))) then
    MissionItemProtocol.send_mission_ack this _link msg (4 : UInt32)
    let t'5 ← MissionItemProtocol_Waypoints.max_items this
    PMem.stU64 (fp + 0) (UInt32.toUInt64 ((UInt16.toUInt32 (t'5))))
    let t'6 ← gcs
    GCS.send_text t'6 (4 : UInt32) (0x188a2 : UInt64) /- "Only %u items are supported" -/ (fp + 0)
    return ()
  let t'7 ← PMem.ldU16 packet
  let t'8 ← MissionItemProtocol.allocate_receive_resources this t'7
  let mut ret_alloc : UInt32 := t'8
  if ((UInt32.toInt32 (ret_alloc)) != (UInt32.toInt32 ((0 : UInt32)))) then
    MissionItemProtocol.send_mission_ack this _link msg ret_alloc
    return ()
  MissionItemProtocol_Waypoints.truncate this packet
  let t'9 ← PMem.ldU16 packet
  if ((UInt32.toInt32 (UInt16.toUInt32 (t'9))) == (0 : Int32)) then
    MissionItemProtocol.transfer_is_complete this _link msg
    return ()
  let t'10 ← PMem.ldU16 packet
  MissionItemProtocol.init_send_requests this _link msg (Int32.toInt16 ((0 : Int32))) (Int32.toInt16 (((UInt32.toInt32 (UInt16.toUInt32 (t'10))) - (1 : Int32))))
  return ()

def MissionItemProtocol.handle_mission_count (this : UInt64) (_link : UInt64) (packet : UInt64) (msg : UInt64) : PMem.M Unit := do
  let fp ← PMem.enter 8
  let r ← MissionItemProtocol.handle_mission_count.body fp this _link packet msg
  PMem.leave fp
  return r

/-- C++ `GCS_MAVLINK::handle_mission_count : void (const mavlink_message_t &)`, `GCS_Common.cpp:783-800`. -/
def GCS_MAVLINK.handle_mission_count.body (fp : UInt64) (this : UInt64) (msg : UInt64) : PMem.M Unit := do
  __mavlink_mission_count_t.__mavlink_mission_count_t (fp + 0)
  mavlink_msg_mission_count_decode msg (fp + 0)
  let t'1 ← PMem.ldU8 ((fp + 0) + 4)
  let t'2 ← gcs
  let t'3 ← GCS.get_prot_for_mission_type t'2 (UInt8.toUInt32 (t'1))
  let mut prot : UInt64 := t'3
  if (prot == (0 : UInt64)) then
    let t'4 ← PMem.ldU32 (this + 40)
    let t'5 ← PMem.ldU32 (msg + 8)
    let t'6 ← PMem.ldU8 (msg + 12)
    let t'7 ← PMem.ldU8 ((fp + 0) + 4)
    mavlink_msg_mission_ack_send t'4 t'5 t'6 (UInt32.toUInt8 ((3 : UInt32))) t'7
    return ()
  MissionItemProtocol.handle_mission_count prot this (fp + 0) msg
  return ()

def GCS_MAVLINK.handle_mission_count (this : UInt64) (msg : UInt64) : PMem.M Unit := do
  let fp ← PMem.enter 5
  let r ← GCS_MAVLINK.handle_mission_count.body fp this msg
  PMem.leave fp
  return r

/-- C++ `MissionItemProtocol_Waypoints::clear_all_items : bool ()`, `MissionItemProtocol_Waypoints.cpp:53-56`. -/
def MissionItemProtocol_Waypoints.clear_all_items (this : UInt64) : PMem.M Bool := do
  let t'1 ← PMem.ldU64 (this + 48)
  let t'2 ← AP_Mission.clear t'1
  return t'2

/-- C++ `MissionItemProtocol::handle_mission_clear_all : void (const GCS_MAVLINK &, const mavlink_message_t &)`, `MissionItemProtocol.cpp:32-39`. -/
def MissionItemProtocol.handle_mission_clear_all (this : UInt64) (_link : UInt64) (msg : UInt64) : PMem.M Unit := do
  let mut success : Bool := true
  let mut sc'2 := success
  if sc'2 then
    let t'1 ← MissionItemProtocol.cancel_upload this _link msg
    sc'2 := t'1
  success := sc'2
  let mut sc'4 := success
  if sc'4 then
    let t'3 ← MissionItemProtocol_Waypoints.clear_all_items this
    sc'4 := t'3
  success := sc'4
  let mut c'5 : UInt32 := default
  if success then
    c'5 := (0 : UInt32)
  else
    c'5 := (1 : UInt32)
  MissionItemProtocol.send_mission_ack this _link msg c'5
  return ()

/-- C++ `GCS_MAVLINK::handle_mission_clear_all : void (const mavlink_message_t &)`, `GCS_Common.cpp:805-819`. -/
def GCS_MAVLINK.handle_mission_clear_all.body (fp : UInt64) (this : UInt64) (msg : UInt64) : PMem.M Unit := do
  __mavlink_mission_clear_all_t.__mavlink_mission_clear_all_t (fp + 0)
  mavlink_msg_mission_clear_all_decode msg (fp + 0)
  let t'1 ← PMem.ldU8 ((fp + 0) + 2)
  let mut mission_type : UInt32 := UInt8.toUInt32 (t'1)
  let t'2 ← gcs
  let t'3 ← GCS.get_prot_for_mission_type t'2 mission_type
  let mut prot : UInt64 := t'3
  if (prot == (0 : UInt64)) then
    GCS_MAVLINK.send_mission_ack this msg mission_type (3 : UInt32)
    return ()
  MissionItemProtocol.handle_mission_clear_all prot this msg
  return ()

def GCS_MAVLINK.handle_mission_clear_all (this : UInt64) (msg : UInt64) : PMem.M Unit := do
  let fp ← PMem.enter 3
  let r ← GCS_MAVLINK.handle_mission_clear_all.body fp this msg
  PMem.leave fp
  return r

/-- C++ `GCS_MAVLINK::location_from_command_t : bool (const mavlink_command_int_t &, Location &)`, `GCS_Common.cpp:5211-5239`. -/
def GCS_MAVLINK.location_from_command_t.body (fp : UInt64) (this : UInt64) (in' : UInt64) (out : UInt64) : PMem.M Bool := do
  let t'1 ← PMem.ldI32 (in' + 16)
  let t'2 ← PMem.ldI32 (in' + 20)
  let t'3 ← check_latlng t'1 t'2
  if !t'3 then
    return false
  let t'4 ← PMem.ldU16 (in' + 28)
  let t'5 ← GCS_MAVLINK.command_long_stores_location (UInt16.toUInt32 (t'4))
  if !t'5 then
    return false
  let t'6 ← PMem.ldF32 (in' + 24)
  let mut sc'8 := (Binary32.isNaN t'6)
  if !sc'8 then
    let t'7 ← PMem.ldF32 (in' + 24)
    sc'8 := (decide ((Binary32.abs t'7) > (Int32.toBinary32 ((83000 : Int32)))))
  if sc'8 then
    return false
  let t'9 ← PMem.ldU8 (in' + 32)
  let t'10 ← GCS_MAVLINK.mavlink_coordinate_frame_to_location_alt_frame this (UInt8.toUInt32 (t'9)) (fp + 0)
  if !t'10 then
    return false
  let t'11 ← PMem.ldI32 (in' + 16)
  PMem.stI32 (out + 8) t'11
  let t'12 ← PMem.ldI32 (in' + 20)
  PMem.stI32 (out + 12) t'12
  let t'13 ← PMem.ldF32 (in' + 24)
  let t'14 ← PMem.ldI32 (fp + 0)
  Location.set_alt_m out t'13 t'14
  return true

def GCS_MAVLINK.location_from_command_t (this : UInt64) (in' : UInt64) (out : UInt64) : PMem.M Bool := do
  let fp ← PMem.enter 4
  let r ← GCS_MAVLINK.location_from_command_t.body fp this in' out
  PMem.leave fp
  return r

/-- C++ `GCS_MAVLINK::handle_command_do_set_roi_location : MAV_RESULT (const mavlink_command_int_t &)`, `GCS_Common.cpp:5578-5598`. -/
def GCS_MAVLINK.handle_command_do_set_roi_location.body (fp : UInt64) (this : UInt64) (packet : UInt64) : PMem.M UInt32 := do
  let t'1 ← PMem.ldF32 packet
  if (Binary32.isInf t'1) then
    return (2 : UInt32)
  Location.Location (fp + 0)
  let t'2 ← PMem.ldU16 (packet + 28)
  let mut sc'6 := ((UInt32.toInt32 (UInt16.toUInt32 (t'2))) == (UInt32.toInt32 ((195 : UInt32))))
  if sc'6 then
    let t'3 ← GCS_MAVLINK.location_from_command_t this packet (fp + 0)
    let mut sc'5 := !t'3
    if !sc'5 then
      let t'4 ← Location.check_latlng (fp + 0)
      sc'5 := !t'4
    sc'6 := sc'5
  if sc'6 then
    return (2 : UInt32)
  let t'7 ← PMem.ldF32 packet
  let mut sc'10 := (Binary32.isNaN t'7)
  if !sc'10 then
    let t'8 ← PMem.ldF32 packet
    let t'9 ← is_zero t'8
    sc'10 := t'9
  if sc'10 then
    let t'11 ← GCS_MAVLINK_Copter.handle_command_do_set_roi this (fp + 0)
    return t'11
  return (3 : UInt32)

def GCS_MAVLINK.handle_command_do_set_roi_location (this : UInt64) (packet : UInt64) : PMem.M UInt32 := do
  let fp ← PMem.enter 16
  let r ← GCS_MAVLINK.handle_command_do_set_roi_location.body fp this packet
  PMem.leave fp
  return r

/-- C++ `GCS_MAVLINK::handle_command_do_set_roi : MAV_RESULT (const mavlink_command_int_t &)`, `GCS_Common.cpp:5557-5573`. -/
def GCS_MAVLINK.handle_command_do_set_roi.body (fp : UInt64) (this : UInt64) (packet : UInt64) : PMem.M UInt32 := do
  Location.Location (fp + 0)
  let t'1 ← GCS_MAVLINK.location_from_command_t this packet (fp + 0)
  if !t'1 then
    return (2 : UInt32)
  let t'2 ← GCS_MAVLINK_Copter.handle_command_do_set_roi this (fp + 0)
  return t'2

def GCS_MAVLINK.handle_command_do_set_roi (this : UInt64) (packet : UInt64) : PMem.M UInt32 := do
  let fp ← PMem.enter 16
  let r ← GCS_MAVLINK.handle_command_do_set_roi.body fp this packet
  PMem.leave fp
  return r

/-- C++ `GCS_MAVLINK::send_attitude : void () const`, `GCS_Common.cpp:6071-6086`. -/
def GCS_MAVLINK.send_attitude.body (fp : UInt64) (this : UInt64) : PMem.M Unit := do
  let t'1 ← VehicleBridge.ahrs'0
  let ahrs : UInt64 := t'1
  VehicleBridge.AP_AHRS.get_gyro'0 ahrs (fp + 16)
  let t'2 := (fp + 16)
  Vector3'float.Vector3'4 (fp + 0) t'2
  let t'3 ← PMem.ldU32 (this + 40)
  let t'4 ← VehicleBridge.AP_AHRS.get_roll_rad'0 ahrs
  let t'5 ← VehicleBridge.AP_AHRS.get_pitch_rad'0 ahrs
  let t'6 ← VehicleBridge.AP_AHRS.get_yaw_rad'0 ahrs
  let t'7 ← PMem.ldF32 (fp + 0)
  let t'8 ← PMem.ldF32 ((fp + 0) + 4)
  let t'9 ← PMem.ldF32 ((fp + 0) + 8)
  mavlink_msg_attitude_send t'3 (((← PMem.clock) / 1000).toUInt32) t'4 t'5 t'6 t'7 t'8 t'9
  return ()

def GCS_MAVLINK.send_attitude (this : UInt64) : PMem.M Unit := do
  let fp ← PMem.enter 28
  let r ← GCS_MAVLINK.send_attitude.body fp this
  PMem.leave fp
  return r

/-- C++ `GCS_MAVLINK::send_attitude_quaternion : void () const`, `GCS_Common.cpp:6088-6111`. -/
def GCS_MAVLINK.send_attitude_quaternion.body (fp : UInt64) (this : UInt64) : PMem.M Unit := do
  let t'1 ← VehicleBridge.ahrs'0
  let ahrs : UInt64 := t'1
  QuaternionT'float.QuaternionT (fp + 0)
  let t'2 ← VehicleBridge.AP_AHRS.get_quaternion'1 ahrs (fp + 0)
  if !t'2 then
    return ()
  VehicleBridge.AP_AHRS.get_gyro'0 ahrs (fp + 32)
  let t'3 := (fp + 32)
  Vector3'float.Vector3'4 (fp + 16) t'3
  PMem.stF32 ((fp + 48) + 0) (Int32.toBinary32 ((0 : Int32)))
  PMem.stF32 ((fp + 48) + 4) (Int32.toBinary32 ((0 : Int32)))
  PMem.stF32 ((fp + 48) + 8) (Int32.toBinary32 ((0 : Int32)))
  PMem.stF32 ((fp + 48) + 12) (Int32.toBinary32 ((0 : Int32)))
  let t'4 ← PMem.ldU32 (this + 40)
  let t'5 ← PMem.ldF32 (fp + 0)
  let t'6 ← PMem.ldF32 ((fp + 0) + 4)
  let t'7 ← PMem.ldF32 ((fp + 0) + 8)
  let t'8 ← PMem.ldF32 ((fp + 0) + 12)
  let t'9 ← PMem.ldF32 (fp + 16)
  let t'10 ← PMem.ldF32 ((fp + 16) + 4)
  let t'11 ← PMem.ldF32 ((fp + 16) + 8)
  mavlink_msg_attitude_quaternion_send t'4 (((← PMem.clock) / 1000).toUInt32) t'5 t'6 t'7 t'8 t'9 t'10 t'11 (fp + 48)
  return ()

def GCS_MAVLINK.send_attitude_quaternion (this : UInt64) : PMem.M Unit := do
  let fp ← PMem.enter 64
  let r ← GCS_MAVLINK.send_attitude_quaternion.body fp this
  PMem.leave fp
  return r

/-- C++ `GCS_MAVLINK::send_param_error : void (const GCS_MAVLINK::pending_param_reply &, MAV_PARAM_ERROR)`, `GCS_Param.cpp:451-466`. -/
def GCS_MAVLINK.send_param_error'2.body (fp : UInt64) (this : UInt64) (reply : UInt64) (error : UInt32) : PMem.M Unit := do
  let mut error := error
  let t'1 ← PMem.ldU32 (this + 40)
  let t'2 ← comm_get_txspace t'1
  let t'3 ← PMem.ldU32 (this + 40)
  let t'4 ← GCS_MAVLINK.packet_overhead_chan t'3
  let mut c'5 : Bool := default
  if (decide ((UInt16.toUInt32 (t'2)) ≥ (Int32.toUInt32 (((UInt32.toInt32 (UInt8.toUInt32 (t'4))) + (21 : Int32)))))) then
    c'5 := true
  else
    let t'6 ← PMem.ldU32 (this + 40)
    gcs_out_of_space_to_send t'6
    c'5 := false
  if !c'5 then
    return ()
  let t'7 ← strncpy_noterm (fp + 0) (reply + 16) ((16 : UInt64) / (1 : UInt64))
  discard <| pure (t'7)
  let t'8 ← PMem.ldU32 (this + 40)
  let t'9 ← PMem.ldU32 (reply + 36)
  let t'10 ← PMem.ldU8 (reply + 40)
  let t'11 ← PMem.ldI16 (reply + 12)
  mavlink_msg_param_error_send t'8 t'9 t'10 (fp + 0) t'11 (UInt32.toUInt8 (error))
  return ()

def GCS_MAVLINK.send_param_error'2 (this : UInt64) (reply : UInt64) (error : UInt32) : PMem.M Unit := do
  let fp ← PMem.enter 16
  let r ← GCS_MAVLINK.send_param_error'2.body fp this reply error
  PMem.leave fp
  return r

/-- C++ `GCS_MAVLINK::send_parameter_async_replies : uint8_t ()`, `GCS_Param.cpp:471-522`. -/
def GCS_MAVLINK.send_parameter_async_replies.body (fp : UInt64) (this : UInt64) : PMem.M UInt8 := do
  let mut async_replies_sent_count : UInt8 := Int8.toUInt8 (Int32.toInt8 ((0 : Int32)))
  for _ in PMem.loopFuel do
    if !((decide ((UInt32.toInt32 (UInt8.toUInt32 (async_replies_sent_count))) < (5 : Int32)))) then break
    GCS_MAVLINK.pending_param_reply.pending_param_reply (fp + 0)
    let t'1 ← ObjectBuffer'GCS_MAVLINK_pending_param_reply.peek (0xbed8 : UInt64) /- &GCS_MAVLINK::param_replies -/ (fp + 0)
    if !t'1 then
      return async_replies_sent_count
    let mut required_space : UInt16 := default  -- uninitialized in C
    let t'2 ← PMem.ldU32 ((fp + 0) + 44)
    if ((UInt32.toInt32 (t'2)) == (UInt32.toInt32 ((0 : UInt32)))) then
      let t'3 ← PMem.ldU32 (this + 40)
      let t'4 ← GCS_MAVLINK.packet_overhead_chan t'3
      let t'5 := UInt32.toUInt16 ((Int32.toUInt32 (((UInt32.toInt32 (UInt8.toUInt32 (t'4))) + (25 : Int32)))))
      required_space := t'5
    else
      let t'6 ← PMem.ldU32 (this + 40)
      let t'7 ← GCS_MAVLINK.packet_overhead_chan t'6
      let t'8 := UInt32.toUInt16 ((Int32.toUInt32 (((UInt32.toInt32 (UInt8.toUInt32 (t'7))) + (21 : Int32)))))
      required_space := t'8
    let t'9 ← PMem.ldU32 (0xc888 : UInt64) /- &GCS_MAVLINK::reserve_param_space_start_ms -/
    let mut saved_reserve_param_space_start_ms : UInt32 := t'9
    let t'10 := Int32.toUInt32 ((0 : Int32))
    PMem.stU32 (0xc888 : UInt64) /- &GCS_MAVLINK::reserve_param_space_start_ms -/ t'10
    let t'11 ← GCS_MAVLINK.txspace this
    if (decide ((UInt32.toInt32 (UInt16.toUInt32 (t'11))) < (UInt32.toInt32 (UInt16.toUInt32 (required_space))))) then
      GCS_MAVLINK.out_of_space_to_send this
      let t'12 := ((← PMem.clock) / 1000).toUInt32
      PMem.stU32 (0xc888 : UInt64) /- &GCS_MAVLINK::reserve_param_space_start_ms -/ t'12
      return async_replies_sent_count
    PMem.stU32 (0xc888 : UInt64) /- &GCS_MAVLINK::reserve_param_space_start_ms -/ saved_reserve_param_space_start_ms
    let t'13 ← PMem.ldU32 ((fp + 0) + 44)
    if ((UInt32.toInt32 (t'13)) == (UInt32.toInt32 ((0 : UInt32)))) then
      let t'14 ← PMem.ldU32 (fp + 0)
      let t'15 ← PMem.ldF32 ((fp + 0) + 4)
      let t'16 ← PMem.ldU32 ((fp + 0) + 8)
      let t'17 ← GCS_MAVLINK.mav_param_type t'16
      let t'18 ← PMem.ldU16 ((fp + 0) + 14)
      let t'19 ← PMem.ldI16 ((fp + 0) + 12)
      mavlink_msg_param_value_send t'14 ((fp + 0) + 16) t'15 (UInt32.toUInt8 (t'17)) t'18 (Int16.toUInt16 (t'19))
    else
      let t'20 ← PMem.ldU32 ((fp + 0) + 44)
      GCS_MAVLINK.send_param_error'2 this (fp + 0) t'20
    let t'21 := ((← PMem.clock) / 1000).toUInt32
    PMem.stU32 (this + 500) t'21
    let t'22 := async_replies_sent_count
    let t'23 := (t'22 + 1)
    async_replies_sent_count := t'23
    let t'24 ← ObjectBuffer'GCS_MAVLINK_pending_param_reply.pop (0xbed8 : UInt64) /- &GCS_MAVLINK::param_replies -/
    if !t'24 then
      return async_replies_sent_count
  return async_replies_sent_count

def GCS_MAVLINK.send_parameter_async_replies (this : UInt64) : PMem.M UInt8 := do
  let fp ← PMem.enter 48
  let r ← GCS_MAVLINK.send_parameter_async_replies.body fp this
  PMem.leave fp
  return r

/-- C++ `GCS_MAVLINK::queued_param_send : void ()`, `GCS_Param.cpp:40-100`. -/
def GCS_MAVLINK.queued_param_send.body (fp : UInt64) (this : UInt64) : PMem.M Unit := do
  let t'1 ← GCS_MAVLINK.send_parameter_async_replies this
  let mut async_replies_sent_count : UInt8 := t'1
  let t'2 ← PMem.ldU64 (this + 32)
  if (t'2 == (0 : UInt64)) then
    return ()
  let mut tnow : UInt32 := ((← PMem.clock) / 1000).toUInt32
  let mut tstart : UInt32 := (← PMem.clock).toUInt32
  let mut link_bw : UInt32 := (1000000 : UInt32)
  let t'3 ← PMem.ldU32 (this + 500)
  let mut bytes_allowed : UInt32 := ((link_bw * (tnow - t'3)) / (Int32.toUInt32 ((3333 : Int32))))
  let t'4 ← GCS_MAVLINK.packet_overhead this
  let mut size_for_one_param_value_msg : UInt16 := Int16.toUInt16 (Int32.toInt16 (((25 : Int32) + (UInt32.toInt32 (UInt8.toUInt32 (t'4))))))
  if (decide (bytes_allowed < (UInt16.toUInt32 (size_for_one_param_value_msg)))) then
    let t'5 := UInt16.toUInt32 (size_for_one_param_value_msg)
    bytes_allowed := t'5
  let t'6 ← GCS_MAVLINK.txspace this
  if (decide (bytes_allowed > (UInt16.toUInt32 (t'6)))) then
    let t'7 ← GCS_MAVLINK.txspace this
    let t'8 := UInt16.toUInt32 (t'7)
    bytes_allowed := t'8
  let mut count : UInt32 := (bytes_allowed / (UInt16.toUInt32 (size_for_one_param_value_msg)))
  let t'9 ← GCS_MAVLINK.have_flow_control this
  if ((!t'9) && (decide (count > (Int32.toUInt32 ((5 : Int32)))))) then
    let t'10 := Int32.toUInt32 ((5 : Int32))
    count := t'10
  if (decide ((UInt8.toUInt32 (async_replies_sent_count)) ≥ count)) then
    return ()
  let t'11 := (count - (UInt8.toUInt32 (async_replies_sent_count)))
  count := t'11
  for _ in PMem.loopFuel do
    let mut sc'13 := count != (0 : UInt32)
    if sc'13 then
      let t'12 ← PMem.ldU64 (this + 32)
      sc'13 := (t'12 != (0 : UInt64))
    let mut sc'15 := sc'13
    if sc'15 then
      let t'14 ← GCS_MAVLINK.last_txbuf_is_greater (Int8.toUInt8 (Int32.toInt8 ((33 : Int32))))
      sc'15 := t'14
    if !(sc'15) then break
    let t'16 ← PMem.ldU64 (this + 32)
    AP_Param.copy_name_token t'16 (this + 492) (fp + 0) (16 : UInt64) true
    let t'17 ← PMem.ldU32 (this + 40)
    let t'18 ← PMem.ldU32 (this + 488)
    let t'19 ← PMem.ldU64 (this + 32)
    let t'20 ← AP_Param.cast_to_float t'19 t'18
    let t'21 ← PMem.ldU32 (this + 488)
    let t'22 ← GCS_MAVLINK.mav_param_type t'21
    let t'23 ← PMem.ldU16 (this + 498)
    let t'24 ← PMem.ldU16 (this + 496)
    mavlink_msg_param_value_send t'17 (fp + 0) t'20 (UInt32.toUInt8 (t'22)) t'23 t'24
    let t'25 ← AP_Param.next_scalar (this + 492) (this + 488) (0 : UInt64)
    PMem.stU64 (this + 32) t'25
    let t'26 := (this + 496)
    let t'27 ← PMem.ldU16 t'26
    let t'28 := (t'27 + 1)
    PMem.stU16 t'26 t'28
    if (decide ((((← PMem.clock).toUInt32) - tstart) > (Int32.toUInt32 ((1000 : Int32))))) then
      break
    let t'29 := count
    let t'30 := (t'29 - 1)
    count := t'30
  PMem.stU32 (this + 500) tnow
  return ()

def GCS_MAVLINK.queued_param_send (this : UInt64) : PMem.M Unit := do
  let fp ← PMem.enter 16
  let r ← GCS_MAVLINK.queued_param_send.body fp this
  PMem.leave fp
  return r

/-- C++ `GCS_MAVLINK::system_status : MAV_STATE () const`, `GCS_Common.cpp:3158-3172`. -/
def GCS_MAVLINK.system_status (this : UInt64) : PMem.M UInt32 := do
  let t'1 ← GCS_MAVLINK_Copter.vehicle_system_status this
  let mut _system_status : UInt32 := t'1
  if (decide ((UInt32.toInt32 (_system_status)) < (UInt32.toInt32 ((5 : UInt32))))) then
    let t'2 := (0 : UInt64)
    let t'3 ← AP_InternalError.errors t'2
    if t'3 != (0 : UInt32) then
      _system_status := (5 : UInt32)
  return _system_status

/-- C++ `GCS_MAVLINK::send_heartbeat : void () const`, `GCS_Common.cpp:3177-3186`. -/
def GCS_MAVLINK.send_heartbeat (this : UInt64) : PMem.M Unit := do
  let t'1 ← PMem.ldU32 (this + 40)
  let t'2 ← gcs
  let t'3 ← GCS_Copter.frame_type t'2
  let t'4 ← GCS_MAVLINK_Copter.base_mode this
  let t'5 ← gcs
  let t'6 ← GCS_Copter.custom_mode t'5
  let t'7 ← GCS_MAVLINK.system_status this
  mavlink_msg_heartbeat_send t'1 (UInt32.toUInt8 (t'3)) (UInt32.toUInt8 ((3 : UInt32))) t'4 t'6 (UInt32.toUInt8 (t'7))
  return ()

/-- C++ `GCS_MAVLINK::send_global_position_int : void ()`, `GCS_Common.cpp:6127-6151`. -/
def GCS_MAVLINK.send_global_position_int.body (fp : UInt64) (this : UInt64) : PMem.M Unit := do
  let t'1 ← VehicleBridge.ahrs'0
  let ahrs : UInt64 := t'1
  for _ in [0:1] do
    let mut __unique_name___COUNTER__ : Bool := default  -- uninitialized in C
    let t'2 ← VehicleBridge.AP_AHRS.get_location'1 ahrs (this + 840)
    __unique_name___COUNTER__ := t'2
  Vector3'float.Vector3'2 (fp + 0)
  let t'3 ← VehicleBridge.AP_AHRS.get_velocity_NED'1 ahrs (fp + 0)
  if !t'3 then
    Vector3'float.zero (fp + 0)
  let t'4 ← PMem.ldU32 (this + 40)
  let t'5 ← PMem.ldI32 ((this + 840) + 8)
  let t'6 ← PMem.ldI32 ((this + 840) + 12)
  let t'7 ← GCS_MAVLINK.global_position_int_alt this
  let t'8 ← GCS_MAVLINK.global_position_int_relative_alt this
  let t'9 ← PMem.ldF32 (fp + 0)
  let t'10 ← PMem.ldF32 ((fp + 0) + 4)
  let t'11 ← PMem.ldF32 ((fp + 0) + 8)
  let t'12 ← VehicleBridge.AP_AHRS.yaw_sensor'field ahrs
  mavlink_msg_global_position_int_send t'4 (((← PMem.clock) / 1000).toUInt32) t'5 t'6 t'7 t'8 (Binary32.toInt16 ((t'9 * (Int32.toBinary32 ((100 : Int32)))))) (Binary32.toInt16 ((t'10 * (Int32.toBinary32 ((100 : Int32)))))) (Binary32.toInt16 ((t'11 * (Int32.toBinary32 ((100 : Int32)))))) (Int16.toUInt16 (Int32.toInt16 (t'12)))
  return ()

def GCS_MAVLINK.send_global_position_int (this : UInt64) : PMem.M Unit := do
  let fp ← PMem.enter 12
  let r ← GCS_MAVLINK.send_global_position_int.body fp this
  PMem.leave fp
  return r

/-- C++ `GCS_MAVLINK::send_home_position : void () const`, `GCS_Common.cpp:3111-3141`. -/
def GCS_MAVLINK.send_home_position.body (fp : UInt64) (this : UInt64) : PMem.M Unit := do
  let t'1 ← VehicleBridge.ahrs'0
  let t'2 ← VehicleBridge.AP_AHRS.home_is_set'0 t'1
  if !t'2 then
    return ()
  let t'3 ← VehicleBridge.ahrs'0
  VehicleBridge.AP_AHRS.get_home'0 t'3 (fp + 0)
  let t'4 := (fp + 0)
  let home : UInt64 := t'4
  Vector3'float.Vector3'2 (fp + 16)
  let t'5 ← Location.get_vector_from_origin_NEU_cm'Vector3_float home (fp + 16)
  if t'5 then
    let t'6 ← Vector3'float.operator__'2 (fp + 16) (Binary32.ofBits 0x3c23d70a /- 999999977/100000000000 -/)
    discard <| pure (t'6)
    let t'7 := ((fp + 16) + 8)
    let t'8 ← PMem.ldF32 t'7
    let t'9 := (t'8 * (Int32.toBinary32 ((-(1 : Int32)))))
    PMem.stF32 t'7 t'9
  else
    Vector3'float.Vector3 (fp + 32) (Binary32.ofBits 0x7fc00000) (Binary32.ofBits 0x7fc00000) (Binary32.ofBits 0x7fc00000)
    discard <| PMem.memcpy (fp + 16) (fp + 32) 12
    discard <| pure ((fp + 16))
  PMem.stF32 ((fp + 48) + 0) (Binary32.ofBits 0x7fc00000)
  PMem.stF32 ((fp + 48) + 4) (Binary32.ofBits 0x7fc00000)
  PMem.stF32 ((fp + 48) + 8) (Binary32.ofBits 0x7fc00000)
  PMem.stF32 ((fp + 48) + 12) (Binary32.ofBits 0x7fc00000)
  let t'10 ← PMem.ldU32 (this + 40)
  let t'11 ← PMem.ldI32 (home + 8)
  let t'12 ← PMem.ldI32 (home + 12)
  let t'13 ← PMem.ldI32 (home + 4)
  let t'14 ← PMem.ldF32 (fp + 16)
  let t'15 ← PMem.ldF32 ((fp + 16) + 4)
  let t'16 ← PMem.ldF32 ((fp + 16) + 8)
  mavlink_msg_home_position_send t'10 t'11 t'12 (t'13 * (10 : Int32)) t'14 t'15 t'16 (fp + 48) (Binary32.ofBits 0x00000000 /- 0 -/) (Binary32.ofBits 0x00000000 /- 0 -/) (Binary32.ofBits 0x00000000 /- 0 -/) (← PMem.clock)
  return ()

def GCS_MAVLINK.send_home_position (this : UInt64) : PMem.M Unit := do
  let fp ← PMem.enter 64
  let r ← GCS_MAVLINK.send_home_position.body fp this
  PMem.leave fp
  return r

/-- C++ `GCS_MAVLINK::send_gps_global_origin : void () const`, `GCS_Common.cpp:3143-3155`. -/
def GCS_MAVLINK.send_gps_global_origin.body (fp : UInt64) (this : UInt64) : PMem.M Unit := do
  Location.Location (fp + 0)
  let t'1 ← VehicleBridge.ahrs'0
  let t'2 ← VehicleBridge.AP_AHRS.get_origin'1 t'1 (fp + 0)
  if !t'2 then
    return ()
  let t'3 ← PMem.ldU32 (this + 40)
  let t'4 ← PMem.ldI32 ((fp + 0) + 8)
  let t'5 ← PMem.ldI32 ((fp + 0) + 12)
  let t'6 ← PMem.ldI32 ((fp + 0) + 4)
  mavlink_msg_gps_global_origin_send t'3 t'4 t'5 (t'6 * (10 : Int32)) (← PMem.clock)
  return ()

def GCS_MAVLINK.send_gps_global_origin (this : UInt64) : PMem.M Unit := do
  let fp ← PMem.enter 16
  let r ← GCS_MAVLINK.send_gps_global_origin.body fp this
  PMem.leave fp
  return r

/-- C++ `GCS::try_send_queued_message_for_type : void (MAV_MISSION_TYPE) const`, `GCS_Common.cpp:5924-5930`. -/
def GCS.try_send_queued_message_for_type (this : UInt64) (type' : UInt32) : PMem.M Unit := do
  let mut type' := type'
  let t'1 ← GCS.get_prot_for_mission_type this type'
  let mut prot : UInt64 := t'1
  if (prot == (0 : UInt64)) then
    return ()
  MissionItemProtocol.queued_request_send prot
  return ()

/-- C++ `GCS_MAVLINK::try_send_mission_message : bool (const enum ap_message)`, `GCS_Common.cpp:5932-5968`. -/
def GCS_MAVLINK.try_send_mission_message (this : UInt64) (id : UInt8) : PMem.M Bool := do
  let mut id := id
  for _ in [0:1] do
    let sw'1 := UInt32.toInt32 (UInt8.toUInt32 (id))
    if sw'1 == (11 : Int32) then
      let t'2 ← GCS_MAVLINK.check_payload_size this (Int16.toUInt16 (Int32.toInt16 ((6 : Int32))))
      if !t'2 then
        return false
      let t'3 ← AP.mission
      let mission : UInt64 := t'3
      let t'4 ← AP_Mission.get_current_nav_index mission
      GCS_MAVLINK.send_mission_current this mission t'4
      break
      let t'5 ← GCS_MAVLINK.check_payload_size this (Int16.toUInt16 (Int32.toInt16 ((2 : Int32))))
      if !t'5 then
        return false
      let t'6 ← PMem.ldU32 (this + 40)
      let t'7 ← PMem.ldU16 (this + 12)
      mavlink_msg_mission_item_reached_send t'6 t'7
    else if sw'1 == (61 : Int32) then
      let t'8 ← GCS_MAVLINK.check_payload_size this (Int16.toUInt16 (Int32.toInt16 ((2 : Int32))))
      if !t'8 then
        return false
      let t'9 ← PMem.ldU32 (this + 40)
      let t'10 ← PMem.ldU16 (this + 12)
      mavlink_msg_mission_item_reached_send t'9 t'10
    else if sw'1 == (28 : Int32) then
      let t'11 ← GCS_MAVLINK.check_payload_size this (Int16.toUInt16 (Int32.toInt16 ((5 : Int32))))
      if !t'11 then
        return false
      let t'12 ← gcs
      GCS.try_send_queued_message_for_type t'12 (0 : UInt32)
    else
      pure ()
  return true

/-- C++ `GCS_MAVLINK::battery_remaining_pct : int8_t (const uint8_t) const`, `GCS_Common.cpp:303-306`. -/
def GCS_MAVLINK.battery_remaining_pct.body (fp : UInt64) (this : UInt64) (instance' : UInt8) : PMem.M Int8 := do
  let mut instance' := instance'
  let t'1 ← AP.battery
  let t'2 ← AP_BattMonitor.capacity_remaining_pct t'1 (fp + 0) instance'
  let mut c'3 : Int32 := default
  if t'2 then
    PMem.stI32 (fp + 4) (127 : Int32)
    let t'4 ← MIN'unsigned_char_int (fp + 0) (fp + 4)
    c'3 := t'4
  else
    c'3 := -(1 : Int32)
  return Int32.toInt8 (c'3)

def GCS_MAVLINK.battery_remaining_pct (this : UInt64) (instance' : UInt8) : PMem.M Int8 := do
  let fp ← PMem.enter 8
  let r ← GCS_MAVLINK.battery_remaining_pct.body fp this instance'
  PMem.leave fp
  return r

/-- C++ `GCS_MAVLINK::send_battery_status : void (const uint8_t) const`, `GCS_Common.cpp:308-427`. -/
def GCS_MAVLINK.send_battery_status'2.body (fp : UInt64) (this : UInt64) (instance' : UInt8) : PMem.M Unit := do
  let mut instance' := instance'
  let t'1 ← AP.battery
  let battery : UInt64 := t'1
  let t'2 ← AP_BattMonitor.get_temperature battery (fp + 0) instance'
  let mut got_temperature : Bool := t'2
  PMem.stU16 (fp + 40) (UInt32.toUInt16 ((65534 : UInt32)))
  let mut invalid_cell_mV : UInt16 := UInt32.toUInt16 ((65535 : UInt32))
  let t'3 ← AP_BattMonitor.has_cell_voltages battery instance'
  if t'3 then
    let t'4 ← AP_BattMonitor.get_cell_voltages battery instance'
    let batt_cells : UInt64 := t'4
    let t'5 ← PMem.memcpy (fp + 8) batt_cells (20 : UInt64)
    discard <| pure (t'5)
    for i'6 in [0:4] do
      let i : UInt8 := UInt8.ofNat i'6
      if (decide (((10 : Int32) + (UInt32.toInt32 (UInt8.toUInt32 (i)))) < (UInt32.toInt32 (UInt8.toUInt32 ((UInt64.toUInt8 (((28 : UInt64) / (2 : UInt64))))))))) then
        let t'7 ← PMem.ldU16 (batt_cells + ((Int32.toInt64 (((10 : Int32) + (UInt32.toInt32 (UInt8.toUInt32 (i)))))) * 2).toUInt64)
        PMem.stU16 ((fp + 32) + ((UInt64.toInt64 (UInt8.toUInt64 (i))) * 2).toUInt64) t'7
      else
        let t'8 := Int16.toUInt16 (Int32.toInt16 ((0 : Int32)))
        PMem.stU16 ((fp + 32) + ((UInt64.toInt64 (UInt8.toUInt64 (i))) * 2).toUInt64) t'8
    let t'9 ← AP_BattMonitor.gcs_voltage'2 battery instance'
    let mut voltage_mV : Binary32 := (t'9 * (Binary32.ofBits 0x447a0000 /- 1000 -/))
    let mut voltage_mV_sum : Binary32 := Int32.toBinary32 ((0 : Int32))
    let mut non_zero_cell_count : UInt8 := Int8.toUInt8 (Int32.toInt8 ((0 : Int32)))
    for i'2'10 in [0:10] do
      let i'2 : UInt8 := UInt8.ofNat i'2'10
      let t'11 ← PMem.ldU16 ((fp + 8) + ((UInt64.toInt64 (UInt8.toUInt64 (i'2))) * 2).toUInt64)
      let mut sc'13 := (decide ((UInt32.toInt32 (UInt16.toUInt32 (t'11))) > (0 : Int32)))
      if sc'13 then
        let t'12 ← PMem.ldU16 ((fp + 8) + ((UInt64.toInt64 (UInt8.toUInt64 (i'2))) * 2).toUInt64)
        sc'13 := ((UInt32.toInt32 (UInt16.toUInt32 (t'12))) != (UInt32.toInt32 (UInt16.toUInt32 (invalid_cell_mV))))
      if sc'13 then
        let t'14 := non_zero_cell_count
        let t'15 := (t'14 + 1)
        non_zero_cell_count := t'15
        let t'16 ← PMem.ldU16 ((fp + 8) + ((UInt64.toInt64 (UInt8.toUInt64 (i'2))) * 2).toUInt64)
        let t'17 := (voltage_mV_sum + (Int32.toBinary32 ((UInt32.toInt32 (UInt16.toUInt32 (t'16))))))
        voltage_mV_sum := t'17
    for i'3'18 in [0:4] do
      let i'3 : UInt8 := UInt8.ofNat i'3'18
      let t'19 ← PMem.ldU16 ((fp + 32) + ((UInt64.toInt64 (UInt8.toUInt64 (i'3))) * 2).toUInt64)
      let mut sc'21 := (decide ((UInt32.toInt32 (UInt16.toUInt32 (t'19))) > (0 : Int32)))
      if sc'21 then
        let t'20 ← PMem.ldU16 ((fp + 32) + ((UInt64.toInt64 (UInt8.toUInt64 (i'3))) * 2).toUInt64)
        sc'21 := ((UInt32.toInt32 (UInt16.toUInt32 (t'20))) != (UInt32.toInt32 (UInt16.toUInt32 (invalid_cell_mV))))
      if sc'21 then
        let t'22 := non_zero_cell_count
        let t'23 := (t'22 + 1)
        non_zero_cell_count := t'23
        let t'24 ← PMem.ldU16 ((fp + 32) + ((UInt64.toInt64 (UInt8.toUInt64 (i'3))) * 2).toUInt64)
        let t'25 := (voltage_mV_sum + (Int32.toBinary32 ((UInt32.toInt32 (UInt16.toUInt32 (t'24))))))
        voltage_mV_sum := t'25
    if ((decide (voltage_mV > voltage_mV_sum)) && (decide ((UInt32.toInt32 (UInt8.toUInt32 (non_zero_cell_count))) > (0 : Int32)))) then
      let mut extra_mV : UInt32 := Binary32.toUInt32 (((voltage_mV - voltage_mV_sum) / (Int32.toBinary32 ((UInt32.toInt32 (UInt8.toUInt32 (non_zero_cell_count)))))))
      for i'4'26 in [0:10] do
        let i'4 : UInt8 := UInt8.ofNat i'4'26
        let t'27 ← PMem.ldU16 ((fp + 8) + ((UInt64.toInt64 (UInt8.toUInt64 (i'4))) * 2).toUInt64)
        let mut sc'29 := (decide ((UInt32.toInt32 (UInt16.toUInt32 (t'27))) > (0 : Int32)))
        if sc'29 then
          let t'28 ← PMem.ldU16 ((fp + 8) + ((UInt64.toInt64 (UInt8.toUInt64 (i'4))) * 2).toUInt64)
          sc'29 := ((UInt32.toInt32 (UInt16.toUInt32 (t'28))) != (UInt32.toInt32 (UInt16.toUInt32 (invalid_cell_mV))))
        if sc'29 then
          let t'30 ← PMem.ldU16 ((fp + 8) + ((UInt64.toInt64 (UInt8.toUInt64 (i'4))) * 2).toUInt64)
          PMem.stU32 (fp + 44) ((UInt16.toUInt32 (t'30)) + extra_mV)
          let t'31 ← MIN'unsigned_int_unsigned_short (fp + 44) (fp + 40)
          let t'32 := UInt32.toUInt16 (t'31)
          PMem.stU16 ((fp + 8) + ((UInt64.toInt64 (UInt8.toUInt64 (i'4))) * 2).toUInt64) t'32
      for i'5'33 in [0:4] do
        let i'5 : UInt8 := UInt8.ofNat i'5'33
        let t'34 ← PMem.ldU16 ((fp + 32) + ((UInt64.toInt64 (UInt8.toUInt64 (i'5))) * 2).toUInt64)
        let mut sc'36 := (decide ((UInt32.toInt32 (UInt16.toUInt32 (t'34))) > (0 : Int32)))
        if sc'36 then
          let t'35 ← PMem.ldU16 ((fp + 32) + ((UInt64.toInt64 (UInt8.toUInt64 (i'5))) * 2).toUInt64)
          sc'36 := ((UInt32.toInt32 (UInt16.toUInt32 (t'35))) != (UInt32.toInt32 (UInt16.toUInt32 (invalid_cell_mV))))
        if sc'36 then
          let t'37 ← PMem.ldU16 ((fp + 32) + ((UInt64.toInt64 (UInt8.toUInt64 (i'5))) * 2).toUInt64)
          PMem.stU32 (fp + 48) ((UInt16.toUInt32 (t'37)) + extra_mV)
          let t'38 ← MIN'unsigned_int_unsigned_short (fp + 48) (fp + 40)
          let t'39 := UInt32.toUInt16 (t'38)
          PMem.stU16 ((fp + 32) + ((UInt64.toInt64 (UInt8.toUInt64 (i'5))) * 2).toUInt64) t'39
  else
    let t'40 ← AP_BattMonitor.gcs_voltage'2 battery instance'
    PMem.stF32 (fp + 56) (t'40 * (Binary32.ofBits 0x447a0000 /- 1000 -/))
    for i'6'41 in [0:10] do
      let i'6 : UInt8 := UInt8.ofNat i'6'41
      let t'42 ← PMem.ldF32 (fp + 56)
      if (decide (t'42 < (Binary32.ofBits 0x3a83126f /- 20000001/20000000000 -/))) then
        let t'43 := Int16.toUInt16 (Int32.toInt16 ((65535 : Int32)))
        PMem.stU16 ((fp + 8) + ((UInt64.toInt64 (UInt8.toUInt64 (i'6))) * 2).toUInt64) t'43
      else
        let t'44 ← MIN'float_unsigned_short (fp + 56) (fp + 40)
        let t'45 := Binary32.toUInt16 (t'44)
        PMem.stU16 ((fp + 8) + ((UInt64.toInt64 (UInt8.toUInt64 (i'6))) * 2).toUInt64) t'45
        let t'46 ← PMem.ldF32 (fp + 56)
        let t'47 ← PMem.ldU16 (fp + 40)
        let t'48 := (t'46 - (Int32.toBinary32 ((UInt32.toInt32 (UInt16.toUInt32 (t'47))))))
        PMem.stF32 (fp + 56) t'48
    for i'7'49 in [0:4] do
      let i'7 : UInt8 := UInt8.ofNat i'7'49
      let t'50 := Int16.toUInt16 (Int32.toInt16 ((0 : Int32)))
      PMem.stU16 ((fp + 32) + ((UInt64.toInt64 (UInt8.toUInt64 (i'7))) * 2).toUInt64) t'50
  let t'51 ← GCS_MAVLINK.battery_remaining_pct this instance'
  let mut percentage : Int8 := t'51
  let t'52 ← AP_BattMonitor.current_amps battery (fp + 64) instance'
  if t'52 then
    let t'53 ← PMem.ldF32 (fp + 64)
    let t'54 ← constrain_value_line'float (t'53 * (Int32.toBinary32 ((100 : Int32)))) (Int32.toBinary32 ((-(32767 : Int32)))) (Int32.toBinary32 ((32767 : Int32))) (Int32.toUInt32 ((395 : Int32)))
    PMem.stF32 (fp + 64) t'54
  else
    let t'55 := Int32.toBinary32 ((-(1 : Int32)))
    PMem.stF32 (fp + 64) t'55
  let t'56 ← AP_BattMonitor.consumed_mah battery (fp + 72) instance'
  if !t'56 then
    let t'57 := Int32.toBinary32 ((-(1 : Int32)))
    PMem.stF32 (fp + 72) t'57
  let t'58 ← AP_BattMonitor.consumed_wh battery (fp + 80) instance'
  if t'58 then
    let t'59 ← PMem.ldF32 (fp + 80)
    let t'60 := (t'59 * (Int32.toBinary32 ((36 : Int32))))
    PMem.stF32 (fp + 80) t'60
  else
    let t'61 := Int32.toBinary32 ((-(1 : Int32)))
    PMem.stF32 (fp + 80) t'61
  let t'62 ← AP_BattMonitor.time_remaining battery (fp + 88) instance'
  if !t'62 then
    let t'63 := Int32.toUInt32 ((0 : Int32))
    PMem.stU32 (fp + 88) t'63
  let t'64 ← PMem.ldU32 (this + 40)
  let mut c'65 : Int32 := default
  if got_temperature then
    let t'66 ← PMem.ldF32 (fp + 0)
    c'65 := Int16.toInt32 ((Binary32.toInt16 ((t'66 * (Int32.toBinary32 ((100 : Int32)))))))
  else
    c'65 := (32767 : Int32)
  let t'67 ← PMem.ldF32 (fp + 64)
  let t'68 ← PMem.ldF32 (fp + 72)
  let t'69 ← PMem.ldF32 (fp + 80)
  let t'70 ← constrain_int16 (Int8.toInt16 (percentage)) (Int32.toInt16 ((-(1 : Int32)))) (Int32.toInt16 ((100 : Int32)))
  let t'71 ← PMem.ldU32 (fp + 88)
  let t'72 ← AP_BattMonitor.get_mavlink_charge_state battery instance'
  let t'73 ← AP_BattMonitor.get_mavlink_fault_bitmask battery instance'
  mavlink_msg_battery_status_send t'64 instance' (UInt32.toUInt8 ((0 : UInt32))) (UInt32.toUInt8 ((0 : UInt32))) (Int32.toInt16 (c'65)) (fp + 8) (Binary32.toInt16 (t'67)) (Binary32.toInt32 (t'68)) (Binary32.toInt32 (t'69)) (Int16.toInt8 (t'70)) (UInt32.toInt32 (t'71)) (UInt32.toUInt8 (t'72)) (fp + 32) (Int8.toUInt8 (Int32.toInt8 ((0 : Int32)))) t'73
  return ()

def GCS_MAVLINK.send_battery_status'2 (this : UInt64) (instance' : UInt8) : PMem.M Unit := do
  let fp ← PMem.enter 92
  let r ← GCS_MAVLINK.send_battery_status'2.body fp this instance'
  PMem.leave fp
  return r

/-- C++ `GCS_MAVLINK::send_battery_status : bool ()`, `GCS_Common.cpp:430-449`. -/
def GCS_MAVLINK.send_battery_status (this : UInt64) : PMem.M Bool := do
  let t'1 ← AP.battery
  let battery : UInt64 := t'1
  for i'2 in [0:9] do
    let i : UInt8 := UInt8.ofNat i'2
    let t'3 ← PMem.ldU8 (this + 868)
    let mut battery_id : UInt8 := Int8.toUInt8 (Int32.toInt8 ((((UInt32.toInt32 (UInt8.toUInt32 (t'3))) + (1 : Int32)) % (9 : Int32))))
    let t'4 ← AP_BattMonitor.configured_type battery battery_id
    let mut configured_type : Int32 := t'4
    let mut sc'6 := (configured_type != (0 : Int32))
    if sc'6 then
      let t'5 ← AP_BattMonitor.allocated_type battery battery_id
      sc'6 := (configured_type == t'5)
    let mut sc'8 := sc'6
    if sc'8 then
      let t'7 ← AP_BattMonitor.option_is_set battery battery_id (256 : UInt16)
      sc'8 := !t'7
    if sc'8 then
      let t'9 ← GCS_MAVLINK.check_payload_size this (Int16.toUInt16 (Int32.toInt16 ((54 : Int32))))
      if !t'9 then
        return false
      GCS_MAVLINK.send_battery_status'2 this battery_id
      PMem.stU8 (this + 868) battery_id
      return true
    else
      PMem.stU8 (this + 868) battery_id
  return true

/-- C++ `GCS_MAVLINK::send_meminfo : void ()`, `GCS_Common.cpp:250-255`. -/
def GCS_MAVLINK.send_meminfo.body (fp : UInt64) (this : UInt64) : PMem.M Unit := do
  let mut __brkval : UInt32 := Int32.toUInt32 ((0 : Int32))
  let t'1 ← PMem.ldU64 ((0xba88 : UInt64) /- &hal -/ + 88)
  let t'2 ← PMem.halDev "AP_HAL::Util::available_memory" t'1 #[]
  PMem.stU32 (fp + 0) (UInt64.toUInt32 (t'2))
  let t'3 ← PMem.ldU32 (this + 40)
  PMem.stU32 (fp + 4) (65535 : UInt32)
  let t'4 ← MIN'unsigned_int_unsigned_int (fp + 0) (fp + 4)
  let t'5 ← PMem.ldU32 t'4
  let t'6 ← PMem.ldU32 (fp + 0)
  mavlink_msg_meminfo_send t'3 (UInt32.toUInt16 (__brkval)) (UInt32.toUInt16 (t'5)) t'6
  return ()

def GCS_MAVLINK.send_meminfo (this : UInt64) : PMem.M Unit := do
  let fp ← PMem.enter 8
  let r ← GCS_MAVLINK.send_meminfo.body fp this
  PMem.leave fp
  return r

/-- C++ `GCS_MAVLINK::send_system_time : void () const`, `GCS_Common.cpp:2150-2161`. -/
def GCS_MAVLINK.send_system_time.body (fp : UInt64) (this : UInt64) : PMem.M Unit := do
  PMem.stU64 (fp + 0) (Int64.toUInt64 (Int32.toInt64 ((0 : Int32))))
  let t'1 ← VehicleBridge.rtc'0
  let t'2 ← VehicleBridge.AP_RTC.get_utc_usec'1 t'1 (fp + 0)
  discard <| pure (t'2)
  let t'3 ← PMem.ldU32 (this + 40)
  let t'4 ← PMem.ldU64 (fp + 0)
  mavlink_msg_system_time_send t'3 t'4 (((← PMem.clock) / 1000).toUInt32)
  return ()

def GCS_MAVLINK.send_system_time (this : UInt64) : PMem.M Unit := do
  let fp ← PMem.enter 8
  let r ← GCS_MAVLINK.send_system_time.body fp this
  PMem.leave fp
  return r

/-- C++ `GCS_MAVLINK::send_local_position : void () const`, `GCS_Common.cpp:3051-3071`. -/
def GCS_MAVLINK.send_local_position.body (fp : UInt64) (this : UInt64) : PMem.M Unit := do
  let t'1 ← VehicleBridge.ahrs'0
  let ahrs : UInt64 := t'1
  Vector3'float.Vector3'2 (fp + 0)
  Vector3'float.Vector3'2 (fp + 16)
  let t'2 ← VehicleBridge.AP_AHRS.get_relative_position_NED_origin_float'1 ahrs (fp + 0)
  let mut sc'4 := !t'2
  if !sc'4 then
    let t'3 ← VehicleBridge.AP_AHRS.get_velocity_NED'1 ahrs (fp + 16)
    sc'4 := !t'3
  if sc'4 then
    return ()
  let t'5 ← PMem.ldU32 (this + 40)
  let t'6 ← PMem.ldF32 (fp + 0)
  let t'7 ← PMem.ldF32 ((fp + 0) + 4)
  let t'8 ← PMem.ldF32 ((fp + 0) + 8)
  let t'9 ← PMem.ldF32 (fp + 16)
  let t'10 ← PMem.ldF32 ((fp + 16) + 4)
  let t'11 ← PMem.ldF32 ((fp + 16) + 8)
  mavlink_msg_local_position_ned_send t'5 (((← PMem.clock) / 1000).toUInt32) t'6 t'7 t'8 t'9 t'10 t'11
  return ()

def GCS_MAVLINK.send_local_position (this : UInt64) : PMem.M Unit := do
  let fp ← PMem.enter 28
  let r ← GCS_MAVLINK.send_local_position.body fp this
  PMem.leave fp
  return r

/-- C++ `GCS_MAVLINK::send_power_status : void ()`, `GCS_Common.cpp:258-268`. -/
def GCS_MAVLINK.send_power_status (this : UInt64) : PMem.M Unit := do
  let t'1 ← gcs
  let t'2 ← GCS_Copter.vehicle_initialised t'1
  if !t'2 then
    return ()
  let t'3 ← PMem.ldU32 (this + 40)
  let t'4 ← PMem.ldU64 ((0xba88 : UInt64) /- &hal -/ + 32)
  let t'5 ← PMem.halDev "AP_HAL::AnalogIn::board_voltage" t'4 #[]
  let t'6 ← PMem.ldU64 ((0xba88 : UInt64) /- &hal -/ + 32)
  let t'7 ← PMem.halDev "AP_HAL::AnalogIn::servorail_voltage" t'6 #[]
  let t'8 ← PMem.ldU64 ((0xba88 : UInt64) /- &hal -/ + 32)
  let t'9 ← PMem.halDev "AP_HAL::AnalogIn::power_status_flags" t'8 #[]
  mavlink_msg_power_status_send t'3 (Binary32.toUInt16 (((Binary32.ofBits t'5.toUInt32) * (Int32.toBinary32 ((1000 : Int32)))))) (Binary32.toUInt16 (((Binary32.ofBits t'7.toUInt32) * (Int32.toBinary32 ((1000 : Int32)))))) (UInt64.toUInt16 (t'9))
  return ()

/-- C++ `GCS_MAVLINK::send_rc_channels : void () const`, `GCS_Common.cpp:2173-2206`. -/
def GCS_MAVLINK.send_rc_channels.body (fp : UInt64) (this : UInt64) : PMem.M Unit := do
  let t'1 ← rc
  let t'2 ← RC_Channels.get_radio_in t'1 (fp + 0) (UInt64.toUInt8 (((36 : UInt64) / (2 : UInt64))))
  discard <| pure (t'2)
  let t'3 ← PMem.ldU32 (this + 40)
  let t'4 ← RC_Channels.get_valid_channel_count
  let t'5 ← PMem.ldU16 ((fp + 0) + ((Int32.toInt64 ((0 : Int32))) * 2).toUInt64)
  let t'6 ← PMem.ldU16 ((fp + 0) + ((Int32.toInt64 ((1 : Int32))) * 2).toUInt64)
  let t'7 ← PMem.ldU16 ((fp + 0) + ((Int32.toInt64 ((2 : Int32))) * 2).toUInt64)
  let t'8 ← PMem.ldU16 ((fp + 0) + ((Int32.toInt64 ((3 : Int32))) * 2).toUInt64)
  let t'9 ← PMem.ldU16 ((fp + 0) + ((Int32.toInt64 ((4 : Int32))) * 2).toUInt64)
  let t'10 ← PMem.ldU16 ((fp + 0) + ((Int32.toInt64 ((5 : Int32))) * 2).toUInt64)
  let t'11 ← PMem.ldU16 ((fp + 0) + ((Int32.toInt64 ((6 : Int32))) * 2).toUInt64)
  let t'12 ← PMem.ldU16 ((fp + 0) + ((Int32.toInt64 ((7 : Int32))) * 2).toUInt64)
  let t'13 ← PMem.ldU16 ((fp + 0) + ((Int32.toInt64 ((8 : Int32))) * 2).toUInt64)
  let t'14 ← PMem.ldU16 ((fp + 0) + ((Int32.toInt64 ((9 : Int32))) * 2).toUInt64)
  let t'15 ← PMem.ldU16 ((fp + 0) + ((Int32.toInt64 ((10 : Int32))) * 2).toUInt64)
  let t'16 ← PMem.ldU16 ((fp + 0) + ((Int32.toInt64 ((11 : Int32))) * 2).toUInt64)
  let t'17 ← PMem.ldU16 ((fp + 0) + ((Int32.toInt64 ((12 : Int32))) * 2).toUInt64)
  let t'18 ← PMem.ldU16 ((fp + 0) + ((Int32.toInt64 ((13 : Int32))) * 2).toUInt64)
  let t'19 ← PMem.ldU16 ((fp + 0) + ((Int32.toInt64 ((14 : Int32))) * 2).toUInt64)
  let t'20 ← PMem.ldU16 ((fp + 0) + ((Int32.toInt64 ((15 : Int32))) * 2).toUInt64)
  let t'21 ← PMem.ldU16 ((fp + 0) + ((Int32.toInt64 ((16 : Int32))) * 2).toUInt64)
  let t'22 ← PMem.ldU16 ((fp + 0) + ((Int32.toInt64 ((17 : Int32))) * 2).toUInt64)
  mavlink_msg_rc_channels_send t'3 (((← PMem.clock) / 1000).toUInt32) t'4 t'5 t'6 t'7 t'8 t'9 t'10 t'11 t'12 t'13 t'14 t'15 t'16 t'17 t'18 t'19 t'20 t'21 t'22 (Int8.toUInt8 (Int32.toInt8 ((255 : Int32))))
  return ()

def GCS_MAVLINK.send_rc_channels (this : UInt64) : PMem.M Unit := do
  let fp ← PMem.enter 36
  let r ← GCS_MAVLINK.send_rc_channels.body fp this
  PMem.leave fp
  return r

/-- C++ `GCS_MAVLINK::send_rc_channels_raw : void () const`, `GCS_Common.cpp:2209-2238`. -/
def GCS_MAVLINK.send_rc_channels_raw.body (fp : UInt64) (this : UInt64) : PMem.M Unit := do
  let t'1 ← GCS_MAVLINK.sending_mavlink1 this
  if !t'1 then
    return ()
  let t'2 ← rc
  let t'3 ← RC_Channels.get_radio_in t'2 (fp + 0) (UInt64.toUInt8 (((16 : UInt64) / (2 : UInt64))))
  discard <| pure (t'3)
  let t'4 ← PMem.ldU32 (this + 40)
  let t'5 ← PMem.ldU16 ((fp + 0) + ((Int32.toInt64 ((0 : Int32))) * 2).toUInt64)
  let t'6 ← PMem.ldU16 ((fp + 0) + ((Int32.toInt64 ((1 : Int32))) * 2).toUInt64)
  let t'7 ← PMem.ldU16 ((fp + 0) + ((Int32.toInt64 ((2 : Int32))) * 2).toUInt64)
  let t'8 ← PMem.ldU16 ((fp + 0) + ((Int32.toInt64 ((3 : Int32))) * 2).toUInt64)
  let t'9 ← PMem.ldU16 ((fp + 0) + ((Int32.toInt64 ((4 : Int32))) * 2).toUInt64)
  let t'10 ← PMem.ldU16 ((fp + 0) + ((Int32.toInt64 ((5 : Int32))) * 2).toUInt64)
  let t'11 ← PMem.ldU16 ((fp + 0) + ((Int32.toInt64 ((6 : Int32))) * 2).toUInt64)
  let t'12 ← PMem.ldU16 ((fp + 0) + ((Int32.toInt64 ((7 : Int32))) * 2).toUInt64)
  mavlink_msg_rc_channels_raw_send t'4 (((← PMem.clock) / 1000).toUInt32) (Int8.toUInt8 (Int32.toInt8 ((0 : Int32)))) t'5 t'6 t'7 t'8 t'9 t'10 t'11 t'12 (Int8.toUInt8 (Int32.toInt8 ((255 : Int32))))
  return ()

def GCS_MAVLINK.send_rc_channels_raw (this : UInt64) : PMem.M Unit := do
  let fp ← PMem.enter 16
  let r ← GCS_MAVLINK.send_rc_channels_raw.body fp this
  PMem.leave fp
  return r

/-- C++ `GCS_MAVLINK::send_raw_imu : void ()`, `GCS_Common.cpp:2242-2272`. -/
def GCS_MAVLINK.send_raw_imu.body (fp : UInt64) (this : UInt64) : PMem.M Unit := do
  let t'1 ← VehicleBridge.ins'0
  let ins : UInt64 := t'1
  VehicleBridge.AP_InertialSensor.get_accel'1 ins (fp + 0) (Int8.toUInt8 (Int32.toInt8 ((0 : Int32))))
  let t'2 := (fp + 0)
  let accel : UInt64 := t'2
  VehicleBridge.AP_InertialSensor.get_gyro'1 ins (fp + 16) (Int8.toUInt8 (Int32.toInt8 ((0 : Int32))))
  let t'3 := (fp + 16)
  let gyro : UInt64 := t'3
  Vector3'float.Vector3'2 (fp + 32)
  let t'4 ← VehicleBridge.compass'0
  let compass : UInt64 := t'4
  let t'5 ← VehicleBridge.Compass.get_count'0 compass
  if (decide ((UInt32.toInt32 (UInt8.toUInt32 (t'5))) ≥ (1 : Int32))) then
    VehicleBridge.Compass.get_field'1 compass (fp + 48) (Int8.toUInt8 (Int32.toInt8 ((0 : Int32))))
    let t'6 := (fp + 48)
    discard <| PMem.memcpy (fp + 32) t'6 12
    discard <| pure ((fp + 32))
  let t'7 ← PMem.ldU32 (this + 40)
  let t'8 ← PMem.ldF32 accel
  let t'9 ← PMem.ldF32 (accel + 4)
  let t'10 ← PMem.ldF32 (accel + 8)
  let t'11 ← PMem.ldF32 gyro
  let t'12 ← PMem.ldF32 (gyro + 4)
  let t'13 ← PMem.ldF32 (gyro + 8)
  let t'14 ← PMem.ldF32 (fp + 32)
  let t'15 ← PMem.ldF32 ((fp + 32) + 4)
  let t'16 ← PMem.ldF32 ((fp + 32) + 8)
  let t'17 ← VehicleBridge.AP_InertialSensor.get_temperature'1 ins (Int8.toUInt8 (Int32.toInt8 ((0 : Int32))))
  mavlink_msg_raw_imu_send t'7 (← PMem.clock) (Binary32.toInt16 (((t'8 * (Binary32.ofBits 0x447a0000 /- 1000 -/)) / (Binary32.ofBits 0x411ce80a /- 122583127/12500000 -/)))) (Binary32.toInt16 (((t'9 * (Binary32.ofBits 0x447a0000 /- 1000 -/)) / (Binary32.ofBits 0x411ce80a /- 122583127/12500000 -/)))) (Binary32.toInt16 (((t'10 * (Binary32.ofBits 0x447a0000 /- 1000 -/)) / (Binary32.ofBits 0x411ce80a /- 122583127/12500000 -/)))) (Binary32.toInt16 ((t'11 * (Binary32.ofBits 0x447a0000 /- 1000 -/)))) (Binary32.toInt16 ((t'12 * (Binary32.ofBits 0x447a0000 /- 1000 -/)))) (Binary32.toInt16 ((t'13 * (Binary32.ofBits 0x447a0000 /- 1000 -/)))) (Binary32.toInt16 (t'14)) (Binary32.toInt16 (t'15)) (Binary32.toInt16 (t'16)) (Int8.toUInt8 (Int32.toInt8 ((0 : Int32)))) (Binary32.toInt16 ((t'17 * (Int32.toBinary32 ((100 : Int32))))))
  return ()

def GCS_MAVLINK.send_raw_imu (this : UInt64) : PMem.M Unit := do
  let fp ← PMem.enter 60
  let r ← GCS_MAVLINK.send_raw_imu.body fp this
  PMem.leave fp
  return r

/-- C++ `GCS_MAVLINK::send_highres_imu : void ()`, `GCS_Common.cpp:2275-2341`. -/
def GCS_MAVLINK.send_highres_imu.body (fp : UInt64) (this : UInt64) : PMem.M Unit := do
  let t'1 ← VehicleBridge.ins'0
  let ins : UInt64 := t'1
  VehicleBridge.AP_InertialSensor.get_accel'0 ins (fp + 0)
  let t'2 := (fp + 0)
  let accel : UInt64 := t'2
  VehicleBridge.AP_InertialSensor.get_gyro'0 ins (fp + 16)
  let t'3 := (fp + 16)
  let gyro : UInt64 := t'3
  PMem.stU64 ((fp + 32) + 0) (← PMem.clock)
  let t'4 ← PMem.ldF32 accel
  PMem.stF32 ((fp + 32) + 8) t'4
  let t'5 ← PMem.ldF32 (accel + 4)
  PMem.stF32 ((fp + 32) + 12) t'5
  let t'6 ← PMem.ldF32 (accel + 8)
  PMem.stF32 ((fp + 32) + 16) t'6
  let t'7 ← PMem.ldF32 gyro
  PMem.stF32 ((fp + 32) + 20) t'7
  let t'8 ← PMem.ldF32 (gyro + 4)
  PMem.stF32 ((fp + 32) + 24) t'8
  let t'9 ← PMem.ldF32 (gyro + 8)
  PMem.stF32 ((fp + 32) + 28) t'9
  PMem.stF32 ((fp + 32) + 32) (Binary64.toBinary32 ((Binary64.ofBits 0x0000000000000000 /- 0 -/)))
  PMem.stF32 ((fp + 32) + 36) (Binary64.toBinary32 ((Binary64.ofBits 0x0000000000000000 /- 0 -/)))
  PMem.stF32 ((fp + 32) + 40) (Binary64.toBinary32 ((Binary64.ofBits 0x0000000000000000 /- 0 -/)))
  PMem.stF32 ((fp + 32) + 44) (Binary64.toBinary32 ((Binary64.ofBits 0x0000000000000000 /- 0 -/)))
  PMem.stF32 ((fp + 32) + 48) (Binary64.toBinary32 ((Binary64.ofBits 0x0000000000000000 /- 0 -/)))
  PMem.stF32 ((fp + 32) + 52) (Binary64.toBinary32 ((Binary64.ofBits 0x0000000000000000 /- 0 -/)))
  PMem.stF32 ((fp + 32) + 56) (Binary64.toBinary32 ((Binary64.ofBits 0x0000000000000000 /- 0 -/)))
  let t'10 ← PMem.ldU16 (0x12e68 : UInt64) /- &GCS_MAVLINK::send_highres_imu(...)::HIGHRES_IMU_UPDATED_XACC -/
  let t'11 ← PMem.ldU16 (0x12e70 : UInt64) /- &GCS_MAVLINK::send_highres_imu(...)::HIGHRES_IMU_UPDATED_YACC -/
  let t'12 ← PMem.ldU16 (0x12e78 : UInt64) /- &GCS_MAVLINK::send_highres_imu(...)::HIGHRES_IMU_UPDATED_ZACC -/
  let t'13 ← PMem.ldU16 (0x12e80 : UInt64) /- &GCS_MAVLINK::send_highres_imu(...)::HIGHRES_IMU_UPDATED_XGYRO -/
  let t'14 ← PMem.ldU16 (0x12e88 : UInt64) /- &GCS_MAVLINK::send_highres_imu(...)::HIGHRES_IMU_UPDATED_YGYRO -/
  let t'15 ← PMem.ldU16 (0x12e90 : UInt64) /- &GCS_MAVLINK::send_highres_imu(...)::HIGHRES_IMU_UPDATED_ZGYRO -/
  PMem.stU16 ((fp + 32) + 60) (Int16.toUInt16 (Int32.toInt16 (((((((UInt32.toInt32 (UInt16.toUInt32 (t'10))) ||| (UInt32.toInt32 (UInt16.toUInt32 (t'11)))) ||| (UInt32.toInt32 (UInt16.toUInt32 (t'12)))) ||| (UInt32.toInt32 (UInt16.toUInt32 (t'13)))) ||| (UInt32.toInt32 (UInt16.toUInt32 (t'14)))) ||| (UInt32.toInt32 (UInt16.toUInt32 (t'15)))))))
  let t'16 ← VehicleBridge.AP_InertialSensor.get_first_usable_accel'0 ins
  PMem.stU8 ((fp + 32) + 62) t'16
  let t'17 ← VehicleBridge.compass'0
  let compass : UInt64 := t'17
  let t'18 ← VehicleBridge.Compass.get_count'0 compass
  if (decide ((UInt32.toInt32 (UInt8.toUInt32 (t'18))) ≥ (1 : Int32))) then
    VehicleBridge.Compass.get_field'0 compass (fp + 112)
    let t'19 := (fp + 112)
    Vector3'float.operator_ t'19 (fp + 128) (Binary32.ofBits 0x3a83126f /- 20000001/20000000000 -/)
    let t'20 := (fp + 128)
    Vector3'float.Vector3'3 (fp + 96) t'20
    let t'21 ← PMem.ldF32 (fp + 96)
    PMem.stF32 ((fp + 32) + 32) t'21
    let t'22 ← PMem.ldF32 ((fp + 96) + 4)
    PMem.stF32 ((fp + 32) + 36) t'22
    let t'23 ← PMem.ldF32 ((fp + 96) + 8)
    PMem.stF32 ((fp + 32) + 40) t'23
    let t'24 := ((fp + 32) + 60)
    let t'25 ← PMem.ldU16 t'24
    let t'26 ← PMem.ldU16 (0x12e98 : UInt64) /- &GCS_MAVLINK::send_highres_imu(...)::HIGHRES_IMU_UPDATED_XMAG -/
    let t'27 ← PMem.ldU16 (0x12ea0 : UInt64) /- &GCS_MAVLINK::send_highres_imu(...)::HIGHRES_IMU_UPDATED_YMAG -/
    let t'28 ← PMem.ldU16 (0x12ea8 : UInt64) /- &GCS_MAVLINK::send_highres_imu(...)::HIGHRES_IMU_UPDATED_ZMAG -/
    let t'29 := (t'25 ||| (Int16.toUInt16 (Int32.toInt16 ((((UInt32.toInt32 (UInt16.toUInt32 (t'26))) ||| (UInt32.toInt32 (UInt16.toUInt32 (t'27)))) ||| (UInt32.toInt32 (UInt16.toUInt32 (t'28))))))))
    PMem.stU16 t'24 t'29
  let t'30 ← VehicleBridge.baro'0
  let barometer : UInt64 := t'30
  let t'31 ← VehicleBridge.AP_Baro.get_pressure'0 barometer
  let t'32 := (t'31 * (Binary32.ofBits 0x3c23d70a /- 999999977/100000000000 -/))
  PMem.stF32 ((fp + 32) + 44) t'32
  let t'33 ← VehicleBridge.AP_Baro.get_temperature'0 barometer
  PMem.stF32 ((fp + 32) + 56) t'33
  let t'34 ← VehicleBridge.AP_Baro.get_altitude_AMSL'0 barometer
  PMem.stF32 ((fp + 32) + 52) t'34
  let t'35 ← PMem.ldF32 ((fp + 32) + 44)
  let t'36 ← VehicleBridge.AP_Baro.get_ground_pressure'0 barometer
  let t'37 := (t'35 - (t'36 * (Binary32.ofBits 0x3c23d70a /- 999999977/100000000000 -/)))
  PMem.stF32 ((fp + 32) + 48) t'37
  let t'38 := ((fp + 32) + 60)
  let t'39 ← PMem.ldU16 t'38
  let t'40 ← PMem.ldU16 (0x12eb0 : UInt64) /- &GCS_MAVLINK::send_highres_imu(...)::HIGHRES_IMU_UPDATED_ABS_PRESSURE -/
  let t'41 ← PMem.ldU16 (0x12eb8 : UInt64) /- &GCS_MAVLINK::send_highres_imu(...)::HIGHRES_IMU_UPDATED_DIFF_PRESSURE -/
  let t'42 ← PMem.ldU16 (0x12ec0 : UInt64) /- &GCS_MAVLINK::send_highres_imu(...)::HIGHRES_IMU_UPDATED_PRESSURE_ALT -/
  let t'43 ← PMem.ldU16 (0x12ec8 : UInt64) /- &GCS_MAVLINK::send_highres_imu(...)::HIGHRES_IMU_UPDATED_TEMPERATURE -/
  let t'44 := (t'39 ||| (Int16.toUInt16 (Int32.toInt16 (((((UInt32.toInt32 (UInt16.toUInt32 (t'40))) ||| (UInt32.toInt32 (UInt16.toUInt32 (t'41)))) ||| (UInt32.toInt32 (UInt16.toUInt32 (t'42)))) ||| (UInt32.toInt32 (UInt16.toUInt32 (t'43))))))))
  PMem.stU16 t'38 t'44
  let t'45 ← PMem.ldU32 (this + 40)
  mavlink_msg_highres_imu_send_struct t'45 (fp + 32)
  return ()

def GCS_MAVLINK.send_highres_imu (this : UInt64) : PMem.M Unit := do
  let fp ← PMem.enter 140
  let r ← GCS_MAVLINK.send_highres_imu.body fp this
  PMem.leave fp
  return r

/-- C++ `GCS_MAVLINK::send_scaled_pressure_instance : void (uint8_t, void (*)(mavlink_channel_t, uint32_t, float, float, int16_t, int16_t))`, `GCS_Common.cpp:2393-2436`. -/
def GCS_MAVLINK.send_scaled_pressure_instance (this : UInt64) (instance' : UInt8) (send_fn : UInt64) : PMem.M Unit := do
  let mut instance' := instance'
  let mut send_fn := send_fn
  let t'1 ← VehicleBridge.baro'0
  let barometer : UInt64 := t'1
  let mut have_data : Bool := false
  let mut press_abs : Binary32 := (Binary32.ofBits 0x00000000 /- 0 -/)
  let mut temperature : Int16 := Int32.toInt16 ((0 : Int32))
  let mut temperature_press_diff : Int16 := Int32.toInt16 ((0 : Int32))
  let t'2 ← VehicleBridge.AP_Baro.num_instances'0 barometer
  if (decide ((UInt32.toInt32 (UInt8.toUInt32 (instance'))) < (UInt32.toInt32 (UInt8.toUInt32 (t'2))))) then
    let t'3 ← VehicleBridge.AP_Baro.get_pressure'1 barometer instance'
    let t'4 := (t'3 * (Binary32.ofBits 0x3c23d70a /- 999999977/100000000000 -/))
    press_abs := t'4
    let t'5 ← VehicleBridge.AP_Baro.get_temperature'1 barometer instance'
    let t'6 := Binary32.toInt16 ((t'5 * (Int32.toBinary32 ((100 : Int32)))))
    temperature := t'6
    have_data := true
  let mut press_diff : Binary32 := Int32.toBinary32 ((0 : Int32))
  if !have_data then
    return ()
  let t'7 ← PMem.ldU32 (this + 40)
  fnptr'2 send_fn t'7 (((← PMem.clock) / 1000).toUInt32) press_abs press_diff temperature temperature_press_diff
  return ()

/-- C++ `GCS_MAVLINK::send_scaled_pressure : void ()`, `GCS_Common.cpp:2438-2441`. -/
def GCS_MAVLINK.send_scaled_pressure (this : UInt64) : PMem.M Unit := do
  GCS_MAVLINK.send_scaled_pressure_instance this (Int8.toUInt8 (Int32.toInt8 ((0 : Int32)))) (0x7f000020 : UInt64)
  return ()

/-- C++ `GCS_MAVLINK::send_scaled_pressure2 : void ()`, `GCS_Common.cpp:2443-2446`. -/
def GCS_MAVLINK.send_scaled_pressure2 (this : UInt64) : PMem.M Unit := do
  GCS_MAVLINK.send_scaled_pressure_instance this (Int8.toUInt8 (Int32.toInt8 ((1 : Int32)))) (0x7f000030 : UInt64)
  return ()

/-- C++ `GCS_MAVLINK::send_scaled_pressure3 : void ()`, `GCS_Common.cpp:2448-2451`. -/
def GCS_MAVLINK.send_scaled_pressure3 (this : UInt64) : PMem.M Unit := do
  GCS_MAVLINK.send_scaled_pressure_instance this (Int8.toUInt8 (Int32.toInt8 ((2 : Int32)))) (0x7f000040 : UInt64)
  return ()

/-- C++ `GCS_MAVLINK::send_servo_output_raw : void ()`, `GCS_Common.cpp:3402-3445`. -/
def GCS_MAVLINK.send_servo_output_raw.body (fp : UInt64) (this : UInt64) : PMem.M Unit := do
  let t'1 ← SRV_Channels.get_output_channel_mask (-1 : Int32)
  let mut enabled_mask : UInt32 := ~~~t'1
  if (enabled_mask == (Int32.toUInt32 ((0 : Int32)))) then
    return ()
  let t'2 ← PMem.ldU64 ((0xba88 : UInt64) /- &hal -/ + 72)
  let t'3 ← PMem.ldU8 (0x12ed0 : UInt64) /- &GCS_MAVLINK::send_servo_output_raw(...)::max_channels -/
  discard <| PMem.halDev "AP_HAL::RCOutput::read" t'2 #[(fp + 0), (UInt8.toUInt64 (t'3))]
  let mut i : UInt8 := Int8.toUInt8 (Int32.toInt8 ((0 : Int32)))
  let mut first'4 := true
  for _ in PMem.loopFuel do
    if !first'4 then
      let t'5 := i
      let t'6 := (t'5 + 1)
      i := t'6
      pure ()
    first'4 := false
    let t'7 ← PMem.ldU8 (0x12ed0 : UInt64) /- &GCS_MAVLINK::send_servo_output_raw(...)::max_channels -/
    if !((decide ((UInt32.toInt32 (UInt8.toUInt32 (i))) < (UInt32.toInt32 (UInt8.toUInt32 (t'7)))))) then break
    let t'8 ← PMem.ldU16 ((fp + 0) + ((UInt64.toInt64 (UInt8.toUInt64 (i))) * 2).toUInt64)
    if ((UInt32.toInt32 (UInt16.toUInt32 (t'8))) == (65535 : Int32)) then
      let t'9 := Int16.toUInt16 (Int32.toInt16 ((0 : Int32)))
      PMem.stU16 ((fp + 0) + ((UInt64.toInt64 (UInt8.toUInt64 (i))) * 2).toUInt64) t'9
  if ((enabled_mask &&& (Int32.toUInt32 ((65535 : Int32)))) != (Int32.toUInt32 ((0 : Int32)))) then
    let t'10 ← PMem.ldU32 (this + 40)
    let t'11 ← PMem.ldU16 ((fp + 0) + ((Int32.toInt64 ((0 : Int32))) * 2).toUInt64)
    let t'12 ← PMem.ldU16 ((fp + 0) + ((Int32.toInt64 ((1 : Int32))) * 2).toUInt64)
    let t'13 ← PMem.ldU16 ((fp + 0) + ((Int32.toInt64 ((2 : Int32))) * 2).toUInt64)
    let t'14 ← PMem.ldU16 ((fp + 0) + ((Int32.toInt64 ((3 : Int32))) * 2).toUInt64)
    let t'15 ← PMem.ldU16 ((fp + 0) + ((Int32.toInt64 ((4 : Int32))) * 2).toUInt64)
    let t'16 ← PMem.ldU16 ((fp + 0) + ((Int32.toInt64 ((5 : Int32))) * 2).toUInt64)
    let t'17 ← PMem.ldU16 ((fp + 0) + ((Int32.toInt64 ((6 : Int32))) * 2).toUInt64)
    let t'18 ← PMem.ldU16 ((fp + 0) + ((Int32.toInt64 ((7 : Int32))) * 2).toUInt64)
    let t'19 ← PMem.ldU16 ((fp + 0) + ((Int32.toInt64 ((8 : Int32))) * 2).toUInt64)
    let t'20 ← PMem.ldU16 ((fp + 0) + ((Int32.toInt64 ((9 : Int32))) * 2).toUInt64)
    let t'21 ← PMem.ldU16 ((fp + 0) + ((Int32.toInt64 ((10 : Int32))) * 2).toUInt64)
    let t'22 ← PMem.ldU16 ((fp + 0) + ((Int32.toInt64 ((11 : Int32))) * 2).toUInt64)
    let t'23 ← PMem.ldU16 ((fp + 0) + ((Int32.toInt64 ((12 : Int32))) * 2).toUInt64)
    let t'24 ← PMem.ldU16 ((fp + 0) + ((Int32.toInt64 ((13 : Int32))) * 2).toUInt64)
    let t'25 ← PMem.ldU16 ((fp + 0) + ((Int32.toInt64 ((14 : Int32))) * 2).toUInt64)
    let t'26 ← PMem.ldU16 ((fp + 0) + ((Int32.toInt64 ((15 : Int32))) * 2).toUInt64)
    mavlink_msg_servo_output_raw_send t'10 ((← PMem.clock).toUInt32) (Int8.toUInt8 (Int32.toInt8 ((0 : Int32)))) t'11 t'12 t'13 t'14 t'15 t'16 t'17 t'18 t'19 t'20 t'21 t'22 t'23 t'24 t'25 t'26
  if ((enabled_mask &&& (4294901760 : UInt32)) != (Int32.toUInt32 ((0 : Int32)))) then
    let t'27 ← PMem.ldU32 (this + 40)
    let t'28 ← PMem.ldU16 ((fp + 0) + ((Int32.toInt64 ((16 : Int32))) * 2).toUInt64)
    let t'29 ← PMem.ldU16 ((fp + 0) + ((Int32.toInt64 ((17 : Int32))) * 2).toUInt64)
    let t'30 ← PMem.ldU16 ((fp + 0) + ((Int32.toInt64 ((18 : Int32))) * 2).toUInt64)
    let t'31 ← PMem.ldU16 ((fp + 0) + ((Int32.toInt64 ((19 : Int32))) * 2).toUInt64)
    let t'32 ← PMem.ldU16 ((fp + 0) + ((Int32.toInt64 ((20 : Int32))) * 2).toUInt64)
    let t'33 ← PMem.ldU16 ((fp + 0) + ((Int32.toInt64 ((21 : Int32))) * 2).toUInt64)
    let t'34 ← PMem.ldU16 ((fp + 0) + ((Int32.toInt64 ((22 : Int32))) * 2).toUInt64)
    let t'35 ← PMem.ldU16 ((fp + 0) + ((Int32.toInt64 ((23 : Int32))) * 2).toUInt64)
    let t'36 ← PMem.ldU16 ((fp + 0) + ((Int32.toInt64 ((24 : Int32))) * 2).toUInt64)
    let t'37 ← PMem.ldU16 ((fp + 0) + ((Int32.toInt64 ((25 : Int32))) * 2).toUInt64)
    let t'38 ← PMem.ldU16 ((fp + 0) + ((Int32.toInt64 ((26 : Int32))) * 2).toUInt64)
    let t'39 ← PMem.ldU16 ((fp + 0) + ((Int32.toInt64 ((27 : Int32))) * 2).toUInt64)
    let t'40 ← PMem.ldU16 ((fp + 0) + ((Int32.toInt64 ((28 : Int32))) * 2).toUInt64)
    let t'41 ← PMem.ldU16 ((fp + 0) + ((Int32.toInt64 ((29 : Int32))) * 2).toUInt64)
    let t'42 ← PMem.ldU16 ((fp + 0) + ((Int32.toInt64 ((30 : Int32))) * 2).toUInt64)
    let t'43 ← PMem.ldU16 ((fp + 0) + ((Int32.toInt64 ((31 : Int32))) * 2).toUInt64)
    mavlink_msg_servo_output_raw_send t'27 ((← PMem.clock).toUInt32) (Int8.toUInt8 (Int32.toInt8 ((1 : Int32)))) t'28 t'29 t'30 t'31 t'32 t'33 t'34 t'35 t'36 t'37 t'38 t'39 t'40 t'41 t'42 t'43
  return ()

def GCS_MAVLINK.send_servo_output_raw (this : UInt64) : PMem.M Unit := do
  let fp ← PMem.enter 64
  let r ← GCS_MAVLINK.send_servo_output_raw.body fp this
  PMem.leave fp
  return r

/-- C++ `GCS::update_sensor_status_flags : void ()`, `GCS.cpp:470-672`. -/
def GCS.update_sensor_status_flags (this : UInt64) : PMem.M Unit := do
  let t'1 := Int32.toUInt32 ((0 : Int32))
  PMem.stU32 (this + 16) t'1
  let t'2 := Int32.toUInt32 ((0 : Int32))
  PMem.stU32 (this + 20) t'2
  let t'3 := Int32.toUInt32 ((0 : Int32))
  PMem.stU32 (this + 24) t'3
  let t'4 ← VehicleBridge.ins'0
  let ins : UInt64 := t'4
  let t'5 ← VehicleBridge.ahrs'0
  let ahrs : UInt64 := t'5
  let t'6 := (this + 16)
  let t'7 ← PMem.ldU32 t'6
  let t'8 := (t'7 ||| (2097152 : UInt32))
  PMem.stU32 t'6 t'8
  let t'9 ← VehicleBridge.AP_AHRS.initialised'0 ahrs
  if t'9 then
    let t'10 := (this + 20)
    let t'11 ← PMem.ldU32 t'10
    let t'12 := (t'11 ||| (2097152 : UInt32))
    PMem.stU32 t'10 t'12
    let t'13 ← VehicleBridge.AP_AHRS.healthy'0 ahrs
    if t'13 then
      let t'14 ← VehicleBridge.AP_AHRS.have_inertial_nav'0 ahrs
      let mut sc'16 := !t'14
      if !sc'16 then
        let t'15 ← VehicleBridge.AP_InertialSensor.accel_calibrated_ok_all'0 ins
        sc'16 := t'15
      if sc'16 then
        let t'17 := (this + 24)
        let t'18 ← PMem.ldU32 t'17
        let t'19 := (t'18 ||| (2097152 : UInt32))
        PMem.stU32 t'17 t'19
  let t'20 ← VehicleBridge.compass'0
  let compass : UInt64 := t'20
  let t'21 ← VehicleBridge.compass'0
  let t'22 ← VehicleBridge.Compass.available'0 t'21
  if t'22 then
    let t'23 := (this + 16)
    let t'24 ← PMem.ldU32 t'23
    let t'25 := (t'24 ||| (4 : UInt32))
    PMem.stU32 t'23 t'25
    let t'26 := (this + 20)
    let t'27 ← PMem.ldU32 t'26
    let t'28 := (t'27 ||| (4 : UInt32))
    PMem.stU32 t'26 t'28
  let t'29 ← VehicleBridge.Compass.available'0 compass
  let mut sc'31 := t'29
  if sc'31 then
    let t'30 ← VehicleBridge.Compass.healthy'0 compass
    sc'31 := t'30
  if sc'31 then
    let t'32 := (this + 24)
    let t'33 ← PMem.ldU32 t'32
    let t'34 := (t'33 ||| (4 : UInt32))
    PMem.stU32 t'32 t'34
  let t'35 ← VehicleBridge.baro'0
  let barometer : UInt64 := t'35
  let t'36 ← VehicleBridge.AP_Baro.num_instances'0 barometer
  if (decide ((UInt32.toInt32 (UInt8.toUInt32 (t'36))) > (0 : Int32))) then
    let t'37 := (this + 16)
    let t'38 ← PMem.ldU32 t'37
    let t'39 := (t'38 ||| (8 : UInt32))
    PMem.stU32 t'37 t'39
    let t'40 := (this + 20)
    let t'41 ← PMem.ldU32 t'40
    let t'42 := (t'41 ||| (8 : UInt32))
    PMem.stU32 t'40 t'42
    let t'43 ← VehicleBridge.AP_Baro.all_healthy'0 barometer
    if t'43 then
      let t'44 := (this + 24)
      let t'45 ← PMem.ldU32 t'44
      let t'46 := (t'45 ||| (8 : UInt32))
      PMem.stU32 t'44 t'46
  let t'47 ← VehicleBridge.gps'0
  let gps : UInt64 := t'47
  let t'48 ← VehicleBridge.AP_GPS.status'0 gps
  if (decide (t'48 > (0 : UInt8))) then
    let t'49 := (this + 16)
    let t'50 ← PMem.ldU32 t'49
    let t'51 := (t'50 ||| (32 : UInt32))
    PMem.stU32 t'49 t'51
    let t'52 := (this + 20)
    let t'53 ← PMem.ldU32 t'52
    let t'54 := (t'53 ||| (32 : UInt32))
    PMem.stU32 t'52 t'54
  let t'55 ← VehicleBridge.AP_GPS.is_healthy'0 gps
  let mut sc'58 := t'55
  if sc'58 then
    let t'56 ← VehicleBridge.AP_GPS.status'0 gps
    let t'57 ← GCS.min_status_for_gps_healthy this
    sc'58 := (decide (t'56 ≥ t'57))
  if sc'58 then
    let t'59 := (this + 24)
    let t'60 ← PMem.ldU32 t'59
    let t'61 := (t'60 ||| (32 : UInt32))
    PMem.stU32 t'59 t'61
  let t'62 ← AP.battery
  let battery : UInt64 := t'62
  let t'63 := (this + 16)
  let t'64 ← PMem.ldU32 t'63
  let t'65 := (t'64 ||| (33554432 : UInt32))
  PMem.stU32 t'63 t'65
  let t'66 ← AP_BattMonitor.num_instances battery
  if (decide ((UInt32.toInt32 (UInt8.toUInt32 (t'66))) > (0 : Int32))) then
    let t'67 := (this + 20)
    let t'68 ← PMem.ldU32 t'67
    let t'69 := (t'68 ||| (33554432 : UInt32))
    PMem.stU32 t'67 t'69
  let t'70 ← AP_BattMonitor.healthy battery
  let mut sc'72 := t'70
  if sc'72 then
    let t'71 ← AP_BattMonitor.has_failsafed battery
    sc'72 := !t'71
  if sc'72 then
    let t'73 := (this + 24)
    let t'74 ← PMem.ldU32 t'73
    let t'75 := (t'74 ||| (33554432 : UInt32))
    PMem.stU32 t'73 t'75
  let t'76 := (this + 16)
  let t'77 ← PMem.ldU32 t'76
  let t'78 := (t'77 ||| (1 : UInt32))
  PMem.stU32 t'76 t'78
  let t'79 := (this + 16)
  let t'80 ← PMem.ldU32 t'79
  let t'81 := (t'80 ||| (2 : UInt32))
  PMem.stU32 t'79 t'81
  let t'82 ← VehicleBridge.AP_InertialSensor.calibrating'0 ins
  if !t'82 then
    let t'83 := (this + 20)
    let t'84 ← PMem.ldU32 t'83
    let t'85 := (t'84 ||| (2 : UInt32))
    PMem.stU32 t'83 t'85
    let t'86 := (this + 20)
    let t'87 ← PMem.ldU32 t'86
    let t'88 := (t'87 ||| (1 : UInt32))
    PMem.stU32 t'86 t'88
    let t'89 ← VehicleBridge.AP_InertialSensor.get_accel_health_all'0 ins
    if t'89 then
      let t'90 := (this + 24)
      let t'91 ← PMem.ldU32 t'90
      let t'92 := (t'91 ||| (2 : UInt32))
      PMem.stU32 t'90 t'92
    let t'93 ← VehicleBridge.AP_InertialSensor.get_gyro_health_all'0 ins
    let mut sc'95 := t'93
    if sc'95 then
      let t'94 ← VehicleBridge.AP_InertialSensor.gyro_calibrated_ok_all'0 ins
      sc'95 := t'94
    if sc'95 then
      let t'96 := (this + 24)
      let t'97 ← PMem.ldU32 t'96
      let t'98 := (t'97 ||| (1 : UInt32))
      PMem.stU32 t'96 t'98
  let t'99 := (this + 16)
  let t'100 ← PMem.ldU32 t'99
  let t'101 := (t'100 ||| (32768 : UInt32))
  PMem.stU32 t'99 t'101
  let t'102 ← PMem.ldU64 ((0xba88 : UInt64) /- &hal -/ + 88)
  let t'103 ← PMem.halDev "AP_HAL::Util::safety_switch_state" t'102 #[]
  if ((UInt32.toInt32 (UInt8.toUInt32 ((UInt64.toUInt8 (t'103))))) != (UInt32.toInt32 (UInt8.toUInt32 ((1 : UInt8))))) then
    let t'104 := (this + 20)
    let t'105 ← PMem.ldU32 t'104
    let t'106 := (t'105 ||| (32768 : UInt32))
    PMem.stU32 t'104 t'106
  let t'107 := (this + 24)
  let t'108 ← PMem.ldU32 t'107
  let t'109 := (t'108 ||| (32768 : UInt32))
  PMem.stU32 t'107 t'109
  let t'110 ← VehicleBridge.AP_AHRS.configured_ekf_type'0 ahrs
  if (t'110 == (10 : UInt8)) then
    let t'111 := (this + 24)
    let t'112 ← PMem.ldU32 t'111
    let t'113 := (t'112 ||| ((((2097152 : UInt32) ||| (32 : UInt32)) ||| (2 : UInt32)) ||| (1 : UInt32)))
    PMem.stU32 t'111 t'113
  let t'114 := (this + 16)
  let t'115 ← PMem.ldU32 t'114
  let t'116 := (t'115 ||| (268435456 : UInt32))
  PMem.stU32 t'114 t'116
  let t'117 ← AP.arming
  let t'118 ← AP_Arming.get_enabled_checks t'117
  if t'118 != (0 : UInt32) then
    let t'119 := (this + 20)
    let t'120 ← PMem.ldU32 t'119
    let t'121 := (t'120 ||| (268435456 : UInt32))
    PMem.stU32 t'119 t'121
    let mut sc'123 := (← get).armed
    if !sc'123 then
      let t'122 ← PMem.ldB ((0xccc0 : UInt64) /- &AP_Notify::flags -/ + 6)
      sc'123 := t'122
    if sc'123 then
      let t'124 := (this + 24)
      let t'125 ← PMem.ldU32 t'124
      let t'126 := (t'125 ||| (268435456 : UInt32))
      PMem.stU32 t'124 t'126
  let t'127 ← rc
  let t'128 ← RC_Channels.has_ever_seen_rc_input t'127
  if t'128 then
    let t'129 := (this + 16)
    let t'130 ← PMem.ldU32 t'129
    let t'131 := (t'130 ||| (65536 : UInt32))
    PMem.stU32 t'129 t'131
    let t'132 := (this + 20)
    let t'133 ← PMem.ldU32 t'132
    let t'134 := (t'133 ||| (65536 : UInt32))
    PMem.stU32 t'132 t'134
    let t'135 ← rc
    let t'136 ← RC_Channels_Copter.in_rc_failsafe t'135
    if !t'136 then
      let t'137 := (this + 24)
      let t'138 ← PMem.ldU32 t'137
      let t'139 := (t'138 ||| (65536 : UInt32))
      PMem.stU32 t'137 t'139
  GCS_Copter.update_vehicle_sensor_status_flags this
  return ()

/-- C++ `GCS::get_sensor_status_flags : void (uint32_t &, uint32_t &, uint32_t &)`, `GCS.cpp:242-259`. -/
def GCS.get_sensor_status_flags (this : UInt64) (present : UInt64) (enabled : UInt64) (health : UInt64) : PMem.M Unit := do
  GCS.update_sensor_status_flags this
  let t'1 ← PMem.ldU32 (this + 16)
  PMem.stU32 present t'1
  let t'2 ← PMem.ldU32 (this + 20)
  PMem.stU32 enabled t'2
  let t'3 ← PMem.ldU32 (this + 24)
  PMem.stU32 health t'3
  return ()

/-- C++ `GCS_MAVLINK::send_sys_status : void ()`, `GCS_Common.cpp:5994-6064`. -/
def GCS_MAVLINK.send_sys_status.body (fp : UInt64) (this : UInt64) : PMem.M Unit := do
  let t'1 ← gcs
  let t'2 ← GCS_Copter.vehicle_initialised t'1
  if !t'2 then
    return ()
  let t'3 ← AP.battery
  let battery : UInt64 := t'3
  let t'4 ← GCS_MAVLINK.battery_remaining_pct this (Int8.toUInt8 (Int32.toInt8 ((0 : Int32))))
  let mut battery_remaining : Int8 := t'4
  let t'5 ← AP_BattMonitor.healthy battery
  let mut sc'7 := t'5
  if sc'7 then
    let t'6 ← AP_BattMonitor.current_amps battery (fp + 0) (Int8.toUInt8 (Int32.toInt8 ((0 : Int32))))
    sc'7 := t'6
  if sc'7 then
    let t'8 ← PMem.ldF32 (fp + 0)
    let t'9 ← constrain_value_line'float (t'8 * (Int32.toBinary32 ((100 : Int32)))) (Int32.toBinary32 ((-(32767 : Int32)))) (Int32.toBinary32 ((32767 : Int32))) (Int32.toUInt32 ((6007 : Int32)))
    PMem.stF32 (fp + 0) t'9
  else
    let t'10 := Int32.toBinary32 ((-(1 : Int32)))
    PMem.stF32 (fp + 0) t'10
  let t'11 ← gcs
  GCS.get_sensor_status_flags t'11 (fp + 8) (fp + 16) (fp + 24)
  let t'12 := (0 : UInt64)
  let t'13 ← AP_InternalError.errors t'12
  let mut errors' : UInt32 := t'13
  let mut errors1 : UInt16 := UInt32.toUInt16 ((errors' &&& (Int32.toUInt32 ((65535 : Int32)))))
  let mut errors2 : UInt16 := UInt32.toUInt16 (((errors' >>> (Int32.toUInt32 ((16 : Int32)))) &&& (Int32.toUInt32 ((65535 : Int32)))))
  let t'14 := (0 : UInt64)
  let t'15 ← AP_InternalError.count t'14
  let mut errors4 : UInt16 := UInt32.toUInt16 ((t'15 &&& (Int32.toUInt32 ((65535 : Int32)))))
  let mut errors_comm : UInt16 := Int16.toUInt16 (Int32.toInt16 ((0 : Int32)))
  let t'16 ← PMem.ldU32 (this + 40)
  let t'17 ← mavlink_get_channel_status (UInt32.toUInt8 (t'16))
  let mut ms : UInt64 := t'17
  if (ms != 0) then
    let t'18 ← PMem.ldU16 (ms + 14)
    errors_comm := t'18
  let mut dropped_logmessage_count : UInt16 := Int16.toUInt16 (Int32.toInt16 ((65535 : Int32)))
  let t'19 ← PMem.ldU32 (this + 40)
  let t'20 ← PMem.ldU32 (fp + 8)
  let t'21 ← PMem.ldU32 (fp + 16)
  let t'22 ← PMem.ldU32 (fp + 24)
  let t'23 ← AP.scheduler
  let t'24 ← AP_Scheduler.load_average t'23
  let t'25 ← AP_BattMonitor.gcs_voltage battery
  let t'26 ← PMem.ldF32 (fp + 0)
  mavlink_msg_sys_status_send t'19 t'20 t'21 t'22 (Binary32.toUInt16 ((t'24 * (Int32.toBinary32 ((1000 : Int32)))))) (Binary32.toUInt16 ((t'25 * (Int32.toBinary32 ((1000 : Int32)))))) (Binary32.toInt16 (t'26)) battery_remaining (Int16.toUInt16 (Int32.toInt16 ((0 : Int32)))) errors_comm errors1 errors2 dropped_logmessage_count errors4 (Int32.toUInt32 ((0 : Int32))) (Int32.toUInt32 ((0 : Int32))) (Int32.toUInt32 ((0 : Int32)))
  return ()

def GCS_MAVLINK.send_sys_status (this : UInt64) : PMem.M Unit := do
  let fp ← PMem.enter 28
  let r ← GCS_MAVLINK.send_sys_status.body fp this
  PMem.leave fp
  return r

/-- C++ `GCS_MAVLINK::send_ahrs2 : void ()`, `GCS_Common.cpp:621-637`. -/
def GCS_MAVLINK.send_ahrs2.body (fp : UInt64) (this : UInt64) : PMem.M Unit := do
  let t'1 ← VehicleBridge.ahrs'0
  let t'2 ← VehicleBridge.AP_AHRS.get_secondary_estimates'0 t'1 (fp + 0)
  let mut estimates : UInt64 := t'2
  if (estimates == (0 : UInt64)) then
    return ()
  let loc : UInt64 := (estimates + 164)
  let t'3 ← PMem.ldU32 (this + 40)
  let t'4 ← PMem.ldF32 (estimates + 8)
  let t'5 ← PMem.ldF32 (estimates + 12)
  let t'6 ← PMem.ldF32 (estimates + 16)
  let t'7 ← PMem.ldI32 (loc + 4)
  let t'8 ← PMem.ldI32 (loc + 8)
  let t'9 ← PMem.ldI32 (loc + 12)
  mavlink_msg_ahrs2_send t'3 t'4 t'5 t'6 ((Int32.toBinary32 (t'7)) * (Binary32.ofBits 0x3c23d70a /- 999999977/100000000000 -/)) t'8 t'9
  return ()

def GCS_MAVLINK.send_ahrs2 (this : UInt64) : PMem.M Unit := do
  let fp ← PMem.enter 328
  let r ← GCS_MAVLINK.send_ahrs2.body fp this
  PMem.leave fp
  return r

/-- C++ `GCS_MAVLINK::send_ahrs : void ()`, `GCS_Common.cpp:2505-2518`. -/
def GCS_MAVLINK.send_ahrs.body (fp : UInt64) (this : UInt64) : PMem.M Unit := do
  let t'1 ← VehicleBridge.ahrs'0
  let ahrs : UInt64 := t'1
  VehicleBridge.AP_AHRS.get_gyro_drift'0 ahrs (fp + 0)
  let t'2 := (fp + 0)
  let omega_I : UInt64 := t'2
  let t'3 ← PMem.ldU32 (this + 40)
  let t'4 ← PMem.ldF32 omega_I
  let t'5 ← PMem.ldF32 (omega_I + 4)
  let t'6 ← PMem.ldF32 (omega_I + 8)
  let t'7 ← VehicleBridge.AP_AHRS.get_error_rp'0 ahrs
  let t'8 ← VehicleBridge.AP_AHRS.get_error_yaw'0 ahrs
  mavlink_msg_ahrs_send t'3 t'4 t'5 t'6 (Int32.toBinary32 ((0 : Int32))) (Int32.toBinary32 ((0 : Int32))) t'7 t'8
  return ()

def GCS_MAVLINK.send_ahrs (this : UInt64) : PMem.M Unit := do
  let fp ← PMem.enter 12
  let r ← GCS_MAVLINK.send_ahrs.body fp this
  PMem.leave fp
  return r

/-- C++ `GCS_MAVLINK::send_vfr_hud : void ()`, `GCS_Common.cpp:3500-3515`. -/
def GCS_MAVLINK.send_vfr_hud (this : UInt64) : PMem.M Unit := do
  let t'1 ← VehicleBridge.ahrs'0
  let ahrs : UInt64 := t'1
  for _ in [0:1] do
    let mut __unique_name___COUNTER__ : Bool := default  -- uninitialized in C
    let t'2 ← VehicleBridge.AP_AHRS.get_location'1 ahrs (this + 840)
    __unique_name___COUNTER__ := t'2
  let t'3 ← PMem.ldU32 (this + 40)
  let t'4 ← GCS_MAVLINK_Copter.vfr_hud_airspeed this
  let t'5 ← VehicleBridge.AP_AHRS.groundspeed'0 ahrs
  let t'6 ← VehicleBridge.AP_AHRS.get_yaw_deg'0 ahrs
  let t'7 ← GCS_MAVLINK_Copter.vfr_hud_throttle this
  let t'8 ← PMem.iabs (Int16.toInt32 (t'7))
  let t'9 ← GCS_MAVLINK_Copter.vfr_hud_alt this
  let t'10 ← GCS_MAVLINK.vfr_hud_climbrate this
  mavlink_msg_vfr_hud_send t'3 t'4 t'5 (Binary32.toInt16 (t'6)) (Int16.toUInt16 (Int32.toInt16 (t'8))) t'9 t'10
  return ()

/-- C++ `GCS_MAVLINK::send_vibration : void () const`, `GCS_Common.cpp:3077-3094`. -/
def GCS_MAVLINK.send_vibration.body (fp : UInt64) (this : UInt64) : PMem.M Unit := do
  let t'1 ← VehicleBridge.ins'0
  let ins : UInt64 := t'1
  VehicleBridge.AP_InertialSensor.get_vibration_levels'0 ins (fp + 16)
  let t'2 := (fp + 16)
  Vector3'float.Vector3'3 (fp + 0) t'2
  let t'3 ← PMem.ldU32 (this + 40)
  let t'4 ← PMem.ldF32 (fp + 0)
  let t'5 ← PMem.ldF32 ((fp + 0) + 4)
  let t'6 ← PMem.ldF32 ((fp + 0) + 8)
  let t'7 ← VehicleBridge.AP_InertialSensor.get_accel_clip_count'1 ins (Int8.toUInt8 (Int32.toInt8 ((0 : Int32))))
  let t'8 ← VehicleBridge.AP_InertialSensor.get_accel_clip_count'1 ins (Int8.toUInt8 (Int32.toInt8 ((1 : Int32))))
  let t'9 ← VehicleBridge.AP_InertialSensor.get_accel_clip_count'1 ins (Int8.toUInt8 (Int32.toInt8 ((2 : Int32))))
  mavlink_msg_vibration_send t'3 (← PMem.clock) t'4 t'5 t'6 t'7 t'8 t'9
  return ()

def GCS_MAVLINK.send_vibration (this : UInt64) : PMem.M Unit := do
  let fp ← PMem.enter 28
  let r ← GCS_MAVLINK.send_vibration.body fp this
  PMem.leave fp
  return r

/-- C++ `GCS_MAVLINK::send_autopilot_version : void () const`, `GCS_Common.cpp:2984-3044`. -/
def GCS_MAVLINK.send_autopilot_version.body (fp : UInt64) (this : UInt64) : PMem.M Unit := do
  let mut flight_sw_version : UInt32 := default  -- uninitialized in C
  let mut middleware_sw_version : UInt32 := Int32.toUInt32 ((0 : Int32))
  let mut board_version : UInt32 := Int32.toUInt32 ((0 : Int32))
  let mut vendor_id : UInt16 := Int16.toUInt16 (Int32.toInt16 ((0 : Int32)))
  let mut product_id : UInt16 := Int16.toUInt16 (Int32.toInt16 ((0 : Int32)))
  let mut uid : UInt64 := Int64.toUInt64 (Int32.toInt64 ((0 : Int32)))
  PMem.stU8 ((fp + 24) + 0) (Int8.toUInt8 (Int32.toInt8 ((0 : Int32))))
  PMem.stU8 (fp + 48) (UInt64.toUInt8 ((18 : UInt64)))
  let t'1 ← PMem.ldU64 ((0xba88 : UInt64) /- &hal -/ + 88)
  let t'2 ← PMem.halDev "AP_HAL::Util::get_system_id_unformatted" t'1 #[(fp + 24), (fp + 48)]
  discard <| pure ((t'2 != 0))
  let t'3 ← AP.fwversion
  let version : UInt64 := t'3
  let t'4 ← PMem.ldU8 (version + 16)
  let t'5 ← PMem.ldU8 (version + 17)
  let t'6 ← PMem.ldU8 (version + 18)
  let t'7 ← PMem.ldU8 (version + 19)
  let t'8 := ((Int32.toUInt32 (((((UInt32.toInt32 (UInt8.toUInt32 (t'4))) <<< ((8 : Int32) * (3 : Int32))) ||| ((UInt32.toInt32 (UInt8.toUInt32 (t'5))) <<< ((8 : Int32) * (2 : Int32)))) ||| ((UInt32.toInt32 (UInt8.toUInt32 (t'6))) <<< ((8 : Int32) * (1 : Int32)))))) ||| ((UInt8.toUInt32 (t'7)) <<< (Int32.toUInt32 (((8 : Int32) * (0 : Int32))))))
  flight_sw_version := t'8
  let t'9 ← PMem.ldU64 (version + 32)
  if (t'9 != 0) then
    let t'10 ← PMem.ldU64 (version + 32)
    let t'11 ← strncpy_noterm (fp + 0) t'10 ((8 : UInt64) / (1 : UInt64))
    discard <| pure (t'11)
  let t'12 ← PMem.ldU64 (version + 68)
  if (t'12 != 0) then
    let t'13 ← PMem.ldU64 (version + 68)
    let t'14 ← strncpy_noterm (fp + 8) t'13 ((8 : UInt64) / (1 : UInt64))
    discard <| pure (t'14)
  let t'15 ← PMem.ldU64 (version + 84)
  if (t'15 != 0) then
    let t'16 ← PMem.ldU64 (version + 84)
    let t'17 ← strncpy_noterm (fp + 16) t'16 ((8 : UInt64) / (1 : UInt64))
    discard <| pure (t'17)
  let t'18 ← PMem.ldU32 (this + 40)
  let t'19 ← GCS_MAVLINK_Copter.capabilities this
  let t'20 ← PMem.ldU32 (version + 20)
  mavlink_msg_autopilot_version_send t'18 t'19 flight_sw_version middleware_sw_version t'20 board_version (fp + 0) (fp + 8) (fp + 16) vendor_id product_id uid (fp + 24)
  return ()

def GCS_MAVLINK.send_autopilot_version (this : UInt64) : PMem.M Unit := do
  let fp ← PMem.enter 49
  let r ← GCS_MAVLINK.send_autopilot_version.body fp this
  PMem.leave fp
  return r

/-- C++ `GCS_MAVLINK::send_available_modes : bool ()`, `GCS_Common.cpp:6547-6578`. -/
def GCS_MAVLINK.send_available_modes (this : UInt64) : PMem.M Bool := do
  let t'1 ← PMem.ldB ((this + 871) + 1)
  if !t'1 then
    return true
  let t'2 ← GCS_MAVLINK.check_payload_size this (Int16.toUInt16 (Int32.toInt16 ((46 : Int32))))
  if !t'2 then
    return false
  let t'3 ← PMem.ldU8 ((this + 871) + 2)
  let mut send_all : Bool := ((UInt32.toInt32 (UInt8.toUInt32 (t'3))) == (0 : Int32))
  let mut request_index : UInt8 := default  -- uninitialized in C
  if !send_all then
    let t'4 ← PMem.ldU8 ((this + 871) + 2)
    request_index := t'4
    PMem.stB ((this + 871) + 1) false
  else
    let t'5 ← PMem.ldU8 ((this + 871) + 3)
    request_index := t'5
    let t'6 := ((this + 871) + 3)
    let t'7 ← PMem.ldU8 t'6
    let t'8 := (t'7 + (Int8.toUInt8 (Int32.toInt8 ((1 : Int32)))))
    PMem.stU8 t'6 t'8
  let t'9 ← GCS_MAVLINK_Copter.send_available_mode this request_index
  let mut mode_count : UInt8 := t'9
  let mut sc'11 := send_all
  if sc'11 then
    let t'10 ← PMem.ldU8 ((this + 871) + 3)
    sc'11 := (decide ((UInt32.toInt32 (UInt8.toUInt32 (t'10))) > (UInt32.toInt32 (UInt8.toUInt32 (mode_count)))))
  if sc'11 then
    PMem.stB ((this + 871) + 1) false
  return true

/-- C++ `GCS_MAVLINK::send_available_mode_monitor : bool ()`, `GCS_Common.cpp:6580-6590`. -/
def GCS_MAVLINK.send_available_mode_monitor (this : UInt64) : PMem.M Bool := do
  let t'1 ← GCS_MAVLINK.check_payload_size this (Int16.toUInt16 (Int32.toInt16 ((1 : Int32))))
  if !t'1 then
    return false
  let t'2 ← PMem.ldU32 (this + 40)
  let t'3 ← PMem.ldU8 ((this + 871) + 4)
  mavlink_msg_available_modes_monitor_send t'2 t'3
  return true

/-- C++ `GCS_MAVLINK::cap_message_interval : uint16_t (uint16_t) const`, `GCS_Common.cpp:272-281`. -/
def GCS_MAVLINK.cap_message_interval (this : UInt64) (interval_ms : UInt16) : PMem.M UInt16 := do
  let mut interval_ms := interval_ms
  if ((UInt32.toInt32 (UInt16.toUInt32 (interval_ms))) == (0 : Int32)) then
    return Int16.toUInt16 (Int32.toInt16 ((0 : Int32)))
  let t'1 ← AP.scheduler
  let t'2 ← AP_Scheduler.get_loop_period_us t'1
  if (decide ((Int32.toUInt32 (((UInt32.toInt32 (UInt16.toUInt32 (interval_ms))) * (800 : Int32)))) < t'2)) then
    let t'3 ← AP.scheduler
    let t'4 ← AP_Scheduler.get_loop_period_us t'3
    return Binary32.toUInt16 (((UInt32.toBinary32 (t'4)) / (Binary32.ofBits 0x44480000 /- 800 -/)))
  return interval_ms

/-- C++ `GCS_MAVLINK::set_ap_message_interval : bool (enum ap_message, uint16_t)`, `GCS_Common.cpp:1725-1827`. -/
def GCS_MAVLINK.set_ap_message_interval (this : UInt64) (id : UInt8) (interval_ms : UInt16) : PMem.M Bool := do
  let mut id := id
  let mut interval_ms := interval_ms
  if ((UInt32.toInt32 (UInt8.toUInt32 (id))) == (UInt32.toInt32 (UInt8.toUInt32 ((31 : UInt8))))) then
    if ((UInt32.toInt32 (UInt16.toUInt32 (interval_ms))) == (0 : Int32)) then
      let t'1 := Int16.toUInt16 (Int32.toInt16 ((100 : Int32)))
      interval_ms := t'1
    else
      if (decide ((UInt32.toInt32 (UInt16.toUInt32 (interval_ms))) > (1000 : Int32))) then
        let t'2 := Int16.toUInt16 (Int32.toInt16 ((1000 : Int32)))
        interval_ms := t'2
  let t'3 ← GCS_MAVLINK.cap_message_interval this interval_ms
  interval_ms := t'3
  let t'4 ← GCS_MAVLINK.get_deferred_message_index this id
  let mut deferred_offset : Int8 := t'4
  if ((Int8.toInt32 (deferred_offset)) != (-(1 : Int32))) then
    PMem.stU16 (((this + 506) + ((Int8.toInt64 (deferred_offset)) * 6).toUInt64) + 2) interval_ms
    let t'5 := ((← PMem.clock) / 1000).toUInt16
    PMem.stU16 (((this + 506) + ((Int8.toInt64 (deferred_offset)) * 6).toUInt64) + 4) t'5
    return true
  let mut closest_bucket : Int8 := Int32.toInt8 ((-(1 : Int32)))
  let mut closest_bucket_interval_delta : UInt16 := Int16.toUInt16 (Int32.toInt16 ((65535 : Int32)))
  let mut in_bucket : Int8 := Int32.toInt8 ((-(1 : Int32)))
  let mut empty_bucket_id : Int8 := Int32.toInt8 ((-(1 : Int32)))
  let mut i : UInt8 := Int8.toUInt8 (Int32.toInt8 ((0 : Int32)))
  let mut first'6 := true
  for _ in PMem.loopFuel do
    if !first'6 then
      let t'7 := i
      let t'8 := (t'7 + 1)
      i := t'8
      pure ()
    first'6 := false
    if !((decide ((UInt8.toUInt64 (i)) < ((200 : UInt64) / (20 : UInt64))))) then break
    let bucket : UInt64 := ((this + 528) + ((UInt64.toInt64 (UInt8.toUInt64 (i))) * 20).toUInt64)
    let t'9 ← PMem.ldU16 (bucket + 16)
    if ((UInt32.toInt32 (UInt16.toUInt32 (t'9))) == (0 : Int32)) then
      if ((Int8.toInt32 (empty_bucket_id)) == (-(1 : Int32))) then
        let t'10 := UInt8.toInt8 (i)
        empty_bucket_id := t'10
      let t'11 ← Bitmask'102.count bucket
      if ((UInt32.toInt32 (UInt16.toUInt32 (t'11))) != (0 : Int32)) then
        pure ()
      continue
    let t'12 ← Bitmask'102.get bucket (UInt8.toUInt16 (id))
    if t'12 then
      let t'13 := UInt8.toInt8 (i)
      in_bucket := t'13
    let t'14 ← PMem.ldU16 (bucket + 16)
    let t'15 ← PMem.iabs ((UInt32.toInt32 (UInt16.toUInt32 (t'14))) - (UInt32.toInt32 (UInt16.toUInt32 (interval_ms))))
    let mut interval_delta : UInt16 := Int16.toUInt16 (Int32.toInt16 (t'15))
    if (decide ((UInt32.toInt32 (UInt16.toUInt32 (interval_delta))) < (UInt32.toInt32 (UInt16.toUInt32 (closest_bucket_interval_delta))))) then
      let t'16 := UInt8.toInt8 (i)
      closest_bucket := t'16
      closest_bucket_interval_delta := interval_delta
  if (((Int8.toInt32 (in_bucket)) == (-(1 : Int32))) && ((UInt32.toInt32 (UInt16.toUInt32 (interval_ms))) == (0 : Int32))) then
    return true
  if ((Int8.toInt32 (in_bucket)) != (-(1 : Int32))) then
    if ((UInt32.toInt32 (UInt16.toUInt32 (interval_ms))) == (0 : Int32)) then
      GCS_MAVLINK.remove_message_from_bucket this in_bucket id
      return true
    if (((UInt32.toInt32 (UInt16.toUInt32 (closest_bucket_interval_delta))) == (0 : Int32)) && ((Int8.toInt32 (in_bucket)) == (Int8.toInt32 (closest_bucket)))) then
      return true
    GCS_MAVLINK.remove_message_from_bucket this in_bucket id
    let mut sc'18 := ((Int8.toInt32 (empty_bucket_id)) == (-(1 : Int32)))
    if sc'18 then
      let t'17 ← Bitmask'102.count ((this + 528) + ((Int8.toInt64 (in_bucket)) * 20).toUInt64)
      sc'18 := ((UInt32.toInt32 (UInt16.toUInt32 (t'17))) == (0 : Int32))
    if sc'18 then
      empty_bucket_id := in_bucket
  if (((Int8.toInt32 (closest_bucket)) == (-(1 : Int32))) && ((Int8.toInt32 (empty_bucket_id)) == (-(1 : Int32)))) then
    discard <| pure ((0 : Int32))
    GCS_MAVLINK_InProgress.abort this
    return false
  if (((UInt32.toInt32 (UInt16.toUInt32 (closest_bucket_interval_delta))) != (0 : Int32)) && ((Int8.toInt32 (empty_bucket_id)) != (-(1 : Int32)))) then
    PMem.stU16 (((this + 528) + ((Int8.toInt64 (empty_bucket_id)) * 20).toUInt64) + 16) interval_ms
    let t'19 := ((← PMem.clock) / 1000).toUInt16
    PMem.stU16 (((this + 528) + ((Int8.toInt64 (empty_bucket_id)) * 20).toUInt64) + 18) t'19
    closest_bucket := empty_bucket_id
  Bitmask'102.set ((this + 528) + ((Int8.toInt64 (closest_bucket)) * 20).toUInt64) (UInt8.toUInt16 (id))
  let t'20 ← PMem.ldU8 (this + 728)
  if ((UInt32.toInt32 (UInt8.toUInt32 (t'20))) == (UInt32.toInt32 (UInt8.toUInt32 ((255 : UInt8))))) then
    let t'21 := Int8.toUInt8 (closest_bucket)
    PMem.stU8 (this + 728) t'21
    discard <| PMem.memcpy (this + 732) ((this + 528) + ((Int8.toInt64 (closest_bucket)) * 20).toUInt64) 16
    discard <| pure ((this + 732))
  return true

/-- C++ `GCS_MAVLINK::set_message_interval : MAV_RESULT (uint32_t, int32_t)`, `GCS_Common.cpp:3213-3260`. -/
def GCS_MAVLINK.set_message_interval.body (fp : UInt64) (this : UInt64) (msg_id : UInt32) (interval_us : Int32) : PMem.M UInt32 := do
  let mut msg_id := msg_id
  let mut interval_us := interval_us
  let t'1 ← GCS_MAVLINK.mavlink_id_to_ap_message_id this msg_id
  let mut id : UInt8 := t'1
  if ((UInt32.toInt32 (UInt8.toUInt32 (id))) == (UInt32.toInt32 (UInt8.toUInt32 ((102 : UInt8))))) then
    PMem.stU64 (fp + 0) (UInt32.toUInt64 (msg_id))
    let t'2 ← gcs
    GCS.send_text t'2 (6 : UInt32) (0x189bb : UInt64) /- "No ap_message for mavlink id (%u)" -/ (fp + 0)
    return (2 : UInt32)
  if (interval_us == (0 : Int32)) then
    let t'3 ← GCS_MAVLINK.get_default_interval_for_ap_message this id (fp + 8)
    if !t'3 then
      let t'4 := Int16.toUInt16 (Int32.toInt16 ((0 : Int32)))
      PMem.stU16 (fp + 8) t'4
  else
    if (interval_us == (-(1 : Int32))) then
      let t'5 := Int16.toUInt16 (Int32.toInt16 ((0 : Int32)))
      PMem.stU16 (fp + 8) t'5
    else
      if (decide (interval_us < (0 : Int32))) then
        return (2 : UInt32)
      else
        if (decide (interval_us < (1000 : Int32))) then
          let t'6 := Int16.toUInt16 (Int32.toInt16 ((1 : Int32)))
          PMem.stU16 (fp + 8) t'6
        else
          if (decide (interval_us > (60000000 : Int32))) then
            let t'7 := Int16.toUInt16 (Int32.toInt16 ((60000 : Int32)))
            PMem.stU16 (fp + 8) t'7
          else
            let t'8 := Int16.toUInt16 (Int32.toInt16 ((interval_us / (1000 : Int32))))
            PMem.stU16 (fp + 8) t'8
  let t'9 ← PMem.ldU16 (fp + 8)
  let mut sc'13 := ((UInt32.toInt32 (UInt16.toUInt32 (t'9))) != (0 : Int32))
  if sc'13 then
    let t'10 ← PMem.ldU16 (fp + 8)
    let t'11 ← GCS_MAVLINK.cap_message_interval this t'10
    let t'12 ← PMem.ldU16 (fp + 8)
    sc'13 := (decide ((UInt32.toInt32 (UInt16.toUInt32 (t'11))) > (UInt32.toInt32 (UInt16.toUInt32 (t'12)))))
  if sc'13 then
    PMem.stU64 (fp + 16) (UInt32.toUInt64 (msg_id))
    let t'14 ← gcs
    GCS.send_text t'14 (6 : UInt32) (0x18aa1 : UInt64) /- "Requested rate for message ID %u too fast. Increase SCHED_LOOP_RATE" -/ (fp + 16)
    return (2 : UInt32)
  let t'15 ← PMem.ldU16 (fp + 8)
  let t'16 ← GCS_MAVLINK.set_ap_message_interval this id t'15
  if t'16 then
    return (0 : UInt32)
  return (4 : UInt32)

def GCS_MAVLINK.set_message_interval (this : UInt64) (msg_id : UInt32) (interval_us : Int32) : PMem.M UInt32 := do
  let fp ← PMem.enter 24
  let r ← GCS_MAVLINK.set_message_interval.body fp this msg_id interval_us
  PMem.leave fp
  return r

/-- C++ `GCS_MAVLINK::handle_command_set_message_interval : MAV_RESULT (const mavlink_command_int_t &)`, `GCS_Common.cpp:3205-3211`. -/
def GCS_MAVLINK.handle_command_set_message_interval (this : UInt64) (packet : UInt64) : PMem.M UInt32 := do
  let t'1 ← PMem.ldF32 (packet + 8)
  let t'2 ← is_zero t'1
  if !t'2 then
    return (2 : UInt32)
  let t'3 ← PMem.ldF32 packet
  let t'4 ← PMem.ldF32 (packet + 4)
  let t'5 ← GCS_MAVLINK.set_message_interval this (Binary32.toUInt32 (t'3)) (Binary32.toInt32 (t'4))
  return t'5

/-- C++ `GCS_MAVLINK::initialise_message_intervals_for_stream : void (GCS_MAVLINK::streams)`, `GCS_Common.cpp:7096-7110`. -/
def GCS_MAVLINK.initialise_message_intervals_for_stream (this : UInt64) (id : UInt8) : PMem.M Unit := do
  let mut id := id
  let mut i : UInt8 := Int8.toUInt8 (Int32.toInt8 ((0 : Int32)))
  let mut first'1 := true
  for _ in PMem.loopFuel do
    if !first'1 then
      let t'2 := i
      let t'3 := (t'2 + 1)
      i := t'3
      pure ()
    first'1 := false
    let t'4 ← PMem.ldU64 (((0xc890 : UInt64) /- &GCS_MAVLINK::all_stream_entries -/ + ((UInt64.toInt64 (UInt8.toUInt64 (i))) * 24).toUInt64) + 8)
    if !((t'4 != (0 : UInt64))) then break
    let entries : UInt64 := ((0xc890 : UInt64) /- &GCS_MAVLINK::all_stream_entries -/ + ((UInt64.toInt64 (UInt8.toUInt64 (i))) * 24).toUInt64)
    let t'5 ← PMem.ldU8 entries
    if ((UInt32.toInt32 (UInt8.toUInt32 (t'5))) != (UInt32.toInt32 (UInt8.toUInt32 (id)))) then
      continue
    let t'6 ← GCS_MAVLINK.get_interval_for_stream this id
    let mut interval_ms : UInt16 := t'6
    let mut j : UInt8 := Int8.toUInt8 (Int32.toInt8 ((0 : Int32)))
    let mut first'7 := true
    for _ in PMem.loopFuel do
      if !first'7 then
        let t'8 := j
        let t'9 := (t'8 + 1)
        j := t'9
        pure ()
      first'7 := false
      let t'10 ← PMem.ldU8 (entries + 16)
      if !((decide ((UInt32.toInt32 (UInt8.toUInt32 (j))) < (UInt32.toInt32 (UInt8.toUInt32 (t'10)))))) then break
      let t'11 ← PMem.ldU64 (entries + 8)
      let t'12 ← PMem.ldU8 (t'11 + ((UInt64.toInt64 (UInt8.toUInt64 (j))) * 1).toUInt64)
      let t'13 ← GCS_MAVLINK.set_ap_message_interval this t'12 interval_ms
      discard <| pure (t'13)
    break
  return ()

/-- C++ `GCS_MAVLINK::handle_request_data_stream : void (const mavlink_message_t &)`, `GCS_Param.cpp:129-204`. -/
def GCS_MAVLINK.handle_request_data_stream.body (fp : UInt64) (this : UInt64) (msg : UInt64) : PMem.M Unit := do
  __mavlink_request_data_stream_t.__mavlink_request_data_stream_t (fp + 0)
  mavlink_msg_request_data_stream_decode msg (fp + 0)
  PMem.stI16 (fp + 8) (Int32.toInt16 ((0 : Int32)))
  let t'1 ← PMem.ldU8 ((fp + 0) + 5)
  if ((UInt32.toInt32 (UInt8.toUInt32 (t'1))) == (0 : Int32)) then
    let t'2 := Int32.toInt16 ((0 : Int32))
    PMem.stI16 (fp + 8) t'2
  else
    let t'3 ← PMem.ldU8 ((fp + 0) + 5)
    if ((UInt32.toInt32 (UInt8.toUInt32 (t'3))) == (1 : Int32)) then
      let t'4 ← PMem.ldU16 (fp + 0)
      let t'5 := UInt16.toInt16 (t'4)
      PMem.stI16 (fp + 8) t'5
    else
      return ()
  let mut stream_id : UInt8 := (10 : UInt8)
  let t'6 ← PMem.ldU8 ((fp + 0) + 4)
  let sw'7 := UInt32.toInt32 (UInt8.toUInt32 (t'6))
  if sw'7 == (0 : Int32) then
    for i'8 in [0:10] do
      let i : UInt8 := UInt8.ofNat i'8
      if ((UInt32.toInt32 (UInt8.toUInt32 (i))) == (UInt32.toInt32 (UInt8.toUInt32 ((8 : UInt8))))) then
        continue
      let t'9 ← GCS_MAVLINK.persist_streamrates this
      if t'9 then
        AP_ParamTBase'short_2.set_and_save_ifchanged ((this + 44) + ((UInt64.toInt64 (UInt8.toUInt64 (i))) * 2).toUInt64) (fp + 8)
      else
        AP_ParamTBase'short_2.set ((this + 44) + ((UInt64.toInt64 (UInt8.toUInt64 (i))) * 2).toUInt64) (fp + 8)
      GCS_MAVLINK.initialise_message_intervals_for_stream this i
  else if sw'7 == (1 : Int32) then
    stream_id := (0 : UInt8)
  else if sw'7 == (2 : Int32) then
    stream_id := (1 : UInt8)
  else if sw'7 == (3 : Int32) then
    stream_id := (2 : UInt8)
  else if sw'7 == (4 : Int32) then
    stream_id := (3 : UInt8)
  else if sw'7 == (6 : Int32) then
    stream_id := (4 : UInt8)
  else if sw'7 == (10 : Int32) then
    stream_id := (5 : UInt8)
  else if sw'7 == (11 : Int32) then
    stream_id := (6 : UInt8)
  else if sw'7 == (12 : Int32) then
    stream_id := (7 : UInt8)
  else
    pure ()
  if ((UInt32.toInt32 (UInt8.toUInt32 (stream_id))) == (UInt32.toInt32 (UInt8.toUInt32 ((10 : UInt8))))) then
    return ()
  let mut rate : UInt64 := ((this + 44) + ((UInt64.toInt64 (UInt8.toUInt64 (stream_id))) * 2).toUInt64)
  if (rate != (0 : UInt64)) then
    let t'10 ← GCS_MAVLINK.persist_streamrates this
    if t'10 then
      AP_ParamTBase'short_2.set_and_save_ifchanged rate (fp + 8)
    else
      AP_ParamTBase'short_2.set rate (fp + 8)
    GCS_MAVLINK.initialise_message_intervals_for_stream this stream_id
  return ()

def GCS_MAVLINK.handle_request_data_stream (this : UInt64) (msg : UInt64) : PMem.M Unit := do
  let fp ← PMem.enter 10
  let r ← GCS_MAVLINK.handle_request_data_stream.body fp this msg
  PMem.leave fp
  return r

/-- C++ `GCS_MAVLINK::send_timesync : void ()`, `GCS_Common.cpp:3738-3751`. -/
def GCS_MAVLINK.send_timesync (this : UInt64) : PMem.M Unit := do
  let t'1 := ((← PMem.clock) * (1000 : UInt64))
  PMem.stU64 ((this + 72) + 8) t'1
  let t'2 ← PMem.ldU64 ((this + 72) + 8)
  let t'3 ← PMem.ldU32 (0xbc50 : UInt64) /- &mavlink_system -/
  let t'4 := UInt64.toInt64 ((t'2 + (UInt32.toUInt64 ((t'3 % (1000 : UInt32))))))
  PMem.stI64 (this + 72) t'4
  let t'5 ← PMem.ldU32 (this + 40)
  let t'6 ← PMem.ldI64 (this + 72)
  mavlink_msg_timesync_send t'5 (Int32.toInt64 ((0 : Int32))) t'6
  return ()

/-- C++ `MissionItemProtocol_Waypoints::timeout : void ()`, `MissionItemProtocol_Waypoints.cpp:123-126`. -/
def MissionItemProtocol_Waypoints.timeout.body (fp : UInt64) (this : UInt64) : PMem.M Unit := do
  let t'1 ← PMem.ldU64 (this + 16)
  GCS_MAVLINK.send_text t'1 (4 : UInt32) (0x18950 : UInt64) /- "Mission upload timeout" -/ (fp + 0)
  return ()

def MissionItemProtocol_Waypoints.timeout (this : UInt64) : PMem.M Unit := do
  let fp ← PMem.enter 8
  let r ← MissionItemProtocol_Waypoints.timeout.body fp this
  PMem.leave fp
  return r

/-- C++ `MissionItemProtocol::update : void ()`, `MissionItemProtocol.cpp:379-412`. -/
def MissionItemProtocol.update (this : UInt64) : PMem.M Unit := do
  let t'1 ← PMem.ldB (this + 8)
  if !t'1 then
    return ()
  let t'2 ← PMem.ldU64 (this + 16)
  if (t'2 == (0 : UInt64)) then
    return ()
  let mut tnow : UInt32 := ((← PMem.clock) / 1000).toUInt32
  let t'3 ← PMem.ldU32 (this + 36)
  let t'4 ← PMem.ldU16 (this + 44)
  if (decide ((tnow - t'3) > (UInt16.toUInt32 (t'4)))) then
    PMem.stB (this + 8) false
    MissionItemProtocol_Waypoints.timeout this
    let t'5 ← PMem.ldU64 (this + 16)
    let t'6 ← GCS_MAVLINK.get_chan t'5
    let mut chan : UInt32 := t'6
    let t'7 ← comm_get_txspace chan
    let t'8 ← GCS_MAVLINK.packet_overhead_chan chan
    let mut c'9 : Bool := default
    if (decide ((UInt16.toUInt32 (t'7)) ≥ (Int32.toUInt32 (((UInt32.toInt32 (UInt8.toUInt32 (t'8))) + (4 : Int32)))))) then
      c'9 := true
    else
      gcs_out_of_space_to_send chan
      c'9 := false
    if c'9 then
      let t'10 ← PMem.ldU32 (this + 28)
      let t'11 ← PMem.ldU8 (this + 32)
      let t'12 ← MissionItemProtocol_Waypoints.mission_type this
      mavlink_msg_mission_ack_send chan t'10 t'11 (UInt32.toUInt8 ((15 : UInt32))) (UInt32.toUInt8 (t'12))
    PMem.stU64 (this + 16) (0 : UInt64)
    MissionItemProtocol.free_upload_resources this
    return ()
  let t'13 ← PMem.ldU64 (this + 16)
  let t'14 ← GCS_MAVLINK.get_stream_slowdown_ms t'13
  let mut wp_recv_timeout_ms : UInt32 := ((1000 : UInt32) + (UInt16.toUInt32 (t'14)))
  let t'15 ← PMem.ldU32 (this + 40)
  if (decide ((tnow - t'15) > wp_recv_timeout_ms)) then
    PMem.stU32 (this + 40) tnow
    let t'16 ← MissionItemProtocol_Waypoints.next_item_ap_message_id this
    let t'17 ← PMem.ldU64 (this + 16)
    GCS_MAVLINK.send_message t'17 t'16
  return ()

/-- C++ `GCS_MAVLINK::set_mavlink_message_id_interval : bool (const uint32_t, const uint16_t)`, `GCS_Common.cpp:1220-1231`. -/
def GCS_MAVLINK.set_mavlink_message_id_interval.body (fp : UInt64) (this : UInt64) (mavlink_id : UInt32) (interval_ms : UInt16) : PMem.M Bool := do
  let mut mavlink_id := mavlink_id
  let mut interval_ms := interval_ms
  let t'1 ← GCS_MAVLINK.mavlink_id_to_ap_message_id this mavlink_id
  let mut id : UInt8 := t'1
  if ((UInt32.toInt32 (UInt8.toUInt32 (id))) == (UInt32.toInt32 (UInt8.toUInt32 ((102 : UInt8))))) then
    PMem.stU64 (fp + 0) (UInt32.toUInt64 (mavlink_id))
    let t'2 ← gcs
    GCS.send_text t'2 (6 : UInt32) (0x189bb : UInt64) /- "No ap_message for mavlink id (%u)" -/ (fp + 0)
    return false
  let t'3 ← GCS_MAVLINK.set_ap_message_interval this id interval_ms
  return t'3

def GCS_MAVLINK.set_mavlink_message_id_interval (this : UInt64) (mavlink_id : UInt32) (interval_ms : UInt16) : PMem.M Bool := do
  let fp ← PMem.enter 8
  let r ← GCS_MAVLINK.set_mavlink_message_id_interval.body fp this mavlink_id interval_ms
  PMem.leave fp
  return r

/-- C++ `GCS_MAVLINK::initialise_message_intervals_from_streamrates : void ()`, `GCS_Common.cpp:7288-7313`. -/
def GCS_MAVLINK.initialise_message_intervals_from_streamrates (this : UInt64) : PMem.M Unit := do
  let t'1 ← GCS_MAVLINK.option_enabled this (16 : UInt16)
  if t'1 then
    let t'2 ← GCS_MAVLINK.set_mavlink_message_id_interval this (Int32.toUInt32 ((0 : Int32))) (Int16.toUInt16 (Int32.toInt16 ((1000 : Int32))))
    discard <| pure (t'2)
    return ()
  let mut i : UInt8 := Int8.toUInt8 (Int32.toInt8 ((0 : Int32)))
  let mut first'3 := true
  for _ in PMem.loopFuel do
    if !first'3 then
      let t'4 := i
      let t'5 := (t'4 + 1)
      i := t'5
      pure ()
    first'3 := false
    let t'6 ← PMem.ldU64 (((0xc890 : UInt64) /- &GCS_MAVLINK::all_stream_entries -/ + ((UInt64.toInt64 (UInt8.toUInt64 (i))) * 24).toUInt64) + 8)
    if !((t'6 != (0 : UInt64))) then break
    let t'7 ← PMem.ldU8 ((0xc890 : UInt64) /- &GCS_MAVLINK::all_stream_entries -/ + ((UInt64.toInt64 (UInt8.toUInt64 (i))) * 24).toUInt64)
    GCS_MAVLINK.initialise_message_intervals_for_stream this t'7
  let t'8 ← GCS_MAVLINK.set_mavlink_message_id_interval this (Int32.toUInt32 ((0 : Int32))) (Int16.toUInt16 (Int32.toInt16 ((1000 : Int32))))
  discard <| pure (t'8)
  return ()

/-- C++ `GCS::out_of_time : bool () const`, `GCS.cpp:674-698`. -/
def GCS.out_of_time (this : UInt64) : PMem.M Bool := do
  if (← get).inDelayCb then
    return false
  let t'1 ← AP_BoardConfig.in_config_error
  if t'1 then
    return false
  let t'2 ← GCS_Copter.min_loop_time_remaining_for_message_send_us this
  let t'3 ← AP.scheduler
  let t'4 ← AP_Scheduler.time_available_usec t'3
  if (decide ((UInt32.toInt32 (UInt16.toUInt32 (t'2))) ≤ (UInt32.toInt32 (UInt16.toUInt32 (t'4))))) then
    return false
  return true

/-- C++ `GCS_MAVLINK::GCS_MAVLINK : void (AP_HAL::UARTDriver &)`, `GCS_Common.cpp:136-141`. -/
def GCS_MAVLINK.GCS_MAVLINK (this : UInt64) (uart : UInt64) : PMem.M Unit := do
  PMem.stU16 (this + 12) (Int16.toUInt16 (Int32.toInt16 ((65535 : Int32))))
  AP_Param.AP_Param'2 ((this + 44) + 0)
  AP_Param.AP_Param'2 ((this + 44) + 2)
  AP_Param.AP_Param'2 ((this + 44) + 4)
  AP_Param.AP_Param'2 ((this + 44) + 6)
  AP_Param.AP_Param'2 ((this + 44) + 8)
  AP_Param.AP_Param'2 ((this + 44) + 10)
  AP_Param.AP_Param'2 ((this + 44) + 12)
  AP_Param.AP_Param'2 ((this + 44) + 14)
  AP_Param.AP_Param'2 ((this + 44) + 16)
  AP_Param.AP_Param'2 ((this + 44) + 18)
  AP_Param.AP_Param'2 (this + 64)
  AP_Param.AP_Param'2 (this + 68)
  AP_Param.AP_Param'2 (this + 70)
  PMem.stU16 ((this + 72) + 20) (Int16.toUInt16 (Int32.toInt16 ((10000 : Int32))))
  __mavlink_message.__mavlink_message (this + 104)
  __mavlink_status.__mavlink_status (this + 408)
  AP_Param.ParamToken.ParamToken (this + 492)
  PMem.stU8 (((this + 506) + 0) + 0) (0 : UInt8)
  discard <| PMem.memset (((this + 506) + 0) + 2) 0 2
  discard <| PMem.memset (((this + 506) + 0) + 4) 0 2
  PMem.stU8 (((this + 506) + 6) + 0) (31 : UInt8)
  discard <| PMem.memset (((this + 506) + 6) + 2) 0 2
  discard <| PMem.memset (((this + 506) + 6) + 4) 0 2
  PMem.stI8 (this + 524) (Int32.toInt8 ((-(1 : Int32))))
  Bitmask'102.Bitmask ((this + 528) + 0)
  Bitmask'102.Bitmask ((this + 528) + 20)
  Bitmask'102.Bitmask ((this + 528) + 40)
  Bitmask'102.Bitmask ((this + 528) + 60)
  Bitmask'102.Bitmask ((this + 528) + 80)
  Bitmask'102.Bitmask ((this + 528) + 100)
  Bitmask'102.Bitmask ((this + 528) + 120)
  Bitmask'102.Bitmask ((this + 528) + 140)
  Bitmask'102.Bitmask ((this + 528) + 160)
  Bitmask'102.Bitmask ((this + 528) + 180)
  PMem.stU8 (this + 728) (255 : UInt8)
  Bitmask'102.Bitmask (this + 732)
  Bitmask'102.Bitmask (this + 748)
  JitterCorrection.JitterCorrection (this + 808) (Int16.toUInt16 (Int32.toInt16 ((500 : Int32)))) (Int16.toUInt16 (Int32.toInt16 ((100 : Int32))))
  Location.Location (this + 840)
  AP_Param.setup_object_defaults this (0xbc70 : UInt64) /- &GCS_MAVLINK::var_info -/
  PMem.stU64 (this + 480) uart
  return ()

/-- C++ `GCS::convert_parameters : void ()`, `GCS.cpp:263-271`. -/
def GCS.convert_parameters (this : UInt64) : PMem.M Unit := do
  let t'1 ← AP_Param.convert_parameter_width (this + 160) (2 : UInt32) (Binary64.toBinary32 ((Binary64.ofBits 0x3ff0000000000000 /- 1 -/)))
  discard <| pure (t'1)
  let t'2 ← AP_Param.convert_parameter_width (this + 164) (2 : UInt32) (Binary64.toBinary32 ((Binary64.ofBits 0x3ff0000000000000 /- 1 -/)))
  discard <| pure (t'2)
  let t'3 ← AP_Param.convert_parameter_width (this + 168) (2 : UInt32) (Binary64.toBinary32 ((Binary64.ofBits 0x3ff0000000000000 /- 1 -/)))
  discard <| pure (t'3)
  AP_Param.flush
  return ()

/-- C++ `GCS::init : void ()`, `GCS.cpp:273-279`. -/
def GCS.init (this : UInt64) : PMem.M Unit := do
  GCS.convert_parameters this
  let t'1 ← GCS.sysid_this_mav this
  PMem.stU32 (0xbc50 : UInt64) /- &mavlink_system -/ t'1
  return ()

/-- C++ `GCS_MAVLINK::enable_option : void (Option)`, `functor.h:558-560`. -/
def GCS_MAVLINK.enable_option.body (fp : UInt64) (this : UInt64) (option : UInt16) : PMem.M Unit := do
  let mut option := option
  let t'1 ← AP_ParamT'unsigned_short_2.operator_const_unsigned_short__ (this + 68)
  let t'2 ← PMem.ldU16 t'1
  PMem.stU16 (fp + 0) (Int16.toUInt16 (Int32.toInt16 (((UInt32.toInt32 (UInt16.toUInt32 (t'2))) ||| (UInt32.toInt32 (UInt16.toUInt32 (option)))))))
  AP_ParamTBase'unsigned_short_2.set_and_save (this + 68) (fp + 0)
  return ()

def GCS_MAVLINK.enable_option (this : UInt64) (option : UInt16) : PMem.M Unit := do
  let fp ← PMem.enter 2
  let r ← GCS_MAVLINK.enable_option.body fp this option
  PMem.leave fp
  return r

/-- C++ `GCS_MAVLINK::init : bool (uint8_t)`, `GCS_Common.cpp:143-248`. -/
def GCS_MAVLINK.init.body (fp : UInt64) (this : UInt64) (instance' : UInt8) : PMem.M Bool := do
  let mut instance' := instance'
  let t'1 := Int32.toUInt32 (((UInt32.toInt32 ((0 : UInt32))) + (UInt32.toInt32 (UInt8.toUInt32 (instance')))))
  PMem.stU32 (this + 40) t'1
  let t'2 ← PMem.ldU32 (this + 40)
  let t'3 ← valid_channel t'2
  if !t'3 then
    return false
  let t'4 ← PMem.findSerialProto (1 : Int32) instance'
  PMem.stU64 (this + 448) t'4
  let t'5 ← PMem.ldU64 (this + 448)
  if (t'5 == (0 : UInt64)) then
    return false
  let t'6 ← PMem.ldU64 (this + 448)
  let t'7 ← PMem.serialDevId t'6
  PMem.stU32 (fp + 0) t'7
  AP_ParamTBase'unsigned_int_3.set (this + 64) (fp + 0)
  let t'8 ← AP_ParamT'signed_char_1.operator_const_signed_char__ (this + 70)
  let t'9 ← PMem.ldI8 t'8
  if !(t'9 != (0 : Int8)) then
    let t'10 ← AP.serialmanager
    let sm : UInt64 := t'10
    PMem.stI8 (fp + 4) (Int32.toInt8 ((1 : Int32)))
    AP_ParamTBase'signed_char_1.set_and_save (this + 70) (fp + 4)
    if false then
      GCS_MAVLINK.enable_option this (2 : UInt16)
    if false then
      GCS_MAVLINK.enable_option this (4 : UInt16)
  let t'11 ← GCS_MAVLINK.option_enabled this (2 : UInt16)
  if t'11 then
    let t'12 ← PMem.ldU32 (this + 40)
    GCS_MAVLINK.set_channel_private t'12
  let t'13 ← PMem.ldU64 (this + 480)
  (discard <| PMem.halDev "AP_HAL::UARTDriver::begin" t'13 #[((Int32.toUInt32 ((115200 : Int32)))).toUInt64])
  let mut old_flow_control : UInt32 := (0 : UInt32)
  for i'14 in [0:3] do
    let i : UInt8 := UInt8.ofNat i'14
    let t'15 ← PMem.ldU64 ((0xba88 : UInt64) /- &hal -/ + 80)
    discard <| PMem.hal "AP_HAL::Scheduler::delay" t'15 #[(UInt16.toUInt64 ((Int16.toUInt16 (Int32.toInt16 ((1 : Int32))))))]
    let t'16 ← PMem.ldU64 (this + 480)
    let t'17 ← PMem.uartWrite1 t'16 (Int8.toUInt8 (Int32.toInt8 ((48 : Int32))))
    discard <| pure (t'17)
    let t'18 ← PMem.ldU64 (this + 480)
    let t'19 ← PMem.uartWrite1 t'18 (Int8.toUInt8 (Int32.toInt8 ((32 : Int32))))
    discard <| pure (t'19)
  let t'20 ← PMem.ldU64 ((0xba88 : UInt64) /- &hal -/ + 80)
  discard <| PMem.hal "AP_HAL::Scheduler::delay" t'20 #[(UInt16.toUInt64 ((Int16.toUInt16 (Int32.toInt16 ((1 : Int32))))))]
  let t'21 ← PMem.ldU64 (this + 448)
  let t'22 ← AP_SerialManager.UARTState.baudrate t'21
  let t'23 ← PMem.ldU64 (this + 480)
  (discard <| PMem.halDev "AP_HAL::UARTDriver::begin" t'23 #[(t'22).toUInt64])
  let t'24 ← PMem.ldU64 (this + 480)
  let t'25 ← PMem.ldU32 (this + 40)
  PMem.stU64 ((0xc9e8 : UInt64) /- &mavlink_comm_port -/ + ((UInt64.toInt64 (UInt32.toUInt64 (t'25))) * 8).toUInt64) t'24
  let mut mavlink_protocol : Int32 := (2 : Int32)
  if ((mavlink_protocol == (2 : Int32)) || (mavlink_protocol == (43 : Int32))) then
    pure ()
  else
    let t'26 := ((this + 408) + 16)
    let t'27 ← PMem.ldU8 t'26
    let t'28 := (t'27 ||| (Int8.toUInt8 (Int32.toInt8 ((2 : Int32)))))
    PMem.stU8 t'26 t'28
  return true

def GCS_MAVLINK.init (this : UInt64) (instance' : UInt8) : PMem.M Bool := do
  let fp ← PMem.enter 5
  let r ← GCS_MAVLINK.init.body fp this instance'
  PMem.leave fp
  return r

/-- C++ `MAVLink_routing::send_to_components : void (const char *, const mavlink_msg_entry_t *, const uint8_t)`, `MAVLink_routing.cpp:281-324`. -/
def MAVLink_routing.send_to_components'2.body (fp : UInt64) (this : UInt64) (pkt : UInt64) (entry : UInt64) (pkt_len : UInt8) : PMem.M Unit := do
  let mut pkt := pkt
  let mut entry := entry
  PMem.stU8 (fp + 0) pkt_len
  let mut i : UInt8 := Int8.toUInt8 (Int32.toInt8 ((0 : Int32)))
  let mut first'1 := true
  for _ in PMem.loopFuel do
    if !first'1 then
      let t'2 := i
      let t'3 := (t'2 + 1)
      i := t'3
      pure ()
    first'1 := false
    let t'4 ← PMem.ldU8 this
    if !((decide ((UInt32.toInt32 (UInt8.toUInt32 (i))) < (UInt32.toInt32 (UInt8.toUInt32 (t'4)))))) then break
    let t'5 ← PMem.ldU32 ((this + 4) + ((UInt64.toInt64 (UInt8.toUInt64 (i))) * 16).toUInt64)
    let t'6 ← PMem.ldU32 (0xbc50 : UInt64) /- &mavlink_system -/
    if (t'5 != t'6) then
      continue
    let t'7 ← PMem.ldU32 (((this + 4) + ((UInt64.toInt64 (UInt8.toUInt64 (i))) * 16).toUInt64) + 8)
    let t'8 ← PMem.ldB ((fp + 8) + ((UInt64.toInt64 (UInt32.toUInt64 (t'7))) * 1).toUInt64)
    if t'8 then
      continue
    let t'9 ← PMem.ldU32 (((this + 4) + ((UInt64.toInt64 (UInt8.toUInt64 (i))) * 16).toUInt64) + 8)
    let t'10 ← comm_get_txspace t'9
    let t'11 ← PMem.ldU8 (entry + 6)
    let t'12 ← PMem.ldU32 (((this + 4) + ((UInt64.toInt64 (UInt8.toUInt64 (i))) * 16).toUInt64) + 8)
    let t'13 ← GCS_MAVLINK.packet_overhead_chan t'12
    if (decide ((UInt32.toInt32 (UInt16.toUInt32 (t'10))) < ((UInt32.toInt32 (UInt16.toUInt32 ((UInt8.toUInt16 (t'11))))) + (UInt32.toInt32 (UInt8.toUInt32 (t'13)))))) then
      continue
    let t'14 ← PMem.ldU8 (entry + 6)
    let t'15 ← PMem.ldU8 (fp + 0)
    if (decide ((UInt32.toInt32 (UInt8.toUInt32 (t'14))) > (UInt32.toInt32 (UInt8.toUInt32 (t'15))))) then
      pure ()
    let t'16 ← PMem.ldU32 (((this + 4) + ((UInt64.toInt64 (UInt8.toUInt64 (i))) * 16).toUInt64) + 8)
    let t'17 ← PMem.ldU32 entry
    let t'18 ← PMem.ldU8 (entry + 5)
    let t'19 ← MIN'unsigned_char_unsigned_char (entry + 6) (fp + 0)
    let t'20 ← PMem.ldU8 t'19
    let t'21 ← PMem.ldU8 (entry + 4)
    let t'22 ← PMem.ldU32 (0xbc50 : UInt64) /- &mavlink_system -/
    _mav_finalize_message_chan_send_target t'16 t'17 pkt t'18 t'20 t'21 t'22
    let t'23 ← PMem.ldU32 (((this + 4) + ((UInt64.toInt64 (UInt8.toUInt64 (i))) * 16).toUInt64) + 8)
    PMem.stB ((fp + 8) + ((UInt64.toInt64 (UInt32.toUInt64 (t'23))) * 1).toUInt64) true
  return ()

def MAVLink_routing.send_to_components'2 (this : UInt64) (pkt : UInt64) (entry : UInt64) (pkt_len : UInt8) : PMem.M Unit := do
  let fp ← PMem.enter 24
  let r ← MAVLink_routing.send_to_components'2.body fp this pkt entry pkt_len
  PMem.leave fp
  return r

/-- C++ `MAVLink_routing::send_to_components : void (uint32_t, const char *, uint8_t)`, `MAVLink_routing.cpp:272-279`. -/
def MAVLink_routing.send_to_components (this : UInt64) (msgid : UInt32) (pkt : UInt64) (pkt_len : UInt8) : PMem.M Unit := do
  let mut msgid := msgid
  let mut pkt := pkt
  let mut pkt_len := pkt_len
  let t'1 ← mavlink_get_msg_entry msgid
  let mut entry : UInt64 := t'1
  if (entry == (0 : UInt64)) then
    return ()
  MAVLink_routing.send_to_components'2 this pkt entry pkt_len
  return ()

/-- C++ `GCS_MAVLINK::send_to_components : void (uint32_t, const char *, uint8_t)`, `AP_Mission.h:467-?`. -/
def GCS_MAVLINK.send_to_components (msgid : UInt32) (pkt : UInt64) (pkt_len : UInt8) : PMem.M Unit := do
  let mut msgid := msgid
  let mut pkt := pkt
  let mut pkt_len := pkt_len
  MAVLink_routing.send_to_components (0xc740 : UInt64) /- &GCS_MAVLINK::routing -/ msgid pkt pkt_len
  return ()

/-- C++ `GCS_MAVLINK::available_modes_changed : void ()`, `GCS_Common.cpp:6592-6604`. -/
def GCS_MAVLINK.available_modes_changed (this : UInt64) : PMem.M Unit := do
  let t'1 ← PMem.ldB (this + 871)
  if !t'1 then
    return ()
  let t'2 := ((this + 871) + 4)
  let t'3 ← PMem.ldU8 t'2
  let t'4 := (t'3 + (Int8.toUInt8 (Int32.toInt8 ((1 : Int32)))))
  PMem.stU8 t'2 t'4
  let t'5 ← GCS_MAVLINK.set_ap_message_interval this (99 : UInt8) (Int16.toUInt16 (Int32.toInt16 ((5000 : Int32))))
  discard <| pure (t'5)
  return ()

/-- C++ `GCS::available_modes_changed : void ()`, `GCS.cpp:756-761`. -/
def GCS.available_modes_changed (this : UInt64) : PMem.M Unit := do
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
    let c : UInt64 := t'5
    GCS_MAVLINK.available_modes_changed c
  return ()

end Vehicle_lib
