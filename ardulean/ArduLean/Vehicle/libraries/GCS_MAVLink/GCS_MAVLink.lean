import ArduLean.Runtime.Bridge
import ArduLean.Vehicle.libraries.AP_Math.AP_Math
import ArduLean.Vehicle.libraries.AP_HAL.AP_HAL
import ArduLean.Vehicle.libraries.AP_Param.AP_Param
import ArduLean.Vehicle.libraries.AP_Mission.AP_Mission
import ArduLean.Vehicle.ArduCopter.ArduCopter
import ArduLean.Vehicle.libraries.AP_Common.AP_Common

/-!
ArduPilot `libraries/GCS_MAVLink`, part 1 of 3. Sources: `libraries/GCS_MAVLink/GCS_Common.cpp`, `libraries/GCS_MAVLink/GCS_MAVLink.cpp`, `libraries/GCS_MAVLink/GCS_Param.cpp`, `libraries/GCS_MAVLink/GCS.cpp`, `libraries/GCS_MAVLink/GCS.h`, `libraries/GCS_MAVLink/MissionItemProtocol.cpp`, `libraries/GCS_MAVLink/GCS_Signing.cpp`, `libraries/GCS_MAVLink/MissionItemProtocol_Waypoints.h` and 3 more.

Items of `lean/Vehicle_lib.lean` (the vehicle translation), unchanged; placed by `tools/split_modules.py` (`ArduLean/Vehicle/INDEX.md`).
-/

open FloatLib.Floats (Binary32 Binary64)

set_option linter.unusedVariables false
set_option linter.unreachableTactic false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false

namespace Vehicle_lib

/-- C++ `GCS::get_singleton : class GCS *()`, `GCS.h:1161-1163`. -/
def GCS.get_singleton  : PMem.M UInt64 := do
  let t'1 ← PMem.ldU64 (0xc738 : UInt64) /- &GCS::_singleton -/
  return t'1

/-- C++ `gcs : GCS &()`, `GCS_Common.cpp:7695-7698`. -/
def gcs  : PMem.M UInt64 := do
  let t'1 ← GCS.get_singleton
  return t'1

/-- `GCS_MAVLINK.mav_param_type` as a pure function of its arguments (it reads and writes no memory). -/
def GCS_MAVLINK.mav_param_type.pure' (t : UInt32) : Id UInt32 := do
  let mut t := t
  if ((UInt32.toInt32 (t)) == (UInt32.toInt32 ((1 : UInt32)))) then
    return (2 : UInt32)
  if ((UInt32.toInt32 (t)) == (UInt32.toInt32 ((2 : UInt32)))) then
    return (4 : UInt32)
  if ((UInt32.toInt32 (t)) == (UInt32.toInt32 ((3 : UInt32)))) then
    return (6 : UInt32)
  return (9 : UInt32)

/-- C++ `GCS_MAVLINK::mav_param_type : MAV_PARAM_TYPE (enum ap_var_type)`, `GCS_MAVLink.cpp:119-132`. -/
def GCS_MAVLINK.mav_param_type (t : UInt32) : PMem.M UInt32 :=
  pure (_root_.Vehicle_lib.GCS_MAVLINK.mav_param_type.pure' t)

/-- C++ `GCS::num_gcs : uint8_t () const`, `AP_Common.h:1219-?`. -/
def GCS.num_gcs (this : UInt64) : PMem.M UInt8 := do
  let t'1 ← PMem.ldU8 (this + 28)
  return t'1

/-- C++ `GCS_MAVLINK::is_private : bool (mavlink_channel_t)`, `AP_Mission.h:449-451`. -/
def GCS_MAVLINK.is_private'2 (_chan : UInt32) : PMem.M Bool := do
  let mut _chan := _chan
  let t'1 ← PMem.ldU32 (0xdf08 : UInt64) /- &GCS_MAVLINK::mavlink_private -/
  return ((t'1 &&& ((1 : UInt32) <<< _chan)) != (Int32.toUInt32 ((0 : Int32))))

/-- C++ `GCS_MAVLINK::is_private : bool () const`, `AP_Mission.h:454-?`. -/
def GCS_MAVLINK.is_private (this : UInt64) : PMem.M Bool := do
  let t'1 ← PMem.ldU32 (this + 40)
  let t'2 ← GCS_MAVLINK.is_private'2 t'1
  return t'2

/-- C++ `GCS_MAVLINK::option_enabled : bool (Option) const`, `functor.h:555-557`. -/
def GCS_MAVLINK.option_enabled (this : UInt64) (option : UInt16) : PMem.M Bool := do
  let mut option := option
  let t'1 ← AP_ParamT'unsigned_short_2.operator_const_unsigned_short__ (this + 68)
  let t'2 ← PMem.ldU16 t'1
  return ((UInt32.toInt32 (UInt16.toUInt32 (t'2))) &&& (UInt32.toInt32 (UInt16.toUInt32 (option)))) != (0 : Int32)

/-- C++ `GCS_MAVLINK::active_channel_mask : mavlink_channel_mask_t ()`, `AP_Mission.h:436-?`. -/
def GCS_MAVLINK.active_channel_mask  : PMem.M UInt32 := do
  let t'1 ← PMem.ldU32 (0xebd8 : UInt64) /- &GCS_MAVLINK::mavlink_active -/
  return t'1

/-- C++ `GCS_MAVLINK::is_active : bool () const`, `mavlink_msg_mission_ack.h:304-306`. -/
def GCS_MAVLINK.is_active (this : UInt64) : PMem.M Bool := do
  let t'1 ← GCS_MAVLINK.active_channel_mask
  let t'2 ← PMem.ldU32 (this + 40)
  return (t'1 &&& (Int32.toUInt32 (((1 : Int32) <<< ((UInt32.toInt32 (t'2)) - (UInt32.toInt32 ((0 : UInt32)))))))) != (0 : UInt32)

/-- `GCS_MAVLINK.channel_status` as a pure function of its arguments (it reads and writes no memory). -/
def GCS_MAVLINK.channel_status.pure' (this : UInt64) : Id UInt64 := do
  return (this + 408)

/-- C++ `GCS_MAVLINK::channel_status : mavlink_status_t *()`, `GCS.h:190-?`. -/
def GCS_MAVLINK.channel_status (this : UInt64) : PMem.M UInt64 :=
  pure (_root_.Vehicle_lib.GCS_MAVLINK.channel_status.pure' this)

/-- C++ `mavlink_get_channel_status : mavlink_status_t *(uint8_t)`, `GCS_MAVLink.cpp:56-66`. -/
def mavlink_get_channel_status (chan : UInt8) : PMem.M UInt64 := do
  let mut chan := chan
  let t'1 ← gcs
  let t'2 ← GCS_Copter.chan t'1 chan
  let mut link : UInt64 := t'2
  if (link == (0 : UInt64)) then
    return (0 : UInt64)
  let t'3 ← GCS_MAVLINK.channel_status link
  return t'3

/-- C++ `GCS_MAVLINK::out_of_space_to_send : void ()`, `AP_Common.h:219-?`. -/
def GCS_MAVLINK.out_of_space_to_send (this : UInt64) : PMem.M Unit := do
  let t'1 := (this + 860)
  let t'2 ← PMem.ldU16 t'1
  let t'3 := (t'2 + 1)
  PMem.stU16 t'1 t'3
  return ()

/-- C++ `gcs_out_of_space_to_send : void (mavlink_channel_t)`, `GCS.cpp:700-707`. -/
def gcs_out_of_space_to_send (chan : UInt32) : PMem.M Unit := do
  let mut chan := chan
  let t'1 ← gcs
  let t'2 ← GCS_Copter.chan t'1 (UInt32.toUInt8 (chan))
  let mut link : UInt64 := t'2
  if (link == (0 : UInt64)) then
    return ()
  GCS_MAVLINK.out_of_space_to_send link
  return ()

/-- C++ `comm_send_lock : void (mavlink_channel_t, uint16_t)`, `GCS_MAVLink.cpp:183-191`. -/
def comm_send_lock (chan_m : UInt32) (size : UInt16) : PMem.M Unit := do
  let mut chan_m := chan_m
  let mut size := size
  let mut chan : UInt8 := UInt32.toUInt8 (chan_m)
  let t'1 ← PMem.ldU64 ((0xc9e8 : UInt64) /- &mavlink_comm_port -/ + ((UInt64.toInt64 (UInt8.toUInt64 (chan))) * 8).toUInt64)
  let t'2 ← PMem.uartTxspace t'1
  if (decide (t'2 < (UInt16.toUInt32 (size)))) then
    PMem.stB ((0xebc8 : UInt64) /- &chan_discard -/ + ((UInt64.toInt64 (UInt8.toUInt64 (chan))) * 1).toUInt64) true
    gcs_out_of_space_to_send chan_m
  return ()

/-- `valid_channel` as a pure function of its arguments (it reads and writes no memory). -/
def valid_channel.pure' (chan : UInt32) : Id Bool := do
  let mut chan := chan
  return (decide ((UInt32.toInt32 (chan)) < (16 : Int32)))

/-- C++ `valid_channel : bool (mavlink_channel_t)`, `GCS_MAVLink.h:62-65`. -/
def valid_channel (chan : UInt32) : PMem.M Bool :=
  pure (_root_.Vehicle_lib.valid_channel.pure' chan)

/-- C++ `comm_send_buffer : void (mavlink_channel_t, const uint8_t *, uint8_t)`, `GCS_MAVLink.cpp:151-175`. -/
def comm_send_buffer (chan : UInt32) (buf : UInt64) (len : UInt8) : PMem.M Unit := do
  let mut chan := chan
  let mut buf := buf
  let mut len := len
  let t'1 ← valid_channel chan
  let mut sc'3 := !t'1
  if !sc'3 then
    let t'2 ← PMem.ldU64 ((0xc9e8 : UInt64) /- &mavlink_comm_port -/ + ((UInt64.toInt64 (UInt32.toUInt64 (chan))) * 8).toUInt64)
    sc'3 := (t'2 == (0 : UInt64))
  let mut sc'5 := sc'3
  if !sc'5 then
    let t'4 ← PMem.ldB ((0xebc8 : UInt64) /- &chan_discard -/ + ((UInt64.toInt64 (UInt32.toUInt64 (chan))) * 1).toUInt64)
    sc'5 := t'4
  if sc'5 then
    return ()
  let t'6 ← PMem.ldB ((0xbf70 : UInt64) /- &gcs_alternative_active -/ + ((UInt64.toInt64 (UInt32.toUInt64 (chan))) * 1).toUInt64)
  if t'6 then
    return ()
  let t'7 ← PMem.ldU64 ((0xc9e8 : UInt64) /- &mavlink_comm_port -/ + ((UInt64.toInt64 (UInt32.toUInt64 (chan))) * 8).toUInt64)
  let t'8 ← PMem.uartWrite t'7 buf (UInt8.toUInt64 (len))
  let mut written : UInt64 := t'8
  if ((decide (written < (UInt8.toUInt64 (len)))) && (!false)) then
    pure ()
  return ()

/-- C++ `comm_send_unlock : void (mavlink_channel_t)`, `GCS_MAVLink.cpp:196-201`. -/
def comm_send_unlock (chan_m : UInt32) : PMem.M Unit := do
  let mut chan_m := chan_m
  let mut chan : UInt8 := UInt32.toUInt8 (chan_m)
  PMem.stB ((0xebc8 : UInt64) /- &chan_discard -/ + ((UInt64.toInt64 (UInt8.toUInt64 (chan))) * 1).toUInt64) false
  discard <| pure (true)
  return ()

/-- C++ `GCS_MAVLINK::txspace : uint16_t () const`, `AP_Common.h:206-214`. -/
def GCS_MAVLINK.txspace.body (fp : UInt64) (this : UInt64) : PMem.M UInt16 := do
  let t'1 ← PMem.ldB (this + 870)
  if t'1 then
    return Int16.toUInt16 (Int32.toInt16 ((0 : Int32)))
  let t'2 ← PMem.ldU64 (this + 480)
  let t'3 ← PMem.uartTxspace t'2
  PMem.stU32 (fp + 0) t'3
  PMem.stU32 (fp + 4) (8192 : UInt32)
  let t'4 ← MIN'unsigned_int_unsigned_int (fp + 0) (fp + 4)
  let t'5 ← PMem.ldU32 t'4
  return UInt32.toUInt16 (t'5)

def GCS_MAVLINK.txspace (this : UInt64) : PMem.M UInt16 := do
  let fp ← PMem.enter 8
  let r ← GCS_MAVLINK.txspace.body fp this
  PMem.leave fp
  return r

/-- C++ `GCS_MAVLINK::packet_overhead_chan : uint8_t (mavlink_channel_t)`, `GCS_Signing.cpp:247-273`. -/
def GCS_MAVLINK.packet_overhead_chan (chan : UInt32) : PMem.M UInt8 := do
  let mut chan := chan
  let mut reserved_space : UInt8 := Int8.toUInt8 (Int32.toInt8 ((0 : Int32)))
  let t'1 ← PMem.ldU32 (0xc888 : UInt64) /- &GCS_MAVLINK::reserve_param_space_start_ms -/
  let mut sc'3 := (t'1 != (Int32.toUInt32 ((0 : Int32))))
  if sc'3 then
    let t'2 ← PMem.ldU32 (0xc888 : UInt64) /- &GCS_MAVLINK::reserve_param_space_start_ms -/
    sc'3 := (decide (((((← PMem.clock) / 1000).toUInt32) - t'2) < (Int32.toUInt32 ((2000 : Int32)))))
  if sc'3 then
    let t'4 := Int8.toUInt8 (Int32.toInt8 ((100 : Int32)))
    reserved_space := t'4
  else
    let t'5 := Int32.toUInt32 ((0 : Int32))
    PMem.stU32 (0xc888 : UInt64) /- &GCS_MAVLINK::reserve_param_space_start_ms -/ t'5
  let t'6 ← mavlink_get_channel_status (UInt32.toUInt8 (chan))
  let mut status : UInt64 := t'6
  let mut ext_header_space : UInt8 := Int8.toUInt8 (Int32.toInt8 (((3 : Int32) + (4 : Int32))))
  let mut sc'8 := (status != (0 : UInt64))
  if sc'8 then
    let t'7 ← PMem.ldU64 (status + 24)
    sc'8 := (t'7 != 0)
  let mut sc'11 := sc'8
  if sc'11 then
    let t'9 ← PMem.ldU64 (status + 24)
    let t'10 ← PMem.ldU8 t'9
    sc'11 := ((UInt32.toInt32 (UInt8.toUInt32 (t'10))) &&& (1 : Int32)) != (0 : Int32)
  if sc'11 then
    return Int8.toUInt8 (Int32.toInt8 (((((((9 : Int32) + (1 : Int32)) + (2 : Int32)) + (UInt32.toInt32 (UInt8.toUInt32 (ext_header_space)))) + (13 : Int32)) + (UInt32.toInt32 (UInt8.toUInt32 (reserved_space))))))
  return Int8.toUInt8 (Int32.toInt8 ((((((9 : Int32) + (1 : Int32)) + (2 : Int32)) + (UInt32.toInt32 (UInt8.toUInt32 (ext_header_space)))) + (UInt32.toInt32 (UInt8.toUInt32 (reserved_space))))))

/-- C++ `GCS_MAVLINK::packet_overhead : uint8_t () const`, `functor.h:536-?`. -/
def GCS_MAVLINK.packet_overhead (this : UInt64) : PMem.M UInt8 := do
  let t'1 ← PMem.ldU32 (this + 40)
  let t'2 ← GCS_MAVLINK.packet_overhead_chan t'1
  return t'2

/-- C++ `GCS_MAVLINK::check_payload_size : bool (uint16_t)`, `GCS.cpp:712-719`. -/
def GCS_MAVLINK.check_payload_size (this : UInt64) (max_payload_len : UInt16) : PMem.M Bool := do
  let mut max_payload_len := max_payload_len
  let t'1 ← GCS_MAVLINK.txspace this
  let t'2 ← GCS_MAVLINK.packet_overhead this
  if (decide ((UInt16.toUInt32 (t'1)) < (Int32.toUInt32 (((UInt32.toInt32 (UInt8.toUInt32 (t'2))) + (UInt32.toInt32 (UInt16.toUInt32 (max_payload_len)))))))) then
    let t'3 ← PMem.ldU32 (this + 40)
    gcs_out_of_space_to_send t'3
    return false
  return true

/-- C++ `GCS_MAVLINK::locked : bool () const`, `AP_Mission.h:430-432`. -/
def GCS_MAVLINK.locked (this : UInt64) : PMem.M Bool := do
  let t'1 ← PMem.ldB (this + 870)
  return t'1

/-- `GCS_MAVLINK.channel_buffer` as a pure function of its arguments (it reads and writes no memory). -/
def GCS_MAVLINK.channel_buffer.pure' (this : UInt64) : Id UInt64 := do
  return (this + 104)

/-- C++ `GCS_MAVLINK::channel_buffer : mavlink_message_t *()`, `GCS.h:189-?`. -/
def GCS_MAVLINK.channel_buffer (this : UInt64) : PMem.M UInt64 :=
  pure (_root_.Vehicle_lib.GCS_MAVLINK.channel_buffer.pure' this)

/-- C++ `GCS_MAVLINK::packetReceived : void (const mavlink_status_t &, const mavlink_message_t &)`, `GCS_Common.cpp:1864-1882`. -/
def GCS_MAVLINK.packetReceived (this : UInt64) (status : UInt64) (msg : UInt64) : PMem.M Unit := do
  let t'1 ← PMem.ldBits msg 104 24
  let mut sc'3 := ((UInt32.toInt32 ((UInt64.toUInt32 (t'1)))) != (166 : Int32))
  if sc'3 then
    let t'2 ← PMem.ldBits msg 104 24
    sc'3 := ((UInt32.toInt32 ((UInt64.toUInt32 (t'2)))) != (109 : Int32))
  if sc'3 then
    let t'4 := (0xebd8 : UInt64) /- &GCS_MAVLINK::mavlink_active -/
    let t'5 ← PMem.ldU32 t'4
    let t'6 ← PMem.ldU32 (this + 40)
    let t'7 := (t'5 ||| ((1 : UInt32) <<< (Int32.toUInt32 (((UInt32.toInt32 (t'6)) - (UInt32.toInt32 ((0 : UInt32))))))))
    PMem.stU32 t'4 t'7
  let mut mavlink_protocol : Int32 := (2 : Int32)
  let t'8 ← PMem.ldU8 (status + 16)
  let mut sc'10 := !(((UInt32.toInt32 (UInt8.toUInt32 (t'8))) &&& (1 : Int32)) != (0 : Int32))
  if sc'10 then
    let t'9 ← PMem.ldU8 (status + 16)
    sc'10 := ((UInt32.toInt32 (UInt8.toUInt32 (t'9))) &&& (2 : Int32)) != (0 : Int32)
  if (sc'10 && ((mavlink_protocol == (2 : Int32)) || (mavlink_protocol == (43 : Int32)))) then
    let t'11 := ((this + 408) + 16)
    let t'12 ← PMem.ldU8 t'11
    let t'13 := (t'12 &&& (Int8.toUInt8 (Int32.toInt8 ((~~~(2 : Int32))))))
    PMem.stU8 t'11 t'13
  return ()

/-- C++ `GCS_MAVLINK::get_chan : mavlink_channel_t () const`, `mavlink_msg_mission_ack.h:311-?`. -/
def GCS_MAVLINK.get_chan (this : UInt64) : PMem.M UInt32 := do
  let t'1 ← PMem.ldU32 (this + 40)
  return t'1

/-- C++ `comm_get_txspace : uint16_t (mavlink_channel_t)`, `GCS_MAVLink.cpp:139-146`. -/
def comm_get_txspace (chan : UInt32) : PMem.M UInt16 := do
  let mut chan := chan
  let t'1 ← gcs
  let t'2 ← GCS_Copter.chan t'1 (UInt32.toUInt8 (chan))
  let mut link : UInt64 := t'2
  if (link == (0 : UInt64)) then
    return Int16.toUInt16 (Int32.toInt16 ((0 : Int32)))
  let t'3 ← GCS_MAVLINK.txspace link
  return t'3

/-- C++ `GCS_MAVLINK::private_channel_mask : mavlink_channel_mask_t ()`, `AP_Mission.h:442-?`. -/
def GCS_MAVLINK.private_channel_mask  : PMem.M UInt32 := do
  let t'1 ← PMem.ldU32 (0xdf08 : UInt64) /- &GCS_MAVLINK::mavlink_private -/
  return t'1

/-- C++ `GCS::sysid_is_gcs : bool (uint32_t) const`, `GCS.cpp:745-753`. -/
def GCS.sysid_is_gcs (this : UInt64) (_sysid : UInt32) : PMem.M Bool := do
  let mut _sysid := _sysid
  let t'1 ← AP_ParamT'unsigned_int_3.operator_const_unsigned_int__ (this + 164)
  let t'2 ← PMem.ldU32 t'1
  let mut low : UInt32 := t'2
  let t'3 ← AP_ParamT'unsigned_int_3.operator_const_unsigned_int__ (this + 168)
  let t'4 ← PMem.ldU32 t'3
  let mut high : UInt32 := t'4
  if (decide (high ≤ low)) then
    return (low == _sysid)
  return ((decide (_sysid ≥ low)) && (decide (_sysid ≤ high)))

/-- C++ `GCS::option_is_enabled : bool (Option) const`, `AP_Common.h:1258-1260`. -/
def GCS.option_is_enabled (this : UInt64) (option : Int32) : PMem.M Bool := do
  let mut option := option
  let t'1 ← AP_ParamT'short_2.operator_const_short__ (this + 172)
  let t'2 ← PMem.ldI16 t'1
  return (((Int16.toInt32 (t'2)) &&& (UInt32.toInt32 (UInt16.toUInt32 ((Int16.toUInt16 (Int32.toInt16 (option))))))) != (0 : Int32))

/-- C++ `GCS_MAVLINK::accept_packet : bool (const mavlink_status_t &, const mavlink_message_t &) const`, `GCS_Common.cpp:7386-7409`. -/
def GCS_MAVLINK.accept_packet (this : UInt64) (status : UInt64) (msg : UInt64) : PMem.M Bool := do
  let t'1 ← PMem.ldU32 (msg + 8)
  let t'2 ← PMem.ldU32 (0xbc50 : UInt64) /- &mavlink_system -/
  if (t'1 == t'2) then
    return true
  let t'3 ← PMem.ldU32 (msg + 8)
  let t'4 ← gcs
  let t'5 ← GCS.sysid_is_gcs t'4 t'3
  if t'5 then
    return true
  let t'6 ← PMem.ldBits msg 104 24
  let mut sc'8 := ((UInt32.toInt32 ((UInt64.toUInt32 (t'6)))) == (166 : Int32))
  if !sc'8 then
    let t'7 ← PMem.ldBits msg 104 24
    sc'8 := ((UInt32.toInt32 ((UInt64.toUInt32 (t'7)))) == (109 : Int32))
  if sc'8 then
    return true
  let t'9 ← gcs
  let t'10 ← GCS.option_is_enabled t'9 (1 : Int32)
  if !t'10 then
    return true
  return false

/-- C++ `GCS_MAVLINK::streaming_channel_mask : mavlink_channel_mask_t ()`, `AP_Mission.h:439-?`. -/
def GCS_MAVLINK.streaming_channel_mask  : PMem.M UInt32 := do
  let t'1 ← PMem.ldU32 (0xbf88 : UInt64) /- &GCS_MAVLINK::chan_is_streaming -/
  return t'1

/-- C++ `GCS::statustext_send_channel_mask : mavlink_channel_mask_t () const`, `GCS.cpp:284-296`. -/
def GCS.statustext_send_channel_mask (this : UInt64) : PMem.M UInt32 := do
  let mut ret : UInt32 := Int32.toUInt32 ((0 : Int32))
  let t'1 ← GCS_MAVLINK.active_channel_mask
  let t'2 := (ret ||| t'1)
  ret := t'2
  let t'3 ← GCS_MAVLINK.streaming_channel_mask
  let t'4 := (ret ||| t'3)
  ret := t'4
  let t'5 ← GCS_MAVLINK.private_channel_mask
  let t'6 := (ret &&& (~~~t'5))
  ret := t'6
  let mut i : UInt8 := Int8.toUInt8 (Int32.toInt8 ((0 : Int32)))
  let mut first'7 := true
  for _ in PMem.loopFuel do
    if !first'7 then
      let t'8 := i
      let t'9 := (t'8 + 1)
      i := t'9
      pure ()
    first'7 := false
    let t'10 ← GCS.num_gcs this
    if !((decide ((UInt32.toInt32 (UInt8.toUInt32 (i))) < (UInt32.toInt32 (UInt8.toUInt32 (t'10)))))) then break
    let t'11 ← GCS_Copter.chan'2 this i
    let t'12 ← GCS_MAVLINK.option_enabled t'11 (16 : UInt16)
    if t'12 then
      let t'13 := (ret &&& (~~~((1 : UInt32) <<< (Int32.toUInt32 ((UInt32.toInt32 (UInt8.toUInt32 (i))))))))
      ret := t'13
  return ret

/-- `GCS.statustext_queue` as a pure function of its arguments (it reads and writes no memory). -/
def GCS.statustext_queue.pure' (this : UInt64) : Id UInt64 := do
  return (this + 440)

/-- C++ `GCS::statustext_queue : StatusTextQueue &()`, `sitl.h:1189-1191`. -/
def GCS.statustext_queue (this : UInt64) : PMem.M UInt64 :=
  pure (_root_.Vehicle_lib.GCS.statustext_queue.pure' this)

/-- C++ `GCS::StatusTextQueue::prune : void ()`, `GCS_Common.cpp:2651-2678`. -/
def GCS.StatusTextQueue.prune (this : UInt64) : PMem.M Unit := do
  let mut now_ms : UInt32 := ((← PMem.clock) / 1000).toUInt32
  let t'1 ← PMem.ldU32 (this + 24)
  if (decide ((now_ms - t'1) < (Int32.toUInt32 ((1000 : Int32))))) then
    return ()
  PMem.stU32 (this + 24) now_ms
  let mut now16_ms : UInt16 := ((← PMem.clock) / 1000).toUInt16
  let mut idx : UInt8 := Int8.toUInt8 (Int32.toInt8 ((0 : Int32)))
  let mut first'2 := true
  for _ in PMem.loopFuel do
    first'2 := false
    let t'3 ← ObjectArray'GCS_statustext_t.available this
    if !((decide ((UInt32.toInt32 (UInt8.toUInt32 (idx))) < (UInt32.toInt32 (UInt16.toUInt32 (t'3)))))) then break
    let t'4 ← ObjectArray'GCS_statustext_t.operator__ this (UInt8.toUInt16 (idx))
    let mut statustext : UInt64 := t'4
    if (statustext == (0 : UInt64)) then
      break
    let t'5 ← PMem.ldU16 (statustext + 56)
    let mut age : UInt16 := Int16.toUInt16 (Int32.toInt16 (((UInt32.toInt32 (UInt16.toUInt32 (now16_ms))) - (UInt32.toInt32 (UInt16.toUInt32 (t'5))))))
    if (decide ((UInt32.toInt32 (UInt16.toUInt32 (age))) > (5000 : Int32))) then
      let t'6 ← ObjectArray'GCS_statustext_t.remove this (UInt8.toUInt16 (idx))
      discard <| pure (t'6)
      continue
    break
  return ()

/-- C++ `GCS::sysid_mygcs_seen : void (uint32_t)`, `sitl.h:1205-1207`. -/
def GCS.sysid_mygcs_seen (this : UInt64) (seen_time_ms : UInt32) : PMem.M Unit := do
  let mut seen_time_ms := seen_time_ms
  PMem.stU32 (this + 432) seen_time_ms
  return ()

/-- C++ `GCS_MAVLINK::sysid_mygcs_seen : void (uint32_t)`, `GCS_Common.cpp:7671-7675`. -/
def GCS_MAVLINK.sysid_mygcs_seen (this : UInt64) (seen_time_ms : UInt32) : PMem.M Unit := do
  let mut seen_time_ms := seen_time_ms
  let t'1 ← gcs
  GCS.sysid_mygcs_seen t'1 seen_time_ms
  PMem.stU32 (this + 472) seen_time_ms
  return ()

/-- C++ `GCS_MAVLINK::handle_heartbeat : void (const mavlink_message_t &)`, `GCS_Common.cpp:4271-4278`. -/
def GCS_MAVLINK.handle_heartbeat (this : UInt64) (msg : UInt64) : PMem.M Unit := do
  let t'1 ← PMem.ldU32 (msg + 8)
  let t'2 ← gcs
  let t'3 ← GCS.sysid_is_gcs t'2 t'1
  if t'3 then
    GCS_MAVLINK.sysid_mygcs_seen this (((← PMem.clock) / 1000).toUInt32)
  return ()

/-- C++ `GCS_MAVLINK::is_unicast : bool () const`, `AP_Mission.h:456-?`. -/
def GCS_MAVLINK.is_unicast (this : UInt64) : PMem.M Bool := do
  let t'1 ← GCS_MAVLINK.option_enabled this (16 : UInt16)
  return t'1

/-- C++ `GCS_MAVLINK::is_streaming : bool () const`, `mavlink_msg_mission_ack.h:307-309`. -/
def GCS_MAVLINK.is_streaming (this : UInt64) : PMem.M Bool := do
  let t'1 ← PMem.ldU8 (this + 728)
  return ((UInt32.toInt32 (UInt8.toUInt32 (t'1))) != (UInt32.toInt32 (UInt8.toUInt32 ((255 : UInt8)))))

/-- C++ `GCS_MAVLINK::send_message : void (enum ap_message)`, `GCS_Common.cpp:1831-1853`. -/
def GCS_MAVLINK.send_message (this : UInt64) (id : UInt8) : PMem.M Unit := do
  let mut id := id
  let sw'1 := UInt32.toInt32 (UInt8.toUInt32 (id))
  if sw'1 == (0 : Int32) then
    let t'2 ← GCS_MAVLINK.is_streaming this
    if t'2 then
      let t'3 := (0xbf88 : UInt64) /- &GCS_MAVLINK::chan_is_streaming -/
      let t'4 ← PMem.ldU32 t'3
      let t'5 ← PMem.ldU32 (this + 40)
      let t'6 := (t'4 ||| ((1 : UInt32) <<< (Int32.toUInt32 (((UInt32.toInt32 (t'5)) - (UInt32.toInt32 ((0 : UInt32))))))))
      PMem.stU32 t'3 t'6
    else
      let t'7 := (0xbf88 : UInt64) /- &GCS_MAVLINK::chan_is_streaming -/
      let t'8 ← PMem.ldU32 t'7
      let t'9 ← PMem.ldU32 (this + 40)
      let t'10 := (t'8 &&& (~~~((1 : UInt32) <<< (Int32.toUInt32 (((UInt32.toInt32 (t'9)) - (UInt32.toInt32 ((0 : UInt32)))))))))
      PMem.stU32 t'7 t'10
  else
    pure ()
  Bitmask'102.set (this + 748) (UInt8.toUInt16 (id))
  return ()

/-- C++ `GCS::send_message : void (enum ap_message)`, `GCS_Common.cpp:2730-2741`. -/
def GCS.send_message (this : UInt64) (id : UInt8) : PMem.M Unit := do
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
    let t'4 ← GCS.num_gcs this
    if !((decide ((UInt32.toInt32 (UInt8.toUInt32 (i))) < (UInt32.toInt32 (UInt8.toUInt32 (t'4)))))) then break
    let t'5 ← GCS_Copter.chan this i
    let link : UInt64 := t'5
    let t'6 ← GCS_MAVLINK.is_unicast link
    if (t'6 && ((UInt32.toInt32 (UInt8.toUInt32 (id))) != (UInt32.toInt32 (UInt8.toUInt32 ((0 : UInt8)))))) then
      continue
    GCS_MAVLINK.send_message link id
  return ()

/-- C++ `GCS::get_allow_param_set : bool () const`, `AP_Common.h:1264-1266`. -/
def GCS.get_allow_param_set (this : UInt64) : PMem.M Bool := do
  let t'1 ← PMem.ldB (this + 436)
  return t'1

/-- `GCS_MAVLINK.pending_param_request.pending_param_request` as a pure function of its arguments (it reads and writes no memory). -/
def GCS_MAVLINK.pending_param_request.pending_param_request.pure' (this : UInt64) : Id Unit := do
  return ()

/-- C++ `GCS_MAVLINK::pending_param_request::pending_param_request : void () noexcept`, `functor.h:994-?`. -/
def GCS_MAVLINK.pending_param_request.pending_param_request (this : UInt64) : PMem.M Unit :=
  pure (_root_.Vehicle_lib.GCS_MAVLINK.pending_param_request.pending_param_request.pure' this)

/-- C++ `GCS_MAVLINK::timesync_receive_timestamp_ns : uint64_t () const`, `GCS_Common.cpp:3661-3668`. -/
def GCS_MAVLINK.timesync_receive_timestamp_ns (this : UInt64) : PMem.M UInt64 := do
  let mut ret : UInt64 := (← PMem.clock)
  if (ret == (Int64.toUInt64 (Int32.toInt64 ((0 : Int32))))) then
    let t'1 := (← PMem.clock)
    ret := t'1
  return (ret * (Int64.toUInt64 ((1000 : Int64))))

/-- C++ `GCS::get_prot_for_mission_type : MissionItemProtocol *(const MAV_MISSION_TYPE) const`, `GCS_Common.cpp:640-646`. -/
def GCS.get_prot_for_mission_type (this : UInt64) (mission_type : UInt32) : PMem.M UInt64 := do
  let mut mission_type := mission_type
  if (decide ((UInt32.toUInt64 (mission_type)) ≥ ((24 : UInt64) / (8 : UInt64)))) then
    return (0 : UInt64)
  let t'1 ← PMem.ldU64 ((0xbc58 : UInt64) /- &GCS::missionitemprotocols -/ + ((UInt64.toInt64 (UInt32.toUInt64 (mission_type))) * 8).toUInt64)
  return t'1

/-- `MissionItemProtocol_Waypoints.mission_type` as a pure function of its arguments (it reads and writes no memory). -/
def MissionItemProtocol_Waypoints.mission_type.pure' (this : UInt64) : Id UInt32 := do
  return (0 : UInt32)

/-- C++ `MissionItemProtocol_Waypoints::mission_type : MAV_MISSION_TYPE () const`, `MissionItemProtocol_Waypoints.h:12-14`. -/
def MissionItemProtocol_Waypoints.mission_type (this : UInt64) : PMem.M UInt32 :=
  pure (_root_.Vehicle_lib.MissionItemProtocol_Waypoints.mission_type.pure' this)

/-- C++ `GCS_MAVLINK::sending_mavlink1 : bool () const`, `GCS_Common.cpp:2164-2167`. -/
def GCS_MAVLINK.sending_mavlink1 (this : UInt64) : PMem.M Bool := do
  let t'1 ← PMem.ldU8 ((this + 408) + 16)
  return (((UInt32.toInt32 (UInt8.toUInt32 (t'1))) &&& (2 : Int32)) != (0 : Int32))

/-- C++ `MissionItemProtocol_Waypoints::item_count : uint16_t () const`, `MissionItemProtocol_Waypoints.cpp:94-96`. -/
def MissionItemProtocol_Waypoints.item_count (this : UInt64) : PMem.M UInt16 := do
  let t'1 ← PMem.ldU64 (this + 48)
  let t'2 ← AP_Mission.num_commands t'1
  return t'2

/-- `MissionItemProtocol.allocate_update_resources` as a pure function of its arguments (it reads and writes no memory). -/
def MissionItemProtocol.allocate_update_resources.pure' (this : UInt64) : Id UInt32 := do
  return (0 : UInt32)

/-- C++ `MissionItemProtocol::allocate_update_resources : MAV_MISSION_RESULT ()`, `AP_Common.h:115-117`. -/
def MissionItemProtocol.allocate_update_resources (this : UInt64) : PMem.M UInt32 :=
  pure (_root_.Vehicle_lib.MissionItemProtocol.allocate_update_resources.pure' this)

/-- `MissionItemProtocol_Waypoints.next_item_ap_message_id` as a pure function of its arguments (it reads and writes no memory). -/
def MissionItemProtocol_Waypoints.next_item_ap_message_id.pure' (this : UInt64) : Id UInt8 := do
  return (28 : UInt8)

/-- C++ `MissionItemProtocol_Waypoints::next_item_ap_message_id : ap_message () const`, `MissionItemProtocol_Waypoints.h:37-39`. -/
def MissionItemProtocol_Waypoints.next_item_ap_message_id (this : UInt64) : PMem.M UInt8 :=
  pure (_root_.Vehicle_lib.MissionItemProtocol_Waypoints.next_item_ap_message_id.pure' this)

/-- C++ `MissionItemProtocol::init_send_requests : void (GCS_MAVLINK &, const mavlink_message_t &, const int16_t, const int16_t)`, `MissionItemProtocol.cpp:9-30`. -/
def MissionItemProtocol.init_send_requests (this : UInt64) (_link : UInt64) (msg : UInt64) (_request_first : Int16) (_request_last : Int16) : PMem.M Unit := do
  let mut _request_first := _request_first
  let mut _request_last := _request_last
  let t'1 := ((← PMem.clock) / 1000).toUInt32
  PMem.stU32 (this + 36) t'1
  PMem.stB (this + 8) true
  let t'2 := Int16.toUInt16 (_request_first)
  PMem.stU16 (this + 26) t'2
  let t'3 := Int16.toUInt16 (_request_last)
  PMem.stU16 (this + 24) t'3
  let t'4 ← PMem.ldU32 (msg + 8)
  PMem.stU32 (this + 28) t'4
  let t'5 ← PMem.ldU8 (msg + 12)
  PMem.stU8 (this + 32) t'5
  PMem.stU64 (this + 16) _link
  let t'6 := ((← PMem.clock) / 1000).toUInt32
  PMem.stU32 (this + 40) t'6
  let t'7 ← MissionItemProtocol_Waypoints.next_item_ap_message_id this
  let t'8 ← PMem.ldU64 (this + 16)
  GCS_MAVLINK.send_message t'8 t'7
  PMem.stB (this + 47) false
  PMem.stB (this + 46) false
  return ()

/-- `GCS_MAVLINK.handle_change_alt_request` as a pure function of its arguments (it reads and writes no memory). -/
def GCS_MAVLINK.handle_change_alt_request.pure' (this : UInt64) (location : UInt64) : Id Unit := do
  return ()

/-- C++ `GCS_MAVLINK::handle_change_alt_request : void (Location &)`, `functor.h:1032-?`. -/
def GCS_MAVLINK.handle_change_alt_request (this : UInt64) (location : UInt64) : PMem.M Unit :=
  pure (_root_.Vehicle_lib.GCS_MAVLINK.handle_change_alt_request.pure' this location)

/-- `MissionItemProtocol.free_upload_resources` as a pure function of its arguments (it reads and writes no memory). -/
def MissionItemProtocol.free_upload_resources.pure' (this : UInt64) : Id Unit := do
  return ()

/-- C++ `MissionItemProtocol::free_upload_resources : void ()`, `AP_Common.h:118-?`. -/
def MissionItemProtocol.free_upload_resources (this : UInt64) : PMem.M Unit :=
  pure (_root_.Vehicle_lib.MissionItemProtocol.free_upload_resources.pure' this)

/-- C++ `GCS_MAVLINK::mission_state : MISSION_STATE (const AP_Mission &) const`, `GCS_Common.cpp:701-718`. -/
def GCS_MAVLINK.mission_state (this : UInt64) (mission : UInt64) : PMem.M UInt32 := do
  let t'1 ← AP_Mission.present mission
  if !t'1 then
    return (1 : UInt32)
  let t'2 ← AP_Mission.state mission
  let sw'3 := UInt32.toInt32 (t'2)
  if sw'3 == (0 : Int32) then
    return (2 : UInt32)
  else if sw'3 == (1 : Int32) then
    return (3 : UInt32)
  else if sw'3 == (2 : Int32) then
    return (5 : UInt32)
  else
    pure ()
  return (0 : UInt32)

/-- C++ `MissionItemProtocol_Waypoints::max_items : uint16_t () const`, `MissionItemProtocol_Waypoints.cpp:98-100`. -/
def MissionItemProtocol_Waypoints.max_items (this : UInt64) : PMem.M UInt16 := do
  let t'1 ← PMem.ldU64 (this + 48)
  let t'2 ← AP_Mission.num_commands_max t'1
  return t'2

/-- `MissionItemProtocol.allocate_receive_resources` as a pure function of its arguments (it reads and writes no memory). -/
def MissionItemProtocol.allocate_receive_resources.pure' (this : UInt64) (count : UInt16) : Id UInt32 := do
  let mut count := count
  return (0 : UInt32)

/-- C++ `MissionItemProtocol::allocate_receive_resources : MAV_MISSION_RESULT (const uint16_t)`, `MissionItemProtocol.h:112-114`. -/
def MissionItemProtocol.allocate_receive_resources (this : UInt64) (count : UInt16) : PMem.M UInt32 :=
  pure (_root_.Vehicle_lib.MissionItemProtocol.allocate_receive_resources.pure' this count)

/-- `GCS_MAVLINK.command_long_stores_location` as a pure function of its arguments (it reads and writes no memory). -/
def GCS_MAVLINK.command_long_stores_location.pure' (command : UInt32) : Id Bool := do
  let mut command := command
  let sw'1 := UInt32.toInt32 (command)
  if sw'1 == (179 : Int32) || sw'1 == (201 : Int32) || sw'1 == (195 : Int32) || sw'1 == (192 : Int32) || sw'1 == (43003 : Int32) || sw'1 == (611 : Int32) then
    return true
  else
    return false
  return false

/-- C++ `GCS_MAVLINK::command_long_stores_location : bool (const MAV_CMD)`, `GCS_Common.cpp:5241-5257`. -/
def GCS_MAVLINK.command_long_stores_location (command : UInt32) : PMem.M Bool :=
  pure (_root_.Vehicle_lib.GCS_MAVLINK.command_long_stores_location.pure' command)

/-- `GCS_MAVLINK.pending_param_reply.pending_param_reply` as a pure function of its arguments (it reads and writes no memory). -/
def GCS_MAVLINK.pending_param_reply.pending_param_reply.pure' (this : UInt64) : Id Unit := do
  return ()

/-- C++ `GCS_MAVLINK::pending_param_reply::pending_param_reply : void () noexcept`, `functor.h:1002-?`. -/
def GCS_MAVLINK.pending_param_reply.pending_param_reply (this : UInt64) : PMem.M Unit :=
  pure (_root_.Vehicle_lib.GCS_MAVLINK.pending_param_reply.pending_param_reply.pure' this)

/-- C++ `GCS_MAVLINK::have_flow_control : bool ()`, `GCS_Param.cpp:105-121`. -/
def GCS_MAVLINK.have_flow_control (this : UInt64) : PMem.M Bool := do
  let t'1 ← PMem.ldU64 (this + 480)
  if (t'1 == (0 : UInt64)) then
    return false
  if false then
    return true
  let t'2 ← PMem.ldU32 (this + 40)
  if ((UInt32.toInt32 (t'2)) == (UInt32.toInt32 ((0 : UInt32)))) then
    return false
  return false

/-- C++ `GCS_MAVLINK::last_txbuf_is_greater : bool (uint8_t)`, `GCS_Common.cpp:895-902`. -/
def GCS_MAVLINK.last_txbuf_is_greater (txbuf_limit : UInt8) : PMem.M Bool := do
  let mut txbuf_limit := txbuf_limit
  let t'1 ← PMem.ldU32 ((0x130d0 : UInt64) /- &GCS_MAVLINK::last_radio_status -/ + 8)
  if (decide (((((← PMem.clock) / 1000).toUInt32) - t'1) > (Int32.toUInt32 ((5000 : Int32))))) then
    return true
  let t'2 ← PMem.ldU8 ((0x130d0 : UInt64) /- &GCS_MAVLINK::last_radio_status -/ + 12)
  return (decide ((UInt32.toInt32 (UInt8.toUInt32 (t'2))) > (UInt32.toInt32 (UInt8.toUInt32 (txbuf_limit)))))

/-- C++ `GCS_MAVLINK::global_position_int_alt : int32_t () const`, `GCS_Common.cpp:6113-6115`. -/
def GCS_MAVLINK.global_position_int_alt (this : UInt64) : PMem.M Int32 := do
  let t'1 ← PMem.ldI32 ((this + 840) + 4)
  return UInt32.toInt32 (UInt64.toUInt32 (((Int64.toUInt64 (Int32.toInt64 (t'1))) * (10 : UInt64))))

/-- C++ `GCS_MAVLINK::global_position_int_relative_alt : int32_t () const`, `GCS_Common.cpp:6116-6125`. -/
def GCS_MAVLINK.global_position_int_relative_alt.body (fp : UInt64) (this : UInt64) : PMem.M Int32 := do
  let t'1 ← VehicleBridge.ahrs'0
  VehicleBridge.AP_AHRS.get_relative_position_D_home'1 t'1 (fp + 0)
  let t'2 ← PMem.ldF32 (fp + 0)
  let t'3 := (t'2 * (-(Binary32.ofBits 0x447a0000 /- 1000 -/)))
  PMem.stF32 (fp + 0) t'3
  let t'4 ← PMem.ldF32 (fp + 0)
  return Binary32.toInt32 (t'4)

def GCS_MAVLINK.global_position_int_relative_alt (this : UInt64) : PMem.M Int32 := do
  let fp ← PMem.enter 4
  let r ← GCS_MAVLINK.global_position_int_relative_alt.body fp this
  PMem.leave fp
  return r

/-- `GCS_MAVLINK.send_distance_sensor` as a pure function of its arguments (it reads and writes no memory). -/
def GCS_MAVLINK.send_distance_sensor.pure' (this : UInt64) : Id Unit := do
  return ()

/-- C++ `GCS_MAVLINK::send_distance_sensor : void ()`, `GCS_Common.cpp:491-536`. -/
def GCS_MAVLINK.send_distance_sensor (this : UInt64) : PMem.M Unit :=
  pure (_root_.Vehicle_lib.GCS_MAVLINK.send_distance_sensor.pure' this)

/-- C++ `GCS_MAVLINK::send_simstate : void () const`, `GCS_Common.cpp:4765-4772`. -/
def GCS_MAVLINK.send_simstate (this : UInt64) : PMem.M Unit := do
  let t'1 ← VehicleBridge.sitl'0
  let mut sitl : UInt64 := t'1
  if (sitl == (0 : UInt64)) then
    return ()
  let t'2 ← GCS_MAVLINK.get_chan this
  SITL.SIM.simstate_send sitl t'2
  return ()

/-- C++ `GCS_MAVLINK::send_sim_state : void () const`, `GCS_Common.cpp:4774-4781`. -/
def GCS_MAVLINK.send_sim_state (this : UInt64) : PMem.M Unit := do
  let t'1 ← VehicleBridge.sitl'0
  let mut sitl : UInt64 := t'1
  if (sitl == (0 : UInt64)) then
    return ()
  let t'2 ← GCS_MAVLINK.get_chan this
  SITL.SIM.sim_state_send sitl t'2
  return ()

/-- `GCS.min_status_for_gps_healthy` as a pure function of its arguments (it reads and writes no memory). -/
def GCS.min_status_for_gps_healthy.pure' (this : UInt64) : Id UInt8 := do
  return (1 : UInt8)

/-- C++ `GCS::min_status_for_gps_healthy : AP_GPS_FixType () const`, `AP_Common.h:1365-1368`. -/
def GCS.min_status_for_gps_healthy (this : UInt64) : PMem.M UInt8 :=
  pure (_root_.Vehicle_lib.GCS.min_status_for_gps_healthy.pure' this)

/-- C++ `GCS_MAVLINK::vfr_hud_alt : float () const`, `GCS_Common.cpp:3495-3498`. -/
def GCS_MAVLINK.vfr_hud_alt (this : UInt64) : PMem.M Binary32 := do
  let t'1 ← PMem.ldI32 ((this + 840) + 4)
  return ((Int32.toBinary32 (t'1)) * (Binary32.ofBits 0x3c23d70a /- 999999977/100000000000 -/))

/-- C++ `GCS_MAVLINK::vfr_hud_climbrate : float () const`, `GCS_Common.cpp:3482-3492`. -/
def GCS_MAVLINK.vfr_hud_climbrate.body (fp : UInt64) (this : UInt64) : PMem.M Binary32 := do
  Vector3'float.Vector3'2 (fp + 0)
  let t'1 ← VehicleBridge.ahrs'0
  let t'2 ← VehicleBridge.AP_AHRS.get_velocity_NED'1 t'1 (fp + 0)
  let mut sc'5 := t'2
  if !sc'5 then
    let t'3 ← VehicleBridge.ahrs'0
    let t'4 ← VehicleBridge.AP_AHRS.get_vert_pos_rate_D'1 t'3 ((fp + 0) + 8)
    sc'5 := t'4
  if sc'5 then
    let t'6 ← PMem.ldF32 ((fp + 0) + 8)
    return -t'6
  return Int32.toBinary32 ((0 : Int32))

def GCS_MAVLINK.vfr_hud_climbrate (this : UInt64) : PMem.M Binary32 := do
  let fp ← PMem.enter 12
  let r ← GCS_MAVLINK.vfr_hud_climbrate.body fp this
  PMem.leave fp
  return r

/-- `GCS_MAVLINK.capabilities` as a pure function of its arguments (it reads and writes no memory). -/
def GCS_MAVLINK.capabilities.pure' (this : UInt64) : Id UInt64 := do
  let mut ret : UInt64 := Int64.toUInt64 (Int32.toInt64 (((UInt32.toInt32 ((2 : UInt32))) ||| (UInt32.toInt32 ((4096 : UInt32))))))
  let mut mavlink_protocol : Int32 := (2 : Int32)
  if ((mavlink_protocol == (2 : Int32)) || (mavlink_protocol == (43 : Int32))) then
    let t'1 := (ret ||| (UInt32.toUInt64 ((8192 : UInt32))))
    ret := t'1
  return ret

/-- C++ `GCS_MAVLINK::capabilities : uint64_t () const`, `GCS_Common.cpp:7587-7624`. -/
def GCS_MAVLINK.capabilities (this : UInt64) : PMem.M UInt64 :=
  pure (_root_.Vehicle_lib.GCS_MAVLINK.capabilities.pure' this)

/-- C++ `GCS_MAVLINK::handle_command_request_autopilot_capabilities : MAV_RESULT (const mavlink_command_int_t &)`, `GCS_Common.cpp:5022-5031`. -/
def GCS_MAVLINK.handle_command_request_autopilot_capabilities (this : UInt64) (packet : UInt64) : PMem.M UInt32 := do
  let t'1 ← PMem.ldF32 packet
  let t'2 ← is_equal'float_float t'1 (Binary32.ofBits 0x3f800000 /- 1 -/)
  if !t'2 then
    return (4 : UInt32)
  GCS_MAVLINK.send_message this (73 : UInt8)
  return (0 : UInt32)

/-- C++ `GCS_MAVLINK::mavlink_id_to_ap_message_id : ap_message (const uint32_t) const`, `GCS_Common.cpp:1035-1218`. -/
def GCS_MAVLINK.mavlink_id_to_ap_message_id (this : UInt64) (mavlink_id : UInt32) : PMem.M UInt8 := do
  let mut mavlink_id := mavlink_id
  let mut i : UInt8 := Int8.toUInt8 (Int32.toInt8 ((0 : Int32)))
  let mut first'1 := true
  for _ in PMem.loopFuel do
    if !first'1 then
      let t'2 := i
      let t'3 := (t'2 + 1)
      i := t'3
      pure ()
    first'1 := false
    if !((decide ((UInt8.toUInt64 (i)) < ((384 : UInt64) / (8 : UInt64))))) then break
    let t'4 ← PMem.ldU32 ((0xebe0 : UInt64) /- &GCS_MAVLINK::mavlink_id_to_ap_message_id(...)::map -/ + ((UInt64.toInt64 (UInt8.toUInt64 (i))) * 8).toUInt64)
    if (t'4 == mavlink_id) then
      let t'5 ← PMem.ldU8 (((0xebe0 : UInt64) /- &GCS_MAVLINK::mavlink_id_to_ap_message_id(...)::map -/ + ((UInt64.toInt64 (UInt8.toUInt64 (i))) * 8).toUInt64) + 4)
      return t'5
  return (102 : UInt8)

/-- C++ `GCS_MAVLINK::get_deferred_message_index : int8_t (const ap_message) const`, `GCS_Common.cpp:1389-1397`. -/
def GCS_MAVLINK.get_deferred_message_index (this : UInt64) (id : UInt8) : PMem.M Int8 := do
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
    if !((decide ((UInt8.toUInt64 (i)) < ((18 : UInt64) / (6 : UInt64))))) then break
    let t'4 ← PMem.ldU8 ((this + 506) + ((UInt64.toInt64 (UInt8.toUInt64 (i))) * 6).toUInt64)
    if ((UInt32.toInt32 (UInt8.toUInt32 (t'4))) == (UInt32.toInt32 (UInt8.toUInt32 (id)))) then
      return UInt8.toInt8 (i)
  return Int32.toInt8 ((-(1 : Int32)))

/-- C++ `MissionItemProtocol::active_link_is : bool (const GCS_MAVLINK *) const`, `MissionItemProtocol.h:58-?`. -/
def MissionItemProtocol.active_link_is (this : UInt64) (_link : UInt64) : PMem.M Bool := do
  let mut _link := _link
  let t'1 ← PMem.ldU64 (this + 16)
  return (_link == t'1)

/-- C++ `GCS_MAVLINK::requesting_mission_items : bool () const`, `GCS_Common.cpp:821-829`. -/
def GCS_MAVLINK.requesting_mission_items (this : UInt64) : PMem.M Bool := do
  let __range1 : UInt64 := (0xbc58 : UInt64) /- &GCS::missionitemprotocols -/
  let mut __begin1 : UInt64 := __range1
  let mut __end1 : UInt64 := (__range1 + ((3 : Int64) * 8).toUInt64)
  let mut first'1 := true
  for _ in PMem.loopFuel do
    if !first'1 then
      let t'2 := (__begin1 + 8)
      __begin1 := t'2
      pure ()
    first'1 := false
    if !((__begin1 != __end1)) then break
    let t'3 ← PMem.ldU64 __begin1
    let mut prot : UInt64 := t'3
    let mut sc'5 := (prot != 0)
    if sc'5 then
      let t'4 ← PMem.ldB (prot + 8)
      sc'5 := t'4
    let mut sc'7 := sc'5
    if sc'7 then
      let t'6 ← MissionItemProtocol.active_link_is prot this
      sc'7 := t'6
    if sc'7 then
      return true
  return false

/-- C++ `GCS_MAVLINK::get_reschedule_interval_ms : uint16_t (const deferred_message_bucket_t &) const`, `GCS_Common.cpp:1253-1281`. -/
def GCS_MAVLINK.get_reschedule_interval_ms (this : UInt64) (deferred : UInt64) : PMem.M UInt16 := do
  let t'1 ← PMem.ldU16 (deferred + 16)
  let mut interval_ms : UInt32 := UInt16.toUInt32 (t'1)
  let t'2 ← PMem.ldU16 (this + 504)
  let t'3 := (interval_ms + (UInt16.toUInt32 (t'2)))
  interval_ms := t'3
  let t'4 ← PMem.ldU64 (this + 32)
  if (t'4 != 0) then
    let t'5 := (interval_ms * (Int32.toUInt32 ((4 : Int32))))
    interval_ms := t'5
  let t'6 ← GCS_MAVLINK.requesting_mission_items this
  if t'6 then
    let t'7 := (interval_ms * (Int32.toUInt32 ((4 : Int32))))
    interval_ms := t'7
  if (decide (interval_ms > (Int32.toUInt32 ((60000 : Int32))))) then
    return Int16.toUInt16 (Int32.toInt16 ((60000 : Int32)))
  return UInt32.toUInt16 (interval_ms)

/-- C++ `GCS_MAVLINK::find_next_bucket_to_send : void (uint16_t)`, `GCS_Common.cpp:1284-1326`. -/
def GCS_MAVLINK.find_next_bucket_to_send (this : UInt64) (now16_ms : UInt16) : PMem.M Unit := do
  let mut now16_ms := now16_ms
  PMem.stU8 (this + 728) (255 : UInt8)
  let mut ms_before_send_next_bucket_to_send : UInt16 := Int16.toUInt16 (Int32.toInt16 ((65535 : Int32)))
  let mut i : UInt8 := Int8.toUInt8 (Int32.toInt8 ((0 : Int32)))
  let mut first'1 := true
  for _ in PMem.loopFuel do
    if !first'1 then
      let t'2 := i
      let t'3 := (t'2 + 1)
      i := t'3
      pure ()
    first'1 := false
    if !((decide ((UInt8.toUInt64 (i)) < ((200 : UInt64) / (20 : UInt64))))) then break
    let t'4 ← Bitmask'102.count ((this + 528) + ((UInt64.toInt64 (UInt8.toUInt64 (i))) * 20).toUInt64)
    if ((UInt32.toInt32 (UInt16.toUInt32 (t'4))) == (0 : Int32)) then
      continue
    let t'5 ← GCS_MAVLINK.get_reschedule_interval_ms this ((this + 528) + ((UInt64.toInt64 (UInt8.toUInt64 (i))) * 20).toUInt64)
    let mut interval : UInt16 := t'5
    let t'6 ← PMem.ldU16 (((this + 528) + ((UInt64.toInt64 (UInt8.toUInt64 (i))) * 20).toUInt64) + 18)
    let mut ms_since_last_sent : UInt16 := Int16.toUInt16 (Int32.toInt16 (((UInt32.toInt32 (UInt16.toUInt32 (now16_ms))) - (UInt32.toInt32 (UInt16.toUInt32 (t'6))))))
    let mut ms_before_send_this_bucket : UInt16 := default  -- uninitialized in C
    if (decide ((UInt32.toInt32 (UInt16.toUInt32 (ms_since_last_sent))) > (UInt32.toInt32 (UInt16.toUInt32 (interval))))) then
      let t'7 := Int16.toUInt16 (Int32.toInt16 ((0 : Int32)))
      ms_before_send_this_bucket := t'7
    else
      let t'8 := Int16.toUInt16 (Int32.toInt16 (((UInt32.toInt32 (UInt16.toUInt32 (interval))) - (UInt32.toInt32 (UInt16.toUInt32 (ms_since_last_sent))))))
      ms_before_send_this_bucket := t'8
    if (decide ((UInt32.toInt32 (UInt16.toUInt32 (ms_before_send_this_bucket))) < (UInt32.toInt32 (UInt16.toUInt32 (ms_before_send_next_bucket_to_send))))) then
      PMem.stU8 (this + 728) i
      ms_before_send_next_bucket_to_send := ms_before_send_this_bucket
  let t'9 ← PMem.ldU8 (this + 728)
  if ((UInt32.toInt32 (UInt8.toUInt32 (t'9))) != (UInt32.toInt32 (UInt8.toUInt32 ((255 : UInt8))))) then
    let t'10 ← PMem.ldU8 (this + 728)
    discard <| PMem.memcpy (this + 732) ((this + 528) + ((UInt64.toInt64 (UInt8.toUInt64 (t'10))) * 20).toUInt64) 16
    discard <| pure ((this + 732))
  else
    Bitmask'102.clearall (this + 732)
  return ()

/-- C++ `GCS_MAVLINK::remove_message_from_bucket : void (int8_t, ap_message)`, `GCS_Common.cpp:1697-1723`. -/
def GCS_MAVLINK.remove_message_from_bucket (this : UInt64) (bucket : Int8) (id : UInt8) : PMem.M Unit := do
  let mut bucket := bucket
  let mut id := id
  Bitmask'102.clear ((this + 528) + ((Int8.toInt64 (bucket)) * 20).toUInt64) (UInt8.toUInt16 (id))
  let t'1 ← Bitmask'102.count ((this + 528) + ((Int8.toInt64 (bucket)) * 20).toUInt64)
  if ((UInt32.toInt32 (UInt16.toUInt32 (t'1))) == (0 : Int32)) then
    let t'2 := Int16.toUInt16 (Int32.toInt16 ((0 : Int32)))
    PMem.stU16 (((this + 528) + ((Int8.toInt64 (bucket)) * 20).toUInt64) + 16) t'2
    let t'3 := Int16.toUInt16 (Int32.toInt16 ((0 : Int32)))
    PMem.stU16 (((this + 528) + ((Int8.toInt64 (bucket)) * 20).toUInt64) + 18) t'3
  let t'4 ← PMem.ldU8 (this + 728)
  if ((Int8.toInt32 (bucket)) == (UInt32.toInt32 (UInt8.toUInt32 (t'4)))) then
    Bitmask'102.clear (this + 732) (UInt8.toUInt16 (id))
    let t'5 ← Bitmask'102.count (this + 732)
    if ((UInt32.toInt32 (UInt16.toUInt32 (t'5))) == (0 : Int32)) then
      GCS_MAVLINK.find_next_bucket_to_send this (((← PMem.clock) / 1000).toUInt16)
    else
      let t'6 ← PMem.ldU16 (((this + 528) + ((Int8.toInt64 (bucket)) * 20).toUInt64) + 16)
      let mut sc'8 := ((UInt32.toInt32 (UInt16.toUInt32 (t'6))) == (0 : Int32))
      if sc'8 then
        let t'7 ← PMem.ldU16 (((this + 528) + ((Int8.toInt64 (bucket)) * 20).toUInt64) + 18)
        sc'8 := ((UInt32.toInt32 (UInt16.toUInt32 (t'7))) == (0 : Int32))
      if sc'8 then
        pure ()
  return ()

/-- C++ `GCS_MAVLINK_InProgress::abort : void ()`, `GCS.h:147-?`. -/
def GCS_MAVLINK_InProgress.abort (this : UInt64) : PMem.M Unit := do
  PMem.stI32 this (0 : Int32)
  return ()

/-- C++ `GCS_MAVLINK::get_interval_for_stream : uint16_t (GCS_MAVLINK::streams) const`, `GCS_Common.cpp:7083-7094`. -/
def GCS_MAVLINK.get_interval_for_stream (this : UInt64) (id : UInt8) : PMem.M UInt16 := do
  let mut id := id
  let t'1 ← AP_ParamTBase'short_2.get ((this + 44) + ((UInt64.toInt64 (UInt8.toUInt64 (id))) * 2).toUInt64)
  let t'2 ← PMem.ldI16 t'1
  let mut frate : Int16 := t'2
  if ((Int16.toInt32 (frate)) == (0 : Int32)) then
    return Int16.toUInt16 (Int32.toInt16 ((0 : Int32)))
  let mut ret : UInt32 := Int32.toUInt32 (((1000 : Int32) / (Int16.toInt32 (frate))))
  if (decide (ret > (Int32.toUInt32 ((60000 : Int32))))) then
    return Int16.toUInt16 (Int32.toInt16 ((60000 : Int32)))
  return UInt32.toUInt16 (ret)

/-- C++ `DefaultIntervalsFromFiles::get_interval_for_ap_message_id : bool (ap_message, uint16_t &) const`, `GCS_Common.cpp:7153-7162`. -/
def DefaultIntervalsFromFiles.get_interval_for_ap_message_id (this : UInt64) (id : UInt8) (interval : UInt64) : PMem.M Bool := do
  let mut id := id
  let mut i : UInt16 := Int16.toUInt16 (Int32.toInt16 ((0 : Int32)))
  let mut first'1 := true
  for _ in PMem.loopFuel do
    if !first'1 then
      let t'2 := i
      let t'3 := (t'2 + 1)
      i := t'3
      pure ()
    first'1 := false
    let t'4 ← PMem.ldU16 (this + 8)
    if !((decide ((UInt32.toInt32 (UInt16.toUInt32 (i))) < (UInt32.toInt32 (UInt16.toUInt32 (t'4)))))) then break
    let t'5 ← PMem.ldU64 this
    let t'6 ← PMem.ldU8 (t'5 + ((UInt64.toInt64 (UInt16.toUInt64 (i))) * 4).toUInt64)
    if ((UInt32.toInt32 (UInt8.toUInt32 (t'6))) == (UInt32.toInt32 (UInt8.toUInt32 (id)))) then
      let t'7 ← PMem.ldU64 this
      let t'8 ← PMem.ldU16 ((t'7 + ((UInt64.toInt64 (UInt16.toUInt64 (i))) * 4).toUInt64) + 2)
      PMem.stU16 interval t'8
      return true
  return false

/-- C++ `GCS_MAVLINK::get_default_interval_for_ap_message : bool (const ap_message, uint16_t &) const`, `GCS_Common.cpp:7315-7358`. -/
def GCS_MAVLINK.get_default_interval_for_ap_message (this : UInt64) (id : UInt8) (interval : UInt64) : PMem.M Bool := do
  let mut id := id
  if ((UInt32.toInt32 (UInt8.toUInt32 (id))) == (UInt32.toInt32 (UInt8.toUInt32 ((0 : UInt8))))) then
    let t'1 := Int16.toUInt16 (Int32.toInt16 ((1000 : Int32)))
    PMem.stU16 interval t'1
    return true
  let t'2 ← PMem.ldU64 (this + 768)
  let mut sc'5 := (t'2 != (0 : UInt64))
  if sc'5 then
    let t'3 ← PMem.ldU64 (this + 768)
    let t'4 ← DefaultIntervalsFromFiles.get_interval_for_ap_message_id t'3 id interval
    sc'5 := t'4
  if sc'5 then
    return true
  let t'6 ← GCS_MAVLINK.option_enabled this (16 : UInt16)
  if t'6 then
    let t'7 := Int16.toUInt16 (Int32.toInt16 ((0 : Int32)))
    PMem.stU16 interval t'7
    return true
  let mut i : UInt8 := Int8.toUInt8 (Int32.toInt8 ((0 : Int32)))
  let mut first'8 := true
  for _ in PMem.loopFuel do
    if !first'8 then
      let t'9 := i
      let t'10 := (t'9 + 1)
      i := t'10
      pure ()
    first'8 := false
    let t'11 ← PMem.ldU64 (((0xc890 : UInt64) /- &GCS_MAVLINK::all_stream_entries -/ + ((UInt64.toInt64 (UInt8.toUInt64 (i))) * 24).toUInt64) + 8)
    if !((t'11 != (0 : UInt64))) then break
    let entries : UInt64 := ((0xc890 : UInt64) /- &GCS_MAVLINK::all_stream_entries -/ + ((UInt64.toInt64 (UInt8.toUInt64 (i))) * 24).toUInt64)
    let mut j : UInt8 := Int8.toUInt8 (Int32.toInt8 ((0 : Int32)))
    let mut first'12 := true
    for _ in PMem.loopFuel do
      if !first'12 then
        let t'13 := j
        let t'14 := (t'13 + 1)
        j := t'14
        pure ()
      first'12 := false
      let t'15 ← PMem.ldU8 (entries + 16)
      if !((decide ((UInt32.toInt32 (UInt8.toUInt32 (j))) < (UInt32.toInt32 (UInt8.toUInt32 (t'15)))))) then break
      let t'16 ← PMem.ldU64 (entries + 8)
      let t'17 ← PMem.ldU8 (t'16 + ((UInt64.toInt64 (UInt8.toUInt64 (j))) * 1).toUInt64)
      if ((UInt32.toInt32 (UInt8.toUInt32 (t'17))) == (UInt32.toInt32 (UInt8.toUInt32 (id)))) then
        let t'18 ← PMem.ldU8 ((0xc890 : UInt64) /- &GCS_MAVLINK::all_stream_entries -/ + ((UInt64.toInt64 (UInt8.toUInt64 (i))) * 24).toUInt64)
        let t'19 ← GCS_MAVLINK.get_interval_for_stream this t'18
        PMem.stU16 interval t'19
        return true
  return false

/-- C++ `GCS_MAVLINK::handle_command_request_message : MAV_RESULT (const mavlink_command_int_t &)`, `GCS_Common.cpp:3288-3328`. -/
def GCS_MAVLINK.handle_command_request_message.body (fp : UInt64) (this : UInt64) (packet : UInt64) : PMem.M UInt32 := do
  let t'1 ← PMem.ldF32 packet
  let mut mavlink_id : UInt32 := Binary32.toUInt32 (t'1)
  if (mavlink_id == (Int32.toUInt32 ((244 : Int32)))) then
    let t'2 ← PMem.ldF32 (packet + 4)
    PMem.stF32 ((fp + 0) + 0) t'2
    discard <| PMem.memset ((fp + 0) + 4) 0 4
    discard <| PMem.memset ((fp + 0) + 8) 0 4
    discard <| PMem.memset ((fp + 0) + 12) 0 4
    discard <| PMem.memset ((fp + 0) + 16) 0 4
    discard <| PMem.memset ((fp + 0) + 20) 0 4
    discard <| PMem.memset ((fp + 0) + 24) 0 4
    discard <| PMem.memset ((fp + 0) + 28) 0 2
    discard <| PMem.memset ((fp + 0) + 30) 0 1
    discard <| PMem.memset ((fp + 0) + 31) 0 1
    discard <| PMem.memset ((fp + 0) + 32) 0 1
    discard <| PMem.memset ((fp + 0) + 33) 0 1
    discard <| PMem.memset ((fp + 0) + 34) 0 1
    PMem.unreached "GCS_MAVLINK::handle_command_get_message_interval"
    return (default : UInt32)
  let t'3 ← GCS_MAVLINK.mavlink_id_to_ap_message_id this mavlink_id
  let mut id : UInt8 := t'3
  if ((UInt32.toInt32 (UInt8.toUInt32 (id))) == (UInt32.toInt32 (UInt8.toUInt32 ((102 : UInt8))))) then
    return (4 : UInt32)
  let sw'4 := UInt32.toInt32 (UInt8.toUInt32 (id))
  if sw'4 == (98 : Int32) then
    PMem.stB (this + 871) true
    PMem.stB ((this + 871) + 1) true
    let t'5 := Int8.toUInt8 (Int32.toInt8 ((1 : Int32)))
    PMem.stU8 ((this + 871) + 3) t'5
    let t'6 ← PMem.ldF32 (packet + 4)
    let t'7 := Binary32.toUInt8 (t'6)
    PMem.stU8 ((this + 871) + 2) t'7
  else
    pure ()
  GCS_MAVLINK.send_message this id
  return (0 : UInt32)

def GCS_MAVLINK.handle_command_request_message (this : UInt64) (packet : UInt64) : PMem.M UInt32 := do
  let fp ← PMem.enter 35
  let r ← GCS_MAVLINK.handle_command_request_message.body fp this packet
  PMem.leave fp
  return r

/-- C++ `GCS_MAVLINK::mav_frame_for_command_long : bool (MAV_FRAME &, MAV_CMD) const`, `GCS_Common.cpp:5277-5299`. -/
def GCS_MAVLINK.mav_frame_for_command_long (this : UInt64) (frame : UInt64) (packet_command : UInt32) : PMem.M Bool := do
  let mut packet_command := packet_command
  let __range1 : UInt64 := (0x13190 : UInt64) /- &GCS_MAVLINK::mav_frame_for_command_long(...)::frame_map -/
  let mut __begin1 : UInt64 := __range1
  let mut __end1 : UInt64 := (__range1 + ((4 : Int64) * 8).toUInt64)
  let mut first'1 := true
  for _ in PMem.loopFuel do
    if !first'1 then
      let t'2 := (__begin1 + 8)
      __begin1 := t'2
      pure ()
    first'1 := false
    if !((__begin1 != __end1)) then break
    let map : UInt64 := __begin1
    let t'3 ← PMem.ldU32 map
    if (t'3 != packet_command) then
      continue
    let t'4 ← PMem.ldU32 (map + 4)
    PMem.stU32 frame t'4
    return true
  return false

/-- `convert_COMMAND_LONG_loc_param` as a pure function of its arguments (it reads and writes no memory). -/
def convert_COMMAND_LONG_loc_param.pure' (param : Binary32) (stores_location : Bool) : Id Int32 := do
  let mut param := param
  let mut stores_location := stores_location
  if (Binary32.isNaN param) then
    return (0 : Int32)
  if stores_location then
    return Binary32.toInt32 ((param * (Binary64.toBinary32 ((Binary64.ofBits 0x416312d000000000 /- 10000000 -/)))))
  return Binary32.toInt32 (param)

/-- C++ `convert_COMMAND_LONG_loc_param : int32_t (float, bool)`, `GCS_Common.cpp:5335-5346`. -/
def convert_COMMAND_LONG_loc_param (param : Binary32) (stores_location : Bool) : PMem.M Int32 :=
  pure (_root_.Vehicle_lib.convert_COMMAND_LONG_loc_param.pure' param stores_location)

/-- C++ `GCS_MAVLINK::convert_COMMAND_LONG_to_COMMAND_INT : void (const mavlink_command_long_t &, mavlink_command_int_t &, MAV_FRAME)`, `GCS_Common.cpp:5348-5365`. -/
def GCS_MAVLINK.convert_COMMAND_LONG_to_COMMAND_INT.body (fp : UInt64) (this : UInt64) (in' : UInt64) (out : UInt64) (frame : UInt32) : PMem.M Unit := do
  let mut frame := frame
  discard <| PMem.memset ((fp + 0) + 0) 0 4
  discard <| PMem.memset ((fp + 0) + 4) 0 4
  discard <| PMem.memset ((fp + 0) + 8) 0 4
  discard <| PMem.memset ((fp + 0) + 12) 0 4
  discard <| PMem.memset ((fp + 0) + 16) 0 4
  discard <| PMem.memset ((fp + 0) + 20) 0 4
  discard <| PMem.memset ((fp + 0) + 24) 0 4
  discard <| PMem.memset ((fp + 0) + 28) 0 2
  discard <| PMem.memset ((fp + 0) + 30) 0 1
  discard <| PMem.memset ((fp + 0) + 31) 0 1
  discard <| PMem.memset ((fp + 0) + 32) 0 1
  discard <| PMem.memset ((fp + 0) + 33) 0 1
  discard <| PMem.memset ((fp + 0) + 34) 0 1
  discard <| PMem.memcpy out (fp + 0) 35
  discard <| pure (out)
  let t'1 ← PMem.ldU8 (in' + 30)
  PMem.stU8 (out + 30) t'1
  let t'2 ← PMem.ldU8 (in' + 31)
  PMem.stU8 (out + 31) t'2
  let t'3 := UInt32.toUInt8 (frame)
  PMem.stU8 (out + 32) t'3
  let t'4 ← PMem.ldU16 (in' + 28)
  PMem.stU16 (out + 28) t'4
  let t'5 := Int8.toUInt8 (Int32.toInt8 ((0 : Int32)))
  PMem.stU8 (out + 33) t'5
  let t'6 := Int8.toUInt8 (Int32.toInt8 ((0 : Int32)))
  PMem.stU8 (out + 34) t'6
  let t'7 ← PMem.ldF32 in'
  PMem.stF32 out t'7
  let t'8 ← PMem.ldF32 (in' + 4)
  PMem.stF32 (out + 4) t'8
  let t'9 ← PMem.ldF32 (in' + 8)
  PMem.stF32 (out + 8) t'9
  let t'10 ← PMem.ldF32 (in' + 12)
  PMem.stF32 (out + 12) t'10
  let t'11 ← PMem.ldU16 (in' + 28)
  let t'12 ← GCS_MAVLINK.command_long_stores_location (UInt16.toUInt32 (t'11))
  let mut stores_location : Bool := t'12
  let t'13 ← PMem.ldF32 (in' + 16)
  let t'14 ← convert_COMMAND_LONG_loc_param t'13 stores_location
  PMem.stI32 (out + 16) t'14
  let t'15 ← PMem.ldF32 (in' + 20)
  let t'16 ← convert_COMMAND_LONG_loc_param t'15 stores_location
  PMem.stI32 (out + 20) t'16
  let t'17 ← PMem.ldF32 (in' + 24)
  PMem.stF32 (out + 24) t'17
  return ()

def GCS_MAVLINK.convert_COMMAND_LONG_to_COMMAND_INT (this : UInt64) (in' : UInt64) (out : UInt64) (frame : UInt32) : PMem.M Unit := do
  let fp ← PMem.enter 35
  let r ← GCS_MAVLINK.convert_COMMAND_LONG_to_COMMAND_INT.body fp this in' out frame
  PMem.leave fp
  return r

/-- `camera_command_result_param2'mavlink_command_long_t` as a pure function of its arguments (it reads and writes no memory). -/
def camera_command_result_param2'mavlink_command_long_t.pure' (packet : UInt64) (result : UInt32) : Id UInt8 := do
  let mut result := result
  return Int8.toUInt8 (Int32.toInt8 ((0 : Int32)))

/-- C++ `camera_command_result_param2 : uint8_t (const __mavlink_command_long_t &, MAV_RESULT)`, `GCS_Common.cpp:5262-5271`. -/
def camera_command_result_param2'mavlink_command_long_t (packet : UInt64) (result : UInt32) : PMem.M UInt8 :=
  pure (_root_.Vehicle_lib.camera_command_result_param2'mavlink_command_long_t.pure' packet result)

/-- `camera_command_result_param2'mavlink_command_int_t` as a pure function of its arguments (it reads and writes no memory). -/
def camera_command_result_param2'mavlink_command_int_t.pure' (packet : UInt64) (result : UInt32) : Id UInt8 := do
  let mut result := result
  return Int8.toUInt8 (Int32.toInt8 ((0 : Int32)))

/-- C++ `camera_command_result_param2 : uint8_t (const __mavlink_command_int_t &, MAV_RESULT)`, `GCS_Common.cpp:5262-5271`. -/
def camera_command_result_param2'mavlink_command_int_t (packet : UInt64) (result : UInt32) : PMem.M UInt8 :=
  pure (_root_.Vehicle_lib.camera_command_result_param2'mavlink_command_int_t.pure' packet result)

/-- `GCS_MAVLINK.persist_streamrates` as a pure function of its arguments (it reads and writes no memory). -/
def GCS_MAVLINK.persist_streamrates.pure' (this : UInt64) : Id Bool := do
  return false

/-- C++ `GCS_MAVLINK::persist_streamrates : bool () const`, `functor.h:544-?`. -/
def GCS_MAVLINK.persist_streamrates (this : UInt64) : PMem.M Bool :=
  pure (_root_.Vehicle_lib.GCS_MAVLINK.persist_streamrates.pure' this)

/-- C++ `MissionItemProtocol_Waypoints::MissionItemProtocol_Waypoints : void (class AP_Mission &)`, `MissionItemProtocol_Waypoints.h:?-8`. -/
def MissionItemProtocol_Waypoints.MissionItemProtocol_Waypoints (this : UInt64) (_mission : UInt64) : PMem.M Unit := do
  PMem.stU16 (this + 44) (Int16.toUInt16 (Int32.toInt16 ((8000 : Int32))))
  PMem.stB (this + 46) false
  PMem.stB (this + 47) false
  PMem.stU64 (this + 48) _mission
  return ()

/-- C++ `GCS_MAVLINK::get_stream_slowdown_ms : uint16_t () const`, `functor.h:509-?`. -/
def GCS_MAVLINK.get_stream_slowdown_ms (this : UInt64) : PMem.M UInt16 := do
  let t'1 ← PMem.ldU16 (this + 504)
  return t'1

/-- C++ `GCS_MAVLINK::deferred_message_to_send_index : int8_t (uint16_t)`, `GCS_Common.cpp:1399-1441`. -/
def GCS_MAVLINK.deferred_message_to_send_index (this : UInt64) (now16_ms : UInt16) : PMem.M Int8 := do
  let mut now16_ms := now16_ms
  let t'1 ← PMem.ldI8 (this + 524)
  if ((Int8.toInt32 (t'1)) == (-(1 : Int32))) then
    let mut ms_before_next_message_to_send : UInt16 := Int16.toUInt16 (Int32.toInt16 ((65535 : Int32)))
    let mut i : UInt8 := Int8.toUInt8 (Int32.toInt8 ((0 : Int32)))
    let mut first'2 := true
    for _ in PMem.loopFuel do
      if !first'2 then
        let t'3 := i
        let t'4 := (t'3 + 1)
        i := t'4
        pure ()
      first'2 := false
      if !((decide ((UInt8.toUInt64 (i)) < ((18 : UInt64) / (6 : UInt64))))) then break
      let t'5 ← PMem.ldU16 (((this + 506) + ((UInt64.toInt64 (UInt8.toUInt64 (i))) * 6).toUInt64) + 2)
      let mut interval_ms : UInt16 := t'5
      if ((UInt32.toInt32 (UInt16.toUInt32 (interval_ms))) == (0 : Int32)) then
        continue
      let t'6 ← PMem.ldU16 (((this + 506) + ((UInt64.toInt64 (UInt8.toUInt64 (i))) * 6).toUInt64) + 4)
      let mut ms_since_last_sent : UInt16 := Int16.toUInt16 (Int32.toInt16 (((UInt32.toInt32 (UInt16.toUInt32 (now16_ms))) - (UInt32.toInt32 (UInt16.toUInt32 (t'6))))))
      let mut ms_before_send_this_message : UInt16 := default  -- uninitialized in C
      if (decide ((UInt32.toInt32 (UInt16.toUInt32 (ms_since_last_sent))) > (UInt32.toInt32 (UInt16.toUInt32 (interval_ms))))) then
        let t'7 := Int16.toUInt16 (Int32.toInt16 ((0 : Int32)))
        ms_before_send_this_message := t'7
      else
        let t'8 := Int16.toUInt16 (Int32.toInt16 (((UInt32.toInt32 (UInt16.toUInt32 (interval_ms))) - (UInt32.toInt32 (UInt16.toUInt32 (ms_since_last_sent))))))
        ms_before_send_this_message := t'8
      if (decide ((UInt32.toInt32 (UInt16.toUInt32 (ms_before_send_this_message))) < (UInt32.toInt32 (UInt16.toUInt32 (ms_before_next_message_to_send))))) then
        let t'9 := UInt8.toInt8 (i)
        PMem.stI8 (this + 524) t'9
        ms_before_next_message_to_send := ms_before_send_this_message
  let t'10 ← PMem.ldI8 (this + 524)
  if ((Int8.toInt32 (t'10)) == (-(1 : Int32))) then
    return Int32.toInt8 ((-(1 : Int32)))
  let t'11 ← PMem.ldI8 (this + 524)
  let t'12 ← PMem.ldU16 (((this + 506) + ((Int8.toInt64 (t'11)) * 6).toUInt64) + 4)
  let mut ms_since_last_sent'2 : UInt16 := Int16.toUInt16 (Int32.toInt16 (((UInt32.toInt32 (UInt16.toUInt32 (now16_ms))) - (UInt32.toInt32 (UInt16.toUInt32 (t'12))))))
  let t'13 ← PMem.ldI8 (this + 524)
  let t'14 ← PMem.ldU16 (((this + 506) + ((Int8.toInt64 (t'13)) * 6).toUInt64) + 2)
  if (decide ((UInt32.toInt32 (UInt16.toUInt32 (ms_since_last_sent'2))) < (UInt32.toInt32 (UInt16.toUInt32 (t'14))))) then
    return Int32.toInt8 ((-(1 : Int32)))
  let t'15 ← PMem.ldI8 (this + 524)
  return t'15

/-- `GCS_MAVLINK.should_send_message_in_delay_callback` as a pure function of its arguments (it reads and writes no memory). -/
def GCS_MAVLINK.should_send_message_in_delay_callback.pure' (this : UInt64) (id : UInt8) : Id Bool := do
  let mut id := id
  let sw'1 := UInt32.toInt32 (UInt8.toUInt32 (id))
  if sw'1 == (31 : Int32) || sw'1 == (0 : Int32) || sw'1 == (73 : Int32) then
    return true
  else
    return false
  return false

/-- C++ `GCS_MAVLINK::should_send_message_in_delay_callback : bool (const ap_message) const`, `GCS_Common.cpp:1233-1251`. -/
def GCS_MAVLINK.should_send_message_in_delay_callback (this : UInt64) (id : UInt8) : PMem.M Bool :=
  pure (_root_.Vehicle_lib.GCS_MAVLINK.should_send_message_in_delay_callback.pure' this id)

/-- C++ `GCS::telem_delay : uint32_t () const`, `AP_Common.h:1324-?`. -/
def GCS.telem_delay (this : UInt64) : PMem.M UInt32 := do
  let t'1 ← AP_ParamT'signed_char_1.operator_const_signed_char__ (this + 174)
  let t'2 ← PMem.ldI8 t'1
  return Int32.toUInt32 (Int8.toInt32 (t'2))

/-- C++ `GCS_MAVLINK::telemetry_delayed : bool () const`, `GCS_Common.cpp:3383-3396`. -/
def GCS_MAVLINK.telemetry_delayed (this : UInt64) : PMem.M Bool := do
  let mut tnow : UInt32 := ((((← PMem.clock) / 1000).toUInt32) >>> (Int32.toUInt32 ((10 : Int32))))
  let t'1 ← gcs
  let t'2 ← GCS.telem_delay t'1
  if (decide (tnow ≥ t'2)) then
    return false
  let t'3 ← PMem.ldU32 (this + 40)
  if (((UInt32.toInt32 (t'3)) == (UInt32.toInt32 ((0 : UInt32)))) && false) then
    return false
  return true

/-- C++ `GCS_MAVLINK::next_deferred_bucket_message_to_send : ap_message (uint16_t)`, `GCS_Common.cpp:1328-1351`. -/
def GCS_MAVLINK.next_deferred_bucket_message_to_send (this : UInt64) (now16_ms : UInt16) : PMem.M UInt8 := do
  let mut now16_ms := now16_ms
  let t'1 ← PMem.ldU8 (this + 728)
  if ((UInt32.toInt32 (UInt8.toUInt32 (t'1))) == (UInt32.toInt32 (UInt8.toUInt32 ((255 : UInt8))))) then
    return (255 : UInt8)
  let t'2 ← PMem.ldU8 (this + 728)
  let t'3 ← PMem.ldU16 (((this + 528) + ((UInt64.toInt64 (UInt8.toUInt64 (t'2))) * 20).toUInt64) + 18)
  let mut ms_since_last_sent : UInt16 := Int16.toUInt16 (Int32.toInt16 (((UInt32.toInt32 (UInt16.toUInt32 (now16_ms))) - (UInt32.toInt32 (UInt16.toUInt32 (t'3))))))
  let t'4 ← PMem.ldU8 (this + 728)
  let t'5 ← GCS_MAVLINK.get_reschedule_interval_ms this ((this + 528) + ((UInt64.toInt64 (UInt8.toUInt64 (t'4))) * 20).toUInt64)
  if (decide ((UInt32.toInt32 (UInt16.toUInt32 (ms_since_last_sent))) < (UInt32.toInt32 (UInt16.toUInt32 (t'5))))) then
    return (255 : UInt8)
  let t'6 ← Bitmask'102.first_set (this + 732)
  let mut next : Int16 := t'6
  if ((Int16.toInt32 (next)) == (-(1 : Int32))) then
    GCS_MAVLINK.find_next_bucket_to_send this now16_ms
    return (255 : UInt8)
  return Int8.toUInt8 (Int16.toInt8 (next))

/-- C++ `GCS_MAVLINK::param_io_timer : void ()`, `GCS_Param.cpp:375-425`. -/
def GCS_MAVLINK.param_io_timer.body (fp : UInt64) (this : UInt64) : PMem.M Unit := do
  GCS_MAVLINK.pending_param_request.pending_param_request (fp + 0)
  let t'1 ← AP_Param.count_parameters
  discard <| pure (t'1)
  let t'2 ← ObjectBuffer'GCS_MAVLINK_pending_param_reply.space (0xbed8 : UInt64) /- &GCS_MAVLINK::param_replies -/
  if (t'2 == (Int32.toUInt32 ((0 : Int32)))) then
    return ()
  let t'3 ← ObjectBuffer'GCS_MAVLINK_pending_param_request.pop (0xbee8 : UInt64) /- &GCS_MAVLINK::param_requests -/ (fp + 0)
  if !t'3 then
    return ()
  GCS_MAVLINK.pending_param_reply.pending_param_reply (fp + 32)
  let mut vp : UInt64 := default  -- uninitialized in C
  let t'4 ← PMem.ldI16 ((fp + 0) + 4)
  if ((Int16.toInt32 (t'4)) != (-(1 : Int32))) then
    PMem.stBits (fp + 80) 0 9 (UInt32.toUInt64 ((0 : UInt32)))
    PMem.stBits (fp + 80) 9 4 (UInt32.toUInt64 ((0 : UInt32)))
    PMem.stBits (fp + 80) 13 18 (UInt32.toUInt64 ((0 : UInt32)))
    PMem.stBits (fp + 80) 31 1 (UInt32.toUInt64 ((0 : UInt32)))
    let t'5 ← PMem.ldI16 ((fp + 0) + 4)
    let t'6 ← AP_Param.find_by_index (Int16.toUInt16 (t'5)) ((fp + 32) + 8) (fp + 80)
    vp := t'6
    if (vp != (0 : UInt64)) then
      AP_Param.copy_name_token vp (fp + 80) ((fp + 32) + 16) (Int64.toUInt64 (Int32.toInt64 ((16 : Int32)))) true
    else
      let t'7 ← PMem.memset ((fp + 32) + 16) (Int8.toInt32 ((0 : Int8))) (17 : UInt64)
      discard <| pure (t'7)
  else
    let t'8 ← PMem.strncpy ((fp + 32) + 16) ((fp + 0) + 6) (Int64.toUInt64 (Int32.toInt64 (((16 : Int32) + (1 : Int32)))))
    discard <| pure (t'8)
    let t'9 ← AP_Param.find ((fp + 0) + 6) ((fp + 32) + 8) (0 : UInt64)
    vp := t'9
  let t'10 ← PMem.ldU32 (fp + 0)
  PMem.stU32 (fp + 32) t'10
  let t'11 ← PMem.ldU32 ((fp + 0) + 24)
  PMem.stU32 ((fp + 32) + 36) t'11
  let t'12 ← PMem.ldU8 ((fp + 0) + 28)
  PMem.stU8 ((fp + 32) + 40) t'12
  let t'13 := Int32.toInt8 ((0 : Int32))
  PMem.stI8 (((fp + 32) + 16) + ((Int32.toInt64 ((16 : Int32))) * 1).toUInt64) t'13
  if (vp != (0 : UInt64)) then
    let t'14 ← PMem.ldU32 ((fp + 32) + 8)
    let t'15 ← AP_Param.cast_to_float vp t'14
    PMem.stF32 ((fp + 32) + 4) t'15
    PMem.stU32 ((fp + 32) + 44) (0 : UInt32)
  else
    let t'16 ← PMem.ldF32 (0xbef8 : UInt64) /- &NaNf -/
    PMem.stF32 ((fp + 32) + 4) t'16
    PMem.stU32 ((fp + 32) + 44) (1 : UInt32)
  let t'17 ← PMem.ldI16 ((fp + 0) + 4)
  PMem.stI16 ((fp + 32) + 12) t'17
  let t'18 ← AP_Param.count_parameters
  PMem.stU16 ((fp + 32) + 14) t'18
  let t'19 ← ObjectBuffer'GCS_MAVLINK_pending_param_reply.push (0xbed8 : UInt64) /- &GCS_MAVLINK::param_replies -/ (fp + 32)
  discard <| pure (t'19)
  return ()

def GCS_MAVLINK.param_io_timer (this : UInt64) : PMem.M Unit := do
  let fp ← PMem.enter 84
  let r ← GCS_MAVLINK.param_io_timer.body fp this
  PMem.leave fp
  return r

/-- C++ `GCS::sysid_this_mav : uint32_t () const`, `AP_Common.h:1323-?`. -/
def GCS.sysid_this_mav (this : UInt64) : PMem.M UInt32 := do
  let t'1 ← AP_ParamT'unsigned_int_3.operator_const_unsigned_int__ (this + 160)
  let t'2 ← PMem.ldU32 t'1
  return t'2

/-- C++ `GCS_MAVLINK::set_channel_private : void (mavlink_channel_t)`, `GCS_MAVLink.cpp:112-116`. -/
def GCS_MAVLINK.set_channel_private (_chan : UInt32) : PMem.M Unit := do
  let mut _chan := _chan
  let mut mask : UInt8 := UInt32.toUInt8 (((1 : UInt32) <<< _chan))
  let t'1 := (0xdf08 : UInt64) /- &GCS_MAVLINK::mavlink_private -/
  let t'2 ← PMem.ldU32 t'1
  let t'3 := (t'2 ||| (UInt8.toUInt32 (mask)))
  PMem.stU32 t'1 t'3
  return ()

/-- C++ `GCS::send_mission_item_reached_message : void (uint16_t)`, `GCS_Common.cpp:2804-2810`. -/
def GCS.send_mission_item_reached_message (this : UInt64) (mission_index : UInt16) : PMem.M Unit := do
  let mut mission_index := mission_index
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
    PMem.stU16 (t'5 + 12) mission_index
    let t'6 ← GCS_Copter.chan this i
    GCS_MAVLINK.send_message t'6 (61 : UInt8)
  return ()

/-- C++ `GCS::sysid_mygcs_last_seen_time_ms : uint32_t () const`, `sitl.h:1200-1202`. -/
def GCS.sysid_mygcs_last_seen_time_ms (this : UInt64) : PMem.M UInt32 := do
  let t'1 ← PMem.ldU32 (this + 432)
  return t'1

/-- C++ `GCS::GCS : void ()`, `GCS.h:1147-1159`. -/
def GCS.GCS (this : UInt64) : PMem.M Unit := do
  HALSITL.Semaphore.Semaphore (this + 8)
  AP_Param.AP_Param'2 (this + 160)
  AP_Param.AP_Param'2 (this + 164)
  AP_Param.AP_Param'2 (this + 168)
  AP_Enum16'GCS_Option.AP_Enum16 (this + 172)
  AP_Param.AP_Param'2 (this + 174)
  PMem.stB (this + 436) ((1 : Int32) != (0 : Int32))
  ObjectArray'GCS_statustext_t.ObjectArray (this + 440) (UInt8.toUInt16 ((30 : UInt8)))
  HALSITL.Semaphore.Semaphore ((this + 480) + 48)
  let t'1 ← PMem.ldU64 (0xc738 : UInt64) /- &GCS::_singleton -/
  if (t'1 == (0 : UInt64)) then
    PMem.stU64 (0xc738 : UInt64) /- &GCS::_singleton -/ this
  else
    pure ()
  AP_Param.setup_object_defaults this (0x57a8 : UInt64) /- &GCS::var_info -/
  return ()

/-- C++ `GCS_MAVLINK::LastRadioStatus::LastRadioStatus : void () noexcept`, `functor.h:836-?`. -/
def GCS_MAVLINK.LastRadioStatus.LastRadioStatus (this : UInt64) : PMem.M Unit := do
  PMem.stU8 (this + 12) (Int8.toUInt8 (Int32.toInt8 ((100 : Int32))))
  return ()

end Vehicle_lib
