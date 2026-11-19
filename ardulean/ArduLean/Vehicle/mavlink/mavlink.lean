import ArduLean.Runtime.GcsPort
import ArduLean.Vehicle.libraries.GCS_MAVLink.GCS_MAVLink

/-!
ArduPilot `mavlink`. Sources: `mavlink_helpers.h`, `mavlink_types.h`, `checksum.h`, `mavlink_msg_rc_channels.h`, `mavlink_msg_system_time.h`, `mavlink_msg_timesync.h`, `mavlink_msg_gps2_raw.h`, `mavlink_msg_mission_item_int.h` and 62 more.

Items of `lean/Vehicle_lib.lean` (the vehicle translation), unchanged; placed by `tools/split_modules.py` (`ArduLean/Vehicle/INDEX.md`).
-/

open FloatLib.Floats (Binary32 Binary64)

set_option linter.unusedVariables false
set_option linter.unreachableTactic false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false

namespace Vehicle_lib

/-- C++ `mavlink_get_msg_entry : const mavlink_msg_entry_t *(uint32_t)`, `mavlink_helpers.h:582-608`. -/
def mavlink_get_msg_entry (msgid : UInt32) : PMem.M UInt64 := do
  let mut msgid := msgid
  let mut low : UInt32 := Int32.toUInt32 ((0 : Int32))
  let mut high : UInt32 := UInt64.toUInt32 ((((4284 : UInt64) / (12 : UInt64)) - (Int64.toUInt64 (Int32.toInt64 ((1 : Int32))))))
  for _ in PMem.loopFuel do
    if !((decide (low < high))) then break
    let mut mid : UInt32 := (((low + (Int32.toUInt32 ((1 : Int32)))) + high) / (Int32.toUInt32 ((2 : Int32))))
    let t'1 ← PMem.ldU32 ((0xce48 : UInt64) /- &mavlink_get_msg_entry(...)::mavlink_message_crcs -/ + ((UInt64.toInt64 (UInt32.toUInt64 (mid))) * 12).toUInt64)
    if (decide (msgid < t'1)) then
      let t'2 := (mid - (Int32.toUInt32 ((1 : Int32))))
      high := t'2
      continue
    let t'3 ← PMem.ldU32 ((0xce48 : UInt64) /- &mavlink_get_msg_entry(...)::mavlink_message_crcs -/ + ((UInt64.toInt64 (UInt32.toUInt64 (mid))) * 12).toUInt64)
    if (decide (msgid > t'3)) then
      low := mid
      continue
    low := mid
    break
  let t'4 ← PMem.ldU32 ((0xce48 : UInt64) /- &mavlink_get_msg_entry(...)::mavlink_message_crcs -/ + ((UInt64.toInt64 (UInt32.toUInt64 (low))) * 12).toUInt64)
  if (t'4 != msgid) then
    return (0 : UInt64)
  return ((0xce48 : UInt64) /- &mavlink_get_msg_entry(...)::mavlink_message_crcs -/ + ((UInt64.toInt64 (UInt32.toUInt64 (low))) * 12).toUInt64)

/-- C++ `_mav_parse_error : void (mavlink_status_t *)`, `mavlink_helpers.h:281-284`. -/
def _mav_parse_error (status : UInt64) : PMem.M Unit := do
  let mut status := status
  let t'1 := (status + 2)
  let t'2 ← PMem.ldU8 t'1
  let t'3 := (t'2 + 1)
  PMem.stU8 t'1 t'3
  return ()

/-- C++ `_mav_trim_payload : uint8_t (const char *, uint8_t)`, `mavlink_helpers.h:115-121`. -/
def _mav_trim_payload (payload : UInt64) (length : UInt8) : PMem.M UInt8 := do
  let mut payload := payload
  let mut length := length
  for _ in PMem.loopFuel do
    let mut sc'2 := (decide ((UInt32.toInt32 (UInt8.toUInt32 (length))) > (1 : Int32)))
    if sc'2 then
      let t'1 ← PMem.ldI8 (payload + ((Int32.toInt64 (((UInt32.toInt32 (UInt8.toUInt32 (length))) - (1 : Int32)))) * 1).toUInt64)
      sc'2 := ((Int8.toInt32 (t'1)) == (0 : Int32))
    if !(sc'2) then break
    let t'3 := length
    let t'4 := (t'3 - 1)
    length := t'4
  return length

/-- C++ `_mav_header_pack : uint8_t (uint8_t *, uint8_t, uint8_t, uint8_t, uint8_t, uint8_t, uint32_t, uint8_t, uint32_t, uint32_t)`, `mavlink_helpers.h:129-168`. -/
def _mav_header_pack (buf : UInt64) (magic : UInt8) (len : UInt8) (incompat_flags : UInt8) (compat_flags : UInt8) (seq : UInt8) (sysid : UInt32) (compid : UInt8) (msgid : UInt32) (target_sysid : UInt32) : PMem.M UInt8 := do
  let mut buf := buf
  let mut magic := magic
  let mut len := len
  let mut incompat_flags := incompat_flags
  let mut compat_flags := compat_flags
  let mut seq := seq
  let mut sysid := sysid
  let mut compid := compid
  let mut msgid := msgid
  let mut target_sysid := target_sysid
  PMem.stU8 (buf + ((Int32.toInt64 ((0 : Int32))) * 1).toUInt64) magic
  PMem.stU8 (buf + ((Int32.toInt64 ((1 : Int32))) * 1).toUInt64) len
  if ((UInt32.toInt32 (UInt8.toUInt32 (magic))) == (254 : Int32)) then
    if (((decide (sysid > (Int32.toUInt32 ((255 : Int32))))) || (decide (target_sysid > (Int32.toUInt32 ((255 : Int32)))))) || (decide (msgid > (Int32.toUInt32 ((255 : Int32)))))) then
      return Int8.toUInt8 (Int32.toInt8 ((0 : Int32)))
    PMem.stU8 (buf + ((Int32.toInt64 ((2 : Int32))) * 1).toUInt64) seq
    let t'1 := UInt32.toUInt8 ((sysid &&& (Int32.toUInt32 ((255 : Int32)))))
    PMem.stU8 (buf + ((Int32.toInt64 ((3 : Int32))) * 1).toUInt64) t'1
    PMem.stU8 (buf + ((Int32.toInt64 ((4 : Int32))) * 1).toUInt64) compid
    let t'2 := UInt32.toUInt8 ((msgid &&& (Int32.toUInt32 ((255 : Int32)))))
    PMem.stU8 (buf + ((Int32.toInt64 ((5 : Int32))) * 1).toUInt64) t'2
    return Int8.toUInt8 (Int32.toInt8 (((5 : Int32) + (1 : Int32))))
  let mut ofs : UInt8 := Int8.toUInt8 (Int32.toInt8 ((2 : Int32)))
  let t'3 := ofs
  let t'4 := (t'3 + 1)
  ofs := t'4
  PMem.stU8 (buf + ((UInt64.toInt64 (UInt8.toUInt64 (t'3))) * 1).toUInt64) incompat_flags
  let t'5 := ofs
  let t'6 := (t'5 + 1)
  ofs := t'6
  PMem.stU8 (buf + ((UInt64.toInt64 (UInt8.toUInt64 (t'5))) * 1).toUInt64) compat_flags
  let t'7 := ofs
  let t'8 := (t'7 + 1)
  ofs := t'8
  PMem.stU8 (buf + ((UInt64.toInt64 (UInt8.toUInt64 (t'7))) * 1).toUInt64) seq
  let t'9 := UInt32.toUInt8 ((sysid &&& (Int32.toUInt32 ((255 : Int32)))))
  let t'10 := ofs
  let t'11 := (t'10 + 1)
  ofs := t'11
  PMem.stU8 (buf + ((UInt64.toInt64 (UInt8.toUInt64 (t'10))) * 1).toUInt64) t'9
  if ((UInt32.toInt32 (UInt8.toUInt32 (incompat_flags))) &&& (2 : Int32)) != (0 : Int32) then
    let t'12 := UInt32.toUInt8 (((sysid >>> (Int32.toUInt32 ((8 : Int32)))) &&& (Int32.toUInt32 ((255 : Int32)))))
    let t'13 := ofs
    let t'14 := (t'13 + 1)
    ofs := t'14
    PMem.stU8 (buf + ((UInt64.toInt64 (UInt8.toUInt64 (t'13))) * 1).toUInt64) t'12
    let t'15 := UInt32.toUInt8 (((sysid >>> (Int32.toUInt32 ((16 : Int32)))) &&& (Int32.toUInt32 ((255 : Int32)))))
    let t'16 := ofs
    let t'17 := (t'16 + 1)
    ofs := t'17
    PMem.stU8 (buf + ((UInt64.toInt64 (UInt8.toUInt64 (t'16))) * 1).toUInt64) t'15
    let t'18 := UInt32.toUInt8 (((sysid >>> (Int32.toUInt32 ((24 : Int32)))) &&& (Int32.toUInt32 ((255 : Int32)))))
    let t'19 := ofs
    let t'20 := (t'19 + 1)
    ofs := t'20
    PMem.stU8 (buf + ((UInt64.toInt64 (UInt8.toUInt64 (t'19))) * 1).toUInt64) t'18
  let t'21 := ofs
  let t'22 := (t'21 + 1)
  ofs := t'22
  PMem.stU8 (buf + ((UInt64.toInt64 (UInt8.toUInt64 (t'21))) * 1).toUInt64) compid
  let t'23 := UInt32.toUInt8 ((msgid &&& (Int32.toUInt32 ((255 : Int32)))))
  let t'24 := ofs
  let t'25 := (t'24 + 1)
  ofs := t'25
  PMem.stU8 (buf + ((UInt64.toInt64 (UInt8.toUInt64 (t'24))) * 1).toUInt64) t'23
  let t'26 := UInt32.toUInt8 (((msgid >>> (Int32.toUInt32 ((8 : Int32)))) &&& (Int32.toUInt32 ((255 : Int32)))))
  let t'27 := ofs
  let t'28 := (t'27 + 1)
  ofs := t'28
  PMem.stU8 (buf + ((UInt64.toInt64 (UInt8.toUInt64 (t'27))) * 1).toUInt64) t'26
  let t'29 := UInt32.toUInt8 (((msgid >>> (Int32.toUInt32 ((16 : Int32)))) &&& (Int32.toUInt32 ((255 : Int32)))))
  let t'30 := ofs
  let t'31 := (t'30 + 1)
  ofs := t'31
  PMem.stU8 (buf + ((UInt64.toInt64 (UInt8.toUInt64 (t'30))) * 1).toUInt64) t'29
  if ((UInt32.toInt32 (UInt8.toUInt32 (incompat_flags))) &&& (4 : Int32)) != (0 : Int32) then
    let t'32 := UInt32.toUInt8 ((target_sysid &&& (Int32.toUInt32 ((255 : Int32)))))
    let t'33 := ofs
    let t'34 := (t'33 + 1)
    ofs := t'34
    PMem.stU8 (buf + ((UInt64.toInt64 (UInt8.toUInt64 (t'33))) * 1).toUInt64) t'32
    let t'35 := UInt32.toUInt8 (((target_sysid >>> (Int32.toUInt32 ((8 : Int32)))) &&& (Int32.toUInt32 ((255 : Int32)))))
    let t'36 := ofs
    let t'37 := (t'36 + 1)
    ofs := t'37
    PMem.stU8 (buf + ((UInt64.toInt64 (UInt8.toUInt64 (t'36))) * 1).toUInt64) t'35
    let t'38 := UInt32.toUInt8 (((target_sysid >>> (Int32.toUInt32 ((16 : Int32)))) &&& (Int32.toUInt32 ((255 : Int32)))))
    let t'39 := ofs
    let t'40 := (t'39 + 1)
    ofs := t'40
    PMem.stU8 (buf + ((UInt64.toInt64 (UInt8.toUInt64 (t'39))) * 1).toUInt64) t'38
    let t'41 := UInt32.toUInt8 (((target_sysid >>> (Int32.toUInt32 ((24 : Int32)))) &&& (Int32.toUInt32 ((255 : Int32)))))
    let t'42 := ofs
    let t'43 := (t'42 + 1)
    ofs := t'43
    PMem.stU8 (buf + ((UInt64.toInt64 (UInt8.toUInt64 (t'42))) * 1).toUInt64) t'41
  return ofs

/-- C++ `crc_accumulate : void (uint8_t, uint16_t *)`, `checksum.h:35-43`. -/
def crc_accumulate (data : UInt8) (crcAccum : UInt64) : PMem.M Unit := do
  let mut data := data
  let mut crcAccum := crcAccum
  let mut tmp : UInt8 := default  -- uninitialized in C
  let t'1 ← PMem.ldU16 crcAccum
  let t'2 := Int8.toUInt8 (Int32.toInt8 (((UInt32.toInt32 (UInt8.toUInt32 (data))) ^^^ (UInt32.toInt32 (UInt8.toUInt32 ((Int8.toUInt8 (Int32.toInt8 (((UInt32.toInt32 (UInt16.toUInt32 (t'1))) &&& (255 : Int32)))))))))))
  tmp := t'2
  let t'3 := (tmp ^^^ (Int8.toUInt8 (Int32.toInt8 (((UInt32.toInt32 (UInt8.toUInt32 (tmp))) <<< (4 : Int32))))))
  tmp := t'3
  let t'4 ← PMem.ldU16 crcAccum
  let t'5 := Int16.toUInt16 (Int32.toInt16 ((((((UInt32.toInt32 (UInt16.toUInt32 (t'4))) >>> (8 : Int32)) ^^^ ((UInt32.toInt32 (UInt8.toUInt32 (tmp))) <<< (8 : Int32))) ^^^ ((UInt32.toInt32 (UInt8.toUInt32 (tmp))) <<< (3 : Int32))) ^^^ ((UInt32.toInt32 (UInt8.toUInt32 (tmp))) >>> (4 : Int32)))))
  PMem.stU16 crcAccum t'5
  return ()

/-- C++ `crc_init : void (uint16_t *)`, `checksum.h:52-55`. -/
def crc_init (crcAccum : UInt64) : PMem.M Unit := do
  let mut crcAccum := crcAccum
  let t'1 := Int16.toUInt16 (Int32.toInt16 ((65535 : Int32)))
  PMem.stU16 crcAccum t'1
  return ()

/-- C++ `crc_calculate : uint16_t (const uint8_t *, uint16_t)`, `checksum.h:65-73`. -/
def crc_calculate.body (fp : UInt64) (pBuffer : UInt64) (length : UInt16) : PMem.M UInt16 := do
  let mut pBuffer := pBuffer
  let mut length := length
  crc_init (fp + 0)
  for _ in PMem.loopFuel do
    let t'1 := length
    let t'2 := (t'1 - 1)
    length := t'2
    if !(t'1 != (0 : UInt16)) then break
    let t'3 := pBuffer
    let t'4 := (t'3 + 1)
    pBuffer := t'4
    let t'5 ← PMem.ldU8 t'3
    crc_accumulate t'5 (fp + 0)
  let t'6 ← PMem.ldU16 (fp + 0)
  return t'6

def crc_calculate (pBuffer : UInt64) (length : UInt16) : PMem.M UInt16 := do
  let fp ← PMem.enter 2
  let r ← crc_calculate.body fp pBuffer length
  PMem.leave fp
  return r

/-- C++ `crc_accumulate_buffer : void (uint16_t *, const char *, uint16_t)`, `checksum.h:85-91`. -/
def crc_accumulate_buffer (crcAccum : UInt64) (pBuffer : UInt64) (length : UInt16) : PMem.M Unit := do
  let mut crcAccum := crcAccum
  let mut pBuffer := pBuffer
  let mut length := length
  let mut p : UInt64 := pBuffer
  for _ in PMem.loopFuel do
    let t'1 := length
    let t'2 := (t'1 - 1)
    length := t'2
    if !(t'1 != (0 : UInt16)) then break
    let t'3 := p
    let t'4 := (t'3 + 1)
    p := t'4
    let t'5 ← PMem.ldU8 t'3
    crc_accumulate t'5 crcAccum
  return ()

/-- C++ `_mavlink_send_uart : void (mavlink_channel_t, const char *, uint16_t)`, `mavlink_helpers.h:1244-1257`. -/
def _mavlink_send_uart (chan : UInt32) (buf : UInt64) (len : UInt16) : PMem.M Unit := do
  let mut chan := chan
  let mut buf := buf
  let mut len := len
  comm_send_buffer chan buf (UInt16.toUInt8 (len))
  return ()

/-- C++ `_mav_finalize_message_chan_send_target : void (mavlink_channel_t, uint32_t, const char *, uint8_t, uint8_t, uint8_t, uint32_t)`, `mavlink_helpers.h:411-475`. -/
def _mav_finalize_message_chan_send_target.body (fp : UInt64) (chan : UInt32) (msgid : UInt32) (packet : UInt64) (min_length : UInt8) (length : UInt8) (crc_extra : UInt8) (target_sysid : UInt32) : PMem.M Unit := do
  let mut chan := chan
  let mut msgid := msgid
  let mut packet := packet
  let mut min_length := min_length
  let mut length := length
  let mut crc_extra := crc_extra
  let mut target_sysid := target_sysid
  let t'1 ← mavlink_get_channel_status (UInt32.toUInt8 (chan))
  let mut status : UInt64 := t'1
  let mut header_len : UInt8 := default  -- uninitialized in C
  let mut signature_len : UInt8 := Int8.toUInt8 (Int32.toInt8 ((0 : Int32)))
  let t'2 ← PMem.ldU8 (status + 16)
  let mut mavlink1 : Bool := (((UInt32.toInt32 (UInt8.toUInt32 (t'2))) &&& (2 : Int32)) != (0 : Int32))
  let mut sc'4 := !mavlink1
  if sc'4 then
    let t'3 ← PMem.ldU64 (status + 24)
    sc'4 := (t'3 != 0)
  let mut sc'7 := sc'4
  if sc'7 then
    let t'5 ← PMem.ldU64 (status + 24)
    let t'6 ← PMem.ldU8 t'5
    sc'7 := ((UInt32.toInt32 (UInt8.toUInt32 (t'6))) &&& (1 : Int32)) != (0 : Int32)
  let mut signing : Bool := sc'7
  let mut incompat_flags : UInt8 := Int8.toUInt8 (Int32.toInt8 ((0 : Int32)))
  if mavlink1 then
    length := min_length
    let mut sc'9 := (decide (msgid > (Int32.toUInt32 ((255 : Int32)))))
    if !sc'9 then
      let t'8 ← PMem.ldU32 (0xbc50 : UInt64) /- &mavlink_system -/
      sc'9 := (decide (t'8 > (Int32.toUInt32 ((255 : Int32)))))
    if (sc'9 || (decide (target_sysid > (Int32.toUInt32 ((255 : Int32)))))) then
      _mav_parse_error status
      return ()
  else
    if signing then
      let t'10 := (incompat_flags ||| (Int8.toUInt8 (Int32.toInt8 ((1 : Int32)))))
      incompat_flags := t'10
    let t'11 ← PMem.ldU32 (0xbc50 : UInt64) /- &mavlink_system -/
    if (decide (t'11 > (Int32.toUInt32 ((255 : Int32))))) then
      let t'12 := (incompat_flags ||| (Int8.toUInt8 (Int32.toInt8 ((2 : Int32)))))
      incompat_flags := t'12
    if (decide (target_sysid > (Int32.toUInt32 ((255 : Int32))))) then
      let t'13 := (incompat_flags ||| (Int8.toUInt8 (Int32.toInt8 ((4 : Int32)))))
      incompat_flags := t'13
    let t'14 ← _mav_trim_payload packet length
    length := t'14
  let mut c'15 : Int32 := default
  if mavlink1 then
    c'15 := (254 : Int32)
  else
    c'15 := (253 : Int32)
  let t'16 ← PMem.ldU8 (status + 10)
  let t'17 ← PMem.ldU32 (0xbc50 : UInt64) /- &mavlink_system -/
  let t'18 ← PMem.ldU8 ((0xbc50 : UInt64) /- &mavlink_system -/ + 4)
  let t'19 ← _mav_header_pack (fp + 8) (Int8.toUInt8 (Int32.toInt8 (c'15))) length incompat_flags (Int8.toUInt8 (Int32.toInt8 ((0 : Int32)))) t'16 t'17 t'18 msgid target_sysid
  header_len := t'19
  let t'20 := (status + 10)
  let t'21 ← PMem.ldU8 t'20
  let t'22 := (t'21 + 1)
  PMem.stU8 t'20 t'22
  let t'23 ← crc_calculate ((fp + 8) + ((Int32.toInt64 ((1 : Int32))) * 1).toUInt64) (Int16.toUInt16 (Int32.toInt16 (((UInt32.toInt32 (UInt8.toUInt32 (header_len))) - (1 : Int32)))))
  PMem.stU16 (fp + 0) t'23
  crc_accumulate_buffer (fp + 0) packet (UInt8.toUInt16 (length))
  crc_accumulate crc_extra (fp + 0)
  let t'24 ← PMem.ldU16 (fp + 0)
  let t'25 := Int8.toUInt8 (Int32.toInt8 (((UInt32.toInt32 (UInt16.toUInt32 (t'24))) &&& (255 : Int32))))
  PMem.stU8 ((fp + 32) + ((Int32.toInt64 ((0 : Int32))) * 1).toUInt64) t'25
  let t'26 ← PMem.ldU16 (fp + 0)
  let t'27 := Int8.toUInt8 (Int32.toInt8 (((UInt32.toInt32 (UInt16.toUInt32 (t'26))) >>> (8 : Int32))))
  PMem.stU8 ((fp + 32) + ((Int32.toInt64 ((1 : Int32))) * 1).toUInt64) t'27
  if signing then
    PMem.unreached "mavlink_sign_packet"
    let t'28 := (default : UInt8)
    signature_len := t'28
  comm_send_lock chan (Int16.toUInt16 (Int32.toInt16 (((((UInt32.toInt32 (UInt8.toUInt32 (header_len))) + (2 : Int32)) + (UInt32.toInt32 (UInt16.toUInt32 ((UInt8.toUInt16 (length)))))) + (UInt32.toInt32 (UInt16.toUInt32 ((UInt8.toUInt16 (signature_len)))))))))
  _mavlink_send_uart chan (fp + 8) (UInt8.toUInt16 (header_len))
  _mavlink_send_uart chan packet (UInt8.toUInt16 (length))
  _mavlink_send_uart chan (fp + 32) (Int16.toUInt16 (Int32.toInt16 ((2 : Int32))))
  if ((UInt32.toInt32 (UInt8.toUInt32 (signature_len))) != (0 : Int32)) then
    _mavlink_send_uart chan (fp + 40) (UInt8.toUInt16 (signature_len))
  comm_send_unlock chan
  return ()

def _mav_finalize_message_chan_send_target (chan : UInt32) (msgid : UInt32) (packet : UInt64) (min_length : UInt8) (length : UInt8) (crc_extra : UInt8) (target_sysid : UInt32) : PMem.M Unit := do
  let fp ← PMem.enter 53
  let r ← _mav_finalize_message_chan_send_target.body fp chan msgid packet min_length length crc_extra target_sysid
  PMem.leave fp
  return r

/-- C++ `_mav_finalize_message_chan_send : void (mavlink_channel_t, uint32_t, const char *, uint8_t, uint8_t, uint8_t)`, `mavlink_helpers.h:477-482`. -/
def _mav_finalize_message_chan_send (chan : UInt32) (msgid : UInt32) (packet : UInt64) (min_length : UInt8) (length : UInt8) (crc_extra : UInt8) : PMem.M Unit := do
  let mut chan := chan
  let mut msgid := msgid
  let mut packet := packet
  let mut min_length := min_length
  let mut length := length
  let mut crc_extra := crc_extra
  _mav_finalize_message_chan_send_target chan msgid packet min_length length crc_extra (Int32.toUInt32 ((0 : Int32)))
  return ()

/-- `__mavlink_message.__mavlink_message` as a pure function of its arguments (it reads and writes no memory). -/
def __mavlink_message.__mavlink_message.pure' (this : UInt64) : Id Unit := do
  return ()

/-- C++ `__mavlink_message::__mavlink_message : void () noexcept`, `mavlink_types.h:?-?`. -/
def __mavlink_message.__mavlink_message (this : UInt64) : PMem.M Unit :=
  pure (_root_.Vehicle_lib.__mavlink_message.__mavlink_message.pure' this)

/-- `__mavlink_status.__mavlink_status` as a pure function of its arguments (it reads and writes no memory). -/
def __mavlink_status.__mavlink_status.pure' (this : UInt64) : Id Unit := do
  return ()

/-- C++ `__mavlink_status::__mavlink_status : void () noexcept`, `mavlink_types.h:?-?`. -/
def __mavlink_status.__mavlink_status (this : UInt64) : PMem.M Unit :=
  pure (_root_.Vehicle_lib.__mavlink_status.__mavlink_status.pure' this)

/-- C++ `mavlink_start_checksum : void (mavlink_message_t *)`, `mavlink_helpers.h:564-569`. -/
def mavlink_start_checksum.body (fp : UInt64) (msg : UInt64) : PMem.M Unit := do
  let mut msg := msg
  PMem.stU16 (fp + 0) (Int16.toUInt16 (Int32.toInt16 ((0 : Int32))))
  crc_init (fp + 0)
  let t'1 ← PMem.ldU16 (fp + 0)
  PMem.stU16 msg t'1
  return ()

def mavlink_start_checksum (msg : UInt64) : PMem.M Unit := do
  let fp ← PMem.enter 2
  let r ← mavlink_start_checksum.body fp msg
  PMem.leave fp
  return r

/-- C++ `mavlink_update_checksum : void (mavlink_message_t *, uint8_t)`, `mavlink_helpers.h:571-576`. -/
def mavlink_update_checksum.body (fp : UInt64) (msg : UInt64) (c : UInt8) : PMem.M Unit := do
  let mut msg := msg
  let mut c := c
  let t'1 ← PMem.ldU16 msg
  PMem.stU16 (fp + 0) t'1
  crc_accumulate c (fp + 0)
  let t'2 ← PMem.ldU16 (fp + 0)
  PMem.stU16 msg t'2
  return ()

def mavlink_update_checksum (msg : UInt64) (c : UInt8) : PMem.M Unit := do
  let fp ← PMem.enter 2
  let r ← mavlink_update_checksum.body fp msg c
  PMem.leave fp
  return r

/-- C++ `mavlink_frame_char_buffer : uint8_t (mavlink_message_t *, mavlink_status_t *, uint8_t, mavlink_message_t *, mavlink_status_t *)`, `mavlink_helpers.h:724-1077`. -/
def mavlink_frame_char_buffer.body (fp : UInt64) (rxmsg : UInt64) (status : UInt64) (c : UInt8) (r_message : UInt64) (r_mavlink_status : UInt64) : PMem.M UInt8 := do
  PMem.stU64 (fp + 0) rxmsg
  let mut status := status
  let mut c := c
  let mut r_message := r_message
  let mut r_mavlink_status := r_mavlink_status
  let t'1 := UInt32.toUInt8 ((0 : UInt32))
  PMem.stU8 status t'1
  for _ in [0:1] do
    let t'2 ← PMem.ldU32 (status + 4)
    let sw'3 := UInt32.toInt32 (t'2)
    if sw'3 == (0 : Int32) || sw'3 == (1 : Int32) then
      if ((UInt32.toInt32 (UInt8.toUInt32 (c))) == (253 : Int32)) then
        PMem.stU32 (status + 4) (2 : UInt32)
        let t'4 := Int8.toUInt8 (Int32.toInt8 ((0 : Int32)))
        let t'5 ← PMem.ldU64 (fp + 0)
        PMem.stU8 (t'5 + 3) t'4
        let t'6 ← PMem.ldU64 (fp + 0)
        PMem.stU8 (t'6 + 2) c
        let t'7 := (status + 16)
        let t'8 ← PMem.ldU8 t'7
        let t'9 := (t'8 &&& (Int8.toUInt8 (Int32.toInt8 ((~~~(1 : Int32))))))
        PMem.stU8 t'7 t'9
        let t'10 ← PMem.ldU64 (fp + 0)
        mavlink_start_checksum t'10
      else
        if ((UInt32.toInt32 (UInt8.toUInt32 (c))) == (254 : Int32)) then
          PMem.stU32 (status + 4) (2 : UInt32)
          let t'11 := Int8.toUInt8 (Int32.toInt8 ((0 : Int32)))
          let t'12 ← PMem.ldU64 (fp + 0)
          PMem.stU8 (t'12 + 3) t'11
          let t'13 ← PMem.ldU64 (fp + 0)
          PMem.stU8 (t'13 + 2) c
          let t'14 := (status + 16)
          let t'15 ← PMem.ldU8 t'14
          let t'16 := (t'15 ||| (Int8.toUInt8 (Int32.toInt8 ((1 : Int32)))))
          PMem.stU8 t'14 t'16
          let t'17 ← PMem.ldU64 (fp + 0)
          mavlink_start_checksum t'17
    else if sw'3 == (2 : Int32) then
      let t'18 ← PMem.ldU8 status
      if t'18 != (0 : UInt8) then
        let t'19 := (status + 1)
        let t'20 ← PMem.ldU8 t'19
        let t'21 := (t'20 + 1)
        PMem.stU8 t'19 t'21
        _mav_parse_error status
        let t'22 := UInt32.toUInt8 ((0 : UInt32))
        PMem.stU8 status t'22
        PMem.stU32 (status + 4) (1 : UInt32)
      else
        let t'23 ← PMem.ldU64 (fp + 0)
        PMem.stU8 (t'23 + 3) c
        let t'24 := Int8.toUInt8 (Int32.toInt8 ((0 : Int32)))
        PMem.stU8 (status + 8) t'24
        let t'25 ← PMem.ldU64 (fp + 0)
        mavlink_update_checksum t'25 c
        let t'26 ← PMem.ldU8 (status + 16)
        if ((UInt32.toInt32 (UInt8.toUInt32 (t'26))) &&& (1 : Int32)) != (0 : Int32) then
          let t'27 := Int8.toUInt8 (Int32.toInt8 ((0 : Int32)))
          let t'28 ← PMem.ldU64 (fp + 0)
          PMem.stU8 (t'28 + 4) t'27
          let t'29 := Int8.toUInt8 (Int32.toInt8 ((0 : Int32)))
          let t'30 ← PMem.ldU64 (fp + 0)
          PMem.stU8 (t'30 + 5) t'29
          let t'31 := Int32.toUInt32 ((0 : Int32))
          let t'32 ← PMem.ldU64 (fp + 0)
          PMem.stU32 (t'32 + 296) t'31
          PMem.stU32 (status + 4) (5 : UInt32)
        else
          PMem.stU32 (status + 4) (3 : UInt32)
    else if sw'3 == (3 : Int32) then
      let t'33 ← PMem.ldU64 (fp + 0)
      PMem.stU8 (t'33 + 4) c
      let t'34 ← PMem.ldU64 (fp + 0)
      let t'35 ← PMem.ldU8 (t'34 + 4)
      if (((UInt32.toInt32 (UInt8.toUInt32 (t'35))) &&& (~~~(7 : Int32))) != (0 : Int32)) then
        _mav_parse_error status
        let t'36 := UInt32.toUInt8 ((0 : UInt32))
        PMem.stU8 status t'36
        PMem.stU32 (status + 4) (1 : UInt32)
        break
      let t'37 ← PMem.ldU64 (fp + 0)
      let t'38 ← PMem.ldU8 (t'37 + 4)
      if !(((UInt32.toInt32 (UInt8.toUInt32 (t'38))) &&& (4 : Int32)) != (0 : Int32)) then
        let t'39 := Int32.toUInt32 ((0 : Int32))
        let t'40 ← PMem.ldU64 (fp + 0)
        PMem.stU32 (t'40 + 296) t'39
      let t'41 ← PMem.ldU64 (fp + 0)
      mavlink_update_checksum t'41 c
      PMem.stU32 (status + 4) (4 : UInt32)
    else if sw'3 == (4 : Int32) then
      let t'42 ← PMem.ldU64 (fp + 0)
      PMem.stU8 (t'42 + 5) c
      let t'43 ← PMem.ldU64 (fp + 0)
      mavlink_update_checksum t'43 c
      PMem.stU32 (status + 4) (5 : UInt32)
    else if sw'3 == (5 : Int32) then
      let t'44 ← PMem.ldU64 (fp + 0)
      PMem.stU8 (t'44 + 6) c
      let t'45 ← PMem.ldU64 (fp + 0)
      mavlink_update_checksum t'45 c
      PMem.stU32 (status + 4) (6 : UInt32)
    else if sw'3 == (6 : Int32) then
      let t'46 := UInt8.toUInt32 (c)
      let t'47 ← PMem.ldU64 (fp + 0)
      PMem.stU32 (t'47 + 8) t'46
      let t'48 ← PMem.ldU64 (fp + 0)
      mavlink_update_checksum t'48 c
      let t'49 ← PMem.ldU64 (fp + 0)
      let t'50 ← PMem.ldU8 (t'49 + 4)
      if ((UInt32.toInt32 (UInt8.toUInt32 (t'50))) &&& (2 : Int32)) != (0 : Int32) then
        PMem.stU32 (status + 4) (17 : UInt32)
      else
        PMem.stU32 (status + 4) (7 : UInt32)
    else if sw'3 == (17 : Int32) then
      let t'51 ← PMem.ldU64 (fp + 0)
      let t'52 := (t'51 + 8)
      let t'53 ← PMem.ldU32 t'52
      let t'54 := (t'53 ||| ((UInt8.toUInt32 (c)) <<< (Int32.toUInt32 ((8 : Int32)))))
      PMem.stU32 t'52 t'54
      let t'55 ← PMem.ldU64 (fp + 0)
      mavlink_update_checksum t'55 c
      PMem.stU32 (status + 4) (18 : UInt32)
    else if sw'3 == (18 : Int32) then
      let t'56 ← PMem.ldU64 (fp + 0)
      let t'57 := (t'56 + 8)
      let t'58 ← PMem.ldU32 t'57
      let t'59 := (t'58 ||| ((UInt8.toUInt32 (c)) <<< (Int32.toUInt32 ((16 : Int32)))))
      PMem.stU32 t'57 t'59
      let t'60 ← PMem.ldU64 (fp + 0)
      mavlink_update_checksum t'60 c
      PMem.stU32 (status + 4) (19 : UInt32)
    else if sw'3 == (19 : Int32) then
      let t'61 ← PMem.ldU64 (fp + 0)
      let t'62 := (t'61 + 8)
      let t'63 ← PMem.ldU32 t'62
      let t'64 := (t'63 ||| ((UInt8.toUInt32 (c)) <<< (Int32.toUInt32 ((24 : Int32)))))
      PMem.stU32 t'62 t'64
      let t'65 ← PMem.ldU64 (fp + 0)
      mavlink_update_checksum t'65 c
      PMem.stU32 (status + 4) (7 : UInt32)
    else if sw'3 == (7 : Int32) then
      let t'66 ← PMem.ldU64 (fp + 0)
      PMem.stU8 (t'66 + 12) c
      let t'67 ← PMem.ldU64 (fp + 0)
      mavlink_update_checksum t'67 c
      PMem.stU32 (status + 4) (8 : UInt32)
    else if sw'3 == (8 : Int32) then
      let t'68 := UInt8.toUInt32 (c)
      let t'69 ← PMem.ldU64 (fp + 0)
      PMem.stBits t'69 104 24 (UInt32.toUInt64 (t'68))
      let t'70 ← PMem.ldU64 (fp + 0)
      mavlink_update_checksum t'70 c
      let t'71 ← PMem.ldU8 (status + 16)
      if ((UInt32.toInt32 (UInt8.toUInt32 (t'71))) &&& (1 : Int32)) != (0 : Int32) then
        let t'72 ← PMem.ldU64 (fp + 0)
        let t'73 ← PMem.ldU8 (t'72 + 3)
        if (decide ((UInt32.toInt32 (UInt8.toUInt32 (t'73))) > (0 : Int32))) then
          PMem.stU32 (status + 4) (11 : UInt32)
        else
          PMem.stU32 (status + 4) (12 : UInt32)
      else
        PMem.stU32 (status + 4) (9 : UInt32)
    else if sw'3 == (9 : Int32) then
      let t'74 ← PMem.ldU64 (fp + 0)
      let t'75 ← PMem.ldBits t'74 104 24
      let t'76 := ((UInt64.toUInt32 (t'75)) ||| ((UInt8.toUInt32 (c)) <<< (Int32.toUInt32 ((8 : Int32)))))
      PMem.stBits t'74 104 24 (UInt32.toUInt64 (t'76))
      let t'77 ← PMem.ldU64 (fp + 0)
      mavlink_update_checksum t'77 c
      PMem.stU32 (status + 4) (10 : UInt32)
    else if sw'3 == (10 : Int32) then
      let t'78 ← PMem.ldU64 (fp + 0)
      let t'79 ← PMem.ldBits t'78 104 24
      let t'80 := ((UInt64.toUInt32 (t'79)) ||| ((UInt8.toUInt32 (c)) <<< (Int32.toUInt32 ((16 : Int32)))))
      PMem.stBits t'78 104 24 (UInt32.toUInt64 (t'80))
      let t'81 ← PMem.ldU64 (fp + 0)
      mavlink_update_checksum t'81 c
      let t'82 ← PMem.ldU64 (fp + 0)
      let t'83 ← PMem.ldU8 (t'82 + 4)
      if ((UInt32.toInt32 (UInt8.toUInt32 (t'83))) &&& (4 : Int32)) != (0 : Int32) then
        PMem.stU32 (status + 4) (20 : UInt32)
      else
        let t'84 ← PMem.ldU64 (fp + 0)
        let t'85 ← PMem.ldU8 (t'84 + 3)
        if (decide ((UInt32.toInt32 (UInt8.toUInt32 (t'85))) > (0 : Int32))) then
          PMem.stU32 (status + 4) (11 : UInt32)
        else
          PMem.stU32 (status + 4) (12 : UInt32)
    else if sw'3 == (20 : Int32) then
      let t'86 := UInt8.toUInt32 (c)
      let t'87 ← PMem.ldU64 (fp + 0)
      PMem.stU32 (t'87 + 296) t'86
      let t'88 ← PMem.ldU64 (fp + 0)
      mavlink_update_checksum t'88 c
      PMem.stU32 (status + 4) (21 : UInt32)
    else if sw'3 == (21 : Int32) then
      let t'89 ← PMem.ldU64 (fp + 0)
      let t'90 := (t'89 + 296)
      let t'91 ← PMem.ldU32 t'90
      let t'92 := (t'91 ||| ((UInt8.toUInt32 (c)) <<< (Int32.toUInt32 ((8 : Int32)))))
      PMem.stU32 t'90 t'92
      let t'93 ← PMem.ldU64 (fp + 0)
      mavlink_update_checksum t'93 c
      PMem.stU32 (status + 4) (22 : UInt32)
    else if sw'3 == (22 : Int32) then
      let t'94 ← PMem.ldU64 (fp + 0)
      let t'95 := (t'94 + 296)
      let t'96 ← PMem.ldU32 t'95
      let t'97 := (t'96 ||| ((UInt8.toUInt32 (c)) <<< (Int32.toUInt32 ((16 : Int32)))))
      PMem.stU32 t'95 t'97
      let t'98 ← PMem.ldU64 (fp + 0)
      mavlink_update_checksum t'98 c
      PMem.stU32 (status + 4) (23 : UInt32)
    else if sw'3 == (23 : Int32) then
      let t'99 ← PMem.ldU64 (fp + 0)
      let t'100 := (t'99 + 296)
      let t'101 ← PMem.ldU32 t'100
      let t'102 := (t'101 ||| ((UInt8.toUInt32 (c)) <<< (Int32.toUInt32 ((24 : Int32)))))
      PMem.stU32 t'100 t'102
      let t'103 ← PMem.ldU64 (fp + 0)
      mavlink_update_checksum t'103 c
      let t'104 ← PMem.ldU64 (fp + 0)
      let t'105 ← PMem.ldU8 (t'104 + 3)
      if (decide ((UInt32.toInt32 (UInt8.toUInt32 (t'105))) > (0 : Int32))) then
        PMem.stU32 (status + 4) (11 : UInt32)
      else
        PMem.stU32 (status + 4) (12 : UInt32)
    else if sw'3 == (11 : Int32) then
      let t'106 := UInt8.toInt8 (c)
      let t'107 ← PMem.ldU64 (fp + 0)
      let t'108 := (status + 8)
      let t'109 ← PMem.ldU8 t'108
      let t'110 := (t'109 + 1)
      PMem.stU8 t'108 t'110
      PMem.stI8 (((t'107 + 16) + ((Int32.toInt64 ((0 : Int32))) * 8).toUInt64) + ((UInt64.toInt64 (UInt8.toUInt64 (t'109))) * 1).toUInt64) t'106
      let t'111 ← PMem.ldU64 (fp + 0)
      mavlink_update_checksum t'111 c
      let t'112 ← PMem.ldU8 (status + 8)
      let t'113 ← PMem.ldU64 (fp + 0)
      let t'114 ← PMem.ldU8 (t'113 + 3)
      if ((UInt32.toInt32 (UInt8.toUInt32 (t'112))) == (UInt32.toInt32 (UInt8.toUInt32 (t'114)))) then
        PMem.stU32 (status + 4) (12 : UInt32)
    else if sw'3 == (12 : Int32) then
      let t'115 ← PMem.ldU64 (fp + 0)
      let t'116 ← PMem.ldBits t'115 104 24
      let t'117 ← mavlink_get_msg_entry (UInt64.toUInt32 (t'116))
      let mut e : UInt64 := t'117
      if (e == (0 : UInt64)) then
        PMem.stU32 (status + 4) (14 : UInt32)
        let t'118 ← PMem.ldU64 (fp + 0)
        PMem.stU8 ((t'118 + 280) + ((Int32.toInt64 ((0 : Int32))) * 1).toUInt64) c
      else
        let t'119 ← PMem.ldU8 (e + 4)
        let mut crc_extra : UInt8 := t'119
        let t'120 ← PMem.ldU64 (fp + 0)
        mavlink_update_checksum t'120 crc_extra
        let t'121 ← PMem.ldU64 (fp + 0)
        let t'122 ← PMem.ldU16 t'121
        if ((UInt32.toInt32 (UInt8.toUInt32 (c))) != ((UInt32.toInt32 (UInt16.toUInt32 (t'122))) &&& (255 : Int32))) then
          PMem.stU32 (status + 4) (14 : UInt32)
        else
          PMem.stU32 (status + 4) (13 : UInt32)
        let t'123 ← PMem.ldU64 (fp + 0)
        PMem.stU8 ((t'123 + 280) + ((Int32.toInt64 ((0 : Int32))) * 1).toUInt64) c
        let t'124 ← PMem.ldU8 (e + 6)
        let mut c'125 : Int32 := default
        if (decide ((UInt32.toInt32 (UInt8.toUInt32 (t'124))) < (255 : Int32))) then
          let t'126 ← PMem.ldU8 (e + 6)
          c'125 := UInt32.toInt32 (UInt8.toUInt32 (t'126))
        else
          c'125 := (255 : Int32)
        let mut fill_len : UInt8 := Int8.toUInt8 (Int32.toInt8 (c'125))
        let mut sc'128 := (e != 0)
        if sc'128 then
          let t'127 ← PMem.ldU8 (status + 8)
          sc'128 := (decide ((UInt32.toInt32 (UInt8.toUInt32 (t'127))) < (UInt32.toInt32 (UInt8.toUInt32 (fill_len)))))
        if sc'128 then
          let t'129 ← PMem.ldU64 (fp + 0)
          let t'130 ← PMem.ldU8 (status + 8)
          let t'131 ← PMem.ldU8 (status + 8)
          let t'132 ← PMem.memset (((t'129 + 16) + ((Int32.toInt64 ((0 : Int32))) * 8).toUInt64) + ((UInt64.toInt64 (UInt8.toUInt64 (t'130))) * 1).toUInt64) (0 : Int32) (Int64.toUInt64 (Int32.toInt64 (((UInt32.toInt32 (UInt8.toUInt32 (fill_len))) - (UInt32.toInt32 (UInt8.toUInt32 (t'131)))))))
          discard <| pure (t'132)
      break
      let t'133 ← PMem.ldU32 (status + 4)
      let mut sc'136 := ((UInt32.toInt32 (t'133)) == (UInt32.toInt32 ((14 : UInt32))))
      if !sc'136 then
        let t'134 ← PMem.ldU64 (fp + 0)
        let t'135 ← PMem.ldU16 t'134
        sc'136 := ((UInt32.toInt32 (UInt8.toUInt32 (c))) != ((UInt32.toInt32 (UInt16.toUInt32 (t'135))) >>> (8 : Int32)))
      if sc'136 then
        let t'137 := UInt32.toUInt8 ((2 : UInt32))
        PMem.stU8 status t'137
      else
        let t'138 := UInt32.toUInt8 ((1 : UInt32))
        PMem.stU8 status t'138
      let t'139 ← PMem.ldU64 (fp + 0)
      PMem.stU8 ((t'139 + 280) + ((Int32.toInt64 ((1 : Int32))) * 1).toUInt64) c
      let t'140 ← PMem.ldU64 (fp + 0)
      let t'141 ← PMem.ldU8 (t'140 + 4)
      if ((UInt32.toInt32 (UInt8.toUInt32 (t'141))) &&& (1 : Int32)) != (0 : Int32) then
        let t'142 ← PMem.ldU8 status
        if ((UInt32.toInt32 (UInt8.toUInt32 (t'142))) == (UInt32.toInt32 ((2 : UInt32)))) then
          PMem.stU32 (status + 4) (16 : UInt32)
        else
          PMem.stU32 (status + 4) (15 : UInt32)
          let t'143 := UInt32.toUInt8 ((0 : UInt32))
          PMem.stU8 status t'143
        let t'144 := Int8.toUInt8 (Int32.toInt8 ((13 : Int32)))
        PMem.stU8 (status + 17) t'144
      else
        let t'145 ← PMem.ldU64 (status + 24)
        let mut sc'148 := (t'145 != 0)
        if sc'148 then
          let t'146 ← PMem.ldU64 (status + 24)
          let t'147 ← PMem.ldU64 (t'146 + 48)
          sc'148 := ((t'147 == (0 : UInt64)) || (!false))
        if sc'148 then
          let t'149 ← PMem.ldU8 status
          if ((UInt32.toInt32 (UInt8.toUInt32 (t'149))) != (UInt32.toInt32 ((2 : UInt32)))) then
            let t'150 := UInt32.toUInt8 ((3 : UInt32))
            PMem.stU8 status t'150
        PMem.stU32 (status + 4) (1 : UInt32)
        if (r_message != (0 : UInt64)) then
          let t'151 ← PMem.ldU64 (fp + 0)
          let t'152 ← PMem.memcpy r_message t'151 (304 : UInt64)
          discard <| pure (t'152)
    else if sw'3 == (13 : Int32) || sw'3 == (14 : Int32) then
      let t'153 ← PMem.ldU32 (status + 4)
      let mut sc'156 := ((UInt32.toInt32 (t'153)) == (UInt32.toInt32 ((14 : UInt32))))
      if !sc'156 then
        let t'154 ← PMem.ldU64 (fp + 0)
        let t'155 ← PMem.ldU16 t'154
        sc'156 := ((UInt32.toInt32 (UInt8.toUInt32 (c))) != ((UInt32.toInt32 (UInt16.toUInt32 (t'155))) >>> (8 : Int32)))
      if sc'156 then
        let t'157 := UInt32.toUInt8 ((2 : UInt32))
        PMem.stU8 status t'157
      else
        let t'158 := UInt32.toUInt8 ((1 : UInt32))
        PMem.stU8 status t'158
      let t'159 ← PMem.ldU64 (fp + 0)
      PMem.stU8 ((t'159 + 280) + ((Int32.toInt64 ((1 : Int32))) * 1).toUInt64) c
      let t'160 ← PMem.ldU64 (fp + 0)
      let t'161 ← PMem.ldU8 (t'160 + 4)
      if ((UInt32.toInt32 (UInt8.toUInt32 (t'161))) &&& (1 : Int32)) != (0 : Int32) then
        let t'162 ← PMem.ldU8 status
        if ((UInt32.toInt32 (UInt8.toUInt32 (t'162))) == (UInt32.toInt32 ((2 : UInt32)))) then
          PMem.stU32 (status + 4) (16 : UInt32)
        else
          PMem.stU32 (status + 4) (15 : UInt32)
          let t'163 := UInt32.toUInt8 ((0 : UInt32))
          PMem.stU8 status t'163
        let t'164 := Int8.toUInt8 (Int32.toInt8 ((13 : Int32)))
        PMem.stU8 (status + 17) t'164
      else
        let t'165 ← PMem.ldU64 (status + 24)
        let mut sc'168 := (t'165 != 0)
        if sc'168 then
          let t'166 ← PMem.ldU64 (status + 24)
          let t'167 ← PMem.ldU64 (t'166 + 48)
          sc'168 := ((t'167 == (0 : UInt64)) || (!false))
        if sc'168 then
          let t'169 ← PMem.ldU8 status
          if ((UInt32.toInt32 (UInt8.toUInt32 (t'169))) != (UInt32.toInt32 ((2 : UInt32)))) then
            let t'170 := UInt32.toUInt8 ((3 : UInt32))
            PMem.stU8 status t'170
        PMem.stU32 (status + 4) (1 : UInt32)
        if (r_message != (0 : UInt64)) then
          let t'171 ← PMem.ldU64 (fp + 0)
          let t'172 ← PMem.memcpy r_message t'171 (304 : UInt64)
          discard <| pure (t'172)
    else if sw'3 == (15 : Int32) || sw'3 == (16 : Int32) then
      let t'173 ← PMem.ldU64 (fp + 0)
      let t'174 ← PMem.ldU8 (status + 17)
      PMem.stU8 ((t'173 + 282) + ((Int32.toInt64 (((13 : Int32) - (UInt32.toInt32 (UInt8.toUInt32 (t'174)))))) * 1).toUInt64) c
      let t'175 := (status + 17)
      let t'176 ← PMem.ldU8 t'175
      let t'177 := (t'176 - 1)
      PMem.stU8 t'175 t'177
      let t'178 ← PMem.ldU8 (status + 17)
      if ((UInt32.toInt32 (UInt8.toUInt32 (t'178))) == (0 : Int32)) then
        let mut sig_ok : Bool := false
        let mut sc'181 := !sig_ok
        if sc'181 then
          let t'179 ← PMem.ldU64 (status + 24)
          let t'180 ← PMem.ldU64 (t'179 + 48)
          sc'181 := ((t'180 != 0) && false)
        if sc'181 then
          sig_ok := true
        let t'182 ← PMem.ldU32 (status + 4)
        if ((UInt32.toInt32 (t'182)) == (UInt32.toInt32 ((16 : UInt32)))) then
          let t'183 := UInt32.toUInt8 ((2 : UInt32))
          PMem.stU8 status t'183
        else
          if sig_ok then
            let t'184 := UInt32.toUInt8 ((1 : UInt32))
            PMem.stU8 status t'184
          else
            let t'185 := UInt32.toUInt8 ((3 : UInt32))
            PMem.stU8 status t'185
        PMem.stU32 (status + 4) (1 : UInt32)
        if (r_message != (0 : UInt64)) then
          let t'186 ← PMem.ldU64 (fp + 0)
          let t'187 ← PMem.memcpy r_message t'186 (304 : UInt64)
          discard <| pure (t'187)
    else
      pure ()
  let t'188 ← PMem.ldU8 status
  if ((UInt32.toInt32 (UInt8.toUInt32 (t'188))) == (UInt32.toInt32 ((1 : UInt32)))) then
    let t'189 ← PMem.ldU64 (fp + 0)
    let t'190 ← PMem.ldU8 (t'189 + 6)
    PMem.stU8 (status + 9) t'190
    let t'191 ← PMem.ldU16 (status + 12)
    if ((UInt32.toInt32 (UInt16.toUInt32 (t'191))) == (0 : Int32)) then
      let t'192 := Int16.toUInt16 (Int32.toInt16 ((0 : Int32)))
      PMem.stU16 (status + 14) t'192
    let t'193 := (status + 12)
    let t'194 ← PMem.ldU16 t'193
    let t'195 := (t'194 + 1)
    PMem.stU16 t'193 t'195
  if (r_message != (0 : UInt64)) then
    let t'196 ← PMem.ldU64 (fp + 0)
    let t'197 ← PMem.ldU8 (t'196 + 3)
    PMem.stU8 (r_message + 3) t'197
  if (r_mavlink_status != (0 : UInt64)) then
    let t'198 ← PMem.ldU32 (status + 4)
    PMem.stU32 (r_mavlink_status + 4) t'198
    let t'199 ← PMem.ldU8 (status + 8)
    PMem.stU8 (r_mavlink_status + 8) t'199
    let t'200 ← PMem.ldU8 (status + 9)
    let t'201 := Int8.toUInt8 (Int32.toInt8 (((UInt32.toInt32 (UInt8.toUInt32 (t'200))) + (1 : Int32))))
    PMem.stU8 (r_mavlink_status + 9) t'201
    let t'202 ← PMem.ldU16 (status + 12)
    PMem.stU16 (r_mavlink_status + 12) t'202
    let t'203 ← PMem.ldU8 (status + 2)
    let t'204 := UInt8.toUInt16 (t'203)
    PMem.stU16 (r_mavlink_status + 14) t'204
    let t'205 ← PMem.ldU8 (status + 16)
    PMem.stU8 (r_mavlink_status + 16) t'205
  let t'206 := Int8.toUInt8 (Int32.toInt8 ((0 : Int32)))
  PMem.stU8 (status + 2) t'206
  let t'207 ← PMem.ldU8 status
  if ((UInt32.toInt32 (UInt8.toUInt32 (t'207))) == (UInt32.toInt32 ((2 : UInt32)))) then
    if (r_message != (0 : UInt64)) then
      let t'208 ← PMem.ldU64 (fp + 0)
      let t'209 ← PMem.ldU8 ((t'208 + 280) + ((Int32.toInt64 ((0 : Int32))) * 1).toUInt64)
      let t'210 ← PMem.ldU64 (fp + 0)
      let t'211 ← PMem.ldU8 ((t'210 + 280) + ((Int32.toInt64 ((1 : Int32))) * 1).toUInt64)
      let t'212 := Int16.toUInt16 (Int32.toInt16 (((UInt32.toInt32 (UInt8.toUInt32 (t'209))) ||| ((UInt32.toInt32 (UInt8.toUInt32 (t'211))) <<< (8 : Int32)))))
      PMem.stU16 r_message t'212
  let t'213 ← PMem.ldU8 status
  return t'213

def mavlink_frame_char_buffer (rxmsg : UInt64) (status : UInt64) (c : UInt8) (r_message : UInt64) (r_mavlink_status : UInt64) : PMem.M UInt8 := do
  let fp ← PMem.enter 8
  let r ← mavlink_frame_char_buffer.body fp rxmsg status c r_message r_mavlink_status
  PMem.leave fp
  return r

/-- C++ `mavlink_msg_get_target_sysid : uint32_t (const mavlink_message_t *, const mavlink_msg_entry_t *)`, `mavlink_helpers.h:679-692`. -/
def mavlink_msg_get_target_sysid.body (fp : UInt64) (msg : UInt64) (entry : UInt64) : PMem.M UInt32 := do
  PMem.stU64 (fp + 0) msg
  let mut entry := entry
  let t'1 ← PMem.ldU64 (fp + 0)
  let t'2 ← PMem.ldU8 (t'1 + 4)
  if ((UInt32.toInt32 (UInt8.toUInt32 (t'2))) &&& (4 : Int32)) != (0 : Int32) then
    let t'3 ← PMem.ldU64 (fp + 0)
    let t'4 ← PMem.ldU32 (t'3 + 296)
    return t'4
  let mut sc'6 := (entry == (0 : UInt64))
  if !sc'6 then
    let t'5 ← PMem.ldU8 (entry + 7)
    sc'6 := !(((UInt32.toInt32 (UInt8.toUInt32 (t'5))) &&& (1 : Int32)) != (0 : Int32))
  if sc'6 then
    return Int32.toUInt32 ((0 : Int32))
  let t'7 ← PMem.ldU8 (entry + 8)
  let t'8 ← PMem.ldU64 (fp + 0)
  let t'9 ← PMem.ldU8 (t'8 + 3)
  if (decide ((UInt32.toInt32 (UInt8.toUInt32 (t'7))) ≥ (UInt32.toInt32 (UInt8.toUInt32 (t'9))))) then
    return Int32.toUInt32 ((0 : Int32))
  let t'10 ← PMem.ldU64 (fp + 0)
  let t'11 ← PMem.ldU8 (entry + 8)
  let t'12 ← PMem.ldI8 (((t'10 + 16) + ((Int32.toInt64 ((0 : Int32))) * 8).toUInt64) + ((UInt64.toInt64 (UInt8.toUInt64 (t'11))) * 1).toUInt64)
  return UInt8.toUInt32 ((Int8.toUInt8 (t'12)))

def mavlink_msg_get_target_sysid (msg : UInt64) (entry : UInt64) : PMem.M UInt32 := do
  let fp ← PMem.enter 8
  let r ← mavlink_msg_get_target_sysid.body fp msg entry
  PMem.leave fp
  return r

/-- C++ `mavlink_msg_get_target_compid : uint8_t (const mavlink_message_t *, const mavlink_msg_entry_t *)`, `mavlink_helpers.h:698-708`. -/
def mavlink_msg_get_target_compid.body (fp : UInt64) (msg : UInt64) (entry : UInt64) : PMem.M UInt8 := do
  PMem.stU64 (fp + 0) msg
  let mut entry := entry
  let mut sc'2 := (entry == (0 : UInt64))
  if !sc'2 then
    let t'1 ← PMem.ldU8 (entry + 7)
    sc'2 := !(((UInt32.toInt32 (UInt8.toUInt32 (t'1))) &&& (2 : Int32)) != (0 : Int32))
  if sc'2 then
    return Int8.toUInt8 (Int32.toInt8 ((0 : Int32)))
  let t'3 ← PMem.ldU8 (entry + 9)
  let t'4 ← PMem.ldU64 (fp + 0)
  let t'5 ← PMem.ldU8 (t'4 + 3)
  if (decide ((UInt32.toInt32 (UInt8.toUInt32 (t'3))) ≥ (UInt32.toInt32 (UInt8.toUInt32 (t'5))))) then
    return Int8.toUInt8 (Int32.toInt8 ((0 : Int32)))
  let t'6 ← PMem.ldU64 (fp + 0)
  let t'7 ← PMem.ldU8 (entry + 9)
  let t'8 ← PMem.ldI8 (((t'6 + 16) + ((Int32.toInt64 ((0 : Int32))) * 8).toUInt64) + ((UInt64.toInt64 (UInt8.toUInt64 (t'7))) * 1).toUInt64)
  return Int8.toUInt8 (t'8)

def mavlink_msg_get_target_compid (msg : UInt64) (entry : UInt64) : PMem.M UInt8 := do
  let fp ← PMem.enter 8
  let r ← mavlink_msg_get_target_compid.body fp msg entry
  PMem.leave fp
  return r

/-- C++ `mavlink_header_to_send_buffer : uint8_t (uint8_t *, const mavlink_message_t *)`, `mavlink_helpers.h:177-183`. -/
def mavlink_header_to_send_buffer (buf : UInt64) (msg : UInt64) : PMem.M UInt8 := do
  let mut buf := buf
  let mut msg := msg
  let t'1 ← PMem.ldU8 (msg + 2)
  let t'2 ← PMem.ldU8 (msg + 3)
  let t'3 ← PMem.ldU8 (msg + 4)
  let t'4 ← PMem.ldU8 (msg + 5)
  let t'5 ← PMem.ldU8 (msg + 6)
  let t'6 ← PMem.ldU32 (msg + 8)
  let t'7 ← PMem.ldU8 (msg + 12)
  let t'8 ← PMem.ldBits msg 104 24
  let t'9 ← PMem.ldU32 (msg + 296)
  let t'10 ← _mav_header_pack buf t'1 t'2 t'3 t'4 t'5 t'6 t'7 (UInt64.toUInt32 (t'8)) t'9
  return t'10

/-- C++ `_mavlink_resend_uart : void (mavlink_channel_t, const mavlink_message_t *)`, `mavlink_helpers.h:489-519`. -/
def _mavlink_resend_uart.body (fp : UInt64) (chan : UInt32) (msg : UInt64) : PMem.M Unit := do
  let mut chan := chan
  PMem.stU64 (fp + 0) msg
  let t'1 ← PMem.ldU64 (fp + 0)
  let t'2 ← PMem.ldU16 t'1
  let t'3 := Int8.toUInt8 (Int32.toInt8 (((UInt32.toInt32 (UInt16.toUInt32 (t'2))) &&& (255 : Int32))))
  PMem.stU8 ((fp + 8) + ((Int32.toInt64 ((0 : Int32))) * 1).toUInt64) t'3
  let t'4 ← PMem.ldU64 (fp + 0)
  let t'5 ← PMem.ldU16 t'4
  let t'6 := Int8.toUInt8 (Int32.toInt8 (((UInt32.toInt32 (UInt16.toUInt32 (t'5))) >>> (8 : Int32))))
  PMem.stU8 ((fp + 8) + ((Int32.toInt64 ((1 : Int32))) * 1).toUInt64) t'6
  let t'7 ← PMem.ldU64 (fp + 0)
  let t'8 ← mavlink_header_to_send_buffer (fp + 16) t'7
  let mut header_len : UInt8 := t'8
  if ((UInt32.toInt32 (UInt8.toUInt32 (header_len))) == (0 : Int32)) then
    return ()
  let mut signature_len : UInt8 := default  -- uninitialized in C
  let t'9 ← PMem.ldU64 (fp + 0)
  let t'10 ← PMem.ldU8 (t'9 + 2)
  if ((UInt32.toInt32 (UInt8.toUInt32 (t'10))) == (254 : Int32)) then
    let t'11 := Int8.toUInt8 (Int32.toInt8 ((0 : Int32)))
    signature_len := t'11
  else
    let t'12 ← PMem.ldU64 (fp + 0)
    let t'13 ← PMem.ldU8 (t'12 + 4)
    let mut c'14 : Int32 := default
    if ((UInt32.toInt32 (UInt8.toUInt32 (t'13))) &&& (1 : Int32)) != (0 : Int32) then
      c'14 := (13 : Int32)
    else
      c'14 := (0 : Int32)
    let t'15 := Int8.toUInt8 (Int32.toInt8 (c'14))
    signature_len := t'15
  let t'16 ← PMem.ldU64 (fp + 0)
  let t'17 ← PMem.ldU8 (t'16 + 3)
  comm_send_lock chan (Int16.toUInt16 (Int32.toInt16 (((((UInt32.toInt32 (UInt8.toUInt32 (header_len))) + (UInt32.toInt32 (UInt8.toUInt32 (t'17)))) + (2 : Int32)) + (UInt32.toInt32 (UInt8.toUInt32 (signature_len)))))))
  _mavlink_send_uart chan (fp + 16) (UInt8.toUInt16 (header_len))
  let t'18 ← PMem.ldU64 (fp + 0)
  let t'19 ← PMem.ldU64 (fp + 0)
  let t'20 ← PMem.ldU8 (t'19 + 3)
  _mavlink_send_uart chan ((t'18 + 16) + ((Int32.toInt64 ((0 : Int32))) * 8).toUInt64) (UInt8.toUInt16 (t'20))
  _mavlink_send_uart chan (fp + 8) (Int16.toUInt16 (Int32.toInt16 ((2 : Int32))))
  if ((UInt32.toInt32 (UInt8.toUInt32 (signature_len))) != (0 : Int32)) then
    let t'21 ← PMem.ldU64 (fp + 0)
    _mavlink_send_uart chan (t'21 + 282) (Int16.toUInt16 (Int32.toInt16 ((13 : Int32))))
  comm_send_unlock chan
  return ()

def _mavlink_resend_uart (chan : UInt32) (msg : UInt64) : PMem.M Unit := do
  let fp ← PMem.enter 33
  let r ← _mavlink_resend_uart.body fp chan msg
  PMem.leave fp
  return r

/-- C++ `mavlink_msg_heartbeat_get_type : uint8_t (const mavlink_message_t *)`, `mavlink_msg_heartbeat.h:323-326`. -/
def mavlink_msg_heartbeat_get_type.body (fp : UInt64) (msg : UInt64) : PMem.M UInt8 := do
  PMem.stU64 (fp + 0) msg
  let t'1 ← PMem.ldU64 (fp + 0)
  let t'2 ← PMem.ldI8 (((t'1 + 16) + ((Int32.toInt64 ((0 : Int32))) * 8).toUInt64) + ((Int32.toInt64 ((4 : Int32))) * 1).toUInt64)
  return Int8.toUInt8 (t'2)

def mavlink_msg_heartbeat_get_type (msg : UInt64) : PMem.M UInt8 := do
  let fp ← PMem.enter 8
  let r ← mavlink_msg_heartbeat_get_type.body fp msg
  PMem.leave fp
  return r

/-- `__mavlink_set_attitude_target_t.__mavlink_set_attitude_target_t` as a pure function of its arguments (it reads and writes no memory). -/
def __mavlink_set_attitude_target_t.__mavlink_set_attitude_target_t.pure' (this : UInt64) : Id Unit := do
  return ()

/-- C++ `__mavlink_set_attitude_target_t::__mavlink_set_attitude_target_t : void () noexcept`, `mavlink_msg_set_attitude_target.h:9-?`. -/
def __mavlink_set_attitude_target_t.__mavlink_set_attitude_target_t (this : UInt64) : PMem.M Unit :=
  pure (_root_.Vehicle_lib.__mavlink_set_attitude_target_t.__mavlink_set_attitude_target_t.pure' this)

/-- C++ `mavlink_msg_decode_target : void (const mavlink_message_t *, void *, uint8_t, uint8_t)`, `mavlink_helpers.h:644-652`. -/
def mavlink_msg_decode_target.body (fp : UInt64) (msg : UInt64) (payload : UInt64) (length : UInt8) (target_system_ofs : UInt8) : PMem.M Unit := do
  PMem.stU64 (fp + 0) msg
  let mut payload := payload
  PMem.stU8 (fp + 8) length
  let mut target_system_ofs := target_system_ofs
  let t'1 ← PMem.ldU64 (fp + 0)
  let t'2 ← PMem.ldU8 (t'1 + 3)
  let t'3 ← PMem.ldU8 (fp + 8)
  let mut c'4 : UInt8 := default
  if (decide ((UInt32.toInt32 (UInt8.toUInt32 (t'2))) < (UInt32.toInt32 (UInt8.toUInt32 (t'3))))) then
    let t'5 ← PMem.ldU64 (fp + 0)
    let t'6 ← PMem.ldU8 (t'5 + 3)
    c'4 := t'6
  else
    let t'7 ← PMem.ldU8 (fp + 8)
    c'4 := t'7
  let mut len : UInt8 := c'4
  let t'8 ← PMem.ldU8 (fp + 8)
  let t'9 ← PMem.memset payload (0 : Int32) (UInt8.toUInt64 (t'8))
  discard <| pure (t'9)
  let t'10 ← PMem.ldU64 (fp + 0)
  let t'11 ← PMem.memcpy payload ((t'10 + 16) + ((Int32.toInt64 ((0 : Int32))) * 8).toUInt64) (UInt8.toUInt64 (len))
  discard <| pure (t'11)
  let t'12 ← PMem.ldU64 (fp + 0)
  let t'13 ← PMem.ldU8 (t'12 + 4)
  if ((UInt32.toInt32 (UInt8.toUInt32 (t'13))) &&& (4 : Int32)) != (0 : Int32) then
    let t'14 ← PMem.ldU64 (fp + 0)
    let t'15 ← PMem.ldU32 (t'14 + 296)
    let mut c'16 : Int32 := default
    if (decide (t'15 > (Int32.toUInt32 ((255 : Int32))))) then
      c'16 := (255 : Int32)
    else
      let t'17 ← PMem.ldU64 (fp + 0)
      let t'18 ← PMem.ldU32 (t'17 + 296)
      c'16 := UInt32.toInt32 (UInt8.toUInt32 ((UInt32.toUInt8 (t'18))))
    let t'19 := Int8.toUInt8 (Int32.toInt8 (c'16))
    PMem.stU8 (payload + ((UInt64.toInt64 (UInt8.toUInt64 (target_system_ofs))) * 1).toUInt64) t'19
  return ()

def mavlink_msg_decode_target (msg : UInt64) (payload : UInt64) (length : UInt8) (target_system_ofs : UInt8) : PMem.M Unit := do
  let fp ← PMem.enter 9
  let r ← mavlink_msg_decode_target.body fp msg payload length target_system_ofs
  PMem.leave fp
  return r

/-- C++ `mavlink_msg_set_attitude_target_decode : void (const mavlink_message_t *, mavlink_set_attitude_target_t *)`, `mavlink_msg_set_attitude_target.h:449-471`. -/
def mavlink_msg_set_attitude_target_decode (msg : UInt64) (set_attitude_target : UInt64) : PMem.M Unit := do
  let mut msg := msg
  let mut set_attitude_target := set_attitude_target
  mavlink_msg_decode_target msg set_attitude_target (Int8.toUInt8 (Int32.toInt8 ((39 : Int32)))) (Int8.toUInt8 (Int32.toInt8 ((36 : Int32))))
  return ()

/-- `__mavlink_set_position_target_local_ned_t.__mavlink_set_position_target_local_ned_t` as a pure function of its arguments (it reads and writes no memory). -/
def __mavlink_set_position_target_local_ned_t.__mavlink_set_position_target_local_ned_t.pure' (this : UInt64) : Id Unit := do
  return ()

/-- C++ `__mavlink_set_position_target_local_ned_t::__mavlink_set_position_target_local_ned_t : void () noexcept`, `mavlink_msg_set_position_target_local_ned.h:9-?`. -/
def __mavlink_set_position_target_local_ned_t.__mavlink_set_position_target_local_ned_t (this : UInt64) : PMem.M Unit :=
  pure (_root_.Vehicle_lib.__mavlink_set_position_target_local_ned_t.__mavlink_set_position_target_local_ned_t.pure' this)

/-- C++ `mavlink_msg_set_position_target_local_ned_decode : void (const mavlink_message_t *, mavlink_set_position_target_local_ned_t *)`, `mavlink_msg_set_position_target_local_ned.h:648-677`. -/
def mavlink_msg_set_position_target_local_ned_decode (msg : UInt64) (set_position_target_local_ned : UInt64) : PMem.M Unit := do
  let mut msg := msg
  let mut set_position_target_local_ned := set_position_target_local_ned
  mavlink_msg_decode_target msg set_position_target_local_ned (Int8.toUInt8 (Int32.toInt8 ((53 : Int32)))) (Int8.toUInt8 (Int32.toInt8 ((50 : Int32))))
  return ()

/-- `__mavlink_set_position_target_global_int_t.__mavlink_set_position_target_global_int_t` as a pure function of its arguments (it reads and writes no memory). -/
def __mavlink_set_position_target_global_int_t.__mavlink_set_position_target_global_int_t.pure' (this : UInt64) : Id Unit := do
  return ()

/-- C++ `__mavlink_set_position_target_global_int_t::__mavlink_set_position_target_global_int_t : void () noexcept`, `mavlink_msg_set_position_target_global_int.h:9-?`. -/
def __mavlink_set_position_target_global_int_t.__mavlink_set_position_target_global_int_t (this : UInt64) : PMem.M Unit :=
  pure (_root_.Vehicle_lib.__mavlink_set_position_target_global_int_t.__mavlink_set_position_target_global_int_t.pure' this)

/-- C++ `mavlink_msg_set_position_target_global_int_decode : void (const mavlink_message_t *, mavlink_set_position_target_global_int_t *)`, `mavlink_msg_set_position_target_global_int.h:648-677`. -/
def mavlink_msg_set_position_target_global_int_decode (msg : UInt64) (set_position_target_global_int : UInt64) : PMem.M Unit := do
  let mut msg := msg
  let mut set_position_target_global_int := set_position_target_global_int
  mavlink_msg_decode_target msg set_position_target_global_int (Int8.toUInt8 (Int32.toInt8 ((53 : Int32)))) (Int8.toUInt8 (Int32.toInt8 ((50 : Int32))))
  return ()

/-- `__mavlink_statustext_t.__mavlink_statustext_t` as a pure function of its arguments (it reads and writes no memory). -/
def __mavlink_statustext_t.__mavlink_statustext_t.pure' (this : UInt64) : Id Unit := do
  return ()

/-- C++ `__mavlink_statustext_t::__mavlink_statustext_t : void () noexcept`, `mavlink_types.h:?-?`. -/
def __mavlink_statustext_t.__mavlink_statustext_t (this : UInt64) : PMem.M Unit :=
  pure (_root_.Vehicle_lib.__mavlink_statustext_t.__mavlink_statustext_t.pure' this)

/-- C++ `mav_array_memcpy : void (void *, const void *, size_t)`, `protocol.h:220-234`. -/
def mav_array_memcpy (dest : UInt64) (src : UInt64) (n : UInt64) : PMem.M Unit := do
  let mut dest := dest
  let mut src := src
  let mut n := n
  if (src == (0 : UInt64)) then
    let t'1 ← PMem.memset dest (0 : Int32) n
    discard <| pure (t'1)
  else
    let t'2 ← PMem.memcpy dest src n
    discard <| pure (t'2)
  return ()

/-- C++ `mavlink_msg_statustext_send : void (mavlink_channel_t, uint8_t, const char *, uint16_t, uint8_t)`, `mavlink_msg_statustext.h:212-229`. -/
def mavlink_msg_statustext_send.body (fp : UInt64) (chan : UInt32) (severity : UInt8) (text : UInt64) (id : UInt16) (chunk_seq : UInt8) : PMem.M Unit := do
  let mut chan := chan
  let mut severity := severity
  let mut text := text
  let mut id := id
  let mut chunk_seq := chunk_seq
  __mavlink_statustext_t.__mavlink_statustext_t (fp + 0)
  PMem.stU8 (fp + 0) severity
  PMem.stU16 ((fp + 0) + 51) id
  PMem.stU8 ((fp + 0) + 53) chunk_seq
  mav_array_memcpy ((fp + 0) + 1) text ((1 : UInt64) * (Int64.toUInt64 (Int32.toInt64 ((50 : Int32)))))
  _mav_finalize_message_chan_send chan (Int32.toUInt32 ((253 : Int32))) (fp + 0) (Int8.toUInt8 (Int32.toInt8 ((51 : Int32)))) (Int8.toUInt8 (Int32.toInt8 ((54 : Int32)))) (Int8.toUInt8 (Int32.toInt8 ((83 : Int32))))
  return ()

def mavlink_msg_statustext_send (chan : UInt32) (severity : UInt8) (text : UInt64) (id : UInt16) (chunk_seq : UInt8) : PMem.M Unit := do
  let fp ← PMem.enter 54
  let r ← mavlink_msg_statustext_send.body fp chan severity text id chunk_seq
  PMem.leave fp
  return r

/-- `__mavlink_param_request_list_t.__mavlink_param_request_list_t` as a pure function of its arguments (it reads and writes no memory). -/
def __mavlink_param_request_list_t.__mavlink_param_request_list_t.pure' (this : UInt64) : Id Unit := do
  return ()

/-- C++ `__mavlink_param_request_list_t::__mavlink_param_request_list_t : void () noexcept`, `mavlink_msg_param_request_list.h:9-?`. -/
def __mavlink_param_request_list_t.__mavlink_param_request_list_t (this : UInt64) : PMem.M Unit :=
  pure (_root_.Vehicle_lib.__mavlink_param_request_list_t.__mavlink_param_request_list_t.pure' this)

/-- C++ `mavlink_msg_param_request_list_decode : void (const mavlink_message_t *, mavlink_param_request_list_t *)`, `mavlink_msg_param_request_list.h:270-285`. -/
def mavlink_msg_param_request_list_decode (msg : UInt64) (param_request_list : UInt64) : PMem.M Unit := do
  let mut msg := msg
  let mut param_request_list := param_request_list
  mavlink_msg_decode_target msg param_request_list (Int8.toUInt8 (Int32.toInt8 ((2 : Int32)))) (Int8.toUInt8 (Int32.toInt8 ((0 : Int32))))
  return ()

/-- C++ `mavlink_msg_ekf_status_report_send_struct : void (mavlink_channel_t, const mavlink_ekf_status_report_t *)`, `mavlink_msg_ekf_status_report.h:289-296`. -/
def mavlink_msg_ekf_status_report_send_struct (chan : UInt32) (ekf_status_report : UInt64) : PMem.M Unit := do
  let mut chan := chan
  let mut ekf_status_report := ekf_status_report
  _mav_finalize_message_chan_send chan (Int32.toUInt32 ((193 : Int32))) ekf_status_report (Int8.toUInt8 (Int32.toInt8 ((22 : Int32)))) (Int8.toUInt8 (Int32.toInt8 ((26 : Int32)))) (Int8.toUInt8 (Int32.toInt8 ((71 : Int32))))
  return ()

/-- `__mavlink_gps_raw_int_t.__mavlink_gps_raw_int_t` as a pure function of its arguments (it reads and writes no memory). -/
def __mavlink_gps_raw_int_t.__mavlink_gps_raw_int_t.pure' (this : UInt64) : Id Unit := do
  return ()

/-- C++ `__mavlink_gps_raw_int_t::__mavlink_gps_raw_int_t : void () noexcept`, `mavlink_types.h:?-?`. -/
def __mavlink_gps_raw_int_t.__mavlink_gps_raw_int_t (this : UInt64) : PMem.M Unit :=
  pure (_root_.Vehicle_lib.__mavlink_gps_raw_int_t.__mavlink_gps_raw_int_t.pure' this)

/-- C++ `mavlink_msg_gps_raw_int_send : void (mavlink_channel_t, uint64_t, uint8_t, int32_t, int32_t, int32_t, uint16_t, uint16_t, uint16_t, uint16_t, uint8_t, int32_t, uint32_t, uint32_t, uint32_t, uint32_t, uint16_t)`, `mavlink_msg_gps_raw_int.h:374-417`. -/
def mavlink_msg_gps_raw_int_send.body (fp : UInt64) (chan : UInt32) (time_usec : UInt64) (fix_type : UInt8) (lat : Int32) (lon : Int32) (alt : Int32) (eph : UInt16) (epv : UInt16) (vel : UInt16) (cog : UInt16) (satellites_visible : UInt8) (alt_ellipsoid : Int32) (h_acc : UInt32) (v_acc : UInt32) (vel_acc : UInt32) (hdg_acc : UInt32) (yaw : UInt16) : PMem.M Unit := do
  let mut chan := chan
  let mut time_usec := time_usec
  let mut fix_type := fix_type
  let mut lat := lat
  let mut lon := lon
  let mut alt := alt
  let mut eph := eph
  let mut epv := epv
  let mut vel := vel
  let mut cog := cog
  let mut satellites_visible := satellites_visible
  let mut alt_ellipsoid := alt_ellipsoid
  let mut h_acc := h_acc
  let mut v_acc := v_acc
  let mut vel_acc := vel_acc
  let mut hdg_acc := hdg_acc
  let mut yaw := yaw
  __mavlink_gps_raw_int_t.__mavlink_gps_raw_int_t (fp + 0)
  PMem.stU64 (fp + 0) time_usec
  PMem.stI32 ((fp + 0) + 8) lat
  PMem.stI32 ((fp + 0) + 12) lon
  PMem.stI32 ((fp + 0) + 16) alt
  PMem.stU16 ((fp + 0) + 20) eph
  PMem.stU16 ((fp + 0) + 22) epv
  PMem.stU16 ((fp + 0) + 24) vel
  PMem.stU16 ((fp + 0) + 26) cog
  PMem.stU8 ((fp + 0) + 28) fix_type
  PMem.stU8 ((fp + 0) + 29) satellites_visible
  PMem.stI32 ((fp + 0) + 30) alt_ellipsoid
  PMem.stU32 ((fp + 0) + 34) h_acc
  PMem.stU32 ((fp + 0) + 38) v_acc
  PMem.stU32 ((fp + 0) + 42) vel_acc
  PMem.stU32 ((fp + 0) + 46) hdg_acc
  PMem.stU16 ((fp + 0) + 50) yaw
  _mav_finalize_message_chan_send chan (Int32.toUInt32 ((24 : Int32))) (fp + 0) (Int8.toUInt8 (Int32.toInt8 ((30 : Int32)))) (Int8.toUInt8 (Int32.toInt8 ((52 : Int32)))) (Int8.toUInt8 (Int32.toInt8 ((24 : Int32))))
  return ()

def mavlink_msg_gps_raw_int_send (chan : UInt32) (time_usec : UInt64) (fix_type : UInt8) (lat : Int32) (lon : Int32) (alt : Int32) (eph : UInt16) (epv : UInt16) (vel : UInt16) (cog : UInt16) (satellites_visible : UInt8) (alt_ellipsoid : Int32) (h_acc : UInt32) (v_acc : UInt32) (vel_acc : UInt32) (hdg_acc : UInt32) (yaw : UInt16) : PMem.M Unit := do
  let fp ← PMem.enter 52
  let r ← mavlink_msg_gps_raw_int_send.body fp chan time_usec fix_type lat lon alt eph epv vel cog satellites_visible alt_ellipsoid h_acc v_acc vel_acc hdg_acc yaw
  PMem.leave fp
  return r

/-- `__mavlink_gps2_raw_t.__mavlink_gps2_raw_t` as a pure function of its arguments (it reads and writes no memory). -/
def __mavlink_gps2_raw_t.__mavlink_gps2_raw_t.pure' (this : UInt64) : Id Unit := do
  return ()

/-- C++ `__mavlink_gps2_raw_t::__mavlink_gps2_raw_t : void () noexcept`, `mavlink_types.h:?-?`. -/
def __mavlink_gps2_raw_t.__mavlink_gps2_raw_t (this : UInt64) : PMem.M Unit :=
  pure (_root_.Vehicle_lib.__mavlink_gps2_raw_t.__mavlink_gps2_raw_t.pure' this)

/-- C++ `mavlink_msg_gps2_raw_send : void (mavlink_channel_t, uint64_t, uint8_t, int32_t, int32_t, int32_t, uint16_t, uint16_t, uint16_t, uint16_t, uint8_t, uint8_t, uint32_t, uint16_t, int32_t, uint32_t, uint32_t, uint32_t, uint32_t)`, `mavlink_msg_gps2_raw.h:400-447`. -/
def mavlink_msg_gps2_raw_send.body (fp : UInt64) (chan : UInt32) (time_usec : UInt64) (fix_type : UInt8) (lat : Int32) (lon : Int32) (alt : Int32) (eph : UInt16) (epv : UInt16) (vel : UInt16) (cog : UInt16) (satellites_visible : UInt8) (dgps_numch : UInt8) (dgps_age : UInt32) (yaw : UInt16) (alt_ellipsoid : Int32) (h_acc : UInt32) (v_acc : UInt32) (vel_acc : UInt32) (hdg_acc : UInt32) : PMem.M Unit := do
  let mut chan := chan
  let mut time_usec := time_usec
  let mut fix_type := fix_type
  let mut lat := lat
  let mut lon := lon
  let mut alt := alt
  let mut eph := eph
  let mut epv := epv
  let mut vel := vel
  let mut cog := cog
  let mut satellites_visible := satellites_visible
  let mut dgps_numch := dgps_numch
  let mut dgps_age := dgps_age
  let mut yaw := yaw
  let mut alt_ellipsoid := alt_ellipsoid
  let mut h_acc := h_acc
  let mut v_acc := v_acc
  let mut vel_acc := vel_acc
  let mut hdg_acc := hdg_acc
  __mavlink_gps2_raw_t.__mavlink_gps2_raw_t (fp + 0)
  PMem.stU64 (fp + 0) time_usec
  PMem.stI32 ((fp + 0) + 8) lat
  PMem.stI32 ((fp + 0) + 12) lon
  PMem.stI32 ((fp + 0) + 16) alt
  PMem.stU32 ((fp + 0) + 20) dgps_age
  PMem.stU16 ((fp + 0) + 24) eph
  PMem.stU16 ((fp + 0) + 26) epv
  PMem.stU16 ((fp + 0) + 28) vel
  PMem.stU16 ((fp + 0) + 30) cog
  PMem.stU8 ((fp + 0) + 32) fix_type
  PMem.stU8 ((fp + 0) + 33) satellites_visible
  PMem.stU8 ((fp + 0) + 34) dgps_numch
  PMem.stU16 ((fp + 0) + 35) yaw
  PMem.stI32 ((fp + 0) + 37) alt_ellipsoid
  PMem.stU32 ((fp + 0) + 41) h_acc
  PMem.stU32 ((fp + 0) + 45) v_acc
  PMem.stU32 ((fp + 0) + 49) vel_acc
  PMem.stU32 ((fp + 0) + 53) hdg_acc
  _mav_finalize_message_chan_send chan (Int32.toUInt32 ((124 : Int32))) (fp + 0) (Int8.toUInt8 (Int32.toInt8 ((35 : Int32)))) (Int8.toUInt8 (Int32.toInt8 ((57 : Int32)))) (Int8.toUInt8 (Int32.toInt8 ((87 : Int32))))
  return ()

def mavlink_msg_gps2_raw_send (chan : UInt32) (time_usec : UInt64) (fix_type : UInt8) (lat : Int32) (lon : Int32) (alt : Int32) (eph : UInt16) (epv : UInt16) (vel : UInt16) (cog : UInt16) (satellites_visible : UInt8) (dgps_numch : UInt8) (dgps_age : UInt32) (yaw : UInt16) (alt_ellipsoid : Int32) (h_acc : UInt32) (v_acc : UInt32) (vel_acc : UInt32) (hdg_acc : UInt32) : PMem.M Unit := do
  let fp ← PMem.enter 57
  let r ← mavlink_msg_gps2_raw_send.body fp chan time_usec fix_type lat lon alt eph epv vel cog satellites_visible dgps_numch dgps_age yaw alt_ellipsoid h_acc v_acc vel_acc hdg_acc
  PMem.leave fp
  return r

/-- `__mavlink_param_set_t.__mavlink_param_set_t` as a pure function of its arguments (it reads and writes no memory). -/
def __mavlink_param_set_t.__mavlink_param_set_t.pure' (this : UInt64) : Id Unit := do
  return ()

/-- C++ `__mavlink_param_set_t::__mavlink_param_set_t : void () noexcept`, `mavlink_msg_param_set.h:9-?`. -/
def __mavlink_param_set_t.__mavlink_param_set_t (this : UInt64) : PMem.M Unit :=
  pure (_root_.Vehicle_lib.__mavlink_param_set_t.__mavlink_param_set_t.pure' this)

/-- C++ `mavlink_msg_param_set_decode : void (const mavlink_message_t *, mavlink_param_set_t *)`, `mavlink_msg_param_set.h:341-359`. -/
def mavlink_msg_param_set_decode (msg : UInt64) (param_set : UInt64) : PMem.M Unit := do
  let mut msg := msg
  let mut param_set := param_set
  mavlink_msg_decode_target msg param_set (Int8.toUInt8 (Int32.toInt8 ((23 : Int32)))) (Int8.toUInt8 (Int32.toInt8 ((4 : Int32))))
  return ()

/-- `mavlink_msg_target_field` as a pure function of its arguments (it reads and writes no memory). -/
def mavlink_msg_target_field.pure' (target_system : UInt32) : Id UInt8 := do
  let mut target_system := target_system
  let mut c'1 : Int32 := default
  if (decide (target_system > (Int32.toUInt32 ((255 : Int32))))) then
    c'1 := (255 : Int32)
  else
    c'1 := UInt32.toInt32 (UInt8.toUInt32 ((UInt32.toUInt8 (target_system))))
  return Int8.toUInt8 (Int32.toInt8 (c'1))

/-- C++ `mavlink_msg_target_field : uint8_t (uint32_t)`, `protocol.h:52-55`. -/
def mavlink_msg_target_field (target_system : UInt32) : PMem.M UInt8 :=
  pure (_root_.Vehicle_lib.mavlink_msg_target_field.pure' target_system)

/-- `__mavlink_param_error_t.__mavlink_param_error_t` as a pure function of its arguments (it reads and writes no memory). -/
def __mavlink_param_error_t.__mavlink_param_error_t.pure' (this : UInt64) : Id Unit := do
  return ()

/-- C++ `__mavlink_param_error_t::__mavlink_param_error_t : void () noexcept`, `mavlink_msg_param_error.h:9-?`. -/
def __mavlink_param_error_t.__mavlink_param_error_t (this : UInt64) : PMem.M Unit :=
  pure (_root_.Vehicle_lib.__mavlink_param_error_t.__mavlink_param_error_t.pure' this)

/-- C++ `mavlink_msg_param_error_send : void (mavlink_channel_t, uint32_t, uint8_t, const char *, int16_t, uint8_t)`, `mavlink_msg_param_error.h:230-249`. -/
def mavlink_msg_param_error_send.body (fp : UInt64) (chan : UInt32) (target_system : UInt32) (target_component : UInt8) (param_id : UInt64) (param_index : Int16) (error : UInt8) : PMem.M Unit := do
  let mut chan := chan
  let mut target_system := target_system
  let mut target_component := target_component
  let mut param_id := param_id
  let mut param_index := param_index
  let mut error := error
  __mavlink_param_error_t.__mavlink_param_error_t (fp + 0)
  PMem.stI16 (fp + 0) param_index
  let t'1 ← mavlink_msg_target_field target_system
  PMem.stU8 ((fp + 0) + 2) t'1
  PMem.stU8 ((fp + 0) + 3) target_component
  PMem.stU8 ((fp + 0) + 20) error
  mav_array_memcpy ((fp + 0) + 4) param_id ((1 : UInt64) * (Int64.toUInt64 (Int32.toInt64 ((16 : Int32)))))
  _mav_finalize_message_chan_send_target chan (Int32.toUInt32 ((345 : Int32))) (fp + 0) (Int8.toUInt8 (Int32.toInt8 ((21 : Int32)))) (Int8.toUInt8 (Int32.toInt8 ((21 : Int32)))) (Int8.toUInt8 (Int32.toInt8 ((209 : Int32)))) target_system
  return ()

def mavlink_msg_param_error_send (chan : UInt32) (target_system : UInt32) (target_component : UInt8) (param_id : UInt64) (param_index : Int16) (error : UInt8) : PMem.M Unit := do
  let fp ← PMem.enter 21
  let r ← mavlink_msg_param_error_send.body fp chan target_system target_component param_id param_index error
  PMem.leave fp
  return r

/-- `__mavlink_param_value_t.__mavlink_param_value_t` as a pure function of its arguments (it reads and writes no memory). -/
def __mavlink_param_value_t.__mavlink_param_value_t.pure' (this : UInt64) : Id Unit := do
  return ()

/-- C++ `__mavlink_param_value_t::__mavlink_param_value_t : void () noexcept`, `mavlink_msg_param_value.h:9-?`. -/
def __mavlink_param_value_t.__mavlink_param_value_t (this : UInt64) : PMem.M Unit :=
  pure (_root_.Vehicle_lib.__mavlink_param_value_t.__mavlink_param_value_t.pure' this)

/-- C++ `mavlink_msg_param_value_send : void (mavlink_channel_t, const char *, float, uint8_t, uint16_t, uint16_t)`, `mavlink_msg_param_value.h:225-244`. -/
def mavlink_msg_param_value_send.body (fp : UInt64) (chan : UInt32) (param_id : UInt64) (param_value : Binary32) (param_type : UInt8) (param_count : UInt16) (param_index : UInt16) : PMem.M Unit := do
  let mut chan := chan
  let mut param_id := param_id
  let mut param_value := param_value
  let mut param_type := param_type
  let mut param_count := param_count
  let mut param_index := param_index
  __mavlink_param_value_t.__mavlink_param_value_t (fp + 0)
  PMem.stF32 (fp + 0) param_value
  PMem.stU16 ((fp + 0) + 4) param_count
  PMem.stU16 ((fp + 0) + 6) param_index
  PMem.stU8 ((fp + 0) + 24) param_type
  mav_array_memcpy ((fp + 0) + 8) param_id ((1 : UInt64) * (Int64.toUInt64 (Int32.toInt64 ((16 : Int32)))))
  _mav_finalize_message_chan_send chan (Int32.toUInt32 ((22 : Int32))) (fp + 0) (Int8.toUInt8 (Int32.toInt8 ((25 : Int32)))) (Int8.toUInt8 (Int32.toInt8 ((25 : Int32)))) (Int8.toUInt8 (Int32.toInt8 ((220 : Int32))))
  return ()

def mavlink_msg_param_value_send (chan : UInt32) (param_id : UInt64) (param_value : Binary32) (param_type : UInt8) (param_count : UInt16) (param_index : UInt16) : PMem.M Unit := do
  let fp ← PMem.enter 25
  let r ← mavlink_msg_param_value_send.body fp chan param_id param_value param_type param_count param_index
  PMem.leave fp
  return r

/-- `__mavlink_param_request_read_t.__mavlink_param_request_read_t` as a pure function of its arguments (it reads and writes no memory). -/
def __mavlink_param_request_read_t.__mavlink_param_request_read_t.pure' (this : UInt64) : Id Unit := do
  return ()

/-- C++ `__mavlink_param_request_read_t::__mavlink_param_request_read_t : void () noexcept`, `mavlink_msg_param_request_read.h:9-?`. -/
def __mavlink_param_request_read_t.__mavlink_param_request_read_t (this : UInt64) : PMem.M Unit :=
  pure (_root_.Vehicle_lib.__mavlink_param_request_read_t.__mavlink_param_request_read_t.pure' this)

/-- C++ `mavlink_msg_param_request_read_decode : void (const mavlink_message_t *, mavlink_param_request_read_t *)`, `mavlink_msg_param_request_read.h:314-331`. -/
def mavlink_msg_param_request_read_decode (msg : UInt64) (param_request_read : UInt64) : PMem.M Unit := do
  let mut msg := msg
  let mut param_request_read := param_request_read
  mavlink_msg_decode_target msg param_request_read (Int8.toUInt8 (Int32.toInt8 ((20 : Int32)))) (Int8.toUInt8 (Int32.toInt8 ((2 : Int32))))
  return ()

/-- `__mavlink_timesync_t.__mavlink_timesync_t` as a pure function of its arguments (it reads and writes no memory). -/
def __mavlink_timesync_t.__mavlink_timesync_t.pure' (this : UInt64) : Id Unit := do
  return ()

/-- C++ `__mavlink_timesync_t::__mavlink_timesync_t : void () noexcept`, `mavlink_msg_timesync.h:9-?`. -/
def __mavlink_timesync_t.__mavlink_timesync_t (this : UInt64) : PMem.M Unit :=
  pure (_root_.Vehicle_lib.__mavlink_timesync_t.__mavlink_timesync_t.pure' this)

/-- C++ `mavlink_msg_timesync_send : void (mavlink_channel_t, int64_t, int64_t)`, `mavlink_msg_timesync.h:192-207`. -/
def mavlink_msg_timesync_send.body (fp : UInt64) (chan : UInt32) (tc1 : Int64) (ts1 : Int64) : PMem.M Unit := do
  let mut chan := chan
  let mut tc1 := tc1
  let mut ts1 := ts1
  __mavlink_timesync_t.__mavlink_timesync_t (fp + 0)
  PMem.stI64 (fp + 0) tc1
  PMem.stI64 ((fp + 0) + 8) ts1
  _mav_finalize_message_chan_send chan (Int32.toUInt32 ((111 : Int32))) (fp + 0) (Int8.toUInt8 (Int32.toInt8 ((16 : Int32)))) (Int8.toUInt8 (Int32.toInt8 ((16 : Int32)))) (Int8.toUInt8 (Int32.toInt8 ((34 : Int32))))
  return ()

def mavlink_msg_timesync_send (chan : UInt32) (tc1 : Int64) (ts1 : Int64) : PMem.M Unit := do
  let fp ← PMem.enter 16
  let r ← mavlink_msg_timesync_send.body fp chan tc1 ts1
  PMem.leave fp
  return r

/-- C++ `mavlink_msg_timesync_decode : void (const mavlink_message_t *, mavlink_timesync_t *)`, `mavlink_msg_timesync.h:280-291`. -/
def mavlink_msg_timesync_decode.body (fp : UInt64) (msg : UInt64) (timesync : UInt64) : PMem.M Unit := do
  PMem.stU64 (fp + 0) msg
  let mut timesync := timesync
  let t'1 ← PMem.ldU64 (fp + 0)
  let t'2 ← PMem.ldU8 (t'1 + 3)
  let mut c'3 : Int32 := default
  if (decide ((UInt32.toInt32 (UInt8.toUInt32 (t'2))) < (16 : Int32))) then
    let t'4 ← PMem.ldU64 (fp + 0)
    let t'5 ← PMem.ldU8 (t'4 + 3)
    c'3 := UInt32.toInt32 (UInt8.toUInt32 (t'5))
  else
    c'3 := (16 : Int32)
  let mut len : UInt8 := Int8.toUInt8 (Int32.toInt8 (c'3))
  let t'6 ← PMem.memset timesync (0 : Int32) (Int64.toUInt64 (Int32.toInt64 ((16 : Int32))))
  discard <| pure (t'6)
  let t'7 ← PMem.ldU64 (fp + 0)
  let t'8 ← PMem.memcpy timesync ((t'7 + 16) + ((Int32.toInt64 ((0 : Int32))) * 8).toUInt64) (UInt8.toUInt64 (len))
  discard <| pure (t'8)
  return ()

def mavlink_msg_timesync_decode (msg : UInt64) (timesync : UInt64) : PMem.M Unit := do
  let fp ← PMem.enter 8
  let r ← mavlink_msg_timesync_decode.body fp msg timesync
  PMem.leave fp
  return r

/-- `__mavlink_set_mode_t.__mavlink_set_mode_t` as a pure function of its arguments (it reads and writes no memory). -/
def __mavlink_set_mode_t.__mavlink_set_mode_t.pure' (this : UInt64) : Id Unit := do
  return ()

/-- C++ `__mavlink_set_mode_t::__mavlink_set_mode_t : void () noexcept`, `mavlink_msg_set_mode.h:9-?`. -/
def __mavlink_set_mode_t.__mavlink_set_mode_t (this : UInt64) : PMem.M Unit :=
  pure (_root_.Vehicle_lib.__mavlink_set_mode_t.__mavlink_set_mode_t.pure' this)

/-- C++ `mavlink_msg_set_mode_decode : void (const mavlink_message_t *, mavlink_set_mode_t *)`, `mavlink_msg_set_mode.h:297-313`. -/
def mavlink_msg_set_mode_decode (msg : UInt64) (set_mode : UInt64) : PMem.M Unit := do
  let mut msg := msg
  let mut set_mode := set_mode
  mavlink_msg_decode_target msg set_mode (Int8.toUInt8 (Int32.toInt8 ((6 : Int32)))) (Int8.toUInt8 (Int32.toInt8 ((4 : Int32))))
  return ()

/-- `__mavlink_mission_write_partial_list_t.__mavlink_mission_write_partial_list_t` as a pure function of its arguments (it reads and writes no memory). -/
def __mavlink_mission_write_partial_list_t.__mavlink_mission_write_partial_list_t.pure' (this : UInt64) : Id Unit := do
  return ()

/-- C++ `__mavlink_mission_write_partial_list_t::__mavlink_mission_write_partial_list_t : void () noexcept`, `mavlink_msg_mission_write_partial_list.h:9-?`. -/
def __mavlink_mission_write_partial_list_t.__mavlink_mission_write_partial_list_t (this : UInt64) : PMem.M Unit :=
  pure (_root_.Vehicle_lib.__mavlink_mission_write_partial_list_t.__mavlink_mission_write_partial_list_t.pure' this)

/-- C++ `mavlink_msg_mission_write_partial_list_decode : void (const mavlink_message_t *, mavlink_mission_write_partial_list_t *)`, `mavlink_msg_mission_write_partial_list.h:351-369`. -/
def mavlink_msg_mission_write_partial_list_decode (msg : UInt64) (mission_write_partial_list : UInt64) : PMem.M Unit := do
  let mut msg := msg
  let mut mission_write_partial_list := mission_write_partial_list
  mavlink_msg_decode_target msg mission_write_partial_list (Int8.toUInt8 (Int32.toInt8 ((7 : Int32)))) (Int8.toUInt8 (Int32.toInt8 ((4 : Int32))))
  return ()

/-- `__mavlink_mission_ack_t.__mavlink_mission_ack_t` as a pure function of its arguments (it reads and writes no memory). -/
def __mavlink_mission_ack_t.__mavlink_mission_ack_t.pure' (this : UInt64) : Id Unit := do
  return ()

/-- C++ `__mavlink_mission_ack_t::__mavlink_mission_ack_t : void () noexcept`, `mavlink_msg_mission_ack.h:9-?`. -/
def __mavlink_mission_ack_t.__mavlink_mission_ack_t (this : UInt64) : PMem.M Unit :=
  pure (_root_.Vehicle_lib.__mavlink_mission_ack_t.__mavlink_mission_ack_t.pure' this)

/-- C++ `mavlink_msg_mission_ack_send : void (mavlink_channel_t, uint32_t, uint8_t, uint8_t, uint8_t)`, `mavlink_msg_mission_ack.h:218-237`. -/
def mavlink_msg_mission_ack_send.body (fp : UInt64) (chan : UInt32) (target_system : UInt32) (target_component : UInt8) (type' : UInt8) (mission_type : UInt8) : PMem.M Unit := do
  let mut chan := chan
  let mut target_system := target_system
  let mut target_component := target_component
  let mut type' := type'
  let mut mission_type := mission_type
  __mavlink_mission_ack_t.__mavlink_mission_ack_t (fp + 0)
  let t'1 ← mavlink_msg_target_field target_system
  PMem.stU8 (fp + 0) t'1
  PMem.stU8 ((fp + 0) + 1) target_component
  PMem.stU8 ((fp + 0) + 2) type'
  PMem.stU8 ((fp + 0) + 3) mission_type
  _mav_finalize_message_chan_send_target chan (Int32.toUInt32 ((47 : Int32))) (fp + 0) (Int8.toUInt8 (Int32.toInt8 ((3 : Int32)))) (Int8.toUInt8 (Int32.toInt8 ((4 : Int32)))) (Int8.toUInt8 (Int32.toInt8 ((153 : Int32)))) target_system
  return ()

def mavlink_msg_mission_ack_send (chan : UInt32) (target_system : UInt32) (target_component : UInt8) (type' : UInt8) (mission_type : UInt8) : PMem.M Unit := do
  let fp ← PMem.enter 4
  let r ← mavlink_msg_mission_ack_send.body fp chan target_system target_component type' mission_type
  PMem.leave fp
  return r

/-- `__mavlink_mission_item_int_t.__mavlink_mission_item_int_t` as a pure function of its arguments (it reads and writes no memory). -/
def __mavlink_mission_item_int_t.__mavlink_mission_item_int_t.pure' (this : UInt64) : Id Unit := do
  return ()

/-- C++ `__mavlink_mission_item_int_t::__mavlink_mission_item_int_t : void () noexcept`, `mavlink_msg_mission_item_int.h:9-?`. -/
def __mavlink_mission_item_int_t.__mavlink_mission_item_int_t (this : UInt64) : PMem.M Unit :=
  pure (_root_.Vehicle_lib.__mavlink_mission_item_int_t.__mavlink_mission_item_int_t.pure' this)

/-- `__mavlink_mission_item_t.__mavlink_mission_item_t` as a pure function of its arguments (it reads and writes no memory). -/
def __mavlink_mission_item_t.__mavlink_mission_item_t.pure' (this : UInt64) : Id Unit := do
  return ()

/-- C++ `__mavlink_mission_item_t::__mavlink_mission_item_t : void () noexcept`, `mavlink_msg_mission_item.h:9-?`. -/
def __mavlink_mission_item_t.__mavlink_mission_item_t (this : UInt64) : PMem.M Unit :=
  pure (_root_.Vehicle_lib.__mavlink_mission_item_t.__mavlink_mission_item_t.pure' this)

/-- C++ `mavlink_msg_mission_item_decode : void (const mavlink_message_t *, mavlink_mission_item_t *)`, `mavlink_msg_mission_item.h:621-649`. -/
def mavlink_msg_mission_item_decode (msg : UInt64) (mission_item : UInt64) : PMem.M Unit := do
  let mut msg := msg
  let mut mission_item := mission_item
  mavlink_msg_decode_target msg mission_item (Int8.toUInt8 (Int32.toInt8 ((38 : Int32)))) (Int8.toUInt8 (Int32.toInt8 ((32 : Int32))))
  return ()

/-- C++ `mavlink_msg_mission_item_int_decode : void (const mavlink_message_t *, mavlink_mission_item_int_t *)`, `mavlink_msg_mission_item_int.h:621-649`. -/
def mavlink_msg_mission_item_int_decode (msg : UInt64) (mission_item_int : UInt64) : PMem.M Unit := do
  let mut msg := msg
  let mut mission_item_int := mission_item_int
  mavlink_msg_decode_target msg mission_item_int (Int8.toUInt8 (Int32.toInt8 ((38 : Int32)))) (Int8.toUInt8 (Int32.toInt8 ((32 : Int32))))
  return ()

/-- C++ `__mavlink_mission_item_int_t::__mavlink_mission_item_int_t : void (const __mavlink_mission_item_int_t &) noexcept`, `mavlink_msg_mission_item_int.h:?-?`. -/
def __mavlink_mission_item_int_t.__mavlink_mission_item_int_t'2 (this : UInt64) (arg : UInt64) : PMem.M Unit := do
  let t'1 ← PMem.ldF32 arg
  PMem.stF32 (this + 0) t'1
  let t'2 ← PMem.ldF32 (arg + 4)
  PMem.stF32 (this + 4) t'2
  let t'3 ← PMem.ldF32 (arg + 8)
  PMem.stF32 (this + 8) t'3
  let t'4 ← PMem.ldF32 (arg + 12)
  PMem.stF32 (this + 12) t'4
  let t'5 ← PMem.ldI32 (arg + 16)
  PMem.stI32 (this + 16) t'5
  let t'6 ← PMem.ldI32 (arg + 20)
  PMem.stI32 (this + 20) t'6
  let t'7 ← PMem.ldF32 (arg + 24)
  PMem.stF32 (this + 24) t'7
  let t'8 ← PMem.ldU16 (arg + 28)
  PMem.stU16 (this + 28) t'8
  let t'9 ← PMem.ldU16 (arg + 30)
  PMem.stU16 (this + 30) t'9
  let t'10 ← PMem.ldU8 (arg + 32)
  PMem.stU8 (this + 32) t'10
  let t'11 ← PMem.ldU8 (arg + 33)
  PMem.stU8 (this + 33) t'11
  let t'12 ← PMem.ldU8 (arg + 34)
  PMem.stU8 (this + 34) t'12
  let t'13 ← PMem.ldU8 (arg + 35)
  PMem.stU8 (this + 35) t'13
  let t'14 ← PMem.ldU8 (arg + 36)
  PMem.stU8 (this + 36) t'14
  let t'15 ← PMem.ldU8 (arg + 37)
  PMem.stU8 (this + 37) t'15
  return ()

/-- `__mavlink_mission_request_t.__mavlink_mission_request_t` as a pure function of its arguments (it reads and writes no memory). -/
def __mavlink_mission_request_t.__mavlink_mission_request_t.pure' (this : UInt64) : Id Unit := do
  return ()

/-- C++ `__mavlink_mission_request_t::__mavlink_mission_request_t : void () noexcept`, `mavlink_msg_mission_request.h:9-?`. -/
def __mavlink_mission_request_t.__mavlink_mission_request_t (this : UInt64) : PMem.M Unit :=
  pure (_root_.Vehicle_lib.__mavlink_mission_request_t.__mavlink_mission_request_t.pure' this)

/-- C++ `mavlink_msg_mission_request_send : void (mavlink_channel_t, uint32_t, uint8_t, uint16_t, uint8_t)`, `mavlink_msg_mission_request.h:218-237`. -/
def mavlink_msg_mission_request_send.body (fp : UInt64) (chan : UInt32) (target_system : UInt32) (target_component : UInt8) (seq : UInt16) (mission_type : UInt8) : PMem.M Unit := do
  let mut chan := chan
  let mut target_system := target_system
  let mut target_component := target_component
  let mut seq := seq
  let mut mission_type := mission_type
  __mavlink_mission_request_t.__mavlink_mission_request_t (fp + 0)
  PMem.stU16 (fp + 0) seq
  let t'1 ← mavlink_msg_target_field target_system
  PMem.stU8 ((fp + 0) + 2) t'1
  PMem.stU8 ((fp + 0) + 3) target_component
  PMem.stU8 ((fp + 0) + 4) mission_type
  _mav_finalize_message_chan_send_target chan (Int32.toUInt32 ((40 : Int32))) (fp + 0) (Int8.toUInt8 (Int32.toInt8 ((4 : Int32)))) (Int8.toUInt8 (Int32.toInt8 ((5 : Int32)))) (Int8.toUInt8 (Int32.toInt8 ((230 : Int32)))) target_system
  return ()

def mavlink_msg_mission_request_send (chan : UInt32) (target_system : UInt32) (target_component : UInt8) (seq : UInt16) (mission_type : UInt8) : PMem.M Unit := do
  let fp ← PMem.enter 5
  let r ← mavlink_msg_mission_request_send.body fp chan target_system target_component seq mission_type
  PMem.leave fp
  return r

/-- `__mavlink_mission_request_int_t.__mavlink_mission_request_int_t` as a pure function of its arguments (it reads and writes no memory). -/
def __mavlink_mission_request_int_t.__mavlink_mission_request_int_t.pure' (this : UInt64) : Id Unit := do
  return ()

/-- C++ `__mavlink_mission_request_int_t::__mavlink_mission_request_int_t : void () noexcept`, `mavlink_msg_mission_request_int.h:9-?`. -/
def __mavlink_mission_request_int_t.__mavlink_mission_request_int_t (this : UInt64) : PMem.M Unit :=
  pure (_root_.Vehicle_lib.__mavlink_mission_request_int_t.__mavlink_mission_request_int_t.pure' this)

/-- C++ `mavlink_msg_mission_request_int_decode : void (const mavlink_message_t *, mavlink_mission_request_int_t *)`, `mavlink_msg_mission_request_int.h:324-341`. -/
def mavlink_msg_mission_request_int_decode (msg : UInt64) (mission_request_int : UInt64) : PMem.M Unit := do
  let mut msg := msg
  let mut mission_request_int := mission_request_int
  mavlink_msg_decode_target msg mission_request_int (Int8.toUInt8 (Int32.toInt8 ((5 : Int32)))) (Int8.toUInt8 (Int32.toInt8 ((2 : Int32))))
  return ()

/-- `__mavlink_mission_count_t.__mavlink_mission_count_t` as a pure function of its arguments (it reads and writes no memory). -/
def __mavlink_mission_count_t.__mavlink_mission_count_t.pure' (this : UInt64) : Id Unit := do
  return ()

/-- C++ `__mavlink_mission_count_t::__mavlink_mission_count_t : void () noexcept`, `mavlink_msg_mission_count.h:9-?`. -/
def __mavlink_mission_count_t.__mavlink_mission_count_t (this : UInt64) : PMem.M Unit :=
  pure (_root_.Vehicle_lib.__mavlink_mission_count_t.__mavlink_mission_count_t.pure' this)

/-- C++ `mavlink_msg_mission_count_send : void (mavlink_channel_t, uint32_t, uint8_t, uint16_t, uint8_t)`, `mavlink_msg_mission_count.h:218-237`. -/
def mavlink_msg_mission_count_send.body (fp : UInt64) (chan : UInt32) (target_system : UInt32) (target_component : UInt8) (count : UInt16) (mission_type : UInt8) : PMem.M Unit := do
  let mut chan := chan
  let mut target_system := target_system
  let mut target_component := target_component
  let mut count := count
  let mut mission_type := mission_type
  __mavlink_mission_count_t.__mavlink_mission_count_t (fp + 0)
  PMem.stU16 (fp + 0) count
  let t'1 ← mavlink_msg_target_field target_system
  PMem.stU8 ((fp + 0) + 2) t'1
  PMem.stU8 ((fp + 0) + 3) target_component
  PMem.stU8 ((fp + 0) + 4) mission_type
  _mav_finalize_message_chan_send_target chan (Int32.toUInt32 ((44 : Int32))) (fp + 0) (Int8.toUInt8 (Int32.toInt8 ((4 : Int32)))) (Int8.toUInt8 (Int32.toInt8 ((5 : Int32)))) (Int8.toUInt8 (Int32.toInt8 ((221 : Int32)))) target_system
  return ()

def mavlink_msg_mission_count_send (chan : UInt32) (target_system : UInt32) (target_component : UInt8) (count : UInt16) (mission_type : UInt8) : PMem.M Unit := do
  let fp ← PMem.enter 5
  let r ← mavlink_msg_mission_count_send.body fp chan target_system target_component count mission_type
  PMem.leave fp
  return r

/-- C++ `mavlink_msg_mission_request_decode : void (const mavlink_message_t *, mavlink_mission_request_t *)`, `mavlink_msg_mission_request.h:324-341`. -/
def mavlink_msg_mission_request_decode (msg : UInt64) (mission_request : UInt64) : PMem.M Unit := do
  let mut msg := msg
  let mut mission_request := mission_request
  mavlink_msg_decode_target msg mission_request (Int8.toUInt8 (Int32.toInt8 ((5 : Int32)))) (Int8.toUInt8 (Int32.toInt8 ((2 : Int32))))
  return ()

/-- `__mavlink_mission_current_t.__mavlink_mission_current_t` as a pure function of its arguments (it reads and writes no memory). -/
def __mavlink_mission_current_t.__mavlink_mission_current_t.pure' (this : UInt64) : Id Unit := do
  return ()

/-- C++ `__mavlink_mission_current_t::__mavlink_mission_current_t : void () noexcept`, `mavlink_msg_mission_current.h:9-?`. -/
def __mavlink_mission_current_t.__mavlink_mission_current_t (this : UInt64) : PMem.M Unit :=
  pure (_root_.Vehicle_lib.__mavlink_mission_current_t.__mavlink_mission_current_t.pure' this)

/-- C++ `mavlink_msg_mission_current_send : void (mavlink_channel_t, uint16_t, uint16_t, uint8_t, uint8_t)`, `mavlink_msg_mission_current.h:218-237`. -/
def mavlink_msg_mission_current_send.body (fp : UInt64) (chan : UInt32) (seq : UInt16) (total : UInt16) (mission_state : UInt8) (mission_mode : UInt8) : PMem.M Unit := do
  let mut chan := chan
  let mut seq := seq
  let mut total := total
  let mut mission_state := mission_state
  let mut mission_mode := mission_mode
  __mavlink_mission_current_t.__mavlink_mission_current_t (fp + 0)
  PMem.stU16 (fp + 0) seq
  PMem.stU16 ((fp + 0) + 2) total
  PMem.stU8 ((fp + 0) + 4) mission_state
  PMem.stU8 ((fp + 0) + 5) mission_mode
  _mav_finalize_message_chan_send chan (Int32.toUInt32 ((42 : Int32))) (fp + 0) (Int8.toUInt8 (Int32.toInt8 ((2 : Int32)))) (Int8.toUInt8 (Int32.toInt8 ((6 : Int32)))) (Int8.toUInt8 (Int32.toInt8 ((28 : Int32))))
  return ()

def mavlink_msg_mission_current_send (chan : UInt32) (seq : UInt16) (total : UInt16) (mission_state : UInt8) (mission_mode : UInt8) : PMem.M Unit := do
  let fp ← PMem.enter 6
  let r ← mavlink_msg_mission_current_send.body fp chan seq total mission_state mission_mode
  PMem.leave fp
  return r

/-- `__mavlink_mission_set_current_t.__mavlink_mission_set_current_t` as a pure function of its arguments (it reads and writes no memory). -/
def __mavlink_mission_set_current_t.__mavlink_mission_set_current_t.pure' (this : UInt64) : Id Unit := do
  return ()

/-- C++ `__mavlink_mission_set_current_t::__mavlink_mission_set_current_t : void () noexcept`, `mavlink_msg_mission_set_current.h:9-?`. -/
def __mavlink_mission_set_current_t.__mavlink_mission_set_current_t (this : UInt64) : PMem.M Unit :=
  pure (_root_.Vehicle_lib.__mavlink_mission_set_current_t.__mavlink_mission_set_current_t.pure' this)

/-- C++ `mavlink_msg_mission_set_current_decode : void (const mavlink_message_t *, mavlink_mission_set_current_t *)`, `mavlink_msg_mission_set_current.h:297-313`. -/
def mavlink_msg_mission_set_current_decode (msg : UInt64) (mission_set_current : UInt64) : PMem.M Unit := do
  let mut msg := msg
  let mut mission_set_current := mission_set_current
  mavlink_msg_decode_target msg mission_set_current (Int8.toUInt8 (Int32.toInt8 ((4 : Int32)))) (Int8.toUInt8 (Int32.toInt8 ((2 : Int32))))
  return ()

/-- `__mavlink_mission_request_list_t.__mavlink_mission_request_list_t` as a pure function of its arguments (it reads and writes no memory). -/
def __mavlink_mission_request_list_t.__mavlink_mission_request_list_t.pure' (this : UInt64) : Id Unit := do
  return ()

/-- C++ `__mavlink_mission_request_list_t::__mavlink_mission_request_list_t : void () noexcept`, `mavlink_msg_mission_request_list.h:9-?`. -/
def __mavlink_mission_request_list_t.__mavlink_mission_request_list_t (this : UInt64) : PMem.M Unit :=
  pure (_root_.Vehicle_lib.__mavlink_mission_request_list_t.__mavlink_mission_request_list_t.pure' this)

/-- C++ `mavlink_msg_mission_request_list_decode : void (const mavlink_message_t *, mavlink_mission_request_list_t *)`, `mavlink_msg_mission_request_list.h:297-313`. -/
def mavlink_msg_mission_request_list_decode (msg : UInt64) (mission_request_list : UInt64) : PMem.M Unit := do
  let mut msg := msg
  let mut mission_request_list := mission_request_list
  mavlink_msg_decode_target msg mission_request_list (Int8.toUInt8 (Int32.toInt8 ((3 : Int32)))) (Int8.toUInt8 (Int32.toInt8 ((0 : Int32))))
  return ()

/-- C++ `mavlink_msg_mission_count_decode : void (const mavlink_message_t *, mavlink_mission_count_t *)`, `mavlink_msg_mission_count.h:324-341`. -/
def mavlink_msg_mission_count_decode (msg : UInt64) (mission_count : UInt64) : PMem.M Unit := do
  let mut msg := msg
  let mut mission_count := mission_count
  mavlink_msg_decode_target msg mission_count (Int8.toUInt8 (Int32.toInt8 ((5 : Int32)))) (Int8.toUInt8 (Int32.toInt8 ((2 : Int32))))
  return ()

/-- `__mavlink_mission_clear_all_t.__mavlink_mission_clear_all_t` as a pure function of its arguments (it reads and writes no memory). -/
def __mavlink_mission_clear_all_t.__mavlink_mission_clear_all_t.pure' (this : UInt64) : Id Unit := do
  return ()

/-- C++ `__mavlink_mission_clear_all_t::__mavlink_mission_clear_all_t : void () noexcept`, `mavlink_msg_mission_clear_all.h:9-?`. -/
def __mavlink_mission_clear_all_t.__mavlink_mission_clear_all_t (this : UInt64) : PMem.M Unit :=
  pure (_root_.Vehicle_lib.__mavlink_mission_clear_all_t.__mavlink_mission_clear_all_t.pure' this)

/-- C++ `mavlink_msg_mission_clear_all_decode : void (const mavlink_message_t *, mavlink_mission_clear_all_t *)`, `mavlink_msg_mission_clear_all.h:297-313`. -/
def mavlink_msg_mission_clear_all_decode (msg : UInt64) (mission_clear_all : UInt64) : PMem.M Unit := do
  let mut msg := msg
  let mut mission_clear_all := mission_clear_all
  mavlink_msg_decode_target msg mission_clear_all (Int8.toUInt8 (Int32.toInt8 ((3 : Int32)))) (Int8.toUInt8 (Int32.toInt8 ((0 : Int32))))
  return ()

/-- `__mavlink_command_long_t.__mavlink_command_long_t` as a pure function of its arguments (it reads and writes no memory). -/
def __mavlink_command_long_t.__mavlink_command_long_t.pure' (this : UInt64) : Id Unit := do
  return ()

/-- C++ `__mavlink_command_long_t::__mavlink_command_long_t : void () noexcept`, `mavlink_msg_command_long.h:9-?`. -/
def __mavlink_command_long_t.__mavlink_command_long_t (this : UInt64) : PMem.M Unit :=
  pure (_root_.Vehicle_lib.__mavlink_command_long_t.__mavlink_command_long_t.pure' this)

/-- C++ `mavlink_msg_command_long_decode : void (const mavlink_message_t *, mavlink_command_long_t *)`, `mavlink_msg_command_long.h:513-537`. -/
def mavlink_msg_command_long_decode (msg : UInt64) (command_long : UInt64) : PMem.M Unit := do
  let mut msg := msg
  let mut command_long := command_long
  mavlink_msg_decode_target msg command_long (Int8.toUInt8 (Int32.toInt8 ((33 : Int32)))) (Int8.toUInt8 (Int32.toInt8 ((30 : Int32))))
  return ()

/-- `__mavlink_command_int_t.__mavlink_command_int_t` as a pure function of its arguments (it reads and writes no memory). -/
def __mavlink_command_int_t.__mavlink_command_int_t.pure' (this : UInt64) : Id Unit := do
  return ()

/-- C++ `__mavlink_command_int_t::__mavlink_command_int_t : void () noexcept`, `mavlink_msg_command_int.h:9-?`. -/
def __mavlink_command_int_t.__mavlink_command_int_t (this : UInt64) : PMem.M Unit :=
  pure (_root_.Vehicle_lib.__mavlink_command_int_t.__mavlink_command_int_t.pure' this)

/-- `__mavlink_wind_t.__mavlink_wind_t` as a pure function of its arguments (it reads and writes no memory). -/
def __mavlink_wind_t.__mavlink_wind_t.pure' (this : UInt64) : Id Unit := do
  return ()

/-- C++ `__mavlink_wind_t::__mavlink_wind_t : void () noexcept`, `mavlink_msg_wind.h:9-?`. -/
def __mavlink_wind_t.__mavlink_wind_t (this : UInt64) : PMem.M Unit :=
  pure (_root_.Vehicle_lib.__mavlink_wind_t.__mavlink_wind_t.pure' this)

/-- C++ `mavlink_msg_wind_send : void (mavlink_channel_t, float, float, float)`, `mavlink_msg_wind.h:205-222`. -/
def mavlink_msg_wind_send.body (fp : UInt64) (chan : UInt32) (direction : Binary32) (speed : Binary32) (speed_z : Binary32) : PMem.M Unit := do
  let mut chan := chan
  let mut direction := direction
  let mut speed := speed
  let mut speed_z := speed_z
  __mavlink_wind_t.__mavlink_wind_t (fp + 0)
  PMem.stF32 (fp + 0) direction
  PMem.stF32 ((fp + 0) + 4) speed
  PMem.stF32 ((fp + 0) + 8) speed_z
  _mav_finalize_message_chan_send chan (Int32.toUInt32 ((168 : Int32))) (fp + 0) (Int8.toUInt8 (Int32.toInt8 ((12 : Int32)))) (Int8.toUInt8 (Int32.toInt8 ((12 : Int32)))) (Int8.toUInt8 (Int32.toInt8 ((1 : Int32))))
  return ()

def mavlink_msg_wind_send (chan : UInt32) (direction : Binary32) (speed : Binary32) (speed_z : Binary32) : PMem.M Unit := do
  let fp ← PMem.enter 12
  let r ← mavlink_msg_wind_send.body fp chan direction speed speed_z
  PMem.leave fp
  return r

/-- `__mavlink_attitude_t.__mavlink_attitude_t` as a pure function of its arguments (it reads and writes no memory). -/
def __mavlink_attitude_t.__mavlink_attitude_t.pure' (this : UInt64) : Id Unit := do
  return ()

/-- C++ `__mavlink_attitude_t::__mavlink_attitude_t : void () noexcept`, `mavlink_msg_attitude.h:9-?`. -/
def __mavlink_attitude_t.__mavlink_attitude_t (this : UInt64) : PMem.M Unit :=
  pure (_root_.Vehicle_lib.__mavlink_attitude_t.__mavlink_attitude_t.pure' this)

/-- C++ `mavlink_msg_attitude_send : void (mavlink_channel_t, uint32_t, float, float, float, float, float, float)`, `mavlink_msg_attitude.h:257-282`. -/
def mavlink_msg_attitude_send.body (fp : UInt64) (chan : UInt32) (time_boot_ms : UInt32) (roll : Binary32) (pitch : Binary32) (yaw : Binary32) (rollspeed : Binary32) (pitchspeed : Binary32) (yawspeed : Binary32) : PMem.M Unit := do
  let mut chan := chan
  let mut time_boot_ms := time_boot_ms
  let mut roll := roll
  let mut pitch := pitch
  let mut yaw := yaw
  let mut rollspeed := rollspeed
  let mut pitchspeed := pitchspeed
  let mut yawspeed := yawspeed
  __mavlink_attitude_t.__mavlink_attitude_t (fp + 0)
  PMem.stU32 (fp + 0) time_boot_ms
  PMem.stF32 ((fp + 0) + 4) roll
  PMem.stF32 ((fp + 0) + 8) pitch
  PMem.stF32 ((fp + 0) + 12) yaw
  PMem.stF32 ((fp + 0) + 16) rollspeed
  PMem.stF32 ((fp + 0) + 20) pitchspeed
  PMem.stF32 ((fp + 0) + 24) yawspeed
  _mav_finalize_message_chan_send chan (Int32.toUInt32 ((30 : Int32))) (fp + 0) (Int8.toUInt8 (Int32.toInt8 ((28 : Int32)))) (Int8.toUInt8 (Int32.toInt8 ((28 : Int32)))) (Int8.toUInt8 (Int32.toInt8 ((39 : Int32))))
  return ()

def mavlink_msg_attitude_send (chan : UInt32) (time_boot_ms : UInt32) (roll : Binary32) (pitch : Binary32) (yaw : Binary32) (rollspeed : Binary32) (pitchspeed : Binary32) (yawspeed : Binary32) : PMem.M Unit := do
  let fp ← PMem.enter 28
  let r ← mavlink_msg_attitude_send.body fp chan time_boot_ms roll pitch yaw rollspeed pitchspeed yawspeed
  PMem.leave fp
  return r

/-- `__mavlink_attitude_quaternion_t.__mavlink_attitude_quaternion_t` as a pure function of its arguments (it reads and writes no memory). -/
def __mavlink_attitude_quaternion_t.__mavlink_attitude_quaternion_t.pure' (this : UInt64) : Id Unit := do
  return ()

/-- C++ `__mavlink_attitude_quaternion_t::__mavlink_attitude_quaternion_t : void () noexcept`, `mavlink_msg_attitude_quaternion.h:9-?`. -/
def __mavlink_attitude_quaternion_t.__mavlink_attitude_quaternion_t (this : UInt64) : PMem.M Unit :=
  pure (_root_.Vehicle_lib.__mavlink_attitude_quaternion_t.__mavlink_attitude_quaternion_t.pure' this)

/-- C++ `mavlink_msg_attitude_quaternion_send : void (mavlink_channel_t, uint32_t, float, float, float, float, float, float, float, const float *)`, `mavlink_msg_attitude_quaternion.h:277-304`. -/
def mavlink_msg_attitude_quaternion_send.body (fp : UInt64) (chan : UInt32) (time_boot_ms : UInt32) (q1 : Binary32) (q2 : Binary32) (q3 : Binary32) (q4 : Binary32) (rollspeed : Binary32) (pitchspeed : Binary32) (yawspeed : Binary32) (repr_offset_q : UInt64) : PMem.M Unit := do
  let mut chan := chan
  let mut time_boot_ms := time_boot_ms
  let mut q1 := q1
  let mut q2 := q2
  let mut q3 := q3
  let mut q4 := q4
  let mut rollspeed := rollspeed
  let mut pitchspeed := pitchspeed
  let mut yawspeed := yawspeed
  let mut repr_offset_q := repr_offset_q
  __mavlink_attitude_quaternion_t.__mavlink_attitude_quaternion_t (fp + 0)
  PMem.stU32 (fp + 0) time_boot_ms
  PMem.stF32 ((fp + 0) + 4) q1
  PMem.stF32 ((fp + 0) + 8) q2
  PMem.stF32 ((fp + 0) + 12) q3
  PMem.stF32 ((fp + 0) + 16) q4
  PMem.stF32 ((fp + 0) + 20) rollspeed
  PMem.stF32 ((fp + 0) + 24) pitchspeed
  PMem.stF32 ((fp + 0) + 28) yawspeed
  mav_array_memcpy ((fp + 0) + 32) repr_offset_q ((4 : UInt64) * (Int64.toUInt64 (Int32.toInt64 ((4 : Int32)))))
  _mav_finalize_message_chan_send chan (Int32.toUInt32 ((31 : Int32))) (fp + 0) (Int8.toUInt8 (Int32.toInt8 ((32 : Int32)))) (Int8.toUInt8 (Int32.toInt8 ((48 : Int32)))) (Int8.toUInt8 (Int32.toInt8 ((246 : Int32))))
  return ()

def mavlink_msg_attitude_quaternion_send (chan : UInt32) (time_boot_ms : UInt32) (q1 : Binary32) (q2 : Binary32) (q3 : Binary32) (q4 : Binary32) (rollspeed : Binary32) (pitchspeed : Binary32) (yawspeed : Binary32) (repr_offset_q : UInt64) : PMem.M Unit := do
  let fp ← PMem.enter 48
  let r ← mavlink_msg_attitude_quaternion_send.body fp chan time_boot_ms q1 q2 q3 q4 rollspeed pitchspeed yawspeed repr_offset_q
  PMem.leave fp
  return r

/-- `__mavlink_heartbeat_t.__mavlink_heartbeat_t` as a pure function of its arguments (it reads and writes no memory). -/
def __mavlink_heartbeat_t.__mavlink_heartbeat_t.pure' (this : UInt64) : Id Unit := do
  return ()

/-- C++ `__mavlink_heartbeat_t::__mavlink_heartbeat_t : void () noexcept`, `mavlink_msg_heartbeat.h:9-?`. -/
def __mavlink_heartbeat_t.__mavlink_heartbeat_t (this : UInt64) : PMem.M Unit :=
  pure (_root_.Vehicle_lib.__mavlink_heartbeat_t.__mavlink_heartbeat_t.pure' this)

/-- C++ `mavlink_msg_heartbeat_send : void (mavlink_channel_t, uint8_t, uint8_t, uint8_t, uint32_t, uint8_t)`, `mavlink_msg_heartbeat.h:240-263`. -/
def mavlink_msg_heartbeat_send.body (fp : UInt64) (chan : UInt32) (type' : UInt8) (autopilot : UInt8) (base_mode : UInt8) (custom_mode : UInt32) (system_status : UInt8) : PMem.M Unit := do
  let mut chan := chan
  let mut type' := type'
  let mut autopilot := autopilot
  let mut base_mode := base_mode
  let mut custom_mode := custom_mode
  let mut system_status := system_status
  __mavlink_heartbeat_t.__mavlink_heartbeat_t (fp + 0)
  PMem.stU32 (fp + 0) custom_mode
  PMem.stU8 ((fp + 0) + 4) type'
  PMem.stU8 ((fp + 0) + 5) autopilot
  PMem.stU8 ((fp + 0) + 6) base_mode
  PMem.stU8 ((fp + 0) + 7) system_status
  let t'1 := Int8.toUInt8 (Int32.toInt8 ((3 : Int32)))
  PMem.stU8 ((fp + 0) + 8) t'1
  _mav_finalize_message_chan_send chan (Int32.toUInt32 ((0 : Int32))) (fp + 0) (Int8.toUInt8 (Int32.toInt8 ((9 : Int32)))) (Int8.toUInt8 (Int32.toInt8 ((9 : Int32)))) (Int8.toUInt8 (Int32.toInt8 ((50 : Int32))))
  return ()

def mavlink_msg_heartbeat_send (chan : UInt32) (type' : UInt8) (autopilot : UInt8) (base_mode : UInt8) (custom_mode : UInt32) (system_status : UInt8) : PMem.M Unit := do
  let fp ← PMem.enter 9
  let r ← mavlink_msg_heartbeat_send.body fp chan type' autopilot base_mode custom_mode system_status
  PMem.leave fp
  return r

/-- `__mavlink_global_position_int_t.__mavlink_global_position_int_t` as a pure function of its arguments (it reads and writes no memory). -/
def __mavlink_global_position_int_t.__mavlink_global_position_int_t.pure' (this : UInt64) : Id Unit := do
  return ()

/-- C++ `__mavlink_global_position_int_t::__mavlink_global_position_int_t : void () noexcept`, `mavlink_msg_global_position_int.h:9-?`. -/
def __mavlink_global_position_int_t.__mavlink_global_position_int_t (this : UInt64) : PMem.M Unit :=
  pure (_root_.Vehicle_lib.__mavlink_global_position_int_t.__mavlink_global_position_int_t.pure' this)

/-- C++ `mavlink_msg_global_position_int_send : void (mavlink_channel_t, uint32_t, int32_t, int32_t, int32_t, int32_t, int16_t, int16_t, int16_t, uint16_t)`, `mavlink_msg_global_position_int.h:283-312`. -/
def mavlink_msg_global_position_int_send.body (fp : UInt64) (chan : UInt32) (time_boot_ms : UInt32) (lat : Int32) (lon : Int32) (alt : Int32) (relative_alt : Int32) (vx : Int16) (vy : Int16) (vz : Int16) (hdg : UInt16) : PMem.M Unit := do
  let mut chan := chan
  let mut time_boot_ms := time_boot_ms
  let mut lat := lat
  let mut lon := lon
  let mut alt := alt
  let mut relative_alt := relative_alt
  let mut vx := vx
  let mut vy := vy
  let mut vz := vz
  let mut hdg := hdg
  __mavlink_global_position_int_t.__mavlink_global_position_int_t (fp + 0)
  PMem.stU32 (fp + 0) time_boot_ms
  PMem.stI32 ((fp + 0) + 4) lat
  PMem.stI32 ((fp + 0) + 8) lon
  PMem.stI32 ((fp + 0) + 12) alt
  PMem.stI32 ((fp + 0) + 16) relative_alt
  PMem.stI16 ((fp + 0) + 20) vx
  PMem.stI16 ((fp + 0) + 22) vy
  PMem.stI16 ((fp + 0) + 24) vz
  PMem.stU16 ((fp + 0) + 26) hdg
  _mav_finalize_message_chan_send chan (Int32.toUInt32 ((33 : Int32))) (fp + 0) (Int8.toUInt8 (Int32.toInt8 ((28 : Int32)))) (Int8.toUInt8 (Int32.toInt8 ((28 : Int32)))) (Int8.toUInt8 (Int32.toInt8 ((104 : Int32))))
  return ()

def mavlink_msg_global_position_int_send (chan : UInt32) (time_boot_ms : UInt32) (lat : Int32) (lon : Int32) (alt : Int32) (relative_alt : Int32) (vx : Int16) (vy : Int16) (vz : Int16) (hdg : UInt16) : PMem.M Unit := do
  let fp ← PMem.enter 28
  let r ← mavlink_msg_global_position_int_send.body fp chan time_boot_ms lat lon alt relative_alt vx vy vz hdg
  PMem.leave fp
  return r

/-- `__mavlink_home_position_t.__mavlink_home_position_t` as a pure function of its arguments (it reads and writes no memory). -/
def __mavlink_home_position_t.__mavlink_home_position_t.pure' (this : UInt64) : Id Unit := do
  return ()

/-- C++ `__mavlink_home_position_t::__mavlink_home_position_t : void () noexcept`, `mavlink_types.h:?-?`. -/
def __mavlink_home_position_t.__mavlink_home_position_t (this : UInt64) : PMem.M Unit :=
  pure (_root_.Vehicle_lib.__mavlink_home_position_t.__mavlink_home_position_t.pure' this)

/-- C++ `mavlink_msg_home_position_send : void (mavlink_channel_t, int32_t, int32_t, int32_t, float, float, float, const float *, float, float, float, uint64_t)`, `mavlink_msg_home_position.h:303-334`. -/
def mavlink_msg_home_position_send.body (fp : UInt64) (chan : UInt32) (latitude : Int32) (longitude : Int32) (altitude : Int32) (x : Binary32) (y : Binary32) (z : Binary32) (q : UInt64) (approach_x : Binary32) (approach_y : Binary32) (approach_z : Binary32) (time_usec : UInt64) : PMem.M Unit := do
  let mut chan := chan
  let mut latitude := latitude
  let mut longitude := longitude
  let mut altitude := altitude
  let mut x := x
  let mut y := y
  let mut z := z
  let mut q := q
  let mut approach_x := approach_x
  let mut approach_y := approach_y
  let mut approach_z := approach_z
  let mut time_usec := time_usec
  __mavlink_home_position_t.__mavlink_home_position_t (fp + 0)
  PMem.stI32 (fp + 0) latitude
  PMem.stI32 ((fp + 0) + 4) longitude
  PMem.stI32 ((fp + 0) + 8) altitude
  PMem.stF32 ((fp + 0) + 12) x
  PMem.stF32 ((fp + 0) + 16) y
  PMem.stF32 ((fp + 0) + 20) z
  PMem.stF32 ((fp + 0) + 40) approach_x
  PMem.stF32 ((fp + 0) + 44) approach_y
  PMem.stF32 ((fp + 0) + 48) approach_z
  PMem.stU64 ((fp + 0) + 52) time_usec
  mav_array_memcpy ((fp + 0) + 24) q ((4 : UInt64) * (Int64.toUInt64 (Int32.toInt64 ((4 : Int32)))))
  _mav_finalize_message_chan_send chan (Int32.toUInt32 ((242 : Int32))) (fp + 0) (Int8.toUInt8 (Int32.toInt8 ((52 : Int32)))) (Int8.toUInt8 (Int32.toInt8 ((60 : Int32)))) (Int8.toUInt8 (Int32.toInt8 ((104 : Int32))))
  return ()

def mavlink_msg_home_position_send (chan : UInt32) (latitude : Int32) (longitude : Int32) (altitude : Int32) (x : Binary32) (y : Binary32) (z : Binary32) (q : UInt64) (approach_x : Binary32) (approach_y : Binary32) (approach_z : Binary32) (time_usec : UInt64) : PMem.M Unit := do
  let fp ← PMem.enter 60
  let r ← mavlink_msg_home_position_send.body fp chan latitude longitude altitude x y z q approach_x approach_y approach_z time_usec
  PMem.leave fp
  return r

/-- `__mavlink_gps_global_origin_t.__mavlink_gps_global_origin_t` as a pure function of its arguments (it reads and writes no memory). -/
def __mavlink_gps_global_origin_t.__mavlink_gps_global_origin_t.pure' (this : UInt64) : Id Unit := do
  return ()

/-- C++ `__mavlink_gps_global_origin_t::__mavlink_gps_global_origin_t : void () noexcept`, `mavlink_types.h:?-?`. -/
def __mavlink_gps_global_origin_t.__mavlink_gps_global_origin_t (this : UInt64) : PMem.M Unit :=
  pure (_root_.Vehicle_lib.__mavlink_gps_global_origin_t.__mavlink_gps_global_origin_t.pure' this)

/-- C++ `mavlink_msg_gps_global_origin_send : void (mavlink_channel_t, int32_t, int32_t, int32_t, uint64_t)`, `mavlink_msg_gps_global_origin.h:218-237`. -/
def mavlink_msg_gps_global_origin_send.body (fp : UInt64) (chan : UInt32) (latitude : Int32) (longitude : Int32) (altitude : Int32) (time_usec : UInt64) : PMem.M Unit := do
  let mut chan := chan
  let mut latitude := latitude
  let mut longitude := longitude
  let mut altitude := altitude
  let mut time_usec := time_usec
  __mavlink_gps_global_origin_t.__mavlink_gps_global_origin_t (fp + 0)
  PMem.stI32 (fp + 0) latitude
  PMem.stI32 ((fp + 0) + 4) longitude
  PMem.stI32 ((fp + 0) + 8) altitude
  PMem.stU64 ((fp + 0) + 12) time_usec
  _mav_finalize_message_chan_send chan (Int32.toUInt32 ((49 : Int32))) (fp + 0) (Int8.toUInt8 (Int32.toInt8 ((12 : Int32)))) (Int8.toUInt8 (Int32.toInt8 ((20 : Int32)))) (Int8.toUInt8 (Int32.toInt8 ((39 : Int32))))
  return ()

def mavlink_msg_gps_global_origin_send (chan : UInt32) (latitude : Int32) (longitude : Int32) (altitude : Int32) (time_usec : UInt64) : PMem.M Unit := do
  let fp ← PMem.enter 20
  let r ← mavlink_msg_gps_global_origin_send.body fp chan latitude longitude altitude time_usec
  PMem.leave fp
  return r

/-- C++ `mavlink_msg_utm_global_position_send_struct : void (mavlink_channel_t, const mavlink_utm_global_position_t *)`, `mavlink_msg_utm_global_position.h:446-453`. -/
def mavlink_msg_utm_global_position_send_struct (chan : UInt32) (utm_global_position : UInt64) : PMem.M Unit := do
  let mut chan := chan
  let mut utm_global_position := utm_global_position
  _mav_finalize_message_chan_send chan (Int32.toUInt32 ((340 : Int32))) utm_global_position (Int8.toUInt8 (Int32.toInt8 ((70 : Int32)))) (Int8.toUInt8 (Int32.toInt8 ((70 : Int32)))) (Int8.toUInt8 (Int32.toInt8 ((99 : Int32))))
  return ()

/-- `__mavlink_mission_item_reached_t.__mavlink_mission_item_reached_t` as a pure function of its arguments (it reads and writes no memory). -/
def __mavlink_mission_item_reached_t.__mavlink_mission_item_reached_t.pure' (this : UInt64) : Id Unit := do
  return ()

/-- C++ `__mavlink_mission_item_reached_t::__mavlink_mission_item_reached_t : void () noexcept`, `mavlink_msg_mission_item_reached.h:9-?`. -/
def __mavlink_mission_item_reached_t.__mavlink_mission_item_reached_t (this : UInt64) : PMem.M Unit :=
  pure (_root_.Vehicle_lib.__mavlink_mission_item_reached_t.__mavlink_mission_item_reached_t.pure' this)

/-- C++ `mavlink_msg_mission_item_reached_send : void (mavlink_channel_t, uint16_t)`, `mavlink_msg_mission_item_reached.h:179-192`. -/
def mavlink_msg_mission_item_reached_send.body (fp : UInt64) (chan : UInt32) (seq : UInt16) : PMem.M Unit := do
  let mut chan := chan
  let mut seq := seq
  __mavlink_mission_item_reached_t.__mavlink_mission_item_reached_t (fp + 0)
  PMem.stU16 (fp + 0) seq
  _mav_finalize_message_chan_send chan (Int32.toUInt32 ((46 : Int32))) (fp + 0) (Int8.toUInt8 (Int32.toInt8 ((2 : Int32)))) (Int8.toUInt8 (Int32.toInt8 ((2 : Int32)))) (Int8.toUInt8 (Int32.toInt8 ((11 : Int32))))
  return ()

def mavlink_msg_mission_item_reached_send (chan : UInt32) (seq : UInt16) : PMem.M Unit := do
  let fp ← PMem.enter 2
  let r ← mavlink_msg_mission_item_reached_send.body fp chan seq
  PMem.leave fp
  return r

/-- `__mavlink_battery_status_t.__mavlink_battery_status_t` as a pure function of its arguments (it reads and writes no memory). -/
def __mavlink_battery_status_t.__mavlink_battery_status_t.pure' (this : UInt64) : Id Unit := do
  return ()

/-- C++ `__mavlink_battery_status_t::__mavlink_battery_status_t : void () noexcept`, `mavlink_types.h:?-?`. -/
def __mavlink_battery_status_t.__mavlink_battery_status_t (this : UInt64) : PMem.M Unit :=
  pure (_root_.Vehicle_lib.__mavlink_battery_status_t.__mavlink_battery_status_t.pure' this)

/-- C++ `mavlink_msg_battery_status_send : void (mavlink_channel_t, uint8_t, uint8_t, uint8_t, int16_t, const uint16_t *, int16_t, int32_t, int32_t, int8_t, int32_t, uint8_t, const uint16_t *, uint8_t, uint32_t)`, `mavlink_msg_battery_status.h:343-380`. -/
def mavlink_msg_battery_status_send.body (fp : UInt64) (chan : UInt32) (id : UInt8) (battery_function : UInt8) (type' : UInt8) (temperature : Int16) (voltages : UInt64) (current_battery : Int16) (current_consumed : Int32) (energy_consumed : Int32) (battery_remaining : Int8) (time_remaining : Int32) (charge_state : UInt8) (voltages_ext : UInt64) (mode : UInt8) (fault_bitmask : UInt32) : PMem.M Unit := do
  let mut chan := chan
  let mut id := id
  let mut battery_function := battery_function
  let mut type' := type'
  let mut temperature := temperature
  let mut voltages := voltages
  let mut current_battery := current_battery
  let mut current_consumed := current_consumed
  let mut energy_consumed := energy_consumed
  let mut battery_remaining := battery_remaining
  let mut time_remaining := time_remaining
  let mut charge_state := charge_state
  let mut voltages_ext := voltages_ext
  let mut mode := mode
  let mut fault_bitmask := fault_bitmask
  __mavlink_battery_status_t.__mavlink_battery_status_t (fp + 0)
  PMem.stI32 (fp + 0) current_consumed
  PMem.stI32 ((fp + 0) + 4) energy_consumed
  PMem.stI16 ((fp + 0) + 8) temperature
  PMem.stI16 ((fp + 0) + 30) current_battery
  PMem.stU8 ((fp + 0) + 32) id
  PMem.stU8 ((fp + 0) + 33) battery_function
  PMem.stU8 ((fp + 0) + 34) type'
  PMem.stI8 ((fp + 0) + 35) battery_remaining
  PMem.stI32 ((fp + 0) + 36) time_remaining
  PMem.stU8 ((fp + 0) + 40) charge_state
  PMem.stU8 ((fp + 0) + 49) mode
  PMem.stU32 ((fp + 0) + 50) fault_bitmask
  mav_array_memcpy ((fp + 0) + 10) voltages ((2 : UInt64) * (Int64.toUInt64 (Int32.toInt64 ((10 : Int32)))))
  mav_array_memcpy ((fp + 0) + 41) voltages_ext ((2 : UInt64) * (Int64.toUInt64 (Int32.toInt64 ((4 : Int32)))))
  _mav_finalize_message_chan_send chan (Int32.toUInt32 ((147 : Int32))) (fp + 0) (Int8.toUInt8 (Int32.toInt8 ((36 : Int32)))) (Int8.toUInt8 (Int32.toInt8 ((54 : Int32)))) (Int8.toUInt8 (Int32.toInt8 ((154 : Int32))))
  return ()

def mavlink_msg_battery_status_send (chan : UInt32) (id : UInt8) (battery_function : UInt8) (type' : UInt8) (temperature : Int16) (voltages : UInt64) (current_battery : Int16) (current_consumed : Int32) (energy_consumed : Int32) (battery_remaining : Int8) (time_remaining : Int32) (charge_state : UInt8) (voltages_ext : UInt64) (mode : UInt8) (fault_bitmask : UInt32) : PMem.M Unit := do
  let fp ← PMem.enter 54
  let r ← mavlink_msg_battery_status_send.body fp chan id battery_function type' temperature voltages current_battery current_consumed energy_consumed battery_remaining time_remaining charge_state voltages_ext mode fault_bitmask
  PMem.leave fp
  return r

/-- `__mavlink_meminfo_t.__mavlink_meminfo_t` as a pure function of its arguments (it reads and writes no memory). -/
def __mavlink_meminfo_t.__mavlink_meminfo_t.pure' (this : UInt64) : Id Unit := do
  return ()

/-- C++ `__mavlink_meminfo_t::__mavlink_meminfo_t : void () noexcept`, `mavlink_msg_meminfo.h:9-?`. -/
def __mavlink_meminfo_t.__mavlink_meminfo_t (this : UInt64) : PMem.M Unit :=
  pure (_root_.Vehicle_lib.__mavlink_meminfo_t.__mavlink_meminfo_t.pure' this)

/-- C++ `mavlink_msg_meminfo_send : void (mavlink_channel_t, uint16_t, uint16_t, uint32_t)`, `mavlink_msg_meminfo.h:205-222`. -/
def mavlink_msg_meminfo_send.body (fp : UInt64) (chan : UInt32) (brkval : UInt16) (freemem : UInt16) (freemem32 : UInt32) : PMem.M Unit := do
  let mut chan := chan
  let mut brkval := brkval
  let mut freemem := freemem
  let mut freemem32 := freemem32
  __mavlink_meminfo_t.__mavlink_meminfo_t (fp + 0)
  PMem.stU16 (fp + 0) brkval
  PMem.stU16 ((fp + 0) + 2) freemem
  PMem.stU32 ((fp + 0) + 4) freemem32
  _mav_finalize_message_chan_send chan (Int32.toUInt32 ((152 : Int32))) (fp + 0) (Int8.toUInt8 (Int32.toInt8 ((4 : Int32)))) (Int8.toUInt8 (Int32.toInt8 ((8 : Int32)))) (Int8.toUInt8 (Int32.toInt8 ((208 : Int32))))
  return ()

def mavlink_msg_meminfo_send (chan : UInt32) (brkval : UInt16) (freemem : UInt16) (freemem32 : UInt32) : PMem.M Unit := do
  let fp ← PMem.enter 8
  let r ← mavlink_msg_meminfo_send.body fp chan brkval freemem freemem32
  PMem.leave fp
  return r

/-- `__mavlink_system_time_t.__mavlink_system_time_t` as a pure function of its arguments (it reads and writes no memory). -/
def __mavlink_system_time_t.__mavlink_system_time_t.pure' (this : UInt64) : Id Unit := do
  return ()

/-- C++ `__mavlink_system_time_t::__mavlink_system_time_t : void () noexcept`, `mavlink_msg_system_time.h:9-?`. -/
def __mavlink_system_time_t.__mavlink_system_time_t (this : UInt64) : PMem.M Unit :=
  pure (_root_.Vehicle_lib.__mavlink_system_time_t.__mavlink_system_time_t.pure' this)

/-- C++ `mavlink_msg_system_time_send : void (mavlink_channel_t, uint64_t, uint32_t)`, `mavlink_msg_system_time.h:192-207`. -/
def mavlink_msg_system_time_send.body (fp : UInt64) (chan : UInt32) (time_unix_usec : UInt64) (time_boot_ms : UInt32) : PMem.M Unit := do
  let mut chan := chan
  let mut time_unix_usec := time_unix_usec
  let mut time_boot_ms := time_boot_ms
  __mavlink_system_time_t.__mavlink_system_time_t (fp + 0)
  PMem.stU64 (fp + 0) time_unix_usec
  PMem.stU32 ((fp + 0) + 8) time_boot_ms
  _mav_finalize_message_chan_send chan (Int32.toUInt32 ((2 : Int32))) (fp + 0) (Int8.toUInt8 (Int32.toInt8 ((12 : Int32)))) (Int8.toUInt8 (Int32.toInt8 ((12 : Int32)))) (Int8.toUInt8 (Int32.toInt8 ((137 : Int32))))
  return ()

def mavlink_msg_system_time_send (chan : UInt32) (time_unix_usec : UInt64) (time_boot_ms : UInt32) : PMem.M Unit := do
  let fp ← PMem.enter 12
  let r ← mavlink_msg_system_time_send.body fp chan time_unix_usec time_boot_ms
  PMem.leave fp
  return r

/-- `__mavlink_local_position_ned_t.__mavlink_local_position_ned_t` as a pure function of its arguments (it reads and writes no memory). -/
def __mavlink_local_position_ned_t.__mavlink_local_position_ned_t.pure' (this : UInt64) : Id Unit := do
  return ()

/-- C++ `__mavlink_local_position_ned_t::__mavlink_local_position_ned_t : void () noexcept`, `mavlink_msg_local_position_ned.h:9-?`. -/
def __mavlink_local_position_ned_t.__mavlink_local_position_ned_t (this : UInt64) : PMem.M Unit :=
  pure (_root_.Vehicle_lib.__mavlink_local_position_ned_t.__mavlink_local_position_ned_t.pure' this)

/-- C++ `mavlink_msg_local_position_ned_send : void (mavlink_channel_t, uint32_t, float, float, float, float, float, float)`, `mavlink_msg_local_position_ned.h:257-282`. -/
def mavlink_msg_local_position_ned_send.body (fp : UInt64) (chan : UInt32) (time_boot_ms : UInt32) (x : Binary32) (y : Binary32) (z : Binary32) (vx : Binary32) (vy : Binary32) (vz : Binary32) : PMem.M Unit := do
  let mut chan := chan
  let mut time_boot_ms := time_boot_ms
  let mut x := x
  let mut y := y
  let mut z := z
  let mut vx := vx
  let mut vy := vy
  let mut vz := vz
  __mavlink_local_position_ned_t.__mavlink_local_position_ned_t (fp + 0)
  PMem.stU32 (fp + 0) time_boot_ms
  PMem.stF32 ((fp + 0) + 4) x
  PMem.stF32 ((fp + 0) + 8) y
  PMem.stF32 ((fp + 0) + 12) z
  PMem.stF32 ((fp + 0) + 16) vx
  PMem.stF32 ((fp + 0) + 20) vy
  PMem.stF32 ((fp + 0) + 24) vz
  _mav_finalize_message_chan_send chan (Int32.toUInt32 ((32 : Int32))) (fp + 0) (Int8.toUInt8 (Int32.toInt8 ((28 : Int32)))) (Int8.toUInt8 (Int32.toInt8 ((28 : Int32)))) (Int8.toUInt8 (Int32.toInt8 ((185 : Int32))))
  return ()

def mavlink_msg_local_position_ned_send (chan : UInt32) (time_boot_ms : UInt32) (x : Binary32) (y : Binary32) (z : Binary32) (vx : Binary32) (vy : Binary32) (vz : Binary32) : PMem.M Unit := do
  let fp ← PMem.enter 28
  let r ← mavlink_msg_local_position_ned_send.body fp chan time_boot_ms x y z vx vy vz
  PMem.leave fp
  return r

/-- `__mavlink_attitude_target_t.__mavlink_attitude_target_t` as a pure function of its arguments (it reads and writes no memory). -/
def __mavlink_attitude_target_t.__mavlink_attitude_target_t.pure' (this : UInt64) : Id Unit := do
  return ()

/-- C++ `__mavlink_attitude_target_t::__mavlink_attitude_target_t : void () noexcept`, `mavlink_msg_attitude_target.h:9-?`. -/
def __mavlink_attitude_target_t.__mavlink_attitude_target_t (this : UInt64) : PMem.M Unit :=
  pure (_root_.Vehicle_lib.__mavlink_attitude_target_t.__mavlink_attitude_target_t.pure' this)

/-- C++ `mavlink_msg_attitude_target_send : void (mavlink_channel_t, uint32_t, uint8_t, const float *, float, float, float, float)`, `mavlink_msg_attitude_target.h:251-274`. -/
def mavlink_msg_attitude_target_send.body (fp : UInt64) (chan : UInt32) (time_boot_ms : UInt32) (type_mask : UInt8) (q : UInt64) (body_roll_rate : Binary32) (body_pitch_rate : Binary32) (body_yaw_rate : Binary32) (thrust : Binary32) : PMem.M Unit := do
  let mut chan := chan
  let mut time_boot_ms := time_boot_ms
  let mut type_mask := type_mask
  let mut q := q
  let mut body_roll_rate := body_roll_rate
  let mut body_pitch_rate := body_pitch_rate
  let mut body_yaw_rate := body_yaw_rate
  let mut thrust := thrust
  __mavlink_attitude_target_t.__mavlink_attitude_target_t (fp + 0)
  PMem.stU32 (fp + 0) time_boot_ms
  PMem.stF32 ((fp + 0) + 20) body_roll_rate
  PMem.stF32 ((fp + 0) + 24) body_pitch_rate
  PMem.stF32 ((fp + 0) + 28) body_yaw_rate
  PMem.stF32 ((fp + 0) + 32) thrust
  PMem.stU8 ((fp + 0) + 36) type_mask
  mav_array_memcpy ((fp + 0) + 4) q ((4 : UInt64) * (Int64.toUInt64 (Int32.toInt64 ((4 : Int32)))))
  _mav_finalize_message_chan_send chan (Int32.toUInt32 ((83 : Int32))) (fp + 0) (Int8.toUInt8 (Int32.toInt8 ((37 : Int32)))) (Int8.toUInt8 (Int32.toInt8 ((37 : Int32)))) (Int8.toUInt8 (Int32.toInt8 ((22 : Int32))))
  return ()

def mavlink_msg_attitude_target_send (chan : UInt32) (time_boot_ms : UInt32) (type_mask : UInt8) (q : UInt64) (body_roll_rate : Binary32) (body_pitch_rate : Binary32) (body_yaw_rate : Binary32) (thrust : Binary32) : PMem.M Unit := do
  let fp ← PMem.enter 37
  let r ← mavlink_msg_attitude_target_send.body fp chan time_boot_ms type_mask q body_roll_rate body_pitch_rate body_yaw_rate thrust
  PMem.leave fp
  return r

/-- `__mavlink_position_target_global_int_t.__mavlink_position_target_global_int_t` as a pure function of its arguments (it reads and writes no memory). -/
def __mavlink_position_target_global_int_t.__mavlink_position_target_global_int_t.pure' (this : UInt64) : Id Unit := do
  return ()

/-- C++ `__mavlink_position_target_global_int_t::__mavlink_position_target_global_int_t : void () noexcept`, `mavlink_msg_position_target_global_int.h:9-?`. -/
def __mavlink_position_target_global_int_t.__mavlink_position_target_global_int_t (this : UInt64) : PMem.M Unit :=
  pure (_root_.Vehicle_lib.__mavlink_position_target_global_int_t.__mavlink_position_target_global_int_t.pure' this)

/-- C++ `mavlink_msg_position_target_global_int_send : void (mavlink_channel_t, uint32_t, uint8_t, uint16_t, int32_t, int32_t, float, float, float, float, float, float, float, float, float)`, `mavlink_msg_position_target_global_int.h:348-387`. -/
def mavlink_msg_position_target_global_int_send.body (fp : UInt64) (chan : UInt32) (time_boot_ms : UInt32) (coordinate_frame : UInt8) (type_mask : UInt16) (lat_int : Int32) (lon_int : Int32) (alt : Binary32) (vx : Binary32) (vy : Binary32) (vz : Binary32) (afx : Binary32) (afy : Binary32) (afz : Binary32) (yaw : Binary32) (yaw_rate : Binary32) : PMem.M Unit := do
  let mut chan := chan
  let mut time_boot_ms := time_boot_ms
  let mut coordinate_frame := coordinate_frame
  let mut type_mask := type_mask
  let mut lat_int := lat_int
  let mut lon_int := lon_int
  let mut alt := alt
  let mut vx := vx
  let mut vy := vy
  let mut vz := vz
  let mut afx := afx
  let mut afy := afy
  let mut afz := afz
  let mut yaw := yaw
  let mut yaw_rate := yaw_rate
  __mavlink_position_target_global_int_t.__mavlink_position_target_global_int_t (fp + 0)
  PMem.stU32 (fp + 0) time_boot_ms
  PMem.stI32 ((fp + 0) + 4) lat_int
  PMem.stI32 ((fp + 0) + 8) lon_int
  PMem.stF32 ((fp + 0) + 12) alt
  PMem.stF32 ((fp + 0) + 16) vx
  PMem.stF32 ((fp + 0) + 20) vy
  PMem.stF32 ((fp + 0) + 24) vz
  PMem.stF32 ((fp + 0) + 28) afx
  PMem.stF32 ((fp + 0) + 32) afy
  PMem.stF32 ((fp + 0) + 36) afz
  PMem.stF32 ((fp + 0) + 40) yaw
  PMem.stF32 ((fp + 0) + 44) yaw_rate
  PMem.stU16 ((fp + 0) + 48) type_mask
  PMem.stU8 ((fp + 0) + 50) coordinate_frame
  _mav_finalize_message_chan_send chan (Int32.toUInt32 ((87 : Int32))) (fp + 0) (Int8.toUInt8 (Int32.toInt8 ((51 : Int32)))) (Int8.toUInt8 (Int32.toInt8 ((51 : Int32)))) (Int8.toUInt8 (Int32.toInt8 ((150 : Int32))))
  return ()

def mavlink_msg_position_target_global_int_send (chan : UInt32) (time_boot_ms : UInt32) (coordinate_frame : UInt8) (type_mask : UInt16) (lat_int : Int32) (lon_int : Int32) (alt : Binary32) (vx : Binary32) (vy : Binary32) (vz : Binary32) (afx : Binary32) (afy : Binary32) (afz : Binary32) (yaw : Binary32) (yaw_rate : Binary32) : PMem.M Unit := do
  let fp ← PMem.enter 51
  let r ← mavlink_msg_position_target_global_int_send.body fp chan time_boot_ms coordinate_frame type_mask lat_int lon_int alt vx vy vz afx afy afz yaw yaw_rate
  PMem.leave fp
  return r

/-- `__mavlink_position_target_local_ned_t.__mavlink_position_target_local_ned_t` as a pure function of its arguments (it reads and writes no memory). -/
def __mavlink_position_target_local_ned_t.__mavlink_position_target_local_ned_t.pure' (this : UInt64) : Id Unit := do
  return ()

/-- C++ `__mavlink_position_target_local_ned_t::__mavlink_position_target_local_ned_t : void () noexcept`, `mavlink_msg_position_target_local_ned.h:9-?`. -/
def __mavlink_position_target_local_ned_t.__mavlink_position_target_local_ned_t (this : UInt64) : PMem.M Unit :=
  pure (_root_.Vehicle_lib.__mavlink_position_target_local_ned_t.__mavlink_position_target_local_ned_t.pure' this)

/-- C++ `mavlink_msg_position_target_local_ned_send : void (mavlink_channel_t, uint32_t, uint8_t, uint16_t, float, float, float, float, float, float, float, float, float, float, float)`, `mavlink_msg_position_target_local_ned.h:348-387`. -/
def mavlink_msg_position_target_local_ned_send.body (fp : UInt64) (chan : UInt32) (time_boot_ms : UInt32) (coordinate_frame : UInt8) (type_mask : UInt16) (x : Binary32) (y : Binary32) (z : Binary32) (vx : Binary32) (vy : Binary32) (vz : Binary32) (afx : Binary32) (afy : Binary32) (afz : Binary32) (yaw : Binary32) (yaw_rate : Binary32) : PMem.M Unit := do
  let mut chan := chan
  let mut time_boot_ms := time_boot_ms
  let mut coordinate_frame := coordinate_frame
  let mut type_mask := type_mask
  let mut x := x
  let mut y := y
  let mut z := z
  let mut vx := vx
  let mut vy := vy
  let mut vz := vz
  let mut afx := afx
  let mut afy := afy
  let mut afz := afz
  let mut yaw := yaw
  let mut yaw_rate := yaw_rate
  __mavlink_position_target_local_ned_t.__mavlink_position_target_local_ned_t (fp + 0)
  PMem.stU32 (fp + 0) time_boot_ms
  PMem.stF32 ((fp + 0) + 4) x
  PMem.stF32 ((fp + 0) + 8) y
  PMem.stF32 ((fp + 0) + 12) z
  PMem.stF32 ((fp + 0) + 16) vx
  PMem.stF32 ((fp + 0) + 20) vy
  PMem.stF32 ((fp + 0) + 24) vz
  PMem.stF32 ((fp + 0) + 28) afx
  PMem.stF32 ((fp + 0) + 32) afy
  PMem.stF32 ((fp + 0) + 36) afz
  PMem.stF32 ((fp + 0) + 40) yaw
  PMem.stF32 ((fp + 0) + 44) yaw_rate
  PMem.stU16 ((fp + 0) + 48) type_mask
  PMem.stU8 ((fp + 0) + 50) coordinate_frame
  _mav_finalize_message_chan_send chan (Int32.toUInt32 ((85 : Int32))) (fp + 0) (Int8.toUInt8 (Int32.toInt8 ((51 : Int32)))) (Int8.toUInt8 (Int32.toInt8 ((51 : Int32)))) (Int8.toUInt8 (Int32.toInt8 ((140 : Int32))))
  return ()

def mavlink_msg_position_target_local_ned_send (chan : UInt32) (time_boot_ms : UInt32) (coordinate_frame : UInt8) (type_mask : UInt16) (x : Binary32) (y : Binary32) (z : Binary32) (vx : Binary32) (vy : Binary32) (vz : Binary32) (afx : Binary32) (afy : Binary32) (afz : Binary32) (yaw : Binary32) (yaw_rate : Binary32) : PMem.M Unit := do
  let fp ← PMem.enter 51
  let r ← mavlink_msg_position_target_local_ned_send.body fp chan time_boot_ms coordinate_frame type_mask x y z vx vy vz afx afy afz yaw yaw_rate
  PMem.leave fp
  return r

/-- `__mavlink_power_status_t.__mavlink_power_status_t` as a pure function of its arguments (it reads and writes no memory). -/
def __mavlink_power_status_t.__mavlink_power_status_t.pure' (this : UInt64) : Id Unit := do
  return ()

/-- C++ `__mavlink_power_status_t::__mavlink_power_status_t : void () noexcept`, `mavlink_msg_power_status.h:9-?`. -/
def __mavlink_power_status_t.__mavlink_power_status_t (this : UInt64) : PMem.M Unit :=
  pure (_root_.Vehicle_lib.__mavlink_power_status_t.__mavlink_power_status_t.pure' this)

/-- C++ `mavlink_msg_power_status_send : void (mavlink_channel_t, uint16_t, uint16_t, uint16_t)`, `mavlink_msg_power_status.h:205-222`. -/
def mavlink_msg_power_status_send.body (fp : UInt64) (chan : UInt32) (Vcc : UInt16) (Vservo : UInt16) (flags : UInt16) : PMem.M Unit := do
  let mut chan := chan
  let mut Vcc := Vcc
  let mut Vservo := Vservo
  let mut flags := flags
  __mavlink_power_status_t.__mavlink_power_status_t (fp + 0)
  PMem.stU16 (fp + 0) Vcc
  PMem.stU16 ((fp + 0) + 2) Vservo
  PMem.stU16 ((fp + 0) + 4) flags
  _mav_finalize_message_chan_send chan (Int32.toUInt32 ((125 : Int32))) (fp + 0) (Int8.toUInt8 (Int32.toInt8 ((6 : Int32)))) (Int8.toUInt8 (Int32.toInt8 ((6 : Int32)))) (Int8.toUInt8 (Int32.toInt8 ((203 : Int32))))
  return ()

def mavlink_msg_power_status_send (chan : UInt32) (Vcc : UInt16) (Vservo : UInt16) (flags : UInt16) : PMem.M Unit := do
  let fp ← PMem.enter 6
  let r ← mavlink_msg_power_status_send.body fp chan Vcc Vservo flags
  PMem.leave fp
  return r

/-- `__mavlink_rc_channels_t.__mavlink_rc_channels_t` as a pure function of its arguments (it reads and writes no memory). -/
def __mavlink_rc_channels_t.__mavlink_rc_channels_t.pure' (this : UInt64) : Id Unit := do
  return ()

/-- C++ `__mavlink_rc_channels_t::__mavlink_rc_channels_t : void () noexcept`, `mavlink_msg_rc_channels.h:9-?`. -/
def __mavlink_rc_channels_t.__mavlink_rc_channels_t (this : UInt64) : PMem.M Unit :=
  pure (_root_.Vehicle_lib.__mavlink_rc_channels_t.__mavlink_rc_channels_t.pure' this)

/-- C++ `mavlink_msg_rc_channels_send : void (mavlink_channel_t, uint32_t, uint8_t, uint16_t, uint16_t, uint16_t, uint16_t, uint16_t, uint16_t, uint16_t, uint16_t, uint16_t, uint16_t, uint16_t, uint16_t, uint16_t, uint16_t, uint16_t, uint16_t, uint16_t, uint16_t, uint8_t)`, `mavlink_msg_rc_channels.h:439-492`. -/
def mavlink_msg_rc_channels_send.body (fp : UInt64) (chan : UInt32) (time_boot_ms : UInt32) (chancount : UInt8) (chan1_raw : UInt16) (chan2_raw : UInt16) (chan3_raw : UInt16) (chan4_raw : UInt16) (chan5_raw : UInt16) (chan6_raw : UInt16) (chan7_raw : UInt16) (chan8_raw : UInt16) (chan9_raw : UInt16) (chan10_raw : UInt16) (chan11_raw : UInt16) (chan12_raw : UInt16) (chan13_raw : UInt16) (chan14_raw : UInt16) (chan15_raw : UInt16) (chan16_raw : UInt16) (chan17_raw : UInt16) (chan18_raw : UInt16) (rssi : UInt8) : PMem.M Unit := do
  let mut chan := chan
  let mut time_boot_ms := time_boot_ms
  let mut chancount := chancount
  let mut chan1_raw := chan1_raw
  let mut chan2_raw := chan2_raw
  let mut chan3_raw := chan3_raw
  let mut chan4_raw := chan4_raw
  let mut chan5_raw := chan5_raw
  let mut chan6_raw := chan6_raw
  let mut chan7_raw := chan7_raw
  let mut chan8_raw := chan8_raw
  let mut chan9_raw := chan9_raw
  let mut chan10_raw := chan10_raw
  let mut chan11_raw := chan11_raw
  let mut chan12_raw := chan12_raw
  let mut chan13_raw := chan13_raw
  let mut chan14_raw := chan14_raw
  let mut chan15_raw := chan15_raw
  let mut chan16_raw := chan16_raw
  let mut chan17_raw := chan17_raw
  let mut chan18_raw := chan18_raw
  let mut rssi := rssi
  __mavlink_rc_channels_t.__mavlink_rc_channels_t (fp + 0)
  PMem.stU32 (fp + 0) time_boot_ms
  PMem.stU16 ((fp + 0) + 4) chan1_raw
  PMem.stU16 ((fp + 0) + 6) chan2_raw
  PMem.stU16 ((fp + 0) + 8) chan3_raw
  PMem.stU16 ((fp + 0) + 10) chan4_raw
  PMem.stU16 ((fp + 0) + 12) chan5_raw
  PMem.stU16 ((fp + 0) + 14) chan6_raw
  PMem.stU16 ((fp + 0) + 16) chan7_raw
  PMem.stU16 ((fp + 0) + 18) chan8_raw
  PMem.stU16 ((fp + 0) + 20) chan9_raw
  PMem.stU16 ((fp + 0) + 22) chan10_raw
  PMem.stU16 ((fp + 0) + 24) chan11_raw
  PMem.stU16 ((fp + 0) + 26) chan12_raw
  PMem.stU16 ((fp + 0) + 28) chan13_raw
  PMem.stU16 ((fp + 0) + 30) chan14_raw
  PMem.stU16 ((fp + 0) + 32) chan15_raw
  PMem.stU16 ((fp + 0) + 34) chan16_raw
  PMem.stU16 ((fp + 0) + 36) chan17_raw
  PMem.stU16 ((fp + 0) + 38) chan18_raw
  PMem.stU8 ((fp + 0) + 40) chancount
  PMem.stU8 ((fp + 0) + 41) rssi
  _mav_finalize_message_chan_send chan (Int32.toUInt32 ((65 : Int32))) (fp + 0) (Int8.toUInt8 (Int32.toInt8 ((42 : Int32)))) (Int8.toUInt8 (Int32.toInt8 ((42 : Int32)))) (Int8.toUInt8 (Int32.toInt8 ((118 : Int32))))
  return ()

def mavlink_msg_rc_channels_send (chan : UInt32) (time_boot_ms : UInt32) (chancount : UInt8) (chan1_raw : UInt16) (chan2_raw : UInt16) (chan3_raw : UInt16) (chan4_raw : UInt16) (chan5_raw : UInt16) (chan6_raw : UInt16) (chan7_raw : UInt16) (chan8_raw : UInt16) (chan9_raw : UInt16) (chan10_raw : UInt16) (chan11_raw : UInt16) (chan12_raw : UInt16) (chan13_raw : UInt16) (chan14_raw : UInt16) (chan15_raw : UInt16) (chan16_raw : UInt16) (chan17_raw : UInt16) (chan18_raw : UInt16) (rssi : UInt8) : PMem.M Unit := do
  let fp ← PMem.enter 42
  let r ← mavlink_msg_rc_channels_send.body fp chan time_boot_ms chancount chan1_raw chan2_raw chan3_raw chan4_raw chan5_raw chan6_raw chan7_raw chan8_raw chan9_raw chan10_raw chan11_raw chan12_raw chan13_raw chan14_raw chan15_raw chan16_raw chan17_raw chan18_raw rssi
  PMem.leave fp
  return r

/-- `__mavlink_rc_channels_raw_t.__mavlink_rc_channels_raw_t` as a pure function of its arguments (it reads and writes no memory). -/
def __mavlink_rc_channels_raw_t.__mavlink_rc_channels_raw_t.pure' (this : UInt64) : Id Unit := do
  return ()

/-- C++ `__mavlink_rc_channels_raw_t::__mavlink_rc_channels_raw_t : void () noexcept`, `mavlink_msg_rc_channels_raw.h:9-?`. -/
def __mavlink_rc_channels_raw_t.__mavlink_rc_channels_raw_t (this : UInt64) : PMem.M Unit :=
  pure (_root_.Vehicle_lib.__mavlink_rc_channels_raw_t.__mavlink_rc_channels_raw_t.pure' this)

/-- C++ `mavlink_msg_rc_channels_raw_send : void (mavlink_channel_t, uint32_t, uint8_t, uint16_t, uint16_t, uint16_t, uint16_t, uint16_t, uint16_t, uint16_t, uint16_t, uint8_t)`, `mavlink_msg_rc_channels_raw.h:309-342`. -/
def mavlink_msg_rc_channels_raw_send.body (fp : UInt64) (chan : UInt32) (time_boot_ms : UInt32) (port : UInt8) (chan1_raw : UInt16) (chan2_raw : UInt16) (chan3_raw : UInt16) (chan4_raw : UInt16) (chan5_raw : UInt16) (chan6_raw : UInt16) (chan7_raw : UInt16) (chan8_raw : UInt16) (rssi : UInt8) : PMem.M Unit := do
  let mut chan := chan
  let mut time_boot_ms := time_boot_ms
  let mut port := port
  let mut chan1_raw := chan1_raw
  let mut chan2_raw := chan2_raw
  let mut chan3_raw := chan3_raw
  let mut chan4_raw := chan4_raw
  let mut chan5_raw := chan5_raw
  let mut chan6_raw := chan6_raw
  let mut chan7_raw := chan7_raw
  let mut chan8_raw := chan8_raw
  let mut rssi := rssi
  __mavlink_rc_channels_raw_t.__mavlink_rc_channels_raw_t (fp + 0)
  PMem.stU32 (fp + 0) time_boot_ms
  PMem.stU16 ((fp + 0) + 4) chan1_raw
  PMem.stU16 ((fp + 0) + 6) chan2_raw
  PMem.stU16 ((fp + 0) + 8) chan3_raw
  PMem.stU16 ((fp + 0) + 10) chan4_raw
  PMem.stU16 ((fp + 0) + 12) chan5_raw
  PMem.stU16 ((fp + 0) + 14) chan6_raw
  PMem.stU16 ((fp + 0) + 16) chan7_raw
  PMem.stU16 ((fp + 0) + 18) chan8_raw
  PMem.stU8 ((fp + 0) + 20) port
  PMem.stU8 ((fp + 0) + 21) rssi
  _mav_finalize_message_chan_send chan (Int32.toUInt32 ((35 : Int32))) (fp + 0) (Int8.toUInt8 (Int32.toInt8 ((22 : Int32)))) (Int8.toUInt8 (Int32.toInt8 ((22 : Int32)))) (Int8.toUInt8 (Int32.toInt8 ((244 : Int32))))
  return ()

def mavlink_msg_rc_channels_raw_send (chan : UInt32) (time_boot_ms : UInt32) (port : UInt8) (chan1_raw : UInt16) (chan2_raw : UInt16) (chan3_raw : UInt16) (chan4_raw : UInt16) (chan5_raw : UInt16) (chan6_raw : UInt16) (chan7_raw : UInt16) (chan8_raw : UInt16) (rssi : UInt8) : PMem.M Unit := do
  let fp ← PMem.enter 22
  let r ← mavlink_msg_rc_channels_raw_send.body fp chan time_boot_ms port chan1_raw chan2_raw chan3_raw chan4_raw chan5_raw chan6_raw chan7_raw chan8_raw rssi
  PMem.leave fp
  return r

/-- `__mavlink_raw_imu_t.__mavlink_raw_imu_t` as a pure function of its arguments (it reads and writes no memory). -/
def __mavlink_raw_imu_t.__mavlink_raw_imu_t.pure' (this : UInt64) : Id Unit := do
  return ()

/-- C++ `__mavlink_raw_imu_t::__mavlink_raw_imu_t : void () noexcept`, `mavlink_types.h:?-?`. -/
def __mavlink_raw_imu_t.__mavlink_raw_imu_t (this : UInt64) : PMem.M Unit :=
  pure (_root_.Vehicle_lib.__mavlink_raw_imu_t.__mavlink_raw_imu_t.pure' this)

/-- C++ `mavlink_msg_raw_imu_send : void (mavlink_channel_t, uint64_t, int16_t, int16_t, int16_t, int16_t, int16_t, int16_t, int16_t, int16_t, int16_t, uint8_t, int16_t)`, `mavlink_msg_raw_imu.h:322-357`. -/
def mavlink_msg_raw_imu_send.body (fp : UInt64) (chan : UInt32) (time_usec : UInt64) (xacc : Int16) (yacc : Int16) (zacc : Int16) (xgyro : Int16) (ygyro : Int16) (zgyro : Int16) (xmag : Int16) (ymag : Int16) (zmag : Int16) (id : UInt8) (temperature : Int16) : PMem.M Unit := do
  let mut chan := chan
  let mut time_usec := time_usec
  let mut xacc := xacc
  let mut yacc := yacc
  let mut zacc := zacc
  let mut xgyro := xgyro
  let mut ygyro := ygyro
  let mut zgyro := zgyro
  let mut xmag := xmag
  let mut ymag := ymag
  let mut zmag := zmag
  let mut id := id
  let mut temperature := temperature
  __mavlink_raw_imu_t.__mavlink_raw_imu_t (fp + 0)
  PMem.stU64 (fp + 0) time_usec
  PMem.stI16 ((fp + 0) + 8) xacc
  PMem.stI16 ((fp + 0) + 10) yacc
  PMem.stI16 ((fp + 0) + 12) zacc
  PMem.stI16 ((fp + 0) + 14) xgyro
  PMem.stI16 ((fp + 0) + 16) ygyro
  PMem.stI16 ((fp + 0) + 18) zgyro
  PMem.stI16 ((fp + 0) + 20) xmag
  PMem.stI16 ((fp + 0) + 22) ymag
  PMem.stI16 ((fp + 0) + 24) zmag
  PMem.stU8 ((fp + 0) + 26) id
  PMem.stI16 ((fp + 0) + 27) temperature
  _mav_finalize_message_chan_send chan (Int32.toUInt32 ((27 : Int32))) (fp + 0) (Int8.toUInt8 (Int32.toInt8 ((26 : Int32)))) (Int8.toUInt8 (Int32.toInt8 ((29 : Int32)))) (Int8.toUInt8 (Int32.toInt8 ((144 : Int32))))
  return ()

def mavlink_msg_raw_imu_send (chan : UInt32) (time_usec : UInt64) (xacc : Int16) (yacc : Int16) (zacc : Int16) (xgyro : Int16) (ygyro : Int16) (zgyro : Int16) (xmag : Int16) (ymag : Int16) (zmag : Int16) (id : UInt8) (temperature : Int16) : PMem.M Unit := do
  let fp ← PMem.enter 29
  let r ← mavlink_msg_raw_imu_send.body fp chan time_usec xacc yacc zacc xgyro ygyro zgyro xmag ymag zmag id temperature
  PMem.leave fp
  return r

/-- C++ `mavlink_msg_highres_imu_send_struct : void (mavlink_channel_t, const mavlink_highres_imu_t *)`, `mavlink_msg_highres_imu.h:424-431`. -/
def mavlink_msg_highres_imu_send_struct (chan : UInt32) (highres_imu : UInt64) : PMem.M Unit := do
  let mut chan := chan
  let mut highres_imu := highres_imu
  _mav_finalize_message_chan_send chan (Int32.toUInt32 ((105 : Int32))) highres_imu (Int8.toUInt8 (Int32.toInt8 ((62 : Int32)))) (Int8.toUInt8 (Int32.toInt8 ((63 : Int32)))) (Int8.toUInt8 (Int32.toInt8 ((93 : Int32))))
  return ()

/-- `__mavlink_scaled_pressure_t.__mavlink_scaled_pressure_t` as a pure function of its arguments (it reads and writes no memory). -/
def __mavlink_scaled_pressure_t.__mavlink_scaled_pressure_t.pure' (this : UInt64) : Id Unit := do
  return ()

/-- C++ `__mavlink_scaled_pressure_t::__mavlink_scaled_pressure_t : void () noexcept`, `mavlink_msg_scaled_pressure.h:9-?`. -/
def __mavlink_scaled_pressure_t.__mavlink_scaled_pressure_t (this : UInt64) : PMem.M Unit :=
  pure (_root_.Vehicle_lib.__mavlink_scaled_pressure_t.__mavlink_scaled_pressure_t.pure' this)

/-- C++ `mavlink_msg_scaled_pressure_send : void (mavlink_channel_t, uint32_t, float, float, int16_t, int16_t)`, `mavlink_msg_scaled_pressure.h:231-252`. -/
def mavlink_msg_scaled_pressure_send.body (fp : UInt64) (chan : UInt32) (time_boot_ms : UInt32) (press_abs : Binary32) (press_diff : Binary32) (temperature : Int16) (temperature_press_diff : Int16) : PMem.M Unit := do
  let mut chan := chan
  let mut time_boot_ms := time_boot_ms
  let mut press_abs := press_abs
  let mut press_diff := press_diff
  let mut temperature := temperature
  let mut temperature_press_diff := temperature_press_diff
  __mavlink_scaled_pressure_t.__mavlink_scaled_pressure_t (fp + 0)
  PMem.stU32 (fp + 0) time_boot_ms
  PMem.stF32 ((fp + 0) + 4) press_abs
  PMem.stF32 ((fp + 0) + 8) press_diff
  PMem.stI16 ((fp + 0) + 12) temperature
  PMem.stI16 ((fp + 0) + 14) temperature_press_diff
  _mav_finalize_message_chan_send chan (Int32.toUInt32 ((29 : Int32))) (fp + 0) (Int8.toUInt8 (Int32.toInt8 ((14 : Int32)))) (Int8.toUInt8 (Int32.toInt8 ((16 : Int32)))) (Int8.toUInt8 (Int32.toInt8 ((115 : Int32))))
  return ()

def mavlink_msg_scaled_pressure_send (chan : UInt32) (time_boot_ms : UInt32) (press_abs : Binary32) (press_diff : Binary32) (temperature : Int16) (temperature_press_diff : Int16) : PMem.M Unit := do
  let fp ← PMem.enter 16
  let r ← mavlink_msg_scaled_pressure_send.body fp chan time_boot_ms press_abs press_diff temperature temperature_press_diff
  PMem.leave fp
  return r

/-- `__mavlink_scaled_pressure2_t.__mavlink_scaled_pressure2_t` as a pure function of its arguments (it reads and writes no memory). -/
def __mavlink_scaled_pressure2_t.__mavlink_scaled_pressure2_t.pure' (this : UInt64) : Id Unit := do
  return ()

/-- C++ `__mavlink_scaled_pressure2_t::__mavlink_scaled_pressure2_t : void () noexcept`, `mavlink_msg_scaled_pressure2.h:9-?`. -/
def __mavlink_scaled_pressure2_t.__mavlink_scaled_pressure2_t (this : UInt64) : PMem.M Unit :=
  pure (_root_.Vehicle_lib.__mavlink_scaled_pressure2_t.__mavlink_scaled_pressure2_t.pure' this)

/-- C++ `mavlink_msg_scaled_pressure2_send : void (mavlink_channel_t, uint32_t, float, float, int16_t, int16_t)`, `mavlink_msg_scaled_pressure2.h:231-252`. -/
def mavlink_msg_scaled_pressure2_send.body (fp : UInt64) (chan : UInt32) (time_boot_ms : UInt32) (press_abs : Binary32) (press_diff : Binary32) (temperature : Int16) (temperature_press_diff : Int16) : PMem.M Unit := do
  let mut chan := chan
  let mut time_boot_ms := time_boot_ms
  let mut press_abs := press_abs
  let mut press_diff := press_diff
  let mut temperature := temperature
  let mut temperature_press_diff := temperature_press_diff
  __mavlink_scaled_pressure2_t.__mavlink_scaled_pressure2_t (fp + 0)
  PMem.stU32 (fp + 0) time_boot_ms
  PMem.stF32 ((fp + 0) + 4) press_abs
  PMem.stF32 ((fp + 0) + 8) press_diff
  PMem.stI16 ((fp + 0) + 12) temperature
  PMem.stI16 ((fp + 0) + 14) temperature_press_diff
  _mav_finalize_message_chan_send chan (Int32.toUInt32 ((137 : Int32))) (fp + 0) (Int8.toUInt8 (Int32.toInt8 ((14 : Int32)))) (Int8.toUInt8 (Int32.toInt8 ((16 : Int32)))) (Int8.toUInt8 (Int32.toInt8 ((195 : Int32))))
  return ()

def mavlink_msg_scaled_pressure2_send (chan : UInt32) (time_boot_ms : UInt32) (press_abs : Binary32) (press_diff : Binary32) (temperature : Int16) (temperature_press_diff : Int16) : PMem.M Unit := do
  let fp ← PMem.enter 16
  let r ← mavlink_msg_scaled_pressure2_send.body fp chan time_boot_ms press_abs press_diff temperature temperature_press_diff
  PMem.leave fp
  return r

/-- `__mavlink_scaled_pressure3_t.__mavlink_scaled_pressure3_t` as a pure function of its arguments (it reads and writes no memory). -/
def __mavlink_scaled_pressure3_t.__mavlink_scaled_pressure3_t.pure' (this : UInt64) : Id Unit := do
  return ()

/-- C++ `__mavlink_scaled_pressure3_t::__mavlink_scaled_pressure3_t : void () noexcept`, `mavlink_msg_scaled_pressure3.h:9-?`. -/
def __mavlink_scaled_pressure3_t.__mavlink_scaled_pressure3_t (this : UInt64) : PMem.M Unit :=
  pure (_root_.Vehicle_lib.__mavlink_scaled_pressure3_t.__mavlink_scaled_pressure3_t.pure' this)

/-- C++ `mavlink_msg_scaled_pressure3_send : void (mavlink_channel_t, uint32_t, float, float, int16_t, int16_t)`, `mavlink_msg_scaled_pressure3.h:231-252`. -/
def mavlink_msg_scaled_pressure3_send.body (fp : UInt64) (chan : UInt32) (time_boot_ms : UInt32) (press_abs : Binary32) (press_diff : Binary32) (temperature : Int16) (temperature_press_diff : Int16) : PMem.M Unit := do
  let mut chan := chan
  let mut time_boot_ms := time_boot_ms
  let mut press_abs := press_abs
  let mut press_diff := press_diff
  let mut temperature := temperature
  let mut temperature_press_diff := temperature_press_diff
  __mavlink_scaled_pressure3_t.__mavlink_scaled_pressure3_t (fp + 0)
  PMem.stU32 (fp + 0) time_boot_ms
  PMem.stF32 ((fp + 0) + 4) press_abs
  PMem.stF32 ((fp + 0) + 8) press_diff
  PMem.stI16 ((fp + 0) + 12) temperature
  PMem.stI16 ((fp + 0) + 14) temperature_press_diff
  _mav_finalize_message_chan_send chan (Int32.toUInt32 ((143 : Int32))) (fp + 0) (Int8.toUInt8 (Int32.toInt8 ((14 : Int32)))) (Int8.toUInt8 (Int32.toInt8 ((16 : Int32)))) (Int8.toUInt8 (Int32.toInt8 ((131 : Int32))))
  return ()

def mavlink_msg_scaled_pressure3_send (chan : UInt32) (time_boot_ms : UInt32) (press_abs : Binary32) (press_diff : Binary32) (temperature : Int16) (temperature_press_diff : Int16) : PMem.M Unit := do
  let fp ← PMem.enter 16
  let r ← mavlink_msg_scaled_pressure3_send.body fp chan time_boot_ms press_abs press_diff temperature temperature_press_diff
  PMem.leave fp
  return r

/-- `__mavlink_servo_output_raw_t.__mavlink_servo_output_raw_t` as a pure function of its arguments (it reads and writes no memory). -/
def __mavlink_servo_output_raw_t.__mavlink_servo_output_raw_t.pure' (this : UInt64) : Id Unit := do
  return ()

/-- C++ `__mavlink_servo_output_raw_t::__mavlink_servo_output_raw_t : void () noexcept`, `mavlink_types.h:?-?`. -/
def __mavlink_servo_output_raw_t.__mavlink_servo_output_raw_t (this : UInt64) : PMem.M Unit :=
  pure (_root_.Vehicle_lib.__mavlink_servo_output_raw_t.__mavlink_servo_output_raw_t.pure' this)

/-- C++ `mavlink_msg_servo_output_raw_send : void (mavlink_channel_t, uint32_t, uint8_t, uint16_t, uint16_t, uint16_t, uint16_t, uint16_t, uint16_t, uint16_t, uint16_t, uint16_t, uint16_t, uint16_t, uint16_t, uint16_t, uint16_t, uint16_t, uint16_t)`, `mavlink_msg_servo_output_raw.h:400-447`. -/
def mavlink_msg_servo_output_raw_send.body (fp : UInt64) (chan : UInt32) (time_usec : UInt32) (port : UInt8) (servo1_raw : UInt16) (servo2_raw : UInt16) (servo3_raw : UInt16) (servo4_raw : UInt16) (servo5_raw : UInt16) (servo6_raw : UInt16) (servo7_raw : UInt16) (servo8_raw : UInt16) (servo9_raw : UInt16) (servo10_raw : UInt16) (servo11_raw : UInt16) (servo12_raw : UInt16) (servo13_raw : UInt16) (servo14_raw : UInt16) (servo15_raw : UInt16) (servo16_raw : UInt16) : PMem.M Unit := do
  let mut chan := chan
  let mut time_usec := time_usec
  let mut port := port
  let mut servo1_raw := servo1_raw
  let mut servo2_raw := servo2_raw
  let mut servo3_raw := servo3_raw
  let mut servo4_raw := servo4_raw
  let mut servo5_raw := servo5_raw
  let mut servo6_raw := servo6_raw
  let mut servo7_raw := servo7_raw
  let mut servo8_raw := servo8_raw
  let mut servo9_raw := servo9_raw
  let mut servo10_raw := servo10_raw
  let mut servo11_raw := servo11_raw
  let mut servo12_raw := servo12_raw
  let mut servo13_raw := servo13_raw
  let mut servo14_raw := servo14_raw
  let mut servo15_raw := servo15_raw
  let mut servo16_raw := servo16_raw
  __mavlink_servo_output_raw_t.__mavlink_servo_output_raw_t (fp + 0)
  PMem.stU32 (fp + 0) time_usec
  PMem.stU16 ((fp + 0) + 4) servo1_raw
  PMem.stU16 ((fp + 0) + 6) servo2_raw
  PMem.stU16 ((fp + 0) + 8) servo3_raw
  PMem.stU16 ((fp + 0) + 10) servo4_raw
  PMem.stU16 ((fp + 0) + 12) servo5_raw
  PMem.stU16 ((fp + 0) + 14) servo6_raw
  PMem.stU16 ((fp + 0) + 16) servo7_raw
  PMem.stU16 ((fp + 0) + 18) servo8_raw
  PMem.stU8 ((fp + 0) + 20) port
  PMem.stU16 ((fp + 0) + 21) servo9_raw
  PMem.stU16 ((fp + 0) + 23) servo10_raw
  PMem.stU16 ((fp + 0) + 25) servo11_raw
  PMem.stU16 ((fp + 0) + 27) servo12_raw
  PMem.stU16 ((fp + 0) + 29) servo13_raw
  PMem.stU16 ((fp + 0) + 31) servo14_raw
  PMem.stU16 ((fp + 0) + 33) servo15_raw
  PMem.stU16 ((fp + 0) + 35) servo16_raw
  _mav_finalize_message_chan_send chan (Int32.toUInt32 ((36 : Int32))) (fp + 0) (Int8.toUInt8 (Int32.toInt8 ((21 : Int32)))) (Int8.toUInt8 (Int32.toInt8 ((37 : Int32)))) (Int8.toUInt8 (Int32.toInt8 ((222 : Int32))))
  return ()

def mavlink_msg_servo_output_raw_send (chan : UInt32) (time_usec : UInt32) (port : UInt8) (servo1_raw : UInt16) (servo2_raw : UInt16) (servo3_raw : UInt16) (servo4_raw : UInt16) (servo5_raw : UInt16) (servo6_raw : UInt16) (servo7_raw : UInt16) (servo8_raw : UInt16) (servo9_raw : UInt16) (servo10_raw : UInt16) (servo11_raw : UInt16) (servo12_raw : UInt16) (servo13_raw : UInt16) (servo14_raw : UInt16) (servo15_raw : UInt16) (servo16_raw : UInt16) : PMem.M Unit := do
  let fp ← PMem.enter 37
  let r ← mavlink_msg_servo_output_raw_send.body fp chan time_usec port servo1_raw servo2_raw servo3_raw servo4_raw servo5_raw servo6_raw servo7_raw servo8_raw servo9_raw servo10_raw servo11_raw servo12_raw servo13_raw servo14_raw servo15_raw servo16_raw
  PMem.leave fp
  return r

/-- `__mavlink_sys_status_t.__mavlink_sys_status_t` as a pure function of its arguments (it reads and writes no memory). -/
def __mavlink_sys_status_t.__mavlink_sys_status_t.pure' (this : UInt64) : Id Unit := do
  return ()

/-- C++ `__mavlink_sys_status_t::__mavlink_sys_status_t : void () noexcept`, `mavlink_types.h:?-?`. -/
def __mavlink_sys_status_t.__mavlink_sys_status_t (this : UInt64) : PMem.M Unit :=
  pure (_root_.Vehicle_lib.__mavlink_sys_status_t.__mavlink_sys_status_t.pure' this)

/-- C++ `mavlink_msg_sys_status_send : void (mavlink_channel_t, uint32_t, uint32_t, uint32_t, uint16_t, uint16_t, int16_t, int8_t, uint16_t, uint16_t, uint16_t, uint16_t, uint16_t, uint16_t, uint32_t, uint32_t, uint32_t)`, `mavlink_msg_sys_status.h:374-417`. -/
def mavlink_msg_sys_status_send.body (fp : UInt64) (chan : UInt32) (onboard_control_sensors_present : UInt32) (onboard_control_sensors_enabled : UInt32) (onboard_control_sensors_health : UInt32) (load : UInt16) (voltage_battery : UInt16) (current_battery : Int16) (battery_remaining : Int8) (drop_rate_comm : UInt16) (errors_comm : UInt16) (errors_count1 : UInt16) (errors_count2 : UInt16) (errors_count3 : UInt16) (errors_count4 : UInt16) (onboard_control_sensors_present_extended : UInt32) (onboard_control_sensors_enabled_extended : UInt32) (onboard_control_sensors_health_extended : UInt32) : PMem.M Unit := do
  let mut chan := chan
  let mut onboard_control_sensors_present := onboard_control_sensors_present
  let mut onboard_control_sensors_enabled := onboard_control_sensors_enabled
  let mut onboard_control_sensors_health := onboard_control_sensors_health
  let mut load := load
  let mut voltage_battery := voltage_battery
  let mut current_battery := current_battery
  let mut battery_remaining := battery_remaining
  let mut drop_rate_comm := drop_rate_comm
  let mut errors_comm := errors_comm
  let mut errors_count1 := errors_count1
  let mut errors_count2 := errors_count2
  let mut errors_count3 := errors_count3
  let mut errors_count4 := errors_count4
  let mut onboard_control_sensors_present_extended := onboard_control_sensors_present_extended
  let mut onboard_control_sensors_enabled_extended := onboard_control_sensors_enabled_extended
  let mut onboard_control_sensors_health_extended := onboard_control_sensors_health_extended
  __mavlink_sys_status_t.__mavlink_sys_status_t (fp + 0)
  PMem.stU32 (fp + 0) onboard_control_sensors_present
  PMem.stU32 ((fp + 0) + 4) onboard_control_sensors_enabled
  PMem.stU32 ((fp + 0) + 8) onboard_control_sensors_health
  PMem.stU16 ((fp + 0) + 12) load
  PMem.stU16 ((fp + 0) + 14) voltage_battery
  PMem.stI16 ((fp + 0) + 16) current_battery
  PMem.stU16 ((fp + 0) + 18) drop_rate_comm
  PMem.stU16 ((fp + 0) + 20) errors_comm
  PMem.stU16 ((fp + 0) + 22) errors_count1
  PMem.stU16 ((fp + 0) + 24) errors_count2
  PMem.stU16 ((fp + 0) + 26) errors_count3
  PMem.stU16 ((fp + 0) + 28) errors_count4
  PMem.stI8 ((fp + 0) + 30) battery_remaining
  PMem.stU32 ((fp + 0) + 31) onboard_control_sensors_present_extended
  PMem.stU32 ((fp + 0) + 35) onboard_control_sensors_enabled_extended
  PMem.stU32 ((fp + 0) + 39) onboard_control_sensors_health_extended
  _mav_finalize_message_chan_send chan (Int32.toUInt32 ((1 : Int32))) (fp + 0) (Int8.toUInt8 (Int32.toInt8 ((31 : Int32)))) (Int8.toUInt8 (Int32.toInt8 ((43 : Int32)))) (Int8.toUInt8 (Int32.toInt8 ((124 : Int32))))
  return ()

def mavlink_msg_sys_status_send (chan : UInt32) (onboard_control_sensors_present : UInt32) (onboard_control_sensors_enabled : UInt32) (onboard_control_sensors_health : UInt32) (load : UInt16) (voltage_battery : UInt16) (current_battery : Int16) (battery_remaining : Int8) (drop_rate_comm : UInt16) (errors_comm : UInt16) (errors_count1 : UInt16) (errors_count2 : UInt16) (errors_count3 : UInt16) (errors_count4 : UInt16) (onboard_control_sensors_present_extended : UInt32) (onboard_control_sensors_enabled_extended : UInt32) (onboard_control_sensors_health_extended : UInt32) : PMem.M Unit := do
  let fp ← PMem.enter 43
  let r ← mavlink_msg_sys_status_send.body fp chan onboard_control_sensors_present onboard_control_sensors_enabled onboard_control_sensors_health load voltage_battery current_battery battery_remaining drop_rate_comm errors_comm errors_count1 errors_count2 errors_count3 errors_count4 onboard_control_sensors_present_extended onboard_control_sensors_enabled_extended onboard_control_sensors_health_extended
  PMem.leave fp
  return r

/-- `__mavlink_ahrs2_t.__mavlink_ahrs2_t` as a pure function of its arguments (it reads and writes no memory). -/
def __mavlink_ahrs2_t.__mavlink_ahrs2_t.pure' (this : UInt64) : Id Unit := do
  return ()

/-- C++ `__mavlink_ahrs2_t::__mavlink_ahrs2_t : void () noexcept`, `mavlink_msg_ahrs2.h:9-?`. -/
def __mavlink_ahrs2_t.__mavlink_ahrs2_t (this : UInt64) : PMem.M Unit :=
  pure (_root_.Vehicle_lib.__mavlink_ahrs2_t.__mavlink_ahrs2_t.pure' this)

/-- C++ `mavlink_msg_ahrs2_send : void (mavlink_channel_t, float, float, float, float, int32_t, int32_t)`, `mavlink_msg_ahrs2.h:244-267`. -/
def mavlink_msg_ahrs2_send.body (fp : UInt64) (chan : UInt32) (roll : Binary32) (pitch : Binary32) (yaw : Binary32) (altitude : Binary32) (lat : Int32) (lng : Int32) : PMem.M Unit := do
  let mut chan := chan
  let mut roll := roll
  let mut pitch := pitch
  let mut yaw := yaw
  let mut altitude := altitude
  let mut lat := lat
  let mut lng := lng
  __mavlink_ahrs2_t.__mavlink_ahrs2_t (fp + 0)
  PMem.stF32 (fp + 0) roll
  PMem.stF32 ((fp + 0) + 4) pitch
  PMem.stF32 ((fp + 0) + 8) yaw
  PMem.stF32 ((fp + 0) + 12) altitude
  PMem.stI32 ((fp + 0) + 16) lat
  PMem.stI32 ((fp + 0) + 20) lng
  _mav_finalize_message_chan_send chan (Int32.toUInt32 ((178 : Int32))) (fp + 0) (Int8.toUInt8 (Int32.toInt8 ((24 : Int32)))) (Int8.toUInt8 (Int32.toInt8 ((24 : Int32)))) (Int8.toUInt8 (Int32.toInt8 ((47 : Int32))))
  return ()

def mavlink_msg_ahrs2_send (chan : UInt32) (roll : Binary32) (pitch : Binary32) (yaw : Binary32) (altitude : Binary32) (lat : Int32) (lng : Int32) : PMem.M Unit := do
  let fp ← PMem.enter 24
  let r ← mavlink_msg_ahrs2_send.body fp chan roll pitch yaw altitude lat lng
  PMem.leave fp
  return r

/-- `__mavlink_pid_tuning_t.__mavlink_pid_tuning_t` as a pure function of its arguments (it reads and writes no memory). -/
def __mavlink_pid_tuning_t.__mavlink_pid_tuning_t.pure' (this : UInt64) : Id Unit := do
  return ()

/-- C++ `__mavlink_pid_tuning_t::__mavlink_pid_tuning_t : void () noexcept`, `mavlink_types.h:?-?`. -/
def __mavlink_pid_tuning_t.__mavlink_pid_tuning_t (this : UInt64) : PMem.M Unit :=
  pure (_root_.Vehicle_lib.__mavlink_pid_tuning_t.__mavlink_pid_tuning_t.pure' this)

/-- C++ `mavlink_msg_pid_tuning_send : void (mavlink_channel_t, uint8_t, float, float, float, float, float, float, float, float)`, `mavlink_msg_pid_tuning.h:283-312`. -/
def mavlink_msg_pid_tuning_send.body (fp : UInt64) (chan : UInt32) (axis : UInt8) (desired : Binary32) (achieved : Binary32) (FF : Binary32) (P : Binary32) (I : Binary32) (D : Binary32) (SRate : Binary32) (PDmod : Binary32) : PMem.M Unit := do
  let mut chan := chan
  let mut axis := axis
  let mut desired := desired
  let mut achieved := achieved
  let mut FF := FF
  let mut P := P
  let mut I := I
  let mut D := D
  let mut SRate := SRate
  let mut PDmod := PDmod
  __mavlink_pid_tuning_t.__mavlink_pid_tuning_t (fp + 0)
  PMem.stF32 (fp + 0) desired
  PMem.stF32 ((fp + 0) + 4) achieved
  PMem.stF32 ((fp + 0) + 8) FF
  PMem.stF32 ((fp + 0) + 12) P
  PMem.stF32 ((fp + 0) + 16) I
  PMem.stF32 ((fp + 0) + 20) D
  PMem.stU8 ((fp + 0) + 24) axis
  PMem.stF32 ((fp + 0) + 25) SRate
  PMem.stF32 ((fp + 0) + 29) PDmod
  _mav_finalize_message_chan_send chan (Int32.toUInt32 ((194 : Int32))) (fp + 0) (Int8.toUInt8 (Int32.toInt8 ((25 : Int32)))) (Int8.toUInt8 (Int32.toInt8 ((33 : Int32)))) (Int8.toUInt8 (Int32.toInt8 ((98 : Int32))))
  return ()

def mavlink_msg_pid_tuning_send (chan : UInt32) (axis : UInt8) (desired : Binary32) (achieved : Binary32) (FF : Binary32) (P : Binary32) (I : Binary32) (D : Binary32) (SRate : Binary32) (PDmod : Binary32) : PMem.M Unit := do
  let fp ← PMem.enter 33
  let r ← mavlink_msg_pid_tuning_send.body fp chan axis desired achieved FF P I D SRate PDmod
  PMem.leave fp
  return r

/-- `__mavlink_nav_controller_output_t.__mavlink_nav_controller_output_t` as a pure function of its arguments (it reads and writes no memory). -/
def __mavlink_nav_controller_output_t.__mavlink_nav_controller_output_t.pure' (this : UInt64) : Id Unit := do
  return ()

/-- C++ `__mavlink_nav_controller_output_t::__mavlink_nav_controller_output_t : void () noexcept`, `mavlink_msg_nav_controller_output.h:9-?`. -/
def __mavlink_nav_controller_output_t.__mavlink_nav_controller_output_t (this : UInt64) : PMem.M Unit :=
  pure (_root_.Vehicle_lib.__mavlink_nav_controller_output_t.__mavlink_nav_controller_output_t.pure' this)

/-- C++ `mavlink_msg_nav_controller_output_send : void (mavlink_channel_t, float, float, int16_t, int16_t, uint16_t, float, float, float)`, `mavlink_msg_nav_controller_output.h:270-297`. -/
def mavlink_msg_nav_controller_output_send.body (fp : UInt64) (chan : UInt32) (nav_roll : Binary32) (nav_pitch : Binary32) (nav_bearing : Int16) (target_bearing : Int16) (wp_dist : UInt16) (alt_error : Binary32) (aspd_error : Binary32) (xtrack_error : Binary32) : PMem.M Unit := do
  let mut chan := chan
  let mut nav_roll := nav_roll
  let mut nav_pitch := nav_pitch
  let mut nav_bearing := nav_bearing
  let mut target_bearing := target_bearing
  let mut wp_dist := wp_dist
  let mut alt_error := alt_error
  let mut aspd_error := aspd_error
  let mut xtrack_error := xtrack_error
  __mavlink_nav_controller_output_t.__mavlink_nav_controller_output_t (fp + 0)
  PMem.stF32 (fp + 0) nav_roll
  PMem.stF32 ((fp + 0) + 4) nav_pitch
  PMem.stF32 ((fp + 0) + 8) alt_error
  PMem.stF32 ((fp + 0) + 12) aspd_error
  PMem.stF32 ((fp + 0) + 16) xtrack_error
  PMem.stI16 ((fp + 0) + 20) nav_bearing
  PMem.stI16 ((fp + 0) + 22) target_bearing
  PMem.stU16 ((fp + 0) + 24) wp_dist
  _mav_finalize_message_chan_send chan (Int32.toUInt32 ((62 : Int32))) (fp + 0) (Int8.toUInt8 (Int32.toInt8 ((26 : Int32)))) (Int8.toUInt8 (Int32.toInt8 ((26 : Int32)))) (Int8.toUInt8 (Int32.toInt8 ((183 : Int32))))
  return ()

def mavlink_msg_nav_controller_output_send (chan : UInt32) (nav_roll : Binary32) (nav_pitch : Binary32) (nav_bearing : Int16) (target_bearing : Int16) (wp_dist : UInt16) (alt_error : Binary32) (aspd_error : Binary32) (xtrack_error : Binary32) : PMem.M Unit := do
  let fp ← PMem.enter 26
  let r ← mavlink_msg_nav_controller_output_send.body fp chan nav_roll nav_pitch nav_bearing target_bearing wp_dist alt_error aspd_error xtrack_error
  PMem.leave fp
  return r

/-- `__mavlink_ahrs_t.__mavlink_ahrs_t` as a pure function of its arguments (it reads and writes no memory). -/
def __mavlink_ahrs_t.__mavlink_ahrs_t.pure' (this : UInt64) : Id Unit := do
  return ()

/-- C++ `__mavlink_ahrs_t::__mavlink_ahrs_t : void () noexcept`, `mavlink_msg_ahrs.h:9-?`. -/
def __mavlink_ahrs_t.__mavlink_ahrs_t (this : UInt64) : PMem.M Unit :=
  pure (_root_.Vehicle_lib.__mavlink_ahrs_t.__mavlink_ahrs_t.pure' this)

/-- C++ `mavlink_msg_ahrs_send : void (mavlink_channel_t, float, float, float, float, float, float, float)`, `mavlink_msg_ahrs.h:257-282`. -/
def mavlink_msg_ahrs_send.body (fp : UInt64) (chan : UInt32) (omegaIx : Binary32) (omegaIy : Binary32) (omegaIz : Binary32) (accel_weight : Binary32) (renorm_val : Binary32) (error_rp : Binary32) (error_yaw : Binary32) : PMem.M Unit := do
  let mut chan := chan
  let mut omegaIx := omegaIx
  let mut omegaIy := omegaIy
  let mut omegaIz := omegaIz
  let mut accel_weight := accel_weight
  let mut renorm_val := renorm_val
  let mut error_rp := error_rp
  let mut error_yaw := error_yaw
  __mavlink_ahrs_t.__mavlink_ahrs_t (fp + 0)
  PMem.stF32 (fp + 0) omegaIx
  PMem.stF32 ((fp + 0) + 4) omegaIy
  PMem.stF32 ((fp + 0) + 8) omegaIz
  PMem.stF32 ((fp + 0) + 12) accel_weight
  PMem.stF32 ((fp + 0) + 16) renorm_val
  PMem.stF32 ((fp + 0) + 20) error_rp
  PMem.stF32 ((fp + 0) + 24) error_yaw
  _mav_finalize_message_chan_send chan (Int32.toUInt32 ((163 : Int32))) (fp + 0) (Int8.toUInt8 (Int32.toInt8 ((28 : Int32)))) (Int8.toUInt8 (Int32.toInt8 ((28 : Int32)))) (Int8.toUInt8 (Int32.toInt8 ((127 : Int32))))
  return ()

def mavlink_msg_ahrs_send (chan : UInt32) (omegaIx : Binary32) (omegaIy : Binary32) (omegaIz : Binary32) (accel_weight : Binary32) (renorm_val : Binary32) (error_rp : Binary32) (error_yaw : Binary32) : PMem.M Unit := do
  let fp ← PMem.enter 28
  let r ← mavlink_msg_ahrs_send.body fp chan omegaIx omegaIy omegaIz accel_weight renorm_val error_rp error_yaw
  PMem.leave fp
  return r

/-- `__mavlink_extended_sys_state_t.__mavlink_extended_sys_state_t` as a pure function of its arguments (it reads and writes no memory). -/
def __mavlink_extended_sys_state_t.__mavlink_extended_sys_state_t.pure' (this : UInt64) : Id Unit := do
  return ()

/-- C++ `__mavlink_extended_sys_state_t::__mavlink_extended_sys_state_t : void () noexcept`, `mavlink_msg_extended_sys_state.h:9-?`. -/
def __mavlink_extended_sys_state_t.__mavlink_extended_sys_state_t (this : UInt64) : PMem.M Unit :=
  pure (_root_.Vehicle_lib.__mavlink_extended_sys_state_t.__mavlink_extended_sys_state_t.pure' this)

/-- C++ `mavlink_msg_extended_sys_state_send : void (mavlink_channel_t, uint8_t, uint8_t)`, `mavlink_msg_extended_sys_state.h:192-207`. -/
def mavlink_msg_extended_sys_state_send.body (fp : UInt64) (chan : UInt32) (vtol_state : UInt8) (landed_state : UInt8) : PMem.M Unit := do
  let mut chan := chan
  let mut vtol_state := vtol_state
  let mut landed_state := landed_state
  __mavlink_extended_sys_state_t.__mavlink_extended_sys_state_t (fp + 0)
  PMem.stU8 (fp + 0) vtol_state
  PMem.stU8 ((fp + 0) + 1) landed_state
  _mav_finalize_message_chan_send chan (Int32.toUInt32 ((245 : Int32))) (fp + 0) (Int8.toUInt8 (Int32.toInt8 ((2 : Int32)))) (Int8.toUInt8 (Int32.toInt8 ((2 : Int32)))) (Int8.toUInt8 (Int32.toInt8 ((130 : Int32))))
  return ()

def mavlink_msg_extended_sys_state_send (chan : UInt32) (vtol_state : UInt8) (landed_state : UInt8) : PMem.M Unit := do
  let fp ← PMem.enter 2
  let r ← mavlink_msg_extended_sys_state_send.body fp chan vtol_state landed_state
  PMem.leave fp
  return r

/-- `__mavlink_vfr_hud_t.__mavlink_vfr_hud_t` as a pure function of its arguments (it reads and writes no memory). -/
def __mavlink_vfr_hud_t.__mavlink_vfr_hud_t.pure' (this : UInt64) : Id Unit := do
  return ()

/-- C++ `__mavlink_vfr_hud_t::__mavlink_vfr_hud_t : void () noexcept`, `mavlink_msg_vfr_hud.h:9-?`. -/
def __mavlink_vfr_hud_t.__mavlink_vfr_hud_t (this : UInt64) : PMem.M Unit :=
  pure (_root_.Vehicle_lib.__mavlink_vfr_hud_t.__mavlink_vfr_hud_t.pure' this)

/-- C++ `mavlink_msg_vfr_hud_send : void (mavlink_channel_t, float, float, int16_t, uint16_t, float, float)`, `mavlink_msg_vfr_hud.h:244-267`. -/
def mavlink_msg_vfr_hud_send.body (fp : UInt64) (chan : UInt32) (airspeed : Binary32) (groundspeed : Binary32) (heading : Int16) (throttle : UInt16) (alt : Binary32) (climb : Binary32) : PMem.M Unit := do
  let mut chan := chan
  let mut airspeed := airspeed
  let mut groundspeed := groundspeed
  let mut heading := heading
  let mut throttle := throttle
  let mut alt := alt
  let mut climb := climb
  __mavlink_vfr_hud_t.__mavlink_vfr_hud_t (fp + 0)
  PMem.stF32 (fp + 0) airspeed
  PMem.stF32 ((fp + 0) + 4) groundspeed
  PMem.stF32 ((fp + 0) + 8) alt
  PMem.stF32 ((fp + 0) + 12) climb
  PMem.stI16 ((fp + 0) + 16) heading
  PMem.stU16 ((fp + 0) + 18) throttle
  _mav_finalize_message_chan_send chan (Int32.toUInt32 ((74 : Int32))) (fp + 0) (Int8.toUInt8 (Int32.toInt8 ((20 : Int32)))) (Int8.toUInt8 (Int32.toInt8 ((20 : Int32)))) (Int8.toUInt8 (Int32.toInt8 ((20 : Int32))))
  return ()

def mavlink_msg_vfr_hud_send (chan : UInt32) (airspeed : Binary32) (groundspeed : Binary32) (heading : Int16) (throttle : UInt16) (alt : Binary32) (climb : Binary32) : PMem.M Unit := do
  let fp ← PMem.enter 20
  let r ← mavlink_msg_vfr_hud_send.body fp chan airspeed groundspeed heading throttle alt climb
  PMem.leave fp
  return r

/-- `__mavlink_vibration_t.__mavlink_vibration_t` as a pure function of its arguments (it reads and writes no memory). -/
def __mavlink_vibration_t.__mavlink_vibration_t.pure' (this : UInt64) : Id Unit := do
  return ()

/-- C++ `__mavlink_vibration_t::__mavlink_vibration_t : void () noexcept`, `mavlink_msg_vibration.h:9-?`. -/
def __mavlink_vibration_t.__mavlink_vibration_t (this : UInt64) : PMem.M Unit :=
  pure (_root_.Vehicle_lib.__mavlink_vibration_t.__mavlink_vibration_t.pure' this)

/-- C++ `mavlink_msg_vibration_send : void (mavlink_channel_t, uint64_t, float, float, float, uint32_t, uint32_t, uint32_t)`, `mavlink_msg_vibration.h:257-282`. -/
def mavlink_msg_vibration_send.body (fp : UInt64) (chan : UInt32) (time_usec : UInt64) (vibration_x : Binary32) (vibration_y : Binary32) (vibration_z : Binary32) (clipping_0 : UInt32) (clipping_1 : UInt32) (clipping_2 : UInt32) : PMem.M Unit := do
  let mut chan := chan
  let mut time_usec := time_usec
  let mut vibration_x := vibration_x
  let mut vibration_y := vibration_y
  let mut vibration_z := vibration_z
  let mut clipping_0 := clipping_0
  let mut clipping_1 := clipping_1
  let mut clipping_2 := clipping_2
  __mavlink_vibration_t.__mavlink_vibration_t (fp + 0)
  PMem.stU64 (fp + 0) time_usec
  PMem.stF32 ((fp + 0) + 8) vibration_x
  PMem.stF32 ((fp + 0) + 12) vibration_y
  PMem.stF32 ((fp + 0) + 16) vibration_z
  PMem.stU32 ((fp + 0) + 20) clipping_0
  PMem.stU32 ((fp + 0) + 24) clipping_1
  PMem.stU32 ((fp + 0) + 28) clipping_2
  _mav_finalize_message_chan_send chan (Int32.toUInt32 ((241 : Int32))) (fp + 0) (Int8.toUInt8 (Int32.toInt8 ((32 : Int32)))) (Int8.toUInt8 (Int32.toInt8 ((32 : Int32)))) (Int8.toUInt8 (Int32.toInt8 ((90 : Int32))))
  return ()

def mavlink_msg_vibration_send (chan : UInt32) (time_usec : UInt64) (vibration_x : Binary32) (vibration_y : Binary32) (vibration_z : Binary32) (clipping_0 : UInt32) (clipping_1 : UInt32) (clipping_2 : UInt32) : PMem.M Unit := do
  let fp ← PMem.enter 32
  let r ← mavlink_msg_vibration_send.body fp chan time_usec vibration_x vibration_y vibration_z clipping_0 clipping_1 clipping_2
  PMem.leave fp
  return r

/-- `__mavlink_autopilot_version_t.__mavlink_autopilot_version_t` as a pure function of its arguments (it reads and writes no memory). -/
def __mavlink_autopilot_version_t.__mavlink_autopilot_version_t.pure' (this : UInt64) : Id Unit := do
  return ()

/-- C++ `__mavlink_autopilot_version_t::__mavlink_autopilot_version_t : void () noexcept`, `mavlink_msg_autopilot_version.h:9-?`. -/
def __mavlink_autopilot_version_t.__mavlink_autopilot_version_t (this : UInt64) : PMem.M Unit :=
  pure (_root_.Vehicle_lib.__mavlink_autopilot_version_t.__mavlink_autopilot_version_t.pure' this)

/-- C++ `mavlink_msg_autopilot_version_send : void (mavlink_channel_t, uint64_t, uint32_t, uint32_t, uint32_t, uint32_t, const uint8_t *, const uint8_t *, const uint8_t *, uint16_t, uint16_t, uint64_t, const uint8_t *)`, `mavlink_msg_autopilot_version.h:329-362`. -/
def mavlink_msg_autopilot_version_send.body (fp : UInt64) (chan : UInt32) (capabilities : UInt64) (flight_sw_version : UInt32) (middleware_sw_version : UInt32) (os_sw_version : UInt32) (board_version : UInt32) (flight_custom_version : UInt64) (middleware_custom_version : UInt64) (os_custom_version : UInt64) (vendor_id : UInt16) (product_id : UInt16) (uid : UInt64) (uid2 : UInt64) : PMem.M Unit := do
  let mut chan := chan
  let mut capabilities := capabilities
  let mut flight_sw_version := flight_sw_version
  let mut middleware_sw_version := middleware_sw_version
  let mut os_sw_version := os_sw_version
  let mut board_version := board_version
  let mut flight_custom_version := flight_custom_version
  let mut middleware_custom_version := middleware_custom_version
  let mut os_custom_version := os_custom_version
  let mut vendor_id := vendor_id
  let mut product_id := product_id
  let mut uid := uid
  let mut uid2 := uid2
  __mavlink_autopilot_version_t.__mavlink_autopilot_version_t (fp + 0)
  PMem.stU64 (fp + 0) capabilities
  PMem.stU64 ((fp + 0) + 8) uid
  PMem.stU32 ((fp + 0) + 16) flight_sw_version
  PMem.stU32 ((fp + 0) + 20) middleware_sw_version
  PMem.stU32 ((fp + 0) + 24) os_sw_version
  PMem.stU32 ((fp + 0) + 28) board_version
  PMem.stU16 ((fp + 0) + 32) vendor_id
  PMem.stU16 ((fp + 0) + 34) product_id
  mav_array_memcpy ((fp + 0) + 36) flight_custom_version ((1 : UInt64) * (Int64.toUInt64 (Int32.toInt64 ((8 : Int32)))))
  mav_array_memcpy ((fp + 0) + 44) middleware_custom_version ((1 : UInt64) * (Int64.toUInt64 (Int32.toInt64 ((8 : Int32)))))
  mav_array_memcpy ((fp + 0) + 52) os_custom_version ((1 : UInt64) * (Int64.toUInt64 (Int32.toInt64 ((8 : Int32)))))
  mav_array_memcpy ((fp + 0) + 60) uid2 ((1 : UInt64) * (Int64.toUInt64 (Int32.toInt64 ((18 : Int32)))))
  _mav_finalize_message_chan_send chan (Int32.toUInt32 ((148 : Int32))) (fp + 0) (Int8.toUInt8 (Int32.toInt8 ((60 : Int32)))) (Int8.toUInt8 (Int32.toInt8 ((78 : Int32)))) (Int8.toUInt8 (Int32.toInt8 ((178 : Int32))))
  return ()

def mavlink_msg_autopilot_version_send (chan : UInt32) (capabilities : UInt64) (flight_sw_version : UInt32) (middleware_sw_version : UInt32) (os_sw_version : UInt32) (board_version : UInt32) (flight_custom_version : UInt64) (middleware_custom_version : UInt64) (os_custom_version : UInt64) (vendor_id : UInt16) (product_id : UInt16) (uid : UInt64) (uid2 : UInt64) : PMem.M Unit := do
  let fp ← PMem.enter 78
  let r ← mavlink_msg_autopilot_version_send.body fp chan capabilities flight_sw_version middleware_sw_version os_sw_version board_version flight_custom_version middleware_custom_version os_custom_version vendor_id product_id uid uid2
  PMem.leave fp
  return r

/-- `__mavlink_available_modes_t.__mavlink_available_modes_t` as a pure function of its arguments (it reads and writes no memory). -/
def __mavlink_available_modes_t.__mavlink_available_modes_t.pure' (this : UInt64) : Id Unit := do
  return ()

/-- C++ `__mavlink_available_modes_t::__mavlink_available_modes_t : void () noexcept`, `mavlink_msg_available_modes.h:9-?`. -/
def __mavlink_available_modes_t.__mavlink_available_modes_t (this : UInt64) : PMem.M Unit :=
  pure (_root_.Vehicle_lib.__mavlink_available_modes_t.__mavlink_available_modes_t.pure' this)

/-- C++ `mavlink_msg_available_modes_send : void (mavlink_channel_t, uint8_t, uint8_t, uint8_t, uint32_t, uint32_t, const char *)`, `mavlink_msg_available_modes.h:238-259`. -/
def mavlink_msg_available_modes_send.body (fp : UInt64) (chan : UInt32) (number_modes : UInt8) (mode_index : UInt8) (standard_mode : UInt8) (custom_mode : UInt32) (properties : UInt32) (mode_name : UInt64) : PMem.M Unit := do
  let mut chan := chan
  let mut number_modes := number_modes
  let mut mode_index := mode_index
  let mut standard_mode := standard_mode
  let mut custom_mode := custom_mode
  let mut properties := properties
  let mut mode_name := mode_name
  __mavlink_available_modes_t.__mavlink_available_modes_t (fp + 0)
  PMem.stU32 (fp + 0) custom_mode
  PMem.stU32 ((fp + 0) + 4) properties
  PMem.stU8 ((fp + 0) + 8) number_modes
  PMem.stU8 ((fp + 0) + 9) mode_index
  PMem.stU8 ((fp + 0) + 10) standard_mode
  mav_array_memcpy ((fp + 0) + 11) mode_name ((1 : UInt64) * (Int64.toUInt64 (Int32.toInt64 ((35 : Int32)))))
  _mav_finalize_message_chan_send chan (Int32.toUInt32 ((435 : Int32))) (fp + 0) (Int8.toUInt8 (Int32.toInt8 ((46 : Int32)))) (Int8.toUInt8 (Int32.toInt8 ((46 : Int32)))) (Int8.toUInt8 (Int32.toInt8 ((134 : Int32))))
  return ()

def mavlink_msg_available_modes_send (chan : UInt32) (number_modes : UInt8) (mode_index : UInt8) (standard_mode : UInt8) (custom_mode : UInt32) (properties : UInt32) (mode_name : UInt64) : PMem.M Unit := do
  let fp ← PMem.enter 46
  let r ← mavlink_msg_available_modes_send.body fp chan number_modes mode_index standard_mode custom_mode properties mode_name
  PMem.leave fp
  return r

/-- `__mavlink_available_modes_monitor_t.__mavlink_available_modes_monitor_t` as a pure function of its arguments (it reads and writes no memory). -/
def __mavlink_available_modes_monitor_t.__mavlink_available_modes_monitor_t.pure' (this : UInt64) : Id Unit := do
  return ()

/-- C++ `__mavlink_available_modes_monitor_t::__mavlink_available_modes_monitor_t : void () noexcept`, `mavlink_msg_available_modes_monitor.h:9-?`. -/
def __mavlink_available_modes_monitor_t.__mavlink_available_modes_monitor_t (this : UInt64) : PMem.M Unit :=
  pure (_root_.Vehicle_lib.__mavlink_available_modes_monitor_t.__mavlink_available_modes_monitor_t.pure' this)

/-- C++ `mavlink_msg_available_modes_monitor_send : void (mavlink_channel_t, uint8_t)`, `mavlink_msg_available_modes_monitor.h:179-192`. -/
def mavlink_msg_available_modes_monitor_send.body (fp : UInt64) (chan : UInt32) (seq : UInt8) : PMem.M Unit := do
  let mut chan := chan
  let mut seq := seq
  __mavlink_available_modes_monitor_t.__mavlink_available_modes_monitor_t (fp + 0)
  PMem.stU8 (fp + 0) seq
  _mav_finalize_message_chan_send chan (Int32.toUInt32 ((437 : Int32))) (fp + 0) (Int8.toUInt8 (Int32.toInt8 ((1 : Int32)))) (Int8.toUInt8 (Int32.toInt8 ((1 : Int32)))) (Int8.toUInt8 (Int32.toInt8 ((30 : Int32))))
  return ()

def mavlink_msg_available_modes_monitor_send (chan : UInt32) (seq : UInt8) : PMem.M Unit := do
  let fp ← PMem.enter 1
  let r ← mavlink_msg_available_modes_monitor_send.body fp chan seq
  PMem.leave fp
  return r

/-- `__mavlink_flight_information_t.__mavlink_flight_information_t` as a pure function of its arguments (it reads and writes no memory). -/
def __mavlink_flight_information_t.__mavlink_flight_information_t.pure' (this : UInt64) : Id Unit := do
  return ()

/-- C++ `__mavlink_flight_information_t::__mavlink_flight_information_t : void () noexcept`, `mavlink_msg_flight_information.h:9-?`. -/
def __mavlink_flight_information_t.__mavlink_flight_information_t (this : UInt64) : PMem.M Unit :=
  pure (_root_.Vehicle_lib.__mavlink_flight_information_t.__mavlink_flight_information_t.pure' this)

/-- C++ `mavlink_msg_flight_information_send : void (mavlink_channel_t, uint32_t, uint64_t, uint64_t, uint64_t, uint32_t)`, `mavlink_msg_flight_information.h:231-252`. -/
def mavlink_msg_flight_information_send.body (fp : UInt64) (chan : UInt32) (time_boot_ms : UInt32) (arming_time_utc : UInt64) (takeoff_time_utc : UInt64) (flight_uuid : UInt64) (landing_time : UInt32) : PMem.M Unit := do
  let mut chan := chan
  let mut time_boot_ms := time_boot_ms
  let mut arming_time_utc := arming_time_utc
  let mut takeoff_time_utc := takeoff_time_utc
  let mut flight_uuid := flight_uuid
  let mut landing_time := landing_time
  __mavlink_flight_information_t.__mavlink_flight_information_t (fp + 0)
  PMem.stU64 (fp + 0) arming_time_utc
  PMem.stU64 ((fp + 0) + 8) takeoff_time_utc
  PMem.stU64 ((fp + 0) + 16) flight_uuid
  PMem.stU32 ((fp + 0) + 24) time_boot_ms
  PMem.stU32 ((fp + 0) + 28) landing_time
  _mav_finalize_message_chan_send chan (Int32.toUInt32 ((264 : Int32))) (fp + 0) (Int8.toUInt8 (Int32.toInt8 ((28 : Int32)))) (Int8.toUInt8 (Int32.toInt8 ((32 : Int32)))) (Int8.toUInt8 (Int32.toInt8 ((49 : Int32))))
  return ()

def mavlink_msg_flight_information_send (chan : UInt32) (time_boot_ms : UInt32) (arming_time_utc : UInt64) (takeoff_time_utc : UInt64) (flight_uuid : UInt64) (landing_time : UInt32) : PMem.M Unit := do
  let fp ← PMem.enter 32
  let r ← mavlink_msg_flight_information_send.body fp chan time_boot_ms arming_time_utc takeoff_time_utc flight_uuid landing_time
  PMem.leave fp
  return r

/-- `__mavlink_command_ack_t.__mavlink_command_ack_t` as a pure function of its arguments (it reads and writes no memory). -/
def __mavlink_command_ack_t.__mavlink_command_ack_t.pure' (this : UInt64) : Id Unit := do
  return ()

/-- C++ `__mavlink_command_ack_t::__mavlink_command_ack_t : void () noexcept`, `mavlink_msg_command_ack.h:9-?`. -/
def __mavlink_command_ack_t.__mavlink_command_ack_t (this : UInt64) : PMem.M Unit :=
  pure (_root_.Vehicle_lib.__mavlink_command_ack_t.__mavlink_command_ack_t.pure' this)

/-- C++ `mavlink_msg_command_ack_send : void (mavlink_channel_t, uint16_t, uint8_t, uint8_t, int32_t, uint32_t, uint8_t)`, `mavlink_msg_command_ack.h:244-267`. -/
def mavlink_msg_command_ack_send.body (fp : UInt64) (chan : UInt32) (command : UInt16) (result : UInt8) (progress : UInt8) (result_param2 : Int32) (target_system : UInt32) (target_component : UInt8) : PMem.M Unit := do
  let mut chan := chan
  let mut command := command
  let mut result := result
  let mut progress := progress
  let mut result_param2 := result_param2
  let mut target_system := target_system
  let mut target_component := target_component
  __mavlink_command_ack_t.__mavlink_command_ack_t (fp + 0)
  PMem.stU16 (fp + 0) command
  PMem.stU8 ((fp + 0) + 2) result
  PMem.stU8 ((fp + 0) + 3) progress
  PMem.stI32 ((fp + 0) + 4) result_param2
  let t'1 ← mavlink_msg_target_field target_system
  PMem.stU8 ((fp + 0) + 8) t'1
  PMem.stU8 ((fp + 0) + 9) target_component
  _mav_finalize_message_chan_send_target chan (Int32.toUInt32 ((77 : Int32))) (fp + 0) (Int8.toUInt8 (Int32.toInt8 ((3 : Int32)))) (Int8.toUInt8 (Int32.toInt8 ((10 : Int32)))) (Int8.toUInt8 (Int32.toInt8 ((143 : Int32)))) target_system
  return ()

def mavlink_msg_command_ack_send (chan : UInt32) (command : UInt16) (result : UInt8) (progress : UInt8) (result_param2 : Int32) (target_system : UInt32) (target_component : UInt8) : PMem.M Unit := do
  let fp ← PMem.enter 10
  let r ← mavlink_msg_command_ack_send.body fp chan command result progress result_param2 target_system target_component
  PMem.leave fp
  return r

/-- C++ `mavlink_msg_command_int_decode : void (const mavlink_message_t *, mavlink_command_int_t *)`, `mavlink_msg_command_int.h:567-593`. -/
def mavlink_msg_command_int_decode (msg : UInt64) (command_int : UInt64) : PMem.M Unit := do
  let mut msg := msg
  let mut command_int := command_int
  mavlink_msg_decode_target msg command_int (Int8.toUInt8 (Int32.toInt8 ((35 : Int32)))) (Int8.toUInt8 (Int32.toInt8 ((30 : Int32))))
  return ()

/-- `__mavlink_request_data_stream_t.__mavlink_request_data_stream_t` as a pure function of its arguments (it reads and writes no memory). -/
def __mavlink_request_data_stream_t.__mavlink_request_data_stream_t.pure' (this : UInt64) : Id Unit := do
  return ()

/-- C++ `__mavlink_request_data_stream_t::__mavlink_request_data_stream_t : void () noexcept`, `mavlink_msg_request_data_stream.h:9-?`. -/
def __mavlink_request_data_stream_t.__mavlink_request_data_stream_t (this : UInt64) : PMem.M Unit :=
  pure (_root_.Vehicle_lib.__mavlink_request_data_stream_t.__mavlink_request_data_stream_t.pure' this)

/-- C++ `mavlink_msg_request_data_stream_decode : void (const mavlink_message_t *, mavlink_request_data_stream_t *)`, `mavlink_msg_request_data_stream.h:351-369`. -/
def mavlink_msg_request_data_stream_decode (msg : UInt64) (request_data_stream : UInt64) : PMem.M Unit := do
  let mut msg := msg
  let mut request_data_stream := request_data_stream
  mavlink_msg_decode_target msg request_data_stream (Int8.toUInt8 (Int32.toInt8 ((6 : Int32)))) (Int8.toUInt8 (Int32.toInt8 ((2 : Int32))))
  return ()

/-- C++ `mavlink_msg_system_time_decode : void (const mavlink_message_t *, mavlink_system_time_t *)`, `mavlink_msg_system_time.h:280-291`. -/
def mavlink_msg_system_time_decode.body (fp : UInt64) (msg : UInt64) (system_time : UInt64) : PMem.M Unit := do
  PMem.stU64 (fp + 0) msg
  let mut system_time := system_time
  let t'1 ← PMem.ldU64 (fp + 0)
  let t'2 ← PMem.ldU8 (t'1 + 3)
  let mut c'3 : Int32 := default
  if (decide ((UInt32.toInt32 (UInt8.toUInt32 (t'2))) < (12 : Int32))) then
    let t'4 ← PMem.ldU64 (fp + 0)
    let t'5 ← PMem.ldU8 (t'4 + 3)
    c'3 := UInt32.toInt32 (UInt8.toUInt32 (t'5))
  else
    c'3 := (12 : Int32)
  let mut len : UInt8 := Int8.toUInt8 (Int32.toInt8 (c'3))
  let t'6 ← PMem.memset system_time (0 : Int32) (Int64.toUInt64 (Int32.toInt64 ((12 : Int32))))
  discard <| pure (t'6)
  let t'7 ← PMem.ldU64 (fp + 0)
  let t'8 ← PMem.memcpy system_time ((t'7 + 16) + ((Int32.toInt64 ((0 : Int32))) * 8).toUInt64) (UInt8.toUInt64 (len))
  discard <| pure (t'8)
  return ()

def mavlink_msg_system_time_decode (msg : UInt64) (system_time : UInt64) : PMem.M Unit := do
  let fp ← PMem.enter 8
  let r ← mavlink_msg_system_time_decode.body fp msg system_time
  PMem.leave fp
  return r

end Vehicle_lib
