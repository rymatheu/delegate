import ArduLean.Runtime.GcsPort
import ArduLean.Vehicle.libraries.AP_Math.AP_Math
import ArduLean.Vehicle.libraries.AP_Param.AP_Param
import ArduLean.Vehicle.libraries.AP_Mission.AP_Mission
import ArduLean.Vehicle.libraries.RC_Channel.RC_Channel
import ArduLean.Vehicle.ArduCopter.ArduCopter
import ArduLean.Vehicle.libraries.AP_Common.AP_Common
import ArduLean.Vehicle.libraries.AP_RCMapper.AP_RCMapper
import ArduLean.Vehicle.libraries.AP_Mission.AP_Mission_2

/-!
ArduPilot `libraries/RC_Channel`, part 2 of 2. Sources: `libraries/RC_Channel/RC_Channels.cpp`, `libraries/RC_Channel/RC_Channel.cpp`, `libraries/RC_Channel/RC_Channel.h`.

Items of `lean/Vehicle_lib.lean` (the vehicle translation), unchanged; placed by `tools/split_modules.py` (`ArduLean/Vehicle/INDEX.md`).
-/

open FloatLib.Floats (Binary32 Binary64)

set_option linter.unusedVariables false
set_option linter.unreachableTactic false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false

namespace Vehicle_lib

/-- C++ `RC_Channels::flight_mode_channel : RC_Channel *()`, `RC_Channels.cpp:257-267`. -/
def RC_Channels.flight_mode_channel (this : UInt64) : PMem.M UInt64 := do
  let t'1 ← RC_Channels_Copter.flight_mode_channel_number this
  let mut num : Int8 := t'1
  if (decide ((Int8.toInt32 (num)) ≤ (0 : Int32))) then
    return (0 : UInt64)
  if (decide ((Int8.toInt32 (num)) ≥ (16 : Int32))) then
    return (0 : UInt64)
  let t'2 ← RC_Channels_Copter.channel this (Int8.toUInt8 (Int32.toInt8 (((Int8.toInt32 (num)) - (1 : Int32)))))
  return t'2

/-- C++ `RC_Channels::find_channel_for_option : RC_Channel *(const RC_Channel::AUX_FUNC)`, `RC_Channel.cpp:2109-2122`. -/
def RC_Channels.find_channel_for_option (this : UInt64) (option : Int32) : PMem.M UInt64 := do
  let mut option := option
  for i'1 in [0:16] do
    let i : UInt8 := UInt8.ofNat i'1
    let t'2 ← RC_Channels_Copter.channel this i
    let mut c : UInt64 := t'2
    if (c == (0 : UInt64)) then
      continue
    let t'3 ← AP_ParamTBase'short_2.get (c + 8)
    let t'4 ← PMem.ldI16 t'3
    if ((Int16.toInt32 (t'4)) == option) then
      return c
  return (0 : UInt64)

/-- `RC_Channels.get_rcmap_channel_nonnull` as a pure function of its arguments (it reads and writes no memory). -/
def RC_Channels.get_rcmap_channel_nonnull.pure' (this : UInt64) (rcmap_number : UInt8) : Id UInt64 := do
  let mut rcmap_number := rcmap_number
  let t'1 ← _root_.Vehicle_lib.RC_Channels_Copter.channel.pure' this (Int8.toUInt8 (Int32.toInt8 (((UInt32.toInt32 (UInt8.toUInt32 (rcmap_number))) - (1 : Int32)))))
  let mut ret : UInt64 := t'1
  if (ret != (0 : UInt64)) then
    return ret
  return (0xed70 : UInt64) /- &dummy_rcchannel -/

/-- C++ `RC_Channels::get_rcmap_channel_nonnull : RC_Channel &(uint8_t)`, `RC_Channels.cpp:394-401`. -/
def RC_Channels.get_rcmap_channel_nonnull (this : UInt64) (rcmap_number : UInt8) : PMem.M UInt64 :=
  pure (_root_.Vehicle_lib.RC_Channels.get_rcmap_channel_nonnull.pure' this rcmap_number)

/-- C++ `RC_Channels::get_throttle_channel : RC_Channel &()`, `RC_Channels.cpp:422-425`. -/
def RC_Channels.get_throttle_channel (this : UInt64) : PMem.M UInt64 := do
  let t'1 ← AP.rcmap
  let t'2 ← RCMapper.throttle t'1
  let t'3 ← RC_Channels.get_rcmap_channel_nonnull this t'2
  return t'3

/-- C++ `RC_Channels::duplicate_options_exist : bool ()`, `RC_Channel.cpp:2125-2147`. -/
def RC_Channels.duplicate_options_exist.body (fp : UInt64) (this : UInt64) : PMem.M Bool := do
  Bitmask'317.Bitmask (fp + 0)
  for i'1 in [0:16] do
    let i : UInt8 := UInt8.ofNat i'1
    let t'2 ← RC_Channels_Copter.channel this i
    let mut c : UInt64 := t'2
    if (c == (0 : UInt64)) then
      continue
    let t'3 ← AP_ParamTBase'short_2.get (c + 8)
    let t'4 ← PMem.ldI16 t'3
    let mut option : UInt16 := Int16.toUInt16 (t'4)
    if ((UInt32.toInt32 (UInt16.toUInt32 (option))) == (UInt32.toInt32 (UInt16.toUInt32 ((Int16.toUInt16 (Int32.toInt16 ((0 : Int32)))))))) then
      continue
    let t'5 ← Bitmask'317.size (fp + 0)
    if (decide ((UInt32.toInt32 (UInt16.toUInt32 (option))) ≥ (UInt32.toInt32 (UInt16.toUInt32 (t'5))))) then
      continue
    let t'6 ← Bitmask'317.get (fp + 0) option
    if t'6 then
      return true
    Bitmask'317.set (fp + 0) option
  return false

def RC_Channels.duplicate_options_exist (this : UInt64) : PMem.M Bool := do
  let fp ← PMem.enter 40
  let r ← RC_Channels.duplicate_options_exist.body fp this
  PMem.leave fp
  return r

/-- C++ `RC_Channels::flight_mode_channel : const RC_Channel *() const`, `RC_Channels.cpp:268-276`. -/
def RC_Channels.flight_mode_channel'2 (this : UInt64) : PMem.M UInt64 := do
  let t'1 ← RC_Channels_Copter.flight_mode_channel_number this
  let mut num : Int8 := t'1
  if (decide ((Int8.toInt32 (num)) ≤ (0 : Int32))) then
    return (0 : UInt64)
  let t'2 ← RC_Channels_Copter.channel this (Int8.toUInt8 (Int32.toInt8 (((Int8.toInt32 (num)) - (1 : Int32)))))
  return t'2

/-- C++ `RC_Channels::flight_mode_channel_conflicts_with_rc_option : bool () const`, `RC_Channels.cpp:302-309`. -/
def RC_Channels.flight_mode_channel_conflicts_with_rc_option (this : UInt64) : PMem.M Bool := do
  let t'1 ← RC_Channels.flight_mode_channel'2 this
  let mut chan : UInt64 := t'1
  if (chan == (0 : UInt64)) then
    return false
  let t'2 ← AP_ParamTBase'short_2.get (chan + 8)
  let t'3 ← PMem.ldI16 t'2
  return ((Int16.toInt32 (t'3)) != (0 : Int32))

/-- C++ `RC_Channels::get_roll_channel : RC_Channel &()`, `RC_Channels.cpp:406-409`. -/
def RC_Channels.get_roll_channel (this : UInt64) : PMem.M UInt64 := do
  let t'1 ← AP.rcmap
  let t'2 ← RCMapper.roll t'1
  let t'3 ← RC_Channels.get_rcmap_channel_nonnull this t'2
  return t'3

/-- C++ `RC_Channels::get_pitch_channel : RC_Channel &()`, `RC_Channels.cpp:414-417`. -/
def RC_Channels.get_pitch_channel (this : UInt64) : PMem.M UInt64 := do
  let t'1 ← AP.rcmap
  let t'2 ← RCMapper.pitch t'1
  let t'3 ← RC_Channels.get_rcmap_channel_nonnull this t'2
  return t'3

/-- C++ `RC_Channels::get_yaw_channel : RC_Channel &()`, `RC_Channels.cpp:430-433`. -/
def RC_Channels.get_yaw_channel (this : UInt64) : PMem.M UInt64 := do
  let t'1 ← AP.rcmap
  let t'2 ← RCMapper.yaw t'1
  let t'3 ← RC_Channels.get_rcmap_channel_nonnull this t'2
  return t'3

/-- C++ `RC_Channels::has_active_overrides : bool ()`, `RC_Channels.cpp:204-214`. -/
def RC_Channels.has_active_overrides  : PMem.M Bool := do
  let t'1 ← rc
  let _rc : UInt64 := t'1
  for i'2 in [0:16] do
    let i : UInt8 := UInt8.ofNat i'2
    let t'3 ← RC_Channels_Copter.channel _rc i
    let t'4 ← RC_Channel.has_override t'3
    if t'4 then
      return true
  return false

/-- C++ `RC_Channel::clear_override : void ()`, `RC_Channel.cpp:550-558`. -/
def RC_Channel.clear_override (this : UInt64) : PMem.M Unit := do
  let t'1 := Int32.toUInt32 ((0 : Int32))
  PMem.stU32 (this + 36) t'1
  let t'2 := Int16.toUInt16 (Int32.toInt16 ((0 : Int32)))
  PMem.stU16 (this + 34) t'2
  let t'3 ← RC_Channels.has_active_overrides
  if !t'3 then
    let t'4 ← rc
    RC_Channels.set_override_start_throttle t'4 (Int32.toInt16 ((-(1 : Int32))))
  return ()

/-- C++ `RC_Channels::clear_overrides : void ()`, `RC_Channels.cpp:173-182`. -/
def RC_Channels.clear_overrides  : PMem.M Unit := do
  let t'1 ← rc
  let _rc : UInt64 := t'1
  for i'2 in [0:16] do
    let i : UInt8 := UInt8.ofNat i'2
    let t'3 ← RC_Channels_Copter.channel _rc i
    RC_Channel.clear_override t'3
  return ()

/-- C++ `RC_Channels::set_gcs_overrides_enabled : void (bool)`, `RC_Channel.h:661-666`. -/
def RC_Channels.set_gcs_overrides_enabled (this : UInt64) (enable : Bool) : PMem.M Unit := do
  let mut enable := enable
  PMem.stB (this + 37) enable
  let t'1 ← PMem.ldB (this + 37)
  if !t'1 then
    RC_Channels.clear_overrides
  return ()

/-- C++ `RC_Channel::do_aux_function_rc_override_enable : void (const AuxSwitchPos)`, `RC_Channel.cpp:1383-1398`. -/
def RC_Channel.do_aux_function_rc_override_enable (this : UInt64) (ch_flag : UInt8) : PMem.M Unit := do
  let mut ch_flag := ch_flag
  for _ in [0:1] do
    let sw'1 := ch_flag
    if sw'1 == (2 : UInt8) then
      let t'2 ← rc
      RC_Channels.set_gcs_overrides_enabled t'2 true
      break
    else if sw'1 == (1 : UInt8) then
      pure ()
    else if sw'1 == (0 : UInt8) then
      let t'3 ← rc
      RC_Channels.set_gcs_overrides_enabled t'3 false
      break
    else
      pure ()
  return ()

/-- C++ `RC_Channel::do_aux_function_clear_wp : void (const AuxSwitchPos)`, `RC_Channel.cpp:1295-1300`. -/
def RC_Channel.do_aux_function_clear_wp (this : UInt64) (ch_flag : UInt8) : PMem.M Unit := do
  let mut ch_flag := ch_flag
  if (ch_flag == (2 : UInt8)) then
    let t'1 ← AP.mission
    let t'2 ← AP_Mission.clear t'1
    discard <| pure (t'2)
  return ()

/-- C++ `RC_Channels::get_radio_in : uint8_t (uint16_t *, const uint8_t)`, `RC_Channels.cpp:76-86`. -/
def RC_Channels.get_radio_in.body (fp : UInt64) (this : UInt64) (chans : UInt64) (num_channels : UInt8) : PMem.M UInt8 := do
  let mut chans := chans
  PMem.stU8 (fp + 0) num_channels
  let t'1 ← PMem.ldU8 (fp + 0)
  let t'2 ← PMem.memset chans (0 : Int32) ((UInt8.toUInt64 (t'1)) * (2 : UInt64))
  discard <| pure (t'2)
  PMem.stI32 (fp + 4) (16 : Int32)
  let t'3 ← MIN'unsigned_char_int (fp + 0) (fp + 4)
  let mut read_channels : UInt8 := Int8.toUInt8 (Int32.toInt8 (t'3))
  for i'4 in [0:read_channels.toNat] do
    let i : UInt8 := UInt8.ofNat i'4
    let t'5 ← RC_Channels_Copter.channel this i
    let t'6 ← RC_Channel.get_radio_in t'5
    let t'7 := Int16.toUInt16 (t'6)
    PMem.stU16 (chans + ((UInt64.toInt64 (UInt8.toUInt64 (i))) * 2).toUInt64) t'7
  return read_channels

def RC_Channels.get_radio_in (this : UInt64) (chans : UInt64) (num_channels : UInt8) : PMem.M UInt8 := do
  let fp ← PMem.enter 8
  let r ← RC_Channels.get_radio_in.body fp this chans num_channels
  PMem.leave fp
  return r

/-- C++ `RC_Channel::in_raw_trim_dz : bool () const`, `RC_Channel.cpp:514-517`. -/
def RC_Channel.in_raw_trim_dz (this : UInt64) : PMem.M Bool := do
  let t'1 ← PMem.ldI16 (this + 14)
  let t'2 ← AP_ParamT'short_2.operator_const_short__ (this + 20)
  let t'3 ← PMem.ldI16 t'2
  let t'4 ← AP_ParamT'short_2.operator_const_short__ (this + 26)
  let t'5 ← PMem.ldI16 t'4
  let t'6 ← AP_ParamT'short_2.operator_const_short__ (this + 20)
  let t'7 ← PMem.ldI16 t'6
  let t'8 ← AP_ParamT'short_2.operator_const_short__ (this + 26)
  let t'9 ← PMem.ldI16 t'8
  let t'10 ← is_bounded_int32 (Int16.toInt32 (t'1)) ((Int16.toInt32 (t'3)) - (Int16.toInt32 (t'5))) ((Int16.toInt32 (t'7)) + (Int16.toInt32 (t'9)))
  return t'10

/-- C++ `RC_Channels::channel_outside_trim_dz : bool (const RC_Channel &)`, `RC_Channels.cpp:130-133`. -/
def RC_Channels.channel_outside_trim_dz (ch : UInt64) : PMem.M Bool := do
  let t'1 ← RC_Channel.in_raw_trim_dz ch
  return !t'1

/-- `RC_Channels.get_rcmap_channel_nonnull'2` as a pure function of its arguments (it reads and writes no memory). -/
def RC_Channels.get_rcmap_channel_nonnull'2.pure' (this : UInt64) (rcmap_number : UInt8) : Id UInt64 := do
  let mut rcmap_number := rcmap_number
  let t'1 ← _root_.Vehicle_lib.RC_Channels_Copter.channel.pure' this (Int8.toUInt8 (Int32.toInt8 (((UInt32.toInt32 (UInt8.toUInt32 (rcmap_number))) - (1 : Int32)))))
  let mut ret : UInt64 := t'1
  if (ret != (0 : UInt64)) then
    return ret
  return (0xed70 : UInt64) /- &dummy_rcchannel -/

/-- C++ `RC_Channels::get_rcmap_channel_nonnull : const RC_Channel &(uint8_t) const`, `RC_Channels.cpp:386-393`. -/
def RC_Channels.get_rcmap_channel_nonnull'2 (this : UInt64) (rcmap_number : UInt8) : PMem.M UInt64 :=
  pure (_root_.Vehicle_lib.RC_Channels.get_rcmap_channel_nonnull'2.pure' this rcmap_number)

/-- C++ `RC_Channels::get_throttle_channel : const RC_Channel &() const`, `RC_Channels.cpp:418-421`. -/
def RC_Channels.get_throttle_channel'2 (this : UInt64) : PMem.M UInt64 := do
  let t'1 ← AP.rcmap
  let t'2 ← RCMapper.throttle t'1
  let t'3 ← RC_Channels.get_rcmap_channel_nonnull'2 this t'2
  return t'3

/-- C++ `RC_Channels::throttle_moved_since_override_start : bool () const`, `RC_Channels.cpp:135-143`. -/
def RC_Channels.throttle_moved_since_override_start (this : UInt64) : PMem.M Bool := do
  let t'1 ← PMem.ldI16 (this + 16)
  if (decide ((Int16.toInt32 (t'1)) < (0 : Int32))) then
    return false
  let t'2 ← RC_Channels.get_throttle_channel'2 this
  let thr : UInt64 := t'2
  let t'3 ← RC_Channel.get_raw_radio_in thr
  let t'4 ← PMem.ldI16 (this + 16)
  let t'5 ← PMem.iabs ((Int16.toInt32 (t'3)) - (Int16.toInt32 (t'4)))
  let t'6 ← RC_Channel.get_dead_zone thr
  return (decide (t'5 > (UInt32.toInt32 (UInt16.toUInt32 (t'6)))))

/-- C++ `RC_Channels::has_pilot_input_for_override_clear : bool ()`, `RC_Channels.cpp:145-158`. -/
def RC_Channels.has_pilot_input_for_override_clear (this : UInt64) : PMem.M Bool := do
  let t'1 ← RC_Channels.get_roll_channel this
  let t'2 ← RC_Channels.channel_outside_trim_dz t'1
  let mut sc'5 := t'2
  if !sc'5 then
    let t'3 ← RC_Channels.get_pitch_channel this
    let t'4 ← RC_Channels.channel_outside_trim_dz t'3
    sc'5 := t'4
  let mut sc'8 := sc'5
  if !sc'8 then
    let t'6 ← RC_Channels.get_yaw_channel this
    let t'7 ← RC_Channels.channel_outside_trim_dz t'6
    sc'8 := t'7
  if sc'8 then
    return true
  let t'9 ← RC_Channels.throttle_moved_since_override_start this
  if t'9 then
    return true
  return false

/-- C++ `RC_Channels::should_ignore_overrides : bool ()`, `RC_Channels.cpp:122-128`. -/
def RC_Channels.should_ignore_overrides (this : UInt64) : PMem.M Bool := do
  let t'1 ← rc
  let t'2 ← RC_Channels.option_is_enabled t'1 (16384 : Int32)
  let mut sc'4 := !t'2
  if !sc'4 then
    let t'3 ← RC_Channels.has_active_overrides
    sc'4 := !t'3
  if sc'4 then
    return false
  let t'5 ← RC_Channels.has_pilot_input_for_override_clear this
  return t'5

end Vehicle_lib
