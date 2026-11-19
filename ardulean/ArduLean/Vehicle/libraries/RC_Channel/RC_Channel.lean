import ArduLean.Runtime.Hal
import ArduLean.Vehicle.libraries.AP_Math.AP_Math
import ArduLean.Vehicle.libraries.AP_Param.AP_Param
import ArduLean.Vehicle.libraries.AP_Mission.AP_Mission

/-!
ArduPilot `libraries/RC_Channel`, part 1 of 2. Sources: `libraries/RC_Channel/RC_Channel.cpp`, `libraries/RC_Channel/RC_Channel.h`, `libraries/RC_Channel/RC_Channels.cpp`.

Items of `lean/Vehicle_lib.lean` (the vehicle translation), unchanged; placed by `tools/split_modules.py` (`ArduLean/Vehicle/INDEX.md`).
-/

open FloatLib.Floats (Binary32 Binary64)

set_option linter.unusedVariables false
set_option linter.unreachableTactic false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false

namespace Vehicle_lib

/-- C++ `RC_Channels::get_singleton : RC_Channels *()`, `RC_Channel.h:615-617`. -/
def RC_Channels.get_singleton  : PMem.M UInt64 := do
  let t'1 ← PMem.ldU64 (0xe528 : UInt64) /- &RC_Channels::_singleton -/
  return t'1

/-- C++ `rc : RC_Channels &()`, `RC_Channels.cpp:522-525`. -/
def rc  : PMem.M UInt64 := do
  let t'1 ← RC_Channels.get_singleton
  return t'1

/-- C++ `RC_Channel::get_control_in : int16_t () const`, `RC_Channel.h:99-?`. -/
def RC_Channel.get_control_in (this : UInt64) : PMem.M Int16 := do
  let t'1 ← PMem.ldI16 (this + 16)
  return t'1

/-- C++ `RC_Channel::get_radio_in : int16_t () const`, `RC_Channel.h:96-?`. -/
def RC_Channel.get_radio_in (this : UInt64) : PMem.M Int16 := do
  let t'1 ← PMem.ldI16 (this + 12)
  return t'1

/-- C++ `RC_Channel::debounce_completed : bool (int8_t)`, `RC_Channel.cpp:650-672`. -/
def RC_Channel.debounce_completed (this : UInt64) (position : Int8) : PMem.M Bool := do
  let mut position := position
  let t'1 ← PMem.ldI8 ((this + 40) + 1)
  if ((Int8.toInt32 (t'1)) == (Int8.toInt32 (position))) then
    PMem.stI8 (this + 40) position
  else
    let mut tnow_ms : UInt32 := ((← PMem.clock) / 1000).toUInt32
    let t'2 ← PMem.ldI8 (this + 40)
    if ((Int8.toInt32 (t'2)) != (Int8.toInt32 (position))) then
      PMem.stI8 (this + 40) position
      PMem.stU32 ((this + 40) + 4) tnow_ms
    else
      let t'3 ← PMem.ldU32 ((this + 40) + 4)
      if (decide ((tnow_ms - t'3) ≥ (Int32.toUInt32 ((200 : Int32))))) then
        PMem.stI8 ((this + 40) + 1) position
        return true
  return false

/-- C++ `RC_Channel::read_6pos_switch : bool (int8_t &)`, `RC_Channel.cpp:612-639`. -/
def RC_Channel.read_6pos_switch (this : UInt64) (position : UInt64) : PMem.M Bool := do
  let t'1 ← RC_Channel.get_radio_in this
  let mut pulsewidth : UInt16 := Int16.toUInt16 (t'1)
  if ((decide ((UInt32.toInt32 (UInt16.toUInt32 (pulsewidth))) ≤ (UInt32.toInt32 (UInt16.toUInt32 ((800 : UInt16)))))) || (decide ((UInt32.toInt32 (UInt16.toUInt32 (pulsewidth))) ≥ (UInt32.toInt32 (UInt16.toUInt32 ((2200 : UInt16))))))) then
    return false
  if (decide ((UInt32.toInt32 (UInt16.toUInt32 (pulsewidth))) < (1231 : Int32))) then
    let t'2 := Int32.toInt8 ((0 : Int32))
    PMem.stI8 position t'2
  else
    if (decide ((UInt32.toInt32 (UInt16.toUInt32 (pulsewidth))) < (1361 : Int32))) then
      let t'3 := Int32.toInt8 ((1 : Int32))
      PMem.stI8 position t'3
    else
      if (decide ((UInt32.toInt32 (UInt16.toUInt32 (pulsewidth))) < (1491 : Int32))) then
        let t'4 := Int32.toInt8 ((2 : Int32))
        PMem.stI8 position t'4
      else
        if (decide ((UInt32.toInt32 (UInt16.toUInt32 (pulsewidth))) < (1621 : Int32))) then
          let t'5 := Int32.toInt8 ((3 : Int32))
          PMem.stI8 position t'5
        else
          if (decide ((UInt32.toInt32 (UInt16.toUInt32 (pulsewidth))) < (1750 : Int32))) then
            let t'6 := Int32.toInt8 ((4 : Int32))
            PMem.stI8 position t'6
          else
            let t'7 := Int32.toInt8 ((5 : Int32))
            PMem.stI8 position t'7
  let t'8 ← PMem.ldI8 position
  let t'9 ← RC_Channel.debounce_completed this t'8
  if !t'9 then
    return false
  return true

/-- C++ `RC_Channels::has_ever_seen_rc_input : bool () const`, `RC_Channel.h:753-755`. -/
def RC_Channels.has_ever_seen_rc_input (this : UInt64) : PMem.M Bool := do
  let t'1 ← PMem.ldB (this + 36)
  return t'1

/-- C++ `RC_Channels::has_valid_input : bool () const`, `RC_Channels.cpp:65-74`. -/
def RC_Channels.has_valid_input (this : UInt64) : PMem.M Bool := do
  let t'1 ← RC_Channels.has_ever_seen_rc_input this
  if !t'1 then
    return false
  return true

/-- C++ `RC_Channel::norm_input_dz : float () const`, `RC_Channel.cpp:440-454`. -/
def RC_Channel.norm_input_dz (this : UInt64) : PMem.M Binary32 := do
  let t'1 ← AP_ParamT'short_2.operator_const_short__ (this + 20)
  let t'2 ← PMem.ldI16 t'1
  let t'3 ← AP_ParamT'short_2.operator_const_short__ (this + 26)
  let t'4 ← PMem.ldI16 t'3
  let mut dz_min : Int16 := Int32.toInt16 (((Int16.toInt32 (t'2)) - (Int16.toInt32 (t'4))))
  let t'5 ← AP_ParamT'short_2.operator_const_short__ (this + 20)
  let t'6 ← PMem.ldI16 t'5
  let t'7 ← AP_ParamT'short_2.operator_const_short__ (this + 26)
  let t'8 ← PMem.ldI16 t'7
  let mut dz_max : Int16 := Int32.toInt16 (((Int16.toInt32 (t'6)) + (Int16.toInt32 (t'8))))
  let mut ret : Binary32 := default  -- uninitialized in C
  let t'9 ← AP_ParamT'signed_char_1.operator_const_signed_char__ (this + 24)
  let t'10 ← PMem.ldI8 t'9
  let mut c'11 : Int32 := default
  if t'10 != (0 : Int8) then
    c'11 := -(1 : Int32)
  else
    c'11 := (1 : Int32)
  let mut reverse_mul : Int16 := Int32.toInt16 (c'11)
  let t'12 ← PMem.ldI16 (this + 12)
  let mut sc'15 := (decide ((Int16.toInt32 (t'12)) < (Int16.toInt32 (dz_min))))
  if sc'15 then
    let t'13 ← AP_ParamT'short_2.operator_const_short__ (this + 18)
    let t'14 ← PMem.ldI16 t'13
    sc'15 := (decide ((Int16.toInt32 (dz_min)) > (Int16.toInt32 (t'14))))
  if sc'15 then
    let t'16 ← PMem.ldI16 (this + 12)
    let t'17 ← AP_ParamT'short_2.operator_const_short__ (this + 18)
    let t'18 ← PMem.ldI16 t'17
    let t'19 := (((Int32.toBinary32 ((Int16.toInt32 (reverse_mul)))) * (Int32.toBinary32 (((Int16.toInt32 (t'16)) - (Int16.toInt32 (dz_min)))))) / (Int32.toBinary32 (((Int16.toInt32 (dz_min)) - (Int16.toInt32 (t'18))))))
    ret := t'19
  else
    let t'20 ← PMem.ldI16 (this + 12)
    let mut sc'23 := (decide ((Int16.toInt32 (t'20)) > (Int16.toInt32 (dz_max))))
    if sc'23 then
      let t'21 ← AP_ParamT'short_2.operator_const_short__ (this + 22)
      let t'22 ← PMem.ldI16 t'21
      sc'23 := (decide ((Int16.toInt32 (t'22)) > (Int16.toInt32 (dz_max))))
    if sc'23 then
      let t'24 ← PMem.ldI16 (this + 12)
      let t'25 ← AP_ParamT'short_2.operator_const_short__ (this + 22)
      let t'26 ← PMem.ldI16 t'25
      let t'27 := (((Int32.toBinary32 ((Int16.toInt32 (reverse_mul)))) * (Int32.toBinary32 (((Int16.toInt32 (t'24)) - (Int16.toInt32 (dz_max)))))) / (Int32.toBinary32 (((Int16.toInt32 (t'26)) - (Int16.toInt32 (dz_max))))))
      ret := t'27
    else
      let t'28 := Int32.toBinary32 ((0 : Int32))
      ret := t'28
  let t'29 ← constrain_value_line'float ret (-(Binary32.ofBits 0x3f800000 /- 1 -/)) (Binary32.ofBits 0x3f800000 /- 1 -/) (Int32.toUInt32 ((453 : Int32)))
  return t'29

/-- C++ `RC_Channel::get_radio_trim : int16_t () const`, `RC_Channel.h:115-?`. -/
def RC_Channel.get_radio_trim (this : UInt64) : PMem.M Int16 := do
  let t'1 ← AP_ParamTBase'short_2.get (this + 20)
  let t'2 ← PMem.ldI16 t'1
  return t'2

/-- C++ `RC_Channel::get_type : ControlType () const`, `RC_Channel.h:125-?`. -/
def RC_Channel.get_type (this : UInt64) : PMem.M Int32 := do
  let t'1 ← PMem.ldI32 (this + 28)
  return t'1

/-- C++ `RC_Channel::norm_input_ignore_trim : float () const`, `RC_Channel.cpp:458-466`. -/
def RC_Channel.norm_input_ignore_trim (this : UInt64) : PMem.M Binary32 := do
  let t'1 ← AP_ParamT'short_2.operator_const_short__ (this + 22)
  let t'2 ← PMem.ldI16 t'1
  let t'3 ← AP_ParamT'short_2.operator_const_short__ (this + 18)
  let t'4 ← PMem.ldI16 t'3
  if (decide ((Int16.toInt32 (t'2)) ≤ (Int16.toInt32 (t'4)))) then
    return (Binary32.ofBits 0x00000000 /- 0 -/)
  let t'5 ← AP_ParamT'signed_char_1.operator_const_signed_char__ (this + 24)
  let t'6 ← PMem.ldI8 t'5
  let mut c'7 : Binary32 := default
  if t'6 != (0 : Int8) then
    c'7 := -(Binary32.ofBits 0x40000000 /- 2 -/)
  else
    c'7 := (Binary32.ofBits 0x40000000 /- 2 -/)
  let t'8 ← PMem.ldI16 (this + 12)
  let t'9 ← AP_ParamT'short_2.operator_const_short__ (this + 18)
  let t'10 ← PMem.ldI16 t'9
  let t'11 ← AP_ParamT'short_2.operator_const_short__ (this + 22)
  let t'12 ← PMem.ldI16 t'11
  let t'13 ← AP_ParamT'short_2.operator_const_short__ (this + 18)
  let t'14 ← PMem.ldI16 t'13
  let mut ret : Binary32 := (c'7 * (((Int32.toBinary32 (((Int16.toInt32 (t'8)) - (Int16.toInt32 (t'10))))) / (Int32.toBinary32 (((Int16.toInt32 (t'12)) - (Int16.toInt32 (t'14)))))) - (Binary32.ofBits 0x3f000000 /- 1/2 -/)))
  let t'15 ← constrain_value_line'float ret (-(Binary32.ofBits 0x3f800000 /- 1 -/)) (Binary32.ofBits 0x3f800000 /- 1 -/) (Int32.toUInt32 ((465 : Int32)))
  return t'15

/-- C++ `RC_Channel::get_dead_zone : uint16_t () const`, `RC_Channel.h:57-?`. -/
def RC_Channel.get_dead_zone (this : UInt64) : PMem.M UInt16 := do
  let t'1 ← AP_ParamT'short_2.operator_const_short__ (this + 26)
  let t'2 ← PMem.ldI16 t'1
  return Int16.toUInt16 (t'2)

/-- C++ `RC_Channels::calibrating : bool ()`, `RC_Channel.h:744-?`. -/
def RC_Channels.calibrating (this : UInt64) : PMem.M Bool := do
  let t'1 ← PMem.ldB (this + 38)
  return t'1

/-- C++ `RC_Channels::option_is_enabled : bool (Option) const`, `RC_Channel.h:686-688`. -/
def RC_Channels.option_is_enabled (this : UInt64) (option : Int32) : PMem.M Bool := do
  let mut option := option
  let t'1 ← AP_ParamT'unsigned_int_3.operator_const_unsigned_int__ (this + 24)
  let t'2 ← PMem.ldU32 t'1
  return (t'2 &&& (Int32.toUInt32 (option))) != (0 : UInt32)

/-- C++ `RC_Channel::read_3pos_switch : bool (RC_Channel::AuxSwitchPos &) const`, `RC_Channel.cpp:2057-2075`. -/
def RC_Channel.read_3pos_switch (this : UInt64) (ret : UInt64) : PMem.M Bool := do
  let t'1 ← RC_Channel.get_radio_in this
  let mut in' : UInt16 := Int16.toUInt16 (t'1)
  if ((decide ((UInt32.toInt32 (UInt16.toUInt32 (in'))) ≤ (UInt32.toInt32 (UInt16.toUInt32 ((800 : UInt16)))))) || (decide ((UInt32.toInt32 (UInt16.toUInt32 (in'))) ≥ (UInt32.toInt32 (UInt16.toUInt32 ((2200 : UInt16))))))) then
    return false
  let t'2 ← AP_ParamT'signed_char_1.operator_const_signed_char__ (this + 24)
  let t'3 ← PMem.ldI8 t'2
  let mut sc'6 := t'3 != (0 : Int8)
  if sc'6 then
    let t'4 ← rc
    let t'5 ← RC_Channels.option_is_enabled t'4 (128 : Int32)
    sc'6 := t'5
  let mut switch_reversed : Bool := sc'6
  if (decide ((UInt32.toInt32 (UInt16.toUInt32 (in'))) < (UInt32.toInt32 (UInt16.toUInt32 ((1200 : UInt16)))))) then
    let mut c'7 : UInt8 := default
    if switch_reversed then
      c'7 := (2 : UInt8)
    else
      c'7 := (0 : UInt8)
    PMem.stU8 ret c'7
  else
    if (decide ((UInt32.toInt32 (UInt16.toUInt32 (in'))) > (UInt32.toInt32 (UInt16.toUInt32 ((1800 : UInt16)))))) then
      let mut c'8 : UInt8 := default
      if switch_reversed then
        c'8 := (0 : UInt8)
      else
        c'8 := (2 : UInt8)
      PMem.stU8 ret c'8
    else
      PMem.stU8 ret (1 : UInt8)
  return true

/-- C++ `RC_Channel::get_aux_switch_pos : RC_Channel::AuxSwitchPos () const`, `RC_Channel.cpp:2079-2085`. -/
def RC_Channel.get_aux_switch_pos.body (fp : UInt64) (this : UInt64) : PMem.M UInt8 := do
  PMem.stU8 (fp + 0) (0 : UInt8)
  for _ in [0:1] do
    let mut __unique_name___COUNTER__ : Bool := default  -- uninitialized in C
    let t'1 ← RC_Channel.read_3pos_switch this (fp + 0)
    __unique_name___COUNTER__ := t'1
  let t'2 ← PMem.ldU8 (fp + 0)
  return t'2

def RC_Channel.get_aux_switch_pos (this : UInt64) : PMem.M UInt8 := do
  let fp ← PMem.enter 1
  let r ← RC_Channel.get_aux_switch_pos.body fp this
  PMem.leave fp
  return r

/-- C++ `RC_Channel::get_radio_min : int16_t () const`, `RC_Channel.h:111-?`. -/
def RC_Channel.get_radio_min (this : UInt64) : PMem.M Int16 := do
  let t'1 ← AP_ParamTBase'short_2.get (this + 18)
  let t'2 ← PMem.ldI16 t'1
  return t'2

/-- C++ `RC_Channels::has_had_rc_receiver : bool () const`, `RC_Channel.h:715-?`. -/
def RC_Channels.has_had_rc_receiver (this : UInt64) : PMem.M Bool := do
  let t'1 ← PMem.ldB (this + 13)
  return t'1

/-- C++ `RC_Channels::has_had_rc_override : bool () const`, `RC_Channel.h:718-?`. -/
def RC_Channels.has_had_rc_override (this : UInt64) : PMem.M Bool := do
  let t'1 ← PMem.ldB (this + 14)
  return t'1

/-- C++ `RC_Channel::get_radio_max : int16_t () const`, `RC_Channel.h:113-?`. -/
def RC_Channel.get_radio_max (this : UInt64) : PMem.M Int16 := do
  let t'1 ← AP_ParamTBase'short_2.get (this + 22)
  let t'2 ← PMem.ldI16 t'1
  return t'2

/-- C++ `RC_Channels::get_valid_channel_count : uint8_t ()`, `RC_Channels.cpp:160-163`. -/
def RC_Channels.get_valid_channel_count.body (fp : UInt64)  : PMem.M UInt8 := do
  PMem.stI32 (fp + 0) (16 : Int32)
  let t'1 ← PMem.ldU64 ((0xba88 : UInt64) /- &hal -/ + 64)
  let t'2 ← PMem.halDev "AP_HAL::RCInput::num_channels" t'1 #[]
  PMem.stU8 (fp + 4) (UInt64.toUInt8 (t'2))
  let t'3 ← MIN'int_unsigned_char (fp + 0) (fp + 4)
  return Int8.toUInt8 (Int32.toInt8 (t'3))

def RC_Channels.get_valid_channel_count  : PMem.M UInt8 := do
  let fp ← PMem.enter 5
  let r ← RC_Channels.get_valid_channel_count.body fp 
  PMem.leave fp
  return r

/-- C++ `RC_Channels::get_override_timeout_ms : bool (uint32_t &) const`, `RC_Channel.h:697-709`. -/
def RC_Channels.get_override_timeout_ms (this : UInt64) (returned_timeout_ms : UInt64) : PMem.M Bool := do
  let t'1 ← AP_ParamTBase'float_4.get (this + 20)
  let t'2 ← PMem.ldF32 t'1
  let mut value : Binary32 := t'2
  let t'3 ← is_positive'float value
  if t'3 then
    let t'4 := Binary32.toUInt32 ((value * (Binary32.ofBits 0x447a0000 /- 1000 -/)))
    PMem.stU32 returned_timeout_ms t'4
    return true
  let t'5 ← is_zero value
  if t'5 then
    let t'6 := Int32.toUInt32 ((0 : Int32))
    PMem.stU32 returned_timeout_ms t'6
    return true
  return false

/-- C++ `RC_Channel::has_override : bool () const`, `RC_Channel.cpp:560-578`. -/
def RC_Channel.has_override.body (fp : UInt64) (this : UInt64) : PMem.M Bool := do
  let t'1 ← PMem.ldU16 (this + 34)
  if ((UInt32.toInt32 (UInt16.toUInt32 (t'1))) == (0 : Int32)) then
    return false
  let t'2 ← rc
  let t'3 ← RC_Channels.get_override_timeout_ms t'2 (fp + 0)
  if !t'3 then
    return true
  let t'4 ← PMem.ldU32 (fp + 0)
  if (t'4 == (Int32.toUInt32 ((0 : Int32)))) then
    return false
  let t'5 ← PMem.ldU32 (this + 36)
  let t'6 ← PMem.ldU32 (fp + 0)
  return (decide (((((← PMem.clock) / 1000).toUInt32) - t'5) < t'6))

def RC_Channel.has_override (this : UInt64) : PMem.M Bool := do
  let fp ← PMem.enter 4
  let r ← RC_Channel.has_override.body fp this
  PMem.leave fp
  return r

/-- C++ `RC_Channel::get_control_mid : int16_t () const`, `RC_Channel.cpp:327-338`. -/
def RC_Channel.get_control_mid (this : UInt64) : PMem.M Int16 := do
  let t'1 ← PMem.ldI32 (this + 28)
  if (t'1 == (1 : Int32)) then
    let t'2 ← AP_ParamTBase'short_2.get (this + 18)
    let t'3 ← PMem.ldI16 t'2
    let t'4 ← AP_ParamTBase'short_2.get (this + 22)
    let t'5 ← PMem.ldI16 t'4
    let mut r_in : Int16 := Int32.toInt16 ((((Int16.toInt32 (t'3)) + (Int16.toInt32 (t'5))) / (2 : Int32)))
    let t'6 ← AP_ParamT'short_2.operator_const_short__ (this + 18)
    let t'7 ← PMem.ldI16 t'6
    let t'8 ← AP_ParamT'short_2.operator_const_short__ (this + 26)
    let t'9 ← PMem.ldI16 t'8
    let mut radio_trim_low : Int16 := Int32.toInt16 (((Int16.toInt32 (t'7)) + (Int16.toInt32 (t'9))))
    let t'10 ← PMem.ldI16 (this + 32)
    let t'11 ← AP_ParamT'short_2.operator_const_short__ (this + 22)
    let t'12 ← PMem.ldI16 t'11
    return Int32.toInt16 ((((Int16.toInt32 (t'10)) * ((Int16.toInt32 (r_in)) - (Int16.toInt32 (radio_trim_low)))) / ((Int16.toInt32 (t'12)) - (Int16.toInt32 (radio_trim_low)))))
  else
    return Int32.toInt16 ((0 : Int32))

/-- C++ `RC_Channels::arming_check_throttle : bool () const`, `RC_Channel.h:690-692`. -/
def RC_Channels.arming_check_throttle (this : UInt64) : PMem.M Bool := do
  let t'1 ← RC_Channels.option_is_enabled this (32 : Int32)
  return t'1

/-- C++ `RC_Channels::last_input_ms : uint32_t () const`, `RC_Channel.h:727-?`. -/
def RC_Channels.last_input_ms (this : UInt64) : PMem.M UInt32 := do
  let t'1 ← PMem.ldU32 (this + 8)
  return t'1

/-- C++ `RC_Channel::ch : uint8_t () const`, `RC_Channel.h:49-?`. -/
def RC_Channel.ch (this : UInt64) : PMem.M UInt8 := do
  let t'1 ← PMem.ldU8 (this + 10)
  return Int8.toUInt8 (Int32.toInt8 (((UInt32.toInt32 (UInt8.toUInt32 (t'1))) + (1 : Int32))))

/-- C++ `RC_Channel::percent_input : uint8_t () const`, `RC_Channel.cpp:488-501`. -/
def RC_Channel.percent_input (this : UInt64) : PMem.M UInt8 := do
  let t'1 ← PMem.ldI16 (this + 12)
  let t'2 ← AP_ParamT'short_2.operator_const_short__ (this + 18)
  let t'3 ← PMem.ldI16 t'2
  if (decide ((Int16.toInt32 (t'1)) ≤ (Int16.toInt32 (t'3)))) then
    let t'4 ← AP_ParamT'signed_char_1.operator_const_signed_char__ (this + 24)
    let t'5 ← PMem.ldI8 t'4
    let mut c'6 : Int32 := default
    if t'5 != (0 : Int8) then
      c'6 := (100 : Int32)
    else
      c'6 := (0 : Int32)
    return Int8.toUInt8 (Int32.toInt8 (c'6))
  let t'7 ← PMem.ldI16 (this + 12)
  let t'8 ← AP_ParamT'short_2.operator_const_short__ (this + 22)
  let t'9 ← PMem.ldI16 t'8
  if (decide ((Int16.toInt32 (t'7)) ≥ (Int16.toInt32 (t'9)))) then
    let t'10 ← AP_ParamT'signed_char_1.operator_const_signed_char__ (this + 24)
    let t'11 ← PMem.ldI8 t'10
    let mut c'12 : Int32 := default
    if t'11 != (0 : Int8) then
      c'12 := (0 : Int32)
    else
      c'12 := (100 : Int32)
    return Int8.toUInt8 (Int32.toInt8 (c'12))
  let t'13 ← PMem.ldI16 (this + 12)
  let t'14 ← AP_ParamT'short_2.operator_const_short__ (this + 18)
  let t'15 ← PMem.ldI16 t'14
  let t'16 ← AP_ParamT'short_2.operator_const_short__ (this + 22)
  let t'17 ← PMem.ldI16 t'16
  let t'18 ← AP_ParamT'short_2.operator_const_short__ (this + 18)
  let t'19 ← PMem.ldI16 t'18
  let mut ret : UInt8 := Binary32.toUInt8 ((((Binary32.ofBits 0x42c80000 /- 100 -/) * (Int32.toBinary32 (((Int16.toInt32 (t'13)) - (Int16.toInt32 (t'15)))))) / (Int32.toBinary32 (((Int16.toInt32 (t'17)) - (Int16.toInt32 (t'19)))))))
  let t'20 ← AP_ParamT'signed_char_1.operator_const_signed_char__ (this + 24)
  let t'21 ← PMem.ldI8 t'20
  if t'21 != (0 : Int8) then
    let t'22 := Int8.toUInt8 (Int32.toInt8 (((100 : Int32) - (UInt32.toInt32 (UInt8.toUInt32 (ret))))))
    ret := t'22
  return ret

/-- C++ `RC_Channels::set_override_start_throttle : void (int16_t)`, `RC_Channel.h:843-?`. -/
def RC_Channels.set_override_start_throttle (this : UInt64) (pwm : Int16) : PMem.M Unit := do
  let mut pwm := pwm
  PMem.stI16 (this + 16) pwm
  return ()

/-- `RC_Channel.do_aux_function_avoid_proximity` as a pure function of its arguments (it reads and writes no memory). -/
def RC_Channel.do_aux_function_avoid_proximity.pure' (this : UInt64) (ch_flag : UInt8) : Id Unit := do
  let mut ch_flag := ch_flag
  return ()

/-- C++ `RC_Channel::do_aux_function_avoid_proximity : void (const AuxSwitchPos)`, `RC_Channel.cpp:1116-1136`. -/
def RC_Channel.do_aux_function_avoid_proximity (this : UInt64) (ch_flag : UInt8) : PMem.M Unit :=
  pure (_root_.Vehicle_lib.RC_Channel.do_aux_function_avoid_proximity.pure' this ch_flag)

/-- C++ `RC_Channel::do_aux_function_mission_reset : void (const AuxSwitchPos)`, `RC_Channel.cpp:1401-1407`. -/
def RC_Channel.do_aux_function_mission_reset (this : UInt64) (ch_flag : UInt8) : PMem.M Unit := do
  let mut ch_flag := ch_flag
  if (ch_flag != (2 : UInt8)) then
    return ()
  let t'1 ← AP.mission
  AP_Mission.reset t'1
  return ()

/-- `RC_Channel.do_aux_function_fft_notch_tune` as a pure function of its arguments (it reads and writes no memory). -/
def RC_Channel.do_aux_function_fft_notch_tune.pure' (this : UInt64) (ch_flag : UInt8) : Id Unit := do
  let mut ch_flag := ch_flag
  return ()

/-- C++ `RC_Channel::do_aux_function_fft_notch_tune : void (const AuxSwitchPos)`, `RC_Channel.cpp:1410-1428`. -/
def RC_Channel.do_aux_function_fft_notch_tune (this : UInt64) (ch_flag : UInt8) : PMem.M Unit :=
  pure (_root_.Vehicle_lib.RC_Channel.do_aux_function_fft_notch_tune.pure' this ch_flag)

/-- C++ `RC_Channel::do_aux_function_lost_vehicle_sound : void (const AuxSwitchPos)`, `RC_Channel.cpp:1368-1381`. -/
def RC_Channel.do_aux_function_lost_vehicle_sound (this : UInt64) (ch_flag : UInt8) : PMem.M Unit := do
  let mut ch_flag := ch_flag
  let sw'1 := ch_flag
  if sw'1 == (2 : UInt8) then
    PMem.stB ((0xccc0 : UInt64) /- &AP_Notify::flags -/ + 23) true
  else if sw'1 == (1 : UInt8) then
    pure ()
  else if sw'1 == (0 : UInt8) then
    PMem.stB ((0xccc0 : UInt64) /- &AP_Notify::flags -/ + 23) false
  else
    pure ()
  return ()

/-- C++ `RC_Channel::set_angle : void (uint16_t)`, `RC_Channel.cpp:285-289`. -/
def RC_Channel.set_angle (this : UInt64) (angle : UInt16) : PMem.M Unit := do
  let mut angle := angle
  PMem.stI32 (this + 28) (0 : Int32)
  let t'1 := UInt16.toInt16 (angle)
  PMem.stI16 (this + 32) t'1
  return ()

/-- C++ `RC_Channel::set_range : void (uint16_t)`, `RC_Channel.cpp:279-283`. -/
def RC_Channel.set_range (this : UInt64) (high : UInt16) : PMem.M Unit := do
  let mut high := high
  PMem.stI32 (this + 28) (1 : Int32)
  let t'1 := UInt16.toInt16 (high)
  PMem.stI16 (this + 32) t'1
  return ()

/-- C++ `RC_Channel::set_default_dead_zone : void (int16_t)`, `RC_Channel.cpp:291-294`. -/
def RC_Channel.set_default_dead_zone.body (fp : UInt64) (this : UInt64) (dzone : Int16) : PMem.M Unit := do
  let mut dzone := dzone
  let t'1 ← PMem.iabs (Int16.toInt32 (dzone))
  PMem.stI16 (fp + 0) (Int32.toInt16 (t'1))
  AP_ParamTBase'short_2.set_default (this + 26) (fp + 0)
  return ()

def RC_Channel.set_default_dead_zone (this : UInt64) (dzone : Int16) : PMem.M Unit := do
  let fp ← PMem.enter 2
  let r ← RC_Channel.set_default_dead_zone.body fp this dzone
  PMem.leave fp
  return r

/-- C++ `RC_Channel::configured : bool ()`, `RC_Channel.h:123-?`. -/
def RC_Channel.configured (this : UInt64) : PMem.M Bool := do
  let t'1 ← AP_Param.configured (this + 18)
  let mut sc'3 := t'1
  if !sc'3 then
    let t'2 ← AP_Param.configured (this + 22)
    sc'3 := t'2
  let mut sc'5 := sc'3
  if !sc'5 then
    let t'4 ← AP_Param.configured (this + 20)
    sc'5 := t'4
  return sc'5

/-- C++ `RC_Channel::pwm_to_range_dz : float (uint16_t) const`, `RC_Channel.cpp:386-400`. -/
def RC_Channel.pwm_to_range_dz (this : UInt64) (_dead_zone : UInt16) : PMem.M Binary32 := do
  let mut _dead_zone := _dead_zone
  let t'1 ← PMem.ldI16 (this + 12)
  let t'2 ← AP_ParamTBase'short_2.get (this + 18)
  let t'3 ← PMem.ldI16 t'2
  let t'4 ← AP_ParamTBase'short_2.get (this + 22)
  let t'5 ← PMem.ldI16 t'4
  let t'6 ← constrain_int16 t'1 t'3 t'5
  let mut r_in : Int16 := t'6
  let t'7 ← AP_ParamT'signed_char_1.operator_const_signed_char__ (this + 24)
  let t'8 ← PMem.ldI8 t'7
  if t'8 != (0 : Int8) then
    let t'9 ← AP_ParamTBase'short_2.get (this + 22)
    let t'10 ← PMem.ldI16 t'9
    let t'11 ← AP_ParamTBase'short_2.get (this + 18)
    let t'12 ← PMem.ldI16 t'11
    let t'13 := Int32.toInt16 (((Int16.toInt32 (t'10)) - ((Int16.toInt32 (r_in)) - (Int16.toInt32 (t'12)))))
    r_in := t'13
  let t'14 ← AP_ParamT'short_2.operator_const_short__ (this + 18)
  let t'15 ← PMem.ldI16 t'14
  let mut radio_trim_low : Int16 := Int32.toInt16 (((Int16.toInt32 (t'15)) + (UInt32.toInt32 (UInt16.toUInt32 (_dead_zone)))))
  if (decide ((Int16.toInt32 (r_in)) > (Int16.toInt32 (radio_trim_low)))) then
    let t'16 ← PMem.ldI16 (this + 32)
    let t'17 ← AP_ParamT'short_2.operator_const_short__ (this + 22)
    let t'18 ← PMem.ldI16 t'17
    return (((Int16.toBinary32 (t'16)) * (Int32.toBinary32 (((Int16.toInt32 (r_in)) - (Int16.toInt32 (radio_trim_low)))))) / (Int32.toBinary32 (((Int16.toInt32 (t'18)) - (Int16.toInt32 (radio_trim_low))))))
  return Int32.toBinary32 ((0 : Int32))

/-- C++ `RC_Channel::pwm_to_range : float () const`, `RC_Channel.cpp:406-409`. -/
def RC_Channel.pwm_to_range (this : UInt64) : PMem.M Binary32 := do
  let t'1 ← AP_ParamT'short_2.operator_const_short__ (this + 26)
  let t'2 ← PMem.ldI16 t'1
  let t'3 ← RC_Channel.pwm_to_range_dz this (Int16.toUInt16 (t'2))
  return t'3

/-- C++ `RC_Channel::pwm_to_angle_dz_trim : float (uint16_t, uint16_t) const`, `RC_Channel.cpp:344-361`. -/
def RC_Channel.pwm_to_angle_dz_trim (this : UInt64) (_dead_zone : UInt16) (_trim : UInt16) : PMem.M Binary32 := do
  let mut _dead_zone := _dead_zone
  let mut _trim := _trim
  let mut radio_trim_high : Int16 := Int32.toInt16 (((UInt32.toInt32 (UInt16.toUInt32 (_trim))) + (UInt32.toInt32 (UInt16.toUInt32 (_dead_zone)))))
  let mut radio_trim_low : Int16 := Int32.toInt16 (((UInt32.toInt32 (UInt16.toUInt32 (_trim))) - (UInt32.toInt32 (UInt16.toUInt32 (_dead_zone)))))
  let t'1 ← AP_ParamT'signed_char_1.operator_const_signed_char__ (this + 24)
  let t'2 ← PMem.ldI8 t'1
  let mut c'3 : Int32 := default
  if t'2 != (0 : Int8) then
    c'3 := -(1 : Int32)
  else
    c'3 := (1 : Int32)
  let mut reverse_mul : Binary32 := Int32.toBinary32 (c'3)
  let t'4 ← PMem.ldI16 (this + 12)
  let t'5 ← AP_ParamTBase'short_2.get (this + 18)
  let t'6 ← PMem.ldI16 t'5
  let t'7 ← AP_ParamTBase'short_2.get (this + 22)
  let t'8 ← PMem.ldI16 t'7
  let t'9 ← constrain_int16 t'4 t'6 t'8
  let mut r_in : Int16 := t'9
  let mut sc'12 := (decide ((Int16.toInt32 (r_in)) > (Int16.toInt32 (radio_trim_high))))
  if sc'12 then
    let t'10 ← AP_ParamT'short_2.operator_const_short__ (this + 22)
    let t'11 ← PMem.ldI16 t'10
    sc'12 := ((Int16.toInt32 (t'11)) != (Int16.toInt32 (radio_trim_high)))
  if sc'12 then
    let t'13 ← PMem.ldI16 (this + 32)
    let t'14 ← AP_ParamT'short_2.operator_const_short__ (this + 22)
    let t'15 ← PMem.ldI16 t'14
    return ((reverse_mul * ((Int16.toBinary32 (t'13)) * (Int32.toBinary32 (((Int16.toInt32 (r_in)) - (Int16.toInt32 (radio_trim_high))))))) / (Int32.toBinary32 (((Int16.toInt32 (t'15)) - (Int16.toInt32 (radio_trim_high))))))
  else
    let mut sc'18 := (decide ((Int16.toInt32 (r_in)) < (Int16.toInt32 (radio_trim_low))))
    if sc'18 then
      let t'16 ← AP_ParamT'short_2.operator_const_short__ (this + 18)
      let t'17 ← PMem.ldI16 t'16
      sc'18 := ((Int16.toInt32 (radio_trim_low)) != (Int16.toInt32 (t'17)))
    if sc'18 then
      let t'19 ← PMem.ldI16 (this + 32)
      let t'20 ← AP_ParamT'short_2.operator_const_short__ (this + 18)
      let t'21 ← PMem.ldI16 t'20
      return ((reverse_mul * ((Int16.toBinary32 (t'19)) * (Int32.toBinary32 (((Int16.toInt32 (r_in)) - (Int16.toInt32 (radio_trim_low))))))) / (Int32.toBinary32 (((Int16.toInt32 (radio_trim_low)) - (Int16.toInt32 (t'21))))))
    else
      return Int32.toBinary32 ((0 : Int32))

/-- C++ `RC_Channel::pwm_to_angle_dz : float (uint16_t) const`, `RC_Channel.cpp:367-370`. -/
def RC_Channel.pwm_to_angle_dz (this : UInt64) (_dead_zone : UInt16) : PMem.M Binary32 := do
  let mut _dead_zone := _dead_zone
  let t'1 ← AP_ParamT'short_2.operator_const_short__ (this + 20)
  let t'2 ← PMem.ldI16 t'1
  let t'3 ← RC_Channel.pwm_to_angle_dz_trim this _dead_zone (Int16.toUInt16 (t'2))
  return t'3

/-- C++ `RC_Channel::pwm_to_angle : float () const`, `RC_Channel.cpp:376-379`. -/
def RC_Channel.pwm_to_angle (this : UInt64) : PMem.M Binary32 := do
  let t'1 ← AP_ParamT'short_2.operator_const_short__ (this + 26)
  let t'2 ← PMem.ldI16 t'1
  let t'3 ← RC_Channel.pwm_to_angle_dz this (Int16.toUInt16 (t'2))
  return t'3

/-- C++ `RC_Channel::update : bool ()`, `RC_Channel.cpp:302-321`. -/
def RC_Channel.update (this : UInt64) : PMem.M Bool := do
  let t'1 ← PMem.ldU64 ((0xba88 : UInt64) /- &hal -/ + 64)
  let t'2 ← PMem.ldU8 (this + 10)
  let t'3 ← PMem.halDev "AP_HAL::RCInput::read" t'1 #[(UInt8.toUInt64 (t'2))]
  let t'4 := UInt16.toInt16 ((UInt64.toUInt16 (t'3)))
  PMem.stI16 (this + 14) t'4
  let t'5 ← RC_Channel.has_override this
  let mut sc'8 := t'5
  if sc'8 then
    let t'6 ← rc
    let t'7 ← RC_Channels.option_is_enabled t'6 (2 : Int32)
    sc'8 := !t'7
  if sc'8 then
    let t'9 ← PMem.ldU16 (this + 34)
    let t'10 := UInt16.toInt16 (t'9)
    PMem.stI16 (this + 12) t'10
  else
    let t'11 ← rc
    let t'12 ← RC_Channels.has_had_rc_receiver t'11
    let mut sc'15 := t'12
    if sc'15 then
      let t'13 ← rc
      let t'14 ← RC_Channels.option_is_enabled t'13 (1 : Int32)
      sc'15 := !t'14
    if sc'15 then
      let t'16 ← PMem.ldI16 (this + 14)
      PMem.stI16 (this + 12) t'16
    else
      return false
  let t'17 ← PMem.ldI32 (this + 28)
  if (t'17 == (1 : Int32)) then
    let t'18 ← RC_Channel.pwm_to_range this
    let t'19 := Binary32.toInt16 (t'18)
    PMem.stI16 (this + 16) t'19
  else
    let t'20 ← RC_Channel.pwm_to_angle this
    let t'21 := Binary32.toInt16 (t'20)
    PMem.stI16 (this + 16) t'21
  return true

/-- C++ `RC_Channel::get_raw_radio_in : int16_t () const`, `RC_Channel.h:560-?`. -/
def RC_Channel.get_raw_radio_in (this : UInt64) : PMem.M Int16 := do
  let t'1 ← PMem.ldI16 (this + 14)
  return t'1

/-- C++ `RC_Channel::norm_input : float () const`, `RC_Channel.cpp:422-438`. -/
def RC_Channel.norm_input (this : UInt64) : PMem.M Binary32 := do
  let mut ret : Binary32 := default  -- uninitialized in C
  let t'1 ← AP_ParamT'signed_char_1.operator_const_signed_char__ (this + 24)
  let t'2 ← PMem.ldI8 t'1
  let mut c'3 : Int32 := default
  if t'2 != (0 : Int8) then
    c'3 := -(1 : Int32)
  else
    c'3 := (1 : Int32)
  let mut reverse_mul : Int16 := Int32.toInt16 (c'3)
  let t'4 ← PMem.ldI16 (this + 12)
  let t'5 ← AP_ParamT'short_2.operator_const_short__ (this + 20)
  let t'6 ← PMem.ldI16 t'5
  if (decide ((Int16.toInt32 (t'4)) < (Int16.toInt32 (t'6)))) then
    let t'7 ← AP_ParamT'short_2.operator_const_short__ (this + 18)
    let t'8 ← PMem.ldI16 t'7
    let t'9 ← AP_ParamT'short_2.operator_const_short__ (this + 20)
    let t'10 ← PMem.ldI16 t'9
    if (decide ((Int16.toInt32 (t'8)) ≥ (Int16.toInt32 (t'10)))) then
      return (Binary32.ofBits 0x00000000 /- 0 -/)
    let t'11 ← PMem.ldI16 (this + 12)
    let t'12 ← AP_ParamT'short_2.operator_const_short__ (this + 20)
    let t'13 ← PMem.ldI16 t'12
    let t'14 ← AP_ParamT'short_2.operator_const_short__ (this + 20)
    let t'15 ← PMem.ldI16 t'14
    let t'16 ← AP_ParamT'short_2.operator_const_short__ (this + 18)
    let t'17 ← PMem.ldI16 t'16
    let t'18 := (((Int32.toBinary32 ((Int16.toInt32 (reverse_mul)))) * (Int32.toBinary32 (((Int16.toInt32 (t'11)) - (Int16.toInt32 (t'13)))))) / (Int32.toBinary32 (((Int16.toInt32 (t'15)) - (Int16.toInt32 (t'17))))))
    ret := t'18
  else
    let t'19 ← AP_ParamT'short_2.operator_const_short__ (this + 22)
    let t'20 ← PMem.ldI16 t'19
    let t'21 ← AP_ParamT'short_2.operator_const_short__ (this + 20)
    let t'22 ← PMem.ldI16 t'21
    if (decide ((Int16.toInt32 (t'20)) ≤ (Int16.toInt32 (t'22)))) then
      return (Binary32.ofBits 0x00000000 /- 0 -/)
    let t'23 ← PMem.ldI16 (this + 12)
    let t'24 ← AP_ParamT'short_2.operator_const_short__ (this + 20)
    let t'25 ← PMem.ldI16 t'24
    let t'26 ← AP_ParamT'short_2.operator_const_short__ (this + 22)
    let t'27 ← PMem.ldI16 t'26
    let t'28 ← AP_ParamT'short_2.operator_const_short__ (this + 20)
    let t'29 ← PMem.ldI16 t'28
    let t'30 := (((Int32.toBinary32 ((Int16.toInt32 (reverse_mul)))) * (Int32.toBinary32 (((Int16.toInt32 (t'23)) - (Int16.toInt32 (t'25)))))) / (Int32.toBinary32 (((Int16.toInt32 (t'27)) - (Int16.toInt32 (t'29))))))
    ret := t'30
  let t'31 ← constrain_value_line'float ret (-(Binary32.ofBits 0x3f800000 /- 1 -/)) (Binary32.ofBits 0x3f800000 /- 1 -/) (Int32.toUInt32 ((437 : Int32)))
  return t'31

/-- C++ `RC_Channel::get_control_in_zero_dz : float () const`, `RC_Channel.cpp:412-418`. -/
def RC_Channel.get_control_in_zero_dz (this : UInt64) : PMem.M Binary32 := do
  let t'1 ← PMem.ldI32 (this + 28)
  if (t'1 == (1 : Int32)) then
    let t'2 ← RC_Channel.pwm_to_range_dz this (Int16.toUInt16 (Int32.toInt16 ((0 : Int32))))
    return t'2
  let t'3 ← RC_Channel.pwm_to_angle_dz this (Int16.toUInt16 (Int32.toInt16 ((0 : Int32))))
  return t'3

/-- C++ `RC_Channels::get_fs_timeout_ms : uint32_t () const`, `RC_Channel.h:758-?`. -/
def RC_Channels.get_fs_timeout_ms.body (fp : UInt64) (this : UInt64) : PMem.M UInt32 := do
  let t'1 ← AP_ParamT'float_4.operator_const_float__'1 (this + 32)
  let t'2 ← PMem.ldF32 t'1
  PMem.stF32 (fp + 0) (t'2 * (Int32.toBinary32 ((1000 : Int32))))
  PMem.stI32 (fp + 4) (100 : Int32)
  let t'3 ← MAX'float_int (fp + 0) (fp + 4)
  return Binary32.toUInt32 (t'3)

def RC_Channels.get_fs_timeout_ms (this : UInt64) : PMem.M UInt32 := do
  let fp ← PMem.enter 8
  let r ← RC_Channels.get_fs_timeout_ms.body fp this
  PMem.leave fp
  return r

/-- `RC_Channel.init_position_on_first_radio_read` as a pure function of its arguments (it reads and writes no memory). -/
def RC_Channel.init_position_on_first_radio_read.pure' (this : UInt64) (func : Int32) : Id Bool := do
  let mut func := func
  let sw'1 := func
  if sw'1 == (154 : Int32) || sw'1 == (153 : Int32) || sw'1 == (165 : Int32) then
    return true
  else
    return false

/-- C++ `RC_Channel::init_position_on_first_radio_read : bool (AUX_FUNC) const`, `RC_Channel.cpp:1051-1068`. -/
def RC_Channel.init_position_on_first_radio_read (this : UInt64) (func : Int32) : PMem.M Bool :=
  pure (_root_.Vehicle_lib.RC_Channel.init_position_on_first_radio_read.pure' this func)

/-- C++ `RC_Channel::string_for_aux_function : const char *(AUX_FUNC) const`, `RC_Channel.cpp:968-976`. -/
def RC_Channel.string_for_aux_function (this : UInt64) (function : Int32) : PMem.M UInt64 := do
  let mut function := function
  let __range1 : UInt64 := (0x13668 : UInt64) /- &RC_Channel::lookuptable -/
  let mut __begin1 : UInt64 := __range1
  let mut __end1 : UInt64 := (__range1 + ((19 : Int64) * 16).toUInt64)
  let mut first'1 := true
  for _ in PMem.loopFuel do
    if !first'1 then
      let t'2 := (__begin1 + 16)
      __begin1 := t'2
      pure ()
    first'1 := false
    if !((__begin1 != __end1)) then break
    let entry : UInt64 := __begin1
    let t'3 ← PMem.ldI32 entry
    if (t'3 == function) then
      let t'4 ← PMem.ldU64 (entry + 8)
      return t'4
  return (0 : UInt64)

/-- `RC_Channel.string_for_aux_pos` as a pure function of its arguments (it reads and writes no memory). -/
def RC_Channel.string_for_aux_pos.pure' (this : UInt64) (pos : UInt8) : Id UInt64 := do
  let mut pos := pos
  let sw'1 := pos
  if sw'1 == (2 : UInt8) then
    return (0x18e42 : UInt64) /- "HIGH" -/
  else if sw'1 == (1 : UInt8) then
    return (0x18e47 : UInt64) /- "MIDDLE" -/
  else if sw'1 == (0 : UInt8) then
    return (0x18e4e : UInt64) /- "LOW" -/
  else
    pure ()
  return (0x14223 : UInt64) /- "" -/

/-- C++ `RC_Channel::string_for_aux_pos : const char *(AuxSwitchPos) const`, `RC_Channel.cpp:979-990`. -/
def RC_Channel.string_for_aux_pos (this : UInt64) (pos : UInt8) : PMem.M UInt64 :=
  pure (_root_.Vehicle_lib.RC_Channel.string_for_aux_pos.pure' this pos)

/-- C++ `RC_Channels::RC_Channels : void ()`, `RC_Channels.cpp:43-53`. -/
def RC_Channels.RC_Channels (this : UInt64) : PMem.M Unit := do
  PMem.stI16 (this + 16) (Int32.toInt16 ((-(1 : Int32))))
  AP_Param.AP_Param'2 (this + 20)
  AP_Param.AP_Param'2 (this + 24)
  AP_Param.AP_Param'2 (this + 28)
  AP_Param.AP_Param'2 (this + 32)
  PMem.stB (this + 37) true
  AP_Param.setup_object_defaults this (0x7300 : UInt64) /- &RC_Channels::var_info -/
  let t'1 ← PMem.ldU64 (0xe528 : UInt64) /- &RC_Channels::_singleton -/
  if (t'1 != (0 : UInt64)) then
    pure ()
  PMem.stU64 (0xe528 : UInt64) /- &RC_Channels::_singleton -/ this
  return ()

/-- C++ `RC_Channel::RC_Channel : void ()`, `RC_Channel.cpp:274-277`. -/
def RC_Channel.RC_Channel (this : UInt64) : PMem.M Unit := do
  AP_Param.AP_Param'2 (this + 8)
  AP_Param.AP_Param'2 (this + 18)
  AP_Param.AP_Param'2 (this + 20)
  AP_Param.AP_Param'2 (this + 22)
  AP_Param.AP_Param'2 (this + 24)
  AP_Param.AP_Param'2 (this + 26)
  PMem.stI8 (this + 40) (Int32.toInt8 ((-(1 : Int32))))
  PMem.stI8 ((this + 40) + 1) (Int32.toInt8 ((-(1 : Int32))))
  AP_Param.setup_object_defaults this (0x8180 : UInt64) /- &RC_Channel::var_info -/
  return ()

end Vehicle_lib
