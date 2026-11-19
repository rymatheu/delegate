import ArduLean.Runtime.Hal
import ArduLean.Vehicle.libraries.AP_Math.AP_Math
import ArduLean.Vehicle.libraries.AP_HAL.AP_HAL
import ArduLean.Vehicle.libraries.AP_Param.AP_Param
import ArduLean.Vehicle.libraries.RC_Channel.RC_Channel
import ArduLean.Vehicle.ArduCopter.ArduCopter
import ArduLean.Vehicle.libraries.AP_Common.AP_Common
import ArduLean.Vehicle.libraries.AP_Scheduler.AP_Scheduler

/-!
ArduPilot `libraries/SRV_Channel`. Sources: `libraries/SRV_Channel/SRV_Channel_aux.cpp`, `libraries/SRV_Channel/SRV_Channel.cpp`, `libraries/SRV_Channel/SRV_Channels.cpp`, `libraries/SRV_Channel/SRV_Channel.h`, `libraries/SRV_Channel/SRV_Channel_config.h`.

Items of `lean/Vehicle_lib.lean` (the vehicle translation), unchanged; placed by `tools/split_modules.py` (`ArduLean/Vehicle/INDEX.md`).
-/

open FloatLib.Floats (Binary32 Binary64)

set_option linter.unusedVariables false
set_option linter.unreachableTactic false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false

namespace Vehicle_lib

/-- C++ `SRV_Channel::SRV_Channel : void ()`, `SRV_Channel.cpp:178-183`. -/
def SRV_Channel.SRV_Channel (this : UInt64) : PMem.M Unit := do
  AP_Param.AP_Param'2 (this + 0)
  AP_Param.AP_Param'2 (this + 2)
  AP_Param.AP_Param'2 (this + 4)
  AP_Param.AP_Param'2 (this + 6)
  AP_Enum16'SRV_Channel_Function.AP_Enum16 (this + 8)
  AP_Param.setup_object_defaults this (0x8080 : UInt64) /- &SRV_Channel::var_info -/
  let t'1 := ~~~(Int32.toUInt32 ((0 : Int32)))
  PMem.stU32 (0xbf68 : UInt64) /- &SRV_Channel::have_pwm_mask -/ t'1
  return ()

/-- C++ `SRV_Channels::SRV_Channels : void ()`, `SRV_Channels.cpp:344-362`. -/
def SRV_Channels.SRV_Channels.body (fp : UInt64) (this : UInt64) : PMem.M Unit := do
  SRV_Channel.SRV_Channel ((this + 4) + 0)
  SRV_Channel.SRV_Channel ((this + 4) + 20)
  SRV_Channel.SRV_Channel ((this + 4) + 40)
  SRV_Channel.SRV_Channel ((this + 4) + 60)
  SRV_Channel.SRV_Channel ((this + 4) + 80)
  SRV_Channel.SRV_Channel ((this + 4) + 100)
  SRV_Channel.SRV_Channel ((this + 4) + 120)
  SRV_Channel.SRV_Channel ((this + 4) + 140)
  SRV_Channel.SRV_Channel ((this + 4) + 160)
  SRV_Channel.SRV_Channel ((this + 4) + 180)
  SRV_Channel.SRV_Channel ((this + 4) + 200)
  SRV_Channel.SRV_Channel ((this + 4) + 220)
  SRV_Channel.SRV_Channel ((this + 4) + 240)
  SRV_Channel.SRV_Channel ((this + 4) + 260)
  SRV_Channel.SRV_Channel ((this + 4) + 280)
  SRV_Channel.SRV_Channel ((this + 4) + 300)
  SRV_Channel.SRV_Channel ((this + 4) + 320)
  SRV_Channel.SRV_Channel ((this + 4) + 340)
  SRV_Channel.SRV_Channel ((this + 4) + 360)
  SRV_Channel.SRV_Channel ((this + 4) + 380)
  SRV_Channel.SRV_Channel ((this + 4) + 400)
  SRV_Channel.SRV_Channel ((this + 4) + 420)
  SRV_Channel.SRV_Channel ((this + 4) + 440)
  SRV_Channel.SRV_Channel ((this + 4) + 460)
  SRV_Channel.SRV_Channel ((this + 4) + 480)
  SRV_Channel.SRV_Channel ((this + 4) + 500)
  SRV_Channel.SRV_Channel ((this + 4) + 520)
  SRV_Channel.SRV_Channel ((this + 4) + 540)
  SRV_Channel.SRV_Channel ((this + 4) + 560)
  SRV_Channel.SRV_Channel ((this + 4) + 580)
  SRV_Channel.SRV_Channel ((this + 4) + 600)
  SRV_Channel.SRV_Channel ((this + 4) + 620)
  AP_Param.AP_Param'2 (this + 644)
  AP_Param.AP_Param'2 (this + 646)
  AP_Param.AP_Param'2 (this + 648)
  AP_Param.AP_Param'2 (this + 649)
  AP_Param.AP_Param'2 (this + 652)
  AP_Param.AP_Param'2 (this + 656)
  AP_Param.AP_Param'2 (this + 660)
  HALSITL.Semaphore.Semaphore (this + 664)
  PMem.stU64 (0xbc40 : UInt64) /- &SRV_Channels::_singleton -/ this
  let t'1 := (this + 4)
  PMem.stU64 (0xbc48 : UInt64) /- &SRV_Channels::channels -/ t'1
  AP_Param.setup_object_defaults this (0x6c90 : UInt64) /- &SRV_Channels::var_info -/
  for i'2 in [0:32] do
    let i : UInt8 := UInt8.ofNat i'2
    let t'3 ← PMem.ldU64 (0xbc48 : UInt64) /- &SRV_Channels::channels -/
    PMem.stU8 ((t'3 + ((UInt64.toInt64 (UInt8.toUInt64 (i))) * 20).toUInt64) + 13) i
    if (decide ((UInt32.toInt32 (UInt8.toUInt32 (i))) ≥ (16 : Int32))) then
      PMem.stI16 (fp + 0) (Int32.toInt16 ((-1 : Int32)))
      let t'4 ← PMem.ldU64 (0xbc48 : UInt64) /- &SRV_Channels::channels -/
      AP_ParamTBase'short_2.set_default ((t'4 + ((UInt64.toInt64 (UInt8.toUInt64 (i))) * 20).toUInt64) + 8) (fp + 0)
  return ()

def SRV_Channels.SRV_Channels (this : UInt64) : PMem.M Unit := do
  let fp ← PMem.enter 2
  let r ← SRV_Channels.SRV_Channels.body fp this
  PMem.leave fp
  return r

/-- `SRV_Channels.get_motor_function` as a pure function of its arguments (it reads and writes no memory). -/
def SRV_Channels.get_motor_function.pure' (channel : UInt8) : Id Int32 := do
  let mut channel := channel
  if (decide ((UInt32.toInt32 (UInt8.toUInt32 (channel))) < (8 : Int32))) then
    return ((33 : Int32) + (UInt32.toInt32 (UInt8.toUInt32 (channel))))
  if (decide ((UInt32.toInt32 (UInt8.toUInt32 (channel))) < (12 : Int32))) then
    return ((82 : Int32) + ((UInt32.toInt32 (UInt8.toUInt32 (channel))) - (8 : Int32)))
  return ((160 : Int32) + ((UInt32.toInt32 (UInt8.toUInt32 (channel))) - (12 : Int32)))

/-- C++ `SRV_Channels::get_motor_function : SRV_Channel::Function (uint8_t)`, `SRV_Channel_config.h:572-580`. -/
def SRV_Channels.get_motor_function (channel : UInt8) : PMem.M Int32 :=
  pure (_root_.Vehicle_lib.SRV_Channels.get_motor_function.pure' channel)

/-- C++ `SRV_Channel::set_output_pwm : void (uint16_t, bool)`, `SRV_Channel.cpp:247-253`. -/
def SRV_Channel.set_output_pwm (this : UInt64) (pwm : UInt16) (force : Bool) : PMem.M Unit := do
  let mut pwm := pwm
  let mut force := force
  let t'1 ← PMem.ldB (this + 19)
  if ((!t'1) || force) then
    PMem.stU16 (this + 10) pwm
    let t'2 := (0xbf68 : UInt64) /- &SRV_Channel::have_pwm_mask -/
    let t'3 ← PMem.ldU32 t'2
    let t'4 ← PMem.ldU8 (this + 13)
    let t'5 := (t'3 ||| ((1 : UInt32) <<< (Int32.toUInt32 ((UInt32.toInt32 (UInt8.toUInt32 (t'4)))))))
    PMem.stU32 t'2 t'5
  return ()

/-- C++ `SRV_Channels::passthrough_disabled : bool ()`, `SRV_Channel_config.h:712-714`. -/
def SRV_Channels.passthrough_disabled  : PMem.M Bool := do
  let t'1 ← PMem.ldB (0x130b8 : UInt64) /- &SRV_Channels::disabled_passthrough -/
  return t'1

/-- C++ `SRV_Channel::pwm_from_angle : uint16_t (float) const`, `SRV_Channel.cpp:199-213`. -/
def SRV_Channel.pwm_from_angle (this : UInt64) (scaled_value : Binary32) : PMem.M UInt16 := do
  let mut scaled_value := scaled_value
  let t'1 ← PMem.ldU16 (this + 14)
  if ((UInt32.toInt32 (UInt16.toUInt32 (t'1))) == (0 : Int32)) then
    let t'2 ← AP_ParamT'short_2.operator_const_short__ (this + 4)
    let t'3 ← PMem.ldI16 t'2
    return Int16.toUInt16 (t'3)
  let t'4 ← AP_ParamT'signed_char_1.operator_const_signed_char__ (this + 6)
  let t'5 ← PMem.ldI8 t'4
  if t'5 != (0 : Int8) then
    let t'6 := -scaled_value
    scaled_value := t'6
  let t'7 ← PMem.ldU16 (this + 14)
  let t'8 ← PMem.ldU16 (this + 14)
  let t'9 ← constrain_value_line'float scaled_value (Int32.toBinary32 ((-(UInt32.toInt32 (UInt16.toUInt32 (t'7)))))) (UInt16.toBinary32 (t'8)) (Int32.toUInt32 ((207 : Int32)))
  scaled_value := t'9
  if (decide (scaled_value > (Int32.toBinary32 ((0 : Int32))))) then
    let t'10 ← AP_ParamT'short_2.operator_const_short__ (this + 4)
    let t'11 ← PMem.ldI16 t'10
    let t'12 ← AP_ParamT'short_2.operator_const_short__ (this + 2)
    let t'13 ← PMem.ldI16 t'12
    let t'14 ← AP_ParamT'short_2.operator_const_short__ (this + 4)
    let t'15 ← PMem.ldI16 t'14
    let t'16 ← PMem.ldU16 (this + 14)
    return Int16.toUInt16 (Int32.toInt16 (((Int16.toInt32 (t'11)) + (UInt32.toInt32 (UInt16.toUInt32 ((Binary32.toUInt16 (((scaled_value * (Int32.toBinary32 (((Int16.toInt32 (t'13)) - (Int16.toInt32 (t'15)))))) / (UInt16.toBinary32 (t'16)))))))))))
  else
    let t'17 ← AP_ParamT'short_2.operator_const_short__ (this + 4)
    let t'18 ← PMem.ldI16 t'17
    let t'19 ← AP_ParamT'short_2.operator_const_short__ (this + 4)
    let t'20 ← PMem.ldI16 t'19
    let t'21 ← AP_ParamT'short_2.operator_const_short__ this
    let t'22 ← PMem.ldI16 t'21
    let t'23 ← PMem.ldU16 (this + 14)
    return Int16.toUInt16 (Int32.toInt16 (((Int16.toInt32 (t'18)) - (UInt32.toInt32 (UInt16.toUInt32 ((Binary32.toUInt16 ((((-scaled_value) * (Int32.toBinary32 (((Int16.toInt32 (t'20)) - (Int16.toInt32 (t'22)))))) / (UInt16.toBinary32 (t'23)))))))))))

/-- C++ `SRV_Channel::pwm_from_range : uint16_t (float) const`, `SRV_Channel.cpp:186-196`. -/
def SRV_Channel.pwm_from_range (this : UInt64) (scaled_value : Binary32) : PMem.M UInt16 := do
  let mut scaled_value := scaled_value
  let t'1 ← AP_ParamT'short_2.operator_const_short__ (this + 2)
  let t'2 ← PMem.ldI16 t'1
  let t'3 ← AP_ParamT'short_2.operator_const_short__ this
  let t'4 ← PMem.ldI16 t'3
  let mut sc'6 := (decide ((Int16.toInt32 (t'2)) ≤ (Int16.toInt32 (t'4))))
  if !sc'6 then
    let t'5 ← PMem.ldU16 (this + 14)
    sc'6 := ((UInt32.toInt32 (UInt16.toUInt32 (t'5))) == (0 : Int32))
  if sc'6 then
    let t'7 ← AP_ParamT'short_2.operator_const_short__ this
    let t'8 ← PMem.ldI16 t'7
    return Int16.toUInt16 (t'8)
  let t'9 ← PMem.ldU16 (this + 14)
  let t'10 ← constrain_value_line'float scaled_value (Int32.toBinary32 ((0 : Int32))) (UInt16.toBinary32 (t'9)) (Int32.toUInt32 ((191 : Int32)))
  scaled_value := t'10
  let t'11 ← AP_ParamT'signed_char_1.operator_const_signed_char__ (this + 6)
  let t'12 ← PMem.ldI8 t'11
  if t'12 != (0 : Int8) then
    let t'13 ← PMem.ldU16 (this + 14)
    let t'14 := ((Int32.toBinary32 ((UInt32.toInt32 (UInt16.toUInt32 (t'13))))) - scaled_value)
    scaled_value := t'14
  let t'15 ← AP_ParamT'short_2.operator_const_short__ this
  let t'16 ← PMem.ldI16 t'15
  let t'17 ← AP_ParamT'short_2.operator_const_short__ (this + 2)
  let t'18 ← PMem.ldI16 t'17
  let t'19 ← AP_ParamT'short_2.operator_const_short__ this
  let t'20 ← PMem.ldI16 t'19
  let t'21 ← PMem.ldU16 (this + 14)
  return Int16.toUInt16 (Int32.toInt16 (((Int16.toInt32 (t'16)) + (UInt32.toInt32 (UInt16.toUInt32 ((Binary32.toUInt16 (((scaled_value * (Int32.toBinary32 (((Int16.toInt32 (t'18)) - (Int16.toInt32 (t'20)))))) / (UInt16.toBinary32 (t'21)))))))))))

/-- C++ `SRV_Channels::get_rc_fs_mask : uint32_t ()`, `SRV_Channel.h:561-?`. -/
def SRV_Channels.get_rc_fs_mask  : PMem.M UInt32 := do
  let t'1 ← PMem.ldU64 (0xbc40 : UInt64) /- &SRV_Channels::_singleton -/
  let t'2 ← AP_ParamTBase'unsigned_int_3.get (t'1 + 656)
  let t'3 ← PMem.ldU32 t'2
  return t'3

/-- C++ `SRV_Channel::output_ch : void ()`, `SRV_Channel_aux.cpp:32-102`. -/
def SRV_Channel.output_ch (this : UInt64) : PMem.M Unit := do
  let mut passthrough_from : Int8 := Int32.toInt8 ((-(1 : Int32)))
  let mut passthrough_mapped : Bool := false
  let t'1 ← AP_ParamTBase'short_2.get (this + 8)
  let t'2 ← PMem.ldI16 t'1
  let sw'3 := Int16.toInt32 (t'2)
  if sw'3 == (1 : Int32) then
    let t'4 ← PMem.ldU8 (this + 13)
    let t'5 := UInt8.toInt8 (t'4)
    passthrough_from := t'5
  else if (decide ((51 : Int32) ≤ sw'3) && decide (sw'3 ≤ (66 : Int32))) then
    let t'6 ← AP_ParamT'short_2.operator_const_short__ (this + 8)
    let t'7 ← PMem.ldI16 t'6
    let t'8 := Int32.toInt8 (((Int16.toInt32 (t'7)) - (51 : Int32)))
    passthrough_from := t'8
  else if (decide ((140 : Int32) ≤ sw'3) && decide (sw'3 ≤ (155 : Int32))) then
    let t'9 ← AP_ParamT'short_2.operator_const_short__ (this + 8)
    let t'10 ← PMem.ldI16 t'9
    let t'11 := Int32.toInt8 (((Int16.toInt32 (t'10)) - (140 : Int32)))
    passthrough_from := t'11
    passthrough_mapped := true
  else
    pure ()
  if ((Int8.toInt32 (passthrough_from)) != (-(1 : Int32))) then
    let t'12 ← rc
    let t'13 ← RC_Channels_Copter.channel t'12 (Int8.toUInt8 (passthrough_from))
    let mut c : UInt64 := t'13
    if (c != 0) then
      let t'14 ← SRV_Channels.passthrough_disabled
      if t'14 then
        let t'15 ← RC_Channel.get_radio_trim c
        let t'16 := Int16.toUInt16 (t'15)
        PMem.stU16 (this + 10) t'16
      else
        let t'17 ← RC_Channel.get_radio_in c
        let mut radio_in : Int16 := t'17
        if passthrough_mapped then
          let t'18 ← rc
          let t'19 ← RC_Channels_Copter.has_valid_input t'18
          if t'19 then
            let t'20 ← RC_Channel.get_type c
            let sw'21 := t'20
            if sw'21 == (0 : Int32) then
              let t'22 ← RC_Channel.norm_input_dz c
              let t'23 ← SRV_Channel.pwm_from_angle this (t'22 * (Int32.toBinary32 ((4500 : Int32))))
              let t'24 := UInt16.toInt16 (t'23)
              radio_in := t'24
            else if sw'21 == (1 : Int32) then
              let t'25 ← RC_Channel.norm_input_ignore_trim c
              let t'26 ← SRV_Channel.pwm_from_range this (((t'25 + (Binary64.toBinary32 ((Binary64.ofBits 0x3ff0000000000000 /- 1 -/)))) * (Binary64.toBinary32 ((Binary64.ofBits 0x3fe0000000000000 /- 1/2 -/)))) * (Int32.toBinary32 ((4500 : Int32))))
              let t'27 := UInt16.toInt16 (t'26)
              radio_in := t'27
            else
              pure ()
          else
            let t'28 ← SRV_Channels.get_rc_fs_mask
            let mut sc'31 := (((1 : UInt32) <<< (Int32.toUInt32 ((Int8.toInt32 (passthrough_from))))) &&& t'28) != (0 : UInt32)
            if sc'31 then
              let t'29 ← rc
              let t'30 ← RC_Channels_Copter.in_rc_failsafe t'29
              sc'31 := t'30
            if sc'31 then
              let t'32 ← SRV_Channel.pwm_from_angle this (Int32.toBinary32 ((0 : Int32)))
              let t'33 := UInt16.toInt16 (t'32)
              radio_in := t'33
            else
              let t'34 ← PMem.ldI16 (this + 16)
              radio_in := t'34
        let t'35 ← PMem.ldB (this + 18)
        if !t'35 then
          let t'36 := Int16.toUInt16 (radio_in)
          PMem.stU16 (this + 10) t'36
          PMem.stI16 (this + 16) radio_in
        else
          let t'37 ← PMem.ldI16 (this + 16)
          let t'38 ← PMem.iabs ((Int16.toInt32 (radio_in)) - (Int16.toInt32 (t'37)))
          let t'39 ← RC_Channel.get_dead_zone c
          if (decide (t'38 > (UInt32.toInt32 (UInt16.toUInt32 (t'39))))) then
            let t'40 := Int16.toUInt16 (radio_in)
            PMem.stU16 (this + 10) t'40
            PMem.stB (this + 18) false
  let t'41 ← PMem.ldU32 (0xe530 : UInt64) /- &SRV_Channels::disabled_mask -/
  let t'42 ← PMem.ldU8 (this + 13)
  if !((t'41 &&& ((1 : UInt32) <<< (Int32.toUInt32 ((UInt32.toInt32 (UInt8.toUInt32 (t'42))))))) != (0 : UInt32)) then
    let t'43 ← PMem.ldU64 ((0xba88 : UInt64) /- &hal -/ + 72)
    let t'44 ← PMem.ldU8 (this + 13)
    let t'45 ← PMem.ldU16 (this + 10)
    discard <| PMem.halDev "AP_HAL::RCOutput::write" t'43 #[(UInt8.toUInt64 (t'44)), (UInt16.toUInt64 (t'45))]
  return ()

/-- `SRV_Channel.valid_function'2` as a pure function of its arguments (it reads and writes no memory). -/
def SRV_Channel.valid_function'2.pure' (fn : Int32) : Id Bool := do
  let mut fn := fn
  return ((decide (fn ≥ (0 : Int32))) && (decide (fn < (190 : Int32))))

/-- C++ `SRV_Channel::valid_function : bool (Function)`, `SRV_Channel.h:232-234`. -/
def SRV_Channel.valid_function'2 (fn : Int32) : PMem.M Bool :=
  pure (_root_.Vehicle_lib.SRV_Channel.valid_function'2.pure' fn)

/-- C++ `SRV_Channel::valid_function : bool () const`, `SRV_Channel.h:235-237`. -/
def SRV_Channel.valid_function (this : UInt64) : PMem.M Bool := do
  let t'1 ← AP_Enum16'SRV_Channel_Function.operator_const_SRV_Channel.Function (this + 8)
  let t'2 ← SRV_Channel.valid_function'2 t'1
  return t'2

/-- C++ `SRV_Channel::set_range : void (uint16_t)`, `SRV_Channel.cpp:271-276`. -/
def SRV_Channel.set_range (this : UInt64) (high : UInt16) : PMem.M Unit := do
  let mut high := high
  PMem.stBits this 96 1 (if false then (1 : UInt64) else 0)
  PMem.stU16 (this + 14) high
  PMem.stBits this 97 1 (if true then (1 : UInt64) else 0)
  return ()

/-- C++ `SRV_Channel::set_angle : void (int16_t)`, `SRV_Channel.cpp:263-268`. -/
def SRV_Channel.set_angle (this : UInt64) (angle : Int16) : PMem.M Unit := do
  let mut angle := angle
  PMem.stBits this 96 1 (if true then (1 : UInt64) else 0)
  let t'1 := Int16.toUInt16 (angle)
  PMem.stU16 (this + 14) t'1
  PMem.stBits this 97 1 (if true then (1 : UInt64) else 0)
  return ()

/-- C++ `SRV_Channel::aux_servo_function_setup : void ()`, `SRV_Channel_aux.cpp:134-219`. -/
def SRV_Channel.aux_servo_function_setup (this : UInt64) : PMem.M Unit := do
  let t'1 ← PMem.ldBits this 97 1
  if (t'1 != 0) then
    return ()
  let t'2 ← AP_ParamTBase'short_2.get (this + 8)
  let t'3 ← PMem.ldI16 t'2
  let sw'4 := Int16.toInt32 (t'3)
  if sw'4 == (2 : Int32) || sw'4 == (3 : Int32) || sw'4 == (11 : Int32) || sw'4 == (156 : Int32) then
    SRV_Channel.set_range this (Int16.toUInt16 (Int32.toInt16 ((100 : Int32))))
  else if sw'4 == (31 : Int32) || sw'4 == (32 : Int32) || sw'4 == (41 : Int32) || sw'4 == (81 : Int32) || sw'4 == (126 : Int32) then
    SRV_Channel.set_range this (Int16.toUInt16 (Int32.toInt16 ((1000 : Int32))))
  else if sw'4 == (18 : Int32) || sw'4 == (20 : Int32) || sw'4 == (4 : Int32) || sw'4 == (19 : Int32) || sw'4 == (16 : Int32) || sw'4 == (86 : Int32) || sw'4 == (17 : Int32) || sw'4 == (87 : Int32) || sw'4 == (21 : Int32) || sw'4 == (26 : Int32) || sw'4 == (24 : Int32) || sw'4 == (25 : Int32) || sw'4 == (75 : Int32) || sw'4 == (76 : Int32) || sw'4 == (45 : Int32) || sw'4 == (46 : Int32) || sw'4 == (47 : Int32) || sw'4 == (77 : Int32) || sw'4 == (78 : Int32) || sw'4 == (79 : Int32) || sw'4 == (80 : Int32) || sw'4 == (94 : Int32) || sw'4 == (95 : Int32) || sw'4 == (96 : Int32) || sw'4 == (97 : Int32) || sw'4 == (98 : Int32) || sw'4 == (99 : Int32) || sw'4 == (100 : Int32) || sw'4 == (101 : Int32) || sw'4 == (102 : Int32) || sw'4 == (103 : Int32) || sw'4 == (104 : Int32) || sw'4 == (105 : Int32) || sw'4 == (106 : Int32) || sw'4 == (107 : Int32) || sw'4 == (108 : Int32) || sw'4 == (109 : Int32) || sw'4 == (124 : Int32) || sw'4 == (125 : Int32) || sw'4 == (127 : Int32) || (decide ((140 : Int32) ≤ sw'4) && decide (sw'4 ≤ (155 : Int32))) then
    SRV_Channel.set_angle this (Int32.toInt16 ((4500 : Int32)))
  else if sw'4 == (70 : Int32) || sw'4 == (73 : Int32) || sw'4 == (74 : Int32) || sw'4 == (110 : Int32) then
    SRV_Channel.set_range this (Int16.toUInt16 (Int32.toInt16 ((100 : Int32))))
  else if sw'4 == (180 : Int32) || sw'4 == (92 : Int32) || sw'4 == (181 : Int32) || sw'4 == (182 : Int32) || sw'4 == (183 : Int32) then
    SRV_Channel.set_range this (Int16.toUInt16 (Int32.toInt16 ((1000 : Int32))))
  else if (decide ((184 : Int32) ≤ sw'4) && decide (sw'4 ≤ (189 : Int32))) then
    SRV_Channel.set_angle this (Int32.toInt16 ((1 : Int32)))
  else
    pure ()
  return ()

/-- C++ `SRV_Channels::update_aux_servo_function : void ()`, `SRV_Channel_aux.cpp:222-246`. -/
def SRV_Channels.update_aux_servo_function  : PMem.M Unit := do
  let t'1 ← PMem.ldU64 (0xbc48 : UInt64) /- &SRV_Channels::channels -/
  if !(t'1 != 0) then
    return ()
  Bitmask'190.clearall (0xe538 : UInt64) /- &SRV_Channels::function_mask -/
  for i'2 in [0:190] do
    let i : UInt16 := UInt16.ofNat i'2
    let t'3 := Int32.toUInt32 ((0 : Int32))
    PMem.stU32 ((0xe550 : UInt64) /- &SRV_Channels::functions -/ + ((UInt64.toInt64 (UInt16.toUInt64 (i))) * 8).toUInt64) t'3
  let t'4 := Int32.toUInt32 ((0 : Int32))
  PMem.stU32 (0xeb40 : UInt64) /- &SRV_Channels::invalid_mask -/ t'4
  for i'2'5 in [0:32] do
    let i'2 : UInt8 := UInt8.ofNat i'2'5
    let t'6 ← PMem.ldU64 (0xbc48 : UInt64) /- &SRV_Channels::channels -/
    let t'7 ← SRV_Channel.valid_function (t'6 + ((UInt64.toInt64 (UInt8.toUInt64 (i'2))) * 20).toUInt64)
    if !t'7 then
      let t'8 := (0xeb40 : UInt64) /- &SRV_Channels::invalid_mask -/
      let t'9 ← PMem.ldU32 t'8
      let t'10 := (t'9 ||| ((1 : UInt32) <<< (Int32.toUInt32 ((UInt32.toInt32 (UInt8.toUInt32 (i'2)))))))
      PMem.stU32 t'8 t'10
      continue
    let t'11 ← PMem.ldU64 (0xbc48 : UInt64) /- &SRV_Channels::channels -/
    let t'12 ← AP_ParamTBase'short_2.get ((t'11 + ((UInt64.toInt64 (UInt8.toUInt64 (i'2))) * 20).toUInt64) + 8)
    let t'13 ← PMem.ldI16 t'12
    let mut function : UInt16 := Int16.toUInt16 (t'13)
    let t'14 ← PMem.ldU64 (0xbc48 : UInt64) /- &SRV_Channels::channels -/
    SRV_Channel.aux_servo_function_setup (t'14 + ((UInt64.toInt64 (UInt8.toUInt64 (i'2))) * 20).toUInt64)
    Bitmask'190.set (0xe538 : UInt64) /- &SRV_Channels::function_mask -/ function
    let t'15 := ((0xe550 : UInt64) /- &SRV_Channels::functions -/ + ((UInt64.toInt64 (UInt16.toUInt64 (function))) * 8).toUInt64)
    let t'16 ← PMem.ldU32 t'15
    let t'17 := (t'16 ||| ((1 : UInt32) <<< (Int32.toUInt32 ((UInt32.toInt32 (UInt8.toUInt32 (i'2)))))))
    PMem.stU32 t'15 t'17
  PMem.stB (0xeb48 : UInt64) /- &SRV_Channels::initialised -/ true
  return ()

/-- C++ `SRV_Channels::function_assigned : bool (SRV_Channel::Function)`, `SRV_Channel_aux.cpp:538-545`. -/
def SRV_Channels.function_assigned (function : Int32) : PMem.M Bool := do
  let mut function := function
  let t'1 ← PMem.ldB (0xeb48 : UInt64) /- &SRV_Channels::initialised -/
  if !t'1 then
    SRV_Channels.update_aux_servo_function
  let t'2 ← Bitmask'190.get (0xe538 : UInt64) /- &SRV_Channels::function_mask -/ (Int16.toUInt16 (Int32.toInt16 (function)))
  return t'2

/-- C++ `SRV_Channels::set_output_pwm : void (SRV_Channel::Function, uint16_t)`, `SRV_Channel_aux.cpp:352-364`. -/
def SRV_Channels.set_output_pwm (function : Int32) (value : UInt16) : PMem.M Unit := do
  let mut function := function
  let mut value := value
  let t'1 ← SRV_Channels.function_assigned function
  if !t'1 then
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
    if !((decide ((UInt8.toUInt64 (i)) < ((640 : UInt64) / (20 : UInt64))))) then break
    let t'5 ← PMem.ldU64 (0xbc48 : UInt64) /- &SRV_Channels::channels -/
    let t'6 ← AP_Enum16'SRV_Channel_Function.operator_const_SRV_Channel.Function ((t'5 + ((UInt64.toInt64 (UInt8.toUInt64 (i))) * 20).toUInt64) + 8)
    if (t'6 == function) then
      let t'7 ← PMem.ldU64 (0xbc48 : UInt64) /- &SRV_Channels::channels -/
      SRV_Channel.set_output_pwm (t'7 + ((UInt64.toInt64 (UInt8.toUInt64 (i))) * 20).toUInt64) value false
      let t'8 ← PMem.ldU64 (0xbc48 : UInt64) /- &SRV_Channels::channels -/
      SRV_Channel.output_ch (t'8 + ((UInt64.toInt64 (UInt8.toUInt64 (i))) * 20).toUInt64)
  return ()

/-- C++ `SRV_Channels::set_output_scaled : void (SRV_Channel::Function, float)`, `SRV_Channel_aux.cpp:638-644`. -/
def SRV_Channels.set_output_scaled (function : Int32) (value : Binary32) : PMem.M Unit := do
  let mut function := function
  let mut value := value
  let t'1 ← SRV_Channel.valid_function'2 function
  if t'1 then
    PMem.stF32 (((0xe550 : UInt64) /- &SRV_Channels::functions -/ + ((Int32.toInt64 (function)) * 8).toUInt64) + 4) value
    let t'2 := (0xbf68 : UInt64) /- &SRV_Channel::have_pwm_mask -/
    let t'3 ← PMem.ldU32 t'2
    let t'4 ← PMem.ldU32 ((0xe550 : UInt64) /- &SRV_Channels::functions -/ + ((Int32.toInt64 (function)) * 8).toUInt64)
    let t'5 := (t'3 &&& (~~~t'4))
    PMem.stU32 t'2 t'5
  return ()

/-- C++ `SRV_Channels::find_channel : bool (SRV_Channel::Function, uint8_t &)`, `SRV_Channel_aux.cpp:603-624`. -/
def SRV_Channels.find_channel (function : Int32) (chan : UInt64) : PMem.M Bool := do
  let mut function := function
  let t'1 ← PMem.ldB (0xeb48 : UInt64) /- &SRV_Channels::initialised -/
  if !t'1 then
    SRV_Channels.update_aux_servo_function
  let t'2 ← SRV_Channel.valid_function'2 function
  if !t'2 then
    return false
  let t'3 ← PMem.ldU32 ((0xe550 : UInt64) /- &SRV_Channels::functions -/ + ((Int32.toInt64 (function)) * 8).toUInt64)
  let t'4 ← PMem.ffs (UInt32.toInt32 (t'3))
  let mut first_chan : Int32 := t'4
  if (first_chan == (0 : Int32)) then
    return false
  let t'5 := Int8.toUInt8 (Int32.toInt8 ((first_chan - (1 : Int32))))
  PMem.stU8 chan t'5
  return true

/-- C++ `SRV_Channels::srv_channel : SRV_Channel *(uint8_t)`, `SRV_Channel.h:563-569`. -/
def SRV_Channels.srv_channel (i : UInt8) : PMem.M UInt64 := do
  let mut i := i
  let mut c'1 : UInt64 := default
  if (decide ((UInt32.toInt32 (UInt8.toUInt32 (i))) < (32 : Int32))) then
    let t'2 ← PMem.ldU64 (0xbc48 : UInt64) /- &SRV_Channels::channels -/
    c'1 := (t'2 + ((UInt64.toInt64 (UInt8.toUInt64 (i))) * 20).toUInt64)
  else
    c'1 := (0 : UInt64)
  return c'1

/-- C++ `SRV_Channel::get_function : SRV_Channel::Function () const`, `SRV_Channel.h:296-298`. -/
def SRV_Channel.get_function (this : UInt64) : PMem.M Int32 := do
  let t'1 ← AP_ParamTBase'short_2.get (this + 8)
  let t'2 ← PMem.ldI16 t'1
  return Int16.toInt32 (t'2)

/-- C++ `SRV_Channel::get_trim : uint16_t () const`, `SRV_Channel.h:282-284`. -/
def SRV_Channel.get_trim (this : UInt64) : PMem.M UInt16 := do
  let t'1 ← AP_ParamT'short_2.operator_const_short__ (this + 4)
  let t'2 ← PMem.ldI16 t'1
  return Int16.toUInt16 (t'2)

/-- C++ `SRV_Channel::get_output_min : uint16_t () const`, `SRV_Channel.h:276-278`. -/
def SRV_Channel.get_output_min (this : UInt64) : PMem.M UInt16 := do
  let t'1 ← AP_ParamT'short_2.operator_const_short__ this
  let t'2 ← PMem.ldI16 t'1
  return Int16.toUInt16 (t'2)

/-- C++ `SRV_Channel::get_output_max : uint16_t () const`, `SRV_Channel.h:279-281`. -/
def SRV_Channel.get_output_max (this : UInt64) : PMem.M UInt16 := do
  let t'1 ← AP_ParamT'short_2.operator_const_short__ (this + 2)
  let t'2 ← PMem.ldI16 t'1
  return Int16.toUInt16 (t'2)

/-- C++ `SRV_Channels::get_disabled_channel_mask : uint32_t ()`, `SRV_Channel_config.h:587-?`. -/
def SRV_Channels.get_disabled_channel_mask  : PMem.M UInt32 := do
  let t'1 ← PMem.ldU32 (0xe530 : UInt64) /- &SRV_Channels::disabled_mask -/
  return t'1

/-- `SRV_Channel.is_motor` as a pure function of its arguments (it reads and writes no memory). -/
def SRV_Channel.is_motor.pure' (function : Int32) : Id Bool := do
  let mut function := function
  return ((((decide (function ≥ (33 : Int32))) && (decide (function ≤ (40 : Int32)))) || ((decide (function ≥ (82 : Int32))) && (decide (function ≤ (85 : Int32))))) || ((decide (function ≥ (160 : Int32))) && (decide (function ≤ (179 : Int32)))))

/-- C++ `SRV_Channel::is_motor : bool (SRV_Channel::Function)`, `SRV_Channel.cpp:317-322`. -/
def SRV_Channel.is_motor (function : Int32) : PMem.M Bool :=
  pure (_root_.Vehicle_lib.SRV_Channel.is_motor.pure' function)

/-- `SRV_Channel.should_e_stop` as a pure function of its arguments (it reads and writes no memory). -/
def SRV_Channel.should_e_stop.pure' (function : Int32) : Id Bool := do
  let mut function := function
  let sw'1 := function
  if sw'1 == (31 : Int32) || sw'1 == (32 : Int32) || sw'1 == (33 : Int32) || sw'1 == (34 : Int32) || sw'1 == (35 : Int32) || sw'1 == (36 : Int32) || sw'1 == (37 : Int32) || sw'1 == (38 : Int32) || sw'1 == (39 : Int32) || sw'1 == (40 : Int32) || sw'1 == (69 : Int32) || sw'1 == (70 : Int32) || sw'1 == (73 : Int32) || sw'1 == (74 : Int32) || sw'1 == (81 : Int32) || sw'1 == (82 : Int32) || sw'1 == (83 : Int32) || sw'1 == (84 : Int32) || sw'1 == (85 : Int32) || (decide ((160 : Int32) ≤ sw'1) && decide (sw'1 ≤ (179 : Int32))) || sw'1 == (30 : Int32) then
    return true
  else
    return false
  return false

/-- C++ `SRV_Channel::should_e_stop : bool (SRV_Channel::Function)`, `SRV_Channel.cpp:325-354`. -/
def SRV_Channel.should_e_stop (function : Int32) : PMem.M Bool :=
  pure (_root_.Vehicle_lib.SRV_Channel.should_e_stop.pure' function)

/-- C++ `SRV_Channels::get_emergency_stop : bool ()`, `SRV_Channel_config.h:602-?`. -/
def SRV_Channels.get_emergency_stop  : PMem.M Bool := do
  let t'1 ← PMem.ldB (0x130c0 : UInt64) /- &SRV_Channels::emergency_stop -/
  return t'1

/-- C++ `SRV_Channels::set_emergency_stop : void (bool)`, `SRV_Channels.cpp:572-582`. -/
def SRV_Channels.set_emergency_stop (state : Bool) : PMem.M Unit := do
  let mut state := state
  PMem.stB (0x130c0 : UInt64) /- &SRV_Channels::emergency_stop -/ state
  return ()

/-- C++ `SRV_Channels::get_output_channel_mask : uint32_t (SRV_Channel::Function)`, `SRV_Channel_aux.cpp:676-685`. -/
def SRV_Channels.get_output_channel_mask (function : Int32) : PMem.M UInt32 := do
  let mut function := function
  let t'1 ← PMem.ldB (0xeb48 : UInt64) /- &SRV_Channels::initialised -/
  if !t'1 then
    SRV_Channels.update_aux_servo_function
  let t'2 ← SRV_Channel.valid_function'2 function
  if t'2 then
    let t'3 ← PMem.ldU32 ((0xe550 : UInt64) /- &SRV_Channels::functions -/ + ((Int32.toInt64 (function)) * 8).toUInt64)
    return t'3
  let t'4 ← PMem.ldU32 (0xeb40 : UInt64) /- &SRV_Channels::invalid_mask -/
  return t'4

/-- C++ `SRV_Channels::get_singleton : SRV_Channels *()`, `SRV_Channel_config.h:605-607`. -/
def SRV_Channels.get_singleton  : PMem.M UInt64 := do
  let t'1 ← PMem.ldU64 (0xbc40 : UInt64) /- &SRV_Channels::_singleton -/
  return t'1

/-- C++ `AP::srv : SRV_Channels &()`, `SRV_Channels.cpp:586-589`. -/
def AP.srv  : PMem.M UInt64 := do
  let t'1 ← SRV_Channels.get_singleton
  return t'1

/-- C++ `SRV_Channels::get_dshot_esc_type : AP_HAL::RCOutput::DshotEscType ()`, `SRV_Channel.h:557-?`. -/
def SRV_Channels.get_dshot_esc_type  : PMem.M UInt32 := do
  let t'1 ← PMem.ldU64 (0xbc40 : UInt64) /- &SRV_Channels::_singleton -/
  let t'2 ← AP_ParamTBase'signed_char_1.get (t'1 + 649)
  let t'3 ← PMem.ldI8 t'2
  return Int32.toUInt32 (Int8.toInt32 (t'3))

/-- C++ `SRV_Channels::set_range : void (SRV_Channel::Function, uint16_t)`, `SRV_Channel_aux.cpp:875-882`. -/
def SRV_Channels.set_range (function : Int32) (range : UInt16) : PMem.M Unit := do
  let mut function := function
  let mut range := range
  for i'1 in [0:32] do
    let i : UInt8 := UInt8.ofNat i'1
    let t'2 ← PMem.ldU64 (0xbc48 : UInt64) /- &SRV_Channels::channels -/
    let t'3 ← AP_Enum16'SRV_Channel_Function.operator_const_SRV_Channel.Function ((t'2 + ((UInt64.toInt64 (UInt8.toUInt64 (i))) * 20).toUInt64) + 8)
    if (t'3 == function) then
      let t'4 ← PMem.ldU64 (0xbc48 : UInt64) /- &SRV_Channels::channels -/
      SRV_Channel.set_range (t'4 + ((UInt64.toInt64 (UInt8.toUInt64 (i))) * 20).toUInt64) range
  return ()

/-- C++ `SRV_Channels::set_angle : void (SRV_Channel::Function, uint16_t)`, `SRV_Channel_aux.cpp:865-872`. -/
def SRV_Channels.set_angle (function : Int32) (angle : UInt16) : PMem.M Unit := do
  let mut function := function
  let mut angle := angle
  for i'1 in [0:32] do
    let i : UInt8 := UInt8.ofNat i'1
    let t'2 ← PMem.ldU64 (0xbc48 : UInt64) /- &SRV_Channels::channels -/
    let t'3 ← AP_Enum16'SRV_Channel_Function.operator_const_SRV_Channel.Function ((t'2 + ((UInt64.toInt64 (UInt8.toUInt64 (i))) * 20).toUInt64) + 8)
    if (t'3 == function) then
      let t'4 ← PMem.ldU64 (0xbc48 : UInt64) /- &SRV_Channels::channels -/
      SRV_Channel.set_angle (t'4 + ((UInt64.toInt64 (UInt8.toUInt64 (i))) * 20).toUInt64) (UInt16.toInt16 (angle))
  return ()

/-- C++ `SRV_Channels::set_aux_channel_default : bool (SRV_Channel::Function, uint8_t)`, `SRV_Channel_aux.cpp:576-600`. -/
def SRV_Channels.set_aux_channel_default.body (fp : UInt64) (function : Int32) (channel : UInt8) : PMem.M Bool := do
  let mut function := function
  let mut channel := channel
  let t'1 ← SRV_Channels.function_assigned function
  if t'1 then
    return true
  let t'2 ← PMem.ldU64 (0xbc48 : UInt64) /- &SRV_Channels::channels -/
  let t'3 ← AP_Enum16'SRV_Channel_Function.operator_const_SRV_Channel.Function ((t'2 + ((UInt64.toInt64 (UInt8.toUInt64 (channel))) * 20).toUInt64) + 8)
  let mut sc'7 := (t'3 != (0 : Int32))
  if sc'7 then
    let mut sc'6 := (decide ((UInt32.toInt32 (UInt8.toUInt32 (channel))) > (15 : Int32)))
    if sc'6 then
      let t'4 ← PMem.ldU64 (0xbc48 : UInt64) /- &SRV_Channels::channels -/
      let t'5 ← AP_Enum16'SRV_Channel_Function.operator_const_SRV_Channel.Function ((t'4 + ((UInt64.toInt64 (UInt8.toUInt64 (channel))) * 20).toUInt64) + 8)
      sc'6 := (t'5 == (-1 : Int32))
    sc'7 := !sc'6
  if sc'7 then
    let t'8 ← PMem.ldU64 (0xbc48 : UInt64) /- &SRV_Channels::channels -/
    let t'9 ← AP_Enum16'SRV_Channel_Function.operator_const_SRV_Channel.Function ((t'8 + ((UInt64.toInt64 (UInt8.toUInt64 (channel))) * 20).toUInt64) + 8)
    if (t'9 == function) then
      return true
    let t'10 ← PMem.ldU64 ((0xba88 : UInt64) /- &hal -/ + 48)
    let t'11 ← PMem.ldU64 (0xbc48 : UInt64) /- &SRV_Channels::channels -/
    let t'12 ← AP_ParamTBase'short_2.get ((t'11 + ((UInt64.toInt64 (UInt8.toUInt64 (channel))) * 20).toUInt64) + 8)
    let t'13 ← PMem.ldI16 t'12
    discard <| PMem.halDev "AP_HAL::BetterStream::printf" t'10 #[(0x18ef5 : UInt64) /- "Channel %u already assigned function %u\n" -/, (UInt32.toUInt64 ((Int32.toUInt32 (((UInt32.toInt32 (UInt8.toUInt32 (channel))) + (1 : Int32)))))), (UInt32.toUInt64 ((Int32.toUInt32 (Int16.toInt32 (t'13)))))]
    return false
  let t'14 ← PMem.ldU64 (0xbc48 : UInt64) /- &SRV_Channels::channels -/
  PMem.stBits (t'14 + ((UInt64.toInt64 (UInt8.toUInt64 (channel))) * 20).toUInt64) 97 1 (if false then (1 : UInt64) else 0)
  PMem.stI16 (fp + 0) (Int32.toInt16 (function))
  let t'15 ← PMem.ldU64 (0xbc48 : UInt64) /- &SRV_Channels::channels -/
  AP_ParamTBase'short_2.set_and_default ((t'15 + ((UInt64.toInt64 (UInt8.toUInt64 (channel))) * 20).toUInt64) + 8) (fp + 0)
  let t'16 ← PMem.ldU64 (0xbc48 : UInt64) /- &SRV_Channels::channels -/
  SRV_Channel.aux_servo_function_setup (t'16 + ((UInt64.toInt64 (UInt8.toUInt64 (channel))) * 20).toUInt64)
  Bitmask'190.set (0xe538 : UInt64) /- &SRV_Channels::function_mask -/ (Int16.toUInt16 (Int32.toInt16 (function)))
  let t'17 ← SRV_Channel.valid_function'2 function
  if t'17 then
    let t'18 := ((0xe550 : UInt64) /- &SRV_Channels::functions -/ + ((Int32.toInt64 (function)) * 8).toUInt64)
    let t'19 ← PMem.ldU32 t'18
    let t'20 := (t'19 ||| ((1 : UInt32) <<< (Int32.toUInt32 ((UInt32.toInt32 (UInt8.toUInt32 (channel)))))))
    PMem.stU32 t'18 t'20
  return true

def SRV_Channels.set_aux_channel_default (function : Int32) (channel : UInt8) : PMem.M Bool := do
  let fp ← PMem.enter 2
  let r ← SRV_Channels.set_aux_channel_default.body fp function channel
  PMem.leave fp
  return r

/-- C++ `SRV_Channels::enable_aux_servos : void ()`, `SRV_Channel_aux.cpp:250-288`. -/
def SRV_Channels.enable_aux_servos (this : UInt64) : PMem.M Unit := do
  let t'1 ← PMem.ldU64 ((0xba88 : UInt64) /- &hal -/ + 72)
  let t'2 ← PMem.ldU64 (0xbc40 : UInt64) /- &SRV_Channels::_singleton -/
  let t'3 ← AP_ParamT'unsigned_short_2.operator_const_unsigned_short__ (t'2 + 646)
  let t'4 ← PMem.ldU16 t'3
  discard <| PMem.halDev "AP_HAL::RCOutput::set_default_rate" t'1 #[(UInt16.toUInt64 (t'4))]
  SRV_Channels.update_aux_servo_function
  for i'5 in [0:32] do
    let i : UInt8 := UInt8.ofNat i'5
    let t'6 ← PMem.ldU64 (0xbc48 : UInt64) /- &SRV_Channels::channels -/
    let c : UInt64 := (t'6 + ((UInt64.toInt64 (UInt8.toUInt64 (i))) * 20).toUInt64)
    let t'7 ← SRV_Channel.valid_function c
    let mut sc'10 := t'7
    if sc'10 then
      let t'8 ← PMem.ldU32 (0xe530 : UInt64) /- &SRV_Channels::disabled_mask -/
      let t'9 ← PMem.ldU8 (c + 13)
      sc'10 := !((t'8 &&& ((1 : UInt32) <<< (Int32.toUInt32 ((UInt32.toInt32 (UInt8.toUInt32 (t'9))))))) != (0 : UInt32))
    if sc'10 then
      let t'11 ← PMem.ldU64 ((0xba88 : UInt64) /- &hal -/ + 72)
      let t'12 ← PMem.ldU8 (c + 13)
      discard <| PMem.halDev "AP_HAL::RCOutput::enable_ch" t'11 #[(UInt8.toUInt64 (t'12))]
    else
      let t'13 ← PMem.ldU64 ((0xba88 : UInt64) /- &hal -/ + 72)
      let t'14 ← PMem.ldU8 (c + 13)
      discard <| PMem.halDev "AP_HAL::RCOutput::disable_ch" t'13 #[(UInt8.toUInt64 (t'14))]
    let t'15 ← AP_Enum16'SRV_Channel_Function.operator_const_SRV_Channel.Function (c + 8)
    if (t'15 == (134 : Int32)) then
      let t'16 ← AP_ParamT'short_2.operator_const_short__ c
      let t'17 ← PMem.ldI16 t'16
      SRV_Channel.set_output_pwm c (Int16.toUInt16 (t'17)) false
      SRV_Channel.output_ch c
    else
      let t'18 ← AP_Enum16'SRV_Channel_Function.operator_const_SRV_Channel.Function (c + 8)
      if (t'18 == (135 : Int32)) then
        let t'19 ← AP_ParamT'short_2.operator_const_short__ (c + 4)
        let t'20 ← PMem.ldI16 t'19
        SRV_Channel.set_output_pwm c (Int16.toUInt16 (t'20)) false
        SRV_Channel.output_ch c
      else
        let t'21 ← AP_Enum16'SRV_Channel_Function.operator_const_SRV_Channel.Function (c + 8)
        if (t'21 == (136 : Int32)) then
          let t'22 ← AP_ParamT'short_2.operator_const_short__ (c + 2)
          let t'23 ← PMem.ldI16 t'22
          SRV_Channel.set_output_pwm c (Int16.toUInt16 (t'23)) false
          SRV_Channel.output_ch c
  let t'24 ← PMem.ldU64 ((0xba88 : UInt64) /- &hal -/ + 72)
  discard <| PMem.halDev "AP_HAL::RCOutput::update_channel_masks" t'24 #[]
  return ()

/-- C++ `SRV_Channels::have_digital_outputs : bool (uint32_t)`, `SRV_Channel_config.h:593-?`. -/
def SRV_Channels.have_digital_outputs (mask : UInt32) : PMem.M Bool := do
  let mut mask := mask
  let mut sc'2 := (mask != (Int32.toUInt32 ((0 : Int32))))
  if sc'2 then
    let t'1 ← PMem.ldU32 (0xeda8 : UInt64) /- &SRV_Channels::digital_mask -/
    sc'2 := ((mask &&& t'1) == mask)
  return sc'2

/-- C++ `SRV_Channels::enable_by_mask : void (uint32_t)`, `SRV_Channel_aux.cpp:340-347`. -/
def SRV_Channels.enable_by_mask (mask : UInt32) : PMem.M Unit := do
  let mut mask := mask
  for i'1 in [0:32] do
    let i : UInt8 := UInt8.ofNat i'1
    if (mask &&& ((1 : UInt32) <<< (Int32.toUInt32 ((UInt32.toInt32 (UInt8.toUInt32 (i))))))) != (0 : UInt32) then
      let t'2 ← PMem.ldU64 ((0xba88 : UInt64) /- &hal -/ + 72)
      discard <| PMem.halDev "AP_HAL::RCOutput::enable_ch" t'2 #[(UInt8.toUInt64 (i))]
  return ()

/-- C++ `SRV_Channels::cork : void ()`, `SRV_Channels.cpp:478-481`. -/
def SRV_Channels.cork (this : UInt64) : PMem.M Unit := do
  let t'1 ← PMem.ldU64 ((0xba88 : UInt64) /- &hal -/ + 72)
  discard <| PMem.halDev "AP_HAL::RCOutput::cork" t'1 #[]
  return ()

/-- C++ `SRV_Channels::push : void ()`, `SRV_Channels.cpp:486-549`. -/
def SRV_Channels.push (this : UInt64) : PMem.M Unit := do
  let t'1 ← PMem.ldU64 ((0xba88 : UInt64) /- &hal -/ + 72)
  discard <| PMem.halDev "AP_HAL::RCOutput::push" t'1 #[]
  return ()

/-- C++ `SRV_Channels::init : void (uint32_t, AP_HAL::RCOutput::output_mode)`, `SRV_Channels.cpp:365-374`. -/
def SRV_Channels.init (this : UInt64) (motor_mask : UInt32) (mode : UInt32) : PMem.M Unit := do
  let mut motor_mask := motor_mask
  let mut mode := mode
  let t'1 ← PMem.ldU64 ((0xba88 : UInt64) /- &hal -/ + 72)
  let t'2 ← PMem.ldU64 (0xbc40 : UInt64) /- &SRV_Channels::_singleton -/
  let t'3 ← AP_ParamT'signed_char_1.operator_const_signed_char__ (t'2 + 648)
  let t'4 ← PMem.ldI8 t'3
  let t'5 ← AP.scheduler
  let t'6 ← AP_Scheduler.get_loop_rate_hz t'5
  discard <| PMem.halDev "AP_HAL::RCOutput::set_dshot_rate" t'1 #[(UInt8.toUInt64 ((Int8.toUInt8 (t'4)))), (UInt16.toUInt64 (t'6))]
  return ()

/-- C++ `SRV_Channel::set_override : void (bool)`, `SRV_Channel.h:383-?`. -/
def SRV_Channel.set_override (this : UInt64) (b : Bool) : PMem.M Unit := do
  let mut b := b
  PMem.stB (this + 19) b
  return ()

/-- C++ `SRV_Channel::pwm_from_scaled_value : uint16_t (float) const`, `SRV_Channel.cpp:215-222`. -/
def SRV_Channel.pwm_from_scaled_value (this : UInt64) (scaled_value : Binary32) : PMem.M UInt16 := do
  let mut scaled_value := scaled_value
  let t'1 ← PMem.ldBits this 96 1
  if (t'1 != 0) then
    let t'2 ← SRV_Channel.pwm_from_angle this scaled_value
    return t'2
  else
    let t'3 ← SRV_Channel.pwm_from_range this scaled_value
    return t'3

/-- C++ `SRV_Channel::calc_pwm : void (float)`, `SRV_Channel.cpp:224-245`. -/
def SRV_Channel.calc_pwm (this : UInt64) (output_scaled : Binary32) : PMem.M Unit := do
  let mut output_scaled := output_scaled
  let t'1 ← PMem.ldU32 (0xbf68 : UInt64) /- &SRV_Channel::have_pwm_mask -/
  let t'2 ← PMem.ldU8 (this + 13)
  if (t'1 &&& ((1 : UInt32) <<< (Int32.toUInt32 ((UInt32.toInt32 (UInt8.toUInt32 (t'2))))))) != (0 : UInt32) then
    return ()
  let mut force : Bool := false
  let t'3 ← SRV_Channel.get_function this
  let t'4 ← SRV_Channel.should_e_stop t'3
  let mut sc'6 := t'4
  if sc'6 then
    let t'5 ← PMem.ldB (0x130c0 : UInt64) /- &SRV_Channels::emergency_stop -/
    sc'6 := t'5
  if sc'6 then
    let t'7 := Binary64.toBinary32 ((Binary64.ofBits 0x0000000000000000 /- 0 -/))
    output_scaled := t'7
    force := true
  let mut sc'9 := !force
  if sc'9 then
    let t'8 ← PMem.ldB (this + 19)
    sc'9 := t'8
  if sc'9 then
    return ()
  let t'10 ← SRV_Channel.pwm_from_scaled_value this output_scaled
  PMem.stU16 (this + 10) t'10
  return ()

/-- C++ `SRV_Channels::calc_pwm : void ()`, `SRV_Channels.cpp:401-427`. -/
def SRV_Channels.calc_pwm  : PMem.M Unit := do
  let t'1 ← PMem.ldU64 (0x135f0 : UInt64) /- &SRV_Channels::_slew -/
  let mut slew : UInt64 := t'1
  let mut first'2 := true
  for _ in PMem.loopFuel do
    if !first'2 then
      let t'3 ← PMem.ldU64 (slew + 16)
      slew := t'3
      pure ()
    first'2 := false
    if !((slew != 0)) then break
    let t'4 ← PMem.ldF32 (slew + 8)
    let t'5 ← is_positive'float t'4
    if t'5 then
      let t'6 ← PMem.ldI32 slew
      let t'7 ← PMem.ldF32 (((0xe550 : UInt64) /- &SRV_Channels::functions -/ + ((Int32.toInt64 (t'6)) * 8).toUInt64) + 4)
      let t'8 ← PMem.ldF32 (slew + 4)
      let t'9 ← PMem.ldF32 (slew + 8)
      let t'10 ← PMem.ldF32 (slew + 4)
      let t'11 ← PMem.ldF32 (slew + 8)
      let t'12 ← constrain_value_line'float t'7 (t'8 - t'9) (t'10 + t'11) (Int32.toUInt32 ((407 : Int32)))
      let t'13 ← PMem.ldI32 slew
      PMem.stF32 (((0xe550 : UInt64) /- &SRV_Channels::functions -/ + ((Int32.toInt64 (t'13)) * 8).toUInt64) + 4) t'12
    let t'14 ← PMem.ldI32 slew
    let t'15 ← PMem.ldF32 (((0xe550 : UInt64) /- &SRV_Channels::functions -/ + ((Int32.toInt64 (t'14)) * 8).toUInt64) + 4)
    PMem.stF32 (slew + 4) t'15
  for i'16 in [0:32] do
    let i : UInt8 := UInt8.ofNat i'16
    let t'17 ← PMem.ldU16 ((0x135f8 : UInt64) /- &SRV_Channels::override_counter -/ + ((UInt64.toInt64 (UInt8.toUInt64 (i))) * 2).toUInt64)
    if ((UInt32.toInt32 (UInt16.toUInt32 (t'17))) == (0 : Int32)) then
      let t'18 ← PMem.ldU64 (0xbc48 : UInt64) /- &SRV_Channels::channels -/
      SRV_Channel.set_override (t'18 + ((UInt64.toInt64 (UInt8.toUInt64 (i))) * 20).toUInt64) false
    else
      let t'19 ← PMem.ldU64 (0xbc48 : UInt64) /- &SRV_Channels::channels -/
      SRV_Channel.set_override (t'19 + ((UInt64.toInt64 (UInt8.toUInt64 (i))) * 20).toUInt64) true
      let t'20 := ((0x135f8 : UInt64) /- &SRV_Channels::override_counter -/ + ((UInt64.toInt64 (UInt8.toUInt64 (i))) * 2).toUInt64)
      let t'21 ← PMem.ldU16 t'20
      let t'22 := (t'21 - 1)
      PMem.stU16 t'20 t'22
    let t'23 ← PMem.ldU64 (0xbc48 : UInt64) /- &SRV_Channels::channels -/
    let t'24 ← SRV_Channel.valid_function (t'23 + ((UInt64.toInt64 (UInt8.toUInt64 (i))) * 20).toUInt64)
    if t'24 then
      let t'25 ← PMem.ldU64 (0xbc48 : UInt64) /- &SRV_Channels::channels -/
      let t'26 ← AP_ParamTBase'short_2.get ((t'25 + ((UInt64.toInt64 (UInt8.toUInt64 (i))) * 20).toUInt64) + 8)
      let t'27 ← PMem.ldI16 t'26
      let t'28 ← PMem.ldF32 (((0xe550 : UInt64) /- &SRV_Channels::functions -/ + ((Int16.toInt64 (t'27)) * 8).toUInt64) + 4)
      let t'29 ← PMem.ldU64 (0xbc48 : UInt64) /- &SRV_Channels::channels -/
      SRV_Channel.calc_pwm (t'29 + ((UInt64.toInt64 (UInt8.toUInt64 (i))) * 20).toUInt64) t'28
  return ()

/-- C++ `SRV_Channels::output_ch_all : void ()`, `SRV_Channel_aux.cpp:107-118`. -/
def SRV_Channels.output_ch_all  : PMem.M Unit := do
  let mut max_chan : UInt8 := Int8.toUInt8 (Int32.toInt8 ((32 : Int32)))
  let t'1 ← PMem.ldU64 (0xbc40 : UInt64) /- &SRV_Channels::_singleton -/
  let mut sc'5 := (t'1 != (0 : UInt64))
  if sc'5 then
    let t'2 ← PMem.ldU64 (0xbc40 : UInt64) /- &SRV_Channels::_singleton -/
    let t'3 ← AP_ParamTBase'signed_char_1.get (t'2 + 660)
    let t'4 ← PMem.ldI8 t'3
    sc'5 := (decide ((Int8.toInt32 (t'4)) ≤ (0 : Int32)))
  if sc'5 then
    let t'6 := Int8.toUInt8 (Int32.toInt8 ((16 : Int32)))
    max_chan := t'6
  for i'7 in [0:max_chan.toNat] do
    let i : UInt8 := UInt8.ofNat i'7
    let t'8 ← PMem.ldU64 (0xbc48 : UInt64) /- &SRV_Channels::channels -/
    SRV_Channel.output_ch (t'8 + ((UInt64.toInt64 (UInt8.toUInt64 (i))) * 20).toUInt64)
  return ()

end Vehicle_lib
