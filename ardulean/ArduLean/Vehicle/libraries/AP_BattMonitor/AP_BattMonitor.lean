import ArduLean.Runtime.Hal
import ArduLean.Vehicle.libraries.AP_Math.AP_Math
import ArduLean.Vehicle.libraries.AP_HAL.AP_HAL
import ArduLean.Vehicle.libraries.AP_Param.AP_Param

/-!
ArduPilot `libraries/AP_BattMonitor`, part 1 of 2. Sources: `libraries/AP_BattMonitor/AP_BattMonitor.cpp`, `libraries/AP_BattMonitor/AP_BattMonitor_Backend.cpp`, `libraries/AP_BattMonitor/AP_BattMonitor_Analog.cpp`, `libraries/AP_BattMonitor/AP_BattMonitor_Params.cpp`, `libraries/AP_BattMonitor/AP_BattMonitor_Backend.h`, `libraries/AP_BattMonitor/AP_BattMonitor_Analog.h`, `libraries/AP_BattMonitor/AP_BattMonitor.h`.

Items of `lean/Vehicle_lib.lean` (the vehicle translation), unchanged; placed by `tools/split_modules.py` (`ArduLean/Vehicle/INDEX.md`).
-/

open FloatLib.Floats (Binary32 Binary64)

set_option linter.unusedVariables false
set_option linter.unreachableTactic false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false

namespace Vehicle_lib

/-- C++ `AP_BattMonitor::voltage : float (uint8_t) const`, `AP_BattMonitor.cpp:830-837`. -/
def AP_BattMonitor.voltage (this : UInt64) (instance' : UInt8) : PMem.M Binary32 := do
  let mut instance' := instance'
  let t'1 ← PMem.ldU8 (this + 1492)
  if (decide ((UInt32.toInt32 (UInt8.toUInt32 (instance'))) < (UInt32.toInt32 (UInt8.toUInt32 (t'1))))) then
    let t'2 ← PMem.ldF32 (((this + 408) + ((UInt64.toInt64 (UInt8.toUInt64 (instance'))) * 112).toUInt64) + 28)
    return t'2
  else
    return (Binary32.ofBits 0x00000000 /- 0 -/)

/-- C++ `AP_BattMonitor::get_singleton : AP_BattMonitor *()`, `AP_Common.h:103-105`. -/
def AP_BattMonitor.get_singleton  : PMem.M UInt64 := do
  let t'1 ← PMem.ldU64 (0x13188 : UInt64) /- &AP_BattMonitor::_singleton -/
  return t'1

/-- C++ `AP::battery : AP_BattMonitor &()`, `AP_BattMonitor.cpp:1305-1308`. -/
def AP.battery  : PMem.M UInt64 := do
  let t'1 ← AP_BattMonitor.get_singleton
  return t'1

/-- C++ `AP_BattMonitor_Backend::voltage_resting_estimate : float () const`, `AP_BattMonitor_Backend.cpp:146-150`. -/
def AP_BattMonitor_Backend.voltage_resting_estimate (this : UInt64) : PMem.M Binary32 := do
  let t'1 ← PMem.ldU64 (this + 16)
  let t'2 ← PMem.ldU64 (this + 16)
  let t'3 ← MAX'float_float (t'1 + 28) (t'2 + 64)
  let t'4 ← PMem.ldF32 t'3
  return t'4

/-- C++ `AP_BattMonitor::voltage_resting_estimate : float (uint8_t) const`, `AP_BattMonitor.cpp:841-848`. -/
def AP_BattMonitor.voltage_resting_estimate (this : UInt64) (instance' : UInt8) : PMem.M Binary32 := do
  let mut instance' := instance'
  let t'1 ← PMem.ldU8 (this + 1492)
  let mut sc'3 := (decide ((UInt32.toInt32 (UInt8.toUInt32 (instance'))) < (UInt32.toInt32 (UInt8.toUInt32 (t'1)))))
  if sc'3 then
    let t'2 ← PMem.ldU64 ((this + 1416) + ((UInt64.toInt64 (UInt8.toUInt64 (instance'))) * 8).toUInt64)
    sc'3 := (t'2 != (0 : UInt64))
  if sc'3 then
    let t'4 ← PMem.ldU64 ((this + 1416) + ((UInt64.toInt64 (UInt8.toUInt64 (instance'))) * 8).toUInt64)
    let t'5 ← AP_BattMonitor_Backend.voltage_resting_estimate t'4
    return t'5
  else
    return (Binary32.ofBits 0x00000000 /- 0 -/)

/-- C++ `AP_BattMonitor_Analog::has_current : bool () const`, `AP_BattMonitor_Analog.cpp:186-191`. -/
def AP_BattMonitor_Analog.has_current (this : UInt64) : PMem.M Bool := do
  let t'1 ← PMem.ldU64 (this + 64)
  let mut sc'7 := (t'1 != (0 : UInt64))
  if sc'7 then
    let t'2 ← PMem.ldU64 (this + 16)
    let t'3 ← PMem.ldI32 (t'2 + 96)
    let mut sc'6 := (t'3 == (4 : Int32))
    if !sc'6 then
      let t'4 ← PMem.ldU64 (this + 16)
      let t'5 ← PMem.ldI32 (t'4 + 96)
      sc'6 := (t'5 == (31 : Int32))
    sc'7 := sc'6
  return sc'7

/-- C++ `AP_BattMonitor::current_amps : bool (float &, uint8_t) const`, `AP_BattMonitor.cpp:871-878`. -/
def AP_BattMonitor.current_amps (this : UInt64) (current : UInt64) (instance' : UInt8) : PMem.M Bool := do
  let mut instance' := instance'
  let t'1 ← PMem.ldU8 (this + 1492)
  let mut sc'3 := (decide ((UInt32.toInt32 (UInt8.toUInt32 (instance'))) < (UInt32.toInt32 (UInt8.toUInt32 (t'1)))))
  if sc'3 then
    let t'2 ← PMem.ldU64 ((this + 1416) + ((UInt64.toInt64 (UInt8.toUInt64 (instance'))) * 8).toUInt64)
    sc'3 := (t'2 != (0 : UInt64))
  let mut sc'6 := sc'3
  if sc'6 then
    let t'4 ← PMem.ldU64 ((this + 1416) + ((UInt64.toInt64 (UInt8.toUInt64 (instance'))) * 8).toUInt64)
    let t'5 ← AP_BattMonitor_Analog.has_current t'4
    sc'6 := t'5
  if sc'6 then
    let t'7 ← PMem.ldF32 (((this + 408) + ((UInt64.toInt64 (UInt8.toUInt64 (instance'))) * 112).toUInt64) + 32)
    PMem.stF32 current t'7
    return true
  else
    return false

/-- C++ `AP_BattMonitor::get_resistance : float (uint8_t) const`, `AP_Common.h:256-?`. -/
def AP_BattMonitor.get_resistance (this : UInt64) (instance' : UInt8) : PMem.M Binary32 := do
  let mut instance' := instance'
  let t'1 ← PMem.ldF32 (((this + 408) + ((UInt64.toInt64 (UInt8.toUInt64 (instance'))) * 112).toUInt64) + 68)
  return t'1

/-- C++ `AP_BattMonitor::configured_type : Type (uint8_t) const`, `AP_Common.h:202-204`. -/
def AP_BattMonitor.configured_type (this : UInt64) (instance' : UInt8) : PMem.M Int32 := do
  let mut instance' := instance'
  let t'1 ← AP_ParamTBase'signed_char_1.get (((this + 8) + ((UInt64.toInt64 (UInt8.toUInt64 (instance'))) * 44).toUInt64) + 38)
  let t'2 ← PMem.ldI8 t'1
  return Int8.toInt32 (t'2)

/-- C++ `AP_BattMonitor::allocated_type : Type (uint8_t) const`, `AP_Common.h:206-208`. -/
def AP_BattMonitor.allocated_type (this : UInt64) (instance' : UInt8) : PMem.M Int32 := do
  let mut instance' := instance'
  let t'1 ← PMem.ldI32 (((this + 408) + ((UInt64.toInt64 (UInt8.toUInt64 (instance'))) * 112).toUInt64) + 96)
  return t'1

/-- C++ `AP_BattMonitor_Params::failsafe_voltage_source : BattMonitor_LowVoltage_Source () const`, `AP_Common.h:68-?`. -/
def AP_BattMonitor_Params.failsafe_voltage_source (this : UInt64) : PMem.M UInt32 := do
  let t'1 ← AP_ParamTBase'signed_char_1.get (this + 40)
  let t'2 ← PMem.ldI8 t'1
  return Int32.toUInt32 (Int8.toInt32 (t'2))

/-- C++ `AP_BattMonitor_Backend::check_failsafe_types : void (bool &, bool &, bool &, bool &) const`, `AP_BattMonitor_Backend.cpp:240-282`. -/
def AP_BattMonitor_Backend.check_failsafe_types (this : UInt64) (low_voltage : UInt64) (low_capacity : UInt64) (critical_voltage : UInt64) (critical_capacity : UInt64) : PMem.M Unit := do
  let mut voltage_used : Binary32 := default  -- uninitialized in C
  let t'1 ← PMem.ldU64 (this + 24)
  let t'2 ← AP_BattMonitor_Params.failsafe_voltage_source t'1
  let sw'3 := UInt32.toInt32 (t'2)
  if sw'3 == (0 : Int32) then
    let t'4 ← PMem.ldU64 (this + 16)
    let t'5 ← PMem.ldF32 (t'4 + 28)
    voltage_used := t'5
  else if sw'3 == (1 : Int32) then
    let t'6 ← AP_BattMonitor_Backend.voltage_resting_estimate this
    voltage_used := t'6
  else
    let t'7 ← PMem.ldU64 (this + 16)
    let t'8 ← PMem.ldF32 (t'7 + 28)
    voltage_used := t'8
  let mut sc'12 := (decide (voltage_used > (Int32.toBinary32 ((0 : Int32)))))
  if sc'12 then
    let t'9 ← PMem.ldU64 (this + 24)
    let t'10 ← AP_ParamT'float_4.operator_const_float__'1 (t'9 + 16)
    let t'11 ← PMem.ldF32 t'10
    sc'12 := (decide (t'11 > (Int32.toBinary32 ((0 : Int32)))))
  let mut sc'16 := sc'12
  if sc'16 then
    let t'13 ← PMem.ldU64 (this + 24)
    let t'14 ← AP_ParamT'float_4.operator_const_float__'1 (t'13 + 16)
    let t'15 ← PMem.ldF32 t'14
    sc'16 := (decide (voltage_used < t'15))
  if sc'16 then
    PMem.stB critical_voltage true
  else
    PMem.stB critical_voltage false
  let t'17 ← AP_BattMonitor_Analog.has_current this
  let mut sc'21 := t'17
  if sc'21 then
    let t'18 ← PMem.ldU64 (this + 24)
    let t'19 ← AP_ParamT'float_4.operator_const_float__'1 (t'18 + 20)
    let t'20 ← PMem.ldF32 t'19
    sc'21 := (decide (t'20 > (Int32.toBinary32 ((0 : Int32)))))
  let mut sc'30 := sc'21
  if sc'30 then
    let t'22 ← PMem.ldU64 (this + 24)
    let t'23 ← AP_ParamT'int_3.operator_const_int__ t'22
    let t'24 ← PMem.ldI32 t'23
    let t'25 ← PMem.ldU64 (this + 16)
    let t'26 ← PMem.ldF32 (t'25 + 36)
    let t'27 ← PMem.ldU64 (this + 24)
    let t'28 ← AP_ParamT'float_4.operator_const_float__'1 (t'27 + 20)
    let t'29 ← PMem.ldF32 t'28
    sc'30 := (decide (((Int32.toBinary32 (t'24)) - t'26) < t'29))
  if sc'30 then
    PMem.stB critical_capacity true
  else
    PMem.stB critical_capacity false
  let mut sc'34 := (decide (voltage_used > (Int32.toBinary32 ((0 : Int32)))))
  if sc'34 then
    let t'31 ← PMem.ldU64 (this + 24)
    let t'32 ← AP_ParamT'float_4.operator_const_float__'1 (t'31 + 8)
    let t'33 ← PMem.ldF32 t'32
    sc'34 := (decide (t'33 > (Int32.toBinary32 ((0 : Int32)))))
  let mut sc'38 := sc'34
  if sc'38 then
    let t'35 ← PMem.ldU64 (this + 24)
    let t'36 ← AP_ParamT'float_4.operator_const_float__'1 (t'35 + 8)
    let t'37 ← PMem.ldF32 t'36
    sc'38 := (decide (voltage_used < t'37))
  if sc'38 then
    PMem.stB low_voltage true
  else
    PMem.stB low_voltage false
  let t'39 ← AP_BattMonitor_Analog.has_current this
  let mut sc'43 := t'39
  if sc'43 then
    let t'40 ← PMem.ldU64 (this + 24)
    let t'41 ← AP_ParamT'float_4.operator_const_float__'1 (t'40 + 12)
    let t'42 ← PMem.ldF32 t'41
    sc'43 := (decide (t'42 > (Int32.toBinary32 ((0 : Int32)))))
  let mut sc'52 := sc'43
  if sc'52 then
    let t'44 ← PMem.ldU64 (this + 24)
    let t'45 ← AP_ParamT'int_3.operator_const_int__ t'44
    let t'46 ← PMem.ldI32 t'45
    let t'47 ← PMem.ldU64 (this + 16)
    let t'48 ← PMem.ldF32 (t'47 + 36)
    let t'49 ← PMem.ldU64 (this + 24)
    let t'50 ← AP_ParamT'float_4.operator_const_float__'1 (t'49 + 12)
    let t'51 ← PMem.ldF32 t'50
    sc'52 := (decide (((Int32.toBinary32 (t'46)) - t'48) < t'51))
  if sc'52 then
    PMem.stB low_capacity true
  else
    PMem.stB low_capacity false
  return ()

/-- C++ `update_check : bool (size_t, char *, bool, const char *)`, `AP_BattMonitor_Backend.cpp:202-209`. -/
def update_check (buflen : UInt64) (buffer : UInt64) (failed : Bool) (message : UInt64) : PMem.M Bool := do
  let mut buflen := buflen
  let mut buffer := buffer
  let mut failed := failed
  let mut message := message
  if failed then
    let t'1 ← PMem.strncpy buffer message buflen
    discard <| pure (t'1)
    return false
  return true

/-- C++ `AP_BattMonitor::has_failsafed : bool () const`, `AP_Common.h:196-?`. -/
def AP_BattMonitor.has_failsafed (this : UInt64) : PMem.M Bool := do
  let t'1 ← PMem.ldB (this + 1521)
  return t'1

/-- `AP_BattMonitor_Backend.set_powered_state` as a pure function of its arguments (it reads and writes no memory). -/
def AP_BattMonitor_Backend.set_powered_state.pure' (this : UInt64) (power_on : Bool) : Id Unit := do
  let mut power_on := power_on
  return ()

/-- C++ `AP_BattMonitor_Backend::set_powered_state : void (bool)`, `AP_Common.h:93-?`. -/
def AP_BattMonitor_Backend.set_powered_state (this : UInt64) (power_on : Bool) : PMem.M Unit :=
  pure (_root_.Vehicle_lib.AP_BattMonitor_Backend.set_powered_state.pure' this power_on)

/-- C++ `AP_BattMonitor::set_powered_state : void (const uint8_t, const bool)`, `AP_BattMonitor.cpp:1250-1255`. -/
def AP_BattMonitor.set_powered_state (this : UInt64) (instance' : UInt8) (power_on : Bool) : PMem.M Unit := do
  let mut instance' := instance'
  let mut power_on := power_on
  let t'1 ← PMem.ldU8 (this + 1492)
  let mut sc'3 := (decide ((UInt32.toInt32 (UInt8.toUInt32 (instance'))) < (UInt32.toInt32 (UInt8.toUInt32 (t'1)))))
  if sc'3 then
    let t'2 ← PMem.ldU64 ((this + 1416) + ((UInt64.toInt64 (UInt8.toUInt64 (instance'))) * 8).toUInt64)
    sc'3 := (t'2 != (0 : UInt64))
  if sc'3 then
    let t'4 ← PMem.ldU64 ((this + 1416) + ((UInt64.toInt64 (UInt8.toUInt64 (instance'))) * 8).toUInt64)
    AP_BattMonitor_Backend.set_powered_state t'4 power_on
  return ()

/-- C++ `AP_BattMonitor::set_powered_state_to_all : void (const bool)`, `AP_BattMonitor.cpp:1240-1245`. -/
def AP_BattMonitor.set_powered_state_to_all (this : UInt64) (power_on : Bool) : PMem.M Unit := do
  let mut power_on := power_on
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
    AP_BattMonitor.set_powered_state this i power_on
  return ()

/-- C++ `AP_BattMonitor_Backend::option_is_set : bool (const AP_BattMonitor_Params::Options) const`, `definitions.h:103-105`. -/
def AP_BattMonitor_Backend.option_is_set (this : UInt64) (option : UInt16) : PMem.M Bool := do
  let mut option := option
  let t'1 ← PMem.ldU64 (this + 24)
  let t'2 ← AP_ParamT'unsigned_int_3.operator_const_unsigned_int__ (t'1 + 32)
  let t'3 ← PMem.ldU32 t'2
  return ((t'3 &&& (UInt16.toUInt32 (option))) != (Int32.toUInt32 ((0 : Int32))))

/-- C++ `AP_BattMonitor::option_is_set : bool (uint8_t, AP_BattMonitor_Params::Options) const`, `AP_BattMonitor.cpp:862-868`. -/
def AP_BattMonitor.option_is_set (this : UInt64) (instance' : UInt8) (option : UInt16) : PMem.M Bool := do
  let mut instance' := instance'
  let mut option := option
  let t'1 ← PMem.ldU8 (this + 1492)
  let mut sc'3 := (decide ((UInt32.toInt32 (UInt8.toUInt32 (instance'))) ≥ (UInt32.toInt32 (UInt8.toUInt32 (t'1)))))
  if !sc'3 then
    let t'2 ← PMem.ldU64 ((this + 1416) + ((UInt64.toInt64 (UInt8.toUInt64 (instance'))) * 8).toUInt64)
    sc'3 := (t'2 == (0 : UInt64))
  if sc'3 then
    return false
  let t'4 ← PMem.ldU64 ((this + 1416) + ((UInt64.toInt64 (UInt8.toUInt64 (instance'))) * 8).toUInt64)
  let t'5 ← AP_BattMonitor_Backend.option_is_set t'4 option
  return t'5

/-- C++ `AP_BattMonitor_Backend::capacity_remaining_pct : bool (uint8_t &) const`, `AP_BattMonitor_Backend.cpp:65-83`. -/
def AP_BattMonitor_Backend.capacity_remaining_pct (this : UInt64) (percentage : UInt64) : PMem.M Bool := do
  let t'1 ← PMem.ldU64 (this + 24)
  let t'2 ← AP_ParamT'int_3.operator_const_int__ t'1
  let t'3 ← PMem.ldI32 t'2
  if (decide (t'3 ≤ (10 : Int32))) then
    return false
  let t'4 ← AP_BattMonitor_Analog.has_current this
  let mut sc'7 := !t'4
  if !sc'7 then
    let t'5 ← PMem.ldU64 (this + 16)
    let t'6 ← PMem.ldB (t'5 + 73)
    sc'7 := !t'6
  if sc'7 then
    return false
  let t'8 ← PMem.ldU64 (this + 16)
  let t'9 ← PMem.ldF32 (t'8 + 36)
  let mut sc'13 := (Binary32.isNaN t'9)
  if !sc'13 then
    let t'10 ← PMem.ldU64 (this + 24)
    let t'11 ← AP_ParamT'int_3.operator_const_int__ t'10
    let t'12 ← PMem.ldI32 t'11
    sc'13 := (decide (t'12 ≤ (0 : Int32)))
  if sc'13 then
    return false
  let t'14 ← PMem.ldU64 (this + 24)
  let t'15 ← AP_ParamT'int_3.operator_const_int__ t'14
  let t'16 ← PMem.ldI32 t'15
  let t'17 ← PMem.ldU64 (this + 16)
  let t'18 ← PMem.ldF32 (t'17 + 36)
  let mut mah_remaining : Binary32 := ((Int32.toBinary32 (t'16)) - t'18)
  let t'19 ← PMem.ldU64 (this + 24)
  let t'20 ← AP_ParamT'int_3.operator_const_int__ t'19
  let t'21 ← PMem.ldI32 t'20
  let t'22 ← constrain_value_line'float (((Int32.toBinary32 ((100 : Int32))) * mah_remaining) / (Int32.toBinary32 (t'21))) (Int32.toBinary32 ((0 : Int32))) (Int32.toBinary32 ((255 : Int32))) (Int32.toUInt32 ((81 : Int32)))
  let t'23 := Binary32.toUInt8 (t'22)
  PMem.stU8 percentage t'23
  return true

/-- C++ `AP_BattMonitor::capacity_remaining_pct : bool (uint8_t &, uint8_t) const`, `AP_BattMonitor.cpp:905-911`. -/
def AP_BattMonitor.capacity_remaining_pct (this : UInt64) (percentage : UInt64) (instance' : UInt8) : PMem.M Bool := do
  let mut instance' := instance'
  let t'1 ← PMem.ldU8 (this + 1492)
  let mut sc'3 := (decide ((UInt32.toInt32 (UInt8.toUInt32 (instance'))) < (UInt32.toInt32 (UInt8.toUInt32 (t'1)))))
  if sc'3 then
    let t'2 ← PMem.ldU64 ((this + 1416) + ((UInt64.toInt64 (UInt8.toUInt64 (instance'))) * 8).toUInt64)
    sc'3 := (t'2 != (0 : UInt64))
  if sc'3 then
    let t'4 ← PMem.ldU64 ((this + 1416) + ((UInt64.toInt64 (UInt8.toUInt64 (instance'))) * 8).toUInt64)
    let t'5 ← AP_BattMonitor_Backend.capacity_remaining_pct t'4 percentage
    return t'5
  return false

/-- `AP_BattMonitor_Backend.has_temperature` as a pure function of its arguments (it reads and writes no memory). -/
def AP_BattMonitor_Backend.has_temperature.pure' (this : UInt64) : Id Bool := do
  return false

/-- C++ `AP_BattMonitor_Backend::has_temperature : bool () const`, `AP_BattMonitor_Backend.h:54-?`. -/
def AP_BattMonitor_Backend.has_temperature (this : UInt64) : PMem.M Bool :=
  pure (_root_.Vehicle_lib.AP_BattMonitor_Backend.has_temperature.pure' this)

/-- C++ `AP_BattMonitor_Backend::get_temperature : bool (float &) const`, `AP_BattMonitor_Backend.cpp:320-332`. -/
def AP_BattMonitor_Backend.get_temperature (this : UInt64) (temperature : UInt64) : PMem.M Bool := do
  let t'1 ← PMem.ldU64 (this + 16)
  let t'2 ← PMem.ldF32 (t'1 + 56)
  PMem.stF32 temperature t'2
  let t'3 ← AP_BattMonitor_Backend.has_temperature this
  return t'3

/-- C++ `AP_BattMonitor::get_temperature : bool (float &, const uint8_t) const`, `AP_BattMonitor.cpp:1057-1064`. -/
def AP_BattMonitor.get_temperature (this : UInt64) (temperature : UInt64) (instance' : UInt8) : PMem.M Bool := do
  let mut instance' := instance'
  let t'1 ← PMem.ldU8 (this + 1492)
  let mut sc'3 := (decide ((UInt32.toInt32 (UInt8.toUInt32 (instance'))) ≥ (UInt32.toInt32 (UInt8.toUInt32 (t'1)))))
  if !sc'3 then
    let t'2 ← PMem.ldU64 ((this + 1416) + ((UInt64.toInt64 (UInt8.toUInt64 (instance'))) * 8).toUInt64)
    sc'3 := (t'2 == (0 : UInt64))
  if sc'3 then
    return false
  let t'4 ← PMem.ldU64 ((this + 1416) + ((UInt64.toInt64 (UInt8.toUInt64 (instance'))) * 8).toUInt64)
  let t'5 ← AP_BattMonitor_Backend.get_temperature t'4 temperature
  return t'5

/-- `AP_BattMonitor_Backend.has_cell_voltages` as a pure function of its arguments (it reads and writes no memory). -/
def AP_BattMonitor_Backend.has_cell_voltages.pure' (this : UInt64) : Id Bool := do
  return false

/-- C++ `AP_BattMonitor_Backend::has_cell_voltages : bool () const`, `AP_BattMonitor_Backend.h:51-?`. -/
def AP_BattMonitor_Backend.has_cell_voltages (this : UInt64) : PMem.M Bool :=
  pure (_root_.Vehicle_lib.AP_BattMonitor_Backend.has_cell_voltages.pure' this)

/-- C++ `AP_BattMonitor::has_cell_voltages : bool (const uint8_t) const`, `AP_BattMonitor.cpp:1020-1027`. -/
def AP_BattMonitor.has_cell_voltages (this : UInt64) (instance' : UInt8) : PMem.M Bool := do
  let mut instance' := instance'
  let t'1 ← PMem.ldU8 (this + 1492)
  let mut sc'3 := (decide ((UInt32.toInt32 (UInt8.toUInt32 (instance'))) < (UInt32.toInt32 (UInt8.toUInt32 (t'1)))))
  if sc'3 then
    let t'2 ← PMem.ldU64 ((this + 1416) + ((UInt64.toInt64 (UInt8.toUInt64 (instance'))) * 8).toUInt64)
    sc'3 := (t'2 != (0 : UInt64))
  if sc'3 then
    let t'4 ← PMem.ldU64 ((this + 1416) + ((UInt64.toInt64 (UInt8.toUInt64 (instance'))) * 8).toUInt64)
    let t'5 ← AP_BattMonitor_Backend.has_cell_voltages t'4
    return t'5
  return false

/-- `AP_BattMonitor.get_cell_voltages` as a pure function of its arguments (it reads and writes no memory). -/
def AP_BattMonitor.get_cell_voltages.pure' (this : UInt64) (instance' : UInt8) : Id UInt64 := do
  let mut instance' := instance'
  if (decide ((UInt32.toInt32 (UInt8.toUInt32 (instance'))) ≥ (9 : Int32))) then
    return ((this + 408) + ((Int32.toInt64 ((0 : Int32))) * 112).toUInt64)
  else
    return ((this + 408) + ((UInt64.toInt64 (UInt8.toUInt64 (instance'))) * 112).toUInt64)

/-- C++ `AP_BattMonitor::get_cell_voltages : const AP_BattMonitor::cells &(const uint8_t) const`, `AP_BattMonitor.cpp:1030-1037`. -/
def AP_BattMonitor.get_cell_voltages (this : UInt64) (instance' : UInt8) : PMem.M UInt64 :=
  pure (_root_.Vehicle_lib.AP_BattMonitor.get_cell_voltages.pure' this instance')

/-- C++ `AP_BattMonitor::gcs_voltage : float (uint8_t) const`, `AP_BattMonitor.cpp:851-860`. -/
def AP_BattMonitor.gcs_voltage'2 (this : UInt64) (instance' : UInt8) : PMem.M Binary32 := do
  let mut instance' := instance'
  let t'1 ← PMem.ldU8 (this + 1492)
  let mut sc'3 := (decide ((UInt32.toInt32 (UInt8.toUInt32 (instance'))) ≥ (UInt32.toInt32 (UInt8.toUInt32 (t'1)))))
  if !sc'3 then
    let t'2 ← PMem.ldU64 ((this + 1416) + ((UInt64.toInt64 (UInt8.toUInt64 (instance'))) * 8).toUInt64)
    sc'3 := (t'2 == (0 : UInt64))
  if sc'3 then
    return (Binary32.ofBits 0x00000000 /- 0 -/)
  let t'4 ← PMem.ldU64 ((this + 1416) + ((UInt64.toInt64 (UInt8.toUInt64 (instance'))) * 8).toUInt64)
  let t'5 ← AP_BattMonitor_Backend.option_is_set t'4 (64 : UInt16)
  if t'5 then
    let t'6 ← AP_BattMonitor.voltage_resting_estimate this instance'
    return t'6
  let t'7 ← PMem.ldF32 (((this + 408) + ((UInt64.toInt64 (UInt8.toUInt64 (instance'))) * 112).toUInt64) + 28)
  return t'7

/-- C++ `AP_BattMonitor::consumed_mah : bool (float &, const uint8_t) const`, `AP_BattMonitor.cpp:881-892`. -/
def AP_BattMonitor.consumed_mah (this : UInt64) (mah : UInt64) (instance' : UInt8) : PMem.M Bool := do
  let mut instance' := instance'
  let t'1 ← PMem.ldU8 (this + 1492)
  let mut sc'3 := (decide ((UInt32.toInt32 (UInt8.toUInt32 (instance'))) < (UInt32.toInt32 (UInt8.toUInt32 (t'1)))))
  if sc'3 then
    let t'2 ← PMem.ldU64 ((this + 1416) + ((UInt64.toInt64 (UInt8.toUInt64 (instance'))) * 8).toUInt64)
    sc'3 := (t'2 != (0 : UInt64))
  let mut sc'6 := sc'3
  if sc'6 then
    let t'4 ← PMem.ldU64 ((this + 1416) + ((UInt64.toInt64 (UInt8.toUInt64 (instance'))) * 8).toUInt64)
    let t'5 ← AP_BattMonitor_Analog.has_current t'4
    sc'6 := t'5
  if sc'6 then
    let t'7 ← PMem.ldF32 (((this + 408) + ((UInt64.toInt64 (UInt8.toUInt64 (instance'))) * 112).toUInt64) + 36)
    let mut consumed_mah : Binary32 := t'7
    if (Binary32.isNaN consumed_mah) then
      return false
    PMem.stF32 mah consumed_mah
    return true
  else
    return false

/-- C++ `AP_BattMonitor_Analog::has_consumed_energy : bool () const`, `AP_BattMonitor_Analog.h:20-?`. -/
def AP_BattMonitor_Analog.has_consumed_energy (this : UInt64) : PMem.M Bool := do
  let t'1 ← AP_BattMonitor_Analog.has_current this
  return t'1

/-- C++ `AP_BattMonitor::consumed_wh : bool (float &, const uint8_t) const`, `AP_BattMonitor.cpp:895-902`. -/
def AP_BattMonitor.consumed_wh (this : UInt64) (wh : UInt64) (instance' : UInt8) : PMem.M Bool := do
  let mut instance' := instance'
  let t'1 ← PMem.ldU8 (this + 1492)
  let mut sc'3 := (decide ((UInt32.toInt32 (UInt8.toUInt32 (instance'))) < (UInt32.toInt32 (UInt8.toUInt32 (t'1)))))
  if sc'3 then
    let t'2 ← PMem.ldU64 ((this + 1416) + ((UInt64.toInt64 (UInt8.toUInt64 (instance'))) * 8).toUInt64)
    sc'3 := (t'2 != (0 : UInt64))
  let mut sc'6 := sc'3
  if sc'6 then
    let t'4 ← PMem.ldU64 ((this + 1416) + ((UInt64.toInt64 (UInt8.toUInt64 (instance'))) * 8).toUInt64)
    let t'5 ← AP_BattMonitor_Analog.has_consumed_energy t'4
    sc'6 := t'5
  if sc'6 then
    let t'7 ← PMem.ldF32 (((this + 408) + ((UInt64.toInt64 (UInt8.toUInt64 (instance'))) * 112).toUInt64) + 40)
    PMem.stF32 wh t'7
    return true
  else
    return false

/-- C++ `AP_BattMonitor::time_remaining : bool (uint32_t &, uint8_t) const`, `AP_BattMonitor.cpp:914-921`. -/
def AP_BattMonitor.time_remaining (this : UInt64) (seconds : UInt64) (instance' : UInt8) : PMem.M Bool := do
  let mut instance' := instance'
  let t'1 ← PMem.ldU8 (this + 1492)
  let mut sc'3 := (decide ((UInt32.toInt32 (UInt8.toUInt32 (instance'))) < (UInt32.toInt32 (UInt8.toUInt32 (t'1)))))
  if sc'3 then
    let t'2 ← PMem.ldU64 ((this + 1416) + ((UInt64.toInt64 (UInt8.toUInt64 (instance'))) * 8).toUInt64)
    sc'3 := (t'2 != (0 : UInt64))
  let mut sc'5 := sc'3
  if sc'5 then
    let t'4 ← PMem.ldB (((this + 408) + ((UInt64.toInt64 (UInt8.toUInt64 (instance'))) * 112).toUInt64) + 88)
    sc'5 := t'4
  if sc'5 then
    let t'6 ← PMem.ldU32 (((this + 408) + ((UInt64.toInt64 (UInt8.toUInt64 (instance'))) * 112).toUInt64) + 84)
    PMem.stU32 seconds t'6
    return true
  return false

/-- `AP_BattMonitor_Backend.get_mavlink_fault_bitmask` as a pure function of its arguments (it reads and writes no memory). -/
def AP_BattMonitor_Backend.get_mavlink_fault_bitmask.pure' (this : UInt64) : Id UInt32 := do
  return Int32.toUInt32 ((0 : Int32))

/-- C++ `AP_BattMonitor_Backend::get_mavlink_fault_bitmask : uint32_t () const`, `AP_Common.h:86-?`. -/
def AP_BattMonitor_Backend.get_mavlink_fault_bitmask (this : UInt64) : PMem.M UInt32 :=
  pure (_root_.Vehicle_lib.AP_BattMonitor_Backend.get_mavlink_fault_bitmask.pure' this)

/-- C++ `AP_BattMonitor::get_mavlink_fault_bitmask : uint32_t (const uint8_t) const`, `AP_BattMonitor.cpp:1222-1228`. -/
def AP_BattMonitor.get_mavlink_fault_bitmask (this : UInt64) (instance' : UInt8) : PMem.M UInt32 := do
  let mut instance' := instance'
  let t'1 ← PMem.ldU8 (this + 1492)
  let mut sc'3 := (decide ((UInt32.toInt32 (UInt8.toUInt32 (instance'))) ≥ (UInt32.toInt32 (UInt8.toUInt32 (t'1)))))
  if !sc'3 then
    let t'2 ← PMem.ldU64 ((this + 1416) + ((UInt64.toInt64 (UInt8.toUInt64 (instance'))) * 8).toUInt64)
    sc'3 := (t'2 == (0 : UInt64))
  if sc'3 then
    return Int32.toUInt32 ((0 : Int32))
  let t'4 ← PMem.ldU64 ((this + 1416) + ((UInt64.toInt64 (UInt8.toUInt64 (instance'))) * 8).toUInt64)
  let t'5 ← AP_BattMonitor_Backend.get_mavlink_fault_bitmask t'4
  return t'5

/-- C++ `AP_BattMonitor::healthy : bool (uint8_t) const`, `AP_BattMonitor.cpp:825-827`. -/
def AP_BattMonitor.healthy'2 (this : UInt64) (instance' : UInt8) : PMem.M Bool := do
  let mut instance' := instance'
  let t'1 ← PMem.ldU8 (this + 1492)
  let mut sc'3 := (decide ((UInt32.toInt32 (UInt8.toUInt32 (instance'))) < (UInt32.toInt32 (UInt8.toUInt32 (t'1)))))
  if sc'3 then
    let t'2 ← PMem.ldB (((this + 408) + ((UInt64.toInt64 (UInt8.toUInt64 (instance'))) * 112).toUInt64) + 73)
    sc'3 := t'2
  return sc'3

/-- C++ `AP_BattMonitor::get_mavlink_charge_state : MAV_BATTERY_CHARGE_STATE (const uint8_t) const`, `AP_BattMonitor.cpp:1195-1219`. -/
def AP_BattMonitor.get_mavlink_charge_state (this : UInt64) (instance' : UInt8) : PMem.M UInt32 := do
  let mut instance' := instance'
  let t'1 ← PMem.ldU8 (this + 1492)
  if (decide ((UInt32.toInt32 (UInt8.toUInt32 (instance'))) ≥ (UInt32.toInt32 (UInt8.toUInt32 (t'1))))) then
    return (0 : UInt32)
  let t'2 ← PMem.ldU8 (((this + 408) + ((UInt64.toInt64 (UInt8.toUInt64 (instance'))) * 112).toUInt64) + 72)
  let sw'3 := t'2
  if sw'3 == (0 : UInt8) || sw'3 == (1 : UInt8) then
    let t'4 ← AP_BattMonitor.get_mavlink_fault_bitmask this instance'
    let mut sc'6 := (t'4 != (Int32.toUInt32 ((0 : Int32))))
    if !sc'6 then
      let t'5 ← AP_BattMonitor.healthy'2 this instance'
      sc'6 := !t'5
    if sc'6 then
      return (6 : UInt32)
    return (1 : UInt32)
  else if sw'3 == (2 : UInt8) then
    return (2 : UInt32)
  else if sw'3 == (3 : UInt8) then
    return (3 : UInt32)
  else
    pure ()
  return (0 : UInt32)

/-- C++ `AP_BattMonitor::healthy : bool () const`, `AP_BattMonitor.cpp:1260-1275`. -/
def AP_BattMonitor.healthy (this : UInt64) : PMem.M Bool := do
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
    let t'5 ← AP_BattMonitor.allocated_type this i
    let t'6 ← AP_BattMonitor.configured_type this i
    if (t'5 != t'6) then
      return false
    let t'7 ← AP_BattMonitor.configured_type this i
    if (t'7 == (0 : Int32)) then
      continue
    let t'8 ← AP_BattMonitor.healthy'2 this i
    if !t'8 then
      return false
  return true

/-- C++ `AP_BattMonitor::num_instances : uint8_t () const`, `AP_Common.h:148-?`. -/
def AP_BattMonitor.num_instances (this : UInt64) : PMem.M UInt8 := do
  let t'1 ← PMem.ldU8 (this + 1492)
  return t'1

/-- C++ `AP_BattMonitor::gcs_voltage : float () const`, `AP_BattMonitor.h:168-?`. -/
def AP_BattMonitor.gcs_voltage (this : UInt64) : PMem.M Binary32 := do
  let t'1 ← AP_BattMonitor.gcs_voltage'2 this (Int8.toUInt8 (Int32.toInt8 ((0 : Int32))))
  return t'1

/-- C++ `AP_BattMonitor_Backend::AP_BattMonitor_Backend : void (AP_BattMonitor &, AP_BattMonitor::BattMonitor_State &, AP_BattMonitor_Params &)`, `AP_BattMonitor_Backend.cpp:55-61`. -/
def AP_BattMonitor_Backend.AP_BattMonitor_Backend (this : UInt64) (mon : UInt64) (mon_state : UInt64) (params : UInt64) : PMem.M Unit := do
  PMem.stU64 (this + 8) mon
  PMem.stU64 (this + 16) mon_state
  PMem.stU64 (this + 24) params
  return ()

/-- C++ `AP_BattMonitor_Analog::AP_BattMonitor_Analog : void (AP_BattMonitor &, AP_BattMonitor::BattMonitor_State &, AP_BattMonitor_Params &)`, `AP_BattMonitor_Analog.cpp:109-149`. -/
def AP_BattMonitor_Analog.AP_BattMonitor_Analog (this : UInt64) (mon : UInt64) (mon_state : UInt64) (params : UInt64) : PMem.M Unit := do
  AP_BattMonitor_Backend.AP_BattMonitor_Backend this mon mon_state params
  AP_Param.AP_Param'2 (this + 72)
  AP_Param.AP_Param'2 (this + 76)
  AP_Param.AP_Param'2 (this + 80)
  AP_Param.AP_Param'2 (this + 84)
  AP_Param.AP_Param'2 (this + 88)
  AP_Param.AP_Param'2 (this + 89)
  AP_Param.setup_object_defaults this (0x2020 : UInt64) /- &AP_BattMonitor_Analog::var_info -/
  let t'1 ← PMem.ldU8 (mon_state + 92)
  if ((UInt32.toInt32 (UInt8.toUInt32 (t'1))) == (1 : Int32)) then
    pure ()
  let t'2 := (0x2020 : UInt64) /- &AP_BattMonitor_Analog::var_info -/
  let t'3 ← PMem.ldU64 (this + 16)
  PMem.stU64 (t'3 + 104) t'2
  let t'4 ← PMem.ldU64 (this + 24)
  let t'5 ← AP_Enum'AP_BattMonitor_Params_Type.operator_const_AP_BattMonitor_Params.Type (t'4 + 38)
  if (t'5 != (31 : Int32)) then
    let t'6 ← PMem.ldU64 ((0xba88 : UInt64) /- &hal -/ + 32)
    let t'7 ← AP_ParamT'signed_char_1.operator_const_signed_char__ (this + 88)
    let t'8 ← PMem.ldI8 t'7
    let t'9 ← PMem.halDev "AP_HAL::AnalogIn::channel" t'6 #[(Int64.toUInt64 (Int16.toInt64 ((Int8.toInt16 (t'8)))))]
    PMem.stU64 (this + 56) t'9
    let t'10 ← PMem.ldU64 (this + 56)
    if (t'10 == (0 : UInt64)) then
      pure ()
  let t'11 ← PMem.ldU64 (this + 24)
  let t'12 ← AP_Enum'AP_BattMonitor_Params_Type.operator_const_AP_BattMonitor_Params.Type (t'11 + 38)
  let mut sc'15 := (t'12 == (4 : Int32))
  if !sc'15 then
    let t'13 ← PMem.ldU64 (this + 24)
    let t'14 ← AP_Enum'AP_BattMonitor_Params_Type.operator_const_AP_BattMonitor_Params.Type (t'13 + 38)
    sc'15 := (t'14 == (31 : Int32))
  if sc'15 then
    let t'16 ← PMem.ldU64 ((0xba88 : UInt64) /- &hal -/ + 32)
    let t'17 ← AP_ParamT'signed_char_1.operator_const_signed_char__ (this + 89)
    let t'18 ← PMem.ldI8 t'17
    let t'19 ← PMem.halDev "AP_HAL::AnalogIn::channel" t'16 #[(Int64.toUInt64 (Int16.toInt64 ((Int8.toInt16 (t'18)))))]
    PMem.stU64 (this + 64) t'19
    let t'20 ← PMem.ldU64 (this + 64)
    if (t'20 == (0 : UInt64)) then
      pure ()
  return ()

/-- `AP_BattMonitor_Analog.init` as a pure function of its arguments (it reads and writes no memory). -/
def AP_BattMonitor_Analog.init.pure' (this : UInt64) : Id Unit := do
  return ()

/-- C++ `AP_BattMonitor_Analog::init : void ()`, `AP_BattMonitor_Analog.h:25-?`. -/
def AP_BattMonitor_Analog.init (this : UInt64) : PMem.M Unit :=
  pure (_root_.Vehicle_lib.AP_BattMonitor_Analog.init.pure' this)

/-- C++ `AP_BattMonitor::init : void ()`, `AP_BattMonitor.cpp:590-774`. -/
def AP_BattMonitor.init (this : UInt64) : PMem.M Unit := do
  let t'1 ← PMem.ldU8 (this + 1492)
  if ((UInt32.toInt32 (UInt8.toUInt32 (t'1))) != (0 : Int32)) then
    return ()
  let t'2 := Int32.toInt8 ((127 : Int32))
  PMem.stI8 (this + 1520) t'2
  for instance''3 in [0:9] do
    let instance' : UInt8 := UInt8.ofNat instance''3
    let t'4 ← PMem.memset ((this + 408) + ((UInt64.toInt64 (UInt8.toUInt64 (instance'))) * 112).toUInt64) (255 : Int32) (28 : UInt64)
    discard <| pure (t'4)
    PMem.stU8 (((this + 408) + ((UInt64.toInt64 (UInt8.toUInt64 (instance'))) * 112).toUInt64) + 92) instance'
    let t'5 ← AP_BattMonitor.configured_type this instance'
    let mut allocation_type : Int32 := t'5
    let sw'6 := allocation_type
    if sw'6 == (3 : Int32) || sw'6 == (4 : Int32) || sw'6 == (31 : Int32) then
      let t'7 ← PMem.alloc 96
      AP_BattMonitor_Analog.AP_BattMonitor_Analog t'7 this ((this + 408) + ((UInt64.toInt64 (UInt8.toUInt64 (instance'))) * 112).toUInt64) ((this + 8) + ((UInt64.toInt64 (UInt8.toUInt64 (instance'))) * 44).toUInt64)
      PMem.stU64 ((this + 1416) + ((UInt64.toInt64 (UInt8.toUInt64 (instance'))) * 8).toUInt64) t'7
    else if sw'6 == (0 : Int32) then
      pure ()
    else
      pure ()
    let t'8 ← PMem.ldU64 ((this + 1416) + ((UInt64.toInt64 (UInt8.toUInt64 (instance'))) * 8).toUInt64)
    if (t'8 != (0 : UInt64)) then
      PMem.stI32 (((this + 408) + ((UInt64.toInt64 (UInt8.toUInt64 (instance'))) * 112).toUInt64) + 96) allocation_type
    let t'9 ← PMem.ldU64 ((this + 1416) + ((UInt64.toInt64 (UInt8.toUInt64 (instance'))) * 8).toUInt64)
    let mut sc'11 := (t'9 != 0)
    if sc'11 then
      let t'10 ← PMem.ldU64 (((this + 408) + ((UInt64.toInt64 (UInt8.toUInt64 (instance'))) * 112).toUInt64) + 104)
      sc'11 := (t'10 != 0)
    if sc'11 then
      let t'12 ← PMem.ldU64 (((this + 408) + ((UInt64.toInt64 (UInt8.toUInt64 (instance'))) * 112).toUInt64) + 104)
      PMem.stU64 ((0x8610 : UInt64) /- &AP_BattMonitor::backend_var_info -/ + ((UInt64.toInt64 (UInt8.toUInt64 (instance'))) * 8).toUInt64) t'12
      let t'13 ← PMem.ldU64 ((this + 1416) + ((UInt64.toInt64 (UInt8.toUInt64 (instance'))) * 8).toUInt64)
      let t'14 ← PMem.ldU64 ((0x8610 : UInt64) /- &AP_BattMonitor::backend_var_info -/ + ((UInt64.toInt64 (UInt8.toUInt64 (instance'))) * 8).toUInt64)
      AP_Param.load_object_from_eeprom t'13 t'14
      AP_Param.invalidate_count
    let t'15 ← PMem.ldU64 ((this + 1416) + ((UInt64.toInt64 (UInt8.toUInt64 (instance'))) * 8).toUInt64)
    if (t'15 != (0 : UInt64)) then
      let t'16 ← PMem.ldU64 ((this + 1416) + ((UInt64.toInt64 (UInt8.toUInt64 (instance'))) * 8).toUInt64)
      AP_BattMonitor_Analog.init t'16
      let t'17 := Int8.toUInt8 (Int32.toInt8 (((UInt32.toInt32 (UInt8.toUInt32 (instance'))) + (1 : Int32))))
      PMem.stU8 (this + 1492) t'17
  return ()

/-- C++ `AP_BattMonitor::get_highest_failsafe_priority : int8_t () const`, `AP_Common.h:199-?`. -/
def AP_BattMonitor.get_highest_failsafe_priority (this : UInt64) : PMem.M Int8 := do
  let t'1 ← PMem.ldI8 (this + 1520)
  return t'1

/-- C++ `AP_BattMonitor::voltage : float () const`, `AP_Common.h:164-?`. -/
def AP_BattMonitor.voltage'2 (this : UInt64) : PMem.M Binary32 := do
  let t'1 ← AP_BattMonitor.voltage this (Int8.toUInt8 (Int32.toInt8 ((0 : Int32))))
  return t'1

/-- `AP_BattMonitor_Backend.calculate_mah` as a pure function of its arguments (it reads and writes no memory). -/
def AP_BattMonitor_Backend.calculate_mah.pure' (amps : Binary32) (dt_us : Binary32) : Id Binary32 := do
  let mut amps := amps
  let mut dt_us := dt_us
  return ((amps * dt_us) * (Binary32.ofBits 0x3495248b /- 69450003/250000000000000 -/))

/-- C++ `AP_BattMonitor_Backend::calculate_mah : float (float, float)`, `AP_Common.h:100-?`. -/
def AP_BattMonitor_Backend.calculate_mah (amps : Binary32) (dt_us : Binary32) : PMem.M Binary32 :=
  pure (_root_.Vehicle_lib.AP_BattMonitor_Backend.calculate_mah.pure' amps dt_us)

/-- C++ `AP_BattMonitor_Backend::update_consumed : void (AP_BattMonitor::BattMonitor_State &, uint32_t)`, `AP_BattMonitor_Backend.cpp:359-367`. -/
def AP_BattMonitor_Backend.update_consumed (this : UInt64) (state : UInt64) (dt_us : UInt32) : PMem.M Unit := do
  let mut dt_us := dt_us
  let t'1 ← PMem.ldU32 (state + 44)
  if ((t'1 != (Int32.toUInt32 ((0 : Int32)))) && (decide (dt_us < (Int32.toUInt32 ((2000000 : Int32)))))) then
    let t'2 ← PMem.ldF32 (state + 32)
    let t'3 ← AP_BattMonitor_Backend.calculate_mah t'2 (UInt32.toBinary32 (dt_us))
    let mut mah : Binary32 := t'3
    let t'4 := (state + 36)
    let t'5 ← PMem.ldF32 t'4
    let t'6 := (t'5 + mah)
    PMem.stF32 t'4 t'6
    let t'7 := (state + 40)
    let t'8 ← PMem.ldF32 t'7
    let t'9 ← PMem.ldF32 (state + 28)
    let t'10 := (t'8 + (((Binary64.toBinary32 ((Binary64.ofBits 0x3f50624dd2f1a9fc /- 1/1000 -/))) * mah) * t'9))
    PMem.stF32 t'7 t'10
  return ()

/-- C++ `AP_BattMonitor_Analog::read : void ()`, `AP_BattMonitor_Analog.cpp:152-183`. -/
def AP_BattMonitor_Analog.read (this : UInt64) : PMem.M Unit := do
  let t'1 ← PMem.ldU64 (this + 16)
  let t'2 ← PMem.ldI32 (t'1 + 96)
  if (t'2 != (31 : Int32)) then
    let t'3 ← PMem.ldU64 (this + 56)
    let t'4 ← AP_ParamT'signed_char_1.operator_const_signed_char__ (this + 88)
    let t'5 ← PMem.ldI8 t'4
    let t'6 ← PMem.halDev "AP_HAL::AnalogSource::set_pin" t'3 #[(UInt8.toUInt64 ((Int8.toUInt8 (t'5))))]
    let t'7 := (t'6 != 0)
    let t'8 ← PMem.ldU64 (this + 16)
    PMem.stB (t'8 + 73) t'7
    let t'9 ← PMem.ldU64 (this + 56)
    let t'10 ← PMem.halDev "AP_HAL::AnalogSource::voltage_average" t'9 #[]
    let t'11 ← AP_ParamT'float_4.operator_const_float__'1 (this + 84)
    let t'12 ← PMem.ldF32 t'11
    let t'13 ← AP_ParamT'float_4.operator_const_float__'1 (this + 72)
    let t'14 ← PMem.ldF32 t'13
    let t'15 := (((Binary32.ofBits t'10.toUInt32) - t'12) * t'14)
    let t'16 ← PMem.ldU64 (this + 16)
    PMem.stF32 (t'16 + 28) t'15
  else
    let t'17 := (1 : Int32) != (0 : Int32)
    let t'18 ← PMem.ldU64 (this + 16)
    PMem.stB (t'18 + 73) t'17
    let t'19 := (Binary32.ofBits 0x00000000 /- 0 -/)
    let t'20 ← PMem.ldU64 (this + 16)
    PMem.stF32 (t'20 + 28) t'19
  let t'21 ← AP_BattMonitor_Analog.has_current this
  if t'21 then
    let mut tnow : UInt32 := (← PMem.clock).toUInt32
    let t'22 ← PMem.ldU64 (this + 16)
    let t'23 ← PMem.ldU32 (t'22 + 44)
    let mut dt_us : UInt32 := (tnow - t'23)
    let t'24 ← PMem.ldU64 (this + 16)
    let t'25 := (t'24 + 73)
    let t'26 ← PMem.ldB t'25
    let t'27 ← PMem.ldU64 (this + 64)
    let t'28 ← AP_ParamT'signed_char_1.operator_const_signed_char__ (this + 89)
    let t'29 ← PMem.ldI8 t'28
    let t'30 ← PMem.halDev "AP_HAL::AnalogSource::set_pin" t'27 #[(UInt8.toUInt64 ((Int8.toUInt8 (t'29))))]
    let t'31 := (t'26 && ((if (t'30 != 0) then (1 : Int32) else (0 : Int32)) != (0 : Int32)))
    PMem.stB t'25 t'31
    let t'32 ← PMem.ldU64 (this + 64)
    let t'33 ← PMem.halDev "AP_HAL::AnalogSource::voltage_average" t'32 #[]
    let t'34 ← AP_ParamT'float_4.operator_const_float__'1 (this + 80)
    let t'35 ← PMem.ldF32 t'34
    let t'36 ← AP_ParamT'float_4.operator_const_float__'1 (this + 76)
    let t'37 ← PMem.ldF32 t'36
    let t'38 := (((Binary32.ofBits t'33.toUInt32) - t'35) * t'37)
    let t'39 ← PMem.ldU64 (this + 16)
    PMem.stF32 (t'39 + 32) t'38
    let t'40 ← PMem.ldU64 (this + 16)
    AP_BattMonitor_Backend.update_consumed this t'40 dt_us
    let t'41 ← PMem.ldU64 (this + 16)
    PMem.stU32 (t'41 + 44) tnow
  return ()

/-- C++ `AP_BattMonitor_Backend::update_resistance_estimate : void ()`, `AP_BattMonitor_Backend.cpp:89-134`. -/
def AP_BattMonitor_Backend.update_resistance_estimate.body (fp : UInt64) (this : UInt64) : PMem.M Unit := do
  let t'1 ← AP_BattMonitor_Analog.has_current this
  let mut sc'5 := !t'1
  if !sc'5 then
    let t'2 ← PMem.ldU64 (this + 16)
    let t'3 ← PMem.ldF32 (t'2 + 32)
    let t'4 ← is_positive'float t'3
    sc'5 := !t'4
  if sc'5 then
    return ()
  let t'6 ← PMem.ldU64 (this + 16)
  let t'7 ← MAX'float_float (this + 40) (t'6 + 32)
  let t'8 ← PMem.ldF32 t'7
  PMem.stF32 (this + 40) t'8
  let t'9 ← PMem.ldU64 (this + 16)
  let t'10 ← PMem.ldF32 (t'9 + 32)
  let t'11 ← PMem.ldF32 (this + 44)
  let mut current_delta : Binary32 := (t'10 - t'11)
  let t'12 ← is_zero current_delta
  if t'12 then
    return ()
  let t'13 ← PMem.ldU64 (this + 16)
  let t'14 ← PMem.ldF32 (t'13 + 28)
  let t'15 ← PMem.ldF32 (this + 48)
  if (decide (t'14 > t'15)) then
    let t'16 ← PMem.ldU64 (this + 16)
    let t'17 ← PMem.ldF32 (t'16 + 28)
    PMem.stF32 (this + 48) t'17
    let t'18 ← PMem.ldU64 (this + 16)
    let t'19 ← PMem.ldF32 (t'18 + 32)
    PMem.stF32 (this + 52) t'19
  let mut now : UInt32 := ((← PMem.clock) / 1000).toUInt32
  let t'20 ← PMem.ldU32 (this + 32)
  let mut loop_interval : Binary32 := ((UInt32.toBinary32 ((now - t'20))) * (Binary32.ofBits 0x3a83126f /- 20000001/20000000000 -/))
  PMem.stU32 (this + 32) now
  let t'21 ← constrain_value_line'float (loop_interval / (loop_interval + (Binary32.ofBits 0x3f000000 /- 1/2 -/))) (Binary32.ofBits 0x00000000 /- 0 -/) (Binary32.ofBits 0x3f000000 /- 1/2 -/) (Int32.toUInt32 ((115 : Int32)))
  let mut filt_alpha : Binary32 := t'21
  PMem.stI32 (fp + 0) (1 : Int32)
  let t'22 ← PMem.ldU64 (this + 16)
  let t'23 ← PMem.ldF32 (t'22 + 32)
  let t'24 ← PMem.ldF32 (this + 44)
  let t'25 ← PMem.ldF32 (this + 40)
  PMem.stF32 (fp + 4) ((Binary32.ofBits 0x3dcccccd /- 100000001/1000000000 -/) * (Binary32.abs ((t'23 - t'24) / t'25)))
  let t'26 ← MIN'int_float (fp + 0) (fp + 4)
  let mut resistance_alpha : Binary32 := t'26
  let t'27 ← PMem.ldU64 (this + 16)
  let t'28 ← PMem.ldF32 (t'27 + 28)
  let t'29 ← PMem.ldF32 (this + 36)
  let mut resistance_estimate : Binary32 := ((-(t'28 - t'29)) / current_delta)
  let t'30 ← is_positive'float resistance_estimate
  if t'30 then
    let t'31 ← PMem.ldU64 (this + 16)
    let t'32 ← PMem.ldF32 (t'31 + 68)
    let t'33 := ((t'32 * ((Int32.toBinary32 ((1 : Int32))) - resistance_alpha)) + (resistance_estimate * resistance_alpha))
    let t'34 ← PMem.ldU64 (this + 16)
    PMem.stF32 (t'34 + 68) t'33
  let t'35 ← PMem.ldF32 (this + 48)
  let t'36 ← PMem.ldU64 (this + 16)
  let t'37 ← PMem.ldF32 (t'36 + 28)
  let mut sc'41 := (decide (t'35 > t'37))
  if sc'41 then
    let t'38 ← PMem.ldU64 (this + 16)
    let t'39 ← PMem.ldF32 (t'38 + 32)
    let t'40 ← PMem.ldF32 (this + 52)
    sc'41 := (decide (t'39 > t'40))
  if sc'41 then
    let t'42 ← PMem.ldF32 (this + 48)
    let t'43 ← PMem.ldU64 (this + 16)
    let t'44 ← PMem.ldF32 (t'43 + 28)
    let t'45 ← PMem.ldU64 (this + 16)
    let t'46 ← PMem.ldF32 (t'45 + 32)
    let t'47 ← PMem.ldF32 (this + 52)
    PMem.stF32 (fp + 8) ((t'42 - t'44) / (t'46 - t'47))
    let t'48 ← PMem.ldU64 (this + 16)
    let t'49 ← MIN'float_float (t'48 + 68) (fp + 8)
    let t'50 ← PMem.ldF32 t'49
    let t'51 ← PMem.ldU64 (this + 16)
    PMem.stF32 (t'51 + 68) t'50
  let t'52 ← PMem.ldF32 (this + 36)
  let t'53 ← PMem.ldU64 (this + 16)
  let t'54 ← PMem.ldF32 (t'53 + 28)
  let t'55 := ((t'52 * ((Int32.toBinary32 ((1 : Int32))) - filt_alpha)) + (t'54 * filt_alpha))
  PMem.stF32 (this + 36) t'55
  let t'56 ← PMem.ldF32 (this + 44)
  let t'57 ← PMem.ldU64 (this + 16)
  let t'58 ← PMem.ldF32 (t'57 + 32)
  let t'59 := ((t'56 * ((Int32.toBinary32 ((1 : Int32))) - filt_alpha)) + (t'58 * filt_alpha))
  PMem.stF32 (this + 44) t'59
  let t'60 ← PMem.ldU64 (this + 16)
  let t'61 ← PMem.ldF32 (t'60 + 28)
  let t'62 ← PMem.ldU64 (this + 16)
  let t'63 ← PMem.ldF32 (t'62 + 32)
  let t'64 ← PMem.ldU64 (this + 16)
  let t'65 ← PMem.ldF32 (t'64 + 68)
  let t'66 := (t'61 + (t'63 * t'65))
  let t'67 ← PMem.ldU64 (this + 16)
  PMem.stF32 (t'67 + 64) t'66
  return ()

def AP_BattMonitor_Backend.update_resistance_estimate (this : UInt64) : PMem.M Unit := do
  let fp ← PMem.enter 12
  let r ← AP_BattMonitor_Backend.update_resistance_estimate.body fp this
  PMem.leave fp
  return r

/-- C++ `AP_BattMonitor_Backend::update_failsafes : AP_BattMonitor::Failsafe ()`, `AP_BattMonitor_Backend.cpp:152-200`. -/
def AP_BattMonitor_Backend.update_failsafes.body (fp : UInt64) (this : UInt64) : PMem.M UInt8 := do
  let mut now : UInt32 := ((← PMem.clock) / 1000).toUInt32
  AP_BattMonitor_Backend.check_failsafe_types this (fp + 0) (fp + 8) (fp + 16) (fp + 24)
  let t'1 ← PMem.ldB (fp + 16)
  if t'1 then
    let t'2 ← PMem.ldU64 (this + 16)
    let t'3 ← PMem.ldU32 (t'2 + 52)
    if (t'3 == (Int32.toUInt32 ((0 : Int32)))) then
      let t'4 ← PMem.ldU64 (this + 16)
      PMem.stU32 (t'4 + 52) now
    else
      let t'5 ← PMem.ldU64 (this + 24)
      let t'6 ← AP_ParamT'unsigned_char_1.operator_const_unsigned_char__ (t'5 + 39)
      let t'7 ← PMem.ldU8 t'6
      let mut sc'13 := (decide ((UInt32.toInt32 (UInt8.toUInt32 (t'7))) > (0 : Int32)))
      if sc'13 then
        let t'8 ← PMem.ldU64 (this + 16)
        let t'9 ← PMem.ldU32 (t'8 + 52)
        let t'10 ← PMem.ldU64 (this + 24)
        let t'11 ← AP_ParamT'unsigned_char_1.operator_const_unsigned_char__ (t'10 + 39)
        let t'12 ← PMem.ldU8 t'11
        sc'13 := (decide ((now - t'9) > ((UInt8.toUInt32 (t'12)) * (1000 : UInt32))))
      if sc'13 then
        return (3 : UInt8)
  else
    let t'14 := Int32.toUInt32 ((0 : Int32))
    let t'15 ← PMem.ldU64 (this + 16)
    PMem.stU32 (t'15 + 52) t'14
  let t'16 ← PMem.ldB (fp + 24)
  if t'16 then
    return (3 : UInt8)
  let t'17 ← PMem.ldB (fp + 0)
  if t'17 then
    let t'18 ← PMem.ldU64 (this + 16)
    let t'19 ← PMem.ldU32 (t'18 + 48)
    if (t'19 == (Int32.toUInt32 ((0 : Int32)))) then
      let t'20 ← PMem.ldU64 (this + 16)
      PMem.stU32 (t'20 + 48) now
    else
      let t'21 ← PMem.ldU64 (this + 24)
      let t'22 ← AP_ParamT'unsigned_char_1.operator_const_unsigned_char__ (t'21 + 39)
      let t'23 ← PMem.ldU8 t'22
      let mut sc'29 := (decide ((UInt32.toInt32 (UInt8.toUInt32 (t'23))) > (0 : Int32)))
      if sc'29 then
        let t'24 ← PMem.ldU64 (this + 16)
        let t'25 ← PMem.ldU32 (t'24 + 48)
        let t'26 ← PMem.ldU64 (this + 24)
        let t'27 ← AP_ParamT'unsigned_char_1.operator_const_unsigned_char__ (t'26 + 39)
        let t'28 ← PMem.ldU8 t'27
        sc'29 := (decide ((now - t'25) > ((UInt8.toUInt32 (t'28)) * (1000 : UInt32))))
      if sc'29 then
        return (2 : UInt8)
  else
    let t'30 := Int32.toUInt32 ((0 : Int32))
    let t'31 ← PMem.ldU64 (this + 16)
    PMem.stU32 (t'31 + 48) t'30
  let t'32 ← PMem.ldB (fp + 8)
  if t'32 then
    return (2 : UInt8)
  let t'33 ← PMem.ldU64 (this + 16)
  let t'34 ← PMem.ldU32 (t'33 + 76)
  if (decide ((now - t'34) > (Int32.toUInt32 ((5000 : Int32))))) then
    return (1 : UInt8)
  return (0 : UInt8)

def AP_BattMonitor_Backend.update_failsafes (this : UInt64) : PMem.M UInt8 := do
  let fp ← PMem.enter 25
  let r ← AP_BattMonitor_Backend.update_failsafes.body fp this
  PMem.leave fp
  return r

/-- C++ `AP_BattMonitor_Params::AP_BattMonitor_Params : void ()`, `AP_BattMonitor_Params.cpp:209-211`. -/
def AP_BattMonitor_Params.AP_BattMonitor_Params (this : UInt64) : PMem.M Unit := do
  AP_Param.AP_Param'2 (this + 0)
  AP_Param.AP_Param'2 (this + 4)
  AP_Param.AP_Param'2 (this + 8)
  AP_Param.AP_Param'2 (this + 12)
  AP_Param.AP_Param'2 (this + 16)
  AP_Param.AP_Param'2 (this + 20)
  AP_Param.AP_Param'2 (this + 24)
  AP_Param.AP_Param'2 (this + 28)
  AP_Param.AP_Param'2 (this + 32)
  AP_Param.AP_Param'2 (this + 36)
  AP_Enum'AP_BattMonitor_Params_Type.AP_Enum (this + 38)
  AP_Param.AP_Param'2 (this + 39)
  AP_Param.AP_Param'2 (this + 40)
  AP_Param.AP_Param'2 (this + 41)
  AP_Param.AP_Param'2 (this + 42)
  AP_Param.setup_object_defaults this (0x64d8 : UInt64) /- &AP_BattMonitor_Params::var_info -/
  return ()

/-- `AP_BattMonitor.cells.cells` as a pure function of its arguments (it reads and writes no memory). -/
def AP_BattMonitor.cells.cells.pure' (this : UInt64) : Id Unit := do
  return ()

/-- C++ `AP_BattMonitor::cells::cells : void () noexcept`, `AP_Common.h:?-?`. -/
def AP_BattMonitor.cells.cells (this : UInt64) : PMem.M Unit :=
  pure (_root_.Vehicle_lib.AP_BattMonitor.cells.cells.pure' this)

/-- C++ `AP_BattMonitor::AP_BattMonitor : void (uint32_t, battery_failsafe_handler_fn_t, const int8_t *)`, `AP_BattMonitor.cpp:576-587`. -/
def AP_BattMonitor.AP_BattMonitor (this : UInt64) (log_battery_bit : UInt32) (battery_failsafe_handler_fn : UInt64) (failsafe_priorities : UInt64) : PMem.M Unit := do
  let mut log_battery_bit := log_battery_bit
  let mut failsafe_priorities := failsafe_priorities
  AP_BattMonitor_Params.AP_BattMonitor_Params ((this + 8) + 0)
  AP_BattMonitor_Params.AP_BattMonitor_Params ((this + 8) + 44)
  AP_BattMonitor_Params.AP_BattMonitor_Params ((this + 8) + 88)
  AP_BattMonitor_Params.AP_BattMonitor_Params ((this + 8) + 132)
  AP_BattMonitor_Params.AP_BattMonitor_Params ((this + 8) + 176)
  AP_BattMonitor_Params.AP_BattMonitor_Params ((this + 8) + 220)
  AP_BattMonitor_Params.AP_BattMonitor_Params ((this + 8) + 264)
  AP_BattMonitor_Params.AP_BattMonitor_Params ((this + 8) + 308)
  AP_BattMonitor_Params.AP_BattMonitor_Params ((this + 8) + 352)
  AP_BattMonitor.cells.cells ((this + 408) + 0)
  AP_BattMonitor.cells.cells ((this + 408) + 112)
  AP_BattMonitor.cells.cells ((this + 408) + 224)
  AP_BattMonitor.cells.cells ((this + 408) + 336)
  AP_BattMonitor.cells.cells ((this + 408) + 448)
  AP_BattMonitor.cells.cells ((this + 408) + 560)
  AP_BattMonitor.cells.cells ((this + 408) + 672)
  AP_BattMonitor.cells.cells ((this + 408) + 784)
  AP_BattMonitor.cells.cells ((this + 408) + 896)
  PMem.stU32 (this + 1488) log_battery_bit
  Functor'void_const_char_const_signed_char.Functor'2 (this + 1496) battery_failsafe_handler_fn
  PMem.stU64 (this + 1512) failsafe_priorities
  AP_Param.setup_object_defaults this (0x37f0 : UInt64) /- &AP_BattMonitor::var_info -/
  let t'1 ← PMem.ldU64 (0x13188 : UInt64) /- &AP_BattMonitor::_singleton -/
  if (t'1 != (0 : UInt64)) then
    pure ()
  PMem.stU64 (0x13188 : UInt64) /- &AP_BattMonitor::_singleton -/ this
  return ()

end Vehicle_lib
