import ArduLean.Runtime.Hal
import ArduLean.Vehicle.libraries.AP_Param.AP_Param

/-!
ArduPilot `libraries/AP_BoardConfig`, part 1 of 2. Sources: `libraries/AP_BoardConfig/AP_BoardConfig.cpp`, `libraries/AP_BoardConfig/board_drivers.cpp`, `libraries/AP_BoardConfig/AP_BoardConfig.h`.

Items of `lean/Vehicle_lib.lean` (the vehicle translation), unchanged; placed by `tools/split_modules.py` (`ArduLean/Vehicle/INDEX.md`).
-/

open FloatLib.Floats (Binary32 Binary64)

set_option linter.unusedVariables false
set_option linter.unreachableTactic false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false

namespace Vehicle_lib

/-- C++ `AP_BoardConfig::in_config_error : bool ()`, `AP_BoardConfig.h:49-?`. -/
def AP_BoardConfig.in_config_error  : PMem.M Bool := do
  let t'1 ← PMem.ldB (0xbf80 : UInt64) /- &AP_BoardConfig::_in_error_loop -/
  return t'1

/-- C++ `AP_BoardConfig::get_singleton : AP_BoardConfig *()`, `AP_Common.h:32-34`. -/
def AP_BoardConfig.get_singleton  : PMem.M UInt64 := do
  let t'1 ← PMem.ldU64 (0xbf98 : UInt64) /- &AP_BoardConfig::_singleton -/
  return t'1

/-- C++ `AP_BoardConfig::get_safety_button_options : uint16_t () const`, `AP_Common.h:127-129`. -/
def AP_BoardConfig.get_safety_button_options (this : UInt64) : PMem.M UInt16 := do
  let t'1 ← AP_ParamT'unsigned_short_2.operator_const_unsigned_short__ ((this + 4) + 2)
  let t'2 ← PMem.ldU16 t'1
  return t'2

/-- C++ `AP_BoardConfig::get_minimum_board_voltage : float ()`, `AP_Common.h:142-144`. -/
def AP_BoardConfig.get_minimum_board_voltage  : PMem.M Binary32 := do
  let t'1 ← PMem.ldU64 (0xbf98 : UInt64) /- &AP_BoardConfig::_singleton -/
  let mut c'2 : Binary32 := default
  if (t'1 != 0) then
    let t'3 ← PMem.ldU64 (0xbf98 : UInt64) /- &AP_BoardConfig::_singleton -/
    let t'4 ← AP_ParamTBase'float_4.get (t'3 + 64)
    let t'5 ← PMem.ldF32 t'4
    c'2 := t'5
  else
    c'2 := Int32.toBinary32 ((0 : Int32))
  return c'2

/-- C++ `AP_BoardConfig::get_minimum_servo_voltage : float ()`, `AP_Common.h:149-151`. -/
def AP_BoardConfig.get_minimum_servo_voltage  : PMem.M Binary32 := do
  let t'1 ← PMem.ldU64 (0xbf98 : UInt64) /- &AP_BoardConfig::_singleton -/
  let mut c'2 : Binary32 := default
  if (t'1 != 0) then
    let t'3 ← PMem.ldU64 (0xbf98 : UInt64) /- &AP_BoardConfig::_singleton -/
    let t'4 ← AP_ParamTBase'float_4.get (t'3 + 68)
    let t'5 ← PMem.ldF32 t'4
    c'2 := t'5
  else
    c'2 := Int32.toBinary32 ((0 : Int32))
  return c'2

/-- C++ `AP::boardConfig : AP_BoardConfig *()`, `AP_BoardConfig.cpp:639-641`. -/
def AP.boardConfig  : PMem.M UInt64 := do
  let t'1 ← AP_BoardConfig.get_singleton
  return t'1

/-- C++ `AP_BoardConfig::get_sdcard_mission_kb : uint16_t ()`, `AP_BoardConfig.h:243-245`. -/
def AP_BoardConfig.get_sdcard_mission_kb  : PMem.M UInt16 := do
  let t'1 ← PMem.ldU64 (0xbf98 : UInt64) /- &AP_BoardConfig::_singleton -/
  let mut c'2 : Int32 := default
  if (t'1 != 0) then
    let t'3 ← PMem.ldU64 (0xbf98 : UInt64) /- &AP_BoardConfig::_singleton -/
    let t'4 ← AP_ParamTBase'short_2.get (t'3 + 24)
    let t'5 ← PMem.ldI16 t'4
    c'2 := Int16.toInt32 (t'5)
  else
    c'2 := (0 : Int32)
  return Int16.toUInt16 (Int32.toInt16 (c'2))

/-- C++ `AP_BoardConfig::board_setup_uart : void ()`, `board_drivers.cpp:350-394`. -/
def AP_BoardConfig.board_setup_uart (this : UInt64) : PMem.M Unit := do
  let t'1 ← PMem.halDev "AP_HAL::HAL::serial" (0xba88 : UInt64) /- &hal -/ #[(UInt8.toUInt64 ((Int8.toUInt8 (Int32.toInt8 ((1 : Int32))))))]
  if (t'1 != (0 : UInt64)) then
    pure ()
  let t'2 ← PMem.halDev "AP_HAL::HAL::serial" (0xba88 : UInt64) /- &hal -/ #[(UInt8.toUInt64 ((Int8.toUInt8 (Int32.toInt8 ((2 : Int32))))))]
  if (t'2 != (0 : UInt64)) then
    pure ()
  let t'3 ← PMem.halDev "AP_HAL::HAL::serial" (0xba88 : UInt64) /- &hal -/ #[(UInt8.toUInt64 ((Int8.toUInt8 (Int32.toInt8 ((3 : Int32))))))]
  if (t'3 != (0 : UInt64)) then
    pure ()
  let t'4 ← PMem.halDev "AP_HAL::HAL::serial" (0xba88 : UInt64) /- &hal -/ #[(UInt8.toUInt64 ((Int8.toUInt8 (Int32.toInt8 ((4 : Int32))))))]
  if (t'4 != (0 : UInt64)) then
    pure ()
  let t'5 ← PMem.halDev "AP_HAL::HAL::serial" (0xba88 : UInt64) /- &hal -/ #[(UInt8.toUInt64 ((Int8.toUInt8 (Int32.toInt8 ((5 : Int32))))))]
  if (t'5 != (0 : UInt64)) then
    pure ()
  let t'6 ← PMem.halDev "AP_HAL::HAL::serial" (0xba88 : UInt64) /- &hal -/ #[(UInt8.toUInt64 ((Int8.toUInt8 (Int32.toInt8 ((6 : Int32))))))]
  if (t'6 != (0 : UInt64)) then
    pure ()
  let t'7 ← PMem.halDev "AP_HAL::HAL::serial" (0xba88 : UInt64) /- &hal -/ #[(UInt8.toUInt64 ((Int8.toUInt8 (Int32.toInt8 ((7 : Int32))))))]
  if (t'7 != (0 : UInt64)) then
    pure ()
  let t'8 ← PMem.halDev "AP_HAL::HAL::serial" (0xba88 : UInt64) /- &hal -/ #[(UInt8.toUInt64 ((Int8.toUInt8 (Int32.toInt8 ((8 : Int32))))))]
  if (t'8 != (0 : UInt64)) then
    pure ()
  return ()

/-- `AP_BoardConfig.board_setup_sbus` as a pure function of its arguments (it reads and writes no memory). -/
def AP_BoardConfig.board_setup_sbus.pure' (this : UInt64) : Id Unit := do
  return ()

/-- C++ `AP_BoardConfig::board_setup_sbus : void ()`, `board_drivers.cpp:399-426`. -/
def AP_BoardConfig.board_setup_sbus (this : UInt64) : PMem.M Unit :=
  pure (_root_.Vehicle_lib.AP_BoardConfig.board_setup_sbus.pure' this)

/-- C++ `AP_BoardConfig::board_setup : void ()`, `board_drivers.cpp:432-453`. -/
def AP_BoardConfig.board_setup (this : UInt64) : PMem.M Unit := do
  AP_BoardConfig.board_setup_uart this
  AP_BoardConfig.board_setup_sbus this
  return ()

/-- C++ `AP_BoardConfig::allocation_error : void (const char *, ...) __attribute__((noreturn))`, `AP_BoardConfig.cpp:591-599`. NOT TRANSLATED (the back end rejects: no Lean type for T(fn,0,False,void (const char *, ...) __attribute__)): a stub. -/
def AP_BoardConfig.allocation_error (fmt : UInt64) (va' : UInt64) : PMem.M Unit := do
  PMem.unreached "rejected AP_BoardConfig::allocation_error"
  return ()

/-- C++ `AP_BoardConfig::set_default_safety_ignore_mask : void (uint32_t)`, `AP_BoardConfig.cpp:534-537`. -/
def AP_BoardConfig.set_default_safety_ignore_mask.body (fp : UInt64) (this : UInt64) (mask : UInt32) : PMem.M Unit := do
  PMem.stU32 (fp + 0) mask
  AP_ParamTBase'unsigned_int_3.set_default ((this + 4) + 4) (fp + 0)
  return ()

def AP_BoardConfig.set_default_safety_ignore_mask (this : UInt64) (mask : UInt32) : PMem.M Unit := do
  let fp ← PMem.enter 4
  let r ← AP_BoardConfig.set_default_safety_ignore_mask.body fp this mask
  PMem.leave fp
  return r

/-- C++ `AP_BoardConfig::board_init_debug : void ()`, `board_drivers.cpp:56-68`. -/
def AP_BoardConfig.board_init_debug (this : UInt64) : PMem.M Unit := do
  let t'1 ← AP_ParamT'unsigned_int_3.operator_const_unsigned_int__ (this + 76)
  let t'2 ← PMem.ldU32 t'1
  if ((t'2 &&& (8 : UInt32)) == (Int32.toUInt32 ((0 : Int32)))) then
    pure ()
  return ()

/-- C++ `AP_BoardConfig::throw_error : void (const char *, const char *, va_list) __attribute__((noreturn))`, `AP_BoardConfig.cpp:550-589`. NOT TRANSLATED (the back end rejects: no body for function d138:0x14891e3c8 (vprintf, int (const char *, va_list))): a stub. -/
def AP_BoardConfig.throw_error (err_type : UInt64) (fmt : UInt64) (arg : UInt64) : PMem.M Unit := do
  PMem.unreached "rejected AP_BoardConfig::throw_error"
  return ()

/-- C++ `AP_BoardConfig::AP_BoardConfig : void ()`, `AP_BoardConfig.cpp:148-157`. -/
def AP_BoardConfig.AP_BoardConfig (this : UInt64) : PMem.M Unit := do
  AP_Param.AP_Param'2 (this + 0)
  AP_Param.AP_Param'2 (this + 4)
  AP_Param.AP_Param'2 ((this + 4) + 2)
  AP_Param.AP_Param'2 ((this + 4) + 4)
  AP_Param.AP_Param'2 ((this + 4) + 8)
  AP_Param.AP_Param'2 ((this + 4) + 9)
  AP_Param.AP_Param'2 ((this + 4) + 10)
  AP_Param.AP_Param'2 ((this + 4) + 11)
  AP_Param.AP_Param'2 ((this + 4) + 12)
  AP_Param.AP_Param'2 ((this + 4) + 13)
  AP_Param.AP_Param'2 ((this + 4) + 14)
  AP_Param.AP_Param'2 ((this + 4) + 15)
  AP_Param.AP_Param'2 ((this + 4) + 16)
  AP_Param.AP_Param'2 ((this + 4) + 17)
  AP_Param.AP_Param'2 ((this + 4) + 18)
  AP_Param.AP_Param'2 ((this + 4) + 19)
  AP_Param.AP_Param'2 (this + 24)
  AP_Param.AP_Param'2 ((this + 24) + 2)
  -- rtc: constructed by the estimator World
  AP_Param.AP_Param'2 (this + 64)
  AP_Param.AP_Param'2 (this + 68)
  AP_Param.AP_Param'2 (this + 72)
  AP_Param.AP_Param'2 (this + 74)
  AP_Param.AP_Param'2 (this + 76)
  AP_Param.AP_Param'2 (this + 80)
  PMem.stU64 (0xbf98 : UInt64) /- &AP_BoardConfig::_singleton -/ this
  AP_Param.setup_object_defaults this (0x3aa0 : UInt64) /- &AP_BoardConfig::var_info -/
  return ()

end Vehicle_lib
