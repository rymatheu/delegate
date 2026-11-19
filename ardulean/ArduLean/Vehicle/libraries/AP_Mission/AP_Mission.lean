import ArduLean.Runtime.Bridge
import ArduLean.Vehicle.libraries.AP_Math.AP_Math
import ArduLean.Vehicle.libraries.StorageManager.StorageManager
import ArduLean.Vehicle.libraries.AP_Param.AP_Param

/-!
ArduPilot `libraries/AP_Mission`, part 1 of 3. Sources: `libraries/AP_Mission/AP_Mission.cpp`, `libraries/AP_Mission/AP_Mission_Commands.cpp`.

Items of `lean/Vehicle_lib.lean` (the vehicle translation), unchanged; placed by `tools/split_modules.py` (`ArduLean/Vehicle/INDEX.md`).
-/

open FloatLib.Floats (Binary32 Binary64)

set_option linter.unusedVariables false
set_option linter.unreachableTactic false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false

namespace Vehicle_lib

/-- C++ `AP_Mission::num_commands_max : uint16_t () const`, `AP_Common.h:536-538`. -/
def AP_Mission.num_commands_max (this : UInt64) : PMem.M UInt16 := do
  let t'1 ← PMem.ldU16 (this + 604)
  return t'1

/-- `AP_Mission.stored_in_location` as a pure function of its arguments (it reads and writes no memory). -/
def AP_Mission.stored_in_location.pure' (id : UInt16) : Id Bool := do
  let mut id := id
  let sw'1 := UInt32.toInt32 (UInt16.toUInt32 (id))
  if sw'1 == (16 : Int32) || sw'1 == (17 : Int32) || sw'1 == (18 : Int32) || sw'1 == (19 : Int32) || sw'1 == (21 : Int32) || sw'1 == (22 : Int32) || sw'1 == (30 : Int32) || sw'1 == (31 : Int32) || sw'1 == (82 : Int32) || sw'1 == (92 : Int32) || sw'1 == (179 : Int32) || sw'1 == (188 : Int32) || sw'1 == (189 : Int32) || sw'1 == (191 : Int32) || sw'1 == (195 : Int32) || sw'1 == (201 : Int32) || sw'1 == (84 : Int32) || sw'1 == (85 : Int32) || sw'1 == (94 : Int32) || sw'1 == (5001 : Int32) || sw'1 == (5002 : Int32) || sw'1 == (5003 : Int32) || sw'1 == (5004 : Int32) || sw'1 == (5000 : Int32) || sw'1 == (5100 : Int32) || sw'1 == (36 : Int32) then
    return true
  else
    return false

/-- C++ `AP_Mission::stored_in_location : bool (uint16_t)`, `AP_Mission.cpp:908-941`. -/
def AP_Mission.stored_in_location (id : UInt16) : PMem.M Bool :=
  pure (_root_.Vehicle_lib.AP_Mission.stored_in_location.pure' id)

/-- C++ `AP_Mission::write_cmd_to_storage : bool (uint16_t, const Mission_Command &)`, `AP_Mission.cpp:946-1007`. -/
def AP_Mission.write_cmd_to_storage.body (fp : UInt64) (this : UInt64) (index : UInt16) (cmd : UInt64) : PMem.M Bool := do
  let mut index := index
  let t'1 ← AP_Mission.num_commands_max this
  if (decide ((UInt32.toInt32 (UInt16.toUInt32 (index))) ≥ (UInt32.toInt32 (UInt16.toUInt32 (t'1))))) then
    return false
  PMem.stBits ((((fp + 0) + 0) + 0) + 0) 0 1 (UInt8.toUInt64 ((0 : UInt8)))
  PMem.stBits ((((fp + 0) + 0) + 0) + 0) 1 1 (UInt8.toUInt64 ((0 : UInt8)))
  PMem.stBits ((((fp + 0) + 0) + 0) + 0) 2 1 (UInt8.toUInt64 ((0 : UInt8)))
  PMem.stBits ((((fp + 0) + 0) + 0) + 0) 3 1 (UInt8.toUInt64 ((0 : UInt8)))
  PMem.stBits ((((fp + 0) + 0) + 0) + 0) 4 1 (UInt8.toUInt64 ((0 : UInt8)))
  PMem.stBits ((((fp + 0) + 0) + 0) + 0) 5 1 (UInt8.toUInt64 ((0 : UInt8)))
  PMem.stBits ((((fp + 0) + 0) + 0) + 0) 6 1 (UInt8.toUInt64 ((0 : UInt8)))
  PMem.stBits ((((fp + 0) + 0) + 0) + 0) 7 1 (UInt8.toUInt64 ((0 : UInt8)))
  PMem.stBits ((fp + 0) + 0) 8 24 (Int64.toUInt64 (Int32.toInt64 ((0 : Int32))))
  discard <| PMem.memset (((fp + 0) + 0) + 4) 0 4
  discard <| PMem.memset (((fp + 0) + 0) + 8) 0 4
  let t'2 ← PMem.ldU16 (cmd + 2)
  let t'3 ← AP_Mission.stored_in_location t'2
  if t'3 then
    let t'4 ← PMem.ldBits (cmd + 8) 0 1
    let t'5 := UInt64.toUInt8 (t'4)
    PMem.stBits (fp + 0) 0 1 (UInt8.toUInt64 (t'5))
    let t'6 ← PMem.ldBits (cmd + 8) 1 1
    let t'7 := UInt64.toUInt8 (t'6)
    PMem.stBits (fp + 0) 2 1 (UInt8.toUInt64 (t'7))
    let t'8 ← PMem.ldBits (cmd + 8) 2 1
    let t'9 := UInt64.toUInt8 (t'8)
    PMem.stBits (fp + 0) 3 1 (UInt8.toUInt64 (t'9))
    let t'10 ← PMem.ldBits (cmd + 8) 3 1
    let t'11 := UInt64.toUInt8 (t'10)
    PMem.stBits (fp + 0) 4 1 (UInt8.toUInt64 (t'11))
    let t'12 ← PMem.ldBits (cmd + 8) 4 1
    let t'13 := UInt64.toUInt8 (t'12)
    PMem.stBits (fp + 0) 5 1 (UInt8.toUInt64 (t'13))
    let t'14 ← PMem.ldU8 (cmd + 24)
    let t'15 := UInt32.toUInt8 ((((UInt8.toUInt32 (t'14)) &&& ((1 : UInt32) <<< (Int32.toUInt32 ((0 : Int32))))) >>> (Int32.toUInt32 ((0 : Int32)))))
    PMem.stBits (fp + 0) 6 1 (UInt8.toUInt64 (t'15))
    let t'16 ← PMem.ldU8 (cmd + 24)
    let t'17 := UInt32.toUInt8 ((((UInt8.toUInt32 (t'16)) &&& ((1 : UInt32) <<< (Int32.toUInt32 ((1 : Int32))))) >>> (Int32.toUInt32 ((1 : Int32)))))
    PMem.stBits (fp + 0) 7 1 (UInt8.toUInt64 (t'17))
    let t'18 ← PMem.ldI32 ((cmd + 8) + 4)
    PMem.stBits (fp + 0) 8 24 (Int64.toUInt64 (Int32.toInt64 (t'18)))
    let t'19 ← PMem.ldI32 ((cmd + 8) + 8)
    PMem.stI32 ((fp + 0) + 4) t'19
    let t'20 ← PMem.ldI32 ((cmd + 8) + 12)
    PMem.stI32 ((fp + 0) + 8) t'20
  else
    let t'21 ← PMem.memcpy (fp + 0) (cmd + 8) (Int64.toUInt64 (Int32.toInt64 ((12 : Int32))))
    discard <| pure (t'21)
  let mut pos_in_storage : UInt16 := Int16.toUInt16 (Int32.toInt16 (((4 : Int32) + ((UInt32.toInt32 (UInt16.toUInt32 (index))) * (15 : Int32)))))
  let t'22 ← PMem.ldU16 (cmd + 2)
  if (decide ((UInt32.toInt32 (UInt16.toUInt32 (t'22))) < (256 : Int32))) then
    let t'23 ← PMem.ldU16 (cmd + 2)
    StorageAccess.write_byte (0xbf28 : UInt64) /- &AP_Mission::_storage -/ pos_in_storage (UInt16.toUInt8 (t'23))
    let t'24 ← PMem.ldU16 (cmd + 4)
    StorageAccess.write_uint16 (0xbf28 : UInt64) /- &AP_Mission::_storage -/ (Int16.toUInt16 (Int32.toInt16 (((UInt32.toInt32 (UInt16.toUInt32 (pos_in_storage))) + (1 : Int32))))) t'24
    let t'25 ← StorageAccess.write_block (0xbf28 : UInt64) /- &AP_Mission::_storage -/ (Int16.toUInt16 (Int32.toInt16 (((UInt32.toInt32 (UInt16.toUInt32 (pos_in_storage))) + (3 : Int32))))) (fp + 0) (Int64.toUInt64 (Int32.toInt64 ((12 : Int32))))
    discard <| pure (t'25)
  else
    let mut tag_byte : UInt8 := Int8.toUInt8 (Int32.toInt8 ((0 : Int32)))
    let t'26 ← PMem.ldU16 (cmd + 2)
    let mut sc'28 := ((UInt32.toInt32 (UInt16.toUInt32 (t'26))) == (UInt32.toInt32 ((42702 : UInt32))))
    if !sc'28 then
      let t'27 ← PMem.ldU16 (cmd + 2)
      sc'28 := ((UInt32.toInt32 (UInt16.toUInt32 (t'27))) == (UInt32.toInt32 ((2500 : UInt32))))
    let mut sc'30 := sc'28
    if !sc'30 then
      let t'29 ← PMem.ldU16 (cmd + 2)
      sc'30 := ((UInt32.toInt32 (UInt16.toUInt32 (t'29))) == (UInt32.toInt32 ((2501 : UInt32))))
    if sc'30 then
      let t'31 := Int8.toUInt8 (Int32.toInt8 ((1 : Int32)))
      tag_byte := t'31
    StorageAccess.write_byte (0xbf28 : UInt64) /- &AP_Mission::_storage -/ pos_in_storage tag_byte
    let t'32 ← PMem.ldU16 (cmd + 2)
    StorageAccess.write_uint16 (0xbf28 : UInt64) /- &AP_Mission::_storage -/ (Int16.toUInt16 (Int32.toInt16 (((UInt32.toInt32 (UInt16.toUInt32 (pos_in_storage))) + (1 : Int32))))) t'32
    let t'33 ← PMem.ldU16 (cmd + 4)
    StorageAccess.write_uint16 (0xbf28 : UInt64) /- &AP_Mission::_storage -/ (Int16.toUInt16 (Int32.toInt16 (((UInt32.toInt32 (UInt16.toUInt32 (pos_in_storage))) + (3 : Int32))))) t'33
    let t'34 ← StorageAccess.write_block (0xbf28 : UInt64) /- &AP_Mission::_storage -/ (Int16.toUInt16 (Int32.toInt16 (((UInt32.toInt32 (UInt16.toUInt32 (pos_in_storage))) + (5 : Int32))))) (fp + 0) (Int64.toUInt64 (Int32.toInt64 ((10 : Int32))))
    discard <| pure (t'34)
  if ((UInt32.toInt32 (UInt16.toUInt32 (index))) != (0 : Int32)) then
    let t'35 := ((← PMem.clock) / 1000).toUInt32
    PMem.stU32 (this + 596) t'35
  return true

def AP_Mission.write_cmd_to_storage (this : UInt64) (index : UInt16) (cmd : UInt64) : PMem.M Bool := do
  let fp ← PMem.enter 12
  let r ← AP_Mission.write_cmd_to_storage.body fp this index cmd
  PMem.leave fp
  return r

/-- C++ `AP_Mission::get_singleton : AP_Mission *()`, `functor.h:500-503`. -/
def AP_Mission.get_singleton  : PMem.M UInt64 := do
  let t'1 ← PMem.ldU64 (0xbf20 : UInt64) /- &AP_Mission::_singleton -/
  return t'1

/-- C++ `AP::mission : AP_Mission &()`, `AP_Mission.cpp:3301-3304`. -/
def AP.mission  : PMem.M UInt64 := do
  let t'1 ← AP_Mission.get_singleton
  return t'1

/-- C++ `AP_Mission::num_commands : uint16_t () const`, `AP_Common.h:530-533`. -/
def AP_Mission.num_commands (this : UInt64) : PMem.M UInt16 := do
  let t'1 ← AP_ParamT'short_2.operator_const_short__ (this + 80)
  let t'2 ← PMem.ldI16 t'1
  return Int16.toUInt16 (t'2)

/-- C++ `AP_Mission::get_command_id : uint16_t (uint16_t) const`, `AP_Mission.cpp:3058-3072`. -/
def AP_Mission.get_command_id.body (fp : UInt64) (this : UInt64) (index : UInt16) : PMem.M UInt16 := do
  let mut index := index
  let mut pos_in_storage : UInt16 := Int16.toUInt16 (Int32.toInt16 (((4 : Int32) + ((UInt32.toInt32 (UInt16.toUInt32 (index))) * (15 : Int32)))))
  let t'1 ← StorageAccess.read_block (0xbf28 : UInt64) /- &AP_Mission::_storage -/ (fp + 0) pos_in_storage (3 : UInt64)
  if !t'1 then
    return UInt32.toUInt16 ((0 : UInt32))
  PMem.stU16 (fp + 8) (Int16.toUInt16 (Int32.toInt16 ((0 : Int32))))
  let t'2 ← PMem.ldU8 ((fp + 0) + ((Int32.toInt64 ((0 : Int32))) * 1).toUInt64)
  let mut sc'4 := ((UInt32.toInt32 (UInt8.toUInt32 (t'2))) == (0 : Int32))
  if !sc'4 then
    let t'3 ← PMem.ldU8 ((fp + 0) + ((Int32.toInt64 ((0 : Int32))) * 1).toUInt64)
    sc'4 := ((UInt32.toInt32 (UInt8.toUInt32 (t'3))) == (1 : Int32))
  if sc'4 then
    let t'5 ← PMem.memcpy (fp + 8) ((fp + 0) + ((Int32.toInt64 ((1 : Int32))) * 1).toUInt64) (Int64.toUInt64 (Int32.toInt64 ((2 : Int32))))
    discard <| pure (t'5)
  else
    let t'6 ← PMem.ldU8 ((fp + 0) + ((Int32.toInt64 ((0 : Int32))) * 1).toUInt64)
    let t'7 := UInt8.toUInt16 (t'6)
    PMem.stU16 (fp + 8) t'7
  let t'8 ← PMem.ldU16 (fp + 8)
  return t'8

def AP_Mission.get_command_id (this : UInt64) (index : UInt16) : PMem.M UInt16 := do
  let fp ← PMem.enter 10
  let r ← AP_Mission.get_command_id.body fp this index
  PMem.leave fp
  return r

/-- C++ `AP_Mission::option_is_set : bool (Option) const`, `sitl.h:780-782`. -/
def AP_Mission.option_is_set (this : UInt64) (option : Int32) : PMem.M Bool := do
  let mut option := option
  let t'1 ← AP_ParamTBase'unsigned_short_2.get (this + 82)
  let t'2 ← PMem.ldU16 t'1
  return (((UInt32.toInt32 (UInt16.toUInt32 (t'2))) &&& (UInt32.toInt32 (UInt16.toUInt32 ((Int16.toUInt16 (Int32.toInt16 (option))))))) != (0 : Int32))

/-- C++ `AP_Mission::format_conversion : void (uint8_t, const Mission_Command &, PackedContent &) const`, `AP_Mission.cpp:3248-3269`. -/
def AP_Mission.format_conversion (this : UInt64) (tag_byte : UInt8) (cmd : UInt64) (packed_content : UInt64) : PMem.M Unit := do
  let mut tag_byte := tag_byte
  let mut sc'4 := ((UInt32.toInt32 (UInt8.toUInt32 (tag_byte))) == (0 : Int32))
  if sc'4 then
    let t'1 ← PMem.ldU16 (cmd + 2)
    let mut sc'3 := ((UInt32.toInt32 (UInt16.toUInt32 (t'1))) == (UInt32.toInt32 ((2500 : UInt32))))
    if !sc'3 then
      let t'2 ← PMem.ldU16 (cmd + 2)
      sc'3 := ((UInt32.toInt32 (UInt16.toUInt32 (t'2))) == (UInt32.toInt32 ((2501 : UInt32))))
    sc'4 := sc'3
  if sc'4 then
    let t'5 ← PMem.memset (packed_content + ((Int32.toInt64 ((1 : Int32))) * 1).toUInt64) (0 : Int32) ((12 : UInt64) - (Int64.toUInt64 (Int32.toInt64 ((1 : Int32)))))
    discard <| pure (t'5)
  return ()

/-- C++ `AP_Mission::get_jump_times_run : int16_t (const Mission_Command &)`, `AP_Mission.cpp:2460-2483`. -/
def AP_Mission.get_jump_times_run (this : UInt64) (cmd : UInt64) : PMem.M Int16 := do
  let t'1 ← PMem.ldU16 (cmd + 2)
  let mut sc'5 := ((UInt32.toInt32 (UInt16.toUInt32 (t'1))) != (UInt32.toInt32 ((177 : UInt32))))
  if !sc'5 then
    let t'2 ← PMem.ldU16 (cmd + 8)
    let t'3 ← AP_ParamT'short_2.operator_const_short__ (this + 80)
    let t'4 ← PMem.ldI16 t'3
    sc'5 := (decide ((UInt16.toUInt32 (t'2)) ≥ (Int32.toUInt32 (Int16.toInt32 (t'4)))))
  let mut sc'7 := sc'5
  if !sc'7 then
    let t'6 ← PMem.ldU16 (cmd + 8)
    sc'7 := ((UInt32.toInt32 (UInt16.toUInt32 (t'6))) == (0 : Int32))
  if sc'7 then
    return Int32.toInt16 ((32767 : Int32))
  for i'8 in [0:100] do
    let i : UInt8 := UInt8.ofNat i'8
    let t'9 ← PMem.ldU16 ((this + 196) + ((UInt64.toInt64 (UInt8.toUInt64 (i))) * 4).toUInt64)
    let t'10 ← PMem.ldU16 cmd
    if ((UInt32.toInt32 (UInt16.toUInt32 (t'9))) == (UInt32.toInt32 (UInt16.toUInt32 (t'10)))) then
      let t'11 ← PMem.ldI16 (((this + 196) + ((UInt64.toInt64 (UInt8.toUInt64 (i))) * 4).toUInt64) + 2)
      return t'11
    else
      let t'12 ← PMem.ldU16 ((this + 196) + ((UInt64.toInt64 (UInt8.toUInt64 (i))) * 4).toUInt64)
      if ((UInt32.toInt32 (UInt16.toUInt32 (t'12))) == (65535 : Int32)) then
        let t'13 ← PMem.ldU16 cmd
        PMem.stU16 ((this + 196) + ((UInt64.toInt64 (UInt8.toUInt64 (i))) * 4).toUInt64) t'13
        let t'14 := Int32.toInt16 ((0 : Int32))
        PMem.stI16 (((this + 196) + ((UInt64.toInt64 (UInt8.toUInt64 (i))) * 4).toUInt64) + 2) t'14
        return Int32.toInt16 ((0 : Int32))
  return Int32.toInt16 ((32767 : Int32))

/-- `AP_Mission.is_landing_type_cmd` as a pure function of its arguments (it reads and writes no memory). -/
def AP_Mission.is_landing_type_cmd.pure' (this : UInt64) (id : UInt16) : Id Bool := do
  let mut id := id
  let sw'1 := UInt32.toInt32 (UInt16.toUInt32 (id))
  if sw'1 == (21 : Int32) || sw'1 == (85 : Int32) || sw'1 == (208 : Int32) then
    return true
  else
    return false

/-- C++ `AP_Mission::is_landing_type_cmd : bool (uint16_t) const`, `AP_Mission.cpp:2880-2890`. -/
def AP_Mission.is_landing_type_cmd (this : UInt64) (id : UInt16) : PMem.M Bool :=
  pure (_root_.Vehicle_lib.AP_Mission.is_landing_type_cmd.pure' this id)

/-- C++ `AP_Mission::init_jump_tracking : void ()`, `AP_Mission.cpp:2451-2457`. -/
def AP_Mission.init_jump_tracking (this : UInt64) : PMem.M Unit := do
  for i'1 in [0:100] do
    let i : UInt8 := UInt8.ofNat i'1
    let t'2 := Int16.toUInt16 (Int32.toInt16 ((65535 : Int32)))
    PMem.stU16 ((this + 196) + ((UInt64.toInt64 (UInt8.toUInt64 (i))) * 4).toUInt64) t'2
    let t'3 := Int32.toInt16 ((0 : Int32))
    PMem.stI16 (((this + 196) + ((UInt64.toInt64 (UInt8.toUInt64 (i))) * 4).toUInt64) + 2) t'3
  return ()

/-- C++ `AP_Mission::reset_wp_history : void ()`, `AP_Mission.cpp:3136-3144`. -/
def AP_Mission.reset_wp_history (this : UInt64) : PMem.M Unit := do
  for i'1 in [0:7] do
    let i : UInt8 := UInt8.ofNat i'1
    let t'2 := Int16.toUInt16 (Int32.toInt16 ((65535 : Int32)))
    PMem.stU16 ((this + 16) + ((UInt64.toInt64 (UInt8.toUInt64 (i))) * 2).toUInt64) t'2
  let t'3 := Int16.toUInt16 (Int32.toInt16 ((65535 : Int32)))
  PMem.stU16 (this + 144) t'3
  PMem.stB ((this + 4) + 8) false
  let t'4 := Int16.toUInt16 (Int32.toInt16 ((0 : Int32)))
  PMem.stU16 (this + 86) t'4
  return ()

/-- C++ `AP_Mission::is_nav_cmd : bool (const Mission_Command &)`, `AP_Mission.cpp:551-558`. -/
def AP_Mission.is_nav_cmd (cmd : UInt64) : PMem.M Bool := do
  let t'1 ← PMem.ldU16 (cmd + 2)
  let mut sc'3 := (decide ((UInt32.toInt32 (UInt16.toUInt32 (t'1))) ≤ (UInt32.toInt32 ((95 : UInt32)))))
  if !sc'3 then
    let t'2 ← PMem.ldU16 (cmd + 2)
    sc'3 := ((UInt32.toInt32 (UInt16.toUInt32 (t'2))) == (UInt32.toInt32 ((213 : UInt32))))
  let mut sc'5 := sc'3
  if !sc'5 then
    let t'4 ← PMem.ldU16 (cmd + 2)
    sc'5 := ((UInt32.toInt32 (UInt16.toUInt32 (t'4))) == (UInt32.toInt32 ((42702 : UInt32))))
  let mut sc'7 := sc'5
  if !sc'7 then
    let t'6 ← PMem.ldU16 (cmd + 2)
    sc'7 := ((UInt32.toInt32 (UInt16.toUInt32 (t'6))) == (UInt32.toInt32 ((42703 : UInt32))))
  return sc'7

/-- `AP_Mission.is_takeoff_type_cmd` as a pure function of its arguments (it reads and writes no memory). -/
def AP_Mission.is_takeoff_type_cmd.pure' (this : UInt64) (id : UInt16) : Id Bool := do
  let mut id := id
  let sw'1 := UInt32.toInt32 (UInt16.toUInt32 (id))
  if sw'1 == (22 : Int32) || sw'1 == (84 : Int32) then
    return true
  else
    return false

/-- C++ `AP_Mission::is_takeoff_type_cmd : bool (uint16_t) const`, `AP_Mission.cpp:2893-2902`. -/
def AP_Mission.is_takeoff_type_cmd (this : UInt64) (id : UInt16) : PMem.M Bool :=
  pure (_root_.Vehicle_lib.AP_Mission.is_takeoff_type_cmd.pure' this id)

/-- C++ `AP_Mission::Mission_Command::type : const char *() const`, `AP_Mission.cpp:2904-3053`. -/
def AP_Mission.Mission_Command.type (this : UInt64) : PMem.M UInt64 := do
  let t'1 ← PMem.ldU16 (this + 2)
  let sw'2 := UInt32.toInt32 (UInt16.toUInt32 (t'1))
  if sw'2 == (16 : Int32) then
    return (0x174eb : UInt64) /- "WP" -/
  else if sw'2 == (82 : Int32) then
    return (0x174ee : UInt64) /- "SplineWP" -/
  else if sw'2 == (36 : Int32) then
    return (0x174f7 : UInt64) /- "ArcWP" -/
  else if sw'2 == (20 : Int32) then
    return (0x14c9a : UInt64) /- "RTL" -/
  else if sw'2 == (17 : Int32) then
    return (0x174fd : UInt64) /- "LoitUnlim" -/
  else if sw'2 == (19 : Int32) then
    return (0x17507 : UInt64) /- "LoitTime" -/
  else if sw'2 == (92 : Int32) then
    return (0x17510 : UInt64) /- "GuidedEnable" -/
  else if sw'2 == (18 : Int32) then
    return (0x1751d : UInt64) /- "LoitTurns" -/
  else if sw'2 == (31 : Int32) then
    return (0x17527 : UInt64) /- "LoitAltitude" -/
  else if sw'2 == (213 : Int32) then
    return (0x17534 : UInt64) /- "SetYawSpd" -/
  else if sw'2 == (112 : Int32) then
    return (0x1753e : UInt64) /- "CondDelay" -/
  else if sw'2 == (114 : Int32) then
    return (0x17548 : UInt64) /- "CondDist" -/
  else if sw'2 == (178 : Int32) then
    return (0x17551 : UInt64) /- "ChangeSpeed" -/
  else if sw'2 == (179 : Int32) then
    return (0x1755d : UInt64) /- "SetHome" -/
  else if sw'2 == (183 : Int32) then
    return (0x17565 : UInt64) /- "SetServo" -/
  else if sw'2 == (181 : Int32) then
    return (0x1756e : UInt64) /- "SetRelay" -/
  else if sw'2 == (184 : Int32) then
    return (0x17577 : UInt64) /- "RepeatServo" -/
  else if sw'2 == (182 : Int32) then
    return (0x17583 : UInt64) /- "RepeatRelay" -/
  else if sw'2 == (202 : Int32) then
    return (0x1758f : UInt64) /- "DigiCamCfg" -/
  else if sw'2 == (203 : Int32) then
    return (0x1759a : UInt64) /- "DigiCamCtrl" -/
  else if sw'2 == (206 : Int32) then
    return (0x175a6 : UInt64) /- "SetCamTrigDst" -/
  else if sw'2 == (195 : Int32) then
    return (0x175b4 : UInt64) /- "SetROILocation" -/
  else if sw'2 == (197 : Int32) then
    return (0x175c3 : UInt64) /- "SetROINone" -/
  else if sw'2 == (201 : Int32) then
    return (0x175ce : UInt64) /- "SetROI" -/
  else if sw'2 == (194 : Int32) then
    return (0x175d5 : UInt64) /- "SetReverse" -/
  else if sw'2 == (215 : Int32) then
    return (0x175e0 : UInt64) /- "SetRepeatDist" -/
  else if sw'2 == (222 : Int32) then
    return (0x175ee : UInt64) /- "GuidedLimits" -/
  else if sw'2 == (22 : Int32) then
    return (0x175fb : UInt64) /- "Takeoff" -/
  else if sw'2 == (21 : Int32) then
    return (0x14b4c : UInt64) /- "Land" -/
  else if sw'2 == (30 : Int32) then
    return (0x17603 : UInt64) /- "ContinueAndChangeAlt" -/
  else if sw'2 == (83 : Int32) then
    return (0x17618 : UInt64) /- "AltitudeWait" -/
  else if sw'2 == (84 : Int32) then
    return (0x17625 : UInt64) /- "VTOLTakeoff" -/
  else if sw'2 == (85 : Int32) then
    return (0x17631 : UInt64) /- "VTOLLand" -/
  else if sw'2 == (210 : Int32) then
    return (0x1763a : UInt64) /- "InvertedFlight" -/
  else if sw'2 == (207 : Int32) then
    return (0x17649 : UInt64) /- "FenceEnable" -/
  else if sw'2 == (212 : Int32) then
    return (0x17655 : UInt64) /- "AutoTuneEnable" -/
  else if sw'2 == (3000 : Int32) then
    return (0x17664 : UInt64) /- "VTOLTransition" -/
  else if sw'2 == (223 : Int32) then
    return (0x17673 : UInt64) /- "EngineControl" -/
  else if sw'2 == (115 : Int32) then
    return (0x17681 : UInt64) /- "CondYaw" -/
  else if sw'2 == (188 : Int32) then
    return (0x17689 : UInt64) /- "ReturnPathStart" -/
  else if sw'2 == (189 : Int32) then
    return (0x17699 : UInt64) /- "LandStart" -/
  else if sw'2 == (93 : Int32) then
    return (0x176a3 : UInt64) /- "Delay" -/
  else if sw'2 == (208 : Int32) then
    return (0x176a9 : UInt64) /- "Parachute" -/
  else if sw'2 == (216 : Int32) then
    return (0x176b3 : UInt64) /- "Sprayer" -/
  else if sw'2 == (218 : Int32) then
    return (0x176bb : UInt64) /- "AuxFunction" -/
  else if sw'2 == (205 : Int32) then
    return (0x176c7 : UInt64) /- "MountControl" -/
  else if sw'2 == (42600 : Int32) then
    return (0x176d4 : UInt64) /- "Winch" -/
  else if sw'2 == (217 : Int32) then
    return (0x176da : UInt64) /- "Scripting" -/
  else if sw'2 == (177 : Int32) then
    return (0x176e4 : UInt64) /- "Jump" -/
  else if sw'2 == (601 : Int32) then
    return (0x176e9 : UInt64) /- "JumpToTag" -/
  else if sw'2 == (600 : Int32) then
    return (0x176f3 : UInt64) /- "Tag" -/
  else if sw'2 == (191 : Int32) then
    return (0x176f7 : UInt64) /- "Go Around" -/
  else if sw'2 == (42703 : Int32) then
    return (0x17701 : UInt64) /- "NavAttitudeTime" -/
  else if sw'2 == (193 : Int32) then
    return (0x17711 : UInt64) /- "PauseContinue" -/
  else if sw'2 == (1000 : Int32) then
    return (0x1771f : UInt64) /- "GimbalPitchYaw" -/
  else if sw'2 == (2000 : Int32) then
    return (0x1772e : UInt64) /- "ImageStartCapture" -/
  else if sw'2 == (2001 : Int32) then
    return (0x17740 : UInt64) /- "ImageStopCapture" -/
  else if sw'2 == (531 : Int32) then
    return (0x17751 : UInt64) /- "SetCameraZoom" -/
  else if sw'2 == (532 : Int32) then
    return (0x1775f : UInt64) /- "SetCameraFocus" -/
  else if sw'2 == (534 : Int32) then
    return (0x1776e : UInt64) /- "SetCameraSource" -/
  else if sw'2 == (2500 : Int32) then
    return (0x1777e : UInt64) /- "VideoStartCapture" -/
  else if sw'2 == (2501 : Int32) then
    return (0x17790 : UInt64) /- "VideoStopCapture" -/
  else if sw'2 == (196 : Int32) then
    return (0x177a1 : UInt64) /- "ROIWPNextOffset" -/
  else
    return (0x16088 : UInt64) /- "?" -/

/-- C++ `AP_Mission::present : bool () const`, `AP_Common.h:541-?`. -/
def AP_Mission.present (this : UInt64) : PMem.M Bool := do
  let t'1 ← AP_ParamT'short_2.operator_const_short__ (this + 80)
  let t'2 ← PMem.ldI16 t'1
  return (decide ((Int16.toInt32 (t'2)) > (1 : Int32)))

/-- C++ `AP_Mission::reset : void ()`, `AP_Mission.cpp:260-274`. -/
def AP_Mission.reset (this : UInt64) : PMem.M Unit := do
  PMem.stB ((this + 4) + 4) false
  PMem.stB ((this + 4) + 5) false
  PMem.stB ((this + 4) + 6) false
  PMem.stB ((this + 4) + 7) false
  PMem.stB ((this + 4) + 9) false
  let t'1 := Int16.toUInt16 (Int32.toInt16 ((65535 : Int32)))
  PMem.stU16 (this + 88) t'1
  let t'2 := Int16.toUInt16 (Int32.toInt16 ((65535 : Int32)))
  PMem.stU16 (this + 116) t'2
  let t'3 := Int16.toUInt16 (Int32.toInt16 ((65535 : Int32)))
  PMem.stU16 (this + 174) t'3
  let t'4 := Int16.toUInt16 (Int32.toInt16 ((65535 : Int32)))
  PMem.stU16 (this + 176) t'4
  let t'5 := Int16.toUInt16 (Int32.toInt16 ((0 : Int32)))
  PMem.stU16 (this + 172) t'5
  AP_Mission.init_jump_tracking this
  AP_Mission.reset_wp_history this
  return ()

/-- C++ `AP_Mission::failed_sdcard_storage : bool () const`, `sitl.h:814-816`. -/
def AP_Mission.failed_sdcard_storage (this : UInt64) : PMem.M Bool := do
  let t'1 ← PMem.ldB (this + 606)
  return t'1

/-- `AP_Mission.start_command_parachute` as a pure function of its arguments (it reads and writes no memory). -/
def AP_Mission.start_command_parachute.pure' (this : UInt64) (cmd : UInt64) : Id Bool := do
  return false

/-- C++ `AP_Mission::start_command_parachute : bool (const AP_Mission::Mission_Command &)`, `AP_Mission_Commands.cpp:131-158`. -/
def AP_Mission.start_command_parachute (this : UInt64) (cmd : UInt64) : PMem.M Bool :=
  pure (_root_.Vehicle_lib.AP_Mission.start_command_parachute.pure' this cmd)

/-- `AP_Mission.start_command_do_scripting` as a pure function of its arguments (it reads and writes no memory). -/
def AP_Mission.start_command_do_scripting.pure' (this : UInt64) (cmd : UInt64) : Id Bool := do
  return false

/-- C++ `AP_Mission::start_command_do_scripting : bool (const AP_Mission::Mission_Command &)`, `AP_Mission_Commands.cpp:187-201`. -/
def AP_Mission.start_command_do_scripting (this : UInt64) (cmd : UInt64) : PMem.M Bool :=
  pure (_root_.Vehicle_lib.AP_Mission.start_command_do_scripting.pure' this cmd)

/-- `AP_Mission.start_command_do_sprayer` as a pure function of its arguments (it reads and writes no memory). -/
def AP_Mission.start_command_do_sprayer.pure' (this : UInt64) (cmd : UInt64) : Id Bool := do
  return false

/-- C++ `AP_Mission::start_command_do_sprayer : bool (const AP_Mission::Mission_Command &)`, `AP_Mission_Commands.cpp:167-185`. -/
def AP_Mission.start_command_do_sprayer (this : UInt64) (cmd : UInt64) : PMem.M Bool :=
  pure (_root_.Vehicle_lib.AP_Mission.start_command_do_sprayer.pure' this cmd)

/-- `AP_Mission.start_command_do_gimbal_manager_pitchyaw` as a pure function of its arguments (it reads and writes no memory). -/
def AP_Mission.start_command_do_gimbal_manager_pitchyaw.pure' (this : UInt64) (cmd : UInt64) : Id Bool := do
  return false

/-- C++ `AP_Mission::start_command_do_gimbal_manager_pitchyaw : bool (const AP_Mission::Mission_Command &)`, `AP_Mission_Commands.cpp:203-244`. -/
def AP_Mission.start_command_do_gimbal_manager_pitchyaw (this : UInt64) (cmd : UInt64) : PMem.M Bool :=
  pure (_root_.Vehicle_lib.AP_Mission.start_command_do_gimbal_manager_pitchyaw.pure' this cmd)

/-- `AP_Mission.start_command_do_set_roi` as a pure function of its arguments (it reads and writes no memory). -/
def AP_Mission.start_command_do_set_roi.pure' (this : UInt64) (cmd : UInt64) : Id Bool := do
  return false

/-- C++ `AP_Mission::start_command_do_set_roi : bool (const AP_Mission::Mission_Command &)`, `AP_Mission_Commands.cpp:246-263`. -/
def AP_Mission.start_command_do_set_roi (this : UInt64) (cmd : UInt64) : PMem.M Bool :=
  pure (_root_.Vehicle_lib.AP_Mission.start_command_do_set_roi.pure' this cmd)

/-- `AP_Mission.start_command_do_set_roi_wpnext_offset` as a pure function of its arguments (it reads and writes no memory). -/
def AP_Mission.start_command_do_set_roi_wpnext_offset.pure' (this : UInt64) (cmd : UInt64) : Id Bool := do
  return false

/-- C++ `AP_Mission::start_command_do_set_roi_wpnext_offset : bool (const AP_Mission::Mission_Command &)`, `AP_Mission_Commands.cpp:294-316`. -/
def AP_Mission.start_command_do_set_roi_wpnext_offset (this : UInt64) (cmd : UInt64) : PMem.M Bool :=
  pure (_root_.Vehicle_lib.AP_Mission.start_command_do_set_roi_wpnext_offset.pure' this cmd)

/-- `AP_Mission.cmd_has_location` as a pure function of its arguments (it reads and writes no memory). -/
def AP_Mission.cmd_has_location.pure' (command : UInt16) : Id Bool := do
  let mut command := command
  let t'1 ← _root_.Vehicle_lib.AP_Mission.stored_in_location.pure' command
  return t'1

/-- C++ `AP_Mission::cmd_has_location : bool (const uint16_t)`, `AP_Mission.cpp:3100-3103`. -/
def AP_Mission.cmd_has_location (command : UInt16) : PMem.M Bool :=
  pure (_root_.Vehicle_lib.AP_Mission.cmd_has_location.pure' command)

/-- C++ `AP_Mission::Mission_Command::get_arc_angle_rad : float () const`, `AP_Common.h:464-467`. -/
def AP_Mission.Mission_Command.get_arc_angle_rad (this : UInt64) : PMem.M Binary32 := do
  let t'1 ← PMem.ldBits (this + 8) 1 1
  let mut c'2 : Binary32 := default
  if ((UInt32.toInt32 (UInt8.toUInt32 ((UInt64.toUInt8 (t'1))))) == (0 : Int32)) then
    c'2 := (Binary32.ofBits 0x3f800000 /- 1 -/)
  else
    c'2 := -(Binary32.ofBits 0x3f800000 /- 1 -/)
  let mut sign : Binary32 := c'2
  let t'3 ← PMem.ldU16 (this + 4)
  let t'4 ← radians ((UInt16.toBinary32 (t'3)) * sign)
  return t'4

/-- C++ `AP_Mission::Mission_Command::get_loiter_turns : float () const`, `AP_Common.h:451-458`. -/
def AP_Mission.Mission_Command.get_loiter_turns (this : UInt64) : PMem.M Binary32 := do
  let t'1 ← PMem.ldU16 (this + 4)
  let mut turns : Binary32 := UInt8.toBinary32 ((UInt16.toUInt8 (t'1)))
  let t'2 ← PMem.ldU8 (this + 24)
  if ((UInt8.toUInt32 (t'2)) &&& ((1 : UInt32) <<< (Int32.toUInt32 ((1 : Int32))))) != (0 : UInt32) then
    let t'3 := (turns * ((Binary64.toBinary32 ((Binary64.ofBits 0x3ff0000000000000 /- 1 -/))) / (Binary64.toBinary32 ((Binary64.ofBits 0x4070000000000000 /- 256 -/)))))
    turns := t'3
  return turns

/-- C++ `AP_Mission::state : mission_state () const`, `AP_Common.h:523-526`. -/
def AP_Mission.state (this : UInt64) : PMem.M UInt32 := do
  let t'1 ← PMem.ldU32 (this + 4)
  return t'1

/-- C++ `AP_Mission::set_force_resume : void (bool)`, `AP_Common.h:741-744`. -/
def AP_Mission.set_force_resume (this : UInt64) (force_resume : Bool) : PMem.M Unit := do
  let mut force_resume := force_resume
  PMem.stB (this + 85) force_resume
  return ()

/-- C++ `AP_Mission::stop : void ()`, `AP_Mission.cpp:123-126`. -/
def AP_Mission.stop (this : UInt64) : PMem.M Unit := do
  PMem.stU32 (this + 4) (0 : UInt32)
  return ()

/-- C++ `AP_Mission::last_change_time_ms : uint32_t () const`, `AP_Common.h:694-697`. -/
def AP_Mission.last_change_time_ms (this : UInt64) : PMem.M UInt32 := do
  let t'1 ← PMem.ldU32 (this + 596)
  return t'1

/-- C++ `AP_Mission::get_current_nav_index : uint16_t () const`, `AP_Common.h:605-608`. -/
def AP_Mission.get_current_nav_index (this : UInt64) : PMem.M UInt16 := do
  let t'1 ← PMem.ldU16 (this + 88)
  let mut c'2 : Int32 := default
  if ((UInt32.toInt32 (UInt16.toUInt32 (t'1))) == (65535 : Int32)) then
    c'2 := (0 : Int32)
  else
    let t'3 ← PMem.ldU16 (this + 88)
    c'2 := UInt32.toInt32 (UInt16.toUInt32 (t'3))
  return Int16.toUInt16 (Int32.toInt16 (c'2))

/-- C++ `AP_Mission::Mission_Command::operator== : bool (const Mission_Command &) const`, `AP_Common.h:444-?`. -/
def AP_Mission.Mission_Command.operator__'2 (this : UInt64) (b : UInt64) : PMem.M Bool := do
  let t'1 ← PMem.memcmp this b (28 : UInt64)
  return (t'1 == (0 : Int32))

/-- C++ `AP_Mission::Mission_Command::operator!= : bool (const Mission_Command &) const`, `AP_Common.h:445-?`. -/
def AP_Mission.Mission_Command.operator__ (this : UInt64) (b : UInt64) : PMem.M Bool := do
  let t'1 ← AP_Mission.Mission_Command.operator__'2 this b
  return !t'1

/-- C++ `AP_Mission::convert_MISSION_ITEM_to_MISSION_ITEM_INT : MAV_MISSION_RESULT (const mavlink_mission_item_t &, mavlink_mission_item_int_t &)`, `AP_Mission.cpp:1614-1658`. -/
def AP_Mission.convert_MISSION_ITEM_to_MISSION_ITEM_INT (packet : UInt64) (mav_cmd : UInt64) : PMem.M UInt32 := do
  let t'1 ← PMem.ldF32 packet
  PMem.stF32 mav_cmd t'1
  let t'2 ← PMem.ldF32 (packet + 4)
  PMem.stF32 (mav_cmd + 4) t'2
  let t'3 ← PMem.ldF32 (packet + 8)
  PMem.stF32 (mav_cmd + 8) t'3
  let t'4 ← PMem.ldF32 (packet + 12)
  PMem.stF32 (mav_cmd + 12) t'4
  let t'5 ← PMem.ldF32 (packet + 24)
  PMem.stF32 (mav_cmd + 24) t'5
  let t'6 ← PMem.ldU16 (packet + 28)
  PMem.stU16 (mav_cmd + 28) t'6
  let t'7 ← PMem.ldU16 (packet + 30)
  PMem.stU16 (mav_cmd + 30) t'7
  let t'8 ← PMem.ldU8 (packet + 32)
  PMem.stU8 (mav_cmd + 32) t'8
  let t'9 ← PMem.ldU8 (packet + 33)
  PMem.stU8 (mav_cmd + 33) t'9
  let t'10 ← PMem.ldU8 (packet + 34)
  PMem.stU8 (mav_cmd + 34) t'10
  let t'11 ← PMem.ldU8 (packet + 35)
  PMem.stU8 (mav_cmd + 35) t'11
  let t'12 ← PMem.ldU8 (packet + 36)
  PMem.stU8 (mav_cmd + 36) t'12
  let t'13 ← PMem.ldU8 (packet + 37)
  PMem.stU8 (mav_cmd + 37) t'13
  let t'14 ← PMem.ldU16 (packet + 30)
  let t'15 ← AP_Mission.cmd_has_location t'14
  if !t'15 then
    let t'16 ← PMem.ldF32 (packet + 16)
    let t'17 := Binary32.toInt32 (t'16)
    PMem.stI32 (mav_cmd + 16) t'17
    let t'18 ← PMem.ldF32 (packet + 20)
    let t'19 := Binary32.toInt32 (t'18)
    PMem.stI32 (mav_cmd + 20) t'19
  else
    let t'20 ← PMem.ldF32 (packet + 16)
    let t'21 ← check_lat'2 t'20
    if !t'21 then
      return (10 : UInt32)
    let t'22 ← PMem.ldF32 (packet + 20)
    let t'23 ← check_lng'2 t'22
    if !t'23 then
      return (11 : UInt32)
    let t'24 ← PMem.ldF32 (packet + 16)
    let t'25 := Binary32.toInt32 ((t'24 * (Binary32.ofBits 0x4b189680 /- 10000000 -/)))
    PMem.stI32 (mav_cmd + 16) t'25
    let t'26 ← PMem.ldF32 (packet + 20)
    let t'27 := Binary32.toInt32 ((t'26 * (Binary32.ofBits 0x4b189680 /- 10000000 -/)))
    PMem.stI32 (mav_cmd + 20) t'27
  return (0 : UInt32)

/-- C++ `AP_Mission::sanity_check_params : MAV_MISSION_RESULT (const mavlink_mission_item_int_t &)`, `AP_Mission.cpp:1024-1071`. -/
def AP_Mission.sanity_check_params (packet : UInt64) : PMem.M UInt32 := do
  let mut nan_mask : UInt8 := default  -- uninitialized in C
  let t'1 ← PMem.ldU16 (packet + 30)
  let sw'2 := UInt32.toInt32 (UInt16.toUInt32 (t'1))
  if sw'2 == (16 : Int32) then
    let t'3 := Int8.toUInt8 (Int32.toInt8 ((~~~((1 : Int32) <<< (3 : Int32)))))
    nan_mask := t'3
  else if sw'2 == (17 : Int32) then
    let t'4 := Int8.toUInt8 (Int32.toInt8 ((~~~((1 : Int32) <<< (3 : Int32)))))
    nan_mask := t'4
  else if sw'2 == (21 : Int32) then
    let t'5 := Int8.toUInt8 (Int32.toInt8 ((~~~((1 : Int32) <<< (3 : Int32)))))
    nan_mask := t'5
  else if sw'2 == (22 : Int32) then
    let t'6 := Int8.toUInt8 (Int32.toInt8 ((~~~((1 : Int32) <<< (3 : Int32)))))
    nan_mask := t'6
  else if sw'2 == (36 : Int32) then
    let t'7 := Int8.toUInt8 (Int32.toInt8 ((~~~((((1 : Int32) <<< (1 : Int32)) ||| ((1 : Int32) <<< (2 : Int32))) ||| ((1 : Int32) <<< (3 : Int32))))))
    nan_mask := t'7
  else if sw'2 == (84 : Int32) then
    let t'8 := Int8.toUInt8 (Int32.toInt8 ((~~~((1 : Int32) <<< (3 : Int32)))))
    nan_mask := t'8
  else if sw'2 == (85 : Int32) then
    let t'9 := Int8.toUInt8 (Int32.toInt8 ((~~~(((1 : Int32) <<< (2 : Int32)) ||| ((1 : Int32) <<< (3 : Int32))))))
    nan_mask := t'9
  else
    let t'10 := Int8.toUInt8 (Int32.toInt8 ((255 : Int32)))
    nan_mask := t'10
  let mut sc'12 := ((UInt32.toInt32 (UInt8.toUInt32 (nan_mask))) &&& ((1 : Int32) <<< (0 : Int32))) != (0 : Int32)
  if sc'12 then
    let t'11 ← PMem.ldF32 packet
    sc'12 := (Binary32.isNaN t'11)
  let mut sc'14 := sc'12
  if !sc'14 then
    let t'13 ← PMem.ldF32 packet
    sc'14 := (Binary32.isInf t'13)
  if sc'14 then
    return (6 : UInt32)
  let mut sc'16 := ((UInt32.toInt32 (UInt8.toUInt32 (nan_mask))) &&& ((1 : Int32) <<< (1 : Int32))) != (0 : Int32)
  if sc'16 then
    let t'15 ← PMem.ldF32 (packet + 4)
    sc'16 := (Binary32.isNaN t'15)
  let mut sc'18 := sc'16
  if !sc'18 then
    let t'17 ← PMem.ldF32 (packet + 4)
    sc'18 := (Binary32.isInf t'17)
  if sc'18 then
    return (7 : UInt32)
  let mut sc'20 := ((UInt32.toInt32 (UInt8.toUInt32 (nan_mask))) &&& ((1 : Int32) <<< (2 : Int32))) != (0 : Int32)
  if sc'20 then
    let t'19 ← PMem.ldF32 (packet + 8)
    sc'20 := (Binary32.isNaN t'19)
  let mut sc'22 := sc'20
  if !sc'22 then
    let t'21 ← PMem.ldF32 (packet + 8)
    sc'22 := (Binary32.isInf t'21)
  if sc'22 then
    return (8 : UInt32)
  let mut sc'24 := ((UInt32.toInt32 (UInt8.toUInt32 (nan_mask))) &&& ((1 : Int32) <<< (3 : Int32))) != (0 : Int32)
  if sc'24 then
    let t'23 ← PMem.ldF32 (packet + 12)
    sc'24 := (Binary32.isNaN t'23)
  let mut sc'26 := sc'24
  if !sc'26 then
    let t'25 ← PMem.ldF32 (packet + 12)
    sc'26 := (Binary32.isInf t'25)
  if sc'26 then
    return (9 : UInt32)
  return (0 : UInt32)

/-- C++ `AP_Mission::replace_cmd : bool (uint16_t, const Mission_Command &)`, `AP_Mission.cpp:533-548`. -/
def AP_Mission.replace_cmd (this : UInt64) (index : UInt16) (cmd : UInt64) : PMem.M Bool := do
  let mut index := index
  let t'1 ← AP_ParamT'short_2.operator_const_short__ (this + 80)
  let t'2 ← PMem.ldI16 t'1
  if (decide ((UInt16.toUInt32 (index)) ≥ (Int32.toUInt32 (Int16.toInt32 (t'2))))) then
    return false
  if ((UInt32.toInt32 (UInt16.toUInt32 (index))) == (0 : Int32)) then
    return true
  let t'3 ← AP_Mission.write_cmd_to_storage this index cmd
  return t'3

/-- C++ `AP_Mission::mission_cmd_to_mavlink_int : bool (const AP_Mission::Mission_Command &, mavlink_mission_item_int_t &)`, `AP_Mission.cpp:1700-2135`. -/
def AP_Mission.mission_cmd_to_mavlink_int.body (fp : UInt64) (cmd : UInt64) (packet : UInt64) : PMem.M Bool := do
  discard <| PMem.memset ((fp + 0) + 0) 0 4
  discard <| PMem.memset ((fp + 0) + 4) 0 4
  discard <| PMem.memset ((fp + 0) + 8) 0 4
  discard <| PMem.memset ((fp + 0) + 12) 0 4
  discard <| PMem.memset ((fp + 0) + 16) 0 4
  discard <| PMem.memset ((fp + 0) + 20) 0 4
  discard <| PMem.memset ((fp + 0) + 24) 0 4
  let t'1 ← PMem.ldU16 cmd
  PMem.stU16 ((fp + 0) + 28) t'1
  let t'2 ← PMem.ldU16 (cmd + 2)
  PMem.stU16 ((fp + 0) + 30) t'2
  discard <| PMem.memset ((fp + 0) + 32) 0 1
  discard <| PMem.memset ((fp + 0) + 33) 0 1
  discard <| PMem.memset ((fp + 0) + 34) 0 1
  discard <| PMem.memset ((fp + 0) + 35) 0 1
  PMem.stU8 ((fp + 0) + 36) (Int8.toUInt8 (Int32.toInt8 ((1 : Int32))))
  discard <| PMem.memset ((fp + 0) + 37) 0 1
  discard <| PMem.memcpy packet (fp + 0) 38
  discard <| pure (packet)
  for _ in [0:1] do
    let t'3 ← PMem.ldU16 (cmd + 2)
    let sw'4 := UInt32.toInt32 (UInt16.toUInt32 (t'3))
    if sw'4 == (0 : Int32) then
      return false
    else if sw'4 == (16 : Int32) then
      let t'5 ← PMem.ldU16 (cmd + 4)
      let t'6 := UInt16.toBinary32 (t'5)
      PMem.stF32 packet t'6
    else if sw'4 == (17 : Int32) then
      let t'7 ← PMem.ldU16 (cmd + 4)
      let t'8 := UInt16.toBinary32 (t'7)
      PMem.stF32 (packet + 8) t'8
      let t'9 ← PMem.ldBits (cmd + 8) 1 1
      if (UInt64.toUInt8 (t'9)) != (0 : UInt8) then
        let t'10 := (packet + 8)
        let t'11 ← PMem.ldF32 t'10
        let t'12 := (t'11 * (Int32.toBinary32 ((-(1 : Int32)))))
        PMem.stF32 t'10 t'12
    else if sw'4 == (18 : Int32) then
      let t'13 ← PMem.ldU16 (cmd + 4)
      let t'14 := UInt8.toBinary32 ((UInt16.toUInt8 (t'13)))
      PMem.stF32 packet t'14
      let t'15 ← PMem.ldU16 (cmd + 4)
      let t'16 := UInt8.toBinary32 ((Int8.toUInt8 (Int32.toInt8 (((UInt32.toInt32 (UInt16.toUInt32 (t'15))) >>> (8 : Int32))))))
      PMem.stF32 (packet + 8) t'16
      let t'17 ← PMem.ldBits (cmd + 8) 1 1
      if (UInt64.toUInt8 (t'17)) != (0 : UInt8) then
        let t'18 ← PMem.ldF32 (packet + 8)
        let t'19 := -t'18
        PMem.stF32 (packet + 8) t'19
      let t'20 ← PMem.ldU8 (cmd + 24)
      if ((UInt8.toUInt32 (t'20)) &&& ((1 : UInt32) <<< (Int32.toUInt32 ((0 : Int32))))) != (0 : UInt32) then
        let t'21 := (packet + 8)
        let t'22 ← PMem.ldF32 t'21
        let t'23 := (t'22 * (Int32.toBinary32 ((10 : Int32))))
        PMem.stF32 t'21 t'23
      let t'24 ← PMem.ldU8 (cmd + 24)
      if ((UInt8.toUInt32 (t'24)) &&& ((1 : UInt32) <<< (Int32.toUInt32 ((1 : Int32))))) != (0 : UInt32) then
        let t'25 ← PMem.ldF32 packet
        let t'26 := (t'25 / (Binary64.toBinary32 ((Binary64.ofBits 0x4070000000000000 /- 256 -/))))
        PMem.stF32 packet t'26
      let t'27 ← PMem.ldBits (cmd + 8) 4 1
      let t'28 := UInt8.toBinary32 ((UInt64.toUInt8 (t'27)))
      PMem.stF32 (packet + 12) t'28
    else if sw'4 == (19 : Int32) then
      let t'29 ← PMem.ldU16 (cmd + 4)
      let t'30 := UInt16.toBinary32 (t'29)
      PMem.stF32 packet t'30
      let t'31 ← PMem.ldBits (cmd + 8) 1 1
      if (UInt64.toUInt8 (t'31)) != (0 : UInt8) then
        let t'32 := Int32.toBinary32 ((-(1 : Int32)))
        PMem.stF32 (packet + 8) t'32
      else
        let t'33 := Int32.toBinary32 ((1 : Int32))
        PMem.stF32 (packet + 8) t'33
      let t'34 ← PMem.ldBits (cmd + 8) 4 1
      let t'35 := UInt8.toBinary32 ((UInt64.toUInt8 (t'34)))
      PMem.stF32 (packet + 12) t'35
    else if sw'4 == (20 : Int32) then
      pure ()
    else if sw'4 == (21 : Int32) then
      let t'36 ← PMem.ldU16 (cmd + 4)
      let t'37 := UInt16.toBinary32 (t'36)
      PMem.stF32 packet t'37
      let t'38 ← PMem.ldBits (cmd + 8) 1 1
      let mut c'39 : Int32 := default
      if (UInt64.toUInt8 (t'38)) != (0 : UInt8) then
        c'39 := -(1 : Int32)
      else
        c'39 := (1 : Int32)
      let t'40 := Int32.toBinary32 (c'39)
      PMem.stF32 (packet + 12) t'40
    else if sw'4 == (22 : Int32) then
      let t'41 ← PMem.ldU16 (cmd + 4)
      let t'42 := UInt16.toBinary32 (t'41)
      PMem.stF32 packet t'42
    else if sw'4 == (30 : Int32) then
      let t'43 ← PMem.ldU16 (cmd + 4)
      let t'44 := UInt16.toBinary32 (t'43)
      PMem.stF32 packet t'44
    else if sw'4 == (31 : Int32) then
      let t'45 ← PMem.ldU16 (cmd + 4)
      let t'46 := UInt16.toBinary32 (t'45)
      PMem.stF32 (packet + 4) t'46
      let t'47 ← PMem.ldBits (cmd + 8) 1 1
      if (UInt64.toUInt8 (t'47)) != (0 : UInt8) then
        let t'48 ← PMem.ldF32 (packet + 4)
        let t'49 := -t'48
        PMem.stF32 (packet + 4) t'49
      let t'50 ← PMem.ldBits (cmd + 8) 4 1
      let t'51 := UInt8.toBinary32 ((UInt64.toUInt8 (t'50)))
      PMem.stF32 (packet + 12) t'51
    else if sw'4 == (36 : Int32) then
      let t'52 ← PMem.ldBits (cmd + 8) 1 1
      let mut c'53 : Binary32 := default
      if ((UInt32.toInt32 (UInt8.toUInt32 ((UInt64.toUInt8 (t'52))))) == (0 : Int32)) then
        c'53 := Binary64.toBinary32 ((Binary64.ofBits 0x3ff0000000000000 /- 1 -/))
      else
        c'53 := -(Binary64.toBinary32 ((Binary64.ofBits 0x3ff0000000000000 /- 1 -/)))
      let mut sign : Binary32 := c'53
      let t'54 ← PMem.ldU16 (cmd + 4)
      let t'55 := ((UInt16.toBinary32 (t'54)) * sign)
      PMem.stF32 packet t'55
      break
      let t'56 ← PMem.ldU16 (cmd + 4)
      let t'57 := UInt16.toBinary32 (t'56)
      PMem.stF32 packet t'57
    else if sw'4 == (82 : Int32) then
      let t'58 ← PMem.ldU16 (cmd + 4)
      let t'59 := UInt16.toBinary32 (t'58)
      PMem.stF32 packet t'59
    else if sw'4 == (92 : Int32) then
      let t'60 ← PMem.ldU16 (cmd + 4)
      let t'61 := UInt16.toBinary32 (t'60)
      PMem.stF32 packet t'61
    else if sw'4 == (93 : Int32) then
      let t'62 ← PMem.ldF32 (cmd + 8)
      PMem.stF32 packet t'62
      let t'63 ← PMem.ldI8 ((cmd + 8) + 4)
      let t'64 := Int8.toBinary32 (t'63)
      PMem.stF32 (packet + 4) t'64
      let t'65 ← PMem.ldI8 ((cmd + 8) + 5)
      let t'66 := Int8.toBinary32 (t'65)
      PMem.stF32 (packet + 8) t'66
      let t'67 ← PMem.ldI8 ((cmd + 8) + 6)
      let t'68 := Int8.toBinary32 (t'67)
      PMem.stF32 (packet + 12) t'68
    else if sw'4 == (112 : Int32) then
      let t'69 ← PMem.ldF32 (cmd + 8)
      PMem.stF32 packet t'69
    else if sw'4 == (114 : Int32) then
      let t'70 ← PMem.ldF32 (cmd + 8)
      PMem.stF32 packet t'70
    else if sw'4 == (115 : Int32) then
      let t'71 ← PMem.ldF32 (cmd + 8)
      PMem.stF32 packet t'71
      let t'72 ← PMem.ldF32 ((cmd + 8) + 4)
      PMem.stF32 (packet + 4) t'72
      let t'73 ← PMem.ldI8 ((cmd + 8) + 8)
      let t'74 := Int8.toBinary32 (t'73)
      PMem.stF32 (packet + 8) t'74
      let t'75 ← PMem.ldU8 ((cmd + 8) + 9)
      let t'76 := UInt8.toBinary32 (t'75)
      PMem.stF32 (packet + 12) t'76
    else if sw'4 == (177 : Int32) || sw'4 == (601 : Int32) then
      let t'77 ← PMem.ldU16 (cmd + 8)
      let t'78 := UInt16.toBinary32 (t'77)
      PMem.stF32 packet t'78
      let t'79 ← PMem.ldI16 ((cmd + 8) + 2)
      let t'80 := Int16.toBinary32 (t'79)
      PMem.stF32 (packet + 4) t'80
    else if sw'4 == (600 : Int32) then
      let t'81 ← PMem.ldU16 (cmd + 8)
      let t'82 := UInt16.toBinary32 (t'81)
      PMem.stF32 packet t'82
    else if sw'4 == (178 : Int32) then
      let t'83 ← PMem.ldU8 (cmd + 8)
      let t'84 := UInt8.toBinary32 (t'83)
      PMem.stF32 packet t'84
      let t'85 ← PMem.ldF32 ((cmd + 8) + 1)
      PMem.stF32 (packet + 4) t'85
      let t'86 ← PMem.ldF32 ((cmd + 8) + 5)
      PMem.stF32 (packet + 8) t'86
    else if sw'4 == (179 : Int32) then
      let t'87 ← PMem.ldU16 (cmd + 4)
      let t'88 := UInt16.toBinary32 (t'87)
      PMem.stF32 packet t'88
    else if sw'4 == (181 : Int32) then
      let t'89 ← PMem.ldU8 (cmd + 8)
      let t'90 := UInt8.toBinary32 (t'89)
      PMem.stF32 packet t'90
      let t'91 ← PMem.ldU8 ((cmd + 8) + 1)
      let t'92 := UInt8.toBinary32 (t'91)
      PMem.stF32 (packet + 4) t'92
    else if sw'4 == (182 : Int32) then
      let t'93 ← PMem.ldU8 (cmd + 8)
      let t'94 := UInt8.toBinary32 (t'93)
      PMem.stF32 packet t'94
      let t'95 ← PMem.ldI16 ((cmd + 8) + 1)
      let t'96 := Int16.toBinary32 (t'95)
      PMem.stF32 (packet + 4) t'96
      let t'97 ← PMem.ldF32 ((cmd + 8) + 3)
      PMem.stF32 (packet + 8) t'97
    else if sw'4 == (183 : Int32) then
      let t'98 ← PMem.ldU8 (cmd + 8)
      let t'99 := UInt8.toBinary32 (t'98)
      PMem.stF32 packet t'99
      let t'100 ← PMem.ldU16 ((cmd + 8) + 1)
      let t'101 := UInt16.toBinary32 (t'100)
      PMem.stF32 (packet + 4) t'101
    else if sw'4 == (184 : Int32) then
      let t'102 ← PMem.ldU8 (cmd + 8)
      let t'103 := UInt8.toBinary32 (t'102)
      PMem.stF32 packet t'103
      let t'104 ← PMem.ldU16 ((cmd + 8) + 1)
      let t'105 := UInt16.toBinary32 (t'104)
      PMem.stF32 (packet + 4) t'105
      let t'106 ← PMem.ldI16 ((cmd + 8) + 3)
      let t'107 := Int16.toBinary32 (t'106)
      PMem.stF32 (packet + 8) t'107
      let t'108 ← PMem.ldF32 ((cmd + 8) + 5)
      PMem.stF32 (packet + 12) t'108
    else if sw'4 == (188 : Int32) || sw'4 == (189 : Int32) then
      pure ()
    else if sw'4 == (191 : Int32) then
      pure ()
    else if sw'4 == (195 : Int32) || sw'4 == (197 : Int32) then
      let t'109 ← PMem.ldU16 (cmd + 4)
      let t'110 := UInt16.toBinary32 (t'109)
      PMem.stF32 packet t'110
    else if sw'4 == (201 : Int32) then
      let t'111 ← PMem.ldU16 (cmd + 4)
      let t'112 := UInt16.toBinary32 (t'111)
      PMem.stF32 packet t'112
    else if sw'4 == (202 : Int32) then
      let t'113 ← PMem.ldU8 (cmd + 8)
      let t'114 := UInt8.toBinary32 (t'113)
      PMem.stF32 packet t'114
      let t'115 ← PMem.ldU16 ((cmd + 8) + 1)
      let t'116 := UInt16.toBinary32 (t'115)
      PMem.stF32 (packet + 4) t'116
      let t'117 ← PMem.ldU8 ((cmd + 8) + 3)
      let t'118 := UInt8.toBinary32 (t'117)
      PMem.stF32 (packet + 8) t'118
      let t'119 ← PMem.ldU16 ((cmd + 8) + 4)
      let t'120 := UInt16.toBinary32 (t'119)
      PMem.stF32 (packet + 12) t'120
      let t'121 ← PMem.ldU8 ((cmd + 8) + 6)
      let t'122 := UInt32.toInt32 (UInt8.toUInt32 (t'121))
      PMem.stI32 (packet + 16) t'122
      let t'123 ← PMem.ldU8 ((cmd + 8) + 7)
      let t'124 := UInt32.toInt32 (UInt8.toUInt32 (t'123))
      PMem.stI32 (packet + 20) t'124
      let t'125 ← PMem.ldF32 ((cmd + 8) + 8)
      PMem.stF32 (packet + 24) t'125
    else if sw'4 == (203 : Int32) then
      let t'126 ← PMem.ldU8 (cmd + 8)
      let t'127 := UInt8.toBinary32 (t'126)
      PMem.stF32 packet t'127
      let t'128 ← PMem.ldU8 ((cmd + 8) + 1)
      let t'129 := UInt8.toBinary32 (t'128)
      PMem.stF32 (packet + 4) t'129
      let t'130 ← PMem.ldI8 ((cmd + 8) + 2)
      let t'131 := Int8.toBinary32 (t'130)
      PMem.stF32 (packet + 8) t'131
      let t'132 ← PMem.ldU8 ((cmd + 8) + 3)
      let t'133 := UInt8.toBinary32 (t'132)
      PMem.stF32 (packet + 12) t'133
      let t'134 ← PMem.ldU8 ((cmd + 8) + 4)
      let t'135 := UInt32.toInt32 (UInt8.toUInt32 (t'134))
      PMem.stI32 (packet + 16) t'135
      let t'136 ← PMem.ldU8 ((cmd + 8) + 5)
      let t'137 := UInt32.toInt32 (UInt8.toUInt32 (t'136))
      PMem.stI32 (packet + 20) t'137
    else if sw'4 == (205 : Int32) then
      let t'138 ← PMem.ldF32 (cmd + 8)
      PMem.stF32 packet t'138
      let t'139 ← PMem.ldF32 ((cmd + 8) + 4)
      PMem.stF32 (packet + 4) t'139
      let t'140 ← PMem.ldF32 ((cmd + 8) + 8)
      PMem.stF32 (packet + 8) t'140
      let t'141 := UInt32.toBinary32 ((2 : UInt32))
      PMem.stF32 (packet + 24) t'141
    else if sw'4 == (206 : Int32) then
      let t'142 ← PMem.ldF32 (cmd + 8)
      PMem.stF32 packet t'142
      let t'143 ← PMem.ldU8 ((cmd + 8) + 4)
      let t'144 := UInt8.toBinary32 (t'143)
      PMem.stF32 (packet + 8) t'144
      let t'145 ← PMem.ldU8 ((cmd + 8) + 5)
      let t'146 := UInt8.toBinary32 (t'145)
      PMem.stF32 (packet + 12) t'146
    else if sw'4 == (207 : Int32) then
      let t'147 ← PMem.ldU16 (cmd + 4)
      let t'148 := UInt16.toBinary32 (t'147)
      PMem.stF32 packet t'148
    else if sw'4 == (208 : Int32) then
      let t'149 ← PMem.ldU16 (cmd + 4)
      let t'150 := UInt16.toBinary32 (t'149)
      PMem.stF32 packet t'150
    else if sw'4 == (216 : Int32) then
      let t'151 ← PMem.ldU16 (cmd + 4)
      let t'152 := UInt16.toBinary32 (t'151)
      PMem.stF32 packet t'152
    else if sw'4 == (218 : Int32) then
      let t'153 ← PMem.ldU16 (cmd + 8)
      let t'154 := UInt16.toBinary32 (t'153)
      PMem.stF32 packet t'154
      let t'155 ← PMem.ldU8 ((cmd + 8) + 2)
      let t'156 := UInt8.toBinary32 (t'155)
      PMem.stF32 (packet + 4) t'156
    else if sw'4 == (210 : Int32) then
      let t'157 ← PMem.ldU16 (cmd + 4)
      let t'158 := UInt16.toBinary32 (t'157)
      PMem.stF32 packet t'158
    else if sw'4 == (222 : Int32) then
      let t'159 ← PMem.ldU16 (cmd + 4)
      let t'160 := UInt16.toBinary32 (t'159)
      PMem.stF32 packet t'160
      let t'161 ← PMem.ldF32 (cmd + 8)
      PMem.stF32 (packet + 4) t'161
      let t'162 ← PMem.ldF32 ((cmd + 8) + 4)
      PMem.stF32 (packet + 8) t'162
      let t'163 ← PMem.ldF32 ((cmd + 8) + 8)
      PMem.stF32 (packet + 12) t'163
    else if sw'4 == (212 : Int32) then
      let t'164 ← PMem.ldU16 (cmd + 4)
      let t'165 := UInt16.toBinary32 (t'164)
      PMem.stF32 packet t'165
    else if sw'4 == (194 : Int32) then
      let t'166 ← PMem.ldU16 (cmd + 4)
      let t'167 := UInt16.toBinary32 (t'166)
      PMem.stF32 packet t'167
    else if sw'4 == (83 : Int32) then
      let t'168 ← PMem.ldF32 (cmd + 8)
      PMem.stF32 packet t'168
      let t'169 ← PMem.ldF32 ((cmd + 8) + 4)
      PMem.stF32 (packet + 4) t'169
      let t'170 ← PMem.ldU8 ((cmd + 8) + 8)
      let t'171 := UInt8.toBinary32 (t'170)
      PMem.stF32 (packet + 8) t'171
    else if sw'4 == (84 : Int32) then
      pure ()
    else if sw'4 == (85 : Int32) then
      let t'172 ← PMem.ldU16 (cmd + 4)
      let t'173 := UInt16.toBinary32 (t'172)
      PMem.stF32 packet t'173
    else if sw'4 == (3000 : Int32) then
      let t'174 ← PMem.ldU8 (cmd + 8)
      let t'175 := UInt8.toBinary32 (t'174)
      PMem.stF32 packet t'175
    else if sw'4 == (223 : Int32) then
      let t'176 ← PMem.ldB (cmd + 8)
      let mut c'177 : Int32 := default
      if t'176 then
        c'177 := (1 : Int32)
      else
        c'177 := (0 : Int32)
      let t'178 := Int32.toBinary32 (c'177)
      PMem.stF32 packet t'178
      let t'179 ← PMem.ldB ((cmd + 8) + 1)
      let mut c'180 : Int32 := default
      if t'179 then
        c'180 := (1 : Int32)
      else
        c'180 := (0 : Int32)
      let t'181 := Int32.toBinary32 (c'180)
      PMem.stF32 (packet + 4) t'181
      let t'182 ← PMem.ldU16 ((cmd + 8) + 2)
      let t'183 := ((Int32.toBinary32 ((UInt32.toInt32 (UInt16.toUInt32 (t'182))))) * (Binary32.ofBits 0x3c23d70a /- 999999977/100000000000 -/))
      PMem.stF32 (packet + 8) t'183
      let t'184 ← PMem.ldB ((cmd + 8) + 4)
      if t'184 then
        let t'185 := UInt32.toBinary32 ((1 : UInt32))
        PMem.stF32 (packet + 12) t'185
    else if sw'4 == (213 : Int32) then
      let t'186 ← PMem.ldF32 (cmd + 8)
      PMem.stF32 packet t'186
      let t'187 ← PMem.ldF32 ((cmd + 8) + 4)
      PMem.stF32 (packet + 4) t'187
      let t'188 ← PMem.ldU8 ((cmd + 8) + 8)
      let t'189 := UInt8.toBinary32 (t'188)
      PMem.stF32 (packet + 8) t'189
    else if sw'4 == (42600 : Int32) then
      let t'190 ← PMem.ldU8 (cmd + 8)
      let t'191 := UInt8.toBinary32 (t'190)
      PMem.stF32 packet t'191
      let t'192 ← PMem.ldU8 ((cmd + 8) + 1)
      let t'193 := UInt8.toBinary32 (t'192)
      PMem.stF32 (packet + 4) t'193
      let t'194 ← PMem.ldF32 ((cmd + 8) + 2)
      PMem.stF32 (packet + 8) t'194
      let t'195 ← PMem.ldF32 ((cmd + 8) + 6)
      PMem.stF32 (packet + 12) t'195
    else if sw'4 == (215 : Int32) then
      let t'196 ← PMem.ldU16 (cmd + 4)
      let t'197 := UInt16.toBinary32 (t'196)
      PMem.stF32 packet t'197
    else if sw'4 == (217 : Int32) then
      let t'198 ← PMem.ldU16 (cmd + 4)
      let t'199 := UInt16.toBinary32 (t'198)
      PMem.stF32 packet t'199
      let t'200 ← PMem.ldF32 (cmd + 8)
      PMem.stF32 (packet + 4) t'200
      let t'201 ← PMem.ldF32 ((cmd + 8) + 4)
      PMem.stF32 (packet + 8) t'201
      let t'202 ← PMem.ldF32 ((cmd + 8) + 8)
      PMem.stF32 (packet + 12) t'202
    else if sw'4 == (42703 : Int32) then
      let t'203 ← PMem.ldU16 (cmd + 8)
      let t'204 := UInt16.toBinary32 (t'203)
      PMem.stF32 packet t'204
      let t'205 ← PMem.ldI16 ((cmd + 8) + 2)
      let t'206 := Int16.toBinary32 (t'205)
      PMem.stF32 (packet + 4) t'206
      let t'207 ← PMem.ldI8 ((cmd + 8) + 4)
      let t'208 := Int8.toBinary32 (t'207)
      PMem.stF32 (packet + 8) t'208
      let t'209 ← PMem.ldI16 ((cmd + 8) + 5)
      let t'210 := Int16.toBinary32 (t'209)
      PMem.stF32 (packet + 12) t'210
      let t'211 ← PMem.ldI16 ((cmd + 8) + 7)
      let t'212 := Int16.toInt32 (t'211)
      PMem.stI32 (packet + 16) t'212
    else if sw'4 == (193 : Int32) then
      let t'213 ← PMem.ldU16 (cmd + 4)
      let t'214 := UInt16.toBinary32 (t'213)
      PMem.stF32 packet t'214
    else if sw'4 == (1000 : Int32) then
      let t'215 ← PMem.ldI8 (cmd + 8)
      let t'216 := Int8.toBinary32 (t'215)
      PMem.stF32 packet t'216
      let t'217 ← PMem.ldI16 ((cmd + 8) + 1)
      let t'218 := Int16.toBinary32 (t'217)
      PMem.stF32 (packet + 4) t'218
      let t'219 ← PMem.ldI8 ((cmd + 8) + 3)
      let t'220 := Int8.toBinary32 (t'219)
      PMem.stF32 (packet + 8) t'220
      let t'221 ← PMem.ldI8 ((cmd + 8) + 4)
      let t'222 := Int8.toBinary32 (t'221)
      PMem.stF32 (packet + 12) t'222
      let t'223 ← PMem.ldU8 ((cmd + 8) + 5)
      let t'224 := UInt32.toInt32 (UInt8.toUInt32 (t'223))
      PMem.stI32 (packet + 16) t'224
      let t'225 ← PMem.ldU8 ((cmd + 8) + 6)
      let t'226 := UInt8.toBinary32 (t'225)
      PMem.stF32 (packet + 24) t'226
    else if sw'4 == (2000 : Int32) then
      let t'227 ← PMem.ldU8 (cmd + 8)
      let t'228 := UInt8.toBinary32 (t'227)
      PMem.stF32 packet t'228
      let t'229 ← PMem.ldF32 ((cmd + 8) + 1)
      PMem.stF32 (packet + 4) t'229
      let t'230 ← PMem.ldU16 ((cmd + 8) + 5)
      let t'231 := UInt16.toBinary32 (t'230)
      PMem.stF32 (packet + 8) t'231
      let t'232 ← PMem.ldU16 ((cmd + 8) + 7)
      let t'233 := UInt16.toBinary32 (t'232)
      PMem.stF32 (packet + 12) t'233
    else if sw'4 == (2001 : Int32) then
      let t'234 ← PMem.ldU16 (cmd + 4)
      let t'235 := UInt16.toBinary32 (t'234)
      PMem.stF32 packet t'235
    else if sw'4 == (531 : Int32) then
      let t'236 ← PMem.ldU8 (cmd + 8)
      let t'237 := UInt8.toBinary32 (t'236)
      PMem.stF32 packet t'237
      let t'238 ← PMem.ldF32 ((cmd + 8) + 1)
      PMem.stF32 (packet + 4) t'238
      let t'239 ← PMem.ldU8 ((cmd + 8) + 5)
      let t'240 := UInt8.toBinary32 (t'239)
      PMem.stF32 (packet + 8) t'240
    else if sw'4 == (532 : Int32) then
      let t'241 ← PMem.ldU8 (cmd + 8)
      let t'242 := UInt8.toBinary32 (t'241)
      PMem.stF32 packet t'242
      let t'243 ← PMem.ldF32 ((cmd + 8) + 1)
      PMem.stF32 (packet + 4) t'243
      let t'244 ← PMem.ldU8 ((cmd + 8) + 5)
      let t'245 := UInt8.toBinary32 (t'244)
      PMem.stF32 (packet + 8) t'245
    else if sw'4 == (534 : Int32) then
      let t'246 ← PMem.ldU8 (cmd + 8)
      let t'247 := UInt8.toBinary32 (t'246)
      PMem.stF32 packet t'247
      let t'248 ← PMem.ldU8 ((cmd + 8) + 1)
      let t'249 := UInt8.toBinary32 (t'248)
      PMem.stF32 (packet + 4) t'249
      let t'250 ← PMem.ldU8 ((cmd + 8) + 2)
      let t'251 := UInt8.toBinary32 (t'250)
      PMem.stF32 (packet + 8) t'251
    else if sw'4 == (2500 : Int32) then
      let t'252 ← PMem.ldU8 (cmd + 8)
      let t'253 := UInt8.toBinary32 (t'252)
      PMem.stF32 packet t'253
      let t'254 ← PMem.ldF32 ((cmd + 8) + 2)
      PMem.stF32 (packet + 4) t'254
      let t'255 ← PMem.ldU8 ((cmd + 8) + 1)
      let t'256 := UInt8.toBinary32 (t'255)
      PMem.stF32 (packet + 8) t'256
    else if sw'4 == (2501 : Int32) then
      let t'257 ← PMem.ldU8 (cmd + 8)
      let t'258 := UInt8.toBinary32 (t'257)
      PMem.stF32 packet t'258
      let t'259 ← PMem.ldU8 ((cmd + 8) + 1)
      let t'260 := UInt8.toBinary32 (t'259)
      PMem.stF32 (packet + 4) t'260
    else if sw'4 == (196 : Int32) then
      let t'261 ← PMem.ldU8 ((cmd + 8) + 6)
      let t'262 := UInt8.toBinary32 (t'261)
      PMem.stF32 packet t'262
      let t'263 ← PMem.ldI16 (cmd + 8)
      let t'264 := Binary32.toInt32 (((Int32.toBinary32 ((Int16.toInt32 (t'263)))) * (Binary64.toBinary32 ((Binary64.ofBits 0x3f847ae147ae147b /- 1/100 -/)))))
      PMem.stI32 (packet + 20) t'264
      let t'265 ← PMem.ldI16 ((cmd + 8) + 2)
      let t'266 := Binary32.toInt32 (((Int32.toBinary32 ((Int16.toInt32 (t'265)))) * (Binary64.toBinary32 ((Binary64.ofBits 0x3f847ae147ae147b /- 1/100 -/)))))
      PMem.stI32 (packet + 16) t'266
      let t'267 ← PMem.ldI16 ((cmd + 8) + 4)
      let t'268 := ((Int32.toBinary32 ((Int16.toInt32 (t'267)))) * (Binary64.toBinary32 ((Binary64.ofBits 0x3f847ae147ae147b /- 1/100 -/))))
      PMem.stF32 (packet + 24) t'268
    else
      return false
  let t'269 ← PMem.ldU16 (cmd + 2)
  let t'270 ← AP_Mission.stored_in_location t'269
  if t'270 then
    let t'271 ← PMem.ldI32 ((cmd + 8) + 8)
    PMem.stI32 (packet + 16) t'271
    let t'272 ← PMem.ldI32 ((cmd + 8) + 12)
    PMem.stI32 (packet + 20) t'272
    let t'273 ← PMem.ldI32 ((cmd + 8) + 4)
    let t'274 := ((Int32.toBinary32 (t'273)) * (Binary32.ofBits 0x3c23d70a /- 999999977/100000000000 -/))
    PMem.stF32 (packet + 24) t'274
    let t'275 ← PMem.ldBits (cmd + 8) 0 1
    if (UInt64.toUInt8 (t'275)) != (0 : UInt8) then
      let t'276 := UInt32.toUInt8 ((3 : UInt32))
      PMem.stU8 (packet + 34) t'276
    else
      let t'277 := UInt32.toUInt8 ((0 : UInt32))
      PMem.stU8 (packet + 34) t'277
    let t'278 ← PMem.ldBits (cmd + 8) 2 1
    if (UInt64.toUInt8 (t'278)) != (0 : UInt8) then
      return false
  return true

def AP_Mission.mission_cmd_to_mavlink_int (cmd : UInt64) (packet : UInt64) : PMem.M Bool := do
  let fp ← PMem.enter 38
  let r ← AP_Mission.mission_cmd_to_mavlink_int.body fp cmd packet
  PMem.leave fp
  return r

/-- `AP_Mission.get_current_nav_cmd` as a pure function of its arguments (it reads and writes no memory). -/
def AP_Mission.get_current_nav_cmd.pure' (this : UInt64) : Id UInt64 := do
  return (this + 88)

/-- C++ `AP_Mission::get_current_nav_cmd : const Mission_Command &() const`, `AP_Common.h:597-600`. -/
def AP_Mission.get_current_nav_cmd (this : UInt64) : PMem.M UInt64 :=
  pure (_root_.Vehicle_lib.AP_Mission.get_current_nav_cmd.pure' this)

/-- C++ `AP_Mission::convert_MISSION_ITEM_INT_to_MISSION_ITEM : MAV_MISSION_RESULT (const mavlink_mission_item_int_t &, mavlink_mission_item_t &)`, `AP_Mission.cpp:1660-1695`. -/
def AP_Mission.convert_MISSION_ITEM_INT_to_MISSION_ITEM (item_int : UInt64) (item : UInt64) : PMem.M UInt32 := do
  let t'1 ← PMem.ldF32 item_int
  PMem.stF32 item t'1
  let t'2 ← PMem.ldF32 (item_int + 4)
  PMem.stF32 (item + 4) t'2
  let t'3 ← PMem.ldF32 (item_int + 8)
  PMem.stF32 (item + 8) t'3
  let t'4 ← PMem.ldF32 (item_int + 12)
  PMem.stF32 (item + 12) t'4
  let t'5 ← PMem.ldF32 (item_int + 24)
  PMem.stF32 (item + 24) t'5
  let t'6 ← PMem.ldU16 (item_int + 28)
  PMem.stU16 (item + 28) t'6
  let t'7 ← PMem.ldU16 (item_int + 30)
  PMem.stU16 (item + 30) t'7
  let t'8 ← PMem.ldU8 (item_int + 32)
  PMem.stU8 (item + 32) t'8
  let t'9 ← PMem.ldU8 (item_int + 33)
  PMem.stU8 (item + 33) t'9
  let t'10 ← PMem.ldU8 (item_int + 34)
  PMem.stU8 (item + 34) t'10
  let t'11 ← PMem.ldU8 (item_int + 35)
  PMem.stU8 (item + 35) t'11
  let t'12 ← PMem.ldU8 (item_int + 36)
  PMem.stU8 (item + 36) t'12
  let t'13 ← PMem.ldU8 (item_int + 37)
  PMem.stU8 (item + 37) t'13
  let t'14 ← PMem.ldU16 (item_int + 30)
  let t'15 ← AP_Mission.cmd_has_location t'14
  if !t'15 then
    let t'16 ← PMem.ldI32 (item_int + 16)
    let t'17 := Int32.toBinary32 (t'16)
    PMem.stF32 (item + 16) t'17
    let t'18 ← PMem.ldI32 (item_int + 20)
    let t'19 := Int32.toBinary32 (t'18)
    PMem.stF32 (item + 20) t'19
  else
    let t'20 ← PMem.ldI32 (item_int + 16)
    let t'21 := ((Int32.toBinary32 (t'20)) * (Binary32.ofBits 0x33d6bf95 /- 100000001/1000000000000000 -/))
    PMem.stF32 (item + 16) t'21
    let t'22 ← PMem.ldI32 (item_int + 20)
    let t'23 := ((Int32.toBinary32 (t'22)) * (Binary32.ofBits 0x33d6bf95 /- 100000001/1000000000000000 -/))
    PMem.stF32 (item + 20) t'23
    let t'24 ← PMem.ldF32 (item + 16)
    let t'25 ← check_lat'2 t'24
    if !t'25 then
      return (10 : UInt32)
    let t'26 ← PMem.ldF32 (item + 20)
    let t'27 ← check_lng'2 t'26
    if !t'27 then
      return (11 : UInt32)
  return (0 : UInt32)

/-- C++ `AP_Mission::is_valid_index : bool (const uint16_t) const`, `sitl.h:811-?`. -/
def AP_Mission.is_valid_index (this : UInt64) (index : UInt16) : PMem.M Bool := do
  let mut index := index
  let t'1 ← AP_ParamT'short_2.operator_const_short__ (this + 80)
  let t'2 ← PMem.ldI16 t'1
  return (decide ((UInt32.toInt32 (UInt16.toUInt32 (index))) < (Int16.toInt32 (t'2))))

/-- C++ `AP_Mission::reset_jump_counters : void ()`, `AP_Common.h:564-?`. -/
def AP_Mission.reset_jump_counters (this : UInt64) : PMem.M Unit := do
  AP_Mission.init_jump_tracking this
  return ()

/-- `AP_Mission.Mission_Flags.Mission_Flags` as a pure function of its arguments (it reads and writes no memory). -/
def AP_Mission.Mission_Flags.Mission_Flags.pure' (this : UInt64) : Id Unit := do
  return ()

/-- C++ `AP_Mission::Mission_Flags::Mission_Flags : void () noexcept`, `sitl.h:?-?`. -/
def AP_Mission.Mission_Flags.Mission_Flags (this : UInt64) : PMem.M Unit :=
  pure (_root_.Vehicle_lib.AP_Mission.Mission_Flags.Mission_Flags.pure' this)

/-- C++ `AP_Mission::update_exit_position : void ()`, `AP_Mission.cpp:3147-3153`. -/
def AP_Mission.update_exit_position (this : UInt64) : PMem.M Unit := do
  let t'1 ← VehicleBridge.ahrs'0
  let t'2 ← VehicleBridge.AP_AHRS.get_location'1 t'1 (this + 180)
  if !t'2 then
    PMem.stI32 ((this + 180) + 8) (0 : Int32)
    PMem.stI32 ((this + 180) + 12) (0 : Int32)
  return ()

/-- C++ `AP_Mission::on_mission_timestamp_change : void ()`, `AP_Mission.cpp:363-366`. -/
def AP_Mission.on_mission_timestamp_change (this : UInt64) : PMem.M Unit := do
  let t'1 := Int16.toUInt16 (Int32.toInt16 ((0 : Int32)))
  PMem.stU16 this t'1
  return ()

/-- C++ `AP_Mission::continue_after_land : bool () const`, `sitl.h:785-787`. -/
def AP_Mission.continue_after_land (this : UInt64) : PMem.M Bool := do
  let t'1 ← AP_Mission.option_is_set this (4 : Int32)
  return t'1

/-- C++ `AP_Mission::get_in_landing_sequence_flag : bool () const`, `AP_Common.h:731-733`. -/
def AP_Mission.get_in_landing_sequence_flag (this : UInt64) : PMem.M Bool := do
  let t'1 ← PMem.ldB ((this + 4) + 7)
  return t'1

/-- C++ `AP_Mission::get_in_return_path_flag : bool () const`, `AP_Common.h:736-738`. -/
def AP_Mission.get_in_return_path_flag (this : UInt64) : PMem.M Bool := do
  let t'1 ← PMem.ldB ((this + 4) + 9)
  return t'1

end Vehicle_lib
