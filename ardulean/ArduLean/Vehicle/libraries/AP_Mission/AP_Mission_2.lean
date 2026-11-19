import ArduLean.Runtime.Bridge
import ArduLean.Vehicle.libraries.AP_Math.AP_Math
import ArduLean.Vehicle.libraries.AP_HAL.AP_HAL
import ArduLean.Vehicle.libraries.StorageManager.StorageManager
import ArduLean.Vehicle.libraries.AP_Param.AP_Param
import ArduLean.Vehicle.libraries.AP_Mission.AP_Mission
import ArduLean.Vehicle.libraries.AP_Common.AP_Common
import ArduLean.Vehicle.mavlink.mavlink
import ArduLean.Vehicle.libraries.AP_Param.AP_Param_2

/-!
ArduPilot `libraries/AP_Mission`, part 2 of 3. Sources: `libraries/AP_Mission/AP_Mission.cpp`.

Items of `lean/Vehicle_lib.lean` (the vehicle translation), unchanged; placed by `tools/split_modules.py` (`ArduLean/Vehicle/INDEX.md`).
-/

open FloatLib.Floats (Binary32 Binary64)

set_option linter.unusedVariables false
set_option linter.unreachableTactic false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false

namespace Vehicle_lib

/-- C++ `AP_Mission::Content::Content : void () noexcept(false)`, `AP_Common.h:?-?`. -/
def AP_Mission.Content.Content (this : UInt64) : PMem.M Unit := do
  Location.Location (this + 0)
  return ()

/-- C++ `AP_Mission::write_home_to_storage : void ()`, `AP_Mission.cpp:1011-1022`. -/
def AP_Mission.write_home_to_storage.body (fp : UInt64) (this : UInt64) : PMem.M Unit := do
  discard <| PMem.memset ((fp + 0) + 0) 0 2
  discard <| PMem.memset ((fp + 0) + 2) 0 2
  discard <| PMem.memset ((fp + 0) + 4) 0 2
  AP_Mission.Content.Content ((fp + 0) + 8)
  discard <| PMem.memset ((fp + 0) + 24) 0 1
  let t'1 := UInt32.toUInt16 ((16 : UInt32))
  PMem.stU16 ((fp + 0) + 2) t'1
  let t'2 ← VehicleBridge.ahrs'0
  VehicleBridge.AP_AHRS.get_home'0 t'2 (fp + 32)
  let t'3 := (fp + 32)
  discard <| PMem.memcpy ((fp + 0) + 8) t'3 16
  discard <| pure (((fp + 0) + 8))
  let t'4 ← AP_Mission.write_cmd_to_storage this (Int16.toUInt16 (Int32.toInt16 ((0 : Int32)))) (fp + 0)
  discard <| pure (t'4)
  let t'5 ← AP_ParamT'short_2.operator_const_short__ (this + 80)
  let t'6 ← PMem.ldI16 t'5
  if (decide ((Int16.toInt32 (t'6)) < (1 : Int32))) then
    PMem.stI16 (fp + 48) (Int32.toInt16 ((1 : Int32)))
    AP_ParamTBase'short_2.set_and_save (this + 80) (fp + 48)
  return ()

def AP_Mission.write_home_to_storage (this : UInt64) : PMem.M Unit := do
  let fp ← PMem.enter 50
  let r ← AP_Mission.write_home_to_storage.body fp this
  PMem.leave fp
  return r

/-- C++ `AP_Mission::Mission_Command::Mission_Command : void () noexcept(false)`, `AP_Common.h:?-?`. -/
def AP_Mission.Mission_Command.Mission_Command (this : UInt64) : PMem.M Unit := do
  AP_Mission.Content.Content (this + 8)
  return ()

/-- C++ `AP_Mission::read_cmd_from_storage : bool (uint16_t, Mission_Command &) const`, `AP_Mission.cpp:829-906`. -/
def AP_Mission.read_cmd_from_storage.body (fp : UInt64) (this : UInt64) (index : UInt16) (cmd : UInt64) : PMem.M Bool := do
  let mut index := index
  for _ in [0:1] do
    assert_storage_size'PackedContent_12.assert_storage_size (fp + 0)
    discard <| pure ((fp + 0))
  if ((UInt32.toInt32 (UInt16.toUInt32 (index))) == (0 : Int32)) then
    discard <| PMem.memset ((fp + 8) + 0) 0 2
    discard <| PMem.memset ((fp + 8) + 2) 0 2
    discard <| PMem.memset ((fp + 8) + 4) 0 2
    AP_Mission.Content.Content ((fp + 8) + 8)
    discard <| PMem.memset ((fp + 8) + 24) 0 1
    discard <| PMem.memcpy cmd (fp + 8) 28
    discard <| pure (cmd)
    let t'1 := UInt32.toUInt16 ((16 : UInt32))
    PMem.stU16 (cmd + 2) t'1
    let t'2 ← VehicleBridge.ahrs'0
    VehicleBridge.AP_AHRS.get_home'0 t'2 (fp + 40)
    let t'3 := (fp + 40)
    discard <| PMem.memcpy (cmd + 8) t'3 16
    discard <| pure ((cmd + 8))
    return true
  let t'4 ← AP_ParamT'short_2.operator_const_short__ (this + 80)
  let t'5 ← PMem.ldI16 t'4
  let mut sc'7 := (decide ((UInt16.toUInt32 (index)) ≥ (Int32.toUInt32 (Int16.toInt32 (t'5)))))
  if !sc'7 then
    let t'6 ← PMem.ldU16 (this + 604)
    sc'7 := (decide ((UInt32.toInt32 (UInt16.toUInt32 (index))) ≥ (UInt32.toInt32 (UInt16.toUInt32 (t'6)))))
  if sc'7 then
    return false
  discard <| PMem.memset ((fp + 56) + 0) 0 2
  discard <| PMem.memset ((fp + 56) + 2) 0 2
  discard <| PMem.memset ((fp + 56) + 4) 0 2
  AP_Mission.Content.Content ((fp + 56) + 8)
  discard <| PMem.memset ((fp + 56) + 24) 0 1
  discard <| PMem.memcpy cmd (fp + 56) 28
  discard <| pure (cmd)
  let mut pos_in_storage : UInt16 := Int16.toUInt16 (Int32.toInt16 (((4 : Int32) + ((UInt32.toInt32 (UInt16.toUInt32 (index))) * (15 : Int32)))))
  PMem.stBits ((((fp + 88) + 0) + 0) + 0) 0 1 (UInt8.toUInt64 ((0 : UInt8)))
  PMem.stBits ((((fp + 88) + 0) + 0) + 0) 1 1 (UInt8.toUInt64 ((0 : UInt8)))
  PMem.stBits ((((fp + 88) + 0) + 0) + 0) 2 1 (UInt8.toUInt64 ((0 : UInt8)))
  PMem.stBits ((((fp + 88) + 0) + 0) + 0) 3 1 (UInt8.toUInt64 ((0 : UInt8)))
  PMem.stBits ((((fp + 88) + 0) + 0) + 0) 4 1 (UInt8.toUInt64 ((0 : UInt8)))
  PMem.stBits ((((fp + 88) + 0) + 0) + 0) 5 1 (UInt8.toUInt64 ((0 : UInt8)))
  PMem.stBits ((((fp + 88) + 0) + 0) + 0) 6 1 (UInt8.toUInt64 ((0 : UInt8)))
  PMem.stBits ((((fp + 88) + 0) + 0) + 0) 7 1 (UInt8.toUInt64 ((0 : UInt8)))
  PMem.stBits ((fp + 88) + 0) 8 24 (Int64.toUInt64 (Int32.toInt64 ((0 : Int32))))
  discard <| PMem.memset (((fp + 88) + 0) + 4) 0 4
  discard <| PMem.memset (((fp + 88) + 0) + 8) 0 4
  let t'8 ← StorageAccess.read_byte (0xbf28 : UInt64) /- &AP_Mission::_storage -/ pos_in_storage
  let mut b1 : UInt8 := t'8
  if (((UInt32.toInt32 (UInt8.toUInt32 (b1))) == (0 : Int32)) || ((UInt32.toInt32 (UInt8.toUInt32 (b1))) == (1 : Int32))) then
    let t'9 ← StorageAccess.read_uint16 (0xbf28 : UInt64) /- &AP_Mission::_storage -/ (Int16.toUInt16 (Int32.toInt16 (((UInt32.toInt32 (UInt16.toUInt32 (pos_in_storage))) + (1 : Int32)))))
    PMem.stU16 (cmd + 2) t'9
    let t'10 ← StorageAccess.read_uint16 (0xbf28 : UInt64) /- &AP_Mission::_storage -/ (Int16.toUInt16 (Int32.toInt16 (((UInt32.toInt32 (UInt16.toUInt32 (pos_in_storage))) + (3 : Int32)))))
    PMem.stU16 (cmd + 4) t'10
    let t'11 ← StorageAccess.read_block (0xbf28 : UInt64) /- &AP_Mission::_storage -/ (fp + 88) (Int16.toUInt16 (Int32.toInt16 (((UInt32.toInt32 (UInt16.toUInt32 (pos_in_storage))) + (5 : Int32))))) (Int64.toUInt64 (Int32.toInt64 ((10 : Int32))))
    discard <| pure (t'11)
    AP_Mission.format_conversion this b1 cmd (fp + 88)
  else
    let t'12 := UInt8.toUInt16 (b1)
    PMem.stU16 (cmd + 2) t'12
    let t'13 ← StorageAccess.read_uint16 (0xbf28 : UInt64) /- &AP_Mission::_storage -/ (Int16.toUInt16 (Int32.toInt16 (((UInt32.toInt32 (UInt16.toUInt32 (pos_in_storage))) + (1 : Int32)))))
    PMem.stU16 (cmd + 4) t'13
    let t'14 ← StorageAccess.read_block (0xbf28 : UInt64) /- &AP_Mission::_storage -/ (fp + 88) (Int16.toUInt16 (Int32.toInt16 (((UInt32.toInt32 (UInt16.toUInt32 (pos_in_storage))) + (3 : Int32))))) (Int64.toUInt64 (Int32.toInt64 ((12 : Int32))))
    discard <| pure (t'14)
  let t'15 ← PMem.ldU16 (cmd + 2)
  let t'16 ← AP_Mission.stored_in_location t'15
  if t'16 then
    if ((UInt32.toInt32 (UInt8.toUInt32 (b1))) == (0 : Int32)) then
      pure ()
    let t'17 ← PMem.ldBits (fp + 88) 0 1
    let t'18 := UInt64.toUInt8 (t'17)
    PMem.stBits (cmd + 8) 0 1 (UInt8.toUInt64 (t'18))
    let t'19 ← PMem.ldBits (fp + 88) 2 1
    let t'20 := UInt64.toUInt8 (t'19)
    PMem.stBits (cmd + 8) 1 1 (UInt8.toUInt64 (t'20))
    let t'21 ← PMem.ldBits (fp + 88) 3 1
    let t'22 := UInt64.toUInt8 (t'21)
    PMem.stBits (cmd + 8) 2 1 (UInt8.toUInt64 (t'22))
    let t'23 ← PMem.ldBits (fp + 88) 4 1
    let t'24 := UInt64.toUInt8 (t'23)
    PMem.stBits (cmd + 8) 3 1 (UInt8.toUInt64 (t'24))
    let t'25 ← PMem.ldBits (fp + 88) 5 1
    let t'26 := UInt64.toUInt8 (t'25)
    PMem.stBits (cmd + 8) 4 1 (UInt8.toUInt64 (t'26))
    let t'27 ← PMem.ldBits (fp + 88) 8 24
    let t'28 := UInt32.toInt32 (UInt64.toUInt32 (t'27))
    PMem.stI32 ((cmd + 8) + 4) t'28
    let t'29 ← PMem.ldI32 ((fp + 88) + 4)
    PMem.stI32 ((cmd + 8) + 8) t'29
    let t'30 ← PMem.ldI32 ((fp + 88) + 8)
    PMem.stI32 ((cmd + 8) + 12) t'30
    let t'31 ← PMem.ldBits (fp + 88) 6 1
    if (UInt64.toUInt8 (t'31)) != (0 : UInt8) then
      let t'32 := (cmd + 24)
      let t'33 ← PMem.ldU8 t'32
      let t'34 := (t'33 ||| (UInt32.toUInt8 (((1 : UInt32) <<< (Int32.toUInt32 ((0 : Int32)))))))
      PMem.stU8 t'32 t'34
    let t'35 ← PMem.ldBits (fp + 88) 7 1
    if (UInt64.toUInt8 (t'35)) != (0 : UInt8) then
      let t'36 := (cmd + 24)
      let t'37 ← PMem.ldU8 t'36
      let t'38 := (t'37 ||| (UInt32.toUInt8 (((1 : UInt32) <<< (Int32.toUInt32 ((1 : Int32)))))))
      PMem.stU8 t'36 t'38
  else
    let t'39 ← PMem.memcpy (cmd + 8) (fp + 88) (Int64.toUInt64 (Int32.toInt64 ((12 : Int32))))
    discard <| pure (t'39)
  PMem.stU16 cmd index
  return true

def AP_Mission.read_cmd_from_storage (this : UInt64) (index : UInt16) (cmd : UInt64) : PMem.M Bool := do
  let fp ← PMem.enter 100
  let r ← AP_Mission.read_cmd_from_storage.body fp this index cmd
  PMem.leave fp
  return r

/-- C++ `AP_Mission::get_index_of_jump_tag : uint16_t (const uint16_t) const`, `AP_Mission.cpp:2420-2436`. -/
def AP_Mission.get_index_of_jump_tag.body (fp : UInt64) (this : UInt64) (tag : UInt16) : PMem.M UInt16 := do
  let mut tag := tag
  let t'1 ← AP_Mission.num_commands this
  let mut count : UInt16 := t'1
  for i'2 in [1:count.toNat] do
    let i : UInt16 := UInt16.ofNat i'2
    let t'3 ← AP_Mission.get_command_id this i
    if ((UInt32.toInt32 (UInt16.toUInt32 (t'3))) != (UInt32.toInt32 (UInt16.toUInt32 ((UInt32.toUInt16 ((600 : UInt32))))))) then
      continue
    AP_Mission.Mission_Command.Mission_Command (fp + 0)
    let t'4 ← AP_Mission.read_cmd_from_storage this i (fp + 0)
    if !t'4 then
      continue
    let t'5 ← PMem.ldU16 ((fp + 0) + 2)
    let mut sc'7 := ((UInt32.toInt32 (UInt16.toUInt32 (t'5))) == (UInt32.toInt32 ((600 : UInt32))))
    if sc'7 then
      let t'6 ← PMem.ldU16 ((fp + 0) + 8)
      sc'7 := ((UInt32.toInt32 (UInt16.toUInt32 (t'6))) == (UInt32.toInt32 (UInt16.toUInt32 (tag))))
    if sc'7 then
      return i
  return Int16.toUInt16 (Int32.toInt16 ((0 : Int32)))

def AP_Mission.get_index_of_jump_tag (this : UInt64) (tag : UInt16) : PMem.M UInt16 := do
  let fp ← PMem.enter 28
  let r ← AP_Mission.get_index_of_jump_tag.body fp this tag
  PMem.leave fp
  return r

/-- C++ `AP_Mission::add_cmd : bool (Mission_Command &)`, `AP_Mission.cpp:510-528`. -/
def AP_Mission.add_cmd.body (fp : UInt64) (this : UInt64) (cmd : UInt64) : PMem.M Bool := do
  let t'1 ← AP_ParamT'short_2.operator_const_short__ (this + 80)
  let t'2 ← PMem.ldI16 t'1
  if (decide ((Int16.toInt32 (t'2)) < (1 : Int32))) then
    AP_Mission.write_home_to_storage this
  let t'3 ← AP_ParamT'short_2.operator_const_short__ (this + 80)
  let t'4 ← PMem.ldI16 t'3
  let t'5 ← AP_Mission.write_cmd_to_storage this (Int16.toUInt16 (t'4)) cmd
  let mut ret : Bool := t'5
  if ret then
    let t'6 ← AP_ParamT'short_2.operator_const_short__ (this + 80)
    let t'7 ← PMem.ldI16 t'6
    let t'8 := Int16.toUInt16 (t'7)
    PMem.stU16 cmd t'8
    let t'9 ← AP_ParamT'short_2.operator_const_short__ (this + 80)
    let t'10 ← PMem.ldI16 t'9
    PMem.stI16 (fp + 0) (Int32.toInt16 (((Int16.toInt32 (t'10)) + (1 : Int32))))
    AP_ParamTBase'short_2.set_and_save (this + 80) (fp + 0)
  return ret

def AP_Mission.add_cmd (this : UInt64) (cmd : UInt64) : PMem.M Bool := do
  let fp ← PMem.enter 2
  let r ← AP_Mission.add_cmd.body fp this cmd
  PMem.leave fp
  return r

/-- C++ `AP_Mission::contains_item : bool (MAV_CMD) const`, `AP_Mission.cpp:3077-3094`. -/
def AP_Mission.contains_item.body (fp : UInt64) (this : UInt64) (command : UInt32) : PMem.M Bool := do
  let mut command := command
  let t'1 ← AP_Mission.num_commands this
  let mut count : UInt16 := t'1
  for i'2 in [1:count.toNat] do
    let i : UInt16 := UInt16.ofNat i'2
    let t'3 ← AP_Mission.get_command_id this i
    if ((UInt32.toInt32 (UInt16.toUInt32 (t'3))) != (UInt32.toInt32 (UInt16.toUInt32 ((UInt32.toUInt16 (command)))))) then
      continue
    AP_Mission.Mission_Command.Mission_Command (fp + 0)
    let t'4 ← AP_Mission.read_cmd_from_storage this i (fp + 0)
    if !t'4 then
      continue
    let t'5 ← PMem.ldU16 ((fp + 0) + 2)
    if ((UInt32.toInt32 (UInt16.toUInt32 (t'5))) == (UInt32.toInt32 (command))) then
      return true
  return false

def AP_Mission.contains_item (this : UInt64) (command : UInt32) : PMem.M Bool := do
  let fp ← PMem.enter 28
  let r ← AP_Mission.contains_item.body fp this command
  PMem.leave fp
  return r

/-- C++ `AP_Mission::calculate_contains_terrain_alt_items : bool () const`, `AP_Mission.cpp:3117-3133`. -/
def AP_Mission.calculate_contains_terrain_alt_items.body (fp : UInt64) (this : UInt64) : PMem.M Bool := do
  let t'1 ← AP_Mission.num_commands this
  let mut count : UInt16 := t'1
  for i'2 in [1:count.toNat] do
    let i : UInt16 := UInt16.ofNat i'2
    let t'3 ← AP_Mission.get_command_id this i
    let t'4 ← AP_Mission.stored_in_location t'3
    if !t'4 then
      continue
    AP_Mission.Mission_Command.Mission_Command (fp + 0)
    let t'5 ← AP_Mission.read_cmd_from_storage this i (fp + 0)
    if !t'5 then
      continue
    let t'6 ← PMem.ldU16 ((fp + 0) + 2)
    let t'7 ← AP_Mission.stored_in_location t'6
    let mut sc'9 := t'7
    if sc'9 then
      let t'8 ← PMem.ldBits ((fp + 0) + 8) 2 1
      sc'9 := (UInt64.toUInt8 (t'8)) != (0 : UInt8)
    if sc'9 then
      return true
  return false

def AP_Mission.calculate_contains_terrain_alt_items (this : UInt64) : PMem.M Bool := do
  let fp ← PMem.enter 28
  let r ← AP_Mission.calculate_contains_terrain_alt_items.body fp this
  PMem.leave fp
  return r

/-- C++ `AP_Mission::contains_terrain_alt_items : bool ()`, `AP_Mission.cpp:3108-3115`. -/
def AP_Mission.contains_terrain_alt_items (this : UInt64) : PMem.M Bool := do
  let t'1 ← PMem.ldU32 (this + 608)
  let t'2 ← PMem.ldU32 (this + 596)
  if (t'1 != t'2) then
    let t'3 ← AP_Mission.calculate_contains_terrain_alt_items this
    PMem.stB (this + 607) t'3
    let t'4 ← PMem.ldU32 (this + 596)
    PMem.stU32 (this + 608) t'4
  let t'5 ← PMem.ldB (this + 607)
  return t'5

/-- C++ `AP_Mission::truncate : void (uint16_t)`, `AP_Mission.cpp:300-306`. -/
def AP_Mission.truncate.body (fp : UInt64) (this : UInt64) (index : UInt16) : PMem.M Unit := do
  let mut index := index
  let t'1 ← AP_ParamT'short_2.operator_const_short__ (this + 80)
  let t'2 ← PMem.ldI16 t'1
  if (decide ((Int32.toUInt32 (Int16.toInt32 (t'2))) > (UInt16.toUInt32 (index)))) then
    PMem.stI16 (fp + 0) (UInt16.toInt16 (index))
    AP_ParamTBase'short_2.set_and_save (this + 80) (fp + 0)
    let t'3 := ((← PMem.clock) / 1000).toUInt32
    PMem.stU32 (this + 596) t'3
  return ()

def AP_Mission.truncate (this : UInt64) (index : UInt16) : PMem.M Unit := do
  let fp ← PMem.enter 2
  let r ← AP_Mission.truncate.body fp this index
  PMem.leave fp
  return r

/-- C++ `AP_Mission::clear : bool ()`, `AP_Mission.cpp:278-296`. -/
def AP_Mission.clear (this : UInt64) : PMem.M Bool := do
  let mut sc'2 := (← get).armed
  if sc'2 then
    let t'1 ← PMem.ldU32 (this + 4)
    sc'2 := ((UInt32.toInt32 (t'1)) == (UInt32.toInt32 ((1 : UInt32))))
  if sc'2 then
    return false
  AP_Mission.truncate this (Int16.toUInt16 (Int32.toInt16 ((0 : Int32))))
  let t'3 := Int16.toUInt16 (Int32.toInt16 ((65535 : Int32)))
  PMem.stU16 (this + 88) t'3
  let t'4 := Int16.toUInt16 (Int32.toInt16 ((65535 : Int32)))
  PMem.stU16 (this + 116) t'4
  PMem.stB ((this + 4) + 4) false
  PMem.stB ((this + 4) + 5) false
  PMem.stU32 (this + 4) (0 : UInt32)
  return true

/-- C++ `AP_Mission::calc_rewind_pos : bool (Mission_Command &)`, `AP_Mission.cpp:3156-3241`. -/
def AP_Mission.calc_rewind_pos.body (fp : UInt64) (this : UInt64) (rewind_cmd : UInt64) : PMem.M Bool := do
  let t'1 ← PMem.ldU16 ((this + 16) + ((Int32.toInt64 (((7 : Int32) - (2 : Int32)))) * 2).toUInt64)
  if ((UInt32.toInt32 (UInt16.toUInt32 (t'1))) == (65535 : Int32)) then
    return false
  let t'2 ← PMem.ldI32 ((this + 180) + 8)
  let mut sc'4 := (t'2 == (0 : Int32))
  if sc'4 then
    let t'3 ← PMem.ldI32 ((this + 180) + 12)
    sc'4 := (t'3 == (0 : Int32))
  if sc'4 then
    return false
  AP_Mission.Mission_Command.Mission_Command (fp + 0)
  let t'5 ← PMem.ldU16 (this + 86)
  let mut rewind_distance : Binary32 := UInt16.toBinary32 (t'5)
  let mut resume_index : UInt16 := default  -- uninitialized in C
  discard <| PMem.memcpy (fp + 32) (this + 180) 16
  let mut i : Int8 := Int32.toInt8 (((7 : Int32) - (2 : Int32)))
  let mut first'6 := true
  for _ in PMem.loopFuel do
    if !first'6 then
      let t'7 := i
      let t'8 := (t'7 - 1)
      i := t'8
      pure ()
    first'6 := false
    if !((decide ((Int8.toInt32 (i)) ≥ (0 : Int32)))) then break
    let t'9 ← PMem.ldU16 ((this + 16) + ((Int8.toInt64 (i)) * 2).toUInt64)
    if ((UInt32.toInt32 (UInt16.toUInt32 (t'9))) == (65535 : Int32)) then
      let t'10 := Int16.toUInt16 (Int32.toInt16 (((Int8.toInt32 (i)) + (1 : Int32))))
      resume_index := t'10
      break
    let t'11 ← PMem.ldU16 ((this + 16) + ((Int8.toInt64 (i)) * 2).toUInt64)
    let t'12 ← AP_Mission.read_cmd_from_storage this t'11 (fp + 0)
    if !t'12 then
      return false
    let t'13 ← Location.get_distance (fp + 32) ((fp + 0) + 8)
    let mut disttemp : Binary32 := Binary64.toBinary32 (t'13)
    let t'14 := (rewind_distance - disttemp)
    rewind_distance := t'14
    let t'15 := Int16.toUInt16 (Int8.toInt16 (i))
    resume_index := t'15
    if (decide (rewind_distance ≤ (Binary32.ofBits 0x00000000 /- 0 -/))) then
      discard <| PMem.memcpy rewind_cmd (fp + 0) 28
      discard <| pure (rewind_cmd)
      break
    discard <| PMem.memcpy (fp + 32) ((fp + 0) + 8) 16
    discard <| pure ((fp + 32))
  if (decide (rewind_distance > (Binary32.ofBits 0x00000000 /- 0 -/))) then
    discard <| PMem.memcpy rewind_cmd (fp + 0) 28
    discard <| pure (rewind_cmd)
    return true
  discard <| PMem.memcpy (fp + 48) ((fp + 0) + 8) 16
  let t'16 ← PMem.ldU16 ((this + 16) + ((Int32.toInt64 (((UInt32.toInt32 (UInt16.toUInt32 (resume_index))) + (1 : Int32)))) * 2).toUInt64)
  let t'17 ← AP_Mission.read_cmd_from_storage this t'16 (fp + 0)
  if !t'17 then
    return false
  let t'18 ← Location.get_distance (fp + 48) ((fp + 0) + 8)
  let mut leg_length : Binary32 := Binary64.toBinary32 (t'18)
  let mut leg_percent : Binary32 := ((Binary32.abs rewind_distance) / leg_length)
  Location.get_distance_NED (fp + 48) (fp + 80) ((fp + 0) + 8)
  let t'19 := (fp + 80)
  Vector3'float.Vector3'3 (fp + 64) t'19
  let t'20 ← PMem.ldF32 (fp + 64)
  let t'21 ← PMem.ldF32 ((fp + 64) + 4)
  Location.offset (rewind_cmd + 8) (Binary32.toBinary64 ((t'20 * leg_percent))) (Binary32.toBinary64 ((t'21 * leg_percent)))
  let t'22 ← PMem.ldF32 ((fp + 64) + 8)
  Location.offset_up_m (rewind_cmd + 8) ((-t'22) * leg_percent)
  return true

def AP_Mission.calc_rewind_pos (this : UInt64) (rewind_cmd : UInt64) : PMem.M Bool := do
  let fp ← PMem.enter 92
  let r ← AP_Mission.calc_rewind_pos.body fp this rewind_cmd
  PMem.leave fp
  return r

/-- C++ `AP_Mission::mavlink_int_to_mission_cmd : MAV_MISSION_RESULT (const mavlink_mission_item_int_t &, AP_Mission::Mission_Command &)`, `AP_Mission.cpp:1075-1612`. -/
def AP_Mission.mavlink_int_to_mission_cmd.body (fp : UInt64) (input_packet : UInt64) (cmd : UInt64) : PMem.M UInt32 := do
  __mavlink_mission_item_int_t.__mavlink_mission_item_int_t'2 (fp + 0) input_packet
  let mut selector : UInt64 := (0 : UInt64)
  let mut selector_error : UInt32 := (6 : UInt32)
  let t'1 ← PMem.ldU16 ((fp + 0) + 30)
  let sw'2 := UInt32.toInt32 (UInt16.toUInt32 (t'1))
  if sw'2 == (195 : Int32) || sw'2 == (197 : Int32) then
    let t'3 ← PMem.ldF32 (fp + 0)
    if (Binary32.isNaN t'3) then
      let t'4 := Int32.toBinary32 ((0 : Int32))
      PMem.stF32 (fp + 0) t'4
    let t'5 := (fp + 0)
    selector := t'5
  else if sw'2 == (2000 : Int32) || sw'2 == (2001 : Int32) || sw'2 == (534 : Int32) || sw'2 == (196 : Int32) then
    let t'6 := (fp + 0)
    selector := t'6
  else if sw'2 == (531 : Int32) || sw'2 == (532 : Int32) || sw'2 == (2500 : Int32) then
    let t'7 ← PMem.ldF32 ((fp + 0) + 8)
    if (Binary32.isNaN t'7) then
      let t'8 := Int32.toBinary32 ((0 : Int32))
      PMem.stF32 ((fp + 0) + 8) t'8
    let t'9 := ((fp + 0) + 8)
    selector := t'9
    selector_error := (8 : UInt32)
  else if sw'2 == (2501 : Int32) then
    let t'10 ← PMem.ldF32 ((fp + 0) + 4)
    if (Binary32.isNaN t'10) then
      let t'11 := Int32.toBinary32 ((0 : Int32))
      PMem.stF32 ((fp + 0) + 4) t'11
    let t'12 := ((fp + 0) + 4)
    selector := t'12
    selector_error := (7 : UInt32)
  else if sw'2 == (206 : Int32) then
    let t'13 ← PMem.ldF32 ((fp + 0) + 12)
    if (Binary32.isNaN t'13) then
      let t'14 := Int32.toBinary32 ((0 : Int32))
      PMem.stF32 ((fp + 0) + 12) t'14
    let t'15 := ((fp + 0) + 12)
    selector := t'15
    selector_error := (9 : UInt32)
  else if sw'2 == (1000 : Int32) then
    let t'16 ← PMem.ldF32 ((fp + 0) + 24)
    if (Binary32.isNaN t'16) then
      let t'17 := Int32.toBinary32 ((0 : Int32))
      PMem.stF32 ((fp + 0) + 24) t'17
    let t'18 := ((fp + 0) + 24)
    selector := t'18
    selector_error := (12 : UInt32)
  else
    pure ()
  let mut sc'27 := (selector != (0 : UInt64))
  if sc'27 then
    let t'19 ← PMem.ldF32 selector
    let mut sc'21 := !(Binary32.isFinite t'19)
    if !sc'21 then
      let t'20 ← PMem.ldF32 selector
      sc'21 := (decide (t'20 < (Int32.toBinary32 ((0 : Int32)))))
    let mut sc'23 := sc'21
    if !sc'23 then
      let t'22 ← PMem.ldF32 selector
      sc'23 := (decide (t'22 > (Int32.toBinary32 ((255 : Int32)))))
    let mut sc'26 := sc'23
    if !sc'26 then
      let t'24 ← PMem.ldF32 selector
      let t'25 ← PMem.ldF32 selector
      sc'26 := (decide (t'24 > (Binary32.floor t'25)))
    sc'27 := sc'26
  if sc'27 then
    return selector_error
  discard <| PMem.memset ((fp + 40) + 0) 0 2
  discard <| PMem.memset ((fp + 40) + 2) 0 2
  discard <| PMem.memset ((fp + 40) + 4) 0 2
  AP_Mission.Content.Content ((fp + 40) + 8)
  discard <| PMem.memset ((fp + 40) + 24) 0 1
  discard <| PMem.memcpy cmd (fp + 40) 28
  discard <| pure (cmd)
  let t'28 ← PMem.ldU16 ((fp + 0) + 28)
  PMem.stU16 cmd t'28
  let t'29 ← PMem.ldU16 ((fp + 0) + 30)
  PMem.stU16 (cmd + 2) t'29
  Location.Location (fp + 72)
  discard <| PMem.memcpy (cmd + 8) (fp + 72) 16
  discard <| pure ((cmd + 8))
  let t'30 ← AP_Mission.sanity_check_params (fp + 0)
  let mut param_check : UInt32 := t'30
  if ((UInt32.toInt32 (param_check)) != (UInt32.toInt32 ((0 : UInt32)))) then
    return param_check
  let t'31 ← PMem.ldU16 (cmd + 2)
  let sw'32 := UInt32.toInt32 (UInt16.toUInt32 (t'31))
  if (decide ((0 : Int32) ≤ sw'32) && decide (sw'32 ≤ (1 : Int32))) then
    return (5 : UInt32)
  else if sw'32 == (16 : Int32) then
    let t'33 ← PMem.ldF32 (fp + 0)
    let mut sc'35 := (decide (t'33 < (Int32.toBinary32 ((0 : Int32)))))
    if !sc'35 then
      let t'34 ← PMem.ldF32 (fp + 0)
      sc'35 := (decide (t'34 > (Int32.toBinary32 ((65535 : Int32)))))
    if sc'35 then
      return (6 : UInt32)
    let t'36 ← PMem.ldF32 (fp + 0)
    let t'37 := Binary32.toUInt16 (t'36)
    PMem.stU16 (cmd + 4) t'37
  else if sw'32 == (17 : Int32) then
    let t'38 ← PMem.ldF32 ((fp + 0) + 8)
    let t'39 := Binary32.toUInt16 ((Binary32.abs t'38))
    PMem.stU16 (cmd + 4) t'39
    let t'40 ← PMem.ldF32 ((fp + 0) + 8)
    let t'41 := if (decide (t'40 < (Int32.toBinary32 ((0 : Int32))))) then (1 : UInt8) else (0 : UInt8)
    PMem.stBits (cmd + 8) 1 1 (UInt8.toUInt64 (t'41))
  else if sw'32 == (18 : Int32) then
    let t'42 ← PMem.ldF32 (fp + 0)
    PMem.stF32 (fp + 88) t'42
    let t'43 ← PMem.ldF32 (fp + 88)
    let mut sc'45 := (decide (t'43 > (Int32.toBinary32 ((0 : Int32)))))
    if sc'45 then
      let t'44 ← PMem.ldF32 (fp + 88)
      sc'45 := (decide (t'44 < (Int32.toBinary32 ((1 : Int32)))))
    if sc'45 then
      let t'46 ← PMem.ldF32 (fp + 88)
      let t'47 := (t'46 * (Binary64.toBinary32 ((Binary64.ofBits 0x4070000000000000 /- 256 -/))))
      PMem.stF32 (fp + 88) t'47
      let t'48 := (cmd + 24)
      let t'49 ← PMem.ldU8 t'48
      let t'50 := (t'49 ||| (UInt32.toUInt8 (((1 : UInt32) <<< (Int32.toUInt32 ((1 : Int32)))))))
      PMem.stU8 t'48 t'50
    PMem.stI32 (fp + 92) (255 : Int32)
    let t'51 ← MIN'int_float (fp + 92) (fp + 88)
    let t'52 := Binary32.toUInt16 (t'51)
    PMem.stU16 (cmd + 4) t'52
    let mut radius_m : UInt8 := default  -- uninitialized in C
    let t'53 ← PMem.ldF32 ((fp + 0) + 8)
    let mut abs_radius : Binary32 := (Binary32.abs t'53)
    if (decide (abs_radius ≤ (Int32.toBinary32 ((255 : Int32))))) then
      let t'54 := Binary32.toUInt8 (abs_radius)
      radius_m := t'54
    else
      PMem.stI32 (fp + 96) (255 : Int32)
      PMem.stF32 (fp + 100) (abs_radius * (Binary64.toBinary32 ((Binary64.ofBits 0x3fb999999999999a /- 10000000000000001/100000000000000000 -/))))
      let t'55 ← MIN'int_float (fp + 96) (fp + 100)
      let t'56 := Binary32.toUInt8 (t'55)
      radius_m := t'56
      let t'57 := (cmd + 24)
      let t'58 ← PMem.ldU8 t'57
      let t'59 := (t'58 ||| (UInt32.toUInt8 (((1 : UInt32) <<< (Int32.toUInt32 ((0 : Int32)))))))
      PMem.stU8 t'57 t'59
    let t'60 := (cmd + 4)
    let t'61 ← PMem.ldU16 t'60
    let t'62 := (t'61 ||| (Int16.toUInt16 (Int32.toInt16 (((UInt32.toInt32 (UInt8.toUInt32 (radius_m))) <<< (8 : Int32))))))
    PMem.stU16 t'60 t'62
    let t'63 ← PMem.ldF32 ((fp + 0) + 8)
    let t'64 := if (decide (t'63 < (Int32.toBinary32 ((0 : Int32))))) then (1 : UInt8) else (0 : UInt8)
    PMem.stBits (cmd + 8) 1 1 (UInt8.toUInt64 (t'64))
    let t'65 ← PMem.ldF32 ((fp + 0) + 12)
    let t'66 := if (decide (t'65 > (Int32.toBinary32 ((0 : Int32))))) then (1 : UInt8) else (0 : UInt8)
    PMem.stBits (cmd + 8) 4 1 (UInt8.toUInt64 (t'66))
  else if sw'32 == (19 : Int32) then
    let t'67 ← PMem.ldF32 (fp + 0)
    let t'68 := Binary32.toUInt16 (t'67)
    PMem.stU16 (cmd + 4) t'68
    let t'69 ← PMem.ldF32 ((fp + 0) + 8)
    let t'70 := if (decide (t'69 < (Int32.toBinary32 ((0 : Int32))))) then (1 : UInt8) else (0 : UInt8)
    PMem.stBits (cmd + 8) 1 1 (UInt8.toUInt64 (t'70))
    let t'71 ← PMem.ldF32 ((fp + 0) + 12)
    let t'72 := if (decide (t'71 > (Int32.toBinary32 ((0 : Int32))))) then (1 : UInt8) else (0 : UInt8)
    PMem.stBits (cmd + 8) 4 1 (UInt8.toUInt64 (t'72))
  else if sw'32 == (20 : Int32) then
    pure ()
  else if sw'32 == (21 : Int32) then
    let t'73 ← PMem.ldF32 (fp + 0)
    let t'74 := Binary32.toUInt16 (t'73)
    PMem.stU16 (cmd + 4) t'74
    let t'75 ← PMem.ldF32 ((fp + 0) + 12)
    if !(Binary32.isNaN t'75) then
      let t'76 ← PMem.ldF32 ((fp + 0) + 12)
      let t'77 ← is_negative'float t'76
      let t'78 := if t'77 then (1 : UInt8) else (0 : UInt8)
      PMem.stBits (cmd + 8) 1 1 (UInt8.toUInt64 (t'78))
  else if sw'32 == (22 : Int32) then
    let t'79 ← PMem.ldF32 (fp + 0)
    let t'80 := Binary32.toUInt16 (t'79)
    PMem.stU16 (cmd + 4) t'80
  else if sw'32 == (30 : Int32) then
    let t'81 ← PMem.ldF32 (fp + 0)
    let t'82 := Binary32.toUInt16 (t'81)
    PMem.stU16 (cmd + 4) t'82
  else if sw'32 == (31 : Int32) then
    let t'83 ← PMem.ldF32 ((fp + 0) + 4)
    let t'84 := Binary32.toUInt16 ((Binary32.abs t'83))
    PMem.stU16 (cmd + 4) t'84
    let t'85 ← PMem.ldF32 ((fp + 0) + 4)
    let t'86 := if (decide (t'85 < (Int32.toBinary32 ((0 : Int32))))) then (1 : UInt8) else (0 : UInt8)
    PMem.stBits (cmd + 8) 1 1 (UInt8.toUInt64 (t'86))
    let t'87 ← PMem.ldF32 ((fp + 0) + 12)
    let t'88 := if (decide (t'87 > (Int32.toBinary32 ((0 : Int32))))) then (1 : UInt8) else (0 : UInt8)
    PMem.stBits (cmd + 8) 4 1 (UInt8.toUInt64 (t'88))
  else if sw'32 == (36 : Int32) then
    let t'89 ← PMem.ldF32 (fp + 0)
    let t'90 ← is_negative'float t'89
    let t'91 := if t'90 then (1 : UInt8) else (0 : UInt8)
    PMem.stBits (cmd + 8) 1 1 (UInt8.toUInt64 (t'91))
    let t'92 ← PMem.ldF32 (fp + 0)
    let t'93 := Binary32.toUInt16 ((Binary32.abs t'92))
    PMem.stU16 (cmd + 4) t'93
  else if sw'32 == (82 : Int32) then
    let t'94 ← PMem.ldF32 (fp + 0)
    let t'95 := Binary32.toUInt16 (t'94)
    PMem.stU16 (cmd + 4) t'95
  else if sw'32 == (92 : Int32) then
    let t'96 ← PMem.ldF32 (fp + 0)
    let t'97 := Binary32.toUInt16 (t'96)
    PMem.stU16 (cmd + 4) t'97
  else if sw'32 == (93 : Int32) then
    let t'98 ← PMem.ldF32 (fp + 0)
    PMem.stF32 (cmd + 8) t'98
    let t'99 ← PMem.ldF32 ((fp + 0) + 4)
    let t'100 := Binary32.toInt8 (t'99)
    PMem.stI8 ((cmd + 8) + 4) t'100
    let t'101 ← PMem.ldF32 ((fp + 0) + 8)
    let t'102 := Binary32.toInt8 (t'101)
    PMem.stI8 ((cmd + 8) + 5) t'102
    let t'103 ← PMem.ldF32 ((fp + 0) + 12)
    let t'104 := Binary32.toInt8 (t'103)
    PMem.stI8 ((cmd + 8) + 6) t'104
  else if sw'32 == (112 : Int32) then
    let t'105 ← PMem.ldF32 (fp + 0)
    PMem.stF32 (cmd + 8) t'105
  else if sw'32 == (114 : Int32) then
    let t'106 ← PMem.ldF32 (fp + 0)
    PMem.stF32 (cmd + 8) t'106
  else if sw'32 == (115 : Int32) then
    let t'107 ← PMem.ldF32 (fp + 0)
    PMem.stF32 (cmd + 8) t'107
    let t'108 ← PMem.ldF32 ((fp + 0) + 4)
    PMem.stF32 ((cmd + 8) + 4) t'108
    let t'109 ← PMem.ldF32 ((fp + 0) + 8)
    let t'110 := Binary32.toInt8 (t'109)
    PMem.stI8 ((cmd + 8) + 8) t'110
    let t'111 ← PMem.ldF32 ((fp + 0) + 12)
    let t'112 := Binary32.toUInt8 (t'111)
    PMem.stU8 ((cmd + 8) + 9) t'112
  else if sw'32 == (177 : Int32) || sw'32 == (601 : Int32) then
    let t'113 ← PMem.ldF32 (fp + 0)
    let t'114 := Binary32.toUInt16 (t'113)
    PMem.stU16 (cmd + 8) t'114
    let t'115 ← PMem.ldF32 ((fp + 0) + 4)
    let t'116 := Binary32.toInt16 (t'115)
    PMem.stI16 ((cmd + 8) + 2) t'116
  else if sw'32 == (600 : Int32) then
    let t'117 ← PMem.ldF32 (fp + 0)
    let t'118 := Binary32.toUInt16 (t'117)
    PMem.stU16 (cmd + 8) t'118
  else if sw'32 == (178 : Int32) then
    let t'119 ← PMem.ldF32 (fp + 0)
    let t'120 := Binary32.toUInt8 (t'119)
    PMem.stU8 (cmd + 8) t'120
    let t'121 ← PMem.ldF32 ((fp + 0) + 4)
    PMem.stF32 ((cmd + 8) + 1) t'121
    let t'122 ← PMem.ldF32 ((fp + 0) + 8)
    PMem.stF32 ((cmd + 8) + 5) t'122
  else if sw'32 == (179 : Int32) then
    let t'123 ← PMem.ldF32 (fp + 0)
    let t'124 := Binary32.toUInt16 (t'123)
    PMem.stU16 (cmd + 4) t'124
  else if sw'32 == (181 : Int32) then
    let t'125 ← PMem.ldF32 (fp + 0)
    let t'126 := Binary32.toUInt8 (t'125)
    PMem.stU8 (cmd + 8) t'126
    let t'127 ← PMem.ldF32 ((fp + 0) + 4)
    let t'128 := Binary32.toUInt8 (t'127)
    PMem.stU8 ((cmd + 8) + 1) t'128
  else if sw'32 == (182 : Int32) then
    let t'129 ← PMem.ldF32 (fp + 0)
    let t'130 := Binary32.toUInt8 (t'129)
    PMem.stU8 (cmd + 8) t'130
    let t'131 ← PMem.ldF32 ((fp + 0) + 4)
    let t'132 := Binary32.toInt16 (t'131)
    PMem.stI16 ((cmd + 8) + 1) t'132
    let t'133 ← PMem.ldF32 ((fp + 0) + 8)
    PMem.stF32 ((cmd + 8) + 3) t'133
  else if sw'32 == (183 : Int32) then
    let t'134 ← PMem.ldF32 (fp + 0)
    let t'135 := Binary32.toUInt8 (t'134)
    PMem.stU8 (cmd + 8) t'135
    let t'136 ← PMem.ldF32 ((fp + 0) + 4)
    let t'137 := Binary32.toUInt16 (t'136)
    PMem.stU16 ((cmd + 8) + 1) t'137
  else if sw'32 == (184 : Int32) then
    let t'138 ← PMem.ldF32 (fp + 0)
    let t'139 := Binary32.toUInt8 (t'138)
    PMem.stU8 (cmd + 8) t'139
    let t'140 ← PMem.ldF32 ((fp + 0) + 4)
    let t'141 := Binary32.toUInt16 (t'140)
    PMem.stU16 ((cmd + 8) + 1) t'141
    let t'142 ← PMem.ldF32 ((fp + 0) + 8)
    let t'143 := Binary32.toInt16 (t'142)
    PMem.stI16 ((cmd + 8) + 3) t'143
    let t'144 ← PMem.ldF32 ((fp + 0) + 12)
    PMem.stF32 ((cmd + 8) + 5) t'144
  else if sw'32 == (188 : Int32) || sw'32 == (189 : Int32) then
    pure ()
  else if sw'32 == (191 : Int32) then
    pure ()
  else if sw'32 == (195 : Int32) || sw'32 == (197 : Int32) then
    let t'145 ← PMem.ldF32 (fp + 0)
    let t'146 := Binary32.toUInt16 (t'145)
    PMem.stU16 (cmd + 4) t'146
  else if sw'32 == (201 : Int32) then
    let t'147 ← PMem.ldF32 (fp + 0)
    let t'148 := Binary32.toUInt16 (t'147)
    PMem.stU16 (cmd + 4) t'148
  else if sw'32 == (202 : Int32) then
    let t'149 ← PMem.ldF32 (fp + 0)
    let t'150 := Binary32.toUInt8 (t'149)
    PMem.stU8 (cmd + 8) t'150
    let t'151 ← PMem.ldF32 ((fp + 0) + 4)
    let t'152 := Binary32.toUInt16 (t'151)
    PMem.stU16 ((cmd + 8) + 1) t'152
    let t'153 ← PMem.ldF32 ((fp + 0) + 8)
    let t'154 := Binary32.toUInt8 (t'153)
    PMem.stU8 ((cmd + 8) + 3) t'154
    let t'155 ← PMem.ldF32 ((fp + 0) + 12)
    let t'156 := Binary32.toUInt16 (t'155)
    PMem.stU16 ((cmd + 8) + 4) t'156
    let t'157 ← PMem.ldI32 ((fp + 0) + 16)
    let t'158 := Int8.toUInt8 (Int32.toInt8 (t'157))
    PMem.stU8 ((cmd + 8) + 6) t'158
    let t'159 ← PMem.ldI32 ((fp + 0) + 20)
    let t'160 := Int8.toUInt8 (Int32.toInt8 (t'159))
    PMem.stU8 ((cmd + 8) + 7) t'160
    let t'161 ← PMem.ldF32 ((fp + 0) + 24)
    PMem.stF32 ((cmd + 8) + 8) t'161
  else if sw'32 == (203 : Int32) then
    let t'162 ← PMem.ldF32 (fp + 0)
    let t'163 := Binary32.toUInt8 (t'162)
    PMem.stU8 (cmd + 8) t'163
    let t'164 ← PMem.ldF32 ((fp + 0) + 4)
    let t'165 := Binary32.toUInt8 (t'164)
    PMem.stU8 ((cmd + 8) + 1) t'165
    let t'166 ← PMem.ldF32 ((fp + 0) + 8)
    let t'167 := Binary32.toInt8 (t'166)
    PMem.stI8 ((cmd + 8) + 2) t'167
    let t'168 ← PMem.ldF32 ((fp + 0) + 12)
    let t'169 := Binary32.toUInt8 (t'168)
    PMem.stU8 ((cmd + 8) + 3) t'169
    let t'170 ← PMem.ldI32 ((fp + 0) + 16)
    let t'171 := Int8.toUInt8 (Int32.toInt8 (t'170))
    PMem.stU8 ((cmd + 8) + 4) t'171
    let t'172 ← PMem.ldI32 ((fp + 0) + 20)
    let t'173 := Int8.toUInt8 (Int32.toInt8 (t'172))
    PMem.stU8 ((cmd + 8) + 5) t'173
  else if sw'32 == (205 : Int32) then
    let t'174 ← PMem.ldF32 (fp + 0)
    PMem.stF32 (cmd + 8) t'174
    let t'175 ← PMem.ldF32 ((fp + 0) + 4)
    PMem.stF32 ((cmd + 8) + 4) t'175
    let t'176 ← PMem.ldF32 ((fp + 0) + 8)
    PMem.stF32 ((cmd + 8) + 8) t'176
  else if sw'32 == (206 : Int32) then
    let t'177 ← PMem.ldF32 (fp + 0)
    PMem.stF32 (cmd + 8) t'177
    let t'178 ← PMem.ldF32 ((fp + 0) + 8)
    let t'179 := Binary32.toUInt8 (t'178)
    PMem.stU8 ((cmd + 8) + 4) t'179
    let t'180 ← PMem.ldF32 ((fp + 0) + 12)
    let t'181 := Binary32.toUInt8 (t'180)
    PMem.stU8 ((cmd + 8) + 5) t'181
  else if sw'32 == (207 : Int32) then
    let t'182 ← PMem.ldF32 (fp + 0)
    let t'183 := Binary32.toUInt16 (t'182)
    PMem.stU16 (cmd + 4) t'183
  else if sw'32 == (218 : Int32) then
    let t'184 ← PMem.ldF32 (fp + 0)
    let t'185 := Binary32.toUInt16 (t'184)
    PMem.stU16 (cmd + 8) t'185
    let t'186 ← PMem.ldF32 ((fp + 0) + 4)
    let t'187 := Binary32.toUInt8 (t'186)
    PMem.stU8 ((cmd + 8) + 2) t'187
  else if sw'32 == (208 : Int32) then
    let t'188 ← PMem.ldF32 (fp + 0)
    let t'189 := Binary32.toUInt16 (t'188)
    PMem.stU16 (cmd + 4) t'189
  else if sw'32 == (210 : Int32) then
    let t'190 ← PMem.ldF32 (fp + 0)
    let t'191 := Binary32.toUInt16 (t'190)
    PMem.stU16 (cmd + 4) t'191
  else if sw'32 == (222 : Int32) then
    let t'192 ← PMem.ldF32 (fp + 0)
    let t'193 := Binary32.toUInt16 (t'192)
    PMem.stU16 (cmd + 4) t'193
    let t'194 ← PMem.ldF32 ((fp + 0) + 4)
    PMem.stF32 (cmd + 8) t'194
    let t'195 ← PMem.ldF32 ((fp + 0) + 8)
    PMem.stF32 ((cmd + 8) + 4) t'195
    let t'196 ← PMem.ldF32 ((fp + 0) + 12)
    PMem.stF32 ((cmd + 8) + 8) t'196
  else if sw'32 == (212 : Int32) then
    let t'197 ← PMem.ldF32 (fp + 0)
    let t'198 := Binary32.toUInt16 (t'197)
    PMem.stU16 (cmd + 4) t'198
  else if sw'32 == (83 : Int32) then
    let t'199 ← PMem.ldF32 (fp + 0)
    PMem.stF32 (cmd + 8) t'199
    let t'200 ← PMem.ldF32 ((fp + 0) + 4)
    PMem.stF32 ((cmd + 8) + 4) t'200
    let t'201 ← PMem.ldF32 ((fp + 0) + 8)
    let t'202 := Binary32.toUInt8 (t'201)
    PMem.stU8 ((cmd + 8) + 8) t'202
  else if sw'32 == (84 : Int32) then
    pure ()
  else if sw'32 == (85 : Int32) then
    let t'203 ← PMem.ldF32 (fp + 0)
    let t'204 := UInt32.toUInt16 ((Binary32.toUInt32 (t'203)))
    PMem.stU16 (cmd + 4) t'204
  else if sw'32 == (3000 : Int32) then
    let t'205 ← PMem.ldF32 (fp + 0)
    let t'206 := Binary32.toUInt8 (t'205)
    PMem.stU8 (cmd + 8) t'206
  else if sw'32 == (194 : Int32) then
    let t'207 ← PMem.ldF32 (fp + 0)
    let t'208 := Binary32.toUInt16 (t'207)
    PMem.stU16 (cmd + 4) t'208
  else if sw'32 == (223 : Int32) then
    let t'209 ← PMem.ldF32 (fp + 0)
    let t'210 := (decide (t'209 > (Int32.toBinary32 ((0 : Int32)))))
    PMem.stB (cmd + 8) t'210
    let t'211 ← PMem.ldF32 ((fp + 0) + 4)
    let t'212 := (decide (t'211 > (Int32.toBinary32 ((0 : Int32)))))
    PMem.stB ((cmd + 8) + 1) t'212
    let t'213 ← PMem.ldF32 ((fp + 0) + 8)
    let t'214 := Binary32.toUInt16 ((t'213 * (Int32.toBinary32 ((100 : Int32)))))
    PMem.stU16 ((cmd + 8) + 2) t'214
    let t'215 ← PMem.ldF32 ((fp + 0) + 12)
    let t'216 := (((Binary32.toUInt32 (t'215)) &&& (1 : UInt32)) != (Int32.toUInt32 ((0 : Int32))))
    PMem.stB ((cmd + 8) + 4) t'216
  else if sw'32 == (213 : Int32) then
    let t'217 ← PMem.ldF32 (fp + 0)
    PMem.stF32 (cmd + 8) t'217
    let t'218 ← PMem.ldF32 ((fp + 0) + 4)
    PMem.stF32 ((cmd + 8) + 4) t'218
    let t'219 ← PMem.ldF32 ((fp + 0) + 8)
    let t'220 := Binary32.toUInt8 (t'219)
    PMem.stU8 ((cmd + 8) + 8) t'220
  else if sw'32 == (42600 : Int32) then
    let t'221 ← PMem.ldF32 (fp + 0)
    let t'222 := Binary32.toUInt8 (t'221)
    PMem.stU8 (cmd + 8) t'222
    let t'223 ← PMem.ldF32 ((fp + 0) + 4)
    let t'224 := Binary32.toUInt8 (t'223)
    PMem.stU8 ((cmd + 8) + 1) t'224
    let t'225 ← PMem.ldF32 ((fp + 0) + 8)
    PMem.stF32 ((cmd + 8) + 2) t'225
    let t'226 ← PMem.ldF32 ((fp + 0) + 12)
    PMem.stF32 ((cmd + 8) + 6) t'226
  else if sw'32 == (215 : Int32) then
    let t'227 ← PMem.ldF32 (fp + 0)
    let t'228 := Binary32.toUInt16 (t'227)
    PMem.stU16 (cmd + 4) t'228
  else if sw'32 == (216 : Int32) then
    let t'229 ← PMem.ldF32 (fp + 0)
    let t'230 := Binary32.toUInt16 (t'229)
    PMem.stU16 (cmd + 4) t'230
  else if sw'32 == (217 : Int32) then
    let t'231 ← PMem.ldF32 (fp + 0)
    let t'232 := Binary32.toUInt16 (t'231)
    PMem.stU16 (cmd + 4) t'232
    let t'233 ← PMem.ldF32 ((fp + 0) + 4)
    PMem.stF32 (cmd + 8) t'233
    let t'234 ← PMem.ldF32 ((fp + 0) + 8)
    PMem.stF32 ((cmd + 8) + 4) t'234
    let t'235 ← PMem.ldF32 ((fp + 0) + 12)
    PMem.stF32 ((cmd + 8) + 8) t'235
  else if sw'32 == (42703 : Int32) then
    let t'236 ← PMem.ldF32 (fp + 0)
    let t'237 ← constrain_value_line'float t'236 (Int32.toBinary32 ((0 : Int32))) (Int32.toBinary32 ((65535 : Int32))) (Int32.toUInt32 ((1479 : Int32)))
    let t'238 := Binary32.toUInt16 (t'237)
    PMem.stU16 (cmd + 8) t'238
    let t'239 ← PMem.ldF32 ((fp + 0) + 4)
    let mut c'240 : Binary32 := default
    if (decide ((Binary32.abs t'239) ≤ (Int32.toBinary32 ((180 : Int32))))) then
      let t'241 ← PMem.ldF32 ((fp + 0) + 4)
      c'240 := t'241
    else
      c'240 := Int32.toBinary32 ((0 : Int32))
    let t'242 := Binary32.toInt16 (c'240)
    PMem.stI16 ((cmd + 8) + 2) t'242
    let t'243 ← PMem.ldF32 ((fp + 0) + 8)
    let mut c'244 : Binary32 := default
    if (decide ((Binary32.abs t'243) ≤ (Int32.toBinary32 ((90 : Int32))))) then
      let t'245 ← PMem.ldF32 ((fp + 0) + 8)
      c'244 := t'245
    else
      c'244 := Int32.toBinary32 ((0 : Int32))
    let t'246 := Binary32.toInt8 (c'244)
    PMem.stI8 ((cmd + 8) + 4) t'246
    let t'247 ← PMem.ldF32 ((fp + 0) + 12)
    let mut sc'249 := (decide (t'247 ≥ (Int32.toBinary32 ((-(180 : Int32))))))
    if sc'249 then
      let t'248 ← PMem.ldF32 ((fp + 0) + 12)
      sc'249 := (decide (t'248 ≤ (Int32.toBinary32 ((360 : Int32)))))
    let mut c'250 : Binary32 := default
    if sc'249 then
      let t'251 ← PMem.ldF32 ((fp + 0) + 12)
      c'250 := t'251
    else
      c'250 := Int32.toBinary32 ((0 : Int32))
    let t'252 := Binary32.toInt16 (c'250)
    PMem.stI16 ((cmd + 8) + 5) t'252
    let t'253 ← PMem.ldI32 ((fp + 0) + 16)
    let t'254 := Int32.toInt16 (t'253)
    PMem.stI16 ((cmd + 8) + 7) t'254
  else if sw'32 == (193 : Int32) then
    let t'255 ← PMem.ldF32 (fp + 0)
    let t'256 := Binary32.toUInt16 (t'255)
    PMem.stU16 (cmd + 4) t'256
  else if sw'32 == (1000 : Int32) then
    let t'257 ← PMem.ldF32 (fp + 0)
    let t'258 := Binary32.toInt8 (t'257)
    PMem.stI8 (cmd + 8) t'258
    let t'259 ← PMem.ldF32 ((fp + 0) + 4)
    let t'260 := Binary32.toInt16 (t'259)
    PMem.stI16 ((cmd + 8) + 1) t'260
    let t'261 ← PMem.ldF32 ((fp + 0) + 8)
    let t'262 := Binary32.toInt8 (t'261)
    PMem.stI8 ((cmd + 8) + 3) t'262
    let t'263 ← PMem.ldF32 ((fp + 0) + 12)
    let t'264 := Binary32.toInt8 (t'263)
    PMem.stI8 ((cmd + 8) + 4) t'264
    let t'265 ← PMem.ldI32 ((fp + 0) + 16)
    let t'266 := Int8.toUInt8 (Int32.toInt8 (t'265))
    PMem.stU8 ((cmd + 8) + 5) t'266
    let t'267 ← PMem.ldF32 ((fp + 0) + 24)
    let t'268 := Binary32.toUInt8 (t'267)
    PMem.stU8 ((cmd + 8) + 6) t'268
  else if sw'32 == (2000 : Int32) then
    let t'269 ← PMem.ldF32 (fp + 0)
    let t'270 := Binary32.toUInt8 (t'269)
    PMem.stU8 (cmd + 8) t'270
    let t'271 ← PMem.ldF32 ((fp + 0) + 4)
    PMem.stF32 ((cmd + 8) + 1) t'271
    let t'272 ← PMem.ldF32 ((fp + 0) + 8)
    let t'273 := Binary32.toUInt16 (t'272)
    PMem.stU16 ((cmd + 8) + 5) t'273
    let t'274 ← PMem.ldF32 ((fp + 0) + 12)
    let t'275 := Binary32.toUInt16 (t'274)
    PMem.stU16 ((cmd + 8) + 7) t'275
  else if sw'32 == (2001 : Int32) then
    let t'276 ← PMem.ldF32 (fp + 0)
    let t'277 := Binary32.toUInt16 (t'276)
    PMem.stU16 (cmd + 4) t'277
  else if sw'32 == (531 : Int32) then
    let t'278 ← PMem.ldF32 (fp + 0)
    let t'279 := Binary32.toUInt8 (t'278)
    PMem.stU8 (cmd + 8) t'279
    let t'280 ← PMem.ldF32 ((fp + 0) + 4)
    PMem.stF32 ((cmd + 8) + 1) t'280
    let t'281 ← PMem.ldF32 ((fp + 0) + 8)
    let t'282 := Binary32.toUInt8 (t'281)
    PMem.stU8 ((cmd + 8) + 5) t'282
  else if sw'32 == (532 : Int32) then
    let t'283 ← PMem.ldF32 (fp + 0)
    let t'284 := Binary32.toUInt8 (t'283)
    PMem.stU8 (cmd + 8) t'284
    let t'285 ← PMem.ldF32 ((fp + 0) + 4)
    PMem.stF32 ((cmd + 8) + 1) t'285
    let t'286 ← PMem.ldF32 ((fp + 0) + 8)
    let t'287 := Binary32.toUInt8 (t'286)
    PMem.stU8 ((cmd + 8) + 5) t'287
  else if sw'32 == (534 : Int32) then
    let t'288 ← PMem.ldF32 (fp + 0)
    let t'289 := Binary32.toUInt8 (t'288)
    PMem.stU8 (cmd + 8) t'289
    let t'290 ← PMem.ldF32 ((fp + 0) + 4)
    let t'291 := Binary32.toUInt8 (t'290)
    PMem.stU8 ((cmd + 8) + 1) t'291
    let t'292 ← PMem.ldF32 ((fp + 0) + 8)
    let t'293 := Binary32.toUInt8 (t'292)
    PMem.stU8 ((cmd + 8) + 2) t'293
  else if sw'32 == (2500 : Int32) then
    let t'294 ← PMem.ldF32 (fp + 0)
    let mut sc'296 := !(Binary32.isFinite t'294)
    if !sc'296 then
      let t'295 ← PMem.ldF32 (fp + 0)
      sc'296 := (decide (t'295 < (Int32.toBinary32 ((0 : Int32)))))
    let mut sc'298 := sc'296
    if !sc'298 then
      let t'297 ← PMem.ldF32 (fp + 0)
      sc'298 := (decide (t'297 > (Int32.toBinary32 ((255 : Int32)))))
    let mut sc'301 := sc'298
    if !sc'301 then
      let t'299 ← PMem.ldF32 (fp + 0)
      let t'300 ← PMem.ldF32 (fp + 0)
      sc'301 := (decide (t'299 > (Binary32.floor t'300)))
    if sc'301 then
      return (6 : UInt32)
    let t'302 ← PMem.ldF32 ((fp + 0) + 4)
    let mut sc'304 := !(Binary32.isFinite t'302)
    if !sc'304 then
      let t'303 ← PMem.ldF32 ((fp + 0) + 4)
      sc'304 := (decide (t'303 < (Int32.toBinary32 ((0 : Int32)))))
    if sc'304 then
      return (7 : UInt32)
    let t'305 ← PMem.ldF32 (fp + 0)
    let t'306 := Binary32.toUInt8 (t'305)
    PMem.stU8 (cmd + 8) t'306
    let t'307 ← PMem.ldF32 ((fp + 0) + 8)
    let t'308 := Binary32.toUInt8 (t'307)
    PMem.stU8 ((cmd + 8) + 1) t'308
    let t'309 ← PMem.ldF32 ((fp + 0) + 4)
    PMem.stF32 ((cmd + 8) + 2) t'309
  else if sw'32 == (2501 : Int32) then
    let t'310 ← PMem.ldF32 (fp + 0)
    let mut sc'312 := !(Binary32.isFinite t'310)
    if !sc'312 then
      let t'311 ← PMem.ldF32 (fp + 0)
      sc'312 := (decide (t'311 < (Int32.toBinary32 ((0 : Int32)))))
    let mut sc'314 := sc'312
    if !sc'314 then
      let t'313 ← PMem.ldF32 (fp + 0)
      sc'314 := (decide (t'313 > (Int32.toBinary32 ((255 : Int32)))))
    let mut sc'317 := sc'314
    if !sc'317 then
      let t'315 ← PMem.ldF32 (fp + 0)
      let t'316 ← PMem.ldF32 (fp + 0)
      sc'317 := (decide (t'315 > (Binary32.floor t'316)))
    if sc'317 then
      return (6 : UInt32)
    let t'318 ← PMem.ldF32 (fp + 0)
    let t'319 := Binary32.toUInt8 (t'318)
    PMem.stU8 (cmd + 8) t'319
    let t'320 ← PMem.ldF32 ((fp + 0) + 4)
    let t'321 := Binary32.toUInt8 (t'320)
    PMem.stU8 ((cmd + 8) + 1) t'321
  else if sw'32 == (196 : Int32) then
    let t'322 ← PMem.ldF32 (fp + 0)
    let t'323 := Binary32.toUInt8 (t'322)
    PMem.stU8 ((cmd + 8) + 6) t'323
    let t'324 ← PMem.ldI32 ((fp + 0) + 20)
    let t'325 := Int32.toInt16 ((t'324 * (100 : Int32)))
    PMem.stI16 (cmd + 8) t'325
    let t'326 ← PMem.ldI32 ((fp + 0) + 16)
    let t'327 := Int32.toInt16 ((t'326 * (100 : Int32)))
    PMem.stI16 ((cmd + 8) + 2) t'327
    let t'328 ← PMem.ldF32 ((fp + 0) + 24)
    let t'329 := Binary32.toInt16 ((t'328 * (Int32.toBinary32 ((100 : Int32)))))
    PMem.stI16 ((cmd + 8) + 4) t'329
  else
    return (3 : UInt32)
  let t'330 ← PMem.ldU16 (cmd + 2)
  let t'331 ← AP_Mission.stored_in_location t'330
  if t'331 then
    let t'332 ← PMem.ldI32 ((fp + 0) + 16)
    let t'333 ← check_lat t'332
    if !t'333 then
      return (10 : UInt32)
    let t'334 ← PMem.ldI32 ((fp + 0) + 20)
    let t'335 ← check_lng t'334
    if !t'335 then
      return (11 : UInt32)
    let t'336 ← PMem.ldF32 ((fp + 0) + 24)
    let mut sc'338 := (Binary32.isNaN t'336)
    if !sc'338 then
      let t'337 ← PMem.ldF32 ((fp + 0) + 24)
      sc'338 := (decide ((Binary32.abs t'337) ≥ (Int32.toBinary32 ((83000 : Int32)))))
    if sc'338 then
      return (12 : UInt32)
    let t'339 ← PMem.ldI32 ((fp + 0) + 16)
    PMem.stI32 ((cmd + 8) + 8) t'339
    let t'340 ← PMem.ldI32 ((fp + 0) + 20)
    PMem.stI32 ((cmd + 8) + 12) t'340
    let t'341 ← PMem.ldF32 ((fp + 0) + 24)
    let t'342 := Binary32.toInt32 ((t'341 * (Binary32.ofBits 0x42c80000 /- 100 -/)))
    PMem.stI32 ((cmd + 8) + 4) t'342
    let t'343 ← PMem.ldU8 ((fp + 0) + 34)
    let sw'344 := UInt32.toInt32 (UInt8.toUInt32 (t'343))
    if sw'344 == (2 : Int32) || sw'344 == (0 : Int32) || sw'344 == (5 : Int32) then
      let t'345 := Int8.toUInt8 (Int32.toInt8 ((0 : Int32)))
      PMem.stBits (cmd + 8) 0 1 (UInt8.toUInt64 (t'345))
    else if sw'344 == (3 : Int32) || sw'344 == (6 : Int32) then
      let t'346 := Int8.toUInt8 (Int32.toInt8 ((1 : Int32)))
      PMem.stBits (cmd + 8) 0 1 (UInt8.toUInt64 (t'346))
    else
      return (2 : UInt32)
  return (0 : UInt32)

def AP_Mission.mavlink_int_to_mission_cmd (input_packet : UInt64) (cmd : UInt64) : PMem.M UInt32 := do
  let fp ← PMem.enter 104
  let r ← AP_Mission.mavlink_int_to_mission_cmd.body fp input_packet cmd
  PMem.leave fp
  return r

/-- C++ `AP_Mission::AP_Mission : void (mission_cmd_fn_t, mission_cmd_fn_t, mission_complete_fn_t)`, `functor.h:476-497`. -/
def AP_Mission.AP_Mission (this : UInt64) (cmd_start_fn : UInt64) (cmd_verify_fn : UInt64) (mission_complete_fn : UInt64) : PMem.M Unit := do
  AP_Mission.Mission_Flags.Mission_Flags (this + 4)
  discard <| PMem.memcpy (this + 32) cmd_start_fn 16
  discard <| PMem.memcpy (this + 48) cmd_verify_fn 16
  Functor'void.Functor (this + 64) mission_complete_fn
  AP_Param.AP_Param'2 (this + 80)
  AP_Param.AP_Param'2 (this + 82)
  AP_Param.AP_Param'2 (this + 84)
  AP_Mission.Mission_Command.Mission_Command (this + 88)
  AP_Mission.Mission_Command.Mission_Command (this + 116)
  AP_Mission.Mission_Command.Mission_Command (this + 144)
  PMem.stU16 (this + 172) (Int16.toUInt16 (Int32.toInt16 ((0 : Int32))))
  PMem.stU16 (this + 174) (Int16.toUInt16 (Int32.toInt16 ((65535 : Int32))))
  PMem.stU16 (this + 176) (Int16.toUInt16 (Int32.toInt16 ((65535 : Int32))))
  Location.Location (this + 180)
  let t'1 ← PMem.ldU64 (0xbf20 : UInt64) /- &AP_Mission::_singleton -/
  if (t'1 != (0 : UInt64)) then
    pure ()
  PMem.stU64 (0xbf20 : UInt64) /- &AP_Mission::_singleton -/ this
  AP_Param.setup_object_defaults this (0x5180 : UInt64) /- &AP_Mission::var_info -/
  let t'2 := Int16.toUInt16 (Int32.toInt16 ((65535 : Int32)))
  PMem.stU16 (this + 88) t'2
  let t'3 := Int16.toUInt16 (Int32.toInt16 ((65535 : Int32)))
  PMem.stU16 (this + 116) t'3
  return ()

/-- C++ `AP_Mission::check_eeprom_version : void ()`, `AP_Mission.cpp:2521-2531`. -/
def AP_Mission.check_eeprom_version (this : UInt64) : PMem.M Unit := do
  let t'1 ← StorageAccess.read_uint32 (0xbf28 : UInt64) /- &AP_Mission::_storage -/ (Int16.toUInt16 (Int32.toInt16 ((0 : Int32))))
  let mut eeprom_version : UInt32 := t'1
  if (eeprom_version != (Int32.toUInt32 ((26030 : Int32)))) then
    let t'2 ← AP_Mission.clear this
    if t'2 then
      StorageAccess.write_uint32 (0xbf28 : UInt64) /- &AP_Mission::_storage -/ (Int16.toUInt16 (Int32.toInt16 ((0 : Int32)))) (Int32.toUInt32 ((26030 : Int32)))
  return ()

end Vehicle_lib
