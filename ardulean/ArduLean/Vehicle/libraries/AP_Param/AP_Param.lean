import ArduLean.Runtime.Hal
import ArduLean.Vehicle.libraries.AP_Math.AP_Math
import ArduLean.Vehicle.libraries.StorageManager.StorageManager

/-!
ArduPilot `libraries/AP_Param`, part 1 of 3. Sources: `libraries/AP_Param/AP_Param.cpp`, `libraries/AP_Param/AP_Param.h`, `libraries/AP_Param/AP_ParamT.cpp`.

Items of `lean/Vehicle_lib.lean` (the vehicle translation), unchanged; placed by `tools/split_modules.py` (`ArduLean/Vehicle/INDEX.md`).
-/

open FloatLib.Floats (Binary32 Binary64)

set_option linter.unusedVariables false
set_option linter.unreachableTactic false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false

namespace Vehicle_lib

/-- C++ `AP_ParamTBase<signed char, 1>::set : void (const signed char &)`, `AP_Param.h:923-925`. -/
def AP_ParamTBase'signed_char_1.set (this : UInt64) (v : UInt64) : PMem.M Unit := do
  let t'1 ← PMem.ldI8 v
  PMem.stI8 this t'1
  return ()

/-- C++ `AP_ParamTBase<short, 2>::set : void (const short &)`, `AP_Param.h:923-925`. -/
def AP_ParamTBase'short_2.set (this : UInt64) (v : UInt64) : PMem.M Unit := do
  let t'1 ← PMem.ldI16 v
  PMem.stI16 this t'1
  return ()

/-- C++ `AP_ParamTBase<int, 3>::set : void (const int &)`, `AP_Param.h:923-925`. -/
def AP_ParamTBase'int_3.set (this : UInt64) (v : UInt64) : PMem.M Unit := do
  let t'1 ← PMem.ldI32 v
  PMem.stI32 this t'1
  return ()

/-- C++ `AP_ParamTBase<float, 4>::set : void (const float &)`, `AP_Param.h:923-925`. -/
def AP_ParamTBase'float_4.set (this : UInt64) (v : UInt64) : PMem.M Unit := do
  let t'1 ← PMem.ldF32 v
  PMem.stF32 this t'1
  return ()

/-- C++ `AP_Param::set_value : void (enum ap_var_type, void *, float)`, `AP_Param.cpp:1501-1519`. -/
def AP_Param.set_value.body (fp : UInt64) (type' : UInt32) (ptr' : UInt64) (value : Binary32) : PMem.M Unit := do
  let mut type' := type'
  let mut ptr' := ptr'
  PMem.stF32 (fp + 0) value
  let sw'1 := UInt32.toInt32 (type')
  if sw'1 == (1 : Int32) then
    let t'2 ← PMem.ldF32 (fp + 0)
    PMem.stI8 (fp + 4) (Binary32.toInt8 (t'2))
    AP_ParamTBase'signed_char_1.set ptr' (fp + 4)
  else if sw'1 == (2 : Int32) then
    let t'3 ← PMem.ldF32 (fp + 0)
    PMem.stI16 (fp + 6) (Binary32.toInt16 (t'3))
    AP_ParamTBase'short_2.set ptr' (fp + 6)
  else if sw'1 == (3 : Int32) then
    let t'4 ← PMem.ldF32 (fp + 0)
    PMem.stI32 (fp + 8) (Binary32.toInt32 (t'4))
    AP_ParamTBase'int_3.set ptr' (fp + 8)
  else if sw'1 == (4 : Int32) then
    AP_ParamTBase'float_4.set ptr' (fp + 0)
  else
    pure ()
  return ()

def AP_Param.set_value (type' : UInt32) (ptr' : UInt64) (value : Binary32) : PMem.M Unit := do
  let fp ← PMem.enter 12
  let r ← AP_Param.set_value.body fp type' ptr' value
  PMem.leave fp
  return r

/-- C++ `AP_Param::setup : bool ()`, `AP_Param.cpp:362-399`. -/
def AP_Param.setup.body (fp : UInt64)  : PMem.M Bool := do
  discard <| PMem.memset ((fp + 0) + 0) 0 2
  discard <| PMem.memset ((fp + 0) + 2) 0 1
  discard <| PMem.memset ((fp + 0) + 3) 0 1
  let t'1 ← StorageAccess.read_block (0xbb70 : UInt64) /- &AP_Param::_storage -/ (fp + 0) (Int16.toUInt16 (Int32.toInt16 ((0 : Int32)))) (4 : UInt64)
  discard <| pure (t'1)
  let t'2 ← PMem.ldU8 ((fp + 0) + ((Int32.toInt64 ((0 : Int32))) * 1).toUInt64)
  let mut sc'4 := ((UInt32.toInt32 (UInt8.toUInt32 (t'2))) != (UInt32.toInt32 (UInt8.toUInt32 ((80 : UInt8)))))
  if !sc'4 then
    let t'3 ← PMem.ldU8 ((fp + 0) + ((Int32.toInt64 ((1 : Int32))) * 1).toUInt64)
    sc'4 := ((UInt32.toInt32 (UInt8.toUInt32 (t'3))) != (UInt32.toInt32 (UInt8.toUInt32 ((65 : UInt8)))))
  let mut sc'6 := sc'4
  if !sc'6 then
    let t'5 ← PMem.ldU8 ((fp + 0) + 2)
    sc'6 := ((UInt32.toInt32 (UInt8.toUInt32 (t'5))) != (UInt32.toInt32 (UInt8.toUInt32 ((6 : UInt8)))))
  if sc'6 then
    PMem.unreached "AP_Param::erase_all"
  return true

def AP_Param.setup  : PMem.M Bool := do
  let fp ← PMem.enter 4
  let r ← AP_Param.setup.body fp 
  PMem.leave fp
  return r

/-- C++ `AP_Param::var_info : const struct Info &(uint16_t)`, `AP_Param.h:846-848`. -/
def AP_Param.var_info (i : UInt16) : PMem.M UInt64 := do
  let mut i := i
  let t'1 ← PMem.ldU64 (0xbbb8 : UInt64) /- &AP_Param::_var_info -/
  return (t'1 + ((UInt64.toInt64 (UInt16.toUInt64 (i))) * 32).toUInt64)

/-- C++ `AP_Param::get_base : bool (const struct Info &, ptrdiff_t &)`, `AP_Param.cpp:440-448`. -/
def AP_Param.get_base (info' : UInt64) (base : UInt64) : PMem.M Bool := do
  let t'1 ← PMem.ldU16 (info' + 24)
  if ((UInt32.toInt32 (UInt16.toUInt32 (t'1))) &&& ((1 : Int32) <<< (1 : Int32))) != (0 : Int32) then
    let t'2 ← PMem.ldU64 (info' + 8)
    let t'3 ← PMem.ldI64 t'2
    PMem.stI64 base t'3
    let t'4 ← PMem.ldI64 base
    return (t'4 != (Int32.toInt64 ((0 : Int32))))
  let t'5 ← PMem.ldU64 (info' + 8)
  let t'6 := UInt64.toInt64 (t'5)
  PMem.stI64 base t'6
  return true

/-- C++ `AP_Param::get_default_value : float (const AP_Param *, const struct Info &)`, `AP_Param.cpp:2698-2709`. -/
def AP_Param.get_default_value (vp : UInt64) (info' : UInt64) : PMem.M Binary32 := do
  let mut vp := vp
  let mut i : UInt16 := Int16.toUInt16 (Int32.toInt16 ((0 : Int32)))
  let mut first'1 := true
  for _ in PMem.loopFuel do
    if !first'1 then
      let t'2 := i
      let t'3 := (t'2 + 1)
      i := t'3
      pure ()
    first'1 := false
    let t'4 ← PMem.ldU16 (0xbf48 : UInt64) /- &AP_Param::num_param_overrides -/
    if !((decide ((UInt32.toInt32 (UInt16.toUInt32 (i))) < (UInt32.toInt32 (UInt16.toUInt32 (t'4)))))) then break
    let t'5 ← PMem.ldU64 (0xbf50 : UInt64) /- &AP_Param::param_overrides -/
    let t'6 ← PMem.ldU64 (t'5 + ((UInt64.toInt64 (UInt16.toUInt64 (i))) * 16).toUInt64)
    if (vp == t'6) then
      let t'7 ← PMem.ldU64 (0xbf50 : UInt64) /- &AP_Param::param_overrides -/
      let t'8 ← PMem.ldF32 ((t'7 + ((UInt64.toInt64 (UInt16.toUInt64 (i))) * 16).toUInt64) + 8)
      return t'8
  let t'9 ← PMem.ldU16 (info' + 24)
  if (((UInt32.toInt32 (UInt16.toUInt32 (t'9))) &&& ((1 : Int32) <<< (7 : Int32))) != (0 : Int32)) then
    let t'10 ← PMem.ldI64 (info' + 16)
    let t'11 ← PMem.ldF32 (Int64.toUInt64 (((UInt64.toInt64 (vp)) - t'10)))
    return t'11
  let t'12 ← PMem.ldF32 (info' + 16)
  return t'12

/-- C++ `AP_Param::setup_sketch_defaults : void ()`, `AP_Param.cpp:1569-1583`. -/
def AP_Param.setup_sketch_defaults.body (fp : UInt64)  : PMem.M Unit := do
  let t'1 ← AP_Param.setup
  discard <| pure (t'1)
  let mut i : UInt16 := Int16.toUInt16 (Int32.toInt16 ((0 : Int32)))
  let mut first'2 := true
  for _ in PMem.loopFuel do
    if !first'2 then
      let t'3 := i
      let t'4 := (t'3 + 1)
      i := t'4
      pure ()
    first'2 := false
    let t'5 ← PMem.ldU16 (0xba78 : UInt64) /- &AP_Param::_num_vars -/
    if !((decide ((UInt32.toInt32 (UInt16.toUInt32 (i))) < (UInt32.toInt32 (UInt16.toUInt32 (t'5)))))) then break
    let t'6 ← AP_Param.var_info i
    let info' : UInt64 := t'6
    let t'7 ← PMem.ldU8 (info' + 28)
    let mut type' : UInt8 := t'7
    if (decide ((UInt32.toInt32 (UInt8.toUInt32 (type'))) ≤ (UInt32.toInt32 ((4 : UInt32))))) then
      let t'8 ← AP_Param.get_base info' (fp + 0)
      if t'8 then
        let t'9 ← PMem.ldI64 (fp + 0)
        let t'10 ← PMem.ldI64 (fp + 0)
        let t'11 ← AP_Param.get_default_value (Int64.toUInt64 (t'10)) info'
        AP_Param.set_value (UInt8.toUInt32 (type')) (Int64.toUInt64 (t'9)) t'11
  return ()

def AP_Param.setup_sketch_defaults  : PMem.M Unit := do
  let fp ← PMem.enter 8
  let r ← AP_Param.setup_sketch_defaults.body fp 
  PMem.leave fp
  return r

/-- `AP_Param.type_size` as a pure function of its arguments (it reads and writes no memory). -/
def AP_Param.type_size.pure' (type' : UInt32) : Id UInt8 := do
  let mut type' := type'
  let sw'1 := UInt32.toInt32 (type')
  if sw'1 == (0 : Int32) || sw'1 == (6 : Int32) then
    return Int8.toUInt8 (Int32.toInt8 ((0 : Int32)))
  else if sw'1 == (1 : Int32) then
    return Int8.toUInt8 (Int32.toInt8 ((1 : Int32)))
  else if sw'1 == (2 : Int32) then
    return Int8.toUInt8 (Int32.toInt8 ((2 : Int32)))
  else if sw'1 == (3 : Int32) then
    return Int8.toUInt8 (Int32.toInt8 ((4 : Int32)))
  else if sw'1 == (4 : Int32) then
    return Int8.toUInt8 (Int32.toInt8 ((4 : Int32)))
  else if sw'1 == (5 : Int32) then
    return Int8.toUInt8 (Int32.toInt8 (((3 : Int32) * (4 : Int32))))
  else
    pure ()
  return Int8.toUInt8 (Int32.toInt8 ((0 : Int32)))

/-- C++ `AP_Param::type_size : uint8_t (enum ap_var_type)`, `AP_Param.cpp:702-721`. -/
def AP_Param.type_size (type' : UInt32) : PMem.M UInt8 :=
  pure (_root_.Vehicle_lib.AP_Param.type_size.pure' type')

/-- C++ `AP_Param::get_group_info : const struct AP_Param::GroupInfo *(const struct Info &)`, `AP_Param.cpp:312-318`. -/
def AP_Param.get_group_info (info' : UInt64) : PMem.M UInt64 := do
  let t'1 ← PMem.ldU16 (info' + 24)
  if ((UInt32.toInt32 (UInt16.toUInt32 (t'1))) &&& ((1 : Int32) <<< (4 : Int32))) != (0 : Int32) then
    let t'2 ← PMem.ldU64 (info' + 16)
    let t'3 ← PMem.ldU64 t'2
    return t'3
  let t'4 ← PMem.ldU64 (info' + 16)
  return t'4

/-- C++ `AP_Param::get_group_info : const struct AP_Param::GroupInfo *(const struct GroupInfo &)`, `AP_Param.cpp:301-307`. -/
def AP_Param.get_group_info'2 (ginfo : UInt64) : PMem.M UInt64 := do
  let t'1 ← PMem.ldU16 (ginfo + 24)
  if ((UInt32.toInt32 (UInt16.toUInt32 (t'1))) &&& ((1 : Int32) <<< (4 : Int32))) != (0 : Int32) then
    let t'2 ← PMem.ldU64 (ginfo + 16)
    let t'3 ← PMem.ldU64 t'2
    return t'3
  let t'4 ← PMem.ldU64 (ginfo + 16)
  return t'4

mutual

/-- C++ `AP_Param::check_group_info : void (const struct AP_Param::GroupInfo *, uint16_t *, uint8_t, uint8_t)`, `AP_Param.cpp:235-283`. -/
def AP_Param.check_group_info'rec (rec'depth : Nat) (group_info : UInt64) (total_size : UInt64) (group_shift : UInt8) (prefix_length : UInt8) : PMem.M Unit := do
  let rec'd + 1 := rec'depth | PMem.depthOut
  let mut group_info := group_info
  let mut total_size := total_size
  let mut group_shift := group_shift
  let mut prefix_length := prefix_length
  let mut type' : UInt8 := default  -- uninitialized in C
  let mut used_mask : UInt64 := Int64.toUInt64 (Int32.toInt64 ((0 : Int32)))
  let mut i : UInt8 := Int8.toUInt8 (Int32.toInt8 ((0 : Int32)))
  let mut first'1 := true
  for _ in PMem.loopFuel do
    if !first'1 then
      let t'2 := i
      let t'3 := (t'2 + 1)
      i := t'3
      pure ()
    first'1 := false
    let t'4 ← PMem.ldU8 ((group_info + ((UInt64.toInt64 (UInt8.toUInt64 (i))) * 32).toUInt64) + 27)
    type' := t'4
    if !(((UInt32.toInt32 (UInt8.toUInt32 (type'))) != (UInt32.toInt32 ((0 : UInt32))))) then break
    let t'5 ← PMem.ldU8 ((group_info + ((UInt64.toInt64 (UInt8.toUInt64 (i))) * 32).toUInt64) + 26)
    let mut idx : UInt8 := t'5
    if (decide ((UInt32.toInt32 (UInt8.toUInt32 (idx))) ≥ ((1 : Int32) <<< (UInt32.toInt32 (UInt8.toUInt32 ((6 : UInt8))))))) then
      pure ()
    if (((UInt32.toInt32 (UInt8.toUInt32 (group_shift))) != (0 : Int32)) && ((UInt32.toInt32 (UInt8.toUInt32 (idx))) == (0 : Int32))) then
      let t'6 := Int8.toUInt8 (Int32.toInt8 ((63 : Int32)))
      idx := t'6
    if (used_mask &&& ((1 : UInt64) <<< (Int64.toUInt64 (Int32.toInt64 ((UInt32.toInt32 (UInt8.toUInt32 (idx)))))))) != (0 : UInt64) then
      pure ()
    let t'7 := (used_mask ||| ((1 : UInt64) <<< (Int64.toUInt64 (Int32.toInt64 ((UInt32.toInt32 (UInt8.toUInt32 (idx))))))))
    used_mask := t'7
    if ((UInt32.toInt32 (UInt8.toUInt32 (type'))) == (UInt32.toInt32 ((6 : UInt32)))) then
      if (decide (((UInt32.toInt32 (UInt8.toUInt32 (group_shift))) + (UInt32.toInt32 (UInt8.toUInt32 ((6 : UInt8))))) ≥ (UInt32.toInt32 (UInt8.toUInt32 ((18 : UInt8)))))) then
        pure ()
      let t'8 ← AP_Param.get_group_info'2 (group_info + ((UInt64.toInt64 (UInt8.toUInt64 (i))) * 32).toUInt64)
      let mut ginfo : UInt64 := t'8
      if (ginfo == (0 : UInt64)) then
        continue
      let t'9 ← PMem.ldU64 (group_info + ((UInt64.toInt64 (UInt8.toUInt64 (i))) * 32).toUInt64)
      let t'10 ← PMem.strlen t'9
      AP_Param.check_group_info'rec rec'd ginfo total_size (Int8.toUInt8 (Int32.toInt8 (((UInt32.toInt32 (UInt8.toUInt32 (group_shift))) + (UInt32.toInt32 (UInt8.toUInt32 ((6 : UInt8)))))))) (UInt64.toUInt8 (((UInt8.toUInt64 (prefix_length)) + t'10)))
      continue
    let t'11 ← AP_Param.type_size (UInt8.toUInt32 (type'))
    let mut size : UInt8 := t'11
    if ((UInt32.toInt32 (UInt8.toUInt32 (size))) == (0 : Int32)) then
      pure ()
    let t'12 ← PMem.ldU64 (group_info + ((UInt64.toInt64 (UInt8.toUInt64 (i))) * 32).toUInt64)
    let t'13 ← PMem.strlen t'12
    let mut param_name_length : UInt8 := UInt64.toUInt8 (((UInt8.toUInt64 (prefix_length)) + t'13))
    if ((UInt32.toInt32 (UInt8.toUInt32 (type'))) == (UInt32.toInt32 ((5 : UInt32)))) then
      let t'14 := (param_name_length + (Int8.toUInt8 (Int32.toInt8 ((2 : Int32)))))
      param_name_length := t'14
    if (decide ((UInt32.toInt32 (UInt8.toUInt32 (param_name_length))) > (16 : Int32))) then
      pure ()
    let t'15 ← PMem.ldU16 total_size
    let t'16 := (t'15 + (UInt64.toUInt16 (((UInt8.toUInt64 (size)) + (4 : UInt64)))))
    PMem.stU16 total_size t'16
  return ()

end

/-- `AP_Param.check_group_info'rec` with the depth of its recursive component (64). -/
def AP_Param.check_group_info (group_info : UInt64) (total_size : UInt64) (group_shift : UInt8) (prefix_length : UInt8) : PMem.M Unit :=
  AP_Param.check_group_info'rec 64 group_info total_size group_shift prefix_length

/-- C++ `AP_Param::duplicate_key : bool (uint16_t, uint16_t)`, `AP_Param.cpp:286-296`. -/
def AP_Param.duplicate_key (vindex : UInt16) (key : UInt16) : PMem.M Bool := do
  let mut vindex := vindex
  let mut key := key
  let mut i : UInt16 := Int16.toUInt16 (Int32.toInt16 (((UInt32.toInt32 (UInt16.toUInt32 (vindex))) + (1 : Int32))))
  let mut first'1 := true
  for _ in PMem.loopFuel do
    if !first'1 then
      let t'2 := i
      let t'3 := (t'2 + 1)
      i := t'3
      pure ()
    first'1 := false
    let t'4 ← PMem.ldU16 (0xba78 : UInt64) /- &AP_Param::_num_vars -/
    if !((decide ((UInt32.toInt32 (UInt16.toUInt32 (i))) < (UInt32.toInt32 (UInt16.toUInt32 (t'4)))))) then break
    let t'5 ← AP_Param.var_info i
    let t'6 ← PMem.ldU16 (t'5 + 26)
    let mut key2 : UInt16 := t'6
    if ((UInt32.toInt32 (UInt16.toUInt32 (key2))) == (UInt32.toInt32 (UInt16.toUInt32 (key)))) then
      return true
  return false

/-- C++ `AP_Param::check_var_info : void ()`, `AP_Param.cpp:321-358`. -/
def AP_Param.check_var_info.body (fp : UInt64)  : PMem.M Unit := do
  PMem.stU16 (fp + 0) (UInt64.toUInt16 ((4 : UInt64)))
  let mut i : UInt16 := Int16.toUInt16 (Int32.toInt16 ((0 : Int32)))
  let mut first'1 := true
  for _ in PMem.loopFuel do
    if !first'1 then
      let t'2 := i
      let t'3 := (t'2 + 1)
      i := t'3
      pure ()
    first'1 := false
    let t'4 ← PMem.ldU16 (0xba78 : UInt64) /- &AP_Param::_num_vars -/
    if !((decide ((UInt32.toInt32 (UInt16.toUInt32 (i))) < (UInt32.toInt32 (UInt16.toUInt32 (t'4)))))) then break
    let t'5 ← AP_Param.var_info i
    let info' : UInt64 := t'5
    let t'6 ← PMem.ldU8 (info' + 28)
    let mut type' : UInt8 := t'6
    let t'7 ← PMem.ldU16 (info' + 26)
    let mut key : UInt16 := t'7
    if ((UInt32.toInt32 (UInt8.toUInt32 (type'))) == (UInt32.toInt32 ((6 : UInt32)))) then
      if ((UInt32.toInt32 (UInt16.toUInt32 (i))) == (0 : Int32)) then
        pure ()
      let t'8 ← AP_Param.get_group_info info'
      let mut group_info : UInt64 := t'8
      if (group_info == (0 : UInt64)) then
        continue
      let t'9 ← PMem.ldU64 info'
      let t'10 ← PMem.strlen t'9
      AP_Param.check_group_info group_info (fp + 0) (Int8.toUInt8 (Int32.toInt8 ((0 : Int32)))) (UInt64.toUInt8 (t'10))
    else
      let t'11 ← AP_Param.type_size (UInt8.toUInt32 (type'))
      let mut size : UInt8 := t'11
      if ((UInt32.toInt32 (UInt8.toUInt32 (size))) == (0 : Int32)) then
        pure ()
      let t'12 ← PMem.ldU16 (fp + 0)
      let t'13 := (t'12 + (UInt64.toUInt16 (((UInt8.toUInt64 (size)) + (4 : UInt64)))))
      PMem.stU16 (fp + 0) t'13
    let t'14 ← AP_Param.duplicate_key i key
    if t'14 then
      pure ()
    let mut sc'16 := ((UInt32.toInt32 (UInt8.toUInt32 (type'))) != (UInt32.toInt32 ((6 : UInt32))))
    if sc'16 then
      let t'15 ← PMem.ldU16 (info' + 24)
      sc'16 := ((UInt32.toInt32 (UInt16.toUInt32 (t'15))) &&& ((1 : Int32) <<< (1 : Int32))) != (0 : Int32)
    if sc'16 then
      pure ()
  return ()

def AP_Param.check_var_info  : PMem.M Unit := do
  let fp ← PMem.enter 2
  let r ← AP_Param.check_var_info.body fp 
  PMem.leave fp
  return r

/-- C++ `AP_Param::get_default_value : float (const AP_Param *, const struct GroupInfo &)`, `AP_Param.cpp:2685-2696`. -/
def AP_Param.get_default_value'2 (vp : UInt64) (info' : UInt64) : PMem.M Binary32 := do
  let mut vp := vp
  let mut i : UInt16 := Int16.toUInt16 (Int32.toInt16 ((0 : Int32)))
  let mut first'1 := true
  for _ in PMem.loopFuel do
    if !first'1 then
      let t'2 := i
      let t'3 := (t'2 + 1)
      i := t'3
      pure ()
    first'1 := false
    let t'4 ← PMem.ldU16 (0xbf48 : UInt64) /- &AP_Param::num_param_overrides -/
    if !((decide ((UInt32.toInt32 (UInt16.toUInt32 (i))) < (UInt32.toInt32 (UInt16.toUInt32 (t'4)))))) then break
    let t'5 ← PMem.ldU64 (0xbf50 : UInt64) /- &AP_Param::param_overrides -/
    let t'6 ← PMem.ldU64 (t'5 + ((UInt64.toInt64 (UInt16.toUInt64 (i))) * 16).toUInt64)
    if (vp == t'6) then
      let t'7 ← PMem.ldU64 (0xbf50 : UInt64) /- &AP_Param::param_overrides -/
      let t'8 ← PMem.ldF32 ((t'7 + ((UInt64.toInt64 (UInt16.toUInt64 (i))) * 16).toUInt64) + 8)
      return t'8
  let t'9 ← PMem.ldU16 (info' + 24)
  if (((UInt32.toInt32 (UInt16.toUInt32 (t'9))) &&& ((1 : Int32) <<< (7 : Int32))) != (0 : Int32)) then
    let t'10 ← PMem.ldI64 (info' + 16)
    let t'11 ← PMem.ldF32 (Int64.toUInt64 (((UInt64.toInt64 (vp)) - t'10)))
    return t'11
  let t'12 ← PMem.ldF32 (info' + 16)
  return t'12

/-- C++ `AP_ParamV<Vector3<float>, 5>::set : void (const Vector3<float> &)`, `AP_Param.h:1065-1067`. -/
def AP_ParamV'Vector3_float_5.set (this : UInt64) (v : UInt64) : PMem.M Unit := do
  discard <| PMem.memcpy this v 12
  discard <| pure (this)
  return ()

/-- C++ `AP_Param::setup_object_defaults : void (const void *, const struct GroupInfo *)`, `AP_Param.cpp:1524-1542`. -/
def AP_Param.setup_object_defaults.body (fp : UInt64) (object_pointer : UInt64) (group_info : UInt64) : PMem.M Unit := do
  let mut object_pointer := object_pointer
  let mut group_info := group_info
  let mut base : Int64 := UInt64.toInt64 (object_pointer)
  let mut type' : UInt8 := default  -- uninitialized in C
  let mut i : UInt8 := Int8.toUInt8 (Int32.toInt8 ((0 : Int32)))
  let mut first'1 := true
  for _ in PMem.loopFuel do
    if !first'1 then
      let t'2 := i
      let t'3 := (t'2 + 1)
      i := t'3
      pure ()
    first'1 := false
    let t'4 ← PMem.ldU8 ((group_info + ((UInt64.toInt64 (UInt8.toUInt64 (i))) * 32).toUInt64) + 27)
    type' := t'4
    if !(((UInt32.toInt32 (UInt8.toUInt32 (type'))) != (UInt32.toInt32 ((0 : UInt32))))) then break
    if (decide ((UInt32.toInt32 (UInt8.toUInt32 (type'))) ≤ (UInt32.toInt32 ((4 : UInt32))))) then
      let t'5 ← PMem.ldI64 ((group_info + ((UInt64.toInt64 (UInt8.toUInt64 (i))) * 32).toUInt64) + 8)
      let mut ptr' : UInt64 := Int64.toUInt64 ((base + t'5))
      let t'6 ← AP_Param.get_default_value'2 ptr' (group_info + ((UInt64.toInt64 (UInt8.toUInt64 (i))) * 32).toUInt64)
      AP_Param.set_value (UInt8.toUInt32 (type')) ptr' t'6
    else
      if ((UInt32.toInt32 (UInt8.toUInt32 (type'))) == (UInt32.toInt32 ((5 : UInt32)))) then
        let t'7 ← PMem.ldI64 ((group_info + ((UInt64.toInt64 (UInt8.toUInt64 (i))) * 32).toUInt64) + 8)
        let mut ptr''2 : UInt64 := Int64.toUInt64 ((base + t'7))
        let t'8 ← AP_Param.get_default_value'2 ptr''2 (group_info + ((UInt64.toInt64 (UInt8.toUInt64 (i))) * 32).toUInt64)
        let mut default_val : Binary32 := t'8
        Vector3'float.Vector3 (fp + 0) default_val default_val default_val
        AP_ParamV'Vector3_float_5.set ptr''2 (fp + 0)
  return ()

def AP_Param.setup_object_defaults (object_pointer : UInt64) (group_info : UInt64) : PMem.M Unit := do
  let fp ← PMem.enter 12
  let r ← AP_Param.setup_object_defaults.body fp object_pointer group_info
  PMem.leave fp
  return r

/-- C++ `AP_Param::Param_header::Param_header : void (const Param_header &) noexcept`, `AP_Param.h:?-?`. -/
def AP_Param.Param_header.Param_header'2 (this : UInt64) (arg : UInt64) : PMem.M Unit := do
  let t'1 ← PMem.ldBits arg 0 8
  PMem.stBits this 0 8 (UInt32.toUInt64 ((UInt64.toUInt32 (t'1))))
  let t'2 ← PMem.ldBits arg 8 5
  PMem.stBits this 8 5 (UInt32.toUInt64 ((UInt64.toUInt32 (t'2))))
  let t'3 ← PMem.ldBits arg 13 1
  PMem.stBits this 13 1 (UInt32.toUInt64 ((UInt64.toUInt32 (t'3))))
  let t'4 ← PMem.ldBits arg 14 18
  PMem.stBits this 14 18 (UInt32.toUInt64 ((UInt64.toUInt32 (t'4))))
  return ()

/-- C++ `AP_Param::get_key : uint16_t (const Param_header &)`, `AP_Param.cpp:743-746`. -/
def AP_Param.get_key (phdr : UInt64) : PMem.M UInt16 := do
  let t'1 ← PMem.ldBits phdr 13 1
  let t'2 ← PMem.ldBits phdr 0 8
  return Int16.toUInt16 (Int32.toInt16 ((((UInt32.toInt32 (UInt16.toUInt32 ((UInt32.toUInt16 ((UInt64.toUInt32 (t'1))))))) <<< (8 : Int32)) ||| (UInt32.toInt32 ((UInt64.toUInt32 (t'2)))))))

/-- C++ `AP_Param::adjust_group_offset : bool (uint16_t, const struct GroupInfo &, ptrdiff_t &)`, `AP_Param.cpp:413-435`. -/
def AP_Param.adjust_group_offset.body (fp : UInt64) (vindex : UInt16) (group_info : UInt64) (new_offset : UInt64) : PMem.M Bool := do
  let mut vindex := vindex
  let t'1 ← PMem.ldU16 (group_info + 24)
  if ((UInt32.toInt32 (UInt16.toUInt32 (t'1))) &&& ((1 : Int32) <<< (0 : Int32))) != (0 : Int32) then
    let t'2 ← PMem.ldI64 new_offset
    let t'3 ← PMem.ldI64 (group_info + 8)
    let t'4 := (t'2 + t'3)
    PMem.stI64 new_offset t'4
    return true
  let t'5 ← PMem.ldU16 (group_info + 24)
  if ((UInt32.toInt32 (UInt16.toUInt32 (t'5))) &&& ((1 : Int32) <<< (1 : Int32))) != (0 : Int32) then
    let t'6 ← AP_Param.var_info vindex
    let t'7 ← AP_Param.get_base t'6 (fp + 0)
    if !t'7 then
      return false
    let t'8 ← PMem.ldI64 (fp + 0)
    let t'9 ← PMem.ldI64 new_offset
    let t'10 ← PMem.ldI64 (group_info + 8)
    let mut p : UInt64 := Int64.toUInt64 (((t'8 + t'9) + t'10))
    let t'11 ← PMem.ldU64 p
    if (t'11 == (0 : UInt64)) then
      return false
    let t'12 ← PMem.ldU64 p
    let t'13 ← PMem.ldI64 (fp + 0)
    let t'14 := ((UInt64.toInt64 (t'12)) - t'13)
    PMem.stI64 new_offset t'14
  return true

def AP_Param.adjust_group_offset (vindex : UInt16) (group_info : UInt64) (new_offset : UInt64) : PMem.M Bool := do
  let fp ← PMem.enter 8
  let r ← AP_Param.adjust_group_offset.body fp vindex group_info new_offset
  PMem.leave fp
  return r

/-- C++ `AP_Param::group_id : uint32_t (const struct GroupInfo *, uint32_t, uint8_t, uint8_t)`, `AP_Param.cpp:201-213`. -/
def AP_Param.group_id (grpinfo : UInt64) (base : UInt32) (i : UInt8) (shift : UInt8) : PMem.M UInt32 := do
  let mut grpinfo := grpinfo
  let mut base := base
  let mut i := i
  let mut shift := shift
  let t'1 ← PMem.ldU8 ((grpinfo + ((UInt64.toInt64 (UInt8.toUInt64 (i))) * 32).toUInt64) + 26)
  let mut sc'3 := (((UInt32.toInt32 (UInt8.toUInt32 (t'1))) == (0 : Int32)) && ((UInt32.toInt32 (UInt8.toUInt32 (shift))) != (0 : Int32)))
  if sc'3 then
    let t'2 ← PMem.ldU16 ((grpinfo + ((UInt64.toInt64 (UInt8.toUInt64 (i))) * 32).toUInt64) + 24)
    sc'3 := !(((UInt32.toInt32 (UInt16.toUInt32 (t'2))) &&& ((1 : Int32) <<< (3 : Int32))) != (0 : Int32))
  if sc'3 then
    return (base + ((63 : UInt32) <<< (Int32.toUInt32 ((UInt32.toInt32 (UInt8.toUInt32 (shift)))))))
  let t'4 ← PMem.ldU8 ((grpinfo + ((UInt64.toInt64 (UInt8.toUInt64 (i))) * 32).toUInt64) + 26)
  return (base + (Int32.toUInt32 (((UInt32.toInt32 (UInt8.toUInt32 (t'4))) <<< (UInt32.toInt32 (UInt8.toUInt32 (shift)))))))

mutual

/-- C++ `AP_Param::find_by_header_group : const struct AP_Param::Info *(struct Param_header, void **, uint16_t, const struct GroupInfo *, uint32_t, uint8_t, ptrdiff_t)`, `AP_Param.cpp:461-508`. -/
def AP_Param.find_by_header_group.body'rec (rec'depth : Nat) (fp : UInt64) (phdr : UInt64) (ptr' : UInt64) (vindex : UInt16) (group_info : UInt64) (group_base : UInt32) (group_shift : UInt8) (group_offset : Int64) : PMem.M UInt64 := do
  let rec'd + 1 := rec'depth | PMem.depthOut
  let mut ptr' := ptr'
  let mut vindex := vindex
  let mut group_info := group_info
  let mut group_base := group_base
  let mut group_shift := group_shift
  let mut group_offset := group_offset
  let mut type' : UInt8 := default  -- uninitialized in C
  let mut i : UInt8 := Int8.toUInt8 (Int32.toInt8 ((0 : Int32)))
  let mut first'1 := true
  for _ in PMem.loopFuel do
    if !first'1 then
      let t'2 := i
      let t'3 := (t'2 + 1)
      i := t'3
      pure ()
    first'1 := false
    let t'4 ← PMem.ldU8 ((group_info + ((UInt64.toInt64 (UInt8.toUInt64 (i))) * 32).toUInt64) + 27)
    type' := t'4
    if !(((UInt32.toInt32 (UInt8.toUInt32 (type'))) != (UInt32.toInt32 ((0 : UInt32))))) then break
    if ((UInt32.toInt32 (UInt8.toUInt32 (type'))) == (UInt32.toInt32 ((6 : UInt32)))) then
      if (decide (((UInt32.toInt32 (UInt8.toUInt32 (group_shift))) + (UInt32.toInt32 (UInt8.toUInt32 ((6 : UInt8))))) ≥ (UInt32.toInt32 (UInt8.toUInt32 ((18 : UInt8)))))) then
        return (0 : UInt64)
      let t'5 ← AP_Param.get_group_info'2 (group_info + ((UInt64.toInt64 (UInt8.toUInt64 (i))) * 32).toUInt64)
      let mut ginfo : UInt64 := t'5
      if (ginfo == (0 : UInt64)) then
        continue
      PMem.stI64 (fp + 0) group_offset
      let t'6 ← AP_Param.adjust_group_offset vindex (group_info + ((UInt64.toInt64 (UInt8.toUInt64 (i))) * 32).toUInt64) (fp + 0)
      if !t'6 then
        continue
      AP_Param.Param_header.Param_header'2 (fp + 8) phdr
      let t'7 ← AP_Param.group_id group_info group_base i group_shift
      let t'8 ← PMem.ldI64 (fp + 0)
      let t'9 ← AP_Param.find_by_header_group'rec rec'd (fp + 8) ptr' vindex ginfo t'7 (Int8.toUInt8 (Int32.toInt8 (((UInt32.toInt32 (UInt8.toUInt32 (group_shift))) + (UInt32.toInt32 (UInt8.toUInt32 ((6 : UInt8)))))))) t'8
      let mut ret : UInt64 := t'9
      if (ret != (0 : UInt64)) then
        return ret
      continue
    let t'10 ← AP_Param.group_id group_info group_base i group_shift
    let t'11 ← PMem.ldBits phdr 14 18
    let mut sc'13 := (t'10 == (UInt64.toUInt32 (t'11)))
    if sc'13 then
      let t'12 ← PMem.ldBits phdr 8 5
      sc'13 := ((UInt32.toInt32 (UInt8.toUInt32 (type'))) == (UInt32.toInt32 ((UInt64.toUInt32 (t'12)))))
    if sc'13 then
      let t'14 ← AP_Param.var_info vindex
      let t'15 ← AP_Param.get_base t'14 (fp + 16)
      if !t'15 then
        continue
      let t'16 ← PMem.ldI64 (fp + 16)
      let t'17 ← PMem.ldI64 ((group_info + ((UInt64.toInt64 (UInt8.toUInt64 (i))) * 32).toUInt64) + 8)
      let t'18 := Int64.toUInt64 (((t'16 + t'17) + group_offset))
      PMem.stU64 ptr' t'18
      let t'19 ← AP_Param.var_info vindex
      return t'19
  return (0 : UInt64)

def AP_Param.find_by_header_group'rec (rec'depth : Nat) (phdr : UInt64) (ptr' : UInt64) (vindex : UInt16) (group_info : UInt64) (group_base : UInt32) (group_shift : UInt8) (group_offset : Int64) : PMem.M UInt64 := do
  let rec'd + 1 := rec'depth | PMem.depthOut
  let fp ← PMem.enter 24
  let r ← AP_Param.find_by_header_group.body'rec rec'd fp phdr ptr' vindex group_info group_base group_shift group_offset
  PMem.leave fp
  return r

end

/-- `AP_Param.find_by_header_group.body'rec` with the depth of its recursive component (64). -/
def AP_Param.find_by_header_group.body (fp : UInt64) (phdr : UInt64) (ptr' : UInt64) (vindex : UInt16) (group_info : UInt64) (group_base : UInt32) (group_shift : UInt8) (group_offset : Int64) : PMem.M UInt64 :=
  AP_Param.find_by_header_group.body'rec 64 fp phdr ptr' vindex group_info group_base group_shift group_offset

/-- `AP_Param.find_by_header_group'rec` with the depth of its recursive component (64). -/
def AP_Param.find_by_header_group (phdr : UInt64) (ptr' : UInt64) (vindex : UInt16) (group_info : UInt64) (group_base : UInt32) (group_shift : UInt8) (group_offset : Int64) : PMem.M UInt64 :=
  AP_Param.find_by_header_group'rec 64 phdr ptr' vindex group_info group_base group_shift group_offset

/-- C++ `AP_Param::find_by_header : const struct AP_Param::Info *(struct Param_header, void **)`, `AP_Param.cpp:512-541`. -/
def AP_Param.find_by_header.body (fp : UInt64) (phdr : UInt64) (ptr' : UInt64) : PMem.M UInt64 := do
  let mut ptr' := ptr'
  let mut i : UInt16 := Int16.toUInt16 (Int32.toInt16 ((0 : Int32)))
  let mut first'1 := true
  for _ in PMem.loopFuel do
    if !first'1 then
      let t'2 := i
      let t'3 := (t'2 + 1)
      i := t'3
      pure ()
    first'1 := false
    let t'4 ← PMem.ldU16 (0xba78 : UInt64) /- &AP_Param::_num_vars -/
    if !((decide ((UInt32.toInt32 (UInt16.toUInt32 (i))) < (UInt32.toInt32 (UInt16.toUInt32 (t'4)))))) then break
    let t'5 ← AP_Param.var_info i
    let info' : UInt64 := t'5
    let t'6 ← PMem.ldU8 (info' + 28)
    let mut type' : UInt8 := t'6
    let t'7 ← PMem.ldU16 (info' + 26)
    let mut key : UInt16 := t'7
    let t'8 ← AP_Param.get_key phdr
    if ((UInt32.toInt32 (UInt16.toUInt32 (key))) != (UInt32.toInt32 (UInt16.toUInt32 (t'8)))) then
      continue
    if ((UInt32.toInt32 (UInt8.toUInt32 (type'))) == (UInt32.toInt32 ((6 : UInt32)))) then
      let t'9 ← AP_Param.get_group_info info'
      let mut group_info : UInt64 := t'9
      if (group_info == (0 : UInt64)) then
        continue
      AP_Param.Param_header.Param_header'2 (fp + 0) phdr
      let t'10 ← AP_Param.find_by_header_group (fp + 0) ptr' i group_info (Int32.toUInt32 ((0 : Int32))) (Int8.toUInt8 (Int32.toInt8 ((0 : Int32)))) (Int32.toInt64 ((0 : Int32)))
      return t'10
    let t'11 ← PMem.ldBits phdr 8 5
    if ((UInt32.toInt32 (UInt8.toUInt32 (type'))) == (UInt32.toInt32 ((UInt64.toUInt32 (t'11))))) then
      let t'12 ← AP_Param.get_base info' (fp + 8)
      if !t'12 then
        return (0 : UInt64)
      let t'13 ← PMem.ldI64 (fp + 8)
      let t'14 := Int64.toUInt64 (t'13)
      PMem.stU64 ptr' t'14
      return info'
  return (0 : UInt64)

def AP_Param.find_by_header (phdr : UInt64) (ptr' : UInt64) : PMem.M UInt64 := do
  let fp ← PMem.enter 16
  let r ← AP_Param.find_by_header.body fp phdr ptr'
  PMem.leave fp
  return r

/-- C++ `AP_Param::is_sentinel : bool (const Param_header &)`, `AP_Param.cpp:760-777`. -/
def AP_Param.is_sentinel (phdr : UInt64) : PMem.M Bool := do
  let t'1 ← PMem.ldBits phdr 8 5
  let mut sc'3 := ((UInt32.toInt32 ((UInt64.toUInt32 (t'1)))) == (UInt32.toInt32 (UInt8.toUInt32 ((31 : UInt8)))))
  if !sc'3 then
    let t'2 ← AP_Param.get_key phdr
    sc'3 := ((UInt32.toInt32 (UInt16.toUInt32 (t'2))) == (UInt32.toInt32 (UInt16.toUInt32 ((511 : UInt16)))))
  if sc'3 then
    return true
  let t'4 ← PMem.ldU32 phdr
  let mut v : UInt32 := t'4
  if ((v == (Int32.toUInt32 ((0 : Int32)))) || (v == (4294967295 : UInt32))) then
    return true
  return false

/-- `AP_Param.Param_header.Param_header` as a pure function of its arguments (it reads and writes no memory). -/
def AP_Param.Param_header.Param_header.pure' (this : UInt64) : Id Unit := do
  return ()

/-- C++ `AP_Param::Param_header::Param_header : void () noexcept`, `AP_Param.h:669-?`. -/
def AP_Param.Param_header.Param_header (this : UInt64) : PMem.M Unit :=
  pure (_root_.Vehicle_lib.AP_Param.Param_header.Param_header.pure' this)

/-- `AP_Param.reload_defaults_file` as a pure function of its arguments (it reads and writes no memory). -/
def AP_Param.reload_defaults_file.pure' (last_pass : Bool) : Id Unit := do
  let mut last_pass := last_pass
  let mut default_file : UInt64 := (0 : UInt64)
  if (default_file != 0) then
    -- AP_Param::load_defaults_file_from_filesystem: dropped (configuration)
  return ()

/-- C++ `AP_Param::reload_defaults_file : void (bool)`, `AP_Param.cpp:1629-1657`. -/
def AP_Param.reload_defaults_file (last_pass : Bool) : PMem.M Unit :=
  pure (_root_.Vehicle_lib.AP_Param.reload_defaults_file.pure' last_pass)

/-- C++ `AP_Param::load_all : bool ()`, `AP_Param.cpp:1588-1622`. -/
def AP_Param.load_all.body (fp : UInt64)  : PMem.M Bool := do
  AP_Param.Param_header.Param_header (fp + 0)
  let mut ofs : UInt16 := UInt64.toUInt16 ((4 : UInt64))
  AP_Param.reload_defaults_file false
  let t'1 ← PMem.ldB (0xba80 : UInt64) /- &AP_Param::registered_save_handler -/
  if !t'1 then
    PMem.stB (0xba80 : UInt64) /- &AP_Param::registered_save_handler -/ true
    let t'2 ← PMem.ldU64 ((0xba88 : UInt64) /- &hal -/ + 80)
    PMem.stU64 (fp + 24) (0xbb68 : UInt64) /- &save_dummy -/
    PMem.stU64 (fp + 32) (0x7e000000 : UInt64)
    let t'3 := (fp + 24)
    discard <| PMem.memcpy (fp + 8) t'3 16
    discard <| PMem.halDev "AP_HAL::Scheduler::register_io_process" t'2 #[(fp + 8)]
  for _ in PMem.loopFuel do
    let t'4 ← StorageAccess.size (0xbb70 : UInt64) /- &AP_Param::_storage -/
    if !((decide ((UInt32.toInt32 (UInt16.toUInt32 (ofs))) < (UInt32.toInt32 (UInt16.toUInt32 (t'4)))))) then break
    let t'5 ← StorageAccess.read_block (0xbb70 : UInt64) /- &AP_Param::_storage -/ (fp + 0) ofs (4 : UInt64)
    discard <| pure (t'5)
    let t'6 ← AP_Param.is_sentinel (fp + 0)
    if t'6 then
      PMem.stU16 (0xbb80 : UInt64) /- &AP_Param::sentinel_offset -/ ofs
      return true
    let mut info' : UInt64 := default  -- uninitialized in C
    AP_Param.Param_header.Param_header'2 (fp + 48) (fp + 0)
    let t'7 ← AP_Param.find_by_header (fp + 48) (fp + 40)
    info' := t'7
    if (info' != (0 : UInt64)) then
      let t'8 ← PMem.ldU64 (fp + 40)
      let t'9 ← PMem.ldBits (fp + 0) 8 5
      let t'10 ← AP_Param.type_size (UInt64.toUInt32 (t'9))
      let t'11 ← StorageAccess.read_block (0xbb70 : UInt64) /- &AP_Param::_storage -/ t'8 (UInt64.toUInt16 (((UInt16.toUInt64 (ofs)) + (4 : UInt64)))) (UInt8.toUInt64 (t'10))
      discard <| pure (t'11)
    let t'12 ← PMem.ldBits (fp + 0) 8 5
    let t'13 ← AP_Param.type_size (UInt64.toUInt32 (t'12))
    let t'14 := (ofs + (UInt64.toUInt16 (((UInt8.toUInt64 (t'13)) + (4 : UInt64)))))
    ofs := t'14
  return false

def AP_Param.load_all  : PMem.M Bool := do
  let fp ← PMem.enter 52
  let r ← AP_Param.load_all.body fp 
  PMem.leave fp
  return r

/-- C++ `AP_Param::scan : bool (const AP_Param::Param_header *, uint16_t *)`, `AP_Param.cpp:784-808`. -/
def AP_Param.scan.body (fp : UInt64) (target : UInt64) (pofs : UInt64) : PMem.M Bool := do
  let mut target := target
  let mut pofs := pofs
  AP_Param.Param_header.Param_header (fp + 0)
  let mut ofs : UInt16 := UInt64.toUInt16 ((4 : UInt64))
  for _ in PMem.loopFuel do
    let t'1 ← StorageAccess.size (0xbb70 : UInt64) /- &AP_Param::_storage -/
    if !((decide ((UInt32.toInt32 (UInt16.toUInt32 (ofs))) < (UInt32.toInt32 (UInt16.toUInt32 (t'1)))))) then break
    let t'2 ← StorageAccess.read_block (0xbb70 : UInt64) /- &AP_Param::_storage -/ (fp + 0) ofs (4 : UInt64)
    discard <| pure (t'2)
    let t'3 ← PMem.ldBits (fp + 0) 8 5
    let t'4 ← PMem.ldBits target 8 5
    let mut sc'7 := ((UInt32.toInt32 ((UInt64.toUInt32 (t'3)))) == (UInt32.toInt32 ((UInt64.toUInt32 (t'4)))))
    if sc'7 then
      let t'5 ← AP_Param.get_key (fp + 0)
      let t'6 ← AP_Param.get_key target
      sc'7 := ((UInt32.toInt32 (UInt16.toUInt32 (t'5))) == (UInt32.toInt32 (UInt16.toUInt32 (t'6))))
    let mut sc'10 := sc'7
    if sc'10 then
      let t'8 ← PMem.ldBits (fp + 0) 14 18
      let t'9 ← PMem.ldBits target 14 18
      sc'10 := ((UInt32.toInt32 ((UInt64.toUInt32 (t'8)))) == (UInt32.toInt32 ((UInt64.toUInt32 (t'9)))))
    if sc'10 then
      PMem.stU16 pofs ofs
      return true
    let t'11 ← AP_Param.is_sentinel (fp + 0)
    if t'11 then
      PMem.stU16 pofs ofs
      PMem.stU16 (0xbb80 : UInt64) /- &AP_Param::sentinel_offset -/ ofs
      return false
    let t'12 ← PMem.ldBits (fp + 0) 8 5
    let t'13 ← AP_Param.type_size (UInt64.toUInt32 (t'12))
    let t'14 := (ofs + (UInt64.toUInt16 (((UInt8.toUInt64 (t'13)) + (4 : UInt64)))))
    ofs := t'14
  let t'15 := Int16.toUInt16 (Int32.toInt16 ((65535 : Int32)))
  PMem.stU16 pofs t'15
  return false

def AP_Param.scan (target : UInt64) (pofs : UInt64) : PMem.M Bool := do
  let fp ← PMem.enter 4
  let r ← AP_Param.scan.body fp target pofs
  PMem.leave fp
  return r

mutual

/-- C++ `AP_Param::find_var_info_group : const struct AP_Param::Info *(const struct GroupInfo *, uint16_t, uint32_t, uint8_t, ptrdiff_t, uint32_t *, const struct GroupInfo *&, struct GroupNesting &, uint8_t *) const`, `AP_Param.cpp:544-612`. -/
def AP_Param.find_var_info_group.body'rec (rec'depth : Nat) (fp : UInt64) (this : UInt64) (group_info : UInt64) (vindex : UInt16) (group_base : UInt32) (group_shift : UInt8) (group_offset : Int64) (group_element : UInt64) (group_ret : UInt64) (group_nesting : UInt64) (idx : UInt64) : PMem.M UInt64 := do
  let rec'd + 1 := rec'depth | PMem.depthOut
  let mut group_info := group_info
  let mut vindex := vindex
  let mut group_base := group_base
  let mut group_shift := group_shift
  let mut group_offset := group_offset
  let mut group_element := group_element
  let mut idx := idx
  let t'1 ← AP_Param.var_info vindex
  let t'2 ← AP_Param.get_base t'1 (fp + 0)
  if !t'2 then
    return (0 : UInt64)
  let mut type' : UInt8 := default  -- uninitialized in C
  let mut i : UInt8 := Int8.toUInt8 (Int32.toInt8 ((0 : Int32)))
  let mut first'3 := true
  for _ in PMem.loopFuel do
    if !first'3 then
      let t'4 := i
      let t'5 := (t'4 + 1)
      i := t'5
      pure ()
    first'3 := false
    let t'6 ← PMem.ldU8 ((group_info + ((UInt64.toInt64 (UInt8.toUInt64 (i))) * 32).toUInt64) + 27)
    type' := t'6
    if !(((UInt32.toInt32 (UInt8.toUInt32 (type'))) != (UInt32.toInt32 ((0 : UInt32))))) then break
    let t'7 ← PMem.ldI64 ((group_info + ((UInt64.toInt64 (UInt8.toUInt64 (i))) * 32).toUInt64) + 8)
    let mut ofs : Int64 := (t'7 + group_offset)
    if ((UInt32.toInt32 (UInt8.toUInt32 (type'))) == (UInt32.toInt32 ((6 : UInt32)))) then
      let t'8 ← AP_Param.get_group_info'2 (group_info + ((UInt64.toInt64 (UInt8.toUInt64 (i))) * 32).toUInt64)
      let mut ginfo : UInt64 := t'8
      if (ginfo == (0 : UInt64)) then
        continue
      if (decide (((UInt32.toInt32 (UInt8.toUInt32 (group_shift))) + (UInt32.toInt32 (UInt8.toUInt32 ((6 : UInt8))))) ≥ (UInt32.toInt32 (UInt8.toUInt32 ((18 : UInt8)))))) then
        return (0 : UInt64)
      let mut info' : UInt64 := default  -- uninitialized in C
      PMem.stI64 (fp + 8) group_offset
      let t'9 ← AP_Param.adjust_group_offset vindex (group_info + ((UInt64.toInt64 (UInt8.toUInt64 (i))) * 32).toUInt64) (fp + 8)
      if !t'9 then
        continue
      let t'10 ← PMem.ldU8 group_nesting
      if (decide ((UInt32.toInt32 (UInt8.toUInt32 (t'10))) ≥ (UInt32.toInt32 (UInt8.toUInt32 ((2 : UInt8)))))) then
        return (0 : UInt64)
      let t'11 := (group_info + ((UInt64.toInt64 (UInt8.toUInt64 (i))) * 32).toUInt64)
      let t'12 ← PMem.ldU8 group_nesting
      let t'13 := (t'12 + 1)
      PMem.stU8 group_nesting t'13
      PMem.stU64 ((group_nesting + 8) + ((UInt64.toInt64 (UInt8.toUInt64 (t'12))) * 8).toUInt64) t'11
      let t'14 ← AP_Param.group_id group_info group_base i group_shift
      let t'15 ← PMem.ldI64 (fp + 8)
      let t'16 ← AP_Param.find_var_info_group'rec rec'd this ginfo vindex t'14 (Int8.toUInt8 (Int32.toInt8 (((UInt32.toInt32 (UInt8.toUInt32 (group_shift))) + (UInt32.toInt32 (UInt8.toUInt32 ((6 : UInt8)))))))) t'15 group_element group_ret group_nesting idx
      info' := t'16
      if (info' != (0 : UInt64)) then
        return info'
      let t'17 ← PMem.ldU8 group_nesting
      let t'18 := (t'17 - 1)
      PMem.stU8 group_nesting t'18
    else
      let t'19 ← PMem.ldI64 (fp + 0)
      if ((UInt64.toInt64 (this)) == (t'19 + ofs)) then
        let t'20 ← AP_Param.group_id group_info group_base i group_shift
        PMem.stU32 group_element t'20
        let t'21 := (group_info + ((UInt64.toInt64 (UInt8.toUInt64 (i))) * 32).toUInt64)
        PMem.stU64 group_ret t'21
        let t'22 := Int8.toUInt8 (Int32.toInt8 ((0 : Int32)))
        PMem.stU8 idx t'22
        let t'23 ← AP_Param.var_info vindex
        return t'23
      else
        let mut sc'27 := ((UInt32.toInt32 (UInt8.toUInt32 (type'))) == (UInt32.toInt32 ((5 : UInt32))))
        if sc'27 then
          let t'24 ← PMem.ldI64 (fp + 0)
          let mut sc'26 := (((t'24 + ofs) + (UInt64.toInt64 ((4 : UInt64)))) == (UInt64.toInt64 (this)))
          if !sc'26 then
            let t'25 ← PMem.ldI64 (fp + 0)
            sc'26 := (((t'25 + ofs) + ((Int32.toInt64 ((2 : Int32))) * (UInt64.toInt64 ((4 : UInt64))))) == (UInt64.toInt64 (this)))
          sc'27 := sc'26
        if sc'27 then
          let t'28 ← PMem.ldI64 (fp + 0)
          let t'29 := UInt64.toUInt8 (((Int64.toUInt64 (((UInt64.toInt64 (this)) - (t'28 + ofs)))) / (4 : UInt64)))
          PMem.stU8 idx t'29
          let t'30 ← AP_Param.group_id group_info group_base i group_shift
          PMem.stU32 group_element t'30
          let t'31 := (group_info + ((UInt64.toInt64 (UInt8.toUInt64 (i))) * 32).toUInt64)
          PMem.stU64 group_ret t'31
          let t'32 ← AP_Param.var_info vindex
          return t'32
  return (0 : UInt64)

def AP_Param.find_var_info_group'rec (rec'depth : Nat) (this : UInt64) (group_info : UInt64) (vindex : UInt16) (group_base : UInt32) (group_shift : UInt8) (group_offset : Int64) (group_element : UInt64) (group_ret : UInt64) (group_nesting : UInt64) (idx : UInt64) : PMem.M UInt64 := do
  let rec'd + 1 := rec'depth | PMem.depthOut
  let fp ← PMem.enter 16
  let r ← AP_Param.find_var_info_group.body'rec rec'd fp this group_info vindex group_base group_shift group_offset group_element group_ret group_nesting idx
  PMem.leave fp
  return r

end

/-- `AP_Param.find_var_info_group.body'rec` with the depth of its recursive component (64). -/
def AP_Param.find_var_info_group.body (fp : UInt64) (this : UInt64) (group_info : UInt64) (vindex : UInt16) (group_base : UInt32) (group_shift : UInt8) (group_offset : Int64) (group_element : UInt64) (group_ret : UInt64) (group_nesting : UInt64) (idx : UInt64) : PMem.M UInt64 :=
  AP_Param.find_var_info_group.body'rec 64 fp this group_info vindex group_base group_shift group_offset group_element group_ret group_nesting idx

/-- `AP_Param.find_var_info_group'rec` with the depth of its recursive component (64). -/
def AP_Param.find_var_info_group (this : UInt64) (group_info : UInt64) (vindex : UInt16) (group_base : UInt32) (group_shift : UInt8) (group_offset : Int64) (group_element : UInt64) (group_ret : UInt64) (group_nesting : UInt64) (idx : UInt64) : PMem.M UInt64 :=
  AP_Param.find_var_info_group'rec 64 this group_info vindex group_base group_shift group_offset group_element group_ret group_nesting idx

/-- C++ `AP_Param::find_var_info : const struct AP_Param::Info *(uint32_t *, const struct GroupInfo *&, struct GroupNesting &, uint8_t *) const`, `AP_Param.cpp:615-654`. -/
def AP_Param.find_var_info.body (fp : UInt64) (this : UInt64) (group_element : UInt64) (group_ret : UInt64) (group_nesting : UInt64) (idx : UInt64) : PMem.M UInt64 := do
  let mut group_element := group_element
  let mut idx := idx
  PMem.stU64 group_ret (0 : UInt64)
  let mut i : UInt16 := Int16.toUInt16 (Int32.toInt16 ((0 : Int32)))
  let mut first'1 := true
  for _ in PMem.loopFuel do
    if !first'1 then
      let t'2 := i
      let t'3 := (t'2 + 1)
      i := t'3
      pure ()
    first'1 := false
    let t'4 ← PMem.ldU16 (0xba78 : UInt64) /- &AP_Param::_num_vars -/
    if !((decide ((UInt32.toInt32 (UInt16.toUInt32 (i))) < (UInt32.toInt32 (UInt16.toUInt32 (t'4)))))) then break
    let t'5 ← AP_Param.var_info i
    let info' : UInt64 := t'5
    let t'6 ← PMem.ldU8 (info' + 28)
    let mut type' : UInt8 := t'6
    let t'7 ← AP_Param.get_base info' (fp + 0)
    if !t'7 then
      continue
    if ((UInt32.toInt32 (UInt8.toUInt32 (type'))) == (UInt32.toInt32 ((6 : UInt32)))) then
      let t'8 ← AP_Param.get_group_info info'
      let mut group_info : UInt64 := t'8
      if (group_info == (0 : UInt64)) then
        continue
      let mut info2 : UInt64 := default  -- uninitialized in C
      let t'9 ← AP_Param.find_var_info_group this group_info i (Int32.toUInt32 ((0 : Int32))) (Int8.toUInt8 (Int32.toInt8 ((0 : Int32)))) (Int32.toInt64 ((0 : Int32))) group_element group_ret group_nesting idx
      info2 := t'9
      if (info2 != (0 : UInt64)) then
        return info2
    else
      let t'10 ← PMem.ldI64 (fp + 0)
      if (t'10 == (UInt64.toInt64 (this))) then
        let t'11 := Int32.toUInt32 ((0 : Int32))
        PMem.stU32 group_element t'11
        let t'12 := Int8.toUInt8 (Int32.toInt8 ((0 : Int32)))
        PMem.stU8 idx t'12
        return info'
      else
        let mut sc'16 := ((UInt32.toInt32 (UInt8.toUInt32 (type'))) == (UInt32.toInt32 ((5 : UInt32))))
        if sc'16 then
          let t'13 ← PMem.ldI64 (fp + 0)
          let mut sc'15 := ((t'13 + (UInt64.toInt64 ((4 : UInt64)))) == (UInt64.toInt64 (this)))
          if !sc'15 then
            let t'14 ← PMem.ldI64 (fp + 0)
            sc'15 := ((t'14 + ((Int32.toInt64 ((2 : Int32))) * (UInt64.toInt64 ((4 : UInt64))))) == (UInt64.toInt64 (this)))
          sc'16 := sc'15
        if sc'16 then
          let t'17 ← PMem.ldI64 (fp + 0)
          let t'18 := UInt64.toUInt8 (((Int64.toUInt64 (((UInt64.toInt64 (this)) - t'17))) / (4 : UInt64)))
          PMem.stU8 idx t'18
          let t'19 := Int32.toUInt32 ((0 : Int32))
          PMem.stU32 group_element t'19
          return info'
  return (0 : UInt64)

def AP_Param.find_var_info (this : UInt64) (group_element : UInt64) (group_ret : UInt64) (group_nesting : UInt64) (idx : UInt64) : PMem.M UInt64 := do
  let fp ← PMem.enter 8
  let r ← AP_Param.find_var_info.body fp this group_element group_ret group_nesting idx
  PMem.leave fp
  return r

/-- C++ `AP_Param::set_key : void (Param_header &, uint16_t)`, `AP_Param.cpp:751-755`. -/
def AP_Param.set_key (phdr : UInt64) (key : UInt16) : PMem.M Unit := do
  let mut key := key
  let t'1 := Int32.toUInt32 (((UInt32.toInt32 (UInt16.toUInt32 (key))) &&& (255 : Int32)))
  PMem.stBits phdr 0 8 (UInt32.toUInt64 (t'1))
  let t'2 := Int32.toUInt32 (((UInt32.toInt32 (UInt16.toUInt32 (key))) >>> (8 : Int32)))
  PMem.stBits phdr 13 1 (UInt32.toUInt64 (t'2))
  return ()

/-- C++ `AP_Param::load : bool ()`, `AP_Param.cpp:1339-1399`. -/
def AP_Param.load.body (fp : UInt64) (this : UInt64) : PMem.M Bool := do
  PMem.stU32 (fp + 0) (Int32.toUInt32 ((0 : Int32)))
  discard <| PMem.memset ((fp + 16) + 0) 0 1
  discard <| PMem.memset ((fp + 16) + 8) 0 16
  let t'1 ← AP_Param.find_var_info this (fp + 0) (fp + 8) (fp + 16) (fp + 40)
  let mut info' : UInt64 := t'1
  if (info' == (0 : UInt64)) then
    return false
  AP_Param.Param_header.Param_header (fp + 48)
  let t'2 ← PMem.ldU64 (fp + 8)
  if (t'2 != (0 : UInt64)) then
    let t'3 ← PMem.ldU64 (fp + 8)
    let t'4 ← PMem.ldU8 (t'3 + 27)
    let t'5 := UInt8.toUInt32 (t'4)
    PMem.stBits (fp + 48) 8 5 (UInt32.toUInt64 (t'5))
  else
    let t'6 ← PMem.ldU8 (info' + 28)
    let t'7 := UInt8.toUInt32 (t'6)
    PMem.stBits (fp + 48) 8 5 (UInt32.toUInt64 (t'7))
  let t'8 ← PMem.ldU16 (info' + 26)
  AP_Param.set_key (fp + 48) t'8
  let t'9 ← PMem.ldU32 (fp + 0)
  PMem.stBits (fp + 48) 14 18 (UInt32.toUInt64 (t'9))
  let t'10 ← AP_Param.scan (fp + 48) (fp + 56)
  if !t'10 then
    let t'11 ← AP_Param.get_base info' (fp + 64)
    if !t'11 then
      return false
    let t'12 ← PMem.ldU64 (fp + 8)
    if (t'12 != (0 : UInt64)) then
      let mut group_offset : Int64 := Int32.toInt64 ((0 : Int32))
      let mut i : UInt8 := Int8.toUInt8 (Int32.toInt8 ((0 : Int32)))
      let mut first'13 := true
      for _ in PMem.loopFuel do
        if !first'13 then
          let t'14 := i
          let t'15 := (t'14 + 1)
          i := t'15
          pure ()
        first'13 := false
        let t'16 ← PMem.ldU8 (fp + 16)
        if !((decide ((UInt32.toInt32 (UInt8.toUInt32 (i))) < (UInt32.toInt32 (UInt8.toUInt32 (t'16)))))) then break
        let t'17 ← PMem.ldU64 (((fp + 16) + 8) + ((UInt64.toInt64 (UInt8.toUInt64 (i))) * 8).toUInt64)
        let t'18 ← PMem.ldI64 (t'17 + 8)
        let t'19 := (group_offset + t'18)
        group_offset := t'19
      let t'20 ← PMem.ldBits (fp + 48) 8 5
      let t'21 ← PMem.ldI64 (fp + 64)
      let t'22 ← PMem.ldU64 (fp + 8)
      let t'23 ← PMem.ldI64 (t'22 + 8)
      let t'24 ← PMem.ldU64 (fp + 8)
      let t'25 ← AP_Param.get_default_value'2 this t'24
      AP_Param.set_value (UInt64.toUInt32 (t'20)) (Int64.toUInt64 (((t'21 + t'23) + group_offset))) t'25
    else
      let t'26 ← PMem.ldBits (fp + 48) 8 5
      let t'27 ← PMem.ldI64 (fp + 64)
      let t'28 ← AP_Param.get_default_value this info'
      AP_Param.set_value (UInt64.toUInt32 (t'26)) (Int64.toUInt64 (t'27)) t'28
    return false
  let t'29 ← PMem.ldBits (fp + 48) 8 5
  let mut sc'31 := ((UInt32.toInt32 ((UInt64.toUInt32 (t'29)))) != (UInt32.toInt32 ((5 : UInt32))))
  if sc'31 then
    let t'30 ← PMem.ldU8 (fp + 40)
    sc'31 := ((UInt32.toInt32 (UInt8.toUInt32 (t'30))) != (0 : Int32))
  if sc'31 then
    return false
  let mut ap : UInt64 := this
  let t'32 ← PMem.ldU8 (fp + 40)
  if ((UInt32.toInt32 (UInt8.toUInt32 (t'32))) != (0 : Int32)) then
    let t'33 ← PMem.ldU8 (fp + 40)
    let t'34 := ((Int64.toUInt64 ((UInt64.toInt64 (ap)))) - ((UInt64.toInt64 (((UInt8.toUInt64 (t'33)) * (4 : UInt64)))) * 1).toUInt64)
    ap := t'34
  let t'35 ← PMem.ldU16 (fp + 56)
  let t'36 ← PMem.ldBits (fp + 48) 8 5
  let t'37 ← AP_Param.type_size (UInt64.toUInt32 (t'36))
  let t'38 ← StorageAccess.read_block (0xbb70 : UInt64) /- &AP_Param::_storage -/ ap (UInt64.toUInt16 (((UInt16.toUInt64 (t'35)) + (4 : UInt64)))) (UInt8.toUInt64 (t'37))
  discard <| pure (t'38)
  return true

def AP_Param.load (this : UInt64) : PMem.M Bool := do
  let fp ← PMem.enter 72
  let r ← AP_Param.load.body fp this
  PMem.leave fp
  return r

/-- `AP_Param.EEPROM_header.EEPROM_header` as a pure function of its arguments (it reads and writes no memory). -/
def AP_Param.EEPROM_header.EEPROM_header.pure' (this : UInt64) : Id Unit := do
  return ()

/-- C++ `AP_Param::EEPROM_header::EEPROM_header : void () noexcept`, `AP_Param.h:648-?`. -/
def AP_Param.EEPROM_header.EEPROM_header (this : UInt64) : PMem.M Unit :=
  pure (_root_.Vehicle_lib.AP_Param.EEPROM_header.EEPROM_header.pure' this)

/-- C++ `AP_Param::eeprom_write_check : void (const void *, uint16_t, uint8_t)`, `AP_Param.cpp:156-162`. -/
def AP_Param.eeprom_write_check (ptr' : UInt64) (ofs : UInt16) (size : UInt8) : PMem.M Unit := do
  let mut ptr' := ptr'
  let mut ofs := ofs
  let mut size := size
  let t'1 ← StorageAccess.write_block (0xbb70 : UInt64) /- &AP_Param::_storage -/ ofs ptr' (UInt8.toUInt64 (size))
  discard <| pure (t'1)
  return ()

/-- C++ `AP_Param::write_sentinel : void (uint16_t)`, `AP_Param.cpp:167-175`. -/
def AP_Param.write_sentinel.body (fp : UInt64) (ofs : UInt16) : PMem.M Unit := do
  let mut ofs := ofs
  AP_Param.Param_header.Param_header (fp + 0)
  let t'1 := UInt8.toUInt32 ((31 : UInt8))
  PMem.stBits (fp + 0) 8 5 (UInt32.toUInt64 (t'1))
  AP_Param.set_key (fp + 0) (511 : UInt16)
  let t'2 := UInt8.toUInt32 ((255 : UInt8))
  PMem.stBits (fp + 0) 14 18 (UInt32.toUInt64 (t'2))
  AP_Param.eeprom_write_check (fp + 0) ofs (UInt64.toUInt8 ((4 : UInt64)))
  PMem.stU16 (0xbb80 : UInt64) /- &AP_Param::sentinel_offset -/ ofs
  return ()

def AP_Param.write_sentinel (ofs : UInt16) : PMem.M Unit := do
  let fp ← PMem.enter 4
  let r ← AP_Param.write_sentinel.body fp ofs
  PMem.leave fp
  return r

/-- C++ `AP_Param::erase_all : void ()`, `AP_Param.cpp:179-192`. -/
def AP_Param.erase_all.body (fp : UInt64)  : PMem.M Unit := do
  AP_Param.EEPROM_header.EEPROM_header (fp + 0)
  PMem.stU8 ((fp + 0) + ((Int32.toInt64 ((0 : Int32))) * 1).toUInt64) (80 : UInt8)
  PMem.stU8 ((fp + 0) + ((Int32.toInt64 ((1 : Int32))) * 1).toUInt64) (65 : UInt8)
  PMem.stU8 ((fp + 0) + 2) (6 : UInt8)
  let t'1 := Int8.toUInt8 (Int32.toInt8 ((0 : Int32)))
  PMem.stU8 ((fp + 0) + 3) t'1
  AP_Param.eeprom_write_check (fp + 0) (Int16.toUInt16 (Int32.toInt16 ((0 : Int32)))) (UInt64.toUInt8 ((4 : UInt64)))
  AP_Param.write_sentinel (UInt64.toUInt16 ((4 : UInt64)))
  return ()

def AP_Param.erase_all  : PMem.M Unit := do
  let fp ← PMem.enter 4
  let r ← AP_Param.erase_all.body fp 
  PMem.leave fp
  return r

/-- C++ `AP_Param::check_default : void (AP_Param *, float *)`, `AP_Param.cpp:2962-2975`. -/
def AP_Param.check_default (ap : UInt64) (default_value : UInt64) : PMem.M Unit := do
  let mut ap := ap
  let mut default_value := default_value
  if ((default_value == (0 : UInt64)) || (ap == (0 : UInt64))) then
    return ()
  let t'1 ← PMem.ldU64 (0xbf58 : UInt64) /- &AP_Param::default_list -/
  if (t'1 != (0 : UInt64)) then
    let t'2 ← PMem.ldU64 (0xbf58 : UInt64) /- &AP_Param::default_list -/
    let mut item : UInt64 := t'2
    let mut first'3 := true
    for _ in PMem.loopFuel do
      if !first'3 then
        let t'4 ← PMem.ldU64 (item + 16)
        item := t'4
        pure ()
      first'3 := false
      if !((item != 0)) then break
      let t'5 ← PMem.ldU64 item
      if (t'5 == ap) then
        let t'6 ← PMem.ldF32 (item + 8)
        PMem.stF32 default_value t'6
        return ()
  return ()

/-- C++ `AP_Param::first : AP_Param *(ParamToken *, enum ap_var_type *, float *)`, `AP_Param.cpp:1765-1788`. -/
def AP_Param.first.body (fp : UInt64) (token : UInt64) (ptype : UInt64) (default_val : UInt64) : PMem.M UInt64 := do
  let mut token := token
  let mut ptype := ptype
  let mut default_val := default_val
  let t'1 := Int32.toUInt32 ((0 : Int32))
  PMem.stBits token 0 9 (UInt32.toUInt64 (t'1))
  let t'2 := Int32.toUInt32 ((0 : Int32))
  PMem.stBits token 13 18 (UInt32.toUInt64 (t'2))
  let t'3 := Int32.toUInt32 ((0 : Int32))
  PMem.stBits token 9 4 (UInt32.toUInt64 (t'3))
  let t'4 ← PMem.ldU16 (0xba78 : UInt64) /- &AP_Param::_num_vars -/
  if ((UInt32.toInt32 (UInt16.toUInt32 (t'4))) == (0 : Int32)) then
    return (0 : UInt64)
  let t'5 ← AP_Param.var_info (Int16.toUInt16 (Int32.toInt16 ((0 : Int32))))
  let t'6 ← AP_Param.get_base t'5 (fp + 0)
  if !t'6 then
    return (0 : UInt64)
  if (ptype != (0 : UInt64)) then
    let t'7 ← AP_Param.var_info (Int16.toUInt16 (Int32.toInt16 ((0 : Int32))))
    let t'8 ← PMem.ldU8 (t'7 + 28)
    let t'9 := UInt8.toUInt32 (t'8)
    PMem.stU32 ptype t'9
  if (default_val != (0 : UInt64)) then
    let t'10 ← PMem.ldI64 (fp + 0)
    let t'11 ← AP_Param.var_info (Int16.toUInt16 (Int32.toInt16 ((0 : Int32))))
    let t'12 ← AP_Param.get_default_value (Int64.toUInt64 (t'10)) t'11
    PMem.stF32 default_val t'12
  let t'13 ← PMem.ldI64 (fp + 0)
  AP_Param.check_default (Int64.toUInt64 (t'13)) default_val
  let t'14 ← PMem.ldI64 (fp + 0)
  return Int64.toUInt64 (t'14)

def AP_Param.first (token : UInt64) (ptype : UInt64) (default_val : UInt64) : PMem.M UInt64 := do
  let fp ← PMem.enter 8
  let r ← AP_Param.first.body fp token ptype default_val
  PMem.leave fp
  return r

/-- C++ `AP_Param::check_frame_type : bool (uint16_t)`, `AP_Param.cpp:221-232`. -/
def AP_Param.check_frame_type (flags : UInt16) : PMem.M Bool := do
  let mut flags := flags
  if ((UInt32.toInt32 (UInt16.toUInt32 (flags))) &&& ((1 : Int32) <<< (6 : Int32))) != (0 : Int32) then
    return false
  let mut frame_flags : UInt16 := Int16.toUInt16 (Int32.toInt16 (((UInt32.toInt32 (UInt16.toUInt32 (flags))) >>> (8 : Int32))))
  if ((UInt32.toInt32 (UInt16.toUInt32 (frame_flags))) == (0 : Int32)) then
    return true
  let t'1 ← PMem.ldU16 (0xbbb0 : UInt64) /- &AP_Param::_frame_type_flags -/
  return (((UInt32.toInt32 (UInt16.toUInt32 (frame_flags))) &&& (UInt32.toInt32 (UInt16.toUInt32 (t'1)))) != (0 : Int32))

/-- `AP_ParamTBase'signed_char_1.get` as a pure function of its arguments (it reads and writes no memory). -/
def AP_ParamTBase'signed_char_1.get.pure' (this : UInt64) : Id UInt64 := do
  return this

/-- C++ `AP_ParamTBase<signed char, 1>::get : const signed char &() const`, `AP_Param.h:917-919`. -/
def AP_ParamTBase'signed_char_1.get (this : UInt64) : PMem.M UInt64 :=
  pure (_root_.Vehicle_lib.AP_ParamTBase'signed_char_1.get.pure' this)

mutual

/-- C++ `AP_Param::next_group : AP_Param *(const uint16_t, const struct GroupInfo *, bool *, const uint32_t, const uint8_t, const ptrdiff_t, ParamToken *, enum ap_var_type *, bool, float *)`, `AP_Param.cpp:1792-1887`. -/
def AP_Param.next_group.body'rec (rec'depth : Nat) (fp : UInt64) (vindex : UInt16) (group_info : UInt64) (found_current : UInt64) (group_base : UInt32) (group_shift : UInt8) (group_offset : Int64) (token : UInt64) (ptype : UInt64) (skip_disabled : Bool) (default_val : UInt64) : PMem.M UInt64 := do
  let rec'd + 1 := rec'depth | PMem.depthOut
  let mut vindex := vindex
  let mut group_info := group_info
  let mut found_current := found_current
  let mut group_base := group_base
  let mut group_shift := group_shift
  let mut group_offset := group_offset
  let mut token := token
  let mut ptype := ptype
  let mut skip_disabled := skip_disabled
  let mut default_val := default_val
  let mut type' : UInt32 := default  -- uninitialized in C
  let mut i : UInt8 := Int8.toUInt8 (Int32.toInt8 ((0 : Int32)))
  let mut first'1 := true
  for _ in PMem.loopFuel do
    if !first'1 then
      let t'2 := i
      let t'3 := (t'2 + 1)
      i := t'3
      pure ()
    first'1 := false
    let t'4 ← PMem.ldU8 ((group_info + ((UInt64.toInt64 (UInt8.toUInt64 (i))) * 32).toUInt64) + 27)
    let t'5 := UInt8.toUInt32 (t'4)
    type' := t'5
    if !(((UInt32.toInt32 (type')) != (UInt32.toInt32 ((0 : UInt32))))) then break
    let t'6 ← PMem.ldU16 ((group_info + ((UInt64.toInt64 (UInt8.toUInt64 (i))) * 32).toUInt64) + 24)
    let t'7 ← AP_Param.check_frame_type t'6
    if !t'7 then
      continue
    if ((UInt32.toInt32 (type')) == (UInt32.toInt32 ((6 : UInt32)))) then
      let t'8 ← AP_Param.get_group_info'2 (group_info + ((UInt64.toInt64 (UInt8.toUInt64 (i))) * 32).toUInt64)
      let mut ginfo : UInt64 := t'8
      if (ginfo == (0 : UInt64)) then
        continue
      let mut ap : UInt64 := default  -- uninitialized in C
      PMem.stI64 (fp + 0) group_offset
      let t'9 ← AP_Param.adjust_group_offset vindex (group_info + ((UInt64.toInt64 (UInt8.toUInt64 (i))) * 32).toUInt64) (fp + 0)
      if !t'9 then
        continue
      let t'10 ← AP_Param.group_id group_info group_base i group_shift
      let t'11 ← PMem.ldI64 (fp + 0)
      let t'12 ← AP_Param.next_group'rec rec'd vindex ginfo found_current t'10 (Int8.toUInt8 (Int32.toInt8 (((UInt32.toInt32 (UInt8.toUInt32 (group_shift))) + (UInt32.toInt32 (UInt8.toUInt32 ((6 : UInt8)))))))) t'11 token ptype skip_disabled default_val
      ap := t'12
      if (ap != (0 : UInt64)) then
        return ap
    else
      let t'13 ← PMem.ldB found_current
      if t'13 then
        let t'14 := UInt16.toUInt32 (vindex)
        PMem.stBits token 0 9 (UInt32.toUInt64 (t'14))
        let t'15 ← AP_Param.group_id group_info group_base i group_shift
        PMem.stBits token 13 18 (UInt32.toUInt64 (t'15))
        let t'16 := Int32.toUInt32 ((0 : Int32))
        PMem.stBits token 9 4 (UInt32.toUInt64 (t'16))
        if (ptype != (0 : UInt64)) then
          PMem.stU32 ptype type'
        let t'17 ← AP_Param.var_info vindex
        let t'18 ← AP_Param.get_base t'17 (fp + 8)
        if !t'18 then
          continue
        let t'19 ← PMem.ldI64 (fp + 8)
        let t'20 ← PMem.ldI64 ((group_info + ((UInt64.toInt64 (UInt8.toUInt64 (i))) * 32).toUInt64) + 8)
        let mut ret : UInt64 := Int64.toUInt64 (((t'19 + t'20) + group_offset))
        let mut sc'22 := skip_disabled
        if sc'22 then
          let t'21 ← PMem.ldB (0xbf60 : UInt64) /- &AP_Param::_hide_disabled_groups -/
          sc'22 := t'21
        let mut sc'24 := sc'22
        if sc'24 then
          let t'23 ← PMem.ldU8 ((group_info + ((UInt64.toInt64 (UInt8.toUInt64 (i))) * 32).toUInt64) + 27)
          sc'24 := ((UInt32.toInt32 (UInt8.toUInt32 (t'23))) == (UInt32.toInt32 ((1 : UInt32))))
        let mut sc'26 := sc'24
        if sc'26 then
          let t'25 ← PMem.ldU16 ((group_info + ((UInt64.toInt64 (UInt8.toUInt64 (i))) * 32).toUInt64) + 24)
          sc'26 := ((UInt32.toInt32 (UInt16.toUInt32 (t'25))) &&& ((1 : Int32) <<< (2 : Int32))) != (0 : Int32)
        let mut sc'29 := sc'26
        if sc'29 then
          let t'27 ← AP_ParamTBase'signed_char_1.get ret
          let t'28 ← PMem.ldI8 t'27
          sc'29 := ((Int8.toInt32 (t'28)) == (0 : Int32))
        if sc'29 then
          let t'30 := Int32.toUInt32 ((1 : Int32))
          PMem.stBits token 31 1 (UInt32.toUInt64 (t'30))
        if (default_val != (0 : UInt64)) then
          let t'31 ← AP_Param.get_default_value'2 ret (group_info + ((UInt64.toInt64 (UInt8.toUInt64 (i))) * 32).toUInt64)
          PMem.stF32 default_val t'31
        return ret
      let t'32 ← AP_Param.group_id group_info group_base i group_shift
      let t'33 ← PMem.ldBits token 13 18
      if (t'32 == (UInt64.toUInt32 (t'33))) then
        PMem.stB found_current true
        let t'34 ← PMem.ldBits token 31 1
        if (UInt64.toUInt32 (t'34)) != (0 : UInt32) then
          let t'35 := Int32.toUInt32 ((0 : Int32))
          PMem.stBits token 31 1 (UInt32.toUInt64 (t'35))
          return (0 : UInt64)
        let mut sc'37 := ((UInt32.toInt32 (type')) == (UInt32.toInt32 ((5 : UInt32))))
        if sc'37 then
          let t'36 ← PMem.ldBits token 9 4
          sc'37 := (decide ((UInt32.toInt32 ((UInt64.toUInt32 (t'36)))) < (3 : Int32)))
        if sc'37 then
          let t'38 ← PMem.ldBits token 9 4
          let t'39 := UInt64.toUInt32 (t'38)
          let t'40 := (t'39 + 1)
          PMem.stBits token 9 4 (UInt32.toUInt64 (t'40))
          if (ptype != (0 : UInt64)) then
            PMem.stU32 ptype (4 : UInt32)
          let t'41 ← AP_Param.var_info vindex
          let t'42 ← AP_Param.get_base t'41 (fp + 16)
          if !t'42 then
            continue
          let t'43 ← PMem.ldI64 (fp + 16)
          let t'44 ← PMem.ldI64 ((group_info + ((UInt64.toInt64 (UInt8.toUInt64 (i))) * 32).toUInt64) + 8)
          let mut ofs : Int64 := ((t'43 + t'44) + group_offset)
          let t'45 ← PMem.ldBits token 9 4
          let t'46 := (ofs + (UInt64.toInt64 (((4 : UInt64) * (UInt32.toUInt64 (((UInt64.toUInt32 (t'45)) - (1 : UInt32))))))))
          ofs := t'46
          if (default_val != (0 : UInt64)) then
            let t'47 ← AP_Param.get_default_value'2 (Int64.toUInt64 (ofs)) (group_info + ((UInt64.toInt64 (UInt8.toUInt64 (i))) * 32).toUInt64)
            PMem.stF32 default_val t'47
          return Int64.toUInt64 (ofs)
  return (0 : UInt64)

def AP_Param.next_group'rec (rec'depth : Nat) (vindex : UInt16) (group_info : UInt64) (found_current : UInt64) (group_base : UInt32) (group_shift : UInt8) (group_offset : Int64) (token : UInt64) (ptype : UInt64) (skip_disabled : Bool) (default_val : UInt64) : PMem.M UInt64 := do
  let rec'd + 1 := rec'depth | PMem.depthOut
  let fp ← PMem.enter 24
  let r ← AP_Param.next_group.body'rec rec'd fp vindex group_info found_current group_base group_shift group_offset token ptype skip_disabled default_val
  PMem.leave fp
  return r

end

/-- `AP_Param.next_group.body'rec` with the depth of its recursive component (64). -/
def AP_Param.next_group.body (fp : UInt64) (vindex : UInt16) (group_info : UInt64) (found_current : UInt64) (group_base : UInt32) (group_shift : UInt8) (group_offset : Int64) (token : UInt64) (ptype : UInt64) (skip_disabled : Bool) (default_val : UInt64) : PMem.M UInt64 :=
  AP_Param.next_group.body'rec 64 fp vindex group_info found_current group_base group_shift group_offset token ptype skip_disabled default_val

/-- `AP_Param.next_group'rec` with the depth of its recursive component (64). -/
def AP_Param.next_group (vindex : UInt16) (group_info : UInt64) (found_current : UInt64) (group_base : UInt32) (group_shift : UInt8) (group_offset : Int64) (token : UInt64) (ptype : UInt64) (skip_disabled : Bool) (default_val : UInt64) : PMem.M UInt64 :=
  AP_Param.next_group'rec 64 vindex group_info found_current group_base group_shift group_offset token ptype skip_disabled default_val

/-- C++ `AP_Param::next : AP_Param *(ParamToken *, enum ap_var_type *, bool, float *)`, `AP_Param.cpp:1891-1953`. -/
def AP_Param.next'2.body (fp : UInt64) (token : UInt64) (ptype : UInt64) (skip_disabled : Bool) (default_val : UInt64) : PMem.M UInt64 := do
  let mut token := token
  let mut ptype := ptype
  let mut skip_disabled := skip_disabled
  let mut default_val := default_val
  let t'1 ← PMem.ldBits token 0 9
  let mut i : UInt16 := UInt32.toUInt16 ((UInt64.toUInt32 (t'1)))
  PMem.stB (fp + 0) false
  let t'2 ← PMem.ldU16 (0xba78 : UInt64) /- &AP_Param::_num_vars -/
  if (decide ((UInt32.toInt32 (UInt16.toUInt32 (i))) ≥ (UInt32.toInt32 (UInt16.toUInt32 (t'2))))) then
    return (0 : UInt64)
  let t'3 ← AP_Param.var_info i
  let t'4 ← PMem.ldU8 (t'3 + 28)
  let mut type' : UInt32 := UInt8.toUInt32 (t'4)
  let mut sc'6 := ((UInt32.toInt32 (type')) == (UInt32.toInt32 ((5 : UInt32))))
  if sc'6 then
    let t'5 ← PMem.ldBits token 9 4
    sc'6 := (decide ((UInt32.toInt32 ((UInt64.toUInt32 (t'5)))) < (3 : Int32)))
  if sc'6 then
    let t'7 ← PMem.ldBits token 9 4
    let t'8 := UInt64.toUInt32 (t'7)
    let t'9 := (t'8 + 1)
    PMem.stBits token 9 4 (UInt32.toUInt64 (t'9))
    if (ptype != (0 : UInt64)) then
      PMem.stU32 ptype (4 : UInt32)
    let t'10 ← PMem.ldBits token 9 4
    let t'11 ← AP_Param.var_info i
    let t'12 ← PMem.ldU64 (t'11 + 8)
    let mut ret : UInt64 := (((UInt32.toUInt64 (((UInt64.toUInt32 (t'10)) - (1 : UInt32)))) * (4 : UInt64)) + (Int64.toUInt64 ((UInt64.toInt64 (t'12)))))
    if (default_val != (0 : UInt64)) then
      let t'13 ← AP_Param.var_info i
      let t'14 ← AP_Param.get_default_value ret t'13
      PMem.stF32 default_val t'14
    return ret
  if ((UInt32.toInt32 (type')) != (UInt32.toInt32 ((6 : UInt32)))) then
    let t'15 := i
    let t'16 := (t'15 + 1)
    i := t'16
    PMem.stB (fp + 0) true
  let mut first'17 := true
  for _ in PMem.loopFuel do
    if !first'17 then
      let t'18 := i
      let t'19 := (t'18 + 1)
      i := t'19
      pure ()
    first'17 := false
    let t'20 ← PMem.ldU16 (0xba78 : UInt64) /- &AP_Param::_num_vars -/
    if !((decide ((UInt32.toInt32 (UInt16.toUInt32 (i))) < (UInt32.toInt32 (UInt16.toUInt32 (t'20)))))) then break
    let t'21 ← AP_Param.var_info i
    let info' : UInt64 := t'21
    let t'22 ← PMem.ldU16 (info' + 24)
    let t'23 ← AP_Param.check_frame_type t'22
    if !t'23 then
      continue
    let t'24 ← PMem.ldU8 (info' + 28)
    let t'25 := UInt8.toUInt32 (t'24)
    type' := t'25
    if ((UInt32.toInt32 (type')) == (UInt32.toInt32 ((6 : UInt32)))) then
      let t'26 ← AP_Param.get_group_info info'
      let mut group_info : UInt64 := t'26
      if (group_info == (0 : UInt64)) then
        continue
      let t'27 ← AP_Param.next_group i group_info (fp + 0) (Int32.toUInt32 ((0 : Int32))) (Int8.toUInt8 (Int32.toInt8 ((0 : Int32)))) (Int32.toInt64 ((0 : Int32))) token ptype skip_disabled default_val
      let mut ap : UInt64 := t'27
      if (ap != (0 : UInt64)) then
        return ap
    else
      let t'28 := UInt16.toUInt32 (i)
      PMem.stBits token 0 9 (UInt32.toUInt64 (t'28))
      let t'29 := Int32.toUInt32 ((0 : Int32))
      PMem.stBits token 13 18 (UInt32.toUInt64 (t'29))
      let t'30 := Int32.toUInt32 ((0 : Int32))
      PMem.stBits token 9 4 (UInt32.toUInt64 (t'30))
      if (ptype != (0 : UInt64)) then
        PMem.stU32 ptype type'
      if (default_val != (0 : UInt64)) then
        let t'31 ← PMem.ldU64 (info' + 8)
        let t'32 ← AP_Param.get_default_value t'31 info'
        PMem.stF32 default_val t'32
      let t'33 ← PMem.ldU64 (info' + 8)
      return t'33
  return (0 : UInt64)

def AP_Param.next'2 (token : UInt64) (ptype : UInt64) (skip_disabled : Bool) (default_val : UInt64) : PMem.M UInt64 := do
  let fp ← PMem.enter 1
  let r ← AP_Param.next'2.body fp token ptype skip_disabled default_val
  PMem.leave fp
  return r

/-- C++ `AP_Param::next : AP_Param *(ParamToken *, enum ap_var_type *)`, `AP_Param.h:561-?`. -/
def AP_Param.next (token : UInt64) (ptype : UInt64) : PMem.M UInt64 := do
  let mut token := token
  let mut ptype := ptype
  let t'1 ← AP_Param.next'2 token ptype false (0 : UInt64)
  return t'1

/-- C++ `AP_Param::next_scalar : AP_Param *(ParamToken *, enum ap_var_type *, float *)`, `AP_Param.cpp:1957-1972`. -/
def AP_Param.next_scalar.body (fp : UInt64) (token : UInt64) (ptype : UInt64) (default_val : UInt64) : PMem.M UInt64 := do
  let mut token := token
  let mut ptype := ptype
  let mut default_val := default_val
  let mut ap : UInt64 := default  -- uninitialized in C
  for _ in PMem.loopFuel do
    let t'1 ← AP_Param.next'2 token (fp + 0) true default_val
    ap := t'1
    let mut sc'3 := (ap != (0 : UInt64))
    if sc'3 then
      let t'2 ← PMem.ldU32 (fp + 0)
      sc'3 := (decide ((UInt32.toInt32 (t'2)) > (UInt32.toInt32 ((4 : UInt32)))))
    if !(sc'3) then break
  if (ap != (0 : UInt64)) then
    if (ptype != (0 : UInt64)) then
      let t'4 ← PMem.ldU32 (fp + 0)
      PMem.stU32 ptype t'4
  AP_Param.check_default ap default_val
  return ap

def AP_Param.next_scalar (token : UInt64) (ptype : UInt64) (default_val : UInt64) : PMem.M UInt64 := do
  let fp ← PMem.enter 4
  let r ← AP_Param.next_scalar.body fp token ptype default_val
  PMem.leave fp
  return r

/-- C++ `AP_Param::find_var_info_token : const struct AP_Param::Info *(const ParamToken &, uint32_t *, const struct GroupInfo *&, struct GroupNesting &, uint8_t *) const`, `AP_Param.cpp:658-697`. -/
def AP_Param.find_var_info_token.body (fp : UInt64) (this : UInt64) (token : UInt64) (group_element : UInt64) (group_ret : UInt64) (group_nesting : UInt64) (idx : UInt64) : PMem.M UInt64 := do
  let mut group_element := group_element
  let mut idx := idx
  let t'1 ← PMem.ldBits token 0 9
  let mut i : UInt16 := UInt32.toUInt16 ((UInt64.toUInt32 (t'1)))
  let t'2 ← AP_Param.var_info i
  let info' : UInt64 := t'2
  let t'3 ← PMem.ldU8 (info' + 28)
  let mut type' : UInt8 := t'3
  let t'4 ← AP_Param.get_base info' (fp + 0)
  if !t'4 then
    return (0 : UInt64)
  PMem.stU64 group_ret (0 : UInt64)
  if ((UInt32.toInt32 (UInt8.toUInt32 (type'))) == (UInt32.toInt32 ((6 : UInt32)))) then
    let t'5 ← AP_Param.get_group_info info'
    let mut group_info : UInt64 := t'5
    if (group_info == (0 : UInt64)) then
      return (0 : UInt64)
    let mut info2 : UInt64 := default  -- uninitialized in C
    let t'6 ← AP_Param.find_var_info_group this group_info i (Int32.toUInt32 ((0 : Int32))) (Int8.toUInt8 (Int32.toInt8 ((0 : Int32)))) (Int32.toInt64 ((0 : Int32))) group_element group_ret group_nesting idx
    info2 := t'6
    if (info2 != (0 : UInt64)) then
      return info2
  else
    let t'7 ← PMem.ldI64 (fp + 0)
    if (t'7 == (UInt64.toInt64 (this))) then
      let t'8 := Int32.toUInt32 ((0 : Int32))
      PMem.stU32 group_element t'8
      let t'9 := Int8.toUInt8 (Int32.toInt8 ((0 : Int32)))
      PMem.stU8 idx t'9
      return info'
    else
      let mut sc'13 := ((UInt32.toInt32 (UInt8.toUInt32 (type'))) == (UInt32.toInt32 ((5 : UInt32))))
      if sc'13 then
        let t'10 ← PMem.ldI64 (fp + 0)
        let mut sc'12 := ((t'10 + (UInt64.toInt64 ((4 : UInt64)))) == (UInt64.toInt64 (this)))
        if !sc'12 then
          let t'11 ← PMem.ldI64 (fp + 0)
          sc'12 := ((t'11 + ((Int32.toInt64 ((2 : Int32))) * (UInt64.toInt64 ((4 : UInt64))))) == (UInt64.toInt64 (this)))
        sc'13 := sc'12
      if sc'13 then
        let t'14 ← PMem.ldI64 (fp + 0)
        let t'15 := UInt64.toUInt8 (((Int64.toUInt64 (((UInt64.toInt64 (this)) - t'14))) / (4 : UInt64)))
        PMem.stU8 idx t'15
        let t'16 := Int32.toUInt32 ((0 : Int32))
        PMem.stU32 group_element t'16
        return info'
  return (0 : UInt64)

def AP_Param.find_var_info_token (this : UInt64) (token : UInt64) (group_element : UInt64) (group_ret : UInt64) (group_nesting : UInt64) (idx : UInt64) : PMem.M UInt64 := do
  let fp ← PMem.enter 8
  let r ← AP_Param.find_var_info_token.body fp this token group_element group_ret group_nesting idx
  PMem.leave fp
  return r

/-- C++ `AP_Param::add_vector3f_suffix : void (char *, size_t, uint8_t) const`, `AP_Param.cpp:816-826`. -/
def AP_Param.add_vector3f_suffix (this : UInt64) (buffer : UInt64) (buffer_size : UInt64) (idx : UInt8) : PMem.M Unit := do
  let mut buffer := buffer
  let mut buffer_size := buffer_size
  let mut idx := idx
  let t'1 ← PMem.strnlen buffer buffer_size
  let mut len : UInt64 := t'1
  if (decide ((len + (Int64.toUInt64 (Int32.toInt64 ((2 : Int32))))) ≤ buffer_size)) then
    PMem.stI8 (buffer + ((UInt64.toInt64 (len)) * 1).toUInt64) (95 : Int8)
    let t'2 := Int32.toInt8 (((Int8.toInt32 ((88 : Int8))) + (UInt32.toInt32 (UInt8.toUInt32 (idx)))))
    PMem.stI8 (buffer + ((UInt64.toInt64 ((len + (Int64.toUInt64 (Int32.toInt64 ((1 : Int32))))))) * 1).toUInt64) t'2
    if (decide ((len + (Int64.toUInt64 (Int32.toInt64 ((3 : Int32))))) ≤ buffer_size)) then
      let t'3 := Int32.toInt8 ((0 : Int32))
      PMem.stI8 (buffer + ((UInt64.toInt64 ((len + (Int64.toUInt64 (Int32.toInt64 ((2 : Int32))))))) * 1).toUInt64) t'3
  return ()

/-- C++ `AP_Param::copy_name_info : void (const struct AP_Param::Info *, const struct GroupInfo *, const struct GroupNesting &, uint8_t, char *, size_t, bool) const`, `AP_Param.cpp:847-871`. -/
def AP_Param.copy_name_info (this : UInt64) (info' : UInt64) (ginfo : UInt64) (group_nesting : UInt64) (idx : UInt8) (buffer : UInt64) (buffer_size : UInt64) (force_scalar : Bool) : PMem.M Unit := do
  let mut info' := info'
  let mut ginfo := ginfo
  let mut idx := idx
  let mut buffer := buffer
  let mut buffer_size := buffer_size
  let mut force_scalar := force_scalar
  let t'1 ← PMem.ldU64 info'
  let t'2 ← PMem.strncpy buffer t'1 buffer_size
  discard <| pure (t'2)
  let mut i : UInt8 := Int8.toUInt8 (Int32.toInt8 ((0 : Int32)))
  let mut first'3 := true
  for _ in PMem.loopFuel do
    if !first'3 then
      let t'4 := i
      let t'5 := (t'4 + 1)
      i := t'5
      pure ()
    first'3 := false
    let t'6 ← PMem.ldU8 group_nesting
    if !((decide ((UInt32.toInt32 (UInt8.toUInt32 (i))) < (UInt32.toInt32 (UInt8.toUInt32 (t'6)))))) then break
    let t'7 ← PMem.strnlen buffer buffer_size
    let mut len : UInt8 := UInt64.toUInt8 (t'7)
    if (decide ((UInt8.toUInt64 (len)) < buffer_size)) then
      let t'8 ← PMem.ldU64 ((group_nesting + 8) + ((UInt64.toInt64 (UInt8.toUInt64 (i))) * 8).toUInt64)
      let t'9 ← PMem.ldU64 t'8
      let t'10 ← PMem.strncpy (buffer + ((UInt64.toInt64 (UInt8.toUInt64 (len))) * 1).toUInt64) t'9 (buffer_size - (UInt8.toUInt64 (len)))
      discard <| pure (t'10)
  if (ginfo != (0 : UInt64)) then
    let t'11 ← PMem.strnlen buffer buffer_size
    let mut len'2 : UInt8 := UInt64.toUInt8 (t'11)
    if (decide ((UInt8.toUInt64 (len'2)) < buffer_size)) then
      let t'12 ← PMem.ldU64 ginfo
      let t'13 ← PMem.strncpy (buffer + ((UInt64.toInt64 (UInt8.toUInt64 (len'2))) * 1).toUInt64) t'12 (buffer_size - (UInt8.toUInt64 (len'2)))
      discard <| pure (t'13)
    let mut sc'15 := (force_scalar || ((UInt32.toInt32 (UInt8.toUInt32 (idx))) != (0 : Int32)))
    if sc'15 then
      let t'14 ← PMem.ldU8 (ginfo + 27)
      sc'15 := ((UInt32.toInt32 ((5 : UInt32))) == (UInt32.toInt32 (UInt8.toUInt32 (t'14))))
    if sc'15 then
      AP_Param.add_vector3f_suffix this buffer buffer_size idx
  else
    let mut sc'17 := (force_scalar || ((UInt32.toInt32 (UInt8.toUInt32 (idx))) != (0 : Int32)))
    if sc'17 then
      let t'16 ← PMem.ldU8 (info' + 28)
      sc'17 := ((UInt32.toInt32 ((5 : UInt32))) == (UInt32.toInt32 (UInt8.toUInt32 (t'16))))
    if sc'17 then
      AP_Param.add_vector3f_suffix this buffer buffer_size idx
  return ()

/-- C++ `AP_Param::copy_name_token : void (const ParamToken &, char *, size_t, bool) const`, `AP_Param.cpp:832-845`. -/
def AP_Param.copy_name_token.body (fp : UInt64) (this : UInt64) (token : UInt64) (buffer : UInt64) (buffer_size : UInt64) (force_scalar : Bool) : PMem.M Unit := do
  let mut buffer := buffer
  let mut buffer_size := buffer_size
  let mut force_scalar := force_scalar
  discard <| PMem.memset ((fp + 16) + 0) 0 1
  discard <| PMem.memset ((fp + 16) + 8) 0 16
  let t'1 ← AP_Param.find_var_info_token this token (fp + 0) (fp + 8) (fp + 16) (fp + 40)
  let mut info' : UInt64 := t'1
  if (info' == (0 : UInt64)) then
    let t'2 := Int32.toInt8 ((0 : Int32))
    PMem.stI8 buffer t'2
    return ()
  let t'3 ← PMem.ldU64 (fp + 8)
  let t'4 ← PMem.ldU8 (fp + 40)
  AP_Param.copy_name_info this info' t'3 (fp + 16) t'4 buffer buffer_size force_scalar
  return ()

def AP_Param.copy_name_token (this : UInt64) (token : UInt64) (buffer : UInt64) (buffer_size : UInt64) (force_scalar : Bool) : PMem.M Unit := do
  let fp ← PMem.enter 41
  let r ← AP_Param.copy_name_token.body fp this token buffer buffer_size force_scalar
  PMem.leave fp
  return r

/-- C++ `AP_Param::find_by_name : AP_Param *(const char *, enum ap_var_type *, ParamToken *)`, `AP_Param.cpp:1003-1025`. -/
def AP_Param.find_by_name.body (fp : UInt64) (name : UInt64) (ptype : UInt64) (token : UInt64) : PMem.M UInt64 := do
  let mut name := name
  let mut ptype := ptype
  let mut token := token
  let mut ap : UInt64 := default  -- uninitialized in C
  let t'1 ← AP_Param.first token ptype (0 : UInt64)
  ap := t'1
  let mut first'2 := true
  for _ in PMem.loopFuel do
    if !first'2 then
      let t'3 ← AP_Param.next_scalar token ptype (0 : UInt64)
      ap := t'3
      pure ()
    first'2 := false
    let mut sc'5 := (ap != 0)
    if sc'5 then
      let t'4 ← PMem.ldU32 ptype
      sc'5 := ((UInt32.toInt32 (t'4)) != (UInt32.toInt32 ((6 : UInt32))))
    let mut sc'7 := sc'5
    if sc'7 then
      let t'6 ← PMem.ldU32 ptype
      sc'7 := ((UInt32.toInt32 (t'6)) != (UInt32.toInt32 ((0 : UInt32))))
    if !(sc'7) then break
    let t'8 ← PMem.ldBits token 0 9
    let t'9 ← AP_Param.var_info (UInt32.toUInt16 ((UInt64.toUInt32 (t'8))))
    let t'10 ← PMem.ldU64 t'9
    let t'11 ← PMem.strlen t'10
    let mut nlen : UInt64 := t'11
    let t'12 ← PMem.ldBits token 0 9
    let t'13 ← AP_Param.var_info (UInt32.toUInt16 ((UInt64.toUInt32 (t'12))))
    let t'14 ← PMem.ldU64 t'13
    let t'15 ← PMem.strncasecmp name t'14 nlen
    let mut ret : Int32 := t'15
    if (ret == (0 : Int32)) then
      AP_Param.copy_name_token ap token (fp + 0) (Int64.toUInt64 (Int32.toInt64 ((16 : Int32)))) false
      let t'16 ← PMem.strncasecmp name (fp + 0) (Int64.toUInt64 (Int32.toInt64 ((16 : Int32))))
      if (t'16 == (0 : Int32)) then
        break
  return ap

def AP_Param.find_by_name (name : UInt64) (ptype : UInt64) (token : UInt64) : PMem.M UInt64 := do
  let fp ← PMem.enter 16
  let r ← AP_Param.find_by_name.body fp name ptype token
  PMem.leave fp
  return r

mutual

/-- C++ `AP_Param::find_group : AP_Param *(const char *, uint16_t, ptrdiff_t, const struct GroupInfo *, enum ap_var_type *)`, `AP_Param.cpp:874-933`. -/
def AP_Param.find_group.body'rec (rec'depth : Nat) (fp : UInt64) (name : UInt64) (vindex : UInt16) (group_offset : Int64) (group_info : UInt64) (ptype : UInt64) : PMem.M UInt64 := do
  let rec'd + 1 := rec'depth | PMem.depthOut
  let mut name := name
  let mut vindex := vindex
  let mut group_offset := group_offset
  let mut group_info := group_info
  let mut ptype := ptype
  let mut type' : UInt8 := default  -- uninitialized in C
  let mut i : UInt8 := Int8.toUInt8 (Int32.toInt8 ((0 : Int32)))
  let mut first'1 := true
  for _ in PMem.loopFuel do
    if !first'1 then
      let t'2 := i
      let t'3 := (t'2 + 1)
      i := t'3
      pure ()
    first'1 := false
    let t'4 ← PMem.ldU8 ((group_info + ((UInt64.toInt64 (UInt8.toUInt64 (i))) * 32).toUInt64) + 27)
    type' := t'4
    if !(((UInt32.toInt32 (UInt8.toUInt32 (type'))) != (UInt32.toInt32 ((0 : UInt32))))) then break
    if ((UInt32.toInt32 (UInt8.toUInt32 (type'))) == (UInt32.toInt32 ((6 : UInt32)))) then
      let t'5 ← PMem.ldU64 (group_info + ((UInt64.toInt64 (UInt8.toUInt64 (i))) * 32).toUInt64)
      let t'6 ← PMem.ldU64 (group_info + ((UInt64.toInt64 (UInt8.toUInt64 (i))) * 32).toUInt64)
      let t'7 ← PMem.strlen t'6
      let t'8 ← PMem.strncasecmp name t'5 t'7
      if (t'8 != (0 : Int32)) then
        continue
      let t'9 ← AP_Param.get_group_info'2 (group_info + ((UInt64.toInt64 (UInt8.toUInt64 (i))) * 32).toUInt64)
      let mut ginfo : UInt64 := t'9
      if (ginfo == (0 : UInt64)) then
        continue
      PMem.stI64 (fp + 0) group_offset
      let t'10 ← AP_Param.adjust_group_offset vindex (group_info + ((UInt64.toInt64 (UInt8.toUInt64 (i))) * 32).toUInt64) (fp + 0)
      if !t'10 then
        continue
      let t'11 ← PMem.ldU64 (group_info + ((UInt64.toInt64 (UInt8.toUInt64 (i))) * 32).toUInt64)
      let t'12 ← PMem.strlen t'11
      let t'13 ← PMem.ldI64 (fp + 0)
      let t'14 ← AP_Param.find_group'rec rec'd (name + ((UInt64.toInt64 (t'12)) * 1).toUInt64) vindex t'13 ginfo ptype
      let mut ap : UInt64 := t'14
      if (ap != (0 : UInt64)) then
        return ap
    else
      let t'15 ← PMem.ldU64 (group_info + ((UInt64.toInt64 (UInt8.toUInt64 (i))) * 32).toUInt64)
      let t'16 ← PMem.strcasecmp name t'15
      if (t'16 == (0 : Int32)) then
        let t'17 ← AP_Param.var_info vindex
        let t'18 ← AP_Param.get_base t'17 (fp + 8)
        if !t'18 then
          continue
        let t'19 := UInt8.toUInt32 (type')
        PMem.stU32 ptype t'19
        let t'20 ← PMem.ldI64 (fp + 8)
        let t'21 ← PMem.ldI64 ((group_info + ((UInt64.toInt64 (UInt8.toUInt64 (i))) * 32).toUInt64) + 8)
        return Int64.toUInt64 (((t'20 + t'21) + group_offset))
      else
        if ((UInt32.toInt32 (UInt8.toUInt32 (type'))) == (UInt32.toInt32 ((5 : UInt32)))) then
          let t'22 ← PMem.ldU64 (group_info + ((UInt64.toInt64 (UInt8.toUInt64 (i))) * 32).toUInt64)
          let t'23 ← PMem.strnlen t'22 (Int64.toUInt64 (Int32.toInt64 ((16 : Int32))))
          let mut suffix_len : UInt8 := UInt64.toUInt8 (t'23)
          let t'24 ← PMem.ldU64 (group_info + ((UInt64.toInt64 (UInt8.toUInt64 (i))) * 32).toUInt64)
          let t'25 ← PMem.strncmp name t'24 (UInt8.toUInt64 (suffix_len))
          let mut sc'27 := (t'25 == (0 : Int32))
          if sc'27 then
            let t'26 ← PMem.ldI8 (name + ((UInt64.toInt64 (UInt8.toUInt64 (suffix_len))) * 1).toUInt64)
            sc'27 := ((Int8.toInt32 (t'26)) == (Int8.toInt32 ((95 : Int8))))
          let mut sc'33 := sc'27
          if sc'33 then
            let t'28 ← PMem.ldI8 (name + ((Int32.toInt64 (((UInt32.toInt32 (UInt8.toUInt32 (suffix_len))) + (1 : Int32)))) * 1).toUInt64)
            let mut sc'30 := ((Int8.toInt32 (t'28)) == (Int8.toInt32 ((88 : Int8))))
            if !sc'30 then
              let t'29 ← PMem.ldI8 (name + ((Int32.toInt64 (((UInt32.toInt32 (UInt8.toUInt32 (suffix_len))) + (1 : Int32)))) * 1).toUInt64)
              sc'30 := ((Int8.toInt32 (t'29)) == (Int8.toInt32 ((89 : Int8))))
            let mut sc'32 := sc'30
            if !sc'32 then
              let t'31 ← PMem.ldI8 (name + ((Int32.toInt64 (((UInt32.toInt32 (UInt8.toUInt32 (suffix_len))) + (1 : Int32)))) * 1).toUInt64)
              sc'32 := ((Int8.toInt32 (t'31)) == (Int8.toInt32 ((90 : Int8))))
            sc'33 := sc'32
          if sc'33 then
            let t'34 ← AP_Param.var_info vindex
            let t'35 ← AP_Param.get_base t'34 (fp + 16)
            if !t'35 then
              continue
            let t'36 ← PMem.ldI64 (fp + 16)
            let t'37 ← PMem.ldI64 ((group_info + ((UInt64.toInt64 (UInt8.toUInt64 (i))) * 32).toUInt64) + 8)
            let mut v : UInt64 := Int64.toUInt64 (((t'36 + t'37) + group_offset))
            PMem.stU32 ptype (4 : UInt32)
            let t'38 ← PMem.ldI8 (name + ((Int32.toInt64 (((UInt32.toInt32 (UInt8.toUInt32 (suffix_len))) + (1 : Int32)))) * 1).toUInt64)
            let sw'39 := Int8.toInt32 (t'38)
            if sw'39 == (88 : Int32) then
              return (v + ((Int32.toInt64 ((0 : Int32))) * 4).toUInt64)
            else if sw'39 == (89 : Int32) then
              return (v + ((Int32.toInt64 ((1 : Int32))) * 4).toUInt64)
            else if sw'39 == (90 : Int32) then
              return (v + ((Int32.toInt64 ((2 : Int32))) * 4).toUInt64)
            else
              pure ()
  return (0 : UInt64)

def AP_Param.find_group'rec (rec'depth : Nat) (name : UInt64) (vindex : UInt16) (group_offset : Int64) (group_info : UInt64) (ptype : UInt64) : PMem.M UInt64 := do
  let rec'd + 1 := rec'depth | PMem.depthOut
  let fp ← PMem.enter 24
  let r ← AP_Param.find_group.body'rec rec'd fp name vindex group_offset group_info ptype
  PMem.leave fp
  return r

end

/-- `AP_Param.find_group.body'rec` with the depth of its recursive component (64). -/
def AP_Param.find_group.body (fp : UInt64) (name : UInt64) (vindex : UInt16) (group_offset : Int64) (group_info : UInt64) (ptype : UInt64) : PMem.M UInt64 :=
  AP_Param.find_group.body'rec 64 fp name vindex group_offset group_info ptype

/-- `AP_Param.find_group'rec` with the depth of its recursive component (64). -/
def AP_Param.find_group (name : UInt64) (vindex : UInt16) (group_offset : Int64) (group_info : UInt64) (ptype : UInt64) : PMem.M UInt64 :=
  AP_Param.find_group'rec 64 name vindex group_offset group_info ptype

/-- C++ `AP_Param::find : AP_Param *(const char *, enum ap_var_type *, uint16_t *)`, `AP_Param.cpp:938-985`. -/
def AP_Param.find.body (fp : UInt64) (name : UInt64) (ptype : UInt64) (flags : UInt64) : PMem.M UInt64 := do
  let mut name := name
  let mut ptype := ptype
  let mut flags := flags
  let mut i : UInt16 := Int16.toUInt16 (Int32.toInt16 ((0 : Int32)))
  let mut first'1 := true
  for _ in PMem.loopFuel do
    if !first'1 then
      let t'2 := i
      let t'3 := (t'2 + 1)
      i := t'3
      pure ()
    first'1 := false
    let t'4 ← PMem.ldU16 (0xba78 : UInt64) /- &AP_Param::_num_vars -/
    if !((decide ((UInt32.toInt32 (UInt16.toUInt32 (i))) < (UInt32.toInt32 (UInt16.toUInt32 (t'4)))))) then break
    let t'5 ← AP_Param.var_info i
    let info' : UInt64 := t'5
    let t'6 ← PMem.ldU8 (info' + 28)
    let mut type' : UInt8 := t'6
    if ((UInt32.toInt32 (UInt8.toUInt32 (type'))) == (UInt32.toInt32 ((6 : UInt32)))) then
      let t'7 ← PMem.ldU64 info'
      let t'8 ← PMem.strnlen t'7 (Int64.toUInt64 (Int32.toInt64 ((16 : Int32))))
      let mut len : UInt8 := UInt64.toUInt8 (t'8)
      let t'9 ← PMem.ldU64 info'
      let t'10 ← PMem.strncmp name t'9 (UInt8.toUInt64 (len))
      if (t'10 != (0 : Int32)) then
        continue
      let t'11 ← AP_Param.get_group_info info'
      let mut group_info : UInt64 := t'11
      if (group_info == (0 : UInt64)) then
        continue
      let t'12 ← AP_Param.find_group (name + ((Int32.toInt64 ((UInt32.toInt32 (UInt8.toUInt32 (len))))) * 1).toUInt64) i (Int32.toInt64 ((0 : Int32))) group_info ptype
      let mut ap : UInt64 := t'12
      if (ap != (0 : UInt64)) then
        if (flags != (0 : UInt64)) then
          PMem.stU32 (fp + 0) (Int32.toUInt32 ((0 : Int32)))
          discard <| PMem.memset ((fp + 16) + 0) 0 1
          discard <| PMem.memset ((fp + 16) + 8) 0 16
          let t'13 ← AP_Param.find_var_info ap (fp + 0) (fp + 8) (fp + 16) (fp + 40)
          discard <| pure (t'13)
          let t'14 ← PMem.ldU64 (fp + 8)
          if (t'14 != (0 : UInt64)) then
            let t'15 ← PMem.ldU64 (fp + 8)
            let t'16 ← PMem.ldU16 (t'15 + 24)
            PMem.stU16 flags t'16
          else
            let t'17 := Int16.toUInt16 (Int32.toInt16 ((0 : Int32)))
            PMem.stU16 flags t'17
        return ap
    else
      let t'18 ← PMem.ldU64 info'
      let t'19 ← PMem.strcasecmp name t'18
      if (t'19 == (0 : Int32)) then
        let t'20 := UInt8.toUInt32 (type')
        PMem.stU32 ptype t'20
        let t'21 ← AP_Param.get_base info' (fp + 48)
        if !t'21 then
          return (0 : UInt64)
        if (flags != (0 : UInt64)) then
          let t'22 := Int16.toUInt16 (Int32.toInt16 ((0 : Int32)))
          PMem.stU16 flags t'22
        let t'23 ← PMem.ldI64 (fp + 48)
        return Int64.toUInt64 (t'23)
  return (0 : UInt64)

def AP_Param.find (name : UInt64) (ptype : UInt64) (flags : UInt64) : PMem.M UInt64 := do
  let fp ← PMem.enter 56
  let r ← AP_Param.find.body fp name ptype flags
  PMem.leave fp
  return r

/-- C++ `AP_Param::find_by_index : AP_Param *(uint16_t, enum ap_var_type *, ParamToken *)`, `AP_Param.cpp:989-1000`. -/
def AP_Param.find_by_index (idx : UInt16) (ptype : UInt64) (token : UInt64) : PMem.M UInt64 := do
  let mut idx := idx
  let mut ptype := ptype
  let mut token := token
  let mut ap : UInt64 := default  -- uninitialized in C
  let mut count : UInt16 := Int16.toUInt16 (Int32.toInt16 ((0 : Int32)))
  let t'1 ← AP_Param.first token ptype (0 : UInt64)
  ap := t'1
  let mut first'2 := true
  for _ in PMem.loopFuel do
    if !first'2 then
      let t'3 ← AP_Param.next_scalar token ptype (0 : UInt64)
      ap := t'3
      pure ()
    first'2 := false
    if !(((ap != 0) && (decide ((UInt32.toInt32 (UInt16.toUInt32 (count))) < (UInt32.toInt32 (UInt16.toUInt32 (idx))))))) then break
    let t'4 := count
    let t'5 := (t'4 + 1)
    count := t'5
  return ap

/-- C++ `AP_Param::count_parameters : uint16_t ()`, `AP_Param.cpp:2752-2782`. -/
def AP_Param.count_parameters.body (fp : UInt64)  : PMem.M UInt16 := do
  let t'1 ← PMem.ldU16 (0xbb88 : UInt64) /- &AP_Param::_parameter_count -/
  let mut sc'4 := ((UInt32.toInt32 (UInt16.toUInt32 (t'1))) != (0 : Int32))
  if sc'4 then
    let t'2 ← PMem.ldU16 (0xbb90 : UInt64) /- &AP_Param::_count_marker -/
    let t'3 ← PMem.ldU16 (0xbb98 : UInt64) /- &AP_Param::_count_marker_done -/
    sc'4 := ((UInt32.toInt32 (UInt16.toUInt32 (t'2))) == (UInt32.toInt32 (UInt16.toUInt32 (t'3))))
  if sc'4 then
    let t'5 ← PMem.ldU16 (0xbb88 : UInt64) /- &AP_Param::_parameter_count -/
    return t'5
  let mut limit : UInt8 := Int8.toUInt8 (Int32.toInt8 ((4 : Int32)))
  for _ in PMem.loopFuel do
    let t'6 ← PMem.ldU16 (0xbb88 : UInt64) /- &AP_Param::_parameter_count -/
    let mut sc'9 := ((UInt32.toInt32 (UInt16.toUInt32 (t'6))) == (0 : Int32))
    if !sc'9 then
      let t'7 ← PMem.ldU16 (0xbb90 : UInt64) /- &AP_Param::_count_marker -/
      let t'8 ← PMem.ldU16 (0xbb98 : UInt64) /- &AP_Param::_count_marker_done -/
      sc'9 := ((UInt32.toInt32 (UInt16.toUInt32 (t'7))) != (UInt32.toInt32 (UInt16.toUInt32 (t'8))))
    let mut sc'12 := sc'9
    if sc'12 then
      let t'10 := limit
      let t'11 := (t'10 - 1)
      limit := t'11
      sc'12 := t'10 != (0 : UInt8)
    if !(sc'12) then break
    let mut vp : UInt64 := default  -- uninitialized in C
    PMem.stBits (fp + 0) 0 9 (UInt32.toUInt64 ((0 : UInt32)))
    PMem.stBits (fp + 0) 9 4 (UInt32.toUInt64 ((0 : UInt32)))
    PMem.stBits (fp + 0) 13 18 (UInt32.toUInt64 ((0 : UInt32)))
    PMem.stBits (fp + 0) 31 1 (UInt32.toUInt64 ((0 : UInt32)))
    let mut count : UInt16 := Int16.toUInt16 (Int32.toInt16 ((0 : Int32)))
    let t'13 ← PMem.ldU16 (0xbb90 : UInt64) /- &AP_Param::_count_marker -/
    let mut marker : UInt16 := t'13
    let t'14 ← AP_Param.first (fp + 0) (0 : UInt64) (0 : UInt64)
    vp := t'14
    let mut first'15 := true
    for _ in PMem.loopFuel do
      if !first'15 then
        let t'16 ← AP_Param.next_scalar (fp + 0) (0 : UInt64) (0 : UInt64)
        vp := t'16
        pure ()
      first'15 := false
      if !((vp != (0 : UInt64))) then break
      let t'17 := count
      let t'18 := (t'17 + 1)
      count := t'18
    PMem.stU16 (0xbb88 : UInt64) /- &AP_Param::_parameter_count -/ count
    PMem.stU16 (0xbb98 : UInt64) /- &AP_Param::_count_marker_done -/ marker
  let t'19 ← PMem.ldU16 (0xbb88 : UInt64) /- &AP_Param::_parameter_count -/
  return t'19

def AP_Param.count_parameters  : PMem.M UInt16 := do
  let fp ← PMem.enter 4
  let r ← AP_Param.count_parameters.body fp 
  PMem.leave fp
  return r

/-- C++ `AP_ParamTBase<signed char, 1>::cast_to_float : float () const`, `AP_ParamT.cpp:104-106`. -/
def AP_ParamTBase'signed_char_1.cast_to_float (this : UInt64) : PMem.M Binary32 := do
  let t'1 ← PMem.ldI8 this
  return Int8.toBinary32 (t'1)

/-- C++ `AP_ParamTBase<short, 2>::cast_to_float : float () const`, `AP_ParamT.cpp:104-106`. -/
def AP_ParamTBase'short_2.cast_to_float (this : UInt64) : PMem.M Binary32 := do
  let t'1 ← PMem.ldI16 this
  return Int16.toBinary32 (t'1)

/-- C++ `AP_ParamTBase<int, 3>::cast_to_float : float () const`, `AP_ParamT.cpp:104-106`. -/
def AP_ParamTBase'int_3.cast_to_float (this : UInt64) : PMem.M Binary32 := do
  let t'1 ← PMem.ldI32 this
  return Int32.toBinary32 (t'1)

/-- C++ `AP_ParamTBase<float, 4>::cast_to_float : float () const`, `AP_ParamT.cpp:104-106`. -/
def AP_ParamTBase'float_4.cast_to_float (this : UInt64) : PMem.M Binary32 := do
  let t'1 ← PMem.ldF32 this
  return t'1

/-- C++ `AP_Param::cast_to_float : float (enum ap_var_type) const`, `AP_Param.cpp:1976-1990`. -/
def AP_Param.cast_to_float (this : UInt64) (type' : UInt32) : PMem.M Binary32 := do
  let mut type' := type'
  let sw'1 := UInt32.toInt32 (type')
  if sw'1 == (1 : Int32) then
    let t'2 ← AP_ParamTBase'signed_char_1.cast_to_float this
    return t'2
  else if sw'1 == (2 : Int32) then
    let t'3 ← AP_ParamTBase'short_2.cast_to_float this
    return t'3
  else if sw'1 == (3 : Int32) then
    let t'4 ← AP_ParamTBase'int_3.cast_to_float this
    return t'4
  else if sw'1 == (4 : Int32) then
    let t'5 ← AP_ParamTBase'float_4.cast_to_float this
    return t'5
  else
    return (Binary32.ofBits 0x7fc00000)

/-- C++ `AP_Param::set_float : void (float, enum ap_var_type)`, `AP_Param.cpp:2299-2329`. -/
def AP_Param.set_float.body (fp : UInt64) (this : UInt64) (value : Binary32) (var_type : UInt32) : PMem.M Unit := do
  PMem.stF32 (fp + 0) value
  let mut var_type := var_type
  let t'1 ← PMem.ldF32 (fp + 0)
  let mut sc'3 := (Binary32.isNaN t'1)
  if !sc'3 then
    let t'2 ← PMem.ldF32 (fp + 0)
    sc'3 := (Binary32.isInf t'2)
  if sc'3 then
    return ()
  let mut rounding_addition : Binary32 := (Binary32.ofBits 0x3c23d70a /- 999999977/100000000000 -/)
  if ((UInt32.toInt32 (var_type)) == (UInt32.toInt32 ((4 : UInt32)))) then
    AP_ParamTBase'float_4.set this (fp + 0)
  else
    if ((UInt32.toInt32 (var_type)) == (UInt32.toInt32 ((3 : UInt32)))) then
      let t'4 ← PMem.ldF32 (fp + 0)
      if (decide (t'4 < (Int32.toBinary32 ((0 : Int32))))) then
        let t'5 := -rounding_addition
        rounding_addition := t'5
      let t'6 ← PMem.ldF32 (fp + 0)
      let mut v : Binary32 := (t'6 + rounding_addition)
      let t'7 ← constrain_value_line'float v (Int32.toBinary32 (((-(2147483647 : Int32)) - (1 : Int32)))) (Int32.toBinary32 ((2147483647 : Int32))) (Int32.toUInt32 ((2316 : Int32)))
      v := t'7
      PMem.stI32 (fp + 4) (Binary32.toInt32 (v))
      AP_ParamTBase'int_3.set this (fp + 4)
    else
      if ((UInt32.toInt32 (var_type)) == (UInt32.toInt32 ((2 : UInt32)))) then
        let t'8 ← PMem.ldF32 (fp + 0)
        if (decide (t'8 < (Int32.toBinary32 ((0 : Int32))))) then
          let t'9 := -rounding_addition
          rounding_addition := t'9
        let t'10 ← PMem.ldF32 (fp + 0)
        let mut v'2 : Binary32 := (t'10 + rounding_addition)
        let t'11 ← constrain_value_line'float v'2 (Int32.toBinary32 ((-(32768 : Int32)))) (Int32.toBinary32 ((32767 : Int32))) (Int32.toUInt32 ((2321 : Int32)))
        v'2 := t'11
        PMem.stI16 (fp + 8) (Binary32.toInt16 (v'2))
        AP_ParamTBase'short_2.set this (fp + 8)
      else
        if ((UInt32.toInt32 (var_type)) == (UInt32.toInt32 ((1 : UInt32)))) then
          let t'12 ← PMem.ldF32 (fp + 0)
          if (decide (t'12 < (Int32.toBinary32 ((0 : Int32))))) then
            let t'13 := -rounding_addition
            rounding_addition := t'13
          let t'14 ← PMem.ldF32 (fp + 0)
          let mut v'3 : Binary32 := (t'14 + rounding_addition)
          let t'15 ← constrain_value_line'float v'3 (Int32.toBinary32 ((-(128 : Int32)))) (Int32.toBinary32 ((127 : Int32))) (Int32.toUInt32 ((2326 : Int32)))
          v'3 := t'15
          PMem.stI8 (fp + 10) (Binary32.toInt8 (v'3))
          AP_ParamTBase'signed_char_1.set this (fp + 10)
  return ()

def AP_Param.set_float (this : UInt64) (value : Binary32) (var_type : UInt32) : PMem.M Unit := do
  let fp ← PMem.enter 11
  let r ← AP_Param.set_float.body fp this value var_type
  PMem.leave fp
  return r

/-- C++ `AP_Param::invalidate_count : void ()`, `AP_Param.cpp:2787-2793`. -/
def AP_Param.invalidate_count  : PMem.M Unit := do
  let t'1 := (0xbb90 : UInt64) /- &AP_Param::_count_marker -/
  let t'2 ← PMem.ldU16 t'1
  let t'3 := (t'2 + 1)
  PMem.stU16 t'1 t'3
  return ()

/-- `AP_ParamT'unsigned_short_2.operator_const_unsigned_short__` as a pure function of its arguments (it reads and writes no memory). -/
def AP_ParamT'unsigned_short_2.operator_const_unsigned_short__.pure' (this : UInt64) : Id UInt64 := do
  return this

/-- C++ `AP_ParamT<unsigned short, 2>::operator const unsigned short & : const unsigned short &() const`, `AP_Param.h:978-980`. -/
def AP_ParamT'unsigned_short_2.operator_const_unsigned_short__ (this : UInt64) : PMem.M UInt64 :=
  pure (_root_.Vehicle_lib.AP_ParamT'unsigned_short_2.operator_const_unsigned_short__.pure' this)

/-- `AP_ParamV'Vector3_float_5.get` as a pure function of its arguments (it reads and writes no memory). -/
def AP_ParamV'Vector3_float_5.get.pure' (this : UInt64) : Id UInt64 := do
  return this

/-- C++ `AP_ParamV<Vector3<float>, 5>::get : const Vector3<float> &() const`, `AP_Param.h:1059-1061`. -/
def AP_ParamV'Vector3_float_5.get (this : UInt64) : PMem.M UInt64 :=
  pure (_root_.Vehicle_lib.AP_ParamV'Vector3_float_5.get.pure' this)

mutual

/-- C++ `AP_Param::find_key_by_pointer_group : bool (const void *, uint16_t, const struct GroupInfo *, ptrdiff_t, uint16_t &)`, `AP_Param.cpp:1030-1064`. -/
def AP_Param.find_key_by_pointer_group.body'rec (rec'depth : Nat) (fp : UInt64) (ptr' : UInt64) (vindex : UInt16) (group_info : UInt64) (offset : Int64) (key : UInt64) : PMem.M Bool := do
  let rec'd + 1 := rec'depth | PMem.depthOut
  let mut ptr' := ptr'
  let mut vindex := vindex
  let mut group_info := group_info
  let mut offset := offset
  let mut i : UInt8 := Int8.toUInt8 (Int32.toInt8 ((0 : Int32)))
  let mut first'1 := true
  for _ in PMem.loopFuel do
    if !first'1 then
      let t'2 := i
      let t'3 := (t'2 + 1)
      i := t'3
      pure ()
    first'1 := false
    let t'4 ← PMem.ldU8 ((group_info + ((UInt64.toInt64 (UInt8.toUInt64 (i))) * 32).toUInt64) + 27)
    if !(((UInt32.toInt32 (UInt8.toUInt32 (t'4))) != (UInt32.toInt32 ((0 : UInt32))))) then break
    let t'5 ← PMem.ldU8 ((group_info + ((UInt64.toInt64 (UInt8.toUInt64 (i))) * 32).toUInt64) + 27)
    if ((UInt32.toInt32 (UInt8.toUInt32 (t'5))) != (UInt32.toInt32 ((6 : UInt32)))) then
      continue
    let t'6 ← AP_Param.var_info vindex
    let t'7 ← AP_Param.get_base t'6 (fp + 0)
    if !t'7 then
      continue
    let t'8 ← PMem.ldU16 ((group_info + ((UInt64.toInt64 (UInt8.toUInt64 (i))) * 32).toUInt64) + 24)
    if ((UInt32.toInt32 (UInt16.toUInt32 (t'8))) &&& ((1 : Int32) <<< (1 : Int32))) != (0 : Int32) then
      let t'9 ← PMem.ldI64 (fp + 0)
      let t'10 ← PMem.ldI64 ((group_info + ((UInt64.toInt64 (UInt8.toUInt64 (i))) * 32).toUInt64) + 8)
      let t'11 ← PMem.ldU64 (Int64.toUInt64 (((t'9 + t'10) + offset)))
      if (ptr' == t'11) then
        let t'12 ← AP_Param.var_info vindex
        let t'13 ← PMem.ldU16 (t'12 + 26)
        PMem.stU16 key t'13
        return true
    else
      let t'14 ← PMem.ldI64 (fp + 0)
      let t'15 ← PMem.ldI64 ((group_info + ((UInt64.toInt64 (UInt8.toUInt64 (i))) * 32).toUInt64) + 8)
      if (ptr' == (Int64.toUInt64 (((t'14 + t'15) + offset)))) then
        let t'16 ← AP_Param.var_info vindex
        let t'17 ← PMem.ldU16 (t'16 + 26)
        PMem.stU16 key t'17
        return true
    PMem.stI64 (fp + 8) offset
    let t'18 ← AP_Param.adjust_group_offset vindex (group_info + ((UInt64.toInt64 (UInt8.toUInt64 (i))) * 32).toUInt64) (fp + 8)
    if !t'18 then
      continue
    let t'19 ← AP_Param.get_group_info'2 (group_info + ((UInt64.toInt64 (UInt8.toUInt64 (i))) * 32).toUInt64)
    let mut ginfo : UInt64 := t'19
    if (ginfo == (0 : UInt64)) then
      continue
    let t'20 ← PMem.ldI64 (fp + 8)
    let t'21 ← AP_Param.find_key_by_pointer_group'rec rec'd ptr' vindex ginfo t'20 key
    if t'21 then
      return true
  return false

def AP_Param.find_key_by_pointer_group'rec (rec'depth : Nat) (ptr' : UInt64) (vindex : UInt16) (group_info : UInt64) (offset : Int64) (key : UInt64) : PMem.M Bool := do
  let rec'd + 1 := rec'depth | PMem.depthOut
  let fp ← PMem.enter 16
  let r ← AP_Param.find_key_by_pointer_group.body'rec rec'd fp ptr' vindex group_info offset key
  PMem.leave fp
  return r

end

/-- `AP_Param.find_key_by_pointer_group.body'rec` with the depth of its recursive component (64). -/
def AP_Param.find_key_by_pointer_group.body (fp : UInt64) (ptr' : UInt64) (vindex : UInt16) (group_info : UInt64) (offset : Int64) (key : UInt64) : PMem.M Bool :=
  AP_Param.find_key_by_pointer_group.body'rec 64 fp ptr' vindex group_info offset key

/-- `AP_Param.find_key_by_pointer_group'rec` with the depth of its recursive component (64). -/
def AP_Param.find_key_by_pointer_group (ptr' : UInt64) (vindex : UInt16) (group_info : UInt64) (offset : Int64) (key : UInt64) : PMem.M Bool :=
  AP_Param.find_key_by_pointer_group'rec 64 ptr' vindex group_info offset key

/-- C++ `AP_Param::find_key_by_pointer : bool (const void *, uint16_t &)`, `AP_Param.cpp:1070-1092`. -/
def AP_Param.find_key_by_pointer (ptr' : UInt64) (key : UInt64) : PMem.M Bool := do
  let mut ptr' := ptr'
  let mut i : UInt16 := Int16.toUInt16 (Int32.toInt16 ((0 : Int32)))
  let mut first'1 := true
  for _ in PMem.loopFuel do
    if !first'1 then
      let t'2 := i
      let t'3 := (t'2 + 1)
      i := t'3
      pure ()
    first'1 := false
    let t'4 ← PMem.ldU16 (0xba78 : UInt64) /- &AP_Param::_num_vars -/
    if !((decide ((UInt32.toInt32 (UInt16.toUInt32 (i))) < (UInt32.toInt32 (UInt16.toUInt32 (t'4)))))) then break
    let t'5 ← AP_Param.var_info i
    let info' : UInt64 := t'5
    let t'6 ← PMem.ldU8 (info' + 28)
    if ((UInt32.toInt32 (UInt8.toUInt32 (t'6))) != (UInt32.toInt32 ((6 : UInt32)))) then
      continue
    let t'7 ← PMem.ldU16 (info' + 24)
    let mut sc'10 := ((UInt32.toInt32 (UInt16.toUInt32 (t'7))) &&& ((1 : Int32) <<< (1 : Int32))) != (0 : Int32)
    if sc'10 then
      let t'8 ← PMem.ldU64 (info' + 8)
      let t'9 ← PMem.ldU64 t'8
      sc'10 := (ptr' == t'9)
    if sc'10 then
      let t'11 ← PMem.ldU16 (info' + 26)
      PMem.stU16 key t'11
      return true
    let mut offset : Int64 := Int32.toInt64 ((0 : Int32))
    let t'12 ← AP_Param.get_group_info info'
    let mut ginfo : UInt64 := t'12
    if (ginfo == (0 : UInt64)) then
      continue
    let t'13 ← AP_Param.find_key_by_pointer_group ptr' i ginfo offset key
    if t'13 then
      return true
  return false

mutual

/-- C++ `AP_Param::load_object_from_eeprom : void (const void *, const struct GroupInfo *)`, `AP_Param.cpp:1705-1761`. -/
def AP_Param.load_object_from_eeprom.body'rec (rec'depth : Nat) (fp : UInt64) (object_pointer : UInt64) (group_info : UInt64) : PMem.M Unit := do
  let rec'd + 1 := rec'depth | PMem.depthOut
  let mut object_pointer := object_pointer
  let mut group_info := group_info
  AP_Param.Param_header.Param_header (fp + 0)
  let t'1 ← AP_Param.find_key_by_pointer object_pointer (fp + 8)
  if !t'1 then
    for _ in [0:1] do
      let t'2 ← PMem.ldU64 ((0xba88 : UInt64) /- &hal -/ + 48)
      discard <| PMem.halDev "AP_HAL::BetterStream::printf" t'2 #[(0x181a9 : UInt64) /- "ERROR: Unable to find param pointer\n" -/]
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
    let t'6 ← PMem.ldU8 ((group_info + ((UInt64.toInt64 (UInt8.toUInt64 (i))) * 32).toUInt64) + 27)
    if !(((UInt32.toInt32 (UInt8.toUInt32 (t'6))) != (UInt32.toInt32 ((0 : UInt32))))) then break
    let t'7 ← PMem.ldU8 ((group_info + ((UInt64.toInt64 (UInt8.toUInt64 (i))) * 32).toUInt64) + 27)
    if ((UInt32.toInt32 (UInt8.toUInt32 (t'7))) == (UInt32.toInt32 ((6 : UInt32)))) then
      PMem.stI64 (fp + 16) (Int32.toInt64 ((0 : Int32)))
      let t'8 ← PMem.ldU16 (fp + 8)
      let t'9 ← AP_Param.adjust_group_offset t'8 (group_info + ((UInt64.toInt64 (UInt8.toUInt64 (i))) * 32).toUInt64) (fp + 16)
      if !t'9 then
        continue
      let t'10 ← AP_Param.get_group_info'2 (group_info + ((UInt64.toInt64 (UInt8.toUInt64 (i))) * 32).toUInt64)
      let mut ginfo : UInt64 := t'10
      if (ginfo != (0 : UInt64)) then
        let t'11 ← PMem.ldI64 (fp + 16)
        AP_Param.load_object_from_eeprom'rec rec'd (Int64.toUInt64 (((UInt64.toInt64 (object_pointer)) + t'11))) ginfo
    let mut ofs : UInt16 := UInt64.toUInt16 ((4 : UInt64))
    for _ in PMem.loopFuel do
      let t'12 ← StorageAccess.size (0xbb70 : UInt64) /- &AP_Param::_storage -/
      if !((decide ((UInt32.toInt32 (UInt16.toUInt32 (ofs))) < (UInt32.toInt32 (UInt16.toUInt32 (t'12)))))) then break
      let t'13 ← StorageAccess.read_block (0xbb70 : UInt64) /- &AP_Param::_storage -/ (fp + 0) ofs (4 : UInt64)
      discard <| pure (t'13)
      let t'14 ← AP_Param.is_sentinel (fp + 0)
      if t'14 then
        PMem.stU16 (0xbb80 : UInt64) /- &AP_Param::sentinel_offset -/ ofs
        break
      let t'15 ← AP_Param.get_key (fp + 0)
      let t'16 ← PMem.ldU16 (fp + 8)
      if ((UInt32.toInt32 (UInt16.toUInt32 (t'15))) == (UInt32.toInt32 (UInt16.toUInt32 (t'16)))) then
        let mut info' : UInt64 := default  -- uninitialized in C
        AP_Param.Param_header.Param_header'2 (fp + 32) (fp + 0)
        let t'17 ← AP_Param.find_by_header (fp + 32) (fp + 24)
        info' := t'17
        if (info' != (0 : UInt64)) then
          let t'18 ← PMem.ldU64 (fp + 24)
          let t'19 ← PMem.ldI64 ((group_info + ((UInt64.toInt64 (UInt8.toUInt64 (i))) * 32).toUInt64) + 8)
          if ((UInt64.toInt64 (t'18)) == ((UInt64.toInt64 (object_pointer)) + t'19)) then
            let t'20 ← PMem.ldU64 (fp + 24)
            let t'21 ← PMem.ldBits (fp + 0) 8 5
            let t'22 ← AP_Param.type_size (UInt64.toUInt32 (t'21))
            let t'23 ← StorageAccess.read_block (0xbb70 : UInt64) /- &AP_Param::_storage -/ t'20 (UInt64.toUInt16 (((UInt16.toUInt64 (ofs)) + (4 : UInt64)))) (UInt8.toUInt64 (t'22))
            discard <| pure (t'23)
            break
      let t'24 ← PMem.ldBits (fp + 0) 8 5
      let t'25 ← AP_Param.type_size (UInt64.toUInt32 (t'24))
      let t'26 := (ofs + (UInt64.toUInt16 (((UInt8.toUInt64 (t'25)) + (4 : UInt64)))))
      ofs := t'26
  let t'27 ← PMem.ldB (0xbba8 : UInt64) /- &AP_Param::done_all_default_params -/
  if !t'27 then
    AP_Param.reload_defaults_file false
  AP_Param.invalidate_count
  return ()

def AP_Param.load_object_from_eeprom'rec (rec'depth : Nat) (object_pointer : UInt64) (group_info : UInt64) : PMem.M Unit := do
  let rec'd + 1 := rec'depth | PMem.depthOut
  let fp ← PMem.enter 36
  let r ← AP_Param.load_object_from_eeprom.body'rec rec'd fp object_pointer group_info
  PMem.leave fp
  return r

end

/-- `AP_Param.load_object_from_eeprom.body'rec` with the depth of its recursive component (64). -/
def AP_Param.load_object_from_eeprom.body (fp : UInt64) (object_pointer : UInt64) (group_info : UInt64) : PMem.M Unit :=
  AP_Param.load_object_from_eeprom.body'rec 64 fp object_pointer group_info

/-- `AP_Param.load_object_from_eeprom'rec` with the depth of its recursive component (64). -/
def AP_Param.load_object_from_eeprom (object_pointer : UInt64) (group_info : UInt64) : PMem.M Unit :=
  AP_Param.load_object_from_eeprom'rec 64 object_pointer group_info

/-- C++ `AP_Param::set_frame_type_flags : void (uint16_t)`, `AP_Param.h:599-602`. -/
def AP_Param.set_frame_type_flags (flags_to_set : UInt16) : PMem.M Unit := do
  let mut flags_to_set := flags_to_set
  AP_Param.invalidate_count
  let t'1 := (0xbbb0 : UInt64) /- &AP_Param::_frame_type_flags -/
  let t'2 ← PMem.ldU16 t'1
  let t'3 := (t'2 ||| (Int16.toUInt16 (Int32.toInt16 ((UInt32.toInt32 (UInt16.toUInt32 (flags_to_set)))))))
  PMem.stU16 t'1 t'3
  return ()

/-- C++ `AP_Param::AP_Param : void (const struct Info *)`, `AP_Param.h:263-276`. -/
def AP_Param.AP_Param (this : UInt64) (info' : UInt64) : PMem.M Unit := do
  let mut info' := info'
  PMem.stU64 (0xbbb8 : UInt64) /- &AP_Param::_var_info -/ info'
  let mut i : UInt16 := default  -- uninitialized in C
  let t'1 := Int16.toUInt16 (Int32.toInt16 ((0 : Int32)))
  i := t'1
  let mut first'2 := true
  for _ in PMem.loopFuel do
    if !first'2 then
      let t'3 := i
      let t'4 := (t'3 + 1)
      i := t'4
      pure ()
    first'2 := false
    let t'5 ← PMem.ldU8 ((info' + ((UInt64.toInt64 (UInt16.toUInt64 (i))) * 32).toUInt64) + 28)
    if !(((UInt32.toInt32 (UInt8.toUInt32 (t'5))) != (UInt32.toInt32 ((0 : UInt32))))) then break
  PMem.stU16 (0xba78 : UInt64) /- &AP_Param::_num_vars -/ i
  let t'6 ← PMem.ldU64 (0xbbc0 : UInt64) /- &AP_Param::_singleton -/
  if (t'6 != (0 : UInt64)) then
    pure ()
  PMem.stU64 (0xbbc0 : UInt64) /- &AP_Param::_singleton -/ this
  return ()

/-- `AP_Param.AP_Param'2` as a pure function of its arguments (it reads and writes no memory). -/
def AP_Param.AP_Param'2.pure' (this : UInt64) : Id Unit := do
  return ()

/-- C++ `AP_Param::AP_Param : void ()`, `AP_Param.h:279-?`. -/
def AP_Param.AP_Param'2 (this : UInt64) : PMem.M Unit :=
  pure (_root_.Vehicle_lib.AP_Param.AP_Param'2.pure' this)

/-- `AP_Param.param_save.param_save` as a pure function of its arguments (it reads and writes no memory). -/
def AP_Param.param_save.param_save.pure' (this : UInt64) : Id Unit := do
  return ()

/-- C++ `AP_Param::param_save::param_save : void () noexcept`, `AP_Common.h:873-?`. -/
def AP_Param.param_save.param_save (this : UInt64) : PMem.M Unit :=
  pure (_root_.Vehicle_lib.AP_Param.param_save.param_save.pure' this)

/-- C++ `AP_Param::add_default : void (AP_Param *, float)`, `AP_Param.cpp:3007-3036`. -/
def AP_Param.add_default (ap : UInt64) (v : Binary32) : PMem.M Unit := do
  let mut ap := ap
  let mut v := v
  let mut i : UInt16 := Int16.toUInt16 (Int32.toInt16 ((0 : Int32)))
  let mut first'1 := true
  for _ in PMem.loopFuel do
    if !first'1 then
      let t'2 := i
      let t'3 := (t'2 + 1)
      i := t'3
      pure ()
    first'1 := false
    let t'4 ← PMem.ldU16 (0xbf48 : UInt64) /- &AP_Param::num_param_overrides -/
    if !((decide ((UInt32.toInt32 (UInt16.toUInt32 (i))) < (UInt32.toInt32 (UInt16.toUInt32 (t'4)))))) then break
    let t'5 ← PMem.ldU64 (0xbf50 : UInt64) /- &AP_Param::param_overrides -/
    let t'6 ← PMem.ldU64 (t'5 + ((UInt64.toInt64 (UInt16.toUInt64 (i))) * 16).toUInt64)
    if (ap == t'6) then
      return ()
  let t'7 ← PMem.ldU64 (0xbf58 : UInt64) /- &AP_Param::default_list -/
  if (t'7 != (0 : UInt64)) then
    let t'8 ← PMem.ldU64 (0xbf58 : UInt64) /- &AP_Param::default_list -/
    let mut item : UInt64 := t'8
    let mut first'9 := true
    for _ in PMem.loopFuel do
      if !first'9 then
        let t'10 ← PMem.ldU64 (item + 16)
        item := t'10
        pure ()
      first'9 := false
      if !((item != 0)) then break
      let t'11 ← PMem.ldU64 item
      if (t'11 == ap) then
        PMem.stF32 (item + 8) v
        return ()
  let t'12 ← PMem.alloc 24
  let mut new_item : UInt64 := t'12
  if (new_item == (0 : UInt64)) then
    return ()
  PMem.stU64 new_item ap
  PMem.stF32 (new_item + 8) v
  let t'13 ← PMem.ldU64 (0xbf58 : UInt64) /- &AP_Param::default_list -/
  PMem.stU64 (new_item + 16) t'13
  PMem.stU64 (0xbf58 : UInt64) /- &AP_Param::default_list -/ new_item
  return ()

/-- C++ `default_as_float : float (const short &)`, `AP_ParamT.cpp:?-?`. -/
def default_as_float'short (v : UInt64) : PMem.M Binary32 := do
  let t'1 ← PMem.ldI16 v
  return Int16.toBinary32 (t'1)

/-- C++ `AP_Param::configured_in_defaults_file : bool (bool &) const`, `AP_Param.cpp:1431-1454`. -/
def AP_Param.configured_in_defaults_file.body (fp : UInt64) (this : UInt64) (read_only : UInt64) : PMem.M Bool := do
  let t'1 ← PMem.ldU16 (0xbf48 : UInt64) /- &AP_Param::num_param_overrides -/
  if ((UInt32.toInt32 (UInt16.toUInt32 (t'1))) == (0 : Int32)) then
    return false
  PMem.stU32 (fp + 0) (Int32.toUInt32 ((0 : Int32)))
  discard <| PMem.memset ((fp + 16) + 0) 0 1
  discard <| PMem.memset ((fp + 16) + 8) 0 16
  let t'2 ← AP_Param.find_var_info this (fp + 0) (fp + 8) (fp + 16) (fp + 40)
  let mut info' : UInt64 := t'2
  if (info' == (0 : UInt64)) then
    return false
  let mut i : UInt16 := Int16.toUInt16 (Int32.toInt16 ((0 : Int32)))
  let mut first'3 := true
  for _ in PMem.loopFuel do
    if !first'3 then
      let t'4 := i
      let t'5 := (t'4 + 1)
      i := t'5
      pure ()
    first'3 := false
    let t'6 ← PMem.ldU16 (0xbf48 : UInt64) /- &AP_Param::num_param_overrides -/
    if !((decide ((UInt32.toInt32 (UInt16.toUInt32 (i))) < (UInt32.toInt32 (UInt16.toUInt32 (t'6)))))) then break
    let t'7 ← PMem.ldU64 (0xbf50 : UInt64) /- &AP_Param::param_overrides -/
    let t'8 ← PMem.ldU64 (t'7 + ((UInt64.toInt64 (UInt16.toUInt64 (i))) * 16).toUInt64)
    if (this == t'8) then
      let t'9 ← PMem.ldU64 (0xbf50 : UInt64) /- &AP_Param::param_overrides -/
      let t'10 ← PMem.ldB ((t'9 + ((UInt64.toInt64 (UInt16.toUInt64 (i))) * 16).toUInt64) + 12)
      PMem.stB read_only t'10
      return true
  return false

def AP_Param.configured_in_defaults_file (this : UInt64) (read_only : UInt64) : PMem.M Bool := do
  let fp ← PMem.enter 41
  let r ← AP_Param.configured_in_defaults_file.body fp this read_only
  PMem.leave fp
  return r

/-- C++ `AP_Param::configured_in_storage : bool () const`, `AP_Param.cpp:1401-1429`. -/
def AP_Param.configured_in_storage.body (fp : UInt64) (this : UInt64) : PMem.M Bool := do
  PMem.stU32 (fp + 0) (Int32.toUInt32 ((0 : Int32)))
  discard <| PMem.memset ((fp + 16) + 0) 0 1
  discard <| PMem.memset ((fp + 16) + 8) 0 16
  let t'1 ← AP_Param.find_var_info this (fp + 0) (fp + 8) (fp + 16) (fp + 40)
  let mut info' : UInt64 := t'1
  if (info' == (0 : UInt64)) then
    return false
  AP_Param.Param_header.Param_header (fp + 48)
  let t'2 ← PMem.ldU64 (fp + 8)
  if (t'2 != (0 : UInt64)) then
    let t'3 ← PMem.ldU64 (fp + 8)
    let t'4 ← PMem.ldU8 (t'3 + 27)
    let t'5 := UInt8.toUInt32 (t'4)
    PMem.stBits (fp + 48) 8 5 (UInt32.toUInt64 (t'5))
  else
    let t'6 ← PMem.ldU8 (info' + 28)
    let t'7 := UInt8.toUInt32 (t'6)
    PMem.stBits (fp + 48) 8 5 (UInt32.toUInt64 (t'7))
  let t'8 ← PMem.ldU16 (info' + 26)
  AP_Param.set_key (fp + 48) t'8
  let t'9 ← PMem.ldU32 (fp + 0)
  PMem.stBits (fp + 48) 14 18 (UInt32.toUInt64 (t'9))
  let t'10 ← AP_Param.scan (fp + 48) (fp + 56)
  let mut sc'14 := t'10
  if sc'14 then
    let t'11 ← PMem.ldBits (fp + 48) 8 5
    let mut sc'13 := ((UInt32.toInt32 ((UInt64.toUInt32 (t'11)))) == (UInt32.toInt32 ((5 : UInt32))))
    if !sc'13 then
      let t'12 ← PMem.ldU8 (fp + 40)
      sc'13 := ((UInt32.toInt32 (UInt8.toUInt32 (t'12))) == (0 : Int32))
    sc'14 := sc'13
  return sc'14

def AP_Param.configured_in_storage (this : UInt64) : PMem.M Bool := do
  let fp ← PMem.enter 58
  let r ← AP_Param.configured_in_storage.body fp this
  PMem.leave fp
  return r

/-- C++ `AP_Param::configured : bool () const`, `AP_Param.cpp:1456-1460`. -/
def AP_Param.configured.body (fp : UInt64) (this : UInt64) : PMem.M Bool := do
  let t'1 ← AP_Param.configured_in_defaults_file this (fp + 0)
  let mut sc'3 := t'1
  if !sc'3 then
    let t'2 ← AP_Param.configured_in_storage this
    sc'3 := t'2
  return sc'3

def AP_Param.configured (this : UInt64) : PMem.M Bool := do
  let fp ← PMem.enter 1
  let r ← AP_Param.configured.body fp this
  PMem.leave fp
  return r

/-- C++ `AP_ParamTBase<short, 2>::set_default : void (const short &)`, `AP_ParamT.cpp:45-52`. -/
def AP_ParamTBase'short_2.set_default (this : UInt64) (v : UInt64) : PMem.M Unit := do
  let t'1 ← default_as_float'short v
  AP_Param.add_default this t'1
  let t'2 ← AP_Param.configured this
  if !t'2 then
    AP_ParamTBase'short_2.set this v
  return ()

/-- `AP_Enum16'SRV_Channel_Function.AP_Enum16` as a pure function of its arguments (it reads and writes no memory). -/
def AP_Enum16'SRV_Channel_Function.AP_Enum16.pure' (this : UInt64) : Id Unit := do
  _root_.Vehicle_lib.AP_Param.AP_Param'2.pure' this
  return ()

/-- C++ `AP_Enum16<SRV_Channel::Function>::AP_Enum16 : void () noexcept(false)`, `AP_Param.h:?-?`. -/
def AP_Enum16'SRV_Channel_Function.AP_Enum16 (this : UInt64) : PMem.M Unit :=
  pure (_root_.Vehicle_lib.AP_Enum16'SRV_Channel_Function.AP_Enum16.pure' this)

/-- `AP_ParamT'unsigned_int_3.operator_const_unsigned_int__` as a pure function of its arguments (it reads and writes no memory). -/
def AP_ParamT'unsigned_int_3.operator_const_unsigned_int__.pure' (this : UInt64) : Id UInt64 := do
  return this

/-- C++ `AP_ParamT<unsigned int, 3>::operator const unsigned int & : const unsigned int &() const`, `AP_Param.h:978-980`. -/
def AP_ParamT'unsigned_int_3.operator_const_unsigned_int__ (this : UInt64) : PMem.M UInt64 :=
  pure (_root_.Vehicle_lib.AP_ParamT'unsigned_int_3.operator_const_unsigned_int__.pure' this)

/-- `AP_ParamT'short_2.operator_const_short__` as a pure function of its arguments (it reads and writes no memory). -/
def AP_ParamT'short_2.operator_const_short__.pure' (this : UInt64) : Id UInt64 := do
  return this

/-- C++ `AP_ParamT<short, 2>::operator const short & : const short &() const`, `AP_Param.h:978-980`. -/
def AP_ParamT'short_2.operator_const_short__ (this : UInt64) : PMem.M UInt64 :=
  pure (_root_.Vehicle_lib.AP_ParamT'short_2.operator_const_short__.pure' this)

/-- `AP_ParamT'float_4.operator_const_float__'1` as a pure function of its arguments (it reads and writes no memory). -/
def AP_ParamT'float_4.operator_const_float__'1.pure' (this : UInt64) : Id UInt64 := do
  return this

/-- C++ `AP_ParamT<float, 4>::operator const float & : const float &() const`, `AP_Param.h:1006-1008`. -/
def AP_ParamT'float_4.operator_const_float__'1 (this : UInt64) : PMem.M UInt64 :=
  pure (_root_.Vehicle_lib.AP_ParamT'float_4.operator_const_float__'1.pure' this)

/-- C++ `AP_ParamT<float, 4>::operator- : float () const`, `AP_Param.h:1022-?`. -/
def AP_ParamT'float_4.operator_'3 (this : UInt64) : PMem.M Binary32 := do
  let t'1 ← PMem.ldF32 this
  return -t'1

/-- `AP_ParamT'signed_char_1.operator_const_signed_char__` as a pure function of its arguments (it reads and writes no memory). -/
def AP_ParamT'signed_char_1.operator_const_signed_char__.pure' (this : UInt64) : Id UInt64 := do
  return this

/-- C++ `AP_ParamT<signed char, 1>::operator const signed char & : const signed char &() const`, `AP_Param.h:978-980`. -/
def AP_ParamT'signed_char_1.operator_const_signed_char__ (this : UInt64) : PMem.M UInt64 :=
  pure (_root_.Vehicle_lib.AP_ParamT'signed_char_1.operator_const_signed_char__.pure' this)

/-- `AP_ParamTBase'float_4.get` as a pure function of its arguments (it reads and writes no memory). -/
def AP_ParamTBase'float_4.get.pure' (this : UInt64) : Id UInt64 := do
  return this

/-- C++ `AP_ParamTBase<float, 4>::get : const float &() const`, `AP_Param.h:917-919`. -/
def AP_ParamTBase'float_4.get (this : UInt64) : PMem.M UInt64 :=
  pure (_root_.Vehicle_lib.AP_ParamTBase'float_4.get.pure' this)

/-- C++ `AP_Enum<Parameters::WPYawBehavior>::operator const Parameters::WPYawBehavior : const Parameters::WPYawBehavior () const`, `AP_Param.h:1140-1142`. -/
def AP_Enum'Parameters_WPYawBehavior.operator_const_Parameters.WPYawBehavior (this : UInt64) : PMem.M Int32 := do
  let t'1 ← PMem.ldI8 this
  return Int8.toInt32 (t'1)

/-- `AP_ParamTBase'unsigned_int_3.get` as a pure function of its arguments (it reads and writes no memory). -/
def AP_ParamTBase'unsigned_int_3.get.pure' (this : UInt64) : Id UInt64 := do
  return this

/-- C++ `AP_ParamTBase<unsigned int, 3>::get : const unsigned int &() const`, `AP_Param.h:917-919`. -/
def AP_ParamTBase'unsigned_int_3.get (this : UInt64) : PMem.M UInt64 :=
  pure (_root_.Vehicle_lib.AP_ParamTBase'unsigned_int_3.get.pure' this)

/-- C++ `AP_Param::is_read_only : bool () const`, `AP_Param.cpp:1462-1472`. -/
def AP_Param.is_read_only.body (fp : UInt64) (this : UInt64) : PMem.M Bool := do
  let t'1 ← PMem.ldU16 (0x131e0 : UInt64) /- &AP_Param::num_read_only -/
  if ((UInt32.toInt32 (UInt16.toUInt32 (t'1))) == (0 : Int32)) then
    return false
  let t'2 ← AP_Param.configured_in_defaults_file this (fp + 0)
  if t'2 then
    let t'3 ← PMem.ldB (fp + 0)
    return t'3
  return false

def AP_Param.is_read_only (this : UInt64) : PMem.M Bool := do
  let fp ← PMem.enter 1
  let r ← AP_Param.is_read_only.body fp this
  PMem.leave fp
  return r

/-- `AP_ParamTBase'unsigned_short_2.get` as a pure function of its arguments (it reads and writes no memory). -/
def AP_ParamTBase'unsigned_short_2.get.pure' (this : UInt64) : Id UInt64 := do
  return this

/-- C++ `AP_ParamTBase<unsigned short, 2>::get : const unsigned short &() const`, `AP_Param.h:917-919`. -/
def AP_ParamTBase'unsigned_short_2.get (this : UInt64) : PMem.M UInt64 :=
  pure (_root_.Vehicle_lib.AP_ParamTBase'unsigned_short_2.get.pure' this)

/-- C++ `AP_Enum<AP_Arming::Required>::operator const AP_Arming::Required : const AP_Arming::Required () const`, `AP_Param.h:1140-1142`. -/
def AP_Enum'AP_Arming_Required.operator_const_AP_Arming.Required (this : UInt64) : PMem.M Int32 := do
  let t'1 ← PMem.ldI8 this
  return Int8.toInt32 (t'1)

/-- `AP_ParamT'unsigned_char_1.operator_const_unsigned_char__` as a pure function of its arguments (it reads and writes no memory). -/
def AP_ParamT'unsigned_char_1.operator_const_unsigned_char__.pure' (this : UInt64) : Id UInt64 := do
  return this

/-- C++ `AP_ParamT<unsigned char, 1>::operator const unsigned char & : const unsigned char &() const`, `AP_Param.h:978-980`. -/
def AP_ParamT'unsigned_char_1.operator_const_unsigned_char__ (this : UInt64) : PMem.M UInt64 :=
  pure (_root_.Vehicle_lib.AP_ParamT'unsigned_char_1.operator_const_unsigned_char__.pure' this)

/-- `AP_ParamTBase'short_2.get` as a pure function of its arguments (it reads and writes no memory). -/
def AP_ParamTBase'short_2.get.pure' (this : UInt64) : Id UInt64 := do
  return this

/-- C++ `AP_ParamTBase<short, 2>::get : const short &() const`, `AP_Param.h:917-919`. -/
def AP_ParamTBase'short_2.get (this : UInt64) : PMem.M UInt64 :=
  pure (_root_.Vehicle_lib.AP_ParamTBase'short_2.get.pure' this)

/-- C++ `AP_ParamT<float, 4>::operator>= : bool (const AP_ParamT<float, AP_PARAM_FLOAT> &) const`, `AP_Param.h:?-?`. -/
def AP_ParamT'float_4.operator__ (this : UInt64) (other : UInt64) : PMem.M Bool := do
  let t'1 ← PMem.ldF32 this
  let t'2 ← PMem.ldF32 other
  return (decide (t'1 ≥ t'2))

/-- C++ `AP_Enum16<SRV_Channel::Function>::operator const SRV_Channel::Function : const SRV_Channel::Function () const`, `AP_Param.h:1155-1157`. -/
def AP_Enum16'SRV_Channel_Function.operator_const_SRV_Channel.Function (this : UInt64) : PMem.M Int32 := do
  let t'1 ← PMem.ldI16 this
  return Int16.toInt32 (t'1)

/-- C++ `AP_ParamT<float, 4>::operator- : float (const AP_ParamT<float, AP_PARAM_FLOAT> &) const`, `AP_Param.h:?-?`. -/
def AP_ParamT'float_4.operator_'2 (this : UInt64) (other : UInt64) : PMem.M Binary32 := do
  let t'1 ← PMem.ldF32 this
  let t'2 ← PMem.ldF32 other
  return (t'1 - t'2)

/-- C++ `AP_Enum<AP_Arming::RequireLocation>::operator const AP_Arming::RequireLocation : const AP_Arming::RequireLocation () const`, `AP_Param.h:1140-1142`. -/
def AP_Enum'AP_Arming_RequireLocation.operator_const_AP_Arming.RequireLocation (this : UInt64) : PMem.M UInt8 := do
  let t'1 ← PMem.ldI8 this
  return Int8.toUInt8 (t'1)

/-- `AP_ParamT'int_3.operator_const_int__` as a pure function of its arguments (it reads and writes no memory). -/
def AP_ParamT'int_3.operator_const_int__.pure' (this : UInt64) : Id UInt64 := do
  return this

/-- C++ `AP_ParamT<int, 3>::operator const int & : const int &() const`, `AP_Param.h:978-980`. -/
def AP_ParamT'int_3.operator_const_int__ (this : UInt64) : PMem.M UInt64 :=
  pure (_root_.Vehicle_lib.AP_ParamT'int_3.operator_const_int__.pure' this)

/-- C++ `AP_Enum<Parameters::FS_GCS_Action>::operator const Parameters::FS_GCS_Action : const Parameters::FS_GCS_Action () const`, `AP_Param.h:1140-1142`. -/
def AP_Enum'Parameters_FS_GCS_Action.operator_const_Parameters.FS_GCS_Action (this : UInt64) : PMem.M Int32 := do
  let t'1 ← PMem.ldI8 this
  return Int8.toInt32 (t'1)

/-- C++ `AP_Enum<ModeRTL::RTLAltType>::operator const ModeRTL::RTLAltType : const ModeRTL::RTLAltType () const`, `AP_Param.h:1140-1142`. -/
def AP_Enum'ModeRTL_RTLAltType.operator_const_ModeRTL.RTLAltType (this : UInt64) : PMem.M Int8 := do
  let t'1 ← PMem.ldI8 this
  return t'1

/-- C++ `AP_Enum<Parameters::FS_THR_Action>::operator const Parameters::FS_THR_Action : const Parameters::FS_THR_Action () const`, `AP_Param.h:1140-1142`. -/
def AP_Enum'Parameters_FS_THR_Action.operator_const_Parameters.FS_THR_Action (this : UInt64) : PMem.M Int32 := do
  let t'1 ← PMem.ldI8 this
  return Int8.toInt32 (t'1)

/-- C++ `AP_ParamT<float, 4>::operator> : bool (const AP_ParamT<float, AP_PARAM_FLOAT> &) const`, `AP_Param.h:?-?`. -/
def AP_ParamT'float_4.operator_ (this : UInt64) (other : UInt64) : PMem.M Bool := do
  let t'1 ← PMem.ldF32 this
  let t'2 ← PMem.ldF32 other
  return (decide (t'1 > t'2))

/-- C++ `AP_Param::get_eeprom_full : bool ()`, `AP_Param.h:445-447`. -/
def AP_Param.get_eeprom_full  : PMem.M Bool := do
  let t'1 ← PMem.ldB (0xbba0 : UInt64) /- &AP_Param::eeprom_full -/
  return t'1

/-- C++ `AP_Enum<Parameters::FS_EKF_Action>::operator const Parameters::FS_EKF_Action : const Parameters::FS_EKF_Action () const`, `AP_Param.h:1140-1142`. -/
def AP_Enum'Parameters_FS_EKF_Action.operator_const_Parameters.FS_EKF_Action (this : UInt64) : PMem.M Int32 := do
  let t'1 ← PMem.ldI8 this
  return Int8.toInt32 (t'1)

/-- `AP_Param.ParamToken.ParamToken` as a pure function of its arguments (it reads and writes no memory). -/
def AP_Param.ParamToken.ParamToken.pure' (this : UInt64) : Id Unit := do
  return ()

/-- C++ `AP_Param::ParamToken::ParamToken : void () noexcept`, `AP_Param.h:?-?`. -/
def AP_Param.ParamToken.ParamToken (this : UInt64) : PMem.M Unit :=
  pure (_root_.Vehicle_lib.AP_Param.ParamToken.ParamToken.pure' this)

/-- `AP_Param_value_storage.AP_Param_value_storage` as a pure function of its arguments (it reads and writes no memory). -/
def AP_Param_value_storage.AP_Param_value_storage.pure' (this : UInt64) : Id Unit := do
  return ()

/-- C++ `AP_Param_value_storage::AP_Param_value_storage : void ()`, `AP_Param.cpp:732-?`. -/
def AP_Param_value_storage.AP_Param_value_storage (this : UInt64) : PMem.M Unit :=
  pure (_root_.Vehicle_lib.AP_Param_value_storage.AP_Param_value_storage.pure' this)

/-- C++ `AP_ParamTBase<unsigned int, 3>::set : void (const unsigned int &)`, `AP_Param.h:923-925`. -/
def AP_ParamTBase'unsigned_int_3.set (this : UInt64) (v : UInt64) : PMem.M Unit := do
  let t'1 ← PMem.ldU32 v
  PMem.stU32 this t'1
  return ()

/-- C++ `AP_ParamTBase<unsigned short, 2>::set : void (const unsigned short &)`, `AP_Param.h:923-925`. -/
def AP_ParamTBase'unsigned_short_2.set (this : UInt64) (v : UInt64) : PMem.M Unit := do
  let t'1 ← PMem.ldU16 v
  PMem.stU16 this t'1
  return ()

/-- C++ `AP_Enum<AP_BattMonitor_Params::Type>::operator const AP_BattMonitor_Params::Type : const AP_BattMonitor_Params::Type () const`, `AP_Param.h:1140-1142`. -/
def AP_Enum'AP_BattMonitor_Params_Type.operator_const_AP_BattMonitor_Params.Type (this : UInt64) : PMem.M Int32 := do
  let t'1 ← PMem.ldI8 this
  return Int8.toInt32 (t'1)

/-- C++ `AP_Param::convert_g2_objects : void (const void *, const G2ObjectConversion *, uint8_t)`, `AP_Param.cpp:2179-2190`. NOT TRANSLATED (the back end rejects: conversion of T(rec,0,False,AP_Param::G2ObjectConversion)): a stub. -/
def AP_Param.convert_g2_objects (g2 : UInt64) (g2_conversions : UInt64) (num_conversions : UInt8) : PMem.M Unit := do
  PMem.unreached "rejected AP_Param::convert_g2_objects"
  return ()

/-- C++ `AP_Param::convert_toplevel_objects : void (const TopLevelObjectConversion *, uint8_t)`, `AP_Param.cpp:2192-2198`. NOT TRANSLATED (the back end rejects: conversion of T(rec,0,False,AP_Param::TopLevelObjectConversion)): a stub. -/
def AP_Param.convert_toplevel_objects (conversions : UInt64) (num_conversions : UInt8) : PMem.M Unit := do
  PMem.unreached "rejected AP_Param::convert_toplevel_objects"
  return ()

/-- C++ `AP_Param::find_old_parameter : bool (const struct ConversionInfo *, AP_Param *)`, `AP_Param.cpp:1995-2011`. -/
def AP_Param.find_old_parameter.body (fp : UInt64) (info' : UInt64) (value : UInt64) : PMem.M Bool := do
  let mut info' := info'
  let mut value := value
  AP_Param.Param_header.Param_header (fp + 8)
  let t'1 ← PMem.ldU32 (info' + 8)
  PMem.stBits (fp + 8) 8 5 (UInt32.toUInt64 (t'1))
  let t'2 ← PMem.ldU16 info'
  AP_Param.set_key (fp + 8) t'2
  let t'3 ← PMem.ldU32 (info' + 4)
  PMem.stBits (fp + 8) 14 18 (UInt32.toUInt64 (t'3))
  let t'4 ← AP_Param.scan (fp + 8) (fp + 0)
  if !t'4 then
    return false
  let t'5 ← PMem.ldU16 (fp + 0)
  let t'6 ← PMem.ldBits (fp + 8) 8 5
  let t'7 ← AP_Param.type_size (UInt64.toUInt32 (t'6))
  let t'8 ← StorageAccess.read_block (0xbb70 : UInt64) /- &AP_Param::_storage -/ value (UInt64.toUInt16 (((UInt16.toUInt64 (t'5)) + (4 : UInt64)))) (UInt8.toUInt64 (t'7))
  discard <| pure (t'8)
  return true

def AP_Param.find_old_parameter (info' : UInt64) (value : UInt64) : PMem.M Bool := do
  let fp ← PMem.enter 12
  let r ← AP_Param.find_old_parameter.body fp info' value
  PMem.leave fp
  return r

/-- C++ `default_as_float : float (const int &)`, `AP_ParamT.cpp:?-?`. -/
def default_as_float'int (v : UInt64) : PMem.M Binary32 := do
  let t'1 ← PMem.ldI32 v
  return Int32.toBinary32 (t'1)

/-- C++ `AP_ParamTBase<int, 3>::set_and_default : void (const int &)`, `AP_ParamT.cpp:56-61`. -/
def AP_ParamTBase'int_3.set_and_default (this : UInt64) (v : UInt64) : PMem.M Unit := do
  let t'1 ← default_as_float'int v
  AP_Param.add_default this t'1
  AP_ParamTBase'int_3.set this v
  return ()

/-- C++ `AP_ParamTBase<int, 3>::set_default : void (const int &)`, `AP_ParamT.cpp:45-52`. -/
def AP_ParamTBase'int_3.set_default (this : UInt64) (v : UInt64) : PMem.M Unit := do
  let t'1 ← default_as_float'int v
  AP_Param.add_default this t'1
  let t'2 ← AP_Param.configured this
  if !t'2 then
    AP_ParamTBase'int_3.set this v
  return ()

/-- `AP_Enum'AP_Motors_PWMType.AP_Enum` as a pure function of its arguments (it reads and writes no memory). -/
def AP_Enum'AP_Motors_PWMType.AP_Enum.pure' (this : UInt64) : Id Unit := do
  _root_.Vehicle_lib.AP_Param.AP_Param'2.pure' this
  return ()

/-- C++ `AP_Enum<AP_Motors::PWMType>::AP_Enum : void () noexcept(false)`, `AP_Param.h:?-?`. -/
def AP_Enum'AP_Motors_PWMType.AP_Enum (this : UInt64) : PMem.M Unit :=
  pure (_root_.Vehicle_lib.AP_Enum'AP_Motors_PWMType.AP_Enum.pure' this)

/-- C++ `AP_Enum<AP_Motors::PWMType>::operator const AP_Motors::PWMType : const AP_Motors::PWMType () const`, `AP_Param.h:1140-1142`. -/
def AP_Enum'AP_Motors_PWMType.operator_const_AP_Motors.PWMType (this : UInt64) : PMem.M UInt8 := do
  let t'1 ← PMem.ldI8 this
  return Int8.toUInt8 (t'1)

/-- C++ `AP_ParamTBase<short, 2>::set_and_default : void (const short &)`, `AP_ParamT.cpp:56-61`. -/
def AP_ParamTBase'short_2.set_and_default (this : UInt64) (v : UInt64) : PMem.M Unit := do
  let t'1 ← default_as_float'short v
  AP_Param.add_default this t'1
  AP_ParamTBase'short_2.set this v
  return ()

/-- C++ `default_as_float : float (const uint32_t &)`, `AP_ParamT.cpp:28-?`. -/
def default_as_float (v : UInt64) : PMem.M Binary32 := do
  let t'1 ← PMem.ldU32 v
  return Int32.toBinary32 ((UInt32.toInt32 (t'1)))

/-- C++ `AP_ParamTBase<unsigned int, 3>::set_default : void (const unsigned int &)`, `AP_ParamT.cpp:45-52`. -/
def AP_ParamTBase'unsigned_int_3.set_default (this : UInt64) (v : UInt64) : PMem.M Unit := do
  let t'1 ← default_as_float v
  AP_Param.add_default this t'1
  let t'2 ← AP_Param.configured this
  if !t'2 then
    AP_ParamTBase'unsigned_int_3.set this v
  return ()

/-- C++ `AP_Param::find_top_level_key_by_pointer : bool (const void *, uint16_t &)`, `AP_Param.cpp:1097-1110`. -/
def AP_Param.find_top_level_key_by_pointer (ptr' : UInt64) (key : UInt64) : PMem.M Bool := do
  let mut ptr' := ptr'
  let mut i : UInt16 := Int16.toUInt16 (Int32.toInt16 ((0 : Int32)))
  let mut first'1 := true
  for _ in PMem.loopFuel do
    if !first'1 then
      let t'2 := i
      let t'3 := (t'2 + 1)
      i := t'3
      pure ()
    first'1 := false
    let t'4 ← PMem.ldU16 (0xba78 : UInt64) /- &AP_Param::_num_vars -/
    if !((decide ((UInt32.toInt32 (UInt16.toUInt32 (i))) < (UInt32.toInt32 (UInt16.toUInt32 (t'4)))))) then break
    let t'5 ← AP_Param.var_info i
    let info' : UInt64 := t'5
    let t'6 ← PMem.ldU8 (info' + 28)
    if ((UInt32.toInt32 (UInt8.toUInt32 (t'6))) != (UInt32.toInt32 ((6 : UInt32)))) then
      continue
    let t'7 ← PMem.ldU64 (info' + 8)
    if (ptr' == t'7) then
      let t'8 ← PMem.ldU16 (info' + 26)
      PMem.stU16 key t'8
      return true
  return false

/-- C++ `AP_Param::get_param_by_index : bool (void *, uint32_t, ap_var_type, void *)`, `AP_Param.cpp:1117-1125`. -/
def AP_Param.get_param_by_index.body (fp : UInt64) (obj_ptr : UInt64) (idx : UInt32) (old_ptype : UInt32) (pvalue : UInt64) : PMem.M Bool := do
  let mut obj_ptr := obj_ptr
  let mut idx := idx
  let mut old_ptype := old_ptype
  let mut pvalue := pvalue
  let t'1 ← AP_Param.find_top_level_key_by_pointer obj_ptr (fp + 0)
  if !t'1 then
    return false
  let t'2 ← PMem.ldU16 (fp + 0)
  PMem.stU16 ((fp + 8) + 0) t'2
  PMem.stU32 ((fp + 8) + 4) idx
  PMem.stU32 ((fp + 8) + 8) old_ptype
  PMem.stU64 ((fp + 8) + 16) (0 : UInt64)
  let t'3 ← AP_Param.find_old_parameter (fp + 8) pvalue
  return t'3

def AP_Param.get_param_by_index (obj_ptr : UInt64) (idx : UInt32) (old_ptype : UInt32) (pvalue : UInt64) : PMem.M Bool := do
  let fp ← PMem.enter 32
  let r ← AP_Param.get_param_by_index.body fp obj_ptr idx old_ptype pvalue
  PMem.leave fp
  return r

/-- `AP_ParamTBase'int_3.get` as a pure function of its arguments (it reads and writes no memory). -/
def AP_ParamTBase'int_3.get.pure' (this : UInt64) : Id UInt64 := do
  return this

/-- C++ `AP_ParamTBase<int, 3>::get : const int &() const`, `AP_Param.h:917-919`. -/
def AP_ParamTBase'int_3.get (this : UInt64) : PMem.M UInt64 :=
  pure (_root_.Vehicle_lib.AP_ParamTBase'int_3.get.pure' this)

/-- C++ `AP_ParamT<float, 4>::operator double : double () const`, `AP_Param.h:1014-1016`. -/
def AP_ParamT'float_4.operator_double (this : UInt64) : PMem.M Binary64 := do
  let t'1 ← PMem.ldF32 this
  return Binary32.toBinary64 (t'1)

/-- `AP_Param.ConversionInfo.ConversionInfo` as a pure function of its arguments (it reads and writes no memory). -/
def AP_Param.ConversionInfo.ConversionInfo.pure' (this : UInt64) : Id Unit := do
  return ()

/-- C++ `AP_Param::ConversionInfo::ConversionInfo : void () noexcept`, `AP_Param.h:234-?`. -/
def AP_Param.ConversionInfo.ConversionInfo (this : UInt64) : PMem.M Unit :=
  pure (_root_.Vehicle_lib.AP_Param.ConversionInfo.ConversionInfo.pure' this)

/-- `AP_Enum'ModeRTL_RTLAltType.AP_Enum` as a pure function of its arguments (it reads and writes no memory). -/
def AP_Enum'ModeRTL_RTLAltType.AP_Enum.pure' (this : UInt64) : Id Unit := do
  _root_.Vehicle_lib.AP_Param.AP_Param'2.pure' this
  return ()

/-- C++ `AP_Enum<ModeRTL::RTLAltType>::AP_Enum : void () noexcept(false)`, `AP_Param.h:1137-?`. -/
def AP_Enum'ModeRTL_RTLAltType.AP_Enum (this : UInt64) : PMem.M Unit :=
  pure (_root_.Vehicle_lib.AP_Enum'ModeRTL_RTLAltType.AP_Enum.pure' this)

/-- `AP_Enum'Parameters_FS_GCS_Action.AP_Enum` as a pure function of its arguments (it reads and writes no memory). -/
def AP_Enum'Parameters_FS_GCS_Action.AP_Enum.pure' (this : UInt64) : Id Unit := do
  _root_.Vehicle_lib.AP_Param.AP_Param'2.pure' this
  return ()

/-- C++ `AP_Enum<Parameters::FS_GCS_Action>::AP_Enum : void () noexcept(false)`, `AP_Param.h:1137-?`. -/
def AP_Enum'Parameters_FS_GCS_Action.AP_Enum (this : UInt64) : PMem.M Unit :=
  pure (_root_.Vehicle_lib.AP_Enum'Parameters_FS_GCS_Action.AP_Enum.pure' this)

/-- `AP_Enum'Parameters_WPYawBehavior.AP_Enum` as a pure function of its arguments (it reads and writes no memory). -/
def AP_Enum'Parameters_WPYawBehavior.AP_Enum.pure' (this : UInt64) : Id Unit := do
  _root_.Vehicle_lib.AP_Param.AP_Param'2.pure' this
  return ()

/-- C++ `AP_Enum<Parameters::WPYawBehavior>::AP_Enum : void () noexcept(false)`, `AP_Param.h:1137-?`. -/
def AP_Enum'Parameters_WPYawBehavior.AP_Enum (this : UInt64) : PMem.M Unit :=
  pure (_root_.Vehicle_lib.AP_Enum'Parameters_WPYawBehavior.AP_Enum.pure' this)

/-- `AP_Enum'Parameters_FS_THR_Action.AP_Enum` as a pure function of its arguments (it reads and writes no memory). -/
def AP_Enum'Parameters_FS_THR_Action.AP_Enum.pure' (this : UInt64) : Id Unit := do
  _root_.Vehicle_lib.AP_Param.AP_Param'2.pure' this
  return ()

/-- C++ `AP_Enum<Parameters::FS_THR_Action>::AP_Enum : void () noexcept(false)`, `AP_Param.h:1137-?`. -/
def AP_Enum'Parameters_FS_THR_Action.AP_Enum (this : UInt64) : PMem.M Unit :=
  pure (_root_.Vehicle_lib.AP_Enum'Parameters_FS_THR_Action.AP_Enum.pure' this)

/-- `AP_Enum'Parameters_FS_EKF_Action.AP_Enum` as a pure function of its arguments (it reads and writes no memory). -/
def AP_Enum'Parameters_FS_EKF_Action.AP_Enum.pure' (this : UInt64) : Id Unit := do
  _root_.Vehicle_lib.AP_Param.AP_Param'2.pure' this
  return ()

/-- C++ `AP_Enum<Parameters::FS_EKF_Action>::AP_Enum : void () noexcept(false)`, `AP_Param.h:1137-?`. -/
def AP_Enum'Parameters_FS_EKF_Action.AP_Enum (this : UInt64) : PMem.M Unit :=
  pure (_root_.Vehicle_lib.AP_Enum'Parameters_FS_EKF_Action.AP_Enum.pure' this)

/-- `AP_Enum'AP_Arming_Required.AP_Enum` as a pure function of its arguments (it reads and writes no memory). -/
def AP_Enum'AP_Arming_Required.AP_Enum.pure' (this : UInt64) : Id Unit := do
  _root_.Vehicle_lib.AP_Param.AP_Param'2.pure' this
  return ()

/-- C++ `AP_Enum<AP_Arming::Required>::AP_Enum : void () noexcept(false)`, `AP_Param.h:?-?`. -/
def AP_Enum'AP_Arming_Required.AP_Enum (this : UInt64) : PMem.M Unit :=
  pure (_root_.Vehicle_lib.AP_Enum'AP_Arming_Required.AP_Enum.pure' this)

/-- `AP_Enum'AP_Arming_RequireLocation.AP_Enum` as a pure function of its arguments (it reads and writes no memory). -/
def AP_Enum'AP_Arming_RequireLocation.AP_Enum.pure' (this : UInt64) : Id Unit := do
  _root_.Vehicle_lib.AP_Param.AP_Param'2.pure' this
  return ()

/-- C++ `AP_Enum<AP_Arming::RequireLocation>::AP_Enum : void () noexcept(false)`, `AP_Param.h:?-?`. -/
def AP_Enum'AP_Arming_RequireLocation.AP_Enum (this : UInt64) : PMem.M Unit :=
  pure (_root_.Vehicle_lib.AP_Enum'AP_Arming_RequireLocation.AP_Enum.pure' this)

/-- C++ `default_as_float : float (const signed char &)`, `AP_ParamT.cpp:?-?`. -/
def default_as_float'signed_char (v : UInt64) : PMem.M Binary32 := do
  let t'1 ← PMem.ldI8 v
  return Int8.toBinary32 (t'1)

/-- C++ `AP_ParamTBase<signed char, 1>::set_default : void (const signed char &)`, `AP_ParamT.cpp:45-52`. -/
def AP_ParamTBase'signed_char_1.set_default (this : UInt64) (v : UInt64) : PMem.M Unit := do
  let t'1 ← default_as_float'signed_char v
  AP_Param.add_default this t'1
  let t'2 ← AP_Param.configured this
  if !t'2 then
    AP_ParamTBase'signed_char_1.set this v
  return ()

/-- `AP_Enum16'GCS_Option.AP_Enum16` as a pure function of its arguments (it reads and writes no memory). -/
def AP_Enum16'GCS_Option.AP_Enum16.pure' (this : UInt64) : Id Unit := do
  _root_.Vehicle_lib.AP_Param.AP_Param'2.pure' this
  return ()

/-- C++ `AP_Enum16<GCS::Option>::AP_Enum16 : void () noexcept(false)`, `AP_Param.h:?-?`. -/
def AP_Enum16'GCS_Option.AP_Enum16 (this : UInt64) : PMem.M Unit :=
  pure (_root_.Vehicle_lib.AP_Enum16'GCS_Option.AP_Enum16.pure' this)

/-- `AP_Enum'AP_BattMonitor_Params_Type.AP_Enum` as a pure function of its arguments (it reads and writes no memory). -/
def AP_Enum'AP_BattMonitor_Params_Type.AP_Enum.pure' (this : UInt64) : Id Unit := do
  _root_.Vehicle_lib.AP_Param.AP_Param'2.pure' this
  return ()

/-- C++ `AP_Enum<AP_BattMonitor_Params::Type>::AP_Enum : void () noexcept(false)`, `AP_Param.h:?-?`. -/
def AP_Enum'AP_BattMonitor_Params_Type.AP_Enum (this : UInt64) : PMem.M Unit :=
  pure (_root_.Vehicle_lib.AP_Enum'AP_BattMonitor_Params_Type.AP_Enum.pure' this)

end Vehicle_lib
