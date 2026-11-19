import ArduLean.Runtime.Hal
import ArduLean.Vehicle.libraries.AP_Math.AP_Math
import ArduLean.Vehicle.libraries.StorageManager.StorageManager
import ArduLean.Vehicle.libraries.AP_Param.AP_Param
import ArduLean.Vehicle.libraries.AP_Common.AP_Common
import ArduLean.Vehicle.libraries.GCS_MAVLink.GCS_MAVLink

/-!
ArduPilot `libraries/AP_Param`, part 2 of 3. Sources: `libraries/AP_Param/AP_Param.cpp`, `libraries/AP_Param/AP_ParamT.cpp`, `libraries/AP_Param/AP_Param.h`.

Items of `lean/Vehicle_lib.lean` (the vehicle translation), unchanged; placed by `tools/split_modules.py` (`ArduLean/Vehicle/INDEX.md`).
-/

open FloatLib.Floats (Binary32 Binary64)

set_option linter.unusedVariables false
set_option linter.unreachableTactic false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false

namespace Vehicle_lib

/-- C++ `AP_Param::save : void (bool)`, `AP_Param.cpp:1269-1298`. -/
def AP_Param.save.body (fp : UInt64) (this : UInt64) (force_save : Bool) : PMem.M Unit := do
  let mut force_save := force_save
  AP_Param.param_save.param_save (fp + 0)
  AP_Param.param_save.param_save (fp + 16)
  PMem.stU64 (fp + 0) this
  PMem.stB ((fp + 0) + 8) force_save
  let t'1 ← ObjectBuffer_TS'AP_Param_param_save.peek (0xbf38 : UInt64) /- &AP_Param::save_queue -/ (fp + 16)
  let mut sc'3 := t'1
  if sc'3 then
    let t'2 ← PMem.ldU64 (fp + 16)
    sc'3 := (t'2 == this)
  let mut sc'5 := sc'3
  if sc'5 then
    let t'4 ← PMem.ldB ((fp + 16) + 8)
    sc'5 := ((if t'4 then (1 : Int32) else (0 : Int32)) == (if force_save then (1 : Int32) else (0 : Int32)))
  if sc'5 then
    return ()
  for _ in PMem.loopFuel do
    let t'6 ← ObjectBuffer_TS'AP_Param_param_save.push (0xbf38 : UInt64) /- &AP_Param::save_queue -/ (fp + 0)
    if !(!t'6) then break
    let mut sc'9 := (← get).armed
    if sc'9 then
      let t'7 ← PMem.ldU64 ((0xba88 : UInt64) /- &hal -/ + 80)
      let t'8 ← PMem.halDev "AP_HAL::Scheduler::in_main_thread" t'7 #[]
      sc'9 := (t'8 != 0)
    if sc'9 then
      return ()
    let t'10 ← PMem.ldU64 ((0xba88 : UInt64) /- &hal -/ + 80)
    discard <| PMem.halDev "AP_HAL::Scheduler::expect_delay_ms" t'10 #[(UInt32.toUInt64 ((Int32.toUInt32 ((1 : Int32)))))]
    let t'11 ← PMem.ldU64 ((0xba88 : UInt64) /- &hal -/ + 80)
    discard <| PMem.hal "AP_HAL::Scheduler::delay_microseconds" t'11 #[(UInt16.toUInt64 ((Int16.toUInt16 (Int32.toInt16 ((500 : Int32))))))]
    let t'12 ← PMem.ldU64 ((0xba88 : UInt64) /- &hal -/ + 80)
    discard <| PMem.halDev "AP_HAL::Scheduler::expect_delay_ms" t'12 #[(UInt32.toUInt64 ((Int32.toUInt32 ((0 : Int32)))))]
  return ()

def AP_Param.save (this : UInt64) (force_save : Bool) : PMem.M Unit := do
  let fp ← PMem.enter 25
  let r ← AP_Param.save.body fp this force_save
  PMem.leave fp
  return r

/-- C++ `AP_ParamTBase<short, 2>::set_and_save : void (const short &)`, `AP_ParamT.cpp:79-83`. -/
def AP_ParamTBase'short_2.set_and_save (this : UInt64) (v : UInt64) : PMem.M Unit := do
  let t'1 ← PMem.ldI16 this
  let t'2 ← PMem.ldI16 v
  let mut force : Bool := (decide ((Binary32.abs (Int32.toBinary32 (((Int16.toInt32 (t'1)) - (Int16.toInt32 (t'2)))))) < (Binary32.ofBits 0x34000000 /- 11920929/100000000000000 -/)))
  AP_ParamTBase'short_2.set this v
  AP_Param.save this force
  return ()

/-- C++ `AP_ParamTBase<float, 4>::set_and_save : void (const float &)`, `AP_ParamT.cpp:79-83`. -/
def AP_ParamTBase'float_4.set_and_save (this : UInt64) (v : UInt64) : PMem.M Unit := do
  let t'1 ← PMem.ldF32 this
  let t'2 ← PMem.ldF32 v
  let mut force : Bool := (decide ((Binary32.abs (t'1 - t'2)) < (Binary32.ofBits 0x34000000 /- 11920929/100000000000000 -/)))
  AP_ParamTBase'float_4.set this v
  AP_Param.save this force
  return ()

/-- C++ `AP_ParamTBase<signed char, 1>::set_and_save : void (const signed char &)`, `AP_ParamT.cpp:79-83`. -/
def AP_ParamTBase'signed_char_1.set_and_save (this : UInt64) (v : UInt64) : PMem.M Unit := do
  let t'1 ← PMem.ldI8 this
  let t'2 ← PMem.ldI8 v
  let mut force : Bool := (decide ((Binary32.abs (Int32.toBinary32 (((Int8.toInt32 (t'1)) - (Int8.toInt32 (t'2)))))) < (Binary32.ofBits 0x34000000 /- 11920929/100000000000000 -/)))
  AP_ParamTBase'signed_char_1.set this v
  AP_Param.save this force
  return ()

/-- C++ `AP_ParamTBase<int, 3>::set_and_save : void (const int &)`, `AP_ParamT.cpp:79-83`. -/
def AP_ParamTBase'int_3.set_and_save (this : UInt64) (v : UInt64) : PMem.M Unit := do
  let t'1 ← PMem.ldI32 this
  let t'2 ← PMem.ldI32 v
  let mut force : Bool := (decide ((Binary32.abs (Int32.toBinary32 ((t'1 - t'2)))) < (Binary32.ofBits 0x34000000 /- 11920929/100000000000000 -/)))
  AP_ParamTBase'int_3.set this v
  AP_Param.save this force
  return ()

/-- C++ `AP_ParamTBase<float, 4>::set_and_save_ifchanged : void (const float &)`, `<built-in>:91-100`. -/
def AP_ParamTBase'float_4.set_and_save_ifchanged (this : UInt64) (v : UInt64) : PMem.M Unit := do
  let t'1 ← PMem.ldF32 v
  let t'2 ← PMem.ldF32 this
  if (t'1 == t'2) then
    return ()
  AP_ParamTBase'float_4.set this v
  AP_Param.save this true
  return ()

/-- C++ `AP_Param::allow_set_via_mavlink : bool (uint16_t) const`, `AP_Param.cpp:1476-1498`. -/
def AP_Param.allow_set_via_mavlink (this : UInt64) (flags : UInt16) : PMem.M Bool := do
  let mut flags := flags
  let t'1 ← AP_Param.is_read_only this
  if t'1 then
    return false
  if ((UInt32.toInt32 (UInt16.toUInt32 (flags))) &&& ((1 : Int32) <<< (5 : Int32))) != (0 : Int32) then
    PMem.unreached "AP_BoardConfig::allow_set_internal_parameters"
    if !(default : Bool) then
      return false
  let t'2 ← gcs
  let t'3 ← GCS.get_allow_param_set t'2
  if !t'3 then
    return false
  return true

/-- C++ `AP_ParamTBase<short, 2>::set_and_save_ifchanged : void (const short &)`, `<built-in>:91-100`. -/
def AP_ParamTBase'short_2.set_and_save_ifchanged (this : UInt64) (v : UInt64) : PMem.M Unit := do
  let t'1 ← PMem.ldI16 v
  let t'2 ← PMem.ldI16 this
  if ((Int16.toInt32 (t'1)) == (Int16.toInt32 (t'2))) then
    return ()
  AP_ParamTBase'short_2.set this v
  AP_Param.save this true
  return ()

/-- C++ `AP_Param::_convert_parameter_width : bool (ap_var_type, float, bool)`, `AP_Param.cpp:2204-2294`. -/
def AP_Param._convert_parameter_width.body (fp : UInt64) (this : UInt64) (old_ptype : UInt32) (scale_factor : Binary32) (bitmask : Bool) : PMem.M Bool := do
  let mut old_ptype := old_ptype
  let mut scale_factor := scale_factor
  let mut bitmask := bitmask
  let t'1 ← AP_Param.configured_in_storage this
  if t'1 then
    return false
  PMem.stU32 (fp + 0) (Int32.toUInt32 ((0 : Int32)))
  discard <| PMem.memset ((fp + 16) + 0) 0 1
  discard <| PMem.memset ((fp + 16) + 8) 0 16
  let t'2 ← AP_Param.find_var_info this (fp + 0) (fp + 8) (fp + 16) (fp + 40)
  let mut info' : UInt64 := t'2
  if (info' == (0 : UInt64)) then
    return false
  let mut new_ptype : UInt32 := default  -- uninitialized in C
  let t'3 ← PMem.ldU64 (fp + 8)
  if (t'3 != (0 : UInt64)) then
    let t'4 ← PMem.ldU64 (fp + 8)
    let t'5 ← PMem.ldU8 (t'4 + 27)
    let t'6 := UInt8.toUInt32 (t'5)
    new_ptype := t'6
  else
    let t'7 ← PMem.ldU8 (info' + 28)
    let t'8 := UInt8.toUInt32 (t'7)
    new_ptype := t'8
  AP_Param.Param_header.Param_header (fp + 48)
  PMem.stBits (fp + 48) 8 5 (UInt32.toUInt64 (old_ptype))
  let t'9 ← PMem.ldU16 (info' + 26)
  AP_Param.set_key (fp + 48) t'9
  let t'10 ← PMem.ldU32 (fp + 0)
  PMem.stBits (fp + 48) 14 18 (UInt32.toUInt64 (t'10))
  let t'11 ← AP_Param.scan (fp + 48) (fp + 56)
  if !t'11 then
    return false
  AP_Param_value_storage.AP_Param_value_storage (fp + 64)
  let t'12 ← PMem.ldU16 (fp + 56)
  let t'13 ← AP_Param.type_size old_ptype
  let t'14 ← StorageAccess.read_block (0xbb70 : UInt64) /- &AP_Param::_storage -/ (fp + 64) (UInt64.toUInt16 (((UInt16.toUInt64 (t'12)) + (4 : UInt64)))) (UInt8.toUInt64 (t'13))
  discard <| pure (t'14)
  let mut old_ap : UInt64 := (fp + 64)
  if !bitmask then
    let t'15 ← AP_Param.cast_to_float old_ap old_ptype
    let mut old_float_value : Binary32 := t'15
    AP_Param.set_value new_ptype this (old_float_value * scale_factor)
  else
    let mut mask : UInt32 := default  -- uninitialized in C
    let sw'16 := UInt32.toInt32 (old_ptype)
    if sw'16 == (1 : Int32) then
      let t'17 ← AP_ParamT'signed_char_1.operator_const_signed_char__ old_ap
      let t'18 ← PMem.ldI8 t'17
      let t'19 := UInt8.toUInt32 ((Int8.toUInt8 (t'18)))
      mask := t'19
    else if sw'16 == (2 : Int32) then
      let t'20 ← AP_ParamT'short_2.operator_const_short__ old_ap
      let t'21 ← PMem.ldI16 t'20
      let t'22 := UInt16.toUInt32 ((Int16.toUInt16 (t'21)))
      mask := t'22
    else if sw'16 == (3 : Int32) then
      let t'23 ← AP_ParamT'int_3.operator_const_int__ old_ap
      let t'24 ← PMem.ldI32 t'23
      let t'25 := Int32.toUInt32 (t'24)
      mask := t'25
    else
      return false
    let sw'26 := UInt32.toInt32 (new_ptype)
    if sw'26 == (1 : Int32) then
      PMem.stI8 (fp + 76) (UInt8.toInt8 (UInt32.toUInt8 (mask)))
      AP_ParamTBase'signed_char_1.set this (fp + 76)
    else if sw'26 == (2 : Int32) then
      PMem.stI16 (fp + 78) (UInt16.toInt16 (UInt32.toUInt16 (mask)))
      AP_ParamTBase'short_2.set this (fp + 78)
    else if sw'26 == (3 : Int32) then
      PMem.stI32 (fp + 80) (UInt32.toInt32 (mask))
      AP_ParamTBase'int_3.set this (fp + 80)
    else
      return false
  AP_Param.save this true
  return true

def AP_Param._convert_parameter_width (this : UInt64) (old_ptype : UInt32) (scale_factor : Binary32) (bitmask : Bool) : PMem.M Bool := do
  let fp ← PMem.enter 84
  let r ← AP_Param._convert_parameter_width.body fp this old_ptype scale_factor bitmask
  PMem.leave fp
  return r

/-- C++ `AP_Param::convert_parameter_width : bool (ap_var_type, float)`, `AP_Param.h:517-519`. -/
def AP_Param.convert_parameter_width (this : UInt64) (old_ptype : UInt32) (scale_factor : Binary32) : PMem.M Bool := do
  let mut old_ptype := old_ptype
  let mut scale_factor := scale_factor
  let t'1 ← AP_Param._convert_parameter_width this old_ptype scale_factor false
  return t'1

/-- C++ `AP_Param::flush : void ()`, `AP_Param.cpp:1323-1335`. -/
def AP_Param.flush  : PMem.M Unit := do
  let mut counter : UInt16 := Int16.toUInt16 (Int32.toInt16 ((200 : Int32)))
  for _ in PMem.loopFuel do
    let t'1 := counter
    let t'2 := (t'1 - 1)
    counter := t'2
    if !(t'1 != (0 : UInt16)) then break
    let t'3 ← ObjectBuffer_TS'AP_Param_param_save.available (0xbf38 : UInt64) /- &AP_Param::save_queue -/
    if ((t'3 == (Int32.toUInt32 ((0 : Int32)))) && true) then
      discard <| pure (true)
      break
    let t'4 ← PMem.ldU64 ((0xba88 : UInt64) /- &hal -/ + 80)
    discard <| PMem.halDev "AP_HAL::Scheduler::expect_delay_ms" t'4 #[(UInt32.toUInt64 ((Int32.toUInt32 ((10 : Int32)))))]
    let t'5 ← PMem.ldU64 ((0xba88 : UInt64) /- &hal -/ + 80)
    discard <| PMem.hal "AP_HAL::Scheduler::delay" t'5 #[(UInt16.toUInt64 ((Int16.toUInt16 (Int32.toInt16 ((10 : Int32))))))]
    let t'6 ← PMem.ldU64 ((0xba88 : UInt64) /- &hal -/ + 80)
    discard <| PMem.halDev "AP_HAL::Scheduler::expect_delay_ms" t'6 #[(UInt32.toUInt64 ((Int32.toUInt32 ((0 : Int32)))))]
  return ()

/-- C++ `AP_ParamTBase<unsigned short, 2>::set_and_save : void (const unsigned short &)`, `AP_ParamT.cpp:79-83`. -/
def AP_ParamTBase'unsigned_short_2.set_and_save (this : UInt64) (v : UInt64) : PMem.M Unit := do
  let t'1 ← PMem.ldU16 this
  let t'2 ← PMem.ldU16 v
  let mut force : Bool := (decide ((Binary32.abs (Int32.toBinary32 (((UInt32.toInt32 (UInt16.toUInt32 (t'1))) - (UInt32.toInt32 (UInt16.toUInt32 (t'2))))))) < (Binary32.ofBits 0x34000000 /- 11920929/100000000000000 -/)))
  AP_ParamTBase'unsigned_short_2.set this v
  AP_Param.save this force
  return ()

/-- C++ `AP_Param::convert_old_parameter : void (const struct ConversionInfo *, float, uint8_t)`, `AP_Param.cpp:2016-2073`. -/
def AP_Param.convert_old_parameter.body (fp : UInt64) (info' : UInt64) (scaler : Binary32) (flags : UInt8) : PMem.M Unit := do
  let mut info' := info'
  let mut scaler := scaler
  let mut flags := flags
  AP_Param_value_storage.AP_Param_value_storage (fp + 0)
  let mut ap : UInt64 := (fp + 0)
  let t'1 ← AP_Param.find_old_parameter info' ap
  if !t'1 then
    return ()
  let t'2 ← PMem.ldU64 (info' + 16)
  let t'3 ← AP_Param.find (t'2 + ((Int32.toInt64 ((0 : Int32))) * 1).toUInt64) (fp + 16) (0 : UInt64)
  let mut ap2 : UInt64 := t'3
  if (ap2 == (0 : UInt64)) then
    for _ in [0:1] do
      let t'4 ← PMem.ldU64 ((0xba88 : UInt64) /- &hal -/ + 48)
      let t'5 ← PMem.ldU64 (info' + 16)
      discard <| PMem.halDev "AP_HAL::BetterStream::printf" t'4 #[(0x181ce : UInt64) /- "Unknown conversion '%s'\n" -/, t'5]
    return ()
  let mut sc'7 := !(((UInt32.toInt32 (UInt8.toUInt32 (flags))) &&& (UInt32.toInt32 ((2 : UInt32)))) != (0 : Int32))
  if sc'7 then
    let t'6 ← AP_Param.configured_in_storage ap2
    sc'7 := t'6
  if sc'7 then
    return ()
  let t'8 ← PMem.ldU32 (fp + 16)
  let t'9 ← PMem.ldU32 (info' + 8)
  let mut sc'11 := ((UInt32.toInt32 (t'8)) == (UInt32.toInt32 (t'9)))
  if sc'11 then
    let t'10 ← is_equal'float_float scaler (Binary32.ofBits 0x3f800000 /- 1 -/)
    sc'11 := t'10
  if (sc'11 && ((UInt32.toInt32 (UInt8.toUInt32 (flags))) == (0 : Int32))) then
    let t'12 ← PMem.ldU32 (info' + 8)
    let t'13 ← AP_Param.type_size t'12
    let mut value_size : UInt8 := t'13
    let t'14 ← PMem.memcmp ap2 ap (UInt8.toUInt64 (value_size))
    if (t'14 != (0 : Int32)) then
      let t'15 ← PMem.memcpy ap2 ap (UInt8.toUInt64 (value_size))
      discard <| pure (t'15)
      AP_Param.save ap2 false
  else
    let t'16 ← PMem.ldU32 (fp + 16)
    let mut sc'18 := (decide ((UInt32.toInt32 (t'16)) ≤ (UInt32.toInt32 ((4 : UInt32)))))
    if sc'18 then
      let t'17 ← PMem.ldU32 (info' + 8)
      sc'18 := (decide ((UInt32.toInt32 (t'17)) ≤ (UInt32.toInt32 ((4 : UInt32)))))
    if sc'18 then
      let t'19 ← PMem.ldU32 (info' + 8)
      let t'20 ← AP_Param.cast_to_float ap t'19
      let mut v : Binary32 := t'20
      if ((UInt32.toInt32 (UInt8.toUInt32 (flags))) &&& (UInt32.toInt32 ((1 : UInt32)))) != (0 : Int32) then
        let t'21 ← is_equal'float_float v (-(Binary32.ofBits 0x3f800000 /- 1 -/))
        let mut c'22 : Int32 := default
        if t'21 then
          c'22 := (1 : Int32)
        else
          c'22 := (0 : Int32)
        let t'23 := Int32.toBinary32 (c'22)
        v := t'23
      let t'24 ← PMem.ldU32 (fp + 16)
      let t'25 ← AP_Param.cast_to_float ap2 t'24
      let t'26 ← is_equal'float_float v t'25
      if !t'26 then
        let t'27 ← PMem.ldU32 (fp + 16)
        AP_Param.set_value t'27 ap2 (v * scaler)
        AP_Param.save ap2 false
    else
      for _ in [0:1] do
        let t'28 ← PMem.ldU64 ((0xba88 : UInt64) /- &hal -/ + 48)
        let t'29 ← PMem.ldU64 (info' + 16)
        discard <| PMem.halDev "AP_HAL::BetterStream::printf" t'28 #[(0x181e7 : UInt64) /- "Bad conversion type '%s'\n" -/, t'29]
  return ()

def AP_Param.convert_old_parameter (info' : UInt64) (scaler : Binary32) (flags : UInt8) : PMem.M Unit := do
  let fp ← PMem.enter 20
  let r ← AP_Param.convert_old_parameter.body fp info' scaler flags
  PMem.leave fp
  return r

/-- C++ `AP_Param::convert_old_parameters_scaled : void (const struct ConversionInfo *, uint8_t, float, uint8_t)`, `AP_Param.cpp:2084-2092`. -/
def AP_Param.convert_old_parameters_scaled (conversion_table : UInt64) (table_size : UInt8) (scaler : Binary32) (flags : UInt8) : PMem.M Unit := do
  let mut conversion_table := conversion_table
  let mut table_size := table_size
  let mut scaler := scaler
  let mut flags := flags
  for i'1 in [0:table_size.toNat] do
    let i : UInt8 := UInt8.ofNat i'1
    AP_Param.convert_old_parameter (conversion_table + ((UInt64.toInt64 (UInt8.toUInt64 (i))) * 24).toUInt64) scaler flags
  AP_Param.flush
  return ()

/-- C++ `AP_Param::convert_old_parameters : void (const struct ConversionInfo *, uint8_t, uint8_t)`, `AP_Param.cpp:2078-2081`. -/
def AP_Param.convert_old_parameters (conversion_table : UInt64) (table_size : UInt8) (flags : UInt8) : PMem.M Unit := do
  let mut conversion_table := conversion_table
  let mut table_size := table_size
  let mut flags := flags
  AP_Param.convert_old_parameters_scaled conversion_table table_size (Binary32.ofBits 0x3f800000 /- 1 -/) flags
  return ()

/-- C++ `AP_ParamTBase<signed char, 1>::set_and_save_ifchanged : void (const signed char &)`, `<built-in>:91-100`. -/
def AP_ParamTBase'signed_char_1.set_and_save_ifchanged (this : UInt64) (v : UInt64) : PMem.M Unit := do
  let t'1 ← PMem.ldI8 v
  let t'2 ← PMem.ldI8 this
  if ((Int8.toInt32 (t'1)) == (Int8.toInt32 (t'2))) then
    return ()
  AP_ParamTBase'signed_char_1.set this v
  AP_Param.save this true
  return ()

/-- C++ `AP_Param::convert_old_parameters_scaled : void (uint16_t, const struct ConversionInfoNoKey *, uint8_t, float, uint8_t)`, `AP_Param.cpp:2103-2117`. -/
def AP_Param.convert_old_parameters_scaled'2.body (fp : UInt64) (old_key : UInt16) (conversion_table : UInt64) (table_size : UInt8) (scaler : Binary32) (flags : UInt8) : PMem.M Unit := do
  let mut old_key := old_key
  let mut conversion_table := conversion_table
  let mut table_size := table_size
  let mut scaler := scaler
  let mut flags := flags
  for i'1 in [0:table_size.toNat] do
    let i : UInt8 := UInt8.ofNat i'1
    PMem.stU16 ((fp + 0) + 0) old_key
    let t'2 ← PMem.ldU32 (conversion_table + ((UInt64.toInt64 (UInt8.toUInt64 (i))) * 16).toUInt64)
    PMem.stU32 ((fp + 0) + 4) t'2
    let t'3 ← PMem.ldU32 ((conversion_table + ((UInt64.toInt64 (UInt8.toUInt64 (i))) * 16).toUInt64) + 4)
    PMem.stU32 ((fp + 0) + 8) t'3
    let t'4 ← PMem.ldU64 ((conversion_table + ((UInt64.toInt64 (UInt8.toUInt64 (i))) * 16).toUInt64) + 8)
    PMem.stU64 ((fp + 0) + 16) t'4
    AP_Param.convert_old_parameter (fp + 0) scaler flags
  AP_Param.flush
  return ()

def AP_Param.convert_old_parameters_scaled'2 (old_key : UInt16) (conversion_table : UInt64) (table_size : UInt8) (scaler : Binary32) (flags : UInt8) : PMem.M Unit := do
  let fp ← PMem.enter 24
  let r ← AP_Param.convert_old_parameters_scaled'2.body fp old_key conversion_table table_size scaler flags
  PMem.leave fp
  return r

/-- C++ `AP_Param::convert_old_parameters : void (uint16_t, const struct ConversionInfoNoKey *, uint8_t, uint8_t)`, `AP_Param.cpp:2096-2099`. -/
def AP_Param.convert_old_parameters'2 (old_key : UInt16) (conversion_table : UInt64) (table_size : UInt8) (flags : UInt8) : PMem.M Unit := do
  let mut old_key := old_key
  let mut conversion_table := conversion_table
  let mut table_size := table_size
  let mut flags := flags
  AP_Param.convert_old_parameters_scaled'2 old_key conversion_table table_size (Binary32.ofBits 0x3f800000 /- 1 -/) flags
  return ()

/-- C++ `AP_ParamTBase<unsigned int, 3>::set_and_save : void (const unsigned int &)`, `AP_ParamT.cpp:79-83`. -/
def AP_ParamTBase'unsigned_int_3.set_and_save (this : UInt64) (v : UInt64) : PMem.M Unit := do
  let t'1 ← PMem.ldU32 this
  let t'2 ← PMem.ldU32 v
  let mut force : Bool := (decide ((Binary32.abs (UInt32.toBinary32 ((t'1 - t'2)))) < (Binary32.ofBits 0x34000000 /- 11920929/100000000000000 -/)))
  AP_ParamTBase'unsigned_int_3.set this v
  AP_Param.save this force
  return ()

end Vehicle_lib
