import ArduLean.Runtime.Hal
import ArduLean.Vehicle.libraries.AP_Math.AP_Math
import ArduLean.Vehicle.libraries.StorageManager.StorageManager
import ArduLean.Vehicle.libraries.AP_Param.AP_Param
import ArduLean.Vehicle.libraries.AP_Common.AP_Common
import ArduLean.Vehicle.libraries.GCS_MAVLink.GCS_MAVLink
import ArduLean.Vehicle.libraries.GCS_MAVLink.GCS_MAVLink_2

/-!
ArduPilot `libraries/AP_Param`, part 3 of 3. Sources: `libraries/AP_Param/AP_Param.cpp`.

Items of `lean/Vehicle_lib.lean` (the vehicle translation), unchanged; placed by `tools/split_modules.py` (`ArduLean/Vehicle/INDEX.md`).
-/

open FloatLib.Floats (Binary32 Binary64)

set_option linter.unusedVariables false
set_option linter.unreachableTactic false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false

namespace Vehicle_lib

/-- C++ `AP_Param::send_parameter : void (const char *, enum ap_var_type, uint8_t) const`, `AP_Param.cpp:2712-2745`. -/
def AP_Param.send_parameter.body (fp : UInt64) (this : UInt64) (name : UInt64) (var_type : UInt32) (idx : UInt8) : PMem.M Unit := do
  let mut name := name
  let mut var_type := var_type
  let mut idx := idx
  if (((UInt32.toInt32 (UInt8.toUInt32 (idx))) != (0 : Int32)) && ((UInt32.toInt32 (var_type)) == (UInt32.toInt32 ((5 : UInt32))))) then
    var_type := (4 : UInt32)
  if (decide ((UInt32.toInt32 (var_type)) > (UInt32.toInt32 ((5 : UInt32))))) then
    return ()
  if ((UInt32.toInt32 (var_type)) != (UInt32.toInt32 ((5 : UInt32)))) then
    let t'1 ← AP_Param.cast_to_float this var_type
    let t'2 ← gcs
    GCS.send_parameter_value t'2 name var_type t'1
    return ()
  let t'3 ← AP_ParamV'Vector3_float_5.get this
  let v : UInt64 := t'3
  let t'4 ← PMem.strncpy (fp + 0) name (Int64.toUInt64 (Int32.toInt64 ((16 : Int32))))
  discard <| pure (t'4)
  let t'5 := Int32.toInt8 ((0 : Int32))
  PMem.stI8 ((fp + 0) + ((Int32.toInt64 ((16 : Int32))) * 1).toUInt64) t'5
  let t'6 ← PMem.strlen name
  let name_axis : UInt64 := ((fp + 0) + ((UInt64.toInt64 ((t'6 - (Int64.toUInt64 (Int32.toInt64 ((1 : Int32))))))) * 1).toUInt64)
  PMem.stI8 name_axis (88 : Int8)
  let t'7 ← PMem.ldF32 v
  let t'8 ← gcs
  GCS.send_parameter_value t'8 (fp + 0) (4 : UInt32) t'7
  PMem.stI8 name_axis (89 : Int8)
  let t'9 ← PMem.ldF32 (v + 4)
  let t'10 ← gcs
  GCS.send_parameter_value t'10 (fp + 0) (4 : UInt32) t'9
  PMem.stI8 name_axis (90 : Int8)
  let t'11 ← PMem.ldF32 (v + 8)
  let t'12 ← gcs
  GCS.send_parameter_value t'12 (fp + 0) (4 : UInt32) t'11
  return ()

def AP_Param.send_parameter (this : UInt64) (name : UInt64) (var_type : UInt32) (idx : UInt8) : PMem.M Unit := do
  let fp ← PMem.enter 17
  let r ← AP_Param.send_parameter.body fp this name var_type idx
  PMem.leave fp
  return r

/-- C++ `AP_Param::save_sync : void (bool, bool)`, `AP_Param.cpp:1158-1264`. -/
def AP_Param.save_sync.body (fp : UInt64) (this : UInt64) (force_save : Bool) (send_to_gcs : Bool) : PMem.M Unit := do
  let mut force_save := force_save
  let mut send_to_gcs := send_to_gcs
  PMem.stU32 (fp + 0) (Int32.toUInt32 ((0 : Int32)))
  discard <| PMem.memset ((fp + 16) + 0) 0 1
  discard <| PMem.memset ((fp + 16) + 8) 0 16
  let t'1 ← AP_Param.find_var_info this (fp + 0) (fp + 8) (fp + 16) (fp + 40)
  let mut info' : UInt64 := t'1
  let mut ap : UInt64 := default  -- uninitialized in C
  if (info' == (0 : UInt64)) then
    return ()
  AP_Param.Param_header.Param_header (fp + 48)
  let t'2 ← PMem.ldU64 (fp + 8)
  if (t'2 != (0 : UInt64)) then
    let t'3 ← PMem.ldU64 (fp + 8)
    let t'4 ← PMem.ldU8 (t'3 + 27)
    let t'5 := UInt8.toUInt32 (t'4)
    PMem.stBits (fp + 48) 8 5 (UInt32.toUInt64 (t'5))
    let t'6 ← PMem.ldU64 (fp + 8)
    let t'7 ← PMem.ldU16 (t'6 + 24)
    if ((UInt32.toInt32 (UInt16.toUInt32 (t'7))) &&& ((1 : Int32) <<< (6 : Int32))) != (0 : Int32) then
      send_to_gcs := false
  else
    let t'8 ← PMem.ldU8 (info' + 28)
    let t'9 := UInt8.toUInt32 (t'8)
    PMem.stBits (fp + 48) 8 5 (UInt32.toUInt64 (t'9))
    let t'10 ← PMem.ldU16 (info' + 24)
    if ((UInt32.toInt32 (UInt16.toUInt32 (t'10))) &&& ((1 : Int32) <<< (6 : Int32))) != (0 : Int32) then
      send_to_gcs := false
  let t'11 ← PMem.ldU16 (info' + 26)
  AP_Param.set_key (fp + 48) t'11
  let t'12 ← PMem.ldU32 (fp + 0)
  PMem.stBits (fp + 48) 14 18 (UInt32.toUInt64 (t'12))
  ap := this
  let t'13 ← PMem.ldBits (fp + 48) 8 5
  let mut sc'15 := ((UInt32.toInt32 ((UInt64.toUInt32 (t'13)))) != (UInt32.toInt32 ((5 : UInt32))))
  if sc'15 then
    let t'14 ← PMem.ldU8 (fp + 40)
    sc'15 := ((UInt32.toInt32 (UInt8.toUInt32 (t'14))) != (0 : Int32))
  if sc'15 then
    return ()
  let t'16 ← PMem.ldU8 (fp + 40)
  if ((UInt32.toInt32 (UInt8.toUInt32 (t'16))) != (0 : Int32)) then
    let t'17 ← PMem.ldU8 (fp + 40)
    let t'18 := ((Int64.toUInt64 ((UInt64.toInt64 (ap)))) - ((UInt64.toInt64 (((UInt8.toUInt64 (t'17)) * (4 : UInt64)))) * 1).toUInt64)
    ap := t'18
  let t'19 ← PMem.ldBits (fp + 48) 8 5
  let mut sc'21 := ((UInt32.toInt32 ((UInt64.toUInt32 (t'19)))) == (UInt32.toInt32 ((1 : UInt32))))
  if sc'21 then
    let t'20 ← PMem.ldU64 (fp + 8)
    sc'21 := (t'20 != (0 : UInt64))
  let mut sc'24 := sc'21
  if sc'24 then
    let t'22 ← PMem.ldU64 (fp + 8)
    let t'23 ← PMem.ldU16 (t'22 + 24)
    sc'24 := ((UInt32.toInt32 (UInt16.toUInt32 (t'23))) &&& ((1 : Int32) <<< (2 : Int32))) != (0 : Int32)
  if sc'24 then
    AP_Param.invalidate_count
  let t'25 ← PMem.ldU64 (fp + 8)
  let t'26 ← PMem.ldU8 (fp + 40)
  AP_Param.copy_name_info this info' t'25 (fp + 16) t'26 (fp + 56) (17 : UInt64) true
  let t'27 ← AP_Param.scan (fp + 48) (fp + 80)
  if t'27 then
    let t'28 ← PMem.ldU16 (fp + 80)
    let t'29 ← PMem.ldBits (fp + 48) 8 5
    let t'30 ← AP_Param.type_size (UInt64.toUInt32 (t'29))
    AP_Param.eeprom_write_check ap (UInt64.toUInt16 (((UInt16.toUInt64 (t'28)) + (4 : UInt64)))) t'30
    if send_to_gcs then
      let t'31 ← PMem.ldBits (fp + 48) 8 5
      let t'32 ← PMem.ldU8 (fp + 40)
      AP_Param.send_parameter this (fp + 56) (UInt64.toUInt32 (t'31)) t'32
    return ()
  let t'33 ← PMem.ldU16 (fp + 80)
  if ((UInt32.toInt32 (UInt16.toUInt32 (t'33))) == (UInt32.toInt32 (UInt16.toUInt32 ((Int16.toUInt16 (Int32.toInt16 ((~~~(0 : Int32))))))))) then
    PMem.stB (0xbba0 : UInt64) /- &AP_Param::eeprom_full -/ true
    for _ in [0:1] do
      let t'34 ← PMem.ldU64 ((0xba88 : UInt64) /- &hal -/ + 48)
      discard <| PMem.halDev "AP_HAL::BetterStream::printf" t'34 #[(0x18163 : UInt64) /- "EEPROM full\n" -/]
    return ()
  let t'35 ← PMem.ldBits (fp + 48) 8 5
  if (decide ((UInt32.toInt32 ((UInt64.toUInt32 (t'35)))) ≤ (UInt32.toInt32 ((4 : UInt32))))) then
    let t'36 ← PMem.ldBits (fp + 48) 8 5
    let t'37 ← AP_Param.cast_to_float this (UInt64.toUInt32 (t'36))
    let mut v1 : Binary32 := t'37
    let mut v2 : Binary32 := default  -- uninitialized in C
    let t'38 ← PMem.ldU64 (fp + 8)
    if (t'38 != (0 : UInt64)) then
      let t'39 ← PMem.ldU64 (fp + 8)
      let t'40 ← AP_Param.get_default_value'2 this t'39
      v2 := t'40
    else
      let t'41 ← AP_Param.get_default_value this info'
      v2 := t'41
    let t'42 ← is_equal'float_float v1 v2
    if (t'42 && (!force_save)) then
      if send_to_gcs then
        let t'43 ← PMem.ldU8 (info' + 28)
        let t'44 ← gcs
        GCS.send_parameter_value t'44 (fp + 56) (UInt8.toUInt32 (t'43)) v2
      return ()
    let mut sc'46 := !force_save
    if sc'46 then
      let t'45 ← PMem.ldBits (fp + 48) 8 5
      sc'46 := (((UInt32.toInt32 ((UInt64.toUInt32 (t'45)))) != (UInt32.toInt32 ((3 : UInt32)))) && (decide ((Binary32.abs (v1 - v2)) < ((Binary32.ofBits 0x38d1b717 /- 499999987/5000000000000 -/) * (Binary32.abs v1)))))
    if sc'46 then
      if send_to_gcs then
        let t'47 ← PMem.ldU8 (info' + 28)
        let t'48 ← gcs
        GCS.send_parameter_value t'48 (fp + 56) (UInt8.toUInt32 (t'47)) v2
      return ()
  let t'49 ← PMem.ldU16 (fp + 80)
  let t'50 ← PMem.ldBits (fp + 48) 8 5
  let t'51 ← AP_Param.type_size (UInt64.toUInt32 (t'50))
  let t'52 ← StorageAccess.size (0xbb70 : UInt64) /- &AP_Param::_storage -/
  if (decide (((Int64.toUInt64 (Int32.toInt64 (((UInt32.toInt32 (UInt16.toUInt32 (t'49))) + (UInt32.toInt32 (UInt8.toUInt32 (t'51))))))) + ((Int64.toUInt64 (Int32.toInt64 ((2 : Int32)))) * (4 : UInt64))) ≥ (UInt16.toUInt64 (t'52)))) then
    PMem.stB (0xbba0 : UInt64) /- &AP_Param::eeprom_full -/ true
    for _ in [0:1] do
      let t'53 ← PMem.ldU64 ((0xba88 : UInt64) /- &hal -/ + 48)
      discard <| PMem.halDev "AP_HAL::BetterStream::printf" t'53 #[(0x18163 : UInt64) /- "EEPROM full\n" -/]
    return ()
  let t'54 ← PMem.ldU16 (fp + 80)
  let t'55 ← PMem.ldBits (fp + 48) 8 5
  let t'56 ← AP_Param.type_size (UInt64.toUInt32 (t'55))
  AP_Param.write_sentinel (UInt64.toUInt16 ((((UInt16.toUInt64 (t'54)) + (4 : UInt64)) + (UInt8.toUInt64 (t'56)))))
  let t'57 ← PMem.ldU16 (fp + 80)
  let t'58 ← PMem.ldBits (fp + 48) 8 5
  let t'59 ← AP_Param.type_size (UInt64.toUInt32 (t'58))
  AP_Param.eeprom_write_check ap (UInt64.toUInt16 (((UInt16.toUInt64 (t'57)) + (4 : UInt64)))) t'59
  let t'60 ← PMem.ldU16 (fp + 80)
  AP_Param.eeprom_write_check (fp + 48) t'60 (UInt64.toUInt8 ((4 : UInt64)))
  if send_to_gcs then
    let t'61 ← PMem.ldBits (fp + 48) 8 5
    let t'62 ← PMem.ldU8 (fp + 40)
    AP_Param.send_parameter this (fp + 56) (UInt64.toUInt32 (t'61)) t'62
  return ()

def AP_Param.save_sync (this : UInt64) (force_save : Bool) (send_to_gcs : Bool) : PMem.M Unit := do
  let fp ← PMem.enter 82
  let r ← AP_Param.save_sync.body fp this force_save send_to_gcs
  PMem.leave fp
  return r

/-- C++ `AP_Param::notify : void () const`, `AP_Param.cpp:1129-1152`. -/
def AP_Param.notify.body (fp : UInt64) (this : UInt64) : PMem.M Unit := do
  PMem.stU32 (fp + 0) (Int32.toUInt32 ((0 : Int32)))
  discard <| PMem.memset ((fp + 16) + 0) 0 1
  discard <| PMem.memset ((fp + 16) + 8) 0 16
  let t'1 ← AP_Param.find_var_info this (fp + 0) (fp + 8) (fp + 16) (fp + 40)
  let mut info' : UInt64 := t'1
  if (info' == (0 : UInt64)) then
    return ()
  let t'2 ← PMem.ldU64 (fp + 8)
  let t'3 ← PMem.ldU8 (fp + 40)
  AP_Param.copy_name_info this info' t'2 (fp + 16) t'3 (fp + 48) (17 : UInt64) true
  let mut param_header_type : UInt32 := default  -- uninitialized in C
  let t'4 ← PMem.ldU64 (fp + 8)
  if (t'4 != (0 : UInt64)) then
    let t'5 ← PMem.ldU64 (fp + 8)
    let t'6 ← PMem.ldU8 (t'5 + 27)
    let t'7 := UInt8.toUInt32 (t'6)
    param_header_type := t'7
  else
    let t'8 ← PMem.ldU8 (info' + 28)
    let t'9 := UInt8.toUInt32 (t'8)
    param_header_type := t'9
  let t'10 ← PMem.ldU8 (fp + 40)
  AP_Param.send_parameter this (fp + 48) param_header_type t'10
  return ()

def AP_Param.notify (this : UInt64) : PMem.M Unit := do
  let fp ← PMem.enter 65
  let r ← AP_Param.notify.body fp this
  PMem.leave fp
  return r

/-- C++ `AP_Param::save_io_handler : void ()`, `AP_Param.cpp:1303-1318`. -/
def AP_Param.save_io_handler.body (fp : UInt64) (this : UInt64) : PMem.M Unit := do
  AP_Param.param_save.param_save (fp + 0)
  for _ in PMem.loopFuel do
    if !(true) then break
    let t'1 ← ObjectBuffer_TS'AP_Param_param_save.pop (0xbf38 : UInt64) /- &AP_Param::save_queue -/ (fp + 0)
    if !t'1 then
      break
    let t'2 ← PMem.ldB ((fp + 0) + 8)
    let t'3 ← PMem.ldU64 (fp + 0)
    AP_Param.save_sync t'3 t'2 true
  if (← get).sysInit then
    let t'4 ← AP_Param.count_parameters
    discard <| pure (t'4)
  return ()

def AP_Param.save_io_handler (this : UInt64) : PMem.M Unit := do
  let fp ← PMem.enter 9
  let r ← AP_Param.save_io_handler.body fp this
  PMem.leave fp
  return r

end Vehicle_lib
