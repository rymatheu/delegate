import ArduLean.Runtime.Bridge
import ArduLean.Vehicle.libraries.AP_Math.AP_Math
import ArduLean.Vehicle.libraries.AP_HAL.AP_HAL
import ArduLean.Vehicle.libraries.AP_Param.AP_Param

/-!
ArduPilot `libraries/AP_Common`. Sources: `libraries/AP_Common/Location.cpp`, `libraries/AP_Common/AP_Common.h`, `libraries/AP_Common/Bitmask.h`, `libraries/AP_Common/AP_Common.cpp`, `libraries/AP_Common/Location.h`, `libraries/AP_Common/AP_FWVersion.cpp`, `libraries/AP_Common/AP_FWVersion.h`.

Items of `lean/Vehicle_lib.lean` (the vehicle translation), unchanged; placed by `tools/split_modules.py` (`ArduLean/Vehicle/INDEX.md`).
-/

open FloatLib.Floats (Binary32 Binary64)

set_option linter.unusedVariables false
set_option linter.unreachableTactic false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false

namespace Vehicle_lib

/-- C++ `ObjectBuffer_TS<AP_Param::param_save>::peek : bool (AP_Param::param_save &)`, `AP_Common.h:420-423`. -/
def ObjectBuffer_TS'AP_Param_param_save.peek (this : UInt64) (object : UInt64) : PMem.M Bool := do
  let t'1 ← PMem.ldU64 this
  let t'2 ← ByteBuffer.peekbytes t'1 object (UInt64.toUInt32 ((9 : UInt64)))
  return ((UInt32.toUInt64 (t'2)) == (9 : UInt64))

/-- C++ `ObjectBuffer_TS<AP_Param::param_save>::push : bool (const AP_Param::param_save &)`, `AP_Common.h:351-357`. -/
def ObjectBuffer_TS'AP_Param_param_save.push (this : UInt64) (object : UInt64) : PMem.M Bool := do
  let t'1 ← PMem.ldU64 this
  let t'2 ← ByteBuffer.space t'1
  if (decide ((UInt32.toUInt64 (t'2)) < (9 : UInt64))) then
    return false
  let t'3 ← PMem.ldU64 this
  let t'4 ← ByteBuffer.write t'3 object (UInt64.toUInt32 ((9 : UInt64)))
  return ((UInt32.toUInt64 (t'4)) == (9 : UInt64))

/-- C++ `Location::zero : void ()`, `Location.cpp:18-21`. -/
def Location.zero (this : UInt64) : PMem.M Unit := do
  let t'1 ← PMem.memset this (0 : Int32) (16 : UInt64)
  discard <| pure (t'1)
  return ()

/-- C++ `Location::Location : void ()`, `Location.h:31-?`. -/
def Location.Location (this : UInt64) : PMem.M Unit := do
  Location.zero this
  return ()

/-- C++ `ObjectArray<GCS::statustext_t>::is_empty : bool () const`, `AP_Common.h:497-499`. -/
def ObjectArray'GCS_statustext_t.is_empty (this : UInt64) : PMem.M Bool := do
  let t'1 ← PMem.ldU16 (this + 10)
  return ((UInt32.toInt32 (UInt16.toUInt32 (t'1))) == (0 : Int32))

/-- C++ `ObjectArray<GCS::statustext_t>::available : uint16_t () const`, `AP_Common.h:487-489`. -/
def ObjectArray'GCS_statustext_t.available (this : UInt64) : PMem.M UInt16 := do
  let t'1 ← PMem.ldU16 (this + 10)
  return t'1

/-- C++ `ObjectArray<GCS::statustext_t>::operator[] : GCS::statustext_t *(uint16_t)`, `AP_Common.h:578-583`. -/
def ObjectArray'GCS_statustext_t.operator__ (this : UInt64) (i : UInt16) : PMem.M UInt64 := do
  let mut i := i
  let t'1 ← PMem.ldU16 (this + 10)
  if (decide ((UInt32.toInt32 (UInt16.toUInt32 (i))) ≥ (UInt32.toInt32 (UInt16.toUInt32 (t'1))))) then
    return (0 : UInt64)
  let t'2 ← PMem.ldU64 this
  let t'3 ← PMem.ldU16 (this + 12)
  let t'4 ← PMem.ldU16 (this + 8)
  return (t'2 + ((Int32.toInt64 ((((UInt32.toInt32 (UInt16.toUInt32 (t'3))) + (UInt32.toInt32 (UInt16.toUInt32 (i)))) % (UInt32.toInt32 (UInt16.toUInt32 (t'4)))))) * 64).toUInt64)

/-- C++ `ObjectArray<GCS::statustext_t>::pop : bool ()`, `AP_Common.h:514-521`. -/
def ObjectArray'GCS_statustext_t.pop (this : UInt64) : PMem.M Bool := do
  let t'1 ← ObjectArray'GCS_statustext_t.is_empty this
  if t'1 then
    return false
  let t'2 ← PMem.ldU16 (this + 12)
  let t'3 ← PMem.ldU16 (this + 8)
  let t'4 := Int16.toUInt16 (Int32.toInt16 ((((UInt32.toInt32 (UInt16.toUInt32 (t'2))) + (1 : Int32)) % (UInt32.toInt32 (UInt16.toUInt32 (t'3))))))
  PMem.stU16 (this + 12) t'4
  let t'5 := (this + 10)
  let t'6 ← PMem.ldU16 t'5
  let t'7 := (t'6 - 1)
  PMem.stU16 t'5 t'7
  return true

/-- C++ `ObjectArray<GCS::statustext_t>::remove : bool (uint16_t)`, `AP_Common.h:555-574`. -/
def ObjectArray'GCS_statustext_t.remove (this : UInt64) (n : UInt16) : PMem.M Bool := do
  let mut n := n
  let t'1 ← PMem.ldU16 (this + 10)
  if (decide ((UInt32.toInt32 (UInt16.toUInt32 (n))) ≥ (UInt32.toInt32 (UInt16.toUInt32 (t'1))))) then
    return false
  let t'2 ← PMem.ldU16 (this + 10)
  if ((UInt32.toInt32 (UInt16.toUInt32 (n))) == ((UInt32.toInt32 (UInt16.toUInt32 (t'2))) - (1 : Int32))) then
    let t'3 := (this + 10)
    let t'4 ← PMem.ldU16 t'3
    let t'5 := (t'4 - 1)
    PMem.stU16 t'3 t'5
    return true
  if ((UInt32.toInt32 (UInt16.toUInt32 (n))) == (0 : Int32)) then
    let t'6 ← ObjectArray'GCS_statustext_t.pop this
    return t'6
  let mut i : UInt16 := n
  let mut first'7 := true
  for _ in PMem.loopFuel do
    if !first'7 then
      let t'8 := i
      let t'9 := (t'8 + 1)
      i := t'9
      pure ()
    first'7 := false
    let t'10 ← PMem.ldU16 (this + 10)
    if !((decide ((UInt32.toInt32 (UInt16.toUInt32 (i))) < ((UInt32.toInt32 (UInt16.toUInt32 (t'10))) - (1 : Int32))))) then break
    let t'11 ← ObjectArray'GCS_statustext_t.operator__ this i
    let t'12 ← ObjectArray'GCS_statustext_t.operator__ this (Int16.toUInt16 (Int32.toInt16 (((UInt32.toInt32 (UInt16.toUInt32 (i))) + (1 : Int32)))))
    discard <| PMem.memcpy t'11 t'12 64
    discard <| pure (t'11)
  let t'13 := (this + 10)
  let t'14 ← PMem.ldU16 t'13
  let t'15 := (t'14 - 1)
  PMem.stU16 t'13 t'15
  return true

/-- `AP_HAL.BetterStream.BetterStream` as a pure function of its arguments (it reads and writes no memory). -/
def AP_HAL.BetterStream.BetterStream.pure' (this : UInt64) : Id Unit := do
  return ()

/-- C++ `AP_HAL::BetterStream::BetterStream : void () noexcept`, `AP_Common.h:?-?`. -/
def AP_HAL.BetterStream.BetterStream (this : UInt64) : PMem.M Unit :=
  pure (_root_.Vehicle_lib.AP_HAL.BetterStream.BetterStream.pure' this)

/-- C++ `ObjectArray<GCS::statustext_t>::space : uint16_t () const`, `AP_Common.h:492-494`. -/
def ObjectArray'GCS_statustext_t.space (this : UInt64) : PMem.M UInt16 := do
  let t'1 ← PMem.ldU16 (this + 8)
  let t'2 ← PMem.ldU16 (this + 10)
  return Int16.toUInt16 (Int32.toInt16 (((UInt32.toInt32 (UInt16.toUInt32 (t'1))) - (UInt32.toInt32 (UInt16.toUInt32 (t'2))))))

/-- C++ `ObjectArray<GCS::statustext_t>::push : bool (const GCS::statustext_t &)`, `AP_Common.h:502-509`. -/
def ObjectArray'GCS_statustext_t.push (this : UInt64) (object : UInt64) : PMem.M Bool := do
  let t'1 ← ObjectArray'GCS_statustext_t.space this
  if ((UInt32.toInt32 (UInt16.toUInt32 (t'1))) == (0 : Int32)) then
    return false
  let t'2 ← PMem.ldU64 this
  let t'3 ← PMem.ldU16 (this + 12)
  let t'4 ← PMem.ldU16 (this + 10)
  let t'5 ← PMem.ldU16 (this + 8)
  discard <| PMem.memcpy (t'2 + ((Int32.toInt64 ((((UInt32.toInt32 (UInt16.toUInt32 (t'3))) + (UInt32.toInt32 (UInt16.toUInt32 (t'4)))) % (UInt32.toInt32 (UInt16.toUInt32 (t'5)))))) * 64).toUInt64) object 64
  discard <| pure ((t'2 + ((Int32.toInt64 ((((UInt32.toInt32 (UInt16.toUInt32 (t'3))) + (UInt32.toInt32 (UInt16.toUInt32 (t'4)))) % (UInt32.toInt32 (UInt16.toUInt32 (t'5)))))) * 64).toUInt64))
  let t'6 := (this + 10)
  let t'7 ← PMem.ldU16 t'6
  let t'8 := (t'7 + 1)
  PMem.stU16 t'6 t'8
  return true

/-- C++ `ObjectArray<GCS::statustext_t>::push_force : bool (const GCS::statustext_t &)`, `AP_Common.h:545-550`. -/
def ObjectArray'GCS_statustext_t.push_force (this : UInt64) (object : UInt64) : PMem.M Bool := do
  let t'1 ← ObjectArray'GCS_statustext_t.space this
  if ((UInt32.toInt32 (UInt16.toUInt32 (t'1))) == (0 : Int32)) then
    for _ in [0:1] do
      let mut __unique_name___COUNTER__ : Bool := default  -- uninitialized in C
      let t'2 ← ObjectArray'GCS_statustext_t.pop this
      __unique_name___COUNTER__ := t'2
  let t'3 ← ObjectArray'GCS_statustext_t.push this object
  return t'3

/-- `_assert_storage_size'Location_16_16._assert_storage_size` as a pure function of its arguments (it reads and writes no memory). -/
def _assert_storage_size'Location_16_16._assert_storage_size.pure' (this : UInt64) : Id Unit := do
  return ()

/-- C++ `_assert_storage_size<Location, 16, 16>::_assert_storage_size : void () noexcept`, `AP_Common.h:180-?`. -/
def _assert_storage_size'Location_16_16._assert_storage_size (this : UInt64) : PMem.M Unit :=
  pure (_root_.Vehicle_lib._assert_storage_size'Location_16_16._assert_storage_size.pure' this)

/-- `assert_storage_size'Location_16.assert_storage_size` as a pure function of its arguments (it reads and writes no memory). -/
def assert_storage_size'Location_16.assert_storage_size.pure' (this : UInt64) : Id Unit := do
  _root_.Vehicle_lib._assert_storage_size'Location_16_16._assert_storage_size.pure' (this + 0)
  return ()

/-- C++ `assert_storage_size<Location, 16>::assert_storage_size : void () noexcept`, `AP_Common.h:183-?`. -/
def assert_storage_size'Location_16.assert_storage_size (this : UInt64) : PMem.M Unit :=
  pure (_root_.Vehicle_lib.assert_storage_size'Location_16.assert_storage_size.pure' this)

/-- C++ `Location::set_alt_cm : void (int32_t, AltFrame)`, `Location.cpp:83-106`. -/
def Location.set_alt_cm (this : UInt64) (alt_cm : Int32) (frame : Int32) : PMem.M Unit := do
  let mut alt_cm := alt_cm
  let mut frame := frame
  PMem.stI32 (this + 4) alt_cm
  let t'1 := if false then (1 : UInt8) else (0 : UInt8)
  PMem.stBits this 0 1 (UInt8.toUInt64 (t'1))
  let t'2 := if false then (1 : UInt8) else (0 : UInt8)
  PMem.stBits this 2 1 (UInt8.toUInt64 (t'2))
  let t'3 := if false then (1 : UInt8) else (0 : UInt8)
  PMem.stBits this 3 1 (UInt8.toUInt64 (t'3))
  let sw'4 := frame
  if sw'4 == (0 : Int32) then
    pure ()
  else if sw'4 == (1 : Int32) then
    let t'5 := if true then (1 : UInt8) else (0 : UInt8)
    PMem.stBits this 0 1 (UInt8.toUInt64 (t'5))
  else if sw'4 == (2 : Int32) then
    let t'6 := if true then (1 : UInt8) else (0 : UInt8)
    PMem.stBits this 3 1 (UInt8.toUInt64 (t'6))
  else if sw'4 == (3 : Int32) then
    let t'7 := if true then (1 : UInt8) else (0 : UInt8)
    PMem.stBits this 0 1 (UInt8.toUInt64 (t'7))
    let t'8 := if true then (1 : UInt8) else (0 : UInt8)
    PMem.stBits this 2 1 (UInt8.toUInt64 (t'8))
  else
    pure ()
  return ()

/-- C++ `Location::Location : void (int32_t, int32_t, int32_t, AltFrame)`, `Location.cpp:24-33`. -/
def Location.Location'3.body (fp : UInt64) (this : UInt64) (latitude : Int32) (longitude : Int32) (alt_in_cm : Int32) (frame : Int32) : PMem.M Unit := do
  let mut latitude := latitude
  let mut longitude := longitude
  let mut alt_in_cm := alt_in_cm
  let mut frame := frame
  for _ in [0:1] do
    assert_storage_size'Location_16.assert_storage_size (fp + 0)
    discard <| pure ((fp + 0))
  Location.zero this
  PMem.stI32 (this + 8) latitude
  PMem.stI32 (this + 12) longitude
  Location.set_alt_cm this alt_in_cm frame
  return ()

def Location.Location'3 (this : UInt64) (latitude : Int32) (longitude : Int32) (alt_in_cm : Int32) (frame : Int32) : PMem.M Unit := do
  let fp ← PMem.enter 1
  let r ← Location.Location'3.body fp this latitude longitude alt_in_cm frame
  PMem.leave fp
  return r

/-- C++ `Location::get_alt_frame : Location::AltFrame () const`, `Location.cpp:128-145`. -/
def Location.get_alt_frame (this : UInt64) : PMem.M Int32 := do
  let t'1 ← PMem.ldBits this 2 1
  if (UInt64.toUInt8 (t'1)) != (0 : UInt8) then
    let t'2 ← PMem.ldBits this 0 1
    if !((UInt64.toUInt8 (t'2)) != (0 : UInt8)) then
      pure ()
    return (3 : Int32)
  let t'3 ← PMem.ldBits this 3 1
  if (UInt64.toUInt8 (t'3)) != (0 : UInt8) then
    return (2 : Int32)
  let t'4 ← PMem.ldBits this 0 1
  if (UInt64.toUInt8 (t'4)) != (0 : UInt8) then
    return (1 : Int32)
  return (0 : Int32)

/-- C++ `Location::initialised : bool () const`, `AP_Common.h:198-?`. -/
def Location.initialised (this : UInt64) : PMem.M Bool := do
  let t'1 ← PMem.ldI32 (this + 8)
  let mut sc'3 := (t'1 != (0 : Int32))
  if !sc'3 then
    let t'2 ← PMem.ldI32 (this + 12)
    sc'3 := (t'2 != (0 : Int32))
  let mut sc'5 := sc'3
  if !sc'5 then
    let t'4 ← PMem.ldI32 (this + 4)
    sc'5 := (t'4 != (0 : Int32))
  return sc'5

/-- C++ `Location::get_alt_cm : bool (AltFrame, int32_t &) const`, `Location.cpp:148-253`. -/
def Location.get_alt_cm.body (fp : UInt64) (this : UInt64) (desired_frame : Int32) (ret_alt_cm : UInt64) : PMem.M Bool := do
  let mut desired_frame := desired_frame
  let t'1 ← Location.initialised this
  if !t'1 then
    pure ()
  let t'2 ← PMem.ldBits this 2 1
  let mut sc'4 := (UInt64.toUInt8 (t'2)) != (0 : UInt8)
  if sc'4 then
    let t'3 ← PMem.ldBits this 0 1
    sc'4 := !((UInt64.toUInt8 (t'3)) != (0 : UInt8))
  if sc'4 then
    pure ()
  let t'5 ← Location.get_alt_frame this
  let mut frame : Int32 := t'5
  if (desired_frame == frame) then
    let t'6 ← PMem.ldI32 (this + 4)
    PMem.stI32 ret_alt_cm t'6
    return true
  let mut alt_terr_cm : Binary32 := Int32.toBinary32 ((0 : Int32))
  if ((frame == (3 : Int32)) || (desired_frame == (3 : Int32))) then
    return false
  let mut alt_abs : Int32 := (0 : Int32)
  let sw'7 := frame
  if sw'7 == (0 : Int32) then
    let t'8 ← PMem.ldI32 (this + 4)
    alt_abs := t'8
  else if sw'7 == (1 : Int32) then
    let t'9 ← VehicleBridge.ahrs'0
    let t'10 ← VehicleBridge.AP_AHRS.home_is_set'0 t'9
    if !t'10 then
      return false
    let t'11 ← PMem.ldI32 (this + 4)
    let t'12 ← VehicleBridge.ahrs'0
    VehicleBridge.AP_AHRS.get_home'0 t'12 (fp + 0)
    let t'13 := (fp + 0)
    let t'14 ← PMem.ldI32 (t'13 + 4)
    let t'15 := (t'11 + t'14)
    alt_abs := t'15
  else if sw'7 == (2 : Int32) then
    Location.Location (fp + 16)
    let t'16 ← VehicleBridge.ahrs'0
    let t'17 ← VehicleBridge.AP_AHRS.get_origin'1 t'16 (fp + 16)
    if !t'17 then
      return false
    let t'18 ← PMem.ldI32 (this + 4)
    let t'19 ← PMem.ldI32 ((fp + 16) + 4)
    let t'20 := (t'18 + t'19)
    alt_abs := t'20
  else if sw'7 == (3 : Int32) then
    let t'21 ← PMem.ldI32 (this + 4)
    let t'22 := Binary32.toInt32 (((Int32.toBinary32 (t'21)) + alt_terr_cm))
    alt_abs := t'22
  else
    pure ()
  let sw'23 := desired_frame
  if sw'23 == (0 : Int32) then
    PMem.stI32 ret_alt_cm alt_abs
    return true
  else if sw'23 == (1 : Int32) then
    let t'24 ← VehicleBridge.ahrs'0
    let t'25 ← VehicleBridge.AP_AHRS.home_is_set'0 t'24
    if !t'25 then
      return false
    let t'26 ← VehicleBridge.ahrs'0
    VehicleBridge.AP_AHRS.get_home'0 t'26 (fp + 32)
    let t'27 := (fp + 32)
    let t'28 ← PMem.ldI32 (t'27 + 4)
    let t'29 := (alt_abs - t'28)
    PMem.stI32 ret_alt_cm t'29
    return true
  else if sw'23 == (2 : Int32) then
    Location.Location (fp + 48)
    let t'30 ← VehicleBridge.ahrs'0
    let t'31 ← VehicleBridge.AP_AHRS.get_origin'1 t'30 (fp + 48)
    if !t'31 then
      return false
    let t'32 ← PMem.ldI32 ((fp + 48) + 4)
    let t'33 := (alt_abs - t'32)
    PMem.stI32 ret_alt_cm t'33
    return true
    let t'34 := Binary32.toInt32 (((Int32.toBinary32 (alt_abs)) - alt_terr_cm))
    PMem.stI32 ret_alt_cm t'34
    return true
  else if sw'23 == (3 : Int32) then
    let t'35 := Binary32.toInt32 (((Int32.toBinary32 (alt_abs)) - alt_terr_cm))
    PMem.stI32 ret_alt_cm t'35
    return true
  else
    pure ()
  return false

def Location.get_alt_cm (this : UInt64) (desired_frame : Int32) (ret_alt_cm : UInt64) : PMem.M Bool := do
  let fp ← PMem.enter 64
  let r ← Location.get_alt_cm.body fp this desired_frame ret_alt_cm
  PMem.leave fp
  return r

/-- `Location.diff_longitude` as a pure function of its arguments (it reads and writes no memory). -/
def Location.diff_longitude.pure' (lon1 : Int32) (lon2 : Int32) : Id Int32 := do
  let mut lon1 := lon1
  let mut lon2 := lon2
  if (((Int32.toUInt32 (lon1)) &&& (2147483648 : UInt32)) == ((Int32.toUInt32 (lon2)) &&& (2147483648 : UInt32))) then
    return (lon1 - lon2)
  let mut dlon : Int64 := ((Int32.toInt64 (lon1)) - (Int32.toInt64 (lon2)))
  if (decide (dlon > (1800000000 : Int64))) then
    let t'1 := (dlon - (3600000000 : Int64))
    dlon := t'1
  else
    if (decide (dlon < (-(1800000000 : Int64)))) then
      let t'2 := (dlon + (3600000000 : Int64))
      dlon := t'2
  return Int64.toInt32 (dlon)

/-- C++ `Location::diff_longitude : int32_t (int32_t, int32_t)`, `Location.cpp:650-663`. -/
def Location.diff_longitude (lon1 : Int32) (lon2 : Int32) : PMem.M Int32 :=
  pure (_root_.Vehicle_lib.Location.diff_longitude.pure' lon1 lon2)

/-- C++ `Location::longitude_scale : ftype (int32_t)`, `Location.cpp:528-532`. -/
def Location.longitude_scale.body (fp : UInt64) (lat : Int32) : PMem.M Binary64 := do
  let mut lat := lat
  PMem.stF64 (fp + 0) (Binary32.toBinary64 ((Musl.cosf.cosf ((Int32.toBinary32 (lat)) * ((Binary64.toBinary32 ((Binary64.ofBits 0x3e7ad7f29abcaf48 /- 19999999999999999/200000000000000000000000 -/))) * ((Binary64.toBinary32 ((Binary64.ofBits 0x400921fb54442d18 /- 31415926535897931/10000000000000000 -/))) / (Binary32.ofBits 0x43340000 /- 180 -/)))))))
  PMem.stF32 (fp + 8) (Binary64.toBinary32 ((Binary64.ofBits 0x3f847ae147ae147b /- 1/100 -/)))
  let t'1 ← MAX'double_float (fp + 0) (fp + 8)
  return t'1

def Location.longitude_scale (lat : Int32) : PMem.M Binary64 := do
  let fp ← PMem.enter 12
  let r ← Location.longitude_scale.body fp lat
  PMem.leave fp
  return r

/-- C++ `Location::get_vector_xy_from_origin_NE_cm : bool (Vector2<double> &) const`, `Location.cpp:269-278`. -/
def Location.get_vector_xy_from_origin_NE_cm'Vector2_double.body (fp : UInt64) (this : UInt64) (vec_ne : UInt64) : PMem.M Bool := do
  Location.Location (fp + 0)
  let t'1 ← VehicleBridge.ahrs'0
  let t'2 ← VehicleBridge.AP_AHRS.get_origin'1 t'1 (fp + 0)
  if !t'2 then
    return false
  let t'3 ← PMem.ldI32 (this + 8)
  let t'4 ← PMem.ldI32 ((fp + 0) + 8)
  let t'5 := ((Int32.toBinary64 ((t'3 - t'4))) * (Binary64.ofBits 0x3ff1cf9eb13f4ca9 /- 11131884502145033/10000000000000000 -/))
  PMem.stF64 vec_ne t'5
  let t'6 ← PMem.ldI32 (this + 12)
  let t'7 ← PMem.ldI32 ((fp + 0) + 12)
  let t'8 ← Location.diff_longitude t'6 t'7
  let t'9 ← PMem.ldI32 (this + 8)
  let t'10 ← PMem.ldI32 ((fp + 0) + 8)
  let t'11 ← Location.longitude_scale ((t'9 + t'10) / (2 : Int32))
  let t'12 := (((Int32.toBinary64 (t'8)) * (Binary64.ofBits 0x3ff1cf9eb13f4ca9 /- 11131884502145033/10000000000000000 -/)) * t'11)
  PMem.stF64 (vec_ne + 8) t'12
  return true

def Location.get_vector_xy_from_origin_NE_cm'Vector2_double (this : UInt64) (vec_ne : UInt64) : PMem.M Bool := do
  let fp ← PMem.enter 16
  let r ← Location.get_vector_xy_from_origin_NE_cm'Vector2_double.body fp this vec_ne
  PMem.leave fp
  return r

/-- C++ `Location::get_vector_from_origin_NEU_cm : bool (Vector3<double> &) const`, `Location.cpp:289-305`. -/
def Location.get_vector_from_origin_NEU_cm'Vector3_double.body (fp : UInt64) (this : UInt64) (vec_neu : UInt64) : PMem.M Bool := do
  PMem.stI32 (fp + 0) (0 : Int32)
  let t'1 ← Location.get_alt_cm this (2 : Int32) (fp + 0)
  if !t'1 then
    return false
  let t'2 ← Vector3'double.xy vec_neu
  let t'3 ← Location.get_vector_xy_from_origin_NE_cm'Vector2_double this t'2
  if !t'3 then
    return false
  let t'4 ← PMem.ldI32 (fp + 0)
  let t'5 := Int32.toBinary64 (t'4)
  PMem.stF64 (vec_neu + 16) t'5
  return true

def Location.get_vector_from_origin_NEU_cm'Vector3_double (this : UInt64) (vec_neu : UInt64) : PMem.M Bool := do
  let fp ← PMem.enter 4
  let r ← Location.get_vector_from_origin_NEU_cm'Vector3_double.body fp this vec_neu
  PMem.leave fp
  return r

/-- C++ `Location::get_vector_from_origin_NED_m : bool (Vector3<double> &) const`, `Location.cpp:335-343`. -/
def Location.get_vector_from_origin_NED_m'Vector3_double (this : UInt64) (vec_ned : UInt64) : PMem.M Bool := do
  let t'1 ← Location.get_vector_from_origin_NEU_cm'Vector3_double this vec_ned
  if !t'1 then
    return false
  let t'2 ← Vector3'double.operator__'2 vec_ned (Binary64.ofBits 0x3f847ae147ae147b /- 1/100 -/)
  discard <| pure (t'2)
  let t'3 := (vec_ned + 16)
  let t'4 ← PMem.ldF64 t'3
  let t'5 := (t'4 * (-(Binary64.ofBits 0x3ff0000000000000 /- 1 -/)))
  PMem.stF64 t'3 t'5
  return true

/-- C++ `Location::get_alt_m : bool (AltFrame, float &) const`, `Location.cpp:255-263`. -/
def Location.get_alt_m.body (fp : UInt64) (this : UInt64) (desired_frame : Int32) (ret_alt : UInt64) : PMem.M Bool := do
  let mut desired_frame := desired_frame
  let t'1 ← Location.get_alt_cm this desired_frame (fp + 0)
  if !t'1 then
    return false
  let t'2 ← PMem.ldI32 (fp + 0)
  let t'3 := ((Int32.toBinary32 (t'2)) * (Binary64.toBinary32 ((Binary64.ofBits 0x3f847ae147ae147b /- 1/100 -/))))
  PMem.stF32 ret_alt t'3
  return true

def Location.get_alt_m (this : UInt64) (desired_frame : Int32) (ret_alt : UInt64) : PMem.M Bool := do
  let fp ← PMem.enter 4
  let r ← Location.get_alt_m.body fp this desired_frame ret_alt
  PMem.leave fp
  return r

/-- C++ `Location::get_vector_xy_from_origin_NE_m : bool (Vector2<double> &) const`, `Location.cpp:321-328`. -/
def Location.get_vector_xy_from_origin_NE_m'Vector2_double (this : UInt64) (vec_ne : UInt64) : PMem.M Bool := do
  let t'1 ← Location.get_vector_xy_from_origin_NE_cm'Vector2_double this vec_ne
  if !t'1 then
    return false
  let t'2 ← Vector2'double.operator__'3 vec_ne (Binary64.ofBits 0x3f847ae147ae147b /- 1/100 -/)
  discard <| pure (t'2)
  return true

/-- C++ `AP_FWVersion::get_fwverz : const AP_FWVersion &()`, `AP_FWVersion.h:40-?`. -/
def AP_FWVersion.get_fwverz  : PMem.M UInt64 := do
  return (0xca68 : UInt64) /- &fwver -/

/-- C++ `AP::fwversion : const AP_FWVersion &()`, `AP_FWVersion.cpp:5-8`. -/
def AP.fwversion  : PMem.M UInt64 := do
  let t'1 ← AP_FWVersion.get_fwverz
  return t'1

/-- `Bitmask'102.validate` as a pure function of its arguments (it reads and writes no memory). -/
def Bitmask'102.validate.pure' (this : UInt64) (bit : UInt16) : Id Bool := do
  let mut bit := bit
  if (decide ((UInt32.toInt32 (UInt16.toUInt32 (bit))) ≥ (UInt32.toInt32 (UInt16.toUInt32 ((102 : UInt16)))))) then
    return false
  return true

/-- C++ `Bitmask<102>::validate : bool (uint16_t) const`, `stdint.h:160-166`. -/
def Bitmask'102.validate (this : UInt64) (bit : UInt16) : PMem.M Bool :=
  pure (_root_.Vehicle_lib.Bitmask'102.validate.pure' this bit)

/-- C++ `Bitmask<102>::set : void (uint16_t)`, `stdint.h:69-76`. -/
def Bitmask'102.set (this : UInt64) (bit : UInt16) : PMem.M Unit := do
  let mut bit := bit
  let t'1 ← Bitmask'102.validate this bit
  if !t'1 then
    return ()
  let mut word : UInt16 := Int16.toUInt16 (Int32.toInt16 (((UInt32.toInt32 (UInt16.toUInt32 (bit))) / (32 : Int32))))
  let mut ofs : UInt8 := Int8.toUInt8 (Int32.toInt8 (((UInt32.toInt32 (UInt16.toUInt32 (bit))) &&& (31 : Int32))))
  let t'2 := (this + ((UInt64.toInt64 (UInt16.toUInt64 (word))) * 4).toUInt64)
  let t'3 ← PMem.ldU32 t'2
  let t'4 := (t'3 ||| ((1 : UInt32) <<< (Int32.toUInt32 ((UInt32.toInt32 (UInt8.toUInt32 (ofs)))))))
  PMem.stU32 t'2 t'4
  return ()

/-- C++ `strncpy_noterm : size_t (char *, const char *, size_t)`, `AP_Common.cpp:124-134`. -/
def strncpy_noterm (dest : UInt64) (src : UInt64) (n : UInt64) : PMem.M UInt64 := do
  let mut dest := dest
  let mut src := src
  let mut n := n
  let t'1 ← PMem.strnlen src n
  let mut len : UInt64 := t'1
  let mut ret : UInt64 := len
  if (decide (len < n)) then
    let t'2 := len
    let t'3 := (t'2 + 1)
    len := t'3
  let t'4 ← PMem.memcpy dest src len
  discard <| pure (t'4)
  return ret

/-- C++ `ObjectBuffer<GCS_MAVLINK::pending_param_request>::space : uint32_t () const`, `AP_Common.h:163-165`. -/
def ObjectBuffer'GCS_MAVLINK_pending_param_request.space (this : UInt64) : PMem.M UInt32 := do
  let t'1 ← PMem.ldU64 this
  let t'2 ← ByteBuffer.space t'1
  return UInt64.toUInt32 (((UInt32.toUInt64 (t'2)) / (32 : UInt64)))

/-- C++ `ObjectBuffer<GCS_MAVLINK::pending_param_request>::push : bool (const GCS_MAVLINK::pending_param_request &)`, `AP_Common.h:175-180`. -/
def ObjectBuffer'GCS_MAVLINK_pending_param_request.push (this : UInt64) (object : UInt64) : PMem.M Bool := do
  let t'1 ← PMem.ldU64 this
  let t'2 ← ByteBuffer.space t'1
  if (decide ((UInt32.toUInt64 (t'2)) < (32 : UInt64))) then
    return false
  let t'3 ← PMem.ldU64 this
  let t'4 ← ByteBuffer.write t'3 object (UInt64.toUInt32 ((32 : UInt64)))
  return ((UInt32.toUInt64 (t'4)) == (32 : UInt64))

/-- C++ `Location::Location : void (Location &&) noexcept`, `definitions.h:?-?`. -/
def Location.Location'2 (this : UInt64) (arg : UInt64) : PMem.M Unit := do
  let t'1 ← PMem.ldBits arg 0 1
  PMem.stBits this 0 1 (UInt8.toUInt64 ((UInt64.toUInt8 (t'1))))
  let t'2 ← PMem.ldBits arg 1 1
  PMem.stBits this 1 1 (UInt8.toUInt64 ((UInt64.toUInt8 (t'2))))
  let t'3 ← PMem.ldBits arg 2 1
  PMem.stBits this 2 1 (UInt8.toUInt64 ((UInt64.toUInt8 (t'3))))
  let t'4 ← PMem.ldBits arg 3 1
  PMem.stBits this 3 1 (UInt8.toUInt64 ((UInt64.toUInt8 (t'4))))
  let t'5 ← PMem.ldBits arg 4 1
  PMem.stBits this 4 1 (UInt8.toUInt64 ((UInt64.toUInt8 (t'5))))
  let t'6 ← PMem.ldI32 (arg + 4)
  PMem.stI32 (this + 4) t'6
  let t'7 ← PMem.ldI32 (arg + 8)
  PMem.stI32 (this + 8) t'7
  let t'8 ← PMem.ldI32 (arg + 12)
  PMem.stI32 (this + 12) t'8
  return ()

/-- `Location.limit_lattitude` as a pure function of its arguments (it reads and writes no memory). -/
def Location.limit_lattitude.pure' (lat : Int32) : Id Int32 := do
  let mut lat := lat
  if (decide ((Int32.toInt64 (lat)) > (900000000 : Int64))) then
    let t'1 := Int64.toInt32 (((1800000000 : Int64) - (Int32.toInt64 (lat))))
    lat := t'1
  else
    if (decide ((Int32.toInt64 (lat)) < (-(900000000 : Int64)))) then
      let t'2 := Int64.toInt32 ((-((1800000000 : Int64) + (Int32.toInt64 (lat)))))
      lat := t'2
  return lat

/-- C++ `Location::limit_lattitude : int32_t (int32_t)`, `Location.cpp:668-676`. -/
def Location.limit_lattitude (lat : Int32) : PMem.M Int32 :=
  pure (_root_.Vehicle_lib.Location.limit_lattitude.pure' lat)

/-- `Location.wrap_longitude` as a pure function of its arguments (it reads and writes no memory). -/
def Location.wrap_longitude.pure' (lon : Int64) : Id Int32 := do
  let mut lon := lon
  if (decide (lon > (1800000000 : Int64))) then
    let t'1 := Int32.toInt64 ((Int64.toInt32 ((lon - (3600000000 : Int64)))))
    lon := t'1
  else
    if (decide (lon < (-(1800000000 : Int64)))) then
      let t'2 := Int32.toInt64 ((Int64.toInt32 ((lon + (3600000000 : Int64)))))
      lon := t'2
  return Int64.toInt32 (lon)

/-- C++ `Location::wrap_longitude : int32_t (int64_t)`, `Location.cpp:637-645`. -/
def Location.wrap_longitude (lon : Int64) : PMem.M Int32 :=
  pure (_root_.Vehicle_lib.Location.wrap_longitude.pure' lon)

/-- C++ `Location::offset_latlng : void (int32_t &, int32_t &, ftype, ftype)`, `Location.cpp:480-487`. -/
def Location.offset_latlng (lat : UInt64) (lng : UInt64) (ofs_north : Binary64) (ofs_east : Binary64) : PMem.M Unit := do
  let mut ofs_north := ofs_north
  let mut ofs_east := ofs_east
  let mut dlat : Int32 := Binary64.toInt32 ((ofs_north * (Binary32.toBinary64 ((Binary32.ofBits 0x42b3aa02 /- 6321368512591417/70368744177664 -/)))))
  let t'1 ← PMem.ldI32 lat
  let t'2 ← Location.longitude_scale (t'1 + (dlat / (2 : Int32)))
  let mut dlng : Int64 := Binary64.toInt64 (((ofs_east * (Binary32.toBinary64 ((Binary32.ofBits 0x42b3aa02 /- 6321368512591417/70368744177664 -/)))) / t'2))
  let t'3 ← PMem.ldI32 lat
  let t'4 := (t'3 + dlat)
  PMem.stI32 lat t'4
  let t'5 ← PMem.ldI32 lat
  let t'6 ← Location.limit_lattitude t'5
  PMem.stI32 lat t'6
  let t'7 ← PMem.ldI32 lng
  let t'8 ← Location.wrap_longitude (dlng + (Int32.toInt64 (t'7)))
  PMem.stI32 lng t'8
  return ()

/-- C++ `Location::offset : void (ftype, ftype)`, `Location.cpp:490-493`. -/
def Location.offset (this : UInt64) (ofs_north : Binary64) (ofs_east : Binary64) : PMem.M Unit := do
  let mut ofs_north := ofs_north
  let mut ofs_east := ofs_east
  Location.offset_latlng (this + 8) (this + 12) ofs_north ofs_east
  return ()

/-- C++ `Location::Location : void (const Vector3d &, AltFrame)`, `Location.cpp:52-66`. -/
def Location.Location'4.body (fp : UInt64) (this : UInt64) (ekf_offset_neu_cm : UInt64) (frame : Int32) : PMem.M Unit := do
  let mut frame := frame
  Location.zero this
  let t'1 ← PMem.ldF64 (ekf_offset_neu_cm + 16)
  Location.set_alt_cm this (Binary64.toInt32 (t'1)) frame
  Location.Location (fp + 0)
  let t'2 ← VehicleBridge.ahrs'0
  let t'3 ← VehicleBridge.AP_AHRS.get_origin'1 t'2 (fp + 0)
  if t'3 then
    let t'4 ← PMem.ldI32 ((fp + 0) + 8)
    PMem.stI32 (this + 8) t'4
    let t'5 ← PMem.ldI32 ((fp + 0) + 12)
    PMem.stI32 (this + 12) t'5
    let t'6 ← PMem.ldF64 ekf_offset_neu_cm
    let t'7 ← PMem.ldF64 (ekf_offset_neu_cm + 8)
    Location.offset this (t'6 * (Binary64.ofBits 0x3f847ae147ae147b /- 1/100 -/)) (t'7 * (Binary64.ofBits 0x3f847ae147ae147b /- 1/100 -/))
  return ()

def Location.Location'4 (this : UInt64) (ekf_offset_neu_cm : UInt64) (frame : Int32) : PMem.M Unit := do
  let fp ← PMem.enter 16
  let r ← Location.Location'4.body fp this ekf_offset_neu_cm frame
  PMem.leave fp
  return r

/-- C++ `Location::from_ekf_offset_NED_m : Location (const Vector3d &, AltFrame)`, `Location.cpp:75-79`. -/
def Location.from_ekf_offset_NED_m.body (fp : UInt64) (sret : UInt64) (ekf_offset_ned_m : UInt64) (frame : Int32) : PMem.M Unit := do
  let mut frame := frame
  let t'1 ← PMem.ldF64 ekf_offset_ned_m
  let t'2 ← PMem.ldF64 (ekf_offset_ned_m + 8)
  let t'3 ← PMem.ldF64 (ekf_offset_ned_m + 16)
  Vector3'double.Vector3'3 (fp + 0) (t'1 * (Binary64.ofBits 0x4059000000000000 /- 100 -/)) (t'2 * (Binary64.ofBits 0x4059000000000000 /- 100 -/)) ((-t'3) * (Binary64.ofBits 0x4059000000000000 /- 100 -/))
  Location.Location'4 (fp + 24) (fp + 0) frame
  Location.Location'2 sret (fp + 24)
  return ()

def Location.from_ekf_offset_NED_m (sret : UInt64) (ekf_offset_ned_m : UInt64) (frame : Int32) : PMem.M Unit := do
  let fp ← PMem.enter 40
  let r ← Location.from_ekf_offset_NED_m.body fp sret ekf_offset_ned_m frame
  PMem.leave fp
  return r

/-- `_assert_storage_size'PackedContent_12_12._assert_storage_size` as a pure function of its arguments (it reads and writes no memory). -/
def _assert_storage_size'PackedContent_12_12._assert_storage_size.pure' (this : UInt64) : Id Unit := do
  return ()

/-- C++ `_assert_storage_size<PackedContent, 12, 12>::_assert_storage_size : void () noexcept`, `AP_Common.h:180-?`. -/
def _assert_storage_size'PackedContent_12_12._assert_storage_size (this : UInt64) : PMem.M Unit :=
  pure (_root_.Vehicle_lib._assert_storage_size'PackedContent_12_12._assert_storage_size.pure' this)

/-- `assert_storage_size'PackedContent_12.assert_storage_size` as a pure function of its arguments (it reads and writes no memory). -/
def assert_storage_size'PackedContent_12.assert_storage_size.pure' (this : UInt64) : Id Unit := do
  _root_.Vehicle_lib._assert_storage_size'PackedContent_12_12._assert_storage_size.pure' (this + 0)
  return ()

/-- C++ `assert_storage_size<PackedContent, 12>::assert_storage_size : void () noexcept`, `AP_Common.h:183-?`. -/
def assert_storage_size'PackedContent_12.assert_storage_size (this : UInt64) : PMem.M Unit :=
  pure (_root_.Vehicle_lib.assert_storage_size'PackedContent_12.assert_storage_size.pure' this)

/-- C++ `Location::get_distance_NED_alt_frame : Vector3f (const Location &) const`, `Location.cpp:449-459`. -/
def Location.get_distance_NED_alt_frame.body (fp : UInt64) (this : UInt64) (sret : UInt64) (loc2 : UInt64) : PMem.M Unit := do
  PMem.stI32 (fp + 8) (0 : Int32)
  let t'1 ← Location.get_alt_cm this (0 : Int32) (fp + 0)
  let mut sc'3 := !t'1
  if !sc'3 then
    let t'2 ← Location.get_alt_cm loc2 (0 : Int32) (fp + 8)
    sc'3 := !t'2
  if sc'3 then
    PMem.stI32 (fp + 0) (0 : Int32)
    PMem.stI32 (fp + 8) (0 : Int32)
  let t'4 ← PMem.ldI32 (loc2 + 8)
  let t'5 ← PMem.ldI32 (this + 8)
  let t'6 ← PMem.ldI32 (loc2 + 12)
  let t'7 ← PMem.ldI32 (this + 12)
  let t'8 ← Location.diff_longitude t'6 t'7
  let t'9 ← PMem.ldI32 (loc2 + 8)
  let t'10 ← PMem.ldI32 (this + 8)
  let t'11 ← Location.longitude_scale ((t'9 + t'10) / (2 : Int32))
  let t'12 ← PMem.ldI32 (fp + 0)
  let t'13 ← PMem.ldI32 (fp + 8)
  Vector3'float.Vector3 (fp + 16) ((Int32.toBinary32 ((t'4 - t'5))) * (Binary32.ofBits 0x3c366282 /- 6417094514661347/576460752303423488 -/)) (Binary64.toBinary32 (((Binary32.toBinary64 (((Int32.toBinary32 (t'8)) * (Binary32.ofBits 0x3c366282 /- 6417094514661347/576460752303423488 -/)))) * t'11))) ((Int32.toBinary32 ((t'12 - t'13))) * (Binary64.toBinary32 ((Binary64.ofBits 0x3f847ae147ae147b /- 1/100 -/))))
  Vector3'float.Vector3'3 sret (fp + 16)
  return ()

def Location.get_distance_NED_alt_frame (this : UInt64) (sret : UInt64) (loc2 : UInt64) : PMem.M Unit := do
  let fp ← PMem.enter 28
  let r ← Location.get_distance_NED_alt_frame.body fp this sret loc2
  PMem.leave fp
  return r

/-- C++ `Location::get_distance : ftype (const Location &) const`, `Location.cpp:369-374`. -/
def Location.get_distance (this : UInt64) (loc2 : UInt64) : PMem.M Binary64 := do
  let t'1 ← PMem.ldI32 (loc2 + 8)
  let t'2 ← PMem.ldI32 (this + 8)
  let mut dlat : Binary64 := Int32.toBinary64 ((t'1 - t'2))
  let t'3 ← PMem.ldI32 (loc2 + 12)
  let t'4 ← PMem.ldI32 (this + 12)
  let t'5 ← Location.diff_longitude t'3 t'4
  let t'6 ← PMem.ldI32 (this + 8)
  let t'7 ← PMem.ldI32 (loc2 + 8)
  let t'8 ← Location.longitude_scale ((t'6 + t'7) / (2 : Int32))
  let mut dlng : Binary64 := ((Int32.toBinary64 (t'5)) * t'8)
  let t'9 ← norm'double_double dlat dlng
  return (t'9 * (Binary32.toBinary64 ((Binary32.ofBits 0x3c366282 /- 6417094514661347/576460752303423488 -/))))

/-- `atan2'int_int_0` as a pure function of its arguments (it reads and writes no memory). -/
def atan2'int_int_0.pure' (__y : Int32) (__x : Int32) : Id Binary64 := do
  let mut __y := __y
  let mut __x := __x
  return (Musl.atan2.atan2 (Int32.toBinary64 (__y)) (Int32.toBinary64 (__x)))

/-- C++ `atan2 : typename __promote<int, int>::type (int, int) noexcept`, `__config:?-93`. -/
def atan2'int_int_0 (__y : Int32) (__x : Int32) : PMem.M Binary64 :=
  pure (_root_.Vehicle_lib.atan2'int_int_0.pure' __y __x)

/-- C++ `Location::get_bearing : ftype (const Location &) const`, `Location.cpp:567-576`. -/
def Location.get_bearing (this : UInt64) (loc2 : UInt64) : PMem.M Binary64 := do
  let t'1 ← PMem.ldI32 (loc2 + 12)
  let t'2 ← PMem.ldI32 (this + 12)
  let t'3 ← Location.diff_longitude t'1 t'2
  let mut off_x : Int32 := t'3
  let t'4 ← PMem.ldI32 (loc2 + 8)
  let t'5 ← PMem.ldI32 (this + 8)
  let t'6 ← PMem.ldI32 (this + 8)
  let t'7 ← PMem.ldI32 (loc2 + 8)
  let t'8 ← Location.longitude_scale ((t'6 + t'7) / (2 : Int32))
  let mut off_y : Int32 := Binary64.toInt32 (((Int32.toBinary64 ((t'4 - t'5))) / t'8))
  let t'9 ← atan2'int_int_0 (-off_y) off_x
  let mut bearing : Binary64 := ((Binary32.toBinary64 (((Binary64.toBinary32 ((Binary64.ofBits 0x400921fb54442d18 /- 31415926535897931/10000000000000000 -/))) * (Binary64.toBinary32 ((Binary64.ofBits 0x3fe0000000000000 /- 1/2 -/)))))) + t'9)
  if (decide (bearing < (Int32.toBinary64 ((0 : Int32))))) then
    let t'10 := (bearing + (Binary32.toBinary64 (((Int32.toBinary32 ((2 : Int32))) * (Binary64.toBinary32 ((Binary64.ofBits 0x400921fb54442d18 /- 31415926535897931/10000000000000000 -/)))))))
    bearing := t'10
  return bearing

/-- C++ `RCMapper::get_singleton : RCMapper *()`, `AP_Common.h:19-22`. -/
def RCMapper.get_singleton  : PMem.M UInt64 := do
  let t'1 ← PMem.ldU64 (0x12ee8 : UInt64) /- &RCMapper::_singleton -/
  return t'1

/-- C++ `RCMapper::throttle : uint8_t () const`, `AP_Common.h:31-?`. -/
def RCMapper.throttle (this : UInt64) : PMem.M UInt8 := do
  let t'1 ← AP_ParamT'signed_char_1.operator_const_signed_char__ (this + 3)
  let t'2 ← PMem.ldI8 t'1
  return Int8.toUInt8 (t'2)

/-- C++ `Bitmask<190>::clearall : void ()`, `stdint.h:111-113`. -/
def Bitmask'190.clearall (this : UInt64) : PMem.M Unit := do
  let t'1 ← PMem.memset this (0 : Int32) ((UInt16.toUInt64 ((6 : UInt16))) * (4 : UInt64))
  discard <| pure (t'1)
  return ()

/-- `Bitmask'190.validate` as a pure function of its arguments (it reads and writes no memory). -/
def Bitmask'190.validate.pure' (this : UInt64) (bit : UInt16) : Id Bool := do
  let mut bit := bit
  if (decide ((UInt32.toInt32 (UInt16.toUInt32 (bit))) ≥ (UInt32.toInt32 (UInt16.toUInt32 ((190 : UInt16)))))) then
    return false
  return true

/-- C++ `Bitmask<190>::validate : bool (uint16_t) const`, `stdint.h:160-166`. -/
def Bitmask'190.validate (this : UInt64) (bit : UInt16) : PMem.M Bool :=
  pure (_root_.Vehicle_lib.Bitmask'190.validate.pure' this bit)

/-- C++ `Bitmask<190>::set : void (uint16_t)`, `stdint.h:69-76`. -/
def Bitmask'190.set (this : UInt64) (bit : UInt16) : PMem.M Unit := do
  let mut bit := bit
  let t'1 ← Bitmask'190.validate this bit
  if !t'1 then
    return ()
  let mut word : UInt16 := Int16.toUInt16 (Int32.toInt16 (((UInt32.toInt32 (UInt16.toUInt32 (bit))) / (32 : Int32))))
  let mut ofs : UInt8 := Int8.toUInt8 (Int32.toInt8 (((UInt32.toInt32 (UInt16.toUInt32 (bit))) &&& (31 : Int32))))
  let t'2 := (this + ((UInt64.toInt64 (UInt16.toUInt64 (word))) * 4).toUInt64)
  let t'3 ← PMem.ldU32 t'2
  let t'4 := (t'3 ||| ((1 : UInt32) <<< (Int32.toUInt32 ((UInt32.toInt32 (UInt8.toUInt32 (ofs)))))))
  PMem.stU32 t'2 t'4
  return ()

/-- C++ `Bitmask<190>::get : bool (uint16_t) const`, `stdint.h:116-123`. -/
def Bitmask'190.get (this : UInt64) (bit : UInt16) : PMem.M Bool := do
  let mut bit := bit
  let t'1 ← Bitmask'190.validate this bit
  if !t'1 then
    return false
  let mut word : UInt16 := Int16.toUInt16 (Int32.toInt16 (((UInt32.toInt32 (UInt16.toUInt32 (bit))) / (32 : Int32))))
  let mut ofs : UInt8 := Int8.toUInt8 (Int32.toInt8 (((UInt32.toInt32 (UInt16.toUInt32 (bit))) &&& (31 : Int32))))
  let t'2 ← PMem.ldU32 (this + ((UInt64.toInt64 (UInt16.toUInt64 (word))) * 4).toUInt64)
  return ((t'2 &&& ((1 : UInt32) <<< (Int32.toUInt32 ((UInt32.toInt32 (UInt8.toUInt32 (ofs))))))) != (Int32.toUInt32 ((0 : Int32))))

/-- C++ `Bitmask<317>::clearall : void ()`, `stdint.h:111-113`. -/
def Bitmask'317.clearall (this : UInt64) : PMem.M Unit := do
  let t'1 ← PMem.memset this (0 : Int32) ((UInt16.toUInt64 ((10 : UInt16))) * (4 : UInt64))
  discard <| pure (t'1)
  return ()

/-- C++ `Bitmask<317>::Bitmask : void ()`, `stdint.h:37-39`. -/
def Bitmask'317.Bitmask (this : UInt64) : PMem.M Unit := do
  Bitmask'317.clearall this
  return ()

/-- `Bitmask'317.size` as a pure function of its arguments (it reads and writes no memory). -/
def Bitmask'317.size.pure' (this : UInt64) : Id UInt16 := do
  return (317 : UInt16)

/-- C++ `Bitmask<317>::size : uint16_t () const`, `stdint.h:155-157`. -/
def Bitmask'317.size (this : UInt64) : PMem.M UInt16 :=
  pure (_root_.Vehicle_lib.Bitmask'317.size.pure' this)

/-- `Bitmask'317.validate` as a pure function of its arguments (it reads and writes no memory). -/
def Bitmask'317.validate.pure' (this : UInt64) (bit : UInt16) : Id Bool := do
  let mut bit := bit
  if (decide ((UInt32.toInt32 (UInt16.toUInt32 (bit))) ≥ (UInt32.toInt32 (UInt16.toUInt32 ((317 : UInt16)))))) then
    return false
  return true

/-- C++ `Bitmask<317>::validate : bool (uint16_t) const`, `stdint.h:160-166`. -/
def Bitmask'317.validate (this : UInt64) (bit : UInt16) : PMem.M Bool :=
  pure (_root_.Vehicle_lib.Bitmask'317.validate.pure' this bit)

/-- C++ `Bitmask<317>::get : bool (uint16_t) const`, `stdint.h:116-123`. -/
def Bitmask'317.get (this : UInt64) (bit : UInt16) : PMem.M Bool := do
  let mut bit := bit
  let t'1 ← Bitmask'317.validate this bit
  if !t'1 then
    return false
  let mut word : UInt16 := Int16.toUInt16 (Int32.toInt16 (((UInt32.toInt32 (UInt16.toUInt32 (bit))) / (32 : Int32))))
  let mut ofs : UInt8 := Int8.toUInt8 (Int32.toInt8 (((UInt32.toInt32 (UInt16.toUInt32 (bit))) &&& (31 : Int32))))
  let t'2 ← PMem.ldU32 (this + ((UInt64.toInt64 (UInt16.toUInt64 (word))) * 4).toUInt64)
  return ((t'2 &&& ((1 : UInt32) <<< (Int32.toUInt32 ((UInt32.toInt32 (UInt8.toUInt32 (ofs))))))) != (Int32.toUInt32 ((0 : Int32))))

/-- C++ `Bitmask<317>::set : void (uint16_t)`, `stdint.h:69-76`. -/
def Bitmask'317.set (this : UInt64) (bit : UInt16) : PMem.M Unit := do
  let mut bit := bit
  let t'1 ← Bitmask'317.validate this bit
  if !t'1 then
    return ()
  let mut word : UInt16 := Int16.toUInt16 (Int32.toInt16 (((UInt32.toInt32 (UInt16.toUInt32 (bit))) / (32 : Int32))))
  let mut ofs : UInt8 := Int8.toUInt8 (Int32.toInt8 (((UInt32.toInt32 (UInt16.toUInt32 (bit))) &&& (31 : Int32))))
  let t'2 := (this + ((UInt64.toInt64 (UInt16.toUInt64 (word))) * 4).toUInt64)
  let t'3 ← PMem.ldU32 t'2
  let t'4 := (t'3 ||| ((1 : UInt32) <<< (Int32.toUInt32 ((UInt32.toInt32 (UInt8.toUInt32 (ofs)))))))
  PMem.stU32 t'2 t'4
  return ()

/-- `AP_CANManager.get_num_drivers` as a pure function of its arguments (it reads and writes no memory). -/
def AP_CANManager.get_num_drivers.pure' (this : UInt64) : Id UInt8 := do
  return Int8.toUInt8 (Int32.toInt8 ((2 : Int32)))

/-- C++ `AP_CANManager::get_num_drivers : uint8_t () const`, `AP_Common.h:67-70`. -/
def AP_CANManager.get_num_drivers (this : UInt64) : PMem.M UInt8 :=
  pure (_root_.Vehicle_lib.AP_CANManager.get_num_drivers.pure' this)

/-- C++ `AP_CANManager::get_singleton : AP_CANManager *()`, `AP_Common.h:42-48`. -/
def AP_CANManager.get_singleton  : PMem.M UInt64 := do
  let t'1 ← PMem.ldU64 (0x134b8 : UInt64) /- &AP_CANManager::_singleton -/
  if (t'1 == (0 : UInt64)) then
    pure ()
  let t'2 ← PMem.ldU64 (0x134b8 : UInt64) /- &AP_CANManager::_singleton -/
  return t'2

/-- C++ `AP_CANManager::get_driver_type : AP_CAN::Protocol (uint8_t) const`, `AP_Common.h:88-94`. -/
def AP_CANManager.get_driver_type (this : UInt64) (i : UInt8) : PMem.M UInt8 := do
  let mut i := i
  if (decide ((UInt8.toUInt64 (i)) < ((2 : UInt64) / (1 : UInt64)))) then
    let t'1 ← PMem.ldU8 ((this + 96) + ((UInt64.toInt64 (UInt8.toUInt64 (i))) * 1).toUInt64)
    return t'1
  return (0 : UInt8)

/-- C++ `RCMapper::roll : uint8_t () const`, `AP_Common.h:25-?`. -/
def RCMapper.roll (this : UInt64) : PMem.M UInt8 := do
  let t'1 ← AP_ParamT'signed_char_1.operator_const_signed_char__ this
  let t'2 ← PMem.ldI8 t'1
  return Int8.toUInt8 (t'2)

/-- C++ `RCMapper::pitch : uint8_t () const`, `AP_Common.h:28-?`. -/
def RCMapper.pitch (this : UInt64) : PMem.M UInt8 := do
  let t'1 ← AP_ParamT'signed_char_1.operator_const_signed_char__ (this + 1)
  let t'2 ← PMem.ldI8 t'1
  return Int8.toUInt8 (t'2)

/-- C++ `RCMapper::yaw : uint8_t () const`, `AP_Common.h:34-?`. -/
def RCMapper.yaw (this : UInt64) : PMem.M UInt8 := do
  let t'1 ← AP_ParamT'signed_char_1.operator_const_signed_char__ (this + 2)
  let t'2 ← PMem.ldI8 t'1
  return Int8.toUInt8 (t'2)

/-- C++ `Location::offset : void (const Vector3p &)`, `Location.cpp:497-501`. -/
def Location.offset'2 (this : UInt64) (ofs_ned : UInt64) : PMem.M Unit := do
  let t'1 ← PMem.ldF64 ofs_ned
  let t'2 ← PMem.ldF64 (ofs_ned + 8)
  Location.offset_latlng (this + 8) (this + 12) t'1 t'2
  let t'3 := (this + 4)
  let t'4 ← PMem.ldI32 t'3
  let t'5 ← PMem.ldF64 (ofs_ned + 16)
  let t'6 := (t'4 + (Binary64.toInt32 (((-t'5) * (Int32.toBinary64 ((100 : Int32)))))))
  PMem.stI32 t'3 t'6
  return ()

/-- C++ `Location::set_alt_m : void (float, AltFrame)`, `Location.h:43-45`. -/
def Location.set_alt_m (this : UInt64) (alt_m : Binary32) (frame : Int32) : PMem.M Unit := do
  let mut alt_m := alt_m
  let mut frame := frame
  Location.set_alt_cm this (Binary32.toInt32 ((alt_m * (Int32.toBinary32 ((100 : Int32)))))) frame
  return ()

/-- C++ `Location::get_vector_xy_from_origin_NE_cm : bool (Vector2<float> &) const`, `Location.cpp:269-278`. -/
def Location.get_vector_xy_from_origin_NE_cm'Vector2_float.body (fp : UInt64) (this : UInt64) (vec_ne : UInt64) : PMem.M Bool := do
  Location.Location (fp + 0)
  let t'1 ← VehicleBridge.ahrs'0
  let t'2 ← VehicleBridge.AP_AHRS.get_origin'1 t'1 (fp + 0)
  if !t'2 then
    return false
  let t'3 ← PMem.ldI32 (this + 8)
  let t'4 ← PMem.ldI32 ((fp + 0) + 8)
  let t'5 := Binary64.toBinary32 (((Int32.toBinary64 ((t'3 - t'4))) * (Binary64.ofBits 0x3ff1cf9eb13f4ca9 /- 11131884502145033/10000000000000000 -/)))
  PMem.stF32 vec_ne t'5
  let t'6 ← PMem.ldI32 (this + 12)
  let t'7 ← PMem.ldI32 ((fp + 0) + 12)
  let t'8 ← Location.diff_longitude t'6 t'7
  let t'9 ← PMem.ldI32 (this + 8)
  let t'10 ← PMem.ldI32 ((fp + 0) + 8)
  let t'11 ← Location.longitude_scale ((t'9 + t'10) / (2 : Int32))
  let t'12 := Binary64.toBinary32 ((((Int32.toBinary64 (t'8)) * (Binary64.ofBits 0x3ff1cf9eb13f4ca9 /- 11131884502145033/10000000000000000 -/)) * t'11))
  PMem.stF32 (vec_ne + 4) t'12
  return true

def Location.get_vector_xy_from_origin_NE_cm'Vector2_float (this : UInt64) (vec_ne : UInt64) : PMem.M Bool := do
  let fp ← PMem.enter 16
  let r ← Location.get_vector_xy_from_origin_NE_cm'Vector2_float.body fp this vec_ne
  PMem.leave fp
  return r

/-- C++ `Location::get_vector_from_origin_NEU_cm : bool (Vector3<float> &) const`, `Location.cpp:289-305`. -/
def Location.get_vector_from_origin_NEU_cm'Vector3_float.body (fp : UInt64) (this : UInt64) (vec_neu : UInt64) : PMem.M Bool := do
  PMem.stI32 (fp + 0) (0 : Int32)
  let t'1 ← Location.get_alt_cm this (2 : Int32) (fp + 0)
  if !t'1 then
    return false
  let t'2 ← Vector3'float.xy vec_neu
  let t'3 ← Location.get_vector_xy_from_origin_NE_cm'Vector2_float this t'2
  if !t'3 then
    return false
  let t'4 ← PMem.ldI32 (fp + 0)
  let t'5 := Int32.toBinary32 (t'4)
  PMem.stF32 (vec_neu + 8) t'5
  return true

def Location.get_vector_from_origin_NEU_cm'Vector3_float (this : UInt64) (vec_neu : UInt64) : PMem.M Bool := do
  let fp ← PMem.enter 4
  let r ← Location.get_vector_from_origin_NEU_cm'Vector3_float.body fp this vec_neu
  PMem.leave fp
  return r

/-- C++ `Location::get_vector_from_origin_NED_m : bool (Vector3<float> &) const`, `Location.cpp:335-343`. -/
def Location.get_vector_from_origin_NED_m'Vector3_float (this : UInt64) (vec_ned : UInt64) : PMem.M Bool := do
  let t'1 ← Location.get_vector_from_origin_NEU_cm'Vector3_float this vec_ned
  if !t'1 then
    return false
  let t'2 ← Vector3'float.operator__'2 vec_ned (Binary64.toBinary32 ((Binary64.ofBits 0x3f847ae147ae147b /- 1/100 -/)))
  discard <| pure (t'2)
  let t'3 := (vec_ned + 8)
  let t'4 ← PMem.ldF32 t'3
  let t'5 := (t'4 * (Binary64.toBinary32 ((-(Binary64.ofBits 0x3ff0000000000000 /- 1 -/)))))
  PMem.stF32 t'3 t'5
  return true

/-- C++ `Location::get_distance_NED : Vector3f (const Location &) const`, `Location.cpp:426-431`. -/
def Location.get_distance_NED.body (fp : UInt64) (this : UInt64) (sret : UInt64) (loc2 : UInt64) : PMem.M Unit := do
  let t'1 ← PMem.ldI32 (loc2 + 8)
  let t'2 ← PMem.ldI32 (this + 8)
  let t'3 ← PMem.ldI32 (loc2 + 12)
  let t'4 ← PMem.ldI32 (this + 12)
  let t'5 ← Location.diff_longitude t'3 t'4
  let t'6 ← PMem.ldI32 (this + 8)
  let t'7 ← PMem.ldI32 (loc2 + 8)
  let t'8 ← Location.longitude_scale ((t'6 + t'7) / (2 : Int32))
  let t'9 ← PMem.ldI32 (this + 4)
  let t'10 ← PMem.ldI32 (loc2 + 4)
  Vector3'float.Vector3 (fp + 0) ((Int32.toBinary32 ((t'1 - t'2))) * (Binary32.ofBits 0x3c366282 /- 6417094514661347/576460752303423488 -/)) (Binary64.toBinary32 (((Binary32.toBinary64 (((Int32.toBinary32 (t'5)) * (Binary32.ofBits 0x3c366282 /- 6417094514661347/576460752303423488 -/)))) * t'8))) ((Int32.toBinary32 ((t'9 - t'10))) * (Binary64.toBinary32 ((Binary64.ofBits 0x3f847ae147ae147b /- 1/100 -/))))
  Vector3'float.Vector3'3 sret (fp + 0)
  return ()

def Location.get_distance_NED (this : UInt64) (sret : UInt64) (loc2 : UInt64) : PMem.M Unit := do
  let fp ← PMem.enter 12
  let r ← Location.get_distance_NED.body fp this sret loc2
  PMem.leave fp
  return r

/-- C++ `Location::offset_up_m : void (float)`, `AP_Common.h:131-133`. -/
def Location.offset_up_m (this : UInt64) (alt_offset_m : Binary32) : PMem.M Unit := do
  let mut alt_offset_m := alt_offset_m
  let t'1 := (this + 4)
  let t'2 ← PMem.ldI32 t'1
  let t'3 := (t'2 + (Binary32.toInt32 ((alt_offset_m * (Int32.toBinary32 ((100 : Int32)))))))
  PMem.stI32 t'1 t'3
  return ()

/-- C++ `Location::check_latlng : bool () const`, `Location.cpp:601-604`. -/
def Location.check_latlng (this : UInt64) : PMem.M Bool := do
  let t'1 ← PMem.ldI32 (this + 8)
  let t'2 ← check_lat t'1
  let mut sc'5 := t'2
  if sc'5 then
    let t'3 ← PMem.ldI32 (this + 12)
    let t'4 ← check_lng t'3
    sc'5 := t'4
  return sc'5

/-- C++ `Location::sanitize : bool (const Location &)`, `Location.cpp:537-564`. -/
def Location.sanitize.body (fp : UInt64) (this : UInt64) (defaultLoc : UInt64) : PMem.M Bool := do
  let mut has_changed : Bool := false
  let t'1 ← PMem.ldI32 (this + 8)
  let mut sc'3 := (t'1 == (0 : Int32))
  if sc'3 then
    let t'2 ← PMem.ldI32 (this + 12)
    sc'3 := (t'2 == (0 : Int32))
  if sc'3 then
    let t'4 ← PMem.ldI32 (defaultLoc + 8)
    PMem.stI32 (this + 8) t'4
    let t'5 ← PMem.ldI32 (defaultLoc + 12)
    PMem.stI32 (this + 12) t'5
    has_changed := true
  let t'6 ← PMem.ldI32 (this + 4)
  let mut sc'8 := (t'6 == (0 : Int32))
  if sc'8 then
    let t'7 ← PMem.ldBits this 0 1
    sc'8 := (UInt64.toUInt8 (t'7)) != (0 : UInt8)
  if sc'8 then
    let t'9 ← Location.get_alt_frame this
    let t'10 ← Location.get_alt_cm defaultLoc t'9 (fp + 0)
    if t'10 then
      let t'11 ← PMem.ldI32 (fp + 0)
      PMem.stI32 (this + 4) t'11
      has_changed := true
  let t'12 ← Location.check_latlng this
  if !t'12 then
    let t'13 ← PMem.ldI32 (defaultLoc + 8)
    PMem.stI32 (this + 8) t'13
    let t'14 ← PMem.ldI32 (defaultLoc + 12)
    PMem.stI32 (this + 12) t'14
    has_changed := true
  return has_changed

def Location.sanitize (this : UInt64) (defaultLoc : UInt64) : PMem.M Bool := do
  let fp ← PMem.enter 4
  let r ← Location.sanitize.body fp this defaultLoc
  PMem.leave fp
  return r

/-- C++ `ObjectBuffer<GCS_MAVLINK::pending_param_reply>::peek : bool (GCS_MAVLINK::pending_param_reply &)`, `AP_Common.h:239-241`. -/
def ObjectBuffer'GCS_MAVLINK_pending_param_reply.peek (this : UInt64) (object : UInt64) : PMem.M Bool := do
  let t'1 ← PMem.ldU64 this
  let t'2 ← ByteBuffer.peekbytes t'1 object (UInt64.toUInt32 ((48 : UInt64)))
  return ((UInt32.toUInt64 (t'2)) == (48 : UInt64))

/-- C++ `ObjectBuffer<GCS_MAVLINK::pending_param_reply>::pop : bool ()`, `AP_Common.h:195-197`. -/
def ObjectBuffer'GCS_MAVLINK_pending_param_reply.pop (this : UInt64) : PMem.M Bool := do
  let t'1 ← PMem.ldU64 this
  let t'2 ← ByteBuffer.advance t'1 (UInt64.toUInt32 ((48 : UInt64)))
  return t'2

/-- `SITL.SIM.simstate_send` as a pure function of its arguments (it reads and writes no memory). -/
def SITL.SIM.simstate_send.pure' (this : UInt64) (chan : UInt32) : Id Unit := do
  let mut chan := chan
  return ()

/-- C++ `SITL::SIM::simstate_send : void (mavlink_channel_t) const`, `AP_Common.h:85-?`. -/
def SITL.SIM.simstate_send (this : UInt64) (chan : UInt32) : PMem.M Unit :=
  pure (_root_.Vehicle_lib.SITL.SIM.simstate_send.pure' this chan)

/-- `SITL.SIM.sim_state_send` as a pure function of its arguments (it reads and writes no memory). -/
def SITL.SIM.sim_state_send.pure' (this : UInt64) (chan : UInt32) : Id Unit := do
  let mut chan := chan
  return ()

/-- C++ `SITL::SIM::sim_state_send : void (mavlink_channel_t) const`, `AP_Common.h:86-?`. -/
def SITL.SIM.sim_state_send (this : UInt64) (chan : UInt32) : PMem.M Unit :=
  pure (_root_.Vehicle_lib.SITL.SIM.sim_state_send.pure' this chan)

/-- C++ `Bitmask<102>::count : uint16_t () const`, `stdint.h:136-142`. -/
def Bitmask'102.count (this : UInt64) : PMem.M UInt16 := do
  let mut sum : UInt16 := Int16.toUInt16 (Int32.toInt16 ((0 : Int32)))
  let mut i : UInt16 := Int16.toUInt16 (Int32.toInt16 ((0 : Int32)))
  let mut first'1 := true
  for _ in PMem.loopFuel do
    if !first'1 then
      let t'2 := i
      let t'3 := (t'2 + 1)
      i := t'3
      pure ()
    first'1 := false
    if !((decide ((UInt32.toInt32 (UInt16.toUInt32 (i))) < (UInt32.toInt32 (UInt16.toUInt32 ((4 : UInt16))))))) then break
    let t'4 ← PMem.ldU32 (this + ((UInt64.toInt64 (UInt16.toUInt64 (i))) * 4).toUInt64)
    let t'5 ← PMem.popcount t'4
    let t'6 := (sum + (Int16.toUInt16 (Int32.toInt16 (t'5))))
    sum := t'6
  return sum

/-- C++ `Bitmask<102>::get : bool (uint16_t) const`, `stdint.h:116-123`. -/
def Bitmask'102.get (this : UInt64) (bit : UInt16) : PMem.M Bool := do
  let mut bit := bit
  let t'1 ← Bitmask'102.validate this bit
  if !t'1 then
    return false
  let mut word : UInt16 := Int16.toUInt16 (Int32.toInt16 (((UInt32.toInt32 (UInt16.toUInt32 (bit))) / (32 : Int32))))
  let mut ofs : UInt8 := Int8.toUInt8 (Int32.toInt8 (((UInt32.toInt32 (UInt16.toUInt32 (bit))) &&& (31 : Int32))))
  let t'2 ← PMem.ldU32 (this + ((UInt64.toInt64 (UInt16.toUInt64 (word))) * 4).toUInt64)
  return ((t'2 &&& ((1 : UInt32) <<< (Int32.toUInt32 ((UInt32.toInt32 (UInt8.toUInt32 (ofs))))))) != (Int32.toUInt32 ((0 : Int32))))

/-- C++ `Bitmask<102>::clear : void (uint16_t)`, `stdint.h:92-99`. -/
def Bitmask'102.clear (this : UInt64) (bit : UInt16) : PMem.M Unit := do
  let mut bit := bit
  let t'1 ← Bitmask'102.validate this bit
  if !t'1 then
    return ()
  let mut word : UInt16 := Int16.toUInt16 (Int32.toInt16 (((UInt32.toInt32 (UInt16.toUInt32 (bit))) / (32 : Int32))))
  let mut ofs : UInt8 := Int8.toUInt8 (Int32.toInt8 (((UInt32.toInt32 (UInt16.toUInt32 (bit))) &&& (31 : Int32))))
  let t'2 := (this + ((UInt64.toInt64 (UInt16.toUInt64 (word))) * 4).toUInt64)
  let t'3 ← PMem.ldU32 t'2
  let t'4 := (t'3 &&& (~~~((1 : UInt32) <<< (Int32.toUInt32 ((UInt32.toInt32 (UInt8.toUInt32 (ofs))))))))
  PMem.stU32 t'2 t'4
  return ()

/-- C++ `Bitmask<102>::clearall : void ()`, `stdint.h:111-113`. -/
def Bitmask'102.clearall (this : UInt64) : PMem.M Unit := do
  let t'1 ← PMem.memset this (0 : Int32) ((UInt16.toUInt64 ((4 : UInt16))) * (4 : UInt64))
  discard <| pure (t'1)
  return ()

/-- C++ `Bitmask<102>::first_set : int16_t () const`, `stdint.h:145-152`. -/
def Bitmask'102.first_set (this : UInt64) : PMem.M Int16 := do
  let mut i : UInt16 := Int16.toUInt16 (Int32.toInt16 ((0 : Int32)))
  let mut first'1 := true
  for _ in PMem.loopFuel do
    if !first'1 then
      let t'2 := i
      let t'3 := (t'2 + 1)
      i := t'3
      pure ()
    first'1 := false
    if !((decide ((UInt32.toInt32 (UInt16.toUInt32 (i))) < (UInt32.toInt32 (UInt16.toUInt32 ((4 : UInt16))))))) then break
    let t'4 ← PMem.ldU32 (this + ((UInt64.toInt64 (UInt16.toUInt64 (i))) * 4).toUInt64)
    if (t'4 != (Int32.toUInt32 ((0 : Int32)))) then
      let t'5 ← PMem.ldU32 (this + ((UInt64.toInt64 (UInt16.toUInt64 (i))) * 4).toUInt64)
      let t'6 ← PMem.ffs (UInt32.toInt32 (t'5))
      return Int32.toInt16 (((((UInt32.toInt32 (UInt16.toUInt32 (i))) * (32 : Int32)) + t'6) - (1 : Int32)))
  return Int32.toInt16 ((-(1 : Int32)))

/-- C++ `Bitmask<102>::Bitmask : void ()`, `stdint.h:37-39`. -/
def Bitmask'102.Bitmask (this : UInt64) : PMem.M Unit := do
  Bitmask'102.clearall this
  return ()

/-- C++ `ObjectBuffer<GCS_MAVLINK::pending_param_reply>::space : uint32_t () const`, `AP_Common.h:163-165`. -/
def ObjectBuffer'GCS_MAVLINK_pending_param_reply.space (this : UInt64) : PMem.M UInt32 := do
  let t'1 ← PMem.ldU64 this
  let t'2 ← ByteBuffer.space t'1
  return UInt64.toUInt32 (((UInt32.toUInt64 (t'2)) / (48 : UInt64)))

/-- C++ `ObjectBuffer<GCS_MAVLINK::pending_param_request>::pop : bool (GCS_MAVLINK::pending_param_request &)`, `AP_Common.h:203-208`. -/
def ObjectBuffer'GCS_MAVLINK_pending_param_request.pop (this : UInt64) (object : UInt64) : PMem.M Bool := do
  let t'1 ← PMem.ldU64 this
  let t'2 ← ByteBuffer.available t'1
  if (decide ((UInt32.toUInt64 (t'2)) < (32 : UInt64))) then
    return false
  let t'3 ← PMem.ldU64 this
  let t'4 ← ByteBuffer.read t'3 object (UInt64.toUInt32 ((32 : UInt64)))
  return ((UInt32.toUInt64 (t'4)) == (32 : UInt64))

/-- C++ `ObjectBuffer<GCS_MAVLINK::pending_param_reply>::push : bool (const GCS_MAVLINK::pending_param_reply &)`, `AP_Common.h:175-180`. -/
def ObjectBuffer'GCS_MAVLINK_pending_param_reply.push (this : UInt64) (object : UInt64) : PMem.M Bool := do
  let t'1 ← PMem.ldU64 this
  let t'2 ← ByteBuffer.space t'1
  if (decide ((UInt32.toUInt64 (t'2)) < (48 : UInt64))) then
    return false
  let t'3 ← PMem.ldU64 this
  let t'4 ← ByteBuffer.write t'3 object (UInt64.toUInt32 ((48 : UInt64)))
  return ((UInt32.toUInt64 (t'4)) == (48 : UInt64))

/-- C++ `ObjectBuffer_TS<AP_Param::param_save>::available : uint32_t ()`, `AP_Common.h:330-333`. -/
def ObjectBuffer_TS'AP_Param_param_save.available (this : UInt64) : PMem.M UInt32 := do
  let t'1 ← PMem.ldU64 this
  let t'2 ← ByteBuffer.available t'1
  return UInt64.toUInt32 (((UInt32.toUInt64 (t'2)) / (9 : UInt64)))

/-- C++ `ObjectBuffer<GCS_MAVLINK::pending_param_request>::ObjectBuffer : void (uint32_t)`, `AP_Common.h:114-121`. -/
def ObjectBuffer'GCS_MAVLINK_pending_param_request.ObjectBuffer (this : UInt64) (_size : UInt32) : PMem.M Unit := do
  let mut _size := _size
  PMem.stU64 (this + 0) (0 : UInt64)
  PMem.stB (this + 8) true
  let t'1 ← PMem.alloc 24
  ByteBuffer.ByteBuffer t'1 (UInt64.toUInt32 (((UInt32.toUInt64 ((_size + (Int32.toUInt32 ((1 : Int32)))))) * (32 : UInt64))))
  PMem.stU64 this t'1
  PMem.stB (this + 8) false
  return ()

/-- C++ `ObjectBuffer<GCS_MAVLINK::pending_param_reply>::ObjectBuffer : void (uint32_t)`, `AP_Common.h:114-121`. -/
def ObjectBuffer'GCS_MAVLINK_pending_param_reply.ObjectBuffer (this : UInt64) (_size : UInt32) : PMem.M Unit := do
  let mut _size := _size
  PMem.stU64 (this + 0) (0 : UInt64)
  PMem.stB (this + 8) true
  let t'1 ← PMem.alloc 24
  ByteBuffer.ByteBuffer t'1 (UInt64.toUInt32 (((UInt32.toUInt64 ((_size + (Int32.toUInt32 ((1 : Int32)))))) * (48 : UInt64))))
  PMem.stU64 this t'1
  PMem.stB (this + 8) false
  return ()

/-- `is_bounded_int32` as a pure function of its arguments (it reads and writes no memory). -/
def is_bounded_int32.pure' (value : Int32) (lower_bound : Int32) (upper_bound : Int32) : Id Bool := do
  let mut value := value
  let mut lower_bound := lower_bound
  let mut upper_bound := upper_bound
  if (((decide (lower_bound ≤ upper_bound)) && (decide (value ≥ lower_bound))) && (decide (value ≤ upper_bound))) then
    return true
  return false

/-- C++ `is_bounded_int32 : bool (int32_t, int32_t, int32_t)`, `AP_Common.cpp:32-41`. -/
def is_bounded_int32 (value : Int32) (lower_bound : Int32) (upper_bound : Int32) : PMem.M Bool :=
  pure (_root_.Vehicle_lib.is_bounded_int32.pure' value lower_bound upper_bound)

/-- C++ `Location::change_alt_frame : bool (AltFrame)`, `Location.cpp:109-117`. -/
def Location.change_alt_frame.body (fp : UInt64) (this : UInt64) (desired_frame : Int32) : PMem.M Bool := do
  let mut desired_frame := desired_frame
  let t'1 ← Location.get_alt_cm this desired_frame (fp + 0)
  if !t'1 then
    return false
  let t'2 ← PMem.ldI32 (fp + 0)
  Location.set_alt_cm this t'2 desired_frame
  return true

def Location.change_alt_frame (this : UInt64) (desired_frame : Int32) : PMem.M Bool := do
  let fp ← PMem.enter 4
  let r ← Location.change_alt_frame.body fp this desired_frame
  PMem.leave fp
  return r

/-- C++ `Location::get_height_above : bool (const Location &, ftype &) const`, `Location.cpp:389-413`. -/
def Location.get_height_above.body (fp : UInt64) (this : UInt64) (loc2 : UInt64) (distance : UInt64) : PMem.M Bool := do
  let t'1 ← Location.get_alt_frame this
  let t'2 ← Location.get_alt_frame loc2
  if (t'1 == t'2) then
    let t'3 ← Location.get_alt_frame this
    let sw'4 := t'3
    if sw'4 == (0 : Int32) || sw'4 == (1 : Int32) || sw'4 == (2 : Int32) then
      let t'5 ← PMem.ldI32 (this + 4)
      let t'6 ← PMem.ldI32 (loc2 + 4)
      let t'7 := Binary32.toBinary64 (((Int32.toBinary32 ((t'5 - t'6))) * (Binary64.toBinary32 ((Binary64.ofBits 0x3f847ae147ae147b /- 1/100 -/)))))
      PMem.stF64 distance t'7
      return true
    else if sw'4 == (3 : Int32) then
      pure ()
    else
      pure ()
  let t'8 ← Location.get_alt_cm this (0 : Int32) (fp + 0)
  let mut sc'10 := !t'8
  if !sc'10 then
    let t'9 ← Location.get_alt_cm loc2 (0 : Int32) (fp + 8)
    sc'10 := !t'9
  if sc'10 then
    return false
  let t'11 ← PMem.ldI32 (fp + 0)
  let t'12 ← PMem.ldI32 (fp + 8)
  let t'13 := Binary32.toBinary64 (((Int32.toBinary32 ((t'11 - t'12))) * (Binary64.toBinary32 ((Binary64.ofBits 0x3f847ae147ae147b /- 1/100 -/)))))
  PMem.stF64 distance t'13
  return true

def Location.get_height_above (this : UInt64) (loc2 : UInt64) (distance : UInt64) : PMem.M Bool := do
  let fp ← PMem.enter 12
  let r ← Location.get_height_above.body fp this loc2 distance
  PMem.leave fp
  return r

/-- C++ `Location::copy_alt_from : void (const Location &)`, `Location.cpp:119-125`. -/
def Location.copy_alt_from (this : UInt64) (other : UInt64) : PMem.M Unit := do
  let t'1 ← PMem.ldI32 (other + 4)
  PMem.stI32 (this + 4) t'1
  let t'2 ← PMem.ldBits other 0 1
  let t'3 := UInt64.toUInt8 (t'2)
  PMem.stBits this 0 1 (UInt8.toUInt64 (t'3))
  let t'4 ← PMem.ldBits other 2 1
  let t'5 := UInt64.toUInt8 (t'4)
  PMem.stBits this 2 1 (UInt8.toUInt64 (t'5))
  let t'6 ← PMem.ldBits other 3 1
  let t'7 := UInt64.toUInt8 (t'6)
  PMem.stBits this 3 1 (UInt8.toUInt64 (t'7))
  return ()

/-- C++ `ObjectBuffer_TS<AP_Param::param_save>::pop : bool (AP_Param::param_save &)`, `<scratch space>:382-388`. -/
def ObjectBuffer_TS'AP_Param_param_save.pop (this : UInt64) (object : UInt64) : PMem.M Bool := do
  let t'1 ← PMem.ldU64 this
  let t'2 ← ByteBuffer.available t'1
  if (decide ((UInt32.toUInt64 (t'2)) < (9 : UInt64))) then
    return false
  let t'3 ← PMem.ldU64 this
  let t'4 ← ByteBuffer.read t'3 object (UInt64.toUInt32 ((9 : UInt64)))
  return ((UInt32.toUInt64 (t'4)) == (9 : UInt64))

/-- `AP_HAL.HAL.Callbacks.Callbacks` as a pure function of its arguments (it reads and writes no memory). -/
def AP_HAL.HAL.Callbacks.Callbacks.pure' (this : UInt64) : Id Unit := do
  return ()

/-- C++ `AP_HAL::HAL::Callbacks::Callbacks : void () noexcept`, `HAL.h:?-?`. -/
def AP_HAL.HAL.Callbacks.Callbacks (this : UInt64) : PMem.M Unit :=
  pure (_root_.Vehicle_lib.AP_HAL.HAL.Callbacks.Callbacks.pure' this)

/-- C++ `AP_CANManager::CANIface_Params::CANIface_Params : void ()`, `AP_Common.h:106-109`. -/
def AP_CANManager.CANIface_Params.CANIface_Params (this : UInt64) : PMem.M Unit := do
  AP_Param.AP_Param'2 (this + 0)
  AP_Param.AP_Param'2 (this + 4)
  AP_Param.AP_Param'2 (this + 8)
  AP_Param.AP_Param'2 (this + 12)
  AP_Param.setup_object_defaults this (0x6820 : UInt64) /- &AP_CANManager::CANIface_Params::var_info -/
  return ()

/-- C++ `AP_CANManager::CANDriver_Params::CANDriver_Params : void ()`, `AP_Common.h:138-141`. -/
def AP_CANManager.CANDriver_Params.CANDriver_Params (this : UInt64) : PMem.M Unit := do
  AP_Param.AP_Param'2 (this + 0)
  AP_Param.AP_Param'2 (this + 1)
  AP_Param.setup_object_defaults this (0x68f0 : UInt64) /- &AP_CANManager::CANDriver_Params::var_info -/
  return ()

/-- `AP_ExternalControl_Copter.AP_ExternalControl_Copter` as a pure function of its arguments (it reads and writes no memory). -/
def AP_ExternalControl_Copter.AP_ExternalControl_Copter.pure' (this : UInt64) : Id Unit := do
  return ()

/-- C++ `AP_ExternalControl_Copter::AP_ExternalControl_Copter : void () noexcept(false)`, `AP_Common.h:?-?`. -/
def AP_ExternalControl_Copter.AP_ExternalControl_Copter (this : UInt64) : PMem.M Unit :=
  pure (_root_.Vehicle_lib.AP_ExternalControl_Copter.AP_ExternalControl_Copter.pure' this)

/-- C++ `ObjectArray<GCS::statustext_t>::ObjectArray : void (uint16_t)`, `AP_Common.h:472-476`. -/
def ObjectArray'GCS_statustext_t.ObjectArray (this : UInt64) (size_ : UInt16) : PMem.M Unit := do
  let mut size_ := size_
  PMem.stU16 (this + 8) size_
  let t'1 := Int16.toUInt16 (Int32.toInt16 ((0 : Int32)))
  PMem.stU16 (this + 10) t'1
  let t'2 ← PMem.ldU16 (this + 10)
  PMem.stU16 (this + 12) t'2
  let t'3 ← PMem.ldU16 (this + 8)
  let t'4 ← PMem.alloc ((UInt16.toUInt64 (t'3)).toNat * 64)
  PMem.stU64 this t'4
  return ()

/-- C++ `ObjectBuffer_TS<AP_Param::param_save>::ObjectBuffer_TS : void (uint32_t)`, `sitl.h:286-292`. -/
def ObjectBuffer_TS'AP_Param_param_save.ObjectBuffer_TS (this : UInt64) (_size : UInt32) : PMem.M Unit := do
  let mut _size := _size
  PMem.stU64 (this + 0) (0 : UInt64)
  HALSITL.Semaphore.Semaphore (this + 8)
  let t'1 ← PMem.alloc 24
  ByteBuffer.ByteBuffer t'1 (UInt64.toUInt32 (((UInt32.toUInt64 ((_size + (Int32.toUInt32 ((1 : Int32)))))) * (9 : UInt64))))
  PMem.stU64 this t'1
  return ()

end Vehicle_lib
