import ArduLean.Runtime.CFloat
import ArduLean.Estimator.libraries.AP_Math.AP_Math
import ArduLean.Estimator.World
import ArduLean.Estimator.libraries.AP_Common.AP_Common
import ArduLean.Estimator.libraries.AP_Declination.AP_Declination
import ArduLean.Estimator.libraries.AP_Param.AP_Param
import ArduLean.Estimator.libraries.AP_Compass.AP_Compass
import ArduLean.Estimator.libraries.AP_AHRS.AP_AHRS
import ArduLean.Estimator.World_2
import ArduLean.Estimator.libraries.AP_Common.AP_Common_2
import ArduLean.Estimator.libraries.AP_Param.AP_Param_2
import ArduLean.Estimator.libraries.AP_Compass.AP_Compass_2
import ArduLean.Estimator.World_3
import ArduLean.Estimator.libraries.AP_Compass.AP_Compass_3
import ArduLean.Estimator.libraries.AP_AHRS.AP_AHRS_2
import ArduLean.Estimator.World_4
import ArduLean.Estimator.libraries.AP_AHRS.AP_AHRS_3

/-!
ArduPilot `libraries/AP_Compass`, part 4 of 4. Sources: `libraries/AP_Compass/AP_Compass.cpp`.

Items of `lean/Estimator_lib.lean` (the estimator translation), unchanged; placed by `tools/split_modules.py` (`ArduLean/Estimator/INDEX.md`).
-/

open FloatLib.Floats (Binary32 Binary64)

set_option maxRecDepth 200000
-- AP_DAL's `const log_RISH old_RISH = _RISH;` read only by WRITE_REPLAY_BLOCK_IFCHANGED, which is `(void)old`
-- without logging (HAL_LOGGING_ENABLED 0): an unused binding, as in the C++
set_option linter.unusedVariables false

namespace Estimator_lib

namespace Compass

/-- C++ `void Compass::try_set_initial_location()`, `AP_Compass/AP_Compass.cpp:1937-1959`. -/
def try_set_initial_location (s : State) (w : World) : State := Id.run do
  let mut s := s
  if !(AP_ParamT_signed_char_1.op_to_signed_char s._auto_declination != (0 : Int8)) then
    return s
  if !(AP_ParamT_signed_char_1.op_to_signed_char s._enabled != (0 : Int8)) then
    return s
  let mut loc : Location.State := Location.init_void
  let (t'1, t'2) := AP_AHRS.get_location w.ahrs loc
  loc := t'1
  if !t'2 then
    return s
  s := { s with _initial_location_set := true }
  s := { s with _declination := AP_ParamT_float_4.set s._declination (Estimator_lib.radians_float (AP_Declination.get_declination (Int32.toBinary32 loc.lat / (Binary32.ofBits 0x4b189680 /- 10000000 -/)) (Int32.toBinary32 loc.lng / (Binary32.ofBits 0x4b189680 /- 10000000 -/)))) }
  return s

/-- C++ `bool Compass::healthy() const`, `AP_Compass/AP_Compass.h:200`. -/
def healthy_void (s : State) : Bool := Id.run do
  return healthy_uint8_t s s._first_usable

end Compass

namespace Compass

/-- C++ `bool Compass::read()`, `AP_Compass/AP_Compass.cpp:1756-1822`. -/
def read (s : State) (w : World) : State × World × Bool := Id.run do
  let mut s := s
  let mut w := w
  if !(available s) then
    return (s, w, false)
  if !s._initial_location_set then
    s := try_set_initial_location s w
  pure ()  -- C++ `_detect_runtime`: no effect in the model
  let t'1 : UInt8 := Int8.toUInt8 (Int32.toInt8 (0 : Int32))
  let t'2 : Int32 := UInt32.toInt32 (UInt8.toUInt32 s._backend_count)
  for i' in [0:(t'2.toInt - (Int.ofNat t'1.toNat)).toNat] do  -- C++ loop bounded by a runtime value (--runtime-loops)
    let i : UInt8 := t'1 + Nat.toUInt8 i'
    let t'3 := (WPtr.index s._backends[UInt8.toNat i]!)
    w := { w with compass := s }  -- this object's state into the World: the call reaches it
    w := AP_Compass_SITL.read w.heap'AP_Compass_SITL[t'3]! w
    s := w.compass  -- this object's state as the call left it
  let time : UInt32 := Estimator_lib.millis w
  let mut any_healthy : Bool := false
  let mut i'2 : typesafe_index_unsigned_char_TAG_StateIndex.State := typesafe_index_unsigned_char_TAG_StateIndex.init (Int8.toUInt8 (Int32.toInt8 (0 : Int32)))
  for _ in [0:2^64] do  -- C loop without a constant trip count (--general-loops)
    if !(typesafe_index_unsigned_char_TAG_StateIndex.op_lt i'2 (Int8.toUInt8 (Int32.toInt8 (3 : Int32)))) then break
    let t'5 := time
    let t'4 := i'2
    let t'6 := i'2
    s := { s with _state._priv_instance := s._state._priv_instance.set! (UInt8.toNat (typesafe_index_unsigned_char_TAG_StateIndex.get_int t'6)) ({ s._state._priv_instance[UInt8.toNat (typesafe_index_unsigned_char_TAG_StateIndex.get_int t'6)]! with healthy := (decide (t'5 - s._state._priv_instance[UInt8.toNat (typesafe_index_unsigned_char_TAG_StateIndex.get_int t'4)]!.last_update_ms < Int32.toUInt32 (500 : Int32))) }) }
    let t'7 := i'2
    any_healthy := (if any_healthy then (1 : Int32) else (0 : Int32)) ||| (if s._state._priv_instance[UInt8.toNat (typesafe_index_unsigned_char_TAG_StateIndex.get_int t'7)]!.healthy then (1 : Int32) else (0 : Int32)) != (0 : Int32)
    let (t'8, _) := typesafe_index_unsigned_char_TAG_StateIndex.op_inc_int32_t i'2 (0 : Int32)
    i'2 := t'8
  let mut i'3 : typesafe_index_unsigned_char_TAG_Priority.State := typesafe_index_unsigned_char_TAG_Priority.init (Int8.toUInt8 (Int32.toInt8 (0 : Int32)))
  for _ in [0:2^64] do  -- C loop without a constant trip count (--general-loops)
    if !(typesafe_index_unsigned_char_TAG_Priority.op_lt i'3 (Int8.toUInt8 (Int32.toInt8 (3 : Int32)))) then break
    let t'10 := i'3
    if AP_ParamT_signed_char_1.op_to_signed_char s._use_for_yaw._priv_instance[UInt8.toNat (typesafe_index_unsigned_char_TAG_Priority.get_int t'10)]! != (0 : Int8) then
      s := { s with _first_usable := typesafe_index_unsigned_char_TAG_Priority.op_to_unsigned_char i'3 }
      break
    let (t'11, _) := typesafe_index_unsigned_char_TAG_Priority.op_inc_int32_t i'3 (0 : Int32)
    i'3 := t'11
  let new_healthy : Bool := healthy_void s
  return (s, w, new_healthy)

/-- C++ `uint32_t Compass::last_update_usec() const`, `AP_Compass/AP_Compass.h:324`. -/
def last_update_usec_void (s : State) : UInt32 := Id.run do
  return last_update_usec_uint8_t s s._first_usable

end Compass

namespace Compass

/-- C++ `void Compass::_detect_backends()`, `AP_Compass/AP_Compass.cpp:1348-1409`. -/
def _detect_backends (s : State) (w : World) (o : Outputs) : State × World × Outputs := Id.run do
  let mut s := s
  let mut w := w
  let mut o := o
  for i' in [0:8] do
    let i : UInt8 := Nat.toUInt8 i'
    let t'5 := Compass.DriverType.DRIVER_SITL
    w := { w with compass := s }  -- this object's state into the World: the call reaches it
    let (t'1, t'3, t'2) := AP_Compass_SITL.init w o (WPtr.heap'AP_Compass_SITL w.heap'AP_Compass_SITL.size) i
    w := t'3
    o := t'2
    s := w.compass  -- this object's state as the call left it
    let t'4 := w.heap'AP_Compass_SITL.size
    w := { w with heap'AP_Compass_SITL := w.heap'AP_Compass_SITL.push t'1 }
    s := add_backend s t'5 (WPtr.heap'AP_Compass_SITL t'4)
    if UInt32.toInt32 (UInt8.toUInt32 s._unreg_compass_count) == (5 : Int32) then
      return (s, w, o)
  if UInt32.toInt32 (UInt8.toUInt32 s._unreg_compass_count) == (5 : Int32) then
    return (s, w, o)
  pure ()  -- C++ `probe_i2c_spi_compasses`: no effect in the model
  if UInt32.toInt32 (UInt8.toUInt32 s._backend_count) == (0 : Int32) || UInt32.toInt32 (UInt8.toUInt32 s._compass_count) == (0 : Int32) then
    for _ in [0:1] do
      o := o.push (Output.console_printf "No Compass backends available\x0a" #[])
  return (s, w, o)

/-- C++ `void Compass::init()`, `AP_Compass/AP_Compass.cpp:697-805`. -/
def init (s : State) (w : World) (o : Outputs) : State × World × Outputs := Id.run do
  let mut s := s
  let mut w := w
  let mut o := o
  if !(AP_ParamT_signed_char_1.op_to_signed_char s._enabled != (0 : Int8)) then
    return (s, w, o)
  s := { s with suppress_devid_save := true }
  for i' in [0:3] do
    let i : UInt8 := Nat.toUInt8 i'
    if AP_ParamT_unsigned_int_3.op_to_unsigned_int s._state._priv_instance[UInt8.toNat i]!.dev_id != Int32.toUInt32 (0 : Int32) then
      s := { s with suppress_devid_save := false }
      break
    if AP_ParamT_unsigned_int_3.op_to_unsigned_int s._priority_did_stored_list._priv_instance[UInt8.toNat i]! != Int32.toUInt32 (0 : Int32) then
      s := { s with suppress_devid_save := false }
      break
  if !s.suppress_devid_save then
    let mut i'2 : typesafe_index_unsigned_char_TAG_Priority.State := typesafe_index_unsigned_char_TAG_Priority.init (Int8.toUInt8 (Int32.toInt8 (0 : Int32)))
    for _ in [0:2^64] do  -- C loop without a constant trip count (--general-loops)
      if !(typesafe_index_unsigned_char_TAG_Priority.op_lt i'2 (Int8.toUInt8 (Int32.toInt8 (3 : Int32)))) then break
      let t'1 := i'2
      if AP_ParamT_unsigned_int_3.op_to_unsigned_int s._priority_did_stored_list._priv_instance[UInt8.toNat (typesafe_index_unsigned_char_TAG_Priority.get_int t'1)]! != Int32.toUInt32 (0 : Int32) then
        let t'2 := i'2
        let t'3 := i'2
        s := { s with _priority_did_list._priv_instance := s._priority_did_list._priv_instance.set! (UInt8.toNat (typesafe_index_unsigned_char_TAG_Priority.get_int t'3)) (AP_ParamT_unsigned_int_3.op_to_unsigned_int s._priority_did_stored_list._priv_instance[UInt8.toNat (typesafe_index_unsigned_char_TAG_Priority.get_int t'2)]!) }
      else
        let mut j : typesafe_index_unsigned_char_TAG_Priority.State := typesafe_index_unsigned_char_TAG_Priority.op_add i'2 (Int8.toUInt8 (Int32.toInt8 (1 : Int32)))
        let mut t'21 := true
        for _ in [0:2^64] do  -- C loop without a constant trip count (--general-loops)
          if t'21 then
            t'21 := false
          else
            let (t'19, _) := typesafe_index_unsigned_char_TAG_Priority.op_inc_int32_t j (0 : Int32)
            j := t'19
          if !(typesafe_index_unsigned_char_TAG_Priority.op_lt j (Int8.toUInt8 (Int32.toInt8 (3 : Int32)))) then break
          let mut temp : UInt32 := (0 : UInt32)  -- uninitialized in C++; assigned before every read
          let t'4 := j
          let t'6 := AP_ParamT_unsigned_int_3.op_to_unsigned_int s._priority_did_stored_list._priv_instance[UInt8.toNat (typesafe_index_unsigned_char_TAG_Priority.get_int t'4)]!
          let t'5 := i'2
          if t'6 == AP_ParamT_unsigned_int_3.op_to_unsigned_int s._priority_did_stored_list._priv_instance[UInt8.toNat (typesafe_index_unsigned_char_TAG_Priority.get_int t'5)]! then
            let t'7 := j
            let (t'8, t'9) := AP_ParamT_unsigned_int_3.set_and_save_ifchanged s._priority_did_stored_list._priv_instance[UInt8.toNat (typesafe_index_unsigned_char_TAG_Priority.get_int t'7)]! o ("compass._priority_did_stored_list._priv_instance[" ++ (toString (UInt8.toNat (typesafe_index_unsigned_char_TAG_Priority.get_int t'7))) ++ "]") (Int32.toUInt32 (0 : Int32))
            s := { s with _priority_did_stored_list._priv_instance := s._priority_did_stored_list._priv_instance.set! (UInt8.toNat (typesafe_index_unsigned_char_TAG_Priority.get_int t'7)) t'8 }
            o := t'9
          let t'10 := j
          if AP_ParamT_unsigned_int_3.op_to_unsigned_int s._priority_did_stored_list._priv_instance[UInt8.toNat (typesafe_index_unsigned_char_TAG_Priority.get_int t'10)]! == Int32.toUInt32 (0 : Int32) then
            continue
          let t'11 := j
          temp := AP_ParamT_unsigned_int_3.op_to_unsigned_int s._priority_did_stored_list._priv_instance[UInt8.toNat (typesafe_index_unsigned_char_TAG_Priority.get_int t'11)]!
          let t'12 := j
          let (t'13, t'14) := AP_ParamT_unsigned_int_3.set_and_save_ifchanged s._priority_did_stored_list._priv_instance[UInt8.toNat (typesafe_index_unsigned_char_TAG_Priority.get_int t'12)]! o ("compass._priority_did_stored_list._priv_instance[" ++ (toString (UInt8.toNat (typesafe_index_unsigned_char_TAG_Priority.get_int t'12))) ++ "]") (Int32.toUInt32 (0 : Int32))
          s := { s with _priority_did_stored_list._priv_instance := s._priority_did_stored_list._priv_instance.set! (UInt8.toNat (typesafe_index_unsigned_char_TAG_Priority.get_int t'12)) t'13 }
          o := t'14
          let t'15 := i'2
          s := { s with _priority_did_list._priv_instance := s._priority_did_list._priv_instance.set! (UInt8.toNat (typesafe_index_unsigned_char_TAG_Priority.get_int t'15)) temp }
          let t'16 := i'2
          let (t'17, t'18) := AP_ParamT_unsigned_int_3.set_and_save_ifchanged s._priority_did_stored_list._priv_instance[UInt8.toNat (typesafe_index_unsigned_char_TAG_Priority.get_int t'16)]! o ("compass._priority_did_stored_list._priv_instance[" ++ (toString (UInt8.toNat (typesafe_index_unsigned_char_TAG_Priority.get_int t'16))) ++ "]") temp
          s := { s with _priority_did_stored_list._priv_instance := s._priority_did_stored_list._priv_instance.set! (UInt8.toNat (typesafe_index_unsigned_char_TAG_Priority.get_int t'16)) t'17 }
          o := t'18
          break
      let (t'22, _) := typesafe_index_unsigned_char_TAG_Priority.op_inc_int32_t i'2 (0 : Int32)
      i'2 := t'22
  let mut i'3 : typesafe_index_unsigned_char_TAG_StateIndex.State := typesafe_index_unsigned_char_TAG_StateIndex.init (Int8.toUInt8 (Int32.toInt8 (0 : Int32)))
  for _ in [0:2^64] do  -- C loop without a constant trip count (--general-loops)
    if !(typesafe_index_unsigned_char_TAG_StateIndex.op_lt i'3 (Int8.toUInt8 (Int32.toInt8 (3 : Int32)))) then break
    let t'24 := i'3
    let t'25 := i'3
    s := { s with _state._priv_instance := s._state._priv_instance.set! (UInt8.toNat (typesafe_index_unsigned_char_TAG_StateIndex.get_int t'25)) ({ s._state._priv_instance[UInt8.toNat (typesafe_index_unsigned_char_TAG_StateIndex.get_int t'25)]! with expected_dev_id := AP_ParamT_unsigned_int_3.op_to_unsigned_int s._state._priv_instance[UInt8.toNat (typesafe_index_unsigned_char_TAG_StateIndex.get_int t'24)]!.dev_id }) }
    let (t'26, _) := typesafe_index_unsigned_char_TAG_StateIndex.op_inc_int32_t i'3 (0 : Int32)
    i'3 := t'26
  let t'28 : UInt8 := s._unreg_compass_count
  let t'29 : Int32 := (5 : Int32)
  for i'4' in [0:(t'29.toInt - (Int.ofNat t'28.toNat)).toNat] do  -- C++ loop bounded by a runtime value (--runtime-loops)
    let i'4 : UInt8 := t'28 + Nat.toUInt8 i'4'
    s := { s with _previously_unreg_mag := s._previously_unreg_mag.set! (UInt8.toNat i'4) (AP_ParamT_unsigned_int_3.op_to_unsigned_int s.extra_dev_id[UInt8.toNat i'4]!) }
    s := { s with extra_dev_id := s.extra_dev_id.set! (UInt8.toNat i'4) (AP_ParamT_unsigned_int_3.set s.extra_dev_id[UInt8.toNat i'4]! (Int32.toUInt32 (0 : Int32))) }
  if !s.suppress_devid_save then
    let (t'30, t'31) := _reorder_compass_params s o
    s := t'30
    o := t'31
  if UInt32.toInt32 (UInt8.toUInt32 s._compass_count) == (0 : Int32) then
    let (t'32, t'33, t'34) := _detect_backends s w o
    w := t'33
    s := t'32
    o := t'34
  if UInt32.toInt32 (UInt8.toUInt32 s._compass_count) != (0 : Int32) then
    w := { w with compass := s }  -- this object's state into the World: the call reaches it
    let t'35 := w.est_scheduler  -- the object out of the World for the call (--swap-out)
    w := { w with est_scheduler := default }
    let (t'36, t'37, t'38) := EstScheduler.delay t'35 w o (Int16.toUInt16 (Int32.toInt16 (100 : Int32)))
    w := t'37
    w := { w with est_scheduler := t'36 }
    o := t'38
    s := w.compass  -- this object's state as the call left it
    let (t'39, t'40, _) := read s w
    w := t'40
    s := t'39
  let mut i'5 : typesafe_index_unsigned_char_TAG_StateIndex.State := typesafe_index_unsigned_char_TAG_StateIndex.init (Int8.toUInt8 (Int32.toInt8 (0 : Int32)))
  for _ in [0:2^64] do  -- C loop without a constant trip count (--general-loops)
    if !(typesafe_index_unsigned_char_TAG_StateIndex.op_lt i'5 (Int8.toUInt8 (Int32.toInt8 (3 : Int32)))) then break
    let t'42 := i'5
    if !s._state._priv_instance[UInt8.toNat (typesafe_index_unsigned_char_TAG_StateIndex.get_int t'42)]!.registered then
      let t'43 := i'5
      s := { s with _state._priv_instance := s._state._priv_instance.set! (UInt8.toNat (typesafe_index_unsigned_char_TAG_StateIndex.get_int t'43)) ({ s._state._priv_instance[UInt8.toNat (typesafe_index_unsigned_char_TAG_StateIndex.get_int t'43)]! with dev_id := AP_ParamT_unsigned_int_3.set s._state._priv_instance[UInt8.toNat (typesafe_index_unsigned_char_TAG_StateIndex.get_int t'43)]!.dev_id (Int32.toUInt32 (0 : Int32)) }) }
    let (t'44, _) := typesafe_index_unsigned_char_TAG_StateIndex.op_inc_int32_t i'5 (0 : Int32)
    i'5 := t'44
  w := { w with compass := s }  -- this object's state into the World: the call reaches it
  let t'46 := w.ahrs  -- the object out of the World for the call (--swap-out)
  w := { w with ahrs := default }
  let (t'47, t'48) := AP_AHRS.update_orientation t'46 w w.ahrs'inp
  w := t'48
  w := { w with ahrs := t'47 }
  s := w.compass  -- this object's state as the call left it
  s := { s with init_done := true }
  s := { s with suppress_devid_save := false }
  return (s, w, o)

/-- C++ `void Compass::set_throttle(float thr_pct)`, `AP_Compass/AP_Compass.h:303-307`. -/
def set_throttle (s : State) (thr_pct : Binary32) : State := Id.run do
  let mut s := s
  if Int8.toInt32 (AP_ParamT_signed_char_1.op_to_signed_char s._motor_comp_type) == (1 : Int32) then
    s := { s with _thr := thr_pct }
  return s

end Compass

end Estimator_lib
