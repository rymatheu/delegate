import ArduLean.Runtime.CFloat
import ArduLean.Estimator.libraries.AP_Math.AP_Math
import ArduLean.Estimator.World
import ArduLean.Estimator.libraries.AP_Common.AP_Common
import ArduLean.Estimator.libraries.AP_Param.AP_Param
import ArduLean.Estimator.libraries.AP_Compass.AP_Compass
import ArduLean.Estimator.World_2
import ArduLean.Estimator.libraries.AP_Common.AP_Common_2
import ArduLean.Estimator.libraries.AP_Param.AP_Param_2

/-!
ArduPilot `libraries/AP_Compass`, part 2 of 4. Sources: `libraries/AP_Compass/AP_Compass.cpp`, `libraries/AP_Compass/AP_Compass.h`.

Items of `lean/Estimator_lib.lean` (the estimator translation), unchanged; placed by `tools/split_modules.py` (`ArduLean/Estimator/INDEX.md`).
-/

open FloatLib.Floats (Binary32 Binary64)

set_option maxRecDepth 200000
-- AP_DAL's `const log_RISH old_RISH = _RISH;` read only by WRITE_REPLAY_BLOCK_IFCHANGED, which is `(void)old`
-- without logging (HAL_LOGGING_ENABLED 0): an unused binding, as in the C++
set_option linter.unusedVariables false

namespace Estimator_lib

namespace Compass

/-- State of C++ `Compass` (`AP_Compass/AP_Compass.h:69-721`): its data members. -/
structure State where
  /-- `AP_Compass_Backend * _backends[3]` of `Compass` (`AP_Compass/AP_Compass.h:551`). -/
  _backends : Array WPtr := Array.replicate 3 WPtr.null
  /-- `uint8_t _backend_count` of `Compass` (`AP_Compass/AP_Compass.h:552`). -/
  _backend_count : UInt8 := (0 : UInt8)
  /-- `AP_Int8 _enabled` of `Compass` (`AP_Compass/AP_Compass.h:555`). -/
  _enabled : AP_ParamT_signed_char_1.State := {}
  /-- `uint8_t _compass_count` of `Compass` (`AP_Compass/AP_Compass.h:558`). -/
  _compass_count : UInt8 := (0 : UInt8)
  /-- `uint8_t _unreg_compass_count` of `Compass` (`AP_Compass/AP_Compass.h:561`). -/
  _unreg_compass_count : UInt8 := (0 : UInt8)
  /-- `AP_Enum<LearnType> _learn` of `Compass` (`AP_Compass/AP_Compass.h:564`). -/
  _learn : AP_Enum_Compass_LearnType.State := {}
  /-- `enum Rotation _board_orientation` of `Compass` (`AP_Compass/AP_Compass.h:567`). -/
  _board_orientation : Rotation := Rotation.ROTATION_NONE
  /-- `AP_Float _declination` of `Compass` (`AP_Compass/AP_Compass.h:570`). -/
  _declination : AP_ParamT_float_4.State := {}
  /-- `AP_Int8 _auto_declination` of `Compass` (`AP_Compass/AP_Compass.h:573`). -/
  _auto_declination : AP_ParamT_signed_char_1.State := {}
  /-- `uint32_t _log_bit` of `Compass` (`AP_Compass/AP_Compass.h:576`). -/
  _log_bit : UInt32 := Int32.toUInt32 (-(1 : Int32))
  /-- `AP_Int8 _motor_comp_type` of `Compass` (`AP_Compass/AP_Compass.h:580`). -/
  _motor_comp_type : AP_ParamT_signed_char_1.State := {}
  /-- `AP_Int8 _rotate_auto` of `Compass` (`AP_Compass/AP_Compass.h:583`). -/
  _rotate_auto : AP_ParamT_signed_char_1.State := {}
  /-- `float _thr` of `Compass` (`AP_Compass/AP_Compass.h:586`). -/
  _thr : Binary32 := (Binary32.ofBits 0x00000000 /- 0.0 -/)
  /-- `RestrictIDTypeArray<mag_state, 3 + 1, StateIndex> _state` of `Compass` (`AP_Compass/AP_Compass.h:634`). -/
  _state : RestrictIDTypeArray_Compass_mag_state_4_typesafe_index_unsigned_char_TAG_StateIndex.State := {}
  /-- `RestrictIDTypeArray<AP_Int8, 3, Priority> _use_for_yaw` of `Compass` (`AP_Compass/AP_Compass.h:662`). -/
  _use_for_yaw : RestrictIDTypeArray_AP_ParamT_signed_char_AP_PARAM_INT8_3_typesafe_index_unsigned_char_TAG_Priority.State := {}
  /-- `RestrictIDTypeArray<AP_UInt32, 3, Priority> _priority_did_stored_list` of `Compass` (`AP_Compass/AP_Compass.h:664`). -/
  _priority_did_stored_list : RestrictIDTypeArray_AP_ParamT_unsigned_int_AP_PARAM_INT32_3_typesafe_index_unsigned_char_TAG_Priority.State := {}
  /-- `RestrictIDTypeArray<uint32_t, 3, Priority> _priority_did_list` of `Compass` (`AP_Compass/AP_Compass.h:665`). -/
  _priority_did_list : RestrictIDTypeArray_unsigned_int_3_typesafe_index_unsigned_char_TAG_Priority.State := {}
  /-- `AP_UInt16 _offset_max` of `Compass` (`AP_Compass/AP_Compass.h:668`). -/
  _offset_max : AP_ParamT_unsigned_short_2.State := {}
  /-- `AP_UInt16 _options` of `Compass` (`AP_Compass/AP_Compass.h:676`). -/
  _options : AP_ParamT_unsigned_short_2.State := {}
  /-- `Compass_PerMotor _per_motor` of `Compass` (`AP_Compass/AP_Compass.h:684`). -/
  _per_motor : Compass_PerMotor.State := {}
  /-- `AP_Float _calibration_threshold` of `Compass` (`AP_Compass/AP_Compass.h:687`). -/
  _calibration_threshold : AP_ParamT_float_4.State := {}
  /-- `AP_UInt32 _driver_type_mask` of `Compass` (`AP_Compass/AP_Compass.h:690`). -/
  _driver_type_mask : AP_ParamT_unsigned_int_3.State := {}
  /-- `AP_UInt32 extra_dev_id[5]` of `Compass` (`AP_Compass/AP_Compass.h:694`). -/
  extra_dev_id : Array AP_ParamT_unsigned_int_3.State := Array.replicate 5 {}
  /-- `uint32_t _previously_unreg_mag[5]` of `Compass` (`AP_Compass/AP_Compass.h:695`). -/
  _previously_unreg_mag : Array UInt32 := Array.replicate 5 (0 : UInt32)
  /-- `AP_UInt8 _filter_range` of `Compass` (`AP_Compass/AP_Compass.h:698`). -/
  _filter_range : AP_ParamT_unsigned_char_1.State := {}
  /-- `CompassLearn * learn` of `Compass` (`AP_Compass/AP_Compass.h:700`). -/
  learn : WPtr := WPtr.null
  /-- `bool learn_allocated` of `Compass` (`AP_Compass/AP_Compass.h:701`). -/
  learn_allocated : Bool := false
  /-- `bool _initial_location_set` of `Compass` (`AP_Compass/AP_Compass.h:709`). -/
  _initial_location_set : Bool := false
  /-- `bool _cal_thread_started` of `Compass` (`AP_Compass/AP_Compass.h:711`). -/
  _cal_thread_started : Bool := false
  /-- `bool init_done` of `Compass` (`AP_Compass/AP_Compass.h:716`). -/
  init_done : Bool := false
  /-- `bool suppress_devid_save` of `Compass` (`AP_Compass/AP_Compass.h:718`). -/
  suppress_devid_save : Bool := false
  /-- `uint8_t _first_usable` of `Compass` (`AP_Compass/AP_Compass.h:720`). -/
  _first_usable : UInt8 := (0 : UInt8)
deriving Inhabited

/-- Values C++ `Compass` reads from objects outside the translation (--boundary): one field per distinct read, in first-use order. -/
structure Inputs where
  /-- What member `_per_motor` reads from the boundary. -/
  _per_motor : Compass_PerMotor.Inputs := {}
deriving Inhabited

end Compass

namespace Compass

/-- C++ `void Compass::set_board_orientation(enum Rotation orientation)`, `AP_Compass/AP_Compass.h:244-246`. -/
def set_board_orientation (s : State) (orientation : Rotation) : State := Id.run do
  let mut s := s
  s := { s with _board_orientation := orientation }
  return s

end Compass

namespace Compass

/-- C++ `StateIndex Compass::_get_state_id(Priority priority) const`, `AP_Compass/AP_Compass.cpp:974-989`. -/
def _get_state_id (s : State) (priority : typesafe_index_unsigned_char_TAG_Priority.State) : typesafe_index_unsigned_char_TAG_StateIndex.State := Id.run do
  if RestrictIDTypeArray_unsigned_int_3_typesafe_index_unsigned_char_TAG_Priority.op_index s._priority_did_list priority == Int32.toUInt32 (0 : Int32) then
    return typesafe_index_unsigned_char_TAG_StateIndex.init (Int8.toUInt8 (Int32.toInt8 (3 : Int32)))
  let mut i : typesafe_index_unsigned_char_TAG_StateIndex.State := typesafe_index_unsigned_char_TAG_StateIndex.init (Int8.toUInt8 (Int32.toInt8 (0 : Int32)))
  for _ in [0:2^64] do  -- C loop without a constant trip count (--general-loops)
    if !(typesafe_index_unsigned_char_TAG_StateIndex.op_lt i (Int8.toUInt8 (Int32.toInt8 (3 : Int32)))) then break
    let t'2 := RestrictIDTypeArray_unsigned_int_3_typesafe_index_unsigned_char_TAG_Priority.op_index s._priority_did_list priority
    let t'1 := i
    if t'2 == s._state._priv_instance[UInt8.toNat (typesafe_index_unsigned_char_TAG_StateIndex.get_int t'1)]!.detected_dev_id then
      return i
    let (t'3, _) := typesafe_index_unsigned_char_TAG_StateIndex.op_inc_int32_t i (0 : Int32)
    i := t'3
  return typesafe_index_unsigned_char_TAG_StateIndex.init (Int8.toUInt8 (Int32.toInt8 (3 : Int32)))

/-- C++ `bool Compass::healthy(uint8_t i) const`, `AP_Compass/AP_Compass.cpp:2211-2214`. -/
def healthy_uint8_t (s : State) (i : UInt8) : Bool := Id.run do
  let mut t'3 : Bool := false
  if UInt32.toInt32 (UInt8.toUInt32 i) < (3 : Int32) then
    let t'1 := typesafe_index_unsigned_char_TAG_Priority.init i
    let t'2 := _get_state_id s t'1
    t'3 := s._state._priv_instance[UInt8.toNat (typesafe_index_unsigned_char_TAG_StateIndex.get_int t'2)]!.healthy
  else
    t'3 := false
  return t'3

end Compass

namespace Compass

/-- C++ `bool Compass::available() const`, `AP_Compass/AP_Compass.h:99`. -/
def available (s : State) : Bool := Id.run do
  return AP_ParamT_signed_char_1.op_to_signed_char s._enabled != (0 : Int8) && s.init_done

/-- C++ `enum class Compass::LearnType`, `AP_Compass/AP_Compass.h:332-337`. -/
inductive LearnType where
  | NONE
  | COPY_FROM_EKF
  | INFLIGHT
deriving DecidableEq, Inhabited

/-- The value of each enumerator of `Compass::LearnType` (underlying type `int32_t`). -/
def LearnType.toInt : LearnType → Int32
  | .NONE => (0 : Int32)
  | .COPY_FROM_EKF => (2 : Int32)
  | .INFLIGHT => (3 : Int32)

/-- The enumerator of `Compass::LearnType` with value `v` (the C++ converts only enumerator values; any other
value gives the first enumerator, the `Inhabited` default). -/
def LearnType.ofInt (v : Int32) : LearnType :=
  if v == (0 : Int32) then .NONE
  else if v == (2 : Int32) then .COPY_FROM_EKF
  else if v == (3 : Int32) then .INFLIGHT
  else default

end Compass

namespace Compass

/-- C++ `bool Compass::have_scale_factor(uint8_t i) const`, `AP_Compass/AP_Compass.cpp:2219-2231`. -/
def have_scale_factor (s : State) (i : UInt8) : Bool := Id.run do
  if !(available s) then
    return false
  let id : typesafe_index_unsigned_char_TAG_StateIndex.State := _get_state_id s (typesafe_index_unsigned_char_TAG_Priority.init i)
  let mut t'2 := typesafe_index_unsigned_char_TAG_StateIndex.op_ge id (Int8.toUInt8 (Int32.toInt8 (3 : Int32)))
  if !t'2 then
    let t'1 := id
    t'2 := decide (AP_ParamT_float_4.op_to_float s._state._priv_instance[UInt8.toNat (typesafe_index_unsigned_char_TAG_StateIndex.get_int t'1)]!.scale_factor < ((Binary32.ofBits 0x3f800000 /- (float)1 -/) / (Binary32.ofBits 0x3fc00000 /- (float)3/2 -/)))
  let mut t'4 := t'2
  if !t'4 then
    let t'3 := id
    t'4 := decide (AP_ParamT_float_4.op_to_float s._state._priv_instance[UInt8.toNat (typesafe_index_unsigned_char_TAG_StateIndex.get_int t'3)]!.scale_factor > (Binary32.ofBits 0x3fc00000 /- (float)3/2 -/))
  if t'4 then
    return false
  return true

end Compass

namespace Compass

/-- C++ `uint8_t Compass::get_filter_range() const`, `AP_Compass/AP_Compass.h:367`. -/
def get_filter_range (s : State) : UInt8 := Id.run do
  return AP_ParamT_unsigned_char_1.op_to_unsigned_char s._filter_range

end Compass

namespace Compass.mag_state

/-- C++ `void Compass::mag_state::copy_from(const mag_state & state)`, `AP_Compass/AP_Compass.cpp:870-884`. -/
def copy_from (s : State) (o : Outputs) (sp : String) (state : Compass.mag_state.State) : State × Outputs := Id.run do
  let mut s := s
  let mut o := o
  let (t'1, t'2) := AP_ParamT_signed_char_1.set_and_save_ifchanged s.external o (sp ++ ".external") (AP_ParamT_signed_char_1.op_to_signed_char state.external)
  s := { s with external := t'1 }
  o := t'2
  let (t'3, t'4) := AP_ParamT_signed_char_1.set_and_save_ifchanged s.orientation o (sp ++ ".orientation") (AP_ParamT_signed_char_1.op_to_signed_char state.orientation)
  s := { s with orientation := t'3 }
  o := t'4
  let (t'5, t'6) := AP_ParamV_Vector3_float_5.set_and_save_ifchanged s.offset o (sp ++ ".offset") (AP_ParamV_Vector3_float_5.op_to_Vector3_float state.offset)
  s := { s with offset := t'5 }
  o := t'6
  let (t'7, t'8) := AP_ParamV_Vector3_float_5.set_and_save_ifchanged s.diagonals o (sp ++ ".diagonals") (AP_ParamV_Vector3_float_5.op_to_Vector3_float state.diagonals)
  s := { s with diagonals := t'7 }
  o := t'8
  let (t'9, t'10) := AP_ParamV_Vector3_float_5.set_and_save_ifchanged s.offdiagonals o (sp ++ ".offdiagonals") (AP_ParamV_Vector3_float_5.op_to_Vector3_float state.offdiagonals)
  s := { s with offdiagonals := t'9 }
  o := t'10
  let (t'11, t'12) := AP_ParamT_float_4.set_and_save_ifchanged s.scale_factor o (sp ++ ".scale_factor") (AP_ParamT_float_4.op_to_float state.scale_factor)
  s := { s with scale_factor := t'11 }
  o := t'12
  let (t'13, t'14) := AP_ParamT_unsigned_int_3.set_and_save_ifchanged s.dev_id o (sp ++ ".dev_id") (AP_ParamT_unsigned_int_3.op_to_unsigned_int state.dev_id)
  s := { s with dev_id := t'13 }
  o := t'14
  let (t'15, t'16) := AP_ParamV_Vector3_float_5.set_and_save_ifchanged s.motor_compensation o (sp ++ ".motor_compensation") (AP_ParamV_Vector3_float_5.op_to_Vector3_float state.motor_compensation)
  s := { s with motor_compensation := t'15 }
  o := t'16
  s := { s with expected_dev_id := state.expected_dev_id }
  s := { s with detected_dev_id := state.detected_dev_id }
  return (s, o)

end Compass.mag_state

namespace Compass

/-- C++ `void Compass::_reorder_compass_params()`, `AP_Compass/AP_Compass.cpp:845-867`. -/
def _reorder_compass_params (s : State) (o : Outputs) : State × Outputs := Id.run do
  let mut s := s
  let mut o := o
  let mut swap_state : Compass.mag_state.State := {}
  let mut curr_state_id : typesafe_index_unsigned_char_TAG_StateIndex.State := typesafe_index_unsigned_char_TAG_StateIndex.init (0 : UInt8)
  let mut i : typesafe_index_unsigned_char_TAG_Priority.State := typesafe_index_unsigned_char_TAG_Priority.init (Int8.toUInt8 (Int32.toInt8 (0 : Int32)))
  let mut t'15 := true
  for _ in [0:2^64] do  -- C loop without a constant trip count (--general-loops)
    if t'15 then
      t'15 := false
    else
      let (t'13, _) := typesafe_index_unsigned_char_TAG_Priority.op_inc_int32_t i (0 : Int32)
      i := t'13
    if !(typesafe_index_unsigned_char_TAG_Priority.op_lt i (Int8.toUInt8 (Int32.toInt8 (3 : Int32)))) then break
    if RestrictIDTypeArray_unsigned_int_3_typesafe_index_unsigned_char_TAG_Priority.op_index s._priority_did_list i == Int32.toUInt32 (0 : Int32) then
      continue
    curr_state_id := typesafe_index_unsigned_char_TAG_StateIndex.op_assign curr_state_id (Int8.toUInt8 (Int32.toInt8 (3 : Int32)))
    let mut j : typesafe_index_unsigned_char_TAG_StateIndex.State := typesafe_index_unsigned_char_TAG_StateIndex.init (Int8.toUInt8 (Int32.toInt8 (0 : Int32)))
    for _ in [0:2^64] do  -- C loop without a constant trip count (--general-loops)
      if !(typesafe_index_unsigned_char_TAG_StateIndex.op_lt j (Int8.toUInt8 (Int32.toInt8 (3 : Int32)))) then break
      let t'2 := RestrictIDTypeArray_unsigned_int_3_typesafe_index_unsigned_char_TAG_Priority.op_index s._priority_did_list i
      let t'1 := j
      if t'2 == AP_ParamT_unsigned_int_3.op_to_unsigned_int s._state._priv_instance[UInt8.toNat (typesafe_index_unsigned_char_TAG_StateIndex.get_int t'1)]!.dev_id then
        curr_state_id := j
        break
      let (t'3, _) := typesafe_index_unsigned_char_TAG_StateIndex.op_inc_int32_t j (0 : Int32)
      j := t'3
    if typesafe_index_unsigned_char_TAG_StateIndex.op_ne curr_state_id (Int8.toUInt8 (Int32.toInt8 (3 : Int32))) && UInt32.toInt32 (UInt8.toUInt32 (typesafe_index_unsigned_char_TAG_StateIndex.op_to_unsigned_char curr_state_id)) != UInt32.toInt32 (UInt8.toUInt32 (typesafe_index_unsigned_char_TAG_Priority.op_to_unsigned_char i)) then
      let (t'5, t'6) := Compass.mag_state.copy_from swap_state o "<local Compass::_reorder_compass_params::swap_state>" (RestrictIDTypeArray_Compass_mag_state_4_typesafe_index_unsigned_char_TAG_StateIndex.op_index s._state curr_state_id)
      swap_state := t'5
      o := t'6
      let t'7 := curr_state_id
      let (t'8, t'9) := Compass.mag_state.copy_from s._state._priv_instance[UInt8.toNat (typesafe_index_unsigned_char_TAG_StateIndex.get_int t'7)]! o ("compass._state._priv_instance[" ++ (toString (UInt8.toNat (typesafe_index_unsigned_char_TAG_StateIndex.get_int t'7))) ++ "]") (RestrictIDTypeArray_Compass_mag_state_4_typesafe_index_unsigned_char_TAG_StateIndex.op_index s._state (typesafe_index_unsigned_char_TAG_StateIndex.init (typesafe_index_unsigned_char_TAG_Priority.op_to_unsigned_char i)))
      s := { s with _state._priv_instance := s._state._priv_instance.set! (UInt8.toNat (typesafe_index_unsigned_char_TAG_StateIndex.get_int t'7)) t'8 }
      o := t'9
      let t'10 := typesafe_index_unsigned_char_TAG_StateIndex.init (typesafe_index_unsigned_char_TAG_Priority.op_to_unsigned_char i)
      let (t'11, t'12) := Compass.mag_state.copy_from s._state._priv_instance[UInt8.toNat (typesafe_index_unsigned_char_TAG_StateIndex.get_int t'10)]! o ("compass._state._priv_instance[" ++ (toString (UInt8.toNat (typesafe_index_unsigned_char_TAG_StateIndex.get_int t'10))) ++ "]") swap_state
      s := { s with _state._priv_instance := s._state._priv_instance.set! (UInt8.toNat (typesafe_index_unsigned_char_TAG_StateIndex.get_int t'10)) t'11 }
      o := t'12
  return (s, o)

/-- C++ `enum Compass::DriverType`, `AP_Compass/AP_Compass.h:456-530`. -/
inductive DriverType where
  | DRIVER_SITL
deriving DecidableEq, Inhabited

/-- The value of each enumerator of `Compass::DriverType` (underlying type `uint32_t`). -/
def DriverType.toInt : DriverType → UInt32
  | .DRIVER_SITL => (13 : UInt32)

/-- C++ `bool Compass::_driver_enabled(enum DriverType driver_type)`, `AP_Compass/AP_Compass.cpp:994-998`. -/
def _driver_enabled (s : State) (driver_type : Compass.DriverType) : Bool := Id.run do
  let mask : UInt32 := ((1 : UInt32) <<< Int32.toUInt32 (UInt32.toInt32 (UInt8.toUInt32 (UInt32.toUInt8 (Compass.DriverType.toInt driver_type)))))
  return (mask &&& AP_ParamT_unsigned_int_3.op_to_unsigned_int s._driver_type_mask) == Int32.toUInt32 (0 : Int32)

/-- C++ `void Compass::add_backend(DriverType driver_type, AP_Compass_Backend * backend)`, `AP_Compass/AP_Compass.cpp:1028-1043`. -/
def add_backend (s : State) (driver_type : Compass.DriverType) (backend : WPtr) : State := Id.run do
  let mut s := s
  if !(_driver_enabled s driver_type) then
    return s
  if !(backend != WPtr.null) then
    return s
  if UInt32.toInt32 (UInt8.toUInt32 s._backend_count) == (3 : Int32) then
    return s
  let t'1 := s._backend_count
  s := { s with _backend_count := s._backend_count + (1 : UInt8) }
  s := { s with _backends := s._backends.set! (UInt8.toNat t'1) backend }
  return s

end Compass

namespace Compass

/-- C++ `Priority Compass::_update_priority_list(uint32_t dev_id)`, `AP_Compass/AP_Compass.cpp:810-838`. -/
def _update_priority_list (s : State) (o : Outputs) (dev_id : UInt32) : State × Outputs × typesafe_index_unsigned_char_TAG_Priority.State := Id.run do
  let mut s := s
  let mut o := o
  let mut i : typesafe_index_unsigned_char_TAG_Priority.State := typesafe_index_unsigned_char_TAG_Priority.init (Int8.toUInt8 (Int32.toInt8 (0 : Int32)))
  for _ in [0:2^64] do  -- C loop without a constant trip count (--general-loops)
    if !(typesafe_index_unsigned_char_TAG_Priority.op_lt i (Int8.toUInt8 (Int32.toInt8 (3 : Int32)))) then break
    if RestrictIDTypeArray_unsigned_int_3_typesafe_index_unsigned_char_TAG_Priority.op_index s._priority_did_list i == dev_id then
      if typesafe_index_unsigned_char_TAG_Priority.op_ge i s._compass_count then
        s := { s with _compass_count := Int8.toUInt8 (Int32.toInt8 (UInt32.toInt32 (UInt8.toUInt32 (typesafe_index_unsigned_char_TAG_Priority.op_to_unsigned_char i)) + (1 : Int32))) }
      return (s, o, i)
    let (t'1, _) := typesafe_index_unsigned_char_TAG_Priority.op_inc_int32_t i (0 : Int32)
    i := t'1
  let mut i'2 : typesafe_index_unsigned_char_TAG_Priority.State := typesafe_index_unsigned_char_TAG_Priority.init (Int8.toUInt8 (Int32.toInt8 (0 : Int32)))
  for _ in [0:2^64] do  -- C loop without a constant trip count (--general-loops)
    if !(typesafe_index_unsigned_char_TAG_Priority.op_lt i'2 (Int8.toUInt8 (Int32.toInt8 (3 : Int32)))) then break
    let t'3 := i'2
    if AP_ParamT_unsigned_int_3.op_to_unsigned_int s._priority_did_stored_list._priv_instance[UInt8.toNat (typesafe_index_unsigned_char_TAG_Priority.get_int t'3)]! == Int32.toUInt32 (0 : Int32) then
      if s.suppress_devid_save then
        let t'4 := i'2
        s := { s with _priority_did_stored_list._priv_instance := s._priority_did_stored_list._priv_instance.set! (UInt8.toNat (typesafe_index_unsigned_char_TAG_Priority.get_int t'4)) (AP_ParamT_unsigned_int_3.set s._priority_did_stored_list._priv_instance[UInt8.toNat (typesafe_index_unsigned_char_TAG_Priority.get_int t'4)]! dev_id) }
      else
        let t'5 := i'2
        let (t'6, t'7) := AP_ParamT_unsigned_int_3.set_and_save s._priority_did_stored_list._priv_instance[UInt8.toNat (typesafe_index_unsigned_char_TAG_Priority.get_int t'5)]! o ("compass._priority_did_stored_list._priv_instance[" ++ (toString (UInt8.toNat (typesafe_index_unsigned_char_TAG_Priority.get_int t'5))) ++ "]") dev_id
        s := { s with _priority_did_stored_list._priv_instance := s._priority_did_stored_list._priv_instance.set! (UInt8.toNat (typesafe_index_unsigned_char_TAG_Priority.get_int t'5)) t'6 }
        o := t'7
      let t'8 := i'2
      s := { s with _priority_did_list._priv_instance := s._priority_did_list._priv_instance.set! (UInt8.toNat (typesafe_index_unsigned_char_TAG_Priority.get_int t'8)) dev_id }
      if typesafe_index_unsigned_char_TAG_Priority.op_ge i'2 s._compass_count then
        s := { s with _compass_count := Int8.toUInt8 (Int32.toInt8 (UInt32.toInt32 (UInt8.toUInt32 (typesafe_index_unsigned_char_TAG_Priority.op_to_unsigned_char i'2)) + (1 : Int32))) }
      return (s, o, i'2)
    let (t'9, _) := typesafe_index_unsigned_char_TAG_Priority.op_inc_int32_t i'2 (0 : Int32)
    i'2 := t'9
  return (s, o, typesafe_index_unsigned_char_TAG_Priority.init (Int8.toUInt8 (Int32.toInt8 (3 : Int32))))

/-- C++ `bool Compass::register_compass(uint32_t dev_id, uint8_t & instance)`, `AP_Compass/AP_Compass.cpp:887-972`. -/
def register_compass (s : State) (o : Outputs) (dev_id : UInt32) («instance» : UInt8) : State × Outputs × UInt8 × Bool := Id.run do
  let mut s := s
  let mut o := o
  let mut «instance» := «instance»
  let mut priority : typesafe_index_unsigned_char_TAG_Priority.State := typesafe_index_unsigned_char_TAG_Priority.init (0 : UInt8)
  let mut i : typesafe_index_unsigned_char_TAG_StateIndex.State := typesafe_index_unsigned_char_TAG_StateIndex.init (Int8.toUInt8 (Int32.toInt8 (0 : Int32)))
  for _ in [0:2^64] do  -- C loop without a constant trip count (--general-loops)
    if !(typesafe_index_unsigned_char_TAG_StateIndex.op_lt i (Int8.toUInt8 (Int32.toInt8 (3 : Int32)))) then break
    let (t'1, t'2, t'3) := _update_priority_list s o dev_id
    s := t'1
    o := t'2
    priority := t'3
    let t'4 := i
    if s._state._priv_instance[UInt8.toNat (typesafe_index_unsigned_char_TAG_StateIndex.get_int t'4)]!.expected_dev_id == dev_id && typesafe_index_unsigned_char_TAG_Priority.op_lt priority (Int8.toUInt8 (Int32.toInt8 (3 : Int32))) then
      let t'5 := i
      s := { s with _state._priv_instance := s._state._priv_instance.set! (UInt8.toNat (typesafe_index_unsigned_char_TAG_StateIndex.get_int t'5)) ({ s._state._priv_instance[UInt8.toNat (typesafe_index_unsigned_char_TAG_StateIndex.get_int t'5)]! with registered := true }) }
      let t'6 := i
      s := { s with _state._priv_instance := s._state._priv_instance.set! (UInt8.toNat (typesafe_index_unsigned_char_TAG_StateIndex.get_int t'6)) ({ s._state._priv_instance[UInt8.toNat (typesafe_index_unsigned_char_TAG_StateIndex.get_int t'6)]! with priority := priority }) }
      «instance» := typesafe_index_unsigned_char_TAG_StateIndex.op_to_unsigned_char i
      return (s, o, «instance», true)
    let (t'7, _) := typesafe_index_unsigned_char_TAG_StateIndex.op_inc_int32_t i (0 : Int32)
    i := t'7
  let mut i'2 : typesafe_index_unsigned_char_TAG_StateIndex.State := typesafe_index_unsigned_char_TAG_StateIndex.init (Int8.toUInt8 (Int32.toInt8 (0 : Int32)))
  for _ in [0:2^64] do  -- C loop without a constant trip count (--general-loops)
    if !(typesafe_index_unsigned_char_TAG_StateIndex.op_lt i'2 (Int8.toUInt8 (Int32.toInt8 (3 : Int32)))) then break
    let (t'9, t'10, t'11) := _update_priority_list s o dev_id
    s := t'9
    o := t'10
    priority := t'11
    let t'12 := i'2
    if AP_ParamT_unsigned_int_3.op_to_unsigned_int s._state._priv_instance[UInt8.toNat (typesafe_index_unsigned_char_TAG_StateIndex.get_int t'12)]!.dev_id == Int32.toUInt32 (0 : Int32) && typesafe_index_unsigned_char_TAG_Priority.op_lt priority (Int8.toUInt8 (Int32.toInt8 (3 : Int32))) then
      let t'13 := i'2
      s := { s with _state._priv_instance := s._state._priv_instance.set! (UInt8.toNat (typesafe_index_unsigned_char_TAG_StateIndex.get_int t'13)) ({ s._state._priv_instance[UInt8.toNat (typesafe_index_unsigned_char_TAG_StateIndex.get_int t'13)]! with registered := true }) }
      let t'14 := i'2
      s := { s with _state._priv_instance := s._state._priv_instance.set! (UInt8.toNat (typesafe_index_unsigned_char_TAG_StateIndex.get_int t'14)) ({ s._state._priv_instance[UInt8.toNat (typesafe_index_unsigned_char_TAG_StateIndex.get_int t'14)]! with priority := priority }) }
      «instance» := typesafe_index_unsigned_char_TAG_StateIndex.op_to_unsigned_char i'2
      return (s, o, «instance», true)
    let (t'15, _) := typesafe_index_unsigned_char_TAG_StateIndex.op_inc_int32_t i'2 (0 : Int32)
    i'2 := t'15
  let (t'17, t'18, t'19) := _update_priority_list s o dev_id
  s := t'17
  o := t'18
  priority := t'19
  let priority_index : typesafe_index_unsigned_char_TAG_StateIndex.State := typesafe_index_unsigned_char_TAG_StateIndex.init (typesafe_index_unsigned_char_TAG_Priority.op_to_unsigned_char priority)
  let t'20 := priority_index
  if !s._state._priv_instance[UInt8.toNat (typesafe_index_unsigned_char_TAG_StateIndex.get_int t'20)]!.registered && typesafe_index_unsigned_char_TAG_Priority.op_lt priority (Int8.toUInt8 (Int32.toInt8 (3 : Int32))) then
    let t'21 := priority_index
    s := { s with _state._priv_instance := s._state._priv_instance.set! (UInt8.toNat (typesafe_index_unsigned_char_TAG_StateIndex.get_int t'21)) ({ s._state._priv_instance[UInt8.toNat (typesafe_index_unsigned_char_TAG_StateIndex.get_int t'21)]! with registered := true }) }
    let t'22 := priority_index
    s := { s with _state._priv_instance := s._state._priv_instance.set! (UInt8.toNat (typesafe_index_unsigned_char_TAG_StateIndex.get_int t'22)) ({ s._state._priv_instance[UInt8.toNat (typesafe_index_unsigned_char_TAG_StateIndex.get_int t'22)]! with priority := priority }) }
    «instance» := typesafe_index_unsigned_char_TAG_StateIndex.op_to_unsigned_char priority_index
    return (s, o, «instance», true)
  let mut i'3 : typesafe_index_unsigned_char_TAG_StateIndex.State := typesafe_index_unsigned_char_TAG_StateIndex.init (Int8.toUInt8 (Int32.toInt8 (0 : Int32)))
  for _ in [0:2^64] do  -- C loop without a constant trip count (--general-loops)
    if !(typesafe_index_unsigned_char_TAG_StateIndex.op_lt i'3 (Int8.toUInt8 (Int32.toInt8 (3 : Int32)))) then break
    let (t'23, t'24, t'25) := _update_priority_list s o dev_id
    s := t'23
    o := t'24
    priority := t'25
    let t'26 := i'3
    if !s._state._priv_instance[UInt8.toNat (typesafe_index_unsigned_char_TAG_StateIndex.get_int t'26)]!.registered && typesafe_index_unsigned_char_TAG_Priority.op_lt priority (Int8.toUInt8 (Int32.toInt8 (3 : Int32))) then
      let t'27 := i'3
      s := { s with _state._priv_instance := s._state._priv_instance.set! (UInt8.toNat (typesafe_index_unsigned_char_TAG_StateIndex.get_int t'27)) ({ s._state._priv_instance[UInt8.toNat (typesafe_index_unsigned_char_TAG_StateIndex.get_int t'27)]! with registered := true }) }
      let t'28 := i'3
      s := { s with _state._priv_instance := s._state._priv_instance.set! (UInt8.toNat (typesafe_index_unsigned_char_TAG_StateIndex.get_int t'28)) ({ s._state._priv_instance[UInt8.toNat (typesafe_index_unsigned_char_TAG_StateIndex.get_int t'28)]! with priority := priority }) }
      «instance» := typesafe_index_unsigned_char_TAG_StateIndex.op_to_unsigned_char i'3
      return (s, o, «instance», true)
    let (t'29, _) := typesafe_index_unsigned_char_TAG_StateIndex.op_inc_int32_t i'3 (0 : Int32)
    i'3 := t'29
  if UInt8.toUInt64 s._unreg_compass_count ≥ (5 : UInt64) then
    return (s, o, «instance», false)
  for i'4' in [0:5] do
    let i'4 : UInt8 := Nat.toUInt8 i'4'
    if AP_ParamT_unsigned_int_3.op_to_unsigned_int s.extra_dev_id[UInt8.toNat i'4]! == dev_id then
      if UInt32.toInt32 (UInt8.toUInt32 i'4) ≥ UInt32.toInt32 (UInt8.toUInt32 s._unreg_compass_count) then
        s := { s with _unreg_compass_count := Int8.toUInt8 (Int32.toInt8 (UInt32.toInt32 (UInt8.toUInt32 i'4) + (1 : Int32))) }
      «instance» := Int8.toUInt8 (Int32.toInt8 (UInt32.toInt32 (UInt8.toUInt32 i'4) + (3 : Int32)))
      return (s, o, «instance», false)
    else if AP_ParamT_unsigned_int_3.op_to_unsigned_int s.extra_dev_id[UInt8.toNat i'4]! == Int32.toUInt32 (0 : Int32) then
      let t'31 := s._unreg_compass_count
      s := { s with _unreg_compass_count := s._unreg_compass_count + (1 : UInt8) }
      s := { s with extra_dev_id := s.extra_dev_id.set! (UInt8.toNat t'31) (AP_ParamT_unsigned_int_3.set s.extra_dev_id[UInt8.toNat t'31]! dev_id) }
      «instance» := Int8.toUInt8 (Int32.toInt8 (UInt32.toInt32 (UInt8.toUInt32 i'4) + (3 : Int32)))
      return (s, o, «instance», false)
  return (s, o, «instance», false)

/-- C++ `void Compass::set_offsets(uint8_t i, const Vector3f & offsets)`, `AP_Compass/AP_Compass.cpp:1836-1844`. -/
def set_offsets (s : State) (i : UInt8) (offsets : Vector3f.State) : State := Id.run do
  let mut s := s
  let id : typesafe_index_unsigned_char_TAG_StateIndex.State := _get_state_id s (typesafe_index_unsigned_char_TAG_Priority.init i)
  if typesafe_index_unsigned_char_TAG_StateIndex.op_lt id (Int8.toUInt8 (Int32.toInt8 (3 : Int32))) then
    let t'1 := id
    s := { s with _state._priv_instance := s._state._priv_instance.set! (UInt8.toNat (typesafe_index_unsigned_char_TAG_StateIndex.get_int t'1)) ({ s._state._priv_instance[UInt8.toNat (typesafe_index_unsigned_char_TAG_StateIndex.get_int t'1)]! with offset := AP_ParamV_Vector3_float_5.set s._state._priv_instance[UInt8.toNat (typesafe_index_unsigned_char_TAG_StateIndex.get_int t'1)]!.offset offsets }) }
  return s

end Compass

namespace Compass

/-- C++ `Compass::Compass()`, `AP_Compass/AP_Compass.cpp:683-693`. -/
def construct : State := Id.run do
  let mut s : State := {}
  s := { s with _per_motor := Compass_PerMotor.init }
  if false /- C++ `_singleton != nullptr` -/ then
    pure ()  -- C++ `AP_HAL::panic(...)`: left out (--drop)
    return s
  pure ()  -- C++ `_singleton = this`: the pointer is the class's one World object (--world)
  let t'1 := (Binary32.ofBits 0x00000000 /- (float)0 -/)
  s := { s with _state._priv_instance := s._state._priv_instance.set! 0 ({ s._state._priv_instance[0]! with offset._value := ({ x := t'1, y := t'1, z := t'1 } : Vector3f.State) }) }
  s := { s with _declination._value := (Binary32.ofBits 0x00000000 /- (float)0 -/) }
  s := { s with _use_for_yaw._priv_instance := s._use_for_yaw._priv_instance.set! 0 ({ s._use_for_yaw._priv_instance[0]! with _value := Binary32.toInt8 (Binary32.ofBits 0x3f800000 /- (float)1 -/) }) }
  s := { s with _auto_declination._value := Binary32.toInt8 (Binary32.ofBits 0x3f800000 /- (float)1 -/) }
  s := { s with _motor_comp_type._value := Binary32.toInt8 (Binary32.ofBits 0x00000000 /- (float)0 -/) }
  let t'2 := (Binary32.ofBits 0x00000000 /- (float)0 -/)
  s := { s with _state._priv_instance := s._state._priv_instance.set! 0 ({ s._state._priv_instance[0]! with motor_compensation._value := ({ x := t'2, y := t'2, z := t'2 } : Vector3f.State) }) }
  s := { s with _state._priv_instance := s._state._priv_instance.set! 0 ({ s._state._priv_instance[0]! with orientation._value := Binary32.toInt8 (UInt8.toBinary32 (Rotation.toInt Rotation.ROTATION_NONE)) }) }
  s := { s with _state._priv_instance := s._state._priv_instance.set! 0 ({ s._state._priv_instance[0]! with external._value := Binary32.toInt8 (Binary32.ofBits 0x00000000 /- (float)0 -/) }) }
  let t'3 := (Binary32.ofBits 0x00000000 /- (float)0 -/)
  s := { s with _state._priv_instance := s._state._priv_instance.set! 1 ({ s._state._priv_instance[1]! with offset._value := ({ x := t'3, y := t'3, z := t'3 } : Vector3f.State) }) }
  let t'4 := (Binary32.ofBits 0x00000000 /- (float)0 -/)
  s := { s with _state._priv_instance := s._state._priv_instance.set! 1 ({ s._state._priv_instance[1]! with motor_compensation._value := ({ x := t'4, y := t'4, z := t'4 } : Vector3f.State) }) }
  let t'5 := (Binary32.ofBits 0x00000000 /- (float)0 -/)
  s := { s with _state._priv_instance := s._state._priv_instance.set! 2 ({ s._state._priv_instance[2]! with offset._value := ({ x := t'5, y := t'5, z := t'5 } : Vector3f.State) }) }
  let t'6 := (Binary32.ofBits 0x00000000 /- (float)0 -/)
  s := { s with _state._priv_instance := s._state._priv_instance.set! 2 ({ s._state._priv_instance[2]! with motor_compensation._value := ({ x := t'6, y := t'6, z := t'6 } : Vector3f.State) }) }
  s := { s with _state._priv_instance := s._state._priv_instance.set! 0 ({ s._state._priv_instance[0]! with dev_id._value := Int32.toUInt32 (Binary32.toInt32 (Binary32.ofBits 0x00000000 /- (float)0 -/)) }) }
  s := { s with _state._priv_instance := s._state._priv_instance.set! 1 ({ s._state._priv_instance[1]! with dev_id._value := Int32.toUInt32 (Binary32.toInt32 (Binary32.ofBits 0x00000000 /- (float)0 -/)) }) }
  s := { s with _state._priv_instance := s._state._priv_instance.set! 2 ({ s._state._priv_instance[2]! with dev_id._value := Int32.toUInt32 (Binary32.toInt32 (Binary32.ofBits 0x00000000 /- (float)0 -/)) }) }
  s := { s with _use_for_yaw._priv_instance := s._use_for_yaw._priv_instance.set! 1 ({ s._use_for_yaw._priv_instance[1]! with _value := Binary32.toInt8 (Binary32.ofBits 0x3f800000 /- (float)1 -/) }) }
  s := { s with _state._priv_instance := s._state._priv_instance.set! 1 ({ s._state._priv_instance[1]! with orientation._value := Binary32.toInt8 (UInt8.toBinary32 (Rotation.toInt Rotation.ROTATION_NONE)) }) }
  s := { s with _state._priv_instance := s._state._priv_instance.set! 1 ({ s._state._priv_instance[1]! with external._value := Binary32.toInt8 (Binary32.ofBits 0x00000000 /- (float)0 -/) }) }
  s := { s with _use_for_yaw._priv_instance := s._use_for_yaw._priv_instance.set! 2 ({ s._use_for_yaw._priv_instance[2]! with _value := Binary32.toInt8 (Binary32.ofBits 0x3f800000 /- (float)1 -/) }) }
  s := { s with _state._priv_instance := s._state._priv_instance.set! 2 ({ s._state._priv_instance[2]! with orientation._value := Binary32.toInt8 (UInt8.toBinary32 (Rotation.toInt Rotation.ROTATION_NONE)) }) }
  s := { s with _state._priv_instance := s._state._priv_instance.set! 2 ({ s._state._priv_instance[2]! with external._value := Binary32.toInt8 (Binary32.ofBits 0x00000000 /- (float)0 -/) }) }
  let t'7 := (Binary32.ofBits 0x3f800000 /- (float)1 -/)
  s := { s with _state._priv_instance := s._state._priv_instance.set! 0 ({ s._state._priv_instance[0]! with diagonals._value := ({ x := t'7, y := t'7, z := t'7 } : Vector3f.State) }) }
  let t'8 := (Binary32.ofBits 0x00000000 /- (float)0 -/)
  s := { s with _state._priv_instance := s._state._priv_instance.set! 0 ({ s._state._priv_instance[0]! with offdiagonals._value := ({ x := t'8, y := t'8, z := t'8 } : Vector3f.State) }) }
  let t'9 := (Binary32.ofBits 0x3f800000 /- (float)1 -/)
  s := { s with _state._priv_instance := s._state._priv_instance.set! 1 ({ s._state._priv_instance[1]! with diagonals._value := ({ x := t'9, y := t'9, z := t'9 } : Vector3f.State) }) }
  let t'10 := (Binary32.ofBits 0x00000000 /- (float)0 -/)
  s := { s with _state._priv_instance := s._state._priv_instance.set! 1 ({ s._state._priv_instance[1]! with offdiagonals._value := ({ x := t'10, y := t'10, z := t'10 } : Vector3f.State) }) }
  let t'11 := (Binary32.ofBits 0x3f800000 /- (float)1 -/)
  s := { s with _state._priv_instance := s._state._priv_instance.set! 2 ({ s._state._priv_instance[2]! with diagonals._value := ({ x := t'11, y := t'11, z := t'11 } : Vector3f.State) }) }
  let t'12 := (Binary32.ofBits 0x00000000 /- (float)0 -/)
  s := { s with _state._priv_instance := s._state._priv_instance.set! 2 ({ s._state._priv_instance[2]! with offdiagonals._value := ({ x := t'12, y := t'12, z := t'12 } : Vector3f.State) }) }
  s := { s with _offset_max._value := Int16.toUInt16 (Binary32.toInt16 (Binary32.ofBits 0x44e10000 /- (float)1800 -/)) }
  s := { s with _driver_type_mask._value := Int32.toUInt32 (Binary32.toInt32 (Binary32.ofBits 0x00000000 /- (float)0 -/)) }
  s := { s with _filter_range._value := Int8.toUInt8 (Binary32.toInt8 (Binary32.ofBits 0x00000000 /- (float)0 -/)) }
  s := { s with _priority_did_stored_list._priv_instance := s._priority_did_stored_list._priv_instance.set! 0 ({ s._priority_did_stored_list._priv_instance[0]! with _value := Int32.toUInt32 (Binary32.toInt32 (Binary32.ofBits 0x00000000 /- (float)0 -/)) }) }
  s := { s with _priority_did_stored_list._priv_instance := s._priority_did_stored_list._priv_instance.set! 1 ({ s._priority_did_stored_list._priv_instance[1]! with _value := Int32.toUInt32 (Binary32.toInt32 (Binary32.ofBits 0x00000000 /- (float)0 -/)) }) }
  s := { s with _priority_did_stored_list._priv_instance := s._priority_did_stored_list._priv_instance.set! 2 ({ s._priority_did_stored_list._priv_instance[2]! with _value := Int32.toUInt32 (Binary32.toInt32 (Binary32.ofBits 0x00000000 /- (float)0 -/)) }) }
  s := { s with _enabled._value := Binary32.toInt8 (Binary32.ofBits 0x3f800000 /- (float)1 -/) }
  s := { s with _state._priv_instance := s._state._priv_instance.set! 0 ({ s._state._priv_instance[0]! with scale_factor._value := (Binary32.ofBits 0x00000000 /- (float)0 -/) }) }
  s := { s with _state._priv_instance := s._state._priv_instance.set! 1 ({ s._state._priv_instance[1]! with scale_factor._value := (Binary32.ofBits 0x00000000 /- (float)0 -/) }) }
  s := { s with _state._priv_instance := s._state._priv_instance.set! 2 ({ s._state._priv_instance[2]! with scale_factor._value := (Binary32.ofBits 0x00000000 /- (float)0 -/) }) }
  s := { s with _options._value := Int16.toUInt16 (Binary32.toInt16 (Binary32.ofBits 0x00000000 /- (float)0 -/)) }
  s := { s with extra_dev_id := s.extra_dev_id.set! 0 ({ s.extra_dev_id[0]! with _value := Int32.toUInt32 (Binary32.toInt32 (Binary32.ofBits 0x00000000 /- (float)0 -/)) }) }
  s := { s with extra_dev_id := s.extra_dev_id.set! 1 ({ s.extra_dev_id[1]! with _value := Int32.toUInt32 (Binary32.toInt32 (Binary32.ofBits 0x00000000 /- (float)0 -/)) }) }
  s := { s with extra_dev_id := s.extra_dev_id.set! 2 ({ s.extra_dev_id[2]! with _value := Int32.toUInt32 (Binary32.toInt32 (Binary32.ofBits 0x00000000 /- (float)0 -/)) }) }
  s := { s with extra_dev_id := s.extra_dev_id.set! 3 ({ s.extra_dev_id[3]! with _value := Int32.toUInt32 (Binary32.toInt32 (Binary32.ofBits 0x00000000 /- (float)0 -/)) }) }
  s := { s with extra_dev_id := s.extra_dev_id.set! 4 ({ s.extra_dev_id[4]! with _value := Int32.toUInt32 (Binary32.toInt32 (Binary32.ofBits 0x00000000 /- (float)0 -/)) }) }
  return s

/-! Not emitted, since they have no effect in the model (they write neither the state, the
parameters nor a reference parameter; e.g. they only save parameters):
- C++ `void Compass::probe_i2c_spi_compasses()`, `AP_Compass/AP_Compass.cpp:1414-1488`.
- C++ `void Compass::_detect_runtime()`, `AP_Compass/AP_Compass.cpp:1726-1754`.
-/

end Compass

end Estimator_lib
