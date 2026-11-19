import ArduLean.Musl.powf
import ArduLean.Estimator.libraries.AP_Math.AP_Math
import ArduLean.Estimator.World
import ArduLean.Estimator.libraries.AP_Common.AP_Common
import ArduLean.Estimator.libraries.AP_Param.AP_Param
import ArduLean.Estimator.libraries.SITL.SITL

/-!
ArduPilot `libraries/AP_Compass`, part 1 of 4. Sources: `libraries/AP_Compass/Compass_PerMotor.h`, `libraries/AP_Compass/AP_Compass.h`, `libraries/AP_Compass/Compass_PerMotor.cpp`, `libraries/AP_Compass/AP_Compass_SITL.h`, `libraries/AP_Compass/AP_Compass_Backend.cpp`.

Items of `lean/Estimator_lib.lean` (the estimator translation), unchanged; placed by `tools/split_modules.py` (`ArduLean/Estimator/INDEX.md`).
-/

open FloatLib.Floats (Binary32 Binary64)

set_option maxRecDepth 200000
-- AP_DAL's `const log_RISH old_RISH = _RISH;` read only by WRITE_REPLAY_BLOCK_IFCHANGED, which is `(void)old`
-- without logging (HAL_LOGGING_ENABLED 0): an unused binding, as in the C++
set_option linter.unusedVariables false

namespace Estimator_lib

namespace Compass.mag_state

/-- State of C++ `Compass::mag_state` (`AP_Compass/AP_Compass.h:588-631`): its data members. -/
structure State where
  /-- `AP_Int8 external` of `Compass::mag_state` (`AP_Compass/AP_Compass.h:589`). -/
  external : AP_ParamT_signed_char_1.State := {}
  /-- `bool healthy` of `Compass::mag_state` (`AP_Compass/AP_Compass.h:590`). -/
  healthy : Bool := false
  /-- `bool registered` of `Compass::mag_state` (`AP_Compass/AP_Compass.h:591`). -/
  registered : Bool := false
  /-- `Compass::Priority priority` of `Compass::mag_state` (`AP_Compass/AP_Compass.h:592`). -/
  priority : typesafe_index_unsigned_char_TAG_Priority.State := {}
  /-- `AP_Int8 orientation` of `Compass::mag_state` (`AP_Compass/AP_Compass.h:593`). -/
  orientation : AP_ParamT_signed_char_1.State := {}
  /-- `AP_Vector3f offset` of `Compass::mag_state` (`AP_Compass/AP_Compass.h:594`). -/
  offset : AP_ParamV_Vector3_float_5.State := {}
  /-- `AP_Vector3f diagonals` of `Compass::mag_state` (`AP_Compass/AP_Compass.h:596`). -/
  diagonals : AP_ParamV_Vector3_float_5.State := {}
  /-- `AP_Vector3f offdiagonals` of `Compass::mag_state` (`AP_Compass/AP_Compass.h:597`). -/
  offdiagonals : AP_ParamV_Vector3_float_5.State := {}
  /-- `AP_Float scale_factor` of `Compass::mag_state` (`AP_Compass/AP_Compass.h:599`). -/
  scale_factor : AP_ParamT_float_4.State := {}
  /-- `AP_UInt32 dev_id` of `Compass::mag_state` (`AP_Compass/AP_Compass.h:604`). -/
  dev_id : AP_ParamT_unsigned_int_3.State := {}
  /-- `uint32_t detected_dev_id` of `Compass::mag_state` (`AP_Compass/AP_Compass.h:606`). -/
  detected_dev_id : UInt32 := (0 : UInt32)
  /-- `uint32_t expected_dev_id` of `Compass::mag_state` (`AP_Compass/AP_Compass.h:608`). -/
  expected_dev_id : UInt32 := (0 : UInt32)
  /-- `AP_Vector3f motor_compensation` of `Compass::mag_state` (`AP_Compass/AP_Compass.h:611`). -/
  motor_compensation : AP_ParamV_Vector3_float_5.State := {}
  /-- `Vector3f motor_offset` of `Compass::mag_state` (`AP_Compass/AP_Compass.h:614`). -/
  motor_offset : Vector3f.State := {}
  /-- `Vector3f field` of `Compass::mag_state` (`AP_Compass/AP_Compass.h:617`). -/
  field : Vector3f.State := {}
  /-- `uint32_t last_update_ms` of `Compass::mag_state` (`AP_Compass/AP_Compass.h:620`). -/
  last_update_ms : UInt32 := (0 : UInt32)
  /-- `uint32_t last_update_usec` of `Compass::mag_state` (`AP_Compass/AP_Compass.h:621`). -/
  last_update_usec : UInt32 := (0 : UInt32)
  /-- `enum Rotation rotation` of `Compass::mag_state` (`AP_Compass/AP_Compass.h:624`). -/
  rotation : Rotation := Rotation.ROTATION_NONE
  /-- `Vector3f accum` of `Compass::mag_state` (`AP_Compass/AP_Compass.h:627`). -/
  accum : Vector3f.State := {}
  /-- `uint32_t accum_count` of `Compass::mag_state` (`AP_Compass/AP_Compass.h:628`). -/
  accum_count : UInt32 := (0 : UInt32)
deriving Inhabited

end Compass.mag_state

namespace Compass_PerMotor

/-- State of C++ `Compass_PerMotor` (`AP_Compass/Compass_PerMotor.h:12-65`): its data members. -/
structure State where
  /-- `AP_Int8 enable` of `Compass_PerMotor` (`AP_Compass/Compass_PerMotor.h:34`). -/
  enable : AP_ParamT_signed_char_1.State := {}
  /-- `AP_Float expo` of `Compass_PerMotor` (`AP_Compass/Compass_PerMotor.h:35`). -/
  expo : AP_ParamT_float_4.State := {}
  /-- `AP_Vector3f compensation[4]` of `Compass_PerMotor` (`AP_Compass/Compass_PerMotor.h:36`). -/
  compensation : Array AP_ParamV_Vector3_float_5.State := Array.replicate 4 {}
  /-- `Vector3f base_field` of `Compass_PerMotor` (`AP_Compass/Compass_PerMotor.h:39`). -/
  base_field : Vector3f.State := {}
  /-- `Vector3f field_sum[4]` of `Compass_PerMotor` (`AP_Compass/Compass_PerMotor.h:42`). -/
  field_sum : Array Vector3f.State := Array.replicate 4 {}
  /-- `float output_sum[4]` of `Compass_PerMotor` (`AP_Compass/Compass_PerMotor.h:45`). -/
  output_sum : Array Binary32 := Array.replicate 4 (Binary32.ofBits 0x00000000 /- 0.0 -/)
  /-- `uint16_t count[4]` of `Compass_PerMotor` (`AP_Compass/Compass_PerMotor.h:48`). -/
  count : Array UInt16 := Array.replicate 4 (0 : UInt16)
  /-- `uint32_t start_ms[4]` of `Compass_PerMotor` (`AP_Compass/Compass_PerMotor.h:51`). -/
  start_ms : Array UInt32 := Array.replicate 4 (0 : UInt32)
  /-- `float voltage` of `Compass_PerMotor` (`AP_Compass/Compass_PerMotor.h:54`). -/
  voltage : Binary32 := (Binary32.ofBits 0x00000000 /- 0.0 -/)
  /-- `bool running` of `Compass_PerMotor` (`AP_Compass/Compass_PerMotor.h:57`). -/
  running : Bool := false
  /-- `bool have_motor_map` of `Compass_PerMotor` (`AP_Compass/Compass_PerMotor.h:63`). -/
  have_motor_map : Bool := false
  /-- `uint8_t motor_map[4]` of `Compass_PerMotor` (`AP_Compass/Compass_PerMotor.h:64`). -/
  motor_map : Array UInt8 := Array.replicate 4 (0 : UInt8)
deriving Inhabited

/-- Values C++ `Compass_PerMotor` reads from objects outside the translation (--boundary): one field per distinct read, in first-use order. -/
structure Inputs where
  /-- `SRV_Channels.find_channel(function, chan) writes chan` (first read at `AP_Compass/Compass_PerMotor.cpp:105`). -/
  find_channel_chan : UInt8 := (0 : UInt8)
  /-- `SRV_Channels.find_channel(k_motor1)` (first read at `AP_Compass/Compass_PerMotor.cpp:105`). -/
  find_channel_k_motor1 : Bool := false
  /-- `SRV_Channels.find_channel(k_motor2)` (first read at `AP_Compass/Compass_PerMotor.cpp:106`). -/
  find_channel_k_motor2 : Bool := false
  /-- `SRV_Channels.find_channel(k_motor3)` (first read at `AP_Compass/Compass_PerMotor.cpp:107`). -/
  find_channel_k_motor3 : Bool := false
  /-- `SRV_Channels.find_channel(k_motor4)` (first read at `AP_Compass/Compass_PerMotor.cpp:108`). -/
  find_channel_k_motor4 : Bool := false
  /-- `hal.rcout.read_last_sent(...) for each motor_map[motor]` (first read at `AP_Compass/Compass_PerMotor.cpp:117`). -/
  read_last_sent_at : Array UInt16 := Array.replicate 0 (0 : UInt16)
  /-- `hal.rcout.scale_esc_to_unity(...) for each pwm` (first read at `AP_Compass/Compass_PerMotor.cpp:120`). -/
  scale_esc_to_unity_at : Array Binary32 := Array.replicate 0 (Binary32.ofBits 0x00000000 /- 0.0 -/)
deriving Inhabited

end Compass_PerMotor

namespace AP_Compass_SITL

/-- State of C++ `AP_Compass_SITL` (`AP_Compass/AP_Compass_SITL.h:14-27`): its data members; base classes flattened, base first: `AP_Compass_Backend`. -/
structure State where
  /-- `uint8_t instance` of `AP_Compass_Backend` (`AP_Compass/AP_Compass_Backend.h:97`). -/
  «instance» : UInt8 := (0 : UInt8)
  /-- `float _mean_field_length` of `AP_Compass_Backend` (`AP_Compass/AP_Compass_Backend.h:157`). -/
  _mean_field_length : Binary32 := (Binary32.ofBits 0x00000000 /- 0.0 -/)
  /-- `uint32_t _error_count` of `AP_Compass_Backend` (`AP_Compass/AP_Compass_Backend.h:159`). -/
  _error_count : UInt32 := (0 : UInt32)
  /-- `SITL::SIM * _sitl` of `AP_Compass_SITL` (`AP_Compass/AP_Compass_SITL.h:19`). -/
  _sitl : WPtr := WPtr.null
  /-- `uint8_t sitl_instance` of `AP_Compass_SITL` (`AP_Compass/AP_Compass_SITL.h:23`). -/
  sitl_instance : UInt8 := (0 : UInt8)
  /-- `SITL::CompassSim _compass_sim` of `AP_Compass_SITL` (`AP_Compass/AP_Compass_SITL.h:26`). -/
  _compass_sim : SITL.CompassSim.State := {}
deriving Inhabited

/-- Values C++ `AP_Compass_SITL` reads from objects outside the translation (--boundary): one field per distinct read, in first-use order. -/
structure Inputs where
  /-- `AP::battery().current_amps(current, instance) writes current` (first read at `AP_Compass/AP_Compass_Backend.cpp:122`). -/
  current_amps_current : Binary32 := (Binary32.ofBits 0x00000000 /- 0.0 -/)
  /-- `AP::battery().current_amps(0)` (first read at `AP_Compass/AP_Compass_Backend.cpp:122`). -/
  current_amps_0 : Bool := false
deriving Inhabited

end AP_Compass_SITL

namespace Compass_PerMotor

/-- C++ `bool Compass_PerMotor::enabled() const`, `AP_Compass/Compass_PerMotor.h:18-20`. -/
def enabled (s : State) : Bool := Id.run do
  return Int8.toInt32 (AP_ParamT_signed_char_1.get_void s.enable) != (0 : Int32)

/-- C++ `float Compass_PerMotor::scaled_output(uint8_t motor)`, `AP_Compass/Compass_PerMotor.cpp:102-132`. -/
def scaled_output (s : State) (inp : Inputs) (motor : UInt8) : State × Binary32 := Id.run do
  let mut s := s
  if !s.have_motor_map then
    s := { s with motor_map := s.motor_map.set! 0 inp.find_channel_chan }
    let mut t'1 := inp.find_channel_k_motor1
    if t'1 then
      s := { s with motor_map := s.motor_map.set! 1 inp.find_channel_chan }
      t'1 := inp.find_channel_k_motor2
    let mut t'2 := t'1
    if t'2 then
      s := { s with motor_map := s.motor_map.set! 2 inp.find_channel_chan }
      t'2 := inp.find_channel_k_motor3
    let mut t'3 := t'2
    if t'3 then
      s := { s with motor_map := s.motor_map.set! 3 inp.find_channel_chan }
      t'3 := inp.find_channel_k_motor4
    if t'3 then
      s := { s with have_motor_map := true }
  if !s.have_motor_map then
    return (s, (Binary32.ofBits 0x00000000 /- 0 -/))
  let pwm : UInt16 := (inp.read_last_sent_at.getD (UInt8.toNat s.motor_map[UInt8.toNat motor]!) (0 : UInt16))
  let mut output : Binary32 := ((inp.scale_esc_to_unity_at.getD (UInt16.toNat pwm) (Binary32.ofBits 0x00000000 /- 0.0 -/)) + (Binary32.ofBits 0x3f800000 /- 1 -/)) * (Binary32.ofBits 0x3f000000 /- 0.5f -/)
  if output ≤ (Binary32.ofBits 0x00000000 /- 0 -/) then
    return (s, (Binary32.ofBits 0x00000000 /- 0 -/))
  output := output * s.voltage
  output := Musl.powf.powf output (AP_ParamT_float_4.op_to_float s.expo)
  return (s, output)

end Compass_PerMotor

namespace Compass_PerMotor

/-- C++ `void Compass_PerMotor::compensate(Vector3f & offset)`, `AP_Compass/Compass_PerMotor.cpp:215-231`. -/
def compensate (s : State) (inp : Inputs) (offset : Vector3f.State) : State × Vector3f.State := Id.run do
  let mut s := s
  let mut offset := offset
  offset := Vector3f.zero offset
  if s.running then
    return (s, offset)
  for i' in [0:4] do
    let i : UInt8 := Nat.toUInt8 i'
    let (t'1, t'2) := scaled_output s inp i
    s := t'1
    let output : Binary32 := t'2
    let (t'3, _) := Vector3f.op_add_assign offset (Vector3f.op_mul_float s.compensation[UInt8.toNat i]!._value output)
    offset := t'3
  return (s, offset)

end Compass_PerMotor

/-- C++ `const float FILTER_KOEF_compass`, `AP_Compass/AP_Compass_Backend.cpp:255`. -/
def FILTER_KOEF_compass : Binary32 := (Binary32.ofBits 0x3dcccccd /- 0.1f -/)

namespace AP_Compass_SITL

/-- C++ `AP_Compass_Backend::AP_Compass_Backend()`, `AP_Compass/AP_Compass_Backend.cpp:14-17` (a member of `AP_Compass_Backend`, translated for `AP_Compass_SITL`). -/
def AP_Compass_Backend.init (s : State) : State := Id.run do
  let mut s := s
  return s

end AP_Compass_SITL

namespace Compass_PerMotor

/-- C++ `void Compass_PerMotor::set_voltage(float _voltage)`, `AP_Compass/Compass_PerMotor.h:22-25`. -/
def set_voltage (s : State) (_voltage : Binary32) : State := Id.run do
  let mut s := s
  s := { s with voltage := (Binary32.ofBits 0x3f666666 /- 0.9f -/) * s.voltage + (Binary32.ofBits 0x3dcccccd /- 0.1f -/) * _voltage }
  return s

end Compass_PerMotor

namespace Compass_PerMotor

/-- C++ `Compass_PerMotor::Compass_PerMotor(Compass & _compass)`, `AP_Compass/Compass_PerMotor.cpp:95-99`. -/
def init : State := Id.run do
  let mut s : State := {}
  s := { s with base_field := Vector3f.init_void }
  s := { s with enable._value := Binary32.toInt8 (Binary32.ofBits 0x00000000 /- (float)0 -/) }
  s := { s with expo._value := (Binary32.ofBits 0x3f266666 /- (float)5854679515581645/9007199254740992 -/) }
  let t'1 := (Binary32.ofBits 0x00000000 /- (float)0 -/)
  s := { s with compensation := s.compensation.set! 0 ({ s.compensation[0]! with _value := ({ x := t'1, y := t'1, z := t'1 } : Vector3f.State) }) }
  let t'2 := (Binary32.ofBits 0x00000000 /- (float)0 -/)
  s := { s with compensation := s.compensation.set! 1 ({ s.compensation[1]! with _value := ({ x := t'2, y := t'2, z := t'2 } : Vector3f.State) }) }
  let t'3 := (Binary32.ofBits 0x00000000 /- (float)0 -/)
  s := { s with compensation := s.compensation.set! 2 ({ s.compensation[2]! with _value := ({ x := t'3, y := t'3, z := t'3 } : Vector3f.State) }) }
  let t'4 := (Binary32.ofBits 0x00000000 /- (float)0 -/)
  s := { s with compensation := s.compensation.set! 3 ({ s.compensation[3]! with _value := ({ x := t'4, y := t'4, z := t'4 } : Vector3f.State) }) }
  return s

end Compass_PerMotor

namespace AP_Compass_SITL

/-! Not emitted, since they have no effect in the model (they write neither the state, the
parameters nor a reference parameter; e.g. they only save parameters):
- C++ `void AP_Compass_Backend::publish_raw_field(const Vector3f & mag)`, `AP_Compass/AP_Compass_Backend.cpp:59-72` (a member of `AP_Compass_Backend`, translated for `AP_Compass_SITL`).
-/

end AP_Compass_SITL

end Estimator_lib
