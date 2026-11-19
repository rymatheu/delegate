import ArduLean.Runtime.CFloat
import ArduLean.Estimator.mavlink.mavlink
import ArduLean.Estimator.libraries.AP_Math.AP_Math
import ArduLean.Estimator.World
import ArduLean.Estimator.libraries.AP_Common.AP_Common
import ArduLean.Estimator.libraries.AP_Param.AP_Param
import ArduLean.Estimator.libraries.AP_RTC.AP_RTC
import ArduLean.Estimator.libraries.AP_GPS.AP_GPS
import ArduLean.Estimator.World_2
import ArduLean.Estimator.libraries.AP_Param.AP_Param_2
import ArduLean.Estimator.World_3
import ArduLean.Estimator.libraries.AP_RTC.AP_RTC_2

/-!
ArduPilot `libraries/AP_GPS`, part 2 of 2. Sources: `libraries/AP_GPS/AP_GPS.cpp`, `libraries/AP_GPS/GPS_Backend.h`, `libraries/AP_GPS/GPS_Backend.cpp`, `libraries/AP_GPS/AP_GPS.h`, `libraries/AP_GPS/AP_GPS_SITL.h`.

Items of `lean/Estimator_lib.lean` (the estimator translation), unchanged; placed by `tools/split_modules.py` (`ArduLean/Estimator/INDEX.md`).
-/

open FloatLib.Floats (Binary32 Binary64)

set_option maxRecDepth 200000
-- AP_DAL's `const log_RISH old_RISH = _RISH;` read only by WRITE_REPLAY_BLOCK_IFCHANGED, which is `(void)old`
-- without logging (HAL_LOGGING_ENABLED 0): an unused binding, as in the C++
set_option linter.unusedVariables false

namespace Estimator_lib

namespace AP_GPS

/-- C++ `bool AP_GPS::get_lag(uint8_t instance, float & lag_sec) const`, `AP_GPS/AP_GPS.cpp:1718-1751`. -/
def get_lag_uint8_t_float (s : State) (w : World) («instance» : UInt8) (lag_sec : Binary32) : Binary32 × Bool := Id.run do
  let mut lag_sec := lag_sec
  lag_sec := (Binary32.ofBits 0x3dcccccd /- 0.1f -/)
  if UInt32.toInt32 (UInt8.toUInt32 «instance») ≥ ((2 : Int32) + (1 : Int32)) then
    return (lag_sec, false)
  if Int16.toInt32 (AP_ParamT_short_2.op_to_short s.params[UInt8.toNat «instance»]!.delay_ms) > (0 : Int32) then
    lag_sec := (Binary32.ofBits 0x3a83126f /- 0.001f -/) * Int16.toBinary32 (AP_ParamT_short_2.op_to_short s.params[UInt8.toNat «instance»]!.delay_ms)
    return (lag_sec, true)
  else if s.drivers[UInt8.toNat «instance»]! == WPtr.null || s.state[UInt8.toNat «instance»]!.status == AP_GPS_FixType.NO_GPS then
    let type : AP_Enum_AP_GPS_GPS_Type.State := s.params[UInt8.toNat «instance»]!.type
    if UInt32.toInt32 (AP_GPS.GPS_Type.toInt (AP_Enum_AP_GPS_GPS_Type.op_to_AP_GPS_GPS_Type type)) == UInt32.toInt32 (AP_GPS.GPS_Type.toInt AP_GPS.GPS_Type.GPS_TYPE_NONE) then
      lag_sec := (Binary32.ofBits 0x00000000 /- 0.0f -/)
      return (lag_sec, true)
    return (lag_sec, UInt32.toInt32 (AP_GPS.GPS_Type.toInt (AP_Enum_AP_GPS_GPS_Type.op_to_AP_GPS_GPS_Type type)) == UInt32.toInt32 (AP_GPS.GPS_Type.toInt AP_GPS.GPS_Type.GPS_TYPE_AUTO))
  else
    let t'1 := (WPtr.index s.drivers[UInt8.toNat «instance»]!)
    let (t'2, t'3) := AP_GPS_SITL.get_lag lag_sec
    lag_sec := t'2
    return (lag_sec, t'3)

/-- C++ `const Vector3f & AP_GPS::velocity(uint8_t instance) const`, `AP_GPS/AP_GPS.h:374-376`. -/
def velocity_uint8_t (s : State) («instance» : UInt8) : Vector3f.State := Id.run do
  return s.state[UInt8.toNat «instance»]!.velocity

/-- C++ `GPS_Type AP_GPS::get_type(uint8_t instance) const`, `AP_GPS/AP_GPS.h:593-595`. -/
def get_type (s : State) («instance» : UInt8) : AP_GPS.GPS_Type := Id.run do
  return if UInt8.toUInt64 «instance» ≥ (3 : UInt64) then AP_GPS.GPS_Type.GPS_TYPE_NONE else AP_Enum_AP_GPS_GPS_Type.op_to_AP_GPS_GPS_Type s.params[UInt8.toNat «instance»]!.type

/-- C++ `bool AP_GPS::is_rtk_base(uint8_t instance) const`, `AP_GPS/AP_GPS.cpp:1968-1978`. -/
def is_rtk_base (s : State) («instance» : UInt8) : Bool := Id.run do
  match get_type s «instance» with
  | .GPS_TYPE_UBLOX_RTK_BASE | .GPS_TYPE_UAVCAN_RTK_BASE =>
    return true
  | _ =>
    pure ()
  return false

/-- C++ `bool AP_GPS::is_rtk_rover(uint8_t instance) const`, `AP_GPS/AP_GPS.cpp:1980-1990`. -/
def is_rtk_rover (s : State) («instance» : UInt8) : Bool := Id.run do
  match get_type s «instance» with
  | .GPS_TYPE_UBLOX_RTK_ROVER | .GPS_TYPE_UAVCAN_RTK_ROVER =>
    return true
  | _ =>
    pure ()
  return false

/-- C++ `uint8_t AP_GPS::yaw_source_instance(uint8_t instance) const`, `AP_GPS/AP_GPS.cpp:1996-2005`. -/
def yaw_source_instance (s : State) («instance» : UInt8) : UInt8 := Id.run do
  let mut «instance» := «instance»
  if is_rtk_base s «instance» && is_rtk_rover s (Int8.toUInt8 (Int32.toInt8 (UInt32.toInt32 (UInt8.toUInt32 «instance») ^^^ (1 : Int32)))) then
    «instance» := Int8.toUInt8 (Int32.toInt8 (UInt32.toInt32 (UInt8.toUInt32 «instance») ^^^ (1 : Int32)))
  return «instance»

/-- C++ `bool AP_GPS::have_gps_yaw(uint8_t instance) const`, `AP_GPS/AP_GPS.h:485-487`. -/
def have_gps_yaw_uint8_t (s : State) («instance» : UInt8) : Bool := Id.run do
  return !s._force_disable_gps_yaw && s.state[UInt8.toNat «instance»]!.have_gps_yaw

/-- C++ `bool AP_GPS::gps_yaw_deg(uint8_t instance, float & yaw_deg, float & accuracy_deg, uint32_t & time_ms) const`, `AP_GPS/AP_GPS.cpp:2010-2034`. -/
def gps_yaw_deg_uint8_t_float2_uint32_t (s : State) (w : World) («instance» : UInt8) (yaw_deg : Binary32) (accuracy_deg : Binary32) (time_ms : UInt32) : Binary32 × Binary32 × UInt32 × Bool := Id.run do
  let mut «instance» := «instance»
  let mut yaw_deg := yaw_deg
  let mut accuracy_deg := accuracy_deg
  let mut time_ms := time_ms
  «instance» := yaw_source_instance s «instance»
  if !(have_gps_yaw_uint8_t s «instance») then
    return (yaw_deg, accuracy_deg, time_ms, false)
  yaw_deg := s.state[UInt8.toNat «instance»]!.gps_yaw
  time_ms := s.state[UInt8.toNat «instance»]!.gps_yaw_time_ms
  let mut lag_s : Binary32 := (Binary32.ofBits 0x00000000 /- 0.0 -/)  -- uninitialized in C++; assigned before every read
  let (t'1, t'2) := get_lag_uint8_t_float s w «instance» lag_s
  lag_s := t'1
  if t'2 then
    let lag_ms : UInt32 := Binary32.toUInt32 (lag_s * (Binary32.ofBits 0x447a0000 /- 1000 -/))
    time_ms := time_ms - lag_ms
  if s.state[UInt8.toNat «instance»]!.have_gps_yaw_accuracy then
    accuracy_deg := s.state[UInt8.toNat «instance»]!.gps_yaw_accuracy
  else
    accuracy_deg := (Binary32.ofBits 0x41200000 /- 10 -/)
  return (yaw_deg, accuracy_deg, time_ms, true)

end AP_GPS

namespace AP_GPS

/-- C++ `const Location & AP_GPS::location(uint8_t instance) const`, `AP_GPS/AP_GPS.h:338-340`. -/
def location_uint8_t (s : State) («instance» : UInt8) : Location.State := Id.run do
  return s.state[UInt8.toNat «instance»]!.location

/-- C++ `const Location & AP_GPS::location() const`, `AP_GPS/AP_GPS.h:341-343`. -/
def location_void (s : State) : Location.State := Id.run do
  return location_uint8_t s s.primary_instance

/-- C++ `uint8_t AP_GPS::num_sats() const`, `AP_GPS/AP_GPS.h:414-416`. -/
def num_sats_void (s : State) : UInt8 := Id.run do
  return num_sats_uint8_t s s.primary_instance

/-- C++ `const Vector3f & AP_GPS::velocity() const`, `AP_GPS/AP_GPS.h:377-379`. -/
def velocity_void (s : State) : Vector3f.State := Id.run do
  return velocity_uint8_t s s.primary_instance

end AP_GPS

namespace AP_GPS

/-- C++ `bool AP_GPS::get_lag(float & lag_sec) const`, `AP_GPS/AP_GPS.h:502-504`. -/
def get_lag_float (s : State) (w : World) (lag_sec : Binary32) : Binary32 × Bool := Id.run do
  let mut lag_sec := lag_sec
  let (t'1, t'2) := get_lag_uint8_t_float s w s.primary_instance lag_sec
  lag_sec := t'1
  return (lag_sec, t'2)

end AP_GPS

namespace AP_GPS

-- not read in the Lean: i
set_option linter.unusedVariables false in
/-- C++ `void AP_GPS::init()`, `AP_GPS/AP_GPS.cpp:311-351`. -/
def init (s : State) (inp : Inputs) : State := Id.run do
  let mut s := s
  if !inp.params_0_type_configured then  -- C++ `params[0].type.set_default(...)`: set unless configured in storage (an input)
    s := { s with params := s.params.set! 0 ({ s.params[0]! with type._value := Int32.toInt8 (1 : Int32) }) }
  for i' in [0:2] do
    let i : UInt8 := Nat.toUInt8 i'
    pure ()  -- C++ `AP_Param::convert_parameter_width(...)`: left out (--drop)
  pure ()  -- C++ `AP_GPS::convert_parameters(...)`: left out (--drop)
  let mut uart_idx : UInt8 := Int8.toUInt8 (Int32.toInt8 (0 : Int32))
  let mut i'2 : UInt8 := Int8.toUInt8 (Int32.toInt8 (0 : Int32))
  for _ in [0:2^64] do  -- C loop without a constant trip count (--general-loops)
    if !(decide (UInt8.toUInt64 i'2 < (3 : UInt64)) && decide (UInt8.toUInt64 i'2 < (2 : UInt64))) then break
    if needs_uart (AP_Enum_AP_GPS_GPS_Type.op_to_AP_GPS_GPS_Type s.params[UInt8.toNat i'2]!.type) then
      s := { s with _port := s._port.set! (UInt8.toNat i'2) (if (inp.find_serial_found_SerialProtocol_GPS_at1.getD (UInt8.toNat uart_idx) false) then WPtr.est_uart else WPtr.null) }
      uart_idx := uart_idx + (1 : UInt8)
    i'2 := i'2 + (1 : UInt8)
  s := { s with _last_instance_swap_ms := Int32.toUInt32 (0 : Int32) }
  for i'3' in [0:3] do
    let i'3 : UInt8 := Nat.toUInt8 i'3'
    s := { s with state := s.state.set! (UInt8.toNat i'3) ({ s.state[UInt8.toNat i'3]! with «instance» := i'3 }) }
  for i'4' in [0:3] do
    let i'4 : UInt8 := Nat.toUInt8 i'4'
    if decide (Int16.toInt32 (AP_ParamT_short_2.op_to_short s.params[UInt8.toNat i'4]!.rate_ms) ≤ (0 : Int32)) || decide (Int16.toInt32 (AP_ParamT_short_2.op_to_short s.params[UInt8.toNat i'4]!.rate_ms) > (200 : Int32)) then
      s := { s with params := s.params.set! (UInt8.toNat i'4) ({ s.params[UInt8.toNat i'4]! with rate_ms := AP_ParamT_short_2.set s.params[UInt8.toNat i'4]!.rate_ms (Int32.toInt16 (200 : Int32)) }) }
  return s

/-- C++ `enum AP_GPS::GPS_AUTO_CONFIG`, `AP_GPS/AP_GPS.h:798-803`. -/
inductive GPS_AUTO_CONFIG where
  | GPS_AUTO_CONFIG_DISABLE
  | GPS_AUTO_CONFIG_ENABLE_SERIAL_ONLY
  | GPS_AUTO_CONFIG_ENABLE_ALL
  | GPS_AUTO_CLEAR_CONFIG_UBLOX_SERIAL_ONLY
deriving DecidableEq, Inhabited

/-- The value of each enumerator of `AP_GPS::GPS_AUTO_CONFIG` (underlying type `uint32_t`). -/
def GPS_AUTO_CONFIG.toInt : GPS_AUTO_CONFIG → UInt32
  | .GPS_AUTO_CONFIG_DISABLE => (0 : UInt32)
  | .GPS_AUTO_CONFIG_ENABLE_SERIAL_ONLY => (1 : UInt32)
  | .GPS_AUTO_CONFIG_ENABLE_ALL => (2 : UInt32)
  | .GPS_AUTO_CLEAR_CONFIG_UBLOX_SERIAL_ONLY => (3 : UInt32)

end AP_GPS

namespace AP_GPS_SITL

/-- C++ `AP_GPS_Backend::AP_GPS_Backend(AP_GPS & _gps, AP_GPS::Params & _params, AP_GPS::GPS_State & _state, AP_HAL::UARTDriver * _port)`, `AP_GPS/GPS_Backend.cpp:44-53` (a member of `AP_GPS_Backend`, translated for `AP_GPS_SITL`). -/
def AP_GPS_Backend.init (s : State) (w : World) (_params'i : Nat) (_state'i : Nat) (_port : WPtr) : State × World := Id.run do
  let mut s := s
  let mut w := w
  s := { s with port := _port }
  s := { s with state'i := _state'i }
  s := { s with params'i := _params'i }
  s := { s with jitter_correction := JitterCorrection.init (Int16.toUInt16 (Int32.toInt16 (500 : Int32))) (Int16.toUInt16 (Int32.toInt16 (100 : Int32))) }
  w := { w with gps.state := w.gps.state.set! s.state'i ({ w.gps.state[s.state'i]! with have_speed_accuracy := false }) }
  w := { w with gps.state := w.gps.state.set! s.state'i ({ w.gps.state[s.state'i]! with have_horizontal_accuracy := false }) }
  w := { w with gps.state := w.gps.state.set! s.state'i ({ w.gps.state[s.state'i]! with have_vertical_accuracy := false }) }
  return (s, w)

/-- C++ `AP_GPS_SITL::AP_GPS_Backend(AP_GPS & , AP_GPS::Params & , AP_GPS::GPS_State & , AP_HAL::UARTDriver * )`, `AP_GPS/AP_GPS_SITL.h:29`. -/
def init (w : World) (unnamed'1'i : Nat) (unnamed'2'i : Nat) (unnamed'3 : WPtr) : State × World := Id.run do
  let mut s : State := {}
  let mut w := w
  let (t'1, t'2) := AP_GPS_Backend.init s w unnamed'1'i unnamed'2'i unnamed'3
  w := t'2
  s := t'1
  return (s, w)

end AP_GPS_SITL

namespace AP_GPS

/-- C++ `AP_GPS_Backend * AP_GPS::_detect_instance(uint8_t instance)`, `AP_GPS/AP_GPS.cpp:626-811`. -/
def _detect_instance (s : State) (w : World) («instance» : UInt8) : State × World × WPtr := Id.run do
  let mut s := s
  let mut w := w
  let type : AP_Enum_AP_GPS_GPS_Type.State := s.params[UInt8.toNat «instance»]!.type
  let mut port : WPtr := if UInt8.toUInt64 «instance» < (2 : UInt64) then s._port[UInt8.toNat «instance»]! else WPtr.null
  match AP_Enum_AP_GPS_GPS_Type.op_to_AP_GPS_GPS_Type type with
  | .GPS_TYPE_MAV | .GPS_TYPE_UAVCAN | .GPS_TYPE_UAVCAN_RTK_BASE | .GPS_TYPE_UAVCAN_RTK_ROVER =>
    return (s, w, WPtr.null)
  | _ =>
    pure ()
  if port == WPtr.null then
    return (s, w, WPtr.null)
  s := { s with detect_state := s.detect_state.set! (UInt8.toNat «instance») ({ s.detect_state[UInt8.toNat «instance»]! with auto_detected_baud := true }) }
  let now : UInt32 := Estimator_lib.millis w
  if now - s.detect_state[UInt8.toNat «instance»]!.last_baud_change_ms > Int32.toUInt32 (1200 : Int32) then
    if s.detect_state[UInt8.toNat «instance»]!.probe_baud == Int32.toUInt32 (0 : Int32) then
      s := { s with detect_state := s.detect_state.set! (UInt8.toNat «instance») ({ s.detect_state[UInt8.toNat «instance»]! with probe_baud := EstUART.get_baud_rate w.est_uart }) }
    else
      s := { s with detect_state := s.detect_state.set! (UInt8.toNat «instance») ({ s.detect_state[UInt8.toNat «instance»]! with current_baud := s.detect_state[UInt8.toNat «instance»]!.current_baud + (1 : UInt8) }) }
      if UInt8.toUInt64 s.detect_state[UInt8.toNat «instance»]!.current_baud == (8 : UInt64) then
        s := { s with detect_state := s.detect_state.set! (UInt8.toNat «instance») ({ s.detect_state[UInt8.toNat «instance»]! with current_baud := Int8.toUInt8 (Int32.toInt8 (0 : Int32)) }) }
      s := { s with detect_state := s.detect_state.set! (UInt8.toNat «instance») ({ s.detect_state[UInt8.toNat «instance»]! with probe_baud := _baudrates[UInt8.toNat s.detect_state[UInt8.toNat «instance»]!.current_baud]! }) }
    let mut rx_size : UInt16 := Int16.toUInt16 (Int32.toInt16 (0 : Int32))
    let mut tx_size : UInt16 := Int16.toUInt16 (Int32.toInt16 (0 : Int32))
    if UInt32.toInt32 (AP_GPS.GPS_Type.toInt (AP_Enum_AP_GPS_GPS_Type.op_to_AP_GPS_GPS_Type type)) == UInt32.toInt32 (AP_GPS.GPS_Type.toInt AP_GPS.GPS_Type.GPS_TYPE_UBLOX_RTK_ROVER) then
      tx_size := Int16.toUInt16 (Int32.toInt16 (2048 : Int32))
    if UInt32.toInt32 (AP_GPS.GPS_Type.toInt (AP_Enum_AP_GPS_GPS_Type.op_to_AP_GPS_GPS_Type type)) == UInt32.toInt32 (AP_GPS.GPS_Type.toInt AP_GPS.GPS_Type.GPS_TYPE_UBLOX_RTK_BASE) then
      rx_size := Int16.toUInt16 (Int32.toInt16 (2048 : Int32))
    let t'1 := w.est_uart  -- the object out of the World for the call (--swap-out)
    w := { w with est_uart := default }
    w := { w with est_uart := EstUART.begin_uint32_t_uint16_t2 t'1 s.detect_state[UInt8.toNat «instance»]!.probe_baud rx_size tx_size }
    pure ()  -- C++ `set_flow_control`: no effect in the model
    s := { s with detect_state := s.detect_state.set! (UInt8.toNat «instance») ({ s.detect_state[UInt8.toNat «instance»]! with last_baud_change_ms := now }) }
    if Int8.toInt32 (AP_ParamT_signed_char_1.op_to_signed_char s._auto_config) ≥ UInt32.toInt32 (AP_GPS.GPS_AUTO_CONFIG.toInt AP_GPS.GPS_AUTO_CONFIG.GPS_AUTO_CONFIG_ENABLE_SERIAL_ONLY) then
      pure ()  -- C++ `AP_GPS::send_blob_start(...)`: left out (--drop)
  if Int8.toInt32 (AP_ParamT_signed_char_1.op_to_signed_char s._auto_config) ≥ UInt32.toInt32 (AP_GPS.GPS_AUTO_CONFIG.toInt AP_GPS.GPS_AUTO_CONFIG.GPS_AUTO_CONFIG_ENABLE_SERIAL_ONLY) then
    pure ()  -- C++ `AP_GPS::send_blob_update(...)`: left out (--drop)
  match AP_Enum_AP_GPS_GPS_Type.op_to_AP_GPS_GPS_Type type with
  | .GPS_TYPE_SITL =>
    w := { w with gps := s }  -- this object's state into the World: the call reaches it
    let (t'2, t'3) := AP_GPS_SITL.init w (UInt8.toNat «instance») (UInt8.toNat «instance») port
    w := t'3
    s := w.gps  -- this object's state as the call left it
    let t'4 := w.heap'AP_GPS_SITL.size
    w := { w with heap'AP_GPS_SITL := w.heap'AP_GPS_SITL.push t'2 }
    return (s, w, (WPtr.heap'AP_GPS_SITL t'4))
  | _ =>
    pure ()
  if UInt32.toInt32 (UInt16.toUInt32 s.initblob_state[UInt8.toNat «instance»]!.remaining) != (0 : Int32) then
    return (s, w, WPtr.null)
  let mut bytecount : UInt16 := UInt32.toUInt16 (Estimator_lib.MIN_uint32_t2 (8192 : UInt32) (EstUART.available w.est_uart))
  for _ in [0:2^64] do  -- C loop without a constant trip count (--general-loops)
    let t'5 := bytecount
    bytecount := bytecount - (1 : UInt16)
    if !(decide (UInt32.toInt32 (UInt16.toUInt32 t'5) > (0 : Int32))) then break
    let data : UInt8 := Int8.toUInt8 (Int16.toInt8 (EstUART.read_void))
  return (s, w, WPtr.null)

end AP_GPS

namespace AP_GPS_SITL

/-- C++ `const char * AP_GPS_SITL::name() const`, `AP_GPS/AP_GPS_SITL.h:33`. -/
def name : String := Id.run do
  return "SITL"

/-- C++ `void AP_GPS_Backend::_detection_message(char * buffer, uint8_t buflen) const`, `AP_GPS/GPS_Backend.cpp:129-146` (a member of `AP_GPS_Backend`, translated for `AP_GPS_SITL`). -/
def _detection_message (s : State) (w : World) (buffer : CText) (buflen : UInt8) : CText := Id.run do
  let mut buffer := buffer
  let «instance» : UInt8 := w.gps.state[s.state'i]!.«instance»
  let dstate : AP_GPS.detect_state := w.gps.detect_state[UInt8.toNat «instance»]!
  if dstate.auto_detected_baud then
    buffer := (CText.fmt (UInt8.toUInt64 buflen) "GPS %d: probing for %s at %d baud" #[Sum.inl (Int64.toUInt64 (Int32.toInt64 (UInt32.toInt32 (UInt8.toUInt32 «instance») + (1 : Int32)))), Sum.inr (name), Sum.inl (Int64.toUInt64 (Int32.toInt64 (UInt32.toInt32 dstate.probe_baud)))])
  else
    buffer := (CText.fmt (UInt8.toUInt64 buflen) "GPS %d: specified as %s" #[Sum.inl (Int64.toUInt64 (Int32.toInt64 (UInt32.toInt32 (UInt8.toUInt32 «instance») + (1 : Int32)))), Sum.inr (name)])
  return buffer

/-- C++ `void AP_GPS_Backend::broadcast_gps_type() const`, `AP_GPS/GPS_Backend.cpp:149-154` (a member of `AP_GPS_Backend`, translated for `AP_GPS_SITL`). -/
def broadcast_gps_type (s : State) (w : World) (o : Outputs) : Outputs := Id.run do
  let mut o := o
  let mut buffer : CText := CText.none  -- uninitialized in C++; assigned before every read
  buffer := _detection_message s w buffer (UInt64.toUInt8 (51 : UInt64))
  o := o.push (Output.send_text_snprintf (6 : UInt32) "%s" buffer)
  return o

end AP_GPS_SITL

namespace AP_GPS

/-- C++ `void AP_GPS::detect_instance(uint8_t instance)`, `AP_GPS/AP_GPS.cpp:601-620`. -/
def detect_instance (s : State) (w : World) (o : Outputs) («instance» : UInt8) : State × World × Outputs := Id.run do
  let mut s := s
  let mut w := w
  let mut o := o
  let now : UInt32 := Estimator_lib.millis w
  s := { s with state := s.state.set! (UInt8.toNat «instance») ({ s.state[UInt8.toNat «instance»]! with status := AP_GPS_FixType.NO_GPS }) }
  s := { s with state := s.state.set! (UInt8.toNat «instance») ({ s.state[UInt8.toNat «instance»]! with hdop := Int16.toUInt16 (Int32.toInt16 (65535 : Int32)) }) }
  s := { s with state := s.state.set! (UInt8.toNat «instance») ({ s.state[UInt8.toNat «instance»]! with vdop := Int16.toUInt16 (Int32.toInt16 (65535 : Int32)) }) }
  let (t'1, t'2, t'3) := _detect_instance s w «instance»
  w := t'2
  s := t'1
  let new_gps : WPtr := t'3
  if new_gps == WPtr.null then
    return (s, w, o)
  s := { s with state := s.state.set! (UInt8.toNat «instance») ({ s.state[UInt8.toNat «instance»]! with status := AP_GPS_FixType.NONE }) }
  s := { s with drivers := s.drivers.set! (UInt8.toNat «instance») new_gps }
  s := { s with timing := s.timing.set! (UInt8.toNat «instance») ({ s.timing[UInt8.toNat «instance»]! with last_message_time_ms := now }) }
  s := { s with timing := s.timing.set! (UInt8.toNat «instance») ({ s.timing[UInt8.toNat «instance»]! with delta_time_ms := UInt32.toUInt16 (4000 : UInt32) }) }
  w := { w with gps := s }  -- this object's state into the World: the call reaches it
  o := AP_GPS_SITL.broadcast_gps_type w.heap'AP_GPS_SITL[(WPtr.index new_gps)]! w o
  return (s, w, o)

/-- C++ `void AP_GPS::update_frame_timing_health(uint8_t instance)`, `AP_GPS/AP_GPS.cpp:844-861`. -/
def update_frame_timing_health (s : State) («instance» : UInt8) : State := Id.run do
  let mut s := s
  let gps_max_delta_ms : UInt16 := Int16.toUInt16 (Int32.toInt16 (245 : Int32))
  if UInt32.toInt32 (UInt16.toUInt32 s.timing[UInt8.toNat «instance»]!.delta_time_ms) > UInt32.toInt32 (UInt16.toUInt32 gps_max_delta_ms) then
    s := { s with timing := s.timing.set! (UInt8.toNat «instance») ({ s.timing[UInt8.toNat «instance»]! with delayed_count := s.timing[UInt8.toNat «instance»]!.delayed_count + (1 : UInt8) }) }
  else
    s := { s with timing := s.timing.set! (UInt8.toNat «instance») ({ s.timing[UInt8.toNat «instance»]! with delayed_count := Int8.toUInt8 (Int32.toInt8 (0 : Int32)) }) }
  if UInt32.toInt32 (UInt16.toUInt32 s.timing[UInt8.toNat «instance»]!.delta_time_ms) < (2000 : Int32) then
    if s.timing[UInt8.toNat «instance»]!.average_delta_ms ≤ (Binary32.ofBits 0x00000000 /- 0 -/) then
      s := { s with timing := s.timing.set! (UInt8.toNat «instance») ({ s.timing[UInt8.toNat «instance»]! with average_delta_ms := UInt16.toBinary32 s.timing[UInt8.toNat «instance»]!.delta_time_ms }) }
    else
      s := { s with timing := s.timing.set! (UInt8.toNat «instance») ({ s.timing[UInt8.toNat «instance»]! with average_delta_ms := (Binary32.ofBits 0x3f7ae148 /- 0.98f -/) * s.timing[UInt8.toNat «instance»]!.average_delta_ms + (Binary32.ofBits 0x3ca3d70a /- 0.02f -/) * Int32.toBinary32 (UInt32.toInt32 (UInt16.toUInt32 s.timing[UInt8.toNat «instance»]!.delta_time_ms)) }) }
  return s

/-- C++ `static uint64_t AP_GPS::istate_time_to_epoch_ms(uint16_t gps_week, uint32_t gps_ms)`, `AP_GPS/AP_GPS.cpp:462-466`. -/
def istate_time_to_epoch_ms (gps_week : UInt16) (gps_ms : UInt32) : UInt64 := Id.run do
  let fix_time_ms : UInt64 := ((17000 : UInt64) * (86400 : UInt64) + (52 : UInt64) * (10 : UInt64) * (((7 : UInt64) * (86400 : UInt64)) * (1000 : UInt64)) - (18000 : UInt64)) + UInt16.toUInt64 gps_week * (((7 : UInt64) * (86400 : UInt64)) * (1000 : UInt64)) + UInt32.toUInt64 gps_ms
  return fix_time_ms

end AP_GPS

namespace AP_GPS_SITL

/-- C++ `uint32_t AP_GPS_Backend::get_last_itow_ms() const`, `AP_GPS/GPS_Backend.cpp:58-64` (a member of `AP_GPS_Backend`, translated for `AP_GPS_SITL`). -/
def get_last_itow_ms (s : State) (w : World) : UInt32 := Id.run do
  if !s._have_itow then
    return w.gps.state[s.state'i]!.time_week_ms
  return UInt64.toUInt32 (if (s._pseudo_itow_delta_ms == (0 : Int32)) then UInt32.toUInt64 s._last_itow_ms else ((s._pseudo_itow / (1000 : UInt64)) + Int64.toUInt64 (Int32.toInt64 s._pseudo_itow_delta_ms)))

end AP_GPS_SITL

namespace AP_GPS

/-- C++ `uint64_t AP_GPS::time_epoch_usec(uint8_t instance) const`, `AP_GPS/AP_GPS.cpp:471-486`. -/
def time_epoch_usec_uint8_t (s : State) (w : World) («instance» : UInt8) : World × UInt64 := Id.run do
  let mut w := w
  if (s.state[UInt8.toNat «instance»]!.last_gps_time_ms == Int32.toUInt32 (0 : Int32) && s.state[UInt8.toNat «instance»]!.last_corrected_gps_time_us == Int64.toUInt64 (Int32.toInt64 (0 : Int32))) || UInt32.toInt32 (UInt16.toUInt32 s.state[UInt8.toNat «instance»]!.time_week) == (0 : Int32) then
    return (w, Int64.toUInt64 (Int32.toInt64 (0 : Int32)))
  let mut fix_time_ms : UInt64 := (0 : UInt64)  -- uninitialized in C++; assigned before every read
  if s.state[UInt8.toNat «instance»]!.last_corrected_gps_time_us != Int64.toUInt64 (Int32.toInt64 (0 : Int32)) then
    let t'2 := s.state[UInt8.toNat «instance»]!.time_week
    let t'1 := (WPtr.index s.drivers[UInt8.toNat «instance»]!)
    w := { w with gps := s }  -- this object's state into the World: the call reaches it
    fix_time_ms := istate_time_to_epoch_ms t'2 (AP_GPS_SITL.get_last_itow_ms w.heap'AP_GPS_SITL[t'1]! w)
    return (w, (fix_time_ms * (1000 : UInt64)) + (Estimator_lib.micros64 w - s.state[UInt8.toNat «instance»]!.last_corrected_gps_time_us))
  else
    fix_time_ms := istate_time_to_epoch_ms s.state[UInt8.toNat «instance»]!.time_week s.state[UInt8.toNat «instance»]!.time_week_ms
    return (w, (fix_time_ms + UInt32.toUInt64 (Estimator_lib.millis w - s.state[UInt8.toNat «instance»]!.last_gps_time_ms)) * (1000 : UInt64))

end AP_GPS

namespace AP_GPS_SITL

/-- C++ `bool AP_GPS_SITL::read()`, `reference/hal/sensors_gps.cpp:29-70`. -/
def read (s : State) (w : World) : State × World × Bool := Id.run do
  let mut s := s
  let mut w := w
  if !(Estimator_lib.est_gps_pending w) then
    return (s, w, false)
  let (t'1, t'2) := Estimator_lib.est_gps_take w
  w := t'1
  let gps_record : EstRecord := t'2
  let now : UInt32 := Estimator_lib.millis w
  s := { s with last_update_ms := now }
  let latitude : Binary64 := gps_record.gps_lat_deg
  let longitude : Binary64 := gps_record.gps_lon_deg
  let altitude : Binary32 := Binary64.toBinary32 gps_record.gps_alt_m
  let speedN : Binary64 := gps_record.gps_vn
  let speedE : Binary64 := gps_record.gps_ve
  let speedD : Binary64 := gps_record.gps_vd
  let mut time_week : UInt16 := Int16.toUInt16 (Int32.toInt16 (0 : Int32))
  let (t'3, t'4) := Estimator_lib.gps_time_week_ms w time_week
  time_week := t'3
  let time_week_ms : UInt32 := t'4
  w := { w with gps.state := w.gps.state.set! s.state'i ({ w.gps.state[s.state'i]! with time_week := time_week }) }
  w := { w with gps.state := w.gps.state.set! s.state'i ({ w.gps.state[s.state'i]! with time_week_ms := time_week_ms }) }
  w := { w with gps.state := w.gps.state.set! s.state'i ({ w.gps.state[s.state'i]! with status := AP_GPS_FixType.FIX_3D }) }
  w := { w with gps.state := w.gps.state.set! s.state'i ({ w.gps.state[s.state'i]! with num_sats := Int8.toUInt8 (Int32.toInt8 (15 : Int32)) }) }
  w := { w with gps.state := w.gps.state.set! s.state'i ({ w.gps.state[s.state'i]! with location := Location.init_int32_t3_AltFrame (Binary64.toInt32 (latitude * (Binary64.ofBits 0x416312d000000000 /- 1e7 -/))) (Binary64.toInt32 (longitude * (Binary64.ofBits 0x416312d000000000 /- 1e7 -/))) (Binary32.toInt32 (altitude * (Binary32.ofBits 0x42c80000 /- 100 -/))) Location.AltFrame.ABSOLUTE }) }
  w := { w with gps.state := w.gps.state.set! s.state'i ({ w.gps.state[s.state'i]! with hdop := Int16.toUInt16 (Int32.toInt16 (100 : Int32)) }) }
  w := { w with gps.state := w.gps.state.set! s.state'i ({ w.gps.state[s.state'i]! with vdop := Int16.toUInt16 (Int32.toInt16 (100 : Int32)) }) }
  w := { w with gps.state := w.gps.state.set! s.state'i ({ w.gps.state[s.state'i]! with have_vertical_velocity := true }) }
  w := { w with gps.state := w.gps.state.set! s.state'i ({ w.gps.state[s.state'i]! with velocity.x := Binary64.toBinary32 speedN }) }
  w := { w with gps.state := w.gps.state.set! s.state'i ({ w.gps.state[s.state'i]! with velocity.y := Binary64.toBinary32 speedE }) }
  w := { w with gps.state := w.gps.state.set! s.state'i ({ w.gps.state[s.state'i]! with velocity.z := Binary64.toBinary32 speedD }) }
  w := { w with gps.state := w.gps.state.set! s.state'i (velocity_to_speed_course w.gps.state[s.state'i]!) }
  w := { w with gps.state := w.gps.state.set! s.state'i ({ w.gps.state[s.state'i]! with have_speed_accuracy := true }) }
  w := { w with gps.state := w.gps.state.set! s.state'i ({ w.gps.state[s.state'i]! with have_horizontal_accuracy := true }) }
  w := { w with gps.state := w.gps.state.set! s.state'i ({ w.gps.state[s.state'i]! with have_vertical_accuracy := true }) }
  w := { w with gps.state := w.gps.state.set! s.state'i ({ w.gps.state[s.state'i]! with have_vertical_velocity := true }) }
  w := { w with gps.state := w.gps.state.set! s.state'i ({ w.gps.state[s.state'i]! with last_gps_time_ms := now }) }
  return (s, w, true)

end AP_GPS_SITL

namespace AP_GPS

/-- C++ `void AP_GPS::update_instance(uint8_t instance)`, `AP_GPS/AP_GPS.cpp:866-1002`. -/
def update_instance (s : State) (w : World) (o : Outputs) («instance» : UInt8) : State × World × Outputs := Id.run do
  let mut s := s
  let mut w := w
  let mut o := o
  let type : AP_Enum_AP_GPS_GPS_Type.State := s.params[UInt8.toNat «instance»]!.type
  if UInt32.toInt32 (AP_GPS.GPS_Type.toInt (AP_Enum_AP_GPS_GPS_Type.op_to_AP_GPS_GPS_Type type)) == UInt32.toInt32 (AP_GPS.GPS_Type.toInt AP_GPS.GPS_Type.GPS_TYPE_HIL) then
    return (s, w, o)
  if UInt32.toInt32 (AP_GPS.GPS_Type.toInt (AP_Enum_AP_GPS_GPS_Type.op_to_AP_GPS_GPS_Type type)) == UInt32.toInt32 (AP_GPS.GPS_Type.toInt AP_GPS.GPS_Type.GPS_TYPE_NONE) then
    s := { s with state := s.state.set! (UInt8.toNat «instance») ({ s.state[UInt8.toNat «instance»]! with status := AP_GPS_FixType.NO_GPS }) }
    s := { s with state := s.state.set! (UInt8.toNat «instance») ({ s.state[UInt8.toNat «instance»]! with hdop := Int16.toUInt16 (Int32.toInt16 (65535 : Int32)) }) }
    s := { s with state := s.state.set! (UInt8.toNat «instance») ({ s.state[UInt8.toNat «instance»]! with vdop := Int16.toUInt16 (Int32.toInt16 (65535 : Int32)) }) }
    return (s, w, o)
  if UInt8.toUInt32 s.locked_ports &&& ((1 : UInt32) <<< Int32.toUInt32 (UInt32.toInt32 (UInt8.toUInt32 «instance»))) != (0 : UInt32) then
    return (s, w, o)
  if s.drivers[UInt8.toNat «instance»]! == WPtr.null then
    let (t'1, t'2, t'3) := detect_instance s w o «instance»
    w := t'2
    s := t'1
    o := t'3
    return (s, w, o)
  if Int8.toInt32 (AP_ParamT_signed_char_1.op_to_signed_char s._auto_config) ≥ UInt32.toInt32 (AP_GPS.GPS_AUTO_CONFIG.toInt AP_GPS.GPS_AUTO_CONFIG.GPS_AUTO_CONFIG_ENABLE_SERIAL_ONLY) then
    pure ()  -- C++ `AP_GPS::send_blob_update(...)`: left out (--drop)
  let t'4 := (WPtr.index s.drivers[UInt8.toNat «instance»]!)
  w := { w with gps := s }  -- this object's state into the World: the call reaches it
  let t'5 := w.heap'AP_GPS_SITL[t'4]!  -- the object out of its slot for the call (--swap-out)
  w := { w with heap'AP_GPS_SITL := w.heap'AP_GPS_SITL.set! t'4 default }
  let (t'6, t'7, t'8) := AP_GPS_SITL.read t'5 w
  w := t'7
  w := { w with heap'AP_GPS_SITL := w.heap'AP_GPS_SITL.set! t'4 t'6 }
  s := w.gps  -- this object's state as the call left it
  let result : Bool := t'8
  let mut tnow : UInt32 := Estimator_lib.millis w
  let mut new_data_or_timeout : Bool := false
  if !result then
    if tnow - s.timing[UInt8.toNat «instance»]!.last_message_time_ms > (4000 : UInt32) then
      s := { s with state := s.state.set! (UInt8.toNat «instance») ({ «instance» := (0 : UInt8), status := AP_GPS_FixType.NO_GPS, time_week_ms := (0 : UInt32), time_week := (0 : UInt16), location := { relative_alt := (0 : UInt8), loiter_ccw := (0 : UInt8), terrain_alt := (0 : UInt8), origin_alt := (0 : UInt8), loiter_xtrack := (0 : UInt8), alt := (0 : Int32), lat := (0 : Int32), lng := (0 : Int32) }, ground_speed := (Binary32.ofBits 0x00000000 /- 0.0 -/), ground_course := (Binary32.ofBits 0x00000000 /- 0.0 -/), gps_yaw := (Binary32.ofBits 0x00000000 /- 0.0 -/), gps_yaw_time_ms := (0 : UInt32), gps_yaw_configured := false, hdop := (0 : UInt16), vdop := (0 : UInt16), num_sats := (0 : UInt8), velocity := { x := (Binary32.ofBits 0x00000000 /- 0.0 -/), y := (Binary32.ofBits 0x00000000 /- 0.0 -/), z := (Binary32.ofBits 0x00000000 /- 0.0 -/) }, speed_accuracy := (Binary32.ofBits 0x00000000 /- 0.0 -/), horizontal_accuracy := (Binary32.ofBits 0x00000000 /- 0.0 -/), vertical_accuracy := (Binary32.ofBits 0x00000000 /- 0.0 -/), gps_yaw_accuracy := (Binary32.ofBits 0x00000000 /- 0.0 -/), have_vertical_velocity := false, have_speed_accuracy := false, have_horizontal_accuracy := false, have_vertical_accuracy := false, have_gps_yaw := false, have_gps_yaw_accuracy := false, undulation := (Binary32.ofBits 0x00000000 /- 0.0 -/), have_undulation := false, last_gps_time_ms := (0 : UInt32), announced_detection := false, last_corrected_gps_time_us := (0 : UInt64), corrected_timestamp_updated := false, lagged_sample_count := (0 : UInt32), rtk_time_week_ms := (0 : UInt32), rtk_week_number := (0 : UInt16), rtk_age_ms := (0 : UInt32), rtk_num_sats := (0 : UInt8), rtk_baseline_coords_type := (0 : UInt8), rtk_baseline_x_mm := (0 : Int32), rtk_baseline_y_mm := (0 : Int32), rtk_baseline_z_mm := (0 : Int32), rtk_accuracy := (0 : UInt32), rtk_iar_num_hypotheses := (0 : Int32), relPosHeading := (Binary32.ofBits 0x00000000 /- 0.0 -/), relPosLength := (Binary32.ofBits 0x00000000 /- 0.0 -/), relPosD := (Binary32.ofBits 0x00000000 /- 0.0 -/), accHeading := (Binary32.ofBits 0x00000000 /- 0.0 -/), relposheading_ts := (0 : UInt32) }) }
      s := { s with state := s.state.set! (UInt8.toNat «instance») ({ s.state[UInt8.toNat «instance»]! with «instance» := «instance» }) }
      s := { s with state := s.state.set! (UInt8.toNat «instance») ({ s.state[UInt8.toNat «instance»]! with hdop := Int16.toUInt16 (Int32.toInt16 (65535 : Int32)) }) }
      s := { s with state := s.state.set! (UInt8.toNat «instance») ({ s.state[UInt8.toNat «instance»]! with vdop := Int16.toUInt16 (Int32.toInt16 (65535 : Int32)) }) }
      s := { s with timing := s.timing.set! (UInt8.toNat «instance») ({ s.timing[UInt8.toNat «instance»]! with last_message_time_ms := tnow }) }
      s := { s with timing := s.timing.set! (UInt8.toNat «instance») ({ s.timing[UInt8.toNat «instance»]! with delta_time_ms := UInt32.toUInt16 (4000 : UInt32) }) }
      s := update_frame_timing_health s «instance»
      if UInt32.toInt32 (AP_GPS.GPS_Type.toInt (AP_Enum_AP_GPS_GPS_Type.op_to_AP_GPS_GPS_Type type)) == UInt32.toInt32 (AP_GPS.GPS_Type.toInt AP_GPS.GPS_Type.GPS_TYPE_MAV) || UInt32.toInt32 (AP_GPS.GPS_Type.toInt (AP_Enum_AP_GPS_GPS_Type.op_to_AP_GPS_GPS_Type type)) == UInt32.toInt32 (AP_GPS.GPS_Type.toInt AP_GPS.GPS_Type.GPS_TYPE_UAVCAN) || UInt32.toInt32 (AP_GPS.GPS_Type.toInt (AP_Enum_AP_GPS_GPS_Type.op_to_AP_GPS_GPS_Type type)) == UInt32.toInt32 (AP_GPS.GPS_Type.toInt AP_GPS.GPS_Type.GPS_TYPE_UAVCAN_RTK_BASE) || UInt32.toInt32 (AP_GPS.GPS_Type.toInt (AP_Enum_AP_GPS_GPS_Type.op_to_AP_GPS_GPS_Type type)) == UInt32.toInt32 (AP_GPS.GPS_Type.toInt AP_GPS.GPS_Type.GPS_TYPE_UAVCAN_RTK_ROVER) then
        s := { s with state := s.state.set! (UInt8.toNat «instance») ({ s.state[UInt8.toNat «instance»]! with status := AP_GPS_FixType.NONE }) }
      else
        pure ()  -- C++ `delete drivers[instance]`: the object's slot is left as it is (nothing refers to it again)
        s := { s with drivers := s.drivers.set! (UInt8.toNat «instance») WPtr.null }
        s := { s with state := s.state.set! (UInt8.toNat «instance») ({ s.state[UInt8.toNat «instance»]! with status := AP_GPS_FixType.NO_GPS }) }
      new_data_or_timeout := true
  else
    if s.state[UInt8.toNat «instance»]!.corrected_timestamp_updated then
      tnow := UInt64.toUInt32 (s.state[UInt8.toNat «instance»]!.last_corrected_gps_time_us / UInt32.toUInt64 (1000 : UInt32))
      s := { s with state := s.state.set! (UInt8.toNat «instance») ({ s.state[UInt8.toNat «instance»]! with corrected_timestamp_updated := false }) }
    if !s.state[UInt8.toNat «instance»]!.announced_detection then
      s := { s with state := s.state.set! (UInt8.toNat «instance») ({ s.state[UInt8.toNat «instance»]! with announced_detection := true }) }
      let t'10 := "GPS %d: detected %s"
      let t'11 := UInt32.toInt32 (UInt8.toUInt32 «instance») + (1 : Int32)
      let t'9 := (WPtr.index s.drivers[UInt8.toNat «instance»]!)
      o := o.push (Output.send_text (6 : UInt32) t'10 #[Sum.inl (Int64.toUInt64 (Int32.toInt64 t'11)), Sum.inr (AP_GPS_SITL.name)])
    let delta_ms : Int32 := UInt32.toInt32 (tnow - s.timing[UInt8.toNat «instance»]!.last_message_time_ms)
    s := { s with timing := s.timing.set! (UInt8.toNat «instance») ({ s.timing[UInt8.toNat «instance»]! with last_message_time_ms := tnow }) }
    if delta_ms < (0 : Int32) then
      s := { s with timing := s.timing.set! (UInt8.toNat «instance») ({ s.timing[UInt8.toNat «instance»]! with delta_time_ms := Int16.toUInt16 (Int32.toInt16 (0 : Int32)) }) }
    else
      s := { s with timing := s.timing.set! (UInt8.toNat «instance») ({ s.timing[UInt8.toNat «instance»]! with delta_time_ms := Int16.toUInt16 (Int32.toInt16 (Estimator_lib.MIN_int32_t2 delta_ms (65535 : Int32))) }) }
      s := update_frame_timing_health s «instance»
    if decide (AP_GPS_FixType.toInt s.state[UInt8.toNat «instance»]!.status ≥ AP_GPS_FixType.toInt AP_GPS_FixType.FIX_2D) && !s._force_disable_gps then
      s := { s with timing := s.timing.set! (UInt8.toNat «instance») ({ s.timing[UInt8.toNat «instance»]! with last_fix_time_ms := tnow }) }
    new_data_or_timeout := true
  if (s.drivers[UInt8.toNat «instance»]! != WPtr.null) && UInt32.toInt32 (AP_GPS.GPS_Type.toInt (AP_Enum_AP_GPS_GPS_Type.op_to_AP_GPS_GPS_Type type)) == UInt32.toInt32 (AP_GPS.GPS_Type.toInt AP_GPS.GPS_Type.GPS_TYPE_UBLOX_RTK_BASE) then
    pure ()  -- C++ `const uint8_t *rtcm_data`: used only where the code cannot run, left out
    pure ()  -- C++ `uint16_t rtcm_len`: used only where the code cannot run, left out
    pure ()  -- C++ `if (drivers[instance]->get_RTCMV3(rtcm_data, rtcm_len))`: false (every overrider the call can reach returns `false`; --ins-gps)
  if AP_GPS_FixType.toInt s.state[UInt8.toNat «instance»]!.status ≥ AP_GPS_FixType.toInt AP_GPS_FixType.FIX_3D then
    let (t'12, t'13) := time_epoch_usec_uint8_t s w «instance»
    w := t'12
    let now : UInt64 := t'13
    if now != Int64.toUInt64 (Int32.toInt64 (0 : Int32)) then
      let t'14 := w.rtc  -- the object out of the World for the call (--swap-out)
      w := { w with rtc := default }
      let (t'15, t'16) := AP_RTC.set_utc_usec t'14 w o w.rtc'inp now AP_RTC.source_type.SOURCE_GPS
      w := { w with rtc := t'15 }
      o := t'16
  return (s, w, o)

/-- C++ `enum class AP_GPS::GPSAutoSwitch`, `AP_GPS/AP_GPS.h:805-811`. -/
inductive GPSAutoSwitch where
  | NONE
  | USE_BEST
  | BLEND
  | USE_PRIMARY_IF_3D_FIX
deriving DecidableEq, Inhabited

/-- The value of each enumerator of `AP_GPS::GPSAutoSwitch` (underlying type `int32_t`). -/
def GPSAutoSwitch.toInt : GPSAutoSwitch → Int32
  | .NONE => (0 : Int32)
  | .USE_BEST => (1 : Int32)
  | .BLEND => (2 : Int32)
  | .USE_PRIMARY_IF_3D_FIX => (4 : Int32)

/-- The enumerator of `AP_GPS::GPSAutoSwitch` with value `v` (the C++ converts only enumerator values; any other
value gives the first enumerator, the `Inhabited` default). -/
def GPSAutoSwitch.ofInt (v : Int32) : GPSAutoSwitch :=
  if v == (0 : Int32) then .NONE
  else if v == (1 : Int32) then .USE_BEST
  else if v == (2 : Int32) then .BLEND
  else if v == (4 : Int32) then .USE_PRIMARY_IF_3D_FIX
  else default

/-- C++ `void AP_GPS::update_primary()`, `AP_GPS/AP_GPS.cpp:1098-1240`. -/
def update_primary (s : State) (w : World) : State := Id.run do
  let mut s := s
  let mut primary_param : Int8 := AP_ParamT_signed_char_1.get_void s._primary
  if (decide (Int8.toInt32 primary_param < (0 : Int32))) || (decide (Int8.toInt32 primary_param ≥ (2 : Int32))) then
    primary_param := Int32.toInt8 (0 : Int32)
  if UInt32.toInt32 (AP_GPS.GPS_Type.toInt (get_type s (Int8.toUInt8 primary_param))) == UInt32.toInt32 (AP_GPS.GPS_Type.toInt AP_GPS.GPS_Type.GPS_TYPE_NONE) then
    primary_param := Int32.toInt8 (0 : Int32)
  if AP_GPS.GPSAutoSwitch.ofInt (Int8.toInt32 (AP_ParamT_signed_char_1.get_void s._auto_switch)) == AP_GPS.GPSAutoSwitch.NONE then
    s := { s with primary_instance := Int8.toUInt8 primary_param }
    return s
  let now : UInt32 := Estimator_lib.millis w
  for i' in [0:2] do
    let i : UInt8 := Nat.toUInt8 i'
    if is_rtk_base s i && is_rtk_rover s (Int8.toUInt8 (Int32.toInt8 (UInt32.toInt32 (UInt8.toUInt32 i) ^^^ (1 : Int32)))) && ((decide (AP_GPS_FixType.toInt s.state[UInt8.toNat i]!.status ≥ AP_GPS_FixType.toInt AP_GPS_FixType.FIX_3D)) || (decide (AP_GPS_FixType.toInt s.state[UInt8.toNat i]!.status ≥ AP_GPS_FixType.toInt s.state[Int32.toNatClampNeg (UInt32.toInt32 (UInt8.toUInt32 i) ^^^ (1 : Int32))]!.status))) then
      if UInt32.toInt32 (UInt8.toUInt32 s.primary_instance) != UInt32.toInt32 (UInt8.toUInt32 i) then
        s := { s with _last_instance_swap_ms := now }
        s := { s with primary_instance := i }
      return s
  if (AP_GPS.GPSAutoSwitch.ofInt (Int8.toInt32 (AP_ParamT_signed_char_1.get_void s._auto_switch)) == AP_GPS.GPSAutoSwitch.USE_PRIMARY_IF_3D_FIX) && (decide (AP_GPS_FixType.toInt s.state[Int8.toNatClampNeg primary_param]!.status ≥ AP_GPS_FixType.toInt AP_GPS_FixType.FIX_3D)) then
    if UInt32.toInt32 (UInt8.toUInt32 s.primary_instance) != Int8.toInt32 primary_param then
      s := { s with primary_instance := Int8.toUInt8 primary_param }
      s := { s with _last_instance_swap_ms := now }
    return s
  for i'2' in [0:2] do
    let i'2 : UInt8 := Nat.toUInt8 i'2'
    if UInt32.toInt32 (UInt8.toUInt32 i'2) == UInt32.toInt32 (UInt8.toUInt32 s.primary_instance) then
      continue
    if AP_GPS_FixType.toInt s.state[UInt8.toNat i'2]!.status > AP_GPS_FixType.toInt s.state[UInt8.toNat s.primary_instance]!.status then
      s := { s with primary_instance := i'2 }
      s := { s with _last_instance_swap_ms := now }
      continue
    let another_gps_has_1_or_more_sats : Bool := (decide (UInt32.toInt32 (UInt8.toUInt32 s.state[UInt8.toNat i'2]!.num_sats) ≥ UInt32.toInt32 (UInt8.toUInt32 s.state[UInt8.toNat s.primary_instance]!.num_sats) + (1 : Int32)))
    if s.state[UInt8.toNat i'2]!.status == s.state[UInt8.toNat s.primary_instance]!.status && another_gps_has_1_or_more_sats then
      let another_gps_has_2_or_more_sats : Bool := (decide (UInt32.toInt32 (UInt8.toUInt32 s.state[UInt8.toNat i'2]!.num_sats) ≥ UInt32.toInt32 (UInt8.toUInt32 s.state[UInt8.toNat s.primary_instance]!.num_sats) + (2 : Int32)))
      if (another_gps_has_1_or_more_sats && decide ((now - s._last_instance_swap_ms) ≥ Int32.toUInt32 (20000 : Int32))) || (another_gps_has_2_or_more_sats && decide ((now - s._last_instance_swap_ms) ≥ Int32.toUInt32 (5000 : Int32))) then
        s := { s with primary_instance := i'2 }
        s := { s with _last_instance_swap_ms := now }
  return s

/-- C++ `void AP_GPS::update()`, `AP_GPS/AP_GPS.cpp:1060-1092`. -/
def update (s : State) (w : World) (o : Outputs) : State × World × Outputs := Id.run do
  let mut s := s
  let mut w := w
  let mut o := o
  pure ()  -- C++ `_getsem29`: a semaphore, which does nothing here (one thread, --semaphores)
  for i' in [0:2] do
    let i : UInt8 := Nat.toUInt8 i'
    let (t'1, t'2, t'3) := update_instance s w o i
    w := t'2
    s := t'1
    o := t'3
  for i'2' in [0:2] do
    let i'2 : UInt8 := Nat.toUInt8 i'2'
    if s.drivers[UInt8.toNat i'2]! != WPtr.null then
      s := { s with num_instances := Int8.toUInt8 (Int32.toInt8 (UInt32.toInt32 (UInt8.toUInt32 i'2) + (1 : Int32))) }
  s := update_primary s w
  o := o.push (Output.AP_Notify_flags_gps_status s.state[UInt8.toNat s.primary_instance]!.status)
  o := o.push (Output.AP_Notify_flags_gps_num_sats s.state[UInt8.toNat s.primary_instance]!.num_sats)
  return (s, w, o)

/-- C++ `bool AP_GPS::have_vertical_velocity() const`, `AP_GPS/AP_GPS.h:480-482`. -/
def have_vertical_velocity_void (s : State) : Bool := Id.run do
  return have_vertical_velocity_uint8_t s s.primary_instance

/-- C++ `bool AP_GPS::horizontal_accuracy(float & hacc) const`, `AP_GPS/AP_GPS.h:362-364`. -/
def horizontal_accuracy_float (s : State) (hacc : Binary32) : Binary32 × Bool := Id.run do
  let mut hacc := hacc
  let (t'1, t'2) := horizontal_accuracy_uint8_t_float s s.primary_instance hacc
  hacc := t'1
  return (hacc, t'2)

/-- C++ `bool AP_GPS::vertical_accuracy(float & vacc) const`, `AP_GPS/AP_GPS.h:367-369`. -/
def vertical_accuracy_float (s : State) (vacc : Binary32) : Binary32 × Bool := Id.run do
  let mut vacc := vacc
  let (t'1, t'2) := vertical_accuracy_uint8_t_float s s.primary_instance vacc
  vacc := t'1
  return (vacc, t'2)

/-- C++ `bool AP_GPS::speed_accuracy(float & sacc) const`, `AP_GPS/AP_GPS.h:357-359`. -/
def speed_accuracy_float (s : State) (sacc : Binary32) : Binary32 × Bool := Id.run do
  let mut sacc := sacc
  let (t'1, t'2) := speed_accuracy_uint8_t_float s s.primary_instance sacc
  sacc := t'1
  return (sacc, t'2)

/-- C++ `uint16_t AP_GPS::get_hdop() const`, `AP_GPS/AP_GPS.h:438-440`. -/
def get_hdop_void (s : State) : UInt16 := Id.run do
  return get_hdop_uint8_t s s.primary_instance

/-- C++ `bool AP_GPS::gps_yaw_deg(float & yaw_deg, float & accuracy_deg, uint32_t & time_ms) const`, `AP_GPS/AP_GPS.h:406-408`. -/
def gps_yaw_deg_float2_uint32_t (s : State) (w : World) (yaw_deg : Binary32) (accuracy_deg : Binary32) (time_ms : UInt32) : Binary32 × Binary32 × UInt32 × Bool := Id.run do
  let mut yaw_deg := yaw_deg
  let mut accuracy_deg := accuracy_deg
  let mut time_ms := time_ms
  let (t'1, t'2, t'3, t'4) := gps_yaw_deg_uint8_t_float2_uint32_t s w s.primary_instance yaw_deg accuracy_deg time_ms
  yaw_deg := t'1
  accuracy_deg := t'2
  time_ms := t'3
  return (yaw_deg, accuracy_deg, time_ms, t'4)

/-- C++ `uint16_t AP_GPS::time_week(uint8_t instance) const`, `AP_GPS/AP_GPS.h:427-429`. -/
def time_week_uint8_t (s : State) («instance» : UInt8) : UInt16 := Id.run do
  return s.state[UInt8.toNat «instance»]!.time_week

/-- C++ `uint16_t AP_GPS::time_week() const`, `AP_GPS/AP_GPS.h:430-432`. -/
def time_week_void (s : State) : UInt16 := Id.run do
  return time_week_uint8_t s s.primary_instance

/-- C++ `uint32_t AP_GPS::time_week_ms(uint8_t instance) const`, `AP_GPS/AP_GPS.h:419-421`. -/
def time_week_ms_uint8_t (s : State) («instance» : UInt8) : UInt32 := Id.run do
  return s.state[UInt8.toNat «instance»]!.time_week_ms

/-- C++ `uint32_t AP_GPS::time_week_ms() const`, `AP_GPS/AP_GPS.h:422-424`. -/
def time_week_ms_void (s : State) : UInt32 := Id.run do
  return time_week_ms_uint8_t s s.primary_instance

/-- C++ `uint16_t AP_GPS::get_vdop(uint8_t instance) const`, `AP_GPS/AP_GPS.h:443-445`. -/
def get_vdop_uint8_t (s : State) («instance» : UInt8) : UInt16 := Id.run do
  return s.state[UInt8.toNat «instance»]!.vdop

/-- C++ `uint16_t AP_GPS::get_vdop() const`, `AP_GPS/AP_GPS.h:446-448`. -/
def get_vdop_void (s : State) : UInt16 := Id.run do
  return get_vdop_uint8_t s s.primary_instance

/-- C++ `bool AP_GPS::all_consistent(float & distance) const`, `AP_GPS/AP_GPS.cpp:1505-1518`. -/
def all_consistent (s : State) (distance : Binary32) : Binary32 × Bool := Id.run do
  let mut distance := distance
  if decide (UInt32.toInt32 (UInt8.toUInt32 s.num_instances) ≤ (1 : Int32)) || s.drivers[0]! == WPtr.null || UInt32.toInt32 (AP_GPS.GPS_Type.toInt (AP_Enum_AP_GPS_GPS_Type.op_to_AP_GPS_GPS_Type s.params[0]!.type)) == UInt32.toInt32 (AP_GPS.GPS_Type.toInt AP_GPS.GPS_Type.GPS_TYPE_NONE) then
    distance := (Binary32.ofBits 0x00000000 /- 0 -/)
    return (distance, true)
  distance := Vector3f.length (Location.get_distance_NED s.state[0]!.location s.state[1]!.location)
  return (distance, (decide (distance < (Binary32.ofBits 0x42480000 /- 50 -/))))

end AP_GPS

namespace AP_GPS

/-- C++ `bool AP_GPS::first_unconfigured_gps(uint8_t & instance) const`, `AP_GPS/AP_GPS.cpp:1481-1490`. -/
def first_unconfigured_gps (s : State) (w : World) («instance» : UInt8) : UInt8 × Bool := Id.run do
  let mut «instance» := «instance»
  for i' in [0:2] do
    let i : Int32 := Nat.toInt32 i'
    let mut t'3 := UInt32.toInt32 (AP_GPS.GPS_Type.toInt (AP_Enum_AP_GPS_GPS_Type.op_to_AP_GPS_GPS_Type s.params[Int32.toNatClampNeg i]!.type)) != UInt32.toInt32 (AP_GPS.GPS_Type.toInt AP_GPS.GPS_Type.GPS_TYPE_NONE)
    if t'3 then
      let mut t'2 := s.drivers[Int32.toNatClampNeg i]! == WPtr.null
      if !t'2 then
        let t'1 := (WPtr.index s.drivers[Int32.toNatClampNeg i]!)
        t'2 := !(AP_GPS_SITL.is_configured)
      t'3 := t'2
    if t'3 then
      «instance» := Int8.toUInt8 (Int32.toInt8 i)
      return («instance», true)
  return («instance», false)

/-- C++ `void AP_GPS::force_disable(bool disable)`, `AP_GPS/AP_GPS.h:580-582`. -/
def force_disable (s : State) (disable : Bool) : State := Id.run do
  let mut s := s
  s := { s with _force_disable_gps := disable }
  return s

/-- C++ `uint8_t AP_GPS::get_auto_switch_type() const`, `AP_GPS/AP_GPS.h:618`. -/
def get_auto_switch_type (s : State) : UInt8 := Id.run do
  return Int8.toUInt8 (AP_ParamT_signed_char_1.op_to_signed_char s._auto_switch)

end AP_GPS

namespace AP_GPS

/-- C++ `bool AP_GPS::is_healthy(uint8_t instance) const`, `AP_GPS/AP_GPS.cpp:1786-1822`. -/
def is_healthy_uint8_t (s : State) (w : World) («instance» : UInt8) : Bool := Id.run do
  if UInt32.toInt32 (UInt8.toUInt32 «instance») ≥ ((2 : Int32) + (1 : Int32)) then
    return false
  if UInt32.toInt32 (AP_GPS.GPS_Type.toInt (get_type s (Int8.toUInt8 (AP_ParamT_signed_char_1.get_void s._primary)))) == UInt32.toInt32 (AP_GPS.GPS_Type.toInt AP_GPS.GPS_Type.GPS_TYPE_NONE) then
    return false
  let delay_threshold : UInt8 := Int8.toUInt8 (Int32.toInt8 (2 : Int32))
  let delay_avg_max : Binary32 := Int32.toBinary32 (if is_rtk_rover s «instance» then (333 : Int32) else (215 : Int32))
  let delay_ok : Bool := (decide (UInt32.toInt32 (UInt8.toUInt32 s.timing[UInt8.toNat «instance»]!.delayed_count) < UInt32.toInt32 (UInt8.toUInt32 delay_threshold))) && decide (s.timing[UInt8.toNat «instance»]!.average_delta_ms < delay_avg_max) && decide (s.state[UInt8.toNat «instance»]!.lagged_sample_count < Int32.toUInt32 (5 : Int32))
  if !delay_ok then
    return false
  let mut t'2 := s.drivers[UInt8.toNat «instance»]! != WPtr.null
  if t'2 then
    let t'1 := (WPtr.index s.drivers[UInt8.toNat «instance»]!)
    t'2 := AP_GPS_SITL.is_healthy
  return t'2

/-- C++ `bool AP_GPS::is_healthy() const`, `AP_GPS/AP_GPS.h:563`. -/
def is_healthy_void (s : State) (w : World) : Bool := Id.run do
  return is_healthy_uint8_t s w s.primary_instance

end AP_GPS

namespace AP_GPS

/-- C++ `bool AP_GPS::prepare_for_arming()`, `AP_GPS/AP_GPS.cpp:1824-1832`. -/
def prepare_for_arming (s : State) (w : World) : Bool := Id.run do
  let mut all_passed : Bool := true
  for i' in [0:2] do
    let i : UInt8 := Nat.toUInt8 i'
    if s.drivers[UInt8.toNat i]! != WPtr.null then
      let t'1 := (WPtr.index s.drivers[UInt8.toNat i]!)
      all_passed := (if all_passed then (1 : Int32) else (0 : Int32)) &&& (if AP_GPS_SITL.prepare_for_arming then (1 : Int32) else (0 : Int32)) != (0 : Int32)
  return all_passed

/-- C++ `void AP_GPS::set_force_disable_yaw(bool disable)`, `AP_GPS/AP_GPS.h:585-587`. -/
def set_force_disable_yaw (s : State) (disable : Bool) : State := Id.run do
  let mut s := s
  s := { s with _force_disable_gps_yaw := disable }
  return s

/-- C++ `void AP_GPS::set_log_gps_bit(uint32_t bit)`, `AP_GPS/AP_GPS.h:558`. -/
def set_log_gps_bit (s : State) (bit : UInt32) : State := Id.run do
  let mut s := s
  s := { s with _log_gps_bit := bit }
  return s

/-- C++ `bool AP_GPS::get_undulation(uint8_t instance, float & undulation) const`, `AP_GPS/AP_GPS.cpp:1897-1904`. -/
def get_undulation_uint8_t_float (s : State) («instance» : UInt8) (undulation : Binary32) : Binary32 × Bool := Id.run do
  let mut undulation := undulation
  if !s.state[UInt8.toNat «instance»]!.have_undulation then
    return (undulation, false)
  undulation := s.state[UInt8.toNat «instance»]!.undulation
  return (undulation, true)

/-- C++ `bool AP_GPS::get_undulation(float & undulation) const`, `AP_GPS/AP_GPS.h:351-353`. -/
def get_undulation_float (s : State) (undulation : Binary32) : Binary32 × Bool := Id.run do
  let mut undulation := undulation
  let (t'1, t'2) := get_undulation_uint8_t_float s s.primary_instance undulation
  undulation := t'1
  return (undulation, t'2)

/-- C++ `bool AP_GPS::have_gps_yaw_configured(uint8_t instance) const`, `AP_GPS/AP_GPS.h:495-497`. -/
def have_gps_yaw_configured (s : State) («instance» : UInt8) : Bool := Id.run do
  return s.state[UInt8.toNat «instance»]!.gps_yaw_configured

end AP_GPS

namespace AP_GPS

/-- C++ `uint16_t AP_GPS::gps_yaw_cdeg(uint8_t instance) const`, `AP_GPS/AP_GPS.cpp:1368-1383`. -/
def gps_yaw_cdeg (s : State) (w : World) («instance» : UInt8) : UInt16 := Id.run do
  if !(have_gps_yaw_configured s «instance») then
    return Int16.toUInt16 (Int32.toInt16 (0 : Int32))
  let mut yaw_deg : Binary32 := (Binary32.ofBits 0x00000000 /- 0.0 -/)  -- uninitialized in C++; assigned before every read
  let mut accuracy_deg : Binary32 := (Binary32.ofBits 0x00000000 /- 0.0 -/)  -- uninitialized in C++; assigned before every read
  let mut time_ms : UInt32 := (0 : UInt32)  -- uninitialized in C++; assigned before every read
  let (t'1, t'2, t'3, t'4) := gps_yaw_deg_uint8_t_float2_uint32_t s w «instance» yaw_deg accuracy_deg time_ms
  yaw_deg := t'1
  accuracy_deg := t'2
  time_ms := t'3
  if !t'4 then
    return Int16.toUInt16 (Int32.toInt16 (65535 : Int32))
  let yaw_cd : Int32 := Binary32.toInt32 (Estimator_lib.wrap_360_cd_float (yaw_deg * (Binary32.ofBits 0x42c80000 /- 100 -/)))
  if yaw_cd == (0 : Int32) then
    return Int16.toUInt16 (Int32.toInt16 (36000 : Int32))
  return Int16.toUInt16 (Int32.toInt16 yaw_cd)

/-- C++ `void AP_GPS::send_mavlink_gps_raw(mavlink_channel_t chan)`, `AP_GPS/AP_GPS.cpp:1386-1423`. -/
def send_mavlink_gps_raw (s : State) (w : World) (o : Outputs) (chan : mavlink_channel_t) : Outputs := Id.run do
  let mut o := o
  if UInt32.toInt32 (AP_GPS.GPS_Type.toInt (get_type s (Int8.toUInt8 (Int32.toInt8 (0 : Int32))))) == UInt32.toInt32 (AP_GPS.GPS_Type.toInt AP_GPS.GPS_Type.GPS_TYPE_NONE) then
    return o
  let t'1 := Int8.toUInt8 (Int32.toInt8 (0 : Int32))
  let mut hacc : Binary32 := (Binary32.ofBits 0x00000000 /- 0.0f -/)
  let mut vacc : Binary32 := (Binary32.ofBits 0x00000000 /- 0.0f -/)
  let mut sacc : Binary32 := (Binary32.ofBits 0x00000000 /- 0.0f -/)
  let mut undulation : Binary32 := (Binary32.ofBits 0x00000000 /- 0.0 -/)
  let mut height_elipsoid_mm : Int32 := (0 : Int32)
  let (t'2, t'3) := get_undulation_uint8_t_float s (Int8.toUInt8 (Int32.toInt8 (0 : Int32))) undulation
  undulation := t'2
  if t'3 then
    height_elipsoid_mm := Binary32.toInt32 (Int32.toBinary32 (s.state[UInt8.toNat t'1]!.location.alt * (10 : Int32)) - undulation * (Binary32.ofBits 0x447a0000 /- 1000 -/))
  let (t'4, _) := horizontal_accuracy_uint8_t_float s (Int8.toUInt8 (Int32.toInt8 (0 : Int32))) hacc
  hacc := t'4
  let (t'6, _) := vertical_accuracy_uint8_t_float s (Int8.toUInt8 (Int32.toInt8 (0 : Int32))) vacc
  vacc := t'6
  let (t'8, _) := speed_accuracy_uint8_t_float s (Int8.toUInt8 (Int32.toInt8 (0 : Int32))) sacc
  sacc := t'8
  o := o.push (Output.mavlink_msg_gps_raw_int_send chan (UInt32.toUInt64 (last_fix_time_ms_uint8_t s (Int8.toUInt8 (Int32.toInt8 (0 : Int32)))) * Int64.toUInt64 (Int32.toInt64 (1000 : Int32))) (AP_GPS_FixType.toInt (status_uint8_t s (Int8.toUInt8 (Int32.toInt8 (0 : Int32))))) s.state[UInt8.toNat t'1]!.location.lat s.state[UInt8.toNat t'1]!.location.lng (UInt32.toInt32 (UInt64.toUInt32 (Int64.toUInt64 (Int32.toInt64 s.state[UInt8.toNat t'1]!.location.alt) * (10 : UInt64)))) (get_hdop_uint8_t s (Int8.toUInt8 (Int32.toInt8 (0 : Int32)))) (get_vdop_uint8_t s (Int8.toUInt8 (Int32.toInt8 (0 : Int32)))) (Binary32.toUInt16 (ground_speed_uint8_t s (Int8.toUInt8 (Int32.toInt8 (0 : Int32))) * (Binary32.ofBits 0x42c80000 /- 100 -/))) (Binary32.toUInt16 (ground_course_uint8_t s (Int8.toUInt8 (Int32.toInt8 (0 : Int32))) * (Binary32.ofBits 0x42c80000 /- 100 -/))) (num_sats_uint8_t s (Int8.toUInt8 (Int32.toInt8 (0 : Int32)))) height_elipsoid_mm (Binary32.toUInt32 (hacc * (Binary32.ofBits 0x447a0000 /- 1000 -/))) (Binary32.toUInt32 (vacc * (Binary32.ofBits 0x447a0000 /- 1000 -/))) (Binary32.toUInt32 (sacc * (Binary32.ofBits 0x447a0000 /- 1000 -/))) (Int32.toUInt32 (0 : Int32)) (gps_yaw_cdeg s w (Int8.toUInt8 (Int32.toInt8 (0 : Int32)))))
  return o

/-- C++ `void AP_GPS::send_mavlink_gps2_raw(mavlink_channel_t chan)`, `AP_GPS/AP_GPS.cpp:1427-1466`. -/
def send_mavlink_gps2_raw (s : State) (w : World) (o : Outputs) (chan : mavlink_channel_t) : Outputs := Id.run do
  let mut o := o
  if UInt32.toInt32 (AP_GPS.GPS_Type.toInt (AP_Enum_AP_GPS_GPS_Type.op_to_AP_GPS_GPS_Type s.params[1]!.type)) == UInt32.toInt32 (AP_GPS.GPS_Type.toInt AP_GPS.GPS_Type.GPS_TYPE_NONE) then
    return o
  let t'1 := Int8.toUInt8 (Int32.toInt8 (1 : Int32))
  let mut hacc : Binary32 := (Binary32.ofBits 0x00000000 /- 0.0f -/)
  let mut vacc : Binary32 := (Binary32.ofBits 0x00000000 /- 0.0f -/)
  let mut sacc : Binary32 := (Binary32.ofBits 0x00000000 /- 0.0f -/)
  let mut undulation : Binary32 := (Binary32.ofBits 0x00000000 /- 0.0 -/)
  let mut height_elipsoid_mm : Binary32 := (Binary32.ofBits 0x00000000 /- 0 -/)
  let (t'2, t'3) := get_undulation_uint8_t_float s (Int8.toUInt8 (Int32.toInt8 (1 : Int32))) undulation
  undulation := t'2
  if t'3 then
    height_elipsoid_mm := Int32.toBinary32 (s.state[UInt8.toNat t'1]!.location.alt * (10 : Int32)) - undulation * (Binary32.ofBits 0x447a0000 /- 1000 -/)
  let (t'4, _) := horizontal_accuracy_uint8_t_float s (Int8.toUInt8 (Int32.toInt8 (1 : Int32))) hacc
  hacc := t'4
  let (t'6, _) := vertical_accuracy_uint8_t_float s (Int8.toUInt8 (Int32.toInt8 (1 : Int32))) vacc
  vacc := t'6
  let (t'8, _) := speed_accuracy_uint8_t_float s (Int8.toUInt8 (Int32.toInt8 (1 : Int32))) sacc
  sacc := t'8
  o := o.push (Output.mavlink_msg_gps2_raw_send chan (UInt32.toUInt64 (last_fix_time_ms_uint8_t s (Int8.toUInt8 (Int32.toInt8 (1 : Int32)))) * Int64.toUInt64 (Int32.toInt64 (1000 : Int32))) (AP_GPS_FixType.toInt (status_uint8_t s (Int8.toUInt8 (Int32.toInt8 (1 : Int32))))) s.state[UInt8.toNat t'1]!.location.lat s.state[UInt8.toNat t'1]!.location.lng (UInt32.toInt32 (UInt64.toUInt32 (Int64.toUInt64 (Int32.toInt64 s.state[UInt8.toNat t'1]!.location.alt) * (10 : UInt64)))) (get_hdop_uint8_t s (Int8.toUInt8 (Int32.toInt8 (1 : Int32)))) (get_vdop_uint8_t s (Int8.toUInt8 (Int32.toInt8 (1 : Int32)))) (Binary32.toUInt16 (ground_speed_uint8_t s (Int8.toUInt8 (Int32.toInt8 (1 : Int32))) * (Binary32.ofBits 0x42c80000 /- 100 -/))) (Binary32.toUInt16 (ground_course_uint8_t s (Int8.toUInt8 (Int32.toInt8 (1 : Int32))) * (Binary32.ofBits 0x42c80000 /- 100 -/))) (num_sats_uint8_t s (Int8.toUInt8 (Int32.toInt8 (1 : Int32)))) s.state[1]!.rtk_num_sats s.state[1]!.rtk_age_ms (gps_yaw_cdeg s w (Int8.toUInt8 (Int32.toInt8 (1 : Int32)))) (Binary32.toInt32 height_elipsoid_mm) (Binary32.toUInt32 (hacc * (Binary32.ofBits 0x447a0000 /- 1000 -/))) (Binary32.toUInt32 (vacc * (Binary32.ofBits 0x447a0000 /- 1000 -/))) (Binary32.toUInt32 (sacc * (Binary32.ofBits 0x447a0000 /- 1000 -/))) (Int32.toUInt32 (0 : Int32)))
  return o

/-- C++ `bool AP_GPS::pre_arm_checks(char * failure_msg, uint16_t failure_msg_len)`, `AP_GPS/AP_GPS.cpp:1834-1861`. -/
def pre_arm_checks (s : State) (w : World) (failure_msg : CText) (failure_msg_len : UInt16) : CText × Bool := Id.run do
  let mut failure_msg := failure_msg
  for i' in [0:2] do
    let i : UInt8 := Nat.toUInt8 i'
    if is_rtk_rover s i then
      if Estimator_lib.millis w - s.state[UInt8.toNat i]!.gps_yaw_time_ms > Int32.toUInt32 (15000 : Int32) then
        failure_msg := (CText.fmt (UInt16.toUInt64 failure_msg_len) "GPS[%u] yaw not available" #[Sum.inl (UInt32.toUInt64 (Int32.toUInt32 (UInt32.toInt32 (UInt8.toUInt32 i) + (1 : Int32))))])
        return (failure_msg, false)
  return (failure_msg, true)

/-- C++ `void AP_GPS::broadcast_first_configuration_failure_reason() const`, `AP_GPS/AP_GPS.cpp:1492-1502`. -/
def broadcast_first_configuration_failure_reason (s : State) (w : World) (o : Outputs) : Outputs := Id.run do
  let mut o := o
  let mut unconfigured : UInt8 := (0 : UInt8)  -- uninitialized in C++; assigned before every read
  let (t'1, t'2) := first_unconfigured_gps s w unconfigured
  unconfigured := t'1
  if t'2 then
    if s.drivers[UInt8.toNat unconfigured]! == WPtr.null then
      o := o.push (Output.send_text (6 : UInt32) "GPS %d: was not found" #[Sum.inl (Int64.toUInt64 (Int32.toInt64 (UInt32.toInt32 (UInt8.toUInt32 unconfigured) + (1 : Int32))))])
    else
      let t'3 := (WPtr.index s.drivers[UInt8.toNat unconfigured]!)
      pure ()  -- C++ `broadcast_configuration_failure_reason`: no effect in the model
  return o

/-- C++ `enum AP_GPS::GPS_Engine_Setting`, `AP_GPS/AP_GPS.h:162-172`. -/
inductive GPS_Engine_Setting where
  | GPS_ENGINE_NONE
  | GPS_ENGINE_PORTABLE
  | GPS_ENGINE_STATIONARY
  | GPS_ENGINE_PEDESTRIAN
  | GPS_ENGINE_AUTOMOTIVE
  | GPS_ENGINE_SEA
  | GPS_ENGINE_AIRBORNE_1G
  | GPS_ENGINE_AIRBORNE_2G
  | GPS_ENGINE_AIRBORNE_4G
deriving DecidableEq, Inhabited

/-- The value of each enumerator of `AP_GPS::GPS_Engine_Setting` (underlying type `int32_t`). -/
def GPS_Engine_Setting.toInt : GPS_Engine_Setting → Int32
  | .GPS_ENGINE_NONE => (-1 : Int32)
  | .GPS_ENGINE_PORTABLE => (0 : Int32)
  | .GPS_ENGINE_STATIONARY => (2 : Int32)
  | .GPS_ENGINE_PEDESTRIAN => (3 : Int32)
  | .GPS_ENGINE_AUTOMOTIVE => (4 : Int32)
  | .GPS_ENGINE_SEA => (5 : Int32)
  | .GPS_ENGINE_AIRBORNE_1G => (6 : Int32)
  | .GPS_ENGINE_AIRBORNE_2G => (7 : Int32)
  | .GPS_ENGINE_AIRBORNE_4G => (8 : Int32)

/-- C++ `AP_GPS::AP_GPS()`, `AP_GPS/AP_GPS.cpp:278-289`. -/
def construct : State := Id.run do
  let mut s : State := {}
  s := { s with params := (Array.replicate 3 AP_GPS.Params.init) }
  s := { s with _navfilter._value := Binary32.toInt8 (Int32.toBinary32 (AP_GPS.GPS_Engine_Setting.toInt AP_GPS.GPS_Engine_Setting.GPS_ENGINE_AIRBORNE_4G)) }
  s := { s with _auto_switch._value := Binary32.toInt8 (Int8.toBinary32 (Int32.toInt8 (AP_GPS.GPSAutoSwitch.toInt AP_GPS.GPSAutoSwitch.USE_BEST))) }
  s := { s with _sbas_mode._value := Binary32.toInt8 (Binary32.ofBits 0x40000000 /- (float)2 -/) }
  s := { s with _min_elevation._value := Binary32.toInt8 (Binary32.ofBits 0xc2c80000 /- (float)-100 -/) }
  s := { s with _inject_to._value := Binary32.toInt8 (Binary32.ofBits 0x42fe0000 /- (float)127 -/) }
  s := { s with _raw_data._value := Binary32.toInt8 (Binary32.ofBits 0x00000000 /- (float)0 -/) }
  s := { s with _save_config._value := Binary32.toInt8 (Binary32.ofBits 0x40000000 /- (float)2 -/) }
  s := { s with _auto_config._value := Binary32.toInt8 (Binary32.ofBits 0x3f800000 /- (float)1 -/) }
  s := { s with _driver_options._value := Int16.toUInt16 (Binary32.toInt16 (Binary32.ofBits 0x00000000 /- (float)0 -/)) }
  s := { s with _primary._value := Binary32.toInt8 (Binary32.ofBits 0x00000000 /- (float)0 -/) }
  if false /- C++ `_singleton != nullptr` -/ then
    pure ()  -- C++ `AP_HAL::panic(...)`: left out (--drop)
  pure ()  -- C++ `_singleton = this`: the pointer is the class's one World object (--world)
  return s

end AP_GPS

end Estimator_lib
