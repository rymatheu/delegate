import ArduLean.Runtime.CFloat
import ArduLean.Estimator.libraries.AP_HAL.AP_HAL
import ArduLean.Estimator.libraries.AP_Math.AP_Math
import ArduLean.Estimator.World
import ArduLean.Estimator.libraries.AP_Param.AP_Param
import ArduLean.Estimator.libraries.AP_Baro.AP_Baro
import ArduLean.Estimator.libraries.AP_Math.AP_Math_2
import ArduLean.Estimator.World_2
import ArduLean.Estimator.libraries.AP_Baro.AP_Baro_2
import ArduLean.Estimator.World_3

/-!
ArduPilot `libraries/AP_Baro`, part 3 of 4. Sources: `libraries/AP_Baro/AP_Baro_Backend.cpp`, `libraries/AP_Baro/AP_Baro.cpp`.

Items of `lean/Estimator_lib.lean` (the estimator translation), unchanged; placed by `tools/split_modules.py` (`ArduLean/Estimator/INDEX.md`).
-/

open FloatLib.Floats (Binary32 Binary64)

set_option maxRecDepth 200000
-- AP_DAL's `const log_RISH old_RISH = _RISH;` read only by WRITE_REPLAY_BLOCK_IFCHANGED, which is `(void)old`
-- without logging (HAL_LOGGING_ENABLED 0): an unused binding, as in the C++
set_option linter.unusedVariables false

namespace Estimator_lib

namespace AP_Baro

/-- C++ `float AP_Baro::get_external_temperature(const uint8_t instance) const`, `AP_Baro/AP_Baro.cpp:455-483`. -/
def get_external_temperature_uint8_t (s : State) (w : World) («instance» : UInt8) : Binary32 := Id.run do
  if s._last_external_temperature_ms != Int32.toUInt32 (0 : Int32) && decide (Estimator_lib.millis w - s._last_external_temperature_ms < Int32.toUInt32 (10000 : Int32)) then
    return s._external_temperature
  return Estimator_lib.MIN_float2 (get_temperature_uint8_t s «instance») (Binary32.ofBits 0x420c0000 /- 35 -/)

/-- C++ `float AP_Baro::get_external_temperature() const`, `AP_Baro/AP_Baro.h:176`. -/
def get_external_temperature_void (s : State) (w : World) : Binary32 := Id.run do
  return get_external_temperature_uint8_t s w s._primary

end AP_Baro

namespace AP_Baro

/-- C++ `void AP_Baro::update_calibration()`, `AP_Baro/AP_Baro.cpp:397-418`. -/
def update_calibration (s : State) (w : World) (o : Outputs) : State × Outputs := Id.run do
  let mut s := s
  let mut o := o
  let now : UInt32 := Estimator_lib.millis w
  let do_notify : Bool := decide (now - s._last_notify_ms > Int32.toUInt32 (10000 : Int32))
  if do_notify then
    s := { s with _last_notify_ms := now }
  let t'1 : UInt8 := Int8.toUInt8 (Int32.toInt8 (0 : Int32))
  let t'2 : Int32 := UInt32.toInt32 (UInt8.toUInt32 s._num_sensors)
  for i' in [0:(t'2.toInt - (Int.ofNat t'1.toNat)).toNat] do  -- C++ loop bounded by a runtime value (--runtime-loops)
    let i : UInt8 := t'1 + Nat.toUInt8 i'
    if healthy_uint8_t s i then
      let corrected_pressure : Binary32 := get_sealevel_pressure s (get_pressure_uint8_t s i + s.sensors[UInt8.toNat i]!.p_correction) s._field_elevation_active
      s := { s with sensors := s.sensors.set! (UInt8.toNat i) ({ s.sensors[UInt8.toNat i]! with ground_pressure := AP_ParamT_float_4.set s.sensors[UInt8.toNat i]!.ground_pressure corrected_pressure }) }
    if do_notify then
      o := o.push (Output.AP_Param_notify ("barometer.sensors[" ++ (toString (UInt8.toNat i)) ++ "].ground_pressure"))
  s := { s with _guessed_ground_temperature := get_external_temperature_void s w }
  return (s, o)

end AP_Baro

namespace AP_Baro_SITL

/-- C++ `void AP_Baro_SITL::_timer()`, `reference/hal/sensors_baro.cpp:27-38`. -/
def _timer (s : State) (w : World) : State := Id.run do
  let mut s := s
  let «in» : EstRecord := Estimator_lib.est_input w
  if !«in».baro || UInt32.toInt32 (UInt8.toUInt32 s._instance) != (0 : Int32) then
    return s
  pure ()  -- C++ `_getsem37`: a semaphore, which does nothing here (one thread, --semaphores)
  s := { s with _recent_press := «in».baro_pa }
  s := { s with _recent_temp := «in».baro_degc }
  s := { s with _last_sample_time := Estimator_lib.millis w }
  s := { s with _has_sample := true }
  return s

end AP_Baro_SITL

namespace AP_Baro_SITL

/-- C++ `void AP_Baro_Backend::set_bus_id(uint8_t instance, uint32_t id)`, `AP_Baro/AP_Baro_Backend.cpp:23-26` (a member of `AP_Baro_Backend`, translated for `AP_Baro_SITL`). -/
def set_bus_id (w : World) («instance» : UInt8) (id : UInt32) : World := Id.run do
  let mut w := w
  w := { w with barometer.sensors := w.barometer.sensors.set! (UInt8.toNat «instance») ({ w.barometer.sensors[UInt8.toNat «instance»]! with bus_id := AP_ParamT_unsigned_int_3.set w.barometer.sensors[UInt8.toNat «instance»]!.bus_id id }) }
  return w

end AP_Baro_SITL

namespace AP_Baro_SITL

/-- C++ `AP_Baro_SITL::AP_Baro_SITL(AP_Baro & )`, `reference/hal/sensors_baro.cpp:14-25`. -/
def init (w : World) (self' : WPtr) : State × World := Id.run do
  let mut s : State := {}
  let mut w := w
  s := AP_Baro_Backend.init s
  s := { s with _sitl := WPtr.sitl }
  s := { s with _buffer := VectorN_AP_Baro_SITL_readings_baro_50.init_void }
  s := { s with _has_sample := false }
  w := Estimator_lib.est_event w Estimator_lib.EST_EV_BARO_INIT
  if s._sitl != WPtr.null then
    let t'1 := w.barometer  -- the object out of the World for the call (--swap-out)
    w := { w with barometer := default }
    let (t'2, t'3) := AP_Baro.register_sensor t'1
    w := { w with barometer := t'2 }
    s := { s with _instance := t'3 }
    w := set_bus_id w s._instance (AP_HAL.Device.make_bus_id Device.BusType.BUS_TYPE_SITL (Int8.toUInt8 (Int32.toInt8 (0 : Int32))) s._instance (UInt32.toUInt8 (AP_Baro_Backend.DevTypes.toInt AP_Baro_Backend.DevTypes.DEVTYPE_BARO_SITL)))
    let t'4 := w.est_scheduler  -- the object out of the World for the call (--swap-out)
    w := { w with est_scheduler := default }
    w := { w with est_scheduler := EstScheduler.register_timer_process t'4 (WFun.AP_Baro_SITL__timer self') }
  return (s, w)

end AP_Baro_SITL

namespace AP_Baro_SITL

/-- C++ `void AP_Baro_Backend::_copy_to_frontend(uint8_t instance, float pressure, float temperature)`, `AP_Baro/AP_Baro_Backend.cpp:63-79` (a member of `AP_Baro_Backend`, translated for `AP_Baro_SITL`). -/
def _copy_to_frontend (w : World) («instance» : UInt8) (pressure : Binary32) (temperature : Binary32) : World := Id.run do
  let mut w := w
  if UInt32.toInt32 (UInt8.toUInt32 «instance») ≥ UInt32.toInt32 (UInt8.toUInt32 w.barometer._num_sensors) then
    return w
  let now : UInt32 := Estimator_lib.millis w
  if !(Estimator_lib.is_equal_float2 w.barometer.sensors[UInt8.toNat «instance»]!.pressure pressure) || !(Estimator_lib.is_equal_float2 w.barometer.sensors[UInt8.toNat «instance»]!.temperature temperature) then
    w := { w with barometer.sensors := w.barometer.sensors.set! (UInt8.toNat «instance») ({ w.barometer.sensors[UInt8.toNat «instance»]! with last_change_ms := now }) }
  w := { w with barometer.sensors := w.barometer.sensors.set! (UInt8.toNat «instance») ({ w.barometer.sensors[UInt8.toNat «instance»]! with pressure := pressure }) }
  w := { w with barometer.sensors := w.barometer.sensors.set! (UInt8.toNat «instance») ({ w.barometer.sensors[UInt8.toNat «instance»]! with temperature := temperature }) }
  w := { w with barometer.sensors := w.barometer.sensors.set! (UInt8.toNat «instance») ({ w.barometer.sensors[UInt8.toNat «instance»]! with last_update_ms := now }) }
  return w

end AP_Baro_SITL

namespace AP_Baro_SITL

/-- C++ `void AP_Baro_SITL::update()`, `reference/hal/sensors_baro.cpp:45-54`. -/
def update (s : State) (w : World) : State × World := Id.run do
  let mut s := s
  let mut w := w
  w := Estimator_lib.est_event w Estimator_lib.EST_EV_BARO_UPDATE
  if !s._has_sample then
    return (s, w)
  pure ()  -- C++ `_getsem38`: a semaphore, which does nothing here (one thread, --semaphores)
  w := _copy_to_frontend w s._instance s._recent_press s._recent_temp
  s := { s with _has_sample := false }
  return (s, w)

-- not read in the Lean: «instance»
set_option linter.unusedVariables false in
/-- C++ `bool AP_Baro_SITL::healthy(uint8_t instance)`, `reference/hal/sensors_baro.cpp:40-43`. -/
def healthy («instance» : UInt8) : Bool := Id.run do
  return true

/-- C++ `void AP_Baro_SITL::update_healthy_flag(uint8_t instance)`, `AP_Baro/AP_Baro_SITL.h:25`. -/
def update_healthy_flag (w : World) («instance» : UInt8) : World := Id.run do
  let mut w := w
  w := { w with barometer.sensors := w.barometer.sensors.set! (UInt8.toNat «instance») ({ w.barometer.sensors[UInt8.toNat «instance»]! with healthy := healthy «instance» }) }
  return w

/-- C++ `void AP_Baro_Backend::backend_update(uint8_t instance)`, `AP_Baro/AP_Baro_Backend.cpp:53-57` (a member of `AP_Baro_Backend`, translated for `AP_Baro_SITL`). -/
def backend_update (s : State) (w : World) («instance» : UInt8) : State × World := Id.run do
  let mut s := s
  let mut w := w
  let (t'1, t'2) := update s w
  w := t'2
  s := t'1
  w := update_healthy_flag w «instance»
  return (s, w)

end AP_Baro_SITL

end Estimator_lib
