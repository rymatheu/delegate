import ArduLean.Musl.expf
import ArduLean.Musl.powf
import ArduLean.Estimator.libraries.AP_Math.AP_Math
import ArduLean.Estimator.World
import ArduLean.Estimator.libraries.Filter.Filter
import ArduLean.Estimator.libraries.AP_Common.AP_Common
import ArduLean.Estimator.libraries.AP_Param.AP_Param
import ArduLean.Estimator.libraries.SITL.SITL
import ArduLean.Estimator.libraries.AP_GPS.AP_GPS
import ArduLean.Estimator.libraries.AP_AHRS.AP_AHRS
import ArduLean.Estimator.libraries.AP_Baro.AP_Baro
import ArduLean.Estimator.libraries.AP_Math.AP_Math_2
import ArduLean.Estimator.World_2
import ArduLean.Estimator.libraries.AP_Param.AP_Param_2
import ArduLean.Estimator.libraries.AP_Baro.AP_Baro_2
import ArduLean.Estimator.World_3
import ArduLean.Estimator.libraries.AP_GPS.AP_GPS_2
import ArduLean.Estimator.libraries.AP_Baro.AP_Baro_3
import ArduLean.Estimator.World_4
import ArduLean.Estimator.libraries.AP_AHRS.AP_AHRS_3

/-!
ArduPilot `libraries/AP_Baro`, part 4 of 4. Sources: `libraries/AP_Baro/AP_Baro.cpp`, `libraries/AP_Baro/AP_Baro_atmosphere.cpp`.

Items of `lean/Estimator_lib.lean` (the estimator translation), unchanged; placed by `tools/split_modules.py` (`ArduLean/Estimator/INDEX.md`).
-/

open FloatLib.Floats (Binary32 Binary64)

set_option maxRecDepth 200000
-- AP_DAL's `const log_RISH old_RISH = _RISH;` read only by WRITE_REPLAY_BLOCK_IFCHANGED, which is `(void)old`
-- without logging (HAL_LOGGING_ENABLED 0): an unused binding, as in the C++
set_option linter.unusedVariables false

namespace Estimator_lib

namespace AP_Baro

/-- C++ `void AP_Baro::init()`, `AP_Baro/AP_Baro.cpp:604-760`. -/
def init (s : State) (w : World) (o : Outputs) : State × World × Outputs := Id.run do
  let mut s := s
  let mut w := w
  let mut o := o
  s := { s with init_done := true }
  if !(Estimator_lib.is_zero_AP_ParamT_float_4 s._field_elevation) then
    let (t'1, t'2) := AP_ParamT_float_4.set_and_save s._field_elevation o "barometer._field_elevation" (Binary32.ofBits 0x00000000 /- 0.0f -/)
    s := { s with _field_elevation := t'1 }
    o := t'2
    o := o.push (Output.AP_Param_notify "barometer._field_elevation")
  for t'3 in [0:3] do
    s := { s with sensors := s.sensors.set! t'3 ({ s.sensors[t'3]! with bus_id := AP_ParamT_unsigned_int_3.set s.sensors[t'3]!.bus_id (Int32.toUInt32 (0 : Int32)) }) }
  let sitl' : WPtr := WPtr.sitl
  if sitl' == WPtr.null then
    pure ()  -- C++ `AP_HAL::panic(...)`: left out (--drop)
  let mut i : UInt8 := Int8.toUInt8 (Int32.toInt8 (0 : Int32))
  for _ in [0:2^64] do  -- C loop without a constant trip count (--general-loops)
    if !(decide (UInt32.toInt32 (UInt8.toUInt32 i) < Int8.toInt32 (AP_ParamT_signed_char_1.op_to_signed_char w.sitl.baro_count))) then break
    w := { w with barometer := s }  -- this object's state into the World: the call reaches it
    let (t'4, t'5) := AP_Baro_SITL.init w (WPtr.heap'AP_Baro_SITL w.heap'AP_Baro_SITL.size)
    w := t'5
    s := w.barometer  -- this object's state as the call left it
    let t'6 := w.heap'AP_Baro_SITL.size
    w := { w with heap'AP_Baro_SITL := w.heap'AP_Baro_SITL.push t'4 }
    let (t'7, _) := _add_backend s (WPtr.heap'AP_Baro_SITL t'6)
    s := t'7
    for _ in [0:1] do
      if UInt32.toInt32 (UInt8.toUInt32 s._num_drivers) == (3 : Int32) || UInt32.toInt32 (UInt8.toUInt32 s._num_sensors) == (3 : Int32) then
        return (s, w, o)
    i := i + (1 : UInt8)
  return (s, w, o)

/-- C++ `uint32_t AP_Baro::get_last_update() const`, `AP_Baro/AP_Baro.h:170`. -/
def get_last_update_void (s : State) : UInt32 := Id.run do
  return get_last_update_uint8_t s s._primary

/-- C++ `void AP_Baro::update_field_elevation()`, `AP_Baro/AP_Baro.cpp:1000-1038`. -/
def update_field_elevation (s : State) (w : World) (o : Outputs) (inp : Inputs) : State × World × Outputs := Id.run do
  let mut s := s
  let mut w := w
  let mut o := o
  let now_ms : UInt32 := Estimator_lib.millis w
  let mut new_field_elev : Bool := false
  let armed : Bool := inp.get_soft_armed
  if now_ms - s._field_elevation_last_ms ≥ Int32.toUInt32 (1000 : Int32) then
    if Estimator_lib.is_zero_float s._field_elevation_active && Estimator_lib.is_zero_AP_ParamT_float_4 s._field_elevation then
      let mut origin : Location.State := Location.init_void
      let mut t'3 := !armed
      if t'3 then
        let (t'1, t'2) := AP_AHRS.get_origin w.ahrs origin
        origin := t'1
        t'3 := t'2
      if t'3 then
        s := { s with _field_elevation_active := Int32.toBinary32 origin.alt * (Binary32.ofBits 0x3c23d70a /- 0.01 -/) }
        if Estimator_lib.is_zero_float s._field_elevation_active then
          s := { s with _field_elevation_active := (Binary32.ofBits 0x3a83126f /- 0.001f -/) }
        new_field_elev := true
    else if decide (Binary32.abs (s._field_elevation_active - AP_ParamT_float_4.op_to_float s._field_elevation) > (Binary32.ofBits 0x3f800000 /- 1.0 -/)) && !(Estimator_lib.is_zero_AP_ParamT_float_4 s._field_elevation) then
      if !armed then
        s := { s with _field_elevation_active := AP_ParamT_float_4.op_to_float s._field_elevation }
        new_field_elev := true
      else
        s := { s with _field_elevation := AP_ParamT_float_4.set s._field_elevation s._field_elevation_active }
        o := o.push (Output.AP_Param_notify "barometer._field_elevation")
        o := o.push (Output.send_text (1 : UInt32) "Failed to Set Field Elevation: Armed" #[])
  if new_field_elev && !armed then
    s := { s with _field_elevation_last_ms := now_ms }
    w := { w with barometer := s }  -- this object's state into the World: the call reaches it
    let (t'4, t'5) := AP_AHRS.resetHeightDatum w.ahrs w o
    w := t'4
    o := t'5
    s := w.barometer  -- this object's state as the call left it
    let (t'6, t'7) := update_calibration s w o
    s := t'6
    o := t'7
    o := o.push (Output.send_text (6 : UInt32) "Field Elevation Set: %.0fm" #[Sum.inl (Binary64.toBits (Binary32.toBinary64 s._field_elevation_active))])
  return (s, w, o)

/-- C++ `static float AP_Baro::geometric_alt_to_geopotential(float alt)`, `AP_Baro/AP_Baro_atmosphere.cpp:131-134`. -/
def geometric_alt_to_geopotential (alt : Binary32) : Binary32 := Id.run do
  return (Estimator_lib.radius_earth * alt) / (Estimator_lib.radius_earth + alt)

/-- C++ `static float AP_Baro::get_temperature_by_altitude_layer(float alt, int8_t idx)`, `AP_Baro/AP_Baro_atmosphere.cpp:149-155`. -/
def get_temperature_by_altitude_layer (alt : Binary32) (idx : Int8) : Binary32 := Id.run do
  if Estimator_lib.is_zero_float Estimator_lib.atmospheric_1976_consts[Int8.toNatClampNeg idx]!.temp_lapse then
    return Estimator_lib.atmospheric_1976_consts[Int8.toNatClampNeg idx]!.temp_K
  return Estimator_lib.atmospheric_1976_consts[Int8.toNatClampNeg idx]!.temp_K + Estimator_lib.atmospheric_1976_consts[Int8.toNatClampNeg idx]!.temp_lapse * (alt - Estimator_lib.atmospheric_1976_consts[Int8.toNatClampNeg idx]!.amsl_m)

end AP_Baro

namespace AP_Baro

/-- C++ `static float AP_Baro::get_air_density_for_alt_amsl(float alt_amsl)`, `AP_Baro/AP_Baro_atmosphere.cpp:211-230`. -/
def get_air_density_for_alt_amsl (alt_amsl : Binary32) : Binary32 := Id.run do
  let mut alt_amsl := alt_amsl
  alt_amsl := geometric_alt_to_geopotential alt_amsl
  let idx : UInt8 := Estimator_lib.find_atmosphere_layer_by_altitude alt_amsl
  let temp_slope : Binary32 := Estimator_lib.atmospheric_1976_consts[UInt8.toNat idx]!.temp_lapse
  let temp : Binary32 := get_temperature_by_altitude_layer alt_amsl (UInt8.toInt8 idx)
  let mut rho : Binary32 := (Binary32.ofBits 0x00000000 /- 0.0 -/)  -- uninitialized in C++; assigned before every read
  if Estimator_lib.is_zero_float temp_slope then
    let fac : Binary32 := Musl.expf.expf (-(Binary32.ofBits 0x411ce80a /- 9.80665016 -/) / (temp * Estimator_lib.R_specific) * (alt_amsl - Estimator_lib.atmospheric_1976_consts[UInt8.toNat idx]!.amsl_m))
    rho := Estimator_lib.atmospheric_1976_consts[UInt8.toNat idx]!.density * fac
  else
    let fac'2 : Binary32 := (Binary32.ofBits 0x411ce80a /- 9.80665016 -/) / (temp_slope * Estimator_lib.R_specific)
    let temp_ratio : Binary32 := temp / Estimator_lib.atmospheric_1976_consts[UInt8.toNat idx]!.temp_K
    rho := Estimator_lib.atmospheric_1976_consts[UInt8.toNat idx]!.density * Musl.powf.powf temp_ratio (-(fac'2 + (Binary32.ofBits 0x3f800000 /- 1 -/)))
  return rho

-- not read in the Lean: table_size
set_option linter.unusedVariables false in
/-- C++ `float AP_Baro::get_EAS2TAS_extended(float pressure) const`, `AP_Baro/AP_Baro_atmosphere.cpp:235-244`. -/
def get_EAS2TAS_extended (altitude : Binary32) : Binary32 := Id.run do
  let mut density : Binary32 := get_air_density_for_alt_amsl altitude
  if !(Estimator_lib.is_positive_float density) then
    let table_size : UInt8 := UInt64.toUInt8 (8 : UInt64)
    density := Estimator_lib.atmospheric_1976_consts[7]!.density
  return Binary32.sqrt ((Binary32.ofBits 0x3f9ccccd /- 1.22500002 -/) / density)

/-- C++ `float AP_Baro::_get_EAS2TAS() const`, `AP_Baro/AP_Baro_atmosphere.cpp:299-309`. -/
def _get_EAS2TAS (s : State) : Binary32 := Id.run do
  let altitude : Binary32 := get_altitude_AMSL_void s
  return get_EAS2TAS_extended altitude

end AP_Baro

namespace AP_Baro

/-- C++ `void AP_Baro::update()`, `AP_Baro/AP_Baro.cpp:875-976`. -/
def update (s : State) (w : World) (o : Outputs) (inp : Inputs) : State × World × Outputs := Id.run do
  let mut s := s
  let mut w := w
  let mut o := o
  pure ()  -- C++ `_getsem17`: a semaphore, which does nothing here (one thread, --semaphores)
  if Binary32.abs (AP_ParamT_float_4.op_to_float s._alt_offset - s._alt_offset_active) > (Binary32.ofBits 0x3c23d70a /- 0.01f -/) then
    s := { s with _alt_offset_active := ((Binary32.ofBits 0x3f7ae148 /- 0.98f -/) * s._alt_offset_active) + ((Binary32.ofBits 0x3ca3d70a /- 0.02f -/) * AP_ParamT_float_4.op_to_float s._alt_offset) }
  else
    s := { s with _alt_offset_active := AP_ParamT_float_4.op_to_float s._alt_offset }
  let t'1 : UInt8 := Int8.toUInt8 (Int32.toInt8 (0 : Int32))
  let t'2 : Int32 := UInt32.toInt32 (UInt8.toUInt32 s._num_drivers)
  for i' in [0:(t'2.toInt - (Int.ofNat t'1.toNat)).toNat] do  -- C++ loop bounded by a runtime value (--runtime-loops)
    let i : UInt8 := t'1 + Nat.toUInt8 i'
    let t'3 := (WPtr.index s.drivers[UInt8.toNat i]!)
    w := { w with barometer := s }  -- this object's state into the World: the call reaches it
    let t'4 := w.heap'AP_Baro_SITL[t'3]!  -- the object out of its slot for the call (--swap-out)
    w := { w with heap'AP_Baro_SITL := w.heap'AP_Baro_SITL.set! t'3 default }
    let (t'5, t'6) := AP_Baro_SITL.backend_update t'4 w i
    w := t'6
    w := { w with heap'AP_Baro_SITL := w.heap'AP_Baro_SITL.set! t'3 t'5 }
    s := w.barometer  -- this object's state as the call left it
  let t'7 : UInt8 := Int8.toUInt8 (Int32.toInt8 (0 : Int32))
  let t'8 : Int32 := UInt32.toInt32 (UInt8.toUInt32 s._num_sensors)
  for i'2' in [0:(t'8.toInt - (Int.ofNat t'7.toNat)).toNat] do  -- C++ loop bounded by a runtime value (--runtime-loops)
    let i'2 : UInt8 := t'7 + Nat.toUInt8 i'2'
    if s.sensors[UInt8.toNat i'2]!.healthy then
      let ground_pressure : Binary32 := AP_ParamT_float_4.op_to_float s.sensors[UInt8.toNat i'2]!.ground_pressure
      if !(Estimator_lib.is_positive_float ground_pressure) || Binary32.isNaN ground_pressure || Binary32.isInf ground_pressure then
        s := { s with sensors := s.sensors.set! (UInt8.toNat i'2) ({ s.sensors[UInt8.toNat i'2]! with ground_pressure := AP_ParamT_float_4.set s.sensors[UInt8.toNat i'2]!.ground_pressure s.sensors[UInt8.toNat i'2]!.pressure }) }
      let mut altitude : Binary32 := s.sensors[UInt8.toNat i'2]!.altitude
      let corrected_pressure : Binary32 := s.sensors[UInt8.toNat i'2]!.pressure + s.sensors[UInt8.toNat i'2]!.p_correction
      if UInt32.toInt32 (AP_Baro.baro_type_t.toInt s.sensors[UInt8.toNat i'2]!.type) == UInt32.toInt32 (AP_Baro.baro_type_t.toInt AP_Baro.baro_type_t.BARO_TYPE_AIR) then
        altitude := get_altitude_difference s (AP_ParamT_float_4.op_to_float s.sensors[UInt8.toNat i'2]!.ground_pressure) corrected_pressure
        altitude := altitude - s._field_elevation_active
      else if UInt32.toInt32 (AP_Baro.baro_type_t.toInt s.sensors[UInt8.toNat i'2]!.type) == UInt32.toInt32 (AP_Baro.baro_type_t.toInt AP_Baro.baro_type_t.BARO_TYPE_WATER) then
        altitude := (AP_ParamT_float_4.op_to_float s.sensors[UInt8.toNat i'2]!.ground_pressure - corrected_pressure) / (Binary32.ofBits 0x46192000 /- 9800.0f -/) / AP_ParamT_float_4.op_to_float s._specific_gravity
      s := { s with sensors := s.sensors.set! (UInt8.toNat i'2) ({ s.sensors[UInt8.toNat i'2]! with alt_ok := !(Binary32.isNaN altitude || Binary32.isInf altitude) }) }
      if s.sensors[UInt8.toNat i'2]!.alt_ok then
        s := { s with sensors := s.sensors.set! (UInt8.toNat i'2) ({ s.sensors[UInt8.toNat i'2]! with altitude := altitude + s._alt_offset_active }) }
  if healthy_void s then
    s := { s with _climb_rate_filter := DerivativeFilterFloat_Size7.update s._climb_rate_filter (get_altitude_void s) (get_last_update_void s) }
  if decide (Int8.toInt32 (AP_ParamT_signed_char_1.op_to_signed_char s._primary_baro) ≥ (0 : Int32)) && decide (Int8.toInt32 (AP_ParamT_signed_char_1.op_to_signed_char s._primary_baro) < UInt32.toInt32 (UInt8.toUInt32 s._num_sensors)) && healthy_uint8_t s (Int8.toUInt8 (AP_ParamT_signed_char_1.op_to_signed_char s._primary_baro)) then
    s := { s with _primary := Int8.toUInt8 (AP_ParamT_signed_char_1.op_to_signed_char s._primary_baro) }
  else
    s := { s with _primary := Int8.toUInt8 (Int32.toInt8 (0 : Int32)) }
    let t'9 : UInt8 := Int8.toUInt8 (Int32.toInt8 (0 : Int32))
    let t'10 : Int32 := UInt32.toInt32 (UInt8.toUInt32 s._num_sensors)
    for i'3' in [0:(t'10.toInt - (Int.ofNat t'9.toNat)).toNat] do  -- C++ loop bounded by a runtime value (--runtime-loops)
      let i'3 : UInt8 := t'9 + Nat.toUInt8 i'3'
      if healthy_uint8_t s i'3 then
        s := { s with _primary := i'3 }
        break
  let (t'11, t'12, t'13) := update_field_elevation s w o inp
  w := t'12
  s := t'11
  o := t'13
  s := { s with _EAS2TAS := _get_EAS2TAS s }
  return (s, w, o)

end AP_Baro

namespace AP_Baro

-- not read in the Lean: i'2, num_samples, c
set_option linter.unusedVariables false in
/-- C++ `void AP_Baro::calibrate(bool save)`, `AP_Baro/AP_Baro.cpp:297-390`. -/
def calibrate (s : State) (w : World) (o : Outputs) (inp : Inputs) (save : Bool := true) : State × World × Outputs := Id.run do
  let mut s := s
  let mut w := w
  let mut o := o
  let t'1 : UInt8 := Int8.toUInt8 (Int32.toInt8 (0 : Int32))
  let t'2 : Int32 := UInt32.toInt32 (UInt8.toUInt32 s._num_sensors)
  for i' in [0:(t'2.toInt - (Int.ofNat t'1.toNat)).toNat] do  -- C++ loop bounded by a runtime value (--runtime-loops)
    let i : UInt8 := t'1 + Nat.toUInt8 i'
    s := { s with sensors := s.sensors.set! (UInt8.toNat i) ({ s.sensors[UInt8.toNat i]! with calibrated := true }) }
    s := { s with sensors := s.sensors.set! (UInt8.toNat i) ({ s.sensors[UInt8.toNat i]! with alt_ok := true }) }
  if inp.was_watchdog_reset then
    o := o.push (Output.send_text (6 : UInt32) "Baro: skipping calibration after WDG reset" #[])
    return (s, w, o)
  if Int8.toInt32 (AP_ParamT_signed_char_1.op_to_signed_char w.sitl.baro_count) == (0 : Int32) then
    return (s, w, o)
  o := o.push (Output.send_text (6 : UInt32) "Calibrating barometer" #[])
  let (t'3, t'4) := AP_ParamT_float_4.set_and_save s._alt_offset o "barometer._alt_offset" (Binary32.ofBits 0x00000000 /- 0 -/)
  s := { s with _alt_offset := t'3 }
  o := t'4
  for _ in [0:10] do
    let tstart : UInt32 := Estimator_lib.millis w
    for _ in [0:2^64] do  -- C loop without a constant trip count (--general-loops)
      let (t'5, t'6, t'7) := update s w o inp
      w := t'6
      s := t'5
      o := t'7
      if Estimator_lib.millis w - tstart > Int32.toUInt32 (500 : Int32) then
        pure ()  -- C++ `AP_BoardConfig::config_error(...)`: left out (--drop)
      let t'8 := w.est_scheduler  -- the object out of the World for the call (--swap-out)
      w := { w with est_scheduler := default }
      let (t'9, t'10, t'11) := EstScheduler.delay t'8 w o (Int16.toUInt16 (Int32.toInt16 (10 : Int32)))
      w := t'10
      w := { w with est_scheduler := t'9 }
      o := t'11
      if !(!(healthy_void s)) then break
    let t'12 := w.est_scheduler  -- the object out of the World for the call (--swap-out)
    w := { w with est_scheduler := default }
    let (t'13, t'14, t'15) := EstScheduler.delay t'12 w o (Int16.toUInt16 (Int32.toInt16 (100 : Int32)))
    w := t'14
    w := { w with est_scheduler := t'13 }
    o := t'15
  let mut sum_pressure : Array Binary32 := Array.replicate 3 (Binary32.ofBits 0x00000000 /- 0.0 -/)
  let mut count : Array UInt8 := Array.replicate 3 (0 : UInt8)
  let num_samples : UInt8 := Int8.toUInt8 (Int32.toInt8 (5 : Int32))
  for _ in [0:5] do
    let tstart'2 : UInt32 := Estimator_lib.millis w
    for _ in [0:2^64] do  -- C loop without a constant trip count (--general-loops)
      let (t'16, t'17, t'18) := update s w o inp
      w := t'17
      s := t'16
      o := t'18
      if Estimator_lib.millis w - tstart'2 > Int32.toUInt32 (500 : Int32) then
        pure ()  -- C++ `AP_BoardConfig::config_error(...)`: left out (--drop)
      if !(!(healthy_void s)) then break
    let t'19 : UInt8 := Int8.toUInt8 (Int32.toInt8 (0 : Int32))
    let t'20 : Int32 := UInt32.toInt32 (UInt8.toUInt32 s._num_sensors)
    for i'3' in [0:(t'20.toInt - (Int.ofNat t'19.toNat)).toNat] do  -- C++ loop bounded by a runtime value (--runtime-loops)
      let i'3 : UInt8 := t'19 + Nat.toUInt8 i'3'
      if healthy_uint8_t s i'3 then
        sum_pressure := sum_pressure.set! (UInt8.toNat i'3) (sum_pressure[UInt8.toNat i'3]! + s.sensors[UInt8.toNat i'3]!.pressure)
        count := count.set! (UInt8.toNat i'3) (Int8.toUInt8 (Int32.toInt8 (UInt32.toInt32 (UInt8.toUInt32 count[UInt8.toNat i'3]!) + (1 : Int32))))
    let t'21 := w.est_scheduler  -- the object out of the World for the call (--swap-out)
    w := { w with est_scheduler := default }
    let (t'22, t'23, t'24) := EstScheduler.delay t'21 w o (Int16.toUInt16 (Int32.toInt16 (100 : Int32)))
    w := t'23
    w := { w with est_scheduler := t'22 }
    o := t'24
  let t'25 : UInt8 := Int8.toUInt8 (Int32.toInt8 (0 : Int32))
  let t'26 : Int32 := UInt32.toInt32 (UInt8.toUInt32 s._num_sensors)
  for i'4' in [0:(t'26.toInt - (Int.ofNat t'25.toNat)).toNat] do  -- C++ loop bounded by a runtime value (--runtime-loops)
    let i'4 : UInt8 := t'25 + Nat.toUInt8 i'4'
    if UInt32.toInt32 (UInt8.toUInt32 count[UInt8.toNat i'4]!) == (0 : Int32) then
      s := { s with sensors := s.sensors.set! (UInt8.toNat i'4) ({ s.sensors[UInt8.toNat i'4]! with calibrated := false }) }
    else
      if save then
        let p0_sealevel : Binary32 := get_sealevel_pressure s (sum_pressure[UInt8.toNat i'4]! / Int32.toBinary32 (UInt32.toInt32 (UInt8.toUInt32 count[UInt8.toNat i'4]!))) s._field_elevation_active
        let (t'27, t'28) := AP_ParamT_float_4.set_and_save s.sensors[UInt8.toNat i'4]!.ground_pressure o ("barometer.sensors[" ++ (toString (UInt8.toNat i'4)) ++ "].ground_pressure") p0_sealevel
        s := { s with sensors := s.sensors.set! (UInt8.toNat i'4) ({ s.sensors[UInt8.toNat i'4]! with ground_pressure := t'27 }) }
        o := t'28
  s := { s with _guessed_ground_temperature := get_external_temperature_void s w }
  let mut num_calibrated : UInt8 := Int8.toUInt8 (Int32.toInt8 (0 : Int32))
  let t'29 : UInt8 := Int8.toUInt8 (Int32.toInt8 (0 : Int32))
  let t'30 : Int32 := UInt32.toInt32 (UInt8.toUInt32 s._num_sensors)
  for i'5' in [0:(t'30.toInt - (Int.ofNat t'29.toNat)).toNat] do  -- C++ loop bounded by a runtime value (--runtime-loops)
    let i'5 : UInt8 := t'29 + Nat.toUInt8 i'5'
    if s.sensors[UInt8.toNat i'5]!.calibrated then
      o := o.push (Output.send_text (6 : UInt32) "Barometer %u calibration complete" #[Sum.inl (Int64.toUInt64 (Int32.toInt64 (UInt32.toInt32 (UInt8.toUInt32 i'5) + (1 : Int32))))])
      num_calibrated := num_calibrated + (1 : UInt8)
  if num_calibrated != (0 : UInt8) then
    return (s, w, o)
  pure ()  -- C++ `AP_BoardConfig::config_error(...)`: left out (--drop)
  return (s, w, o)

/-- C++ `float AP_Baro::get_pressure() const`, `AP_Baro/AP_Baro.h:72`. -/
def get_pressure_void (s : State) : Binary32 := Id.run do
  return get_pressure_uint8_t s s._primary

/-- C++ `float AP_Baro::get_temperature() const`, `AP_Baro/AP_Baro.h:83`. -/
def get_temperature_void (s : State) : Binary32 := Id.run do
  return get_temperature_uint8_t s s._primary

/-- C++ `float AP_Baro::get_ground_pressure(uint8_t i) const`, `AP_Baro/AP_Baro.h:162`. -/
def get_ground_pressure_uint8_t (s : State) (i : UInt8) : Binary32 := Id.run do
  return AP_ParamT_float_4.get_void s.sensors[UInt8.toNat i]!.ground_pressure

/-- C++ `float AP_Baro::get_ground_pressure() const`, `AP_Baro/AP_Baro.h:161`. -/
def get_ground_pressure_void (s : State) : Binary32 := Id.run do
  return get_ground_pressure_uint8_t s s._primary

/-- C++ `float AP_Baro::get_baro_drift_offset() const`, `AP_Baro/AP_Baro.h:199`. -/
def get_baro_drift_offset (s : State) : Binary32 := Id.run do
  return s._alt_offset_active

/-- C++ `void AP_Baro::set_log_baro_bit(uint32_t bit)`, `AP_Baro/AP_Baro.h:210`. -/
def set_log_baro_bit (s : State) (bit : UInt32) : State := Id.run do
  let mut s := s
  s := { s with _log_baro_bit := bit }
  return s

/-- C++ `bool AP_Baro::all_healthy() const`, `AP_Baro/AP_Baro.cpp:1088-1096`. -/
def all_healthy (s : State) : Bool := Id.run do
  for i' in [0:s._num_sensors.toNat] do
    let i : UInt8 := Nat.toUInt8 i'
    if !(healthy_uint8_t s i) then
      return false
  return decide (UInt32.toInt32 (UInt8.toUInt32 s._num_sensors) > (0 : Int32))

/-- C++ `bool AP_Baro::arming_checks(size_t buflen, char * buffer) const`, `AP_Baro/AP_Baro.cpp:1138-1164`. -/
def arming_checks (s : State) (w : World) (buflen : UInt64) (buffer : CText) : CText × Bool := Id.run do
  let mut buffer := buffer
  if !(all_healthy s) then
    buffer := (CText.fmt buflen "not healthy" #[])
    return (buffer, false)
  if decide (AP_ParamT_float_4.op_to_float s._alt_error_max > (Binary32.ofBits 0x00000000 /- 0 -/)) && decide (AP_GPS_FixType.toInt (AP_GPS.status_void w.gps) ≥ AP_GPS_FixType.toInt AP_GPS_FixType.FIX_3D) then
    let alt_amsl : Binary32 := Int32.toBinary32 (AP_GPS.location_void w.gps).alt * (Binary32.ofBits 0x3c23d70a /- 0.01 -/)
    let alt_pressure : Binary32 := get_altitude_difference s (Binary32.ofBits 0x47c5e682 /- 101325.016 -/) (get_pressure_void s)
    let error : Binary32 := Binary32.abs (alt_amsl - alt_pressure)
    if error > AP_ParamT_float_4.op_to_float s._alt_error_max then
      buffer := (CText.fmt buflen "GPS alt error %.0fm (see BARO_ALTERR_MAX)" #[Sum.inl (Binary64.toBits (Binary32.toBinary64 error))])
      return (buffer, false)
  return (buffer, true)

/-- C++ `AP_Baro::AP_Baro()`, `AP_Baro/AP_Baro.cpp:286-292`. -/
def construct : State := Id.run do
  let mut s : State := {}
  s := { s with _climb_rate_filter := DerivativeFilterFloat_Size7.init }
  pure ()  -- C++ `_singleton = this`: the pointer is the class's one World object (--world)
  s := { s with sensors := s.sensors.set! 0 ({ s.sensors[0]! with ground_pressure._value := (Binary32.ofBits 0x00000000 /- (float)0 -/) }) }
  s := { s with _user_ground_temperature._value := (Binary32.ofBits 0x00000000 /- (float)0 -/) }
  s := { s with _alt_offset._value := (Binary32.ofBits 0x00000000 /- (float)0 -/) }
  s := { s with _primary_baro._value := Binary32.toInt8 (Binary32.ofBits 0x00000000 /- (float)0 -/) }
  s := { s with _ext_bus._value := Binary32.toInt8 (Binary32.ofBits 0xbf800000 /- (float)-1 -/) }
  s := { s with _specific_gravity._value := (Binary32.ofBits 0x3f800000 /- (float)1 -/) }
  s := { s with sensors := s.sensors.set! 1 ({ s.sensors[1]! with ground_pressure._value := (Binary32.ofBits 0x00000000 /- (float)0 -/) }) }
  s := { s with sensors := s.sensors.set! 2 ({ s.sensors[2]! with ground_pressure._value := (Binary32.ofBits 0x00000000 /- (float)0 -/) }) }
  s := { s with _filter_range._value := Binary32.toInt8 (Binary32.ofBits 0x00000000 /- (float)0 -/) }
  s := { s with sensors := s.sensors.set! 0 ({ s.sensors[0]! with bus_id._value := Int32.toUInt32 (Binary32.toInt32 (Binary32.ofBits 0x00000000 /- (float)0 -/)) }) }
  s := { s with sensors := s.sensors.set! 1 ({ s.sensors[1]! with bus_id._value := Int32.toUInt32 (Binary32.toInt32 (Binary32.ofBits 0x00000000 /- (float)0 -/)) }) }
  s := { s with sensors := s.sensors.set! 2 ({ s.sensors[2]! with bus_id._value := Int32.toUInt32 (Binary32.toInt32 (Binary32.ofBits 0x00000000 /- (float)0 -/)) }) }
  s := { s with _field_elevation._value := (Binary32.ofBits 0x00000000 /- (float)0 -/) }
  s := { s with _alt_error_max._value := (Binary32.ofBits 0x44fa0000 /- (float)2000 -/) }
  s := { s with _options._value := Int16.toUInt16 (Binary32.toInt16 (Binary32.ofBits 0x00000000 /- (float)0 -/)) }
  s := { s with _field_elevation_active := AP_ParamT_float_4.op_to_float s._field_elevation }
  return s

end AP_Baro

end Estimator_lib
