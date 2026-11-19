import ArduLean.Musl.cosf
import ArduLean.Musl.sinf
import ArduLean.Estimator.libraries.GCS_MAVLink.GCS_MAVLink
import ArduLean.Estimator.mavlink.mavlink
import ArduLean.Estimator.libraries.AP_Math.AP_Math
import ArduLean.Estimator.World
import ArduLean.Estimator.libraries.AP_Common.AP_Common
import ArduLean.Estimator.libraries.AP_Param.AP_Param
import ArduLean.Estimator.libraries.AP_NavEKF.AP_NavEKF
import ArduLean.Estimator.libraries.AP_GPS.AP_GPS
import ArduLean.Estimator.libraries.AP_InertialSensor.AP_InertialSensor
import ArduLean.Estimator.libraries.AP_NavEKF3.AP_NavEKF3
import ArduLean.Estimator.libraries.AP_AHRS.AP_AHRS
import ArduLean.Estimator.libraries.AP_Baro.AP_Baro
import ArduLean.Estimator.World_2
import ArduLean.Estimator.libraries.AP_Param.AP_Param_2
import ArduLean.Estimator.libraries.AP_Compass.AP_Compass_2
import ArduLean.Estimator.libraries.AP_NavEKF3.AP_NavEKF3_2
import ArduLean.Estimator.World_3
import ArduLean.Estimator.libraries.AP_Compass.AP_Compass_3
import ArduLean.Estimator.libraries.AP_GPS.AP_GPS_2
import ArduLean.Estimator.libraries.AP_NavEKF3.AP_NavEKF3_3

/-!
ArduPilot `libraries/AP_AHRS`, part 2 of 4. Sources: `libraries/AP_AHRS/AP_AHRS.cpp`, `libraries/AP_AHRS/AP_AHRS.h`, `libraries/AP_AHRS/AP_AHRS_DCM.cpp`, `libraries/AP_AHRS/AP_AHRS_Backend.cpp`, `libraries/AP_AHRS/AP_AHRS_NavEKF3.h`, `libraries/AP_AHRS/AP_AHRS_View.cpp`, `libraries/AP_AHRS/AP_AHRS_NavEKF3.cpp`.

Items of `lean/Estimator_lib.lean` (the estimator translation), unchanged; placed by `tools/split_modules.py` (`ArduLean/Estimator/INDEX.md`).
-/

open FloatLib.Floats (Binary32 Binary64)

set_option maxRecDepth 200000
-- AP_DAL's `const log_RISH old_RISH = _RISH;` read only by WRITE_REPLAY_BLOCK_IFCHANGED, which is `(void)old`
-- without logging (HAL_LOGGING_ENABLED 0): an unused binding, as in the C++
set_option linter.unusedVariables false

namespace Estimator_lib

namespace AP_AHRS

/-- C++ `void AP_AHRS::update_orientation()`, `AP_AHRS/AP_AHRS_Backend.cpp:67-88`. -/
def update_orientation (s : State) (w : World) (inp : Inputs) : State × World := Id.run do
  let mut s := s
  let mut w := w
  let now_ms : UInt32 := Estimator_lib.millis w
  if s.last_orientation_update_ms != Int32.toUInt32 (0 : Int32) && decide (now_ms - s.last_orientation_update_ms < Int32.toUInt32 (1000 : Int32)) then
    return (s, w)
  if inp.get_soft_armed && s.last_orientation_update_ms != Int32.toUInt32 (0 : Int32) then
    return (s, w)
  s := { s with last_orientation_update_ms := now_ms }
  let orientation : Rotation := Rotation.ofInt (Int8.toUInt8 (AP_ParamT_signed_char_1.get_void s._board_orientation))
  let t'1 := w.ins  -- the object out of the World for the call (--swap-out)
  w := { w with ins := default }
  w := { w with ins := AP_InertialSensor.set_board_orientation t'1 orientation }
  let t'2 := w.compass  -- the object out of the World for the call (--swap-out)
  w := { w with compass := default }
  w := { w with compass := Compass.set_board_orientation t'2 orientation }
  return (s, w)

/-- C++ `const Location & AP_AHRS::get_home() const`, `AP_AHRS/AP_AHRS.h:592-594`. -/
def get_home (s : State) : Location.State := Id.run do
  return s._home

/-- C++ `VehicleClass AP_AHRS::get_vehicle_class() const`, `AP_AHRS/AP_AHRS.h:751-753`. -/
def get_vehicle_class (s : State) : AP_AHRS.VehicleClass := Id.run do
  return s._vehicle_class

/-- C++ `bool AP_AHRS::get_fly_forward() const`, `AP_AHRS/AP_AHRS.h:736-738`. -/
def get_fly_forward (s : State) : Bool := Id.run do
  return s.fly_forward

/-- C++ `bool AP_AHRS::get_takeoff_expected() const`, `AP_AHRS/AP_AHRS.h:717-719`. -/
def get_takeoff_expected (s : State) : Bool := Id.run do
  return s.takeoff_expected

/-- C++ `bool AP_AHRS::get_touchdown_expected() const`, `AP_AHRS/AP_AHRS.h:723-725`. -/
def get_touchdown_expected (s : State) : Bool := Id.run do
  return s.touchdown_expected

end AP_AHRS

namespace AP_AHRS

/-- C++ `const Vector3f & AP_AHRS::get_trim() const`, `AP_AHRS/AP_AHRS.h:553`. -/
def get_trim (s : State) : Vector3f.State := Id.run do
  return AP_ParamV_Vector3_float_5.get_void s._trim

/-- C++ `EKFType AP_AHRS::configured_ekf_type() const`, `AP_AHRS/AP_AHRS.h:524-526`. -/
def configured_ekf_type (s : State) : AP_AHRS.EKFType := Id.run do
  return s.state.configured_ekf_type

/-- C++ `const Matrix3f & AP_AHRS::get_rotation_vehicle_body_to_autopilot_body() const`, `AP_AHRS/AP_AHRS.h:563`. -/
def get_rotation_vehicle_body_to_autopilot_body (s : State) : Matrix3f.State := Id.run do
  return s._rotation_vehicle_body_to_autopilot_body

/-- C++ `void AP_AHRS::set_takeoff_expected(bool b)`, `AP_AHRS/AP_AHRS_Backend.cpp:287-291`. -/
def set_takeoff_expected (s : State) (w : World) (b : Bool) : State := Id.run do
  let mut s := s
  s := { s with takeoff_expected := b }
  s := { s with takeoff_expected_start_ms := Estimator_lib.millis w }
  return s

/-- C++ `enum AP_AHRS::Flags`, `AP_AHRS/AP_AHRS.h:50-52`. -/
inductive Flags where
  | FLAG_ALWAYS_USE_EKF
deriving DecidableEq, Inhabited

/-- The value of each enumerator of `AP_AHRS::Flags` (underlying type `uint32_t`). -/
def Flags.toInt : Flags → UInt32
  | .FLAG_ALWAYS_USE_EKF => (1 : UInt32)

/-- C++ `bool AP_AHRS::always_use_EKF() const`, `AP_AHRS/AP_AHRS.h:810-812`. -/
def always_use_EKF (s : State) : Bool := Id.run do
  return UInt32.toInt32 (UInt8.toUInt32 s._ekf_flags) &&& UInt32.toInt32 (AP_AHRS.Flags.toInt AP_AHRS.Flags.FLAG_ALWAYS_USE_EKF) != (0 : Int32)

end AP_AHRS

namespace AP_AHRS

/-- C++ `EKFType AP_AHRS::_configured_ekf_type() const`, `AP_AHRS/AP_AHRS.cpp:1090-1134`. -/
def _configured_ekf_type (s : State) : AP_AHRS.EKFType := Id.run do
  let type : AP_AHRS.EKFType := AP_AHRS.EKFType.ofInt (Int8.toUInt8 (AP_Enum_AP_AHRS_EKFType.get_void s._ekf_type))
  match type with
  | .SIM =>
    return type
  | .THREE =>
    return type
  | .DCM =>
    if always_use_EKF s then
      return AP_AHRS.EKFType.THREE
    return AP_AHRS.EKFType.DCM

/-- C++ `AP_AHRS_Backend * AP_AHRS::backend_for_type(EKFType type)`, `AP_AHRS/AP_AHRS.cpp:245-270`. -/
def backend_for_type (type : AP_AHRS.EKFType) : WPtr := Id.run do
  match type with
  | .DCM =>
    return WPtr.ahrs'dcm
  | .THREE =>
    return WPtr.ahrs'ekf3
  | .SIM =>
    return WPtr.ahrs'sim

/-- C++ `AP_AHRS_Backend::Estimates * AP_AHRS::estimates_for_type(EKFType type)`, `AP_AHRS/AP_AHRS.cpp:859-888`. -/
def estimates_for_type (type : AP_AHRS.EKFType) : WPtr := Id.run do
  match type with
  | .DCM =>
    return WPtr.ahrs'dcm_estimates
  | .THREE =>
    return WPtr.ahrs'ekf3_estimates
  | .SIM =>
    return WPtr.ahrs'sim_estimates

/-- C++ `void AP_AHRS::update_configured_ekf_type()`, `AP_AHRS/AP_AHRS.cpp:275-286`. -/
def update_configured_ekf_type (s : State) : State := Id.run do
  let mut s := s
  let new_type : AP_AHRS.EKFType := _configured_ekf_type s
  let new_backend : WPtr := backend_for_type new_type
  if new_backend != WPtr.null then
    s := { s with state.configured_ekf_type := new_type }
    s := { s with configured_backend := new_backend }
    s := { s with configured_estimates := estimates_for_type new_type }
    return s
  pure ()  -- C++ `AP_InternalError::error(...)`: left out (--drop)
  return s

/-- C++ `EKFType AP_AHRS::fallback_active_EKF_type() const`, `AP_AHRS/AP_AHRS.cpp:1300-1332`. -/
def fallback_active_EKF_type : AP_AHRS.EKFType := Id.run do
  return AP_AHRS.EKFType.DCM

/-- C++ `enum class AP_AHRS::Options`, `AP_AHRS/AP_AHRS.h:1074-1080`. -/
inductive Options where
  | DISABLE_DCM_FALLBACK_FW
  | DISABLE_DCM_FALLBACK_VTOL
  | DISABLE_AIRSPEED_EKF_CHECK
  | RECORD_ORIGIN
  | USE_RECORDED_ORIGIN_FOR_NONGPS
deriving DecidableEq, Inhabited

/-- The value of each enumerator of `AP_AHRS::Options` (underlying type `uint16_t`). -/
def Options.toInt : Options → UInt16
  | .DISABLE_DCM_FALLBACK_FW => (1 : UInt16)
  | .DISABLE_DCM_FALLBACK_VTOL => (2 : UInt16)
  | .DISABLE_AIRSPEED_EKF_CHECK => (4 : UInt16)
  | .RECORD_ORIGIN => (8 : UInt16)
  | .USE_RECORDED_ORIGIN_FOR_NONGPS => (16 : UInt16)

end AP_AHRS

namespace AP_AHRS

/-- C++ `bool AP_AHRS::option_set(Options option) const`, `AP_AHRS/AP_AHRS.h:1084-1086`. -/
def option_set (s : State) (option : AP_AHRS.Options) : Bool := Id.run do
  return (UInt32.toInt32 (UInt16.toUInt32 (AP_ParamT_unsigned_short_2.op_to_unsigned_short s._options)) &&& UInt32.toInt32 (UInt16.toUInt32 (AP_AHRS.Options.toInt option))) != (0 : Int32)

end AP_AHRS

namespace AP_AHRS_DCM

/-- C++ `bool AP_AHRS_DCM::yaw_source_available() const`, `AP_AHRS/AP_AHRS_DCM.cpp:1518-1521`. -/
def yaw_source_available (w : World) : Bool := Id.run do
  return Compass.use_for_yaw_void w.compass

end AP_AHRS_DCM

namespace AP_AHRS

/-- C++ `EKFType AP_AHRS::_active_EKF_type() const`, `AP_AHRS/AP_AHRS.cpp:1136-1298`. -/
def _active_EKF_type (s : State) (w : World) (inp : Inputs) : AP_AHRS.EKFType := Id.run do
  let mut ret : AP_AHRS.EKFType := fallback_active_EKF_type
  match configured_ekf_type s with
  | .DCM =>
    return AP_AHRS.EKFType.DCM
  | .THREE =>
    if !s.ekf3.started then
      return fallback_active_EKF_type
    if always_use_EKF s then
      if UInt32.toInt32 (UInt16.toUInt32 s.ekf3_estimates.filter_faults) == (0 : Int32) then
        ret := AP_AHRS.EKFType.THREE
    else if s.ekf3_estimates.healthy then
      ret := AP_AHRS.EKFType.THREE
  | .SIM =>
    ret := AP_AHRS.EKFType.SIM
  if s._vehicle_class == AP_AHRS.VehicleClass.FIXED_WING || s._vehicle_class == AP_AHRS.VehicleClass.GROUND then
    let mut should_use_gps : Bool := true
    let mut filt_state : UInt32 := (0 : UInt32)
    match ret with
    | .DCM =>
      pure ()
    | .THREE =>
      filt_state := s.ekf3_estimates.filter_status
      should_use_gps := NavEKF3.configuredToUseGPSForPosXY w.EKF3
    | .SIM =>
      filt_state := s.sim_estimates.filter_status
    let can_use_dcm : Bool := AP_AHRS_DCM.yaw_source_available w || s.fly_forward
    let can_use_ekf : Bool := (filt_state >>> 0 &&& 1 != 0) && ((s._vehicle_class == AP_AHRS.VehicleClass.GROUND) || ((filt_state >>> 2 &&& 1 != 0) && (filt_state >>> 5 &&& 1 != 0)))
    if !can_use_dcm && can_use_ekf then
      return ret
    else if !can_use_ekf then
      return AP_AHRS.EKFType.DCM
    let disable_dcm_fallback : Bool := if s.fly_forward then option_set s AP_AHRS.Options.DISABLE_DCM_FALLBACK_FW else option_set s AP_AHRS.Options.DISABLE_DCM_FALLBACK_VTOL
    if disable_dcm_fallback then
      return ret
    if inp.get_soft_armed && (AP_Enum_GPSUse.op_to_GPSUse s._gps_use != GPSUse.Disable) && should_use_gps && decide (AP_GPS_FixType.toInt (AP_GPS.status_void w.gps) ≥ AP_GPS_FixType.toInt AP_GPS_FixType.FIX_3D) && (!(filt_state >>> 13 &&& 1 != 0) || !(filt_state >>> 4 &&& 1 != 0)) then
      return AP_AHRS.EKFType.DCM
    if inp.get_soft_armed && (filt_state >>> 7 &&& 1 != 0) then
      return AP_AHRS.EKFType.DCM
    if !(filt_state >>> 1 &&& 1 != 0) || (!(filt_state >>> 4 &&& 1 != 0) && !(filt_state >>> 3 &&& 1 != 0)) then
      if (!(Compass.use_for_yaw_void w.compass)) && decide (AP_GPS_FixType.toInt (AP_GPS.status_void w.gps) ≥ AP_GPS_FixType.toInt AP_GPS_FixType.FIX_3D) && decide (AP_GPS.ground_speed_void w.gps < (Binary32.ofBits 0x40000000 /- 2 -/)) then
        if (filt_state >>> 15 &&& 1 != 0) then
          return ret
      return AP_AHRS.EKFType.DCM
  return ret

/-- C++ `void AP_AHRS::update_active_EKF_type()`, `AP_AHRS/AP_AHRS.cpp:288-299`. -/
def update_active_EKF_type (s : State) (w : World) (inp : Inputs) : State := Id.run do
  let mut s := s
  let new_type : AP_AHRS.EKFType := _active_EKF_type s w inp
  let new_backend : WPtr := backend_for_type new_type
  if new_backend != WPtr.null then
    s := { s with state.active_EKF_type := new_type }
    s := { s with active_backend := new_backend }
    s := { s with active_estimates := estimates_for_type new_type }
    return s
  pure ()  -- C++ `AP_InternalError::error(...)`: left out (--drop)
  return s

/-- C++ `EKFType AP_AHRS::active_EKF_type() const`, `AP_AHRS/AP_AHRS.h:808`. -/
def active_EKF_type (s : State) : AP_AHRS.EKFType := Id.run do
  return s.state.active_EKF_type

/-- C++ `bool AP_AHRS::_get_secondary_EKF_type(EKFType & secondary_ekf_type) const`, `AP_AHRS/AP_AHRS.cpp:1335-1381`. -/
def _get_secondary_EKF_type (s : State) (secondary_ekf_type : AP_AHRS.EKFType) : AP_AHRS.EKFType × Bool := Id.run do
  let mut secondary_ekf_type := secondary_ekf_type
  match active_EKF_type s with
  | .DCM =>
    if AP_AHRS.EKFType.ofInt (Int8.toUInt8 (AP_Enum_AP_AHRS_EKFType.get_void s._ekf_type)) == AP_AHRS.EKFType.THREE then
      secondary_ekf_type := AP_AHRS.EKFType.THREE
      return (secondary_ekf_type, true)
    return (secondary_ekf_type, false)
  | .THREE | .SIM =>
    secondary_ekf_type := fallback_active_EKF_type
    return (secondary_ekf_type, true)

/-- C++ `void AP_AHRS::update_secondary_backend_pointers()`, `AP_AHRS/AP_AHRS.cpp:302-310`. -/
def update_secondary_backend_pointers (s : State) : State := Id.run do
  let mut s := s
  let mut secondary_type : AP_AHRS.EKFType := AP_AHRS.EKFType.DCM  -- uninitialized in C++; assigned before every read
  let (t'1, t'2) := _get_secondary_EKF_type s secondary_type
  secondary_type := t'1
  if !t'2 then
    s := { s with secondary_estimates := WPtr.null }
    return s
  s := { s with secondary_estimates := estimates_for_type secondary_type }
  return s

end AP_AHRS

namespace AP_AHRS

/-- C++ `void AP_AHRS::init()`, `AP_AHRS/AP_AHRS.cpp:313-348`. -/
def init (s : State) (w : World) (inp : Inputs) : State × World := Id.run do
  let mut s := s
  let mut w := w
  let (t'1, t'2) := update_orientation s w inp
  w := t'2
  s := t'1
  if Int8.toInt32 (AP_Enum_AP_AHRS_EKFType.get_void s._ekf_type) == (1 : Int32) then
    pure ()  -- C++ `AP_BoardConfig::config_error(...)`: left out (--drop)
  if Int8.toInt32 (AP_Enum_AP_AHRS_EKFType.get_void s._ekf_type) == (2 : Int32) then
    s := { s with _ekf_type := AP_Enum_AP_AHRS_EKFType.set_EKFType s._ekf_type AP_AHRS.EKFType.THREE }
    let t'3 := w.EKF3  -- the object out of the World for the call (--swap-out)
    w := { w with EKF3 := default }
    w := { w with EKF3 := NavEKF3.set_enable t'3 true }
  s := update_configured_ekf_type s
  s := update_active_EKF_type s w inp
  s := update_secondary_backend_pointers s
  s := { s with last_active_ekf_type := s.state.active_EKF_type }
  return (s, w)

end AP_AHRS

namespace AP_AHRS

/-- C++ `void AP_AHRS::update_trim_rotation_matrices()`, `AP_AHRS/AP_AHRS.cpp:363-373`. -/
def update_trim_rotation_matrices (s : State) : State := Id.run do
  let mut s := s
  if Vector3f.op_eq s._last_trim (AP_ParamV_Vector3_float_5.get_void s._trim) then
    return s
  s := { s with _last_trim := AP_ParamV_Vector3_float_5.get_void s._trim }
  s := { s with _rotation_autopilot_body_to_vehicle_body := Matrix3f.from_euler s._rotation_autopilot_body_to_vehicle_body s._last_trim.x s._last_trim.y s._last_trim.z }
  s := { s with _rotation_vehicle_body_to_autopilot_body := Matrix3f.transposed s._rotation_autopilot_body_to_vehicle_body }
  return s

/-- C++ `void AP_AHRS::update_flags()`, `AP_AHRS/AP_AHRS_Backend.cpp:302-311`. -/
def update_flags (s : State) (w : World) : State := Id.run do
  let mut s := s
  let timeout_ms : UInt32 := Int32.toUInt32 (1000 : Int32)
  if s.takeoff_expected && decide (Estimator_lib.millis w - s.takeoff_expected_start_ms > timeout_ms) then
    s := { s with takeoff_expected := false }
  if s.touchdown_expected && decide (Estimator_lib.millis w - s.touchdown_expected_start_ms > timeout_ms) then
    s := { s with touchdown_expected := false }
  return s

/-- C++ `bool AP_AHRS::get_wind_estimation_enabled() const`, `AP_AHRS/AP_AHRS.h:122`. -/
def get_wind_estimation_enabled (s : State) : Bool := Id.run do
  return s.wind_estimation_enabled

/-- C++ `const Matrix3f & AP_AHRS::get_rotation_autopilot_body_to_vehicle_body() const`, `AP_AHRS/AP_AHRS.h:562`. -/
def get_rotation_autopilot_body_to_vehicle_body (s : State) : Matrix3f.State := Id.run do
  return s._rotation_autopilot_body_to_vehicle_body

/-- C++ `uint8_t AP_AHRS::get_max_wind() const`, `AP_AHRS/AP_AHRS.h:144-146`. -/
def get_max_wind (s : State) : UInt8 := Id.run do
  return Int8.toUInt8 (AP_ParamT_signed_char_1.op_to_signed_char s._wind_max)

end AP_AHRS

namespace AP_AHRS_DCM

/-- C++ `bool AP_AHRS_DCM::get_origin(Location & ret) const`, `AP_AHRS/AP_AHRS_DCM.cpp:1507-1515`. -/
def get_origin (s : State) (w : World) (ret : Location.State) : Location.State × Bool := Id.run do
  let mut ret := ret
  ret := s.last_origin
  if Location.is_zero ret then
    ret := AP_AHRS.get_home w.ahrs
  return (ret, !(Location.is_zero ret))

-- not read in the Lean: loc
set_option linter.unusedVariables false in
/-- C++ `bool AP_AHRS_Backend::set_origin(const Location & loc)`, `AP_AHRS/AP_AHRS_Backend.h:341-343` (a member of `AP_AHRS_Backend`, translated for `AP_AHRS_DCM`). -/
def set_origin (loc : Location.State) : Bool := Id.run do
  return false

end AP_AHRS_DCM

namespace AP_AHRS_NavEKF3

/-- C++ `bool AP_AHRS_NavEKF3::get_origin(Location & ret) const`, `AP_AHRS/AP_AHRS_NavEKF3.h:54-56`. -/
def get_origin (w : World) (ret : Location.State) : World × Location.State × Bool := Id.run do
  let mut w := w
  let mut ret := ret
  let (t'1, t'2, t'3) := NavEKF3.getOriginLLH w.EKF3 w ret
  w := t'1
  ret := t'2
  return (w, ret, t'3)

end AP_AHRS_NavEKF3

namespace AP_AHRS_NavEKF3

/-- C++ `bool AP_AHRS_NavEKF3::set_origin(const Location & loc)`, `AP_AHRS/AP_AHRS_NavEKF3.h:57-59`. -/
def set_origin (w : World) (o : Outputs) (loc : Location.State) : World × Outputs × Bool := Id.run do
  let mut w := w
  let mut o := o
  let t'1 := w.EKF3  -- the object out of the World for the call (--swap-out)
  w := { w with EKF3 := default }
  let (t'2, t'3, t'4, t'5) := NavEKF3.setOriginLLH t'1 w o loc
  w := t'3
  w := { w with EKF3 := t'2 }
  o := t'4
  return (w, o, t'5)

end AP_AHRS_NavEKF3

namespace AP_AHRS

/-- C++ `void AP_AHRS::try_set_common_origin(const AP_AHRS_Backend & source_backend, const AP_AHRS_Backend::Estimates & source_estimates)`, `AP_AHRS/AP_AHRS.cpp:493-525`. -/
def try_set_common_origin (s : State) (w : World) (o : Outputs) (inp : Inputs) (source_backend : WPtr) (source_estimates : WPtr) : State × World × Outputs := Id.run do
  let mut s := s
  let mut w := w
  let mut o := o
  if s.done_common_origin then
    return (s, w, o)
  if !((match source_estimates with | .ahrs'dcm_estimates => s.dcm_estimates | .ahrs'ekf3_estimates => s.ekf3_estimates | _ => s.sim_estimates) : AP_AHRS_Backend.Estimates.State).provides_common_origin then
    return (s, w, o)
  let mut new_origin : Location.State := Location.init_void
  let t'1 := source_backend
  let mut t'7 : Bool := false
  match t'1 with
  | .ahrs'ekf3 =>  -- C++ `ahrs.ekf3`
      let (t'2, t'3, t'4) := AP_AHRS_NavEKF3.get_origin w new_origin
      w := t'2
      new_origin := t'3
      t'7 := t'4
  | .ahrs'dcm =>  -- C++ `ahrs.dcm`
      w := { w with ahrs := s }  -- this object's state into the World: the call reaches it
      let (t'5, t'6) := AP_AHRS_DCM.get_origin s.dcm w new_origin
      new_origin := t'5
      t'7 := t'6
  | .ahrs'sim =>  -- C++ `ahrs.sim`
      new_origin := inp.get_origin_ret
      t'7 := inp.get_origin
  | _ => pure ()  -- (no other object: undefined in C++)
  if !t'7 then
    return (s, w, o)
  for t'8 in [0:3] do
    if s.backends_and_estimates[t'8]!.estimates == source_estimates then
      continue
    let t'9 := s.backends_and_estimates[t'8]!.backend
    let mut t'13 : Bool := false
    match t'9 with
    | .ahrs'ekf3 =>  -- C++ `ahrs.ekf3`
        let (t'10, t'11, t'12) := AP_AHRS_NavEKF3.set_origin w o new_origin
        w := t'10
        o := t'11
        t'13 := t'12
    | .ahrs'dcm =>  -- C++ `ahrs.dcm`
        t'13 := AP_AHRS_DCM.set_origin new_origin
    | .ahrs'sim =>  -- C++ `ahrs.sim`
        pure ()  -- C++ `AP_AHRS_Backend::set_origin`: returns a constant
        t'13 := false
    | _ => pure ()  -- (no other object: undefined in C++)
  s := { s with done_common_origin := true }
  return (s, w, o)

end AP_AHRS

namespace AP_AHRS_Backend

/-- C++ `static float AP_AHRS_Backend::get_EAS2TAS()`, `AP_AHRS/AP_AHRS_Backend.cpp:277-279`. -/
def get_EAS2TAS (w : World) : Binary32 := Id.run do
  return AP_Baro.get_EAS2TAS w.barometer

/-- C++ `static float AP_AHRS_Backend::get_TAS2EAS()`, `AP_AHRS/AP_AHRS_Backend.h:339`. -/
def get_TAS2EAS (w : World) : Binary32 := Id.run do
  return (Binary32.ofBits 0x3f800000 /- 1.0 -/) / get_EAS2TAS w

end AP_AHRS_Backend

namespace AP_AHRS_DCM

/-- C++ `bool AP_AHRS_Backend::get_unconstrained_airspeed_EAS(bool have_velocity_source, float & airspeed_ret) const`, `AP_AHRS/AP_AHRS_DCM.cpp:1301-1323` (a member of `AP_AHRS_Backend`, translated for `AP_AHRS_DCM`). -/
def get_unconstrained_airspeed_EAS (s : State) (w : World) (have_velocity_source : Bool) (airspeed_ret : Binary32) : Binary32 × Bool := Id.run do
  let mut airspeed_ret := airspeed_ret
  if AP_AHRS.get_wind_estimation_enabled w.ahrs && have_velocity_source then
    airspeed_ret := s._last_airspeed_TAS * AP_AHRS_Backend.get_TAS2EAS w
    return (airspeed_ret, true)
  airspeed_ret := s._last_airspeed_TAS * AP_AHRS_Backend.get_TAS2EAS w
  return (airspeed_ret, false)

/-- C++ `void AP_AHRS_Backend::constrain_airspeed_EAS_by_ground_speed(float & airspeed_ret) const`, `AP_AHRS/AP_AHRS_DCM.cpp:1284-1299` (a member of `AP_AHRS_Backend`, translated for `AP_AHRS_DCM`). -/
def constrain_airspeed_EAS_by_ground_speed (w : World) (airspeed_ret : Binary32) : Binary32 := Id.run do
  let mut airspeed_ret := airspeed_ret
  let _wind_max : Binary32 := UInt8.toBinary32 (AP_AHRS.get_max_wind w.ahrs)
  if decide (_wind_max > (Binary32.ofBits 0x00000000 /- 0 -/)) && decide (AP_GPS_FixType.toInt (AP_GPS.status_void w.gps) ≥ AP_GPS_FixType.toInt AP_GPS_FixType.FIX_2D) then
    let gnd_speed : Binary32 := AP_GPS.ground_speed_void w.gps
    let mut true_airspeed : Binary32 := airspeed_ret * AP_AHRS_Backend.get_EAS2TAS w
    true_airspeed := Estimator_lib.constrain_value_line_float true_airspeed (gnd_speed - _wind_max) (gnd_speed + _wind_max) (Int32.toUInt32 (1295 : Int32))
    airspeed_ret := true_airspeed / AP_AHRS_Backend.get_EAS2TAS w
  return airspeed_ret

/-- C++ `bool AP_AHRS_Backend::airspeed_EAS(bool have_velocity_source, float & airspeed_ret) const`, `AP_AHRS/AP_AHRS_DCM.cpp:1272-1281` (a member of `AP_AHRS_Backend`, translated for `AP_AHRS_DCM`). -/
def airspeed_EAS (s : State) (w : World) (have_velocity_source : Bool) (airspeed_ret : Binary32) : Binary32 × Bool := Id.run do
  let mut airspeed_ret := airspeed_ret
  let (t'1, t'2) := get_unconstrained_airspeed_EAS s w have_velocity_source airspeed_ret
  airspeed_ret := t'1
  if !t'2 then
    return (airspeed_ret, false)
  airspeed_ret := constrain_airspeed_EAS_by_ground_speed w airspeed_ret
  return (airspeed_ret, true)

end AP_AHRS_DCM

namespace AP_AHRS

/-- C++ `void AP_AHRS::fallback_synthetic_airspeed_EAS(AP_AHRS_Backend::Estimates & results)`, `AP_AHRS/AP_AHRS.cpp:760-776`. -/
def fallback_synthetic_airspeed_EAS (s : State) (w : World) (results : AP_AHRS_Backend.Estimates.State) : World × AP_AHRS_Backend.Estimates.State := Id.run do
  let mut w := w
  let mut results := results
  if UInt32.toInt32 (UInt8.toUInt32 (AP_AHRS_Backend.AirspeedEstimateType.toInt results.airspeed_estimate_type)) != UInt32.toInt32 (UInt8.toUInt32 (AP_AHRS_Backend.AirspeedEstimateType.toInt AP_AHRS_Backend.AirspeedEstimateType.DCM_FALLBACK)) then
    return (w, results)
  w := { w with ahrs := s }  -- this object's state into the World: the call reaches it
  let (t'1, t'2) := AP_AHRS_DCM.airspeed_EAS s.dcm w s.dcm_estimates.have_velocity_source results.airspeed_EAS
  results := { results with airspeed_EAS := t'1 }
  results := { results with airspeed_EAS_ok := t'2 }
  results := { results with airspeed_estimate_type := AP_AHRS_Backend.AirspeedEstimateType.DCM_SYNTHETIC }
  results := { results with airspeed_TAS := results.airspeed_EAS * AP_AHRS_Backend.get_EAS2TAS w }
  results := { results with airspeed_TAS_ok := results.airspeed_EAS_ok }
  return (w, results)

/-- C++ `void AP_AHRS::update_notify_from_filter_status(const nav_filter_status & status)`, `AP_AHRS/AP_AHRS.cpp:669-674`. -/
def update_notify_from_filter_status (o : Outputs) (status : UInt32) : Outputs := Id.run do
  let mut o := o
  o := o.push (Output.AP_Notify_flags_gps_fusion (status >>> 13 &&& 1 != 0))
  o := o.push (Output.AP_Notify_flags_gps_glitching (status >>> 14 &&& 1 != 0))
  o := o.push (Output.AP_Notify_flags_have_pos_abs (status >>> 4 &&& 1 != 0))
  return o

end AP_AHRS

namespace AP_AHRS

/-- C++ `bool AP_AHRS::_airspeed_TAS(Vector3f & vec) const`, `AP_AHRS/AP_AHRS.cpp:780-808`; for a call that binds `vec` to member `state.airspeed_TAS_vec`, which the function also reaches through `this`, so each such parameter is that member here. -/
def _airspeed_TAS'state_airspeed_TAS_vec (s : State) (w : World) : State × Bool := Id.run do
  let mut s := s
  match active_EKF_type s with
  | .DCM =>
    pure ()
  | .THREE =>
    let (t'1, t'2) := NavEKF3.getAirSpdVec w.EKF3 w s.state.airspeed_TAS_vec
    s := { s with state.airspeed_TAS_vec := t'1 }
    return (s, t'2)
  | .SIM =>
    pure ()
  return (s, false)

end AP_AHRS

namespace AP_AHRS

/-- C++ `bool AP_AHRS::_get_location(Location & loc) const`, `AP_AHRS/AP_AHRS.cpp:687-701`. -/
def _get_location (s : State) (loc : Location.State) : Location.State × Bool := Id.run do
  let mut loc := loc
  let t'1 := s.active_estimates
  let mut t'8 : Bool := false
  match t'1 with
  | .ahrs'dcm_estimates =>  -- C++ `ahrs.dcm_estimates`
      let (t'2, t'3) := AP_AHRS_Backend.Estimates.get_location s.dcm_estimates loc
      loc := t'2
      t'8 := t'3
  | .ahrs'ekf3_estimates =>  -- C++ `ahrs.ekf3_estimates`
      let (t'4, t'5) := AP_AHRS_Backend.Estimates.get_location s.ekf3_estimates loc
      loc := t'4
      t'8 := t'5
  | .ahrs'sim_estimates =>  -- C++ `ahrs.sim_estimates`
      let (t'6, t'7) := AP_AHRS_Backend.Estimates.get_location s.sim_estimates loc
      loc := t'6
      t'8 := t'7
  | _ => pure ()  -- (no other object: undefined in C++)
  if t'8 then
    return (loc, true)
  if !(always_use_EKF s) then
    let (t'9, t'10) := AP_AHRS_Backend.Estimates.get_location s.dcm_estimates loc
    loc := t'9
    return (loc, t'10)
  return (loc, false)

end AP_AHRS

namespace AP_AHRS

/-- C++ `bool AP_AHRS::_getCorrectedDeltaVelocityNED(Vector3f & ret, float & dt) const`, `AP_AHRS/AP_AHRS.cpp:1514-1523`; for a call that binds `ret` to member `state.corrected_dv`, `dt` to member `state.corrected_dv_dt`, which the function also reaches through `this`, so each such parameter is that member here. -/
def _getCorrectedDeltaVelocityNED'state_corrected_dv'state_corrected_dv_dt (s : State) (w : World) : State × Bool := Id.run do
  let mut s := s
  let (t'1, t'2, t'3) := AP_InertialSensor.get_delta_velocity_uint8_t_Vector3f_float w.ins ((match s.active_estimates with | .ahrs'dcm_estimates => s.dcm_estimates | .ahrs'ekf3_estimates => s.ekf3_estimates | _ => s.sim_estimates) : AP_AHRS_Backend.Estimates.State).primary_accel s.state.corrected_dv s.state.corrected_dv_dt
  s := { s with state.corrected_dv := t'1 }
  s := { s with state.corrected_dv_dt := t'2 }
  if !t'3 then
    return (s, false)
  let (t'4, _) := Vector3f.op_sub_assign s.state.corrected_dv (Vector3f.op_mul_float ((match s.active_estimates with | .ahrs'dcm_estimates => s.dcm_estimates | .ahrs'ekf3_estimates => s.ekf3_estimates | _ => s.sim_estimates) : AP_AHRS_Backend.Estimates.State).accel_bias s.state.corrected_dv_dt)
  s := { s with state.corrected_dv := t'4 }
  s := { s with state.corrected_dv := Matrix3f.op_mul_Vector3f (Matrix3f.op_mul_Matrix3f s.state.dcm_matrix (get_rotation_autopilot_body_to_vehicle_body s)) s.state.corrected_dv }
  s := { s with state.corrected_dv.z := s.state.corrected_dv.z + (Binary32.ofBits 0x411ce80a /- 9.80665016 -/) * s.state.corrected_dv_dt }
  return (s, true)

/-- C++ `bool AP_AHRS::_get_origin(EKFType type, Location & ret) const`, `AP_AHRS/AP_AHRS.cpp:1714-1723`. -/
def _get_origin_EKFType_Location (s : State) (w : World) (inp : Inputs) (type : AP_AHRS.EKFType) (ret : Location.State) : World × Location.State × Bool := Id.run do
  let mut w := w
  let mut ret := ret
  let backend : WPtr := backend_for_type type
  if backend == WPtr.null then
    return (w, ret, false)
  let t'1 := backend
  let mut t'7 : Bool := false
  match t'1 with
  | .ahrs'ekf3 =>  -- C++ `ahrs.ekf3`
      let (t'2, t'3, t'4) := AP_AHRS_NavEKF3.get_origin w ret
      w := t'2
      ret := t'3
      t'7 := t'4
  | .ahrs'dcm =>  -- C++ `ahrs.dcm`
      w := { w with ahrs := s }  -- this object's state into the World: the call reaches it
      let (t'5, t'6) := AP_AHRS_DCM.get_origin s.dcm w ret
      ret := t'5
      t'7 := t'6
  | .ahrs'sim =>  -- C++ `ahrs.sim`
      ret := inp.get_origin_ret
      t'7 := inp.get_origin
  | _ => pure ()  -- (no other object: undefined in C++)
  return (w, ret, t'7)

/-- C++ `bool AP_AHRS::_get_origin(Location & ret) const`, `AP_AHRS/AP_AHRS.cpp:1733-1742`; for a call that binds `ret` to member `state.origin`, which the function also reaches through `this`, so each such parameter is that member here. -/
def _get_origin_Location'state_origin (s : State) (w : World) (inp : Inputs) : State × World × Bool := Id.run do
  let mut s := s
  let mut w := w
  let (t'1, t'2, t'3) := _get_origin_EKFType_Location s w inp (configured_ekf_type s) s.state.origin
  w := t'1
  s := { s with state.origin := t'2 }
  if t'3 then
    return (s, w, true)
  let mut t'7 := inp.get_soft_armed
  if t'7 then
    let (t'4, t'5, t'6) := _get_origin_EKFType_Location s w inp (active_EKF_type s) s.state.origin
    w := t'4
    s := { s with state.origin := t'5 }
    t'7 := t'6
  if t'7 then
    return (s, w, true)
  return (s, w, false)

end AP_AHRS

namespace AP_AHRS

/-- C++ `void AP_AHRS::record_origin()`, `AP_AHRS/AP_AHRS.cpp:911-920`. -/
def record_origin (s : State) (o : Outputs) : State × Outputs := Id.run do
  let mut s := s
  let mut o := o
  if !(option_set s AP_AHRS.Options.RECORD_ORIGIN) then
    return (s, o)
  let (t'1, t'2) := AP_ParamT_float_4.set_and_save_ifchanged s._origin_lat o "ahrs._origin_lat" (Int32.toBinary32 s.state.origin.lat * (Binary32.ofBits 0x33d6bf95 /- 1.0e-7 -/))
  s := { s with _origin_lat := t'1 }
  o := t'2
  let (t'3, t'4) := AP_ParamT_float_4.set_and_save_ifchanged s._origin_lon o "ahrs._origin_lon" (Int32.toBinary32 s.state.origin.lng * (Binary32.ofBits 0x33d6bf95 /- 1.0e-7 -/))
  s := { s with _origin_lon := t'3 }
  o := t'4
  let (t'5, t'6) := AP_ParamT_float_4.set_and_save_ifchanged s._origin_alt o "ahrs._origin_alt" (Int32.toBinary32 s.state.origin.alt * (Binary32.ofBits 0x3c23d70a /- 1.0e-2 -/))
  s := { s with _origin_alt := t'5 }
  o := t'6
  return (s, o)

/-- C++ `bool AP_AHRS::set_origin(const Location & loc)`, `AP_AHRS/AP_AHRS.cpp:893-907`. -/
def set_origin (s : State) (w : World) (o : Outputs) (loc : Location.State) : World × Outputs × Bool := Id.run do
  let mut w := w
  let mut o := o
  pure ()  -- C++ `_getsem34`: a semaphore, which does nothing here (one thread, --semaphores)
  for t'1 in [0:3] do
    let backend := s.backends_and_estimates[t'1]!.backend
    if backend == s.active_backend then
      continue
    let t'2 := backend
    let mut t'6 : Bool := false
    match t'2 with
    | .ahrs'ekf3 =>  -- C++ `ahrs.ekf3`
        let (t'3, t'4, t'5) := AP_AHRS_NavEKF3.set_origin w o loc
        w := t'3
        o := t'4
        t'6 := t'5
    | .ahrs'dcm =>  -- C++ `ahrs.dcm`
        t'6 := AP_AHRS_DCM.set_origin loc
    | .ahrs'sim =>  -- C++ `ahrs.sim`
        pure ()  -- C++ `AP_AHRS_Backend::set_origin`: returns a constant
        t'6 := false
    | _ => pure ()  -- (no other object: undefined in C++)
  let t'7 := s.active_backend
  let mut t'11 : Bool := false
  match t'7 with
  | .ahrs'ekf3 =>  -- C++ `ahrs.ekf3`
      let (t'8, t'9, t'10) := AP_AHRS_NavEKF3.set_origin w o loc
      w := t'8
      o := t'9
      t'11 := t'10
  | .ahrs'dcm =>  -- C++ `ahrs.dcm`
      t'11 := AP_AHRS_DCM.set_origin loc
  | .ahrs'sim =>  -- C++ `ahrs.sim`
      pure ()  -- C++ `AP_AHRS_Backend::set_origin`: returns a constant
      t'11 := false
  | _ => pure ()  -- (no other object: undefined in C++)
  return (w, o, t'11)

/-- C++ `void AP_AHRS::use_recorded_origin_maybe()`, `AP_AHRS/AP_AHRS.cpp:924-955`. -/
def use_recorded_origin_maybe (s : State) (w : World) (o : Outputs) : World × Outputs := Id.run do
  let mut w := w
  let mut o := o
  if s.state.origin_ok || !(option_set s AP_AHRS.Options.USE_RECORDED_ORIGIN_FOR_NONGPS) then
    return (w, o)
  if Estimator_lib.is_zero_float (AP_ParamT_float_4.get_void s._origin_lat) && Estimator_lib.is_zero_float (AP_ParamT_float_4.get_void s._origin_lon) && Estimator_lib.is_zero_float (AP_ParamT_float_4.get_void s._origin_alt) then
    return (w, o)
  if ((match s.active_estimates with | .ahrs'dcm_estimates => s.dcm_estimates | .ahrs'ekf3_estimates => s.ekf3_estimates | _ => s.sim_estimates) : AP_AHRS_Backend.Estimates.State).configured_to_use_gps_for_pos_XY then
    return (w, o)
  let loc : Location.State := Location.init_int32_t3_AltFrame (Binary32.toInt32 (AP_ParamT_float_4.get_void s._origin_lat * (Binary32.ofBits 0x4b189680 /- 1e7 -/))) (Binary32.toInt32 (AP_ParamT_float_4.get_void s._origin_lon * (Binary32.ofBits 0x4b189680 /- 1e7 -/))) (Binary32.toInt32 (AP_ParamT_float_4.get_void s._origin_alt * (Binary32.ofBits 0x42c80000 /- 100 -/))) Location.AltFrame.ABSOLUTE
  let (t'1, t'2, t'3) := set_origin s w o loc
  w := t'1
  o := t'2
  if t'3 then
    o := o.push (Output.send_text (6 : UInt32) "AHRS: using recorded origin:%.7f,%.7f,%.1f" #[Sum.inl (Binary64.toBits (Binary32.toBinary64 (AP_ParamT_float_4.get_void s._origin_lat))), Sum.inl (Binary64.toBits (Binary32.toBinary64 (AP_ParamT_float_4.get_void s._origin_lon))), Sum.inl (Binary64.toBits (Binary32.toBinary64 (AP_ParamT_float_4.get_void s._origin_alt)))])
  return (w, o)

end AP_AHRS

namespace AP_AHRS

/-- C++ `void AP_AHRS::update_state()`, `AP_AHRS/AP_AHRS.cpp:411-491`. -/
def update_state (s : State) (w : World) (o : Outputs) (inp : Inputs) : State × World × Outputs := Id.run do
  let mut s := s
  let mut w := w
  let mut o := o
  let primary_gyro : UInt8 := ((match s.active_estimates with | .ahrs'dcm_estimates => s.dcm_estimates | .ahrs'ekf3_estimates => s.ekf3_estimates | _ => s.sim_estimates) : AP_AHRS_Backend.Estimates.State).primary_gyro
  if UInt32.toInt32 (UInt8.toUInt32 primary_gyro) != UInt32.toInt32 (UInt8.toUInt32 s.state.primary_gyro) then
    let t'1 := w.ins  -- the object out of the World for the call (--swap-out)
    w := { w with ins := default }
    w := { w with ins := AP_InertialSensor.set_primary t'1 primary_gyro }
  s := { s with state.primary_gyro := primary_gyro }
  s := { s with state.primary_accel := ((match s.active_estimates with | .ahrs'dcm_estimates => s.dcm_estimates | .ahrs'ekf3_estimates => s.ekf3_estimates | _ => s.sim_estimates) : AP_AHRS_Backend.Estimates.State).primary_accel }
  s := { s with state.EAS2TAS := AP_AHRS_Backend.get_EAS2TAS w }
  s := { s with state.airspeed_estimate_type := ((match s.active_estimates with | .ahrs'dcm_estimates => s.dcm_estimates | .ahrs'ekf3_estimates => s.ekf3_estimates | _ => s.sim_estimates) : AP_AHRS_Backend.Estimates.State).airspeed_estimate_type }
  if UInt32.toInt32 (UInt8.toUInt32 (AP_AHRS_Backend.AirspeedEstimateType.toInt s.state.airspeed_estimate_type)) == UInt32.toInt32 (UInt8.toUInt32 (AP_AHRS_Backend.AirspeedEstimateType.toInt AP_AHRS_Backend.AirspeedEstimateType.NO_NEW_ESTIMATE)) then
    s := { s with state.airspeed_EAS_ok := false }
    s := { s with state.airspeed_TAS_ok := false }
  else
    s := { s with state.airspeed_EAS := ((match s.active_estimates with | .ahrs'dcm_estimates => s.dcm_estimates | .ahrs'ekf3_estimates => s.ekf3_estimates | _ => s.sim_estimates) : AP_AHRS_Backend.Estimates.State).airspeed_EAS }
    s := { s with state.airspeed_EAS_ok := ((match s.active_estimates with | .ahrs'dcm_estimates => s.dcm_estimates | .ahrs'ekf3_estimates => s.ekf3_estimates | _ => s.sim_estimates) : AP_AHRS_Backend.Estimates.State).airspeed_EAS_ok }
    s := { s with state.airspeed_TAS := ((match s.active_estimates with | .ahrs'dcm_estimates => s.dcm_estimates | .ahrs'ekf3_estimates => s.ekf3_estimates | _ => s.sim_estimates) : AP_AHRS_Backend.Estimates.State).airspeed_TAS }
    s := { s with state.airspeed_TAS_ok := ((match s.active_estimates with | .ahrs'dcm_estimates => s.dcm_estimates | .ahrs'ekf3_estimates => s.ekf3_estimates | _ => s.sim_estimates) : AP_AHRS_Backend.Estimates.State).airspeed_TAS_ok }
  let (t'2, t'3) := _airspeed_TAS'state_airspeed_TAS_vec s w
  s := t'2
  s := { s with state.airspeed_TAS_vec_ok := t'3 }
  s := { s with roll := ((match s.active_estimates with | .ahrs'dcm_estimates => s.dcm_estimates | .ahrs'ekf3_estimates => s.ekf3_estimates | _ => s.sim_estimates) : AP_AHRS_Backend.Estimates.State).roll_rad }
  s := { s with pitch := ((match s.active_estimates with | .ahrs'dcm_estimates => s.dcm_estimates | .ahrs'ekf3_estimates => s.ekf3_estimates | _ => s.sim_estimates) : AP_AHRS_Backend.Estimates.State).pitch_rad }
  s := { s with yaw := ((match s.active_estimates with | .ahrs'dcm_estimates => s.dcm_estimates | .ahrs'ekf3_estimates => s.ekf3_estimates | _ => s.sim_estimates) : AP_AHRS_Backend.Estimates.State).yaw_rad }
  s := { s with state.dcm_matrix := ((match s.active_estimates with | .ahrs'dcm_estimates => s.dcm_estimates | .ahrs'ekf3_estimates => s.ekf3_estimates | _ => s.sim_estimates) : AP_AHRS_Backend.Estimates.State).dcm_matrix }
  s := { s with state.gyro_estimate := ((match s.active_estimates with | .ahrs'dcm_estimates => s.dcm_estimates | .ahrs'ekf3_estimates => s.ekf3_estimates | _ => s.sim_estimates) : AP_AHRS_Backend.Estimates.State).gyro_estimate }
  s := { s with state.gyro_drift := ((match s.active_estimates with | .ahrs'dcm_estimates => s.dcm_estimates | .ahrs'ekf3_estimates => s.ekf3_estimates | _ => s.sim_estimates) : AP_AHRS_Backend.Estimates.State).gyro_drift }
  s := { s with state.accel_ef := ((match s.active_estimates with | .ahrs'dcm_estimates => s.dcm_estimates | .ahrs'ekf3_estimates => s.ekf3_estimates | _ => s.sim_estimates) : AP_AHRS_Backend.Estimates.State).accel_ef }
  s := { s with state.accel_bias := ((match s.active_estimates with | .ahrs'dcm_estimates => s.dcm_estimates | .ahrs'ekf3_estimates => s.ekf3_estimates | _ => s.sim_estimates) : AP_AHRS_Backend.Estimates.State).accel_bias }
  s := update_cd_values s
  s := update_trig s
  let t'4 := s.active_estimates
  let mut t'11 : Bool := false
  match t'4 with
  | .ahrs'dcm_estimates =>  -- C++ `ahrs.dcm_estimates`
      let (t'5, t'6) := AP_AHRS_Backend.Estimates.get_quaternion s.dcm_estimates s.state.quat
      s := { s with state.quat := t'5 }
      t'11 := t'6
  | .ahrs'ekf3_estimates =>  -- C++ `ahrs.ekf3_estimates`
      let (t'7, t'8) := AP_AHRS_Backend.Estimates.get_quaternion s.ekf3_estimates s.state.quat
      s := { s with state.quat := t'7 }
      t'11 := t'8
  | .ahrs'sim_estimates =>  -- C++ `ahrs.sim_estimates`
      let (t'9, t'10) := AP_AHRS_Backend.Estimates.get_quaternion s.sim_estimates s.state.quat
      s := { s with state.quat := t'9 }
      t'11 := t'10
  | _ => pure ()  -- (no other object: undefined in C++)
  s := { s with state.quat_ok := t'11 }
  let (t'12, t'13) := _get_location s s.state.location
  s := { s with state.location := t'12 }
  s := { s with state.location_ok := t'13 }
  if s.state.location_ok && !(Location.initialised s.state.location) then
    pure ()  -- C++ `AP_HAL::panic(...)`: left out (--drop)
  s := { s with state.ground_speed_vec := ((match s.active_estimates with | .ahrs'dcm_estimates => s.dcm_estimates | .ahrs'ekf3_estimates => s.ekf3_estimates | _ => s.sim_estimates) : AP_AHRS_Backend.Estimates.State).velocity_NE }
  s := { s with state.ground_speed := Vector2f.length s.state.ground_speed_vec }
  let (t'14, t'15) := _getCorrectedDeltaVelocityNED'state_corrected_dv'state_corrected_dv_dt s w
  s := t'14
  s := { s with state.corrected_dv_valid := t'15 }
  let (t'16, t'17, t'18) := _get_origin_Location'state_origin s w inp
  w := t'17
  s := t'16
  let origin_ok : Bool := t'18
  if origin_ok && !s.state.origin_ok then
    s := { s with state.origin_ok := origin_ok }
    o := o.push (Output.send_message ap_message.MSG_ORIGIN)
    let (t'19, t'20) := record_origin s o
    s := t'19
    o := t'20
  if !s.state.origin_ok then
    let (t'21, t'22) := use_recorded_origin_maybe s w o
    w := t'21
    o := t'22
  let t'23 := s.active_estimates
  let mut t'30 : Bool := false
  match t'23 with
  | .ahrs'dcm_estimates =>  -- C++ `ahrs.dcm_estimates`
      let (t'24, t'25) := AP_AHRS_Backend.Estimates.get_velocity_NED s.dcm_estimates s.state.velocity_NED
      s := { s with state.velocity_NED := t'24 }
      t'30 := t'25
  | .ahrs'ekf3_estimates =>  -- C++ `ahrs.ekf3_estimates`
      let (t'26, t'27) := AP_AHRS_Backend.Estimates.get_velocity_NED s.ekf3_estimates s.state.velocity_NED
      s := { s with state.velocity_NED := t'26 }
      t'30 := t'27
  | .ahrs'sim_estimates =>  -- C++ `ahrs.sim_estimates`
      let (t'28, t'29) := AP_AHRS_Backend.Estimates.get_velocity_NED s.sim_estimates s.state.velocity_NED
      s := { s with state.velocity_NED := t'28 }
      t'30 := t'29
  | _ => pure ()  -- (no other object: undefined in C++)
  s := { s with state.velocity_NED_ok := t'30 }
  return (s, w, o)

/-- C++ `const Vector3f & AP_AHRS::get_gyro() const`, `AP_AHRS/AP_AHRS.h:92`. -/
def get_gyro (s : State) : Vector3f.State := Id.run do
  return s.state.gyro_estimate

end AP_AHRS

namespace AP_AHRS_DCM

/-- C++ `float AP_AHRS_DCM::yaw_error_compass(class Compass & compass)`, `AP_AHRS/AP_AHRS_DCM.cpp:524-551`. -/
def yaw_error_compass (s : State) (w : World) : State × Binary32 := Id.run do
  let mut s := s
  let mut rb : Vector2f.State := Matrix3f.mulXY s._dcm_matrix (Compass.get_field_void w.compass)
  if Vector2f.length rb < (Binary32.ofBits 0x34000000 /- 1.1920929E-7 -/) then
    return (s, (Binary32.ofBits 0x00000000 /- 0.0f -/))
  rb := Vector2f.normalize rb
  if Vector2f.is_inf rb then
    return (s, (Binary32.ofBits 0x00000000 /- 0.0f -/))
  if !(Estimator_lib.is_equal_float2 s._last_declination (Compass.get_declination w.compass)) then
    s := { s with _last_declination := Compass.get_declination w.compass }
    s := { s with _mag_earth.x := Musl.cosf.cosf s._last_declination }
    s := { s with _mag_earth.y := Musl.sinf.sinf s._last_declination }
  return (s, Vector2f.op_mod rb s._mag_earth)

/-- C++ `float AP_AHRS_DCM::_yaw_gain() const`, `AP_AHRS/AP_AHRS_DCM.cpp:575-584`. -/
def _yaw_gain (s : State) : Binary32 := Id.run do
  let VdotEFmag : Binary32 := Vector2f.length ({ x := s._accel_ef.x, y := s._accel_ef.y } : Vector2f.State)
  if VdotEFmag ≤ (Binary32.ofBits 0x40800000 /- 4.0f -/) then
    return (Binary32.ofBits 0x3e4ccccd /- 0.2f -/) * ((Binary32.ofBits 0x40900000 /- 4.5f -/) - VdotEFmag)
  return (Binary32.ofBits 0x3dcccccd /- 0.1f -/)

/-- C++ `static const float AP_AHRS_DCM::_ki_yaw`, `AP_AHRS/AP_AHRS_DCM.h:123`. -/
def _ki_yaw : Binary32 := (Binary32.ofBits 0x3c23d70a /- 0.01f -/)

end AP_AHRS_DCM

namespace AP_AHRS_DCM

/-- C++ `bool AP_AHRS_DCM::get_location(Location & loc) const`, `AP_AHRS/AP_AHRS_DCM.cpp:1234-1262`. -/
def get_location (s : State) (w : World) (loc : Location.State) : Location.State × Bool := Id.run do
  let mut loc := loc
  if s._last_lat == (0 : Int32) && s._last_lng == (0 : Int32) then
    return (loc, false)
  loc := { loc with lat := s._last_lat }
  loc := { loc with lng := s._last_lng }
  let mut alt_cm : Int32 := (0 : Int32)  -- uninitialized in C++; assigned before every read
  if AP_Enum_GPSUse.op_to_GPSUse w.ahrs._gps_use == GPSUse.EnableWithHeight && decide (AP_GPS_FixType.toInt (AP_GPS.status_void w.gps) ≥ AP_GPS_FixType.toInt AP_GPS_FixType.FIX_3D) then
    alt_cm := (AP_GPS.location_void w.gps).alt
  else
    alt_cm := Binary32.toInt32 (AP_Baro.get_altitude_void w.barometer * (Binary32.ofBits 0x42c80000 /- 100 -/) + Int32.toBinary32 w.ahrs._home.alt)
  loc := Location.set_alt_cm loc alt_cm Location.AltFrame.ABSOLUTE
  loc := Location.offset_double2 loc (Binary32.toBinary64 s._position_offset_north) (Binary32.toBinary64 s._position_offset_east)
  if s._have_position then
    let now : UInt32 := Estimator_lib.millis w
    let mut dt : Binary32 := (Binary32.ofBits 0x00000000 /- 0 -/)
    let (t'1, _) := AP_GPS.get_lag_float w.gps w dt
    dt := t'1
    dt := dt + Estimator_lib.constrain_value_line_float (UInt32.toBinary32 (now - s._last_pos_ms) * (Binary32.ofBits 0x3a83126f /- (float)1152921504606847/1152921504606846976 -/)) (Binary32.ofBits 0x00000000 /- (float)0 -/) (Binary32.ofBits 0x3f000000 /- (float)1/2 -/) (Int32.toUInt32 (1257 : Int32))
    let dpos : Vector2f.State := Vector2f.op_mul_float ({ x := s._last_velocity.x, y := s._last_velocity.y } : Vector2f.State) dt
    loc := Location.offset_double2 loc (Binary32.toBinary64 dpos.x) (Binary32.toBinary64 dpos.y)
  return (loc, s._have_position)

/-- C++ `bool AP_AHRS_DCM::synthetic_airspeed_EAS(const Estimates & results, float & airspeed_ret, AirspeedEstimateType & type)`, `AP_AHRS/AP_AHRS_DCM.cpp:1496-1502`. -/
def synthetic_airspeed_EAS (s : State) (w : World) (results : AP_AHRS_Backend.Estimates.State) (airspeed_ret : Binary32) (type : AP_AHRS_Backend.AirspeedEstimateType) : Binary32 × AP_AHRS_Backend.AirspeedEstimateType × Bool := Id.run do
  let mut airspeed_ret := airspeed_ret
  let mut type := type
  type := AP_AHRS_Backend.AirspeedEstimateType.DCM_SYNTHETIC
  airspeed_ret := s._last_airspeed_TAS * AP_AHRS_Backend.get_TAS2EAS w
  airspeed_ret := constrain_airspeed_EAS_by_ground_speed w airspeed_ret
  return (airspeed_ret, type, results.have_velocity_source)

/-- C++ `bool AP_AHRS_Backend::fill_airspeed_EAS_estimate(Estimates & results)`, `AP_AHRS/AP_AHRS_DCM.cpp:1382-1396` (a member of `AP_AHRS_Backend`, translated for `AP_AHRS_DCM`). -/
def fill_airspeed_EAS_estimate (s : State) (w : World) (results : AP_AHRS_Backend.Estimates.State) : AP_AHRS_Backend.Estimates.State × Bool := Id.run do
  let mut results := results
  if !(AP_AHRS.get_wind_estimation_enabled w.ahrs) then
    results := { results with airspeed_estimate_type := AP_AHRS_Backend.AirspeedEstimateType.NO_NEW_ESTIMATE }
    return (results, false)
  let (t'1, t'2, t'3) := synthetic_airspeed_EAS s w results results.airspeed_EAS results.airspeed_estimate_type
  results := { results with airspeed_EAS := t'1 }
  results := { results with airspeed_estimate_type := t'2 }
  return (results, t'3)

/-- C++ `void AP_AHRS_Backend::fill_airspeed_estimate(Estimates & results)`, `AP_AHRS/AP_AHRS_DCM.cpp:1371-1378` (a member of `AP_AHRS_Backend`, translated for `AP_AHRS_DCM`). -/
def fill_airspeed_estimate (s : State) (w : World) (results : AP_AHRS_Backend.Estimates.State) : AP_AHRS_Backend.Estimates.State := Id.run do
  let mut results := results
  let (t'1, t'2) := fill_airspeed_EAS_estimate s w results
  results := t'1
  results := { results with airspeed_EAS_ok := t'2 }
  results := { results with airspeed_TAS := results.airspeed_EAS * AP_AHRS_Backend.get_EAS2TAS w }
  results := { results with airspeed_TAS_ok := results.airspeed_EAS_ok }
  return results

end AP_AHRS_DCM

namespace AP_AHRS_NavEKF3

/-- C++ `bool AP_AHRS_NavEKF3::synthetic_airspeed_EAS(const Estimates & results, float & airspeed_ret, AirspeedEstimateType & type)`, `AP_AHRS/AP_AHRS_NavEKF3.cpp:250-273`. -/
def synthetic_airspeed_EAS (w : World) (results : AP_AHRS_Backend.Estimates.State) (airspeed_ret : Binary32) (type : AP_AHRS_Backend.AirspeedEstimateType) : Binary32 × AP_AHRS_Backend.AirspeedEstimateType × Bool := Id.run do
  let mut airspeed_ret := airspeed_ret
  let mut type := type
  if !results.wind_valid || !results.velocity_NED_valid then
    type := AP_AHRS_Backend.AirspeedEstimateType.DCM_FALLBACK
    return (airspeed_ret, type, false)
  type := AP_AHRS_Backend.AirspeedEstimateType.EKF3_SYNTHETIC
  let mut true_airspeed : Binary32 := Vector3f.length (Vector3f.op_sub_Vector3f results.velocity_NED results.wind)
  let gnd_speed : Binary32 := Vector3f.length results.velocity_NED
  let wind_max : Binary32 := UInt8.toBinary32 (AP_AHRS.get_max_wind w.ahrs)
  if wind_max > (Binary32.ofBits 0x00000000 /- 0 -/) then
    let tas_lim_lower : Binary32 := Estimator_lib.MAX_float2 (Binary32.ofBits 0x00000000 /- 0.0f -/) (gnd_speed - wind_max)
    let tas_lim_upper : Binary32 := Estimator_lib.MAX_float2 tas_lim_lower (gnd_speed + wind_max)
    true_airspeed := Estimator_lib.constrain_value_line_float true_airspeed tas_lim_lower tas_lim_upper (Int32.toUInt32 (265 : Int32))
  else
    true_airspeed := Estimator_lib.MAX_float2 (Binary32.ofBits 0x00000000 /- 0.0f -/) true_airspeed
  airspeed_ret := true_airspeed / AP_AHRS_Backend.get_EAS2TAS w
  return (airspeed_ret, type, true)

/-- C++ `bool AP_AHRS_Backend::fill_airspeed_EAS_estimate(Estimates & results)`, `AP_AHRS/AP_AHRS_DCM.cpp:1382-1396` (a member of `AP_AHRS_Backend`, translated for `AP_AHRS_NavEKF3`). -/
def fill_airspeed_EAS_estimate (w : World) (results : AP_AHRS_Backend.Estimates.State) : AP_AHRS_Backend.Estimates.State × Bool := Id.run do
  let mut results := results
  if !(AP_AHRS.get_wind_estimation_enabled w.ahrs) then
    results := { results with airspeed_estimate_type := AP_AHRS_Backend.AirspeedEstimateType.NO_NEW_ESTIMATE }
    return (results, false)
  let (t'1, t'2, t'3) := synthetic_airspeed_EAS w results results.airspeed_EAS results.airspeed_estimate_type
  results := { results with airspeed_EAS := t'1 }
  results := { results with airspeed_estimate_type := t'2 }
  return (results, t'3)

/-- C++ `void AP_AHRS_Backend::fill_airspeed_estimate(Estimates & results)`, `AP_AHRS/AP_AHRS_DCM.cpp:1371-1378` (a member of `AP_AHRS_Backend`, translated for `AP_AHRS_NavEKF3`). -/
def fill_airspeed_estimate (w : World) (results : AP_AHRS_Backend.Estimates.State) : AP_AHRS_Backend.Estimates.State := Id.run do
  let mut results := results
  let (t'1, t'2) := fill_airspeed_EAS_estimate w results
  results := t'1
  results := { results with airspeed_EAS_ok := t'2 }
  results := { results with airspeed_TAS := results.airspeed_EAS * AP_AHRS_Backend.get_EAS2TAS w }
  results := { results with airspeed_TAS_ok := results.airspeed_EAS_ok }
  return results

end AP_AHRS_NavEKF3

namespace AP_AHRS_View

/-- C++ `void AP_AHRS_View::update()`, `AP_AHRS/AP_AHRS_View.cpp:61-83`. -/
def update (s : State) (w : World) : State := Id.run do
  let mut s := s
  s := { s with rot_body_to_ned := AP_AHRS.get_rotation_body_to_ned w.ahrs }
  s := { s with gyro := AP_AHRS.get_gyro w.ahrs }
  if !(Estimator_lib.is_zero_float (s.y_angle + s._pitch_trim_deg)) then
    s := { s with rot_body_to_ned := Matrix3f.op_mul_Matrix3f s.rot_body_to_ned s.rot_view_T }
    s := { s with gyro := Matrix3f.op_mul_Vector3f s.rot_view s.gyro }
  let (t'1, t'2, t'3) := Matrix3f.to_euler s.rot_body_to_ned true s.roll true s.pitch true s.yaw
  s := { s with roll := t'1 }
  s := { s with pitch := t'2 }
  s := { s with yaw := t'3 }
  s := { s with roll_sensor := Binary32.toInt32 (Estimator_lib.degrees s.roll * (Binary32.ofBits 0x42c80000 /- 100 -/)) }
  s := { s with pitch_sensor := Binary32.toInt32 (Estimator_lib.degrees s.pitch * (Binary32.ofBits 0x42c80000 /- 100 -/)) }
  s := { s with yaw_sensor := Binary32.toInt32 (Estimator_lib.degrees s.yaw * (Binary32.ofBits 0x42c80000 /- 100 -/)) }
  if s.yaw_sensor < (0 : Int32) then
    s := { s with yaw_sensor := s.yaw_sensor + (36000 : Int32) }
  let (t'4, t'5, t'6, t'7, t'8, t'9) := AP_AHRS.calc_trig s.rot_body_to_ned s.trig.cos_roll s.trig.cos_pitch s.trig.cos_yaw s.trig.sin_roll s.trig.sin_pitch s.trig.sin_yaw
  s := { s with trig.cos_roll := t'4 }
  s := { s with trig.cos_pitch := t'5 }
  s := { s with trig.cos_yaw := t'6 }
  s := { s with trig.sin_roll := t'7 }
  s := { s with trig.sin_pitch := t'8 }
  s := { s with trig.sin_yaw := t'9 }
  return s

end AP_AHRS_View

namespace AP_AHRS_View

/-- C++ `AP_AHRS_View::AP_AHRS_View(AP_AHRS & ahrs, enum Rotation rotation, float pitch_trim_deg)`, `AP_AHRS/AP_AHRS_View.cpp:24-50`. -/
def init (w : World) (_rotation : Rotation) (pitch_trim_deg : Binary32 := (Binary32.ofBits 0x00000000 /- 0 -/)) : State := Id.run do
  let mut s : State := {}
  s := { s with rotation := _rotation }
  s := { s with rot_view := Matrix3f.init_void }
  s := { s with rot_view_T := Matrix3f.init_void }
  s := { s with rot_body_to_ned := Matrix3f.init_void }
  s := { s with gyro := Vector3f.init_void }
  match s.rotation with
  | .ROTATION_NONE =>
    s := { s with y_angle := (Binary32.ofBits 0x00000000 /- 0 -/) }
  | .ROTATION_PITCH_90 =>
    s := { s with y_angle := (Binary32.ofBits 0x42b40000 /- 90 -/) }
  | .ROTATION_PITCH_270 =>
    s := { s with y_angle := (Binary32.ofBits 0x43870000 /- 270 -/) }
  | _ =>
    pure ()  -- C++ `AP_HAL::panic(...)`: left out (--drop)
  s := { s with _pitch_trim_deg := pitch_trim_deg }
  s := { s with rot_view := Matrix3f.from_euler s.rot_view (Binary32.ofBits 0x00000000 /- 0 -/) (Estimator_lib.radians_float (Estimator_lib.wrap_360_float (s.y_angle + pitch_trim_deg))) (Binary32.ofBits 0x00000000 /- 0 -/) }
  s := { s with rot_view_T := s.rot_view }
  s := { s with rot_view_T := Matrix3f.transpose s.rot_view_T }
  s := update s w
  return s

end AP_AHRS_View

namespace AP_AHRS

/-- C++ `AP_AHRS_View * AP_AHRS::create_view(enum Rotation rotation, float pitch_trim_deg)`, `AP_AHRS/AP_AHRS_Backend.cpp:165-173`. -/
def create_view (s : State) (w : World) (rotation : Rotation) (pitch_trim_deg : Binary32 := (Binary32.ofBits 0x00000000 /- 0 -/)) : State × World × WPtr := Id.run do
  let mut s := s
  let mut w := w
  if s._view != WPtr.null then
    return (s, w, WPtr.null)
  w := { w with ahrs := s }  -- this object's state into the World: the call reaches it
  let t'1 := AP_AHRS_View.init w rotation pitch_trim_deg
  let t'2 := w.heap'AP_AHRS_View.size
  w := { w with heap'AP_AHRS_View := w.heap'AP_AHRS_View.push t'1 }
  s := { s with _view := (WPtr.heap'AP_AHRS_View t'2) }
  return (s, w, s._view)

/-- C++ `void AP_AHRS::set_vehicle_class(VehicleClass vclass)`, `AP_AHRS/AP_AHRS.h:754-756`. -/
def set_vehicle_class (s : State) (vclass : AP_AHRS.VehicleClass) : State := Id.run do
  let mut s := s
  s := { s with _vehicle_class := vclass }
  return s

/-- C++ `bool AP_AHRS::home_is_set() const`, `AP_AHRS/AP_AHRS.h:606-608`. -/
def home_is_set (s : State) : Bool := Id.run do
  return s._home_is_set

end AP_AHRS

namespace AP_AHRS

/-- C++ `void AP_AHRS::set_terrain_hgt_stable(bool stable)`, `AP_AHRS/AP_AHRS.cpp:1809-1835`. -/
def set_terrain_hgt_stable (s : State) (w : World) (stable : Bool) : State × World := Id.run do
  let mut s := s
  let mut w := w
  match s.terrainHgtStableState with
  | .UNKNOWN =>
    pure ()
  | .True =>
    if stable then
      return (s, w)
  | .False =>
    if !stable then
      return (s, w)
  s := { s with terrainHgtStableState := AP_AHRS.TriState.ofInt (if stable then (1 : Int32) else (0 : Int32)) }
  w := NavEKF3.setTerrainHgtStable w.EKF3 w stable
  return (s, w)

/-- C++ `void AP_AHRS::set_touchdown_expected(bool b)`, `AP_AHRS/AP_AHRS_Backend.cpp:293-297`. -/
def set_touchdown_expected (s : State) (w : World) (b : Bool) : State := Id.run do
  let mut s := s
  s := { s with touchdown_expected := b }
  s := { s with touchdown_expected_start_ms := Estimator_lib.millis w }
  return s

end AP_AHRS

namespace AP_AHRS_NavEKF3

/-- C++ `void AP_AHRS_NavEKF3::request_yaw_reset()`, `AP_AHRS/AP_AHRS_NavEKF3.h:74-76`. -/
def request_yaw_reset (w : World) : World := Id.run do
  let mut w := w
  w := NavEKF3.requestYawReset w.EKF3 w
  return w

end AP_AHRS_NavEKF3

namespace AP_AHRS

/-- C++ `void AP_AHRS::request_yaw_reset()`, `AP_AHRS/AP_AHRS.h:472-474`. -/
def request_yaw_reset (s : State) (w : World) : World := Id.run do
  let mut w := w
  let t'1 := s.active_backend
  match t'1 with
  | .ahrs'ekf3 =>  -- C++ `ahrs.ekf3`
      w := AP_AHRS_NavEKF3.request_yaw_reset w
  | .ahrs'dcm =>  -- C++ `ahrs.dcm`
      pure ()  -- C++ `request_yaw_reset`: no effect in the model
  | .ahrs'sim =>  -- C++ `ahrs.sim`
      pure ()  -- C++ `AP_AHRS_Backend::request_yaw_reset`: an empty body
  | _ => pure ()  -- (no other object: undefined in C++)
  return w

end AP_AHRS

namespace AP_AHRS

/-- C++ `uint8_t AP_AHRS::get_posvelyaw_source_set() const`, `AP_AHRS/AP_AHRS.cpp:1933-1940`. -/
def get_posvelyaw_source_set (w : World) : UInt8 := Id.run do
  return NavEKF3.get_active_source_set w.EKF3

/-- C++ `bool AP_AHRS::have_inertial_nav() const`, `AP_AHRS/AP_AHRS.cpp:968-974`. -/
def have_inertial_nav (s : State) : Bool := Id.run do
  return active_EKF_type s != AP_AHRS.EKFType.DCM

/-- C++ `const Vector3f & AP_AHRS::get_gyro_drift() const`, `AP_AHRS/AP_AHRS.h:95`. -/
def get_gyro_drift (s : State) : Vector3f.State := Id.run do
  return s.state.gyro_drift

end AP_AHRS

namespace AP_AHRS_NavEKF3

/-- C++ `bool AP_AHRS_NavEKF3::get_innovations(Vector3f & velInnov, Vector3f & posInnov, Vector3f & magInnov, float & tasInnov, float & yawInnov) const`, `AP_AHRS/AP_AHRS_NavEKF3.h:85-87`. -/
def get_innovations (w : World) (velInnov : Vector3f.State) (posInnov : Vector3f.State) (magInnov : Vector3f.State) (tasInnov : Binary32) (yawInnov : Binary32) : Vector3f.State × Vector3f.State × Vector3f.State × Binary32 × Binary32 × Bool := Id.run do
  let mut velInnov := velInnov
  let mut posInnov := posInnov
  let mut magInnov := magInnov
  let mut tasInnov := tasInnov
  let mut yawInnov := yawInnov
  let (t'1, t'2, t'3, t'4, t'5, t'6) := NavEKF3.getInnovations w.EKF3 w velInnov posInnov magInnov tasInnov yawInnov
  velInnov := t'1
  posInnov := t'2
  magInnov := t'3
  tasInnov := t'4
  yawInnov := t'5
  return (velInnov, posInnov, magInnov, tasInnov, yawInnov, t'6)

end AP_AHRS_NavEKF3

namespace AP_AHRS

/-- C++ `bool AP_AHRS::get_innovations(Vector3f & velInnov, Vector3f & posInnov, Vector3f & magInnov, float & tasInnov, float & yawInnov) const`, `AP_AHRS/AP_AHRS.h:402-404`. -/
def get_innovations (s : State) (w : World) (inp : Inputs) (velInnov : Vector3f.State) (posInnov : Vector3f.State) (magInnov : Vector3f.State) (tasInnov : Binary32) (yawInnov : Binary32) : Vector3f.State × Vector3f.State × Vector3f.State × Binary32 × Binary32 × Bool := Id.run do
  let mut velInnov := velInnov
  let mut posInnov := posInnov
  let mut magInnov := magInnov
  let mut tasInnov := tasInnov
  let mut yawInnov := yawInnov
  let t'1 := s.configured_backend
  let mut t'14 : Bool := false
  match t'1 with
  | .ahrs'ekf3 =>  -- C++ `ahrs.ekf3`
      let (t'2, t'3, t'4, t'5, t'6, t'7) := AP_AHRS_NavEKF3.get_innovations w velInnov posInnov magInnov tasInnov yawInnov
      velInnov := t'2
      posInnov := t'3
      magInnov := t'4
      tasInnov := t'5
      yawInnov := t'6
      t'14 := t'7
  | .ahrs'dcm =>  -- C++ `ahrs.dcm`
      let (t'8, t'9, t'10, t'11, t'12, t'13) := AP_AHRS_DCM.get_innovations velInnov posInnov magInnov tasInnov yawInnov
      velInnov := t'8
      posInnov := t'9
      magInnov := t'10
      tasInnov := t'11
      yawInnov := t'12
      t'14 := t'13
  | .ahrs'sim =>  -- C++ `ahrs.sim`
      velInnov := inp.get_innovations_velInnov
      posInnov := inp.get_innovations_posInnov
      magInnov := inp.get_innovations_magInnov
      tasInnov := inp.get_innovations_tasInnov
      yawInnov := inp.get_innovations_yawInnov
      t'14 := inp.get_innovations
  | _ => pure ()  -- (no other object: undefined in C++)
  return (velInnov, posInnov, magInnov, tasInnov, yawInnov, t'14)

/-- C++ `bool AP_AHRS::get_relative_position_D_origin(postype_t & posD) const`, `AP_AHRS/AP_AHRS.h:280-283`. -/
def get_relative_position_D_origin (s : State) (posD : Binary64) : Binary64 × Bool := Id.run do
  let mut posD := posD
  posD := ((match s.active_estimates with | .ahrs'dcm_estimates => s.dcm_estimates | .ahrs'ekf3_estimates => s.ekf3_estimates | _ => s.sim_estimates) : AP_AHRS_Backend.Estimates.State).position_D
  return (posD, ((match s.active_estimates with | .ahrs'dcm_estimates => s.dcm_estimates | .ahrs'ekf3_estimates => s.ekf3_estimates | _ => s.sim_estimates) : AP_AHRS_Backend.Estimates.State).position_D_valid)

/-- C++ `bool AP_AHRS::_get_origin(Location & ret) const`, `AP_AHRS/AP_AHRS.cpp:1733-1742`. -/
def _get_origin_Location (s : State) (w : World) (inp : Inputs) (ret : Location.State) : World × Location.State × Bool := Id.run do
  let mut w := w
  let mut ret := ret
  let (t'1, t'2, t'3) := _get_origin_EKFType_Location s w inp (configured_ekf_type s) ret
  w := t'1
  ret := t'2
  if t'3 then
    return (w, ret, true)
  let mut t'7 := inp.get_soft_armed
  if t'7 then
    let (t'4, t'5, t'6) := _get_origin_EKFType_Location s w inp (active_EKF_type s) ret
    w := t'4
    ret := t'5
    t'7 := t'6
  if t'7 then
    return (w, ret, true)
  return (w, ret, false)

/-- C++ `void AP_AHRS::get_relative_position_D_home(float & posD) const`, `AP_AHRS/AP_AHRS.cpp:1057-1084`. -/
def get_relative_position_D_home (s : State) (w : World) (inp : Inputs) (posD : Binary32) : World × Binary32 := Id.run do
  let mut w := w
  let mut posD := posD
  if !s._home_is_set then
    posD := -(AP_Baro.get_altitude_void w.barometer)
    return (w, posD)
  let mut originLLH : Location.State := Location.init_void
  let mut originD : Binary64 := (Binary64.ofBits 0x0000000000000000 /- 0.0 -/)  -- uninitialized in C++; assigned before every read
  let (t'1, t'2) := get_relative_position_D_origin s originD
  originD := t'1
  let mut t'6 := !t'2
  if !t'6 then
    let (t'3, t'4, t'5) := _get_origin_Location s w inp originLLH
    w := t'3
    originLLH := t'4
    t'6 := !t'5
  if t'6 then
    if AP_Enum_GPSUse.op_to_GPSUse s._gps_use == GPSUse.EnableWithHeight && decide (AP_GPS_FixType.toInt (AP_GPS.status_void w.gps) ≥ AP_GPS_FixType.toInt AP_GPS_FixType.FIX_3D) then
      posD := Int32.toBinary32 (s._home.alt - (AP_GPS.location_void w.gps).alt) * (Binary32.ofBits 0x3c23d70a /- 0.01 -/)
      return (w, posD)
    posD := -(AP_Baro.get_altitude_void w.barometer)
    return (w, posD)
  posD := Binary64.toBinary32 (originD - Binary32.toBinary64 (Int32.toBinary32 (originLLH.alt - s._home.alt) * (Binary32.ofBits 0x3c23d70a /- 0.01f -/)))
  return (w, posD)

/-- C++ `bool AP_AHRS::is_vibration_affected() const`, `AP_AHRS/AP_AHRS.h:407-409`. -/
def is_vibration_affected (s : State) : Bool := Id.run do
  return ((match s.configured_estimates with | .ahrs'dcm_estimates => s.dcm_estimates | .ahrs'ekf3_estimates => s.ekf3_estimates | _ => s.sim_estimates) : AP_AHRS_Backend.Estimates.State).is_vibration_affected

/-- C++ `bool AP_AHRS::using_noncompass_for_yaw() const`, `AP_AHRS/AP_AHRS.cpp:1960-1970`. -/
def using_noncompass_for_yaw (s : State) : Bool := Id.run do
  if s.active_estimates == WPtr.ahrs'dcm_estimates then
    return s.ekf3_estimates.using_noncompass_for_yaw
  return ((match s.active_estimates with | .ahrs'dcm_estimates => s.dcm_estimates | .ahrs'ekf3_estimates => s.ekf3_estimates | _ => s.sim_estimates) : AP_AHRS_Backend.Estimates.State).using_noncompass_for_yaw

/-- C++ `float AP_AHRS::cos_yaw() const`, `AP_AHRS/AP_AHRS.h:644-646`. -/
def cos_yaw (s : State) : Binary32 := Id.run do
  return s._cos_yaw

/-- C++ `float AP_AHRS::sin_yaw() const`, `AP_AHRS/AP_AHRS.h:653-655`. -/
def sin_yaw (s : State) : Binary32 := Id.run do
  return s._sin_yaw

/-- C++ `float AP_AHRS::cos_pitch() const`, `AP_AHRS/AP_AHRS.h:641-643`. -/
def cos_pitch (s : State) : Binary32 := Id.run do
  return s._cos_pitch

/-- C++ `float AP_AHRS::cos_roll() const`, `AP_AHRS/AP_AHRS.h:638-640`. -/
def cos_roll (s : State) : Binary32 := Id.run do
  return s._cos_roll

/-- C++ `bool AP_AHRS::get_relative_position_D_origin_float(float & posD) const`, `AP_AHRS/AP_AHRS.cpp:1044-1052`. -/
def get_relative_position_D_origin_float (s : State) (posD : Binary32) : Binary32 × Bool := Id.run do
  let mut posD := posD
  let mut tmp_posD : Binary64 := (Binary64.ofBits 0x0000000000000000 /- 0.0 -/)  -- uninitialized in C++; assigned before every read
  let (t'1, t'2) := get_relative_position_D_origin s tmp_posD
  tmp_posD := t'1
  if !t'2 then
    return (posD, false)
  posD := Binary64.toBinary32 tmp_posD
  return (posD, true)

/-- C++ `bool AP_AHRS::get_relative_position_NE_origin(Vector2p & posNE) const`, `AP_AHRS/AP_AHRS.h:272-275`. -/
def get_relative_position_NE_origin (s : State) (posNE : Vector2p.State) : Vector2p.State × Bool := Id.run do
  let mut posNE := posNE
  posNE := ((match s.active_estimates with | .ahrs'dcm_estimates => s.dcm_estimates | .ahrs'ekf3_estimates => s.ekf3_estimates | _ => s.sim_estimates) : AP_AHRS_Backend.Estimates.State).position_NE
  return (posNE, ((match s.active_estimates with | .ahrs'dcm_estimates => s.dcm_estimates | .ahrs'ekf3_estimates => s.ekf3_estimates | _ => s.sim_estimates) : AP_AHRS_Backend.Estimates.State).position_NE_valid)

/-- C++ `bool AP_AHRS::get_relative_position_NE_origin_float(Vector2f & posNE) const`, `AP_AHRS/AP_AHRS.cpp:1019-1027`. -/
def get_relative_position_NE_origin_float (s : State) (posNE : Vector2f.State) : Vector2f.State × Bool := Id.run do
  let mut posNE := posNE
  let mut tmp_posNE : Vector2p.State := Vector2p.init_void
  let (t'1, t'2) := get_relative_position_NE_origin s tmp_posNE
  tmp_posNE := t'1
  if !t'2 then
    return (posNE, false)
  posNE := Vector2p.tofloat tmp_posNE
  return (posNE, true)

end AP_AHRS

namespace AP_AHRS

/-- C++ `void AP_AHRS::add_trim(float roll_in_radians, float pitch_in_radians, bool save_to_eeprom)`, `AP_AHRS/AP_AHRS_Backend.cpp:49-64`. -/
def add_trim (s : State) (o : Outputs) (roll_in_radians : Binary32) (pitch_in_radians : Binary32) (save_to_eeprom : Bool := true) : State × Outputs := Id.run do
  let mut s := s
  let mut o := o
  let mut trim : Vector3f.State := AP_ParamV_Vector3_float_5.get_void s._trim
  trim := { trim with x := Estimator_lib.constrain_value_line_float (trim.x + roll_in_radians) (Estimator_lib.radians_float (-(Binary32.ofBits 0x41200000 /- 10 -/))) (Estimator_lib.radians_float (Binary32.ofBits 0x41200000 /- 10 -/)) (Int32.toUInt32 (54 : Int32)) }
  trim := { trim with y := Estimator_lib.constrain_value_line_float (trim.y + pitch_in_radians) (Estimator_lib.radians_float (-(Binary32.ofBits 0x41200000 /- 10 -/))) (Estimator_lib.radians_float (Binary32.ofBits 0x41200000 /- 10 -/)) (Int32.toUInt32 (55 : Int32)) }
  s := { s with _trim := AP_ParamV_Vector3_float_5.set s._trim trim }
  if save_to_eeprom then
    o := o.push (Output.AP_Param_save "ahrs._trim" false)
  return (s, o)

end AP_AHRS

namespace AP_AHRS

/-- C++ `void AP_AHRS::set_posvelyaw_source_set(AP_NavEKF_Source::SourceSetSelection source_set_idx)`, `AP_AHRS/AP_AHRS.cpp:1925-1930`. -/
def set_posvelyaw_source_set (w : World) (source_set_idx : AP_NavEKF_Source.SourceSetSelection) : World := Id.run do
  let mut w := w
  let t'1 := w.EKF3  -- the object out of the World for the call (--swap-out)
  w := { w with EKF3 := default }
  let (t'2, t'3) := NavEKF3.setPosVelYawSourceSet t'1 w (AP_NavEKF_Source.SourceSetSelection.toInt source_set_idx)
  w := t'3
  w := { w with EKF3 := t'2 }
  return w

end AP_AHRS

namespace AP_AHRS_NavEKF3

/-- C++ `bool AP_AHRS_NavEKF3::use_compass()`, `AP_AHRS/AP_AHRS_NavEKF3.h:61-63`. -/
def use_compass (w : World) : Bool := Id.run do
  return NavEKF3.use_compass w.EKF3 w

end AP_AHRS_NavEKF3

namespace AP_AHRS

/-- C++ `void AP_AHRS::send_ekf_status_report(class GCS_MAVLINK & link) const`, `AP_AHRS/AP_AHRS.cpp:1643-1710`. -/
def send_ekf_status_report (s : State) (o : Outputs) (inp : Inputs) : Outputs := Id.run do
  let mut o := o
  if !((match s.configured_estimates with | .ahrs'dcm_estimates => s.dcm_estimates | .ahrs'ekf3_estimates => s.ekf3_estimates | _ => s.sim_estimates) : AP_AHRS_Backend.Estimates.State).filter_status_valid then
    return o
  if !((match s.configured_estimates with | .ahrs'dcm_estimates => s.dcm_estimates | .ahrs'ekf3_estimates => s.ekf3_estimates | _ => s.sim_estimates) : AP_AHRS_Backend.Estimates.State).variances_valid then
    return o
  if !((match s.configured_estimates with | .ahrs'dcm_estimates => s.dcm_estimates | .ahrs'ekf3_estimates => s.ekf3_estimates | _ => s.sim_estimates) : AP_AHRS_Backend.Estimates.State).terrain_alt_variance_valid then
    return o
  let mut flags : UInt16 := Int16.toUInt16 (Int32.toInt16 (0 : Int32))
  if (((match s.configured_estimates with | .ahrs'dcm_estimates => s.dcm_estimates | .ahrs'ekf3_estimates => s.ekf3_estimates | _ => s.sim_estimates) : AP_AHRS_Backend.Estimates.State).filter_status >>> 0 &&& 1 != 0) then
    flags := Int16.toUInt16 (Int32.toInt16 (UInt32.toInt32 (UInt16.toUInt32 flags) ||| UInt32.toInt32 (EKF_STATUS_FLAGS.toInt EKF_STATUS_FLAGS.EKF_ATTITUDE)))
  if (((match s.configured_estimates with | .ahrs'dcm_estimates => s.dcm_estimates | .ahrs'ekf3_estimates => s.ekf3_estimates | _ => s.sim_estimates) : AP_AHRS_Backend.Estimates.State).filter_status >>> 1 &&& 1 != 0) then
    flags := Int16.toUInt16 (Int32.toInt16 (UInt32.toInt32 (UInt16.toUInt32 flags) ||| UInt32.toInt32 (EKF_STATUS_FLAGS.toInt EKF_STATUS_FLAGS.EKF_VELOCITY_HORIZ)))
  if (((match s.configured_estimates with | .ahrs'dcm_estimates => s.dcm_estimates | .ahrs'ekf3_estimates => s.ekf3_estimates | _ => s.sim_estimates) : AP_AHRS_Backend.Estimates.State).filter_status >>> 2 &&& 1 != 0) then
    flags := Int16.toUInt16 (Int32.toInt16 (UInt32.toInt32 (UInt16.toUInt32 flags) ||| UInt32.toInt32 (EKF_STATUS_FLAGS.toInt EKF_STATUS_FLAGS.EKF_VELOCITY_VERT)))
  if (((match s.configured_estimates with | .ahrs'dcm_estimates => s.dcm_estimates | .ahrs'ekf3_estimates => s.ekf3_estimates | _ => s.sim_estimates) : AP_AHRS_Backend.Estimates.State).filter_status >>> 3 &&& 1 != 0) then
    flags := Int16.toUInt16 (Int32.toInt16 (UInt32.toInt32 (UInt16.toUInt32 flags) ||| UInt32.toInt32 (EKF_STATUS_FLAGS.toInt EKF_STATUS_FLAGS.EKF_POS_HORIZ_REL)))
  if (((match s.configured_estimates with | .ahrs'dcm_estimates => s.dcm_estimates | .ahrs'ekf3_estimates => s.ekf3_estimates | _ => s.sim_estimates) : AP_AHRS_Backend.Estimates.State).filter_status >>> 4 &&& 1 != 0) then
    flags := Int16.toUInt16 (Int32.toInt16 (UInt32.toInt32 (UInt16.toUInt32 flags) ||| UInt32.toInt32 (EKF_STATUS_FLAGS.toInt EKF_STATUS_FLAGS.EKF_POS_HORIZ_ABS)))
  if (((match s.configured_estimates with | .ahrs'dcm_estimates => s.dcm_estimates | .ahrs'ekf3_estimates => s.ekf3_estimates | _ => s.sim_estimates) : AP_AHRS_Backend.Estimates.State).filter_status >>> 5 &&& 1 != 0) then
    flags := Int16.toUInt16 (Int32.toInt16 (UInt32.toInt32 (UInt16.toUInt32 flags) ||| UInt32.toInt32 (EKF_STATUS_FLAGS.toInt EKF_STATUS_FLAGS.EKF_POS_VERT_ABS)))
  if (((match s.configured_estimates with | .ahrs'dcm_estimates => s.dcm_estimates | .ahrs'ekf3_estimates => s.ekf3_estimates | _ => s.sim_estimates) : AP_AHRS_Backend.Estimates.State).filter_status >>> 6 &&& 1 != 0) then
    flags := Int16.toUInt16 (Int32.toInt16 (UInt32.toInt32 (UInt16.toUInt32 flags) ||| UInt32.toInt32 (EKF_STATUS_FLAGS.toInt EKF_STATUS_FLAGS.EKF_POS_VERT_AGL)))
  if (((match s.configured_estimates with | .ahrs'dcm_estimates => s.dcm_estimates | .ahrs'ekf3_estimates => s.ekf3_estimates | _ => s.sim_estimates) : AP_AHRS_Backend.Estimates.State).filter_status >>> 7 &&& 1 != 0) then
    flags := Int16.toUInt16 (Int32.toInt16 (UInt32.toInt32 (UInt16.toUInt32 flags) ||| UInt32.toInt32 (EKF_STATUS_FLAGS.toInt EKF_STATUS_FLAGS.EKF_CONST_POS_MODE)))
  if (((match s.configured_estimates with | .ahrs'dcm_estimates => s.dcm_estimates | .ahrs'ekf3_estimates => s.ekf3_estimates | _ => s.sim_estimates) : AP_AHRS_Backend.Estimates.State).filter_status >>> 8 &&& 1 != 0) then
    flags := Int16.toUInt16 (Int32.toInt16 (UInt32.toInt32 (UInt16.toUInt32 flags) ||| UInt32.toInt32 (EKF_STATUS_FLAGS.toInt EKF_STATUS_FLAGS.EKF_PRED_POS_HORIZ_REL)))
  if (((match s.configured_estimates with | .ahrs'dcm_estimates => s.dcm_estimates | .ahrs'ekf3_estimates => s.ekf3_estimates | _ => s.sim_estimates) : AP_AHRS_Backend.Estimates.State).filter_status >>> 9 &&& 1 != 0) then
    flags := Int16.toUInt16 (Int32.toInt16 (UInt32.toInt32 (UInt16.toUInt32 flags) ||| UInt32.toInt32 (EKF_STATUS_FLAGS.toInt EKF_STATUS_FLAGS.EKF_PRED_POS_HORIZ_ABS)))
  if !(((match s.configured_estimates with | .ahrs'dcm_estimates => s.dcm_estimates | .ahrs'ekf3_estimates => s.ekf3_estimates | _ => s.sim_estimates) : AP_AHRS_Backend.Estimates.State).filter_status >>> 16 &&& 1 != 0) then
    flags := Int16.toUInt16 (Int32.toInt16 (UInt32.toInt32 (UInt16.toUInt32 flags) ||| UInt32.toInt32 (EKF_STATUS_FLAGS.toInt EKF_STATUS_FLAGS.EKF_UNINITIALIZED)))
  if (((match s.configured_estimates with | .ahrs'dcm_estimates => s.dcm_estimates | .ahrs'ekf3_estimates => s.ekf3_estimates | _ => s.sim_estimates) : AP_AHRS_Backend.Estimates.State).filter_status >>> 14 &&& 1 != 0) then
    flags := Int16.toUInt16 (Int32.toInt16 (UInt32.toInt32 (UInt16.toUInt32 flags) ||| ((1 : Int32) <<< (15 : Int32))))
  let packet : __mavlink_ekf_status_report_t := { velocity_variance := ((match s.configured_estimates with | .ahrs'dcm_estimates => s.dcm_estimates | .ahrs'ekf3_estimates => s.ekf3_estimates | _ => s.sim_estimates) : AP_AHRS_Backend.Estimates.State).velVar, pos_horiz_variance := ((match s.configured_estimates with | .ahrs'dcm_estimates => s.dcm_estimates | .ahrs'ekf3_estimates => s.ekf3_estimates | _ => s.sim_estimates) : AP_AHRS_Backend.Estimates.State).posVar, pos_vert_variance := ((match s.configured_estimates with | .ahrs'dcm_estimates => s.dcm_estimates | .ahrs'ekf3_estimates => s.ekf3_estimates | _ => s.sim_estimates) : AP_AHRS_Backend.Estimates.State).hgtVar, compass_variance := Binary32.fmax (Binary32.fmax ((match s.configured_estimates with | .ahrs'dcm_estimates => s.dcm_estimates | .ahrs'ekf3_estimates => s.ekf3_estimates | _ => s.sim_estimates) : AP_AHRS_Backend.Estimates.State).magVar.x ((match s.configured_estimates with | .ahrs'dcm_estimates => s.dcm_estimates | .ahrs'ekf3_estimates => s.ekf3_estimates | _ => s.sim_estimates) : AP_AHRS_Backend.Estimates.State).magVar.y) ((match s.configured_estimates with | .ahrs'dcm_estimates => s.dcm_estimates | .ahrs'ekf3_estimates => s.ekf3_estimates | _ => s.sim_estimates) : AP_AHRS_Backend.Estimates.State).magVar.z, terrain_alt_variance := ((match s.configured_estimates with | .ahrs'dcm_estimates => s.dcm_estimates | .ahrs'ekf3_estimates => s.ekf3_estimates | _ => s.sim_estimates) : AP_AHRS_Backend.Estimates.State).terrain_alt_variance, flags := flags, airspeed_variance := ((match s.configured_estimates with | .ahrs'dcm_estimates => s.dcm_estimates | .ahrs'ekf3_estimates => s.ekf3_estimates | _ => s.sim_estimates) : AP_AHRS_Backend.Estimates.State).tasVar }
  o := o.push (Output.mavlink_msg_ekf_status_report_send_struct inp.get_chan packet)
  return o

/-- C++ `void AP_AHRS::get_quat_body_to_ned(Quaternion & quat) const`, `AP_AHRS/AP_AHRS.cpp:376-379`. -/
def get_quat_body_to_ned (s : State) (quat : Quaternion.State) : Quaternion.State := Id.run do
  let mut quat := quat
  quat := Quaternion.from_rotation_matrix quat (get_rotation_body_to_ned s)
  return quat

/-- C++ `void AP_AHRS::set_failure_inconsistent_message(const char * estimator, const char * axis, float diff_rad, char * failure_msg, const uint8_t failure_msg_len) const`, `AP_AHRS/AP_AHRS.cpp:1525-1528`. -/
def set_failure_inconsistent_message (estimator : String) (axis : String) (diff_rad : Binary32) (failure_msg : CText) (failure_msg_len : UInt8) : CText := Id.run do
  let mut failure_msg := failure_msg
  failure_msg := (CText.fmt (UInt8.toUInt64 failure_msg_len) "%s %s inconsistent %d deg. Wait or reboot" #[Sum.inr estimator, Sum.inr axis, Sum.inl (Int64.toUInt64 (Int32.toInt64 (Binary32.toInt32 (Estimator_lib.degrees diff_rad))))])
  return failure_msg

/-- C++ `const Matrix3f & AP_AHRS::get_DCM_rotation_body_to_ned() const`, `AP_AHRS/AP_AHRS.h:673-675`. -/
def get_DCM_rotation_body_to_ned (s : State) : Matrix3f.State := Id.run do
  return s.dcm_estimates.dcm_matrix

end AP_AHRS

namespace AP_AHRS

/-- C++ `AP_AHRS::AP_AHRS(uint8_t flags)`, `AP_AHRS/AP_AHRS.cpp:218-242`. -/
def construct (w : World) (inp : Inputs) (flags : UInt8 := Int8.toUInt8 (Int32.toInt8 (0 : Int32))) : State := Id.run do
  let mut s : State := {}
  s := { s with ekf3 := AP_AHRS_NavEKF3.init }
  s := { s with _ekf_flags := flags }
  s := { s with _home := Location.init_void }
  s := { s with _last_trim := Vector3f.init_void }
  s := { s with _rotation_autopilot_body_to_vehicle_body := Matrix3f.init_void }
  s := { s with _rotation_vehicle_body_to_autopilot_body := Matrix3f.init_void }
  let (t'1, t'2, t'3, t'4, t'5, t'6, t'7) := AP_AHRS_DCM.init s._kp_yaw s._kp s.gps_gain s.beta s._gps_use s._gps_minsats
  s := { s with dcm := t'1 }
  s := { s with _kp_yaw := t'2 }
  s := { s with _kp := t'3 }
  s := { s with gps_gain := t'4 }
  s := { s with beta := t'5 }
  s := { s with _gps_use := t'6 }
  s := { s with _gps_minsats := t'7 }
  pure ()  -- C++ `_singleton = this`: the pointer is the class's one World object (--world)
  s := { s with gps_gain._value := (Binary32.ofBits 0x3f800000 /- 1 -/) }
  s := { s with _gps_use._value := Binary32.toInt8 (UInt8.toBinary32 (GPSUse.toInt GPSUse.Enable)) }
  s := { s with _kp_yaw._value := (Binary32.ofBits 0x3e4ccccd /- 0.200000003 -/) }
  s := { s with _kp._value := (Binary32.ofBits 0x3e4ccccd /- 0.200000003 -/) }
  s := { s with _wind_max._value := Binary32.toInt8 (Binary32.ofBits 0x00000000 /- 0 -/) }
  let t'8 := (Binary32.ofBits 0x00000000 /- (float)0 -/)
  s := { s with _trim._value := ({ x := t'8, y := t'8, z := t'8 } : Vector3f.State) }
  s := { s with _board_orientation._value := Binary32.toInt8 (Binary32.ofBits 0x00000000 /- (float)0 -/) }
  s := { s with beta._value := (Binary32.ofBits 0x3dcccccd /- 0.100000001 -/) }
  s := { s with _gps_minsats._value := Binary32.toInt8 (Binary32.ofBits 0x40c00000 /- (float)6 -/) }
  s := { s with _ekf_type._value := Binary32.toInt8 (Binary32.ofBits 0x40400000 /- (float)3 -/) }
  s := { s with _options._value := Int16.toUInt16 (Binary32.toInt16 (Binary32.ofBits 0x00000000 /- (float)0 -/)) }
  s := { s with _origin_lat._value := (Binary32.ofBits 0x00000000 /- (float)0 -/) }
  s := { s with _origin_lon._value := (Binary32.ofBits 0x00000000 /- (float)0 -/) }
  s := { s with _origin_alt._value := (Binary32.ofBits 0x00000000 /- (float)0 -/) }
  s := update_configured_ekf_type s
  s := update_active_EKF_type s w inp
  s := update_secondary_backend_pointers s
  s := { s with _ekf_flags := Int8.toUInt8 (Int32.toInt8 (UInt32.toInt32 (UInt8.toUInt32 s._ekf_flags) ||| UInt32.toInt32 (AP_AHRS.Flags.toInt AP_AHRS.Flags.FLAG_ALWAYS_USE_EKF))) }
  s := { s with state.dcm_matrix := Matrix3f.identity s.state.dcm_matrix }
  s := { s with _last_trim := AP_ParamV_Vector3_float_5.get_void s._trim }
  s := { s with _rotation_autopilot_body_to_vehicle_body := Matrix3f.from_euler s._rotation_autopilot_body_to_vehicle_body s._last_trim.x s._last_trim.y s._last_trim.z }
  s := { s with _rotation_vehicle_body_to_autopilot_body := Matrix3f.transposed s._rotation_autopilot_body_to_vehicle_body }
  return s

/-! Not emitted, since they have no effect in the model (they write neither the state, the
parameters nor a reference parameter; e.g. they only save parameters):
- C++ `void AP_AHRS::update_AOA_SSA()`, `AP_AHRS/AP_AHRS_Backend.cpp:188-234`.
-/

/-- C++ `enum class AP_AHRS::LogOriginType`, `AP_AHRS/AP_AHRS.h:569-572`. -/
inductive LogOriginType where
  | ekf_origin
  | ahrs_home
deriving DecidableEq, Inhabited

/-- The value of each enumerator of `AP_AHRS::LogOriginType` (underlying type `int32_t`). -/
def LogOriginType.toInt : LogOriginType → Int32
  | .ekf_origin => (0 : Int32)
  | .ahrs_home => (1 : Int32)

end AP_AHRS

end Estimator_lib
