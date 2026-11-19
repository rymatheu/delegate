import ArduLean.Runtime.CFloat
import ArduLean.Estimator.World
import ArduLean.Estimator.libraries.AP_Param.AP_Param
import ArduLean.Estimator.libraries.AP_NavEKF.AP_NavEKF
import ArduLean.Estimator.libraries.AP_DAL.AP_DAL
import ArduLean.Estimator.libraries.AP_Param.AP_Param_2
import ArduLean.Estimator.libraries.AP_NavEKF.AP_NavEKF_2
import ArduLean.Estimator.World_3
import ArduLean.Estimator.libraries.AP_DAL.AP_DAL_2
import ArduLean.Estimator.libraries.AP_Math.AP_Math_3

/-!
ArduPilot `libraries/AP_NavEKF`, part 3 of 3. Sources: `libraries/AP_NavEKF/AP_NavEKF_Source.cpp`, `libraries/AP_NavEKF/AP_NavEKF_core_common.cpp`.

Items of `lean/Estimator_lib.lean` (the estimator translation), unchanged; placed by `tools/split_modules.py` (`ArduLean/Estimator/INDEX.md`).
-/

open FloatLib.Floats (Binary32 Binary64)

set_option maxRecDepth 200000
-- AP_DAL's `const log_RISH old_RISH = _RISH;` read only by WRITE_REPLAY_BLOCK_IFCHANGED, which is `(void)old`
-- without logging (HAL_LOGGING_ENABLED 0): an unused binding, as in the C++
set_option linter.unusedVariables false

namespace Estimator_lib

namespace AP_NavEKF_Source

/-- C++ `SourceYaw AP_NavEKF_Source::getYawSource(uint8_t core_index) const`, `AP_NavEKF/AP_NavEKF_Source.cpp:228-236`. -/
def getYawSource (s : State) (w : World) (core_index : UInt8) : World × AP_NavEKF_Source.SourceYaw := Id.run do
  let mut w := w
  let mut t'7 := (AP_Enum_AP_NavEKF_Source_SourceYaw.op_to_AP_NavEKF_Source_SourceYaw s._source_set[UInt8.toNat (getActiveSourceSet s core_index)]!.yaw == AP_NavEKF_Source.SourceYaw.COMPASS)
  if t'7 then
    let (t'4, t'5) := AP_DAL.get_singleton w
    w := t'4
    let t'6 := (WPtr.index t'5)
    t'7 := (UInt32.toInt32 (UInt8.toUInt32 (AP_DAL_Compass.get_num_enabled w.heap'AP_DAL[t'6]!._compass)) == (0 : Int32))
  if t'7 then
    return (w, AP_NavEKF_Source.SourceYaw.NONE)
  return (w, AP_Enum_AP_NavEKF_Source_SourceYaw.op_to_AP_NavEKF_Source_SourceYaw s._source_set[UInt8.toNat (getActiveSourceSet s core_index)]!.yaw)

/-- C++ `bool AP_NavEKF_Source::usingGPS(uint8_t core_index) const`, `AP_NavEKF/AP_NavEKF_Source.cpp:330-337`. -/
def usingGPS (s : State) (w : World) (core_index : UInt8) : World × Bool := Id.run do
  let mut w := w
  let mut t'3 := getPosXYSource s core_index == AP_NavEKF_Source.SourceXY.GPS || getPosZSource s core_index == AP_NavEKF_Source.SourceZ.GPS || getVelXYSource s core_index == AP_NavEKF_Source.SourceXY.GPS || getVelZSource s core_index == AP_NavEKF_Source.SourceZ.GPS
  if !t'3 then
    let (t'1, t'2) := getYawSource s w core_index
    w := t'1
    t'3 := t'2 == AP_NavEKF_Source.SourceYaw.GSF
  return (w, t'3)

/-- C++ `bool AP_NavEKF_Source::ext_nav_enabled() const`, `AP_NavEKF/AP_NavEKF_Source.cpp:558-579`. -/
def ext_nav_enabled (s : State) : Bool := Id.run do
  for i' in [0:3] do
    let i : UInt8 := Nat.toUInt8 i'
    if AP_Enum_AP_NavEKF_Source_SourceXY.op_to_AP_NavEKF_Source_SourceXY s._source_set[UInt8.toNat i]!.posxy == AP_NavEKF_Source.SourceXY.EXTNAV then
      return true
    if AP_Enum_AP_NavEKF_Source_SourceZ.op_to_AP_NavEKF_Source_SourceZ s._source_set[UInt8.toNat i]!.posz == AP_NavEKF_Source.SourceZ.EXTNAV then
      return true
    if AP_Enum_AP_NavEKF_Source_SourceXY.op_to_AP_NavEKF_Source_SourceXY s._source_set[UInt8.toNat i]!.velxy == AP_NavEKF_Source.SourceXY.EXTNAV then
      return true
    if AP_Enum_AP_NavEKF_Source_SourceZ.op_to_AP_NavEKF_Source_SourceZ s._source_set[UInt8.toNat i]!.velz == AP_NavEKF_Source.SourceZ.EXTNAV then
      return true
    if AP_Enum_AP_NavEKF_Source_SourceYaw.op_to_AP_NavEKF_Source_SourceYaw s._source_set[UInt8.toNat i]!.yaw == AP_NavEKF_Source.SourceYaw.EXTNAV then
      return true
  return false

/-- C++ `bool AP_NavEKF_Source::wheel_encoder_enabled() const`, `AP_NavEKF/AP_NavEKF_Source.cpp:582-591`. -/
def wheel_encoder_enabled (s : State) : Bool := Id.run do
  for i' in [0:3] do
    let i : UInt8 := Nat.toUInt8 i'
    if AP_Enum_AP_NavEKF_Source_SourceXY.op_to_AP_NavEKF_Source_SourceXY s._source_set[UInt8.toNat i]!.velxy == AP_NavEKF_Source.SourceXY.WHEEL_ENCODER then
      return true
  return false

end AP_NavEKF_Source

namespace NavEKF3_core

/-- C++ `void NavEKF_core_common::fill_scratch_variables()`, `AP_NavEKF/AP_NavEKF_core_common.cpp:25-35` (a member of `NavEKF_core_common`, translated for `NavEKF3_core`). -/
def fill_scratch_variables (w : World) : World := Id.run do
  let mut w := w
  let (t'1, t'2) := Estimator_lib.fill_nanf_double_uint16_t w w.NavEKF_core_common'KHP 0 (UInt64.toUInt16 ((4608 : UInt64) / (8 : UInt64)))
  w := t'1
  w := { w with NavEKF_core_common'KHP := t'2 }
  let (t'3, t'4) := Estimator_lib.fill_nanf_double_uint16_t w w.NavEKF_core_common'Kfusion 0 (UInt64.toUInt16 ((224 : UInt64) / (8 : UInt64)))
  w := t'3
  w := { w with NavEKF_core_common'Kfusion := t'4 }
  return w

end NavEKF3_core

namespace AP_NavEKF_Source

/-- C++ `bool AP_NavEKF_Source::pre_arm_check(bool requires_position, char * failure_msg, uint8_t failure_msg_len) const`, `AP_NavEKF/AP_NavEKF_Source.cpp:361-555`. -/
def pre_arm_check (s : State) (w : World) (requires_position : Bool) (failure_msg : CText) (failure_msg_len : UInt8) : World × CText × Bool := Id.run do
  let mut w := w
  let mut failure_msg := failure_msg
  let (t'1, t'2) := AP_DAL.get_singleton w
  w := t'1
  let t'3 := (WPtr.index t'2)
  let mut baro_required : Bool := false
  let mut beacon_required : Bool := false
  let mut compass_required : Bool := false
  let mut gps_required : Bool := false
  let mut rangefinder_required : Bool := false
  let mut visualodom_required : Bool := false
  let mut optflow_required : Bool := false
  let mut wheelencoder_required : Bool := false
  for i' in [0:3] do
    let i : UInt8 := Nat.toUInt8 i'
    if requires_position then
      match AP_NavEKF_Source.SourceXY.ofInt (Int8.toUInt8 (AP_Enum_AP_NavEKF_Source_SourceXY.get_void s._source_set[UInt8.toNat i]!.posxy)) with
      | .NONE =>
        pure ()
      | .GPS =>
        gps_required := true
      | .BEACON =>
        beacon_required := true
      | .EXTNAV =>
        visualodom_required := true
      | .OPTFLOW | .WHEEL_ENCODER =>
        failure_msg := (CText.fmt (UInt8.toUInt64 failure_msg_len) "Check EK3_SRC%d_POSXY" #[Sum.inl (Int64.toUInt64 (Int32.toInt64 (UInt32.toInt32 (UInt8.toUInt32 i) + (1 : Int32))))])
        return (w, failure_msg, false)
      match AP_NavEKF_Source.SourceXY.ofInt (Int8.toUInt8 (AP_Enum_AP_NavEKF_Source_SourceXY.get_void s._source_set[UInt8.toNat i]!.velxy)) with
      | .NONE =>
        pure ()
      | .GPS =>
        gps_required := true
      | .OPTFLOW =>
        optflow_required := true
      | .EXTNAV =>
        visualodom_required := true
      | .WHEEL_ENCODER =>
        wheelencoder_required := true
      | .BEACON =>
        failure_msg := (CText.fmt (UInt8.toUInt64 failure_msg_len) "Check EK3_SRC%d_VELXY" #[Sum.inl (Int64.toUInt64 (Int32.toInt64 (UInt32.toInt32 (UInt8.toUInt32 i) + (1 : Int32))))])
        return (w, failure_msg, false)
      match AP_NavEKF_Source.SourceZ.ofInt (Int8.toUInt8 (AP_Enum_AP_NavEKF_Source_SourceZ.get_void s._source_set[UInt8.toNat i]!.posz)) with
      | .BARO =>
        baro_required := true
      | .RANGEFINDER =>
        rangefinder_required := true
      | .GPS =>
        gps_required := true
      | .BEACON =>
        beacon_required := true
      | .EXTNAV =>
        visualodom_required := true
      | .NONE =>
        pure ()
      match AP_NavEKF_Source.SourceZ.ofInt (Int8.toUInt8 (AP_Enum_AP_NavEKF_Source_SourceZ.get_void s._source_set[UInt8.toNat i]!.velz)) with
      | .NONE =>
        pure ()
      | .GPS =>
        gps_required := true
      | .EXTNAV =>
        visualodom_required := true
      | .BARO | .RANGEFINDER | .BEACON =>
        failure_msg := (CText.fmt (UInt8.toUInt64 failure_msg_len) "Check EK3_SRC%d_VELZ" #[Sum.inl (Int64.toUInt64 (Int32.toInt64 (UInt32.toInt32 (UInt8.toUInt32 i) + (1 : Int32))))])
        return (w, failure_msg, false)
    match AP_NavEKF_Source.SourceYaw.ofInt (Int8.toUInt8 (AP_Enum_AP_NavEKF_Source_SourceYaw.get_void s._source_set[UInt8.toNat i]!.yaw)) with
    | .NONE | .GPS =>
      pure ()
    | .COMPASS =>
      pure ()
    | .GPS_COMPASS_FALLBACK =>
      compass_required := true
    | .EXTNAV =>
      visualodom_required := true
    | .GSF =>
      gps_required := true
  let ekf_requires_msg : String := "EK3 sources require %s"
  if baro_required && (UInt32.toInt32 (UInt8.toUInt32 (AP_DAL_Baro.num_instances w.heap'AP_DAL[t'3]!._baro)) == (0 : Int32)) then
    failure_msg := (CText.fmt (UInt8.toUInt64 failure_msg_len) ekf_requires_msg #[Sum.inr "Baro"])
    return (w, failure_msg, false)
  if beacon_required then
    let beacon_available : Bool := false
    if !beacon_available then
      failure_msg := (CText.fmt (UInt8.toUInt64 failure_msg_len) ekf_requires_msg #[Sum.inr "Beacon"])
      return (w, failure_msg, false)
  if compass_required && (UInt32.toInt32 (UInt8.toUInt32 (AP_DAL_Compass.get_num_enabled w.heap'AP_DAL[t'3]!._compass)) == (0 : Int32)) then
    failure_msg := (CText.fmt (UInt8.toUInt64 failure_msg_len) ekf_requires_msg #[Sum.inr "Compass"])
    return (w, failure_msg, false)
  if gps_required && (UInt32.toInt32 (UInt8.toUInt32 (AP_DAL_GPS.num_sensors w.heap'AP_DAL[t'3]!._gps)) == (0 : Int32)) then
    failure_msg := (CText.fmt (UInt8.toUInt64 failure_msg_len) ekf_requires_msg #[Sum.inr "GPS"])
    return (w, failure_msg, false)
  if optflow_required && !(AP_DAL.opticalflow_enabled w.heap'AP_DAL[t'3]!) then
    failure_msg := (CText.fmt (UInt8.toUInt64 failure_msg_len) ekf_requires_msg #[Sum.inr "OpticalFlow"])
    return (w, failure_msg, false)
  if rangefinder_required then
    let have_rangefinder : Bool := false
    if !have_rangefinder then
      failure_msg := (CText.fmt (UInt8.toUInt64 failure_msg_len) ekf_requires_msg #[Sum.inr "RangeFinder"])
      return (w, failure_msg, false)
  if visualodom_required then
    let visualodom_available : Bool := false
    if !visualodom_available then
      failure_msg := (CText.fmt (UInt8.toUInt64 failure_msg_len) ekf_requires_msg #[Sum.inr "VisualOdom"])
      return (w, failure_msg, false)
  if wheelencoder_required && !(AP_DAL.wheelencoder_enabled w.heap'AP_DAL[t'3]!) then
    failure_msg := (CText.fmt (UInt8.toUInt64 failure_msg_len) ekf_requires_msg #[Sum.inr "WheelEncoder"])
    return (w, failure_msg, false)
  return (w, failure_msg, true)

end AP_NavEKF_Source

end Estimator_lib
