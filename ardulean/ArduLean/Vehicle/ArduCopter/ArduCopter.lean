import ArduLean.Runtime.Bridge
import ArduLean.Vehicle.libraries.AP_Math.AP_Math
import ArduLean.Vehicle.libraries.AP_Param.AP_Param
import ArduLean.Vehicle.libraries.AC_AttitudeControl.AC_AttitudeControl
import ArduLean.Vehicle.libraries.AC_WPNav.AC_WPNav
import ArduLean.Vehicle.libraries.AP_SurfaceDistance.AP_SurfaceDistance
import ArduLean.Vehicle.libraries.AP_Mission.AP_Mission
import ArduLean.Vehicle.libraries.AP_BoardConfig.AP_BoardConfig
import ArduLean.Vehicle.libraries.RC_Channel.RC_Channel
import ArduLean.Vehicle.libraries.AP_Arming.AP_Arming

/-!
ArduPilot `ArduCopter`, part 1 of 3. Sources: `ArduCopter/mode.h`, `ArduCopter/mode.cpp`, `ArduCopter/mode_auto.cpp`, `ArduCopter/mode_guided.cpp`, `ArduCopter/autoyaw.cpp`, `ArduCopter/GCS_MAVLink_Copter.cpp`, `ArduCopter/RC_Channel_Copter.cpp`, `ArduCopter/mode_rtl.cpp` and 23 more.

Items of `lean/Vehicle_lib.lean` (the vehicle translation), unchanged; placed by `tools/split_modules.py` (`ArduLean/Vehicle/INDEX.md`).
-/

open FloatLib.Floats (Binary32 Binary64)

set_option linter.unusedVariables false
set_option linter.unreachableTactic false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false

namespace Vehicle_lib

/-- C++ `GCS_Copter::chan : GCS_MAVLINK_Copter *(const uint8_t)`, `GCS.h:?-?`. -/
def GCS_Copter.chan (this : UInt64) (ofs : UInt8) : PMem.M UInt64 := do
  let mut ofs := ofs
  let t'1 ← PMem.ldU8 (this + 28)
  if (decide ((UInt32.toInt32 (UInt8.toUInt32 (ofs))) ≥ (UInt32.toInt32 (UInt8.toUInt32 (t'1))))) then
    return (0 : UInt64)
  let t'2 ← PMem.ldU64 ((this + 32) + ((UInt64.toInt64 (UInt8.toUInt64 (ofs))) * 8).toUInt64)
  return t'2

/-- C++ `Mode::AutoYaw::set_mode : void (Mode)`, `autoyaw.cpp:60-112`. -/
def Mode.AutoYaw.set_mode (this : UInt64) (yaw_mode : Int32) : PMem.M Unit := do
  let mut yaw_mode := yaw_mode
  let t'1 ← PMem.ldI32 this
  if (t'1 == yaw_mode) then
    return ()
  let t'2 ← PMem.ldI32 this
  PMem.stI32 (this + 4) t'2
  PMem.stI32 this yaw_mode
  let t'3 ← PMem.ldI32 this
  let sw'4 := t'3
  if sw'4 == (0 : Int32) then
    let t'5 ← PMem.ldU64 ((0x86d8 : UInt64) /- &copter -/ + 11168)
    let t'6 ← AC_AttitudeControl.get_att_target_euler_rad t'5
    let t'7 ← PMem.ldF32 (t'6 + 8)
    PMem.stF32 (this + 36) t'7
  else if sw'4 == (1 : Int32) then
    pure ()
  else if sw'4 == (2 : Int32) then
    pure ()
  else if sw'4 == (3 : Int32) then
    pure ()
  else if sw'4 == (4 : Int32) then
    let t'8 ← VehicleBridge.AP_AHRS.get_yaw_rad'0 ((0x86d8 : UInt64) /- &copter -/ + 4080)
    PMem.stF32 (this + 32) t'8
  else if sw'4 == (5 : Int32) then
    pure ()
  else if sw'4 == (6 : Int32) then
    pure ()
  else if sw'4 == (7 : Int32) then
    let t'9 := Binary64.toBinary32 ((Binary64.ofBits 0x0000000000000000 /- 0 -/))
    PMem.stF32 (this + 40) t'9
  else if sw'4 == (8 : Int32) || sw'4 == (9 : Int32) || sw'4 == (10 : Int32) then
    pure ()
  else
    pure ()
  return ()

/-- C++ `Mode::AutoYaw::default_mode : Mode::AutoYaw::Mode (bool) const`, `autoyaw.cpp:36-57`. -/
def Mode.AutoYaw.default_mode (this : UInt64) (rtl : Bool) : PMem.M Int32 := do
  let mut rtl := rtl
  let t'1 ← AP_Enum'Parameters_WPYawBehavior.operator_const_Parameters.WPYawBehavior (((0x86d8 : UInt64) /- &copter -/ + 6776) + 25)
  let sw'2 := t'1
  if sw'2 == (0 : Int32) then
    return (0 : Int32)
  else if sw'2 == (2 : Int32) then
    if rtl then
      return (0 : Int32)
    else
      return (1 : Int32)
    return (4 : Int32)
  else if sw'2 == (3 : Int32) then
    return (4 : Int32)
  else if sw'2 == (1 : Int32) then
    return (1 : Int32)
  else
    return (1 : Int32)

/-- C++ `Mode::AutoYaw::set_mode_to_default : void (bool)`, `autoyaw.cpp:29-32`. -/
def Mode.AutoYaw.set_mode_to_default (this : UInt64) (rtl : Bool) : PMem.M Unit := do
  let mut rtl := rtl
  let t'1 ← Mode.AutoYaw.default_mode this rtl
  Mode.AutoYaw.set_mode this t'1
  return ()

/-- C++ `ModeGuided::option_is_enabled : bool (Option) const`, `mode_guided.cpp:113-116`. -/
def ModeGuided.option_is_enabled (this : UInt64) (option : UInt32) : PMem.M Bool := do
  let mut option := option
  let t'1 ← AP_ParamTBase'unsigned_int_3.get (((0x86d8 : UInt64) /- &copter -/ + 6840) + 1684)
  let t'2 ← PMem.ldU32 t'1
  return ((t'2 &&& option) != (Int32.toUInt32 ((0 : Int32))))

/-- C++ `ModeGuided::set_attitude_target_provides_thrust : bool () const`, `mode_guided.cpp:652-655`. -/
def ModeGuided.set_attitude_target_provides_thrust (this : UInt64) : PMem.M Bool := do
  let t'1 ← ModeGuided.option_is_enabled this (8 : UInt32)
  return t'1

/-- `Mode.in_guided_mode` as a pure function of its arguments (it reads and writes no memory). -/
def Mode.in_guided_mode.pure' (this : UInt64) : Id Bool := do
  return false

/-- C++ `Mode::in_guided_mode : bool () const`, `AP_Common.h:133-?`. -/
def Mode.in_guided_mode (this : UInt64) : PMem.M Bool :=
  pure (_root_.Vehicle_lib.Mode.in_guided_mode.pure' this)

/-- C++ `ModeAuto::in_guided_mode : bool () const`, `mode.h:549-?`. -/
def ModeAuto.in_guided_mode (this : UInt64) : PMem.M Bool := do
  let t'1 ← PMem.ldU8 (this + 820)
  let mut sc'3 := (t'1 == (7 : UInt8))
  if !sc'3 then
    let t'2 ← PMem.ldU8 (this + 820)
    sc'3 := (t'2 == (10 : UInt8))
  return sc'3

/-- `ModeGuided.in_guided_mode` as a pure function of its arguments (it reads and writes no memory). -/
def ModeGuided.in_guided_mode.pure' (this : UInt64) : Id Bool := do
  return true

/-- C++ `ModeGuided::in_guided_mode : bool () const`, `mode.h:1125-?`. -/
def ModeGuided.in_guided_mode (this : UInt64) : PMem.M Bool :=
  pure (_root_.Vehicle_lib.ModeGuided.in_guided_mode.pure' this)

/-- C++ `GCS_MAVLINK_Copter::sane_vel_or_acc_vector : bool (const Vector3f &) const`, `GCS_MAVLink_Copter.cpp:855-864`. -/
def GCS_MAVLINK_Copter.sane_vel_or_acc_vector (this : UInt64) (vec : UInt64) : PMem.M Bool := do
  for i'1 in [0:3] do
    let i : UInt8 := UInt8.ofNat i'1
    let t'2 ← Vector3'float.operator__ vec i
    let t'3 ← PMem.ldF32 t'2
    let mut sc'6 := (Binary32.isNaN t'3)
    if !sc'6 then
      let t'4 ← Vector3'float.operator__ vec i
      let t'5 ← PMem.ldF32 t'4
      sc'6 := (decide ((Binary32.abs t'5) > (Int32.toBinary32 ((1000 : Int32)))))
    if sc'6 then
      return false
  return true

/-- C++ `Mode::AutoYaw::set_yaw_angle_and_rate_rad : void (float, float)`, `autoyaw.cpp:149-158`. -/
def Mode.AutoYaw.set_yaw_angle_and_rate_rad (this : UInt64) (yaw_angle_rad : Binary32) (yaw_rate_rads : Binary32) : PMem.M Unit := do
  let mut yaw_angle_rad := yaw_angle_rad
  let mut yaw_rate_rads := yaw_rate_rads
  let t'1 := ((← PMem.clock) / 1000).toUInt32
  PMem.stU32 (this + 28) t'1
  PMem.stF32 (this + 36) yaw_angle_rad
  PMem.stF32 (this + 40) yaw_rate_rads
  Mode.AutoYaw.set_mode this (6 : Int32)
  return ()

/-- C++ `Mode::AutoYaw::set_rate_rad : void (float)`, `autoyaw.cpp:210-214`. -/
def Mode.AutoYaw.set_rate_rad (this : UInt64) (turn_rate_rads : Binary32) : PMem.M Unit := do
  let mut turn_rate_rads := turn_rate_rads
  Mode.AutoYaw.set_mode this (7 : Int32)
  PMem.stF32 (this + 40) turn_rate_rads
  return ()

/-- C++ `ModeGuided::use_wpnav_for_position_control : bool () const`, `mode_guided.cpp:670-673`. -/
def ModeGuided.use_wpnav_for_position_control (this : UInt64) : PMem.M Bool := do
  let t'1 ← ModeGuided.option_is_enabled this (64 : UInt32)
  return t'1

/-- C++ `GCS_Copter::chan : const GCS_MAVLINK_Copter *(const uint8_t) const`, `GCS.h:?-?`. -/
def GCS_Copter.chan'2 (this : UInt64) (ofs : UInt8) : PMem.M UInt64 := do
  let mut ofs := ofs
  let t'1 ← PMem.ldU8 (this + 28)
  if (decide ((UInt32.toInt32 (UInt8.toUInt32 (ofs))) ≥ (UInt32.toInt32 (UInt8.toUInt32 (t'1))))) then
    return (0 : UInt64)
  let t'2 ← PMem.ldU64 ((this + 32) + ((UInt64.toInt64 (UInt8.toUInt64 (ofs))) * 8).toUInt64)
  return t'2

/-- C++ `GCS_Copter::vehicle_initialised : bool () const`, `GCS_MAVLink_Copter.cpp:288-290`. -/
def GCS_Copter.vehicle_initialised (this : UInt64) : PMem.M Bool := do
  let t'1 ← PMem.ldB (((0x86d8 : UInt64) /- &copter -/ + 9448) + 13)
  return t'1

/-- C++ `GCS_MAVLINK_Copter::params_ready : bool () const`, `GCS_MAVLink_Copter.cpp:359-369`. -/
def GCS_MAVLINK_Copter.params_ready (this : UInt64) : PMem.M Bool := do
  let t'1 ← AP_BoardConfig.in_config_error
  if t'1 then
    return true
  let t'2 ← PMem.ldB (((0x86d8 : UInt64) /- &copter -/ + 9448) + 22)
  return t'2

/-- `ModeAltHold.is_autopilot` as a pure function of its arguments (it reads and writes no memory). -/
def ModeAltHold.is_autopilot.pure' (this : UInt64) : Id Bool := do
  return false

/-- C++ `ModeAltHold::is_autopilot : bool () const`, `mode.h:511-?`. -/
def ModeAltHold.is_autopilot (this : UInt64) : PMem.M Bool :=
  pure (_root_.Vehicle_lib.ModeAltHold.is_autopilot.pure' this)

/-- `ModeAuto.is_autopilot` as a pure function of its arguments (it reads and writes no memory). -/
def ModeAuto.is_autopilot.pure' (this : UInt64) : Id Bool := do
  return true

/-- C++ `ModeAuto::is_autopilot : bool () const`, `mode.h:548-?`. -/
def ModeAuto.is_autopilot (this : UInt64) : PMem.M Bool :=
  pure (_root_.Vehicle_lib.ModeAuto.is_autopilot.pure' this)

/-- `ModeBrake.is_autopilot` as a pure function of its arguments (it reads and writes no memory). -/
def ModeBrake.is_autopilot.pure' (this : UInt64) : Id Bool := do
  return true

/-- C++ `ModeBrake::is_autopilot : bool () const`, `mode.h:890-?`. -/
def ModeBrake.is_autopilot (this : UInt64) : PMem.M Bool :=
  pure (_root_.Vehicle_lib.ModeBrake.is_autopilot.pure' this)

/-- `ModeCircle.is_autopilot` as a pure function of its arguments (it reads and writes no memory). -/
def ModeCircle.is_autopilot.pure' (this : UInt64) : Id Bool := do
  return true

/-- C++ `ModeCircle::is_autopilot : bool () const`, `mode.h:920-?`. -/
def ModeCircle.is_autopilot (this : UInt64) : PMem.M Bool :=
  pure (_root_.Vehicle_lib.ModeCircle.is_autopilot.pure' this)

/-- `ModeGuided.is_autopilot` as a pure function of its arguments (it reads and writes no memory). -/
def ModeGuided.is_autopilot.pure' (this : UInt64) : Id Bool := do
  return true

/-- C++ `ModeGuided::is_autopilot : bool () const`, `mode.h:1123-?`. -/
def ModeGuided.is_autopilot (this : UInt64) : PMem.M Bool :=
  pure (_root_.Vehicle_lib.ModeGuided.is_autopilot.pure' this)

/-- `ModeLand.is_autopilot` as a pure function of its arguments (it reads and writes no memory). -/
def ModeLand.is_autopilot.pure' (this : UInt64) : Id Bool := do
  return true

/-- C++ `ModeLand::is_autopilot : bool () const`, `mode.h:1318-?`. -/
def ModeLand.is_autopilot (this : UInt64) : PMem.M Bool :=
  pure (_root_.Vehicle_lib.ModeLand.is_autopilot.pure' this)

/-- `ModeLoiter.is_autopilot` as a pure function of its arguments (it reads and writes no memory). -/
def ModeLoiter.is_autopilot.pure' (this : UInt64) : Id Bool := do
  return false

/-- C++ `ModeLoiter::is_autopilot : bool () const`, `mode.h:1380-?`. -/
def ModeLoiter.is_autopilot (this : UInt64) : PMem.M Bool :=
  pure (_root_.Vehicle_lib.ModeLoiter.is_autopilot.pure' this)

/-- `ModeRTL.is_autopilot` as a pure function of its arguments (it reads and writes no memory). -/
def ModeRTL.is_autopilot.pure' (this : UInt64) : Id Bool := do
  return true

/-- C++ `ModeRTL::is_autopilot : bool () const`, `mode.h:1527-?`. -/
def ModeRTL.is_autopilot (this : UInt64) : PMem.M Bool :=
  pure (_root_.Vehicle_lib.ModeRTL.is_autopilot.pure' this)

/-- `ModeStabilize.is_autopilot` as a pure function of its arguments (it reads and writes no memory). -/
def ModeStabilize.is_autopilot.pure' (this : UInt64) : Id Bool := do
  return false

/-- C++ `ModeStabilize::is_autopilot : bool () const`, `mode.h:1759-?`. -/
def ModeStabilize.is_autopilot (this : UInt64) : PMem.M Bool :=
  pure (_root_.Vehicle_lib.ModeStabilize.is_autopilot.pure' this)

/-- `ModeAltHold.mode_number` as a pure function of its arguments (it reads and writes no memory). -/
def ModeAltHold.mode_number.pure' (this : UInt64) : Id UInt8 := do
  return (2 : UInt8)

/-- C++ `ModeAltHold::mode_number : Number () const`, `mode.h:503-?`. -/
def ModeAltHold.mode_number (this : UInt64) : PMem.M UInt8 :=
  pure (_root_.Vehicle_lib.ModeAltHold.mode_number.pure' this)

/-- C++ `ModeAuto::mode_number : Number () const`, `mode.h:539-?`. -/
def ModeAuto.mode_number (this : UInt64) : PMem.M UInt8 := do
  let t'1 ← PMem.ldB (this + 861)
  let mut c'2 : UInt8 := default
  if t'1 then
    c'2 := (27 : UInt8)
  else
    c'2 := (3 : UInt8)
  return c'2

/-- `ModeBrake.mode_number` as a pure function of its arguments (it reads and writes no memory). -/
def ModeBrake.mode_number.pure' (this : UInt64) : Id UInt8 := do
  return (17 : UInt8)

/-- C++ `ModeBrake::mode_number : Number () const`, `mode.h:882-?`. -/
def ModeBrake.mode_number (this : UInt64) : PMem.M UInt8 :=
  pure (_root_.Vehicle_lib.ModeBrake.mode_number.pure' this)

/-- `ModeCircle.mode_number` as a pure function of its arguments (it reads and writes no memory). -/
def ModeCircle.mode_number.pure' (this : UInt64) : Id UInt8 := do
  return (7 : UInt8)

/-- C++ `ModeCircle::mode_number : Number () const`, `mode.h:912-?`. -/
def ModeCircle.mode_number (this : UInt64) : PMem.M UInt8 :=
  pure (_root_.Vehicle_lib.ModeCircle.mode_number.pure' this)

/-- `ModeGuided.mode_number` as a pure function of its arguments (it reads and writes no memory). -/
def ModeGuided.mode_number.pure' (this : UInt64) : Id UInt8 := do
  return (4 : UInt8)

/-- C++ `ModeGuided::mode_number : Number () const`, `mode.h:1115-?`. -/
def ModeGuided.mode_number (this : UInt64) : PMem.M UInt8 :=
  pure (_root_.Vehicle_lib.ModeGuided.mode_number.pure' this)

/-- `ModeLand.mode_number` as a pure function of its arguments (it reads and writes no memory). -/
def ModeLand.mode_number.pure' (this : UInt64) : Id UInt8 := do
  return (9 : UInt8)

/-- C++ `ModeLand::mode_number : Number () const`, `mode.h:1310-?`. -/
def ModeLand.mode_number (this : UInt64) : PMem.M UInt8 :=
  pure (_root_.Vehicle_lib.ModeLand.mode_number.pure' this)

/-- `ModeLoiter.mode_number` as a pure function of its arguments (it reads and writes no memory). -/
def ModeLoiter.mode_number.pure' (this : UInt64) : Id UInt8 := do
  return (5 : UInt8)

/-- C++ `ModeLoiter::mode_number : Number () const`, `mode.h:1372-?`. -/
def ModeLoiter.mode_number (this : UInt64) : PMem.M UInt8 :=
  pure (_root_.Vehicle_lib.ModeLoiter.mode_number.pure' this)

/-- `ModeRTL.mode_number` as a pure function of its arguments (it reads and writes no memory). -/
def ModeRTL.mode_number.pure' (this : UInt64) : Id UInt8 := do
  return (6 : UInt8)

/-- C++ `ModeRTL::mode_number : Number () const`, `mode.h:1516-?`. -/
def ModeRTL.mode_number (this : UInt64) : PMem.M UInt8 :=
  pure (_root_.Vehicle_lib.ModeRTL.mode_number.pure' this)

/-- `ModeStabilize.mode_number` as a pure function of its arguments (it reads and writes no memory). -/
def ModeStabilize.mode_number.pure' (this : UInt64) : Id UInt8 := do
  return (0 : UInt8)

/-- C++ `ModeStabilize::mode_number : Number () const`, `mode.h:1752-?`. -/
def ModeStabilize.mode_number (this : UInt64) : PMem.M UInt8 :=
  pure (_root_.Vehicle_lib.ModeStabilize.mode_number.pure' this)

/-- `ModeAltHold.name4` as a pure function of its arguments (it reads and writes no memory). -/
def ModeAltHold.name4.pure' (this : UInt64) : Id UInt64 := do
  return (0x14916 : UInt64) /- "ALTH" -/

/-- C++ `ModeAltHold::name4 : const char *() const`, `mode.h:525-?`. -/
def ModeAltHold.name4 (this : UInt64) : PMem.M UInt64 :=
  pure (_root_.Vehicle_lib.ModeAltHold.name4.pure' this)

/-- C++ `ModeAuto::name4 : const char *() const`, `functor.h:638-?`. -/
def ModeAuto.name4 (this : UInt64) : PMem.M UInt64 := do
  let t'1 ← PMem.ldB (this + 861)
  let mut c'2 : UInt64 := 0
  if t'1 then
    c'2 := (0x14ad6 : UInt64) /- "ARTL" -/
  else
    c'2 := (0x14adb : UInt64) /- "AUTO" -/
  return c'2

/-- `ModeBrake.name4` as a pure function of its arguments (it reads and writes no memory). -/
def ModeBrake.name4.pure' (this : UInt64) : Id UInt64 := do
  return (0x14ae6 : UInt64) /- "BRAK" -/

/-- C++ `ModeBrake::name4 : const char *() const`, `mode.h:897-?`. -/
def ModeBrake.name4 (this : UInt64) : PMem.M UInt64 :=
  pure (_root_.Vehicle_lib.ModeBrake.name4.pure' this)

/-- `ModeCircle.name4` as a pure function of its arguments (it reads and writes no memory). -/
def ModeCircle.name4.pure' (this : UInt64) : Id UInt64 := do
  return (0x14af2 : UInt64) /- "CIRC" -/

/-- C++ `ModeCircle::name4 : const char *() const`, `mode.h:925-?`. -/
def ModeCircle.name4 (this : UInt64) : PMem.M UInt64 :=
  pure (_root_.Vehicle_lib.ModeCircle.name4.pure' this)

/-- `ModeGuided.name4` as a pure function of its arguments (it reads and writes no memory). -/
def ModeGuided.name4.pure' (this : UInt64) : Id UInt64 := do
  return (0x14afe : UInt64) /- "GUID" -/

/-- C++ `ModeGuided::name4 : const char *() const`, `mode.h:1207-?`. -/
def ModeGuided.name4 (this : UInt64) : PMem.M UInt64 :=
  pure (_root_.Vehicle_lib.ModeGuided.name4.pure' this)

/-- `ModeLand.name4` as a pure function of its arguments (it reads and writes no memory). -/
def ModeLand.name4.pure' (this : UInt64) : Id UInt64 := do
  return (0x14b51 : UInt64) /- "LAND" -/

/-- C++ `ModeLand::name4 : const char *() const`, `mode.h:1348-?`. -/
def ModeLand.name4 (this : UInt64) : PMem.M UInt64 :=
  pure (_root_.Vehicle_lib.ModeLand.name4.pure' this)

/-- `ModeLoiter.name4` as a pure function of its arguments (it reads and writes no memory). -/
def ModeLoiter.name4.pure' (this : UInt64) : Id UInt64 := do
  return (0x14b5d : UInt64) /- "LOIT" -/

/-- C++ `ModeLoiter::name4 : const char *() const`, `mode.h:1396-?`. -/
def ModeLoiter.name4 (this : UInt64) : PMem.M UInt64 :=
  pure (_root_.Vehicle_lib.ModeLoiter.name4.pure' this)

/-- `ModeRTL.name4` as a pure function of its arguments (it reads and writes no memory). -/
def ModeRTL.name4.pure' (this : UInt64) : Id UInt64 := do
  return (0x14c9e : UInt64) /- "RTL " -/

/-- C++ `ModeRTL::name4 : const char *() const`, `mode.h:1586-?`. -/
def ModeRTL.name4 (this : UInt64) : PMem.M UInt64 :=
  pure (_root_.Vehicle_lib.ModeRTL.name4.pure' this)

/-- `ModeStabilize.name4` as a pure function of its arguments (it reads and writes no memory). -/
def ModeStabilize.name4.pure' (this : UInt64) : Id UInt64 := do
  return (0x14cad : UInt64) /- "STAB" -/

/-- C++ `ModeStabilize::name4 : const char *() const`, `mode.h:1769-?`. -/
def ModeStabilize.name4 (this : UInt64) : PMem.M UInt64 :=
  pure (_root_.Vehicle_lib.ModeStabilize.name4.pure' this)

/-- `Copter.gcs` as a pure function of its arguments (it reads and writes no memory). -/
def Copter.gcs.pure' (this : UInt64) : Id UInt64 := do
  return (this + 8904)

/-- C++ `Copter::gcs : GCS_Copter &()`, `Copter.h:341-?`. -/
def Copter.gcs (this : UInt64) : PMem.M UInt64 :=
  pure (_root_.Vehicle_lib.Copter.gcs.pure' this)

/-- `Copter.mode_from_mode_num` as a pure function of its arguments (it reads and writes no memory). -/
def Copter.mode_from_mode_num.pure' (this : UInt64) (mode : UInt8) : Id UInt64 := do
  let mut mode := mode
  let sw'1 := mode
  if sw'1 == (0 : UInt8) then
    return (this + 13096)
  else if sw'1 == (2 : UInt8) then
    return (this + 11256)
  else if sw'1 == (3 : UInt8) then
    return (this + 11368)
  else if sw'1 == (7 : UInt8) then
    return (this + 12400)
  else if sw'1 == (5 : UInt8) then
    return (this + 12776)
  else if sw'1 == (4 : UInt8) then
    return (this + 12520)
  else if sw'1 == (9 : UInt8) then
    return (this + 12640)
  else if sw'1 == (6 : UInt8) then
    return (this + 12888)
  else if sw'1 == (17 : UInt8) then
    return (this + 12280)
  else
    pure ()
  return (0 : UInt64)

/-- C++ `Copter::mode_from_mode_num : Mode *(const Mode::Number)`, `mode.cpp:32-171`. -/
def Copter.mode_from_mode_num (this : UInt64) (mode : UInt8) : PMem.M UInt64 :=
  pure (_root_.Vehicle_lib.Copter.mode_from_mode_num.pure' this mode)

/-- `ModeAltHold.name` as a pure function of its arguments (it reads and writes no memory). -/
def ModeAltHold.name.pure' (this : UInt64) : Id UInt64 := do
  return (0x14908 : UInt64) /- "Altitude Hold" -/

/-- C++ `ModeAltHold::name : const char *() const`, `mode.h:524-?`. -/
def ModeAltHold.name (this : UInt64) : PMem.M UInt64 :=
  pure (_root_.Vehicle_lib.ModeAltHold.name.pure' this)

/-- C++ `ModeAuto::name : const char *() const`, `functor.h:637-?`. -/
def ModeAuto.name (this : UInt64) : PMem.M UInt64 := do
  let t'1 ← PMem.ldB (this + 861)
  let mut c'2 : UInt64 := default
  if t'1 then
    c'2 := (0x14019 : UInt64) /- "Auto RTL" -/
  else
    c'2 := (0x14022 : UInt64) /- "Auto" -/
  return c'2

/-- `ModeBrake.name` as a pure function of its arguments (it reads and writes no memory). -/
def ModeBrake.name.pure' (this : UInt64) : Id UInt64 := do
  return (0x14ae0 : UInt64) /- "Brake" -/

/-- C++ `ModeBrake::name : const char *() const`, `mode.h:896-?`. -/
def ModeBrake.name (this : UInt64) : PMem.M UInt64 :=
  pure (_root_.Vehicle_lib.ModeBrake.name.pure' this)

/-- `ModeCircle.name` as a pure function of its arguments (it reads and writes no memory). -/
def ModeCircle.name.pure' (this : UInt64) : Id UInt64 := do
  return (0x14aeb : UInt64) /- "Circle" -/

/-- C++ `ModeCircle::name : const char *() const`, `mode.h:924-?`. -/
def ModeCircle.name (this : UInt64) : PMem.M UInt64 :=
  pure (_root_.Vehicle_lib.ModeCircle.name.pure' this)

/-- `ModeGuided.name` as a pure function of its arguments (it reads and writes no memory). -/
def ModeGuided.name.pure' (this : UInt64) : Id UInt64 := do
  return (0x14af7 : UInt64) /- "Guided" -/

/-- C++ `ModeGuided::name : const char *() const`, `mode.h:1206-?`. -/
def ModeGuided.name (this : UInt64) : PMem.M UInt64 :=
  pure (_root_.Vehicle_lib.ModeGuided.name.pure' this)

/-- `ModeLand.name` as a pure function of its arguments (it reads and writes no memory). -/
def ModeLand.name.pure' (this : UInt64) : Id UInt64 := do
  return (0x14b4c : UInt64) /- "Land" -/

/-- C++ `ModeLand::name : const char *() const`, `mode.h:1347-?`. -/
def ModeLand.name (this : UInt64) : PMem.M UInt64 :=
  pure (_root_.Vehicle_lib.ModeLand.name.pure' this)

/-- `ModeLoiter.name` as a pure function of its arguments (it reads and writes no memory). -/
def ModeLoiter.name.pure' (this : UInt64) : Id UInt64 := do
  return (0x14b56 : UInt64) /- "Loiter" -/

/-- C++ `ModeLoiter::name : const char *() const`, `mode.h:1395-?`. -/
def ModeLoiter.name (this : UInt64) : PMem.M UInt64 :=
  pure (_root_.Vehicle_lib.ModeLoiter.name.pure' this)

/-- `ModeRTL.name` as a pure function of its arguments (it reads and writes no memory). -/
def ModeRTL.name.pure' (this : UInt64) : Id UInt64 := do
  return (0x14c9a : UInt64) /- "RTL" -/

/-- C++ `ModeRTL::name : const char *() const`, `mode.h:1585-?`. -/
def ModeRTL.name (this : UInt64) : PMem.M UInt64 :=
  pure (_root_.Vehicle_lib.ModeRTL.name.pure' this)

/-- `ModeStabilize.name` as a pure function of its arguments (it reads and writes no memory). -/
def ModeStabilize.name.pure' (this : UInt64) : Id UInt64 := do
  return (0x14ca3 : UInt64) /- "Stabilize" -/

/-- C++ `ModeStabilize::name : const char *() const`, `mode.h:1768-?`. -/
def ModeStabilize.name (this : UInt64) : PMem.M UInt64 :=
  pure (_root_.Vehicle_lib.ModeStabilize.name.pure' this)

/-- `RC_Channels_Copter.channel` as a pure function of its arguments (it reads and writes no memory). -/
def RC_Channels_Copter.channel.pure' (this : UInt64) (chan : UInt8) : Id UInt64 := do
  let mut chan := chan
  if (decide ((UInt8.toUInt64 (chan)) ≥ ((896 : UInt64) / (56 : UInt64)))) then
    return (0 : UInt64)
  return ((this + 48) + ((UInt64.toInt64 (UInt8.toUInt64 (chan))) * 56).toUInt64)

/-- C++ `RC_Channels_Copter::channel : RC_Channel_Copter *(const uint8_t)`, `RC_Channel_Copter.h:39-44`. -/
def RC_Channels_Copter.channel (this : UInt64) (chan : UInt8) : PMem.M UInt64 :=
  pure (_root_.Vehicle_lib.RC_Channels_Copter.channel.pure' this chan)

/-- C++ `Copter::init_simple_bearing : void ()`, `Copter.cpp:836-853`. -/
def Copter.init_simple_bearing (this : UInt64) : PMem.M Unit := do
  let t'1 ← VehicleBridge.AP_AHRS.cos_yaw'0 (this + 4080)
  PMem.stF32 (this + 9556) t'1
  let t'2 ← VehicleBridge.AP_AHRS.sin_yaw'0 (this + 4080)
  PMem.stF32 (this + 9560) t'2
  let t'3 ← VehicleBridge.AP_AHRS.get_yaw_rad'0 (this + 4080)
  let t'4 ← radians (Binary64.toBinary32 ((Binary64.ofBits 0x4066800000000000 /- 180 -/)))
  let t'5 ← wrap_2PI (t'3 + t'4)
  PMem.stF32 (this + 9564) t'5
  let t'6 ← PMem.ldF32 (this + 9556)
  PMem.stF32 (this + 9568) t'6
  let t'7 ← PMem.ldF32 (this + 9560)
  PMem.stF32 (this + 9572) t'7
  return ()

/-- C++ `RC_Channels_Copter::flight_mode_channel_number : int8_t () const`, `RC_Channel_Copter.cpp:12-15`. -/
def RC_Channels_Copter.flight_mode_channel_number (this : UInt64) : PMem.M Int8 := do
  let t'1 ← AP_ParamTBase'signed_char_1.get (((0x86d8 : UInt64) /- &copter -/ + 6776) + 39)
  let t'2 ← PMem.ldI8 t'1
  return t'2

/-- C++ `RC_Channels_Copter::in_rc_failsafe : bool () const`, `RC_Channel_Copter.cpp:40-43`. -/
def RC_Channels_Copter.in_rc_failsafe (this : UInt64) : PMem.M Bool := do
  let t'1 ← PMem.ldBits ((0x86d8 : UInt64) /- &copter -/ + 9508) 72 1
  return (UInt64.toUInt8 (t'1)) != (0 : UInt8)

/-- C++ `RC_Channels_Copter::has_valid_input : bool () const`, `RC_Channel_Copter.cpp:45-54`. -/
def RC_Channels_Copter.has_valid_input (this : UInt64) : PMem.M Bool := do
  let t'1 ← RC_Channels_Copter.in_rc_failsafe this
  if t'1 then
    return false
  let t'2 ← PMem.ldI8 (((0x86d8 : UInt64) /- &copter -/ + 9508) + 8)
  if ((Int8.toInt32 (t'2)) != (0 : Int32)) then
    return false
  let t'3 ← RC_Channels.has_valid_input this
  return t'3

/-- C++ `Mode::apply_simple_mode : void (float &, float &) const`, `mode.cpp:1106-1128`. -/
def Mode.apply_simple_mode (this : UInt64) (roll : UInt64) (pitch : UInt64) : PMem.M Unit := do
  let t'1 ← PMem.ldI32 ((0x86d8 : UInt64) /- &copter -/ + 9552)
  if (t'1 == (0 : Int32)) then
    return ()
  let mut roll_out : Binary32 := default  -- uninitialized in C
  let mut pitch_out : Binary32 := default  -- uninitialized in C
  let t'2 ← PMem.ldI32 ((0x86d8 : UInt64) /- &copter -/ + 9552)
  if (t'2 == (1 : Int32)) then
    let t'3 ← PMem.ldF32 roll
    let t'4 ← PMem.ldF32 ((0x86d8 : UInt64) /- &copter -/ + 9556)
    let t'5 ← PMem.ldF32 pitch
    let t'6 ← PMem.ldF32 ((0x86d8 : UInt64) /- &copter -/ + 9560)
    let t'7 := ((t'3 * t'4) - (t'5 * t'6))
    roll_out := t'7
    let t'8 ← PMem.ldF32 roll
    let t'9 ← PMem.ldF32 ((0x86d8 : UInt64) /- &copter -/ + 9560)
    let t'10 ← PMem.ldF32 pitch
    let t'11 ← PMem.ldF32 ((0x86d8 : UInt64) /- &copter -/ + 9556)
    let t'12 := ((t'8 * t'9) + (t'10 * t'11))
    pitch_out := t'12
  else
    let t'13 ← PMem.ldF32 roll
    let t'14 ← PMem.ldF32 ((0x86d8 : UInt64) /- &copter -/ + 9568)
    let t'15 ← PMem.ldF32 pitch
    let t'16 ← PMem.ldF32 ((0x86d8 : UInt64) /- &copter -/ + 9572)
    let t'17 := ((t'13 * t'14) - (t'15 * t'16))
    roll_out := t'17
    let t'18 ← PMem.ldF32 roll
    let t'19 ← PMem.ldF32 ((0x86d8 : UInt64) /- &copter -/ + 9572)
    let t'20 ← PMem.ldF32 pitch
    let t'21 ← PMem.ldF32 ((0x86d8 : UInt64) /- &copter -/ + 9568)
    let t'22 := ((t'18 * t'19) + (t'20 * t'21))
    pitch_out := t'22
  let t'23 ← VehicleBridge.AP_AHRS.cos_yaw'0 ((0x86d8 : UInt64) /- &copter -/ + 4080)
  let t'24 ← VehicleBridge.AP_AHRS.sin_yaw'0 ((0x86d8 : UInt64) /- &copter -/ + 4080)
  let t'25 := ((roll_out * t'23) + (pitch_out * t'24))
  PMem.stF32 roll t'25
  let t'26 ← VehicleBridge.AP_AHRS.sin_yaw'0 ((0x86d8 : UInt64) /- &copter -/ + 4080)
  let t'27 ← VehicleBridge.AP_AHRS.cos_yaw'0 ((0x86d8 : UInt64) /- &copter -/ + 4080)
  let t'28 := (((-roll_out) * t'26) + (pitch_out * t'27))
  PMem.stF32 pitch t'28
  return ()

/-- C++ `Mode::get_pilot_desired_lean_angles_rad : void (float &, float &, float, float) const`, `mode.cpp:557-575`. -/
def Mode.get_pilot_desired_lean_angles_rad.body (fp : UInt64) (this : UInt64) (roll_out_rad : UInt64) (pitch_out_rad : UInt64) (angle_max_rad : Binary32) (angle_limit_rad : Binary32) : PMem.M Unit := do
  let mut angle_max_rad := angle_max_rad
  let mut angle_limit_rad := angle_limit_rad
  let t'1 ← rc
  let t'2 ← RC_Channels_Copter.has_valid_input t'1
  if !t'2 then
    let t'3 := Binary64.toBinary32 ((Binary64.ofBits 0x0000000000000000 /- 0 -/))
    PMem.stF32 roll_out_rad t'3
    let t'4 := Binary64.toBinary32 ((Binary64.ofBits 0x0000000000000000 /- 0 -/))
    PMem.stF32 pitch_out_rad t'4
    return ()
  let t'5 ← PMem.ldU64 (this + 72)
  let t'6 ← PMem.ldU64 t'5
  let t'7 ← RC_Channel.norm_input_dz t'6
  PMem.stF32 (fp + 0) t'7
  let t'8 ← PMem.ldU64 (this + 80)
  let t'9 ← PMem.ldU64 t'8
  let t'10 ← RC_Channel.norm_input_dz t'9
  PMem.stF32 (fp + 8) t'10
  Mode.apply_simple_mode this (fp + 0) (fp + 8)
  let t'11 ← PMem.ldF32 (fp + 0)
  let t'12 ← PMem.ldF32 (fp + 8)
  rc_input_to_roll_pitch_rad t'11 t'12 angle_max_rad angle_limit_rad roll_out_rad pitch_out_rad
  return ()

def Mode.get_pilot_desired_lean_angles_rad (this : UInt64) (roll_out_rad : UInt64) (pitch_out_rad : UInt64) (angle_max_rad : Binary32) (angle_limit_rad : Binary32) : PMem.M Unit := do
  let fp ← PMem.enter 12
  let r ← Mode.get_pilot_desired_lean_angles_rad.body fp this roll_out_rad pitch_out_rad angle_max_rad angle_limit_rad
  PMem.leave fp
  return r

/-- C++ `RC_Channel_Copter::do_aux_function_change_air_mode : void (const AuxSwitchPos)`, `RC_Channel_Copter.cpp:704-716`. -/
def RC_Channel_Copter.do_aux_function_change_air_mode (this : UInt64) (ch_flag : UInt8) : PMem.M Unit := do
  let mut ch_flag := ch_flag
  let sw'1 := ch_flag
  if sw'1 == (2 : UInt8) then
    PMem.stI32 ((0x86d8 : UInt64) /- &copter -/ + 9476) (2 : Int32)
  else if sw'1 == (1 : UInt8) then
    pure ()
  else if sw'1 == (0 : UInt8) then
    PMem.stI32 ((0x86d8 : UInt64) /- &copter -/ + 9476) (1 : Int32)
  else
    pure ()
  return ()

/-- C++ `RC_Channel_Copter::do_aux_function_change_force_flying : void (const AuxSwitchPos)`, `RC_Channel_Copter.cpp:719-731`. -/
def RC_Channel_Copter.do_aux_function_change_force_flying (this : UInt64) (ch_flag : UInt8) : PMem.M Unit := do
  let mut ch_flag := ch_flag
  let sw'1 := ch_flag
  if sw'1 == (2 : UInt8) then
    PMem.stB ((0x86d8 : UInt64) /- &copter -/ + 9480) true
  else if sw'1 == (1 : UInt8) then
    pure ()
  else if sw'1 == (0 : UInt8) then
    PMem.stB ((0x86d8 : UInt64) /- &copter -/ + 9480) false
  else
    pure ()
  return ()

/-- `ModeAltHold.allows_arming` as a pure function of its arguments (it reads and writes no memory). -/
def ModeAltHold.allows_arming.pure' (this : UInt64) (method : Int32) : Id Bool := do
  let mut method := method
  return true

/-- C++ `ModeAltHold::allows_arming : bool (AP_Arming::Method) const`, `mode.h:510-?`. -/
def ModeAltHold.allows_arming (this : UInt64) (method : Int32) : PMem.M Bool :=
  pure (_root_.Vehicle_lib.ModeAltHold.allows_arming.pure' this method)

/-- C++ `ModeAuto::option_is_enabled : bool (Option) const`, `mode_auto.cpp:214-217`. -/
def ModeAuto.option_is_enabled (this : UInt64) (option : Int32) : PMem.M Bool := do
  let mut option := option
  let t'1 ← AP_ParamT'unsigned_int_3.operator_const_unsigned_int__ (((0x86d8 : UInt64) /- &copter -/ + 6840) + 1680)
  let t'2 ← PMem.ldU32 t'1
  return ((t'2 &&& (Int32.toUInt32 (option))) != (Int32.toUInt32 ((0 : Int32))))

/-- C++ `ModeAuto::allows_arming : bool (AP_Arming::Method) const`, `mode_auto.cpp:219-225`. -/
def ModeAuto.allows_arming (this : UInt64) (method : Int32) : PMem.M Bool := do
  let mut method := method
  let t'1 ← PMem.ldB (this + 861)
  if t'1 then
    return false
  let t'2 ← ModeAuto.option_is_enabled this (1 : Int32)
  return t'2

/-- `ModeBrake.allows_arming` as a pure function of its arguments (it reads and writes no memory). -/
def ModeBrake.allows_arming.pure' (this : UInt64) (method : Int32) : Id Bool := do
  let mut method := method
  return false

/-- C++ `ModeBrake::allows_arming : bool (AP_Arming::Method) const`, `mode.h:889-?`. -/
def ModeBrake.allows_arming (this : UInt64) (method : Int32) : PMem.M Bool :=
  pure (_root_.Vehicle_lib.ModeBrake.allows_arming.pure' this method)

/-- `ModeCircle.allows_arming` as a pure function of its arguments (it reads and writes no memory). -/
def ModeCircle.allows_arming.pure' (this : UInt64) (method : Int32) : Id Bool := do
  let mut method := method
  return false

/-- C++ `ModeCircle::allows_arming : bool (AP_Arming::Method) const`, `mode.h:919-?`. -/
def ModeCircle.allows_arming (this : UInt64) (method : Int32) : PMem.M Bool :=
  pure (_root_.Vehicle_lib.ModeCircle.allows_arming.pure' this method)

/-- C++ `ModeGuided::allows_arming : bool (AP_Arming::Method) const`, `mode_guided.cpp:118-127`. -/
def ModeGuided.allows_arming (this : UInt64) (method : Int32) : PMem.M Bool := do
  let mut method := method
  let t'1 ← AP_Arming.method_is_GCS method
  if (t'1 || (method == (4 : Int32))) then
    return true
  let t'2 ← ModeGuided.option_is_enabled this (1 : UInt32)
  return t'2

/-- `ModeLand.allows_arming` as a pure function of its arguments (it reads and writes no memory). -/
def ModeLand.allows_arming.pure' (this : UInt64) (method : Int32) : Id Bool := do
  let mut method := method
  return false

/-- C++ `ModeLand::allows_arming : bool (AP_Arming::Method) const`, `mode.h:1317-?`. -/
def ModeLand.allows_arming (this : UInt64) (method : Int32) : PMem.M Bool :=
  pure (_root_.Vehicle_lib.ModeLand.allows_arming.pure' this method)

/-- `ModeLoiter.allows_arming` as a pure function of its arguments (it reads and writes no memory). -/
def ModeLoiter.allows_arming.pure' (this : UInt64) (method : Int32) : Id Bool := do
  let mut method := method
  return true

/-- C++ `ModeLoiter::allows_arming : bool (AP_Arming::Method) const`, `mode.h:1379-?`. -/
def ModeLoiter.allows_arming (this : UInt64) (method : Int32) : PMem.M Bool :=
  pure (_root_.Vehicle_lib.ModeLoiter.allows_arming.pure' this method)

/-- `ModeRTL.allows_arming` as a pure function of its arguments (it reads and writes no memory). -/
def ModeRTL.allows_arming.pure' (this : UInt64) (method : Int32) : Id Bool := do
  let mut method := method
  return false

/-- C++ `ModeRTL::allows_arming : bool (AP_Arming::Method) const`, `mode.h:1526-?`. -/
def ModeRTL.allows_arming (this : UInt64) (method : Int32) : PMem.M Bool :=
  pure (_root_.Vehicle_lib.ModeRTL.allows_arming.pure' this method)

/-- `ModeStabilize.allows_arming` as a pure function of its arguments (it reads and writes no memory). -/
def ModeStabilize.allows_arming.pure' (this : UInt64) (method : Int32) : Id Bool := do
  let mut method := method
  return true

/-- C++ `ModeStabilize::allows_arming : bool (AP_Arming::Method) const`, `mode.h:1758-?`. -/
def ModeStabilize.allows_arming (this : UInt64) (method : Int32) : PMem.M Bool :=
  pure (_root_.Vehicle_lib.ModeStabilize.allows_arming.pure' this method)

/-- `ModeAltHold.has_manual_throttle` as a pure function of its arguments (it reads and writes no memory). -/
def ModeAltHold.has_manual_throttle.pure' (this : UInt64) : Id Bool := do
  return false

/-- C++ `ModeAltHold::has_manual_throttle : bool () const`, `mode.h:509-?`. -/
def ModeAltHold.has_manual_throttle (this : UInt64) : PMem.M Bool :=
  pure (_root_.Vehicle_lib.ModeAltHold.has_manual_throttle.pure' this)

/-- `ModeAuto.has_manual_throttle` as a pure function of its arguments (it reads and writes no memory). -/
def ModeAuto.has_manual_throttle.pure' (this : UInt64) : Id Bool := do
  return false

/-- C++ `ModeAuto::has_manual_throttle : bool () const`, `mode.h:546-?`. -/
def ModeAuto.has_manual_throttle (this : UInt64) : PMem.M Bool :=
  pure (_root_.Vehicle_lib.ModeAuto.has_manual_throttle.pure' this)

/-- `ModeBrake.has_manual_throttle` as a pure function of its arguments (it reads and writes no memory). -/
def ModeBrake.has_manual_throttle.pure' (this : UInt64) : Id Bool := do
  return false

/-- C++ `ModeBrake::has_manual_throttle : bool () const`, `mode.h:888-?`. -/
def ModeBrake.has_manual_throttle (this : UInt64) : PMem.M Bool :=
  pure (_root_.Vehicle_lib.ModeBrake.has_manual_throttle.pure' this)

/-- `ModeCircle.has_manual_throttle` as a pure function of its arguments (it reads and writes no memory). -/
def ModeCircle.has_manual_throttle.pure' (this : UInt64) : Id Bool := do
  return false

/-- C++ `ModeCircle::has_manual_throttle : bool () const`, `mode.h:918-?`. -/
def ModeCircle.has_manual_throttle (this : UInt64) : PMem.M Bool :=
  pure (_root_.Vehicle_lib.ModeCircle.has_manual_throttle.pure' this)

/-- `ModeGuided.has_manual_throttle` as a pure function of its arguments (it reads and writes no memory). -/
def ModeGuided.has_manual_throttle.pure' (this : UInt64) : Id Bool := do
  return false

/-- C++ `ModeGuided::has_manual_throttle : bool () const`, `mode.h:1121-?`. -/
def ModeGuided.has_manual_throttle (this : UInt64) : PMem.M Bool :=
  pure (_root_.Vehicle_lib.ModeGuided.has_manual_throttle.pure' this)

/-- `ModeLand.has_manual_throttle` as a pure function of its arguments (it reads and writes no memory). -/
def ModeLand.has_manual_throttle.pure' (this : UInt64) : Id Bool := do
  return false

/-- C++ `ModeLand::has_manual_throttle : bool () const`, `mode.h:1316-?`. -/
def ModeLand.has_manual_throttle (this : UInt64) : PMem.M Bool :=
  pure (_root_.Vehicle_lib.ModeLand.has_manual_throttle.pure' this)

/-- `ModeLoiter.has_manual_throttle` as a pure function of its arguments (it reads and writes no memory). -/
def ModeLoiter.has_manual_throttle.pure' (this : UInt64) : Id Bool := do
  return false

/-- C++ `ModeLoiter::has_manual_throttle : bool () const`, `mode.h:1378-?`. -/
def ModeLoiter.has_manual_throttle (this : UInt64) : PMem.M Bool :=
  pure (_root_.Vehicle_lib.ModeLoiter.has_manual_throttle.pure' this)

/-- `ModeRTL.has_manual_throttle` as a pure function of its arguments (it reads and writes no memory). -/
def ModeRTL.has_manual_throttle.pure' (this : UInt64) : Id Bool := do
  return false

/-- C++ `ModeRTL::has_manual_throttle : bool () const`, `mode.h:1525-?`. -/
def ModeRTL.has_manual_throttle (this : UInt64) : PMem.M Bool :=
  pure (_root_.Vehicle_lib.ModeRTL.has_manual_throttle.pure' this)

/-- `ModeStabilize.has_manual_throttle` as a pure function of its arguments (it reads and writes no memory). -/
def ModeStabilize.has_manual_throttle.pure' (this : UInt64) : Id Bool := do
  return true

/-- C++ `ModeStabilize::has_manual_throttle : bool () const`, `mode.h:1757-?`. -/
def ModeStabilize.has_manual_throttle (this : UInt64) : PMem.M Bool :=
  pure (_root_.Vehicle_lib.ModeStabilize.has_manual_throttle.pure' this)

/-- C++ `Copter::set_land_complete_maybe : void (bool)`, `land_detector.cpp:266-276`. -/
def Copter.set_land_complete_maybe (this : UInt64) (b : Bool) : PMem.M Unit := do
  let mut b := b
  let t'1 ← PMem.ldB ((this + 9448) + 14)
  if ((if t'1 then (1 : Int32) else (0 : Int32)) == (if b then (1 : Int32) else (0 : Int32))) then
    return ()
  if b then
    pure ()
  PMem.stB ((this + 9448) + 14) b
  return ()

/-- C++ `Copter::failsafe_enable : void ()`, `failsafe.cpp:18-22`. -/
def Copter.failsafe_enable (this : UInt64) : PMem.M Unit := do
  PMem.stB (0xce28 : UInt64) /- &failsafe_enabled -/ true
  let t'1 := (← PMem.clock).toUInt32
  PMem.stU32 (0xce30 : UInt64) /- &failsafe_last_timestamp -/ t'1
  return ()

/-- `ModeAltHold.requires_position` as a pure function of its arguments (it reads and writes no memory). -/
def ModeAltHold.requires_position.pure' (this : UInt64) : Id Bool := do
  return false

/-- C++ `ModeAltHold::requires_position : bool () const`, `mode.h:508-?`. -/
def ModeAltHold.requires_position (this : UInt64) : PMem.M Bool :=
  pure (_root_.Vehicle_lib.ModeAltHold.requires_position.pure' this)

/-- C++ `ModeAuto::requires_position : bool () const`, `mode_auto.cpp:187-191`. -/
def ModeAuto.requires_position (this : UInt64) : PMem.M Bool := do
  let t'1 ← PMem.ldU8 (this + 820)
  return (t'1 != (11 : UInt8))

/-- `ModeBrake.requires_position` as a pure function of its arguments (it reads and writes no memory). -/
def ModeBrake.requires_position.pure' (this : UInt64) : Id Bool := do
  return true

/-- C++ `ModeBrake::requires_position : bool () const`, `mode.h:887-?`. -/
def ModeBrake.requires_position (this : UInt64) : PMem.M Bool :=
  pure (_root_.Vehicle_lib.ModeBrake.requires_position.pure' this)

/-- `ModeCircle.requires_position` as a pure function of its arguments (it reads and writes no memory). -/
def ModeCircle.requires_position.pure' (this : UInt64) : Id Bool := do
  return true

/-- C++ `ModeCircle::requires_position : bool () const`, `mode.h:917-?`. -/
def ModeCircle.requires_position (this : UInt64) : PMem.M Bool :=
  pure (_root_.Vehicle_lib.ModeCircle.requires_position.pure' this)

/-- `ModeGuided.requires_position` as a pure function of its arguments (it reads and writes no memory). -/
def ModeGuided.requires_position.pure' (this : UInt64) : Id Bool := do
  return true

/-- C++ `ModeGuided::requires_position : bool () const`, `mode.h:1120-?`. -/
def ModeGuided.requires_position (this : UInt64) : PMem.M Bool :=
  pure (_root_.Vehicle_lib.ModeGuided.requires_position.pure' this)

/-- `ModeLand.requires_position` as a pure function of its arguments (it reads and writes no memory). -/
def ModeLand.requires_position.pure' (this : UInt64) : Id Bool := do
  return false

/-- C++ `ModeLand::requires_position : bool () const`, `mode.h:1315-?`. -/
def ModeLand.requires_position (this : UInt64) : PMem.M Bool :=
  pure (_root_.Vehicle_lib.ModeLand.requires_position.pure' this)

/-- `ModeLoiter.requires_position` as a pure function of its arguments (it reads and writes no memory). -/
def ModeLoiter.requires_position.pure' (this : UInt64) : Id Bool := do
  return true

/-- C++ `ModeLoiter::requires_position : bool () const`, `mode.h:1377-?`. -/
def ModeLoiter.requires_position (this : UInt64) : PMem.M Bool :=
  pure (_root_.Vehicle_lib.ModeLoiter.requires_position.pure' this)

/-- `ModeRTL.requires_position` as a pure function of its arguments (it reads and writes no memory). -/
def ModeRTL.requires_position.pure' (this : UInt64) : Id Bool := do
  return true

/-- C++ `ModeRTL::requires_position : bool () const`, `mode.h:1524-?`. -/
def ModeRTL.requires_position (this : UInt64) : PMem.M Bool :=
  pure (_root_.Vehicle_lib.ModeRTL.requires_position.pure' this)

/-- `ModeStabilize.requires_position` as a pure function of its arguments (it reads and writes no memory). -/
def ModeStabilize.requires_position.pure' (this : UInt64) : Id Bool := do
  return false

/-- C++ `ModeStabilize::requires_position : bool () const`, `mode.h:1756-?`. -/
def ModeStabilize.requires_position (this : UInt64) : PMem.M Bool :=
  pure (_root_.Vehicle_lib.ModeStabilize.requires_position.pure' this)

/-- C++ `Copter::ekf_alt_ok : bool () const`, `system.cpp:294-309`. -/
def Copter.ekf_alt_ok (this : UInt64) : PMem.M Bool := do
  let t'1 ← VehicleBridge.AP_AHRS.have_inertial_nav'0 (this + 4080)
  if !t'1 then
    return false
  let t'2 ← VehicleBridge.AP_AHRS.configured_backend_has_status'1 (this + 4080) (32 : Int32)
  if !t'2 then
    return false
  let t'3 ← VehicleBridge.AP_AHRS.configured_backend_has_status'1 (this + 4080) (4 : Int32)
  if !t'3 then
    return false
  return true

/-- C++ `ModeRTL::get_alt_type : ModeRTL::RTLAltType () const`, `mode_rtl.cpp:119-128`. -/
def ModeRTL.get_alt_type (this : UInt64) : PMem.M Int8 := do
  let t'1 ← PMem.ldU64 (this + 8)
  let t'2 ← AP_Enum'ModeRTL_RTLAltType.operator_const_ModeRTL.RTLAltType (t'1 + 20)
  let sw'3 := t'2
  if (decide ((0 : Int8) ≤ sw'3) && decide (sw'3 ≤ (1 : Int8))) then
    let t'4 ← PMem.ldU64 (this + 8)
    let t'5 ← AP_Enum'ModeRTL_RTLAltType.operator_const_ModeRTL.RTLAltType (t'4 + 20)
    return t'5
  else
    pure ()
  return (0 : Int8)

/-- `AP_Arming_Copter.oa_checks` as a pure function of its arguments (it reads and writes no memory). -/
def AP_Arming_Copter.oa_checks.pure' (this : UInt64) (display_failure : Bool) : Id Bool := do
  let mut display_failure := display_failure
  return true

/-- C++ `AP_Arming_Copter::oa_checks : bool (bool)`, `AP_Arming_Copter.cpp:319-336`. -/
def AP_Arming_Copter.oa_checks (this : UInt64) (display_failure : Bool) : PMem.M Bool :=
  pure (_root_.Vehicle_lib.AP_Arming_Copter.oa_checks.pure' this display_failure)

/-- `AP_Arming_Copter.winch_checks` as a pure function of its arguments (it reads and writes no memory). -/
def AP_Arming_Copter.winch_checks.pure' (this : UInt64) (display_failure : Bool) : Id Bool := do
  let mut display_failure := display_failure
  return true

/-- C++ `AP_Arming_Copter::winch_checks : bool (bool) const`, `AP_Arming_Copter.cpp:529-548`. -/
def AP_Arming_Copter.winch_checks (this : UInt64) (display_failure : Bool) : PMem.M Bool :=
  pure (_root_.Vehicle_lib.AP_Arming_Copter.winch_checks.pure' this display_failure)

/-- C++ `AP_Arming_Copter::pre_arm_ekf_attitude_check : bool ()`, `AP_Arming_Copter.cpp:407-410`. -/
def AP_Arming_Copter.pre_arm_ekf_attitude_check (this : UInt64) : PMem.M Bool := do
  let t'1 ← VehicleBridge.ahrs'0
  let t'2 ← VehicleBridge.AP_AHRS.configured_backend_has_status'1 t'1 (1 : Int32)
  return t'2

/-- C++ `Copter::current_mode_requires_mission : bool () const`, `Copter.cpp:574-581`. -/
def Copter.current_mode_requires_mission (this : UInt64) : PMem.M Bool := do
  let t'1 ← PMem.ldU64 (this + 9488)
  return (t'1 == (this + 11368))

/-- C++ `AP_Arming_Copter::set_pre_arm_check : void (bool)`, `AP_Arming_Copter.cpp:668-672`. -/
def AP_Arming_Copter.set_pre_arm_check (this : UInt64) (b : Bool) : PMem.M Unit := do
  let mut b := b
  PMem.stB (((0x86d8 : UInt64) /- &copter -/ + 9448) + 4) b
  PMem.stB ((0xccc0 : UInt64) /- &AP_Notify::flags -/ + 6) b
  return ()

/-- C++ `Copter::get_throttle_mid : int16_t ()`, `radio.cpp:209-217`. -/
def Copter.get_throttle_mid (this : UInt64) : PMem.M Int16 := do
  let t'1 ← PMem.ldU64 (this + 8616)
  let t'2 ← RC_Channel.get_control_mid t'1
  return t'2

/-- C++ `Copter::get_pilot_speed_up_adjusted_ms : float () const`, `Attitude.cpp:144-150`. -/
def Copter.get_pilot_speed_up_adjusted_ms.body (fp : UInt64) (this : UInt64) : PMem.M Binary32 := do
  let t'1 ← PMem.ldU64 (this + 11184)
  let t'2 ← AC_PosControl.get_vel_terrain_D_ms t'1
  let mut terrain_climb_ms : Binary32 := -t'2
  PMem.stF32 (fp + 0) (Binary32.ofBits 0x00000000 /- 0 -/)
  let t'3 ← AP_ParamT'float_4.operator_const_float__'1 ((this + 6840) + 1636)
  let t'4 ← PMem.ldF32 t'3
  PMem.stF32 (fp + 4) (t'4 - terrain_climb_ms)
  let t'5 ← MAX'float_float (fp + 0) (fp + 4)
  let t'6 ← PMem.ldF32 t'5
  return t'6

def Copter.get_pilot_speed_up_adjusted_ms (this : UInt64) : PMem.M Binary32 := do
  let fp ← PMem.enter 8
  let r ← Copter.get_pilot_speed_up_adjusted_ms.body fp this
  PMem.leave fp
  return r

/-- C++ `RC_Channels_Copter::get_arming_channel : RC_Channel *() const`, `RC_Channel_Copter.cpp:66-69`. -/
def RC_Channels_Copter.get_arming_channel (this : UInt64) : PMem.M UInt64 := do
  let t'1 ← PMem.ldU64 ((0x86d8 : UInt64) /- &copter -/ + 8624)
  return t'1

/-- C++ `RC_Channels_Copter::arming_check_throttle : bool () const`, `RC_Channel_Copter.cpp:57-64`. -/
def RC_Channels_Copter.arming_check_throttle (this : UInt64) : PMem.M Bool := do
  let t'1 ← AP_ParamT'unsigned_short_2.operator_const_unsigned_short__ (((0x86d8 : UInt64) /- &copter -/ + 6776) + 8)
  let t'2 ← PMem.ldU16 t'1
  if (((UInt32.toInt32 (UInt16.toUInt32 (t'2))) &&& ((1 : Int32) <<< (0 : Int32))) != (0 : Int32)) then
    return false
  let t'3 ← RC_Channels.arming_check_throttle this
  return t'3

/-- `Mode.allows_GCS_or_SCR_arming_with_throttle_high` as a pure function of its arguments (it reads and writes no memory). -/
def Mode.allows_GCS_or_SCR_arming_with_throttle_high.pure' (this : UInt64) : Id Bool := do
  return false

/-- C++ `Mode::allows_GCS_or_SCR_arming_with_throttle_high : bool () const`, `AP_Common.h:151-?`. -/
def Mode.allows_GCS_or_SCR_arming_with_throttle_high (this : UInt64) : PMem.M Bool :=
  pure (_root_.Vehicle_lib.Mode.allows_GCS_or_SCR_arming_with_throttle_high.pure' this)

/-- `ModeAuto.allows_GCS_or_SCR_arming_with_throttle_high` as a pure function of its arguments (it reads and writes no memory). -/
def ModeAuto.allows_GCS_or_SCR_arming_with_throttle_high.pure' (this : UInt64) : Id Bool := do
  return true

/-- C++ `ModeAuto::allows_GCS_or_SCR_arming_with_throttle_high : bool () const`, `mode.h:561-?`. -/
def ModeAuto.allows_GCS_or_SCR_arming_with_throttle_high (this : UInt64) : PMem.M Bool :=
  pure (_root_.Vehicle_lib.ModeAuto.allows_GCS_or_SCR_arming_with_throttle_high.pure' this)

/-- `ModeGuided.allows_GCS_or_SCR_arming_with_throttle_high` as a pure function of its arguments (it reads and writes no memory). -/
def ModeGuided.allows_GCS_or_SCR_arming_with_throttle_high.pure' (this : UInt64) : Id Bool := do
  return true

/-- C++ `ModeGuided::allows_GCS_or_SCR_arming_with_throttle_high : bool () const`, `mode.h:1136-?`. -/
def ModeGuided.allows_GCS_or_SCR_arming_with_throttle_high (this : UInt64) : PMem.M Bool :=
  pure (_root_.Vehicle_lib.ModeGuided.allows_GCS_or_SCR_arming_with_throttle_high.pure' this)

/-- C++ `Copter::failsafe_disable : void ()`, `failsafe.cpp:27-30`. -/
def Copter.failsafe_disable (this : UInt64) : PMem.M Unit := do
  PMem.stB (0xce28 : UInt64) /- &failsafe_enabled -/ false
  return ()

/-- `ModeAltHold.allows_save_trim` as a pure function of its arguments (it reads and writes no memory). -/
def ModeAltHold.allows_save_trim.pure' (this : UInt64) : Id Bool := do
  return true

/-- C++ `ModeAltHold::allows_save_trim : bool () const`, `mode.h:518-?`. -/
def ModeAltHold.allows_save_trim (this : UInt64) : PMem.M Bool :=
  pure (_root_.Vehicle_lib.ModeAltHold.allows_save_trim.pure' this)

/-- `Mode.allows_save_trim` as a pure function of its arguments (it reads and writes no memory). -/
def Mode.allows_save_trim.pure' (this : UInt64) : Id Bool := do
  return false

/-- C++ `Mode::allows_save_trim : bool () const`, `AP_Common.h:135-?`. -/
def Mode.allows_save_trim (this : UInt64) : PMem.M Bool :=
  pure (_root_.Vehicle_lib.Mode.allows_save_trim.pure' this)

/-- `ModeStabilize.allows_save_trim` as a pure function of its arguments (it reads and writes no memory). -/
def ModeStabilize.allows_save_trim.pure' (this : UInt64) : Id Bool := do
  return true

/-- C++ `ModeStabilize::allows_save_trim : bool () const`, `mode.h:1760-?`. -/
def ModeStabilize.allows_save_trim (this : UInt64) : PMem.M Bool :=
  pure (_root_.Vehicle_lib.ModeStabilize.allows_save_trim.pure' this)

/-- `Mode.pause` as a pure function of its arguments (it reads and writes no memory). -/
def Mode.pause.pure' (this : UInt64) : Id Bool := do
  return false

/-- C++ `Mode::pause : bool ()`, `AP_Common.h:200-?`. -/
def Mode.pause (this : UInt64) : PMem.M Bool :=
  pure (_root_.Vehicle_lib.Mode.pause.pure' this)

/-- C++ `ModeAuto::pause : bool ()`, `mode_auto.cpp:2427-2438`. -/
def ModeAuto.pause (this : UInt64) : PMem.M Bool := do
  let t'1 ← PMem.ldU8 (this + 820)
  let mut sc'3 := (t'1 == (2 : UInt8))
  if !sc'3 then
    let t'2 ← PMem.ldU8 (this + 820)
    sc'3 := (t'2 == (5 : UInt8))
  let mut sc'5 := sc'3
  if !sc'5 then
    let t'4 ← PMem.ldU8 (this + 820)
    sc'5 := (t'4 == (6 : UInt8))
  let mut wp_leg_active : Bool := sc'5
  let mut sc'9 := !wp_leg_active
  if !sc'9 then
    let t'6 ← PMem.ldU64 (this + 24)
    let t'7 ← PMem.ldU64 t'6
    let t'8 ← AC_WPNav.reached_wp_destination t'7
    sc'9 := t'8
  if sc'9 then
    return false
  let t'10 ← PMem.ldU64 (this + 24)
  let t'11 ← PMem.ldU64 t'10
  AC_WPNav.set_pause t'11
  return true

/-- C++ `ModeGuided::pause : bool ()`, `mode_guided.cpp:1208-1212`. -/
def ModeGuided.pause (this : UInt64) : PMem.M Bool := do
  PMem.stB (this + 117) true
  return true

/-- `Mode.resume` as a pure function of its arguments (it reads and writes no memory). -/
def Mode.resume.pure' (this : UInt64) : Id Bool := do
  return false

/-- C++ `Mode::resume : bool ()`, `AP_Common.h:201-?`. -/
def Mode.resume (this : UInt64) : PMem.M Bool :=
  pure (_root_.Vehicle_lib.Mode.resume.pure' this)

/-- C++ `ModeAuto::resume : bool ()`, `mode_auto.cpp:2441-2445`. -/
def ModeAuto.resume (this : UInt64) : PMem.M Bool := do
  let t'1 ← PMem.ldU64 (this + 24)
  let t'2 ← PMem.ldU64 t'1
  AC_WPNav.set_resume t'2
  return true

/-- C++ `ModeGuided::resume : bool ()`, `mode_guided.cpp:1215-1219`. -/
def ModeGuided.resume (this : UInt64) : PMem.M Bool := do
  PMem.stB (this + 117) false
  return true

/-- C++ `ModeLand::set_land_pause : void (bool)`, `mode.h:1331-?`. -/
def ModeLand.set_land_pause (this : UInt64) (new_value : Bool) : PMem.M Unit := do
  let mut new_value := new_value
  PMem.stB (this + 132) new_value
  return ()

/-- C++ `ModeLand::controlling_position : bool () const`, `mode.h:1329-?`. -/
def ModeLand.controlling_position (this : UInt64) : PMem.M Bool := do
  let t'1 ← PMem.ldB (this + 112)
  return t'1

/-- C++ `ModeLand::do_not_use_GPS : void ()`, `mode_land.cpp:198-201`. -/
def ModeLand.do_not_use_GPS (this : UInt64) : PMem.M Unit := do
  PMem.stB (this + 112) false
  return ()

/-- `Mode.gcs` as a pure function of its arguments (it reads and writes no memory). -/
def Mode.gcs.pure' (this : UInt64) : Id UInt64 := do
  let t'1 ← _root_.Vehicle_lib.Copter.gcs.pure' (0x86d8 : UInt64) /- &copter -/
  return t'1

/-- C++ `Mode::gcs : GCS_Copter &() const`, `mode.cpp:1143-1146`. -/
def Mode.gcs (this : UInt64) : PMem.M UInt64 :=
  pure (_root_.Vehicle_lib.Mode.gcs.pure' this)

/-- C++ `Mode::AutoYaw::mode : Mode () const`, `Copter.h:332-?`. -/
def Mode.AutoYaw.mode (this : UInt64) : PMem.M Int32 := do
  let t'1 ← PMem.ldI32 this
  return t'1

/-- C++ `_AutoTakeoff::get_completion_pos_ned_m : bool (Vector3p &)`, `takeoff.cpp:242-251`. -/
def _AutoTakeoff.get_completion_pos_ned_m (this : UInt64) (pos_ned_m : UInt64) : PMem.M Bool := do
  let t'1 ← PMem.ldB this
  if !t'1 then
    return false
  discard <| PMem.memcpy pos_ned_m (this + 16) 24
  discard <| pure (pos_ned_m)
  return true

/-- C++ `ModeGuided::limit_init_time_and_pos : void ()`, `mode_guided.cpp:1090-1097`. -/
def ModeGuided.limit_init_time_and_pos (this : UInt64) : PMem.M Unit := do
  let t'1 := ((← PMem.clock) / 1000).toUInt32
  PMem.stU32 ((0xedb8 : UInt64) /- &guided_limit -/ + 16) t'1
  let t'2 ← PMem.ldU64 (this + 40)
  let t'3 ← PMem.ldU64 t'2
  let t'4 ← AC_PosControl.get_pos_estimate_NED_m t'3
  discard <| PMem.memcpy ((0xedb8 : UInt64) /- &guided_limit -/ + 24) t'4 24
  discard <| pure (((0xedb8 : UInt64) /- &guided_limit -/ + 24))
  return ()

/-- C++ `ModeAuto::do_wait_delay : void (const AP_Mission::Mission_Command &)`, `mode_auto.cpp:1993-1997`. -/
def ModeAuto.do_wait_delay (this : UInt64) (cmd : UInt64) : PMem.M Unit := do
  let t'1 := ((← PMem.clock) / 1000).toUInt32
  PMem.stU32 (this + 852) t'1
  let t'2 ← PMem.ldF32 (cmd + 8)
  let t'3 := Binary32.toInt32 ((t'2 * (Int32.toBinary32 ((1000 : Int32)))))
  PMem.stI32 (this + 848) t'3
  return ()

/-- C++ `ModeAuto::do_within_distance : void (const AP_Mission::Mission_Command &)`, `mode_auto.cpp:1999-2002`. -/
def ModeAuto.do_within_distance (this : UInt64) (cmd : UInt64) : PMem.M Unit := do
  let t'1 ← PMem.ldF32 (cmd + 8)
  let t'2 := Binary32.toInt32 (t'1)
  PMem.stI32 (this + 848) t'2
  return ()

/-- C++ `ModeGuided::limit_set : void (uint32_t, float, float, float)`, `mode_guided.cpp:1080-1086`. -/
def ModeGuided.limit_set (this : UInt64) (timeout_ms : UInt32) (alt_min_m : Binary32) (alt_max_m : Binary32) (horiz_max_m : Binary32) : PMem.M Unit := do
  let mut timeout_ms := timeout_ms
  let mut alt_min_m := alt_min_m
  let mut alt_max_m := alt_max_m
  let mut horiz_max_m := horiz_max_m
  PMem.stU32 (0xedb8 : UInt64) /- &guided_limit -/ timeout_ms
  PMem.stF32 ((0xedb8 : UInt64) /- &guided_limit -/ + 4) alt_min_m
  PMem.stF32 ((0xedb8 : UInt64) /- &guided_limit -/ + 8) alt_max_m
  PMem.stF32 ((0xedb8 : UInt64) /- &guided_limit -/ + 12) horiz_max_m
  return ()

/-- C++ `ModeAuto::do_guided_limits : void (const AP_Mission::Mission_Command &)`, `mode_auto.cpp:1925-1932`. -/
def ModeAuto.do_guided_limits (this : UInt64) (cmd : UInt64) : PMem.M Unit := do
  let t'1 ← PMem.ldU16 (cmd + 4)
  let t'2 ← PMem.ldF32 (cmd + 8)
  let t'3 ← PMem.ldF32 ((cmd + 8) + 4)
  let t'4 ← PMem.ldF32 ((cmd + 8) + 8)
  ModeGuided.limit_set ((0x86d8 : UInt64) /- &copter -/ + 12520) (Int32.toUInt32 (((UInt32.toInt32 (UInt16.toUInt32 (t'1))) * (1000 : Int32)))) t'2 t'3 t'4
  return ()

/-- `Mode.exit` as a pure function of its arguments (it reads and writes no memory). -/
def Mode.exit.pure' (this : UInt64) : Id Unit := do
  return ()

/-- C++ `Mode::exit : void ()`, `AP_Common.h:126-?`. -/
def Mode.exit (this : UInt64) : PMem.M Unit :=
  pure (_root_.Vehicle_lib.Mode.exit.pure' this)

/-- C++ `ModeAuto::exit : void ()`, `mode_auto.cpp:77-87`. -/
def ModeAuto.exit (this : UInt64) : PMem.M Unit := do
  let t'1 ← AP_Mission.state (((0x86d8 : UInt64) /- &copter -/ + 11368) + 112)
  if ((UInt32.toInt32 (t'1)) == (UInt32.toInt32 ((1 : UInt32)))) then
    AP_Mission.stop (((0x86d8 : UInt64) /- &copter -/ + 11368) + 112)
  PMem.stB (this + 861) false
  return ()

/-- `Mode.allows_entry_in_rc_failsafe` as a pure function of its arguments (it reads and writes no memory). -/
def Mode.allows_entry_in_rc_failsafe.pure' (this : UInt64) : Id Bool := do
  return true

/-- C++ `Mode::allows_entry_in_rc_failsafe : bool () const`, `AP_Common.h:143-?`. -/
def Mode.allows_entry_in_rc_failsafe (this : UInt64) : PMem.M Bool :=
  pure (_root_.Vehicle_lib.Mode.allows_entry_in_rc_failsafe.pure' this)

/-- `ModeStabilize.allows_entry_in_rc_failsafe` as a pure function of its arguments (it reads and writes no memory). -/
def ModeStabilize.allows_entry_in_rc_failsafe.pure' (this : UInt64) : Id Bool := do
  return false

/-- C++ `ModeStabilize::allows_entry_in_rc_failsafe : bool () const`, `mode.h:1764-?`. -/
def ModeStabilize.allows_entry_in_rc_failsafe (this : UInt64) : PMem.M Bool :=
  pure (_root_.Vehicle_lib.ModeStabilize.allows_entry_in_rc_failsafe.pure' this)

/-- C++ `Mode::get_pilot_speed_up_ms : float () const`, `mode.cpp:1149-1152`. -/
def Mode.get_pilot_speed_up_ms (this : UInt64) : PMem.M Binary32 := do
  let t'1 ← PMem.ldU64 (this + 16)
  let t'2 ← AP_ParamT'float_4.operator_const_float__'1 (t'1 + 1636)
  let t'3 ← PMem.ldF32 t'2
  return t'3

/-- C++ `Mode::get_pilot_accel_D_mss : float () const`, `mode.cpp:1161-1164`. -/
def Mode.get_pilot_accel_D_mss (this : UInt64) : PMem.M Binary32 := do
  let t'1 ← PMem.ldU64 (this + 16)
  let t'2 ← AP_ParamT'float_4.operator_const_float__'1 (t'1 + 1632)
  let t'3 ← PMem.ldF32 t'2
  return t'3

/-- C++ `ModeGuided::limit_clear : void ()`, `mode_guided.cpp:1071-1077`. -/
def ModeGuided.limit_clear (this : UInt64) : PMem.M Unit := do
  let t'1 := Int32.toUInt32 ((0 : Int32))
  PMem.stU32 (0xedb8 : UInt64) /- &guided_limit -/ t'1
  let t'2 := (Binary32.ofBits 0x00000000 /- 0 -/)
  PMem.stF32 ((0xedb8 : UInt64) /- &guided_limit -/ + 4) t'2
  let t'3 := (Binary32.ofBits 0x00000000 /- 0 -/)
  PMem.stF32 ((0xedb8 : UInt64) /- &guided_limit -/ + 8) t'3
  let t'4 := (Binary32.ofBits 0x00000000 /- 0 -/)
  PMem.stF32 ((0xedb8 : UInt64) /- &guided_limit -/ + 12) t'4
  return ()

/-- `Mode.init` as a pure function of its arguments (it reads and writes no memory). -/
def Mode.init.pure' (this : UInt64) (ignore_checks : Bool) : Id Bool := do
  let mut ignore_checks := ignore_checks
  return true

/-- C++ `Mode::init : bool (bool)`, `AP_Common.h:123-125`. -/
def Mode.init (this : UInt64) (ignore_checks : Bool) : PMem.M Bool :=
  pure (_root_.Vehicle_lib.Mode.init.pure' this ignore_checks)

/-- C++ `ModeAuto::paused : bool () const`, `mode_auto.cpp:2447-2450`. -/
def ModeAuto.paused (this : UInt64) : PMem.M Bool := do
  let t'1 ← PMem.ldU64 (this + 24)
  let t'2 ← PMem.ldU64 t'1
  let mut sc'6 := (t'2 != (0 : UInt64))
  if sc'6 then
    let t'3 ← PMem.ldU64 (this + 24)
    let t'4 ← PMem.ldU64 t'3
    let t'5 ← AC_WPNav.paused t'4
    sc'6 := t'5
  return sc'6

/-- `Mode.set_speed_NE_ms` as a pure function of its arguments (it reads and writes no memory). -/
def Mode.set_speed_NE_ms.pure' (this : UInt64) (speed_ne_ms : Binary32) : Id Bool := do
  let mut speed_ne_ms := speed_ne_ms
  return false

/-- C++ `Mode::set_speed_NE_ms : bool (float)`, `AP_Common.h:177-?`. -/
def Mode.set_speed_NE_ms (this : UInt64) (speed_ne_ms : Binary32) : PMem.M Bool :=
  pure (_root_.Vehicle_lib.Mode.set_speed_NE_ms.pure' this speed_ne_ms)

/-- `Mode.set_speed_down_ms` as a pure function of its arguments (it reads and writes no memory). -/
def Mode.set_speed_down_ms.pure' (this : UInt64) (speed_down_ms : Binary32) : Id Bool := do
  let mut speed_down_ms := speed_down_ms
  return false

/-- C++ `Mode::set_speed_down_ms : bool (float)`, `AP_Common.h:179-?`. -/
def Mode.set_speed_down_ms (this : UInt64) (speed_down_ms : Binary32) : PMem.M Bool :=
  pure (_root_.Vehicle_lib.Mode.set_speed_down_ms.pure' this speed_down_ms)

/-- `Mode.set_speed_up_ms` as a pure function of its arguments (it reads and writes no memory). -/
def Mode.set_speed_up_ms.pure' (this : UInt64) (speed_up_ms : Binary32) : Id Bool := do
  let mut speed_up_ms := speed_up_ms
  return false

/-- C++ `Mode::set_speed_up_ms : bool (float)`, `AP_Common.h:178-?`. -/
def Mode.set_speed_up_ms (this : UInt64) (speed_up_ms : Binary32) : PMem.M Bool :=
  pure (_root_.Vehicle_lib.Mode.set_speed_up_ms.pure' this speed_up_ms)

/-- C++ `Copter::set_auto_armed : void (bool)`, `AP_State.cpp:4-14`. -/
def Copter.set_auto_armed (this : UInt64) (b : Bool) : PMem.M Unit := do
  let mut b := b
  let t'1 ← PMem.ldB ((this + 9448) + 5)
  if ((if t'1 then (1 : Int32) else (0 : Int32)) == (if b then (1 : Int32) else (0 : Int32))) then
    return ()
  PMem.stB ((this + 9448) + 5) b
  if b then
    pure ()
  return ()

/-- C++ `Mode::_TakeOff::start_m : void (float)`, `takeoff.cpp:51-57`. -/
def Mode._TakeOff.start_m (this : UInt64) (alt_m : Binary32) : PMem.M Unit := do
  let mut alt_m := alt_m
  PMem.stB this true
  let t'1 ← PMem.ldU64 ((0x86d8 : UInt64) /- &copter -/ + 11184)
  let t'2 ← AC_PosControl.get_pos_estimate_U_m t'1
  PMem.stF32 (this + 4) t'2
  let t'3 ← PMem.ldF32 (this + 4)
  let t'4 := (t'3 + alt_m)
  PMem.stF32 (this + 8) t'4
  return ()

/-- C++ `Mode::do_user_takeoff_start_m : bool (float)`, `takeoff.cpp:11-15`. -/
def Mode.do_user_takeoff_start_m (this : UInt64) (takeoff_alt_m : Binary32) : PMem.M Bool := do
  let mut takeoff_alt_m := takeoff_alt_m
  Mode._TakeOff.start_m (0xede8 : UInt64) /- &Mode::takeoff -/ takeoff_alt_m
  return true

/-- `ModeAltHold.has_user_takeoff` as a pure function of its arguments (it reads and writes no memory). -/
def ModeAltHold.has_user_takeoff.pure' (this : UInt64) (must_navigate : Bool) : Id Bool := do
  let mut must_navigate := must_navigate
  return !must_navigate

/-- C++ `ModeAltHold::has_user_takeoff : bool (bool) const`, `mode.h:512-514`. -/
def ModeAltHold.has_user_takeoff (this : UInt64) (must_navigate : Bool) : PMem.M Bool :=
  pure (_root_.Vehicle_lib.ModeAltHold.has_user_takeoff.pure' this must_navigate)

/-- `Mode.has_user_takeoff` as a pure function of its arguments (it reads and writes no memory). -/
def Mode.has_user_takeoff.pure' (this : UInt64) (must_navigate : Bool) : Id Bool := do
  let mut must_navigate := must_navigate
  return false

/-- C++ `Mode::has_user_takeoff : bool (bool) const`, `AP_Common.h:132-?`. -/
def Mode.has_user_takeoff (this : UInt64) (must_navigate : Bool) : PMem.M Bool :=
  pure (_root_.Vehicle_lib.Mode.has_user_takeoff.pure' this must_navigate)

/-- `ModeGuided.has_user_takeoff` as a pure function of its arguments (it reads and writes no memory). -/
def ModeGuided.has_user_takeoff.pure' (this : UInt64) (must_navigate : Bool) : Id Bool := do
  let mut must_navigate := must_navigate
  return true

/-- C++ `ModeGuided::has_user_takeoff : bool (bool) const`, `mode.h:1124-?`. -/
def ModeGuided.has_user_takeoff (this : UInt64) (must_navigate : Bool) : PMem.M Bool :=
  pure (_root_.Vehicle_lib.ModeGuided.has_user_takeoff.pure' this must_navigate)

/-- `ModeLoiter.has_user_takeoff` as a pure function of its arguments (it reads and writes no memory). -/
def ModeLoiter.has_user_takeoff.pure' (this : UInt64) (must_navigate : Bool) : Id Bool := do
  let mut must_navigate := must_navigate
  return true

/-- C++ `ModeLoiter::has_user_takeoff : bool (bool) const`, `mode.h:1381-?`. -/
def ModeLoiter.has_user_takeoff (this : UInt64) (must_navigate : Bool) : PMem.M Bool :=
  pure (_root_.Vehicle_lib.ModeLoiter.has_user_takeoff.pure' this must_navigate)

/-- `Mode.get_wp` as a pure function of its arguments (it reads and writes no memory). -/
def Mode.get_wp.pure' (this : UInt64) (loc : UInt64) : Id Bool := do
  return false

/-- C++ `Mode::get_wp : bool (Location &) const`, `AP_Common.h:171-?`. -/
def Mode.get_wp (this : UInt64) (loc : UInt64) : PMem.M Bool :=
  pure (_root_.Vehicle_lib.Mode.get_wp.pure' this loc)

/-- `Mode.is_landing` as a pure function of its arguments (it reads and writes no memory). -/
def Mode.is_landing.pure' (this : UInt64) : Id Bool := do
  return false

/-- C++ `Mode::is_landing : bool () const`, `AP_Common.h:165-?`. -/
def Mode.is_landing (this : UInt64) : PMem.M Bool :=
  pure (_root_.Vehicle_lib.Mode.is_landing.pure' this)

/-- C++ `ModeRTL::is_landing : bool () const`, `mode_rtl.cpp:429-432`. -/
def ModeRTL.is_landing (this : UInt64) : PMem.M Bool := do
  let t'1 ← PMem.ldU8 (this + 128)
  return (t'1 == (5 : UInt8))

/-- C++ `ModeAuto::is_landing : bool () const`, `mode_auto.cpp:675-686`. -/
def ModeAuto.is_landing (this : UInt64) : PMem.M Bool := do
  let t'1 ← PMem.ldU8 (this + 820)
  let sw'2 := t'1
  if sw'2 == (3 : UInt8) then
    return true
  else if sw'2 == (4 : UInt8) then
    let t'3 ← ModeRTL.is_landing ((0x86d8 : UInt64) /- &copter -/ + 12888)
    return t'3
  else
    return false
  return false

/-- `ModeLand.is_landing` as a pure function of its arguments (it reads and writes no memory). -/
def ModeLand.is_landing.pure' (this : UInt64) : Id Bool := do
  return true

/-- C++ `ModeLand::is_landing : bool () const`, `mode.h:1319-?`. -/
def ModeLand.is_landing (this : UInt64) : PMem.M Bool :=
  pure (_root_.Vehicle_lib.ModeLand.is_landing.pure' this)

/-- C++ `Mode::_TakeOff::running : bool () const`, `Copter.h:297-?`. -/
def Mode._TakeOff.running (this : UInt64) : PMem.M Bool := do
  let t'1 ← PMem.ldB this
  return t'1

/-- C++ `ModeAuto::is_taking_off : bool () const`, `mode_auto.cpp:688-691`. -/
def ModeAuto.is_taking_off (this : UInt64) : PMem.M Bool := do
  let t'1 ← PMem.ldU8 (this + 820)
  let mut sc'3 := (t'1 == (1 : UInt8))
  if sc'3 then
    let t'2 ← PMem.ldB (0x131b0 : UInt64) /- &Mode::auto_takeoff -/
    sc'3 := !t'2
  return sc'3

/-- C++ `ModeGuided::is_taking_off : bool () const`, `mode_guided.cpp:313-316`. -/
def ModeGuided.is_taking_off (this : UInt64) : PMem.M Bool := do
  let t'1 ← PMem.ldI32 (this + 112)
  let mut sc'3 := (t'1 == (0 : Int32))
  if sc'3 then
    let t'2 ← PMem.ldB (0x131d8 : UInt64) /- &ModeGuided::takeoff_complete -/
    sc'3 := !t'2
  return sc'3

/-- C++ `ModeGuided::submode : SubMode () const`, `mode.h:1185-?`. -/
def ModeGuided.submode (this : UInt64) : PMem.M Int32 := do
  let t'1 ← PMem.ldI32 (this + 112)
  return t'1

/-- `ModeGuided.get_target_pos_NED_m` as a pure function of its arguments (it reads and writes no memory). -/
def ModeGuided.get_target_pos_NED_m.pure' (this : UInt64) : Id UInt64 := do
  return (0x12e38 : UInt64) /- &guided_pos_target_ned_m -/

/-- C++ `ModeGuided::get_target_pos_NED_m : const Vector3p &() const`, `mode_guided.cpp:1133-1136`. -/
def ModeGuided.get_target_pos_NED_m (this : UInt64) : PMem.M UInt64 :=
  pure (_root_.Vehicle_lib.ModeGuided.get_target_pos_NED_m.pure' this)

/-- `ModeGuided.get_target_vel_NED_ms` as a pure function of its arguments (it reads and writes no memory). -/
def ModeGuided.get_target_vel_NED_ms.pure' (this : UInt64) : Id UInt64 := do
  return (0xeba8 : UInt64) /- &guided_vel_target_ned_ms -/

/-- C++ `ModeGuided::get_target_vel_NED_ms : const Vector3f &() const`, `mode_guided.cpp:1138-1141`. -/
def ModeGuided.get_target_vel_NED_ms (this : UInt64) : PMem.M UInt64 :=
  pure (_root_.Vehicle_lib.ModeGuided.get_target_vel_NED_ms.pure' this)

/-- `ModeGuided.get_target_accel_NED_mss` as a pure function of its arguments (it reads and writes no memory). -/
def ModeGuided.get_target_accel_NED_mss.pure' (this : UInt64) : Id UInt64 := do
  return (0xebb8 : UInt64) /- &guided_accel_target_ned_mss -/

/-- C++ `ModeGuided::get_target_accel_NED_mss : const Vector3f &() const`, `mode_guided.cpp:1143-1146`. -/
def ModeGuided.get_target_accel_NED_mss (this : UInt64) : PMem.M UInt64 :=
  pure (_root_.Vehicle_lib.ModeGuided.get_target_accel_NED_mss.pure' this)

/-- `Mode.crosstrack_error_m` as a pure function of its arguments (it reads and writes no memory). -/
def Mode.crosstrack_error_m.pure' (this : UInt64) : Id Binary32 := do
  return (Binary32.ofBits 0x00000000 /- 0 -/)

/-- C++ `Mode::crosstrack_error_m : float () const`, `AP_Common.h:174-?`. -/
def Mode.crosstrack_error_m (this : UInt64) : PMem.M Binary32 :=
  pure (_root_.Vehicle_lib.Mode.crosstrack_error_m.pure' this)

/-- C++ `ModeAuto::crosstrack_error_m : float () const`, `functor.h:642-?`. -/
def ModeAuto.crosstrack_error_m (this : UInt64) : PMem.M Binary32 := do
  let t'1 ← PMem.ldU64 (this + 24)
  let t'2 ← PMem.ldU64 t'1
  let t'3 ← AC_WPNav.crosstrack_error_m t'2
  return t'3

/-- C++ `ModeGuided::crosstrack_error_m : float () const`, `mode_guided.cpp:1182-1199`. -/
def ModeGuided.crosstrack_error_m (this : UInt64) : PMem.M Binary32 := do
  let t'1 ← PMem.ldI32 (this + 112)
  let sw'2 := t'1
  if sw'2 == (1 : Int32) then
    let t'3 ← PMem.ldU64 (this + 24)
    let t'4 ← PMem.ldU64 t'3
    let t'5 ← AC_WPNav.crosstrack_error_m t'4
    return t'5
  else if sw'2 == (2 : Int32) || sw'2 == (0 : Int32) || sw'2 == (5 : Int32) || sw'2 == (4 : Int32) || sw'2 == (3 : Int32) then
    let t'6 ← PMem.ldU64 (this + 40)
    let t'7 ← PMem.ldU64 t'6
    let t'8 ← AC_PosControl.crosstrack_error_m t'7
    return t'8
  else if sw'2 == (6 : Int32) then
    return Int32.toBinary32 ((0 : Int32))
  else
    pure ()
  return Int32.toBinary32 ((0 : Int32))

/-- C++ `ModeLoiter::crosstrack_error_m : float () const`, `mode.h:1400-?`. -/
def ModeLoiter.crosstrack_error_m (this : UInt64) : PMem.M Binary32 := do
  let t'1 ← PMem.ldU64 (this + 40)
  let t'2 ← PMem.ldU64 t'1
  let t'3 ← AC_PosControl.crosstrack_error_m t'2
  return t'3

/-- C++ `ModeRTL::crosstrack_error_m : float () const`, `mode.h:1591-?`. -/
def ModeRTL.crosstrack_error_m (this : UInt64) : PMem.M Binary32 := do
  let t'1 ← PMem.ldU64 (this + 24)
  let t'2 ← PMem.ldU64 t'1
  let t'3 ← AC_WPNav.crosstrack_error_m t'2
  return t'3

/-- `Mode.wp_bearing_deg` as a pure function of its arguments (it reads and writes no memory). -/
def Mode.wp_bearing_deg.pure' (this : UInt64) : Id Binary32 := do
  return Int32.toBinary32 ((0 : Int32))

/-- C++ `Mode::wp_bearing_deg : float () const`, `AP_Common.h:172-?`. -/
def Mode.wp_bearing_deg (this : UInt64) : PMem.M Binary32 :=
  pure (_root_.Vehicle_lib.Mode.wp_bearing_deg.pure' this)

/-- C++ `ModeAuto::wp_bearing_deg : float () const`, `mode_auto.cpp:956-959`. -/
def ModeAuto.wp_bearing_deg (this : UInt64) : PMem.M Binary32 := do
  let t'1 ← PMem.ldU64 (this + 24)
  let t'2 ← PMem.ldU64 t'1
  let t'3 ← AC_WPNav.get_wp_bearing_to_destination_rad t'2
  let t'4 ← degrees t'3
  return t'4

/-- C++ `ModeCircle::wp_bearing_deg : float () const`, `mode_circle.cpp:138-141`. -/
def ModeCircle.wp_bearing_deg (this : UInt64) : PMem.M Binary32 := do
  let t'1 ← PMem.ldU64 ((0x86d8 : UInt64) /- &copter -/ + 11208)
  let t'2 ← AC_Circle.get_bearing_to_target_rad t'1
  let t'3 ← degrees t'2
  return t'3

/-- C++ `ModeGuided::wp_bearing_deg : float () const`, `mode_guided.cpp:1162-1180`. -/
def ModeGuided.wp_bearing_deg.body (fp : UInt64) (this : UInt64) : PMem.M Binary32 := do
  let t'1 ← PMem.ldI32 (this + 112)
  let sw'2 := t'1
  if sw'2 == (1 : Int32) then
    let t'3 ← PMem.ldU64 (this + 24)
    let t'4 ← PMem.ldU64 t'3
    let t'5 ← AC_WPNav.get_wp_bearing_to_destination_rad t'4
    let t'6 ← degrees t'5
    return t'6
  else if sw'2 == (2 : Int32) then
    let t'7 ← PMem.ldU64 (this + 40)
    let t'8 ← PMem.ldU64 t'7
    let t'9 ← AC_PosControl.get_pos_estimate_NED_m t'8
    let t'10 ← Vector3'double.xy t'9
    Vector2'double.tofloat t'10 (fp + 0)
    let t'11 := (fp + 0)
    let t'12 ← Vector3'double.xy (0x12e38 : UInt64) /- &guided_pos_target_ned_m -/
    Vector2'double.tofloat t'12 (fp + 8)
    let t'13 := (fp + 8)
    let t'14 ← get_bearing_rad t'11 t'13
    let t'15 ← degrees t'14
    return t'15
  else if sw'2 == (3 : Int32) then
    let t'16 ← PMem.ldU64 (this + 40)
    let t'17 ← PMem.ldU64 t'16
    let t'18 ← AC_PosControl.get_bearing_to_target_rad t'17
    let t'19 ← degrees t'18
    return t'19
  else if sw'2 == (0 : Int32) || sw'2 == (5 : Int32) || sw'2 == (4 : Int32) || sw'2 == (6 : Int32) then
    return Int32.toBinary32 ((0 : Int32))
  else
    pure ()
  return Binary64.toBinary32 ((Binary64.ofBits 0x0000000000000000 /- 0 -/))

def ModeGuided.wp_bearing_deg (this : UInt64) : PMem.M Binary32 := do
  let fp ← PMem.enter 16
  let r ← ModeGuided.wp_bearing_deg.body fp this
  PMem.leave fp
  return r

/-- C++ `ModeLoiter::wp_bearing_deg : float () const`, `mode_loiter.cpp:188-191`. -/
def ModeLoiter.wp_bearing_deg (this : UInt64) : PMem.M Binary32 := do
  let t'1 ← PMem.ldU64 (this + 32)
  let t'2 ← PMem.ldU64 t'1
  let t'3 ← AC_Loiter.get_bearing_to_target_rad t'2
  let t'4 ← degrees t'3
  return t'4

/-- C++ `ModeRTL::wp_bearing_deg : float () const`, `mode_rtl.cpp:634-637`. -/
def ModeRTL.wp_bearing_deg (this : UInt64) : PMem.M Binary32 := do
  let t'1 ← PMem.ldU64 (this + 24)
  let t'2 ← PMem.ldU64 t'1
  let t'3 ← AC_WPNav.get_wp_bearing_to_destination_rad t'2
  let t'4 ← degrees t'3
  return t'4

/-- `Mode.wp_distance_m` as a pure function of its arguments (it reads and writes no memory). -/
def Mode.wp_distance_m.pure' (this : UInt64) : Id Binary32 := do
  return (Binary32.ofBits 0x00000000 /- 0 -/)

/-- C++ `Mode::wp_distance_m : float () const`, `AP_Common.h:173-?`. -/
def Mode.wp_distance_m (this : UInt64) : PMem.M Binary32 :=
  pure (_root_.Vehicle_lib.Mode.wp_distance_m.pure' this)

/-- C++ `ModeAuto::wp_distance_m : float () const`, `mode_auto.cpp:950-954`. -/
def ModeAuto.wp_distance_m (this : UInt64) : PMem.M Binary32 := do
  let t'1 ← PMem.ldU64 (this + 24)
  let t'2 ← PMem.ldU64 t'1
  let t'3 ← AC_WPNav.get_wp_distance_to_destination_m t'2
  return t'3

/-- C++ `ModeCircle::wp_distance_m : float () const`, `mode_circle.cpp:133-136`. -/
def ModeCircle.wp_distance_m (this : UInt64) : PMem.M Binary32 := do
  let t'1 ← PMem.ldU64 ((0x86d8 : UInt64) /- &copter -/ + 11208)
  let t'2 ← AC_Circle.get_distance_to_target_m t'1
  return t'2

/-- C++ `ModeGuided::wp_distance_m : float () const`, `mode_guided.cpp:1148-1160`. -/
def ModeGuided.wp_distance_m.body (fp : UInt64) (this : UInt64) : PMem.M Binary32 := do
  let t'1 ← PMem.ldI32 (this + 112)
  let sw'2 := t'1
  if sw'2 == (1 : Int32) then
    let t'3 ← PMem.ldU64 (this + 24)
    let t'4 ← PMem.ldU64 t'3
    let t'5 ← AC_WPNav.get_wp_distance_to_destination_m t'4
    return t'5
  else if sw'2 == (2 : Int32) then
    let t'6 ← PMem.ldU64 (this + 40)
    let t'7 ← PMem.ldU64 t'6
    let t'8 ← AC_PosControl.get_pos_estimate_NED_m t'7
    let t'9 ← Vector3'double.xy t'8
    Vector2'double.tofloat t'9 (fp + 0)
    let t'10 := (fp + 0)
    let t'11 ← Vector3'double.xy (0x12e38 : UInt64) /- &guided_pos_target_ned_m -/
    Vector2'double.tofloat t'11 (fp + 8)
    let t'12 := (fp + 8)
    let t'13 ← get_horizontal_distance'float t'10 t'12
    return t'13
  else if sw'2 == (3 : Int32) then
    let t'14 ← PMem.ldU64 (this + 40)
    let t'15 ← PMem.ldU64 t'14
    let t'16 ← AC_PosControl.get_pos_error_NE_m t'15
    return t'16
  else
    return (Binary32.ofBits 0x00000000 /- 0 -/)

def ModeGuided.wp_distance_m (this : UInt64) : PMem.M Binary32 := do
  let fp ← PMem.enter 16
  let r ← ModeGuided.wp_distance_m.body fp this
  PMem.leave fp
  return r

/-- C++ `ModeLoiter::wp_distance_m : float () const`, `mode_loiter.cpp:183-186`. -/
def ModeLoiter.wp_distance_m (this : UInt64) : PMem.M Binary32 := do
  let t'1 ← PMem.ldU64 (this + 32)
  let t'2 ← PMem.ldU64 t'1
  let t'3 ← AC_Loiter.get_distance_to_target_m t'2
  return t'3

/-- C++ `ModeRTL::wp_distance_m : float () const`, `mode_rtl.cpp:629-632`. -/
def ModeRTL.wp_distance_m (this : UInt64) : PMem.M Binary32 := do
  let t'1 ← PMem.ldU64 (this + 24)
  let t'2 ← PMem.ldU64 t'1
  let t'3 ← AC_WPNav.get_wp_distance_to_destination_m t'2
  return t'3

/-- `GCS_MAVLINK_Copter.vtol_state` as a pure function of its arguments (it reads and writes no memory). -/
def GCS_MAVLINK_Copter.vtol_state.pure' (this : UInt64) : Id UInt32 := do
  return (3 : UInt32)

/-- C++ `GCS_MAVLINK_Copter::vtol_state : MAV_VTOL_STATE () const`, `GCS_MAVLink_Copter.h:50-?`. -/
def GCS_MAVLINK_Copter.vtol_state (this : UInt64) : PMem.M UInt32 :=
  pure (_root_.Vehicle_lib.GCS_MAVLINK_Copter.vtol_state.pure' this)

/-- C++ `GCS_MAVLINK_Copter::vfr_hud_airspeed : float () const`, `GCS_MAVLink_Copter.cpp:197-216`. -/
def GCS_MAVLINK_Copter.vfr_hud_airspeed.body (fp : UInt64) (this : UInt64) : PMem.M Binary32 := do
  Vector3'float.Vector3'2 (fp + 0)
  let t'1 ← VehicleBridge.ahrs'0
  let t'2 ← VehicleBridge.AP_AHRS.airspeed_vector_TAS'1 t'1 (fp + 0)
  if t'2 then
    let t'3 ← Vector3'float.length (fp + 0)
    return t'3
  let t'4 ← VehicleBridge.gps'0
  let t'5 ← VehicleBridge.AP_GPS.ground_speed'0 t'4
  return t'5

def GCS_MAVLINK_Copter.vfr_hud_airspeed (this : UInt64) : PMem.M Binary32 := do
  let fp ← PMem.enter 12
  let r ← GCS_MAVLINK_Copter.vfr_hud_airspeed.body fp this
  PMem.leave fp
  return r

/-- `Mode.enabled` as a pure function of its arguments (it reads and writes no memory). -/
def Mode.enabled.pure' (this : UInt64) : Id Bool := do
  return true

/-- C++ `Mode::enabled : bool () const`, `AP_Common.h:213-?`. -/
def Mode.enabled (this : UInt64) : PMem.M Bool :=
  pure (_root_.Vehicle_lib.Mode.enabled.pure' this)

/-- `GCS_MAVLINK_Copter.command_int_only` as a pure function of its arguments (it reads and writes no memory). -/
def GCS_MAVLINK_Copter.command_int_only.pure' (this : UInt64) (command : UInt32) : Id Bool := do
  let mut command := command
  let sw'1 := UInt32.toInt32 (command)
  if sw'1 == (84 : Int32) then
    return true
  else
    return false

/-- C++ `GCS_MAVLINK_Copter::command_int_only : bool (MAV_CMD) const`, `GCS_MAVLink_Copter.cpp:602-610`. -/
def GCS_MAVLINK_Copter.command_int_only (this : UInt64) (command : UInt32) : PMem.M Bool :=
  pure (_root_.Vehicle_lib.GCS_MAVLINK_Copter.command_int_only.pure' this command)

/-- `GCS_Copter.min_loop_time_remaining_for_message_send_us` as a pure function of its arguments (it reads and writes no memory). -/
def GCS_Copter.min_loop_time_remaining_for_message_send_us.pure' (this : UInt64) : Id UInt16 := do
  return Int16.toUInt16 (Int32.toInt16 ((250 : Int32)))

/-- C++ `GCS_Copter::min_loop_time_remaining_for_message_send_us : uint16_t () const`, `GCS.h:38-40`. -/
def GCS_Copter.min_loop_time_remaining_for_message_send_us (this : UInt64) : PMem.M UInt16 :=
  pure (_root_.Vehicle_lib.GCS_Copter.min_loop_time_remaining_for_message_send_us.pure' this)

/-- C++ `Copter::get_scheduler_tasks : void (const AP_Scheduler::Task *&, uint8_t &, uint32_t &)`, `Copter.cpp:264-271`. -/
def Copter.get_scheduler_tasks (this : UInt64) (tasks : UInt64) (task_count : UInt64) (log_bit : UInt64) : PMem.M Unit := do
  let t'1 := ((0xc020 : UInt64) /- &Copter::scheduler_tasks -/ + ((Int32.toInt64 ((0 : Int32))) * 32).toUInt64)
  PMem.stU64 tasks t'1
  let t'2 := UInt64.toUInt8 (((960 : UInt64) / (32 : UInt64)))
  PMem.stU8 task_count t'2
  let t'3 := Int32.toUInt32 (((1 : Int32) <<< (3 : Int32)))
  PMem.stU32 log_bit t'3
  return ()

/-- C++ `Copter::default_dead_zones : void ()`, `radio.cpp:7-18`. -/
def Copter.default_dead_zones (this : UInt64) : PMem.M Unit := do
  let t'1 ← PMem.ldU64 (this + 8600)
  RC_Channel.set_default_dead_zone t'1 (Int32.toInt16 ((20 : Int32)))
  let t'2 ← PMem.ldU64 (this + 8608)
  RC_Channel.set_default_dead_zone t'2 (Int32.toInt16 ((20 : Int32)))
  let t'3 ← PMem.ldU64 (this + 8616)
  RC_Channel.set_default_dead_zone t'3 (Int32.toInt16 ((30 : Int32)))
  let t'4 ← PMem.ldU64 (this + 8624)
  RC_Channel.set_default_dead_zone t'4 (Int32.toInt16 ((20 : Int32)))
  return ()

/-- C++ `Copter::failsafe_option : bool (FailsafeOption) const`, `events.cpp:8-11`. -/
def Copter.failsafe_option (this : UInt64) (opt : Int32) : PMem.M Bool := do
  let mut opt := opt
  let t'1 ← AP_ParamT'unsigned_int_3.operator_const_unsigned_int__ ((this + 6840) + 1652)
  let t'2 ← PMem.ldU32 t'1
  return (t'2 &&& (Int32.toUInt32 (opt))) != (0 : UInt32)

/-- C++ `Copter::air_mode_active : bool () const`, `AP_Common.h:392-394`. -/
def Copter.air_mode_active (this : UInt64) : PMem.M Bool := do
  let t'1 ← PMem.ldI32 (this + 9476)
  let mut sc'3 := (t'1 == (2 : Int32))
  if !sc'3 then
    let t'2 ← PMem.ldB ((this + 9448) + 25)
    sc'3 := t'2
  return sc'3

/-- C++ `Copter::esc_calibration_notify : void ()`, `esc_calibration.cpp:143-151`. -/
def Copter.esc_calibration_notify (this : UInt64) : PMem.M Unit := do
  PMem.stB ((0xccc0 : UInt64) /- &AP_Notify::flags -/ + 9) true
  let mut now : UInt32 := ((← PMem.clock) / 1000).toUInt32
  let t'1 ← PMem.ldU32 (this + 11224)
  if (decide ((now - t'1) > (Int32.toUInt32 ((20 : Int32))))) then
    PMem.stU32 (this + 11224) now
  return ()

/-- C++ `Copter::check_ekf_reset : void ()`, `ekf_check.cpp:248-263`. -/
def Copter.check_ekf_reset (this : UInt64) : PMem.M Unit := do
  let t'1 ← VehicleBridge.AP_AHRS.get_yaw_reset_count'0 (this + 4080)
  let mut new_yaw_reset_count : UInt16 := t'1
  let t'2 ← PMem.ldU16 (this + 8848)
  if ((UInt32.toInt32 (UInt16.toUInt32 (new_yaw_reset_count))) != (UInt32.toInt32 (UInt16.toUInt32 (t'2)))) then
    let t'3 ← PMem.ldU64 (this + 11168)
    AC_AttitudeControl.inertial_frame_reset t'3
    PMem.stU16 (this + 8848) new_yaw_reset_count
  let t'4 ← VehicleBridge.AP_AHRS.get_last_attitude_reset_count'0 (this + 4080)
  let mut new_reset_count : UInt16 := t'4
  let t'5 ← PMem.ldU16 (this + 8850)
  if ((UInt32.toInt32 (UInt16.toUInt32 (new_reset_count))) != (UInt32.toInt32 (UInt16.toUInt32 (t'5)))) then
    let t'6 ← PMem.ldU64 (this + 11168)
    AC_AttitudeControl.inertial_frame_reset t'6
    PMem.stU16 (this + 8850) new_reset_count
  return ()

/-- `Mode.move_vehicle_on_ekf_reset` as a pure function of its arguments (it reads and writes no memory). -/
def Mode.move_vehicle_on_ekf_reset.pure' (this : UInt64) : Id Bool := do
  return false

/-- C++ `Mode::move_vehicle_on_ekf_reset : bool () const`, `AP_Common.h:140-?`. -/
def Mode.move_vehicle_on_ekf_reset (this : UInt64) : PMem.M Bool :=
  pure (_root_.Vehicle_lib.Mode.move_vehicle_on_ekf_reset.pure' this)

/-- C++ `ModeAuto::move_vehicle_on_ekf_reset : bool () const`, `mode_auto.cpp:235-263`. -/
def ModeAuto.move_vehicle_on_ekf_reset (this : UInt64) : PMem.M Bool := do
  let t'1 ← PMem.ldU8 (this + 820)
  let sw'2 := t'1
  if sw'2 == (0 : UInt8) || sw'2 == (1 : UInt8) || sw'2 == (3 : UInt8) || sw'2 == (4 : UInt8) || sw'2 == (7 : UInt8) || sw'2 == (8 : UInt8) || sw'2 == (9 : UInt8) || sw'2 == (10 : UInt8) || sw'2 == (11 : UInt8) then
    return false
  else if sw'2 == (2 : UInt8) || sw'2 == (5 : UInt8) || sw'2 == (6 : UInt8) then
    return true
  else
    pure ()
  return true

/-- C++ `ModeGuided::move_vehicle_on_ekf_reset : bool () const`, `mode_guided.cpp:137-156`. -/
def ModeGuided.move_vehicle_on_ekf_reset (this : UInt64) : PMem.M Bool := do
  let t'1 ← PMem.ldI32 (this + 112)
  let sw'2 := t'1
  if sw'2 == (0 : Int32) || sw'2 == (5 : Int32) || sw'2 == (4 : Int32) || sw'2 == (6 : Int32) then
    return false
  else if sw'2 == (1 : Int32) || sw'2 == (2 : Int32) || sw'2 == (3 : Int32) then
    return true
  else
    pure ()
  return true

/-- C++ `Mode::get_pilot_desired_yaw_rate_rads : float () const`, `mode.cpp:1075-1086`. -/
def Mode.get_pilot_desired_yaw_rate_rads (this : UInt64) : PMem.M Binary32 := do
  let t'1 ← rc
  let t'2 ← RC_Channels_Copter.has_valid_input t'1
  if !t'2 then
    return (Binary32.ofBits 0x00000000 /- 0 -/)
  let t'3 ← PMem.ldU64 (this + 96)
  let t'4 ← PMem.ldU64 t'3
  let t'5 ← RC_Channel.norm_input_dz t'4
  let mut yaw_in_norm : Binary32 := t'5
  let t'6 ← PMem.ldU64 (this + 16)
  let t'7 ← AC_CommandModel.get_rate (t'6 + 1656)
  let t'8 ← radians t'7
  let t'9 ← PMem.ldU64 (this + 16)
  let t'10 ← AC_CommandModel.get_expo (t'9 + 1656)
  let t'11 ← input_expo yaw_in_norm t'10
  return (t'8 * t'11)

/-- `Mode.get_avoidance_adjusted_climbrate_ms` as a pure function of its arguments (it reads and writes no memory). -/
def Mode.get_avoidance_adjusted_climbrate_ms.pure' (this : UInt64) (target_rate_ms : Binary32) : Id Binary32 := do
  let mut target_rate_ms := target_rate_ms
  return target_rate_ms

/-- C++ `Mode::get_avoidance_adjusted_climbrate_ms : float (float)`, `mode.cpp:1005-1014`. -/
def Mode.get_avoidance_adjusted_climbrate_ms (this : UInt64) (target_rate_ms : Binary32) : PMem.M Binary32 :=
  pure (_root_.Vehicle_lib.Mode.get_avoidance_adjusted_climbrate_ms.pure' this target_rate_ms)

/-- C++ `ModeAuto::verify_takeoff : bool ()`, `mode_auto.cpp:2141-2152`. -/
def ModeAuto.verify_takeoff (this : UInt64) : PMem.M Bool := do
  let t'1 ← PMem.ldB (0x131b0 : UInt64) /- &Mode::auto_takeoff -/
  return t'1

/-- `ModeAuto.verify_loiter_unlimited` as a pure function of its arguments (it reads and writes no memory). -/
def ModeAuto.verify_loiter_unlimited.pure' (this : UInt64) : Id Bool := do
  return false

/-- C++ `ModeAuto::verify_loiter_unlimited : bool ()`, `mode_auto.cpp:2219-2222`. -/
def ModeAuto.verify_loiter_unlimited (this : UInt64) : PMem.M Bool :=
  pure (_root_.Vehicle_lib.ModeAuto.verify_loiter_unlimited.pure' this)

/-- C++ `ModeAuto::verify_loiter_to_alt : bool () const`, `mode_auto.cpp:2248-2255`. -/
def ModeAuto.verify_loiter_to_alt (this : UInt64) : PMem.M Bool := do
  let t'1 ← PMem.ldBits (this + 828) 0 1
  let mut sc'3 := (t'1 != 0)
  if sc'3 then
    let t'2 ← PMem.ldBits (this + 828) 2 1
    sc'3 := (t'2 != 0)
  if sc'3 then
    return true
  return false

/-- C++ `ModeGuided::limit_check : bool ()`, `mode_guided.cpp:1101-1131`. -/
def ModeGuided.limit_check (this : UInt64) : PMem.M Bool := do
  let t'1 ← PMem.ldU32 (0xedb8 : UInt64) /- &guided_limit -/
  let mut sc'4 := (decide (t'1 > (Int32.toUInt32 ((0 : Int32)))))
  if sc'4 then
    let t'2 ← PMem.ldU32 ((0xedb8 : UInt64) /- &guided_limit -/ + 16)
    let t'3 ← PMem.ldU32 (0xedb8 : UInt64) /- &guided_limit -/
    sc'4 := (decide (((((← PMem.clock) / 1000).toUInt32) - t'2) ≥ t'3))
  if sc'4 then
    return true
  let t'5 ← PMem.ldU64 (this + 40)
  let t'6 ← PMem.ldU64 t'5
  let t'7 ← AC_PosControl.get_pos_estimate_NED_m t'6
  let curr_pos_ned_m : UInt64 := t'7
  let t'8 ← PMem.ldF32 ((0xedb8 : UInt64) /- &guided_limit -/ + 4)
  let t'9 ← is_zero t'8
  let mut sc'12 := !t'9
  if sc'12 then
    let t'10 ← PMem.ldF64 (curr_pos_ned_m + 16)
    let t'11 ← PMem.ldF32 ((0xedb8 : UInt64) /- &guided_limit -/ + 4)
    sc'12 := (decide ((-t'10) < (Binary32.toBinary64 (t'11))))
  if sc'12 then
    return true
  let t'13 ← PMem.ldF32 ((0xedb8 : UInt64) /- &guided_limit -/ + 8)
  let t'14 ← is_zero t'13
  let mut sc'17 := !t'14
  if sc'17 then
    let t'15 ← PMem.ldF64 (curr_pos_ned_m + 16)
    let t'16 ← PMem.ldF32 ((0xedb8 : UInt64) /- &guided_limit -/ + 8)
    sc'17 := (decide ((-t'15) > (Binary32.toBinary64 (t'16))))
  if sc'17 then
    return true
  let t'18 ← PMem.ldF32 ((0xedb8 : UInt64) /- &guided_limit -/ + 12)
  if (decide (t'18 > (Binary32.ofBits 0x00000000 /- 0 -/))) then
    let t'19 ← Vector3'double.xy ((0xedb8 : UInt64) /- &guided_limit -/ + 24)
    let t'20 ← Vector3'double.xy curr_pos_ned_m
    let t'21 ← get_horizontal_distance'double t'19 t'20
    let mut horiz_offset_m : Binary32 := t'21
    let t'22 ← PMem.ldF32 ((0xedb8 : UInt64) /- &guided_limit -/ + 12)
    if (decide (horiz_offset_m > t'22)) then
      return true
  return false

/-- C++ `ModeAuto::verify_nav_guided_enable : bool (const AP_Mission::Mission_Command &)`, `mode_auto.cpp:2384-2393`. -/
def ModeAuto.verify_nav_guided_enable (this : UInt64) (cmd : UInt64) : PMem.M Bool := do
  let t'1 ← PMem.ldU16 (cmd + 4)
  if ((UInt32.toInt32 (UInt16.toUInt32 (t'1))) == (0 : Int32)) then
    return true
  let t'2 ← ModeGuided.limit_check ((0x86d8 : UInt64) /- &copter -/ + 12520)
  return t'2

/-- C++ `ModeAuto::verify_nav_delay : bool (const AP_Mission::Mission_Command &)`, `mode_auto.cpp:2397-2404`. -/
def ModeAuto.verify_nav_delay (this : UInt64) (cmd : UInt64) : PMem.M Bool := do
  let t'1 ← PMem.ldU32 (this + 844)
  let t'2 ← PMem.ldU32 (this + 840)
  if (decide (((((← PMem.clock) / 1000).toUInt32) - t'1) > t'2)) then
    let t'3 := Int32.toUInt32 ((0 : Int32))
    PMem.stU32 (this + 840) t'3
    return true
  return false

/-- C++ `ModeAuto::verify_nav_attitude_time : bool (const AP_Mission::Mission_Command &)`, `mode_auto.cpp:2421-2424`. -/
def ModeAuto.verify_nav_attitude_time (this : UInt64) (cmd : UInt64) : PMem.M Bool := do
  let t'1 ← PMem.ldU32 ((this + 864) + 12)
  let t'2 ← PMem.ldU16 (cmd + 8)
  return (decide (((((← PMem.clock) / 1000).toUInt32) - t'1) > (Int32.toUInt32 (((UInt32.toInt32 (UInt16.toUInt32 (t'2))) * (1000 : Int32))))))

/-- C++ `ModeAuto::verify_wait_delay : bool ()`, `mode_auto.cpp:2268-2275`. -/
def ModeAuto.verify_wait_delay.body (fp : UInt64) (this : UInt64) : PMem.M Bool := do
  let t'1 ← PMem.ldU32 (this + 852)
  PMem.stI32 (fp + 0) (0 : Int32)
  let t'2 ← MAX'int_int (this + 848) (fp + 0)
  let t'3 ← PMem.ldI32 t'2
  if (decide (((((← PMem.clock) / 1000).toUInt32) - t'1) > (Int32.toUInt32 (t'3)))) then
    PMem.stI32 (this + 848) (0 : Int32)
    return true
  return false

def ModeAuto.verify_wait_delay (this : UInt64) : PMem.M Bool := do
  let fp ← PMem.enter 4
  let r ← ModeAuto.verify_wait_delay.body fp this
  PMem.leave fp
  return r

/-- C++ `ModeAuto::verify_within_distance : bool ()`, `mode_auto.cpp:2277-2284`. -/
def ModeAuto.verify_within_distance.body (fp : UInt64) (this : UInt64) : PMem.M Bool := do
  let t'1 ← ModeAuto.wp_distance_m this
  PMem.stI32 (fp + 0) (0 : Int32)
  let t'2 ← MAX'int_int (this + 848) (fp + 0)
  let t'3 ← PMem.ldI32 t'2
  if (decide (t'1 < (Int32.toBinary32 (t'3)))) then
    PMem.stI32 (this + 848) (0 : Int32)
    return true
  return false

def ModeAuto.verify_within_distance (this : UInt64) : PMem.M Bool := do
  let fp ← PMem.enter 4
  let r ← ModeAuto.verify_within_distance.body fp this
  PMem.leave fp
  return r

/-- C++ `Mode::AutoYaw::reached_fixed_yaw_target : bool ()`, `autoyaw.cpp:217-231`. -/
def Mode.AutoYaw.reached_fixed_yaw_target (this : UInt64) : PMem.M Bool := do
  let t'1 ← Mode.AutoYaw.mode this
  if (t'1 != (3 : Int32)) then
    return true
  let t'2 ← PMem.ldF32 (this + 20)
  let t'3 ← is_zero t'2
  if !t'3 then
    return false
  let t'4 ← PMem.ldF32 (this + 36)
  let t'5 ← VehicleBridge.AP_AHRS.get_yaw_rad'0 ((0x86d8 : UInt64) /- &copter -/ + 4080)
  let t'6 ← wrap_PI'float (t'4 - t'5)
  let t'7 ← radians'2 (2 : Int32)
  return (decide ((Binary32.abs t'6) ≤ t'7))

/-- C++ `ModeAuto::verify_yaw : bool ()`, `mode_auto.cpp:2287-2294`. -/
def ModeAuto.verify_yaw (this : UInt64) : PMem.M Bool := do
  Mode.AutoYaw.set_mode (0xeb78 : UInt64) /- &Mode::auto_yaw -/ (3 : Int32)
  let t'1 ← Mode.AutoYaw.reached_fixed_yaw_target (0xeb78 : UInt64) /- &Mode::auto_yaw -/
  return t'1

/-- C++ `Copter::failsafe_terrain_set_status : void (bool)`, `events.cpp:261-278`. -/
def Copter.failsafe_terrain_set_status (this : UInt64) (data_ok : Bool) : PMem.M Unit := do
  let mut data_ok := data_ok
  let mut now : UInt32 := ((← PMem.clock) / 1000).toUInt32
  if !data_ok then
    PMem.stU32 ((this + 9508) + 4) now
    let t'1 ← PMem.ldU32 (this + 9508)
    if (t'1 == (Int32.toUInt32 ((0 : Int32)))) then
      PMem.stU32 (this + 9508) now
  else
    let t'2 ← PMem.ldU32 ((this + 9508) + 4)
    if (decide ((now - t'2) > (Int32.toUInt32 ((100 : Int32))))) then
      let t'3 := Int32.toUInt32 ((0 : Int32))
      PMem.stU32 ((this + 9508) + 4) t'3
      let t'4 := Int32.toUInt32 ((0 : Int32))
      PMem.stU32 (this + 9508) t'4
  return ()

/-- C++ `Mode::AutoYaw::roi_yaw_rad : float () const`, `autoyaw.cpp:6-13`. -/
def Mode.AutoYaw.roi_yaw_rad.body (fp : UInt64) (this : UInt64) : PMem.M Binary32 := do
  Vector2'float.Vector2 (fp + 0)
  let t'1 ← VehicleBridge.ahrs'0
  let t'2 ← VehicleBridge.AP_AHRS.get_relative_position_NE_origin_float'1 t'1 (fp + 0)
  if t'2 then
    let t'3 ← Vector3'float.xy (this + 8)
    let t'4 ← get_bearing_rad (fp + 0) t'3
    return t'4
  let t'5 ← PMem.ldU64 ((0x86d8 : UInt64) /- &copter -/ + 11168)
  let t'6 ← AC_AttitudeControl.get_att_target_euler_rad t'5
  let t'7 ← PMem.ldF32 (t'6 + 8)
  return t'7

def Mode.AutoYaw.roi_yaw_rad (this : UInt64) : PMem.M Binary32 := do
  let fp ← PMem.enter 8
  let r ← Mode.AutoYaw.roi_yaw_rad.body fp this
  PMem.leave fp
  return r

/-- C++ `Mode::AutoYaw::rate_rads : float ()`, `autoyaw.cpp:325-354`. -/
def Mode.AutoYaw.rate_rads (this : UInt64) : PMem.M Binary32 := do
  let t'1 ← PMem.ldI32 this
  let sw'2 := t'1
  if sw'2 == (0 : Int32) || sw'2 == (2 : Int32) || sw'2 == (3 : Int32) || sw'2 == (4 : Int32) || sw'2 == (5 : Int32) || sw'2 == (8 : Int32) then
    let t'3 := (Binary32.ofBits 0x00000000 /- 0 -/)
    PMem.stF32 (this + 40) t'3
  else if sw'2 == (1 : Int32) then
    let t'4 ← PMem.ldU64 ((0x86d8 : UInt64) /- &copter -/ + 11184)
    let t'5 ← AC_PosControl.get_yaw_rate_rads t'4
    PMem.stF32 (this + 40) t'5
  else if sw'2 == (9 : Int32) then
    let t'6 ← PMem.ldF32 (this + 44)
    PMem.stF32 (this + 40) t'6
  else if sw'2 == (6 : Int32) || sw'2 == (7 : Int32) || sw'2 == (10 : Int32) then
    pure ()
  else
    pure ()
  let t'7 ← PMem.ldF32 (this + 40)
  return t'7

/-- `Mode.use_pilot_yaw` as a pure function of its arguments (it reads and writes no memory). -/
def Mode.use_pilot_yaw.pure' (this : UInt64) : Id Bool := do
  return true

/-- C++ `Mode::use_pilot_yaw : bool () const`, `AP_Common.h:197-?`. -/
def Mode.use_pilot_yaw (this : UInt64) : PMem.M Bool :=
  pure (_root_.Vehicle_lib.Mode.use_pilot_yaw.pure' this)

/-- C++ `ModeGuided::use_pilot_yaw : bool () const`, `mode_guided.cpp:1063-1066`. -/
def ModeGuided.use_pilot_yaw (this : UInt64) : PMem.M Bool := do
  let t'1 ← ModeGuided.option_is_enabled this (4 : UInt32)
  return !t'1

/-- C++ `ModeLand::use_pilot_yaw : bool () const`, `mode_land.cpp:204-208`. -/
def ModeLand.use_pilot_yaw (this : UInt64) : PMem.M Bool := do
  let t'1 ← PMem.ldU64 (this + 8)
  let t'2 ← AP_ParamT'signed_char_1.operator_const_signed_char__ (t'1 + 51)
  let t'3 ← PMem.ldI8 t'2
  return t'3 != (0 : Int8)

/-- C++ `ModeRTL::option_is_enabled : bool (Option) const`, `mode_rtl.cpp:667-670`. -/
def ModeRTL.option_is_enabled (this : UInt64) (option : Int32) : PMem.M Bool := do
  let mut option := option
  let t'1 ← AP_ParamT'unsigned_int_3.operator_const_unsigned_int__ (((0x86d8 : UInt64) /- &copter -/ + 6840) + 1692)
  let t'2 ← PMem.ldU32 t'1
  return ((t'2 &&& (Int32.toUInt32 (option))) != (Int32.toUInt32 ((0 : Int32))))

/-- C++ `ModeRTL::use_pilot_yaw : bool () const`, `mode_rtl.cpp:640-647`. -/
def ModeRTL.use_pilot_yaw (this : UInt64) : PMem.M Bool := do
  let t'1 ← PMem.ldU8 (this + 128)
  let mut sc'3 := (t'1 == (4 : UInt8))
  if !sc'3 then
    let t'2 ← PMem.ldU8 (this + 128)
    sc'3 := (t'2 == (5 : UInt8))
  if sc'3 then
    let t'4 ← ModeLand.use_pilot_yaw ((0x86d8 : UInt64) /- &copter -/ + 12640)
    return t'4
  let t'5 ← ModeRTL.option_is_enabled this (4 : Int32)
  return !t'5

/-- C++ `ModeAuto::use_pilot_yaw : bool () const`, `mode_auto.cpp:726-741`. -/
def ModeAuto.use_pilot_yaw (this : UInt64) : PMem.M Bool := do
  let t'1 ← PMem.ldU8 (this + 820)
  let sw'2 := t'1
  if sw'2 == (3 : UInt8) then
    let t'3 ← ModeLand.use_pilot_yaw ((0x86d8 : UInt64) /- &copter -/ + 12640)
    return t'3
  else if sw'2 == (4 : UInt8) then
    let t'4 ← ModeRTL.use_pilot_yaw ((0x86d8 : UInt64) /- &copter -/ + 12888)
    return t'4
  else if sw'2 == (7 : UInt8) then
    let t'5 ← ModeGuided.use_pilot_yaw ((0x86d8 : UInt64) /- &copter -/ + 12520)
    return t'5
  else
    let t'6 ← ModeAuto.option_is_enabled this (4 : Int32)
    return !t'6

/-- `Copter.is_tradheli` as a pure function of its arguments (it reads and writes no memory). -/
def Copter.is_tradheli.pure' (this : UInt64) : Id Bool := do
  return false

/-- C++ `Copter::is_tradheli : bool () const`, `system.cpp:567-574`. -/
def Copter.is_tradheli (this : UInt64) : PMem.M Bool :=
  pure (_root_.Vehicle_lib.Copter.is_tradheli.pure' this)

/-- C++ `Mode::get_pilot_desired_velocity : Vector2f (float) const`, `mode.cpp:578-605`. -/
def Mode.get_pilot_desired_velocity.body (fp : UInt64) (this : UInt64) (sret : UInt64) (vel_max : Binary32) : PMem.M Unit := do
  let mut vel_max := vel_max
  Vector2'float.Vector2 (fp + 0)
  let t'1 ← rc
  let t'2 ← RC_Channels_Copter.has_valid_input t'1
  if !t'2 then
    Vector2'float.Vector2'3 sret (fp + 0)
    return ()
  let t'3 ← PMem.ldU64 (this + 72)
  let t'4 ← PMem.ldU64 t'3
  let t'5 ← RC_Channel.norm_input_dz t'4
  PMem.stF32 (fp + 8) t'5
  let t'6 ← PMem.ldU64 (this + 80)
  let t'7 ← PMem.ldU64 t'6
  let t'8 ← RC_Channel.norm_input_dz t'7
  PMem.stF32 (fp + 16) t'8
  Mode.apply_simple_mode this (fp + 8) (fp + 16)
  let t'9 ← PMem.ldF32 (fp + 16)
  let t'10 ← PMem.ldF32 (fp + 8)
  Vector2'float.Vector2'2 (fp + 24) (-t'9) t'10
  discard <| PMem.memcpy (fp + 0) (fp + 24) 8
  discard <| pure ((fp + 0))
  let t'11 ← Vector2'float.is_zero (fp + 0)
  if t'11 then
    Vector2'float.Vector2'3 sret (fp + 0)
    return ()
  VehicleBridge.AP_AHRS.body_to_earth2D'1 ((0x86d8 : UInt64) /- &copter -/ + 4080) (fp + 32) (fp + 0)
  let t'12 := (fp + 32)
  discard <| PMem.memcpy (fp + 0) t'12 8
  discard <| pure ((fp + 0))
  let t'13 ← PMem.ldF32 (fp + 0)
  PMem.stF32 (fp + 48) (Binary32.abs t'13)
  let t'14 ← PMem.ldF32 ((fp + 0) + 4)
  PMem.stF32 (fp + 52) (Binary32.abs t'14)
  let t'15 ← MAX'float_float (fp + 48) (fp + 52)
  let t'16 ← PMem.ldF32 t'15
  Vector2'float.operator_'5 (fp + 0) (fp + 56) t'16
  let t'17 := (fp + 56)
  Vector2'float.Vector2'3 (fp + 40) t'17
  let t'18 ← Vector2'float.length (fp + 40)
  let t'19 ← Vector2'float.operator__'3 (fp + 0) (vel_max / t'18)
  discard <| pure (t'19)
  Vector2'float.Vector2'3 sret (fp + 0)
  return ()

def Mode.get_pilot_desired_velocity (this : UInt64) (sret : UInt64) (vel_max : Binary32) : PMem.M Unit := do
  let fp ← PMem.enter 64
  let r ← Mode.get_pilot_desired_velocity.body fp this sret vel_max
  PMem.leave fp
  return r

/-- C++ `ModeLand::get_land_alt_low_m : float () const`, `mode.h:1337-?`. -/
def ModeLand.get_land_alt_low_m (this : UInt64) : PMem.M Binary32 := do
  let t'1 ← AP_ParamTBase'float_4.get (this + 124)
  let t'2 ← PMem.ldF32 t'1
  return t'2

/-- C++ `ModeLand::get_land_speed_high_ms : float () const`, `mode.h:1336-?`. -/
def ModeLand.get_land_speed_high_ms (this : UInt64) : PMem.M Binary32 := do
  let t'1 ← AP_ParamTBase'float_4.get (this + 120)
  let t'2 ← PMem.ldF32 t'1
  return t'2

/-- C++ `ModeLand::get_land_speed_ms : float () const`, `mode.h:1335-?`. -/
def ModeLand.get_land_speed_ms (this : UInt64) : PMem.M Binary32 := do
  let t'1 ← AP_ParamTBase'float_4.get (this + 116)
  let t'2 ← PMem.ldF32 t'1
  return t'2

/-- `Copter.get_rangefinder_height_interpolated_m` as a pure function of its arguments (it reads and writes no memory). -/
def Copter.get_rangefinder_height_interpolated_m.pure' (this : UInt64) (height_m : UInt64) : Id Bool := do
  return false

/-- C++ `Copter::get_rangefinder_height_interpolated_m : bool (float &) const`, `sensors.cpp:71-78`. -/
def Copter.get_rangefinder_height_interpolated_m (this : UInt64) (height_m : UInt64) : PMem.M Bool :=
  pure (_root_.Vehicle_lib.Copter.get_rangefinder_height_interpolated_m.pure' this height_m)

/-- C++ `ModeRTL::hold_at_return_point_start : void ()`, `mode_rtl.cpp:297-305`. -/
def ModeRTL.hold_at_return_point_start (this : UInt64) : PMem.M Unit := do
  let t'1 ← Mode.AutoYaw.default_mode (0xeb78 : UInt64) /- &Mode::auto_yaw -/ true
  if (t'1 != (0 : Int32)) then
    Mode.AutoYaw.set_mode (0xeb78 : UInt64) /- &Mode::auto_yaw -/ (5 : Int32)
  else
    Mode.AutoYaw.set_mode (0xeb78 : UInt64) /- &Mode::auto_yaw -/ (0 : Int32)
  return ()

/-- C++ `ModeGuided::stabilizing_vel_NE : bool () const`, `mode_guided.cpp:664-667`. -/
def ModeGuided.stabilizing_vel_NE (this : UInt64) : PMem.M Bool := do
  let t'1 ← ModeGuided.option_is_enabled this (32 : UInt32)
  return !t'1

/-- C++ `ModeGuided::stabilizing_pos_NE : bool () const`, `mode_guided.cpp:658-661`. -/
def ModeGuided.stabilizing_pos_NE (this : UInt64) : PMem.M Bool := do
  let t'1 ← ModeGuided.option_is_enabled this (16 : UInt32)
  return !t'1

/-- C++ `Copter::rangefinder_alt_ok : bool () const`, `sensors.cpp:41-44`. -/
def Copter.rangefinder_alt_ok (this : UInt64) : PMem.M Bool := do
  let t'1 ← AP_SurfaceDistance.enabled_and_healthy (this + 8632)
  return t'1

/-- C++ `Copter::get_force_flying : bool () const`, `land_detector.cpp:327-335`. -/
def Copter.get_force_flying (this : UInt64) : PMem.M Bool := do
  let t'1 ← PMem.ldB (this + 9480)
  return t'1

/-- `Mode.crash_check_enabled` as a pure function of its arguments (it reads and writes no memory). -/
def Mode.crash_check_enabled.pure' (this : UInt64) : Id Bool := do
  return true

/-- C++ `Mode::crash_check_enabled : bool () const`, `AP_Common.h:139-?`. -/
def Mode.crash_check_enabled (this : UInt64) : PMem.M Bool :=
  pure (_root_.Vehicle_lib.Mode.crash_check_enabled.pure' this)

/-- C++ `Copter::option_is_enabled : bool (FlightOption) const`, `functor.h:636-638`. -/
def Copter.option_is_enabled (this : UInt64) (option : UInt32) : PMem.M Bool := do
  let mut option := option
  let t'1 ← AP_ParamT'unsigned_int_3.operator_const_unsigned_int__ ((this + 6840) + 1696)
  let t'2 ← PMem.ldU32 t'1
  return ((t'2 &&& option) != (Int32.toUInt32 ((0 : Int32))))

/-- C++ `Copter::set_failsafe_gcs : void (bool)`, `AP_State.cpp:73-79`. -/
def Copter.set_failsafe_gcs (this : UInt64) (b : Bool) : PMem.M Unit := do
  let mut b := b
  let t'1 := if b then (1 : UInt8) else (0 : UInt8)
  PMem.stBits (this + 9508) 73 1 (UInt8.toUInt64 (t'1))
  PMem.stB ((0xccc0 : UInt64) /- &AP_Notify::flags -/ + 12) b
  return ()

/-- `Mode.requires_terrain_failsafe` as a pure function of its arguments (it reads and writes no memory). -/
def Mode.requires_terrain_failsafe.pure' (this : UInt64) : Id Bool := do
  return false

/-- C++ `Mode::requires_terrain_failsafe : bool () const`, `AP_Common.h:168-?`. -/
def Mode.requires_terrain_failsafe (this : UInt64) : PMem.M Bool :=
  pure (_root_.Vehicle_lib.Mode.requires_terrain_failsafe.pure' this)

/-- `ModeAuto.requires_terrain_failsafe` as a pure function of its arguments (it reads and writes no memory). -/
def ModeAuto.requires_terrain_failsafe.pure' (this : UInt64) : Id Bool := do
  return true

/-- C++ `ModeAuto::requires_terrain_failsafe : bool () const`, `mode.h:599-?`. -/
def ModeAuto.requires_terrain_failsafe (this : UInt64) : PMem.M Bool :=
  pure (_root_.Vehicle_lib.ModeAuto.requires_terrain_failsafe.pure' this)

/-- `ModeGuided.requires_terrain_failsafe` as a pure function of its arguments (it reads and writes no memory). -/
def ModeGuided.requires_terrain_failsafe.pure' (this : UInt64) : Id Bool := do
  return true

/-- C++ `ModeGuided::requires_terrain_failsafe : bool () const`, `mode.h:1128-?`. -/
def ModeGuided.requires_terrain_failsafe (this : UInt64) : PMem.M Bool :=
  pure (_root_.Vehicle_lib.ModeGuided.requires_terrain_failsafe.pure' this)

/-- `ModeRTL.requires_terrain_failsafe` as a pure function of its arguments (it reads and writes no memory). -/
def ModeRTL.requires_terrain_failsafe.pure' (this : UInt64) : Id Bool := do
  return true

/-- C++ `ModeRTL::requires_terrain_failsafe : bool () const`, `mode.h:1529-?`. -/
def ModeRTL.requires_terrain_failsafe (this : UInt64) : PMem.M Bool :=
  pure (_root_.Vehicle_lib.ModeRTL.requires_terrain_failsafe.pure' this)

/-- `Copter.low_alt_avoidance` as a pure function of its arguments (it reads and writes no memory). -/
def Copter.low_alt_avoidance.pure' (this : UInt64) : Id Unit := do
  return ()

/-- C++ `Copter::low_alt_avoidance : void ()`, `avoidance.cpp:4-20`. -/
def Copter.low_alt_avoidance (this : UInt64) : PMem.M Unit :=
  pure (_root_.Vehicle_lib.Copter.low_alt_avoidance.pure' this)

/-- C++ `Copter::standby_update : void ()`, `standby.cpp:14-23`. -/
def Copter.standby_update (this : UInt64) : PMem.M Unit := do
  let t'1 ← PMem.ldB (this + 11229)
  if !t'1 then
    return ()
  let t'2 ← PMem.ldU64 (this + 11168)
  AC_AttitudeControl.reset_rate_controller_I_terms t'2
  let t'3 ← PMem.ldU64 (this + 11168)
  AC_AttitudeControl.reset_yaw_target_and_rate t'3 true
  let t'4 ← PMem.ldU64 (this + 11184)
  AC_PosControl.NED_standby_reset t'4
  return ()

/-- `Parameters.Parameters` as a pure function of its arguments (it reads and writes no memory). -/
def Parameters.Parameters.pure' (this : UInt64) : Id Unit := do
  _root_.Vehicle_lib.AP_Param.AP_Param'2.pure' (this + 0)
  _root_.Vehicle_lib.AP_Param.AP_Param'2.pure' (this + 4)
  _root_.Vehicle_lib.AP_Param.AP_Param'2.pure' (this + 8)
  _root_.Vehicle_lib.AP_Param.AP_Param'2.pure' (this + 12)
  _root_.Vehicle_lib.AP_Param.AP_Param'2.pure' (this + 16)
  _root_.Vehicle_lib.AP_Enum'ModeRTL_RTLAltType.AP_Enum.pure' (this + 20)
  _root_.Vehicle_lib.AP_Enum'Parameters_FS_GCS_Action.AP_Enum.pure' (this + 21)
  _root_.Vehicle_lib.AP_Param.AP_Param'2.pure' (this + 22)
  _root_.Vehicle_lib.AP_Param.AP_Param'2.pure' (this + 24)
  _root_.Vehicle_lib.AP_Enum'Parameters_WPYawBehavior.AP_Enum.pure' (this + 25)
  _root_.Vehicle_lib.AP_Enum'Parameters_FS_THR_Action.AP_Enum.pure' (this + 26)
  _root_.Vehicle_lib.AP_Param.AP_Param'2.pure' (this + 28)
  _root_.Vehicle_lib.AP_Param.AP_Param'2.pure' (this + 30)
  _root_.Vehicle_lib.AP_Param.AP_Param'2.pure' ((this + 32) + 0)
  _root_.Vehicle_lib.AP_Param.AP_Param'2.pure' ((this + 32) + 1)
  _root_.Vehicle_lib.AP_Param.AP_Param'2.pure' ((this + 32) + 2)
  _root_.Vehicle_lib.AP_Param.AP_Param'2.pure' ((this + 32) + 3)
  _root_.Vehicle_lib.AP_Param.AP_Param'2.pure' ((this + 32) + 4)
  _root_.Vehicle_lib.AP_Param.AP_Param'2.pure' ((this + 32) + 5)
  _root_.Vehicle_lib.AP_Param.AP_Param'2.pure' (this + 38)
  _root_.Vehicle_lib.AP_Param.AP_Param'2.pure' (this + 39)
  _root_.Vehicle_lib.AP_Param.AP_Param'2.pure' (this + 40)
  _root_.Vehicle_lib.AP_Param.AP_Param'2.pure' (this + 44)
  _root_.Vehicle_lib.AP_Param.AP_Param'2.pure' (this + 48)
  _root_.Vehicle_lib.AP_Param.AP_Param'2.pure' (this + 49)
  _root_.Vehicle_lib.AP_Param.AP_Param'2.pure' (this + 50)
  _root_.Vehicle_lib.AP_Param.AP_Param'2.pure' (this + 51)
  _root_.Vehicle_lib.AP_Enum'Parameters_FS_EKF_Action.AP_Enum.pure' (this + 52)
  _root_.Vehicle_lib.AP_Param.AP_Param'2.pure' (this + 53)
  _root_.Vehicle_lib.AP_Param.AP_Param'2.pure' (this + 56)
  _root_.Vehicle_lib.AP_Param.AP_Param'2.pure' (this + 60)
  _root_.Vehicle_lib.AP_Param.AP_Param'2.pure' (this + 62)
  return ()

/-- C++ `Parameters::Parameters : void ()`, `Parameters.h:512-514`. -/
def Parameters.Parameters (this : UInt64) : PMem.M Unit :=
  pure (_root_.Vehicle_lib.Parameters.Parameters.pure' this)

/-- C++ `RC_Channel_Copter::RC_Channel_Copter : void () noexcept(false)`, `RC_Channel_Copter.h:?-?`. -/
def RC_Channel_Copter.RC_Channel_Copter (this : UInt64) : PMem.M Unit := do
  RC_Channel.RC_Channel this
  return ()

/-- C++ `RC_Channels_Copter::RC_Channels_Copter : void () noexcept(false)`, `AP_Common.h:?-?`. -/
def RC_Channels_Copter.RC_Channels_Copter (this : UInt64) : PMem.M Unit := do
  RC_Channels.RC_Channels this
  RC_Channel_Copter.RC_Channel_Copter ((this + 48) + 0)
  RC_Channel_Copter.RC_Channel_Copter ((this + 48) + 56)
  RC_Channel_Copter.RC_Channel_Copter ((this + 48) + 112)
  RC_Channel_Copter.RC_Channel_Copter ((this + 48) + 168)
  RC_Channel_Copter.RC_Channel_Copter ((this + 48) + 224)
  RC_Channel_Copter.RC_Channel_Copter ((this + 48) + 280)
  RC_Channel_Copter.RC_Channel_Copter ((this + 48) + 336)
  RC_Channel_Copter.RC_Channel_Copter ((this + 48) + 392)
  RC_Channel_Copter.RC_Channel_Copter ((this + 48) + 448)
  RC_Channel_Copter.RC_Channel_Copter ((this + 48) + 504)
  RC_Channel_Copter.RC_Channel_Copter ((this + 48) + 560)
  RC_Channel_Copter.RC_Channel_Copter ((this + 48) + 616)
  RC_Channel_Copter.RC_Channel_Copter ((this + 48) + 672)
  RC_Channel_Copter.RC_Channel_Copter ((this + 48) + 728)
  RC_Channel_Copter.RC_Channel_Copter ((this + 48) + 784)
  RC_Channel_Copter.RC_Channel_Copter ((this + 48) + 840)
  return ()

/-- C++ `AP_Arming_Copter::AP_Arming_Copter : void ()`, `AP_Arming_Copter.h:11-16`. -/
def AP_Arming_Copter.AP_Arming_Copter.body (fp : UInt64) (this : UInt64) : PMem.M Unit := do
  AP_Arming.AP_Arming this
  PMem.stI8 (fp + 0) (UInt8.toInt8 ((Int8.toUInt8 (Int32.toInt8 ((1 : Int32))))))
  AP_ParamTBase'signed_char_1.set_default (this + 8) (fp + 0)
  return ()

def AP_Arming_Copter.AP_Arming_Copter (this : UInt64) : PMem.M Unit := do
  let fp ← PMem.enter 1
  let r ← AP_Arming_Copter.AP_Arming_Copter.body fp this
  PMem.leave fp
  return r

/-- `Copter.AHRSTrimming.AHRSTrimming` as a pure function of its arguments (it reads and writes no memory). -/
def Copter.AHRSTrimming.AHRSTrimming.pure' (this : UInt64) : Id Unit := do
  return ()

/-- C++ `Copter::AHRSTrimming::AHRSTrimming : void () noexcept`, `AP_Common.h:?-?`. -/
def Copter.AHRSTrimming.AHRSTrimming (this : UInt64) : PMem.M Unit :=
  pure (_root_.Vehicle_lib.Copter.AHRSTrimming.AHRSTrimming.pure' this)

/-- C++ `Mode::Mode : void ()`, `mode.cpp:11-25`. -/
def Mode.Mode (this : UInt64) : PMem.M Unit := do
  PMem.stU64 (this + 8) ((0x86d8 : UInt64) /- &copter -/ + 6776)
  PMem.stU64 (this + 16) ((0x86d8 : UInt64) /- &copter -/ + 6840)
  PMem.stU64 (this + 24) ((0x86d8 : UInt64) /- &copter -/ + 11192)
  PMem.stU64 (this + 32) ((0x86d8 : UInt64) /- &copter -/ + 11200)
  PMem.stU64 (this + 40) ((0x86d8 : UInt64) /- &copter -/ + 11184)
  PMem.stU64 (this + 48) ((0x86d8 : UInt64) /- &copter -/ + 4080)
  PMem.stU64 (this + 56) ((0x86d8 : UInt64) /- &copter -/ + 11168)
  PMem.stU64 (this + 64) ((0x86d8 : UInt64) /- &copter -/ + 9528)
  PMem.stU64 (this + 72) ((0x86d8 : UInt64) /- &copter -/ + 8600)
  PMem.stU64 (this + 80) ((0x86d8 : UInt64) /- &copter -/ + 8608)
  PMem.stU64 (this + 88) ((0x86d8 : UInt64) /- &copter -/ + 8616)
  PMem.stU64 (this + 96) ((0x86d8 : UInt64) /- &copter -/ + 8624)
  PMem.stU64 (this + 104) ((0x86d8 : UInt64) /- &copter -/ + 376)
  return ()

/-- C++ `ModeLand::ModeLand : void ()`, `mode_land.cpp:37-41`. -/
def ModeLand.ModeLand (this : UInt64) : PMem.M Unit := do
  Mode.Mode this
  AP_Param.AP_Param'2 (this + 116)
  AP_Param.AP_Param'2 (this + 120)
  AP_Param.AP_Param'2 (this + 124)
  AP_Param.setup_object_defaults this (0x8380 : UInt64) /- &ModeLand::var_info -/
  return ()

/-- C++ `_AutoTakeoff::_AutoTakeoff : void () noexcept(false)`, `mode.h:19-?`. -/
def _AutoTakeoff._AutoTakeoff (this : UInt64) : PMem.M Unit := do
  Vector3'double.Vector3 (this + 16)
  return ()

end Vehicle_lib
