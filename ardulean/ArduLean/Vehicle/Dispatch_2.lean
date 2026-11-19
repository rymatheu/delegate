import ArduLean.Runtime.GcsPort
import ArduLean.Vehicle.ArduCopter.ArduCopter
import ArduLean.Vehicle.mavlink.mavlink
import ArduLean.Vehicle.ArduCopter.ArduCopter_2

/-!
`Dispatch`: generated items without a C++ function of their own.

Items of `lean/Vehicle_lib.lean` (the vehicle translation), unchanged; placed by `tools/split_modules.py` (`ArduLean/Vehicle/INDEX.md`).
-/

open FloatLib.Floats (Binary32 Binary64)

set_option linter.unusedVariables false
set_option linter.unreachableTactic false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false

namespace Vehicle_lib

/-- Virtual calls of `Mode::throttle_hover() const` through a `Mode *`: by the object's address, over the member objects of `copter` whose class derives from Mode (9), each arm the final overrider of its class. -/
def vcall'Mode'throttle_hover'9 (this : UInt64) : PMem.M Binary32 := do
  if this == ((0x86d8 : UInt64) /- &copter -/ + 11256) then  -- copter.ModeAltHold
    Mode.throttle_hover this
  else if this == ((0x86d8 : UInt64) /- &copter -/ + 11368) then  -- copter.ModeAuto
    Mode.throttle_hover this
  else if this == ((0x86d8 : UInt64) /- &copter -/ + 12280) then  -- copter.ModeBrake
    Mode.throttle_hover this
  else if this == ((0x86d8 : UInt64) /- &copter -/ + 12400) then  -- copter.ModeCircle
    Mode.throttle_hover this
  else if this == ((0x86d8 : UInt64) /- &copter -/ + 12520) then  -- copter.ModeGuided
    Mode.throttle_hover this
  else if this == ((0x86d8 : UInt64) /- &copter -/ + 12640) then  -- copter.ModeLand
    Mode.throttle_hover this
  else if this == ((0x86d8 : UInt64) /- &copter -/ + 12776) then  -- copter.ModeLoiter
    Mode.throttle_hover this
  else if this == ((0x86d8 : UInt64) /- &copter -/ + 12888) then  -- copter.ModeRTL
    Mode.throttle_hover this
  else if this == ((0x86d8 : UInt64) /- &copter -/ + 13096) then  -- copter.ModeStabilize
    Mode.throttle_hover this
  else
    PMem.unreached "virtual Mode::throttle_hover on an object outside copter"
    return default

/-- Virtual calls of `Mode::set_speed_NE_ms(float)` through a `Mode *`: by the object's address, over the member objects of `copter` whose class derives from Mode (9), each arm the final overrider of its class. -/
def vcall'Mode'set_speed_NE_ms'19 (this : UInt64) (p0 : Binary32) : PMem.M Bool := do
  if this == ((0x86d8 : UInt64) /- &copter -/ + 11256) then  -- copter.ModeAltHold
    Mode.set_speed_NE_ms this p0
  else if this == ((0x86d8 : UInt64) /- &copter -/ + 11368) then  -- copter.ModeAuto
    ModeAuto.set_speed_NE_ms this p0
  else if this == ((0x86d8 : UInt64) /- &copter -/ + 12280) then  -- copter.ModeBrake
    Mode.set_speed_NE_ms this p0
  else if this == ((0x86d8 : UInt64) /- &copter -/ + 12400) then  -- copter.ModeCircle
    Mode.set_speed_NE_ms this p0
  else if this == ((0x86d8 : UInt64) /- &copter -/ + 12520) then  -- copter.ModeGuided
    ModeGuided.set_speed_NE_ms this p0
  else if this == ((0x86d8 : UInt64) /- &copter -/ + 12640) then  -- copter.ModeLand
    Mode.set_speed_NE_ms this p0
  else if this == ((0x86d8 : UInt64) /- &copter -/ + 12776) then  -- copter.ModeLoiter
    Mode.set_speed_NE_ms this p0
  else if this == ((0x86d8 : UInt64) /- &copter -/ + 12888) then  -- copter.ModeRTL
    ModeRTL.set_speed_NE_ms this p0
  else if this == ((0x86d8 : UInt64) /- &copter -/ + 13096) then  -- copter.ModeStabilize
    Mode.set_speed_NE_ms this p0
  else
    PMem.unreached "virtual Mode::set_speed_NE_ms on an object outside copter"
    return default

/-- Virtual calls of `Mode::set_speed_down_ms(float)` through a `Mode *`: by the object's address, over the member objects of `copter` whose class derives from Mode (9), each arm the final overrider of its class. -/
def vcall'Mode'set_speed_down_ms'21 (this : UInt64) (p0 : Binary32) : PMem.M Bool := do
  if this == ((0x86d8 : UInt64) /- &copter -/ + 11256) then  -- copter.ModeAltHold
    Mode.set_speed_down_ms this p0
  else if this == ((0x86d8 : UInt64) /- &copter -/ + 11368) then  -- copter.ModeAuto
    ModeAuto.set_speed_down_ms this p0
  else if this == ((0x86d8 : UInt64) /- &copter -/ + 12280) then  -- copter.ModeBrake
    Mode.set_speed_down_ms this p0
  else if this == ((0x86d8 : UInt64) /- &copter -/ + 12400) then  -- copter.ModeCircle
    Mode.set_speed_down_ms this p0
  else if this == ((0x86d8 : UInt64) /- &copter -/ + 12520) then  -- copter.ModeGuided
    ModeGuided.set_speed_down_ms this p0
  else if this == ((0x86d8 : UInt64) /- &copter -/ + 12640) then  -- copter.ModeLand
    Mode.set_speed_down_ms this p0
  else if this == ((0x86d8 : UInt64) /- &copter -/ + 12776) then  -- copter.ModeLoiter
    Mode.set_speed_down_ms this p0
  else if this == ((0x86d8 : UInt64) /- &copter -/ + 12888) then  -- copter.ModeRTL
    ModeRTL.set_speed_down_ms this p0
  else if this == ((0x86d8 : UInt64) /- &copter -/ + 13096) then  -- copter.ModeStabilize
    Mode.set_speed_down_ms this p0
  else
    PMem.unreached "virtual Mode::set_speed_down_ms on an object outside copter"
    return default

/-- Virtual calls of `Mode::set_speed_up_ms(float)` through a `Mode *`: by the object's address, over the member objects of `copter` whose class derives from Mode (9), each arm the final overrider of its class. -/
def vcall'Mode'set_speed_up_ms'20 (this : UInt64) (p0 : Binary32) : PMem.M Bool := do
  if this == ((0x86d8 : UInt64) /- &copter -/ + 11256) then  -- copter.ModeAltHold
    Mode.set_speed_up_ms this p0
  else if this == ((0x86d8 : UInt64) /- &copter -/ + 11368) then  -- copter.ModeAuto
    ModeAuto.set_speed_up_ms this p0
  else if this == ((0x86d8 : UInt64) /- &copter -/ + 12280) then  -- copter.ModeBrake
    Mode.set_speed_up_ms this p0
  else if this == ((0x86d8 : UInt64) /- &copter -/ + 12400) then  -- copter.ModeCircle
    Mode.set_speed_up_ms this p0
  else if this == ((0x86d8 : UInt64) /- &copter -/ + 12520) then  -- copter.ModeGuided
    ModeGuided.set_speed_up_ms this p0
  else if this == ((0x86d8 : UInt64) /- &copter -/ + 12640) then  -- copter.ModeLand
    Mode.set_speed_up_ms this p0
  else if this == ((0x86d8 : UInt64) /- &copter -/ + 12776) then  -- copter.ModeLoiter
    Mode.set_speed_up_ms this p0
  else if this == ((0x86d8 : UInt64) /- &copter -/ + 12888) then  -- copter.ModeRTL
    ModeRTL.set_speed_up_ms this p0
  else if this == ((0x86d8 : UInt64) /- &copter -/ + 13096) then  -- copter.ModeStabilize
    Mode.set_speed_up_ms this p0
  else
    PMem.unreached "virtual Mode::set_speed_up_ms on an object outside copter"
    return default

/-- Virtual calls of `Mode::do_user_takeoff_start_m(float)` through a `Mode *`: by the object's address, over the member objects of `copter` whose class derives from Mode (9), each arm the final overrider of its class. -/
def vcall'Mode'do_user_takeoff_start_m'25 (this : UInt64) (p0 : Binary32) : PMem.M Bool := do
  if this == ((0x86d8 : UInt64) /- &copter -/ + 11256) then  -- copter.ModeAltHold
    Mode.do_user_takeoff_start_m this p0
  else if this == ((0x86d8 : UInt64) /- &copter -/ + 11368) then  -- copter.ModeAuto
    Mode.do_user_takeoff_start_m this p0
  else if this == ((0x86d8 : UInt64) /- &copter -/ + 12280) then  -- copter.ModeBrake
    Mode.do_user_takeoff_start_m this p0
  else if this == ((0x86d8 : UInt64) /- &copter -/ + 12400) then  -- copter.ModeCircle
    Mode.do_user_takeoff_start_m this p0
  else if this == ((0x86d8 : UInt64) /- &copter -/ + 12520) then  -- copter.ModeGuided
    ModeGuided.do_user_takeoff_start_m this p0
  else if this == ((0x86d8 : UInt64) /- &copter -/ + 12640) then  -- copter.ModeLand
    Mode.do_user_takeoff_start_m this p0
  else if this == ((0x86d8 : UInt64) /- &copter -/ + 12776) then  -- copter.ModeLoiter
    Mode.do_user_takeoff_start_m this p0
  else if this == ((0x86d8 : UInt64) /- &copter -/ + 12888) then  -- copter.ModeRTL
    Mode.do_user_takeoff_start_m this p0
  else if this == ((0x86d8 : UInt64) /- &copter -/ + 13096) then  -- copter.ModeStabilize
    Mode.do_user_takeoff_start_m this p0
  else
    PMem.unreached "virtual Mode::do_user_takeoff_start_m on an object outside copter"
    return default

/-- Virtual calls of `Mode::get_wp(Location &) const` through a `Mode *`: by the object's address, over the member objects of `copter` whose class derives from Mode (9), each arm the final overrider of its class. -/
def vcall'Mode'get_wp'16 (this : UInt64) (p0 : UInt64) : PMem.M Bool := do
  if this == ((0x86d8 : UInt64) /- &copter -/ + 11256) then  -- copter.ModeAltHold
    Mode.get_wp this p0
  else if this == ((0x86d8 : UInt64) /- &copter -/ + 11368) then  -- copter.ModeAuto
    ModeAuto.get_wp this p0
  else if this == ((0x86d8 : UInt64) /- &copter -/ + 12280) then  -- copter.ModeBrake
    Mode.get_wp this p0
  else if this == ((0x86d8 : UInt64) /- &copter -/ + 12400) then  -- copter.ModeCircle
    Mode.get_wp this p0
  else if this == ((0x86d8 : UInt64) /- &copter -/ + 12520) then  -- copter.ModeGuided
    ModeGuided.get_wp this p0
  else if this == ((0x86d8 : UInt64) /- &copter -/ + 12640) then  -- copter.ModeLand
    Mode.get_wp this p0
  else if this == ((0x86d8 : UInt64) /- &copter -/ + 12776) then  -- copter.ModeLoiter
    Mode.get_wp this p0
  else if this == ((0x86d8 : UInt64) /- &copter -/ + 12888) then  -- copter.ModeRTL
    ModeRTL.get_wp this p0
  else if this == ((0x86d8 : UInt64) /- &copter -/ + 13096) then  -- copter.ModeStabilize
    Mode.get_wp this p0
  else
    PMem.unreached "virtual Mode::get_wp on an object outside copter"
    return default

/-- Virtual calls of `Mode::is_taking_off() const` through a `Mode *`: by the object's address, over the member objects of `copter` whose class derives from Mode (9), each arm the final overrider of its class. -/
def vcall'Mode'is_taking_off'17 (this : UInt64) : PMem.M Bool := do
  if this == ((0x86d8 : UInt64) /- &copter -/ + 11256) then  -- copter.ModeAltHold
    Mode.is_taking_off this
  else if this == ((0x86d8 : UInt64) /- &copter -/ + 11368) then  -- copter.ModeAuto
    ModeAuto.is_taking_off this
  else if this == ((0x86d8 : UInt64) /- &copter -/ + 12280) then  -- copter.ModeBrake
    Mode.is_taking_off this
  else if this == ((0x86d8 : UInt64) /- &copter -/ + 12400) then  -- copter.ModeCircle
    Mode.is_taking_off this
  else if this == ((0x86d8 : UInt64) /- &copter -/ + 12520) then  -- copter.ModeGuided
    ModeGuided.is_taking_off this
  else if this == ((0x86d8 : UInt64) /- &copter -/ + 12640) then  -- copter.ModeLand
    Mode.is_taking_off this
  else if this == ((0x86d8 : UInt64) /- &copter -/ + 12776) then  -- copter.ModeLoiter
    Mode.is_taking_off this
  else if this == ((0x86d8 : UInt64) /- &copter -/ + 12888) then  -- copter.ModeRTL
    Mode.is_taking_off this
  else if this == ((0x86d8 : UInt64) /- &copter -/ + 13096) then  -- copter.ModeStabilize
    Mode.is_taking_off this
  else
    PMem.unreached "virtual Mode::is_taking_off on an object outside copter"
    return default

/-- Calls through a function pointer of type `void (mavlink_channel_t, uint32_t, float, float, int16_t, int16_t)`: the functions whose address the program takes with this type (3). -/
def fnptr'2 (f : UInt64) (a0 : UInt32) (a1 : UInt32) (a2 : Binary32) (a3 : Binary32) (a4 : Int16) (a5 : Int16) : PMem.M Unit := do
  if f == 0x7f000020 then  -- mavlink_msg_scaled_pressure_send
    mavlink_msg_scaled_pressure_send a0 a1 a2 a3 a4 a5
  else if f == 0x7f000030 then  -- mavlink_msg_scaled_pressure2_send
    mavlink_msg_scaled_pressure2_send a0 a1 a2 a3 a4 a5
  else if f == 0x7f000040 then  -- mavlink_msg_scaled_pressure3_send
    mavlink_msg_scaled_pressure3_send a0 a1 a2 a3 a4 a5
  else
    PMem.unreached "function pointer void (mavlink_channel_t, uint32_t, float, float, int16_t, int16_t)"
    return ()

/-- Virtual calls of `Mode::get_alt_above_ground_m() const` through a `Mode *`: by the object's address, over the member objects of `copter` whose class derives from Mode (9), each arm the final overrider of its class. -/
def vcall'Mode'get_alt_above_ground_m'34 (this : UInt64) : PMem.M Binary32 := do
  if this == ((0x86d8 : UInt64) /- &copter -/ + 11256) then  -- copter.ModeAltHold
    Mode.get_alt_above_ground_m this
  else if this == ((0x86d8 : UInt64) /- &copter -/ + 11368) then  -- copter.ModeAuto
    ModeAuto.get_alt_above_ground_m this
  else if this == ((0x86d8 : UInt64) /- &copter -/ + 12280) then  -- copter.ModeBrake
    Mode.get_alt_above_ground_m this
  else if this == ((0x86d8 : UInt64) /- &copter -/ + 12400) then  -- copter.ModeCircle
    Mode.get_alt_above_ground_m this
  else if this == ((0x86d8 : UInt64) /- &copter -/ + 12520) then  -- copter.ModeGuided
    Mode.get_alt_above_ground_m this
  else if this == ((0x86d8 : UInt64) /- &copter -/ + 12640) then  -- copter.ModeLand
    Mode.get_alt_above_ground_m this
  else if this == ((0x86d8 : UInt64) /- &copter -/ + 12776) then  -- copter.ModeLoiter
    Mode.get_alt_above_ground_m this
  else if this == ((0x86d8 : UInt64) /- &copter -/ + 12888) then  -- copter.ModeRTL
    Mode.get_alt_above_ground_m this
  else if this == ((0x86d8 : UInt64) /- &copter -/ + 13096) then  -- copter.ModeStabilize
    Mode.get_alt_above_ground_m this
  else
    PMem.unreached "virtual Mode::get_alt_above_ground_m on an object outside copter"
    return default

end Vehicle_lib
