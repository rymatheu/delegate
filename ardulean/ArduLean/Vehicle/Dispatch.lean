import ArduLean.Runtime.GcsPort
import ArduLean.Vehicle.ArduCopter.ArduCopter

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

/-- Virtual calls of `Mode::in_guided_mode() const` through a `Mode *`: by the object's address, over the member objects of `copter` whose class derives from Mode (9), each arm the final overrider of its class. -/
def vcall'Mode'in_guided_mode'11 (this : UInt64) : PMem.M Bool := do
  if this == ((0x86d8 : UInt64) /- &copter -/ + 11256) then  -- copter.ModeAltHold
    Mode.in_guided_mode this
  else if this == ((0x86d8 : UInt64) /- &copter -/ + 11368) then  -- copter.ModeAuto
    ModeAuto.in_guided_mode this
  else if this == ((0x86d8 : UInt64) /- &copter -/ + 12280) then  -- copter.ModeBrake
    Mode.in_guided_mode this
  else if this == ((0x86d8 : UInt64) /- &copter -/ + 12400) then  -- copter.ModeCircle
    Mode.in_guided_mode this
  else if this == ((0x86d8 : UInt64) /- &copter -/ + 12520) then  -- copter.ModeGuided
    ModeGuided.in_guided_mode this
  else if this == ((0x86d8 : UInt64) /- &copter -/ + 12640) then  -- copter.ModeLand
    Mode.in_guided_mode this
  else if this == ((0x86d8 : UInt64) /- &copter -/ + 12776) then  -- copter.ModeLoiter
    Mode.in_guided_mode this
  else if this == ((0x86d8 : UInt64) /- &copter -/ + 12888) then  -- copter.ModeRTL
    Mode.in_guided_mode this
  else if this == ((0x86d8 : UInt64) /- &copter -/ + 13096) then  -- copter.ModeStabilize
    Mode.in_guided_mode this
  else
    PMem.unreached "virtual Mode::in_guided_mode on an object outside copter"
    return default

/-- Virtual calls of `Mode::is_autopilot() const` through a `Mode *`: by the object's address, over the member objects of `copter` whose class derives from Mode (9), each arm the final overrider of its class. -/
def vcall'Mode'is_autopilot'0 (this : UInt64) : PMem.M Bool := do
  if this == ((0x86d8 : UInt64) /- &copter -/ + 11256) then  -- copter.ModeAltHold
    ModeAltHold.is_autopilot this
  else if this == ((0x86d8 : UInt64) /- &copter -/ + 11368) then  -- copter.ModeAuto
    ModeAuto.is_autopilot this
  else if this == ((0x86d8 : UInt64) /- &copter -/ + 12280) then  -- copter.ModeBrake
    ModeBrake.is_autopilot this
  else if this == ((0x86d8 : UInt64) /- &copter -/ + 12400) then  -- copter.ModeCircle
    ModeCircle.is_autopilot this
  else if this == ((0x86d8 : UInt64) /- &copter -/ + 12520) then  -- copter.ModeGuided
    ModeGuided.is_autopilot this
  else if this == ((0x86d8 : UInt64) /- &copter -/ + 12640) then  -- copter.ModeLand
    ModeLand.is_autopilot this
  else if this == ((0x86d8 : UInt64) /- &copter -/ + 12776) then  -- copter.ModeLoiter
    ModeLoiter.is_autopilot this
  else if this == ((0x86d8 : UInt64) /- &copter -/ + 12888) then  -- copter.ModeRTL
    ModeRTL.is_autopilot this
  else if this == ((0x86d8 : UInt64) /- &copter -/ + 13096) then  -- copter.ModeStabilize
    ModeStabilize.is_autopilot this
  else
    PMem.unreached "virtual Mode::is_autopilot on an object outside copter"
    return default

/-- Virtual calls of `Mode::mode_number() const` through a `Mode *`: by the object's address, over the member objects of `copter` whose class derives from Mode (9), each arm the final overrider of its class. -/
def vcall'Mode'mode_number'1 (this : UInt64) : PMem.M UInt8 := do
  if this == ((0x86d8 : UInt64) /- &copter -/ + 11256) then  -- copter.ModeAltHold
    ModeAltHold.mode_number this
  else if this == ((0x86d8 : UInt64) /- &copter -/ + 11368) then  -- copter.ModeAuto
    ModeAuto.mode_number this
  else if this == ((0x86d8 : UInt64) /- &copter -/ + 12280) then  -- copter.ModeBrake
    ModeBrake.mode_number this
  else if this == ((0x86d8 : UInt64) /- &copter -/ + 12400) then  -- copter.ModeCircle
    ModeCircle.mode_number this
  else if this == ((0x86d8 : UInt64) /- &copter -/ + 12520) then  -- copter.ModeGuided
    ModeGuided.mode_number this
  else if this == ((0x86d8 : UInt64) /- &copter -/ + 12640) then  -- copter.ModeLand
    ModeLand.mode_number this
  else if this == ((0x86d8 : UInt64) /- &copter -/ + 12776) then  -- copter.ModeLoiter
    ModeLoiter.mode_number this
  else if this == ((0x86d8 : UInt64) /- &copter -/ + 12888) then  -- copter.ModeRTL
    ModeRTL.mode_number this
  else if this == ((0x86d8 : UInt64) /- &copter -/ + 13096) then  -- copter.ModeStabilize
    ModeStabilize.mode_number this
  else
    PMem.unreached "virtual Mode::mode_number on an object outside copter"
    return default

/-- Virtual calls of `Mode::name4() const` through a `Mode *`: by the object's address, over the member objects of `copter` whose class derives from Mode (9), each arm the final overrider of its class. -/
def vcall'Mode'name4'2 (this : UInt64) : PMem.M UInt64 := do
  if this == ((0x86d8 : UInt64) /- &copter -/ + 11256) then  -- copter.ModeAltHold
    ModeAltHold.name4 this
  else if this == ((0x86d8 : UInt64) /- &copter -/ + 11368) then  -- copter.ModeAuto
    ModeAuto.name4 this
  else if this == ((0x86d8 : UInt64) /- &copter -/ + 12280) then  -- copter.ModeBrake
    ModeBrake.name4 this
  else if this == ((0x86d8 : UInt64) /- &copter -/ + 12400) then  -- copter.ModeCircle
    ModeCircle.name4 this
  else if this == ((0x86d8 : UInt64) /- &copter -/ + 12520) then  -- copter.ModeGuided
    ModeGuided.name4 this
  else if this == ((0x86d8 : UInt64) /- &copter -/ + 12640) then  -- copter.ModeLand
    ModeLand.name4 this
  else if this == ((0x86d8 : UInt64) /- &copter -/ + 12776) then  -- copter.ModeLoiter
    ModeLoiter.name4 this
  else if this == ((0x86d8 : UInt64) /- &copter -/ + 12888) then  -- copter.ModeRTL
    ModeRTL.name4 this
  else if this == ((0x86d8 : UInt64) /- &copter -/ + 13096) then  -- copter.ModeStabilize
    ModeStabilize.name4 this
  else
    PMem.unreached "virtual Mode::name4 on an object outside copter"
    return default

/-- Virtual calls of `Mode::name() const` through a `Mode *`: by the object's address, over the member objects of `copter` whose class derives from Mode (9), each arm the final overrider of its class. -/
def vcall'Mode'name'8 (this : UInt64) : PMem.M UInt64 := do
  if this == ((0x86d8 : UInt64) /- &copter -/ + 11256) then  -- copter.ModeAltHold
    ModeAltHold.name this
  else if this == ((0x86d8 : UInt64) /- &copter -/ + 11368) then  -- copter.ModeAuto
    ModeAuto.name this
  else if this == ((0x86d8 : UInt64) /- &copter -/ + 12280) then  -- copter.ModeBrake
    ModeBrake.name this
  else if this == ((0x86d8 : UInt64) /- &copter -/ + 12400) then  -- copter.ModeCircle
    ModeCircle.name this
  else if this == ((0x86d8 : UInt64) /- &copter -/ + 12520) then  -- copter.ModeGuided
    ModeGuided.name this
  else if this == ((0x86d8 : UInt64) /- &copter -/ + 12640) then  -- copter.ModeLand
    ModeLand.name this
  else if this == ((0x86d8 : UInt64) /- &copter -/ + 12776) then  -- copter.ModeLoiter
    ModeLoiter.name this
  else if this == ((0x86d8 : UInt64) /- &copter -/ + 12888) then  -- copter.ModeRTL
    ModeRTL.name this
  else if this == ((0x86d8 : UInt64) /- &copter -/ + 13096) then  -- copter.ModeStabilize
    ModeStabilize.name this
  else
    PMem.unreached "virtual Mode::name on an object outside copter"
    return default

/-- Virtual calls of `Mode::allows_arming(AP_Arming::Method) const` through a `Mode *`: by the object's address, over the member objects of `copter` whose class derives from Mode (9), each arm the final overrider of its class. -/
def vcall'Mode'allows_arming'4 (this : UInt64) (p0 : Int32) : PMem.M Bool := do
  if this == ((0x86d8 : UInt64) /- &copter -/ + 11256) then  -- copter.ModeAltHold
    ModeAltHold.allows_arming this p0
  else if this == ((0x86d8 : UInt64) /- &copter -/ + 11368) then  -- copter.ModeAuto
    ModeAuto.allows_arming this p0
  else if this == ((0x86d8 : UInt64) /- &copter -/ + 12280) then  -- copter.ModeBrake
    ModeBrake.allows_arming this p0
  else if this == ((0x86d8 : UInt64) /- &copter -/ + 12400) then  -- copter.ModeCircle
    ModeCircle.allows_arming this p0
  else if this == ((0x86d8 : UInt64) /- &copter -/ + 12520) then  -- copter.ModeGuided
    ModeGuided.allows_arming this p0
  else if this == ((0x86d8 : UInt64) /- &copter -/ + 12640) then  -- copter.ModeLand
    ModeLand.allows_arming this p0
  else if this == ((0x86d8 : UInt64) /- &copter -/ + 12776) then  -- copter.ModeLoiter
    ModeLoiter.allows_arming this p0
  else if this == ((0x86d8 : UInt64) /- &copter -/ + 12888) then  -- copter.ModeRTL
    ModeRTL.allows_arming this p0
  else if this == ((0x86d8 : UInt64) /- &copter -/ + 13096) then  -- copter.ModeStabilize
    ModeStabilize.allows_arming this p0
  else
    PMem.unreached "virtual Mode::allows_arming on an object outside copter"
    return default

/-- Virtual calls of `Mode::has_manual_throttle() const` through a `Mode *`: by the object's address, over the member objects of `copter` whose class derives from Mode (9), each arm the final overrider of its class. -/
def vcall'Mode'has_manual_throttle'3 (this : UInt64) : PMem.M Bool := do
  if this == ((0x86d8 : UInt64) /- &copter -/ + 11256) then  -- copter.ModeAltHold
    ModeAltHold.has_manual_throttle this
  else if this == ((0x86d8 : UInt64) /- &copter -/ + 11368) then  -- copter.ModeAuto
    ModeAuto.has_manual_throttle this
  else if this == ((0x86d8 : UInt64) /- &copter -/ + 12280) then  -- copter.ModeBrake
    ModeBrake.has_manual_throttle this
  else if this == ((0x86d8 : UInt64) /- &copter -/ + 12400) then  -- copter.ModeCircle
    ModeCircle.has_manual_throttle this
  else if this == ((0x86d8 : UInt64) /- &copter -/ + 12520) then  -- copter.ModeGuided
    ModeGuided.has_manual_throttle this
  else if this == ((0x86d8 : UInt64) /- &copter -/ + 12640) then  -- copter.ModeLand
    ModeLand.has_manual_throttle this
  else if this == ((0x86d8 : UInt64) /- &copter -/ + 12776) then  -- copter.ModeLoiter
    ModeLoiter.has_manual_throttle this
  else if this == ((0x86d8 : UInt64) /- &copter -/ + 12888) then  -- copter.ModeRTL
    ModeRTL.has_manual_throttle this
  else if this == ((0x86d8 : UInt64) /- &copter -/ + 13096) then  -- copter.ModeStabilize
    ModeStabilize.has_manual_throttle this
  else
    PMem.unreached "virtual Mode::has_manual_throttle on an object outside copter"
    return default

/-- Calls through a function pointer of type `void (void *, float *, unsigned char)`: the functions whose address the program takes with this type (0). -/
def fnptr'1 (f : UInt64) (a0 : UInt64) (a1 : UInt64) (a2 : UInt8) : PMem.M Unit := do
  PMem.unreached "function pointer void (void *, float *, unsigned char)"
  return ()

/-- Virtual calls of `Mode::requires_position() const` through a `Mode *`: by the object's address, over the member objects of `copter` whose class derives from Mode (9), each arm the final overrider of its class. -/
def vcall'Mode'requires_position'5 (this : UInt64) : PMem.M Bool := do
  if this == ((0x86d8 : UInt64) /- &copter -/ + 11256) then  -- copter.ModeAltHold
    ModeAltHold.requires_position this
  else if this == ((0x86d8 : UInt64) /- &copter -/ + 11368) then  -- copter.ModeAuto
    ModeAuto.requires_position this
  else if this == ((0x86d8 : UInt64) /- &copter -/ + 12280) then  -- copter.ModeBrake
    ModeBrake.requires_position this
  else if this == ((0x86d8 : UInt64) /- &copter -/ + 12400) then  -- copter.ModeCircle
    ModeCircle.requires_position this
  else if this == ((0x86d8 : UInt64) /- &copter -/ + 12520) then  -- copter.ModeGuided
    ModeGuided.requires_position this
  else if this == ((0x86d8 : UInt64) /- &copter -/ + 12640) then  -- copter.ModeLand
    ModeLand.requires_position this
  else if this == ((0x86d8 : UInt64) /- &copter -/ + 12776) then  -- copter.ModeLoiter
    ModeLoiter.requires_position this
  else if this == ((0x86d8 : UInt64) /- &copter -/ + 12888) then  -- copter.ModeRTL
    ModeRTL.requires_position this
  else if this == ((0x86d8 : UInt64) /- &copter -/ + 13096) then  -- copter.ModeStabilize
    ModeStabilize.requires_position this
  else
    PMem.unreached "virtual Mode::requires_position on an object outside copter"
    return default

/-- Virtual calls of `Mode::allows_GCS_or_SCR_arming_with_throttle_high() const` through a `Mode *`: by the object's address, over the member objects of `copter` whose class derives from Mode (9), each arm the final overrider of its class. -/
def vcall'Mode'allows_GCS_or_SCR_arming_with_throttle_high'27 (this : UInt64) : PMem.M Bool := do
  if this == ((0x86d8 : UInt64) /- &copter -/ + 11256) then  -- copter.ModeAltHold
    Mode.allows_GCS_or_SCR_arming_with_throttle_high this
  else if this == ((0x86d8 : UInt64) /- &copter -/ + 11368) then  -- copter.ModeAuto
    ModeAuto.allows_GCS_or_SCR_arming_with_throttle_high this
  else if this == ((0x86d8 : UInt64) /- &copter -/ + 12280) then  -- copter.ModeBrake
    Mode.allows_GCS_or_SCR_arming_with_throttle_high this
  else if this == ((0x86d8 : UInt64) /- &copter -/ + 12400) then  -- copter.ModeCircle
    Mode.allows_GCS_or_SCR_arming_with_throttle_high this
  else if this == ((0x86d8 : UInt64) /- &copter -/ + 12520) then  -- copter.ModeGuided
    ModeGuided.allows_GCS_or_SCR_arming_with_throttle_high this
  else if this == ((0x86d8 : UInt64) /- &copter -/ + 12640) then  -- copter.ModeLand
    Mode.allows_GCS_or_SCR_arming_with_throttle_high this
  else if this == ((0x86d8 : UInt64) /- &copter -/ + 12776) then  -- copter.ModeLoiter
    Mode.allows_GCS_or_SCR_arming_with_throttle_high this
  else if this == ((0x86d8 : UInt64) /- &copter -/ + 12888) then  -- copter.ModeRTL
    Mode.allows_GCS_or_SCR_arming_with_throttle_high this
  else if this == ((0x86d8 : UInt64) /- &copter -/ + 13096) then  -- copter.ModeStabilize
    Mode.allows_GCS_or_SCR_arming_with_throttle_high this
  else
    PMem.unreached "virtual Mode::allows_GCS_or_SCR_arming_with_throttle_high on an object outside copter"
    return default

/-- Virtual calls of `Mode::allows_save_trim() const` through a `Mode *`: by the object's address, over the member objects of `copter` whose class derives from Mode (9), each arm the final overrider of its class. -/
def vcall'Mode'allows_save_trim'26 (this : UInt64) : PMem.M Bool := do
  if this == ((0x86d8 : UInt64) /- &copter -/ + 11256) then  -- copter.ModeAltHold
    ModeAltHold.allows_save_trim this
  else if this == ((0x86d8 : UInt64) /- &copter -/ + 11368) then  -- copter.ModeAuto
    Mode.allows_save_trim this
  else if this == ((0x86d8 : UInt64) /- &copter -/ + 12280) then  -- copter.ModeBrake
    Mode.allows_save_trim this
  else if this == ((0x86d8 : UInt64) /- &copter -/ + 12400) then  -- copter.ModeCircle
    Mode.allows_save_trim this
  else if this == ((0x86d8 : UInt64) /- &copter -/ + 12520) then  -- copter.ModeGuided
    Mode.allows_save_trim this
  else if this == ((0x86d8 : UInt64) /- &copter -/ + 12640) then  -- copter.ModeLand
    Mode.allows_save_trim this
  else if this == ((0x86d8 : UInt64) /- &copter -/ + 12776) then  -- copter.ModeLoiter
    Mode.allows_save_trim this
  else if this == ((0x86d8 : UInt64) /- &copter -/ + 12888) then  -- copter.ModeRTL
    Mode.allows_save_trim this
  else if this == ((0x86d8 : UInt64) /- &copter -/ + 13096) then  -- copter.ModeStabilize
    ModeStabilize.allows_save_trim this
  else
    PMem.unreached "virtual Mode::allows_save_trim on an object outside copter"
    return default

/-- Virtual calls of `Mode::pause()` through a `Mode *`: by the object's address, over the member objects of `copter` whose class derives from Mode (9), each arm the final overrider of its class. -/
def vcall'Mode'pause'22 (this : UInt64) : PMem.M Bool := do
  if this == ((0x86d8 : UInt64) /- &copter -/ + 11256) then  -- copter.ModeAltHold
    Mode.pause this
  else if this == ((0x86d8 : UInt64) /- &copter -/ + 11368) then  -- copter.ModeAuto
    ModeAuto.pause this
  else if this == ((0x86d8 : UInt64) /- &copter -/ + 12280) then  -- copter.ModeBrake
    Mode.pause this
  else if this == ((0x86d8 : UInt64) /- &copter -/ + 12400) then  -- copter.ModeCircle
    Mode.pause this
  else if this == ((0x86d8 : UInt64) /- &copter -/ + 12520) then  -- copter.ModeGuided
    ModeGuided.pause this
  else if this == ((0x86d8 : UInt64) /- &copter -/ + 12640) then  -- copter.ModeLand
    Mode.pause this
  else if this == ((0x86d8 : UInt64) /- &copter -/ + 12776) then  -- copter.ModeLoiter
    Mode.pause this
  else if this == ((0x86d8 : UInt64) /- &copter -/ + 12888) then  -- copter.ModeRTL
    Mode.pause this
  else if this == ((0x86d8 : UInt64) /- &copter -/ + 13096) then  -- copter.ModeStabilize
    Mode.pause this
  else
    PMem.unreached "virtual Mode::pause on an object outside copter"
    return default

/-- Virtual calls of `Mode::resume()` through a `Mode *`: by the object's address, over the member objects of `copter` whose class derives from Mode (9), each arm the final overrider of its class. -/
def vcall'Mode'resume'23 (this : UInt64) : PMem.M Bool := do
  if this == ((0x86d8 : UInt64) /- &copter -/ + 11256) then  -- copter.ModeAltHold
    Mode.resume this
  else if this == ((0x86d8 : UInt64) /- &copter -/ + 11368) then  -- copter.ModeAuto
    ModeAuto.resume this
  else if this == ((0x86d8 : UInt64) /- &copter -/ + 12280) then  -- copter.ModeBrake
    Mode.resume this
  else if this == ((0x86d8 : UInt64) /- &copter -/ + 12400) then  -- copter.ModeCircle
    Mode.resume this
  else if this == ((0x86d8 : UInt64) /- &copter -/ + 12520) then  -- copter.ModeGuided
    ModeGuided.resume this
  else if this == ((0x86d8 : UInt64) /- &copter -/ + 12640) then  -- copter.ModeLand
    Mode.resume this
  else if this == ((0x86d8 : UInt64) /- &copter -/ + 12776) then  -- copter.ModeLoiter
    Mode.resume this
  else if this == ((0x86d8 : UInt64) /- &copter -/ + 12888) then  -- copter.ModeRTL
    Mode.resume this
  else if this == ((0x86d8 : UInt64) /- &copter -/ + 13096) then  -- copter.ModeStabilize
    Mode.resume this
  else
    PMem.unreached "virtual Mode::resume on an object outside copter"
    return default

/-- Virtual calls of `Mode::exit()` through a `Mode *`: by the object's address, over the member objects of `copter` whose class derives from Mode (9), each arm the final overrider of its class. -/
def vcall'Mode'exit'10 (this : UInt64) : PMem.M Unit := do
  if this == ((0x86d8 : UInt64) /- &copter -/ + 11256) then  -- copter.ModeAltHold
    Mode.exit this
  else if this == ((0x86d8 : UInt64) /- &copter -/ + 11368) then  -- copter.ModeAuto
    ModeAuto.exit this
  else if this == ((0x86d8 : UInt64) /- &copter -/ + 12280) then  -- copter.ModeBrake
    Mode.exit this
  else if this == ((0x86d8 : UInt64) /- &copter -/ + 12400) then  -- copter.ModeCircle
    Mode.exit this
  else if this == ((0x86d8 : UInt64) /- &copter -/ + 12520) then  -- copter.ModeGuided
    Mode.exit this
  else if this == ((0x86d8 : UInt64) /- &copter -/ + 12640) then  -- copter.ModeLand
    Mode.exit this
  else if this == ((0x86d8 : UInt64) /- &copter -/ + 12776) then  -- copter.ModeLoiter
    Mode.exit this
  else if this == ((0x86d8 : UInt64) /- &copter -/ + 12888) then  -- copter.ModeRTL
    Mode.exit this
  else if this == ((0x86d8 : UInt64) /- &copter -/ + 13096) then  -- copter.ModeStabilize
    Mode.exit this
  else
    PMem.unreached "virtual Mode::exit on an object outside copter"
    return ()

/-- Virtual calls of `Mode::allows_entry_in_rc_failsafe() const` through a `Mode *`: by the object's address, over the member objects of `copter` whose class derives from Mode (9), each arm the final overrider of its class. -/
def vcall'Mode'allows_entry_in_rc_failsafe'6 (this : UInt64) : PMem.M Bool := do
  if this == ((0x86d8 : UInt64) /- &copter -/ + 11256) then  -- copter.ModeAltHold
    Mode.allows_entry_in_rc_failsafe this
  else if this == ((0x86d8 : UInt64) /- &copter -/ + 11368) then  -- copter.ModeAuto
    Mode.allows_entry_in_rc_failsafe this
  else if this == ((0x86d8 : UInt64) /- &copter -/ + 12280) then  -- copter.ModeBrake
    Mode.allows_entry_in_rc_failsafe this
  else if this == ((0x86d8 : UInt64) /- &copter -/ + 12400) then  -- copter.ModeCircle
    Mode.allows_entry_in_rc_failsafe this
  else if this == ((0x86d8 : UInt64) /- &copter -/ + 12520) then  -- copter.ModeGuided
    Mode.allows_entry_in_rc_failsafe this
  else if this == ((0x86d8 : UInt64) /- &copter -/ + 12640) then  -- copter.ModeLand
    Mode.allows_entry_in_rc_failsafe this
  else if this == ((0x86d8 : UInt64) /- &copter -/ + 12776) then  -- copter.ModeLoiter
    Mode.allows_entry_in_rc_failsafe this
  else if this == ((0x86d8 : UInt64) /- &copter -/ + 12888) then  -- copter.ModeRTL
    Mode.allows_entry_in_rc_failsafe this
  else if this == ((0x86d8 : UInt64) /- &copter -/ + 13096) then  -- copter.ModeStabilize
    ModeStabilize.allows_entry_in_rc_failsafe this
  else
    PMem.unreached "virtual Mode::allows_entry_in_rc_failsafe on an object outside copter"
    return default

/-- Virtual calls of `Mode::has_user_takeoff(bool) const` through a `Mode *`: by the object's address, over the member objects of `copter` whose class derives from Mode (9), each arm the final overrider of its class. -/
def vcall'Mode'has_user_takeoff'24 (this : UInt64) (p0 : Bool) : PMem.M Bool := do
  if this == ((0x86d8 : UInt64) /- &copter -/ + 11256) then  -- copter.ModeAltHold
    ModeAltHold.has_user_takeoff this p0
  else if this == ((0x86d8 : UInt64) /- &copter -/ + 11368) then  -- copter.ModeAuto
    Mode.has_user_takeoff this p0
  else if this == ((0x86d8 : UInt64) /- &copter -/ + 12280) then  -- copter.ModeBrake
    Mode.has_user_takeoff this p0
  else if this == ((0x86d8 : UInt64) /- &copter -/ + 12400) then  -- copter.ModeCircle
    Mode.has_user_takeoff this p0
  else if this == ((0x86d8 : UInt64) /- &copter -/ + 12520) then  -- copter.ModeGuided
    ModeGuided.has_user_takeoff this p0
  else if this == ((0x86d8 : UInt64) /- &copter -/ + 12640) then  -- copter.ModeLand
    Mode.has_user_takeoff this p0
  else if this == ((0x86d8 : UInt64) /- &copter -/ + 12776) then  -- copter.ModeLoiter
    ModeLoiter.has_user_takeoff this p0
  else if this == ((0x86d8 : UInt64) /- &copter -/ + 12888) then  -- copter.ModeRTL
    Mode.has_user_takeoff this p0
  else if this == ((0x86d8 : UInt64) /- &copter -/ + 13096) then  -- copter.ModeStabilize
    Mode.has_user_takeoff this p0
  else
    PMem.unreached "virtual Mode::has_user_takeoff on an object outside copter"
    return default

/-- Virtual calls of `Mode::is_landing() const` through a `Mode *`: by the object's address, over the member objects of `copter` whose class derives from Mode (9), each arm the final overrider of its class. -/
def vcall'Mode'is_landing'15 (this : UInt64) : PMem.M Bool := do
  if this == ((0x86d8 : UInt64) /- &copter -/ + 11256) then  -- copter.ModeAltHold
    Mode.is_landing this
  else if this == ((0x86d8 : UInt64) /- &copter -/ + 11368) then  -- copter.ModeAuto
    ModeAuto.is_landing this
  else if this == ((0x86d8 : UInt64) /- &copter -/ + 12280) then  -- copter.ModeBrake
    Mode.is_landing this
  else if this == ((0x86d8 : UInt64) /- &copter -/ + 12400) then  -- copter.ModeCircle
    Mode.is_landing this
  else if this == ((0x86d8 : UInt64) /- &copter -/ + 12520) then  -- copter.ModeGuided
    Mode.is_landing this
  else if this == ((0x86d8 : UInt64) /- &copter -/ + 12640) then  -- copter.ModeLand
    ModeLand.is_landing this
  else if this == ((0x86d8 : UInt64) /- &copter -/ + 12776) then  -- copter.ModeLoiter
    Mode.is_landing this
  else if this == ((0x86d8 : UInt64) /- &copter -/ + 12888) then  -- copter.ModeRTL
    ModeRTL.is_landing this
  else if this == ((0x86d8 : UInt64) /- &copter -/ + 13096) then  -- copter.ModeStabilize
    Mode.is_landing this
  else
    PMem.unreached "virtual Mode::is_landing on an object outside copter"
    return default

/-- Virtual calls of `Mode::crosstrack_error_m() const` through a `Mode *`: by the object's address, over the member objects of `copter` whose class derives from Mode (9), each arm the final overrider of its class. -/
def vcall'Mode'crosstrack_error_m'14 (this : UInt64) : PMem.M Binary32 := do
  if this == ((0x86d8 : UInt64) /- &copter -/ + 11256) then  -- copter.ModeAltHold
    Mode.crosstrack_error_m this
  else if this == ((0x86d8 : UInt64) /- &copter -/ + 11368) then  -- copter.ModeAuto
    ModeAuto.crosstrack_error_m this
  else if this == ((0x86d8 : UInt64) /- &copter -/ + 12280) then  -- copter.ModeBrake
    Mode.crosstrack_error_m this
  else if this == ((0x86d8 : UInt64) /- &copter -/ + 12400) then  -- copter.ModeCircle
    Mode.crosstrack_error_m this
  else if this == ((0x86d8 : UInt64) /- &copter -/ + 12520) then  -- copter.ModeGuided
    ModeGuided.crosstrack_error_m this
  else if this == ((0x86d8 : UInt64) /- &copter -/ + 12640) then  -- copter.ModeLand
    Mode.crosstrack_error_m this
  else if this == ((0x86d8 : UInt64) /- &copter -/ + 12776) then  -- copter.ModeLoiter
    ModeLoiter.crosstrack_error_m this
  else if this == ((0x86d8 : UInt64) /- &copter -/ + 12888) then  -- copter.ModeRTL
    ModeRTL.crosstrack_error_m this
  else if this == ((0x86d8 : UInt64) /- &copter -/ + 13096) then  -- copter.ModeStabilize
    Mode.crosstrack_error_m this
  else
    PMem.unreached "virtual Mode::crosstrack_error_m on an object outside copter"
    return default

/-- Virtual calls of `Mode::wp_bearing_deg() const` through a `Mode *`: by the object's address, over the member objects of `copter` whose class derives from Mode (9), each arm the final overrider of its class. -/
def vcall'Mode'wp_bearing_deg'12 (this : UInt64) : PMem.M Binary32 := do
  if this == ((0x86d8 : UInt64) /- &copter -/ + 11256) then  -- copter.ModeAltHold
    Mode.wp_bearing_deg this
  else if this == ((0x86d8 : UInt64) /- &copter -/ + 11368) then  -- copter.ModeAuto
    ModeAuto.wp_bearing_deg this
  else if this == ((0x86d8 : UInt64) /- &copter -/ + 12280) then  -- copter.ModeBrake
    Mode.wp_bearing_deg this
  else if this == ((0x86d8 : UInt64) /- &copter -/ + 12400) then  -- copter.ModeCircle
    ModeCircle.wp_bearing_deg this
  else if this == ((0x86d8 : UInt64) /- &copter -/ + 12520) then  -- copter.ModeGuided
    ModeGuided.wp_bearing_deg this
  else if this == ((0x86d8 : UInt64) /- &copter -/ + 12640) then  -- copter.ModeLand
    Mode.wp_bearing_deg this
  else if this == ((0x86d8 : UInt64) /- &copter -/ + 12776) then  -- copter.ModeLoiter
    ModeLoiter.wp_bearing_deg this
  else if this == ((0x86d8 : UInt64) /- &copter -/ + 12888) then  -- copter.ModeRTL
    ModeRTL.wp_bearing_deg this
  else if this == ((0x86d8 : UInt64) /- &copter -/ + 13096) then  -- copter.ModeStabilize
    Mode.wp_bearing_deg this
  else
    PMem.unreached "virtual Mode::wp_bearing_deg on an object outside copter"
    return default

/-- Virtual calls of `Mode::wp_distance_m() const` through a `Mode *`: by the object's address, over the member objects of `copter` whose class derives from Mode (9), each arm the final overrider of its class. -/
def vcall'Mode'wp_distance_m'13 (this : UInt64) : PMem.M Binary32 := do
  if this == ((0x86d8 : UInt64) /- &copter -/ + 11256) then  -- copter.ModeAltHold
    Mode.wp_distance_m this
  else if this == ((0x86d8 : UInt64) /- &copter -/ + 11368) then  -- copter.ModeAuto
    ModeAuto.wp_distance_m this
  else if this == ((0x86d8 : UInt64) /- &copter -/ + 12280) then  -- copter.ModeBrake
    Mode.wp_distance_m this
  else if this == ((0x86d8 : UInt64) /- &copter -/ + 12400) then  -- copter.ModeCircle
    ModeCircle.wp_distance_m this
  else if this == ((0x86d8 : UInt64) /- &copter -/ + 12520) then  -- copter.ModeGuided
    ModeGuided.wp_distance_m this
  else if this == ((0x86d8 : UInt64) /- &copter -/ + 12640) then  -- copter.ModeLand
    Mode.wp_distance_m this
  else if this == ((0x86d8 : UInt64) /- &copter -/ + 12776) then  -- copter.ModeLoiter
    ModeLoiter.wp_distance_m this
  else if this == ((0x86d8 : UInt64) /- &copter -/ + 12888) then  -- copter.ModeRTL
    ModeRTL.wp_distance_m this
  else if this == ((0x86d8 : UInt64) /- &copter -/ + 13096) then  -- copter.ModeStabilize
    Mode.wp_distance_m this
  else
    PMem.unreached "virtual Mode::wp_distance_m on an object outside copter"
    return default

/-- Virtual calls of `Mode::enabled() const` through a `Mode *`: by the object's address, over the member objects of `copter` whose class derives from Mode (9), each arm the final overrider of its class. -/
def vcall'Mode'enabled'18 (this : UInt64) : PMem.M Bool := do
  if this == ((0x86d8 : UInt64) /- &copter -/ + 11256) then  -- copter.ModeAltHold
    Mode.enabled this
  else if this == ((0x86d8 : UInt64) /- &copter -/ + 11368) then  -- copter.ModeAuto
    Mode.enabled this
  else if this == ((0x86d8 : UInt64) /- &copter -/ + 12280) then  -- copter.ModeBrake
    Mode.enabled this
  else if this == ((0x86d8 : UInt64) /- &copter -/ + 12400) then  -- copter.ModeCircle
    Mode.enabled this
  else if this == ((0x86d8 : UInt64) /- &copter -/ + 12520) then  -- copter.ModeGuided
    Mode.enabled this
  else if this == ((0x86d8 : UInt64) /- &copter -/ + 12640) then  -- copter.ModeLand
    Mode.enabled this
  else if this == ((0x86d8 : UInt64) /- &copter -/ + 12776) then  -- copter.ModeLoiter
    Mode.enabled this
  else if this == ((0x86d8 : UInt64) /- &copter -/ + 12888) then  -- copter.ModeRTL
    Mode.enabled this
  else if this == ((0x86d8 : UInt64) /- &copter -/ + 13096) then  -- copter.ModeStabilize
    Mode.enabled this
  else
    PMem.unreached "virtual Mode::enabled on an object outside copter"
    return default

/-- Virtual calls of `Mode::move_vehicle_on_ekf_reset() const` through a `Mode *`: by the object's address, over the member objects of `copter` whose class derives from Mode (9), each arm the final overrider of its class. -/
def vcall'Mode'move_vehicle_on_ekf_reset'28 (this : UInt64) : PMem.M Bool := do
  if this == ((0x86d8 : UInt64) /- &copter -/ + 11256) then  -- copter.ModeAltHold
    Mode.move_vehicle_on_ekf_reset this
  else if this == ((0x86d8 : UInt64) /- &copter -/ + 11368) then  -- copter.ModeAuto
    ModeAuto.move_vehicle_on_ekf_reset this
  else if this == ((0x86d8 : UInt64) /- &copter -/ + 12280) then  -- copter.ModeBrake
    Mode.move_vehicle_on_ekf_reset this
  else if this == ((0x86d8 : UInt64) /- &copter -/ + 12400) then  -- copter.ModeCircle
    Mode.move_vehicle_on_ekf_reset this
  else if this == ((0x86d8 : UInt64) /- &copter -/ + 12520) then  -- copter.ModeGuided
    ModeGuided.move_vehicle_on_ekf_reset this
  else if this == ((0x86d8 : UInt64) /- &copter -/ + 12640) then  -- copter.ModeLand
    Mode.move_vehicle_on_ekf_reset this
  else if this == ((0x86d8 : UInt64) /- &copter -/ + 12776) then  -- copter.ModeLoiter
    Mode.move_vehicle_on_ekf_reset this
  else if this == ((0x86d8 : UInt64) /- &copter -/ + 12888) then  -- copter.ModeRTL
    Mode.move_vehicle_on_ekf_reset this
  else if this == ((0x86d8 : UInt64) /- &copter -/ + 13096) then  -- copter.ModeStabilize
    Mode.move_vehicle_on_ekf_reset this
  else
    PMem.unreached "virtual Mode::move_vehicle_on_ekf_reset on an object outside copter"
    return default

/-- Virtual calls of `Mode::use_pilot_yaw() const` through a `Mode *`: by the object's address, over the member objects of `copter` whose class derives from Mode (9), each arm the final overrider of its class. -/
def vcall'Mode'use_pilot_yaw'33 (this : UInt64) : PMem.M Bool := do
  if this == ((0x86d8 : UInt64) /- &copter -/ + 11256) then  -- copter.ModeAltHold
    Mode.use_pilot_yaw this
  else if this == ((0x86d8 : UInt64) /- &copter -/ + 11368) then  -- copter.ModeAuto
    ModeAuto.use_pilot_yaw this
  else if this == ((0x86d8 : UInt64) /- &copter -/ + 12280) then  -- copter.ModeBrake
    Mode.use_pilot_yaw this
  else if this == ((0x86d8 : UInt64) /- &copter -/ + 12400) then  -- copter.ModeCircle
    Mode.use_pilot_yaw this
  else if this == ((0x86d8 : UInt64) /- &copter -/ + 12520) then  -- copter.ModeGuided
    ModeGuided.use_pilot_yaw this
  else if this == ((0x86d8 : UInt64) /- &copter -/ + 12640) then  -- copter.ModeLand
    ModeLand.use_pilot_yaw this
  else if this == ((0x86d8 : UInt64) /- &copter -/ + 12776) then  -- copter.ModeLoiter
    Mode.use_pilot_yaw this
  else if this == ((0x86d8 : UInt64) /- &copter -/ + 12888) then  -- copter.ModeRTL
    ModeRTL.use_pilot_yaw this
  else if this == ((0x86d8 : UInt64) /- &copter -/ + 13096) then  -- copter.ModeStabilize
    Mode.use_pilot_yaw this
  else
    PMem.unreached "virtual Mode::use_pilot_yaw on an object outside copter"
    return default

/-- Virtual calls of `Mode::crash_check_enabled() const` through a `Mode *`: by the object's address, over the member objects of `copter` whose class derives from Mode (9), each arm the final overrider of its class. -/
def vcall'Mode'crash_check_enabled'31 (this : UInt64) : PMem.M Bool := do
  if this == ((0x86d8 : UInt64) /- &copter -/ + 11256) then  -- copter.ModeAltHold
    Mode.crash_check_enabled this
  else if this == ((0x86d8 : UInt64) /- &copter -/ + 11368) then  -- copter.ModeAuto
    Mode.crash_check_enabled this
  else if this == ((0x86d8 : UInt64) /- &copter -/ + 12280) then  -- copter.ModeBrake
    Mode.crash_check_enabled this
  else if this == ((0x86d8 : UInt64) /- &copter -/ + 12400) then  -- copter.ModeCircle
    Mode.crash_check_enabled this
  else if this == ((0x86d8 : UInt64) /- &copter -/ + 12520) then  -- copter.ModeGuided
    Mode.crash_check_enabled this
  else if this == ((0x86d8 : UInt64) /- &copter -/ + 12640) then  -- copter.ModeLand
    Mode.crash_check_enabled this
  else if this == ((0x86d8 : UInt64) /- &copter -/ + 12776) then  -- copter.ModeLoiter
    Mode.crash_check_enabled this
  else if this == ((0x86d8 : UInt64) /- &copter -/ + 12888) then  -- copter.ModeRTL
    Mode.crash_check_enabled this
  else if this == ((0x86d8 : UInt64) /- &copter -/ + 13096) then  -- copter.ModeStabilize
    Mode.crash_check_enabled this
  else
    PMem.unreached "virtual Mode::crash_check_enabled on an object outside copter"
    return default

/-- Virtual calls of `Mode::requires_terrain_failsafe() const` through a `Mode *`: by the object's address, over the member objects of `copter` whose class derives from Mode (9), each arm the final overrider of its class. -/
def vcall'Mode'requires_terrain_failsafe'32 (this : UInt64) : PMem.M Bool := do
  if this == ((0x86d8 : UInt64) /- &copter -/ + 11256) then  -- copter.ModeAltHold
    Mode.requires_terrain_failsafe this
  else if this == ((0x86d8 : UInt64) /- &copter -/ + 11368) then  -- copter.ModeAuto
    ModeAuto.requires_terrain_failsafe this
  else if this == ((0x86d8 : UInt64) /- &copter -/ + 12280) then  -- copter.ModeBrake
    Mode.requires_terrain_failsafe this
  else if this == ((0x86d8 : UInt64) /- &copter -/ + 12400) then  -- copter.ModeCircle
    Mode.requires_terrain_failsafe this
  else if this == ((0x86d8 : UInt64) /- &copter -/ + 12520) then  -- copter.ModeGuided
    ModeGuided.requires_terrain_failsafe this
  else if this == ((0x86d8 : UInt64) /- &copter -/ + 12640) then  -- copter.ModeLand
    Mode.requires_terrain_failsafe this
  else if this == ((0x86d8 : UInt64) /- &copter -/ + 12776) then  -- copter.ModeLoiter
    Mode.requires_terrain_failsafe this
  else if this == ((0x86d8 : UInt64) /- &copter -/ + 12888) then  -- copter.ModeRTL
    ModeRTL.requires_terrain_failsafe this
  else if this == ((0x86d8 : UInt64) /- &copter -/ + 13096) then  -- copter.ModeStabilize
    Mode.requires_terrain_failsafe this
  else
    PMem.unreached "virtual Mode::requires_terrain_failsafe on an object outside copter"
    return default

end Vehicle_lib
