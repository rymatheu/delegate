import ArduLean.Runtime.GcsPort
import ArduLean.Vehicle.ArduCopter.ArduCopter
import ArduLean.Vehicle.ArduCopter.ArduCopter_2
import ArduLean.Vehicle.ArduCopter.ArduCopter_3

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

/-- Virtual calls of `Mode::init(bool)` through a `Mode *`: by the object's address, over the member objects of `copter` whose class derives from Mode (9), each arm the final overrider of its class. -/
def vcall'Mode'init'7 (this : UInt64) (p0 : Bool) : PMem.M Bool := do
  if this == ((0x86d8 : UInt64) /- &copter -/ + 11256) then  -- copter.ModeAltHold
    ModeAltHold.init this p0
  else if this == ((0x86d8 : UInt64) /- &copter -/ + 11368) then  -- copter.ModeAuto
    ModeAuto.init this p0
  else if this == ((0x86d8 : UInt64) /- &copter -/ + 12280) then  -- copter.ModeBrake
    ModeBrake.init this p0
  else if this == ((0x86d8 : UInt64) /- &copter -/ + 12400) then  -- copter.ModeCircle
    ModeCircle.init this p0
  else if this == ((0x86d8 : UInt64) /- &copter -/ + 12520) then  -- copter.ModeGuided
    ModeGuided.init this p0
  else if this == ((0x86d8 : UInt64) /- &copter -/ + 12640) then  -- copter.ModeLand
    ModeLand.init this p0
  else if this == ((0x86d8 : UInt64) /- &copter -/ + 12776) then  -- copter.ModeLoiter
    ModeLoiter.init this p0
  else if this == ((0x86d8 : UInt64) /- &copter -/ + 12888) then  -- copter.ModeRTL
    ModeRTL.init this p0
  else if this == ((0x86d8 : UInt64) /- &copter -/ + 13096) then  -- copter.ModeStabilize
    Mode.init this p0
  else
    PMem.unreached "virtual Mode::init on an object outside copter"
    return default

/-- Virtual calls of `Mode::output_to_motors()` through a `Mode *`: by the object's address, over the member objects of `copter` whose class derives from Mode (9), each arm the final overrider of its class. -/
def vcall'Mode'output_to_motors'30 (this : UInt64) : PMem.M Unit := do
  if this == ((0x86d8 : UInt64) /- &copter -/ + 11256) then  -- copter.ModeAltHold
    Mode.output_to_motors this
  else if this == ((0x86d8 : UInt64) /- &copter -/ + 11368) then  -- copter.ModeAuto
    Mode.output_to_motors this
  else if this == ((0x86d8 : UInt64) /- &copter -/ + 12280) then  -- copter.ModeBrake
    Mode.output_to_motors this
  else if this == ((0x86d8 : UInt64) /- &copter -/ + 12400) then  -- copter.ModeCircle
    Mode.output_to_motors this
  else if this == ((0x86d8 : UInt64) /- &copter -/ + 12520) then  -- copter.ModeGuided
    Mode.output_to_motors this
  else if this == ((0x86d8 : UInt64) /- &copter -/ + 12640) then  -- copter.ModeLand
    Mode.output_to_motors this
  else if this == ((0x86d8 : UInt64) /- &copter -/ + 12776) then  -- copter.ModeLoiter
    Mode.output_to_motors this
  else if this == ((0x86d8 : UInt64) /- &copter -/ + 12888) then  -- copter.ModeRTL
    Mode.output_to_motors this
  else if this == ((0x86d8 : UInt64) /- &copter -/ + 13096) then  -- copter.ModeStabilize
    Mode.output_to_motors this
  else
    PMem.unreached "virtual Mode::output_to_motors on an object outside copter"
    return ()

end Vehicle_lib
