import ArduLean.Vehicle
import Corpus.Machine.Float
import Corpus.Machine.Memory

/-!
# ArduCopter: the mode tables (`mode.h`, `mode_*.cpp`)

Protocol lemmas of the flight modes' constant answers, by evaluation: each `Mode*.f.pure'` that returns a constant
returns that constant (`_val`), and its memory-side `f` is `pure` of it (`_eq`). The table of all modes is
`mode_numbers_nodup`. Generated from the code's definitions; every proof is `rfl` (the kernel unfolds the body).
-/

open FloatLib.Floats (Binary32 Binary64)

namespace Corpus.ArduCopter

/-- C++ `Mode::in_guided_mode : bool () const`, `AP_Common.h:133-?`. -/
theorem Mode.in_guided_mode_eq (this : UInt64) :
    Vehicle_lib.Mode.in_guided_mode this = pure (Vehicle_lib.Mode.in_guided_mode.pure' this) := rfl

/-- Protocol. -/
theorem Mode.in_guided_mode_val (this : UInt64) :
    Id.run (Vehicle_lib.Mode.in_guided_mode.pure' this) = false := rfl

/-- C++ `ModeGuided::in_guided_mode : bool () const`, `mode.h:1125-?`. -/
theorem ModeGuided.in_guided_mode_eq (this : UInt64) :
    Vehicle_lib.ModeGuided.in_guided_mode this = pure (Vehicle_lib.ModeGuided.in_guided_mode.pure' this) := rfl

/-- Protocol. -/
theorem ModeGuided.in_guided_mode_val (this : UInt64) :
    Id.run (Vehicle_lib.ModeGuided.in_guided_mode.pure' this) = true := rfl

/-- C++ `ModeAltHold::is_autopilot : bool () const`, `mode.h:511-?`. -/
theorem ModeAltHold.is_autopilot_eq (this : UInt64) :
    Vehicle_lib.ModeAltHold.is_autopilot this = pure (Vehicle_lib.ModeAltHold.is_autopilot.pure' this) := rfl

/-- Protocol. -/
theorem ModeAltHold.is_autopilot_val (this : UInt64) :
    Id.run (Vehicle_lib.ModeAltHold.is_autopilot.pure' this) = false := rfl

/-- C++ `ModeAuto::is_autopilot : bool () const`, `mode.h:548-?`. -/
theorem ModeAuto.is_autopilot_eq (this : UInt64) :
    Vehicle_lib.ModeAuto.is_autopilot this = pure (Vehicle_lib.ModeAuto.is_autopilot.pure' this) := rfl

/-- Protocol. -/
theorem ModeAuto.is_autopilot_val (this : UInt64) :
    Id.run (Vehicle_lib.ModeAuto.is_autopilot.pure' this) = true := rfl

/-- C++ `ModeBrake::is_autopilot : bool () const`, `mode.h:890-?`. -/
theorem ModeBrake.is_autopilot_eq (this : UInt64) :
    Vehicle_lib.ModeBrake.is_autopilot this = pure (Vehicle_lib.ModeBrake.is_autopilot.pure' this) := rfl

/-- Protocol. -/
theorem ModeBrake.is_autopilot_val (this : UInt64) :
    Id.run (Vehicle_lib.ModeBrake.is_autopilot.pure' this) = true := rfl

/-- C++ `ModeCircle::is_autopilot : bool () const`, `mode.h:920-?`. -/
theorem ModeCircle.is_autopilot_eq (this : UInt64) :
    Vehicle_lib.ModeCircle.is_autopilot this = pure (Vehicle_lib.ModeCircle.is_autopilot.pure' this) := rfl

/-- Protocol. -/
theorem ModeCircle.is_autopilot_val (this : UInt64) :
    Id.run (Vehicle_lib.ModeCircle.is_autopilot.pure' this) = true := rfl

/-- C++ `ModeGuided::is_autopilot : bool () const`, `mode.h:1123-?`. -/
theorem ModeGuided.is_autopilot_eq (this : UInt64) :
    Vehicle_lib.ModeGuided.is_autopilot this = pure (Vehicle_lib.ModeGuided.is_autopilot.pure' this) := rfl

/-- Protocol. -/
theorem ModeGuided.is_autopilot_val (this : UInt64) :
    Id.run (Vehicle_lib.ModeGuided.is_autopilot.pure' this) = true := rfl

/-- C++ `ModeLand::is_autopilot : bool () const`, `mode.h:1318-?`. -/
theorem ModeLand.is_autopilot_eq (this : UInt64) :
    Vehicle_lib.ModeLand.is_autopilot this = pure (Vehicle_lib.ModeLand.is_autopilot.pure' this) := rfl

/-- Protocol. -/
theorem ModeLand.is_autopilot_val (this : UInt64) :
    Id.run (Vehicle_lib.ModeLand.is_autopilot.pure' this) = true := rfl

/-- C++ `ModeLoiter::is_autopilot : bool () const`, `mode.h:1380-?`. -/
theorem ModeLoiter.is_autopilot_eq (this : UInt64) :
    Vehicle_lib.ModeLoiter.is_autopilot this = pure (Vehicle_lib.ModeLoiter.is_autopilot.pure' this) := rfl

/-- Protocol. -/
theorem ModeLoiter.is_autopilot_val (this : UInt64) :
    Id.run (Vehicle_lib.ModeLoiter.is_autopilot.pure' this) = false := rfl

/-- C++ `ModeRTL::is_autopilot : bool () const`, `mode.h:1527-?`. -/
theorem ModeRTL.is_autopilot_eq (this : UInt64) :
    Vehicle_lib.ModeRTL.is_autopilot this = pure (Vehicle_lib.ModeRTL.is_autopilot.pure' this) := rfl

/-- Protocol. -/
theorem ModeRTL.is_autopilot_val (this : UInt64) :
    Id.run (Vehicle_lib.ModeRTL.is_autopilot.pure' this) = true := rfl

/-- C++ `ModeStabilize::is_autopilot : bool () const`, `mode.h:1759-?`. -/
theorem ModeStabilize.is_autopilot_eq (this : UInt64) :
    Vehicle_lib.ModeStabilize.is_autopilot this = pure (Vehicle_lib.ModeStabilize.is_autopilot.pure' this) := rfl

/-- Protocol. -/
theorem ModeStabilize.is_autopilot_val (this : UInt64) :
    Id.run (Vehicle_lib.ModeStabilize.is_autopilot.pure' this) = false := rfl

/-- C++ `ModeAltHold::mode_number : Number () const`, `mode.h:503-?`. -/
theorem ModeAltHold.mode_number_eq (this : UInt64) :
    Vehicle_lib.ModeAltHold.mode_number this = pure (Vehicle_lib.ModeAltHold.mode_number.pure' this) := rfl

/-- Protocol. -/
theorem ModeAltHold.mode_number_val (this : UInt64) :
    Id.run (Vehicle_lib.ModeAltHold.mode_number.pure' this) = (2 : UInt8) := rfl

/-- C++ `ModeBrake::mode_number : Number () const`, `mode.h:882-?`. -/
theorem ModeBrake.mode_number_eq (this : UInt64) :
    Vehicle_lib.ModeBrake.mode_number this = pure (Vehicle_lib.ModeBrake.mode_number.pure' this) := rfl

/-- Protocol. -/
theorem ModeBrake.mode_number_val (this : UInt64) :
    Id.run (Vehicle_lib.ModeBrake.mode_number.pure' this) = (17 : UInt8) := rfl

/-- C++ `ModeCircle::mode_number : Number () const`, `mode.h:912-?`. -/
theorem ModeCircle.mode_number_eq (this : UInt64) :
    Vehicle_lib.ModeCircle.mode_number this = pure (Vehicle_lib.ModeCircle.mode_number.pure' this) := rfl

/-- Protocol. -/
theorem ModeCircle.mode_number_val (this : UInt64) :
    Id.run (Vehicle_lib.ModeCircle.mode_number.pure' this) = (7 : UInt8) := rfl

/-- C++ `ModeGuided::mode_number : Number () const`, `mode.h:1115-?`. -/
theorem ModeGuided.mode_number_eq (this : UInt64) :
    Vehicle_lib.ModeGuided.mode_number this = pure (Vehicle_lib.ModeGuided.mode_number.pure' this) := rfl

/-- Protocol. -/
theorem ModeGuided.mode_number_val (this : UInt64) :
    Id.run (Vehicle_lib.ModeGuided.mode_number.pure' this) = (4 : UInt8) := rfl

/-- C++ `ModeLand::mode_number : Number () const`, `mode.h:1310-?`. -/
theorem ModeLand.mode_number_eq (this : UInt64) :
    Vehicle_lib.ModeLand.mode_number this = pure (Vehicle_lib.ModeLand.mode_number.pure' this) := rfl

/-- Protocol. -/
theorem ModeLand.mode_number_val (this : UInt64) :
    Id.run (Vehicle_lib.ModeLand.mode_number.pure' this) = (9 : UInt8) := rfl

/-- C++ `ModeLoiter::mode_number : Number () const`, `mode.h:1372-?`. -/
theorem ModeLoiter.mode_number_eq (this : UInt64) :
    Vehicle_lib.ModeLoiter.mode_number this = pure (Vehicle_lib.ModeLoiter.mode_number.pure' this) := rfl

/-- Protocol. -/
theorem ModeLoiter.mode_number_val (this : UInt64) :
    Id.run (Vehicle_lib.ModeLoiter.mode_number.pure' this) = (5 : UInt8) := rfl

/-- C++ `ModeRTL::mode_number : Number () const`, `mode.h:1516-?`. -/
theorem ModeRTL.mode_number_eq (this : UInt64) :
    Vehicle_lib.ModeRTL.mode_number this = pure (Vehicle_lib.ModeRTL.mode_number.pure' this) := rfl

/-- Protocol. -/
theorem ModeRTL.mode_number_val (this : UInt64) :
    Id.run (Vehicle_lib.ModeRTL.mode_number.pure' this) = (6 : UInt8) := rfl

/-- C++ `ModeStabilize::mode_number : Number () const`, `mode.h:1752-?`. -/
theorem ModeStabilize.mode_number_eq (this : UInt64) :
    Vehicle_lib.ModeStabilize.mode_number this = pure (Vehicle_lib.ModeStabilize.mode_number.pure' this) := rfl

/-- Protocol. -/
theorem ModeStabilize.mode_number_val (this : UInt64) :
    Id.run (Vehicle_lib.ModeStabilize.mode_number.pure' this) = (0 : UInt8) := rfl

/-- C++ `ModeAltHold::name4 : const char *() const`, `mode.h:525-?`. -/
theorem ModeAltHold.name4_eq (this : UInt64) :
    Vehicle_lib.ModeAltHold.name4 this = pure (Vehicle_lib.ModeAltHold.name4.pure' this) := rfl

/-- Protocol (`"ALTH"`). -/
theorem ModeAltHold.name4_val (this : UInt64) :
    Id.run (Vehicle_lib.ModeAltHold.name4.pure' this) = (0x14916 : UInt64) := rfl

/-- C++ `ModeBrake::name4 : const char *() const`, `mode.h:897-?`. -/
theorem ModeBrake.name4_eq (this : UInt64) :
    Vehicle_lib.ModeBrake.name4 this = pure (Vehicle_lib.ModeBrake.name4.pure' this) := rfl

/-- Protocol (`"BRAK"`). -/
theorem ModeBrake.name4_val (this : UInt64) :
    Id.run (Vehicle_lib.ModeBrake.name4.pure' this) = (0x14ae6 : UInt64) := rfl

/-- C++ `ModeCircle::name4 : const char *() const`, `mode.h:925-?`. -/
theorem ModeCircle.name4_eq (this : UInt64) :
    Vehicle_lib.ModeCircle.name4 this = pure (Vehicle_lib.ModeCircle.name4.pure' this) := rfl

/-- Protocol (`"CIRC"`). -/
theorem ModeCircle.name4_val (this : UInt64) :
    Id.run (Vehicle_lib.ModeCircle.name4.pure' this) = (0x14af2 : UInt64) := rfl

/-- C++ `ModeGuided::name4 : const char *() const`, `mode.h:1207-?`. -/
theorem ModeGuided.name4_eq (this : UInt64) :
    Vehicle_lib.ModeGuided.name4 this = pure (Vehicle_lib.ModeGuided.name4.pure' this) := rfl

/-- Protocol (`"GUID"`). -/
theorem ModeGuided.name4_val (this : UInt64) :
    Id.run (Vehicle_lib.ModeGuided.name4.pure' this) = (0x14afe : UInt64) := rfl

/-- C++ `ModeLand::name4 : const char *() const`, `mode.h:1348-?`. -/
theorem ModeLand.name4_eq (this : UInt64) :
    Vehicle_lib.ModeLand.name4 this = pure (Vehicle_lib.ModeLand.name4.pure' this) := rfl

/-- Protocol (`"LAND"`). -/
theorem ModeLand.name4_val (this : UInt64) :
    Id.run (Vehicle_lib.ModeLand.name4.pure' this) = (0x14b51 : UInt64) := rfl

/-- C++ `ModeLoiter::name4 : const char *() const`, `mode.h:1396-?`. -/
theorem ModeLoiter.name4_eq (this : UInt64) :
    Vehicle_lib.ModeLoiter.name4 this = pure (Vehicle_lib.ModeLoiter.name4.pure' this) := rfl

/-- Protocol (`"LOIT"`). -/
theorem ModeLoiter.name4_val (this : UInt64) :
    Id.run (Vehicle_lib.ModeLoiter.name4.pure' this) = (0x14b5d : UInt64) := rfl

/-- C++ `ModeRTL::name4 : const char *() const`, `mode.h:1586-?`. -/
theorem ModeRTL.name4_eq (this : UInt64) :
    Vehicle_lib.ModeRTL.name4 this = pure (Vehicle_lib.ModeRTL.name4.pure' this) := rfl

/-- Protocol (`"RTL "`). -/
theorem ModeRTL.name4_val (this : UInt64) :
    Id.run (Vehicle_lib.ModeRTL.name4.pure' this) = (0x14c9e : UInt64) := rfl

/-- C++ `ModeStabilize::name4 : const char *() const`, `mode.h:1769-?`. -/
theorem ModeStabilize.name4_eq (this : UInt64) :
    Vehicle_lib.ModeStabilize.name4 this = pure (Vehicle_lib.ModeStabilize.name4.pure' this) := rfl

/-- Protocol (`"STAB"`). -/
theorem ModeStabilize.name4_val (this : UInt64) :
    Id.run (Vehicle_lib.ModeStabilize.name4.pure' this) = (0x14cad : UInt64) := rfl

/-- C++ `ModeAltHold::name : const char *() const`, `mode.h:524-?`. -/
theorem ModeAltHold.name_eq (this : UInt64) :
    Vehicle_lib.ModeAltHold.name this = pure (Vehicle_lib.ModeAltHold.name.pure' this) := rfl

/-- Protocol (`"Altitude Hold"`). -/
theorem ModeAltHold.name_val (this : UInt64) :
    Id.run (Vehicle_lib.ModeAltHold.name.pure' this) = (0x14908 : UInt64) := rfl

/-- C++ `ModeBrake::name : const char *() const`, `mode.h:896-?`. -/
theorem ModeBrake.name_eq (this : UInt64) :
    Vehicle_lib.ModeBrake.name this = pure (Vehicle_lib.ModeBrake.name.pure' this) := rfl

/-- Protocol (`"Brake"`). -/
theorem ModeBrake.name_val (this : UInt64) :
    Id.run (Vehicle_lib.ModeBrake.name.pure' this) = (0x14ae0 : UInt64) := rfl

/-- C++ `ModeCircle::name : const char *() const`, `mode.h:924-?`. -/
theorem ModeCircle.name_eq (this : UInt64) :
    Vehicle_lib.ModeCircle.name this = pure (Vehicle_lib.ModeCircle.name.pure' this) := rfl

/-- Protocol (`"Circle"`). -/
theorem ModeCircle.name_val (this : UInt64) :
    Id.run (Vehicle_lib.ModeCircle.name.pure' this) = (0x14aeb : UInt64) := rfl

/-- C++ `ModeGuided::name : const char *() const`, `mode.h:1206-?`. -/
theorem ModeGuided.name_eq (this : UInt64) :
    Vehicle_lib.ModeGuided.name this = pure (Vehicle_lib.ModeGuided.name.pure' this) := rfl

/-- Protocol (`"Guided"`). -/
theorem ModeGuided.name_val (this : UInt64) :
    Id.run (Vehicle_lib.ModeGuided.name.pure' this) = (0x14af7 : UInt64) := rfl

/-- C++ `ModeLand::name : const char *() const`, `mode.h:1347-?`. -/
theorem ModeLand.name_eq (this : UInt64) :
    Vehicle_lib.ModeLand.name this = pure (Vehicle_lib.ModeLand.name.pure' this) := rfl

/-- Protocol (`"Land"`). -/
theorem ModeLand.name_val (this : UInt64) :
    Id.run (Vehicle_lib.ModeLand.name.pure' this) = (0x14b4c : UInt64) := rfl

/-- C++ `ModeLoiter::name : const char *() const`, `mode.h:1395-?`. -/
theorem ModeLoiter.name_eq (this : UInt64) :
    Vehicle_lib.ModeLoiter.name this = pure (Vehicle_lib.ModeLoiter.name.pure' this) := rfl

/-- Protocol (`"Loiter"`). -/
theorem ModeLoiter.name_val (this : UInt64) :
    Id.run (Vehicle_lib.ModeLoiter.name.pure' this) = (0x14b56 : UInt64) := rfl

/-- C++ `ModeRTL::name : const char *() const`, `mode.h:1585-?`. -/
theorem ModeRTL.name_eq (this : UInt64) :
    Vehicle_lib.ModeRTL.name this = pure (Vehicle_lib.ModeRTL.name.pure' this) := rfl

/-- Protocol (`"RTL"`). -/
theorem ModeRTL.name_val (this : UInt64) :
    Id.run (Vehicle_lib.ModeRTL.name.pure' this) = (0x14c9a : UInt64) := rfl

/-- C++ `ModeStabilize::name : const char *() const`, `mode.h:1768-?`. -/
theorem ModeStabilize.name_eq (this : UInt64) :
    Vehicle_lib.ModeStabilize.name this = pure (Vehicle_lib.ModeStabilize.name.pure' this) := rfl

/-- Protocol (`"Stabilize"`). -/
theorem ModeStabilize.name_val (this : UInt64) :
    Id.run (Vehicle_lib.ModeStabilize.name.pure' this) = (0x14ca3 : UInt64) := rfl

/-- C++ `ModeAltHold::allows_arming : bool (AP_Arming::Method) const`, `mode.h:510-?`. -/
theorem ModeAltHold.allows_arming_eq (this : UInt64) (method : Int32) :
    Vehicle_lib.ModeAltHold.allows_arming this method = pure (Vehicle_lib.ModeAltHold.allows_arming.pure' this method) := rfl

/-- Protocol. -/
theorem ModeAltHold.allows_arming_val (this : UInt64) (method : Int32) :
    Id.run (Vehicle_lib.ModeAltHold.allows_arming.pure' this method) = true := rfl

/-- C++ `ModeBrake::allows_arming : bool (AP_Arming::Method) const`, `mode.h:889-?`. -/
theorem ModeBrake.allows_arming_eq (this : UInt64) (method : Int32) :
    Vehicle_lib.ModeBrake.allows_arming this method = pure (Vehicle_lib.ModeBrake.allows_arming.pure' this method) := rfl

/-- Protocol. -/
theorem ModeBrake.allows_arming_val (this : UInt64) (method : Int32) :
    Id.run (Vehicle_lib.ModeBrake.allows_arming.pure' this method) = false := rfl

/-- C++ `ModeCircle::allows_arming : bool (AP_Arming::Method) const`, `mode.h:919-?`. -/
theorem ModeCircle.allows_arming_eq (this : UInt64) (method : Int32) :
    Vehicle_lib.ModeCircle.allows_arming this method = pure (Vehicle_lib.ModeCircle.allows_arming.pure' this method) := rfl

/-- Protocol. -/
theorem ModeCircle.allows_arming_val (this : UInt64) (method : Int32) :
    Id.run (Vehicle_lib.ModeCircle.allows_arming.pure' this method) = false := rfl

/-- C++ `ModeLand::allows_arming : bool (AP_Arming::Method) const`, `mode.h:1317-?`. -/
theorem ModeLand.allows_arming_eq (this : UInt64) (method : Int32) :
    Vehicle_lib.ModeLand.allows_arming this method = pure (Vehicle_lib.ModeLand.allows_arming.pure' this method) := rfl

/-- Protocol. -/
theorem ModeLand.allows_arming_val (this : UInt64) (method : Int32) :
    Id.run (Vehicle_lib.ModeLand.allows_arming.pure' this method) = false := rfl

/-- C++ `ModeLoiter::allows_arming : bool (AP_Arming::Method) const`, `mode.h:1379-?`. -/
theorem ModeLoiter.allows_arming_eq (this : UInt64) (method : Int32) :
    Vehicle_lib.ModeLoiter.allows_arming this method = pure (Vehicle_lib.ModeLoiter.allows_arming.pure' this method) := rfl

/-- Protocol. -/
theorem ModeLoiter.allows_arming_val (this : UInt64) (method : Int32) :
    Id.run (Vehicle_lib.ModeLoiter.allows_arming.pure' this method) = true := rfl

/-- C++ `ModeRTL::allows_arming : bool (AP_Arming::Method) const`, `mode.h:1526-?`. -/
theorem ModeRTL.allows_arming_eq (this : UInt64) (method : Int32) :
    Vehicle_lib.ModeRTL.allows_arming this method = pure (Vehicle_lib.ModeRTL.allows_arming.pure' this method) := rfl

/-- Protocol. -/
theorem ModeRTL.allows_arming_val (this : UInt64) (method : Int32) :
    Id.run (Vehicle_lib.ModeRTL.allows_arming.pure' this method) = false := rfl

/-- C++ `ModeStabilize::allows_arming : bool (AP_Arming::Method) const`, `mode.h:1758-?`. -/
theorem ModeStabilize.allows_arming_eq (this : UInt64) (method : Int32) :
    Vehicle_lib.ModeStabilize.allows_arming this method = pure (Vehicle_lib.ModeStabilize.allows_arming.pure' this method) := rfl

/-- Protocol. -/
theorem ModeStabilize.allows_arming_val (this : UInt64) (method : Int32) :
    Id.run (Vehicle_lib.ModeStabilize.allows_arming.pure' this method) = true := rfl

/-- C++ `ModeAltHold::has_manual_throttle : bool () const`, `mode.h:509-?`. -/
theorem ModeAltHold.has_manual_throttle_eq (this : UInt64) :
    Vehicle_lib.ModeAltHold.has_manual_throttle this = pure (Vehicle_lib.ModeAltHold.has_manual_throttle.pure' this) := rfl

/-- Protocol. -/
theorem ModeAltHold.has_manual_throttle_val (this : UInt64) :
    Id.run (Vehicle_lib.ModeAltHold.has_manual_throttle.pure' this) = false := rfl

/-- C++ `ModeAuto::has_manual_throttle : bool () const`, `mode.h:546-?`. -/
theorem ModeAuto.has_manual_throttle_eq (this : UInt64) :
    Vehicle_lib.ModeAuto.has_manual_throttle this = pure (Vehicle_lib.ModeAuto.has_manual_throttle.pure' this) := rfl

/-- Protocol. -/
theorem ModeAuto.has_manual_throttle_val (this : UInt64) :
    Id.run (Vehicle_lib.ModeAuto.has_manual_throttle.pure' this) = false := rfl

/-- C++ `ModeBrake::has_manual_throttle : bool () const`, `mode.h:888-?`. -/
theorem ModeBrake.has_manual_throttle_eq (this : UInt64) :
    Vehicle_lib.ModeBrake.has_manual_throttle this = pure (Vehicle_lib.ModeBrake.has_manual_throttle.pure' this) := rfl

/-- Protocol. -/
theorem ModeBrake.has_manual_throttle_val (this : UInt64) :
    Id.run (Vehicle_lib.ModeBrake.has_manual_throttle.pure' this) = false := rfl

/-- C++ `ModeCircle::has_manual_throttle : bool () const`, `mode.h:918-?`. -/
theorem ModeCircle.has_manual_throttle_eq (this : UInt64) :
    Vehicle_lib.ModeCircle.has_manual_throttle this = pure (Vehicle_lib.ModeCircle.has_manual_throttle.pure' this) := rfl

/-- Protocol. -/
theorem ModeCircle.has_manual_throttle_val (this : UInt64) :
    Id.run (Vehicle_lib.ModeCircle.has_manual_throttle.pure' this) = false := rfl

/-- C++ `ModeGuided::has_manual_throttle : bool () const`, `mode.h:1121-?`. -/
theorem ModeGuided.has_manual_throttle_eq (this : UInt64) :
    Vehicle_lib.ModeGuided.has_manual_throttle this = pure (Vehicle_lib.ModeGuided.has_manual_throttle.pure' this) := rfl

/-- Protocol. -/
theorem ModeGuided.has_manual_throttle_val (this : UInt64) :
    Id.run (Vehicle_lib.ModeGuided.has_manual_throttle.pure' this) = false := rfl

/-- C++ `ModeLand::has_manual_throttle : bool () const`, `mode.h:1316-?`. -/
theorem ModeLand.has_manual_throttle_eq (this : UInt64) :
    Vehicle_lib.ModeLand.has_manual_throttle this = pure (Vehicle_lib.ModeLand.has_manual_throttle.pure' this) := rfl

/-- Protocol. -/
theorem ModeLand.has_manual_throttle_val (this : UInt64) :
    Id.run (Vehicle_lib.ModeLand.has_manual_throttle.pure' this) = false := rfl

/-- C++ `ModeLoiter::has_manual_throttle : bool () const`, `mode.h:1378-?`. -/
theorem ModeLoiter.has_manual_throttle_eq (this : UInt64) :
    Vehicle_lib.ModeLoiter.has_manual_throttle this = pure (Vehicle_lib.ModeLoiter.has_manual_throttle.pure' this) := rfl

/-- Protocol. -/
theorem ModeLoiter.has_manual_throttle_val (this : UInt64) :
    Id.run (Vehicle_lib.ModeLoiter.has_manual_throttle.pure' this) = false := rfl

/-- C++ `ModeRTL::has_manual_throttle : bool () const`, `mode.h:1525-?`. -/
theorem ModeRTL.has_manual_throttle_eq (this : UInt64) :
    Vehicle_lib.ModeRTL.has_manual_throttle this = pure (Vehicle_lib.ModeRTL.has_manual_throttle.pure' this) := rfl

/-- Protocol. -/
theorem ModeRTL.has_manual_throttle_val (this : UInt64) :
    Id.run (Vehicle_lib.ModeRTL.has_manual_throttle.pure' this) = false := rfl

/-- C++ `ModeStabilize::has_manual_throttle : bool () const`, `mode.h:1757-?`. -/
theorem ModeStabilize.has_manual_throttle_eq (this : UInt64) :
    Vehicle_lib.ModeStabilize.has_manual_throttle this = pure (Vehicle_lib.ModeStabilize.has_manual_throttle.pure' this) := rfl

/-- Protocol. -/
theorem ModeStabilize.has_manual_throttle_val (this : UInt64) :
    Id.run (Vehicle_lib.ModeStabilize.has_manual_throttle.pure' this) = true := rfl

/-- C++ `ModeAltHold::requires_position : bool () const`, `mode.h:508-?`. -/
theorem ModeAltHold.requires_position_eq (this : UInt64) :
    Vehicle_lib.ModeAltHold.requires_position this = pure (Vehicle_lib.ModeAltHold.requires_position.pure' this) := rfl

/-- Protocol. -/
theorem ModeAltHold.requires_position_val (this : UInt64) :
    Id.run (Vehicle_lib.ModeAltHold.requires_position.pure' this) = false := rfl

/-- C++ `ModeBrake::requires_position : bool () const`, `mode.h:887-?`. -/
theorem ModeBrake.requires_position_eq (this : UInt64) :
    Vehicle_lib.ModeBrake.requires_position this = pure (Vehicle_lib.ModeBrake.requires_position.pure' this) := rfl

/-- Protocol. -/
theorem ModeBrake.requires_position_val (this : UInt64) :
    Id.run (Vehicle_lib.ModeBrake.requires_position.pure' this) = true := rfl

/-- C++ `ModeCircle::requires_position : bool () const`, `mode.h:917-?`. -/
theorem ModeCircle.requires_position_eq (this : UInt64) :
    Vehicle_lib.ModeCircle.requires_position this = pure (Vehicle_lib.ModeCircle.requires_position.pure' this) := rfl

/-- Protocol. -/
theorem ModeCircle.requires_position_val (this : UInt64) :
    Id.run (Vehicle_lib.ModeCircle.requires_position.pure' this) = true := rfl

/-- C++ `ModeGuided::requires_position : bool () const`, `mode.h:1120-?`. -/
theorem ModeGuided.requires_position_eq (this : UInt64) :
    Vehicle_lib.ModeGuided.requires_position this = pure (Vehicle_lib.ModeGuided.requires_position.pure' this) := rfl

/-- Protocol. -/
theorem ModeGuided.requires_position_val (this : UInt64) :
    Id.run (Vehicle_lib.ModeGuided.requires_position.pure' this) = true := rfl

/-- C++ `ModeLand::requires_position : bool () const`, `mode.h:1315-?`. -/
theorem ModeLand.requires_position_eq (this : UInt64) :
    Vehicle_lib.ModeLand.requires_position this = pure (Vehicle_lib.ModeLand.requires_position.pure' this) := rfl

/-- Protocol. -/
theorem ModeLand.requires_position_val (this : UInt64) :
    Id.run (Vehicle_lib.ModeLand.requires_position.pure' this) = false := rfl

/-- C++ `ModeLoiter::requires_position : bool () const`, `mode.h:1377-?`. -/
theorem ModeLoiter.requires_position_eq (this : UInt64) :
    Vehicle_lib.ModeLoiter.requires_position this = pure (Vehicle_lib.ModeLoiter.requires_position.pure' this) := rfl

/-- Protocol. -/
theorem ModeLoiter.requires_position_val (this : UInt64) :
    Id.run (Vehicle_lib.ModeLoiter.requires_position.pure' this) = true := rfl

/-- C++ `ModeRTL::requires_position : bool () const`, `mode.h:1524-?`. -/
theorem ModeRTL.requires_position_eq (this : UInt64) :
    Vehicle_lib.ModeRTL.requires_position this = pure (Vehicle_lib.ModeRTL.requires_position.pure' this) := rfl

/-- Protocol. -/
theorem ModeRTL.requires_position_val (this : UInt64) :
    Id.run (Vehicle_lib.ModeRTL.requires_position.pure' this) = true := rfl

/-- C++ `ModeStabilize::requires_position : bool () const`, `mode.h:1756-?`. -/
theorem ModeStabilize.requires_position_eq (this : UInt64) :
    Vehicle_lib.ModeStabilize.requires_position this = pure (Vehicle_lib.ModeStabilize.requires_position.pure' this) := rfl

/-- Protocol. -/
theorem ModeStabilize.requires_position_val (this : UInt64) :
    Id.run (Vehicle_lib.ModeStabilize.requires_position.pure' this) = false := rfl

/-- C++ `Mode::allows_GCS_or_SCR_arming_with_throttle_high : bool () const`, `AP_Common.h:151-?`. -/
theorem Mode.allows_GCS_or_SCR_arming_with_throttle_high_eq (this : UInt64) :
    Vehicle_lib.Mode.allows_GCS_or_SCR_arming_with_throttle_high this = pure (Vehicle_lib.Mode.allows_GCS_or_SCR_arming_with_throttle_high.pure' this) := rfl

/-- Protocol. -/
theorem Mode.allows_GCS_or_SCR_arming_with_throttle_high_val (this : UInt64) :
    Id.run (Vehicle_lib.Mode.allows_GCS_or_SCR_arming_with_throttle_high.pure' this) = false := rfl

/-- C++ `ModeAuto::allows_GCS_or_SCR_arming_with_throttle_high : bool () const`, `mode.h:561-?`. -/
theorem ModeAuto.allows_GCS_or_SCR_arming_with_throttle_high_eq (this : UInt64) :
    Vehicle_lib.ModeAuto.allows_GCS_or_SCR_arming_with_throttle_high this = pure (Vehicle_lib.ModeAuto.allows_GCS_or_SCR_arming_with_throttle_high.pure' this) := rfl

/-- Protocol. -/
theorem ModeAuto.allows_GCS_or_SCR_arming_with_throttle_high_val (this : UInt64) :
    Id.run (Vehicle_lib.ModeAuto.allows_GCS_or_SCR_arming_with_throttle_high.pure' this) = true := rfl

/-- C++ `ModeGuided::allows_GCS_or_SCR_arming_with_throttle_high : bool () const`, `mode.h:1136-?`. -/
theorem ModeGuided.allows_GCS_or_SCR_arming_with_throttle_high_eq (this : UInt64) :
    Vehicle_lib.ModeGuided.allows_GCS_or_SCR_arming_with_throttle_high this = pure (Vehicle_lib.ModeGuided.allows_GCS_or_SCR_arming_with_throttle_high.pure' this) := rfl

/-- Protocol. -/
theorem ModeGuided.allows_GCS_or_SCR_arming_with_throttle_high_val (this : UInt64) :
    Id.run (Vehicle_lib.ModeGuided.allows_GCS_or_SCR_arming_with_throttle_high.pure' this) = true := rfl

/-- C++ `ModeAltHold::allows_save_trim : bool () const`, `mode.h:518-?`. -/
theorem ModeAltHold.allows_save_trim_eq (this : UInt64) :
    Vehicle_lib.ModeAltHold.allows_save_trim this = pure (Vehicle_lib.ModeAltHold.allows_save_trim.pure' this) := rfl

/-- Protocol. -/
theorem ModeAltHold.allows_save_trim_val (this : UInt64) :
    Id.run (Vehicle_lib.ModeAltHold.allows_save_trim.pure' this) = true := rfl

/-- C++ `Mode::allows_save_trim : bool () const`, `AP_Common.h:135-?`. -/
theorem Mode.allows_save_trim_eq (this : UInt64) :
    Vehicle_lib.Mode.allows_save_trim this = pure (Vehicle_lib.Mode.allows_save_trim.pure' this) := rfl

/-- Protocol. -/
theorem Mode.allows_save_trim_val (this : UInt64) :
    Id.run (Vehicle_lib.Mode.allows_save_trim.pure' this) = false := rfl

/-- C++ `ModeStabilize::allows_save_trim : bool () const`, `mode.h:1760-?`. -/
theorem ModeStabilize.allows_save_trim_eq (this : UInt64) :
    Vehicle_lib.ModeStabilize.allows_save_trim this = pure (Vehicle_lib.ModeStabilize.allows_save_trim.pure' this) := rfl

/-- Protocol. -/
theorem ModeStabilize.allows_save_trim_val (this : UInt64) :
    Id.run (Vehicle_lib.ModeStabilize.allows_save_trim.pure' this) = true := rfl

/-- C++ `Mode::pause : bool ()`, `AP_Common.h:200-?`. -/
theorem Mode.pause_eq (this : UInt64) :
    Vehicle_lib.Mode.pause this = pure (Vehicle_lib.Mode.pause.pure' this) := rfl

/-- Protocol. -/
theorem Mode.pause_val (this : UInt64) :
    Id.run (Vehicle_lib.Mode.pause.pure' this) = false := rfl

/-- C++ `Mode::resume : bool ()`, `AP_Common.h:201-?`. -/
theorem Mode.resume_eq (this : UInt64) :
    Vehicle_lib.Mode.resume this = pure (Vehicle_lib.Mode.resume.pure' this) := rfl

/-- Protocol. -/
theorem Mode.resume_val (this : UInt64) :
    Id.run (Vehicle_lib.Mode.resume.pure' this) = false := rfl

/-- C++ `Mode::gcs : GCS_Copter &() const`, `mode.cpp:1143-1146`. -/
theorem Mode.gcs_eq (this : UInt64) :
    Vehicle_lib.Mode.gcs this = pure (Vehicle_lib.Mode.gcs.pure' this) := rfl

/-- C++ `Mode::exit : void ()`, `AP_Common.h:126-?`. -/
theorem Mode.exit_eq (this : UInt64) :
    Vehicle_lib.Mode.exit this = pure (Vehicle_lib.Mode.exit.pure' this) := rfl

/-- Protocol. -/
theorem Mode.exit_val (this : UInt64) :
    Id.run (Vehicle_lib.Mode.exit.pure' this) = () := rfl

/-- C++ `Mode::allows_entry_in_rc_failsafe : bool () const`, `AP_Common.h:143-?`. -/
theorem Mode.allows_entry_in_rc_failsafe_eq (this : UInt64) :
    Vehicle_lib.Mode.allows_entry_in_rc_failsafe this = pure (Vehicle_lib.Mode.allows_entry_in_rc_failsafe.pure' this) := rfl

/-- Protocol. -/
theorem Mode.allows_entry_in_rc_failsafe_val (this : UInt64) :
    Id.run (Vehicle_lib.Mode.allows_entry_in_rc_failsafe.pure' this) = true := rfl

/-- C++ `ModeStabilize::allows_entry_in_rc_failsafe : bool () const`, `mode.h:1764-?`. -/
theorem ModeStabilize.allows_entry_in_rc_failsafe_eq (this : UInt64) :
    Vehicle_lib.ModeStabilize.allows_entry_in_rc_failsafe this = pure (Vehicle_lib.ModeStabilize.allows_entry_in_rc_failsafe.pure' this) := rfl

/-- Protocol. -/
theorem ModeStabilize.allows_entry_in_rc_failsafe_val (this : UInt64) :
    Id.run (Vehicle_lib.ModeStabilize.allows_entry_in_rc_failsafe.pure' this) = false := rfl

/-- C++ `Mode::init : bool (bool)`, `AP_Common.h:123-125`. -/
theorem Mode.init_eq (this : UInt64) (ignore_checks : Bool) :
    Vehicle_lib.Mode.init this ignore_checks = pure (Vehicle_lib.Mode.init.pure' this ignore_checks) := rfl

/-- Protocol. -/
theorem Mode.init_val (this : UInt64) (ignore_checks : Bool) :
    Id.run (Vehicle_lib.Mode.init.pure' this ignore_checks) = true := rfl

/-- C++ `Mode::set_speed_NE_ms : bool (float)`, `AP_Common.h:177-?`. -/
theorem Mode.set_speed_NE_ms_eq (this : UInt64) (speed_ne_ms : Binary32) :
    Vehicle_lib.Mode.set_speed_NE_ms this speed_ne_ms = pure (Vehicle_lib.Mode.set_speed_NE_ms.pure' this speed_ne_ms) := rfl

/-- Protocol. -/
theorem Mode.set_speed_NE_ms_val (this : UInt64) (speed_ne_ms : Binary32) :
    Id.run (Vehicle_lib.Mode.set_speed_NE_ms.pure' this speed_ne_ms) = false := rfl

/-- C++ `Mode::set_speed_down_ms : bool (float)`, `AP_Common.h:179-?`. -/
theorem Mode.set_speed_down_ms_eq (this : UInt64) (speed_down_ms : Binary32) :
    Vehicle_lib.Mode.set_speed_down_ms this speed_down_ms = pure (Vehicle_lib.Mode.set_speed_down_ms.pure' this speed_down_ms) := rfl

/-- Protocol. -/
theorem Mode.set_speed_down_ms_val (this : UInt64) (speed_down_ms : Binary32) :
    Id.run (Vehicle_lib.Mode.set_speed_down_ms.pure' this speed_down_ms) = false := rfl

/-- C++ `Mode::set_speed_up_ms : bool (float)`, `AP_Common.h:178-?`. -/
theorem Mode.set_speed_up_ms_eq (this : UInt64) (speed_up_ms : Binary32) :
    Vehicle_lib.Mode.set_speed_up_ms this speed_up_ms = pure (Vehicle_lib.Mode.set_speed_up_ms.pure' this speed_up_ms) := rfl

/-- Protocol. -/
theorem Mode.set_speed_up_ms_val (this : UInt64) (speed_up_ms : Binary32) :
    Id.run (Vehicle_lib.Mode.set_speed_up_ms.pure' this speed_up_ms) = false := rfl

/-- C++ `ModeAltHold::has_user_takeoff : bool (bool) const`, `mode.h:512-514`. -/
theorem ModeAltHold.has_user_takeoff_eq (this : UInt64) (must_navigate : Bool) :
    Vehicle_lib.ModeAltHold.has_user_takeoff this must_navigate = pure (Vehicle_lib.ModeAltHold.has_user_takeoff.pure' this must_navigate) := rfl

/-- Protocol. -/
theorem ModeAltHold.has_user_takeoff_val (this : UInt64) (must_navigate : Bool) :
    Id.run (Vehicle_lib.ModeAltHold.has_user_takeoff.pure' this must_navigate) = !must_navigate := rfl

/-- C++ `Mode::has_user_takeoff : bool (bool) const`, `AP_Common.h:132-?`. -/
theorem Mode.has_user_takeoff_eq (this : UInt64) (must_navigate : Bool) :
    Vehicle_lib.Mode.has_user_takeoff this must_navigate = pure (Vehicle_lib.Mode.has_user_takeoff.pure' this must_navigate) := rfl

/-- Protocol. -/
theorem Mode.has_user_takeoff_val (this : UInt64) (must_navigate : Bool) :
    Id.run (Vehicle_lib.Mode.has_user_takeoff.pure' this must_navigate) = false := rfl

/-- C++ `ModeGuided::has_user_takeoff : bool (bool) const`, `mode.h:1124-?`. -/
theorem ModeGuided.has_user_takeoff_eq (this : UInt64) (must_navigate : Bool) :
    Vehicle_lib.ModeGuided.has_user_takeoff this must_navigate = pure (Vehicle_lib.ModeGuided.has_user_takeoff.pure' this must_navigate) := rfl

/-- Protocol. -/
theorem ModeGuided.has_user_takeoff_val (this : UInt64) (must_navigate : Bool) :
    Id.run (Vehicle_lib.ModeGuided.has_user_takeoff.pure' this must_navigate) = true := rfl

/-- C++ `ModeLoiter::has_user_takeoff : bool (bool) const`, `mode.h:1381-?`. -/
theorem ModeLoiter.has_user_takeoff_eq (this : UInt64) (must_navigate : Bool) :
    Vehicle_lib.ModeLoiter.has_user_takeoff this must_navigate = pure (Vehicle_lib.ModeLoiter.has_user_takeoff.pure' this must_navigate) := rfl

/-- Protocol. -/
theorem ModeLoiter.has_user_takeoff_val (this : UInt64) (must_navigate : Bool) :
    Id.run (Vehicle_lib.ModeLoiter.has_user_takeoff.pure' this must_navigate) = true := rfl

/-- C++ `Mode::get_wp : bool (Location &) const`, `AP_Common.h:171-?`. -/
theorem Mode.get_wp_eq (this : UInt64) (loc : UInt64) :
    Vehicle_lib.Mode.get_wp this loc = pure (Vehicle_lib.Mode.get_wp.pure' this loc) := rfl

/-- Protocol. -/
theorem Mode.get_wp_val (this : UInt64) (loc : UInt64) :
    Id.run (Vehicle_lib.Mode.get_wp.pure' this loc) = false := rfl

/-- C++ `Mode::is_landing : bool () const`, `AP_Common.h:165-?`. -/
theorem Mode.is_landing_eq (this : UInt64) :
    Vehicle_lib.Mode.is_landing this = pure (Vehicle_lib.Mode.is_landing.pure' this) := rfl

/-- Protocol. -/
theorem Mode.is_landing_val (this : UInt64) :
    Id.run (Vehicle_lib.Mode.is_landing.pure' this) = false := rfl

/-- C++ `ModeLand::is_landing : bool () const`, `mode.h:1319-?`. -/
theorem ModeLand.is_landing_eq (this : UInt64) :
    Vehicle_lib.ModeLand.is_landing this = pure (Vehicle_lib.ModeLand.is_landing.pure' this) := rfl

/-- Protocol. -/
theorem ModeLand.is_landing_val (this : UInt64) :
    Id.run (Vehicle_lib.ModeLand.is_landing.pure' this) = true := rfl

/-- C++ `ModeGuided::get_target_pos_NED_m : const Vector3p &() const`, `mode_guided.cpp:1133-1136`. -/
theorem ModeGuided.get_target_pos_NED_m_eq (this : UInt64) :
    Vehicle_lib.ModeGuided.get_target_pos_NED_m this = pure (Vehicle_lib.ModeGuided.get_target_pos_NED_m.pure' this) := rfl

/-- Protocol (`&guided_pos_target_ned_m`). -/
theorem ModeGuided.get_target_pos_NED_m_val (this : UInt64) :
    Id.run (Vehicle_lib.ModeGuided.get_target_pos_NED_m.pure' this) = (0x12e38 : UInt64) := rfl

/-- C++ `ModeGuided::get_target_vel_NED_ms : const Vector3f &() const`, `mode_guided.cpp:1138-1141`. -/
theorem ModeGuided.get_target_vel_NED_ms_eq (this : UInt64) :
    Vehicle_lib.ModeGuided.get_target_vel_NED_ms this = pure (Vehicle_lib.ModeGuided.get_target_vel_NED_ms.pure' this) := rfl

/-- Protocol (`&guided_vel_target_ned_ms`). -/
theorem ModeGuided.get_target_vel_NED_ms_val (this : UInt64) :
    Id.run (Vehicle_lib.ModeGuided.get_target_vel_NED_ms.pure' this) = (0xeba8 : UInt64) := rfl

/-- C++ `ModeGuided::get_target_accel_NED_mss : const Vector3f &() const`, `mode_guided.cpp:1143-1146`. -/
theorem ModeGuided.get_target_accel_NED_mss_eq (this : UInt64) :
    Vehicle_lib.ModeGuided.get_target_accel_NED_mss this = pure (Vehicle_lib.ModeGuided.get_target_accel_NED_mss.pure' this) := rfl

/-- Protocol (`&guided_accel_target_ned_mss`). -/
theorem ModeGuided.get_target_accel_NED_mss_val (this : UInt64) :
    Id.run (Vehicle_lib.ModeGuided.get_target_accel_NED_mss.pure' this) = (0xebb8 : UInt64) := rfl

/-- C++ `Mode::crosstrack_error_m : float () const`, `AP_Common.h:174-?`. -/
theorem Mode.crosstrack_error_m_eq (this : UInt64) :
    Vehicle_lib.Mode.crosstrack_error_m this = pure (Vehicle_lib.Mode.crosstrack_error_m.pure' this) := rfl

/-- Protocol. -/
theorem Mode.crosstrack_error_m_val (this : UInt64) :
    Id.run (Vehicle_lib.Mode.crosstrack_error_m.pure' this) = (Binary32.ofBits 0x00000000 /- 0 -/) := rfl

/-- C++ `Mode::wp_bearing_deg : float () const`, `AP_Common.h:172-?`. -/
theorem Mode.wp_bearing_deg_eq (this : UInt64) :
    Vehicle_lib.Mode.wp_bearing_deg this = pure (Vehicle_lib.Mode.wp_bearing_deg.pure' this) := rfl

/-- Protocol. -/
theorem Mode.wp_bearing_deg_val (this : UInt64) :
    Id.run (Vehicle_lib.Mode.wp_bearing_deg.pure' this) = Int32.toBinary32 ((0 : Int32)) := rfl

/-- C++ `Mode::wp_distance_m : float () const`, `AP_Common.h:173-?`. -/
theorem Mode.wp_distance_m_eq (this : UInt64) :
    Vehicle_lib.Mode.wp_distance_m this = pure (Vehicle_lib.Mode.wp_distance_m.pure' this) := rfl

/-- Protocol. -/
theorem Mode.wp_distance_m_val (this : UInt64) :
    Id.run (Vehicle_lib.Mode.wp_distance_m.pure' this) = (Binary32.ofBits 0x00000000 /- 0 -/) := rfl

/-- C++ `Mode::enabled : bool () const`, `AP_Common.h:213-?`. -/
theorem Mode.enabled_eq (this : UInt64) :
    Vehicle_lib.Mode.enabled this = pure (Vehicle_lib.Mode.enabled.pure' this) := rfl

/-- Protocol. -/
theorem Mode.enabled_val (this : UInt64) :
    Id.run (Vehicle_lib.Mode.enabled.pure' this) = true := rfl

/-- C++ `Mode::move_vehicle_on_ekf_reset : bool () const`, `AP_Common.h:140-?`. -/
theorem Mode.move_vehicle_on_ekf_reset_eq (this : UInt64) :
    Vehicle_lib.Mode.move_vehicle_on_ekf_reset this = pure (Vehicle_lib.Mode.move_vehicle_on_ekf_reset.pure' this) := rfl

/-- Protocol. -/
theorem Mode.move_vehicle_on_ekf_reset_val (this : UInt64) :
    Id.run (Vehicle_lib.Mode.move_vehicle_on_ekf_reset.pure' this) = false := rfl

/-- C++ `Mode::get_avoidance_adjusted_climbrate_ms : float (float)`, `mode.cpp:1005-1014`. -/
theorem Mode.get_avoidance_adjusted_climbrate_ms_eq (this : UInt64) (target_rate_ms : Binary32) :
    Vehicle_lib.Mode.get_avoidance_adjusted_climbrate_ms this target_rate_ms = pure (Vehicle_lib.Mode.get_avoidance_adjusted_climbrate_ms.pure' this target_rate_ms) := rfl

/-- Protocol. -/
theorem Mode.get_avoidance_adjusted_climbrate_ms_val (this : UInt64) (target_rate_ms : Binary32) :
    Id.run (Vehicle_lib.Mode.get_avoidance_adjusted_climbrate_ms.pure' this target_rate_ms) = target_rate_ms := rfl

/-- C++ `ModeAuto::verify_loiter_unlimited : bool ()`, `mode_auto.cpp:2219-2222`. -/
theorem ModeAuto.verify_loiter_unlimited_eq (this : UInt64) :
    Vehicle_lib.ModeAuto.verify_loiter_unlimited this = pure (Vehicle_lib.ModeAuto.verify_loiter_unlimited.pure' this) := rfl

/-- Protocol. -/
theorem ModeAuto.verify_loiter_unlimited_val (this : UInt64) :
    Id.run (Vehicle_lib.ModeAuto.verify_loiter_unlimited.pure' this) = false := rfl

/-- C++ `Mode::use_pilot_yaw : bool () const`, `AP_Common.h:197-?`. -/
theorem Mode.use_pilot_yaw_eq (this : UInt64) :
    Vehicle_lib.Mode.use_pilot_yaw this = pure (Vehicle_lib.Mode.use_pilot_yaw.pure' this) := rfl

/-- Protocol. -/
theorem Mode.use_pilot_yaw_val (this : UInt64) :
    Id.run (Vehicle_lib.Mode.use_pilot_yaw.pure' this) = true := rfl

/-- C++ `Mode::crash_check_enabled : bool () const`, `AP_Common.h:139-?`. -/
theorem Mode.crash_check_enabled_eq (this : UInt64) :
    Vehicle_lib.Mode.crash_check_enabled this = pure (Vehicle_lib.Mode.crash_check_enabled.pure' this) := rfl

/-- Protocol. -/
theorem Mode.crash_check_enabled_val (this : UInt64) :
    Id.run (Vehicle_lib.Mode.crash_check_enabled.pure' this) = true := rfl

/-- C++ `Mode::requires_terrain_failsafe : bool () const`, `AP_Common.h:168-?`. -/
theorem Mode.requires_terrain_failsafe_eq (this : UInt64) :
    Vehicle_lib.Mode.requires_terrain_failsafe this = pure (Vehicle_lib.Mode.requires_terrain_failsafe.pure' this) := rfl

/-- Protocol. -/
theorem Mode.requires_terrain_failsafe_val (this : UInt64) :
    Id.run (Vehicle_lib.Mode.requires_terrain_failsafe.pure' this) = false := rfl

/-- C++ `ModeAuto::requires_terrain_failsafe : bool () const`, `mode.h:599-?`. -/
theorem ModeAuto.requires_terrain_failsafe_eq (this : UInt64) :
    Vehicle_lib.ModeAuto.requires_terrain_failsafe this = pure (Vehicle_lib.ModeAuto.requires_terrain_failsafe.pure' this) := rfl

/-- Protocol. -/
theorem ModeAuto.requires_terrain_failsafe_val (this : UInt64) :
    Id.run (Vehicle_lib.ModeAuto.requires_terrain_failsafe.pure' this) = true := rfl

/-- C++ `ModeGuided::requires_terrain_failsafe : bool () const`, `mode.h:1128-?`. -/
theorem ModeGuided.requires_terrain_failsafe_eq (this : UInt64) :
    Vehicle_lib.ModeGuided.requires_terrain_failsafe this = pure (Vehicle_lib.ModeGuided.requires_terrain_failsafe.pure' this) := rfl

/-- Protocol. -/
theorem ModeGuided.requires_terrain_failsafe_val (this : UInt64) :
    Id.run (Vehicle_lib.ModeGuided.requires_terrain_failsafe.pure' this) = true := rfl

/-- C++ `ModeRTL::requires_terrain_failsafe : bool () const`, `mode.h:1529-?`. -/
theorem ModeRTL.requires_terrain_failsafe_eq (this : UInt64) :
    Vehicle_lib.ModeRTL.requires_terrain_failsafe this = pure (Vehicle_lib.ModeRTL.requires_terrain_failsafe.pure' this) := rfl

/-- Protocol. -/
theorem ModeRTL.requires_terrain_failsafe_val (this : UInt64) :
    Id.run (Vehicle_lib.ModeRTL.requires_terrain_failsafe.pure' this) = true := rfl

/-- Protocol: the mode numbers of the modes that answer by a constant are distinct (`ModeAuto`'s depends on its
state: `27` (Auto RTL) or `3`). -/
theorem mode_numbers_nodup :
    [Id.run (Vehicle_lib.ModeStabilize.mode_number.pure' 0), Id.run (Vehicle_lib.ModeAltHold.mode_number.pure' 0), Id.run (Vehicle_lib.ModeGuided.mode_number.pure' 0), Id.run (Vehicle_lib.ModeLoiter.mode_number.pure' 0), Id.run (Vehicle_lib.ModeRTL.mode_number.pure' 0), Id.run (Vehicle_lib.ModeCircle.mode_number.pure' 0), Id.run (Vehicle_lib.ModeLand.mode_number.pure' 0), Id.run (Vehicle_lib.ModeBrake.mode_number.pure' 0)].Nodup := by
  decide

end Corpus.ArduCopter

/-! ## The mode-table functions that read memory (second increment)

`ModeAuto` keeps its `auto_RTL` flag at `+861` and its submode at `+820` (`SubMode::NAV_PAYLOAD_PLACE` is `11`);
`AUTO_OPTIONS` is the parameter at `copter + 6840 + 1680` and `GUID_OPTIONS` at `copter + 6840 + 1684`
(`copter` at `0x86d8`; both above the bridged range). -/

namespace Corpus.ArduCopter

open Corpus.Mem (w32)

/-- C++ `ModeAuto::mode_number : Number () const`, `mode.h`: `AUTO_RTL` (27) when the `auto_RTL` flag is set, else
`AUTO` (3); the memory unchanged. -/
theorem ModeAuto.mode_number_run {this : UInt64} (h : PMem.inBridge (this + 861) = false) (s : PMem.Mem) :
    (Vehicle_lib.ModeAuto.mode_number this).run s =
      ((if s.m.get! (this + 861).toNat != 0 then (27 : UInt8) else 3), s) := by
  unfold Vehicle_lib.ModeAuto.mode_number
  simp only [StateT.run_bind, Corpus.Mem.ldB_run h, Corpus.id_bind, Corpus.id_run_eq]
  split <;> rfl

/-- Protocol: the two answers of `ModeAuto::mode_number`. -/
theorem ModeAuto.mode_number_val {this : UInt64} (h : PMem.inBridge (this + 861) = false) (s : PMem.Mem) :
    ((Vehicle_lib.ModeAuto.mode_number this).run s).1 = 27 ∨ ((Vehicle_lib.ModeAuto.mode_number this).run s).1 = 3 := by
  rw [ModeAuto.mode_number_run h]
  by_cases hc : (s.m.get! (this + 861).toNat != 0) = true
  · exact Or.inl (by simp only [hc, ite_true])
  · exact Or.inr (by simp only [hc, Bool.false_eq_true, ite_false])

/-- C++ `ModeAuto::requires_position : bool () const`, `mode.h`: every submode but `NAV_PAYLOAD_PLACE` (11); the
memory unchanged. -/
theorem ModeAuto.requires_position_run {this : UInt64} (h : PMem.inBridge (this + 820) = false) (s : PMem.Mem) :
    (Vehicle_lib.ModeAuto.requires_position this).run s = (s.m.get! (this + 820).toNat != 11, s) := by
  unfold Vehicle_lib.ModeAuto.requires_position
  simp only [StateT.run_bind, Corpus.Mem.ldU8_run h, Corpus.id_bind, Corpus.id_run_eq]
  rfl

/-- C++ `ModeAuto::option_is_enabled : bool (Option) const`, `mode_auto.cpp`: a bit of `AUTO_OPTIONS`; the memory
unchanged. -/
theorem ModeAuto.option_is_enabled_run {this : UInt64} (option : Int32)
    (h : PMem.inBridgeN ((0x86d8 : UInt64) + 6840 + 1680) 4 = false) (s : PMem.Mem) :
    (Vehicle_lib.ModeAuto.option_is_enabled this option).run s =
      ((w32 s.m ((0x86d8 : UInt64) + 6840 + 1680).toNat &&& Int32.toUInt32 option) != Int32.toUInt32 0, s) := by
  unfold Vehicle_lib.ModeAuto.option_is_enabled
  simp only [StateT.run_bind, Corpus.id_bind, Corpus.id_run_eq]
  show (do let w ← PMem.ldU32 ((0x86d8 : UInt64) + 6840 + 1680); pure _ : PMem.M Bool).run s = _
  rw [StateT.run_bind, Corpus.Mem.ldU32_run h]
  rfl

/-- C++ `ModeAuto::allows_arming : bool (AP_Arming::Method) const`, `mode_auto.cpp:219-225`: never in `AUTO_RTL`,
else when `AUTO_OPTIONS` bit 0 (`AllowArming`) is set; the memory unchanged. -/
theorem ModeAuto.allows_arming_run {this : UInt64} (method : Int32) (h : PMem.inBridge (this + 861) = false)
    (hopt : PMem.inBridgeN ((0x86d8 : UInt64) + 6840 + 1680) 4 = false) (s : PMem.Mem) :
    (Vehicle_lib.ModeAuto.allows_arming this method).run s =
      ((if s.m.get! (this + 861).toNat != 0 then false
        else (w32 s.m ((0x86d8 : UInt64) + 6840 + 1680).toNat &&& Int32.toUInt32 1) != Int32.toUInt32 0), s) := by
  unfold Vehicle_lib.ModeAuto.allows_arming
  simp only [StateT.run_bind, Corpus.Mem.ldB_run h, Corpus.id_bind, Corpus.id_run_eq]
  split
  · rfl
  · rw [ModeAuto.option_is_enabled_run 1 hopt]

/-- C++ `ModeGuided::option_is_enabled : bool (Option) const`, `mode_guided.cpp:113-116`: a bit of `GUID_OPTIONS`;
the memory unchanged. -/
theorem ModeGuided.option_is_enabled_run {this : UInt64} (option : UInt32)
    (h : PMem.inBridgeN ((0x86d8 : UInt64) + 6840 + 1684) 4 = false) (s : PMem.Mem) :
    (Vehicle_lib.ModeGuided.option_is_enabled this option).run s =
      ((w32 s.m ((0x86d8 : UInt64) + 6840 + 1684).toNat &&& option) != Int32.toUInt32 0, s) := by
  unfold Vehicle_lib.ModeGuided.option_is_enabled
  simp only [StateT.run_bind, Corpus.id_bind, Corpus.id_run_eq]
  show (do let w ← PMem.ldU32 ((0x86d8 : UInt64) + 6840 + 1684); pure _ : PMem.M Bool).run s = _
  rw [StateT.run_bind, Corpus.Mem.ldU32_run h]
  rfl

/-- C++ `ModeGuided::allows_arming : bool (AP_Arming::Method) const`, `mode_guided.cpp:118-127`: always from the GCS
(methods 1 and 35) or a scripting method (4), else when `GUID_OPTIONS` bit 0 (`AllowArmingFromTX`) is set; the
memory unchanged. -/
theorem ModeGuided.allows_arming_run {this : UInt64} (method : Int32)
    (hopt : PMem.inBridgeN ((0x86d8 : UInt64) + 6840 + 1684) 4 = false) (s : PMem.Mem) :
    (Vehicle_lib.ModeGuided.allows_arming this method).run s =
      ((if (method == 1 || method == 35) || method == 4 then true
        else (w32 s.m ((0x86d8 : UInt64) + 6840 + 1684).toNat &&& 1) != Int32.toUInt32 0), s) := by
  have hg : Vehicle_lib.AP_Arming.method_is_GCS method = pure (method == 1 || method == 35) := rfl
  unfold Vehicle_lib.ModeGuided.allows_arming
  simp only [hg]
  cases hm : ((method == 1 || method == 35) || method == 4)
  · simp only [hm, Bool.false_eq_true, ite_false, StateT.run_bind, StateT.run_pure, Corpus.id_bind,
      Corpus.id_run_eq, pure_bind]
    rw [ModeGuided.option_is_enabled_run 1 hopt]
  · simp only [hm, ite_true, StateT.run_bind, StateT.run_pure, Corpus.id_bind, Corpus.id_run_eq, pure_bind]
    rfl

/-- The two option parameters are not bridged (checked on the addresses). -/
theorem options_not_bridged :
    PMem.inBridgeN ((0x86d8 : UInt64) + 6840 + 1680) 4 = false ∧
      PMem.inBridgeN ((0x86d8 : UInt64) + 6840 + 1684) 4 = false ∧ Vehicle_lib.addr'copter = 0x86d8 := by
  decide

end Corpus.ArduCopter
