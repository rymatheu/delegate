import ArduLean.Runtime.CFloat
import ArduLean.Estimator.libraries.AP_Math.AP_Math
import ArduLean.Estimator.libraries.AP_Common.AP_Common
import ArduLean.Estimator.libraries.AP_AHRS.AP_AHRS
import ArduLean.Estimator.World_3
import ArduLean.Estimator.libraries.AP_AHRS.AP_AHRS_2

/-!
ArduPilot `libraries/AP_Common`, part 3 of 3. Sources: `libraries/AP_Common/Location.cpp`.

Items of `lean/Estimator_lib.lean` (the estimator translation), unchanged; placed by `tools/split_modules.py` (`ArduLean/Estimator/INDEX.md`).
-/

open FloatLib.Floats (Binary32 Binary64)

set_option maxRecDepth 200000
-- AP_DAL's `const log_RISH old_RISH = _RISH;` read only by WRITE_REPLAY_BLOCK_IFCHANGED, which is `(void)old`
-- without logging (HAL_LOGGING_ENABLED 0): an unused binding, as in the C++
set_option linter.unusedVariables false

namespace Estimator_lib

namespace Location

/-- C++ `bool Location::check_latlng() const`, `AP_Common/Location.cpp:601-604`. -/
def check_latlng (s : State) : Bool := Id.run do
  return Estimator_lib.check_lat_int32_t s.lat && Estimator_lib.check_lng_int32_t s.lng

/-- C++ `AltFrame Location::get_alt_frame() const`, `AP_Common/Location.cpp:128-145`. -/
def get_alt_frame (s : State) : Location.AltFrame := Id.run do
  if s.terrain_alt != (0 : UInt8) then
    if !(s.relative_alt != (0 : UInt8)) then
      pure ()  -- C++ `AP_HAL::panic(...)`: left out (--drop)
    return Location.AltFrame.ABOVE_TERRAIN
  if s.origin_alt != (0 : UInt8) then
    return Location.AltFrame.ABOVE_ORIGIN
  if s.relative_alt != (0 : UInt8) then
    return Location.AltFrame.ABOVE_HOME
  return Location.AltFrame.ABSOLUTE

/-- C++ `bool Location::get_alt_cm(AltFrame desired_frame, int32_t & ret_alt_cm) const`, `AP_Common/Location.cpp:148-253`. -/
def get_alt_cm (s : State) (w : World) (desired_frame : Location.AltFrame) (ret_alt_cm : Int32) : Int32 × Bool := Id.run do
  let mut ret_alt_cm := ret_alt_cm
  if !(initialised s) then
    pure ()  -- C++ `AP_HAL::panic(...)`: left out (--drop)
  if s.terrain_alt != (0 : UInt8) && !(s.relative_alt != (0 : UInt8)) then
    pure ()  -- C++ `AP_HAL::panic(...)`: left out (--drop)
  let frame : Location.AltFrame := get_alt_frame s
  if desired_frame == frame then
    ret_alt_cm := s.alt
    return (ret_alt_cm, true)
  let alt_terr_cm : Binary32 := (Binary32.ofBits 0x00000000 /- 0 -/)
  if frame == Location.AltFrame.ABOVE_TERRAIN || desired_frame == Location.AltFrame.ABOVE_TERRAIN then
    return (ret_alt_cm, false)
  let mut alt_abs : Int32 := (0 : Int32)
  match frame with
  | .ABSOLUTE =>
    alt_abs := s.alt
  | .ABOVE_HOME =>
    if !(AP_AHRS.home_is_set w.ahrs) then
      return (ret_alt_cm, false)
    alt_abs := s.alt + w.ahrs._home.alt
  | .ABOVE_ORIGIN =>
    let mut ekf_origin : Location.State := Location.init_void
    let (t'1, t'2) := AP_AHRS.get_origin w.ahrs ekf_origin
    ekf_origin := t'1
    if !t'2 then
      return (ret_alt_cm, false)
    alt_abs := s.alt + ekf_origin.alt
  | .ABOVE_TERRAIN =>
    alt_abs := Binary32.toInt32 (Int32.toBinary32 s.alt + alt_terr_cm)
  match desired_frame with
  | .ABSOLUTE =>
    ret_alt_cm := alt_abs
    return (ret_alt_cm, true)
  | .ABOVE_HOME =>
    if !(AP_AHRS.home_is_set w.ahrs) then
      return (ret_alt_cm, false)
    ret_alt_cm := alt_abs - w.ahrs._home.alt
    return (ret_alt_cm, true)
  | .ABOVE_ORIGIN =>
    let mut ekf_origin'2 : Location.State := Location.init_void
    let (t'3, t'4) := AP_AHRS.get_origin w.ahrs ekf_origin'2
    ekf_origin'2 := t'3
    if !t'4 then
      return (ret_alt_cm, false)
    ret_alt_cm := alt_abs - ekf_origin'2.alt
    return (ret_alt_cm, true)
  | .ABOVE_TERRAIN =>
    ret_alt_cm := Binary32.toInt32 (Int32.toBinary32 alt_abs - alt_terr_cm)
    return (ret_alt_cm, true)

/-- C++ `bool Location::change_alt_frame(AltFrame desired_frame)`, `AP_Common/Location.cpp:109-117`. -/
def change_alt_frame (s : State) (w : World) (desired_frame : Location.AltFrame) : State × Bool := Id.run do
  let mut s := s
  let mut new_alt_cm : Int32 := (0 : Int32)  -- uninitialized in C++; assigned before every read
  let (t'1, t'2) := get_alt_cm s w desired_frame new_alt_cm
  new_alt_cm := t'1
  if !t'2 then
    return (s, false)
  s := set_alt_cm s new_alt_cm desired_frame
  return (s, true)

end Location

end Estimator_lib
