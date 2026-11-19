import ArduLean.Runtime.Memory
import ArduLean.Vehicle.libraries.AP_HAL.AP_HAL_2

/-!
ArduPilot `libraries/AP_InternalError`. Sources: `libraries/AP_InternalError/AP_InternalError.cpp`, `libraries/AP_InternalError/AP_InternalError.h`.

Items of `lean/Vehicle_lib.lean` (the vehicle translation), unchanged; placed by `tools/split_modules.py` (`ArduLean/Vehicle/INDEX.md`).
-/

open FloatLib.Floats (Binary32 Binary64)

set_option linter.unusedVariables false
set_option linter.unreachableTactic false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false

namespace Vehicle_lib

/-- C++ `AP_InternalError::errors : uint32_t () const`, `AP_InternalError.h:96-98`. -/
def AP_InternalError.errors (this : UInt64) : PMem.M UInt32 := do
  let t'1 ← PMem.ldU32 this
  return t'1

/-- C++ `AP_InternalError::errors_as_string : void (uint8_t *, const uint16_t) const`, `AP_InternalError.cpp:84-106`. -/
def AP_InternalError.errors_as_string.body (fp : UInt64) (this : UInt64) (buffer : UInt64) (len : UInt16) : PMem.M Unit := do
  let mut buffer := buffer
  let mut len := len
  let t'1 := Int8.toUInt8 (Int32.toInt8 ((0 : Int32)))
  PMem.stU8 (buffer + ((Int32.toInt64 ((0 : Int32))) * 1).toUInt64) t'1
  let mut buffer_used : UInt32 := Int32.toUInt32 ((0 : Int32))
  let mut format : UInt64 := (0x13fd2 : UInt64) /- "%s" -/
  let mut i : UInt8 := Int8.toUInt8 (Int32.toInt8 ((0 : Int32)))
  let mut first'2 := true
  for _ in PMem.loopFuel do
    if !first'2 then
      let t'3 := i
      let t'4 := (t'3 + 1)
      i := t'4
      pure ()
    first'2 := false
    if !((decide ((UInt8.toUInt64 (i)) < ((240 : UInt64) / (8 : UInt64))))) then break
    if (decide (buffer_used ≥ (UInt16.toUInt32 (len)))) then
      break
    let t'5 ← PMem.ldU32 this
    if (t'5 &&& ((1 : UInt32) <<< (Int32.toUInt32 ((UInt32.toInt32 (UInt8.toUInt32 (i))))))) != (0 : UInt32) then
      let t'6 ← PMem.ldU64 ((0x131f0 : UInt64) /- &error_bit_descriptions -/ + ((UInt64.toInt64 (UInt8.toUInt64 (i))) * 8).toUInt64)
      PMem.stU64 (fp + 0) t'6
      let t'7 ← AP_HAL.Util.snprintf (0 : UInt64) (buffer + ((UInt64.toInt64 (UInt32.toUInt64 (buffer_used))) * 1).toUInt64) (UInt32.toUInt64 (((UInt16.toUInt32 (len)) - buffer_used))) format (fp + 0)
      let mut written : Int32 := t'7
      let t'8 := (0x18693 : UInt64) /- ",%s" -/
      format := t'8
      if (decide (written < (0 : Int32))) then
        break
      let t'9 := (buffer_used + (Int32.toUInt32 (written)))
      buffer_used := t'9
  return ()

def AP_InternalError.errors_as_string (this : UInt64) (buffer : UInt64) (len : UInt16) : PMem.M Unit := do
  let fp ← PMem.enter 8
  let r ← AP_InternalError.errors_as_string.body fp this buffer len
  PMem.leave fp
  return r

/-- C++ `AP_InternalError::last_error_line : uint16_t () const`, `AP_InternalError.h:82-?`. -/
def AP_InternalError.last_error_line (this : UInt64) : PMem.M UInt16 := do
  let t'1 ← PMem.ldU16 (this + 8)
  return t'1

/-- C++ `AP_InternalError::count : uint32_t () const`, `AP_InternalError.h:93-?`. -/
def AP_InternalError.count (this : UInt64) : PMem.M UInt32 := do
  let t'1 ← PMem.ldU32 (this + 4)
  return t'1

end Vehicle_lib
