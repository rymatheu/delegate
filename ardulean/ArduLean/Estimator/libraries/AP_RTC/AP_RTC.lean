import ArduLean.Runtime.CFloat
import ArduLean.Estimator.libraries.AP_Param.AP_Param

/-!
ArduPilot `libraries/AP_RTC`, part 1 of 2. Sources: `libraries/AP_RTC/AP_RTC.h`, `libraries/AP_RTC/JitterCorrection.h`, `libraries/AP_RTC/JitterCorrection.cpp`.

Items of `lean/Estimator_lib.lean` (the estimator translation), unchanged; placed by `tools/split_modules.py` (`ArduLean/Estimator/INDEX.md`).
-/

open FloatLib.Floats (Binary32 Binary64)

set_option maxRecDepth 200000
-- AP_DAL's `const log_RISH old_RISH = _RISH;` read only by WRITE_REPLAY_BLOCK_IFCHANGED, which is `(void)old`
-- without logging (HAL_LOGGING_ENABLED 0): an unused binding, as in the C++
set_option linter.unusedVariables false

namespace Estimator_lib

namespace JitterCorrection

/-- State of C++ `JitterCorrection` (`AP_RTC/JitterCorrection.h:7-29`): its data members. -/
structure State where
  /-- `const uint16_t max_lag_ms` of `JitterCorrection` (`AP_RTC/JitterCorrection.h:23`). -/
  max_lag_ms : UInt16 := (0 : UInt16)
  /-- `const uint16_t convergence_loops` of `JitterCorrection` (`AP_RTC/JitterCorrection.h:24`). -/
  convergence_loops : UInt16 := (0 : UInt16)
  /-- `int64_t link_offset_usec` of `JitterCorrection` (`AP_RTC/JitterCorrection.h:25`). -/
  link_offset_usec : Int64 := (0 : Int64)
  /-- `int64_t min_sample_us` of `JitterCorrection` (`AP_RTC/JitterCorrection.h:26`). -/
  min_sample_us : Int64 := (0 : Int64)
  /-- `bool initialised` of `JitterCorrection` (`AP_RTC/JitterCorrection.h:27`). -/
  initialised : Bool := false
  /-- `uint16_t min_sample_counter` of `JitterCorrection` (`AP_RTC/JitterCorrection.h:28`). -/
  min_sample_counter : UInt16 := (0 : UInt16)
deriving Inhabited

end JitterCorrection

namespace AP_RTC

/-- C++ `enum AP_RTC::source_type`, `AP_RTC/AP_RTC.h:25-30`. -/
inductive source_type where
  | SOURCE_GPS
  | SOURCE_MAVLINK_SYSTEM_TIME
  | SOURCE_HW
  | SOURCE_NONE
deriving DecidableEq, Inhabited

/-- The value of each enumerator of `AP_RTC::source_type` (underlying type `uint8_t`). -/
def source_type.toInt : source_type → UInt8
  | .SOURCE_GPS => (0 : UInt8)
  | .SOURCE_MAVLINK_SYSTEM_TIME => (1 : UInt8)
  | .SOURCE_HW => (2 : UInt8)
  | .SOURCE_NONE => (3 : UInt8)

/-- State of C++ `AP_RTC` (`AP_RTC/AP_RTC.h:11-86`): its data members. -/
structure State where
  /-- `AP_UInt8 allowed_types` of `AP_RTC` (`AP_RTC/AP_RTC.h:19`). -/
  allowed_types : AP_ParamT_unsigned_char_1.State := {}
  /-- `AP_Int16 tz_min` of `AP_RTC` (`AP_RTC/AP_RTC.h:20`). -/
  tz_min : AP_ParamT_short_2.State := {}
  /-- `source_type rtc_source_type` of `AP_RTC` (`AP_RTC/AP_RTC.h:79`). -/
  rtc_source_type : AP_RTC.source_type := AP_RTC.source_type.SOURCE_NONE
  /-- `int64_t rtc_shift` of `AP_RTC` (`AP_RTC/AP_RTC.h:80`). -/
  rtc_shift : Int64 := (0 : Int64)
deriving Inhabited

/-- Values C++ `AP_RTC` reads from objects outside the translation (--boundary): one field per distinct read, in first-use order. -/
structure Inputs where
  /-- `hal.util.get_soft_armed()` (first read at `AP_RTC/AP_RTC.cpp:53`). -/
  get_soft_armed : Bool := false
deriving Inhabited

end AP_RTC

namespace JitterCorrection

/-- C++ `JitterCorrection::JitterCorrection(uint16_t max_lag_ms, uint16_t convergence_loops)`, `AP_RTC/JitterCorrection.cpp:39-42`. -/
def init (_max_lag_ms : UInt16 := Int16.toUInt16 (Int32.toInt16 (500 : Int32))) (_convergence_loops : UInt16 := Int16.toUInt16 (Int32.toInt16 (100 : Int32))) : State := Id.run do
  let mut s : State := {}
  s := { s with max_lag_ms := _max_lag_ms }
  s := { s with convergence_loops := _convergence_loops }
  return s

end JitterCorrection

end Estimator_lib
