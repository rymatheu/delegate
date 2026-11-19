import ArduLean.Runtime.CFloat
import ArduLean.Estimator.libraries.AP_Param.AP_Param
import ArduLean.Estimator.libraries.AP_RTC.AP_RTC
import ArduLean.Estimator.World_2
import ArduLean.Estimator.World_3

/-!
ArduPilot `libraries/AP_RTC`, part 2 of 2. Sources: `libraries/AP_RTC/AP_RTC.cpp`.

Items of `lean/Estimator_lib.lean` (the estimator translation), unchanged; placed by `tools/split_modules.py` (`ArduLean/Estimator/INDEX.md`).
-/

open FloatLib.Floats (Binary32 Binary64)

set_option maxRecDepth 200000
-- AP_DAL's `const log_RISH old_RISH = _RISH;` read only by WRITE_REPLAY_BLOCK_IFCHANGED, which is `(void)old`
-- without logging (HAL_LOGGING_ENABLED 0): an unused binding, as in the C++
set_option linter.unusedVariables false

namespace Estimator_lib

namespace AP_RTC

/-- C++ `void AP_RTC::set_utc_usec(uint64_t time_utc_usec, source_type type)`, `AP_RTC/AP_RTC.cpp:47-104`. -/
def set_utc_usec (s : State) (w : World) (o : Outputs) (inp : Inputs) (time_utc_usec : UInt64) (type : AP_RTC.source_type) : State × Outputs := Id.run do
  let mut s := s
  let mut o := o
  let oldest_acceptable_date_us : UInt64 := (1640995200 : UInt64) * Int64.toUInt64 (Int32.toInt64 (1000 : Int32)) * Int64.toUInt64 (Int32.toInt64 (1000 : Int32))
  if inp.get_soft_armed then
    if UInt32.toInt32 (UInt8.toUInt32 (AP_RTC.source_type.toInt type)) ≥ UInt32.toInt32 (UInt8.toUInt32 (AP_RTC.source_type.toInt s.rtc_source_type)) then
      return (s, o)
  else
    if UInt32.toInt32 (UInt8.toUInt32 (AP_RTC.source_type.toInt type)) > UInt32.toInt32 (UInt8.toUInt32 (AP_RTC.source_type.toInt s.rtc_source_type)) then
      return (s, o)
  if !((UInt32.toInt32 (UInt8.toUInt32 (AP_ParamT_unsigned_char_1.op_to_unsigned_char s.allowed_types)) &&& ((1 : Int32) <<< UInt32.toInt32 (UInt8.toUInt32 (AP_RTC.source_type.toInt type)))) != (0 : Int32)) then
    return (s, o)
  if time_utc_usec < oldest_acceptable_date_us then
    return (s, o)
  let now : UInt64 := Estimator_lib.micros64 w
  let tmp : Int64 := UInt64.toInt64 time_utc_usec - UInt64.toInt64 now
  if tmp < s.rtc_shift then
    return (s, o)
  pure ()  -- C++ `_getsem30`: a semaphore, which does nothing here (one thread, --semaphores)
  s := { s with rtc_shift := tmp }
  if UInt32.toInt32 (UInt8.toUInt32 (AP_RTC.source_type.toInt type)) != UInt32.toInt32 (UInt8.toUInt32 (AP_RTC.source_type.toInt AP_RTC.source_type.SOURCE_HW)) then
    o := o.push (Output.set_hw_rtc time_utc_usec)
  s := { s with rtc_source_type := type }
  return (s, o)

end AP_RTC

namespace AP_RTC

/-- C++ `bool AP_RTC::get_utc_usec(uint64_t & usec) const`, `AP_RTC/AP_RTC.cpp:106-113`. -/
def get_utc_usec (s : State) (w : World) (usec : UInt64) : UInt64 × Bool := Id.run do
  let mut usec := usec
  if UInt32.toInt32 (UInt8.toUInt32 (AP_RTC.source_type.toInt s.rtc_source_type)) == UInt32.toInt32 (UInt8.toUInt32 (AP_RTC.source_type.toInt AP_RTC.source_type.SOURCE_NONE)) then
    return (usec, false)
  usec := Estimator_lib.micros64 w + Int64.toUInt64 s.rtc_shift
  return (usec, true)

/-- C++ `void AP_RTC::clock_ms_to_hms_fields(const uint64_t time_ms, uint8_t & hour, uint8_t & min, uint8_t & sec, uint16_t & ms) const`, `AP_RTC/AP_RTC.cpp:115-127`. -/
def clock_ms_to_hms_fields (time_ms : UInt64) (hour : UInt8) (min : UInt8) (sec : UInt8) (ms : UInt16) : UInt8 × UInt8 × UInt8 × UInt16 := Id.run do
  let mut hour := hour
  let mut min := min
  let mut sec := sec
  let mut ms := ms
  ms := UInt64.toUInt16 (time_ms % Int64.toUInt64 (Int32.toInt64 (1000 : Int32)))
  let sec_ms : UInt32 := UInt64.toUInt32 ((time_ms % Int64.toUInt64 (Int32.toInt64 ((60 : Int32) * (1000 : Int32)))) - UInt16.toUInt64 ms)
  let min_ms : UInt32 := UInt64.toUInt32 ((time_ms % Int64.toUInt64 (Int32.toInt64 ((60 : Int32) * (60 : Int32) * (1000 : Int32)))) - UInt32.toUInt64 sec_ms - UInt16.toUInt64 ms)
  let hour_ms : UInt32 := UInt64.toUInt32 ((time_ms % Int64.toUInt64 (Int32.toInt64 ((24 : Int32) * (60 : Int32) * (60 : Int32) * (1000 : Int32)))) - UInt32.toUInt64 min_ms - UInt32.toUInt64 sec_ms - UInt16.toUInt64 ms)
  sec := UInt32.toUInt8 (sec_ms / Int32.toUInt32 (1000 : Int32))
  min := UInt32.toUInt8 (min_ms / Int32.toUInt32 ((60 : Int32) * (1000 : Int32)))
  hour := UInt32.toUInt8 (hour_ms / Int32.toUInt32 ((60 : Int32) * (60 : Int32) * (1000 : Int32)))
  return (hour, min, sec, ms)

/-- C++ `bool AP_RTC::get_system_clock_utc(uint8_t & hour, uint8_t & min, uint8_t & sec, uint16_t & ms) const`, `AP_RTC/AP_RTC.cpp:207-217`. -/
def get_system_clock_utc (s : State) (w : World) (hour : UInt8) (min : UInt8) (sec : UInt8) (ms : UInt16) : UInt8 × UInt8 × UInt8 × UInt16 × Bool := Id.run do
  let mut hour := hour
  let mut min := min
  let mut sec := sec
  let mut ms := ms
  let mut time_ms : UInt64 := (0 : UInt64)  -- uninitialized in C++; assigned before every read
  let (t'1, t'2) := get_utc_usec s w time_ms
  time_ms := t'1
  if !t'2 then
    return (hour, min, sec, ms, false)
  time_ms := time_ms / UInt32.toUInt64 (1000 : UInt32)
  let (t'3, t'4, t'5, t'6) := clock_ms_to_hms_fields time_ms hour min sec ms
  hour := t'3
  min := t'4
  sec := t'5
  ms := t'6
  return (hour, min, sec, ms, true)

/-- C++ `uint32_t AP_RTC::get_time_utc(int32_t hour, int32_t min, int32_t sec, int32_t ms)`, `AP_RTC/AP_RTC.cpp:238-297`. -/
def get_time_utc (s : State) (w : World) (hour : Int32) (min : Int32) (sec : Int32) (ms : Int32) : UInt32 := Id.run do
  let mut largest_element : Int8 := Int32.toInt8 (0 : Int32)
  if hour != -(1 : Int32) then
    largest_element := Int32.toInt8 (4 : Int32)
  else if min != -(1 : Int32) then
    largest_element := Int32.toInt8 (3 : Int32)
  else if sec != -(1 : Int32) then
    largest_element := Int32.toInt8 (2 : Int32)
  else if ms != -(1 : Int32) then
    largest_element := Int32.toInt8 (1 : Int32)
  else
    return Int32.toUInt32 (0 : Int32)
  let mut curr_hour : UInt8 := (0 : UInt8)  -- uninitialized in C++; assigned before every read
  let mut curr_min : UInt8 := (0 : UInt8)  -- uninitialized in C++; assigned before every read
  let mut curr_sec : UInt8 := (0 : UInt8)  -- uninitialized in C++; assigned before every read
  let mut curr_ms : UInt16 := (0 : UInt16)  -- uninitialized in C++; assigned before every read
  let (t'1, t'2, t'3, t'4, t'5) := get_system_clock_utc s w curr_hour curr_min curr_sec curr_ms
  curr_hour := t'1
  curr_min := t'2
  curr_sec := t'3
  curr_ms := t'4
  if !t'5 then
    return Int32.toUInt32 (0 : Int32)
  let mut total_delay_ms : Int32 := (0 : Int32)
  if Int8.toInt32 largest_element ≥ (1 : Int32) then
    total_delay_ms := total_delay_ms + (ms - UInt32.toInt32 (UInt16.toUInt32 curr_ms))
  if Int8.toInt32 largest_element == (1 : Int32) && decide (total_delay_ms < (0 : Int32)) then
    return Int32.toUInt32 (total_delay_ms + (1000 : Int32))
  if Int8.toInt32 largest_element ≥ (2 : Int32) then
    total_delay_ms := total_delay_ms + (sec - UInt32.toInt32 (UInt8.toUInt32 curr_sec)) * (1000 : Int32)
  if Int8.toInt32 largest_element == (2 : Int32) && decide (total_delay_ms < (0 : Int32)) then
    return Int32.toUInt32 (total_delay_ms + ((60 : Int32) * (1000 : Int32)))
  if Int8.toInt32 largest_element ≥ (3 : Int32) then
    total_delay_ms := total_delay_ms + (min - UInt32.toInt32 (UInt8.toUInt32 curr_min)) * (60 : Int32) * (1000 : Int32)
  if Int8.toInt32 largest_element == (3 : Int32) && decide (total_delay_ms < (0 : Int32)) then
    return Int32.toUInt32 (total_delay_ms + ((60 : Int32) * (60 : Int32) * (1000 : Int32)))
  if Int8.toInt32 largest_element ≥ (4 : Int32) then
    total_delay_ms := total_delay_ms + (hour - UInt32.toInt32 (UInt8.toUInt32 curr_hour)) * (60 : Int32) * (60 : Int32) * (1000 : Int32)
  if Int8.toInt32 largest_element == (4 : Int32) && decide (total_delay_ms < (0 : Int32)) then
    return Int32.toUInt32 (total_delay_ms + ((24 : Int32) * (60 : Int32) * (60 : Int32) * (1000 : Int32)))
  return Int32.toUInt32 total_delay_ms

/-- C++ `AP_RTC::AP_RTC()`, `AP_RTC/AP_RTC.cpp:15-24`. -/
def init : State := Id.run do
  let mut s : State := {}
  s := { s with allowed_types._value := Int8.toUInt8 (Binary32.toInt8 (Binary32.ofBits 0x3f800000 /- (float)1 -/)) }
  s := { s with tz_min._value := Binary32.toInt16 (Binary32.ofBits 0x00000000 /- (float)0 -/) }
  if false /- C++ `_singleton != nullptr` -/ then
    return s
  pure ()  -- C++ `_singleton = this`: the pointer is the class's one World object (--world)
  return s

end AP_RTC

end Estimator_lib
