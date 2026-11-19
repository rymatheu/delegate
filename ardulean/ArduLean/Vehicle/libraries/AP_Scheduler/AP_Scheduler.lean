import ArduLean.Runtime.Hal
import ArduLean.Vehicle.libraries.AP_Math.AP_Math
import ArduLean.Vehicle.libraries.AP_HAL.AP_HAL
import ArduLean.Vehicle.libraries.AP_Param.AP_Param
import ArduLean.Vehicle.libraries.AP_Vehicle.AP_Vehicle

/-!
ArduPilot `libraries/AP_Scheduler`. Sources: `libraries/AP_Scheduler/AP_Scheduler.cpp`, `libraries/AP_Scheduler/PerfInfo.cpp`, `libraries/AP_Scheduler/PerfInfo.h`.

Items of `lean/Vehicle_lib.lean` (the vehicle translation), unchanged; placed by `tools/split_modules.py` (`ArduLean/Vehicle/INDEX.md`).
-/

open FloatLib.Floats (Binary32 Binary64)

set_option linter.unusedVariables false
set_option linter.unreachableTactic false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false

namespace Vehicle_lib

/-- C++ `AP_Scheduler::get_singleton : AP_Scheduler *()`, `AP_Scheduler.cpp:98-101`. -/
def AP_Scheduler.get_singleton  : PMem.M UInt64 := do
  let t'1 ← PMem.ldU64 (0xccb8 : UInt64) /- &AP_Scheduler::_singleton -/
  return t'1

/-- C++ `AP::scheduler : AP_Scheduler &()`, `AP_Scheduler.cpp:552-555`. -/
def AP.scheduler  : PMem.M UInt64 := do
  let t'1 ← AP_Scheduler.get_singleton
  return t'1

/-- C++ `AP_Scheduler::ticks32 : uint32_t () const`, `functor.h:125-?`. -/
def AP_Scheduler.ticks32 (this : UInt64) : PMem.M UInt32 := do
  let t'1 ← PMem.ldU32 (this + 100)
  return t'1

/-- C++ `AP_Scheduler::get_loop_rate_hz : uint16_t ()`, `functor.h:144-150`. -/
def AP_Scheduler.get_loop_rate_hz (this : UInt64) : PMem.M UInt16 := do
  let t'1 ← PMem.ldU16 (this + 60)
  if ((UInt32.toInt32 (UInt16.toUInt32 (t'1))) == (0 : Int32)) then
    let t'2 ← AP_ParamT'short_2.operator_const_short__ (this + 58)
    let t'3 ← PMem.ldI16 t'2
    let t'4 := Int16.toUInt16 (t'3)
    PMem.stU16 (this + 60) t'4
  let t'5 ← PMem.ldU16 (this + 60)
  return t'5

/-- C++ `AP::PerfInfo::get_filtered_time : float () const`, `PerfInfo.cpp:198-201`. -/
def AP.PerfInfo.get_filtered_time (this : UInt64) : PMem.M Binary32 := do
  let t'1 ← PMem.ldF32 (this + 40)
  return t'1

/-- C++ `AP::PerfInfo::get_filtered_loop_rate_hz : float () const`, `PerfInfo.cpp:204-211`. -/
def AP.PerfInfo.get_filtered_loop_rate_hz (this : UInt64) : PMem.M Binary32 := do
  let t'1 ← AP.PerfInfo.get_filtered_time this
  let mut filt_time_s : Binary32 := t'1
  if (decide (filt_time_s ≤ (Int32.toBinary32 ((0 : Int32))))) then
    let t'2 ← PMem.ldU16 this
    return UInt16.toBinary32 (t'2)
  return ((Binary64.toBinary32 ((Binary64.ofBits 0x3ff0000000000000 /- 1 -/))) / filt_time_s)

/-- C++ `AP_Scheduler::get_filtered_loop_rate_hz : float ()`, `<scratch space>:174-176`. -/
def AP_Scheduler.get_filtered_loop_rate_hz (this : UInt64) : PMem.M Binary32 := do
  let t'1 ← AP.PerfInfo.get_filtered_loop_rate_hz this
  return t'1

/-- C++ `AP::PerfInfo::ignore_this_loop : void ()`, `PerfInfo.cpp:40-43`. -/
def AP.PerfInfo.ignore_this_loop (this : UInt64) : PMem.M Unit := do
  PMem.stB (this + 44) true
  return ()

/-- C++ `AP_Scheduler::get_loop_period_us : uint32_t ()`, `<scratch space>:152-158`. -/
def AP_Scheduler.get_loop_period_us (this : UInt64) : PMem.M UInt32 := do
  let t'1 ← PMem.ldU16 (this + 64)
  if ((UInt32.toInt32 (UInt16.toUInt32 (t'1))) == (0 : Int32)) then
    let t'2 ← AP_ParamT'short_2.operator_const_short__ (this + 58)
    let t'3 ← PMem.ldI16 t'2
    let t'4 := UInt64.toUInt16 (((1000000 : UInt64) / (Int64.toUInt64 (Int16.toInt64 (t'3)))))
    PMem.stU16 (this + 64) t'4
  let t'5 ← PMem.ldU16 (this + 64)
  return UInt16.toUInt32 (t'5)

/-- C++ `AP_Scheduler::load_average : float ()`, `AP_Scheduler.cpp:334-346`. -/
def AP_Scheduler.load_average (this : UInt64) : PMem.M Binary32 := do
  let t'1 ← AP_Scheduler.get_filtered_loop_rate_hz this
  let t'2 ← AP_Scheduler.get_loop_rate_hz this
  if (decide (t'1 < ((Int32.toBinary32 ((UInt32.toInt32 (UInt16.toUInt32 (t'2))))) * (Binary64.toBinary32 ((Binary64.ofBits 0x3fee666666666666 /- 23749999999999999/25000000000000000 -/)))))) then
    return Binary64.toBinary32 ((Binary64.ofBits 0x3ff0000000000000 /- 1 -/))
  let t'3 ← PMem.ldU8 (this + 124)
  if ((UInt32.toInt32 (UInt8.toUInt32 (t'3))) == (0 : Int32)) then
    return (Binary32.ofBits 0x00000000 /- 0 -/)
  let t'4 ← AP_Scheduler.get_loop_period_us this
  let mut loop_us : UInt32 := t'4
  let t'5 ← PMem.ldU32 (this + 120)
  let t'6 ← PMem.ldU8 (this + 124)
  let mut used_time : UInt32 := (loop_us - (t'5 / (UInt8.toUInt32 (t'6))))
  let t'7 ← constrain_value_line'float ((UInt32.toBinary32 (used_time)) / (UInt32.toBinary32 (loop_us))) (Int32.toBinary32 ((0 : Int32))) (Int32.toBinary32 ((1 : Int32))) (Int32.toUInt32 ((345 : Int32)))
  return t'7

/-- C++ `AP_Scheduler::time_available_usec : uint16_t () const`, `AP_Scheduler.cpp:322-329`. -/
def AP_Scheduler.time_available_usec (this : UInt64) : PMem.M UInt16 := do
  let t'1 ← PMem.ldU32 (this + 116)
  let mut dt : UInt32 := (((← PMem.clock).toUInt32) - t'1)
  let t'2 ← PMem.ldU32 (this + 112)
  if (decide (dt > t'2)) then
    return Int16.toUInt16 (Int32.toInt16 ((0 : Int32)))
  let t'3 ← PMem.ldU32 (this + 112)
  return UInt32.toUInt16 ((t'3 - dt))

/-- C++ `AP::PerfInfo::set_loop_rate : void (uint16_t)`, `PerfInfo.cpp:227-236`. -/
def AP.PerfInfo.set_loop_rate (this : UInt64) (rate_hz : UInt16) : PMem.M Unit := do
  let mut rate_hz := rate_hz
  let t'1 := Binary32.toUInt16 (((Int32.toBinary32 (((1000000 : Int32) / (UInt32.toInt32 (UInt16.toUInt32 (rate_hz)))))) * (Binary32.ofBits 0x3f99999a /- 24000001/20000000 -/)))
  PMem.stU16 (this + 2) t'1
  let t'2 ← PMem.ldU16 this
  if ((UInt32.toInt32 (UInt16.toUInt32 (t'2))) != (UInt32.toInt32 (UInt16.toUInt32 (rate_hz)))) then
    PMem.stU16 this rate_hz
    let t'3 := ((Binary32.ofBits 0x3f800000 /- 1 -/) / (Int32.toBinary32 ((UInt32.toInt32 (UInt16.toUInt32 (rate_hz))))))
    PMem.stF32 (this + 40) t'3
  return ()

/-- C++ `AP::PerfInfo::reset : void ()`, `PerfInfo.cpp:26-37`. -/
def AP.PerfInfo.reset (this : UInt64) : PMem.M Unit := do
  let t'1 := Int16.toUInt16 (Int32.toInt16 ((0 : Int32)))
  PMem.stU16 (this + 4) t'1
  let t'2 := Int32.toUInt32 ((0 : Int32))
  PMem.stU32 (this + 8) t'2
  let t'3 := Int32.toUInt32 ((0 : Int32))
  PMem.stU32 (this + 12) t'3
  let t'4 := Int16.toUInt16 (Int32.toInt16 ((0 : Int32)))
  PMem.stU16 (this + 32) t'4
  let t'5 := Int64.toUInt64 (Int32.toInt64 ((0 : Int32)))
  PMem.stU64 (this + 16) t'5
  let t'6 := Int64.toUInt64 (Int32.toInt64 ((0 : Int32)))
  PMem.stU64 (this + 24) t'6
  let t'7 ← PMem.ldU64 (this + 48)
  if (t'7 != (0 : UInt64)) then
    let t'8 ← PMem.ldU64 (this + 48)
    let t'9 ← PMem.ldU8 (this + 45)
    let t'10 ← PMem.memset t'8 (0 : Int32) ((UInt8.toUInt64 (t'9)) * (16 : UInt64))
    discard <| pure (t'10)
  return ()

/-- C++ `AP::PerfInfo::allocate_task_info : void (uint8_t)`, `PerfInfo.cpp:46-55`. -/
def AP.PerfInfo.allocate_task_info (this : UInt64) (num_tasks : UInt8) : PMem.M Unit := do
  let mut num_tasks := num_tasks
  let t'1 ← PMem.alloc ((UInt8.toUInt64 (num_tasks)).toNat * 16)
  PMem.stU64 (this + 48) t'1
  let t'2 ← PMem.ldU64 (this + 48)
  if (t'2 == (0 : UInt64)) then
    for _ in [0:1] do
      let t'3 ← PMem.ldU64 ((0xba88 : UInt64) /- &hal -/ + 48)
      discard <| PMem.halDev "AP_HAL::BetterStream::printf" t'3 #[(0x182c1 : UInt64) /- "Unable to allocate scheduler TaskInfo\n" -/]
    let t'4 := Int8.toUInt8 (Int32.toInt8 ((0 : Int32)))
    PMem.stU8 (this + 45) t'4
    return ()
  PMem.stU8 (this + 45) num_tasks
  return ()

/-- C++ `AP_Scheduler::init : void (const AP_Scheduler::Task *, uint8_t, uint32_t)`, `AP_Scheduler.cpp:104-166`. -/
def AP_Scheduler.init.body (fp : UInt64) (this : UInt64) (tasks : UInt64) (num_tasks : UInt8) (log_performance_bit : UInt32) : PMem.M Unit := do
  let mut tasks := tasks
  let mut num_tasks := num_tasks
  let mut log_performance_bit := log_performance_bit
  let t'1 ← AP_ParamT'short_2.operator_const_short__ (this + 58)
  let t'2 ← PMem.ldI16 t'1
  if (decide ((Int16.toInt32 (t'2)) < (50 : Int32))) then
    PMem.stI16 (fp + 0) (Int32.toInt16 ((50 : Int32)))
    AP_ParamTBase'short_2.set (this + 58) (fp + 0)
  else
    let t'3 ← AP_ParamT'short_2.operator_const_short__ (this + 58)
    let t'4 ← PMem.ldI16 t'3
    if (decide ((Int16.toInt32 (t'4)) > (2000 : Int32))) then
      PMem.stI16 (fp + 2) (Int32.toInt16 ((2000 : Int32)))
      AP_ParamTBase'short_2.set (this + 58) (fp + 2)
  let t'5 ← AP_ParamT'short_2.operator_const_short__ (this + 58)
  let t'6 ← PMem.ldI16 t'5
  let t'7 := ((Binary64.toBinary32 ((Binary64.ofBits 0x3ff0000000000000 /- 1 -/))) / (Int32.toBinary32 ((Int16.toInt32 (t'6)))))
  PMem.stF32 (this + 132) t'7
  let t'8 ← AP_ParamT'short_2.operator_const_short__ (this + 58)
  let t'9 ← PMem.ldI16 t'8
  let t'10 := UInt64.toUInt16 (((1000000 : UInt64) / (Int64.toUInt64 (Int16.toInt64 (t'9)))))
  PMem.stU16 (this + 64) t'10
  let t'11 ← AP_ParamT'short_2.operator_const_short__ (this + 58)
  let t'12 ← PMem.ldI16 t'11
  let t'13 := ((Binary32.ofBits 0x3f800000 /- 1 -/) / (Int32.toBinary32 ((Int16.toInt32 (t'12)))))
  PMem.stF32 (this + 68) t'13
  let t'14 ← AP_ParamT'short_2.operator_const_short__ (this + 58)
  let t'15 ← PMem.ldI16 t'14
  let t'16 := Int16.toUInt16 (t'15)
  PMem.stU16 (this + 60) t'16
  PMem.stU64 (this + 72) tasks
  PMem.stU8 (this + 80) num_tasks
  let t'17 ← AP.vehicle
  let mut vehicle : UInt64 := t'17
  if (vehicle != (0 : UInt64)) then
    AP_Vehicle.get_common_scheduler_tasks vehicle (this + 88) (this + 96)
  let t'18 ← PMem.ldU8 (this + 80)
  let t'19 ← PMem.ldU8 (this + 96)
  let t'20 := Int8.toUInt8 (Int32.toInt8 (((UInt32.toInt32 (UInt8.toUInt32 (t'18))) + (UInt32.toInt32 (UInt8.toUInt32 (t'19))))))
  PMem.stU8 (this + 97) t'20
  let t'21 ← PMem.ldU8 (this + 97)
  let t'22 ← PMem.alloc ((UInt8.toUInt64 (t'21)).toNat * 2)
  PMem.stU64 (this + 104) t'22
  let t'23 := Int16.toUInt16 (Int32.toInt16 ((0 : Int32)))
  PMem.stU16 (this + 98) t'23
  let t'24 ← AP_Scheduler.get_loop_rate_hz this
  AP.PerfInfo.set_loop_rate this t'24
  AP.PerfInfo.reset this
  let t'25 ← AP_ParamT'unsigned_char_1.operator_const_unsigned_char__ (this + 62)
  let t'26 ← PMem.ldU8 t'25
  if ((UInt32.toInt32 (UInt8.toUInt32 (t'26))) &&& (UInt32.toInt32 (UInt8.toUInt32 ((1 : UInt8))))) != (0 : Int32) then
    let t'27 ← PMem.ldU8 (this + 97)
    AP.PerfInfo.allocate_task_info this t'27
  PMem.stU32 (this + 144) log_performance_bit
  let mut old : UInt8 := Int8.toUInt8 (Int32.toInt8 ((0 : Int32)))
  let mut i : UInt8 := Int8.toUInt8 (Int32.toInt8 ((0 : Int32)))
  let mut first'28 := true
  for _ in PMem.loopFuel do
    if !first'28 then
      let t'29 := i
      let t'30 := (t'29 + 1)
      i := t'30
      pure ()
    first'28 := false
    let t'31 ← PMem.ldU8 (this + 96)
    if !((decide ((UInt32.toInt32 (UInt8.toUInt32 (i))) < (UInt32.toInt32 (UInt8.toUInt32 (t'31)))))) then break
    let t'32 ← PMem.ldU64 (this + 88)
    let t'33 ← PMem.ldU8 ((t'32 + ((UInt64.toInt64 (UInt8.toUInt64 (i))) * 32).toUInt64) + 30)
    if (decide ((UInt32.toInt32 (UInt8.toUInt32 (t'33))) < (UInt32.toInt32 (UInt8.toUInt32 (old))))) then
      break
    let t'34 ← PMem.ldU64 (this + 88)
    let t'35 ← PMem.ldU8 ((t'34 + ((UInt64.toInt64 (UInt8.toUInt64 (i))) * 32).toUInt64) + 30)
    old := t'35
  let t'36 := Int8.toUInt8 (Int32.toInt8 ((0 : Int32)))
  old := t'36
  let mut i'2 : UInt8 := Int8.toUInt8 (Int32.toInt8 ((0 : Int32)))
  let mut first'37 := true
  for _ in PMem.loopFuel do
    if !first'37 then
      let t'38 := i'2
      let t'39 := (t'38 + 1)
      i'2 := t'39
      pure ()
    first'37 := false
    let t'40 ← PMem.ldU8 (this + 80)
    if !((decide ((UInt32.toInt32 (UInt8.toUInt32 (i'2))) < (UInt32.toInt32 (UInt8.toUInt32 (t'40)))))) then break
    let t'41 ← PMem.ldU64 (this + 72)
    let t'42 ← PMem.ldU8 ((t'41 + ((UInt64.toInt64 (UInt8.toUInt64 (i'2))) * 32).toUInt64) + 30)
    if (decide ((UInt32.toInt32 (UInt8.toUInt32 (t'42))) < (UInt32.toInt32 (UInt8.toUInt32 (old))))) then
      break
    let t'43 ← PMem.ldU64 (this + 72)
    let t'44 ← PMem.ldU8 ((t'43 + ((UInt64.toInt64 (UInt8.toUInt64 (i'2))) * 32).toUInt64) + 30)
    old := t'44
  return ()

def AP_Scheduler.init (this : UInt64) (tasks : UInt64) (num_tasks : UInt8) (log_performance_bit : UInt32) : PMem.M Unit := do
  let fp ← PMem.enter 4
  let r ← AP_Scheduler.init.body fp this tasks num_tasks log_performance_bit
  PMem.leave fp
  return r

/-- C++ `AP_Scheduler::get_loop_period_s : float ()`, `<scratch space>:160-166`. -/
def AP_Scheduler.get_loop_period_s (this : UInt64) : PMem.M Binary32 := do
  let t'1 ← PMem.ldF32 (this + 68)
  let t'2 ← is_zero t'1
  if t'2 then
    let t'3 ← AP_ParamT'short_2.operator_const_short__ (this + 58)
    let t'4 ← PMem.ldI16 t'3
    let t'5 := ((Binary32.ofBits 0x3f800000 /- 1 -/) / (Int32.toBinary32 ((Int16.toInt32 (t'4)))))
    PMem.stF32 (this + 68) t'5
  let t'6 ← PMem.ldF32 (this + 68)
  return t'6

/-- C++ `AP_Scheduler::tick : void ()`, `AP_Scheduler.cpp:169-173`. -/
def AP_Scheduler.tick (this : UInt64) : PMem.M Unit := do
  let t'1 := (this + 98)
  let t'2 ← PMem.ldU16 t'1
  let t'3 := (t'2 + 1)
  PMem.stU16 t'1 t'3
  let t'4 := (this + 100)
  let t'5 ← PMem.ldU32 t'4
  let t'6 := (t'5 + 1)
  PMem.stU32 t'4 t'6
  return ()

/-- C++ `AP::PerfInfo::task_slipped : void (uint8_t)`, `AP_Common.h:59-63`. -/
def AP.PerfInfo.task_slipped (this : UInt64) (task_index : UInt8) : PMem.M Unit := do
  let mut task_index := task_index
  let t'1 ← PMem.ldU64 (this + 48)
  let mut sc'3 := (t'1 != 0)
  if sc'3 then
    let t'2 ← PMem.ldU8 (this + 45)
    sc'3 := (decide ((UInt32.toInt32 (UInt8.toUInt32 (task_index))) < (UInt32.toInt32 (UInt8.toUInt32 (t'2)))))
  if sc'3 then
    let t'4 ← PMem.ldU64 (this + 48)
    let t'5 := ((t'4 + ((UInt64.toInt64 (UInt8.toUInt64 (task_index))) * 16).toUInt64) + 14)
    let t'6 ← PMem.ldU16 t'5
    let t'7 := (t'6 + 1)
    PMem.stU16 t'5 t'7
  return ()

/-- C++ `fill_nanf_stack : void ()`, `AP_Scheduler.cpp:180-184`. -/
def fill_nanf_stack.body (fp : UInt64)  : PMem.M Unit := do
  fill_nanf (fp + 0) (UInt64.toUInt16 (((4096 : UInt64) / (4 : UInt64))))
  return ()

def fill_nanf_stack  : PMem.M Unit := do
  let fp ← PMem.enter 4096
  let r ← fill_nanf_stack.body fp 
  PMem.leave fp
  return r

/-- C++ `AP::PerfInfo::TaskInfo::update : void (uint16_t, bool)`, `PerfInfo.cpp:79-92`. -/
def AP.PerfInfo.TaskInfo.update.body (fp : UInt64) (this : UInt64) (task_time_us : UInt16) (overrun : Bool) : PMem.M Unit := do
  PMem.stU16 (fp + 0) task_time_us
  let mut overrun := overrun
  let t'1 ← MAX'unsigned_short_unsigned_short (this + 2) (fp + 0)
  let t'2 ← PMem.ldU16 t'1
  PMem.stU16 (this + 2) t'2
  let t'3 ← PMem.ldU16 this
  if ((UInt32.toInt32 (UInt16.toUInt32 (t'3))) == (0 : Int32)) then
    let t'4 ← PMem.ldU16 (fp + 0)
    PMem.stU16 this t'4
  else
    let t'5 ← MIN'unsigned_short_unsigned_short this (fp + 0)
    let t'6 ← PMem.ldU16 t'5
    PMem.stU16 this t'6
  let t'7 := (this + 4)
  let t'8 ← PMem.ldU32 t'7
  let t'9 ← PMem.ldU16 (fp + 0)
  let t'10 := (t'8 + (UInt16.toUInt32 (t'9)))
  PMem.stU32 t'7 t'10
  let t'11 := (this + 8)
  let t'12 ← PMem.ldU32 t'11
  let t'13 := (t'12 + 1)
  PMem.stU32 t'11 t'13
  if overrun then
    let t'14 := (this + 14)
    let t'15 ← PMem.ldU16 t'14
    let t'16 := (t'15 + 1)
    PMem.stU16 t'14 t'16
  return ()

def AP.PerfInfo.TaskInfo.update (this : UInt64) (task_time_us : UInt16) (overrun : Bool) : PMem.M Unit := do
  let fp ← PMem.enter 2
  let r ← AP.PerfInfo.TaskInfo.update.body fp this task_time_us overrun
  PMem.leave fp
  return r

/-- C++ `AP::PerfInfo::update_task_info : void (uint8_t, uint16_t, bool)`, `PerfInfo.cpp:65-77`. -/
def AP.PerfInfo.update_task_info (this : UInt64) (task_index : UInt8) (task_time_us : UInt16) (overrun : Bool) : PMem.M Unit := do
  let mut task_index := task_index
  let mut task_time_us := task_time_us
  let mut overrun := overrun
  let t'1 ← PMem.ldU64 (this + 48)
  if (t'1 == (0 : UInt64)) then
    return ()
  let t'2 ← PMem.ldU8 (this + 45)
  if (decide ((UInt32.toInt32 (UInt8.toUInt32 (task_index))) ≥ (UInt32.toInt32 (UInt8.toUInt32 (t'2))))) then
    return ()
  let t'3 ← PMem.ldU64 (this + 48)
  let ti : UInt64 := (t'3 + ((UInt64.toInt64 (UInt8.toUInt64 (task_index))) * 16).toUInt64)
  AP.PerfInfo.TaskInfo.update ti task_time_us overrun
  return ()

/-- C++ `AP_Scheduler::get_last_loop_time_s : float () const`, `<scratch space>:179-181`. -/
def AP_Scheduler.get_last_loop_time_s (this : UInt64) : PMem.M Binary32 := do
  let t'1 ← PMem.ldF32 (this + 132)
  return t'1

/-- C++ `AP::PerfInfo::check_loop_time : void (uint32_t)`, `PerfInfo.cpp:113-159`. -/
def AP.PerfInfo.check_loop_time (this : UInt64) (time_in_micros : UInt32) : PMem.M Unit := do
  let mut time_in_micros := time_in_micros
  let t'1 := (this + 4)
  let t'2 ← PMem.ldU16 t'1
  let t'3 := (t'2 + 1)
  PMem.stU16 t'1 t'3
  let t'4 ← PMem.ldB (this + 44)
  if t'4 then
    PMem.stB (this + 44) false
    return ()
  let t'5 ← PMem.ldU32 (this + 8)
  if (decide (time_in_micros > t'5)) then
    PMem.stU32 (this + 8) time_in_micros
  let t'6 ← PMem.ldU32 (this + 12)
  let mut sc'8 := (t'6 == (Int32.toUInt32 ((0 : Int32))))
  if !sc'8 then
    let t'7 ← PMem.ldU32 (this + 12)
    sc'8 := (decide (time_in_micros < t'7))
  if sc'8 then
    PMem.stU32 (this + 12) time_in_micros
  let t'9 ← PMem.ldU16 (this + 2)
  if (decide (time_in_micros > (UInt16.toUInt32 (t'9)))) then
    let t'10 := (this + 32)
    let t'11 ← PMem.ldU16 t'10
    let t'12 := (t'11 + 1)
    PMem.stU16 t'10 t'12
  let t'13 := (this + 16)
  let t'14 ← PMem.ldU64 t'13
  let t'15 := (t'14 + (UInt32.toUInt64 (time_in_micros)))
  PMem.stU64 t'13 t'15
  let t'16 := (this + 24)
  let t'17 ← PMem.ldU64 t'16
  let t'18 := (t'17 + (UInt32.toUInt64 ((time_in_micros * time_in_micros))))
  PMem.stU64 t'16 t'18
  let mut now : UInt32 := (← PMem.clock).toUInt32
  let t'19 ← PMem.ldU32 (this + 36)
  let mut loop_time_us : UInt32 := (now - t'19)
  PMem.stU32 (this + 36) now
  let t'20 ← PMem.ldU16 (this + 2)
  if (decide ((UInt32.toUInt64 (loop_time_us)) < ((UInt16.toUInt64 (t'20)) + (10000 : UInt64)))) then
    let t'21 ← PMem.ldF32 (this + 40)
    let t'22 := (((Binary32.ofBits 0x3f7d70a4 /- 990000009/1000000000 -/) * t'21) + (((Binary32.ofBits 0x3c23d70a /- 999999977/100000000000 -/) * (UInt32.toBinary32 (loop_time_us))) * (Binary32.ofBits 0x358637bd /- 999999997/1000000000000000 -/)))
    PMem.stF32 (this + 40) t'22
  else
    pure ()
  return ()

/-- C++ `AP_Scheduler::ticks : uint16_t () const`, `functor.h:124-?`. -/
def AP_Scheduler.ticks (this : UInt64) : PMem.M UInt16 := do
  let t'1 ← PMem.ldU16 (this + 98)
  return t'1

/-- `AP.PerfInfo.PerfInfo` as a pure function of its arguments (it reads and writes no memory). -/
def AP.PerfInfo.PerfInfo.pure' (this : UInt64) : Id Unit := do
  return ()

/-- C++ `AP::PerfInfo::PerfInfo : void ()`, `PerfInfo.h:14-?`. -/
def AP.PerfInfo.PerfInfo (this : UInt64) : PMem.M Unit :=
  pure (_root_.Vehicle_lib.AP.PerfInfo.PerfInfo.pure' this)

/-- C++ `AP_Scheduler::AP_Scheduler : void ()`, `AP_Scheduler.cpp:81-92`. -/
def AP_Scheduler.AP_Scheduler (this : UInt64) : PMem.M Unit := do
  AP.PerfInfo.PerfInfo (this + 0)
  AP_Param.AP_Param'2 (this + 56)
  AP_Param.AP_Param'2 (this + 58)
  AP_Param.AP_Param'2 (this + 62)
  HALSITL.Semaphore.Semaphore (this + 160)
  let t'1 ← PMem.ldU64 (0xccb8 : UInt64) /- &AP_Scheduler::_singleton -/
  if (t'1 != 0) then
    return ()
  PMem.stU64 (0xccb8 : UInt64) /- &AP_Scheduler::_singleton -/ this
  AP_Param.setup_object_defaults this (0x44a0 : UInt64) /- &AP_Scheduler::var_info -/
  return ()

end Vehicle_lib
