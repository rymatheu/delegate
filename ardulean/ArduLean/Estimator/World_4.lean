import ArduLean.Runtime.CFloat
import ArduLean.Estimator.libraries.AP_Math.AP_Math
import ArduLean.Estimator.World
import ArduLean.Estimator.libraries.AP_Compass.AP_Compass
import ArduLean.Estimator.libraries.AP_InertialSensor.AP_InertialSensor
import ArduLean.Estimator.World_2
import ArduLean.Estimator.libraries.AP_Baro.AP_Baro_2
import ArduLean.Estimator.World_3
import ArduLean.Estimator.libraries.AP_Compass.AP_Compass_3
import ArduLean.Estimator.libraries.AP_InertialSensor.AP_InertialSensor_2
import ArduLean.Estimator.libraries.AP_Baro.AP_Baro_3

/-!
`World`: generated items without a C++ function of their own.

Items of `lean/Estimator_lib.lean` (the estimator translation), unchanged; placed by `tools/split_modules.py` (`ArduLean/Estimator/INDEX.md`).
-/

open FloatLib.Floats (Binary32 Binary64)

set_option maxRecDepth 200000
-- AP_DAL's `const log_RISH old_RISH = _RISH;` read only by WRITE_REPLAY_BLOCK_IFCHANGED, which is `(void)old`
-- without logging (HAL_LOGGING_ENABLED 0): an unused binding, as in the C++
set_option linter.unusedVariables false

namespace Estimator_lib

/-- C++ `_timer` through a pointer of type `AP_Baro_SITL *` (--world-pointers): the final overrider of the object it
points to, called on that object; a null pointer (undefined behavior in C++) changes nothing. -/
def WPtr.call'AP_Baro_SITL'_timer (ptr : WPtr) (w : World) : World :=
  match ptr with
  | .heap'AP_Baro_SITL i =>
    let s' := AP_Baro_SITL._timer (w.heap'AP_Baro_SITL[i]!) w
    { w with heap'AP_Baro_SITL := w.heap'AP_Baro_SITL.set! i s' }
  | _ => w

/-- C++ `_timer` through a pointer of type `AP_Compass_SITL *` (--world-pointers): the final overrider of the object it
points to, called on that object; a null pointer (undefined behavior in C++) changes nothing. -/
def WPtr.call'AP_Compass_SITL'_timer (ptr : WPtr) (w : World) : World :=
  match ptr with
  | .heap'AP_Compass_SITL i =>
    let (s', w') := AP_Compass_SITL._timer (w.heap'AP_Compass_SITL[i]!) w w.heap'AP_Compass_SITL'inp
    { w' with heap'AP_Compass_SITL := w'.heap'AP_Compass_SITL.set! i s' }
  | _ => w

/-- C++ `timer_update` through a pointer of type `AP_InertialSensor_SITL *` (--world-pointers): the final overrider of the object it
points to, called on that object; a null pointer (undefined behavior in C++) changes nothing. -/
def WPtr.call'AP_InertialSensor_SITL'timer_update (ptr : WPtr) (w : World) : World :=
  match ptr with
  | .heap'AP_InertialSensor_SITL i =>
    let (s', w') := AP_InertialSensor_SITL.timer_update (w.heap'AP_InertialSensor_SITL[i]!) w w.heap'AP_InertialSensor_SITL'inp (.heap'AP_InertialSensor_SITL i)
    { w' with heap'AP_InertialSensor_SITL := w'.heap'AP_InertialSensor_SITL.set! i s' }
  | _ => w

/-- C++ `f()` of a `Functor<void>` (--world-pointers): the member function it binds, called on the object
it is bound to; an empty functor (a null call in C++) changes nothing. -/
def WFun.call (f : WFun) (w : World) : World :=
  match f with
  | .AP_Baro_SITL__timer p => WPtr.call'AP_Baro_SITL'_timer p w
  | .AP_Compass_SITL__timer p => WPtr.call'AP_Compass_SITL'_timer p w
  | .AP_InertialSensor_SITL_timer_update p => WPtr.call'AP_InertialSensor_SITL'timer_update p w
  | _ => w

namespace EstScheduler

/-- C++ `void EstScheduler::step()`, `reference/hal/est_scheduler.cpp:96-172`. -/
def step (s : State) (w : World) (o : Outputs) : State × World × Outputs := Id.run do
  let mut s := s
  let mut w := w
  let mut o := o
  if UInt32.toInt32 (UInt16.toUInt32 s._count) == (0 : Int32) then
    s := { s with _exhausted := true }
    o := o.push (Output.est_mark (Int8.toUInt8 (Int32.toInt8 (3 : Int32))) s._lines)
    s := { s with _in := s._synth }
    s := { s with _in.t_us := s._clock_us + s._step_period }
    s := { s with _in.gps := false }
    s := { s with _clock_us := s._in.t_us }
    s := { s with _events := Int8.toUInt8 (Int32.toInt8 (0 : Int32)) }
    if s._in_timer_proc then
      return (s, w, o)
    s := { s with _in_timer_proc := true }
    let t'1 : UInt8 := Int8.toUInt8 (Int32.toInt8 (0 : Int32))
    let t'2 : Int32 := UInt32.toInt32 (UInt8.toUInt32 s._num_timer)
    for i' in [0:(t'2.toInt - (Int.ofNat t'1.toNat)).toNat] do  -- C++ loop bounded by a runtime value (--runtime-loops)
      let i : UInt8 := t'1 + Nat.toUInt8 i'
      if (s._timer_proc[UInt8.toNat i]! != WFun.null) then
        w := { w with est_scheduler := s }  -- this object's state into the World: the call reaches it
        w := WFun.call s._timer_proc[UInt8.toNat i]! w
        s := w.est_scheduler  -- this object's state as the call left it
    s := { s with _in_timer_proc := false }
    return (s, w, o)
  s := { s with _in := s._recs[UInt16.toNat s._head]! }
  if s._lines > Int32.toUInt32 (0 : Int32) then
    s := { s with _step_period := s._in.t_us - s._clock_us }
  s := { s with _head := Int16.toUInt16 (Int32.toInt16 ((UInt32.toInt32 (UInt16.toUInt32 s._head) + (1 : Int32)) % UInt32.toInt32 (UInt16.toUInt32 Estimator_lib.EST_MAX_RECORDS))) }
  s := { s with _count := s._count - (1 : UInt16) }
  s := { s with _lines := s._lines + (1 : UInt32) }
  s := { s with _events := Int8.toUInt8 (Int32.toInt8 (0 : Int32)) }
  s := { s with _clock_us := s._in.t_us }
  o := o.push (Output.est_mark (Int8.toUInt8 (Int32.toInt8 (0 : Int32))) s._lines)
  s := { s with _synth.imu_n := s._synth.imu_n.set! 0 (s._in.imu_n[0]!) }
  s := { s with _synth.imu_n := s._synth.imu_n.set! 1 (s._in.imu_n[1]!) }
  for j' in [0:16] do
    let j : UInt8 := Nat.toUInt8 j'
    s := { s with _synth.accel := s._synth.accel.set! (UInt8.toNat j) (s._in.accel[UInt8.toNat j]!) }
    s := { s with _synth.gyro := s._synth.gyro.set! (UInt8.toNat j) (s._in.gyro[UInt8.toNat j]!) }
  if s._in.baro then
    s := { s with _synth.baro := true }
    s := { s with _synth.baro_pa := s._in.baro_pa }
    s := { s with _synth.baro_degc := s._in.baro_degc }
  if s._in.mag then
    s := { s with _synth.mag := true }
    s := { s with _synth.mag_mgauss := s._in.mag_mgauss }
  if s._in.gps then
    s := { s with _gps := s._in }
    s := { s with _gps_pending := true }
  if s._in_timer_proc then
    o := o.push (Output.est_mark (Int8.toUInt8 (Int32.toInt8 (1 : Int32))) s._lines)
    return (s, w, o)
  s := { s with _in_timer_proc := true }
  let t'3 : UInt8 := Int8.toUInt8 (Int32.toInt8 (0 : Int32))
  let t'4 : Int32 := UInt32.toInt32 (UInt8.toUInt32 s._num_timer)
  for i'2' in [0:(t'4.toInt - (Int.ofNat t'3.toNat)).toNat] do  -- C++ loop bounded by a runtime value (--runtime-loops)
    let i'2 : UInt8 := t'3 + Nat.toUInt8 i'2'
    if (s._timer_proc[UInt8.toNat i'2]! != WFun.null) then
      w := { w with est_scheduler := s }  -- this object's state into the World: the call reaches it
      w := WFun.call s._timer_proc[UInt8.toNat i'2]! w
      s := w.est_scheduler  -- this object's state as the call left it
  s := { s with _in_timer_proc := false }
  o := o.push (Output.est_mark (Int8.toUInt8 (Int32.toInt8 (1 : Int32))) s._lines)
  return (s, w, o)

/-- C++ `void EstScheduler::delay_microseconds(uint16_t usec)`, `reference/hal/est_scheduler.cpp:174-187`. -/
def delay_microseconds (s : State) (w : World) (o : Outputs) (usec : UInt16) : State × World × Outputs := Id.run do
  let mut s := s
  let mut w := w
  let mut o := o
  let start : UInt64 := s._clock_us
  for _ in [0:2^64] do  -- C loop without a constant trip count (--general-loops)
    if !(decide (s._clock_us - start < UInt16.toUInt64 usec)) then break
    let (t'1, t'2, t'3) := step s w o
    w := t'2
    s := t'1
    o := t'3
  return (s, w, o)

/-- C++ `void AP_HAL::Scheduler::delay_microseconds_boost(uint16_t us)`, `AP_HAL/Scheduler.h:30` (a member of `AP_HAL::Scheduler`, translated for `EstScheduler`). -/
def delay_microseconds_boost (s : State) (w : World) (o : Outputs) (us : UInt16) : State × World × Outputs := Id.run do
  let mut s := s
  let mut w := w
  let mut o := o
  let (t'1, t'2, t'3) := delay_microseconds s w o us
  w := t'2
  s := t'1
  o := t'3
  return (s, w, o)

end EstScheduler

namespace EstScheduler

/-- C++ `void EstScheduler::delay(uint16_t ms)`, `reference/hal/est_scheduler.cpp:189-204`. -/
def delay (s : State) (w : World) (o : Outputs) (ms : UInt16) : State × World × Outputs := Id.run do
  let mut s := s
  let mut w := w
  let mut o := o
  let start : UInt32 := UInt64.toUInt32 (s._clock_us / Int64.toUInt64 (Int32.toInt64 (1000 : Int32)))
  let mut now : UInt32 := start
  for _ in [0:2^64] do  -- C loop without a constant trip count (--general-loops)
    let (t'1, t'2, t'3) := delay_microseconds s w o (Int16.toUInt16 (Int32.toInt16 (1000 : Int32)))
    w := t'2
    s := t'1
    o := t'3
    o := o.push (Output.est_mark (Int8.toUInt8 (Int32.toInt8 (2 : Int32))) (UInt16.toUInt32 ms - (now - start)))
    now := UInt64.toUInt32 (s._clock_us / Int64.toUInt64 (Int32.toInt64 (1000 : Int32)))
    if !(decide (now - start < UInt16.toUInt32 ms)) then break
  return (s, w, o)

end EstScheduler

end Estimator_lib
