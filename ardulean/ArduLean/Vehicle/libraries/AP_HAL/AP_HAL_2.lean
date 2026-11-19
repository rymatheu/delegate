import ArduLean.Runtime.Memory
import ArduLean.Vehicle.libraries.AP_HAL.AP_HAL
import ArduLean.Vehicle.ArduCopter.ArduCopter
import ArduLean.Vehicle.Dispatch
import ArduLean.Vehicle.libraries.AP_Common.AP_Common

/-!
ArduPilot `libraries/AP_HAL`, part 2 of 2. Sources: `libraries/AP_HAL/Util.cpp`, `libraries/AP_HAL/utility/functor.h`.

Items of `lean/Vehicle_lib.lean` (the vehicle translation), unchanged; placed by `tools/split_modules.py` (`ArduLean/Vehicle/INDEX.md`).
-/

open FloatLib.Floats (Binary32 Binary64)

set_option linter.unusedVariables false
set_option linter.unreachableTactic false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false

namespace Vehicle_lib

/-- C++ `BufferPrinter::BufferPrinter : void (char *, size_t)`, `Util.cpp:18-19`. -/
def BufferPrinter.BufferPrinter (this : UInt64) (str : UInt64) (size : UInt64) : PMem.M Unit := do
  let mut str := str
  let mut size := size
  AP_HAL.BetterStream.BetterStream this
  PMem.stU64 (this + 8) (Int64.toUInt64 (Int32.toInt64 ((0 : Int32))))
  PMem.stU64 (this + 16) str
  PMem.stU64 (this + 24) size
  return ()

/-- C++ `AP_HAL::Util::vsnprintf : int (char *, size_t, const char *, va_list)`, `Util.cpp:55-71`. -/
def AP_HAL.Util.vsnprintf.body (fp : UInt64) (this : UInt64) (str : UInt64) (size : UInt64) (format : UInt64) (ap : UInt64) : PMem.M Int32 := do
  let mut str := str
  let mut size := size
  let mut format := format
  let mut ap := ap
  let mut c'1 : UInt64 := default
  if size != (0 : UInt64) then
    c'1 := (size - (Int64.toUInt64 (Int32.toInt64 ((1 : Int32)))))
  else
    c'1 := Int64.toUInt64 (Int32.toInt64 ((0 : Int32)))
  BufferPrinter.BufferPrinter (fp + 0) str c'1
  print_vprintf (fp + 0) format ap
  let t'2 ← PMem.ldU64 ((fp + 0) + 8)
  let mut ret : UInt64 := t'2
  if (decide (ret < size)) then
    PMem.stI8 (str + ((UInt64.toInt64 (ret)) * 1).toUInt64) (0 : Int8)
  else
    if (decide (size > (Int64.toUInt64 (Int32.toInt64 ((0 : Int32)))))) then
      let t'3 := Int32.toInt8 ((0 : Int32))
      PMem.stI8 (str + ((UInt64.toInt64 ((size - (Int64.toUInt64 (Int32.toInt64 ((1 : Int32))))))) * 1).toUInt64) t'3
  return UInt32.toInt32 (UInt64.toUInt32 (ret))

def AP_HAL.Util.vsnprintf (this : UInt64) (str : UInt64) (size : UInt64) (format : UInt64) (ap : UInt64) : PMem.M Int32 := do
  let fp ← PMem.enter 32
  let r ← AP_HAL.Util.vsnprintf.body fp this str size format ap
  PMem.leave fp
  return r

/-- C++ `AP_HAL::Util::snprintf : int (char *, size_t, const char *, ...)`, `Util.cpp:46-53`. -/
def AP_HAL.Util.snprintf.body (fp : UInt64) (this : UInt64) (str : UInt64) (size : UInt64) (format : UInt64) (va' : UInt64) : PMem.M Int32 := do
  let mut str := str
  let mut size := size
  PMem.stU64 (fp + 0) format
  PMem.stU64 (fp + 8) va'
  let t'1 ← PMem.ldU64 (fp + 0)
  let t'2 ← PMem.ldU64 (fp + 8)
  let t'3 ← AP_HAL.Util.vsnprintf (0 : UInt64) str size t'1 t'2
  let mut res : Int32 := t'3
  return res

def AP_HAL.Util.snprintf (this : UInt64) (str : UInt64) (size : UInt64) (format : UInt64) (va' : UInt64) : PMem.M Int32 := do
  let fp ← PMem.enter 16
  let r ← AP_HAL.Util.snprintf.body fp this str size format va'
  PMem.leave fp
  return r

/-- C++ `Functor<void, float *, unsigned char>::operator() : void (float *, unsigned char) const`, `functor.h:52-55`. -/
def Functor'void_float_unsigned_char.operator__ (this : UInt64) (args : UInt64) (args'2 : UInt8) : PMem.M Unit := do
  let mut args := args
  let mut args'2 := args'2
  let t'1 ← PMem.ldU64 (this + 8)
  let t'2 ← PMem.ldU64 this
  fnptr'1 t'1 t'2 args args'2
  return ()

/-- C++ `Functor<void>::method_wrapper : void (void *)`, `functor.h:85-89`. -/
def Functor'void.method_wrapper'Copter_check_ekf_reset (obj : UInt64) : PMem.M Unit := do
  let mut obj := obj
  let mut t : UInt64 := obj
  Copter.check_ekf_reset t
  return ()

/-- C++ `Functor<void>::method_wrapper : void (void *)`, `functor.h:85-89`. -/
def Functor'void.method_wrapper'Copter_standby_update (obj : UInt64) : PMem.M Unit := do
  let mut obj := obj
  let mut t : UInt64 := obj
  Copter.standby_update t
  return ()

end Vehicle_lib
