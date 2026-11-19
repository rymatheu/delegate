import ArduLean.Runtime.Bridge
import ArduLean.Vehicle.libraries.AP_Math.AP_Math

/-!
ArduPilot `libraries/AP_HAL`, part 1 of 2. Sources: `libraries/AP_HAL/utility/print_vprintf.cpp`, `libraries/AP_HAL/utility/RingBuffer.cpp`, `libraries/AP_HAL/utility/ftoa_engine.cpp`, `libraries/AP_HAL/utility/utoa_invert.cpp`, `libraries/AP_HAL/utility/functor.h`, `libraries/AP_HAL/Storage.cpp`, `libraries/AP_HAL/Semaphores.h`, `libraries/AP_HAL/Util.cpp` and 1 more.

Items of `lean/Vehicle_lib.lean` (the vehicle translation), unchanged; placed by `tools/split_modules.py` (`ArduLean/Vehicle/INDEX.md`).
-/

open FloatLib.Floats (Binary32 Binary64)

set_option linter.unusedVariables false
set_option linter.unreachableTactic false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false

namespace Vehicle_lib

/-- C++ `AP_HAL::Storage::erase : bool ()`, `Storage.cpp:8-17`. -/
def AP_HAL.Storage.erase.body (fp : UInt64) (this : UInt64) : PMem.M Bool := do
  let mut ofs : UInt32 := default  -- uninitialized in C
  let t'1 := Int32.toUInt32 ((0 : Int32))
  ofs := t'1
  let mut first'2 := true
  for _ in PMem.loopFuel do
    if !first'2 then
      let t'3 := (ofs + (UInt64.toUInt32 ((16 : UInt64))))
      ofs := t'3
      pure ()
    first'2 := false
    if !((decide (ofs < (Int32.toUInt32 ((16384 : Int32)))))) then break
    PMem.stU64 (fp + 16) (16 : UInt64)
    PMem.stU32 (fp + 24) ((Int32.toUInt32 ((16384 : Int32))) - ofs)
    let t'4 ← MIN'unsigned_long_unsigned_int (fp + 16) (fp + 24)
    let mut n : UInt32 := UInt64.toUInt32 (t'4)
    PMem.halWrite (UInt32.toUInt16 (ofs)) (fp + 0) (UInt32.toUInt64 (n))
  return true

def AP_HAL.Storage.erase (this : UInt64) : PMem.M Bool := do
  let fp ← PMem.enter 28
  let r ← AP_HAL.Storage.erase.body fp this
  PMem.leave fp
  return r

/-- `ByteBuffer.IoVec.IoVec` as a pure function of its arguments (it reads and writes no memory). -/
def ByteBuffer.IoVec.IoVec.pure' (this : UInt64) : Id Unit := do
  return ()

/-- C++ `ByteBuffer::IoVec::IoVec : void () noexcept`, `AP_Common.h:76-?`. -/
def ByteBuffer.IoVec.IoVec (this : UInt64) : PMem.M Unit :=
  pure (_root_.Vehicle_lib.ByteBuffer.IoVec.IoVec.pure' this)

/-- C++ `ByteBuffer::available : uint32_t () const`, `RingBuffer.cpp:58-68`. -/
def ByteBuffer.available (this : UInt64) : PMem.M UInt32 := do
  let t'1 ← PMem.ldU32 (this + 16)
  let mut _tail : UInt32 := t'1
  let t'2 ← PMem.ldU32 (this + 12)
  if (decide (t'2 > _tail)) then
    let t'3 ← PMem.ldU32 (this + 8)
    let t'4 ← PMem.ldU32 (this + 12)
    return ((t'3 - t'4) + _tail)
  let t'5 ← PMem.ldU32 (this + 12)
  return (_tail - t'5)

/-- C++ `ByteBuffer::readptr : const uint8_t *(uint32_t &)`, `RingBuffer.cpp:266-272`. -/
def ByteBuffer.readptr (this : UInt64) (available_bytes : UInt64) : PMem.M UInt64 := do
  let t'1 ← PMem.ldU32 (this + 16)
  let mut _tail : UInt32 := t'1
  let t'2 ← PMem.ldU32 (this + 12)
  let mut c'3 : UInt32 := default
  if (decide (t'2 > _tail)) then
    let t'4 ← PMem.ldU32 (this + 8)
    let t'5 ← PMem.ldU32 (this + 12)
    c'3 := (t'4 - t'5)
  else
    let t'6 ← PMem.ldU32 (this + 12)
    c'3 := (_tail - t'6)
  PMem.stU32 available_bytes c'3
  let t'7 ← PMem.ldU32 available_bytes
  let mut c'8 : UInt64 := default
  if t'7 != (0 : UInt32) then
    let t'9 ← PMem.ldU64 this
    let t'10 ← PMem.ldU32 (this + 12)
    c'8 := (t'9 + ((UInt64.toInt64 (UInt32.toUInt64 (t'10))) * 1).toUInt64)
  else
    c'8 := (0 : UInt64)
  return c'8

/-- C++ `ByteBuffer::peekiovec : uint8_t (ByteBuffer::IoVec *, uint32_t)`, `RingBuffer.cpp:146-180`. -/
def ByteBuffer.peekiovec.body (fp : UInt64) (this : UInt64) (iovec : UInt64) (len : UInt32) : PMem.M UInt8 := do
  let mut iovec := iovec
  let mut len := len
  let t'1 ← ByteBuffer.available this
  PMem.stU32 (fp + 0) t'1
  let t'2 ← PMem.ldU32 (fp + 0)
  if (decide (len > t'2)) then
    let t'3 ← PMem.ldU32 (fp + 0)
    len := t'3
  if (len == (Int32.toUInt32 ((0 : Int32)))) then
    return Int8.toUInt8 (Int32.toInt8 ((0 : Int32)))
  let t'4 ← ByteBuffer.readptr this (fp + 0)
  let mut b : UInt64 := t'4
  let t'5 ← PMem.ldU32 (fp + 0)
  if (t'5 == (Int32.toUInt32 ((0 : Int32)))) then
    let t'6 ← PMem.ldU64 this
    PMem.stU64 (iovec + ((Int32.toInt64 ((0 : Int32))) * 16).toUInt64) t'6
    PMem.stU32 ((iovec + ((Int32.toInt64 ((0 : Int32))) * 16).toUInt64) + 8) len
    PMem.stU64 (iovec + ((Int32.toInt64 ((1 : Int32))) * 16).toUInt64) (0 : UInt64)
    let t'7 := Int32.toUInt32 ((0 : Int32))
    PMem.stU32 ((iovec + ((Int32.toInt64 ((1 : Int32))) * 16).toUInt64) + 8) t'7
    return Int8.toUInt8 (Int32.toInt8 ((1 : Int32)))
  let t'8 ← PMem.ldU32 (fp + 0)
  if (decide (t'8 > len)) then
    PMem.stU32 (fp + 0) len
  PMem.stU64 (iovec + ((Int32.toInt64 ((0 : Int32))) * 16).toUInt64) b
  let t'9 ← PMem.ldU32 (fp + 0)
  PMem.stU32 ((iovec + ((Int32.toInt64 ((0 : Int32))) * 16).toUInt64) + 8) t'9
  let t'10 ← PMem.ldU32 (fp + 0)
  if (decide (len ≤ t'10)) then
    return Int8.toUInt8 (Int32.toInt8 ((1 : Int32)))
  let t'11 ← PMem.ldU64 this
  PMem.stU64 (iovec + ((Int32.toInt64 ((1 : Int32))) * 16).toUInt64) t'11
  let t'12 ← PMem.ldU32 (fp + 0)
  let t'13 := (len - t'12)
  PMem.stU32 ((iovec + ((Int32.toInt64 ((1 : Int32))) * 16).toUInt64) + 8) t'13
  return Int8.toUInt8 (Int32.toInt8 ((2 : Int32)))

def ByteBuffer.peekiovec (this : UInt64) (iovec : UInt64) (len : UInt32) : PMem.M UInt8 := do
  let fp ← PMem.enter 4
  let r ← ByteBuffer.peekiovec.body fp this iovec len
  PMem.leave fp
  return r

/-- C++ `ByteBuffer::peekbytes : uint32_t (uint8_t *, uint32_t)`, `RingBuffer.cpp:185-197`. -/
def ByteBuffer.peekbytes.body (fp : UInt64) (this : UInt64) (data : UInt64) (len : UInt32) : PMem.M UInt32 := do
  let mut data := data
  let mut len := len
  ByteBuffer.IoVec.IoVec ((fp + 0) + 0)
  ByteBuffer.IoVec.IoVec ((fp + 0) + 16)
  let t'1 ← ByteBuffer.peekiovec this (fp + 0) len
  let mut n_vec : UInt8 := t'1
  let mut ret : UInt32 := Int32.toUInt32 ((0 : Int32))
  for i'2 in [0:n_vec.toNat] do
    let i : Int32 := Int32.ofNat i'2
    let t'3 ← PMem.ldU64 ((fp + 0) + ((Int32.toInt64 (i)) * 16).toUInt64)
    let t'4 ← PMem.ldU32 (((fp + 0) + ((Int32.toInt64 (i)) * 16).toUInt64) + 8)
    let t'5 ← PMem.memcpy (data + ((UInt64.toInt64 (UInt32.toUInt64 (ret))) * 1).toUInt64) t'3 (UInt32.toUInt64 (t'4))
    discard <| pure (t'5)
    let t'6 ← PMem.ldU32 (((fp + 0) + ((Int32.toInt64 (i)) * 16).toUInt64) + 8)
    let t'7 := (ret + t'6)
    ret := t'7
  return ret

def ByteBuffer.peekbytes (this : UInt64) (data : UInt64) (len : UInt32) : PMem.M UInt32 := do
  let fp ← PMem.enter 32
  let r ← ByteBuffer.peekbytes.body fp this data len
  PMem.leave fp
  return r

/-- C++ `ByteBuffer::space : uint32_t () const`, `RingBuffer.cpp:75-93`. -/
def ByteBuffer.space (this : UInt64) : PMem.M UInt32 := do
  let t'1 ← PMem.ldU32 (this + 8)
  if (t'1 == (Int32.toUInt32 ((0 : Int32)))) then
    return Int32.toUInt32 ((0 : Int32))
  let t'2 ← PMem.ldU32 (this + 12)
  let mut _head : UInt32 := t'2
  let mut ret : UInt32 := Int32.toUInt32 ((0 : Int32))
  let t'3 ← PMem.ldU32 (this + 16)
  if (decide (_head ≤ t'3)) then
    let t'4 ← PMem.ldU32 (this + 8)
    ret := t'4
  let t'5 ← PMem.ldU32 (this + 16)
  let t'6 := (ret + ((_head - t'5) - (Int32.toUInt32 ((1 : Int32)))))
  ret := t'6
  return ret

/-- C++ `ByteBuffer::reserve : uint8_t (ByteBuffer::IoVec *, uint32_t)`, `RingBuffer.cpp:199-225`. -/
def ByteBuffer.reserve (this : UInt64) (iovec : UInt64) (len : UInt32) : PMem.M UInt8 := do
  let mut iovec := iovec
  let mut len := len
  let t'1 ← ByteBuffer.space this
  let mut n : UInt32 := t'1
  if (decide (len > n)) then
    len := n
  if !(len != (0 : UInt32)) then
    return Int8.toUInt8 (Int32.toInt8 ((0 : Int32)))
  let t'2 ← PMem.ldU64 this
  let t'3 ← PMem.ldU32 (this + 16)
  let t'4 := (t'2 + ((UInt64.toInt64 (UInt32.toUInt64 (t'3))) * 1).toUInt64)
  PMem.stU64 (iovec + ((Int32.toInt64 ((0 : Int32))) * 16).toUInt64) t'4
  let t'5 ← PMem.ldU32 (this + 8)
  let t'6 ← PMem.ldU32 (this + 16)
  let t'7 := (t'5 - t'6)
  n := t'7
  if (decide (len ≤ n)) then
    PMem.stU32 ((iovec + ((Int32.toInt64 ((0 : Int32))) * 16).toUInt64) + 8) len
    return Int8.toUInt8 (Int32.toInt8 ((1 : Int32)))
  PMem.stU32 ((iovec + ((Int32.toInt64 ((0 : Int32))) * 16).toUInt64) + 8) n
  let t'8 ← PMem.ldU64 this
  PMem.stU64 (iovec + ((Int32.toInt64 ((1 : Int32))) * 16).toUInt64) t'8
  let t'9 := (len - n)
  PMem.stU32 ((iovec + ((Int32.toInt64 ((1 : Int32))) * 16).toUInt64) + 8) t'9
  return Int8.toUInt8 (Int32.toInt8 ((2 : Int32)))

/-- C++ `ByteBuffer::commit : bool (uint32_t)`, `RingBuffer.cpp:230-238`. -/
def ByteBuffer.commit (this : UInt64) (len : UInt32) : PMem.M Bool := do
  let mut len := len
  let t'1 ← ByteBuffer.space this
  if (decide (len > t'1)) then
    return false
  let t'2 ← PMem.ldU32 (this + 16)
  let t'3 ← PMem.ldU32 (this + 8)
  let t'4 ← PMem.atomicStU32 (this + 16) ((t'2 + len) % t'3)
  discard <| pure (t'4)
  return true

/-- C++ `ByteBuffer::write : uint32_t (const uint8_t *, uint32_t)`, `RingBuffer.cpp:100-113`. -/
def ByteBuffer.write.body (fp : UInt64) (this : UInt64) (data : UInt64) (len : UInt32) : PMem.M UInt32 := do
  let mut data := data
  let mut len := len
  ByteBuffer.IoVec.IoVec ((fp + 0) + 0)
  ByteBuffer.IoVec.IoVec ((fp + 0) + 16)
  let t'1 ← ByteBuffer.reserve this (fp + 0) len
  let mut n_vec : UInt8 := t'1
  let mut ret : UInt32 := Int32.toUInt32 ((0 : Int32))
  for i'2 in [0:n_vec.toNat] do
    let i : Int32 := Int32.ofNat i'2
    let t'3 ← PMem.ldU64 ((fp + 0) + ((Int32.toInt64 (i)) * 16).toUInt64)
    let t'4 ← PMem.ldU32 (((fp + 0) + ((Int32.toInt64 (i)) * 16).toUInt64) + 8)
    let t'5 ← PMem.memcpy t'3 (data + ((UInt64.toInt64 (UInt32.toUInt64 (ret))) * 1).toUInt64) (UInt32.toUInt64 (t'4))
    discard <| pure (t'5)
    let t'6 ← PMem.ldU32 (((fp + 0) + ((Int32.toInt64 (i)) * 16).toUInt64) + 8)
    let t'7 := (ret + t'6)
    ret := t'7
  let t'8 ← ByteBuffer.commit this ret
  discard <| pure (t'8)
  return ret

def ByteBuffer.write (this : UInt64) (data : UInt64) (len : UInt32) : PMem.M UInt32 := do
  let fp ← PMem.enter 32
  let r ← ByteBuffer.write.body fp this data len
  PMem.leave fp
  return r

/-- `AP_HAL.Semaphore.Semaphore` as a pure function of its arguments (it reads and writes no memory). -/
def AP_HAL.Semaphore.Semaphore.pure' (this : UInt64) : Id Unit := do
  return ()

/-- C++ `AP_HAL::Semaphore::Semaphore : void ()`, `Semaphores.h:12-?`. -/
def AP_HAL.Semaphore.Semaphore (this : UInt64) : PMem.M Unit :=
  pure (_root_.Vehicle_lib.AP_HAL.Semaphore.Semaphore.pure' this)

/-- `HALSITL.Semaphore.Semaphore` as a pure function of its arguments (it reads and writes no memory). -/
def HALSITL.Semaphore.Semaphore.pure' (this : UInt64) : Id Unit := do
  _root_.Vehicle_lib.AP_HAL.Semaphore.Semaphore.pure' this
  return ()

/-- C++ `HALSITL::Semaphore::Semaphore : void ()`, `Semaphores.h:13-?`. -/
def HALSITL.Semaphore.Semaphore (this : UInt64) : PMem.M Unit :=
  pure (_root_.Vehicle_lib.HALSITL.Semaphore.Semaphore.pure' this)

/-- C++ `BufferPrinter::write : size_t (uint8_t)`, `Util.cpp:21-27`. -/
def BufferPrinter.write (this : UInt64) (c : UInt8) : PMem.M UInt64 := do
  let mut c := c
  let t'1 ← PMem.ldU64 (this + 8)
  let t'2 ← PMem.ldU64 (this + 24)
  if (decide (t'1 < t'2)) then
    let t'3 := UInt8.toInt8 (c)
    let t'4 ← PMem.ldU64 (this + 16)
    let t'5 ← PMem.ldU64 (this + 8)
    PMem.stI8 (t'4 + ((UInt64.toInt64 (t'5)) * 1).toUInt64) t'3
  let t'6 := (this + 8)
  let t'7 ← PMem.ldU64 t'6
  let t'8 := (t'7 + 1)
  PMem.stU64 t'6 t'8
  return Int64.toUInt64 (Int32.toInt64 ((1 : Int32)))

/-- C++ `ftoa_engine : int16_t (float, char *, uint8_t, uint8_t)`, `ftoa_engine.cpp:88-237`. -/
def ftoa_engine.body (fp : UInt64) (val : Binary32) (buf : UInt64) (precision : UInt8) (maxDecimals : UInt8) : PMem.M Int16 := do
  PMem.stF32 (fp + 0) val
  let mut buf := buf
  let mut precision := precision
  let mut maxDecimals := maxDecimals
  let mut goto_roundup : Bool := false
  let mut flags : UInt8 := default  -- uninitialized in C
  let mut valbits : UInt64 := (fp + 0)
  let t'1 ← PMem.ldF32 (fp + 0)
  PMem.stF32 (fp + 8) t'1
  let t'2 ← PMem.ldU32 (fp + 8)
  let mut frac : UInt32 := UInt64.toUInt32 (((UInt32.toUInt64 (t'2)) &&& (8388607 : UInt64)))
  if (decide ((UInt32.toInt32 (UInt8.toUInt32 (precision))) > (7 : Int32))) then
    let t'3 := Int8.toUInt8 (Int32.toInt8 ((7 : Int32)))
    precision := t'3
  let t'4 ← PMem.ldU8 (valbits + ((Int32.toInt64 ((3 : Int32))) * 1).toUInt64)
  if ((UInt32.toInt32 (UInt8.toUInt32 (t'4))) &&& ((1 : Int32) <<< (7 : Int32))) != (0 : Int32) then
    let t'5 := Int8.toUInt8 (Int32.toInt8 ((1 : Int32)))
    flags := t'5
  else
    let t'6 := Int8.toUInt8 (Int32.toInt8 ((0 : Int32)))
    flags := t'6
  let t'7 ← PMem.ldU8 (valbits + ((Int32.toInt64 ((3 : Int32))) * 1).toUInt64)
  let mut exp : UInt8 := Int8.toUInt8 (Int32.toInt8 (((UInt32.toInt32 (UInt8.toUInt32 (t'7))) <<< (1 : Int32))))
  let t'8 ← PMem.ldU8 (valbits + ((Int32.toInt64 ((2 : Int32))) * 1).toUInt64)
  if ((UInt32.toInt32 (UInt8.toUInt32 (t'8))) &&& ((1 : Int32) <<< (7 : Int32))) != (0 : Int32) then
    let t'9 := exp
    let t'10 := (t'9 + 1)
    exp := t'10
  if ((UInt32.toInt32 (UInt8.toUInt32 (exp))) == (0 : Int32)) then
    if (frac == (Int32.toUInt32 ((0 : Int32)))) then
      let t'11 := Int32.toInt8 (((UInt32.toInt32 (UInt8.toUInt32 (flags))) ||| (2 : Int32)))
      PMem.stI8 (buf + ((Int32.toInt64 ((0 : Int32))) * 1).toUInt64) t'11
      let mut i : UInt8 := default  -- uninitialized in C
      let t'12 := Int8.toUInt8 (Int32.toInt8 ((0 : Int32)))
      i := t'12
      let mut first'13 := true
      for _ in PMem.loopFuel do
        if !first'13 then
          let t'14 := i
          let t'15 := (t'14 + 1)
          i := t'15
          pure ()
        first'13 := false
        if !((decide ((UInt32.toInt32 (UInt8.toUInt32 (i))) ≤ (UInt32.toInt32 (UInt8.toUInt32 (precision)))))) then break
        PMem.stI8 (buf + ((Int32.toInt64 (((UInt32.toInt32 (UInt8.toUInt32 (i))) + (1 : Int32)))) * 1).toUInt64) (48 : Int8)
      return Int32.toInt16 ((0 : Int32))
    else
      let t'16 := Int8.toUInt8 (Int32.toInt8 ((1 : Int32)))
      exp := t'16
  else
    if ((UInt32.toInt32 (UInt8.toUInt32 (exp))) == (255 : Int32)) then
      if (frac == (Int32.toUInt32 ((0 : Int32)))) then
        let t'17 := (flags ||| (Int8.toUInt8 (Int32.toInt8 ((4 : Int32)))))
        flags := t'17
      else
        let t'18 := (flags ||| (Int8.toUInt8 (Int32.toInt8 ((8 : Int32)))))
        flags := t'18
    let t'19 := (frac ||| (UInt64.toUInt32 (((1 : UInt64) <<< (Int64.toUInt64 (Int32.toInt64 ((23 : Int32))))))))
    frac := t'19
  let mut idx : UInt8 := Int8.toUInt8 (Int32.toInt8 (((UInt32.toInt32 (UInt8.toUInt32 (exp))) >>> (3 : Int32))))
  let t'20 ← PMem.ldI8 ((0x130e0 : UInt64) /- &exponentTable -/ + ((UInt64.toInt64 (UInt8.toUInt64 (idx))) * 1).toUInt64)
  let mut exp10 : Int8 := t'20
  let t'21 ← PMem.ldU32 ((0x13100 : UInt64) /- &factorTable -/ + ((UInt64.toInt64 (UInt8.toUInt64 (idx))) * 4).toUInt64)
  let mut prod : Int64 := ((UInt64.toInt64 (UInt32.toUInt64 (frac))) * (UInt64.toInt64 (UInt32.toUInt64 (t'21))))
  let t'22 := (prod >>> (Int32.toInt64 (((15 : Int32) - ((UInt32.toInt32 (UInt8.toUInt32 (exp))) &&& (7 : Int32))))))
  prod := t'22
  let mut hadNonzeroDigit : UInt8 := Int8.toUInt8 (Int32.toInt8 ((0 : Int32)))
  let mut outputIdx : UInt8 := Int8.toUInt8 (Int32.toInt8 ((0 : Int32)))
  let mut decimal : Int64 := UInt64.toInt64 ((100000000000000 : UInt64))
  for _ in [0:1] do
    let mut first'23 := true
    for _ in PMem.loopFuel do
      if !first'23 then
        if !((decide ((UInt32.toInt32 (UInt8.toUInt32 (outputIdx))) < (UInt32.toInt32 (UInt8.toUInt32 (precision)))))) then break
      first'23 := false
      let mut digit : Int8 := (48 : Int8)
      if (decimal == (Int32.toInt64 ((0 : Int32)))) then
        break
      for _ in PMem.loopFuel do
        if !((1 : Int32) != (0 : Int32)) then break
        for _ in PMem.loopFuel do
          let t'24 := (prod - decimal)
          prod := t'24
          if !((decide (prod ≥ (Int32.toInt64 ((0 : Int32)))))) then break
          let t'25 := digit
          let t'26 := (t'25 + 1)
          digit := t'26
        let t'27 := (prod + decimal)
        prod := t'27
        let t'28 := (decimal / (Int32.toInt64 ((10 : Int32))))
        decimal := t'28
        if hadNonzeroDigit != (0 : UInt8) then
          break
        if ((Int8.toInt32 (digit)) == (Int8.toInt32 ((48 : Int8)))) then
          let t'29 := exp10
          let t'30 := (t'29 - 1)
          exp10 := t'30
          continue
        let t'31 := Int8.toUInt8 (Int32.toInt8 ((1 : Int32)))
        hadNonzeroDigit := t'31
        if ((UInt32.toInt32 (UInt8.toUInt32 (maxDecimals))) != (0 : Int32)) then
          let mut beforeDP : Int8 := Int32.toInt8 (((Int8.toInt32 (exp10)) + (1 : Int32)))
          if (decide ((Int8.toInt32 (beforeDP)) < (1 : Int32))) then
            let t'32 := Int32.toInt8 ((1 : Int32))
            beforeDP := t'32
          let t'33 := Int8.toUInt8 (Int32.toInt8 ((((UInt32.toInt32 (UInt8.toUInt32 (maxDecimals))) + (Int8.toInt32 (beforeDP))) - (1 : Int32))))
          maxDecimals := t'33
          if (decide ((UInt32.toInt32 (UInt8.toUInt32 (precision))) > (UInt32.toInt32 (UInt8.toUInt32 (maxDecimals))))) then
            precision := maxDecimals
        else
          let t'34 := precision
          let t'35 := (t'34 + 1)
          precision := t'35
        break
      let t'36 := outputIdx
      let t'37 := (t'36 + 1)
      outputIdx := t'37
      if (decide ((Int8.toInt32 (digit)) < ((Int8.toInt32 ((48 : Int8))) + (10 : Int32)))) then
        PMem.stI8 (buf + ((UInt64.toInt64 (UInt8.toUInt64 (outputIdx))) * 1).toUInt64) digit
      else
        hadNonzeroDigit := outputIdx
        let mut first'38 := true
        for _ in PMem.loopFuel do
          if !first'38 then
            let t'39 := hadNonzeroDigit
            let t'40 := (t'39 - 1)
            hadNonzeroDigit := t'40
            pure ()
          first'38 := false
          if !((decide ((UInt32.toInt32 (UInt8.toUInt32 (hadNonzeroDigit))) > (0 : Int32)))) then break
          PMem.stI8 (buf + ((UInt64.toInt64 (UInt8.toUInt64 (hadNonzeroDigit))) * 1).toUInt64) (57 : Int8)
        goto_roundup := true
        break
    if goto_roundup then
      break
    let t'41 := (decimal * (Int32.toInt64 ((10 : Int32))))
    decimal := t'41
  if (goto_roundup || (decide ((prod - (decimal >>> (Int32.toInt64 ((1 : Int32))))) ≥ (Int32.toInt64 ((0 : Int32)))))) then
    for _ in PMem.loopFuel do
      if !(((UInt32.toInt32 (UInt8.toUInt32 (outputIdx))) != (0 : Int32))) then break
      let t'42 := (buf + ((UInt64.toInt64 (UInt8.toUInt64 (outputIdx))) * 1).toUInt64)
      let t'43 ← PMem.ldI8 t'42
      let t'44 := (t'43 + 1)
      PMem.stI8 t'42 t'44
      let t'45 ← PMem.ldI8 (buf + ((UInt64.toInt64 (UInt8.toUInt64 (outputIdx))) * 1).toUInt64)
      if ((Int8.toInt32 (t'45)) == ((Int8.toInt32 ((48 : Int8))) + (10 : Int32))) then
        if ((UInt32.toInt32 (UInt8.toUInt32 (outputIdx))) == (1 : Int32)) then
          PMem.stI8 (buf + ((UInt64.toInt64 (UInt8.toUInt64 (outputIdx))) * 1).toUInt64) (49 : Int8)
          let t'46 := exp10
          let t'47 := (t'46 + 1)
          exp10 := t'47
          let t'48 := (flags ||| (Int8.toUInt8 (Int32.toInt8 ((16 : Int32)))))
          flags := t'48
          break
        else
          let t'49 := outputIdx
          let t'50 := (t'49 - 1)
          outputIdx := t'50
          PMem.stI8 (buf + ((UInt64.toInt64 (UInt8.toUInt64 (t'49))) * 1).toUInt64) (48 : Int8)
      else
        break
  let t'51 := UInt8.toInt8 (flags)
  PMem.stI8 (buf + ((Int32.toInt64 ((0 : Int32))) * 1).toUInt64) t'51
  return Int8.toInt16 (exp10)

def ftoa_engine (val : Binary32) (buf : UInt64) (precision : UInt8) (maxDecimals : UInt8) : PMem.M Int16 := do
  let fp ← PMem.enter 12
  let r ← ftoa_engine.body fp val buf precision maxDecimals
  PMem.leave fp
  return r

/-- C++ `ulltoa_invert : char *(uint64_t, char *, uint8_t)`, `utoa_invert.cpp:79-122`. -/
def ulltoa_invert (val : UInt64) (s : UInt64) (base : UInt8) : PMem.M UInt64 := do
  let mut val := val
  let mut s := s
  let mut base := base
  if ((UInt32.toInt32 (UInt8.toUInt32 (base))) == (8 : Int32)) then
    let mut first'1 := true
    for _ in PMem.loopFuel do
      if !first'1 then
        if !(val != (0 : UInt64)) then break
      first'1 := false
      let t'2 := UInt8.toInt8 (UInt64.toUInt8 (((Int64.toUInt64 (Int8.toInt64 ((48 : Int8)))) + (val &&& (Int64.toUInt64 (Int32.toInt64 ((7 : Int32))))))))
      let t'3 := s
      let t'4 := (t'3 + 1)
      s := t'4
      PMem.stI8 t'3 t'2
      let t'5 := (val >>> (Int64.toUInt64 (Int32.toInt64 ((3 : Int32)))))
      val := t'5
    return s
  if ((UInt32.toInt32 (UInt8.toUInt32 (base))) == (16 : Int32)) then
    let mut first'6 := true
    for _ in PMem.loopFuel do
      if !first'6 then
        if !(val != (0 : UInt64)) then break
      first'6 := false
      let mut digit : UInt8 := UInt64.toUInt8 (((Int64.toUInt64 (Int8.toInt64 ((48 : Int8)))) + (val &&& (Int64.toUInt64 (Int32.toInt64 ((15 : Int32)))))))
      if (decide ((UInt32.toInt32 (UInt8.toUInt32 (digit))) > ((Int8.toInt32 ((48 : Int8))) + (9 : Int32)))) then
        let t'7 := (digit + (Int8.toUInt8 (Int32.toInt8 ((((Int8.toInt32 ((65 : Int8))) - (Int8.toInt32 ((48 : Int8)))) - (10 : Int32))))))
        digit := t'7
      let t'8 := UInt8.toInt8 (digit)
      let t'9 := s
      let t'10 := (t'9 + 1)
      s := t'10
      PMem.stI8 t'9 t'8
      let t'11 := (val >>> (Int64.toUInt64 (Int32.toInt64 ((4 : Int32)))))
      val := t'11
    return s
  let mut xval : UInt64 := val
  let mut first'12 := true
  for _ in PMem.loopFuel do
    if !first'12 then
      if !(xval != (0 : UInt64)) then break
    first'12 := false
    let mut saved : UInt8 := UInt64.toUInt8 (xval)
    let t'13 := (xval &&& (Int64.toUInt64 (Int32.toInt64 ((~~~(1 : Int32))))))
    xval := t'13
    let t'14 := (xval + (Int64.toUInt64 (Int32.toInt64 ((2 : Int32)))))
    xval := t'14
    let t'15 := (xval + (xval >>> (Int64.toUInt64 (Int32.toInt64 ((1 : Int32))))))
    xval := t'15
    let t'16 := (xval + (xval >>> (Int64.toUInt64 (Int32.toInt64 ((4 : Int32))))))
    xval := t'16
    let t'17 := (xval + (xval >>> (Int64.toUInt64 (Int32.toInt64 ((8 : Int32))))))
    xval := t'17
    let t'18 := (xval + (xval >>> (Int64.toUInt64 (Int32.toInt64 ((16 : Int32))))))
    xval := t'18
    let t'19 := (xval + (xval >>> (Int64.toUInt64 (Int32.toInt64 ((32 : Int32))))))
    xval := t'19
    let t'20 := (xval >>> (Int64.toUInt64 (Int32.toInt64 ((4 : Int32)))))
    xval := t'20
    let t'21 := Int32.toInt8 ((((Int8.toInt32 ((48 : Int8))) + (UInt32.toInt32 (UInt8.toUInt32 (saved)))) - ((10 : Int32) * (UInt32.toInt32 (UInt8.toUInt32 ((UInt64.toUInt8 (xval))))))))
    let t'22 := s
    let t'23 := (t'22 + 1)
    s := t'23
    PMem.stI8 t'22 t'21
  return s

/-- C++ `ultoa_invert : char *(uint32_t, char *, uint8_t)`, `utoa_invert.cpp:34-76`. -/
def ultoa_invert (val : UInt32) (s : UInt64) (base : UInt8) : PMem.M UInt64 := do
  let mut val := val
  let mut s := s
  let mut base := base
  if ((UInt32.toInt32 (UInt8.toUInt32 (base))) == (8 : Int32)) then
    let mut first'1 := true
    for _ in PMem.loopFuel do
      if !first'1 then
        if !(val != (0 : UInt32)) then break
      first'1 := false
      let t'2 := UInt8.toInt8 (UInt32.toUInt8 (((Int32.toUInt32 (Int8.toInt32 ((48 : Int8)))) + (val &&& (Int32.toUInt32 ((7 : Int32)))))))
      let t'3 := s
      let t'4 := (t'3 + 1)
      s := t'4
      PMem.stI8 t'3 t'2
      let t'5 := (val >>> (Int32.toUInt32 ((3 : Int32))))
      val := t'5
    return s
  if ((UInt32.toInt32 (UInt8.toUInt32 (base))) == (16 : Int32)) then
    let mut first'6 := true
    for _ in PMem.loopFuel do
      if !first'6 then
        if !(val != (0 : UInt32)) then break
      first'6 := false
      let mut digit : UInt8 := UInt32.toUInt8 (((Int32.toUInt32 (Int8.toInt32 ((48 : Int8)))) + (val &&& (Int32.toUInt32 ((15 : Int32))))))
      if (decide ((UInt32.toInt32 (UInt8.toUInt32 (digit))) > ((Int8.toInt32 ((48 : Int8))) + (9 : Int32)))) then
        let t'7 := (digit + (Int8.toUInt8 (Int32.toInt8 ((((Int8.toInt32 ((65 : Int8))) - (Int8.toInt32 ((48 : Int8)))) - (10 : Int32))))))
        digit := t'7
      let t'8 := UInt8.toInt8 (digit)
      let t'9 := s
      let t'10 := (t'9 + 1)
      s := t'10
      PMem.stI8 t'9 t'8
      let t'11 := (val >>> (Int32.toUInt32 ((4 : Int32))))
      val := t'11
    return s
  let mut xval : UInt64 := UInt32.toUInt64 (val)
  let mut first'12 := true
  for _ in PMem.loopFuel do
    if !first'12 then
      if !(xval != (0 : UInt64)) then break
    first'12 := false
    let mut saved : UInt8 := UInt64.toUInt8 (xval)
    let t'13 := (xval &&& (Int64.toUInt64 (Int32.toInt64 ((~~~(1 : Int32))))))
    xval := t'13
    let t'14 := (xval + (Int64.toUInt64 (Int32.toInt64 ((2 : Int32)))))
    xval := t'14
    let t'15 := (xval + (xval >>> (Int64.toUInt64 (Int32.toInt64 ((1 : Int32))))))
    xval := t'15
    let t'16 := (xval + (xval >>> (Int64.toUInt64 (Int32.toInt64 ((4 : Int32))))))
    xval := t'16
    let t'17 := (xval + (xval >>> (Int64.toUInt64 (Int32.toInt64 ((8 : Int32))))))
    xval := t'17
    let t'18 := (xval + (xval >>> (Int64.toUInt64 (Int32.toInt64 ((16 : Int32))))))
    xval := t'18
    let t'19 := (xval + (xval >>> (Int64.toUInt64 (Int32.toInt64 ((32 : Int32))))))
    xval := t'19
    let t'20 := (xval >>> (Int64.toUInt64 (Int32.toInt64 ((4 : Int32)))))
    xval := t'20
    let t'21 := Int32.toInt8 ((((Int8.toInt32 ((48 : Int8))) + (UInt32.toInt32 (UInt8.toUInt32 (saved)))) - ((10 : Int32) * (UInt32.toInt32 (UInt8.toUInt32 ((UInt64.toUInt8 (xval))))))))
    let t'22 := s
    let t'23 := (t'22 + 1)
    s := t'23
    PMem.stI8 t'22 t'21
  return s

/-- C++ `print_vprintf : void (AP_HAL::BetterStream *, const char *, va_list)`, `print_vprintf.cpp:74-540`. -/
def print_vprintf.body (fp : UInt64) (s : UInt64) (fmt : UInt64) (ap : UInt64) : PMem.M Unit := do
  let mut s := s
  let mut fmt := fmt
  PMem.stU64 (fp + 0) ap
  let mut c : UInt8 := default  -- uninitialized in C
  let mut flags : UInt16 := default  -- uninitialized in C
  let mut width : UInt8 := default  -- uninitialized in C
  let mut prec : UInt8 := default  -- uninitialized in C
  let mut first'1 := true
  for _ in PMem.loopFuel do
    first'1 := false
    let mut goto_tail : Bool := false
    let mut goto_non_string : Bool := false
    let mut first'2 := true
    for _ in PMem.loopFuel do
      first'2 := false
      let t'3 := fmt
      let t'4 := (t'3 + 1)
      fmt := t'4
      let t'5 ← PMem.ldI8 t'3
      let t'6 := Int8.toUInt8 (t'5)
      c := t'6
      if !(c != (0 : UInt8)) then
        return ()
      if ((UInt32.toInt32 (UInt8.toUInt32 (c))) == (Int8.toInt32 ((37 : Int8)))) then
        let t'7 := fmt
        let t'8 := (t'7 + 1)
        fmt := t'8
        let t'9 ← PMem.ldI8 t'7
        let t'10 := Int8.toUInt8 (t'9)
        c := t'10
        if ((UInt32.toInt32 (UInt8.toUInt32 (c))) != (Int8.toInt32 ((37 : Int8)))) then
          break
      let t'11 ← BufferPrinter.write s c
      discard <| pure (t'11)
    let t'12 := Int16.toUInt16 (Int32.toInt16 ((0 : Int32)))
    flags := t'12
    let t'13 := Int8.toUInt8 (Int32.toInt8 ((0 : Int32)))
    width := t'13
    let t'14 := Int8.toUInt8 (Int32.toInt8 ((0 : Int32)))
    prec := t'14
    let mut first'15 := true
    for _ in PMem.loopFuel do
      if !first'15 then
        let t'16 := fmt
        let t'17 := (t'16 + 1)
        fmt := t'17
        let t'18 ← PMem.ldI8 t'16
        let t'19 := Int8.toUInt8 (t'18)
        c := t'19
        if !(((UInt32.toInt32 (UInt8.toUInt32 (c))) != (0 : Int32))) then break
      first'15 := false
      let mut goto_cont_14 : Bool := false
      let mut break_27 : Bool := false
      for _ in [0:1] do
        if (decide ((UInt32.toInt32 (UInt16.toUInt32 (flags))) < (32 : Int32))) then
          let sw'20 := UInt32.toInt32 (UInt8.toUInt32 (c))
          if sw'20 == (48 : Int32) then
            let t'21 := (flags ||| (Int16.toUInt16 (Int32.toInt16 ((1 : Int32)))))
            flags := t'21
            goto_cont_14 := true
          else if sw'20 == (43 : Int32) then
            let t'22 := (flags ||| (Int16.toUInt16 (Int32.toInt16 ((2 : Int32)))))
            flags := t'22
            let t'23 := (flags ||| (Int16.toUInt16 (Int32.toInt16 ((4 : Int32)))))
            flags := t'23
            goto_cont_14 := true
          else if sw'20 == (32 : Int32) then
            let t'24 := (flags ||| (Int16.toUInt16 (Int32.toInt16 ((4 : Int32)))))
            flags := t'24
            goto_cont_14 := true
          else if sw'20 == (45 : Int32) then
            let t'25 := (flags ||| (Int16.toUInt16 (Int32.toInt16 ((8 : Int32)))))
            flags := t'25
            goto_cont_14 := true
          else if sw'20 == (35 : Int32) then
            let t'26 := (flags ||| (Int16.toUInt16 (Int32.toInt16 ((16 : Int32)))))
            flags := t'26
            goto_cont_14 := true
          else
            pure ()
          if goto_cont_14 then
            break
          if goto_cont_14 then
            break
          if goto_cont_14 then
            break
          if goto_cont_14 then
            break
          if goto_cont_14 then
            break
        if (decide ((UInt32.toInt32 (UInt16.toUInt32 (flags))) < (128 : Int32))) then
          if ((decide ((UInt32.toInt32 (UInt8.toUInt32 (c))) ≥ (Int8.toInt32 ((48 : Int8))))) && (decide ((UInt32.toInt32 (UInt8.toUInt32 (c))) ≤ (Int8.toInt32 ((57 : Int8)))))) then
            let t'27 := (c - (Int8.toUInt8 (Int32.toInt8 ((Int8.toInt32 ((48 : Int8)))))))
            c := t'27
            if ((UInt32.toInt32 (UInt16.toUInt32 (flags))) &&& (64 : Int32)) != (0 : Int32) then
              let t'28 := Int8.toUInt8 (Int32.toInt8 ((((10 : Int32) * (UInt32.toInt32 (UInt8.toUInt32 (prec)))) + (UInt32.toInt32 (UInt8.toUInt32 (c))))))
              prec := t'28
              goto_cont_14 := true
              break
            let t'29 := Int8.toUInt8 (Int32.toInt8 ((((10 : Int32) * (UInt32.toInt32 (UInt8.toUInt32 (width)))) + (UInt32.toInt32 (UInt8.toUInt32 (c))))))
            width := t'29
            let t'30 := (flags ||| (Int16.toUInt16 (Int32.toInt16 ((32 : Int32)))))
            flags := t'30
            goto_cont_14 := true
            break
          if ((UInt32.toInt32 (UInt8.toUInt32 (c))) == (Int8.toInt32 ((46 : Int8)))) then
            if ((UInt32.toInt32 (UInt16.toUInt32 (flags))) &&& (64 : Int32)) != (0 : Int32) then
              return ()
            let t'31 := (flags ||| (Int16.toUInt16 (Int32.toInt16 ((64 : Int32)))))
            flags := t'31
            goto_cont_14 := true
            break
          if ((UInt32.toInt32 (UInt8.toUInt32 (c))) == (Int8.toInt32 ((108 : Int8)))) then
            let t'32 := (flags ||| (Int16.toUInt16 (Int32.toInt16 ((128 : Int32)))))
            flags := t'32
            goto_cont_14 := true
            break
          if ((UInt32.toInt32 (UInt8.toUInt32 (c))) == (Int8.toInt32 ((104 : Int8)))) then
            goto_cont_14 := true
            break
        else
          if ((((UInt32.toInt32 (UInt16.toUInt32 (flags))) &&& (128 : Int32)) != (0 : Int32)) && ((UInt32.toInt32 (UInt8.toUInt32 (c))) == (Int8.toInt32 ((108 : Int8))))) then
            let t'33 := (flags ||| (Int16.toUInt16 (Int32.toInt16 ((256 : Int32)))))
            flags := t'33
            goto_cont_14 := true
            break
        break_27 := true
        break
      if break_27 then
        break
    for _ in [0:1] do
      let mut goto_flt_oper : Bool := false
      let mut cond_76 : Bool := ((decide ((UInt32.toInt32 (UInt8.toUInt32 (c))) ≥ (Int8.toInt32 ((69 : Int8))))) && (decide ((UInt32.toInt32 (UInt8.toUInt32 (c))) ≤ (Int8.toInt32 ((71 : Int8))))))
      if cond_76 then
        for _ in [0:1] do
          let t'34 := (flags ||| (Int16.toUInt16 (Int32.toInt16 ((16 : Int32)))))
          flags := t'34
          let t'35 := (c + (Int8.toUInt8 (Int32.toInt8 (((Int8.toInt32 ((101 : Int8))) - (Int8.toInt32 ((69 : Int8))))))))
          c := t'35
          goto_flt_oper := true
          break
      if (goto_flt_oper || (!cond_76)) then
        if (goto_flt_oper || ((decide ((UInt32.toInt32 (UInt8.toUInt32 (c))) ≥ (Int8.toInt32 ((101 : Int8))))) && (decide ((UInt32.toInt32 (UInt8.toUInt32 (c))) ≤ (Int8.toInt32 ((103 : Int8))))))) then
          let mut exp : Int32 := default  -- uninitialized in C
          let mut n : Int32 := default  -- uninitialized in C
          let mut vtype : UInt8 := default  -- uninitialized in C
          let mut sign : UInt8 := default  -- uninitialized in C
          let mut ndigs : UInt8 := default  -- uninitialized in C
          if !goto_flt_oper then
            let t'36 := (flags &&& (Int16.toUInt16 (Int32.toInt16 ((~~~(16 : Int32))))))
            flags := t'36
          let t'37 ← PMem.ldU64 (fp + 0)
          let t'38 ← PMem.ldF64 t'37
          PMem.stU64 (fp + 0) (t'37 + 8)
          let mut value : Binary32 := Binary64.toBinary32 (t'38)
          if !(((UInt32.toInt32 (UInt16.toUInt32 (flags))) &&& (64 : Int32)) != (0 : Int32)) then
            let t'39 := Int8.toUInt8 (Int32.toInt8 ((6 : Int32)))
            prec := t'39
          let t'40 := (flags &&& (Int16.toUInt16 (Int32.toInt16 ((~~~((64 : Int32) ||| (128 : Int32)))))))
          flags := t'40
          if ((UInt32.toInt32 (UInt8.toUInt32 (c))) == (Int8.toInt32 ((101 : Int8)))) then
            let t'41 := (flags ||| (Int16.toUInt16 (Int32.toInt16 ((64 : Int32)))))
            flags := t'41
          else
            if ((UInt32.toInt32 (UInt8.toUInt32 (c))) == (Int8.toInt32 ((102 : Int8)))) then
              let t'42 := (flags ||| (Int16.toUInt16 (Int32.toInt16 ((128 : Int32)))))
              flags := t'42
            else
              if (decide ((UInt32.toInt32 (UInt8.toUInt32 (prec))) > (0 : Int32))) then
                let t'43 := (prec - (Int8.toUInt8 (Int32.toInt8 ((1 : Int32)))))
                prec := t'43
          if ((((UInt32.toInt32 (UInt16.toUInt32 (flags))) &&& (128 : Int32)) != (0 : Int32)) && (decide ((Binary32.abs value) > (Int32.toBinary32 ((9999999 : Int32)))))) then
            let t'44 := Int16.toUInt16 (Int32.toInt16 ((((UInt32.toInt32 (UInt16.toUInt32 (flags))) &&& (~~~(128 : Int32))) ||| (64 : Int32))))
            flags := t'44
          if ((UInt32.toInt32 (UInt16.toUInt32 (flags))) &&& (128 : Int32)) != (0 : Int32) then
            let t'45 := Int8.toUInt8 (Int32.toInt8 ((7 : Int32)))
            vtype := t'45
            let mut c'46 : Int32 := default
            if (decide ((UInt32.toInt32 (UInt8.toUInt32 (prec))) < (60 : Int32))) then
              c'46 := ((UInt32.toInt32 (UInt8.toUInt32 (prec))) + (1 : Int32))
            else
              c'46 := (60 : Int32)
            let t'47 := Int8.toUInt8 (Int32.toInt8 (c'46))
            ndigs := t'47
          else
            if (decide ((UInt32.toInt32 (UInt8.toUInt32 (prec))) > (10 : Int32))) then
              let t'48 := Int8.toUInt8 (Int32.toInt8 ((10 : Int32)))
              prec := t'48
            vtype := prec
            let t'49 := Int8.toUInt8 (Int32.toInt8 ((0 : Int32)))
            ndigs := t'49
          let t'50 ← PMem.memset (fp + 8) (0 : Int32) (23 : UInt64)
          discard <| pure (t'50)
          let t'51 ← ftoa_engine value (fp + 8) vtype ndigs
          let t'52 := Int16.toInt32 (t'51)
          exp := t'52
          let t'53 ← PMem.ldU8 ((fp + 8) + ((Int32.toInt64 ((0 : Int32))) * 1).toUInt64)
          vtype := t'53
          let t'54 := Int8.toUInt8 (Int32.toInt8 ((0 : Int32)))
          sign := t'54
          if ((((UInt32.toInt32 (UInt8.toUInt32 (vtype))) &&& (1 : Int32)) != (0 : Int32)) && (!(((UInt32.toInt32 (UInt8.toUInt32 (vtype))) &&& (8 : Int32)) != (0 : Int32)))) then
            let t'55 := Int8.toUInt8 ((45 : Int8))
            sign := t'55
          else
            if ((UInt32.toInt32 (UInt16.toUInt32 (flags))) &&& (2 : Int32)) != (0 : Int32) then
              let t'56 := Int8.toUInt8 ((43 : Int8))
              sign := t'56
            else
              if ((UInt32.toInt32 (UInt16.toUInt32 (flags))) &&& (4 : Int32)) != (0 : Int32) then
                let t'57 := Int8.toUInt8 ((32 : Int8))
                sign := t'57
          if ((UInt32.toInt32 (UInt8.toUInt32 (vtype))) &&& ((8 : Int32) ||| (4 : Int32))) != (0 : Int32) then
            let mut c'58 : Int32 := default
            if sign != (0 : UInt8) then
              c'58 := (4 : Int32)
            else
              c'58 := (3 : Int32)
            let t'59 := Int8.toUInt8 (Int32.toInt8 (c'58))
            ndigs := t'59
            if (decide ((UInt32.toInt32 (UInt8.toUInt32 (width))) > (UInt32.toInt32 (UInt8.toUInt32 (ndigs))))) then
              let t'60 := (width - (Int8.toUInt8 (Int32.toInt8 ((UInt32.toInt32 (UInt8.toUInt32 (ndigs)))))))
              width := t'60
              if !(((UInt32.toInt32 (UInt16.toUInt32 (flags))) &&& (8 : Int32)) != (0 : Int32)) then
                let mut first'61 := true
                for _ in PMem.loopFuel do
                  if !first'61 then
                    let t'62 := (width - 1)
                    width := t'62
                    if !(width != (0 : UInt8)) then break
                  first'61 := false
                  let t'63 ← BufferPrinter.write s (Int8.toUInt8 ((32 : Int8)))
                  discard <| pure (t'63)
            else
              let t'64 := Int8.toUInt8 (Int32.toInt8 ((0 : Int32)))
              width := t'64
            if sign != (0 : UInt8) then
              let t'65 ← BufferPrinter.write s sign
              discard <| pure (t'65)
            let mut p : UInt64 := (0x16dec : UInt64) /- "inf" -/
            if ((UInt32.toInt32 (UInt8.toUInt32 (vtype))) &&& (8 : Int32)) != (0 : Int32) then
              let t'66 := (0x16df0 : UInt64) /- "nan" -/
              p := t'66
            for _ in PMem.loopFuel do
              let t'67 ← PMem.ldI8 p
              let t'68 := Int8.toUInt8 (t'67)
              ndigs := t'68
              if !(((UInt32.toInt32 (UInt8.toUInt32 (ndigs))) != (0 : Int32))) then break
              if ((UInt32.toInt32 (UInt16.toUInt32 (flags))) &&& (16 : Int32)) != (0 : Int32) then
                let t'69 := (ndigs + (Int8.toUInt8 (Int32.toInt8 (((Int8.toInt32 ((73 : Int8))) - (Int8.toInt32 ((105 : Int8))))))))
                ndigs := t'69
              let t'70 ← BufferPrinter.write s ndigs
              discard <| pure (t'70)
              let t'71 := p
              let t'72 := (t'71 + 1)
              p := t'72
            goto_tail := true
            break
          if ((UInt32.toInt32 (UInt16.toUInt32 (flags))) &&& (128 : Int32)) != (0 : Int32) then
            let t'73 := (ndigs + (Int8.toUInt8 (Int32.toInt8 (exp))))
            ndigs := t'73
            let mut sc'75 := ((UInt32.toInt32 (UInt8.toUInt32 (vtype))) &&& (16 : Int32)) != (0 : Int32)
            if sc'75 then
              let t'74 ← PMem.ldU8 ((fp + 8) + ((Int32.toInt64 ((1 : Int32))) * 1).toUInt64)
              sc'75 := ((UInt32.toInt32 (UInt8.toUInt32 (t'74))) == (Int8.toInt32 ((49 : Int8))))
            if sc'75 then
              let t'76 := (ndigs - (Int8.toUInt8 (Int32.toInt8 ((1 : Int32)))))
              ndigs := t'76
            if (decide ((Int8.toInt32 ((UInt8.toInt8 (ndigs)))) < (1 : Int32))) then
              let t'77 := Int8.toUInt8 (Int32.toInt8 ((1 : Int32)))
              ndigs := t'77
            else
              if (decide ((UInt32.toInt32 (UInt8.toUInt32 (ndigs))) > (8 : Int32))) then
                let t'78 := Int8.toUInt8 (Int32.toInt8 ((8 : Int32)))
                ndigs := t'78
          else
            if !(((UInt32.toInt32 (UInt16.toUInt32 (flags))) &&& (64 : Int32)) != (0 : Int32)) then
              if ((decide (exp ≤ (UInt32.toInt32 (UInt8.toUInt32 (prec))))) && (decide (exp ≥ (-(4 : Int32))))) then
                let t'79 := (flags ||| (Int16.toUInt16 (Int32.toInt16 ((128 : Int32)))))
                flags := t'79
              for _ in PMem.loopFuel do
                let mut sc'81 := prec != (0 : UInt8)
                if sc'81 then
                  let t'80 ← PMem.ldU8 ((fp + 8) + ((Int32.toInt64 (((1 : Int32) + (UInt32.toInt32 (UInt8.toUInt32 (prec)))))) * 1).toUInt64)
                  sc'81 := ((UInt32.toInt32 (UInt8.toUInt32 (t'80))) == (Int8.toInt32 ((48 : Int8))))
                if !(sc'81) then break
                let t'82 := prec
                let t'83 := (t'82 - 1)
                prec := t'83
              if ((UInt32.toInt32 (UInt16.toUInt32 (flags))) &&& (128 : Int32)) != (0 : Int32) then
                let t'84 := Int8.toUInt8 (Int32.toInt8 (((UInt32.toInt32 (UInt8.toUInt32 (prec))) + (1 : Int32))))
                ndigs := t'84
                let mut c'85 : Int32 := default
                if (decide ((UInt32.toInt32 (UInt8.toUInt32 (prec))) > exp)) then
                  c'85 := ((UInt32.toInt32 (UInt8.toUInt32 (prec))) - exp)
                else
                  c'85 := (0 : Int32)
                let t'86 := Int8.toUInt8 (Int32.toInt8 (c'85))
                prec := t'86
          if ((UInt32.toInt32 (UInt16.toUInt32 (flags))) &&& (128 : Int32)) != (0 : Int32) then
            let mut c'87 : Int32 := default
            if (decide (exp > (0 : Int32))) then
              c'87 := (exp + (1 : Int32))
            else
              c'87 := (1 : Int32)
            n := c'87
          else
            n := (5 : Int32)
          if sign != (0 : UInt8) then
            let t'88 := (n + (1 : Int32))
            n := t'88
          if prec != (0 : UInt8) then
            let t'89 := (n + ((UInt32.toInt32 (UInt8.toUInt32 (prec))) + (1 : Int32)))
            n := t'89
          let mut c'90 : Int32 := default
          if (decide ((UInt32.toInt32 (UInt8.toUInt32 (width))) > n)) then
            c'90 := ((UInt32.toInt32 (UInt8.toUInt32 (width))) - n)
          else
            c'90 := (0 : Int32)
          let t'91 := Int8.toUInt8 (Int32.toInt8 (c'90))
          width := t'91
          if !(((UInt32.toInt32 (UInt16.toUInt32 (flags))) &&& ((8 : Int32) ||| (1 : Int32))) != (0 : Int32)) then
            for _ in PMem.loopFuel do
              if !(width != (0 : UInt8)) then break
              let t'92 ← BufferPrinter.write s (Int8.toUInt8 ((32 : Int8)))
              discard <| pure (t'92)
              let t'93 := width
              let t'94 := (t'93 - 1)
              width := t'94
          if sign != (0 : UInt8) then
            let t'95 ← BufferPrinter.write s sign
            discard <| pure (t'95)
          if !(((UInt32.toInt32 (UInt16.toUInt32 (flags))) &&& (8 : Int32)) != (0 : Int32)) then
            for _ in PMem.loopFuel do
              if !(width != (0 : UInt8)) then break
              let t'96 ← BufferPrinter.write s (Int8.toUInt8 ((48 : Int8)))
              discard <| pure (t'96)
              let t'97 := width
              let t'98 := (t'97 - 1)
              width := t'98
          if ((UInt32.toInt32 (UInt16.toUInt32 (flags))) &&& (128 : Int32)) != (0 : Int32) then
            let mut c'99 : Int32 := default
            if (decide (exp > (0 : Int32))) then
              c'99 := exp
            else
              c'99 := (0 : Int32)
            n := c'99
            let mut v : UInt8 := Int8.toUInt8 (Int32.toInt8 ((0 : Int32)))
            let mut first'100 := true
            for _ in PMem.loopFuel do
              if !first'100 then
                if !((1 : Int32) != (0 : Int32)) then break
              first'100 := false
              if (n == (-(1 : Int32))) then
                let t'101 ← BufferPrinter.write s (Int8.toUInt8 ((46 : Int8)))
                discard <| pure (t'101)
              let mut c'102 : Int32 := default
              if ((decide (n ≤ exp)) && (decide (n > (exp - (UInt32.toInt32 (UInt8.toUInt32 (ndigs))))))) then
                let t'103 ← PMem.ldU8 ((fp + 8) + ((Int32.toInt64 (((exp - n) + (1 : Int32)))) * 1).toUInt64)
                c'102 := UInt32.toInt32 (UInt8.toUInt32 (t'103))
              else
                c'102 := Int8.toInt32 ((48 : Int8))
              let t'104 := Int8.toUInt8 (Int32.toInt8 (c'102))
              v := t'104
              let t'105 := (n - 1)
              n := t'105
              if ((decide (n < (-(UInt32.toInt32 (UInt8.toUInt32 (prec)))))) || ((UInt32.toInt32 (UInt8.toUInt32 (v))) == (0 : Int32))) then
                break
              let t'106 ← BufferPrinter.write s v
              discard <| pure (t'106)
            let mut sc'110 := (n == exp)
            if sc'110 then
              let t'107 ← PMem.ldU8 ((fp + 8) + ((Int32.toInt64 ((1 : Int32))) * 1).toUInt64)
              let mut sc'109 := (decide ((UInt32.toInt32 (UInt8.toUInt32 (t'107))) > (Int8.toInt32 ((53 : Int8)))))
              if !sc'109 then
                let t'108 ← PMem.ldU8 ((fp + 8) + ((Int32.toInt64 ((1 : Int32))) * 1).toUInt64)
                sc'109 := (((UInt32.toInt32 (UInt8.toUInt32 (t'108))) == (Int8.toInt32 ((53 : Int8)))) && (!(((UInt32.toInt32 (UInt8.toUInt32 (vtype))) &&& (16 : Int32)) != (0 : Int32))))
              sc'110 := sc'109
            if sc'110 then
              let t'111 := Int8.toUInt8 ((49 : Int8))
              v := t'111
            if v != (0 : UInt8) then
              let t'112 ← BufferPrinter.write s v
              discard <| pure (t'112)
          else
            let t'113 ← PMem.ldU8 ((fp + 8) + ((Int32.toInt64 ((1 : Int32))) * 1).toUInt64)
            if ((UInt32.toInt32 (UInt8.toUInt32 (t'113))) != (Int8.toInt32 ((49 : Int8)))) then
              let t'114 := (vtype &&& (Int8.toUInt8 (Int32.toInt8 ((~~~(16 : Int32))))))
              vtype := t'114
            let t'115 ← PMem.ldU8 ((fp + 8) + ((Int32.toInt64 ((1 : Int32))) * 1).toUInt64)
            let t'116 ← BufferPrinter.write s t'115
            discard <| pure (t'116)
            if prec != (0 : UInt8) then
              let t'117 ← BufferPrinter.write s (Int8.toUInt8 ((46 : Int8)))
              discard <| pure (t'117)
              let t'118 := Int8.toUInt8 (Int32.toInt8 ((2 : Int32)))
              sign := t'118
              let mut first'119 := true
              for _ in PMem.loopFuel do
                if !first'119 then
                  let t'120 := (prec - 1)
                  prec := t'120
                  if !(prec != (0 : UInt8)) then break
                first'119 := false
                let t'121 := sign
                let t'122 := (t'121 + 1)
                sign := t'122
                let t'123 ← PMem.ldU8 ((fp + 8) + ((UInt64.toInt64 (UInt8.toUInt64 (t'121))) * 1).toUInt64)
                let t'124 ← BufferPrinter.write s t'123
                discard <| pure (t'124)
            let mut c'125 : Int8 := default
            if ((UInt32.toInt32 (UInt16.toUInt32 (flags))) &&& (16 : Int32)) != (0 : Int32) then
              c'125 := (69 : Int8)
            else
              c'125 := (101 : Int8)
            let t'126 ← BufferPrinter.write s (Int8.toUInt8 (c'125))
            discard <| pure (t'126)
            let t'127 := Int8.toUInt8 ((43 : Int8))
            ndigs := t'127
            if ((decide (exp < (0 : Int32))) || ((exp == (0 : Int32)) && (((UInt32.toInt32 (UInt8.toUInt32 (vtype))) &&& (16 : Int32)) != (0 : Int32)))) then
              let t'128 := -exp
              exp := t'128
              let t'129 := Int8.toUInt8 ((45 : Int8))
              ndigs := t'129
            let t'130 ← BufferPrinter.write s ndigs
            discard <| pure (t'130)
            let t'131 := Int8.toUInt8 ((48 : Int8))
            ndigs := t'131
            let mut first'132 := true
            for _ in PMem.loopFuel do
              if !first'132 then
                let t'133 := (exp - (10 : Int32))
                exp := t'133
                pure ()
              first'132 := false
              if !((decide (exp ≥ (10 : Int32)))) then break
              let t'134 := (ndigs + (Int8.toUInt8 (Int32.toInt8 ((1 : Int32)))))
              ndigs := t'134
            let t'135 ← BufferPrinter.write s ndigs
            discard <| pure (t'135)
            let t'136 ← BufferPrinter.write s (Int8.toUInt8 (Int32.toInt8 (((Int8.toInt32 ((48 : Int8))) + exp))))
            discard <| pure (t'136)
          goto_tail := true
          break
      for _ in [0:1] do
        let mut pnt : UInt64 := default  -- uninitialized in C
        let mut size : UInt64 := default  -- uninitialized in C
        for _ in [0:1] do
          let sw'137 := UInt32.toInt32 (UInt8.toUInt32 (c))
          if sw'137 == (99 : Int32) then
            let t'138 ← PMem.ldU64 (fp + 0)
            let t'139 ← PMem.ldI32 t'138
            PMem.stU64 (fp + 0) (t'138 + 8)
            let t'140 := Int8.toUInt8 (Int32.toInt8 (t'139))
            PMem.stU8 ((fp + 8) + ((Int32.toInt64 ((0 : Int32))) * 1).toUInt64) t'140
            let t'141 := (fp + 8)
            pnt := t'141
            let t'142 := Int64.toUInt64 (Int32.toInt64 ((1 : Int32)))
            size := t'142
          else if sw'137 == (115 : Int32) then
            let t'143 ← PMem.ldU64 (fp + 0)
            let t'144 ← PMem.ldU64 t'143
            PMem.stU64 (fp + 0) (t'143 + 8)
            pnt := t'144
            let mut c'145 : Int32 := default
            if ((UInt32.toInt32 (UInt16.toUInt32 (flags))) &&& (64 : Int32)) != (0 : Int32) then
              c'145 := UInt32.toInt32 (UInt8.toUInt32 (prec))
            else
              c'145 := ~~~(0 : Int32)
            let t'146 ← PMem.strnlen pnt (Int64.toUInt64 (Int32.toInt64 (c'145)))
            size := t'146
          else
            goto_non_string := true
            break
        if goto_non_string then
          break
        if !(((UInt32.toInt32 (UInt16.toUInt32 (flags))) &&& (8 : Int32)) != (0 : Int32)) then
          for _ in PMem.loopFuel do
            if !((decide (size < (UInt8.toUInt64 (width))))) then break
            let t'147 ← BufferPrinter.write s (Int8.toUInt8 ((32 : Int8)))
            discard <| pure (t'147)
            let t'148 := width
            let t'149 := (t'148 - 1)
            width := t'149
        for _ in PMem.loopFuel do
          if !(size != (0 : UInt64)) then break
          let t'150 := pnt
          let t'151 := (t'150 + 1)
          pnt := t'151
          let t'152 ← PMem.ldI8 t'150
          let t'153 ← BufferPrinter.write s (Int8.toUInt8 (t'152))
          discard <| pure (t'153)
          if width != (0 : UInt8) then
            let t'154 := (width - (Int8.toUInt8 (Int32.toInt8 ((1 : Int32)))))
            width := t'154
          let t'155 := (size - (Int64.toUInt64 (Int32.toInt64 ((1 : Int32)))))
          size := t'155
        goto_tail := true
        break
      if goto_tail then
        break
      if (((UInt32.toInt32 (UInt8.toUInt32 (c))) == (Int8.toInt32 ((100 : Int8)))) || ((UInt32.toInt32 (UInt8.toUInt32 (c))) == (Int8.toInt32 ((105 : Int8))))) then
        if ((UInt32.toInt32 (UInt16.toUInt32 (flags))) &&& (256 : Int32)) != (0 : Int32) then
          let t'156 ← PMem.ldU64 (fp + 0)
          let t'157 ← PMem.ldI64 t'156
          PMem.stU64 (fp + 0) (t'156 + 8)
          let mut x : Int64 := t'157
          let t'158 := (flags &&& (Int16.toUInt16 (Int32.toInt16 ((~~~((128 : Int32) ||| (16 : Int32)))))))
          flags := t'158
          if (decide (x < (Int32.toInt64 ((0 : Int32))))) then
            let t'159 := -x
            x := t'159
            let t'160 := (flags ||| (Int16.toUInt16 (Int32.toInt16 ((128 : Int32)))))
            flags := t'160
          let t'161 ← ulltoa_invert (Int64.toUInt64 (x)) (fp + 8) (Int8.toUInt8 (Int32.toInt8 ((10 : Int32))))
          let t'162 := Int8.toUInt8 (Int64.toInt8 (((t'161 - (fp + 8)).toInt64 / 1)))
          c := t'162
        else
          let mut c'163 : Int64 := default
          if ((UInt32.toInt32 (UInt16.toUInt32 (flags))) &&& (128 : Int32)) != (0 : Int32) then
            let t'164 ← PMem.ldU64 (fp + 0)
            let t'165 ← PMem.ldI64 t'164
            PMem.stU64 (fp + 0) (t'164 + 8)
            c'163 := t'165
          else
            let t'166 ← PMem.ldU64 (fp + 0)
            let t'167 ← PMem.ldI32 t'166
            PMem.stU64 (fp + 0) (t'166 + 8)
            c'163 := Int32.toInt64 (t'167)
          let mut x'2 : Int64 := c'163
          let t'168 := (flags &&& (Int16.toUInt16 (Int32.toInt16 ((~~~((128 : Int32) ||| (16 : Int32)))))))
          flags := t'168
          if (decide (x'2 < (Int32.toInt64 ((0 : Int32))))) then
            let t'169 := -x'2
            x'2 := t'169
            let t'170 := (flags ||| (Int16.toUInt16 (Int32.toInt16 ((128 : Int32)))))
            flags := t'170
          let t'171 ← ultoa_invert (Int32.toUInt32 (Int64.toInt32 (x'2))) (fp + 8) (Int8.toUInt8 (Int32.toInt8 ((10 : Int32))))
          let t'172 := Int8.toUInt8 (Int64.toInt8 (((t'171 - (fp + 8)).toInt64 / 1)))
          c := t'172
      else
        let mut goto_ultoa : Bool := false
        let mut base : Int32 := default  -- uninitialized in C
        for _ in [0:1] do
          if ((UInt32.toInt32 (UInt8.toUInt32 (c))) == (Int8.toInt32 ((117 : Int8)))) then
            let t'173 := (flags &&& (Int16.toUInt16 (Int32.toInt16 ((~~~(16 : Int32))))))
            flags := t'173
            base := (10 : Int32)
            goto_ultoa := true
            break
          let t'174 := (flags &&& (Int16.toUInt16 (Int32.toInt16 ((~~~((2 : Int32) ||| (4 : Int32)))))))
          flags := t'174
        if !goto_ultoa then
          let sw'175 := UInt32.toInt32 (UInt8.toUInt32 (c))
          if sw'175 == (111 : Int32) then
            base := (8 : Int32)
            goto_ultoa := true
          else if sw'175 == (112 : Int32) then
            let t'176 := (flags ||| (Int16.toUInt16 (Int32.toInt16 ((16 : Int32)))))
            flags := t'176
            if ((UInt32.toInt32 (UInt16.toUInt32 (flags))) &&& (16 : Int32)) != (0 : Int32) then
              let t'177 := (flags ||| (Int16.toUInt16 (Int32.toInt16 ((4 : Int32)))))
              flags := t'177
            base := (16 : Int32)
            goto_ultoa := true
          else if sw'175 == (120 : Int32) then
            if ((UInt32.toInt32 (UInt16.toUInt32 (flags))) &&& (16 : Int32)) != (0 : Int32) then
              let t'178 := (flags ||| (Int16.toUInt16 (Int32.toInt16 ((4 : Int32)))))
              flags := t'178
            base := (16 : Int32)
            goto_ultoa := true
          else if sw'175 == (88 : Int32) then
            if ((UInt32.toInt32 (UInt16.toUInt32 (flags))) &&& (16 : Int32)) != (0 : Int32) then
              let t'179 := (flags ||| (Int16.toUInt16 (Int32.toInt16 (((4 : Int32) ||| (2 : Int32))))))
              flags := t'179
            let t'180 := ((16 : Int32) ||| (512 : Int32))
            base := t'180
            goto_ultoa := true
          else
            return ()
        if goto_ultoa then
          if ((UInt32.toInt32 (UInt16.toUInt32 (flags))) &&& (256 : Int32)) != (0 : Int32) then
            let t'181 ← PMem.ldU64 (fp + 0)
            let t'182 ← PMem.ldU64 t'181
            PMem.stU64 (fp + 0) (t'181 + 8)
            let t'183 ← ulltoa_invert t'182 (fp + 8) (Int8.toUInt8 (Int32.toInt8 (base)))
            let t'184 := Int8.toUInt8 (Int64.toInt8 (((t'183 - (fp + 8)).toInt64 / 1)))
            c := t'184
          else
            let mut c'185 : UInt64 := default
            if ((UInt32.toInt32 (UInt16.toUInt32 (flags))) &&& (128 : Int32)) != (0 : Int32) then
              let t'186 ← PMem.ldU64 (fp + 0)
              let t'187 ← PMem.ldU64 t'186
              PMem.stU64 (fp + 0) (t'186 + 8)
              c'185 := t'187
            else
              let t'188 ← PMem.ldU64 (fp + 0)
              let t'189 ← PMem.ldU32 t'188
              PMem.stU64 (fp + 0) (t'188 + 8)
              c'185 := UInt32.toUInt64 (t'189)
            let t'190 ← ultoa_invert (UInt64.toUInt32 (c'185)) (fp + 8) (Int8.toUInt8 (Int32.toInt8 (base)))
            let t'191 := Int8.toUInt8 (Int64.toInt8 (((t'190 - (fp + 8)).toInt64 / 1)))
            c := t'191
          let t'192 := (flags &&& (Int16.toUInt16 (Int32.toInt16 ((~~~(128 : Int32))))))
          flags := t'192
      let mut len : UInt8 := default  -- uninitialized in C
      len := c
      if ((UInt32.toInt32 (UInt16.toUInt32 (flags))) &&& (64 : Int32)) != (0 : Int32) then
        let t'193 := (flags &&& (Int16.toUInt16 (Int32.toInt16 ((~~~(1 : Int32))))))
        flags := t'193
        if (decide ((UInt32.toInt32 (UInt8.toUInt32 (len))) < (UInt32.toInt32 (UInt8.toUInt32 (prec))))) then
          len := prec
          if ((((UInt32.toInt32 (UInt16.toUInt32 (flags))) &&& (16 : Int32)) != (0 : Int32)) && (!(((UInt32.toInt32 (UInt16.toUInt32 (flags))) &&& (4 : Int32)) != (0 : Int32)))) then
            let t'194 := (flags &&& (Int16.toUInt16 (Int32.toInt16 ((~~~(16 : Int32))))))
            flags := t'194
      if ((UInt32.toInt32 (UInt16.toUInt32 (flags))) &&& (16 : Int32)) != (0 : Int32) then
        let t'195 ← PMem.ldU8 ((fp + 8) + ((Int32.toInt64 (((UInt32.toInt32 (UInt8.toUInt32 (c))) - (1 : Int32)))) * 1).toUInt64)
        if ((UInt32.toInt32 (UInt8.toUInt32 (t'195))) == (Int8.toInt32 ((48 : Int8)))) then
          let t'196 := (flags &&& (Int16.toUInt16 (Int32.toInt16 ((~~~(((16 : Int32) ||| (4 : Int32)) ||| (2 : Int32)))))))
          flags := t'196
        else
          let t'197 := (len + (Int8.toUInt8 (Int32.toInt8 ((1 : Int32)))))
          len := t'197
          if ((UInt32.toInt32 (UInt16.toUInt32 (flags))) &&& (4 : Int32)) != (0 : Int32) then
            let t'198 := (len + (Int8.toUInt8 (Int32.toInt8 ((1 : Int32)))))
            len := t'198
      else
        if ((UInt32.toInt32 (UInt16.toUInt32 (flags))) &&& (((128 : Int32) ||| (2 : Int32)) ||| (4 : Int32))) != (0 : Int32) then
          let t'199 := (len + (Int8.toUInt8 (Int32.toInt8 ((1 : Int32)))))
          len := t'199
      if !(((UInt32.toInt32 (UInt16.toUInt32 (flags))) &&& (8 : Int32)) != (0 : Int32)) then
        if ((UInt32.toInt32 (UInt16.toUInt32 (flags))) &&& (1 : Int32)) != (0 : Int32) then
          prec := c
          if (decide ((UInt32.toInt32 (UInt8.toUInt32 (len))) < (UInt32.toInt32 (UInt8.toUInt32 (width))))) then
            let t'200 := (prec + (Int8.toUInt8 (Int32.toInt8 (((UInt32.toInt32 (UInt8.toUInt32 (width))) - (UInt32.toInt32 (UInt8.toUInt32 (len))))))))
            prec := t'200
            len := width
        for _ in PMem.loopFuel do
          if !((decide ((UInt32.toInt32 (UInt8.toUInt32 (len))) < (UInt32.toInt32 (UInt8.toUInt32 (width)))))) then break
          let t'201 ← BufferPrinter.write s (Int8.toUInt8 ((32 : Int8)))
          discard <| pure (t'201)
          let t'202 := len
          let t'203 := (t'202 + 1)
          len := t'203
      let mut c'204 : Int32 := default
      if (decide ((UInt32.toInt32 (UInt8.toUInt32 (len))) < (UInt32.toInt32 (UInt8.toUInt32 (width))))) then
        c'204 := ((UInt32.toInt32 (UInt8.toUInt32 (width))) - (UInt32.toInt32 (UInt8.toUInt32 (len))))
      else
        c'204 := (0 : Int32)
      let t'205 := Int8.toUInt8 (Int32.toInt8 (c'204))
      width := t'205
      if ((UInt32.toInt32 (UInt16.toUInt32 (flags))) &&& (16 : Int32)) != (0 : Int32) then
        let t'206 ← BufferPrinter.write s (Int8.toUInt8 ((48 : Int8)))
        discard <| pure (t'206)
        if ((UInt32.toInt32 (UInt16.toUInt32 (flags))) &&& (4 : Int32)) != (0 : Int32) then
          let mut c'207 : Int8 := default
          if ((UInt32.toInt32 (UInt16.toUInt32 (flags))) &&& (2 : Int32)) != (0 : Int32) then
            c'207 := (88 : Int8)
          else
            c'207 := (120 : Int8)
          let t'208 ← BufferPrinter.write s (Int8.toUInt8 (c'207))
          discard <| pure (t'208)
      else
        if ((UInt32.toInt32 (UInt16.toUInt32 (flags))) &&& (((128 : Int32) ||| (2 : Int32)) ||| (4 : Int32))) != (0 : Int32) then
          let mut z : UInt8 := Int8.toUInt8 ((32 : Int8))
          if ((UInt32.toInt32 (UInt16.toUInt32 (flags))) &&& (2 : Int32)) != (0 : Int32) then
            let t'209 := Int8.toUInt8 ((43 : Int8))
            z := t'209
          if ((UInt32.toInt32 (UInt16.toUInt32 (flags))) &&& (128 : Int32)) != (0 : Int32) then
            let t'210 := Int8.toUInt8 ((45 : Int8))
            z := t'210
          let t'211 ← BufferPrinter.write s z
          discard <| pure (t'211)
      for _ in PMem.loopFuel do
        if !((decide ((UInt32.toInt32 (UInt8.toUInt32 (prec))) > (UInt32.toInt32 (UInt8.toUInt32 (c)))))) then break
        let t'212 ← BufferPrinter.write s (Int8.toUInt8 ((48 : Int8)))
        discard <| pure (t'212)
        let t'213 := prec
        let t'214 := (t'213 - 1)
        prec := t'214
      let mut first'215 := true
      for _ in PMem.loopFuel do
        if !first'215 then
          if !(c != (0 : UInt8)) then break
        first'215 := false
        let t'216 := (c - 1)
        c := t'216
        let t'217 ← PMem.ldU8 ((fp + 8) + ((UInt64.toInt64 (UInt8.toUInt64 (c))) * 1).toUInt64)
        let t'218 ← BufferPrinter.write s t'217
        discard <| pure (t'218)
    for _ in PMem.loopFuel do
      if !(width != (0 : UInt8)) then break
      let t'219 ← BufferPrinter.write s (Int8.toUInt8 ((32 : Int8)))
      discard <| pure (t'219)
      let t'220 := width
      let t'221 := (t'220 - 1)
      width := t'221
  return ()

def print_vprintf (s : UInt64) (fmt : UInt64) (ap : UInt64) : PMem.M Unit := do
  let fp ← PMem.enter 31
  let r ← print_vprintf.body fp s fmt ap
  PMem.leave fp
  return r

/-- C++ `Functor<void>::Functor : void (Functor<void> &&) noexcept`, `functor.h:?-?`. -/
def Functor'void.Functor'2 (this : UInt64) (arg : UInt64) : PMem.M Unit := do
  let t'1 ← PMem.ldU64 arg
  PMem.stU64 (this + 0) t'1
  let t'2 ← PMem.ldU64 (arg + 8)
  PMem.stU64 (this + 8) t'2
  return ()

/-- C++ `Functor<void, float *, unsigned char>::operator bool : bool () const`, `functor.h:69-72`. -/
def Functor'void_float_unsigned_char.operator_bool (this : UInt64) : PMem.M Bool := do
  let t'1 ← PMem.ldU64 (this + 8)
  return (t'1 != (0 : UInt64))

/-- C++ `ByteBuffer::advance : bool (uint32_t)`, `RingBuffer.cpp:137-144`. -/
def ByteBuffer.advance (this : UInt64) (n : UInt32) : PMem.M Bool := do
  let mut n := n
  let t'1 ← ByteBuffer.available this
  if (decide (n > t'1)) then
    return false
  let t'2 ← PMem.ldU32 (this + 12)
  let t'3 ← PMem.ldU32 (this + 8)
  let t'4 ← PMem.atomicStU32 (this + 12) ((t'2 + n) % t'3)
  discard <| pure (t'4)
  return true

/-- C++ `ByteBuffer::read : uint32_t (uint8_t *, uint32_t)`, `RingBuffer.cpp:240-245`. -/
def ByteBuffer.read (this : UInt64) (data : UInt64) (len : UInt32) : PMem.M UInt32 := do
  let mut data := data
  let mut len := len
  let t'1 ← ByteBuffer.peekbytes this data len
  let mut ret : UInt32 := t'1
  let t'2 ← ByteBuffer.advance this ret
  discard <| pure (t'2)
  return ret

/-- C++ `ByteBuffer::ByteBuffer : void (uint32_t)`, `RingBuffer.cpp:6-11`. -/
def ByteBuffer.ByteBuffer (this : UInt64) (_size : UInt32) : PMem.M Unit := do
  let mut _size := _size
  PMem.stU32 (this + 12) (Int32.toUInt32 ((0 : Int32)))
  PMem.stU32 (this + 16) (Int32.toUInt32 ((0 : Int32)))
  let t'1 ← PMem.calloc (Int64.toUInt64 (Int32.toInt64 ((1 : Int32)))) (UInt32.toUInt64 (_size))
  PMem.stU64 this t'1
  let t'2 ← PMem.ldU64 this
  let mut c'3 : UInt32 := default
  if (t'2 != 0) then
    c'3 := _size
  else
    c'3 := Int32.toUInt32 ((0 : Int32))
  PMem.stU32 (this + 8) c'3
  PMem.stB (this + 20) false
  return ()

/-- C++ `Functor<void>::Functor : void (const Functor<void> &) noexcept`, `functor.h:35-?`. -/
def Functor'void.Functor (this : UInt64) (arg : UInt64) : PMem.M Unit := do
  let t'1 ← PMem.ldU64 arg
  PMem.stU64 (this + 0) t'1
  let t'2 ← PMem.ldU64 (arg + 8)
  PMem.stU64 (this + 8) t'2
  return ()

/-- C++ `ExpectDelay::ExpectDelay : void (uint32_t)`, `Scheduler.cpp:30-33`. -/
def ExpectDelay.ExpectDelay (this : UInt64) (ms : UInt32) : PMem.M Unit := do
  let mut ms := ms
  let t'1 ← PMem.ldU64 ((0xba88 : UInt64) /- &hal -/ + 80)
  discard <| PMem.halDev "AP_HAL::Scheduler::expect_delay_ms" t'1 #[(UInt32.toUInt64 (ms))]
  return ()

/-- C++ `Functor<void>::method_wrapper : void (void *)`, `functor.h:85-89`. -/
def Functor'void.method_wrapper'AP_InertialSensor_periodic (obj : UInt64) : PMem.M Unit := do
  let mut obj := obj
  let mut t : UInt64 := obj
  VehicleBridge.AP_InertialSensor.periodic'0 t
  return ()

/-- C++ `Functor<void, const char *, const signed char>::Functor : void (const Functor<void, const char *, const signed char> &) noexcept`, `functor.h:?-?`. -/
def Functor'void_const_char_const_signed_char.Functor'2 (this : UInt64) (arg : UInt64) : PMem.M Unit := do
  let t'1 ← PMem.ldU64 arg
  PMem.stU64 (this + 0) t'1
  let t'2 ← PMem.ldU64 (arg + 8)
  PMem.stU64 (this + 8) t'2
  return ()

/-- C++ `Functor<void, const char *, const signed char>::Functor : void (Functor<void, const char *, const signed char> &&) noexcept`, `functor.h:?-?`. -/
def Functor'void_const_char_const_signed_char.Functor (this : UInt64) (arg : UInt64) : PMem.M Unit := do
  let t'1 ← PMem.ldU64 arg
  PMem.stU64 (this + 0) t'1
  let t'2 ← PMem.ldU64 (arg + 8)
  PMem.stU64 (this + 8) t'2
  return ()

/-- C++ `Functor<bool, const AP_Mission::Mission_Command &>::Functor : void (Functor<bool, const Mission_Command &> &&) noexcept`, `functor.h:?-?`. -/
def Functor'bool_const_AP_Mission_Mission_Command.Functor (this : UInt64) (arg : UInt64) : PMem.M Unit := do
  let t'1 ← PMem.ldU64 arg
  PMem.stU64 (this + 0) t'1
  let t'2 ← PMem.ldU64 (arg + 8)
  PMem.stU64 (this + 8) t'2
  return ()

end Vehicle_lib
