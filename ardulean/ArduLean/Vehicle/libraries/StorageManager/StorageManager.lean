import ArduLean.Runtime.Memory
import ArduLean.Vehicle.libraries.AP_Math.AP_Math
import ArduLean.Vehicle.libraries.AP_HAL.AP_HAL

/-!
ArduPilot `libraries/StorageManager`. Sources: `libraries/StorageManager/StorageManager.cpp`, `libraries/StorageManager/StorageManager.h`.

Items of `lean/Vehicle_lib.lean` (the vehicle translation), unchanged; placed by `tools/split_modules.py` (`ArduLean/Vehicle/INDEX.md`).
-/

open FloatLib.Floats (Binary32 Binary64)

set_option linter.unusedVariables false
set_option linter.unreachableTactic false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false

namespace Vehicle_lib

/-- C++ `StorageAccess::read_block : bool (void *, uint16_t, size_t) const`, `StorageManager.cpp:139-186`. -/
def StorageAccess.read_block.body (fp : UInt64) (this : UInt64) (data : UInt64) (addr : UInt16) (n : UInt64) : PMem.M Bool := do
  let mut data := data
  let mut addr := addr
  PMem.stU64 (fp + 0) n
  let mut b : UInt64 := data
  let t'1 ← PMem.ldU64 (this + 8)
  if (t'1 != (0 : UInt64)) then
    let t'2 ← PMem.ldU64 (this + 8)
    let t'3 ← PMem.ldU32 (t'2 + 24)
    if (decide ((UInt16.toUInt32 (addr)) > t'3)) then
      return false
    let t'4 ← PMem.ldU64 (this + 8)
    let t'5 ← PMem.ldU32 (t'4 + 24)
    PMem.stU32 (fp + 8) (t'5 - (UInt16.toUInt32 (addr)))
    let t'6 ← MIN'unsigned_long_unsigned_int (fp + 0) (fp + 8)
    let mut n2 : UInt64 := t'6
    let t'7 ← PMem.ldU64 (this + 8)
    let t'8 ← PMem.ldU64 (t'7 + 16)
    let t'9 ← PMem.memcpy b (t'8 + ((UInt64.toInt64 (UInt16.toUInt64 (addr))) * 1).toUInt64) n2
    discard <| pure (t'9)
    let t'10 ← PMem.ldU64 (fp + 0)
    return (t'10 == n2)
  for i'11 in [0:15] do
    let i : UInt8 := UInt8.ofNat i'11
    let area : UInt64 := ((0xbbc8 : UInt64) /- &StorageManager::layout -/ + ((UInt64.toInt64 (UInt8.toUInt64 (i))) * 8).toUInt64)
    let t'12 ← PMem.ldU16 (area + 6)
    let mut length : UInt16 := t'12
    let t'13 ← PMem.ldU16 (area + 4)
    let mut offset : UInt16 := t'13
    let t'14 ← PMem.ldU32 area
    let t'15 ← PMem.ldU32 this
    if ((UInt32.toInt32 (t'14)) != (UInt32.toInt32 (t'15))) then
      continue
    if (decide ((UInt32.toInt32 (UInt16.toUInt32 (addr))) ≥ (UInt32.toInt32 (UInt16.toUInt32 (length))))) then
      let t'16 := (addr - (Int16.toUInt16 (Int32.toInt16 ((UInt32.toInt32 (UInt16.toUInt32 (length)))))))
      addr := t'16
      continue
    let t'17 ← PMem.ldU64 (fp + 0)
    let mut count : UInt16 := UInt64.toUInt16 (t'17)
    if (decide (((UInt32.toInt32 (UInt16.toUInt32 (count))) + (UInt32.toInt32 (UInt16.toUInt32 (addr)))) > (UInt32.toInt32 (UInt16.toUInt32 (length))))) then
      let t'18 := Int16.toUInt16 (Int32.toInt16 (((UInt32.toInt32 (UInt16.toUInt32 (length))) - (UInt32.toInt32 (UInt16.toUInt32 (addr))))))
      count := t'18
    PMem.halRead b (Int16.toUInt16 (Int32.toInt16 (((UInt32.toInt32 (UInt16.toUInt32 (addr))) + (UInt32.toInt32 (UInt16.toUInt32 (offset))))))) (UInt16.toUInt64 (count))
    let t'19 ← PMem.ldU64 (fp + 0)
    let t'20 := (t'19 - (UInt16.toUInt64 (count)))
    PMem.stU64 (fp + 0) t'20
    let t'21 ← PMem.ldU64 (fp + 0)
    if (t'21 == (Int64.toUInt64 (Int32.toInt64 ((0 : Int32))))) then
      break
    let t'22 := (b + ((Int32.toInt64 ((UInt32.toInt32 (UInt16.toUInt32 (count))))) * 1).toUInt64)
    b := t'22
    let t'23 := Int16.toUInt16 (Int32.toInt16 ((0 : Int32)))
    addr := t'23
  let t'24 ← PMem.ldU64 (fp + 0)
  return (t'24 == (Int64.toUInt64 (Int32.toInt64 ((0 : Int32)))))

def StorageAccess.read_block (this : UInt64) (data : UInt64) (addr : UInt16) (n : UInt64) : PMem.M Bool := do
  let fp ← PMem.enter 12
  let r ← StorageAccess.read_block.body fp this data addr n
  PMem.leave fp
  return r

/-- C++ `StorageAccess::size : uint16_t () const`, `StorageManager.h:97-?`. -/
def StorageAccess.size (this : UInt64) : PMem.M UInt16 := do
  let t'1 ← PMem.ldU16 (this + 4)
  return t'1

/-- C++ `StorageAccess::write_block : bool (uint16_t, const void *, size_t) const`, `StorageManager.cpp:193-244`. -/
def StorageAccess.write_block.body (fp : UInt64) (this : UInt64) (addr : UInt16) (data : UInt64) (n : UInt64) : PMem.M Bool := do
  let mut addr := addr
  let mut data := data
  PMem.stU64 (fp + 0) n
  let mut b : UInt64 := data
  let t'1 ← PMem.ldU64 (this + 8)
  if (t'1 != (0 : UInt64)) then
    let t'2 ← PMem.ldU64 (this + 8)
    let t'3 ← PMem.ldU32 (t'2 + 24)
    if (decide ((UInt16.toUInt32 (addr)) > t'3)) then
      return false
    let t'4 ← PMem.ldU64 (this + 8)
    let t'5 ← PMem.ldU32 (t'4 + 24)
    PMem.stU32 (fp + 8) (t'5 - (UInt16.toUInt32 (addr)))
    let t'6 ← MIN'unsigned_long_unsigned_int (fp + 0) (fp + 8)
    let mut n2 : UInt64 := t'6
    let t'7 ← PMem.ldU64 (this + 8)
    let t'8 ← PMem.ldU64 (t'7 + 16)
    let t'9 ← PMem.memcpy (t'8 + ((UInt64.toInt64 (UInt16.toUInt64 (addr))) * 1).toUInt64) b n2
    discard <| pure (t'9)
    let mut i : UInt8 := UInt32.toUInt8 (((UInt16.toUInt32 (addr)) / (1024 : UInt32)))
    let mut first'10 := true
    for _ in PMem.loopFuel do
      if !first'10 then
        let t'11 := i
        let t'12 := (t'11 + 1)
        i := t'12
        pure ()
      first'10 := false
      if !((decide ((UInt8.toUInt64 (i)) < ((((UInt16.toUInt64 (addr)) + n2) + (UInt32.toUInt64 ((1023 : UInt32)))) / (UInt32.toUInt64 ((1024 : UInt32))))))) then break
      let t'13 ← PMem.ldU64 (this + 8)
      let t'14 := (t'13 + 40)
      let t'15 ← PMem.ldU64 t'14
      let t'16 := (t'15 ||| ((1 : UInt64) <<< (Int64.toUInt64 (Int32.toInt64 ((UInt32.toInt32 (UInt8.toUInt32 (i))))))))
      PMem.stU64 t'14 t'16
    let t'17 ← PMem.ldU64 (fp + 0)
    return (t'17 == n2)
  for i'2'18 in [0:15] do
    let i'2 : UInt8 := UInt8.ofNat i'2'18
    let area : UInt64 := ((0xbbc8 : UInt64) /- &StorageManager::layout -/ + ((UInt64.toInt64 (UInt8.toUInt64 (i'2))) * 8).toUInt64)
    let t'19 ← PMem.ldU16 (area + 6)
    let mut length : UInt16 := t'19
    let t'20 ← PMem.ldU16 (area + 4)
    let mut offset : UInt16 := t'20
    let t'21 ← PMem.ldU32 area
    let t'22 ← PMem.ldU32 this
    if ((UInt32.toInt32 (t'21)) != (UInt32.toInt32 (t'22))) then
      continue
    if (decide ((UInt32.toInt32 (UInt16.toUInt32 (addr))) ≥ (UInt32.toInt32 (UInt16.toUInt32 (length))))) then
      let t'23 := (addr - (Int16.toUInt16 (Int32.toInt16 ((UInt32.toInt32 (UInt16.toUInt32 (length)))))))
      addr := t'23
      continue
    let t'24 ← PMem.ldU64 (fp + 0)
    let mut count : UInt16 := UInt64.toUInt16 (t'24)
    if (decide (((UInt32.toInt32 (UInt16.toUInt32 (count))) + (UInt32.toInt32 (UInt16.toUInt32 (addr)))) > (UInt32.toInt32 (UInt16.toUInt32 (length))))) then
      let t'25 := Int16.toUInt16 (Int32.toInt16 (((UInt32.toInt32 (UInt16.toUInt32 (length))) - (UInt32.toInt32 (UInt16.toUInt32 (addr))))))
      count := t'25
    PMem.halWrite (Int16.toUInt16 (Int32.toInt16 (((UInt32.toInt32 (UInt16.toUInt32 (addr))) + (UInt32.toInt32 (UInt16.toUInt32 (offset))))))) b (UInt16.toUInt64 (count))
    let t'26 ← PMem.ldU64 (fp + 0)
    let t'27 := (t'26 - (UInt16.toUInt64 (count)))
    PMem.stU64 (fp + 0) t'27
    let t'28 ← PMem.ldU64 (fp + 0)
    if (t'28 == (Int64.toUInt64 (Int32.toInt64 ((0 : Int32))))) then
      break
    let t'29 := (b + ((Int32.toInt64 ((UInt32.toInt32 (UInt16.toUInt32 (count))))) * 1).toUInt64)
    b := t'29
    let t'30 := Int16.toUInt16 (Int32.toInt16 ((0 : Int32)))
    addr := t'30
  let t'31 ← PMem.ldU64 (fp + 0)
  return (t'31 == (Int64.toUInt64 (Int32.toInt64 ((0 : Int32)))))

def StorageAccess.write_block (this : UInt64) (addr : UInt16) (data : UInt64) (n : UInt64) : PMem.M Bool := do
  let fp ← PMem.enter 12
  let r ← StorageAccess.write_block.body fp this addr data n
  PMem.leave fp
  return r

/-- C++ `StorageAccess::StorageAccess : void (StorageManager::StorageType)`, `StorageManager.cpp:119-133`. -/
def StorageAccess.StorageAccess (this : UInt64) (_type : UInt32) : PMem.M Unit := do
  let mut _type := _type
  PMem.stU32 (this + 0) _type
  let t'1 := Int16.toUInt16 (Int32.toInt16 ((0 : Int32)))
  PMem.stU16 (this + 4) t'1
  PMem.stU64 (this + 8) (0 : UInt64)
  for i'2 in [0:15] do
    let i : UInt8 := UInt8.ofNat i'2
    let area : UInt64 := ((0xbbc8 : UInt64) /- &StorageManager::layout -/ + ((UInt64.toInt64 (UInt8.toUInt64 (i))) * 8).toUInt64)
    let t'3 ← PMem.ldU32 area
    let t'4 ← PMem.ldU32 this
    if ((UInt32.toInt32 (t'3)) == (UInt32.toInt32 (t'4))) then
      let t'5 := (this + 4)
      let t'6 ← PMem.ldU16 t'5
      let t'7 ← PMem.ldU16 (area + 6)
      let t'8 := (t'6 + (Int16.toUInt16 (Int32.toInt16 ((UInt32.toInt32 (UInt16.toUInt32 (t'7)))))))
      PMem.stU16 t'5 t'8
  return ()

/-- C++ `StorageManager::erase : void ()`, `StorageManager.cpp:109-114`. -/
def StorageManager.erase  : PMem.M Unit := do
  let t'1 ← AP_HAL.Storage.erase (0 : UInt64)
  if !t'1 then
    pure ()
  return ()

/-- C++ `StorageAccess::write_byte : void (uint16_t, uint8_t) const`, `StorageManager.cpp:289-292`. -/
def StorageAccess.write_byte.body (fp : UInt64) (this : UInt64) (loc : UInt16) (value : UInt8) : PMem.M Unit := do
  let mut loc := loc
  PMem.stU8 (fp + 0) value
  let t'1 ← StorageAccess.write_block this loc (fp + 0) (1 : UInt64)
  discard <| pure (t'1)
  return ()

def StorageAccess.write_byte (this : UInt64) (loc : UInt16) (value : UInt8) : PMem.M Unit := do
  let fp ← PMem.enter 1
  let r ← StorageAccess.write_byte.body fp this loc value
  PMem.leave fp
  return r

/-- C++ `StorageAccess::write_uint16 : void (uint16_t, uint16_t) const`, `StorageManager.cpp:297-300`. -/
def StorageAccess.write_uint16.body (fp : UInt64) (this : UInt64) (loc : UInt16) (value : UInt16) : PMem.M Unit := do
  let mut loc := loc
  PMem.stU16 (fp + 0) value
  let t'1 ← StorageAccess.write_block this loc (fp + 0) (2 : UInt64)
  discard <| pure (t'1)
  return ()

def StorageAccess.write_uint16 (this : UInt64) (loc : UInt16) (value : UInt16) : PMem.M Unit := do
  let fp ← PMem.enter 2
  let r ← StorageAccess.write_uint16.body fp this loc value
  PMem.leave fp
  return r

/-- C++ `StorageAccess::read_byte : uint8_t (uint16_t) const`, `StorageManager.cpp:249-254`. -/
def StorageAccess.read_byte.body (fp : UInt64) (this : UInt64) (loc : UInt16) : PMem.M UInt8 := do
  let mut loc := loc
  let t'1 ← StorageAccess.read_block this (fp + 0) loc (1 : UInt64)
  discard <| pure (t'1)
  let t'2 ← PMem.ldU8 (fp + 0)
  return t'2

def StorageAccess.read_byte (this : UInt64) (loc : UInt16) : PMem.M UInt8 := do
  let fp ← PMem.enter 1
  let r ← StorageAccess.read_byte.body fp this loc
  PMem.leave fp
  return r

/-- C++ `StorageAccess::read_uint16 : uint16_t (uint16_t) const`, `StorageManager.cpp:259-264`. -/
def StorageAccess.read_uint16.body (fp : UInt64) (this : UInt64) (loc : UInt16) : PMem.M UInt16 := do
  let mut loc := loc
  let t'1 ← StorageAccess.read_block this (fp + 0) loc (2 : UInt64)
  discard <| pure (t'1)
  let t'2 ← PMem.ldU16 (fp + 0)
  return t'2

def StorageAccess.read_uint16 (this : UInt64) (loc : UInt16) : PMem.M UInt16 := do
  let fp ← PMem.enter 2
  let r ← StorageAccess.read_uint16.body fp this loc
  PMem.leave fp
  return r

/-- C++ `StorageManager::storage_failed : bool ()`, `StorageManager.h:68-70`. -/
def StorageManager.storage_failed  : PMem.M Bool := do
  let t'1 ← PMem.ldB (0x131e8 : UInt64) /- &StorageManager::last_io_failed -/
  return t'1

/-- C++ `StorageAccess::read_uint32 : uint32_t (uint16_t) const`, `StorageManager.cpp:269-274`. -/
def StorageAccess.read_uint32.body (fp : UInt64) (this : UInt64) (loc : UInt16) : PMem.M UInt32 := do
  let mut loc := loc
  let t'1 ← StorageAccess.read_block this (fp + 0) loc (4 : UInt64)
  discard <| pure (t'1)
  let t'2 ← PMem.ldU32 (fp + 0)
  return t'2

def StorageAccess.read_uint32 (this : UInt64) (loc : UInt16) : PMem.M UInt32 := do
  let fp ← PMem.enter 4
  let r ← StorageAccess.read_uint32.body fp this loc
  PMem.leave fp
  return r

/-- C++ `StorageAccess::write_uint32 : void (uint16_t, uint32_t) const`, `StorageManager.cpp:305-308`. -/
def StorageAccess.write_uint32.body (fp : UInt64) (this : UInt64) (loc : UInt16) (value : UInt32) : PMem.M Unit := do
  let mut loc := loc
  PMem.stU32 (fp + 0) value
  let t'1 ← StorageAccess.write_block this loc (fp + 0) (4 : UInt64)
  discard <| pure (t'1)
  return ()

def StorageAccess.write_uint32 (this : UInt64) (loc : UInt16) (value : UInt32) : PMem.M Unit := do
  let fp ← PMem.enter 4
  let r ← StorageAccess.write_uint32.body fp this loc value
  PMem.leave fp
  return r

end Vehicle_lib
