import CFloat

/-!
Written by hand for cpp2lean; copied by `cpp2lean.py --param-memory` next to the translation
(`OutDir/ParamMemory.lean`). Do not edit the copies.

The memory of `--param-memory` (README.md, "Phase 4: AP_Param"): AP_Param treats parameters as raw
memory (`var_info` holds addresses and `offsetof` offsets, the code computes `base + offset`, casts to
`AP_Float *` and reads storage blocks straight into objects), so the translation of such code works on
one byte array, the address space of the objects it can reach: the parameter tables and their strings
(constant data), the static objects they point into (`copter`, `AP_AHRS_NavEKF3::EKF3`, ...), AP_Param's
static members, a heap for `new` and a stack for the locals whose address the code takes (and every
local struct or array). An address is a `UInt64` (C's pointers and `ptrdiff_t` on the 64-bit target); a
read or write of a scalar is its little-endian bytes at that address, a float its bit pattern
(`Binary32.toBits`/`ofBits`), a bit-field its bits by shift and mask. This file is the memory and the C
library functions the code calls on it; it holds no parameter logic (every function of AP_Param is
translated from ArduPilot). The HAL storage (`hal.storage`, `HAL_STORAGE_SIZE` bytes) is a second byte
array with lockstep.cpp's semantics (a block that does not fit is not transferred), as `--hal-storage`.
A read outside the memory gives 0 and a write outside it is dropped (C's behaviour there is undefined).
-/

open FloatLib.Floats (Binary32 Binary64)

namespace PMem

structure Mem where
  /-- the address space -/
  m : ByteArray
  /-- the stack pointer (the stack grows up from `stackBase`) -/
  sp : UInt64
  /-- the next free heap address -/
  hp : UInt64
  /-- the HAL storage -/
  st : ByteArray
  /-- boundary answers of the HAL (`hal.scheduler->is_system_initialized()`, `hal.util->get_soft_armed()`) -/
  sysInit : Bool := false
  armed : Bool := false
  /-- (the GCS translation, `support/GCSMemory.lean`) the HAL clock in µs, SERIAL0's receive queue and read
  position and its transmit bytes since the last output line, the boundary's records -/
  clockUs : UInt64 := 0
  rx : ByteArray := ByteArray.empty
  rxPos : Nat := 0
  tx : ByteArray := ByteArray.empty
  unreached : Array String := #[]
  frames : Array (UInt32 × Array ByteArray) := #[]
  framePos : Array Nat := #[]
  seqAddr : UInt64 := 0
  log : Array String := #[]
  answers : Array (String × Array UInt64) := #[]
  answerPos : Array Nat := #[]
  inDelayCb : Bool := false
  homeAddr : UInt64 := 0
  textQuota : Nat := 0
  timeAvail : UInt16 := 0xffff
  delayMarks : Array (Nat × UInt32) := #[]
  bfAt : Array Nat := #[]
  curStep : Nat := 0
  chan0 : UInt64 := 0

instance : Inhabited Mem := ⟨{ m := ByteArray.empty, sp := 0, hp := 0, st := ByteArray.empty }⟩

abbrev M := StateM Mem

@[inline] def rd (a : UInt64) : M UInt8 := do
  let s ← get
  return s.m.get! a.toNat

@[inline] def wr (a : UInt64) (v : UInt8) : M Unit :=
  modify fun s => if a.toNat < s.m.size then { s with m := s.m.set! a.toNat v } else s

@[inline] def ldU8 (a : UInt64) : M UInt8 := rd a
@[inline] def ldU16 (a : UInt64) : M UInt16 := do
  let s ← get
  let b := s.m
  let i := a.toNat
  return (b.get! i).toUInt16 ||| ((b.get! (i + 1)).toUInt16 <<< 8)
@[inline] def ldU32 (a : UInt64) : M UInt32 := do
  let s ← get
  let b := s.m
  let i := a.toNat
  return (b.get! i).toUInt32 ||| ((b.get! (i + 1)).toUInt32 <<< 8) ||| ((b.get! (i + 2)).toUInt32 <<< 16) ||| ((b.get! (i + 3)).toUInt32 <<< 24)
@[inline] def ldU64 (a : UInt64) : M UInt64 := do
  let lo ← ldU32 a
  let hi ← ldU32 (a + 4)
  return lo.toUInt64 ||| (hi.toUInt64 <<< 32)
@[inline] def ldI8 (a : UInt64) : M Int8 := return (← ldU8 a).toInt8
@[inline] def ldI16 (a : UInt64) : M Int16 := return (← ldU16 a).toInt16
@[inline] def ldI32 (a : UInt64) : M Int32 := return (← ldU32 a).toInt32
@[inline] def ldI64 (a : UInt64) : M Int64 := return (← ldU64 a).toInt64
@[inline] def ldF32 (a : UInt64) : M Binary32 := return Binary32.ofBits (← ldU32 a)
@[inline] def ldF64 (a : UInt64) : M Binary64 := return Binary64.ofBits (← ldU64 a)
@[inline] def ldB (a : UInt64) : M Bool := return (← ldU8 a) != 0

@[inline] def stU8 (a : UInt64) (v : UInt8) : M Unit := wr a v
@[inline] def stU16 (a : UInt64) (v : UInt16) : M Unit := do
  wr a v.toUInt8; wr (a + 1) (v >>> 8).toUInt8
@[inline] def stU32 (a : UInt64) (v : UInt32) : M Unit := do
  wr a v.toUInt8; wr (a + 1) (v >>> 8).toUInt8; wr (a + 2) (v >>> 16).toUInt8; wr (a + 3) (v >>> 24).toUInt8
@[inline] def stU64 (a : UInt64) (v : UInt64) : M Unit := do
  stU32 a v.toUInt32; stU32 (a + 4) (v >>> 32).toUInt32
@[inline] def stI8 (a : UInt64) (v : Int8) : M Unit := stU8 a v.toUInt8
@[inline] def stI16 (a : UInt64) (v : Int16) : M Unit := stU16 a v.toUInt16
@[inline] def stI32 (a : UInt64) (v : Int32) : M Unit := stU32 a v.toUInt32
@[inline] def stI64 (a : UInt64) (v : Int64) : M Unit := stU64 a v.toUInt64
@[inline] def stF32 (a : UInt64) (v : Binary32) : M Unit := stU32 a (Binary32.toBits v)
@[inline] def stF64 (a : UInt64) (v : Binary64) : M Unit := stU64 a (Binary64.toBits v)
@[inline] def stB (a : UInt64) (v : Bool) : M Unit := stU8 a (if v then 1 else 0)

/-- The `w` bits from bit `o` of the bytes at `a` (bit-fields: bits from the least significant of the
first byte, as clang's record layout numbers them on the little-endian target). -/
def ldBits (a : UInt64) (o w : Nat) : M UInt64 := do
  let mut v : Nat := 0
  for k in [0:w] do
    let bit := o + k
    let byte ← rd (a + (bit / 8).toUInt64)
    if (byte.toNat >>> (bit % 8)) % 2 == 1 then
      v := v ||| (1 <<< k)
  return v.toUInt64

/-- Store the low `w` bits of `v` at bit `o` of the bytes at `a`, the other bits unchanged. -/
def stBits (a : UInt64) (o w : Nat) (v : UInt64) : M Unit := do
  for k in [0:w] do
    let bit := o + k
    let ad := a + (bit / 8).toUInt64
    let byte ← rd ad
    let mask : UInt8 := (1 : UInt8) <<< (bit % 8).toUInt8
    let b := if (v.toNat >>> k) % 2 == 1 then byte ||| mask else byte &&& ~~~mask
    wr ad b

/-- A stack frame of `n` bytes, zeroed (C leaves locals uninitialized; the code reads none before
writing it); returns its address. -/
def enter (n : Nat) : M UInt64 := do
  let s ← get
  let base := s.sp
  let n' := (n + 15) / 16 * 16
  set { s with sp := base + n'.toUInt64 }
  for k in [0:n'] do
    wr (base + k.toUInt64) 0
  return base

def leave (base : UInt64) : M Unit := modify fun s => { s with sp := base }

/-- `new T` / `calloc`: `n` bytes of the heap, zeroed, aligned to 16. -/
def alloc (n : Nat) : M UInt64 := do
  let s ← get
  let base := s.hp
  set { s with hp := base + ((n + 15) / 16 * 16).toUInt64 }
  for k in [0:n] do
    wr (base + k.toUInt64) 0
  return base

/-! The C library on the memory (C's semantics; the comparisons return the difference of the first
differing bytes as `unsigned char`s, as the platform's library does, checked by `difftest.py cstring`
for `CString.lean`'s versions of them). -/

def memcpy (d s : UInt64) (n : UInt64) : M UInt64 := do
  for k in [0:n.toNat] do
    wr (d + k.toUInt64) (← rd (s + k.toUInt64))
  return d

def memset (d : UInt64) (c : Int32) (n : UInt64) : M UInt64 := do
  for k in [0:n.toNat] do
    wr (d + k.toUInt64) c.toUInt32.toUInt8
  return d

def strlen (a : UInt64) : M UInt64 := do
  let mut n : UInt64 := 0
  while (← rd (a + n)) != 0 do
    n := n + 1
  return n

def strnlen (a : UInt64) (maxlen : UInt64) : M UInt64 := do
  let mut n : UInt64 := 0
  while n < maxlen && (← rd (a + n)) != 0 do
    n := n + 1
  return n

def strncpy (d s : UInt64) (n : UInt64) : M UInt64 := do
  let mut ended := false
  for k in [0:n.toNat] do
    if ended then
      wr (d + k.toUInt64) 0
    else
      let c ← rd (s + k.toUInt64)
      wr (d + k.toUInt64) c
      if c == 0 then ended := true
  return d

@[inline] def diff (x y : UInt8) : Int32 := x.toUInt32.toInt32 - y.toUInt32.toInt32
@[inline] def lower (c : UInt8) : UInt8 := if 65 ≤ c && c ≤ 90 then c + 32 else c

def strncmpGen (f : UInt8 → UInt8) (a b : UInt64) (n : UInt64) : M Int32 := do
  for k in [0:n.toNat] do
    let x := f (← rd (a + k.toUInt64))
    let y := f (← rd (b + k.toUInt64))
    if x != y then return diff x y
    if x == 0 then return 0
  return 0

def strncmp (a b : UInt64) (n : UInt64) : M Int32 := strncmpGen id a b n
def strcmp (a b : UInt64) : M Int32 := strncmpGen id a b (UInt64.ofNat (2 ^ 63))
def strncasecmp (a b : UInt64) (n : UInt64) : M Int32 := strncmpGen lower a b n
def strcasecmp (a b : UInt64) : M Int32 := strncmpGen lower a b (UInt64.ofNat (2 ^ 63))

def memcmp (a b : UInt64) (n : UInt64) : M Int32 := do
  for k in [0:n.toNat] do
    let x ← rd (a + k.toUInt64)
    let y ← rd (b + k.toUInt64)
    if x != y then return diff x y
  return 0

/-! The HAL storage (reference/hal/lockstep.cpp, `class Storage`). -/

def halRead (dst : UInt64) (src : UInt16) (n : UInt64) : M Unit := do
  let s ← get
  if src.toNat + n.toNat > s.st.size then return
  for k in [0:n.toNat] do
    wr (dst + k.toUInt64) (s.st.get! (src.toNat + k))

def halWrite (dst : UInt16) (src : UInt64) (n : UInt64) : M Unit := do
  let s0 ← get
  if dst.toNat + n.toNat > s0.st.size then return
  for k in [0:n.toNat] do
    let c ← rd (src + k.toUInt64)
    modify fun s => { s with st := s.st.set! (dst.toNat + k) c }

/-- Place constant data (a hex string of bytes) at an address. -/
def place (a : UInt64) (hex : String) : M Unit := do
  let digit (c : Char) : Nat := if c.isDigit then c.toNat - '0'.toNat else c.toNat - 'a'.toNat + 10
  let cs := hex.toList.toArray
  for k in [0:cs.size / 2] do
    wr (a + k.toUInt64) (UInt8.ofNat (digit cs[2 * k]! * 16 + digit cs[2 * k + 1]!))

/-- A fresh memory of `size` bytes, the stack from `stackBase`, the heap from `heapBase`, and the HAL
storage `st`. -/
def fresh (size stackBase heapBase : Nat) (st : ByteArray) : Mem :=
  { m := ByteArray.mk (Array.replicate size 0), sp := stackBase.toUInt64, hp := heapBase.toUInt64, st := st }

end PMem
