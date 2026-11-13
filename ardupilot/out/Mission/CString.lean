import CFloat

/-!
Written by hand for cpp2lean; copied by `cpp2lean.py` next to every translation made with
`--c-strings` or `--byte-objects` (`OutDir/CString.lean`), imported by those that use it. Do not edit
the copies.

C's bytes, strings and variadic arguments (README.md, "Phase 2b"). Memory of the model is bytes: a
`char[N]`, `unsigned char[N]` or `uint8_t[N]` object, a string literal (with its terminating zero),
and the object representation of a byte-level object are an `Array UInt8`; a pointer into one is
the array and an offset (`Nat`). C's `char` (signed on the reference target, `-fsigned-char`) is
stored as its byte; the translator converts a `char` value to a wider type through `UInt8.toInt8`
(sign extension), as C's integer promotion does.

The functions below are C's, on (array, offset) pairs, with C's results on every input where C
defines one. Where C's behavior is undefined they are total: a byte read outside the array is 0
(as if a terminator followed), a write outside it is dropped. `strcmp`, `strncmp`,
`strncasecmp` and `memcmp` return the difference of the first differing bytes as unsigned chars
(musl's and Apple's libc; C fixes only the sign); `strncasecmp` lowers ASCII letters only (the C
locale). Checked against the platform's C library by `difftest.py cstring` (README.md).
-/

open FloatLib.Floats

namespace CString

/-- The byte at index i, or 0 outside the array. -/
@[inline] def get (a : Array UInt8) (i : Nat) : UInt8 := a.getD i 0

/-- The array with byte i replaced by v (unchanged outside the array). -/
@[inline] def put (a : Array UInt8) (i : Nat) (v : UInt8) : Array UInt8 :=
  if h : i < a.size then a.set i v h else a

/-- C `strlen(a + o)`. -/
def strlen (a : Array UInt8) (o : Nat) : USize := Id.run do
  let mut n : Nat := 0
  for i in [o:a.size] do
    if a[i]! == 0 then return n.toUSize
    n := n + 1
  return n.toUSize

/-- C `strnlen(a + o, maxlen)`. -/
def strnlen (a : Array UInt8) (o : Nat) (maxlen : USize) : USize := Id.run do
  let m := maxlen.toNat
  let mut n : Nat := 0
  for i in [o:a.size] do
    if n ≥ m || a[i]! == 0 then return n.toUSize
    n := n + 1
  return (min n m).toUSize

/-- C `strncpy(d + dO, s + sO, n)`: the bytes of s up to its terminator, then zeros, n bytes in
all; returns d's array. -/
def strncpy (d : Array UInt8) (dO : Nat) (s : Array UInt8) (sO : Nat) (n : USize) : Array UInt8 := Id.run do
  let mut d := d
  let mut ended := false
  for i in [0:n.toNat] do
    let c := if ended then 0 else get s (sO + i)
    if c == 0 then ended := true
    d := put d (dO + i) c
  return d

/-- C `memcpy(d + dO, s + sO, n)` (the arrays are distinct Lean values: overlap does not arise). -/
def memcpy (d : Array UInt8) (dO : Nat) (s : Array UInt8) (sO : Nat) (n : USize) : Array UInt8 := Id.run do
  let mut d := d
  for i in [0:n.toNat] do
    d := put d (dO + i) (get s (sO + i))
  return d

/-- C `memset(d + dO, c, n)`: c converted to `unsigned char`. -/
def memset (d : Array UInt8) (dO : Nat) (c : Int32) (n : USize) : Array UInt8 := Id.run do
  let mut d := d
  for i in [0:n.toNat] do
    d := put d (dO + i) c.toUInt32.toUInt8
  return d

/-- The difference of two bytes as `unsigned char`s, as an `int`. -/
@[inline] def diff (x y : UInt8) : Int32 := x.toUInt32.toInt32 - y.toUInt32.toInt32

/-- C `memcmp(a + aO, b + bO, n)`. -/
def memcmp (a : Array UInt8) (aO : Nat) (b : Array UInt8) (bO : Nat) (n : USize) : Int32 := Id.run do
  for i in [0:n.toNat] do
    let x := get a (aO + i)
    let y := get b (bO + i)
    if x != y then return diff x y
  return 0

/-- C `strncmp(a + aO, b + bO, n)`. -/
def strncmp (a : Array UInt8) (aO : Nat) (b : Array UInt8) (bO : Nat) (n : USize) : Int32 := Id.run do
  for i in [0:n.toNat] do
    let x := get a (aO + i)
    let y := get b (bO + i)
    if x != y then return diff x y
    if x == 0 then return 0
  return 0

/-- C `strcmp(a + aO, b + bO)` (at most the bytes of a and one more). -/
def strcmp (a : Array UInt8) (aO : Nat) (b : Array UInt8) (bO : Nat) : Int32 :=
  strncmp a aO b bO (a.size + 1 - aO).toUSize

/-- ASCII `tolower` (the C locale). -/
@[inline] def lower (c : UInt8) : UInt8 := if 65 ≤ c && c ≤ 90 then c + 32 else c

/-- C `strncasecmp(a + aO, b + bO, n)` in the C locale. -/
def strncasecmp (a : Array UInt8) (aO : Nat) (b : Array UInt8) (bO : Nat) (n : USize) : Int32 := Id.run do
  for i in [0:n.toNat] do
    let x := lower (get a (aO + i))
    let y := lower (get b (bO + i))
    if x != y then return diff x y
    if x == 0 then return 0
  return 0

/-- C `strcasecmp`. -/
def strcasecmp (a : Array UInt8) (aO : Nat) (b : Array UInt8) (bO : Nat) : Int32 :=
  strncasecmp a aO b bO (a.size + 1 - aO).toUSize

/-! Object representations (byte-level objects, README.md "Phase 2b"): little-endian, as on the
reference target (arm64 and x86-64); a float's bytes are those of its bit pattern. -/

/-- The 2 bytes of v, least significant first. -/
def ofUInt16 (v : UInt16) : Array UInt8 := #[v.toUInt8, (v >>> 8).toUInt8]
/-- The 4 bytes of v, least significant first. -/
def ofUInt32 (v : UInt32) : Array UInt8 := #[v.toUInt8, (v >>> 8).toUInt8, (v >>> 16).toUInt8, (v >>> 24).toUInt8]
/-- The 8 bytes of v, least significant first. -/
def ofUInt64 (v : UInt64) : Array UInt8 := (ofUInt32 v.toUInt32) ++ (ofUInt32 (v >>> 32).toUInt32)
/-- The value of the 2 bytes at offset o, least significant first. -/
def toUInt16 (a : Array UInt8) (o : Nat) : UInt16 := (get a o).toUInt16 ||| ((get a (o + 1)).toUInt16 <<< 8)
/-- The value of the 4 bytes at offset o, least significant first. -/
def toUInt32 (a : Array UInt8) (o : Nat) : UInt32 :=
  (get a o).toUInt32 ||| ((get a (o + 1)).toUInt32 <<< 8) ||| ((get a (o + 2)).toUInt32 <<< 16) ||| ((get a (o + 3)).toUInt32 <<< 24)
/-- The value of the 8 bytes at offset o, least significant first. -/
def toUInt64 (a : Array UInt8) (o : Nat) : UInt64 := (toUInt32 a o).toUInt64 ||| ((toUInt32 a (o + 4)).toUInt64 <<< 32)
/-- The array with the bytes of piece written from offset o. -/
def write (a : Array UInt8) (o : Nat) (piece : Array UInt8) : Array UInt8 := Id.run do
  let mut a := a
  for i in [0:piece.size] do
    a := put a (o + i) piece[i]!
  return a
/-- The n bytes from offset o (zeros outside the array). -/
def slice (a : Array UInt8) (o n : Nat) : Array UInt8 := Id.run do
  let mut r : Array UInt8 := Array.replicate n 0
  for i in [0:n] do
    r := r.set! i (get a (o + i))
  return r

end CString

/-! Variadic arguments (README.md, "Phase 2b"). A call of a variadic function passes its variadic
arguments, after C's default argument promotions (clang's implicit casts: `float` to `double`,
narrow integers to `int`), as an array of slots; `va_list` is the array and the index of the next
slot. On the reference target (arm64 Apple: every variadic argument in its own 8-byte stack slot) an
integer slot holds the value sign-extended (signed types) or zero-extended (unsigned) to 64 bits, and
`va_arg(ap, T)` reads the slot's bits as T, so a mismatched `va_arg` (undefined in C) reads the
bits the target would; a pointer (`char *`, `%s`) is the array and offset. -/

/-- One variadic argument. -/
inductive CArg where
  | int (bits : UInt64)
  | dbl (v : Binary64)
  | ptr (a : Array UInt8) (o : Nat)
  deriving Inhabited

namespace CArg
/-- The slot's 64 bits. -/
def bits : CArg → UInt64
  | .int b => b
  | .dbl v => Binary64.toBits v
  | .ptr _ _ => 0
/-- An `int` argument (sign-extended). -/
@[inline] def ofInt32 (v : Int32) : CArg := .int v.toInt64.toUInt64
/-- An `unsigned int` argument (zero-extended). -/
@[inline] def ofUInt32 (v : UInt32) : CArg := .int v.toUInt64
/-- A `long`/`long long` argument. -/
@[inline] def ofInt64 (v : Int64) : CArg := .int v.toUInt64
/-- An `unsigned long`/`unsigned long long` argument. -/
@[inline] def ofUInt64 (v : UInt64) : CArg := .int v
end CArg

/-- C `va_list`: the variadic arguments of the call and the index of the next one. -/
structure VaList where
  args : Array CArg := #[]
  pos : Nat := 0
  deriving Inhabited

namespace VaList
/-- The next slot. -/
@[inline] def cur (ap : VaList) : CArg := ap.args.getD ap.pos (CArg.int 0)
/-- `ap` after one `va_arg`. -/
@[inline] def next (ap : VaList) : VaList := { ap with pos := ap.pos + 1 }
/-- `va_start`: the arguments of this call, from the first. -/
@[inline] def start (args : Array CArg) : VaList := { args := args, pos := 0 }
/-- `va_arg(ap, int)`. -/
@[inline] def argInt32 (ap : VaList) : Int32 := ap.cur.bits.toUInt32.toInt32
/-- `va_arg(ap, unsigned int)`. -/
@[inline] def argUInt32 (ap : VaList) : UInt32 := ap.cur.bits.toUInt32
/-- `va_arg(ap, long)`, `va_arg(ap, long long)`. -/
@[inline] def argInt64 (ap : VaList) : Int64 := ap.cur.bits.toInt64
/-- `va_arg(ap, unsigned long)`, `va_arg(ap, unsigned long long)`. -/
@[inline] def argUInt64 (ap : VaList) : UInt64 := ap.cur.bits
/-- `va_arg(ap, double)`. -/
@[inline] def argBinary64 (ap : VaList) : Binary64 := Binary64.ofBits ap.cur.bits
/-- `va_arg(ap, char *)`: the array and offset (an empty string for a slot that holds no pointer). -/
@[inline] def argPtr (ap : VaList) : Array UInt8 × Nat :=
  match ap.cur with
  | .ptr a o => (a, o)
  | _ => (#[0], 0)
end VaList

/-! The HAL storage (`hal.storage`, `--hal-storage`; README.md, "Phase 2b"): the boundary of
StorageManager. Its contents are a byte array of HAL_STORAGE_SIZE that the translated functions
thread through (`hal'storage`). The two operations are those of the reference vehicle's lock-step
HAL (reference/hal/lockstep.cpp, `class Storage`): a block that does not fit in the storage is not
transferred (the destination is unchanged), else the bytes are copied. -/

namespace HalStorage
/-- `hal.storage->read_block(dst + dO, src, n)`: dst after the read. -/
def read_block (st : Array UInt8) (dst : Array UInt8) (dO : Nat) (src : UInt16) (n : USize) : Array UInt8 :=
  if src.toNat + n.toNat > st.size then dst else CString.memcpy dst dO st src.toNat n
/-- `hal.storage->write_block(dst, src + sO, n)`: the storage after the write. -/
def write_block (st : Array UInt8) (dst : UInt16) (src : Array UInt8) (sO : Nat) (n : USize) : Array UInt8 :=
  if dst.toNat + n.toNat > st.size then st else CString.memcpy st dst.toNat src sO n
end HalStorage
