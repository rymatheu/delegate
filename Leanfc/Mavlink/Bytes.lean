import Leanfc.Scalar

/-!
# Bytes

Little-endian reading and writing of MAVLink payload fields, total by construction: a read past the
end of the array gives zero bytes, which is MAVLink 2's zero extension of truncated payloads, and
writes append to a `ByteArray`. Floats are binary32 by their bit pattern
(`ExecFloat.Binary.ofBits32`/`toBits32`), never through `Float`. Used by the generated
`Messages.lean` and by `Frame.lean`.
-/

namespace Mavlink.Bytes

open FloatLib.Floats

/-- The byte at `i`, zero past the end. -/
def at_ (b : ByteArray) (i : Nat) : UInt8 := if h : i < b.size then b[i] else 0

def u8 (b : ByteArray) (o : Nat) : UInt8 := at_ b o
def u16 (b : ByteArray) (o : Nat) : UInt16 := (at_ b o).toUInt16 ||| ((at_ b (o + 1)).toUInt16 <<< 8)
def u32 (b : ByteArray) (o : Nat) : UInt32 := (u16 b o).toUInt32 ||| ((u16 b (o + 2)).toUInt32 <<< 16)
def u64 (b : ByteArray) (o : Nat) : UInt64 := (u32 b o).toUInt64 ||| ((u32 b (o + 4)).toUInt64 <<< 32)
def i8 (b : ByteArray) (o : Nat) : Int8 := (u8 b o).toInt8
def i16 (b : ByteArray) (o : Nat) : Int16 := (u16 b o).toInt16
def i32 (b : ByteArray) (o : Nat) : Int32 := (u32 b o).toInt32
def i64 (b : ByteArray) (o : Nat) : Int64 := (u64 b o).toInt64
def f32 (b : ByteArray) (o : Nat) : R := ExecFloat.Binary.ofBits32 (u32 b o)

/-- `n` bytes from `o` (a `char[n]` field). -/
def chars (b : ByteArray) (o n : Nat) : ByteArray := ByteArray.mk (Array.ofFn (n := n) fun i => at_ b (o + i.val))

/-- `n` elements of `size` bytes each from `o`. -/
def array {α : Type} (b : ByteArray) (o n size : Nat) (get : ByteArray → Nat → α) : Array α :=
  Array.ofFn (n := n) fun i => get b (o + size * i.val)

def putU8 (x : UInt8) (b : ByteArray) : ByteArray := b.push x
def putU16 (x : UInt16) (b : ByteArray) : ByteArray := (b.push x.toUInt8).push (x >>> 8).toUInt8
def putU32 (x : UInt32) (b : ByteArray) : ByteArray := putU16 (x >>> 16).toUInt16 (putU16 x.toUInt16 b)
def putU64 (x : UInt64) (b : ByteArray) : ByteArray := putU32 (x >>> 32).toUInt32 (putU32 x.toUInt32 b)
def putI8 (x : Int8) (b : ByteArray) : ByteArray := putU8 x.toUInt8 b
def putI16 (x : Int16) (b : ByteArray) : ByteArray := putU16 x.toUInt16 b
def putI32 (x : Int32) (b : ByteArray) : ByteArray := putU32 x.toUInt32 b
def putI64 (x : Int64) (b : ByteArray) : ByteArray := putU64 x.toUInt64 b
def putF32 (x : R) (b : ByteArray) : ByteArray := putU32 (ExecFloat.Binary.toBits32 x) b

/-- The first `n` elements of `xs`, padded with `zero`. -/
def padded {α : Type} (n : Nat) (zero : α) (xs : Array α) : Array α :=
  Array.ofFn (n := n) fun i => xs.getD i.val zero

/-- The first `n` bytes of `s`, padded with zeros. -/
def charsPadded (n : Nat) (s : ByteArray) : Array UInt8 := padded n 0 s.data

def putArray {α : Type} [Inhabited α] (n : Nat) (put : α → ByteArray → ByteArray) (xs : Array α)
    (b : ByteArray) : ByteArray :=
  (padded n default xs).foldl (fun acc x => put x acc) b

def putChars (n : Nat) (s : ByteArray) (b : ByteArray) : ByteArray :=
  (charsPadded n s).foldl (fun acc x => acc.push x) b

/-- A string as a `char[n]` field: its UTF-8 bytes, cut to `n` (no terminator when full). -/
def ofString (s : String) : ByteArray := s.toUTF8

/-- A `char[n]` field as a string: the bytes up to the first zero (invalid UTF-8 gives `""`). -/
def toString (b : ByteArray) : String :=
  let bs := b.data.toList.takeWhile (· != 0)
  (String.fromUTF8? (ByteArray.mk bs.toArray)).getD ""

end Mavlink.Bytes
