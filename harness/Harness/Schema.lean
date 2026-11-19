import Harness.F32

/-! Schemas and records. A schema is a flat list of named fields of fixed-size numeric types. A
record holds one 32-bit word per field: a float's bit pattern, an integer's two's complement, a
Boolean as 0 or 1. Records cross the pipe and enter files in that form; decimals are only for
people to read. -/

namespace Harness

inductive FieldType where
  | f32 | i32 | u32 | bool
  deriving BEq, Repr, Inhabited, DecidableEq

namespace FieldType

def name : FieldType → String
  | f32 => "f32" | i32 => "i32" | u32 => "u32" | bool => "bool"

def ofName? : String → Option FieldType
  | "f32" => some f32 | "i32" => some i32 | "u32" => some u32 | "bool" => some bool | _ => none

/-- Bytes on the wire. -/
def bytes : FieldType → Nat
  | bool => 1 | _ => 4

def cType : FieldType → String
  | f32 => "float" | i32 => "int32_t" | u32 => "uint32_t" | bool => "bool"

end FieldType

structure Field where
  name : String
  type : FieldType
  doc : String := ""
  /-- for an output: the word a `prev` wire made by `compose` holds at the first tick -/
  init : UInt32 := 0
  deriving Repr, Inhabited

abbrev Schema := Array Field

def Schema.bytes (s : Schema) : Nat := s.foldl (fun n f => n + f.type.bytes) 0

def Schema.text (s : Schema) : String :=
  ", ".intercalate (s.toList.map fun f => s!"{f.name}: {f.type.name}")

/-- Same names and types in the same order (documentation is not compared). -/
def Schema.same (a b : Schema) : Bool :=
  a.size == b.size && (a.zip b).all fun (x, y) => x.name == y.name && x.type == y.type

/-- One word per field. -/
abbrev Record := Array UInt32

def Record.encode (s : Schema) (r : Record) : ByteArray := Id.run do
  let mut b := ByteArray.emptyWithCapacity s.bytes
  for i in [0:s.size] do
    let w := r[i]!
    match s[i]!.type with
    | .bool => b := b.push (if w != 0 then 1 else 0)
    | _ =>
      b := b.push w.toUInt8
      b := b.push (w >>> 8).toUInt8
      b := b.push (w >>> 16).toUInt8
      b := b.push (w >>> 24).toUInt8
  return b

def Record.decode (s : Schema) (b : ByteArray) (off : Nat := 0) : Record := Id.run do
  let mut r : Record := Array.mkEmpty s.size
  let mut o := off
  for f in s do
    match f.type with
    | .bool =>
      r := r.push (if b[o]! != 0 then 1 else 0)
      o := o + 1
    | _ =>
      r := r.push (b[o]!.toUInt32 ||| (b[o+1]!.toUInt32 <<< 8) ||| (b[o+2]!.toUInt32 <<< 16) |||
                   (b[o+3]!.toUInt32 <<< 24))
      o := o + 4
  return r

/-- Readable text of one word. -/
def FieldType.showWord (t : FieldType) (w : UInt32) : String :=
  match t with
  | .f32 => F32.text w
  | .u32 => toString w.toNat
  | .i32 => if w &&& 0x80000000 != 0 then s!"-{(0 - w).toNat}" else toString w.toNat
  | .bool => if w != 0 then "true" else "false"

def Record.text (s : Schema) (r : Record) : String :=
  " ".intercalate ((s.zip r).toList.map fun (f, w) => s!"{f.name}={f.type.showWord w}")

/-- Words as text for files: hexadecimal for f32, decimal for the others. -/
def FieldType.wordText (t : FieldType) (w : UInt32) : String :=
  match t with
  | .f32 => F32.hex w
  | _ => t.showWord w

def FieldType.parseWord? (t : FieldType) (s : String) : Option UInt32 :=
  match t with
  | .f32 => F32.parseHex? s
  | .bool => if s == "true" then some 1 else if s == "false" then some 0 else none
  | .u32 => s.toNat?.bind fun n => if n < 2 ^ 32 then some (UInt32.ofNat n) else none
  | .i32 =>
    if s.startsWith "-" then
      (s.drop 1).toString.toNat?.bind fun n => if n ≤ 2 ^ 31 then some (0 - UInt32.ofNat n) else none
    else s.toNat?.bind fun n => if n < 2 ^ 31 then some (UInt32.ofNat n) else none

end Harness
