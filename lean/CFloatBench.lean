import CFloat

/-!
Micro-benchmark and equality check of `CFloat`'s conversions (cpp2lean/README.md, "Phase 3:
conversions on the bit patterns"). `cfloat_bench bench` times each conversion as compiled (with the
`@[csimp]` fast paths, if any); `cfloat_bench check [N]` compares every compiled conversion with a
copy of FloatLib's definition (`ref*` below: the same bodies under other names, which no `@[csimp]`
theorem rewrites) on N random bit patterns per conversion plus the special values and boundaries.
-/

open FloatLib.Floats
open FloatLib.Floats.Formats.BinaryInterchange (Model FloatFormat)

namespace Ref
def truncSat32 (lo hi : Int) (x : Binary32) : Int :=
  match ExecFloat.Binary.toInt? x with
  | some n => if n < lo then lo else if n > hi then hi else n
  | none => if ExecFloat.Binary.isNaN x then 0 else if ExecFloat.Binary.signBit x then lo else hi
def truncSat64 (lo hi : Int) (x : Binary64) : Int :=
  match ExecFloat.Binary.toInt? x with
  | some n => if n < lo then lo else if n > hi then hi else n
  | none => if ExecFloat.Binary.isNaN x then 0 else if ExecFloat.Binary.signBit x then lo else hi
def ofInt32 (n : Int) : Binary32 := ExecFloat.Binary.ofRat (n : Rat)
def ofInt64 (n : Int) : Binary64 := ExecFloat.Binary.ofRat (n : Rat)
def toBinary32 (x : Binary64) : Binary32 :=
  ExecFloat.Binary.ofModel (Model.cast .binary64 .binary32 (ExecFloat.Binary.toModel x))
end Ref

def lcg (s : UInt64) : UInt64 := s * 6364136223846793005 + 1442695040888963407

/-- `n` pseudo-random words (the high half of an LCG mixed with the low half). -/
def words (n : Nat) (seed : UInt64) : Array UInt64 := Id.run do
  let mut s := seed
  let mut a := Array.mkEmpty n
  for _ in [0:n] do
    s := lcg s
    let t := lcg s
    s := t
    a := a.push ((s >>> 32) ||| (lcg (s ^^^ 0x9e3779b97f4a7c15) <<< 32))
  return a

@[noinline] def run64 (xs : Array Binary64) (seed : UInt64) (f : Binary64 → UInt64) : UInt64 :=
  xs.foldl (fun acc x => acc * 31 + f x) seed
@[noinline] def run32 (xs : Array Binary32) (seed : UInt64) (f : Binary32 → UInt64) : UInt64 :=
  xs.foldl (fun acc x => acc * 31 + f x) seed
@[noinline] def runI32 (xs : Array Int32) (seed : UInt64) (f : Int32 → UInt64) : UInt64 :=
  xs.foldl (fun acc x => acc * 31 + f x) seed
@[noinline] def runI64 (xs : Array Int64) (seed : UInt64) (f : Int64 → UInt64) : UInt64 :=
  xs.foldl (fun acc x => acc * 31 + f x) seed
@[noinline] def runU32 (xs : Array UInt32) (seed : UInt64) (f : UInt32 → UInt64) : UInt64 :=
  xs.foldl (fun acc x => acc * 31 + f x) seed
@[noinline] def runU64 (xs : Array UInt64) (seed : UInt64) (f : UInt64 → UInt64) : UInt64 :=
  xs.foldl (fun acc x => acc * 31 + f x) seed
@[noinline] def runInt (xs : Array Int) (seed : UInt64) (f : Int → UInt64) : UInt64 :=
  xs.foldl (fun acc x => acc * 31 + f x) seed

/-- `n` integers of magnitude in `[2^lo, 2^hi]` (exponent uniform), random sign if `signed`, with the
limits `±2^hi` (and `2^hi - 1`) among them. -/
def magnitudes (n : Nat) (seed : UInt64) (lo hi : Nat) (signed : Bool) : Array Int :=
  let base : Array Int := #[2 ^ lo, 2 ^ hi - 1] ++ (if signed then #[-(2 ^ hi : Int), -(2 ^ lo : Int)] else #[])
  base ++ ((words n seed).map fun (w : UInt64) =>
    let e := lo + (w >>> 58).toNat % (hi - lo)
    let v : Int := Int.ofNat (2 ^ e + (w >>> 1).toNat % 2 ^ e)
    if signed && w &&& 1 == 1 then -v else v)

def timeIt (name : String) (n reps : Nat) (body : UInt64 → UInt64) : IO Unit := do
  let t0 ← IO.monoNanosNow
  let mut acc : UInt64 := 0
  for i in [0:reps] do
    acc := acc + body i.toUInt64
  let t1 ← IO.monoNanosNow
  let ns := (t1 - t0).toFloat / (n * reps).toFloat
  IO.println s!"{name}: {ns} ns per conversion  (checksum {acc})"

def bench : IO Unit := do
  let n := 20000
  -- doubles in about [-1e5, 1e5] with fractions, as EKF3's values: k / 1000
  let ks := (words n 1).map fun w => ((UInt64.toNat (w % 200000001) : Int) - 100000000)
  let thousand := Ref.ofInt64 1000
  let ds : Array Binary64 := ks.map fun k => (Ref.ofInt64 k / thousand : Binary64)
  let fs : Array Binary32 := ds.map Ref.toBinary32
  let is32 : Array Int := ks.map fun k => k / 100          -- |n| < 2^24
  let is64 : Array Int := (words n 2).map fun (w : UInt64) => Int.ofNat (UInt64.toNat (UInt64.shiftRight w 12)) - (2^51 : Int)   -- |n| < 2^53
  let a32 : Array Int32 := is32.map Int32.ofInt
  let a64 : Array Int64 := is64.map Int64.ofInt
  let u32 : Array UInt32 := is32.map fun k => UInt32.ofNat k.natAbs
  -- integers that round: above 2^24 (float) and 2^53 (double), up to INT64_MIN and UINT64_MAX
  let a32big : Array Int32 := (magnitudes n 3 24 31 true).map Int32.ofInt
  let u32big : Array UInt32 := (magnitudes n 4 24 32 false).map fun k => UInt32.ofNat k.natAbs
  let a64mid : Array Int64 := (magnitudes n 5 31 53 true).map Int64.ofInt
  let a64big : Array Int64 := (magnitudes n 6 53 63 true).map Int64.ofInt
  let a64f : Array Int64 := (magnitudes n 8 24 63 true).map Int64.ofInt
  let u64big : Array UInt64 := (magnitudes n 9 63 64 false).map fun k => UInt64.ofNat k.natAbs
  let u64small : Array UInt64 := (magnitudes n 10 0 53 false).map fun k => UInt64.ofNat k.natAbs
  let i64big : Array Int := (magnitudes n 11 53 64 true)
  let a64small : Array Int64 := a32.map Int32.toInt64
  let reps := 20
  timeIt "Binary32.toInt32" n reps fun s => run32 fs s fun x => (Binary32.toInt32 x).toInt64.toUInt64
  timeIt "Binary64.toInt32" n reps fun s => run64 ds s fun x => (Binary64.toInt32 x).toInt64.toUInt64
  timeIt "Binary64.toInt64" n reps fun s => run64 ds s fun x => (Binary64.toInt64 x).toUInt64
  timeIt "Binary64.toUInt16" n reps fun s => run64 ds s fun x => (Binary64.toUInt16 x).toUInt64
  timeIt "Int32.toBinary32" n reps fun s => runI32 a32 s fun k => (Binary32.toBits (Int32.toBinary32 k)).toUInt64
  timeIt "Int32.toBinary64" n reps fun s => runI32 a32 s fun k => Binary64.toBits (Int32.toBinary64 k)
  timeIt "Int64.toBinary64" n reps fun s => runI64 a64 s fun k => Binary64.toBits (Int64.toBinary64 k)
  timeIt "UInt32.toBinary32" n reps fun s => runU32 u32 s fun k => (Binary32.toBits (UInt32.toBinary32 k)).toUInt64
  timeIt "Int32.toBinary32, 2^24 <= |n| <= 2^31" n reps fun s => runI32 a32big s fun k => (Binary32.toBits (Int32.toBinary32 k)).toUInt64
  timeIt "UInt32.toBinary32, 2^24 <= n < 2^32" n reps fun s => runU32 u32big s fun k => (Binary32.toBits (UInt32.toBinary32 k)).toUInt64
  timeIt "Int64.toBinary64, 2^31 <= |n| <= 2^53" n reps fun s => runI64 a64mid s fun k => Binary64.toBits (Int64.toBinary64 k)
  timeIt "Int64.toBinary64, 2^53 <= |n| <= 2^63" n reps fun s => runI64 a64big s fun k => Binary64.toBits (Int64.toBinary64 k)
  timeIt "Int64.toBinary32, |n| < 2^24" n reps fun s => runI64 a64small s fun k => (Binary32.toBits (Int64.toBinary32 k)).toUInt64
  timeIt "Int64.toBinary32, 2^24 <= |n| <= 2^63" n reps fun s => runI64 a64f s fun k => (Binary32.toBits (Int64.toBinary32 k)).toUInt64
  timeIt "UInt64.toBinary64, n < 2^53" n reps fun s => runU64 u64small s fun k => Binary64.toBits (UInt64.toBinary64 k)
  timeIt "UInt64.toBinary64, 2^63 <= n < 2^64" n reps fun s => runU64 u64big s fun k => Binary64.toBits (UInt64.toBinary64 k)
  timeIt "UInt64.toBinary32, 2^63 <= n < 2^64" n reps fun s => runU64 u64big s fun k => (Binary32.toBits (UInt64.toBinary32 k)).toUInt64
  timeIt "CFloat.ofInt64 (Int), 2^53 <= |n| <= 2^64" n reps fun s => runInt i64big s fun k => Binary64.toBits (CFloat.ofInt64 k)
  timeIt "Binary64.toBinary32" n reps fun s => run64 ds s fun x => (Binary32.toBits (Binary64.toBinary32 x)).toUInt64
  timeIt "Binary32.toBinary64 (fast since phase 1)" n reps fun s => run32 fs s fun x => Binary64.toBits (Binary32.toBinary64 x)


/-- Random words with the exponent field drawn from `[lo, hi]` (the band where conversions to and
from integers change behaviour), plus fully random words. -/
def words32 (n : Nat) (seed : UInt64) (lo hi : Nat) : Array UInt32 :=
  (words n seed).map fun (w : UInt64) =>
    let e : Nat := lo + UInt64.toNat (UInt64.shiftRight w 40) % (hi - lo + 1)
    ((UInt64.toUInt32 w &&& (0x807fffff : UInt32)) ||| (UInt32.ofNat e <<< (23 : UInt32)))
def words64 (n : Nat) (seed : UInt64) (lo hi : Nat) : Array UInt64 :=
  (words n seed).map fun (w : UInt64) =>
    let e : Nat := lo + UInt64.toNat (UInt64.shiftRight (lcg w) 40) % (hi - lo + 1)
    ((w &&& (0x800fffffffffffff : UInt64)) ||| (UInt64.ofNat e <<< (52 : UInt64)))

def specials32 : Array UInt32 :=
  #[0, 0x80000000, 0x7f800000, 0xff800000, 0x7fc00000, 0xffc00000, 0x7f800001, 0xff800001,
    0x7fbfffff, 0x7fffffff, 1, 0x80000001, 0x007fffff, 0x807fffff, 0x00800000, 0x80800000,
    0x7f7fffff, 0xff7fffff, 0x3f800000, 0xbf800000, 0x3f000000, 0xbf000000, 0x3f7fffff, 0xbf7fffff,
    0x3fc00000, 0x4b000000, 0x4b7fffff, 0x4b800000, 0x4effffff, 0x4f000000, 0xcf000000, 0xcf000001,
    0x5effffff, 0x5f000000, 0xdf000000, 0xdf000001, 0x5f7fffff, 0x5f800000, 0x437f0000, 0x43800000,
    0xc3000000, 0xc3010000, 0x477fff00, 0x47800000, 0xc7000000, 0xc7000100]
def specials64 : Array UInt64 :=
  #[0, 0x8000000000000000, 0x7ff0000000000000, 0xfff0000000000000, 0x7ff8000000000000,
    0xfff8000000000000, 0x7ff0000000000001, 0xfff0000000000001, 0x7ff7ffffffffffff,
    0x7fffffffffffffff, 1, 0x8000000000000001, 0x000fffffffffffff, 0x0010000000000000,
    0x7fefffffffffffff, 0xffefffffffffffff, 0x3ff0000000000000, 0xbff0000000000000,
    0x3fe0000000000000, 0x3fefffffffffffff, 0xbfefffffffffffff, 0x4330000000000000,
    0x433fffffffffffff, 0x4340000000000000, 0x41dfffffffc00000, 0x41e0000000000000,
    0xc1e0000000000000, 0xc1e0000000200000, 0x43dfffffffffffff, 0x43e0000000000000,
    0xc3e0000000000000, 0xc3e0000000000001, 0x43efffffffffffff, 0x43f0000000000000,
    0x47efffffe0000000, 0x47effffff0000000, 0x47f0000000000000, 0x36a0000000000000,
    0x3690000000000000, 0x3690000000000001, 0x380fffffffffffff, 0x3810000000000000,
    0x3800000000000000, 0x37ffffffffffffff, 0x3ff0000010000000, 0x3ff0000030000000,
    0x3ff0000008000000, 0x3ff0000018000000, 0xbff0000010000000, 0x3ff00000f0000000]

/-- The (lo, hi) of every integer type C converts to (the wrappers of `CFloat.lean`). -/
def ranges : Array (Int × Int) :=
  #[(-2^7, 2^7 - 1), (-2^15, 2^15 - 1), (-2^31, 2^31 - 1), (-2^63, 2^63 - 1),
    (0, 2^8 - 1), (0, 2^16 - 1), (0, 2^32 - 1), (0, 2^64 - 1)]

/-- Integers around every boundary of the fast paths and of the integer types. -/
def intSamples (n : Nat) : Array Int := Id.run do
  let mut a : Array Int := #[0, 1, -1, 2, -2, 3, 7, -7]
  for k in [0:66] do
    for d in [0:4] do
      let p : Int := 2 ^ k
      a := a.push (p + d) |>.push (p - d) |>.push (-(p + d)) |>.push (-(p - d))
  let ws := words n 7
  for w in ws do
    let sh := (w >>> 58).toNat            -- 0..63: magnitude 2^0 .. 2^64
    let v : Int := Int.ofNat ((w >>> 1).toNat % 2 ^ (sh + 1))
    a := a.push (if w &&& 1 == 0 then v else -v)
  return a

def check (n : Nat) : IO UInt32 := do
  let mut bad : Nat := 0
  let mut count : Nat := 0
  -- float to integer
  let w32 := specials32 ++ (words n 11).map (·.toUInt32) ++ words32 n 12 100 200
  for b in w32 do
    let x := Binary32.ofBits b
    for (lo, hi) in ranges do
      count := count + 1
      if CFloat.truncSat32 lo hi x != Ref.truncSat32 lo hi x then
        bad := bad + 1
        if bad ≤ 10 then IO.println s!"truncSat32 {lo} {hi} {b}: {CFloat.truncSat32 lo hi x} vs {Ref.truncSat32 lo hi x}"
  let w64 := specials64 ++ words n 13 ++ words64 n 14 1000 1100
  for b in w64 do
    let x := Binary64.ofBits b
    for (lo, hi) in ranges do
      count := count + 1
      if CFloat.truncSat64 lo hi x != Ref.truncSat64 lo hi x then
        bad := bad + 1
        if bad ≤ 10 then IO.println s!"truncSat64 {lo} {hi} {b}: {CFloat.truncSat64 lo hi x} vs {Ref.truncSat64 lo hi x}"
  IO.println s!"float to integer: {count} conversions compared"
  -- integer to float
  let mut c2 : Nat := 0
  for k in intSamples n do
    c2 := c2 + 2
    if Binary32.toBits (CFloat.ofInt32 k) != Binary32.toBits (Ref.ofInt32 k) then
      bad := bad + 1
      if bad ≤ 20 then IO.println s!"ofInt32 {k}: {Binary32.toBits (CFloat.ofInt32 k)} vs {Binary32.toBits (Ref.ofInt32 k)}"
    if Binary64.toBits (CFloat.ofInt64 k) != Binary64.toBits (Ref.ofInt64 k) then
      bad := bad + 1
      if bad ≤ 20 then IO.println s!"ofInt64 {k}: {Binary64.toBits (CFloat.ofInt64 k)} vs {Binary64.toBits (Ref.ofInt64 k)}"
  IO.println s!"integer to float: {c2} conversions compared"
  -- integer to float through the wrappers of every integer type (the value wrapped into the type)
  let mut c4 : Nat := 0
  let mut bad4 : Nat := 0
  for k in intSamples n do
    let r32 := fun (v : Int) => Binary32.toBits (Ref.ofInt32 v)
    let r64 := fun (v : Int) => Binary64.toBits (Ref.ofInt64 v)
    let tests : Array (String × UInt64 × UInt64) := #[
      ("Int8.toBinary32", (Binary32.toBits (Int8.toBinary32 (Int8.ofInt k))).toUInt64, (r32 (Int8.ofInt k).toInt).toUInt64),
      ("Int16.toBinary32", (Binary32.toBits (Int16.toBinary32 (Int16.ofInt k))).toUInt64, (r32 (Int16.ofInt k).toInt).toUInt64),
      ("Int32.toBinary32", (Binary32.toBits (Int32.toBinary32 (Int32.ofInt k))).toUInt64, (r32 (Int32.ofInt k).toInt).toUInt64),
      ("Int64.toBinary32", (Binary32.toBits (Int64.toBinary32 (Int64.ofInt k))).toUInt64, (r32 (Int64.ofInt k).toInt).toUInt64),
      ("UInt8.toBinary32", (Binary32.toBits (UInt8.toBinary32 (UInt8.ofInt k))).toUInt64, (r32 (UInt8.ofInt k).toNat).toUInt64),
      ("UInt16.toBinary32", (Binary32.toBits (UInt16.toBinary32 (UInt16.ofInt k))).toUInt64, (r32 (UInt16.ofInt k).toNat).toUInt64),
      ("UInt32.toBinary32", (Binary32.toBits (UInt32.toBinary32 (UInt32.ofInt k))).toUInt64, (r32 (UInt32.ofInt k).toNat).toUInt64),
      ("UInt64.toBinary32", (Binary32.toBits (UInt64.toBinary32 (UInt64.ofInt k))).toUInt64, (r32 (UInt64.ofInt k).toNat).toUInt64),
      ("USize.toBinary32", (Binary32.toBits (USize.toBinary32 (USize.ofNat (UInt64.ofInt k).toNat))).toUInt64, (r32 (USize.ofNat (UInt64.ofInt k).toNat).toNat).toUInt64),
      ("Int8.toBinary64", Binary64.toBits (Int8.toBinary64 (Int8.ofInt k)), r64 (Int8.ofInt k).toInt),
      ("Int16.toBinary64", Binary64.toBits (Int16.toBinary64 (Int16.ofInt k)), r64 (Int16.ofInt k).toInt),
      ("Int32.toBinary64", Binary64.toBits (Int32.toBinary64 (Int32.ofInt k)), r64 (Int32.ofInt k).toInt),
      ("Int64.toBinary64", Binary64.toBits (Int64.toBinary64 (Int64.ofInt k)), r64 (Int64.ofInt k).toInt),
      ("UInt8.toBinary64", Binary64.toBits (UInt8.toBinary64 (UInt8.ofInt k)), r64 (UInt8.ofInt k).toNat),
      ("UInt16.toBinary64", Binary64.toBits (UInt16.toBinary64 (UInt16.ofInt k)), r64 (UInt16.ofInt k).toNat),
      ("UInt32.toBinary64", Binary64.toBits (UInt32.toBinary64 (UInt32.ofInt k)), r64 (UInt32.ofInt k).toNat),
      ("UInt64.toBinary64", Binary64.toBits (UInt64.toBinary64 (UInt64.ofInt k)), r64 (UInt64.ofInt k).toNat),
      ("USize.toBinary64", Binary64.toBits (USize.toBinary64 (USize.ofNat (UInt64.ofInt k).toNat)), r64 (USize.ofNat (UInt64.ofInt k).toNat).toNat)]
    for (name, got, want) in tests do
      c4 := c4 + 1
      if got != want then
        bad4 := bad4 + 1
        if bad4 ≤ 20 then IO.println s!"{name} {k}: {got} vs {want}"
  bad := bad + bad4
  IO.println s!"integer types to float: {c4} conversions compared"
  -- double to float
  let mut c3 : Nat := 0
  for b in specials64 ++ words n 15 ++ words64 n 16 870 1160 ++ words64 n 17 1023 1023 do
    let x := Binary64.ofBits b
    c3 := c3 + 1
    if Binary32.toBits (Binary64.toBinary32 x) != Binary32.toBits (Ref.toBinary32 x) then
      bad := bad + 1
      if bad ≤ 30 then IO.println s!"toBinary32 {b}: {Binary32.toBits (Binary64.toBinary32 x)} vs {Binary32.toBits (Ref.toBinary32 x)}"
  IO.println s!"double to float: {c3} conversions compared"
  IO.println s!"differences: {bad}"
  return if bad == 0 then 0 else 1

def main (args : List String) : IO UInt32 := do
  match args with
  | ["bench"] => bench; return 0
  | ["check"] => check 100000
  | ["check", k] => check k.toNat!
  | _ => IO.eprintln "usage: cfloat_bench bench | check [N]"; return 2
