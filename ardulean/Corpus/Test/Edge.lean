import ArduLean.Runtime.CFloat

/-!
# Edge inputs (Corpus/PLAN.md, rule 6)

The inputs on which every candidate statement is evaluated before it is proved: NaNs (quiet, negative, signaling),
`±∞`, `±0`, the smallest and largest subnormals, the smallest normal, the largest finite, `±1` and its neighbors,
`FLT_EPSILON` (`2⁻²³`) and its neighbors, `±π`, `±π/2`, `2π` and their neighbors, and a few ordinary values. A candidate
is a `Bool`-valued function; `fails₁`/`fails₂`/`fails₃` list the inputs (tuples) on which it is `false`.
-/

open FloatLib.Floats (Binary32 Binary64)

namespace Corpus.Edge

/-- The edge words, by name. -/
def words : List (String × UInt32) := [
  ("nan", 0x7fc00000), ("-nan", 0xffc00000), ("snan", 0x7f800001),
  ("inf", 0x7f800000), ("-inf", 0xff800000),
  ("0", 0x00000000), ("-0", 0x80000000),
  ("minsub", 0x00000001), ("-minsub", 0x80000001), ("maxsub", 0x007fffff), ("minnorm", 0x00800000),
  ("max", 0x7f7fffff), ("-max", 0xff7fffff),
  ("1", 0x3f800000), ("-1", 0xbf800000), ("1-", 0x3f7fffff), ("1+", 0x3f800001), ("-1-", 0xbf7fffff),
  ("-1+", 0xbf800001),
  ("eps", 0x34000000), ("eps-", 0x33ffffff), ("eps+", 0x34000001), ("-eps", 0xb4000000), ("-eps-", 0xb3ffffff),
  ("-eps+", 0xb4000001),
  ("pi", 0x40490fdb), ("pi-", 0x40490fda), ("pi+", 0x40490fdc), ("-pi", 0xc0490fdb), ("-pi-", 0xc0490fda),
  ("-pi+", 0xc0490fdc),
  ("pi/2", 0x3fc90fdb), ("-pi/2", 0xbfc90fdb), ("2pi", 0x40c90fdb), ("2pi-", 0x40c90fda), ("2pi+", 0x40c90fdc),
  ("-2pi", 0xc0c90fdb), ("-2pi+", 0xc0c90fdc), ("-2pi-", 0xc0c90fda),
  ("0.5", 0x3f000000), ("2", 0x40000000), ("-2", 0xc0000000), ("0.95", 0x3f733333), ("0.95-", 0x3f733332),
  ("0.1", 0x3dcccccd), ("-0.3", 0xbe99999a), ("9.80665", 0x411ce80a), ("100", 0x42c80000), ("-100", 0xc2c80000),
  ("1e6", 0x49742400), ("1e20", 0x60ad78ec), ("-1e20", 0xe0ad78ec)]

/-- The edge inputs. -/
def inputs : List Binary32 := words.map fun (_, w) => Binary32.ofBits w

/-- The name of an edge input (or its bits, for a value not in the list). -/
def nameOf (x : Binary32) : String :=
  match words.find? (fun (_, w) => w == Binary32.toBits x) with
  | some (n, _) => n
  | none => s!"0x{String.ofList (Nat.toDigits 16 (Binary32.toBits x).toNat)}"

/-- The inputs on which a one-argument candidate fails. -/
def fails₁ (p : Binary32 → Bool) : List String :=
  (inputs.filter fun x => !p x).map nameOf

/-- The pairs on which a two-argument candidate fails. -/
def fails₂ (p : Binary32 → Binary32 → Bool) : List (String × String) := Id.run do
  let mut out := []
  for x in inputs do
    for y in inputs do
      if !p x y then out := (nameOf x, nameOf y) :: out
  return out.reverse

/-- The triples on which a three-argument candidate fails. -/
def fails₃ (p : Binary32 → Binary32 → Binary32 → Bool) : List (String × String × String) := Id.run do
  let mut out := []
  for x in inputs do
    for y in inputs do
      for z in inputs do
        if !p x y z then out := (nameOf x, nameOf y, nameOf z) :: out
  return out.reverse

/-- The `Int16` edge inputs. -/
def inputs16 : List Int16 := [-32768, -32767, -1000, -2, -1, 0, 1, 2, 1000, 32766, 32767]

def fails16₃ (p : Int16 → Int16 → Int16 → Bool) : List (Int16 × Int16 × Int16) := Id.run do
  let mut out := []
  for x in inputs16 do
    for y in inputs16 do
      for z in inputs16 do
        if !p x y z then out := (x, y, z) :: out
  return out.reverse

/-- A deterministic pseudo-random word sequence (xorshift32), for a wider sample than the edge list. -/
def xorshift (s : UInt32) : UInt32 :=
  let s := s ^^^ (s <<< 13)
  let s := s ^^^ (s >>> 17)
  s ^^^ (s <<< 5)

/-- `n` pseudo-random `Binary32` values (all bit patterns equally likely: NaNs, infinities, subnormals included). -/
def sample (n : Nat) (seed : UInt32 := 2463534242) : List Binary32 := Id.run do
  let mut s := seed
  let mut out := []
  for _ in [0:n] do
    s := xorshift s
    out := Binary32.ofBits s :: out
  return out

/-- `n` pseudo-random values in `[-a, a]` for a word `a`: words below `a`'s, with a random sign. -/
def sampleBelow (n : Nat) (a : UInt32) (seed : UInt32 := 88675123) : List Binary32 := Id.run do
  let mut s := seed
  let mut out := []
  for _ in [0:n] do
    s := xorshift s
    let w := (s &&& 0x7fffffff) % (a + 1)
    out := Binary32.ofBits (w ||| (s &&& 0x80000000)) :: out
  return out

end Corpus.Edge
