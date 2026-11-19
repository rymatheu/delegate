import Harness.Module

/-! Generating parameter records and input sequences that satisfy a module's assumption.

For each field the generator builds a pool of edge values: for f32 ±0, the smallest subnormal,
the largest subnormal, the smallest normal, ±1, the largest finite, ±∞, NaN, and every literal of
the assumption that the field is compared with, its negation, and the binary32 neighbors of both;
for integers 0, ±1 and the extremes, and the integers nearest to every literal the field is
compared with and their neighbors; for Booleans both. The pool keeps the values that satisfy
the assumption's conjuncts that mention only that field. A value is drawn from that pool, or
uniformly between the smallest and largest finite pool values (for an integer field only when it is
compared with a literal; otherwise as a random bit pattern), or as a uniformly random bit
pattern (which spreads over all exponents), each time kept only if it satisfies those conjuncts.
Each case draws a parameter record, then decides per input field whether the field is held at one
value for the whole case or drawn afresh every step; every drawn (params, input) pair is checked
against the full assumption and redrawn if it fails. Everything follows from the seed. -/

namespace Harness

/-- SplitMix64. -/
structure Rng where
  s : UInt64

def Rng.next (g : Rng) : UInt64 × Rng :=
  let s := g.s + 0x9E3779B97F4A7C15
  let z := (s ^^^ (s >>> 30)) * 0xBF58476D1CE4E5B9
  let z := (z ^^^ (z >>> 27)) * 0x94D049BB133111EB
  (z ^^^ (z >>> 31), ⟨s⟩)

abbrev GenM := StateM Rng

def rand64 : GenM UInt64 := modifyGet Rng.next
def rand32 : GenM UInt32 := return (← rand64).toUInt32
/-- Uniform in [0, 1). -/
def randUnit : GenM Float := return ((← rand64) >>> 11).toFloat / 9007199254740992.0
def randBelow (n : Nat) : GenM Nat := return (← rand64).toNat % (max n 1)
def chance (p : Float) : GenM Bool := return (← randUnit) < p

structure FieldGen where
  field : Field
  slot : Nat
  /-- conjuncts of the assumption that mention only this field -/
  local_ : List Expr
  edges : Array UInt32
  lo : Option Float
  hi : Option Float

private def f32Edges : List UInt32 :=
  [0x00000000, 0x80000000, 0x00000001, 0x80000001, 0x007fffff, 0x807fffff, 0x00800000, 0x80800000,
   0x3f800000, 0xbf800000, 0x7f7fffff, 0xff7fffff, 0x7f800000, 0xff800000, 0x7fc00000]

private def intEdges : List UInt32 := [0, 1, 0xffffffff, 0x7fffffff, 0x80000000, 2]

/-- The word of an integer-valued float for an integer field, if it is in the field's range. -/
def intWord (t : FieldType) (x : Float) : Option UInt32 :=
  if x.isNaN || x.isInf then none
  else if t == .u32 then
    if 0 ≤ x && x < 4294967296 then some x.toUInt64.toUInt32 else none
  else if -2147483648 ≤ x && x < 2147483648 then
    some (if x < 0 then 0 - (-x).toUInt64.toUInt32 else x.toUInt64.toUInt32)
  else none

/-- For an integer field compared with the binary32 literal `c`: the integer nearest to it and
its two neighbors. -/
def intNear (t : FieldType) (c : UInt32) : List UInt32 :=
  let x := (Float32.ofBits c).toFloat.round
  [x - 1, x, x + 1].filterMap (intWord t)

def FieldGen.ok (g : FieldGen) (env : Array UInt32) (w : UInt32) : Bool :=
  let env := env.set! g.slot w
  g.local_.all (·.holds env)

def FieldGen.make (envSize : Nat) (conj : List Expr) (f : Field) (slot : Nat) : FieldGen :=
  let local_ := conj.filter fun c => c.vars == [f.name]
  let cands : List UInt32 := match f.type with
    | .f32 =>
      let litsN := (local_.flatMap (·.lits)).flatMap fun c =>
        let n := c ^^^ F32.signBit
        [c, F32.nextUp c, F32.nextDown c, n, F32.nextUp n, F32.nextDown n]
      (f32Edges ++ litsN).eraseDups
    | .bool => [0, 1]
    | t => intEdges ++ ((local_.flatMap (·.lits)).flatMap (intNear t)).eraseDups
  let env0 := Array.replicate envSize (0 : UInt32)
  let g0 : FieldGen := { field := f, slot, local_, edges := #[], lo := none, hi := none }
  let edges := (cands.filter (g0.ok env0)).toArray
  let finite := (edges.filter fun w => f.type == .f32 && (Float32.ofBits w).isFinite).map
    fun w => (Float32.ofBits w).toFloat
  -- an integer field gets a range only from the literals it is compared with
  let hasLits := !(local_.flatMap (·.lits)).isEmpty
  let finite := if f.type == .f32 || f.type == .bool || !hasLits then finite
    else edges.map fun w => (Expr.wordToF32 f.type w).toFloat
  let lo := finite.foldl (fun m x => some (match m with | some y => min x y | none => x)) none
  let hi := finite.foldl (fun m x => some (match m with | some y => max x y | none => x)) none
  { g0 with edges, lo, hi }

/-- One value satisfying the field's own conjuncts. -/
def FieldGen.draw (g : FieldGen) (env0 : Array UInt32) : GenM UInt32 := do
  let pickEdge : GenM (Option UInt32) := do
    if g.edges.isEmpty then return none
    return some g.edges[← randBelow g.edges.size]!
  for _ in [0:200] do
    let r ← randUnit
    let cand ← if r < 0.3 then pickEdge
      else if r < 0.65 && g.field.type == .f32 then
        match g.lo, g.hi with
        | some lo, some hi => do
          let u ← randUnit
          pure (some (lo + u * (hi - lo)).toFloat32.toBits)
        | _, _ => pure (some (← rand32))
      else if r < 0.65 && (g.field.type == .u32 || g.field.type == .i32) &&
          g.lo.isSome && g.hi.isSome then
        let n ← randBelow ((g.hi.get! - g.lo.get!).toUInt64.toNat + 1)
        pure (intWord g.field.type (g.lo.get! + n.toFloat))
      else if g.field.type == .bool then pure (some ((← rand32) &&& 1))
      else pure (some (← rand32))
    if let some w := cand then
      if g.ok env0 w then return w
  match ← pickEdge with
  | some w => return w
  | none => return 0

end Harness
