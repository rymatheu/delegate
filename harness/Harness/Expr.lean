import Harness.Schema

/-! The contract expression language: field names, binary32 and Boolean literals, `+ - * /`,
negation, `abs`, `≤ < =`, `∧ ∨ ¬`, `finite`.

Three readings are built here:
* `eval`: evaluation on records, every arithmetic operation one IEEE binary32 operation (round to
  nearest even), comparisons as IEEE (false when either side is NaN);
* `print`: readable text (also what the contract hash is taken of);
* `margin`: how far a formula is from being violated, from its `≤`/`<` atoms (`b - a` for `a ≤ b`
  and `a < b`, computed in binary64 from the two binary32 sides), combined by min over `∧`, max over
  `∨`, negation pushed to the atoms; `=`, `finite` and Boolean fields carry no margin, and a
  disjunction that holds by such a disjunct has none either (not its other disjunct's).

Integer fields are read as binary32 (exact for magnitudes below 2^24). -/

namespace Harness

inductive Expr where
  | var (name : String)
  /-- a field resolved to its slot in the evaluation environment -/
  | ref (name : String) (slot : Nat) (type : FieldType)
  | lit (bits : UInt32)
  | blit (b : Bool)
  | add (a b : Expr)
  | sub (a b : Expr)
  | mul (a b : Expr)
  | div (a b : Expr)
  | neg (a : Expr)
  | abs (a : Expr)
  | le (a b : Expr)
  | lt (a b : Expr)
  | eq (a b : Expr)
  | and (a b : Expr)
  | or (a b : Expr)
  | not (a : Expr)
  | finite (a : Expr)
  deriving Inhabited, Repr, BEq

namespace Expr

instance : Add Expr := ⟨add⟩
instance : Sub Expr := ⟨sub⟩
instance : Mul Expr := ⟨mul⟩
instance : Div Expr := ⟨div⟩
instance : Neg Expr := ⟨neg⟩
instance : OfScientific Expr := ⟨fun m s e => lit (Float32.ofScientific m s e).toBits⟩
instance : OfNat Expr n := ⟨lit (Float32.ofNat n).toBits⟩
instance : Coe String Expr := ⟨var⟩

infix:50 " ≤. " => Expr.le
infix:50 " <. " => Expr.lt
infix:50 " =. " => Expr.eq
infixr:35 " ∧. " => Expr.and
infixr:30 " ∨. " => Expr.or
notation:max "¬." a:40 => Expr.not a

/-- Field names, in order of first appearance. -/
def vars : Expr → List String
  | var n | ref n _ _ => [n]
  | lit _ | blit _ => []
  | add a b | sub a b | mul a b | div a b | le a b | lt a b | eq a b | and a b | or a b =>
    (a.vars ++ b.vars).eraseDups
  | neg a | abs a | not a | finite a => a.vars

/-- Binary32 literals appearing in the expression. -/
def lits : Expr → List UInt32
  | lit b => [b]
  | var _ | ref _ _ _ | blit _ => []
  | add a b | sub a b | mul a b | div a b | le a b | lt a b | eq a b | and a b | or a b =>
    a.lits ++ b.lits
  | neg a | abs a | not a | finite a => a.lits

/-- Top-level conjuncts. -/
def conjuncts : Expr → List Expr
  | and a b => a.conjuncts ++ b.conjuncts
  | e => [e]

/-! ### Printing -/

private def prec : Expr → Nat
  | or .. => 30 | and .. => 35 | not _ => 40 | le .. | lt .. | eq .. => 50
  | add .. | sub .. => 65 | mul .. | div .. => 70 | neg _ => 75 | _ => 100

partial def print (e : Expr) : String :=
  let p := prec e
  -- a child printed at the given minimum precedence, parenthesized below it
  let child (c : Expr) (min : Nat) : String :=
    if prec c < min then s!"({print c})" else print c
  match e with
  | var n | ref n _ _ => n
  | lit b => F32.text b
  | blit b => if b then "true" else "false"
  | add a b => s!"{child a p} + {child b (p+1)}"
  | sub a b => s!"{child a p} - {child b (p+1)}"
  | mul a b => s!"{child a p} * {child b (p+1)}"
  | div a b => s!"{child a p} / {child b (p+1)}"
  | neg a => s!"-{child a p}"
  | abs a => s!"|{print a}|"
  | le a b => s!"{child a (p+1)} ≤ {child b (p+1)}"
  | lt a b => s!"{child a (p+1)} < {child b (p+1)}"
  | eq a b => s!"{child a (p+1)} = {child b (p+1)}"
  | and a b => s!"{child a (p+1)} ∧ {child b p}"
  | or a b => s!"{child a (p+1)} ∨ {child b p}"
  | not a => s!"¬{child a p}"
  | finite a => s!"finite({print a})"

/-! ### Types and name resolution -/

inductive Ty where
  | num | bool
  deriving BEq, Repr

def Ty.name : Ty → String
  | num => "number" | bool => "Boolean"

/-- Replace field names by their slots; fails on an unknown name. -/
def resolve (look : String → Option (Nat × FieldType)) : Expr → Except String Expr
  | var n => match look n with
    | some (i, t) => pure (ref n i t)
    | none => throw s!"unknown field '{n}'"
  | ref n _ _ => match look n with
    | some (i, t) => pure (ref n i t)
    | none => throw s!"unknown field '{n}'"
  | lit b => pure (lit b)
  | blit b => pure (blit b)
  | add a b => return add (← resolve look a) (← resolve look b)
  | sub a b => return sub (← resolve look a) (← resolve look b)
  | mul a b => return mul (← resolve look a) (← resolve look b)
  | div a b => return div (← resolve look a) (← resolve look b)
  | neg a => return neg (← resolve look a)
  | abs a => return abs (← resolve look a)
  | le a b => return le (← resolve look a) (← resolve look b)
  | lt a b => return lt (← resolve look a) (← resolve look b)
  | eq a b => return eq (← resolve look a) (← resolve look b)
  | and a b => return and (← resolve look a) (← resolve look b)
  | or a b => return or (← resolve look a) (← resolve look b)
  | not a => return not (← resolve look a)
  | finite a => return finite (← resolve look a)

def typeOf : Expr → Except String Ty
  | var n => throw s!"unresolved field '{n}'"
  | ref _ _ t => pure (if t == .bool then .bool else .num)
  | lit _ => pure .num
  | blit _ => pure .bool
  | e@(add a b) | e@(sub a b) | e@(mul a b) | e@(div a b) => do
    expect e .num a; expect e .num b; pure .num
  | e@(neg a) | e@(abs a) => do expect e .num a; pure .num
  | e@(le a b) | e@(lt a b) => do expect e .num a; expect e .num b; pure .bool
  | eq a b => do
    let ta ← typeOf a
    let tb ← typeOf b
    if ta != tb then throw s!"'{print (eq a b)}' compares a {ta.name} with a {tb.name}"
    pure .bool
  | e@(and a b) | e@(or a b) => do expect e .bool a; expect e .bool b; pure .bool
  | e@(not a) => do expect e .bool a; pure .bool
  | e@(finite a) => do expect e .num a; pure .bool
where
  expect (parent : Expr) (t : Ty) (c : Expr) : Except String Unit := do
    let tc ← typeOf c
    if tc != t then throw s!"in '{print parent}': '{print c}' is a {tc.name}, expected a {t.name}"

/-! ### Evaluation -/

inductive Val where
  | num (x : Float32)
  | bool (b : Bool)

def Val.toF32 : Val → Float32
  | num x => x | bool _ => 0
def Val.toBool : Val → Bool
  | bool b => b | num _ => false

def wordToF32 (t : FieldType) (w : UInt32) : Float32 :=
  match t with
  | .f32 => Float32.ofBits w
  | .u32 => w.toFloat32
  | .i32 => if w &&& 0x80000000 != 0 then -((0 - w).toFloat32) else w.toFloat32
  | .bool => if w != 0 then 1 else 0

/-- Evaluate on an environment of words (the concatenated records). -/
def eval (env : Array UInt32) : Expr → Val
  | var _ => .bool false
  | ref _ i t => if t == .bool then .bool (env[i]! != 0) else .num (wordToF32 t env[i]!)
  | lit b => .num (Float32.ofBits b)
  | blit b => .bool b
  | add a b => .num ((a.eval env).toF32 + (b.eval env).toF32)
  | sub a b => .num ((a.eval env).toF32 - (b.eval env).toF32)
  | mul a b => .num ((a.eval env).toF32 * (b.eval env).toF32)
  | div a b => .num ((a.eval env).toF32 / (b.eval env).toF32)
  | neg a => .num (-(a.eval env).toF32)
  | abs a => .num ((a.eval env).toF32.abs)
  | le a b => .bool ((a.eval env).toF32 ≤ (b.eval env).toF32)
  | lt a b => .bool ((a.eval env).toF32 < (b.eval env).toF32)
  | eq a b => match a.eval env, b.eval env with
    | .num x, .num y => .bool (x == y)
    | .bool x, .bool y => .bool (x == y)
    | _, _ => .bool false
  | and a b => .bool ((a.eval env).toBool && (b.eval env).toBool)
  | or a b => .bool ((a.eval env).toBool || (b.eval env).toBool)
  | not a => .bool (!(a.eval env).toBool)
  | finite a => .bool ((a.eval env).toF32.isFinite)

def holds (env : Array UInt32) (e : Expr) : Bool := (e.eval env).toBool

private def negInf : Float := -1.0 / 0.0

private def minO : Option Float → Option Float → Option Float
  | some x, some y => some (if x ≤ y then x else y)
  | some x, none | none, some x => some x
  | none, none => none

private def maxO : Option Float → Option Float → Option Float
  | some x, some y => some (if x ≥ y then x else y)
  | some x, none | none, some x => some x
  | none, none => none

/-- A disjunction's margin from its disjuncts' (each with whether it holds): when a disjunct
without a margin of its own (a Boolean, `=`, `finite`) holds, the disjunction holds by it and
has no numeric margin (`none`); otherwise the larger of the disjuncts' margins. -/
private def orMargin (ma : Option Float) (ha : Bool) (mb : Option Float) (hb : Bool) :
    Option Float :=
  if (ma.isNone && ha) || (mb.isNone && hb) then none else maxO ma mb

/-- The margin of the formula (`pos`) or of its negation (`!pos`), negations pushed to the atoms
(De Morgan), so that `¬(p ∧ x ≤ c)` is read as `¬p ∨ c < x`. -/
def marginPol (env : Array UInt32) (pos : Bool) : Expr → Option Float
  | le a b | lt a b =>
    let d := (b.eval env).toF32.toFloat - (a.eval env).toF32.toFloat
    let d := if d.isNaN then negInf else d
    some (if pos then d else -d)
  | and a b =>
    if pos then minO (a.marginPol env true) (b.marginPol env true)
    else orMargin (a.marginPol env false) (!a.holds env) (b.marginPol env false) (!b.holds env)
  | or a b =>
    if pos then orMargin (a.marginPol env true) (a.holds env) (b.marginPol env true) (b.holds env)
    else minO (a.marginPol env false) (b.marginPol env false)
  | not a => a.marginPol env (!pos)
  | _ => none

/-- How far from violation (see the module comment); `none` when the formula has no `≤`/`<` atom,
or holds by a Boolean disjunct (a clause `¬b ∨ x ≤ c` with `b` false has no numeric margin: the
margin reported for it is not that of the disjunct `x ≤ c`, which may be negative). -/
def margin (env : Array UInt32) (e : Expr) : Option Float := e.marginPol env true

end Expr

-- functions of the contract language, for writing contracts
namespace Contract.Lang
def abs (e : Expr) : Expr := .abs e
def finite (e : Expr) : Expr := .finite e
def tt : Expr := .blit true
def ff : Expr := .blit false
end Contract.Lang

end Harness
