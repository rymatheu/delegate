/-!
# Scalar interface for the flight controller

Every controller component is written over a type parameter `α` carrying an `Arith α` instance, so
that one definition can be executed over `Float` (see `Flight.FloatInstance`) and reasoned about over
the real numbers. The class holds exactly the operations the controller
uses: the field operations, a decidable order, `min`, `max`, `abs`, `sqrt`, `sin`, `cos`, `atan2`,
the constant `pi`, and literals. The literals `0` and `1` come from the `Zero` and `One` parents, so
over `ℝ` they are Mathlib's own `0` and `1`; decimal literals such as `0.135` come from the
`OfScientific` parent; other natural literals go through `natCast` (the controller code itself uses
only `0`, `1` and decimals).

This file imports only core Lean.
-/

namespace Flight

/-- The scalar operations a controller step may use, packaged so the same code runs over `Float` and is proven over `ℝ`. -/
class Arith (α : Type) extends Zero α, One α, Add α, Sub α, Mul α, Div α, Neg α, LT α, LE α,
    Min α, Max α, OfScientific α where
  /-- Interpretation of a natural-number literal of value two or more. -/
  natCast : Nat → α
  /-- Strict order is decidable, so controller code may branch on `a < b`. -/
  decLt : DecidableRel (fun a b : α => a < b)
  /-- Non-strict order is decidable, so controller code may branch on `a ≤ b`. -/
  decLe : DecidableRel (fun a b : α => a ≤ b)
  /-- Absolute value. -/
  abs : α → α
  /-- Square root (only applied to non-negative arguments by the controller). -/
  sqrt : α → α
  /-- Sine of an angle in radians. -/
  sin : α → α
  /-- Cosine of an angle in radians. -/
  cos : α → α
  /-- Two-argument arctangent `atan2 y x`, the angle of the point `(x, y)` in `(-π, π]`. -/
  atan2 : α → α → α
  /-- The constant π. -/
  pi : α

attribute [instance_reducible, instance] Arith.decLt Arith.decLe

/-- Natural-number literals from two upwards are read through `Arith.natCast`; low priority so concrete types keep their own literals. -/
instance (priority := low) Arith.instOfNat {α : Type} [Arith α] (n : Nat) : OfNat α (n + 2) :=
  ⟨Arith.natCast (n + 2)⟩

variable {α : Type} [Arith α]

/-- Saturate `x` to the interval `[lo, hi]` (assuming `lo ≤ hi`). -/
def clip (lo hi x : α) : α := max lo (min hi x)

/-- Saturate `x` to the symmetric interval `[-lim, lim]`. -/
def clipSym (lim x : α) : α := clip (-lim) lim x

/-- Square of a scalar. -/
def sq (x : α) : α := x * x

/-- Wrap an angle to `(-π, π]` via `atan2 (sin e) (cos e)`, which avoids any loop or floor. -/
def wrapAngle (e : α) : α := Arith.atan2 (Arith.sin e) (Arith.cos e)

end Flight
