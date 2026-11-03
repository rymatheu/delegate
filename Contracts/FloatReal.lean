import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import FloatModel.ToReal

/-!
# The exact value of a float, and the arithmetic hypotheses

`Float.toReal` (defined in `FloatModel.ToReal`) reads the real number a `Float` denotes off Lean's
logical model of `Float` (`Float.toModel`, then `Float.Model.unpack`): a finite float `finite s m e` denotes
`s · m · 2^e`, and both signed zeros denote `0`. NaN and the two infinities also map to `0`; this
choice is harmless because every statement below asks for finiteness (`Float.isFinite`) wherever it
reads a value through `toReal`.

`FloatArith` lists, as propositions about `Float`, the facts about rounding that the closed-loop
proof of `Contracts.FloatLoop` uses. They are hypotheses of the theorems, not axioms. Each is the
standard model of IEEE-754 round-to-nearest and holds of binary64 with `ε = 2⁻⁵³`, `η = 2⁻¹⁰⁷⁵`
(half the smallest subnormal, the absolute error of a product in the subnormal range; a difference
is exact there) and `Ω` the largest finite double: `Contracts.FloatLoopIEEE.ieeeArith` proves this from Lean's
bit-level model of `Float`.

The values of the literals the controller uses are not hypotheses: they are computed from the model
by kernel reduction (`toReal_four`, `toReal_five`, `isFinite_four`, `isFinite_five`).
-/

open Float.Model UnpackedFloat

namespace Contracts.FloatReal

/-- The Boolean finiteness test used in the hypotheses below is the proposition `Float.IsFinite` of
`FloatModel`. -/
theorem isFinite_iff_IsFinite (f : Float) : f.isFinite = true ↔ f.IsFinite := Iff.rfl

theorem toReal_four : (4.0 : Float).toReal = 4 := by
  have h : (4.0 : Float).toModel.unpack = .finite .positive 4503599627370496 (-50) (by decide) := by
    rfl
  rw [Float.toReal, h]; simp [UnpackedFloat.toReal, Sign.apply]; norm_num

theorem toReal_five : (5.0 : Float).toReal = 5 := by
  have h : (5.0 : Float).toModel.unpack = .finite .positive 5629499534213120 (-50) (by decide) := by
    rfl
  rw [Float.toReal, h]; simp [UnpackedFloat.toReal, Sign.apply]; norm_num

theorem isFinite_four : (4.0 : Float).isFinite = true := by decide

theorem isFinite_five : (5.0 : Float).isFinite = true := by decide

/-- Rounding hypotheses on `Float` subtraction and multiplication, with unit roundoff `ε`, absolute
underflow error `η` and overflow threshold `Ω`. -/
-- <<FloatArith>>
structure FloatArith (ε η Ω : ℝ) : Prop where
  /-- A difference of finite floats whose exact value is at most `Ω` in magnitude is finite and
  within relative error `ε`. -/
  sub_err : ∀ a b : Float, a.isFinite → b.isFinite → |a.toReal - b.toReal| ≤ Ω →
    (a - b).isFinite ∧ |(a - b).toReal - (a.toReal - b.toReal)| ≤ ε * |a.toReal - b.toReal|
  /-- A product of finite floats whose exact value is at most `Ω` in magnitude is finite and within
  relative error `ε` plus absolute error `η`. -/
  mul_err : ∀ a b : Float, a.isFinite → b.isFinite → |a.toReal * b.toReal| ≤ Ω →
    (a * b).isFinite ∧ |(a * b).toReal - a.toReal * b.toReal| ≤ ε * |a.toReal * b.toReal| + η
-- <</FloatArith>>

/-- The sensing hypothesis: on the sensor range `|r| ≤ 100`, `sense` rounds a real to a finite float
within `δ`. The range is necessary: a finite float is at most `maxFinite` in magnitude
(`Float.abs_toReal_le_maxFinite`), so no `sense` meets the bound at every real
(`Contracts.FloatLoopIEEE.not_global_sense`). -/
-- <<SenseSpec>>
structure SenseSpec (δ : ℝ) (sense : ℝ → Float) : Prop where
  /-- Every reading in range is finite and within `δ` of the real value. -/
  sense_err : ∀ r : ℝ, |r| ≤ 100 → (sense r).isFinite ∧ |(sense r).toReal - r| ≤ δ
-- <</SenseSpec>>

end Contracts.FloatReal
