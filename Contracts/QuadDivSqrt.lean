import FloatModel.DivSqrt
import Contracts.QuadNear
import Contracts.QuadFloat

/-!
# Rounding bounds for `Float` division and square root

`FloatModel` bounds the rounding of `+`, `-`, `*`, whose exact results reach `roundWithAccuracy`
with accuracy `exact`. Division and square root reach it with the accuracy that `divCore` and
`sqrtCore` compute from the remainder of an integer quotient or integer square root.
`FloatModel.DivSqrt` proves, for every format, that whenever the accuracy correctly describes the
real value `v` that the mantissa truncates (`AccOK`), `roundWithAccuracy` rounds `v · 2^e` to
nearest within `2⁻ᴾ |x| + 2^(minExponent - 1)` (`UnpackedFloat.roundWithAccuracy_real`), and that
the division and square-root cores produce correct accuracies and enough quotient bits. This file
states the binary64 instances (`2⁻⁵³ |x| + 2⁻¹⁰⁷⁵`) and discharges `QuadNear.DivSqrtSpec`
(`divSqrtSpec`).
-/

open Float.Model UnpackedFloat ExtendedMantissa

namespace Contracts.QuadDivSqrt

/-- **Correct rounding with an accuracy**, binary64: if `acc` correctly places `v` relative to `m`,
and either `m` has at least 53 bits or `e` is at the bottom of the exponent range,
`roundWithAccuracy` gives a canonical finite float within `2⁻⁵³ (v 2^e) + 2⁻¹⁰⁷⁵` of `± v 2^e`. -/
theorem roundWithAccuracy_real (s : Sign) (m : ℕ) (e : ℤ) (acc : Accuracy) (v : ℝ)
    (hacc : AccOK acc m v) (hL : 52 ≤ m.log2 ∨ e ≤ -1074) (hhi : v * 2 ^ e ≤ maxFinite) :
    (roundWithAccuracy Format.binary64 s m e acc).Canonical ∧
    (roundWithAccuracy Format.binary64 s m e acc).isFinite = true ∧
    |(roundWithAccuracy Format.binary64 s m e acc).toReal - s.toReal * (v * 2 ^ e)| ≤
      2 ^ (-53 : ℤ) * (v * 2 ^ e) + 2 ^ (-1075 : ℤ) := by
  obtain ⟨hc, hf, herr⟩ :=
    UnpackedFloat.roundWithAccuracy_real Format.binary64 (by decide) s m e acc v hacc hL hhi
  exact ⟨(canonical_iff _).2 hc, hf, herr⟩

/-- **Division** rounds to nearest: relative error `2⁻⁵³` plus absolute error `2⁻¹⁰⁷⁵`. -/
theorem div_err_model {a b : Float} (ha : a.IsFinite) (hb : b.IsFinite) (hb0 : b.toReal ≠ 0)
    (hq : |a.toReal / b.toReal| ≤ maxFinite) :
    (a / b).IsFinite ∧ |(a / b).toReal - a.toReal / b.toReal| ≤
      2 ^ (-53 : ℤ) * |a.toReal / b.toReal| + 2 ^ (-1075 : ℤ) :=
  Float.div_err_all ha hb hb0 hq

/-- **Square root** rounds to nearest: relative error `2⁻⁵³` plus absolute error `2⁻¹⁰⁷⁵`. -/
theorem sqrt_err_model {a : Float} (ha : a.IsFinite) (h0 : 0 ≤ a.toReal)
    (h1 : a.toReal ≤ maxFinite) (_h1' : 1 ≤ maxFinite) :
    (Float.sqrt a).IsFinite ∧ |(Float.sqrt a).toReal - Real.sqrt a.toReal| ≤
      2 ^ (-53 : ℤ) * Real.sqrt a.toReal + 2 ^ (-1075 : ℤ) :=
  Float.sqrt_err_all ha h0 h1

/-! ## The hypotheses `DivSqrtSpec` hold of binary64 -/

/-- Lean's binary64 division and square root meet `QuadNear.DivSqrtSpec`. -/
-- <<divSqrtSpec>>
theorem divSqrtSpec : QuadNear.DivSqrtSpec where
  div_err a b ha hb hb0 hq :=
    div_err_model ha hb hb0 (hq.trans QuadNear.maxFinite_ge)
  sqrt_err a ha h0 h1 :=
    sqrt_err_model ha h0 (h1.trans QuadNear.maxFinite_ge) (le_trans (by norm_num) QuadNear.maxFinite_ge)
-- <</divSqrtSpec>>

end Contracts.QuadDivSqrt
