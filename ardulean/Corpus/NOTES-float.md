# FloatLib for the corpus: what the proofs need and where it is

FloatLib pin `acba2057`, Lean 4.35. Paths are relative to `.lake/packages/floatlib/`. `BI` stands for
`FloatLib/Floats/Formats/BinaryInterchange`, `Cfg` for `BI/Configured`.

This table is the phase A survey (read-only) checked against phase B. "Used" means a `Corpus` proof calls the name and
the build accepted it. "Machine/Float" means FloatLib does not have the lemma in the form we need, so `Corpus/Machine/Float.lean`
proves it from FloatLib's definitions.

## How `Binary32` is built

- `Binary32 := ExecFloat.Binary 8 23` (`Cfg/Type.lean`). It is a subtype of the raw `UInt32` word, not an inductive.
  The proof model is `Model (ExecFloat.Binary.descriptor 8 23)`, a structure over a `BitVec 32`. The bridges are
  `ExecFloat.Binary.toModel` and `ofModel`.
- `Model.cast .binary32 .binary64` in `ArduLean/Runtime/CFloat.lean` has argument type `Model (descriptor 8 23)`. The two formats are
  definitionally equal, but `rw` and `generalize` do not match them syntactically. State `Model`-level lemmas with
  `descriptor 8 23`; this is what `Corpus.F64.toModel_toBinary64` does.
- The configured lemmas (`ExecFloat.Binary.*`) apply to `Binary32` by unification. Their `hformat` argument is
  discharged automatically.
- **Pitfall.** `rw` with a configured lemma whose statement uses `toReal` fails: the target, written with
  `Corpus.F32.real` (an abbrev), raises "motive is not type correct (Binary32._proof_1)". Use `have e : real … = … := lemma`
  and then `rw [e]`, or use the `real_*` restatements in Machine/Float. Likewise, rewriting with `toModel_hAdd` and the
  other `toModel_h*` lemmas needs `simp only`, because `rw` cannot synthesize their `HasSpec` instance.

## Lookup table

| Need | FloatLib (file) | Corpus |
|---|---|---|
| `<` and `≤` | `instance : LT/LE` = `compareLess`/`compareLessEqual` (`Cfg/Instances.lean`). The code's `decide` uses CFloat's `Binary32.decLt`/`decLe` (priority high), which are definitionally the same. | used through `lt_iff_compare_eq_lt`, `le_iff_compare_eq_lt_or_eq` |
| `>`, `≥` | Lean's `GT.gt a b := b < a` | `decide (x ≥ c)` is `decide (c ≤ x)` by `Iff.rfl` |
| `==` | `Binary32.instBEq := ⟨Binary32.beq⟩` (CFloat) = `compareEqual`. FloatLib's `beq_*` lemmas are stated for `execFloatBEq` and need a `change` first. | not needed yet |
| NaN in comparisons | `ExecFloat.Binary.not_lt_of_isNaN`, `not_le_of_isNaN` (`Cfg/Instances.lean`, hypothesis `isNaN l ∨ isNaN r`) | used: `F32.not_lt_of_isNaN_left/right`, `not_le_of_isNaN_left/right`, `isNaN_false_of_lt/le` |
| order ↔ value, finite operands | `lt_iff_toReal_lt`, `le_iff_toReal_le` (`Cfg/Real.lean`) | not used: they exclude `±∞` |
| order ↔ value, all non-NaN operands | `Model.compare_eq_some_lt_iff_toEReal_lt`, `compare_eq_some_eq_iff_toEReal_eq`, `exists_toEReal?_of_isNaN_eq_false` (`BI/Operations/Compare/Proof.lean`), `Model.toEReal` (`BI/Model/ERealSemantics.lean`) | **Machine/Float**: `F32.ext x := Model.toEReal (toModel x)`; `lt_iff_ext`, `le_iff_ext`, `not_lt_iff_le`, `le_trans`, `lt_of_lt_of_le`, `lt_of_le_of_lt`, `le_of_lt`, `le_refl_of_not_isNaN`; the same for `Binary64` in `Corpus.F64` |
| `ext` of a finite value | `Model.toEReal_eq_coe_toReal_of_isFinite` | used: `ext_of_isFinite` |
| `ext` of `±∞` | `Model.toEReal_eq_ite`, `toEReal_posInf/negInf` | **Machine/Float**: `ext_posInf`, `ext_negInf` (`decide +kernel` for the classification) |
| `isNaN`, `isFinite`, `isInf` | `ExecFloat.Binary.isNaN …` = `Model.* (toModel v)` (`Cfg/Value/Core.lean`); CFloat's `Binary32.isNaN` is a plain `def` (`rfl`) | — |
| non-NaN value is finite or ±∞ | `Model.isFinite_eq_true_of_isNaN_eq_false_of_isInf_eq_false` (`BI/Dyadic/Classification.lean`) | **Machine/Float**: `finite_or_inf` (`x` finite, or `x = ofBits 0x7f800000`, or `x = ofBits 0xff800000`), using `isInf_toModel` (bit pattern, proved on the model the way CFloat's `isZero_toModel` is), `eq_posInf`, `eq_negInf` |
| `abs` | `Model.abs = copySign x posZero` (`BI/Model/Carrier.lean`); `@[simp] Model.isNaN_abs`, `isInf_abs`, `isFinite_abs`; `Model.signBit_abs_of_supportsSignedZero`; `toModel_abs` (`Cfg/Operations/Proof.lean`) | **Machine/Float**: `model_abs_eq` (`abs = if signBit then neg else id`), `ext_abs` (`max e (-e)`), `abs_lt_iff` (`|x| < c ↔ -c < x < c`, every `x`), `isNaN_abs`. `Model.toReal_abs_of_isFinite` (`BI/Analysis/Rational.lean`) exists but its module is not built in this workspace, so it is not imported. |
| `neg` | `Model.neg` = sign flip for IEEE; `@[simp] Model.isNaN_neg`, `isInf_neg`, `signBit_neg`; `Model.toEReal_neg_of_isNaN_eq_false` (`BI/Model/SignedERealSemantics.lean`); `Model.toReal_neg` (`BI/Arithmetic/SignedSemantics/Core.lean`); configured `isFinite_neg` (`Cfg/Real.lean`) | used: `ext_neg`, `isNaN_neg`, `real_neg`, `isFinite_neg` |
| sign of a value | `Model.toReal_nonneg_of_signBit_eq_false` (`BI/DirectedSemantics/Bounds.lean`) | **Machine/Float**: `toEReal_nonneg_of_signBit`, `toEReal_nonpos_of_signBit` |
| result = rounding of the exact result | `toReal_add/sub/mul_eq_roundAt (hresult : isFinite (l ∘ r))`, `toReal_div_eq_roundAt (hright) (hresult)`, `toReal_sqrt_eq_roundAt (hvalue) (hdomain : isZero ∨ signBit = false)` (`Cfg/Real.lean`) | used; restated as `F32.real_add/sub/mul/div` |
| error bounds | `abs_toReal_*_sub_le` (half-ulp), `Model.abs_roundAt_sub_le`, `relativeError_roundAt_le_of_normal`, `roundAt_standardModel`, `abs_roundAt_sub_le_unitRoundoffAt` (`BI/Analysis/{Error,StandardModel}.lean`); `MixedError` forms (`Cfg/MixedError/Rounding.lean`) | not used yet: no Meaning lemma so far needs an error bound |
| monotone rounding | `Model.roundAt_mono` (`BI/Rounding/Proof.lean`) | used: **Machine/Float** `roundAt_mem` (a result between two floats rounds between them) |
| rounding fixes floats | `@[simp] Model.roundAt_toReal_eq (x) (hfin)`, `roundAt_zero` | used |
| finiteness from a magnitude bound | `Model.isFinite_add_of_abs_toReal_add_le_posMaxFinite` (`BI/Arithmetic/Semantics.lean`), `isFinite_sub_of_…` (`…/Subtraction.lean`), `isFinite_mul_of_abs_mul_le_posMaxFinite`, `isFinite_div_of_abs_div_le_posMaxFinite` (`BI/Arithmetic/DivisionSemantics.lean`, needs `isZero y = false`); `ExecFloat.Binary.abs_toReal_le_posMaxFinite_of_isFinite` | used: **Machine/Float** `add_mem`, `sub_mem`, `div_mem` (finite and between `lo` and `hi`), `isFinite_mul_of_le` |
| finite result ⇒ finite operands | `Model.isFinite_of_isFinite_add`, `isFinite_of_isFinite_mul` | used |
| sign of a finite sum or product | `Configured.toReal_add_nonneg` (`Cfg/MixedError.lean`): an infinite sum gets real value 0, so it says nothing about `±∞` | **Machine/Float**: `add_nonneg_of_isFinite`, `mul_nonneg_of_isFinite` (finite result only). **Not in the library: the sign of an overflowed product or sum (`signBit (mul x y)`)**, so `sq_nonneg` needs a finite square (OPEN.md) |
| `sqrt` | `isFinite_sqrt (hvalue) (hdomain)`, `toReal_sqrt_eq_roundAt`, `isZero_or_signBit_eq_false_of_toReal_nonneg` (`Cfg/Real.lean`) | **Machine/Float**: `sqrt_of_nonneg` (not NaN, `≥ 0`, for every `x ≥ 0` with `+∞` included; `sqrt_posInf` by `decide +kernel`). **Not in the library: a nearest-mode `isNaN_sqrt`, `sqrt_mono`** |
| exactness | `toReal_sub_self`, `toReal_*_of_isZero_*`, `toReal_mul_of_abs_toReal_eq_one_*`, Sterbenz `Model.toReal_sub_eq_of_sterbenz*` (`BI/Analysis/Sterbenz.lean`), `Model.roundAt_of_genericFormat` | not used. **Not in the library: multiplication by a power of two is exact; `Model.mul (neg x) y = neg (mul x y)`; `sub x y = neg (sub y x)`** (OPEN.md: the `_odd` lemmas, `is_equal` symmetry) |
| `Int32.toBinary32`, `Int16.toBinary32`, `Int32.toBinary64` | CFloat: `CFloat.ofInt32 n = ExecFloat.Binary.ofRat n` (`ArduLean/Runtime/CFloat.lean:2404-2421`); `toReal_ofRat_intCast_of_abs_le` (`Cfg/MixedError/Rounding.lean`) | the code's literals by `decide +kernel`: `F32.int32_zero/one/two` |
| `Binary64.toBinary32` | CFloat: `ofModel (Model.cast .binary64 .binary32 …)`; `Model.cast_eq_roundAt` (`BI/Conversion/Cast/Proof.lean`) | the code's literals by `decide +kernel` (`F32.pi_const`, `two_pi_const`, `half_pi_const`, `one64_const`, `expo_max_const`, …) |
| `Binary32.toBinary64` exact | `Model.cast_exact_of_gridExtension` (finite, needs a finite result), `Model.isFinite_cast_of_abs_toReal_le_posMaxFinite` (`BI/Analysis/Error.lean`), `Model.cast_of_isNaN`, `isNaN_propagatedNaN`; `nativeOverflow_eq_signedInf_of_isIEEE` (`BI/Dyadic/Rounding.lean`) | **Machine/Float**: `F64.isNaN_toBinary64`, `F64.ext_toBinary64` (every non-NaN value, `±∞` included), `cast_of_isInf`, `posMaxFinite_le` |
| `ofBits`/`toBits` | `ExecFloat.Binary.ofBits32_toBits32`, `toBits32_ofBits32` (`FloatLib/Floats/Formats/IEEE754/Native.lean`, `@[simp]`) | used: `F32.ofBits_toBits` |
| a literal's value | `ExecFloat.Binary.toRat?` (computable; `Cfg/Value/Core.lean:94`); `toReal_of_toRat?_eq_some` (`Cfg/Real.lean:90`); `Model.Algebraic.isFinite_of_toRat?_eq_some` (`BI/Model/RealSemantics.lean`) | **Machine/Float**: `ext_eq_of_toRat?`, `real_eq_of_toRat?`, `isFinite_of_toRat?`; the hypothesis is closed by `decide +kernel` (e.g. `ext_eps`: `ofBits 0x34000000` is `1/8388608`) |
| evaluating code on literals | `decide +kernel` evaluates `+ - * /`, `sqrt`, comparisons, casts and `ofRat` on literal words in the kernel. FloatLib's tests do the same, and the corpus does it for every folded constant. Plain `decide` fails on `Id`-typed goals. | used throughout. `sqrt (ofBits 0x40800000)` and the divisions `π/180`, `180/π`, `π/18000` evaluate in well under a second. |
| tactics | `roundoff` (`BI/Automation/Roundoff.lean`; separate import, not built here), `interval` (`FloatLib/Numerics/Automation/Interval.lean`), `numerics`, `ieee_format` | none used yet. `ieee_format` is the default argument of the configured lemmas. |
| samplers | none for `Binary32` in FloatLib or Plausible. Plausible has `UInt32.Arbitrary`, but it draws mostly small words. | **Test/Edge.lean**: edge words plus an xorshift sample over all words (`sample`, `sampleBelow`) |
| C `fmodf`, `asinf`, `atanf`, `tanf` | not in FloatLib (it has IEEE `remainder`, which is not C `fmod`); the code calls the musl translations `Musl.*` | named premises: `AP_Math.FmodfRange`, `AP_Math.AsinfRange`, `Control.AtanfNotNaN` |

## Memory (for Machine/Memory)

Core's `ByteArray` lemmas (`Init/Data/ByteArray/Lemmas.lean`) are stated for `getElem!` and `ByteArray.copySlice_eq_append`,
not for the `get!` the code uses. `Corpus/Machine/Memory.lean` proves the code-facing forms through `Array`:
`get!_eq`, `get!_set!`, `get!_copySlice`, `get!_extract`, `size_copySlice`, and `bytes32` (the four little-endian bytes
reassemble the word, proved bit by bit with `interval_cases`; `bv_decide` would add the axiom `Lean.ofReduceBool`).

## Second increment (2026-11-16): what `Machine/Float` now proves from FloatLib's internals

The table's "Not in the library" entries for signs, negation and exactness are closed in `Corpus/Machine/Float.lean`,
section "Rounding with overflow, negation, signs". The FloatLib names they rest on:

| Need | FloatLib (file) | Corpus |
|---|---|---|
| a nearest rounding's sign bit | `Model.roundDyadic_eq_internal`, `Model.Internal.ieeeRoundDyadic` (`Dyadic/RoundingKernel/{Proof,Runtime}.lean`): every leaf is a zero, an infinity or `ofFields` with the dyadic's sign | `signBit_roundDyadic`, `neg_roundDyadic` (by `split_ifs` over the rounder's branches) |
| the overflow threshold | the same rounder; `Model.roundAt_dyadic_eq` (`Rounding/Proof.lean`, the unbounded rounding as `±rounded · 2^target`), `targetExponent_eq_normal`, `roundMantissaAtExponentEven_eq_roundMantissaToLeadingBitEven`, `pow2_le_roundMantissaToLeadingBitEven` (`ModelRounding/Proof.lean`), `toReal_posMaxFinite_lt_bpow` | `isFinite_roundDyadic_of_abs_roundAt_le`: infinite only when `|roundAt r| ≥ 2^128 > FLT_MAX` |
| a rounded value as an extended real | `Model.toReal_roundDyadic_eq_roundAt`, `Model.isNaN_roundDyadic_eq_false`, `Model.roundAt_neg`, `Model.roundAt_mono` | `rnd` (proof-side: `roundAt r` in range, else `±∞` by the sign of `r`), `toEReal_roundDyadic`, `rnd_mono`, `rnd_neg` |
| `* + -` on finite operands | `Model.Proof.mul_eq_spec`/`add_eq_spec`/`sub_eq_spec`, `Model.Spec.mul`/`add`/`sub` (`Spec/Dyadic.lean`), `Model.Dyadic.toReal_mul`, `toReal_addDyadic` (`Model/RealSemantics.lean`) | `ext_mul_of_isFinite`, `ext_add_of_isFinite`, `ext_sub_of_isFinite` (`ext (x ∘ y) = rnd (real x ∘ real y)`) |
| infinite operands | `Model.Spec.mul`/`add` second branches, `Model.chooseNaN2_eq_none_iff`, `toDyadic?_eq_none_of_isInf_eq_true` | `model_mul_of_isInf_left/right`, `model_add_of_isInf_left/right`, `mul_of_isInf_of_pos/neg`, `add_of_isInf_left/right`, `sub_of_isInf_left/right` |
| negation | `Model.toDyadic?_neg_of_toDyadic?_some`, `Model.negDyadic`, `Model.neg_ofFields_of_supportsSignedZero`, `Model.neg_posInf/negInf/posZero`, `Model.roundRatScaled_true_eq_neg_false` (`DirectedSemantics/Rational/RoundingSemantics/RoundedReal.lean`) | `neg_mul'`, `mul_neg'`, `neg_div'`, `isNaN_neg_mul`, `isNaN_mul_neg`, `isNaN_neg_div`, `abs_neg'` |
| quotient signs | `Model.Spec.div` (`Spec/Division.lean`), `Model.ieeeRoundRatScaled` (`Dyadic/Rational.lean`), `isNaN_roundRatScaled_eq_false` | `signBit_roundRatScaled`, `div_nonneg_of_pos` |
| exact doubling | `generic_format_FLT_iff` (`Flocq/Theory/Format/Theorems.lean`), `Model.toReal_genericFormat_of_isFinite`, `Model.roundAt_of_genericFormat` | `genericFormat_two_mul`, `roundAt_two_mul`, `midpoint_mem` |
| NaN propagation | `Model.isNaN_of_chooseNaN2_eq_some`, `toDyadic?_eq_none_of_isNaN` | `isNaN_mul_of_isNaN`, `isNaN_add_of_isNaN`, `isNaN_sub_of_isNaN`, `isNaN_div_of_isNaN` |

Pitfall (new): a tactic proof term inside `first | … | …` whose `by decide +kernel` arguments are elaborated before
unification fails silently and falls through; give the implicit arguments explicitly (`ext_of_isNaN (x := …)`) or
state a small lemma whose statement fixes them (`nan_case`). And `decide +kernel` on `Binary32` subtraction of
infinities inside one large `first` block timed out at 200000 heartbeats; split such cases into their own lemmas.
