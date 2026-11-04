/-
Axiom check for the float library and the binary32 clip.

One `#print axioms` line per theorem of `FloatModel.*` (format-generic lemmas, the binary64
instance, the binary32 instance) and of `Contracts.Float32Clip`; each must show at most
`propext`, `Classical.choice`, `Quot.sound`. The final command `#assert_standard_axioms` enforces
this at build time: it walks every theorem declared in these modules (not only the listed ones)
and fails the build if any depends on another axiom (`sorryAx`, a custom `axiom`,
`Lean.ofReduceBool`).
-/
import FloatModel.Float32
import Contracts.Float32Clip

-- FloatModel/ToReal.lean
#print axioms Float.Model.Format.mantissaBits_eq
#print axioms Float.Model.Format.two_le_mantissaBits
#print axioms Float.Model.Format.exponentBias_add_one
#print axioms Float.Model.Format.two_pow_exponentBits
#print axioms Float.Model.Format.minExponent_eq
#print axioms Float.Model.Format.normExponent_eq
#print axioms Float.Model.Format.one_le_exponentBias
#print axioms Float.Model.UnpackedFloat.one_append_toNat
#print axioms Float.Model.UnpackedFloat.toNat_neg_one
#print axioms Float.Model.UnpackedFloat.two_pow_mantissaBits
#print axioms Float.Model.UnpackedFloat.unpack_canonicalIn
#print axioms Float.Model.UnpackedFloat.unpackSign_packComponents
#print axioms Float.Model.UnpackedFloat.Sign.ofBitVec_toBitVec
#print axioms Float.Model.UnpackedFloat.neg_one_ne_zero
#print axioms Float.Model.UnpackedFloat.unpack_pack_zeroIn
#print axioms Float.Model.UnpackedFloat.unpack_pack_finiteIn
#print axioms Float.Model.UnpackedFloat.unpack_pack_infinityIn
#print axioms Float.Model.UnpackedFloat.unpack_pack_notANumberIn
#print axioms Float.Model.UnpackedFloat.canonicalIn_neg
#print axioms Float.Model.UnpackedFloat.unpack_pack_of_canonicalIn
#print axioms Float.Model.UnpackedFloat.Sign.neg_positive
#print axioms Float.Model.UnpackedFloat.Sign.neg_negative
#print axioms Float.Model.UnpackedFloat.toReal_neg
#print axioms Float.Model.UnpackedFloat.canonical_iff
#print axioms Float.Model.UnpackedFloat.unpack_canonical
#print axioms Float.Model.UnpackedFloat.unpack_pack_zero
#print axioms Float.Model.UnpackedFloat.unpack_pack_finite
#print axioms Float.Model.UnpackedFloat.unpack_pack_infinity
#print axioms Float.Model.UnpackedFloat.unpack_pack_notANumber
#print axioms Float.Model.UnpackedFloat.canonical_neg
#print axioms Float.Model.UnpackedFloat.unpack_pack_of_canonical
#print axioms Float.Model.unpack_canonical
#print axioms Float.Model.unpack_pack_of_canonical
#print axioms Float.isFinite_iff
#print axioms Float.toModel_unpack_zero
#print axioms Float.toModel_unpack_one
#print axioms Float.toModel_unpack_half
#print axioms Float.toReal_zero
#print axioms Float.toReal_one
#print axioms Float.toReal_half
#print axioms Float.isFinite_zero
#print axioms Float.isFinite_one
#print axioms Float.isFinite_half
#print axioms Float.toModel_neg_unpack
#print axioms Float.toReal_neg
#print axioms Float.toReal_neg_of_isFinite
#print axioms Float.isFinite_neg

-- FloatModel/Order.lean
#print axioms Float.Model.UnpackedFloat.compare_real_eq_iff
#print axioms Float.Model.UnpackedFloat.mag_pos
#print axioms Float.Model.UnpackedFloat.mag_lt_of_exp_lt
#print axioms Float.Model.UnpackedFloat.lex_eq_compare_mag
#print axioms Float.Model.UnpackedFloat.compare_neg_neg
#print axioms Float.Model.UnpackedFloat.toReal_finite_positive
#print axioms Float.Model.UnpackedFloat.toReal_finite_negative
#print axioms Float.Model.UnpackedFloat.compare_eq_some_compare_toReal
#print axioms Float.Model.UnpackedFloat.lt_eq_true_iff
#print axioms Float.Model.UnpackedFloat.le_eq_true_iff
#print axioms Float.Model.UnpackedFloat.beq_eq_true_iff
#print axioms Float.lt_iff_unpack
#print axioms Float.le_iff_unpack
#print axioms Float.canonicalIn_unpack
#print axioms Float.compare_toModel_unpack
#print axioms Float.lt_iff_toReal_lt
#print axioms Float.le_iff_toReal_le
#print axioms Float.decide_lt_eq
#print axioms Float.decide_le_eq
#print axioms Float.beq_iff_toReal_eq

-- FloatModel/Add.lean
#print axioms Float.Model.UnpackedFloat.ExtendedMantissa.shiftRight_succ
#print axioms Float.Model.UnpackedFloat.ExtendedMantissa.shiftRight_zero
#print axioms Float.Model.UnpackedFloat.ExtendedMantissa.mantissa_shiftRight
#print axioms Float.Model.UnpackedFloat.ExtendedMantissa.shift_spec
#print axioms Float.Model.UnpackedFloat.ExtendedMantissa.round_shift
#print axioms Float.Model.Format.minExponent_nonpos
#print axioms Float.Model.UnpackedFloat.mkFin_pos
#print axioms Float.Model.UnpackedFloat.roundWithAccuracy_eq_mkFin
#print axioms Float.Model.UnpackedFloat.shiftToTargetExponent_exact
#print axioms Float.Model.UnpackedFloat.shiftToTargetExponent_binary64
#print axioms Float.Model.UnpackedFloat.roundWithAccuracy_exact_spec
#print axioms Float.Model.UnpackedFloat.maxFinite_eq_in
#print axioms Float.Model.UnpackedFloat.two_zpow_pos
#print axioms Float.Model.UnpackedFloat.two_pow_mul_two_zpow_neg
#print axioms Float.Model.UnpackedFloat.two_zpow_neg_mantissaBits
#print axioms Float.Model.UnpackedFloat.maxFiniteIn_mul_lt
#print axioms Float.Model.UnpackedFloat.maxFinite_mul_lt
#print axioms Float.Model.UnpackedFloat.roundWithAccuracy_exact_real
#print axioms Float.Model.UnpackedFloat.log2_mul_two_pow
#print axioms Float.Model.UnpackedFloat.mag_mul_two_pow
#print axioms Float.Model.UnpackedFloat.round_shift_amount
#print axioms Float.Model.UnpackedFloat.round_real
#print axioms Float.Model.UnpackedFloat.toReal_finite
#print axioms Float.Model.UnpackedFloat.Sign.abs_toReal
#print axioms Float.Model.UnpackedFloat.Sign.toReal_mul
#print axioms Float.Model.UnpackedFloat.Sign.toReal_neg
#print axioms Float.Model.UnpackedFloat.signed_bound
#print axioms Float.Model.UnpackedFloat.goodRound_iff
#print axioms Float.Model.UnpackedFloat.goodRoundIn_finite_round
#print axioms Float.Model.UnpackedFloat.goodRoundIn_normalize
#print axioms Float.Model.UnpackedFloat.goodRound_normalize
#print axioms Float.Model.UnpackedFloat.apply_shift_toReal
#print axioms Float.Model.UnpackedFloat.goodRoundIn_of_exact
#print axioms Float.Model.UnpackedFloat.not_tiny_zero
#print axioms Float.Model.UnpackedFloat.add_key
#print axioms Float.Model.UnpackedFloat.sub_key
#print axioms Float.Model.UnpackedFloat.goodRoundIn_add
#print axioms Float.Model.UnpackedFloat.goodRoundIn_sub
#print axioms Float.Model.UnpackedFloat.mag_mul
#print axioms Float.Model.UnpackedFloat.mul_key
#print axioms Float.Model.UnpackedFloat.abs_sign_mag
#print axioms Float.Model.UnpackedFloat.mul_log2_or
#print axioms Float.Model.UnpackedFloat.goodRoundIn_mul
#print axioms Float.Model.UnpackedFloat.goodRound_finite_round
#print axioms Float.Model.UnpackedFloat.goodRound_of_exact
#print axioms Float.Model.UnpackedFloat.goodRound_add
#print axioms Float.Model.UnpackedFloat.goodRound_sub
#print axioms Float.Model.UnpackedFloat.goodRound_mul
#print axioms Float.Model.UnpackedFloat.maxFiniteIn_nonneg
#print axioms Float.Model.UnpackedFloat.abs_toReal_le_maxFiniteIn
#print axioms Float.goodRoundIn_transfer
#print axioms Float.goodRound_transfer
#print axioms Float.add_error
#print axioms Float.sub_error
#print axioms Float.mul_error
#print axioms Float.std_model
#print axioms Float.add_std_model
#print axioms Float.sub_std_model
#print axioms Float.mul_std_model
#print axioms Float.abs_toReal_le_maxFinite
#print axioms Float.maxFinite_eq

-- FloatModel/Small.lean
#print axioms Float.Model.UnpackedFloat.roundWithAccuracy_small
#print axioms Float.Model.UnpackedFloat.toReal_mkFin
#print axioms Float.Model.UnpackedFloat.isFinite_mkFin
#print axioms Float.Model.UnpackedFloat.canonicalIn_mkFin
#print axioms Float.Model.UnpackedFloat.log2_add_le_of_small
#print axioms Float.Model.UnpackedFloat.small_real_bound
#print axioms Float.Model.UnpackedFloat.round_small
#print axioms Float.Model.UnpackedFloat.exactRoundIn_normalize
#print axioms Float.Model.UnpackedFloat.goodRoundIn_normalize_all
#print axioms Float.Model.UnpackedFloat.goodRound_normalize_all
#print axioms Float.Model.UnpackedFloat.exactRoundIn_sub
#print axioms Float.Model.UnpackedFloat.exactRoundIn_add
#print axioms Float.Model.UnpackedFloat.smallRoundIn_of_exact
#print axioms Float.Model.UnpackedFloat.smallRoundIn_mul
#print axioms Float.Model.UnpackedFloat.canonical_mkFin
#print axioms Float.Model.UnpackedFloat.exactRound_iff
#print axioms Float.Model.UnpackedFloat.exactRound_normalize
#print axioms Float.Model.UnpackedFloat.exactRound_sub
#print axioms Float.Model.UnpackedFloat.exactRound_add
#print axioms Float.Model.UnpackedFloat.smallRound_iff
#print axioms Float.Model.UnpackedFloat.smallRound_of_exact
#print axioms Float.Model.UnpackedFloat.smallRound_mul
#print axioms Float.exactRoundIn_transfer
#print axioms Float.smallRoundIn_transfer
#print axioms Float.exactRound_transfer
#print axioms Float.smallRound_transfer
#print axioms Float.sub_error_small
#print axioms Float.add_error_small
#print axioms Float.mul_error_small
#print axioms Float.sub_err_all
#print axioms Float.add_err_all
#print axioms Float.mul_err_all

-- FloatModel/DivSqrt.lean
#print axioms Float.Model.UnpackedFloat.cons_shiftRightOne
#print axioms Float.Model.UnpackedFloat.cons_shiftRight
#print axioms Float.Model.UnpackedFloat.cons_ofMA
#print axioms Float.Model.UnpackedFloat.round_cons
#print axioms Float.Model.UnpackedFloat.accOK_bounds
#print axioms Float.Model.UnpackedFloat.shiftToTarget_eq
#print axioms Float.Model.UnpackedFloat.roundWithAccuracy_struct
#print axioms Float.Model.UnpackedFloat.roundWithAccuracy_real
#print axioms Float.Model.UnpackedFloat.accOK_frac
#print axioms Float.Model.UnpackedFloat.divCore_spec
#print axioms Float.Model.UnpackedFloat.sign_div_toReal
#print axioms Float.Model.UnpackedFloat.nearRoundIn_of_exact
#print axioms Float.Model.UnpackedFloat.nearRoundIn_div
#print axioms Float.Model.UnpackedFloat.accOK_sqrt
#print axioms Float.Model.UnpackedFloat.sqrtCore_spec
#print axioms Float.Model.UnpackedFloat.nearRoundIn_sqrt
#print axioms Float.nearRoundIn_transfer
#print axioms Float.one_le_maxFinite
#print axioms Float.div_err_all
#print axioms Float.sqrt_err_all

-- FloatModel/Bracket.lean
#print axioms Float.Model.UnpackedFloat.bracketIn_of_eq
#print axioms Float.Model.UnpackedFloat.nearest_grid_le
#print axioms Float.Model.UnpackedFloat.nearest_grid_ge
#print axioms Float.Model.UnpackedFloat.toReal_finite_grid
#print axioms Float.Model.UnpackedFloat.bracket_mag
#print axioms Float.Model.UnpackedFloat.bracketIn_signed
#print axioms Float.Model.UnpackedFloat.bracketIn_roundWithAccuracy
#print axioms Float.Model.UnpackedFloat.bracketIn_round
#print axioms Float.Model.UnpackedFloat.bracketIn_normalize
#print axioms Float.Model.UnpackedFloat.bracketIn_add
#print axioms Float.Model.UnpackedFloat.bracketIn_sub
#print axioms Float.Model.UnpackedFloat.bracketIn_mul
#print axioms Float.Model.UnpackedFloat.bracketIn_div
#print axioms Float.Model.UnpackedFloat.bracketIn_sqrt
#print axioms Float.Model.UnpackedFloat.canonicalIn_add_all
#print axioms Float.Model.UnpackedFloat.canonicalIn_sub_all
#print axioms Float.Model.UnpackedFloat.canonicalIn_mul_all
#print axioms Float.Model.UnpackedFloat.exists_double
#print axioms Float.toReal_of_toModel
#print axioms Float.isFinite_of_isFinite_unpack
#print axioms Float.bracket_transfer
#print axioms Float.add_bracket
#print axioms Float.sub_bracket
#print axioms Float.mul_bracket
#print axioms Float.div_bracket
#print axioms Float.sqrt_bracket

-- FloatModel/Float32.lean
#print axioms Float.Model.UnpackedFloat.canonical32_iff
#print axioms Float.Model.UnpackedFloat.maxFinite32_eq_in
#print axioms Float.Model.UnpackedFloat.maxFinite32_mul_lt
#print axioms Float32.Model.unpack_canonicalIn
#print axioms Float32.Model.unpack_canonical32
#print axioms Float32.Model.unpack_pack_of_canonicalIn
#print axioms Float32.Model.unpack_pack_of_canonical32
#print axioms Float32.isFinite_iff
#print axioms Float32.canonicalIn_unpack
#print axioms Float32.toModel_unpack_zero
#print axioms Float32.toModel_unpack_one
#print axioms Float32.toModel_unpack_half
#print axioms Float32.toReal_zero
#print axioms Float32.toReal_one
#print axioms Float32.toReal_half
#print axioms Float32.isFinite_zero
#print axioms Float32.isFinite_one
#print axioms Float32.isFinite_half
#print axioms Float32.toModel_neg_unpack
#print axioms Float32.toReal_neg
#print axioms Float32.isFinite_neg
#print axioms Float32.abs_toReal_le_maxFinite
#print axioms Float32.maxFinite32_eq
#print axioms Float32.lt_iff_unpack
#print axioms Float32.le_iff_unpack
#print axioms Float32.compare_toModel_unpack
#print axioms Float32.lt_iff_toReal_lt
#print axioms Float32.le_iff_toReal_le
#print axioms Float32.decide_lt_eq
#print axioms Float32.decide_le_eq
#print axioms Float32.beq_iff_toReal_eq
#print axioms Float32.of_pack
#print axioms Float32.goodRoundIn_transfer
#print axioms Float32.exactRoundIn_transfer
#print axioms Float32.smallRoundIn_transfer
#print axioms Float32.nearRoundIn_transfer
#print axioms Float32.add_error
#print axioms Float32.sub_error
#print axioms Float32.mul_error
#print axioms Float32.add_std_model
#print axioms Float32.sub_std_model
#print axioms Float32.mul_std_model
#print axioms Float32.sub_error_small
#print axioms Float32.add_error_small
#print axioms Float32.mul_error_small
#print axioms Float32.sub_err_all
#print axioms Float32.add_err_all
#print axioms Float32.mul_err_all
#print axioms Float32.one_le_maxFinite32
#print axioms Float32.div_err_all
#print axioms Float32.sqrt_err_all
#print axioms Float32.toReal_of_toModel
#print axioms Float32.exists_of_canonicalIn
#print axioms Float32.exists_double
#print axioms Float32.bracket_transfer
#print axioms Float32.add_bracket
#print axioms Float32.sub_bracket
#print axioms Float32.mul_bracket
#print axioms Float32.div_bracket
#print axioms Float32.sqrt_bracket

-- Contracts/Float32Clip.lean
#print axioms Contracts.Float32Clip.isNaN_iff
#print axioms Contracts.Float32Clip.isFinite_of_le_of_not_le
#print axioms Contracts.Float32Clip.isFinite_of_not_lt_of_not_lt
#print axioms Contracts.Float32Clip.not_isNaN_of_isFinite
#print axioms Contracts.Float32Clip.clip_eq
#print axioms Contracts.Float32Clip.clip_spec
#print axioms Contracts.Float32Clip.clip_toReal
#print axioms Contracts.Float32Clip.toModel_unpack_two
#print axioms Contracts.Float32Clip.isFinite_two
#print axioms Contracts.Float32Clip.toReal_two
#print axioms Contracts.Float32Clip.midpoint_spec
#print axioms Contracts.Float32Clip.constrain_float_spec_of_not_isNaN
#print axioms Contracts.Float32Clip.constrain_float_spec
#print axioms Contracts.Float32Clip.constrain_float_toReal
#print axioms Contracts.Float32Clip.constrain_float_eq_clip
#print axioms Contracts.Float32Clip.constrain_float_nan_overflow

open Lean Elab Command in
/-- Fail unless every theorem declared in a `FloatModel.*` module or in `Contracts.Float32Clip`
depends only on `propext`, `Classical.choice`, `Quot.sound`. -/
elab "#assert_standard_axioms" : command => do
  let env ← getEnv
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let inScope (m : Name) : Bool :=
    (`FloatModel).isPrefixOf m || m == `Contracts.Float32Clip
  let mut bad : Array (Name × Array Name) := #[]
  let mut count : Nat := 0
  for (n, ci) in env.constants.map₁.toList do
    if let .thmInfo _ := ci then
      if let some idx := env.getModuleIdxFor? n then
        if inScope env.header.moduleNames[idx.toNat]! && !n.isInternal then
          count := count + 1
          let axs ← liftCoreM (Lean.collectAxioms n)
          let extra := axs.filter (fun a => !allowed.contains a)
          if !extra.isEmpty then bad := bad.push (n, extra)
  if bad.isEmpty then
    logInfo m!"{count} theorems checked: only propext, Classical.choice, Quot.sound"
  else
    throwError m!"nonstandard axioms: {bad}"

#assert_standard_axioms
