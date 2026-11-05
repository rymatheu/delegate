module

/-
Exact real semantics for Lean's floats via the bit-level model (Lean ≥ 4.33,
`Init/Data/Float/Model`), generic over the IEEE format.

`UnpackedFloat.toReal u` is the exact real value `± m · 2^e` of an unpacked float, with NaN and
infinities sent to `0`. `CanonicalIn spec` is the shape that `unpack spec` produces for a format
`spec : Format` with `k = spec.mantissaBitsWithoutImplicit` stored mantissa bits: a normal number
(`2^k ≤ m < 2^(k+1)`, `minExponent ≤ e ≤ maxExponent`) or a subnormal one (`m < 2^k`,
`e = minExponent`). Packing then unpacking is the identity on it (`unpack_pack_of_canonicalIn`).

The binary64 instance (`Canonical`, `Float.toReal`, `Float.IsFinite`, the literal lemmas) is at the
end of this file; the binary32 reading (`Float32.toReal`, `Float32.IsFinite`) is in
`FloatModel.Float32`.
-/
public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.Order.Field.Power
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.GCongr

@[expose] public section

open Float.Model UnpackedFloat

namespace Float.Model.Format

/-- Largest exponent of a finite float in unpacked form: `971` for binary64, `104` for binary32.
The largest finite value is `(2^mantissaBits - 1) · 2^maxExponent`. -/
def maxExponent (spec : Format) : Int := spec.exponentBias - spec.mantissaBitsWithoutImplicit

/-- Exponent of the smallest normal number: `-1022` for binary64, `-126` for binary32. -/
def normExponent (spec : Format) : Int := spec.minExponent + spec.mantissaBits - 1

theorem mantissaBits_eq (spec : Format) :
    spec.mantissaBits = spec.mantissaBitsWithoutImplicit + 1 := Nat.add_comm _ _

theorem two_le_mantissaBits (spec : Format) : 2 ≤ spec.mantissaBits := by
  have := spec.hm; rw [mantissaBits_eq]; omega

theorem exponentBias_add_one (spec : Format) :
    spec.exponentBias + 1 = 2 ^ (spec.exponentBits - 1) := by
  have : 1 ≤ 2 ^ (spec.exponentBits - 1) := Nat.one_le_two_pow
  simp only [exponentBias]; omega

theorem two_pow_exponentBits (spec : Format) :
    2 ^ spec.exponentBits = 2 * spec.exponentBias + 2 := by
  have h := exponentBias_add_one spec
  have : 2 ^ spec.exponentBits = 2 * 2 ^ (spec.exponentBits - 1) := by
    rw [← Nat.pow_succ']; congr 1; have := spec.he; omega
  omega

theorem minExponent_eq (spec : Format) :
    spec.minExponent = 1 - (spec.exponentBias : Int) - spec.mantissaBitsWithoutImplicit := by
  have h := exponentBias_add_one spec
  have h' : ((2 ^ (spec.exponentBits - 1) : Nat) : Int) = (spec.exponentBias : Int) + 1 := by
    rw [← h]; push_cast; ring
  simp only [minExponent, mantissaBits]
  push_cast at h' ⊢
  omega

theorem normExponent_eq (spec : Format) :
    spec.normExponent = spec.minExponent + spec.mantissaBitsWithoutImplicit := by
  simp only [normExponent, mantissaBits]; push_cast; ring

theorem one_le_exponentBias (spec : Format) (hw : 2 ≤ spec.exponentBits) :
    1 ≤ spec.exponentBias := by
  have := exponentBias_add_one spec
  have : 2 ≤ 2 ^ (spec.exponentBits - 1) := by
    calc 2 = 2 ^ 1 := rfl
      _ ≤ _ := Nat.pow_le_pow_right (by norm_num) (by omega)
  omega

end Float.Model.Format

namespace Float.Model.UnpackedFloat

/-! ## Canonical form for a format -/

/-- Canonical form for the format `spec`, as produced by `unpack spec`: a normal number
(`2^k ≤ m < 2^(k+1)`, `minExponent ≤ e ≤ maxExponent`, with `k` the stored mantissa bits) or a
subnormal one (`m < 2^k`, `e = minExponent`). -/
def CanonicalIn (spec : Format) : UnpackedFloat → Prop
  | .finite _ m e _ => spec.minExponent ≤ e ∧ e ≤ spec.maxExponent ∧
      m < 2 ^ spec.mantissaBits ∧ (spec.minExponent < e → 2 ^ spec.mantissaBitsWithoutImplicit ≤ m)
  | _ => True

/-- Exact real value of an unpacked float; NaN and infinities go to `0`. -/
noncomputable def toReal : UnpackedFloat → ℝ
  | .finite s m e _ => ((s.apply (m : ℤ) : ℤ) : ℝ) * (2 : ℝ) ^ e
  | _ => 0

theorem one_append_toNat {k : Nat} (v : BitVec k) : (1#1 ++ v).toNat = 2 ^ k + v.toNat := by
  rw [BitVec.toNat_append, ← Nat.shiftLeft_add_eq_or_of_lt v.isLt]
  simp [Nat.shiftLeft_eq]

theorem toNat_neg_one (w : Nat) : (-1#w).toNat = 2 ^ w - 1 := by
  rw [BitVec.neg_one_eq_allOnes, BitVec.toNat_allOnes]

theorem two_pow_mantissaBits (spec : Format) :
    2 ^ spec.mantissaBits = 2 * 2 ^ spec.mantissaBitsWithoutImplicit := by
  rw [Format.mantissaBits_eq, Nat.pow_succ]; ring

/-- Every float produced by `unpack spec` is in canonical form for `spec` (for any format with
at least two exponent bits). -/
theorem unpack_canonicalIn (spec : Format) (hw : 2 ≤ spec.exponentBits) (b : BitVec spec.numBits) :
    CanonicalIn spec (unpack spec b) := by
  have hm := (unpackMantissa (spec := spec) b).isLt
  have he := (unpackExponent (spec := spec) b).isLt
  have h2w := Format.two_pow_exponentBits spec
  have hmin := Format.minExponent_eq spec
  have hbias := Format.one_le_exponentBias spec hw
  have hP := two_pow_mantissaBits spec
  simp only [unpack]
  split_ifs with h1 h2 h3 h4
  · trivial
  · trivial
  · trivial
  · simp only [CanonicalIn, Format.maxExponent]
    simp only [h3, BitVec.toNat_zero] at *
    refine ⟨by omega, by omega, by omega, fun h => absurd h (by omega)⟩
  · simp only [CanonicalIn, Format.maxExponent]
    have hne1 : (unpackExponent (spec := spec) b).toNat ≠ 2 ^ spec.exponentBits - 1 := by
      intro h; apply h1; apply BitVec.eq_of_toNat_eq; rw [h, toNat_neg_one]
    have hne0 : (unpackExponent (spec := spec) b).toNat ≠ 0 := by
      intro h; apply h3; apply BitVec.eq_of_toNat_eq; simp [h]
    rw [one_append_toNat]
    refine ⟨by omega, by omega, by omega, fun _ => by omega⟩

@[simp] theorem unpackSign_packComponents {spec : Format} {sign exponent mantissa} :
    unpackSign (packComponents spec sign exponent mantissa) = sign.toBitVec := by
  ext i hi
  have : i = 0 := by omega
  subst this
  simp [unpackSign, packComponents, BitVec.getLsbD_eq_getElem, BitVec.getLsbD_append, BitVec.getElem_append]

@[simp] theorem Sign.ofBitVec_toBitVec (s : Sign) : Sign.ofBitVec s.toBitVec = s := by
  cases s <;> rfl

theorem neg_one_ne_zero {w : Nat} (hw : 2 ≤ w) : (-1#w) ≠ 0#w := by
  intro h
  have := congrArg BitVec.toNat h
  rw [toNat_neg_one, BitVec.toNat_zero] at this
  have : 2 ≤ 2 ^ w := by
    calc 2 = 2 ^ 1 := rfl
      _ ≤ _ := Nat.pow_le_pow_right (by norm_num) (by omega)
  omega

theorem unpack_pack_zeroIn (spec : Format) (s : Sign) :
    unpack spec (pack spec (.zero s)) = .zero s := by
  have := neg_one_ne_zero spec.he
  simp [pack, packedZero, unpack, unpackExponent_packComponents, unpackMantissa_packComponents,
    Ne.symm this]

theorem unpack_pack_finiteIn (spec : Format) (s : Sign) (m : Nat) (e : Int) (hm : 0 < m)
    (h : CanonicalIn spec (.finite s m e hm)) :
    unpack spec (pack spec (.finite s m e hm)) = .finite s m e hm := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  have h2w := Format.two_pow_exponentBits spec
  have hmin := Format.minExponent_eq spec
  have hP := two_pow_mantissaBits spec
  simp only [Format.maxExponent] at h2
  simp only [pack]
  rw [ite_eq_right (by omega)]
  by_cases hn : 2 ^ spec.mantissaBitsWithoutImplicit ≤ m
  · have hlog : m.log2 = spec.mantissaBitsWithoutImplicit :=
      (Nat.log2_eq_iff (by omega)).2 ⟨hn, by rw [Nat.pow_succ]; omega⟩
    rw [ite_eq_left (by rw [hlog, Format.mantissaBits_eq])]
    simp only [unpack, unpackMantissa_packComponents, unpackExponent_packComponents,
      unpackSign_packComponents, Sign.ofBitVec_toBitVec]
    have hlt : (e + ↑spec.exponentBias + ↑spec.mantissaBitsWithoutImplicit).toNat
        < 2 ^ spec.exponentBits := by omega
    have hE : (BitVec.ofNat spec.exponentBits
        (e + ↑spec.exponentBias + ↑spec.mantissaBitsWithoutImplicit).toNat) ≠ -1#_ := by
      intro hc; have := congrArg BitVec.toNat hc
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt, toNat_neg_one] at this; omega
    have hE0 : (BitVec.ofNat spec.exponentBits
        (e + ↑spec.exponentBias + ↑spec.mantissaBitsWithoutImplicit).toNat) ≠ 0#_ := by
      intro hc; have := congrArg BitVec.toNat hc
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt] at this; simp at this; omega
    rw [ite_eq_right hE, ite_eq_right hE0]
    simp only [finite.injEq, true_and]
    constructor
    · rw [one_append_toNat, BitVec.toNat_ofNat]
      have : m % 2 ^ spec.mantissaBitsWithoutImplicit = m - 2 ^ spec.mantissaBitsWithoutImplicit := by
        rw [Nat.mod_eq_sub_mod hn, Nat.mod_eq_of_lt (by omega)]
      omega
    · rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt]; omega
  · have he : e = spec.minExponent := by by_contra hc; exact hn (h4 (by omega))
    have hlog : m.log2 < spec.mantissaBitsWithoutImplicit := (Nat.log2_lt (by omega)).2 (by omega)
    rw [ite_eq_right (by rw [Format.mantissaBits_eq]; omega)]
    simp only [unpack, unpackMantissa_packComponents, unpackExponent_packComponents,
      unpackSign_packComponents, Sign.ofBitVec_toBitVec]
    have hM : (BitVec.ofNat spec.mantissaBitsWithoutImplicit m) ≠ 0#_ := by
      intro hc; have := congrArg BitVec.toNat hc
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at this; simp at this; omega
    rw [ite_eq_right (Ne.symm (neg_one_ne_zero spec.he)), ite_eq_left trivial, dite_eq_right hM]
    simp only [finite.injEq, true_and, BitVec.toNat_zero]
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    exact ⟨rfl, by omega⟩

theorem unpack_pack_infinityIn (spec : Format) (s : Sign) :
    unpack spec (pack spec (.infinity s)) = .infinity s := by
  simp [pack, packedInfinity, unpack, unpackExponent_packComponents, unpackMantissa_packComponents]

theorem unpack_pack_notANumberIn (spec : Format) :
    unpack spec (pack spec .notANumber) = .notANumber := by
  have hk := spec.hm
  have hne : (1#spec.mantissaBitsWithoutImplicit <<< (spec.mantissaBitsWithoutImplicit - 1)) ≠ 0#_ := by
    intro hc; have := congrArg BitVec.toNat hc
    rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, BitVec.toNat_zero] at this
    have h1 : 1 % 2 ^ spec.mantissaBitsWithoutImplicit = 1 :=
      Nat.mod_eq_of_lt (Nat.one_lt_two_pow (by omega))
    rw [h1, Nat.shiftLeft_eq, one_mul,
      Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by norm_num) (by omega))] at this
    exact absurd this (by positivity)
  simp [pack, packedNaN, unpack, unpackExponent_packComponents, unpackMantissa_packComponents, hne]

theorem canonicalIn_neg {spec : Format} {u : UnpackedFloat} (h : CanonicalIn spec u) :
    CanonicalIn spec u.neg := by
  cases u <;> simp_all [CanonicalIn, neg]

/-- Packing then unpacking is the identity on canonical floats. -/
theorem unpack_pack_of_canonicalIn {spec : Format} {u : UnpackedFloat} (h : CanonicalIn spec u) :
    unpack spec (pack spec u) = u := by
  cases u with
  | infinity s => exact unpack_pack_infinityIn spec s
  | notANumber => exact unpack_pack_notANumberIn spec
  | zero s => exact unpack_pack_zeroIn spec s
  | finite s m e hm => exact unpack_pack_finiteIn spec s m e hm h

@[simp] theorem Sign.neg_positive : -Sign.positive = Sign.negative := rfl
@[simp] theorem Sign.neg_negative : -Sign.negative = Sign.positive := rfl

theorem toReal_neg (u : UnpackedFloat) : u.neg.toReal = - u.toReal := by
  cases u with
  | finite s m e hm => cases s <;> simp [neg, toReal, Sign.apply]
  | _ => simp [neg, toReal]

/-! ## The binary64 instance -/

/-- Canonical binary64 form, as produced by `unpack`: either a normal number
(`2^52 ≤ m < 2^53`, `-1074 ≤ e ≤ 971`) or a subnormal one (`m < 2^52`, `e = -1074`). This is
`CanonicalIn Format.binary64` with the constants written out (`canonical_iff`). -/
def Canonical : UnpackedFloat → Prop
  | .finite _ m e _ => -1074 ≤ e ∧ e ≤ 971 ∧ m < 2 ^ 53 ∧ (-1074 < e → 2 ^ 52 ≤ m)
  | _ => True

theorem canonical_iff (u : UnpackedFloat) : Canonical u ↔ CanonicalIn Format.binary64 u := by
  cases u <;> exact Iff.rfl

/-- Every float produced by `unpack` is in canonical binary64 form. -/
theorem unpack_canonical (b : BitVec 64) : Canonical (unpack Format.binary64 b) :=
  (canonical_iff _).2 (unpack_canonicalIn Format.binary64 (by decide) b)

theorem unpack_pack_zero (s : Sign) :
    unpack Format.binary64 (pack Format.binary64 (.zero s)) = .zero s :=
  unpack_pack_zeroIn _ s

theorem unpack_pack_finite (s : Sign) (m : Nat) (e : Int) (hm : 0 < m)
    (h : Canonical (.finite s m e hm)) :
    unpack Format.binary64 (pack Format.binary64 (.finite s m e hm)) = .finite s m e hm :=
  unpack_pack_finiteIn _ s m e hm ((canonical_iff _).1 h)

theorem unpack_pack_infinity (s : Sign) :
    unpack Format.binary64 (pack Format.binary64 (.infinity s)) = .infinity s :=
  unpack_pack_infinityIn _ s

theorem unpack_pack_notANumber :
    unpack Format.binary64 (pack Format.binary64 .notANumber) = .notANumber :=
  unpack_pack_notANumberIn _

theorem canonical_neg {u : UnpackedFloat} (h : Canonical u) : Canonical u.neg :=
  (canonical_iff _).2 (canonicalIn_neg ((canonical_iff _).1 h))

/-- Packing then unpacking is the identity on canonical floats. -/
theorem unpack_pack_of_canonical {u : UnpackedFloat} (h : Canonical u) :
    unpack Format.binary64 (pack Format.binary64 u) = u :=
  unpack_pack_of_canonicalIn ((canonical_iff _).1 h)

end Float.Model.UnpackedFloat

namespace Float.Model

theorem unpack_canonical (f : Float.Model) : f.unpack.Canonical :=
  UnpackedFloat.unpack_canonical _

@[simp] theorem unpack_pack_of_canonical {u : UnpackedFloat} (h : u.Canonical) :
    (Float.Model.pack u).unpack = u := by
  simp [Float.Model.pack, Float.Model.unpack, UnpackedFloat.unpack_pack_of_canonical h]

end Float.Model

namespace Float

/-- Exact real value of a binary64 float: `± m · 2^e` for finite floats (with the
format's bias and implicit bit already resolved by `unpack`), `0` for NaN and `±∞`. -/
noncomputable def toReal (x : Float) : ℝ := x.toModel.unpack.toReal

/-- `x` is neither NaN nor infinite (the propositional form of `Float.isFinite`). -/
def IsFinite (x : Float) : Prop := x.isFinite = true

instance (x : Float) : Decidable x.IsFinite := inferInstanceAs (Decidable (_ = true))

theorem isFinite_iff (x : Float) : x.IsFinite ↔ x.toModel.unpack.isFinite = true := Iff.rfl

theorem toModel_unpack_zero : (0 : Float).toModel.unpack = .zero .positive := rfl
theorem toModel_unpack_one : (1 : Float).toModel.unpack = .finite .positive (2 ^ 52) (-52) (by decide) := rfl
theorem toModel_unpack_half : (0.5 : Float).toModel.unpack = .finite .positive (2 ^ 52) (-53) (by decide) := rfl

@[simp] theorem toReal_zero : (0 : Float).toReal = 0 := by
  simp [toReal, toModel_unpack_zero, UnpackedFloat.toReal]

@[simp] theorem toReal_one : (1 : Float).toReal = 1 := by
  rw [toReal, toModel_unpack_one]
  simp [UnpackedFloat.toReal, Sign.apply]
  norm_num

theorem toReal_half : (0.5 : Float).toReal = 1 / 2 := by
  rw [toReal, toModel_unpack_half]
  simp [UnpackedFloat.toReal, Sign.apply]
  norm_num

theorem isFinite_zero : (0 : Float).IsFinite := by
  simp [isFinite_iff, toModel_unpack_zero, UnpackedFloat.isFinite]

theorem isFinite_one : (1 : Float).IsFinite := by
  simp [isFinite_iff, toModel_unpack_one, UnpackedFloat.isFinite]

theorem isFinite_half : (0.5 : Float).IsFinite := by
  simp [isFinite_iff, toModel_unpack_half, UnpackedFloat.isFinite]

theorem toModel_neg_unpack (x : Float) : (-x).toModel.unpack = x.toModel.unpack.neg :=
  Float.Model.unpack_pack_of_canonical (UnpackedFloat.canonical_neg x.toModel.unpack_canonical)

/-- Negation is exact. This holds for every float, finite or not (both sides are `0` on NaN
and `±∞`). -/
@[simp] theorem toReal_neg (x : Float) : (-x).toReal = - x.toReal := by
  rw [toReal, toModel_neg_unpack, UnpackedFloat.toReal_neg, toReal]

/-- The finite-hypothesis form requested in the specification. -/
theorem toReal_neg_of_isFinite (x : Float) (_ : x.IsFinite) : (-x).toReal = - x.toReal :=
  toReal_neg x

theorem isFinite_neg (x : Float) : (-x).IsFinite ↔ x.IsFinite := by
  rw [isFinite_iff, isFinite_iff, toModel_neg_unpack]
  cases x.toModel.unpack <;> simp [UnpackedFloat.neg, UnpackedFloat.isFinite]

end Float
