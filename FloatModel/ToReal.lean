/-
Exact real semantics for Lean's `Float` via the bit-level model `Float.Model`
(Lean ≥ 4.33, `Init/Data/Float/Model`).

`Float.toReal x` is the exact real value `± m · 2^e` of the unpacked binary64 float,
with NaN and infinities sent to `0`.
-/
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.Field.Power
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.GCongr

open Float.Model UnpackedFloat

namespace Float.Model.UnpackedFloat

/-- Canonical binary64 form, as produced by `unpack`: either a normal number
(`2^52 ≤ m < 2^53`, `-1074 ≤ e ≤ 971`) or a subnormal one (`m < 2^52`, `e = -1074`). -/
def Canonical : UnpackedFloat → Prop
  | .finite _ m e _ => -1074 ≤ e ∧ e ≤ 971 ∧ m < 2 ^ 53 ∧ (-1074 < e → 2 ^ 52 ≤ m)
  | _ => True

/-- Exact real value of an unpacked float; NaN and infinities go to `0`. -/
noncomputable def toReal : UnpackedFloat → ℝ
  | .finite s m e _ => ((s.apply (m : ℤ) : ℤ) : ℝ) * (2 : ℝ) ^ e
  | _ => 0

theorem one_append_toNat (v : BitVec 52) : (1#1 ++ v).toNat = 2 ^ 52 + v.toNat := by
  rw [BitVec.toNat_append, ← Nat.shiftLeft_add_eq_or_of_lt v.isLt]
  simp [Nat.shiftLeft_eq]

/-- Every float produced by `unpack` is in canonical binary64 form. -/
theorem unpack_canonical (b : BitVec 64) : Canonical (unpack Format.binary64 b) := by
  have hm := (unpackMantissa (spec := Format.binary64) b).isLt
  have he := (unpackExponent (spec := Format.binary64) b).isLt
  simp only [unpack]
  split_ifs with h1 h2 h3 h4
  · trivial
  · trivial
  · trivial
  · simp only [Canonical]
    simp only [h3, BitVec.toNat_zero] at *
    refine ⟨by decide, by decide, by omega, fun h => absurd h (by decide)⟩
  · simp only [Canonical]
    have hne1 : (unpackExponent (spec := Format.binary64) b).toNat ≠ 2047 := by
      intro h; apply h1; apply BitVec.eq_of_toNat_eq; simp [h]
    have hne0 : (unpackExponent (spec := Format.binary64) b).toNat ≠ 0 := by
      intro h; apply h3; apply BitVec.eq_of_toNat_eq; simp [h]
    rw [one_append_toNat]
    simp only [Format.exponentBias]
    norm_num at he hm ⊢
    omega

@[simp] theorem unpackSign_packComponents {spec : Format} {sign exponent mantissa} :
    unpackSign (packComponents spec sign exponent mantissa) = sign.toBitVec := by
  ext i hi
  have : i = 0 := by omega
  subst this
  simp [unpackSign, packComponents, BitVec.getLsbD_eq_getElem, BitVec.getLsbD_append, BitVec.getElem_append]

@[simp] theorem Sign.ofBitVec_toBitVec (s : Sign) : Sign.ofBitVec s.toBitVec = s := by
  cases s <;> rfl

theorem unpack_pack_zero (s : Sign) :
    unpack Format.binary64 (pack Format.binary64 (.zero s)) = .zero s := by
  simp [pack, packedZero, unpack]

theorem unpack_pack_finite (s : Sign) (m : Nat) (e : Int) (hm : 0 < m)
    (h : Canonical (.finite s m e hm)) :
    unpack Format.binary64 (pack Format.binary64 (.finite s m e hm)) = .finite s m e hm := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  simp only [pack]
  have hb : (e + ↑Format.binary64.exponentBias + ↑Format.binary64.mantissaBitsWithoutImplicit).toNat
      = (e + 1075).toNat := by simp [Format.exponentBias]; congr 1; omega
  rw [hb]
  rw [if_neg (by simp; omega)]
  by_cases hn : 2 ^ 52 ≤ m
  · have hlog : m.log2 = 52 := (Nat.log2_eq_iff (by omega)).2 ⟨hn, h3⟩
    rw [if_pos (by simp [hlog, Format.mantissaBits])]
    simp only [unpack, unpackMantissa_packComponents, unpackExponent_packComponents,
      unpackSign_packComponents, Sign.ofBitVec_toBitVec]
    have hE : (BitVec.ofNat 11 (e + 1075).toNat) ≠ -1#11 := by
      intro hc; have := congrArg BitVec.toNat hc; simp at this; omega
    have hE0 : (BitVec.ofNat 11 (e + 1075).toNat) ≠ 0#11 := by
      intro hc; have := congrArg BitVec.toNat hc; simp at this; omega
    rw [if_neg hE, if_neg hE0]
    simp only [finite.injEq, true_and]
    constructor
    · rw [one_append_toNat]; simp; omega
    · simp [Format.exponentBias]; omega
  · have he : e = -1074 := by by_contra hc; exact hn (h4 (by omega))
    subst he
    have hlog : m.log2 < 52 := (Nat.log2_lt (by omega)).2 (by omega)
    rw [if_neg (by simp [Format.mantissaBits]; omega)]
    simp only [unpack, unpackMantissa_packComponents, unpackExponent_packComponents,
      unpackSign_packComponents, Sign.ofBitVec_toBitVec]
    have hM : (BitVec.ofNat 52 m) ≠ 0#52 := by
      intro hc; have := congrArg BitVec.toNat hc; simp at this; omega
    simp [hM, Format.exponentBias]
    omega

theorem unpack_pack_infinity (s : Sign) :
    unpack Format.binary64 (pack Format.binary64 (.infinity s)) = .infinity s := by
  simp [pack, packedInfinity, unpack]

theorem unpack_pack_notANumber :
    unpack Format.binary64 (pack Format.binary64 .notANumber) = .notANumber := by
  simp [pack, packedNaN, unpack]

theorem canonical_neg {u : UnpackedFloat} (h : Canonical u) : Canonical u.neg := by
  cases u <;> simp_all [Canonical, neg]

/-- Packing then unpacking is the identity on canonical floats. -/
theorem unpack_pack_of_canonical {u : UnpackedFloat} (h : Canonical u) :
    unpack Format.binary64 (pack Format.binary64 u) = u := by
  cases u with
  | infinity s => exact unpack_pack_infinity s
  | notANumber => exact unpack_pack_notANumber
  | zero s => exact unpack_pack_zero s
  | finite s m e hm => exact unpack_pack_finite s m e hm h

@[simp] theorem Sign.neg_positive : -Sign.positive = Sign.negative := rfl
@[simp] theorem Sign.neg_negative : -Sign.negative = Sign.positive := rfl

theorem toReal_neg (u : UnpackedFloat) : u.neg.toReal = - u.toReal := by
  cases u with
  | finite s m e hm => cases s <;> simp [neg, toReal, Sign.apply]
  | _ => simp [neg, toReal]

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
