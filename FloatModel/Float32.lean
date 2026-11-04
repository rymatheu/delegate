/-
The binary32 instance of the generic float library: exact real semantics and rounding bounds for
Lean's `Float32` (`Float32.Model`, `Format.binary32`: 23 stored mantissa bits, 8 exponent bits).

Constants: precision `P = 24`, unit roundoff `u = 2^-24`, smallest normal `2^-126`, subnormal
spacing `2^-149`, underflow error `η = 2^-150`, largest finite value
`maxFinite32 = (2^24 - 1) · 2^104 = (2 - 2^-23) · 2^127`.

Every theorem here is a thin wrapper around the format-generic statement in `FloatModel.ToReal`,
`Order`, `Add`, `Small`, `DivSqrt` at `spec = Format.binary32`; the per-type part is only the
passage between `Float32` and its unpacked model (`Float32.Model.unpack_pack_of_canonicalIn`).
Nothing is duplicated.
-/
import FloatModel.Bracket

open Float.Model UnpackedFloat

namespace Float.Model.UnpackedFloat

/-- Canonical binary32 form, as produced by `unpack Format.binary32`: either a normal number
(`2^23 ≤ m < 2^24`, `-149 ≤ e ≤ 104`) or a subnormal one (`m < 2^23`, `e = -149`). This is
`CanonicalIn Format.binary32` with the constants written out (`canonical32_iff`). -/
def Canonical32 : UnpackedFloat → Prop
  | .finite _ m e _ => -149 ≤ e ∧ e ≤ 104 ∧ m < 2 ^ 24 ∧ (-149 < e → 2 ^ 23 ≤ m)
  | _ => True

theorem canonical32_iff (u : UnpackedFloat) : Canonical32 u ↔ CanonicalIn Format.binary32 u := by
  cases u <;> exact Iff.rfl

/-- Largest finite binary32 value, `(2^24 - 1) · 2^104`. -/
noncomputable def maxFinite32 : ℝ := (2 ^ 24 - 1) * (2 : ℝ) ^ (104 : ℤ)

theorem maxFinite32_eq_in : maxFinite32 = maxFiniteIn Format.binary32 := rfl

theorem maxFinite32_mul_lt : maxFinite32 * (1 + 2 ^ (-24 : ℤ)) < (2 : ℝ) ^ (128 : ℤ) :=
  maxFiniteIn_mul_lt Format.binary32

end Float.Model.UnpackedFloat

namespace Float32.Model

theorem unpack_canonicalIn (f : Float32.Model) : CanonicalIn Format.binary32 f.unpack :=
  UnpackedFloat.unpack_canonicalIn Format.binary32 (by decide) _

theorem unpack_canonical32 (f : Float32.Model) : f.unpack.Canonical32 :=
  (canonical32_iff _).2 f.unpack_canonicalIn

@[simp] theorem unpack_pack_of_canonicalIn {u : UnpackedFloat} (h : CanonicalIn Format.binary32 u) :
    (Float32.Model.pack u).unpack = u := by
  simp [Float32.Model.pack, Float32.Model.unpack, UnpackedFloat.unpack_pack_of_canonicalIn h]

theorem unpack_pack_of_canonical32 {u : UnpackedFloat} (h : u.Canonical32) :
    (Float32.Model.pack u).unpack = u :=
  unpack_pack_of_canonicalIn ((canonical32_iff _).1 h)

end Float32.Model

namespace Float32

/-! ## Exact value, finiteness, literals, negation -/

/-- Exact real value of a binary32 float: `± m · 2^e` for finite floats, `0` for NaN and `±∞`. -/
noncomputable def toReal (x : Float32) : ℝ := x.toModel.unpack.toReal

/-- `x` is neither NaN nor infinite (the propositional form of `Float32.isFinite`). -/
def IsFinite (x : Float32) : Prop := x.isFinite = true

instance (x : Float32) : Decidable x.IsFinite := inferInstanceAs (Decidable (_ = true))

theorem isFinite_iff (x : Float32) : x.IsFinite ↔ x.toModel.unpack.isFinite = true := Iff.rfl

theorem canonicalIn_unpack (a : Float32) : CanonicalIn Format.binary32 a.toModel.unpack :=
  a.toModel.unpack_canonicalIn

theorem toModel_unpack_zero : (0 : Float32).toModel.unpack = .zero .positive := rfl
theorem toModel_unpack_one :
    (1 : Float32).toModel.unpack = .finite .positive (2 ^ 23) (-23) (by decide) := rfl
theorem toModel_unpack_half :
    (0.5 : Float32).toModel.unpack = .finite .positive (2 ^ 23) (-24) (by decide) := rfl

@[simp] theorem toReal_zero : (0 : Float32).toReal = 0 := by
  simp [toReal, toModel_unpack_zero, UnpackedFloat.toReal]

@[simp] theorem toReal_one : (1 : Float32).toReal = 1 := by
  rw [toReal, toModel_unpack_one]
  simp [UnpackedFloat.toReal, Sign.apply]
  norm_num

theorem toReal_half : (0.5 : Float32).toReal = 1 / 2 := by
  rw [toReal, toModel_unpack_half]
  simp [UnpackedFloat.toReal, Sign.apply]
  norm_num

theorem isFinite_zero : (0 : Float32).IsFinite := by
  simp [isFinite_iff, toModel_unpack_zero, UnpackedFloat.isFinite]

theorem isFinite_one : (1 : Float32).IsFinite := by
  simp [isFinite_iff, toModel_unpack_one, UnpackedFloat.isFinite]

theorem isFinite_half : (0.5 : Float32).IsFinite := by
  simp [isFinite_iff, toModel_unpack_half, UnpackedFloat.isFinite]

theorem toModel_neg_unpack (x : Float32) : (-x).toModel.unpack = x.toModel.unpack.neg :=
  Float32.Model.unpack_pack_of_canonicalIn (canonicalIn_neg x.canonicalIn_unpack)

/-- Negation is exact, for every float (both sides are `0` on NaN and `±∞`). -/
@[simp] theorem toReal_neg (x : Float32) : (-x).toReal = - x.toReal := by
  rw [toReal, toModel_neg_unpack, UnpackedFloat.toReal_neg, toReal]

theorem isFinite_neg (x : Float32) : (-x).IsFinite ↔ x.IsFinite := by
  rw [isFinite_iff, isFinite_iff, toModel_neg_unpack]
  cases x.toModel.unpack <;> simp [UnpackedFloat.neg, UnpackedFloat.isFinite]

/-- Every float, finite or not, denotes a real of magnitude at most `maxFinite32`. -/
theorem abs_toReal_le_maxFinite (f : Float32) : |f.toReal| ≤ maxFinite32 :=
  abs_toReal_le_maxFiniteIn f.canonicalIn_unpack

/-- `maxFinite32` is the familiar `(2 - 2^-23) · 2^127`. -/
theorem maxFinite32_eq : maxFinite32 = (2 - 2 ^ (-23 : ℤ)) * 2 ^ (127 : ℤ) := by
  rw [maxFinite32, show (127 : ℤ) = 23 + 104 by norm_num, zpow_add₀ two_ne_zero]
  have : (2 : ℝ) ^ (23 : ℤ) * 2 ^ (-23 : ℤ) = 1 := by
    rw [← zpow_add₀ two_ne_zero]; norm_num
  have h24 : (2 : ℝ) ^ 24 = 2 * 2 ^ (23 : ℤ) := by norm_num
  rw [h24]; linear_combination (2 : ℝ) ^ (104 : ℤ) * this

/-! ## Comparisons -/

theorem lt_iff_unpack (a b : Float32) : a < b ↔ a.toModel.unpack.lt b.toModel.unpack = true := by
  show a.lt b = true ↔ _
  simp [Float32.lt]
  rfl

theorem le_iff_unpack (a b : Float32) : a ≤ b ↔ a.toModel.unpack.le b.toModel.unpack = true := by
  show a.le b = true ↔ _
  simp [Float32.le]
  rfl

theorem compare_toModel_unpack {a b : Float32} (ha : a.IsFinite) (hb : b.IsFinite) :
    a.toModel.unpack.compare b.toModel.unpack = some (compare a.toReal b.toReal) :=
  UnpackedFloat.compare_eq_some_compare_toReal a.canonicalIn_unpack b.canonicalIn_unpack ha hb

/-- `Float32`'s `<` (hence the runtime `decLt`) agrees with the exact real order on finite floats. -/
theorem lt_iff_toReal_lt {a b : Float32} (ha : a.IsFinite) (hb : b.IsFinite) :
    a < b ↔ a.toReal < b.toReal := by
  rw [lt_iff_unpack]
  exact lt_eq_true_iff a.canonicalIn_unpack b.canonicalIn_unpack ha hb

/-- `Float32`'s `≤` (hence the runtime `decLe`) agrees with the exact real order on finite
floats. -/
theorem le_iff_toReal_le {a b : Float32} (ha : a.IsFinite) (hb : b.IsFinite) :
    a ≤ b ↔ a.toReal ≤ b.toReal := by
  rw [le_iff_unpack]
  exact le_eq_true_iff a.canonicalIn_unpack b.canonicalIn_unpack ha hb

theorem decide_lt_eq {a b : Float32} (ha : a.IsFinite) (hb : b.IsFinite) :
    decide (a < b) = decide (a.toReal < b.toReal) := by
  simp [lt_iff_toReal_lt ha hb]

theorem decide_le_eq {a b : Float32} (ha : a.IsFinite) (hb : b.IsFinite) :
    decide (a ≤ b) = decide (a.toReal ≤ b.toReal) := by
  simp [le_iff_toReal_le ha hb]

/-- `==` on finite floats is equality of exact values (so `0.0 == -0.0`). -/
theorem beq_iff_toReal_eq {a b : Float32} (ha : a.IsFinite) (hb : b.IsFinite) :
    (a == b) = true ↔ a.toReal = b.toReal := by
  show a.toModel.unpack.beq b.toModel.unpack = true ↔ _
  exact beq_eq_true_iff a.canonicalIn_unpack b.canonicalIn_unpack ha hb

/-! ## Transfer from the unpacked model -/

theorem of_pack {x : Float32} {r : UnpackedFloat} (h : x.toModel = Float32.Model.pack r)
    (hc : CanonicalIn Format.binary32 r) (hf : r.isFinite = true) :
    x.IsFinite ∧ x.toReal = r.toReal := by
  have hu : x.toModel.unpack = r := by rw [h]; exact Float32.Model.unpack_pack_of_canonicalIn hc
  exact ⟨by rw [isFinite_iff, hu]; exact hf, by rw [toReal, hu]⟩

theorem goodRoundIn_transfer {r : UnpackedFloat} {x : ℝ} (h : GoodRoundIn Format.binary32 r x) :
    (Float32.ofModel (Float32.Model.pack r)).IsFinite ∧
      |(Float32.ofModel (Float32.Model.pack r)).toReal - x| ≤ 2 ^ (-24 : ℤ) * |x| := by
  obtain ⟨hc, hf, herr⟩ := h
  obtain ⟨h1, h2⟩ := of_pack rfl hc hf
  exact ⟨h1, h2 ▸ herr⟩

theorem exactRoundIn_transfer {r : UnpackedFloat} {x : ℝ} (h : ExactRoundIn Format.binary32 r x) :
    (Float32.ofModel (Float32.Model.pack r)).IsFinite ∧
      (Float32.ofModel (Float32.Model.pack r)).toReal = x := by
  obtain ⟨hc, hf, hx⟩ := h
  obtain ⟨h1, h2⟩ := of_pack rfl hc hf
  exact ⟨h1, h2.trans hx⟩

theorem smallRoundIn_transfer {r : UnpackedFloat} {x : ℝ} (h : SmallRoundIn Format.binary32 r x) :
    (Float32.ofModel (Float32.Model.pack r)).IsFinite ∧
      |(Float32.ofModel (Float32.Model.pack r)).toReal - x| ≤ 2 ^ (-150 : ℤ) := by
  obtain ⟨hc, hf, herr⟩ := h
  obtain ⟨h1, h2⟩ := of_pack rfl hc hf
  exact ⟨h1, h2 ▸ herr⟩

theorem nearRoundIn_transfer {r : UnpackedFloat} {x : ℝ} (h : NearRoundIn Format.binary32 r x) :
    (Float32.ofModel (Float32.Model.pack r)).IsFinite ∧
      |(Float32.ofModel (Float32.Model.pack r)).toReal - x| ≤
        2 ^ (-24 : ℤ) * |x| + 2 ^ (-150 : ℤ) := by
  obtain ⟨hc, hf, herr⟩ := h
  obtain ⟨h1, h2⟩ := of_pack rfl hc hf
  exact ⟨h1, h2 ▸ herr⟩

/-! ## `+`, `-`, `*` on the normal range: relative error `2^-24` -/

/-- Rounding-error bound for `Float32` addition on the normal range (unit roundoff `2^-24`). -/
theorem add_error {a b : Float32} (ha : a.IsFinite) (hb : b.IsFinite)
    (hlo : (2 : ℝ) ^ (-126 : ℤ) ≤ |a.toReal + b.toReal|)
    (hhi : |a.toReal + b.toReal| ≤ maxFinite32) :
    (a + b).IsFinite ∧
      |(a + b).toReal - (a.toReal + b.toReal)| ≤ 2 ^ (-24 : ℤ) * |a.toReal + b.toReal| :=
  goodRoundIn_transfer (goodRoundIn_add a.canonicalIn_unpack b.canonicalIn_unpack ha hb hlo hhi)

/-- Rounding-error bound for `Float32` subtraction on the normal range. -/
theorem sub_error {a b : Float32} (ha : a.IsFinite) (hb : b.IsFinite)
    (hlo : (2 : ℝ) ^ (-126 : ℤ) ≤ |a.toReal - b.toReal|)
    (hhi : |a.toReal - b.toReal| ≤ maxFinite32) :
    (a - b).IsFinite ∧
      |(a - b).toReal - (a.toReal - b.toReal)| ≤ 2 ^ (-24 : ℤ) * |a.toReal - b.toReal| :=
  goodRoundIn_transfer (goodRoundIn_sub a.canonicalIn_unpack b.canonicalIn_unpack ha hb hlo hhi)

/-- Rounding-error bound for `Float32` multiplication on the normal range. -/
theorem mul_error {a b : Float32} (ha : a.IsFinite) (hb : b.IsFinite)
    (hlo : (2 : ℝ) ^ (-126 : ℤ) ≤ |a.toReal * b.toReal|)
    (hhi : |a.toReal * b.toReal| ≤ maxFinite32) :
    (a * b).IsFinite ∧
      |(a * b).toReal - a.toReal * b.toReal| ≤ 2 ^ (-24 : ℤ) * |a.toReal * b.toReal| :=
  goodRoundIn_transfer (goodRoundIn_mul a.canonicalIn_unpack b.canonicalIn_unpack ha hb hlo hhi)

theorem add_std_model {a b : Float32} (ha : a.IsFinite) (hb : b.IsFinite)
    (hlo : (2 : ℝ) ^ (-126 : ℤ) ≤ |a.toReal + b.toReal|)
    (hhi : |a.toReal + b.toReal| ≤ maxFinite32) :
    ∃ δ : ℝ, |δ| ≤ 2 ^ (-24 : ℤ) ∧ (a + b).toReal = (a.toReal + b.toReal) * (1 + δ) :=
  Float.std_model (fun h0 => not_tiny_zero (h0 ▸ hlo)) (add_error ha hb hlo hhi).2

theorem sub_std_model {a b : Float32} (ha : a.IsFinite) (hb : b.IsFinite)
    (hlo : (2 : ℝ) ^ (-126 : ℤ) ≤ |a.toReal - b.toReal|)
    (hhi : |a.toReal - b.toReal| ≤ maxFinite32) :
    ∃ δ : ℝ, |δ| ≤ 2 ^ (-24 : ℤ) ∧ (a - b).toReal = (a.toReal - b.toReal) * (1 + δ) :=
  Float.std_model (fun h0 => not_tiny_zero (h0 ▸ hlo)) (sub_error ha hb hlo hhi).2

theorem mul_std_model {a b : Float32} (ha : a.IsFinite) (hb : b.IsFinite)
    (hlo : (2 : ℝ) ^ (-126 : ℤ) ≤ |a.toReal * b.toReal|)
    (hhi : |a.toReal * b.toReal| ≤ maxFinite32) :
    ∃ δ : ℝ, |δ| ≤ 2 ^ (-24 : ℤ) ∧ (a * b).toReal = (a.toReal * b.toReal) * (1 + δ) :=
  Float.std_model (fun h0 => not_tiny_zero (h0 ▸ hlo)) (mul_error ha hb hlo hhi).2

/-! ## Below the normal range -/

/-- A difference of finite floats below `2^-126` in magnitude is computed exactly. -/
theorem sub_error_small {a b : Float32} (ha : a.IsFinite) (hb : b.IsFinite)
    (hsmall : |a.toReal - b.toReal| < (2 : ℝ) ^ (-126 : ℤ)) :
    (a - b).IsFinite ∧ (a - b).toReal = a.toReal - b.toReal :=
  exactRoundIn_transfer
    (exactRoundIn_sub (by decide) a.canonicalIn_unpack b.canonicalIn_unpack ha hb hsmall)

/-- A sum of finite floats below `2^-126` in magnitude is computed exactly. -/
theorem add_error_small {a b : Float32} (ha : a.IsFinite) (hb : b.IsFinite)
    (hsmall : |a.toReal + b.toReal| < (2 : ℝ) ^ (-126 : ℤ)) :
    (a + b).IsFinite ∧ (a + b).toReal = a.toReal + b.toReal :=
  exactRoundIn_transfer
    (exactRoundIn_add (by decide) a.canonicalIn_unpack b.canonicalIn_unpack ha hb hsmall)

/-- A product of finite floats below `2^-126` in magnitude is within `2^-150` (half the subnormal
spacing). -/
theorem mul_error_small {a b : Float32} (ha : a.IsFinite) (hb : b.IsFinite)
    (hsmall : |a.toReal * b.toReal| < (2 : ℝ) ^ (-126 : ℤ)) :
    (a * b).IsFinite ∧ |(a * b).toReal - a.toReal * b.toReal| ≤ 2 ^ (-150 : ℤ) :=
  smallRoundIn_transfer
    (smallRoundIn_mul (by decide) a.canonicalIn_unpack b.canonicalIn_unpack ha hb hsmall)

/-! ## Every exact result up to `maxFinite32` -/

/-- Rounding-error bound for `Float32` subtraction on every exact result up to `maxFinite32`. -/
theorem sub_err_all {a b : Float32} (ha : a.IsFinite) (hb : b.IsFinite)
    (hhi : |a.toReal - b.toReal| ≤ maxFinite32) :
    (a - b).IsFinite ∧
      |(a - b).toReal - (a.toReal - b.toReal)| ≤ 2 ^ (-24 : ℤ) * |a.toReal - b.toReal| := by
  rcases lt_or_ge |a.toReal - b.toReal| ((2 : ℝ) ^ (-126 : ℤ)) with h | h
  · obtain ⟨hf, hx⟩ := sub_error_small ha hb h
    refine ⟨hf, ?_⟩
    rw [hx, sub_self, abs_zero]; positivity
  · exact sub_error ha hb h hhi

/-- Rounding-error bound for `Float32` addition on every exact result up to `maxFinite32`. -/
theorem add_err_all {a b : Float32} (ha : a.IsFinite) (hb : b.IsFinite)
    (hhi : |a.toReal + b.toReal| ≤ maxFinite32) :
    (a + b).IsFinite ∧
      |(a + b).toReal - (a.toReal + b.toReal)| ≤ 2 ^ (-24 : ℤ) * |a.toReal + b.toReal| := by
  rcases lt_or_ge |a.toReal + b.toReal| ((2 : ℝ) ^ (-126 : ℤ)) with h | h
  · obtain ⟨hf, hx⟩ := add_error_small ha hb h
    refine ⟨hf, ?_⟩
    rw [hx, sub_self, abs_zero]; positivity
  · exact add_error ha hb h hhi

/-- Rounding-error bound for `Float32` multiplication on every exact result up to `maxFinite32`:
relative error `2^-24` plus absolute underflow error `2^-150`. -/
theorem mul_err_all {a b : Float32} (ha : a.IsFinite) (hb : b.IsFinite)
    (hhi : |a.toReal * b.toReal| ≤ maxFinite32) :
    (a * b).IsFinite ∧
      |(a * b).toReal - a.toReal * b.toReal| ≤
        2 ^ (-24 : ℤ) * |a.toReal * b.toReal| + 2 ^ (-150 : ℤ) := by
  rcases lt_or_ge |a.toReal * b.toReal| ((2 : ℝ) ^ (-126 : ℤ)) with h | h
  · obtain ⟨hf, hx⟩ := mul_error_small ha hb h
    refine ⟨hf, hx.trans ?_⟩
    have : 0 ≤ (2 : ℝ) ^ (-24 : ℤ) * |a.toReal * b.toReal| := by positivity
    linarith
  · obtain ⟨hf, hx⟩ := mul_error ha hb h hhi
    refine ⟨hf, hx.trans ?_⟩
    linarith [two_zpow_pos (-150)]

/-! ## Division and square root -/

theorem one_le_maxFinite32 : (1 : ℝ) ≤ maxFinite32 := by
  unfold maxFinite32
  have h : (1 : ℝ) ≤ 2 ^ (104 : ℤ) := one_le_zpow₀ one_le_two (by norm_num)
  calc (1 : ℝ) ≤ (2 ^ 24 - 1) * 1 := by norm_num
    _ ≤ (2 ^ 24 - 1) * 2 ^ (104 : ℤ) := mul_le_mul_of_nonneg_left h (by norm_num)

/-- **Division** of finite floats by a nonzero finite float rounds to nearest: relative error
`2^-24` plus absolute error `2^-150`, on every quotient up to `maxFinite32`. -/
theorem div_err_all {a b : Float32} (ha : a.IsFinite) (hb : b.IsFinite) (hb0 : b.toReal ≠ 0)
    (hq : |a.toReal / b.toReal| ≤ maxFinite32) :
    (a / b).IsFinite ∧ |(a / b).toReal - a.toReal / b.toReal| ≤
      2 ^ (-24 : ℤ) * |a.toReal / b.toReal| + 2 ^ (-150 : ℤ) :=
  nearRoundIn_transfer
    (nearRoundIn_div (by decide) a.canonicalIn_unpack b.canonicalIn_unpack ha hb hb0 hq)

/-- **Square root** of a finite non-negative float rounds to nearest: relative error `2^-24` plus
absolute error `2^-150`. -/
theorem sqrt_err_all {a : Float32} (ha : a.IsFinite) (h0 : 0 ≤ a.toReal)
    (h1 : a.toReal ≤ maxFinite32) :
    (Float32.sqrt a).IsFinite ∧ |(Float32.sqrt a).toReal - Real.sqrt a.toReal| ≤
      2 ^ (-24 : ℤ) * Real.sqrt a.toReal + 2 ^ (-150 : ℤ) := by
  have h := nearRoundIn_transfer
    (nearRoundIn_sqrt (by decide) a.canonicalIn_unpack ha h0 h1 one_le_maxFinite32)
  rwa [abs_of_nonneg (Real.sqrt_nonneg _)] at h

/-! ## Rounding does not cross a float -/

theorem toReal_of_toModel {x : Float32} {r : UnpackedFloat} (h : x.toModel = Float32.Model.pack r)
    (hc : CanonicalIn Format.binary32 r) : x.toReal = r.toReal := by
  rw [toReal, h, Float32.Model.unpack_pack_of_canonicalIn hc]

/-- Every canonical finite unpacked binary32 value is the value of a finite `Float32`. -/
theorem exists_of_canonicalIn {w : UnpackedFloat} (hc : CanonicalIn Format.binary32 w)
    (hf : w.isFinite = true) : ∃ d : Float32, d.IsFinite ∧ d.toReal = w.toReal :=
  ⟨Float32.ofModel (Float32.Model.pack w), (of_pack rfl hc hf).1, (of_pack rfl hc hf).2⟩

/-- Twice a finite float is a float, when it does not overflow. -/
theorem exists_double {a : Float32} (ha : a.IsFinite) (hhi : |2 * a.toReal| ≤ maxFinite32) :
    ∃ d : Float32, d.IsFinite ∧ d.toReal = 2 * a.toReal := by
  obtain ⟨w, hc, hf, hw⟩ := UnpackedFloat.exists_double a.canonicalIn_unpack ha hhi
  obtain ⟨d, hd, hd'⟩ := exists_of_canonicalIn hc hf
  exact ⟨d, hd, hd'.trans hw⟩

theorem bracket_transfer {x : Float32} {r : UnpackedFloat} {y : ℝ}
    (h : x.toModel = Float32.Model.pack r) (hc : CanonicalIn Format.binary32 r)
    (hb : BracketIn Format.binary32 r y) {f : Float32} (hf : f.IsFinite) :
    (f.toReal ≤ y → f.toReal ≤ x.toReal) ∧ (y ≤ f.toReal → x.toReal ≤ f.toReal) := by
  rw [toReal_of_toModel h hc]
  exact hb _ f.canonicalIn_unpack hf

/-- `Float32` addition does not cross a float: a finite float below (above) the exact sum is below
(above) the computed sum. -/
theorem add_bracket {a b : Float32} (ha : a.IsFinite) (hb : b.IsFinite)
    (hhi : |a.toReal + b.toReal| ≤ maxFinite32) {f : Float32} (hf : f.IsFinite) :
    (f.toReal ≤ a.toReal + b.toReal → f.toReal ≤ (a + b).toReal) ∧
      (a.toReal + b.toReal ≤ f.toReal → (a + b).toReal ≤ f.toReal) :=
  bracket_transfer rfl (canonicalIn_add_all (by decide) a.canonicalIn_unpack b.canonicalIn_unpack
    ha hb hhi) (bracketIn_add ha hb) hf

theorem sub_bracket {a b : Float32} (ha : a.IsFinite) (hb : b.IsFinite)
    (hhi : |a.toReal - b.toReal| ≤ maxFinite32) {f : Float32} (hf : f.IsFinite) :
    (f.toReal ≤ a.toReal - b.toReal → f.toReal ≤ (a - b).toReal) ∧
      (a.toReal - b.toReal ≤ f.toReal → (a - b).toReal ≤ f.toReal) :=
  bracket_transfer rfl (canonicalIn_sub_all (by decide) a.canonicalIn_unpack b.canonicalIn_unpack
    ha hb hhi) (bracketIn_sub ha hb) hf

theorem mul_bracket {a b : Float32} (ha : a.IsFinite) (hb : b.IsFinite)
    (hhi : |a.toReal * b.toReal| ≤ maxFinite32) {f : Float32} (hf : f.IsFinite) :
    (f.toReal ≤ a.toReal * b.toReal → f.toReal ≤ (a * b).toReal) ∧
      (a.toReal * b.toReal ≤ f.toReal → (a * b).toReal ≤ f.toReal) :=
  bracket_transfer rfl (canonicalIn_mul_all (by decide) a.canonicalIn_unpack b.canonicalIn_unpack
    ha hb hhi) (bracketIn_mul a.canonicalIn_unpack b.canonicalIn_unpack ha hb) hf

theorem div_bracket {a b : Float32} (ha : a.IsFinite) (hb : b.IsFinite) (hb0 : b.toReal ≠ 0)
    (hhi : |a.toReal / b.toReal| ≤ maxFinite32) {f : Float32} (hf : f.IsFinite) :
    (f.toReal ≤ a.toReal / b.toReal → f.toReal ≤ (a / b).toReal) ∧
      (a.toReal / b.toReal ≤ f.toReal → (a / b).toReal ≤ f.toReal) :=
  bracket_transfer rfl (nearRoundIn_div (by decide) a.canonicalIn_unpack b.canonicalIn_unpack
    ha hb hb0 hhi).1 (bracketIn_div ha hb hb0) hf

theorem sqrt_bracket {a : Float32} (ha : a.IsFinite) (h0 : 0 ≤ a.toReal)
    (h1 : a.toReal ≤ maxFinite32) {f : Float32} (hf : f.IsFinite) :
    (f.toReal ≤ Real.sqrt a.toReal → f.toReal ≤ (Float32.sqrt a).toReal) ∧
      (Real.sqrt a.toReal ≤ f.toReal → (Float32.sqrt a).toReal ≤ f.toReal) :=
  bracket_transfer rfl (nearRoundIn_sqrt (by decide) a.canonicalIn_unpack ha h0 h1
    one_le_maxFinite32).1 (bracketIn_sqrt ha h0) hf

end Float32
