/-
Rounding-error bounds for `+`, `-`, `*` through Lean's bit-level float model, generic over the
format `spec : Format` with precision `P = spec.mantissaBits` (53 for binary64, 24 for binary32).

For finite canonical operands whose exact result `x` lies in the normal range
`2^normExponent ≤ |x| ≤ maxFiniteIn spec`, the rounded result is canonical, finite, and
`|fl(x) - x| ≤ 2^-P · |x|` (unit roundoff of round-to-nearest-even).

Structure: integer analysis of `ExtendedMantissa` shifts (`round_shift`), the two-shift
structure of `roundWithAccuracy` (`roundWithAccuracy_exact_spec`), its real-valued form
(`roundWithAccuracy_exact_real`), then `round`/`normalize`, the three operations on
`UnpackedFloat` (`goodRoundIn_add`, `goodRoundIn_sub`, `goodRoundIn_mul`), and finally the
binary64 statements `Float.add_error`, `sub_error`, `mul_error` (`2^-53`, `2^-1022`,
`maxFinite`). The binary32 statements are in `FloatModel.Float32`.
-/
import FloatModel.Order
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination

open Float.Model UnpackedFloat

namespace Float.Model.UnpackedFloat.ExtendedMantissa

theorem shiftRight_succ (em : ExtendedMantissa) (n : Nat) :
    em >>> (n + 1) = shiftRightOne (em >>> n) := rfl

theorem shiftRight_zero (em : ExtendedMantissa) : em >>> 0 = em := rfl

theorem mantissa_shiftRight (m n : Nat) (rb sb : Bool) :
    ((⟨m, rb, sb⟩ : ExtendedMantissa) >>> n).mantissa = m / 2 ^ n := by
  induction n with
  | zero => simp [shiftRight_zero]
  | succ k ih =>
    rw [shiftRight_succ]
    simp only [shiftRightOne, ih, Nat.div_div_eq_div_mul, Nat.pow_succ]

theorem shift_spec (m k : Nat) :
    (((⟨m, false, false⟩ : ExtendedMantissa) >>> (k + 1)).roundBit = true ↔ 2 ^ k ≤ m % 2 ^ (k + 1)) ∧
    (((⟨m, false, false⟩ : ExtendedMantissa) >>> (k + 1)).stickyBit = true ↔ m % 2 ^ k ≠ 0) := by
  induction k with
  | zero =>
    simp only [shiftRight_succ, shiftRight_zero, shiftRightOne]
    simp
    omega
  | succ k ih =>
    rw [shiftRight_succ]
    simp only [shiftRightOne, mantissa_shiftRight, Bool.or_eq_true, ih.1, ih.2]
    have h1 : m % 2 ^ (k + 1 + 1) = m % 2 ^ (k + 1) + 2 ^ (k + 1) * (m / 2 ^ (k + 1) % 2) := by
      rw [Nat.pow_succ, Nat.mod_mul]
    have h2 : m % 2 ^ (k + 1) = m % 2 ^ k + 2 ^ k * (m / 2 ^ k % 2) := by
      rw [Nat.pow_succ, Nat.mod_mul]
    have hlt1 := Nat.mod_lt m (Nat.two_pow_pos (k + 1))
    have hlt0 := Nat.mod_lt m (Nat.two_pow_pos k)
    constructor
    · rcases Nat.mod_two_eq_zero_or_one (m / 2 ^ (k + 1)) with h | h <;> simp [h] at h1 ⊢ <;> omega
    · rcases Nat.mod_two_eq_zero_or_one (m / 2 ^ k) with h | h <;> simp [h] at h2 ⊢ <;> omega

/-- Rounding after a shift by `n` lands within half an ulp (`2^n / 2`) of the exact mantissa,
and on one of the two neighbours `⌊m / 2^n⌋`, `⌊m / 2^n⌋ + 1`. -/
theorem round_shift (m n : Nat) :
    let M := ((⟨m, false, false⟩ : ExtendedMantissa) >>> n).roundedMantissa
    (M = m / 2 ^ n ∨ M = m / 2 ^ n + 1) ∧
      2 * m ≤ 2 * (M * 2 ^ n) + 2 ^ n ∧ 2 * (M * 2 ^ n) ≤ 2 * m + 2 ^ n := by
  intro M
  cases n with
  | zero =>
    have : M = m := rfl
    simp [this]
  | succ k =>
    obtain ⟨hrb, hsb⟩ := shift_spec m k
    have hq := mantissa_shiftRight m (k + 1) false false
    have hdm := Nat.div_add_mod m (2 ^ (k + 1))
    have h2 : m % 2 ^ (k + 1) = m % 2 ^ k + 2 ^ k * (m / 2 ^ k % 2) := by
      rw [Nat.pow_succ, Nat.mod_mul]
    have hlt1 := Nat.mod_lt m (Nat.two_pow_pos (k + 1))
    have hlt0 := Nat.mod_lt m (Nat.two_pow_pos k)
    have hp : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [Nat.pow_succ, Nat.mul_comm]
    generalize hem : ((⟨m, false, false⟩ : ExtendedMantissa) >>> (k + 1)) = em at hrb hsb hq M
    obtain ⟨q, rb, sb⟩ := em
    simp only at hrb hsb hq
    subst hq
    have hM : M = (⟨m / 2 ^ (k + 1), rb, sb⟩ : ExtendedMantissa).roundedMantissa := by
      rw [← hem]
    set q := m / 2 ^ (k + 1)
    have hqq : 2 ^ (k + 1) * q = q * 2 ^ (k + 1) := Nat.mul_comm _ _
    have hq1 : (q + 1) * 2 ^ (k + 1) = q * 2 ^ (k + 1) + 2 ^ (k + 1) := by ring
    rcases Nat.mod_two_eq_zero_or_one (m / 2 ^ k) with hb | hb <;> rw [hb] at h2 <;>
      cases rb <;> cases sb <;>
      simp [roundedMantissa, accuracy, Accuracy.roundToNearestEven] at hM hrb hsb <;>
      rcases Nat.mod_two_eq_zero_or_one q with hq2 | hq2 <;> simp_all <;> omega

end Float.Model.UnpackedFloat.ExtendedMantissa

namespace Float.Model.Format

theorem minExponent_nonpos (spec : Format) : spec.minExponent ≤ 0 := by
  have := spec.hm; rw [minExponent_eq]; omega

end Float.Model.Format

namespace Float.Model.UnpackedFloat

open ExtendedMantissa

/-- The final packaging step of `roundWithAccuracy`. -/
def mkFin (s : Sign) (M : Nat) (E : Int) : UnpackedFloat :=
  if h : M = 0 then .zero s else .finite s M E (Nat.pos_of_ne_zero h)

theorem mkFin_pos {s : Sign} {M : Nat} {E : Int} (h : 0 < M) : mkFin s M E = .finite s M E h := by
  unfold mkFin; rw [dif_neg (by omega)]

theorem roundWithAccuracy_eq_mkFin (spec : Format) (s : Sign) (m : Nat) (e : Int) (acc : Accuracy) :
    roundWithAccuracy spec s m e acc =
      mkFin s (shiftToTargetExponent spec (shiftToTargetExponent spec m e acc).1.roundedMantissa
          (shiftToTargetExponent spec m e acc).2 .exact).1.mantissa
        (shiftToTargetExponent spec (shiftToTargetExponent spec m e acc).1.roundedMantissa
          (shiftToTargetExponent spec m e acc).2 .exact).2 := rfl

/-- `shiftToTargetExponent` on an exact input shifts right by the amount the target exponent
dictates. -/
theorem shiftToTargetExponent_exact (spec : Format) (m : Nat) (e : Int) (n : Nat)
    (hn : (max ((m.log2 : Int) + 1 + e - spec.mantissaBits) spec.minExponent - e).toNat = n) :
    shiftToTargetExponent spec m e .exact =
      ((⟨m, false, false⟩ : ExtendedMantissa) >>> n, e + (n : Int)) := by
  simp only [shiftToTargetExponent, shiftToExponent, ExtendedMantissa.ofMantissaAndAccuracy,
    Format.targetExponent, totalExponent, hn]

theorem shiftToTargetExponent_binary64 (m : Nat) (e : Int) (n : Nat)
    (hn : (max ((m.log2 : Int) + 1 + e - 53) (-1074) - e).toNat = n) :
    shiftToTargetExponent Format.binary64 m e .exact =
      ((⟨m, false, false⟩ : ExtendedMantissa) >>> n, e + (n : Int)) :=
  shiftToTargetExponent_exact Format.binary64 m e n hn

/-- Integer-level description of `roundWithAccuracy` on an exact input whose result is a
normal number: with `k` the stored mantissa bits, the first shift is by `n = log2 m - k` bits,
rounding gives `M₀` within half an ulp, and the renormalizing second shift (by `j ∈ {0,1}`) is
exact. -/
theorem roundWithAccuracy_exact_spec (spec : Format) (s : Sign) (m : Nat) (e : Int) (hm : 0 < m)
    (hL : spec.mantissaBitsWithoutImplicit ≤ m.log2)
    (hT : spec.minExponent ≤ (m.log2 : Int) + e - spec.mantissaBitsWithoutImplicit) :
    ∃ (M : Nat) (E : Int) (hM : 0 < M) (M₀ j : Nat),
      roundWithAccuracy spec s m e .exact = .finite s M E hM ∧
      2 ^ spec.mantissaBitsWithoutImplicit ≤ M ∧ M < 2 ^ spec.mantissaBits ∧ M * 2 ^ j = M₀ ∧
      E = (m.log2 : Int) + e - spec.mantissaBitsWithoutImplicit + j ∧
      2 * m ≤ 2 * (M₀ * 2 ^ (m.log2 - spec.mantissaBitsWithoutImplicit)) +
        2 ^ (m.log2 - spec.mantissaBitsWithoutImplicit) ∧
      2 * (M₀ * 2 ^ (m.log2 - spec.mantissaBitsWithoutImplicit)) ≤
        2 * m + 2 ^ (m.log2 - spec.mantissaBitsWithoutImplicit) := by
  have hPk := Format.mantissaBits_eq spec
  have hP := two_pow_mantissaBits spec
  rw [roundWithAccuracy_eq_mkFin]
  set k := spec.mantissaBitsWithoutImplicit with hk
  set L := m.log2 with hLdef
  set n := L - k with hn
  rw [shiftToTargetExponent_exact spec m e n (by omega)]
  simp only
  obtain ⟨hMq, hlo, hhi⟩ := round_shift m n
  generalize ((⟨m, false, false⟩ : ExtendedMantissa) >>> n).roundedMantissa = M₀ at hMq hlo hhi ⊢
  have hmL : 2 ^ L ≤ m := Nat.log2_self_le (by omega)
  have hmL' : m < 2 ^ (L + 1) := Nat.lt_log2_self
  have hpow : 2 ^ L = 2 ^ k * 2 ^ n := by rw [← Nat.pow_add]; congr 1; omega
  have hpow' : 2 ^ (L + 1) = 2 ^ spec.mantissaBits * 2 ^ n := by
    rw [← Nat.pow_add]; congr 1; omega
  have hq1 : 2 ^ k ≤ m / 2 ^ n := (Nat.le_div_iff_mul_le (Nat.two_pow_pos n)).2 (by rw [← hpow]; exact hmL)
  have hq2 : m / 2 ^ n < 2 ^ spec.mantissaBits :=
    (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos n)).2 (by rw [← hpow']; exact hmL')
  have hM1 : 2 ^ k ≤ M₀ := by omega
  have hM2 : M₀ ≤ 2 ^ spec.mantissaBits := by omega
  by_cases hM : M₀ < 2 ^ spec.mantissaBits
  · have hlog : M₀.log2 = k := (Nat.log2_eq_iff (by omega)).2 ⟨hM1, by rw [Nat.pow_succ]; omega⟩
    rw [shiftToTargetExponent_exact spec M₀ (e + n) 0 (by rw [hlog]; omega)]
    simp only [mantissa_shiftRight, pow_zero, Nat.div_one]
    rw [mkFin_pos (by omega)]
    exact ⟨M₀, _, by omega, M₀, 0, rfl, hM1, hM, by simp, by omega, hlo, hhi⟩
  · have hM' : M₀ = 2 ^ spec.mantissaBits := by omega
    subst hM'
    have hlog : (2 ^ spec.mantissaBits : Nat).log2 = spec.mantissaBits := Nat.log2_two_pow
    rw [shiftToTargetExponent_exact spec (2 ^ spec.mantissaBits) (e + n) 1 (by rw [hlog]; omega)]
    simp only [mantissa_shiftRight]
    have hdiv : 2 ^ spec.mantissaBits / 2 ^ 1 = 2 ^ k := by rw [hP]; simp
    rw [hdiv, mkFin_pos (by positivity)]
    exact ⟨_, _, by positivity, 2 ^ spec.mantissaBits, 1, rfl, le_rfl, by omega, by omega,
      by omega, hlo, hhi⟩

/-- Largest finite value of the format `spec`, `(2^P - 1) · 2^maxExponent`. -/
noncomputable def maxFiniteIn (spec : Format) : ℝ :=
  (2 ^ spec.mantissaBits - 1) * (2 : ℝ) ^ spec.maxExponent

/-- Largest finite binary64 value, `(2^53 - 1) · 2^971`. -/
noncomputable def maxFinite : ℝ := (2 ^ 53 - 1) * (2 : ℝ) ^ (971 : ℤ)

theorem maxFinite_eq_in : maxFinite = maxFiniteIn Format.binary64 := rfl

theorem two_zpow_pos (k : Int) : (0 : ℝ) < (2 : ℝ) ^ k := zpow_pos two_pos k

theorem two_pow_mul_two_zpow_neg (P : Nat) : (2 : ℝ) ^ P * (2 : ℝ) ^ (-(P : ℤ)) = 1 := by
  rw [← zpow_natCast, ← zpow_add₀ two_ne_zero]; simp

/-- `2^-P · 2^(P-1) = 1/2`. -/
theorem two_zpow_neg_mantissaBits (spec : Format) :
    (2 : ℝ) ^ (-(spec.mantissaBits : ℤ)) * 2 ^ spec.mantissaBitsWithoutImplicit = 1 / 2 := by
  have h := two_pow_mul_two_zpow_neg spec.mantissaBits
  rw [Format.mantissaBits_eq, pow_succ] at h
  rw [Format.mantissaBits_eq]
  linarith

theorem maxFiniteIn_mul_lt (spec : Format) :
    maxFiniteIn spec * (1 + 2 ^ (-(spec.mantissaBits : ℤ))) <
      (2 : ℝ) ^ (spec.maxExponent + spec.mantissaBits) := by
  have hx := two_pow_mul_two_zpow_neg spec.mantissaBits
  have h : (2 : ℝ) ^ (spec.maxExponent + spec.mantissaBits) =
      2 ^ spec.mantissaBits * 2 ^ spec.maxExponent := by
    rw [zpow_add₀ two_ne_zero, zpow_natCast]; ring
  rw [h, maxFiniteIn]
  have hy := two_zpow_pos (-(spec.mantissaBits : ℤ))
  have h2 : ((2 : ℝ) ^ spec.mantissaBits - 1) * (1 + 2 ^ (-(spec.mantissaBits : ℤ))) <
      2 ^ spec.mantissaBits := by nlinarith
  have := two_zpow_pos spec.maxExponent
  calc ((2 : ℝ) ^ spec.mantissaBits - 1) * 2 ^ spec.maxExponent * (1 + 2 ^ (-(spec.mantissaBits : ℤ)))
      = (((2 : ℝ) ^ spec.mantissaBits - 1) * (1 + 2 ^ (-(spec.mantissaBits : ℤ)))) *
          2 ^ spec.maxExponent := by ring
    _ < 2 ^ spec.mantissaBits * 2 ^ spec.maxExponent := mul_lt_mul_of_pos_right h2 this

theorem maxFinite_mul_lt : maxFinite * (1 + 2 ^ (-53 : ℤ)) < (2 : ℝ) ^ (1024 : ℤ) :=
  maxFiniteIn_mul_lt Format.binary64

/-- Real-level rounding bound for `roundWithAccuracy` on an exact input in the normal range. -/
theorem roundWithAccuracy_exact_real (spec : Format) (s : Sign) (m : Nat) (e : Int) (hm : 0 < m)
    (hL : spec.mantissaBitsWithoutImplicit ≤ m.log2 ∨ e ≤ spec.minExponent)
    (hlo : (2 : ℝ) ^ spec.normExponent ≤ mag m e) (hhi : mag m e ≤ maxFiniteIn spec) :
    ∃ (M : Nat) (E : Int) (hM : 0 < M),
      roundWithAccuracy spec s m e .exact = .finite s M E hM ∧
      CanonicalIn spec (.finite s M E hM) ∧
      |mag M E - mag m e| ≤ 2 ^ (-(spec.mantissaBits : ℤ)) * mag m e := by
  have hPk := Format.mantissaBits_eq spec
  have hnorm := Format.normExponent_eq spec
  set k := spec.mantissaBitsWithoutImplicit with hk
  set L := m.log2 with hLdef
  have hmL : 2 ^ L ≤ m := Nat.log2_self_le (by omega)
  have hmL' : m < 2 ^ (L + 1) := Nat.lt_log2_self
  -- the total exponent is above the normal threshold
  have hT : spec.normExponent < (L : Int) + 1 + e := by
    have h1 : mag m e < (2 : ℝ) ^ ((L : Int) + 1 + e) := by
      rw [zpow_add₀ two_ne_zero, mag]
      have : (m : ℝ) < (2 : ℝ) ^ ((L : Int) + 1) := by
        rw [show ((L : Int) + 1) = ((L + 1 : Nat) : Int) by push_cast; ring, zpow_natCast]
        exact_mod_cast hmL'
      exact mul_lt_mul_of_pos_right this (two_zpow_pos e)
    exact (zpow_lt_zpow_iff_right₀ one_lt_two).1 (lt_of_le_of_lt hlo h1)
  have hL' : k ≤ L := by omega
  obtain ⟨M, E, hM, M₀, j, hres, hM1, hM2, hMj, hE, hlo', hhi'⟩ :=
    roundWithAccuracy_exact_spec spec s m e hm hL' (by omega)
  set n := L - k with hn
  refine ⟨M, E, hM, hres, ?_⟩
  -- real-valued facts
  have hN : (0 : ℝ) < 2 ^ n := by positivity
  have hEn : (2 : ℝ) ^ E = 2 ^ j * 2 ^ n * 2 ^ e := by
    rw [hE, show (L : Int) + e - k + j = ((j + n : Nat) : Int) + e by push_cast; omega,
      zpow_add₀ two_ne_zero, zpow_natCast, pow_add]
  have hmagM : mag M E = (M₀ : ℝ) * 2 ^ n * 2 ^ e := by
    rw [mag, hEn, ← hMj]; push_cast; ring
  have hlo'' : (2 * m : ℝ) ≤ 2 * (M₀ * 2 ^ n) + 2 ^ n := by exact_mod_cast hlo'
  have hhi'' : (2 * (M₀ * 2 ^ n) : ℝ) ≤ 2 * m + 2 ^ n := by exact_mod_cast hhi'
  have hmN : (2 : ℝ) ^ k * 2 ^ n ≤ m := by
    have : 2 ^ k * 2 ^ n ≤ m := by rw [← Nat.pow_add, show k + n = L by omega]; exact hmL
    exact_mod_cast this
  have he := two_zpow_pos e
  have herr : |mag M E - mag m e| ≤ 2 ^ (-(spec.mantissaBits : ℤ)) * mag m e := by
    have h53 := two_zpow_neg_mantissaBits spec
    have hk : |(M₀ : ℝ) * 2 ^ n - m| ≤ 2 ^ n / 2 := by
      rw [abs_le]; constructor <;> linarith
    have hk' : (2 : ℝ) ^ n / 2 ≤ 2 ^ (-(spec.mantissaBits : ℤ)) * m := by
      have hu : (0 : ℝ) < 2 ^ (-(spec.mantissaBits : ℤ)) := two_zpow_pos _
      have := mul_le_mul_of_nonneg_left hmN hu.le
      calc (2 : ℝ) ^ n / 2 = (2 ^ (-(spec.mantissaBits : ℤ)) * 2 ^ k) * 2 ^ n := by rw [h53]; ring
        _ = 2 ^ (-(spec.mantissaBits : ℤ)) * (2 ^ k * 2 ^ n) := by ring
        _ ≤ _ := this
    rw [hmagM, mag, show (M₀ : ℝ) * 2 ^ n * 2 ^ e - m * 2 ^ e = ((M₀ : ℝ) * 2 ^ n - m) * 2 ^ e by ring,
      abs_mul, abs_of_pos he,
      show (2 : ℝ) ^ (-(spec.mantissaBits : ℤ)) * (m * 2 ^ e) =
        (2 ^ (-(spec.mantissaBits : ℤ)) * m) * 2 ^ e by ring]
    exact mul_le_mul_of_nonneg_right (hk.trans hk') he.le
  refine ⟨⟨?_, ?_, hM2, fun _ => hM1⟩, herr⟩
  · omega
  · -- no overflow: 2^(k+E) ≤ mag M E < 2^(maxExponent + P)
    have hup : mag M E < (2 : ℝ) ^ (spec.maxExponent + spec.mantissaBits) := by
      have h1 : mag M E ≤ mag m e * (1 + 2 ^ (-(spec.mantissaBits : ℤ))) := by
        have := (abs_le.1 herr).2; nlinarith
      have h2 : mag m e * (1 + 2 ^ (-(spec.mantissaBits : ℤ))) ≤
          maxFiniteIn spec * (1 + 2 ^ (-(spec.mantissaBits : ℤ))) := by
        have : (0 : ℝ) < 1 + 2 ^ (-(spec.mantissaBits : ℤ)) := by positivity
        nlinarith
      linarith [maxFiniteIn_mul_lt spec]
    have hdown : (2 : ℝ) ^ ((k : Int) + E) ≤ mag M E := by
      rw [zpow_add₀ two_ne_zero, mag, zpow_natCast]
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hM1) (two_zpow_pos E).le
    have := (zpow_lt_zpow_iff_right₀ one_lt_two).1 (lt_of_le_of_lt hdown hup)
    omega

theorem log2_mul_two_pow (m k : Nat) (hm : 0 < m) : (m * 2 ^ k).log2 = m.log2 + k := by
  rw [Nat.log2_eq_iff (by positivity)]
  have h1 : 2 ^ m.log2 ≤ m := Nat.log2_self_le (by omega)
  have h2 : m < 2 ^ (m.log2 + 1) := Nat.lt_log2_self
  constructor
  · rw [Nat.pow_add]; exact Nat.mul_le_mul_right _ h1
  · rw [show m.log2 + k + 1 = (m.log2 + 1) + k by omega, Nat.pow_add]
    exact Nat.mul_lt_mul_of_pos_right h2 (Nat.two_pow_pos k)

theorem mag_mul_two_pow (m k : Nat) (e : Int) : mag (m * 2 ^ k) (e - k) = mag m e := by
  unfold mag
  have : (2 : ℝ) ^ e = 2 ^ k * 2 ^ (e - k) := by
    rw [← zpow_natCast, ← zpow_add₀ two_ne_zero]; congr 1; ring
  rw [this]; push_cast; ring

/-- The left-alignment amount of `round`. -/
theorem round_shift_amount (spec : Format) (m : Nat) (e : Int) :
    (e - spec.targetExponent (totalExponent m e)).toNat =
      (e - max ((m.log2 : Int) + 1 + e - spec.mantissaBits) spec.minExponent).toNat := rfl

/-- Rounding (`round`, which first left-aligns the mantissa) is within relative error
`2^-P` on the normal range. -/
theorem round_real (spec : Format) (s : Sign) (m : Nat) (e : Int) (hm : 0 < m)
    (hlo : (2 : ℝ) ^ spec.normExponent ≤ mag m e) (hhi : mag m e ≤ maxFiniteIn spec) :
    ∃ (M : Nat) (E : Int) (hM : 0 < M),
      round spec s m e = .finite s M E hM ∧
      CanonicalIn spec (.finite s M E hM) ∧
      |mag M E - mag m e| ≤ 2 ^ (-(spec.mantissaBits : ℤ)) * mag m e := by
  have hPk := Format.mantissaBits_eq spec
  simp only [round, decreaseExponent, Nat.shiftLeft_eq]
  set k := (e - spec.targetExponent (totalExponent m e)).toNat with hk
  have hk' := round_shift_amount spec m e
  have hmag := mag_mul_two_pow m k e
  have hlog := log2_mul_two_pow m k hm
  refine roundWithAccuracy_exact_real spec s (m * 2 ^ k) (e - k) (by positivity) ?_
    (hmag ▸ hlo) (hmag ▸ hhi) |>.imp fun M h => ?_
  · rw [hlog]; omega
  · rw [hmag] at h; exact h

/-- Sign as a real number. -/
def Sign.toReal : Sign → ℝ
  | .positive => 1
  | .negative => -1

theorem toReal_finite (s : Sign) (m : Nat) (e : Int) (hm : 0 < m) :
    (UnpackedFloat.finite s m e hm).toReal = s.toReal * mag m e := by
  cases s <;> simp [toReal, Sign.apply, Sign.toReal, mag]

theorem Sign.abs_toReal (s : Sign) : |s.toReal| = 1 := by cases s <;> simp [Sign.toReal]

theorem Sign.toReal_mul (s t : Sign) : (s * t).toReal = s.toReal * t.toReal := by
  cases s <;> cases t <;> simp [Sign.toReal]

theorem Sign.toReal_neg (s : Sign) : (-s).toReal = - s.toReal := by
  cases s <;> simp [Sign.toReal]

/-- Signed version of a rounding bound, phrased on `toReal`. -/
theorem signed_bound {u : ℝ} {s : Sign} {M m : Nat} {E e : Int} (hM : 0 < M)
    (h : |mag M E - mag m e| ≤ u * mag m e) :
    |(UnpackedFloat.finite s M E hM).toReal - s.toReal * mag m e| ≤
      u * |s.toReal * mag m e| := by
  rw [toReal_finite, ← mul_sub, abs_mul, abs_mul, Sign.abs_toReal, one_mul, one_mul]
  have : 0 ≤ mag m e := by unfold mag; positivity
  rwa [abs_of_nonneg this]

/-- What the float-level theorems need from an unpacked result: canonical for `spec`, finite,
within relative error `2^-P` of `x`. -/
def GoodRoundIn (spec : Format) (r : UnpackedFloat) (x : ℝ) : Prop :=
  CanonicalIn spec r ∧ r.isFinite = true ∧ |r.toReal - x| ≤ 2 ^ (-(spec.mantissaBits : ℤ)) * |x|

/-- `GoodRoundIn` for binary64, with the constants written out. -/
def GoodRound (r : UnpackedFloat) (x : ℝ) : Prop :=
  r.Canonical ∧ r.isFinite = true ∧ |r.toReal - x| ≤ 2 ^ (-53 : ℤ) * |x|

theorem goodRound_iff (r : UnpackedFloat) (x : ℝ) : GoodRound r x ↔ GoodRoundIn Format.binary64 r x := by
  rw [GoodRound, GoodRoundIn, canonical_iff]; rfl

theorem goodRoundIn_finite_round {spec : Format} {s : Sign} {m : Nat} {e : Int} (hm : 0 < m)
    (hlo : (2 : ℝ) ^ spec.normExponent ≤ mag m e) (hhi : mag m e ≤ maxFiniteIn spec) :
    GoodRoundIn spec (round spec s m e) (s.toReal * mag m e) := by
  obtain ⟨M, E, hM, hr, hc, herr⟩ := round_real spec s m e hm hlo hhi
  rw [hr]
  exact ⟨hc, rfl, signed_bound hM herr⟩

/-- `normalize` (used by `add` and `sub`) on a nonzero integer mantissa in the normal range. -/
theorem goodRoundIn_normalize (spec : Format) (N : Int) (E : Int) (zs : Sign) (hN : N ≠ 0)
    (hlo : (2 : ℝ) ^ spec.normExponent ≤ |(N : ℝ) * 2 ^ E|)
    (hhi : |(N : ℝ) * 2 ^ E| ≤ maxFiniteIn spec) :
    GoodRoundIn spec (normalize spec N E zs) ((N : ℝ) * 2 ^ E) := by
  have hE := two_zpow_pos E
  unfold normalize
  rcases lt_trichotomy N 0 with h | h | h
  · rw [Int.compare_eq_lt.2 h]
    have hm : 0 < (-N).toNat := by omega
    have hmag : mag (-N).toNat E = |(N : ℝ) * 2 ^ E| := by
      rw [mag, abs_mul, abs_of_pos hE]
      congr 1
      rw [abs_of_neg (by exact_mod_cast h)]
      have : (((-N).toNat : Int) : ℝ) = ((-N : Int) : ℝ) := by
        congr 1; omega
      push_cast at this ⊢; linarith
    have hneg : (N : ℝ) * 2 ^ E < 0 := mul_neg_of_neg_of_pos (by exact_mod_cast h) hE
    have hx : (N : ℝ) * 2 ^ E = Sign.negative.toReal * mag (-N).toNat E := by
      rw [hmag, abs_of_neg hneg]; simp [Sign.toReal]
    rw [hx]
    exact goodRoundIn_finite_round hm (hmag ▸ hlo) (hmag ▸ hhi)
  · exact absurd h hN
  · rw [Int.compare_eq_gt.2 h]
    have hm : 0 < N.toNat := by omega
    have hmag : mag N.toNat E = (N : ℝ) * 2 ^ E := by
      rw [mag]; congr 1
      have : ((N.toNat : Int) : ℝ) = (N : ℝ) := by congr 1; omega
      exact_mod_cast this
    have hpos : 0 < (N : ℝ) * 2 ^ E := mul_pos (by exact_mod_cast h) hE
    have hx : (N : ℝ) * 2 ^ E = Sign.positive.toReal * mag N.toNat E := by
      rw [hmag]; simp [Sign.toReal]
    rw [hx]
    rw [abs_of_pos hpos] at hlo hhi
    exact goodRoundIn_finite_round hm (hmag ▸ hlo) (hmag ▸ hhi)

theorem goodRound_normalize (N : Int) (E : Int) (zs : Sign) (hN : N ≠ 0)
    (hlo : (2 : ℝ) ^ (-1022 : ℤ) ≤ |(N : ℝ) * 2 ^ E|) (hhi : |(N : ℝ) * 2 ^ E| ≤ maxFinite) :
    GoodRound (normalize Format.binary64 N E zs) ((N : ℝ) * 2 ^ E) :=
  (goodRound_iff _ _).2 (goodRoundIn_normalize Format.binary64 N E zs hN hlo hhi)

theorem apply_shift_toReal (s : Sign) (m : Nat) (e E : Int) (hE : E ≤ e) :
    ((s.apply ((m <<< (e - E).toNat : Nat) : Int) : Int) : ℝ) * 2 ^ E = s.toReal * mag m e := by
  have h := mag_mul_two_pow m (e - E).toNat e
  rw [show e - ((e - E).toNat : Int) = E by omega] at h
  rw [Nat.shiftLeft_eq, ← h, mag]
  cases s <;> simp [Sign.apply, Sign.toReal]

theorem goodRoundIn_of_exact {spec : Format} {r : UnpackedFloat} {x : ℝ} (hc : CanonicalIn spec r)
    (hf : r.isFinite = true) (hx : r.toReal = x) : GoodRoundIn spec r x := by
  refine ⟨hc, hf, ?_⟩
  rw [hx, sub_self, abs_zero]; positivity

theorem not_tiny_zero {n : Int} (h : (2 : ℝ) ^ n ≤ |(0 : ℝ)|) : False := by
  rw [abs_zero] at h; linarith [two_zpow_pos n]

/-- The exact sum of two finite nonzero floats, as an integer mantissa on the smaller exponent. -/
theorem add_key (s₁ s₂ : Sign) (m₁ m₂ : Nat) (e₁ e₂ : Int) (hm₁ : 0 < m₁) (hm₂ : 0 < m₂) :
    (((s₁.apply ((m₁ <<< (e₁ - min e₁ e₂).toNat : Nat) : Int) +
        s₂.apply ((m₂ <<< (e₂ - min e₁ e₂).toNat : Nat) : Int) : Int) : ℝ) * 2 ^ (min e₁ e₂)) =
      (UnpackedFloat.finite s₁ m₁ e₁ hm₁).toReal + (UnpackedFloat.finite s₂ m₂ e₂ hm₂).toReal := by
  rw [Int.cast_add, add_mul, apply_shift_toReal _ _ _ _ (min_le_left _ _),
    apply_shift_toReal _ _ _ _ (min_le_right _ _), toReal_finite, toReal_finite]

/-- The exact difference of two finite nonzero floats, as an integer mantissa on the smaller
exponent. -/
theorem sub_key (s₁ s₂ : Sign) (m₁ m₂ : Nat) (e₁ e₂ : Int) (hm₁ : 0 < m₁) (hm₂ : 0 < m₂) :
    (((s₁.apply ((m₁ <<< (e₁ - min e₁ e₂).toNat : Nat) : Int) -
        s₂.apply ((m₂ <<< (e₂ - min e₁ e₂).toNat : Nat) : Int) : Int) : ℝ) * 2 ^ (min e₁ e₂)) =
      (UnpackedFloat.finite s₁ m₁ e₁ hm₁).toReal - (UnpackedFloat.finite s₂ m₂ e₂ hm₂).toReal := by
  rw [Int.cast_sub, sub_mul, apply_shift_toReal _ _ _ _ (min_le_left _ _),
    apply_shift_toReal _ _ _ _ (min_le_right _ _), toReal_finite, toReal_finite]

/-- Addition of canonical finite unpacked floats, exact sum in the normal range. -/
theorem goodRoundIn_add {spec : Format} {u v : UnpackedFloat} (cu : CanonicalIn spec u)
    (cv : CanonicalIn spec v) (fu : u.isFinite = true) (fv : v.isFinite = true)
    (hlo : (2 : ℝ) ^ spec.normExponent ≤ |u.toReal + v.toReal|)
    (hhi : |u.toReal + v.toReal| ≤ maxFiniteIn spec) :
    GoodRoundIn spec (add spec u v) (u.toReal + v.toReal) := by
  cases u with
  | infinity _ => simp [isFinite] at fu
  | notANumber => simp [isFinite] at fu
  | zero s₁ =>
    cases v with
    | infinity _ => simp [isFinite] at fv
    | notANumber => simp [isFinite] at fv
    | zero s₂ => exact (not_tiny_zero (by simpa [toReal] using hlo)).elim
    | finite s₂ m₂ e₂ hm₂ =>
      exact goodRoundIn_of_exact cv rfl (by simp [add, toReal])
  | finite s₁ m₁ e₁ hm₁ =>
    cases v with
    | infinity _ => simp [isFinite] at fv
    | notANumber => simp [isFinite] at fv
    | zero s₂ => exact goodRoundIn_of_exact cu rfl (by simp [add, toReal])
    | finite s₂ m₂ e₂ hm₂ =>
      simp only [add, decreaseExponent]
      rw [← add_key s₁ s₂ m₁ m₂ e₁ e₂ hm₁ hm₂] at hlo hhi ⊢
      refine goodRoundIn_normalize spec _ _ _ ?_ hlo hhi
      intro h0; rw [h0, Int.cast_zero, zero_mul] at hlo; exact not_tiny_zero hlo

/-- Subtraction of canonical finite unpacked floats, exact difference in the normal range. -/
theorem goodRoundIn_sub {spec : Format} {u v : UnpackedFloat} (cu : CanonicalIn spec u)
    (cv : CanonicalIn spec v) (fu : u.isFinite = true) (fv : v.isFinite = true)
    (hlo : (2 : ℝ) ^ spec.normExponent ≤ |u.toReal - v.toReal|)
    (hhi : |u.toReal - v.toReal| ≤ maxFiniteIn spec) :
    GoodRoundIn spec (sub spec u v) (u.toReal - v.toReal) := by
  cases u with
  | infinity _ => simp [isFinite] at fu
  | notANumber => simp [isFinite] at fu
  | zero s₁ =>
    cases v with
    | infinity _ => simp [isFinite] at fv
    | notANumber => simp [isFinite] at fv
    | zero s₂ => exact (not_tiny_zero (by simpa [toReal] using hlo)).elim
    | finite s₂ m₂ e₂ hm₂ =>
      refine goodRoundIn_of_exact cv rfl ?_
      have := toReal_neg (.finite s₂ m₂ e₂ hm₂)
      simp only [neg] at this
      simp only [sub, this]; simp [toReal]
  | finite s₁ m₁ e₁ hm₁ =>
    cases v with
    | infinity _ => simp [isFinite] at fv
    | notANumber => simp [isFinite] at fv
    | zero s₂ => exact goodRoundIn_of_exact cu rfl (by simp [sub, toReal])
    | finite s₂ m₂ e₂ hm₂ =>
      simp only [sub, decreaseExponent]
      rw [← sub_key s₁ s₂ m₁ m₂ e₁ e₂ hm₁ hm₂] at hlo hhi ⊢
      refine goodRoundIn_normalize spec _ _ _ ?_ hlo hhi
      intro h0; rw [h0, Int.cast_zero, zero_mul] at hlo; exact not_tiny_zero hlo

theorem mag_mul (m₁ m₂ : Nat) (e₁ e₂ : Int) : mag (m₁ * m₂) (e₁ + e₂) = mag m₁ e₁ * mag m₂ e₂ := by
  unfold mag; rw [zpow_add₀ two_ne_zero]; push_cast; ring

/-- The exact product of two finite nonzero floats as a signed magnitude. -/
theorem mul_key (s₁ s₂ : Sign) (m₁ m₂ : Nat) (e₁ e₂ : Int) (hm₁ : 0 < m₁) (hm₂ : 0 < m₂) :
    (UnpackedFloat.finite s₁ m₁ e₁ hm₁).toReal * (UnpackedFloat.finite s₂ m₂ e₂ hm₂).toReal
      = (s₁ * s₂).toReal * mag (m₁ * m₂) (e₁ + e₂) := by
  rw [toReal_finite, toReal_finite, Sign.toReal_mul, mag_mul]; ring

theorem abs_sign_mag (s : Sign) (m : Nat) (e : Int) : |s.toReal * mag m e| = mag m e := by
  rw [abs_mul, Sign.abs_toReal, one_mul, abs_of_nonneg]; unfold mag; positivity

/-- A product of canonical mantissas has at least `k` bits unless its exponent is at the
bottom of the range. -/
theorem mul_log2_or {spec : Format} {s₁ s₂ : Sign} {m₁ m₂ : Nat} {e₁ e₂ : Int}
    {hm₁ : 0 < m₁} {hm₂ : 0 < m₂}
    (cu : CanonicalIn spec (.finite s₁ m₁ e₁ hm₁)) (cv : CanonicalIn spec (.finite s₂ m₂ e₂ hm₂)) :
    spec.mantissaBitsWithoutImplicit ≤ (m₁ * m₂).log2 ∨ e₁ + e₂ ≤ spec.minExponent := by
  obtain ⟨c₁, -, -, h₁'⟩ := cu
  obtain ⟨c₂, -, -, h₂'⟩ := cv
  have hneg := Format.minExponent_nonpos spec
  by_cases he : e₁ + e₂ ≤ spec.minExponent
  · exact Or.inr he
  · left
    have hbig : 2 ^ spec.mantissaBitsWithoutImplicit ≤ m₁ * m₂ := by
      by_cases h : spec.minExponent < e₁
      · exact le_trans (h₁' h) (Nat.le_mul_of_pos_right _ hm₂)
      · exact le_trans (h₂' (by omega)) (Nat.le_mul_of_pos_left _ hm₁)
    exact (Nat.le_log2 (by positivity)).2 hbig

/-- Multiplication of canonical finite unpacked floats, exact product in the normal range. -/
theorem goodRoundIn_mul {spec : Format} {u v : UnpackedFloat} (cu : CanonicalIn spec u)
    (cv : CanonicalIn spec v) (fu : u.isFinite = true) (fv : v.isFinite = true)
    (hlo : (2 : ℝ) ^ spec.normExponent ≤ |u.toReal * v.toReal|)
    (hhi : |u.toReal * v.toReal| ≤ maxFiniteIn spec) :
    GoodRoundIn spec (mul spec u v) (u.toReal * v.toReal) := by
  cases u with
  | infinity _ => simp [isFinite] at fu
  | notANumber => simp [isFinite] at fu
  | zero s₁ =>
    cases v with
    | infinity _ => simp [isFinite] at fv
    | notANumber => simp [isFinite] at fv
    | zero s₂ => exact goodRoundIn_of_exact trivial rfl (by simp [mul, toReal])
    | finite s₂ m₂ e₂ hm₂ => exact goodRoundIn_of_exact trivial rfl (by simp [mul, toReal])
  | finite s₁ m₁ e₁ hm₁ =>
    cases v with
    | infinity _ => simp [isFinite] at fv
    | notANumber => simp [isFinite] at fv
    | zero s₂ => exact goodRoundIn_of_exact trivial rfl (by simp [mul, toReal])
    | finite s₂ m₂ e₂ hm₂ =>
      simp only [mul]
      rw [mul_key] at hlo hhi ⊢
      rw [abs_sign_mag] at hlo hhi
      obtain ⟨M, E, hM, hr, hc, herr⟩ :=
        roundWithAccuracy_exact_real spec (s₁ * s₂) (m₁ * m₂) (e₁ + e₂) (Nat.mul_pos hm₁ hm₂)
          (mul_log2_or cu cv) hlo hhi
      rw [hr]
      exact ⟨hc, rfl, signed_bound hM herr⟩

/-! ### binary64 forms of the unpacked bounds -/

theorem goodRound_finite_round {s : Sign} {m : Nat} {e : Int} (hm : 0 < m)
    (hlo : (2 : ℝ) ^ (-1022 : ℤ) ≤ mag m e) (hhi : mag m e ≤ maxFinite) :
    GoodRound (round Format.binary64 s m e) (s.toReal * mag m e) :=
  (goodRound_iff _ _).2 (goodRoundIn_finite_round hm hlo hhi)

theorem goodRound_of_exact {r : UnpackedFloat} {x : ℝ} (hc : r.Canonical) (hf : r.isFinite = true)
    (hx : r.toReal = x) : GoodRound r x :=
  (goodRound_iff _ _).2 (goodRoundIn_of_exact ((canonical_iff _).1 hc) hf hx)

theorem goodRound_add {u v : UnpackedFloat} (cu : u.Canonical) (cv : v.Canonical)
    (fu : u.isFinite = true) (fv : v.isFinite = true)
    (hlo : (2 : ℝ) ^ (-1022 : ℤ) ≤ |u.toReal + v.toReal|) (hhi : |u.toReal + v.toReal| ≤ maxFinite) :
    GoodRound (add Format.binary64 u v) (u.toReal + v.toReal) :=
  (goodRound_iff _ _).2
    (goodRoundIn_add ((canonical_iff _).1 cu) ((canonical_iff _).1 cv) fu fv hlo hhi)

theorem goodRound_sub {u v : UnpackedFloat} (cu : u.Canonical) (cv : v.Canonical)
    (fu : u.isFinite = true) (fv : v.isFinite = true)
    (hlo : (2 : ℝ) ^ (-1022 : ℤ) ≤ |u.toReal - v.toReal|) (hhi : |u.toReal - v.toReal| ≤ maxFinite) :
    GoodRound (sub Format.binary64 u v) (u.toReal - v.toReal) :=
  (goodRound_iff _ _).2
    (goodRoundIn_sub ((canonical_iff _).1 cu) ((canonical_iff _).1 cv) fu fv hlo hhi)

theorem goodRound_mul {u v : UnpackedFloat} (cu : u.Canonical) (cv : v.Canonical)
    (fu : u.isFinite = true) (fv : v.isFinite = true)
    (hlo : (2 : ℝ) ^ (-1022 : ℤ) ≤ |u.toReal * v.toReal|) (hhi : |u.toReal * v.toReal| ≤ maxFinite) :
    GoodRound (mul Format.binary64 u v) (u.toReal * v.toReal) :=
  (goodRound_iff _ _).2
    (goodRoundIn_mul ((canonical_iff _).1 cu) ((canonical_iff _).1 cv) fu fv hlo hhi)

/-- The largest finite value is nonnegative. -/
theorem maxFiniteIn_nonneg (spec : Format) : 0 ≤ maxFiniteIn spec := by
  unfold maxFiniteIn
  have : (1 : ℝ) ≤ 2 ^ spec.mantissaBits := one_le_pow₀ one_le_two
  have := two_zpow_pos spec.maxExponent
  positivity

/-- Every canonical unpacked float, finite or not, denotes a real of magnitude at most the largest
finite value. -/
theorem abs_toReal_le_maxFiniteIn {spec : Format} {u : UnpackedFloat} (hc : CanonicalIn spec u) :
    |u.toReal| ≤ maxFiniteIn spec := by
  cases u with
  | finite s m e hm =>
    obtain ⟨-, h2, h3, -⟩ := hc
    rw [toReal_finite, abs_sign_mag, mag, maxFiniteIn]
    have hm' : (m : ℝ) + 1 ≤ 2 ^ spec.mantissaBits := by
      exact_mod_cast (show m + 1 ≤ 2 ^ spec.mantissaBits by omega)
    have he : (2 : ℝ) ^ e ≤ 2 ^ spec.maxExponent := zpow_le_zpow_right₀ one_le_two h2
    exact mul_le_mul (by linarith) he (two_zpow_pos e).le (by linarith)
  | _ => simp only [toReal, abs_zero]; exact maxFiniteIn_nonneg spec

end Float.Model.UnpackedFloat

namespace Float

open Float.Model.UnpackedFloat

/-- Transfer a `GoodRoundIn Format.binary64` result through `pack` back to `Float`. -/
theorem goodRoundIn_transfer {r : UnpackedFloat} {x : ℝ} (h : GoodRoundIn Format.binary64 r x) :
    (Float.ofModel (Float.Model.pack r)).IsFinite ∧
      |(Float.ofModel (Float.Model.pack r)).toReal - x| ≤ 2 ^ (-53 : ℤ) * |x| := by
  obtain ⟨hc, hf, herr⟩ := h
  have hu : (Float.ofModel (Float.Model.pack r)).toModel.unpack = r :=
    Float.Model.unpack_pack_of_canonical ((canonical_iff _).2 hc)
  refine ⟨?_, ?_⟩
  · rw [isFinite_iff, hu]; exact hf
  · rw [toReal, hu]; exact herr

/-- Transfer a `GoodRound` result through `pack` back to `Float`. -/
theorem goodRound_transfer {r : UnpackedFloat} {x : ℝ} (h : GoodRound r x) :
    (Float.ofModel (Float.Model.pack r)).IsFinite ∧
      |(Float.ofModel (Float.Model.pack r)).toReal - x| ≤ 2 ^ (-53 : ℤ) * |x| :=
  goodRoundIn_transfer ((goodRound_iff _ _).1 h)

/-- Rounding-error bound for `Float` addition on the normal range (unit roundoff `2^-53`). -/
theorem add_error {a b : Float} (ha : a.IsFinite) (hb : b.IsFinite)
    (hlo : (2 : ℝ) ^ (-1022 : ℤ) ≤ |a.toReal + b.toReal|)
    (hhi : |a.toReal + b.toReal| ≤ maxFinite) :
    (a + b).IsFinite ∧
      |(a + b).toReal - (a.toReal + b.toReal)| ≤ 2 ^ (-53 : ℤ) * |a.toReal + b.toReal| :=
  goodRoundIn_transfer (goodRoundIn_add a.canonicalIn_unpack b.canonicalIn_unpack ha hb hlo hhi)

/-- Rounding-error bound for `Float` subtraction on the normal range. -/
theorem sub_error {a b : Float} (ha : a.IsFinite) (hb : b.IsFinite)
    (hlo : (2 : ℝ) ^ (-1022 : ℤ) ≤ |a.toReal - b.toReal|)
    (hhi : |a.toReal - b.toReal| ≤ maxFinite) :
    (a - b).IsFinite ∧
      |(a - b).toReal - (a.toReal - b.toReal)| ≤ 2 ^ (-53 : ℤ) * |a.toReal - b.toReal| :=
  goodRoundIn_transfer (goodRoundIn_sub a.canonicalIn_unpack b.canonicalIn_unpack ha hb hlo hhi)

/-- Rounding-error bound for `Float` multiplication on the normal range. -/
theorem mul_error {a b : Float} (ha : a.IsFinite) (hb : b.IsFinite)
    (hlo : (2 : ℝ) ^ (-1022 : ℤ) ≤ |a.toReal * b.toReal|)
    (hhi : |a.toReal * b.toReal| ≤ maxFinite) :
    (a * b).IsFinite ∧
      |(a * b).toReal - a.toReal * b.toReal| ≤ 2 ^ (-53 : ℤ) * |a.toReal * b.toReal| :=
  goodRoundIn_transfer (goodRoundIn_mul a.canonicalIn_unpack b.canonicalIn_unpack ha hb hlo hhi)

/-- Relative-error bound to the "standard model" `fl(x) = x (1 + δ)`, `|δ| ≤ u`. -/
theorem std_model {r x u : ℝ} (hx : x ≠ 0) (h : |r - x| ≤ u * |x|) :
    ∃ δ : ℝ, |δ| ≤ u ∧ r = x * (1 + δ) := by
  refine ⟨(r - x) / x, ?_, ?_⟩
  · rw [abs_div]; exact (div_le_iff₀ (abs_pos.2 hx)).2 h
  · field_simp; ring

theorem add_std_model {a b : Float} (ha : a.IsFinite) (hb : b.IsFinite)
    (hlo : (2 : ℝ) ^ (-1022 : ℤ) ≤ |a.toReal + b.toReal|)
    (hhi : |a.toReal + b.toReal| ≤ maxFinite) :
    ∃ δ : ℝ, |δ| ≤ 2 ^ (-53 : ℤ) ∧ (a + b).toReal = (a.toReal + b.toReal) * (1 + δ) :=
  std_model (fun h0 => not_tiny_zero (h0 ▸ hlo)) (add_error ha hb hlo hhi).2

theorem sub_std_model {a b : Float} (ha : a.IsFinite) (hb : b.IsFinite)
    (hlo : (2 : ℝ) ^ (-1022 : ℤ) ≤ |a.toReal - b.toReal|)
    (hhi : |a.toReal - b.toReal| ≤ maxFinite) :
    ∃ δ : ℝ, |δ| ≤ 2 ^ (-53 : ℤ) ∧ (a - b).toReal = (a.toReal - b.toReal) * (1 + δ) :=
  std_model (fun h0 => not_tiny_zero (h0 ▸ hlo)) (sub_error ha hb hlo hhi).2

theorem mul_std_model {a b : Float} (ha : a.IsFinite) (hb : b.IsFinite)
    (hlo : (2 : ℝ) ^ (-1022 : ℤ) ≤ |a.toReal * b.toReal|)
    (hhi : |a.toReal * b.toReal| ≤ maxFinite) :
    ∃ δ : ℝ, |δ| ≤ 2 ^ (-53 : ℤ) ∧ (a * b).toReal = (a.toReal * b.toReal) * (1 + δ) :=
  std_model (fun h0 => not_tiny_zero (h0 ▸ hlo)) (mul_error ha hb hlo hhi).2

/-- Every float, finite or not, denotes a real of magnitude at most `maxFinite`. -/
theorem abs_toReal_le_maxFinite (f : Float) : |f.toReal| ≤ maxFinite :=
  abs_toReal_le_maxFiniteIn f.canonicalIn_unpack

/-- `maxFinite` is the familiar `(2 - 2^-52) · 2^1023`. -/
theorem maxFinite_eq : maxFinite = (2 - 2 ^ (-52 : ℤ)) * 2 ^ (1023 : ℤ) := by
  rw [maxFinite, show (1023 : ℤ) = 52 + 971 by norm_num, zpow_add₀ two_ne_zero]
  have : (2 : ℝ) ^ (52 : ℤ) * 2 ^ (-52 : ℤ) = 1 := by
    rw [← zpow_add₀ two_ne_zero]; norm_num
  have h53 : (2 : ℝ) ^ 53 = 2 * 2 ^ (52 : ℤ) := by norm_num
  rw [h53]; linear_combination (2 : ℝ) ^ (971 : ℤ) * this

end Float
