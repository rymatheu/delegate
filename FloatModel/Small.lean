/-
Rounding below the normal range, generic over the format: `+`, `-`, `*` when the exact result `x`
satisfies `|x| < 2^normExponent` (`2^-1022` for binary64, `2^-126` for binary32).

Every finite float is a multiple of `2^minExponent` (`2^-1074`, `2^-149`), so a sum or difference
of two of them is a multiple of it too; below the normal range such a number is a subnormal (or
zero) and the model computes it exactly. A product is rounded to the subnormal grid
`2^minExponent ℤ`, so its absolute error is at most half that spacing, `2^(minExponent - 1)`
(`2^-1075`, `2^-150`). Together with the normal-range bounds of `FloatModel.Add` this gives the
error bounds for every exact result up to the largest finite value (`sub_err_all`, `add_err_all`,
`mul_err_all`; binary64 here, binary32 in `FloatModel.Float32`).

The generic lemmas that build a subnormal result take `hw : 2 ≤ spec.exponentBits`, which makes
the subnormal exponent `minExponent` at most `maxExponent`.
-/
import FloatModel.Add

open Float.Model UnpackedFloat

namespace Float.Model.UnpackedFloat

open ExtendedMantissa

/-! ## `roundWithAccuracy` and `round` on the subnormal grid -/

/-- On an exact input whose total exponent is below the normal range and whose exponent is at most
`minExponent`, `roundWithAccuracy` shifts by `n = minExponent - e` bits onto the subnormal grid,
and the second (renormalizing) shift is trivial. -/
theorem roundWithAccuracy_small (spec : Format) (s : Sign) (m : Nat) (e : Int)
    (hT : (m.log2 : Int) + e ≤ spec.normExponent - 1) (he : e ≤ spec.minExponent) :
    ∃ M₀ : Nat, roundWithAccuracy spec s m e .exact = mkFin s M₀ spec.minExponent ∧
      M₀ ≤ 2 ^ spec.mantissaBitsWithoutImplicit ∧
      2 * m ≤ 2 * (M₀ * 2 ^ (spec.minExponent - e).toNat) + 2 ^ (spec.minExponent - e).toNat ∧
      2 * (M₀ * 2 ^ (spec.minExponent - e).toNat) ≤ 2 * m + 2 ^ (spec.minExponent - e).toNat := by
  have hPk := Format.mantissaBits_eq spec
  have hnorm := Format.normExponent_eq spec
  rw [roundWithAccuracy_eq_mkFin]
  set k := spec.mantissaBitsWithoutImplicit with hk
  set n := (spec.minExponent - e).toNat with hn
  rw [shiftToTargetExponent_exact spec m e n (by omega)]
  simp only
  obtain ⟨hMq, hlo, hhi⟩ := round_shift m n
  generalize ((⟨m, false, false⟩ : ExtendedMantissa) >>> n).roundedMantissa = M₀ at hMq hlo hhi ⊢
  have hmL' : m < 2 ^ (m.log2 + 1) := Nat.lt_log2_self
  have hpow : 2 ^ (m.log2 + 1) ≤ 2 ^ k * 2 ^ n := by
    rw [← Nat.pow_add]; exact Nat.pow_le_pow_right (by norm_num) (by omega)
  have hq : m / 2 ^ n < 2 ^ k := (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos n)).2 (by omega)
  have hM : M₀ ≤ 2 ^ k := by omega
  have hlog : M₀.log2 ≤ k := by
    rcases Nat.eq_zero_or_pos M₀ with h0 | h0
    · subst h0; simp
    · have := (Nat.log2_lt (by omega)).2 (show M₀ < 2 ^ (k + 1) by rw [Nat.pow_succ]; omega)
      omega
  rw [shiftToTargetExponent_exact spec M₀ (e + n) 0 (by omega)]
  simp only [mantissa_shiftRight, pow_zero, Nat.div_one]
  exact ⟨M₀, by congr 1; omega, hM, hlo, hhi⟩

theorem toReal_mkFin (s : Sign) (M : Nat) (E : Int) : (mkFin s M E).toReal = s.toReal * mag M E := by
  unfold mkFin
  split_ifs with h
  · subst h; simp [toReal, mag]
  · exact toReal_finite _ _ _ _

theorem isFinite_mkFin (s : Sign) (M : Nat) (E : Int) : (mkFin s M E).isFinite = true := by
  unfold mkFin; split_ifs <;> rfl

theorem canonicalIn_mkFin (spec : Format) (hw : 2 ≤ spec.exponentBits) (s : Sign) (M : Nat)
    (hM : M < 2 ^ spec.mantissaBits) : CanonicalIn spec (mkFin s M spec.minExponent) := by
  have hb := Format.one_le_exponentBias spec hw
  have hmin := Format.minExponent_eq spec
  unfold mkFin
  split_ifs
  · trivial
  · refine ⟨le_refl _, ?_, hM, fun h => absurd h (lt_irrefl _)⟩
    simp only [Format.maxExponent]; omega

/-- A magnitude below the normal range has total exponent below it. -/
theorem log2_add_le_of_small {m : Nat} (hm : 0 < m) {e N : Int}
    (h : mag m e < (2 : ℝ) ^ N) : (m.log2 : Int) + e ≤ N - 1 := by
  have hmL : 2 ^ m.log2 ≤ m := Nat.log2_self_le (by omega)
  have h1 : (2 : ℝ) ^ ((m.log2 : Int) + e) ≤ mag m e := by
    rw [zpow_add₀ two_ne_zero, mag, zpow_natCast]
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hmL) (two_zpow_pos e).le
  have := (zpow_lt_zpow_iff_right₀ one_lt_two).1 (lt_of_le_of_lt h1 h)
  omega

/-- The integer half-ulp bounds of a shift by `n` onto exponent `E₀`, read in `ℝ`. -/
theorem small_real_bound {m M₀ n : Nat} {e E₀ : Int} (hen : e + n = E₀)
    (hlo : 2 * m ≤ 2 * (M₀ * 2 ^ n) + 2 ^ n) (hhi : 2 * (M₀ * 2 ^ n) ≤ 2 * m + 2 ^ n) :
    |mag M₀ E₀ - mag m e| ≤ 2 ^ (E₀ - 1) := by
  have hlo' : (2 * m : ℝ) ≤ 2 * (M₀ * 2 ^ n) + 2 ^ n := by exact_mod_cast hlo
  have hhi' : (2 * (M₀ * 2 ^ n) : ℝ) ≤ 2 * m + 2 ^ n := by exact_mod_cast hhi
  have he := two_zpow_pos e
  have hE : (2 : ℝ) ^ E₀ = 2 ^ n * 2 ^ e := by
    rw [← hen, add_comm, zpow_add₀ two_ne_zero, zpow_natCast]
  have hE' : (2 : ℝ) ^ (E₀ - 1) = 2 ^ E₀ / 2 := by
    rw [zpow_sub₀ two_ne_zero, zpow_one]
  have hk : |(M₀ : ℝ) * 2 ^ n - m| ≤ 2 ^ n / 2 := by
    rw [abs_le]; constructor <;> linarith
  rw [hE', hE, mag, mag, hE,
    show (M₀ : ℝ) * (2 ^ n * 2 ^ e) - m * 2 ^ e = ((M₀ : ℝ) * 2 ^ n - m) * 2 ^ e by ring,
    abs_mul, abs_of_pos he, show (2 : ℝ) ^ n * 2 ^ e / 2 = 2 ^ n / 2 * 2 ^ e by ring]
  exact mul_le_mul_of_nonneg_right hk he.le

/-- `round` below the normal range lands on the subnormal grid, within `2^(minExponent - 1)`,
and exactly when the input exponent is already at least `minExponent`. -/
theorem round_small (spec : Format) (s : Sign) (m : Nat) (e : Int) (hm : 0 < m)
    (hsmall : mag m e < (2 : ℝ) ^ spec.normExponent) :
    ∃ M₀ : Nat, round spec s m e = mkFin s M₀ spec.minExponent ∧
      M₀ ≤ 2 ^ spec.mantissaBitsWithoutImplicit ∧
      |mag M₀ spec.minExponent - mag m e| ≤ 2 ^ (spec.minExponent - 1) ∧
      (spec.minExponent ≤ e → mag M₀ spec.minExponent = mag m e) := by
  have hPk := Format.mantissaBits_eq spec
  have hnorm := Format.normExponent_eq spec
  have hT := log2_add_le_of_small hm hsmall
  simp only [round, decreaseExponent, Nat.shiftLeft_eq]
  set k := (e - spec.targetExponent (totalExponent m e)).toNat with hk
  have hk' : k = (e - spec.minExponent).toNat := by
    rw [hk, round_shift_amount]; omega
  have hmag := mag_mul_two_pow m k e
  have hlog := log2_mul_two_pow m k hm
  obtain ⟨M₀, hr, hM, hlo, hhi⟩ :=
    roundWithAccuracy_small spec s (m * 2 ^ k) (e - k) (by rw [hlog]; push_cast; omega) (by omega)
  refine ⟨M₀, hr, hM, ?_, fun he => ?_⟩
  · rw [← hmag]; exact small_real_bound (by omega) hlo hhi
  · have hn : (spec.minExponent - (e - (k : Int))).toNat = 0 := by omega
    rw [hn, pow_zero, Nat.mul_one] at hlo hhi
    have hM₀ : M₀ = m * 2 ^ k := by omega
    rw [← hmag, hM₀, show e - (k : Int) = spec.minExponent by omega]

/-- An unpacked result equal to the exact value. -/
def ExactRoundIn (spec : Format) (r : UnpackedFloat) (x : ℝ) : Prop :=
  CanonicalIn spec r ∧ r.isFinite = true ∧ r.toReal = x

/-- `normalize` of an integer mantissa on an exponent `≥ minExponent` with a value below the
normal range is exact. -/
theorem exactRoundIn_normalize (spec : Format) (hw : 2 ≤ spec.exponentBits) (N : Int) (E : Int)
    (zs : Sign) (hE0 : spec.minExponent ≤ E)
    (hsmall : |(N : ℝ) * 2 ^ E| < (2 : ℝ) ^ spec.normExponent) :
    ExactRoundIn spec (normalize spec N E zs) ((N : ℝ) * 2 ^ E) := by
  have hP := two_pow_mantissaBits spec
  have hk0 := Nat.two_pow_pos spec.mantissaBitsWithoutImplicit
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
    obtain ⟨M₀, hr, hM, -, hex⟩ := round_small spec .negative (-N).toNat E hm (hmag ▸ hsmall)
    rw [hr]
    refine ⟨canonicalIn_mkFin spec hw _ _ (by omega), isFinite_mkFin _ _ _, ?_⟩
    rw [toReal_mkFin, hex hE0, hmag, abs_of_neg hneg]; simp [Sign.toReal]
  · subst h; exact ⟨trivial, rfl, by simp [toReal]⟩
  · rw [Int.compare_eq_gt.2 h]
    have hm : 0 < N.toNat := by omega
    have hmag : mag N.toNat E = (N : ℝ) * 2 ^ E := by
      rw [mag]; congr 1
      have : ((N.toNat : Int) : ℝ) = (N : ℝ) := by congr 1; omega
      exact_mod_cast this
    have hpos : 0 < (N : ℝ) * 2 ^ E := mul_pos (by exact_mod_cast h) hE
    rw [abs_of_pos hpos] at hsmall
    obtain ⟨M₀, hr, hM, -, hex⟩ := round_small spec .positive N.toNat E hm (hmag ▸ hsmall)
    rw [hr]
    refine ⟨canonicalIn_mkFin spec hw _ _ (by omega), isFinite_mkFin _ _ _, ?_⟩
    rw [toReal_mkFin, hex hE0, hmag]; simp [Sign.toReal]

/-- `normalize` of an integer mantissa on an exponent `≥ minExponent`, on every value up to the
largest finite value: exact below the normal range, relative error `2^-P` above. -/
theorem goodRoundIn_normalize_all (spec : Format) (hw : 2 ≤ spec.exponentBits) (N : Int) (E : Int)
    (zs : Sign) (hE0 : spec.minExponent ≤ E) (hhi : |(N : ℝ) * 2 ^ E| ≤ maxFiniteIn spec) :
    GoodRoundIn spec (normalize spec N E zs) ((N : ℝ) * 2 ^ E) := by
  rcases lt_or_ge |(N : ℝ) * 2 ^ E| ((2 : ℝ) ^ spec.normExponent) with h | h
  · obtain ⟨hc, hf, hx⟩ := exactRoundIn_normalize spec hw N E zs hE0 h
    exact goodRoundIn_of_exact hc hf hx
  · refine goodRoundIn_normalize spec N E zs ?_ h hhi
    rintro rfl; rw [Int.cast_zero, zero_mul] at h; exact not_tiny_zero h

/-- `normalize` of an integer mantissa on an exponent `≥ -1074`, on every value up to `maxFinite`:
exact below `2^-1022`, relative error `2^-53` above. -/
theorem goodRound_normalize_all (N : Int) (E : Int) (zs : Sign) (hE0 : -1074 ≤ E)
    (hhi : |(N : ℝ) * 2 ^ E| ≤ maxFinite) :
    GoodRound (normalize Format.binary64 N E zs) ((N : ℝ) * 2 ^ E) :=
  (goodRound_iff _ _).2 (goodRoundIn_normalize_all Format.binary64 (by decide) N E zs hE0 hhi)

/-! ## Subtraction and addition below the normal range are exact -/

theorem exactRoundIn_sub {spec : Format} (hw : 2 ≤ spec.exponentBits) {u v : UnpackedFloat}
    (cu : CanonicalIn spec u) (cv : CanonicalIn spec v)
    (fu : u.isFinite = true) (fv : v.isFinite = true)
    (hsmall : |u.toReal - v.toReal| < (2 : ℝ) ^ spec.normExponent) :
    ExactRoundIn spec (sub spec u v) (u.toReal - v.toReal) := by
  cases u with
  | infinity _ => simp [isFinite] at fu
  | notANumber => simp [isFinite] at fu
  | zero s₁ =>
    cases v with
    | infinity _ => simp [isFinite] at fv
    | notANumber => simp [isFinite] at fv
    | zero s₂ =>
      refine ⟨?_, ?_, ?_⟩ <;> simp only [sub] <;> split_ifs <;> simp [toReal, CanonicalIn, isFinite]
    | finite s₂ m₂ e₂ hm₂ =>
      refine ⟨cv, rfl, ?_⟩
      have := toReal_neg (.finite s₂ m₂ e₂ hm₂)
      simp only [neg] at this
      simp only [sub, this]; simp [toReal]
  | finite s₁ m₁ e₁ hm₁ =>
    cases v with
    | infinity _ => simp [isFinite] at fv
    | notANumber => simp [isFinite] at fv
    | zero s₂ => exact ⟨cu, rfl, by simp [sub, toReal]⟩
    | finite s₂ m₂ e₂ hm₂ =>
      simp only [sub, decreaseExponent]
      rw [← sub_key s₁ s₂ m₁ m₂ e₁ e₂ hm₁ hm₂] at hsmall ⊢
      exact exactRoundIn_normalize spec hw _ _ _ (le_min cu.1 cv.1) hsmall

theorem exactRoundIn_add {spec : Format} (hw : 2 ≤ spec.exponentBits) {u v : UnpackedFloat}
    (cu : CanonicalIn spec u) (cv : CanonicalIn spec v)
    (fu : u.isFinite = true) (fv : v.isFinite = true)
    (hsmall : |u.toReal + v.toReal| < (2 : ℝ) ^ spec.normExponent) :
    ExactRoundIn spec (add spec u v) (u.toReal + v.toReal) := by
  cases u with
  | infinity _ => simp [isFinite] at fu
  | notANumber => simp [isFinite] at fu
  | zero s₁ =>
    cases v with
    | infinity _ => simp [isFinite] at fv
    | notANumber => simp [isFinite] at fv
    | zero s₂ =>
      refine ⟨?_, ?_, ?_⟩ <;> simp only [add] <;> split_ifs <;> simp [toReal, CanonicalIn, isFinite]
    | finite s₂ m₂ e₂ hm₂ => exact ⟨cv, rfl, by simp [add, toReal]⟩
  | finite s₁ m₁ e₁ hm₁ =>
    cases v with
    | infinity _ => simp [isFinite] at fv
    | notANumber => simp [isFinite] at fv
    | zero s₂ => exact ⟨cu, rfl, by simp [add, toReal]⟩
    | finite s₂ m₂ e₂ hm₂ =>
      simp only [add, decreaseExponent]
      rw [← add_key s₁ s₂ m₁ m₂ e₁ e₂ hm₁ hm₂] at hsmall ⊢
      exact exactRoundIn_normalize spec hw _ _ _ (le_min cu.1 cv.1) hsmall

/-! ## Multiplication below the normal range: absolute error `2^(minExponent - 1)` -/

/-- An unpacked result within absolute error `2^(minExponent - 1)` of the exact value. -/
def SmallRoundIn (spec : Format) (r : UnpackedFloat) (x : ℝ) : Prop :=
  CanonicalIn spec r ∧ r.isFinite = true ∧ |r.toReal - x| ≤ 2 ^ (spec.minExponent - 1)

theorem smallRoundIn_of_exact {spec : Format} {r : UnpackedFloat} {x : ℝ} (hc : CanonicalIn spec r)
    (hf : r.isFinite = true) (hx : r.toReal = x) : SmallRoundIn spec r x := by
  refine ⟨hc, hf, ?_⟩
  rw [hx, sub_self, abs_zero]; exact (two_zpow_pos _).le

theorem smallRoundIn_mul {spec : Format} (hw : 2 ≤ spec.exponentBits) {u v : UnpackedFloat}
    (cu : CanonicalIn spec u) (cv : CanonicalIn spec v)
    (fu : u.isFinite = true) (fv : v.isFinite = true)
    (hsmall : |u.toReal * v.toReal| < (2 : ℝ) ^ spec.normExponent) :
    SmallRoundIn spec (mul spec u v) (u.toReal * v.toReal) := by
  have hP := two_pow_mantissaBits spec
  have hk0 := Nat.two_pow_pos spec.mantissaBitsWithoutImplicit
  have hnorm := Format.normExponent_eq spec
  cases u with
  | infinity _ => simp [isFinite] at fu
  | notANumber => simp [isFinite] at fu
  | zero s₁ =>
    cases v with
    | infinity _ => simp [isFinite] at fv
    | notANumber => simp [isFinite] at fv
    | zero s₂ => exact smallRoundIn_of_exact trivial rfl (by simp [mul, toReal])
    | finite s₂ m₂ e₂ hm₂ => exact smallRoundIn_of_exact trivial rfl (by simp [mul, toReal])
  | finite s₁ m₁ e₁ hm₁ =>
    cases v with
    | infinity _ => simp [isFinite] at fv
    | notANumber => simp [isFinite] at fv
    | zero s₂ => exact smallRoundIn_of_exact trivial rfl (by simp [mul, toReal])
    | finite s₂ m₂ e₂ hm₂ =>
      simp only [mul]
      rw [mul_key] at hsmall ⊢
      rw [abs_sign_mag] at hsmall
      have hmm : 0 < m₁ * m₂ := Nat.mul_pos hm₁ hm₂
      have hT := log2_add_le_of_small hmm hsmall
      have he : e₁ + e₂ ≤ spec.minExponent := by
        rcases mul_log2_or cu cv with h | h
        · omega
        · exact h
      obtain ⟨M₀, hr, hM, hlo, hhi⟩ :=
        roundWithAccuracy_small spec (s₁ * s₂) (m₁ * m₂) (e₁ + e₂) hT he
      rw [hr]
      refine ⟨canonicalIn_mkFin spec hw _ _ (by omega), isFinite_mkFin _ _ _, ?_⟩
      rw [toReal_mkFin, ← mul_sub, abs_mul, Sign.abs_toReal, one_mul]
      exact small_real_bound (by omega) hlo hhi

/-! ### binary64 forms -/

theorem canonical_mkFin (s : Sign) (M : Nat) (hM : M < 2 ^ 53) :
    (mkFin s M (-1074)).Canonical :=
  (canonical_iff _).2 (canonicalIn_mkFin Format.binary64 (by decide) s M hM)

/-- An unpacked binary64 result equal to the exact value. -/
def ExactRound (r : UnpackedFloat) (x : ℝ) : Prop :=
  r.Canonical ∧ r.isFinite = true ∧ r.toReal = x

theorem exactRound_iff (r : UnpackedFloat) (x : ℝ) :
    ExactRound r x ↔ ExactRoundIn Format.binary64 r x := by
  rw [ExactRound, ExactRoundIn, canonical_iff]

theorem exactRound_normalize (N : Int) (E : Int) (zs : Sign) (hE0 : -1074 ≤ E)
    (hsmall : |(N : ℝ) * 2 ^ E| < (2 : ℝ) ^ (-1022 : ℤ)) :
    ExactRound (normalize Format.binary64 N E zs) ((N : ℝ) * 2 ^ E) :=
  (exactRound_iff _ _).2 (exactRoundIn_normalize Format.binary64 (by decide) N E zs hE0 hsmall)

theorem exactRound_sub {u v : UnpackedFloat} (cu : u.Canonical) (cv : v.Canonical)
    (fu : u.isFinite = true) (fv : v.isFinite = true)
    (hsmall : |u.toReal - v.toReal| < (2 : ℝ) ^ (-1022 : ℤ)) :
    ExactRound (sub Format.binary64 u v) (u.toReal - v.toReal) :=
  (exactRound_iff _ _).2
    (exactRoundIn_sub (by decide) ((canonical_iff _).1 cu) ((canonical_iff _).1 cv) fu fv hsmall)

theorem exactRound_add {u v : UnpackedFloat} (cu : u.Canonical) (cv : v.Canonical)
    (fu : u.isFinite = true) (fv : v.isFinite = true)
    (hsmall : |u.toReal + v.toReal| < (2 : ℝ) ^ (-1022 : ℤ)) :
    ExactRound (add Format.binary64 u v) (u.toReal + v.toReal) :=
  (exactRound_iff _ _).2
    (exactRoundIn_add (by decide) ((canonical_iff _).1 cu) ((canonical_iff _).1 cv) fu fv hsmall)

/-- An unpacked binary64 result within absolute error `2^-1075` of the exact value. -/
def SmallRound (r : UnpackedFloat) (x : ℝ) : Prop :=
  r.Canonical ∧ r.isFinite = true ∧ |r.toReal - x| ≤ 2 ^ (-1075 : ℤ)

theorem smallRound_iff (r : UnpackedFloat) (x : ℝ) :
    SmallRound r x ↔ SmallRoundIn Format.binary64 r x := by
  rw [SmallRound, SmallRoundIn, canonical_iff]; rfl

theorem smallRound_of_exact {r : UnpackedFloat} {x : ℝ} (hc : r.Canonical) (hf : r.isFinite = true)
    (hx : r.toReal = x) : SmallRound r x :=
  (smallRound_iff _ _).2 (smallRoundIn_of_exact ((canonical_iff _).1 hc) hf hx)

theorem smallRound_mul {u v : UnpackedFloat} (cu : u.Canonical) (cv : v.Canonical)
    (fu : u.isFinite = true) (fv : v.isFinite = true)
    (hsmall : |u.toReal * v.toReal| < (2 : ℝ) ^ (-1022 : ℤ)) :
    SmallRound (mul Format.binary64 u v) (u.toReal * v.toReal) :=
  (smallRound_iff _ _).2
    (smallRoundIn_mul (by decide) ((canonical_iff _).1 cu) ((canonical_iff _).1 cv) fu fv hsmall)

end Float.Model.UnpackedFloat

namespace Float

open Float.Model.UnpackedFloat

theorem exactRoundIn_transfer {r : UnpackedFloat} {x : ℝ} (h : ExactRoundIn Format.binary64 r x) :
    (Float.ofModel (Float.Model.pack r)).IsFinite ∧ (Float.ofModel (Float.Model.pack r)).toReal = x := by
  obtain ⟨hc, hf, hx⟩ := h
  have hu : (Float.ofModel (Float.Model.pack r)).toModel.unpack = r :=
    Float.Model.unpack_pack_of_canonical ((canonical_iff _).2 hc)
  exact ⟨by rw [isFinite_iff, hu]; exact hf, by rw [toReal, hu]; exact hx⟩

theorem smallRoundIn_transfer {r : UnpackedFloat} {x : ℝ} (h : SmallRoundIn Format.binary64 r x) :
    (Float.ofModel (Float.Model.pack r)).IsFinite ∧
      |(Float.ofModel (Float.Model.pack r)).toReal - x| ≤ 2 ^ (-1075 : ℤ) := by
  obtain ⟨hc, hf, hx⟩ := h
  have hu : (Float.ofModel (Float.Model.pack r)).toModel.unpack = r :=
    Float.Model.unpack_pack_of_canonical ((canonical_iff _).2 hc)
  exact ⟨by rw [isFinite_iff, hu]; exact hf, by rw [toReal, hu]; exact hx⟩

theorem exactRound_transfer {r : UnpackedFloat} {x : ℝ} (h : ExactRound r x) :
    (Float.ofModel (Float.Model.pack r)).IsFinite ∧ (Float.ofModel (Float.Model.pack r)).toReal = x :=
  exactRoundIn_transfer ((exactRound_iff _ _).1 h)

theorem smallRound_transfer {r : UnpackedFloat} {x : ℝ} (h : SmallRound r x) :
    (Float.ofModel (Float.Model.pack r)).IsFinite ∧
      |(Float.ofModel (Float.Model.pack r)).toReal - x| ≤ 2 ^ (-1075 : ℤ) :=
  smallRoundIn_transfer ((smallRound_iff _ _).1 h)

/-- A difference of finite floats below `2^-1022` in magnitude is computed exactly. -/
theorem sub_error_small {a b : Float} (ha : a.IsFinite) (hb : b.IsFinite)
    (hsmall : |a.toReal - b.toReal| < (2 : ℝ) ^ (-1022 : ℤ)) :
    (a - b).IsFinite ∧ (a - b).toReal = a.toReal - b.toReal :=
  exactRoundIn_transfer
    (exactRoundIn_sub (by decide) a.canonicalIn_unpack b.canonicalIn_unpack ha hb hsmall)

/-- A sum of finite floats below `2^-1022` in magnitude is computed exactly. -/
theorem add_error_small {a b : Float} (ha : a.IsFinite) (hb : b.IsFinite)
    (hsmall : |a.toReal + b.toReal| < (2 : ℝ) ^ (-1022 : ℤ)) :
    (a + b).IsFinite ∧ (a + b).toReal = a.toReal + b.toReal :=
  exactRoundIn_transfer
    (exactRoundIn_add (by decide) a.canonicalIn_unpack b.canonicalIn_unpack ha hb hsmall)

/-- A product of finite floats below `2^-1022` in magnitude is within `2^-1075` (half the subnormal
spacing). -/
theorem mul_error_small {a b : Float} (ha : a.IsFinite) (hb : b.IsFinite)
    (hsmall : |a.toReal * b.toReal| < (2 : ℝ) ^ (-1022 : ℤ)) :
    (a * b).IsFinite ∧ |(a * b).toReal - a.toReal * b.toReal| ≤ 2 ^ (-1075 : ℤ) :=
  smallRoundIn_transfer
    (smallRoundIn_mul (by decide) a.canonicalIn_unpack b.canonicalIn_unpack ha hb hsmall)

/-- Rounding-error bound for `Float` subtraction on every exact result up to `maxFinite`. -/
theorem sub_err_all {a b : Float} (ha : a.IsFinite) (hb : b.IsFinite)
    (hhi : |a.toReal - b.toReal| ≤ maxFinite) :
    (a - b).IsFinite ∧
      |(a - b).toReal - (a.toReal - b.toReal)| ≤ 2 ^ (-53 : ℤ) * |a.toReal - b.toReal| := by
  rcases lt_or_ge |a.toReal - b.toReal| ((2 : ℝ) ^ (-1022 : ℤ)) with h | h
  · obtain ⟨hf, hx⟩ := sub_error_small ha hb h
    refine ⟨hf, ?_⟩
    rw [hx, sub_self, abs_zero]; positivity
  · exact sub_error ha hb h hhi

/-- Rounding-error bound for `Float` addition on every exact result up to `maxFinite`. -/
theorem add_err_all {a b : Float} (ha : a.IsFinite) (hb : b.IsFinite)
    (hhi : |a.toReal + b.toReal| ≤ maxFinite) :
    (a + b).IsFinite ∧
      |(a + b).toReal - (a.toReal + b.toReal)| ≤ 2 ^ (-53 : ℤ) * |a.toReal + b.toReal| := by
  rcases lt_or_ge |a.toReal + b.toReal| ((2 : ℝ) ^ (-1022 : ℤ)) with h | h
  · obtain ⟨hf, hx⟩ := add_error_small ha hb h
    refine ⟨hf, ?_⟩
    rw [hx, sub_self, abs_zero]; positivity
  · exact add_error ha hb h hhi

/-- Rounding-error bound for `Float` multiplication on every exact result up to `maxFinite`:
relative error `2^-53` plus absolute underflow error `2^-1075`. -/
theorem mul_err_all {a b : Float} (ha : a.IsFinite) (hb : b.IsFinite)
    (hhi : |a.toReal * b.toReal| ≤ maxFinite) :
    (a * b).IsFinite ∧
      |(a * b).toReal - a.toReal * b.toReal| ≤
        2 ^ (-53 : ℤ) * |a.toReal * b.toReal| + 2 ^ (-1075 : ℤ) := by
  rcases lt_or_ge |a.toReal * b.toReal| ((2 : ℝ) ^ (-1022 : ℤ)) with h | h
  · obtain ⟨hf, hx⟩ := mul_error_small ha hb h
    refine ⟨hf, hx.trans ?_⟩
    have : 0 ≤ (2 : ℝ) ^ (-53 : ℤ) * |a.toReal * b.toReal| := by positivity
    linarith
  · obtain ⟨hf, hx⟩ := mul_error ha hb h hhi
    refine ⟨hf, hx.trans ?_⟩
    linarith [two_zpow_pos (-1075)]

end Float
