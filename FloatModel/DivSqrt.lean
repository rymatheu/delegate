/-
Rounding bounds for division and square root, generic over the format.

`FloatModel.Add` bounds the rounding of `+`, `-`, `*`, whose exact results reach
`roundWithAccuracy` with accuracy `exact`. Division and square root reach it with the accuracy that
`divCore` and `sqrtCore` compute from the remainder of an integer quotient or integer square root.
Whenever the accuracy correctly describes the real value `v` that the mantissa truncates (`AccOK`),
`roundWithAccuracy spec` rounds `v · 2^e` to nearest within `2^-P |x| + 2^(minExponent - 1)`
(`roundWithAccuracy_real`). The key invariant is that every one-bit shift of an extended mantissa
keeps its round and sticky bits a correct description of the shifted value (`cons_shiftRightOne`).
The division and square-root cores produce correct accuracies and enough quotient bits
(`divCore_spec`, `sqrtCore_spec`), which gives the bounds on `UnpackedFloat.div` and
`UnpackedFloat.sqrt` (`nearRoundIn_div`, `nearRoundIn_sqrt`) and the binary64 statements
`Float.div_err_all`, `Float.sqrt_err_all` (binary32 in `FloatModel.Float32`).
-/
import FloatModel.Small
import Mathlib.Analysis.SpecialFunctions.Sqrt

open Float.Model UnpackedFloat ExtendedMantissa

namespace Float.Model.UnpackedFloat

/-! ## Extended mantissas that describe a real -/

/-- `em` describes `v ≥ 0`: its mantissa is `⌊v⌋`, its round bit says `v` is at least half way to
the next integer, its sticky bit that `v` is neither an integer nor a half-integer. -/
def Cons (em : ExtendedMantissa) (v : ℝ) : Prop :=
  (em.mantissa : ℝ) ≤ v ∧ v < em.mantissa + 1 ∧
  (em.roundBit = true ↔ (em.mantissa : ℝ) + 1/2 ≤ v) ∧
  (em.stickyBit = true ↔ (v ≠ em.mantissa ∧ v ≠ em.mantissa + 1/2))

theorem cons_shiftRightOne {em : ExtendedMantissa} {v : ℝ} (h : Cons em v) :
    Cons (shiftRightOne em) (v / 2) := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  obtain ⟨m, rb, sb⟩ := em
  simp only at h1 h2 h3 h4
  simp only [Cons, shiftRightOne]
  have hdm : (m : ℝ) = 2 * ((m / 2 : ℕ) : ℝ) + ((m % 2 : ℕ) : ℝ) := by
    have := Nat.div_add_mod m 2; exact_mod_cast this.symm
  rcases Nat.mod_two_eq_zero_or_one m with hb | hb
  · rw [hb] at hdm; simp only [Nat.cast_zero, add_zero] at hdm
    simp only [hb, bne_self_eq_false, Bool.false_eq_true, false_iff, not_le]
    refine ⟨by linarith, by linarith, by linarith, ?_⟩
    rw [Bool.or_eq_true, h3, h4]
    constructor
    · rintro (h | ⟨h, -⟩)
      · constructor <;> intro e <;> linarith
      · constructor
        · intro e; apply h; linarith
        · intro e; linarith
    · rintro ⟨e1, -⟩
      by_cases hv : (m : ℝ) + 1/2 ≤ v
      · exact Or.inl hv
      · right; refine ⟨fun e => e1 (by linarith), fun e => hv (by linarith)⟩
  · rw [hb] at hdm; simp only [Nat.cast_one] at hdm
    simp only [hb]
    refine ⟨by linarith, by linarith, ⟨fun _ => by linarith, fun _ => rfl⟩, ?_⟩
    rw [Bool.or_eq_true, h3, h4]
    constructor
    · rintro (h | ⟨h, -⟩)
      · constructor <;> intro e <;> linarith
      · constructor
        · intro e; linarith
        · intro e; apply h; linarith
    · rintro ⟨-, e2⟩
      by_cases hv : (m : ℝ) + 1/2 ≤ v
      · exact Or.inl hv
      · right; refine ⟨fun e => e2 (by linarith), fun e => hv (by linarith)⟩

theorem cons_shiftRight {em : ExtendedMantissa} {v : ℝ} (h : Cons em v) (n : ℕ) :
    Cons (em >>> n) (v / 2 ^ n) := by
  induction n with
  | zero => simpa [shiftRight_zero] using h
  | succ k ih =>
    rw [shiftRight_succ, pow_succ, ← div_div]
    exact cons_shiftRightOne ih

/-- The accuracy `acc` correctly places `v` relative to `m`, `m + 1/2`, `m + 1`. -/
def AccOK : Accuracy → ℕ → ℝ → Prop
  | .exact, m, v => v = m
  | .inexact .lt, m, v => (m : ℝ) < v ∧ v < m + 1/2
  | .inexact .eq, m, v => v = m + 1/2
  | .inexact .gt, m, v => (m : ℝ) + 1/2 < v ∧ v < m + 1

theorem cons_ofMA {acc : Accuracy} {m : ℕ} {v : ℝ} (h : AccOK acc m v) :
    Cons (ofMantissaAndAccuracy m acc) v := by
  rcases acc with _ | (_ | _ | _) <;> simp only [AccOK] at h <;>
    simp only [Cons, ofMantissaAndAccuracy]
  · subst h; refine ⟨le_rfl, by linarith, by simp, by simp⟩
  · obtain ⟨h1, h2⟩ := h
    refine ⟨h1.le, by linarith, by simp; linarith, ?_⟩
    simp only [true_iff]; constructor <;> intro e <;> linarith
  · subst h; refine ⟨by linarith, by linarith, by simp, by simp⟩
  · obtain ⟨h1, h2⟩ := h
    refine ⟨by linarith, h2, by simp; linarith, ?_⟩
    simp only [true_iff]; constructor <;> intro e <;> linarith

/-- Rounding a described value lands on one of its two neighbors, within half a unit. -/
theorem round_cons {em : ExtendedMantissa} {v : ℝ} (h : Cons em v) :
    (em.roundedMantissa = em.mantissa ∨ em.roundedMantissa = em.mantissa + 1) ∧
      |(em.roundedMantissa : ℝ) - v| ≤ 1/2 := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  obtain ⟨m, rb, sb⟩ := em
  simp only at h1 h2 h3 h4
  cases rb <;> cases sb <;>
    simp only [roundedMantissa, accuracy, Accuracy.roundToNearestEven, Bool.false_eq_true,
      false_iff, true_iff, not_le, not_and_or, not_not] at h3 h4 ⊢
  · -- exact
    rcases h4 with h4 | h4
    · refine ⟨by simp, ?_⟩; rw [h4]; simp
    · linarith
  · refine ⟨by simp, ?_⟩; rw [abs_le]; constructor <;> linarith
  · -- tie
    rcases h4 with h4 | h4
    · linarith
    · rcases Nat.mod_two_eq_zero_or_one m with hb | hb
      · refine ⟨Or.inl (by simp [hb]), ?_⟩
        rw [hb, Nat.add_zero, h4, abs_le]; constructor <;> linarith
      · refine ⟨Or.inr (by simp [hb]), ?_⟩
        rw [hb, h4, abs_le]; push_cast; constructor <;> linarith
  · refine ⟨by simp, ?_⟩
    rw [abs_le]; push_cast; constructor <;> linarith

theorem accOK_bounds {acc : Accuracy} {m : ℕ} {v : ℝ} (h : AccOK acc m v) :
    (m : ℝ) ≤ v ∧ v < m + 1 := by
  rcases acc with _ | (_ | _ | _) <;> simp only [AccOK] at h
  · subst h; constructor <;> linarith
  · constructor <;> linarith [h.1, h.2]
  · subst h; constructor <;> linarith
  · constructor <;> linarith [h.1, h.2]

/-! ## `roundWithAccuracy` with a correct accuracy -/

theorem shiftToTarget_eq (spec : Format) (m : ℕ) (e : ℤ) (acc : Accuracy) :
    shiftToTargetExponent spec m e acc =
      (ofMantissaAndAccuracy m acc >>>
          (max ((m.log2 : ℤ) + 1 + e - spec.mantissaBits) spec.minExponent - e).toNat,
       e + ((max ((m.log2 : ℤ) + 1 + e - spec.mantissaBits) spec.minExponent - e).toNat : ℤ)) := by
  simp only [shiftToTargetExponent, shiftToExponent, Format.targetExponent, totalExponent]

/-- **The structure of `roundWithAccuracy`** on a value `X = v 2^e` that the accuracy correctly
describes: the result is `mkFin s M E` with magnitude `M₀ 2^G`, where `M₀` is a nearest integer to
`X / 2^G` (`|M₀ 2^G - X| ≤ 2^G / 2`), the grid exponent `G` is at least `minExponent`, and above it
`X ≥ 2^k 2^G` and `M₀ ≥ 2^k` (`k` the stored mantissa bits); the final mantissa `M` has at most `P`
bits, `E ∈ {G, G+1}`, and `M ≥ 2^k` when `E > minExponent`. -/
theorem roundWithAccuracy_struct (spec : Format) (s : Sign) (m : ℕ) (e : ℤ) (acc : Accuracy)
    (v : ℝ) (hacc : AccOK acc m v)
    (hL : spec.mantissaBitsWithoutImplicit ≤ m.log2 ∨ e ≤ spec.minExponent) :
    ∃ (M M₀ : ℕ) (E G : ℤ), roundWithAccuracy spec s m e acc = mkFin s M E ∧
      mag M E = (M₀ : ℝ) * 2 ^ G ∧ M < 2 ^ spec.mantissaBits ∧
      (spec.minExponent < E → 2 ^ spec.mantissaBitsWithoutImplicit ≤ M) ∧
      G ≤ E ∧ E ≤ G + 1 ∧ spec.minExponent ≤ G ∧
      |(M₀ : ℝ) * 2 ^ G - v * 2 ^ e| ≤ 2 ^ G / 2 ∧
      (spec.minExponent < G → (2 : ℝ) ^ spec.mantissaBitsWithoutImplicit * 2 ^ G ≤ v * 2 ^ e ∧
        2 ^ spec.mantissaBitsWithoutImplicit ≤ M₀) := by
  have hPk := Format.mantissaBits_eq spec
  have hP := two_pow_mantissaBits spec
  have hk0 := Nat.two_pow_pos spec.mantissaBitsWithoutImplicit
  have hk1 := spec.hm
  obtain ⟨hmv, hvm⟩ := accOK_bounds hacc
  have hv0 : 0 ≤ v := le_trans (Nat.cast_nonneg m) hmv
  rw [roundWithAccuracy_eq_mkFin, shiftToTarget_eq]
  set k := spec.mantissaBitsWithoutImplicit with hk
  set L := m.log2 with hLdef
  set n := (max ((L : ℤ) + 1 + e - spec.mantissaBits) spec.minExponent - e).toNat with hn
  have hc1 := cons_shiftRight (cons_ofMA hacc) n
  simp only
  set em₁ := ofMantissaAndAccuracy m acc >>> n with hem₁
  set q := em₁.mantissa with hq
  set M₀ := em₁.roundedMantissa with hM₀
  obtain ⟨hMq, herr⟩ := round_cons hc1
  obtain ⟨hq1, hq2, -, -⟩ := hc1
  have hN : (0 : ℝ) < 2 ^ n := by positivity
  -- `q 2^n ≤ m`
  have hqm : q * 2 ^ n ≤ m := by
    have h1 : (q : ℝ) * 2 ^ n ≤ v := by rw [le_div_iff₀ hN] at hq1; exact hq1
    have h2 : ((q * 2 ^ n : ℕ) : ℝ) < m + 1 := by push_cast; linarith
    exact_mod_cast Nat.lt_succ_iff.1 (by exact_mod_cast h2)
  -- `q < 2^P`
  have hqP : q < 2 ^ spec.mantissaBits := by
    by_cases hmk : m < 2 ^ k
    · have : q ≤ q * 2 ^ n := Nat.le_mul_of_pos_right _ (Nat.two_pow_pos n)
      omega
    · have hLge : k ≤ L := by
        rw [hLdef]; by_contra hcon
        have := (Nat.log2_lt (by omega)).1 (by omega : m.log2 < k); omega
      have hmL : m < 2 ^ (L + 1) := Nat.lt_log2_self
      have : 2 ^ (L + 1) ≤ 2 ^ spec.mantissaBits * 2 ^ n := by
        rw [← Nat.pow_add]; exact Nat.pow_le_pow_right (by norm_num) (by omega)
      by_contra hcon
      have : 2 ^ spec.mantissaBits * 2 ^ n ≤ q * 2 ^ n := Nat.mul_le_mul_right _ (by omega)
      omega
  have hMP : M₀ ≤ 2 ^ spec.mantissaBits := by omega
  have he1 : spec.minExponent ≤ e + n := by omega
  -- the normal case
  have hnorm : spec.minExponent < e + n → 2 ^ k ≤ q ∧ (2 : ℝ) ^ k * 2 ^ n ≤ v := by
    intro hlt
    have hLge : k ≤ L ∧ n = L - k := by
      rcases hL with hL | hL
      · constructor
        · exact hL
        · omega
      · omega
    have hmL : 2 ^ L ≤ m := Nat.log2_self_le (by
      intro h0; rw [h0] at hLdef; simp at hLdef; omega)
    have hpow : 2 ^ L = 2 ^ k * 2 ^ n := by rw [← Nat.pow_add]; congr 1; omega
    have hvk : (2 : ℝ) ^ k * 2 ^ n ≤ v := by
      have : ((2 ^ k * 2 ^ n : ℕ) : ℝ) ≤ m := by exact_mod_cast hpow ▸ hmL
      push_cast at this; linarith
    have hvk' : (2 : ℝ) ^ k ≤ v / 2 ^ n := by rw [le_div_iff₀ hN]; exact hvk
    refine ⟨?_, hvk⟩
    have : ((2 ^ k : ℕ) : ℝ) < q + 1 := by push_cast; linarith
    exact_mod_cast Nat.lt_succ_iff.1 (by exact_mod_cast this)
  -- the second shift
  rw [shiftToTarget_eq]
  have hom : ofMantissaAndAccuracy M₀ .exact = ⟨M₀, false, false⟩ := rfl
  rw [hom, mantissa_shiftRight]
  -- the final mantissa and exponent, and the value they denote
  have key : ∃ M E, M < 2 ^ spec.mantissaBits ∧ e + n ≤ E ∧
      (spec.minExponent < E → 2 ^ k ≤ M) ∧ (E ≤ e + n + 1) ∧
      mag M E = (M₀ : ℝ) * 2 ^ (e + n) ∧
      M₀ / 2 ^ (max ((M₀.log2 : ℤ) + 1 + (e + n) - spec.mantissaBits) spec.minExponent -
        (e + n)).toNat = M ∧
      e + n + ((max ((M₀.log2 : ℤ) + 1 + (e + n) - spec.mantissaBits) spec.minExponent -
        (e + n)).toNat : ℤ) = E := by
    by_cases hlt : M₀ < 2 ^ spec.mantissaBits
    · have hlog : (M₀.log2 : ℤ) ≤ k := by
        by_cases h0 : M₀ = 0
        · rw [h0]; simp
        · have := (Nat.log2_lt h0).2 (show M₀ < 2 ^ (k + 1) by rw [Nat.pow_succ]; omega); omega
      have hz : (max ((M₀.log2 : ℤ) + 1 + (e + n) - spec.mantissaBits) spec.minExponent -
          (e + n)).toNat = 0 := by omega
      refine ⟨M₀, e + n, hlt, le_rfl, fun h => ?_, by omega, by rw [mag],
        by rw [hz]; simp, by rw [hz]; simp⟩
      have := (hnorm h).1
      rcases hMq with h' | h' <;> omega
    · have hM : M₀ = 2 ^ spec.mantissaBits := by omega
      have hlog : M₀.log2 = spec.mantissaBits := by rw [hM]; exact Nat.log2_two_pow
      have hz : (max ((M₀.log2 : ℤ) + 1 + (e + n) - spec.mantissaBits) spec.minExponent -
          (e + n)).toNat = 1 := by
        rw [hlog]; omega
      refine ⟨2 ^ k, e + n + 1, by omega, by omega, fun _ => le_rfl, le_rfl, ?_,
        by rw [hz, hM, hP]; simp, by rw [hz]; simp⟩
      rw [mag, hM, hP, zpow_add₀ two_ne_zero]; push_cast; ring
  obtain ⟨M, E, hMP', hE1, hEn, hE2, hmag, hMdef, hEdef⟩ := key
  rw [hMdef, hEdef]
  -- the error of the value
  have hval : |(M₀ : ℝ) * 2 ^ (e + n) - v * 2 ^ e| ≤ 2 ^ (e + n) / 2 := by
    have h2 : (2 : ℝ) ^ (e + n) = 2 ^ n * 2 ^ e := by
      rw [zpow_add₀ two_ne_zero, zpow_natCast]; ring
    have : (M₀ : ℝ) * 2 ^ (e + n) - v * 2 ^ e = ((M₀ : ℝ) - v / 2 ^ n) * 2 ^ (e + n) := by
      rw [h2]; field_simp
    rw [this, abs_mul, abs_of_pos (two_zpow_pos _)]
    nlinarith [two_zpow_pos (e + n)]
  refine ⟨M, M₀, E, e + n, rfl, hmag, hMP', hEn, hE1, hE2, he1, hval, fun h => ?_⟩
  obtain ⟨hq', hv⟩ := hnorm h
  refine ⟨?_, by rcases hMq with h' | h' <;> omega⟩
  have h2 : (2 : ℝ) ^ (e + n) = 2 ^ n * 2 ^ e := by
    rw [zpow_add₀ two_ne_zero, zpow_natCast]; ring
  rw [h2, ← mul_assoc]
  exact mul_le_mul_of_nonneg_right hv (two_zpow_pos e).le

/-- **Correct rounding with an accuracy.** If `acc` correctly places `v` relative to `m`, and either
`m` has at least `k + 1` bits (`k` the stored mantissa bits) or `e` is at the bottom of the exponent
range, `roundWithAccuracy spec` gives a canonical finite float within
`2^-P (v 2^e) + 2^(minExponent - 1)` of `± v 2^e`. -/
theorem roundWithAccuracy_real (spec : Format) (hw : 2 ≤ spec.exponentBits) (s : Sign) (m : ℕ)
    (e : ℤ) (acc : Accuracy) (v : ℝ) (hacc : AccOK acc m v)
    (hL : spec.mantissaBitsWithoutImplicit ≤ m.log2 ∨ e ≤ spec.minExponent)
    (hhi : v * 2 ^ e ≤ maxFiniteIn spec) :
    CanonicalIn spec (roundWithAccuracy spec s m e acc) ∧
    (roundWithAccuracy spec s m e acc).isFinite = true ∧
    |(roundWithAccuracy spec s m e acc).toReal - s.toReal * (v * 2 ^ e)| ≤
      2 ^ (-(spec.mantissaBits : ℤ)) * (v * 2 ^ e) + 2 ^ (spec.minExponent - 1) := by
  have hbias := Format.one_le_exponentBias spec hw
  have hmin := Format.minExponent_eq spec
  obtain ⟨M, M₀, E, G, hres, hmag, hMP', hEn, hE1, hE2, he1, hval, hnorm⟩ :=
    roundWithAccuracy_struct spec s m e acc v hacc hL
  have hv0 : 0 ≤ v := le_trans (Nat.cast_nonneg m) (accOK_bounds hacc).1
  rw [hres]
  have h53 := two_zpow_neg_mantissaBits spec
  have hrel : spec.minExponent < G →
      2 ^ G / 2 ≤ (2 : ℝ) ^ (-(spec.mantissaBits : ℤ)) * (v * 2 ^ e) := by
    intro h
    have hv := (hnorm h).1
    have hu := two_zpow_pos (-(spec.mantissaBits : ℤ))
    calc (2 : ℝ) ^ G / 2 = (2 ^ (-(spec.mantissaBits : ℤ)) * 2 ^ spec.mantissaBitsWithoutImplicit) *
          2 ^ G := by rw [h53]; ring
      _ = 2 ^ (-(spec.mantissaBits : ℤ)) * (2 ^ spec.mantissaBitsWithoutImplicit * 2 ^ G) := by ring
      _ ≤ 2 ^ (-(spec.mantissaBits : ℤ)) * (v * 2 ^ e) := by gcongr
  have hbound : 2 ^ G / 2 ≤
      (2 : ℝ) ^ (-(spec.mantissaBits : ℤ)) * (v * 2 ^ e) + 2 ^ (spec.minExponent - 1) := by
    have hnn : 0 ≤ (2 : ℝ) ^ (-(spec.mantissaBits : ℤ)) * (v * 2 ^ e) := by
      have := two_zpow_pos e; positivity
    rcases eq_or_lt_of_le he1 with h | h
    · rw [← h, zpow_sub₀ two_ne_zero, zpow_one]; linarith
    · linarith [hrel h, two_zpow_pos (spec.minExponent - 1)]
  refine ⟨?_, isFinite_mkFin _ _ _, ?_⟩
  · -- canonical
    unfold mkFin
    split_ifs with h0
    · trivial
    · refine ⟨by omega, ?_, hMP', hEn⟩
      by_contra hcon
      have hcon := not_le.1 hcon
      simp only [Format.maxExponent] at hcon
      have hEgt : spec.minExponent < E := by omega
      have hMk := hEn hEgt
      have hupper : mag M E ≤ v * 2 ^ e * (1 + 2 ^ (-(spec.mantissaBits : ℤ))) := by
        rcases eq_or_lt_of_le he1 with h | h
        · exfalso; omega
        · have hA : (M₀ : ℝ) * 2 ^ G ≤ v * 2 ^ e + 2 ^ G / 2 := by
            have := (abs_le.1 hval).2; linarith
          calc mag M E = (M₀ : ℝ) * 2 ^ G := hmag
            _ ≤ v * 2 ^ e + 2 ^ G / 2 := hA
            _ ≤ v * 2 ^ e + 2 ^ (-(spec.mantissaBits : ℤ)) * (v * 2 ^ e) := by linarith [hrel h]
            _ = v * 2 ^ e * (1 + 2 ^ (-(spec.mantissaBits : ℤ))) := by ring
      have h2 : v * 2 ^ e * (1 + 2 ^ (-(spec.mantissaBits : ℤ))) ≤
          maxFiniteIn spec * (1 + 2 ^ (-(spec.mantissaBits : ℤ))) :=
        mul_le_mul_of_nonneg_right hhi (by positivity)
      have hup : mag M E < (2 : ℝ) ^ (spec.maxExponent + spec.mantissaBits) := by
        linarith [maxFiniteIn_mul_lt spec]
      have hdown : (2 : ℝ) ^ ((spec.mantissaBitsWithoutImplicit : ℤ) + E) ≤ mag M E := by
        rw [zpow_add₀ two_ne_zero, mag, zpow_natCast]
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast hMk) (two_zpow_pos E).le
      have := (zpow_lt_zpow_iff_right₀ one_lt_two).1 (lt_of_le_of_lt hdown hup)
      have hPk := Format.mantissaBits_eq spec
      simp only [Format.maxExponent] at this
      omega
  · -- error
    rw [toReal_mkFin, hmag, ← mul_sub, abs_mul, Sign.abs_toReal, one_mul]
    exact hval.trans hbound

/-! ## Division -/

theorem accOK_frac (N d : ℕ) (hd : 0 < d) :
    AccOK (accuracyOfFraction (N % d) d) (N / d) ((N : ℝ) / d) := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hNd : (N : ℝ) / d = ((N / d : ℕ) : ℝ) + ((N % d : ℕ) : ℝ) / d := by
    have := Nat.div_add_mod N d
    have h' : ((d * (N / d) + N % d : ℕ) : ℝ) = (N : ℝ) := by exact_mod_cast this
    push_cast at h'
    rw [div_eq_iff hdR.ne', add_mul, div_mul_cancel₀ _ hdR.ne']; linarith
  have hlt : ((N % d : ℕ) : ℝ) < d := by exact_mod_cast Nat.mod_lt N hd
  have hrem0 : (0 : ℝ) ≤ ((N % d : ℕ) : ℝ) := Nat.cast_nonneg _
  have hf1 : ((N % d : ℕ) : ℝ) / d < 1 := (div_lt_one hdR).2 hlt
  unfold accuracyOfFraction
  split_ifs with h0
  · simp only [AccOK]; rw [hNd, h0]; simp
  · have hpos : (0 : ℝ) < ((N % d : ℕ) : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero h0
    have hf0 : 0 < ((N % d : ℕ) : ℝ) / d := div_pos hpos hdR
    rcases hc : compare (2 * (N % d)) d with _ | _ | _ <;> simp only [AccOK]
    · have h2 : 2 * (N % d) < d := Nat.compare_eq_lt.1 hc
      have h2' : (2 : ℝ) * ((N % d : ℕ) : ℝ) < d := by exact_mod_cast h2
      have : ((N % d : ℕ) : ℝ) / d < 1/2 := by rw [div_lt_iff₀ hdR]; linarith
      rw [hNd]; constructor <;> linarith
    · have h2 : 2 * (N % d) = d := Nat.compare_eq_eq.1 hc
      have h2' : (2 : ℝ) * ((N % d : ℕ) : ℝ) = d := by exact_mod_cast h2
      have : ((N % d : ℕ) : ℝ) / d = 1/2 := by rw [div_eq_iff hdR.ne']; linarith
      rw [hNd, this]
    · have h2 : d < 2 * (N % d) := Nat.compare_eq_gt.1 hc
      have h2' : (d : ℝ) < 2 * ((N % d : ℕ) : ℝ) := by exact_mod_cast h2
      have : 1/2 < ((N % d : ℕ) : ℝ) / d := by rw [lt_div_iff₀ hdR]; linarith
      rw [hNd]; constructor <;> linarith

/-- What `divCore` computes: the truncated quotient with a correct accuracy, enough bits, and
the exact quotient as `v · 2^T`. -/
theorem divCore_spec (spec : Format) (m₁ m₂ : ℕ) (e₁ e₂ : ℤ) (h1 : 0 < m₁) (h2 : 0 < m₂) :
    let r := divCore spec m₁ e₁ m₂ e₂
    let v := (((m₁ * 2 ^ (e₁ - e₂ - r.2.1).toNat : ℕ) : ℝ) / m₂)
    AccOK r.2.2 r.1 v ∧ v * 2 ^ r.2.1 = mag m₁ e₁ / mag m₂ e₂ ∧
      (spec.mantissaBitsWithoutImplicit ≤ r.1.log2 ∨ r.2.1 ≤ spec.minExponent) := by
  intro r v
  have hPk := Format.mantissaBits_eq spec
  set T := r.2.1 with hT
  have hTdef : T = min (e₁ - e₂) (max (((m₁.log2 : ℤ) + 1 + e₁) - ((m₂.log2 : ℤ) + 1 + e₂) -
      spec.mantissaBits) spec.minExponent) := by
    simp only [hT, r, divCore, Format.targetExponent, totalExponent]
  set k := (e₁ - e₂ - T).toNat with hk
  have hr1 : r.1 = (m₁ * 2 ^ k) / m₂ := by
    simp only [r, divCore, Nat.shiftLeft_eq]; rfl
  have hr22 : r.2.2 = accuracyOfFraction ((m₁ * 2 ^ k) % m₂) m₂ := by
    simp only [r, divCore, Nat.shiftLeft_eq]; rfl
  refine ⟨?_, ?_, ?_⟩
  · rw [hr1, hr22]; exact accOK_frac _ _ h2
  · have hkT : (k : ℤ) + T = e₁ - e₂ := by omega
    simp only [v, mag]
    have hm2 : (0 : ℝ) < m₂ := by exact_mod_cast h2
    have h2e : (0 : ℝ) < 2 ^ e₂ := two_zpow_pos _
    rw [div_mul_eq_mul_div, div_eq_div_iff hm2.ne' (by positivity)]
    push_cast
    have : (2 : ℝ) ^ (k : ℕ) * 2 ^ T * 2 ^ e₂ = 2 ^ e₁ := by
      rw [← zpow_natCast, ← zpow_add₀ two_ne_zero, ← zpow_add₀ two_ne_zero]; congr 1; omega
    calc (m₁ : ℝ) * 2 ^ k * 2 ^ T * ((m₂ : ℝ) * 2 ^ e₂)
        = (m₁ : ℝ) * m₂ * (2 ^ (k : ℕ) * 2 ^ T * 2 ^ e₂) := by ring
      _ = _ := by rw [this]; ring
  · by_cases hlo : T ≤ spec.minExponent
    · exact Or.inr hlo
    · left
      rw [hr1]
      set L₁ := m₁.log2; set L₂ := m₂.log2
      have hk' : (L₂ : ℤ) + spec.mantissaBits ≤ L₁ + k := by omega
      have hm1 : 2 ^ L₁ ≤ m₁ := Nat.log2_self_le (by omega)
      have hm2 : m₂ < 2 ^ (L₂ + 1) := Nat.lt_log2_self
      have hbig : 2 ^ spec.mantissaBitsWithoutImplicit * m₂ ≤ m₁ * 2 ^ k := by
        have h3 : 2 ^ spec.mantissaBitsWithoutImplicit * m₂ <
            2 ^ spec.mantissaBitsWithoutImplicit * 2 ^ (L₂ + 1) :=
          Nat.mul_lt_mul_of_pos_left hm2 (by positivity)
        have h4 : 2 ^ spec.mantissaBitsWithoutImplicit * 2 ^ (L₂ + 1) ≤ 2 ^ L₁ * 2 ^ k := by
          rw [← Nat.pow_add, ← Nat.pow_add]; exact Nat.pow_le_pow_right (by norm_num) (by omega)
        have h5 : 2 ^ L₁ * 2 ^ k ≤ m₁ * 2 ^ k := Nat.mul_le_mul_right _ hm1
        omega
      have hq : 2 ^ spec.mantissaBitsWithoutImplicit ≤ m₁ * 2 ^ k / m₂ :=
        (Nat.le_div_iff_mul_le h2).2 (by linarith)
      exact (Nat.le_log2 (Nat.pos_iff_ne_zero.1 (lt_of_lt_of_le (Nat.two_pow_pos _) hq))).2 hq

theorem sign_div_toReal (s₁ s₂ : Sign) : (s₁ / s₂).toReal = s₁.toReal / s₂.toReal := by
  cases s₁ <;> cases s₂ <;> norm_num [Sign.toReal] <;> rfl

/-- An unpacked result within relative error `2^-P` plus absolute error `2^(minExponent - 1)` of
`x`. -/
def NearRoundIn (spec : Format) (r : UnpackedFloat) (x : ℝ) : Prop :=
  CanonicalIn spec r ∧ r.isFinite = true ∧
    |r.toReal - x| ≤ 2 ^ (-(spec.mantissaBits : ℤ)) * |x| + 2 ^ (spec.minExponent - 1)

theorem nearRoundIn_of_exact {spec : Format} {r : UnpackedFloat} {x : ℝ} (hc : CanonicalIn spec r)
    (hf : r.isFinite = true) (hx : r.toReal = x) : NearRoundIn spec r x := by
  refine ⟨hc, hf, ?_⟩
  rw [hx, sub_self, abs_zero]; positivity

/-- **Division** of canonical finite unpacked floats by a nonzero one rounds to nearest: relative
error `2^-P` plus absolute error `2^(minExponent - 1)`. -/
theorem nearRoundIn_div {spec : Format} (hw : 2 ≤ spec.exponentBits) {u v : UnpackedFloat}
    (cu : CanonicalIn spec u) (cv : CanonicalIn spec v)
    (fu : u.isFinite = true) (fv : v.isFinite = true) (hv0 : v.toReal ≠ 0)
    (hq : |u.toReal / v.toReal| ≤ maxFiniteIn spec) :
    NearRoundIn spec (div spec u v) (u.toReal / v.toReal) := by
  cases u with
  | infinity _ => simp [isFinite] at fu
  | notANumber => simp [isFinite] at fu
  | zero s₁ =>
    cases v with
    | infinity _ => simp [isFinite] at fv
    | notANumber => simp [isFinite] at fv
    | zero s₂ => exact absurd rfl hv0
    | finite s₂ m₂ e₂ hm₂ => exact nearRoundIn_of_exact trivial rfl (by simp [div, toReal])
  | finite s₁ m₁ e₁ hm₁ =>
    cases v with
    | infinity _ => simp [isFinite] at fv
    | notANumber => simp [isFinite] at fv
    | zero s₂ => exact absurd rfl hv0
    | finite s₂ m₂ e₂ hm₂ =>
      simp only [div]
      obtain ⟨hacc, hval, hL⟩ := divCore_spec spec m₁ m₂ e₁ e₂ hm₁ hm₂
      set r := divCore spec m₁ e₁ m₂ e₂
      set w := (((m₁ * 2 ^ (e₁ - e₂ - r.2.1).toNat : ℕ) : ℝ) / m₂)
      have hquot : (UnpackedFloat.finite s₁ m₁ e₁ hm₁).toReal /
          (UnpackedFloat.finite s₂ m₂ e₂ hm₂).toReal = (s₁ / s₂).toReal * (w * 2 ^ r.2.1) := by
        rw [toReal_finite, toReal_finite, hval, sign_div_toReal]
        have := Sign.abs_toReal s₂
        have hs2 : s₂.toReal ≠ 0 := by intro h; rw [h] at this; simp at this
        have := mag_pos hm₂ e₂
        field_simp
      have habs : |(UnpackedFloat.finite s₁ m₁ e₁ hm₁).toReal /
          (UnpackedFloat.finite s₂ m₂ e₂ hm₂).toReal| = w * 2 ^ r.2.1 := by
        rw [hquot, abs_mul, Sign.abs_toReal, one_mul, abs_of_nonneg]
        rw [hval]; exact div_nonneg (mag_pos hm₁ _).le (mag_pos hm₂ _).le
      obtain ⟨hc, hf, herr⟩ := roundWithAccuracy_real spec hw (s₁ / s₂) r.1 r.2.1 r.2.2 w hacc hL
        (habs ▸ hq)
      refine ⟨hc, hf, ?_⟩
      rw [habs, hquot]; exact herr

/-! ## Square root -/

theorem accOK_sqrt (M : ℕ) :
    AccOK (if M - M.sqrt * M.sqrt = 0 then .exact
      else .inexact (if M - M.sqrt * M.sqrt ≤ M.sqrt then .lt else .gt)) M.sqrt (Real.sqrt M) := by
  set r := M.sqrt with hr
  have h1 : r * r ≤ M := Nat.sqrt_le M
  have h2 : M < (r + 1) * (r + 1) := Nat.lt_succ_sqrt M
  have hr0 : (0 : ℝ) ≤ r := Nat.cast_nonneg r
  have hM0 : (0 : ℝ) ≤ M := Nat.cast_nonneg M
  have hup : Real.sqrt M < r + 1 := by
    rw [Real.sqrt_lt' (by positivity)]
    have : ((M : ℕ) : ℝ) < (((r + 1) * (r + 1) : ℕ) : ℝ) := by exact_mod_cast h2
    push_cast at this; nlinarith
  have hlo : (r : ℝ) ≤ Real.sqrt M := by
    rw [Real.le_sqrt hr0 hM0]
    have : (((r * r) : ℕ) : ℝ) ≤ (M : ℝ) := by exact_mod_cast h1
    push_cast at this; nlinarith
  split_ifs with h0 h3
  · simp only [AccOK]
    have : M = r * r := by omega
    rw [this]; push_cast; exact Real.sqrt_mul_self hr0
  · simp only [AccOK]
    have hlt : r * r < M := by omega
    have hle : M ≤ r * r + r := by omega
    constructor
    · rw [Real.lt_sqrt hr0]
      have : (((r * r) : ℕ) : ℝ) < (M : ℝ) := by exact_mod_cast hlt
      push_cast at this; nlinarith
    · rw [Real.sqrt_lt' (by positivity)]
      have : (M : ℝ) ≤ (((r * r + r) : ℕ) : ℝ) := by exact_mod_cast hle
      push_cast at this; nlinarith
  · simp only [AccOK]
    have hge : r * r + r + 1 ≤ M := by omega
    refine ⟨?_, hup⟩
    rw [Real.lt_sqrt (by positivity)]
    have : (((r * r + r + 1) : ℕ) : ℝ) ≤ (M : ℝ) := by exact_mod_cast hge
    push_cast at this; nlinarith

/-- What `sqrtCore` computes. -/
theorem sqrtCore_spec (spec : Format) (m : ℕ) (e : ℤ) (hm : 0 < m) :
    let r := sqrtCore spec m e
    let M := m * 2 ^ (e - 2 * r.2.1).toNat
    AccOK r.2.2 r.1 (Real.sqrt M) ∧ Real.sqrt M * 2 ^ r.2.1 = Real.sqrt (mag m e) ∧
      (spec.mantissaBitsWithoutImplicit ≤ r.1.log2 ∨ r.2.1 ≤ spec.minExponent) := by
  intro r M
  have hPk := Format.mantissaBits_eq spec
  set T := r.2.1 with hT
  have hTdef : T = min (e.ediv 2) (max ((((m.log2 : ℤ) + 1 + e) + 1).ediv 2 - spec.mantissaBits)
      spec.minExponent) := by
    simp only [hT, r, sqrtCore, Format.targetExponent, totalExponent]
  have hr1 : r.1 = M.sqrt := by simp only [r, M, sqrtCore, Nat.shiftLeft_eq]
  have hr22 : r.2.2 = (if M - M.sqrt * M.sqrt = 0 then .exact
      else .inexact (if M - M.sqrt * M.sqrt ≤ M.sqrt then .lt else .gt)) := by
    simp only [r, M, sqrtCore, Nat.shiftLeft_eq]
  have hTdef' : T = min (e / 2) (max ((((m.log2 : ℤ) + 1 + e) + 1) / 2 - spec.mantissaBits)
      spec.minExponent) := hTdef
  have he2 : 2 * T ≤ e := by rw [hTdef']; omega
  refine ⟨?_, ?_, ?_⟩
  · rw [hr1, hr22]; exact accOK_sqrt M
  · have hk : ((e - 2 * T).toNat : ℤ) = e - 2 * T := by omega
    have hmag : mag m e = (M : ℝ) * (2 ^ T) ^ 2 := by
      simp only [M, mag]; push_cast
      rw [← zpow_natCast, hk, ← zpow_natCast, ← zpow_mul, mul_assoc, ← zpow_add₀ two_ne_zero]
      congr 2; push_cast; ring
    rw [hmag, Real.sqrt_mul (Nat.cast_nonneg _), Real.sqrt_sq (two_zpow_pos T).le]
  · by_cases hlo : T ≤ spec.minExponent
    · exact Or.inr hlo
    · left
      rw [hr1]
      have hsh : 2 * spec.mantissaBitsWithoutImplicit ≤ m.log2 + (e - 2 * T).toNat := by
        rw [hTdef'] at hlo ⊢; omega
      have hmL : 2 ^ m.log2 ≤ m := Nat.log2_self_le (by omega)
      have hM : 2 ^ spec.mantissaBitsWithoutImplicit * 2 ^ spec.mantissaBitsWithoutImplicit ≤ M := by
        have : 2 ^ spec.mantissaBitsWithoutImplicit * 2 ^ spec.mantissaBitsWithoutImplicit ≤
            2 ^ m.log2 * 2 ^ (e - 2 * T).toNat := by
          rw [← Nat.pow_add, ← Nat.pow_add]; exact Nat.pow_le_pow_right (by norm_num) (by omega)
        exact this.trans (Nat.mul_le_mul_right _ hmL)
      have hroot : 2 ^ spec.mantissaBitsWithoutImplicit ≤ M.sqrt := Nat.le_sqrt.2 hM
      exact (Nat.le_log2 (Nat.pos_iff_ne_zero.1 (lt_of_lt_of_le (Nat.two_pow_pos _) hroot))).2 hroot

/-- **Square root** of a canonical finite non-negative unpacked float rounds to nearest: relative
error `2^-P` plus absolute error `2^(minExponent - 1)`. -/
theorem nearRoundIn_sqrt {spec : Format} (hw : 2 ≤ spec.exponentBits) {u : UnpackedFloat}
    (cu : CanonicalIn spec u) (fu : u.isFinite = true) (h0 : 0 ≤ u.toReal)
    (h1 : u.toReal ≤ maxFiniteIn spec) (h1' : 1 ≤ maxFiniteIn spec) :
    NearRoundIn spec (sqrt spec u) (Real.sqrt u.toReal) := by
  cases u with
  | infinity _ => simp [isFinite] at fu
  | notANumber => simp [isFinite] at fu
  | zero s => exact nearRoundIn_of_exact trivial rfl (by simp [UnpackedFloat.sqrt, toReal])
  | finite s m e hm =>
    cases s with
    | negative =>
      exfalso
      have := mag_pos hm e
      rw [toReal_finite] at h0; simp [Sign.toReal] at h0; linarith
    | positive =>
      have hav' : (UnpackedFloat.finite .positive m e hm).toReal = mag m e := by
        rw [toReal_finite]; simp [Sign.toReal]
      simp only [UnpackedFloat.sqrt]
      obtain ⟨hacc, hval, hL⟩ := sqrtCore_spec spec m e hm
      set r := sqrtCore spec m e
      have hhi : Real.sqrt (m * 2 ^ (e - 2 * r.2.1).toNat : ℕ) * 2 ^ r.2.1 ≤ maxFiniteIn spec := by
        rw [hval, ← hav']
        rcases le_total (UnpackedFloat.finite .positive m e hm).toReal 1 with h | h
        · have := Real.sqrt_le_one.mpr h
          linarith
        · have : Real.sqrt (UnpackedFloat.finite .positive m e hm).toReal ≤
              (UnpackedFloat.finite .positive m e hm).toReal := by
            rw [Real.sqrt_le_left (by linarith)]; nlinarith
          linarith
      obtain ⟨hc, hf, herr⟩ := roundWithAccuracy_real spec hw .positive r.1 r.2.1 r.2.2 _ hacc hL hhi
      refine ⟨hc, hf, ?_⟩
      rw [hav', ← hval, abs_of_nonneg (mul_nonneg (Real.sqrt_nonneg _) (two_zpow_pos _).le)]
      simp only [Sign.toReal, one_mul] at herr
      exact herr

end Float.Model.UnpackedFloat

namespace Float

open Float.Model.UnpackedFloat

theorem nearRoundIn_transfer {r : UnpackedFloat} {x : ℝ} (h : NearRoundIn Format.binary64 r x) :
    (Float.ofModel (Float.Model.pack r)).IsFinite ∧
      |(Float.ofModel (Float.Model.pack r)).toReal - x| ≤
        2 ^ (-53 : ℤ) * |x| + 2 ^ (-1075 : ℤ) := by
  obtain ⟨hc, hf, hx⟩ := h
  have hu : (Float.ofModel (Float.Model.pack r)).toModel.unpack = r :=
    Float.Model.unpack_pack_of_canonical ((canonical_iff _).2 hc)
  exact ⟨by rw [isFinite_iff, hu]; exact hf, by rw [toReal, hu]; exact hx⟩

theorem one_le_maxFinite : (1 : ℝ) ≤ maxFinite := by
  unfold maxFinite
  have h : (1 : ℝ) ≤ 2 ^ (971 : ℤ) := one_le_zpow₀ one_le_two (by norm_num)
  calc (1 : ℝ) ≤ (2 ^ 53 - 1) * 1 := by norm_num
    _ ≤ (2 ^ 53 - 1) * 2 ^ (971 : ℤ) := mul_le_mul_of_nonneg_left h (by norm_num)

/-- **Division** of finite floats by a nonzero finite float rounds to nearest: relative error
`2^-53` plus absolute error `2^-1075`, on every quotient up to `maxFinite`. -/
theorem div_err_all {a b : Float} (ha : a.IsFinite) (hb : b.IsFinite) (hb0 : b.toReal ≠ 0)
    (hq : |a.toReal / b.toReal| ≤ maxFinite) :
    (a / b).IsFinite ∧ |(a / b).toReal - a.toReal / b.toReal| ≤
      2 ^ (-53 : ℤ) * |a.toReal / b.toReal| + 2 ^ (-1075 : ℤ) :=
  nearRoundIn_transfer
    (nearRoundIn_div (by decide) a.canonicalIn_unpack b.canonicalIn_unpack ha hb hb0 hq)

/-- **Square root** of a finite non-negative float rounds to nearest: relative error `2^-53` plus
absolute error `2^-1075`. -/
theorem sqrt_err_all {a : Float} (ha : a.IsFinite) (h0 : 0 ≤ a.toReal) (h1 : a.toReal ≤ maxFinite) :
    (Float.sqrt a).IsFinite ∧ |(Float.sqrt a).toReal - Real.sqrt a.toReal| ≤
      2 ^ (-53 : ℤ) * Real.sqrt a.toReal + 2 ^ (-1075 : ℤ) := by
  have h := nearRoundIn_transfer
    (nearRoundIn_sqrt (by decide) a.canonicalIn_unpack ha h0 h1 one_le_maxFinite)
  rwa [abs_of_nonneg (Real.sqrt_nonneg _)] at h

end Float
