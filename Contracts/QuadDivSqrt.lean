import FloatModel.Small
import Contracts.QuadNear
import Contracts.QuadFloat

/-!
# Rounding bounds for `Float` division and square root

`FloatModel` bounds the rounding of `+`, `-`, `*`, whose exact results reach `roundWithAccuracy`
with accuracy `exact`. Division and square root reach it with the accuracy that `divCore` and
`sqrtCore` compute from the remainder of an integer quotient or integer square root. This file
proves the general statement: whenever the accuracy correctly describes the real value `v` that
the mantissa truncates (`AccOK`), `roundWithAccuracy` rounds `v · 2^e` to nearest within
`2⁻⁵³ |x| + 2⁻¹⁰⁷⁵` (`roundWithAccuracy_real`). The key invariant is that every one-bit shift of
an extended mantissa keeps its round and sticky bits a correct description of the shifted value
(`cons_shiftRightOne`). The division and square-root cores are then shown to produce correct
accuracies and enough quotient bits, which discharges `QuadNear.DivSqrtSpec` (`divSqrtSpec`).
-/

open Float.Model UnpackedFloat ExtendedMantissa

namespace Contracts.QuadDivSqrt

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

theorem shiftToTarget_eq (m : ℕ) (e : ℤ) (acc : Accuracy) :
    shiftToTargetExponent Format.binary64 m e acc =
      (ofMantissaAndAccuracy m acc >>> (max ((m.log2 : ℤ) + 1 + e - 53) (-1074) - e).toNat,
       e + ((max ((m.log2 : ℤ) + 1 + e - 53) (-1074) - e).toNat : ℤ)) := by
  have : Format.binary64.targetExponent (totalExponent m e) - e
      = max ((m.log2 : Int) + 1 + e - 53) (-1074) - e := by
    simp only [Format.targetExponent, totalExponent, Format.mantissaBits, Format.minExponent]
    norm_num
  simp only [shiftToTargetExponent, shiftToExponent, this]

theorem two_zpow_pos' (k : ℤ) : (0 : ℝ) < (2 : ℝ) ^ k := zpow_pos two_pos k

/-- **Correct rounding with an accuracy.** If `acc` correctly places `v` relative to `m`, and either
`m` has at least 53 bits or `e` is at the bottom of the exponent range, `roundWithAccuracy` gives a
canonical finite float within `2⁻⁵³ (v 2^e) + 2⁻¹⁰⁷⁵` of `± v 2^e`. -/
theorem roundWithAccuracy_real (s : Sign) (m : ℕ) (e : ℤ) (acc : Accuracy) (v : ℝ)
    (hacc : AccOK acc m v) (hL : 52 ≤ m.log2 ∨ e ≤ -1074) (hhi : v * 2 ^ e ≤ maxFinite) :
    (roundWithAccuracy Format.binary64 s m e acc).Canonical ∧
    (roundWithAccuracy Format.binary64 s m e acc).isFinite = true ∧
    |(roundWithAccuracy Format.binary64 s m e acc).toReal - s.toReal * (v * 2 ^ e)| ≤
      2 ^ (-53 : ℤ) * (v * 2 ^ e) + 2 ^ (-1075 : ℤ) := by
  obtain ⟨hmv, hvm⟩ := accOK_bounds hacc
  have hv0 : 0 ≤ v := le_trans (Nat.cast_nonneg m) hmv
  rw [roundWithAccuracy_eq_mkFin, shiftToTarget_eq]
  set L := m.log2 with hLdef
  set n := (max ((L : ℤ) + 1 + e - 53) (-1074) - e).toNat with hn
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
  -- `q < 2^53`
  have hq53 : q < 2 ^ 53 := by
    by_cases hm52 : m < 2 ^ 52
    · have : q ≤ q * 2 ^ n := Nat.le_mul_of_pos_right _ (Nat.two_pow_pos n)
      omega
    · have hLge : 52 ≤ L := by
        rw [hLdef]; by_contra hcon
        have := (Nat.log2_lt (by omega)).1 (by omega : m.log2 < 52); omega
      have hnL : L - 52 ≤ n := by omega
      have hmL : m < 2 ^ (L + 1) := Nat.lt_log2_self
      have : 2 ^ (L + 1) ≤ 2 ^ 53 * 2 ^ n := by
        rw [← Nat.pow_add]; exact Nat.pow_le_pow_right (by norm_num) (by omega)
      by_contra hcon
      have : 2 ^ 53 * 2 ^ n ≤ q * 2 ^ n := Nat.mul_le_mul_right _ (by omega)
      omega
  have hM53 : M₀ ≤ 2 ^ 53 := by omega
  have he1 : -1074 ≤ e + n := by omega
  -- the normal case
  have hnorm : -1074 < e + n → 2 ^ 52 ≤ q ∧ (2 : ℝ) ^ 52 ≤ v / 2 ^ n := by
    intro hlt
    have hLge : 52 ≤ L ∧ n = L - 52 := by
      rcases hL with hL | hL
      · constructor
        · exact hL
        · omega
      · omega
    have hmL : 2 ^ L ≤ m := Nat.log2_self_le (by
      intro h0; rw [h0] at hLdef; simp at hLdef; omega)
    have hpow : 2 ^ L = 2 ^ 52 * 2 ^ n := by rw [← Nat.pow_add]; congr 1; omega
    have hv52 : (2 : ℝ) ^ 52 * 2 ^ n ≤ v := by
      have : ((2 ^ 52 * 2 ^ n : ℕ) : ℝ) ≤ m := by exact_mod_cast hpow ▸ hmL
      push_cast at this; linarith
    have hv52' : (2 : ℝ) ^ 52 ≤ v / 2 ^ n := by rw [le_div_iff₀ hN]; exact hv52
    refine ⟨?_, hv52'⟩
    have : ((2 ^ 52 : ℕ) : ℝ) < q + 1 := by push_cast; linarith
    exact_mod_cast Nat.lt_succ_iff.1 (by exact_mod_cast this)
  -- the second shift
  rw [shiftToTarget_eq]
  have hom : ofMantissaAndAccuracy M₀ .exact = ⟨M₀, false, false⟩ := rfl
  rw [hom, mantissa_shiftRight]
  -- the final mantissa and exponent, and the value they denote
  have key : ∃ M E, M < 2 ^ 53 ∧ e + n ≤ E ∧ (-1074 < E → 2 ^ 52 ≤ M) ∧ (E ≤ e + n + 1) ∧
      (E = e + n + 1 → -1074 < E ∧ q = 2 ^ 53 - 1) ∧
      mag M E = (M₀ : ℝ) * 2 ^ (e + n) ∧
      M₀ / 2 ^ (max ((M₀.log2 : ℤ) + 1 + (e + n) - 53) (-1074) - (e + n)).toNat = M ∧
      e + n + ((max ((M₀.log2 : ℤ) + 1 + (e + n) - 53) (-1074) - (e + n)).toNat : ℤ) = E := by
    by_cases hlt : M₀ < 2 ^ 53
    · have hlog : (M₀.log2 : ℤ) ≤ 52 := by
        by_cases h0 : M₀ = 0
        · rw [h0]; simp
        · have := (Nat.log2_lt h0).2 hlt; omega
      have hz : (max ((M₀.log2 : ℤ) + 1 + (e + n) - 53) (-1074) - (e + n)).toNat = 0 := by omega
      refine ⟨M₀, e + n, hlt, le_rfl, fun h => ?_, by omega, fun h => by omega, by rw [mag],
        by rw [hz]; simp, by rw [hz]; simp⟩
      have := (hnorm h).1
      rcases hMq with h' | h' <;> omega
    · have hM : M₀ = 2 ^ 53 := by omega
      have hq' : q = 2 ^ 53 - 1 := by rcases hMq with h' | h' <;> omega
      have hlog : M₀.log2 = 53 := by rw [hM]; decide
      have hz : (max ((M₀.log2 : ℤ) + 1 + (e + n) - 53) (-1074) - (e + n)).toNat = 1 := by
        rw [hlog]; omega
      refine ⟨2 ^ 52, e + n + 1, by norm_num, by omega, fun _ => le_rfl, le_rfl,
        fun _ => ⟨by omega, hq'⟩, ?_, by rw [hz, hM]; norm_num, by rw [hz]; simp⟩
      rw [mag, hM, zpow_add₀ two_ne_zero]; push_cast; ring
  obtain ⟨M, E, hM53', hE1, hEn, hE2, hE3, hmag, hMdef, hEdef⟩ := key
  rw [hMdef, hEdef]
  -- the error of the value
  have hval : |(M₀ : ℝ) * 2 ^ (e + n) - v * 2 ^ e| ≤ 2 ^ (e + n) / 2 := by
    have h2 : (2 : ℝ) ^ (e + n) = 2 ^ n * 2 ^ e := by
      rw [zpow_add₀ two_ne_zero, zpow_natCast]; ring
    have : (M₀ : ℝ) * 2 ^ (e + n) - v * 2 ^ e = ((M₀ : ℝ) - v / 2 ^ n) * 2 ^ (e + n) := by
      rw [h2]; field_simp
    rw [this, abs_mul, abs_of_pos (two_zpow_pos' _)]
    nlinarith [two_zpow_pos' (e + n)]
  have hbound : 2 ^ (e + n) / 2 ≤ (2 : ℝ) ^ (-53 : ℤ) * (v * 2 ^ e) + 2 ^ (-1075 : ℤ) := by
    have hp := two_zpow_pos' e
    have hnn : 0 ≤ (2 : ℝ) ^ (-53 : ℤ) * (v * 2 ^ e) := by positivity
    rcases eq_or_lt_of_le he1 with h | h
    · rw [← h, show ((2 : ℝ) ^ (-1074 : ℤ)) / 2 = 2 ^ (-1075 : ℤ) by
        rw [show (-1074 : ℤ) = -1075 + 1 by norm_num, zpow_add₀ two_ne_zero]; ring]
      linarith
    · have hv := (hnorm h).2
      have : (2 : ℝ) ^ (e + n) / 2 ≤ 2 ^ (-53 : ℤ) * (v * 2 ^ e) := by
        have h2 : (2 : ℝ) ^ (e + n) = 2 ^ n * 2 ^ e := by
          rw [zpow_add₀ two_ne_zero, zpow_natCast]; ring
        have h53 : (2 : ℝ) ^ (-53 : ℤ) * 2 ^ 52 = 1 / 2 := by norm_num
        rw [le_div_iff₀ hN] at hv
        rw [h2]; nlinarith
      linarith [two_zpow_pos' (-1075)]
  refine ⟨?_, isFinite_mkFin _ _ _, ?_⟩
  · -- canonical
    unfold mkFin
    split_ifs with h0
    · trivial
    · refine ⟨by omega, ?_, hM53', hEn⟩
      by_contra hcon
      have hcon := not_le.1 hcon
      have hEgt : -1074 < E := by omega
      have hM52 := hEn hEgt
      have hupper : mag M E ≤ v * 2 ^ e * (1 + 2 ^ (-53 : ℤ)) := by
        rcases eq_or_lt_of_le he1 with h | h
        · exfalso; omega
        · have hv := (hnorm h).2
          have : 2 ^ (e + n) / 2 ≤ (2 : ℝ) ^ (-53 : ℤ) * (v * 2 ^ e) := by
            have h2 : (2 : ℝ) ^ (e + n) = 2 ^ n * 2 ^ e := by
              rw [zpow_add₀ two_ne_zero, zpow_natCast]; ring
            have h53 : (2 : ℝ) ^ (-53 : ℤ) * 2 ^ 52 = 1 / 2 := by norm_num
            rw [le_div_iff₀ hN] at hv
            rw [h2]; nlinarith [two_zpow_pos' e]
          have hA : (M₀ : ℝ) * 2 ^ (e + n) ≤ v * 2 ^ e + 2 ^ (e + n) / 2 := by
            have := (abs_le.1 hval).2; linarith
          calc mag M E = (M₀ : ℝ) * 2 ^ (e + n) := hmag
            _ ≤ v * 2 ^ e + 2 ^ (e + n) / 2 := hA
            _ ≤ v * 2 ^ e + 2 ^ (-53 : ℤ) * (v * 2 ^ e) := by linarith
            _ = v * 2 ^ e * (1 + 2 ^ (-53 : ℤ)) := by ring
      have h2 : v * 2 ^ e * (1 + 2 ^ (-53 : ℤ)) ≤ maxFinite * (1 + 2 ^ (-53 : ℤ)) :=
        mul_le_mul_of_nonneg_right hhi (by positivity)
      have hup : mag M E < (2 : ℝ) ^ (1024 : ℤ) := by linarith [maxFinite_mul_lt]
      have hdown : (2 : ℝ) ^ ((52 : ℤ) + E) ≤ mag M E := by
        rw [zpow_add₀ two_ne_zero, mag]
        have : (2 : ℝ) ^ (52 : ℤ) ≤ M := by
          rw [show ((52 : ℤ)) = ((52 : ℕ) : ℤ) from rfl, zpow_natCast]; exact_mod_cast hM52
        exact mul_le_mul_of_nonneg_right this (two_zpow_pos' E).le
      have := (zpow_lt_zpow_iff_right₀ one_lt_two).1 (lt_of_le_of_lt hdown hup)
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
theorem divCore_spec (m₁ m₂ : ℕ) (e₁ e₂ : ℤ) (h1 : 0 < m₁) (h2 : 0 < m₂) :
    let r := divCore Format.binary64 m₁ e₁ m₂ e₂
    let v := (((m₁ * 2 ^ (e₁ - e₂ - r.2.1).toNat : ℕ) : ℝ) / m₂)
    AccOK r.2.2 r.1 v ∧ v * 2 ^ r.2.1 = mag m₁ e₁ / mag m₂ e₂ ∧
      (52 ≤ r.1.log2 ∨ r.2.1 ≤ -1074) := by
  intro r v
  set T := r.2.1 with hT
  have hTdef : T = min (e₁ - e₂) (max (((m₁.log2 : ℤ) + 1 + e₁) - ((m₂.log2 : ℤ) + 1 + e₂) - 53)
      (-1074)) := by
    simp only [hT, r, divCore, Format.targetExponent, totalExponent, Format.mantissaBits,
      Format.minExponent]; norm_num
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
    have h2e : (0 : ℝ) < 2 ^ e₂ := two_zpow_pos' _
    rw [div_mul_eq_mul_div, div_eq_div_iff hm2.ne' (by positivity)]
    push_cast
    have : (2 : ℝ) ^ (k : ℕ) * 2 ^ T * 2 ^ e₂ = 2 ^ e₁ := by
      rw [← zpow_natCast, ← zpow_add₀ two_ne_zero, ← zpow_add₀ two_ne_zero]; congr 1; omega
    calc (m₁ : ℝ) * 2 ^ k * 2 ^ T * ((m₂ : ℝ) * 2 ^ e₂)
        = (m₁ : ℝ) * m₂ * (2 ^ (k : ℕ) * 2 ^ T * 2 ^ e₂) := by ring
      _ = _ := by rw [this]; ring
  · by_cases hlo : T ≤ -1074
    · exact Or.inr hlo
    · left
      rw [hr1]
      set L₁ := m₁.log2; set L₂ := m₂.log2
      have hk' : (L₂ : ℤ) + 53 ≤ L₁ + k := by omega
      have hm1 : 2 ^ L₁ ≤ m₁ := Nat.log2_self_le (by omega)
      have hm2 : m₂ < 2 ^ (L₂ + 1) := Nat.lt_log2_self
      have hbig : 2 ^ 52 * m₂ ≤ m₁ * 2 ^ k := by
        have h3 : 2 ^ 52 * m₂ < 2 ^ 52 * 2 ^ (L₂ + 1) := Nat.mul_lt_mul_of_pos_left hm2 (by positivity)
        have h4 : 2 ^ 52 * 2 ^ (L₂ + 1) ≤ 2 ^ L₁ * 2 ^ k := by
          rw [← Nat.pow_add, ← Nat.pow_add]; exact Nat.pow_le_pow_right (by norm_num) (by omega)
        have h5 : 2 ^ L₁ * 2 ^ k ≤ m₁ * 2 ^ k := Nat.mul_le_mul_right _ hm1
        omega
      have hq : 2 ^ 52 ≤ m₁ * 2 ^ k / m₂ := (Nat.le_div_iff_mul_le h2).2 (by linarith)
      exact (Nat.le_log2 (by omega)).2 hq

theorem sign_div_toReal (s₁ s₂ : Sign) : (s₁ / s₂).toReal = s₁.toReal / s₂.toReal := by
  cases s₁ <;> cases s₂ <;> norm_num [Sign.toReal] <;> rfl

theorem mag_pos' {m : ℕ} (hm : 0 < m) (e : ℤ) : 0 < mag m e := mag_pos hm e

/-- **Division** rounds to nearest: relative error `2⁻⁵³` plus absolute error `2⁻¹⁰⁷⁵`. -/
theorem div_err_model {a b : Float} (ha : a.IsFinite) (hb : b.IsFinite) (hb0 : b.toReal ≠ 0)
    (hq : |a.toReal / b.toReal| ≤ maxFinite) :
    (a / b).IsFinite ∧ |(a / b).toReal - a.toReal / b.toReal| ≤
      2 ^ (-53 : ℤ) * |a.toReal / b.toReal| + 2 ^ (-1075 : ℤ) := by
  rcases QuadFloat.Zero.finite_cases ha with hz | ⟨s₁, m₁, e₁, hm₁, hfa⟩
  · have h0 : a.toReal = 0 := (QuadFloat.Zero.zero_iff.2 hz).2
    obtain ⟨hf, hv⟩ := QuadFloat.Zero.div_zero_left ha hb h0 hb0
    refine ⟨hf, ?_⟩
    rw [hv, h0, zero_div, sub_zero, abs_zero]; positivity
  rcases QuadFloat.Zero.finite_cases hb with hz | ⟨s₂, m₂, e₂, hm₂, hfb⟩
  · exact absurd (QuadFloat.Zero.zero_iff.2 hz).2 hb0
  have hav : a.toReal = s₁.toReal * mag m₁ e₁ := by rw [Float.toReal, hfa, toReal_finite]
  have hbv : b.toReal = s₂.toReal * mag m₂ e₂ := by rw [Float.toReal, hfb, toReal_finite]
  set r := divCore Format.binary64 m₁ e₁ m₂ e₂ with hr
  have e : (a / b).toModel = Float.Model.pack
      (roundWithAccuracy Format.binary64 (s₁ / s₂) r.1 r.2.1 r.2.2) := by
    show Float.Model.pack (UnpackedFloat.div Format.binary64 a.toModel.unpack b.toModel.unpack) = _
    rw [hfa, hfb]; rfl
  obtain ⟨hacc, hval, hL⟩ := divCore_spec m₁ m₂ e₁ e₂ hm₁ hm₂
  set v := (((m₁ * 2 ^ (e₁ - e₂ - r.2.1).toNat : ℕ) : ℝ) / m₂)
  have hquot : a.toReal / b.toReal = (s₁ / s₂).toReal * (v * 2 ^ r.2.1) := by
    rw [hav, hbv, hval, sign_div_toReal]
    have := Sign.abs_toReal s₂
    have hs2 : s₂.toReal ≠ 0 := by intro h; rw [h] at this; simp at this
    field_simp
  have habs : |a.toReal / b.toReal| = v * 2 ^ r.2.1 := by
    rw [hquot, abs_mul, Sign.abs_toReal, one_mul, abs_of_nonneg]
    rw [hval]; exact div_nonneg (mag_pos' hm₁ _).le (mag_pos' hm₂ _).le
  obtain ⟨hc, hf, herr⟩ := roundWithAccuracy_real (s₁ / s₂) r.1 r.2.1 r.2.2 v hacc hL
    (habs ▸ hq)
  obtain ⟨hF, hV⟩ := QuadFloat.Zero.of_pack e hc hf
  refine ⟨hF, ?_⟩
  rw [hV, habs, hquot]; exact herr

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
theorem sqrtCore_spec (m : ℕ) (e : ℤ) (hm : 0 < m) :
    let r := sqrtCore Format.binary64 m e
    let M := m * 2 ^ (e - 2 * r.2.1).toNat
    AccOK r.2.2 r.1 (Real.sqrt M) ∧ Real.sqrt M * 2 ^ r.2.1 = Real.sqrt (mag m e) ∧
      (52 ≤ r.1.log2 ∨ r.2.1 ≤ -1074) := by
  intro r M
  set T := r.2.1 with hT
  have hTdef : T = min (e.ediv 2) (max ((((m.log2 : ℤ) + 1 + e) + 1).ediv 2 - 53) (-1074)) := by
    simp only [hT, r, sqrtCore, Format.targetExponent, totalExponent, Format.mantissaBits,
      Format.minExponent]; norm_num
  have hr1 : r.1 = M.sqrt := by simp only [r, M, sqrtCore, Nat.shiftLeft_eq]
  have hr22 : r.2.2 = (if M - M.sqrt * M.sqrt = 0 then .exact
      else .inexact (if M - M.sqrt * M.sqrt ≤ M.sqrt then .lt else .gt)) := by
    simp only [r, M, sqrtCore, Nat.shiftLeft_eq]
  have hTdef' : T = min (e / 2) (max ((((m.log2 : ℤ) + 1 + e) + 1) / 2 - 53) (-1074)) := hTdef
  have he2 : 2 * T ≤ e := by rw [hTdef']; omega
  refine ⟨?_, ?_, ?_⟩
  · rw [hr1, hr22]; exact accOK_sqrt M
  · have hk : ((e - 2 * T).toNat : ℤ) = e - 2 * T := by omega
    have hmag : mag m e = (M : ℝ) * (2 ^ T) ^ 2 := by
      simp only [M, mag]; push_cast
      rw [← zpow_natCast, hk, ← zpow_natCast, ← zpow_mul, mul_assoc, ← zpow_add₀ two_ne_zero]
      congr 2; push_cast; ring
    rw [hmag, Real.sqrt_mul (Nat.cast_nonneg _), Real.sqrt_sq (two_zpow_pos' T).le]
  · by_cases hlo : T ≤ -1074
    · exact Or.inr hlo
    · left
      rw [hr1]
      have hsh : 104 ≤ m.log2 + (e - 2 * T).toNat := by rw [hTdef'] at hlo ⊢; omega
      have hmL : 2 ^ m.log2 ≤ m := Nat.log2_self_le (by omega)
      have hM : 2 ^ 52 * 2 ^ 52 ≤ M := by
        have : 2 ^ 52 * 2 ^ 52 ≤ 2 ^ m.log2 * 2 ^ (e - 2 * T).toNat := by
          rw [← Nat.pow_add, ← Nat.pow_add]; exact Nat.pow_le_pow_right (by norm_num) (by omega)
        exact this.trans (Nat.mul_le_mul_right _ hmL)
      have hroot : 2 ^ 52 ≤ M.sqrt := Nat.le_sqrt.2 hM
      exact (Nat.le_log2 (by omega)).2 hroot

/-- **Square root** rounds to nearest: relative error `2⁻⁵³` plus absolute error `2⁻¹⁰⁷⁵`. -/
theorem sqrt_err_model {a : Float} (ha : a.IsFinite) (h0 : 0 ≤ a.toReal)
    (h1 : a.toReal ≤ maxFinite) (h1' : 1 ≤ maxFinite) :
    (Float.sqrt a).IsFinite ∧ |(Float.sqrt a).toReal - Real.sqrt a.toReal| ≤
      2 ^ (-53 : ℤ) * Real.sqrt a.toReal + 2 ^ (-1075 : ℤ) := by
  have e0 : (Float.sqrt a).toModel =
      Float.Model.pack (UnpackedFloat.sqrt Format.binary64 a.toModel.unpack) := rfl
  rcases QuadFloat.Zero.finite_cases ha with ⟨s, hz⟩ | ⟨s, m, e, hm, hfa⟩
  · rw [hz] at e0
    obtain ⟨hF, hV⟩ := QuadFloat.Zero.of_pack_zero e0 ⟨s, rfl⟩
    have ha0 : a.toReal = 0 := by rw [Float.toReal, hz]; rfl
    refine ⟨hF, ?_⟩
    rw [hV, ha0, Real.sqrt_zero, sub_zero, abs_zero]; positivity
  have hav : a.toReal = s.toReal * mag m e := by rw [Float.toReal, hfa, toReal_finite]
  cases s with
  | negative =>
    exfalso
    have := mag_pos' hm e
    rw [hav] at h0; simp [Sign.toReal] at h0; linarith
  | positive =>
    have hav' : a.toReal = mag m e := by rw [hav]; simp [Sign.toReal]
    rw [hfa] at e0
    set r := sqrtCore Format.binary64 m e
    have eq : (Float.sqrt a).toModel = Float.Model.pack
        (roundWithAccuracy Format.binary64 .positive r.1 r.2.1 r.2.2) := e0
    obtain ⟨hacc, hval, hL⟩ := sqrtCore_spec m e hm
    have hhi : Real.sqrt (m * 2 ^ (e - 2 * r.2.1).toNat : ℕ) * 2 ^ r.2.1 ≤ maxFinite := by
      rw [hval, ← hav']
      rcases le_total a.toReal 1 with h | h
      · have : Real.sqrt a.toReal ≤ 1 := Real.sqrt_le_one.mpr h
        linarith
      · have : Real.sqrt a.toReal ≤ a.toReal := by
          rw [Real.sqrt_le_left (by linarith)]; nlinarith
        linarith
    obtain ⟨hc, hf, herr⟩ := roundWithAccuracy_real .positive r.1 r.2.1 r.2.2 _ hacc hL hhi
    obtain ⟨hF, hV⟩ := QuadFloat.Zero.of_pack eq hc hf
    refine ⟨hF, ?_⟩
    rw [hV, hav', ← hval]
    simpa [Sign.toReal] using herr

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
