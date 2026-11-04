/-
Round-to-nearest never crosses a float, generic over the format.

The error bounds of `FloatModel.Add`, `Small`, `DivSqrt` bound how far a rounded result is from
the exact value `x`; they do not say that a float `f ≤ x` stays below the rounded result, which is
what monotone code such as a midpoint `(lo + hi) / 2 ∈ [lo, hi]` needs. `BracketIn spec r x`
states it: every float of the format below `x` is below `r`, every float above `x` is above `r`.
In particular a result whose exact value is itself a float is computed exactly.

The proof works on the structure of `roundWithAccuracy` (`roundWithAccuracy_struct`): the result
has magnitude `M₀ 2^G` with `M₀` a nearest integer to `X / 2^G`; a float with exponent at least `G`
is an integer multiple of `2^G`, so it cannot lie strictly between `X` and `M₀ 2^G`; a float with a
smaller exponent is below `2^k 2^G`, which bounds both `X` and `M₀ 2^G` from below whenever such
floats exist (`bracket_mag`). The binary64 statements (`Float.add_bracket`, …) are at the end; the
binary32 ones are in `FloatModel.Float32`.
-/
import FloatModel.DivSqrt

open Float.Model UnpackedFloat ExtendedMantissa

namespace Float.Model.UnpackedFloat

/-- No float of the format lies strictly between `x` and the value of `r`. -/
def BracketIn (spec : Format) (r : UnpackedFloat) (x : ℝ) : Prop :=
  ∀ f : UnpackedFloat, CanonicalIn spec f → f.isFinite = true →
    (f.toReal ≤ x → f.toReal ≤ r.toReal) ∧ (x ≤ f.toReal → r.toReal ≤ f.toReal)

theorem bracketIn_of_eq {spec : Format} {r : UnpackedFloat} {x : ℝ} (h : r.toReal = x) :
    BracketIn spec r x :=
  fun _ _ _ => ⟨fun h' => h ▸ h', fun h' => h ▸ h'⟩

/-- A nearest integer multiple of `2^G` to `X` is at least every multiple of `2^G` below `X`. -/
theorem nearest_grid_le {M₀ : ℕ} {G : ℤ} {X : ℝ} (hval : |(M₀ : ℝ) * 2 ^ G - X| ≤ 2 ^ G / 2)
    {Y : ℤ} (hY : (Y : ℝ) * 2 ^ G ≤ X) : (Y : ℝ) * 2 ^ G ≤ M₀ * 2 ^ G := by
  have hp := two_zpow_pos G
  by_contra hc
  have hlt : ((M₀ : ℤ) : ℝ) < Y := by
    have := not_le.1 hc; push_cast; exact lt_of_mul_lt_mul_right this hp.le
  have hle : ((M₀ : ℤ) : ℝ) + 1 ≤ Y := by exact_mod_cast (show (M₀ : ℤ) + 1 ≤ Y by exact_mod_cast hlt)
  push_cast at hle
  have := (abs_le.1 hval).1
  nlinarith

/-- A nearest integer multiple of `2^G` to `X` is at most every multiple of `2^G` above `X`. -/
theorem nearest_grid_ge {M₀ : ℕ} {G : ℤ} {X : ℝ} (hval : |(M₀ : ℝ) * 2 ^ G - X| ≤ 2 ^ G / 2)
    {Y : ℤ} (hY : X ≤ (Y : ℝ) * 2 ^ G) : (M₀ : ℝ) * 2 ^ G ≤ Y * 2 ^ G := by
  have hp := two_zpow_pos G
  by_contra hc
  have hlt : (Y : ℝ) < ((M₀ : ℤ) : ℝ) := by
    have := not_le.1 hc; push_cast; exact lt_of_mul_lt_mul_right this hp.le
  have hle : (Y : ℝ) + 1 ≤ ((M₀ : ℤ) : ℝ) := by exact_mod_cast (show Y + 1 ≤ (M₀ : ℤ) by exact_mod_cast hlt)
  push_cast at hle
  have := (abs_le.1 hval).2
  nlinarith

/-- A finite float with exponent at least `G` is an integer multiple of `2^G`. -/
theorem toReal_finite_grid (s : Sign) (F : ℕ) (g G : ℤ) (hF : 0 < F) (hg : G ≤ g) :
    (UnpackedFloat.finite s F g hF).toReal =
      ((s.apply ((F * 2 ^ (g - G).toNat : ℕ) : ℤ) : ℤ) : ℝ) * 2 ^ G := by
  have h := mag_mul_two_pow F (g - G).toNat g
  rw [show g - ((g - G).toNat : ℤ) = G by omega] at h
  rw [toReal_finite, ← h, mag]
  cases s <;> simp [Sign.apply, Sign.toReal]

/-- **The core.** A nonnegative `X` rounded to `M₀ 2^G` as in `roundWithAccuracy_struct` is not
separated from `M₀ 2^G` by any float. -/
theorem bracket_mag {spec : Format} {M₀ : ℕ} {G : ℤ} {X : ℝ}
    (hG : spec.minExponent ≤ G) (hval : |(M₀ : ℝ) * 2 ^ G - X| ≤ 2 ^ G / 2)
    (hnorm : spec.minExponent < G →
      (2 : ℝ) ^ spec.mantissaBitsWithoutImplicit * 2 ^ G ≤ X ∧ 2 ^ spec.mantissaBitsWithoutImplicit ≤ M₀)
    (f : UnpackedFloat) (cf : CanonicalIn spec f) (ff : f.isFinite = true) :
    (f.toReal ≤ X → f.toReal ≤ M₀ * 2 ^ G) ∧ (X ≤ f.toReal → M₀ * 2 ^ G ≤ f.toReal) := by
  cases f with
  | infinity _ => simp [isFinite] at ff
  | notANumber => simp [isFinite] at ff
  | zero s =>
    have h0 : (zero s).toReal = ((0 : ℤ) : ℝ) * 2 ^ G := by simp [toReal]
    rw [h0]
    exact ⟨fun h => nearest_grid_le hval h, fun h => nearest_grid_ge hval h⟩
  | finite s F g hF =>
    by_cases hg : G ≤ g
    · rw [toReal_finite_grid s F g G hF hg]
      exact ⟨fun h => nearest_grid_le hval h, fun h => nearest_grid_ge hval h⟩
    · obtain ⟨c1, -, c3, -⟩ := cf
      have hGt : spec.minExponent < G := by omega
      obtain ⟨hXk, hMk⟩ := hnorm hGt
      have hF' : (F : ℝ) < 2 * 2 ^ spec.mantissaBitsWithoutImplicit := by
        have : (F : ℝ) < (2 : ℝ) ^ spec.mantissaBits := by exact_mod_cast c3
        rwa [Format.mantissaBits_eq, pow_succ, mul_comm] at this
      have hz : (2 : ℝ) ^ g * 2 ≤ 2 ^ G := by
        rw [← zpow_add_one₀ two_ne_zero]; exact zpow_le_zpow_right₀ one_le_two (by omega)
      have hpg := two_zpow_pos g
      have hmag : |(UnpackedFloat.finite s F g hF).toReal| <
          (2 : ℝ) ^ spec.mantissaBitsWithoutImplicit * 2 ^ G := by
        rw [toReal_finite, abs_sign_mag, mag]
        calc (F : ℝ) * 2 ^ g < 2 * 2 ^ spec.mantissaBitsWithoutImplicit * 2 ^ g := by gcongr
          _ = 2 ^ spec.mantissaBitsWithoutImplicit * (2 ^ g * 2) := by ring
          _ ≤ 2 ^ spec.mantissaBitsWithoutImplicit * 2 ^ G := by gcongr
      have hM : (2 : ℝ) ^ spec.mantissaBitsWithoutImplicit * 2 ^ G ≤ M₀ * 2 ^ G := by
        have : (2 : ℝ) ^ spec.mantissaBitsWithoutImplicit ≤ M₀ := by exact_mod_cast hMk
        exact mul_le_mul_of_nonneg_right this (two_zpow_pos G).le
      have hle := le_abs_self (UnpackedFloat.finite s F g hF).toReal
      exact ⟨fun _ => by linarith, fun h => by linarith⟩

/-- The signed form: from the bracket of the magnitudes to the bracket of `± R` around `± X`. -/
theorem bracketIn_signed {spec : Format} {s : Sign} {R X : ℝ} {r : UnpackedFloat}
    (hcore : ∀ f : UnpackedFloat, CanonicalIn spec f → f.isFinite = true →
      (f.toReal ≤ X → f.toReal ≤ R) ∧ (X ≤ f.toReal → R ≤ f.toReal))
    (hr : r.toReal = s.toReal * R) : BracketIn spec r (s.toReal * X) := by
  intro f cf ff
  rw [hr]
  cases s with
  | positive => simpa [Sign.toReal] using hcore f cf ff
  | negative =>
    have cf' := canonicalIn_neg cf
    have ff' : f.neg.isFinite = true := by
      cases f <;> simp_all [UnpackedFloat.neg, UnpackedFloat.isFinite]
    obtain ⟨h1, h2⟩ := hcore f.neg cf' ff'
    rw [toReal_neg] at h1 h2
    simp only [Sign.toReal, neg_one_mul]
    exact ⟨fun h => by linarith [h2 (by linarith)], fun h => by linarith [h1 (by linarith)]⟩

/-- `roundWithAccuracy` with a correct accuracy does not cross a float. -/
theorem bracketIn_roundWithAccuracy (spec : Format) (s : Sign) (m : ℕ) (e : ℤ) (acc : Accuracy)
    (v : ℝ) (hacc : AccOK acc m v)
    (hL : spec.mantissaBitsWithoutImplicit ≤ m.log2 ∨ e ≤ spec.minExponent) :
    BracketIn spec (roundWithAccuracy spec s m e acc) (s.toReal * (v * 2 ^ e)) := by
  obtain ⟨M, M₀, E, G, hres, hmag, -, -, -, -, he1, hval, hnorm⟩ :=
    roundWithAccuracy_struct spec s m e acc v hacc hL
  refine bracketIn_signed (bracket_mag he1 hval hnorm) ?_
  rw [hres, toReal_mkFin, hmag]

/-- `round` does not cross a float. -/
theorem bracketIn_round (spec : Format) (s : Sign) (m : ℕ) (e : ℤ) (hm : 0 < m) :
    BracketIn spec (round spec s m e) (s.toReal * mag m e) := by
  have hPk := Format.mantissaBits_eq spec
  simp only [round, decreaseExponent, Nat.shiftLeft_eq]
  set k := (e - spec.targetExponent (totalExponent m e)).toNat with hk
  have hk' := round_shift_amount spec m e
  have hmag := mag_mul_two_pow m k e
  have hlog := log2_mul_two_pow m k hm
  have h := bracketIn_roundWithAccuracy spec s (m * 2 ^ k) (e - k) .exact ((m * 2 ^ k : ℕ) : ℝ)
    rfl (by rw [hlog]; omega)
  rwa [show ((m * 2 ^ k : ℕ) : ℝ) * 2 ^ (e - (k : ℤ)) = mag m e by rw [← hmag, mag]] at h

/-- `normalize` does not cross a float. -/
theorem bracketIn_normalize (spec : Format) (N : ℤ) (E : ℤ) (zs : Sign) :
    BracketIn spec (normalize spec N E zs) ((N : ℝ) * 2 ^ E) := by
  have hE := two_zpow_pos E
  unfold normalize
  rcases lt_trichotomy N 0 with h | h | h
  · rw [Int.compare_eq_lt.2 h]
    have hm : 0 < (-N).toNat := by omega
    have hx : (N : ℝ) * 2 ^ E = Sign.negative.toReal * mag (-N).toNat E := by
      rw [mag]; simp only [Sign.toReal]
      have : (((-N).toNat : ℤ) : ℝ) = ((-N : ℤ) : ℝ) := by congr 1; omega
      push_cast at this ⊢; rw [this]; ring
    rw [hx]; exact bracketIn_round spec _ _ _ hm
  · subst h; exact bracketIn_of_eq (by simp [toReal])
  · rw [Int.compare_eq_gt.2 h]
    have hm : 0 < N.toNat := by omega
    have hx : (N : ℝ) * 2 ^ E = Sign.positive.toReal * mag N.toNat E := by
      have : ((N.toNat : ℤ) : ℝ) = (N : ℝ) := by congr 1; omega
      rw [mag]; simp only [Sign.toReal, one_mul]; rw [← this, Int.cast_natCast]
    rw [hx]; exact bracketIn_round spec _ _ _ hm

theorem bracketIn_add {spec : Format} {u v : UnpackedFloat}
    (fu : u.isFinite = true) (fv : v.isFinite = true) :
    BracketIn spec (add spec u v) (u.toReal + v.toReal) := by
  cases u with
  | infinity _ => simp [isFinite] at fu
  | notANumber => simp [isFinite] at fu
  | zero s₁ =>
    cases v with
    | infinity _ => simp [isFinite] at fv
    | notANumber => simp [isFinite] at fv
    | zero s₂ => exact bracketIn_of_eq (by simp only [add]; split_ifs <;> simp [toReal])
    | finite s₂ m₂ e₂ hm₂ => exact bracketIn_of_eq (by simp [add, toReal])
  | finite s₁ m₁ e₁ hm₁ =>
    cases v with
    | infinity _ => simp [isFinite] at fv
    | notANumber => simp [isFinite] at fv
    | zero s₂ => exact bracketIn_of_eq (by simp [add, toReal])
    | finite s₂ m₂ e₂ hm₂ =>
      simp only [add, decreaseExponent]
      rw [← add_key s₁ s₂ m₁ m₂ e₁ e₂ hm₁ hm₂]
      exact bracketIn_normalize spec _ _ _

theorem bracketIn_sub {spec : Format} {u v : UnpackedFloat}
    (fu : u.isFinite = true) (fv : v.isFinite = true) :
    BracketIn spec (sub spec u v) (u.toReal - v.toReal) := by
  cases u with
  | infinity _ => simp [isFinite] at fu
  | notANumber => simp [isFinite] at fu
  | zero s₁ =>
    cases v with
    | infinity _ => simp [isFinite] at fv
    | notANumber => simp [isFinite] at fv
    | zero s₂ => exact bracketIn_of_eq (by simp only [sub]; split_ifs <;> simp [toReal])
    | finite s₂ m₂ e₂ hm₂ =>
      refine bracketIn_of_eq ?_
      have := toReal_neg (.finite s₂ m₂ e₂ hm₂)
      simp only [neg] at this
      simp only [sub, this]; simp [toReal]
  | finite s₁ m₁ e₁ hm₁ =>
    cases v with
    | infinity _ => simp [isFinite] at fv
    | notANumber => simp [isFinite] at fv
    | zero s₂ => exact bracketIn_of_eq (by simp [sub, toReal])
    | finite s₂ m₂ e₂ hm₂ =>
      simp only [sub, decreaseExponent]
      rw [← sub_key s₁ s₂ m₁ m₂ e₁ e₂ hm₁ hm₂]
      exact bracketIn_normalize spec _ _ _

theorem bracketIn_mul {spec : Format} {u v : UnpackedFloat} (cu : CanonicalIn spec u)
    (cv : CanonicalIn spec v) (fu : u.isFinite = true) (fv : v.isFinite = true) :
    BracketIn spec (mul spec u v) (u.toReal * v.toReal) := by
  cases u with
  | infinity _ => simp [isFinite] at fu
  | notANumber => simp [isFinite] at fu
  | zero s₁ =>
    cases v with
    | infinity _ => simp [isFinite] at fv
    | notANumber => simp [isFinite] at fv
    | zero s₂ => exact bracketIn_of_eq (by simp [mul, toReal])
    | finite s₂ m₂ e₂ hm₂ => exact bracketIn_of_eq (by simp [mul, toReal])
  | finite s₁ m₁ e₁ hm₁ =>
    cases v with
    | infinity _ => simp [isFinite] at fv
    | notANumber => simp [isFinite] at fv
    | zero s₂ => exact bracketIn_of_eq (by simp [mul, toReal])
    | finite s₂ m₂ e₂ hm₂ =>
      simp only [mul]
      rw [mul_key]
      have h := bracketIn_roundWithAccuracy spec (s₁ * s₂) (m₁ * m₂) (e₁ + e₂) .exact
        ((m₁ * m₂ : ℕ) : ℝ) rfl (mul_log2_or cu cv)
      rwa [show ((m₁ * m₂ : ℕ) : ℝ) * 2 ^ (e₁ + e₂) = mag (m₁ * m₂) (e₁ + e₂) from rfl] at h

theorem bracketIn_div {spec : Format} {u v : UnpackedFloat}
    (fu : u.isFinite = true) (fv : v.isFinite = true) (hv0 : v.toReal ≠ 0) :
    BracketIn spec (div spec u v) (u.toReal / v.toReal) := by
  cases u with
  | infinity _ => simp [isFinite] at fu
  | notANumber => simp [isFinite] at fu
  | zero s₁ =>
    cases v with
    | infinity _ => simp [isFinite] at fv
    | notANumber => simp [isFinite] at fv
    | zero s₂ => exact absurd rfl hv0
    | finite s₂ m₂ e₂ hm₂ => exact bracketIn_of_eq (by simp [div, toReal])
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
      rw [hquot]
      exact bracketIn_roundWithAccuracy spec (s₁ / s₂) r.1 r.2.1 r.2.2 w hacc hL

theorem bracketIn_sqrt {spec : Format} {u : UnpackedFloat} (fu : u.isFinite = true)
    (h0 : 0 ≤ u.toReal) : BracketIn spec (sqrt spec u) (Real.sqrt u.toReal) := by
  cases u with
  | infinity _ => simp [isFinite] at fu
  | notANumber => simp [isFinite] at fu
  | zero s => exact bracketIn_of_eq (by simp [UnpackedFloat.sqrt, toReal])
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
      have h := bracketIn_roundWithAccuracy spec .positive r.1 r.2.1 r.2.2 _ hacc hL
      rwa [hval, ← hav', show Sign.positive.toReal = 1 from rfl, one_mul] at h

/-! ## Canonical results on every value up to the largest finite one -/

theorem canonicalIn_add_all {spec : Format} (hw : 2 ≤ spec.exponentBits) {u v : UnpackedFloat}
    (cu : CanonicalIn spec u) (cv : CanonicalIn spec v)
    (fu : u.isFinite = true) (fv : v.isFinite = true)
    (hhi : |u.toReal + v.toReal| ≤ maxFiniteIn spec) : CanonicalIn spec (add spec u v) := by
  rcases lt_or_ge |u.toReal + v.toReal| ((2 : ℝ) ^ spec.normExponent) with h | h
  · exact (exactRoundIn_add hw cu cv fu fv h).1
  · exact (goodRoundIn_add cu cv fu fv h hhi).1

theorem canonicalIn_sub_all {spec : Format} (hw : 2 ≤ spec.exponentBits) {u v : UnpackedFloat}
    (cu : CanonicalIn spec u) (cv : CanonicalIn spec v)
    (fu : u.isFinite = true) (fv : v.isFinite = true)
    (hhi : |u.toReal - v.toReal| ≤ maxFiniteIn spec) : CanonicalIn spec (sub spec u v) := by
  rcases lt_or_ge |u.toReal - v.toReal| ((2 : ℝ) ^ spec.normExponent) with h | h
  · exact (exactRoundIn_sub hw cu cv fu fv h).1
  · exact (goodRoundIn_sub cu cv fu fv h hhi).1

theorem canonicalIn_mul_all {spec : Format} (hw : 2 ≤ spec.exponentBits) {u v : UnpackedFloat}
    (cu : CanonicalIn spec u) (cv : CanonicalIn spec v)
    (fu : u.isFinite = true) (fv : v.isFinite = true)
    (hhi : |u.toReal * v.toReal| ≤ maxFiniteIn spec) : CanonicalIn spec (mul spec u v) := by
  rcases lt_or_ge |u.toReal * v.toReal| ((2 : ℝ) ^ spec.normExponent) with h | h
  · exact (smallRoundIn_mul hw cu cv fu fv h).1
  · exact (goodRoundIn_mul cu cv fu fv h hhi).1

/-- A float twice a float, when that does not overflow. -/
theorem exists_double {spec : Format} {u : UnpackedFloat} (cu : CanonicalIn spec u)
    (fu : u.isFinite = true) (hhi : |2 * u.toReal| ≤ maxFiniteIn spec) :
    ∃ w : UnpackedFloat, CanonicalIn spec w ∧ w.isFinite = true ∧ w.toReal = 2 * u.toReal := by
  have hP := two_pow_mantissaBits spec
  cases u with
  | infinity _ => simp [isFinite] at fu
  | notANumber => simp [isFinite] at fu
  | zero s => exact ⟨.zero s, trivial, rfl, by simp [toReal]⟩
  | finite s F g hF =>
    obtain ⟨c1, c2, c3, c4⟩ := cu
    by_cases hsub : F < 2 ^ spec.mantissaBitsWithoutImplicit
    · have hg : g = spec.minExponent := by
        by_contra hc; have := c4 (by omega); omega
      refine ⟨.finite s (2 * F) g (by omega), ⟨c1, c2, by omega, fun h => by omega⟩, rfl, ?_⟩
      rw [toReal_finite, toReal_finite, mag, mag]; push_cast; ring
    · push Not at hsub
      refine ⟨.finite s F (g + 1) hF, ⟨by omega, ?_, c3, fun _ => hsub⟩, rfl, ?_⟩
      · by_contra hc
        have hc' : spec.maxExponent ≤ g := by omega
        rw [toReal_finite, abs_mul, abs_two, abs_sign_mag, mag, maxFiniteIn] at hhi
        have hk : (2 : ℝ) ^ spec.mantissaBitsWithoutImplicit ≤ F := by exact_mod_cast hsub
        have hge : (2 : ℝ) ^ spec.maxExponent ≤ 2 ^ g := zpow_le_zpow_right₀ one_le_two hc'
        have hpos := two_zpow_pos spec.maxExponent
        have hPr : (2 : ℝ) ^ spec.mantissaBits = 2 * 2 ^ spec.mantissaBitsWithoutImplicit := by
          exact_mod_cast hP
        rw [hPr] at hhi
        nlinarith
      · rw [toReal_finite, toReal_finite, mag, mag, zpow_add_one₀ two_ne_zero]; ring

end Float.Model.UnpackedFloat

namespace Float

open Float.Model.UnpackedFloat

theorem toReal_of_toModel {x : Float} {r : UnpackedFloat} (h : x.toModel = Float.Model.pack r)
    (hc : CanonicalIn Format.binary64 r) : x.toReal = r.toReal := by
  rw [toReal, h, Float.Model.unpack_pack_of_canonical ((canonical_iff _).2 hc)]

theorem isFinite_of_isFinite_unpack {f : Float} (hf : f.IsFinite) : f.toModel.unpack.isFinite = true := hf

/-- The bracket of a computed result against every finite float `f`. -/
theorem bracket_transfer {x : Float} {r : UnpackedFloat} {y : ℝ}
    (h : x.toModel = Float.Model.pack r) (hc : CanonicalIn Format.binary64 r)
    (hb : BracketIn Format.binary64 r y) {f : Float} (hf : f.IsFinite) :
    (f.toReal ≤ y → f.toReal ≤ x.toReal) ∧ (y ≤ f.toReal → x.toReal ≤ f.toReal) := by
  rw [toReal_of_toModel h hc]
  exact hb _ f.canonicalIn_unpack hf

/-- `Float` addition does not cross a float: a finite float below (above) the exact sum is below
(above) the computed sum. -/
theorem add_bracket {a b : Float} (ha : a.IsFinite) (hb : b.IsFinite)
    (hhi : |a.toReal + b.toReal| ≤ maxFinite) {f : Float} (hf : f.IsFinite) :
    (f.toReal ≤ a.toReal + b.toReal → f.toReal ≤ (a + b).toReal) ∧
      (a.toReal + b.toReal ≤ f.toReal → (a + b).toReal ≤ f.toReal) :=
  bracket_transfer rfl (canonicalIn_add_all (by decide) a.canonicalIn_unpack b.canonicalIn_unpack
    ha hb hhi) (bracketIn_add ha hb) hf

theorem sub_bracket {a b : Float} (ha : a.IsFinite) (hb : b.IsFinite)
    (hhi : |a.toReal - b.toReal| ≤ maxFinite) {f : Float} (hf : f.IsFinite) :
    (f.toReal ≤ a.toReal - b.toReal → f.toReal ≤ (a - b).toReal) ∧
      (a.toReal - b.toReal ≤ f.toReal → (a - b).toReal ≤ f.toReal) :=
  bracket_transfer rfl (canonicalIn_sub_all (by decide) a.canonicalIn_unpack b.canonicalIn_unpack
    ha hb hhi) (bracketIn_sub ha hb) hf

theorem mul_bracket {a b : Float} (ha : a.IsFinite) (hb : b.IsFinite)
    (hhi : |a.toReal * b.toReal| ≤ maxFinite) {f : Float} (hf : f.IsFinite) :
    (f.toReal ≤ a.toReal * b.toReal → f.toReal ≤ (a * b).toReal) ∧
      (a.toReal * b.toReal ≤ f.toReal → (a * b).toReal ≤ f.toReal) :=
  bracket_transfer rfl (canonicalIn_mul_all (by decide) a.canonicalIn_unpack b.canonicalIn_unpack
    ha hb hhi) (bracketIn_mul a.canonicalIn_unpack b.canonicalIn_unpack ha hb) hf

theorem div_bracket {a b : Float} (ha : a.IsFinite) (hb : b.IsFinite) (hb0 : b.toReal ≠ 0)
    (hhi : |a.toReal / b.toReal| ≤ maxFinite) {f : Float} (hf : f.IsFinite) :
    (f.toReal ≤ a.toReal / b.toReal → f.toReal ≤ (a / b).toReal) ∧
      (a.toReal / b.toReal ≤ f.toReal → (a / b).toReal ≤ f.toReal) :=
  bracket_transfer rfl (nearRoundIn_div (by decide) a.canonicalIn_unpack b.canonicalIn_unpack
    ha hb hb0 hhi).1 (bracketIn_div ha hb hb0) hf

theorem sqrt_bracket {a : Float} (ha : a.IsFinite) (h0 : 0 ≤ a.toReal)
    (h1 : a.toReal ≤ maxFinite) {f : Float} (hf : f.IsFinite) :
    (f.toReal ≤ Real.sqrt a.toReal → f.toReal ≤ (Float.sqrt a).toReal) ∧
      (Real.sqrt a.toReal ≤ f.toReal → (Float.sqrt a).toReal ≤ f.toReal) :=
  bracket_transfer rfl (nearRoundIn_sqrt (by decide) a.canonicalIn_unpack ha h0 h1
    one_le_maxFinite).1 (bracketIn_sqrt ha h0) hf

end Float
