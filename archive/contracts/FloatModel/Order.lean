module

/-
The comparison operators of a float format agree with the exact real values on finite floats,
generic over the format (`compare_eq_some_compare_toReal`); the `Float` instances follow.
-/
public import FloatModel.ToReal

@[expose] public section

open Float.Model UnpackedFloat

namespace Float.Model.UnpackedFloat

/-- A real `compare` pinned down by trichotomy. -/
theorem compare_real_eq_iff {x y : ℝ} {c : Ordering} :
    compare x y = c ↔ (c = .lt ∧ x < y) ∨ (c = .eq ∧ x = y) ∨ (c = .gt ∧ y < x) := by
  rcases lt_trichotomy x y with h | h | h
  · rw [compare_lt_iff_lt.2 h]; cases c <;> simp [h, h.ne, h.not_gt]
  · rw [compare_eq_iff_eq.2 h]; cases c <;> simp [h]
  · rw [compare_gt_iff_gt.2 h]; cases c <;> simp [h, h.ne', h.not_gt]

/-- Magnitude `m · 2^e` of a finite unpacked float. -/
noncomputable def mag (m : Nat) (e : Int) : ℝ := (m : ℝ) * (2 : ℝ) ^ e

theorem mag_pos {m : Nat} (hm : 0 < m) (e : Int) : 0 < mag m e := by
  unfold mag; positivity

/-- Canonical floats with a smaller exponent have a smaller magnitude. -/
theorem mag_lt_of_exp_lt {spec : Format} {m₁ m₂ : Nat} {e₁ e₂ : Int}
    (h₁ : m₁ < 2 ^ spec.mantissaBits)
    (h₂ : spec.minExponent < e₂ → 2 ^ spec.mantissaBitsWithoutImplicit ≤ m₂)
    (h₁' : spec.minExponent ≤ e₁) (he : e₁ < e₂) :
    mag m₁ e₁ < mag m₂ e₂ := by
  have hk : (2 : ℝ) ^ spec.mantissaBitsWithoutImplicit ≤ m₂ := by exact_mod_cast h₂ (by omega)
  have hm₁ : (m₁ : ℝ) < 2 * 2 ^ spec.mantissaBitsWithoutImplicit := by
    have : (m₁ : ℝ) < (2 : ℝ) ^ spec.mantissaBits := by exact_mod_cast h₁
    rwa [Format.mantissaBits_eq, pow_succ, mul_comm] at this
  have hz : (2 : ℝ) ^ e₁ * 2 ≤ (2 : ℝ) ^ e₂ := by
    rw [← zpow_add_one₀ two_ne_zero]
    exact zpow_le_zpow_right₀ one_le_two (by omega)
  have hp : (0 : ℝ) < (2 : ℝ) ^ e₁ := by positivity
  unfold mag
  calc (m₁ : ℝ) * 2 ^ e₁ < 2 * 2 ^ spec.mantissaBitsWithoutImplicit * 2 ^ e₁ := by gcongr
    _ = 2 ^ spec.mantissaBitsWithoutImplicit * (2 ^ e₁ * 2) := by ring
    _ ≤ 2 ^ spec.mantissaBitsWithoutImplicit * 2 ^ e₂ := by gcongr
    _ ≤ m₂ * 2 ^ e₂ := by gcongr

/-- On canonical positive floats, the lexicographic (exponent, mantissa) comparison used by
`UnpackedFloat.compare` is the comparison of exact magnitudes. -/
theorem lex_eq_compare_mag {spec : Format} {s₁ s₂ : Sign} {m₁ m₂ : Nat} {e₁ e₂ : Int}
    {hm₁ : 0 < m₁} {hm₂ : 0 < m₂}
    (c₁ : CanonicalIn spec (.finite s₁ m₁ e₁ hm₁)) (c₂ : CanonicalIn spec (.finite s₂ m₂ e₂ hm₂)) :
    (compare e₁ e₂).then (compare m₁ m₂) = compare (mag m₁ e₁) (mag m₂ e₂) := by
  rcases lt_trichotomy e₁ e₂ with he | he | he
  · rw [Int.compare_eq_lt.2 he, compare_lt_iff_lt.2 (mag_lt_of_exp_lt c₁.2.2.1 c₂.2.2.2 c₁.1 he)]
    rfl
  · subst he
    rw [Int.compare_eq_eq.2 rfl]
    show compare m₁ m₂ = _
    have hp : (0 : ℝ) < (2 : ℝ) ^ e₁ := by positivity
    rcases lt_trichotomy m₁ m₂ with hm | hm | hm
    · rw [Nat.compare_eq_lt.2 hm, compare_lt_iff_lt.2]
      unfold mag; gcongr
    · subst hm; rw [Nat.compare_eq_eq.2 rfl, compare_eq_iff_eq.2 rfl]
    · rw [Nat.compare_eq_gt.2 hm, compare_gt_iff_gt.2]
      unfold mag; gcongr
  · rw [Int.compare_eq_gt.2 he, compare_gt_iff_gt.2 (mag_lt_of_exp_lt c₂.2.2.1 c₁.2.2.2 c₂.1 he)]
    rfl

theorem compare_neg_neg (x y : ℝ) : compare (-x) (-y) = (compare x y).swap := by
  rcases lt_trichotomy x y with h | h | h
  · rw [compare_lt_iff_lt.2 h, compare_gt_iff_gt.2 (neg_lt_neg h)]; rfl
  · rw [h, compare_eq_iff_eq.2 rfl, compare_eq_iff_eq.2 rfl]; rfl
  · rw [compare_gt_iff_gt.2 h, compare_lt_iff_lt.2 (neg_lt_neg h)]; rfl

theorem toReal_finite_positive (m : Nat) (e : Int) (hm : 0 < m) :
    (UnpackedFloat.finite .positive m e hm).toReal = mag m e := by
  simp [toReal, Sign.apply, mag]

theorem toReal_finite_negative (m : Nat) (e : Int) (hm : 0 < m) :
    (UnpackedFloat.finite .negative m e hm).toReal = - mag m e := by
  simp [toReal, Sign.apply, mag]

/-- For finite floats canonical in the same format, `UnpackedFloat.compare` is the real comparison
of exact values. -/
theorem compare_eq_some_compare_toReal {spec : Format} {u v : UnpackedFloat}
    (cu : CanonicalIn spec u) (cv : CanonicalIn spec v)
    (fu : u.isFinite = true) (fv : v.isFinite = true) :
    u.compare v = some (compare u.toReal v.toReal) := by
  cases u with
  | infinity _ => simp [isFinite] at fu
  | notANumber => simp [isFinite] at fu
  | zero s₁ =>
    cases v with
    | infinity _ => simp [isFinite] at fv
    | notANumber => simp [isFinite] at fv
    | zero s₂ =>
      simp only [UnpackedFloat.compare, toReal]
      rw [compare_eq_iff_eq.2 rfl]
    | finite s₂ m₂ e₂ hm₂ =>
      cases s₂
      · rw [toReal_finite_negative]
        simp only [UnpackedFloat.compare, toReal]
        rw [compare_gt_iff_gt.2 (by linarith [mag_pos hm₂ e₂])]
      · rw [toReal_finite_positive]
        simp only [UnpackedFloat.compare, toReal]
        rw [compare_lt_iff_lt.2 (mag_pos hm₂ e₂)]
  | finite s₁ m₁ e₁ hm₁ =>
    cases v with
    | infinity _ => simp [isFinite] at fv
    | notANumber => simp [isFinite] at fv
    | zero s₂ =>
      cases s₁
      · rw [toReal_finite_negative]
        simp only [UnpackedFloat.compare, toReal]
        rw [compare_lt_iff_lt.2 (by linarith [mag_pos hm₁ e₁])]
      · rw [toReal_finite_positive]
        simp only [UnpackedFloat.compare, toReal]
        rw [compare_gt_iff_gt.2 (mag_pos hm₁ e₁)]
    | finite s₂ m₂ e₂ hm₂ =>
      cases s₁ <;> cases s₂
      · rw [toReal_finite_negative, toReal_finite_negative, compare_neg_neg,
          ← lex_eq_compare_mag cu cv]
        rfl
      · rw [toReal_finite_negative, toReal_finite_positive,
          compare_lt_iff_lt.2 (by linarith [mag_pos hm₁ e₁, mag_pos hm₂ e₂])]
        rfl
      · rw [toReal_finite_positive, toReal_finite_negative,
          compare_gt_iff_gt.2 (by linarith [mag_pos hm₁ e₁, mag_pos hm₂ e₂])]
        rfl
      · rw [toReal_finite_positive, toReal_finite_positive,
          ← lex_eq_compare_mag cu cv]
        rfl

/-- `UnpackedFloat.lt` on finite canonical floats is the real order. -/
theorem lt_eq_true_iff {spec : Format} {u v : UnpackedFloat}
    (cu : CanonicalIn spec u) (cv : CanonicalIn spec v)
    (fu : u.isFinite = true) (fv : v.isFinite = true) :
    u.lt v = true ↔ u.toReal < v.toReal := by
  rw [UnpackedFloat.lt, compare_eq_some_compare_toReal cu cv fu fv]
  simp [compare_lt_iff_lt]

/-- `UnpackedFloat.le` on finite canonical floats is the real order. -/
theorem le_eq_true_iff {spec : Format} {u v : UnpackedFloat}
    (cu : CanonicalIn spec u) (cv : CanonicalIn spec v)
    (fu : u.isFinite = true) (fv : v.isFinite = true) :
    u.le v = true ↔ u.toReal ≤ v.toReal := by
  rw [UnpackedFloat.le, compare_eq_some_compare_toReal cu cv fu fv]
  rcases lt_trichotomy u.toReal v.toReal with h | h | h
  · simp [compare_lt_iff_lt.2 h, h.le]
  · simp [h]
  · simp [compare_gt_iff_gt.2 h, h.not_ge]

/-- `UnpackedFloat.beq` on finite canonical floats is equality of exact values. -/
theorem beq_eq_true_iff {spec : Format} {u v : UnpackedFloat}
    (cu : CanonicalIn spec u) (cv : CanonicalIn spec v)
    (fu : u.isFinite = true) (fv : v.isFinite = true) :
    u.beq v = true ↔ u.toReal = v.toReal := by
  rw [UnpackedFloat.beq, compare_eq_some_compare_toReal cu cv fu fv]
  simp

end Float.Model.UnpackedFloat

namespace Float

theorem lt_iff_unpack (a b : Float) : a < b ↔ a.toModel.unpack.lt b.toModel.unpack = true := by
  show a.lt b = true ↔ _
  simp [Float.lt]
  rfl

theorem le_iff_unpack (a b : Float) : a ≤ b ↔ a.toModel.unpack.le b.toModel.unpack = true := by
  show a.le b = true ↔ _
  simp [Float.le]
  rfl

theorem canonicalIn_unpack (a : Float) : CanonicalIn Format.binary64 a.toModel.unpack :=
  (canonical_iff _).1 a.toModel.unpack_canonical

theorem compare_toModel_unpack {a b : Float} (ha : a.IsFinite) (hb : b.IsFinite) :
    a.toModel.unpack.compare b.toModel.unpack = some (compare a.toReal b.toReal) :=
  UnpackedFloat.compare_eq_some_compare_toReal a.canonicalIn_unpack b.canonicalIn_unpack ha hb

/-- `Float`'s `<` (hence the runtime `decLt`) agrees with the exact real order on finite floats. -/
theorem lt_iff_toReal_lt {a b : Float} (ha : a.IsFinite) (hb : b.IsFinite) :
    a < b ↔ a.toReal < b.toReal := by
  rw [lt_iff_unpack]
  exact lt_eq_true_iff a.canonicalIn_unpack b.canonicalIn_unpack ha hb

/-- `Float`'s `≤` (hence the runtime `decLe`) agrees with the exact real order on finite floats. -/
theorem le_iff_toReal_le {a b : Float} (ha : a.IsFinite) (hb : b.IsFinite) :
    a ≤ b ↔ a.toReal ≤ b.toReal := by
  rw [le_iff_unpack]
  exact le_eq_true_iff a.canonicalIn_unpack b.canonicalIn_unpack ha hb

/-- The `Bool`-valued `decide` forms, i.e. what compiled code computes via `lean_float_decLt`. -/
theorem decide_lt_eq {a b : Float} (ha : a.IsFinite) (hb : b.IsFinite) :
    decide (a < b) = decide (a.toReal < b.toReal) := by
  simp [lt_iff_toReal_lt ha hb]

theorem decide_le_eq {a b : Float} (ha : a.IsFinite) (hb : b.IsFinite) :
    decide (a ≤ b) = decide (a.toReal ≤ b.toReal) := by
  simp [le_iff_toReal_le ha hb]

/-- `==` on finite floats is equality of exact values (so `0.0 == -0.0`). -/
theorem beq_iff_toReal_eq {a b : Float} (ha : a.IsFinite) (hb : b.IsFinite) :
    (a == b) = true ↔ a.toReal = b.toReal := by
  show a.toModel.unpack.beq b.toModel.unpack = true ↔ _
  exact beq_eq_true_iff a.canonicalIn_unpack b.canonicalIn_unpack ha hb

end Float
