import FloatModel.Small
import Flight.FloatInstance

/-!
# `Float` facts used by the quadcopter contracts

Saturation (`Flight.clip`) at the `Float` instance is `max lo (min hi x)` with `min`, `max` the
core `minOfLe`, `maxOfLe`, i.e. two comparisons. Every comparison with a NaN is false, so a NaN
input is sent to `lo`, `+∞` to `hi` and `-∞` to `lo`: the result is always finite and in
`[lo, hi]`, whatever `x` is (`clip_spec`). On a finite `x` it is the real clip of `x.toReal`
(`clip_toReal`).
-/

open Float.Model UnpackedFloat

namespace Contracts.QuadFloat

open Flight

/-! ## Order and finiteness -/

theorem isFinite_iff' (x : Float) : x.IsFinite ↔ x.toModel.unpack.isFinite = true := Iff.rfl

/-- A float above a finite float and not above another finite float is finite. -/
theorem isFinite_of_le_of_not_le {lo hi x : Float} (hlo : lo.IsFinite) (hhi : hi.IsFinite)
    (h1 : lo ≤ x) (h2 : ¬ hi ≤ x) : x.IsFinite := by
  rw [Float.le_iff_unpack] at h1 h2
  rw [isFinite_iff'] at hlo hhi ⊢
  generalize lo.toModel.unpack = u at *
  generalize hi.toModel.unpack = w at *
  generalize x.toModel.unpack = y at *
  cases y with
  | notANumber => cases u <;> simp_all [UnpackedFloat.le, UnpackedFloat.compare]
  | infinity s =>
    cases s <;> cases u <;> cases w <;>
      simp_all [UnpackedFloat.le, UnpackedFloat.compare, UnpackedFloat.isFinite]
  | zero _ => rfl
  | finite _ _ _ _ => rfl

/-! ## Saturation -/

theorem min_eq (a b : Float) : min a b = if a ≤ b then a else b := rfl
theorem max_eq (a b : Float) : max a b = if a ≤ b then b else a := rfl

theorem clip_eq (lo hi x : Float) :
    clip lo hi x = (if lo ≤ (if hi ≤ x then hi else x) then (if hi ≤ x then hi else x) else lo) :=
  rfl

/-- The `Float` clip is finite and in `[lo, hi]` for every input, NaN and infinities included. -/
theorem clip_spec {lo hi : Float} (hlo : lo.IsFinite) (hhi : hi.IsFinite)
    (hle : lo.toReal ≤ hi.toReal) (x : Float) :
    (clip lo hi x).IsFinite ∧ lo.toReal ≤ (clip lo hi x).toReal ∧ (clip lo hi x).toReal ≤ hi.toReal := by
  rw [clip_eq]
  by_cases h1 : hi ≤ x
  · simp only [h1, if_true]
    by_cases h2 : lo ≤ hi
    · simp only [h2, if_true]; exact ⟨hhi, hle, le_rfl⟩
    · simp only [h2, if_false]; exact ⟨hlo, le_rfl, hle⟩
  · simp only [h1, if_false]
    by_cases h2 : lo ≤ x
    · simp only [h2, if_true]
      have hx := isFinite_of_le_of_not_le hlo hhi h2 h1
      refine ⟨hx, (Float.le_iff_toReal_le hlo hx).1 h2, ?_⟩
      exact le_of_lt (not_le.1 fun h => h1 ((Float.le_iff_toReal_le hhi hx).2 h))
    · simp only [h2, if_false]; exact ⟨hlo, le_rfl, hle⟩

/-- On a finite input the `Float` clip is the real clip of its value. -/
theorem clip_toReal {lo hi x : Float} (hlo : lo.IsFinite) (hhi : hi.IsFinite)
    (hle : lo.toReal ≤ hi.toReal) (hx : x.IsFinite) :
    (clip lo hi x).toReal = max lo.toReal (min hi.toReal x.toReal) := by
  rw [clip_eq]
  by_cases h1 : hi ≤ x
  · have h1' := (Float.le_iff_toReal_le hhi hx).1 h1
    simp only [h1, if_true, min_eq_left h1']
    by_cases h2 : lo ≤ hi
    · simp only [h2, if_true, max_eq_right hle]
    · exact absurd ((Float.le_iff_toReal_le hlo hhi).2 hle) h2
  · have h1' : x.toReal < hi.toReal := not_le.1 fun h => h1 ((Float.le_iff_toReal_le hhi hx).2 h)
    simp only [h1, if_false, min_eq_right h1'.le]
    by_cases h2 : lo ≤ x
    · simp only [h2, if_true, max_eq_right ((Float.le_iff_toReal_le hlo hx).1 h2)]
    · have h2' : x.toReal < lo.toReal :=
        not_le.1 fun h => h2 ((Float.le_iff_toReal_le hlo hx).2 h)
      simp only [h2, if_false, max_eq_left h2'.le]

/-- The symmetric clip is finite and bounded by its limit. -/
theorem clipSym_spec {lim : Float} (hl : lim.IsFinite) (h0 : 0 ≤ lim.toReal) (x : Float) :
    (clipSym lim x).IsFinite ∧ |(clipSym lim x).toReal| ≤ lim.toReal := by
  have hn : (-lim).IsFinite := (Float.isFinite_neg lim).2 hl
  obtain ⟨hf, h1, h2⟩ := clip_spec hn hl (by rw [Float.toReal_neg]; linarith) x
  rw [Float.toReal_neg] at h1
  exact ⟨hf, abs_le.2 ⟨h1, h2⟩⟩

/-- On a finite input the symmetric clip is the real symmetric clip. -/
theorem clipSym_toReal {lim x : Float} (hl : lim.IsFinite) (h0 : 0 ≤ lim.toReal)
    (hx : x.IsFinite) :
    (clipSym lim x).toReal = max (-lim.toReal) (min lim.toReal x.toReal) := by
  have hn : (-lim).IsFinite := (Float.isFinite_neg lim).2 hl
  have := clip_toReal hn hl (by rw [Float.toReal_neg]; linarith) hx
  rwa [Float.toReal_neg] at this

/-- The symmetric clip leaves a finite value inside the limit unchanged. -/
theorem clipSym_toReal_of_le {lim x : Float} (hl : lim.IsFinite) (h0 : 0 ≤ lim.toReal)
    (hx : x.IsFinite) (hb : |x.toReal| ≤ lim.toReal) :
    (clipSym lim x).toReal = x.toReal := by
  rw [clipSym_toReal hl h0 hx, min_eq_right (abs_le.1 hb).2, max_eq_right (abs_le.1 hb).1]

/-! ## Literals -/

theorem zero_isFinite : (0 : Float).IsFinite := Float.isFinite_zero
theorem one_isFinite : (1 : Float).IsFinite := Float.isFinite_one


/-! ## Exact operations with a zero operand

A finite float of value `0` is `+0` or `-0`. Adding or subtracting it, multiplying by it, and
dividing it by a nonzero finite float are exact (the model's zero cases), which is what keeps the
horizontal and attitude channels of the hover exactly at zero. -/

namespace Zero

open Float.Model UnpackedFloat

theorem canon_zero (s : Sign) : Canonical (.zero s) := trivial

theorem zero_iff {x : Float} : (x.IsFinite ∧ x.toReal = 0) ↔ ∃ s, x.toModel.unpack = .zero s := by
  constructor
  · rintro ⟨hf, h0⟩
    rw [isFinite_iff'] at hf
    rw [Float.toReal] at h0
    revert hf h0
    cases x.toModel.unpack with
    | zero s => intro _ _; exact ⟨s, rfl⟩
    | finite s m e hm =>
      intro _ h0
      rw [toReal_finite] at h0
      have : 0 < mag m e := mag_pos hm e
      cases s <;> simp [Sign.toReal] at h0 <;> linarith
    | infinity _ => intro hf; simp [UnpackedFloat.isFinite] at hf
    | notANumber => intro hf; simp [UnpackedFloat.isFinite] at hf
  · rintro ⟨s, hs⟩
    refine ⟨?_, ?_⟩
    · rw [isFinite_iff', hs]; rfl
    · rw [Float.toReal, hs]; rfl

theorem of_unpack {x : Float} {r : UnpackedFloat} (h : x.toModel = Float.Model.pack r)
    (hc : r.Canonical) : x.toModel.unpack = r := by
  rw [h]; exact Float.Model.unpack_pack_of_canonical hc

/-- An unpacked float that is one of the two zeros. -/
def IsZeroU (r : UnpackedFloat) : Prop := ∃ s, r = .zero s

theorem isZeroU_ite (c : Prop) [Decidable c] (s₁ s₂ : Sign) :
    IsZeroU (if c then .zero s₁ else .zero s₂) := by
  split
  · exact ⟨_, rfl⟩
  · exact ⟨_, rfl⟩

/-- A float whose unpacked form is the canonical `r` is finite with value `r.toReal` when `r` is
finite. -/
theorem of_pack {x : Float} {r : UnpackedFloat} (h : x.toModel = Float.Model.pack r)
    (hc : r.Canonical) (hf : r.isFinite = true) : x.IsFinite ∧ x.toReal = r.toReal := by
  have hu := of_unpack h hc
  exact ⟨by rw [isFinite_iff', hu]; exact hf, by rw [Float.toReal, hu]⟩

theorem of_pack_zero {x : Float} {r : UnpackedFloat} (h : x.toModel = Float.Model.pack r)
    (hz : IsZeroU r) : x.IsFinite ∧ x.toReal = 0 := by
  obtain ⟨s, rfl⟩ := hz
  exact of_pack h trivial rfl

theorem unpack_of_zero {x : Float} (hx : x.IsFinite) (h0 : x.toReal = 0) :
    IsZeroU x.toModel.unpack := zero_iff.1 ⟨hx, h0⟩

/-- The four shapes of a finite float. -/
theorem finite_cases {x : Float} (hx : x.IsFinite) :
    IsZeroU x.toModel.unpack ∨ ∃ s m e hm, x.toModel.unpack = .finite s m e hm := by
  rw [isFinite_iff'] at hx
  revert hx
  cases x.toModel.unpack with
  | zero s => intro _; exact Or.inl ⟨s, rfl⟩
  | finite s m e hm => intro _; exact Or.inr ⟨s, m, e, hm, rfl⟩
  | infinity _ => intro h; simp [UnpackedFloat.isFinite] at h
  | notANumber => intro h; simp [UnpackedFloat.isFinite] at h

/-- `a + b` with `b` a zero is `a` in value. -/
theorem add_zero_right {a b : Float} (ha : a.IsFinite) (hb : b.IsFinite) (hb0 : b.toReal = 0) :
    (a + b).IsFinite ∧ (a + b).toReal = a.toReal := by
  obtain ⟨s, hs⟩ := unpack_of_zero hb hb0
  have e : (a + b).toModel =
      Float.Model.pack (UnpackedFloat.add Format.binary64 a.toModel.unpack b.toModel.unpack) := rfl
  rw [hs] at e
  rcases finite_cases ha with ⟨s₁, hz⟩ | ⟨s₁, m, e₁, hm, hf⟩
  · rw [hz] at e
    have h0 : a.toReal = 0 := by rw [Float.toReal, hz]; rfl
    rw [h0]
    refine of_pack_zero e ?_
    simp only [UnpackedFloat.add]; exact isZeroU_ite _ _ _
  · rw [hf] at e
    have hc := a.toModel.unpack_canonical
    rw [hf] at hc
    have := of_pack e hc rfl
    refine ⟨this.1, this.2.trans ?_⟩
    rw [Float.toReal, hf]; rfl

/-- `a + b` with `a` a zero is `b` in value. -/
theorem add_zero_left {a b : Float} (ha : a.IsFinite) (hb : b.IsFinite) (ha0 : a.toReal = 0) :
    (a + b).IsFinite ∧ (a + b).toReal = b.toReal := by
  obtain ⟨s, hs⟩ := unpack_of_zero ha ha0
  have e : (a + b).toModel =
      Float.Model.pack (UnpackedFloat.add Format.binary64 a.toModel.unpack b.toModel.unpack) := rfl
  rw [hs] at e
  rcases finite_cases hb with ⟨s₁, hz⟩ | ⟨s₁, m, e₁, hm, hf⟩
  · rw [hz] at e
    have h0 : b.toReal = 0 := by rw [Float.toReal, hz]; rfl
    rw [h0]
    refine of_pack_zero e ?_
    simp only [UnpackedFloat.add]; exact isZeroU_ite _ _ _
  · rw [hf] at e
    have hc := b.toModel.unpack_canonical
    rw [hf] at hc
    have := of_pack e hc rfl
    refine ⟨this.1, this.2.trans ?_⟩
    rw [Float.toReal, hf]; rfl

/-- `a - b` with `b` a zero is `a` in value. -/
theorem sub_zero_right {a b : Float} (ha : a.IsFinite) (hb : b.IsFinite) (hb0 : b.toReal = 0) :
    (a - b).IsFinite ∧ (a - b).toReal = a.toReal := by
  obtain ⟨s, hs⟩ := unpack_of_zero hb hb0
  have e : (a - b).toModel =
      Float.Model.pack (UnpackedFloat.sub Format.binary64 a.toModel.unpack b.toModel.unpack) := rfl
  rw [hs] at e
  rcases finite_cases ha with ⟨s₁, hz⟩ | ⟨s₁, m, e₁, hm, hf⟩
  · rw [hz] at e
    have h0 : a.toReal = 0 := by rw [Float.toReal, hz]; rfl
    rw [h0]
    refine of_pack_zero e ?_
    simp only [UnpackedFloat.sub]; exact isZeroU_ite _ _ _
  · rw [hf] at e
    have hc := a.toModel.unpack_canonical
    rw [hf] at hc
    have := of_pack e hc rfl
    refine ⟨this.1, this.2.trans ?_⟩
    rw [Float.toReal, hf]; rfl

/-- `a - b` with `a` a zero is `-b` in value. -/
theorem sub_zero_left {a b : Float} (ha : a.IsFinite) (hb : b.IsFinite) (ha0 : a.toReal = 0) :
    (a - b).IsFinite ∧ (a - b).toReal = - b.toReal := by
  obtain ⟨s, hs⟩ := unpack_of_zero ha ha0
  have e : (a - b).toModel =
      Float.Model.pack (UnpackedFloat.sub Format.binary64 a.toModel.unpack b.toModel.unpack) := rfl
  rw [hs] at e
  rcases finite_cases hb with ⟨s₁, hz⟩ | ⟨s₁, m, e₁, hm, hf⟩
  · rw [hz] at e
    have h0 : b.toReal = 0 := by rw [Float.toReal, hz]; rfl
    rw [h0, neg_zero]
    refine of_pack_zero e ?_
    simp only [UnpackedFloat.sub]; exact isZeroU_ite _ _ _
  · rw [hf] at e
    have hc := b.toModel.unpack_canonical
    rw [hf] at hc
    have := of_pack e (r := .finite (-s₁) m e₁ hm) (by simpa [Canonical] using hc) rfl
    refine ⟨this.1, this.2.trans ?_⟩
    rw [Float.toReal, hf]
    cases s₁ <;> simp [UnpackedFloat.toReal, Sign.apply]

/-- A product with a zero factor is a zero. -/
theorem mul_zero_right {a b : Float} (ha : a.IsFinite) (hb : b.IsFinite) (hb0 : b.toReal = 0) :
    (a * b).IsFinite ∧ (a * b).toReal = 0 := by
  obtain ⟨s, hs⟩ := unpack_of_zero hb hb0
  have e : (a * b).toModel =
      Float.Model.pack (UnpackedFloat.mul Format.binary64 a.toModel.unpack b.toModel.unpack) := rfl
  rw [hs] at e
  rcases finite_cases ha with ⟨s₁, hz⟩ | ⟨s₁, m, e₁, hm, hf⟩
  · rw [hz] at e; exact of_pack_zero e ⟨_, rfl⟩
  · rw [hf] at e; exact of_pack_zero e ⟨_, rfl⟩

theorem mul_zero_left {a b : Float} (ha : a.IsFinite) (hb : b.IsFinite) (ha0 : a.toReal = 0) :
    (a * b).IsFinite ∧ (a * b).toReal = 0 := by
  obtain ⟨s, hs⟩ := unpack_of_zero ha ha0
  have e : (a * b).toModel =
      Float.Model.pack (UnpackedFloat.mul Format.binary64 a.toModel.unpack b.toModel.unpack) := rfl
  rw [hs] at e
  rcases finite_cases hb with ⟨s₁, hz⟩ | ⟨s₁, m, e₁, hm, hf⟩
  · rw [hz] at e; exact of_pack_zero e ⟨_, rfl⟩
  · rw [hf] at e; exact of_pack_zero e ⟨_, rfl⟩

/-- A zero divided by a nonzero finite float is a zero. -/
theorem div_zero_left {a b : Float} (ha : a.IsFinite) (hb : b.IsFinite) (ha0 : a.toReal = 0)
    (hb0 : b.toReal ≠ 0) : (a / b).IsFinite ∧ (a / b).toReal = 0 := by
  obtain ⟨s, hs⟩ := unpack_of_zero ha ha0
  have e : (a / b).toModel =
      Float.Model.pack (UnpackedFloat.div Format.binary64 a.toModel.unpack b.toModel.unpack) := rfl
  rw [hs] at e
  rcases finite_cases hb with ⟨s₁, hz⟩ | ⟨s₁, m, e₁, hm, hf⟩
  · exact absurd (by rw [Float.toReal, hz]; rfl) hb0
  · rw [hf] at e; exact of_pack_zero e ⟨_, rfl⟩

/-- Negation of a zero is a zero. -/
theorem neg_zero' {a : Float} (ha : a.IsFinite) (ha0 : a.toReal = 0) :
    (-a).IsFinite ∧ (-a).toReal = 0 :=
  ⟨(Float.isFinite_neg a).2 ha, by rw [Float.toReal_neg, ha0, neg_zero]⟩

end Zero

end Contracts.QuadFloat
