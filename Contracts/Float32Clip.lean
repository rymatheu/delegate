import FloatModel.Float32

/-!
# The `Float32` clip and ArduPilot's `constrain_float`

C++ source: `libraries/AP_Math/AP_Math.cpp:283-305` (`constrain_value_line<float>`), which the
`constrain_float` macro (`AP_Math.h:178`) calls with `float` arguments. Left out: the internal-error
report on a NaN input (`AP::internalerror().error(...)`, `AP_Math.cpp:289-291`, under
`AP_INTERNALERROR_ENABLED`), which does not affect the returned value, and the `line` argument it
reports.

`clip lo hi x = max lo (min hi x)` with the core `minOfLe`/`maxOfLe` is two comparisons; every
comparison with a NaN is false, so the result is finite and in `[lo, hi]` for every input
(`clip_spec`), and on a finite input it is the real clip (`clip_toReal`).

`constrain_float` returns the binary32 midpoint `(low + high) / 2` on a NaN and clamps otherwise.
The clamp branches are finite and in `[low, high]` for every non-NaN input
(`constrain_float_spec_of_not_isNaN`). The midpoint is in `[low, high]` because rounding never
crosses a float (`Float32.add_bracket`, `div_bracket`): `2 low ≤ fl(low + high) ≤ 2 high`, then
`low ≤ fl(fl(low + high) / 2) ≤ high` (`midpoint_spec`). This needs `low + high` not to overflow
(`|low + high| ≤ maxFinite32`); without it the statement is false: with `low = high` the largest
finite float, `low + high` rounds to `+∞` and a NaN input returns `+∞`
(`constrain_float_nan_overflow`). With that hypothesis the result is finite and in `[low, high]`
for every input, NaN and infinities included (`constrain_float_spec`).
-/

open Float.Model UnpackedFloat

namespace Contracts.Float32Clip

/-- The saturation `max lo (min hi x)` at `Float32`. -/
def clip (lo hi x : Float32) : Float32 := max lo (min hi x)

/-- ArduPilot's `constrain_float(amt, low, high)` (`constrain_value_line<float>`,
`AP_Math.cpp:283-305`). -/
def constrain_float (amt low high : Float32) : Float32 :=
  if amt.isNaN then (low + high) / 2
  else if amt < low then low
  else if amt > high then high
  else amt

/-! ## Order and finiteness -/

theorem isNaN_iff (x : Float32) : x.isNaN = true ↔ x.toModel.unpack.isNaN = true := Iff.rfl

/-- A float above a finite float and not above another finite float is finite. -/
theorem isFinite_of_le_of_not_le {lo hi x : Float32} (hlo : lo.IsFinite) (hhi : hi.IsFinite)
    (h1 : lo ≤ x) (h2 : ¬ hi ≤ x) : x.IsFinite := by
  rw [Float32.le_iff_unpack] at h1 h2
  rw [Float32.isFinite_iff] at hlo hhi ⊢
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

/-- A non-NaN float neither below a finite float nor above another finite float is finite. -/
theorem isFinite_of_not_lt_of_not_lt {lo hi x : Float32} (hlo : lo.IsFinite) (hhi : hi.IsFinite)
    (hn : ¬ x.isNaN = true) (h1 : ¬ x < lo) (h2 : ¬ hi < x) : x.IsFinite := by
  rw [Float32.lt_iff_unpack] at h1 h2
  rw [isNaN_iff] at hn
  rw [Float32.isFinite_iff] at hlo hhi ⊢
  generalize lo.toModel.unpack = u at *
  generalize hi.toModel.unpack = w at *
  generalize x.toModel.unpack = y at *
  cases y with
  | notANumber => simp [UnpackedFloat.isNaN] at hn
  | infinity s =>
    cases s <;> cases u <;> cases w <;>
      simp_all [UnpackedFloat.lt, UnpackedFloat.compare, UnpackedFloat.isFinite]
  | zero _ => rfl
  | finite _ _ _ _ => rfl

theorem not_isNaN_of_isFinite {x : Float32} (hx : x.IsFinite) : ¬ x.isNaN = true := by
  rw [isNaN_iff]; rw [Float32.isFinite_iff] at hx
  cases h : x.toModel.unpack <;> simp_all [UnpackedFloat.isNaN, UnpackedFloat.isFinite]

/-! ## The clip -/

theorem clip_eq (lo hi x : Float32) :
    clip lo hi x = (if lo ≤ (if hi ≤ x then hi else x) then (if hi ≤ x then hi else x) else lo) :=
  rfl

/-- The `Float32` clip is finite and in `[lo, hi]` for every input, NaN and infinities
included. -/
theorem clip_spec {lo hi : Float32} (hlo : lo.IsFinite) (hhi : hi.IsFinite)
    (hle : lo.toReal ≤ hi.toReal) (x : Float32) :
    (clip lo hi x).IsFinite ∧ lo.toReal ≤ (clip lo hi x).toReal ∧
      (clip lo hi x).toReal ≤ hi.toReal := by
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
      refine ⟨hx, (Float32.le_iff_toReal_le hlo hx).1 h2, ?_⟩
      exact le_of_lt (not_le.1 fun h => h1 ((Float32.le_iff_toReal_le hhi hx).2 h))
    · simp only [h2, if_false]; exact ⟨hlo, le_rfl, hle⟩

/-- On a finite input the `Float32` clip is the real clip of its value. -/
theorem clip_toReal {lo hi x : Float32} (hlo : lo.IsFinite) (hhi : hi.IsFinite)
    (hle : lo.toReal ≤ hi.toReal) (hx : x.IsFinite) :
    (clip lo hi x).toReal = max lo.toReal (min hi.toReal x.toReal) := by
  rw [clip_eq]
  by_cases h1 : hi ≤ x
  · have h1' := (Float32.le_iff_toReal_le hhi hx).1 h1
    simp only [h1, if_true, min_eq_left h1']
    by_cases h2 : lo ≤ hi
    · simp only [h2, if_true, max_eq_right hle]
    · exact absurd ((Float32.le_iff_toReal_le hlo hhi).2 hle) h2
  · have h1' : x.toReal < hi.toReal :=
      not_le.1 fun h => h1 ((Float32.le_iff_toReal_le hhi hx).2 h)
    simp only [h1, if_false, min_eq_right h1'.le]
    by_cases h2 : lo ≤ x
    · simp only [h2, if_true, max_eq_right ((Float32.le_iff_toReal_le hlo hx).1 h2)]
    · have h2' : x.toReal < lo.toReal :=
        not_le.1 fun h => h2 ((Float32.le_iff_toReal_le hlo hx).2 h)
      simp only [h2, if_false, max_eq_left h2'.le]

/-! ## The binary32 midpoint -/

theorem toModel_unpack_two :
    (2 : Float32).toModel.unpack = .finite .positive (2 ^ 23) (-22) (by decide) := rfl

theorem isFinite_two : (2 : Float32).IsFinite := by
  simp [Float32.isFinite_iff, toModel_unpack_two, UnpackedFloat.isFinite]

theorem toReal_two : (2 : Float32).toReal = 2 := by
  rw [Float32.toReal, toModel_unpack_two]
  simp [UnpackedFloat.toReal, Sign.apply]
  norm_num

/-- The binary32 midpoint `(lo + hi) / 2` of finite `lo ≤ hi` whose sum does not overflow is finite
and in `[lo, hi]`. -/
theorem midpoint_spec {lo hi : Float32} (hlo : lo.IsFinite) (hhi : hi.IsFinite)
    (hle : lo.toReal ≤ hi.toReal) (hsum : |lo.toReal + hi.toReal| ≤ maxFinite32) :
    ((lo + hi) / 2).IsFinite ∧ lo.toReal ≤ ((lo + hi) / 2).toReal ∧
      ((lo + hi) / 2).toReal ≤ hi.toReal := by
  obtain ⟨hs, -⟩ := Float32.add_err_all hlo hhi hsum
  have hsM := Float32.abs_toReal_le_maxFinite (lo + hi)
  have hsum' := abs_le.1 hsum
  have hsM' := abs_le.1 hsM
  -- `2 lo ≤ fl(lo + hi) ≤ 2 hi`
  have hs_lo : 2 * lo.toReal ≤ (lo + hi).toReal := by
    by_cases h : |2 * lo.toReal| ≤ maxFinite32
    · obtain ⟨d, hd, hdv⟩ := Float32.exists_double hlo h
      have := (Float32.add_bracket hlo hhi hsum hd).1 (by rw [hdv]; linarith)
      rwa [hdv] at this
    · rcases lt_abs.1 (not_le.1 h) with h | h <;> linarith
  have hs_hi : (lo + hi).toReal ≤ 2 * hi.toReal := by
    by_cases h : |2 * hi.toReal| ≤ maxFinite32
    · obtain ⟨d, hd, hdv⟩ := Float32.exists_double hhi h
      have := (Float32.add_bracket hlo hhi hsum hd).2 (by rw [hdv]; linarith)
      rwa [hdv] at this
    · rcases lt_abs.1 (not_le.1 h) with h | h <;> linarith
  -- the division by two
  have h20 : (2 : Float32).toReal ≠ 0 := by rw [toReal_two]; norm_num
  have hq : |(lo + hi).toReal / (2 : Float32).toReal| ≤ maxFinite32 := by
    rw [toReal_two, abs_div, abs_two]
    have := Float32.one_le_maxFinite32
    have := abs_nonneg (lo + hi).toReal
    linarith
  obtain ⟨ht, -⟩ := Float32.div_err_all hs isFinite_two h20 hq
  have h1 := (Float32.div_bracket hs isFinite_two h20 hq hlo).1 (by rw [toReal_two]; linarith)
  have h2 := (Float32.div_bracket hs isFinite_two h20 hq hhi).2 (by rw [toReal_two]; linarith)
  exact ⟨ht, h1, h2⟩

/-! ## `constrain_float` -/

/-- On a non-NaN input, `constrain_float` is finite and in `[low, high]` (no overflow hypothesis
needed: the midpoint is not computed). -/
theorem constrain_float_spec_of_not_isNaN {lo hi : Float32} (hlo : lo.IsFinite) (hhi : hi.IsFinite)
    (hle : lo.toReal ≤ hi.toReal) {x : Float32} (hn : ¬ x.isNaN = true) :
    (constrain_float x lo hi).IsFinite ∧ lo.toReal ≤ (constrain_float x lo hi).toReal ∧
      (constrain_float x lo hi).toReal ≤ hi.toReal := by
  unfold constrain_float
  rw [if_neg hn]
  split_ifs with h1 h2
  · exact ⟨hlo, le_rfl, hle⟩
  · exact ⟨hhi, hle, le_rfl⟩
  · have hx := isFinite_of_not_lt_of_not_lt hlo hhi hn h1 h2
    refine ⟨hx, ?_, ?_⟩
    · exact not_lt.1 fun h => h1 ((Float32.lt_iff_toReal_lt hx hlo).2 h)
    · exact not_lt.1 fun h => h2 ((Float32.lt_iff_toReal_lt hhi hx).2 h)

/-- **`constrain_float` is finite and in `[low, high]` for every input**, NaN and infinities
included, for finite `low ≤ high` whose sum does not overflow. -/
theorem constrain_float_spec {lo hi : Float32} (hlo : lo.IsFinite) (hhi : hi.IsFinite)
    (hle : lo.toReal ≤ hi.toReal) (hsum : |lo.toReal + hi.toReal| ≤ maxFinite32) (x : Float32) :
    (constrain_float x lo hi).IsFinite ∧ lo.toReal ≤ (constrain_float x lo hi).toReal ∧
      (constrain_float x lo hi).toReal ≤ hi.toReal := by
  by_cases hn : x.isNaN = true
  · unfold constrain_float
    rw [if_pos hn]
    exact midpoint_spec hlo hhi hle hsum
  · exact constrain_float_spec_of_not_isNaN hlo hhi hle hn

/-- On a finite input, `constrain_float` is the real clamp of its value. -/
theorem constrain_float_toReal {lo hi x : Float32} (hlo : lo.IsFinite) (hhi : hi.IsFinite)
    (hle : lo.toReal ≤ hi.toReal) (hx : x.IsFinite) :
    (constrain_float x lo hi).toReal = max lo.toReal (min hi.toReal x.toReal) := by
  unfold constrain_float
  rw [if_neg (not_isNaN_of_isFinite hx)]
  split_ifs with h1 h2
  · have h1' := (Float32.lt_iff_toReal_lt hx hlo).1 h1
    rw [min_eq_right (by linarith), max_eq_left h1'.le]
  · have h2' := (Float32.lt_iff_toReal_lt hhi hx).1 h2
    rw [min_eq_left h2'.le, max_eq_right hle]
  · have h1' := not_lt.1 fun h => h1 ((Float32.lt_iff_toReal_lt hx hlo).2 h)
    have h2' := not_lt.1 fun h => h2 ((Float32.lt_iff_toReal_lt hhi hx).2 h)
    rw [min_eq_right h2', max_eq_right h1']

/-- On a non-NaN input, `constrain_float` and the clip agree in value. -/
theorem constrain_float_eq_clip {lo hi x : Float32} (hlo : lo.IsFinite) (hhi : hi.IsFinite)
    (hle : lo.toReal ≤ hi.toReal) (hx : x.IsFinite) :
    (constrain_float x lo hi).toReal = (clip lo hi x).toReal := by
  rw [constrain_float_toReal hlo hhi hle hx, clip_toReal hlo hhi hle hx]

/-! ## The overflow hypothesis is needed -/

/-- The largest finite binary32 float, `0x7F7FFFFF`. -/
def maxFloat32 : Float32 := Float32.ofBits 0x7F7FFFFF

/-- With `low = high` the largest finite float, a NaN input gives `+∞`: `low + high` overflows. -/
theorem constrain_float_nan_overflow :
    ¬ (constrain_float ((0 : Float32) / 0) maxFloat32 maxFloat32).IsFinite := by
  decide

end Contracts.Float32Clip
