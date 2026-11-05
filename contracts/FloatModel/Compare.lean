module

/-
Comparisons with NaN and the infinities, the midpoint `(lo + hi) / 2`, and the NaN-safe clamp as
the translator emits it (ArduPilot's `constrain_value_line`), for `Float32` and `Float`.

The rounding layer (`FloatModel.Float32`, `Small`, `DivSqrt`, `Bracket`) speaks of finite floats.
The translated code also compares possibly non-finite values (a NaN or infinite sample), and its
clamps are what keep such values out of the state. This file gives the facts for that:

* `isNaN_iff`, `trichotomy`: every float is finite, NaN, `+∞` or `-∞`;
* `not_lt_of_isNaN_left` etc.: every comparison with a NaN is false;
* `between_of_not_lt_of_not_gt`: a non-NaN value that is neither below a finite `lo` nor above a
  finite `hi` is finite and between them;
* `mid_between`: `(lo + hi) / 2` of two finite floats lies between them (no overflow assumed below
  `maxFinite / 2`);
* `cvl`: the clamp `if isNaN a then (lo + hi) / 2 else if a < lo then lo else if a > hi then hi
  else a`, with `cvl_between` (always finite, between `lo` and `hi`), `cvl_of_between` (identity
  on `[lo, hi]`), `cvl_mem` (in any interval containing `lo` and `hi`).
-/
public import FloatModel.Float32

@[expose] public section

open Float.Model UnpackedFloat

namespace Float32

/-! ## Finite, NaN, or infinite -/

theorem isNaN_iff (x : Float32) : x.isNaN = true ↔ x.toModel.unpack = .notANumber := by
  show x.toModel.unpack.isNaN = true ↔ _
  cases x.toModel.unpack <;> simp [UnpackedFloat.isNaN]

theorem trichotomy (x : Float32) :
    x.IsFinite ∨ x.isNaN = true ∨ x.toModel.unpack = .infinity .positive ∨
      x.toModel.unpack = .infinity .negative := by
  rw [isNaN_iff, isFinite_iff]
  rcases x.toModel.unpack with (s | _ | s | ⟨s, m, e, h⟩)
  · cases s <;> simp
  · simp
  · simp [UnpackedFloat.isFinite]
  · simp [UnpackedFloat.isFinite]

theorem not_isNaN_of_isFinite {x : Float32} (h : x.IsFinite) : x.isNaN = false := by
  rw [isFinite_iff] at h
  show x.toModel.unpack.isNaN = false
  revert h; cases x.toModel.unpack <;> simp [UnpackedFloat.isNaN, UnpackedFloat.isFinite]

/-! ## Comparisons with NaN are false -/

theorem not_lt_of_isNaN_left {a b : Float32} (ha : a.isNaN = true) : ¬ a < b := by
  rw [lt_iff_unpack, (isNaN_iff a).1 ha]; simp [UnpackedFloat.lt, UnpackedFloat.compare]

theorem not_lt_of_isNaN_right {a b : Float32} (hb : b.isNaN = true) : ¬ a < b := by
  rw [lt_iff_unpack, (isNaN_iff b).1 hb]
  cases a.toModel.unpack <;> simp [UnpackedFloat.lt, UnpackedFloat.compare]

theorem not_le_of_isNaN_left {a b : Float32} (ha : a.isNaN = true) : ¬ a ≤ b := by
  rw [le_iff_unpack, (isNaN_iff a).1 ha]; simp [UnpackedFloat.le, UnpackedFloat.compare]

theorem not_le_of_isNaN_right {a b : Float32} (hb : b.isNaN = true) : ¬ a ≤ b := by
  rw [le_iff_unpack, (isNaN_iff b).1 hb]
  cases a.toModel.unpack <;> simp [UnpackedFloat.le, UnpackedFloat.compare]

/-! ## Comparisons with the infinities -/

theorem lt_of_unpack_inf_neg {a b : Float32} (ha : a.toModel.unpack = .infinity .negative)
    (hb : b.IsFinite) : a < b := by
  rw [isFinite_iff] at hb
  rw [lt_iff_unpack, ha]
  revert hb; cases b.toModel.unpack <;> simp [UnpackedFloat.lt, UnpackedFloat.compare,
    UnpackedFloat.isFinite]

theorem lt_of_unpack_inf_pos {a b : Float32} (ha : a.toModel.unpack = .infinity .positive)
    (hb : b.IsFinite) : b < a := by
  rw [isFinite_iff] at hb
  rw [lt_iff_unpack, ha]
  revert hb; rcases b.toModel.unpack with (s | _ | s | ⟨s, m, e, h⟩) <;>
    simp [UnpackedFloat.lt, UnpackedFloat.compare, UnpackedFloat.isFinite]

/-- A non-NaN float that is not below a finite `lo` and not above a finite `hi` is finite and
between them. -/
theorem between_of_not_lt_of_not_gt {a lo hi : Float32} (ha : a.isNaN = false)
    (hlo : lo.IsFinite) (hhi : hi.IsFinite) (h1 : ¬ a < lo) (h2 : ¬ hi < a) :
    a.IsFinite ∧ lo.toReal ≤ a.toReal ∧ a.toReal ≤ hi.toReal := by
  rcases trichotomy a with hf | hn | hp | hm
  · refine ⟨hf, ?_, ?_⟩
    · rw [lt_iff_toReal_lt hf hlo] at h1; exact not_lt.1 h1
    · rw [lt_iff_toReal_lt hhi hf] at h2; exact not_lt.1 h2
  · rw [ha] at hn; exact absurd hn (by decide)
  · exact absurd (lt_of_unpack_inf_pos hp hhi) h2
  · exact absurd (lt_of_unpack_inf_neg hm hlo) h1

/-! ## Literals -/

/-- The literal `Int32.toFloat32 2` of the translated midpoint is the finite float `2`. Its proof
(`FloatModel.Lit.two32`) evaluates the literal, which needs the bodies of core's conversions: they
are not exposed to modules, so it lives in a plain file and the lemmas below take it as an
argument. -/
def Two32 : Prop := (Int32.toFloat32 (2 : Int32)).IsFinite ∧ (Int32.toFloat32 (2 : Int32)).toReal = 2

/-! ## The midpoint -/

/-- A sum of two finite floats lies between their doubles. -/
theorem add_between {a b : Float32} (ha : a.IsFinite) (hb : b.IsFinite)
    (ha2 : |a.toReal| ≤ maxFinite32 / 2) (hb2 : |b.toReal| ≤ maxFinite32 / 2)
    (hab : a.toReal ≤ b.toReal) :
    (a + b).IsFinite ∧ 2 * a.toReal ≤ (a + b).toReal ∧ (a + b).toReal ≤ 2 * b.toReal := by
  have hs : |a.toReal + b.toReal| ≤ maxFinite32 := by
    have := abs_add_le a.toReal b.toReal; linarith
  obtain ⟨da, hda, hda'⟩ := exists_double ha (by rw [abs_mul]; norm_num; linarith)
  obtain ⟨db, hdb, hdb'⟩ := exists_double hb (by rw [abs_mul]; norm_num; linarith)
  refine ⟨(add_err_all ha hb hs).1, ?_, ?_⟩
  · rw [← hda']; exact (add_bracket ha hb hs hda).1 (by rw [hda']; linarith)
  · rw [← hdb']; exact (add_bracket ha hb hs hdb).2 (by rw [hdb']; linarith)

/-- The midpoint `(a + b) / 2` of two finite floats (below `maxFinite32 / 2`) is finite and lies
between them, in either order. -/
theorem mid_between (two : Two32) {a b : Float32} (ha : a.IsFinite) (hb : b.IsFinite)
    (ha2 : |a.toReal| ≤ maxFinite32 / 2) (hb2 : |b.toReal| ≤ maxFinite32 / 2) :
    ((a + b) / Int32.toFloat32 2).IsFinite ∧
      min a.toReal b.toReal ≤ ((a + b) / Int32.toFloat32 2).toReal ∧
      ((a + b) / Int32.toFloat32 2).toReal ≤ max a.toReal b.toReal := by
  have hs : |a.toReal + b.toReal| ≤ maxFinite32 := by
    have := abs_add_le a.toReal b.toReal; linarith
  have hsf := (add_err_all ha hb hs).1
  have hS : |(a + b).toReal| ≤ maxFinite32 := abs_toReal_le_maxFinite _
  have h2 := two.1
  have h2r := two.2
  have hq : |(a + b).toReal / (Int32.toFloat32 2).toReal| ≤ maxFinite32 := by
    rw [h2r, abs_div]; norm_num; linarith [abs_nonneg (a + b).toReal]
  have h20 : (Int32.toFloat32 2).toReal ≠ 0 := by rw [h2r]; norm_num
  refine ⟨(div_err_all hsf h2 h20 hq).1, ?_, ?_⟩
  · -- lower bound: the smaller of `a`, `b`
    rcases le_total a.toReal b.toReal with hab | hab
    · rw [min_eq_left hab]
      have := (add_between ha hb ha2 hb2 hab).2.1
      exact (div_bracket hsf h2 h20 hq ha).1 (by rw [h2r]; linarith)
    · rw [min_eq_right hab]
      obtain ⟨_, h1, _⟩ := add_between hb ha hb2 ha2 hab
      -- `b + a` and `a + b` have the same exact value; reason on the exact sum directly
      have hlow : 2 * b.toReal ≤ (a + b).toReal := by
        obtain ⟨db, hdb, hdb'⟩ := exists_double hb (by rw [abs_mul]; norm_num; linarith)
        rw [← hdb']; exact (add_bracket ha hb hs hdb).1 (by rw [hdb']; linarith)
      exact (div_bracket hsf h2 h20 hq hb).1 (by rw [h2r]; linarith)
  · rcases le_total a.toReal b.toReal with hab | hab
    · rw [max_eq_right hab]
      have := (add_between ha hb ha2 hb2 hab).2.2
      exact (div_bracket hsf h2 h20 hq hb).2 (by rw [h2r]; linarith)
    · rw [max_eq_left hab]
      have hup : (a + b).toReal ≤ 2 * a.toReal := by
        obtain ⟨da, hda, hda'⟩ := exists_double ha (by rw [abs_mul]; norm_num; linarith)
        rw [← hda']; exact (add_bracket ha hb hs hda).2 (by rw [hda']; linarith)
      exact (div_bracket hsf h2 h20 hq ha).2 (by rw [h2r]; linarith)

/-! ## The NaN-safe clamp (`constrain_value_line`) -/

/-- ArduPilot's `constrain_value_line(amt, low, high)` (`AP_Math/AP_Math.cpp:283-304`) on floats,
as the translator emits it: NaN goes to the midpoint, then the two comparisons. -/
def cvl (amt lo hi : Float32) : Float32 :=
  if amt.isNaN then (lo + hi) / Int32.toFloat32 2
  else if amt < lo then lo else if amt > hi then hi else amt

/-- **The clamp is always finite and between its bounds**, whatever `amt` is (NaN, `±∞`
included), for finite bounds below `maxFinite32 / 2` (given in either order). -/
theorem cvl_between (two : Two32) {amt lo hi : Float32} (hlo : lo.IsFinite) (hhi : hi.IsFinite)
    (hlo2 : |lo.toReal| ≤ maxFinite32 / 2) (hhi2 : |hi.toReal| ≤ maxFinite32 / 2) :
    (cvl amt lo hi).IsFinite ∧ min lo.toReal hi.toReal ≤ (cvl amt lo hi).toReal ∧
      (cvl amt lo hi).toReal ≤ max lo.toReal hi.toReal := by
  unfold cvl
  by_cases hn : amt.isNaN = true
  · rw [ite_eq_left hn]; exact mid_between two hlo hhi hlo2 hhi2
  · rw [ite_eq_right hn]
    have hn' : amt.isNaN = false := by simpa using hn
    by_cases h1 : amt < lo
    · rw [ite_eq_left h1]; exact ⟨hlo, min_le_left _ _, le_max_left _ _⟩
    · rw [ite_eq_right h1]
      by_cases h2 : amt > hi
      · rw [ite_eq_left h2]; exact ⟨hhi, min_le_right _ _, le_max_right _ _⟩
      · rw [ite_eq_right h2]
        obtain ⟨hf, ha1, ha2⟩ := between_of_not_lt_of_not_gt hn' hlo hhi h1 h2
        exact ⟨hf, (min_le_left _ _).trans ha1, ha2.trans (le_max_right _ _)⟩

/-- The clamp lies in every interval that contains both bounds. -/
theorem cvl_mem (two : Two32) {amt lo hi : Float32} {A B : ℝ} (hlo : lo.IsFinite) (hhi : hi.IsFinite)
    (hlo2 : |lo.toReal| ≤ maxFinite32 / 2) (hhi2 : |hi.toReal| ≤ maxFinite32 / 2)
    (hA1 : A ≤ lo.toReal) (hA2 : A ≤ hi.toReal) (hB1 : lo.toReal ≤ B) (hB2 : hi.toReal ≤ B) :
    (cvl amt lo hi).IsFinite ∧ A ≤ (cvl amt lo hi).toReal ∧ (cvl amt lo hi).toReal ≤ B := by
  obtain ⟨h1, h2, h3⟩ := cvl_between two (amt := amt) hlo hhi hlo2 hhi2
  exact ⟨h1, (le_min hA1 hA2).trans h2, h3.trans (max_le hB1 hB2)⟩

/-- On a finite value between the bounds the clamp is the identity. -/
theorem cvl_of_between {amt lo hi : Float32} (ha : amt.IsFinite) (hlo : lo.IsFinite)
    (hhi : hi.IsFinite) (h1 : lo.toReal ≤ amt.toReal) (h2 : amt.toReal ≤ hi.toReal) :
    cvl amt lo hi = amt := by
  unfold cvl
  rw [ite_eq_right (by rw [not_isNaN_of_isFinite ha]; decide), ite_eq_right (by
    rw [lt_iff_toReal_lt ha hlo]; exact not_lt.2 h1), ite_eq_right (by
    show ¬ hi < amt; rw [lt_iff_toReal_lt hhi ha]; exact not_lt.2 h2)]

/-- A symmetric clamp `[-k, k]` keeps the magnitude within `k`: the form of every integrator
limit. -/
theorem cvl_symm (two : Two32) {amt k : Float32} (hk : k.IsFinite) (hk0 : 0 ≤ k.toReal)
    (hk2 : k.toReal ≤ maxFinite32 / 2) :
    (cvl amt (-k) k).IsFinite ∧ |(cvl amt (-k) k).toReal| ≤ k.toReal := by
  have hnk : (-k).IsFinite := (isFinite_neg k).2 hk
  obtain ⟨h1, h2, h3⟩ := cvl_between two (amt := amt) hnk hk
    (by rw [toReal_neg, abs_neg, abs_of_nonneg hk0]; exact hk2) (by rw [abs_of_nonneg hk0]; exact hk2)
  rw [toReal_neg] at h2 h3
  refine ⟨h1, abs_le.2 ⟨?_, ?_⟩⟩
  · exact (le_min le_rfl (by linarith)).trans h2
  · exact h3.trans (max_le (by linarith) le_rfl)

end Float32


namespace Float

/-! ## Finite, NaN, or infinite -/

theorem isNaN_iff (x : Float) : x.isNaN = true ↔ x.toModel.unpack = .notANumber := by
  show x.toModel.unpack.isNaN = true ↔ _
  cases x.toModel.unpack <;> simp [UnpackedFloat.isNaN]

theorem trichotomy (x : Float) :
    x.IsFinite ∨ x.isNaN = true ∨ x.toModel.unpack = .infinity .positive ∨
      x.toModel.unpack = .infinity .negative := by
  rw [isNaN_iff, isFinite_iff]
  rcases x.toModel.unpack with (s | _ | s | ⟨s, m, e, h⟩)
  · cases s <;> simp
  · simp
  · simp [UnpackedFloat.isFinite]
  · simp [UnpackedFloat.isFinite]

theorem not_isNaN_of_isFinite {x : Float} (h : x.IsFinite) : x.isNaN = false := by
  rw [isFinite_iff] at h
  show x.toModel.unpack.isNaN = false
  revert h; cases x.toModel.unpack <;> simp [UnpackedFloat.isNaN, UnpackedFloat.isFinite]

/-! ## Comparisons with NaN are false -/

theorem not_lt_of_isNaN_left {a b : Float} (ha : a.isNaN = true) : ¬ a < b := by
  rw [lt_iff_unpack, (isNaN_iff a).1 ha]; simp [UnpackedFloat.lt, UnpackedFloat.compare]

theorem not_lt_of_isNaN_right {a b : Float} (hb : b.isNaN = true) : ¬ a < b := by
  rw [lt_iff_unpack, (isNaN_iff b).1 hb]
  cases a.toModel.unpack <;> simp [UnpackedFloat.lt, UnpackedFloat.compare]

theorem not_le_of_isNaN_left {a b : Float} (ha : a.isNaN = true) : ¬ a ≤ b := by
  rw [le_iff_unpack, (isNaN_iff a).1 ha]; simp [UnpackedFloat.le, UnpackedFloat.compare]

theorem not_le_of_isNaN_right {a b : Float} (hb : b.isNaN = true) : ¬ a ≤ b := by
  rw [le_iff_unpack, (isNaN_iff b).1 hb]
  cases a.toModel.unpack <;> simp [UnpackedFloat.le, UnpackedFloat.compare]

/-! ## Comparisons with the infinities -/

theorem lt_of_unpack_inf_neg {a b : Float} (ha : a.toModel.unpack = .infinity .negative)
    (hb : b.IsFinite) : a < b := by
  rw [isFinite_iff] at hb
  rw [lt_iff_unpack, ha]
  revert hb; cases b.toModel.unpack <;> simp [UnpackedFloat.lt, UnpackedFloat.compare,
    UnpackedFloat.isFinite]

theorem lt_of_unpack_inf_pos {a b : Float} (ha : a.toModel.unpack = .infinity .positive)
    (hb : b.IsFinite) : b < a := by
  rw [isFinite_iff] at hb
  rw [lt_iff_unpack, ha]
  revert hb; rcases b.toModel.unpack with (s | _ | s | ⟨s, m, e, h⟩) <;>
    simp [UnpackedFloat.lt, UnpackedFloat.compare, UnpackedFloat.isFinite]

/-- A non-NaN float that is not below a finite `lo` and not above a finite `hi` is finite and
between them. -/
theorem between_of_not_lt_of_not_gt {a lo hi : Float} (ha : a.isNaN = false)
    (hlo : lo.IsFinite) (hhi : hi.IsFinite) (h1 : ¬ a < lo) (h2 : ¬ hi < a) :
    a.IsFinite ∧ lo.toReal ≤ a.toReal ∧ a.toReal ≤ hi.toReal := by
  rcases trichotomy a with hf | hn | hp | hm
  · refine ⟨hf, ?_, ?_⟩
    · rw [lt_iff_toReal_lt hf hlo] at h1; exact not_lt.1 h1
    · rw [lt_iff_toReal_lt hhi hf] at h2; exact not_lt.1 h2
  · rw [ha] at hn; exact absurd hn (by decide)
  · exact absurd (lt_of_unpack_inf_pos hp hhi) h2
  · exact absurd (lt_of_unpack_inf_neg hm hlo) h1

/-! ## Literals -/

/-- The literal `Int32.toFloat 2` of the translated midpoint is the finite float `2`. Its proof
(`FloatModel.Lit.two64`) evaluates the literal, which needs the bodies of core's conversions: they
are not exposed to modules, so it lives in a plain file and the lemmas below take it as an
argument. -/
def Two64 : Prop := (Int32.toFloat (2 : Int32)).IsFinite ∧ (Int32.toFloat (2 : Int32)).toReal = 2

/-- Twice a finite float is a float, when it does not overflow. -/
theorem exists_double {a : Float} (ha : a.IsFinite) (hhi : |2 * a.toReal| ≤ maxFinite) :
    ∃ d : Float, d.IsFinite ∧ d.toReal = 2 * a.toReal := by
  obtain ⟨w, hc, hf, hw⟩ := UnpackedFloat.exists_double a.canonicalIn_unpack ha hhi
  refine ⟨Float.ofModel (Float.Model.pack w), ?_, ?_⟩
  · rw [isFinite_iff]; show (Float.Model.pack w).unpack.isFinite = true
    rw [Float.Model.unpack_pack_of_canonical ((canonical_iff w).2 hc)]; exact hf
  · show (Float.Model.pack w).unpack.toReal = 2 * a.toModel.unpack.toReal
    rw [Float.Model.unpack_pack_of_canonical ((canonical_iff w).2 hc), hw]

/-! ## The midpoint -/

/-- A sum of two finite floats lies between their doubles. -/
theorem add_between {a b : Float} (ha : a.IsFinite) (hb : b.IsFinite)
    (ha2 : |a.toReal| ≤ maxFinite / 2) (hb2 : |b.toReal| ≤ maxFinite / 2)
    (hab : a.toReal ≤ b.toReal) :
    (a + b).IsFinite ∧ 2 * a.toReal ≤ (a + b).toReal ∧ (a + b).toReal ≤ 2 * b.toReal := by
  have hs : |a.toReal + b.toReal| ≤ maxFinite := by
    have := abs_add_le a.toReal b.toReal; linarith
  obtain ⟨da, hda, hda'⟩ := exists_double ha (by rw [abs_mul]; norm_num; linarith)
  obtain ⟨db, hdb, hdb'⟩ := exists_double hb (by rw [abs_mul]; norm_num; linarith)
  refine ⟨(add_err_all ha hb hs).1, ?_, ?_⟩
  · rw [← hda']; exact (add_bracket ha hb hs hda).1 (by rw [hda']; linarith)
  · rw [← hdb']; exact (add_bracket ha hb hs hdb).2 (by rw [hdb']; linarith)

/-- The midpoint `(a + b) / 2` of two finite floats (below `maxFinite / 2`) is finite and lies
between them, in either order. -/
theorem mid_between (two : Two64) {a b : Float} (ha : a.IsFinite) (hb : b.IsFinite)
    (ha2 : |a.toReal| ≤ maxFinite / 2) (hb2 : |b.toReal| ≤ maxFinite / 2) :
    ((a + b) / Int32.toFloat 2).IsFinite ∧
      min a.toReal b.toReal ≤ ((a + b) / Int32.toFloat 2).toReal ∧
      ((a + b) / Int32.toFloat 2).toReal ≤ max a.toReal b.toReal := by
  have hs : |a.toReal + b.toReal| ≤ maxFinite := by
    have := abs_add_le a.toReal b.toReal; linarith
  have hsf := (add_err_all ha hb hs).1
  have hS : |(a + b).toReal| ≤ maxFinite := abs_toReal_le_maxFinite _
  have h2 := two.1
  have h2r := two.2
  have hq : |(a + b).toReal / (Int32.toFloat 2).toReal| ≤ maxFinite := by
    rw [h2r, abs_div]; norm_num; linarith [abs_nonneg (a + b).toReal]
  have h20 : (Int32.toFloat 2).toReal ≠ 0 := by rw [h2r]; norm_num
  refine ⟨(div_err_all hsf h2 h20 hq).1, ?_, ?_⟩
  · -- lower bound: the smaller of `a`, `b`
    rcases le_total a.toReal b.toReal with hab | hab
    · rw [min_eq_left hab]
      have := (add_between ha hb ha2 hb2 hab).2.1
      exact (div_bracket hsf h2 h20 hq ha).1 (by rw [h2r]; linarith)
    · rw [min_eq_right hab]
      obtain ⟨_, h1, _⟩ := add_between hb ha hb2 ha2 hab
      -- `b + a` and `a + b` have the same exact value; reason on the exact sum directly
      have hlow : 2 * b.toReal ≤ (a + b).toReal := by
        obtain ⟨db, hdb, hdb'⟩ := exists_double hb (by rw [abs_mul]; norm_num; linarith)
        rw [← hdb']; exact (add_bracket ha hb hs hdb).1 (by rw [hdb']; linarith)
      exact (div_bracket hsf h2 h20 hq hb).1 (by rw [h2r]; linarith)
  · rcases le_total a.toReal b.toReal with hab | hab
    · rw [max_eq_right hab]
      have := (add_between ha hb ha2 hb2 hab).2.2
      exact (div_bracket hsf h2 h20 hq hb).2 (by rw [h2r]; linarith)
    · rw [max_eq_left hab]
      have hup : (a + b).toReal ≤ 2 * a.toReal := by
        obtain ⟨da, hda, hda'⟩ := exists_double ha (by rw [abs_mul]; norm_num; linarith)
        rw [← hda']; exact (add_bracket ha hb hs hda).2 (by rw [hda']; linarith)
      exact (div_bracket hsf h2 h20 hq ha).2 (by rw [h2r]; linarith)

/-! ## The NaN-safe clamp (`constrain_value_line`) -/

/-- ArduPilot's `constrain_value_line(amt, low, high)` (`AP_Math/AP_Math.cpp:283-304`) on floats,
as the translator emits it: NaN goes to the midpoint, then the two comparisons. -/
def cvl (amt lo hi : Float) : Float :=
  if amt.isNaN then (lo + hi) / Int32.toFloat 2
  else if amt < lo then lo else if amt > hi then hi else amt

/-- **The clamp is always finite and between its bounds**, whatever `amt` is (NaN, `±∞`
included), for finite bounds below `maxFinite / 2` (given in either order). -/
theorem cvl_between (two : Two64) {amt lo hi : Float} (hlo : lo.IsFinite) (hhi : hi.IsFinite)
    (hlo2 : |lo.toReal| ≤ maxFinite / 2) (hhi2 : |hi.toReal| ≤ maxFinite / 2) :
    (cvl amt lo hi).IsFinite ∧ min lo.toReal hi.toReal ≤ (cvl amt lo hi).toReal ∧
      (cvl amt lo hi).toReal ≤ max lo.toReal hi.toReal := by
  unfold cvl
  by_cases hn : amt.isNaN = true
  · rw [ite_eq_left hn]; exact mid_between two hlo hhi hlo2 hhi2
  · rw [ite_eq_right hn]
    have hn' : amt.isNaN = false := by simpa using hn
    by_cases h1 : amt < lo
    · rw [ite_eq_left h1]; exact ⟨hlo, min_le_left _ _, le_max_left _ _⟩
    · rw [ite_eq_right h1]
      by_cases h2 : amt > hi
      · rw [ite_eq_left h2]; exact ⟨hhi, min_le_right _ _, le_max_right _ _⟩
      · rw [ite_eq_right h2]
        obtain ⟨hf, ha1, ha2⟩ := between_of_not_lt_of_not_gt hn' hlo hhi h1 h2
        exact ⟨hf, (min_le_left _ _).trans ha1, ha2.trans (le_max_right _ _)⟩

/-- The clamp lies in every interval that contains both bounds. -/
theorem cvl_mem (two : Two64) {amt lo hi : Float} {A B : ℝ} (hlo : lo.IsFinite) (hhi : hi.IsFinite)
    (hlo2 : |lo.toReal| ≤ maxFinite / 2) (hhi2 : |hi.toReal| ≤ maxFinite / 2)
    (hA1 : A ≤ lo.toReal) (hA2 : A ≤ hi.toReal) (hB1 : lo.toReal ≤ B) (hB2 : hi.toReal ≤ B) :
    (cvl amt lo hi).IsFinite ∧ A ≤ (cvl amt lo hi).toReal ∧ (cvl amt lo hi).toReal ≤ B := by
  obtain ⟨h1, h2, h3⟩ := cvl_between two (amt := amt) hlo hhi hlo2 hhi2
  exact ⟨h1, (le_min hA1 hA2).trans h2, h3.trans (max_le hB1 hB2)⟩

/-- On a finite value between the bounds the clamp is the identity. -/
theorem cvl_of_between {amt lo hi : Float} (ha : amt.IsFinite) (hlo : lo.IsFinite)
    (hhi : hi.IsFinite) (h1 : lo.toReal ≤ amt.toReal) (h2 : amt.toReal ≤ hi.toReal) :
    cvl amt lo hi = amt := by
  unfold cvl
  rw [ite_eq_right (by rw [not_isNaN_of_isFinite ha]; decide), ite_eq_right (by
    rw [lt_iff_toReal_lt ha hlo]; exact not_lt.2 h1), ite_eq_right (by
    show ¬ hi < amt; rw [lt_iff_toReal_lt hhi ha]; exact not_lt.2 h2)]

/-- A symmetric clamp `[-k, k]` keeps the magnitude within `k`: the form of every integrator
limit. -/
theorem cvl_symm (two : Two64) {amt k : Float} (hk : k.IsFinite) (hk0 : 0 ≤ k.toReal)
    (hk2 : k.toReal ≤ maxFinite / 2) :
    (cvl amt (-k) k).IsFinite ∧ |(cvl amt (-k) k).toReal| ≤ k.toReal := by
  have hnk : (-k).IsFinite := (isFinite_neg k).2 hk
  obtain ⟨h1, h2, h3⟩ := cvl_between two (amt := amt) hnk hk
    (by rw [toReal_neg, abs_neg, abs_of_nonneg hk0]; exact hk2) (by rw [abs_of_nonneg hk0]; exact hk2)
  rw [toReal_neg] at h2 h3
  refine ⟨h1, abs_le.2 ⟨?_, ?_⟩⟩
  · exact (le_min le_rfl (by linarith)).trans h2
  · exact h3.trans (max_le (by linarith) le_rfl)

end Float
