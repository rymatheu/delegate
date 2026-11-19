import ArduLean.Vehicle
import Corpus.Machine.Float
import Corpus.Machine.Memory
import Corpus.Machine.Hoare
import Corpus.Code.AP_Param.AP_Param

/-!
# AP_Math: `AP_Math.{h,cpp}`, `ftype.h`, `definitions.h`

Low-level lemmas about the translated functions (Corpus/PLAN.md, "Kinds of low-level proof"). Every statement
names its code constant; every proof opens that constant's body (or uses lemmas of this file that did).
Throughout, `ε` is `FLT_EPSILON`, the word `0x34000000` (`2⁻²³`), and `ext` (`Corpus.F32.ext`) is the extended real a
`Binary32` denotes.
-/

open FloatLib.Floats (Binary32 Binary64)
open Corpus.F32 (ext)
open FloatLib.Floats (ExecFloat)
open FloatLib.Floats.Formats.BinaryInterchange (Model)

namespace Corpus.AP_Math

/-! ## `is_zero`

C++ `is_zero : bool (const float)`, `ftype.h:61-63`: `fabsf(x) < FLT_EPSILON`. -/

theorem is_zero_eq (x : Binary32) :
    Vehicle_lib.is_zero x = pure (Vehicle_lib.is_zero.pure' x) := rfl

/-- Case: the exact threshold, as the code compares. -/
theorem is_zero_pure_eq (x : Binary32) :
    Id.run (Vehicle_lib.is_zero.pure' x) = decide (Binary32.abs x < Binary32.ofBits 0x34000000) := rfl

/-- Case: `is_zero x` iff `-ε < x < ε` (float comparisons). -/
theorem is_zero_iff (x : Binary32) :
    Id.run (Vehicle_lib.is_zero.pure' x) = true ↔
      Binary32.ofBits 0xb4000000 < x ∧ x < Binary32.ofBits 0x34000000 := by
  rw [is_zero_pure_eq, decide_eq_true_iff, Corpus.F32.abs_lt_iff Corpus.F32.isNaN_eps, Corpus.F32.neg_eps]

/-- NaN: `is_zero` of a NaN is `false`. -/
theorem is_zero_of_isNaN {x : Binary32} (hx : Binary32.isNaN x = true) :
    Id.run (Vehicle_lib.is_zero.pure' x) = false := by
  rw [Bool.eq_false_iff, Ne, is_zero_iff]
  exact fun h => Corpus.F32.not_lt_of_isNaN_left hx h.2

/-- Meaning: `is_zero x` iff `x` is a number with `|x| < 2⁻²³`. -/
theorem is_zero_iff_ext (x : Binary32) :
    Id.run (Vehicle_lib.is_zero.pure' x) = true ↔
      Binary32.isNaN x = false ∧ -(((1 / 8388608 : ℚ) : ℝ) : EReal) < ext x ∧
        ext x < (((1 / 8388608 : ℚ) : ℝ) : EReal) := by
  rw [is_zero_iff, ← Corpus.F32.neg_eps]
  cases hx : Binary32.isNaN x
  · have hn : Binary32.isNaN (-(Binary32.ofBits 0x34000000)) = false := by decide +kernel
    rw [Corpus.F32.lt_iff_ext hn hx, Corpus.F32.lt_iff_ext hx Corpus.F32.isNaN_eps,
      Corpus.F32.ext_neg Corpus.F32.isNaN_eps, Corpus.F32.ext_eps]
    simp
  · simp only [Bool.true_eq_false, false_and, iff_false, not_and]
    exact fun _ h => Corpus.F32.not_lt_of_isNaN_left hx h

/-! ## `is_positive`, `is_negative`

C++ `is_positive : bool (const float)`, `AP_Math.h:65-69` (`fVal1 >= FLT_EPSILON`), and
`is_negative : bool (const float)`, `AP_Math.h:76-80` (`fVal1 <= (-1.0 * FLT_EPSILON)`, compared in `double`). -/

theorem is_positive_eq (x : Binary32) :
    Vehicle_lib.is_positive'float x = pure (Vehicle_lib.is_positive'float.pure' x) := rfl

theorem is_negative_eq (x : Binary32) :
    Vehicle_lib.is_negative'float x = pure (Vehicle_lib.is_negative'float.pure' x) := rfl

/-- Case: `is_positive x` iff `ε ≤ x`. -/
theorem is_positive_iff (x : Binary32) :
    Id.run (Vehicle_lib.is_positive'float.pure' x) = true ↔ Binary32.ofBits 0x34000000 ≤ x := by
  show decide (x ≥ Binary32.ofBits 0x34000000) = true ↔ _
  rw [decide_eq_true_iff]

/-- Meaning: `is_positive x` iff `x` is a number `≥ 2⁻²³` (`+∞` included). -/
theorem is_positive_iff_ext (x : Binary32) :
    Id.run (Vehicle_lib.is_positive'float.pure' x) = true ↔
      Binary32.isNaN x = false ∧ (((1 / 8388608 : ℚ) : ℝ) : EReal) ≤ ext x := by
  rw [is_positive_iff]
  cases hx : Binary32.isNaN x
  · rw [Corpus.F32.le_iff_ext Corpus.F32.isNaN_eps hx, Corpus.F32.ext_eps]; simp
  · simp only [Bool.true_eq_false, false_and, iff_false]
    exact Corpus.F32.not_le_of_isNaN_right hx

/-- Meaning: `is_negative x` iff `x` is a number `≤ -2⁻²³` (`-∞` included). -/
theorem is_negative_iff_ext (x : Binary32) :
    Id.run (Vehicle_lib.is_negative'float.pure' x) = true ↔
      Binary32.isNaN x = false ∧ ext x ≤ -(((1 / 8388608 : ℚ) : ℝ) : EReal) := by
  show decide (Binary32.toBinary64 x ≤ (-(Binary64.ofBits 0x3ff0000000000000)) *
    Binary32.toBinary64 (Binary32.ofBits 0x34000000)) = true ↔ _
  rw [decide_eq_true_iff, Corpus.F32.is_negative_const]
  have hc : Binary64.isNaN (Binary64.ofBits 0xbe80000000000000) = false := by decide +kernel
  cases hx : Binary32.isNaN x
  · have hx64 : Binary64.isNaN (Binary32.toBinary64 x) = false := by
      rw [Corpus.F64.isNaN_toBinary64]; exact hx
    rw [Corpus.F64.le_iff_ext hx64 hc, Corpus.F64.ext_toBinary64 hx,
      Corpus.F64.ext_eq_of_toRat? (q := -1 / 8388608) (by decide +kernel)]
    have e : (((-1 / 8388608 : ℚ) : ℝ) : EReal) = -(((1 / 8388608 : ℚ) : ℝ) : EReal) := by
      rw [← EReal.coe_neg]; norm_num
    rw [e]; simp
  · simp only [Bool.true_eq_false, false_and, iff_false]
    apply Corpus.F64.not_le_of_isNaN_left
    rw [Corpus.F64.isNaN_toBinary64]; exact hx

/-- Case: `is_negative x` iff `x ≤ -ε`, compared in `float`. -/
theorem is_negative_iff (x : Binary32) :
    Id.run (Vehicle_lib.is_negative'float.pure' x) = true ↔ x ≤ Binary32.ofBits 0xb4000000 := by
  rw [is_negative_iff_ext, ← Corpus.F32.neg_eps]
  have hn : Binary32.isNaN (-(Binary32.ofBits 0x34000000)) = false := by decide +kernel
  cases hx : Binary32.isNaN x
  · rw [Corpus.F32.le_iff_ext hx hn, Corpus.F32.ext_neg Corpus.F32.isNaN_eps, Corpus.F32.ext_eps]; simp
  · simp only [Bool.true_eq_false, false_and, false_iff]
    exact Corpus.F32.not_le_of_isNaN_left hx

/-! ## Relations between the three tests -/

theorem is_zero_not_positive (x : Binary32) (h : Id.run (Vehicle_lib.is_zero.pure' x) = true) :
    Id.run (Vehicle_lib.is_positive'float.pure' x) = false := by
  rw [Bool.eq_false_iff, Ne, is_positive_iff_ext]
  rw [is_zero_iff_ext] at h
  exact fun h' => absurd h.2.2 (not_lt.2 h'.2)

theorem is_zero_not_negative (x : Binary32) (h : Id.run (Vehicle_lib.is_zero.pure' x) = true) :
    Id.run (Vehicle_lib.is_negative'float.pure' x) = false := by
  rw [Bool.eq_false_iff, Ne, is_negative_iff_ext]
  rw [is_zero_iff_ext] at h
  exact fun h' => absurd h.2.1 (not_lt.2 h'.2)

theorem is_positive_not_negative (x : Binary32) (h : Id.run (Vehicle_lib.is_positive'float.pure' x) = true) :
    Id.run (Vehicle_lib.is_negative'float.pure' x) = false := by
  rw [Bool.eq_false_iff, Ne, is_negative_iff_ext]
  rw [is_positive_iff_ext] at h
  intro h'
  have h1 := h.2.trans h'.2
  have h2 : (0 : EReal) < (((1 / 8388608 : ℚ) : ℝ) : EReal) := by
    have : (0 : ℝ) < ((1 / 8388608 : ℚ) : ℝ) := by norm_num
    exact_mod_cast this
  exact absurd h1 (not_le.2 ((EReal.neg_lt_zero.2 h2).trans h2))

/-- NaN: none of the three tests holds. -/
theorem is_positive_of_isNaN {x : Binary32} (hx : Binary32.isNaN x = true) :
    Id.run (Vehicle_lib.is_positive'float.pure' x) = false := by
  rw [Bool.eq_false_iff, Ne, is_positive_iff_ext, hx]; simp

theorem is_negative_of_isNaN {x : Binary32} (hx : Binary32.isNaN x = true) :
    Id.run (Vehicle_lib.is_negative'float.pure' x) = false := by
  rw [Bool.eq_false_iff, Ne, is_negative_iff_ext, hx]; simp

/-- A number is zero, positive or negative in the sense of the three tests. -/
theorem is_zero_or_positive_or_negative {x : Binary32} (hx : Binary32.isNaN x = false) :
    Id.run (Vehicle_lib.is_zero.pure' x) = true ∨ Id.run (Vehicle_lib.is_positive'float.pure' x) = true ∨
      Id.run (Vehicle_lib.is_negative'float.pure' x) = true := by
  rw [is_zero_iff_ext, is_positive_iff_ext, is_negative_iff_ext]
  simp only [hx, true_and]
  rcases lt_or_ge (ext x) (((1 / 8388608 : ℚ) : ℝ) : EReal) with h1 | h1
  · rcases lt_or_ge (-(((1 / 8388608 : ℚ) : ℝ) : EReal)) (ext x) with h2 | h2
    · exact Or.inl ⟨h2, h1⟩
    · exact Or.inr (Or.inr h2)
  · exact Or.inr (Or.inl h1)

/-! ## `is_equal`

C++ `is_equal : bool (const float, const float)`, `AP_Math.cpp:25-41`: `fabsf(v_1 - v_2) < FLT_EPSILON` (the `double`
branch is dead for `float`). -/

theorem is_equal_eq (a b : Binary32) :
    Vehicle_lib.is_equal'float_float a b = pure (Vehicle_lib.is_equal'float_float.pure' a b) := rfl

/-- Case: `is_equal a b` is `is_zero (a - b)`. -/
theorem is_equal_eq_is_zero (a b : Binary32) :
    Id.run (Vehicle_lib.is_equal'float_float.pure' a b) = Id.run (Vehicle_lib.is_zero.pure' (a - b)) := rfl

/-! ## `constrain_value_line` (float)

C++ `constrain_value_line : float (const float, const float, const float, uint32_t)`, `AP_Math.cpp:283-304`: a NaN
`amt` gives the midpoint `(low + high) / 2` (and an internal-error report, not translated: `line` is unused); otherwise
`low` below `low`, `high` above `high`, else `amt`. -/

theorem constrain_float_eq (amt low high : Binary32) (line : UInt32) :
    Vehicle_lib.constrain_value_line'float amt low high line =
      pure (Vehicle_lib.constrain_value_line'float.pure' amt low high line) := rfl

/-- Case: the body as one conditional (the literal `2` as its word). -/
theorem constrain_float_pure_eq (amt low high : Binary32) (line : UInt32) :
    Id.run (Vehicle_lib.constrain_value_line'float.pure' amt low high line) =
      if Binary32.isNaN amt then (low + high) / Binary32.ofBits 0x40000000
      else if amt < low then low else if high < amt then high else amt := by
  rw [← Corpus.F32.int32_two]; rfl

theorem constrain_float_of_isNaN {amt : Binary32} (low high : Binary32) (line : UInt32)
    (h : Binary32.isNaN amt = true) :
    Id.run (Vehicle_lib.constrain_value_line'float.pure' amt low high line) =
      (low + high) / Binary32.ofBits 0x40000000 := by
  rw [constrain_float_pure_eq, Corpus.ite_pos h]

theorem constrain_float_of_lt {amt low : Binary32} (high : Binary32) (line : UInt32) (h : amt < low) :
    Id.run (Vehicle_lib.constrain_value_line'float.pure' amt low high line) = low := by
  rw [constrain_float_pure_eq, Corpus.ite_neg (by simp [(Corpus.F32.isNaN_false_of_lt h).1]), Corpus.ite_pos h]

theorem constrain_float_of_gt {amt low high : Binary32} (line : UInt32) (hl : ¬ amt < low) (h : high < amt) :
    Id.run (Vehicle_lib.constrain_value_line'float.pure' amt low high line) = high := by
  rw [constrain_float_pure_eq, Corpus.ite_neg (by simp [(Corpus.F32.isNaN_false_of_lt h).2]), Corpus.ite_neg hl, Corpus.ite_pos h]

/-- Case (identity): on `[low, high]` the result is `amt`. -/
theorem constrain_float_of_mem {amt low high : Binary32} (line : UInt32) (hl : low ≤ amt) (hh : amt ≤ high) :
    Id.run (Vehicle_lib.constrain_value_line'float.pure' amt low high line) = amt := by
  obtain ⟨hln, han⟩ := Corpus.F32.isNaN_false_of_le hl
  have hhn := (Corpus.F32.isNaN_false_of_le hh).2
  rw [constrain_float_pure_eq, Corpus.ite_neg (by simp [han]), Corpus.ite_neg ((Corpus.F32.not_lt_iff_le han hln).2 hl),
    Corpus.ite_neg ((Corpus.F32.not_lt_iff_le hhn han).2 hh)]

/-- Case: for a number `amt` the result is one of `amt`, `low`, `high`. -/
theorem constrain_float_cases {amt : Binary32} (low high : Binary32) (line : UInt32)
    (hn : Binary32.isNaN amt = false) :
    Id.run (Vehicle_lib.constrain_value_line'float.pure' amt low high line) = amt ∨
      Id.run (Vehicle_lib.constrain_value_line'float.pure' amt low high line) = low ∨
      Id.run (Vehicle_lib.constrain_value_line'float.pure' amt low high line) = high := by
  rw [constrain_float_pure_eq, Corpus.ite_neg (by simp [hn])]
  split_ifs <;> simp

/-- Meaning: for a number `amt` and `low ≤ high`, the result denotes `max low (min amt high)`. -/
theorem constrain_float_ext {amt low high : Binary32} (line : UInt32) (hlh : low ≤ high)
    (hn : Binary32.isNaN amt = false) :
    ext (Id.run (Vehicle_lib.constrain_value_line'float.pure' amt low high line)) =
      max (ext low) (min (ext amt) (ext high)) := by
  obtain ⟨hln, hhn⟩ := Corpus.F32.isNaN_false_of_le hlh
  have hlh' := (Corpus.F32.le_iff_ext hln hhn).1 hlh
  rw [constrain_float_pure_eq, Corpus.ite_neg (by simp [hn])]
  split_ifs with h1 h2
  · have h1' := (Corpus.F32.lt_iff_ext hn hln).1 h1
    rw [min_eq_left (h1'.le.trans hlh'), max_eq_left h1'.le]
  · have h2' := (Corpus.F32.lt_iff_ext hhn hn).1 h2
    rw [min_eq_right h2'.le, max_eq_right hlh']
  · have h1' := not_lt.1 ((Corpus.F32.lt_iff_ext hn hln).not.1 h1)
    have h2' := not_lt.1 ((Corpus.F32.lt_iff_ext hhn hn).not.1 h2)
    rw [min_eq_left h2', max_eq_right h1']

theorem constrain_float_not_isNaN {amt low high : Binary32} (line : UInt32) (hlh : low ≤ high)
    (hn : Binary32.isNaN amt = false) :
    Binary32.isNaN (Id.run (Vehicle_lib.constrain_value_line'float.pure' amt low high line)) = false := by
  obtain ⟨hln, hhn⟩ := Corpus.F32.isNaN_false_of_le hlh
  rcases constrain_float_cases low high line hn with h | h | h <;> rw [h] <;> assumption

/-- Range: for a number `amt` and `low ≤ high`, the result is in `[low, high]`. -/
theorem constrain_float_mem {amt low high : Binary32} (line : UInt32) (hlh : low ≤ high)
    (hn : Binary32.isNaN amt = false) :
    low ≤ Id.run (Vehicle_lib.constrain_value_line'float.pure' amt low high line) ∧
      Id.run (Vehicle_lib.constrain_value_line'float.pure' amt low high line) ≤ high := by
  obtain ⟨hln, hhn⟩ := Corpus.F32.isNaN_false_of_le hlh
  have hlh' := (Corpus.F32.le_iff_ext hln hhn).1 hlh
  have hr := constrain_float_not_isNaN line hlh hn
  rw [Corpus.F32.le_iff_ext hln hr, Corpus.F32.le_iff_ext hr hhn, constrain_float_ext line hlh hn]
  exact ⟨le_max_left _ _, max_le hlh' (min_le_right _ _)⟩

/-- Order: idempotent. -/
theorem constrain_float_idem {amt low high : Binary32} (line line' : UInt32) (hlh : low ≤ high)
    (hn : Binary32.isNaN amt = false) :
    Id.run (Vehicle_lib.constrain_value_line'float.pure'
        (Id.run (Vehicle_lib.constrain_value_line'float.pure' amt low high line)) low high line') =
      Id.run (Vehicle_lib.constrain_value_line'float.pure' amt low high line) :=
  constrain_float_of_mem line' (constrain_float_mem line hlh hn).1 (constrain_float_mem line hlh hn).2

/-- Order: monotone in `amt`. -/
theorem constrain_float_mono {a b low high : Binary32} (line line' : UInt32) (hlh : low ≤ high) (hab : a ≤ b) :
    Id.run (Vehicle_lib.constrain_value_line'float.pure' a low high line) ≤
      Id.run (Vehicle_lib.constrain_value_line'float.pure' b low high line') := by
  obtain ⟨han, hbn⟩ := Corpus.F32.isNaN_false_of_le hab
  rw [Corpus.F32.le_iff_ext (constrain_float_not_isNaN line hlh han) (constrain_float_not_isNaN line' hlh hbn),
    constrain_float_ext line hlh han, constrain_float_ext line' hlh hbn]
  exact max_le_max le_rfl (min_le_min ((Corpus.F32.le_iff_ext han hbn).1 hab) le_rfl)

/-! ## `constrain_int16`, `constrain_value` (short)

C++ `constrain_int16 : int16_t (const int16_t, const int16_t, const int16_t)`, `AP_Math.h:191-194`, calling
`constrain_value : short (const short, const short, const short)` (`AP_Math.cpp:310-331`; the NaN branch is dead for
integers), compared after promotion to `int`. -/

theorem constrain_short_eq (amt low high : Int16) :
    Vehicle_lib.constrain_value'short amt low high = pure (Vehicle_lib.constrain_value'short.pure' amt low high) := rfl

theorem constrain_int16_eq (amt low high : Int16) :
    Vehicle_lib.constrain_int16 amt low high = pure (Vehicle_lib.constrain_int16.pure' amt low high) := rfl

/-- Case: the promoted comparisons are the `Int16` ones. -/
theorem constrain_short_pure_eq (amt low high : Int16) :
    Id.run (Vehicle_lib.constrain_value'short.pure' amt low high) =
      if amt < low then low else if high < amt then high else amt := by
  have e : ∀ a b : Int16, (Int16.toInt32 a < Int16.toInt32 b) = (a < b) := fun a b =>
    propext (by simp [Int16.lt_iff_toInt_lt, Int32.lt_iff_toInt_lt])
  show (if Int16.toInt32 amt < Int16.toInt32 low then low
    else if Int16.toInt32 amt > Int16.toInt32 high then high else amt) = _
  simp only [gt_iff_lt, e]

theorem constrain_int16_pure_eq (amt low high : Int16) :
    Id.run (Vehicle_lib.constrain_int16.pure' amt low high) =
      Id.run (Vehicle_lib.constrain_value'short.pure' amt low high) := rfl

/-- Range: in `[low, high]` when `low ≤ high`. -/
theorem constrain_int16_mem {amt low high : Int16} (hlh : low ≤ high) :
    low ≤ Id.run (Vehicle_lib.constrain_int16.pure' amt low high) ∧
      Id.run (Vehicle_lib.constrain_int16.pure' amt low high) ≤ high := by
  rw [constrain_int16_pure_eq, constrain_short_pure_eq]
  simp only [Int16.le_iff_toInt_le, Int16.lt_iff_toInt_lt] at *
  split_ifs <;> omega

/-- Case (identity): on `[low, high]` the result is `amt`. -/
theorem constrain_int16_of_mem {amt low high : Int16} (hl : low ≤ amt) (hh : amt ≤ high) :
    Id.run (Vehicle_lib.constrain_int16.pure' amt low high) = amt := by
  rw [constrain_int16_pure_eq, constrain_short_pure_eq]
  simp only [Int16.le_iff_toInt_le, Int16.lt_iff_toInt_lt] at *
  split_ifs <;> first | rfl | omega

/-- Order: idempotent when `low ≤ high`. -/
theorem constrain_int16_idem {amt low high : Int16} (hlh : low ≤ high) :
    Id.run (Vehicle_lib.constrain_int16.pure' (Id.run (Vehicle_lib.constrain_int16.pure' amt low high)) low high) =
      Id.run (Vehicle_lib.constrain_int16.pure' amt low high) :=
  constrain_int16_of_mem (constrain_int16_mem hlh).1 (constrain_int16_mem hlh).2

/-- Order: monotone in `amt` when `low ≤ high`. -/
theorem constrain_int16_mono {a b low high : Int16} (hlh : low ≤ high) (hab : a ≤ b) :
    Id.run (Vehicle_lib.constrain_int16.pure' a low high) ≤ Id.run (Vehicle_lib.constrain_int16.pure' b low high) := by
  rw [constrain_int16_pure_eq, constrain_short_pure_eq, constrain_int16_pure_eq, constrain_short_pure_eq]
  simp only [Int16.le_iff_toInt_le, Int16.lt_iff_toInt_lt] at *
  split_ifs <;> first | rfl | omega

/-! ## `safe_sqrt` (float)

C++ `safe_sqrt : float (const float)`, `AP_Math.cpp:72-81`: `sqrtf(v)` when `v >= 0`, else `0` (NaN included). -/

theorem safe_sqrt_eq (v : Binary32) :
    Vehicle_lib.safe_sqrt'float v = pure (Vehicle_lib.safe_sqrt'float.pure' v) := rfl

/-- Case: the body as one conditional (the literal `0` as its word). -/
theorem safe_sqrt_pure_eq (v : Binary32) :
    Id.run (Vehicle_lib.safe_sqrt'float.pure' v) =
      if Binary32.ofBits 0x00000000 ≤ v then Binary32.sqrt v else Binary32.ofBits 0x00000000 := by
  rw [← Corpus.F32.int32_zero]; rfl

theorem safe_sqrt_of_nonneg {v : Binary32} (h : Binary32.ofBits 0x00000000 ≤ v) :
    Id.run (Vehicle_lib.safe_sqrt'float.pure' v) = Binary32.sqrt v := by
  rw [safe_sqrt_pure_eq, Corpus.ite_pos h]

theorem safe_sqrt_of_not_nonneg {v : Binary32} (h : ¬ Binary32.ofBits 0x00000000 ≤ v) :
    Id.run (Vehicle_lib.safe_sqrt'float.pure' v) = Binary32.ofBits 0x00000000 := by
  rw [safe_sqrt_pure_eq, Corpus.ite_neg h]

theorem safe_sqrt_of_isNaN {v : Binary32} (h : Binary32.isNaN v = true) :
    Id.run (Vehicle_lib.safe_sqrt'float.pure' v) = Binary32.ofBits 0x00000000 :=
  safe_sqrt_of_not_nonneg (Corpus.F32.not_le_of_isNaN_right h)

theorem safe_sqrt_of_neg {v : Binary32} (h : v < Binary32.ofBits 0x00000000) :
    Id.run (Vehicle_lib.safe_sqrt'float.pure' v) = Binary32.ofBits 0x00000000 := by
  obtain ⟨hv, h0⟩ := Corpus.F32.isNaN_false_of_lt h
  apply safe_sqrt_of_not_nonneg
  rw [Corpus.F32.le_iff_ext h0 hv]
  exact not_le.2 ((Corpus.F32.lt_iff_ext hv h0).1 h)

/-- Safety: never a NaN. -/
theorem safe_sqrt_not_isNaN (v : Binary32) :
    Binary32.isNaN (Id.run (Vehicle_lib.safe_sqrt'float.pure' v)) = false := by
  rw [safe_sqrt_pure_eq]
  split_ifs with h
  · exact (Corpus.F32.sqrt_of_nonneg h).1
  · exact Corpus.F32.isNaN_zero

/-- Range: nonnegative (`-0` for `v = -0`, which compares equal to `0`). -/
theorem safe_sqrt_nonneg (v : Binary32) :
    Binary32.ofBits 0x00000000 ≤ Id.run (Vehicle_lib.safe_sqrt'float.pure' v) := by
  rw [safe_sqrt_pure_eq]
  split_ifs with h
  · exact (Corpus.F32.sqrt_of_nonneg h).2
  · exact Corpus.F32.le_refl_of_not_isNaN Corpus.F32.isNaN_zero

/-- Meaning: for a finite `v ≥ 0`, the correctly rounded square root of its real value. -/
theorem safe_sqrt_toReal {v : Binary32} (hf : Binary32.isFinite v = true) (h : Binary32.ofBits 0x00000000 ≤ v) :
    Corpus.F32.real (Id.run (Vehicle_lib.safe_sqrt'float.pure' v)) =
      Model.roundAt (ExecFloat.Binary.descriptor 8 23) (Real.sqrt (Corpus.F32.real v)) := by
  rw [safe_sqrt_of_nonneg h]
  have hx := (Corpus.F32.isNaN_false_of_le h).2
  rw [Corpus.F32.le_iff_ext Corpus.F32.isNaN_zero hx, Corpus.F32.ext_zero, Corpus.F32.ext_of_isFinite hf] at h
  have hr : 0 ≤ Corpus.F32.real v := by exact_mod_cast h
  exact ExecFloat.Binary.toReal_sqrt_eq_roundAt hf
    (ExecFloat.Binary.isZero_or_signBit_eq_false_of_toReal_nonneg hf hr)

/-! ## `safe_asin` (float)

C++ `safe_asin : float (const float)`, `definitions.h:50-63`: `0` for a NaN, `π/2` from `1` up, `-π/2` from `-1` down,
else `asinf`. The `π/2` constants are computed in `double` and rounded to `float` (`0x3fc90fdb`, `0xbfc90fdb`). -/

theorem safe_asin_eq (v : Binary32) :
    Vehicle_lib.safe_asin'float v = pure (Vehicle_lib.safe_asin'float.pure' v) := rfl







/-- Case: the four branches as one conditional. -/
theorem safe_asin_pure_eq (v : Binary32) :
    Id.run (Vehicle_lib.safe_asin'float.pure' v) =
      if Binary32.isNaN v then Binary32.ofBits 0x00000000
      else if Binary32.ofBits 0x3f800000 ≤ v then Binary32.ofBits 0x3fc90fdb
      else if v ≤ Binary32.ofBits 0xbf800000 then Binary32.ofBits 0xbfc90fdb
      else Musl.asinf.asinf v := by
  rw [← Corpus.F32.half_pi_const, ← Corpus.F32.neg_half_pi_const, ← Corpus.F32.neg_one_const]; rfl

theorem safe_asin_of_isNaN {v : Binary32} (h : Binary32.isNaN v = true) :
    Id.run (Vehicle_lib.safe_asin'float.pure' v) = Binary32.ofBits 0x00000000 := by
  rw [safe_asin_pure_eq, Corpus.ite_pos h]

theorem safe_asin_of_ge_one {v : Binary32} (h : Binary32.ofBits 0x3f800000 ≤ v) :
    Id.run (Vehicle_lib.safe_asin'float.pure' v) = Binary32.ofBits 0x3fc90fdb := by
  rw [safe_asin_pure_eq, Corpus.ite_neg (by simp [(Corpus.F32.isNaN_false_of_le h).2]), Corpus.ite_pos h]

theorem safe_asin_of_le_neg_one {v : Binary32} (h : v ≤ Binary32.ofBits 0xbf800000) :
    Id.run (Vehicle_lib.safe_asin'float.pure' v) = Binary32.ofBits 0xbfc90fdb := by
  have hv := (Corpus.F32.isNaN_false_of_le h).1
  have h1 : ¬ Binary32.ofBits 0x3f800000 ≤ v := fun h' =>
    absurd (Corpus.F32.le_trans h' h) (by decide +kernel)
  rw [safe_asin_pure_eq, Corpus.ite_neg (by simp [hv]), Corpus.ite_neg h1, Corpus.ite_pos h]

/-- Case: strictly inside `(-1, 1)`, the result is `asinf v`. -/
theorem safe_asin_of_mem {v : Binary32} (h1 : Binary32.ofBits 0xbf800000 < v) (h2 : v < Binary32.ofBits 0x3f800000) :
    Id.run (Vehicle_lib.safe_asin'float.pure' v) = Musl.asinf.asinf v := by
  obtain ⟨hm, hv⟩ := Corpus.F32.isNaN_false_of_lt h1
  have hp := (Corpus.F32.isNaN_false_of_lt h2).2
  have n1 : ¬ Binary32.ofBits 0x3f800000 ≤ v := fun h' => (Corpus.F32.not_lt_iff_le hv hp).2 h' h2
  have n2 : ¬ v ≤ Binary32.ofBits 0xbf800000 := fun h' => (Corpus.F32.not_lt_iff_le hm hv).2 h' h1
  rw [safe_asin_pure_eq, Corpus.ite_neg (by simp [hv]), Corpus.ite_neg n1, Corpus.ite_neg n2]

/-- The premise on musl's `asinf` that `safe_asin` needs (plan rule 5): on `(-1, 1)` it is a number in
`[-π/2, π/2]` (the `float` words of `±π/2`). -/
def AsinfRange : Prop :=
  ∀ v : Binary32, Binary32.ofBits 0xbf800000 < v → v < Binary32.ofBits 0x3f800000 →
    Binary32.isNaN (Musl.asinf.asinf v) = false ∧ Binary32.ofBits 0xbfc90fdb ≤ Musl.asinf.asinf v ∧
      Musl.asinf.asinf v ≤ Binary32.ofBits 0x3fc90fdb

/-- Safety and Range: under `AsinfRange`, never a NaN and in `[-π/2, π/2]`. -/
theorem safe_asin_mem (hasin : AsinfRange) (v : Binary32) :
    Binary32.isNaN (Id.run (Vehicle_lib.safe_asin'float.pure' v)) = false ∧
      Binary32.ofBits 0xbfc90fdb ≤ Id.run (Vehicle_lib.safe_asin'float.pure' v) ∧
      Id.run (Vehicle_lib.safe_asin'float.pure' v) ≤ Binary32.ofBits 0x3fc90fdb := by
  cases hv : Binary32.isNaN v
  · by_cases h1 : Binary32.ofBits 0x3f800000 ≤ v
    · rw [safe_asin_of_ge_one h1]; exact ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩
    by_cases h2 : v ≤ Binary32.ofBits 0xbf800000
    · rw [safe_asin_of_le_neg_one h2]; exact ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩
    have hm : Binary32.isNaN (Binary32.ofBits 0xbf800000) = false := by decide +kernel
    have hp : Binary32.isNaN (Binary32.ofBits 0x3f800000) = false := by decide +kernel
    have l1 : Binary32.ofBits 0xbf800000 < v := by
      by_contra h; exact h2 ((Corpus.F32.not_lt_iff_le hm hv).1 h)
    have l2 : v < Binary32.ofBits 0x3f800000 := by
      by_contra h; exact h1 ((Corpus.F32.not_lt_iff_le hv hp).1 h)
    rw [safe_asin_of_mem l1 l2]; exact hasin v l1 l2
  · rw [safe_asin_of_isNaN hv]; exact ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩

/-! ## `wrap_2PI`, `wrap_PI` (float)

C++ `wrap_2PI : float (const float)`, `AP_Math.cpp:251-258`: `res = fmodf(radian, M_2PI)`, plus `M_2PI` if negative.
C++ `wrap_PI : float (const float)`, `AP_Math.cpp:270-277`: `wrap_2PI`, minus `M_2PI` above `M_PI`. `M_2PI` is the
`float` product `(float)M_PI * 2` (`0x40c90fdb`, exactly twice `M_PI`'s word `0x40490fdb`). -/

theorem wrap_2PI_eq (r : Binary32) : Vehicle_lib.wrap_2PI r = pure (Vehicle_lib.wrap_2PI.pure' r) := rfl

theorem wrap_PI_eq (r : Binary32) : Vehicle_lib.wrap_PI'float r = pure (Vehicle_lib.wrap_PI'float.pure' r) := rfl


/-- Case: the body of `wrap_2PI` as a conditional on the remainder. -/
theorem wrap_2PI_pure_eq (r : Binary32) :
    Id.run (Vehicle_lib.wrap_2PI.pure' r) =
      let res := Musl.fmodf.fmodf r (Binary32.ofBits 0x40c90fdb)
      if res < Binary32.ofBits 0x00000000 then res + Binary32.ofBits 0x40c90fdb else res := by
  rw [← Corpus.F32.two_pi_const, ← Corpus.F32.int32_zero]; rfl

/-- Case: the body of `wrap_PI` as a conditional on `wrap_2PI`. -/
theorem wrap_PI_pure_eq (r : Binary32) :
    Id.run (Vehicle_lib.wrap_PI'float.pure' r) =
      let res := Id.run (Vehicle_lib.wrap_2PI.pure' r)
      if Binary32.ofBits 0x40490fdb < res then res - Binary32.ofBits 0x40c90fdb else res := by
  rw [← Corpus.F32.two_pi_const64, ← Corpus.F32.pi_const]; rfl

/-- The premise on musl's `fmodf` that `wrap_2PI` needs (plan rule 5): the remainder of a finite value by `M_2PI` is
finite and strictly between `-M_2PI` and `M_2PI` (C's `fmodf` is exact, with the sign of the dividend). -/
def FmodfRange : Prop :=
  ∀ r : Binary32, Binary32.isFinite r = true →
    Binary32.isFinite (Musl.fmodf.fmodf r (Binary32.ofBits 0x40c90fdb)) = true ∧
      Binary32.ofBits 0xc0c90fdb < Musl.fmodf.fmodf r (Binary32.ofBits 0x40c90fdb) ∧
      Musl.fmodf.fmodf r (Binary32.ofBits 0x40c90fdb) < Binary32.ofBits 0x40c90fdb

/-- Range: under `FmodfRange`, `wrap_2PI` of a finite value is finite and in `[0, M_2PI]`. The upper end is reached
(`FINDINGS.md`: `wrap_2PI (-ε) = M_2PI`), so the range is closed. -/
theorem wrap_2PI_mem (hfmod : FmodfRange) {r : Binary32} (hr : Binary32.isFinite r = true) :
    Binary32.isFinite (Id.run (Vehicle_lib.wrap_2PI.pure' r)) = true ∧
      Binary32.ofBits 0x00000000 ≤ Id.run (Vehicle_lib.wrap_2PI.pure' r) ∧
      Id.run (Vehicle_lib.wrap_2PI.pure' r) ≤ Binary32.ofBits 0x40c90fdb := by
  obtain ⟨hf, h1, h2⟩ := hfmod r hr
  rw [wrap_2PI_pure_eq]
  simp only
  generalize Musl.fmodf.fmodf r (Binary32.ofBits 0x40c90fdb) = m at hf h1 h2
  have h2pi : Binary32.isFinite (Binary32.ofBits 0x40c90fdb) = true := by decide +kernel
  have h0 : Binary32.isFinite (Binary32.ofBits 0x00000000) = true := by decide +kernel
  have hmn := Model.isNaN_eq_false_of_isFinite_eq_true (Corpus.F32.model m) hf
  have e2pi := Corpus.F32.real_eq_of_toRat? (x := Binary32.ofBits 0x40c90fdb) (q := 13176795 / 2097152) (by decide +kernel)
  have em2pi := Corpus.F32.real_eq_of_toRat? (x := Binary32.ofBits 0xc0c90fdb) (q := -13176795 / 2097152) (by decide +kernel)
  have e0 := Corpus.F32.real_eq_of_toRat? (x := Binary32.ofBits 0x00000000) (q := 0) (by decide +kernel)
  split_ifs with hneg
  · have lo := Corpus.F32.real_lt_of_lt (by decide +kernel) hf h1
    have hi := Corpus.F32.real_lt_of_lt hf h0 hneg
    rw [em2pi] at lo; rw [e0] at hi
    exact Corpus.F32.add_mem hf h2pi h0 h2pi (by rw [e0, e2pi]; push_cast at lo ⊢; linarith)
      (by rw [e2pi]; push_cast at hi ⊢; linarith)
  · exact ⟨hf, (Corpus.F32.not_lt_iff_le hmn Corpus.F32.isNaN_zero).1 hneg, Corpus.F32.le_of_real_le hf h2pi
      (Corpus.F32.real_lt_of_lt hf h2pi h2).le⟩

/-- Range: under `FmodfRange`, `wrap_PI` of a finite value is finite and in `[-M_PI, M_PI]`. -/
theorem wrap_PI_mem (hfmod : FmodfRange) {r : Binary32} (hr : Binary32.isFinite r = true) :
    Binary32.isFinite (Id.run (Vehicle_lib.wrap_PI'float.pure' r)) = true ∧
      Binary32.ofBits 0xc0490fdb ≤ Id.run (Vehicle_lib.wrap_PI'float.pure' r) ∧
      Id.run (Vehicle_lib.wrap_PI'float.pure' r) ≤ Binary32.ofBits 0x40490fdb := by
  obtain ⟨hf, h1, h2⟩ := wrap_2PI_mem hfmod hr
  rw [wrap_PI_pure_eq]
  simp only
  generalize Id.run (Vehicle_lib.wrap_2PI.pure' r) = w at hf h1 h2
  have h2pi : Binary32.isFinite (Binary32.ofBits 0x40c90fdb) = true := by decide +kernel
  have hpi : Binary32.isFinite (Binary32.ofBits 0x40490fdb) = true := by decide +kernel
  have hmpi : Binary32.isFinite (Binary32.ofBits 0xc0490fdb) = true := by decide +kernel
  have h0 : Binary32.isFinite (Binary32.ofBits 0x00000000) = true := by decide +kernel
  have hwn := Model.isNaN_eq_false_of_isFinite_eq_true (Corpus.F32.model w) hf
  have e2pi := Corpus.F32.real_eq_of_toRat? (x := Binary32.ofBits 0x40c90fdb) (q := 13176795 / 2097152) (by decide +kernel)
  have epi := Corpus.F32.real_eq_of_toRat? (x := Binary32.ofBits 0x40490fdb) (q := 13176795 / 4194304) (by decide +kernel)
  have empi := Corpus.F32.real_eq_of_toRat? (x := Binary32.ofBits 0xc0490fdb) (q := -13176795 / 4194304) (by decide +kernel)
  have e0 := Corpus.F32.real_eq_of_toRat? (x := Binary32.ofBits 0x00000000) (q := 0) (by decide +kernel)
  split_ifs with hgt
  · have lo := Corpus.F32.real_lt_of_lt hpi hf hgt
    have hi := Corpus.F32.real_le_of_le hf h2pi h2
    rw [epi] at lo; rw [e2pi] at hi
    obtain ⟨f, l, u⟩ := Corpus.F32.sub_mem hf h2pi hmpi h0 (by rw [empi, e2pi]; push_cast at lo ⊢; linarith)
      (by rw [e0, e2pi]; push_cast at hi ⊢; linarith)
    exact ⟨f, l, Corpus.F32.le_trans u (show Binary32.ofBits 0x00000000 ≤ Binary32.ofBits 0x40490fdb by decide +kernel)⟩
  · have le := (Corpus.F32.not_lt_iff_le (by decide +kernel) hwn).1 hgt
    exact ⟨hf, Corpus.F32.le_trans (show Binary32.ofBits 0xc0490fdb ≤ Binary32.ofBits 0x00000000 by decide +kernel) h1, le⟩

/-! ## `sq`, `norm` (float)

C++ `sq : float (const float)`, `AP_Math.h:266-269` (`val * val`); `norm : float (const float, const float)`,
`AP_Math.h:291-293` (`sqrtf(sq(first) + sq(second))`). -/

theorem sq_eq (v : Binary32) : Vehicle_lib.sq v = pure (Vehicle_lib.sq.pure' v) := rfl

theorem sq_pure_eq (v : Binary32) : Id.run (Vehicle_lib.sq.pure' v) = v * v := rfl

/-- Range: a finite square is `≥ 0`. -/
theorem sq_nonneg {v : Binary32} (h : Binary32.isFinite (Id.run (Vehicle_lib.sq.pure' v)) = true) :
    Binary32.ofBits 0x00000000 ≤ Id.run (Vehicle_lib.sq.pure' v) := by
  rw [sq_pure_eq] at *
  exact Corpus.F32.mul_nonneg_of_isFinite h (mul_self_nonneg _)

/-- Meaning: a finite square is the rounded square of the real value. -/
theorem sq_toReal {v : Binary32} (h : Binary32.isFinite (Id.run (Vehicle_lib.sq.pure' v)) = true) :
    Corpus.F32.real (Id.run (Vehicle_lib.sq.pure' v)) =
      Model.roundAt Corpus.F32.fmt (Corpus.F32.real v * Corpus.F32.real v) := by
  rw [sq_pure_eq] at *
  exact Corpus.F32.real_mul h

theorem norm_eq (a b : Binary32) : Vehicle_lib.norm a b = pure (Vehicle_lib.norm.pure' a b) := rfl

theorem norm_pure_eq (a b : Binary32) :
    Id.run (Vehicle_lib.norm.pure' a b) =
      Binary32.sqrt (Id.run (Vehicle_lib.sq.pure' a) + Id.run (Vehicle_lib.sq.pure' b)) := rfl

/-- Safety and Range: when the sum of the squares is finite, `norm` is not a NaN and is `≥ 0`. -/
theorem norm_nonneg {a b : Binary32}
    (hs : Binary32.isFinite (Id.run (Vehicle_lib.sq.pure' a) + Id.run (Vehicle_lib.sq.pure' b)) = true) :
    Binary32.isNaN (Id.run (Vehicle_lib.norm.pure' a b)) = false ∧
      Binary32.ofBits 0x00000000 ≤ Id.run (Vehicle_lib.norm.pure' a b) := by
  rw [norm_pure_eq]
  apply Corpus.F32.sqrt_of_nonneg
  have hxy : Model.isFinite (Model.add (Corpus.F32.model (Id.run (Vehicle_lib.sq.pure' a)))
      (Corpus.F32.model (Id.run (Vehicle_lib.sq.pure' b)))) = true := by
    have := hs
    simp only [Binary32.isFinite, ExecFloat.Binary.isFinite, ExecFloat.Binary.toModel_hAdd] at this
    exact this
  obtain ⟨ha, hb⟩ := Model.isFinite_of_isFinite_add (by decide) hxy
  exact Corpus.F32.add_nonneg_of_isFinite hs (sq_nonneg ha) (sq_nonneg hb)

/-! ## `radians`, `degrees`, `cd_to_rad` (float)

C++ `radians : float (float)`, `AP_Math.h:232-235` (`deg * DEG_TO_RAD`); `degrees : float (float)`,
`AP_Math.h:255-258` (`rad * RAD_TO_DEG`); `cd_to_rad : float (float)`, `AP_Math.h:243-246` (`cdeg * DEG_TO_RAD * 0.01`
as `cdeg * (M_PI / 18000)`). Each constant is folded by the kernel to its `float` word. -/

theorem radians_eq (d : Binary32) : Vehicle_lib.radians d = pure (Vehicle_lib.radians.pure' d) := rfl
theorem degrees_eq (r : Binary32) : Vehicle_lib.degrees r = pure (Vehicle_lib.degrees.pure' r) := rfl
theorem cd_to_rad_eq (c : Binary32) : Vehicle_lib.cd_to_rad c = pure (Vehicle_lib.cd_to_rad.pure' c) := rfl




/-- Case: multiplication by the folded constant. -/
theorem radians_pure_eq (d : Binary32) :
    Id.run (Vehicle_lib.radians.pure' d) = d * Binary32.ofBits 0x3c8efa35 := by
  rw [← Corpus.F32.deg_to_rad_const]; rfl

theorem degrees_pure_eq (r : Binary32) :
    Id.run (Vehicle_lib.degrees.pure' r) = r * Binary32.ofBits 0x42652ee0 := by
  rw [← Corpus.F32.rad_to_deg_const]; rfl

theorem cd_to_rad_pure_eq (c : Binary32) :
    Id.run (Vehicle_lib.cd_to_rad.pure' c) = c * Binary32.ofBits 0x393702d4 := by
  rw [← Corpus.F32.cd_to_rad_const]; rfl

/-- Safety: a finite angle in degrees gives a finite angle in radians (the constant is below `1`). -/
theorem radians_isFinite {d : Binary32} (hd : Binary32.isFinite d = true) :
    Binary32.isFinite (Id.run (Vehicle_lib.radians.pure' d)) = true := by
  rw [radians_pure_eq]
  have hc : Binary32.isFinite (Binary32.ofBits 0x3c8efa35) = true := by decide +kernel
  apply Corpus.F32.isFinite_mul_of_le hd hc
  have ec := Corpus.F32.real_eq_of_toRat? (x := Binary32.ofBits 0x3c8efa35) (q := 9370165 / 536870912)
    (by decide +kernel)
  have hb := ExecFloat.Binary.abs_toReal_le_posMaxFinite_of_isFinite hd
  rw [ec]
  have : |((9370165 / 536870912 : ℚ) : ℝ)| ≤ 1 := by norm_num [abs_of_nonneg]
  calc |Corpus.F32.real d| * |((9370165 / 536870912 : ℚ) : ℝ)| ≤ |Corpus.F32.real d| * 1 :=
        mul_le_mul_of_nonneg_left this (abs_nonneg _)
    _ ≤ _ := by rw [mul_one]; exact hb

theorem cd_to_rad_isFinite {c : Binary32} (hc : Binary32.isFinite c = true) :
    Binary32.isFinite (Id.run (Vehicle_lib.cd_to_rad.pure' c)) = true := by
  rw [cd_to_rad_pure_eq]
  have hk : Binary32.isFinite (Binary32.ofBits 0x393702d4) = true := by decide +kernel
  apply Corpus.F32.isFinite_mul_of_le hc hk
  have ec := Corpus.F32.real_eq_of_toRat? (x := Binary32.ofBits 0x393702d4) (q := 2998453 / 17179869184)
    (by decide +kernel)
  have hb := ExecFloat.Binary.abs_toReal_le_posMaxFinite_of_isFinite hc
  rw [ec]
  have : |((2998453 / 17179869184 : ℚ) : ℝ)| ≤ 1 := by norm_num [abs_of_nonneg]
  calc |Corpus.F32.real c| * |((2998453 / 17179869184 : ℚ) : ℝ)| ≤ |Corpus.F32.real c| * 1 :=
        mul_le_mul_of_nonneg_left this (abs_nonneg _)
    _ ≤ _ := by rw [mul_one]; exact hb

/-- Range: a finite nonnegative angle stays nonnegative. -/
theorem radians_nonneg {d : Binary32} (hd : Binary32.isFinite d = true) (h : Binary32.ofBits 0x00000000 ≤ d) :
    Binary32.ofBits 0x00000000 ≤ Id.run (Vehicle_lib.radians.pure' d) := by
  have hf := radians_isFinite hd
  rw [radians_pure_eq] at *
  apply Corpus.F32.mul_nonneg_of_isFinite hf
  exact mul_nonneg (Corpus.F32.real_nonneg_of_le hd h)
    (Corpus.F32.real_nonneg_of_le (by decide +kernel) (by decide +kernel))

theorem cd_to_rad_nonneg {c : Binary32} (hc : Binary32.isFinite c = true) (h : Binary32.ofBits 0x00000000 ≤ c) :
    Binary32.ofBits 0x00000000 ≤ Id.run (Vehicle_lib.cd_to_rad.pure' c) := by
  have hf := cd_to_rad_isFinite hc
  rw [cd_to_rad_pure_eq] at *
  apply Corpus.F32.mul_nonneg_of_isFinite hf
  exact mul_nonneg (Corpus.F32.real_nonneg_of_le hc h)
    (Corpus.F32.real_nonneg_of_le (by decide +kernel) (by decide +kernel))

/-- Range: a finite result of `degrees` of a nonnegative angle is nonnegative (`degrees` overflows above about
`5.9e36`). -/
theorem degrees_nonneg {r : Binary32} (hf : Binary32.isFinite (Id.run (Vehicle_lib.degrees.pure' r)) = true)
    (h : Binary32.ofBits 0x00000000 ≤ r) :
    Binary32.ofBits 0x00000000 ≤ Id.run (Vehicle_lib.degrees.pure' r) := by
  rw [degrees_pure_eq] at *
  have hr := (Corpus.F32.isFinite_of_isFinite_mul hf).1
  apply Corpus.F32.mul_nonneg_of_isFinite hf
  exact mul_nonneg (Corpus.F32.real_nonneg_of_le hr h)
    (Corpus.F32.real_nonneg_of_le (by decide +kernel) (by decide +kernel))

/-- Meaning: a finite angle in radians is the rounded product of the real value and `DEG_TO_RAD`'s word. -/
theorem radians_toReal {d : Binary32} (hd : Binary32.isFinite d = true) :
    Corpus.F32.real (Id.run (Vehicle_lib.radians.pure' d)) =
      Model.roundAt Corpus.F32.fmt (Corpus.F32.real d * ((9370165 / 536870912 : ℚ) : ℝ)) := by
  have hf := radians_isFinite hd
  rw [radians_pure_eq] at *
  rw [Corpus.F32.real_mul hf,
    Corpus.F32.real_eq_of_toRat? (x := Binary32.ofBits 0x3c8efa35) (q := 9370165 / 536870912) (by decide +kernel)]

end Corpus.AP_Math

/-! ## `is_zero` of an `AP_Float`

C++ `is_zero : bool (const AP_ParamT<float, AP_PARAM_FLOAT>)`, `AP_Math.h:59`: `is_zero` of the parameter's value. -/

namespace Corpus.AP_Math

theorem is_zero_param_run {a : UInt64} (hb : PMem.inBridgeN a 4 = false) (s : PMem.Mem) :
    (Vehicle_lib.is_zero'AP_ParamT_float_AP_PARAM_FLOAT a).run s =
      (Id.run (Vehicle_lib.is_zero.pure' (Binary32.ofBits (Corpus.Mem.w32 s.m a.toNat))), s) := by
  unfold Vehicle_lib.is_zero'AP_ParamT_float_AP_PARAM_FLOAT
  simp only [StateT.run_bind, Corpus.AP_Param.operator_const_float_run, Corpus.id_bind, Corpus.id_run_eq,
    Corpus.Mem.ldF32_run hb, is_zero_eq]
  rfl

end Corpus.AP_Math

/-! ## Closing the first increment's partial entries (second increment)

The float facts these use are in `Corpus/Machine/Float.lean`, section "Rounding with overflow, negation, signs". -/

namespace Corpus.AP_Math

/-- Order: `is_equal` is symmetric (`a - b` and `b - a` are both NaN or denote opposite values). -/
theorem is_equal_comm (a b : Binary32) :
    Id.run (Vehicle_lib.is_equal'float_float.pure' a b) = Id.run (Vehicle_lib.is_equal'float_float.pure' b a) := by
  rw [is_equal_eq_is_zero, is_equal_eq_is_zero]
  cases ha : Binary32.isNaN a
  · cases hb : Binary32.isNaN b
    · obtain ⟨hn, he⟩ := Corpus.F32.sub_antisymm ha hb
      apply Bool.eq_iff_iff.2
      rw [is_zero_iff_ext, is_zero_iff_ext, hn, he, EReal.neg_lt_neg_iff, EReal.neg_lt_comm]
      exact and_congr_right fun _ => and_comm
    · rw [is_zero_of_isNaN (Corpus.F32.isNaN_sub_of_isNaN (Or.inr hb)),
        is_zero_of_isNaN (Corpus.F32.isNaN_sub_of_isNaN (Or.inl hb))]
  · rw [is_zero_of_isNaN (Corpus.F32.isNaN_sub_of_isNaN (Or.inl ha)),
      is_zero_of_isNaN (Corpus.F32.isNaN_sub_of_isNaN (Or.inr ha))]

/-- Case: `is_equal a a` holds exactly for finite `a` (`∞ - ∞` and NaN are NaN). -/
theorem is_equal_self (a : Binary32) :
    Id.run (Vehicle_lib.is_equal'float_float.pure' a a) = Binary32.isFinite a := by
  rw [is_equal_eq_is_zero]
  cases hf : Binary32.isFinite a
  · exact is_zero_of_isNaN (by rw [Corpus.F32.sub_self_isNaN, hf]; rfl)
  · rw [is_zero_iff_ext, Corpus.F32.ext_sub_self hf, Corpus.F32.sub_self_isNaN, hf]
    refine ⟨rfl, ?_, ?_⟩
    · rw [EReal.neg_lt_comm, neg_zero]; exact_mod_cast (show (0 : ℝ) < ((1 / 8388608 : ℚ) : ℝ) by norm_num)
    · exact_mod_cast (show (0 : ℝ) < ((1 / 8388608 : ℚ) : ℝ) by norm_num)

/-- Safety and Range: the square of a number is a number and is `≥ 0`, also when it overflows (`+∞`). -/
theorem sq_nonneg_of_not_isNaN {v : Binary32} (hv : Binary32.isNaN v = false) :
    Binary32.isNaN (Id.run (Vehicle_lib.sq.pure' v)) = false ∧
      Binary32.ofBits 0x00000000 ≤ Id.run (Vehicle_lib.sq.pure' v) := by
  rw [sq_pure_eq]; exact Corpus.F32.mul_self_nonneg' hv

/-- Safety and Range: for numbers `a`, `b`, `norm a b` is a number and `≥ 0`, overflow included (`+∞`). -/
theorem norm_nonneg_of_not_isNaN {a b : Binary32} (ha : Binary32.isNaN a = false) (hb : Binary32.isNaN b = false) :
    Binary32.isNaN (Id.run (Vehicle_lib.norm.pure' a b)) = false ∧
      Binary32.ofBits 0x00000000 ≤ Id.run (Vehicle_lib.norm.pure' a b) := by
  rw [norm_pure_eq]
  exact Corpus.F32.sqrt_of_nonneg (Corpus.F32.add_nonneg' (sq_nonneg_of_not_isNaN ha).2 (sq_nonneg_of_not_isNaN hb).2).2

/-! ### `radians`, `degrees`, `cd_to_rad`: odd and monotone -/

private theorem odd_of_const {k d : Binary32} (hk : Binary32.isFinite k = true)
    (hp : Binary32.ofBits 0x00000000 < k) (hd : Binary32.isNaN d = false) : (-d) * k = -(d * k) :=
  Corpus.F32.neg_mul' hd (Corpus.F32.isNaN_false_of_lt hp).2 (Corpus.F32.isNaN_mul_of_pos hd hk hp)

/-- Order: `radians` is odd, as words, on numbers (and a NaN gives a NaN, `radians_isNaN`). -/
theorem radians_odd {d : Binary32} (hd : Binary32.isNaN d = false) :
    Id.run (Vehicle_lib.radians.pure' (-d)) = -Id.run (Vehicle_lib.radians.pure' d) := by
  rw [radians_pure_eq, radians_pure_eq]; exact odd_of_const (by decide +kernel) (by decide +kernel) hd

theorem degrees_odd {r : Binary32} (hr : Binary32.isNaN r = false) :
    Id.run (Vehicle_lib.degrees.pure' (-r)) = -Id.run (Vehicle_lib.degrees.pure' r) := by
  rw [degrees_pure_eq, degrees_pure_eq]; exact odd_of_const (by decide +kernel) (by decide +kernel) hr

theorem cd_to_rad_odd {c : Binary32} (hc : Binary32.isNaN c = false) :
    Id.run (Vehicle_lib.cd_to_rad.pure' (-c)) = -Id.run (Vehicle_lib.cd_to_rad.pure' c) := by
  rw [cd_to_rad_pure_eq, cd_to_rad_pure_eq]; exact odd_of_const (by decide +kernel) (by decide +kernel) hc

/-- Safety: `radians` is a NaN exactly on a NaN. -/
theorem radians_isNaN (d : Binary32) :
    Binary32.isNaN (Id.run (Vehicle_lib.radians.pure' d)) = Binary32.isNaN d := by
  rw [radians_pure_eq]
  cases hd : Binary32.isNaN d
  · exact Corpus.F32.isNaN_mul_of_pos hd (by decide +kernel) (by decide +kernel)
  · exact Corpus.F32.isNaN_mul_of_isNaN (Or.inl hd)

theorem degrees_isNaN (r : Binary32) :
    Binary32.isNaN (Id.run (Vehicle_lib.degrees.pure' r)) = Binary32.isNaN r := by
  rw [degrees_pure_eq]
  cases hr : Binary32.isNaN r
  · exact Corpus.F32.isNaN_mul_of_pos hr (by decide +kernel) (by decide +kernel)
  · exact Corpus.F32.isNaN_mul_of_isNaN (Or.inl hr)

theorem cd_to_rad_isNaN (c : Binary32) :
    Binary32.isNaN (Id.run (Vehicle_lib.cd_to_rad.pure' c)) = Binary32.isNaN c := by
  rw [cd_to_rad_pure_eq]
  cases hc : Binary32.isNaN c
  · exact Corpus.F32.isNaN_mul_of_pos hc (by decide +kernel) (by decide +kernel)
  · exact Corpus.F32.isNaN_mul_of_isNaN (Or.inl hc)

/-- Order: `radians` is monotone (`±∞` included). -/
theorem radians_mono {d e : Binary32} (h : d ≤ e) :
    Id.run (Vehicle_lib.radians.pure' d) ≤ Id.run (Vehicle_lib.radians.pure' e) := by
  rw [radians_pure_eq, radians_pure_eq]
  exact Corpus.F32.mul_le_mul_of_pos_right' h (by decide +kernel) (by decide +kernel)

/-- Order: `degrees` is monotone, through overflow (`degrees` overflows above about `5.9e36`). -/
theorem degrees_mono {r s : Binary32} (h : r ≤ s) :
    Id.run (Vehicle_lib.degrees.pure' r) ≤ Id.run (Vehicle_lib.degrees.pure' s) := by
  rw [degrees_pure_eq, degrees_pure_eq]
  exact Corpus.F32.mul_le_mul_of_pos_right' h (by decide +kernel) (by decide +kernel)

theorem cd_to_rad_mono {c d : Binary32} (h : c ≤ d) :
    Id.run (Vehicle_lib.cd_to_rad.pure' c) ≤ Id.run (Vehicle_lib.cd_to_rad.pure' d) := by
  rw [cd_to_rad_pure_eq, cd_to_rad_pure_eq]
  exact Corpus.F32.mul_le_mul_of_pos_right' h (by decide +kernel) (by decide +kernel)

/-! ### `constrain_value_line` (float) with a NaN `amt` -/

/-- Range: a NaN `amt` gives the midpoint, which is finite and in `[low, high]` when `low + high` is finite
(FINDINGS F1: not otherwise). -/
theorem constrain_float_mem_of_isNaN {amt low high : Binary32} (line : UInt32) (hlh : low ≤ high)
    (hs : Binary32.isFinite (low + high) = true) (h : Binary32.isNaN amt = true) :
    low ≤ Id.run (Vehicle_lib.constrain_value_line'float.pure' amt low high line) ∧
      Id.run (Vehicle_lib.constrain_value_line'float.pure' amt low high line) ≤ high := by
  rw [constrain_float_of_isNaN _ _ _ h]
  exact (Corpus.F32.midpoint_mem hlh hs).2

/-- Range: for `low ≤ high` with `low + high` finite, the result is in `[low, high]` for every `amt`. -/
theorem constrain_float_mem_all {amt low high : Binary32} (line : UInt32) (hlh : low ≤ high)
    (hs : Binary32.isFinite (low + high) = true) :
    low ≤ Id.run (Vehicle_lib.constrain_value_line'float.pure' amt low high line) ∧
      Id.run (Vehicle_lib.constrain_value_line'float.pure' amt low high line) ≤ high := by
  cases h : Binary32.isNaN amt
  · exact constrain_float_mem line hlh h
  · exact constrain_float_mem_of_isNaN line hlh hs h

/-- Safety: for `low ≤ high` with `low + high` finite, the result is never a NaN. -/
theorem constrain_float_not_isNaN_all {amt low high : Binary32} (line : UInt32) (hlh : low ≤ high)
    (hs : Binary32.isFinite (low + high) = true) :
    Binary32.isNaN (Id.run (Vehicle_lib.constrain_value_line'float.pure' amt low high line)) = false :=
  (Corpus.F32.isNaN_false_of_le (constrain_float_mem_all line hlh hs (amt := amt)).1).2

/-- Order: idempotent for `low ≤ high` with `low + high` finite, for every `amt` (NaN included). -/
theorem constrain_float_idem_all {amt low high : Binary32} (line line' : UInt32) (hlh : low ≤ high)
    (hs : Binary32.isFinite (low + high) = true) :
    Id.run (Vehicle_lib.constrain_value_line'float.pure'
        (Id.run (Vehicle_lib.constrain_value_line'float.pure' amt low high line)) low high line') =
      Id.run (Vehicle_lib.constrain_value_line'float.pure' amt low high line) := by
  obtain ⟨h1, h2⟩ := constrain_float_mem_all line hlh hs (amt := amt)
  exact constrain_float_of_mem line' h1 h2

end Corpus.AP_Math

namespace Corpus.AP_Math

/-- Order: with symmetric bounds `[-M, M]` (`M ≥ 0`), `constrain_float` is odd on numbers, as words. -/
theorem constrain_float_odd {amt M : Binary32} (line line' : UInt32) (hM : Binary32.ofBits 0x00000000 ≤ M)
    (ha : Binary32.isNaN amt = false) :
    Id.run (Vehicle_lib.constrain_value_line'float.pure' (-amt) (-M) M line) =
      -Id.run (Vehicle_lib.constrain_value_line'float.pure' amt (-M) M line') := by
  have hMn := (Corpus.F32.isNaN_false_of_le hM).2
  have hnM : Binary32.isNaN (-M) = false := by rw [Corpus.F32.isNaN_neg]; exact hMn
  have hna : Binary32.isNaN (-amt) = false := by rw [Corpus.F32.isNaN_neg]; exact ha
  have hle := Corpus.F32.neg_le_self hM
  -- the two tests on `-amt`, in terms of `amt`
  have t1 : -amt < -M ↔ M < amt := Corpus.F32.neg_lt_neg_iff' ha hMn
  have t2 : M < -amt ↔ amt < -M := by
    have := Corpus.F32.neg_lt_neg_iff' (x := -M) (y := amt) hnM ha
    rw [Corpus.F32.neg_neg'] at this; exact this
  rw [constrain_float_pure_eq, constrain_float_pure_eq, hna, ha]
  simp only [Bool.false_eq_true, ite_false]
  by_cases h1 : amt < -M
  · have h1' : ¬ M < amt := fun h => by
      have hMM := Corpus.F32.lt_of_lt_of_le (Corpus.F32.lt_of_lt_of_le h (Corpus.F32.le_of_lt h1)) hle
      rw [Corpus.F32.lt_iff_ext hMn hMn] at hMM; exact lt_irrefl _ hMM
    rw [Corpus.ite_neg (fun h => h1' (t1.1 h)), Corpus.ite_pos (t2.2 h1), Corpus.ite_pos h1, Corpus.F32.neg_neg']
  · rw [Corpus.ite_neg h1]
    by_cases h2 : M < amt
    · rw [Corpus.ite_pos (t1.2 h2), Corpus.ite_pos h2]
    · rw [Corpus.ite_neg (fun h => h2 (t1.1 h)), Corpus.ite_neg (fun h => h1 (t2.1 h)), Corpus.ite_neg h2]

end Corpus.AP_Math

/-! ## `calc_lowpass_alpha_dt`, `is_positive` of an `AP_Float`, `MIN` (callees of `AC_PID::update_all`) -/

namespace Corpus.AP_Math

/-- C++ `calc_lowpass_alpha_dt : float (float, float)`, `AP_Math.cpp:418-432`. Case/Effect: the memory is
unchanged; the result is `1` for a negative `dt` or `cutoff_freq` or a zero `cutoff_freq`, `0` for a zero `dt`, else
`dt / (dt + 1 / (2π · cutoff_freq))` (`2π` the word `0x40c90fdb`). -/
theorem calc_lowpass_alpha_dt_run (dt c : Binary32) (s : PMem.Mem) :
    (Vehicle_lib.calc_lowpass_alpha_dt dt c).run s =
      ((if (Id.run (Vehicle_lib.is_negative'float.pure' dt) || Id.run (Vehicle_lib.is_negative'float.pure' c)) then
          Binary32.ofBits 0x3f800000
        else if Id.run (Vehicle_lib.is_zero.pure' c) then Binary32.ofBits 0x3f800000
        else if Id.run (Vehicle_lib.is_zero.pure' dt) then Binary32.ofBits 0x00000000
        else dt / (dt + Binary32.ofBits 0x3f800000 / (Binary32.ofBits 0x40c90fdb * c))), s) := by
  unfold Vehicle_lib.calc_lowpass_alpha_dt
  simp only [is_negative_eq, is_zero_eq, Corpus.F32.one64_const, Corpus.F32.zero64_const, Corpus.F32.two_pi_const]
  cases h1 : Id.run (Vehicle_lib.is_negative'float.pure' dt) <;> cases h2 : Id.run (Vehicle_lib.is_negative'float.pure' c) <;>
    cases h3 : Id.run (Vehicle_lib.is_zero.pure' c) <;> cases h4 : Id.run (Vehicle_lib.is_zero.pure' dt) <;>
    simp_all [StateT.run, bind, StateT.bind, pure, StateT.pure, Corpus.id_run_eq] <;> rfl

/-- C++ `is_positive : bool (const AP_ParamT<float, AP_PARAM_FLOAT>)`, `AP_Math.h:65-69`: `is_positive` of the
parameter's value; the memory unchanged. -/
theorem is_positive_param_run {a : UInt64} (hb : PMem.inBridgeN a 4 = false) (s : PMem.Mem) :
    (Vehicle_lib.is_positive'AP_ParamT_float_AP_PARAM_FLOAT a).run s =
      (Id.run (Vehicle_lib.is_positive'float.pure' (Binary32.ofBits (Corpus.Mem.w32 s.m a.toNat))), s) := by
  unfold Vehicle_lib.is_positive'AP_ParamT_float_AP_PARAM_FLOAT
  simp only [StateT.run_bind, Corpus.AP_Param.operator_const_float_run, Corpus.id_bind, Corpus.id_run_eq,
    Corpus.Mem.ldF32_run hb]
  rfl

/-- C++ `MIN : unsigned int (unsigned int, unsigned int)` (by reference), `AP_Math.h`: the address of the smaller
word (the second on a tie); the memory unchanged. -/
theorem MIN_uint_run {one two : UInt64} (h1 : PMem.inBridgeN one 4 = false) (h2 : PMem.inBridgeN two 4 = false)
    (s : PMem.Mem) :
    (Vehicle_lib.MIN'unsigned_int_unsigned_int one two).run s =
      ((if Corpus.Mem.w32 s.m one.toNat < Corpus.Mem.w32 s.m two.toNat then one else two), s) := by
  unfold Vehicle_lib.MIN'unsigned_int_unsigned_int
  simp only [StateT.run_bind, Corpus.Mem.ldU32_run h1, Corpus.id_bind, Corpus.id_run_eq, Corpus.Mem.ldU32_run h2]
  split <;> rename_i h <;> simp only [decide_eq_true_eq] at h <;> simp [h] <;> rfl

end Corpus.AP_Math

namespace Corpus.AP_Math

/-- Effect: `MIN` of two `uint32_t` (by reference) reads and writes nothing else: the state is unchanged, whatever the
addresses. -/
theorem MIN_uint_state (one two : UInt64) (s : PMem.Mem) :
    ((Vehicle_lib.MIN'unsigned_int_unsigned_int one two).run s).2 = s := by
  unfold Vehicle_lib.MIN'unsigned_int_unsigned_int
  simp only [Corpus.Mem.run_bind', Corpus.Mem.ldU32_state]
  split <;> rfl

end Corpus.AP_Math

namespace Corpus.AP_Math

/-- `is_positive` of an `AP_Float` reads and writes nothing: every precondition is kept. -/
theorem is_positive_param_triple {P : PMem.Mem → Prop} {a : UInt64} (hb : PMem.inBridgeN a 4 = false) :
    Corpus.Hoare.Triple P (Vehicle_lib.is_positive'AP_ParamT_float_AP_PARAM_FLOAT a) (fun _ => P) :=
  Corpus.Hoare.Triple.of_state fun s => congrArg Prod.snd (is_positive_param_run hb s)

end Corpus.AP_Math

/-! ## Fourth increment: the `double` and integer overloads, `norm` of three, `check_lat`/`check_lng` -/

namespace Corpus.AP_Math

/-! ### `is_zero (double)` (`ftype.h:68-74`) -/

theorem is_zero'2_eq (x : Binary64) : Vehicle_lib.is_zero'2 x = pure (Vehicle_lib.is_zero'2.pure' x) := rfl

/-- Case: `|x| < FLT_EPSILON`, compared in `double`. -/
theorem is_zero'2_pure_eq (x : Binary64) :
    Id.run (Vehicle_lib.is_zero'2.pure' x) =
      decide (Binary64.abs x < Binary32.toBinary64 (Binary32.ofBits 0x34000000)) := rfl

/-- NaN: `false`. -/
theorem is_zero'2_of_isNaN {x : Binary64} (h : Binary64.isNaN x = true) :
    Id.run (Vehicle_lib.is_zero'2.pure' x) = false := by
  rw [is_zero'2_pure_eq, decide_eq_false_iff_not]
  exact Corpus.F64.not_lt_of_isNaN_left (by rw [Corpus.F64.isNaN_abs]; exact h)

/-! ### `sq`, `norm` over `double` (`AP_Math.h`, `ftype.h`) -/

theorem sq'double_eq (v : Binary64) : Vehicle_lib.sq'double v = pure (Vehicle_lib.sq'double.pure' v) := rfl
theorem sq'double_pure_eq (v : Binary64) : Id.run (Vehicle_lib.sq'double.pure' v) = v * v := rfl
theorem sq'double_double_eq (a b : Binary64) :
    Vehicle_lib.sq'double_double a b = pure (Vehicle_lib.sq'double_double.pure' a b) := rfl
/-- Case: `sq(a, b) = sq(a) + sq(b)`. -/
theorem sq'double_double_pure_eq (a b : Binary64) :
    Id.run (Vehicle_lib.sq'double_double.pure' a b) = a * a + b * b := rfl
theorem sq'double_double_double_eq (a b c : Binary64) :
    Vehicle_lib.sq'double_double_double a b c = pure (Vehicle_lib.sq'double_double_double.pure' a b c) := rfl
/-- Case: `sq(a, b, c) = sq(a) + (sq(b) + sq(c))` (the variadic recursion associates to the right). -/
theorem sq'double_double_double_pure_eq (a b c : Binary64) :
    Id.run (Vehicle_lib.sq'double_double_double.pure' a b c) = a * a + (b * b + c * c) := rfl
theorem norm'double_double_eq (a b : Binary64) :
    Vehicle_lib.norm'double_double a b = pure (Vehicle_lib.norm'double_double.pure' a b) := rfl
theorem norm'double_double_pure_eq (a b : Binary64) :
    Id.run (Vehicle_lib.norm'double_double.pure' a b) = Binary64.sqrt (a * a + b * b) := rfl
theorem norm'double_double_double_eq (a b c : Binary64) :
    Vehicle_lib.norm'double_double_double a b c = pure (Vehicle_lib.norm'double_double_double.pure' a b c) := rfl
theorem norm'double_double_double_pure_eq (a b c : Binary64) :
    Id.run (Vehicle_lib.norm'double_double_double.pure' a b c) = Binary64.sqrt (a * a + (b * b + c * c)) := rfl

/-! ### `norm (float, float, float)` (`AP_Math.h:294-296`) -/

theorem norm'2_eq (a b c : Binary32) : Vehicle_lib.norm'2 a b c = pure (Vehicle_lib.norm'2.pure' a b c) := rfl

/-- Case: `sqrtf((sq(a) + sq(b)) + sq(c))` (this overload associates to the left). -/
theorem norm'2_pure_eq (a b c : Binary32) :
    Id.run (Vehicle_lib.norm'2.pure' a b c) = Binary32.sqrt ((a * a + b * b) + c * c) := rfl

/-- Safety and Range: for numbers `a`, `b`, `c`, a number `≥ 0`, overflow included (`+∞`). -/
theorem norm'2_nonneg_of_not_isNaN {a b c : Binary32} (ha : Binary32.isNaN a = false)
    (hb : Binary32.isNaN b = false) (hc : Binary32.isNaN c = false) :
    Binary32.isNaN (Id.run (Vehicle_lib.norm'2.pure' a b c)) = false ∧
      Binary32.ofBits 0x00000000 ≤ Id.run (Vehicle_lib.norm'2.pure' a b c) := by
  have e : Id.run (Vehicle_lib.norm'2.pure' a b c) =
      Binary32.sqrt ((Id.run (Vehicle_lib.sq.pure' a) + Id.run (Vehicle_lib.sq.pure' b)) +
        Id.run (Vehicle_lib.sq.pure' c)) := rfl
  rw [e]
  exact Corpus.F32.sqrt_of_nonneg (Corpus.F32.add_nonneg'
    (Corpus.F32.add_nonneg' (sq_nonneg_of_not_isNaN ha).2 (sq_nonneg_of_not_isNaN hb).2).2
    (sq_nonneg_of_not_isNaN hc).2).2

/-- Case: the body in terms of the code's `sq`. -/
theorem norm'2_pure_eq_norm (a b c : Binary32) :
    Id.run (Vehicle_lib.norm'2.pure' a b c) =
      Binary32.sqrt ((Id.run (Vehicle_lib.sq.pure' a) + Id.run (Vehicle_lib.sq.pure' b)) +
        Id.run (Vehicle_lib.sq.pure' c)) := rfl

/-! ### `atan2 (int, int)` (`__config`), `is_equal (double, double)`, `radians (int)` -/

theorem atan2'int_int_0_eq (y x : Int32) :
    Vehicle_lib.atan2'int_int_0 y x = pure (Vehicle_lib.atan2'int_int_0.pure' y x) := rfl
/-- Case: musl's `atan2` on the operands widened to `double`. -/
theorem atan2'int_int_0_pure_eq (y x : Int32) :
    Id.run (Vehicle_lib.atan2'int_int_0.pure' y x) = Musl.atan2.atan2 (Int32.toBinary64 y) (Int32.toBinary64 x) := rfl

theorem is_equal'double_double_eq (a b : Binary64) :
    Vehicle_lib.is_equal'double_double a b = pure (Vehicle_lib.is_equal'double_double.pure' a b) := rfl
/-- Case: the `double` overload narrows the difference to `float` and applies `is_zero` (`AP_Math.cpp:25-41`; the
`double` branch is compiled out). -/
theorem is_equal'double_double_eq_is_zero (a b : Binary64) :
    Id.run (Vehicle_lib.is_equal'double_double.pure' a b) =
      Id.run (Vehicle_lib.is_zero.pure' (Binary64.toBinary32 (a - b))) := rfl
/-- NaN: a NaN difference is not equal (whatever the narrowing gives for it). -/
theorem is_equal'double_double_of_isNaN {a b : Binary64} (h : Binary32.isNaN (Binary64.toBinary32 (a - b)) = true) :
    Id.run (Vehicle_lib.is_equal'double_double.pure' a b) = false := by
  rw [is_equal'double_double_eq_is_zero]; exact is_zero_of_isNaN h

theorem radians'2_eq (d : Int32) : Vehicle_lib.radians'2 d = pure (Vehicle_lib.radians'2.pure' d) := rfl
/-- Order: `radians (int)` is `radians (float)` of the converted integer. -/
theorem radians'2_eq_radians (d : Int32) :
    Id.run (Vehicle_lib.radians'2.pure' d) = Id.run (Vehicle_lib.radians.pure' (Int32.toBinary32 d)) := rfl

/-! ### `check_lat`, `check_lng` (float) (`location.cpp:39-46`) -/

theorem check_lat'2_eq (lat : Binary32) : Vehicle_lib.check_lat'2 lat = pure (Vehicle_lib.check_lat'2.pure' lat) := rfl

/-- Case: a latitude in degrees is valid in `[-90, 90]` (float comparisons). -/
theorem check_lat'2_iff (lat : Binary32) :
    Id.run (Vehicle_lib.check_lat'2.pure' lat) = true ↔
      Binary32.ofBits 0xc2b40000 ≤ lat ∧ lat ≤ Binary32.ofBits 0x42b40000 := by
  have e : Int32.toBinary32 (90 : Int32) = Binary32.ofBits 0x42b40000 := by decide +kernel
  have n : -(Binary32.ofBits 0x42b40000) = Binary32.ofBits 0xc2b40000 := by decide +kernel
  show decide (Binary32.abs lat ≤ Int32.toBinary32 90) = true ↔ _
  rw [decide_eq_true_iff, e, Corpus.F32.abs_le_iff (by decide +kernel), n]

/-- NaN: not a valid latitude. -/
theorem check_lat'2_of_isNaN {lat : Binary32} (h : Binary32.isNaN lat = true) :
    Id.run (Vehicle_lib.check_lat'2.pure' lat) = false := by
  rw [Bool.eq_false_iff, Ne, check_lat'2_iff]
  exact fun h' => Corpus.F32.not_le_of_isNaN_left h h'.2

theorem check_lng'2_eq (lng : Binary32) : Vehicle_lib.check_lng'2 lng = pure (Vehicle_lib.check_lng'2.pure' lng) := rfl

/-- Case: a longitude in degrees is valid in `[-180, 180]`. -/
theorem check_lng'2_iff (lng : Binary32) :
    Id.run (Vehicle_lib.check_lng'2.pure' lng) = true ↔
      Binary32.ofBits 0xc3340000 ≤ lng ∧ lng ≤ Binary32.ofBits 0x43340000 := by
  have e : Int32.toBinary32 (180 : Int32) = Binary32.ofBits 0x43340000 := by decide +kernel
  have n : -(Binary32.ofBits 0x43340000) = Binary32.ofBits 0xc3340000 := by decide +kernel
  show decide (Binary32.abs lng ≤ Int32.toBinary32 180) = true ↔ _
  rw [decide_eq_true_iff, e, Corpus.F32.abs_le_iff (by decide +kernel), n]

/-- NaN: not a valid longitude. -/
theorem check_lng'2_of_isNaN {lng : Binary32} (h : Binary32.isNaN lng = true) :
    Id.run (Vehicle_lib.check_lng'2.pure' lng) = false := by
  rw [Bool.eq_false_iff, Ne, check_lng'2_iff]
  exact fun h' => Corpus.F32.not_le_of_isNaN_left h h'.2

/-- Order: a valid latitude is a valid longitude. -/
theorem check_lng'2_of_check_lat (x : Binary32) (h : Id.run (Vehicle_lib.check_lat'2.pure' x) = true) :
    Id.run (Vehicle_lib.check_lng'2.pure' x) = true := by
  rw [check_lat'2_iff] at h
  rw [check_lng'2_iff]
  have h1 : Binary32.ofBits 0xc3340000 ≤ Binary32.ofBits 0xc2b40000 := by decide +kernel
  have h2 : Binary32.ofBits 0x42b40000 ≤ Binary32.ofBits 0x43340000 := by decide +kernel
  exact ⟨Corpus.F32.le_trans h1 h.1, Corpus.F32.le_trans h.2 h2⟩

end Corpus.AP_Math
