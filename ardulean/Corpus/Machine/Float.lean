import ArduLean.Runtime.CFloat
import FloatLib.Floats.Formats.BinaryInterchange.DirectedSemantics.Bounds
import FloatLib.Floats.Formats.BinaryInterchange.Analysis.Error

/-!
# `Binary32` as the code uses it

A thin interface over FloatLib for the corpus (Corpus/PLAN.md, `Machine/`): order and comparison through the
extended real value `ext`, NaN and infinity, abs and neg, literals. No ArduPilot function appears here. Grown on
demand: a lemma is added when a proof in `Corpus/Code/` needs it.
-/

open FloatLib.Floats (Binary32 Binary64 ExecFloat)
open FloatLib.Floats.Formats.BinaryInterchange (Model FloatFormat)

namespace Corpus

/-- `Id`'s bind is application (for unfolding the translated `pure'` bodies, which are `do` blocks in `Id`). -/
theorem id_bind {α β : Type} (x : Id α) (f : α → Id β) : x >>= f = f (Id.run x) := rfl

theorem id_run_pure {α : Type} (x : α) : Id.run (pure x : Id α) = x := rfl

theorem id_run_eq {α : Type} (x : Id α) : Id.run x = x := rfl

theorem id_pure_eq {α : Type} (x : α) : (pure x : Id α) = x := rfl

/-- `if` on a true condition (core's `if_pos`, which this toolchain deprecates). -/
theorem ite_pos {c : Prop} [Decidable c] {α : Sort _} {a b : α} (h : c) : (if c then a else b) = a := by
  simp [h]

/-- `if` on a false condition. -/
theorem ite_neg {c : Prop} [Decidable c] {α : Sort _} {a b : α} (h : ¬ c) : (if c then a else b) = b := by
  simp [h]

end Corpus

namespace Corpus.F32

/-- The model of a `Binary32` value (FloatLib's `toModel`). -/
abbrev model (x : Binary32) := ExecFloat.Binary.toModel x

/-- The extended real a `Binary32` denotes: its real value, `⊤`/`⊥` for `±∞`, and `0` for a NaN (where no
lemma below uses it). -/
noncomputable def ext (x : Binary32) : EReal := Model.toEReal (model x)

/-- The real value (FloatLib's `toReal`; `0` on NaN and `±∞`). -/
noncomputable abbrev real (x : Binary32) : ℝ := ExecFloat.Binary.toReal x

/-! ## NaN in comparisons -/

theorem isNaN_def (x : Binary32) : Binary32.isNaN x = ExecFloat.Binary.isNaN x := rfl

theorem not_lt_of_isNaN_left {x y : Binary32} (h : Binary32.isNaN x = true) : ¬ x < y :=
  ExecFloat.Binary.not_lt_of_isNaN (Or.inl h)

theorem not_lt_of_isNaN_right {x y : Binary32} (h : Binary32.isNaN y = true) : ¬ x < y :=
  ExecFloat.Binary.not_lt_of_isNaN (Or.inr h)

theorem not_le_of_isNaN_left {x y : Binary32} (h : Binary32.isNaN x = true) : ¬ x ≤ y :=
  ExecFloat.Binary.not_le_of_isNaN (Or.inl h)

theorem not_le_of_isNaN_right {x y : Binary32} (h : Binary32.isNaN y = true) : ¬ x ≤ y :=
  ExecFloat.Binary.not_le_of_isNaN (Or.inr h)

/-! ## Order through `ext` -/

theorem toEReal?_eq_some_ext {x : Binary32} (hx : Binary32.isNaN x = false) :
    Model.toEReal? (model x) = some (ext x) := by
  obtain ⟨v, hv⟩ := Model.exists_toEReal?_of_isNaN_eq_false (model x) hx
  rw [hv, ext, Model.toEReal_of_toEReal? hv]

theorem lt_iff_ext {x y : Binary32} (hx : Binary32.isNaN x = false) (hy : Binary32.isNaN y = false) :
    x < y ↔ ext x < ext y := by
  rw [ExecFloat.Binary.lt_iff_compare_eq_lt]
  exact Model.compare_eq_some_lt_iff_toEReal_lt (toEReal?_eq_some_ext hx) (toEReal?_eq_some_ext hy)

theorem le_iff_ext {x y : Binary32} (hx : Binary32.isNaN x = false) (hy : Binary32.isNaN y = false) :
    x ≤ y ↔ ext x ≤ ext y := by
  rw [ExecFloat.Binary.le_iff_compare_eq_lt_or_eq,
    Model.compare_eq_some_lt_iff_toEReal_lt (toEReal?_eq_some_ext hx) (toEReal?_eq_some_ext hy),
    Model.compare_eq_some_eq_iff_toEReal_eq (toEReal?_eq_some_ext hx) (toEReal?_eq_some_ext hy)]
  exact le_iff_lt_or_eq.symm

theorem ext_of_isFinite {x : Binary32} (hx : Binary32.isFinite x = true) : ext x = (real x : EReal) :=
  Model.toEReal_eq_coe_toReal_of_isFinite _ hx

end Corpus.F32

namespace Corpus.F32

theorem isNaN_false_of_lt {x y : Binary32} (h : x < y) :
    Binary32.isNaN x = false ∧ Binary32.isNaN y = false := by
  constructor
  · cases hx : Binary32.isNaN x
    · rfl
    · exact absurd h (not_lt_of_isNaN_left hx)
  · cases hy : Binary32.isNaN y
    · rfl
    · exact absurd h (not_lt_of_isNaN_right hy)

theorem isNaN_false_of_le {x y : Binary32} (h : x ≤ y) :
    Binary32.isNaN x = false ∧ Binary32.isNaN y = false := by
  constructor
  · cases hx : Binary32.isNaN x
    · rfl
    · exact absurd h (not_le_of_isNaN_left hx)
  · cases hy : Binary32.isNaN y
    · rfl
    · exact absurd h (not_le_of_isNaN_right hy)

theorem not_lt_iff_le {x y : Binary32} (hx : Binary32.isNaN x = false) (hy : Binary32.isNaN y = false) :
    ¬ x < y ↔ y ≤ x := by
  rw [lt_iff_ext hx hy, le_iff_ext hy hx, not_lt]

theorem le_trans {x y z : Binary32} (h1 : x ≤ y) (h2 : y ≤ z) : x ≤ z := by
  obtain ⟨hx, hy⟩ := isNaN_false_of_le h1
  have hz := (isNaN_false_of_le h2).2
  rw [le_iff_ext hx hy] at h1; rw [le_iff_ext hy hz] at h2; rw [le_iff_ext hx hz]
  exact h1.trans h2

theorem lt_of_lt_of_le {x y z : Binary32} (h1 : x < y) (h2 : y ≤ z) : x < z := by
  obtain ⟨hx, hy⟩ := isNaN_false_of_lt h1
  have hz := (isNaN_false_of_le h2).2
  rw [lt_iff_ext hx hy] at h1; rw [le_iff_ext hy hz] at h2; rw [lt_iff_ext hx hz]
  exact h1.trans_le h2

theorem lt_of_le_of_lt {x y z : Binary32} (h1 : x ≤ y) (h2 : y < z) : x < z := by
  obtain ⟨hx, hy⟩ := isNaN_false_of_le h1
  have hz := (isNaN_false_of_lt h2).2
  rw [le_iff_ext hx hy] at h1; rw [lt_iff_ext hy hz] at h2; rw [lt_iff_ext hx hz]
  exact h1.trans_lt h2

theorem le_of_lt {x y : Binary32} (h : x < y) : x ≤ y := by
  obtain ⟨hx, hy⟩ := isNaN_false_of_lt h
  rw [lt_iff_ext hx hy] at h; rw [le_iff_ext hx hy]; exact h.le

theorem le_refl_of_not_isNaN {x : Binary32} (hx : Binary32.isNaN x = false) : x ≤ x :=
  (le_iff_ext hx hx).2 le_rfl

/-- `ext` of a negation. -/
theorem ext_neg {x : Binary32} (hx : Binary32.isNaN x = false) : ext (-x) = -ext x := by
  unfold ext model
  rw [ExecFloat.Binary.toModel_neg]
  exact Model.toEReal_neg_of_isNaN_eq_false _ hx

theorem isNaN_neg (x : Binary32) : Binary32.isNaN (-x) = Binary32.isNaN x := by
  show Model.isNaN (ExecFloat.Binary.toModel (-x)) = _
  rw [ExecFloat.Binary.toModel_neg, Model.isNaN_neg]; rfl

theorem isNaN_abs (x : Binary32) : Binary32.isNaN (Binary32.abs x) = Binary32.isNaN x := by
  show Model.isNaN (ExecFloat.Binary.toModel (ExecFloat.Binary.abs x)) = _
  rw [ExecFloat.Binary.toModel_abs, Model.isNaN_abs]; rfl

/-- A non-NaN model with a clear sign bit denotes a nonnegative extended real. -/
theorem toEReal_nonneg_of_signBit {m : Model (ExecFloat.Binary.descriptor 8 23)} (hm : Model.isNaN m = false)
    (hs : Model.signBit m = false) : 0 ≤ Model.toEReal m := by
  rw [Model.toEReal_eq_ite, hm]
  simp only [Bool.false_eq_true, ite_false]
  split
  · simp [hs]
  · exact EReal.coe_nonneg.2 (Model.toReal_nonneg_of_signBit_eq_false hs)

/-- A non-NaN model with its sign bit set denotes a nonpositive extended real. -/
theorem toEReal_nonpos_of_signBit {m : Model (ExecFloat.Binary.descriptor 8 23)} (hm : Model.isNaN m = false)
    (hs : Model.signBit m = true) : Model.toEReal m ≤ 0 := by
  have h := toEReal_nonneg_of_signBit (m := Model.neg m) (by rw [Model.isNaN_neg]; exact hm)
    (by rw [Model.signBit_neg]; simp [hs])
  rw [Model.toEReal_neg_of_isNaN_eq_false m hm] at h
  exact EReal.neg_nonneg.1 h

/-- `abs` is `neg` on a value with its sign bit set and the identity otherwise. -/
theorem model_abs_eq (m : Model (ExecFloat.Binary.descriptor 8 23)) :
    Model.abs m = if Model.signBit m then Model.neg m else m := by
  unfold Model.abs Model.copySign Model.neg
  have hz : (ExecFloat.Binary.descriptor 8 23).supportsSignedZero = true := by decide
  simp only [hz, Bool.not_true, Bool.false_and, Bool.false_eq_true, ite_false, ite_true]
  cases h : Model.signBit m <;> simp [Model.signBit_posZero]

/-- `ext` of an absolute value. -/
theorem ext_abs {x : Binary32} (hx : Binary32.isNaN x = false) :
    ext (Binary32.abs x) = max (ext x) (-ext x) := by
  unfold ext model
  show Model.toEReal (ExecFloat.Binary.toModel (ExecFloat.Binary.abs x)) = _
  rw [ExecFloat.Binary.toModel_abs]
  generalize hm : ExecFloat.Binary.toModel x = m
  have hmn : Model.isNaN m = false := by rw [← hm]; exact hx
  rw [model_abs_eq]
  cases hs : Model.signBit m
  · have := toEReal_nonneg_of_signBit hmn hs
    simp only [Bool.false_eq_true, ite_false]
    exact (max_eq_left ((EReal.neg_le.2 (by simpa using this)).trans this)).symm
  · have := toEReal_nonpos_of_signBit hmn hs
    simp only [ite_true]
    rw [Model.toEReal_neg_of_isNaN_eq_false m hmn]
    exact (max_eq_right (this.trans (EReal.neg_nonneg.2 this))).symm

/-- `|x| < c` is `-c < x < c`, for every `x` (a NaN satisfies neither side). -/
theorem abs_lt_iff {x c : Binary32} (hc : Binary32.isNaN c = false) :
    Binary32.abs x < c ↔ -c < x ∧ x < c := by
  cases hx : Binary32.isNaN x
  · have hcn : Binary32.isNaN (-c) = false := by rw [isNaN_neg]; exact hc
    have hax : Binary32.isNaN (Binary32.abs x) = false := by rw [isNaN_abs]; exact hx
    rw [lt_iff_ext hax hc, lt_iff_ext hcn hx, lt_iff_ext hx hc, ext_abs hx, ext_neg hc, max_lt_iff,
      EReal.neg_lt_comm]
    exact and_comm
  · have hax : Binary32.isNaN (Binary32.abs x) = true := by rw [isNaN_abs]; exact hx
    exact iff_of_false (not_lt_of_isNaN_left hax) (fun h => not_lt_of_isNaN_right hx h.1)

end Corpus.F32

/-! ## `Binary64` and the widening `Binary32.toBinary64` -/

namespace Corpus.F64

noncomputable def ext (x : Binary64) : EReal := Model.toEReal (ExecFloat.Binary.toModel x)

theorem toEReal?_eq_some_ext {x : Binary64} (hx : Binary64.isNaN x = false) :
    Model.toEReal? (ExecFloat.Binary.toModel x) = some (ext x) := by
  obtain ⟨v, hv⟩ := Model.exists_toEReal?_of_isNaN_eq_false (ExecFloat.Binary.toModel x) hx
  rw [hv, ext, Model.toEReal_of_toEReal? hv]

theorem lt_iff_ext {x y : Binary64} (hx : Binary64.isNaN x = false) (hy : Binary64.isNaN y = false) :
    x < y ↔ ext x < ext y := by
  rw [ExecFloat.Binary.lt_iff_compare_eq_lt]
  exact Model.compare_eq_some_lt_iff_toEReal_lt (toEReal?_eq_some_ext hx) (toEReal?_eq_some_ext hy)

theorem le_iff_ext {x y : Binary64} (hx : Binary64.isNaN x = false) (hy : Binary64.isNaN y = false) :
    x ≤ y ↔ ext x ≤ ext y := by
  rw [ExecFloat.Binary.le_iff_compare_eq_lt_or_eq,
    Model.compare_eq_some_lt_iff_toEReal_lt (toEReal?_eq_some_ext hx) (toEReal?_eq_some_ext hy),
    Model.compare_eq_some_eq_iff_toEReal_eq (toEReal?_eq_some_ext hx) (toEReal?_eq_some_ext hy)]
  exact le_iff_lt_or_eq.symm

theorem not_le_of_isNaN_left {x y : Binary64} (h : Binary64.isNaN x = true) : ¬ x ≤ y :=
  ExecFloat.Binary.not_le_of_isNaN (Or.inl h)

theorem not_lt_of_isNaN_left {x y : Binary64} (h : Binary64.isNaN x = true) : ¬ x < y :=
  ExecFloat.Binary.not_lt_of_isNaN (Or.inl h)

/-- A cast of an infinity is the destination's overflow value (FloatLib's `Nearest.cast`, second branch). -/
theorem cast_of_isInf {src dst : FloatFormat} (m : Model src) (hnan : Model.isNaN m = false)
    (hinf : Model.isInf m = true) :
    Model.cast src dst m = Model.nativeOverflow dst (Model.signBit m) := by
  unfold Model.cast Model.Internal.Nearest.cast
  simp only [hnan, hinf, Bool.false_eq_true, dite_false, dite_true]

theorem toModel_toBinary64 (x : Binary32) :
    ExecFloat.Binary.toModel (Binary32.toBinary64 x) =
      Model.cast (ExecFloat.Binary.descriptor 8 23) FloatFormat.binary64 (ExecFloat.Binary.toModel x) :=
  ExecFloat.Binary.toModel_ofModel _

/-- The largest finite `Binary32` is below the largest finite `Binary64`. -/
theorem posMaxFinite_le :
    Model.toReal (Model.posMaxFinite (ExecFloat.Binary.descriptor 8 23)) ≤
      Model.toReal (Model.posMaxFinite FloatFormat.binary64) := by
  rw [Model.Algebraic.toReal_of_toRat?_eq_some (q := 340282346638528859811704183484516925440) (by decide +kernel),
    Model.Algebraic.toReal_of_toRat?_eq_some
      (q := 179769313486231570814527423731704356798070567525844996598917476803157260780028538760589558632766878171540458953514382464234321326889464182768467546703537516986049910576551282076245490090389328944075868508455133942304583236903222948165808559332123348274797826204144723168738177180919299881250404026184124858368) (by decide +kernel)]
  norm_num

/-- The widening keeps NaN-ness. -/
theorem isNaN_toBinary64 (x : Binary32) : Binary64.isNaN (Binary32.toBinary64 x) = Binary32.isNaN x := by
  show Model.isNaN (ExecFloat.Binary.toModel (Binary32.toBinary64 x)) = Model.isNaN (ExecFloat.Binary.toModel x)
  rw [toModel_toBinary64]
  generalize ExecFloat.Binary.toModel x = m
  cases hnan : Model.isNaN m
  · cases hinf : Model.isInf m
    · have hfin := Model.isFinite_eq_true_of_isNaN_eq_false_of_isInf_eq_false m hnan hinf
      have hb : |Model.toReal m| ≤ Model.toReal (Model.posMaxFinite FloatFormat.binary64) :=
        (Model.abs_toReal_le_posMaxFinite_of_isFinite m hfin).trans posMaxFinite_le
      exact Model.isNaN_eq_false_of_isFinite_eq_true _
        (Model.isFinite_cast_of_abs_toReal_le_posMaxFinite m (by decide) hfin hb)
    · rw [cast_of_isInf m hnan hinf, Model.nativeOverflow_eq_signedInf_of_isIEEE _ (by decide)]
      cases Model.signBit m
      · exact Model.isNaN_posInf _
      · exact Model.isNaN_negInf _
  · rw [Model.cast_of_isNaN m hnan]
    exact Model.isNaN_propagatedNaN _ _ _ (by decide)

/-- The widening is exact: it keeps the extended real value. -/
theorem ext_toBinary64 {x : Binary32} (hx : Binary32.isNaN x = false) :
    ext (Binary32.toBinary64 x) = Corpus.F32.ext x := by
  unfold ext Corpus.F32.ext Corpus.F32.model
  rw [toModel_toBinary64]
  generalize hm : ExecFloat.Binary.toModel x = m
  have hnan : Model.isNaN m = false := by rw [← hm]; exact hx
  cases hinf : Model.isInf m
  · have hfin := Model.isFinite_eq_true_of_isNaN_eq_false_of_isInf_eq_false m hnan hinf
    have hb : |Model.toReal m| ≤ Model.toReal (Model.posMaxFinite FloatFormat.binary64) :=
      (Model.abs_toReal_le_posMaxFinite_of_isFinite m hfin).trans posMaxFinite_le
    have hc := Model.isFinite_cast_of_abs_toReal_le_posMaxFinite m (by decide) hfin hb
    have e1 := Model.toEReal_eq_coe_toReal_of_isFinite _ hc
    have e2 := Model.cast_exact_of_gridExtension m (by decide) (by decide) (by decide) hc
    rw [Model.toEReal_eq_coe_toReal_of_isFinite _ hfin]
    exact e1.trans (by rw [e2])
  · rw [Model.toEReal_eq_ite m, hnan, hinf]
    rw [cast_of_isInf m hnan hinf, Model.nativeOverflow_eq_signedInf_of_isIEEE _ (by decide)]
    cases Model.signBit m
    · exact Model.toEReal_posInf FloatFormat.binary64 (by decide)
    · exact Model.toEReal_negInf FloatFormat.binary64 (by decide)

end Corpus.F64

/-! ## Literals

The words the code writes for its constants (`Binary32.ofBits 0x…`, `Int32.toBinary32 n`, `Binary64.toBinary32 …`),
evaluated by the kernel (`decide +kernel` on FloatLib's executable operations), and the extended reals they denote
(through FloatLib's computable `toRat?`). -/

namespace Corpus.F32

theorem ext_eq_of_toRat? {x : Binary32} {q : ℚ} (h : ExecFloat.Binary.toRat? x = some q) :
    ext x = ((q : ℝ) : EReal) := by
  rw [ext_of_isFinite (Model.Algebraic.isFinite_of_toRat?_eq_some h)]
  exact congrArg _ (ExecFloat.Binary.toReal_of_toRat?_eq_some h)

theorem int32_zero : Int32.toBinary32 (0 : Int32) = Binary32.ofBits 0x00000000 := by decide +kernel
theorem int32_one : Int32.toBinary32 (1 : Int32) = Binary32.ofBits 0x3f800000 := by decide +kernel
theorem int32_two : Int32.toBinary32 (2 : Int32) = Binary32.ofBits 0x40000000 := by decide +kernel

/-- `FLT_EPSILON` (`2⁻²³`), the threshold of `is_zero`, `is_positive`, `is_negative`, `is_equal`. -/
theorem ext_eps : ext (Binary32.ofBits 0x34000000) = (((1 / 8388608 : ℚ) : ℝ) : EReal) :=
  ext_eq_of_toRat? (by decide +kernel)

theorem neg_eps : -(Binary32.ofBits 0x34000000) = Binary32.ofBits 0xb4000000 := by decide +kernel

theorem isNaN_eps : Binary32.isNaN (Binary32.ofBits 0x34000000) = false := by decide +kernel

theorem ext_zero : ext (Binary32.ofBits 0x00000000) = 0 := by
  rw [ext_eq_of_toRat? (q := 0) (by decide +kernel)]; simp

theorem isNaN_zero : Binary32.isNaN (Binary32.ofBits 0x00000000) = false := by decide +kernel

end Corpus.F32

namespace Corpus.F64

theorem ext_eq_of_toRat? {x : Binary64} {q : ℚ} (h : ExecFloat.Binary.toRat? x = some q) :
    ext x = ((q : ℝ) : EReal) := by
  rw [ext, Model.toEReal_eq_coe_toReal_of_isFinite _ (Model.Algebraic.isFinite_of_toRat?_eq_some h)]
  exact congrArg _ (ExecFloat.Binary.toReal_of_toRat?_eq_some h)

end Corpus.F64

/-! ## Infinities on the bit pattern, square root -/

namespace Corpus.F32

/-- FloatLib's `isInf` on the bit pattern: the bits below the sign are `0x7f800000`. -/
theorem isInf_toModel (x : Binary32) :
    Model.isInf (ExecFloat.Binary.toModel x) = ((Binary32.toBits x &&& 0x7fffffff) == 0x7f800000) := by
  have hb : (ExecFloat.Binary.toModel x).bits.toNat = (Binary32.toBits x).toNat := rfl
  have hand : (Binary32.toBits x &&& 0x7fffffff).toNat = (Binary32.toBits x).toNat % 2 ^ 31 := by
    rw [UInt32.toNat_and]; exact Nat.and_two_pow_sub_one_eq_mod _ 31
  have hdec : ((Binary32.toBits x &&& 0x7fffffff) == 0x7f800000) =
      decide ((Binary32.toBits x).toNat % 2 ^ 31 = 0x7f800000) := by
    rw [Bool.eq_iff_iff]
    simp only [beq_iff_eq, decide_eq_true_eq, ← UInt32.toNat_inj, hand, UInt32.reduceToNat]
  rw [hdec]
  generalize ExecFloat.Binary.toModel x = m at *
  generalize (Binary32.toBits x).toNat = n at *
  subst hb
  show Model.IEEE.isInf m = _
  simp only [Model.IEEE.isInf, CFloat.Compare.expField_eq, CFloat.Compare.fracField_eq,
    FloatFormat.expAllOnesNat]
  generalize BitVec.toNat m.bits = n at *
  rw [Bool.eq_iff_iff]
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq]
  omega

theorem ofBits_toBits (x : Binary32) : Binary32.ofBits (Binary32.toBits x) = x :=
  ExecFloat.Binary.ofBits32_toBits32 x

/-- An infinity with a clear sign bit is `+∞` (the word `0x7f800000`). -/
theorem eq_posInf {x : Binary32} (hinf : Model.isInf (model x) = true)
    (hs : Model.signBit (model x) = false) : x = Binary32.ofBits 0x7f800000 := by
  rw [isInf_toModel, beq_iff_eq] at hinf
  rw [Binary32.signBit_toModel, decide_eq_false_iff_not] at hs
  rw [← ofBits_toBits x]
  congr 1
  apply UInt32.toNat_inj.1
  have hand : (Binary32.toBits x &&& 0x7fffffff).toNat = (Binary32.toBits x).toNat % 2 ^ 31 := by
    rw [UInt32.toNat_and]; exact Nat.and_two_pow_sub_one_eq_mod _ 31
  have h1 := congrArg UInt32.toNat hinf
  rw [hand] at h1
  simp only [UInt32.le_iff_toNat_le, UInt32.reduceToNat] at hs h1 ⊢
  have := UInt32.toNat_lt (Binary32.toBits x)
  omega

/-- An infinity with its sign bit set is `-∞` (the word `0xff800000`). -/
theorem eq_negInf {x : Binary32} (hinf : Model.isInf (model x) = true)
    (hs : Model.signBit (model x) = true) : x = Binary32.ofBits 0xff800000 := by
  rw [isInf_toModel, beq_iff_eq] at hinf
  rw [Binary32.signBit_toModel, decide_eq_true_iff] at hs
  rw [← ofBits_toBits x]
  congr 1
  apply UInt32.toNat_inj.1
  have hand : (Binary32.toBits x &&& 0x7fffffff).toNat = (Binary32.toBits x).toNat % 2 ^ 31 := by
    rw [UInt32.toNat_and]; exact Nat.and_two_pow_sub_one_eq_mod _ 31
  have h1 := congrArg UInt32.toNat hinf
  rw [hand] at h1
  simp only [UInt32.le_iff_toNat_le, UInt32.reduceToNat] at hs h1 ⊢
  have := UInt32.toNat_lt (Binary32.toBits x)
  omega

/-- Every non-NaN value is finite, `+∞` or `-∞`. -/
theorem finite_or_inf {x : Binary32} (hx : Binary32.isNaN x = false) :
    Binary32.isFinite x = true ∨ x = Binary32.ofBits 0x7f800000 ∨ x = Binary32.ofBits 0xff800000 := by
  cases hinf : Model.isInf (model x)
  · exact Or.inl (Model.isFinite_eq_true_of_isNaN_eq_false_of_isInf_eq_false (model x) hx hinf)
  · cases hs : Model.signBit (model x)
    · exact Or.inr (Or.inl (eq_posInf hinf hs))
    · exact Or.inr (Or.inr (eq_negInf hinf hs))

theorem ext_posInf : ext (Binary32.ofBits 0x7f800000) = ⊤ := by
  unfold ext model
  rw [Model.toEReal_eq_ite]
  have h1 : Model.isNaN (ExecFloat.Binary.toModel (Binary32.ofBits 0x7f800000)) = false := by decide +kernel
  have h2 : Model.isInf (ExecFloat.Binary.toModel (Binary32.ofBits 0x7f800000)) = true := by decide +kernel
  have h3 : Model.signBit (ExecFloat.Binary.toModel (Binary32.ofBits 0x7f800000)) = false := by decide +kernel
  simp [h1, h2, h3]

theorem ext_negInf : ext (Binary32.ofBits 0xff800000) = ⊥ := by
  unfold ext model
  rw [Model.toEReal_eq_ite]
  have h1 : Model.isNaN (ExecFloat.Binary.toModel (Binary32.ofBits 0xff800000)) = false := by decide +kernel
  have h2 : Model.isInf (ExecFloat.Binary.toModel (Binary32.ofBits 0xff800000)) = true := by decide +kernel
  have h3 : Model.signBit (ExecFloat.Binary.toModel (Binary32.ofBits 0xff800000)) = true := by decide +kernel
  simp [h1, h2, h3]

theorem sqrt_posInf : Binary32.sqrt (Binary32.ofBits 0x7f800000) = Binary32.ofBits 0x7f800000 := by
  decide +kernel

/-- The square root of a nonnegative value (`-0`, `+∞` included) is not a NaN, and is nonnegative. -/
theorem sqrt_of_nonneg {x : Binary32} (h : Binary32.ofBits 0x00000000 ≤ x) :
    Binary32.isNaN (Binary32.sqrt x) = false ∧ Binary32.ofBits 0x00000000 ≤ Binary32.sqrt x := by
  have hx := (isNaN_false_of_le h).2
  rw [le_iff_ext isNaN_zero hx, ext_zero] at h
  rcases finite_or_inf hx with hf | hp | hn
  · have hr : 0 ≤ real x := by
      rw [ext_of_isFinite hf] at h; exact_mod_cast h
    have hd := ExecFloat.Binary.isZero_or_signBit_eq_false_of_toReal_nonneg hf hr
    have hsf : Binary32.isFinite (Binary32.sqrt x) = true := ExecFloat.Binary.isFinite_sqrt hf hd
    have hsn : Binary32.isNaN (Binary32.sqrt x) = false := Model.isNaN_eq_false_of_isFinite_eq_true (model (Binary32.sqrt x)) hsf
    refine ⟨hsn, ?_⟩
    rw [le_iff_ext isNaN_zero hsn, ext_zero, ext_of_isFinite hsf]
    have : 0 ≤ real (Binary32.sqrt x) := by
      show 0 ≤ ExecFloat.Binary.toReal (ExecFloat.Binary.sqrt x)
      rw [ExecFloat.Binary.toReal_sqrt_eq_roundAt hf hd]
      have := Model.roundAt_mono (ExecFloat.Binary.descriptor 8 23) (Real.sqrt_nonneg (real x))
      rwa [Model.roundAt_zero] at this
    exact_mod_cast this
  · subst hp; rw [sqrt_posInf]; exact ⟨by decide +kernel, by decide +kernel⟩
  · subst hn; rw [ext_negInf] at h; simp at h

end Corpus.F32

/-! ## Rounding between two floats

Nearest rounding is monotone and fixes floats, so an exact result between two finite floats rounds to a float between
them; and a result that small does not overflow. -/

namespace Corpus.F32

abbrev fmt := ExecFloat.Binary.descriptor 8 23

theorem roundAt_mem {lo hi : Binary32} (hlo : Binary32.isFinite lo = true) (hhi : Binary32.isFinite hi = true)
    {r : ℝ} (h1 : real lo ≤ r) (h2 : r ≤ real hi) :
    real lo ≤ Model.roundAt fmt r ∧ Model.roundAt fmt r ≤ real hi := by
  have e1 : Model.roundAt fmt (real lo) = real lo := Model.roundAt_toReal_eq (model lo) hlo
  have e2 : Model.roundAt fmt (real hi) = real hi := Model.roundAt_toReal_eq (model hi) hhi
  exact ⟨e1.symm.trans_le (Model.roundAt_mono fmt h1), (Model.roundAt_mono fmt h2).trans_eq e2⟩

theorem abs_le_posMax_of_mem {lo hi : Binary32} (hlo : Binary32.isFinite lo = true)
    (hhi : Binary32.isFinite hi = true) {r : ℝ} (h1 : real lo ≤ r) (h2 : r ≤ real hi) :
    |r| ≤ Model.toReal (Model.posMaxFinite fmt) := by
  have a1 := ExecFloat.Binary.abs_toReal_le_posMaxFinite_of_isFinite hlo
  have a2 := ExecFloat.Binary.abs_toReal_le_posMaxFinite_of_isFinite hhi
  rw [abs_le] at a1 a2 ⊢
  constructor <;> linarith [a1.1, a2.2]

theorem le_of_real_le {x y : Binary32} (hx : Binary32.isFinite x = true) (hy : Binary32.isFinite y = true)
    (h : real x ≤ real y) : x ≤ y := by
  rw [le_iff_ext (Model.isNaN_eq_false_of_isFinite_eq_true (model x) hx)
    (Model.isNaN_eq_false_of_isFinite_eq_true (model y) hy), ext_of_isFinite hx, ext_of_isFinite hy]
  exact_mod_cast h

/-- A sum whose exact value lies between two finite floats is finite and lies between them. -/
theorem add_mem {x y lo hi : Binary32} (hx : Binary32.isFinite x = true) (hy : Binary32.isFinite y = true)
    (hlo : Binary32.isFinite lo = true) (hhi : Binary32.isFinite hi = true)
    (h1 : real lo ≤ real x + real y) (h2 : real x + real y ≤ real hi) :
    Binary32.isFinite (x + y) = true ∧ lo ≤ x + y ∧ x + y ≤ hi := by
  have hf : Binary32.isFinite (x + y) = true := by
    show Model.isFinite (ExecFloat.Binary.toModel (x + y)) = true
    simp only [ExecFloat.Binary.toModel_hAdd]
    exact Model.isFinite_add_of_abs_toReal_add_le_posMaxFinite _ _ (by decide) hx hy
      (abs_le_posMax_of_mem hlo hhi h1 h2)
  have hr : real (x + y) = Model.roundAt fmt (real x + real y) := ExecFloat.Binary.toReal_add_eq_roundAt hf
  obtain ⟨m1, m2⟩ := roundAt_mem hlo hhi h1 h2
  exact ⟨hf, le_of_real_le hlo hf (hr ▸ m1), le_of_real_le hf hhi (hr ▸ m2)⟩

/-- A difference whose exact value lies between two finite floats is finite and lies between them. -/
theorem sub_mem {x y lo hi : Binary32} (hx : Binary32.isFinite x = true) (hy : Binary32.isFinite y = true)
    (hlo : Binary32.isFinite lo = true) (hhi : Binary32.isFinite hi = true)
    (h1 : real lo ≤ real x - real y) (h2 : real x - real y ≤ real hi) :
    Binary32.isFinite (x - y) = true ∧ lo ≤ x - y ∧ x - y ≤ hi := by
  have hf : Binary32.isFinite (x - y) = true := by
    show Model.isFinite (ExecFloat.Binary.toModel (x - y)) = true
    simp only [ExecFloat.Binary.toModel_hSub]
    exact Model.isFinite_sub_of_abs_toReal_sub_le_posMaxFinite _ _ (by decide) hx hy
      (abs_le_posMax_of_mem hlo hhi h1 h2)
  have hr : real (x - y) = Model.roundAt fmt (real x - real y) := ExecFloat.Binary.toReal_sub_eq_roundAt hf
  obtain ⟨m1, m2⟩ := roundAt_mem hlo hhi h1 h2
  exact ⟨hf, le_of_real_le hlo hf (hr ▸ m1), le_of_real_le hf hhi (hr ▸ m2)⟩

theorem real_le_of_le {x y : Binary32} (hx : Binary32.isFinite x = true) (hy : Binary32.isFinite y = true)
    (h : x ≤ y) : real x ≤ real y := by
  rw [le_iff_ext (Model.isNaN_eq_false_of_isFinite_eq_true (model x) hx)
    (Model.isNaN_eq_false_of_isFinite_eq_true (model y) hy), ext_of_isFinite hx, ext_of_isFinite hy] at h
  exact_mod_cast h

theorem real_lt_of_lt {x y : Binary32} (hx : Binary32.isFinite x = true) (hy : Binary32.isFinite y = true)
    (h : x < y) : real x < real y := by
  rw [lt_iff_ext (Model.isNaN_eq_false_of_isFinite_eq_true (model x) hx)
    (Model.isNaN_eq_false_of_isFinite_eq_true (model y) hy), ext_of_isFinite hx, ext_of_isFinite hy] at h
  exact_mod_cast h

theorem real_eq_of_toRat? {x : Binary32} {q : ℚ} (h : ExecFloat.Binary.toRat? x = some q) : real x = q :=
  ExecFloat.Binary.toReal_of_toRat?_eq_some h

theorem isFinite_of_toRat? {x : Binary32} {q : ℚ} (h : ExecFloat.Binary.toRat? x = some q) :
    Binary32.isFinite x = true :=
  Model.Algebraic.isFinite_of_toRat?_eq_some h

end Corpus.F32

/-! ## Products -/

namespace Corpus.F32

theorem isFinite_of_isFinite_mul {x y : Binary32} (h : Binary32.isFinite (x * y) = true) :
    Binary32.isFinite x = true ∧ Binary32.isFinite y = true := by
  have h' : Model.isFinite (Model.mul (model x) (model y)) = true := by
    have := h
    simp only [Binary32.isFinite, ExecFloat.Binary.isFinite, ExecFloat.Binary.toModel_hMul] at this
    exact this
  exact Model.isFinite_of_isFinite_mul (by decide) h'

theorem isFinite_mul_of_le {x y : Binary32} (hx : Binary32.isFinite x = true) (hy : Binary32.isFinite y = true)
    (h : |real x| * |real y| ≤ Model.toReal (Model.posMaxFinite fmt)) : Binary32.isFinite (x * y) = true := by
  show Model.isFinite (ExecFloat.Binary.toModel (x * y)) = true
  simp only [ExecFloat.Binary.toModel_hMul]
  exact Model.isFinite_mul_of_abs_mul_le_posMaxFinite _ _ (by decide) hx hy h

/-- A finite product whose exact value is nonnegative is `≥ 0` (rounding is monotone and fixes `0`). -/
theorem mul_nonneg_of_isFinite {x y : Binary32} (hr : Binary32.isFinite (x * y) = true)
    (h : 0 ≤ real x * real y) : Binary32.ofBits 0x00000000 ≤ x * y := by
  have e : real (x * y) = Model.roundAt fmt (real x * real y) := ExecFloat.Binary.toReal_mul_eq_roundAt hr
  have h0 : Binary32.isFinite (Binary32.ofBits 0x00000000) = true := by decide +kernel
  apply le_of_real_le h0 hr
  rw [e, real_eq_of_toRat? (q := 0) (by decide +kernel)]
  have := Model.roundAt_mono fmt h
  rw [Model.roundAt_zero] at this
  exact_mod_cast this

theorem real_nonneg_of_le {x : Binary32} (hx : Binary32.isFinite x = true) (h : Binary32.ofBits 0x00000000 ≤ x) :
    0 ≤ real x := by
  have := real_le_of_le (by decide +kernel) hx h
  rwa [real_eq_of_toRat? (q := 0) (by decide +kernel), Rat.cast_zero] at this

/-- A finite sum of two nonnegative values is nonnegative. -/
theorem add_nonneg_of_isFinite {x y : Binary32} (hr : Binary32.isFinite (x + y) = true)
    (h1 : Binary32.ofBits 0x00000000 ≤ x) (h2 : Binary32.ofBits 0x00000000 ≤ y) :
    Binary32.ofBits 0x00000000 ≤ x + y := by
  have hn : Binary32.isNaN (x + y) = false := Model.isNaN_eq_false_of_isFinite_eq_true (model (x + y)) hr
  have hxn := (isNaN_false_of_le h1).2
  have hyn := (isNaN_false_of_le h2).2
  have hxy : Model.isFinite (Model.add (model x) (model y)) = true := by
    have := hr
    simp only [Binary32.isFinite, ExecFloat.Binary.isFinite, ExecFloat.Binary.toModel_hAdd] at this
    exact this
  obtain ⟨hx, hy⟩ := Model.isFinite_of_isFinite_add (by decide) hxy
  apply le_of_real_le (by decide +kernel) hr
  have e : real (x + y) = Model.roundAt fmt (real x + real y) := ExecFloat.Binary.toReal_add_eq_roundAt hr
  rw [e, real_eq_of_toRat? (q := 0) (by decide +kernel), Rat.cast_zero]
  have := Model.roundAt_mono fmt (add_nonneg (real_nonneg_of_le hx h1) (real_nonneg_of_le hy h2))
  rwa [Model.roundAt_zero] at this

end Corpus.F32

/-! ## The four operations as rounded real operations (stated with `real`, for rewriting) -/

namespace Corpus.F32

theorem real_add {x y : Binary32} (h : Binary32.isFinite (x + y) = true) :
    real (x + y) = Model.roundAt fmt (real x + real y) := ExecFloat.Binary.toReal_add_eq_roundAt h

theorem real_sub {x y : Binary32} (h : Binary32.isFinite (x - y) = true) :
    real (x - y) = Model.roundAt fmt (real x - real y) := ExecFloat.Binary.toReal_sub_eq_roundAt h

theorem real_mul {x y : Binary32} (h : Binary32.isFinite (x * y) = true) :
    real (x * y) = Model.roundAt fmt (real x * real y) := ExecFloat.Binary.toReal_mul_eq_roundAt h

theorem real_div {x y : Binary32} (hy : Binary32.isFinite y = true) (h : Binary32.isFinite (x / y) = true) :
    real (x / y) = Model.roundAt fmt (real x / real y) := ExecFloat.Binary.toReal_div_eq_roundAt hy h

end Corpus.F32

/-! ## Negation and division, the midpoint of `[-M, M]` -/

namespace Corpus.F32

theorem isFinite_neg (x : Binary32) : Binary32.isFinite (-x) = Binary32.isFinite x :=
  ExecFloat.Binary.isFinite_neg x

theorem real_neg {x : Binary32} (hx : Binary32.isFinite x = true) : real (-x) = -real x := by
  show Model.toReal (ExecFloat.Binary.toModel (-x)) = -Model.toReal (ExecFloat.Binary.toModel x)
  rw [ExecFloat.Binary.toModel_neg]
  exact Model.toReal_neg _ hx

/-- A quotient whose exact value lies between two finite floats is finite and lies between them. -/
theorem div_mem {x y lo hi : Binary32} (hx : Binary32.isFinite x = true) (hy : Binary32.isFinite y = true)
    (hy0 : Model.isZero (model y) = false)
    (hlo : Binary32.isFinite lo = true) (hhi : Binary32.isFinite hi = true)
    (h1 : real lo ≤ real x / real y) (h2 : real x / real y ≤ real hi) :
    Binary32.isFinite (x / y) = true ∧ lo ≤ x / y ∧ x / y ≤ hi := by
  have hf : Binary32.isFinite (x / y) = true := by
    show Model.isFinite (ExecFloat.Binary.toModel (x / y)) = true
    simp only [ExecFloat.Binary.toModel_hDiv]
    exact Model.isFinite_div_of_abs_div_le_posMaxFinite _ _ (by decide) hx hy hy0
      (abs_le_posMax_of_mem hlo hhi h1 h2)
  have hr : real (x / y) = Model.roundAt fmt (real x / real y) := real_div hy hf
  obtain ⟨m1, m2⟩ := roundAt_mem hlo hhi h1 h2
  exact ⟨hf, le_of_real_le hlo hf (hr ▸ m1), le_of_real_le hf hhi (hr ▸ m2)⟩

/-- For a finite `M ≥ 0`, the midpoint `(-M + M) / 2` (what `constrain_float` returns for a NaN between `-M` and
`M`) is a zero, so it lies in `[-M, M]`. -/
theorem midpoint_neg_self_mem {M : Binary32} (hf : Binary32.isFinite M = true)
    (h0 : Binary32.ofBits 0x00000000 ≤ M) :
    Binary32.isFinite ((-M + M) / Binary32.ofBits 0x40000000) = true ∧
      -M ≤ (-M + M) / Binary32.ofBits 0x40000000 ∧ (-M + M) / Binary32.ofBits 0x40000000 ≤ M := by
  have hz : Binary32.isFinite (Binary32.ofBits 0x00000000) = true := by decide +kernel
  have e0 : real (Binary32.ofBits 0x00000000) = 0 := by
    rw [real_eq_of_toRat? (q := 0) (by decide +kernel)]; simp
  have hnf : Binary32.isFinite (-M) = true := by rw [isFinite_neg]; exact hf
  obtain ⟨af, a1, a2⟩ := add_mem hnf hf hz hz (by rw [e0, real_neg hf]; simp) (by rw [e0, real_neg hf]; simp)
  have ha0 : real (-M + M) = 0 := by
    have l := real_le_of_le hz af a1
    have u := real_le_of_le af hz a2
    rw [e0] at l u; linarith
  have h2f : Binary32.isFinite (Binary32.ofBits 0x40000000) = true := by decide +kernel
  obtain ⟨qf, q1, q2⟩ := div_mem af h2f (by decide +kernel) hz hz (by rw [ha0, e0]; simp) (by rw [ha0, e0]; simp)
  have hMn := (isNaN_false_of_le h0).2
  have hmM : -M ≤ Binary32.ofBits 0x00000000 := by
    have hnn : Binary32.isNaN (-M) = false := by rw [isNaN_neg]; exact hMn
    rw [le_iff_ext hnn isNaN_zero, ext_neg hMn, ext_zero]
    rw [le_iff_ext isNaN_zero hMn, ext_zero] at h0
    exact EReal.neg_le_zero.2 h0
  exact ⟨qf, le_trans hmM q1, le_trans q2 h0⟩

theorem neg_le_self {M : Binary32} (h0 : Binary32.ofBits 0x00000000 ≤ M) : -M ≤ M := by
  have hMn := (isNaN_false_of_le h0).2
  have hnn : Binary32.isNaN (-M) = false := by rw [isNaN_neg]; exact hMn
  rw [le_iff_ext hnn hMn, ext_neg hMn]
  rw [le_iff_ext isNaN_zero hMn, ext_zero] at h0
  exact (EReal.neg_le.2 (by simpa using h0)).trans h0

end Corpus.F32

/-! ## The constants the code folds (its `double` and `float` literal expressions), evaluated by the kernel -/

namespace Corpus.F32

theorem is_negative_const :
    (-(Binary64.ofBits 0x3ff0000000000000)) * Binary32.toBinary64 (Binary32.ofBits 0x34000000) =
      Binary64.ofBits 0xbe80000000000000 := by decide +kernel


theorem two_pi_const :
    Binary64.toBinary32 (Binary64.ofBits 0x400921fb54442d18) * Int32.toBinary32 ((2 : Int32)) =
      Binary32.ofBits 0x40c90fdb := by decide +kernel

theorem pi_const : Binary64.toBinary32 (Binary64.ofBits 0x400921fb54442d18) = Binary32.ofBits 0x40490fdb := by
  decide +kernel

theorem two_pi_const64 :
    Binary64.toBinary32 ((Binary64.ofBits 0x400921fb54442d18) * (Int32.toBinary64 ((2 : Int32)))) =
      Binary32.ofBits 0x40c90fdb := by decide +kernel

theorem deg_to_rad_const :
    Binary64.toBinary32 (Binary64.ofBits 0x400921fb54442d18) / Binary32.ofBits 0x43340000 =
      Binary32.ofBits 0x3c8efa35 := by decide +kernel

theorem rad_to_deg_const :
    Binary32.ofBits 0x43340000 / Binary64.toBinary32 (Binary64.ofBits 0x400921fb54442d18) =
      Binary32.ofBits 0x42652ee0 := by decide +kernel

theorem cd_to_rad_const :
    Binary64.toBinary32 (Binary64.ofBits 0x400921fb54442d18) / Binary32.ofBits 0x468ca000 =
      Binary32.ofBits 0x393702d4 := by decide +kernel

theorem zero64_const : Binary64.toBinary32 (Binary64.ofBits 0x0000000000000000) = Binary32.ofBits 0x00000000 := by
  decide +kernel

theorem two64_const : Binary64.toBinary32 (Binary64.ofBits 0x4000000000000000) = Binary32.ofBits 0x40000000 := by
  decide +kernel

theorem one64_const : Binary64.toBinary32 (Binary64.ofBits 0x3ff0000000000000) = Binary32.ofBits 0x3f800000 := by
  decide +kernel

theorem neg_one64_const : -(Binary64.toBinary32 (Binary64.ofBits 0x3ff0000000000000)) = Binary32.ofBits 0xbf800000 := by
  decide +kernel

theorem expo_max_const : Binary64.toBinary32 (Binary64.ofBits 0x3fee666666666666) = Binary32.ofBits 0x3f733333 := by
  decide +kernel


theorem half_pi_const :
    Binary64.toBinary32 ((Binary64.ofBits 0x400921fb54442d18) / (Int32.toBinary64 ((2 : Int32)))) =
      Binary32.ofBits 0x3fc90fdb := by decide +kernel

theorem neg_half_pi_const :
    Binary64.toBinary32 (-((Binary64.ofBits 0x400921fb54442d18) / (Int32.toBinary64 ((2 : Int32))))) =
      Binary32.ofBits 0xbfc90fdb := by decide +kernel

theorem neg_one_const : -(Binary32.ofBits 0x3f800000) = Binary32.ofBits 0xbf800000 := by decide +kernel

end Corpus.F32

/-! ## Rounding with overflow, negation, signs

FloatLib describes a finite result as the rounding `roundAt` of the exact result, on a grid with no upper exponent
bound; it says nothing about a result that overflows. This section closes that gap for `Binary32`:

- `isFinite_roundDyadic_of_abs_roundAt_le`: the overflow threshold. A rounding whose unbounded value is at most the
  largest finite value in magnitude is finite. With FloatLib's `toReal_roundDyadic_eq_roundAt`, every rounded result
  denotes `rnd r` (`toEReal_roundDyadic`), where `rnd` sends `r` to `roundAt r` when that is in range and to `±∞` (the
  sign of `r`) otherwise. `rnd` is monotone (`rnd_mono`) and odd (`rnd_neg`).
- `ext_mul_of_isFinite`, `ext_add_of_isFinite`, `ext_sub_of_isFinite`: the three operations on finite operands, overflow
  included; `mul_of_isInf_of_pos`, `add_of_isInf_left/right`, `sub_of_isInf_left/right`: infinite operands.
- Sign under overflow: `mul_self_nonneg'`, `add_nonneg'`, `mul_nonneg_of_isFinite'`, `mul_nonpos_of_isFinite'`.
- Negation commutes: `neg_mul'` (as words, for a product that is a number); `sub_antisymm` (`x - y` denotes
  `-(y - x)`; as words it fails at `x = y`, where `x - y = +0 = y - x`).
- Monotone multiplication through overflow: `mul_le_mul_of_pos_right'`.
- Doubling is exact on the grid: `genericFormat_two_mul`; hence `midpoint_mem`.

All of it unfolds FloatLib's nearest-even dyadic rounder (`Model.Internal.ieeeRoundDyadic`) and the operations'
specifications (`Model.Spec.mul`, `Model.Spec.add`). -/

namespace Corpus.F32

open FloatLib.Floats.Formats.Flocq (bpow)

set_option linter.unusedSimpArgs false

theorem fmt_signedZero : (fmt : FloatFormat).supportsSignedZero = true := by decide
theorem fmt_isIEEE : (fmt : FloatFormat).isIEEE = true := by decide



theorem signBit_roundDyadic (d : FloatLib.Numerics.Dyadic) :
    Model.signBit (Model.roundDyadic fmt d) = d.negative := by
  rw [Model.roundDyadic_eq_internal]
  have hi : (fmt : FloatFormat).isIEEE = true := by decide
  simp only [Model.Internal.roundDyadic, hi, ite_true, Model.Internal.ieeeRoundDyadic]
  split_ifs <;> simp_all


theorem abs_roundAt_dyadic_of_normal (d : FloatLib.Numerics.Dyadic)
    (hk : FloatFormat.ieeeMinNormalExponent fmt ≤ (d.significand.log2 : Int) + d.exponent) :
    |Model.roundAt fmt d.toReal| =
      (Model.roundMantissaToLeadingBitEven d.significand fmt.fracWidth : ℝ) *
        bpow FloatLib.Numerics.binaryRadix ((d.significand.log2 : Int) + d.exponent - fmt.fracWidth) := by
  have e := Model.roundAt_dyadic_eq fmt d (by decide)
  dsimp only at e
  rw [e, Model.targetExponent_eq_normal fmt d.significand d.exponent hk,
    Model.roundMantissaAtExponentEven_eq_roundMantissaToLeadingBitEven]
  rw [abs_mul, FloatLib.Floats.Formats.Flocq.bpow_binaryRadix, abs_of_pos (by positivity : (0:ℝ) < (2:ℝ) ^ ((d.significand.log2 : Int) + d.exponent - fmt.fracWidth))]
  congr 1
  split <;> simp [Int.cast_natCast]


theorem fracWidth_eq : (fmt : FloatFormat).fracWidth = 23 := rfl
theorem maxNormal_eq : FloatFormat.ieeeMaxNormalExponent fmt = 127 := by decide
theorem minNormal_eq : FloatFormat.ieeeMinNormalExponent fmt = -126 := by decide
theorem maxNormal_eq' : (fmt : FloatFormat).maxNormalExponent = 127 := by decide

theorem posMax_lt : Model.toReal (Model.posMaxFinite fmt) < (2 : ℝ) ^ (128 : ℤ) := by
  have h := Model.toReal_posMaxFinite_lt_bpow fmt
  rw [maxNormal_eq'] at h
  simpa [Model.bpow, FloatLib.Floats.Formats.Flocq.bpow_binaryRadix] using h

theorem overflow_bound {r : Nat} {k : Int} (hr : 2 ^ 23 ≤ r) (hk : 128 ≤ k ∨ (r = 2 ^ 24 ∧ 127 ≤ k)) :
    (2 : ℝ) ^ (128 : ℤ) ≤ (r : ℝ) * (2 : ℝ) ^ (k - 23) := by
  rcases hk with hk | ⟨rfl, hk⟩
  · have h1 : (2 : ℝ) ^ (23 : ℕ) ≤ (r : ℝ) := by exact_mod_cast hr
    have h2 : (2 : ℝ) ^ (105 : ℤ) ≤ (2 : ℝ) ^ (k - 23) := zpow_le_zpow_right₀ (by norm_num) (by omega)
    calc (2 : ℝ) ^ (128 : ℤ) = (2 : ℝ) ^ (23 : ℕ) * (2 : ℝ) ^ (105 : ℤ) := by norm_num
      _ ≤ (r : ℝ) * (2 : ℝ) ^ (k - 23) := mul_le_mul h1 h2 (by positivity) (by positivity)
  · have h2 : (2 : ℝ) ^ (104 : ℤ) ≤ (2 : ℝ) ^ (k - 23) := zpow_le_zpow_right₀ (by norm_num) (by omega)
    have e : ((2 ^ 24 : ℕ) : ℝ) = 16777216 := by norm_num
    rw [e]
    calc (2 : ℝ) ^ (128 : ℤ) = 16777216 * (2 : ℝ) ^ (104 : ℤ) := by norm_num
      _ ≤ 16777216 * (2 : ℝ) ^ (k - 23) := mul_le_mul_of_nonneg_left h2 (by norm_num)

/-- The overflow threshold of nearest rounding: a dyadic whose rounding (with no upper exponent bound) is at most the
largest finite value in magnitude rounds to a finite value. -/
theorem isFinite_roundDyadic_of_abs_roundAt_le (d : FloatLib.Numerics.Dyadic)
    (h : |Model.roundAt fmt d.toReal| ≤ Model.toReal (Model.posMaxFinite fmt)) :
    Model.isFinite (Model.roundDyadic fmt d) = true := by
  by_contra hnf
  rw [Model.roundDyadic_eq_internal] at hnf
  have hi : (fmt : FloatFormat).isIEEE = true := by decide
  have fmt_signedZero : (fmt : FloatFormat).supportsSignedZero = true := by decide
  have hlt := posMax_lt
  simp only [Model.Internal.roundDyadic, hi, ite_true, Model.Internal.ieeeRoundDyadic] at hnf
  by_cases h0 : d.significand = 0
  · simp only [h0, beq_self_eq_true, ite_true] at hnf
    split_ifs at hnf <;> simp [fmt_signedZero] at hnf
  have hR : Model.roundMantissaToLeadingBitEven d.significand 23 =
      if 23 ≤ d.significand.log2 then FloatLib.Numerics.roundShiftRightEven d.significand (d.significand.log2 - 23)
      else d.significand <<< (23 - d.significand.log2) := rfl
  have hr23 : 2 ^ 23 ≤ Model.roundMantissaToLeadingBitEven d.significand 23 := by
    have := Model.pow2_le_roundMantissaToLeadingBitEven d.significand 23 h0
    rwa [Model.pow2_eq_two_pow] at this
  have hp24 : Model.pow2 (23 + 1) = 2 ^ 24 := by rw [Model.pow2_eq_two_pow]
  have hp23 : Model.pow2 23 = 2 ^ 23 := by rw [Model.pow2_eq_two_pow]
  simp only [beq_iff_eq, h0, ite_false, minNormal_eq, maxNormal_eq, hp24, hp23] at hnf
  by_cases hsub : (d.significand.log2 : Int) + d.exponent < -126
  · simp only [hsub, ite_true] at hnf
    split_ifs at hnf
    · simp [fmt_signedZero] at hnf
    · simp [fmt_signedZero] at hnf
    · rw [Model.isFinite_ofFields_ieee fmt hi] at hnf
      · exact absurd hnf (by decide)
      · decide
    · rw [Model.isFinite_ofFields_ieee fmt hi] at hnf
      · exact absurd hnf (by decide)
      · decide
  simp only [hsub, ite_false] at hnf
  have habs := abs_roundAt_dyadic_of_normal d (by rw [minNormal_eq]; omega)
  rw [fracWidth_eq] at habs
  generalize hk : (d.significand.log2 : Int) + d.exponent = k at hnf habs hsub
  rw [← hR] at hnf
  generalize Model.roundMantissaToLeadingBitEven d.significand 23 = r at hnf habs hr23
  have hbig : ¬ ((2 : ℝ) ^ (128 : ℤ) ≤ (r : ℝ) * (2 : ℝ) ^ (k - 23)) := by
    intro hb
    have : (r : ℝ) * FloatLib.Floats.Formats.Flocq.bpow FloatLib.Numerics.binaryRadix (k - (23 : ℕ)) ≤
        Model.toReal (Model.posMaxFinite fmt) := habs ▸ h
    rw [FloatLib.Floats.Formats.Flocq.bpow_binaryRadix] at this
    push_cast at this
    linarith
  have hb : (fmt : FloatFormat).bias = 127 := rfl
  have hall : (fmt : FloatFormat).expAllOnesNat = 255 := rfl
  split_ifs at hnf with hc hov hov
  all_goals simp only [Int.ofNat_eq_natCast, hb] at *
  all_goals first
    | exact hbig (overflow_bound hr23 (Or.inr ⟨hc, by omega⟩))
    | exact hbig (overflow_bound hr23 (Or.inl (by omega)))
    | (rw [Model.isFinite_ofFields_ieee fmt hi] at hnf
       · simp at hnf
       · rw [hall]; omega)



theorem neg_roundDyadic (d : FloatLib.Numerics.Dyadic) :
    Model.neg (Model.roundDyadic fmt d) = Model.roundDyadic fmt d.neg := by
  rw [Model.roundDyadic_eq_internal]
  obtain ⟨b, m, e⟩ := d
  simp only [Model.Internal.roundDyadic, fmt_isIEEE, ite_true, FloatLib.Numerics.Dyadic.neg]
  cases b <;>
  · simp only [Model.Internal.ieeeRoundDyadic, Bool.not_true, Bool.not_false, Bool.false_eq_true, ite_true, ite_false]
    split_ifs <;> simp [Model.neg_ofFields_of_supportsSignedZero _ fmt_signedZero, Model.neg_negZero_of_supportsSignedZero _ fmt_signedZero]

theorem model_neg_zero (s : Bool) : Model.neg (Model.zero fmt s) = Model.zero fmt (!s) := by
  cases s <;> simp [Model.zero, fmt_signedZero, Model.neg_negZero_of_supportsSignedZero _ fmt_signedZero]

theorem neg_nativeOverflow (s : Bool) : Model.neg (Model.nativeOverflow fmt s) = Model.nativeOverflow fmt (!s) := by
  cases s <;> simp [Model.nativeOverflow_eq_signedInf_of_isIEEE _ fmt_isIEEE]


theorem isNaN_canonicalNaN' : Model.isNaN (Model.canonicalNaN fmt) = true := Model.isNaN_canonicalNaN rfl

theorem toDyadic?_neg {x : Model fmt} {d : FloatLib.Numerics.Dyadic} (h : Model.toDyadic? x = some d) :
    Model.toDyadic? (Model.neg x) = some d.neg := by
  rw [Model.toDyadic?_neg_of_toDyadic?_some x h]
  simp [Model.negDyadic, fmt_signedZero]

theorem toDyadic?_neg_none {x : Model fmt} (h : Model.toDyadic? x = none) :
    Model.toDyadic? (Model.neg x) = none := by
  have hf : Model.isFinite x = false := by
    rw [← Model.toDyadic?_isSome_eq_isFinite, h]; rfl
  apply Model.toDyadic?_eq_none_of_isFinite_eq_false
  rw [Model.isFinite_neg, hf]

/-- Negating the left factor negates a product that is not a NaN (for non-NaN factors). -/
theorem model_neg_mul {x y : Model fmt} (hx : Model.isNaN x = false) (hy : Model.isNaN y = false)
    (h : Model.isNaN (Model.mul x y) = false) :
    Model.mul (Model.neg x) y = Model.neg (Model.mul x y) := by
  rw [Model.Proof.mul_eq_spec] at h ⊢
  rw [Model.Proof.mul_eq_spec]
  have hnx : Model.isNaN (Model.neg x) = false := by rw [Model.isNaN_neg]; exact hx
  have hc1 : Model.chooseNaN2 (Model.neg x) y = none := (Model.chooseNaN2_eq_none_iff _ _).2 ⟨hnx, hy⟩
  have hc2 : Model.chooseNaN2 x y = none := (Model.chooseNaN2_eq_none_iff _ _).2 ⟨hx, hy⟩
  rcases hdx : Model.toDyadic? x with _ | dx <;> rcases hdy : Model.toDyadic? y with _ | dy
  · have := toDyadic?_neg_none hdx
    simp only [Model.Spec.mul, hdx, hdy, this, hc1, hc2] at h ⊢
    split_ifs at h ⊢ <;> simp_all [neg_nativeOverflow, isNaN_canonicalNaN'] <;> split <;> simp
  · have := toDyadic?_neg_none hdx
    simp only [Model.Spec.mul, hdx, hdy, this, hc1, hc2] at h ⊢
    split_ifs at h ⊢ <;> simp_all [neg_nativeOverflow, isNaN_canonicalNaN'] <;> split <;> simp
  · have := toDyadic?_neg hdx
    simp only [Model.Spec.mul, hdx, hdy, this, hc1, hc2] at h ⊢
    split_ifs at h ⊢ <;> simp_all [neg_nativeOverflow, isNaN_canonicalNaN'] <;> split <;> simp
  · have := toDyadic?_neg hdx
    simp only [Model.Spec.mul, hdx, hdy, this, FloatLib.Numerics.Dyadic.neg]
    split_ifs
    · rw [model_neg_zero]; congr 1; cases dx.negative <;> cases dy.negative <;> rfl
    · rw [neg_roundDyadic]; congr 1; simp [FloatLib.Numerics.Dyadic.neg]


/-- The extended real that nearest rounding, with overflow to `±∞`, makes of an exact real `r`. -/
noncomputable def rnd (r : ℝ) : EReal :=
  if |Model.roundAt fmt r| ≤ Model.toReal (Model.posMaxFinite fmt) then ((Model.roundAt fmt r : ℝ) : EReal)
  else if 0 < r then ⊤ else ⊥

theorem toReal_dyadic_pos_iff {d : FloatLib.Numerics.Dyadic} (h : d.toReal ≠ 0) :
    0 < d.toReal ↔ d.negative = false := by
  have hs : d.significand ≠ 0 := by
    intro h0; apply h; simp [FloatLib.Numerics.Dyadic.toReal, FloatLib.Numerics.Dyadic.signedSignificand, h0]
  have hpos : (0 : ℝ) < (d.significand : ℝ) * (2 : ℝ) ^ d.exponent := by positivity
  cases hn : d.negative <;>
    simp [FloatLib.Numerics.Dyadic.toReal, FloatLib.Numerics.Dyadic.signedSignificand, hn] <;> linarith

/-- A rounded dyadic denotes `rnd` of the dyadic's value. -/
theorem toEReal_roundDyadic (d : FloatLib.Numerics.Dyadic) :
    Model.toEReal (Model.roundDyadic fmt d) = rnd d.toReal := by
  have hnan := Model.isNaN_roundDyadic_eq_false fmt d fmt_isIEEE
  unfold rnd
  by_cases hf : Model.isFinite (Model.roundDyadic fmt d) = true
  · have e := Model.toReal_roundDyadic_eq_roundAt fmt fmt_isIEEE d hf
    have hb := Model.abs_toReal_le_posMaxFinite_of_isFinite _ hf
    rw [e] at hb
    rw [Model.toEReal_eq_coe_toReal_of_isFinite _ hf, e, Corpus.ite_pos hb]
  · have hgt : ¬ |Model.roundAt fmt d.toReal| ≤ Model.toReal (Model.posMaxFinite fmt) :=
      fun hle => hf (isFinite_roundDyadic_of_abs_roundAt_le d hle)
    have hinf : Model.isInf (Model.roundDyadic fmt d) = true := by
      cases hi : Model.isInf (Model.roundDyadic fmt d)
      · exact absurd (Model.isFinite_eq_true_of_isNaN_eq_false_of_isInf_eq_false _ hnan hi) hf
      · rfl
    have hne : d.toReal ≠ 0 := by
      intro h0; apply hgt; rw [h0, Model.roundAt_zero, abs_zero]; exact Model.toReal_posMaxFinite_nonneg fmt
    rw [Model.toEReal_eq_ite, hnan, hinf, signBit_roundDyadic, Corpus.ite_neg hgt]
    simp only [Bool.false_eq_true, ite_false, ite_true]
    by_cases hp : 0 < d.toReal
    · rw [Corpus.ite_pos hp, (toReal_dyadic_pos_iff hne).1 hp]; rfl
    · rw [Corpus.ite_neg hp]
      have : d.negative = true := by
        cases hn : d.negative
        · exact absurd ((toReal_dyadic_pos_iff hne).2 hn) hp
        · rfl
      rw [this]; rfl

theorem rnd_zero : rnd 0 = 0 := by
  unfold rnd; rw [Model.roundAt_zero, abs_zero, Corpus.ite_pos (Model.toReal_posMaxFinite_nonneg fmt)]; rfl

theorem roundAt_nonneg {r : ℝ} (h : 0 ≤ r) : 0 ≤ Model.roundAt fmt r := by
  have := Model.roundAt_mono fmt h; rwa [Model.roundAt_zero] at this

theorem roundAt_nonpos {r : ℝ} (h : r ≤ 0) : Model.roundAt fmt r ≤ 0 := by
  have := Model.roundAt_mono fmt h; rwa [Model.roundAt_zero] at this

/-- `rnd` is monotone: nearest rounding with overflow keeps the order of the exact values. -/
theorem rnd_mono {r s : ℝ} (h : r ≤ s) : rnd r ≤ rnd s := by
  have hab := Model.roundAt_mono fmt h
  unfold rnd
  by_cases h1 : |Model.roundAt fmt r| ≤ Model.toReal (Model.posMaxFinite fmt)
  · by_cases h2 : |Model.roundAt fmt s| ≤ Model.toReal (Model.posMaxFinite fmt)
    · rw [Corpus.ite_pos h1, Corpus.ite_pos h2]; exact_mod_cast hab
    · rw [Corpus.ite_pos h1, Corpus.ite_neg h2]
      by_cases h3 : 0 < s
      · rw [Corpus.ite_pos h3]; exact le_top
      · exfalso
        have hb : Model.roundAt fmt s ≤ 0 := roundAt_nonpos (not_lt.1 h3)
        rw [abs_le] at h1; rw [abs_of_nonpos hb] at h2; linarith [h1.1]
  · rw [Corpus.ite_neg h1]
    by_cases h4 : 0 < r
    · have hs : 0 < s := h4.trans_le h
      have ha : 0 ≤ Model.roundAt fmt r := roundAt_nonneg h4.le
      rw [abs_of_nonneg ha] at h1
      have h2 : ¬ |Model.roundAt fmt s| ≤ Model.toReal (Model.posMaxFinite fmt) := by
        rw [abs_of_nonneg (ha.trans hab)]; intro h2; exact h1 (hab.trans h2)
      rw [Corpus.ite_pos h4, Corpus.ite_neg h2, Corpus.ite_pos hs]
    · rw [Corpus.ite_neg h4]; exact bot_le

theorem rnd_nonneg {r : ℝ} (h : 0 ≤ r) : 0 ≤ rnd r := rnd_zero ▸ rnd_mono h

theorem rnd_nonpos {r : ℝ} (h : r ≤ 0) : rnd r ≤ 0 := rnd_zero ▸ rnd_mono h

/-- `rnd` is odd: nearest rounding is symmetric, and so is overflow. -/
theorem rnd_neg (r : ℝ) : rnd (-r) = -rnd r := by
  have e : Model.roundAt fmt (-r) = -Model.roundAt fmt r := Model.roundAt_neg fmt r
  unfold rnd
  rw [e, abs_neg]
  by_cases h1 : |Model.roundAt fmt r| ≤ Model.toReal (Model.posMaxFinite fmt)
  · rw [Corpus.ite_pos h1, Corpus.ite_pos h1, EReal.coe_neg]
  · rw [Corpus.ite_neg h1, Corpus.ite_neg h1]
    rcases lt_trichotomy r 0 with hr | hr | hr
    · rw [Corpus.ite_pos (neg_pos.2 hr), Corpus.ite_neg (not_lt.2 hr.le)]; rfl
    · subst hr; rw [Model.roundAt_zero, abs_zero] at h1; exact absurd (Model.toReal_posMaxFinite_nonneg fmt) h1
    · rw [Corpus.ite_neg (not_lt.2 (neg_nonpos.2 hr.le)), Corpus.ite_pos hr]; rfl

/-- On finite operands, multiplication is a signed zero (exact product `0`) or one rounding of the exact product. -/
theorem model_mul_eq_of_isFinite {x y : Model fmt} (hx : Model.isFinite x = true) (hy : Model.isFinite y = true) :
    (∃ sign, Model.mul x y = Model.zero fmt sign ∧ Model.toReal x * Model.toReal y = 0) ∨
      ∃ exact : FloatLib.Numerics.Dyadic, Model.mul x y = Model.roundDyadic fmt exact ∧
        exact.toReal = Model.toReal x * Model.toReal y := by
  obtain ⟨dx, hdx⟩ := Model.exists_toDyadic?_of_isFinite hx
  obtain ⟨dy, hdy⟩ := Model.exists_toDyadic?_of_isFinite hy
  by_cases hxzero : dx.significand = 0
  · refine Or.inl ⟨Bool.xor dx.negative dy.negative,
      by simp [Model.Proof.mul_eq_spec, Model.Spec.mul, hdx, hdy, hxzero], ?_⟩
    simp [Model.toReal_eq, hdx, FloatLib.Numerics.Dyadic.toReal, hxzero]
  by_cases hyzero : dy.significand = 0
  · refine Or.inl ⟨Bool.xor dx.negative dy.negative,
      by simp [Model.Proof.mul_eq_spec, Model.Spec.mul, hdx, hdy, hyzero], ?_⟩
    simp [Model.toReal_eq, hdy, FloatLib.Numerics.Dyadic.toReal, hyzero]
  refine Or.inr ⟨{ negative := Bool.xor dx.negative dy.negative
                   significand := dx.significand * dy.significand
                   exponent := dx.exponent + dy.exponent },
    by simp [Model.Proof.mul_eq_spec, Model.Spec.mul, hdx, hdy, hxzero, hyzero], ?_⟩
  rw [Model.Dyadic.toReal_mul]
  simp [Model.toReal_eq, hdx, hdy]

theorem model_add_eq_of_isFinite {x y : Model fmt} (hx : Model.isFinite x = true) (hy : Model.isFinite y = true) :
    ∃ exact : FloatLib.Numerics.Dyadic, Model.add x y = Model.roundDyadic fmt exact ∧
      exact.toReal = Model.toReal x + Model.toReal y := by
  obtain ⟨dx, hdx⟩ := Model.exists_toDyadic?_of_isFinite hx
  obtain ⟨dy, hdy⟩ := Model.exists_toDyadic?_of_isFinite hy
  refine ⟨Model.addDyadic dx dy, by simp [Model.Proof.add_eq_spec, Model.Spec.add, hdx, hdy], ?_⟩
  rw [Model.Dyadic.toReal_addDyadic]
  simp [Model.toReal_eq, hdx, hdy]

theorem toEReal_zero' (sign : Bool) : Model.toEReal (Model.zero fmt sign) = 0 := by
  have hf : Model.isFinite (Model.zero fmt sign) = true := by cases sign <;> simp [Model.zero, fmt_signedZero]
  rw [Model.toEReal_eq_coe_toReal_of_isFinite _ hf, Model.toReal_zero]; rfl

/-- The product of two finite values denotes `rnd` of the exact product (overflow to `±∞` included). -/
theorem ext_mul_of_isFinite {x y : Binary32} (hx : Binary32.isFinite x = true) (hy : Binary32.isFinite y = true) :
    ext (x * y) = rnd (real x * real y) := by
  unfold ext model
  simp only [ExecFloat.Binary.toModel_hMul]
  rcases model_mul_eq_of_isFinite hx hy with ⟨s, e, h0⟩ | ⟨d, e, hd⟩
  · rw [e, toEReal_zero']
    have h0' : real x * real y = 0 := h0
    rw [h0', rnd_zero]
  · rw [e, toEReal_roundDyadic, hd]; rfl

/-- The sum of two finite values denotes `rnd` of the exact sum. -/
theorem ext_add_of_isFinite {x y : Binary32} (hx : Binary32.isFinite x = true) (hy : Binary32.isFinite y = true) :
    ext (x + y) = rnd (real x + real y) := by
  unfold ext model
  simp only [ExecFloat.Binary.toModel_hAdd]
  obtain ⟨d, e, hd⟩ := model_add_eq_of_isFinite hx hy
  rw [e, toEReal_roundDyadic, hd]; rfl

/-- Subtraction is addition of the negation (FloatLib's `Spec.sub`). -/
theorem model_sub (x y : Binary32) : model (x - y) = model (x + -y) := by
  unfold model
  simp only [ExecFloat.Binary.toModel_hSub, ExecFloat.Binary.toModel_hAdd, ExecFloat.Binary.toModel_neg,
    Model.Proof.sub_eq_spec, Model.Proof.add_eq_spec, Model.Spec.sub]

theorem ext_sub_of_isFinite {x y : Binary32} (hx : Binary32.isFinite x = true) (hy : Binary32.isFinite y = true) :
    ext (x - y) = rnd (real x - real y) := by
  have hny : Binary32.isFinite (-y) = true := by rw [isFinite_neg]; exact hy
  rw [show ext (x - y) = ext (x + -y) by unfold ext; rw [model_sub], ext_add_of_isFinite hx hny, real_neg hy,
    sub_eq_add_neg]

/-! ### Infinite operands -/

theorem toDyadic?_of_isInf {x : Model fmt} (h : Model.isInf x = true) : Model.toDyadic? x = none :=
  Model.toDyadic?_eq_none_of_isInf_eq_true h

theorem model_mul_of_isInf_left {x y : Model fmt} (hx : Model.isInf x = true) (hxn : Model.isNaN x = false)
    (hyn : Model.isNaN y = false) (hy0 : Model.isZero y = false) :
    Model.mul x y = Model.nativeOverflow fmt (Model.signBit x != Model.signBit y) := by
  rw [Model.Proof.mul_eq_spec]
  have hc : Model.chooseNaN2 x y = none := (Model.chooseNaN2_eq_none_iff _ _).2 ⟨hxn, hyn⟩
  simp only [Model.Spec.mul, toDyadic?_of_isInf hx, hc, hx, hy0, ite_true, Bool.false_eq_true, ite_false]

theorem model_mul_of_isInf_right {x y : Model fmt} (hy : Model.isInf y = true) (hyn : Model.isNaN y = false)
    (hxn : Model.isNaN x = false) (hx0 : Model.isZero x = false) :
    Model.mul x y = Model.nativeOverflow fmt (Model.signBit x != Model.signBit y) := by
  rw [Model.Proof.mul_eq_spec]
  have hc : Model.chooseNaN2 x y = none := (Model.chooseNaN2_eq_none_iff _ _).2 ⟨hxn, hyn⟩
  have hd : ∀ d, Model.toDyadic? y ≠ some d := by rw [toDyadic?_of_isInf hy]; simp
  have hy0 : Model.isZero y = false := by
    cases hz : Model.isZero y
    · rfl
    · have := Model.isInf_eq_false_of_isFinite_eq_true y (Model.isFinite_eq_true_of_isZero_eq_true y hz)
      rw [hy] at this; exact absurd this (by decide)
  unfold Model.Spec.mul
  split
  · next dx dy _ h2 => exact absurd h2 (hd dy)
  · simp only [hc, hy, hx0, ite_true, Bool.false_eq_true, ite_false]
    split_ifs with h1 <;> simp_all

theorem model_add_of_isInf_left {x y : Model fmt} (hx : Model.isInf x = true) (hxn : Model.isNaN x = false)
    (hy : Model.isFinite y = true) : Model.add x y = x := by
  rw [Model.Proof.add_eq_spec]
  have hyn := Model.isNaN_eq_false_of_isFinite_eq_true y hy
  have hc : Model.chooseNaN2 x y = none := (Model.chooseNaN2_eq_none_iff _ _).2 ⟨hxn, hyn⟩
  have hyi := Model.isInf_eq_false_of_isFinite_eq_true y hy
  simp only [Model.Spec.add, toDyadic?_of_isInf hx, hc, hx, hyi, ite_true, Bool.false_eq_true, ite_false]

theorem model_add_of_isInf_right {x y : Model fmt} (hy : Model.isInf y = true) (hyn : Model.isNaN y = false)
    (hx : Model.isFinite x = true) : Model.add x y = y := by
  rw [Model.Proof.add_eq_spec]
  have hxn := Model.isNaN_eq_false_of_isFinite_eq_true x hx
  have hc : Model.chooseNaN2 x y = none := (Model.chooseNaN2_eq_none_iff _ _).2 ⟨hxn, hyn⟩
  have hxi := Model.isInf_eq_false_of_isFinite_eq_true x hx
  have hd : ∀ d, Model.toDyadic? y ≠ some d := by rw [toDyadic?_of_isInf hy]; simp
  unfold Model.Spec.add
  split
  · next dx dy _ h2 => exact absurd h2 (hd dy)
  · simp only [hc, hy, hxi, ite_true, Bool.false_eq_true, ite_false]

/-! ### The lemmas the code proofs use -/

theorem model_inj {x y : Binary32} (h : model x = model y) : x = y := ExecFloat.Binary.toModel_inj.1 h

theorem isNaN_mul_of_isFinite {x y : Binary32} (hx : Binary32.isFinite x = true) (hy : Binary32.isFinite y = true) :
    Binary32.isNaN (x * y) = false := by
  show Model.isNaN (model (x * y)) = false
  simp only [model, ExecFloat.Binary.toModel_hMul]
  exact Model.isNaN_mul_eq_false_of_isFinite _ _ .nearest fmt_isIEEE hx hy

theorem isNaN_add_of_isFinite {x y : Binary32} (hx : Binary32.isFinite x = true) (hy : Binary32.isFinite y = true) :
    Binary32.isNaN (x + y) = false := by
  show Model.isNaN (model (x + y)) = false
  simp only [model, ExecFloat.Binary.toModel_hAdd]
  exact Model.isNaN_add_eq_false_of_isFinite _ _ .nearest fmt_isIEEE hx hy

theorem isNaN_sub_of_isFinite {x y : Binary32} (hx : Binary32.isFinite x = true) (hy : Binary32.isFinite y = true) :
    Binary32.isNaN (x - y) = false := by
  show Model.isNaN (model (x - y)) = false
  simp only [model, ExecFloat.Binary.toModel_hSub]
  exact Model.isNaN_sub_eq_false_of_isFinite _ _ .nearest fmt_isIEEE hx hy

/-- `0 ≤ x` for a number `x` is `0 ≤ ext x`. -/
theorem zero_le_iff {x : Binary32} (hx : Binary32.isNaN x = false) :
    Binary32.ofBits 0x00000000 ≤ x ↔ 0 ≤ ext x := by
  rw [le_iff_ext isNaN_zero hx, ext_zero]

theorem le_zero_iff {x : Binary32} (hx : Binary32.isNaN x = false) :
    x ≤ Binary32.ofBits 0x00000000 ↔ ext x ≤ 0 := by
  rw [le_iff_ext hx isNaN_zero, ext_zero]

/-- Sign under overflow: the square of a number is a number and is `≥ 0`, also when it overflows to `+∞`. -/
theorem mul_self_nonneg' {x : Binary32} (hx : Binary32.isNaN x = false) :
    Binary32.isNaN (x * x) = false ∧ Binary32.ofBits 0x00000000 ≤ x * x := by
  rcases finite_or_inf hx with hf | rfl | rfl
  · have hn := isNaN_mul_of_isFinite hf hf
    refine ⟨hn, (zero_le_iff hn).2 ?_⟩
    rw [ext_mul_of_isFinite hf hf]
    exact rnd_nonneg (mul_self_nonneg _)
  · exact ⟨by decide +kernel, by decide +kernel⟩
  · exact ⟨by decide +kernel, by decide +kernel⟩

theorem nonneg_cases {x : Binary32} (h : Binary32.ofBits 0x00000000 ≤ x) :
    Binary32.isFinite x = true ∨ x = Binary32.ofBits 0x7f800000 := by
  have hx := (isNaN_false_of_le h).2
  rcases finite_or_inf hx with hf | hp | hn
  · exact Or.inl hf
  · exact Or.inr hp
  · subst hn; rw [zero_le_iff (by decide +kernel), ext_negInf] at h; simp at h

theorem add_of_isInf_left {x y : Binary32} (hx : Model.isInf (model x) = true) (hxn : Binary32.isNaN x = false)
    (hy : Binary32.isFinite y = true) : x + y = x := by
  apply model_inj; simp only [model, ExecFloat.Binary.toModel_hAdd]; exact model_add_of_isInf_left hx hxn hy

theorem add_of_isInf_right {x y : Binary32} (hy : Model.isInf (model y) = true) (hyn : Binary32.isNaN y = false)
    (hx : Binary32.isFinite x = true) : x + y = y := by
  apply model_inj; simp only [model, ExecFloat.Binary.toModel_hAdd]; exact model_add_of_isInf_right hy hyn hx

theorem isInf_model_posInf : Model.isInf (model (Binary32.ofBits 0x7f800000)) = true := by decide +kernel
theorem isInf_model_negInf : Model.isInf (model (Binary32.ofBits 0xff800000)) = true := by decide +kernel

/-- Sign under overflow: a sum of two values `≥ 0` is a number and is `≥ 0`, also when it overflows to `+∞`. -/
theorem add_nonneg' {x y : Binary32} (hx : Binary32.ofBits 0x00000000 ≤ x) (hy : Binary32.ofBits 0x00000000 ≤ y) :
    Binary32.isNaN (x + y) = false ∧ Binary32.ofBits 0x00000000 ≤ x + y := by
  rcases nonneg_cases hx with hxf | rfl <;> rcases nonneg_cases hy with hyf | rfl
  · have hn := isNaN_add_of_isFinite hxf hyf
    refine ⟨hn, (zero_le_iff hn).2 ?_⟩
    rw [ext_add_of_isFinite hxf hyf]
    exact rnd_nonneg (add_nonneg (real_nonneg_of_le hxf hx) (real_nonneg_of_le hyf hy))
  · rw [add_of_isInf_right isInf_model_posInf (by decide +kernel) hxf]; exact ⟨by decide +kernel, hy⟩
  · rw [add_of_isInf_left isInf_model_posInf (by decide +kernel) hyf]; exact ⟨by decide +kernel, hx⟩
  · exact ⟨by decide +kernel, by decide +kernel⟩

/-- Sign under overflow: a product of two finite values is `≥ 0` or `≤ 0` as the exact product is (`±∞` included). -/
theorem mul_nonneg_of_isFinite' {x y : Binary32} (hx : Binary32.isFinite x = true) (hy : Binary32.isFinite y = true)
    (h : 0 ≤ real x * real y) : Binary32.ofBits 0x00000000 ≤ x * y := by
  rw [zero_le_iff (isNaN_mul_of_isFinite hx hy), ext_mul_of_isFinite hx hy]; exact rnd_nonneg h

theorem mul_nonpos_of_isFinite' {x y : Binary32} (hx : Binary32.isFinite x = true) (hy : Binary32.isFinite y = true)
    (h : real x * real y ≤ 0) : x * y ≤ Binary32.ofBits 0x00000000 := by
  rw [le_zero_iff (isNaN_mul_of_isFinite hx hy), ext_mul_of_isFinite hx hy]; exact rnd_nonpos h

/-- Negation commutes with multiplication, as words, whenever the product is a number. -/
theorem neg_mul' {x y : Binary32} (hx : Binary32.isNaN x = false) (hy : Binary32.isNaN y = false)
    (h : Binary32.isNaN (x * y) = false) : (-x) * y = -(x * y) := by
  apply model_inj
  simp only [model, ExecFloat.Binary.toModel_hMul, ExecFloat.Binary.toModel_neg]
  have h' : Model.isNaN (Model.mul (model x) (model y)) = false := by
    have := h; simp only [isNaN_def, ExecFloat.Binary.isNaN, ExecFloat.Binary.toModel_hMul] at this; exact this
  exact model_neg_mul hx hy h'

theorem isNaN_of_lt_left {x y : Binary32} (h : x < y) : Binary32.isNaN x = false := (isNaN_false_of_lt h).1

/-- A value `> 0` is not a zero and has its sign bit clear. -/
theorem pos_isZero_signBit {c : Binary32} (h : Binary32.ofBits 0x00000000 < c) :
    Model.isZero (model c) = false ∧ Model.signBit (model c) = false := by
  have hcn := (isNaN_false_of_lt h).2
  rw [lt_iff_ext isNaN_zero hcn, ext_zero] at h
  constructor
  · cases hz : Model.isZero (model c)
    · rfl
    · exfalso
      have hf := Model.isFinite_eq_true_of_isZero_eq_true _ hz
      have h0 := Model.toReal_eq_zero_of_isZero _ hz
      have : ext c = 0 := by unfold ext; rw [Model.toEReal_eq_coe_toReal_of_isFinite _ hf, h0]; rfl
      rw [this] at h; exact lt_irrefl _ h
  · cases hs : Model.signBit (model c)
    · rfl
    · exact absurd (toEReal_nonpos_of_signBit hcn hs) (not_le.2 h)

theorem model_posInf : model (Binary32.ofBits 0x7f800000) = Model.posInf fmt := by decide +kernel
theorem model_negInf : model (Binary32.ofBits 0xff800000) = Model.negInf fmt := by decide +kernel

/-- An infinity times a value `> 0` (not a NaN, not a zero) is that infinity. -/
theorem mul_of_isInf_of_pos {x c : Binary32} (hx : Model.isInf (model x) = true) (hxn : Binary32.isNaN x = false)
    (hc : Binary32.ofBits 0x00000000 < c) : x * c = x := by
  obtain ⟨hz, hs⟩ := pos_isZero_signBit hc
  have hcn := (isNaN_false_of_lt hc).2
  apply model_inj
  simp only [model, ExecFloat.Binary.toModel_hMul]
  rw [model_mul_of_isInf_left hx hxn hcn hz]
  simp only [model] at hs; rw [hs, Model.nativeOverflow_eq_signedInf_of_isIEEE _ fmt_isIEEE]
  cases hsx : Model.signBit (model x)
  · rw [eq_posInf hx hsx]; simp only [bne_self_eq_false, Bool.bne_false]; exact model_posInf.symm
  · rw [eq_negInf hx hsx]; simp only [bne_self_eq_false, Bool.bne_false]; exact model_negInf.symm

theorem le_posInf {z : Binary32} (hz : Binary32.isNaN z = false) : z ≤ Binary32.ofBits 0x7f800000 := by
  rw [le_iff_ext hz (by decide +kernel), ext_posInf]; exact le_top

theorem negInf_le {z : Binary32} (hz : Binary32.isNaN z = false) : Binary32.ofBits 0xff800000 ≤ z := by
  rw [le_iff_ext (by decide +kernel) hz, ext_negInf]; exact bot_le

/-- A number times a finite value `> 0` is a number. -/
theorem isNaN_mul_of_pos {x c : Binary32} (hx : Binary32.isNaN x = false) (hcf : Binary32.isFinite c = true)
    (hc : Binary32.ofBits 0x00000000 < c) : Binary32.isNaN (x * c) = false := by
  rcases finite_or_inf hx with hf | rfl | rfl
  · exact isNaN_mul_of_isFinite hf hcf
  · rw [mul_of_isInf_of_pos isInf_model_posInf (by decide +kernel) hc]; decide +kernel
  · rw [mul_of_isInf_of_pos isInf_model_negInf (by decide +kernel) hc]; decide +kernel

/-- Monotone multiplication through overflow: `x ≤ y → x * c ≤ y * c` for a finite `c > 0`, for every `x` and `y`
(`±∞` included; the products may overflow). -/
theorem mul_le_mul_of_pos_right' {x y c : Binary32} (hxy : x ≤ y) (hcf : Binary32.isFinite c = true)
    (hc : Binary32.ofBits 0x00000000 < c) : x * c ≤ y * c := by
  obtain ⟨hxn, hyn⟩ := isNaN_false_of_le hxy
  have hxc := isNaN_mul_of_pos hxn hcf hc
  have hyc := isNaN_mul_of_pos hyn hcf hc
  have hrc : 0 ≤ real c := real_nonneg_of_le hcf (le_of_lt hc)
  rcases finite_or_inf hxn with hxf | rfl | rfl <;> rcases finite_or_inf hyn with hyf | rfl | rfl
  · rw [le_iff_ext hxc hyc, ext_mul_of_isFinite hxf hcf, ext_mul_of_isFinite hyf hcf]
    exact rnd_mono (mul_le_mul_of_nonneg_right (real_le_of_le hxf hyf hxy) hrc)
  · rw [mul_of_isInf_of_pos isInf_model_posInf (by decide +kernel) hc]; exact le_posInf hxc
  · exfalso; rw [le_iff_ext hxn (by decide +kernel), ext_negInf, ext_of_isFinite hxf] at hxy; simp at hxy
  · exfalso; rw [le_iff_ext (by decide +kernel) hyn, ext_posInf, ext_of_isFinite hyf] at hxy; simp at hxy
  · exact le_refl_of_not_isNaN hxc
  · exfalso; exact absurd hxy (by decide +kernel)
  · rw [mul_of_isInf_of_pos isInf_model_negInf (by decide +kernel) hc]; exact negInf_le hyc
  · rw [mul_of_isInf_of_pos isInf_model_negInf (by decide +kernel) hc]; exact negInf_le hyc
  · exact le_refl_of_not_isNaN hxc

theorem ext_of_isNaN {x : Binary32} (h : Binary32.isNaN x = true) : ext x = 0 := by
  have h' : Model.isNaN (model x) = true := h
  unfold ext; rw [Model.toEReal_eq_ite, h']; rfl

theorem ext_sub_eq_ext_add (x y : Binary32) : ext (x - y) = ext (x + -y) := by unfold ext; rw [model_sub]

theorem isNaN_sub_eq_isNaN_add (x y : Binary32) : Binary32.isNaN (x - y) = Binary32.isNaN (x + -y) := by
  show Model.isNaN (model (x - y)) = Model.isNaN (model (x + -y)); rw [model_sub]

theorem isInf_neg' (x : Binary32) : Model.isInf (model (-x)) = Model.isInf (model x) := by
  simp only [model, ExecFloat.Binary.toModel_neg, Model.isInf_neg]

theorem sub_of_isInf_left {x y : Binary32} (hx : Model.isInf (model x) = true) (hxn : Binary32.isNaN x = false)
    (hy : Binary32.isFinite y = true) : x - y = x := by
  apply model_inj; rw [model_sub, add_of_isInf_left hx hxn (by rw [isFinite_neg]; exact hy)]

theorem sub_of_isInf_right {x y : Binary32} (hx : Binary32.isFinite x = true) (hy : Model.isInf (model y) = true)
    (hyn : Binary32.isNaN y = false) : x - y = -y := by
  apply model_inj
  rw [model_sub, add_of_isInf_right (by rw [isInf_neg']; exact hy) (by rw [isNaN_neg]; exact hyn) hx]

private theorem nan_case {z : Binary32} (h : Binary32.isNaN z = true) :
    Binary32.isNaN z = Binary32.isNaN z ∧ ext z = -ext z := ⟨rfl, by rw [ext_of_isNaN h, _root_.neg_zero]⟩

private theorem inf_sub_inf1 : Binary32.ofBits 0x7f800000 - Binary32.ofBits 0xff800000 = Binary32.ofBits 0x7f800000 := by
  decide +kernel
private theorem inf_sub_inf2 : Binary32.ofBits 0xff800000 - Binary32.ofBits 0x7f800000 = Binary32.ofBits 0xff800000 := by
  decide +kernel
private theorem inf_sub_inf3 : Binary32.isNaN (Binary32.ofBits 0x7f800000 - Binary32.ofBits 0x7f800000) = true := by
  decide +kernel
private theorem inf_sub_inf4 : Binary32.isNaN (Binary32.ofBits 0xff800000 - Binary32.ofBits 0xff800000) = true := by
  decide +kernel
private theorem isNaN_posInf' : Binary32.isNaN (Binary32.ofBits 0x7f800000) = false := by decide +kernel
private theorem isNaN_negInf' : Binary32.isNaN (Binary32.ofBits 0xff800000) = false := by decide +kernel
private theorem neg_posInf' : -(Binary32.ofBits 0x7f800000) = Binary32.ofBits 0xff800000 := by decide +kernel
private theorem neg_negInf' : -(Binary32.ofBits 0xff800000) = Binary32.ofBits 0x7f800000 := by decide +kernel

private theorem fin_sub_inf {x t : Binary32} (hxf : Binary32.isFinite x = true) (ht : Model.isInf (model t) = true)
    (htn : Binary32.isNaN t = false) :
    Binary32.isNaN (x - t) = Binary32.isNaN (t - x) ∧ ext (x - t) = -ext (t - x) := by
  rw [sub_of_isInf_right hxf ht htn, sub_of_isInf_left ht htn hxf, isNaN_neg, ext_neg htn]
  exact ⟨rfl, rfl⟩

private theorem inf_sub_fin {x t : Binary32} (hxf : Binary32.isFinite x = true) (ht : Model.isInf (model t) = true)
    (htn : Binary32.isNaN t = false) :
    Binary32.isNaN (t - x) = Binary32.isNaN (x - t) ∧ ext (t - x) = -ext (x - t) := by
  rw [sub_of_isInf_right hxf ht htn, sub_of_isInf_left ht htn hxf, isNaN_neg, ext_neg htn, neg_neg]
  exact ⟨rfl, rfl⟩

/-- Subtraction is antisymmetric in value: for numbers `x`, `y`, `x - y` and `y - x` are both NaN or both numbers,
and `x - y` denotes the negation of `y - x`. (As words `x - y = -(y - x)` fails at `x = y`: `+0` against `-0`.) -/
theorem sub_antisymm {x y : Binary32} (hx : Binary32.isNaN x = false) (hy : Binary32.isNaN y = false) :
    Binary32.isNaN (x - y) = Binary32.isNaN (y - x) ∧ ext (x - y) = -ext (y - x) := by
  rcases finite_or_inf hx with hxf | rfl | rfl <;> rcases finite_or_inf hy with hyf | rfl | rfl
  · refine ⟨by rw [isNaN_sub_of_isFinite hxf hyf, isNaN_sub_of_isFinite hyf hxf], ?_⟩
    rw [ext_sub_of_isFinite hxf hyf, ext_sub_of_isFinite hyf hxf, ← rnd_neg, neg_sub]
  · exact fin_sub_inf hxf isInf_model_posInf isNaN_posInf'
  · exact fin_sub_inf hxf isInf_model_negInf isNaN_negInf'
  · exact inf_sub_fin hyf isInf_model_posInf isNaN_posInf'
  · exact nan_case inf_sub_inf3
  · rw [inf_sub_inf1, inf_sub_inf2, ext_posInf, ext_negInf]; exact ⟨rfl, rfl⟩
  · exact inf_sub_fin hyf isInf_model_negInf isNaN_negInf'
  · rw [inf_sub_inf1, inf_sub_inf2, ext_posInf, ext_negInf]; exact ⟨rfl, by rw [EReal.neg_top]⟩
  · exact nan_case inf_sub_inf4



theorem genericFormat_two_mul {r : ℝ}
    (h : FloatLib.Floats.Formats.Flocq.genericFormat FloatLib.Numerics.binaryRadix (Model.fexpOf fmt) r) :
    FloatLib.Floats.Formats.Flocq.genericFormat FloatLib.Numerics.binaryRadix (Model.fexpOf fmt) (2 * r) := by
  have hprec : (0 : ℤ) < fmt.fracWidth + 1 := by positivity
  have h' := (FloatLib.Floats.Formats.Flocq.generic_format_FLT_iff fmt.minSubnormalExponent (fmt.fracWidth + 1) hprec r).1 h
  apply (FloatLib.Floats.Formats.Flocq.generic_format_FLT_iff fmt.minSubnormalExponent (fmt.fracWidth + 1) hprec _).2
  obtain ⟨hp, f, hf, hm, he⟩ := h'
  refine ⟨hp, ⟨f.mantissa, f.exponent + 1⟩, ?_, hm, show fmt.minSubnormalExponent ≤ f.exponent + 1 by omega⟩
  rw [hf]
  simp only [FloatLib.Floats.Formats.Flocq.toReal, FloatLib.Floats.Formats.Flocq.bpow_binaryRadix]
  rw [zpow_add₀ (by norm_num)]
  ring


theorem roundAt_two_mul {x : Binary32} (hx : Binary32.isFinite x = true) :
    Model.roundAt fmt (2 * real x) = 2 * real x :=
  Model.roundAt_of_genericFormat fmt (genericFormat_two_mul (Model.toReal_genericFormat_of_isFinite (model x) hx))

/-- The midpoint `(low + high) / 2` of `low ≤ high` lies in `[low, high]` when `low + high` is finite. -/
theorem midpoint_mem {l h : Binary32} (hlh : l ≤ h) (hs : Binary32.isFinite (l + h) = true) :
    Binary32.isFinite ((l + h) / Binary32.ofBits 0x40000000) = true ∧
      l ≤ (l + h) / Binary32.ofBits 0x40000000 ∧ (l + h) / Binary32.ofBits 0x40000000 ≤ h := by
  have hxy : Model.isFinite (Model.add (model l) (model h)) = true := by
    have := hs
    simp only [Binary32.isFinite, ExecFloat.Binary.isFinite, ExecFloat.Binary.toModel_hAdd] at this
    exact this
  obtain ⟨hl, hh⟩ := Model.isFinite_of_isFinite_add (by decide) hxy
  have hle := real_le_of_le hl hh hlh
  have e := real_add hs
  have m1 : 2 * real l ≤ real (l + h) := by
    rw [e, ← roundAt_two_mul hl]; exact Model.roundAt_mono fmt (by linarith)
  have m2 : real (l + h) ≤ 2 * real h := by
    rw [e, ← roundAt_two_mul hh]; exact Model.roundAt_mono fmt (by linarith)
  have h2f : Binary32.isFinite (Binary32.ofBits 0x40000000) = true := by decide +kernel
  have e2 : real (Binary32.ofBits 0x40000000) = 2 := by
    rw [real_eq_of_toRat? (q := 2) (by decide +kernel)]; norm_num
  exact div_mem hs h2f (by decide +kernel) hl hh (by rw [e2]; linarith) (by rw [e2]; linarith)


end Corpus.F32

/-! ### NaN in, NaN out -/

namespace Corpus.F32

private theorem chooseNaN2_ne_none {x y : Model fmt} (h : Model.isNaN x = true ∨ Model.isNaN y = true) :
    Model.chooseNaN2 x y ≠ none := by
  intro hc
  have := (Model.chooseNaN2_eq_none_iff _ _).1 hc
  rcases h with h | h <;> simp_all

private theorem model_isNaN_mul {x y : Model fmt} (h : Model.isNaN x = true ∨ Model.isNaN y = true) :
    Model.isNaN (Model.mul x y) = true := by
  rw [Model.Proof.mul_eq_spec]; unfold Model.Spec.mul
  rcases hc : Model.chooseNaN2 x y with _ | n
  · exact absurd hc (chooseNaN2_ne_none h)
  · split
    · next dx dy h1 h2 =>
      rcases h with h | h
      · rw [Model.toDyadic?_eq_none_of_isNaN h] at h1; cases h1
      · rw [Model.toDyadic?_eq_none_of_isNaN h] at h2; cases h2
    · simp only [hc]; exact Model.isNaN_of_chooseNaN2_eq_some hc

private theorem model_isNaN_add {x y : Model fmt} (h : Model.isNaN x = true ∨ Model.isNaN y = true) :
    Model.isNaN (Model.add x y) = true := by
  rw [Model.Proof.add_eq_spec]; unfold Model.Spec.add
  rcases hc : Model.chooseNaN2 x y with _ | n
  · exact absurd hc (chooseNaN2_ne_none h)
  · split
    · next dx dy h1 h2 =>
      rcases h with h | h
      · rw [Model.toDyadic?_eq_none_of_isNaN h] at h1; cases h1
      · rw [Model.toDyadic?_eq_none_of_isNaN h] at h2; cases h2
    · simp only [hc]; exact Model.isNaN_of_chooseNaN2_eq_some hc

/-- A NaN operand gives a NaN product. -/
theorem isNaN_mul_of_isNaN {x y : Binary32} (h : Binary32.isNaN x = true ∨ Binary32.isNaN y = true) :
    Binary32.isNaN (x * y) = true := by
  show Model.isNaN (model (x * y)) = true
  simp only [model, ExecFloat.Binary.toModel_hMul]; exact model_isNaN_mul h

/-- A NaN operand gives a NaN sum. -/
theorem isNaN_add_of_isNaN {x y : Binary32} (h : Binary32.isNaN x = true ∨ Binary32.isNaN y = true) :
    Binary32.isNaN (x + y) = true := by
  show Model.isNaN (model (x + y)) = true
  simp only [model, ExecFloat.Binary.toModel_hAdd]; exact model_isNaN_add h

/-- A NaN operand gives a NaN difference. -/
theorem isNaN_sub_of_isNaN {x y : Binary32} (h : Binary32.isNaN x = true ∨ Binary32.isNaN y = true) :
    Binary32.isNaN (x - y) = true := by
  rw [isNaN_sub_eq_isNaN_add]; apply isNaN_add_of_isNaN
  rcases h with h | h
  · exact Or.inl h
  · exact Or.inr (by rw [isNaN_neg]; exact h)

/-- `x - x` is a zero for a finite `x` and a NaN otherwise. -/
theorem sub_self_isNaN (x : Binary32) : Binary32.isNaN (x - x) = !Binary32.isFinite x := by
  cases hn : Binary32.isNaN x
  · rcases finite_or_inf hn with hf | rfl | rfl
    · rw [isNaN_sub_of_isFinite hf hf, hf]; rfl
    · decide +kernel
    · decide +kernel
  · rw [isNaN_sub_of_isNaN (Or.inl hn)]
    have : Binary32.isFinite x = false := by
      cases hf : Binary32.isFinite x
      · rfl
      · have : Binary32.isNaN x = false := Model.isNaN_eq_false_of_isFinite_eq_true (model x) hf
        rw [this] at hn; cases hn
    rw [this]; rfl

theorem ext_sub_self {x : Binary32} (hf : Binary32.isFinite x = true) : ext (x - x) = 0 := by
  rw [ext_sub_of_isFinite hf hf, sub_self, rnd_zero]

end Corpus.F32

/-! ### Commutativity, negation on the right, negation and division -/

namespace Corpus.F32

theorem model_isZero_of_isInf {x : Model fmt} (h : Model.isInf x = true) : Model.isZero x = false := by
  cases hz : Model.isZero x
  · rfl
  · have := Model.isInf_eq_false_of_isFinite_eq_true x (Model.isFinite_eq_true_of_isZero_eq_true x hz)
    rw [h] at this; exact absurd this (by decide)

theorem model_mul_comm {x y : Model fmt} (hx : Model.isNaN x = false) (hy : Model.isNaN y = false) :
    Model.mul x y = Model.mul y x := by
  rw [Model.Proof.mul_eq_spec, Model.Proof.mul_eq_spec]
  have hc1 : Model.chooseNaN2 x y = none := (Model.chooseNaN2_eq_none_iff _ _).2 ⟨hx, hy⟩
  have hc2 : Model.chooseNaN2 y x = none := (Model.chooseNaN2_eq_none_iff _ _).2 ⟨hy, hx⟩
  rcases hdx : Model.toDyadic? x with _ | dx <;> rcases hdy : Model.toDyadic? y with _ | dy <;>
    simp only [Model.Spec.mul, hdx, hdy, hc1, hc2]
  rotate_left 3
  · rw [Bool.xor_comm, Nat.mul_comm, Int.add_comm, Bool.or_comm]
  all_goals (split_ifs <;> cases hsx : Model.signBit x <;> cases hsy : Model.signBit y <;>
    simp_all [model_isZero_of_isInf])

theorem neg_neg' (x : Binary32) : -(-x) = x := by
  apply model_inj; simp only [model, ExecFloat.Binary.toModel_neg, Model.neg_neg]

/-- Multiplication of numbers commutes (as words). -/
theorem mul_comm' {x y : Binary32} (hx : Binary32.isNaN x = false) (hy : Binary32.isNaN y = false) :
    x * y = y * x := by
  apply model_inj; simp only [model, ExecFloat.Binary.toModel_hMul]; exact model_mul_comm hx hy

/-- Negating the right factor negates a product that is a number. -/
theorem mul_neg' {x y : Binary32} (hx : Binary32.isNaN x = false) (hy : Binary32.isNaN y = false)
    (h : Binary32.isNaN (x * y) = false) : x * (-y) = -(x * y) := by
  have hny : Binary32.isNaN (-y) = false := by rw [isNaN_neg]; exact hy
  rw [mul_comm' hx hny, mul_comm' hx hy]
  exact neg_mul' hy hx (by rw [mul_comm' hy hx]; exact h)

/-- Negating a factor keeps the product's NaN-ness. -/
theorem isNaN_neg_mul (x y : Binary32) : Binary32.isNaN ((-x) * y) = Binary32.isNaN (x * y) := by
  cases hx : Binary32.isNaN x
  · cases hy : Binary32.isNaN y
    · have hnx : Binary32.isNaN (-x) = false := by rw [isNaN_neg]; exact hx
      cases h : Binary32.isNaN (x * y)
      · rw [neg_mul' hx hy h, isNaN_neg, h]
      · cases h' : Binary32.isNaN ((-x) * y)
        · have := neg_mul' hnx hy h'
          rw [neg_neg'] at this
          rw [this, isNaN_neg, h'] at h; exact absurd h (by decide)
        · rfl
    · rw [isNaN_mul_of_isNaN (Or.inr hy), isNaN_mul_of_isNaN (Or.inr hy)]
  · rw [isNaN_mul_of_isNaN (Or.inl (by rw [isNaN_neg]; exact hx)), isNaN_mul_of_isNaN (Or.inl hx)]

theorem isNaN_mul_neg (x y : Binary32) : Binary32.isNaN (x * (-y)) = Binary32.isNaN (x * y) := by
  cases hx : Binary32.isNaN x
  · cases hy : Binary32.isNaN y
    · have hny : Binary32.isNaN (-y) = false := by rw [isNaN_neg]; exact hy
      rw [mul_comm' hx hny, mul_comm' hx hy, isNaN_neg_mul]
    · rw [isNaN_mul_of_isNaN (Or.inr (by rw [isNaN_neg]; exact hy)), isNaN_mul_of_isNaN (Or.inr hy)]
  · rw [isNaN_mul_of_isNaN (Or.inl hx), isNaN_mul_of_isNaN (Or.inl hx)]

theorem model_neg_div {x y : Model fmt} (hx : Model.isNaN x = false) (hy : Model.isNaN y = false)
    (h : Model.isNaN (Model.div x y) = false) :
    Model.div (Model.neg x) y = Model.neg (Model.div x y) := by
  rw [Model.Proof.div_eq_spec] at h ⊢
  rw [Model.Proof.div_eq_spec]
  have hnx : Model.isNaN (Model.neg x) = false := by rw [Model.isNaN_neg]; exact hx
  have hc1 : Model.chooseNaN2 (Model.neg x) y = none := (Model.chooseNaN2_eq_none_iff _ _).2 ⟨hnx, hy⟩
  have hc2 : Model.chooseNaN2 x y = none := (Model.chooseNaN2_eq_none_iff _ _).2 ⟨hx, hy⟩
  rcases hdx : Model.toDyadic? x with _ | dx <;> rcases hdy : Model.toDyadic? y with _ | dy
  · have := toDyadic?_neg_none hdx
    simp only [Model.Spec.div, Model.Spec.divSpecial, hdx, hdy, this, hc1, hc2] at h ⊢
    split_ifs at h ⊢ <;> simp_all [neg_nativeOverflow, isNaN_canonicalNaN', model_neg_zero]
    all_goals (split <;> first
      | exact (Model.neg_posInf _).symm
      | exact (Model.neg_negInf _).symm
      | (rw [Model.neg_posZero]; simp [Model.zero, fmt_signedZero])
      | exact (Model.neg_negZero_of_supportsSignedZero _ fmt_signedZero).symm)
  · have := toDyadic?_neg_none hdx
    simp only [Model.Spec.div, Model.Spec.divSpecial, hdx, hdy, this, hc1, hc2] at h ⊢
    split_ifs at h ⊢ <;> simp_all [neg_nativeOverflow, isNaN_canonicalNaN', model_neg_zero]
    all_goals (split <;> first
      | exact (Model.neg_posInf _).symm
      | exact (Model.neg_negInf _).symm
      | (rw [Model.neg_posZero]; simp [Model.zero, fmt_signedZero])
      | exact (Model.neg_negZero_of_supportsSignedZero _ fmt_signedZero).symm)
  · have := toDyadic?_neg hdx
    simp only [Model.Spec.div, Model.Spec.divSpecial, hdx, hdy, this, hc1, hc2] at h ⊢
    split_ifs at h ⊢ <;> simp_all [neg_nativeOverflow, isNaN_canonicalNaN', model_neg_zero]
    all_goals (split <;> first
      | exact (Model.neg_posInf _).symm
      | exact (Model.neg_negInf _).symm
      | (rw [Model.neg_posZero]; simp [Model.zero, fmt_signedZero])
      | exact (Model.neg_negZero_of_supportsSignedZero _ fmt_signedZero).symm)
  · have := toDyadic?_neg hdx
    simp only [Model.Spec.div, hdx, hdy, this, FloatLib.Numerics.Dyadic.neg] at h ⊢
    split_ifs at h ⊢ with h1 h2
    · simp_all [isNaN_canonicalNaN']
    · rw [neg_nativeOverflow]; congr 1; cases dx.negative <;> cases dy.negative <;> rfl
    · rw [model_neg_zero]; congr 1; cases dx.negative <;> cases dy.negative <;> rfl
    · have hd : dy.significand ≠ 0 := by simpa using h1
      cases hxn : dx.negative <;> cases hyn : dy.negative <;>
        simp only [Bool.not_true, Bool.not_false, Bool.xor_true, Bool.xor_false, Bool.true_xor, Bool.false_xor] <;>
        first
          | exact Model.roundRatScaled_true_eq_neg_false fmt _ _ _ fmt_isIEEE hd
          | (rw [Model.roundRatScaled_true_eq_neg_false fmt _ _ _ fmt_isIEEE hd, Model.neg_neg])

/-- Negating the dividend negates a quotient that is a number. -/
theorem neg_div' {x y : Binary32} (hx : Binary32.isNaN x = false) (hy : Binary32.isNaN y = false)
    (h : Binary32.isNaN (x / y) = false) : (-x) / y = -(x / y) := by
  apply model_inj
  simp only [model, ExecFloat.Binary.toModel_hDiv, ExecFloat.Binary.toModel_neg]
  have h' : Model.isNaN (Model.div (model x) (model y)) = false := by
    have := h; simp only [isNaN_def, ExecFloat.Binary.isNaN, ExecFloat.Binary.toModel_hDiv] at this; exact this
  exact model_neg_div hx hy h'

private theorem model_isNaN_div {x y : Model fmt} (h : Model.isNaN x = true ∨ Model.isNaN y = true) :
    Model.isNaN (Model.div x y) = true := by
  rw [Model.Proof.div_eq_spec]; unfold Model.Spec.div
  rcases hc : Model.chooseNaN2 x y with _ | n
  · exact absurd hc (chooseNaN2_ne_none h)
  · split
    · next dx dy h1 h2 =>
      rcases h with h | h
      · rw [Model.toDyadic?_eq_none_of_isNaN h] at h1; cases h1
      · rw [Model.toDyadic?_eq_none_of_isNaN h] at h2; cases h2
    · simp only [Model.Spec.divSpecial, hc]; exact Model.isNaN_of_chooseNaN2_eq_some hc

/-- A NaN operand gives a NaN quotient. -/
theorem isNaN_div_of_isNaN {x y : Binary32} (h : Binary32.isNaN x = true ∨ Binary32.isNaN y = true) :
    Binary32.isNaN (x / y) = true := by
  show Model.isNaN (model (x / y)) = true
  simp only [model, ExecFloat.Binary.toModel_hDiv]; exact model_isNaN_div h

theorem isNaN_neg_div (x y : Binary32) : Binary32.isNaN ((-x) / y) = Binary32.isNaN (x / y) := by
  cases hx : Binary32.isNaN x
  · cases hy : Binary32.isNaN y
    · have hnx : Binary32.isNaN (-x) = false := by rw [isNaN_neg]; exact hx
      cases h : Binary32.isNaN (x / y)
      · rw [neg_div' hx hy h, isNaN_neg, h]
      · cases h' : Binary32.isNaN ((-x) / y)
        · have := neg_div' hnx hy h'
          rw [neg_neg'] at this
          rw [this, isNaN_neg, h'] at h; exact absurd h (by decide)
        · rfl
    · rw [isNaN_div_of_isNaN (Or.inr hy), isNaN_div_of_isNaN (Or.inr hy)]
  · rw [isNaN_div_of_isNaN (Or.inl (by rw [isNaN_neg]; exact hx)), isNaN_div_of_isNaN (Or.inl hx)]

end Corpus.F32

/-! ### Signs of quotients and of products with an infinity -/

namespace Corpus.F32

theorem signBit_roundRatScaled (sign : Bool) (n d : Nat) (e : Int) :
    Model.signBit (Model.roundRatScaled fmt sign n d e) = sign ∨ d = 0 := by
  by_cases hd : d = 0
  · exact Or.inr hd
  left
  rw [Model.roundRatScaled, dite_eq_left_of_eq_true (eq_true fmt_isIEEE)]
  unfold Model.ieeeRoundRatScaled
  dsimp only
  simp only [beq_iff_eq, hd, ite_false]
  split_ifs <;> (try split) <;> cases sign <;> simp_all [Model.signBit_negZero]

/-- The quotient of two finite values `> 0` is a number `≥ 0` (`+∞` when it overflows). -/
theorem div_nonneg_of_pos {x y : Binary32} (hxf : Binary32.isFinite x = true) (hx : Binary32.ofBits 0x00000000 < x)
    (hyf : Binary32.isFinite y = true) (hy : Binary32.ofBits 0x00000000 < y) :
    Binary32.isNaN (x / y) = false ∧ Binary32.ofBits 0x00000000 ≤ x / y := by
  obtain ⟨hx0, hxs⟩ := pos_isZero_signBit hx
  obtain ⟨hy0, hys⟩ := pos_isZero_signBit hy
  obtain ⟨dx, hdx⟩ := Model.exists_toDyadic?_of_isFinite (x := model x) hxf
  obtain ⟨dy, hdy⟩ := Model.exists_toDyadic?_of_isFinite (x := model y) hyf
  have hmx := Model.significand_ne_zero_of_toDyadic?_some_of_isZero_eq_false hdx hx0
  have hmy := Model.significand_ne_zero_of_toDyadic?_some_of_isZero_eq_false hdy hy0
  have hnx : dx.negative = false := by rw [Model.sign_eq_signBit_of_toDyadic?_some hdx]; exact hxs
  have hny : dy.negative = false := by rw [Model.sign_eq_signBit_of_toDyadic?_some hdy]; exact hys
  have e : model (x / y) = Model.roundRatScaled fmt false dx.significand dy.significand (dx.exponent - dy.exponent) := by
    simp only [model, ExecFloat.Binary.toModel_hDiv, Model.Proof.div_eq_spec, Model.Spec.div]
    simp only [model] at hdx hdy
    simp [hdx, hdy, hmx, hmy, hnx, hny]
  have hn : Binary32.isNaN (x / y) = false := by
    show Model.isNaN (model (x / y)) = false
    rw [e]; exact Model.isNaN_roundRatScaled_eq_false fmt _ _ _ _ fmt_isIEEE hmy
  refine ⟨hn, (zero_le_iff hn).2 ?_⟩
  unfold ext; rw [e]
  rcases signBit_roundRatScaled false dx.significand dy.significand (dx.exponent - dy.exponent) with hs | hs
  · exact toEReal_nonneg_of_signBit (by rw [← e]; exact hn) hs
  · exact absurd hs hmy

/-- A value `< 0` is not a zero and has its sign bit set. -/
theorem neg_isZero_signBit {c : Binary32} (h : c < Binary32.ofBits 0x00000000) :
    Model.isZero (model c) = false ∧ Model.signBit (model c) = true := by
  have hcn := (isNaN_false_of_lt h).1
  have h' : Binary32.ofBits 0x00000000 < -c := by
    rw [lt_iff_ext isNaN_zero (by rw [isNaN_neg]; exact hcn), ext_zero, ext_neg hcn]
    rw [lt_iff_ext hcn isNaN_zero, ext_zero] at h
    exact EReal.neg_pos.2 h
  obtain ⟨hz, hs⟩ := pos_isZero_signBit h'
  simp only [model, ExecFloat.Binary.toModel_neg, Model.isZero_neg, Model.signBit_neg] at hz hs
  exact ⟨hz, by simpa using hs⟩

theorem model_eq_nativeOverflow_of_isInf {x : Binary32} (hx : Model.isInf (model x) = true) :
    model x = Model.nativeOverflow fmt (Model.signBit (model x)) := by
  cases hs : Model.signBit (model x)
  · rw [eq_posInf hx hs]; decide +kernel
  · rw [eq_negInf hx hs]; decide +kernel

theorem signBit_nativeOverflow (s : Bool) : Model.signBit (Model.nativeOverflow fmt s) = s := by
  cases s <;> simp [Model.nativeOverflow_eq_signedInf_of_isIEEE _ fmt_isIEEE]

/-- An infinity times a value `< 0` is the opposite infinity. -/
theorem mul_of_isInf_of_neg {x c : Binary32} (hx : Model.isInf (model x) = true) (hxn : Binary32.isNaN x = false)
    (hc : c < Binary32.ofBits 0x00000000) : x * c = -x := by
  obtain ⟨hz, hs⟩ := neg_isZero_signBit hc
  have hcn := (isNaN_false_of_lt hc).1
  apply model_inj
  simp only [model, ExecFloat.Binary.toModel_hMul, ExecFloat.Binary.toModel_neg]
  rw [model_mul_of_isInf_left hx hxn hcn hz]
  simp only [model] at hs; rw [hs]
  have e := model_eq_nativeOverflow_of_isInf hx
  simp only [model] at e
  rw [e, neg_nativeOverflow]
  show Model.nativeOverflow fmt (Model.signBit (model x) != true) = Model.nativeOverflow fmt (!Model.signBit (model x))
  congr 1

/-- A number times a finite non-zero value is a number. -/
theorem isNaN_mul_of_ne_zero {x c : Binary32} (hx : Binary32.isNaN x = false) (hcf : Binary32.isFinite c = true)
    (hc : Model.isZero (model c) = false) : Binary32.isNaN (x * c) = false := by
  rcases finite_or_inf hx with hf | rfl | rfl
  · exact isNaN_mul_of_isFinite hf hcf
  · show Model.isNaN (model _) = false
    simp only [model, ExecFloat.Binary.toModel_hMul]
    rw [model_mul_of_isInf_left isInf_model_posInf (by decide +kernel)
      (Model.isNaN_eq_false_of_isFinite_eq_true (model c) hcf) hc, Model.nativeOverflow_eq_signedInf_of_isIEEE _ fmt_isIEEE]
    split <;> simp
  · show Model.isNaN (model _) = false
    simp only [model, ExecFloat.Binary.toModel_hMul]
    rw [model_mul_of_isInf_left isInf_model_negInf (by decide +kernel)
      (Model.isNaN_eq_false_of_isFinite_eq_true (model c) hcf) hc, Model.nativeOverflow_eq_signedInf_of_isIEEE _ fmt_isIEEE]
    split <;> simp

/-- A finite value that is not a zero is `< 0` or `> 0`. -/
theorem lt_or_gt_of_ne_zero {c : Binary32} (hcf : Binary32.isFinite c = true) (hc : Model.isZero (model c) = false) :
    c < Binary32.ofBits 0x00000000 ∨ Binary32.ofBits 0x00000000 < c := by
  have hcn : Binary32.isNaN c = false := Model.isNaN_eq_false_of_isFinite_eq_true (model c) hcf
  have hr : real c ≠ 0 := by
    obtain ⟨d, hd⟩ := Model.exists_toDyadic?_of_isFinite (x := model c) hcf
    have hm := Model.significand_ne_zero_of_toDyadic?_some_of_isZero_eq_false hd hc
    show Model.toReal (model c) ≠ 0
    rw [Model.toReal_eq, hd]; simp only
    exact fun h => hm ((Model.Dyadic.toReal_eq_zero_iff d).1 h)
  rw [lt_iff_ext hcn isNaN_zero, lt_iff_ext isNaN_zero hcn, ext_zero, ext_of_isFinite hcf]
  rcases lt_or_gt_of_ne hr with h | h
  · left; exact_mod_cast h
  · right; exact_mod_cast h

end Corpus.F32

/-! ### Signs of products with a factor `≤ 0` -/

namespace Corpus.F32

theorem zero_mul_ext {c : Binary32} (hcf : Binary32.isFinite c = true) : ext (Binary32.ofBits 0x00000000 * c) = 0 := by
  rw [ext_mul_of_isFinite (by decide +kernel) hcf, real_eq_of_toRat? (q := 0) (by decide +kernel)]
  simp [rnd_zero]

/-- A value `≤ 0` times a finite value `> 0` is `≤ 0` (`-∞` included). -/
theorem mul_nonpos_of_pos {x c : Binary32} (hx : x ≤ Binary32.ofBits 0x00000000) (hcf : Binary32.isFinite c = true)
    (hc : Binary32.ofBits 0x00000000 < c) : x * c ≤ Binary32.ofBits 0x00000000 := by
  have h := mul_le_mul_of_pos_right' hx hcf hc
  have hz : Binary32.isNaN (Binary32.ofBits 0x00000000 * c) = false := isNaN_mul_of_isFinite (by decide +kernel) hcf
  have hxn := (isNaN_false_of_le hx).1
  rw [le_iff_ext (isNaN_mul_of_pos hxn hcf hc) hz, zero_mul_ext hcf] at h
  rw [le_zero_iff (isNaN_mul_of_pos hxn hcf hc)]; exact h

/-- A value `≤ 0` times a finite value `< 0` is `≥ 0` (`+∞` included). -/
theorem nonneg_of_mul_neg {x c : Binary32} (hx : x ≤ Binary32.ofBits 0x00000000) (hcf : Binary32.isFinite c = true)
    (hc : c < Binary32.ofBits 0x00000000) : Binary32.ofBits 0x00000000 ≤ x * c := by
  have hxn := (isNaN_false_of_le hx).1
  have hcn := (isNaN_false_of_lt hc).1
  have hnc : Binary32.ofBits 0x00000000 < -c := by
    rw [lt_iff_ext isNaN_zero (by rw [isNaN_neg]; exact hcn), ext_zero, ext_neg hcn]
    rw [lt_iff_ext hcn isNaN_zero, ext_zero] at hc
    exact EReal.neg_pos.2 hc
  have hncf : Binary32.isFinite (-c) = true := by rw [isFinite_neg]; exact hcf
  have h1 := mul_nonpos_of_pos hx hncf hnc
  have hn1 := isNaN_mul_of_pos hxn hncf hnc
  have e : x * c = -(x * (-c)) := by
    have := mul_neg' hxn (by rw [isNaN_neg]; exact hcn) hn1
    rw [neg_neg'] at this; exact this
  rw [e, zero_le_iff (by rw [isNaN_neg]; exact hn1), ext_neg hn1]
  rw [le_zero_iff hn1] at h1
  exact EReal.neg_nonneg.2 h1

end Corpus.F32

/-! ### `abs` of a negation; order under negation -/

namespace Corpus.F32

theorem abs_neg' (x : Binary32) : Binary32.abs (-x) = Binary32.abs x := by
  apply model_inj
  show ExecFloat.Binary.toModel (ExecFloat.Binary.abs (-x)) = ExecFloat.Binary.toModel (ExecFloat.Binary.abs x)
  rw [ExecFloat.Binary.toModel_abs, ExecFloat.Binary.toModel_abs, ExecFloat.Binary.toModel_neg, model_abs_eq,
    model_abs_eq, Model.signBit_neg]
  cases Model.signBit (ExecFloat.Binary.toModel x) <;> simp

theorem neg_lt_neg_iff' {x y : Binary32} (hx : Binary32.isNaN x = false) (hy : Binary32.isNaN y = false) :
    -x < -y ↔ y < x := by
  rw [lt_iff_ext (by rw [isNaN_neg]; exact hx) (by rw [isNaN_neg]; exact hy), ext_neg hx, ext_neg hy,
    EReal.neg_lt_neg_iff, lt_iff_ext hy hx]

theorem neg_le_neg_iff' {x y : Binary32} (hx : Binary32.isNaN x = false) (hy : Binary32.isNaN y = false) :
    -x ≤ -y ↔ y ≤ x := by
  rw [le_iff_ext (by rw [isNaN_neg]; exact hx) (by rw [isNaN_neg]; exact hy), ext_neg hx, ext_neg hy,
    EReal.neg_le_neg_iff, le_iff_ext hy hx]

end Corpus.F32

/-! ### Finiteness from a bound on the rounded value -/

namespace Corpus.F32

theorem isFinite_of_ext_eq_coe {x : Binary32} {r : ℝ} (hx : Binary32.isNaN x = false) (h : ext x = (r : EReal)) :
    Binary32.isFinite x = true := by
  rcases finite_or_inf hx with hf | rfl | rfl
  · exact hf
  · rw [ext_posInf] at h; exact absurd h.symm (EReal.coe_ne_top r)
  · rw [ext_negInf] at h; exact absurd h.symm (EReal.coe_ne_bot r)

/-- A difference of finite values whose unbounded rounding lies between two finite values is finite. -/
theorem isFinite_sub_of_roundAt_mem {x y lo hi : Binary32} (hx : Binary32.isFinite x = true)
    (hy : Binary32.isFinite y = true) (hlo : Binary32.isFinite lo = true) (hhi : Binary32.isFinite hi = true)
    (h1 : real lo ≤ Model.roundAt fmt (real x - real y)) (h2 : Model.roundAt fmt (real x - real y) ≤ real hi) :
    Binary32.isFinite (x - y) = true := by
  apply isFinite_of_ext_eq_coe (isNaN_sub_of_isFinite hx hy) (r := Model.roundAt fmt (real x - real y))
  rw [ext_sub_of_isFinite hx hy]
  unfold rnd
  rw [Corpus.ite_pos]
  have a1 := ExecFloat.Binary.abs_toReal_le_posMaxFinite_of_isFinite hlo
  have a2 := ExecFloat.Binary.abs_toReal_le_posMaxFinite_of_isFinite hhi
  rw [abs_le] at a1 a2 ⊢
  constructor <;> linarith [a1.1, a2.2]

/-- `1 - e` is finite for every finite `e` (at `e = -FLT_MAX` the exact `1 + FLT_MAX` rounds to `FLT_MAX`). -/
theorem isFinite_one_sub {e : Binary32} (he : Binary32.isFinite e = true) :
    Binary32.isFinite (Binary32.ofBits 0x3f800000 - e) = true := by
  have h1f : Binary32.isFinite (Binary32.ofBits 0x3f800000) = true := by decide +kernel
  have hmf : Binary32.isFinite (Binary32.ofBits 0x7f7fffff) = true := by decide +kernel
  have hnf : Binary32.isFinite (Binary32.ofBits 0xff7fffff) = true := by decide +kernel
  -- the two extreme cases, evaluated
  have ehi : Binary32.ofBits 0x3f800000 - Binary32.ofBits 0xff7fffff = Binary32.ofBits 0x7f7fffff := by decide +kernel
  have elo : Binary32.ofBits 0x3f800000 - Binary32.ofBits 0x7f7fffff = Binary32.ofBits 0xff7fffff := by decide +kernel
  have rhi : Model.roundAt fmt (real (Binary32.ofBits 0x3f800000) - real (Binary32.ofBits 0xff7fffff)) =
      real (Binary32.ofBits 0x7f7fffff) := by
    rw [← real_sub (by rw [ehi]; exact hmf), ehi]
  have rlo : Model.roundAt fmt (real (Binary32.ofBits 0x3f800000) - real (Binary32.ofBits 0x7f7fffff)) =
      real (Binary32.ofBits 0xff7fffff) := by
    rw [← real_sub (by rw [elo]; exact hnf), elo]
  have hb := ExecFloat.Binary.abs_toReal_le_posMaxFinite_of_isFinite he
  have emax : real (Binary32.ofBits 0x7f7fffff) = Model.toReal (Model.posMaxFinite fmt) := by
    rw [real_eq_of_toRat? (q := 340282346638528859811704183484516925440) (by decide +kernel),
      Model.Algebraic.toReal_of_toRat?_eq_some (q := 340282346638528859811704183484516925440) (by decide +kernel)]
  have emin : real (Binary32.ofBits 0xff7fffff) = -Model.toReal (Model.posMaxFinite fmt) := by
    rw [← emax, ← real_neg hmf]; congr 1
  rw [abs_le] at hb
  apply isFinite_sub_of_roundAt_mem h1f he hnf hmf
  · rw [← rlo]; apply Model.roundAt_mono; rw [emax]; linarith [hb.2]
  · rw [← rhi]; apply Model.roundAt_mono; rw [emin]; linarith [hb.1]

end Corpus.F32

/-! ## Fourth increment: `|x| ≤ c`, the NaN of a `double`'s absolute value, bits round trip -/

namespace Corpus.F32

/-- `|x| ≤ c` is `-c ≤ x ≤ c`, for every `x` (a NaN satisfies neither side). -/
theorem abs_le_iff {x c : Binary32} (hc : Binary32.isNaN c = false) :
    Binary32.abs x ≤ c ↔ -c ≤ x ∧ x ≤ c := by
  cases hx : Binary32.isNaN x
  · have hcn : Binary32.isNaN (-c) = false := by rw [isNaN_neg]; exact hc
    have hax : Binary32.isNaN (Binary32.abs x) = false := by rw [isNaN_abs]; exact hx
    rw [le_iff_ext hax hc, le_iff_ext hcn hx, le_iff_ext hx hc, ext_abs hx, ext_neg hc, max_le_iff,
      EReal.neg_le]
    exact and_comm
  · have hax : Binary32.isNaN (Binary32.abs x) = true := by rw [isNaN_abs]; exact hx
    exact iff_of_false (not_le_of_isNaN_left hax) (fun h => not_le_of_isNaN_right hx h.1)

/-- The bits of a word read back as a float are the word. -/
theorem toBits_ofBits (w : UInt32) : Binary32.toBits (Binary32.ofBits w) = w := rfl

end Corpus.F32

namespace Corpus.F64

theorem isNaN_abs (x : Binary64) : Binary64.isNaN (Binary64.abs x) = Binary64.isNaN x := by
  show Model.isNaN (ExecFloat.Binary.toModel (ExecFloat.Binary.abs x)) = _
  rw [ExecFloat.Binary.toModel_abs, Model.isNaN_abs]; rfl

end Corpus.F64
