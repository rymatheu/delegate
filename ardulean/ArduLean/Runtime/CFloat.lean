import FloatLib.Floats

/-!
Written by hand for cpp2lean; copied by `cpp2lean.py` next to every translation (`OutDir/CFloat.lean`).
Do not edit the copies.

C's `float` is FloatLib's `Binary32` and C's `double` is FloatLib's `Binary64` (IEEE 754 binary32 and
binary64, round to nearest even). The emitted code computes with FloatLib's operations only:
`+ - * /` (FloatLib's certified kernels), unary `-` (`Model.neg`, which flips the sign bit, as C's
negation does), `<`, `≤` (IEEE comparisons, false on NaN), `==` (IEEE equality, `0 == -0`, `NaN != NaN`)
and literals (`(0.1 : Binary32)`, FloatLib's `OfScientific`, the exact rational rounded once to
nearest even). The comparisons run on the bit patterns, by functions proved equal to FloatLib's
(`@[csimp]`, "Comparisons on the bit patterns" below). This module names the rest of C's
floating-point semantics the translator uses: the conversions between the two formats and to and
from the integer types, the bit patterns (C's `memcpy`/union access to a float's representation),
classification, and the functions of `<math.h>` that IEEE 754 defines exactly (`sqrt`, `fabs`,
`fmin`/`fmax`, `floor`, `ceil`, `trunc`, `round`, `copysign`, `scalbn`, `fma`) and the
classification macros (`isnan`, `isinf`, `isfinite`, `signbit`). Each is one FloatLib operation (or
a FloatLib operation and a clamp, for the conversions to integers); none goes through Lean's
`Float32`/`Float` or the C library. The functions of `<math.h>` that IEEE 754 does not define
exactly (`sin`, `pow`, ...) are not here: they are the translation of musl's C sources
(`Musl.lean`).
-/

open FloatLib.Floats
open FloatLib.Floats.Formats.BinaryInterchange (Model FloatFormat)

namespace Binary32

/-- The value with this bit pattern (every pattern, NaN payloads and signaling NaNs included). -/
@[inline] def ofBits (b : UInt32) : Binary32 := ExecFloat.Binary.ofBits32 b
/-- The bit pattern (C: `memcpy` of a `float` into a `uint32_t`, or a union). -/
@[inline] def toBits (x : Binary32) : UInt32 := ExecFloat.Binary.toBits32 x

/-- C `(double)x`: exact (FloatLib's binary32 to binary64 cast; a NaN keeps its sign and payload, quieted). -/
@[inline] def toBinary64 (x : Binary32) : Binary64 :=
  ExecFloat.Binary.ofModel (Model.cast .binary32 .binary64 (ExecFloat.Binary.toModel x))

/-- C `isnan`. -/
@[inline] def isNaN (x : Binary32) : Bool := ExecFloat.Binary.isNaN x
/-- C `isinf`. -/
@[inline] def isInf (x : Binary32) : Bool := ExecFloat.Binary.isInf x
/-- C `isfinite`. -/
@[inline] def isFinite (x : Binary32) : Bool := ExecFloat.Binary.isFinite x
/-- C `signbit`: whether the sign bit is set (also for a zero and a NaN). -/
@[inline] def signbit (x : Binary32) : Bool := ExecFloat.Binary.signBit x

/-- C `sqrtf`: IEEE 754 squareRoot, correctly rounded (FloatLib `ExecFloat.Binary.sqrt`). -/
@[inline] def sqrt (x : Binary32) : Binary32 := ExecFloat.Binary.sqrt x
/-- C `fabsf`: the value with the sign bit cleared (FloatLib `ExecFloat.Binary.abs`, IEEE 754 abs). -/
@[inline] def abs (x : Binary32) : Binary32 := ExecFloat.Binary.abs x
/-- C `fminf`: IEEE 754-2019 minimumNumber (FloatLib `minimumNumber`): the other operand if one is a
NaN, `-0` below `+0` (C99 F.10.9.3, and musl's `fminf`). -/
@[inline] def fmin (x y : Binary32) : Binary32 := ExecFloat.Binary.minimumNumber x y
/-- C `fmaxf`: IEEE 754-2019 maximumNumber (FloatLib `maximumNumber`): the other operand if one is a
NaN, `+0` above `-0` (C99 F.10.9.2, and musl's `fmaxf`). -/
@[inline] def fmax (x y : Binary32) : Binary32 := ExecFloat.Binary.maximumNumber x y
/-- C `floorf`: IEEE 754 roundToIntegralTowardNegative. -/
@[inline] def floor (x : Binary32) : Binary32 := ExecFloat.Binary.roundToIntegral x .down
/-- C `ceilf`: IEEE 754 roundToIntegralTowardPositive. -/
@[inline] def ceil (x : Binary32) : Binary32 := ExecFloat.Binary.roundToIntegral x .up
/-- C `truncf`: IEEE 754 roundToIntegralTowardZero. -/
@[inline] def trunc (x : Binary32) : Binary32 := ExecFloat.Binary.roundToIntegral x .towardZero
/-- C `roundf` (halfway cases away from zero): IEEE 754 roundToIntegralTiesToAway. -/
@[inline] def round (x : Binary32) : Binary32 := ExecFloat.Binary.roundToIntegral x .nearestAway
/-- C `copysignf`: the magnitude of `x` with the sign bit of `y` (IEEE 754 copySign). -/
@[inline] def copysign (x y : Binary32) : Binary32 := ExecFloat.Binary.copySign x y
/-- C `scalbnf`/`ldexpf`: `x * 2^n` rounded once (IEEE 754 scaleB). -/
@[inline] def scalbn (x : Binary32) (n : Int32) : Binary32 := ExecFloat.Binary.scale x n.toInt
/-- C `fmaf` (clang's `__builtin_fmaf`): `x * y + z` rounded once (IEEE 754 fusedMultiplyAdd). -/
@[inline] def fma (x y z : Binary32) : Binary32 := ExecFloat.Binary.fma x y z

end Binary32

namespace Binary64

/-- The value with this bit pattern (every pattern, NaN payloads and signaling NaNs included). -/
@[inline] def ofBits (b : UInt64) : Binary64 := ExecFloat.Binary.ofBits64 b
/-- The bit pattern (C: `memcpy` of a `double` into a `uint64_t`, or a union). -/
@[inline] def toBits (x : Binary64) : UInt64 := ExecFloat.Binary.toBits64 x

/-- C `(float)x`: rounded to nearest even (FloatLib's binary64 to binary32 cast; overflow gives an
infinity, a NaN keeps its sign and the payload if it fits, quieted). -/
@[inline] def toBinary32 (x : Binary64) : Binary32 :=
  ExecFloat.Binary.ofModel (Model.cast .binary64 .binary32 (ExecFloat.Binary.toModel x))

/-- C `isnan`. -/
@[inline] def isNaN (x : Binary64) : Bool := ExecFloat.Binary.isNaN x
/-- C `isinf`. -/
@[inline] def isInf (x : Binary64) : Bool := ExecFloat.Binary.isInf x
/-- C `isfinite`. -/
@[inline] def isFinite (x : Binary64) : Bool := ExecFloat.Binary.isFinite x
/-- C `signbit`: whether the sign bit is set (also for a zero and a NaN). -/
@[inline] def signbit (x : Binary64) : Bool := ExecFloat.Binary.signBit x

/-- C `sqrt`: IEEE 754 squareRoot, correctly rounded (FloatLib `ExecFloat.Binary.sqrt`). -/
@[inline] def sqrt (x : Binary64) : Binary64 := ExecFloat.Binary.sqrt x
/-- C `fabs`: the value with the sign bit cleared (IEEE 754 abs). -/
@[inline] def abs (x : Binary64) : Binary64 := ExecFloat.Binary.abs x
/-- C `fmin`: IEEE 754-2019 minimumNumber. -/
@[inline] def fmin (x y : Binary64) : Binary64 := ExecFloat.Binary.minimumNumber x y
/-- C `fmax`: IEEE 754-2019 maximumNumber. -/
@[inline] def fmax (x y : Binary64) : Binary64 := ExecFloat.Binary.maximumNumber x y
/-- C `floor`: IEEE 754 roundToIntegralTowardNegative. -/
@[inline] def floor (x : Binary64) : Binary64 := ExecFloat.Binary.roundToIntegral x .down
/-- C `ceil`: IEEE 754 roundToIntegralTowardPositive. -/
@[inline] def ceil (x : Binary64) : Binary64 := ExecFloat.Binary.roundToIntegral x .up
/-- C `trunc`: IEEE 754 roundToIntegralTowardZero. -/
@[inline] def trunc (x : Binary64) : Binary64 := ExecFloat.Binary.roundToIntegral x .towardZero
/-- C `round` (halfway cases away from zero): IEEE 754 roundToIntegralTiesToAway. -/
@[inline] def round (x : Binary64) : Binary64 := ExecFloat.Binary.roundToIntegral x .nearestAway
/-- C `copysign`: the magnitude of `x` with the sign bit of `y` (IEEE 754 copySign). -/
@[inline] def copysign (x y : Binary64) : Binary64 := ExecFloat.Binary.copySign x y
/-- C `scalbn`/`ldexp`: `x * 2^n` rounded once (IEEE 754 scaleB). -/
@[inline] def scalbn (x : Binary64) (n : Int32) : Binary64 := ExecFloat.Binary.scale x n.toInt
/-- C `fma` (clang's `__builtin_fma`): `x * y + z` rounded once (IEEE 754 fusedMultiplyAdd). -/
@[inline] def fma (x y z : Binary64) : Binary64 := ExecFloat.Binary.fma x y z

end Binary64

namespace CFloat

/-- The integer C's conversion to an integer type of range `[lo, hi]` gives: the value truncated
toward zero (FloatLib `toInt?`, mode `.towardZero`). Outside the range the conversion is undefined
in C; here it saturates, NaN gives 0 (what arm64's `fcvtzs`/`fcvtzu` compute, and what core Lean's
`Float32.toInt32` did). -/
@[inline] def truncSat32 (lo hi : Int) (x : Binary32) : Int :=
  match ExecFloat.Binary.toInt? x with
  | some n => if n < lo then lo else if n > hi then hi else n
  | none => if Binary32.isNaN x then 0 else if ExecFloat.Binary.signBit x then lo else hi

/-- As `truncSat32`, for `double`. -/
@[inline] def truncSat64 (lo hi : Int) (x : Binary64) : Int :=
  match ExecFloat.Binary.toInt? x with
  | some n => if n < lo then lo else if n > hi then hi else n
  | none => if Binary64.isNaN x then 0 else if ExecFloat.Binary.signBit x then lo else hi

/-- C's conversion of an integer to `float`: rounded to nearest even (FloatLib `ofRat`). -/
@[inline] def ofInt32 (n : Int) : Binary32 := ExecFloat.Binary.ofRat (n : Rat)
/-- C's conversion of an integer to `double`: rounded to nearest even (FloatLib `ofRat`). -/
@[inline] def ofInt64 (n : Int) : Binary64 := ExecFloat.Binary.ofRat (n : Rat)

end CFloat

/-! ## Comparisons on the bit patterns

FloatLib decides `<`, `≤` and `==` through `Model.compare`, which compares the exact dyadic values
of finite operands (about 2 µs a comparison, most of the run time of a translated controller). The
functions below decide the same relations on the bit patterns, with a few `UInt32`/`UInt64`
operations and no allocation, and the `@[csimp]` theorems prove each fast function equal to its
FloatLib function, so the compiler substitutes one for the other and the logical meaning of `<`,
`≤`, `==` stays FloatLib's.

The argument: a word is a NaN when its exponent field is all ones and its fraction field is not
zero, i.e. when its bits below the sign exceed those of `+∞`. On non-NaN words FloatLib's
`Model.adjacencyRank` (the word plus `2^(W-1)` for a positive sign, `2^W` minus the word for a
negative sign, so both zeros get rank `2^(W-1)`) orders the values as their extended reals
(`Model.adjacencyRank_lt_adjacencyRank_iff`, `Model.adjacencyRank_eq_adjacencyRank_iff`), and
`Model.compare` returns the order of the extended reals (`Model.compare_eq_of_toEReal?`). So on
non-NaN operands `Model.compare` is the order of the ranks, and `rankBits` computes the rank in
`UInt32`/`UInt64` without wrapping (it is at most `2^W - 1`).
-/

namespace CFloat.Compare

/-- A non-NaN value has an extended-real value. -/
theorem toEReal?_eq_some {fmt : FloatFormat} {x : Model fmt} (hx : Model.isNaN x = false) :
    Model.toEReal? x = some (Model.toEReal x) := by
  cases h : Model.toEReal? x with
  | none => rw [Model.toEReal?_eq_none_iff_isNaN_eq_true] at h; simp [h] at hx
  | some r => rw [Model.toEReal_of_toEReal? h]

/-- On non-NaN operands, FloatLib's comparison is the order of the adjacency ranks. -/
theorem compare_eq_rank {fmt : FloatFormat} {x y : Model fmt}
    (hx : Model.isNaN x = false) (hy : Model.isNaN y = false) :
    Model.compare x y = some (Ord.compare (Model.adjacencyRank x) (Model.adjacencyRank y)) := by
  rw [Model.compare_eq_of_toEReal? (toEReal?_eq_some hx) (toEReal?_eq_some hy)]
  congr 1
  rcases lt_trichotomy (Model.adjacencyRank x) (Model.adjacencyRank y) with h | h | h
  · rw [compare_lt_iff_lt.2 h,
      compare_lt_iff_lt.2 ((Model.adjacencyRank_lt_adjacencyRank_iff hx hy).1 h)]
  · rw [compare_eq_iff_eq.2 h,
      compare_eq_iff_eq.2 ((Model.adjacencyRank_eq_adjacencyRank_iff hx hy).1 h)]
  · rw [compare_gt_iff_gt.2 h,
      compare_gt_iff_gt.2 ((Model.adjacencyRank_lt_adjacencyRank_iff hy hx).1 h)]

/-- A comparison with a NaN operand is unordered. -/
theorem compare_eq_none {fmt : FloatFormat} {x y : Model fmt}
    (h : (Model.isNaN x || Model.isNaN y) = true) : Model.compare x y = none := by
  unfold Model.compare; simp [h]

/-- The exponent field, in natural-number arithmetic. -/
theorem expField_eq {fmt : FloatFormat} (m : Model fmt) :
    Model.expField m = m.bits.toNat / 2 ^ fmt.fracWidth % 2 ^ fmt.expWidth := by
  have h1 : 2 ^ fmt.expWidth - 1 < 2 ^ fmt.bitWidth := by
    have : 2 ^ fmt.expWidth ≤ 2 ^ fmt.bitWidth :=
      Nat.pow_le_pow_right (by decide) (by unfold FloatFormat.bitWidth; omega)
    have := Nat.two_pow_pos fmt.expWidth
    omega
  simp only [Model.expField, FloatFormat.expAllOnes, FloatFormat.ofWordNat,
    FloatFormat.expAllOnesNat, BitVec.toNat_and, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt h1, Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow]

/-- The fraction field, in natural-number arithmetic. -/
theorem fracField_eq {fmt : FloatFormat} (m : Model fmt) :
    Model.fracField m = m.bits.toNat % 2 ^ fmt.fracWidth := by
  have h1 : 2 ^ fmt.fracWidth - 1 < 2 ^ fmt.bitWidth := by
    have : 2 ^ fmt.fracWidth ≤ 2 ^ fmt.bitWidth :=
      Nat.pow_le_pow_right (by decide) (by unfold FloatFormat.bitWidth; omega)
    have := Nat.two_pow_pos fmt.fracWidth
    omega
  simp only [Model.fracField, FloatFormat.fracMask, FloatFormat.ofWordNat, FloatFormat.fracMaskNat,
    BitVec.toNat_and, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h1, Nat.and_two_pow_sub_one_eq_mod]

/-- The adjacency rank of a word of width `w`, in natural-number arithmetic. -/
theorem adjacencyRank_eq {fmt : FloatFormat} (m : Model fmt) {w : Nat} (hw : fmt.bitWidth = w) :
    Model.adjacencyRank m =
      if 2 ^ (w - 1) ≤ m.bits.toNat then 2 ^ w - m.bits.toNat
      else 2 ^ (w - 1) + m.bits.toNat := by
  subst hw
  rw [Model.adjacencyRank, Model.signBit_eq_msb, BitVec.msb_eq_decide]
  simp only [decide_eq_true_eq, FloatFormat.signMaskNat, FloatFormat.signBitIndex, Model.toNatBits]

theorem compare_lt_beq (a b : Nat) :
    (some (Ord.compare a b) == some Ordering.lt) = decide (a < b) := by
  rcases lt_trichotomy a b with h | h | h
  · simp [compare_lt_iff_lt.2 h, h]
  · simp [h]
  · simp [compare_gt_iff_gt.2 h, Nat.not_lt.2 h.le]

theorem compare_eq_beq (a b : Nat) :
    (some (Ord.compare a b) == some Ordering.eq) = decide (a = b) := by
  rcases lt_trichotomy a b with h | h | h
  · simp [compare_lt_iff_lt.2 h, h.ne]
  · simp [h]
  · simp [compare_gt_iff_gt.2 h, h.ne']

end CFloat.Compare

namespace Binary32

/-- C `x < y`: FloatLib's IEEE `<` (`ExecFloat.compareLess`; false on NaN). Computed by
`bltImpl`. -/
def blt (x y : Binary32) : Bool := ExecFloat.compareLess x y
/-- C `x <= y`: FloatLib's IEEE `≤` (`ExecFloat.compareLessEqual`). Computed by `bleImpl`. -/
def ble (x y : Binary32) : Bool := ExecFloat.compareLessEqual x y
/-- C `x == y`: FloatLib's IEEE equality (`ExecFloat.compareEqual`; `0 == -0`, `NaN != NaN`).
Computed by `beqImpl`. -/
def beq (x y : Binary32) : Bool := ExecFloat.compareEqual x y

/-- Whether the bit pattern is a NaN: the bits below the sign exceed those of `+∞`. -/
@[inline] def isNaNBits (b : UInt32) : Bool := 0x7f800000 < (b &&& 0x7fffffff)
/-- FloatLib's `Model.adjacencyRank` of the bit pattern (`rankBits_toBits`): `2^31 + b` for a
positive sign, `2^32 - b` for a negative sign, so `-0` and `+0` both get `2^31`. -/
@[inline] def rankBits (b : UInt32) : UInt32 :=
  if 0x80000000 ≤ b then 0 - b else b + 0x80000000

/-- `blt` on the bit patterns (`blt_eq_bltImpl`). -/
@[inline] def bltImpl (x y : Binary32) : Bool :=
  let a := toBits x; let b := toBits y
  !isNaNBits a && !isNaNBits b && rankBits a < rankBits b
/-- `ble` on the bit patterns (`ble_eq_bleImpl`). -/
@[inline] def bleImpl (x y : Binary32) : Bool :=
  let a := toBits x; let b := toBits y
  !isNaNBits a && !isNaNBits b && rankBits a ≤ rankBits b
/-- `beq` on the bit patterns (`beq_eq_beqImpl`). -/
@[inline] def beqImpl (x y : Binary32) : Bool :=
  let a := toBits x; let b := toBits y
  !isNaNBits a && !isNaNBits b && rankBits a == rankBits b

theorem isNaNBits_toBits (x : Binary32) :
    isNaNBits (toBits x) = Model.isNaN (ExecFloat.Binary.toModel x) := by
  have hb : (ExecFloat.Binary.toModel x).bits.toNat = (toBits x).toNat := rfl
  have hn := UInt32.toNat_lt (toBits x)
  have hand : (toBits x &&& 0x7fffffff).toNat = (toBits x).toNat % 2 ^ 31 := by
    rw [UInt32.toNat_and]; exact Nat.and_two_pow_sub_one_eq_mod _ 31
  have hdec : isNaNBits (toBits x) = decide (0x7f800000 < (toBits x).toNat % 2 ^ 31) := by
    rw [Bool.eq_iff_iff]
    simp only [isNaNBits, decide_eq_true_eq, UInt32.lt_iff_toNat_lt, hand, UInt32.reduceToNat]
  rw [hdec]
  generalize ExecFloat.Binary.toModel x = m at *
  generalize (toBits x).toNat = n at *
  subst hb
  show _ = Model.IEEE.isNaN m
  simp only [Model.IEEE.isNaN, CFloat.Compare.expField_eq, CFloat.Compare.fracField_eq,
    FloatFormat.expAllOnesNat]
  generalize BitVec.toNat m.bits = n at *
  rw [Bool.eq_iff_iff]
  simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne, decide_eq_true_eq]
  omega

theorem rankBits_toBits (x : Binary32) :
    (rankBits (toBits x)).toNat = Model.adjacencyRank (ExecFloat.Binary.toModel x) := by
  have hb : (ExecFloat.Binary.toModel x).bits.toNat = (toBits x).toNat := rfl
  have hn := UInt32.toNat_lt (toBits x)
  rw [CFloat.Compare.adjacencyRank_eq _ (w := 32) rfl, hb, rankBits]
  split <;> split <;>
    simp only [UInt32.le_iff_toNat_le, UInt32.toNat_sub, UInt32.toNat_add, UInt32.reduceToNat,
      Nat.reduceSub, Nat.reducePow] at * <;> omega

@[csimp] theorem blt_eq_bltImpl : @blt = @bltImpl := by
  funext x y
  simp only [blt, bltImpl, ExecFloat.compareLess, ExecFloat.Binary.compare_eq_compare_toModel,
    isNaNBits_toBits]
  cases hx : Model.isNaN (ExecFloat.Binary.toModel x) <;>
    cases hy : Model.isNaN (ExecFloat.Binary.toModel y)
  · rw [CFloat.Compare.compare_eq_rank hx hy, CFloat.Compare.compare_lt_beq, Bool.eq_iff_iff]
    simp [UInt32.lt_iff_toNat_lt, rankBits_toBits]
  all_goals rw [CFloat.Compare.compare_eq_none (by simp [hx, hy])]; rfl

@[csimp] theorem ble_eq_bleImpl : @ble = @bleImpl := by
  funext x y
  simp only [ble, bleImpl, ExecFloat.compareLessEqual, ExecFloat.Binary.compare_eq_compare_toModel,
    isNaNBits_toBits]
  cases hx : Model.isNaN (ExecFloat.Binary.toModel x) <;>
    cases hy : Model.isNaN (ExecFloat.Binary.toModel y)
  · rw [CFloat.Compare.compare_eq_rank hx hy]
    have hle : decide (rankBits (toBits x) ≤ rankBits (toBits y)) =
        decide (Model.adjacencyRank (ExecFloat.Binary.toModel x) ≤
          Model.adjacencyRank (ExecFloat.Binary.toModel y)) := by
      simp only [UInt32.le_iff_toNat_le, rankBits_toBits]
    rw [hle]
    rcases lt_trichotomy (Model.adjacencyRank (ExecFloat.Binary.toModel x))
      (Model.adjacencyRank (ExecFloat.Binary.toModel y)) with h | h | h
    · rw [compare_lt_iff_lt.2 h]; simp [h.le]
    · rw [compare_eq_iff_eq.2 h]; simp [h]
    · rw [compare_gt_iff_gt.2 h]; simp [Nat.not_le.2 h]
  all_goals rw [CFloat.Compare.compare_eq_none (by simp [hx, hy])]; rfl

@[csimp] theorem beq_eq_beqImpl : @beq = @beqImpl := by
  funext x y
  simp only [beq, beqImpl, ExecFloat.compareEqual, ExecFloat.Binary.compare_eq_compare_toModel,
    isNaNBits_toBits]
  cases hx : Model.isNaN (ExecFloat.Binary.toModel x) <;>
    cases hy : Model.isNaN (ExecFloat.Binary.toModel y)
  · rw [CFloat.Compare.compare_eq_rank hx hy, CFloat.Compare.compare_eq_beq, Bool.eq_iff_iff]
    simp [← UInt32.toNat_inj, rankBits_toBits]
  all_goals rw [CFloat.Compare.compare_eq_none (by simp [hx, hy])]; rfl

/-! `fmin`/`fmax` (FloatLib's `minimumNumber`/`maximumNumber`) on the bit patterns: a NaN operand
gives the other operand, two numbers are ordered by `rankBits`, and of two zeros `fmin` takes the
negative one and `fmax` the positive one (FloatLib's `Model.minimum`/`Model.maximum`). Only two NaN
operands, whose result FloatLib chooses (`bothNaNNumber`), are left to FloatLib's function. -/

/-- FloatLib's `isZero` on the bit pattern: the bits below the sign are zero. -/
theorem isZero_toModel (x : Binary32) :
    Model.isZero (ExecFloat.Binary.toModel x) = ((toBits x &&& 0x7fffffff) == 0) := by
  have hb : (ExecFloat.Binary.toModel x).bits.toNat = (toBits x).toNat := rfl
  have hand : (toBits x &&& 0x7fffffff).toNat = (toBits x).toNat % 2 ^ 31 := by
    rw [UInt32.toNat_and]; exact Nat.and_two_pow_sub_one_eq_mod _ 31
  have hdec : ((toBits x &&& 0x7fffffff) == 0) = decide ((toBits x).toNat % 2 ^ 31 = 0) := by
    rw [Bool.eq_iff_iff]
    simp only [beq_iff_eq, decide_eq_true_eq, ← UInt32.toNat_inj, hand, UInt32.reduceToNat]
  rw [hdec]
  generalize ExecFloat.Binary.toModel x = m at *
  generalize (toBits x).toNat = n at *
  subst hb
  show Model.IEEE.isZero m = _
  simp only [Model.IEEE.isZero, CFloat.Compare.expField_eq, CFloat.Compare.fracField_eq]
  generalize BitVec.toNat m.bits = n at *
  rw [Bool.eq_iff_iff]
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq]
  omega

/-- FloatLib's comparison of two non-NaN values is the order of their `rankBits`. -/
theorem compareNonNaN_eq {x y : Binary32} (hx : Model.isNaN (ExecFloat.Binary.toModel x) = false)
    (hy : Model.isNaN (ExecFloat.Binary.toModel y) = false) :
    Model.compareNonNaN (ExecFloat.Binary.toModel x) (ExecFloat.Binary.toModel y) hx hy =
      Ord.compare (rankBits (toBits x)).toNat (rankBits (toBits y)).toNat := by
  have h := CFloat.Compare.compare_eq_rank hx hy
  simp only [Model.compare, hx, hy, Bool.or_false, Bool.false_eq_true, dite_false,
    Option.some.injEq] at h
  rw [h, rankBits_toBits, rankBits_toBits]

/-- A zero is FloatLib's `Model.zero` with its sign. -/
theorem toModel_eq_zero (x : Binary32) (hz : (toBits x &&& 0x7fffffff) = 0) :
    ExecFloat.Binary.toModel x = Model.zero _ (decide (0x80000000 ≤ toBits x)) := by
  have hb : (ExecFloat.Binary.toModel x).bits.toNat = (toBits x).toNat := rfl
  have hn := UInt32.toNat_lt (toBits x)
  have hand : (toBits x &&& 0x7fffffff).toNat = (toBits x).toNat % 2 ^ 31 := by
    rw [UInt32.toNat_and]; exact Nat.and_two_pow_sub_one_eq_mod _ 31
  rw [hz] at hand
  simp only [UInt32.reduceToNat] at hand
  rw [← Model.ofBits_toBits (ExecFloat.Binary.toModel x)]
  by_cases hs : (0x80000000 : UInt32) ≤ toBits x
  · rw [decide_eq_true hs, show Model.zero _ true = Model.negZero _ from rfl, Model.negZero]
    congr 1
    apply BitVec.eq_of_toNat_eq
    rw [Model.toBits, hb, FloatFormat.signMask_toNat]
    simp only [UInt32.le_iff_toNat_le, UInt32.reduceToNat] at hs
    simp only [FloatFormat.bitWidth, Nat.reduceAdd, Nat.reduceSub, Nat.reducePow]
    omega
  · rw [decide_eq_false hs, show Model.zero _ false = Model.posZero _ from rfl, Model.posZero,
      Model.ofNatBits]
    congr 1
    apply BitVec.eq_of_toNat_eq
    rw [Model.toBits, hb, FloatFormat.ofWordNat, BitVec.toNat_ofNat]
    simp only [UInt32.le_iff_toNat_le, UInt32.reduceToNat] at hs
    simp only [Nat.zero_mod]
    omega

/-- FloatLib's `signBit` on the bit pattern. -/
theorem signBit_toModel (x : Binary32) :
    Model.signBit (ExecFloat.Binary.toModel x) = decide (0x80000000 ≤ toBits x) := by
  have hb : (ExecFloat.Binary.toModel x).bits.toNat = (toBits x).toNat := rfl
  rw [Model.signBit_eq_msb, BitVec.msb_eq_decide, hb]
  simp only [UInt32.le_iff_toNat_le, UInt32.reduceToNat, FloatFormat.bitWidth, Nat.reduceAdd,
    Nat.reduceSub, Nat.reducePow]
  exact decide_eq_decide.mpr Iff.rfl

/-- `fmin` on the bit patterns (`fmin_eq_fminImpl`); two NaNs go to FloatLib's `minimumNumber`. -/
@[inline] def fminImpl (x y : Binary32) : Binary32 :=
  let a := toBits x; let b := toBits y
  if isNaNBits a then (if isNaNBits b then ExecFloat.Binary.minimumNumber x y else y)
  else if isNaNBits b then x
  else
    let ra := rankBits a; let rb := rankBits b
    if ra < rb then x else if rb < ra then y
    else if (a &&& 0x7fffffff) == 0 && (b &&& 0x7fffffff) == 0 then
      (if 0x80000000 ≤ a then x else y)
    else x

@[csimp] theorem fmin_eq_fminImpl : @fmin = @fminImpl := by
  funext x y
  have hx' := isNaNBits_toBits x
  have hy' := isNaNBits_toBits y
  have hspec : ExecFloat.Binary.minimumNumber x y = ExecFloat.Binary.ofModel
      (Model.Internal.Value.minimumNumber (ExecFloat.Binary.toModel x)
        (ExecFloat.Binary.toModel y)) := rfl
  rw [fmin, fminImpl, hspec]
  cases hx : Model.isNaN (ExecFloat.Binary.toModel x) <;>
    cases hy : Model.isNaN (ExecFloat.Binary.toModel y) <;>
    simp only [hx', hy', hx, hy, Bool.false_eq_true, ↓reduceIte,
      Model.Internal.Value.minimumNumber, ExecFloat.Binary.ofModel_toModel]
  · have hsel : Model.chooseNaN2 (ExecFloat.Binary.toModel x) (ExecFloat.Binary.toModel y) = none :=
      (Model.chooseNaN2_eq_none_iff _ _).2 ⟨hx, hy⟩
    simp only [Model.minimum, Model.Internal.Value.minimum, Model.withNaNSelection, hsel,
      ↓reduceDIte]
    rw [compareNonNaN_eq hx hy]
    simp only [isZero_toModel, signBit_toModel, UInt32.lt_iff_toNat_lt]
    rcases lt_trichotomy (rankBits (toBits x)).toNat (rankBits (toBits y)).toNat with h | h | h
    · simp [compare_lt_iff_lt.2 h, h]
    · rw [compare_eq_iff_eq.2 h]
      simp only [h, Nat.lt_irrefl, ↓reduceIte]
      by_cases hz : (toBits x &&& 0x7fffffff) = 0 ∧ (toBits y &&& 0x7fffffff) = 0
      · simp only [hz, beq_self_eq_true, Bool.and_self, ↓reduceIte]
        by_cases hs : (0x80000000 : UInt32) ≤ toBits x
        · simp only [hs, decide_true, Bool.true_or, ↓reduceIte]
          rw [← decide_eq_true hs, ← toModel_eq_zero x hz.1, ExecFloat.Binary.ofModel_toModel]
        · simp only [hs, decide_false, Bool.false_or, ↓reduceIte]
          rw [← toModel_eq_zero y hz.2, ExecFloat.Binary.ofModel_toModel]
      · have : ((toBits x &&& 0x7fffffff == 0) && (toBits y &&& 0x7fffffff == 0)) = false := by
          simpa using hz
        simp [this]
    · simp [compare_gt_iff_gt.2 h, h, Nat.not_lt.2 h.le]

/-- `fmax` on the bit patterns (`fmax_eq_fmaxImpl`); two NaNs go to FloatLib's `maximumNumber`. -/
@[inline] def fmaxImpl (x y : Binary32) : Binary32 :=
  let a := toBits x; let b := toBits y
  if isNaNBits a then (if isNaNBits b then ExecFloat.Binary.maximumNumber x y else y)
  else if isNaNBits b then x
  else
    let ra := rankBits a; let rb := rankBits b
    if ra < rb then y else if rb < ra then x
    else if (a &&& 0x7fffffff) == 0 && (b &&& 0x7fffffff) == 0 then
      (if 0x80000000 ≤ a then y else x)
    else x

@[csimp] theorem fmax_eq_fmaxImpl : @fmax = @fmaxImpl := by
  funext x y
  have hx' := isNaNBits_toBits x
  have hy' := isNaNBits_toBits y
  have hspec : ExecFloat.Binary.maximumNumber x y = ExecFloat.Binary.ofModel
      (Model.Internal.Value.maximumNumber (ExecFloat.Binary.toModel x)
        (ExecFloat.Binary.toModel y)) := rfl
  rw [fmax, fmaxImpl, hspec]
  cases hx : Model.isNaN (ExecFloat.Binary.toModel x) <;>
    cases hy : Model.isNaN (ExecFloat.Binary.toModel y) <;>
    simp only [hx', hy', hx, hy, Bool.false_eq_true, ↓reduceIte,
      Model.Internal.Value.maximumNumber, ExecFloat.Binary.ofModel_toModel]
  · have hsel : Model.chooseNaN2 (ExecFloat.Binary.toModel x) (ExecFloat.Binary.toModel y) = none :=
      (Model.chooseNaN2_eq_none_iff _ _).2 ⟨hx, hy⟩
    simp only [Model.maximum, Model.Internal.Value.maximum, Model.withNaNSelection, hsel,
      ↓reduceDIte]
    rw [compareNonNaN_eq hx hy]
    simp only [isZero_toModel, signBit_toModel, UInt32.lt_iff_toNat_lt]
    rcases lt_trichotomy (rankBits (toBits x)).toNat (rankBits (toBits y)).toNat with h | h | h
    · simp [compare_lt_iff_lt.2 h, h]
    · rw [compare_eq_iff_eq.2 h]
      simp only [h, Nat.lt_irrefl, ↓reduceIte]
      by_cases hz : (toBits x &&& 0x7fffffff) = 0 ∧ (toBits y &&& 0x7fffffff) = 0
      · simp only [hz, beq_self_eq_true, Bool.and_self, ↓reduceIte]
        by_cases hs : (0x80000000 : UInt32) ≤ toBits x
        · simp only [hs, decide_true, Bool.true_and, ↓reduceIte]
          rw [← toModel_eq_zero y hz.2, ExecFloat.Binary.ofModel_toModel]
        · simp only [hs, decide_false, Bool.false_and, ↓reduceIte]
          rw [← decide_eq_false hs, ← toModel_eq_zero x hz.1, ExecFloat.Binary.ofModel_toModel]
      · have : ((toBits x &&& 0x7fffffff == 0) && (toBits y &&& 0x7fffffff == 0)) = false := by
          simpa using hz
        simp [this]
    · simp [compare_gt_iff_gt.2 h, h, Nat.not_lt.2 h.le]

end Binary32

namespace Binary64

/-- C `x < y` on `double`: FloatLib's IEEE `<` (`ExecFloat.compareLess`; false on NaN). Computed
by `bltImpl`. -/
def blt (x y : Binary64) : Bool := ExecFloat.compareLess x y
/-- C `x <= y` on `double`: FloatLib's IEEE `≤` (`ExecFloat.compareLessEqual`). Computed by
`bleImpl`. -/
def ble (x y : Binary64) : Bool := ExecFloat.compareLessEqual x y
/-- C `x == y` on `double`: FloatLib's IEEE equality (`ExecFloat.compareEqual`; `0 == -0`,
`NaN != NaN`). Computed by `beqImpl`. -/
def beq (x y : Binary64) : Bool := ExecFloat.compareEqual x y

/-- Whether the bit pattern is a NaN: the bits below the sign exceed those of `+∞`. -/
@[inline] def isNaNBits (b : UInt64) : Bool := 0x7ff0000000000000 < (b &&& 0x7fffffffffffffff)
/-- FloatLib's `Model.adjacencyRank` of the bit pattern (`rankBits_toBits`): `2^63 + b` for a
positive sign, `2^64 - b` for a negative sign, so `-0` and `+0` both get `2^63`. -/
@[inline] def rankBits (b : UInt64) : UInt64 :=
  if 0x8000000000000000 ≤ b then 0 - b else b + 0x8000000000000000

/-- `blt` on the bit patterns (`blt_eq_bltImpl`). -/
@[inline] def bltImpl (x y : Binary64) : Bool :=
  let a := toBits x; let b := toBits y
  !isNaNBits a && !isNaNBits b && rankBits a < rankBits b
/-- `ble` on the bit patterns (`ble_eq_bleImpl`). -/
@[inline] def bleImpl (x y : Binary64) : Bool :=
  let a := toBits x; let b := toBits y
  !isNaNBits a && !isNaNBits b && rankBits a ≤ rankBits b
/-- `beq` on the bit patterns (`beq_eq_beqImpl`). -/
@[inline] def beqImpl (x y : Binary64) : Bool :=
  let a := toBits x; let b := toBits y
  !isNaNBits a && !isNaNBits b && rankBits a == rankBits b

theorem isNaNBits_toBits (x : Binary64) :
    isNaNBits (toBits x) = Model.isNaN (ExecFloat.Binary.toModel x) := by
  have hb : (ExecFloat.Binary.toModel x).bits.toNat = (toBits x).toNat := rfl
  have hn := UInt64.toNat_lt (toBits x)
  have hand : (toBits x &&& 0x7fffffffffffffff).toNat = (toBits x).toNat % 2 ^ 63 := by
    rw [UInt64.toNat_and]; exact Nat.and_two_pow_sub_one_eq_mod _ 63
  have hdec : isNaNBits (toBits x) = decide (0x7ff0000000000000 < (toBits x).toNat % 2 ^ 63) := by
    rw [Bool.eq_iff_iff]
    simp only [isNaNBits, decide_eq_true_eq, UInt64.lt_iff_toNat_lt, hand, UInt64.reduceToNat]
  rw [hdec]
  generalize ExecFloat.Binary.toModel x = m at *
  generalize (toBits x).toNat = n at *
  subst hb
  show _ = Model.IEEE.isNaN m
  simp only [Model.IEEE.isNaN, CFloat.Compare.expField_eq, CFloat.Compare.fracField_eq,
    FloatFormat.expAllOnesNat]
  generalize BitVec.toNat m.bits = n at *
  rw [Bool.eq_iff_iff]
  simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne, decide_eq_true_eq]
  omega

theorem rankBits_toBits (x : Binary64) :
    (rankBits (toBits x)).toNat = Model.adjacencyRank (ExecFloat.Binary.toModel x) := by
  have hb : (ExecFloat.Binary.toModel x).bits.toNat = (toBits x).toNat := rfl
  have hn := UInt64.toNat_lt (toBits x)
  rw [CFloat.Compare.adjacencyRank_eq _ (w := 64) rfl, hb, rankBits]
  split <;> split <;>
    simp only [UInt64.le_iff_toNat_le, UInt64.toNat_sub, UInt64.toNat_add, UInt64.reduceToNat,
      Nat.reduceSub, Nat.reducePow] at * <;> omega

@[csimp] theorem blt_eq_bltImpl : @blt = @bltImpl := by
  funext x y
  simp only [blt, bltImpl, ExecFloat.compareLess, ExecFloat.Binary.compare_eq_compare_toModel,
    isNaNBits_toBits]
  cases hx : Model.isNaN (ExecFloat.Binary.toModel x) <;>
    cases hy : Model.isNaN (ExecFloat.Binary.toModel y)
  · rw [CFloat.Compare.compare_eq_rank hx hy, CFloat.Compare.compare_lt_beq, Bool.eq_iff_iff]
    simp [UInt64.lt_iff_toNat_lt, rankBits_toBits]
  all_goals rw [CFloat.Compare.compare_eq_none (by simp [hx, hy])]; rfl

@[csimp] theorem ble_eq_bleImpl : @ble = @bleImpl := by
  funext x y
  simp only [ble, bleImpl, ExecFloat.compareLessEqual, ExecFloat.Binary.compare_eq_compare_toModel,
    isNaNBits_toBits]
  cases hx : Model.isNaN (ExecFloat.Binary.toModel x) <;>
    cases hy : Model.isNaN (ExecFloat.Binary.toModel y)
  · rw [CFloat.Compare.compare_eq_rank hx hy]
    have hle : decide (rankBits (toBits x) ≤ rankBits (toBits y)) =
        decide (Model.adjacencyRank (ExecFloat.Binary.toModel x) ≤
          Model.adjacencyRank (ExecFloat.Binary.toModel y)) := by
      simp only [UInt64.le_iff_toNat_le, rankBits_toBits]
    rw [hle]
    rcases lt_trichotomy (Model.adjacencyRank (ExecFloat.Binary.toModel x))
      (Model.adjacencyRank (ExecFloat.Binary.toModel y)) with h | h | h
    · rw [compare_lt_iff_lt.2 h]; simp [h.le]
    · rw [compare_eq_iff_eq.2 h]; simp [h]
    · rw [compare_gt_iff_gt.2 h]; simp [Nat.not_le.2 h]
  all_goals rw [CFloat.Compare.compare_eq_none (by simp [hx, hy])]; rfl

@[csimp] theorem beq_eq_beqImpl : @beq = @beqImpl := by
  funext x y
  simp only [beq, beqImpl, ExecFloat.compareEqual, ExecFloat.Binary.compare_eq_compare_toModel,
    isNaNBits_toBits]
  cases hx : Model.isNaN (ExecFloat.Binary.toModel x) <;>
    cases hy : Model.isNaN (ExecFloat.Binary.toModel y)
  · rw [CFloat.Compare.compare_eq_rank hx hy, CFloat.Compare.compare_eq_beq, Bool.eq_iff_iff]
    simp [← UInt64.toNat_inj, rankBits_toBits]
  all_goals rw [CFloat.Compare.compare_eq_none (by simp [hx, hy])]; rfl

/-! `fmin`/`fmax` (FloatLib's `minimumNumber`/`maximumNumber`) on the bit patterns: a NaN operand
gives the other operand, two numbers are ordered by `rankBits`, and of two zeros `fmin` takes the
negative one and `fmax` the positive one (FloatLib's `Model.minimum`/`Model.maximum`). Only two NaN
operands, whose result FloatLib chooses (`bothNaNNumber`), are left to FloatLib's function. -/

/-- FloatLib's `isZero` on the bit pattern: the bits below the sign are zero. -/
theorem isZero_toModel (x : Binary64) :
    Model.isZero (ExecFloat.Binary.toModel x) = ((toBits x &&& 0x7fffffffffffffff) == 0) := by
  have hb : (ExecFloat.Binary.toModel x).bits.toNat = (toBits x).toNat := rfl
  have hand : (toBits x &&& 0x7fffffffffffffff).toNat = (toBits x).toNat % 2 ^ 63 := by
    rw [UInt64.toNat_and]; exact Nat.and_two_pow_sub_one_eq_mod _ 63
  have hdec :
      ((toBits x &&& 0x7fffffffffffffff) == 0) = decide ((toBits x).toNat % 2 ^ 63 = 0) := by
    rw [Bool.eq_iff_iff]
    simp only [beq_iff_eq, decide_eq_true_eq, ← UInt64.toNat_inj, hand, UInt64.reduceToNat]
  rw [hdec]
  generalize ExecFloat.Binary.toModel x = m at *
  generalize (toBits x).toNat = n at *
  subst hb
  show Model.IEEE.isZero m = _
  simp only [Model.IEEE.isZero, CFloat.Compare.expField_eq, CFloat.Compare.fracField_eq]
  generalize BitVec.toNat m.bits = n at *
  rw [Bool.eq_iff_iff]
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq]
  omega

/-- FloatLib's comparison of two non-NaN values is the order of their `rankBits`. -/
theorem compareNonNaN_eq {x y : Binary64} (hx : Model.isNaN (ExecFloat.Binary.toModel x) = false)
    (hy : Model.isNaN (ExecFloat.Binary.toModel y) = false) :
    Model.compareNonNaN (ExecFloat.Binary.toModel x) (ExecFloat.Binary.toModel y) hx hy =
      Ord.compare (rankBits (toBits x)).toNat (rankBits (toBits y)).toNat := by
  have h := CFloat.Compare.compare_eq_rank hx hy
  simp only [Model.compare, hx, hy, Bool.or_false, Bool.false_eq_true, dite_false,
    Option.some.injEq] at h
  rw [h, rankBits_toBits, rankBits_toBits]

/-- A zero is FloatLib's `Model.zero` with its sign. -/
theorem toModel_eq_zero (x : Binary64) (hz : (toBits x &&& 0x7fffffffffffffff) = 0) :
    ExecFloat.Binary.toModel x = Model.zero _ (decide (0x8000000000000000 ≤ toBits x)) := by
  have hb : (ExecFloat.Binary.toModel x).bits.toNat = (toBits x).toNat := rfl
  have hn := UInt64.toNat_lt (toBits x)
  have hand : (toBits x &&& 0x7fffffffffffffff).toNat = (toBits x).toNat % 2 ^ 63 := by
    rw [UInt64.toNat_and]; exact Nat.and_two_pow_sub_one_eq_mod _ 63
  rw [hz] at hand
  simp only [UInt64.reduceToNat] at hand
  rw [← Model.ofBits_toBits (ExecFloat.Binary.toModel x)]
  by_cases hs : (0x8000000000000000 : UInt64) ≤ toBits x
  · rw [decide_eq_true hs, show Model.zero _ true = Model.negZero _ from rfl, Model.negZero]
    congr 1
    apply BitVec.eq_of_toNat_eq
    rw [Model.toBits, hb, FloatFormat.signMask_toNat]
    simp only [UInt64.le_iff_toNat_le, UInt64.reduceToNat] at hs
    simp only [FloatFormat.bitWidth, Nat.reduceAdd, Nat.reduceSub, Nat.reducePow]
    omega
  · rw [decide_eq_false hs, show Model.zero _ false = Model.posZero _ from rfl, Model.posZero,
      Model.ofNatBits]
    congr 1
    apply BitVec.eq_of_toNat_eq
    rw [Model.toBits, hb, FloatFormat.ofWordNat, BitVec.toNat_ofNat]
    simp only [UInt64.le_iff_toNat_le, UInt64.reduceToNat] at hs
    simp only [Nat.zero_mod]
    omega

/-- FloatLib's `signBit` on the bit pattern. -/
theorem signBit_toModel (x : Binary64) :
    Model.signBit (ExecFloat.Binary.toModel x) = decide (0x8000000000000000 ≤ toBits x) := by
  have hb : (ExecFloat.Binary.toModel x).bits.toNat = (toBits x).toNat := rfl
  rw [Model.signBit_eq_msb, BitVec.msb_eq_decide, hb]
  simp only [UInt64.le_iff_toNat_le, UInt64.reduceToNat, FloatFormat.bitWidth, Nat.reduceAdd,
    Nat.reduceSub, Nat.reducePow]
  exact decide_eq_decide.mpr Iff.rfl

/-- `fmin` on the bit patterns (`fmin_eq_fminImpl`); two NaNs go to FloatLib's `minimumNumber`. -/
@[inline] def fminImpl (x y : Binary64) : Binary64 :=
  let a := toBits x; let b := toBits y
  if isNaNBits a then (if isNaNBits b then ExecFloat.Binary.minimumNumber x y else y)
  else if isNaNBits b then x
  else
    let ra := rankBits a; let rb := rankBits b
    if ra < rb then x else if rb < ra then y
    else if (a &&& 0x7fffffffffffffff) == 0 && (b &&& 0x7fffffffffffffff) == 0 then
      (if 0x8000000000000000 ≤ a then x else y)
    else x

@[csimp] theorem fmin_eq_fminImpl : @fmin = @fminImpl := by
  funext x y
  have hx' := isNaNBits_toBits x
  have hy' := isNaNBits_toBits y
  have hspec : ExecFloat.Binary.minimumNumber x y = ExecFloat.Binary.ofModel
      (Model.Internal.Value.minimumNumber (ExecFloat.Binary.toModel x)
        (ExecFloat.Binary.toModel y)) := rfl
  rw [fmin, fminImpl, hspec]
  cases hx : Model.isNaN (ExecFloat.Binary.toModel x) <;>
    cases hy : Model.isNaN (ExecFloat.Binary.toModel y) <;>
    simp only [hx', hy', hx, hy, Bool.false_eq_true, ↓reduceIte,
      Model.Internal.Value.minimumNumber, ExecFloat.Binary.ofModel_toModel]
  · have hsel : Model.chooseNaN2 (ExecFloat.Binary.toModel x) (ExecFloat.Binary.toModel y) = none :=
      (Model.chooseNaN2_eq_none_iff _ _).2 ⟨hx, hy⟩
    simp only [Model.minimum, Model.Internal.Value.minimum, Model.withNaNSelection, hsel,
      ↓reduceDIte]
    rw [compareNonNaN_eq hx hy]
    simp only [isZero_toModel, signBit_toModel, UInt64.lt_iff_toNat_lt]
    rcases lt_trichotomy (rankBits (toBits x)).toNat (rankBits (toBits y)).toNat with h | h | h
    · simp [compare_lt_iff_lt.2 h, h]
    · rw [compare_eq_iff_eq.2 h]
      simp only [h, Nat.lt_irrefl, ↓reduceIte]
      by_cases hz : (toBits x &&& 0x7fffffffffffffff) = 0 ∧ (toBits y &&& 0x7fffffffffffffff) = 0
      · simp only [hz, beq_self_eq_true, Bool.and_self, ↓reduceIte]
        by_cases hs : (0x8000000000000000 : UInt64) ≤ toBits x
        · simp only [hs, decide_true, Bool.true_or, ↓reduceIte]
          rw [← decide_eq_true hs, ← toModel_eq_zero x hz.1, ExecFloat.Binary.ofModel_toModel]
        · simp only [hs, decide_false, Bool.false_or, ↓reduceIte]
          rw [← toModel_eq_zero y hz.2, ExecFloat.Binary.ofModel_toModel]
      · have : ((toBits x &&& 0x7fffffffffffffff == 0) &&
            (toBits y &&& 0x7fffffffffffffff == 0)) = false := by
          simpa using hz
        simp [this]
    · simp [compare_gt_iff_gt.2 h, h, Nat.not_lt.2 h.le]

/-- `fmax` on the bit patterns (`fmax_eq_fmaxImpl`); two NaNs go to FloatLib's `maximumNumber`. -/
@[inline] def fmaxImpl (x y : Binary64) : Binary64 :=
  let a := toBits x; let b := toBits y
  if isNaNBits a then (if isNaNBits b then ExecFloat.Binary.maximumNumber x y else y)
  else if isNaNBits b then x
  else
    let ra := rankBits a; let rb := rankBits b
    if ra < rb then y else if rb < ra then x
    else if (a &&& 0x7fffffffffffffff) == 0 && (b &&& 0x7fffffffffffffff) == 0 then
      (if 0x8000000000000000 ≤ a then y else x)
    else x

@[csimp] theorem fmax_eq_fmaxImpl : @fmax = @fmaxImpl := by
  funext x y
  have hx' := isNaNBits_toBits x
  have hy' := isNaNBits_toBits y
  have hspec : ExecFloat.Binary.maximumNumber x y = ExecFloat.Binary.ofModel
      (Model.Internal.Value.maximumNumber (ExecFloat.Binary.toModel x)
        (ExecFloat.Binary.toModel y)) := rfl
  rw [fmax, fmaxImpl, hspec]
  cases hx : Model.isNaN (ExecFloat.Binary.toModel x) <;>
    cases hy : Model.isNaN (ExecFloat.Binary.toModel y) <;>
    simp only [hx', hy', hx, hy, Bool.false_eq_true, ↓reduceIte,
      Model.Internal.Value.maximumNumber, ExecFloat.Binary.ofModel_toModel]
  · have hsel : Model.chooseNaN2 (ExecFloat.Binary.toModel x) (ExecFloat.Binary.toModel y) = none :=
      (Model.chooseNaN2_eq_none_iff _ _).2 ⟨hx, hy⟩
    simp only [Model.maximum, Model.Internal.Value.maximum, Model.withNaNSelection, hsel,
      ↓reduceDIte]
    rw [compareNonNaN_eq hx hy]
    simp only [isZero_toModel, signBit_toModel, UInt64.lt_iff_toNat_lt]
    rcases lt_trichotomy (rankBits (toBits x)).toNat (rankBits (toBits y)).toNat with h | h | h
    · simp [compare_lt_iff_lt.2 h, h]
    · rw [compare_eq_iff_eq.2 h]
      simp only [h, Nat.lt_irrefl, ↓reduceIte]
      by_cases hz : (toBits x &&& 0x7fffffffffffffff) = 0 ∧ (toBits y &&& 0x7fffffffffffffff) = 0
      · simp only [hz, beq_self_eq_true, Bool.and_self, ↓reduceIte]
        by_cases hs : (0x8000000000000000 : UInt64) ≤ toBits x
        · simp only [hs, decide_true, Bool.true_and, ↓reduceIte]
          rw [← toModel_eq_zero y hz.2, ExecFloat.Binary.ofModel_toModel]
        · simp only [hs, decide_false, Bool.false_and, ↓reduceIte]
          rw [← decide_eq_false hs, ← toModel_eq_zero x hz.1, ExecFloat.Binary.ofModel_toModel]
      · have : ((toBits x &&& 0x7fffffffffffffff == 0) &&
            (toBits y &&& 0x7fffffffffffffff == 0)) = false := by
          simpa using hz
        simp [this]
    · simp [compare_gt_iff_gt.2 h, h, Nat.not_lt.2 h.le]

end Binary64

/-! The instances the emitted code's `<`, `≤` (and `>`, `≥`, their flips) and `==` (and `!=`)
select. Each is FloatLib's: the propositions `x < y`, `x ≤ y` are FloatLib's
(`compareLess x y = true`, `compareLessEqual x y = true`), and `blt`, `ble`, `beq` are
definitionally `compareLess`, `compareLessEqual`, `compareEqual`; only the compiled code differs,
through the `@[csimp]` theorems above. Priority `high` puts them before FloatLib's (`execFloatBEq`
has priority 2000). -/

instance (priority := high) Binary32.decLt (x y : Binary32) : Decidable (x < y) :=
  inferInstanceAs (Decidable (Binary32.blt x y = true))
instance (priority := high) Binary32.decLe (x y : Binary32) : Decidable (x ≤ y) :=
  inferInstanceAs (Decidable (Binary32.ble x y = true))
instance (priority := high) Binary32.instBEq : BEq Binary32 := ⟨Binary32.beq⟩
instance (priority := high) Binary64.decLt (x y : Binary64) : Decidable (x < y) :=
  inferInstanceAs (Decidable (Binary64.blt x y = true))
instance (priority := high) Binary64.decLe (x y : Binary64) : Decidable (x ≤ y) :=
  inferInstanceAs (Decidable (Binary64.ble x y = true))
instance (priority := high) Binary64.instBEq : BEq Binary64 := ⟨Binary64.beq⟩

/-! ## Widening on the bit patterns

C's `(double)x` of a normal `float` is exact and moves the fields: the sign to bit 63, the exponent
rebiased, the fraction shifted. `toBinary64Impl` does that, keeps the sign of a zero, and leaves
subnormals, infinities and NaNs to FloatLib's cast; `toBinary64_eq_toBinary64Impl` proves it equal
to `toBinary64`. -/

namespace Binary32

/-- Whether the bit pattern is a normal number (exponent field neither zero nor all ones). -/
@[inline] def isNormalBits (b : UInt32) : Bool :=
  let m := b &&& 0x7fffffff
  0x00800000 ≤ m && m < 0x7f800000

/-- The binary64 bit pattern of a normal binary32 pattern: the sign moved to bit 63, the exponent
rebiased by `1023 - 127 = 896` and the fraction shifted up by `52 - 23 = 29` bits. -/
@[inline] def widenBits (b : UInt32) : UInt64 :=
  ((b >>> 31).toUInt64 <<< 63) + ((b &&& 0x7fffffff).toUInt64 <<< 29) + 0x3800000000000000

/-- `toBinary64` itself, out of line: the path `toBinary64Impl` takes for subnormals, infinities
and NaNs. -/
@[noinline] def toBinary64Slow (x : Binary32) : Binary64 :=
  ExecFloat.Binary.ofModel (Model.cast .binary32 .binary64 (ExecFloat.Binary.toModel x))

/-- `toBinary64` on the bit patterns for normal numbers and zeros
(`toBinary64_eq_toBinary64Impl`). -/
@[inline] def toBinary64Impl (x : Binary32) : Binary64 :=
  let b := toBits x
  if isNormalBits b then Binary64.ofBits (widenBits b)
  else if (b &&& 0x7fffffff) == 0 then Binary64.ofBits ((b >>> 31).toUInt64 <<< 63)
  else toBinary64Slow x

/-- FloatLib's cast of a normal binary32 word `n` to binary64 is the word `widenBits` computes.
The cast rounds the exact dyadic value of `n` into binary64 (`Model.roundDyadic`); the value is
representable there (`Model.roundDyadic_of_representable`), so the result has the same real value
as the word built from the fields, and a nonzero real value determines the word
(`Model.eq_of_toReal_eq_of_nonzero`). -/
theorem cast_normal_model (m : Model FloatFormat.binary32) (n : Nat) (hb : m.bits.toNat = n)
    (hn : n < 2 ^ 32) (hrange : 2 ^ 23 ≤ n % 2 ^ 31 ∧ n % 2 ^ 31 < 0x7f800000) :
    Model.cast .binary32 .binary64 m =
      (Model.ofBits (BitVec.ofNat 64 (n / 2 ^ 31 * 2 ^ 63 + n % 2 ^ 31 * 2 ^ 29 + 896 * 2 ^ 52)) :
        Model .binary64) := by
  have hs : Model.signBit m = decide (2 ^ 31 ≤ n) := by
    rw [Model.signBit_eq_msb, BitVec.msb_eq_decide, hb]; rfl
  have he : Model.expField m = n / 2 ^ 23 % 2 ^ 8 := by
    rw [CFloat.Compare.expField_eq, hb]; rfl
  have hf : Model.fracField m = n % 2 ^ 23 := by
    rw [CFloat.Compare.fracField_eq, hb]; rfl
  have hnan : Model.isNaN m = false := by
    show Model.IEEE.isNaN _ = false
    simp only [Model.IEEE.isNaN, he, hf]
    rw [Bool.eq_false_iff]
    simp only [ne_eq, Bool.and_eq_true, beq_iff_eq, bne_iff_ne]
    show ¬(_ = 2 ^ 8 - 1 ∧ _)
    omega
  have hinf : Model.isInf m = false := by
    show Model.IEEE.isInf _ = false
    simp only [Model.IEEE.isInf, he, hf]
    rw [Bool.eq_false_iff]
    simp only [ne_eq, Bool.and_eq_true, beq_iff_eq]
    show ¬(_ = 2 ^ 8 - 1 ∧ _)
    omega
  have hfin := Model.isFinite_eq_true_of_isNaN_eq_false_of_isInf_eq_false _ hnan hinf
  have hcast : Model.cast .binary32 .binary64 m =
      Model.roundDyadic .binary64 (Model.finiteDyadic m hfin) := by
    have hexp : FloatFormat.binary32.expWidth ≠ FloatFormat.binary64.expWidth := by decide
    have hne : FloatFormat.binary32 ≠ FloatFormat.binary64 := fun h => hexp (h ▸ rfl)
    unfold Model.cast Model.Internal.Directed.cast Model.Internal.Nearest.cast
    simp only [hnan, hinf, hne, hexp, Bool.false_eq_true, ↓reduceDIte]
  rw [hcast]
  -- the exact value of the source
  have he0 : n / 2 ^ 23 % 2 ^ 8 ≠ 0 := by omega
  have he1 : n / 2 ^ 23 % 2 ^ 8 < FloatFormat.expAllOnesNat .binary32 := by
    show _ < 2 ^ 8 - 1; omega
  have hd : Model.toDyadic? m = some ⟨decide (2 ^ 31 ≤ n), Model.pow2 23 + n % 2 ^ 23,
      Int.ofNat (n / 2 ^ 23 % 2 ^ 8) - 127 - 23⟩ := by
    have h := Model.toDyadic?_ofFields_normal .binary32 (decide (2 ^ 31 ≤ n)) (n / 2 ^ 23 % 2 ^ 8)
      (n % 2 ^ 23) he0 he1 (by show n % 2 ^ 23 < 2 ^ 23; omega)
    have hm : Model.ofFields .binary32 (decide (2 ^ 31 ≤ n)) (n / 2 ^ 23 % 2 ^ 8) (n % 2 ^ 23) =
        m := by
      rw [← hs, ← he, ← hf]; exact Model.ofFields_signBit_expField_fracField m
    rw [hm] at h
    exact h
  rw [Model.finiteDyadic_eq_of_toDyadic hfin hd]
  -- the target as fields
  have htarget : (Model.ofBits (BitVec.ofNat 64
      (n / 2 ^ 31 * 2 ^ 63 + n % 2 ^ 31 * 2 ^ 29 + 896 * 2 ^ 52)) : Model .binary64) =
      Model.ofFields .binary64 (decide (2 ^ 31 ≤ n)) (n / 2 ^ 23 % 2 ^ 8 + 896)
        (n % 2 ^ 23 * 2 ^ 29) := by
    generalize hr : (Model.ofBits (BitVec.ofNat 64
      (n / 2 ^ 31 * 2 ^ 63 + n % 2 ^ 31 * 2 ^ 29 + 896 * 2 ^ 52)) : Model .binary64) = r
    have hrb : r.bits.toNat = n / 2 ^ 31 * 2 ^ 63 + n % 2 ^ 31 * 2 ^ 29 + 896 * 2 ^ 52 := by
      rw [← hr]; show (BitVec.ofNat 64 _).toNat = _; rw [BitVec.toNat_ofNat]; omega
    rw [← Model.ofFields_signBit_expField_fracField r]
    congr 1
    · rw [Model.signBit_eq_msb, BitVec.msb_eq_decide, hrb]
      show decide (2 ^ 63 ≤ _) = _
      exact decide_eq_decide.2 (by omega)
    · rw [CFloat.Compare.expField_eq, hrb]; show _ / 2 ^ 52 % 2 ^ 11 = _; omega
    · rw [CFloat.Compare.fracField_eq, hrb]; show _ % 2 ^ 52 = _; omega
  rw [htarget]
  have hE : 1 ≤ n / 2 ^ 23 % 2 ^ 8 ∧ n / 2 ^ 23 % 2 ^ 8 ≤ 254 := by omega
  have hF : n % 2 ^ 23 < 2 ^ 23 := Nat.mod_lt _ (by norm_num)
  generalize decide (2 ^ 31 ≤ n) = s
  generalize n / 2 ^ 23 % 2 ^ 8 = e at hE ⊢
  generalize n % 2 ^ 23 = f at hF ⊢
  have hsig : Model.pow2 23 + f < 2 ^ 24 := by rw [Model.pow2_eq_two_pow]; omega
  have hdreal : (⟨s, Model.pow2 23 + f, Int.ofNat e - 127 - 23⟩ : FloatLib.Numerics.Dyadic).toReal =
      (if s then (-1 : ℝ) else 1) * ((Model.pow2 23 + f : Nat) : ℝ) *
        (2 : ℝ) ^ ((e : ℤ) - 150) := by
    rw [Model.Dyadic.toReal_mk, Int.ofNat_eq_natCast,
      show (e : ℤ) - 127 - 23 = (e : ℤ) - 150 by omega]
    simp [FloatLib.Floats.Formats.Flocq.bpow, FloatLib.Numerics.binaryRadix,
      FloatLib.Numerics.Radix.toReal]
  have hpos : (0 : ℝ) < ((Model.pow2 23 + f : Nat) : ℝ) * (2 : ℝ) ^ ((e : ℤ) - 150) := by
    apply mul_pos
    · rw [Model.pow2_eq_two_pow]; positivity
    · positivity
  have habs : |(⟨s, Model.pow2 23 + f, Int.ofNat e - 127 - 23⟩ : FloatLib.Numerics.Dyadic).toReal| =
      ((Model.pow2 23 + f : Nat) : ℝ) * (2 : ℝ) ^ ((e : ℤ) - 150) := by
    rw [hdreal, mul_assoc, abs_mul, abs_of_pos hpos]; cases s <;> simp
  have hbound : ((Model.pow2 23 + f : Nat) : ℝ) * (2 : ℝ) ^ ((e : ℤ) - 150) ≤
      Model.toReal (Model.posMaxFinite .binary64) := by
    rw [Model.toReal_posMaxFinite_of_eq .binary64 (significand := 2 ^ 53 - 1) (exponent := 971)
      (by decide) (by decide)]
    have h1 : ((Model.pow2 23 + f : Nat) : ℝ) ≤ 2 ^ 24 := by
      rw [Model.pow2_eq_two_pow]; push_cast
      have : (f : ℝ) ≤ 2 ^ 23 := by exact_mod_cast hF.le
      linarith
    have h2 : (2 : ℝ) ^ ((e : ℤ) - 150) ≤ 2 ^ (104 : ℤ) :=
      zpow_le_zpow_right₀ (by norm_num) (by omega)
    calc ((Model.pow2 23 + f : Nat) : ℝ) * (2 : ℝ) ^ ((e : ℤ) - 150)
        ≤ 2 ^ 24 * 2 ^ (104 : ℤ) := mul_le_mul h1 h2 (by positivity) (by positivity)
      _ = 2 ^ (128 : ℤ) := by
        rw [← zpow_natCast, ← zpow_add₀ two_ne_zero]; norm_num
      _ ≤ 1 * 2 ^ (971 : ℤ) := by
        rw [one_mul]; exact zpow_le_zpow_right₀ (by norm_num) (by norm_num)
      _ ≤ ((2 ^ 53 - 1 : Nat) : ℝ) * (2 : ℝ) ^ (971 : ℤ) :=
        mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
  have hrep := Model.roundDyadic_of_representable .binary64 (by decide)
    ⟨s, Model.pow2 23 + f, Int.ofNat e - 127 - 23⟩ (Model.pow2 23 + f) 0 (by simp)
    (by show _ < 2 ^ 53; omega)
    (by show (-1074 : ℤ) ≤ Int.ofNat e - 127 - 23; rw [Int.ofNat_eq_natCast]; omega)
    (by rw [habs]; exact hbound)
  have hR := Model.toReal_ofFields_normal .binary64 s (e + 896) (f * 2 ^ 29) (by omega)
    (by show _ < 2 ^ 11 - 1; omega) (by show _ < 2 ^ 52; omega)
  apply Model.eq_of_toReal_eq_of_nonzero
  · rw [hrep.2, hR, hdreal]
    have hn1 : Model.pow2 FloatFormat.binary64.fracWidth + f * 2 ^ 29 =
        (Model.pow2 23 + f) * 2 ^ 29 := by
      rw [Model.pow2_eq_two_pow, Model.pow2_eq_two_pow]; show 2 ^ 52 + _ = _; ring
    have hb1 : FloatLib.Floats.Formats.Flocq.bpow FloatLib.Numerics.binaryRadix
        (Int.ofNat (e + 896) - Int.ofNat FloatFormat.binary64.exponentBias -
          Int.ofNat FloatFormat.binary64.fracWidth) = (2 : ℝ) ^ ((e : ℤ) - 150) / 2 ^ 29 := by
      rw [show Int.ofNat (e + 896) - Int.ofNat FloatFormat.binary64.exponentBias -
          Int.ofNat FloatFormat.binary64.fracWidth = ((e : ℤ) - 150) - ((29 : ℕ) : ℤ) by
        show Int.ofNat (e + 896) - 1023 - 52 = _; rw [Int.ofNat_eq_natCast]; push_cast; ring]
      have h2 : FloatLib.Numerics.binaryRadix.toReal = 2 := by
        simp [FloatLib.Numerics.binaryRadix, FloatLib.Numerics.Radix.toReal]
      rw [FloatLib.Floats.Formats.Flocq.bpow, h2, zpow_sub₀ two_ne_zero, zpow_natCast]
    rw [hn1, hb1]
    push_cast
    field_simp
    norm_num
  · rw [hrep.2, hdreal, mul_assoc]
    exact mul_ne_zero (by cases s <;> norm_num) hpos.ne'

/-- The binary64 model of a `UInt64`, two spellings. -/
theorem ofBits_ofNat_toNat (w : UInt64) :
    (Model.ofBits (BitVec.ofNat 64 w.toNat) : Model .binary64) =
      (Model.ofBits (BitVec.ofNatLT w.toNat (UInt64.toNat_lt w)) : Model .binary64) := by
  apply congrArg Model.ofBits
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat]
  exact Nat.mod_eq_of_lt (UInt64.toNat_lt w)

/-- On a normal number `toBinary64` is `widenBits` on the bit pattern. -/
theorem toBinary64_normal (x : Binary32) (hnorm : isNormalBits (toBits x) = true) :
    toBinary64 x = Binary64.ofBits (widenBits (toBits x)) := by
  have hn := UInt32.toNat_lt (toBits x)
  have hand : (toBits x &&& 0x7fffffff).toNat = (toBits x).toNat % 2 ^ 31 := by
    rw [UInt32.toNat_and]; exact Nat.and_two_pow_sub_one_eq_mod _ 31
  have hrange : 2 ^ 23 ≤ (toBits x).toNat % 2 ^ 31 ∧ (toBits x).toNat % 2 ^ 31 < 0x7f800000 := by
    simpa [isNormalBits, UInt32.le_iff_toNat_le, UInt32.lt_iff_toNat_lt, hand] using hnorm
  have hw : (widenBits (toBits x)).toNat =
      (toBits x).toNat / 2 ^ 31 * 2 ^ 63 + (toBits x).toNat % 2 ^ 31 * 2 ^ 29 + 896 * 2 ^ 52 := by
    simp only [widenBits, UInt64.toNat_add, UInt64.toNat_shiftLeft, UInt32.toNat_toUInt64,
      UInt32.toNat_shiftRight, hand, UInt64.reduceToNat, Nat.shiftLeft_eq,
      Nat.shiftRight_eq_div_pow, UInt32.reduceToNat, Nat.reduceMod]
    omega
  have hc := cast_normal_model (ExecFloat.Binary.toModel x) (toBits x).toNat rfl hn hrange
  rw [← hw, ofBits_ofNat_toNat] at hc
  rw [toBinary64, hc,
    ← ExecFloat.Binary.ofModel_toModel (Binary64.ofBits (widenBits (toBits x)))]
  rfl

/-- On a zero `toBinary64` keeps the sign: there are two words, and the kernel evaluates FloatLib's
cast on each (`decide`). -/
theorem toBinary64_zero (x : Binary32) (hz : (toBits x &&& 0x7fffffff) = 0) :
    toBinary64 x = Binary64.ofBits ((toBits x >>> 31).toUInt64 <<< 63) := by
  have hand : (toBits x &&& 0x7fffffff).toNat = (toBits x).toNat % 2 ^ 31 := by
    rw [UInt32.toNat_and]; exact Nat.and_two_pow_sub_one_eq_mod _ 31
  have hn := UInt32.toNat_lt (toBits x)
  rw [hz] at hand
  have h : toBits x = 0 ∨ toBits x = 0x80000000 := by
    simp only [← UInt32.toNat_inj, UInt32.reduceToNat] at hand ⊢; omega
  rw [← ExecFloat.Binary.ofBits32_toBits32 x]
  rcases h with h | h <;> rw [show ExecFloat.Binary.toBits32 x = toBits x from rfl, h] <;> decide

@[csimp] theorem toBinary64_eq_toBinary64Impl : @toBinary64 = @toBinary64Impl := by
  funext x
  rw [toBinary64Impl]
  by_cases hnorm : isNormalBits (toBits x) = true
  · rw [toBinary64_normal x hnorm]; simp only [hnorm, ↓reduceIte]
  · by_cases hz : (toBits x &&& 0x7fffffff) = 0
    · rw [toBinary64_zero x hz]
      simp only [hnorm, hz, Bool.false_eq_true, ↓reduceIte, beq_self_eq_true]
    · have hz' : ((toBits x &&& 0x7fffffff) == 0) = false := by simpa using hz
      simp only [hnorm, hz', Bool.false_eq_true, ↓reduceIte]; rfl

end Binary32

/-! ## Conversions between floats and integers on the bit patterns (Phase 3)

`truncSat32`/`truncSat64` (C's conversion of a float to an integer type), `ofInt32`/`ofInt64`
(an integer to a float) and `Binary64.toBinary32` (C's `(float)d`) are FloatLib's `toInt?` (an exact
dyadic decoded from the word, truncated), `ofRat` (rational rounding) and `Model.cast` (dyadic
rounding): 100 ns to over 1 µs each. The functions below compute
them on the bit patterns, and the `@[csimp]` theorems prove each equal to its FloatLib definition.

To an integer: `toIntBits` reads the fields of the word and shifts the significand (with its
implicit leading one) by the unbiased exponent; a zero or subnormal truncates to 0, an all-ones
exponent field (NaN, infinity) gives `none`. `toInt?_eq_toIntBits` shows it is FloatLib's
`toInt?` for every word: `toDyadic?` decodes the same fields (`Model.ieeeToDyadic?`) and
`Model.roundDyadicToInt .towardZero` is that shift.

From an integer: FloatLib's `ofRat` of a nonzero integer `n` rounds the real `n` once, and so does
its dyadic rounding of `⟨n < 0, |n|, 0⟩` (`Model.toReal_roundRatScaled_eq_roundAt`,
`Model.toReal_roundDyadic_eq_roundAt`); both results are finite and nonzero, so they are the same
word (`ofRat_int_eq_roundDyadicGeneral`, by `Model.eq_of_toReal_eq_of_nonzero`). FloatLib's integer
algorithm for the dyadic rounding (`Model.roundDyadicGeneral`, `roundDyadicGeneral_eq_roundDyadic`)
keeps, for `k = ⌊log₂ |n|⌋`, the significand `|n|` shifted up to 24 (53) bits when `k < 23` (`52`)
and `roundShiftRightEven |n| (k - 23)` (`k - 52`) otherwise, and carries a round-up to `2^24`
(`2^53`) into the exponent (`roundDyadicGeneral_int`). `ofMagWord` computes that word from the sign
and the magnitude as a `UInt64` (`ofMagWord_toNat`): `k` by a binary search on the word
(`log2w`), the nearest-even shift as quotient, remainder and half (`roundShiftRightEvenW`), the
biased exponent `127 + k` (`1023 + k`) added to the significand without its leading one, so the
carry runs into the exponent field. Zero is `+0`. Every integer below `2^64` in magnitude is
converted on the words (`ofMag32`, `ofMag64`); larger `Int`s go through `ofRat` (`ofInt32Slow`,
`ofInt64Slow`). The wrappers `Int8.toBinary32` .. `USize.toBinary64` (end of the file) take the
magnitude from the integer word itself, without `Int`.

Double to float (`Binary64.toBinary32`, FloatLib's `Model.cast`): when the result is a normal float
(the double's biased exponent in `[897, 1149]`) `toBinary32Word` rebiases the exponent by 896 and
rounds the 53-bit significand to 24 bits, to nearest even, on the bits (a round-up that carries
into the exponent field stays a normal float below `2^128`); `cast_binary32_model` computes FloatLib's
cast there through `Model.roundDyadicGeneral` (`Model.roundDyadicGeneral_eq_roundDyadic`), and
`toBinary32Word_toNat` matches the word. Zeros keep their sign; subnormal and overflowing results,
infinities and NaNs go through FloatLib's cast (`toBinary32Slow`). -/

open FloatLib.Floats
open FloatLib.Floats.Formats.BinaryInterchange (Model FloatFormat)

namespace CFloat.Conv

/-- FloatLib's truncation of an exact dyadic, by cases on the sign of the exponent. -/
theorem roundDyadicToInt_towardZero_eq (s : Bool) (sig : Nat) (k : Int) :
    Model.roundDyadicToInt .towardZero ⟨s, sig, k⟩ =
      if s then -((if 0 ≤ k then sig <<< k.toNat else sig >>> (-k).toNat : Nat) : Int)
      else ((if 0 ≤ k then sig <<< k.toNat else sig >>> (-k).toNat : Nat) : Int) := by
  unfold Model.roundDyadicToInt
  by_cases h0 : sig = 0
  · subst h0; cases k <;> cases s <;> simp
  · simp only [beq_iff_eq, h0, ↓reduceIte]
    cases k with
    | ofNat m => simp
    | negSucc m =>
      simp only [Int.negSucc_not_nonneg, ↓reduceIte]
      have : (-(Int.negSucc m)).toNat = m + 1 := by simp [Int.neg_negSucc]
      rw [this]; rfl

end CFloat.Conv

namespace Binary32

/-- C's truncation toward zero of the value with bit pattern `b` (`none` for a NaN or an
infinity): the significand shifted by the unbiased exponent. -/
@[inline] def toIntBits (b : UInt32) : Option Int :=
  let e := (b >>> 23) &&& 0xff
  if e == 0xff then none
  else
    let mag : Nat :=
      if e == 0 then 0
      else
        let sig := ((b &&& 0x7fffff) ||| 0x800000).toNat
        if 150 ≤ e then sig <<< (e - 150).toNat else sig >>> (150 - e).toNat
    some (if b >>> 31 == 0 then (mag : Int) else -(mag : Int))

theorem toIntBits_eq_nat (b : UInt32) : toIntBits b =
    let n := b.toNat
    let E := n / 2 ^ 23 % 2 ^ 8
    if E = 255 then none
    else
      let mag : Nat := if E = 0 then 0
        else if 150 ≤ E then (2 ^ 23 + n % 2 ^ 23) <<< (E - 150) else (2 ^ 23 + n % 2 ^ 23) >>> (150 - E)
      some (if n < 2 ^ 31 then (mag : Int) else -(mag : Int)) := by
  have hn := UInt32.toNat_lt b
  have he : ((b >>> 23) &&& 0xff).toNat = b.toNat / 2 ^ 23 % 2 ^ 8 := by
    rw [UInt32.toNat_and, UInt32.toNat_shiftRight]
    simp only [UInt32.reduceToNat, Nat.reduceMod, Nat.shiftRight_eq_div_pow]
    exact Nat.and_two_pow_sub_one_eq_mod _ 8
  have hsig : ((b &&& 0x7fffff) ||| 0x800000).toNat = 2 ^ 23 + b.toNat % 2 ^ 23 := by
    rw [UInt32.toNat_or, UInt32.toNat_and]
    simp only [UInt32.reduceToNat]
    rw [show (8388607 : Nat) = 2 ^ 23 - 1 by norm_num, Nat.and_two_pow_sub_one_eq_mod]
    rw [show (8388608 : Nat) = 2 ^ 23 by norm_num, Nat.or_two_pow_eq_add_of_lt (Nat.mod_lt _ (by norm_num))]
    omega
  have hs : (b >>> 31).toNat = b.toNat / 2 ^ 31 := by
    rw [UInt32.toNat_shiftRight]; simp [Nat.shiftRight_eq_div_pow]
  simp only [toIntBits]
  generalize hE : (b >>> 23) &&& 0xff = e
  rw [hE] at he
  have hE' : e.toNat < 2 ^ 8 := by rw [he]; exact Nat.mod_lt _ (by norm_num)
  have h0 : (e == 0) = decide (b.toNat / 2 ^ 23 % 2 ^ 8 = 0) := by
    rw [Bool.eq_iff_iff]; simp [← UInt32.toNat_inj, he]
  have h255 : (e == 0xff) = decide (b.toNat / 2 ^ 23 % 2 ^ 8 = 255) := by
    rw [Bool.eq_iff_iff]; simp [← UInt32.toNat_inj, he]
  have hle : (150 ≤ e) = (150 ≤ b.toNat / 2 ^ 23 % 2 ^ 8) := by
    simp [UInt32.le_iff_toNat_le, he]
  have hsub1 : 150 ≤ e → (e - 150).toNat = b.toNat / 2 ^ 23 % 2 ^ 8 - 150 := by
    intro h; rw [UInt32.toNat_sub_of_le _ _ h, he]; rfl
  have hsub2 : ¬ 150 ≤ e → (150 - e).toNat = 150 - b.toNat / 2 ^ 23 % 2 ^ 8 := by
    intro h; rw [UInt32.toNat_sub_of_le _ _ (by simp [UInt32.le_iff_toNat_le] at h ⊢; omega), he]; rfl
  have hsign : (b >>> 31 == 0) = decide (b.toNat < 2 ^ 31) := by
    rw [Bool.eq_iff_iff]
    simp only [beq_iff_eq, ← UInt32.toNat_inj, hs, decide_eq_true_eq, UInt32.reduceToNat]; omega
  simp only [h0, h255, hsign, hsig]
  by_cases hc : 150 ≤ e
  · simp only [hc, hsub1 hc, ↓reduceIte, decide_eq_true_eq, (by rw [← hle]; exact hc : 150 ≤ b.toNat / 2 ^ 23 % 2 ^ 8)]
  · simp only [hc, hsub2 hc, ↓reduceIte, decide_eq_true_eq, (by rw [← hle]; exact hc : ¬ 150 ≤ b.toNat / 2 ^ 23 % 2 ^ 8)]


theorem toInt?_eq_toIntBits (x : Binary32) : ExecFloat.Binary.toInt? x = toIntBits (toBits x) := by
  have hb : (ExecFloat.Binary.toModel x).bits.toNat = (toBits x).toNat := rfl
  have hn := UInt32.toNat_lt (toBits x)
  rw [toIntBits_eq_nat]
  show (Model.toDyadic? (ExecFloat.Binary.toModel x)).map (Model.roundDyadicToInt .towardZero) = _
  have hsgn : Model.signBit (ExecFloat.Binary.toModel x) = !decide ((toBits x).toNat < 2147483648) := by
    rw [signBit_toModel]
    by_cases h : (toBits x).toNat < 2147483648
    · simp [h, UInt32.le_iff_toNat_le, show ¬ 2147483648 ≤ (toBits x).toNat by omega]
    · simp [h, UInt32.le_iff_toNat_le, show 2147483648 ≤ (toBits x).toNat by omega]
  simp only [Model.toDyadic?, Model.ieeeToDyadic?, Model.IEEE.isNaN,
    Model.IEEE.isInf, CFloat.Compare.expField_eq, CFloat.Compare.fracField_eq, hsgn, hb]
  generalize (toBits x).toNat = n at *
  have hI : FloatFormat.Encoding.ieee.defaultBias 8 = 127 := rfl
  simp only [FloatFormat.isIEEE, FloatFormat.expAllOnesNat,
    FloatFormat.ieeeNormalMantissaExpOffset, FloatFormat.ieeeMinSubnormalExponent, FloatFormat.bias,
    hI, Model.pow2_eq_two_pow, beq_self_eq_true, Bool.true_and, ↓reduceIte, Nat.reducePow, Nat.reduceSub,
    Nat.reduceAdd]
  have hF : n % 8388608 < 8388608 := Nat.mod_lt _ (by norm_num)
  have hE : n / 8388608 % 256 < 256 := Nat.mod_lt _ (by norm_num)
  generalize n / 8388608 % 256 = E at *
  generalize n % 8388608 = F at *
  have hsg : ∀ (a : Int), (if (!decide (n < 2147483648)) = true then -a else a) =
      (if n < 2147483648 then a else -a) := by
    intro a; by_cases hsn : n < 2147483648 <;> simp [hsn]
  by_cases h255 : E = 255
  · subst h255; simp
  by_cases h0 : E = 0
  · subst h0
    by_cases hF0 : F = 0
    · subst hF0; simp [CFloat.Conv.roundDyadicToInt_towardZero_eq]
    · have hsh : F >>> 149 = 0 := by
        rw [Nat.shiftRight_eq_div_pow]; exact Nat.div_eq_of_lt (by omega)
      simp [hF0, CFloat.Conv.roundDyadicToInt_towardZero_eq, hsh]
  · have h255' : (E == 255) = false := by simpa using h255
    have h0' : (E == 0) = false := by simpa using h0
    simp only [h255', h0', Bool.false_and, Bool.or_false, Bool.false_eq_true, ↓reduceIte, h255, h0,
      Option.map_some, CFloat.Conv.roundDyadicToInt_towardZero_eq, Int.ofNat_eq_natCast,
      Option.some.injEq]
    rw [hsg]
    by_cases hc : 150 ≤ E
    · have hk : (0 : Int) ≤ (E : Int) - ((150 : Nat) : Int) := by omega
      have hk' : ((E : Int) - ((150 : Nat) : Int)).toNat = E - 150 := by omega
      simp only [hc, hk, hk', ↓reduceIte]
    · have hk : ¬ (0 : Int) ≤ (E : Int) - ((150 : Nat) : Int) := by omega
      have hk' : (-((E : Int) - ((150 : Nat) : Int))).toNat = 150 - E := by omega
      simp only [hc, hk, hk', ↓reduceIte]

end Binary32

namespace Binary64

/-- C's truncation toward zero of the value with bit pattern `b` (`none` for a NaN or an
infinity): the significand shifted by the unbiased exponent. -/
@[inline] def toIntBits (b : UInt64) : Option Int :=
  let e := (b >>> 52) &&& 0x7ff
  if e == 0x7ff then none
  else
    let mag : Nat :=
      if e == 0 then 0
      else
        let sig := ((b &&& 0xfffffffffffff) ||| 0x10000000000000).toNat
        if 1075 ≤ e then sig <<< (e - 1075).toNat else sig >>> (1075 - e).toNat
    some (if b >>> 63 == 0 then (mag : Int) else -(mag : Int))

theorem toIntBits_eq_nat (b : UInt64) : toIntBits b =
    let n := b.toNat
    let E := n / 2 ^ 52 % 2 ^ 11
    if E = 2047 then none
    else
      let mag : Nat := if E = 0 then 0
        else if 1075 ≤ E then (2 ^ 52 + n % 2 ^ 52) <<< (E - 1075) else (2 ^ 52 + n % 2 ^ 52) >>> (1075 - E)
      some (if n < 2 ^ 63 then (mag : Int) else -(mag : Int)) := by
  have hn := UInt64.toNat_lt b
  have he : ((b >>> 52) &&& 0x7ff).toNat = b.toNat / 2 ^ 52 % 2 ^ 11 := by
    rw [UInt64.toNat_and, UInt64.toNat_shiftRight]
    simp only [UInt64.reduceToNat, Nat.reduceMod, Nat.shiftRight_eq_div_pow]
    exact Nat.and_two_pow_sub_one_eq_mod _ 11
  have hsig : ((b &&& 0xfffffffffffff) ||| 0x10000000000000).toNat = 2 ^ 52 + b.toNat % 2 ^ 52 := by
    rw [UInt64.toNat_or, UInt64.toNat_and]
    simp only [UInt64.reduceToNat]
    rw [show (4503599627370495 : Nat) = 2 ^ 52 - 1 by norm_num, Nat.and_two_pow_sub_one_eq_mod]
    rw [show (4503599627370496 : Nat) = 2 ^ 52 by norm_num, Nat.or_two_pow_eq_add_of_lt (Nat.mod_lt _ (by norm_num))]
    omega
  have hs : (b >>> 63).toNat = b.toNat / 2 ^ 63 := by
    rw [UInt64.toNat_shiftRight]; simp [Nat.shiftRight_eq_div_pow]
  simp only [toIntBits]
  generalize hE : (b >>> 52) &&& 0x7ff = e
  rw [hE] at he
  have hE' : e.toNat < 2 ^ 11 := by rw [he]; exact Nat.mod_lt _ (by norm_num)
  have h0 : (e == 0) = decide (b.toNat / 2 ^ 52 % 2 ^ 11 = 0) := by
    rw [Bool.eq_iff_iff]; simp [← UInt64.toNat_inj, he]
  have h255 : (e == 0x7ff) = decide (b.toNat / 2 ^ 52 % 2 ^ 11 = 2047) := by
    rw [Bool.eq_iff_iff]; simp [← UInt64.toNat_inj, he]
  have hle : (1075 ≤ e) = (1075 ≤ b.toNat / 2 ^ 52 % 2 ^ 11) := by
    simp [UInt64.le_iff_toNat_le, he]
  have hsub1 : 1075 ≤ e → (e - 1075).toNat = b.toNat / 2 ^ 52 % 2 ^ 11 - 1075 := by
    intro h; rw [UInt64.toNat_sub_of_le _ _ h, he]; rfl
  have hsub2 : ¬ 1075 ≤ e → (1075 - e).toNat = 1075 - b.toNat / 2 ^ 52 % 2 ^ 11 := by
    intro h; rw [UInt64.toNat_sub_of_le _ _ (by simp [UInt64.le_iff_toNat_le] at h ⊢; omega), he]; rfl
  have hsign : (b >>> 63 == 0) = decide (b.toNat < 2 ^ 63) := by
    rw [Bool.eq_iff_iff]
    simp only [beq_iff_eq, ← UInt64.toNat_inj, hs, decide_eq_true_eq, UInt64.reduceToNat]; omega
  simp only [h0, h255, hsign, hsig]
  by_cases hc : 1075 ≤ e
  · simp only [hc, hsub1 hc, ↓reduceIte, decide_eq_true_eq, (by rw [← hle]; exact hc : 1075 ≤ b.toNat / 2 ^ 52 % 2 ^ 11)]
  · simp only [hc, hsub2 hc, ↓reduceIte, decide_eq_true_eq, (by rw [← hle]; exact hc : ¬ 1075 ≤ b.toNat / 2 ^ 52 % 2 ^ 11)]


theorem toInt?_eq_toIntBits (x : Binary64) : ExecFloat.Binary.toInt? x = toIntBits (toBits x) := by
  have hb : (ExecFloat.Binary.toModel x).bits.toNat = (toBits x).toNat := rfl
  have hn := UInt64.toNat_lt (toBits x)
  rw [toIntBits_eq_nat]
  show (Model.toDyadic? (ExecFloat.Binary.toModel x)).map (Model.roundDyadicToInt .towardZero) = _
  have hsgn : Model.signBit (ExecFloat.Binary.toModel x) = !decide ((toBits x).toNat < 9223372036854775808) := by
    rw [signBit_toModel]
    by_cases h : (toBits x).toNat < 9223372036854775808
    · simp [h, UInt64.le_iff_toNat_le, show ¬ 9223372036854775808 ≤ (toBits x).toNat by omega]
    · simp [h, UInt64.le_iff_toNat_le, show 9223372036854775808 ≤ (toBits x).toNat by omega]
  simp only [Model.toDyadic?, Model.ieeeToDyadic?, Model.IEEE.isNaN,
    Model.IEEE.isInf, CFloat.Compare.expField_eq, CFloat.Compare.fracField_eq, hsgn, hb]
  generalize (toBits x).toNat = n at *
  have hI : FloatFormat.Encoding.ieee.defaultBias 11 = 1023 := rfl
  simp only [FloatFormat.isIEEE, FloatFormat.expAllOnesNat,
    FloatFormat.ieeeNormalMantissaExpOffset, FloatFormat.ieeeMinSubnormalExponent, FloatFormat.bias,
    hI, Model.pow2_eq_two_pow, beq_self_eq_true, Bool.true_and, ↓reduceIte, Nat.reducePow, Nat.reduceSub,
    Nat.reduceAdd]
  have hF : n % 4503599627370496 < 4503599627370496 := Nat.mod_lt _ (by norm_num)
  have hE : n / 4503599627370496 % 2048 < 2048 := Nat.mod_lt _ (by norm_num)
  generalize n / 4503599627370496 % 2048 = E at *
  generalize n % 4503599627370496 = F at *
  have hsg : ∀ (a : Int), (if (!decide (n < 9223372036854775808)) = true then -a else a) =
      (if n < 9223372036854775808 then a else -a) := by
    intro a; by_cases hsn : n < 9223372036854775808 <;> simp [hsn]
  by_cases h255 : E = 2047
  · subst h255; simp
  by_cases h0 : E = 0
  · subst h0
    by_cases hF0 : F = 0
    · subst hF0; simp [CFloat.Conv.roundDyadicToInt_towardZero_eq]
    · have hsh : F >>> 1074 = 0 := by
        rw [Nat.shiftRight_eq_div_pow]; exact Nat.div_eq_of_lt (by omega)
      simp [hF0, CFloat.Conv.roundDyadicToInt_towardZero_eq, hsh]
  · have h255' : (E == 2047) = false := by simpa using h255
    have h0' : (E == 0) = false := by simpa using h0
    simp only [h255', h0', Bool.false_and, Bool.or_false, Bool.false_eq_true, ↓reduceIte, h255, h0,
      Option.map_some, CFloat.Conv.roundDyadicToInt_towardZero_eq, Int.ofNat_eq_natCast,
      Option.some.injEq]
    rw [hsg]
    by_cases hc : 1075 ≤ E
    · have hk : (0 : Int) ≤ (E : Int) - ((1075 : Nat) : Int) := by omega
      have hk' : ((E : Int) - ((1075 : Nat) : Int)).toNat = E - 1075 := by omega
      simp only [hc, hk, hk', ↓reduceIte]
    · have hk : ¬ (0 : Int) ≤ (E : Int) - ((1075 : Nat) : Int) := by omega
      have hk' : (-((E : Int) - ((1075 : Nat) : Int))).toNat = 1075 - E := by omega
      simp only [hc, hk, hk', ↓reduceIte]

end Binary64

namespace CFloat

/-- `truncSat32` on the bit patterns (`truncSat32_eq_truncSat32Impl`). -/
@[inline] def truncSat32Impl (lo hi : Int) (x : Binary32) : Int :=
  let b := Binary32.toBits x
  match Binary32.toIntBits b with
  | some n => if n < lo then lo else if n > hi then hi else n
  | none => if Binary32.isNaNBits b then 0 else if 0x80000000 ≤ b then lo else hi

/-- `truncSat64` on the bit patterns (`truncSat64_eq_truncSat64Impl`). -/
@[inline] def truncSat64Impl (lo hi : Int) (x : Binary64) : Int :=
  let b := Binary64.toBits x
  match Binary64.toIntBits b with
  | some n => if n < lo then lo else if n > hi then hi else n
  | none => if Binary64.isNaNBits b then 0 else if 0x8000000000000000 ≤ b then lo else hi

@[csimp] theorem truncSat32_eq_truncSat32Impl : @truncSat32 = @truncSat32Impl := by
  funext lo hi x
  simp only [truncSat32, truncSat32Impl, Binary32.toInt?_eq_toIntBits]
  cases Binary32.toIntBits (Binary32.toBits x) with
  | some n => rfl
  | none =>
    have hnan : Binary32.isNaN x = Binary32.isNaNBits (Binary32.toBits x) := by
      rw [Binary32.isNaNBits_toBits]; rfl
    have hsb : ExecFloat.Binary.signBit x = decide (0x80000000 ≤ Binary32.toBits x) := by
      rw [← Binary32.signBit_toModel]; rfl
    simp only [hnan, hsb, decide_eq_true_eq]

@[csimp] theorem truncSat64_eq_truncSat64Impl : @truncSat64 = @truncSat64Impl := by
  funext lo hi x
  simp only [truncSat64, truncSat64Impl, Binary64.toInt?_eq_toIntBits]
  cases Binary64.toIntBits (Binary64.toBits x) with
  | some n => rfl
  | none =>
    have hnan : Binary64.isNaN x = Binary64.isNaNBits (Binary64.toBits x) := by
      rw [Binary64.isNaNBits_toBits]; rfl
    have hsb : ExecFloat.Binary.signBit x = decide (0x8000000000000000 ≤ Binary64.toBits x) := by
      rw [← Binary64.signBit_toModel]; rfl
    simp only [hnan, hsb, decide_eq_true_eq]

end CFloat

namespace CFloat.Conv

/-- The exact real that FloatLib's rational rounding receives for an integer. -/
theorem signedScaledRatToReal_int (n : Int) :
    Model.signedScaledRatToReal (decide ((n : Rat).num < 0)) (n : Rat).num.natAbs (n : Rat).den 0 =
      (n : ℝ) := by
  simp only [Rat.num_intCast, Rat.den_intCast]
  by_cases h : n < 0
  · simp [Model.signedScaledRatToReal, Model.scaledRatToReal, h, abs_of_neg h]
  · simp [Model.signedScaledRatToReal, Model.scaledRatToReal, h, abs_of_nonneg (le_of_not_gt h)]

/-- `⌊log₂ v⌋ = k` from `2^k ≤ v < 2^(k+1)`. -/
theorem log2_eq_of_le_of_lt (v k : Nat) (h1 : 2 ^ k ≤ v) (h2 : v < 2 ^ (k + 1)) : v.log2 = k := by
  have hv : v ≠ 0 := by have := Nat.two_pow_pos k; omega
  apply le_antisymm
  · exact Nat.lt_succ_iff.1 ((Nat.log2_lt hv).2 h2)
  · exact (Nat.le_log2 hv).2 h1

/-- FloatLib's nearest-even shift by `s ≥ 1` in quotient/remainder form. -/
theorem roundShiftRightEven_qr (v s : Nat) (hs : s ≠ 0) : FloatLib.Numerics.roundShiftRightEven v s =
    v / 2 ^ s + (if 2 ^ (s - 1) < v % 2 ^ s ∨ (v % 2 ^ s = 2 ^ (s - 1) ∧ v / 2 ^ s % 2 = 1) then 1 else 0) := by
  rw [FloatLib.Numerics.roundShiftRightEven_def]
  have hs' : (s == 0) = false := by simpa using hs
  simp only [hs', Bool.false_eq_true, ↓reduceIte, Nat.shiftRight_eq', Nat.shiftLeft_eq',
    Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq]
  rw [Nat.mul_comm, ← Nat.mod_eq_sub_mul_div]
  simp only [beq_iff_eq]
  split_ifs <;> omega

/-- The dyadic `⟨n < 0, |n|, 0⟩` is the integer `n`. -/
theorem dyadic_int_toReal (n : Int) :
    (⟨decide (n < 0), n.natAbs, 0⟩ : FloatLib.Numerics.Dyadic).toReal = n := by
  rw [Model.Dyadic.toReal_mk]
  simp only [FloatLib.Floats.Formats.Flocq.bpow, zpow_zero, mul_one]
  by_cases h : n < 0
  · simp [h, abs_of_neg h]
  · have h' : 0 ≤ n := le_of_not_gt h
    simp [h]
    exact h'

/-- FloatLib's rational rounding of an integer is its dyadic rounding (`Model.roundDyadicGeneral`)
of `⟨n < 0, |n|, 0⟩`, when the latter is finite and nonzero: both round the real `n`. -/
theorem ofRat_int_eq_roundDyadicGeneral (fmt : FloatFormat) (hfmt : fmt.isIEEE = true) (n : Int)
    (hrange : |(n : ℝ)| ≤ Model.toReal (Model.posMaxFinite fmt))
    (hfin : Model.isFinite (Model.roundDyadicGeneral fmt ⟨decide (n < 0), n.natAbs, 0⟩) = true)
    (hnz : Model.toReal (Model.roundDyadicGeneral fmt ⟨decide (n < 0), n.natAbs, 0⟩) ≠ 0) :
    Model.ofRat fmt (n : Rat) = Model.roundDyadicGeneral fmt ⟨decide (n < 0), n.natAbs, 0⟩ := by
  have hD : Model.toReal (Model.roundDyadicGeneral fmt ⟨decide (n < 0), n.natAbs, 0⟩) =
      Model.roundAt fmt n := by
    rw [Model.roundDyadicGeneral_eq_roundDyadic] at hfin ⊢
    rw [Model.toReal_roundDyadic_eq_roundAt fmt hfmt _ hfin, dyadic_int_toReal]
  have hR : Model.toReal (Model.ofRat fmt (n : Rat)) = Model.roundAt fmt n := by
    change Model.toReal (Model.roundRat fmt (decide ((n : Rat).num < 0)) (n : Rat).num.natAbs
      (n : Rat).den) = _
    rw [Model.roundRat]
    have hfin' := Model.isFinite_roundRatScaled_of_abs_le_posMaxFinite fmt
      (decide ((n : Rat).num < 0)) (n : Rat).num.natAbs (n : Rat).den 0 hfmt (n : Rat).den_nz
      (by rw [signedScaledRatToReal_int]; exact hrange)
    rw [Model.toReal_roundRatScaled_eq_roundAt fmt _ _ _ _ hfmt hfin', signedScaledRatToReal_int]
  symm
  apply Model.eq_of_toReal_eq_of_nonzero
  · rw [hD, hR]
  · exact hnz


/-- The significand of a nonzero `m` brought to `p + 1` bits as `Model.roundDyadicGeneral` does
(`k = ⌊log₂ m⌋`): rounded to nearest even when `k ≥ p`, shifted up otherwise. -/
def roundedSig (p m : Nat) : Nat :=
  if p ≤ m.log2 then FloatLib.Numerics.roundShiftRightEven m (m.log2 - p) else m <<< (p - m.log2)

theorem roundedSig_bounds (p m : Nat) (hm : m ≠ 0) :
    2 ^ p ≤ roundedSig p m ∧ roundedSig p m ≤ 2 ^ (p + 1) := by
  have hklo : 2 ^ m.log2 ≤ m := Nat.log2_self_le hm
  have hkhi : m < 2 ^ (m.log2 + 1) := (Nat.log2_lt hm).1 (Nat.lt_succ_self _)
  unfold roundedSig
  generalize m.log2 = k at hklo hkhi ⊢
  split
  · rename_i hpk
    have hR1 := FloatLib.Numerics.shiftRight_le_roundShiftRightEven m (k - p)
    have hR2 := FloatLib.Numerics.roundShiftRightEven_le_shiftRight_add1 m (k - p)
    have hq : m.shiftRight (k - p) = m / 2 ^ (k - p) := Nat.shiftRight_eq_div_pow _ _
    rw [hq] at hR1 hR2
    have hP : 2 ^ p * 2 ^ (k - p) = 2 ^ k := by rw [← pow_add]; congr 1; omega
    have hlo : 2 ^ p ≤ m / 2 ^ (k - p) := by
      rw [Nat.le_div_iff_mul_le (Nat.two_pow_pos _), hP]; exact hklo
    have hhi : m / 2 ^ (k - p) < 2 ^ (p + 1) := by
      rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _), pow_succ, mul_assoc, mul_comm 2, ← mul_assoc,
        hP, ← pow_succ]; exact hkhi
    omega
  · rename_i hpk
    rw [Nat.shiftLeft_eq]
    have hP : 2 ^ k * 2 ^ (p - k) = 2 ^ p := by rw [← pow_add]; congr 1; omega
    constructor
    · rw [← hP]; exact Nat.mul_le_mul_right _ hklo
    · have : m * 2 ^ (p - k) < 2 ^ (k + 1) * 2 ^ (p - k) :=
        Nat.mul_lt_mul_of_pos_right hkhi (Nat.two_pow_pos _)
      rw [pow_succ, mul_assoc, mul_comm 2, ← mul_assoc, hP, ← pow_succ] at this; omega


/-- `⌊log₂ v⌋ = s + ⌊log₂ (v / 2^s)⌋` when `2^s ≤ v`. -/
theorem log2_eq_add_log2_div (v s : Nat) (h : v / 2 ^ s ≠ 0) : v.log2 = s + (v / 2 ^ s).log2 := by
  have hklo := Nat.log2_self_le h
  have hkhi := (Nat.log2_lt h).1 (Nat.lt_succ_self (v / 2 ^ s).log2)
  generalize (v / 2 ^ s).log2 = j at hklo hkhi
  apply log2_eq_of_le_of_lt
  · rw [pow_add, mul_comm]; exact (Nat.le_div_iff_mul_le (Nat.two_pow_pos _)).1 hklo
  · rw [show s + j + 1 = (j + 1) + s by omega, pow_add]
    exact (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _)).1 hkhi

/-- One step of the binary search for `⌊log₂ m⌋`: the word shifted right by `s` if that leaves it
nonzero (`log2StepK` adds `s` to the count). -/
@[inline] def log2StepM (s m : UInt64) : UInt64 := if m >>> s != 0 then m >>> s else m
@[inline] def log2StepK (s m k : UInt64) : UInt64 := if m >>> s != 0 then k + s else k

theorem log2Step (s m k : UInt64) (hs : s.toNat < 64) (hm : m.toNat ≠ 0) (hk : k.toNat + s.toNat < 2 ^ 64)
    (b : Nat) (hb : m.toNat < 2 ^ (b + s.toNat)) :
    (log2StepM s m).toNat ≠ 0 ∧ (log2StepM s m).toNat < 2 ^ (max b s.toNat) ∧
      (log2StepK s m k).toNat ≤ k.toNat + s.toNat ∧
      (log2StepK s m k).toNat + (log2StepM s m).toNat.log2 = k.toNat + m.toNat.log2 := by
  have hsh : (m >>> s).toNat = m.toNat / 2 ^ s.toNat := by
    rw [UInt64.toNat_shiftRight, Nat.mod_eq_of_lt hs, Nat.shiftRight_eq_div_pow]
  unfold log2StepM log2StepK
  by_cases hc : m >>> s = 0
  · have hc' : (m >>> s != 0) = false := by simpa using hc
    simp only [hc', Bool.false_eq_true, ↓reduceIte]
    have h0 : m.toNat / 2 ^ s.toNat = 0 := by rw [← hsh, hc]; rfl
    have hlt : m.toNat < 2 ^ s.toNat := by
      rcases Nat.lt_or_ge m.toNat (2 ^ s.toNat) with h | h
      · exact h
      · exact absurd h0 (Nat.ne_of_gt (Nat.div_pos h (Nat.two_pow_pos _)))
    refine ⟨hm, lt_of_lt_of_le hlt (Nat.pow_le_pow_right (by norm_num) (le_max_right _ _)), by omega, trivial⟩
  · have hc' : (m >>> s != 0) = true := by simpa using hc
    simp only [hc', ↓reduceIte]
    have h0 : m.toNat / 2 ^ s.toNat ≠ 0 := by
      rw [← hsh]; intro h; apply hc; rw [← UInt64.toNat_inj]; simpa using h
    refine ⟨by rw [hsh]; exact h0, ?_, ?_, ?_⟩
    · rw [hsh, Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _), ← pow_add]
      exact lt_of_lt_of_le hb (Nat.pow_le_pow_right (by norm_num) (by omega))
    · rw [UInt64.toNat_add, Nat.mod_eq_of_lt hk]
    · rw [UInt64.toNat_add, Nat.mod_eq_of_lt hk, hsh, log2_eq_add_log2_div _ _ h0]; omega

/-- `⌊log₂ m⌋` of a nonzero word by binary search (shifts by 32, 16, 8, 4, 2, 1), with no
`Nat` (`log2w_toNat`). -/
@[inline] def log2w (m : UInt64) : UInt64 :=
  let m5 := log2StepM 32 m
  let k5 := log2StepK 32 m 0
  let m4 := log2StepM 16 m5
  let k4 := log2StepK 16 m5 k5
  let m3 := log2StepM 8 m4
  let k3 := log2StepK 8 m4 k4
  let m2 := log2StepM 4 m3
  let k2 := log2StepK 4 m3 k3
  let m1 := log2StepM 2 m2
  let k1 := log2StepK 2 m2 k2
  log2StepK 1 m1 k1

theorem log2w_toNat (m : UInt64) (hm : m ≠ 0) : (log2w m).toNat = m.toNat.log2 := by
  have hm0 : m.toNat ≠ 0 := by
    intro h; apply hm; rw [← UInt64.toNat_inj]; simpa using h
  have hlt : m.toNat < 2 ^ (32 + 32) := UInt64.toNat_lt m
  unfold log2w
  dsimp only
  generalize hm5 : log2StepM 32 m = m5
  generalize hk5 : log2StepK 32 m 0 = k5
  obtain ⟨a5, b5, c5, d5⟩ := log2Step 32 m 0 (by decide) hm0 (by decide) 32 hlt
  rw [hm5, hk5] at *
  simp only [UInt64.reduceToNat, Nat.max_self] at a5 b5 c5 d5
  generalize hm4 : log2StepM 16 m5 = m4
  generalize hk4 : log2StepK 16 m5 k5 = k4
  obtain ⟨a4, b4, c4, d4⟩ := log2Step 16 m5 k5 (by decide) a5 (by simp only [UInt64.reduceToNat]; omega)
    16 (by simpa using b5)
  rw [hm4, hk4] at *
  simp only [UInt64.reduceToNat, Nat.max_self] at a4 b4 c4 d4
  generalize hm3 : log2StepM 8 m4 = m3
  generalize hk3 : log2StepK 8 m4 k4 = k3
  obtain ⟨a3, b3, c3, d3⟩ := log2Step 8 m4 k4 (by decide) a4 (by simp only [UInt64.reduceToNat]; omega)
    8 (by simpa using b4)
  rw [hm3, hk3] at *
  simp only [UInt64.reduceToNat, Nat.max_self] at a3 b3 c3 d3
  generalize hm2 : log2StepM 4 m3 = m2
  generalize hk2 : log2StepK 4 m3 k3 = k2
  obtain ⟨a2, b2, c2, d2⟩ := log2Step 4 m3 k3 (by decide) a3 (by simp only [UInt64.reduceToNat]; omega)
    4 (by simpa using b3)
  rw [hm2, hk2] at *
  simp only [UInt64.reduceToNat, Nat.max_self] at a2 b2 c2 d2
  generalize hm1 : log2StepM 2 m2 = m1
  generalize hk1 : log2StepK 2 m2 k2 = k1
  obtain ⟨a1, b1, c1, d1⟩ := log2Step 2 m2 k2 (by decide) a2 (by simp only [UInt64.reduceToNat]; omega)
    2 (by simpa using b2)
  rw [hm1, hk1] at *
  simp only [UInt64.reduceToNat, Nat.max_self] at a1 b1 c1 d1
  obtain ⟨a0, b0, c0, d0⟩ := log2Step 1 m1 k1 (by decide) a1 (by simp only [UInt64.reduceToNat]; omega)
    1 (by simpa using b1)
  simp only [UInt64.reduceToNat, Nat.max_self] at a0 b0 c0 d0
  have hone : (log2StepM 1 m1).toNat = 1 := by omega
  rw [hone, show Nat.log2 1 = 0 from rfl] at d0
  omega

/-- FloatLib's nearest-even shift (`roundShiftRightEven m sh`) on a word, `1 ≤ sh < 64`: the
quotient, plus one when the dropped bits exceed half or equal half with an odd quotient. -/
@[inline] def roundShiftRightEvenW (m sh : UInt64) : UInt64 :=
  let q := m >>> sh
  let r := m &&& ((1 <<< sh) - 1)
  let half : UInt64 := 1 <<< (sh - 1)
  q + (if half < r || (r == half && (q &&& 1) == 1) then 1 else 0)

theorem roundShiftRightEvenW_toNat (m sh : UInt64) (h1 : 1 ≤ sh.toNat) (h2 : sh.toNat < 64) :
    (roundShiftRightEvenW m sh).toNat = FloatLib.Numerics.roundShiftRightEven m.toNat sh.toNat := by
  have hm : m.toNat < 2 ^ 64 := UInt64.toNat_lt m
  rw [roundShiftRightEven_qr _ _ (by omega)]
  generalize hs : sh.toNat = s at *
  have hq : (m >>> sh).toNat = m.toNat / 2 ^ s := by
    rw [UInt64.toNat_shiftRight, hs, Nat.mod_eq_of_lt h2, Nat.shiftRight_eq_div_pow]
  have hP : 2 ^ s - 1 < 2 ^ 64 := by
    have : 2 ^ s ≤ 2 ^ 64 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hone : ((1 : UInt64) <<< sh).toNat = 2 ^ s := by
    rw [UInt64.toNat_shiftLeft, hs, Nat.mod_eq_of_lt h2]
    simp only [UInt64.reduceToNat, Nat.one_shiftLeft]
    exact Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by norm_num) h2)
  have hr : (m &&& ((1 <<< sh) - 1)).toNat = m.toNat % 2 ^ s := by
    rw [UInt64.toNat_and, UInt64.toNat_sub_of_le _ _ (by
      rw [UInt64.le_iff_toNat_le, hone]; simp only [UInt64.reduceToNat]; exact Nat.one_le_two_pow), hone]
    simp only [UInt64.reduceToNat]
    exact Nat.and_two_pow_sub_one_eq_mod _ _
  have hhalf : ((1 : UInt64) <<< (sh - 1)).toNat = 2 ^ (s - 1) := by
    rw [UInt64.toNat_shiftLeft, UInt64.toNat_sub_of_le _ _ (by
      rw [UInt64.le_iff_toNat_le]; simp only [UInt64.reduceToNat]; omega)]
    simp only [UInt64.reduceToNat, Nat.one_shiftLeft, hs]
    rw [Nat.mod_eq_of_lt (by omega : s - 1 < 64)]
    exact Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by norm_num) (by omega))
  have hq1 : ((m >>> sh) &&& 1).toNat = m.toNat / 2 ^ s % 2 := by
    rw [UInt64.toNat_and, hq]; simp only [UInt64.reduceToNat]
    rw [show (1 : Nat) = 2 ^ 1 - 1 by norm_num, Nat.and_two_pow_sub_one_eq_mod]
  have hqlt : m.toNat / 2 ^ s < 2 ^ 63 := by
    rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _)]
    have : 2 ^ 1 ≤ 2 ^ s := Nat.pow_le_pow_right (by norm_num) h1
    have : 2 ^ 63 * 2 ≤ 2 ^ 63 * 2 ^ s := Nat.mul_le_mul_left _ this
    omega
  have hc : (((1 : UInt64) <<< (sh - 1)) < (m &&& (((1 : UInt64) <<< sh) - 1)) ||
      ((m &&& (((1 : UInt64) <<< sh) - 1)) == ((1 : UInt64) <<< (sh - 1)) && ((m >>> sh) &&& 1) == 1)) =
      decide (2 ^ (s - 1) < m.toNat % 2 ^ s ∨
        (m.toNat % 2 ^ s = 2 ^ (s - 1) ∧ m.toNat / 2 ^ s % 2 = 1)) := by
    rw [Bool.eq_iff_iff]
    simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq,
      UInt64.lt_iff_toNat_lt, ← UInt64.toNat_inj, hr, hq1, hhalf, UInt64.reduceToNat]
  simp only [roundShiftRightEvenW]
  rw [hc, UInt64.toNat_add, hq]
  by_cases hcond : 2 ^ (s - 1) < m.toNat % 2 ^ s ∨
      (m.toNat % 2 ^ s = 2 ^ (s - 1) ∧ m.toNat / 2 ^ s % 2 = 1) <;>
    simp only [hcond, decide_true, decide_false, ↓reduceIte, Bool.false_eq_true, UInt64.reduceToNat] <;>
    omega

end CFloat.Conv

namespace Binary32

theorem ofBits_fields32 (s : Bool) (e f : Nat) (he : e < 2 ^ 8) (hf : f < 2 ^ 23) :
    (Model.ofBits (BitVec.ofNat 32 ((if s then 2 ^ 31 else 0) + e * 2 ^ 23 + f)) : Model .binary32) =
      Model.ofFields .binary32 s e f := by
  generalize hr : (Model.ofBits (BitVec.ofNat 32 ((if s then 2 ^ 31 else 0) + e * 2 ^ 23 + f)) :
    Model .binary32) = r
  have hrb : r.bits.toNat = (if s then 2 ^ 31 else 0) + e * 2 ^ 23 + f := by
    rw [← hr]; show (BitVec.ofNat 32 _).toNat = _; rw [BitVec.toNat_ofNat]
    cases s <;> simp <;> omega
  rw [← Model.ofFields_signBit_expField_fracField r]
  congr 1
  · rw [Model.signBit_eq_msb, BitVec.msb_eq_decide, hrb]
    show decide (2 ^ 31 ≤ _) = _
    cases s <;> simp <;> omega
  · rw [CFloat.Compare.expField_eq, hrb]; show _ / 2 ^ 23 % 2 ^ 8 = _
    cases s <;> simp <;> omega
  · rw [CFloat.Compare.fracField_eq, hrb]; show _ % 2 ^ 23 = _
    cases s <;> simp <;> omega

/-- FloatLib's dyadic rounding of a nonzero integer magnitude `m` to binary32: the significand
`roundedSig 23 m`, the exponent `⌊log₂ m⌋`, a round-up to `2^24` carried into the exponent. -/
theorem roundDyadicGeneral_int (s : Bool) (m : Nat) (hm : m ≠ 0) (hk : m.log2 < 127) :
    Model.roundDyadicGeneral .binary32 ⟨s, m, 0⟩ =
      if CFloat.Conv.roundedSig 23 m = 2 ^ 24 then Model.ofFields .binary32 s (m.log2 + 128) 0
      else Model.ofFields .binary32 s (m.log2 + 127) (CFloat.Conv.roundedSig 23 m - 2 ^ 23) := by
  have hb := CFloat.Conv.roundedSig_bounds 23 m hm
  have hmax : FloatFormat.binary32.maxNormalExponent = 127 := by decide
  have hmin : FloatFormat.binary32.minNormalExponent = -126 := by decide
  have hmfe : FloatFormat.binary32.maxFiniteExpField = 254 := by decide
  have hmff : FloatFormat.binary32.maxFiniteFracField = 2 ^ 23 - 1 := by decide
  have hbias : FloatFormat.binary32.exponentBias = 127 := by decide
  have hfw : FloatFormat.binary32.fracWidth = 23 := rfl
  have hRS : (if 23 ≤ m.log2 then FloatLib.Numerics.roundShiftRightEven m (m.log2 - 23)
      else m <<< (23 - m.log2)) = CFloat.Conv.roundedSig 23 m := rfl
  unfold Model.roundDyadicGeneral Model.packRoundedNormal
  simp only [hmax, hmin, hmfe, hmff, hbias, hfw, Model.pow2_eq_two_pow, Int.ofNat_eq_natCast]
  have hz : (m == 0) = false := by simpa using hm
  simp only [hz, Bool.false_eq_true, ↓reduceIte, hRS]
  generalize CFloat.Conv.roundedSig 23 m = R at *
  generalize m.log2 = k at *
  have h1 : ¬ ((k : Int) + 0 > 127) := by omega
  have h2 : ¬ ((k : Int) + 0 < -126) := by omega
  simp only [h1, h2, ↓reduceIte]
  by_cases hc : R = 2 ^ 24
  · simp only [hc, ↓reduceIte]
    simp
    have e1 : ¬ (127 ≤ k) := by omega
    have e2 : ¬ (254 < (k : Int) + 1 + 127) := by omega
    simp only [e1, e2, ↓reduceIte]
    congr 1
  · have hc' : (R == 2 ^ (23 + 1)) = false := by simpa using hc
    simp only [hc', hc, Bool.false_eq_true, ↓reduceIte]
    simp
    have e1 : ¬ (127 < k) := by omega
    have e2 : ¬ (254 < (k : Int) + 127 ∨ ((k : Int) + 127).toNat = 254 ∧ 8388607 < R - 8388608) := by
      omega
    simp only [e1, e2, ↓reduceIte]
    congr 1

/-- The binary32 bit pattern of a nonzero integer of sign `s` and magnitude `m < 2^127`: the sign,
the biased exponent `127 + ⌊log₂ m⌋`, the significand rounded (or shifted) to 24 bits without its
leading one; a round-up to `2^24` carries into the exponent field. -/
def ofMagBitsNat (s : Bool) (m : Nat) : Nat :=
  (if s then 2 ^ 31 else 0) + (127 + m.log2) * 2 ^ 23 + (CFloat.Conv.roundedSig 23 m - 2 ^ 23)

/-- FloatLib's conversion of a nonzero integer `n`, `|n| < 2^127`, to binary32 is the word
`ofMagBitsNat`: rational and dyadic rounding of the real `n` agree
(`CFloat.Conv.ofRat_int_eq_roundDyadicGeneral`), and the dyadic rounding is FloatLib's integer
algorithm (`roundDyadicGeneral_int`). -/
theorem ofRat_int (n : Int) (h0 : n ≠ 0) (hk : n.natAbs.log2 < 127) :
    Model.ofRat .binary32 (n : Rat) =
      (Model.ofBits (BitVec.ofNat 32 (ofMagBitsNat (decide (n < 0)) n.natAbs)) : Model .binary32) := by
  have hm0 : n.natAbs ≠ 0 := Int.natAbs_ne_zero.2 h0
  have hrd := roundDyadicGeneral_int (decide (n < 0)) n.natAbs hm0 hk
  have hb := CFloat.Conv.roundedSig_bounds 23 n.natAbs hm0
  have hbits : (Model.ofBits (BitVec.ofNat 32 (ofMagBitsNat (decide (n < 0)) n.natAbs)) :
      Model .binary32) = Model.roundDyadicGeneral .binary32 ⟨decide (n < 0), n.natAbs, 0⟩ := by
    rw [hrd]
    unfold ofMagBitsNat
    by_cases hc : CFloat.Conv.roundedSig 23 n.natAbs = 2 ^ 24
    · rw [ite_eq_left_of_eq_true _ _ (eq_true hc), hc,
        show (if decide (n < 0) = true then 2 ^ 31 else 0) + (127 + n.natAbs.log2) * 2 ^ 23 +
          (2 ^ 24 - 2 ^ 23) = (if decide (n < 0) = true then 2 ^ 31 else 0) +
          (n.natAbs.log2 + 128) * 2 ^ 23 + 0 by omega]
      exact ofBits_fields32 _ _ _ (by omega) (by norm_num)
    · rw [ite_eq_right_of_eq_false _ _ (eq_false hc), show 127 + n.natAbs.log2 = n.natAbs.log2 + 127 by omega]
      exact ofBits_fields32 _ _ _ (by omega) (by omega)
  rw [hbits]
  have hbpow : ∀ e : Int, FloatLib.Floats.Formats.Flocq.bpow FloatLib.Numerics.binaryRadix e ≠ 0 := by
    intro e
    have h2 : FloatLib.Numerics.binaryRadix.toReal = 2 := by
      simp [FloatLib.Numerics.binaryRadix, FloatLib.Numerics.Radix.toReal]
    rw [FloatLib.Floats.Formats.Flocq.bpow, h2]
    exact zpow_ne_zero _ two_ne_zero
  apply CFloat.Conv.ofRat_int_eq_roundDyadicGeneral .binary32 (by decide) n
  · rw [Model.toReal_posMaxFinite_of_eq .binary32 (significand := 2 ^ 24 - 1) (exponent := 104)
      (by decide) (by decide)]
    have hkhi : n.natAbs < 2 ^ (n.natAbs.log2 + 1) := (Nat.log2_lt hm0).1 (Nat.lt_succ_self _)
    have hp : 2 ^ (n.natAbs.log2 + 1) ≤ 2 ^ 127 := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h1 : |(n : ℝ)| < 2 ^ 127 := by
      rw [← Int.cast_abs, Int.abs_eq_natAbs]; exact_mod_cast (show n.natAbs < 2 ^ 127 by omega)
    have h2 : (2 : ℝ) ^ 127 ≤ ((2 ^ 24 - 1 : Nat) : ℝ) * (2 : ℝ) ^ (104 : ℤ) := by
      norm_num
    linarith
  · rw [hrd]
    split <;> exact Model.isFinite_ofFields_ieee _ (by decide) _ _ _ (by show _ < 2 ^ 8 - 1; omega)
  · rw [hrd]
    split
    · rw [Model.toReal_ofFields_normal .binary32 _ _ _ (by omega) (by show _ < 2 ^ 8 - 1; omega)
        (by show 0 < 2 ^ 23; norm_num)]
      refine mul_ne_zero (mul_ne_zero (by split <;> norm_num) ?_) (hbpow _)
      rw [Model.pow2_eq_two_pow]; positivity
    · rw [Model.toReal_ofFields_normal .binary32 _ _ _ (by omega) (by show _ < 2 ^ 8 - 1; omega)
        (by show _ < 2 ^ 23; omega)]
      refine mul_ne_zero (mul_ne_zero (by split <;> norm_num) ?_) (hbpow _)
      rw [Model.pow2_eq_two_pow]; positivity

/-- `ofMagBitsNat` on the word: `k = ⌊log₂ m⌋` (`CFloat.Conv.log2w`); for `k < 24` the magnitude
shifted up to 24 bits (exact), otherwise shifted right by `k - 23` and rounded to nearest even
(`CFloat.Conv.roundShiftRightEvenW`); sign, exponent `127 + k` and significand without its leading
one are added, so a round-up to `2^24` carries into the exponent field (`ofMagWord_toNat`). -/
@[inline] def ofMagWord (neg : Bool) (m : UInt64) : UInt32 :=
  let k := CFloat.Conv.log2w m
  let sig : UInt64 := if k < 24 then m <<< (23 - k) else CFloat.Conv.roundShiftRightEvenW m (k - 23)
  ((if neg then (0x80000000 : UInt64) else 0) + ((127 + k) <<< 23) + (sig - 0x800000)).toUInt32

theorem ofMagWord_toNat (neg : Bool) (m : UInt64) (hm : m ≠ 0) :
    (ofMagWord neg m).toNat = ofMagBitsNat neg m.toNat := by
  have hm0 : m.toNat ≠ 0 := by
    intro h; apply hm; rw [← UInt64.toNat_inj]; simpa using h
  have hmlt : m.toNat < 2 ^ 64 := UInt64.toNat_lt m
  have hK := CFloat.Conv.log2w_toNat m hm
  have hK64 : m.toNat.log2 < 64 := (Nat.log2_lt hm0).2 hmlt
  have hklo : 2 ^ m.toNat.log2 ≤ m.toNat := Nat.log2_self_le hm0
  have hkhi : m.toNat < 2 ^ (m.toNat.log2 + 1) := (Nat.log2_lt hm0).1 (Nat.lt_succ_self _)
  have hb := CFloat.Conv.roundedSig_bounds 23 m.toNat hm0
  have hsig : (if CFloat.Conv.log2w m < 24 then m <<< (23 - CFloat.Conv.log2w m)
      else CFloat.Conv.roundShiftRightEvenW m (CFloat.Conv.log2w m - 23)).toNat =
      CFloat.Conv.roundedSig 23 m.toNat := by
    unfold CFloat.Conv.roundedSig
    by_cases hk : m.toNat.log2 < 24
    · have hc : CFloat.Conv.log2w m < 24 := by
        rw [UInt64.lt_iff_toNat_lt, hK]; simpa using hk
      simp only [hc, ↓reduceIte]
      have h23 : (23 - CFloat.Conv.log2w m).toNat = 23 - m.toNat.log2 := by
        rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le, hK]; simp only [UInt64.reduceToNat]; omega), hK]
        rfl
      have hP : 2 ^ m.toNat.log2 * 2 ^ (23 - m.toNat.log2) = 2 ^ 23 := by
        rw [← pow_add]; congr 1; omega
      have hhi : m.toNat * 2 ^ (23 - m.toNat.log2) < 2 ^ 24 := by
        have : m.toNat * 2 ^ (23 - m.toNat.log2) < 2 ^ (m.toNat.log2 + 1) * 2 ^ (23 - m.toNat.log2) :=
          Nat.mul_lt_mul_of_pos_right hkhi (Nat.two_pow_pos _)
        rw [pow_succ, mul_assoc, mul_comm 2, ← mul_assoc, hP] at this; omega
      rw [UInt64.toNat_shiftLeft, h23, Nat.mod_eq_of_lt (by omega : 23 - m.toNat.log2 < 64),
        Nat.shiftLeft_eq, Nat.mod_eq_of_lt (by omega)]
      split
      · have h23' : m.toNat.log2 = 23 := by omega
        rw [h23', Nat.sub_self, FloatLib.Numerics.roundShiftRightEven_def]; simp
      · rfl
    · have hc : ¬ CFloat.Conv.log2w m < 24 := by
        rw [UInt64.lt_iff_toNat_lt, hK]; simpa using hk
      simp only [hc, ↓reduceIte, show 23 ≤ m.toNat.log2 by omega]
      have hsh : (CFloat.Conv.log2w m - 23).toNat = m.toNat.log2 - 23 := by
        rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le, hK]; simp only [UInt64.reduceToNat]; omega), hK]
        rfl
      rw [CFloat.Conv.roundShiftRightEvenW_toNat _ _ (by omega) (by omega), hsh]
  generalize hS : (if CFloat.Conv.log2w m < 24 then m <<< (23 - CFloat.Conv.log2w m)
      else CFloat.Conv.roundShiftRightEvenW m (CFloat.Conv.log2w m - 23)) = sig at hsig
  have hsub : (sig - 0x800000).toNat = CFloat.Conv.roundedSig 23 m.toNat - 2 ^ 23 := by
    rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le, hsig]; simpa using hb.1), hsig]; rfl
  have hexp : ((127 + CFloat.Conv.log2w m) <<< 23).toNat = (127 + m.toNat.log2) * 2 ^ 23 := by
    rw [UInt64.toNat_shiftLeft, UInt64.toNat_add, hK]
    simp only [UInt64.reduceToNat, Nat.reduceMod, Nat.shiftLeft_eq]
    rw [Nat.mod_eq_of_lt (by omega)]
    omega
  have hs : ((if neg then 0x80000000 else 0 : UInt64)).toNat = (if neg then 2 ^ 31 else 0) := by
    split <;> rfl
  unfold ofMagWord ofMagBitsNat
  simp only [hS, UInt64.toNat_toUInt32, UInt64.toNat_add, hsub, hexp, hs]
  split <;> omega

end Binary32

namespace Binary64

theorem ofBits_fields64 (s : Bool) (e f : Nat) (he : e < 2 ^ 11) (hf : f < 2 ^ 52) :
    (Model.ofBits (BitVec.ofNat 64 ((if s then 2 ^ 63 else 0) + e * 2 ^ 52 + f)) : Model .binary64) =
      Model.ofFields .binary64 s e f := by
  generalize hr : (Model.ofBits (BitVec.ofNat 64 ((if s then 2 ^ 63 else 0) + e * 2 ^ 52 + f)) :
    Model .binary64) = r
  have hrb : r.bits.toNat = (if s then 2 ^ 63 else 0) + e * 2 ^ 52 + f := by
    rw [← hr]; show (BitVec.ofNat 64 _).toNat = _; rw [BitVec.toNat_ofNat]
    cases s <;> simp <;> omega
  rw [← Model.ofFields_signBit_expField_fracField r]
  congr 1
  · rw [Model.signBit_eq_msb, BitVec.msb_eq_decide, hrb]
    show decide (2 ^ 63 ≤ _) = _
    cases s <;> simp <;> omega
  · rw [CFloat.Compare.expField_eq, hrb]; show _ / 2 ^ 52 % 2 ^ 11 = _
    cases s <;> simp <;> omega
  · rw [CFloat.Compare.fracField_eq, hrb]; show _ % 2 ^ 52 = _
    cases s <;> simp <;> omega

/-- FloatLib's dyadic rounding of a nonzero integer magnitude `m` to binary64: the significand
`roundedSig 52 m`, the exponent `⌊log₂ m⌋`, a round-up to `2^53` carried into the exponent. -/
theorem roundDyadicGeneral_int (s : Bool) (m : Nat) (hm : m ≠ 0) (hk : m.log2 < 1023) :
    Model.roundDyadicGeneral .binary64 ⟨s, m, 0⟩ =
      if CFloat.Conv.roundedSig 52 m = 2 ^ 53 then Model.ofFields .binary64 s (m.log2 + 1024) 0
      else Model.ofFields .binary64 s (m.log2 + 1023) (CFloat.Conv.roundedSig 52 m - 2 ^ 52) := by
  have hb := CFloat.Conv.roundedSig_bounds 52 m hm
  have hmax : FloatFormat.binary64.maxNormalExponent = 1023 := by decide
  have hmin : FloatFormat.binary64.minNormalExponent = -1022 := by decide
  have hmfe : FloatFormat.binary64.maxFiniteExpField = 2046 := by decide
  have hmff : FloatFormat.binary64.maxFiniteFracField = 2 ^ 52 - 1 := by decide
  have hbias : FloatFormat.binary64.exponentBias = 1023 := by decide
  have hfw : FloatFormat.binary64.fracWidth = 52 := rfl
  have hRS : (if 52 ≤ m.log2 then FloatLib.Numerics.roundShiftRightEven m (m.log2 - 52)
      else m <<< (52 - m.log2)) = CFloat.Conv.roundedSig 52 m := rfl
  unfold Model.roundDyadicGeneral Model.packRoundedNormal
  simp only [hmax, hmin, hmfe, hmff, hbias, hfw, Model.pow2_eq_two_pow, Int.ofNat_eq_natCast]
  have hz : (m == 0) = false := by simpa using hm
  simp only [hz, Bool.false_eq_true, ↓reduceIte, hRS]
  generalize CFloat.Conv.roundedSig 52 m = R at *
  generalize m.log2 = k at *
  have h1 : ¬ ((k : Int) + 0 > 1023) := by omega
  have h2 : ¬ ((k : Int) + 0 < -1022) := by omega
  simp only [h1, h2, ↓reduceIte]
  by_cases hc : R = 2 ^ 53
  · simp only [hc, ↓reduceIte]
    simp
    have e1 : ¬ (1023 ≤ k) := by omega
    have e2 : ¬ (2046 < (k : Int) + 1 + 1023) := by omega
    simp only [e1, e2, ↓reduceIte]
    congr 1
  · have hc' : (R == 2 ^ (52 + 1)) = false := by simpa using hc
    simp only [hc', hc, Bool.false_eq_true, ↓reduceIte]
    simp
    have e1 : ¬ (1023 < k) := by omega
    have e2 : ¬ (2046 < (k : Int) + 1023 ∨ ((k : Int) + 1023).toNat = 2046 ∧ 4503599627370495 < R - 4503599627370496) := by
      omega
    simp only [e1, e2, ↓reduceIte]
    congr 1

/-- The binary64 bit pattern of a nonzero integer of sign `s` and magnitude `m < 2^1023`: the sign,
the biased exponent `1023 + ⌊log₂ m⌋`, the significand rounded (or shifted) to 53 bits without its
leading one; a round-up to `2^53` carries into the exponent field. -/
def ofMagBitsNat (s : Bool) (m : Nat) : Nat :=
  (if s then 2 ^ 63 else 0) + (1023 + m.log2) * 2 ^ 52 + (CFloat.Conv.roundedSig 52 m - 2 ^ 52)

set_option exponentiation.threshold 1100 in
/-- FloatLib's conversion of a nonzero integer `n`, `|n| < 2^1023`, to binary64 is the word
`ofMagBitsNat`: rational and dyadic rounding of the real `n` agree
(`CFloat.Conv.ofRat_int_eq_roundDyadicGeneral`), and the dyadic rounding is FloatLib's integer
algorithm (`roundDyadicGeneral_int`). -/
theorem ofRat_int (n : Int) (h0 : n ≠ 0) (hk : n.natAbs.log2 < 1023) :
    Model.ofRat .binary64 (n : Rat) =
      (Model.ofBits (BitVec.ofNat 64 (ofMagBitsNat (decide (n < 0)) n.natAbs)) : Model .binary64) := by
  have hm0 : n.natAbs ≠ 0 := Int.natAbs_ne_zero.2 h0
  have hrd := roundDyadicGeneral_int (decide (n < 0)) n.natAbs hm0 hk
  have hb := CFloat.Conv.roundedSig_bounds 52 n.natAbs hm0
  have hbits : (Model.ofBits (BitVec.ofNat 64 (ofMagBitsNat (decide (n < 0)) n.natAbs)) :
      Model .binary64) = Model.roundDyadicGeneral .binary64 ⟨decide (n < 0), n.natAbs, 0⟩ := by
    rw [hrd]
    unfold ofMagBitsNat
    by_cases hc : CFloat.Conv.roundedSig 52 n.natAbs = 2 ^ 53
    · rw [ite_eq_left_of_eq_true _ _ (eq_true hc), hc,
        show (if decide (n < 0) = true then 2 ^ 63 else 0) + (1023 + n.natAbs.log2) * 2 ^ 52 +
          (2 ^ 53 - 2 ^ 52) = (if decide (n < 0) = true then 2 ^ 63 else 0) +
          (n.natAbs.log2 + 1024) * 2 ^ 52 + 0 by omega]
      exact ofBits_fields64 _ _ _ (by omega) (by norm_num)
    · rw [ite_eq_right_of_eq_false _ _ (eq_false hc), show 1023 + n.natAbs.log2 = n.natAbs.log2 + 1023 by omega]
      exact ofBits_fields64 _ _ _ (by omega) (by omega)
  rw [hbits]
  have hbpow : ∀ e : Int, FloatLib.Floats.Formats.Flocq.bpow FloatLib.Numerics.binaryRadix e ≠ 0 := by
    intro e
    have h2 : FloatLib.Numerics.binaryRadix.toReal = 2 := by
      simp [FloatLib.Numerics.binaryRadix, FloatLib.Numerics.Radix.toReal]
    rw [FloatLib.Floats.Formats.Flocq.bpow, h2]
    exact zpow_ne_zero _ two_ne_zero
  apply CFloat.Conv.ofRat_int_eq_roundDyadicGeneral .binary64 (by decide) n
  · rw [Model.toReal_posMaxFinite_of_eq .binary64 (significand := 2 ^ 53 - 1) (exponent := 971)
      (by decide) (by decide)]
    have hkhi : n.natAbs < 2 ^ (n.natAbs.log2 + 1) := (Nat.log2_lt hm0).1 (Nat.lt_succ_self _)
    have hp : 2 ^ (n.natAbs.log2 + 1) ≤ 2 ^ 1023 := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h1 : |(n : ℝ)| < 2 ^ 1023 := by
      rw [← Int.cast_abs, Int.abs_eq_natAbs]; exact_mod_cast (show n.natAbs < 2 ^ 1023 by omega)
    have h2 : (2 : ℝ) ^ 1023 ≤ ((2 ^ 53 - 1 : Nat) : ℝ) * (2 : ℝ) ^ (971 : ℤ) := by
      have e1 : (2 : ℝ) ^ (971 : ℤ) = (2 : ℝ) ^ (971 : ℕ) := zpow_natCast 2 971
      have e2 : (2 : ℝ) ^ 1023 = (2 : ℝ) ^ 52 * (2 : ℝ) ^ (971 : ℕ) := by rw [← pow_add]
      rw [e1, e2]
      gcongr
      norm_num
    linarith
  · rw [hrd]
    split <;> exact Model.isFinite_ofFields_ieee _ (by decide) _ _ _ (by show _ < 2 ^ 11 - 1; omega)
  · rw [hrd]
    split
    · rw [Model.toReal_ofFields_normal .binary64 _ _ _ (by omega) (by show _ < 2 ^ 11 - 1; omega)
        (by show 0 < 2 ^ 52; norm_num)]
      refine mul_ne_zero (mul_ne_zero (by split <;> norm_num) ?_) (hbpow _)
      rw [Model.pow2_eq_two_pow]; positivity
    · rw [Model.toReal_ofFields_normal .binary64 _ _ _ (by omega) (by show _ < 2 ^ 11 - 1; omega)
        (by show _ < 2 ^ 52; omega)]
      refine mul_ne_zero (mul_ne_zero (by split <;> norm_num) ?_) (hbpow _)
      rw [Model.pow2_eq_two_pow]; positivity

/-- `ofMagBitsNat` on the word, as `Binary32.ofMagWord`: for `k = ⌊log₂ m⌋ < 53` the magnitude
shifted up to 53 bits (exact), otherwise shifted right by `k - 52` and rounded to nearest even;
exponent `1023 + k` (`ofMagWord_toNat`). -/
@[inline] def ofMagWord (neg : Bool) (m : UInt64) : UInt64 :=
  let k := CFloat.Conv.log2w m
  let sig : UInt64 := if k < 53 then m <<< (52 - k) else CFloat.Conv.roundShiftRightEvenW m (k - 52)
  ((if neg then (0x8000000000000000 : UInt64) else 0) + ((1023 + k) <<< 52) + (sig - 0x10000000000000))

theorem ofMagWord_toNat (neg : Bool) (m : UInt64) (hm : m ≠ 0) :
    (ofMagWord neg m).toNat = ofMagBitsNat neg m.toNat := by
  have hm0 : m.toNat ≠ 0 := by
    intro h; apply hm; rw [← UInt64.toNat_inj]; simpa using h
  have hmlt : m.toNat < 2 ^ 64 := UInt64.toNat_lt m
  have hK := CFloat.Conv.log2w_toNat m hm
  have hK64 : m.toNat.log2 < 64 := (Nat.log2_lt hm0).2 hmlt
  have hklo : 2 ^ m.toNat.log2 ≤ m.toNat := Nat.log2_self_le hm0
  have hkhi : m.toNat < 2 ^ (m.toNat.log2 + 1) := (Nat.log2_lt hm0).1 (Nat.lt_succ_self _)
  have hb := CFloat.Conv.roundedSig_bounds 52 m.toNat hm0
  have hsig : (if CFloat.Conv.log2w m < 53 then m <<< (52 - CFloat.Conv.log2w m)
      else CFloat.Conv.roundShiftRightEvenW m (CFloat.Conv.log2w m - 52)).toNat =
      CFloat.Conv.roundedSig 52 m.toNat := by
    unfold CFloat.Conv.roundedSig
    by_cases hk : m.toNat.log2 < 53
    · have hc : CFloat.Conv.log2w m < 53 := by
        rw [UInt64.lt_iff_toNat_lt, hK]; simpa using hk
      simp only [hc, ↓reduceIte]
      have h52 : (52 - CFloat.Conv.log2w m).toNat = 52 - m.toNat.log2 := by
        rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le, hK]; simp only [UInt64.reduceToNat]; omega), hK]
        rfl
      have hP : 2 ^ m.toNat.log2 * 2 ^ (52 - m.toNat.log2) = 2 ^ 52 := by
        rw [← pow_add]; congr 1; omega
      have hhi : m.toNat * 2 ^ (52 - m.toNat.log2) < 2 ^ 53 := by
        have : m.toNat * 2 ^ (52 - m.toNat.log2) < 2 ^ (m.toNat.log2 + 1) * 2 ^ (52 - m.toNat.log2) :=
          Nat.mul_lt_mul_of_pos_right hkhi (Nat.two_pow_pos _)
        rw [pow_succ, mul_assoc, mul_comm 2, ← mul_assoc, hP] at this; omega
      rw [UInt64.toNat_shiftLeft, h52, Nat.mod_eq_of_lt (by omega : 52 - m.toNat.log2 < 64),
        Nat.shiftLeft_eq, Nat.mod_eq_of_lt (by omega)]
      split
      · have h52' : m.toNat.log2 = 52 := by omega
        rw [h52', Nat.sub_self, FloatLib.Numerics.roundShiftRightEven_def]; simp
      · rfl
    · have hc : ¬ CFloat.Conv.log2w m < 53 := by
        rw [UInt64.lt_iff_toNat_lt, hK]; simpa using hk
      simp only [hc, ↓reduceIte, show 52 ≤ m.toNat.log2 by omega]
      have hsh : (CFloat.Conv.log2w m - 52).toNat = m.toNat.log2 - 52 := by
        rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le, hK]; simp only [UInt64.reduceToNat]; omega), hK]
        rfl
      rw [CFloat.Conv.roundShiftRightEvenW_toNat _ _ (by omega) (by omega), hsh]
  generalize hS : (if CFloat.Conv.log2w m < 53 then m <<< (52 - CFloat.Conv.log2w m)
      else CFloat.Conv.roundShiftRightEvenW m (CFloat.Conv.log2w m - 52)) = sig at hsig
  have hsub : (sig - 0x10000000000000).toNat = CFloat.Conv.roundedSig 52 m.toNat - 2 ^ 52 := by
    rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le, hsig]; simpa using hb.1), hsig]; rfl
  have hexp : ((1023 + CFloat.Conv.log2w m) <<< 52).toNat = (1023 + m.toNat.log2) * 2 ^ 52 := by
    rw [UInt64.toNat_shiftLeft, UInt64.toNat_add, hK]
    simp only [UInt64.reduceToNat, Nat.reduceMod, Nat.shiftLeft_eq]
    rw [Nat.mod_eq_of_lt (by omega)]
    omega
  have hs : ((if neg then 0x8000000000000000 else 0 : UInt64)).toNat = (if neg then 2 ^ 63 else 0) := by
    split <;> rfl
  unfold ofMagWord ofMagBitsNat
  simp only [hS, UInt64.toNat_add, hsub, hexp, hs]
  split <;> omega

end Binary64

namespace CFloat

/-- C's conversion to `float` of the integer of sign `neg` and magnitude `m` (a word):
`+0` for `m = 0`, otherwise `Binary32.ofMagWord` (`ofInt32_eq_ofMag32`). -/
@[inline] def ofMag32 (neg : Bool) (m : UInt64) : Binary32 :=
  if m == 0 then Binary32.ofBits 0 else Binary32.ofBits (Binary32.ofMagWord neg m)

theorem ofInt32_eq_ofMag32 (n : Int) (m : UInt64) (hm : m.toNat = n.natAbs) :
    ofInt32 n = ofMag32 (decide (n < 0)) m := by
  unfold ofMag32
  by_cases h0 : n = 0
  · subst h0
    have : m = 0 := by rw [← UInt64.toNat_inj]; simpa using hm
    subst this
    simp only [beq_self_eq_true, ↓reduceIte]
    decide
  · have hm0 : m ≠ 0 := by
      intro h; subst h; apply h0; simpa using hm.symm
    have hm0' : (m == 0) = false := by simpa using hm0
    simp only [hm0', Bool.false_eq_true, ↓reduceIte]
    have hk : n.natAbs.log2 < 127 := by
      rw [← hm]
      have := (Nat.log2_lt (by rw [hm]; exact Int.natAbs_ne_zero.2 h0)).2 (UInt64.toNat_lt m)
      omega
    have hmodel := Binary32.ofRat_int n h0 hk
    have hword := Binary32.ofMagWord_toNat (decide (n < 0)) m hm0
    rw [hm] at hword
    generalize hw : Binary32.ofMagWord (decide (n < 0)) m = w at hword
    have hto : ExecFloat.Binary.toModel (Binary32.ofBits w) =
        (Model.ofBits (BitVec.ofNatLT w.toNat (UInt32.toNat_lt w)) : Model .binary32) := rfl
    have hbv : BitVec.ofNatLT w.toNat (UInt32.toNat_lt w) =
        BitVec.ofNat 32 (Binary32.ofMagBitsNat (decide (n < 0)) n.natAbs) := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_ofNatLT, BitVec.toNat_ofNat, ← hword, Nat.mod_eq_of_lt (UInt32.toNat_lt w)]
    calc ofInt32 n = (ExecFloat.Binary.ofModel (Model.ofRat .binary32 (n : Rat)) : Binary32) := rfl
      _ = (ExecFloat.Binary.ofModel (Model.ofBits (BitVec.ofNat 32
            (Binary32.ofMagBitsNat (decide (n < 0)) n.natAbs)) : Model .binary32) : Binary32) := by
            rw [hmodel]
      _ = (ExecFloat.Binary.ofModel (ExecFloat.Binary.toModel (Binary32.ofBits w)) : Binary32) := by
            rw [hto]
            exact congrArg (fun b => (ExecFloat.Binary.ofModel (Model.ofBits b : Model .binary32) :
              Binary32)) hbv.symm
      _ = Binary32.ofBits w := ExecFloat.Binary.ofModel_toModel _

/-- C's conversion to `double` of the integer of sign `neg` and magnitude `m` (a word):
`+0` for `m = 0`, otherwise `Binary64.ofMagWord` (`ofInt64_eq_ofMag64`). -/
@[inline] def ofMag64 (neg : Bool) (m : UInt64) : Binary64 :=
  if m == 0 then Binary64.ofBits 0 else Binary64.ofBits (Binary64.ofMagWord neg m)

theorem ofInt64_eq_ofMag64 (n : Int) (m : UInt64) (hm : m.toNat = n.natAbs) :
    ofInt64 n = ofMag64 (decide (n < 0)) m := by
  unfold ofMag64
  by_cases h0 : n = 0
  · subst h0
    have : m = 0 := by rw [← UInt64.toNat_inj]; simpa using hm
    subst this
    simp only [beq_self_eq_true, ↓reduceIte]
    decide
  · have hm0 : m ≠ 0 := by
      intro h; subst h; apply h0; simpa using hm.symm
    have hm0' : (m == 0) = false := by simpa using hm0
    simp only [hm0', Bool.false_eq_true, ↓reduceIte]
    have hk : n.natAbs.log2 < 1023 := by
      rw [← hm]
      have := (Nat.log2_lt (by rw [hm]; exact Int.natAbs_ne_zero.2 h0)).2 (UInt64.toNat_lt m)
      omega
    have hmodel := Binary64.ofRat_int n h0 hk
    have hword := Binary64.ofMagWord_toNat (decide (n < 0)) m hm0
    rw [hm] at hword
    generalize hw : Binary64.ofMagWord (decide (n < 0)) m = w at hword
    have hto : ExecFloat.Binary.toModel (Binary64.ofBits w) =
        (Model.ofBits (BitVec.ofNatLT w.toNat (UInt64.toNat_lt w)) : Model .binary64) := rfl
    have hbv : BitVec.ofNatLT w.toNat (UInt64.toNat_lt w) =
        BitVec.ofNat 64 (Binary64.ofMagBitsNat (decide (n < 0)) n.natAbs) := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_ofNatLT, BitVec.toNat_ofNat, ← hword, Nat.mod_eq_of_lt (UInt64.toNat_lt w)]
    calc ofInt64 n = (ExecFloat.Binary.ofModel (Model.ofRat .binary64 (n : Rat)) : Binary64) := rfl
      _ = (ExecFloat.Binary.ofModel (Model.ofBits (BitVec.ofNat 64
            (Binary64.ofMagBitsNat (decide (n < 0)) n.natAbs)) : Model .binary64) : Binary64) := by
            rw [hmodel]
      _ = (ExecFloat.Binary.ofModel (ExecFloat.Binary.toModel (Binary64.ofBits w)) : Binary64) := by
            rw [hto]
            exact congrArg (fun b => (ExecFloat.Binary.ofModel (Model.ofBits b : Model .binary64) :
              Binary64)) hbv.symm
      _ = Binary64.ofBits w := ExecFloat.Binary.ofModel_toModel _

end CFloat

namespace CFloat

/-- `ofInt32` itself, out of line: the path `ofInt32Impl` takes for `|n| ≥ 2^64`. -/
@[noinline] def ofInt32Slow (n : Int) : Binary32 := ExecFloat.Binary.ofRat (n : Rat)
/-- `ofInt64` itself, out of line: the path `ofInt64Impl` takes for `|n| ≥ 2^64`. -/
@[noinline] def ofInt64Slow (n : Int) : Binary64 := ExecFloat.Binary.ofRat (n : Rat)

/-- `ofInt32` on the bit patterns for `|n| < 2^64` (`ofMag32`: exact below `2^24`, rounded to
nearest even above), in `UInt64` arithmetic (`ofInt32_eq_ofInt32Impl`). -/
@[inline] def ofInt32Impl (n : Int) : Binary32 :=
  let m := n.natAbs
  if m < 0x10000000000000000 then ofMag32 (decide (n < 0)) (UInt64.ofNat m) else ofInt32Slow n

/-- `ofInt64` on the bit patterns for `|n| < 2^64` (`ofMag64`: exact below `2^53`, rounded to
nearest even above), in `UInt64` arithmetic (`ofInt64_eq_ofInt64Impl`). -/
@[inline] def ofInt64Impl (n : Int) : Binary64 :=
  let m := n.natAbs
  if m < 0x10000000000000000 then ofMag64 (decide (n < 0)) (UInt64.ofNat m) else ofInt64Slow n

@[csimp] theorem ofInt32_eq_ofInt32Impl : @ofInt32 = @ofInt32Impl := by
  funext n
  unfold ofInt32Impl
  dsimp only
  split
  · rename_i h
    exact ofInt32_eq_ofMag32 n _ (UInt64.toNat_ofNat_of_lt' h)
  · rfl

@[csimp] theorem ofInt64_eq_ofInt64Impl : @ofInt64 = @ofInt64Impl := by
  funext n
  unfold ofInt64Impl
  dsimp only
  split
  · rename_i h
    exact ofInt64_eq_ofMag64 n _ (UInt64.toNat_ofNat_of_lt' h)
  · rfl

end CFloat

namespace CFloat.Conv

/-- FloatLib's nearest-even shift by 29 in quotient/remainder form. -/
theorem roundShiftRightEven_29 (v : Nat) : FloatLib.Numerics.roundShiftRightEven v 29 =
    v / 2 ^ 29 + (if 2 ^ 28 < v % 2 ^ 29 ∨ (v % 2 ^ 29 = 2 ^ 28 ∧ v / 2 ^ 29 % 2 = 1) then 1 else 0) := by
  rw [FloatLib.Numerics.roundShiftRightEven_def]
  simp only [Nat.reduceBEq, Bool.false_eq_true, ↓reduceIte, Nat.shiftRight_eq', Nat.shiftLeft_eq',
    Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq, Nat.reduceSub]
  have h := Nat.div_add_mod v (2 ^ 29)
  have hr : v - v / 2 ^ 29 * 2 ^ 29 = v % 2 ^ 29 := by omega
  rw [hr]
  simp only [beq_iff_eq]
  split_ifs <;> omega

end CFloat.Conv

namespace Binary64

/-- FloatLib's cast of a double whose result is a normal float (biased exponent in `[897, 1149]`):
`Model.cast` rounds the exact dyadic (`Model.roundDyadic`, which is `Model.roundDyadicGeneral`), whose
normal branch keeps 24 bits of the 53-bit significand rounded to nearest even
(`roundShiftRightEven … 29`) and carries a round-up to `2^24` into the exponent. -/
theorem cast_binary32_model (m : Model FloatFormat.binary64) (n : Nat) (hb : m.bits.toNat = n)
    (hE : 897 ≤ n / 2 ^ 52 % 2 ^ 11 ∧ n / 2 ^ 52 % 2 ^ 11 ≤ 1149) :
    Model.cast .binary64 .binary32 m =
      if FloatLib.Numerics.roundShiftRightEven (2 ^ 52 + n % 2 ^ 52) 29 = 2 ^ 24 then
        Model.ofFields .binary32 (decide (2 ^ 63 ≤ n)) (n / 2 ^ 52 % 2 ^ 11 - 895) 0
      else
        Model.ofFields .binary32 (decide (2 ^ 63 ≤ n)) (n / 2 ^ 52 % 2 ^ 11 - 896)
          (FloatLib.Numerics.roundShiftRightEven (2 ^ 52 + n % 2 ^ 52) 29 - 2 ^ 23) := by
  have hs : Model.signBit m = decide (2 ^ 63 ≤ n) := by
    rw [Model.signBit_eq_msb, BitVec.msb_eq_decide, hb]; rfl
  have he : Model.expField m = n / 2 ^ 52 % 2 ^ 11 := by
    rw [CFloat.Compare.expField_eq, hb]; rfl
  have hf : Model.fracField m = n % 2 ^ 52 := by
    rw [CFloat.Compare.fracField_eq, hb]; rfl
  have hnan : Model.isNaN m = false := by
    show Model.IEEE.isNaN _ = false
    simp only [Model.IEEE.isNaN, he, hf]
    rw [Bool.eq_false_iff]
    simp only [ne_eq, Bool.and_eq_true, beq_iff_eq, bne_iff_ne]
    show ¬(_ = 2 ^ 11 - 1 ∧ _)
    omega
  have hinf : Model.isInf m = false := by
    show Model.IEEE.isInf _ = false
    simp only [Model.IEEE.isInf, he, hf]
    rw [Bool.eq_false_iff]
    simp only [ne_eq, Bool.and_eq_true, beq_iff_eq]
    show ¬(_ = 2 ^ 11 - 1 ∧ _)
    omega
  have hfin := Model.isFinite_eq_true_of_isNaN_eq_false_of_isInf_eq_false _ hnan hinf
  have hcast : Model.cast .binary64 .binary32 m =
      Model.roundDyadic .binary32 (Model.finiteDyadic m hfin) := by
    have hexp : FloatFormat.binary64.expWidth ≠ FloatFormat.binary32.expWidth := by decide
    have hne : FloatFormat.binary64 ≠ FloatFormat.binary32 := fun h => hexp (h ▸ rfl)
    unfold Model.cast Model.Internal.Directed.cast Model.Internal.Nearest.cast
    simp only [hnan, hinf, hne, hexp, Bool.false_eq_true, ↓reduceDIte]
  rw [hcast]
  have he0 : n / 2 ^ 52 % 2 ^ 11 ≠ 0 := by omega
  have he1 : n / 2 ^ 52 % 2 ^ 11 < FloatFormat.expAllOnesNat .binary64 := by
    show _ < 2 ^ 11 - 1; omega
  have hd : Model.toDyadic? m = some ⟨decide (2 ^ 63 ≤ n), Model.pow2 52 + n % 2 ^ 52,
      Int.ofNat (n / 2 ^ 52 % 2 ^ 11) - 1023 - 52⟩ := by
    have h := Model.toDyadic?_ofFields_normal .binary64 (decide (2 ^ 63 ≤ n)) (n / 2 ^ 52 % 2 ^ 11)
      (n % 2 ^ 52) he0 he1 (by show n % 2 ^ 52 < 2 ^ 52; omega)
    have hm : Model.ofFields .binary64 (decide (2 ^ 63 ≤ n)) (n / 2 ^ 52 % 2 ^ 11) (n % 2 ^ 52) =
        m := by
      rw [← hs, ← he, ← hf]; exact Model.ofFields_signBit_expField_fracField m
    rw [hm] at h
    exact h
  rw [Model.finiteDyadic_eq_of_toDyadic hfin hd, ← Model.roundDyadicGeneral_eq_roundDyadic]
  generalize decide (2 ^ 63 ≤ n) = s
  have hEb := hE
  generalize n / 2 ^ 52 % 2 ^ 11 = E at *
  have hF : n % 2 ^ 52 < 2 ^ 52 := Nat.mod_lt _ (by norm_num)
  generalize n % 2 ^ 52 = F at *
  rw [Model.pow2_eq_two_pow]
  have hlog : (2 ^ 52 + F).log2 = 52 := CFloat.Conv.log2_eq_of_le_of_lt _ _ (by omega) (by omega)
  have hR1 := FloatLib.Numerics.shiftRight_le_roundShiftRightEven (2 ^ 52 + F) 29
  have hR2 := FloatLib.Numerics.roundShiftRightEven_le_shiftRight_add1 (2 ^ 52 + F) 29
  have hq : (2 ^ 52 + F).shiftRight 29 = (2 ^ 52 + F) / 2 ^ 29 := Nat.shiftRight_eq_div_pow _ _
  rw [hq] at hR1 hR2
  generalize hR : FloatLib.Numerics.roundShiftRightEven (2 ^ 52 + F) 29 = R at *
  have hRlo : 2 ^ 23 ≤ R := by omega
  have hRhi : R ≤ 2 ^ 24 := by omega
  have hmax : FloatFormat.binary32.maxNormalExponent = 127 := by decide
  have hmin : FloatFormat.binary32.minNormalExponent = -126 := by decide
  have hmfe : FloatFormat.binary32.maxFiniteExpField = 254 := by decide
  have hmff : FloatFormat.binary32.maxFiniteFracField = 2 ^ 23 - 1 := by decide
  have hbias : FloatFormat.binary32.exponentBias = 127 := by decide
  have hfw : FloatFormat.binary32.fracWidth = 23 := rfl
  unfold Model.roundDyadicGeneral Model.packRoundedNormal
  simp only [hlog, hmax, hmin, hmfe, hmff, hbias, hfw, Model.pow2_eq_two_pow, Int.ofNat_eq_natCast]
  have hz : (2 ^ 52 + F == 0) = false := by simp
  simp only [hz, Bool.false_eq_true, ↓reduceIte]
  have h1 : ¬ ((52 : Nat) : Int) + ((E : Int) - 1023 - 52) > 127 := by omega
  have h2 : ¬ ((52 : Nat) : Int) + ((E : Int) - 1023 - 52) < -126 := by omega
  have h3 : (23 ≤ 52) := by omega
  simp only [h1, h2, h3, ↓reduceIte, Nat.reduceSub, hR, Nat.reduceAdd]
  by_cases hc : R = 2 ^ 24
  · simp only [hc, ↓reduceIte]
    simp
    rw [ite_eq_right_of_eq_false _ _ (by simp only [eq_iff_iff, iff_false]; omega),
      ite_eq_right_of_eq_false _ _ (by simp only [eq_iff_iff, iff_false]; omega)]
    have h8 : ((E : Int) - 1023 + 1 + 127).toNat = E - 895 := by omega
    rw [h8]
  · have hc' : (R == 2 ^ 24) = false := by simpa using hc
    simp only [hc', hc, ↓reduceIte, h1, Bool.false_eq_true]
    simp
    rw [ite_eq_right_of_eq_false _ _ (by simp only [eq_iff_iff, iff_false]; omega)]
    have h8 : ((E : Int) - 1023 + 127).toNat = E - 896 := by omega
    rw [h8]

/-- `toBinary32` of a double whose result is a normal float, on the bit pattern: the sign, the
exponent rebiased by `1023 - 127 = 896`, the 53-bit significand shifted right by 29 bits and
rounded to nearest even (the carry of a round-up runs into the exponent field). -/
@[inline] def toBinary32Word (b : UInt64) : UInt32 :=
  let sig := (b &&& 0xfffffffffffff) ||| 0x10000000000000
  let q := sig >>> 29
  let r := sig &&& 0x1fffffff
  let up : UInt64 := if 0x10000000 < r || (r == 0x10000000 && (q &&& 1) == 1) then 1 else 0
  (((b >>> 63) <<< 31) + ((((b >>> 52) &&& 0x7ff) - 896) <<< 23) + (q - 0x800000) + up).toUInt32

theorem toBinary32Word_toNat (b : UInt64)
    (hE : 897 ≤ b.toNat / 2 ^ 52 % 2 ^ 11 ∧ b.toNat / 2 ^ 52 % 2 ^ 11 ≤ 1149) :
    (toBinary32Word b).toNat =
      (if 2 ^ 63 ≤ b.toNat then 2 ^ 31 else 0) +
      (b.toNat / 2 ^ 52 % 2 ^ 11 - 896) * 2 ^ 23 +
      (FloatLib.Numerics.roundShiftRightEven (2 ^ 52 + b.toNat % 2 ^ 52) 29 - 2 ^ 23) := by
  have hn := UInt64.toNat_lt b
  have hsig : ((b &&& 0xfffffffffffff) ||| 0x10000000000000).toNat = 2 ^ 52 + b.toNat % 2 ^ 52 := by
    rw [UInt64.toNat_or, UInt64.toNat_and]
    simp only [UInt64.reduceToNat]
    rw [show (4503599627370495 : Nat) = 2 ^ 52 - 1 by norm_num, Nat.and_two_pow_sub_one_eq_mod]
    rw [show (4503599627370496 : Nat) = 2 ^ 52 by norm_num,
      Nat.or_two_pow_eq_add_of_lt (Nat.mod_lt _ (by norm_num))]
    omega
  generalize hsg : (b &&& 0xfffffffffffff) ||| 0x10000000000000 = sig at hsig
  have hq : (sig >>> 29).toNat = (2 ^ 52 + b.toNat % 2 ^ 52) / 2 ^ 29 := by
    rw [UInt64.toNat_shiftRight, hsig]; simp [Nat.shiftRight_eq_div_pow]
  have hr : (sig &&& 0x1fffffff).toNat = (2 ^ 52 + b.toNat % 2 ^ 52) % 2 ^ 29 := by
    rw [UInt64.toNat_and, hsig]; simp only [UInt64.reduceToNat]
    rw [show (536870911 : Nat) = 2 ^ 29 - 1 by norm_num, Nat.and_two_pow_sub_one_eq_mod]
  have hq1 : ((sig >>> 29) &&& 1).toNat = (2 ^ 52 + b.toNat % 2 ^ 52) / 2 ^ 29 % 2 := by
    rw [UInt64.toNat_and, hq]; simp only [UInt64.reduceToNat]
    rw [show (1 : Nat) = 2 ^ 1 - 1 by norm_num, Nat.and_two_pow_sub_one_eq_mod]
  have he : ((b >>> 52) &&& 0x7ff).toNat = b.toNat / 2 ^ 52 % 2 ^ 11 := by
    rw [UInt64.toNat_and, UInt64.toNat_shiftRight]
    simp only [UInt64.reduceToNat, Nat.reduceMod, Nat.shiftRight_eq_div_pow]
    rw [show (2047 : Nat) = 2 ^ 11 - 1 by norm_num, Nat.and_two_pow_sub_one_eq_mod]
  have hs : ((b >>> 63) <<< 31).toNat = (if 2 ^ 63 ≤ b.toNat then 2 ^ 31 else 0) := by
    rw [UInt64.toNat_shiftLeft, UInt64.toNat_shiftRight]
    simp only [UInt64.reduceToNat, Nat.reduceMod, Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq]
    split <;> omega
  rw [CFloat.Conv.roundShiftRightEven_29]
  generalize hv : 2 ^ 52 + b.toNat % 2 ^ 52 = v at *
  have hF : b.toNat % 2 ^ 52 < 2 ^ 52 := Nat.mod_lt _ (by norm_num)
  have hvq : 2 ^ 23 ≤ v / 2 ^ 29 ∧ v / 2 ^ 29 < 2 ^ 24 := by omega
  have hup : (if (0x10000000 < (sig &&& 0x1fffffff) ||
      ((sig &&& 0x1fffffff) == 0x10000000 && ((sig >>> 29) &&& 1) == 1)) = true then (1 : UInt64)
      else 0).toNat =
      (if 2 ^ 28 < v % 2 ^ 29 ∨ (v % 2 ^ 29 = 2 ^ 28 ∧ v / 2 ^ 29 % 2 = 1) then 1 else 0) := by
    have hc : (0x10000000 < (sig &&& 0x1fffffff) ||
        ((sig &&& 0x1fffffff) == 0x10000000 && ((sig >>> 29) &&& 1) == 1)) =
        decide (2 ^ 28 < v % 2 ^ 29 ∨ (v % 2 ^ 29 = 2 ^ 28 ∧ v / 2 ^ 29 % 2 = 1)) := by
      rw [Bool.eq_iff_iff]
      simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq,
        UInt64.lt_iff_toNat_lt, ← UInt64.toNat_inj, hr, hq1, UInt64.reduceToNat, Nat.reducePow]
    rw [hc]
    by_cases hcond : 2 ^ 28 < v % 2 ^ 29 ∨ (v % 2 ^ 29 = 2 ^ 28 ∧ v / 2 ^ 29 % 2 = 1) <;>
      simp only [hcond, decide_true, decide_false, ↓reduceIte, Bool.false_eq_true] <;> rfl
  have hsub : (sig >>> 29 - 0x800000).toNat = v / 2 ^ 29 - 2 ^ 23 := by
    rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le, hq]; simpa using hvq.1), hq]; rfl
  have hexp : ((((b >>> 52) &&& 0x7ff) - 896) <<< 23).toNat = (b.toNat / 2 ^ 52 % 2 ^ 11 - 896) * 2 ^ 23 := by
    rw [UInt64.toNat_shiftLeft, UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le, he]; simp only [UInt64.reduceToNat]; omega), he]
    simp only [UInt64.reduceToNat, Nat.reduceMod, Nat.shiftLeft_eq]
    omega
  simp only [toBinary32Word, UInt64.toNat_toUInt32, UInt64.toNat_add]
  rw [hsg, hup, hsub, hexp, hs]
  split <;> split <;> omega


theorem toBinary32_normal (x : Binary64)
    (hE : 897 ≤ (toBits x).toNat / 2 ^ 52 % 2 ^ 11 ∧ (toBits x).toNat / 2 ^ 52 % 2 ^ 11 ≤ 1149) :
    toBinary32 x = Binary32.ofBits (toBinary32Word (toBits x)) := by
  have hn := UInt64.toNat_lt (toBits x)
  have hc := cast_binary32_model (ExecFloat.Binary.toModel x) (toBits x).toNat rfl hE
  have hw := toBinary32Word_toNat (toBits x) hE
  generalize toBinary32Word (toBits x) = w at hw
  generalize (toBits x).toNat = n at hc hw hE hn
  have hR1 := FloatLib.Numerics.shiftRight_le_roundShiftRightEven (2 ^ 52 + n % 2 ^ 52) 29
  have hR2 := FloatLib.Numerics.roundShiftRightEven_le_shiftRight_add1 (2 ^ 52 + n % 2 ^ 52) 29
  have hq : (2 ^ 52 + n % 2 ^ 52).shiftRight 29 = (2 ^ 52 + n % 2 ^ 52) / 2 ^ 29 :=
    Nat.shiftRight_eq_div_pow _ _
  rw [hq] at hR1 hR2
  have hF : n % 2 ^ 52 < 2 ^ 52 := Nat.mod_lt _ (by norm_num)
  have hsgn : (if 2 ^ 63 ≤ n then 2 ^ 31 else 0) = (if decide (2 ^ 63 ≤ n) then 2 ^ 31 else 0) := by
    simp
  rw [hsgn] at hw
  generalize FloatLib.Numerics.roundShiftRightEven (2 ^ 52 + n % 2 ^ 52) 29 = R at hc hw hR1 hR2
  have hmodel : Model.cast .binary64 .binary32 (ExecFloat.Binary.toModel x) =
      (Model.ofBits (BitVec.ofNat 32 w.toNat) : Model .binary32) := by
    rw [hc, hw]
    by_cases hcar : R = 2 ^ 24
    · simp only [hcar, ↓reduceIte]
      rw [show (if decide (2 ^ 63 ≤ n) = true then 2 ^ 31 else 0) + (n / 2 ^ 52 % 2 ^ 11 - 896) * 2 ^ 23 +
          (2 ^ 24 - 2 ^ 23) = (if decide (2 ^ 63 ≤ n) = true then 2 ^ 31 else 0) +
          (n / 2 ^ 52 % 2 ^ 11 - 895) * 2 ^ 23 + 0 by omega]
      exact (Binary32.ofBits_fields32 _ _ _ (by omega) (by norm_num)).symm
    · simp only [hcar, ↓reduceIte]
      exact (Binary32.ofBits_fields32 _ _ _ (by omega) (by omega)).symm
  have hto : ExecFloat.Binary.toModel (Binary32.ofBits w) =
      (Model.ofBits (BitVec.ofNatLT w.toNat (UInt32.toNat_lt w)) : Model .binary32) := rfl
  have hbv : BitVec.ofNatLT w.toNat (UInt32.toNat_lt w) = BitVec.ofNat 32 w.toNat := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofNatLT, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (UInt32.toNat_lt w)]
  calc toBinary32 x = (ExecFloat.Binary.ofModel (Model.cast .binary64 .binary32
          (ExecFloat.Binary.toModel x)) : Binary32) := rfl
    _ = (ExecFloat.Binary.ofModel (Model.ofBits (BitVec.ofNat 32 w.toNat) : Model .binary32) :
          Binary32) := by rw [hmodel]
    _ = (ExecFloat.Binary.ofModel (ExecFloat.Binary.toModel (Binary32.ofBits w)) : Binary32) := by
          rw [hto]
          exact congrArg (fun b => (ExecFloat.Binary.ofModel (Model.ofBits b : Model .binary32) :
            Binary32)) hbv.symm
    _ = Binary32.ofBits w := ExecFloat.Binary.ofModel_toModel _

/-- `toBinary32` itself, out of line: the path `toBinary32Impl` takes when the result is not a
normal float (or the input a zero). -/
@[noinline] def toBinary32Slow (x : Binary64) : Binary32 :=
  ExecFloat.Binary.ofModel (Model.cast .binary64 .binary32 (ExecFloat.Binary.toModel x))

/-- `toBinary32` on the bit patterns when the result is a normal float (biased exponent of the
double in `[897, 1149]`) and for zeros (`toBinary32_eq_toBinary32Impl`). -/
@[inline] def toBinary32Impl (x : Binary64) : Binary32 :=
  let b := toBits x
  let e := (b >>> 52) &&& 0x7ff
  if 897 ≤ e && e ≤ 1149 then Binary32.ofBits (toBinary32Word b)
  else if (b &&& 0x7fffffffffffffff) == 0 then Binary32.ofBits (b >>> 32).toUInt32
  else toBinary32Slow x

/-- On a zero `toBinary32` keeps the sign (two words, evaluated by the kernel). -/
theorem toBinary32_zero (x : Binary64) (hz : (toBits x &&& 0x7fffffffffffffff) = 0) :
    toBinary32 x = Binary32.ofBits (toBits x >>> 32).toUInt32 := by
  have hand : (toBits x &&& 0x7fffffffffffffff).toNat = (toBits x).toNat % 2 ^ 63 := by
    rw [UInt64.toNat_and]; exact Nat.and_two_pow_sub_one_eq_mod _ 63
  have hn := UInt64.toNat_lt (toBits x)
  rw [hz] at hand
  have h : toBits x = 0 ∨ toBits x = 0x8000000000000000 := by
    simp only [← UInt64.toNat_inj, UInt64.reduceToNat] at hand ⊢; omega
  rw [← ExecFloat.Binary.ofBits64_toBits64 x]
  rcases h with h | h <;> rw [show ExecFloat.Binary.toBits64 x = toBits x from rfl, h] <;> decide

@[csimp] theorem toBinary32_eq_toBinary32Impl : @toBinary32 = @toBinary32Impl := by
  funext x
  rw [toBinary32Impl]
  have he : ((toBits x >>> 52) &&& 0x7ff).toNat = (toBits x).toNat / 2 ^ 52 % 2 ^ 11 := by
    rw [UInt64.toNat_and, UInt64.toNat_shiftRight]
    simp only [UInt64.reduceToNat, Nat.reduceMod, Nat.shiftRight_eq_div_pow]
    rw [show (2047 : Nat) = 2 ^ 11 - 1 by norm_num, Nat.and_two_pow_sub_one_eq_mod]
  by_cases hE : 897 ≤ (toBits x).toNat / 2 ^ 52 % 2 ^ 11 ∧ (toBits x).toNat / 2 ^ 52 % 2 ^ 11 ≤ 1149
  · have hc : (decide ((897 : UInt64) ≤ ((toBits x >>> 52) &&& 0x7ff)) &&
        decide (((toBits x >>> 52) &&& 0x7ff) ≤ (1149 : UInt64))) = true := by
      simp only [Bool.and_eq_true, decide_eq_true_eq, UInt64.le_iff_toNat_le, he, UInt64.reduceToNat]
      exact hE
    simp only [hc, ↓reduceIte]
    exact toBinary32_normal x hE
  · have hc : (decide ((897 : UInt64) ≤ ((toBits x >>> 52) &&& 0x7ff)) &&
        decide (((toBits x >>> 52) &&& 0x7ff) ≤ (1149 : UInt64))) = false := by
      simp only [Bool.and_eq_false_iff, decide_eq_false_iff_not, UInt64.le_iff_toNat_le, he,
        UInt64.reduceToNat]
      omega
    simp only [hc, Bool.false_eq_true, ↓reduceIte]
    by_cases hz : (toBits x &&& 0x7fffffffffffffff) = 0
    · simp only [hz, beq_self_eq_true, ↓reduceIte]
      exact toBinary32_zero x hz
    · have hz' : ((toBits x &&& 0x7fffffffffffffff) == 0) = false := by simpa using hz
      simp only [hz', Bool.false_eq_true, ↓reduceIte]; rfl

end Binary64

/-! Conversions to the integer types: C's `(T)x`, truncation toward zero (see `CFloat.truncSat32`).

To a 32- or 64-bit type the value saturates to the type's range (NaN: 0), as arm64's `fcvtzs`/`fcvtzu`
with a `w` or `x` destination compute. To an 8- or 16-bit type C's conversion is undefined outside
the type's range, and clang on the reference target (arm64, `-O2 -ffp-contract=off -fno-fast-math`)
emits `fcvtzs w` (truncation toward zero, saturation to `int32_t`, NaN: 0) for `int8_t`, `uint8_t`,
`int16_t` and `uint16_t`, from `float` and from `double`, and keeps the low 8 or 16 bits when the
value is stored (`strb`/`strh`): `(uint8_t)-221.0f` stored is 35, `(uint8_t)300.0f` is 44,
`(int16_t)40000.0` is -25536, `(uint8_t)1e12f` is 255 (`INT32_MAX`'s low byte). The narrow
conversions below are that: `toInt32`, then the 32-bit word's low bits (`Int32.toInt8`,
`Int32.toInt16`, then `Int8.toUInt8`/`Int16.toUInt16`, as the translator's integer conversions).
(Used directly in a wider expression without a store, clang may keep the whole `int32_t`, since an
in-range value needs no truncation; no `UInt8` reproduces that.) -/

@[inline] def Binary32.toInt32 (x : Binary32) : Int32 := Int32.ofInt (CFloat.truncSat32 (-2^31) (2^31 - 1) x)
@[inline] def Binary32.toInt64 (x : Binary32) : Int64 := Int64.ofInt (CFloat.truncSat32 (-2^63) (2^63 - 1) x)
@[inline] def Binary32.toInt8 (x : Binary32) : Int8 := (Binary32.toInt32 x).toInt8
@[inline] def Binary32.toInt16 (x : Binary32) : Int16 := (Binary32.toInt32 x).toInt16
@[inline] def Binary32.toUInt8 (x : Binary32) : UInt8 := (Binary32.toInt32 x).toInt8.toUInt8
@[inline] def Binary32.toUInt16 (x : Binary32) : UInt16 := (Binary32.toInt32 x).toInt16.toUInt16
@[inline] def Binary32.toUInt32 (x : Binary32) : UInt32 := UInt32.ofNat (CFloat.truncSat32 0 (2^32 - 1) x).toNat
@[inline] def Binary32.toUInt64 (x : Binary32) : UInt64 := UInt64.ofNat (CFloat.truncSat32 0 (2^64 - 1) x).toNat
@[inline] def Binary32.toUSize (x : Binary32) : USize := USize.ofNat (CFloat.truncSat32 0 (2^64 - 1) x).toNat
@[inline] def Binary64.toInt32 (x : Binary64) : Int32 := Int32.ofInt (CFloat.truncSat64 (-2^31) (2^31 - 1) x)
@[inline] def Binary64.toInt64 (x : Binary64) : Int64 := Int64.ofInt (CFloat.truncSat64 (-2^63) (2^63 - 1) x)
@[inline] def Binary64.toInt8 (x : Binary64) : Int8 := (Binary64.toInt32 x).toInt8
@[inline] def Binary64.toInt16 (x : Binary64) : Int16 := (Binary64.toInt32 x).toInt16
@[inline] def Binary64.toUInt8 (x : Binary64) : UInt8 := (Binary64.toInt32 x).toInt8.toUInt8
@[inline] def Binary64.toUInt16 (x : Binary64) : UInt16 := (Binary64.toInt32 x).toInt16.toUInt16
@[inline] def Binary64.toUInt32 (x : Binary64) : UInt32 := UInt32.ofNat (CFloat.truncSat64 0 (2^32 - 1) x).toNat
@[inline] def Binary64.toUInt64 (x : Binary64) : UInt64 := UInt64.ofNat (CFloat.truncSat64 0 (2^64 - 1) x).toNat
@[inline] def Binary64.toUSize (x : Binary64) : USize := USize.ofNat (CFloat.truncSat64 0 (2^64 - 1) x).toNat

/-! Conversions from the integer types: C's `(float)n` and `(double)n`, rounded to nearest even. -/

@[inline] def Int8.toBinary32 (n : Int8) : Binary32 := CFloat.ofInt32 n.toInt
@[inline] def Int16.toBinary32 (n : Int16) : Binary32 := CFloat.ofInt32 n.toInt
@[inline] def Int32.toBinary32 (n : Int32) : Binary32 := CFloat.ofInt32 n.toInt
@[inline] def Int64.toBinary32 (n : Int64) : Binary32 := CFloat.ofInt32 n.toInt
@[inline] def UInt8.toBinary32 (n : UInt8) : Binary32 := CFloat.ofInt32 n.toNat
@[inline] def UInt16.toBinary32 (n : UInt16) : Binary32 := CFloat.ofInt32 n.toNat
@[inline] def UInt32.toBinary32 (n : UInt32) : Binary32 := CFloat.ofInt32 n.toNat
@[inline] def UInt64.toBinary32 (n : UInt64) : Binary32 := CFloat.ofInt32 n.toNat
@[inline] def USize.toBinary32 (n : USize) : Binary32 := CFloat.ofInt32 n.toNat
@[inline] def Int8.toBinary64 (n : Int8) : Binary64 := CFloat.ofInt64 n.toInt
@[inline] def Int16.toBinary64 (n : Int16) : Binary64 := CFloat.ofInt64 n.toInt
@[inline] def Int32.toBinary64 (n : Int32) : Binary64 := CFloat.ofInt64 n.toInt
@[inline] def Int64.toBinary64 (n : Int64) : Binary64 := CFloat.ofInt64 n.toInt
@[inline] def UInt8.toBinary64 (n : UInt8) : Binary64 := CFloat.ofInt64 n.toNat
@[inline] def UInt16.toBinary64 (n : UInt16) : Binary64 := CFloat.ofInt64 n.toNat
@[inline] def UInt32.toBinary64 (n : UInt32) : Binary64 := CFloat.ofInt64 n.toNat
@[inline] def UInt64.toBinary64 (n : UInt64) : Binary64 := CFloat.ofInt64 n.toNat
@[inline] def USize.toBinary64 (n : USize) : Binary64 := CFloat.ofInt64 n.toNat

/-! ## Integer types to float on the words

`Int64.toBinary64 n` is `CFloat.ofInt64 n.toInt`, and `Int64.toInt` of a value of magnitude `2^31`
or more allocates a big integer (a boxed `Int` is a scalar only below `2^31`). The functions below convert from the integer word itself: the sign and the
magnitude as a `UInt64` (`CFloat.absWord`: `INT64_MIN` gives `2^63`), then `ofMag32`/`ofMag64`; the
`@[csimp]` theorems prove each equal to its wrapper above, so the emitted text (`Int64.toBinary64
x`) is unchanged. -/

namespace CFloat

/-- `|x|` of a 64-bit signed integer as a word (`INT64_MIN` gives `2^63`). -/
@[inline] def absWord (x : Int64) : UInt64 := if x < 0 then 0 - x.toUInt64 else x.toUInt64

theorem absWord_toNat (x : Int64) : (absWord x).toNat = x.toInt.natAbs := by
  have h1 : x.toInt = x.toBitVec.toInt := (Int64.toInt_toBitVec x).symm
  have h2 : x.toUInt64.toNat = x.toBitVec.toNat := by rw [← Int64.toBitVec_toUInt64]; rfl
  have hlt : x.toBitVec.toNat < 2 ^ 64 := x.toBitVec.isLt
  rw [BitVec.toInt_eq_toNat_cond] at h1
  unfold absWord
  split
  · rename_i h
    rw [Int64.lt_iff_toInt_lt, Int64.toInt_zero] at h
    rw [UInt64.toNat_sub, h2]
    simp only [UInt64.reduceToNat]
    split at h1 <;> omega
  · rename_i h
    rw [Int64.lt_iff_toInt_lt, Int64.toInt_zero] at h
    rw [h2]
    split at h1 <;> omega

end CFloat

/-- `Int8.toBinary32` on the word (`Int8.toBinary32_eq_toBinary32Impl`). -/
@[inline] def Int8.toBinary32Impl (x : Int8) : Binary32 := CFloat.ofMag32 (x < 0) (CFloat.absWord x.toInt64)
@[csimp] theorem Int8.toBinary32_eq_toBinary32Impl : @Int8.toBinary32 = @Int8.toBinary32Impl := by
  funext x
  unfold Int8.toBinary32 Int8.toBinary32Impl
  rw [CFloat.ofInt32_eq_ofMag32 x.toInt (CFloat.absWord x.toInt64) (by rw [CFloat.absWord_toNat, Int8.toInt_toInt64]),
    show decide (x.toInt < 0) = decide (x < 0) from
      decide_eq_decide.2 (by rw [Int8.lt_iff_toInt_lt, Int8.toInt_zero])]

/-- `Int16.toBinary32` on the word (`Int16.toBinary32_eq_toBinary32Impl`). -/
@[inline] def Int16.toBinary32Impl (x : Int16) : Binary32 := CFloat.ofMag32 (x < 0) (CFloat.absWord x.toInt64)
@[csimp] theorem Int16.toBinary32_eq_toBinary32Impl : @Int16.toBinary32 = @Int16.toBinary32Impl := by
  funext x
  unfold Int16.toBinary32 Int16.toBinary32Impl
  rw [CFloat.ofInt32_eq_ofMag32 x.toInt (CFloat.absWord x.toInt64) (by rw [CFloat.absWord_toNat, Int16.toInt_toInt64]),
    show decide (x.toInt < 0) = decide (x < 0) from
      decide_eq_decide.2 (by rw [Int16.lt_iff_toInt_lt, Int16.toInt_zero])]

/-- `Int32.toBinary32` on the word (`Int32.toBinary32_eq_toBinary32Impl`). -/
@[inline] def Int32.toBinary32Impl (x : Int32) : Binary32 := CFloat.ofMag32 (x < 0) (CFloat.absWord x.toInt64)
@[csimp] theorem Int32.toBinary32_eq_toBinary32Impl : @Int32.toBinary32 = @Int32.toBinary32Impl := by
  funext x
  unfold Int32.toBinary32 Int32.toBinary32Impl
  rw [CFloat.ofInt32_eq_ofMag32 x.toInt (CFloat.absWord x.toInt64) (by rw [CFloat.absWord_toNat, Int32.toInt_toInt64]),
    show decide (x.toInt < 0) = decide (x < 0) from
      decide_eq_decide.2 (by rw [Int32.lt_iff_toInt_lt, Int32.toInt_zero])]

/-- `Int64.toBinary32` on the word (`Int64.toBinary32_eq_toBinary32Impl`). -/
@[inline] def Int64.toBinary32Impl (x : Int64) : Binary32 := CFloat.ofMag32 (x < 0) (CFloat.absWord x)
@[csimp] theorem Int64.toBinary32_eq_toBinary32Impl : @Int64.toBinary32 = @Int64.toBinary32Impl := by
  funext x
  unfold Int64.toBinary32 Int64.toBinary32Impl
  rw [CFloat.ofInt32_eq_ofMag32 x.toInt (CFloat.absWord x) (CFloat.absWord_toNat x),
    show decide (x.toInt < 0) = decide (x < 0) from
      decide_eq_decide.2 (by rw [Int64.lt_iff_toInt_lt, Int64.toInt_zero])]

/-- `UInt8.toBinary32` on the word (`UInt8.toBinary32_eq_toBinary32Impl`). -/
@[inline] def UInt8.toBinary32Impl (x : UInt8) : Binary32 := CFloat.ofMag32 false x.toUInt64
@[csimp] theorem UInt8.toBinary32_eq_toBinary32Impl : @UInt8.toBinary32 = @UInt8.toBinary32Impl := by
  funext x
  unfold UInt8.toBinary32 UInt8.toBinary32Impl
  rw [CFloat.ofInt32_eq_ofMag32 (x.toNat : Int) x.toUInt64 (by rw [UInt8.toNat_toUInt64]; simp),
    show decide ((x.toNat : Int) < 0) = false from decide_eq_false (by omega)]

/-- `UInt16.toBinary32` on the word (`UInt16.toBinary32_eq_toBinary32Impl`). -/
@[inline] def UInt16.toBinary32Impl (x : UInt16) : Binary32 := CFloat.ofMag32 false x.toUInt64
@[csimp] theorem UInt16.toBinary32_eq_toBinary32Impl : @UInt16.toBinary32 = @UInt16.toBinary32Impl := by
  funext x
  unfold UInt16.toBinary32 UInt16.toBinary32Impl
  rw [CFloat.ofInt32_eq_ofMag32 (x.toNat : Int) x.toUInt64 (by rw [UInt16.toNat_toUInt64]; simp),
    show decide ((x.toNat : Int) < 0) = false from decide_eq_false (by omega)]

/-- `UInt32.toBinary32` on the word (`UInt32.toBinary32_eq_toBinary32Impl`). -/
@[inline] def UInt32.toBinary32Impl (x : UInt32) : Binary32 := CFloat.ofMag32 false x.toUInt64
@[csimp] theorem UInt32.toBinary32_eq_toBinary32Impl : @UInt32.toBinary32 = @UInt32.toBinary32Impl := by
  funext x
  unfold UInt32.toBinary32 UInt32.toBinary32Impl
  rw [CFloat.ofInt32_eq_ofMag32 (x.toNat : Int) x.toUInt64 (by rw [UInt32.toNat_toUInt64]; simp),
    show decide ((x.toNat : Int) < 0) = false from decide_eq_false (by omega)]

/-- `UInt64.toBinary32` on the word (`UInt64.toBinary32_eq_toBinary32Impl`). -/
@[inline] def UInt64.toBinary32Impl (x : UInt64) : Binary32 := CFloat.ofMag32 false x
@[csimp] theorem UInt64.toBinary32_eq_toBinary32Impl : @UInt64.toBinary32 = @UInt64.toBinary32Impl := by
  funext x
  unfold UInt64.toBinary32 UInt64.toBinary32Impl
  rw [CFloat.ofInt32_eq_ofMag32 (x.toNat : Int) x (by simp),
    show decide ((x.toNat : Int) < 0) = false from decide_eq_false (by omega)]

/-- `USize.toBinary32` on the word (`USize.toBinary32_eq_toBinary32Impl`). -/
@[inline] def USize.toBinary32Impl (x : USize) : Binary32 := CFloat.ofMag32 false x.toUInt64
@[csimp] theorem USize.toBinary32_eq_toBinary32Impl : @USize.toBinary32 = @USize.toBinary32Impl := by
  funext x
  unfold USize.toBinary32 USize.toBinary32Impl
  rw [CFloat.ofInt32_eq_ofMag32 (x.toNat : Int) x.toUInt64 (by rw [USize.toNat_toUInt64]; simp),
    show decide ((x.toNat : Int) < 0) = false from decide_eq_false (by omega)]

/-- `Int8.toBinary64` on the word (`Int8.toBinary64_eq_toBinary64Impl`). -/
@[inline] def Int8.toBinary64Impl (x : Int8) : Binary64 := CFloat.ofMag64 (x < 0) (CFloat.absWord x.toInt64)
@[csimp] theorem Int8.toBinary64_eq_toBinary64Impl : @Int8.toBinary64 = @Int8.toBinary64Impl := by
  funext x
  unfold Int8.toBinary64 Int8.toBinary64Impl
  rw [CFloat.ofInt64_eq_ofMag64 x.toInt (CFloat.absWord x.toInt64) (by rw [CFloat.absWord_toNat, Int8.toInt_toInt64]),
    show decide (x.toInt < 0) = decide (x < 0) from
      decide_eq_decide.2 (by rw [Int8.lt_iff_toInt_lt, Int8.toInt_zero])]

/-- `Int16.toBinary64` on the word (`Int16.toBinary64_eq_toBinary64Impl`). -/
@[inline] def Int16.toBinary64Impl (x : Int16) : Binary64 := CFloat.ofMag64 (x < 0) (CFloat.absWord x.toInt64)
@[csimp] theorem Int16.toBinary64_eq_toBinary64Impl : @Int16.toBinary64 = @Int16.toBinary64Impl := by
  funext x
  unfold Int16.toBinary64 Int16.toBinary64Impl
  rw [CFloat.ofInt64_eq_ofMag64 x.toInt (CFloat.absWord x.toInt64) (by rw [CFloat.absWord_toNat, Int16.toInt_toInt64]),
    show decide (x.toInt < 0) = decide (x < 0) from
      decide_eq_decide.2 (by rw [Int16.lt_iff_toInt_lt, Int16.toInt_zero])]

/-- `Int32.toBinary64` on the word (`Int32.toBinary64_eq_toBinary64Impl`). -/
@[inline] def Int32.toBinary64Impl (x : Int32) : Binary64 := CFloat.ofMag64 (x < 0) (CFloat.absWord x.toInt64)
@[csimp] theorem Int32.toBinary64_eq_toBinary64Impl : @Int32.toBinary64 = @Int32.toBinary64Impl := by
  funext x
  unfold Int32.toBinary64 Int32.toBinary64Impl
  rw [CFloat.ofInt64_eq_ofMag64 x.toInt (CFloat.absWord x.toInt64) (by rw [CFloat.absWord_toNat, Int32.toInt_toInt64]),
    show decide (x.toInt < 0) = decide (x < 0) from
      decide_eq_decide.2 (by rw [Int32.lt_iff_toInt_lt, Int32.toInt_zero])]

/-- `Int64.toBinary64` on the word (`Int64.toBinary64_eq_toBinary64Impl`). -/
@[inline] def Int64.toBinary64Impl (x : Int64) : Binary64 := CFloat.ofMag64 (x < 0) (CFloat.absWord x)
@[csimp] theorem Int64.toBinary64_eq_toBinary64Impl : @Int64.toBinary64 = @Int64.toBinary64Impl := by
  funext x
  unfold Int64.toBinary64 Int64.toBinary64Impl
  rw [CFloat.ofInt64_eq_ofMag64 x.toInt (CFloat.absWord x) (CFloat.absWord_toNat x),
    show decide (x.toInt < 0) = decide (x < 0) from
      decide_eq_decide.2 (by rw [Int64.lt_iff_toInt_lt, Int64.toInt_zero])]

/-- `UInt8.toBinary64` on the word (`UInt8.toBinary64_eq_toBinary64Impl`). -/
@[inline] def UInt8.toBinary64Impl (x : UInt8) : Binary64 := CFloat.ofMag64 false x.toUInt64
@[csimp] theorem UInt8.toBinary64_eq_toBinary64Impl : @UInt8.toBinary64 = @UInt8.toBinary64Impl := by
  funext x
  unfold UInt8.toBinary64 UInt8.toBinary64Impl
  rw [CFloat.ofInt64_eq_ofMag64 (x.toNat : Int) x.toUInt64 (by rw [UInt8.toNat_toUInt64]; simp),
    show decide ((x.toNat : Int) < 0) = false from decide_eq_false (by omega)]

/-- `UInt16.toBinary64` on the word (`UInt16.toBinary64_eq_toBinary64Impl`). -/
@[inline] def UInt16.toBinary64Impl (x : UInt16) : Binary64 := CFloat.ofMag64 false x.toUInt64
@[csimp] theorem UInt16.toBinary64_eq_toBinary64Impl : @UInt16.toBinary64 = @UInt16.toBinary64Impl := by
  funext x
  unfold UInt16.toBinary64 UInt16.toBinary64Impl
  rw [CFloat.ofInt64_eq_ofMag64 (x.toNat : Int) x.toUInt64 (by rw [UInt16.toNat_toUInt64]; simp),
    show decide ((x.toNat : Int) < 0) = false from decide_eq_false (by omega)]

/-- `UInt32.toBinary64` on the word (`UInt32.toBinary64_eq_toBinary64Impl`). -/
@[inline] def UInt32.toBinary64Impl (x : UInt32) : Binary64 := CFloat.ofMag64 false x.toUInt64
@[csimp] theorem UInt32.toBinary64_eq_toBinary64Impl : @UInt32.toBinary64 = @UInt32.toBinary64Impl := by
  funext x
  unfold UInt32.toBinary64 UInt32.toBinary64Impl
  rw [CFloat.ofInt64_eq_ofMag64 (x.toNat : Int) x.toUInt64 (by rw [UInt32.toNat_toUInt64]; simp),
    show decide ((x.toNat : Int) < 0) = false from decide_eq_false (by omega)]

/-- `UInt64.toBinary64` on the word (`UInt64.toBinary64_eq_toBinary64Impl`). -/
@[inline] def UInt64.toBinary64Impl (x : UInt64) : Binary64 := CFloat.ofMag64 false x
@[csimp] theorem UInt64.toBinary64_eq_toBinary64Impl : @UInt64.toBinary64 = @UInt64.toBinary64Impl := by
  funext x
  unfold UInt64.toBinary64 UInt64.toBinary64Impl
  rw [CFloat.ofInt64_eq_ofMag64 (x.toNat : Int) x (by simp),
    show decide ((x.toNat : Int) < 0) = false from decide_eq_false (by omega)]

/-- `USize.toBinary64` on the word (`USize.toBinary64_eq_toBinary64Impl`). -/
@[inline] def USize.toBinary64Impl (x : USize) : Binary64 := CFloat.ofMag64 false x.toUInt64
@[csimp] theorem USize.toBinary64_eq_toBinary64Impl : @USize.toBinary64 = @USize.toBinary64Impl := by
  funext x
  unfold USize.toBinary64 USize.toBinary64Impl
  rw [CFloat.ofInt64_eq_ofMag64 (x.toNat : Int) x.toUInt64 (by rw [USize.toNat_toUInt64]; simp),
    show decide ((x.toNat : Int) < 0) = false from decide_eq_false (by omega)]
