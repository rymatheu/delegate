import FloatModel.Float32
import Contracts.Float32Clip
import AP_Math

/-!
# The zero half of the hover, binary32 foundations

The new stack computes every control quantity in `Float32`. At a hover sample the horizontal and
rotational signals are zeros, and the attitudes are the identity quaternion. This file holds what
the module lemmas (`Contracts.CopterZeroMath`, `CopterZeroAtt`, `CopterZeroRate`, `CopterZeroPos`,
`CopterZeroMotors`) share:

- the predicates: `Z x` (finite, value `0`, either sign), `One x` (finite, value `1`), `ZV`, `ZV2`
  for vectors, `ZD` for a binary64 zero, `IdQ q` for the identity quaternion (value `(1, 0, 0, 0)`,
  all four components finite);
- `LibmZero32`, the five C-library facts at zero (C99 Annex F, binary32): `acosf 1 = +0`,
  `sinf ±0 = ±0`, `cosf ±0 = 1`, `atan2f(±0, x > 0) = ±0`, `asinf ±0 = ±0`, stated on values
  (the result is a zero; the sign is not used);
- `ConvZero`, the two conversions between `float` and `double` at zero. They are not libm
  functions: `Float32.toFloat` and `Float.toFloat32` are opaque `extern` constants in core Lean, so
  their behaviour at `±0` (IEEE 754 requires `±0 ↦ ±0`) has to be a hypothesis like the libm facts;
- exactness of `+ - * / sqrt` whenever the exact result is itself a float (`add_exact`, ...,
  from the bracket theorems of `FloatModel.Float32`): sums, differences, products and quotients of
  zeros are zeros, `1 · 1 = 1`, `x + 0 = x`, `x · 1 = x`, ...;
- a few facts at the level of the unpacked model (`Z_unpack`, `add_unpack_of_Z_left`,
  `congr_sqrt`, `congr_div`) and the binary32 values of the literals the hover reaches
  (`FLT_EPSILON = 2⁻²³`, `M_PI`, `GRAVITY_MSS`, ...), computed by the kernel (`rfl`);
- `is_zero`, `is_positive`, `is_negative`, `constrain_float`, `MIN`, `MAX`, `wrap_PI` at zeros.
-/

open Float.Model UnpackedFloat AP_Math

namespace Contracts.CopterZero

/-! ## Predicates -/

/-- A finite binary32 float of value zero (`+0` or `-0`). -/
def Z (x : Float32) : Prop := x.IsFinite ∧ x.toReal = 0

/-- A finite binary32 float of value one. -/
def One (x : Float32) : Prop := x.IsFinite ∧ x.toReal = 1

/-- A finite binary64 float of value zero. -/
def ZD (x : Float) : Prop := x.IsFinite ∧ x.toReal = 0

/-- The zero `Vector3f`. -/
def ZV (v : Vector3f) : Prop := Z v.x ∧ Z v.y ∧ Z v.z

/-- The zero `Vector2f`. -/
def ZV2 (v : Vector2f) : Prop := Z v.x ∧ Z v.y

/-- The zero `Vector2p` (binary64). -/
def ZV2p (v : Vector2p) : Prop := ZD v.x ∧ ZD v.y

/-- The identity quaternion: `q1` of value one, `q2 q3 q4` zeros, all finite. -/
def IdQ (q : Quaternion) : Prop := One q.q1 ∧ Z q.q2 ∧ Z q.q3 ∧ Z q.q4

/-- A finite float. -/
abbrev Fin32 (x : Float32) : Prop := x.IsFinite

/-- A finite `Vector3f`. -/
def FinV (v : Vector3f) : Prop := v.x.IsFinite ∧ v.y.IsFinite ∧ v.z.IsFinite

/-! ## The C library and the conversions -/

/-- The five facts about the binary32 C library at zero that the hover uses (`Float32.acos`,
`sin`, `cos`, `atan2`, `asin` are opaque `extern` constants, `acosf`, `sinf`, `cosf`, `atan2f`,
`asinf`). C99 Annex F (F.9.1.1, F.9.1.2, F.9.1.4, F.9.1.6, F.9.1.5) requires each of them. -/
-- <<LibmZero32>>
structure LibmZero32 : Prop where
  /-- `acosf(1) = +0`. -/
  acos_one : ∀ x : Float32, One x → Z (Float32.acos x)
  /-- `sinf(±0) = ±0`. -/
  sin_zero : ∀ x : Float32, Z x → Z (Float32.sin x)
  /-- `cosf(±0) = 1`. -/
  cos_zero : ∀ x : Float32, Z x → One (Float32.cos x)
  /-- `atan2f(±0, x) = ±0` for `x > 0`. -/
  atan2_zero : ∀ y x : Float32, Z y → x.IsFinite → 0 < x.toReal → Z (Float32.atan2 y x)
  /-- `asinf(±0) = ±0`. -/
  asin_zero : ∀ x : Float32, Z x → Z (Float32.asin x)
-- <</LibmZero32>>

/-- The conversions `(double)x` and `(float)x` at zero (`Float32.toFloat`, `Float.toFloat32` are
opaque `extern` constants). IEEE 754 (5.4.2) requires `±0 ↦ ±0`. Only the positions and the
angles widened by `shape_angle_vel_accel` pass through them on the hover path. -/
-- <<ConvZero>>
structure ConvZero : Prop where
  toFloat_zero : ∀ x : Float32, Z x → ZD x.toFloat
  toFloat32_zero : ∀ x : Float, ZD x → Z x.toFloat32
-- <</ConvZero>>

/-! ## Exactness when the exact result is a float -/

theorem exact_of_bracket {r f : Float32} {y : ℝ} (hy : y = f.toReal)
    (hb : (f.toReal ≤ y → f.toReal ≤ r.toReal) ∧ (y ≤ f.toReal → r.toReal ≤ f.toReal)) :
    r.toReal = f.toReal :=
  le_antisymm (hb.2 hy.le) (hb.1 hy.ge)

theorem add_exact {a b f : Float32} (ha : a.IsFinite) (hb : b.IsFinite) (hf : f.IsFinite)
    (h : a.toReal + b.toReal = f.toReal) : (a + b).IsFinite ∧ (a + b).toReal = f.toReal := by
  have hM : |a.toReal + b.toReal| ≤ maxFinite32 := h ▸ Float32.abs_toReal_le_maxFinite f
  exact ⟨(Float32.add_err_all ha hb hM).1, exact_of_bracket h (Float32.add_bracket ha hb hM hf)⟩

theorem sub_exact {a b f : Float32} (ha : a.IsFinite) (hb : b.IsFinite) (hf : f.IsFinite)
    (h : a.toReal - b.toReal = f.toReal) : (a - b).IsFinite ∧ (a - b).toReal = f.toReal := by
  have hM : |a.toReal - b.toReal| ≤ maxFinite32 := h ▸ Float32.abs_toReal_le_maxFinite f
  exact ⟨(Float32.sub_err_all ha hb hM).1, exact_of_bracket h (Float32.sub_bracket ha hb hM hf)⟩

theorem mul_exact {a b f : Float32} (ha : a.IsFinite) (hb : b.IsFinite) (hf : f.IsFinite)
    (h : a.toReal * b.toReal = f.toReal) : (a * b).IsFinite ∧ (a * b).toReal = f.toReal := by
  have hM : |a.toReal * b.toReal| ≤ maxFinite32 := h ▸ Float32.abs_toReal_le_maxFinite f
  exact ⟨(Float32.mul_err_all ha hb hM).1, exact_of_bracket h (Float32.mul_bracket ha hb hM hf)⟩

theorem div_exact {a b f : Float32} (ha : a.IsFinite) (hb : b.IsFinite) (hb0 : b.toReal ≠ 0)
    (hf : f.IsFinite) (h : a.toReal / b.toReal = f.toReal) :
    (a / b).IsFinite ∧ (a / b).toReal = f.toReal := by
  have hM : |a.toReal / b.toReal| ≤ maxFinite32 := h ▸ Float32.abs_toReal_le_maxFinite f
  exact ⟨(Float32.div_err_all ha hb hb0 hM).1,
    exact_of_bracket h (Float32.div_bracket ha hb hb0 hM hf)⟩

theorem sqrt_exact {a f : Float32} (ha : a.IsFinite) (h0 : 0 ≤ a.toReal) (hf : f.IsFinite)
    (h : Real.sqrt a.toReal = f.toReal) :
    (Float32.sqrt a).IsFinite ∧ (Float32.sqrt a).toReal = f.toReal := by
  have h1 : a.toReal ≤ maxFinite32 := (le_abs_self _).trans (Float32.abs_toReal_le_maxFinite a)
  exact ⟨(Float32.sqrt_err_all ha h0 h1).1, exact_of_bracket h (Float32.sqrt_bracket ha h0 h1 hf)⟩

/-! ## Zeros and ones -/

theorem Z_zero : Z (0 : Float32) := ⟨Float32.isFinite_zero, Float32.toReal_zero⟩

theorem lit0_unpack : (0.0 : Float32).toModel.unpack = .zero .positive := by rfl

/-- The literal `0.0` (an `OfScientific` literal, not `OfNat 0`) is a zero. -/
theorem Z_lit0 : Z (0.0 : Float32) := by
  refine ⟨by rw [Float32.isFinite_iff, lit0_unpack]; rfl, ?_⟩
  rw [Float32.toReal, lit0_unpack]; rfl
theorem One_one : One (1 : Float32) := ⟨Float32.isFinite_one, Float32.toReal_one⟩
theorem Z.fin {x : Float32} (h : Z x) : x.IsFinite := h.1
theorem One.fin {x : Float32} (h : One x) : x.IsFinite := h.1

theorem Z_add {a b : Float32} (ha : Z a) (hb : Z b) : Z (a + b) :=
  add_exact ha.1 hb.1 Float32.isFinite_zero (by rw [ha.2, hb.2]; simp)
theorem Z_sub {a b : Float32} (ha : Z a) (hb : Z b) : Z (a - b) :=
  sub_exact ha.1 hb.1 Float32.isFinite_zero (by rw [ha.2, hb.2]; simp)
theorem Z_mul_left {a b : Float32} (ha : Z a) (hb : b.IsFinite) : Z (a * b) :=
  mul_exact ha.1 hb Float32.isFinite_zero (by rw [ha.2]; simp)
theorem Z_mul_right {a b : Float32} (ha : a.IsFinite) (hb : Z b) : Z (a * b) :=
  mul_exact ha hb.1 Float32.isFinite_zero (by rw [hb.2]; simp)
theorem Z_div {a b : Float32} (ha : Z a) (hb : b.IsFinite) (hb0 : b.toReal ≠ 0) : Z (a / b) :=
  div_exact ha.1 hb hb0 Float32.isFinite_zero (by rw [ha.2]; simp)
theorem Z_sqrt {a : Float32} (ha : Z a) : Z (Float32.sqrt a) :=
  sqrt_exact ha.1 (by rw [ha.2]) Float32.isFinite_zero (by rw [ha.2]; simp)
theorem Z_sq {a : Float32} (ha : Z a) : Z (AP_Math.sq a) := Z_mul_left ha ha.1
theorem Z_neg {a : Float32} (ha : Z a) : Z (-a) :=
  ⟨(Float32.isFinite_neg a).2 ha.1, by rw [Float32.toReal_neg, ha.2, neg_zero]⟩

/-- `a + 0 = a` in value. -/
theorem add_Z_right {a b : Float32} (ha : a.IsFinite) (hb : Z b) :
    (a + b).IsFinite ∧ (a + b).toReal = a.toReal :=
  add_exact ha hb.1 ha (by rw [hb.2, add_zero])
/-- `0 + b = b` in value. -/
theorem add_Z_left {a b : Float32} (ha : Z a) (hb : b.IsFinite) :
    (a + b).IsFinite ∧ (a + b).toReal = b.toReal :=
  add_exact ha.1 hb hb (by rw [ha.2, zero_add])
/-- `a - 0 = a` in value. -/
theorem sub_Z_right {a b : Float32} (ha : a.IsFinite) (hb : Z b) :
    (a - b).IsFinite ∧ (a - b).toReal = a.toReal :=
  sub_exact ha hb.1 ha (by rw [hb.2, sub_zero])
/-- `0 - b = -b` in value. -/
theorem sub_Z_left {a b : Float32} (ha : Z a) (hb : b.IsFinite) :
    (a - b).IsFinite ∧ (a - b).toReal = -b.toReal := by
  have := sub_exact ha.1 hb ((Float32.isFinite_neg b).2 hb) (by rw [ha.2, Float32.toReal_neg]; ring)
  rwa [Float32.toReal_neg] at this
/-- `a * 1 = a` in value. -/
theorem mul_One_right {a b : Float32} (ha : a.IsFinite) (hb : One b) :
    (a * b).IsFinite ∧ (a * b).toReal = a.toReal :=
  mul_exact ha hb.1 ha (by rw [hb.2, mul_one])
/-- `1 * b = b` in value. -/
theorem mul_One_left {a b : Float32} (ha : One a) (hb : b.IsFinite) :
    (a * b).IsFinite ∧ (a * b).toReal = b.toReal :=
  mul_exact ha.1 hb hb (by rw [ha.2, one_mul])
/-- `a / 1 = a` in value. -/
theorem div_One_right {a b : Float32} (ha : a.IsFinite) (hb : One b) :
    (a / b).IsFinite ∧ (a / b).toReal = a.toReal :=
  div_exact ha hb.1 (by rw [hb.2]; norm_num) ha (by rw [hb.2, div_one])

theorem One_mul {a b : Float32} (ha : One a) (hb : One b) : One (a * b) := by
  have := mul_One_left ha hb.1; exact ⟨this.1, this.2.trans hb.2⟩
theorem One_sq {a : Float32} (ha : One a) : One (AP_Math.sq a) := One_mul ha ha
theorem One_add_Z {a b : Float32} (ha : One a) (hb : Z b) : One (a + b) := by
  have := add_Z_right ha.1 hb; exact ⟨this.1, this.2.trans ha.2⟩
theorem One_sub_Z {a b : Float32} (ha : One a) (hb : Z b) : One (a - b) := by
  have := sub_Z_right ha.1 hb; exact ⟨this.1, this.2.trans ha.2⟩
theorem Z_add_One {a b : Float32} (ha : Z a) (hb : One b) : One (a + b) := by
  have := add_Z_left ha hb.1; exact ⟨this.1, this.2.trans hb.2⟩
theorem One_div {a b : Float32} (ha : One a) (hb : One b) : One (a / b) := by
  have := div_One_right ha.1 hb; exact ⟨this.1, this.2.trans ha.2⟩
theorem One_sqrt {a : Float32} (ha : One a) : One (Float32.sqrt a) := by
  have := sqrt_exact ha.1 (by rw [ha.2]; norm_num) Float32.isFinite_one
    (by rw [ha.2, Float32.toReal_one, Real.sqrt_one])
  exact ⟨this.1, this.2.trans Float32.toReal_one⟩

/-- Two floats with the same finiteness and value are interchangeable for `Z`. -/
theorem Z_of_eq {a b : Float32} (h : a.IsFinite ∧ a.toReal = b.toReal) (hb : Z b) : Z a :=
  ⟨h.1, h.2.trans hb.2⟩
theorem One_of_eq {a b : Float32} (h : a.IsFinite ∧ a.toReal = b.toReal) (hb : One b) : One a :=
  ⟨h.1, h.2.trans hb.2⟩

/-! ## `abs` -/

theorem canonicalIn_abs {spec : Format} {u : UnpackedFloat} (h : CanonicalIn spec u) :
    CanonicalIn spec u.abs := by
  cases u <;> simp_all [CanonicalIn, UnpackedFloat.abs]

theorem toModel_abs_unpack (x : Float32) : x.abs.toModel.unpack = x.toModel.unpack.abs :=
  Float32.Model.unpack_pack_of_canonicalIn (canonicalIn_abs x.canonicalIn_unpack)

theorem toReal_abs (x : Float32) : x.abs.toReal = |x.toReal| := by
  rw [Float32.toReal, toModel_abs_unpack, Float32.toReal]
  cases x.toModel.unpack with
  | finite s m e hm =>
    cases s <;> simp [UnpackedFloat.abs, UnpackedFloat.toReal, Sign.apply, abs_mul]
  | _ => simp [UnpackedFloat.abs, UnpackedFloat.toReal]

theorem isFinite_abs (x : Float32) : x.abs.IsFinite ↔ x.IsFinite := by
  rw [Float32.isFinite_iff, Float32.isFinite_iff, toModel_abs_unpack]
  cases x.toModel.unpack <;> simp [UnpackedFloat.abs, UnpackedFloat.isFinite]

theorem Z_abs {a : Float32} (ha : Z a) : Z a.abs :=
  ⟨(isFinite_abs a).2 ha.1, by rw [toReal_abs, ha.2, abs_zero]⟩

/-! ## The unpacked form of a zero -/

theorem Z_unpack {x : Float32} (h : Z x) : ∃ s, x.toModel.unpack = .zero s := by
  obtain ⟨hf, h0⟩ := h
  rw [Float32.isFinite_iff] at hf
  rw [Float32.toReal] at h0
  revert hf h0
  cases x.toModel.unpack with
  | zero s => intro _ _; exact ⟨s, rfl⟩
  | finite s m e hm =>
    intro _ h0
    have : 0 < mag m e := mag_pos hm e
    rw [toReal_finite] at h0
    cases s <;> simp [Sign.toReal] at h0 <;> linarith
  | infinity _ => intro hf; simp [UnpackedFloat.isFinite] at hf
  | notANumber => intro hf; simp [UnpackedFloat.isFinite] at hf

/-- Adding a zero on the left leaves a non-zero float unchanged, bit for bit in the model. -/
theorem add_unpack_of_Z_left {a b : Float32} (ha : Z a) (hb : ∀ s, b.toModel.unpack ≠ .zero s) :
    (a + b).toModel.unpack = b.toModel.unpack := by
  obtain ⟨s, hs⟩ := Z_unpack ha
  have e : (a + b).toModel =
      Float32.Model.pack (UnpackedFloat.add Format.binary32 a.toModel.unpack b.toModel.unpack) :=
    rfl
  rw [e, hs]
  have hc := b.canonicalIn_unpack
  revert hb hc
  cases b.toModel.unpack with
  | zero s' => intro hb; exact absurd rfl (hb s')
  | _ => intro _ hc; simp only [UnpackedFloat.add]; exact Float32.Model.unpack_pack_of_canonicalIn hc

theorem congr_sqrt {a b : Float32} (h : a.toModel.unpack = b.toModel.unpack) :
    (Float32.sqrt a).toModel.unpack = (Float32.sqrt b).toModel.unpack := by
  show (Float32.Model.pack (UnpackedFloat.sqrt Format.binary32 a.toModel.unpack)).unpack =
    (Float32.Model.pack (UnpackedFloat.sqrt Format.binary32 b.toModel.unpack)).unpack
  rw [h]

theorem congr_div {a b c d : Float32} (h1 : a.toModel.unpack = c.toModel.unpack)
    (h2 : b.toModel.unpack = d.toModel.unpack) : (a / b).toModel.unpack = (c / d).toModel.unpack := by
  show (Float32.Model.pack (UnpackedFloat.div Format.binary32 a.toModel.unpack b.toModel.unpack)).unpack =
    (Float32.Model.pack (UnpackedFloat.div Format.binary32 c.toModel.unpack d.toModel.unpack)).unpack
  rw [h1, h2]

theorem fin_toReal_of_unpack {a b : Float32} (h : a.toModel.unpack = b.toModel.unpack) :
    (a.IsFinite ↔ b.IsFinite) ∧ a.toReal = b.toReal := by
  refine ⟨?_, ?_⟩
  · rw [Float32.isFinite_iff, Float32.isFinite_iff, h]
  · rw [Float32.toReal, Float32.toReal, h]

/-! ## Literals -/

/-- A literal whose unpacked form is a positive finite `m · 2^e`. -/
theorem litPos {x : Float32} {m : Nat} {e : Int} {hm : 0 < m}
    (h : x.toModel.unpack = .finite .positive m e hm) : x.IsFinite ∧ x.toReal = (m : ℝ) * 2 ^ e := by
  refine ⟨by rw [Float32.isFinite_iff, h]; rfl, ?_⟩
  rw [Float32.toReal, h]; simp [UnpackedFloat.toReal, Sign.apply]

/-- A literal whose unpacked form is a negative finite `-m · 2^e`. -/
theorem litNeg {x : Float32} {m : Nat} {e : Int} {hm : 0 < m}
    (h : x.toModel.unpack = .finite .negative m e hm) :
    x.IsFinite ∧ x.toReal = -((m : ℝ) * 2 ^ e) := by
  refine ⟨by rw [Float32.isFinite_iff, h]; rfl, ?_⟩
  rw [Float32.toReal, h]; simp [UnpackedFloat.toReal, Sign.apply]

theorem FLT_EPSILON_spec : FLT_EPSILON.IsFinite ∧ FLT_EPSILON.toReal = 2 ^ (-23 : ℤ) := by
  obtain ⟨h1, h2⟩ := litPos (x := FLT_EPSILON) (m := 2 ^ 23) (e := -46) (hm := by decide) rfl
  refine ⟨h1, h2.trans ?_⟩
  push_cast
  rw [show (8388608 : ℝ) = 2 ^ (23 : ℤ) by norm_num, ← zpow_add₀ two_ne_zero]
  norm_num

theorem eps_pos : (0 : ℝ) < 2 ^ (-23 : ℤ) := by positivity
theorem eps_le_one : (2 : ℝ) ^ (-23 : ℤ) ≤ 1 := zpow_le_one_of_nonpos₀ one_le_two (by norm_num)
theorem eps_lt_tenth : (2 : ℝ) ^ (-23 : ℤ) < 1 / 10 := by
  rw [zpow_neg]; norm_num

theorem lit_one : One (1.0 : Float32) := by
  obtain ⟨h1, h2⟩ := litPos (x := (1.0 : Float32)) (m := 8388608) (e := -23) (hm := by decide) rfl
  exact ⟨h1, by rw [h2]; norm_num⟩

theorem lit_neg_one : (-1.0 : Float32).IsFinite ∧ (-1.0 : Float32).toReal = -1 := by
  obtain ⟨h1, h2⟩ := litNeg (x := (-1.0 : Float32)) (m := 8388608) (e := -23) (hm := by decide) rfl
  exact ⟨h1, by rw [h2]; norm_num⟩

theorem lit_two : (2.0 : Float32).IsFinite ∧ (2.0 : Float32).toReal = 2 := by
  obtain ⟨h1, h2⟩ := litPos (x := (2.0 : Float32)) (m := 8388608) (e := -22) (hm := by decide) rfl
  exact ⟨h1, by rw [h2]; norm_num⟩

theorem lit_half : (0.5 : Float32).IsFinite ∧ (0.5 : Float32).toReal = 1 / 2 := by
  obtain ⟨h1, h2⟩ := litPos (x := (0.5 : Float32)) (m := 8388608) (e := -24) (hm := by decide) rfl
  exact ⟨h1, by rw [h2]; norm_num⟩

theorem lit_ten : (10.0 : Float32).IsFinite ∧ (10.0 : Float32).toReal = 10 := by
  obtain ⟨h1, h2⟩ := litPos (x := (10.0 : Float32)) (m := 10485760) (e := -20) (hm := by decide) rfl
  exact ⟨h1, by rw [h2]; norm_num⟩

theorem lit_tenth : (0.1 : Float32).IsFinite ∧ 0 < (0.1 : Float32).toReal ∧
    (0.1 : Float32).toReal < 1 := by
  obtain ⟨h1, h2⟩ := litPos (x := (0.1 : Float32)) (m := 13421773) (e := -27) (hm := by decide) rfl
  refine ⟨h1, ?_, ?_⟩ <;> rw [h2] <;> norm_num

theorem lit_twentieth : (0.05 : Float32).IsFinite ∧ 0 < (0.05 : Float32).toReal := by
  obtain ⟨h1, h2⟩ := litPos (x := (0.05 : Float32)) (m := 13421773) (e := -28) (hm := by decide) rfl
  exact ⟨h1, by rw [h2]; positivity⟩

theorem M_PI_spec : M_PI.IsFinite ∧ 3 < M_PI.toReal ∧ M_PI.toReal < 4 := by
  obtain ⟨h1, h2⟩ := litPos (x := M_PI) (m := 13176795) (e := -22) (hm := by decide) rfl
  refine ⟨h1, ?_, ?_⟩ <;> rw [h2] <;> norm_num

theorem M_2PI_spec : M_2PI.IsFinite ∧ 6 < M_2PI.toReal ∧ M_2PI.toReal < 7 := by
  obtain ⟨h1, h2⟩ := litPos (x := M_2PI) (m := 13176795) (e := -21) (hm := by decide) rfl
  refine ⟨h1, ?_, ?_⟩ <;> rw [h2] <;> norm_num

/-- `GRAVITY_MSS` is `10283018 · 2⁻²⁰ ≈ 9.80665`. -/
theorem GRAVITY_MSS_unpack :
    GRAVITY_MSS.toModel.unpack = .finite .positive 10283018 (-20) (by decide) := by rfl

theorem GRAVITY_MSS_spec : GRAVITY_MSS.IsFinite ∧ 9 < GRAVITY_MSS.toReal ∧
    GRAVITY_MSS.toReal < 10 := by
  obtain ⟨h1, h2⟩ := litPos GRAVITY_MSS_unpack
  refine ⟨h1, ?_, ?_⟩ <;> rw [h2] <;> norm_num

theorem sq_GRAVITY_unpack :
    ((-GRAVITY_MSS) * (-GRAVITY_MSS)).toModel.unpack =
      .finite .positive 12605245 (-17) (by decide) := by rfl

/-- The integer square root inside `sqrtf(GRAVITY_MSS²)`: `⌊√(12605245 · 2²³)⌋ = 10283017`. -/
theorem natSqrt_g : Nat.sqrt 105740459048960 = 10283017 := by
  symm; rw [Nat.eq_sqrt]; constructor <;> norm_num

/-- `sqrtf(GRAVITY_MSS · GRAVITY_MSS) = GRAVITY_MSS` (binary32; the kernel computes everything but
`Nat.sqrt`, which is well-founded recursion and is supplied by `natSqrt_g`). -/
theorem sqrt_sq_GRAVITY :
    (Float32.sqrt ((-GRAVITY_MSS) * (-GRAVITY_MSS))).toModel.unpack = GRAVITY_MSS.toModel.unpack := by
  have key : ∀ n, Nat.sqrt n = if n = 105740459048960 then 10283017 else Nat.sqrt n := by
    intro n; split
    · subst_vars; exact natSqrt_g
    · rfl
  show (Float32.Model.pack (UnpackedFloat.sqrt Format.binary32
    ((-GRAVITY_MSS) * (-GRAVITY_MSS)).toModel.unpack)).unpack = _
  rw [sq_GRAVITY_unpack]
  simp only [UnpackedFloat.sqrt, UnpackedFloat.sqrtCore]
  rw [key]
  rfl

/-- `-GRAVITY_MSS / GRAVITY_MSS = -1` (binary32). -/
theorem neg_g_div_g :
    ((-GRAVITY_MSS) / GRAVITY_MSS).toModel.unpack = (-1.0 : Float32).toModel.unpack := by rfl



/-! ## Order at zeros -/

theorem lt_iff {a b : Float32} (ha : a.IsFinite) (hb : b.IsFinite) : a < b ↔ a.toReal < b.toReal :=
  Float32.lt_iff_toReal_lt ha hb
theorem le_iff {a b : Float32} (ha : a.IsFinite) (hb : b.IsFinite) : a ≤ b ↔ a.toReal ≤ b.toReal :=
  Float32.le_iff_toReal_le ha hb

/-! ## `is_zero`, `is_positive`, `is_negative` -/

theorem is_zero_Z {x : Float32} (hx : Z x) : is_zero x = true := by
  unfold is_zero
  have ha := Z_abs hx
  rw [decide_eq_true_iff, lt_iff ha.1 FLT_EPSILON_spec.1, ha.2, FLT_EPSILON_spec.2]
  exact eps_pos

/-- `is_zero x` is false when `|x| ≥ 2⁻²³`. -/
theorem is_zero_false {x : Float32} (hx : x.IsFinite) (h : 2 ^ (-23 : ℤ) ≤ |x.toReal|) :
    is_zero x = false := by
  unfold is_zero
  rw [decide_eq_false_iff_not, lt_iff ((isFinite_abs x).2 hx) FLT_EPSILON_spec.1, toReal_abs,
    FLT_EPSILON_spec.2]
  exact not_lt.2 h

theorem is_zero_One {x : Float32} (hx : One x) : is_zero x = false :=
  is_zero_false hx.1 (by rw [hx.2, abs_one]; exact eps_le_one)

theorem is_positive_Z {x : Float32} (hx : Z x) : is_positive x = false := by
  unfold is_positive
  rw [decide_eq_false_iff_not, ge_iff_le, le_iff FLT_EPSILON_spec.1 hx.1, hx.2, FLT_EPSILON_spec.2]
  exact not_le.2 eps_pos

/-- A finite `x` with `is_positive x` has `x ≥ 2⁻²³`. -/
theorem is_positive_ge {x : Float32} (hx : x.IsFinite) (h : is_positive x = true) :
    2 ^ (-23 : ℤ) ≤ x.toReal := by
  unfold is_positive at h
  rw [decide_eq_true_iff, ge_iff_le, le_iff FLT_EPSILON_spec.1 hx, FLT_EPSILON_spec.2] at h
  exact h

theorem is_positive_of_ge {x : Float32} (hx : x.IsFinite) (h : 2 ^ (-23 : ℤ) ≤ x.toReal) :
    is_positive x = true := by
  unfold is_positive
  rw [decide_eq_true_iff, ge_iff_le, le_iff FLT_EPSILON_spec.1 hx, FLT_EPSILON_spec.2]
  exact h

theorem neg_eps_spec : (-1.0 * FLT_EPSILON).IsFinite ∧
    (-1.0 * FLT_EPSILON).toReal = -2 ^ (-23 : ℤ) := by
  have h := mul_exact lit_neg_one.1 FLT_EPSILON_spec.1
    ((Float32.isFinite_neg _).2 FLT_EPSILON_spec.1)
    (by rw [lit_neg_one.2, Float32.toReal_neg]; ring)
  rw [Float32.toReal_neg, FLT_EPSILON_spec.2] at h
  exact h

theorem is_negative_Z {x : Float32} (hx : Z x) : is_negative x = false := by
  unfold is_negative
  rw [decide_eq_false_iff_not, le_iff hx.1 neg_eps_spec.1, hx.2, neg_eps_spec.2]
  exact not_le.2 (by linarith [eps_pos])

/-- A finite `x` with `is_negative x` has `x ≤ -2⁻²³`. -/
theorem is_negative_le {x : Float32} (hx : x.IsFinite) (h : is_negative x = true) :
    x.toReal ≤ -2 ^ (-23 : ℤ) := by
  unfold is_negative at h
  rw [decide_eq_true_iff, le_iff hx neg_eps_spec.1, neg_eps_spec.2] at h
  exact h

/-- A finite `x` with `is_negative x = false` and `is_zero x = false` has `x ≥ 2⁻²³`. -/
theorem pos_of_not_neg_not_zero {x : Float32} (hx : x.IsFinite) (h1 : is_negative x = false)
    (h2 : is_zero x = false) : 2 ^ (-23 : ℤ) ≤ x.toReal := by
  unfold is_negative at h1
  unfold is_zero at h2
  rw [decide_eq_false_iff_not, le_iff hx neg_eps_spec.1, neg_eps_spec.2] at h1
  rw [decide_eq_false_iff_not, lt_iff ((isFinite_abs x).2 hx) FLT_EPSILON_spec.1, toReal_abs,
    FLT_EPSILON_spec.2] at h2
  rcases le_or_gt 0 x.toReal with h | h
  · rw [abs_of_nonneg h] at h2; linarith
  · rw [abs_of_neg h] at h2; linarith

/-! ## `constrain_float`, `MIN`, `MAX` -/

theorem constrain_float_eq (amt low high : Float32) :
    AP_Math.constrain_float amt low high = Contracts.Float32Clip.constrain_float amt low high := rfl

/-- A zero clamped between bounds of opposite signs is a zero. -/
theorem constrain_Z {a lo hi : Float32} (ha : Z a) (hlo : lo.IsFinite) (hhi : hi.IsFinite)
    (h0 : lo.toReal ≤ 0) (h1 : 0 ≤ hi.toReal) : Z (AP_Math.constrain_float a lo hi) := by
  rw [constrain_float_eq]
  have hle : lo.toReal ≤ hi.toReal := le_trans h0 h1
  refine ⟨(Contracts.Float32Clip.constrain_float_spec_of_not_isNaN hlo hhi hle
    (Contracts.Float32Clip.not_isNaN_of_isFinite ha.1)).1, ?_⟩
  rw [Contracts.Float32Clip.constrain_float_toReal hlo hhi hle ha.1, ha.2,
    min_eq_right h1, max_eq_right h0]

/-- `constrain_float` of a value inside `[lo, hi]` keeps it. -/
theorem constrain_in {a lo hi : Float32} (ha : a.IsFinite) (hlo : lo.IsFinite) (hhi : hi.IsFinite)
    (h0 : lo.toReal ≤ a.toReal) (h1 : a.toReal ≤ hi.toReal) :
    (AP_Math.constrain_float a lo hi).IsFinite ∧ (AP_Math.constrain_float a lo hi).toReal = a.toReal := by
  rw [constrain_float_eq]
  have hle : lo.toReal ≤ hi.toReal := le_trans h0 h1
  refine ⟨(Contracts.Float32Clip.constrain_float_spec_of_not_isNaN hlo hhi hle
    (Contracts.Float32Clip.not_isNaN_of_isFinite ha)).1, ?_⟩
  rw [Contracts.Float32Clip.constrain_float_toReal hlo hhi hle ha, min_eq_right h1, max_eq_right h0]

/-- `constrain_float` of a finite value above `hi` is `hi`'s value. -/
theorem constrain_above {a lo hi : Float32} (ha : a.IsFinite) (hlo : lo.IsFinite) (hhi : hi.IsFinite)
    (hle : lo.toReal ≤ hi.toReal) (h1 : hi.toReal ≤ a.toReal) :
    (AP_Math.constrain_float a lo hi).IsFinite ∧ (AP_Math.constrain_float a lo hi).toReal = hi.toReal := by
  rw [constrain_float_eq]
  refine ⟨(Contracts.Float32Clip.constrain_float_spec_of_not_isNaN hlo hhi hle
    (Contracts.Float32Clip.not_isNaN_of_isFinite ha)).1, ?_⟩
  rw [Contracts.Float32Clip.constrain_float_toReal hlo hhi hle ha, min_eq_left h1, max_eq_right hle]

theorem MIN_eq (a b : Float32) : MIN a b = if a < b then a else b := rfl
theorem MAX_eq (a b : Float32) : MAX a b = if a > b then a else b := rfl

/-! ## `wrap_PI` at a zero -/

theorem isNaN_false {x : Float32} (hx : x.IsFinite) : x.isNaN = false := by
  have := Contracts.Float32Clip.not_isNaN_of_isFinite hx
  simpa using this

theorem isInf_false {x : Float32} (hx : x.IsFinite) : x.isInf = false := by
  rw [Float32.isFinite_iff] at hx
  show x.toModel.isInf = false
  show x.toModel.unpack.isInf = false
  cases h : x.toModel.unpack <;> simp_all [UnpackedFloat.isFinite, UnpackedFloat.isInf]

theorem beq_false {a b : Float32} (ha : a.IsFinite) (hb : b.IsFinite) (h : a.toReal ≠ b.toReal) :
    (a == b) = false := by
  cases hab : (a == b)
  · rfl
  · exact absurd ((Float32.beq_iff_toReal_eq ha hb).1 hab) h

/-- `fmodf(±0, 2π) = ±0`: `|x| < |2π|` returns `x`. -/
theorem fmodf_Z {x : Float32} (hx : Z x) : fmodf x M_2PI = x := by
  obtain ⟨h2f, h2lo, -⟩ := M_2PI_spec
  unfold fmodf
  rw [isNaN_false hx.1, isNaN_false h2f, isInf_false hx.1,
    beq_false h2f Float32.isFinite_zero (by rw [Float32.toReal_zero]; linarith)]
  simp only [Bool.or_false, Bool.false_eq_true, if_false]
  rw [isInf_false h2f]
  simp only [Bool.false_eq_true, if_false]
  have hlt : x.abs < M_2PI.abs := by
    rw [lt_iff ((isFinite_abs x).2 hx.1) ((isFinite_abs _).2 h2f), toReal_abs, toReal_abs, hx.2,
      abs_zero, abs_of_pos (by linarith)]
    linarith
  rw [if_pos hlt]

/-- `wrap_PI(±0) = ±0`. -/
theorem wrap_PI_Z {x : Float32} (hx : Z x) : wrap_PI x = x := by
  obtain ⟨hpf, hplo, -⟩ := M_PI_spec
  unfold wrap_PI wrap_2PI
  simp only
  rw [fmodf_Z hx]
  have h1 : ¬ x < 0 := by
    rw [lt_iff hx.1 Float32.isFinite_zero, hx.2, Float32.toReal_zero]; exact lt_irrefl 0
  have h2 : ¬ x > M_PI := by
    show ¬ M_PI < x
    rw [lt_iff hpf hx.1, hx.2]; linarith
  rw [if_neg h1, if_neg h2]

/-! ## Binary64 zeros -/

theorem ZD_zero : ZD (0 : Float) := ⟨Float.isFinite_zero, Float.toReal_zero⟩

theorem add_exact_d {a b f : Float} (ha : a.IsFinite) (hb : b.IsFinite) (hf : f.IsFinite)
    (h : a.toReal + b.toReal = f.toReal) : (a + b).IsFinite ∧ (a + b).toReal = f.toReal := by
  have hM : |a.toReal + b.toReal| ≤ maxFinite := h ▸ Float.abs_toReal_le_maxFinite f
  refine ⟨(Float.add_err_all ha hb hM).1, ?_⟩
  have hb' := Float.add_bracket ha hb hM hf
  exact le_antisymm (hb'.2 h.le) (hb'.1 h.ge)

theorem sub_exact_d {a b f : Float} (ha : a.IsFinite) (hb : b.IsFinite) (hf : f.IsFinite)
    (h : a.toReal - b.toReal = f.toReal) : (a - b).IsFinite ∧ (a - b).toReal = f.toReal := by
  have hM : |a.toReal - b.toReal| ≤ maxFinite := h ▸ Float.abs_toReal_le_maxFinite f
  refine ⟨(Float.sub_err_all ha hb hM).1, ?_⟩
  have hb' := Float.sub_bracket ha hb hM hf
  exact le_antisymm (hb'.2 h.le) (hb'.1 h.ge)

theorem ZD_add {a b : Float} (ha : ZD a) (hb : ZD b) : ZD (a + b) :=
  add_exact_d ha.1 hb.1 Float.isFinite_zero (by rw [ha.2, hb.2, Float.toReal_zero]; simp)
theorem ZD_sub {a b : Float} (ha : ZD a) (hb : ZD b) : ZD (a - b) :=
  sub_exact_d ha.1 hb.1 Float.isFinite_zero (by rw [ha.2, hb.2, Float.toReal_zero]; simp)
theorem add_ZD_right {a b : Float} (ha : a.IsFinite) (hb : ZD b) :
    (a + b).IsFinite ∧ (a + b).toReal = a.toReal :=
  add_exact_d ha hb.1 ha (by rw [hb.2, add_zero])
/-- The difference of two finite doubles of the same value is a zero. -/
theorem ZD_sub_eq {a b : Float} (ha : a.IsFinite) (hb : b.IsFinite) (h : a.toReal = b.toReal) :
    ZD (a - b) :=
  sub_exact_d ha hb Float.isFinite_zero (by rw [h, sub_self, Float.toReal_zero])

/-! ## Vectors -/

theorem ZV_zero_lit : ZV (⟨0, 0, 0⟩ : Vector3f) := ⟨Z_zero, Z_zero, Z_zero⟩
theorem ZV2_zero_lit : ZV2 (⟨0, 0⟩ : Vector2f) := ⟨Z_zero, Z_zero⟩

theorem ZV2_add {a b : Vector2f} (ha : ZV2 a) (hb : ZV2 b) : ZV2 (a + b) :=
  ⟨Z_add ha.1 hb.1, Z_add ha.2 hb.2⟩
theorem ZV2_sub {a b : Vector2f} (ha : ZV2 a) (hb : ZV2 b) : ZV2 (a - b) :=
  ⟨Z_sub ha.1 hb.1, Z_sub ha.2 hb.2⟩
theorem ZV2_mul {a : Vector2f} {k : Float32} (ha : ZV2 a) (hk : k.IsFinite) : ZV2 (a * k) :=
  ⟨Z_mul_left ha.1 hk, Z_mul_left ha.2 hk⟩
theorem ZV2_div {a : Vector2f} {k : Float32} (ha : ZV2 a) (hk : k.IsFinite) (hk0 : k.toReal ≠ 0) :
    ZV2 (a / k) :=
  ⟨Z_div ha.1 hk hk0, Z_div ha.2 hk hk0⟩
theorem ZV_add {a b : Vector3f} (ha : ZV a) (hb : ZV b) : ZV (a + b) :=
  ⟨Z_add ha.1 hb.1, Z_add ha.2.1 hb.2.1, Z_add ha.2.2 hb.2.2⟩
theorem ZV_mul {a : Vector3f} {k : Float32} (ha : ZV a) (hk : k.IsFinite) : ZV (a * k) :=
  ⟨Z_mul_left ha.1 hk, Z_mul_left ha.2.1 hk, Z_mul_left ha.2.2 hk⟩

theorem norm_Z {x y : Float32} (hx : Z x) (hy : Z y) : Z (norm x y) :=
  Z_sqrt (Z_add (Z_mul_left hx hx.1) (Z_mul_left hy hy.1))

theorem norm3_Z {x y z : Float32} (hx : Z x) (hy : Z y) (hz : Z z) : Z (norm3 x y z) :=
  Z_sqrt (Z_add (Z_add (Z_mul_left hx hx.1) (Z_mul_left hy hy.1)) (Z_mul_left hz hz.1))

theorem ZV2_length {v : Vector2f} (hv : ZV2 v) : Z v.length := norm_Z hv.1 hv.2
theorem ZV_length {v : Vector3f} (hv : ZV v) : Z v.length := norm3_Z hv.1 hv.2.1 hv.2.2

theorem ZV2_is_zero {v : Vector2f} (hv : ZV2 v) : v.is_zero = true := by
  simp [Vector2f.is_zero, is_zero_Z hv.1, is_zero_Z hv.2]

/-- `limit_length` of a zero vector leaves it (its length is not positive). -/
theorem ZV2_limit_length {v : Vector2f} (hv : ZV2 v) (m : Float32) : (v.limit_length m).1 = v := by
  unfold Vector2f.limit_length
  simp [is_positive_Z (ZV2_length hv)]

theorem ZV2_limit_length_snd {v : Vector2f} (hv : ZV2 v) (m : Float32) :
    (v.limit_length m).2 = false := by
  unfold Vector2f.limit_length
  simp [is_positive_Z (ZV2_length hv)]

end Contracts.CopterZero
