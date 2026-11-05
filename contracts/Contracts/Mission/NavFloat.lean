import Contracts.Mission.Spec

/-!
# Float lemmas for the navigator proofs

* the literals the navigator and the position controller compute with, as reals (`f32_toReal_…`,
  by evaluating Lean's float model);
* `fabsf` (`Float32.abs`, defined through the model);
* `A32 x r e` / `A64 x r e`: the float `x` is finite and within `e` of the real `r`, with one lemma
  per rounded operation (`+ - * / sqrt`, the conversions), from the rounding bounds of `FloatModel`
  and, for the opaque conversions, `LibmSpec`.
-/

namespace Contracts.Mission

open Float.Model UnpackedFloat

noncomputable section

/-- `pure` of `Id` is the value. -/
@[simp] theorem id_pure_eq {α : Type} (a : α) : (pure a : Id α) = a := rfl

/-- `bind` of `Id` is application. -/
@[simp] theorem id_bind_eq {α β : Type} (x : Id α) (f : α → Id β) : x >>= f = f x := rfl

/-- `Id.run` is the identity. -/
@[simp] theorem id_run_eq {α : Type} (a : Id α) : Id.run a = a := rfl

/-! ## Literals -/

theorem f32_unpack_1p5 : (1.5 : Float32).toModel.unpack = .finite .positive 12582912 (-23) (by decide) := by rfl
theorem f32_toReal_1p5 : (1.5 : Float32).toReal = (3 / 2 : ℝ) := by
  rw [Float32.toReal, f32_unpack_1p5]; simp [UnpackedFloat.toReal, Sign.apply]; norm_num
theorem f32_isFinite_1p5 : (1.5 : Float32).IsFinite := by
  rw [Float32.isFinite_iff, f32_unpack_1p5]; rfl

theorem f32_unpack_1p1920929Em7 : (1.1920929e-7 : Float32).toModel.unpack = .finite .positive 8388608 (-46) (by decide) := by rfl
theorem f32_toReal_1p1920929Em7 : (1.1920929e-7 : Float32).toReal = (1 / 8388608 : ℝ) := by
  rw [Float32.toReal, f32_unpack_1p1920929Em7]; simp [UnpackedFloat.toReal, Sign.apply]; norm_num
theorem f32_isFinite_1p1920929Em7 : (1.1920929e-7 : Float32).IsFinite := by
  rw [Float32.isFinite_iff, f32_unpack_1p1920929Em7]; rfl

theorem f32_unpack_1p0 : (1.0 : Float32).toModel.unpack = .finite .positive 8388608 (-23) (by decide) := by rfl
theorem f32_toReal_1p0 : (1.0 : Float32).toReal = (1 : ℝ) := by
  rw [Float32.toReal, f32_unpack_1p0]; simp [UnpackedFloat.toReal, Sign.apply]; norm_num
theorem f32_isFinite_1p0 : (1.0 : Float32).IsFinite := by
  rw [Float32.isFinite_iff, f32_unpack_1p0]; rfl

theorem f32_unpack_2p0 : (2.0 : Float32).toModel.unpack = .finite .positive 8388608 (-22) (by decide) := by rfl
theorem f32_toReal_2p0 : (2.0 : Float32).toReal = (2 : ℝ) := by
  rw [Float32.toReal, f32_unpack_2p0]; simp [UnpackedFloat.toReal, Sign.apply]; norm_num
theorem f32_isFinite_2p0 : (2.0 : Float32).IsFinite := by
  rw [Float32.isFinite_iff, f32_unpack_2p0]; rfl

theorem f32_unpack_0p5 : (0.5 : Float32).toModel.unpack = .finite .positive 8388608 (-24) (by decide) := by rfl
theorem f32_toReal_0p5 : (0.5 : Float32).toReal = (1 / 2 : ℝ) := by
  rw [Float32.toReal, f32_unpack_0p5]; simp [UnpackedFloat.toReal, Sign.apply]; norm_num
theorem f32_isFinite_0p5 : (0.5 : Float32).IsFinite := by
  rw [Float32.isFinite_iff, f32_unpack_0p5]; rfl

theorem f32_unpack_3p0 : (3.0 : Float32).toModel.unpack = .finite .positive 12582912 (-22) (by decide) := by rfl
theorem f32_toReal_3p0 : (3.0 : Float32).toReal = (3 : ℝ) := by
  rw [Float32.toReal, f32_unpack_3p0]; simp [UnpackedFloat.toReal, Sign.apply]; norm_num
theorem f32_isFinite_3p0 : (3.0 : Float32).IsFinite := by
  rw [Float32.isFinite_iff, f32_unpack_3p0]; rfl

theorem f32_unpack_1800p0 : (1800.0 : Float32).toModel.unpack = .finite .positive 14745600 (-13) (by decide) := by rfl
theorem f32_toReal_1800p0 : (1800.0 : Float32).toReal = (1800 : ℝ) := by
  rw [Float32.toReal, f32_unpack_1800p0]; simp [UnpackedFloat.toReal, Sign.apply]; norm_num
theorem f32_isFinite_1800p0 : (1800.0 : Float32).IsFinite := by
  rw [Float32.isFinite_iff, f32_unpack_1800p0]; rfl

theorem f32_unpack_0p05 : (0.05 : Float32).toModel.unpack = .finite .positive 13421773 (-28) (by decide) := by rfl
theorem f32_toReal_0p05 : (0.05 : Float32).toReal = (13421773 / 268435456 : ℝ) := by
  rw [Float32.toReal, f32_unpack_0p05]; simp [UnpackedFloat.toReal, Sign.apply]; norm_num
theorem f32_isFinite_0p05 : (0.05 : Float32).IsFinite := by
  rw [Float32.isFinite_iff, f32_unpack_0p05]; rfl

theorem f32_unpack_0p1 : (0.1 : Float32).toModel.unpack = .finite .positive 13421773 (-27) (by decide) := by rfl
theorem f32_toReal_0p1 : (0.1 : Float32).toReal = (13421773 / 134217728 : ℝ) := by
  rw [Float32.toReal, f32_unpack_0p1]; simp [UnpackedFloat.toReal, Sign.apply]; norm_num
theorem f32_isFinite_0p1 : (0.1 : Float32).IsFinite := by
  rw [Float32.isFinite_iff, f32_unpack_0p1]; rfl

theorem f32_unpack_5p0 : (5.0 : Float32).toModel.unpack = .finite .positive 10485760 (-21) (by decide) := by rfl
theorem f32_toReal_5p0 : (5.0 : Float32).toReal = (5 : ℝ) := by
  rw [Float32.toReal, f32_unpack_5p0]; simp [UnpackedFloat.toReal, Sign.apply]; norm_num
theorem f32_isFinite_5p0 : (5.0 : Float32).IsFinite := by
  rw [Float32.isFinite_iff, f32_unpack_5p0]; rfl

theorem f32_unpack_2p5 : (2.5 : Float32).toModel.unpack = .finite .positive 10485760 (-22) (by decide) := by rfl
theorem f32_toReal_2p5 : (2.5 : Float32).toReal = (5 / 2 : ℝ) := by
  rw [Float32.toReal, f32_unpack_2p5]; simp [UnpackedFloat.toReal, Sign.apply]; norm_num
theorem f32_isFinite_2p5 : (2.5 : Float32).IsFinite := by
  rw [Float32.isFinite_iff, f32_unpack_2p5]; rfl

theorem f32_unpack_10p0 : (10.0 : Float32).toModel.unpack = .finite .positive 10485760 (-20) (by decide) := by rfl
theorem f32_toReal_10p0 : (10.0 : Float32).toReal = (10 : ℝ) := by
  rw [Float32.toReal, f32_unpack_10p0]; simp [UnpackedFloat.toReal, Sign.apply]; norm_num
theorem f32_isFinite_10p0 : (10.0 : Float32).IsFinite := by
  rw [Float32.isFinite_iff, f32_unpack_10p0]; rfl

theorem f32_unpack_m3p0 : (-3.0 : Float32).toModel.unpack = .finite .negative 12582912 (-22) (by decide) := by rfl
theorem f32_toReal_m3p0 : (-3.0 : Float32).toReal = (-3 : ℝ) := by
  rw [Float32.toReal, f32_unpack_m3p0]; simp [UnpackedFloat.toReal, Sign.apply]; norm_num
theorem f32_isFinite_m3p0 : (-3.0 : Float32).IsFinite := by
  rw [Float32.isFinite_iff, f32_unpack_m3p0]; rfl

theorem f64_unpack_2p0 : (2.0 : Float).toModel.unpack = .finite .positive 4503599627370496 (-51) (by decide) := by rfl
theorem f64_toReal_2p0 : (2.0 : Float).toReal = (2 : ℝ) := by
  rw [Float.toReal, f64_unpack_2p0]; simp [UnpackedFloat.toReal, Sign.apply]; norm_num
theorem f64_isFinite_2p0 : (2.0 : Float).IsFinite := by
  rw [Float.isFinite_iff, f64_unpack_2p0]; rfl

theorem f64_unpack_1p0 : (1.0 : Float).toModel.unpack = .finite .positive 4503599627370496 (-52) (by decide) := by rfl
theorem f64_toReal_1p0 : (1.0 : Float).toReal = (1 : ℝ) := by
  rw [Float.toReal, f64_unpack_1p0]; simp [UnpackedFloat.toReal, Sign.apply]; norm_num
theorem f64_isFinite_1p0 : (1.0 : Float).IsFinite := by
  rw [Float.isFinite_iff, f64_unpack_1p0]; rfl

theorem f64_unpack_0p5 : (0.5 : Float).toModel.unpack = .finite .positive 4503599627370496 (-53) (by decide) := by rfl
theorem f64_toReal_0p5 : (0.5 : Float).toReal = (1 / 2 : ℝ) := by
  rw [Float.toReal, f64_unpack_0p5]; simp [UnpackedFloat.toReal, Sign.apply]; norm_num
theorem f64_isFinite_0p5 : (0.5 : Float).IsFinite := by
  rw [Float.isFinite_iff, f64_unpack_0p5]; rfl


theorem f32_toReal_0p0 : (0.0 : Float32).toReal = 0 := by
  rw [Float32.toReal, show (0.0 : Float32).toModel.unpack = .zero .positive from rfl]
  simp [UnpackedFloat.toReal]
theorem f32_isFinite_0p0 : (0.0 : Float32).IsFinite := by
  rw [Float32.isFinite_iff, show (0.0 : Float32).toModel.unpack = .zero .positive from rfl]; rfl
theorem f64_toReal_0p0 : (0.0 : Float).toReal = 0 := by
  rw [Float.toReal, show (0.0 : Float).toModel.unpack = .zero .positive from rfl]
  simp [UnpackedFloat.toReal]
theorem f64_isFinite_0p0 : (0.0 : Float).IsFinite := by
  rw [Float.isFinite_iff, show (0.0 : Float).toModel.unpack = .zero .positive from rfl]; rfl

/-! ## `fabsf` -/

theorem Float32.toModel_abs_unpack (a : Float32) :
    (Float32.abs a).toModel.unpack = a.toModel.unpack.abs := by
  have hc := a.canonicalIn_unpack
  have : CanonicalIn Format.binary32 a.toModel.unpack.abs := by
    cases h : a.toModel.unpack <;> simp_all [CanonicalIn, UnpackedFloat.abs]
  exact Float32.Model.unpack_pack_of_canonicalIn this

theorem Float32.toReal_abs (a : Float32) : (Float32.abs a).toReal = |a.toReal| := by
  rw [Float32.toReal, Float32.toModel_abs_unpack, Float32.toReal]
  cases a.toModel.unpack with
  | finite s m e hm =>
    cases s <;> simp [UnpackedFloat.abs, UnpackedFloat.toReal, Sign.apply, abs_mul]
  | _ => simp [UnpackedFloat.abs, UnpackedFloat.toReal]

theorem Float32.isFinite_abs (a : Float32) : (Float32.abs a).IsFinite ↔ a.IsFinite := by
  rw [Float32.isFinite_iff, Float32.isFinite_iff, Float32.toModel_abs_unpack]
  cases a.toModel.unpack <;> simp [UnpackedFloat.abs, UnpackedFloat.isFinite]

/-! ## Approximations -/

/-- The `float` `x` is finite and within `e` of `r`. -/
def A32 (x : Float32) (r e : ℝ) : Prop := x.IsFinite ∧ |x.toReal - r| ≤ e

/-- The `double` `x` is finite and within `e` of `r`. -/
def A64 (x : Float) (r e : ℝ) : Prop := x.IsFinite ∧ |x.toReal - r| ≤ e

/-- Unit roundoff and underflow bound of `float`. -/
abbrev u32 : ℝ := 2 ^ (-24 : ℤ)
def η32 : ℝ := 2 ^ (-149 : ℤ)
/-- Unit roundoff and underflow bound of `double`. -/
abbrev u64 : ℝ := 2 ^ (-53 : ℤ)
def η64 : ℝ := 2 ^ (-1074 : ℤ)

theorem η32_eq : η32 = 2 ^ (-149 : ℤ) := rfl
theorem η64_eq : η64 = 2 ^ (-1074 : ℤ) := rfl

/-- The magnitude cap of the approximation lemmas, far below both overflow thresholds. -/
abbrev capF : ℝ := 2 ^ (100 : ℤ)

theorem u32_pos : (0 : ℝ) < u32 := by positivity

theorem two_pow_inv_small (n : ℕ) (hn : 140 ≤ n) : ((2 : ℝ) ^ n)⁻¹ ≤ 1 / 10 ^ 40 := by
  rw [inv_le_comm₀ (by positivity) (by positivity)]
  have : (2 : ℝ) ^ 140 ≤ 2 ^ n := pow_le_pow_right₀ one_le_two hn
  have h2 : (1 / 10 ^ 40 : ℝ)⁻¹ ≤ 2 ^ 140 := by norm_num
  linarith

theorem η32_small : η32 ≤ 1 / 10 ^ 40 := by
  have := two_pow_inv_small 149 (by norm_num)
  rw [η32_eq]; simpa [zpow_neg, zpow_natCast] using this

theorem η64_small : η64 ≤ 1 / 10 ^ 40 := by
  have := two_pow_inv_small 1074 (by norm_num)
  rw [η64_eq]; simpa [zpow_neg, zpow_natCast] using this
theorem η32_pos : (0 : ℝ) < η32 := by rw [η32_eq]; positivity
theorem u64_pos : (0 : ℝ) < u64 := by positivity
theorem η64_pos : (0 : ℝ) < η64 := by rw [η64_eq]; positivity

theorem capF_le_max32 : capF ≤ maxFinite32 := by
  rw [Float32.maxFinite32_eq]
  have h1 : (2 : ℝ) ^ (100 : ℤ) ≤ 2 ^ (127 : ℤ) := zpow_le_zpow_right₀ one_le_two (by norm_num)
  have h2 : (0 : ℝ) ≤ 2 ^ (-23 : ℤ) := by positivity
  have h3 : (2 : ℝ) ^ (-23 : ℤ) ≤ 1 := zpow_le_one_of_nonpos₀ one_le_two (by norm_num)
  have h4 : (0 : ℝ) ≤ 2 ^ (127 : ℤ) := by positivity
  nlinarith

theorem capF_le_max64 : capF ≤ maxFinite := by
  unfold maxFinite
  show (2 : ℝ) ^ (100 : ℤ) ≤ _
  have h1 : (2 : ℝ) ^ (100 : ℤ) ≤ 2 ^ (971 : ℤ) := zpow_le_zpow_right₀ one_le_two (by norm_num)
  have h4 : (0 : ℝ) ≤ 2 ^ (971 : ℤ) := by positivity
  have h5 : (1 : ℝ) ≤ 2 ^ 53 - 1 := by norm_num
  calc (2 : ℝ) ^ (100 : ℤ) = 1 * 2 ^ (100 : ℤ) := by ring
    _ ≤ (2 ^ 53 - 1) * 2 ^ (971 : ℤ) := mul_le_mul h5 h1 (by positivity) (by norm_num)

theorem rnd32 {fl x : ℝ} (h : |fl - x| ≤ 2 ^ (-24 : ℤ) * |x| + 2 ^ (-150 : ℤ)) :
    |fl - x| ≤ u32 * |x| + η32 := by
  have : (2 : ℝ) ^ (-150 : ℤ) ≤ η32 := by rw [η32_eq]; exact zpow_le_zpow_right₀ one_le_two (by norm_num)
  simp only [u32]; linarith

theorem rnd64 {fl x : ℝ} (h : |fl - x| ≤ 2 ^ (-53 : ℤ) * |x| + 2 ^ (-1075 : ℤ)) :
    |fl - x| ≤ u64 * |x| + η64 := by
  have : (2 : ℝ) ^ (-1075 : ℤ) ≤ η64 := by
    rw [η64_eq]; exact zpow_le_zpow_right₀ one_le_two (by norm_num)
  simp only [u64]; linarith

/-- Combine a rounding bound with an approximation of the exact result. -/
theorem round_approx {fl x r e u η : ℝ} (hu : 0 ≤ u) (hfl : |fl - x| ≤ u * |x| + η)
    (hx : |x - r| ≤ e) : |fl - r| ≤ e + u * (|r| + e) + η := by
  have h1 : |x| ≤ |r| + e := by
    have := abs_sub_abs_le_abs_sub x r; linarith
  have h2 := abs_sub_le fl x r
  nlinarith [mul_le_mul_of_nonneg_left h1 hu]

theorem A32.mono {x : Float32} {r e e' : ℝ} (h : A32 x r e) (he : e ≤ e') : A32 x r e' :=
  ⟨h.1, h.2.trans he⟩

theorem A64.mono {x : Float} {r e e' : ℝ} (h : A64 x r e) (he : e ≤ e') : A64 x r e' :=
  ⟨h.1, h.2.trans he⟩

theorem A32.congr {x : Float32} {r r' e : ℝ} (h : A32 x r e) (hr : r = r') : A32 x r' e := hr ▸ h

theorem A64.congr {x : Float} {r r' e : ℝ} (h : A64 x r e) (hr : r = r') : A64 x r' e := hr ▸ h

theorem A32.abs_le {x : Float32} {r e : ℝ} (h : A32 x r e) : |x.toReal| ≤ |r| + e := by
  have := abs_sub_abs_le_abs_sub x.toReal r; linarith [h.2]

theorem A64.abs_le {x : Float} {r e : ℝ} (h : A64 x r e) : |x.toReal| ≤ |r| + e := by
  have := abs_sub_abs_le_abs_sub x.toReal r; linarith [h.2]

theorem A32.of_exact {x : Float32} (h : x.IsFinite) : A32 x x.toReal 0 := ⟨h, by simp⟩

theorem A64.of_exact {x : Float} (h : x.IsFinite) : A64 x x.toReal 0 := ⟨h, by simp⟩

theorem A32.add {a b : Float32} {ra rb ea eb : ℝ} (ha : A32 a ra ea) (hb : A32 b rb eb)
    (hc : |ra + rb| + ea + eb ≤ capF) :
    A32 (a + b) (ra + rb) (ea + eb + u32 * (|ra + rb| + ea + eb) + η32) := by
  have hx : |(a.toReal + b.toReal) - (ra + rb)| ≤ ea + eb := by
    have := abs_add_le (a.toReal - ra) (b.toReal - rb)
    rw [show a.toReal - ra + (b.toReal - rb) = (a.toReal + b.toReal) - (ra + rb) by ring] at this
    linarith [ha.2, hb.2]
  have hm : |a.toReal + b.toReal| ≤ maxFinite32 := by
    have := abs_sub_abs_le_abs_sub (a.toReal + b.toReal) (ra + rb)
    linarith [capF_le_max32]
  obtain ⟨hf, he⟩ := Float32.add_err_all ha.1 hb.1 hm
  refine ⟨hf, ?_⟩
  have := round_approx u32_pos.le (fl := (a + b).toReal) (η := η32) (by linarith [η32_pos]) hx
  linarith

theorem A32.sub {a b : Float32} {ra rb ea eb : ℝ} (ha : A32 a ra ea) (hb : A32 b rb eb)
    (hc : |ra - rb| + ea + eb ≤ capF) :
    A32 (a - b) (ra - rb) (ea + eb + u32 * (|ra - rb| + ea + eb) + η32) := by
  have hx : |(a.toReal - b.toReal) - (ra - rb)| ≤ ea + eb := by
    have := abs_sub (a.toReal - ra) (b.toReal - rb)
    rw [show a.toReal - ra - (b.toReal - rb) = (a.toReal - b.toReal) - (ra - rb) by ring] at this
    linarith [ha.2, hb.2]
  have hm : |a.toReal - b.toReal| ≤ maxFinite32 := by
    have := abs_sub_abs_le_abs_sub (a.toReal - b.toReal) (ra - rb)
    linarith [capF_le_max32]
  obtain ⟨hf, he⟩ := Float32.sub_err_all ha.1 hb.1 hm
  refine ⟨hf, ?_⟩
  have := round_approx u32_pos.le (fl := (a - b).toReal) (η := η32) (by linarith [η32_pos]) hx
  linarith

/-- The error of a product of approximations. -/
theorem mul_approx {a b ra rb ea eb : ℝ} (ha : |a - ra| ≤ ea) (hb : |b - rb| ≤ eb) :
    |a * b - ra * rb| ≤ |ra| * eb + |rb| * ea + ea * eb := by
  have : a * b - ra * rb = ra * (b - rb) + rb * (a - ra) + (a - ra) * (b - rb) := by ring
  rw [this]
  have e1 := abs_add_le (ra * (b - rb) + rb * (a - ra)) ((a - ra) * (b - rb))
  have e2 := abs_add_le (ra * (b - rb)) (rb * (a - ra))
  simp only [abs_mul] at e1 e2
  have : |ra| * |b - rb| ≤ |ra| * eb := mul_le_mul_of_nonneg_left hb (abs_nonneg _)
  have : |rb| * |a - ra| ≤ |rb| * ea := mul_le_mul_of_nonneg_left ha (abs_nonneg _)
  have : |a - ra| * |b - rb| ≤ ea * eb :=
    mul_le_mul ha hb (abs_nonneg _) ((abs_nonneg _).trans ha)
  linarith

theorem A32.mul {a b : Float32} {ra rb ea eb : ℝ} (ha : A32 a ra ea) (hb : A32 b rb eb)
    (hc : |ra * rb| + (|ra| * eb + |rb| * ea + ea * eb) ≤ capF) :
    A32 (a * b) (ra * rb) ((|ra| * eb + |rb| * ea + ea * eb) +
      u32 * (|ra * rb| + (|ra| * eb + |rb| * ea + ea * eb)) + η32) := by
  have hx := mul_approx ha.2 hb.2
  have hm : |a.toReal * b.toReal| ≤ maxFinite32 := by
    have := abs_sub_abs_le_abs_sub (a.toReal * b.toReal) (ra * rb)
    linarith [capF_le_max32]
  obtain ⟨hf, he⟩ := Float32.mul_err_all ha.1 hb.1 hm
  refine ⟨hf, ?_⟩
  have := round_approx u32_pos.le (fl := (a * b).toReal) (η := η32)
    (rnd32 he) hx
  linarith

/-- The error of a quotient of approximations, with the divisor bounded away from `0`. -/
theorem div_approx {a b ra rb ea eb m : ℝ} (ha : |a - ra| ≤ ea) (hb : |b - rb| ≤ eb)
    (hm : 0 < m) (hrb : m + eb ≤ |rb|) :
    |a / b - ra / rb| ≤ (|rb| * ea + |ra| * eb) / (m * |rb|) := by
  have hrb0 : 0 < |rb| := by linarith [abs_nonneg (b - rb)]
  have hbm : m ≤ |b| := by
    have := abs_sub_abs_le_abs_sub rb b; rw [abs_sub_comm] at this; linarith
  have hb0 : 0 < |b| := by linarith
  have hb0' : b ≠ 0 := abs_pos.1 hb0
  have hrb0' : rb ≠ 0 := abs_pos.1 hrb0
  rw [div_sub_div _ _ hb0' hrb0', abs_div, abs_mul]
  have hnum : |a * rb - b * ra| ≤ |rb| * ea + |ra| * eb := by
    have : a * rb - b * ra = rb * (a - ra) - ra * (b - rb) := by ring
    rw [this]
    have := abs_sub (rb * (a - ra)) (ra * (b - rb))
    rw [abs_mul, abs_mul] at this
    have : |rb| * |a - ra| ≤ |rb| * ea := mul_le_mul_of_nonneg_left ha (abs_nonneg _)
    have : |ra| * |b - rb| ≤ |ra| * eb := mul_le_mul_of_nonneg_left hb (abs_nonneg _)
    linarith
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have h1 : 0 ≤ |rb| * ea + |ra| * eb := (abs_nonneg _).trans hnum
  calc |a * rb - b * ra| * (m * |rb|) ≤ (|rb| * ea + |ra| * eb) * (m * |rb|) :=
        mul_le_mul_of_nonneg_right hnum (by positivity)
    _ ≤ (|rb| * ea + |ra| * eb) * (|b| * |rb|) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hbm (abs_nonneg _)) h1

theorem A32.div {a b : Float32} {ra rb ea eb m : ℝ} (ha : A32 a ra ea) (hb : A32 b rb eb)
    (hm : 0 < m) (hrb : m + eb ≤ |rb|)
    (hc : |ra / rb| + (|rb| * ea + |ra| * eb) / (m * |rb|) ≤ capF) :
    A32 (a / b) (ra / rb) ((|rb| * ea + |ra| * eb) / (m * |rb|) +
      u32 * (|ra / rb| + (|rb| * ea + |ra| * eb) / (m * |rb|)) + η32) := by
  have hx := div_approx ha.2 hb.2 hm hrb
  have hb0 : b.toReal ≠ 0 := by
    intro h
    have := hb.2
    rw [h, zero_sub, abs_neg] at this
    linarith
  have hq : |a.toReal / b.toReal| ≤ maxFinite32 := by
    have := abs_sub_abs_le_abs_sub (a.toReal / b.toReal) (ra / rb)
    linarith [capF_le_max32]
  obtain ⟨hf, he⟩ := Float32.div_err_all ha.1 hb.1 hb0 hq
  refine ⟨hf, ?_⟩
  have := round_approx u32_pos.le (fl := (a / b).toReal) (η := η32)
    (rnd32 he) hx
  linarith

/-- `√` is `½`-Hölder: `|√x - √y| ≤ √|x - y|`. -/
theorem sqrt_sub_le (x y : ℝ) : |Real.sqrt x - Real.sqrt y| ≤ Real.sqrt |x - y| := by
  wlog h : y ≤ x generalizing x y
  · rw [abs_sub_comm, abs_sub_comm x]; exact this y x (by linarith)
  rcases le_or_gt y 0 with hy | hy
  · rw [Real.sqrt_eq_zero'.2 hy, sub_zero, abs_of_nonneg (Real.sqrt_nonneg _)]
    exact Real.sqrt_le_sqrt (by rw [abs_of_nonneg (by linarith)]; linarith)
  · have hs : Real.sqrt y ≤ Real.sqrt x := Real.sqrt_le_sqrt h
    rw [abs_of_nonneg (sub_nonneg.2 hs), abs_of_nonneg (by linarith : (0 : ℝ) ≤ x - y)]
    apply Real.le_sqrt_of_sq_le
    have hx0 : 0 ≤ x := by linarith
    have e1 := Real.sq_sqrt hx0
    have e2 := Real.sq_sqrt hy.le
    nlinarith [Real.sqrt_nonneg x, Real.sqrt_nonneg y]

theorem A32.sqrt {a : Float32} {ra ea : ℝ} (ha : A32 a ra ea) (h0 : 0 ≤ a.toReal)
    (hc : |ra| + ea ≤ capF) :
    A32 (Float32.sqrt a) (Real.sqrt ra) (Real.sqrt ea + u32 * (Real.sqrt ra + Real.sqrt ea) + η32) := by
  have hx : |Real.sqrt a.toReal - Real.sqrt ra| ≤ Real.sqrt ea :=
    (sqrt_sub_le _ _).trans (Real.sqrt_le_sqrt ha.2)
  have hm : a.toReal ≤ maxFinite32 := by
    have := (_root_.abs_le.1 (show |a.toReal - ra| ≤ ea from ha.2)).2
    have := le_abs_self ra
    linarith [capF_le_max32]
  obtain ⟨hf, he⟩ := Float32.sqrt_err_all ha.1 h0 hm
  refine ⟨hf, ?_⟩
  have he' : |(Float32.sqrt a).toReal - Real.sqrt a.toReal| ≤
      u32 * |Real.sqrt a.toReal| + η32 := by
    rw [abs_of_nonneg (Real.sqrt_nonneg _)]
    have := rnd32 (fl := (Float32.sqrt a).toReal) (x := Real.sqrt a.toReal)
      (by rw [abs_of_nonneg (Real.sqrt_nonneg _)]; exact he)
    rwa [abs_of_nonneg (Real.sqrt_nonneg _)] at this
  have := round_approx u32_pos.le he' hx
  rw [abs_of_nonneg (Real.sqrt_nonneg _)] at this
  linarith

theorem A64.add {a b : Float} {ra rb ea eb : ℝ} (ha : A64 a ra ea) (hb : A64 b rb eb)
    (hc : |ra + rb| + ea + eb ≤ capF) :
    A64 (a + b) (ra + rb) (ea + eb + u64 * (|ra + rb| + ea + eb) + η64) := by
  have hx : |(a.toReal + b.toReal) - (ra + rb)| ≤ ea + eb := by
    have := abs_add_le (a.toReal - ra) (b.toReal - rb)
    rw [show a.toReal - ra + (b.toReal - rb) = (a.toReal + b.toReal) - (ra + rb) by ring] at this
    linarith [ha.2, hb.2]
  have hm : |a.toReal + b.toReal| ≤ maxFinite := by
    have := abs_sub_abs_le_abs_sub (a.toReal + b.toReal) (ra + rb)
    linarith [capF_le_max64]
  obtain ⟨hf, he⟩ := Float.add_err_all ha.1 hb.1 hm
  refine ⟨hf, ?_⟩
  have := round_approx u64_pos.le (fl := (a + b).toReal) (η := η64) (by linarith [η64_pos]) hx
  linarith

theorem A64.sub {a b : Float} {ra rb ea eb : ℝ} (ha : A64 a ra ea) (hb : A64 b rb eb)
    (hc : |ra - rb| + ea + eb ≤ capF) :
    A64 (a - b) (ra - rb) (ea + eb + u64 * (|ra - rb| + ea + eb) + η64) := by
  have hx : |(a.toReal - b.toReal) - (ra - rb)| ≤ ea + eb := by
    have := abs_sub (a.toReal - ra) (b.toReal - rb)
    rw [show a.toReal - ra - (b.toReal - rb) = (a.toReal - b.toReal) - (ra - rb) by ring] at this
    linarith [ha.2, hb.2]
  have hm : |a.toReal - b.toReal| ≤ maxFinite := by
    have := abs_sub_abs_le_abs_sub (a.toReal - b.toReal) (ra - rb)
    linarith [capF_le_max64]
  obtain ⟨hf, he⟩ := Float.sub_err_all ha.1 hb.1 hm
  refine ⟨hf, ?_⟩
  have := round_approx u64_pos.le (fl := (a - b).toReal) (η := η64) (by linarith [η64_pos]) hx
  linarith

theorem A64.mul {a b : Float} {ra rb ea eb : ℝ} (ha : A64 a ra ea) (hb : A64 b rb eb)
    (hc : |ra * rb| + (|ra| * eb + |rb| * ea + ea * eb) ≤ capF) :
    A64 (a * b) (ra * rb) ((|ra| * eb + |rb| * ea + ea * eb) +
      u64 * (|ra * rb| + (|ra| * eb + |rb| * ea + ea * eb)) + η64) := by
  have hx := mul_approx ha.2 hb.2
  have hm : |a.toReal * b.toReal| ≤ maxFinite := by
    have := abs_sub_abs_le_abs_sub (a.toReal * b.toReal) (ra * rb)
    linarith [capF_le_max64]
  obtain ⟨hf, he⟩ := Float.mul_err_all ha.1 hb.1 hm
  refine ⟨hf, ?_⟩
  have := round_approx u64_pos.le (fl := (a * b).toReal) (η := η64)
    (rnd64 he) hx
  linarith

/-! ## Conversions (`LibmSpec`) -/

theorem A32.toFloat (hL : LibmSpec) {a : Float32} {r e : ℝ} (ha : A32 a r e) :
    A64 (Float32.toFloat a) r e := by
  obtain ⟨hf, he⟩ := hL.f32ToF64 a ha.1
  exact ⟨hf, he ▸ ha.2⟩

theorem A64.toFloat32 (hL : LibmSpec) {a : Float} {r e : ℝ} (ha : A64 a r e)
    (hc : |r| + e ≤ capF) : A32 (Float.toFloat32 a) r (e + u32 * (|r| + e) + η32) := by
  have hm : |a.toReal| ≤ maxFinite32 := by
    have := ha.abs_le; linarith [capF_le_max32]
  obtain ⟨hf, he⟩ := hL.f64ToF32 a ha.1 hm
  refine ⟨hf, ?_⟩
  have := round_approx u32_pos.le (fl := (Float.toFloat32 a).toReal) (η := η32)
    (rnd32 he) ha.2
  linarith

end

end Contracts.Mission
