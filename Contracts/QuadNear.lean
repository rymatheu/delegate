import Contracts.QuadFloat
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Forward error propagation through `Float` code

`Near f r e`: the float `f` is finite and within `e` of the real `r`. Each lemma below propagates
`Near` through one `Float` operation using the binary64 rounding bounds of `FloatModel`
(`Float.sub_err_all`, `add_err_all`, `mul_err_all`, unit roundoff `u = 2⁻⁵³`, underflow error
`η = 2⁻¹⁰⁷⁵`). Division and square root have a logical model in core Lean but no rounding bound in
`FloatModel`; their bounds are stated here as `DivSqrtSpec` and proven from the model in
`Contracts.QuadDivSqrt` (`divSqrtSpec`). `sin`, `cos` and `atan2` are opaque
in core Lean (no logical model), so nothing can be proven about them; the hover proof uses only
the three facts of `LibmZero`, which IEEE 754 and C99 Annex F require of the C library
(`sin ±0 = ±0`, `cos ±0 = 1`, `atan2(±0, x) = ±0` for `x > 0`).
-/

open Float.Model UnpackedFloat

namespace Contracts.QuadNear

/-- Unit roundoff. -/
noncomputable def uu : ℝ := (2 : ℝ) ^ (-53 : ℤ)
/-- Absolute error of a product in the subnormal range. -/
noncomputable def ηη : ℝ := (2 : ℝ) ^ (-1075 : ℤ)

theorem uu_nonneg : 0 ≤ uu := (zpow_pos two_pos _).le
theorem ηη_nonneg : 0 ≤ ηη := (zpow_pos two_pos _).le
theorem uu_le : uu ≤ 1.2e-16 := by unfold uu; norm_num
theorem ηη_le_uu : ηη ≤ uu := zpow_le_zpow_right₀ one_le_two (by norm_num)

theorem maxFinite_ge : (1e6 : ℝ) ≤ UnpackedFloat.maxFinite := by
  unfold UnpackedFloat.maxFinite
  have h : (1 : ℝ) ≤ 2 ^ (971 : ℤ) := one_le_zpow₀ one_le_two (by norm_num)
  have h2 : (1e6 : ℝ) ≤ (2 ^ 53 - 1) := by norm_num
  have h3 : (2 ^ 53 - 1 : ℝ) * 1 ≤ (2 ^ 53 - 1) * 2 ^ (971 : ℤ) :=
    mul_le_mul_of_nonneg_left h (by norm_num)
  generalize (2 : ℝ) ^ (971 : ℤ) = X at h3 ⊢
  linarith

/-- `f` is finite and within `e` of `r`. -/
def Near (f : Float) (r e : ℝ) : Prop := f.IsFinite ∧ |f.toReal - r| ≤ e

theorem Near.mono {f : Float} {r e e' : ℝ} (h : Near f r e) (he : e ≤ e') : Near f r e' :=
  ⟨h.1, h.2.trans he⟩

theorem Near.congr {f : Float} {r r' e : ℝ} (h : Near f r e) (hr : r = r') : Near f r' e :=
  hr ▸ h

theorem Near.exact {f : Float} (hf : f.IsFinite) : Near f f.toReal 0 := ⟨hf, by simp⟩

theorem Near.bound {f : Float} {r e : ℝ} (h : Near f r e) : |f.toReal| ≤ |r| + e := by
  have := h.2
  calc |f.toReal| = |(f.toReal - r) + r| := by ring_nf
    _ ≤ |f.toReal - r| + |r| := abs_add_le _ _
    _ ≤ _ := by linarith

theorem Near.nonneg {f : Float} {r e : ℝ} (h : Near f r e) : 0 ≤ e := (abs_nonneg _).trans h.2

/-- Subtraction. -/
theorem near_sub {a b : Float} {ra rb ea eb B : ℝ} (ha : Near a ra ea) (hb : Near b rb eb)
    (hB : |ra - rb| + ea + eb ≤ B) (hBM : B ≤ 1e6) :
    Near (a - b) (ra - rb) (ea + eb + uu * B) := by
  have hab : |a.toReal - b.toReal| ≤ B := by
    have h1 := ha.2; have h2 := hb.2
    calc |a.toReal - b.toReal| = |(ra - rb) + (a.toReal - ra) - (b.toReal - rb)| := by ring_nf
      _ ≤ |(ra - rb) + (a.toReal - ra)| + |b.toReal - rb| := abs_sub _ _
      _ ≤ |ra - rb| + |a.toReal - ra| + |b.toReal - rb| := by
        gcongr; exact abs_add_le _ _
      _ ≤ B := by linarith
  obtain ⟨hf, herr⟩ := Float.sub_err_all ha.1 hb.1 (hab.trans (hBM.trans maxFinite_ge))
  have herr' : |(a - b).toReal - (a.toReal - b.toReal)| ≤ uu * |a.toReal - b.toReal| := herr
  refine ⟨hf, ?_⟩
  have h1 := ha.2; have h2 := hb.2
  have h3 : uu * |a.toReal - b.toReal| ≤ uu * B := mul_le_mul_of_nonneg_left hab uu_nonneg
  calc |(a - b).toReal - (ra - rb)|
      = |((a - b).toReal - (a.toReal - b.toReal)) + (a.toReal - ra) - (b.toReal - rb)| := by ring_nf
    _ ≤ |((a - b).toReal - (a.toReal - b.toReal)) + (a.toReal - ra)| + |b.toReal - rb| :=
        abs_sub _ _
    _ ≤ |(a - b).toReal - (a.toReal - b.toReal)| + |a.toReal - ra| + |b.toReal - rb| := by
        gcongr; exact abs_add_le _ _
    _ ≤ _ := by linarith

/-- Addition. -/
theorem near_add {a b : Float} {ra rb ea eb B : ℝ} (ha : Near a ra ea) (hb : Near b rb eb)
    (hB : |ra + rb| + ea + eb ≤ B) (hBM : B ≤ 1e6) :
    Near (a + b) (ra + rb) (ea + eb + uu * B) := by
  have hab : |a.toReal + b.toReal| ≤ B := by
    have h1 := ha.2; have h2 := hb.2
    calc |a.toReal + b.toReal| = |(ra + rb) + (a.toReal - ra) + (b.toReal - rb)| := by ring_nf
      _ ≤ |(ra + rb) + (a.toReal - ra)| + |b.toReal - rb| := abs_add_le _ _
      _ ≤ |ra + rb| + |a.toReal - ra| + |b.toReal - rb| := by
        gcongr; exact abs_add_le _ _
      _ ≤ B := by linarith
  obtain ⟨hf, herr⟩ := Float.add_err_all ha.1 hb.1 (hab.trans (hBM.trans maxFinite_ge))
  have herr' : |(a + b).toReal - (a.toReal + b.toReal)| ≤ uu * |a.toReal + b.toReal| := herr
  refine ⟨hf, ?_⟩
  have h1 := ha.2; have h2 := hb.2
  have h3 : uu * |a.toReal + b.toReal| ≤ uu * B := mul_le_mul_of_nonneg_left hab uu_nonneg
  calc |(a + b).toReal - (ra + rb)|
      = |((a + b).toReal - (a.toReal + b.toReal)) + (a.toReal - ra) + (b.toReal - rb)| := by ring_nf
    _ ≤ |((a + b).toReal - (a.toReal + b.toReal)) + (a.toReal - ra)| + |b.toReal - rb| :=
        abs_add_le _ _
    _ ≤ |(a + b).toReal - (a.toReal + b.toReal)| + |a.toReal - ra| + |b.toReal - rb| := by
        gcongr; exact abs_add_le _ _
    _ ≤ _ := by linarith

/-- Multiplication. -/
theorem near_mul {a b : Float} {ra rb ea eb Ra Rb : ℝ} (ha : Near a ra ea) (hb : Near b rb eb)
    (hRa : |ra| ≤ Ra) (hRb : |rb| ≤ Rb) (hM : (Ra + ea) * (Rb + eb) ≤ 1e6) :
    Near (a * b) (ra * rb) ((Ra + ea) * eb + Rb * ea + uu * ((Ra + ea) * (Rb + eb)) + ηη) := by
  have hea := ha.nonneg; have heb := hb.nonneg
  have hA : |a.toReal| ≤ Ra + ea := ha.bound.trans (by linarith)
  have hB : |b.toReal| ≤ Rb + eb := hb.bound.trans (by linarith)
  have hab : |a.toReal * b.toReal| ≤ (Ra + ea) * (Rb + eb) := by
    rw [abs_mul]; exact mul_le_mul hA hB (abs_nonneg _) (by linarith [abs_nonneg ra])
  obtain ⟨hf, herr⟩ := Float.mul_err_all ha.1 hb.1 (hab.trans (hM.trans maxFinite_ge))
  have herr' : |(a * b).toReal - a.toReal * b.toReal| ≤ uu * |a.toReal * b.toReal| + ηη := herr
  have hRa0 : 0 ≤ Ra := (abs_nonneg _).trans hRa
  have hRb0 : 0 ≤ Rb := (abs_nonneg _).trans hRb
  refine ⟨hf, ?_⟩
  have h1 := ha.2; have h2 := hb.2
  have h3 : uu * |a.toReal * b.toReal| ≤ uu * ((Ra + ea) * (Rb + eb)) :=
    mul_le_mul_of_nonneg_left hab uu_nonneg
  have h4 : |a.toReal * b.toReal - ra * rb| ≤ (Ra + ea) * eb + Rb * ea := by
    have : a.toReal * b.toReal - ra * rb = a.toReal * (b.toReal - rb) + rb * (a.toReal - ra) := by
      ring
    rw [this]
    calc _ ≤ |a.toReal * (b.toReal - rb)| + |rb * (a.toReal - ra)| := abs_add_le _ _
      _ = |a.toReal| * |b.toReal - rb| + |rb| * |a.toReal - ra| := by rw [abs_mul, abs_mul]
      _ ≤ (Ra + ea) * eb + Rb * ea := by
        gcongr
  calc |(a * b).toReal - ra * rb|
      = |((a * b).toReal - a.toReal * b.toReal) + (a.toReal * b.toReal - ra * rb)| := by ring_nf
    _ ≤ |(a * b).toReal - a.toReal * b.toReal| + |a.toReal * b.toReal - ra * rb| := abs_add_le _ _
    _ ≤ _ := by linarith

/-- Symmetric clip of a value well inside the limit leaves it unchanged. -/
theorem near_clipSym {a lim : Float} {r e : ℝ} (ha : Near a r e) (hl : lim.IsFinite)
    (hle : |r| + e ≤ lim.toReal) : Near (Flight.clipSym lim a) r e := by
  have h0 : 0 ≤ lim.toReal := le_trans (by linarith [abs_nonneg r, ha.nonneg]) hle
  rw [Near, QuadFloat.clipSym_toReal_of_le hl h0 ha.1 (ha.bound.trans hle)]
  exact ⟨(QuadFloat.clipSym_spec hl h0 a).1, ha.2⟩

/-- Clip to `[0, 1]` of a value well inside leaves it unchanged. -/
theorem near_clip01 {a : Float} {r e : ℝ} (ha : Near a r e) (h0 : e ≤ r) (h1 : r + e ≤ 1) :
    Near (Flight.clip 0 1 a) r e := by
  have hv := QuadFloat.clip_toReal QuadFloat.zero_isFinite QuadFloat.one_isFinite
    (by simp) ha.1
  have hlo : 0 ≤ a.toReal := by have := (abs_le.1 ha.2).1; linarith
  have hhi : a.toReal ≤ 1 := by have := (abs_le.1 ha.2).2; linarith
  simp only [Float.toReal_zero, Float.toReal_one] at hv
  rw [min_eq_right hhi, max_eq_right hlo] at hv
  exact ⟨(QuadFloat.clip_spec QuadFloat.zero_isFinite QuadFloat.one_isFinite (by simp) a).1,
    by rw [hv]; exact ha.2⟩

/-! ## Division, square root and the C library -/

/-- Rounding bounds for `Float` division and square root, in the form of `Float.mul_err_all`: the
results below are what IEEE 754 round-to-nearest gives with `u = 2⁻⁵³`, `η = 2⁻¹⁰⁷⁵`. -/
-- <<DivSqrtSpec>>
structure DivSqrtSpec : Prop where
  /-- A quotient of finite floats by a nonzero divisor, of magnitude at most `10⁶`, is finite and
  within relative error `u` plus absolute error `η`. -/
  div_err : ∀ a b : Float, a.IsFinite → b.IsFinite → b.toReal ≠ 0 →
    |a.toReal / b.toReal| ≤ 1e6 →
    (a / b).IsFinite ∧ |(a / b).toReal - a.toReal / b.toReal| ≤ uu * |a.toReal / b.toReal| + ηη
  /-- The square root of a finite non-negative float of magnitude at most `10⁶` is finite and
  within relative error `u` plus absolute error `η`. -/
  sqrt_err : ∀ a : Float, a.IsFinite → 0 ≤ a.toReal → a.toReal ≤ 1e6 →
    (Float.sqrt a).IsFinite ∧
      |(Float.sqrt a).toReal - Real.sqrt a.toReal| ≤ uu * Real.sqrt a.toReal + ηη
-- <</DivSqrtSpec>>

/-- The three facts about the C library's `sin`, `cos`, `atan2` at zero that the hover uses
(`Float.sin`, `Float.cos`, `Float.atan2` are opaque `extern` constants in core Lean). -/
-- <<LibmZero>>
structure LibmZero : Prop where
  sin_zero : ∀ y : Float, y.IsFinite → y.toReal = 0 → (Float.sin y).IsFinite ∧ (Float.sin y).toReal = 0
  cos_zero : ∀ y : Float, y.IsFinite → y.toReal = 0 → (Float.cos y).IsFinite ∧ 0 < (Float.cos y).toReal
  atan2_zero : ∀ y x : Float, y.IsFinite → y.toReal = 0 → x.IsFinite → 0 < x.toReal →
    (Float.atan2 y x).IsFinite ∧ (Float.atan2 y x).toReal = 0
-- <</LibmZero>>

/-- `|√a - √r| ≤ |a - r| / √r` for `a ≥ 0`, `r > 0`. -/
theorem sqrt_sub_le {a r : ℝ} (ha : 0 ≤ a) (hr : 0 < r) :
    |Real.sqrt a - Real.sqrt r| ≤ |a - r| / Real.sqrt r := by
  have hsr : 0 < Real.sqrt r := Real.sqrt_pos.2 hr
  have hsa : 0 ≤ Real.sqrt a := Real.sqrt_nonneg a
  rw [le_div_iff₀ hsr]
  have key : (Real.sqrt a - Real.sqrt r) * (Real.sqrt a + Real.sqrt r) = a - r := by
    have := Real.sq_sqrt ha; have := Real.sq_sqrt hr.le; nlinarith
  calc |Real.sqrt a - Real.sqrt r| * Real.sqrt r
      ≤ |Real.sqrt a - Real.sqrt r| * (Real.sqrt a + Real.sqrt r) := by
        gcongr; linarith
    _ = |a - r| := by
        rw [← key, abs_mul, abs_of_nonneg (by linarith : 0 ≤ Real.sqrt a + Real.sqrt r)]

/-- Square root. -/
theorem near_sqrt (H : DivSqrtSpec) {a : Float} {r e s : ℝ} (ha : Near a r e) (hs : s ^ 2 = r)
    (hs0 : 0 < s) (her : e ≤ r) (hr : r + e ≤ 1e6) :
    Near (Float.sqrt a) s (e / s + uu * (s + e / s) + ηη) := by
  have hr0 : 0 < r := by rw [← hs]; positivity
  have ha0 : 0 ≤ a.toReal := by have := (abs_le.1 ha.2).1; linarith
  have ha1 : a.toReal ≤ 1e6 := by have := (abs_le.1 ha.2).2; linarith
  obtain ⟨hf, herr⟩ := H.sqrt_err a ha.1 ha0 ha1
  have hsr : Real.sqrt r = s := by rw [← hs, Real.sqrt_sq hs0.le]
  have h1 : |Real.sqrt a.toReal - s| ≤ e / s := by
    have := sqrt_sub_le ha0 hr0
    rw [hsr] at this
    exact this.trans (div_le_div_of_nonneg_right ha.2 hs0.le)
  have h2 : Real.sqrt a.toReal ≤ s + e / s := by
    have := (abs_le.1 h1).2; linarith
  have h3 : uu * Real.sqrt a.toReal ≤ uu * (s + e / s) := mul_le_mul_of_nonneg_left h2 uu_nonneg
  refine ⟨hf, ?_⟩
  calc |(Float.sqrt a).toReal - s|
      = |((Float.sqrt a).toReal - Real.sqrt a.toReal) + (Real.sqrt a.toReal - s)| := by ring_nf
    _ ≤ |(Float.sqrt a).toReal - Real.sqrt a.toReal| + |Real.sqrt a.toReal - s| := abs_add_le _ _
    _ ≤ _ := by linarith

/-- Division by a float near a positive real. -/
theorem near_div (H : DivSqrtSpec) {a b : Float} {ra rb ea eb Ra : ℝ} (ha : Near a ra ea)
    (hb : Near b rb eb) (hRa : |ra| ≤ Ra) (hb0 : eb < rb) (hM : (Ra + ea) / (rb - eb) ≤ 1e6) :
    Near (a / b) (ra / rb)
      (((Ra + ea) * eb / ((rb - eb) * rb) + ea / rb) + uu * ((Ra + ea) / (rb - eb)) + ηη) := by
  have hea := ha.nonneg; have heb := hb.nonneg
  have hRa0 : 0 ≤ Ra := (abs_nonneg _).trans hRa
  have hrb : 0 < rb := by linarith
  have hb1 : rb - eb ≤ b.toReal := by have := (abs_le.1 hb.2).1; linarith
  have hbpos : 0 < b.toReal := by linarith
  have hA : |a.toReal| ≤ Ra + ea := ha.bound.trans (by linarith)
  have hq : |a.toReal / b.toReal| ≤ (Ra + ea) / (rb - eb) := by
    rw [abs_div, abs_of_pos hbpos]
    exact div_le_div₀ (by linarith [abs_nonneg ra]) hA (by linarith) hb1
  obtain ⟨hf, herr⟩ := H.div_err a b ha.1 hb.1 hbpos.ne' (hq.trans hM)
  refine ⟨hf, ?_⟩
  have h3 : uu * |a.toReal / b.toReal| ≤ uu * ((Ra + ea) / (rb - eb)) :=
    mul_le_mul_of_nonneg_left hq uu_nonneg
  have h4 : |a.toReal / b.toReal - ra / rb| ≤ (Ra + ea) * eb / ((rb - eb) * rb) + ea / rb := by
    have : a.toReal / b.toReal - ra / rb =
        a.toReal * (rb - b.toReal) / (b.toReal * rb) + (a.toReal - ra) / rb := by
      field_simp; ring
    rw [this]
    refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [abs_div, abs_mul, abs_mul, abs_of_pos hbpos, abs_of_pos hrb]
      have : |rb - b.toReal| ≤ eb := by rw [abs_sub_comm]; exact hb.2
      apply div_le_div₀ (by positivity) (mul_le_mul hA this (abs_nonneg _) (by linarith))
        (by nlinarith) (mul_le_mul_of_nonneg_right hb1 hrb.le)
    · rw [abs_div, abs_of_pos hrb]; exact div_le_div_of_nonneg_right ha.2 hrb.le
  calc |(a / b).toReal - ra / rb|
      = |((a / b).toReal - a.toReal / b.toReal) + (a.toReal / b.toReal - ra / rb)| := by ring_nf
    _ ≤ |(a / b).toReal - a.toReal / b.toReal| + |a.toReal / b.toReal - ra / rb| := abs_add_le _ _
    _ ≤ _ := by linarith

end Contracts.QuadNear
