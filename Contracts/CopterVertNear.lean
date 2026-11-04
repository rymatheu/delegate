import Contracts.Float32ClipAP
import Contracts.CopterVert
import Copter.Loop

/-!
# Forward error propagation through `Float32` code, and the constants of the vertical channel

The bridge between the `Float32` vertical path of the ArduCopter port and the real recurrence
`Contracts.CopterVert.stepN` is an operation-by-operation forward error analysis. This file holds
its calculus and its constants; `Contracts.CopterVertNearStep` applies it to the functions on the
path and `Contracts.CopterVertNearTick` assembles one tick.

**The calculus.** `Near32 f r e`: the binary32 float `f` is finite and within `e` of the real `r`
(`Near64` for binary64). Each propagation lemma moves `Near32` through one operation with the
binary32 rounding bounds of `FloatModel.Float32` (`add_err_all`, `sub_err_all`, `mul_err_all`,
`div_err_all`: unit roundoff `u = 2⁻²⁴`, underflow error `η = 2⁻¹⁵⁰` for `*` and `/`):
`near_add`, `near_sub`, `near_mul`, `near_div`. The exactness lemmas (`add_exact`, `sub_exact`,
`mul_exact`) use the bracket theorems instead (rounding never crosses a float): when the exact
result is the value of a finite float, the computed result has that value. They give `x · 1 = x`,
`x + (±0) = x`, `x · (±0) = ±0` and so on, which the path uses wherever a gain is `1` or a term is
`0`. `constrain_float`, `MIN`, `MAX` and the clip are handled by comparing exact values
(`constrain_float_of_near`, `MIN_eq_left`, ...).

**Narrowing.** `Float.toFloat32` (C `(float)x`) is an opaque `extern` constant in core Lean, like
the C library, so its rounding is a hypothesis: `NarrowSpec`, round to nearest on a range. The
position error of `AC_P_1D.update_all` passes through it.

**Constants.** The binary32 values the code computes are evaluated by the kernel through the
logical model of `Float32` (`rfl` on the unpacked form, no rounding argument):
`dtF = float(2500) · 1e-6f` (and `1.0f / 400`), `calc_lowpass_alpha_dt` at `dtF` and the cutoffs
`5`, `20`, `2` and `0` (`alpha_v`, `alpha_a`, `alpha_m`, and `1`), the literals of the parameters
on the path (`PSC_D_POS_P = 1`, `PSC_D_VEL_P = 5`, `PSC_D_ACC_P = 0.05`, `PSC_D_ACC_I = 0.1`,
`PSC_D_ACC_IMAX = 0.8`, `GRAVITY_MSS`, `MOT_THST_HOVER = 0.4444`, `FLT_EPSILON`). Their exact
values are the rationals of `Contracts.CopterVert` (`dtc`, `av`, `aa`, `am`, `kp`, `ki`) and of
`Contracts/VerticalChannel.md`, section 5.
-/

open Float.Model UnpackedFloat AP_Math Contracts.CopterVert

namespace Contracts.CopterVertNear

/-! ## Unit roundoff -/

/-- binary32 unit roundoff. -/
noncomputable def u32 : ℝ := (2 : ℝ) ^ (-24 : ℤ)
/-- binary32 absolute error of a product or quotient in the subnormal range. -/
noncomputable def η32 : ℝ := (2 : ℝ) ^ (-150 : ℤ)

theorem u32_nonneg : 0 ≤ u32 := (zpow_pos two_pos _).le
theorem η32_nonneg : 0 ≤ η32 := (zpow_pos two_pos _).le
theorem u32_le : u32 ≤ 5.97e-8 := by unfold u32; norm_num
theorem η32_le : η32 ≤ 1e-44 := by unfold η32; norm_num

theorem maxFinite32_ge : (1e6 : ℝ) ≤ maxFinite32 := by
  unfold maxFinite32
  have h : (1 : ℝ) ≤ 2 ^ (104 : ℤ) := one_le_zpow₀ one_le_two (by norm_num)
  have h2 : (1e6 : ℝ) ≤ (2 ^ 24 - 1) := by norm_num
  have h3 : (2 ^ 24 - 1 : ℝ) * 1 ≤ (2 ^ 24 - 1) * 2 ^ (104 : ℤ) :=
    mul_le_mul_of_nonneg_left h (by norm_num)
  generalize (2 : ℝ) ^ (104 : ℤ) = X at h3 ⊢
  linarith

/-! ## `Near32` -/

/-- The binary32 float `f` is finite and within `e` of the real `r`. -/
def Near32 (f : Float32) (r e : ℝ) : Prop := f.IsFinite ∧ |f.toReal - r| ≤ e

/-- The binary64 float `f` is finite and within `e` of the real `r`. -/
def Near64 (f : Float) (r e : ℝ) : Prop := f.IsFinite ∧ |f.toReal - r| ≤ e

theorem Near32.mono {f : Float32} {r e e' : ℝ} (h : Near32 f r e) (he : e ≤ e') : Near32 f r e' :=
  ⟨h.1, h.2.trans he⟩

theorem Near32.congr {f : Float32} {r r' e : ℝ} (h : Near32 f r e) (hr : r = r') : Near32 f r' e :=
  hr ▸ h

theorem Near32.exact {f : Float32} (hf : f.IsFinite) : Near32 f f.toReal 0 := ⟨hf, by simp⟩

theorem Near32.of_val {f : Float32} {r : ℝ} (hf : f.IsFinite) (hr : f.toReal = r) : Near32 f r 0 :=
  ⟨hf, by rw [hr]; simp⟩

theorem Near32.nonneg {f : Float32} {r e : ℝ} (h : Near32 f r e) : 0 ≤ e := (abs_nonneg _).trans h.2

theorem Near32.bound {f : Float32} {r e : ℝ} (h : Near32 f r e) : |f.toReal| ≤ |r| + e := by
  have := h.2
  calc |f.toReal| = |(f.toReal - r) + r| := by ring_nf
    _ ≤ |f.toReal - r| + |r| := abs_add_le _ _
    _ ≤ _ := by linarith

theorem Near32.val0 {f : Float32} {r : ℝ} (h : Near32 f r 0) : f.toReal = r := by
  have := h.2; rw [abs_nonpos_iff, sub_eq_zero] at this; exact this

theorem Near32.lo {f : Float32} {r e : ℝ} (h : Near32 f r e) : r - e ≤ f.toReal := by
  have := (abs_le.1 h.2).1; linarith

theorem Near32.hi {f : Float32} {r e : ℝ} (h : Near32 f r e) : f.toReal ≤ r + e := by
  have := (abs_le.1 h.2).2; linarith

/-- Transport along a float with the same value. -/
theorem Near32.of_eq_val {x y : Float32} {r e : ℝ} (hf : x.IsFinite) (hv : x.toReal = y.toReal)
    (hy : Near32 y r e) : Near32 x r e := ⟨hf, by rw [hv]; exact hy.2⟩

/-- Change of the reference value: `Near32 f r e` and `|r - r'| ≤ d` give `Near32 f r' (e + d)`. -/
theorem Near32.shift {f : Float32} {r r' e d : ℝ} (h : Near32 f r e) (hd : |r - r'| ≤ d) :
    Near32 f r' (e + d) := by
  refine ⟨h.1, ?_⟩
  calc |f.toReal - r'| = |(f.toReal - r) + (r - r')| := by ring_nf
    _ ≤ |f.toReal - r| + |r - r'| := abs_add_le _ _
    _ ≤ e + d := add_le_add h.2 hd

theorem bnd3 {x a b B : ℝ} (h1 : -(B - a - b) ≤ x) (h2 : x ≤ B - a - b) : |x| + a + b ≤ B := by
  have := abs_le.2 ⟨h1, h2⟩; linarith

theorem bnd {x B : ℝ} (h1 : -B ≤ x) (h2 : x ≤ B) : |x| ≤ B := abs_le.2 ⟨h1, h2⟩

/-! ## Propagation through `+`, `-`, `*`, `/` -/

/-- Subtraction. -/
theorem near_sub {a b : Float32} {ra rb ea eb B : ℝ} (ha : Near32 a ra ea) (hb : Near32 b rb eb)
    (hB : |ra - rb| + ea + eb ≤ B) (hBM : B ≤ 1e6) :
    Near32 (a - b) (ra - rb) (ea + eb + u32 * B) := by
  have hab : |a.toReal - b.toReal| ≤ B := by
    have h1 := ha.2; have h2 := hb.2
    calc |a.toReal - b.toReal| = |(ra - rb) + (a.toReal - ra) - (b.toReal - rb)| := by ring_nf
      _ ≤ |(ra - rb) + (a.toReal - ra)| + |b.toReal - rb| := abs_sub _ _
      _ ≤ |ra - rb| + |a.toReal - ra| + |b.toReal - rb| := by
        gcongr; exact abs_add_le _ _
      _ ≤ B := by linarith
  obtain ⟨hf, herr⟩ := Float32.sub_err_all ha.1 hb.1 (hab.trans (hBM.trans maxFinite32_ge))
  have herr' : |(a - b).toReal - (a.toReal - b.toReal)| ≤ u32 * |a.toReal - b.toReal| := herr
  refine ⟨hf, ?_⟩
  have h1 := ha.2; have h2 := hb.2
  have h3 : u32 * |a.toReal - b.toReal| ≤ u32 * B := mul_le_mul_of_nonneg_left hab u32_nonneg
  calc |(a - b).toReal - (ra - rb)|
      = |((a - b).toReal - (a.toReal - b.toReal)) + (a.toReal - ra) - (b.toReal - rb)| := by ring_nf
    _ ≤ |((a - b).toReal - (a.toReal - b.toReal)) + (a.toReal - ra)| + |b.toReal - rb| :=
        abs_sub _ _
    _ ≤ |(a - b).toReal - (a.toReal - b.toReal)| + |a.toReal - ra| + |b.toReal - rb| := by
        gcongr; exact abs_add_le _ _
    _ ≤ _ := by linarith

/-- Addition. -/
theorem near_add {a b : Float32} {ra rb ea eb B : ℝ} (ha : Near32 a ra ea) (hb : Near32 b rb eb)
    (hB : |ra + rb| + ea + eb ≤ B) (hBM : B ≤ 1e6) :
    Near32 (a + b) (ra + rb) (ea + eb + u32 * B) := by
  have hab : |a.toReal + b.toReal| ≤ B := by
    have h1 := ha.2; have h2 := hb.2
    calc |a.toReal + b.toReal| = |(ra + rb) + (a.toReal - ra) + (b.toReal - rb)| := by ring_nf
      _ ≤ |(ra + rb) + (a.toReal - ra)| + |b.toReal - rb| := abs_add_le _ _
      _ ≤ |ra + rb| + |a.toReal - ra| + |b.toReal - rb| := by
        gcongr; exact abs_add_le _ _
      _ ≤ B := by linarith
  obtain ⟨hf, herr⟩ := Float32.add_err_all ha.1 hb.1 (hab.trans (hBM.trans maxFinite32_ge))
  have herr' : |(a + b).toReal - (a.toReal + b.toReal)| ≤ u32 * |a.toReal + b.toReal| := herr
  refine ⟨hf, ?_⟩
  have h1 := ha.2; have h2 := hb.2
  have h3 : u32 * |a.toReal + b.toReal| ≤ u32 * B := mul_le_mul_of_nonneg_left hab u32_nonneg
  calc |(a + b).toReal - (ra + rb)|
      = |((a + b).toReal - (a.toReal + b.toReal)) + (a.toReal - ra) + (b.toReal - rb)| := by ring_nf
    _ ≤ |((a + b).toReal - (a.toReal + b.toReal)) + (a.toReal - ra)| + |b.toReal - rb| :=
        abs_add_le _ _
    _ ≤ |(a + b).toReal - (a.toReal + b.toReal)| + |a.toReal - ra| + |b.toReal - rb| := by
        gcongr; exact abs_add_le _ _
    _ ≤ _ := by linarith

/-- Multiplication. -/
theorem near_mul {a b : Float32} {ra rb ea eb Ra Rb : ℝ} (ha : Near32 a ra ea) (hb : Near32 b rb eb)
    (hRa : |ra| ≤ Ra) (hRb : |rb| ≤ Rb) (hM : (Ra + ea) * (Rb + eb) ≤ 1e6) :
    Near32 (a * b) (ra * rb) ((Ra + ea) * eb + Rb * ea + u32 * ((Ra + ea) * (Rb + eb)) + η32) := by
  have hea := ha.nonneg; have heb := hb.nonneg
  have hA : |a.toReal| ≤ Ra + ea := ha.bound.trans (by linarith)
  have hB : |b.toReal| ≤ Rb + eb := hb.bound.trans (by linarith)
  have hab : |a.toReal * b.toReal| ≤ (Ra + ea) * (Rb + eb) := by
    rw [abs_mul]; exact mul_le_mul hA hB (abs_nonneg _) (by linarith [abs_nonneg ra])
  obtain ⟨hf, herr⟩ := Float32.mul_err_all ha.1 hb.1 (hab.trans (hM.trans maxFinite32_ge))
  have herr' : |(a * b).toReal - a.toReal * b.toReal| ≤ u32 * |a.toReal * b.toReal| + η32 := herr
  have hRa0 : 0 ≤ Ra := (abs_nonneg _).trans hRa
  have hRb0 : 0 ≤ Rb := (abs_nonneg _).trans hRb
  refine ⟨hf, ?_⟩
  have h1 := ha.2; have h2 := hb.2
  have h3 : u32 * |a.toReal * b.toReal| ≤ u32 * ((Ra + ea) * (Rb + eb)) :=
    mul_le_mul_of_nonneg_left hab u32_nonneg
  have h4 : |a.toReal * b.toReal - ra * rb| ≤ (Ra + ea) * eb + Rb * ea := by
    have : a.toReal * b.toReal - ra * rb = a.toReal * (b.toReal - rb) + rb * (a.toReal - ra) := by
      ring
    rw [this]
    calc _ ≤ |a.toReal * (b.toReal - rb)| + |rb * (a.toReal - ra)| := abs_add_le _ _
      _ = |a.toReal| * |b.toReal - rb| + |rb| * |a.toReal - ra| := by rw [abs_mul, abs_mul]
      _ ≤ (Ra + ea) * eb + Rb * ea := by gcongr
  calc |(a * b).toReal - ra * rb|
      = |((a * b).toReal - a.toReal * b.toReal) + (a.toReal * b.toReal - ra * rb)| := by ring_nf
    _ ≤ |(a * b).toReal - a.toReal * b.toReal| + |a.toReal * b.toReal - ra * rb| := abs_add_le _ _
    _ ≤ _ := by linarith

/-- Multiplication by a float whose value is known exactly (a gain or a filter constant). -/
theorem near_mul_const {a c : Float32} {ra rc ea Ra : ℝ} (ha : Near32 a ra ea) (hc : Near32 c rc 0)
    (hRa : |ra| ≤ Ra) (hM : (Ra + ea) * |rc| ≤ 1e6) :
    Near32 (a * c) (ra * rc) (|rc| * ea + u32 * ((Ra + ea) * |rc|) + η32) := by
  have h := near_mul ha hc hRa le_rfl (by simpa using hM)
  exact h.mono (by simp)

/-- Multiplication of a float whose value is known exactly by another float. -/
theorem near_const_mul {a c : Float32} {ra rc ea Ra : ℝ} (hc : Near32 c rc 0) (ha : Near32 a ra ea)
    (hRa : |ra| ≤ Ra) (hM : |rc| * (Ra + ea) ≤ 1e6) :
    Near32 (c * a) (rc * ra) (|rc| * ea + u32 * (|rc| * (Ra + ea)) + η32) := by
  have h := near_mul hc ha le_rfl hRa (by simpa using hM)
  exact h.mono (by simp)

/-- Division by a float near a positive real. -/
theorem near_div {a b : Float32} {ra rb ea eb Ra : ℝ} (ha : Near32 a ra ea)
    (hb : Near32 b rb eb) (hRa : |ra| ≤ Ra) (hb0 : eb < rb) (hM : (Ra + ea) / (rb - eb) ≤ 1e6) :
    Near32 (a / b) (ra / rb)
      (((Ra + ea) * eb / ((rb - eb) * rb) + ea / rb) + u32 * ((Ra + ea) / (rb - eb)) + η32) := by
  have hea := ha.nonneg; have heb := hb.nonneg
  have hRa0 : 0 ≤ Ra := (abs_nonneg _).trans hRa
  have hrb : 0 < rb := by linarith
  have hb1 : rb - eb ≤ b.toReal := hb.lo
  have hbpos : 0 < b.toReal := by linarith
  have hA : |a.toReal| ≤ Ra + ea := ha.bound.trans (by linarith)
  have hq : |a.toReal / b.toReal| ≤ (Ra + ea) / (rb - eb) := by
    rw [abs_div, abs_of_pos hbpos]
    exact div_le_div₀ (by linarith [abs_nonneg ra]) hA (by linarith) hb1
  obtain ⟨hf, herr⟩ := Float32.div_err_all ha.1 hb.1 hbpos.ne'
    (hq.trans (hM.trans maxFinite32_ge))
  have herr' : |(a / b).toReal - a.toReal / b.toReal| ≤ u32 * |a.toReal / b.toReal| + η32 := herr
  refine ⟨hf, ?_⟩
  have h3 : u32 * |a.toReal / b.toReal| ≤ u32 * ((Ra + ea) / (rb - eb)) :=
    mul_le_mul_of_nonneg_left hq u32_nonneg
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

/-- Negation is exact. -/
theorem near_neg {a : Float32} {r e : ℝ} (ha : Near32 a r e) : Near32 (-a) (-r) e := by
  refine ⟨(Float32.isFinite_neg a).2 ha.1, ?_⟩
  rw [Float32.toReal_neg, show -a.toReal - -r = -(a.toReal - r) by ring, abs_neg]; exact ha.2

/-! ## Exactness: the exact result is a float -/

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

/-- A finite float of value zero (`+0` or `-0`). -/
def Z (x : Float32) : Prop := x.IsFinite ∧ x.toReal = 0

/-- A finite float of value one. -/
def One (x : Float32) : Prop := x.IsFinite ∧ x.toReal = 1

theorem Z.near {x : Float32} (h : Z x) : Near32 x 0 0 := Near32.of_val h.1 h.2
theorem One.near {x : Float32} (h : One x) : Near32 x 1 0 := Near32.of_val h.1 h.2

theorem Z_zero : Z (0 : Float32) := ⟨Float32.isFinite_zero, Float32.toReal_zero⟩
theorem lit0_unpack : (0.0 : Float32).toModel.unpack = .zero .positive := by rfl
/-- The literal `0.0` (`OfScientific`, not `OfNat 0`) is a zero. -/
theorem Z_lit0 : Z (0.0 : Float32) := by
  refine ⟨by rw [Float32.isFinite_iff, lit0_unpack]; rfl, ?_⟩
  rw [Float32.toReal, lit0_unpack]; rfl
theorem One_one : One (1 : Float32) := ⟨Float32.isFinite_one, Float32.toReal_one⟩
theorem lit1_unpack : (1.0 : Float32).toModel.unpack = .finite .positive (2 ^ 23) (-23) (by decide) := by
  rfl
/-- The literal `1.0` is a one. -/
theorem One_lit1 : One (1.0 : Float32) := by
  have : (1.0 : Float32).toModel.unpack = (1 : Float32).toModel.unpack := by
    rw [lit1_unpack, Float32.toModel_unpack_one]
  refine ⟨?_, ?_⟩
  · rw [Float32.isFinite_iff, this]; exact Float32.isFinite_one
  · rw [Float32.toReal, this]; exact Float32.toReal_one

/-- `x · c = x` in value for `c` of value one. -/
theorem mul_one_val {x c : Float32} (hx : x.IsFinite) (hc : One c) :
    (x * c).IsFinite ∧ (x * c).toReal = x.toReal :=
  mul_exact hx hc.1 hx (by rw [hc.2, mul_one])

/-- `c · x = x` in value for `c` of value one. -/
theorem one_mul_val {x c : Float32} (hx : x.IsFinite) (hc : One c) :
    (c * x).IsFinite ∧ (c * x).toReal = x.toReal :=
  mul_exact hc.1 hx hx (by rw [hc.2, one_mul])

/-- `x + z = x` in value for `z` of value zero. -/
theorem add_zero_val {x z : Float32} (hx : x.IsFinite) (hz : Z z) :
    (x + z).IsFinite ∧ (x + z).toReal = x.toReal :=
  add_exact hx hz.1 hx (by rw [hz.2, add_zero])

/-- `z + x = x` in value for `z` of value zero. -/
theorem zero_add_val {x z : Float32} (hx : x.IsFinite) (hz : Z z) :
    (z + x).IsFinite ∧ (z + x).toReal = x.toReal :=
  add_exact hz.1 hx hx (by rw [hz.2, zero_add])

/-- `x - z = x` in value for `z` of value zero. -/
theorem sub_zero_val {x z : Float32} (hx : x.IsFinite) (hz : Z z) :
    (x - z).IsFinite ∧ (x - z).toReal = x.toReal :=
  sub_exact hx hz.1 hx (by rw [hz.2, sub_zero])

/-- A finite float times a zero is a zero. -/
theorem mul_zero_Z {x z : Float32} (hx : x.IsFinite) (hz : Z z) : Z (x * z) :=
  mul_exact hx hz.1 Z_zero.1 (by rw [hz.2, mul_zero, Z_zero.2])

/-- A zero times a finite float is a zero. -/
theorem zero_mul_Z {x z : Float32} (hx : x.IsFinite) (hz : Z z) : Z (z * x) :=
  mul_exact hz.1 hx Z_zero.1 (by rw [hz.2, zero_mul, Z_zero.2])

/-- The sum of two zeros is a zero. -/
theorem add_Z {a b : Float32} (ha : Z a) (hb : Z b) : Z (a + b) :=
  add_exact ha.1 hb.1 Z_zero.1 (by rw [ha.2, hb.2, add_zero, Z_zero.2])

/-- `Near32` through `x · 1`. -/
theorem Near32.mul_one {x c : Float32} {r e : ℝ} (h : Near32 x r e) (hc : One c) : Near32 (x * c) r e :=
  Near32.of_eq_val (mul_one_val h.1 hc).1 (mul_one_val h.1 hc).2 h

/-- `Near32` through `x + 0`. -/
theorem Near32.add_zero {x z : Float32} {r e : ℝ} (h : Near32 x r e) (hz : Z z) : Near32 (x + z) r e :=
  Near32.of_eq_val (add_zero_val h.1 hz).1 (add_zero_val h.1 hz).2 h

/-- `Near32` through `0 + x`. -/
theorem Near32.zero_add {x z : Float32} {r e : ℝ} (h : Near32 x r e) (hz : Z z) : Near32 (z + x) r e :=
  Near32.of_eq_val (zero_add_val h.1 hz).1 (zero_add_val h.1 hz).2 h

/-! ## Comparisons, `constrain_float`, `MIN`, `MAX` -/

theorem not_isNaN {x : Float32} (hx : x.IsFinite) : x.isNaN = false := by
  have := Float32Clip.not_isNaN_of_isFinite hx
  simpa using this

theorem isFinite_true {x : Float32} (hx : x.IsFinite) : x.isFinite = true := hx

theorem lt_true {a b : Float32} (ha : a.IsFinite) (hb : b.IsFinite) (h : a.toReal < b.toReal) :
    a < b := (Float32.lt_iff_toReal_lt ha hb).2 h

theorem not_lt_of {a b : Float32} (ha : a.IsFinite) (hb : b.IsFinite) (h : b.toReal ≤ a.toReal) :
    ¬ a < b := fun h' => absurd ((Float32.lt_iff_toReal_lt ha hb).1 h') (not_lt.2 h)

theorem le_true {a b : Float32} (ha : a.IsFinite) (hb : b.IsFinite) (h : a.toReal ≤ b.toReal) :
    a ≤ b := (Float32.le_iff_toReal_le ha hb).2 h

theorem not_le_of {a b : Float32} (ha : a.IsFinite) (hb : b.IsFinite) (h : b.toReal < a.toReal) :
    ¬ a ≤ b := fun h' => absurd ((Float32.le_iff_toReal_le ha hb).1 h') (not_le.2 h)

/-- `constrain_float` of a finite value inside the bounds returns it (as a float). -/
theorem constrain_float_of_le {x lo hi : Float32} (hx : x.IsFinite) (hlo : lo.IsFinite)
    (hhi : hi.IsFinite) (h1 : lo.toReal ≤ x.toReal) (h2 : x.toReal ≤ hi.toReal) :
    constrain_float x lo hi = x := by
  show Float32Clip.constrain_float x lo hi = x
  unfold Float32Clip.constrain_float
  rw [if_neg (Float32Clip.not_isNaN_of_isFinite hx), if_neg (not_lt_of hx hlo h1)]
  have : ¬ x > hi := not_lt_of hhi hx h2
  rw [if_neg this]

/-- `constrain_float` of a float near a value well inside the bounds returns it. -/
theorem constrain_float_of_near {x lo hi : Float32} {r e : ℝ} (hx : Near32 x r e)
    (hlo : lo.IsFinite) (hhi : hi.IsFinite) (h1 : lo.toReal ≤ r - e) (h2 : r + e ≤ hi.toReal) :
    constrain_float x lo hi = x :=
  constrain_float_of_le hx.1 hlo hhi (h1.trans hx.lo) (hx.hi.trans h2)

/-- `constrain_float` is finite and between its bounds for every input. -/
theorem constrain_float_mem {lo hi : Float32} (hlo : lo.IsFinite) (hhi : hi.IsFinite)
    (hle : lo.toReal ≤ hi.toReal) (hsum : |lo.toReal + hi.toReal| ≤ maxFinite32) (x : Float32) :
    (constrain_float x lo hi).IsFinite ∧ lo.toReal ≤ (constrain_float x lo hi).toReal ∧
      (constrain_float x lo hi).toReal ≤ hi.toReal :=
  Float32ClipAP.constrain_float_spec hlo hhi hle hsum x

/-- `MIN a b = a` when `a < b`. -/
theorem MIN_eq_left {a b : Float32} (ha : a.IsFinite) (hb : b.IsFinite) (h : a.toReal < b.toReal) :
    MIN a b = a := by
  unfold MIN; rw [if_pos (lt_true ha hb h)]

/-- `MIN a b = b` when `b ≤ a`. -/
theorem MIN_eq_right {a b : Float32} (ha : a.IsFinite) (hb : b.IsFinite) (h : b.toReal ≤ a.toReal) :
    MIN a b = b := by
  unfold MIN; rw [if_neg (not_lt_of ha hb h)]

/-- `MAX a b = a` when `b < a`. -/
theorem MAX_eq_left {a b : Float32} (ha : a.IsFinite) (hb : b.IsFinite) (h : b.toReal < a.toReal) :
    MAX a b = a := by
  unfold MAX; rw [if_pos (lt_true hb ha h)]

/-- `MAX a b = b` when `a ≤ b`. -/
theorem MAX_eq_right {a b : Float32} (ha : a.IsFinite) (hb : b.IsFinite) (h : a.toReal ≤ b.toReal) :
    MAX a b = b := by
  unfold MAX; rw [if_neg (not_lt_of hb ha h)]

/-- `MIN` of finite floats is one of them, so finite with value the real minimum. -/
theorem MIN_val {a b : Float32} (ha : a.IsFinite) (hb : b.IsFinite) :
    (MIN a b).IsFinite ∧ (MIN a b).toReal = min a.toReal b.toReal := by
  rcases lt_or_ge a.toReal b.toReal with h | h
  · rw [MIN_eq_left ha hb h, min_eq_left h.le]; exact ⟨ha, rfl⟩
  · rw [MIN_eq_right ha hb h, min_eq_right h]; exact ⟨hb, rfl⟩

/-- `MAX` of finite floats is one of them, so finite with value the real maximum. -/
theorem MAX_val {a b : Float32} (ha : a.IsFinite) (hb : b.IsFinite) :
    (MAX a b).IsFinite ∧ (MAX a b).toReal = max a.toReal b.toReal := by
  rcases lt_or_ge b.toReal a.toReal with h | h
  · rw [MAX_eq_left ha hb h, max_eq_left h.le]; exact ⟨ha, rfl⟩
  · rw [MAX_eq_right ha hb h, max_eq_right h]; exact ⟨hb, rfl⟩

/-! ## Narrowing `double → float` -/

/-- The C conversion `(float)x` (`Float.toFloat32`, an opaque `extern` constant in core Lean) rounds
to nearest on `|x| ≤ R`: the result is finite and within `2⁻²⁴ |x| + 2⁻¹⁵⁰`. IEEE 754 (5.4.2)
requires it for every `|x|` below the binary32 overflow threshold. -/
-- <<NarrowSpec>>
structure NarrowSpec (R : ℝ) : Prop where
  err : ∀ x : Float, x.IsFinite → |x.toReal| ≤ R →
    (Float.toFloat32 x).IsFinite ∧ |(Float.toFloat32 x).toReal - x.toReal| ≤ u32 * |x.toReal| + η32
-- <</NarrowSpec>>

/-- binary64 subtraction. -/
theorem near64_sub {a b : Float} {ra rb ea eb B : ℝ} (ha : Near64 a ra ea) (hb : Near64 b rb eb)
    (hB : |ra - rb| + ea + eb ≤ B) (hBM : B ≤ 1e6) :
    Near64 (a - b) (ra - rb) (ea + eb + (2 : ℝ) ^ (-53 : ℤ) * B) := by
  have hab : |a.toReal - b.toReal| ≤ B := by
    have h1 := ha.2; have h2 := hb.2
    calc |a.toReal - b.toReal| = |(ra - rb) + (a.toReal - ra) - (b.toReal - rb)| := by ring_nf
      _ ≤ |(ra - rb) + (a.toReal - ra)| + |b.toReal - rb| := abs_sub _ _
      _ ≤ |ra - rb| + |a.toReal - ra| + |b.toReal - rb| := by
        gcongr; exact abs_add_le _ _
      _ ≤ B := by linarith
  have hmax : (1e6 : ℝ) ≤ UnpackedFloat.maxFinite := by
    unfold UnpackedFloat.maxFinite
    have h : (1 : ℝ) ≤ 2 ^ (971 : ℤ) := one_le_zpow₀ one_le_two (by norm_num)
    have h2 : (1e6 : ℝ) ≤ (2 ^ 53 - 1) := by norm_num
    have h3 : (2 ^ 53 - 1 : ℝ) * 1 ≤ (2 ^ 53 - 1) * 2 ^ (971 : ℤ) :=
      mul_le_mul_of_nonneg_left h (by norm_num)
    generalize (2 : ℝ) ^ (971 : ℤ) = X at h3 ⊢
    linarith
  obtain ⟨hf, herr⟩ := Float.sub_err_all ha.1 hb.1 (hab.trans (hBM.trans hmax))
  refine ⟨hf, ?_⟩
  have h1 := ha.2; have h2 := hb.2
  have h3 : (2 : ℝ) ^ (-53 : ℤ) * |a.toReal - b.toReal| ≤ (2 : ℝ) ^ (-53 : ℤ) * B :=
    mul_le_mul_of_nonneg_left hab (zpow_pos two_pos _).le
  calc |(a - b).toReal - (ra - rb)|
      = |((a - b).toReal - (a.toReal - b.toReal)) + (a.toReal - ra) - (b.toReal - rb)| := by ring_nf
    _ ≤ |((a - b).toReal - (a.toReal - b.toReal)) + (a.toReal - ra)| + |b.toReal - rb| :=
        abs_sub _ _
    _ ≤ |(a - b).toReal - (a.toReal - b.toReal)| + |a.toReal - ra| + |b.toReal - rb| := by
        gcongr; exact abs_add_le _ _
    _ ≤ _ := by linarith

/-- Narrowing of a binary64 float near `r`. -/
theorem near_narrow {R : ℝ} (hN : NarrowSpec R) {a : Float} {r e : ℝ} (ha : Near64 a r e)
    (hR : |r| + e ≤ R) : Near32 (Float.toFloat32 a) r (e + u32 * (|r| + e) + η32) := by
  have hA : |a.toReal| ≤ |r| + e := by
    have := ha.2
    calc |a.toReal| = |(a.toReal - r) + r| := by ring_nf
      _ ≤ |a.toReal - r| + |r| := abs_add_le _ _
      _ ≤ _ := by linarith
  obtain ⟨hf, herr⟩ := hN.err a ha.1 (hA.trans hR)
  refine ⟨hf, ?_⟩
  have h3 : u32 * |a.toReal| ≤ u32 * (|r| + e) := mul_le_mul_of_nonneg_left hA u32_nonneg
  have := ha.2
  calc |(Float.toFloat32 a).toReal - r|
      = |((Float.toFloat32 a).toReal - a.toReal) + (a.toReal - r)| := by ring_nf
    _ ≤ |(Float.toFloat32 a).toReal - a.toReal| + |a.toReal - r| := abs_add_le _ _
    _ ≤ _ := by linarith

/-! ## Literals and computed constants -/

/-- The value of a positive binary32 float read off its unpacked form. -/
theorem lit32 {x : Float32} (m : ℕ) (e : ℤ) (hm : 0 < m)
    (h : x.toModel.unpack = .finite .positive m e hm) :
    x.IsFinite ∧ x.toReal = (m : ℝ) * 2 ^ e := by
  refine ⟨?_, ?_⟩
  · rw [Float32.isFinite_iff, h]; rfl
  · rw [Float32.toReal, h]; simp [UnpackedFloat.toReal, Sign.apply]

/-- The main-loop period `_last_loop_time_s = float(2500) * 1.0e-6f` (`Copter.scheduler_loop`,
`AP_Scheduler.cpp:363`), bits `0x3B23D70A`. -/
def dtF : Float32 := Float32.ofNat 2500 * 1.0e-6

theorem dtF_unpack : dtF.toModel.unpack = .finite .positive 10737418 (-32) (by decide) := by rfl
/-- The first tick's period `1.0f / SCHED_LOOP_RATE` has the same bits. -/
theorem dtF_first : (1.0 / Copter.SCHED_LOOP_RATE).toModel.unpack = dtF.toModel.unpack := by rfl
theorem dtF_toBits : dtF.toBits = 992204554 := by decide

theorem dtF_val : dtF.IsFinite ∧ dtF.toReal = CopterVert.dtc := by
  obtain ⟨h1, h2⟩ := lit32 _ _ _ dtF_unpack
  exact ⟨h1, by rw [h2, CopterVert.dtc]; norm_num⟩

theorem near_dtF : Near32 dtF CopterVert.dtc 0 := Near32.of_val dtF_val.1 dtF_val.2

/-- `alpha_v = calc_lowpass_alpha_dt(dt, 5)`, the velocity error filter. -/
theorem alpha5_unpack :
    (calc_lowpass_alpha_dt dtF AC_PosControl.POSCONTROL_D_VEL_FILT_HZ).toModel.unpack =
      .finite .positive 9773802 (-27) (by decide) := by rfl
/-- `alpha_a = calc_lowpass_alpha_dt(dt, 20)`, the acceleration error filter. -/
theorem alpha20_unpack :
    (calc_lowpass_alpha_dt dtF AC_PosControl.POSCONTROL_D_ACC_FILT_HZ).toModel.unpack =
      .finite .positive 16042859 (-26) (by decide) := by rfl
/-- `alpha_m = calc_lowpass_alpha_dt(dt, 2)`, the motors' throttle filter. -/
theorem alpha2_unpack :
    (calc_lowpass_alpha_dt dtF AC_PosControl.POSCONTROL_THROTTLE_CUTOFF_FREQ_HZ).toModel.unpack =
      .finite .positive 16352567 (-29) (by decide) := by rfl
/-- `calc_lowpass_alpha_dt(dt, 0) = 1` (`FLTT = FLTD = 0`: no filter). -/
theorem alpha0_eq : calc_lowpass_alpha_dt dtF 0.0 = 1.0 := by
  unfold calc_lowpass_alpha_dt
  have h1 : (is_negative dtF || is_negative 0.0) = false := by decide
  have h2 : is_zero (0.0 : Float32) = true := by decide
  rw [if_neg (by simp [h1]), if_pos h2]

theorem near_av : Near32 (calc_lowpass_alpha_dt dtF AC_PosControl.POSCONTROL_D_VEL_FILT_HZ)
    CopterVert.av 0 := by
  obtain ⟨h1, h2⟩ := lit32 _ _ _ alpha5_unpack
  exact Near32.of_val h1 (by rw [h2, CopterVert.av]; norm_num)

theorem near_aa : Near32 (calc_lowpass_alpha_dt dtF AC_PosControl.POSCONTROL_D_ACC_FILT_HZ)
    CopterVert.aa 0 := by
  obtain ⟨h1, h2⟩ := lit32 _ _ _ alpha20_unpack
  exact Near32.of_val h1 (by rw [h2, CopterVert.aa]; norm_num)

theorem near_am : Near32 (calc_lowpass_alpha_dt dtF AC_PosControl.POSCONTROL_THROTTLE_CUTOFF_FREQ_HZ)
    CopterVert.am 0 := by
  obtain ⟨h1, h2⟩ := lit32 _ _ _ alpha2_unpack
  exact Near32.of_val h1 (by rw [h2, CopterVert.am]; norm_num)

/-- `PSC_D_POS_P = 1.0f`. -/
theorem one_D_POS_P : One AC_PosControl.POSCONTROL_D_POS_P := One_lit1

/-- `PSC_D_VEL_P = 5.0f`. -/
theorem near_kv : Near32 AC_PosControl.POSCONTROL_D_VEL_P CopterVert.kv 0 := by
  obtain ⟨h1, h2⟩ := lit32 10485760 (-21) (by decide)
    (x := AC_PosControl.POSCONTROL_D_VEL_P) (by rfl)
  exact Near32.of_val h1 (by rw [h2, CopterVert.kv]; norm_num)

/-- `PSC_D_ACC_P = 0.05f`. -/
theorem near_kp : Near32 AC_PosControl.POSCONTROL_D_ACC_P CopterVert.kp 0 := by
  obtain ⟨h1, h2⟩ := lit32 13421773 (-28) (by decide)
    (x := AC_PosControl.POSCONTROL_D_ACC_P) (by rfl)
  exact Near32.of_val h1 (by rw [h2, CopterVert.kp]; norm_num)

/-- `PSC_D_ACC_I = 0.1f`. -/
theorem near_ki : Near32 AC_PosControl.POSCONTROL_D_ACC_I CopterVert.ki 0 := by
  obtain ⟨h1, h2⟩ := lit32 13421773 (-27) (by decide)
    (x := AC_PosControl.POSCONTROL_D_ACC_I) (by rfl)
  exact Near32.of_val h1 (by rw [h2, CopterVert.ki]; norm_num)

/-- `PSC_D_ACC_IMAX = 0.8f`, exact value `13421773 / 2²⁴`. -/
theorem val_imax : AC_PosControl.POSCONTROL_D_ACC_IMAX.IsFinite ∧
    AC_PosControl.POSCONTROL_D_ACC_IMAX.toReal = 13421773 / 16777216 := by
  obtain ⟨h1, h2⟩ := lit32 13421773 (-24) (by decide)
    (x := AC_PosControl.POSCONTROL_D_ACC_IMAX) (by rfl)
  exact ⟨h1, by rw [h2]; norm_num⟩

/-- `GRAVITY_MSS = 9.80665f`, exact value `5141509 / 2¹⁹`. -/
noncomputable def Gf : ℝ := 5141509 / 524288

theorem near_G : Near32 GRAVITY_MSS Gf 0 := by
  obtain ⟨h1, h2⟩ := lit32 10283018 (-20) (by decide) (x := GRAVITY_MSS) (by rfl)
  exact Near32.of_val h1 (by rw [h2, Gf]; norm_num)

/-- The gravity constant's mismatch, `GRAVITY_MSS - 9.80665 ≈ 1.6174e-7`. -/
theorem G_sub_g : Gf - CopterVert.g = 1617431640625 / 10000000000000000000 := by
  norm_num [Gf, CopterVert.g]

/-- `MOT_THST_HOVER 0.4444` (`sim/params/copter-cf2x.txt`), the `float` nearest to `0.4444`. -/
def hoverF : Float32 := 0.4444

/-- Its exact value `H = 7455795 / 2²⁴`. -/
noncomputable def Hf : ℝ := 7455795 / 16777216

theorem near_H : Near32 hoverF Hf 0 := by
  obtain ⟨h1, h2⟩ := lit32 14911590 (-25) (by decide) (x := hoverF) (by rfl)
  exact Near32.of_val h1 (by rw [h2, Hf]; norm_num)

/-- The parameter parser reads `0.4444` to the same float (`Decimal.toFloat32`, one rounding). -/
theorem hoverF_parse : Copter.Text.Decimal.toFloat32 ⟨false, 4444, -4⟩ = hoverF := by rfl

/-- The equilibrium of the acceleration integrator, `I* = H - 4/9 ≈ -4.4432e-5`. -/
noncomputable def Istar : ℝ := Hf - 4 / 9

/-- `FLT_EPSILON = 2⁻²³`. -/
theorem val_FLT_EPSILON : FLT_EPSILON.IsFinite ∧ FLT_EPSILON.toReal = 1 / 8388608 := by
  obtain ⟨h1, h2⟩ := lit32 8388608 (-46) (by decide) (x := FLT_EPSILON) (by rfl)
  exact ⟨h1, by rw [h2]; norm_num⟩

/-- `POSCONTROL_THROTTLE_CUTOFF_FREQ_HZ = 2.0f`. -/
theorem val_cutoff2 : AC_PosControl.POSCONTROL_THROTTLE_CUTOFF_FREQ_HZ.IsFinite ∧
    AC_PosControl.POSCONTROL_THROTTLE_CUTOFF_FREQ_HZ.toReal = 2 := by
  obtain ⟨h1, h2⟩ := lit32 8388608 (-22) (by decide)
    (x := AC_PosControl.POSCONTROL_THROTTLE_CUTOFF_FREQ_HZ) (by rfl)
  exact ⟨h1, by rw [h2]; norm_num⟩

/-- `PSC_D_VEL_FLTE = 5.0f`. -/
theorem val_cutoff5 : AC_PosControl.POSCONTROL_D_VEL_FILT_HZ.IsFinite ∧
    AC_PosControl.POSCONTROL_D_VEL_FILT_HZ.toReal = 5 := by
  obtain ⟨h1, h2⟩ := lit32 10485760 (-21) (by decide)
    (x := AC_PosControl.POSCONTROL_D_VEL_FILT_HZ) (by rfl)
  exact ⟨h1, by rw [h2]; norm_num⟩

/-- `PSC_D_ACC_FLTE = 20.0f`. -/
theorem val_cutoff20 : AC_PosControl.POSCONTROL_D_ACC_FILT_HZ.IsFinite ∧
    AC_PosControl.POSCONTROL_D_ACC_FILT_HZ.toReal = 20 := by
  obtain ⟨h1, h2⟩ := lit32 10485760 (-19) (by decide)
    (x := AC_PosControl.POSCONTROL_D_ACC_FILT_HZ) (by rfl)
  exact ⟨h1, by rw [h2]; norm_num⟩

/-! ## `abs`, `is_zero`, `is_positive`, `is_negative` on finite floats -/

theorem canonicalIn_abs' {spec : Format} {u : UnpackedFloat} (h : CanonicalIn spec u) :
    CanonicalIn spec u.abs := by
  cases u <;> simp_all [CanonicalIn, UnpackedFloat.abs]

theorem abs_unpack (x : Float32) : x.abs.toModel.unpack = x.toModel.unpack.abs :=
  Float32.Model.unpack_pack_of_canonicalIn (canonicalIn_abs' x.canonicalIn_unpack)

/-- `fabsf` is exact. -/
theorem abs_val (x : Float32) : x.abs.toReal = |x.toReal| := by
  rw [Float32.toReal, abs_unpack, Float32.toReal]
  cases x.toModel.unpack with
  | finite s m e hm =>
    cases s <;> simp [UnpackedFloat.abs, UnpackedFloat.toReal, Sign.apply, abs_mul]
  | _ => simp [UnpackedFloat.abs, UnpackedFloat.toReal]

theorem abs_isFinite {x : Float32} (hx : x.IsFinite) : x.abs.IsFinite := by
  rw [Float32.isFinite_iff, abs_unpack]
  rw [Float32.isFinite_iff] at hx
  cases h : x.toModel.unpack <;> simp_all [UnpackedFloat.abs, UnpackedFloat.isFinite]

/-- `-1.0f * FLT_EPSILON = -2⁻²³`. -/
theorem val_negeps : ((-1.0 : Float32) * FLT_EPSILON).IsFinite ∧
    ((-1.0 : Float32) * FLT_EPSILON).toReal = -(1 / 8388608) := by
  have h : ((-1.0 : Float32) * FLT_EPSILON).toModel.unpack =
      .finite .negative 8388608 (-46) (by decide) := by rfl
  refine ⟨by rw [Float32.isFinite_iff, h]; rfl, ?_⟩
  rw [Float32.toReal, h]; simp [UnpackedFloat.toReal, Sign.apply]; norm_num

theorem is_positive_true {x : Float32} (hx : x.IsFinite) (h : 1 / 8388608 ≤ x.toReal) :
    is_positive x = true := by
  unfold is_positive
  have := le_true val_FLT_EPSILON.1 hx (by rw [val_FLT_EPSILON.2]; exact h)
  simpa using this

theorem is_positive_false {x : Float32} (hx : x.IsFinite) (h : x.toReal < 1 / 8388608) :
    is_positive x = false := by
  unfold is_positive
  have := not_le_of val_FLT_EPSILON.1 hx (by rw [val_FLT_EPSILON.2]; exact h)
  simpa using this

theorem is_negative_false {x : Float32} (hx : x.IsFinite) (h : -(1 / 8388608) < x.toReal) :
    is_negative x = false := by
  unfold is_negative
  have := not_le_of hx val_negeps.1 (by rw [val_negeps.2]; exact h)
  simpa using this

theorem is_negative_true {x : Float32} (hx : x.IsFinite) (h : x.toReal ≤ -(1 / 8388608)) :
    is_negative x = true := by
  unfold is_negative
  have := le_true hx val_negeps.1 (by rw [val_negeps.2]; exact h)
  simpa using this

theorem is_zero_false {x : Float32} (hx : x.IsFinite) (h : 1 / 8388608 ≤ |x.toReal|) :
    is_zero x = false := by
  unfold is_zero
  have := not_lt_of (abs_isFinite hx) val_FLT_EPSILON.1 (by rw [val_FLT_EPSILON.2, abs_val]; exact h)
  simpa using this

theorem is_zero_true {x : Float32} (hx : x.IsFinite) (h : |x.toReal| < 1 / 8388608) :
    is_zero x = true := by
  unfold is_zero
  have := lt_true (abs_isFinite hx) val_FLT_EPSILON.1 (by rw [val_FLT_EPSILON.2, abs_val]; exact h)
  simpa using this

/-! ## The rational constants of `CopterVert`, as equations -/

theorem av_eq : av = 4886901 / 67108864 := rfl
theorem aa_eq : aa = 16042859 / 67108864 := rfl
theorem am_eq : am = 16352567 / 536870912 := rfl
theorem kp_eq : kp = 13421773 / 268435456 := rfl
theorem ki_eq : ki = 13421773 / 134217728 := rfl
theorem kv_eq : kv = 5 := rfl
theorem kpos_eq : kpos = 1 := rfl
theorem dtc_eq : dtc = 5368709 / 2147483648 := rfl
theorem g_eq : g = 980665 / 100000 := rfl
theorem k_eq : k = 9 / 4 * (980665 / 100000) := rfl
theorem h_eq : CopterVert.h = 1 / 400 := rfl
theorem Gf_eq : Gf = 5141509 / 524288 := rfl
theorem Hf_eq : Hf = 7455795 / 16777216 := rfl

end Contracts.CopterVertNear
