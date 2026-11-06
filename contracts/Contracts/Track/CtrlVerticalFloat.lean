import FloatModel.Lit
import Contracts.Mission.NavFloat
import Contracts.Track.Vertical

/-!
# Float lemmas for the vertical controller lemmas (C-series, `CTRL_VERTICAL.md`)

The tools the C-lemmas of `CtrlVerticalPID.lean` and `CtrlVertical.lean` share, on top of the
`A32`/`A64` approximation calculus of `Contracts/Mission/NavFloat.lean`:

* exactness (`f32_add_exact`, `f32_mul_one`, `f32_mul_zero`, ...): a rounded operation whose exact
  result is a float returns it (the bracket lemmas of `FloatModel`);
* the literals the code writes `Float.toFloat32 d` (`LibmSpec.f64ToF32_exact`), and `(float) π`
  (`f32_pi`, within `2⁻²⁴` relative of the `double` `π`: `LibmSpec.f64ToF32` does not determine
  it, both neighbours of `π` are within that bound);
* the low-pass coefficients `calc_lowpass_alpha_dt(0.0025f, fc)` for `fc = 20, 5, 2` (`alpha20`,
  `alpha5`, `alpha2`), within `2⁻²²` of the exact float values `αA`, `αV`, `αT` of
  `Contracts.Track.Vertical` (computed with the `float` `π`), and `fc = 0` (`alpha0`: exactly `1`);
* `A32.filt`: the low-pass step `e + α (x - e)` with an approximate input and coefficient;
  `A32.filt2`, `A32.lpf2`: the same with sharp constants;
* `PiF32` (an explicit float fact: `(float) π` is the nearest float `3.14159274f`) and, with it,
  the coefficients exactly (`alphaA`, `alphaV`, `alphaT`).
-/

namespace Contracts.Track.CtrlV

open Float.Model UnpackedFloat Contracts.Mission

noncomputable section

/-! ## The comparisons of `AP_Math` (as in `Contracts/Mission/NavStop.lean`) -/

section Cmp
open AC_PosControl_lib

theorem f32_toReal_eps : (1.1920929e-7 : Float32).toReal = 2 ^ (-23 : ℤ) := by
  rw [f32_toReal_1p1920929Em7]; norm_num

theorem isPos_iff {x : Float32} (hx : x.IsFinite) :
    is_positive_float x = true ↔ 2 ^ (-23 : ℤ) ≤ x.toReal := by
  show decide ((1.1920929e-7 : Float32) ≤ x) = true ↔ _
  rw [decide_eq_true_iff, Float32.le_iff_toReal_le f32_isFinite_1p1920929Em7 hx, f32_toReal_eps]

theorem isPosAP_iff {x : Float32} (hx : x.IsFinite) :
    is_positive_AP_Float x = true ↔ 2 ^ (-23 : ℤ) ≤ x.toReal := by
  show decide ((1.1920929e-7 : Float32) ≤ x) = true ↔ _
  rw [decide_eq_true_iff, Float32.le_iff_toReal_le f32_isFinite_1p1920929Em7 hx, f32_toReal_eps]

theorem isZero_iff {x : Float32} (hx : x.IsFinite) :
    is_zero_float x = true ↔ |x.toReal| < 2 ^ (-23 : ℤ) := by
  show decide (Float32.abs x < (1.1920929e-7 : Float32)) = true ↔ _
  rw [decide_eq_true_iff, Float32.lt_iff_toReal_lt ((Float32.isFinite_abs x).2 hx) f32_isFinite_1p1920929Em7,
    Float32.toReal_abs, f32_toReal_eps]

/-- `is_negative` of a nonnegative float is false. -/
theorem isNeg_false (hL : LibmSpec) {x : Float32} (hx : x.IsFinite) (h0 : 0 ≤ x.toReal) :
    is_negative_float x = false := by
  show decide (Float32.toFloat x ≤ -(1.0 : Float) * Float32.toFloat (1.1920929e-7 : Float32)) = false
  rw [decide_eq_false_iff_not]
  obtain ⟨f1, e1⟩ := hL.f32ToF64 x hx
  obtain ⟨f2, e2⟩ := hL.f32ToF64 _ f32_isFinite_1p1920929Em7
  have fm1 : (-(1.0 : Float)).IsFinite := (Float.isFinite_neg _).2 f64_isFinite_1p0
  have em1 : (-(1.0 : Float)).toReal = -1 := by rw [Float.toReal_neg, f64_toReal_1p0]
  have hm := A64.mul (A64.of_exact fm1) (A64.of_exact f2)
    (by rw [e2, f32_toReal_eps, em1]; norm_num)
  rw [Float.le_iff_toReal_le f1 hm.1, e1]
  intro h
  have := (abs_le.1 hm.2).2
  rw [e2, f32_toReal_eps, em1] at this
  have hη := η64_small
  simp only [u64] at this
  norm_num at this
  linarith

/-- `constrain_value` of finite floats with `low ≤ high` is the real clamp. -/
theorem constrain_spec {amt low high : Float32} (line : UInt32) (ha : amt.IsFinite)
    (hl : low.IsFinite) (hh : high.IsFinite) (hlh : low.toReal ≤ high.toReal) :
    (constrain_value_line_float amt low high line).IsFinite ∧
      (constrain_value_line_float amt low high line).toReal =
        max low.toReal (min high.toReal amt.toReal) := by
  simp only [constrain_value_line_float, Id.run, Float32.not_isNaN_of_isFinite ha,
    Bool.false_eq_true, ite_false, id_pure_eq]
  by_cases h1 : amt < low
  · rw [ite_eq_left h1]
    have := (Float32.lt_iff_toReal_lt ha hl).1 h1
    exact ⟨hl, by rw [min_eq_right (by linarith), max_eq_left this.le]⟩
  · rw [ite_eq_right h1]
    have h1' : low.toReal ≤ amt.toReal := not_lt.1 ((Float32.lt_iff_toReal_lt ha hl).not.1 h1)
    by_cases h2 : amt > high
    · rw [ite_eq_left h2]
      have := (Float32.lt_iff_toReal_lt hh ha).1 h2
      exact ⟨hh, by rw [min_eq_left this.le, max_eq_right hlh]⟩
    · rw [ite_eq_right h2]
      have h2' : amt.toReal ≤ high.toReal :=
        not_lt.1 ((Float32.lt_iff_toReal_lt hh ha).not.1 h2)
      exact ⟨ha, by rw [min_eq_right h2', max_eq_right h1']⟩

end Cmp

/-! ## Exact operations: a result whose exact value is a float is computed exactly -/

theorem f32_add_exact {a b c : Float32} (ha : a.IsFinite) (hb : b.IsFinite) (hc : c.IsFinite)
    (h : a.toReal + b.toReal = c.toReal) : (a + b).IsFinite ∧ (a + b).toReal = c.toReal := by
  have hm : |a.toReal + b.toReal| ≤ maxFinite32 := h ▸ Float32.abs_toReal_le_maxFinite c
  obtain ⟨hf, -⟩ := Float32.add_err_all ha hb hm
  have := Float32.add_bracket ha hb hm hc
  exact ⟨hf, le_antisymm (this.2 h.le) (this.1 h.ge)⟩

theorem f32_sub_exact {a b c : Float32} (ha : a.IsFinite) (hb : b.IsFinite) (hc : c.IsFinite)
    (h : a.toReal - b.toReal = c.toReal) : (a - b).IsFinite ∧ (a - b).toReal = c.toReal := by
  have hm : |a.toReal - b.toReal| ≤ maxFinite32 := h ▸ Float32.abs_toReal_le_maxFinite c
  obtain ⟨hf, -⟩ := Float32.sub_err_all ha hb hm
  have := Float32.sub_bracket ha hb hm hc
  exact ⟨hf, le_antisymm (this.2 h.le) (this.1 h.ge)⟩

theorem f32_mul_exact {a b c : Float32} (ha : a.IsFinite) (hb : b.IsFinite) (hc : c.IsFinite)
    (h : a.toReal * b.toReal = c.toReal) : (a * b).IsFinite ∧ (a * b).toReal = c.toReal := by
  have hm : |a.toReal * b.toReal| ≤ maxFinite32 := h ▸ Float32.abs_toReal_le_maxFinite c
  obtain ⟨hf, -⟩ := Float32.mul_err_all ha hb hm
  have := Float32.mul_bracket ha hb hm hc
  exact ⟨hf, le_antisymm (this.2 h.le) (this.1 h.ge)⟩

theorem f32_add_zero {a b : Float32} (ha : a.IsFinite) (hb : b.IsFinite) (h0 : b.toReal = 0) :
    (a + b).IsFinite ∧ (a + b).toReal = a.toReal :=
  f32_add_exact ha hb ha (by rw [h0, add_zero])

theorem f32_zero_add {a b : Float32} (ha : a.IsFinite) (hb : b.IsFinite) (h0 : a.toReal = 0) :
    (a + b).IsFinite ∧ (a + b).toReal = b.toReal :=
  f32_add_exact ha hb hb (by rw [h0, zero_add])

theorem f32_mul_one {a b : Float32} (ha : a.IsFinite) (hb : b.IsFinite) (h1 : b.toReal = 1) :
    (a * b).IsFinite ∧ (a * b).toReal = a.toReal :=
  f32_mul_exact ha hb ha (by rw [h1, mul_one])

theorem f32_mul_zero {a b : Float32} (ha : a.IsFinite) (hb : b.IsFinite) (h0 : b.toReal = 0) :
    (a * b).IsFinite ∧ (a * b).toReal = 0 := by
  have := f32_mul_exact ha hb Float32.isFinite_lit_zero (by rw [h0, mul_zero, Float32.toReal_lit_zero])
  rwa [Float32.toReal_lit_zero] at this

/-! ## The literals that are written `Float.toFloat32 d` -/

theorem f32_ofF64_one (hL : LibmSpec) :
    (Float.toFloat32 (1.0 : Float)).IsFinite ∧ (Float.toFloat32 (1.0 : Float)).toReal = 1 := by
  have := hL.f64ToF32_exact (1.0 : Float) (1.0 : Float32) f64_isFinite_1p0 Float32.isFinite_lit_one
    (by rw [Float32.toReal_lit_one, f64_toReal_1p0])
  rwa [f64_toReal_1p0] at this

theorem f32_ofF64_zero (hL : LibmSpec) :
    (Float.toFloat32 (0.0 : Float)).IsFinite ∧ (Float.toFloat32 (0.0 : Float)).toReal = 0 := by
  have := hL.f64ToF32_exact (0.0 : Float) (0.0 : Float32) Float.isFinite_lit_zero
    Float32.isFinite_lit_zero (by rw [Float32.toReal_lit_zero, Float.toReal_lit_zero])
  rwa [Float.toReal_lit_zero] at this

/-- `(float) π` (the `double` literal narrowed): within `2⁻²⁴` relative of the `double` `π`. -/
theorem f32_pi (hL : LibmSpec) :
    A32 (Float.toFloat32 (3.1415926535897931 : Float)) (884279719003555 / 281474976710656)
      (u32 * (884279719003555 / 281474976710656) + η32) := by
  have hd : (3.1415926535897931 : Float).IsFinite := f64_isFinite_3p1415926535897931
  have hdv := f64_toReal_3p1415926535897931
  have hm : |(3.1415926535897931 : Float).toReal| ≤ maxFinite32 := by
    rw [hdv]; have : (884279719003555 / 281474976710656 : ℝ) ≤ capF := by norm_num [capF]
    rw [abs_of_pos (by norm_num)]; linarith [capF_le_max32]
  obtain ⟨hf, he⟩ := hL.f64ToF32 _ hd hm
  refine ⟨hf, ?_⟩
  rw [hdv, abs_of_pos (by norm_num : (0 : ℝ) < 884279719003555 / 281474976710656)] at he
  have := rnd32 (fl := (Float.toFloat32 (3.1415926535897931 : Float)).toReal)
    (x := 884279719003555 / 281474976710656) (by
      rw [abs_of_pos (by norm_num : (0 : ℝ) < 884279719003555 / 281474976710656)]; exact he)
  rwa [abs_of_pos (by norm_num : (0 : ℝ) < 884279719003555 / 281474976710656)] at this


/-- The code's sample period, `2500 · 1e-6f = 0.0025f`, as a real. -/
def dtR : ℝ := 5368709 / 2147483648

theorem u32_eq : u32 = 1 / 16777216 := by norm_num [u32]

/-- Numeric side conditions: `u32` as a fraction, `η32` bounded. -/
macro "numle" : tactic => `(tactic| (
  have hη1 := η32_small; have hη0 := η32_pos
  rw [u32_eq] at *
  norm_num [capF] at *
  try nlinarith))


open AC_PosControl_lib in
theorem alpha20 (hL : LibmSpec) {dt fc : Float32} (hdt : dt.IsFinite) (hdtv : dt.toReal = dtR)
    (hfc : fc.IsFinite) (hfcv : fc.toReal = 20) :
    A32 (calc_lowpass_alpha_dt dt fc) (16042859 / 67108864) (1 / 2 ^ 22) := by
  have hn1 : is_negative_float dt = false := isNeg_false hL hdt (by rw [hdtv, dtR]; norm_num)
  have hn2 : is_negative_float fc = false := isNeg_false hL hfc (by rw [hfcv]; norm_num)
  have hz1 : is_zero_float fc = false := by
    rw [Bool.eq_false_iff, ne_eq, isZero_iff hfc, hfcv]; norm_num
  have hz2 : is_zero_float dt = false := by
    rw [Bool.eq_false_iff, ne_eq, isZero_iff hdt, hdtv, dtR]; norm_num
  simp only [calc_lowpass_alpha_dt, Id.run, hn1, hn2, hz1, hz2, Bool.or_false, Bool.false_eq_true,
    ite_false, id_pure_eq]
  have p1 := f32_pi hL
  have t2 : A32 (Int32.toFloat32 (2 : Int32)) 2 0 :=
    ⟨Float32.isFinite_int32_two, by rw [Float32.toReal_int32_two]; simp⟩
  have p2 := (p1.mul t2 (by numle)).mono (e' := 1 / 2 ^ 20) (by numle)
  have p3 := (p2.mul ((A32.of_exact hfc).congr hfcv) (by numle)).mono (e' := 1 / 2 ^ 15) (by numle)
  have o1 := (A32.of_exact Float32.isFinite_lit_one).congr Float32.toReal_lit_one
  have p4 := (o1.div p3 (m := 125662 / 1000) (by norm_num) (by numle) (by numle)).mono
    (e' := 1 / 2 ^ 28) (by numle)
  have d0 := (A32.of_exact hdt).congr (hdtv.trans rfl : dt.toReal = 5368709 / 2147483648)
  have p5 := (d0.add p4 (by numle)).mono (e' := 1 / 2 ^ 27) (by numle)
  have p6 := d0.div p5 (m := 10456 / 1000000) (by norm_num) (by numle) (by numle)
  refine ⟨p6.1, (abs_sub_le _ ((5368709 / 2147483648 : ℝ) / (5368709 / 2147483648 + 1 / (884279719003555 / 281474976710656 * 2 * 20))) _).trans ?_⟩
  have h6 := p6.2
  have h7 : |((5368709 / 2147483648 : ℝ) / (5368709 / 2147483648 + 1 / (884279719003555 / 281474976710656 * 2 * 20)))
      - (16042859 / 67108864)| ≤ 1 / 2 ^ 25 := by norm_num [abs_le]
  have hη1 := η32_small; have hη0 := η32_pos
  rw [u32_eq] at h6
  norm_num at h6 h7 ⊢
  linarith

open AC_PosControl_lib in
theorem alpha5 (hL : LibmSpec) {dt fc : Float32} (hdt : dt.IsFinite) (hdtv : dt.toReal = dtR)
    (hfc : fc.IsFinite) (hfcv : fc.toReal = 5) :
    A32 (calc_lowpass_alpha_dt dt fc) (4886901 / 67108864) (1 / 2 ^ 22) := by
  have hn1 : is_negative_float dt = false := isNeg_false hL hdt (by rw [hdtv, dtR]; norm_num)
  have hn2 : is_negative_float fc = false := isNeg_false hL hfc (by rw [hfcv]; norm_num)
  have hz1 : is_zero_float fc = false := by
    rw [Bool.eq_false_iff, ne_eq, isZero_iff hfc, hfcv]; norm_num
  have hz2 : is_zero_float dt = false := by
    rw [Bool.eq_false_iff, ne_eq, isZero_iff hdt, hdtv, dtR]; norm_num
  simp only [calc_lowpass_alpha_dt, Id.run, hn1, hn2, hz1, hz2, Bool.or_false, Bool.false_eq_true,
    ite_false, id_pure_eq]
  have p1 := f32_pi hL
  have t2 : A32 (Int32.toFloat32 (2 : Int32)) 2 0 :=
    ⟨Float32.isFinite_int32_two, by rw [Float32.toReal_int32_two]; simp⟩
  have p2 := (p1.mul t2 (by numle)).mono (e' := 1 / 2 ^ 20) (by numle)
  have p3 := (p2.mul ((A32.of_exact hfc).congr hfcv) (by numle)).mono (e' := 1 / 2 ^ 17) (by numle)
  have o1 := (A32.of_exact Float32.isFinite_lit_one).congr Float32.toReal_lit_one
  have p4 := (o1.div p3 (m := 31414 / 1000) (by norm_num) (by numle) (by numle)).mono
    (e' := 1 / 2 ^ 26) (by numle)
  have d0 := (A32.of_exact hdt).congr (hdtv.trans rfl : dt.toReal = 5368709 / 2147483648)
  have p5 := (d0.add p4 (by numle)).mono (e' := 1 / 2 ^ 25) (by numle)
  have p6 := d0.div p5 (m := 34329 / 1000000) (by norm_num) (by numle) (by numle)
  refine ⟨p6.1, (abs_sub_le _ ((5368709 / 2147483648 : ℝ) / (5368709 / 2147483648 + 1 / (884279719003555 / 281474976710656 * 2 * 5))) _).trans ?_⟩
  have h6 := p6.2
  have h7 : |((5368709 / 2147483648 : ℝ) / (5368709 / 2147483648 + 1 / (884279719003555 / 281474976710656 * 2 * 5)))
      - (4886901 / 67108864)| ≤ 1 / 2 ^ 25 := by norm_num [abs_le]
  have hη1 := η32_small; have hη0 := η32_pos
  rw [u32_eq] at h6
  norm_num at h6 h7 ⊢
  linarith

open AC_PosControl_lib in
theorem alpha2 (hL : LibmSpec) {dt fc : Float32} (hdt : dt.IsFinite) (hdtv : dt.toReal = dtR)
    (hfc : fc.IsFinite) (hfcv : fc.toReal = 2) :
    A32 (calc_lowpass_alpha_dt dt fc) (16352567 / 536870912) (1 / 2 ^ 22) := by
  have hn1 : is_negative_float dt = false := isNeg_false hL hdt (by rw [hdtv, dtR]; norm_num)
  have hn2 : is_negative_float fc = false := isNeg_false hL hfc (by rw [hfcv]; norm_num)
  have hz1 : is_zero_float fc = false := by
    rw [Bool.eq_false_iff, ne_eq, isZero_iff hfc, hfcv]; norm_num
  have hz2 : is_zero_float dt = false := by
    rw [Bool.eq_false_iff, ne_eq, isZero_iff hdt, hdtv, dtR]; norm_num
  simp only [calc_lowpass_alpha_dt, Id.run, hn1, hn2, hz1, hz2, Bool.or_false, Bool.false_eq_true,
    ite_false, id_pure_eq]
  have p1 := f32_pi hL
  have t2 : A32 (Int32.toFloat32 (2 : Int32)) 2 0 :=
    ⟨Float32.isFinite_int32_two, by rw [Float32.toReal_int32_two]; simp⟩
  have p2 := (p1.mul t2 (by numle)).mono (e' := 1 / 2 ^ 20) (by numle)
  have p3 := (p2.mul ((A32.of_exact hfc).congr hfcv) (by numle)).mono (e' := 1 / 2 ^ 18) (by numle)
  have o1 := (A32.of_exact Float32.isFinite_lit_one).congr Float32.toReal_lit_one
  have p4 := (o1.div p3 (m := 12565 / 1000) (by norm_num) (by numle) (by numle)).mono
    (e' := 1 / 2 ^ 25) (by numle)
  have d0 := (A32.of_exact hdt).congr (hdtv.trans rfl : dt.toReal = 5368709 / 2147483648)
  have p5 := (d0.add p4 (by numle)).mono (e' := 1 / 2 ^ 24) (by numle)
  have p6 := d0.div p5 (m := 82076 / 1000000) (by norm_num) (by numle) (by numle)
  refine ⟨p6.1, (abs_sub_le _ ((5368709 / 2147483648 : ℝ) / (5368709 / 2147483648 + 1 / (884279719003555 / 281474976710656 * 2 * 2))) _).trans ?_⟩
  have h6 := p6.2
  have h7 : |((5368709 / 2147483648 : ℝ) / (5368709 / 2147483648 + 1 / (884279719003555 / 281474976710656 * 2 * 2)))
      - (16352567 / 536870912)| ≤ 1 / 2 ^ 25 := by norm_num [abs_le]
  have hη1 := η32_small; have hη0 := η32_pos
  rw [u32_eq] at h6
  norm_num at h6 h7 ⊢
  linarith


/-- **The low-pass step of `AC_PID`/`AC_PID_Basic`**, `e + α (x - e)`, with the input `x` and the
coefficient `α` approximate. For `|x|, |e| ≤ M`: within `α ex + (3 δα + (1 + 12 α) u) M + η` of
the exact step. -/
theorem A32.filt {e x α : Float32} {xr αr ex δα M : ℝ} (he : e.IsFinite) (hx : A32 x xr ex)
    (hα : A32 α αr δα) (hα0 : 0 ≤ αr) (hα1 : αr ≤ 1) (hδ : δα ≤ 1 / 2 ^ 20)
    (hexM : ex ≤ M) (hxM : |xr| ≤ M) (heM : |e.toReal| ≤ M) (hMc : M ≤ 2 ^ 90) :
    A32 (e + α * (x - e)) (e.toReal + αr * (xr - e.toReal))
      (αr * ex + (4 * δα + (1 + 12 * αr) * u32) * M + 2 * η32) := by
  have hη1 := η32_small; have hη0 := η32_pos
  have hu : u32 = 1 / 16777216 := u32_eq
  have hδ0 : 0 ≤ δα := (abs_nonneg _).trans hα.2
  have hex0 : 0 ≤ ex := (abs_nonneg _).trans hx.2
  have hM0 : 0 ≤ M := (abs_nonneg _).trans heM
  have mf : (2 : ℝ) ^ 100 ≤ maxFinite32 := capF_le_max32
  -- the difference
  set X := x.toReal - e.toReal with hXd
  have hxx : |x.toReal - xr| ≤ ex := hx.2
  have hX : |X| ≤ 3 * M := by
    have h1 := abs_sub x.toReal e.toReal
    have h2 : |x.toReal| ≤ |xr| + ex := hx.abs_le
    linarith
  obtain ⟨f1, e1⟩ := Float32.sub_err_all hx.1 he (by linarith)
  set D := (x - e).toReal with hDd
  have e1' : |D - X| ≤ u32 * (3 * M) := by
    rw [show (2 : ℝ) ^ (-24 : ℤ) = u32 from rfl] at e1
    exact e1.trans (mul_le_mul_of_nonneg_left hX u32_pos.le)
  have hD : |D| ≤ 4 * M := by
    have := abs_sub_abs_le_abs_sub D X; rw [hu] at e1'; linarith
  -- the coefficient
  have hαa : |α.toReal| ≤ αr + δα := by
    have := hα.abs_le; rwa [abs_of_nonneg hα0] at this
  have hαD : |α.toReal * D| ≤ (αr + δα) * (4 * M) := by
    rw [abs_mul]; exact mul_le_mul hαa hD (abs_nonneg _) (by linarith)
  obtain ⟨f2, e2⟩ := Float32.mul_err_all hα.1 f1 (by nlinarith)
  set P := (α * (x - e)).toReal with hPd
  have e2' : |P - α.toReal * D| ≤ u32 * ((αr + δα) * (4 * M)) + η32 := by
    have := rnd32 e2
    nlinarith [u32_pos]
  have hP : |P| ≤ (αr + δα) * (4 * M) * (1 + u32) + η32 := by
    have := abs_sub_abs_le_abs_sub P (α.toReal * D); nlinarith [u32_pos]
  -- the sum
  have hEP : |e.toReal + P| ≤ M + (αr + δα) * (4 * M) * (1 + u32) + η32 :=
    (abs_add_le _ _).trans (by linarith)
  have hb16 : (αr + δα) * (4 * M) * (1 + u32) ≤ 16 * M := by
    have : αr + δα ≤ 2 := by linarith
    have : 1 + u32 ≤ 2 := by rw [hu]; norm_num
    have : (αr + δα) * (4 * M) ≤ 2 * (4 * M) := mul_le_mul_of_nonneg_right (by linarith) (by linarith)
    have := mul_le_mul this (show 1 + u32 ≤ 2 by linarith) (by rw [hu]; norm_num) (by linarith)
    linarith
  obtain ⟨f3, e3⟩ := Float32.add_err_all he f2 (by linarith)
  refine ⟨f3, ?_⟩
  have e3' : |(e + α * (x - e)).toReal - (e.toReal + P)| ≤
      u32 * (M + (αr + δα) * (4 * M) * (1 + u32) + η32) :=
    e3.trans (mul_le_mul_of_nonneg_left hEP u32_pos.le)
  -- the pieces of the error
  have k1 : |α.toReal * D - α.toReal * X| ≤ (αr + δα) * (u32 * (3 * M)) := by
    rw [← mul_sub, abs_mul]; exact mul_le_mul hαa e1' (abs_nonneg _) (by linarith)
  have k2 : |α.toReal * X - αr * X| ≤ δα * (3 * M) := by
    rw [← sub_mul, abs_mul]; exact mul_le_mul hα.2 hX (abs_nonneg _) hδ0
  have k3 : |αr * X - αr * (xr - e.toReal)| ≤ αr * ex := by
    rw [← mul_sub, abs_mul, abs_of_nonneg hα0]
    exact mul_le_mul_of_nonneg_left (by rw [hXd, show x.toReal - e.toReal - (xr - e.toReal) = x.toReal - xr by ring]; exact hxx) hα0
  have tri : |(e + α * (x - e)).toReal - (e.toReal + αr * (xr - e.toReal))| ≤
      |(e + α * (x - e)).toReal - (e.toReal + P)| + |P - α.toReal * D| +
        |α.toReal * D - α.toReal * X| + |α.toReal * X - αr * X| +
        |αr * X - αr * (xr - e.toReal)| := by
    have a1 := abs_sub_le (e + α * (x - e)).toReal (e.toReal + P) (e.toReal + αr * (xr - e.toReal))
    have a2 := abs_sub_le (e.toReal + P) (e.toReal + α.toReal * D) (e.toReal + αr * (xr - e.toReal))
    have a3 := abs_sub_le (e.toReal + α.toReal * D) (e.toReal + α.toReal * X) (e.toReal + αr * (xr - e.toReal))
    have a4 := abs_sub_le (e.toReal + α.toReal * X) (e.toReal + αr * X) (e.toReal + αr * (xr - e.toReal))
    simp only [add_sub_add_left_eq_sub] at a1 a2 a3 a4
    linarith
  refine tri.trans ?_
  rw [hu] at e2' e3' k1 ⊢
  have := mul_nonneg hδ0 hM0; have := mul_nonneg hα0 hM0
  have := mul_nonneg (mul_nonneg hα0 hM0) hδ0
  have := mul_nonneg (mul_nonneg hδ0 hM0) hδ0
  ring_nf at e2' e3' k1 k2 k3 ⊢
  linarith


open AC_PosControl_lib in
theorem alpha0 (hL : LibmSpec) {dt fc : Float32} (hdt : dt.IsFinite) (hdt0 : 0 ≤ dt.toReal)
    (hfc : fc.IsFinite) (hfcv : fc.toReal = 0) :
    A32 (calc_lowpass_alpha_dt dt fc) 1 0 := by
  have hn1 : is_negative_float dt = false := isNeg_false hL hdt hdt0
  have hn2 : is_negative_float fc = false := isNeg_false hL hfc (by rw [hfcv])
  have hz1 : is_zero_float fc = true := by
    rw [isZero_iff hfc, hfcv]; norm_num
  simp only [calc_lowpass_alpha_dt, Id.run, hn1, hn2, hz1, Bool.or_false, Bool.false_eq_true,
    ite_false, ite_true, id_pure_eq]
  obtain ⟨h1, h2⟩ := f32_ofF64_one hL
  exact ⟨h1, by rw [h2]; simp⟩

theorem A32.exact_one {a : Float32} (ha : a.IsFinite) (h1 : a.toReal = 1) : A32 a 1 0 :=
  ⟨ha, by rw [h1]; simp⟩

/-! ## Exact low-pass coefficients (with the float `π`) and the sharp low-pass step -/

/-- **`(float) π` is the nearest float**, `0x40490FDB = 3.14159274f` (correct rounding of the
`double` `π`; `LibmSpec.f64ToF32` alone allows both neighbours). An explicit float fact. -/
def PiF32 : Prop := Float.toFloat32 (3.1415926535897931 : Float) = (3.14159274 : Float32)

/-- The period of the scheduler, `2500 µs · 1e-6f`. -/
abbrev d0 : Float32 := (2500 : UInt64).toFloat32 * (1.0e-6 : Float32)

theorem d0_fin : d0.IsFinite := Float32.isFinite_of_unpack (by f32_unpack :
  d0.toModel.unpack = .finite .positive 10737418 (-32) (by decide))
theorem d0_val : d0.toReal = dtR := by
  rw [Float32.toReal_of_unpack (by f32_unpack :
    d0.toModel.unpack = .finite .positive 10737418 (-32) (by decide)), dtR]
  simp [Sign.apply]; norm_num

open AC_PosControl_lib in
/-- `calc_lowpass_alpha_dt(0.0025f, fc)` with the float `π`: the float `a`, exactly. -/
theorem alpha_exact (hL : LibmSpec) (hpi : PiF32) (fc : Float32) (hfc : fc.IsFinite)
    (hfc0 : 1 ≤ fc.toReal) {m : ℕ} {e : ℤ} {hm : 0 < m}
    (h : (d0 / (d0 + (1.0 : Float32) / (((3.14159274 : Float32) * Int32.toFloat32 (2 : Int32)) * fc))).toModel.unpack =
      .finite .positive m e hm) :
    A32 (calc_lowpass_alpha_dt d0 fc) ((m : ℝ) * 2 ^ e) 0 := by
  have hn1 : is_negative_float d0 = false := isNeg_false hL d0_fin (by rw [d0_val, dtR]; norm_num)
  have hn2 : is_negative_float fc = false := isNeg_false hL hfc (by linarith)
  have hz1 : is_zero_float fc = false := by
    rw [Bool.eq_false_iff, ne_eq, isZero_iff hfc, abs_of_pos (by linarith)]; norm_num; linarith
  have hz2 : is_zero_float d0 = false := by
    rw [Bool.eq_false_iff, ne_eq, isZero_iff d0_fin, d0_val, dtR]; norm_num
  simp only [calc_lowpass_alpha_dt, Id.run, hn1, hn2, hz1, hz2, Bool.or_false, Bool.false_eq_true,
    ite_false, id_pure_eq]
  rw [hpi]
  refine ⟨Float32.isFinite_of_unpack h, ?_⟩
  rw [Float32.toReal_of_unpack h]; simp [Sign.apply]

theorem f20_fin : (20.0 : Float32).IsFinite := Float32.isFinite_of_unpack (by f32_unpack :
  (20.0 : Float32).toModel.unpack = .finite .positive 10485760 (-19) (by decide))
theorem f20_val : (20.0 : Float32).toReal = 20 := by
  rw [Float32.toReal_of_unpack (by f32_unpack :
    (20.0 : Float32).toModel.unpack = .finite .positive 10485760 (-19) (by decide))]
  simp [Sign.apply]; norm_num

/-- `αA` exactly. -/
theorem alphaA (hL : LibmSpec) (hpi : PiF32) :
    A32 (AC_PosControl_lib.calc_lowpass_alpha_dt d0 20.0) (16042859 / 67108864) 0 := by
  have := alpha_exact hL hpi 20.0 f20_fin (by rw [f20_val]; norm_num)
    (m := 16042859) (e := -26) (hm := by decide) (by f32_unpack)
  exact this.congr (by norm_num)

theorem f5_fin : (5.0 : Float32).IsFinite := Float32.isFinite_of_unpack (by f32_unpack :
  (5.0 : Float32).toModel.unpack = .finite .positive 10485760 (-21) (by decide))
theorem f5_val : (5.0 : Float32).toReal = 5 := by
  rw [Float32.toReal_of_unpack (by f32_unpack :
    (5.0 : Float32).toModel.unpack = .finite .positive 10485760 (-21) (by decide))]
  simp [Sign.apply]; norm_num

theorem f2_fin : (2.0 : Float32).IsFinite := Float32.isFinite_of_unpack (by f32_unpack :
  (2.0 : Float32).toModel.unpack = .finite .positive 8388608 (-22) (by decide))
theorem f2_val : (2.0 : Float32).toReal = 2 := by
  rw [Float32.toReal_of_unpack (by f32_unpack :
    (2.0 : Float32).toModel.unpack = .finite .positive 8388608 (-22) (by decide))]
  simp [Sign.apply]; norm_num

/-- `αV` exactly. -/
theorem alphaV (hL : LibmSpec) (hpi : PiF32) :
    A32 (AC_PosControl_lib.calc_lowpass_alpha_dt d0 5.0) (4886901 / 67108864) 0 := by
  have := alpha_exact hL hpi 5.0 f5_fin (by rw [f5_val]; norm_num)
    (m := 9773802) (e := -27) (hm := by decide) (by f32_unpack)
  exact this.congr (by norm_num)

/-- `αT` exactly. -/
theorem alphaT (hL : LibmSpec) (hpi : PiF32) :
    A32 (AC_PosControl_lib.calc_lowpass_alpha_dt d0 2.0) (16352567 / 536870912) 0 := by
  have := alpha_exact hL hpi 2.0 f2_fin (by rw [f2_val]; norm_num)
    (m := 16352567) (e := -29) (hm := by decide) (by f32_unpack)
  exact this.congr (by norm_num)

/-- **The low-pass step, sharp form.** `e + α (x - e)` with the input `x` within `ex ≤ M/2¹⁰` of
`xr`, `|xr|, |e| ≤ M`, and the coefficient within `δα` of `αr ∈ [0, 1]`: within
`αr ex + (2.01 δα + (1.02 + 4.11 αr) u) M + 2η` of the exact step. -/
theorem A32.filt2 {e x α : Float32} {xr αr ex δα M : ℝ} (he : e.IsFinite) (hx : A32 x xr ex)
    (hα : A32 α αr δα) (hα0 : 0 ≤ αr) (hα1 : αr ≤ 1) (hδ : δα ≤ 1 / 2 ^ 20)
    (hexM : ex ≤ M / 2 ^ 10) (hxM : |xr| ≤ M) (heM : |e.toReal| ≤ M) (hMc : M ≤ 2 ^ 90) :
    A32 (e + α * (x - e)) (e.toReal + αr * (xr - e.toReal))
      (αr * ex + (201 / 100 * δα + (102 / 100 + 411 / 100 * αr) * u32) * M + 2 * η32) := by
  have hη1 := η32_small; have hη0 := η32_pos
  have hu : u32 = 1 / 16777216 := u32_eq
  have hδ0 : 0 ≤ δα := (abs_nonneg _).trans hα.2
  have hex0 : 0 ≤ ex := (abs_nonneg _).trans hx.2
  have hM0 : 0 ≤ M := (abs_nonneg _).trans heM
  have mf : (2 : ℝ) ^ 100 ≤ maxFinite32 := capF_le_max32
  set X := x.toReal - e.toReal with hXd
  have hxx : |x.toReal - xr| ≤ ex := hx.2
  have hX : |X| ≤ (2 + 1 / 1024) * M := by
    have h1 := abs_sub x.toReal e.toReal
    have h2 : |x.toReal| ≤ |xr| + ex := hx.abs_le
    linarith
  obtain ⟨f1, e1⟩ := Float32.sub_err_all hx.1 he (by linarith)
  set D := (x - e).toReal with hDd
  have e1' : |D - X| ≤ u32 * ((2 + 1 / 1024) * M) := by
    rw [show (2 : ℝ) ^ (-24 : ℤ) = u32 from rfl] at e1
    exact e1.trans (mul_le_mul_of_nonneg_left hX u32_pos.le)
  have hD : |D| ≤ (21 / 10) * M := by
    have := abs_sub_abs_le_abs_sub D X; rw [hu] at e1'; nlinarith
  have hαa : |α.toReal| ≤ αr + δα := by
    have := hα.abs_le; rwa [abs_of_nonneg hα0] at this
  have hαD : |α.toReal * D| ≤ (αr + δα) * ((21 / 10) * M) := by
    rw [abs_mul]; exact mul_le_mul hαa hD (abs_nonneg _) (by linarith)
  have hαD' : |α.toReal * D| ≤ 3 * M := by
    have : (αr + δα) * ((21 / 10) * M) ≤ 3 * M := by nlinarith
    linarith
  obtain ⟨f2, e2⟩ := Float32.mul_err_all hα.1 f1 (by linarith)
  set P := (α * (x - e)).toReal with hPd
  have e2' : |P - α.toReal * D| ≤ u32 * ((αr + δα) * ((21 / 10) * M)) + η32 := by
    have h := rnd32 e2
    rw [← hDd] at h
    exact h.trans (add_le_add_left (mul_le_mul_of_nonneg_left hαD u32_pos.le) η32)
  -- the pieces of the error before the last rounding
  have k1 : |α.toReal * D - α.toReal * X| ≤ (αr + δα) * (u32 * ((2 + 1 / 1024) * M)) := by
    rw [← mul_sub, abs_mul]; exact mul_le_mul hαa e1' (abs_nonneg _) (by linarith)
  have k2 : |α.toReal * X - αr * X| ≤ δα * ((2 + 1 / 1024) * M) := by
    rw [← sub_mul, abs_mul]; exact mul_le_mul hα.2 hX (abs_nonneg _) hδ0
  have k3 : |αr * X - αr * (xr - e.toReal)| ≤ αr * ex := by
    rw [← mul_sub, abs_mul, abs_of_nonneg hα0]
    exact mul_le_mul_of_nonneg_left (by rw [hXd, show x.toReal - e.toReal - (xr - e.toReal) = x.toReal - xr by ring]; exact hxx) hα0
  have hP : |P - αr * (xr - e.toReal)| ≤ u32 * ((αr + δα) * ((21 / 10) * M)) + η32 +
      (αr + δα) * (u32 * ((2 + 1 / 1024) * M)) + δα * ((2 + 1 / 1024) * M) + αr * ex := by
    have a1 := abs_sub_le P (α.toReal * D) (αr * (xr - e.toReal))
    have a2 := abs_sub_le (α.toReal * D) (α.toReal * X) (αr * (xr - e.toReal))
    have a3 := abs_sub_le (α.toReal * X) (αr * X) (αr * (xr - e.toReal))
    linarith
  have hsmall : u32 * ((αr + δα) * ((21 / 10) * M)) + η32 +
      (αr + δα) * (u32 * ((2 + 1 / 1024) * M)) + δα * ((2 + 1 / 1024) * M) + αr * ex ≤ M / 100 + η32 := by
    have hab : αr + δα ≤ 2 := by linarith
    have t1 : αr * ex ≤ 1 * (M / 2 ^ 10) := mul_le_mul hα1 hexM hex0 zero_le_one
    have t2 : δα * ((2 + 1 / 1024) * M) ≤ (1 / 2 ^ 20) * ((2 + 1 / 1024) * M) :=
      mul_le_mul_of_nonneg_right hδ (by positivity)
    have t3 : (αr + δα) * (u32 * ((2 + 1 / 1024) * M)) ≤ 2 * (u32 * ((2 + 1 / 1024) * M)) :=
      mul_le_mul_of_nonneg_right hab (by positivity)
    have t4 : u32 * ((αr + δα) * ((21 / 10) * M)) ≤ u32 * (2 * ((21 / 10) * M)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hab (by positivity)) u32_pos.le
    rw [hu] at t3 t4
    linarith
  have hconv : |e.toReal + αr * (xr - e.toReal)| ≤ M := by
    rw [show e.toReal + αr * (xr - e.toReal) = (1 - αr) * e.toReal + αr * xr by ring]
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_mul, abs_of_nonneg (by linarith : (0 : ℝ) ≤ 1 - αr), abs_of_nonneg hα0]
    nlinarith
  have hEP : |e.toReal + P| ≤ (101 / 100) * M + η32 := by
    have := abs_sub_abs_le_abs_sub (e.toReal + P) (e.toReal + αr * (xr - e.toReal))
    rw [show e.toReal + P - (e.toReal + αr * (xr - e.toReal)) = P - αr * (xr - e.toReal) by ring] at this
    linarith
  obtain ⟨f3, e3⟩ := Float32.add_err_all he f2 (by linarith)
  refine ⟨f3, ?_⟩
  have e3' : |(e + α * (x - e)).toReal - (e.toReal + P)| ≤ u32 * ((101 / 100) * M + η32) :=
    e3.trans (mul_le_mul_of_nonneg_left hEP u32_pos.le)
  have a0 := abs_sub_le (e + α * (x - e)).toReal (e.toReal + P) (e.toReal + αr * (xr - e.toReal))
  rw [show e.toReal + P - (e.toReal + αr * (xr - e.toReal)) = P - αr * (xr - e.toReal) by ring] at a0
  refine a0.trans ?_
  rw [hu] at e3' hP ⊢
  have := mul_nonneg hδ0 hM0; have := mul_nonneg hα0 hM0
  have := mul_nonneg (mul_nonneg hα0 hM0) hδ0
  have := mul_nonneg (mul_nonneg hδ0 hM0) hδ0
  ring_nf at e3' hP ⊢
  nlinarith

/-- **The low-pass step of `DigitalLPF::_apply`, sharp form** (operand order `(x - e) α`). `e + α (x - e)` with the input `x` within `ex ≤ M/2¹⁰` of
`xr`, `|xr|, |e| ≤ M`, and the coefficient within `δα` of `αr ∈ [0, 1]`: within
`αr ex + (2.01 δα + (1.02 + 4.11 αr) u) M + 2η` of the exact step. -/
theorem A32.lpf2 {e x α : Float32} {xr αr ex δα M : ℝ} (he : e.IsFinite) (hx : A32 x xr ex)
    (hα : A32 α αr δα) (hα0 : 0 ≤ αr) (hα1 : αr ≤ 1) (hδ : δα ≤ 1 / 2 ^ 20)
    (hexM : ex ≤ M / 2 ^ 10) (hxM : |xr| ≤ M) (heM : |e.toReal| ≤ M) (hMc : M ≤ 2 ^ 90) :
    A32 (e + (x - e) * α) (e.toReal + αr * (xr - e.toReal))
      (αr * ex + (201 / 100 * δα + (102 / 100 + 411 / 100 * αr) * u32) * M + 2 * η32) := by
  have hη1 := η32_small; have hη0 := η32_pos
  have hu : u32 = 1 / 16777216 := u32_eq
  have hδ0 : 0 ≤ δα := (abs_nonneg _).trans hα.2
  have hex0 : 0 ≤ ex := (abs_nonneg _).trans hx.2
  have hM0 : 0 ≤ M := (abs_nonneg _).trans heM
  have mf : (2 : ℝ) ^ 100 ≤ maxFinite32 := capF_le_max32
  set X := x.toReal - e.toReal with hXd
  have hxx : |x.toReal - xr| ≤ ex := hx.2
  have hX : |X| ≤ (2 + 1 / 1024) * M := by
    have h1 := abs_sub x.toReal e.toReal
    have h2 : |x.toReal| ≤ |xr| + ex := hx.abs_le
    linarith
  obtain ⟨f1, e1⟩ := Float32.sub_err_all hx.1 he (by linarith)
  set D := (x - e).toReal with hDd
  have e1' : |D - X| ≤ u32 * ((2 + 1 / 1024) * M) := by
    rw [show (2 : ℝ) ^ (-24 : ℤ) = u32 from rfl] at e1
    exact e1.trans (mul_le_mul_of_nonneg_left hX u32_pos.le)
  have hD : |D| ≤ (21 / 10) * M := by
    have := abs_sub_abs_le_abs_sub D X; rw [hu] at e1'; nlinarith
  have hαa : |α.toReal| ≤ αr + δα := by
    have := hα.abs_le; rwa [abs_of_nonneg hα0] at this
  have hαD : |α.toReal * D| ≤ (αr + δα) * ((21 / 10) * M) := by
    rw [abs_mul]; exact mul_le_mul hαa hD (abs_nonneg _) (by linarith)
  have hαD' : |α.toReal * D| ≤ 3 * M := by
    have : (αr + δα) * ((21 / 10) * M) ≤ 3 * M := by nlinarith
    linarith
  obtain ⟨f2, e2⟩ := Float32.mul_err_all f1 hα.1 (by rw [mul_comm]; linarith)
  set P := ((x - e) * α).toReal with hPd
  have e2' : |P - α.toReal * D| ≤ u32 * ((αr + δα) * ((21 / 10) * M)) + η32 := by
    have h := rnd32 e2
    rw [← hDd, mul_comm D α.toReal] at h
    exact h.trans (add_le_add_left (mul_le_mul_of_nonneg_left hαD u32_pos.le) η32)
  -- the pieces of the error before the last rounding
  have k1 : |α.toReal * D - α.toReal * X| ≤ (αr + δα) * (u32 * ((2 + 1 / 1024) * M)) := by
    rw [← mul_sub, abs_mul]; exact mul_le_mul hαa e1' (abs_nonneg _) (by linarith)
  have k2 : |α.toReal * X - αr * X| ≤ δα * ((2 + 1 / 1024) * M) := by
    rw [← sub_mul, abs_mul]; exact mul_le_mul hα.2 hX (abs_nonneg _) hδ0
  have k3 : |αr * X - αr * (xr - e.toReal)| ≤ αr * ex := by
    rw [← mul_sub, abs_mul, abs_of_nonneg hα0]
    exact mul_le_mul_of_nonneg_left (by rw [hXd, show x.toReal - e.toReal - (xr - e.toReal) = x.toReal - xr by ring]; exact hxx) hα0
  have hP : |P - αr * (xr - e.toReal)| ≤ u32 * ((αr + δα) * ((21 / 10) * M)) + η32 +
      (αr + δα) * (u32 * ((2 + 1 / 1024) * M)) + δα * ((2 + 1 / 1024) * M) + αr * ex := by
    have a1 := abs_sub_le P (α.toReal * D) (αr * (xr - e.toReal))
    have a2 := abs_sub_le (α.toReal * D) (α.toReal * X) (αr * (xr - e.toReal))
    have a3 := abs_sub_le (α.toReal * X) (αr * X) (αr * (xr - e.toReal))
    linarith
  have hsmall : u32 * ((αr + δα) * ((21 / 10) * M)) + η32 +
      (αr + δα) * (u32 * ((2 + 1 / 1024) * M)) + δα * ((2 + 1 / 1024) * M) + αr * ex ≤ M / 100 + η32 := by
    have hab : αr + δα ≤ 2 := by linarith
    have t1 : αr * ex ≤ 1 * (M / 2 ^ 10) := mul_le_mul hα1 hexM hex0 zero_le_one
    have t2 : δα * ((2 + 1 / 1024) * M) ≤ (1 / 2 ^ 20) * ((2 + 1 / 1024) * M) :=
      mul_le_mul_of_nonneg_right hδ (by positivity)
    have t3 : (αr + δα) * (u32 * ((2 + 1 / 1024) * M)) ≤ 2 * (u32 * ((2 + 1 / 1024) * M)) :=
      mul_le_mul_of_nonneg_right hab (by positivity)
    have t4 : u32 * ((αr + δα) * ((21 / 10) * M)) ≤ u32 * (2 * ((21 / 10) * M)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hab (by positivity)) u32_pos.le
    rw [hu] at t3 t4
    linarith
  have hconv : |e.toReal + αr * (xr - e.toReal)| ≤ M := by
    rw [show e.toReal + αr * (xr - e.toReal) = (1 - αr) * e.toReal + αr * xr by ring]
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_mul, abs_of_nonneg (by linarith : (0 : ℝ) ≤ 1 - αr), abs_of_nonneg hα0]
    nlinarith
  have hEP : |e.toReal + P| ≤ (101 / 100) * M + η32 := by
    have := abs_sub_abs_le_abs_sub (e.toReal + P) (e.toReal + αr * (xr - e.toReal))
    rw [show e.toReal + P - (e.toReal + αr * (xr - e.toReal)) = P - αr * (xr - e.toReal) by ring] at this
    linarith
  obtain ⟨f3, e3⟩ := Float32.add_err_all he f2 (by linarith)
  refine ⟨f3, ?_⟩
  have e3' : |(e + (x - e) * α).toReal - (e.toReal + P)| ≤ u32 * ((101 / 100) * M + η32) :=
    e3.trans (mul_le_mul_of_nonneg_left hEP u32_pos.le)
  have a0 := abs_sub_le (e + (x - e) * α).toReal (e.toReal + P) (e.toReal + αr * (xr - e.toReal))
  rw [show e.toReal + P - (e.toReal + αr * (xr - e.toReal)) = P - αr * (xr - e.toReal) by ring] at a0
  refine a0.trans ?_
  rw [hu] at e3' hP ⊢
  have := mul_nonneg hδ0 hM0; have := mul_nonneg hα0 hM0
  have := mul_nonneg (mul_nonneg hα0 hM0) hδ0
  have := mul_nonneg (mul_nonneg hδ0 hM0) hδ0
  ring_nf at e3' hP ⊢
  nlinarith

end

end Contracts.Track.CtrlV
