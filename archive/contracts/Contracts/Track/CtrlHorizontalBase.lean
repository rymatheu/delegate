import Contracts.Mission.FloatCalc
import Contracts.Quick.Tilt
import Contracts.Track.Integrators2D
import Contracts.Track.Horizontal

/-!
# Shared float facts for the horizontal controller lemmas (milestone M6, C-series)

Tools for `CtrlHorizontal*.lean` (`CTRL_HORIZONTAL.md`), on the translation `AC_PosControl_lib`:

* `isInf_false`, `vec_ok`: finite vectors pass the `is_nan`/`is_inf` guard of
  `AC_PID_2D::update_all`;
* `B32.lit`, `B32.mul_one`, `B32.sub_R`: the numeric calculus of `FloatCalc.lean` with literals,
  products by an exact `1`, and a difference whose exact value is bounded directly;
* `flen_le`: the `float` length `sqrtf(x*x + y*y)` is at most `|v| (1 + 2⁻²²) + 2⁻⁷⁰` (the upper
  companion of `Contracts.Quick.flen_ge`);
* `limit_length_inactive`: `Vector2f::limit_length` returns its argument unchanged (and `false`)
  when the exact length is below the limit by that factor;
* `lensq_le_sq`, `limit_accel_xy_inactive`: `limit_accel_xy` returns its argument unchanged (and
  `false`) when the exact length is at most `accel_max (1 - 2⁻²⁰)`.
-/

namespace Contracts.Track.HCtl

open AC_PosControl_lib Contracts.Quick Contracts.Mission Float.Model UnpackedFloat

noncomputable section

/-! ## The comparisons of `AP_Math` (as in `Contracts.Mission.NavStop`, without its imports) -/

theorem f32_toReal_eps : (1.1920929e-7 : Float32).toReal = 2 ^ (-23 : ℤ) := by
  rw [f32_toReal_1p1920929Em7]; norm_num

theorem isPos_iff {x : Float32} (hx : x.IsFinite) :
    is_positive_float x = true ↔ 2 ^ (-23 : ℤ) ≤ x.toReal := by
  show decide ((1.1920929e-7 : Float32) ≤ x) = true ↔ _
  rw [decide_eq_true_iff, Float32.le_iff_toReal_le f32_isFinite_1p1920929Em7 hx, f32_toReal_eps]

theorem isZero_iff {x : Float32} (hx : x.IsFinite) :
    is_zero_float x = true ↔ |x.toReal| < 2 ^ (-23 : ℤ) := by
  show decide (Float32.abs x < (1.1920929e-7 : Float32)) = true ↔ _
  rw [decide_eq_true_iff, Float32.lt_iff_toReal_lt ((Float32.isFinite_abs x).2 hx)
    f32_isFinite_1p1920929Em7, Float32.toReal_abs, f32_toReal_eps]

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

/-- `(float) 0.0` is `0` (`LibmSpec.f64ToF32_exact`). -/
theorem f32_isFinite_toFloat32_0 (hL : LibmSpec) :
    (Float.toFloat32 0.0).IsFinite ∧ (Float.toFloat32 0.0).toReal = 0 := by
  obtain ⟨f, e⟩ := hL.f64ToF32_exact 0.0 0.0 f64_isFinite_0p0 f32_isFinite_0p0
    (by rw [f32_toReal_0p0, f64_toReal_0p0])
  exact ⟨f, by rw [e, f64_toReal_0p0]⟩


/-! ## The 5 Hz filter coefficient (as `Contracts.Track.CtrlV.alpha5`, `CtrlVerticalFloat.lean`) -/

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

/-- Numeric side conditions: `u32` as a fraction, `η32` bounded. -/
macro "hnumle" : tactic => `(tactic| (
  have hη1 := η32_small; have hη0 := η32_pos
  rw [u32_eq] at *
  norm_num [capF] at *
  try nlinarith))

/-- **The 5 Hz filter coefficient** `calc_lowpass_alpha_dt(0.0025f, 5)` (`PSC_NE_VEL_FLTE`,
`FLTD`): within `2⁻²²` of `αE = 4886901 / 2²⁶`, the `float` value computed with the `float` `π`.
`LibmSpec` does not determine `(float) M_PI` (both neighbours of `π` are within its bound), so the
coefficient is bounded rather than fixed. -/
theorem alpha5 (hL : LibmSpec) {dt fc : Float32} (hdt : dt.IsFinite)
    (hdtv : dt.toReal = 5368709 / 2147483648) (hfc : fc.IsFinite) (hfcv : fc.toReal = 5) :
    A32 (calc_lowpass_alpha_dt dt fc) (4886901 / 67108864) (1 / 2 ^ 22) := by
  have hn1 : is_negative_float dt = false := isNeg_false hL hdt (by rw [hdtv]; norm_num)
  have hn2 : is_negative_float fc = false := isNeg_false hL hfc (by rw [hfcv]; norm_num)
  have hz1 : is_zero_float fc = false := by
    rw [Bool.eq_false_iff, ne_eq, isZero_iff hfc, hfcv]; norm_num
  have hz2 : is_zero_float dt = false := by
    rw [Bool.eq_false_iff, ne_eq, isZero_iff hdt, hdtv]; norm_num
  simp only [calc_lowpass_alpha_dt, Id.run, hn1, hn2, hz1, hz2, Bool.or_false, Bool.false_eq_true,
    ite_false, id_pure_eq]
  have p1 := f32_pi hL
  have t2 : A32 (Int32.toFloat32 (2 : Int32)) 2 0 :=
    ⟨Float32.isFinite_int32_two, by rw [Float32.toReal_int32_two]; simp⟩
  have p2 := (p1.mul t2 (by hnumle)).mono (e' := 1 / 2 ^ 20) (by hnumle)
  have p3 := (p2.mul ((A32.of_exact hfc).congr hfcv) (by hnumle)).mono (e' := 1 / 2 ^ 17)
    (by hnumle)
  have o1 := (A32.of_exact Float32.isFinite_lit_one).congr Float32.toReal_lit_one
  have p4 := (o1.div p3 (m := 31414 / 1000) (by norm_num) (by hnumle) (by hnumle)).mono
    (e' := 1 / 2 ^ 26) (by hnumle)
  have d0 := (A32.of_exact hdt).congr hdtv
  have p5 := (d0.add p4 (by hnumle)).mono (e' := 1 / 2 ^ 25) (by hnumle)
  have p6 := d0.div p5 (m := 34329 / 1000000) (by norm_num) (by hnumle) (by hnumle)
  refine ⟨p6.1, (abs_sub_le _ ((5368709 / 2147483648 : ℝ) / (5368709 / 2147483648 + 1 /
    (884279719003555 / 281474976710656 * 2 * 5))) _).trans ?_⟩
  have h6 := p6.2
  have h7 : |((5368709 / 2147483648 : ℝ) / (5368709 / 2147483648 + 1 /
      (884279719003555 / 281474976710656 * 2 * 5))) - (4886901 / 67108864)| ≤ 1 / 2 ^ 25 := by
    norm_num [abs_le]
  have hη1 := η32_small; have hη0 := η32_pos
  rw [u32_eq] at h6
  norm_num at h6 h7 ⊢
  linarith

/-! ## Finite vectors pass the NaN/∞ guard -/

theorem isInf_false {x : Float32} (h : x.IsFinite) : x.isInf = false := by
  rw [Float32.isFinite_iff] at h
  show x.toModel.unpack.isInf = false
  revert h; cases x.toModel.unpack <;> simp [UnpackedFloat.isInf, UnpackedFloat.isFinite]

theorem vec_nan_false {v : Vector2f.State} (hx : v.x.IsFinite) (hy : v.y.IsFinite) :
    Vector2f.is_nan v = false := by
  simp [Vector2f.is_nan, Id.run, Float32.not_isNaN_of_isFinite hx,
    Float32.not_isNaN_of_isFinite hy]

theorem vec_inf_false {v : Vector2f.State} (hx : v.x.IsFinite) (hy : v.y.IsFinite) :
    Vector2f.is_inf v = false := by
  simp [Vector2f.is_inf, Id.run, isInf_false hx, isInf_false hy]

theorem vec_ok {t m : Vector2f.State} (htx : t.x.IsFinite) (hty : t.y.IsFinite)
    (hmx : m.x.IsFinite) (hmy : m.y.IsFinite) :
    (Vector2f.is_nan t || Vector2f.is_inf t || Vector2f.is_nan m || Vector2f.is_inf m) = false := by
  rw [vec_nan_false htx hty, vec_inf_false htx hty, vec_nan_false hmx hmy,
    vec_inf_false hmx hmy]; rfl

/-! ## The numeric calculus -/

theorem B32.lit {x : Float32} {v R : ℝ} (hx : x.IsFinite) (hv : x.toReal = v) (hR : |v| ≤ R) :
    B32 x v 0 R := (B32.of_exact hx (hv ▸ hR)).congr hv

theorem B32.val {x : Float32} {R : ℝ} (hx : x.IsFinite) (hR : |x.toReal| ≤ R) :
    B32 x x.toReal 0 R := B32.of_exact hx hR

/-- Multiplying by a `float` whose value is `1` is exact. -/
theorem mul_one_val {a b : Float32} (ha : a.IsFinite) (hb : b.IsFinite) (hb1 : b.toReal = 1) :
    (a * b).IsFinite ∧ (a * b).toReal = a.toReal :=
  Float32.mul_exact ha hb ha (by rw [hb1, mul_one])

theorem B32.mul_one {a b : Float32} {r e R : ℝ} (h : B32 a r e R) (hb : b.IsFinite)
    (hb1 : b.toReal = 1) : B32 (a * b) r e R :=
  ⟨A32.congr_x h.1 (mul_one_val h.1.1 hb hb1).1 (mul_one_val h.1.1 hb hb1).2, h.2⟩

theorem B32.add_zero {a z : Float32} {r e R : ℝ} (h : B32 a r e R) (hz : z.IsFinite)
    (h0 : z.toReal = 0) : B32 (a + z) r e R :=
  ⟨A32.congr_x h.1 (Float32.add_zero_val h.1.1 hz h0).1 (Float32.add_zero_val h.1.1 hz h0).2, h.2⟩

/-- A difference whose exact value is bounded directly (not by the sum of the bounds). -/
theorem B32.sub_R {a b : Float32} {ra rb ea eb Ra Rb e R : ℝ} (ha : B32 a ra ea Ra)
    (hb : B32 b rb eb Rb) (hR : |ra - rb| ≤ R) (hcap : R + ea + eb ≤ capF)
    (hc : ea + eb + 1 / 16777216 * (R + ea + eb) + 1 / 10 ^ 40 ≤ e) :
    B32 (a - b) (ra - rb) e R :=
  ⟨A32.sub_c ha.1 hb.1 hR hcap hc, hR⟩

/-- The same for a sum. -/
theorem B32.add_R {a b : Float32} {ra rb ea eb Ra Rb e R : ℝ} (ha : B32 a ra ea Ra)
    (hb : B32 b rb eb Rb) (hR : |ra + rb| ≤ R) (hcap : R + ea + eb ≤ capF)
    (hc : ea + eb + 1 / 16777216 * (R + ea + eb) + 1 / 10 ^ 40 ≤ e) :
    B32 (a + b) (ra + rb) e R :=
  ⟨A32.add_c ha.1 hb.1 hR hcap hc, hR⟩

theorem A32.shift {x : Float32} {r q e δ : ℝ} (h : A32 x r e) (hq : |r - q| ≤ δ) :
    A32 x q (e + δ) :=
  ⟨h.1, by
    calc |x.toReal - q| ≤ |x.toReal - r| + |r - q| := abs_sub_le _ _ _
      _ ≤ e + δ := add_le_add h.2 hq⟩

theorem A32.abs_le' {x : Float32} {r e : ℝ} (h : A32 x r e) : |x.toReal| ≤ |r| + e := by
  have := abs_sub_abs_le_abs_sub x.toReal r; linarith [h.2]

theorem N2_le_near (a b c d : ℝ) : N2 a b ≤ N2 c d + |a - c| + |b - d| := by
  have h := N2_add_le c d (a - c) (b - d)
  rw [show c + (a - c) = a by ring, show d + (b - d) = b by ring] at h
  linarith [N2_le_abs_add (a - c) (b - d)]

/-! ## The `float` length from above -/

set_option maxHeartbeats 1000000 in
/-- **The `float` length is at most the exact length** (up to `1 + 2⁻²²` and `2⁻⁷⁰`), for finite
components below `2⁴⁰`. -/
theorem flen_le {a b : Float32} (ha : a.IsFinite) (hb : b.IsFinite) (ha' : |a.toReal| ≤ 2 ^ 40)
    (hb' : |b.toReal| ≤ 2 ^ 40) :
    (Float32.sqrt (a * a + b * b)).IsFinite ∧ 0 ≤ (Float32.sqrt (a * a + b * b)).toReal ∧
      (Float32.sqrt (a * a + b * b)).toReal ≤
        N2 a.toReal b.toReal * (1 + 1 / 2 ^ 22) + 1 / 2 ^ 70 := by
  obtain ⟨fL, hL0, -, -⟩ := flen_ge ha hb ha' hb'
  obtain ⟨fa, na, ea⟩ := fsq ha ha'
  obtain ⟨fb, nb, eb⟩ := fsq hb hb'
  set x := a.toReal
  set y := b.toReal
  set sa := (a * a).toReal
  set sb := (b * b).toReal
  have hx2 : x ^ 2 ≤ 2 ^ 80 := by nlinarith [abs_nonneg x, sq_abs x]
  have hy2 : y ^ 2 ≤ 2 ^ 80 := by nlinarith [abs_nonneg y, sq_abs y]
  have hsa : sa ≤ 2 ^ 81 := by have := (abs_le.1 ea).2; nlinarith
  have hsb : sb ≤ 2 ^ 81 := by have := (abs_le.1 eb).2; nlinarith
  have hm : |sa + sb| ≤ maxFinite32 := by
    rw [abs_of_nonneg (by linarith)]; linarith [maxF_big, show (2 : ℝ) ^ 82 ≤ 2 ^ 100 by norm_num]
  obtain ⟨fS, eS⟩ := Float32.add_err_all fa fb hm
  set S := (a * a + b * b).toReal
  rw [abs_of_nonneg (by linarith : 0 ≤ sa + sb), u24] at eS
  have hS0 : 0 ≤ S := by have := (abs_le.1 eS).1; nlinarith
  have hS1 : S ≤ maxFinite32 := by
    have := (abs_le.1 eS).2; linarith [maxF_big, show (2 : ℝ) ^ 83 ≤ 2 ^ 100 by norm_num]
  obtain ⟨-, eL⟩ := Float32.sqrt_err_all fS hS0 hS1
  set L := (Float32.sqrt (a * a + b * b)).toReal
  rw [u24, e150] at eL
  refine ⟨fL, hL0, ?_⟩
  have hN0 : 0 ≤ N2 x y := N2_nonneg x y
  have hNsq : N2 x y ^ 2 = x ^ 2 + y ^ 2 := Real.sq_sqrt (by positivity)
  have eS' : S ≤ (sa + sb) * (1 + 1 / 16777216) := by
    have := (abs_le.1 eS).2; linarith
  have e1 : sa + sb ≤ (x ^ 2 + y ^ 2) * (1 + 1 / 16777216) + 2 * (1 / 2 ^ 150) := by
    have := (abs_le.1 ea).2; have := (abs_le.1 eb).2; linarith
  have e3 : S ≤ (N2 x y * (1 + 1 / 16777216) + 1 / 2 ^ 74) ^ 2 := by
    have h1 : S ≤ (x ^ 2 + y ^ 2) * (1 + 1 / 16777216) ^ 2 +
        2 * (1 / 2 ^ 150) * (1 + 1 / 16777216) := by
      have := mul_le_mul_of_nonneg_right e1 (by norm_num : (0 : ℝ) ≤ 1 + 1 / 16777216)
      nlinarith
    have h2 : 2 * (1 / 2 ^ 150 : ℝ) * (1 + 1 / 16777216) ≤ (1 / 2 ^ 74) ^ 2 := by norm_num
    have h3 : 0 ≤ 2 * (N2 x y * (1 + 1 / 16777216)) * (1 / 2 ^ 74) := by positivity
    rw [← hNsq] at h1
    nlinarith
  have e4 : Real.sqrt S ≤ N2 x y * (1 + 1 / 16777216) + 1 / 2 ^ 74 := by
    rw [Real.sqrt_le_left (by positivity)]; exact e3
  have e5 : L ≤ Real.sqrt S * (1 + 1 / 16777216) + 1 / 2 ^ 150 := by
    have := (abs_le.1 eL).2; nlinarith [Real.sqrt_nonneg S]
  have e6 : L ≤ (N2 x y * (1 + 1 / 16777216) + 1 / 2 ^ 74) * (1 + 1 / 16777216) + 1 / 2 ^ 150 :=
    e5.trans (by nlinarith [Real.sqrt_nonneg S])
  have e7 : (N2 x y * (1 + 1 / 16777216) + 1 / 2 ^ 74) * (1 + 1 / 16777216) + 1 / 2 ^ 150 ≤
      N2 x y * (1 + 1 / 2 ^ 22) + 1 / 2 ^ 70 := by
    have h1 : (1 + 1 / 16777216 : ℝ) * (1 + 1 / 16777216) ≤ 1 + 1 / 2 ^ 22 := by norm_num
    have h2 : (1 / 2 ^ 74 : ℝ) * (1 + 1 / 16777216) + 1 / 2 ^ 150 ≤ 1 / 2 ^ 70 := by norm_num
    nlinarith
  linarith

theorem limit_length_def (v : Vector2f.State) (m : Float32) :
    Vector2f.limit_length v m =
      if (decide (Float32.sqrt (v.x * v.x + v.y * v.y) > m) &&
        is_positive_float (Float32.sqrt (v.x * v.x + v.y * v.y))) = true then
        ({ x := v.x * (m / Float32.sqrt (v.x * v.x + v.y * v.y)),
           y := v.y * (m / Float32.sqrt (v.x * v.x + v.y * v.y)) }, true)
      else (v, false) := by
  unfold Vector2f.limit_length Vector2f.length norm_float2 sq_float
  rfl

/-- **`Vector2f::limit_length` is inactive below the limit**: for finite components below `2⁴⁰`
whose exact length satisfies `|v| (1 + 2⁻²²) + 2⁻⁷⁰ ≤ m`, the vector is returned unchanged. -/
theorem limit_length_inactive (v : Vector2f.State) (m : Float32) (hx : v.x.IsFinite)
    (hy : v.y.IsFinite) (hx' : |v.x.toReal| ≤ 2 ^ 40) (hy' : |v.y.toReal| ≤ 2 ^ 40)
    (hm : m.IsFinite) (hle : N2 v.x.toReal v.y.toReal * (1 + 1 / 2 ^ 22) + 1 / 2 ^ 70 ≤ m.toReal) :
    Vector2f.limit_length v m = (v, false) := by
  obtain ⟨fL, -, hL⟩ := flen_le hx hy hx' hy'
  rw [limit_length_def, ite_eq_right]
  intro h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  have := (Float32.lt_iff_toReal_lt hm fL).1 h.1
  linarith

/-! ## `limit_accel_xy` below the limit -/

set_option maxHeartbeats 1000000 in
/-- The `float` comparison `length_squared(a) ≤ sq(m)` holds when `|a| ≤ m (1 - 2⁻²⁰)`, for a
finite `m ≥ 2⁻²⁰` below `2⁴⁰`. -/
theorem lensq_le_sq {a : Vector2f.State} {m : Float32} (hx : a.x.IsFinite) (hy : a.y.IsFinite)
    (hx' : |a.x.toReal| ≤ 2 ^ 40) (hy' : |a.y.toReal| ≤ 2 ^ 40) (hm : m.IsFinite)
    (hm1 : 1 / 2 ^ 20 ≤ m.toReal) (hm2 : m.toReal ≤ 2 ^ 40)
    (hle : N2 a.x.toReal a.y.toReal ≤ m.toReal * (1 - 1 / 2 ^ 20)) :
    Vector2f.length_squared a ≤ sq_float m := by
  show a.x * a.x + a.y * a.y ≤ m * m
  obtain ⟨fa, na, ea⟩ := fsq hx hx'
  obtain ⟨fb, nb, eb⟩ := fsq hy hy'
  obtain ⟨fm, nm, em⟩ := fsq hm (by rw [abs_of_nonneg (by linarith)]; exact hm2)
  set x := a.x.toReal
  set y := a.y.toReal
  set sa := (a.x * a.x).toReal
  set sb := (a.y * a.y).toReal
  have hx2 : x ^ 2 ≤ 2 ^ 80 := by nlinarith [abs_nonneg x, sq_abs x]
  have hy2 : y ^ 2 ≤ 2 ^ 80 := by nlinarith [abs_nonneg y, sq_abs y]
  have hsa : sa ≤ 2 ^ 81 := by have := (abs_le.1 ea).2; nlinarith
  have hsb : sb ≤ 2 ^ 81 := by have := (abs_le.1 eb).2; nlinarith
  have hmS : |sa + sb| ≤ maxFinite32 := by
    rw [abs_of_nonneg (by linarith)]; linarith [maxF_big, show (2 : ℝ) ^ 82 ≤ 2 ^ 100 by norm_num]
  obtain ⟨fS, eS⟩ := Float32.add_err_all fa fb hmS
  rw [abs_of_nonneg (by linarith : 0 ≤ sa + sb), u24] at eS
  rw [Float32.le_iff_toReal_le fS fm]
  set S := (a.x * a.x + a.y * a.y).toReal
  set M := (m * m).toReal
  set mm := m.toReal
  have hN0 := N2_nonneg x y
  have hNsq : N2 x y ^ 2 = x ^ 2 + y ^ 2 := Real.sq_sqrt (by positivity)
  have hq : x ^ 2 + y ^ 2 ≤ mm ^ 2 * (1 - 1 / 2 ^ 20) ^ 2 := by
    rw [← hNsq]; exact pow_le_pow_left₀ hN0 hle 2 |>.trans_eq (by ring)
  have e1 : S ≤ (sa + sb) * (1 + 1 / 16777216) := by have := (abs_le.1 eS).2; linarith
  have e2 : sa + sb ≤ (x ^ 2 + y ^ 2) * (1 + 1 / 16777216) + 2 * (1 / 2 ^ 150) := by
    have := (abs_le.1 ea).2; have := (abs_le.1 eb).2; linarith
  have e3 : mm ^ 2 * (1 - 1 / 16777216) - 1 / 2 ^ 150 ≤ M := by
    have := (abs_le.1 em).1; linarith
  have hm2' : (1 / 2 ^ 40 : ℝ) ≤ mm ^ 2 := by nlinarith
  clear_value x y sa sb S M mm
  nlinarith

/-- **`limit_accel_xy` is inactive below the limit**: for a finite limit `m ∈ [2⁻²⁰, 2⁴⁰]` and a
finite acceleration with `|a| ≤ m (1 - 2⁻²⁰)`, the acceleration is returned unchanged and the
limit flag is `false`, whatever the reference velocity. -/
theorem limit_accel_xy_inactive (v a : Vector2f.State) (m : Float32) (hx : a.x.IsFinite)
    (hy : a.y.IsFinite) (hx' : |a.x.toReal| ≤ 2 ^ 40) (hy' : |a.y.toReal| ≤ 2 ^ 40)
    (hm : m.IsFinite) (hm1 : 1 / 2 ^ 20 ≤ m.toReal) (hm2 : m.toReal ≤ 2 ^ 40)
    (hle : N2 a.x.toReal a.y.toReal ≤ m.toReal * (1 - 1 / 2 ^ 20)) :
    limit_accel_xy v a m = (a, false) := by
  have h1 : is_positive_float m = true :=
    (isPos_iff hm).2 (le_trans (by norm_num) hm1)
  exact limit_accel_xy_within v a m h1 (lensq_le_sq hx hy hx' hy' hm hm1 hm2 hle)

end

end Contracts.Track.HCtl
