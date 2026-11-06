import Contracts.Track.CtrlHorizontalBase

/-!
# C-series, `AC_P_2D::update_all` of the horizontal position loop (milestone M6)

`AC_PosControl::NE_update_controller` calls `_p_pos_ne_m.update_all(pos_target, pos_estimate)`
(`AC_P_2D.cpp:26-38`): the error `(target - measurement).tofloat()`, the error limit
`limit_length(_error_max)`, and `sqrt_controller(error, kp, _D1_max, 0)` (`control.cpp:616-625`,
`575-610`), which scales the error vector by `correction_length / error_length`. In its linear zone
(`|error| ≤ D1_max / kp²`) the correction is `error_length · kp`, so the output is
`error · ((|e| kp) / |e|)`, which is `kp · error` up to three roundings.

* `p_update_all_eq`: with the error limit inactive (`_error_max` not positive, or the error
  within it), the target is returned unchanged and the output is
  `sqrt_controller(error, kp, D1_max, 0)`;
* `sqrtc_lin`: `sqrt_controller` in the linear zone is `error_length * kp`;
* `ratio_near`: `(L · kp) / L` is within `2.1·10⁻⁷` of `kp = 1.5`, for `L ∈ [2⁻²³, 1]`;
* `p_spec`: per axis, `⟦vt⟧ = kpPos (⟦pos_target⟧ - ⟦pos_estimate⟧) + β` with `|β| ≤ 2.5·10⁻⁷`,
  for `kp = 1.5`, `D1_max ∈ [1, 2²⁰]`, `_error_max` either not positive or at least `1/2`, finite
  `double` positions below `2³⁰` and the error (the exact difference of the `double`s, as a
  2-vector) at most `2/5` (the linear zone needs `D1_max / kp² ≥ 4/9`). Below `2⁻²³` the code
  returns the zero vector (`is_positive(error_length)` false); `kp · error` is then below
  `1.8·10⁻⁷`, inside the same `β`.
-/

namespace Contracts.Track.HCtl

open AC_PosControl_lib Contracts.Quick Contracts.Mission Float.Model UnpackedFloat

noncomputable section

/-- The position error as the code computes it: the `double` difference, rounded to `float`. -/
def pErr (tg ms : Vector2p.State) : Vector2f.State :=
  { x := Float.toFloat32 (tg.x - ms.x), y := Float.toFloat32 (tg.y - ms.y) }

/-- **The structure of `AC_P_2D::update_all`** with the error limit inactive. -/
theorem p_update_all_eq (pp : AC_P_2D.Params) (s : AC_P_2D.State) (tg ms : Vector2p.State)
    (hlim : is_positive_float s._error_max = true →
      Vector2f.limit_length (pErr tg ms) s._error_max = (pErr tg ms, false)) :
    AC_P_2D.update_all pp s tg ms =
      ({ s with _error := pErr tg ms }, tg,
        sqrt_controller_Vector2f_float3 (pErr tg ms) pp._kp s._D1_max
          (Float.toFloat32 (0.0 : Float))) := by
  have he : Vector2p.tofloat (Vector2p.op_sub_Vector2p tg ms) = pErr tg ms := rfl
  unfold AC_P_2D.update_all
  simp only [Id.run, he]
  rcases h : is_positive_float s._error_max with _ | _
  · rfl
  · simp only [hlim h]
    rfl

/-- `sqrt_controller` for a vector: the scaling of the error by `correction / length`. -/
theorem sqrtc_vec_eq (e : Vector2f.State) (p D1 dt : Float32) :
    sqrt_controller_Vector2f_float3 e p D1 dt =
      if is_positive_float (Vector2f.length e) = true then
        { x := e.x * (sqrt_controller_float4 (Vector2f.length e) p D1 dt / Vector2f.length e),
          y := e.y * (sqrt_controller_float4 (Vector2f.length e) p D1 dt / Vector2f.length e) }
      else Vector2f.init_void := by
  unfold sqrt_controller_Vector2f_float3
  cases h : is_positive_float (Vector2f.length e) <;> simp only [Id.run, h, Bool.not_false,
    Bool.not_true, ite_true, ite_false, Bool.false_eq_true] <;> rfl

theorem isZero_false' {x : Float32} (hx : x.IsFinite) (h : 2 ^ (-23 : ℤ) ≤ |x.toReal|) :
    is_zero_float x = false := by
  rcases hz : is_zero_float x with _ | _
  · rfl
  · have := (isZero_iff hx).1 hz; linarith

/-- **`sqrt_controller` in its linear zone** (`second_ord_lim = D1 ≥ 1`, `p = 1.5`, `dt = 0`,
`0 ≤ error ≤ 4/9 · (1 - 2⁻²⁰)`): the correction is `error * p`. -/
theorem sqrtc_lin (hL : LibmSpec) {L p D1 : Float32} (hLf : L.IsFinite) (hL0 : 0 ≤ L.toReal)
    (hL1 : L.toReal ≤ 4 / 9 * (1 - 1 / 2 ^ 20)) (hp : p.IsFinite) (hpv : p.toReal = 3 / 2)
    (hD : D1.IsFinite) (hD1 : 1 ≤ D1.toReal) (hD2 : D1.toReal ≤ 2 ^ 20) :
    sqrt_controller_float4 L p D1 (Float.toFloat32 (0.0 : Float)) = L * p := by
  obtain ⟨fz, ez⟩ := f32_isFinite_toFloat32_0 hL
  have hnD : is_negative_float D1 = false := isNeg_false hL hD (by linarith)
  have hzD : is_zero_float D1 = false := isZero_false' hD (by
    rw [abs_of_nonneg (by linarith)]; exact le_trans (by norm_num) hD1)
  have hzp : is_zero_float p = false := isZero_false' hp (by rw [hpv]; norm_num)
  have hpz : is_positive_float (Float.toFloat32 (0.0 : Float)) = false := by
    rcases h : is_positive_float (Float.toFloat32 (0.0 : Float)) with _ | _
    · rfl
    · have := (isPos_iff fz).1 h; rw [ez] at this; exact absurd this (by norm_num)
  -- the linear distance `D1 / (p * p)`
  have hpp := Float32.mul_err_all hp hp (by rw [hpv]; norm_num [maxFinite32])
  rw [hpv] at hpp
  have hpp1 : |(p * p).toReal - 9 / 4| ≤ 9 / 4 / 2 ^ 24 + 1 / 2 ^ 150 := by
    have := hpp.2; norm_num at this ⊢; linarith
  have hppv : 2 ≤ (p * p).toReal ∧ (p * p).toReal ≤ 9 / 4 * (1 + 1 / 2 ^ 23) := by
    have h := abs_le.1 hpp1
    have c1 : (9 / 4 : ℝ) / 2 ^ 24 + 1 / 2 ^ 150 ≤ 1 / 4 := by norm_num
    have c2 : (9 / 4 : ℝ) + (9 / 4 / 2 ^ 24 + 1 / 2 ^ 150) ≤ 9 / 4 * (1 + 1 / 2 ^ 23) := by norm_num
    constructor <;> linarith [h.1, h.2]
  have hq : |D1.toReal / (p * p).toReal| ≤ maxFinite32 := by
    rw [abs_div, abs_of_nonneg (by linarith), abs_of_nonneg (by linarith),
      div_le_iff₀ (by linarith)]
    have : (2 : ℝ) ^ 20 * 3 ≤ maxFinite32 := by norm_num [maxFinite32]
    nlinarith [hppv.1]
  obtain ⟨fld, eld⟩ := Float32.div_err_all hD hpp.1 (by linarith) hq
  have hratio : 4 / 9 * (1 - 1 / 2 ^ 23) ≤ D1.toReal / (p * p).toReal := by
    rw [le_div_iff₀ (by linarith)]
    have : (4 / 9 * (1 - 1 / 2 ^ 23)) * (9 / 4 * (1 + 1 / 2 ^ 23)) ≤ 1 := by norm_num
    have h0 : (0 : ℝ) ≤ 4 / 9 * (1 - 1 / 2 ^ 23) := by norm_num
    nlinarith [mul_le_mul_of_nonneg_left hppv.2 h0]
  have hld : 4 / 9 * (1 - 1 / 2 ^ 21) ≤ (D1 / (p * p)).toReal := by
    have h1 := (abs_le.1 eld).1
    have h2 : (0 : ℝ) ≤ D1.toReal / (p * p).toReal := div_nonneg (by linarith) (by linarith)
    rw [abs_of_nonneg h2] at h1
    norm_num at h1 ⊢
    nlinarith
  have hgt : ¬ L > D1 / sq_float p := by
    intro h
    have := (Float32.lt_iff_toReal_lt fld hLf).1 h
    nlinarith
  have hlt : ¬ L < -(D1 / sq_float p) := by
    intro h
    have := (Float32.lt_iff_toReal_lt hLf ((Float32.isFinite_neg _).2 fld)).1 h
    rw [Float32.toReal_neg] at this
    nlinarith
  unfold sqrt_controller_float4
  simp only [Id.run, hnD, hzD, Bool.or_self, Bool.false_eq_true, ite_false, hzp, hgt, hlt,
    hpz, pure]

set_option maxHeartbeats 1000000 in
/-- **The scaling factor** `(L · p) / L` is within `2.1·10⁻⁷` of `p = 1.5`, for `L ∈ [2⁻²³, 1]`. -/
theorem ratio_near {L p : Float32} (hLf : L.IsFinite) (hL0 : 1 / 2 ^ 23 ≤ L.toReal)
    (hL1 : L.toReal ≤ 1) (hp : p.IsFinite) (hpv : p.toReal = 3 / 2) :
    (L * p / L).IsFinite ∧ |(L * p / L).toReal - 3 / 2| ≤ 21 / 10 ^ 8 := by
  have hLp : 0 < L.toReal := lt_of_lt_of_le (by norm_num) hL0
  have hl32 : |L.toReal * (3 / 2)| = L.toReal * (3 / 2) := abs_of_nonneg (by linarith)
  obtain ⟨fm, em⟩ := Float32.mul_err_all hLf hp (by
    rw [hpv, hl32]
    have : (1 : ℝ) * (3 / 2) ≤ maxFinite32 := by norm_num [maxFinite32]
    nlinarith)
  rw [hpv, hl32] at em
  set m := (L * p).toReal
  set l := L.toReal
  have hml : |m / l - 3 / 2| ≤ 3 / 2 / 2 ^ 24 + 1 / 2 ^ 127 := by
    rw [show m / l - 3 / 2 = (m - l * (3 / 2)) / l by field_simp, abs_div, abs_of_pos hLp,
      div_le_iff₀ hLp]
    have h1 : (2 : ℝ) ^ (-24 : ℤ) * (l * (3 / 2)) + 2 ^ (-150 : ℤ) ≤
        (3 / 2 / 2 ^ 24 + 1 / 2 ^ 127) * l := by
      have : (2 : ℝ) ^ (-150 : ℤ) ≤ 1 / 2 ^ 127 * l := by
        have h3 : (2 : ℝ) ^ (-150 : ℤ) = 1 / 2 ^ 127 * (1 / 2 ^ 23) := by norm_num
        rw [h3]; gcongr
      have h4 : (2 : ℝ) ^ (-24 : ℤ) * (l * (3 / 2)) = 3 / 2 / 2 ^ 24 * l := by
        rw [show (2 : ℝ) ^ (-24 : ℤ) = 1 / 2 ^ 24 by norm_num]; ring
      linarith
    exact em.trans h1
  have hq2 : |m / l| ≤ 2 := by
    have := abs_sub_abs_le_abs_sub (m / l) (3 / 2)
    rw [abs_of_pos (by norm_num : (0 : ℝ) < 3 / 2)] at this
    have : (3 / 2 / 2 ^ 24 + 1 / 2 ^ 127 : ℝ) ≤ 1 / 2 := by norm_num
    linarith
  obtain ⟨fq, eq⟩ := Float32.div_err_all fm hLf hLp.ne' (hq2.trans (by norm_num [maxFinite32]))
  refine ⟨fq, ?_⟩
  have h5 : |(L * p / L).toReal - 3 / 2| ≤ |(L * p / L).toReal - m / l| + |m / l - 3 / 2| :=
    abs_sub_le _ _ _
  have h6 : (2 : ℝ) ^ (-24 : ℤ) * |m / l| + 2 ^ (-150 : ℤ) ≤ 2 / 2 ^ 24 + 1 / 2 ^ 150 := by
    rw [show (2 : ℝ) ^ (-24 : ℤ) = 1 / 2 ^ 24 by norm_num,
      show (2 : ℝ) ^ (-150 : ℤ) = 1 / 2 ^ 150 by norm_num]
    nlinarith
  have h7 : (2 / 2 ^ 24 + 1 / 2 ^ 150 : ℝ) + (3 / 2 / 2 ^ 24 + 1 / 2 ^ 127) ≤ 21 / 10 ^ 8 := by
    norm_num
  linarith

/-- One output component: `e * q` with `q` near `1.5`, against `1.5 · d` for `e` near `d`. -/
theorem out_comp {e q : Float32} {d : ℝ} (he : e.IsFinite) (hq : q.IsFinite)
    (hqn : |q.toReal - 3 / 2| ≤ 21 / 10 ^ 8) (hed : |e.toReal - d| ≤ 3 / 10 ^ 8)
    (heb : |e.toReal| ≤ 41 / 100) :
    (e * q).IsFinite ∧ |(e * q).toReal - 3 / 2 * d| ≤ 25 / 10 ^ 8 := by
  have hqb : |q.toReal| ≤ 2 := by
    have := abs_sub_abs_le_abs_sub q.toReal (3 / 2)
    rw [abs_of_pos (by norm_num : (0 : ℝ) < 3 / 2)] at this; linarith
  have hP : |e.toReal * q.toReal| ≤ 41 / 100 * 2 := by
    rw [abs_mul]; exact mul_le_mul heb hqb (abs_nonneg _) (by norm_num)
  obtain ⟨f, err⟩ := Float32.mul_err_all he hq (hP.trans (by norm_num [maxFinite32]))
  refine ⟨f, ?_⟩
  have h1 : |e.toReal * q.toReal - 3 / 2 * e.toReal| ≤ 41 / 100 * (21 / 10 ^ 8) := by
    rw [show e.toReal * q.toReal - 3 / 2 * e.toReal = e.toReal * (q.toReal - 3 / 2) by ring,
      abs_mul]
    exact mul_le_mul heb hqn (abs_nonneg _) (by norm_num)
  have h2 : |3 / 2 * e.toReal - 3 / 2 * d| ≤ 3 / 2 * (3 / 10 ^ 8) := by
    rw [← mul_sub, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 3 / 2)]
    exact mul_le_mul_of_nonneg_left hed (by norm_num)
  have h3 : (2 : ℝ) ^ (-24 : ℤ) * |e.toReal * q.toReal| + 2 ^ (-150 : ℤ) ≤
      1 / 2 ^ 24 * (41 / 100 * 2) + 1 / 2 ^ 150 := by
    rw [show (2 : ℝ) ^ (-24 : ℤ) = 1 / 2 ^ 24 by norm_num,
      show (2 : ℝ) ^ (-150 : ℤ) = 1 / 2 ^ 150 by norm_num]
    nlinarith
  have h4 := abs_sub_le (e * q).toReal (e.toReal * q.toReal) (3 / 2 * e.toReal)
  have h5 := abs_sub_le (e * q).toReal (3 / 2 * e.toReal) (3 / 2 * d)
  have h6 : (1 / 2 ^ 24 * (41 / 100 * 2) + 1 / 2 ^ 150 : ℝ) + 41 / 100 * (21 / 10 ^ 8) +
      3 / 2 * (3 / 10 ^ 8) ≤ 25 / 10 ^ 8 := by norm_num
  have h7 := err.trans h3
  linarith [h7, h4, h5, h1, h2, h6]

/-- The `float` error component: the `double` difference rounded to `float`. -/
theorem err_comp (hL : LibmSpec) {a b : Float} (ha : a.IsFinite) (hb : b.IsFinite)
    (hd : |a.toReal - b.toReal| ≤ 2 / 5) :
    A32 (Float.toFloat32 (a - b)) (a.toReal - b.toReal) (3 / 10 ^ 8) := by
  have hc : (2 / 5 : ℝ) ≤ capF := by norm_num [capF]
  have h := A64.sub (A64.of_exact ha) (A64.of_exact hb) (by simp only [add_zero]; linarith)
  simp only [add_zero, zero_add] at h
  have h2 := A64.toFloat32 hL h (by
    have : u64 * |a.toReal - b.toReal| + η64 ≤ 1 := by
      have k1 := η64_small
      have k2 : u64 * |a.toReal - b.toReal| ≤ 1 / 2 ^ 53 * (2 / 5) := by
        simp only [u64]; rw [show (2 : ℝ) ^ (-53 : ℤ) = 1 / 2 ^ 53 by norm_num]
        exact mul_le_mul_of_nonneg_left hd (by norm_num)
      have k3 : (1 / 2 ^ 53 * (2 / 5) : ℝ) + 1 / 10 ^ 40 ≤ 1 := by norm_num
      exact (add_le_add k2 k1).trans k3
    have hc1 : (2 / 5 + 1 : ℝ) ≤ capF := by norm_num [capF]
    linarith)
  refine h2.mono ?_
  have e1 : u64 * |a.toReal - b.toReal| ≤ 1 / 2 ^ 53 * (2 / 5) := by
    simp only [u64]; rw [show (2 : ℝ) ^ (-53 : ℤ) = 1 / 2 ^ 53 by norm_num]
    exact mul_le_mul_of_nonneg_left hd (by norm_num)
  have e2 := η64_small
  have e3 := η32_small
  have e4 : u32 * (|a.toReal - b.toReal| + (u64 * |a.toReal - b.toReal| + η64)) ≤
      1 / 2 ^ 24 * (2 / 5 + 1 / 10 ^ 10) := by
    simp only [u32]; rw [show (2 : ℝ) ^ (-24 : ℤ) = 1 / 2 ^ 24 by norm_num]
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    have : (1 / 2 ^ 53 * (2 / 5) : ℝ) + 1 / 10 ^ 40 ≤ 1 / 10 ^ 10 := by norm_num
    linarith
  have e5 : (1 / 2 ^ 53 * (2 / 5) + 1 / 10 ^ 40 : ℝ) + 1 / 2 ^ 24 * (2 / 5 + 1 / 10 ^ 10) +
      1 / 10 ^ 40 ≤ 3 / 10 ^ 8 := by norm_num
  linarith

/-- The parameters and state of `_p_pos_ne_m` the lemma needs (the mission's values). -/
structure PosGains (pp : AC_P_2D.Params) (s : AC_P_2D.State) : Prop where
  kp : pp._kp.IsFinite ∧ pp._kp.toReal = 3 / 2
  D1 : s._D1_max.IsFinite ∧ 1 ≤ s._D1_max.toReal ∧ s._D1_max.toReal ≤ 2 ^ 20
  emax : s._error_max.IsFinite ∧ (s._error_max.toReal < 2 ^ (-23 : ℤ) ∨ 1 / 2 ≤ s._error_max.toReal)

/-- The region of one tick of the position P controller: finite `double` positions, the error
(exact difference of the `double`s) at most `2/5` as a 2-vector. -/
structure PosRegion (tg ms : Vector2p.State) : Prop where
  tx : tg.x.IsFinite
  ty : tg.y.IsFinite
  mx : ms.x.IsFinite
  my : ms.y.IsFinite
  e : N2 (tg.x.toReal - ms.x.toReal) (tg.y.toReal - ms.y.toReal) ≤ 2 / 5

set_option maxHeartbeats 1000000 in
/-- **C-series, the position P controller** (`AC_P_2D::update_all`, `PSC_NE_POS_P = 1.5`, linear
zone): the target is returned unchanged and each component of the output is
`1.5 (target - measurement)` within `2.5·10⁻⁷`. -/
theorem p_spec (hL : LibmSpec) (pp : AC_P_2D.Params) (s : AC_P_2D.State) (tg ms : Vector2p.State)
    (g : PosGains pp s) (hR : PosRegion tg ms) :
    let r := AC_P_2D.update_all pp s tg ms
    r.2.1 = tg ∧ r.1 = { s with _error := pErr tg ms } ∧
      A32 r.2.2.x (3 / 2 * (tg.x.toReal - ms.x.toReal)) (25 / 10 ^ 8) ∧
      A32 r.2.2.y (3 / 2 * (tg.y.toReal - ms.y.toReal)) (25 / 10 ^ 8) := by
  show (AC_P_2D.update_all pp s tg ms).2.1 = tg ∧ _
  obtain ⟨hdx, hdy⟩ := abs_le_N2 (tg.x.toReal - ms.x.toReal) (tg.y.toReal - ms.y.toReal)
  have ex : A32 (pErr tg ms).x _ _ := err_comp hL hR.tx hR.mx (hdx.trans hR.e)
  have ey : A32 (pErr tg ms).y _ _ := err_comp hL hR.ty hR.my (hdy.trans hR.e)
  have exb : |(pErr tg ms).x.toReal| ≤ 41 / 100 := by
    have := A32.abs_le' ex; linarith [hdx.trans hR.e]
  have eyb : |(pErr tg ms).y.toReal| ≤ 41 / 100 := by
    have := A32.abs_le' ey; linarith [hdy.trans hR.e]
  -- the error limit is inactive
  have hlim : is_positive_float s._error_max = true →
      Vector2f.limit_length (pErr tg ms) s._error_max = (pErr tg ms, false) := by
    intro hp
    have h2 := (isPos_iff g.emax.1).1 hp
    have h3 : 1 / 2 ≤ s._error_max.toReal := by
      rcases g.emax.2 with h | h
      · exact absurd h (not_lt.2 h2)
      · exact h
    apply limit_length_inactive (pErr tg ms) _ ex.1 ey.1 (exb.trans (by norm_num))
      (eyb.trans (by norm_num)) g.emax.1
    have hN := N2_le_near (pErr tg ms).x.toReal (pErr tg ms).y.toReal
      (tg.x.toReal - ms.x.toReal) (tg.y.toReal - ms.y.toReal)
    have := hR.e
    have := ex.2
    have := ey.2
    have hN0 := N2_nonneg (pErr tg ms).x.toReal (pErr tg ms).y.toReal
    nlinarith
  rw [p_update_all_eq pp s tg ms hlim]
  refine ⟨rfl, rfl, ?_⟩
  dsimp only
  generalize hE : pErr tg ms = e at ex ey exb eyb
  obtain ⟨fL, hL0, hLle⟩ := flen_le ex.1 ey.1 (exb.trans (by norm_num)) (eyb.trans (by norm_num))
  have hLe : Vector2f.length e = Float32.sqrt (e.x * e.x + e.y * e.y) := rfl
  have hN : N2 e.x.toReal e.y.toReal ≤ 2 / 5 + 6 / 10 ^ 8 := by
    have := N2_le_near e.x.toReal e.y.toReal (tg.x.toReal - ms.x.toReal)
      (tg.y.toReal - ms.y.toReal)
    linarith [ex.2, ey.2, hR.e]
  rw [← hLe] at fL hL0 hLle
  have hL1 : (Vector2f.length e).toReal ≤ 41 / 100 := by
    have := N2_nonneg e.x.toReal e.y.toReal
    nlinarith
  rw [sqrtc_vec_eq]
  by_cases hpos : is_positive_float (Vector2f.length e) = true
  · rw [ite_eq_left hpos]
    have hLpos := (isPos_iff fL).1 hpos
    have h23 : (2 : ℝ) ^ (-23 : ℤ) = 1 / 2 ^ 23 := by norm_num
    rw [h23] at hLpos
    rw [sqrtc_lin hL fL hL0 (by linarith) g.kp.1 g.kp.2 g.D1.1 g.D1.2.1 g.D1.2.2]
    obtain ⟨fq, hq⟩ := ratio_near fL hLpos (by linarith) g.kp.1 g.kp.2
    exact ⟨out_comp ex.1 fq hq ex.2 exb, out_comp ey.1 fq hq ey.2 eyb⟩
  · rw [ite_eq_right hpos]
    have hLsmall : (Vector2f.length e).toReal < 1 / 2 ^ 23 := by
      by_contra h
      have h23 : (2 : ℝ) ^ (-23 : ℤ) = 1 / 2 ^ 23 := by norm_num
      exact hpos ((isPos_iff fL).2 (by rw [h23]; linarith))
    obtain ⟨-, -, -, hge⟩ := flen_ge ex.1 ey.1 (exb.trans (by norm_num)) (eyb.trans (by norm_num))
    rw [← hLe] at hge
    have hNs : N2 e.x.toReal e.y.toReal ≤ 1 / 2 ^ 23 * (1 + 1 / 2 ^ 21) + 1 / 2 ^ 74 := by
      apply N2_le_of_sq (by norm_num)
      refine hge.trans (pow_le_pow_left₀ (by positivity) ?_ 2)
      nlinarith
    obtain ⟨ax, ay⟩ := abs_le_N2 e.x.toReal e.y.toReal
    have z : (Vector2f.init_void).x = Int32.toFloat32 0 := rfl
    have z' : (Vector2f.init_void).y = Int32.toFloat32 0 := rfl
    have h2 : (3 / 2 : ℝ) * ((1 / 2 ^ 23 * (1 + 1 / 2 ^ 21) + 1 / 2 ^ 74) + 3 / 10 ^ 8) ≤
        25 / 10 ^ 8 := by norm_num
    refine ⟨⟨by rw [z]; exact Float32.isFinite_int32_zero, ?_⟩,
      ⟨by rw [z']; exact Float32.isFinite_int32_zero, ?_⟩⟩
    · rw [z, Float32.toReal_int32_zero, zero_sub, abs_neg, abs_mul,
        abs_of_pos (by norm_num : (0 : ℝ) < 3 / 2)]
      have := ex.2
      have h1 : |tg.x.toReal - ms.x.toReal| ≤ |e.x.toReal| + 3 / 10 ^ 8 := by
        have := abs_sub_abs_le_abs_sub (tg.x.toReal - ms.x.toReal) e.x.toReal
        rw [abs_sub_comm (tg.x.toReal - ms.x.toReal) e.x.toReal] at this; linarith
      calc 3 / 2 * |tg.x.toReal - ms.x.toReal|
          ≤ 3 / 2 * ((1 / 2 ^ 23 * (1 + 1 / 2 ^ 21) + 1 / 2 ^ 74) + 3 / 10 ^ 8) := by
            gcongr; linarith [ax, hNs, h1]
        _ ≤ 25 / 10 ^ 8 := h2
    · rw [z', Float32.toReal_int32_zero, zero_sub, abs_neg, abs_mul,
        abs_of_pos (by norm_num : (0 : ℝ) < 3 / 2)]
      have := ey.2
      have h1 : |tg.y.toReal - ms.y.toReal| ≤ |e.y.toReal| + 3 / 10 ^ 8 := by
        have := abs_sub_abs_le_abs_sub (tg.y.toReal - ms.y.toReal) e.y.toReal
        rw [abs_sub_comm (tg.y.toReal - ms.y.toReal) e.y.toReal] at this; linarith
      calc 3 / 2 * |tg.y.toReal - ms.y.toReal|
          ≤ 3 / 2 * ((1 / 2 ^ 23 * (1 + 1 / 2 ^ 21) + 1 / 2 ^ 74) + 3 / 10 ^ 8) := by
            gcongr; linarith [ay, hNs, h1]
        _ ≤ 25 / 10 ^ 8 := h2

end

end Contracts.Track.HCtl
