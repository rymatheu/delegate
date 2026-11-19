import Contracts.Mission.NavFloat

/-!
# A numeric calculus for `float` approximations

`A32 x r e` (`NavFloat.lean`): the `float` `x` is finite and within `e` of the real `r`. The lemmas
here propagate it through one rounded operation with numeric side conditions: magnitudes of the
exact operands bounded by constants, and the new error bound a constant, checked by `norm_num`.
This keeps the error terms of long chains numeric.
-/

namespace Contracts.Mission

open Float.Model UnpackedFloat

noncomputable section

theorem u32_eq : u32 = 1 / 16777216 := by norm_num [u32]
theorem u64_eq : u64 = 1 / 9007199254740992 := by norm_num [u64]

theorem A32.add_c {a b : Float32} {ra rb ea eb e R : ℝ} (ha : A32 a ra ea) (hb : A32 b rb eb)
    (hR : |ra + rb| ≤ R) (hcap : R + ea + eb ≤ capF)
    (hc : ea + eb + 1 / 16777216 * (R + ea + eb) + 1 / 10 ^ 40 ≤ e) : A32 (a + b) (ra + rb) e := by
  have h := A32.add ha hb (by linarith)
  refine h.mono ?_
  rw [u32_eq]
  have := η32_small
  have : 1 / 16777216 * (|ra + rb| + ea + eb) ≤ 1 / 16777216 * (R + ea + eb) := by linarith
  linarith

theorem A32.sub_c {a b : Float32} {ra rb ea eb e R : ℝ} (ha : A32 a ra ea) (hb : A32 b rb eb)
    (hR : |ra - rb| ≤ R) (hcap : R + ea + eb ≤ capF)
    (hc : ea + eb + 1 / 16777216 * (R + ea + eb) + 1 / 10 ^ 40 ≤ e) : A32 (a - b) (ra - rb) e := by
  have h := A32.sub ha hb (by linarith)
  refine h.mono ?_
  rw [u32_eq]
  have := η32_small
  have : 1 / 16777216 * (|ra - rb| + ea + eb) ≤ 1 / 16777216 * (R + ea + eb) := by linarith
  linarith

theorem A32.mul_c {a b : Float32} {ra rb ea eb e Ra Rb : ℝ} (ha : A32 a ra ea) (hb : A32 b rb eb)
    (hRa : |ra| ≤ Ra) (hRb : |rb| ≤ Rb) (hea : 0 ≤ ea) (heb : 0 ≤ eb)
    (hcap : Ra * Rb + (Ra * eb + Rb * ea + ea * eb) ≤ capF)
    (hc : Ra * eb + Rb * ea + ea * eb + 1 / 16777216 * (Ra * Rb + (Ra * eb + Rb * ea + ea * eb)) +
      1 / 10 ^ 40 ≤ e) : A32 (a * b) (ra * rb) e := by
  have h1 : |ra| * eb ≤ Ra * eb := mul_le_mul_of_nonneg_right hRa heb
  have h2 : |rb| * ea ≤ Rb * ea := mul_le_mul_of_nonneg_right hRb hea
  have h3 : |ra * rb| ≤ Ra * Rb := by
    rw [abs_mul]; exact mul_le_mul hRa hRb (abs_nonneg _) ((abs_nonneg _).trans hRa)
  have h := A32.mul ha hb (by linarith)
  refine h.mono ?_
  rw [u32_eq]
  have := η32_small
  have : 1 / 16777216 * (|ra * rb| + (|ra| * eb + |rb| * ea + ea * eb)) ≤
      1 / 16777216 * (Ra * Rb + (Ra * eb + Rb * ea + ea * eb)) := by linarith
  linarith

theorem A32.div_c {a b : Float32} {ra rb ea eb e Ra m Q : ℝ} (ha : A32 a ra ea) (hb : A32 b rb eb)
    (hRa : |ra| ≤ Ra) (hm : 0 < m) (hmb : m + eb ≤ |rb|) (heb : 0 ≤ eb)
    (hQ : |ra / rb| ≤ Q) (hcap : Q + (ea / m + Ra * eb / (m * (m + eb))) ≤ capF)
    (hc : ea / m + Ra * eb / (m * (m + eb)) + 1 / 16777216 * (Q + (ea / m + Ra * eb / (m * (m + eb)))) +
      1 / 10 ^ 40 ≤ e) : A32 (a / b) (ra / rb) e := by
  have hrb0 : 0 < |rb| := by linarith
  have hE : (|rb| * ea + |ra| * eb) / (m * |rb|) ≤ ea / m + Ra * eb / (m * (m + eb)) := by
    rw [add_div, mul_comm m |rb|, mul_div_mul_left _ _ hrb0.ne', mul_comm |rb| m]
    have : |ra| * eb / (m * |rb|) ≤ Ra * eb / (m * (m + eb)) := by
      apply div_le_div₀ (mul_nonneg ((abs_nonneg _).trans hRa) heb) (mul_le_mul_of_nonneg_right hRa heb) (by positivity)
      exact mul_le_mul_of_nonneg_left hmb hm.le
    linarith
  have h := A32.div ha hb hm hmb (by linarith)
  refine h.mono ?_
  rw [u32_eq]
  have := η32_small
  have : 1 / 16777216 * (|ra / rb| + (|rb| * ea + |ra| * eb) / (m * |rb|)) ≤
      1 / 16777216 * (Q + (ea / m + Ra * eb / (m * (m + eb)))) := by
    have := add_le_add hQ hE
    linarith
  linarith

/-- `√` of a positive approximation: the error divides by `√r₀`. -/
theorem A32.sqrt_c {a : Float32} {ra ea e r0 s0 Rs : ℝ} (ha : A32 a ra ea) (h0 : 0 ≤ a.toReal)
    (hr0 : r0 ≤ ra) (hs0 : 0 < s0) (hs0' : s0 ≤ Real.sqrt r0) (hRs : Real.sqrt ra ≤ Rs)
    (hcap : |ra| + ea ≤ capF)
    (hc : ea / s0 + 1 / 16777216 * (Rs + ea / s0) + 1 / 10 ^ 40 ≤ e) :
    A32 (Float32.sqrt a) (Real.sqrt ra) e := by
  have hm : a.toReal ≤ maxFinite32 := by
    have := (_root_.abs_le.1 (show |a.toReal - ra| ≤ ea from ha.2)).2
    have := le_abs_self ra
    linarith [capF_le_max32]
  obtain ⟨hf, he⟩ := Float32.sqrt_err_all ha.1 h0 hm
  refine ⟨hf, ?_⟩
  have hsr : 0 < Real.sqrt ra := lt_of_lt_of_le hs0 (hs0'.trans (Real.sqrt_le_sqrt hr0))
  have hx : |Real.sqrt a.toReal - Real.sqrt ra| ≤ ea / s0 := by
    have hra : 0 < ra := Real.sqrt_pos.1 hsr
    have key : |Real.sqrt a.toReal - Real.sqrt ra| * (Real.sqrt a.toReal + Real.sqrt ra) =
        |a.toReal - ra| := by
      rw [← abs_of_pos (by positivity : 0 < Real.sqrt a.toReal + Real.sqrt ra), ← abs_mul]
      congr 1
      have := Real.sq_sqrt h0; have := Real.sq_sqrt hra.le; nlinarith
    rw [le_div_iff₀ hs0]
    have hge : s0 ≤ Real.sqrt a.toReal + Real.sqrt ra := by
      have := Real.sqrt_nonneg a.toReal
      linarith [hs0'.trans (Real.sqrt_le_sqrt hr0)]
    calc |Real.sqrt a.toReal - Real.sqrt ra| * s0
        ≤ |Real.sqrt a.toReal - Real.sqrt ra| * (Real.sqrt a.toReal + Real.sqrt ra) :=
          mul_le_mul_of_nonneg_left hge (abs_nonneg _)
      _ = |a.toReal - ra| := key
      _ ≤ ea := ha.2
  have he' := rnd32 (fl := (Float32.sqrt a).toReal) (x := Real.sqrt a.toReal)
    (by rw [abs_of_nonneg (Real.sqrt_nonneg _)]; exact he)
  have := round_approx u32_pos.le he' hx
  rw [abs_of_nonneg (Real.sqrt_nonneg _), u32_eq] at this
  have := η32_small
  have : 1 / 16777216 * (Real.sqrt ra + ea / s0) ≤ 1 / 16777216 * (Rs + ea / s0) := by linarith
  linarith

/-! ## Exact operations -/

/-- A rounded operation whose exact result is the value of a finite float returns that value. -/
theorem Float32.add_exact {a b f : Float32} (ha : a.IsFinite) (hb : b.IsFinite) (hf : f.IsFinite)
    (h : a.toReal + b.toReal = f.toReal) : (a + b).IsFinite ∧ (a + b).toReal = f.toReal := by
  have hm : |a.toReal + b.toReal| ≤ maxFinite32 := h ▸ Float32.abs_toReal_le_maxFinite f
  obtain ⟨b1, b2⟩ := Float32.add_bracket ha hb hm hf
  exact ⟨(Float32.add_err_all ha hb hm).1, le_antisymm (b2 h.le) (b1 h.symm.le)⟩

theorem Float32.sub_exact {a b f : Float32} (ha : a.IsFinite) (hb : b.IsFinite) (hf : f.IsFinite)
    (h : a.toReal - b.toReal = f.toReal) : (a - b).IsFinite ∧ (a - b).toReal = f.toReal := by
  have hm : |a.toReal - b.toReal| ≤ maxFinite32 := h ▸ Float32.abs_toReal_le_maxFinite f
  obtain ⟨b1, b2⟩ := Float32.sub_bracket ha hb hm hf
  exact ⟨(Float32.sub_err_all ha hb hm).1, le_antisymm (b2 h.le) (b1 h.symm.le)⟩

theorem Float32.mul_exact {a b f : Float32} (ha : a.IsFinite) (hb : b.IsFinite) (hf : f.IsFinite)
    (h : a.toReal * b.toReal = f.toReal) : (a * b).IsFinite ∧ (a * b).toReal = f.toReal := by
  have hm : |a.toReal * b.toReal| ≤ maxFinite32 := h ▸ Float32.abs_toReal_le_maxFinite f
  obtain ⟨b1, b2⟩ := Float32.mul_bracket ha hb hm hf
  exact ⟨(Float32.mul_err_all ha hb hm).1, le_antisymm (b2 h.le) (b1 h.symm.le)⟩

/-- `x + z = x`, `x - z = x` for `z = 0`; `x * z = 0`. -/
theorem Float32.add_zero_val {a z : Float32} (ha : a.IsFinite) (hz : z.IsFinite) (h0 : z.toReal = 0) :
    (a + z).IsFinite ∧ (a + z).toReal = a.toReal :=
  Float32.add_exact ha hz ha (by rw [h0, add_zero])

theorem Float32.sub_zero_val {a z : Float32} (ha : a.IsFinite) (hz : z.IsFinite) (h0 : z.toReal = 0) :
    (a - z).IsFinite ∧ (a - z).toReal = a.toReal :=
  Float32.sub_exact ha hz ha (by rw [h0, sub_zero])

theorem Float32.mul_zero_val {a z : Float32} (ha : a.IsFinite) (hz : z.IsFinite) (h0 : z.toReal = 0) :
    (a * z).IsFinite ∧ (a * z).toReal = 0 := by
  have := Float32.mul_exact ha hz hz (by rw [h0, mul_zero])
  rwa [h0] at this

/-! ## Bounded approximations: `A32` with a magnitude bound on the exact value -/

/-- `x` is finite, within `e` of `r`, and `|r| ≤ R`. -/
def B32 (x : Float32) (r e R : ℝ) : Prop := A32 x r e ∧ |r| ≤ R

theorem B32.mono {x : Float32} {r e R e' R' : ℝ} (h : B32 x r e R) (he : e ≤ e') (hR : R ≤ R') :
    B32 x r e' R' := ⟨h.1.mono he, h.2.trans hR⟩

theorem B32.congr {x : Float32} {r r' e R : ℝ} (h : B32 x r e R) (hr : r = r') : B32 x r' e R :=
  hr ▸ h

theorem B32.of_exact {x : Float32} (h : x.IsFinite) {R : ℝ} (hR : |x.toReal| ≤ R) :
    B32 x x.toReal 0 R := ⟨A32.of_exact h, hR⟩

theorem B32.e_nonneg {x : Float32} {r e R : ℝ} (h : B32 x r e R) : 0 ≤ e :=
  (abs_nonneg _).trans h.1.2

theorem B32.neg {x : Float32} {r e R : ℝ} (h : B32 x r e R) : B32 (-x) (-r) e R :=
  ⟨⟨(Float32.isFinite_neg x).2 h.1.1, by
    rw [Float32.toReal_neg, show -x.toReal - -r = -(x.toReal - r) by ring, abs_neg]; exact h.1.2⟩,
    by rw [abs_neg]; exact h.2⟩

theorem B32.mul {a b : Float32} {ra rb ea eb Ra Rb e R : ℝ} (ha : B32 a ra ea Ra)
    (hb : B32 b rb eb Rb) (hcap : Ra * Rb + (Ra * eb + Rb * ea + ea * eb) ≤ capF)
    (hc : Ra * eb + Rb * ea + ea * eb + 1 / 16777216 * (Ra * Rb + (Ra * eb + Rb * ea + ea * eb)) +
      1 / 10 ^ 40 ≤ e) (hR : Ra * Rb ≤ R) : B32 (a * b) (ra * rb) e R := by
  have hRa : 0 ≤ Ra := (abs_nonneg _).trans ha.2
  have hRb : 0 ≤ Rb := (abs_nonneg _).trans hb.2
  refine ⟨A32.mul_c ha.1 hb.1 ha.2 hb.2 ha.e_nonneg hb.e_nonneg hcap hc, ?_⟩
  rw [abs_mul]; exact (mul_le_mul ha.2 hb.2 (abs_nonneg _) hRa).trans hR

theorem B32.add {a b : Float32} {ra rb ea eb Ra Rb e R : ℝ} (ha : B32 a ra ea Ra)
    (hb : B32 b rb eb Rb) (hR : Ra + Rb ≤ R) (hcap : R + ea + eb ≤ capF)
    (hc : ea + eb + 1 / 16777216 * (R + ea + eb) + 1 / 10 ^ 40 ≤ e) :
    B32 (a + b) (ra + rb) e R := by
  have h : |ra + rb| ≤ R := (abs_add_le _ _).trans (by linarith [ha.2, hb.2])
  exact ⟨A32.add_c ha.1 hb.1 h hcap hc, h⟩

theorem B32.sub {a b : Float32} {ra rb ea eb Ra Rb e R : ℝ} (ha : B32 a ra ea Ra)
    (hb : B32 b rb eb Rb) (hR : Ra + Rb ≤ R) (hcap : R + ea + eb ≤ capF)
    (hc : ea + eb + 1 / 16777216 * (R + ea + eb) + 1 / 10 ^ 40 ≤ e) :
    B32 (a - b) (ra - rb) e R := by
  have h : |ra - rb| ≤ R := (abs_sub _ _).trans (by linarith [ha.2, hb.2])
  exact ⟨A32.sub_c ha.1 hb.1 h hcap hc, h⟩

/-- Division by an exact value bounded away from `0` by `mlo`. -/
theorem B32.div {a b : Float32} {ra rb ea eb Ra Rb mlo e R : ℝ} (ha : B32 a ra ea Ra)
    (hb : B32 b rb eb Rb) (hlo : mlo ≤ |rb|) (hm : 0 < mlo - eb)
    (hR : Ra / mlo ≤ R)
    (hcap : R + (ea / (mlo - eb) + Ra * eb / ((mlo - eb) * mlo)) ≤ capF)
    (hc : ea / (mlo - eb) + Ra * eb / ((mlo - eb) * mlo) +
      1 / 16777216 * (R + (ea / (mlo - eb) + Ra * eb / ((mlo - eb) * mlo))) + 1 / 10 ^ 40 ≤ e) :
    B32 (a / b) (ra / rb) e R := by
  have heb := hb.e_nonneg
  have hmlo : 0 < mlo := by linarith
  have hQ : |ra / rb| ≤ R := by
    rw [abs_div]
    calc |ra| / |rb| ≤ Ra / mlo := div_le_div₀ ((abs_nonneg _).trans ha.2) ha.2 hmlo hlo
      _ ≤ R := hR
  refine ⟨A32.div_c ha.1 hb.1 ha.2 hm (by linarith) heb hQ (by
    rw [show mlo - eb + eb = mlo by ring]; exact hcap) (by rw [show mlo - eb + eb = mlo by ring]; exact hc), hQ⟩

/-- `√` of a value bounded below by `r0 > 0`. -/
theorem B32.sqrt {a : Float32} {ra ea Ra r0 s0 e R : ℝ} (ha : B32 a ra ea Ra) (h0 : 0 ≤ a.toReal)
    (hr0 : r0 ≤ ra) (hs0 : 0 < s0) (hs0' : s0 ≤ Real.sqrt r0) (hR : Real.sqrt Ra ≤ R)
    (hcap : Ra + ea ≤ capF)
    (hc : ea / s0 + 1 / 16777216 * (R + ea / s0) + 1 / 10 ^ 40 ≤ e) :
    B32 (Float32.sqrt a) (Real.sqrt ra) e R := by
  have hRs : Real.sqrt ra ≤ R := (Real.sqrt_le_sqrt (le_abs_self ra |>.trans ha.2)).trans hR
  exact ⟨A32.sqrt_c ha.1 h0 hr0 hs0 hs0' hRs (by linarith [ha.2]) hc,
    by rw [abs_of_nonneg (Real.sqrt_nonneg _)]; exact hRs⟩

/-! ## Relative errors -/

/-- The `float` `x` is finite and within relative error `k u` of the real `r`. -/
def R32 (x : Float32) (r k : ℝ) : Prop := x.IsFinite ∧ |x.toReal - r| ≤ k * (1 / 16777216) * |r|

theorem R32.to_A32 {x : Float32} {r k : ℝ} (h : R32 x r k) : A32 x r (k * (1 / 16777216) * |r|) := h

theorem R32.of_exact {x : Float32} (h : x.IsFinite) {k : ℝ} (hk : 0 ≤ k) : R32 x x.toReal k :=
  ⟨h, by rw [sub_self, abs_zero]; positivity⟩

/-- Two floats with the same value approximate alike (`A32`). -/
theorem A32.congr_x {x y : Float32} {r e : ℝ} (h : A32 x r e) (hy : y.IsFinite)
    (hxy : y.toReal = x.toReal) : A32 y r e := ⟨hy, by rw [hxy]; exact h.2⟩

/-- Two floats with the same value approximate alike. -/
theorem R32.congr_x {x y : Float32} {r k : ℝ} (h : R32 x r k) (hy : y.IsFinite)
    (hxy : y.toReal = x.toReal) : R32 y r k := ⟨hy, by rw [hxy]; exact h.2⟩

theorem R32.mono {x : Float32} {r k k' : ℝ} (h : R32 x r k) (hk : k ≤ k') : R32 x r k' :=
  ⟨h.1, h.2.trans (by gcongr)⟩

theorem R32.k_nonneg {x : Float32} {r k : ℝ} (h : R32 x r k) (hr : r ≠ 0) : 0 ≤ k := by
  have h1 := h.2
  have h2 : 0 < |r| := abs_pos.2 hr
  by_contra hk
  have hk := not_le.1 hk
  have : k * (1 / 16777216) * |r| < 0 := by
    have : k * (1 / 16777216) < 0 := by linarith
    exact mul_neg_of_neg_of_pos this h2
  linarith [abs_nonneg (x.toReal - r)]

/-- The smallest magnitude the relative calculus handles (`η32` is negligible against it). -/
theorem eta32_rel {r : ℝ} (hr : (1 / 2 ^ 60 : ℝ) ≤ |r|) : η32 ≤ 1 / 2 ^ 60 * (1 / 16777216) * |r| := by
  have h1 : η32 = 1 / 2 ^ 149 := by rw [η32_eq]; norm_num
  have h2 : (1 / 2 ^ 149 : ℝ) ≤ 1 / 2 ^ 60 * (1 / 16777216) * (1 / 2 ^ 60) := by norm_num
  have h3 : 1 / 2 ^ 60 * (1 / 16777216) * (1 / 2 ^ 60) ≤ 1 / 2 ^ 60 * (1 / 16777216) * |r| := by
    gcongr
  linarith

theorem R32.mul {a b : Float32} {ra rb ka kb k : ℝ} (ha : R32 a ra ka) (hb : R32 b rb kb)
    (hka : 0 ≤ ka) (hkb : 0 ≤ kb) (hka' : ka ≤ 2 ^ 20) (hkb' : kb ≤ 2 ^ 20)
    (hlo : (1 / 2 ^ 60 : ℝ) ≤ |ra * rb|) (hhi : |ra * rb| ≤ 2 ^ 90)
    (hk : ka + kb + 1 + (ka * kb + ka + kb + ka * kb / 16777216) / 16777216 + 1 / 2 ^ 60 ≤ k) :
    R32 (a * b) (ra * rb) k := by
  have hx := mul_approx ha.2 hb.2
  have hR : |ra| * (kb * (1 / 16777216) * |rb|) + |rb| * (ka * (1 / 16777216) * |ra|) +
      ka * (1 / 16777216) * |ra| * (kb * (1 / 16777216) * |rb|) =
      (ka + kb + ka * kb / 16777216) / 16777216 * |ra * rb| := by rw [abs_mul]; ring
  rw [hR] at hx
  have hc1 : (ka + kb + ka * kb / 16777216) / 16777216 ≤ 1 := by
    rw [div_le_one (by norm_num)]
    have : ka * kb ≤ 2 ^ 20 * 2 ^ 20 := mul_le_mul hka' hkb' hkb (by norm_num)
    have : ka * kb / 16777216 ≤ 2 ^ 20 * 2 ^ 20 / 16777216 := by gcongr
    norm_num at *; linarith
  have hab : |a.toReal * b.toReal| ≤ 2 * |ra * rb| := by
    have := abs_sub_abs_le_abs_sub (a.toReal * b.toReal) (ra * rb)
    nlinarith [abs_nonneg (ra * rb)]
  have hm : |a.toReal * b.toReal| ≤ maxFinite32 := by
    have : (2 : ℝ) * 2 ^ 90 ≤ capF := by norm_num [capF]
    linarith [capF_le_max32]
  obtain ⟨hf, he⟩ := Float32.mul_err_all ha.1 hb.1 hm
  refine ⟨hf, ?_⟩
  have he' := rnd32 he
  rw [u32_eq] at he'
  have hη := eta32_rel hlo
  have h1 : |a.toReal * b.toReal| ≤ |ra * rb| + (ka + kb + ka * kb / 16777216) / 16777216 * |ra * rb| := by
    have := abs_sub_abs_le_abs_sub (a.toReal * b.toReal) (ra * rb); linarith
  have := abs_sub_le (a * b).toReal (a.toReal * b.toReal) (ra * rb)
  have hr0 : 0 ≤ |ra * rb| := abs_nonneg _
  have : k * (1 / 16777216) * |ra * rb| ≥
      (ka + kb + 1 + (ka * kb + ka + kb + ka * kb / 16777216) / 16777216 + 1 / 2 ^ 60) *
        (1 / 16777216) * |ra * rb| := by gcongr
  nlinarith

theorem R32.div {a b : Float32} {ra rb ka kb k : ℝ} (ha : R32 a ra ka) (hb : R32 b rb kb)
    (hka : 0 ≤ ka) (hkb : 0 ≤ kb) (hka' : ka ≤ 2 ^ 20) (hkb' : kb ≤ 2 ^ 20) (hrb : rb ≠ 0)
    (hlo : (1 / 2 ^ 60 : ℝ) ≤ |ra / rb|) (hhi : |ra / rb| ≤ 2 ^ 90)
    (hk : (ka + kb) * (1 + 2 * kb / 16777216) * (1 + 1 / 16777216) + 1 + 1 / 2 ^ 60 ≤ k) :
    R32 (a / b) (ra / rb) k := by
  have hkbu : kb * (1 / 16777216) ≤ 1 / 16 := by
    have : kb * (1 / 16777216) ≤ 2 ^ 20 * (1 / 16777216) := by gcongr
    norm_num at this ⊢; linarith
  have hkku : (ka + kb) * (1 / 16777216) ≤ 1 / 8 := by
    have : (ka + kb) * (1 / 16777216) ≤ (2 ^ 20 + 2 ^ 20) * (1 / 16777216) := by gcongr
    norm_num at this ⊢; linarith
  have hk' : (ka + kb) * (1 + 2 * kb * (1 / 16777216)) * (1 + 1 / 16777216) + 1 + 1 / 2 ^ 60 ≤ k := by
    have : 2 * kb / 16777216 = 2 * kb * (1 / 16777216) := by ring
    rw [this] at hk; exact hk
  have hη := eta32_rel hlo
  have hdiv := Float32.div_err_all (a := a) (b := b)
  have ha1 := ha.1
  have hb1 := hb.1
  have ha2 : |a.toReal - ra| ≤ ka * (1 / 16777216) * |ra| := ha.2
  have hb2 : |b.toReal - rb| ≤ kb * (1 / 16777216) * |rb| := hb.2
  clear hk ha hb
  show (a / b).IsFinite ∧ |(a / b).toReal - ra / rb| ≤ k * (1 / 16777216) * |ra / rb|
  generalize hu : (1 / 16777216 : ℝ) = u at *
  have hu0 : 0 ≤ u := by rw [← hu]; norm_num
  have hrb0 : 0 < |rb| := abs_pos.2 hrb
  set m := |rb| * (1 - kb * u) with hm
  have hm0 : 0 < m := mul_pos hrb0 (by linarith)
  have hmb : m + kb * u * |rb| ≤ |rb| := by rw [hm]; nlinarith
  set q := |ra / rb| with hq
  have hq0 : 0 ≤ q := abs_nonneg _
  have hqr : |ra| = q * |rb| := by rw [hq, abs_div, div_mul_cancel₀ _ hrb0.ne']
  have hx := div_approx ha2 hb2 hm0 hmb
  have hE : (|rb| * (ka * u * |ra|) + |ra| * (kb * u * |rb|)) / (m * |rb|) =
      (ka + kb) * u * q / (1 - kb * u) := by
    rw [hm, hqr]
    have : 1 - kb * u ≠ 0 := by linarith
    field_simp
  rw [hE] at hx
  set E1 := (ka + kb) * u * q * (1 + 2 * kb * u) with hE1
  have hden : (ka + kb) * u * q / (1 - kb * u) ≤ E1 := by
    rw [div_le_iff₀ (by linarith), hE1]
    have h0 : 0 ≤ (ka + kb) * u * q := by positivity
    have : 0 ≤ (ka + kb) * u * q * (kb * u * (1 - 2 * kb * u)) := by
      apply mul_nonneg h0; apply mul_nonneg (by positivity); linarith
    nlinarith
  have hx' := hx.trans hden
  have hE1q : E1 ≤ q / 4 := by
    have : 1 + 2 * kb * u ≤ 9 / 8 := by linarith
    have h1 : (ka + kb) * u * q ≤ 1 / 8 * q := mul_le_mul_of_nonneg_right hkku hq0
    have h2 : 0 ≤ (ka + kb) * u * q := by positivity
    nlinarith
  have hab : |a.toReal / b.toReal| ≤ 2 * q := by
    have := abs_sub_abs_le_abs_sub (a.toReal / b.toReal) (ra / rb); linarith
  have hm' : |a.toReal / b.toReal| ≤ maxFinite32 := by
    have : (2 : ℝ) * 2 ^ 90 ≤ capF := by norm_num [capF]
    linarith [capF_le_max32]
  have hb0 : b.toReal ≠ 0 := by
    intro h0
    have := hb2
    rw [h0, zero_sub, abs_neg] at this
    nlinarith
  obtain ⟨hf, he⟩ := hdiv ha1 hb1 hb0 hm'
  refine ⟨hf, ?_⟩
  have he' := rnd32 he
  rw [u32_eq, hu] at he'
  have h1 : |a.toReal / b.toReal| ≤ q + E1 := by
    have := abs_sub_abs_le_abs_sub (a.toReal / b.toReal) (ra / rb); linarith
  have := abs_sub_le (a / b).toReal (a.toReal / b.toReal) (ra / rb)
  have hkq : k * u * q ≥ ((ka + kb) * (1 + 2 * kb * u) * (1 + u) + 1 + 1 / 2 ^ 60) * u * q := by
    gcongr
  have hE1' : E1 * (1 + u) = (ka + kb) * (1 + 2 * kb * u) * (1 + u) * u * q := by
    rw [hE1]; ring
  have : u * |a.toReal / b.toReal| ≤ u * (q + E1) := mul_le_mul_of_nonneg_left h1 hu0
  nlinarith

theorem R32.add_pos {a b : Float32} {ra rb K k : ℝ} (ha : R32 a ra K) (hb : R32 b rb K)
    (hra : 0 ≤ ra) (hrb : 0 ≤ rb) (hK' : K ≤ 2 ^ 20)
    (hlo : (1 / 2 ^ 60 : ℝ) ≤ ra + rb) (hhi : ra + rb ≤ 2 ^ 90)
    (hk : K * (1 + 1 / 16777216) + 1 + 1 / 2 ^ 60 ≤ k) : R32 (a + b) (ra + rb) k := by
  have hs : 0 ≤ ra + rb := by linarith
  have hx : |(a.toReal + b.toReal) - (ra + rb)| ≤ K * (1 / 16777216) * (ra + rb) := by
    have := abs_add_le (a.toReal - ra) (b.toReal - rb)
    rw [show a.toReal - ra + (b.toReal - rb) = (a.toReal + b.toReal) - (ra + rb) by ring] at this
    have h1 := ha.2; have h2 := hb.2
    rw [abs_of_nonneg hra] at h1; rw [abs_of_nonneg hrb] at h2
    linarith
  have hKu : K * (1 / 16777216) ≤ 1 := by
    have : K * (1 / 16777216) ≤ 2 ^ 20 * (1 / 16777216) := by gcongr
    norm_num at this ⊢; linarith
  have hab : |a.toReal + b.toReal| ≤ 2 * (ra + rb) := by
    have := abs_sub_abs_le_abs_sub (a.toReal + b.toReal) (ra + rb)
    rw [abs_of_nonneg hs] at this
    nlinarith
  have hm : |a.toReal + b.toReal| ≤ maxFinite32 := by
    have : (2 : ℝ) * 2 ^ 90 ≤ capF := by norm_num [capF]
    linarith [capF_le_max32]
  obtain ⟨hf, he⟩ := Float32.add_err_all ha.1 hb.1 hm
  refine ⟨hf, ?_⟩
  rw [abs_of_nonneg hs]
  have hη := eta32_rel (r := ra + rb) (by rw [abs_of_nonneg hs]; exact hlo)
  rw [abs_of_nonneg hs] at hη
  have h1 : |a.toReal + b.toReal| ≤ (ra + rb) + K * (1 / 16777216) * (ra + rb) := by
    have := abs_sub_abs_le_abs_sub (a.toReal + b.toReal) (ra + rb)
    rw [abs_of_nonneg hs] at this; linarith
  have := abs_sub_le (a + b).toReal (a.toReal + b.toReal) (ra + rb)
  have h24 : (2 : ℝ) ^ (-24 : ℤ) = 1 / 16777216 := by norm_num
  rw [h24] at he
  have : k * (1 / 16777216) * (ra + rb) ≥
      (K * (1 + 1 / 16777216) + 1 + 1 / 2 ^ 60) * (1 / 16777216) * (ra + rb) := by gcongr
  nlinarith

theorem R32.sqrt {a : Float32} {ra ka k : ℝ} (ha : R32 a ra ka) (hka : 0 ≤ ka) (hka' : ka ≤ 2 ^ 20)
    (hlo : (1 / 2 ^ 120 : ℝ) ≤ ra) (hhi : ra ≤ 2 ^ 90)
    (hk : ka + 1 + ka / 16777216 + 1 / 2 ^ 60 ≤ k) : R32 (Float32.sqrt a) (Real.sqrt ra) k := by
  have hra : 0 < ra := lt_of_lt_of_le (by norm_num) hlo
  have hKu : ka * (1 / 16777216) ≤ 1 / 16 := by
    have : ka * (1 / 16777216) ≤ 2 ^ 20 * (1 / 16777216) := by gcongr
    norm_num at this ⊢; linarith
  have h2 := ha.2
  rw [abs_of_pos hra] at h2
  have ha0 : 0 ≤ a.toReal := by
    have := (abs_le.1 h2).1; nlinarith
  have hm : a.toReal ≤ maxFinite32 := by
    have := (abs_le.1 h2).2
    have : (2 : ℝ) * 2 ^ 90 ≤ capF := by norm_num [capF]
    nlinarith [capF_le_max32]
  obtain ⟨hf, he⟩ := Float32.sqrt_err_all ha.1 ha0 hm
  refine ⟨hf, ?_⟩
  have hsr : 0 < Real.sqrt ra := Real.sqrt_pos.2 hra
  rw [abs_of_pos hsr]
  -- `|√a - √r| ≤ k_a u √r`
  have hx : |Real.sqrt a.toReal - Real.sqrt ra| ≤ ka * (1 / 16777216) * Real.sqrt ra := by
    have key : |Real.sqrt a.toReal - Real.sqrt ra| * (Real.sqrt a.toReal + Real.sqrt ra) =
        |a.toReal - ra| := by
      rw [← abs_of_pos (by positivity : 0 < Real.sqrt a.toReal + Real.sqrt ra), ← abs_mul]
      congr 1
      have := Real.sq_sqrt ha0; have := Real.sq_sqrt hra.le; nlinarith
    have hge : Real.sqrt ra ≤ Real.sqrt a.toReal + Real.sqrt ra := by
      linarith [Real.sqrt_nonneg a.toReal]
    have hsq : ra = Real.sqrt ra * Real.sqrt ra := (Real.mul_self_sqrt hra.le).symm
    by_contra hc
    have hc := not_le.1 hc
    have : ka * (1 / 16777216) * Real.sqrt ra * Real.sqrt ra <
        |Real.sqrt a.toReal - Real.sqrt ra| * (Real.sqrt a.toReal + Real.sqrt ra) :=
      calc ka * (1 / 16777216) * Real.sqrt ra * Real.sqrt ra
          < |Real.sqrt a.toReal - Real.sqrt ra| * Real.sqrt ra := by gcongr
        _ ≤ _ := mul_le_mul_of_nonneg_left hge (abs_nonneg _)
    rw [key] at this
    nlinarith
  have hη : η32 ≤ 1 / 2 ^ 60 * (1 / 16777216) * Real.sqrt ra := by
    have h1 : (1 / 2 ^ 60 : ℝ) ≤ Real.sqrt ra := by
      rw [show (1 / 2 ^ 60 : ℝ) = Real.sqrt (1 / 2 ^ 120) by
        rw [show (1 / 2 ^ 120 : ℝ) = (1 / 2 ^ 60) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
      exact Real.sqrt_le_sqrt hlo
    have := eta32_rel (r := Real.sqrt ra) (by rw [abs_of_pos hsr]; exact h1)
    rwa [abs_of_pos hsr] at this
  have he' := rnd32 (fl := (Float32.sqrt a).toReal) (x := Real.sqrt a.toReal)
    (by rw [abs_of_nonneg (Real.sqrt_nonneg _)]; exact he)
  rw [u32_eq, abs_of_nonneg (Real.sqrt_nonneg _)] at he'
  have h3 : Real.sqrt a.toReal ≤ Real.sqrt ra + ka * (1 / 16777216) * Real.sqrt ra := by
    have := (abs_le.1 hx).2; linarith
  have := abs_sub_le (Float32.sqrt a).toReal (Real.sqrt a.toReal) (Real.sqrt ra)
  have : k * (1 / 16777216) * Real.sqrt ra ≥
      (ka + 1 + ka / 16777216 + 1 / 2 ^ 60) * (1 / 16777216) * Real.sqrt ra := by gcongr
  nlinarith

/-- `powf a b` for `0 < b ≤ 1` (`LibmSpec.powf`). -/
theorem R32.pow {a b : Float32} {ra ka k : ℝ} (hL : LibmSpec) (ha : R32 a ra ka) (hb : b.IsFinite)
    (hb0 : 0 ≤ b.toReal) (hb1 : b.toReal ≤ 1) (hka : 0 ≤ ka) (hka' : ka ≤ 2 ^ 20) (hra : 0 < ra)
    (hhi : ra ≤ 2 ^ 50) (hk : ka + 4 + 4 * ka / 16777216 ≤ k) :
    R32 (Float32.pow a b) (ra ^ b.toReal) k := by
  have hKu : ka * (1 / 16777216) ≤ 1 / 16 := by
    have : ka * (1 / 16777216) ≤ 2 ^ 20 * (1 / 16777216) := by gcongr
    norm_num at this ⊢; linarith
  have h2 := ha.2
  rw [abs_of_pos hra] at h2
  obtain ⟨hlo2, hhi2⟩ := abs_le.1 h2
  have ha0 : 0 < a.toReal := by nlinarith
  -- `a = ra (1 + α)`
  set α := a.toReal / ra - 1 with hα
  have haα : a.toReal = ra * (1 + α) := by rw [hα]; field_simp; ring
  have hαb : |α| ≤ ka * (1 / 16777216) := by
    rw [hα, abs_le]; constructor
    · rw [le_sub_iff_add_le, le_div_iff₀ hra]; nlinarith
    · rw [sub_le_iff_le_add, div_le_iff₀ hra]; nlinarith
  have hα1 : -1 ≤ α := by linarith [neg_abs_le α]
  have hpow : a.toReal ^ b.toReal = ra ^ b.toReal * (1 + α) ^ b.toReal := by
    rw [haα, Real.mul_rpow hra.le (by linarith)]
  have hrb : 0 < ra ^ b.toReal := Real.rpow_pos_of_pos hra _
  -- `|(1 + α)^b - 1| ≤ |α|`
  have hup : (1 + α) ^ b.toReal ≤ 1 + |α| := by
    have := rpow_one_add_le_one_add_mul_self hα1 hb0 hb1
    have : b.toReal * α ≤ |α| := by
      rcases le_total 0 α with h | h
      · rw [abs_of_nonneg h]; nlinarith
      · nlinarith [abs_nonneg α]
    linarith
  have hlow : 1 - |α| ≤ (1 + α) ^ b.toReal := by
    rcases le_total 0 α with h | h
    · have := Real.one_le_rpow (by linarith : (1 : ℝ) ≤ 1 + α) hb0
      linarith [abs_nonneg α]
    · have h1 : 0 ≤ 1 + α := by linarith
      have h2' : 1 + α ≤ 1 := by linarith
      have := Real.rpow_le_rpow_of_exponent_ge' h1 h2' hb0 hb1
      rw [Real.rpow_one] at this
      rw [abs_of_nonpos h]; linarith
  have hd : |a.toReal ^ b.toReal - ra ^ b.toReal| ≤ ka * (1 / 16777216) * ra ^ b.toReal := by
    rw [hpow, abs_le]; constructor <;> nlinarith
  have hcap : a.toReal ^ b.toReal ≤ 2 ^ (100 : ℤ) := by
    have h1 : a.toReal ≤ 2 * 2 ^ 50 := by nlinarith
    have h3 : a.toReal ^ b.toReal ≤ max 1 a.toReal := by
      rcases le_total a.toReal 1 with h | h
      · exact (Real.rpow_le_one ha0.le h hb0).trans (le_max_left _ _)
      · exact (Real.rpow_le_rpow_of_exponent_le h hb1).trans (by rw [Real.rpow_one]; exact le_max_right _ _)
    have : max 1 a.toReal ≤ 2 ^ (100 : ℤ) := by
      apply max_le (by norm_num); have : (2 : ℝ) * 2 ^ 50 ≤ 2 ^ (100 : ℤ) := by norm_num
      linarith
    linarith
  obtain ⟨hf, he⟩ := hL.powf a b ha.1 hb ha0 hcap
  refine ⟨hf, ?_⟩
  rw [abs_of_pos hrb]
  have h22 : (2 : ℝ) ^ (-22 : ℤ) = 4 * (1 / 16777216) := by norm_num
  rw [h22] at he
  have h3 : a.toReal ^ b.toReal ≤ ra ^ b.toReal + ka * (1 / 16777216) * ra ^ b.toReal := by
    have := (abs_le.1 hd).2; linarith
  have := abs_sub_le (Float32.pow a b).toReal (a.toReal ^ b.toReal) (ra ^ b.toReal)
  have : k * (1 / 16777216) * ra ^ b.toReal ≥
      (ka + 4 + 4 * ka / 16777216) * (1 / 16777216) * ra ^ b.toReal := by gcongr
  nlinarith

/-- The `float` of the `double` `π` (`Float.toFloat32 3.1415926535897931`): within `2u` of `π`. -/
theorem R32.pi_f (hL : LibmSpec) : R32 (Float.toFloat32 3.1415926535897931) Real.pi 2 := by
  have hd : (3.1415926535897931 : Float).IsFinite := f64_isFinite_3p1415926535897931
  have hdv := f64_toReal_3p1415926535897931
  have hm : |(3.1415926535897931 : Float).toReal| ≤ maxFinite32 := by
    rw [hdv]; have : (884279719003555 / 281474976710656 : ℝ) ≤ capF := by norm_num [capF]
    rw [abs_of_pos (by norm_num)]; linarith [capF_le_max32]
  obtain ⟨hf, he⟩ := hL.f64ToF32 _ hd hm
  refine ⟨hf, ?_⟩
  rw [hdv] at he
  have p1 := Real.pi_gt_d20
  have p2 := Real.pi_lt_d20
  rw [abs_of_pos Real.pi_pos]
  have := abs_sub_le (Float.toFloat32 3.1415926535897931).toReal (884279719003555 / 281474976710656) Real.pi
  have h3 : |(884279719003555 / 281474976710656 : ℝ) - Real.pi| ≤ 1 / 10 ^ 15 := by
    rw [abs_le]; constructor <;> norm_num at p1 p2 ⊢ <;> linarith
  rw [abs_of_pos (by norm_num : (0 : ℝ) < 884279719003555 / 281474976710656)] at he
  norm_num at he ⊢
  linarith

end

end Contracts.Mission
