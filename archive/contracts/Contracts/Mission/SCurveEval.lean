import Contracts.Mission.FloatCalc
import Contracts.Mission.SCurveReal

/-!
# The `float` evaluation of an S-curve segment

`SCurve::calc_javp_for_segment_const_jerk`, `…_incr_jerk`, `…_decr_jerk` (`AP_Math/SCurve.cpp`)
evaluate the position of a segment from its start node at local time `τ`. In `float`, with the
libm accuracy of `LibmSpec` for `sinf`/`cosf` and `π` rounded to `float`, the position is within a
small absolute error of the real closed form (`SC.cP`, `SC.iP`, `SC.dP`) at the inputs' values.
-/

namespace Contracts.Mission

open Float.Model UnpackedFloat AC_WPNav_lib

noncomputable section

/-! ## Helpers -/

theorem sce_max : (2 : ℝ) ^ 91 ≤ maxFinite32 := by
  have h := capF_le_max32
  have : (2 : ℝ) ^ 91 ≤ capF := by norm_num [capF]
  linarith

/-- `x` is finite, within `k u M + c` of `r`, and `|r| ≤ M`: a relative error against a magnitude
`M` with an absolute floor `c` for underflow. -/
def SCE32 (x : Float32) (r M k c : ℝ) : Prop :=
  x.IsFinite ∧ |x.toReal - r| ≤ k * (1 / 16777216) * M + c ∧ |r| ≤ M

theorem SCE32.lit {x : Float32} {v M : ℝ} (h : x.IsFinite) (hx : x.toReal = v) (hM : |v| ≤ M) :
    SCE32 x v M 0 0 := ⟨h, by rw [hx]; simp, hM⟩

theorem SCE32.M_nonneg {x : Float32} {r M k c : ℝ} (h : SCE32 x r M k c) : 0 ≤ M :=
  (abs_nonneg _).trans h.2.2

theorem SCE32.add {a b : Float32} {ra rb Ma Mb ka kb ca cb K k c : ℝ}
    (ha : SCE32 a ra Ma ka ca) (hb : SCE32 b rb Mb kb cb)
    (hKa : ka ≤ K) (hKb : kb ≤ K) (hK : K ≤ 2 ^ 10) (hca1 : ca ≤ 1) (hcb1 : cb ≤ 1) (hM : Ma + Mb ≤ 2 ^ 90)
    (hk : K + 1 + K / 16777216 ≤ k) (hc : (ca + cb) * (1 + 1 / 16777216) ≤ c) :
    SCE32 (a + b) (ra + rb) (Ma + Mb) k c := by
  have hMa := ha.M_nonneg
  have hMb := hb.M_nonneg
  obtain ⟨fa, ea, Ra⟩ := ha
  obtain ⟨fb, eb, Rb⟩ := hb
  have h1 : ka * Ma ≤ K * Ma := mul_le_mul_of_nonneg_right hKa hMa
  have h2 : kb * Mb ≤ K * Mb := mul_le_mul_of_nonneg_right hKb hMb
  have hx : |(a.toReal + b.toReal) - (ra + rb)| ≤ K * (1 / 16777216) * (Ma + Mb) + (ca + cb) := by
    have := abs_add_le (a.toReal - ra) (b.toReal - rb)
    rw [show a.toReal - ra + (b.toReal - rb) = (a.toReal + b.toReal) - (ra + rb) by ring] at this
    linarith
  have hxa : |a.toReal + b.toReal| ≤ (Ma + Mb) + (K * (1 / 16777216) * (Ma + Mb) + (ca + cb)) := by
    have := abs_sub_abs_le_abs_sub (a.toReal + b.toReal) (ra + rb)
    have := abs_add_le ra rb
    linarith
  have hKM : K * (Ma + Mb) ≤ 2 ^ 10 * 2 ^ 90 :=
    mul_le_mul hK hM (by positivity) (by norm_num)
  have hm : |a.toReal + b.toReal| ≤ maxFinite32 := by
    have := sce_max; nlinarith
  obtain ⟨hf, he⟩ := Float32.add_err_all fa fb hm
  refine ⟨hf, ?_, (abs_add_le _ _).trans (add_le_add Ra Rb)⟩
  have h24 : (2 : ℝ) ^ (-24 : ℤ) = 1 / 16777216 := by norm_num
  rw [h24] at he
  have := abs_sub_le (a + b).toReal (a.toReal + b.toReal) (ra + rb)
  have hkM : (K + 1 + K / 16777216) * (1 / 16777216) * (Ma + Mb) ≤ k * (1 / 16777216) * (Ma + Mb) := by
    gcongr
  have := mul_le_mul_of_nonneg_left hxa (by norm_num : (0 : ℝ) ≤ 1 / 16777216)
  linarith

theorem SCE32.mul {a b : Float32} {ra rb Ma Mb ka kb ca cb da db k c : ℝ}
    (ha : SCE32 a ra Ma ka ca) (hb : SCE32 b rb Mb kb cb) (hka : 0 ≤ ka) (hkb : 0 ≤ kb)
    (hka1 : ka ≤ 2 ^ 10) (hkb1 : kb ≤ 2 ^ 10) (hca : 0 ≤ ca) (hcb : 0 ≤ cb) (hca1 : ca ≤ 1)
    (hcb1 : cb ≤ 1) (hda : Mb * ca ≤ da) (hdb : Ma * cb ≤ db) (hda1 : da ≤ 1) (hdb1 : db ≤ 1)
    (hM : Ma * Mb ≤ 2 ^ 90)
    (hk : (ka + kb + ka * kb / 16777216) * (1 + 1 / 16777216) + 1 ≤ k)
    (hc : (da * (1 + kb / 16777216) + db * (1 + ka / 16777216) + ca * cb) * (1 + 1 / 16777216) +
      1 / 2 ^ 150 ≤ c) :
    SCE32 (a * b) (ra * rb) (Ma * Mb) k c := by
  have hMa := ha.M_nonneg
  have hMb := hb.M_nonneg
  obtain ⟨fa, ea, Ra⟩ := ha
  obtain ⟨fb, eb, Rb⟩ := hb
  have hx := mul_approx (le_refl |a.toReal - ra|) (le_refl |b.toReal - rb|)
  have t1 : |ra| * |b.toReal - rb| ≤ Ma * (kb * (1 / 16777216) * Mb + cb) :=
    mul_le_mul Ra eb (abs_nonneg _) hMa
  have t2 : |rb| * |a.toReal - ra| ≤ Mb * (ka * (1 / 16777216) * Ma + ca) :=
    mul_le_mul Rb ea (abs_nonneg _) hMb
  have t3 : |a.toReal - ra| * |b.toReal - rb| ≤
      (ka * (1 / 16777216) * Ma + ca) * (kb * (1 / 16777216) * Mb + cb) :=
    mul_le_mul ea eb (abs_nonneg _) (by positivity)
  have t4 : ka * (Ma * cb) ≤ ka * db := mul_le_mul_of_nonneg_left hdb hka
  have t5 : kb * (Mb * ca) ≤ kb * da := mul_le_mul_of_nonneg_left hda hkb
  have hD : |a.toReal * b.toReal - ra * rb| ≤
      (ka + kb + ka * kb * (1 / 16777216)) * (1 / 16777216) * (Ma * Mb) +
        (da * (1 + kb * (1 / 16777216)) + db * (1 + ka * (1 / 16777216)) + ca * cb) := by
    linarith
  have hrr : |ra * rb| ≤ Ma * Mb := by
    rw [abs_mul]; exact mul_le_mul Ra Rb (abs_nonneg _) hMa
  have hxa : |a.toReal * b.toReal| ≤ Ma * Mb +
      ((ka + kb + ka * kb * (1 / 16777216)) * (1 / 16777216) * (Ma * Mb) +
        (da * (1 + kb * (1 / 16777216)) + db * (1 + ka * (1 / 16777216)) + ca * cb)) := by
    have := abs_sub_abs_le_abs_sub (a.toReal * b.toReal) (ra * rb)
    linarith
  have hkk : ka * kb ≤ 2 ^ 10 * 2 ^ 10 := mul_le_mul hka1 hkb1 hkb (by norm_num)
  have hK1 : ka + kb + ka * kb * (1 / 16777216) ≤ 2 ^ 12 := by linarith
  have hK2 : (ka + kb + ka * kb * (1 / 16777216)) * (Ma * Mb) ≤ 2 ^ 12 * 2 ^ 90 :=
    mul_le_mul hK1 hM (by positivity) (by norm_num)
  have hd1 : da * kb ≤ 1 * 2 ^ 10 := mul_le_mul hda1 hkb1 hkb (by norm_num)
  have hd2 : db * ka ≤ 1 * 2 ^ 10 := mul_le_mul hdb1 hka1 hka (by norm_num)
  have hd3 : ca * cb ≤ 1 * 1 := mul_le_mul hca1 hcb1 hcb (by norm_num)
  have hm : |a.toReal * b.toReal| ≤ maxFinite32 := by
    have := sce_max; linarith
  obtain ⟨hf, he⟩ := Float32.mul_err_all fa fb hm
  refine ⟨hf, ?_, hrr⟩
  have h24 : (2 : ℝ) ^ (-24 : ℤ) = 1 / 16777216 := by norm_num
  have h150 : (2 : ℝ) ^ (-150 : ℤ) = 1 / 2 ^ 150 := by norm_num
  rw [h24, h150] at he
  have := abs_sub_le (a * b).toReal (a.toReal * b.toReal) (ra * rb)
  have hkM : ((ka + kb + ka * kb / 16777216) * (1 + 1 / 16777216) + 1) * (1 / 16777216) * (Ma * Mb)
      ≤ k * (1 / 16777216) * (Ma * Mb) := by
    gcongr
  have := mul_le_mul_of_nonneg_left hxa (by norm_num : (0 : ℝ) ≤ 1 / 16777216)
  linarith

theorem sce_c6 : (1.0 : Float32) / (6.0 : Float32) = 0.166666672 := by decide +kernel
theorem sce_unpack_c6 : (0.166666672 : Float32).toModel.unpack = .finite .positive 11184811 (-26) (by decide) := by rfl
theorem sce_toReal_c6 : (0.166666672 : Float32).toReal = (11184811 / 67108864 : ℝ) := by
  rw [Float32.toReal, sce_unpack_c6]; simp [UnpackedFloat.toReal, Sign.apply]; norm_num
theorem sce_isFinite_c6 : (0.166666672 : Float32).IsFinite := by
  rw [Float32.isFinite_iff, sce_unpack_c6]; rfl

theorem sce_isPos {x : Float32} (hx : x.IsFinite) (h : 1 / 512 ≤ x.toReal) :
    is_positive_float x = true := by
  show decide (x ≥ (1.1920929e-7 : Float32)) = true
  rw [decide_eq_true_iff, ge_iff_le, Float32.le_iff_toReal_le f32_isFinite_1p1920929Em7 hx,
    f32_toReal_1p1920929Em7]
  linarith


macro "sce_side" : tactic => `(tactic| first | (norm_num; done) | linarith | nlinarith)

set_option maxHeartbeats 4000000 in
/-- **Constant jerk.** Error `16 u` relative to the sum of the magnitudes of the terms. The bounds
`|J0| ≤ 2²⁰`, `|A0| ≤ 2²⁰` keep the underflow of `τ²`, `τ³` (absolute `2⁻¹⁴⁹`) from being amplified
by a huge `J0` or `A0`; without them the statement fails (`τ = 2⁻⁶⁰`, `J0 = 2¹²⁰`: `τ³` underflows to
`0` while `J0 τ³ / 6 ≈ 2⁻⁶²·⁶`). -/
theorem eval_const {τ J0 A0 V0 P0 Jt At Vt Pt : Float32} (fτ : τ.IsFinite) (fJ : J0.IsFinite)
    (fA : A0.IsFinite) (fV : V0.IsFinite) (fP : P0.IsFinite) (hτ0 : 0 ≤ τ.toReal)
    (hτ1 : τ.toReal ≤ 2 ^ 10) (hJ : |J0.toReal| * τ.toReal ^ 3 ≤ 64)
    (hA : |A0.toReal| * τ.toReal ^ 2 ≤ 64) (hV : |V0.toReal| * τ.toReal ≤ 64)
    (hP : |P0.toReal| ≤ 64) (hJb : |J0.toReal| ≤ 2 ^ 20) (hAb : |A0.toReal| ≤ 2 ^ 20) :
    (SCurve.calc_javp_for_segment_const_jerk τ J0 A0 V0 P0 Jt At Vt Pt).2.2.2.IsFinite ∧
      |(SCurve.calc_javp_for_segment_const_jerk τ J0 A0 V0 P0 Jt At Vt Pt).2.2.2.toReal -
        SC.cP ⟨A0.toReal, V0.toReal, P0.toReal⟩ J0.toReal τ.toReal| ≤
        16 / 16777216 * (|P0.toReal| + |V0.toReal| * τ.toReal + |A0.toReal| * τ.toReal ^ 2 +
          |J0.toReal| * τ.toReal ^ 3) + 1 / 2 ^ 100 := by
  have hPt : (SCurve.calc_javp_for_segment_const_jerk τ J0 A0 V0 P0 Jt At Vt Pt).2.2.2 =
      P0 + V0 * τ + (0.5 : Float32) * A0 * (τ * τ) + (0.166666672 : Float32) * J0 * (τ * τ * τ) := by
    rw [← sce_c6]; rfl
  rw [hPt]
  generalize ht : τ.toReal = t at *
  have eT : SCE32 τ t t 0 0 := SCE32.lit fτ ht (by rw [abs_of_nonneg hτ0])
  have eV := SCE32.lit fV rfl le_rfl
  have eP := SCE32.lit fP rfl le_rfl
  have eA := SCE32.lit fA rfl le_rfl
  have eJ := SCE32.lit fJ rfl le_rfl
  have eH : SCE32 (0.5 : Float32) (1 / 2) (1 / 2) 0 0 :=
    SCE32.lit f32_isFinite_0p5 f32_toReal_0p5 (by norm_num)
  have eC : SCE32 (0.166666672 : Float32) (1 / 6) (1 / 6) 1 0 :=
    ⟨sce_isFinite_c6, by rw [sce_toReal_c6]; norm_num, by norm_num⟩
  have ht2 : t * t ≤ 2 ^ 20 := by nlinarith
  have ht3 : t * t * t ≤ 2 ^ 30 := by nlinarith
  have hA0 := abs_nonneg A0.toReal
  have hJ0 := abs_nonneg J0.toReal
  have v1 : SCE32 (V0 * τ) (V0.toReal * t) (|V0.toReal| * t) 1 (1 / 2 ^ 150) := by
    apply SCE32.mul eV eT (da := 0) (db := 0) <;> sce_side
  have s1 : SCE32 (P0 + V0 * τ) (P0.toReal + V0.toReal * t) (|P0.toReal| + |V0.toReal| * t) 3
      (1 / 2 ^ 149) := by
    apply SCE32.add eP v1 (K := 1) <;> sce_side
  have h1 : SCE32 ((0.5 : Float32) * A0) (1 / 2 * A0.toReal) (1 / 2 * |A0.toReal|) 1 (1 / 2 ^ 150) := by
    apply SCE32.mul eH eA (da := 0) (db := 0) <;> sce_side
  have q1 : SCE32 (τ * τ) (t * t) (t * t) 1 (1 / 2 ^ 150) := by
    apply SCE32.mul eT eT (da := 0) (db := 0) <;> sce_side
  have t2 : SCE32 ((0.5 : Float32) * A0 * (τ * τ)) (1 / 2 * A0.toReal * (t * t))
      (1 / 2 * |A0.toReal| * (t * t)) 4 (1 / 2 ^ 128) := by
    apply SCE32.mul h1 q1 (da := 1 / 2 ^ 130) (db := 1 / 2 ^ 131) <;> sce_side
  have s2 : SCE32 (P0 + V0 * τ + (0.5 : Float32) * A0 * (τ * τ))
      (P0.toReal + V0.toReal * t + 1 / 2 * A0.toReal * (t * t))
      (|P0.toReal| + |V0.toReal| * t + 1 / 2 * |A0.toReal| * (t * t)) 6 (1 / 2 ^ 127) := by
    apply SCE32.add s1 t2 (K := 4) <;> sce_side
  have j1 : SCE32 ((0.166666672 : Float32) * J0) (1 / 6 * J0.toReal) (1 / 6 * |J0.toReal|) 3
      (1 / 2 ^ 150) := by
    apply SCE32.mul eC eJ (da := 0) (db := 0) <;> sce_side
  have q3 : SCE32 (τ * τ * τ) (t * t * t) (t * t * t) 3 (1 / 2 ^ 139) := by
    apply SCE32.mul q1 eT (da := 1 / 2 ^ 140) (db := 0) <;> sce_side
  have t3 : SCE32 ((0.166666672 : Float32) * J0 * (τ * τ * τ)) (1 / 6 * J0.toReal * (t * t * t))
      (1 / 6 * |J0.toReal| * (t * t * t)) 8 (1 / 2 ^ 118) := by
    apply SCE32.mul j1 q3 (da := 1 / 2 ^ 120) (db := 1 / 2 ^ 120) <;> sce_side
  have s3 := SCE32.add s2 t3 (K := 8) (k := 10) (c := 1 / 2 ^ 117) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by nlinarith) (by norm_num) (by norm_num)
  refine ⟨s3.1, ?_⟩
  have hr : P0.toReal + V0.toReal * t + 1 / 2 * A0.toReal * (t * t) + 1 / 6 * J0.toReal * (t * t * t)
      = SC.cP ⟨A0.toReal, V0.toReal, P0.toReal⟩ J0.toReal t := by
    simp only [SC.cP]; ring
  have := s3.2.1
  rw [hr] at this
  have : 0 ≤ |A0.toReal| * (t * t) := by positivity
  have : 0 ≤ |J0.toReal| * (t * t * t) := by positivity
  have : 0 ≤ |V0.toReal| * t := by positivity
  have := abs_nonneg P0.toReal
  have e1 : t ^ 2 = t * t := by ring
  have e2 : t ^ 3 = t * t * t := by ring
  rw [e1, e2]
  linarith

theorem B32.sce_lit {x : Float32} {v R : ℝ} (h : x.IsFinite) (hx : x.toReal = v) (hR : |v| ≤ R) :
    B32 x v 0 R := ⟨⟨h, by rw [hx]; simp⟩, hR⟩

theorem B32.sce_ofR32 {x : Float32} {r k R : ℝ} (h : R32 x r k) (hk : 0 ≤ k) (hR : |r| ≤ R) :
    B32 x r (k * (1 / 16777216) * R) R :=
  ⟨⟨h.1, h.2.trans (mul_le_mul_of_nonneg_left hR (by positivity))⟩, hR⟩

/-- Division by a relative approximation bounded away from `0` by `mlo`. -/
theorem B32.sce_divR {a b : Float32} {ra rb ea Ra kb mlo e R : ℝ} (ha : B32 a ra ea Ra)
    (hb : R32 b rb kb) (hkb : 0 ≤ kb) (hkb1 : kb ≤ 2 ^ 20) (hlo : mlo ≤ |rb|) (hmlo : 0 < mlo)
    (hR : Ra / mlo ≤ R)
    (hcap : R + (ea + Ra * kb / 16777216) / (mlo * (1 - kb / 16777216)) ≤ capF)
    (hc : (ea + Ra * kb / 16777216) / (mlo * (1 - kb / 16777216)) +
      1 / 16777216 * (R + (ea + Ra * kb / 16777216) / (mlo * (1 - kb / 16777216))) +
        1 / 10 ^ 40 ≤ e) :
    B32 (a / b) (ra / rb) e R := by
  have hea := ha.e_nonneg
  have hRa : 0 ≤ Ra := (abs_nonneg _).trans ha.2
  have hu : kb / 16777216 ≤ 1 / 16 := by
    rw [div_le_iff₀ (by norm_num)]; linarith
  have hrb : 0 < |rb| := by linarith
  have h1 : 0 < 1 - kb / 16777216 := by linarith
  have hm : 0 < |rb| * (1 - kb / 16777216) := mul_pos hrb h1
  have hmeb : |rb| * (1 - kb / 16777216) + kb * (1 / 16777216) * |rb| = |rb| := by ring
  have hQ : |ra / rb| ≤ R := by
    rw [abs_div]
    exact (div_le_div₀ hRa ha.2 hmlo hlo).trans hR
  have key : ea / (|rb| * (1 - kb / 16777216)) + Ra * (kb * (1 / 16777216) * |rb|) /
      ((|rb| * (1 - kb / 16777216)) * (|rb| * (1 - kb / 16777216) + kb * (1 / 16777216) * |rb|)) ≤
      (ea + Ra * kb / 16777216) / (mlo * (1 - kb / 16777216)) := by
    rw [hmeb]
    have e1 : ea / (|rb| * (1 - kb / 16777216)) + Ra * (kb * (1 / 16777216) * |rb|) /
        ((|rb| * (1 - kb / 16777216)) * |rb|) =
        (ea + Ra * kb / 16777216) / (|rb| * (1 - kb / 16777216)) := by
      field_simp
    rw [e1]
    apply div_le_div_of_nonneg_left (by positivity) (mul_pos hmlo h1)
    exact mul_le_mul_of_nonneg_right hlo h1.le
  refine ⟨A32.div_c ha.1 (R32.to_A32 hb) ha.2 hm (le_of_eq hmeb) (by positivity) hQ
    (by linarith) (by linarith), hQ⟩

theorem B32.sce_sin (hL : LibmSpec) {x : Float32} {r e R : ℝ} (h : B32 x r e R) :
    B32 (Float32.sin x) (Real.sin r) (e + 1 / 2 ^ 22) 1 := by
  obtain ⟨hf, -, h2⟩ := hL.sinf x h.1.1
  refine ⟨⟨hf, ?_⟩, Real.abs_sin_le_one r⟩
  have h3 := Real.abs_sin_sub_sin_le x.toReal r
  have h4 := abs_sub_le (Float32.sin x).toReal (Real.sin x.toReal) (Real.sin r)
  have h5 : libm32Err = 1 / 2 ^ 22 := by unfold libm32Err; norm_num
  rw [h5] at h2
  linarith [h.1.2]

macro "sce_num" : tactic => `(tactic| norm_num [capF])

set_option maxHeartbeats 4000000 in
/-- **Increasing jerk** (`b = π / t_j`): within `10⁻⁴` on the mission's ranges. -/
theorem eval_incr (hL : LibmSpec) {τ tj Jm A0 V0 P0 Jt At Vt Pt : Float32} (fτ : τ.IsFinite)
    (ft : tj.IsFinite) (fJ : Jm.IsFinite) (fA : A0.IsFinite) (fV : V0.IsFinite)
    (fP : P0.IsFinite) (ht0 : 1 / 512 ≤ tj.toReal) (ht1 : tj.toReal ≤ 1 / 2)
    (hτ0 : 0 ≤ τ.toReal) (hτ1 : τ.toReal ≤ 2 * tj.toReal) (hJ : |Jm.toReal| ≤ 8)
    (hA : |A0.toReal| ≤ 8) (hV : |V0.toReal| ≤ 8) (hP : |P0.toReal| ≤ 8) :
    (SCurve.calc_javp_for_segment_incr_jerk τ tj Jm A0 V0 P0 Jt At Vt Pt).2.2.2.IsFinite ∧
      |(SCurve.calc_javp_for_segment_incr_jerk τ tj Jm A0 V0 P0 Jt At Vt Pt).2.2.2.toReal -
        SC.iP ⟨A0.toReal, V0.toReal, P0.toReal⟩ Jm.toReal (Real.pi / tj.toReal) τ.toReal| ≤
        1 / 10 ^ 4 := by
  have hpos := sce_isPos ft ht0
  have hPt : (SCurve.calc_javp_for_segment_incr_jerk τ tj Jm A0 V0 P0 Jt At Vt Pt).2.2.2 =
      P0 + V0 * τ + (0.5 : Float32) * A0 * (τ * τ) +
        (-(Jm * (0.5 : Float32)) / ((Float.toFloat32 (3.1415926535897931 : Float) / tj) *
          (Float.toFloat32 (3.1415926535897931 : Float) / tj))) * τ +
        (Jm * (0.5 : Float32)) * (τ * τ * τ) / (6.0 : Float32) +
        ((Jm * (0.5 : Float32)) / ((Float.toFloat32 (3.1415926535897931 : Float) / tj) *
          (Float.toFloat32 (3.1415926535897931 : Float) / tj) *
          (Float.toFloat32 (3.1415926535897931 : Float) / tj))) *
          Float32.sin ((Float.toFloat32 (3.1415926535897931 : Float) / tj) * τ) := by
    simp only [SCurve.calc_javp_for_segment_incr_jerk, hpos, Bool.not_true]
    rfl
  rw [hPt]
  have hpf := R32.pi_f hL
  generalize Float.toFloat32 (3.1415926535897931 : Float) = pf at hpf ⊢
  have p3 := Real.pi_gt_three
  have p4 := Real.pi_lt_d2
  generalize hT : tj.toReal = T at *
  generalize ht : τ.toReal = t at *
  have hT0 : 0 < T := by linarith
  -- `β = π / tj`, relative
  have hb6 : 6 ≤ Real.pi / T := by rw [le_div_iff₀ hT0]; linarith
  have hb1 : Real.pi / T ≤ 1613 := by rw [div_le_iff₀ hT0]; nlinarith
  generalize hb : Real.pi / T = b at hb6 hb1 ⊢
  have hβ : R32 (pf / tj) b 4 := by
    rw [← hb]
    have eTj : R32 tj T 0 := hT ▸ R32.of_exact ft le_rfl
    refine R32.div hpf eTj (by norm_num) le_rfl (by norm_num)
      (by norm_num) hT0.ne' ?_ ?_ (by norm_num)
    · rw [hb, abs_of_pos (by linarith)]; linarith
    · rw [hb, abs_of_pos (by linarith)]; linarith
  have hββ : R32 (pf / tj * (pf / tj)) (b * b) 10 := by
    refine R32.mul hβ hβ (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_ ?_ (by norm_num)
    · rw [abs_of_pos (by positivity)]; nlinarith
    · rw [abs_of_pos (by positivity)]; nlinarith
  have hβββ : R32 (pf / tj * (pf / tj) * (pf / tj)) (b * b * b) 16 := by
    refine R32.mul hββ hβ (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_ ?_ (by norm_num)
    · rw [abs_of_pos (by positivity)]; nlinarith
    · rw [abs_of_pos (by positivity)]
      have : b * b ≤ 1613 * 1613 := by nlinarith
      nlinarith
  have hbb : 36 ≤ |b * b| := by rw [abs_of_pos (by positivity)]; nlinarith
  have hbbb : 216 ≤ |b * b * b| := by
    rw [abs_of_pos (by positivity)]
    have : 36 ≤ b * b := by nlinarith
    nlinarith
  have hbR : |b| ≤ 1613 := by rw [abs_of_pos (by linarith)]; exact hb1
  -- the inputs
  have eP := B32.of_exact fP hP
  have eV := B32.of_exact fV hV
  have eA := B32.of_exact fA hA
  have eJ := B32.of_exact fJ hJ
  have eT : B32 τ t 0 1 := B32.sce_lit fτ ht (by rw [abs_of_nonneg hτ0]; linarith)
  have eH : B32 (0.5 : Float32) (1 / 2) 0 (1 / 2) :=
    B32.sce_lit f32_isFinite_0p5 f32_toReal_0p5 (by norm_num)
  have e6 : B32 (6.0 : Float32) 6 0 6 := B32.sce_lit f32_isFinite_6p0 f32_toReal_6p0 (by norm_num)
  -- the chain
  have v1 : B32 (V0 * τ) (V0.toReal * t) (49 / 10 ^ 8) 8 := B32.mul eV eT (by sce_num) (by sce_num) (by sce_num)
  have s1 : B32 (P0 + V0 * τ) (P0.toReal + V0.toReal * t) (15 / 10 ^ 7) 16 :=
    B32.add eP v1 (by sce_num) (by sce_num) (by sce_num)
  have h1 : B32 ((0.5 : Float32) * A0) (1 / 2 * A0.toReal) (25 / 10 ^ 8) 4 :=
    B32.mul eH eA (by sce_num) (by sce_num) (by sce_num)
  have q1 : B32 (τ * τ) (t * t) (61 / 10 ^ 9) 1 := B32.mul eT eT (by sce_num) (by sce_num) (by sce_num)
  have t2 : B32 ((0.5 : Float32) * A0 * (τ * τ)) (1 / 2 * A0.toReal * (t * t)) (74 / 10 ^ 8) 4 :=
    B32.mul h1 q1 (by sce_num) (by sce_num) (by sce_num)
  have s2 := B32.add s1 t2 (e := 35 / 10 ^ 7) (R := 20) (by sce_num) (by sce_num) (by sce_num)
  have al : B32 (Jm * (0.5 : Float32)) (Jm.toReal * (1 / 2)) (25 / 10 ^ 8) 4 :=
    B32.mul eJ eH (by sce_num) (by sce_num) (by sce_num)
  have d1 : B32 (-(Jm * (0.5 : Float32)) / (pf / tj * (pf / tj))) (-(Jm.toReal * (1 / 2)) / (b * b))
      (81 / 10 ^ 9) (1 / 9) :=
    B32.sce_divR al.neg hββ (by norm_num) (by norm_num) hbb (by norm_num) (by sce_num) (by sce_num)
      (by sce_num)
  have t3 := B32.mul d1 eT (e := 89 / 10 ^ 9) (R := 1 / 9) (by sce_num) (by sce_num) (by sce_num)
  have s3 := B32.add s2 t3 (e := 49 / 10 ^ 7) (R := 21) (by sce_num) (by sce_num) (by sce_num)
  have q3 := B32.mul q1 eT (e := 13 / 10 ^ 8) (R := 1) (by sce_num) (by sce_num) (by sce_num)
  have a3 := B32.mul al q3 (e := 11 / 10 ^ 7) (R := 4) (by sce_num) (by sce_num) (by sce_num)
  have t4 := B32.div a3 e6 (e := 23 / 10 ^ 8) (R := 2 / 3) (mlo := 6) (by norm_num) (by norm_num)
    (by sce_num) (by sce_num) (by sce_num)
  have s4 := B32.add s3 t4 (e := 66 / 10 ^ 7) (R := 22) (by sce_num) (by sce_num) (by sce_num)
  have d2 : B32 (Jm * (0.5 : Float32) / (pf / tj * (pf / tj) * (pf / tj)))
      (Jm.toReal * (1 / 2) / (b * b * b)) (21 / 10 ^ 9) (1 / 54) :=
    B32.sce_divR al hβββ (by norm_num) (by norm_num) hbbb (by norm_num) (by sce_num) (by sce_num)
      (by sce_num)
  have eB : B32 (pf / tj) b (4 / 10 ^ 4) 1613 :=
    (B32.sce_ofR32 hβ (by norm_num) hbR).mono (by norm_num) le_rfl
  have bt := B32.mul eB eT (e := 51 / 10 ^ 5) (R := 1613) (by sce_num) (by sce_num) (by sce_num)
  have sn : B32 (Float32.sin (pf / tj * τ)) (Real.sin (b * t)) (52 / 10 ^ 5) 1 :=
    (B32.sce_sin hL bt).mono (by norm_num) le_rfl
  have t5 := B32.mul d2 sn (e := 98 / 10 ^ 7) (R := 1 / 54) (by sce_num) (by sce_num) (by sce_num)
  have s5 := B32.add s4 t5 (e := 18 / 10 ^ 6) (R := 23) (by sce_num) (by sce_num) (by sce_num)
  refine ⟨s5.1.1, ?_⟩
  have hb0 : b ≠ 0 := by linarith
  have hr : P0.toReal + V0.toReal * t + 1 / 2 * A0.toReal * (t * t) +
      -(Jm.toReal * (1 / 2)) / (b * b) * t + Jm.toReal * (1 / 2) * (t * t * t) / 6 +
      Jm.toReal * (1 / 2) / (b * b * b) * Real.sin (b * t) =
      SC.iP ⟨A0.toReal, V0.toReal, P0.toReal⟩ Jm.toReal b t := by
    simp only [SC.iP]; field_simp
  have := s5.1.2
  rw [hr] at this
  linarith

set_option maxHeartbeats 4000000 in
/-- **Decreasing jerk** (`b = π / t_j`): within `10⁻⁴` on the mission's ranges. -/
theorem eval_decr (hL : LibmSpec) {τ tj Jm A0 V0 P0 Jt At Vt Pt : Float32} (fτ : τ.IsFinite)
    (ft : tj.IsFinite) (fJ : Jm.IsFinite) (fA : A0.IsFinite) (fV : V0.IsFinite)
    (fP : P0.IsFinite) (ht0 : 1 / 512 ≤ tj.toReal) (ht1 : tj.toReal ≤ 1 / 2)
    (hτ0 : 0 ≤ τ.toReal) (hτ1 : τ.toReal ≤ 2 * tj.toReal) (hJ : |Jm.toReal| ≤ 8)
    (hA : |A0.toReal| ≤ 8) (hV : |V0.toReal| ≤ 8) (hP : |P0.toReal| ≤ 8) :
    (SCurve.calc_javp_for_segment_decr_jerk τ tj Jm A0 V0 P0 Jt At Vt Pt).2.2.2.IsFinite ∧
      |(SCurve.calc_javp_for_segment_decr_jerk τ tj Jm A0 V0 P0 Jt At Vt Pt).2.2.2.toReal -
        SC.dP ⟨A0.toReal, V0.toReal, P0.toReal⟩ Jm.toReal (Real.pi / tj.toReal) tj.toReal
          τ.toReal| ≤ 1 / 10 ^ 4 := by
  have hpos := sce_isPos ft ht0
  have hPt : (SCurve.calc_javp_for_segment_decr_jerk τ tj Jm A0 V0 P0 Jt At Vt Pt).2.2.2 =
      (P0 - ((Jm * (0.5 : Float32)) * ((-(1.0 : Float32) / (((Float.toFloat32 (3.1415926535897931 : Float)) / tj) * ((Float.toFloat32 (3.1415926535897931 : Float)) / tj))) * tj + ((1.0 : Float32) / (6.0 : Float32)) * ((tj * tj) * tj)))) + (V0 - ((Jm * (0.5 : Float32)) * ((tj * tj) * (0.5 : Float32) - (2.0 : Float32) / (((Float.toFloat32 (3.1415926535897931 : Float)) / tj) * ((Float.toFloat32 (3.1415926535897931 : Float)) / tj))))) * τ + (0.5 : Float32) * (A0 - ((Jm * (0.5 : Float32)) * tj)) * (τ * τ) + (-(Jm * (0.5 : Float32)) / (((Float.toFloat32 (3.1415926535897931 : Float)) / tj) * ((Float.toFloat32 (3.1415926535897931 : Float)) / tj))) * (τ + tj) + ((Jm * (0.5 : Float32)) / (6.0 : Float32)) * (τ + tj) * (τ + tj) * (τ + tj) + ((Jm * (0.5 : Float32)) / (((Float.toFloat32 (3.1415926535897931 : Float)) / tj) * ((Float.toFloat32 (3.1415926535897931 : Float)) / tj) * ((Float.toFloat32 (3.1415926535897931 : Float)) / tj))) * Float32.sin (((Float.toFloat32 (3.1415926535897931 : Float)) / tj) * (τ + tj)) := by
    simp only [SCurve.calc_javp_for_segment_decr_jerk, hpos, Bool.not_true]
    rfl
  rw [hPt]
  have hpf := R32.pi_f hL
  generalize Float.toFloat32 (3.1415926535897931 : Float) = pf at hpf ⊢
  have p3 := Real.pi_gt_three
  have p4 := Real.pi_lt_d2
  generalize hT : tj.toReal = T at *
  generalize ht : τ.toReal = t at *
  have hT0 : 0 < T := by linarith
  have hb6 : 6 ≤ Real.pi / T := by rw [le_div_iff₀ hT0]; linarith
  have hb1 : Real.pi / T ≤ 1613 := by rw [div_le_iff₀ hT0]; nlinarith
  generalize hb : Real.pi / T = b at hb6 hb1 ⊢
  have hβ : R32 (pf / tj) b 4 := by
    rw [← hb]
    have eTj : R32 tj T 0 := hT ▸ R32.of_exact ft le_rfl
    refine R32.div hpf eTj (by norm_num) le_rfl (by norm_num)
      (by norm_num) hT0.ne' ?_ ?_ (by norm_num)
    · rw [hb, abs_of_pos (by linarith)]; linarith
    · rw [hb, abs_of_pos (by linarith)]; linarith
  have hββ : R32 (pf / tj * (pf / tj)) (b * b) 10 := by
    refine R32.mul hβ hβ (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_ ?_ (by norm_num)
    · rw [abs_of_pos (by positivity)]; nlinarith
    · rw [abs_of_pos (by positivity)]; nlinarith
  have hβββ : R32 (pf / tj * (pf / tj) * (pf / tj)) (b * b * b) 16 := by
    refine R32.mul hββ hβ (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_ ?_ (by norm_num)
    · rw [abs_of_pos (by positivity)]; nlinarith
    · rw [abs_of_pos (by positivity)]
      have : b * b ≤ 1613 * 1613 := by nlinarith
      nlinarith
  have hbb : 36 ≤ |b * b| := by rw [abs_of_pos (by positivity)]; nlinarith
  have hbbb : 216 ≤ |b * b * b| := by
    rw [abs_of_pos (by positivity)]
    have : 36 ≤ b * b := by nlinarith
    nlinarith
  have hbR : |b| ≤ 1613 := by rw [abs_of_pos (by linarith)]; exact hb1
  -- the inputs
  have eP := B32.of_exact fP hP
  have eV := B32.of_exact fV hV
  have eA := B32.of_exact fA hA
  have eJ := B32.of_exact fJ hJ
  have eT : B32 τ t 0 1 := B32.sce_lit fτ ht (by rw [abs_of_nonneg hτ0]; linarith)
  have eTj : B32 tj T 0 (1 / 2) := B32.sce_lit ft hT (by rw [abs_of_pos hT0]; linarith)
  have eH : B32 (0.5 : Float32) (1 / 2) 0 (1 / 2) :=
    B32.sce_lit f32_isFinite_0p5 f32_toReal_0p5 (by norm_num)
  have e6 : B32 (6.0 : Float32) 6 0 6 := B32.sce_lit f32_isFinite_6p0 f32_toReal_6p0 (by norm_num)
  have e2 : B32 (2.0 : Float32) 2 0 2 := B32.sce_lit f32_isFinite_2p0 f32_toReal_2p0 (by norm_num)
  have e1 : B32 (1.0 : Float32) 1 0 1 := B32.sce_lit f32_isFinite_1p0 f32_toReal_1p0 (by norm_num)
  -- `AT`, `VT`, `PT`
  have al : B32 (Jm * (0.5 : Float32)) (Jm.toReal * (1 / 2)) (25 / 10 ^ 8) 4 :=
    B32.mul eJ eH (by sce_num) (by sce_num) (by sce_num)
  have cAT := B32.mul al eTj (e := 25 / 10 ^ 8) (R := 2) (by sce_num) (by sce_num) (by sce_num)
  have tt := B32.mul eTj eTj (e := 16 / 10 ^ 9) (R := 1 / 4) (by sce_num) (by sce_num) (by sce_num)
  have tth := B32.mul tt eH (e := 16 / 10 ^ 9) (R := 1 / 8) (by sce_num) (by sce_num) (by sce_num)
  have d2b : B32 ((2.0 : Float32) / (pf / tj * (pf / tj))) (2 / (b * b)) (37 / 10 ^ 9) (1 / 18) :=
    B32.sce_divR e2 hββ (by norm_num) (by norm_num) hbb (by norm_num) (by sce_num) (by sce_num)
      (by sce_num)
  have vd := B32.sub tth d2b (e := 66 / 10 ^ 9) (R := 1 / 5) (by sce_num) (by sce_num) (by sce_num)
  have cVT := B32.mul al vd (e := 37 / 10 ^ 8) (R := 4 / 5) (by sce_num) (by sce_num) (by sce_num)
  have m1 : B32 (-(1.0 : Float32) / (pf / tj * (pf / tj))) (-1 / (b * b)) (19 / 10 ^ 9) (1 / 36) :=
    B32.sce_divR e1.neg hββ (by norm_num) (by norm_num) hbb (by norm_num) (by sce_num) (by sce_num)
      (by sce_num)
  have m1t := B32.mul m1 eTj (e := 11 / 10 ^ 9) (R := 1 / 72) (by sce_num) (by sce_num) (by sce_num)
  have c6 := B32.div e1 e6 (e := 11 / 10 ^ 9) (R := 1 / 6) (mlo := 6) (by norm_num) (by norm_num)
    (by sce_num) (by sce_num) (by sce_num)
  have t3j := B32.mul tt eTj (e := 16 / 10 ^ 9) (R := 1 / 8) (by sce_num) (by sce_num) (by sce_num)
  have c6t := B32.mul c6 t3j (e := 54 / 10 ^ 10) (R := 1 / 48) (by sce_num) (by sce_num) (by sce_num)
  have pin := B32.add m1t c6t (e := 2 / 10 ^ 8) (R := 1 / 20) (by sce_num) (by sce_num) (by sce_num)
  have cPT := B32.mul al pin (e := 11 / 10 ^ 8) (R := 1 / 5) (by sce_num) (by sce_num) (by sce_num)
  -- the position
  have w1 := B32.sub eP cPT (e := 66 / 10 ^ 8) (R := 9) (by sce_num) (by sce_num) (by sce_num)
  have w2 := B32.sub eV cVT (e := 92 / 10 ^ 8) (R := 9) (by sce_num) (by sce_num) (by sce_num)
  have w3 := B32.mul w2 eT (e := 15 / 10 ^ 7) (R := 9) (by sce_num) (by sce_num) (by sce_num)
  have s1 := B32.add w1 w3 (e := 33 / 10 ^ 7) (R := 18) (by sce_num) (by sce_num) (by sce_num)
  have w4 := B32.sub eA cAT (e := 86 / 10 ^ 8) (R := 10) (by sce_num) (by sce_num) (by sce_num)
  have w5 := B32.mul eH w4 (e := 74 / 10 ^ 8) (R := 5) (by sce_num) (by sce_num) (by sce_num)
  have q1 := B32.mul eT eT (e := 61 / 10 ^ 9) (R := 1) (by sce_num) (by sce_num) (by sce_num)
  have w6 := B32.mul w5 q1 (e := 14 / 10 ^ 7) (R := 5) (by sce_num) (by sce_num) (by sce_num)
  have s2 := B32.add s1 w6 (e := 62 / 10 ^ 7) (R := 23) (by sce_num) (by sce_num) (by sce_num)
  have tp := B32.add eT eTj (e := 91 / 10 ^ 9) (R := 3 / 2) (by sce_num) (by sce_num) (by sce_num)
  have d1 : B32 (-(Jm * (0.5 : Float32)) / (pf / tj * (pf / tj))) (-(Jm.toReal * (1 / 2)) / (b * b))
      (81 / 10 ^ 9) (1 / 9) :=
    B32.sce_divR al.neg hββ (by norm_num) (by norm_num) hbb (by norm_num) (by sce_num) (by sce_num)
      (by sce_num)
  have w7 := B32.mul d1 tp (e := 15 / 10 ^ 8) (R := 1 / 6) (by sce_num) (by sce_num) (by sce_num)
  have s3 := B32.add s2 w7 (e := 79 / 10 ^ 7) (R := 24) (by sce_num) (by sce_num) (by sce_num)
  have a6 := B32.div al e6 (e := 83 / 10 ^ 9) (R := 2 / 3) (mlo := 6) (by norm_num) (by norm_num)
    (by sce_num) (by sce_num) (by sce_num)
  have x1 := B32.mul a6 tp (e := 25 / 10 ^ 8) (R := 1) (by sce_num) (by sce_num) (by sce_num)
  have x2 := B32.mul x1 tp (e := 57 / 10 ^ 8) (R := 3 / 2) (by sce_num) (by sce_num) (by sce_num)
  have x3 := B32.mul x2 tp (e := 12 / 10 ^ 7) (R := 9 / 4) (by sce_num) (by sce_num) (by sce_num)
  have s4 := B32.add s3 x3 (e := 11 / 10 ^ 6) (R := 27) (by sce_num) (by sce_num) (by sce_num)
  have d3 : B32 (Jm * (0.5 : Float32) / (pf / tj * (pf / tj) * (pf / tj)))
      (Jm.toReal * (1 / 2) / (b * b * b)) (21 / 10 ^ 9) (1 / 54) :=
    B32.sce_divR al hβββ (by norm_num) (by norm_num) hbbb (by norm_num) (by sce_num) (by sce_num)
      (by sce_num)
  have eB : B32 (pf / tj) b (4 / 10 ^ 4) 1613 :=
    (B32.sce_ofR32 hβ (by norm_num) hbR).mono (by norm_num) le_rfl
  have bt := B32.mul eB tp (e := 9 / 10 ^ 4) (R := 2420) (by sce_num) (by sce_num) (by sce_num)
  have sn : B32 (Float32.sin (pf / tj * (τ + tj))) (Real.sin (b * (t + T))) (91 / 10 ^ 5) 1 :=
    (B32.sce_sin hL bt).mono (by norm_num) le_rfl
  have t5 := B32.mul d3 sn (e := 18 / 10 ^ 6) (R := 1 / 54) (by sce_num) (by sce_num) (by sce_num)
  have s5 := B32.add s4 t5 (e := 31 / 10 ^ 6) (R := 28) (by sce_num) (by sce_num) (by sce_num)
  refine ⟨s5.1.1, ?_⟩
  have hb0 : b ≠ 0 := by linarith
  refine le_trans (le_of_eq ?_) (s5.1.2.trans (by norm_num))
  congr 2
  simp only [SC.dP, SC.rAT, SC.rVT, SC.rPT]
  field_simp

end

end Contracts.Mission
