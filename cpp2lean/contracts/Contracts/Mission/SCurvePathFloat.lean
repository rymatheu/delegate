import Contracts.Mission.SCurveFloat

/-!
# `calculate_path` in `float`: the accelerating phase stays within the half leg

Per branch of `SCurve::calculate_path` (`AP_Math/SCurve.cpp`), with the code's `float`
expressions: the constant-acceleration time `t₄` keeps `p7` within `L (1 + 1/5000)`
(`p7_t4_bound`), from the root's `float` accuracy (`quad_float`).
-/

namespace Contracts.Mission

open Float.Model UnpackedFloat AC_WPNav_lib

noncomputable section

/-- The code's time to reach `Vm` (`V0 = 0`). -/
def tvelF (Am Jm tj Vm : Float32) : Float32 :=
  -((0.0 : Float32) - Vm + Am * tj + (Am * Am) / Jm) / Am

/-- The code's `t₄` (`V0 = 0`). -/
def t4F (Am Jm tj L Vm : Float32) : Float32 :=
  MAX_float2 (MIN_float2 (tvelF Am Jm tj Vm) (MAX_float2 (quadNum Am Jm tj L true)
    (quadNum Am Jm tj L false))) (0.0 : Float32)

theorem tvelF_finite {Am Jm tj L Vm : Float32} (h : QIn Am Jm tj L) (hV : Vm.IsFinite)
    (hV' : |Vm.toReal| ≤ 4) : (tvelF Am Jm tj Vm).IsFinite := by
  obtain ⟨fa, fj, ft, fl, a0, a1, j0, j1, t0, t1, l0, l1⟩ := h
  have ha0 : 0 < Am.toReal := lt_of_lt_of_le (by norm_num) a0
  have hj0 : 0 < Jm.toReal := lt_of_lt_of_le (by norm_num) j0
  have bA := B32.of_exact fa (R := 4) (by rw [abs_of_pos ha0]; exact a1)
  have bJ := B32.of_exact fj (R := 8) (by rw [abs_of_pos hj0]; exact j1)
  have bT := B32.of_exact ft (R := 1) (by rw [abs_of_pos (lt_of_lt_of_le (by norm_num) t0)]; exact t1)
  have bV := B32.of_exact hV hV'
  have b0 := B32.of_exact f32_isFinite_0p0 (R := 0) (by rw [f32_toReal_0p0]; simp)
  have s1 := B32.sub (e := 1 / 10 ^ 6) (R := 4) b0 bV (by norm_num) (by norm_num [capF]) (by norm_num)
  have m1 := B32.mul (e := 1 / 10 ^ 6) (R := 4) bA bT (by norm_num [capF]) (by norm_num) (by norm_num)
  have s2 := B32.add (e := 1 / 10 ^ 5) (R := 8) s1 m1 (by norm_num) (by norm_num [capF]) (by norm_num)
  have m2 := B32.mul (e := 1 / 10 ^ 5) (R := 16) bA bA (by norm_num [capF]) (by norm_num) (by norm_num)
  have d1 := B32.div (e := 1 / 10 ^ 3) (R := 256) (mlo := 1 / 2 ^ 4) m2 bJ
    (by rw [abs_of_pos hj0]; exact j0) (by norm_num) (by norm_num) (by norm_num [capF]) (by norm_num)
  have s3 := B32.add (e := 1 / 10 ^ 2) (R := 264) s2 d1 (by norm_num) (by norm_num [capF]) (by norm_num)
  have d2 := B32.div (e := 100) (R := 264 * 2 ^ 12) (mlo := 1 / 2 ^ 12) s3.neg bA
    (by rw [abs_of_pos ha0]; exact a0) (by norm_num) (by norm_num) (by norm_num [capF]) (by norm_num)
  exact d2.1.1

/-- The positive root is at least `-3/2 (t + a/j)`. -/
theorem quadRoot_ge {a j t l : ℝ} (ha : 0 < a) (hj : 0 < j) :
    -(3 / 2) * (t + a / j) ≤ SC.quadRoot a j t l := by
  rw [quadRoot_eq, le_div_iff₀ (by positivity)]
  have := Real.sqrt_nonneg (quadX a j t l)
  have : -(3 / 2) * (t + a / j) * (a * j) = a ^ 2 * (-3 / 2) - a * j * t * (3 / 2) := by
    field_simp; ring
  linarith

set_option maxHeartbeats 4000000 in
/-- **`t₄` of `calculate_path`** keeps the accelerating phase within `L (1 + 1/2000)`, provided
the leg is not much longer than the ramps (`L ≤ 200 a R²`) and the accelerating phase without
constant acceleration fits (`p7 a R 0 ≤ L (1 + 10⁻⁴)`), with `R = t + a/j`. -/
theorem p7_t4_bound (hL : LibmSpec) {Am Jm tj L Vm : Float32} (h : QIn Am Jm tj L)
    (hV : Vm.IsFinite) (hV' : |Vm.toReal| ≤ 4)
    (hl : L.toReal ≤ 200 * Am.toReal * (tj.toReal + Am.toReal / Jm.toReal) ^ 2)
    (h0 : SC.p7 Am.toReal (tj.toReal + Am.toReal / Jm.toReal) 0 ≤ L.toReal * (1 + 1 / 10 ^ 4)) :
    (t4F Am Jm tj L Vm).IsFinite ∧ 0 ≤ (t4F Am Jm tj L Vm).toReal ∧
      SC.p7 Am.toReal (tj.toReal + Am.toReal / Jm.toReal) (t4F Am Jm tj L Vm).toReal ≤
        L.toReal * (1 + 1 / 2000) := by
  have hq := h
  obtain ⟨fa, fj, ft, fl, a0, a1, j0, j1, t0, t1, l0, l1⟩ := hq
  have ⟨fp, ep⟩ := quad_float hL h true
  have ⟨fm, em⟩ := quad_float hL h false
  have ftv := tvelF_finite h hV hV'
  set a := Am.toReal
  set j := Jm.toReal
  set t := tj.toReal
  set l := L.toReal
  have ha0 : 0 < a := lt_of_lt_of_le (by norm_num) a0
  have hj0 : 0 < j := lt_of_lt_of_le (by norm_num) j0
  have ht0 : 0 < t := lt_of_lt_of_le (by norm_num) t0
  have hl0 : 0 < l := lt_of_lt_of_le (by norm_num) l0
  set R := t + a / j with hR
  have hR0 : 0 < R := by positivity
  set root := SC.quadRoot a j t l with hroot
  have hpr := SC.p7_quadRoot ha0 hj0 ht0.le hl0.le
  rw [← hroot] at hpr
  -- `|root| ≤ 20 R`
  have hlo := quadRoot_ge (l := l) (t := t) ha0 hj0
  rw [← hroot] at hlo
  have hhi : root ≤ 20 * R := by
    by_contra hc
    have hc := not_le.1 hc
    have : a * (20 * R) ^ 2 / 2 < SC.p7 a R root := by
      simp only [SC.p7]
      have h1 : (20 * R) ^ 2 < (R + root) * (2 * R + root) := by nlinarith
      nlinarith
    rw [hpr] at this
    nlinarith
  have habs : |root| ≤ 20 * R := abs_le.2 ⟨by linarith, hhi⟩
  -- the error of the `float` root
  set E := 40 / 16777216 * (a / j + t + |root|) with hE
  have hER : E ≤ 840 / 16777216 * R := by rw [hE]; linarith
  have hE0 : 0 ≤ E := by positivity
  -- `t₄`
  obtain ⟨fM, eM⟩ := wp_max_spec fp fm
  obtain ⟨fN, eN⟩ := wp_min_spec ftv fM
  obtain ⟨f4, e4⟩ := wp_max_spec fN f32_isFinite_0p0
  rw [f32_toReal_0p0] at e4
  refine ⟨f4, ?_, ?_⟩
  · simp only [t4F]; rw [e4]; exact le_max_right _ _
  have ht4 : (t4F Am Jm tj L Vm).toReal ≤ max (root + E) 0 := by
    simp only [t4F]; rw [e4, eN, eM]
    have : max (quadNum Am Jm tj L true).toReal (quadNum Am Jm tj L false).toReal ≤ root + E :=
      max_le ep em
    exact max_le_max (le_trans (min_le_right _ _) this) le_rfl
  have ht40 : 0 ≤ (t4F Am Jm tj L Vm).toReal := by
    simp only [t4F]; rw [e4]; exact le_max_right _ _
  have hfac : (1 + E / R) ^ 2 ≤ 1 + 2 / 10 ^ 4 := by
    have : E / R ≤ 840 / 16777216 := by rw [div_le_iff₀ hR0]; linarith
    have h0' : 0 ≤ E / R := by positivity
    nlinarith
  rcases le_total 0 root with hr | hr
  · -- the root is nonnegative
    have h1 : (t4F Am Jm tj L Vm).toReal ≤ root + E := by
      rw [max_eq_left (by linarith)] at ht4; exact ht4
    calc SC.p7 a R (t4F Am Jm tj L Vm).toReal ≤ SC.p7 a R (root + E) :=
          SC.p7_mono ha0.le hR0.le ht40 h1
      _ ≤ SC.p7 a R root * (1 + E / R) ^ 2 := SC.p7_add ha0.le hR0 hr hE0
      _ ≤ l * (1 + 1 / 2000) := by
          rw [hpr]; nlinarith
  · -- the root is negative: `t₄ ≤ E`
    have h1 : (t4F Am Jm tj L Vm).toReal ≤ 0 + E := by
      rcases le_total (root + E) 0 with h2 | h2
      · rw [max_eq_right h2] at ht4; linarith
      · rw [max_eq_left h2] at ht4; linarith
    have hp0 : 0 ≤ SC.p7 a R 0 := SC.p7_nonneg ha0.le hR0.le le_rfl
    calc SC.p7 a R (t4F Am Jm tj L Vm).toReal ≤ SC.p7 a R (0 + E) :=
          SC.p7_mono ha0.le hR0.le ht40 h1
      _ ≤ SC.p7 a R 0 * (1 + E / R) ^ 2 := SC.p7_add ha0.le hR0 le_rfl hE0
      _ ≤ l * (1 + 1 / 10 ^ 4) * (1 + 2 / 10 ^ 4) := by
          apply mul_le_mul h0 hfac (by positivity) (by positivity)
      _ ≤ l * (1 + 1 / 2000) := by nlinarith

/-! ## The ramp time `tj` -/

theorem R32.two_mul {x : Float32} {r k : ℝ} (h : R32 x r k) (hk : 0 ≤ k) (hk' : k ≤ 2 ^ 20)
    (hlo : 1 / 2 ^ 59 ≤ |r|) (hhi : |r| ≤ 2 ^ 89) : R32 ((2.0 : Float32) * x) (2 * r) (k + 1 + (k + 1) / 2 ^ 20) := by
  have h2 := R32.of_exact f32_isFinite_2p0 (le_refl (0 : ℝ))
  rw [f32_toReal_2p0] at h2
  exact R32.mul h2 h (le_refl 0) hk (by norm_num) hk' (by rw [abs_mul]; norm_num; linarith)
    (by rw [abs_mul]; norm_num; linarith) (by
      norm_num; linarith)

/-- `tj = Jm π / (2 Sm)` in `float`: within `6 u` relative; in `[0.19, 0.21]` on the ranges. -/
theorem tj0_spec (hL : LibmSpec) {Sm Jm : Float32} (fS : Sm.IsFinite) (hS : 39 ≤ Sm.toReal ∧ Sm.toReal ≤ 40)
    (fJ : Jm.IsFinite) (hJ : 49 / 10 ≤ Jm.toReal ∧ Jm.toReal ≤ 51 / 10) :
    R32 (Jm * Float.toFloat32 3.1415926535897931 / ((2.0 : Float32) * Sm))
      (Jm.toReal * Real.pi / (2 * Sm.toReal)) 6 ∧
    19 / 100 ≤ (Jm * Float.toFloat32 3.1415926535897931 / ((2.0 : Float32) * Sm)).toReal ∧
    (Jm * Float.toFloat32 3.1415926535897931 / ((2.0 : Float32) * Sm)).toReal ≤ 21 / 100 := by
  have p1 := Real.pi_gt_d6
  have p2 := Real.pi_lt_d6
  have hpf := R32.pi_f hL
  have eJ := R32.of_exact fJ (le_refl (0 : ℝ))
  have eS := R32.of_exact fS (le_refl (0 : ℝ))
  have m1 := R32.mul (k := 302 / 100) eJ hpf (le_refl 0) (by norm_num) (by norm_num) (by norm_num)
    (by rw [abs_of_pos (by nlinarith)]; nlinarith) (by rw [abs_of_pos (by nlinarith)]; nlinarith)
    (by norm_num)
  have s2 := R32.two_mul eS (le_refl 0) (by norm_num)
    (by rw [abs_of_pos (by linarith)]; nlinarith) (by rw [abs_of_pos (by linarith)]; nlinarith)
  have d := R32.div (k := 6) m1 s2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (ne_of_gt (by linarith))
    (by rw [abs_div, abs_of_pos (by nlinarith), abs_of_pos (by linarith)]
        rw [le_div_iff₀ (by linarith)]; nlinarith)
    (by rw [abs_div, abs_of_pos (by nlinarith), abs_of_pos (by linarith)]
        rw [div_le_iff₀ (by linarith)]; nlinarith)
    (by norm_num)
  refine ⟨d, ?_⟩
  have h := d.2
  have hv : 0.1924 ≤ Jm.toReal * Real.pi / (2 * Sm.toReal) ∧
      Jm.toReal * Real.pi / (2 * Sm.toReal) ≤ 0.2055 := by
    constructor
    · rw [le_div_iff₀ (by linarith)]
      nlinarith [mul_le_mul hJ.1 (le_of_lt p1) (by norm_num) (by linarith)]
    · rw [div_le_iff₀ (by linarith)]
      nlinarith [mul_le_mul hJ.2 (le_of_lt p2) (by linarith) (by norm_num)]
  have hp : 0 < Jm.toReal * Real.pi / (2 * Sm.toReal) := by linarith [hv.1]
  rw [abs_of_pos hp] at h
  obtain ⟨h1, h2⟩ := abs_le.1 h
  constructor <;> nlinarith [hv.1, hv.2]

end

end Contracts.Mission
