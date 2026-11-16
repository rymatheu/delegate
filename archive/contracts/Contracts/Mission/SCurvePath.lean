import Contracts.Mission.SCurveReal

/-!
# `SCurve::calculate_path` over the reals: the accelerating phase covers at most half the leg

`calculate_path(Sm, Jm, 0, Am, Vm, L)` (`L` is half the leg) returns the jerk `Jm`, the ramp time
`tj` and the times `t2 = t6`, `t4`. With `A = Jm (tj + t2)` and `R = 2 tj + t2`, the accelerating phase
covers `P₇ = A (R + t₄)(2R + t₄)/2` (`SC.node_7_eq`). Each branch keeps `P₇ ≤ L`:

* `p7_quad_root`: the time at constant acceleration is at most the positive root of
  `P₇(t₄) = L` (the closed form of the code, `quadRoot`);
* `p7_cubic_root`: the reduced acceleration is at most the Cardano root of `A (tj + A/Jm)² = L`
  (`cubicRoot`);
* `p7_short`: on short legs `tj⁴ ≤ L π / (8 Sm)` and `Jm = 2 Sm tj / π`, so `4 Jm tj³ ≤ L`.
-/

namespace Contracts.Mission.SC

open Real

noncomputable section

/-- The distance of the accelerating phase. -/
def p7 (A R t4 : ℝ) : ℝ := A * (R + t4) * (2 * R + t4) / 2

/-- The code's positive root of `p7 Am (tj + Am/Jm) t₄ = L` (with `V0 = 0`). -/
def quadRoot (Am Jm tj L : ℝ) : ℝ :=
  (Am ^ 2 * (-3 / 2) + sqrt (Am ^ 4 / 4 + Am ^ 2 * Jm ^ 2 * tj ^ 2 / 4 + Am * Jm ^ 2 * L * 2 +
    Am ^ 3 * Jm * tj / 2) - Am * Jm * tj * (3 / 2)) / (Am * Jm)

theorem p7_quadRoot {Am Jm tj L : ℝ} (hA : 0 < Am) (hJ : 0 < Jm) (htj : 0 ≤ tj) (hL : 0 ≤ L) :
    p7 Am (tj + Am / Jm) (quadRoot Am Jm tj L) = L := by
  have hq : 0 < Am * Jm := mul_pos hA hJ
  have hD : 0 ≤ Am ^ 4 / 4 + Am ^ 2 * Jm ^ 2 * tj ^ 2 / 4 + Am * Jm ^ 2 * L * 2 +
      Am ^ 3 * Jm * tj / 2 := by positivity
  have hs := Real.sq_sqrt hD
  simp only [p7, quadRoot]
  generalize sqrt (Am ^ 4 / 4 + Am ^ 2 * Jm ^ 2 * tj ^ 2 / 4 + Am * Jm ^ 2 * L * 2 +
      Am ^ 3 * Jm * tj / 2) = r at hs ⊢
  have key : Am * (tj + Am / Jm + (Am ^ 2 * (-3 / 2) + r - Am * Jm * tj * (3 / 2)) / (Am * Jm)) *
      (2 * (tj + Am / Jm) + (Am ^ 2 * (-3 / 2) + r - Am * Jm * tj * (3 / 2)) / (Am * Jm)) / 2 - L =
      Am * (r ^ 2 - (Am ^ 4 / 4 + Am ^ 2 * Jm ^ 2 * tj ^ 2 / 4 + Am * Jm ^ 2 * L * 2 +
        Am ^ 3 * Jm * tj / 2)) / (2 * (Am * Jm) ^ 2) := by
    field_simp
    ring
  rw [hs, sub_self, mul_zero, zero_div, sub_eq_zero] at key
  exact key

theorem p7_mono {A R t t' : ℝ} (hA : 0 ≤ A) (hR : 0 ≤ R) (ht : 0 ≤ t) (htt : t ≤ t') :
    p7 A R t ≤ p7 A R t' := by
  simp only [p7]
  have h1 : (R + t) * (2 * R + t) ≤ (R + t') * (2 * R + t') := by nlinarith
  have := mul_le_mul_of_nonneg_left h1 hA
  nlinarith

/-- **The constant-acceleration branch**: a time at constant acceleration in `[0, quadRoot]` keeps
the accelerating phase within `L`. -/
theorem p7_quad_root {Am Jm tj L t4 : ℝ} (hA : 0 < Am) (hJ : 0 < Jm) (htj : 0 ≤ tj) (hL : 0 ≤ L)
    (h0 : 0 ≤ t4) (h1 : t4 ≤ quadRoot Am Jm tj L) :
    p7 Am (tj + Am / Jm) t4 ≤ L := by
  rw [← p7_quadRoot hA hJ htj hL]
  exact p7_mono hA.le (by positivity) h0 h1

/-- The code's Cardano root of `A (tj + A/Jm)² = L` (with `V0 = 0`). -/
def cubicRoot (Jm tj L : ℝ) : ℝ :=
  let Y := Jm ^ 2 * tj ^ 2 / 9
  let X := -(Jm ^ 2) * L / 2 + Jm ^ 3 * tj ^ 3 * (8 / 27) - Jm * tj * (Jm ^ 2 * tj ^ 2) / 3
  let Q := sqrt (X ^ 2 - Y ^ 3) - X
  Jm * tj * (-2 / 3) + Y / Q ^ ((1 : ℝ) / 3) + Q ^ ((1 : ℝ) / 3)

theorem cubicRoot_eq {Jm tj L : ℝ} (hJ : 0 < Jm) (htj : 0 ≤ tj) (hL : 0 < L) :
    let A := cubicRoot Jm tj L
    A * (tj + A / Jm) ^ 2 = L := by
  intro A
  set p := Jm * tj with hp
  set Y := Jm ^ 2 * tj ^ 2 / 9 with hY
  set K := Jm ^ 2 * L / 2 + p ^ 3 / 27 with hK
  have hX : -(Jm ^ 2) * L / 2 + Jm ^ 3 * tj ^ 3 * (8 / 27) - Jm * tj * (Jm ^ 2 * tj ^ 2) / 3 = -K := by
    simp only [hK, hp]; ring
  have hKY : 0 ≤ K ^ 2 - Y ^ 3 := by
    have : K ^ 2 - Y ^ 3 = Jm ^ 4 * L ^ 2 / 4 + Jm ^ 2 * L * p ^ 3 / 27 := by
      simp only [hK, hY, hp]; ring
    rw [this]; positivity
  have hK0 : 0 < K := by positivity
  set S := sqrt (K ^ 2 - Y ^ 3) with hS
  have hS2 : S ^ 2 = K ^ 2 - Y ^ 3 := Real.sq_sqrt hKY
  have hS0 : 0 ≤ S := Real.sqrt_nonneg _
  set Q := K + S with hQ
  have hQ0 : 0 < Q := by linarith
  have hA : A = Jm * tj * (-2 / 3) + Y / Q ^ ((1 : ℝ) / 3) + Q ^ ((1 : ℝ) / 3) := by
    simp only [A, cubicRoot]
    rw [hX, neg_sq, sub_neg_eq_add, add_comm (sqrt _) K, ← hY]
  set c := Q ^ ((1 : ℝ) / 3) with hc
  have hc0 : 0 < c := Real.rpow_pos_of_pos hQ0 _
  have hc3 : c ^ 3 = Q := by
    rw [hc, ← Real.rpow_natCast, ← Real.rpow_mul hQ0.le]; norm_num
  -- `Q · (K - S) = Y³`
  have hQc : Q * (K - S) = Y ^ 3 := by rw [hQ]; nlinarith [hS2]
  rw [hA]
  have hY0 : Y = p ^ 2 / 9 := by simp only [hY, hp]; ring
  have key : (Jm * tj * (-2 / 3) + Y / c + c) * (tj + (Jm * tj * (-2 / 3) + Y / c + c) / Jm) ^ 2 * Jm ^ 2 =
      (c ^ 3 + Y ^ 3 / c ^ 3 - 2 * p ^ 3 / 27) := by
    rw [hY0]; field_simp; rw [hp]; ring
  have hsum : c ^ 3 + Y ^ 3 / c ^ 3 = 2 * K := by
    rw [hc3, ← hQc]; field_simp; rw [hQ]; ring
  have : (Jm * tj * (-2 / 3) + Y / c + c) * (tj + (Jm * tj * (-2 / 3) + Y / c + c) / Jm) ^ 2 * Jm ^ 2 =
      L * Jm ^ 2 := by
    rw [key, hsum, hK]; ring
  have hJ2 : Jm ^ 2 ≠ 0 := by positivity
  exact mul_right_cancel₀ hJ2 this

/-- **The cubic branch**: an acceleration in `[0, cubicRoot]` keeps the accelerating phase
(`t₂ = A/Jm - tj`, `t₄ = 0`) within `L`. -/
theorem p7_cubic_root {Jm tj L A : ℝ} (hJ : 0 < Jm) (htj : 0 ≤ tj) (hL : 0 < L)
    (h0 : 0 ≤ A) (h1 : A ≤ cubicRoot Jm tj L) : A * (tj + A / Jm) ^ 2 ≤ L := by
  have e := cubicRoot_eq hJ htj hL
  simp only at e
  rw [← e]
  have h2 : 0 ≤ tj + A / Jm := by positivity
  have h3 : tj + A / Jm ≤ tj + cubicRoot Jm tj L / Jm := by gcongr
  exact mul_le_mul h1 (pow_le_pow_left₀ h2 h3 2) (sq_nonneg _) (h0.trans h1)

theorem p7_nonneg {A R t : ℝ} (hA : 0 ≤ A) (hR : 0 ≤ R) (ht : 0 ≤ t) : 0 ≤ p7 A R t := by
  simp only [p7]; positivity

/-- `p7` grows by at most `(1 + E/R)²` when the constant-acceleration time grows by `E`. -/
theorem p7_add {A R t E : ℝ} (hA : 0 ≤ A) (hR : 0 < R) (ht : 0 ≤ t) (hE : 0 ≤ E) :
    p7 A R (t + E) ≤ p7 A R t * (1 + E / R) ^ 2 := by
  simp only [p7]
  have h1 : R + (t + E) ≤ (R + t) * (1 + E / R) := by
    have : (R + t) * (1 + E / R) = R + t + E + t * E / R := by field_simp; ring
    rw [this]; have : 0 ≤ t * E / R := by positivity
    linarith
  have h2 : 2 * R + (t + E) ≤ (2 * R + t) * (1 + E / R) := by
    have : (2 * R + t) * (1 + E / R) = 2 * R + t + 2 * E + t * E / R := by field_simp; ring
    rw [this]; have : 0 ≤ t * E / R := by positivity
    linarith
  have h3 := mul_le_mul h1 h2 (by positivity) (by positivity)
  have h4 := mul_le_mul_of_nonneg_left h3 hA
  have : A * ((R + t) * (1 + E / R)) * ((2 * R + t) * (1 + E / R)) / 2 =
      A * (R + t) * (2 * R + t) / 2 * (1 + E / R) ^ 2 := by ring
  nlinarith

/-- `p7` is monotone in the acceleration and in `R`. -/
theorem p7_mono_AR {A A' R R' t : ℝ} (hA : 0 ≤ A) (hR : 0 ≤ R) (ht : 0 ≤ t) (hAA : A ≤ A')
    (hRR : R ≤ R') : p7 A R t ≤ p7 A' R' t := by
  simp only [p7]
  have h1 : (R + t) * (2 * R + t) ≤ (R' + t) * (2 * R' + t) :=
    mul_le_mul (by linarith) (by linarith) (by positivity) (by linarith)
  have := mul_le_mul hAA h1 (by positivity) (hA.trans hAA)
  nlinarith

/-- **The short branch**: with `Jm = 2 Sm tj / π` and `tj⁴ ≤ L π / (8 Sm)`, the accelerating phase
(`t₂ = t₄ = 0`, `A = Jm tj`) covers `4 Jm tj³ ≤ L`. -/
theorem p7_short {Sm tj L : ℝ} (hS : 0 < Sm) (h : tj ^ 4 ≤ L * π / (8 * Sm)) :
    p7 (2 * Sm * tj / π * tj) (2 * tj) 0 ≤ L := by
  simp only [p7]
  rw [le_div_iff₀ (by positivity)] at h
  have hp := pi_pos
  field_simp
  nlinarith

end

end Contracts.Mission.SC
