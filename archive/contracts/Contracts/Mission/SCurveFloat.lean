import Contracts.Mission.WPHelp
import Contracts.Mission.SCurvePath

/-!
# `SCurve::calculate_path` in `float`

The constant-acceleration time `t₄` of `calculate_path` is computed from the closed form of the
positive root of `p7 = L` (`SC.quadRoot`). `quad_float`: the `float` evaluation is within
`60 u (a/j + t + |root|)` of the root, a bound that scales with the leg (`u = 2⁻²⁴`).
-/

namespace Contracts.Mission

open Float.Model UnpackedFloat AC_WPNav_lib

noncomputable section

theorem lo_mul {x y xl yl : ℝ} (hx : xl ≤ x) (hy : yl ≤ y) (hxl : 0 ≤ xl) (hyl : 0 ≤ yl) :
    xl * yl ≤ x * y := mul_le_mul hx hy hyl (hxl.trans hx)

theorem hi_mul {x y xh yh : ℝ} (hx : x ≤ xh) (hy : y ≤ yh) (hx0 : 0 ≤ x) (hy0 : 0 ≤ y) :
    x * y ≤ xh * yh := mul_le_mul hx hy hy0 (hx0.trans hx)

/-- The `float` expression of `calculate_path`'s root (`sgn = +1` or `-1`), with `V0 = 0`. -/
def quadNum (Am Jm tj L : Float32) (plus : Bool) : Float32 :=
  let V0 : Float32 := 0.0
  let X := (Am * Am * Am * Am) * ((1.0 : Float32) / (4.0 : Float32)) + (Jm * Jm) * (V0 * V0) +
    (Am * Am) * (Jm * Jm) * (tj * tj) * ((1.0 : Float32) / (4.0 : Float32)) +
    Am * (Jm * Jm) * L * (2.0 : Float32) - (Am * Am) * Jm * V0 +
    (Am * Am * Am) * Jm * tj * ((1.0 : Float32) / (2.0 : Float32)) - Am * (Jm * Jm) * V0 * tj
  if plus then
    ((Am * Am) * (-(3.0 : Float32) / (2.0 : Float32)) + safe_sqrt_float X - Jm * V0 -
      Am * Jm * tj * ((3.0 : Float32) / (2.0 : Float32))) / (Am * Jm)
  else
    ((Am * Am) * (-(3.0 : Float32) / (2.0 : Float32)) - safe_sqrt_float X - Jm * V0 -
      Am * Jm * tj * ((3.0 : Float32) / (2.0 : Float32))) / (Am * Jm)

theorem f32_quarter : (1.0 : Float32) / (4.0 : Float32) = 0.25 := by decide +kernel
theorem f32_half' : (1.0 : Float32) / (2.0 : Float32) = 0.5 := by decide +kernel
theorem f32_m3h : (-(3.0 : Float32)) / (2.0 : Float32) = -1.5 := by decide +kernel
theorem f32_3h : (3.0 : Float32) / (2.0 : Float32) = 1.5 := by decide +kernel

/-- Exact inputs in the ranges of the S-curve's root. -/
structure QIn (Am Jm tj L : Float32) : Prop where
  fa : Am.IsFinite
  fj : Jm.IsFinite
  ft : tj.IsFinite
  fl : L.IsFinite
  a0 : 1 / 2 ^ 12 ≤ Am.toReal
  a1 : Am.toReal ≤ 4
  j0 : 1 / 2 ^ 4 ≤ Jm.toReal
  j1 : Jm.toReal ≤ 8
  t0 : 1 / 2 ^ 9 ≤ tj.toReal
  t1 : tj.toReal ≤ 1
  l0 : 1 / 2 ^ 23 ≤ L.toReal
  l1 : L.toReal ≤ 4

/-- The exact value under the root's square root. -/
def quadX (a j t l : ℝ) : ℝ := a ^ 4 / 4 + a ^ 2 * j ^ 2 * t ^ 2 / 4 + a * j ^ 2 * l * 2 + a ^ 3 * j * t / 2

set_option maxHeartbeats 4000000 in
/-- The `float` value under the square root: within `9.1 u` relative. -/
theorem quadX_float {Am Jm tj L : Float32} (h : QIn Am Jm tj L) :
    R32 ((Am * Am * Am * Am) * ((1.0 : Float32) / (4.0 : Float32)) + (Jm * Jm) * ((0.0 : Float32) * 0.0) +
      (Am * Am) * (Jm * Jm) * (tj * tj) * ((1.0 : Float32) / (4.0 : Float32)) +
      Am * (Jm * Jm) * L * (2.0 : Float32) - (Am * Am) * Jm * (0.0 : Float32) +
      (Am * Am * Am) * Jm * tj * ((1.0 : Float32) / (2.0 : Float32)) - Am * (Jm * Jm) * (0.0 : Float32) * tj)
      (quadX Am.toReal Jm.toReal tj.toReal L.toReal) (91 / 10) := by
  obtain ⟨fa, fj, ft, fl, a0, a1, j0, j1, t0, t1, l0, l1⟩ := h
  rw [f32_quarter, f32_half']
  set a := Am.toReal
  set j := Jm.toReal
  set t := tj.toReal
  set l := L.toReal
  have ha0 : 0 < a := lt_of_lt_of_le (by norm_num) a0
  have hj0 : 0 < j := lt_of_lt_of_le (by norm_num) j0
  have ht0 : 0 < t := lt_of_lt_of_le (by norm_num) t0
  have hl0 : 0 < l := lt_of_lt_of_le (by norm_num) l0
  have eA := R32.of_exact fa (le_refl (0 : ℝ))
  have eJ := R32.of_exact fj (le_refl (0 : ℝ))
  have eT := R32.of_exact ft (le_refl (0 : ℝ))
  have eL := R32.of_exact fl (le_refl (0 : ℝ))
  have eQ := R32.of_exact f32_isFinite_0p25 (le_refl (0 : ℝ))
  have eH := R32.of_exact f32_isFinite_0p5 (le_refl (0 : ℝ))
  have e2 := R32.of_exact f32_isFinite_2p0 (le_refl (0 : ℝ))
  rw [f32_toReal_0p25] at eQ
  rw [f32_toReal_0p5] at eH
  rw [f32_toReal_2p0] at e2
  -- magnitudes
  have ba2 : 1 / 2 ^ 24 ≤ a * a ∧ a * a ≤ 16 :=
    ⟨by have := lo_mul a0 a0 (by norm_num) (by norm_num); norm_num at this ⊢; linarith,
     by have := hi_mul a1 a1 ha0.le ha0.le; norm_num at this ⊢; linarith⟩
  have ba3 : 1 / 2 ^ 36 ≤ a * a * a ∧ a * a * a ≤ 64 :=
    ⟨by have := lo_mul ba2.1 a0 (by norm_num) (by norm_num); norm_num at this ⊢; linarith,
     by have := hi_mul ba2.2 a1 (by positivity) ha0.le; norm_num at this ⊢; linarith⟩
  have ba4 : 1 / 2 ^ 48 ≤ a * a * a * a ∧ a * a * a * a ≤ 256 :=
    ⟨by have := lo_mul ba3.1 a0 (by norm_num) (by norm_num); norm_num at this ⊢; linarith,
     by have := hi_mul ba3.2 a1 (by positivity) ha0.le; norm_num at this ⊢; linarith⟩
  have bj2 : 1 / 2 ^ 8 ≤ j * j ∧ j * j ≤ 64 :=
    ⟨by have := lo_mul j0 j0 (by norm_num) (by norm_num); norm_num at this ⊢; linarith,
     by have := hi_mul j1 j1 hj0.le hj0.le; norm_num at this ⊢; linarith⟩
  have bt2 : 1 / 2 ^ 18 ≤ t * t ∧ t * t ≤ 1 :=
    ⟨by have := lo_mul t0 t0 (by norm_num) (by norm_num); norm_num at this ⊢; linarith,
     by have := hi_mul t1 t1 ht0.le ht0.le; norm_num at this ⊢; linarith⟩
  have baj : 1 / 2 ^ 32 ≤ a * a * (j * j) ∧ a * a * (j * j) ≤ 1024 :=
    ⟨by have := lo_mul ba2.1 bj2.1 (by norm_num) (by norm_num); norm_num at this ⊢; linarith,
     by have := hi_mul ba2.2 bj2.2 (by positivity) (by positivity); norm_num at this ⊢; linarith⟩
  have bajt : 1 / 2 ^ 50 ≤ a * a * (j * j) * (t * t) ∧ a * a * (j * j) * (t * t) ≤ 1024 :=
    ⟨by have := lo_mul baj.1 bt2.1 (by norm_num) (by norm_num); norm_num at this ⊢; linarith,
     by have := hi_mul baj.2 bt2.2 (by positivity) (by positivity); norm_num at this ⊢; linarith⟩
  have bajj : 1 / 2 ^ 20 ≤ a * (j * j) ∧ a * (j * j) ≤ 256 :=
    ⟨by have := lo_mul a0 bj2.1 (by norm_num) (by norm_num); norm_num at this ⊢; linarith,
     by have := hi_mul a1 bj2.2 ha0.le (by positivity); norm_num at this ⊢; linarith⟩
  have bajjl : 1 / 2 ^ 43 ≤ a * (j * j) * l ∧ a * (j * j) * l ≤ 1024 :=
    ⟨by have := lo_mul bajj.1 l0 (by norm_num) (by norm_num); norm_num at this ⊢; linarith,
     by have := hi_mul bajj.2 l1 (by positivity) hl0.le; norm_num at this ⊢; linarith⟩
  have ba3j : 1 / 2 ^ 40 ≤ a * a * a * j ∧ a * a * a * j ≤ 512 :=
    ⟨by have := lo_mul ba3.1 j0 (by norm_num) (by norm_num); norm_num at this ⊢; linarith,
     by have := hi_mul ba3.2 j1 (by positivity) hj0.le; norm_num at this ⊢; linarith⟩
  have ba3jt : 1 / 2 ^ 49 ≤ a * a * a * j * t ∧ a * a * a * j * t ≤ 512 :=
    ⟨by have := lo_mul ba3j.1 t0 (by norm_num) (by norm_num); norm_num at this ⊢; linarith,
     by have := hi_mul ba3j.2 t1 (by positivity) ht0.le; norm_num at this ⊢; linarith⟩
  have bq : 1 / 2 ^ 50 ≤ a * a * a * a * (1 / 4) ∧ a * a * a * a * (1 / 4) ≤ 64 :=
    ⟨by linarith [ba4.1], by linarith [ba4.2]⟩
  have bq2 : 1 / 2 ^ 52 ≤ a * a * (j * j) * (t * t) * (1 / 4) ∧ a * a * (j * j) * (t * t) * (1 / 4) ≤ 256 :=
    ⟨by linarith [bajt.1], by linarith [bajt.2]⟩
  have bq3 : 1 / 2 ^ 43 ≤ a * (j * j) * l * 2 ∧ a * (j * j) * l * 2 ≤ 2048 :=
    ⟨by linarith [bajjl.1], by linarith [bajjl.2]⟩
  have bq4 : 1 / 2 ^ 50 ≤ a * a * a * j * t * (1 / 2) ∧ a * a * a * j * t * (1 / 2) ≤ 256 :=
    ⟨by linarith [ba3jt.1], by linarith [ba3jt.2]⟩
  have pAA := R32.mul (k := 101/100) eA eA (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by rw [abs_of_pos (lt_of_lt_of_le (by norm_num) ba2.1)]; exact le_trans (by norm_num) ba2.1)
    (by rw [abs_of_pos (lt_of_lt_of_le (by norm_num) ba2.1)]; exact le_trans ba2.2 (by norm_num))
    (by norm_num)
  have pAAA := R32.mul (k := 203/100) pAA eA (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by rw [abs_of_pos (lt_of_lt_of_le (by norm_num) ba3.1)]; exact le_trans (by norm_num) ba3.1)
    (by rw [abs_of_pos (lt_of_lt_of_le (by norm_num) ba3.1)]; exact le_trans ba3.2 (by norm_num))
    (by norm_num)
  have pA4 := R32.mul (k := 305/100) pAAA eA (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by rw [abs_of_pos (lt_of_lt_of_le (by norm_num) ba4.1)]; exact le_trans (by norm_num) ba4.1)
    (by rw [abs_of_pos (lt_of_lt_of_le (by norm_num) ba4.1)]; exact le_trans ba4.2 (by norm_num))
    (by norm_num)
  have tA := R32.mul (k := 406/100) pA4 eQ (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by rw [abs_of_pos (lt_of_lt_of_le (by norm_num) bq.1)]; exact le_trans (by norm_num) bq.1)
    (by rw [abs_of_pos (lt_of_lt_of_le (by norm_num) bq.1)]; exact le_trans bq.2 (by norm_num))
    (by norm_num)
  have pJJ := R32.mul (k := 101/100) eJ eJ (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by rw [abs_of_pos (lt_of_lt_of_le (by norm_num) bj2.1)]; exact le_trans (by norm_num) bj2.1)
    (by rw [abs_of_pos (lt_of_lt_of_le (by norm_num) bj2.1)]; exact le_trans bj2.2 (by norm_num))
    (by norm_num)
  have pAAJJ := R32.mul (k := 303/100) pAA pJJ (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by rw [abs_of_pos (lt_of_lt_of_le (by norm_num) baj.1)]; exact le_trans (by norm_num) baj.1)
    (by rw [abs_of_pos (lt_of_lt_of_le (by norm_num) baj.1)]; exact le_trans baj.2 (by norm_num))
    (by norm_num)
  have pTT := R32.mul (k := 101/100) eT eT (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by rw [abs_of_pos (lt_of_lt_of_le (by norm_num) bt2.1)]; exact le_trans (by norm_num) bt2.1)
    (by rw [abs_of_pos (lt_of_lt_of_le (by norm_num) bt2.1)]; exact le_trans bt2.2 (by norm_num))
    (by norm_num)
  have pAAJJTT := R32.mul (k := 505/100) pAAJJ pTT (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by rw [abs_of_pos (lt_of_lt_of_le (by norm_num) bajt.1)]; exact le_trans (by norm_num) bajt.1)
    (by rw [abs_of_pos (lt_of_lt_of_le (by norm_num) bajt.1)]; exact le_trans bajt.2 (by norm_num))
    (by norm_num)
  have tB := R32.mul (k := 606/100) pAAJJTT eQ (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by rw [abs_of_pos (lt_of_lt_of_le (by norm_num) bq2.1)]; exact le_trans (by norm_num) bq2.1)
    (by rw [abs_of_pos (lt_of_lt_of_le (by norm_num) bq2.1)]; exact le_trans bq2.2 (by norm_num))
    (by norm_num)
  have pAJJ := R32.mul (k := 202/100) eA pJJ (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by rw [abs_of_pos (lt_of_lt_of_le (by norm_num) bajj.1)]; exact le_trans (by norm_num) bajj.1)
    (by rw [abs_of_pos (lt_of_lt_of_le (by norm_num) bajj.1)]; exact le_trans bajj.2 (by norm_num))
    (by norm_num)
  have pAJJL := R32.mul (k := 303/100) pAJJ eL (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by rw [abs_of_pos (lt_of_lt_of_le (by norm_num) bajjl.1)]; exact le_trans (by norm_num) bajjl.1)
    (by rw [abs_of_pos (lt_of_lt_of_le (by norm_num) bajjl.1)]; exact le_trans bajjl.2 (by norm_num))
    (by norm_num)
  have tC := R32.mul (k := 404/100) pAJJL e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by rw [abs_of_pos (lt_of_lt_of_le (by norm_num) bq3.1)]; exact le_trans (by norm_num) bq3.1)
    (by rw [abs_of_pos (lt_of_lt_of_le (by norm_num) bq3.1)]; exact le_trans bq3.2 (by norm_num))
    (by norm_num)
  have pAAAJ := R32.mul (k := 304/100) pAAA eJ (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by rw [abs_of_pos (lt_of_lt_of_le (by norm_num) ba3j.1)]; exact le_trans (by norm_num) ba3j.1)
    (by rw [abs_of_pos (lt_of_lt_of_le (by norm_num) ba3j.1)]; exact le_trans ba3j.2 (by norm_num))
    (by norm_num)
  have pAAAJT := R32.mul (k := 405/100) pAAAJ eT (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by rw [abs_of_pos (lt_of_lt_of_le (by norm_num) ba3jt.1)]; exact le_trans (by norm_num) ba3jt.1)
    (by rw [abs_of_pos (lt_of_lt_of_le (by norm_num) ba3jt.1)]; exact le_trans ba3jt.2 (by norm_num))
    (by norm_num)
  have tD := R32.mul (k := 506/100) pAAAJT eH (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by rw [abs_of_pos (lt_of_lt_of_le (by norm_num) bq4.1)]; exact le_trans (by norm_num) bq4.1)
    (by rw [abs_of_pos (lt_of_lt_of_le (by norm_num) bq4.1)]; exact le_trans bq4.2 (by norm_num))
    (by norm_num)
  -- the zero terms
  have f00 := Float32.mul_zero_val f32_isFinite_0p0 f32_isFinite_0p0 f32_toReal_0p0
  have z1 := Float32.mul_zero_val pJJ.1 f00.1 f00.2
  have baaj : 1 / 2 ^ 28 ≤ a * a * j ∧ a * a * j ≤ 128 :=
    ⟨by have := lo_mul ba2.1 j0 (by norm_num) (by norm_num); norm_num at this ⊢; linarith,
     by have := hi_mul ba2.2 j1 (by positivity) hj0.le; norm_num at this ⊢; linarith⟩
  have pAAJ := R32.mul (k := 203/100) pAA eJ (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by rw [abs_of_pos (lt_of_lt_of_le (by norm_num) baaj.1)]; exact le_trans (by norm_num) baaj.1)
    (by rw [abs_of_pos (lt_of_lt_of_le (by norm_num) baaj.1)]; exact le_trans baaj.2 (by norm_num))
    (by norm_num)
  have z2 := Float32.mul_zero_val pAAJ.1 f32_isFinite_0p0 f32_toReal_0p0
  have z3a := Float32.mul_zero_val pAJJ.1 f32_isFinite_0p0 f32_toReal_0p0
  have z3 := Float32.mul_exact z3a.1 ft f32_isFinite_0p0 (by rw [z3a.2, f32_toReal_0p0, zero_mul])
  rw [f32_toReal_0p0] at z3
  -- the sums
  have x1 := Float32.add_zero_val tA.1 z1.1 z1.2
  have sA : R32 (Am * Am * Am * Am * 0.25 + Jm * Jm * (0.0 * 0.0)) (a * a * a * a * (1 / 4)) (606 / 100) :=
    (R32.mono tA (by norm_num)).congr_x x1.1 x1.2
  have sAB := R32.add_pos (k := 707 / 100) sA (R32.mono tB (by norm_num)) (by linarith [bq.1])
    (by linarith [bq2.1]) (by norm_num) (by linarith [bq.1, bq2.1]) (by linarith [bq.2, bq2.2])
    (by norm_num)
  have sABC := R32.add_pos (k := 808 / 100) sAB (R32.mono tC (by norm_num))
    (by linarith [bq.1, bq2.1]) (by linarith [bq3.1]) (by norm_num) (by linarith [bq.1, bq2.1, bq3.1])
    (by linarith [bq.2, bq2.2, bq3.2]) (by norm_num)
  have x4 := Float32.sub_zero_val sABC.1 z2.1 z2.2
  have sABC' := sABC.congr_x x4.1 x4.2
  have sX := R32.add_pos (k := 909 / 100) sABC' (R32.mono tD (by norm_num))
    (by linarith [bq.1, bq2.1, bq3.1]) (by linarith [bq4.1]) (by norm_num)
    (by linarith [bq.1, bq2.1, bq3.1, bq4.1]) (by linarith [bq.2, bq2.2, bq3.2, bq4.2]) (by norm_num)
  have x6 := Float32.sub_zero_val sX.1 z3.1 z3.2
  have := (sX.congr_x x6.1 x6.2).mono (show (909 / 100 : ℝ) ≤ 91 / 10 by norm_num)
  have hq : a * a * a * a * (1 / 4) + a * a * (j * j) * (t * t) * (1 / 4) + a * (j * j) * l * 2 +
      a * a * a * j * t * (1 / 2) = quadX a j t l := by simp only [quadX]; ring
  rw [hq] at this
  exact this

/-- The exact square root and the root's closed form. -/
theorem quadRoot_eq (a j t l : ℝ) :
    SC.quadRoot a j t l = (a ^ 2 * (-3 / 2) + Real.sqrt (quadX a j t l) - a * j * t * (3 / 2)) / (a * j) := by
  simp only [SC.quadRoot, quadX]

set_option maxHeartbeats 20000000 in
/-- **The root of `calculate_path` in `float`**: both signs of the closed form are within
`40 u (a/j + t + |root|)` above the positive root. -/
theorem quad_float (hL : LibmSpec) {Am Jm tj L : Float32} (h : QIn Am Jm tj L) (plus : Bool) :
    (quadNum Am Jm tj L plus).IsFinite ∧
      (quadNum Am Jm tj L plus).toReal ≤ SC.quadRoot Am.toReal Jm.toReal tj.toReal L.toReal +
        40 / 16777216 * (Am.toReal / Jm.toReal + tj.toReal +
          |SC.quadRoot Am.toReal Jm.toReal tj.toReal L.toReal|) := by
  have hX := quadX_float h
  obtain ⟨fa, fj, ft, fl, a0, a1, j0, j1, t0, t1, l0, l1⟩ := h
  simp only [quadNum]
  rw [f32_m3h, f32_3h]
  set X := (Am * Am * Am * Am) * ((1.0 : Float32) / (4.0 : Float32)) + (Jm * Jm) * ((0.0 : Float32) * 0.0) +
    (Am * Am) * (Jm * Jm) * (tj * tj) * ((1.0 : Float32) / (4.0 : Float32)) +
    Am * (Jm * Jm) * L * (2.0 : Float32) - (Am * Am) * Jm * (0.0 : Float32) +
    (Am * Am * Am) * Jm * tj * ((1.0 : Float32) / (2.0 : Float32)) - Am * (Jm * Jm) * (0.0 : Float32) * tj
    with hXd
  set a := Am.toReal
  set j := Jm.toReal
  set t := tj.toReal
  set l := L.toReal
  have ha0 : 0 < a := lt_of_lt_of_le (by norm_num) a0
  have hj0 : 0 < j := lt_of_lt_of_le (by norm_num) j0
  have ht0 : 0 < t := lt_of_lt_of_le (by norm_num) t0
  have hl0 : 0 < l := lt_of_lt_of_le (by norm_num) l0
  set Xi := quadX a j t l with hXi
  have bX : a ^ 4 / 4 ≤ Xi ∧ Xi ≤ 3000 := by
    have h1 : a ^ 4 ≤ 256 := by nlinarith [pow_le_pow_left₀ ha0.le a1 4]
    have h2 : a ^ 2 * j ^ 2 * t ^ 2 ≤ 1024 := by
      have := hi_mul (hi_mul (pow_le_pow_left₀ ha0.le a1 2) (pow_le_pow_left₀ hj0.le j1 2)
        (by positivity) (by positivity)) (pow_le_pow_left₀ ht0.le t1 2) (by positivity) (by positivity)
      norm_num at this; linarith
    have h3 : a * j ^ 2 * l ≤ 1024 := by
      have := hi_mul (hi_mul a1 (pow_le_pow_left₀ hj0.le j1 2) ha0.le (by positivity)) l1
        (by positivity) hl0.le
      norm_num at this; linarith
    have h4 : a ^ 3 * j * t ≤ 512 := by
      have := hi_mul (hi_mul (pow_le_pow_left₀ ha0.le a1 3) j1 (by positivity) hj0.le) t1
        (by positivity) ht0.le
      norm_num at this; linarith
    constructor
    · simp only [hXi, quadX]; have : 0 ≤ a ^ 2 * j ^ 2 * t ^ 2 / 4 + a * j ^ 2 * l * 2 + a ^ 3 * j * t / 2 := by positivity
      linarith
    · simp only [hXi, quadX]; linarith
  have ba4 : 1 / 2 ^ 48 ≤ a ^ 4 := by
    have := pow_le_pow_left₀ (by norm_num) a0 4; norm_num at this ⊢; linarith
  -- the square root
  have hX0 : 0 ≤ X.toReal := by
    have := (abs_le.1 hX.2).1
    rw [abs_of_pos (by linarith : (0 : ℝ) < Xi)] at this
    nlinarith [bX.1]
  have hss := (wp_safe_sqrt hL hX.1).1 hX0
  rw [hss]
  have hS := R32.sqrt (k := 103 / 10) hX (by norm_num) (by norm_num)
    (by have := bX.1; have : (1 / 2 ^ 120 : ℝ) ≤ a ^ 4 / 4 := by linarith
        linarith) (by linarith [bX.2]) (by norm_num)
  set sq := Real.sqrt Xi with hsq
  have hsq0 : 0 < sq := Real.sqrt_pos.2 (by linarith [bX.1])
  -- the products
  have eA := R32.of_exact fa (le_refl (0 : ℝ))
  have eJ := R32.of_exact fj (le_refl (0 : ℝ))
  have eT := R32.of_exact ft (le_refl (0 : ℝ))
  have em := R32.of_exact f32_isFinite_m1p5 (le_refl (0 : ℝ))
  have ep := R32.of_exact f32_isFinite_1p5 (le_refl (0 : ℝ))
  rw [f32_toReal_m1p5] at em
  rw [f32_toReal_1p5] at ep
  have ba2 : 1 / 2 ^ 24 ≤ a * a ∧ a * a ≤ 16 :=
    ⟨by have := lo_mul a0 a0 (by norm_num) (by norm_num); norm_num at this ⊢; linarith,
     by have := hi_mul a1 a1 ha0.le ha0.le; norm_num at this ⊢; linarith⟩
  have baj : 1 / 2 ^ 16 ≤ a * j ∧ a * j ≤ 32 :=
    ⟨by have := lo_mul a0 j0 (by norm_num) (by norm_num); norm_num at this ⊢; linarith,
     by have := hi_mul a1 j1 ha0.le hj0.le; norm_num at this ⊢; linarith⟩
  have bajt : 1 / 2 ^ 25 ≤ a * j * t ∧ a * j * t ≤ 32 :=
    ⟨by have := lo_mul baj.1 t0 (by norm_num) (by norm_num); norm_num at this ⊢; linarith,
     by have := hi_mul baj.2 t1 (by positivity) ht0.le; norm_num at this ⊢; linarith⟩
  have pAA := R32.mul (k := 101/100) eA eA (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by rw [abs_of_pos (by positivity)]; exact le_trans (by norm_num) ba2.1)
    (by rw [abs_of_pos (by positivity)]; exact le_trans ba2.2 (by norm_num)) (by norm_num)
  have T1 := R32.mul (k := 203/100) pAA em (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by rw [abs_mul, abs_of_pos (by positivity)]; norm_num; linarith [ba2.1])
    (by rw [abs_mul, abs_of_pos (by positivity)]; norm_num; linarith [ba2.2]) (by norm_num)
  have pAJ := R32.mul (k := 101/100) eA eJ (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by rw [abs_of_pos (by positivity)]; exact le_trans (by norm_num) baj.1)
    (by rw [abs_of_pos (by positivity)]; exact le_trans baj.2 (by norm_num)) (by norm_num)
  have pAJT := R32.mul (k := 202/100) pAJ eT (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by rw [abs_of_pos (by positivity)]; exact le_trans (by norm_num) bajt.1)
    (by rw [abs_of_pos (by positivity)]; exact le_trans bajt.2 (by norm_num)) (by norm_num)
  have T3 := R32.mul (k := 303/100) pAJT ep (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by rw [abs_of_pos (by positivity)]; have := bajt.1; norm_num at this ⊢; linarith)
    (by rw [abs_of_pos (by positivity)]; have := bajt.2; norm_num at this ⊢; linarith) (by norm_num)
  have z := Float32.mul_zero_val fj f32_isFinite_0p0 f32_toReal_0p0
  -- the root's numerator and quotient, both signs
  have hroot := quadRoot_eq a j t l
  rw [← hXi, ← hsq] at hroot
  set root := SC.quadRoot a j t l with hrootd
  set A2 := a * a with hA2
  set q := a * j with hq
  have hq0 : 0 < q := by positivity
  have hA20 : 0 < A2 := by positivity
  have hs_id : sq = q * root + 3 / 2 * A2 + 3 / 2 * (q * t) := by
    rw [hroot]; field_simp; ring
  have hs_le : sq ≤ q * |root| + 3 / 2 * A2 + 3 / 2 * (q * t) := by
    rw [hs_id]; nlinarith [le_abs_self root, hq0]
  have hη := η32_small
  have hu := u32_eq
  have T1A := T1.to_A32
  have SA := hS.to_A32
  have T3A := T3.to_A32
  have DA := pAJ.to_A32
  rw [abs_of_pos hsq0] at SA
  rw [show |A2 * (-3 / 2)| = 3 / 2 * A2 by rw [abs_mul, abs_of_pos hA20]; norm_num; ring] at T1A
  rw [show |a * j * t * (3 / 2)| = 3 / 2 * (q * t) by
    rw [abs_of_pos (by positivity)]; ring] at T3A
  rw [abs_of_pos hq0] at DA
  have hbig : 3 / 2 * A2 + sq ≤ 1000 := by
    have : sq ≤ 60 := by
      rw [hsq, Real.sqrt_le_left (by norm_num)]; linarith [bX.2]
    linarith [ba2.2]
  have hqt : q * t ≤ 32 := by rw [hq]; linarith [bajt.2]
  cases plus
  · -- the minus sign
    simp only [Bool.false_eq_true, ite_false]
    have e1b : 203 / 100 * (1 / 16777216) * (3 / 2 * A2) ≤ 1 := by nlinarith [ba2.2]
    have eSb : 103 / 10 * (1 / 16777216) * sq ≤ 1 := by nlinarith [hbig]
    have n1 := A32.sub T1A SA (by
      have := abs_sub (A2 * (-3 / 2)) sq
      rw [show |A2 * (-3 / 2)| = 3 / 2 * A2 by rw [abs_mul, abs_of_pos hA20]; norm_num; ring,
        abs_of_pos hsq0] at this
      have : (1002 : ℝ) ≤ capF := by norm_num [capF]
      linarith)
    have n2 := Float32.sub_zero_val n1.1 z.1 z.2
    have n1' := A32.congr_x n1 n2.1 n2.2
    set E1 := 203 / 100 * (1 / 16777216) * (3 / 2 * A2) + 103 / 10 * (1 / 16777216) * sq +
      u32 * (|A2 * (-3 / 2) - sq| + 203 / 100 * (1 / 16777216) * (3 / 2 * A2) +
        103 / 10 * (1 / 16777216) * sq) + η32 with hE1
    have hE1b : E1 ≤ 1 / 16777216 * (46 / 10 * A2 + 114 / 10 * sq) + η32 := by
      have := abs_sub (A2 * (-3 / 2)) sq
      rw [show |A2 * (-3 / 2)| = 3 / 2 * A2 by rw [abs_mul, abs_of_pos hA20]; norm_num; ring,
        abs_of_pos hsq0] at this
      rw [hE1, hu]
      have h1 : 1 / 16777216 * (|A2 * (-3 / 2) - sq| + 203 / 100 * (1 / 16777216) * (3 / 2 * A2) +
        103 / 10 * (1 / 16777216) * sq) ≤ 1 / 16777216 * (3 / 2 * A2 + sq + 203 / 100 * (1 / 16777216) * (3 / 2 * A2) +
        103 / 10 * (1 / 16777216) * sq) := by gcongr
      nlinarith
    have hE1c : E1 ≤ 1 := by
      have : 1 / 16777216 * (46 / 10 * A2 + 114 / 10 * sq) ≤ 1 / 2 := by nlinarith [ba2.2, hbig]
      linarith
    have e3b : 303 / 100 * (1 / 16777216) * (3 / 2 * (q * t)) ≤ 1 := by nlinarith [hqt]
    have n3 := A32.sub n1' T3A (by
      have := abs_sub (A2 * (-3 / 2) - sq) (a * j * t * (3 / 2))
      rw [show |a * j * t * (3 / 2)| = 3 / 2 * (q * t) by rw [abs_of_pos (by positivity)]; ring] at this
      have := abs_sub (A2 * (-3 / 2)) sq
      rw [show |A2 * (-3 / 2)| = 3 / 2 * A2 by rw [abs_mul, abs_of_pos hA20]; norm_num; ring,
        abs_of_pos hsq0] at this
      have : (2000 : ℝ) ≤ capF := by norm_num [capF]
      linarith)
    set nm := A2 * (-3 / 2) - sq - a * j * t * (3 / 2) with hnm
    have hnm_le : nm ≤ q * root := by rw [hnm, hs_id]; nlinarith [hsq0]
    have hnm_abs : |nm| ≤ 3 / 2 * A2 + sq + 3 / 2 * (q * t) := by
      rw [hnm]
      have := abs_sub (A2 * (-3 / 2) - sq) (a * j * t * (3 / 2))
      rw [show |a * j * t * (3 / 2)| = 3 / 2 * (q * t) by rw [abs_of_pos (by positivity)]; ring] at this
      have := abs_sub (A2 * (-3 / 2)) sq
      rw [show |A2 * (-3 / 2)| = 3 / 2 * A2 by rw [abs_mul, abs_of_pos hA20]; norm_num; ring,
        abs_of_pos hsq0] at this
      linarith
    have hnmq : |nm| ≤ q * (3 * (a / j) + |root| + 3 * t) := by
      have hAq : A2 = a / j * q := by rw [hA2, hq]; field_simp [hj0.ne']
      have : q * (3 * (a / j) + |root| + 3 * t) = 3 * A2 + q * |root| + 3 * (q * t) := by rw [hAq]; ring
      rw [this]; linarith [hs_le]
    set E3 := E1 + 303 / 100 * (1 / 16777216) * (3 / 2 * (q * t)) +
      u32 * (|nm| + E1 + 303 / 100 * (1 / 16777216) * (3 / 2 * (q * t))) + η32 with hE3
    have hηA : η32 ≤ 1 / 2 ^ 100 * (1 / 16777216) * A2 := by
      have h1 : η32 = 1 / 2 ^ 149 := by rw [η32_eq]; norm_num
      have h2 : (1 / 2 ^ 100 : ℝ) * (1 / 16777216) * (1 / 2 ^ 24) ≤ 1 / 2 ^ 100 * (1 / 16777216) * A2 := by
        gcongr; exact ba2.1
      rw [h1]; norm_num at h2 ⊢; linarith
    have hE3b : E3 ≤ 1 / 16777216 * (63 / 10 * A2 + 126 / 10 * sq + 62 / 10 * (q * t)) := by
      rw [hE3, hu]
      have h1 : 1 / 16777216 * (|nm| + E1 + 303 / 100 * (1 / 16777216) * (3 / 2 * (q * t))) ≤
          1 / 16777216 * (3 / 2 * A2 + sq + 3 / 2 * (q * t) + (1 / 16777216 * (46 / 10 * A2 + 114 / 10 * sq) + η32) +
            303 / 100 * (1 / 16777216) * (3 / 2 * (q * t))) := by gcongr
      have hqt0 : 0 ≤ q * t := by positivity
      nlinarith
    set m := q * (1 - 101 / 100 * (1 / 16777216)) with hm
    have hm0 : 0 < m := by rw [hm]; positivity
    have hcapb : |nm / q| + (|q| * E3 + |nm| * (101 / 100 * (1 / 16777216) * q)) / (m * |q|)
        ≤ capF := by
      rw [abs_of_pos hq0, abs_div, abs_of_pos hq0]
      have hE3' : E3 ≤ 1 := by
        have : 1 / 16777216 * (63 / 10 * A2 + 126 / 10 * sq + 62 / 10 * (q * t)) ≤ 1 := by
          nlinarith [ba2.2, hbig, hqt]
        linarith
      have hnm3 : |nm| ≤ 3000 := by linarith [hbig, hqt, ba2.2]
      have hq' : 1 / 2 ^ 16 ≤ q := by rw [hq]; exact baj.1
      have h1 : |nm| / q ≤ 2 ^ 40 := by
        rw [div_le_iff₀ hq0]; nlinarith
      have : (q * E3 + |nm| * (101 / 100 * (1 / 16777216) * q)) / (m * q) ≤ 2 ^ 40 := by
        rw [div_le_iff₀ (by positivity)]
        have hm' : 1 / 2 ^ 17 ≤ m := by rw [hm]; nlinarith [baj.1]
        nlinarith [baj.2, baj.1]
      refine le_trans (add_le_add h1 this) ?_
      norm_num [capF]
    have rD := A32.div n3 DA hm0 (by rw [hm, abs_of_pos hq0]; nlinarith) hcapb
    refine ⟨rD.1, ?_⟩
    have hrd := (abs_le.1 rD.2).2
    simp only [abs_div, abs_of_pos hq0] at hrd
    have hAq : A2 = a / j * q := by rw [hA2, hq]; field_simp [hj0.ne']
    have key : E3 + 101 / 100 * (1 / 16777216) * |nm| ≤
        1 / 16777216 * (28 * A2 + 15 * (q * |root|) + 28 * (q * t)) * (1 - 101 / 100 * (1 / 16777216)) := by
      have hr0 : 0 ≤ q * |root| := by positivity
      have hqt0 : 0 ≤ q * t := by positivity
      nlinarith [hE3b, hs_le, hnm_abs]
    have hdiv : (q * E3 + |nm| * (101 / 100 * (1 / 16777216) * q)) / (m * q) ≤
        1 / 16777216 * (28 * (a / j) + 15 * |root| + 28 * t) := by
      rw [div_le_iff₀ (by positivity), hm]
      have : q * E3 + |nm| * (101 / 100 * (1 / 16777216) * q) =
          q * (E3 + 101 / 100 * (1 / 16777216) * |nm|) := by ring
      rw [this]
      have h2 : 1 / 16777216 * (28 * (a / j) + 15 * |root| + 28 * t) *
          (q * (1 - 101 / 100 * (1 / 16777216)) * q) =
          q * (1 / 16777216 * (28 * A2 + 15 * (q * |root|) + 28 * (q * t)) *
            (1 - 101 / 100 * (1 / 16777216))) := by rw [hAq]; ring
      rw [h2]
      exact mul_le_mul_of_nonneg_left key hq0.le
    have hηt : η32 ≤ 1 / 16777216 * t := by
      have h1 : η32 = 1 / 2 ^ 149 := by rw [η32_eq]; norm_num
      have : (1 / 16777216 : ℝ) * (1 / 2 ^ 9) ≤ 1 / 16777216 * t := by gcongr
      rw [h1]; norm_num at this ⊢; linarith
    have hnmq' : |nm| / q ≤ 3 * (a / j) + |root| + 3 * t := by
      rw [div_le_iff₀ hq0]; linarith [hnmq]
    have hnm_root : nm / q ≤ root := by rw [div_le_iff₀ hq0]; linarith
    rw [hu] at hrd
    have h3 : 1 / 16777216 * (|nm| / q + (q * E3 + |nm| * (101 / 100 * (1 / 16777216) * q)) / (m * q)) ≤
        1 / 16777216 * (3 * (a / j) + |root| + 3 * t + 1 / 16777216 * (28 * (a / j) + 15 * |root| + 28 * t)) := by
      gcongr
    have ha0' : 0 ≤ a / j := by positivity
    have hr0 : 0 ≤ |root| := abs_nonneg _
    nlinarith
  · -- the plus sign
    simp only [ite_true]
    have e1b : 203 / 100 * (1 / 16777216) * (3 / 2 * A2) ≤ 1 := by nlinarith [ba2.2]
    have eSb : 103 / 10 * (1 / 16777216) * sq ≤ 1 := by nlinarith [hbig]
    have n1 := A32.add T1A SA (by
      have := abs_add_le (A2 * (-3 / 2)) sq
      rw [show |A2 * (-3 / 2)| = 3 / 2 * A2 by rw [abs_mul, abs_of_pos hA20]; norm_num; ring,
        abs_of_pos hsq0] at this
      have : (1002 : ℝ) ≤ capF := by norm_num [capF]
      linarith)
    have n2 := Float32.sub_zero_val n1.1 z.1 z.2
    have n1' := A32.congr_x n1 n2.1 n2.2
    set E1 := 203 / 100 * (1 / 16777216) * (3 / 2 * A2) + 103 / 10 * (1 / 16777216) * sq +
      u32 * (|A2 * (-3 / 2) + sq| + 203 / 100 * (1 / 16777216) * (3 / 2 * A2) +
        103 / 10 * (1 / 16777216) * sq) + η32 with hE1
    have hE1b : E1 ≤ 1 / 16777216 * (46 / 10 * A2 + 114 / 10 * sq) + η32 := by
      have := abs_add_le (A2 * (-3 / 2)) sq
      rw [show |A2 * (-3 / 2)| = 3 / 2 * A2 by rw [abs_mul, abs_of_pos hA20]; norm_num; ring,
        abs_of_pos hsq0] at this
      rw [hE1, hu]
      have h1 : 1 / 16777216 * (|A2 * (-3 / 2) + sq| + 203 / 100 * (1 / 16777216) * (3 / 2 * A2) +
        103 / 10 * (1 / 16777216) * sq) ≤ 1 / 16777216 * (3 / 2 * A2 + sq + 203 / 100 * (1 / 16777216) * (3 / 2 * A2) +
        103 / 10 * (1 / 16777216) * sq) := by gcongr
      nlinarith
    have hE1c : E1 ≤ 1 := by
      have : 1 / 16777216 * (46 / 10 * A2 + 114 / 10 * sq) ≤ 1 / 2 := by nlinarith [ba2.2, hbig]
      linarith
    have e3b : 303 / 100 * (1 / 16777216) * (3 / 2 * (q * t)) ≤ 1 := by nlinarith [hqt]
    have n3 := A32.sub n1' T3A (by
      have := abs_sub (A2 * (-3 / 2) + sq) (a * j * t * (3 / 2))
      rw [show |a * j * t * (3 / 2)| = 3 / 2 * (q * t) by rw [abs_of_pos (by positivity)]; ring] at this
      have := abs_add_le (A2 * (-3 / 2)) sq
      rw [show |A2 * (-3 / 2)| = 3 / 2 * A2 by rw [abs_mul, abs_of_pos hA20]; norm_num; ring,
        abs_of_pos hsq0] at this
      have : (2000 : ℝ) ≤ capF := by norm_num [capF]
      linarith)
    have hra : A2 * (-3 / 2) + sq - a * j * t * (3 / 2) = q * root := by
      rw [hs_id]; ring
    rw [hra] at n3
    set E3 := E1 + 303 / 100 * (1 / 16777216) * (3 / 2 * (q * t)) +
      u32 * (|q * root| + E1 + 303 / 100 * (1 / 16777216) * (3 / 2 * (q * t))) + η32 with hE3
    have hqr : |q * root| ≤ 3 / 2 * A2 + sq + 3 / 2 * (q * t) := by
      rw [← hra]
      have := abs_sub (A2 * (-3 / 2) + sq) (a * j * t * (3 / 2))
      rw [show |a * j * t * (3 / 2)| = 3 / 2 * (q * t) by rw [abs_of_pos (by positivity)]; ring] at this
      have := abs_add_le (A2 * (-3 / 2)) sq
      rw [show |A2 * (-3 / 2)| = 3 / 2 * A2 by rw [abs_mul, abs_of_pos hA20]; norm_num; ring,
        abs_of_pos hsq0] at this
      linarith
    have hηA : η32 ≤ 1 / 2 ^ 100 * (1 / 16777216) * A2 := by
      have h1 : η32 = 1 / 2 ^ 149 := by rw [η32_eq]; norm_num
      have h2 : (1 / 2 ^ 100 : ℝ) * (1 / 16777216) * (1 / 2 ^ 24) ≤ 1 / 2 ^ 100 * (1 / 16777216) * A2 := by
        gcongr; exact ba2.1
      rw [h1]; norm_num at h2 ⊢; linarith
    have hE3b : E3 ≤ 1 / 16777216 * (63 / 10 * A2 + 126 / 10 * sq + 62 / 10 * (q * t)) := by
      rw [hE3, hu]
      have h1 : 1 / 16777216 * (|q * root| + E1 + 303 / 100 * (1 / 16777216) * (3 / 2 * (q * t))) ≤
          1 / 16777216 * (3 / 2 * A2 + sq + 3 / 2 * (q * t) + (1 / 16777216 * (46 / 10 * A2 + 114 / 10 * sq) + η32) +
            303 / 100 * (1 / 16777216) * (3 / 2 * (q * t))) := by gcongr
      have hqt0 : 0 ≤ q * t := by positivity
      nlinarith
    set m := q * (1 - 101 / 100 * (1 / 16777216)) with hm
    have hm0 : 0 < m := by rw [hm]; positivity
    have hroot_q : |q * root / q| = |root| := by rw [mul_div_cancel_left₀ _ hq0.ne']
    have hcapb : |q * root / q| + (|q| * E3 + |q * root| * (101 / 100 * (1 / 16777216) * q)) / (m * |q|)
        ≤ capF := by
      rw [hroot_q, abs_of_pos hq0]
      have hr : |root| ≤ 2 ^ 40 := by
        have : |q * root| ≤ 3000 := by linarith [hbig, hqt, ba2.2]
        rw [abs_mul, abs_of_pos hq0] at this
        have : |root| ≤ 3000 / q := by rw [le_div_iff₀ hq0]; linarith
        have : 3000 / q ≤ 3000 * 2 ^ 16 := by
          rw [div_le_iff₀ hq0]; nlinarith [baj.1]
        norm_num at *; linarith
      have hE3' : E3 ≤ 1 := by
        have : 1 / 16777216 * (63 / 10 * A2 + 126 / 10 * sq + 62 / 10 * (q * t)) ≤ 1 := by
          nlinarith [ba2.2, hbig, hqt]
        linarith
      have : (q * E3 + |q * root| * (101 / 100 * (1 / 16777216) * q)) / (m * q) ≤ 2 ^ 40 := by
        rw [div_le_iff₀ (by positivity)]
        have : |q * root| ≤ 3000 := by linarith [hbig, hqt, ba2.2]
        have hm' : 1 / 2 ^ 17 ≤ m := by rw [hm]; nlinarith [baj.1]
        nlinarith [baj.2, baj.1]
      refine le_trans (add_le_add hr this) ?_
      norm_num [capF]
    have rD := A32.div n3 DA hm0 (by rw [hm, abs_of_pos hq0]; nlinarith) hcapb
    rw [mul_div_cancel_left₀ _ hq0.ne'] at rD
    refine ⟨rD.1, ?_⟩
    have hrd := (abs_le.1 rD.2).2
    rw [abs_of_pos hq0, abs_mul, abs_of_pos hq0] at hrd
    -- the quotient's error
    have hAq : A2 = a / j * q := by rw [hA2, hq]; field_simp [hj0.ne']
    have key : E3 + 101 / 100 * (1 / 16777216) * q * |root| ≤
        1 / 16777216 * (26 * A2 + 14 * (q * |root|) + 26 * (q * t)) * (1 - 101 / 100 * (1 / 16777216)) := by
      have hr0 : 0 ≤ q * |root| := by positivity
      have hqt0 : 0 ≤ q * t := by positivity
      nlinarith [hE3b, hs_le]
    have hdiv : (q * E3 + q * |root| * (101 / 100 * (1 / 16777216) * q)) / (m * q) ≤
        1 / 16777216 * (26 * (a / j) + 14 * |root| + 26 * t) := by
      rw [div_le_iff₀ (by positivity), hm]
      have : q * E3 + q * |root| * (101 / 100 * (1 / 16777216) * q) =
          q * (E3 + 101 / 100 * (1 / 16777216) * q * |root|) := by ring
      rw [this]
      have h2 : 1 / 16777216 * (26 * (a / j) + 14 * |root| + 26 * t) *
          (q * (1 - 101 / 100 * (1 / 16777216)) * q) =
          q * (1 / 16777216 * (26 * A2 + 14 * (q * |root|) + 26 * (q * t)) *
            (1 - 101 / 100 * (1 / 16777216))) := by rw [hAq]; ring
      rw [h2]
      exact mul_le_mul_of_nonneg_left key hq0.le
    have hηt : η32 ≤ 1 / 16777216 * t := by
      have h1 : η32 = 1 / 2 ^ 149 := by rw [η32_eq]; norm_num
      have : (1 / 16777216 : ℝ) * (1 / 2 ^ 9) ≤ 1 / 16777216 * t := by gcongr
      rw [h1]; norm_num at this ⊢; linarith
    have hpos : 0 ≤ 26 * (a / j) + 14 * |root| + 26 * t := by positivity
    have hsmall : 1 / 16777216 * (26 * (a / j) + 14 * |root| + 26 * t) ≤
        1 / 16777216 * (26 * (a / j) + 14 * |root| + 26 * t) := le_rfl
    rw [hu] at hrd
    have h3 : 1 / 16777216 * (|root| + (q * E3 + q * |root| * (101 / 100 * (1 / 16777216) * q)) / (m * q)) ≤
        1 / 16777216 * (|root| + 1 / 16777216 * (26 * (a / j) + 14 * |root| + 26 * t)) := by
      gcongr
    have h4 : 1 / 16777216 * (1 / 16777216 * (26 * (a / j) + 14 * |root| + 26 * t)) ≤
        1 / 16777216 * (26 * (a / j) + 14 * |root| + 26 * t) := by
      have := mul_le_mul_of_nonneg_right (show (1 / 16777216 : ℝ) ≤ 1 by norm_num)
        (show 0 ≤ 1 / 16777216 * (26 * (a / j) + 14 * |root| + 26 * t) by positivity)
      linarith
    have ha0' : 0 ≤ a / j := by positivity
    have hr0 : 0 ≤ |root| := abs_nonneg _
    nlinarith

end

end Contracts.Mission
