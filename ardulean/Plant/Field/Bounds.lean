module

public import Plant.Model.Field
public import Plant.Field.Motor
public import Plant.Lib.Blocks
public import Mathlib.Analysis.Normed.Group.Constructions
public import Mathlib.Tactic

/-!
# Bounds on the vector field

Every estimate is explicit. The thrusts are clipped inside the force and torque maps, so the thrust acceleration is
in `[0, amax]` (`accel_nonneg`, `accel_le`) and each angular acceleration of the torques is at most
`alphaMax = 2 · lever · fmax / Jx` (`abs_torqueX_div_le` etc.) at every state. Both are Lipschitz in the thrusts:
`amax` and `2 alphaMax` per unit of the largest thrust difference (`abs_accel_sub_le_of`,
`abs_torqueX_div_sub_le_of`, …).

**Block bounds.** The coordinates split into blocks `p` (`0,1,2`), `v` (`3,4,5`), `q` (`6,7,8,9`), `ω`
(`10,11,12`), `f` (`13,…,16`). With `|qⱼ| ≤ Rq`, `|ωⱼ| ≤ Rw` at two states and coordinate differences at most `Dv`,
`Dq`, `Dw`, `Df` in the blocks, each component of `vf x u - vf y u` is at most
* `Dv` in the `p` block (`ṗ = v`),
* `amax (8 Rq Dq + 4 Rq² Df)` in the `v` block (the down axis is quadratic in `q`, the thrust linear in `f`),
* `(3/2)(Rq Dw + Rw Dq)` in the `q` block (bilinear kinematics),
* `gyro · 2 Rw Dw + 2 alphaMax Df` in the `ω` block, `gyro = (Jz - Jx)/Jx`, which bounds
  `|Jz - Jy| / Jx, |Jx - Jz| / Jy, |Jy - Jx| / Jz` because `Jy = Jx ≤ Jz`,
* `Df / tauUp` in the `f` block (the lag is `1/tauUp`-Lipschitz, `Plant.Field.Motor`)
(`vf_sub_p`, `vf_sub_v`, `vf_sub_q`, `vf_sub_w`, `vf_sub_f`). On the sup-norm ball of radius `R` this gives the
Lipschitz constant `Klip R = 1 + 1/tauUp + 2 alphaMax + (8 amax + 3 + 2 gyro) R + 4 amax R²`
(`vf_lipschitz_ball`) and the bound
`‖vf x u‖ ≤ Mbd R = R + g + alphaMax + (1 + R)/tauUp + (4 amax + 2 + gyro) R²` (`norm_vf_le`).
-/

@[expose] public section

namespace Plant

noncomputable section

open Finset

/-! ## Forces, torques -/

theorem thrust_eq (u : Fin 4 → ℝ) :
    thrust u = fmax * (clip01 (u 0) + clip01 (u 1) + clip01 (u 2) + clip01 (u 3)) := by
  simp only [thrust, force]; ring

/-- The thrust acceleration is nonnegative. -/
theorem accel_nonneg (u : Fin 4 → ℝ) : 0 ≤ accel u := by
  rw [accel, thrust_eq]
  have := clip01_nonneg (u 0); have := clip01_nonneg (u 1)
  have := clip01_nonneg (u 2); have := clip01_nonneg (u 3)
  have := fmax_pos; have := mass_pos
  positivity

/-- The thrust acceleration is at most `amax = thrust2weight · g`. -/
theorem accel_le (u : Fin 4 → ℝ) : accel u ≤ amax := by
  rw [accel, thrust_eq, ← four_fmax_div_mass, div_le_div_iff_of_pos_right mass_pos]
  have := clip01_le_one (u 0); have := clip01_le_one (u 1)
  have := clip01_le_one (u 2); have := clip01_le_one (u 3)
  nlinarith [fmax_pos]

/-- `|accel u| ≤ amax`. -/
theorem abs_accel_le (u : Fin 4 → ℝ) : |accel u| ≤ amax := by
  rw [abs_of_nonneg (accel_nonneg u)]; exact accel_le u

/-- Bound on the angular accelerations of the torques, rad/s²: `2 · lever · fmax / Jx`. -/
def alphaMax : ℝ := 2 * lever * fmax / Jx

theorem alphaMax_pos : 0 < alphaMax := by
  have := lever_pos; have := fmax_pos; have := Jx_pos; unfold alphaMax; positivity

private theorem abs_signed_sum_le (a b c d : ℝ) (ha : 0 ≤ a) (ha' : a ≤ 1) (hb : 0 ≤ b)
    (hb' : b ≤ 1) (hc : 0 ≤ c) (hc' : c ≤ 1) (hd : 0 ≤ d) (hd' : d ≤ 1) :
    |-a + b + c - d| ≤ 2 ∧ |a - b + c - d| ≤ 2 ∧ |a + b - c - d| ≤ 2 := by
  refine ⟨abs_le.mpr ⟨?_, ?_⟩, abs_le.mpr ⟨?_, ?_⟩, abs_le.mpr ⟨?_, ?_⟩⟩ <;> linarith

private theorem clips (u : Fin 4 → ℝ) :
    |-clip01 (u 0) + clip01 (u 1) + clip01 (u 2) - clip01 (u 3)| ≤ 2 ∧
    |clip01 (u 0) - clip01 (u 1) + clip01 (u 2) - clip01 (u 3)| ≤ 2 ∧
    |clip01 (u 0) + clip01 (u 1) - clip01 (u 2) - clip01 (u 3)| ≤ 2 :=
  abs_signed_sum_le _ _ _ _ (clip01_nonneg _) (clip01_le_one _) (clip01_nonneg _)
    (clip01_le_one _) (clip01_nonneg _) (clip01_le_one _) (clip01_nonneg _) (clip01_le_one _)

/-- `|τx| ≤ 2 · lever · fmax`. -/
theorem abs_torqueX_le (u : Fin 4 → ℝ) : |torqueX u| ≤ 2 * lever * fmax := by
  have e : torqueX u = lever * fmax *
      (-clip01 (u 0) + clip01 (u 1) + clip01 (u 2) - clip01 (u 3)) := by
    simp only [torqueX, force]; ring
  rw [e, abs_mul, abs_of_pos (mul_pos lever_pos fmax_pos)]
  calc _ ≤ lever * fmax * 2 :=
        mul_le_mul_of_nonneg_left (clips u).1 (mul_pos lever_pos fmax_pos).le
    _ = _ := by ring

/-- `|τy| ≤ 2 · lever · fmax`. -/
theorem abs_torqueY_le (u : Fin 4 → ℝ) : |torqueY u| ≤ 2 * lever * fmax := by
  have e : torqueY u = lever * fmax *
      (clip01 (u 0) - clip01 (u 1) + clip01 (u 2) - clip01 (u 3)) := by
    simp only [torqueY, force]; ring
  rw [e, abs_mul, abs_of_pos (mul_pos lever_pos fmax_pos)]
  calc _ ≤ lever * fmax * 2 :=
        mul_le_mul_of_nonneg_left (clips u).2.1 (mul_pos lever_pos fmax_pos).le
    _ = _ := by ring

/-- `|τz| ≤ 2 · (km/kf) · fmax`. -/
theorem abs_torqueZ_le (u : Fin 4 → ℝ) : |torqueZ u| ≤ 2 * kmkf * fmax := by
  rw [torqueZ, km_maxRPM_sq, abs_mul, abs_of_pos (mul_pos kmkf_pos fmax_pos)]
  calc _ ≤ kmkf * fmax * 2 :=
        mul_le_mul_of_nonneg_left (clips u).2.2 (mul_pos kmkf_pos fmax_pos).le
    _ = _ := by ring

theorem abs_torqueX_div_le (u : Fin 4 → ℝ) : |torqueX u / Jx| ≤ alphaMax := by
  rw [abs_div, abs_of_pos Jx_pos, alphaMax]
  exact div_le_div_of_nonneg_right (abs_torqueX_le u) Jx_pos.le

theorem abs_torqueY_div_le (u : Fin 4 → ℝ) : |torqueY u / Jy| ≤ alphaMax := by
  rw [abs_div, abs_of_pos Jy_pos, alphaMax, Jy_eq_Jx]
  exact div_le_div_of_nonneg_right (abs_torqueY_le u) Jx_pos.le

theorem abs_torqueZ_div_le (u : Fin 4 → ℝ) : |torqueZ u / Jz| ≤ alphaMax := by
  rw [abs_div, abs_of_pos Jz_pos]
  calc |torqueZ u| / Jz ≤ 2 * kmkf * fmax / Jz :=
        div_le_div_of_nonneg_right (abs_torqueZ_le u) Jz_pos.le
    _ ≤ alphaMax := by
        rw [alphaMax, div_le_div_iff₀ Jz_pos Jx_pos]
        have := kmkf_Jx_le_lever_Jz
        nlinarith [fmax_pos]

/-! ## Rotational energy and the gyroscopic coefficient -/

/-- Twice the rotational kinetic energy, `ωᵀ J ω`. -/
def energy (x : X) : ℝ := Jx * x 10 ^ 2 + Jy * x 11 ^ 2 + Jz * x 12 ^ 2

theorem energy_nonneg (x : X) : 0 ≤ energy x := by
  have := Jx_pos; have := Jy_pos; have := Jz_pos; unfold energy; positivity

/-- The coefficient of the gyroscopic coupling: `(Jz - Jx)/Jx`. -/
def gyro : ℝ := (Jz - Jx) / Jx

theorem gyro_nonneg : 0 ≤ gyro := div_nonneg (by linarith [Jx_le_Jz]) Jx_pos.le

/-- The roll coefficient of the gyroscopic coupling is `gyro`. -/
theorem abs_gyroX_le : |-((Jz - Jy) / Jx)| ≤ gyro := by
  rw [Jy_eq_Jx, abs_neg]; exact le_of_eq (abs_of_nonneg gyro_nonneg)

/-- The pitch coefficient of the gyroscopic coupling is `gyro`. -/
theorem abs_gyroY_le : |-((Jx - Jz) / Jy)| ≤ gyro := by
  rw [Jy_eq_Jx, abs_neg, show (Jx - Jz) / Jx = -gyro by unfold gyro; ring, abs_neg,
    abs_of_nonneg gyro_nonneg]

/-- The yaw coefficient of the gyroscopic coupling is `0`. -/
theorem abs_gyroZ_le : |-((Jy - Jx) / Jz)| ≤ gyro := by
  rw [Jy_eq_Jx, sub_self, zero_div, neg_zero, abs_zero]; exact gyro_nonneg

/-! ## Dependence on the thrusts -/

/-- The clip is 1-Lipschitz. -/
theorem abs_clip01_sub_le (a b : ℝ) : |clip01 a - clip01 b| ≤ |a - b| := by
  unfold clip01
  rw [max_comm 0, max_comm 0]
  refine (abs_max_sub_max_le_abs _ _ _).trans ?_
  rw [min_comm 1, min_comm 1]
  have := abs_min_sub_min_le_max a 1 b 1
  simpa using this

section thrusts
variable {f g : Fin 4 → ℝ} {D : ℝ}

private theorem four_le (h : ∀ i, |f i - g i| ≤ D) :
    (-D ≤ clip01 (f 0) - clip01 (g 0) ∧ clip01 (f 0) - clip01 (g 0) ≤ D) ∧
    (-D ≤ clip01 (f 1) - clip01 (g 1) ∧ clip01 (f 1) - clip01 (g 1) ≤ D) ∧
    (-D ≤ clip01 (f 2) - clip01 (g 2) ∧ clip01 (f 2) - clip01 (g 2) ≤ D) ∧
    (-D ≤ clip01 (f 3) - clip01 (g 3) ∧ clip01 (f 3) - clip01 (g 3) ≤ D) :=
  ⟨abs_le.mp ((abs_clip01_sub_le _ _).trans (h 0)), abs_le.mp ((abs_clip01_sub_le _ _).trans (h 1)),
    abs_le.mp ((abs_clip01_sub_le _ _).trans (h 2)), abs_le.mp ((abs_clip01_sub_le _ _).trans (h 3))⟩

/-- **The thrust acceleration is `amax`-Lipschitz in the thrusts** (largest difference `D`). -/
theorem abs_accel_sub_le_of (h : ∀ i, |f i - g i| ≤ D) : |accel f - accel g| ≤ amax * D := by
  obtain ⟨⟨a0, b0⟩, ⟨a1, b1⟩, ⟨a2, b2⟩, ⟨a3, b3⟩⟩ := four_le h
  have e : accel f - accel g = amax / 4 * ((clip01 (f 0) - clip01 (g 0)) +
      (clip01 (f 1) - clip01 (g 1)) + (clip01 (f 2) - clip01 (g 2)) +
      (clip01 (f 3) - clip01 (g 3))) := by
    rw [accel, accel, thrust_eq, thrust_eq, ← four_fmax_div_mass]; field_simp; ring
  have hs : |(clip01 (f 0) - clip01 (g 0)) + (clip01 (f 1) - clip01 (g 1)) +
      (clip01 (f 2) - clip01 (g 2)) + (clip01 (f 3) - clip01 (g 3))| ≤ 4 * D :=
    abs_le.mpr ⟨by linarith, by linarith⟩
  have := amax_pos
  rw [e, abs_mul, abs_of_pos (by positivity)]
  calc amax / 4 * _ ≤ amax / 4 * (4 * D) := mul_le_mul_of_nonneg_left hs (by positivity)
    _ = _ := by ring

/-- **The roll angular acceleration moves by at most `2 alphaMax D`.** -/
theorem abs_torqueX_div_sub_le_of (h : ∀ i, |f i - g i| ≤ D) :
    |torqueX f / Jx - torqueX g / Jx| ≤ 2 * alphaMax * D := by
  obtain ⟨⟨a0, b0⟩, ⟨a1, b1⟩, ⟨a2, b2⟩, ⟨a3, b3⟩⟩ := four_le h
  have hc : 0 < lever * fmax / Jx := by have := lever_pos; have := fmax_pos; have := Jx_pos; positivity
  have e : torqueX f / Jx - torqueX g / Jx = lever * fmax / Jx * (-(clip01 (f 0) - clip01 (g 0)) +
      (clip01 (f 1) - clip01 (g 1)) + (clip01 (f 2) - clip01 (g 2)) -
      (clip01 (f 3) - clip01 (g 3))) := by simp only [torqueX, force]; ring
  have hs : |-(clip01 (f 0) - clip01 (g 0)) + (clip01 (f 1) - clip01 (g 1)) +
      (clip01 (f 2) - clip01 (g 2)) - (clip01 (f 3) - clip01 (g 3))| ≤ 4 * D :=
    abs_le.mpr ⟨by linarith, by linarith⟩
  rw [e, abs_mul, abs_of_pos hc]
  calc lever * fmax / Jx * _ ≤ lever * fmax / Jx * (4 * D) := mul_le_mul_of_nonneg_left hs hc.le
    _ = _ := by rw [alphaMax]; ring

/-- **The pitch angular acceleration moves by at most `2 alphaMax D`.** -/
theorem abs_torqueY_div_sub_le_of (h : ∀ i, |f i - g i| ≤ D) :
    |torqueY f / Jy - torqueY g / Jy| ≤ 2 * alphaMax * D := by
  obtain ⟨⟨a0, b0⟩, ⟨a1, b1⟩, ⟨a2, b2⟩, ⟨a3, b3⟩⟩ := four_le h
  have hc : 0 < lever * fmax / Jy := by have := lever_pos; have := fmax_pos; have := Jy_pos; positivity
  have e : torqueY f / Jy - torqueY g / Jy = lever * fmax / Jy * ((clip01 (f 0) - clip01 (g 0)) -
      (clip01 (f 1) - clip01 (g 1)) + (clip01 (f 2) - clip01 (g 2)) -
      (clip01 (f 3) - clip01 (g 3))) := by simp only [torqueY, force]; ring
  have hs : |(clip01 (f 0) - clip01 (g 0)) - (clip01 (f 1) - clip01 (g 1)) +
      (clip01 (f 2) - clip01 (g 2)) - (clip01 (f 3) - clip01 (g 3))| ≤ 4 * D :=
    abs_le.mpr ⟨by linarith, by linarith⟩
  rw [e, abs_mul, abs_of_pos hc]
  calc lever * fmax / Jy * _ ≤ lever * fmax / Jy * (4 * D) := mul_le_mul_of_nonneg_left hs hc.le
    _ = _ := by rw [alphaMax, Jy_eq_Jx]; ring

/-- **The yaw angular acceleration moves by at most `2 alphaMax D`.** -/
theorem abs_torqueZ_div_sub_le_of (h : ∀ i, |f i - g i| ≤ D) :
    |torqueZ f / Jz - torqueZ g / Jz| ≤ 2 * alphaMax * D := by
  obtain ⟨⟨a0, b0⟩, ⟨a1, b1⟩, ⟨a2, b2⟩, ⟨a3, b3⟩⟩ := four_le h
  have hc : 0 < kmkf * fmax / Jz := by have := kmkf_pos; have := fmax_pos; have := Jz_pos; positivity
  have e : torqueZ f / Jz - torqueZ g / Jz = kmkf * fmax / Jz * ((clip01 (f 0) - clip01 (g 0)) +
      (clip01 (f 1) - clip01 (g 1)) - (clip01 (f 2) - clip01 (g 2)) -
      (clip01 (f 3) - clip01 (g 3))) := by rw [torqueZ, torqueZ, km_maxRPM_sq]; ring
  have hs : |(clip01 (f 0) - clip01 (g 0)) + (clip01 (f 1) - clip01 (g 1)) -
      (clip01 (f 2) - clip01 (g 2)) - (clip01 (f 3) - clip01 (g 3))| ≤ 4 * D :=
    abs_le.mpr ⟨by linarith, by linarith⟩
  have hk : kmkf * fmax / Jz ≤ lever * fmax / Jx := by
    rw [div_le_div_iff₀ Jz_pos Jx_pos]
    have := kmkf_Jx_le_lever_Jz
    nlinarith [fmax_pos]
  have hD : 0 ≤ D := by have := (abs_nonneg _).trans (h 0); exact this
  rw [e, abs_mul, abs_of_pos hc]
  calc kmkf * fmax / Jz * _ ≤ lever * fmax / Jx * (4 * D) :=
        mul_le_mul hk hs (abs_nonneg _) (by have := lever_pos; have := fmax_pos; have := Jx_pos; positivity)
    _ = _ := by rw [alphaMax]; ring

end thrusts

/-- The thrust block of a difference. -/
theorem thr_sub_le {x y : X} {D : ℝ} (h : FBd (x - y) D) : ∀ i, |thr x i - thr y i| ≤ D := by
  obtain ⟨a, b, c, d⟩ := h
  intro i; fin_cases i
  exacts [a, b, c, d]


/-! ## Differences of the field, block by block -/

section diff
variable {x y : X} {u : Fin 4 → ℝ}

theorem vf_sub_p {Dv : ℝ} (hd : VBd (x - y) Dv) :
    |vf x u 0 - vf y u 0| ≤ Dv ∧ |vf x u 1 - vf y u 1| ≤ Dv ∧ |vf x u 2 - vf y u 2| ≤ Dv := by
  simpa [vf_0, vf_1, vf_2, VBd] using hd

/-- A velocity row: `|a d - a' d'| ≤ amax |d - d'| + |a - a'| |d'|`. -/
private theorem vrow {a a' d d' A Dd Q : ℝ} (ha : |a| ≤ amax) (haa : |a - a'| ≤ amax * A)
    (hd : |d - d'| ≤ Dd) (hd' : |d'| ≤ Q) (hA : 0 ≤ A) :
    |-a * d - -a' * d'| ≤ amax * (Dd + Q * A) := by
  have e : -a * d - -a' * d' = -(a * (d - d') + (a - a') * d') := by ring
  rw [e, abs_neg]
  have hq : 0 ≤ Q := (abs_nonneg _).trans hd'
  have hAm : 0 ≤ amax := amax_pos.le
  calc |a * (d - d') + (a - a') * d'| ≤ |a| * |d - d'| + |a - a'| * |d'| := by
        rw [← abs_mul, ← abs_mul]; exact abs_add_le _ _
    _ ≤ amax * Dd + amax * A * Q :=
        add_le_add (mul_le_mul ha hd (abs_nonneg _) hAm)
          (mul_le_mul haa hd' (abs_nonneg _) (mul_nonneg hAm hA))
    _ = _ := by ring

theorem vf_sub_v {Rq Dq Df : ℝ} (hx : QBd x Rq) (hy : QBd y Rq) (hd : QBd (x - y) Dq)
    (hf : FBd (x - y) Df) :
    |vf x u 3 - vf y u 3| ≤ amax * (8 * Rq * Dq + 4 * Rq ^ 2 * Df) ∧
      |vf x u 4 - vf y u 4| ≤ amax * (8 * Rq * Dq + 4 * Rq ^ 2 * Df) ∧
      |vf x u 5 - vf y u 5| ≤ amax * (8 * Rq * Dq + 4 * Rq ^ 2 * Df) := by
  obtain ⟨d3, d4, d5⟩ := dn_sub_le hx hy hd
  obtain ⟨e3, e4, e5⟩ := abs_down_le y
  have hQ := qnormSq_le_of_QBd hy
  have hA := abs_accel_le (thr x)
  have ha := abs_accel_sub_le_of (thr_sub_le hf)
  have hDf : 0 ≤ Df := (abs_nonneg _).trans hf.1
  refine ⟨?_, ?_, ?_⟩
  · rw [vf_3, vf_3]; exact vrow hA ha d3 (e3.trans hQ) hDf
  · rw [vf_4, vf_4]; exact vrow hA ha d4 (e4.trans hQ) hDf
  · rw [vf_5, vf_5, add_sub_add_left_eq_sub]; exact vrow hA ha d5 (e5.trans hQ) hDf

/-- Three bilinear products with a factor `½`. -/
private theorem half_three {a b c : ℝ} {B : ℝ} (ha : |a| ≤ B) (hb : |b| ≤ B)
    (hc : |c| ≤ B) :
    |(a + b + c) / 2| ≤ (3 / 2) * B ∧ |(a + b - c) / 2| ≤ (3 / 2) * B ∧
      |(a - b + c) / 2| ≤ (3 / 2) * B ∧ |(-a - b - c) / 2| ≤ (3 / 2) * B := by
  have := abs_le.mp ha; have := abs_le.mp hb; have := abs_le.mp hc
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rw [abs_le] <;> constructor <;> linarith

theorem vf_sub_q {Rq Rw Dq Dw : ℝ} (hx : QBd x Rq) (hy : WBd y Rw) (hdq : QBd (x - y) Dq)
    (hdw : WBd (x - y) Dw) :
    |vf x u 6 - vf y u 6| ≤ (3 / 2) * (Rq * Dw + Rw * Dq) ∧
      |vf x u 7 - vf y u 7| ≤ (3 / 2) * (Rq * Dw + Rw * Dq) ∧
      |vf x u 8 - vf y u 8| ≤ (3 / 2) * (Rq * Dw + Rw * Dq) ∧
      |vf x u 9 - vf y u 9| ≤ (3 / 2) * (Rq * Dw + Rw * Dq) := by
  obtain ⟨x6, x7, x8, x9⟩ := hx
  obtain ⟨y10, y11, y12⟩ := hy
  obtain ⟨d6, d7, d8, d9⟩ := hdq
  obtain ⟨d10, d11, d12⟩ := hdw
  simp only [Pi.sub_apply] at d6 d7 d8 d9 d10 d11 d12
  have P : ∀ {i j : Fin 17}, |x i| ≤ Rq → |y j| ≤ Rw → |x i - y i| ≤ Dq → |x j - y j| ≤ Dw →
      |x i * x j - y i * y j| ≤ Rq * Dw + Rw * Dq := fun a b c d => abs_mul_sub_mul_le a b c d
  refine ⟨?_, ?_, ?_, ?_⟩
  · have e : vf x u 6 - vf y u 6 = (-(x 7 * x 10 - y 7 * y 10) - (x 8 * x 11 - y 8 * y 11) -
        (x 9 * x 12 - y 9 * y 12)) / 2 := by rw [vf_6, vf_6]; ring
    rw [e]; exact (half_three (P x7 y10 d7 d10) (P x8 y11 d8 d11) (P x9 y12 d9 d12)).2.2.2
  · have e : vf x u 7 - vf y u 7 = ((x 6 * x 10 - y 6 * y 10) + (x 8 * x 12 - y 8 * y 12) -
        (x 9 * x 11 - y 9 * y 11)) / 2 := by rw [vf_7, vf_7]; ring
    rw [e]; exact (half_three (P x6 y10 d6 d10) (P x8 y12 d8 d12) (P x9 y11 d9 d11)).2.1
  · have e : vf x u 8 - vf y u 8 = ((x 6 * x 11 - y 6 * y 11) - (x 7 * x 12 - y 7 * y 12) +
        (x 9 * x 10 - y 9 * y 10)) / 2 := by rw [vf_8, vf_8]; ring
    rw [e]; exact (half_three (P x6 y11 d6 d11) (P x7 y12 d7 d12) (P x9 y10 d9 d10)).2.2.1
  · have e : vf x u 9 - vf y u 9 = ((x 6 * x 12 - y 6 * y 12) + (x 7 * x 11 - y 7 * y 11) -
        (x 8 * x 10 - y 8 * y 10)) / 2 := by rw [vf_9, vf_9]; ring
    rw [e]; exact (half_three (P x6 y12 d6 d12) (P x7 y11 d7 d11) (P x8 y10 d8 d10)).2.1

theorem vf_sub_w {Rw Dw Df : ℝ} (hx : WBd x Rw) (hy : WBd y Rw) (hd : WBd (x - y) Dw)
    (hf : FBd (x - y) Df) :
    |vf x u 10 - vf y u 10| ≤ gyro * (2 * Rw * Dw) + 2 * alphaMax * Df ∧
      |vf x u 11 - vf y u 11| ≤ gyro * (2 * Rw * Dw) + 2 * alphaMax * Df ∧
      |vf x u 12 - vf y u 12| ≤ gyro * (2 * Rw * Dw) + 2 * alphaMax * Df := by
  obtain ⟨x10, x11, x12⟩ := hx
  obtain ⟨y10, y11, y12⟩ := hy
  obtain ⟨d10, d11, d12⟩ := hd
  simp only [Pi.sub_apply] at d10 d11 d12
  have hg := gyro_nonneg
  have hF := thr_sub_le hf
  have G : ∀ {c : ℝ} {i j : Fin 17}, |c| ≤ gyro → |x i| ≤ Rw → |y j| ≤ Rw → |x i - y i| ≤ Dw →
      |x j - y j| ≤ Dw → |c * (x i * x j - y i * y j)| ≤ gyro * (2 * Rw * Dw) := by
    intro c i j hc a b da db
    rw [abs_mul]
    calc |c| * |x i * x j - y i * y j| ≤ gyro * (Rw * Dw + Rw * Dw) :=
          mul_le_mul hc (abs_mul_sub_mul_le a b da db) (abs_nonneg _) hg
      _ = _ := by ring
  refine ⟨?_, ?_, ?_⟩
  · have e : vf x u 10 - vf y u 10 = (torqueX (thr x) / Jx - torqueX (thr y) / Jx) +
        -((Jz - Jy) / Jx) * (x 11 * x 12 - y 11 * y 12) := by
      rw [vf_10, vf_10]; field_simp [Jx_pos.ne']; ring
    rw [e]; refine (abs_add_le _ _).trans ?_
    have := G abs_gyroX_le x11 y12 d11 d12
    have := abs_torqueX_div_sub_le_of hF
    linarith
  · have e : vf x u 11 - vf y u 11 = (torqueY (thr x) / Jy - torqueY (thr y) / Jy) +
        -((Jx - Jz) / Jy) * (x 12 * x 10 - y 12 * y 10) := by
      rw [vf_11, vf_11]; field_simp [Jy_pos.ne']; ring
    rw [e]; refine (abs_add_le _ _).trans ?_
    have := G abs_gyroY_le x12 y10 d12 d10
    have := abs_torqueY_div_sub_le_of hF
    linarith
  · have e : vf x u 12 - vf y u 12 = (torqueZ (thr x) / Jz - torqueZ (thr y) / Jz) +
        -((Jy - Jx) / Jz) * (x 10 * x 11 - y 10 * y 11) := by
      rw [vf_12, vf_12]; field_simp [Jz_pos.ne']; ring
    rw [e]; refine (abs_add_le _ _).trans ?_
    have := G abs_gyroZ_le x10 y11 d10 d11
    have := abs_torqueZ_div_sub_le_of hF
    linarith

/-- The thrust rows: `|ḟᵢ(x) - ḟᵢ(y)| ≤ Df / tauUp`. -/
theorem vf_sub_f {Df : ℝ} (hf : FBd (x - y) Df) :
    |vf x u 13 - vf y u 13| ≤ Df / tauUp ∧ |vf x u 14 - vf y u 14| ≤ Df / tauUp ∧
      |vf x u 15 - vf y u 15| ≤ Df / tauUp ∧ |vf x u 16 - vf y u 16| ≤ Df / tauUp := by
  obtain ⟨a, b, c, d⟩ := hf
  simp only [Pi.sub_apply] at a b c d
  have k : ∀ (c' p q : ℝ), |p - q| ≤ Df → |lagRate c' p - lagRate c' q| ≤ Df / tauUp := fun c' p q hpq =>
    (abs_lagRate_sub_thrust_le c' p q).trans (div_le_div_of_nonneg_right hpq tauUp_pos.le)
  exact ⟨k _ _ _ a, k _ _ _ b, k _ _ _ c, k _ _ _ d⟩

end diff

/-! ## Magnitudes of the field -/

section mag
variable (x : X) (u : Fin 4 → ℝ)

theorem abs_vf_v :
    |vf x u 3| ≤ amax * qnormSq x ∧ |vf x u 4| ≤ amax * qnormSq x ∧
      |vf x u 5| ≤ grav + amax * qnormSq x := by
  obtain ⟨d3, d4, d5⟩ := abs_down_le x
  have hA := abs_accel_le (thr x)
  have hQ := qnormSq_nonneg x
  refine ⟨?_, ?_, ?_⟩
  · rw [vf_3, abs_mul, abs_neg]; exact mul_le_mul hA d3 (abs_nonneg _) amax_pos.le
  · rw [vf_4, abs_mul, abs_neg]; exact mul_le_mul hA d4 (abs_nonneg _) amax_pos.le
  · rw [vf_5]
    calc _ ≤ |grav| + |-accel (thr x) * (x 6 * x 6 - x 7 * x 7 - x 8 * x 8 + x 9 * x 9)| :=
          abs_add_le _ _
      _ ≤ grav + amax * qnormSq x := by
          rw [abs_of_pos grav_pos, abs_mul, abs_neg]
          gcongr
          · exact amax_pos.le

theorem abs_vf_q {Rq Rw : ℝ} (hq : QBd x Rq) (hw : WBd x Rw) :
    |vf x u 6| ≤ (3 / 2) * (Rq * Rw) ∧ |vf x u 7| ≤ (3 / 2) * (Rq * Rw) ∧
      |vf x u 8| ≤ (3 / 2) * (Rq * Rw) ∧ |vf x u 9| ≤ (3 / 2) * (Rq * Rw) := by
  obtain ⟨x6, x7, x8, x9⟩ := hq
  obtain ⟨x10, x11, x12⟩ := hw
  have hRw : 0 ≤ Rw := (abs_nonneg _).trans x10
  have P : ∀ {i j : Fin 17}, |x i| ≤ Rq → |x j| ≤ Rw → |x i * x j| ≤ Rq * Rw := by
    intro i j a b; rw [abs_mul]; exact mul_le_mul a b (abs_nonneg _) ((abs_nonneg _).trans a)
  have T : ∀ {a b c : ℝ}, |a| ≤ Rq * Rw → |b| ≤ Rq * Rw → |c| ≤ Rq * Rw →
      |(a + b + c) / 2| ≤ (3 / 2) * (Rq * Rw) ∧ |(a + b - c) / 2| ≤ (3 / 2) * (Rq * Rw) ∧
      |(a - b + c) / 2| ≤ (3 / 2) * (Rq * Rw) ∧ |(-a - b - c) / 2| ≤ (3 / 2) * (Rq * Rw) := by
    intro a b c ha hb hc
    have := abs_le.mp ha; have := abs_le.mp hb; have := abs_le.mp hc
    refine ⟨?_, ?_, ?_, ?_⟩ <;> rw [abs_le] <;> constructor <;> linarith
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [show vf x u 6 = (-(x 7 * x 10) - x 8 * x 11 - x 9 * x 12) / 2 by rw [vf_6]; ring]
    exact (T (P x7 x10) (P x8 x11) (P x9 x12)).2.2.2
  · rw [show vf x u 7 = (x 6 * x 10 + x 8 * x 12 - x 9 * x 11) / 2 by rw [vf_7]; ring]
    exact (T (P x6 x10) (P x8 x12) (P x9 x11)).2.1
  · rw [show vf x u 8 = (x 6 * x 11 - x 7 * x 12 + x 9 * x 10) / 2 by rw [vf_8]; ring]
    exact (T (P x6 x11) (P x7 x12) (P x9 x10)).2.2.1
  · rw [show vf x u 9 = (x 6 * x 12 + x 7 * x 11 - x 8 * x 10) / 2 by rw [vf_9]; ring]
    exact (T (P x6 x12) (P x7 x11) (P x8 x10)).2.1

theorem abs_vf_w {Rw : ℝ} (hw : WBd x Rw) :
    |vf x u 10| ≤ alphaMax + gyro * Rw ^ 2 ∧ |vf x u 11| ≤ alphaMax + gyro * Rw ^ 2 ∧
      |vf x u 12| ≤ alphaMax + gyro * Rw ^ 2 := by
  obtain ⟨x10, x11, x12⟩ := hw
  have hg := gyro_nonneg
  have P : ∀ {i j : Fin 17}, |x i| ≤ Rw → |x j| ≤ Rw → |x i * x j| ≤ Rw ^ 2 := by
    intro i j a b; rw [abs_mul, sq]; exact mul_le_mul a b (abs_nonneg _) ((abs_nonneg _).trans a)
  have G : ∀ {c p : ℝ}, |c| ≤ gyro → |p| ≤ Rw ^ 2 → |c * p| ≤ gyro * Rw ^ 2 := by
    intro c p hc hp; rw [abs_mul]; exact mul_le_mul hc hp (abs_nonneg _) hg
  refine ⟨?_, ?_, ?_⟩
  · rw [show vf x u 10 = torqueX (thr x) / Jx + (-((Jz - Jy) / Jx)) * (x 11 * x 12) by
      rw [vf_10]; field_simp [Jx_pos.ne']; ring]
    exact (abs_add_le _ _).trans (add_le_add (abs_torqueX_div_le _) (G abs_gyroX_le (P x11 x12)))
  · rw [show vf x u 11 = torqueY (thr x) / Jy + (-((Jx - Jz) / Jy)) * (x 12 * x 10) by
      rw [vf_11]; field_simp [Jy_pos.ne']; ring]
    exact (abs_add_le _ _).trans (add_le_add (abs_torqueY_div_le _) (G abs_gyroY_le (P x12 x10)))
  · rw [show vf x u 12 = torqueZ (thr x) / Jz + (-((Jy - Jx) / Jz)) * (x 10 * x 11) by
      rw [vf_12]; field_simp [Jz_pos.ne']; ring]
    exact (abs_add_le _ _).trans (add_le_add (abs_torqueZ_div_le _) (G abs_gyroZ_le (P x10 x11)))

/-- The thrust rows: `|ḟᵢ| ≤ (1 + |fᵢ|) / tauUp` (the command is in `[0, 1]`). -/
theorem abs_vf_f {Rf : ℝ} (hf : FBd x Rf) :
    |vf x u 13| ≤ (1 + Rf) / tauUp ∧ |vf x u 14| ≤ (1 + Rf) / tauUp ∧
      |vf x u 15| ≤ (1 + Rf) / tauUp ∧ |vf x u 16| ≤ (1 + Rf) / tauUp := by
  obtain ⟨a, b, c, d⟩ := hf
  have k : ∀ (c' p : ℝ), 0 ≤ c' → c' ≤ 1 → |p| ≤ Rf → |lagRate c' p| ≤ (1 + Rf) / tauUp :=
    fun c' p h0 h1 hp => (abs_lagRate_le c' p).trans (div_le_div_of_nonneg_right (by
      have := abs_sub c' p; rw [abs_of_nonneg h0] at this; linarith) tauUp_pos.le)
  exact ⟨k _ _ (clip01_nonneg _) (clip01_le_one _) a, k _ _ (clip01_nonneg _) (clip01_le_one _) b,
    k _ _ (clip01_nonneg _) (clip01_le_one _) c, k _ _ (clip01_nonneg _) (clip01_le_one _) d⟩

end mag

/-! ## The sup-norm ball (the block lemmas are in `Plant.Lib.Blocks`) -/

/-- **The Lipschitz constant on the ball of radius `R`**:
`1 + 1/tauUp + 2 alphaMax + (8 amax + 3 + 2 gyro) R + 4 amax R²`. -/
def Klip (R : ℝ) : ℝ :=
  1 + 1 / tauUp + 2 * alphaMax + (8 * amax + 3 + 2 * gyro) * R + 4 * amax * R ^ 2

/-- **The bound of the field on the ball of radius `R`**:
`R + g + alphaMax + (1 + R)/tauUp + (4 amax + 2 + gyro) R²`. -/
def Mbd (R : ℝ) : ℝ := R + grav + alphaMax + (1 + R) / tauUp + (4 * amax + 2 + gyro) * R ^ 2

theorem Klip_pos {R : ℝ} (hR : 0 ≤ R) : 0 < Klip R := by
  have := amax_pos; have := tauUp_pos; have := alphaMax_pos; have := gyro_nonneg; unfold Klip; positivity

theorem Mbd_nonneg {R : ℝ} (hR : 0 ≤ R) : 0 ≤ Mbd R := by
  have := amax_pos; have := grav_pos; have := alphaMax_pos; have := tauUp_pos; have := gyro_nonneg
  unfold Mbd; positivity

/-- **`F(·, u)` is Lipschitz on every ball**, with constant `Klip R`. -/
theorem vf_lipschitz_ball (u : Fin 4 → ℝ) {R : ℝ} {x y : X} (hx : ‖x‖ ≤ R) (hy : ‖y‖ ≤ R) :
    ‖vf x u - vf y u‖ ≤ Klip R * ‖x - y‖ := by
  have hR : 0 ≤ R := (norm_nonneg _).trans hx
  set d := ‖x - y‖
  have hd : 0 ≤ d := norm_nonneg _
  have hA := amax_pos; have hτ := tauUp_pos; have hal := alphaMax_pos; have hg := gyro_nonneg
  have t1 : 0 ≤ 2 * alphaMax * d := by positivity
  have t2 : 0 ≤ amax * (R * d) := by positivity
  have t3 : 0 ≤ amax * (R * R * d) := by positivity
  have t4 : 0 ≤ d / tauUp := by positivity
  have t5 : 0 ≤ R * d := by positivity
  have t6 : 0 ≤ gyro * (R * d) := by positivity
  have e : Klip R * d = d + d / tauUp + 2 * alphaMax * d + 8 * (amax * (R * d)) + 3 * (R * d) +
      2 * (gyro * (R * d)) + 4 * (amax * (R * R * d)) := by unfold Klip; ring
  have k1 : d ≤ Klip R * d := by rw [e]; linarith
  have kv : amax * (8 * R * d + 4 * R ^ 2 * d) ≤ Klip R * d := by
    rw [e, show amax * (8 * R * d + 4 * R ^ 2 * d) = 8 * (amax * (R * d)) + 4 * (amax * (R * R * d)) by
      ring]; linarith
  have kq : (3 / 2) * (R * d + R * d) ≤ Klip R * d := by rw [e]; linarith
  have kw : gyro * (2 * R * d) + 2 * alphaMax * d ≤ Klip R * d := by
    rw [e, show gyro * (2 * R * d) = 2 * (gyro * (R * d)) by ring]; linarith
  have kf : d / tauUp ≤ Klip R * d := by rw [e]; linarith
  have hp := vf_sub_p (u := u) (VBd_of_norm_le (le_refl d))
  have hv := vf_sub_v (u := u) (QBd_of_norm_le hx) (QBd_of_norm_le hy) (QBd_of_norm_le (le_refl d))
    (FBd_of_norm_le (le_refl d))
  have hq := vf_sub_q (u := u) (QBd_of_norm_le hx) (WBd_of_norm_le hy) (QBd_of_norm_le (le_refl d))
    (WBd_of_norm_le (le_refl d))
  have hw := vf_sub_w (u := u) (WBd_of_norm_le hx) (WBd_of_norm_le hy) (WBd_of_norm_le (le_refl d))
    (FBd_of_norm_le (le_refl d))
  have hf := vf_sub_f (u := u) (FBd_of_norm_le (le_refl d))
  refine norm_le_of_abs_le (mul_nonneg (Klip_pos hR).le hd) fun i => ?_
  rw [Pi.sub_apply]
  fin_cases i
  · exact hp.1.trans k1
  · exact hp.2.1.trans k1
  · exact hp.2.2.trans k1
  · exact hv.1.trans kv
  · exact hv.2.1.trans kv
  · exact hv.2.2.trans kv
  · exact hq.1.trans kq
  · exact hq.2.1.trans kq
  · exact hq.2.2.1.trans kq
  · exact hq.2.2.2.trans kq
  · exact hw.1.trans kw
  · exact hw.2.1.trans kw
  · exact hw.2.2.trans kw
  · exact hf.1.trans kf
  · exact hf.2.1.trans kf
  · exact hf.2.2.1.trans kf
  · exact hf.2.2.2.trans kf

/-- **The field is bounded on every ball**: `‖F(x, u)‖ ≤ Mbd R` for `‖x‖ ≤ R`. -/
theorem norm_vf_le (u : Fin 4 → ℝ) {R : ℝ} {x : X} (hx : ‖x‖ ≤ R) : ‖vf x u‖ ≤ Mbd R := by
  have hR : 0 ≤ R := (norm_nonneg _).trans hx
  have hQ := qnormSq_le_of_norm_le hx
  have hA := amax_pos; have hg := grav_pos; have hal := alphaMax_pos; have hτ := tauUp_pos
  have hgy := gyro_nonneg
  have t1 : 0 ≤ (1 + R) / tauUp := by positivity
  have t2 : 0 ≤ amax * R ^ 2 := by positivity
  have t3 : 0 ≤ gyro * R ^ 2 := by positivity
  have t4 : 0 ≤ R ^ 2 := by positivity
  have e : Mbd R = R + grav + alphaMax + (1 + R) / tauUp + 4 * (amax * R ^ 2) + 2 * R ^ 2 +
      gyro * R ^ 2 := by unfold Mbd; ring
  have kp : R ≤ Mbd R := by rw [e]; linarith
  have hAQ : amax * qnormSq x ≤ 4 * (amax * R ^ 2) := by nlinarith
  have kv : grav + amax * qnormSq x ≤ Mbd R := by rw [e]; linarith
  have kv' : amax * qnormSq x ≤ Mbd R := by linarith
  have kq : (3 / 2) * (R * R) ≤ Mbd R := by rw [e, ← sq]; linarith
  have kw : alphaMax + gyro * R ^ 2 ≤ Mbd R := by rw [e]; linarith
  have kf : (1 + R) / tauUp ≤ Mbd R := by rw [e]; linarith
  obtain ⟨v3, v4, v5⟩ := abs_vf_v x u
  have hq := abs_vf_q x u (QBd_of_norm_le hx) (WBd_of_norm_le hx)
  have hw := abs_vf_w x u (WBd_of_norm_le hx)
  have hf := abs_vf_f x u (FBd_of_norm_le hx)
  obtain ⟨x3, x4, x5⟩ := VBd_of_norm_le hx
  refine norm_le_of_abs_le (Mbd_nonneg hR) fun i => ?_
  fin_cases i
  · exact (show |vf x u 0| ≤ R from x3).trans kp
  · exact (show |vf x u 1| ≤ R from x4).trans kp
  · exact (show |vf x u 2| ≤ R from x5).trans kp
  · exact v3.trans kv'
  · exact v4.trans kv'
  · exact v5.trans kv
  · exact hq.1.trans kq
  · exact hq.2.1.trans kq
  · exact hq.2.2.1.trans kq
  · exact hq.2.2.2.trans kq
  · exact hw.1.trans kw
  · exact hw.2.1.trans kw
  · exact hw.2.2.trans kw
  · exact hf.1.trans kf
  · exact hf.2.1.trans kf
  · exact hf.2.2.1.trans kf
  · exact hf.2.2.2.trans kf

end

end Plant
