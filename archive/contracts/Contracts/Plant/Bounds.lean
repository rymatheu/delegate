module

public import Contracts.Plant.Field
public import Mathlib.Analysis.Normed.Group.Constructions
public import Mathlib.Tactic

/-!
# Bounds on the vector field

Every estimate is explicit. The actuators are clipped inside `vf`, so the thrust acceleration is in
`[0, amax]` (`accel_nonneg`, `accel_le`) and each angular acceleration of the torques is at most
`alphaMax = 2 · lever · fmax / Jx` (`abs_torqueX_div_le` etc.).

**Block bounds.** The coordinates split into blocks `p` (`0,1,2`), `v` (`3,4,5`), `q`
(`6,7,8,9`), `ω` (`10,11,12`). With `|qⱼ| ≤ Rq`, `|ωⱼ| ≤ Rw` at two states and coordinate
differences at most `Dv`, `Dq`, `Dw` in the blocks, each component of `vf x u - vf y u` is at most
* `Dv` in the `p` block (`ṗ = v`),
* `amax · 8 Rq Dq` in the `v` block (the down axis is quadratic in `q`),
* `(3/2)(Rq Dw + Rw Dq)` in the `q` block (bilinear kinematics),
* `gyro · 2 Rw Dw` in the `ω` block, `gyro = 11/20 ≥ |Jz - Jy| / Jx, |Jx - Jz| / Jy, |Jy - Jx| / Jz`
  (`vf_sub_p`, `vf_sub_v`, `vf_sub_q`, `vf_sub_w`).
On the sup-norm ball of radius `R` this gives the Lipschitz constant
`Klip R = 1 + (8 amax + 3) R` (`vf_lipschitz_ball`) and the bound
`‖vf x u‖ ≤ Mbd R = R + g + alphaMax + (4 amax + 2) R²` (`norm_vf_le`).
-/

@[expose] public section

namespace Contracts.Plant

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
        have : kmkf * Jx ≤ lever * Jz := by norm_num [kmkf, km, kf, Jx, lever, Jz]
        nlinarith [fmax_pos]

/-! ## Elementary estimates -/

/-- Difference of products: `|a b - a' b'| ≤ Ra Db + Rb Da` when `|a| ≤ Ra`, `|b'| ≤ Rb`,
`|a - a'| ≤ Da`, `|b - b'| ≤ Db`. -/
theorem abs_mul_sub_mul_le {a b a' b' Ra Rb Da Db : ℝ} (ha : |a| ≤ Ra) (hb : |b'| ≤ Rb)
    (hda : |a - a'| ≤ Da) (hdb : |b - b'| ≤ Db) : |a * b - a' * b'| ≤ Ra * Db + Rb * Da := by
  have e : a * b - a' * b' = a * (b - b') + (a - a') * b' := by ring
  rw [e]
  calc |a * (b - b') + (a - a') * b'| ≤ |a| * |b - b'| + |a - a'| * |b'| := by
        rw [← abs_mul, ← abs_mul]; exact abs_add_le _ _
    _ ≤ Ra * Db + Da * Rb := by
        gcongr
        · exact (abs_nonneg _).trans ha
        · exact (abs_nonneg _).trans hda
    _ = Ra * Db + Rb * Da := by ring

/-- `2 |a b| ≤ a² + b²`. -/
theorem two_abs_mul_le (a b : ℝ) : 2 * |a * b| ≤ a ^ 2 + b ^ 2 := by
  rw [abs_mul]; nlinarith [sq_nonneg (|a| - |b|), sq_abs a, sq_abs b]

/-! ## Block predicates -/

/-- The quaternion coordinates of `x` are at most `R` in absolute value. -/
def QBd (x : X) (R : ℝ) : Prop := |x 6| ≤ R ∧ |x 7| ≤ R ∧ |x 8| ≤ R ∧ |x 9| ≤ R

/-- The rate coordinates of `x` are at most `R` in absolute value. -/
def WBd (x : X) (R : ℝ) : Prop := |x 10| ≤ R ∧ |x 11| ≤ R ∧ |x 12| ≤ R

/-- The velocity coordinates of `x` are at most `R` in absolute value. -/
def VBd (x : X) (R : ℝ) : Prop := |x 3| ≤ R ∧ |x 4| ≤ R ∧ |x 5| ≤ R

/-- Squared Euclidean norm of the quaternion block. -/
def qnormSq (x : X) : ℝ := x 6 ^ 2 + x 7 ^ 2 + x 8 ^ 2 + x 9 ^ 2

/-- Twice the rotational kinetic energy, `ωᵀ J ω`. -/
def energy (x : X) : ℝ := Jx * x 10 ^ 2 + Jy * x 11 ^ 2 + Jz * x 12 ^ 2

theorem qnormSq_nonneg (x : X) : 0 ≤ qnormSq x := by unfold qnormSq; positivity

theorem energy_nonneg (x : X) : 0 ≤ energy x := by
  have := Jx_pos; have := Jy_pos; have := Jz_pos; unfold energy; positivity

/-- The coefficient of the gyroscopic coupling: `11/20 = (Jz - Jx)/Jx`. -/
def gyro : ℝ := 11 / 20

/-! ## Differences of the field, block by block -/

section diff
variable {x y : X} {u : Fin 4 → ℝ}

theorem vf_sub_p {Dv : ℝ} (hd : VBd (x - y) Dv) :
    |vf x u 0 - vf y u 0| ≤ Dv ∧ |vf x u 1 - vf y u 1| ≤ Dv ∧ |vf x u 2 - vf y u 2| ≤ Dv := by
  simpa [vf_0, vf_1, vf_2, VBd] using hd

theorem vf_sub_v {Rq Dq : ℝ} (hx : QBd x Rq) (hy : QBd y Rq) (hd : QBd (x - y) Dq) :
    |vf x u 3 - vf y u 3| ≤ amax * (8 * Rq * Dq) ∧ |vf x u 4 - vf y u 4| ≤ amax * (8 * Rq * Dq) ∧
      |vf x u 5 - vf y u 5| ≤ amax * (8 * Rq * Dq) := by
  obtain ⟨x6, x7, x8, x9⟩ := hx
  obtain ⟨y6, y7, y8, y9⟩ := hy
  obtain ⟨d6, d7, d8, d9⟩ := hd
  simp only [Pi.sub_apply] at d6 d7 d8 d9
  have hA := abs_accel_le u
  have hA0 := accel_nonneg u
  have hRq : 0 ≤ Rq := (abs_nonneg _).trans x6
  have hDq : 0 ≤ Dq := (abs_nonneg _).trans d6
  have key : ∀ e : ℝ, |e| ≤ 8 * Rq * Dq → |-(accel u) * e| ≤ amax * (8 * Rq * Dq) := by
    intro e he
    rw [abs_mul, abs_neg]
    exact mul_le_mul hA he (abs_nonneg _) amax_pos.le
  refine ⟨?_, ?_, ?_⟩
  · rw [vf_3, vf_3, ← mul_sub]
    apply key
    have e : 2 * (x 7 * x 9 + x 6 * x 8) - 2 * (y 7 * y 9 + y 6 * y 8) =
        2 * ((x 7 * x 9 - y 7 * y 9) + (x 6 * x 8 - y 6 * y 8)) := by ring
    rw [e, abs_mul, abs_two]
    have h1 := abs_mul_sub_mul_le x7 y9 d7 d9
    have h2 := abs_mul_sub_mul_le x6 y8 d6 d8
    have := abs_add_le (x 7 * x 9 - y 7 * y 9) (x 6 * x 8 - y 6 * y 8)
    nlinarith
  · rw [vf_4, vf_4, ← mul_sub]
    apply key
    have e : 2 * (x 8 * x 9 - x 6 * x 7) - 2 * (y 8 * y 9 - y 6 * y 7) =
        2 * ((x 8 * x 9 - y 8 * y 9) - (x 6 * x 7 - y 6 * y 7)) := by ring
    rw [e, abs_mul, abs_two]
    have h1 := abs_mul_sub_mul_le x8 y9 d8 d9
    have h2 := abs_mul_sub_mul_le x6 y7 d6 d7
    have := abs_sub (x 8 * x 9 - y 8 * y 9) (x 6 * x 7 - y 6 * y 7)
    nlinarith
  · rw [vf_5, vf_5, add_sub_add_left_eq_sub, ← mul_sub]
    apply key
    have e : (x 6 * x 6 - x 7 * x 7 - x 8 * x 8 + x 9 * x 9) -
        (y 6 * y 6 - y 7 * y 7 - y 8 * y 8 + y 9 * y 9) =
        (x 6 * x 6 - y 6 * y 6) - (x 7 * x 7 - y 7 * y 7) - (x 8 * x 8 - y 8 * y 8) +
          (x 9 * x 9 - y 9 * y 9) := by ring
    rw [e]
    have h1 := abs_mul_sub_mul_le x6 y6 d6 d6
    have h2 := abs_mul_sub_mul_le x7 y7 d7 d7
    have h3 := abs_mul_sub_mul_le x8 y8 d8 d8
    have h4 := abs_mul_sub_mul_le x9 y9 d9 d9
    have a1 := abs_sub (x 6 * x 6 - y 6 * y 6) (x 7 * x 7 - y 7 * y 7)
    have a2 := abs_sub ((x 6 * x 6 - y 6 * y 6) - (x 7 * x 7 - y 7 * y 7)) (x 8 * x 8 - y 8 * y 8)
    have a3 := abs_add_le ((x 6 * x 6 - y 6 * y 6) - (x 7 * x 7 - y 7 * y 7) -
      (x 8 * x 8 - y 8 * y 8)) (x 9 * x 9 - y 9 * y 9)
    nlinarith

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
  have P : ∀ {i j : Fin 13}, |x i| ≤ Rq → |y j| ≤ Rw → |x i - y i| ≤ Dq → |x j - y j| ≤ Dw →
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

theorem vf_sub_w {Rw Dw : ℝ} (hx : WBd x Rw) (hy : WBd y Rw) (hd : WBd (x - y) Dw) :
    |vf x u 10 - vf y u 10| ≤ gyro * (2 * Rw * Dw) ∧
      |vf x u 11 - vf y u 11| ≤ gyro * (2 * Rw * Dw) ∧
      |vf x u 12 - vf y u 12| ≤ gyro * (2 * Rw * Dw) := by
  obtain ⟨x10, x11, x12⟩ := hx
  obtain ⟨y10, y11, y12⟩ := hy
  obtain ⟨d10, d11, d12⟩ := hd
  simp only [Pi.sub_apply] at d10 d11 d12
  have hRw : 0 ≤ Rw := (abs_nonneg _).trans x10
  have hDw : 0 ≤ Dw := (abs_nonneg _).trans d10
  have hg : 0 ≤ gyro := by norm_num [gyro]
  refine ⟨?_, ?_, ?_⟩
  · have e : vf x u 10 - vf y u 10 = -((Jz - Jy) / Jx) * (x 11 * x 12 - y 11 * y 12) := by
      rw [vf_10, vf_10]; field_simp [Jx_pos.ne']; ring
    rw [e, abs_mul]
    have h1 : |-((Jz - Jy) / Jx)| ≤ gyro := by norm_num [Jx, Jy, Jz, gyro, abs_of_pos]
    have h2 := abs_mul_sub_mul_le x11 y12 d11 d12
    calc _ ≤ gyro * (Rw * Dw + Rw * Dw) := mul_le_mul h1 h2 (abs_nonneg _) hg
      _ = _ := by ring
  · have e : vf x u 11 - vf y u 11 = -((Jx - Jz) / Jy) * (x 12 * x 10 - y 12 * y 10) := by
      rw [vf_11, vf_11]; field_simp [Jy_pos.ne']; ring
    rw [e, abs_mul]
    have h1 : |-((Jx - Jz) / Jy)| ≤ gyro := by norm_num [Jx, Jy, Jz, gyro, abs_of_pos]
    have h2 := abs_mul_sub_mul_le x12 y10 d12 d10
    calc _ ≤ gyro * (Rw * Dw + Rw * Dw) := mul_le_mul h1 h2 (abs_nonneg _) hg
      _ = _ := by ring
  · have e : vf x u 12 - vf y u 12 = -((Jy - Jx) / Jz) * (x 10 * x 11 - y 10 * y 11) := by
      rw [vf_12, vf_12]; field_simp [Jz_pos.ne']; ring
    rw [e, abs_mul]
    have h1 : |-((Jy - Jx) / Jz)| ≤ gyro := by norm_num [Jx, Jy, Jz, gyro]
    have h2 := abs_mul_sub_mul_le x10 y11 d10 d11
    calc _ ≤ gyro * (Rw * Dw + Rw * Dw) := mul_le_mul h1 h2 (abs_nonneg _) hg
      _ = _ := by ring

end diff

/-! ## Magnitudes of the field -/

section mag
variable (x : X) (u : Fin 4 → ℝ)

/-- Each component of the down axis is at most `‖q‖²`. -/
theorem abs_down_le :
    |2 * (x 7 * x 9 + x 6 * x 8)| ≤ qnormSq x ∧ |2 * (x 8 * x 9 - x 6 * x 7)| ≤ qnormSq x ∧
      |x 6 * x 6 - x 7 * x 7 - x 8 * x 8 + x 9 * x 9| ≤ qnormSq x := by
  unfold qnormSq
  have a := two_abs_mul_le (x 7) (x 9); have b := two_abs_mul_le (x 6) (x 8)
  have c := two_abs_mul_le (x 8) (x 9); have d := two_abs_mul_le (x 6) (x 7)
  refine ⟨?_, ?_, ?_⟩
  · rw [abs_mul, abs_two]
    have := abs_add_le (x 7 * x 9) (x 6 * x 8); nlinarith
  · rw [abs_mul, abs_two]
    have := abs_sub (x 8 * x 9) (x 6 * x 7); nlinarith
  · rw [abs_le]; constructor <;> nlinarith [sq_nonneg (x 6), sq_nonneg (x 7), sq_nonneg (x 8),
      sq_nonneg (x 9)]

theorem abs_vf_v :
    |vf x u 3| ≤ amax * qnormSq x ∧ |vf x u 4| ≤ amax * qnormSq x ∧
      |vf x u 5| ≤ grav + amax * qnormSq x := by
  obtain ⟨d3, d4, d5⟩ := abs_down_le x
  have hA := abs_accel_le u
  have hQ := qnormSq_nonneg x
  refine ⟨?_, ?_, ?_⟩
  · rw [vf_3, abs_mul, abs_neg]; exact mul_le_mul hA d3 (abs_nonneg _) amax_pos.le
  · rw [vf_4, abs_mul, abs_neg]; exact mul_le_mul hA d4 (abs_nonneg _) amax_pos.le
  · rw [vf_5]
    calc _ ≤ |grav| + |-accel u * (x 6 * x 6 - x 7 * x 7 - x 8 * x 8 + x 9 * x 9)| :=
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
  have P : ∀ {i j : Fin 13}, |x i| ≤ Rq → |x j| ≤ Rw → |x i * x j| ≤ Rq * Rw := by
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
  have hg : 0 ≤ gyro := by norm_num [gyro]
  have P : ∀ {i j : Fin 13}, |x i| ≤ Rw → |x j| ≤ Rw → |x i * x j| ≤ Rw ^ 2 := by
    intro i j a b; rw [abs_mul, sq]; exact mul_le_mul a b (abs_nonneg _) ((abs_nonneg _).trans a)
  have G : ∀ {c p : ℝ}, |c| ≤ gyro → |p| ≤ Rw ^ 2 → |c * p| ≤ gyro * Rw ^ 2 := by
    intro c p hc hp; rw [abs_mul]; exact mul_le_mul hc hp (abs_nonneg _) hg
  refine ⟨?_, ?_, ?_⟩
  · rw [show vf x u 10 = torqueX u / Jx + (-((Jz - Jy) / Jx)) * (x 11 * x 12) by
      rw [vf_10]; field_simp [Jx_pos.ne']; ring]
    refine (abs_add_le _ _).trans (add_le_add (abs_torqueX_div_le u) (G ?_ (P x11 x12)))
    norm_num [Jx, Jy, Jz, gyro, abs_of_pos]
  · rw [show vf x u 11 = torqueY u / Jy + (-((Jx - Jz) / Jy)) * (x 12 * x 10) by
      rw [vf_11]; field_simp [Jy_pos.ne']; ring]
    refine (abs_add_le _ _).trans (add_le_add (abs_torqueY_div_le u) (G ?_ (P x12 x10)))
    norm_num [Jx, Jy, Jz, gyro, abs_of_pos]
  · rw [show vf x u 12 = torqueZ u / Jz + (-((Jy - Jx) / Jz)) * (x 10 * x 11) by
      rw [vf_12]; field_simp [Jz_pos.ne']; ring]
    refine (abs_add_le _ _).trans (add_le_add (abs_torqueZ_div_le u) (G ?_ (P x10 x11)))
    norm_num [Jx, Jy, Jz, gyro]

end mag

/-! ## The sup-norm ball -/

/-- A coordinate is at most the sup norm. -/
theorem abs_le_norm (x : X) (i : Fin 13) : |x i| ≤ ‖x‖ := by
  rw [← Real.norm_eq_abs]; exact norm_le_pi_norm x i

/-- The sup norm is at most `r` when every coordinate is. -/
theorem norm_le_of_abs_le {x : X} {r : ℝ} (hr : 0 ≤ r) (h : ∀ i, |x i| ≤ r) : ‖x‖ ≤ r :=
  (pi_norm_le_iff_of_nonneg hr).2 fun i => by rw [Real.norm_eq_abs]; exact h i

theorem QBd_of_norm_le {x : X} {R : ℝ} (h : ‖x‖ ≤ R) : QBd x R :=
  ⟨(abs_le_norm x 6).trans h, (abs_le_norm x 7).trans h, (abs_le_norm x 8).trans h,
    (abs_le_norm x 9).trans h⟩

theorem WBd_of_norm_le {x : X} {R : ℝ} (h : ‖x‖ ≤ R) : WBd x R :=
  ⟨(abs_le_norm x 10).trans h, (abs_le_norm x 11).trans h, (abs_le_norm x 12).trans h⟩

theorem VBd_of_norm_le {x : X} {R : ℝ} (h : ‖x‖ ≤ R) : VBd x R :=
  ⟨(abs_le_norm x 3).trans h, (abs_le_norm x 4).trans h, (abs_le_norm x 5).trans h⟩

/-- `‖q‖² ≤ 4 R²` on the ball of radius `R`. -/
theorem qnormSq_le_of_norm_le {x : X} {R : ℝ} (h : ‖x‖ ≤ R) : qnormSq x ≤ 4 * R ^ 2 := by
  obtain ⟨a, b, c, d⟩ := QBd_of_norm_le h
  unfold qnormSq
  have := sq_le_sq' (abs_le.mp a).1 (abs_le.mp a).2
  have := sq_le_sq' (abs_le.mp b).1 (abs_le.mp b).2
  have := sq_le_sq' (abs_le.mp c).1 (abs_le.mp c).2
  have := sq_le_sq' (abs_le.mp d).1 (abs_le.mp d).2
  linarith

/-- **The Lipschitz constant on the ball of radius `R`**: `1 + (8 amax + 3) R`. -/
def Klip (R : ℝ) : ℝ := 1 + (8 * amax + 3) * R

/-- **The bound of the field on the ball of radius `R`**: `R + g + alphaMax + (4 amax + 2) R²`. -/
def Mbd (R : ℝ) : ℝ := R + grav + alphaMax + (4 * amax + 2) * R ^ 2

theorem Klip_pos {R : ℝ} (hR : 0 ≤ R) : 0 < Klip R := by
  have := amax_pos; unfold Klip; positivity

theorem Mbd_nonneg {R : ℝ} (hR : 0 ≤ R) : 0 ≤ Mbd R := by
  have := amax_pos; have := grav_pos; have := alphaMax_pos; unfold Mbd; positivity

/-- **`F(·, u)` is Lipschitz on every ball**, with constant `Klip R`. -/
theorem vf_lipschitz_ball (u : Fin 4 → ℝ) {R : ℝ} {x y : X} (hx : ‖x‖ ≤ R) (hy : ‖y‖ ≤ R) :
    ‖vf x u - vf y u‖ ≤ Klip R * ‖x - y‖ := by
  have hR : 0 ≤ R := (norm_nonneg _).trans hx
  set d := ‖x - y‖
  have hd : 0 ≤ d := norm_nonneg _
  have hp := vf_sub_p (u := u) (VBd_of_norm_le (le_refl d))
  have hv := vf_sub_v (u := u) (QBd_of_norm_le hx) (QBd_of_norm_le hy) (QBd_of_norm_le (le_refl d))
  have hq := vf_sub_q (u := u) (QBd_of_norm_le hx) (WBd_of_norm_le hy) (QBd_of_norm_le (le_refl d))
    (WBd_of_norm_le (le_refl d))
  have hw := vf_sub_w (u := u) (WBd_of_norm_le hx) (WBd_of_norm_le hy) (WBd_of_norm_le (le_refl d))
  have hA := amax_pos
  have hRd := mul_nonneg hR hd
  have hARd := mul_nonneg (mul_nonneg hA.le hR) hd
  have k1 : d ≤ Klip R * d := by unfold Klip; nlinarith
  have kv : amax * (8 * R * d) ≤ Klip R * d := by unfold Klip; nlinarith
  have kq : (3 / 2) * (R * d + R * d) ≤ Klip R * d := by unfold Klip; nlinarith
  have kw : gyro * (2 * R * d) ≤ Klip R * d := by unfold Klip gyro; nlinarith
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

/-- **The field is bounded on every ball**: `‖F(x, u)‖ ≤ Mbd R` for `‖x‖ ≤ R`. -/
theorem norm_vf_le (u : Fin 4 → ℝ) {R : ℝ} {x : X} (hx : ‖x‖ ≤ R) : ‖vf x u‖ ≤ Mbd R := by
  have hR : 0 ≤ R := (norm_nonneg _).trans hx
  have hQ := qnormSq_le_of_norm_le hx
  obtain ⟨v3, v4, v5⟩ := abs_vf_v x u
  have hq := abs_vf_q x u (QBd_of_norm_le hx) (WBd_of_norm_le hx)
  have hw := abs_vf_w x u (WBd_of_norm_le hx)
  obtain ⟨x3, x4, x5⟩ := VBd_of_norm_le hx
  have hA := amax_pos; have hg := grav_pos; have hal := alphaMax_pos
  have kp : R ≤ Mbd R := by unfold Mbd; nlinarith
  have kv : grav + amax * qnormSq x ≤ Mbd R := by unfold Mbd; nlinarith
  have kv' : amax * qnormSq x ≤ Mbd R := by linarith
  have kq : (3 / 2) * (R * R) ≤ Mbd R := by unfold Mbd; nlinarith
  have kw : alphaMax + gyro * R ^ 2 ≤ Mbd R := by unfold Mbd gyro; nlinarith
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

end

end Contracts.Plant
