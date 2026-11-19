module

public import Plant.Lib.Real
public import Mathlib.Analysis.Normed.Group.Constructions
public import Mathlib.Analysis.Calculus.Deriv.Prod
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Data.Fin.VecNotation

/-!
# Blocks of the 13 coordinates

Model-free definitions and lemmas on `Fin 17 → ℝ` (the carrier `X` of the plant, with the sup
norm), by the block layout of the state: position `0,1,2`, velocity `3,4,5`, quaternion `6,…,9`,
rates `10,11,12`. The block bounds `QBd`, `WBd`, `VBd`, the quaternion block's squared norm
`qnormSq`, the attitude block `att`, and the columns of the (unnormalized) rotation matrix of the
quaternion block `col0`, `col1`, `dn` with `dnDot`. Moved here from the archive's `Bounds.lean`,
`Invariants.lean`, `Euler.lean` and `Sharp.lean` with their names and proofs unchanged; statements
read `Fin 17 → ℝ` where they read `X`.
-/

@[expose] public section

namespace Plant

noncomputable section

open Set

/-- The quaternion coordinates of `x` are at most `R` in absolute value. -/
def QBd (x : (Fin 17 → ℝ)) (R : ℝ) : Prop := |x 6| ≤ R ∧ |x 7| ≤ R ∧ |x 8| ≤ R ∧ |x 9| ≤ R

/-- The rate coordinates of `x` are at most `R` in absolute value. -/
def WBd (x : (Fin 17 → ℝ)) (R : ℝ) : Prop := |x 10| ≤ R ∧ |x 11| ≤ R ∧ |x 12| ≤ R

/-- The velocity coordinates of `x` are at most `R` in absolute value. -/
def VBd (x : (Fin 17 → ℝ)) (R : ℝ) : Prop := |x 3| ≤ R ∧ |x 4| ≤ R ∧ |x 5| ≤ R

/-- The thrust coordinates of `x` are at most `R` in absolute value. -/
def FBd (x : (Fin 17 → ℝ)) (R : ℝ) : Prop := |x 13| ≤ R ∧ |x 14| ≤ R ∧ |x 15| ≤ R ∧ |x 16| ≤ R

/-- Squared Euclidean norm of the quaternion block. -/
def qnormSq (x : (Fin 17 → ℝ)) : ℝ := x 6 ^ 2 + x 7 ^ 2 + x 8 ^ 2 + x 9 ^ 2

theorem qnormSq_nonneg (x : (Fin 17 → ℝ)) : 0 ≤ qnormSq x := by unfold qnormSq; positivity

/-- `‖q‖²` of a scaled state. -/
theorem qnormSq_smul (c : ℝ) (y : (Fin 17 → ℝ)) : qnormSq (c • y) = c ^ 2 * qnormSq y := by
  simp only [qnormSq, Pi.smul_apply, smul_eq_mul]; ring

theorem hasDerivAt_qnormSq {γ : ℝ → (Fin 17 → ℝ)} {γ' : (Fin 17 → ℝ)} {t : ℝ} (hγ : HasDerivAt γ γ' t) :
    HasDerivAt (fun s => qnormSq (γ s))
      (2 * (γ t 6 * γ' 6 + γ t 7 * γ' 7 + γ t 8 * γ' 8 + γ t 9 * γ' 9)) t := by
  have d := fun i => hasDerivAt_pi.1 hγ i
  have := ((((d 6).mul (d 6)).add ((d 7).mul (d 7))).add ((d 8).mul (d 8))).add ((d 9).mul (d 9))
  convert this using 1
  · funext s; simp only [qnormSq, Pi.add_apply, Pi.mul_apply]; ring
  · ring

/-- A coordinate is at most the sup norm. -/
theorem abs_le_norm (x : (Fin 17 → ℝ)) (i : Fin 17) : |x i| ≤ ‖x‖ := by
  rw [← Real.norm_eq_abs]; exact norm_le_pi_norm x i

/-- The sup norm is at most `r` when every coordinate is. -/
theorem norm_le_of_abs_le {x : (Fin 17 → ℝ)} {r : ℝ} (hr : 0 ≤ r) (h : ∀ i, |x i| ≤ r) : ‖x‖ ≤ r :=
  (pi_norm_le_iff_of_nonneg hr).2 fun i => by rw [Real.norm_eq_abs]; exact h i

theorem QBd_of_norm_le {x : (Fin 17 → ℝ)} {R : ℝ} (h : ‖x‖ ≤ R) : QBd x R :=
  ⟨(abs_le_norm x 6).trans h, (abs_le_norm x 7).trans h, (abs_le_norm x 8).trans h,
    (abs_le_norm x 9).trans h⟩

theorem WBd_of_norm_le {x : (Fin 17 → ℝ)} {R : ℝ} (h : ‖x‖ ≤ R) : WBd x R :=
  ⟨(abs_le_norm x 10).trans h, (abs_le_norm x 11).trans h, (abs_le_norm x 12).trans h⟩

theorem VBd_of_norm_le {x : (Fin 17 → ℝ)} {R : ℝ} (h : ‖x‖ ≤ R) : VBd x R :=
  ⟨(abs_le_norm x 3).trans h, (abs_le_norm x 4).trans h, (abs_le_norm x 5).trans h⟩

theorem FBd_of_norm_le {x : (Fin 17 → ℝ)} {R : ℝ} (h : ‖x‖ ≤ R) : FBd x R :=
  ⟨(abs_le_norm x 13).trans h, (abs_le_norm x 14).trans h, (abs_le_norm x 15).trans h,
    (abs_le_norm x 16).trans h⟩

/-- `‖q‖² ≤ 4 R²` on the ball of radius `R`. -/
theorem qnormSq_le_of_norm_le {x : (Fin 17 → ℝ)} {R : ℝ} (h : ‖x‖ ≤ R) : qnormSq x ≤ 4 * R ^ 2 := by
  obtain ⟨a, b, c, d⟩ := QBd_of_norm_le h
  unfold qnormSq
  have := sq_le_sq' (abs_le.mp a).1 (abs_le.mp a).2
  have := sq_le_sq' (abs_le.mp b).1 (abs_le.mp b).2
  have := sq_le_sq' (abs_le.mp c).1 (abs_le.mp c).2
  have := sq_le_sq' (abs_le.mp d).1 (abs_le.mp d).2
  linarith

theorem QBd_of_qnormSq_le {y : (Fin 17 → ℝ)} {Q : ℝ} (hQ : qnormSq y ≤ Q) : QBd y (Real.sqrt Q) := by
  unfold qnormSq at hQ
  have := sq_nonneg (y 6); have := sq_nonneg (y 7); have := sq_nonneg (y 8)
  have := sq_nonneg (y 9)
  exact ⟨Real.abs_le_sqrt (by linarith), Real.abs_le_sqrt (by linarith),
    Real.abs_le_sqrt (by linarith), Real.abs_le_sqrt (by linarith)⟩

theorem WBd_mono {x : (Fin 17 → ℝ)} {R R' : ℝ} (h : WBd x R) (hR : R ≤ R') : WBd x R' :=
  ⟨h.1.trans hR, h.2.1.trans hR, h.2.2.trans hR⟩

theorem QBd_one_of_unit {x : (Fin 17 → ℝ)} (hq : qnormSq x = 1) : QBd x 1 := by
  simpa using QBd_of_qnormSq_le (le_of_eq hq)

/-- Each component of the down axis is at most `‖q‖²`. -/
theorem abs_down_le (x : Fin 17 → ℝ) :
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

/-- The first column of the rotation of `q` (body forward axis in NED), times `‖q‖²`. -/
def col0 (x : (Fin 17 → ℝ)) : Fin 3 → ℝ :=
  ![x 6 * x 6 + x 7 * x 7 - x 8 * x 8 - x 9 * x 9, 2 * (x 7 * x 8 + x 6 * x 9),
    2 * (x 7 * x 9 - x 6 * x 8)]

/-- The second column of the rotation of `q` (body right axis in NED), times `‖q‖²`. -/
def col1 (x : (Fin 17 → ℝ)) : Fin 3 → ℝ :=
  ![2 * (x 7 * x 8 - x 6 * x 9), x 6 * x 6 - x 7 * x 7 + x 8 * x 8 - x 9 * x 9,
    2 * (x 8 * x 9 + x 6 * x 7)]

/-- The down axis `d(q)` (third column of the rotation, times `‖q‖²`), as in `downAxis`. -/
def dn (x : (Fin 17 → ℝ)) : Fin 3 → ℝ :=
  ![2 * (x 7 * x 9 + x 6 * x 8), 2 * (x 8 * x 9 - x 6 * x 7),
    x 6 * x 6 - x 7 * x 7 - x 8 * x 8 + x 9 * x 9]

/-- The time derivative of the down axis along the flow, `Dd(q)[q̇] = R(q) (ω × e_z)`
`= c₀ ω_y - c₁ ω_x`. -/
def dnDot (x : (Fin 17 → ℝ)) (j : Fin 3) : ℝ := col0 x j * x 11 - col1 x j * x 10

/-- The rows of the (unnormalized) rotation have length `‖q‖²`. -/
theorem row_sq (x : (Fin 17 → ℝ)) (j : Fin 3) :
    col0 x j ^ 2 + col1 x j ^ 2 + dn x j ^ 2 = qnormSq x ^ 2 := by
  fin_cases j <;> simp [col0, col1, dn, qnormSq] <;> ring

/-- **Cauchy-Schwarz with a rotation row**: for a unit quaternion,
`|c₀ⱼ a + c₁ⱼ b + dⱼ c| ≤ √(a² + b² + c²)`. -/
theorem abs_row_le {x : (Fin 17 → ℝ)} (hq : qnormSq x = 1) (j : Fin 3) (a b c : ℝ) :
    |col0 x j * a + col1 x j * b + dn x j * c| ≤ Real.sqrt (a ^ 2 + b ^ 2 + c ^ 2) := by
  apply Real.abs_le_sqrt
  have hr := row_sq x j
  rw [hq, one_pow] at hr
  set r0 := col0 x j; set r1 := col1 x j; set r2 := dn x j
  nlinarith [sq_nonneg (r0 * b - r1 * a), sq_nonneg (r0 * c - r2 * a), sq_nonneg (r1 * c - r2 * b)]

/-- **First derivative of the down axis**: `|ḋⱼ| ≤ √2 Ω` for a unit quaternion and rates at most
`Ω`. -/
theorem abs_dnDot_le {x : (Fin 17 → ℝ)} {Ω : ℝ} (hq : qnormSq x = 1) (hw : WBd x Ω) (j : Fin 3) :
    |dnDot x j| ≤ Real.sqrt 2 * Ω := by
  obtain ⟨w10, w11, -⟩ := hw
  have hΩ : 0 ≤ Ω := (abs_nonneg _).trans w10
  have e : dnDot x j = col0 x j * x 11 + col1 x j * (-x 10) + dn x j * 0 := by
    simp only [dnDot]; ring
  rw [e]
  refine (abs_row_le hq j _ _ _).trans ?_
  have s10 := sq_le_sq' (abs_le.mp w10).1 (abs_le.mp w10).2
  have s11 := sq_le_sq' (abs_le.mp w11).1 (abs_le.mp w11).2
  calc Real.sqrt (x 11 ^ 2 + (-x 10) ^ 2 + 0 ^ 2) ≤ Real.sqrt (2 * Ω ^ 2) :=
        Real.sqrt_le_sqrt (by nlinarith)
    _ = Real.sqrt 2 * Ω := by
        rw [Real.sqrt_mul (by norm_num), Real.sqrt_sq hΩ]

/-- The attitude block `(q, ω)` of a state, coordinates `6, …, 12`, with the sup norm. -/
def att (x : (Fin 17 → ℝ)) : Fin 7 → ℝ := fun i => x ⟨i.val + 6, by omega⟩

theorem abs_le_att_norm (x : (Fin 17 → ℝ)) (i : Fin 7) : |x ⟨i.val + 6, by omega⟩| ≤ ‖att x‖ := by
  rw [← Real.norm_eq_abs]; exact norm_le_pi_norm (att x) i

/-- The quaternion block `q`, coordinates `6, …, 9`, with the sup norm. -/
def quat (x : (Fin 17 → ℝ)) : Fin 4 → ℝ := fun i => x ⟨i.val + 6, by omega⟩

/-- The rate block `ω`, coordinates `10, 11, 12`, with the sup norm. -/
def rates (x : (Fin 17 → ℝ)) : Fin 3 → ℝ := fun i => x ⟨i.val + 10, by omega⟩

/-- The velocity block `v`, coordinates `3, 4, 5`. -/
def vel (x : (Fin 17 → ℝ)) : Fin 3 → ℝ := fun i => x ⟨i.val + 3, by omega⟩

/-- The thrust block `f`, coordinates `13, …, 16`, with the sup norm. -/
def mot (x : (Fin 17 → ℝ)) : Fin 4 → ℝ := fun i => x ⟨i.val + 13, by omega⟩

theorem quat_sub (x y : Fin 17 → ℝ) : quat (x - y) = quat x - quat y := rfl
theorem rates_sub (x y : Fin 17 → ℝ) : rates (x - y) = rates x - rates y := rfl
theorem mot_sub (x y : Fin 17 → ℝ) : mot (x - y) = mot x - mot y := rfl
theorem vel_sub (x y : Fin 17 → ℝ) : vel (x - y) = vel x - vel y := rfl

/-- A block bound from coordinate bounds. -/
theorem norm_block_le {n : ℕ} {b : Fin n → ℝ} {R : ℝ} (hR : 0 ≤ R) (h : ∀ i, |b i| ≤ R) : ‖b‖ ≤ R :=
  (pi_norm_le_iff_of_nonneg hR).2 fun i => by rw [Real.norm_eq_abs]; exact h i

/-- A coordinate bound from a block bound. -/
theorem abs_le_block {n : ℕ} (b : Fin n → ℝ) (i : Fin n) : |b i| ≤ ‖b‖ := by
  rw [← Real.norm_eq_abs]; exact norm_le_pi_norm b i

theorem QBd_of_quat {x : Fin 17 → ℝ} {R : ℝ} (h : ‖quat x‖ ≤ R) : QBd x R :=
  ⟨(abs_le_block (quat x) 0).trans h, (abs_le_block (quat x) 1).trans h,
    (abs_le_block (quat x) 2).trans h, (abs_le_block (quat x) 3).trans h⟩

theorem WBd_of_rates {x : Fin 17 → ℝ} {R : ℝ} (h : ‖rates x‖ ≤ R) : WBd x R :=
  ⟨(abs_le_block (rates x) 0).trans h, (abs_le_block (rates x) 1).trans h,
    (abs_le_block (rates x) 2).trans h⟩

theorem FBd_of_mot {x : Fin 17 → ℝ} {R : ℝ} (h : ‖mot x‖ ≤ R) : FBd x R :=
  ⟨(abs_le_block (mot x) 0).trans h, (abs_le_block (mot x) 1).trans h,
    (abs_le_block (mot x) 2).trans h, (abs_le_block (mot x) 3).trans h⟩

/-- **The down axis has Euclidean length `‖q‖²`.** -/
theorem sum_dn_sq (x : Fin 17 → ℝ) : ∑ j, dn x j ^ 2 = qnormSq x ^ 2 := by
  simp [Fin.sum_univ_three, dn, qnormSq]; ring

/-! ## Bounds from block bounds -/

/-- `‖q‖² ≤ 4 R²` from coordinate bounds. -/
theorem qnormSq_le_of_QBd {x : Fin 17 → ℝ} {R : ℝ} (h : QBd x R) : qnormSq x ≤ 4 * R ^ 2 := by
  obtain ⟨a, b, c, d⟩ := h
  unfold qnormSq
  have := sq_le_sq' (abs_le.mp a).1 (abs_le.mp a).2
  have := sq_le_sq' (abs_le.mp b).1 (abs_le.mp b).2
  have := sq_le_sq' (abs_le.mp c).1 (abs_le.mp c).2
  have := sq_le_sq' (abs_le.mp d).1 (abs_le.mp d).2
  linarith

/-- The down axis moves by at most `8 Rq Dq` per component. -/
theorem dn_sub_le {x y : Fin 17 → ℝ} {Rq Dq : ℝ} (hx : QBd x Rq) (hy : QBd y Rq) (hd : QBd (x - y) Dq) :
    |2 * (x 7 * x 9 + x 6 * x 8) - 2 * (y 7 * y 9 + y 6 * y 8)| ≤ 8 * Rq * Dq ∧
      |2 * (x 8 * x 9 - x 6 * x 7) - 2 * (y 8 * y 9 - y 6 * y 7)| ≤ 8 * Rq * Dq ∧
      |(x 6 * x 6 - x 7 * x 7 - x 8 * x 8 + x 9 * x 9) -
        (y 6 * y 6 - y 7 * y 7 - y 8 * y 8 + y 9 * y 9)| ≤ 8 * Rq * Dq := by
  obtain ⟨x6, x7, x8, x9⟩ := hx
  obtain ⟨y6, y7, y8, y9⟩ := hy
  obtain ⟨d6, d7, d8, d9⟩ := hd
  simp only [Pi.sub_apply] at d6 d7 d8 d9
  have hRq : 0 ≤ Rq := (abs_nonneg _).trans x6
  have hDq : 0 ≤ Dq := (abs_nonneg _).trans d6
  refine ⟨?_, ?_, ?_⟩
  · have e : 2 * (x 7 * x 9 + x 6 * x 8) - 2 * (y 7 * y 9 + y 6 * y 8) =
        2 * ((x 7 * x 9 - y 7 * y 9) + (x 6 * x 8 - y 6 * y 8)) := by ring
    rw [e, abs_mul, abs_two]
    have h1 := abs_mul_sub_mul_le x7 y9 d7 d9
    have h2 := abs_mul_sub_mul_le x6 y8 d6 d8
    have := abs_add_le (x 7 * x 9 - y 7 * y 9) (x 6 * x 8 - y 6 * y 8)
    nlinarith
  · have e : 2 * (x 8 * x 9 - x 6 * x 7) - 2 * (y 8 * y 9 - y 6 * y 7) =
        2 * ((x 8 * x 9 - y 8 * y 9) - (x 6 * x 7 - y 6 * y 7)) := by ring
    rw [e, abs_mul, abs_two]
    have h1 := abs_mul_sub_mul_le x8 y9 d8 d9
    have h2 := abs_mul_sub_mul_le x6 y7 d6 d7
    have := abs_sub (x 8 * x 9 - y 8 * y 9) (x 6 * x 7 - y 6 * y 7)
    nlinarith
  · have e : (x 6 * x 6 - x 7 * x 7 - x 8 * x 8 + x 9 * x 9) -
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

/-! ## Translation and yaw rotation of the coordinates (used by `Plant.Step.Symmetry`) -/

/-- The position shift by `a` as a state vector. -/
def posVec (a : Fin 3 → ℝ) : (Fin 17 → ℝ) := ![a 0, a 1, a 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

/-- **The yaw rotation** with `(c, s) = (cos ψ/2, sin ψ/2)`: position and velocity turned by
`Rz(ψ)`, attitude multiplied on the left by `(c, 0, 0, s)`, body rates and thrusts kept. -/
def yawRot (c s : ℝ) (x : (Fin 17 → ℝ)) : (Fin 17 → ℝ) :=
  ![(c ^ 2 - s ^ 2) * x 0 - 2 * c * s * x 1, 2 * c * s * x 0 + (c ^ 2 - s ^ 2) * x 1, x 2,
    (c ^ 2 - s ^ 2) * x 3 - 2 * c * s * x 4, 2 * c * s * x 3 + (c ^ 2 - s ^ 2) * x 4, x 5,
    c * x 6 - s * x 9, c * x 7 - s * x 8, c * x 8 + s * x 7, c * x 9 + s * x 6,
    x 10, x 11, x 12, x 13, x 14, x 15, x 16]

/-- The yaw rotation is a linear map. -/
def yawRotLin (c s : ℝ) : (Fin 17 → ℝ) →ₗ[ℝ] (Fin 17 → ℝ) where
  toFun := yawRot c s
  map_add' x y := by funext i; fin_cases i <;> simp [yawRot] <;> ring
  map_smul' a x := by funext i; fin_cases i <;> simp [yawRot] <;> ring

/-- The yaw rotation keeps `‖q‖²`. -/
theorem qnormSq_yawRot {c s : ℝ} (hcs : c ^ 2 + s ^ 2 = 1) (x : (Fin 17 → ℝ)) :
    qnormSq (yawRot c s x) = qnormSq x := by
  simp only [qnormSq, yawRot]
  simp
  linear_combination (x 6 ^ 2 + x 7 ^ 2 + x 8 ^ 2 + x 9 ^ 2) * hcs

end

end Plant
