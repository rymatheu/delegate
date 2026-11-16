import Contracts.Track.HorizontalCertData

/-!
# The horizontal Lyapunov certificate (TRACK_PLAN.md 3.4, milestone M6)

The identities between the rational matrices of `HorizontalCertData.lean` are checked by the kernel
(`decide +kernel`, no `native_decide`); everything else is derived over `ℝ`. For one horizontal
axis (`Ah`, `Horizontal.lean`):

* `Ph_posDef`: `Ph` is symmetric positive definite;
* `V_A`: `V (Ah x) ≤ λ² V x` with `λ = 0.9997`;
* `sq_e_le`: `e² ≤ γ V`;
* `V_iss`: `V (Ah x + w) ≤ λ V x + V w / (1 - λ)`;
* `V_traj_le`, `e_traj_le`, `e_traj_le_const`: the discrete ISS bound and the induced bound on the
  horizontal position error of any trajectory `x (k+1) = Ah x k + w k`.

The generic tools (quadratic forms, Young's inequality, the comparison lemma) are those of
`Vertical.lean`.
-/

namespace Contracts.Track.Horizontal

open Matrix Finset
open Contracts.Track.Vertical (qf qf_nonneg_of_ldl qf_mulVec qf_smul_sub qf_iss_step
  qf_le_of_abs_le comparison comparison_const)


/-! ## Kernel checks of the certificate -/

theorem Ph_symm_Q : Phᵀ = Ph := by decide +kernel

theorem certV : lamh ^ 2 • Ph - Ahᵀ * Ph * Ah = Lc * diagonal Dc * Lcᵀ := by decide +kernel

theorem Dc_nonneg : ∀ i, 0 ≤ Dc i := by decide +kernel

theorem certP : Ph = Lp * diagonal Dp * Lpᵀ := by decide +kernel

theorem Dp_pos : ∀ i, 0 < Dp i := by decide +kernel

theorem Lp_mul_inv : Lp * Lpinv = 1 := by decide +kernel

theorem certO : gamh • Ph - Matrix.single 0 0 1 = Lo * diagonal Do * Loᵀ := by decide +kernel

theorem Do_nonneg : ∀ i, 0 ≤ Do i := by decide +kernel

theorem Psumh_eq : (∑ i, ∑ j, |Ph i j|) = Psumh := by decide +kernel

/-! ## Over `ℝ` -/

/-- The cast of a rational matrix. -/
noncomputable abbrev castM (M : Matrix (Fin 9) (Fin 9) ℚ) : Matrix (Fin 9) (Fin 9) ℝ :=
  M.map (Rat.castHom ℝ)

theorem castM_mul (M N : Matrix (Fin 9) (Fin 9) ℚ) : castM (M * N) = castM M * castM N :=
  Matrix.map_mul

theorem castM_transpose (M : Matrix (Fin 9) (Fin 9) ℚ) : castM Mᵀ = (castM M)ᵀ :=
  (Matrix.transpose_map).symm

theorem castM_diagonal (d : Fin 9 → ℚ) :
    castM (diagonal d) = diagonal (fun i => (d i : ℝ)) := by
  simp [castM, Matrix.diagonal_map]

theorem castM_ldl {M L : Matrix (Fin 9) (Fin 9) ℚ} {d : Fin 9 → ℚ}
    (h : M = L * diagonal d * Lᵀ) :
    castM M = castM L * diagonal (fun i => (d i : ℝ)) * (castM L)ᵀ := by
  rw [h, castM_mul, castM_mul, castM_transpose, castM_diagonal]

theorem AhR_eq : AhR = castM Ah := by
  ext i j; simp [AhR, castM]

/-- The Lyapunov matrix over `ℝ`. -/
noncomputable def PhR : Matrix (Fin 9) (Fin 9) ℝ := castM Ph

/-- The Lyapunov function `V x = xᵀ Ph x`. -/
noncomputable def V (x : Fin 9 → ℝ) : ℝ := qf PhR x

theorem PhR_symm : PhRᵀ = PhR := by
  rw [PhR, ← castM_transpose, Ph_symm_Q]

theorem V_nonneg (x : Fin 9 → ℝ) : 0 ≤ V x :=
  qf_nonneg_of_ldl _ _ _ (fun i => by exact_mod_cast (Dp_pos i).le) (castM_ldl certP) x

/-- `Ph` is symmetric positive definite. -/
theorem Ph_posDef : PhR.PosDef := by
  have hD : (diagonal (fun i => (Dp i : ℝ))).PosDef :=
    PosDef.diagonal (fun i => by exact_mod_cast Dp_pos i)
  have hinj : Function.Injective (castM Lp)ᵀ.mulVec := by
    intro x y hxy
    have hinv : (castM Lpinv)ᵀ * (castM Lp)ᵀ = 1 := by
      rw [← transpose_mul, ← castM_mul, Lp_mul_inv]
      ext i j; simp only [castM, transpose_apply, map_apply]; rw [Matrix.one_apply, Matrix.one_apply]
      by_cases hij : i = j <;> simp [hij, eq_comm]
    have := congrArg ((castM Lpinv)ᵀ.mulVec) hxy
    simpa [mulVec_mulVec, hinv] using this
  have h := hD.conjTranspose_mul_mul_same hinj
  rw [conjTranspose_eq_transpose_of_trivial, transpose_transpose] at h
  have e : PhR = castM Lp * diagonal (fun i => (Dp i : ℝ)) * (castM Lp)ᵀ := castM_ldl certP
  rw [e]
  convert h using 1

/-- **Contraction**: `V (Ah x) ≤ λ² V x`. -/
theorem V_A (x : Fin 9 → ℝ) : V (AhR *ᵥ x) ≤ ((lamh : ℝ)) ^ 2 * V x := by
  have hM : castM (lamh ^ 2 • Ph - Ahᵀ * Ph * Ah) =
      ((lamh : ℝ)) ^ 2 • PhR - AhRᵀ * PhR * AhR := by
    rw [AhR_eq, PhR, ← castM_transpose, ← castM_mul, ← castM_mul]
    ext i j; simp [castM]
  have h := qf_nonneg_of_ldl _ _ _ (fun i => by exact_mod_cast Dc_nonneg i) (castM_ldl certV) x
  rw [hM, qf_smul_sub, ← qf_mulVec] at h
  simp only [V]; linarith

/-- **Output bound**: `e² ≤ γ V`. -/
theorem sq_e_le (x : Fin 9 → ℝ) : x 0 ^ 2 ≤ (gamh : ℝ) * V x := by
  have hM : castM (gamh • Ph - Matrix.single 0 0 1) =
      (gamh : ℝ) • PhR - Matrix.single 0 0 1 := by
    rw [PhR]; ext i j; simp [castM, Matrix.single_apply]; split_ifs <;> simp
  have h := qf_nonneg_of_ldl _ _ _ (fun i => by exact_mod_cast Do_nonneg i) (castM_ldl certO) x
  rw [hM, qf_smul_sub] at h
  have : qf (Matrix.single 0 0 1 : Matrix (Fin 9) (Fin 9) ℝ) x = x 0 ^ 2 := by
    simp [qf, dotProduct, mulVec, Matrix.single_apply, Fin.sum_univ_succ]; ring
  rw [this] at h; simp only [V]; linarith

theorem lamh_pos : (0 : ℝ) < lamh := by norm_num [lamh]
theorem lamh_lt_one : (lamh : ℝ) < 1 := by norm_num [lamh]

/-- **ISS step**: `V (Ah x + w) ≤ λ V x + V w / (1 - λ)`. -/
theorem V_iss (x w : Fin 9 → ℝ) :
    V (AhR *ᵥ x + w) ≤ (lamh : ℝ) * V x + V w / (1 - lamh) :=
  qf_iss_step PhR AhR PhR_symm (fun z => V_nonneg z) lamh_pos lamh_lt_one (fun z => V_A z) x w

/-- `V` is nonincreasing along the free motion. -/
theorem V_A_le (x : Fin 9 → ℝ) : V (AhR *ᵥ x) ≤ V x := by
  have h := V_A x
  have h1 : ((lamh : ℝ)) ^ 2 ≤ 1 := by norm_num [lamh]
  nlinarith [V_nonneg x]

/-- `V w ≤ Psumh ε²` when `|w i| ≤ ε`. -/
theorem V_le_of_abs_le (w : Fin 9 → ℝ) {ε : ℝ} (hw : ∀ i, |w i| ≤ ε) :
    V w ≤ (Psumh : ℝ) * ε ^ 2 := by
  have h := qf_le_of_abs_le PhR w hw
  have e : (∑ i, ∑ j, |PhR i j|) = (Psumh : ℝ) := by
    rw [← Psumh_eq]; simp [PhR, castM]
  rwa [e] at h

/-- **Discrete ISS** for one horizontal axis: along `x (k+1) = Ah x k + w k` with
`V (w k) ≤ c k`, `V (x n) ≤ λⁿ V (x 0) + Σ_{k<n} λ^(n-1-k) c k / (1 - λ)`. -/
theorem V_traj_le (x w : ℕ → Fin 9 → ℝ) (c : ℕ → ℝ)
    (hx : ∀ k, x (k + 1) = AhR *ᵥ x k + w k) (hw : ∀ k, V (w k) ≤ c k) (n : ℕ) :
    V (x n) ≤ (lamh : ℝ) ^ n * V (x 0) +
      ∑ k ∈ range n, (lamh : ℝ) ^ (n - 1 - k) * (c k / (1 - lamh)) := by
  refine comparison (V := fun k => V (x k)) (c := fun k => c k / (1 - lamh)) lamh_pos.le
    (fun k => ?_) n
  rw [hx k]
  have h1 := V_iss (x k) (w k)
  have h2 : V (w k) / (1 - lamh) ≤ c k / (1 - lamh) :=
    div_le_div_of_nonneg_right (hw k) (by linarith [lamh_lt_one])
  linarith

/-- **The induced bound on the horizontal position error (one axis)**: under the hypotheses of `V_traj_le`,
`|e n| ≤ √(γ (λⁿ V (x 0) + Σ_{k<n} λ^(n-1-k) c k / (1 - λ)))`. -/
theorem e_traj_le (x w : ℕ → Fin 9 → ℝ) (c : ℕ → ℝ)
    (hx : ∀ k, x (k + 1) = AhR *ᵥ x k + w k) (hw : ∀ k, V (w k) ≤ c k) (n : ℕ) :
    |x n 0| ≤ Real.sqrt ((gamh : ℝ) * ((lamh : ℝ) ^ n * V (x 0) +
      ∑ k ∈ range n, (lamh : ℝ) ^ (n - 1 - k) * (c k / (1 - lamh)))) := by
  have hg : (0 : ℝ) ≤ gamh := by norm_num [gamh]
  have h1 := sq_e_le (x n)
  have h2 := V_traj_le x w c hx hw n
  have h3 : (x n 0) ^ 2 ≤ (gamh : ℝ) * ((lamh : ℝ) ^ n * V (x 0) +
      ∑ k ∈ range n, (lamh : ℝ) ^ (n - 1 - k) * (c k / (1 - lamh))) :=
    h1.trans (mul_le_mul_of_nonneg_left h2 hg)
  exact Real.abs_le_sqrt h3

/-- The same with a constant disturbance bound: `|e n| ≤ √(γ (λⁿ V (x 0) + c / (1 - λ)²))`. -/
theorem e_traj_le_const (x w : ℕ → Fin 9 → ℝ) {c : ℝ} (hc : 0 ≤ c)
    (hx : ∀ k, x (k + 1) = AhR *ᵥ x k + w k) (hw : ∀ k, V (w k) ≤ c) (n : ℕ) :
    |x n 0| ≤ Real.sqrt ((gamh : ℝ) * ((lamh : ℝ) ^ n * V (x 0) + c / (1 - lamh) ^ 2)) := by
  have hg : (0 : ℝ) ≤ gamh := by norm_num [gamh]
  have hl1 : (0 : ℝ) < 1 - lamh := by linarith [lamh_lt_one]
  have h2 : V (x n) ≤ (lamh : ℝ) ^ n * V (x 0) + c / (1 - lamh) / (1 - lamh) := by
    refine comparison_const (V := fun k => V (x k)) lamh_pos.le lamh_lt_one (div_nonneg hc hl1.le)
      (fun k => ?_) n
    rw [hx k]
    have h1 := V_iss (x k) (w k)
    have := div_le_div_of_nonneg_right (hw k) hl1.le
    linarith
  have e : c / (1 - lamh) / (1 - lamh) = c / (1 - (lamh : ℝ)) ^ 2 := by
    rw [div_div, sq]
  rw [e] at h2
  exact Real.abs_le_sqrt ((sq_e_le (x n)).trans (mul_le_mul_of_nonneg_left h2 hg))

end Contracts.Track.Horizontal
