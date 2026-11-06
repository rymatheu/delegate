import Contracts.Track.VerticalCertData

/-!
# The vertical Lyapunov certificate (TRACK_PLAN.md 3.4, milestone M5)

The identities between the rational matrices of `VerticalCertData.lean` are checked by the kernel
(`decide +kernel`: rational arithmetic on GMP numbers, no `native_decide`); everything else is
derived over `ℝ`:

* `Pv_posDef`: `Pv` is symmetric positive definite (`Pv = Lp · diag Dp · Lpᵀ`, `Dp > 0`, `Lp`
  invertible);
* `V_A`: `V (Av x) ≤ λ² V x` with `λ = 0.998`, from `λ² Pv - Avᵀ Pv Av = Lc · diag Dc · Lcᵀ`,
  `Dc ≥ 0`;
* `sq_ez_le`: `ez² ≤ γ V` (`γ Pv - e₀ e₀ᵀ = Lo · diag Do · Loᵀ`, `Do ≥ 0`);
* `V_iss`: `V (Av x + w) ≤ λ V x + V w / (1 - λ)`;
* `V_traj_le` and `ez_traj_le`: the discrete ISS bound and the induced bound on the vertical
  position error for any trajectory `x (k+1) = Av x k + w k`.
-/

namespace Contracts.Track.Vertical

open Matrix Finset

/-! ## Kernel checks of the certificate -/

theorem Pv_symm_Q : Pvᵀ = Pv := by decide +kernel

theorem certV : lamv ^ 2 • Pv - Avᵀ * Pv * Av = Lc * diagonal Dc * Lcᵀ := by decide +kernel

theorem Dc_nonneg : ∀ i, 0 ≤ Dc i := by decide +kernel

theorem certP : Pv = Lp * diagonal Dp * Lpᵀ := by decide +kernel

theorem Dp_pos : ∀ i, 0 < Dp i := by decide +kernel

theorem Lp_mul_inv : Lp * Lpinv = 1 := by decide +kernel

theorem certO : gamv • Pv - Matrix.single 0 0 1 = Lo * diagonal Do * Loᵀ := by decide +kernel

theorem Do_nonneg : ∀ i, 0 ≤ Do i := by decide +kernel

theorem Psum_eq : (∑ i, ∑ j, |Pv i j|) = Psum := by decide +kernel

/-! ## Over `ℝ` -/

/-- The cast of a rational matrix. -/
noncomputable abbrev castM (M : Matrix (Fin 8) (Fin 8) ℚ) : Matrix (Fin 8) (Fin 8) ℝ :=
  M.map (Rat.castHom ℝ)

theorem castM_mul (M N : Matrix (Fin 8) (Fin 8) ℚ) : castM (M * N) = castM M * castM N :=
  Matrix.map_mul

theorem castM_transpose (M : Matrix (Fin 8) (Fin 8) ℚ) : castM Mᵀ = (castM M)ᵀ :=
  (Matrix.transpose_map).symm

theorem castM_diagonal (d : Fin 8 → ℚ) :
    castM (diagonal d) = diagonal (fun i => (d i : ℝ)) := by
  simp [castM, Matrix.diagonal_map]

theorem castM_ldl {M L : Matrix (Fin 8) (Fin 8) ℚ} {d : Fin 8 → ℚ}
    (h : M = L * diagonal d * Lᵀ) :
    castM M = castM L * diagonal (fun i => (d i : ℝ)) * (castM L)ᵀ := by
  rw [h, castM_mul, castM_mul, castM_transpose, castM_diagonal]

theorem AvR_eq : AvR = castM Av := by
  ext i j; simp [AvR, castM]

/-- The Lyapunov matrix over `ℝ`. -/
noncomputable def PvR : Matrix (Fin 8) (Fin 8) ℝ := castM Pv

/-- The Lyapunov function `V x = xᵀ Pv x`. -/
noncomputable def V (x : Fin 8 → ℝ) : ℝ := qf PvR x

theorem PvR_symm : PvRᵀ = PvR := by
  rw [PvR, ← castM_transpose, Pv_symm_Q]

theorem V_nonneg (x : Fin 8 → ℝ) : 0 ≤ V x :=
  qf_nonneg_of_ldl _ _ _ (fun i => by exact_mod_cast (Dp_pos i).le) (castM_ldl certP) x

/-- `Pv` is symmetric positive definite. -/
theorem Pv_posDef : PvR.PosDef := by
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
  have e : PvR = castM Lp * diagonal (fun i => (Dp i : ℝ)) * (castM Lp)ᵀ := castM_ldl certP
  rw [e]
  convert h using 1

/-- **Contraction**: `V (Av x) ≤ λ² V x`. -/
theorem V_A (x : Fin 8 → ℝ) : V (AvR *ᵥ x) ≤ ((lamv : ℝ)) ^ 2 * V x := by
  have hM : castM (lamv ^ 2 • Pv - Avᵀ * Pv * Av) =
      ((lamv : ℝ)) ^ 2 • PvR - AvRᵀ * PvR * AvR := by
    rw [AvR_eq, PvR, ← castM_transpose, ← castM_mul, ← castM_mul]
    ext i j; simp [castM]
  have h := qf_nonneg_of_ldl _ _ _ (fun i => by exact_mod_cast Dc_nonneg i) (castM_ldl certV) x
  rw [hM, qf_smul_sub, ← qf_mulVec] at h
  simp only [V]; linarith

/-- **Output bound**: `ez² ≤ γ V`. -/
theorem sq_ez_le (x : Fin 8 → ℝ) : x 0 ^ 2 ≤ (gamv : ℝ) * V x := by
  have hM : castM (gamv • Pv - Matrix.single 0 0 1) =
      (gamv : ℝ) • PvR - Matrix.single 0 0 1 := by
    rw [PvR]; ext i j; simp [castM, Matrix.single_apply]; split_ifs <;> simp
  have h := qf_nonneg_of_ldl _ _ _ (fun i => by exact_mod_cast Do_nonneg i) (castM_ldl certO) x
  rw [hM, qf_smul_sub] at h
  have : qf (Matrix.single 0 0 1 : Matrix (Fin 8) (Fin 8) ℝ) x = x 0 ^ 2 := by
    simp [qf, dotProduct, mulVec, Matrix.single_apply, Fin.sum_univ_eight]; ring
  rw [this] at h; simp only [V]; linarith

theorem lamv_pos : (0 : ℝ) < lamv := by norm_num [lamv]
theorem lamv_lt_one : (lamv : ℝ) < 1 := by norm_num [lamv]

/-- **ISS step**: `V (Av x + w) ≤ λ V x + V w / (1 - λ)`. -/
theorem V_iss (x w : Fin 8 → ℝ) :
    V (AvR *ᵥ x + w) ≤ (lamv : ℝ) * V x + V w / (1 - lamv) :=
  qf_iss_step PvR AvR PvR_symm (fun z => V_nonneg z) lamv_pos lamv_lt_one (fun z => V_A z) x w

/-- `V` is nonincreasing along the free motion. -/
theorem V_A_le (x : Fin 8 → ℝ) : V (AvR *ᵥ x) ≤ V x := by
  have h := V_A x
  have h1 : ((lamv : ℝ)) ^ 2 ≤ 1 := by norm_num [lamv]
  nlinarith [V_nonneg x]

/-- `V w ≤ Psum ε²` when `|w i| ≤ ε`. -/
theorem V_le_of_abs_le (w : Fin 8 → ℝ) {ε : ℝ} (hw : ∀ i, |w i| ≤ ε) :
    V w ≤ (Psum : ℝ) * ε ^ 2 := by
  have h := qf_le_of_abs_le PvR w hw
  have e : (∑ i, ∑ j, |PvR i j|) = (Psum : ℝ) := by
    rw [← Psum_eq]; simp [PvR, castM]
  rwa [e] at h

/-- **Discrete ISS** for the vertical channel: along `x (k+1) = Av x k + w k` with
`V (w k) ≤ c k`, `V (x n) ≤ λⁿ V (x 0) + Σ_{k<n} λ^(n-1-k) c k / (1 - λ)`. -/
theorem V_traj_le (x w : ℕ → Fin 8 → ℝ) (c : ℕ → ℝ)
    (hx : ∀ k, x (k + 1) = AvR *ᵥ x k + w k) (hw : ∀ k, V (w k) ≤ c k) (n : ℕ) :
    V (x n) ≤ (lamv : ℝ) ^ n * V (x 0) +
      ∑ k ∈ range n, (lamv : ℝ) ^ (n - 1 - k) * (c k / (1 - lamv)) := by
  refine comparison (V := fun k => V (x k)) (c := fun k => c k / (1 - lamv)) lamv_pos.le
    (fun k => ?_) n
  rw [hx k]
  have h1 := V_iss (x k) (w k)
  have h2 : V (w k) / (1 - lamv) ≤ c k / (1 - lamv) :=
    div_le_div_of_nonneg_right (hw k) (by linarith [lamv_lt_one])
  linarith

/-- **The induced bound on the vertical position error**: under the hypotheses of `V_traj_le`,
`|ez n| ≤ √(γ (λⁿ V (x 0) + Σ_{k<n} λ^(n-1-k) c k / (1 - λ)))`. -/
theorem ez_traj_le (x w : ℕ → Fin 8 → ℝ) (c : ℕ → ℝ)
    (hx : ∀ k, x (k + 1) = AvR *ᵥ x k + w k) (hw : ∀ k, V (w k) ≤ c k) (n : ℕ) :
    |x n 0| ≤ Real.sqrt ((gamv : ℝ) * ((lamv : ℝ) ^ n * V (x 0) +
      ∑ k ∈ range n, (lamv : ℝ) ^ (n - 1 - k) * (c k / (1 - lamv)))) := by
  have hg : (0 : ℝ) ≤ gamv := by norm_num [gamv]
  have h1 := sq_ez_le (x n)
  have h2 := V_traj_le x w c hx hw n
  have h3 : (x n 0) ^ 2 ≤ (gamv : ℝ) * ((lamv : ℝ) ^ n * V (x 0) +
      ∑ k ∈ range n, (lamv : ℝ) ^ (n - 1 - k) * (c k / (1 - lamv))) :=
    h1.trans (mul_le_mul_of_nonneg_left h2 hg)
  exact Real.abs_le_sqrt h3

/-- The same with a constant disturbance bound: `|ez n| ≤ √(γ (λⁿ V (x 0) + c / (1 - λ)²))`. -/
theorem ez_traj_le_const (x w : ℕ → Fin 8 → ℝ) {c : ℝ} (hc : 0 ≤ c)
    (hx : ∀ k, x (k + 1) = AvR *ᵥ x k + w k) (hw : ∀ k, V (w k) ≤ c) (n : ℕ) :
    |x n 0| ≤ Real.sqrt ((gamv : ℝ) * ((lamv : ℝ) ^ n * V (x 0) + c / (1 - lamv) ^ 2)) := by
  have hg : (0 : ℝ) ≤ gamv := by norm_num [gamv]
  have hl1 : (0 : ℝ) < 1 - lamv := by linarith [lamv_lt_one]
  have h2 : V (x n) ≤ (lamv : ℝ) ^ n * V (x 0) + c / (1 - lamv) / (1 - lamv) := by
    refine comparison_const (V := fun k => V (x k)) lamv_pos.le lamv_lt_one (div_nonneg hc hl1.le)
      (fun k => ?_) n
    rw [hx k]
    have h1 := V_iss (x k) (w k)
    have := div_le_div_of_nonneg_right (hw k) hl1.le
    linarith
  have e : c / (1 - lamv) / (1 - lamv) = c / (1 - (lamv : ℝ)) ^ 2 := by
    rw [div_div, sq]
  rw [e] at h2
  exact Real.abs_le_sqrt ((sq_ez_le (x n)).trans (mul_le_mul_of_nonneg_left h2 hg))

end Contracts.Track.Vertical
