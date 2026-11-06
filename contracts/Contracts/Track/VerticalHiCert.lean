import Contracts.Track.VerticalHiCertData
import Contracts.Track.VerticalCert

/-!
# The vertical Lyapunov certificate at `PSC_D_ACC_P = 0.25`

The identities between the rational matrices of `VerticalHiCertData.lean` are checked by the
kernel (`decide +kernel`); over `ℝ`: `V x = xᵀ Pv x` is nonnegative (`Pv = Lp · diag Dp · Lpᵀ`,
`Dp > 0`) and contracts, `V (Av x) ≤ λ² V x` with `λ = 0.9995` (`λ² Pv - Avᵀ Pv Av =
Lc · diag Dc · Lcᵀ`, `Dc ≥ 0`). The bound on the powers of `Av` (`hpow`, Leg3GainV.lean) follows.
The generic tools (`castM`, `qf`, `qf_nonneg_of_ldl`) are `Vertical`'s.
-/

namespace Contracts.Track.VerticalHi

open Matrix Finset Contracts.Track.Vertical

theorem Pv_symm_Q : Pvᵀ = Pv := by decide +kernel

theorem certV : lamv ^ 2 • Pv - Avᵀ * Pv * Av = Lc * diagonal Dc * Lcᵀ := by decide +kernel

theorem Dc_nonneg : ∀ i, 0 ≤ Dc i := by decide +kernel

theorem certP : Pv = Lp * diagonal Dp * Lpᵀ := by decide +kernel

theorem Dp_pos : ∀ i, 0 < Dp i := by decide +kernel

theorem Lp_mul_inv : Lp * Lpinv = 1 := by decide +kernel

theorem AvR_eq : AvR = castM Av := by
  ext i j; simp [AvR, castM]

/-- The Lyapunov matrix over `ℝ`. -/
noncomputable def PvR : Matrix (Fin 8) (Fin 8) ℝ := castM Pv

/-- The Lyapunov function `V x = xᵀ Pv x`. -/
noncomputable def V (x : Fin 8 → ℝ) : ℝ := qf PvR x

theorem V_nonneg (x : Fin 8 → ℝ) : 0 ≤ V x :=
  qf_nonneg_of_ldl _ _ _ (fun i => by exact_mod_cast (Dp_pos i).le) (castM_ldl certP) x

/-- **Contraction**: `V (Av x) ≤ λ² V x`. -/
theorem V_A (x : Fin 8 → ℝ) : V (AvR *ᵥ x) ≤ ((lamv : ℝ)) ^ 2 * V x := by
  have hM : castM (lamv ^ 2 • Pv - Avᵀ * Pv * Av) =
      ((lamv : ℝ)) ^ 2 • PvR - AvRᵀ * PvR * AvR := by
    rw [AvR_eq, PvR, ← castM_transpose, ← castM_mul, ← castM_mul]
    ext i j; simp [castM]
  have h := qf_nonneg_of_ldl _ _ _ (fun i => by exact_mod_cast Dc_nonneg i) (castM_ldl certV) x
  rw [hM, qf_smul_sub, ← qf_mulVec] at h
  simp only [V]; linarith

end Contracts.Track.VerticalHi
