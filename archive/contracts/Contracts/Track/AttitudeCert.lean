import Contracts.Track.AttitudeJointCertData

/-!
# The attitude certificate: the joint horizontal–attitude axis (milestone (1) of REACH.md)

`AttitudeJoint.lean` gives one horizontal NED axis of the closed loop in the linear regime as an
exact rational model with 14 states and 7 inputs (`jtick σ x u = Ajσ x + Bj u`, `jtick_eq0`,
`jtick_eq1`): the position controller (`AC_P_2D`, `AC_PID_2D`), the attitude input shaping in its
linear zone (with the `sqrt_controller_accel` switch `σ ∈ {0, 1}`), the angle P controller, the rate
PID, the mixer and the rigid body's attitude and position rows. The attitude states are scaled by
`g`, so the tilt error from the commanded tilt is the state `a` (index 7) in m/s².

`AttitudeJointCertData.lean` holds a common quadratic Lyapunov matrix `Pj` of both modes and exact
`L D Lᵀ` factorizations. This file checks them in the kernel (`decide +kernel`: rational arithmetic
on GMP numbers, no `native_decide`) and derives over `ℝ`:

* `V_nonneg`: `V x = xᵀ Pj x ≥ 0` (`Pj = Lp · diag Dp · Lpᵀ`, `Dp > 0`);
* `V_A0`, `V_A1`: `V (Ajσ x) ≤ λ² V x` for both modes, `λ = 0.9997` (a common Lyapunov function
  of the switched system: any switching sequence of the shaping is stable);
* `out_sq_le`: for each watched output `c` (position error `e`, velocity error `ev`, the PID states
  `E, D, I`, the tilt error `a`, the tilt `s`, the rate `w`, the command `c`, the shaping error `es`,
  the rate-loop output `uu`, the shaping accelerations `al0, al1` and their one-tick changes
  `dal`), `(c ⬝ x)² ≤ γ_c V x`, from `Lp y = c` and `Σ yᵢ²/Dpᵢ ≤ γ_c` (`cᵀ Pj⁻¹ c ≤ γ_c`);
* `V_iss_sw`: `V (Ajσ x + w) ≤ λ V x + V w / (1 - λ)` for both modes;
* `V_traj_sw`: the discrete ISS bound along `x (k+1) = Aj(σ k) x k + w k` for any switching
  sequence `σ`.

The no-saturation region is the sublevel set of `V` on which every watched output stays inside its
linear zone; `out_sq_le` turns a level `V ≤ ν` into the bound `|c ⬝ x| ≤ √(γ_c ν)` for each output.
-/

namespace Contracts.Track.AttJ

open Matrix Finset
open Contracts.Track.Vertical (qf qf_nonneg_of_ldl qf_mulVec qf_smul_sub qf_iss_step comparison)

/-! ## Kernel checks -/

theorem Pj_symm_Q : Pjᵀ = Pj := by decide +kernel

theorem certA0 : lamj ^ 2 • Pj - Aj0ᵀ * Pj * Aj0 = Lc0 * diagonal Dc0 * Lc0ᵀ := by decide +kernel

theorem certA1 : lamj ^ 2 • Pj - Aj1ᵀ * Pj * Aj1 = Lc1 * diagonal Dc1 * Lc1ᵀ := by decide +kernel

theorem Dc0_nonneg : ∀ i, 0 ≤ Dc0 i := by decide +kernel

theorem Dc1_nonneg : ∀ i, 0 ≤ Dc1 i := by decide +kernel

theorem certP : Pj = Lp * diagonal Dp * Lpᵀ := by decide +kernel

theorem Dp_pos : ∀ i, 0 < Dp i := by decide +kernel

/-- An output certificate: `Lp y = c` and `Σ yᵢ² / Dpᵢ ≤ γ`. -/
def OutCert (c y : Fin 14 → ℚ) (γ : ℚ) : Prop := Lp *ᵥ y = c ∧ (∑ i, y i ^ 2 / Dp i) ≤ γ

instance (c y : Fin 14 → ℚ) (γ : ℚ) : Decidable (OutCert c y γ) := by
  unfold OutCert; infer_instance

theorem cert_e : OutCert c_e y_e g_e := by decide +kernel
theorem cert_ev : OutCert c_ev y_ev g_ev := by decide +kernel
theorem cert_E : OutCert c_E y_E g_E := by decide +kernel
theorem cert_D : OutCert c_D y_D g_D := by decide +kernel
theorem cert_I : OutCert c_I y_I g_I := by decide +kernel
theorem cert_a : OutCert c_a y_a g_a := by decide +kernel
theorem cert_es : OutCert c_es y_es g_es := by decide +kernel
theorem cert_uu : OutCert c_uu y_uu g_uu := by decide +kernel
theorem cert_c : OutCert c_c y_c g_c := by decide +kernel
theorem cert_s : OutCert c_s y_s g_s := by decide +kernel
theorem cert_w : OutCert c_w y_w g_w := by decide +kernel
theorem cert_al0 : OutCert c_al0 y_al0 g_al0 := by decide +kernel
theorem cert_al1 : OutCert c_al1 y_al1 g_al1 := by decide +kernel
theorem cert_dal00 : OutCert c_dal00 y_dal00 g_dal00 := by decide +kernel
theorem cert_dal01 : OutCert c_dal01 y_dal01 g_dal01 := by decide +kernel
theorem cert_dal10 : OutCert c_dal10 y_dal10 g_dal10 := by decide +kernel
theorem cert_dal11 : OutCert c_dal11 y_dal11 g_dal11 := by decide +kernel

/-! ## Over `ℝ` -/

abbrev M14 := Matrix (Fin 14) (Fin 14) ℚ

theorem castM_mul (M N : M14) : castM (M * N) = castM M * castM N := Matrix.map_mul

theorem castM_transpose (M : M14) : castM Mᵀ = (castM M)ᵀ := (Matrix.transpose_map).symm

theorem castM_diagonal (d : Fin 14 → ℚ) :
    castM (diagonal d) = diagonal (fun i => (d i : ℝ)) := by
  simp [castM, Matrix.diagonal_map]

theorem castM_ldl {M L : M14} {d : Fin 14 → ℚ} (h : M = L * diagonal d * Lᵀ) :
    castM M = castM L * diagonal (fun i => (d i : ℝ)) * (castM L)ᵀ := by
  rw [h, castM_mul, castM_mul, castM_transpose, castM_diagonal]

/-- The Lyapunov matrix over `ℝ`. -/
noncomputable def PjR : Matrix (Fin 14) (Fin 14) ℝ := castM Pj

/-- The Lyapunov function of the joint axis, `V x = xᵀ Pj x`. -/
noncomputable def V (x : Fin 14 → ℝ) : ℝ := qf PjR x

theorem PjR_symm : PjRᵀ = PjR := by
  rw [PjR, ← castM_transpose, Pj_symm_Q]

theorem V_nonneg (x : Fin 14 → ℝ) : 0 ≤ V x :=
  qf_nonneg_of_ldl _ _ _ (fun i => by exact_mod_cast (Dp_pos i).le) (castM_ldl certP) x

/-- The mode matrices over `ℝ`. -/
noncomputable def AjR (σ : Fin 2) : Matrix (Fin 14) (Fin 14) ℝ :=
  if σ = 0 then castM Aj0 else castM Aj1

theorem V_A_of {A : M14} {L : M14} {d : Fin 14 → ℚ} (hd : ∀ i, 0 ≤ d i)
    (hc : lamj ^ 2 • Pj - Aᵀ * Pj * A = L * diagonal d * Lᵀ) (x : Fin 14 → ℝ) :
    V (castM A *ᵥ x) ≤ ((lamj : ℝ)) ^ 2 * V x := by
  have hM : castM (lamj ^ 2 • Pj - Aᵀ * Pj * A) =
      ((lamj : ℝ)) ^ 2 • PjR - (castM A)ᵀ * PjR * castM A := by
    rw [PjR, ← castM_transpose, ← castM_mul, ← castM_mul]
    ext i j; simp [castM]
  have h := qf_nonneg_of_ldl _ _ _ (fun i => by exact_mod_cast hd i) (castM_ldl hc) x
  rw [hM, qf_smul_sub, ← qf_mulVec] at h
  simp only [V]; linarith

/-- **Contraction, mode `σ = 0`**: `V (Aj0 x) ≤ λ² V x`. -/
theorem V_A0 (x : Fin 14 → ℝ) : V (castM Aj0 *ᵥ x) ≤ ((lamj : ℝ)) ^ 2 * V x :=
  V_A_of Dc0_nonneg certA0 x

/-- **Contraction, mode `σ = 1`**: `V (Aj1 x) ≤ λ² V x`. -/
theorem V_A1 (x : Fin 14 → ℝ) : V (castM Aj1 *ᵥ x) ≤ ((lamj : ℝ)) ^ 2 * V x :=
  V_A_of Dc1_nonneg certA1 x

/-- **Contraction in either mode.** -/
theorem V_A (σ : Fin 2) (x : Fin 14 → ℝ) : V (AjR σ *ᵥ x) ≤ ((lamj : ℝ)) ^ 2 * V x := by
  unfold AjR; split_ifs
  · exact V_A0 x
  · exact V_A1 x

theorem lamj_pos : (0 : ℝ) < lamj := by norm_num [lamj]
theorem lamj_lt_one : (lamj : ℝ) < 1 := by norm_num [lamj]

/-- **ISS step in either mode**: `V (Ajσ x + w) ≤ λ V x + V w / (1 - λ)`. -/
theorem V_iss_sw (σ : Fin 2) (x w : Fin 14 → ℝ) :
    V (AjR σ *ᵥ x + w) ≤ (lamj : ℝ) * V x + V w / (1 - lamj) :=
  qf_iss_step PjR (AjR σ) PjR_symm (fun z => V_nonneg z) lamj_pos lamj_lt_one (fun z => V_A σ z) x w

/-- **Discrete ISS for the switched joint axis**: along `x (k+1) = Aj(σ k) x k + w k` with
`V (w k) ≤ c k`, `V (x n) ≤ λⁿ V (x 0) + Σ_{k<n} λ^(n-1-k) c k / (1 - λ)`, for every switching
sequence `σ`. -/
theorem V_traj_sw (σ : ℕ → Fin 2) (x w : ℕ → Fin 14 → ℝ) (c : ℕ → ℝ)
    (hx : ∀ k, x (k + 1) = AjR (σ k) *ᵥ x k + w k) (hw : ∀ k, V (w k) ≤ c k) (n : ℕ) :
    V (x n) ≤ (lamj : ℝ) ^ n * V (x 0) +
      ∑ k ∈ range n, (lamj : ℝ) ^ (n - 1 - k) * (c k / (1 - lamj)) := by
  refine comparison (V := fun k => V (x k)) (c := fun k => c k / (1 - lamj)) lamj_pos.le
    (fun k => ?_) n
  rw [hx k]
  have h1 := V_iss_sw (σ k) (x k) (w k)
  have h2 : V (w k) / (1 - lamj) ≤ c k / (1 - lamj) :=
    div_le_div_of_nonneg_right (hw k) (by linarith [lamj_lt_one])
  linarith

/-- The model tick is the switched linear map: `jtick σ x u = Ajσ x + Bj u`. -/
theorem jtick_eq_sw (σ : Fin 2) (x : Fin 14 → ℝ) (u : Fin 7 → ℝ) :
    jtick (σ : ℝ) x u = AjR σ *ᵥ x + castM Bj *ᵥ u := by
  fin_cases σ
  · simpa [AjR] using jtick_eq0 x u
  · simpa [AjR] using jtick_eq1 x u

/-- `Σ |Pj i j|` (an integer). -/
def PsumJ : ℚ := 4673074267459201

theorem PsumJ_eq : (∑ i, ∑ j, |Pj i j|) = PsumJ := by decide +kernel

/-- `V w ≤ PsumJ ε²` when `|w i| ≤ ε`. -/
theorem V_le_of_abs_le (w : Fin 14 → ℝ) {ε : ℝ} (hw : ∀ i, |w i| ≤ ε) :
    V w ≤ (PsumJ : ℝ) * ε ^ 2 := by
  have h := Contracts.Track.Vertical.qf_le_of_abs_le PjR w hw
  have e : (∑ i, ∑ j, |PjR i j|) = (PsumJ : ℝ) := by
    rw [← PsumJ_eq]; simp [PjR, castM]
  rwa [e] at h

/-- The pure position offset: `V (e·e₀) = Pj₀₀ e²` with `Pj₀₀ = 10¹⁵`. -/
theorem V_single (e : ℝ) : V (Pi.single 0 e) = 10 ^ 15 * e ^ 2 := by
  simp [V, qf, PjR, castM, Pj, dotProduct, mulVec, Pi.single_apply]
  ring

/-! ## Outputs -/

/-- `qf (L · diag d · Lᵀ) x = Σ dᵢ ((Lᵀ x)ᵢ)²`. -/
theorem qf_ldl_eq {n : ℕ} (L : Matrix (Fin n) (Fin n) ℝ) (d : Fin n → ℝ) (x : Fin n → ℝ) :
    qf (L * diagonal d * Lᵀ) x = ∑ i, d i * (Lᵀ *ᵥ x) i ^ 2 := by
  simp only [qf]
  rw [← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec, ← mulVec_transpose]
  simp [dotProduct, mulVec_diagonal]
  refine Finset.sum_congr rfl fun i _ => by ring

/-- **The output bound** of a certified output: `(c ⬝ x)² ≤ γ V x`. -/
theorem out_sq_le {c y : Fin 14 → ℚ} {γ : ℚ} (h : OutCert c y γ) (x : Fin 14 → ℝ) :
    ((fun i => (c i : ℝ)) ⬝ᵥ x) ^ 2 ≤ (γ : ℝ) * V x := by
  obtain ⟨hLy, hg⟩ := h
  set z : Fin 14 → ℝ := (castM Lp)ᵀ *ᵥ x with hz
  have hV : V x = ∑ i, (Dp i : ℝ) * z i ^ 2 := by
    simp only [V, PjR]; rw [castM_ldl certP, qf_ldl_eq]
  have hc : (fun i => (c i : ℝ)) = castM Lp *ᵥ (fun i => (y i : ℝ)) := by
    rw [← hLy]; ext i; simp [castM, mulVec, dotProduct]
  have hcx : (fun i => (c i : ℝ)) ⬝ᵥ x = ∑ i, (y i : ℝ) * z i := by
    rw [hc, dotProduct_comm, dotProduct_mulVec, ← mulVec_transpose, ← hz, dotProduct_comm]; rfl
  have hD : ∀ i, (0 : ℝ) < Dp i := fun i => by exact_mod_cast Dp_pos i
  -- Cauchy–Schwarz with weights `Dp`
  have cs : (∑ i, (y i : ℝ) * z i) ^ 2 ≤
      (∑ i, ((y i : ℝ) / Real.sqrt (Dp i)) ^ 2) * ∑ i, (Real.sqrt (Dp i) * z i) ^ 2 := by
    have e : ∀ i, (y i : ℝ) * z i = (y i : ℝ) / Real.sqrt (Dp i) * (Real.sqrt (Dp i) * z i) := by
      intro i; have := Real.sqrt_pos.2 (hD i); field_simp
    simp_rw [e]
    exact Finset.sum_mul_sq_le_sq_mul_sq _ _ _
  have e1 : ∑ i, ((y i : ℝ) / Real.sqrt (Dp i)) ^ 2 = ∑ i, (y i : ℝ) ^ 2 / Dp i := by
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [div_pow, Real.sq_sqrt (hD i).le]
  have e2 : ∑ i, (Real.sqrt (Dp i) * z i) ^ 2 = ∑ i, (Dp i : ℝ) * z i ^ 2 := by
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [mul_pow, Real.sq_sqrt (hD i).le]
  have hg' : ∑ i, (y i : ℝ) ^ 2 / Dp i ≤ (γ : ℝ) := by exact_mod_cast hg
  rw [e1, e2, ← hV] at cs
  rw [hcx]
  exact cs.trans (mul_le_mul_of_nonneg_right hg' (V_nonneg x))

/-- The position error of the axis: `e² ≤ γ_e V`. -/
theorem sq_e_le (x : Fin 14 → ℝ) : x 0 ^ 2 ≤ (g_e : ℝ) * V x := by
  have h := out_sq_le cert_e x
  have : (fun i => (c_e i : ℝ)) ⬝ᵥ x = x 0 := by
    simp [c_e, dotProduct, Fin.sum_univ_succ]
  rwa [this] at h

/-- The tilt error from the commanded tilt (the attitude error `a`, m/s²): `a² ≤ γ_a V`. -/
theorem sq_a_le (x : Fin 14 → ℝ) : x 7 ^ 2 ≤ (g_a : ℝ) * V x := by
  have h := out_sq_le cert_a x
  have : (fun i => (c_a i : ℝ)) ⬝ᵥ x = x 7 := by
    simp [c_a, dotProduct, Fin.sum_univ_succ]
  rwa [this] at h

end Contracts.Track.AttJ
