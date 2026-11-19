module

public import Plant.Step.Euler

/-!
# The sharp one-period step

The estimates of `Flow.lean` and `Euler.lean` are too coarse for per-tick use in a closed-loop invariant. This file
proves block-wise bounds instead.

**Torque bound along the period.** `TorqueBd f A` bounds the angular accelerations of the torques of the thrusts
`f`; `TorqueBdT x u A` asks it along the whole trajectory. `alphaMax` always works (`torqueBdT_alphaMax`); thrusts and
commands in an interval of width `s` give `alphaMax · s`, because each thrust moves between its start value and its
command (`torqueBdT_of_spread`).

**Attitude block.** The `(q, ω)` rows of the field do not depend on `(p, v)`. On unit quaternions and body rates at
most `Ω` they are Lipschitz with constant `Katt Ω = max((3/2)(1 + Ω), 2 gyro Ω)` in the attitude coordinates, plus
`2 alphaMax` per unit of thrust difference (`vf_att_lipschitz`). The rates stay below `wTA W A = W + h (A + gyro
(wB W)²)` over the period (`WBd_trajA`). Grönwall on this block gives `step_qw_gronwall`; a second-order expansion of
each attitude coordinate is `traj_att_taylor`.

**Translation block.** `v̇ = g e_z - a(t) d(q(t))`, `ṗ = v`, where the thrust acceleration `a(t)` is now the lagged
thrust of the period, in closed form (`accel_traj_eq`): `a(t) = (amax/4) Σᵢ lagSol cᵢ fᵢ t`. Its integrals
`accK1`, …, `accK4` (`∫ a`, `∫ s a`, and their integrals) are explicit in `e^{-t/τᵢ}` (`Plant.Field.Motor`,
`lagK1`…`lagK4`). Along the flow the down axis `d` and the first two columns `c₀`, `c₁` of the rotation satisfy
`ḋ = c₀ ω_y - c₁ ω_x` (`dnDot`) and `d̈ = c₀ (ω̇_y + ω_x ω_z) + c₁ (ω_y ω_z - ω̇_x) - d (ω_x² + ω_y²)` (`dnDDot`), so
`|d̈ⱼ| ≤ Cd A Ω = √(2 (A + (Jz/Jx) Ω²)² + 4 Ω⁴)` (`abs_dnDDot_le`). Three and four integrations give, from a unit
quaternion with thrusts in `[0, 1]⁴` (`traj_pv_sharp`, `step_pv_sharp`), per NED component,
* `v(t) = v + t g e_z - accK1(t) d(q) - accK2(t) Dd(q)[q̇] + r_v`, `|r_v| ≤ amax Cd t³ / 6`,
* `p(t) = p + t v + (t²/2) g e_z - accK3(t) d(q) - accK4(t) Dd(q)[q̇] + r_p`, `|r_p| ≤ amax Cd t⁴ / 24`.
With the thrusts at their commands the kernels are `a t`, `a t²/2`, `a t²/2`, `a t³/6`, the expansion of a held
thrust. The lower-order versions are `traj_pv_first`, and `traj_pos_move` bounds the position change over the
period by `V t + (g + amax) t² / 2`. The evaluated constants for the X500 are in `Plant.Step.Numbers`.
-/

@[expose] public section

namespace Plant

noncomputable section

open Set

/-! ## Indices, axes, torque bounds -/

/-- Position coordinate `j` (`0, 1, 2`, NED) of the flat state. -/
def pI (j : Fin 3) : Fin 17 := ⟨j.val, by omega⟩

/-- Velocity coordinate `j` (`3, 4, 5`). -/
def vI (j : Fin 3) : Fin 17 := ⟨j.val + 3, by omega⟩

/-- Quaternion coordinate `i` (`6, …, 9`). -/
def qI (i : Fin 4) : Fin 17 := ⟨i.val + 6, by omega⟩

/-- Rate coordinate `k` (`10, 11, 12`). -/
def wI (k : Fin 3) : Fin 17 := ⟨k.val + 10, by omega⟩

/-- The NED down unit vector `e_z`. -/
def ez : Fin 3 → ℝ := ![0, 0, 1]

/-- The second time derivative of the down axis along the flow,
`c₀ (ω̇_y + ω_x ω_z) + c₁ (ω_y ω_z - ω̇_x) - d (ω_x² + ω_y²)`. -/
def dnDDot (x : X) (u : Fin 4 → ℝ) (j : Fin 3) : ℝ :=
  col0 x j * (vf x u 11 + x 10 * x 12) + col1 x j * (x 11 * x 12 - vf x u 10) -
    dn x j * (x 10 ^ 2 + x 11 ^ 2)

theorem dn_eq_downAxis (x : X) :
    dn x 0 = (downAxis (State.ofX x).q).x ∧ dn x 1 = (downAxis (State.ofX x).q).y ∧
      dn x 2 = (downAxis (State.ofX x).q).z := ⟨rfl, rfl, rfl⟩

/-- The position rows of the field: `ṗ = v`. -/
theorem vf_pI (x : X) (u : Fin 4 → ℝ) (j : Fin 3) : vf x u (pI j) = x (vI j) := by
  fin_cases j <;> rfl

/-- The velocity rows of the field: `v̇ = g e_z - a d(q)`, `a` the thrust acceleration of the state's thrusts. -/
theorem vf_vI (x : X) (u : Fin 4 → ℝ) (j : Fin 3) :
    vf x u (vI j) = grav * ez j - accel (thr x) * dn x j := by
  fin_cases j <;> simp [vI, ez, dn, vf_3, vf_4, vf_5]
  ring

/-- The angular accelerations of the torques are at most `A`. -/
def TorqueBd (u : Fin 4 → ℝ) (A : ℝ) : Prop :=
  |torqueX u / Jx| ≤ A ∧ |torqueY u / Jy| ≤ A ∧ |torqueZ u / Jz| ≤ A

/-- Every thrust vector satisfies the torque bound `alphaMax` (the thrusts are clipped). -/
theorem torqueBd_alphaMax (u : Fin 4 → ℝ) : TorqueBd u alphaMax :=
  ⟨abs_torqueX_div_le u, abs_torqueY_div_le u, abs_torqueZ_div_le u⟩

theorem TorqueBd.nonneg {u : Fin 4 → ℝ} {A : ℝ} (hA : TorqueBd u A) : 0 ≤ A :=
  (abs_nonneg _).trans hA.1

/-- **Torque bound from the thrust spread.** Thrusts in an interval `[lo, lo + s] ⊆ [0, 1]` give angular
accelerations at most `alphaMax · s`. -/
theorem torqueBd_of_spread {u : Fin 4 → ℝ} {lo s : ℝ} (h0 : 0 ≤ lo) (h1 : lo + s ≤ 1)
    (hu : ∀ i, lo ≤ u i ∧ u i ≤ lo + s) : TorqueBd u (alphaMax * s) := by
  have hc : ∀ i, clip01 (u i) = u i := fun i =>
    clip01_of_mem (h0.trans (hu i).1) ((hu i).2.trans h1)
  have hs : 0 ≤ s := by linarith [(hu 0).1, (hu 0).2]
  obtain ⟨a0, b0⟩ := hu 0; obtain ⟨a1, b1⟩ := hu 1
  obtain ⟨a2, b2⟩ := hu 2; obtain ⟨a3, b3⟩ := hu 3
  have hl := lever_pos; have hf := fmax_pos; have hJ := Jx_pos
  have hαs : alphaMax * s = lever * fmax * (2 * s) / Jx := by unfold alphaMax; ring
  refine ⟨?_, ?_, ?_⟩
  · rw [hαs, abs_div, abs_of_pos hJ]
    apply div_le_div_of_nonneg_right _ hJ.le
    have e : torqueX u = lever * fmax * (-u 0 + u 1 + u 2 - u 3) := by
      simp only [torqueX, force, hc]; ring
    rw [e, abs_mul, abs_of_pos (mul_pos hl hf)]
    exact mul_le_mul_of_nonneg_left (abs_le.2 ⟨by linarith, by linarith⟩) (mul_pos hl hf).le
  · rw [hαs, abs_div, abs_of_pos Jy_pos, ← Jy_eq_Jx]
    apply div_le_div_of_nonneg_right _ Jy_pos.le
    have e : torqueY u = lever * fmax * (u 0 - u 1 + u 2 - u 3) := by
      simp only [torqueY, force, hc]; ring
    rw [e, abs_mul, abs_of_pos (mul_pos hl hf)]
    exact mul_le_mul_of_nonneg_left (abs_le.2 ⟨by linarith, by linarith⟩) (mul_pos hl hf).le
  · rw [abs_div, abs_of_pos Jz_pos, torqueZ, km_maxRPM_sq, hc, hc, hc, hc, abs_mul,
      abs_of_pos (mul_pos kmkf_pos hf)]
    have hk : |u 0 + u 1 - u 2 - u 3| ≤ 2 * s := abs_le.2 ⟨by linarith, by linarith⟩
    rw [div_le_iff₀ Jz_pos, hαs, div_mul_eq_mul_div, le_div_iff₀ hJ]
    have := kmkf_Jx_le_lever_Jz
    have h2 : kmkf * fmax * |u 0 + u 1 - u 2 - u 3| ≤ kmkf * fmax * (2 * s) :=
      mul_le_mul_of_nonneg_left hk (mul_pos kmkf_pos hf).le
    have h3 : 0 ≤ fmax * (2 * s) := by positivity
    nlinarith

/-- Thrusts at most `c ∈ [0, 1]` give a thrust acceleration at most `c · amax`. -/
theorem accel_le_mul {u : Fin 4 → ℝ} {c : ℝ} (hc : 0 ≤ c) (hu : ∀ i, u i ≤ c) :
    accel u ≤ c * amax := by
  have hcl : ∀ i, clip01 (u i) ≤ c := fun i =>
    max_le hc ((min_le_right _ _).trans (hu i))
  rw [accel, thrust_eq, ← four_fmax_div_mass, mul_div_assoc', div_le_div_iff_of_pos_right mass_pos]
  have := hcl 0; have := hcl 1; have := hcl 2; have := hcl 3
  nlinarith [fmax_pos]

/-- The torque bound along the trajectory of the period. -/
def TorqueBdT (x : X) (u : Fin 4 → ℝ) (A : ℝ) : Prop := ∀ t ∈ Icc 0 h, TorqueBd (thr (traj x u t)) A

theorem torqueBdT_alphaMax (x : X) (u : Fin 4 → ℝ) : TorqueBdT x u alphaMax := fun _ _ =>
  torqueBd_alphaMax _

theorem TorqueBdT.nonneg {x : X} {u : Fin 4 → ℝ} {A : ℝ} (hA : TorqueBdT x u A) : 0 ≤ A :=
  (hA 0 ⟨le_rfl, h_pos.le⟩).nonneg

theorem TorqueBdT.zero {x : X} {u : Fin 4 → ℝ} {A : ℝ} (hA : TorqueBdT x u A) : TorqueBd (thr x) A := by
  have := hA 0 ⟨le_rfl, h_pos.le⟩; rwa [traj_zero] at this

/-- **Torque bound along the period from the spread**: thrusts and commands in `[lo, lo + s] ⊆ [0, 1]` keep the
thrusts there over the period, so the angular accelerations stay below `alphaMax · s`. -/
theorem torqueBdT_of_spread {x : X} {u : Fin 4 → ℝ} {lo s : ℝ} (h0 : 0 ≤ lo) (h1 : lo + s ≤ 1)
    (hx : ∀ i, lo ≤ thr x i ∧ thr x i ≤ lo + s) (hu : ∀ i, lo ≤ u i ∧ u i ≤ lo + s) :
    TorqueBdT x u (alphaMax * s) := by
  intro t ht
  refine torqueBd_of_spread h0 h1 fun i => ?_
  have hc : clip01 (u i) = u i := clip01_of_mem (h0.trans (hu i).1) ((hu i).2.trans h1)
  rw [thr_traj x u i t ht, hc]
  obtain ⟨a, b⟩ := lagSol_between (u i) (thr x i) ht.1
  exact ⟨le_trans (le_min (hx i).1 (hu i).1) a, b.trans (max_le (hx i).2 (hu i).2)⟩

/-- The rate rows of the field under a torque bound. -/
theorem abs_vf_wA (x : X) {u : Fin 4 → ℝ} {Rw A : ℝ} (hw : WBd x Rw) (hA : TorqueBd (thr x) A) :
    |vf x u 10| ≤ A + gyro * Rw ^ 2 ∧ |vf x u 11| ≤ A + gyro * Rw ^ 2 ∧
      |vf x u 12| ≤ A + gyro * Rw ^ 2 := by
  obtain ⟨x10, x11, x12⟩ := hw
  obtain ⟨t10, t11, t12⟩ := hA
  have hg := gyro_nonneg
  have P : ∀ {i j : Fin 17}, |x i| ≤ Rw → |x j| ≤ Rw → |x i * x j| ≤ Rw ^ 2 := by
    intro i j a b; rw [abs_mul, sq]; exact mul_le_mul a b (abs_nonneg _) ((abs_nonneg _).trans a)
  have G : ∀ {c p : ℝ}, |c| ≤ gyro → |p| ≤ Rw ^ 2 → |c * p| ≤ gyro * Rw ^ 2 := by
    intro c p hc hp; rw [abs_mul]; exact mul_le_mul hc hp (abs_nonneg _) hg
  refine ⟨?_, ?_, ?_⟩
  · rw [show vf x u 10 = torqueX (thr x) / Jx + (-((Jz - Jy) / Jx)) * (x 11 * x 12) by
      rw [vf_10]; field_simp [Jx_pos.ne']; ring]
    exact (abs_add_le _ _).trans (add_le_add t10 (G abs_gyroX_le (P x11 x12)))
  · rw [show vf x u 11 = torqueY (thr x) / Jy + (-((Jx - Jz) / Jy)) * (x 12 * x 10) by
      rw [vf_11]; field_simp [Jy_pos.ne']; ring]
    exact (abs_add_le _ _).trans (add_le_add t11 (G abs_gyroY_le (P x12 x10)))
  · rw [show vf x u 12 = torqueZ (thr x) / Jz + (-((Jy - Jx) / Jz)) * (x 10 * x 11) by
      rw [vf_12]; field_simp [Jz_pos.ne']; ring]
    exact (abs_add_le _ _).trans (add_le_add t12 (G abs_gyroZ_le (P x10 x11)))

/-! ## Rates along the trajectory -/

/-- Rate bound over one period under the torque bound `A`: `W + h (A + gyro (wB W)²)`. -/
def wTA (W A : ℝ) : ℝ := W + h * (A + gyro * wB W ^ 2)

theorem le_wTA {W A : ℝ} (hA : 0 ≤ A) : W ≤ wTA W A := by
  have : 0 ≤ h * (A + gyro * wB W ^ 2) := by
    have := h_pos
    have := gyro_nonneg
    positivity
  unfold wTA; linarith

/-- **Rates along the trajectory** under the torque bound `A`: `|ωⱼ(t)| ≤ wTA W A` on `[0, h]`. -/
theorem WBd_trajA {x : X} {u : Fin 4 → ℝ} {W A : ℝ} (hW : WBd x W) (hA : TorqueBdT x u A) :
    ∀ t ∈ Icc 0 h, WBd (traj x u t) (wTA W A) := by
  intro t ht
  have hd : ∀ j, ∀ r ∈ Icc 0 h, HasDerivAt (fun r => traj x u r j) (vf (traj x u r) u j) r :=
    fun j r hr => hasDerivAt_pi.1 (traj_hasDerivAt x u r hr) j
  have bw := fun r hr => abs_vf_wA (traj x u r) (u := u) (WBd_traj_energy hW r hr) (hA r hr)
  have hM : 0 ≤ A + gyro * wB W ^ 2 := by
    have := hA.nonneg
    have := gyro_nonneg
    positivity
  have one : ∀ j, |x j| ≤ W → (∀ r ∈ Icc 0 h, |vf (traj x u r) u j| ≤ A + gyro * wB W ^ 2) →
      |traj x u t j| ≤ wTA W A := by
    intro j hx hb
    have h1 := abs_sub_le_of_deriv (hd j) hb t ht
    simp only [traj_zero] at h1
    have h2 : (A + gyro * wB W ^ 2) * t ≤ h * (A + gyro * wB W ^ 2) := by
      rw [mul_comm]; exact mul_le_mul_of_nonneg_right ht.2 hM
    have := abs_sub_abs_le_abs_sub (traj x u t j) (x j)
    unfold wTA; linarith
  obtain ⟨w10, w11, w12⟩ := hW
  exact ⟨one 10 w10 fun r hr => (bw r hr).1, one 11 w11 fun r hr => (bw r hr).2.1,
    one 12 w12 fun r hr => (bw r hr).2.2⟩

/-! ## Taylor expansions with bounded remainder -/

/-! ## Derivatives of the rotation columns along a solution -/

section deriv
variable {u : Fin 4 → ℝ} {γ : ℝ → X} {t : ℝ}

private theorem hd_mul (hγ : HasDerivAt γ (vf (γ t) u) t) (i k : Fin 17) :
    HasDerivAt (fun s => γ s i * γ s k) (vf (γ t) u i * γ t k + γ t i * vf (γ t) u k) t :=
  (hasDerivAt_pi.1 hγ i).mul (hasDerivAt_pi.1 hγ k)

/-- `ċ₀ = R (ω × e_x) = c₁ ω_z - d ω_y`. -/
theorem hasDerivAt_col0 (hγ : HasDerivAt γ (vf (γ t) u) t) (j : Fin 3) :
    HasDerivAt (fun s => col0 (γ s) j) (col1 (γ t) j * γ t 12 - dn (γ t) j * γ t 11) t := by
  have M := hd_mul hγ
  fin_cases j
  · convert (((M 6 6).add (M 7 7)).sub (M 8 8)).sub (M 9 9) using 1
    · funext s; simp [col0]
    · simp [col1, dn, vf_6, vf_7, vf_8, vf_9]; ring
  · convert ((M 7 8).add (M 6 9)).const_mul 2 using 1
    · funext s; simp [col0]
    · simp [col1, dn, vf_6, vf_7, vf_8, vf_9]; ring
  · convert ((M 7 9).sub (M 6 8)).const_mul 2 using 1
    · funext s; simp [col0]
    · simp [col1, dn, vf_6, vf_7, vf_8, vf_9]; ring

/-- `ċ₁ = R (ω × e_y) = d ω_x - c₀ ω_z`. -/
theorem hasDerivAt_col1 (hγ : HasDerivAt γ (vf (γ t) u) t) (j : Fin 3) :
    HasDerivAt (fun s => col1 (γ s) j) (dn (γ t) j * γ t 10 - col0 (γ t) j * γ t 12) t := by
  have M := hd_mul hγ
  fin_cases j
  · convert ((M 7 8).sub (M 6 9)).const_mul 2 using 1
    · funext s; simp [col1]
    · simp [col0, dn, vf_6, vf_7, vf_8, vf_9]; ring
  · convert (((M 6 6).sub (M 7 7)).add (M 8 8)).sub (M 9 9) using 1
    · funext s; simp [col1]
    · simp [col0, dn, vf_6, vf_7, vf_8, vf_9]; ring
  · convert ((M 8 9).add (M 6 7)).const_mul 2 using 1
    · funext s; simp [col1]
    · simp [col0, dn, vf_6, vf_7, vf_8, vf_9]; ring

/-- `ḋ = R (ω × e_z) = c₀ ω_y - c₁ ω_x` (`dnDot`). -/
theorem hasDerivAt_dn (hγ : HasDerivAt γ (vf (γ t) u) t) (j : Fin 3) :
    HasDerivAt (fun s => dn (γ s) j) (dnDot (γ t) j) t := by
  have M := hd_mul hγ
  fin_cases j
  · convert ((M 7 9).add (M 6 8)).const_mul 2 using 1
    · funext s; simp [dn]
    · simp [dnDot, col0, col1, vf_6, vf_7, vf_8, vf_9]; ring
  · convert ((M 8 9).sub (M 6 7)).const_mul 2 using 1
    · funext s; simp [dn]
    · simp [dnDot, col0, col1, vf_6, vf_7, vf_8, vf_9]; ring
  · convert (((M 6 6).sub (M 7 7)).sub (M 8 8)).add (M 9 9) using 1
    · funext s; simp [dn]
    · simp [dnDot, col0, col1, vf_6, vf_7, vf_8, vf_9]; ring

/-- `d/dt Dd(q)[q̇] = dnDDot`. -/
theorem hasDerivAt_dnDot (hγ : HasDerivAt γ (vf (γ t) u) t) (j : Fin 3) :
    HasDerivAt (fun s => dnDot (γ s) j) (dnDDot (γ t) u j) t := by
  have := ((hasDerivAt_col0 hγ j).mul (hasDerivAt_pi.1 hγ 11)).sub
    ((hasDerivAt_col1 hγ j).mul (hasDerivAt_pi.1 hγ 10))
  convert this using 1
  · funext s; simp only [dnDot, Pi.sub_apply, Pi.mul_apply]
  · simp only [dnDDot]; ring

end deriv

/-! ## Bounds through the rotation rows -/

/-- The constant of the second derivative of the down axis: `Cd A Ω = √(2 (A + (Jz/Jx) Ω²)² + 4 Ω⁴)`. -/
def Cd (A Ω : ℝ) : ℝ := Real.sqrt (2 * (A + Jz / Jx * Ω ^ 2) ^ 2 + 4 * Ω ^ 4)

theorem JzJx_pos : 0 < Jz / Jx := div_pos Jz_pos Jx_pos

theorem Cd_nonneg (A Ω : ℝ) : 0 ≤ Cd A Ω := Real.sqrt_nonneg _

/-- `Cd` is monotone. -/
theorem Cd_mono {A A' Ω Ω' : ℝ} (hA : 0 ≤ A) (hAA : A ≤ A') (hΩ : 0 ≤ Ω) (hΩΩ : Ω ≤ Ω') :
    Cd A Ω ≤ Cd A' Ω' := by
  unfold Cd
  apply Real.sqrt_le_sqrt
  have h2 : Ω ^ 2 ≤ Ω' ^ 2 := pow_le_pow_left₀ hΩ hΩΩ 2
  have h4 : Ω ^ 4 ≤ Ω' ^ 4 := pow_le_pow_left₀ hΩ hΩΩ 4
  have hJ := JzJx_pos
  have h0 : 0 ≤ A + Jz / Jx * Ω ^ 2 := by positivity
  have h1 : A + Jz / Jx * Ω ^ 2 ≤ A' + Jz / Jx * Ω' ^ 2 := by nlinarith
  nlinarith

/-- **Second derivative of the down axis**: `|d̈ⱼ| ≤ Cd A Ω` for a unit quaternion, rates at most
`Ω` and angular accelerations of the torques at most `A`. -/
theorem abs_dnDDot_le {x : X} {u : Fin 4 → ℝ} {A Ω : ℝ} (hq : qnormSq x = 1) (hw : WBd x Ω)
    (hA : TorqueBd (thr x) A) (j : Fin 3) : |dnDDot x u j| ≤ Cd A Ω := by
  obtain ⟨w10, w11, w12⟩ := hw
  obtain ⟨t10, t11, -⟩ := hA
  have hΩ : 0 ≤ Ω := (abs_nonneg _).trans w10
  have hJ := JzJx_pos
  have z0 : vf x u 11 + x 10 * x 12 = torqueY (thr x) / Jy + Jz / Jx * (x 10 * x 12) := by
    rw [vf_11, Jy_eq_Jx]; field_simp [Jx_pos.ne']; ring
  have z1 : x 11 * x 12 - vf x u 10 = -(torqueX (thr x) / Jx) + Jz / Jx * (x 11 * x 12) := by
    rw [vf_10, Jy_eq_Jx]; field_simp [Jx_pos.ne']; ring
  have P : ∀ {i k : Fin 17}, |x i| ≤ Ω → |x k| ≤ Ω → |x i * x k| ≤ Ω ^ 2 := by
    intro i k a b; rw [abs_mul, sq]; exact mul_le_mul a b (abs_nonneg _) hΩ
  have b0 : |vf x u 11 + x 10 * x 12| ≤ A + Jz / Jx * Ω ^ 2 := by
    rw [z0]; refine (abs_add_le _ _).trans (add_le_add t11 ?_)
    rw [abs_mul, abs_of_pos hJ]
    exact mul_le_mul_of_nonneg_left (P w10 w12) hJ.le
  have b1 : |x 11 * x 12 - vf x u 10| ≤ A + Jz / Jx * Ω ^ 2 := by
    rw [z1]; refine (abs_add_le _ _).trans (add_le_add (by rwa [abs_neg]) ?_)
    rw [abs_mul, abs_of_pos hJ]
    exact mul_le_mul_of_nonneg_left (P w11 w12) hJ.le
  have b2 : |-(x 10 ^ 2 + x 11 ^ 2)| ≤ 2 * Ω ^ 2 := by
    rw [abs_neg, abs_of_nonneg (by positivity)]
    have := P w10 w10; have := P w11 w11
    rw [abs_mul_self] at *
    nlinarith [sq_abs (x 10), sq_abs (x 11), abs_mul_abs_self (x 10), abs_mul_abs_self (x 11)]
  have e : dnDDot x u j = col0 x j * (vf x u 11 + x 10 * x 12) +
      col1 x j * (x 11 * x 12 - vf x u 10) + dn x j * (-(x 10 ^ 2 + x 11 ^ 2)) := by
    simp only [dnDDot]; ring
  rw [e]
  refine (abs_row_le hq j _ _ _).trans (Real.sqrt_le_sqrt ?_)
  have s0 := sq_le_sq' (abs_le.mp b0).1 (abs_le.mp b0).2
  have s1 := sq_le_sq' (abs_le.mp b1).1 (abs_le.mp b1).2
  have s2 := sq_le_sq' (abs_le.mp b2).1 (abs_le.mp b2).2
  nlinarith

/-! ## The thrust acceleration over the period, in closed form -/

/-- The thrust acceleration along the period from the thrusts of `x` under the commands `u`, in closed form:
`(amax/4) Σᵢ lagSol cᵢ fᵢ t`. -/
def accT (x : X) (u : Fin 4 → ℝ) (t : ℝ) : ℝ :=
  amax / 4 * (lagSol (clip01 (u 0)) (thr x 0) t + lagSol (clip01 (u 1)) (thr x 1) t +
    lagSol (clip01 (u 2)) (thr x 2) t + lagSol (clip01 (u 3)) (thr x 3) t)

/-- A kernel of the lag summed over the propellers, times `amax / 4`. -/
def accK (k : ℝ → ℝ → ℝ → ℝ) (x : X) (u : Fin 4 → ℝ) (t : ℝ) : ℝ :=
  amax / 4 * (k (clip01 (u 0)) (thr x 0) t + k (clip01 (u 1)) (thr x 1) t +
    k (clip01 (u 2)) (thr x 2) t + k (clip01 (u 3)) (thr x 3) t)

/-- `∫₀ᵗ a`. -/ abbrev accK1 := accK lagK1
/-- `∫₀ᵗ s a(s) ds`. -/ abbrev accK2 := accK lagK2
/-- `∫₀ᵗ accK1`. -/ abbrev accK3 := accK lagK3
/-- `∫₀ᵗ accK2`. -/ abbrev accK4 := accK lagK4

private theorem hasDerivAt_accK {k k' : ℝ → ℝ → ℝ → ℝ} (hk : ∀ c f t, HasDerivAt (k c f) (k' c f t) t)
    (x : X) (u : Fin 4 → ℝ) (t : ℝ) : HasDerivAt (accK k x u) (accK k' x u t) t :=
  ((((hk _ _ t).add (hk _ _ t)).add (hk _ _ t)).add (hk _ _ t)).const_mul (amax / 4)

theorem hasDerivAt_accK1 (x : X) (u : Fin 4 → ℝ) (t : ℝ) : HasDerivAt (accK1 x u) (accT x u t) t :=
  hasDerivAt_accK hasDerivAt_lagK1 x u t

theorem hasDerivAt_accK2 (x : X) (u : Fin 4 → ℝ) (t : ℝ) :
    HasDerivAt (accK2 x u) (t * accT x u t) t := by
  refine (hasDerivAt_accK hasDerivAt_lagK2 x u t).congr_deriv ?_
  simp only [accK, accT]; ring

theorem hasDerivAt_accK3 (x : X) (u : Fin 4 → ℝ) (t : ℝ) :
    HasDerivAt (accK3 x u) (accK1 x u t) t := hasDerivAt_accK hasDerivAt_lagK3 x u t

theorem hasDerivAt_accK4 (x : X) (u : Fin 4 → ℝ) (t : ℝ) :
    HasDerivAt (accK4 x u) (accK2 x u t) t := hasDerivAt_accK hasDerivAt_lagK4 x u t

theorem accK1_zero (x : X) (u : Fin 4 → ℝ) : accK1 x u 0 = 0 := by simp [accK, lagK1_zero]
theorem accK2_zero (x : X) (u : Fin 4 → ℝ) : accK2 x u 0 = 0 := by simp [accK, lagK2_zero]
theorem accK3_zero (x : X) (u : Fin 4 → ℝ) : accK3 x u 0 = 0 := by simp [accK, lagK3_zero]
theorem accK4_zero (x : X) (u : Fin 4 → ℝ) : accK4 x u 0 = 0 := by simp [accK, lagK4_zero]

/-- **The thrust acceleration along the trajectory is the closed form** (thrusts in `[0, 1]⁴`). -/
theorem accel_traj_eq {x : X} (hf : ThrustRange x) (u : Fin 4 → ℝ) :
    ∀ t ∈ Icc 0 h, accel (thr (traj x u t)) = accT x u t := by
  intro t ht
  rw [accel_eq, clip_thr_traj hf u 0 t ht, clip_thr_traj hf u 1 t ht, clip_thr_traj hf u 2 t ht,
    clip_thr_traj hf u 3 t ht]
  rfl

/-- With every thrust at its command the kernels are those of a held thrust acceleration `a`. -/
theorem accK_held {x : X} {u : Fin 4 → ℝ} (hc : ∀ i, thr x i = clip01 (u i)) (t : ℝ) :
    accK1 x u t = accel (thr x) * t ∧ accK2 x u t = accel (thr x) * (t ^ 2 / 2) ∧
      accK3 x u t = accel (thr x) * (t ^ 2 / 2) ∧ accK4 x u t = accel (thr x) * (t ^ 3 / 6) := by
  have hcl : ∀ i, clip01 (thr x i) = thr x i := fun i => by rw [hc i, clip01_of_mem (clip01_nonneg _)
    (clip01_le_one _)]
  simp only [accK, lagK1, lagK2, lagK3, lagK4, ← hc, sub_self, zero_mul, add_zero, accel_eq, hcl]
  refine ⟨by ring, by ring, by ring, by ring⟩

/-! ## The translation block: exact integration -/

section pv
variable {x : X} {u : Fin 4 → ℝ} {W A Ω : ℝ}

/-- Along the trajectory, the quaternion stays a unit quaternion and the rates stay below `Ω`. -/
theorem traj_unit_rates (hq : qnormSq x = 1) (hW : WBd x W) (hA : TorqueBdT x u A)
    (hΩ : wTA W A ≤ Ω) :
    ∀ t ∈ Icc 0 h, qnormSq (traj x u t) = 1 ∧ WBd (traj x u t) Ω := fun t ht =>
  ⟨(qnormSq_traj x u t ht).trans hq, WBd_mono (WBd_trajA hW hA t ht) hΩ⟩

/-- **The down axis along the trajectory**, to first and second order:
`|d(t) - d(0)| ≤ √2 Ω t` and `|d(t) - d(0) - t ḋ(0)| ≤ Cd A Ω t² / 2`. -/
theorem traj_dn (hq : qnormSq x = 1) (hW : WBd x W) (hA : TorqueBdT x u A) (hΩ : wTA W A ≤ Ω)
    (j : Fin 3) : ∀ t ∈ Icc 0 h,
      |dn (traj x u t) j - dn x j| ≤ Real.sqrt 2 * Ω * t ∧
      |dn (traj x u t) j - dn x j - t * dnDot x j| ≤ Cd A Ω * t ^ 2 / 2 := by
  have hur := traj_unit_rates hq hW hA hΩ
  have hd1 : ∀ s ∈ Icc 0 h, HasDerivAt (fun s => dn (traj x u s) j) (dnDot (traj x u s) j) s :=
    fun s hs => hasDerivAt_dn (traj_hasDerivAt x u s hs) j
  have hd2 : ∀ s ∈ Icc 0 h,
      HasDerivAt (fun s => dnDot (traj x u s) j) (dnDDot (traj x u s) u j) s :=
    fun s hs => hasDerivAt_dnDot (traj_hasDerivAt x u s hs) j
  have m1 := abs_sub_le_of_deriv hd1 (fun s hs => abs_dnDot_le (hur s hs).1 (hur s hs).2 j)
  have m2 := abs_sub_le_of_deriv hd2 (fun s hs =>
    abs_dnDDot_le (hur s hs).1 (hur s hs).2 (hA s hs) j)
  have t2 := taylor2 hd1 m2
  simp only [traj_zero] at m1 t2
  exact fun t ht => ⟨m1 t ht, t2 t ht⟩

/-- The velocity rows along the trajectory, with the thrust acceleration in closed form. -/
private theorem hdv (hf : ThrustRange x) (j : Fin 3) : ∀ s ∈ Icc 0 h,
    HasDerivAt (fun s => traj x u s (vI j)) (grav * ez j - accT x u s * dn (traj x u s) j) s :=
  fun s hs => by
    have := hasDerivAt_pi.1 (traj_hasDerivAt x u s hs) (vI j)
    rwa [vf_vI, accel_traj_eq hf u s hs] at this

private theorem hdp (j : Fin 3) : ∀ s ∈ Icc 0 h,
    HasDerivAt (fun s => traj x u s (pI j)) (traj x u s (vI j)) s := fun s hs => by
  have := hasDerivAt_pi.1 (traj_hasDerivAt x u s hs) (pI j)
  rwa [vf_pI] at this

theorem accT_nonneg (hf : ThrustRange x) : ∀ t ∈ Icc 0 h, 0 ≤ accT x u t := fun t ht => by
  rw [← accel_traj_eq hf u t ht]; exact accel_nonneg _

theorem accT_le (hf : ThrustRange x) : ∀ t ∈ Icc 0 h, accT x u t ≤ amax := fun t ht => by
  rw [← accel_traj_eq hf u t ht]; exact accel_le _

/-- **The sharp step of the translation block, along the period.** From a unit quaternion with body rates at most
`W` and thrusts in `[0, 1]⁴`, under angular accelerations of the torques at most `A` along the period, with
`Ω ≥ wTA W A`, for `t ∈ [0, h]` and each NED component `j`:
* `v(t) = v + t g e_z - accK1(t) d(q) - accK2(t) Dd(q)[q̇] + r_v`, `|r_v| ≤ amax Cd A Ω t³ / 6`,
* `p(t) = p + t v + (t²/2) g e_z - accK3(t) d(q) - accK4(t) Dd(q)[q̇] + r_p`, `|r_p| ≤ amax Cd A Ω t⁴ / 24`,
with the lagged thrust in the kernels `accK1 = ∫ a`, `accK2 = ∫ s a(s)`, `accK3 = ∫ accK1`, `accK4 = ∫ accK2`. -/
theorem traj_pv_sharp (hq : qnormSq x = 1) (hW : WBd x W) (hA : TorqueBdT x u A) (hf : ThrustRange x)
    (hΩ : wTA W A ≤ Ω) (j : Fin 3) : ∀ t ∈ Icc 0 h,
      |traj x u t (vI j) - (x (vI j) + t * (grav * ez j) - accK1 x u t * dn x j -
          accK2 x u t * dnDot x j)| ≤ amax * Cd A Ω * t ^ 3 / 6 ∧
      |traj x u t (pI j) - (x (pI j) + t * x (vI j) + t ^ 2 / 2 * (grav * ez j) - accK3 x u t * dn x j -
          accK4 x u t * dnDot x j)| ≤ amax * Cd A Ω * t ^ 4 / 24 := by
  have hdn := traj_dn hq hW hA hΩ j
  have hC := Cd_nonneg A Ω
  have hAm := amax_pos
  -- the velocity rows to third order
  have hv := abs_sub_poly_le (f := fun s => traj x u s (vI j))
    (g := fun s => grav * ez j - accT x u s * dn (traj x u s) j)
    (P := fun s => s * (grav * ez j) - accK1 x u s * dn x j - accK2 x u s * dnDot x j)
    (p := fun s => grav * ez j - accT x u s * dn x j - s * accT x u s * dnDot x j)
    (B := fun s => amax * Cd A Ω * s ^ 3 / 6) (B' := fun s => amax * Cd A Ω * s ^ 2 / 2)
    (hdv hf j)
    (fun s => by
      refine ((((hasDerivAt_id s).mul_const _).sub ((hasDerivAt_accK1 x u s).mul_const _)).sub
        ((hasDerivAt_accK2 x u s).mul_const _)).congr_deriv ?_
      simp)
    (fun s => by
      refine ((hasDerivAt_pow 3 s).const_mul (amax * Cd A Ω) |>.div_const 6).congr_deriv ?_
      push_cast; ring)
    (by simp)
    (fun s hs => by
      have e : grav * ez j - accT x u s * dn (traj x u s) j -
          (grav * ez j - accT x u s * dn x j - s * accT x u s * dnDot x j) =
          -(accT x u s * (dn (traj x u s) j - dn x j - s * dnDot x j)) := by ring
      rw [e, abs_neg, abs_mul, abs_of_nonneg (accT_nonneg hf s hs)]
      calc accT x u s * |dn (traj x u s) j - dn x j - s * dnDot x j|
          ≤ amax * (Cd A Ω * s ^ 2 / 2) :=
            mul_le_mul (accT_le hf s hs) (hdn s hs).2 (abs_nonneg _) hAm.le
        _ = _ := by ring)
  -- the position rows to fourth order
  have hp := abs_sub_poly_le (f := fun s => traj x u s (pI j)) (g := fun s => traj x u s (vI j))
    (P := fun s => s * x (vI j) + s ^ 2 / 2 * (grav * ez j) - accK3 x u s * dn x j - accK4 x u s * dnDot x j)
    (p := fun s => x (vI j) + s * (grav * ez j) - accK1 x u s * dn x j - accK2 x u s * dnDot x j)
    (B := fun s => amax * Cd A Ω * s ^ 4 / 24) (B' := fun s => amax * Cd A Ω * s ^ 3 / 6)
    (hdp j)
    (fun s => by
      refine (((((hasDerivAt_id s).mul_const _).add (((hasDerivAt_pow 2 s).div_const 2).mul_const _)).sub
        ((hasDerivAt_accK3 x u s).mul_const _)).sub ((hasDerivAt_accK4 x u s).mul_const _)).congr_deriv ?_
      simp)
    (fun s => by
      refine ((hasDerivAt_pow 4 s).const_mul (amax * Cd A Ω) |>.div_const 24).congr_deriv ?_
      push_cast; ring)
    (by simp)
    (fun s hs => by
      have := hv s hs
      simp only [traj_zero, accK1_zero, accK2_zero, zero_mul, sub_zero] at this
      rw [show traj x u s (vI j) - (x (vI j) + s * (grav * ez j) - accK1 x u s * dn x j -
        accK2 x u s * dnDot x j) = traj x u s (vI j) - x (vI j) -
        (s * (grav * ez j) - accK1 x u s * dn x j - accK2 x u s * dnDot x j) by ring]
      exact this)
  intro t ht
  constructor
  · have := hv t ht
    simp only [traj_zero, accK1_zero, accK2_zero, zero_mul, sub_zero] at this
    rw [show traj x u t (vI j) - (x (vI j) + t * (grav * ez j) - accK1 x u t * dn x j -
        accK2 x u t * dnDot x j) = traj x u t (vI j) - x (vI j) -
        (t * (grav * ez j) - accK1 x u t * dn x j - accK2 x u t * dnDot x j) by ring]
    exact this
  · have := hp t ht
    simp only [traj_zero, accK3_zero, accK4_zero, zero_mul, sub_zero,
      ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_div, add_zero] at this
    rw [show traj x u t (pI j) - (x (pI j) + t * x (vI j) + t ^ 2 / 2 * (grav * ez j) - accK3 x u t * dn x j -
        accK4 x u t * dnDot x j) = traj x u t (pI j) - x (pI j) -
        (t * x (vI j) + t ^ 2 / 2 * (grav * ez j) - accK3 x u t * dn x j - accK4 x u t * dnDot x j) by ring]
    exact this

/-- **The sharp step of the translation block** (`step_pv_sharp`): the case `t = h` of `traj_pv_sharp`. -/
theorem step_pv_sharp (hq : qnormSq x = 1) (hW : WBd x W) (hA : TorqueBdT x u A) (hf : ThrustRange x)
    (hΩ : wTA W A ≤ Ω) (j : Fin 3) :
    |step x u (vI j) - (x (vI j) + h * (grav * ez j) - accK1 x u h * dn x j -
        accK2 x u h * dnDot x j)| ≤ amax * Cd A Ω * h ^ 3 / 6 ∧
    |step x u (pI j) - (x (pI j) + h * x (vI j) + h ^ 2 / 2 * (grav * ez j) - accK3 x u h * dn x j -
        accK4 x u h * dnDot x j)| ≤ amax * Cd A Ω * h ^ 4 / 24 :=
  traj_pv_sharp hq hW hA hf hΩ j h ⟨h_pos.le, le_rfl⟩

/-- **The translation block to one order less**, with the remainder through `|ḋ| ≤ √2 Ω`:
`|v(t) - v - t g e_z + accK1(t) d(q)| ≤ amax √2 Ω t² / 2` and
`|p(t) - p - t v - (t²/2) g e_z + accK3(t) d(q)| ≤ amax √2 Ω t³ / 6`. -/
theorem traj_pv_first (hq : qnormSq x = 1) (hW : WBd x W) (hA : TorqueBdT x u A) (hf : ThrustRange x)
    (hΩ : wTA W A ≤ Ω) (j : Fin 3) : ∀ t ∈ Icc 0 h,
      |traj x u t (vI j) - (x (vI j) + t * (grav * ez j) - accK1 x u t * dn x j)| ≤
        amax * (Real.sqrt 2 * Ω) * t ^ 2 / 2 ∧
      |traj x u t (pI j) - (x (pI j) + t * x (vI j) + t ^ 2 / 2 * (grav * ez j) - accK3 x u t * dn x j)|
        ≤ amax * (Real.sqrt 2 * Ω) * t ^ 3 / 6 := by
  have hdn := traj_dn hq hW hA hΩ j
  have hAm := amax_pos
  have hv := abs_sub_poly_le (f := fun s => traj x u s (vI j))
    (g := fun s => grav * ez j - accT x u s * dn (traj x u s) j)
    (P := fun s => s * (grav * ez j) - accK1 x u s * dn x j)
    (p := fun s => grav * ez j - accT x u s * dn x j)
    (B := fun s => amax * (Real.sqrt 2 * Ω) * s ^ 2 / 2) (B' := fun s => amax * (Real.sqrt 2 * Ω) * s)
    (hdv hf j)
    (fun s => by
      refine (((hasDerivAt_id s).mul_const _).sub ((hasDerivAt_accK1 x u s).mul_const _)).congr_deriv ?_
      simp)
    (fun s => by
      refine ((hasDerivAt_pow 2 s).const_mul (amax * (Real.sqrt 2 * Ω)) |>.div_const 2).congr_deriv ?_
      push_cast; ring)
    (by simp)
    (fun s hs => by
      have e : grav * ez j - accT x u s * dn (traj x u s) j - (grav * ez j - accT x u s * dn x j) =
          -(accT x u s * (dn (traj x u s) j - dn x j)) := by ring
      rw [e, abs_neg, abs_mul, abs_of_nonneg (accT_nonneg hf s hs)]
      calc accT x u s * |dn (traj x u s) j - dn x j| ≤ amax * (Real.sqrt 2 * Ω * s) :=
            mul_le_mul (accT_le hf s hs) (hdn s hs).1 (abs_nonneg _) hAm.le
        _ = _ := by ring)
  have hp := abs_sub_poly_le (f := fun s => traj x u s (pI j)) (g := fun s => traj x u s (vI j))
    (P := fun s => s * x (vI j) + s ^ 2 / 2 * (grav * ez j) - accK3 x u s * dn x j)
    (p := fun s => x (vI j) + s * (grav * ez j) - accK1 x u s * dn x j)
    (B := fun s => amax * (Real.sqrt 2 * Ω) * s ^ 3 / 6)
    (B' := fun s => amax * (Real.sqrt 2 * Ω) * s ^ 2 / 2)
    (hdp j)
    (fun s => by
      refine ((((hasDerivAt_id s).mul_const _).add (((hasDerivAt_pow 2 s).div_const 2).mul_const _)).sub
        ((hasDerivAt_accK3 x u s).mul_const _)).congr_deriv ?_
      simp)
    (fun s => by
      refine ((hasDerivAt_pow 3 s).const_mul (amax * (Real.sqrt 2 * Ω)) |>.div_const 6).congr_deriv ?_
      push_cast; ring)
    (by simp)
    (fun s hs => by
      have := hv s hs
      simp only [traj_zero, accK1_zero, zero_mul, sub_zero] at this
      rw [show traj x u s (vI j) - (x (vI j) + s * (grav * ez j) - accK1 x u s * dn x j) =
        traj x u s (vI j) - x (vI j) - (s * (grav * ez j) - accK1 x u s * dn x j) by ring]
      exact this)
  intro t ht
  constructor
  · have := hv t ht
    simp only [traj_zero, accK1_zero, zero_mul, sub_zero] at this
    rw [show traj x u t (vI j) - (x (vI j) + t * (grav * ez j) - accK1 x u t * dn x j) =
      traj x u t (vI j) - x (vI j) - (t * (grav * ez j) - accK1 x u t * dn x j) by ring]
    exact this
  · have := hp t ht
    simp only [traj_zero, accK3_zero, zero_mul, sub_zero, ne_eq,
      OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_div, add_zero] at this
    rw [show traj x u t (pI j) - (x (pI j) + t * x (vI j) + t ^ 2 / 2 * (grav * ez j) - accK3 x u t * dn x j) =
      traj x u t (pI j) - x (pI j) - (t * x (vI j) + t ^ 2 / 2 * (grav * ez j) - accK3 x u t * dn x j) by
      ring]
    exact this

/-- The velocity rows of the field are at most `g + a` from a unit quaternion. -/
theorem abs_vf_vI_le (hq : qnormSq x = 1) (j : Fin 3) :
    |vf x u (vI j)| ≤ grav + accel (thr x) := by
  rw [vf_vI]
  have ha := accel_nonneg (thr x)
  obtain ⟨d0, d1, d2⟩ := abs_down_le x
  rw [hq] at d0 d1 d2
  have hd : |dn x j| ≤ 1 := by
    fin_cases j
    exacts [d0, d1, d2]
  have hz : |ez j| ≤ 1 := by fin_cases j <;> simp [ez]
  have h1 : |grav * ez j| ≤ grav := by
    rw [abs_mul, abs_of_pos grav_pos]; nlinarith [grav_pos, abs_nonneg (ez j)]
  have h2 : |accel (thr x) * dn x j| ≤ accel (thr x) := by
    rw [abs_mul, abs_of_nonneg ha]; nlinarith [abs_nonneg (dn x j)]
  calc |grav * ez j - accel (thr x) * dn x j| ≤ |grav * ez j| + |accel (thr x) * dn x j| := abs_sub _ _
    _ ≤ _ := add_le_add h1 h2

/-- **Position change over the period** (intersample corridor): for velocity components at most
`V` and a unit quaternion, every position component moves by at most `V t + (g + amax) t² / 2` on
`[0, h]`, and every velocity component by at most `(g + amax) t`. -/
theorem traj_pos_move (hq : qnormSq x = 1) {V : ℝ} (hV : VBd x V) (j : Fin 3) :
    ∀ t ∈ Icc 0 h, |traj x u t (vI j) - x (vI j)| ≤ (grav + amax) * t ∧
      |traj x u t (pI j) - x (pI j)| ≤ V * t + (grav + amax) * t ^ 2 / 2 := by
  have hdv : ∀ s ∈ Icc 0 h, HasDerivAt (fun s => traj x u s (vI j)) (vf (traj x u s) u (vI j)) s :=
    fun s hs => hasDerivAt_pi.1 (traj_hasDerivAt x u s hs) (vI j)
  have hv := abs_sub_le_of_deriv (C := grav + amax) hdv
    (fun s hs => (abs_vf_vI_le ((qnormSq_traj x u s hs).trans hq) j).trans
      (by linarith [accel_le (thr (traj x u s))]))
  simp only [traj_zero] at hv
  have hp := taylor2 (hdp j) (fun s hs => by simp only [traj_zero]; exact hv s hs)
  simp only [traj_zero] at hp
  have hx : |x (vI j)| ≤ V := by
    obtain ⟨a, b, c⟩ := hV; fin_cases j
    exacts [a, b, c]
  intro t ht
  refine ⟨hv t ht, ?_⟩
  have h1 := hp t ht
  have h2 : |t * x (vI j)| ≤ V * t := by
    rw [abs_mul, abs_of_nonneg ht.1, mul_comm]; exact mul_le_mul_of_nonneg_right hx ht.1
  calc |traj x u t (pI j) - x (pI j)|
      = |(traj x u t (pI j) - x (pI j) - t * x (vI j)) + t * x (vI j)| := by ring_nf
    _ ≤ |traj x u t (pI j) - x (pI j) - t * x (vI j)| + |t * x (vI j)| := abs_add_le _ _
    _ ≤ _ := by linarith

/-- `traj_pos_move` at the end of the period. -/
theorem step_pos_move (hq : qnormSq x = 1) {V : ℝ} (hV : VBd x V) (j : Fin 3) :
    |step x u (vI j) - x (vI j)| ≤ (grav + amax) * h ∧
      |step x u (pI j) - x (pI j)| ≤ V * h + (grav + amax) * h ^ 2 / 2 :=
  traj_pos_move hq hV j h ⟨h_pos.le, le_rfl⟩

end pv

/-! ## The attitude block -/

/-- **The Lipschitz constant of the attitude block of the field** on unit quaternions and rates at
most `Ω`: `max((3/2)(1 + Ω), 2 gyro Ω)`. No position or velocity enters. -/
def Katt (Ω : ℝ) : ℝ := max ((3 / 2) * (1 + Ω)) (2 * gyro * Ω)

theorem Katt_pos {Ω : ℝ} (hΩ : 0 ≤ Ω) : 0 < Katt Ω :=
  lt_max_of_lt_left (by positivity)

/-- The attitude block of the field at a state: at most `attF0 W A` from a unit quaternion with
rates at most `W` under the torque bound `A`. -/
def attF0 (W A : ℝ) : ℝ := max ((3 / 2) * W) (A + gyro * W ^ 2)

private theorem att_coords {x y : X} {D : ℝ} (hD : ‖att x - att y‖ ≤ D) :
    QBd (x - y) D ∧ WBd (x - y) D := by
  have c : ∀ i : Fin 7, |(x - y) ⟨i.val + 6, by omega⟩| ≤ D := fun i => by
    have := norm_le_pi_norm (att x - att y) i
    rw [Real.norm_eq_abs] at this
    exact this.trans hD
  exact ⟨⟨c 0, c 1, c 2, c 3⟩, ⟨c 4, c 5, c 6⟩⟩

/-- **The attitude block of the field is Lipschitz** with constant `Katt Ω` in the attitude coordinates, plus
`2 alphaMax` per unit of thrust difference, between a state with a quaternion in the unit cube and rates at most `Ω`
and a state with rates at most `Ω`. -/
theorem vf_att_lipschitz {x y : X} (u : Fin 4 → ℝ) {Ω Df : ℝ} (hx : QBd x 1) (hwx : WBd x Ω)
    (hwy : WBd y Ω) (hf : FBd (x - y) Df) :
    ‖att (vf x u) - att (vf y u)‖ ≤ Katt Ω * ‖att x - att y‖ + 2 * alphaMax * Df := by
  set D := ‖att x - att y‖
  have hD : 0 ≤ D := norm_nonneg _
  have hΩ : 0 ≤ Ω := (abs_nonneg _).trans hwx.1
  have hDf : 0 ≤ Df := (abs_nonneg _).trans hf.1
  have hal := alphaMax_pos
  obtain ⟨dq, dw⟩ := att_coords (le_refl D)
  have hq := vf_sub_q (u := u) hx hwy dq dw
  have hw := vf_sub_w (u := u) hwx hwy dw hf
  have kq : (3 / 2) * (1 * D + Ω * D) ≤ Katt Ω * D + 2 * alphaMax * Df := by
    rw [show (3 / 2) * (1 * D + Ω * D) = (3 / 2) * (1 + Ω) * D by ring]
    have := mul_le_mul_of_nonneg_right (le_max_left ((3 / 2) * (1 + Ω)) (2 * gyro * Ω)) hD
    have : 0 ≤ 2 * alphaMax * Df := by positivity
    unfold Katt; linarith
  have kw : gyro * (2 * Ω * D) + 2 * alphaMax * Df ≤ Katt Ω * D + 2 * alphaMax * Df := by
    rw [show gyro * (2 * Ω * D) = 2 * gyro * Ω * D by ring]
    have := mul_le_mul_of_nonneg_right (le_max_right ((3 / 2) * (1 + Ω)) (2 * gyro * Ω)) hD
    unfold Katt; linarith
  refine (pi_norm_le_iff_of_nonneg (by have := Katt_pos hΩ; positivity)).2 fun i => ?_
  rw [Real.norm_eq_abs, Pi.sub_apply]
  fin_cases i
  · exact hq.1.trans kq
  · exact hq.2.1.trans kq
  · exact hq.2.2.1.trans kq
  · exact hq.2.2.2.trans kq
  · exact hw.1.trans kw
  · exact hw.2.1.trans kw
  · exact hw.2.2.trans kw

/-- The attitude block of the field at the initial state. -/
theorem norm_att_vf_le {x : X} {u : Fin 4 → ℝ} {W A : ℝ} (hq : qnormSq x = 1) (hW : WBd x W)
    (hA : TorqueBd (thr x) A) : ‖att (vf x u)‖ ≤ attF0 W A := by
  have hb := abs_vf_q x u (QBd_one_of_unit hq) hW
  have hw := abs_vf_wA x (u := u) hW hA
  have hW0 : 0 ≤ W := (abs_nonneg _).trans hW.1
  have kq : (3 / 2) * (1 * W) ≤ attF0 W A := by
    rw [one_mul]; exact le_max_left _ _
  have kw : A + gyro * W ^ 2 ≤ attF0 W A := le_max_right _ _
  refine (pi_norm_le_iff_of_nonneg ((by positivity : (0 : ℝ) ≤ (3 / 2) * W).trans
    (le_max_left _ _))).2 fun i => ?_
  rw [Real.norm_eq_abs]
  fin_cases i
  · exact hb.1.trans kq
  · exact hb.2.1.trans kq
  · exact hb.2.2.1.trans kq
  · exact hb.2.2.2.trans kq
  · exact hw.1.trans kw
  · exact hw.2.1.trans kw
  · exact hw.2.2.trans kw

/-- **Grönwall on the attitude block alone**, along the period, with the lagged thrust as a forcing term:
`‖(q, ω)(t) - (q, ω)(0)‖ ≤ gronwallBound 0 (Katt Ω) (‖(q̇, ω̇)(0)‖ + 2 alphaMax Mf h) t`. -/
theorem traj_qw_gronwall {x : X} {u : Fin 4 → ℝ} {W A Ω : ℝ} (hq : qnormSq x = 1)
    (hW : WBd x W) (hA : TorqueBdT x u A) (hf : ThrustRange x) (hΩ : wTA W A ≤ Ω) :
    ∀ t ∈ Icc 0 h, ‖att (traj x u t) - att x‖ ≤
      gronwallBound 0 (Katt Ω) (‖att (vf x u)‖ + 2 * alphaMax * (Mf * h)) t := by
  have hur := traj_unit_rates hq hW hA hΩ
  have hWx : WBd x Ω := WBd_mono hW ((le_wTA hA.nonneg).trans hΩ)
  have hd : ∀ s ∈ Icc 0 h, HasDerivAt (fun s => att (traj x u s)) (att (vf (traj x u s) u)) s :=
    fun s hs => hasDerivAt_pi.2 fun i => hasDerivAt_pi.1 (traj_hasDerivAt x u s hs) _
  have hal := alphaMax_pos
  intro t ht
  have := norm_le_gronwallBound_of_norm_deriv_right_le (f := fun s => att (traj x u s) - att x)
    (f' := fun s => att (vf (traj x u s) u)) (δ := 0) (K := Katt Ω)
    (ε := ‖att (vf x u)‖ + 2 * alphaMax * (Mf * h)) (a := 0) (b := h)
    (fun s hs => ((hd s hs).sub_const _).continuousAt.continuousWithinAt)
    (fun s hs => ((hd s (Ico_subset_Icc_self hs)).sub_const _).hasDerivWithinAt)
    (by simp [traj_zero])
    (fun s hs => by
      have hs' := Ico_subset_Icc_self hs
      obtain ⟨-, -, -, df⟩ := traj_moves (u := u) (le_of_eq hq) hW hf 0 ⟨le_rfl, h_pos.le⟩ s hs'
      rw [traj_zero, sub_zero, abs_of_nonneg hs'.1] at df
      have hdf : FBd (traj x u s - x) (Mf * h) := by
        have hm : Mf * s ≤ Mf * h := mul_le_mul_of_nonneg_left hs'.2 (by unfold Mf; have := tauUp_pos; positivity)
        obtain ⟨a, b, c, d⟩ := df
        exact ⟨a.trans hm, b.trans hm, c.trans hm, d.trans hm⟩
      have h1 := vf_att_lipschitz u (QBd_one_of_unit (hur s hs').1) (hur s hs').2 hWx hdf
      calc ‖att (vf (traj x u s) u)‖
          = ‖(att (vf (traj x u s) u) - att (vf x u)) + att (vf x u)‖ := by rw [sub_add_cancel]
        _ ≤ ‖att (vf (traj x u s) u) - att (vf x u)‖ + ‖att (vf x u)‖ := norm_add_le _ _
        _ ≤ _ := by linarith) t ht
  simpa using this

/-- **The attitude block over one period** (`step_qw_gronwall`):
`‖(q, ω)(h) - (q, ω)(0)‖ ≤ (attF0 W A + 2 alphaMax Mf h) / Katt Ω · (e^{Katt Ω · h} - 1)`. -/
theorem step_qw_gronwall {x : X} {u : Fin 4 → ℝ} {W A Ω : ℝ} (hq : qnormSq x = 1)
    (hW : WBd x W) (hA : TorqueBdT x u A) (hf : ThrustRange x) (hΩ : wTA W A ≤ Ω) :
    ‖att (step x u) - att x‖ ≤
      (attF0 W A + 2 * alphaMax * (Mf * h)) / Katt Ω * (Real.exp (Katt Ω * h) - 1) := by
  have hΩ0 : 0 ≤ Ω := ((abs_nonneg _).trans hW.1).trans ((le_wTA hA.nonneg).trans hΩ)
  have hK := Katt_pos hΩ0
  have := traj_qw_gronwall hq hW hA hf hΩ h ⟨h_pos.le, le_rfl⟩
  rw [gronwallBound_of_K_ne_0 hK.ne'] at this
  simp only [zero_mul, zero_add] at this
  refine this.trans ?_
  have he : 0 ≤ Real.exp (Katt Ω * h) - 1 := by
    have := Real.add_one_le_exp (Katt Ω * h)
    have : 0 ≤ Katt Ω * h := mul_nonneg hK.le h_pos.le
    linarith
  exact mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right
    (add_le_add (norm_att_vf_le hq hW hA.zero) le_rfl) hK.le) he

/-- Bound of `|q̇ⱼ|` on unit quaternions with rates at most `Ω`. -/
def Mq1 (Ω : ℝ) : ℝ := (3 / 2) * Ω

/-- Bound of `|ω̇ⱼ|` with rates at most `Ω` under the torque bound `A`. -/
def Mw1 (A Ω : ℝ) : ℝ := A + gyro * Ω ^ 2

/-- Lipschitz-in-time constant of the quaternion rows of the field along the period. -/
def cQ (A Ω : ℝ) : ℝ := (3 / 2) * (Mw1 A Ω + Ω * Mq1 Ω)

/-- Lipschitz-in-time constant of the rate rows of the field along the period (the lagged thrust moves the
torques by at most `2 alphaMax Mf` per second). -/
def cW (A Ω : ℝ) : ℝ := gyro * (2 * Ω * Mw1 A Ω) + 2 * alphaMax * Mf

/-- **The attitude block to second order**, coordinate by coordinate, along the period:
`|q(t) - q - t q̇| ≤ cQ t² / 2`, `|ω(t) - ω - t ω̇| ≤ cW t² / 2`, together with the first-order
moves `|q(t) - q| ≤ Mq1 t`, `|ω(t) - ω| ≤ Mw1 t`. -/
theorem traj_att_taylor {x : X} {u : Fin 4 → ℝ} {W A Ω : ℝ} (hq : qnormSq x = 1)
    (hW : WBd x W) (hA : TorqueBdT x u A) (hf : ThrustRange x) (hΩ : wTA W A ≤ Ω) : ∀ t ∈ Icc 0 h,
      (∀ i : Fin 4, |traj x u t (qI i) - x (qI i)| ≤ Mq1 Ω * t ∧
        |traj x u t (qI i) - x (qI i) - t * vf x u (qI i)| ≤ cQ A Ω * t ^ 2 / 2) ∧
      (∀ k : Fin 3, |traj x u t (wI k) - x (wI k)| ≤ Mw1 A Ω * t ∧
        |traj x u t (wI k) - x (wI k) - t * vf x u (wI k)| ≤ cW A Ω * t ^ 2 / 2) := by
  have hur := traj_unit_rates hq hW hA hΩ
  have hΩ0 : 0 ≤ Ω := ((abs_nonneg _).trans hW.1).trans ((le_wTA hA.nonneg).trans hΩ)
  have hd : ∀ j, ∀ r ∈ Icc 0 h, HasDerivAt (fun r => traj x u r j) (vf (traj x u r) u j) r :=
    fun j r hr => hasDerivAt_pi.1 (traj_hasDerivAt x u r hr) j
  have bq := fun r hr => abs_vf_q (traj x u r) u (QBd_one_of_unit (hur r hr).1) (hur r hr).2
  have bw := fun r hr => abs_vf_wA (traj x u r) (u := u) (hur r hr).2 (hA r hr)
  -- first-order moves
  have mq : ∀ j, (∀ r ∈ Icc 0 h, |vf (traj x u r) u j| ≤ (3 / 2) * (1 * Ω)) →
      ∀ t ∈ Icc 0 h, |traj x u t j - x j| ≤ Mq1 Ω * t := fun j hb t ht => by
    have := abs_sub_le_of_deriv (hd j) hb t ht
    simpa [traj_zero, Mq1] using this
  have mw : ∀ j, (∀ r ∈ Icc 0 h, |vf (traj x u r) u j| ≤ A + gyro * Ω ^ 2) →
      ∀ t ∈ Icc 0 h, |traj x u t j - x j| ≤ Mw1 A Ω * t := fun j hb t ht => by
    have := abs_sub_le_of_deriv (hd j) hb t ht
    simpa [traj_zero, Mw1] using this
  have hmq : ∀ t ∈ Icc 0 h, QBd (traj x u t - x) (Mq1 Ω * t) := fun t ht =>
    ⟨mq 6 (fun r hr => (bq r hr).1) t ht, mq 7 (fun r hr => (bq r hr).2.1) t ht,
      mq 8 (fun r hr => (bq r hr).2.2.1) t ht, mq 9 (fun r hr => (bq r hr).2.2.2) t ht⟩
  have hmw : ∀ t ∈ Icc 0 h, WBd (traj x u t - x) (Mw1 A Ω * t) := fun t ht =>
    ⟨mw 10 (fun r hr => (bw r hr).1) t ht, mw 11 (fun r hr => (bw r hr).2.1) t ht,
      mw 12 (fun r hr => (bw r hr).2.2) t ht⟩
  have hmf : ∀ t ∈ Icc 0 h, FBd (traj x u t - x) (Mf * t) := fun t ht => by
    obtain ⟨-, -, -, df⟩ := traj_moves (u := u) (le_of_eq hq) hW hf 0 ⟨le_rfl, h_pos.le⟩ t ht
    rwa [traj_zero, sub_zero, abs_of_nonneg ht.1] at df
  have hWx : WBd x Ω := WBd_mono hW ((le_wTA hA.nonneg).trans hΩ)
  -- the field rows are Lipschitz in time
  have lq : ∀ t ∈ Icc 0 h, ∀ i : Fin 4,
      |vf (traj x u t) u (qI i) - vf x u (qI i)| ≤ cQ A Ω * t := by
    intro t ht i
    have := vf_sub_q (u := u) (QBd_one_of_unit (hur t ht).1) hWx (hmq t ht) (hmw t ht)
    have e : (3 / 2) * (1 * (Mw1 A Ω * t) + Ω * (Mq1 Ω * t)) = cQ A Ω * t := by
      unfold cQ; ring
    rw [e] at this
    fin_cases i
    exacts [this.1, this.2.1, this.2.2.1, this.2.2.2]
  have lw : ∀ t ∈ Icc 0 h, ∀ k : Fin 3,
      |vf (traj x u t) u (wI k) - vf x u (wI k)| ≤ cW A Ω * t := by
    intro t ht k
    have := vf_sub_w (u := u) (hur t ht).2 hWx (hmw t ht) (hmf t ht)
    have e : gyro * (2 * Ω * (Mw1 A Ω * t)) + 2 * alphaMax * (Mf * t) = cW A Ω * t := by
      unfold cW; ring
    rw [e] at this
    fin_cases k
    exacts [this.1, this.2.1, this.2.2]
  intro t ht
  refine ⟨fun i => ⟨?_, ?_⟩, fun k => ⟨?_, ?_⟩⟩
  · have := hmq t ht
    fin_cases i
    exacts [this.1, this.2.1, this.2.2.1, this.2.2.2]
  · have := taylor2 (hd (qI i)) (fun s hs => by simpa [traj_zero] using lq s hs i) t ht
    simpa [traj_zero] using this
  · have := hmw t ht
    fin_cases k
    exacts [this.1, this.2.1, this.2.2]
  · have := taylor2 (hd (wI k)) (fun s hs => by simpa [traj_zero] using lw s hs k) t ht
    simpa [traj_zero] using this

end

end Plant
