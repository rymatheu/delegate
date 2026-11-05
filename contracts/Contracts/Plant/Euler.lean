module

public import Contracts.Plant.Flow

/-!
# The step against one forward-Euler step

`eulerStep x u = x + h F(x, u)` is the forward-Euler step of the same vector field, in the same
(quaternion) coordinates. Over one period from a state with `‖q‖² ≤ Q` and body rates at most `W`,
* the quaternion stays at `|qⱼ| ≤ √Q`, and the rates at `|ωⱼ| ≤ wB W` (energy estimate), hence
  at `|ωⱼ| ≤ wT W = W + h (alphaMax + gyro (wB W)²)` (one period of the largest angular
  acceleration on that box),
* hence along the trajectory `|v̇ⱼ| ≤ Mv = g + amax Q`, `|q̇ⱼ| ≤ Mq = (3/2) √Q wT W`,
  `|ω̇ⱼ| ≤ Mw = alphaMax + gyro (wT W)²`,
* hence each component of `F(γ t, u) - F(γ s, u)` is at most `cE Q W |t - s|`, block by block
  (`cE`, from the block Lipschitz bounds of `Bounds.lean`),
* hence `‖step x u - eulerStep x u‖ ≤ (cE Q W / 2) h²` (`step_sub_eulerStep_le`).

The same estimate anchored at the end of the period bounds the gap between the specific force the
driver reports, the backward difference `(v(t) - v(t - h)) / h - g e_z` of the exact velocity
(`run_copter.py:160-162`), and the instantaneous specific force `-(T/m) d(q)` of the model at the
tick (`backwardDiff_sub_specForce`): at most `8 amax √Q Mq · h / 2`.

`Contracts.CopterPlant.dynR` (the port's Euler plant) is the forward-Euler step in ZYX Euler-angle
coordinates; its `p`, `v`, `ω` rows are the rows of `eulerStep` here once its `thrustDir att` is
the down axis `d(q)` of the quaternion of `att`, and its attitude row is the Euler step of the
Euler-angle kinematics, which agrees with the quaternion row to first order in `h` only.
-/

@[expose] public section

namespace Contracts.Plant

noncomputable section

open Set

/-- **One forward-Euler step** of `F(·, u)` over the control period. -/
def eulerStep (x : X) (u : Fin 4 → ℝ) : X := x + h • vf x u

/-! ## Block bounds along the trajectory -/

theorem QBd_of_qnormSq_le {y : X} {Q : ℝ} (hQ : qnormSq y ≤ Q) : QBd y (Real.sqrt Q) := by
  unfold qnormSq at hQ
  have := sq_nonneg (y 6); have := sq_nonneg (y 7); have := sq_nonneg (y 8)
  have := sq_nonneg (y 9)
  exact ⟨Real.abs_le_sqrt (by linarith), Real.abs_le_sqrt (by linarith),
    Real.abs_le_sqrt (by linarith), Real.abs_le_sqrt (by linarith)⟩

theorem energy_le_of_WBd {y : X} {W : ℝ} (hW : WBd y W) : energy y ≤ (Jx + Jy + Jz) * W ^ 2 := by
  obtain ⟨a, b, c⟩ := hW
  have sq_le : ∀ {a b : ℝ}, |a| ≤ b → a ^ 2 ≤ b ^ 2 := fun hab =>
    sq_le_sq' (abs_le.mp hab).1 (abs_le.mp hab).2
  have := sq_le a; have := sq_le b; have := sq_le c
  have := Jx_pos; have := Jy_pos; have := Jz_pos
  unfold energy; nlinarith

theorem WBd_of_energy_le {y : X} {E : ℝ} (hE : energy y ≤ E) : WBd y (Real.sqrt (E / Jx)) := by
  have := Jx_pos; have := Jy_pos; have := Jz_pos; have := Jx_le_Jz; have hy := Jy_eq_Jx
  have := sq_nonneg (y 10); have := sq_nonneg (y 11); have := sq_nonneg (y 12)
  unfold energy at hE
  refine ⟨Real.abs_le_sqrt ?_, Real.abs_le_sqrt ?_, Real.abs_le_sqrt ?_⟩ <;>
    rw [le_div_iff₀ Jx_pos]
  · nlinarith
  · rw [hy] at hE; nlinarith
  · nlinarith

section traj
variable {x : X} {u : Fin 4 → ℝ} {Q W : ℝ}

theorem QBd_traj (hQ : qnormSq x ≤ Q) : ∀ t ∈ Icc 0 h, QBd (traj x u t) (Real.sqrt Q) :=
  fun t ht => QBd_of_qnormSq_le (by rw [qnormSq_traj x u t ht]; exact hQ)

/-- Rates along the trajectory, by the energy estimate. -/
theorem WBd_traj_energy (hW : WBd x W) : ∀ t ∈ Icc 0 h, WBd (traj x u t) (wB W) := by
  intro t ht
  have hE := energy_scaledSol (scaledSol_traj x u h) t ht
  rw [traj_zero] at hE
  have hE0 := energy_le_of_WBd hW
  have hexp : Real.exp (t / h) ≤ Real.exp 1 := by
    rw [Real.exp_le_exp, div_le_one h_pos]; exact ht.2
  have hc := ctau_nonneg
  have hEt : energy (traj x u t) ≤ ((Jx + Jy + Jz) * W ^ 2 + ctau * h ^ 2) * Real.exp 1 := by
    have := energy_nonneg x
    have : (energy x + ctau * h ^ 2) * Real.exp (t / h) ≤
        ((Jx + Jy + Jz) * W ^ 2 + ctau * h ^ 2) * Real.exp 1 :=
      mul_le_mul (by linarith) hexp (Real.exp_pos _).le
        (add_nonneg (mul_nonneg (by norm_num [Jx, Jy, Jz]) (sq_nonneg W))
          (mul_nonneg hc (sq_nonneg h)))
    nlinarith
  exact WBd_of_energy_le hEt

/-- Rates along the trajectory, refined: the start value plus one period of the largest angular
acceleration on the energy box, `W + h (alphaMax + gyro (wB W)²)`. -/
def wT (W : ℝ) : ℝ := W + h * (alphaMax + gyro * wB W ^ 2)

/-- **Rates along the trajectory**: `|ωⱼ(t)| ≤ wT W` on `[0, h]`. -/
theorem WBd_traj (hW : WBd x W) : ∀ t ∈ Icc 0 h, WBd (traj x u t) (wT W) := by
  intro t ht
  have hd : ∀ j, ∀ r ∈ Icc 0 h, HasDerivAt (fun r => traj x u r j) (vf (traj x u r) u j) r :=
    fun j r hr => hasDerivAt_pi.1 (traj_hasDerivAt x u r hr) j
  have bw := fun r hr => abs_vf_w (traj x u r) u (WBd_traj_energy hW r hr)
  have hM : 0 ≤ alphaMax + gyro * wB W ^ 2 := by
    have := alphaMax_pos
    have : (0 : ℝ) ≤ gyro := by norm_num [gyro]
    positivity
  have one : ∀ j, |x j| ≤ W → (∀ r ∈ Icc 0 h, |vf (traj x u r) u j| ≤
      alphaMax + gyro * wB W ^ 2) → |traj x u t j| ≤ wT W := by
    intro j hx hb
    have h1 := abs_sub_le_of_deriv (hd j) hb t ht
    simp only [traj_zero] at h1
    have h2 : (alphaMax + gyro * wB W ^ 2) * t ≤ h * (alphaMax + gyro * wB W ^ 2) := by
      rw [mul_comm]; exact mul_le_mul_of_nonneg_right ht.2 hM
    have := abs_sub_abs_le_abs_sub (traj x u t j) (x j)
    unfold wT; linarith
  obtain ⟨w10, w11, w12⟩ := hW
  exact ⟨one 10 w10 fun r hr => (bw r hr).1, one 11 w11 fun r hr => (bw r hr).2.1,
    one 12 w12 fun r hr => (bw r hr).2.2⟩

end traj

/-- A real function with derivative bounded by `C` on `[a, b]` is `C`-Lipschitz there. -/
theorem abs_sub_le_of_deriv_Icc {f g : ℝ → ℝ} {a b C : ℝ}
    (hd : ∀ t ∈ Icc a b, HasDerivAt f (g t) t) (hb : ∀ t ∈ Icc a b, |g t| ≤ C) :
    ∀ s ∈ Icc a b, ∀ t ∈ Icc a b, |f t - f s| ≤ C * |t - s| := by
  have key : ∀ s ∈ Icc a b, ∀ t ∈ Icc a b, s ≤ t → |f t - f s| ≤ C * |t - s| := by
    intro s hs t ht hst
    have := norm_image_sub_le_of_norm_deriv_le_segment' (f := f) (f' := g) (C := C) (a := s)
      (b := t) (fun r hr => (hd r ⟨hs.1.trans hr.1, hr.2.trans ht.2⟩).hasDerivWithinAt)
      (fun r hr => hb r ⟨hs.1.trans hr.1, hr.2.le.trans ht.2⟩) t ⟨hst, le_rfl⟩
    rw [Real.norm_eq_abs] at this
    rwa [abs_of_nonneg (sub_nonneg.2 hst)]
  intro s hs t ht
  rcases le_total s t with hst | hts
  · exact key s hs t ht hst
  · rw [abs_sub_comm, abs_sub_comm t]; exact key t ht s hs hts

/-! ## Constants -/

/-- Bound of `|v̇ⱼ|` along the trajectory. -/
def Mv (Q : ℝ) : ℝ := grav + amax * Q
/-- Bound of `|q̇ⱼ|` along the trajectory. -/
def Mq (Q W : ℝ) : ℝ := (3 / 2) * (Real.sqrt Q * wT W)
/-- Bound of `|ω̇ⱼ|` along the trajectory. -/
def Mw (W : ℝ) : ℝ := alphaMax + gyro * wT W ^ 2

/-- Lipschitz-in-time constant of the `v` rows of `F` along the trajectory. -/
def cV (Q W : ℝ) : ℝ := amax * (8 * Real.sqrt Q * Mq Q W)

/-- **The Lipschitz-in-time constant of `F` along the trajectory**: the largest of the block
constants `Mv` (`p` rows), `8 amax √Q Mq` (`v` rows), `(3/2)(√Q Mw + wT W · Mq)` (`q` rows),
`2 gyro (wT W) Mw` (`ω` rows). -/
def cE (Q W : ℝ) : ℝ :=
  max (max (Mv Q) (cV Q W))
    (max ((3 / 2) * (Real.sqrt Q * Mw W + wT W * Mq Q W)) (gyro * (2 * wT W * Mw W)))

/-- **The Euler constant**: `‖step x u - eulerStep x u‖ ≤ eulerC Q W · h²`. -/
def eulerC (Q W : ℝ) : ℝ := cE Q W / 2

section traj
variable {x : X} {u : Fin 4 → ℝ} {Q W : ℝ}

/-- Rates of the trajectory, block by block. -/
theorem traj_moves (hQ : qnormSq x ≤ Q) (hW : WBd x W) :
    ∀ s ∈ Icc 0 h, ∀ t ∈ Icc 0 h,
      VBd (traj x u t - traj x u s) (Mv Q * |t - s|) ∧
      QBd (traj x u t - traj x u s) (Mq Q W * |t - s|) ∧
      WBd (traj x u t - traj x u s) (Mw W * |t - s|) := by
  intro s hs t ht
  have hd : ∀ j, ∀ r ∈ Icc 0 h, HasDerivAt (fun r => traj x u r j) (vf (traj x u r) u j) r :=
    fun j r hr => hasDerivAt_pi.1 (traj_hasDerivAt x u r hr) j
  have mv : ∀ j, (∀ r ∈ Icc 0 h, |vf (traj x u r) u j| ≤ Mv Q) →
      |(traj x u t - traj x u s) j| ≤ Mv Q * |t - s| := fun j hb => by
    rw [Pi.sub_apply]; exact abs_sub_le_of_deriv_Icc (hd j) hb s hs t ht
  have mq : ∀ j, (∀ r ∈ Icc 0 h, |vf (traj x u r) u j| ≤ Mq Q W) →
      |(traj x u t - traj x u s) j| ≤ Mq Q W * |t - s| := fun j hb => by
    rw [Pi.sub_apply]; exact abs_sub_le_of_deriv_Icc (hd j) hb s hs t ht
  have mw : ∀ j, (∀ r ∈ Icc 0 h, |vf (traj x u r) u j| ≤ Mw W) →
      |(traj x u t - traj x u s) j| ≤ Mw W * |t - s| := fun j hb => by
    rw [Pi.sub_apply]; exact abs_sub_le_of_deriv_Icc (hd j) hb s hs t ht
  have bv : ∀ r ∈ Icc 0 h, |vf (traj x u r) u 3| ≤ Mv Q ∧ |vf (traj x u r) u 4| ≤ Mv Q ∧
      |vf (traj x u r) u 5| ≤ Mv Q := by
    intro r hr
    obtain ⟨a, b, c⟩ := abs_vf_v (traj x u r) u
    rw [qnormSq_traj x u r hr] at a b c
    have := amax_pos; have := grav_pos
    have e : amax * qnormSq x ≤ amax * Q := mul_le_mul_of_nonneg_left hQ amax_pos.le
    refine ⟨a.trans ?_, b.trans ?_, c.trans ?_⟩ <;> unfold Mv <;> linarith
  have bq := fun r hr => abs_vf_q (traj x u r) u (QBd_traj hQ r hr) (WBd_traj hW r hr)
  have bw := fun r hr => abs_vf_w (traj x u r) u (WBd_traj hW r hr)
  exact ⟨⟨mv 3 fun r hr => (bv r hr).1, mv 4 fun r hr => (bv r hr).2.1,
      mv 5 fun r hr => (bv r hr).2.2⟩,
    ⟨mq 6 fun r hr => (bq r hr).1, mq 7 fun r hr => (bq r hr).2.1,
      mq 8 fun r hr => (bq r hr).2.2.1, mq 9 fun r hr => (bq r hr).2.2.2⟩,
    ⟨mw 10 fun r hr => (bw r hr).1, mw 11 fun r hr => (bw r hr).2.1,
      mw 12 fun r hr => (bw r hr).2.2⟩⟩

/-- **The field is Lipschitz in time along the trajectory**, component by component. -/
theorem vf_traj_sub (hQ : qnormSq x ≤ Q) (hW : WBd x W) :
    ∀ s ∈ Icc 0 h, ∀ t ∈ Icc 0 h, ∀ j,
      |vf (traj x u t) u j - vf (traj x u s) u j| ≤ cE Q W * |t - s| := by
  intro s hs t ht j
  obtain ⟨dv, dq, dw⟩ := traj_moves (u := u) hQ hW s hs t ht
  set d := |t - s|
  have hd : 0 ≤ d := abs_nonneg _
  have hp := vf_sub_p (u := u) dv
  have hv := vf_sub_v (u := u) (QBd_traj hQ t ht) (QBd_traj hQ s hs) dq
  have hq := vf_sub_q (u := u) (QBd_traj hQ t ht) (WBd_traj hW s hs) dq dw
  have hw := vf_sub_w (u := u) (WBd_traj hW t ht) (WBd_traj hW s hs) dw
  have kp : Mv Q * d ≤ cE Q W * d :=
    mul_le_mul_of_nonneg_right (le_max_of_le_left (le_max_left _ _)) hd
  have kv : amax * (8 * Real.sqrt Q * (Mq Q W * d)) ≤ cE Q W * d := by
    have : amax * (8 * Real.sqrt Q * (Mq Q W * d)) = cV Q W * d := by unfold cV; ring
    rw [this]; exact mul_le_mul_of_nonneg_right (le_max_of_le_left (le_max_right _ _)) hd
  have kq : (3 / 2) * (Real.sqrt Q * (Mw W * d) + wT W * (Mq Q W * d)) ≤ cE Q W * d := by
    have : (3 / 2) * (Real.sqrt Q * (Mw W * d) + wT W * (Mq Q W * d)) =
        (3 / 2) * (Real.sqrt Q * Mw W + wT W * Mq Q W) * d := by ring
    rw [this]; exact mul_le_mul_of_nonneg_right (le_max_of_le_right (le_max_left _ _)) hd
  have kw : gyro * (2 * wT W * (Mw W * d)) ≤ cE Q W * d := by
    have : gyro * (2 * wT W * (Mw W * d)) = gyro * (2 * wT W * Mw W) * d := by ring
    rw [this]; exact mul_le_mul_of_nonneg_right (le_max_of_le_right (le_max_right _ _)) hd
  fin_cases j
  · exact hp.1.trans kp
  · exact hp.2.1.trans kp
  · exact hp.2.2.trans kp
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

/-- The `v` rows of the field are `cV`-Lipschitz in time along the trajectory. -/
theorem vf_traj_sub_v (hQ : qnormSq x ≤ Q) (hW : WBd x W) :
    ∀ s ∈ Icc 0 h, ∀ t ∈ Icc 0 h,
      |vf (traj x u t) u 3 - vf (traj x u s) u 3| ≤ cV Q W * |t - s| ∧
      |vf (traj x u t) u 4 - vf (traj x u s) u 4| ≤ cV Q W * |t - s| ∧
      |vf (traj x u t) u 5 - vf (traj x u s) u 5| ≤ cV Q W * |t - s| := by
  intro s hs t ht
  obtain ⟨-, dq, -⟩ := traj_moves (u := u) hQ hW s hs t ht
  have hv := vf_sub_v (u := u) (QBd_traj hQ t ht) (QBd_traj hQ s hs) dq
  have e : amax * (8 * Real.sqrt Q * (Mq Q W * |t - s|)) = cV Q W * |t - s| := by
    unfold cV; ring
  rw [e] at hv; exact hv

end traj

/-! ## Taylor remainders over one period -/

/-- Forward remainder: if `|g t - g 0| ≤ c t` on `[0, h]` and `f' = g`, then
`|f h - f 0 - h g 0| ≤ c h² / 2`. -/
theorem remainder_fwd {f g : ℝ → ℝ} {c : ℝ} (hd : ∀ t ∈ Icc 0 h, HasDerivAt f (g t) t)
    (hc : ∀ t ∈ Icc 0 h, |g t - g 0| ≤ c * t) : |f h - f 0 - h * g 0| ≤ c * h ^ 2 / 2 := by
  have := image_norm_le_of_norm_deriv_right_le_deriv_boundary
    (f := fun t => f t - f 0 - t * g 0) (f' := fun t => g t - g 0) (a := 0) (b := h)
    (B := fun t => c * t ^ 2 / 2) (B' := fun t => c * t)
    (fun t ht => (((hd t ht).sub_const (f 0)).sub (hasDerivAt_mul_const (g 0))).continuousAt
      |>.continuousWithinAt)
    (fun t ht => (((hd t (Ico_subset_Icc_self ht)).sub_const (f 0)).sub
        (hasDerivAt_mul_const (g 0))).hasDerivWithinAt)
    (by simp)
    (fun t => by
      have := ((hasDerivAt_pow 2 t).const_mul c).div_const 2
      convert this using 1; ring)
    (fun t ht => by rw [Real.norm_eq_abs]; exact hc t (Ico_subset_Icc_self ht))
    (right_mem_Icc.2 h_pos.le)
  simpa [Real.norm_eq_abs] using this

/-- Backward remainder: if `|g t - g h| ≤ c (h - t)` on `[0, h]` and `f' = g`, then
`|f h - f 0 - h g h| ≤ c h² / 2`. -/
theorem remainder_bwd {f g : ℝ → ℝ} {c : ℝ} (hd : ∀ t ∈ Icc 0 h, HasDerivAt f (g t) t)
    (hc : ∀ t ∈ Icc 0 h, |g t - g h| ≤ c * (h - t)) :
    |f h - f 0 - h * g h| ≤ c * h ^ 2 / 2 := by
  have := image_norm_le_of_norm_deriv_right_le_deriv_boundary
    (f := fun t => f t - f 0 - t * g h) (f' := fun t => g t - g h) (a := 0) (b := h)
    (B := fun t => c * (h ^ 2 - (h - t) ^ 2) / 2) (B' := fun t => c * (h - t))
    (fun t ht => (((hd t ht).sub_const (f 0)).sub (hasDerivAt_mul_const (g h))).continuousAt
      |>.continuousWithinAt)
    (fun t ht => (((hd t (Ico_subset_Icc_self ht)).sub_const (f 0)).sub
        (hasDerivAt_mul_const (g h))).hasDerivWithinAt)
    (by simp)
    (fun t => by
      have := ((((hasDerivAt_id' t).const_sub h).pow 2).const_sub (h ^ 2) |>.const_mul c).div_const 2
      convert this using 1; simp; ring)
    (fun t ht => by rw [Real.norm_eq_abs]; exact hc t (Ico_subset_Icc_self ht))
    (right_mem_Icc.2 h_pos.le)
  simpa [Real.norm_eq_abs] using this

/-! ## The comparison -/

/-- **The step against one Euler step.** From a state with `‖q‖² ≤ Q` and body rates at most `W`,
the exact step and the forward-Euler step of the same field differ by at most
`eulerC Q W · h²` in the sup norm. -/
theorem step_sub_eulerStep_le {x : X} {u : Fin 4 → ℝ} {Q W : ℝ} (hQ : qnormSq x ≤ Q)
    (hW : WBd x W) : ‖step x u - eulerStep x u‖ ≤ eulerC Q W * h ^ 2 := by
  have hc0 : 0 ≤ cE Q W := le_max_of_le_left (le_max_of_le_left (by
    have := amax_pos; have := grav_pos; unfold Mv
    nlinarith [qnormSq_nonneg x]))
  refine norm_le_of_abs_le (by unfold eulerC; positivity) fun j => ?_
  have h0 : (0 : ℝ) ∈ Icc 0 h := ⟨le_rfl, h_pos.le⟩
  have := remainder_fwd (f := fun t => traj x u t j) (g := fun t => vf (traj x u t) u j)
    (c := cE Q W) (fun t ht => hasDerivAt_pi.1 (traj_hasDerivAt x u t ht) j)
    (fun t ht => by
      have := vf_traj_sub (u := u) hQ hW 0 h0 t ht j
      rwa [sub_zero, abs_of_nonneg ht.1] at this)
  simp only [traj_zero] at this
  simp only [step, eulerStep, Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, eulerC]
  calc |traj x u h j - (x j + h * vf x u j)| = |traj x u h j - x j - h * vf x u j| := by ring_nf
    _ ≤ _ := this
    _ = _ := by ring

/-- **The step against one Euler step on a ball**: for `‖x‖ ≤ r`,
`‖step x u - eulerStep x u‖ ≤ eulerC (4 r²) r · h²`. -/
theorem step_sub_eulerStep_le_ball {x : X} {u : Fin 4 → ℝ} {r : ℝ} (hx : ‖x‖ ≤ r) :
    ‖step x u - eulerStep x u‖ ≤ eulerC (4 * r ^ 2) r * h ^ 2 :=
  step_sub_eulerStep_le (qnormSq_le_of_norm_le hx) (WBd_of_norm_le hx)

/-! ## Specific force: backward difference against the instantaneous value -/

/-- The earth-frame specific force of a flat state under held actuators `u`. -/
def sfX (x : X) (u : Fin 4 → ℝ) : Vec3 := specForce (State.ofX x).q u

theorem vf_v_eq_sf (x : X) (u : Fin 4 → ℝ) :
    vf x u 3 = (sfX x u).x ∧ vf x u 4 = (sfX x u).y ∧ vf x u 5 = grav + (sfX x u).z :=
  ⟨rfl, rfl, rfl⟩

/-- **Backward difference against the instantaneous specific force.** Over the period that ends
at the tick, the backward difference of the exact velocity minus gravity, which is what the driver
reports as `accel_ef` (`run_copter.py:160-162`) when the integration is exact, differs from the
model's instantaneous specific force at the tick, component by component, by at most
`cV Q W · h / 2`. -/
theorem backwardDiff_sub_specForce {x : X} {u : Fin 4 → ℝ} {Q W : ℝ} (hQ : qnormSq x ≤ Q)
    (hW : WBd x W) :
    |(step x u 3 - x 3) / h - (sfX (step x u) u).x| ≤ cV Q W * h / 2 ∧
      |(step x u 4 - x 4) / h - (sfX (step x u) u).y| ≤ cV Q W * h / 2 ∧
      |(step x u 5 - x 5) / h - grav - (sfX (step x u) u).z| ≤ cV Q W * h / 2 := by
  have hh := h_pos
  have h1 : (h : ℝ) ∈ Icc 0 h := ⟨hh.le, le_rfl⟩
  have rem : ∀ j : Fin 13, (j = 3 ∨ j = 4 ∨ j = 5) →
      |traj x u h j - x j - h * vf (step x u) u j| ≤ cV Q W * h ^ 2 / 2 := by
    intro j hj
    have := remainder_bwd (f := fun t => traj x u t j) (g := fun t => vf (traj x u t) u j)
      (c := cV Q W) (fun t ht => hasDerivAt_pi.1 (traj_hasDerivAt x u t ht) j)
      (fun t ht => by
        have := vf_traj_sub_v (u := u) hQ hW h h1 t ht
        rw [abs_sub_comm t h, abs_of_nonneg (sub_nonneg.2 ht.2)] at this
        rcases hj with rfl | rfl | rfl
        exacts [this.1, this.2.1, this.2.2])
    simpa [traj_zero, step] using this
  have div : ∀ a b : ℝ, |a - h * b| ≤ cV Q W * h ^ 2 / 2 → |a / h - b| ≤ cV Q W * h / 2 := by
    intro a b hab
    have e : a / h - b = (a - h * b) / h := by field_simp
    rw [e, abs_div, abs_of_pos hh, div_le_iff₀ hh]
    calc _ ≤ cV Q W * h ^ 2 / 2 := hab
      _ = _ := by ring
  obtain ⟨e3, e4, e5⟩ := vf_v_eq_sf (step x u) u
  refine ⟨?_, ?_, ?_⟩
  · apply div; rw [← e3]; simpa [step] using rem 3 (by simp)
  · apply div; rw [← e4]; simpa [step] using rem 4 (by simp)
  · rw [sub_sub]; apply div; rw [← e5]; simpa [step] using rem 5 (by simp)

/-! ## The Euler-angle plant of the port -/

/-- The body-to-NED quaternion of ZYX Euler angles (`Quaternion::from_euler`,
`AP_Math/quaternion.cpp`; `Contracts.CopterPlant.quatOf` of the port). -/
def quatOf (roll pitch yaw : ℝ) : Quat :=
  let cr2 := Real.cos (roll / 2)
  let cp2 := Real.cos (pitch / 2)
  let cy2 := Real.cos (yaw / 2)
  let sr2 := Real.sin (roll / 2)
  let sp2 := Real.sin (pitch / 2)
  let sy2 := Real.sin (yaw / 2)
  ⟨cr2 * cp2 * cy2 + sr2 * sp2 * sy2, sr2 * cp2 * cy2 - cr2 * sp2 * sy2,
   cr2 * sp2 * cy2 + sr2 * cp2 * sy2, cr2 * cp2 * sy2 - sr2 * sp2 * cy2⟩

/-- The thrust direction of the port's Euler-angle plant: the body down axis in NED of the ZYX
rotation `Rz(yaw) Ry(pitch) Rx(roll)` (`Contracts.QuadPlant.thrustDir`). -/
def thrustDir (roll pitch yaw : ℝ) : Vec3 :=
  ⟨Real.cos yaw * Real.sin pitch * Real.cos roll + Real.sin yaw * Real.sin roll,
   Real.sin yaw * Real.sin pitch * Real.cos roll - Real.cos yaw * Real.sin roll,
   Real.cos pitch * Real.cos roll⟩

private theorem half_angle (a : ℝ) : Real.cos a = Real.cos (a / 2) ^ 2 - Real.sin (a / 2) ^ 2 ∧
    Real.sin a = 2 * Real.sin (a / 2) * Real.cos (a / 2) := by
  have h := Real.cos_sq_add_sin_sq (a / 2)
  constructor
  · have := Real.cos_two_mul (a / 2); rw [show 2 * (a / 2) = a by ring] at this; rw [this]
    linarith
  · have := Real.sin_two_mul (a / 2); rw [show 2 * (a / 2) = a by ring] at this; exact this

/-- The quaternion of Euler angles is a unit quaternion. -/
theorem normSq_quatOf (roll pitch yaw : ℝ) : (quatOf roll pitch yaw).normSq = 1 := by
  have hr := Real.cos_sq_add_sin_sq (roll / 2)
  have hp := Real.cos_sq_add_sin_sq (pitch / 2)
  have hy := Real.cos_sq_add_sin_sq (yaw / 2)
  simp only [Quat.normSq, quatOf]
  set a := Real.cos (roll / 2); set b := Real.sin (roll / 2)
  set c := Real.cos (pitch / 2); set d := Real.sin (pitch / 2)
  set e := Real.cos (yaw / 2); set f := Real.sin (yaw / 2)
  linear_combination (c ^ 2 + d ^ 2) * (e ^ 2 + f ^ 2) * hr + (e ^ 2 + f ^ 2) * hp + hy

/-- **The down axis of the quaternion of Euler angles is the Euler plant's thrust direction.** -/
theorem downAxis_quatOf (roll pitch yaw : ℝ) :
    downAxis (quatOf roll pitch yaw) = thrustDir roll pitch yaw := by
  obtain ⟨cr, sr⟩ := half_angle roll
  obtain ⟨cp, sp⟩ := half_angle pitch
  obtain ⟨cy, sy⟩ := half_angle yaw
  have hp := Real.cos_sq_add_sin_sq (pitch / 2)
  have hy := Real.cos_sq_add_sin_sq (yaw / 2)
  simp only [downAxis, quatOf, thrustDir, cr, sr, cp, sp, cy, sy]
  set a := Real.cos (roll / 2); set b := Real.sin (roll / 2)
  set c := Real.cos (pitch / 2); set d := Real.sin (pitch / 2)
  set e := Real.cos (yaw / 2); set f := Real.sin (yaw / 2)
  congr 1
  · linear_combination (4 * a * b * e * f) * hp
  · linear_combination (-2 * a * b * (e ^ 2 - f ^ 2)) * hp
  · linear_combination ((c ^ 2 - d ^ 2) * (a ^ 2 - b ^ 2)) * hy

/-- **The `p` and `v` rows of `eulerStep` are those of the port's `dynR`.** At a state whose
attitude is the quaternion of Euler angles `(roll, pitch, yaw)`, one Euler step of `F` moves the
position by `h v` and the velocity by `h (g e_z - (T/m) thrustDir)`, which is `dynR` with the same
`g`, `h` and thrust law. (The `ω` rows differ only in the lever arm, `0.028` here and `armL / √2`
in `dynR`; the attitude rows are Euler steps of different kinematics, quaternion here and Euler
angles there.) -/
theorem eulerStep_pv_quatOf (s : State) (roll pitch yaw : ℝ) (hq : s.q = quatOf roll pitch yaw)
    (u : Fin 4 → ℝ) :
    let e := eulerStep s.toX u
    let d := thrustDir roll pitch yaw
    e 0 = s.p.x + h * s.v.x ∧ e 1 = s.p.y + h * s.v.y ∧ e 2 = s.p.z + h * s.v.z ∧
      e 3 = s.v.x + h * (-(accel u) * d.x) ∧ e 4 = s.v.y + h * (-(accel u) * d.y) ∧
      e 5 = s.v.z + h * (grav - accel u * d.z) := by
  have hd := downAxis_quatOf roll pitch yaw
  rw [← hq] at hd
  simp only [eulerStep, Pi.add_apply, Pi.smul_apply, smul_eq_mul, vf_toX]
  rw [← hd]
  refine ⟨rfl, rfl, rfl, rfl, rfl, ?_⟩
  simp only [field, specForce, State.toX, downAxis]
  simp only [Matrix.cons_val, neg_mul, ← sub_eq_add_neg]

end

end Contracts.Plant
