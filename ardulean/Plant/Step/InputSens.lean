module

public import Plant.Step.Sharp

/-!
# Sharp sensitivity of the step to the held command, block by block

From the same state `x` (unit quaternion, rates at most `W`, thrusts in `[0, 1]⁴`), two held commands `u` and `w`
with `δ = ‖u - w‖` give trajectories that differ, for `t ∈ [0, h]`, by at most (`traj_input_sens`)
```
thrusts       |Δfᵢ(t)| ≤ δ μ(t),                 μ = 1 - e^{-t/tauUp}            (exact, sharp)
rates         |Δω_k(t)| ≤ 2 alphaMax δ M1(t) e^{Kω t},        Kω = 2 gyro Ω
quaternion    |Δq_i(t)| ≤ 3 alphaMax δ M2(t) e^{Kq t},        Kq = (3/2 + 2 gyro) Ω
velocity      |Δv_j(t)| ≤ amax δ (M1(t) + 24 alphaMax M3(t) e^{Kq t})
position      |Δp_j(t)| ≤ amax δ (M2(t) + 24 alphaMax t M3(t) e^{Kq t})
```
where `M1`, `M2`, `M3` are the first three integrals of `μ` (`lagM1` …, `Plant.Lib.Gronwall`; `M1(t) ≤ t²/(2 tauUp)`,
`M2(t) ≤ t³/(6 tauUp)`, `M3(t) ≤ t⁴/(24 tauUp)`) and `Ω ≥ wTA W alphaMax` bounds the rates of both trajectories.
The leading terms are exact for a command step on one axis: the thrust error is the lag's step response, the torque
error integrates it once (`2 alphaMax` per unit of thrust error), the attitude error twice, and the velocity error
integrates the thrust error once (`amax` per unit). The factors `e^{K t}` (at most `e^{Kq h}`, `≈ 1 + 0.006 Ω` for
the X500) and the `M3` terms are the coupling through the gyroscopic term and the tilt of the thrust.

The proof is block by block: the motor block is exact (`Plant.Flow.Motor`); the rate block depends on the rest of the
state only through the rates and the thrusts, so Grönwall with the thrust error as a forcing term
(`norm_le_of_supersol`) bounds it; the quaternion block is forced by the rate error; the velocity and position rows
integrate. No Lipschitz constant of the whole state (which contains the position) enters, unlike
`norm_step_sub_input_le` (`Plant.Flow.Sensitivity`).
-/

@[expose] public section

namespace Plant

noncomputable section

open Set

/-- The rate rows of the field do not depend on the command. -/
theorem vf_rates_input (y : X) (u w : Fin 4 → ℝ) : rates (vf y u) = rates (vf y w) := by
  funext k; fin_cases k
  · show vf y u 10 = vf y w 10; rw [vf_10, vf_10]
  · show vf y u 11 = vf y w 11; rw [vf_11, vf_11]
  · show vf y u 12 = vf y w 12; rw [vf_12, vf_12]

/-- The quaternion rows of the field do not depend on the command. -/
theorem vf_quat_input (y : X) (u w : Fin 4 → ℝ) : quat (vf y u) = quat (vf y w) := by
  funext k; fin_cases k
  · show vf y u 6 = vf y w 6; rw [vf_6, vf_6]
  · show vf y u 7 = vf y w 7; rw [vf_7, vf_7]
  · show vf y u 8 = vf y w 8; rw [vf_8, vf_8]
  · show vf y u 9 = vf y w 9; rw [vf_9, vf_9]

/-- The exponential factor and its derivative. -/
private theorem hasDerivAt_expK (K t : ℝ) :
    HasDerivAt (fun s => Real.exp (K * s)) (Real.exp (K * t) * K) t := by
  refine ((hasDerivAt_id t).const_mul K).exp.congr_deriv ?_; simp

private theorem one_le_expK {K t : ℝ} (hK : 0 ≤ K) (ht : 0 ≤ t) : 1 ≤ Real.exp (K * t) :=
  Real.one_le_exp (mul_nonneg hK ht)

section sens
variable {x : X} {u w : Fin 4 → ℝ} {W Ω : ℝ}

/-- The common hypotheses: both trajectories keep a unit quaternion and rates at most `Ω`. -/
private theorem both_unit_rates (hq : qnormSq x = 1) (hW : WBd x W) (hΩ : wTA W alphaMax ≤ Ω) :
    ∀ t ∈ Icc 0 h, (qnormSq (traj x u t) = 1 ∧ WBd (traj x u t) Ω) ∧
      (qnormSq (traj x w t) = 1 ∧ WBd (traj x w t) Ω) := fun t ht =>
  ⟨traj_unit_rates hq hW (torqueBdT_alphaMax x u) hΩ t ht,
    traj_unit_rates hq hW (torqueBdT_alphaMax x w) hΩ t ht⟩

/-- **Thrust block**: `|Δfᵢ(t)| ≤ (1 - e^{-t/tauUp}) ‖u - w‖`. -/
theorem traj_sens_thr : ∀ t ∈ Icc 0 h, FBd (traj x u t - traj x w t) (lagM0 tauUp t * ‖u - w‖) := by
  intro t ht
  have k : ∀ i : Fin 4, |(traj x u t - traj x w t) (fI i)| ≤ lagM0 tauUp t * ‖u - w‖ := fun i => by
    rw [Pi.sub_apply]
    refine (abs_traj_fI_sub_input_le x u w i t ht).trans (mul_le_mul_of_nonneg_left ?_
      (lagM0_nonneg tauUp_pos ht.1))
    rw [← Pi.sub_apply, ← Real.norm_eq_abs]; exact norm_le_pi_norm (u - w) i
  exact ⟨k 0, k 1, k 2, k 3⟩

/-- The bound of the rate error. -/
def sensW (Ω δ t : ℝ) : ℝ := 2 * alphaMax * δ * lagM1 tauUp t * Real.exp (2 * gyro * Ω * t)

/-- The bound of the quaternion error. -/
def sensQ (Ω δ t : ℝ) : ℝ := 3 * alphaMax * δ * lagM2 tauUp t * Real.exp ((3 / 2 + 2 * gyro) * Ω * t)

/-- The bound of the velocity error. -/
def sensV (Ω δ t : ℝ) : ℝ :=
  amax * δ * (lagM1 tauUp t + 24 * alphaMax * lagM3 tauUp t * Real.exp ((3 / 2 + 2 * gyro) * Ω * t))

/-- The bound of the position error. -/
def sensP (Ω δ t : ℝ) : ℝ :=
  amax * δ * (lagM2 tauUp t + 24 * alphaMax * (t * lagM3 tauUp t) * Real.exp ((3 / 2 + 2 * gyro) * Ω * t))

/-- **Rate block**: `‖Δω(t)‖ ≤ 2 alphaMax δ lagM1(t) e^{2 gyro Ω t}`. -/
theorem traj_sens_rates (hq : qnormSq x = 1) (hW : WBd x W) (hΩ : wTA W alphaMax ≤ Ω) :
    ∀ t ∈ Icc 0 h, ‖rates (traj x u t) - rates (traj x w t)‖ ≤ sensW Ω ‖u - w‖ t := by
  have hb := both_unit_rates (u := u) (w := w) hq hW hΩ
  have hΩ0 : 0 ≤ Ω := ((abs_nonneg _).trans hW.1).trans ((le_wTA alphaMax_pos.le).trans hΩ)
  set δ := ‖u - w‖
  have hδ : 0 ≤ δ := norm_nonneg _
  have hal := alphaMax_pos
  have hg := gyro_nonneg
  set K := 2 * gyro * Ω
  have hK : 0 ≤ K := by positivity
  have hd : ∀ (v : Fin 4 → ℝ), ∀ s ∈ Icc 0 h,
      HasDerivAt (fun s => rates (traj x v s)) (rates (vf (traj x v s) v)) s :=
    fun v s hs => hasDerivAt_pi.2 fun k => hasDerivAt_pi.1 (traj_hasDerivAt x v s hs) _
  refine norm_le_of_supersol (f := fun s => rates (traj x u s) - rates (traj x w s))
    (f' := fun s => rates (vf (traj x u s) u) - rates (vf (traj x w s) w))
    (B' := fun s => 2 * alphaMax * δ * (lagM0 tauUp s * Real.exp (K * s) +
      lagM1 tauUp s * (Real.exp (K * s) * K)))
    (g := fun s => 2 * alphaMax * (lagM0 tauUp s * δ)) (K := K) (T := h)
    (fun s hs => ((hd u s hs).sub (hd w s hs)).continuousAt.continuousWithinAt)
    (fun s hs => ((hd u s (Ico_subset_Icc_self hs)).sub (hd w s (Ico_subset_Icc_self hs))).hasDerivWithinAt)
    (fun s _ => by
      refine (((hasDerivAt_lagM1 tauUp_pos.ne' s).const_mul (2 * alphaMax * δ)).mul
        (hasDerivAt_expK K s)).congr_deriv ?_
      ring)
    (by simp [traj_zero, sensW, lagM1_zero]) ?_ ?_
  · intro s hs
    have hs' := Ico_subset_Icc_self hs
    obtain ⟨⟨-, wu⟩, ⟨-, ww⟩⟩ := hb s hs'
    set D := ‖rates (traj x u s) - rates (traj x w s)‖
    have hD : WBd (traj x u s - traj x w s) D := WBd_of_rates (by rw [rates_sub])
    have hw := vf_sub_w (u := u) wu ww hD (traj_sens_thr s hs')
    rw [vf_rates_input (traj x w s) w u]
    refine norm_block_le (by have := lagM0_nonneg tauUp_pos hs'.1; positivity) fun k => ?_
    have e : ∀ k : Fin 3, gyro * (2 * Ω * D) + 2 * alphaMax * (lagM0 tauUp s * δ) =
        K * D + 2 * alphaMax * (lagM0 tauUp s * δ) := fun _ => by simp only [K]; ring
    fin_cases k
    · exact (e 0) ▸ hw.1
    · exact (e 0) ▸ hw.2.1
    · exact (e 0) ▸ hw.2.2
  · intro s hs
    have h0 := lagM0_nonneg (τ := tauUp) tauUp_pos hs.1
    have h1 := lagM1_nonneg (τ := tauUp) tauUp_pos hs.1
    have he := one_le_expK hK hs.1
    unfold sensW
    have : 2 * alphaMax * (lagM0 tauUp s * δ) ≤ 2 * alphaMax * δ * (lagM0 tauUp s * Real.exp (K * s)) := by
      have := mul_le_mul_of_nonneg_left he (mul_nonneg h0 (by positivity : (0 : ℝ) ≤ 2 * alphaMax * δ))
      nlinarith
    nlinarith [mul_nonneg (mul_nonneg (by positivity : (0 : ℝ) ≤ 2 * alphaMax * δ) h1) (Real.exp_pos (K * s)).le]

/-- **Quaternion block**: `‖Δq(t)‖ ≤ 3 alphaMax δ lagM2(t) e^{(3/2 + 2 gyro) Ω t}`. -/
theorem traj_sens_quat (hq : qnormSq x = 1) (hW : WBd x W) (hΩ : wTA W alphaMax ≤ Ω) :
    ∀ t ∈ Icc 0 h, ‖quat (traj x u t) - quat (traj x w t)‖ ≤ sensQ Ω ‖u - w‖ t := by
  have hb := both_unit_rates (u := u) (w := w) hq hW hΩ
  have hr := traj_sens_rates (u := u) (w := w) hq hW hΩ
  have hΩ0 : 0 ≤ Ω := ((abs_nonneg _).trans hW.1).trans ((le_wTA alphaMax_pos.le).trans hΩ)
  set δ := ‖u - w‖
  have hδ : 0 ≤ δ := norm_nonneg _
  have hal := alphaMax_pos
  have hg := gyro_nonneg
  set Kw := 2 * gyro * Ω
  set K := (3 / 2 + 2 * gyro) * Ω
  have hK : 0 ≤ K := by positivity
  have hd : ∀ (v : Fin 4 → ℝ), ∀ s ∈ Icc 0 h,
      HasDerivAt (fun s => quat (traj x v s)) (quat (vf (traj x v s) v)) s :=
    fun v s hs => hasDerivAt_pi.2 fun k => hasDerivAt_pi.1 (traj_hasDerivAt x v s hs) _
  refine norm_le_of_supersol (f := fun s => quat (traj x u s) - quat (traj x w s))
    (f' := fun s => quat (vf (traj x u s) u) - quat (vf (traj x w s) w))
    (B' := fun s => 3 * alphaMax * δ * (lagM1 tauUp s * Real.exp (K * s) +
      lagM2 tauUp s * (Real.exp (K * s) * K)))
    (g := fun s => (3 / 2) * sensW Ω δ s) (K := (3 / 2) * Ω) (T := h)
    (fun s hs => ((hd u s hs).sub (hd w s hs)).continuousAt.continuousWithinAt)
    (fun s hs => ((hd u s (Ico_subset_Icc_self hs)).sub (hd w s (Ico_subset_Icc_self hs))).hasDerivWithinAt)
    (fun s _ => by
      refine (((hasDerivAt_lagM2 s).const_mul (3 * alphaMax * δ)).mul
        (hasDerivAt_expK K s)).congr_deriv ?_
      ring)
    (by simp [traj_zero, sensQ, lagM2_zero]) ?_ ?_
  · intro s hs
    have hs' := Ico_subset_Icc_self hs
    obtain ⟨⟨qu, -⟩, ⟨-, ww⟩⟩ := hb s hs'
    set D := ‖quat (traj x u s) - quat (traj x w s)‖
    have hDq : QBd (traj x u s - traj x w s) D := QBd_of_quat (by rw [quat_sub])
    have hDw : WBd (traj x u s - traj x w s) (sensW Ω δ s) := WBd_of_rates (by rw [rates_sub]; exact hr s hs')
    have hqv := vf_sub_q (u := u) (QBd_one_of_unit qu) ww hDq hDw
    rw [vf_quat_input (traj x w s) w u]
    refine norm_block_le (by
      have := lagM1_nonneg (τ := tauUp) tauUp_pos hs'.1
      unfold sensW; positivity) fun k => ?_
    have e : (3 / 2) * (1 * sensW Ω δ s + Ω * D) = 3 / 2 * Ω * D + 3 / 2 * sensW Ω δ s := by ring
    fin_cases k
    · exact e ▸ hqv.1
    · exact e ▸ hqv.2.1
    · exact e ▸ hqv.2.2.1
    · exact e ▸ hqv.2.2.2
  · intro s hs
    have h1 := lagM1_nonneg (τ := tauUp) tauUp_pos hs.1
    have h2 := lagM2_nonneg (τ := tauUp) tauUp_pos hs.1
    have hKw : Kw * s ≤ K * s := mul_le_mul_of_nonneg_right (by simp only [Kw, K]; nlinarith) hs.1
    have hee : Real.exp (Kw * s) ≤ Real.exp (K * s) := Real.exp_le_exp.2 hKw
    have hA : 0 ≤ 3 * alphaMax * δ := by positivity
    unfold sensQ sensW
    have t1 : (3 / 2) * (2 * alphaMax * δ * lagM1 tauUp s * Real.exp (2 * gyro * Ω * s)) ≤
        3 * alphaMax * δ * (lagM1 tauUp s * Real.exp (K * s)) := by
      have := mul_le_mul_of_nonneg_left hee (mul_nonneg hA h1)
      simp only [Kw] at this; nlinarith
    have t2 : (3 / 2) * Ω * (3 * alphaMax * δ * lagM2 tauUp s * Real.exp (K * s)) ≤
        3 * alphaMax * δ * (lagM2 tauUp s * (Real.exp (K * s) * K)) := by
      have hk : (3 / 2) * Ω ≤ K := by simp only [K]; nlinarith
      have := mul_le_mul_of_nonneg_left hk (mul_nonneg (mul_nonneg hA h2) (Real.exp_pos (K * s)).le)
      nlinarith
    linarith

/-- **Velocity rows**: `|Δv_j(t)| ≤ amax δ (lagM1(t) + 24 alphaMax lagM3(t) e^{Kq t})`. -/
theorem traj_sens_vel (hq : qnormSq x = 1) (hW : WBd x W) (hΩ : wTA W alphaMax ≤ Ω) (j : Fin 3) :
    ∀ t ∈ Icc 0 h, |traj x u t (vI j) - traj x w t (vI j)| ≤ sensV Ω ‖u - w‖ t := by
  have hb := both_unit_rates (u := u) (w := w) hq hW hΩ
  have hqs := traj_sens_quat (u := u) (w := w) hq hW hΩ
  have hΩ0 : 0 ≤ Ω := ((abs_nonneg _).trans hW.1).trans ((le_wTA alphaMax_pos.le).trans hΩ)
  set δ := ‖u - w‖
  have hδ : 0 ≤ δ := norm_nonneg _
  have hal := alphaMax_pos
  have hAm := amax_pos
  have hg := gyro_nonneg
  set K := (3 / 2 + 2 * gyro) * Ω
  have hK : 0 ≤ K := by positivity
  have hd : ∀ (v : Fin 4 → ℝ), ∀ s ∈ Icc 0 h,
      HasDerivAt (fun s => traj x v s (vI j)) (grav * ez j - accel (thr (traj x v s)) * dn (traj x v s) j) s :=
    fun v s hs => by
      have := hasDerivAt_pi.1 (traj_hasDerivAt x v s hs) (vI j)
      rwa [vf_vI] at this
  have key := abs_sub_poly_le (f := fun s => traj x u s (vI j) - traj x w s (vI j))
    (g := fun s => (grav * ez j - accel (thr (traj x u s)) * dn (traj x u s) j) -
      (grav * ez j - accel (thr (traj x w s)) * dn (traj x w s) j))
    (P := fun _ => 0) (p := fun _ => 0) (B := sensV Ω δ)
    (B' := fun s => amax * δ * (lagM0 tauUp s + 24 * alphaMax * (lagM2 tauUp s * Real.exp (K * s) +
      lagM3 tauUp s * (Real.exp (K * s) * K))))
    (fun s hs => (hd u s hs).sub (hd w s hs)) (fun _ => hasDerivAt_const _ _)
    (fun s => by
      refine (((hasDerivAt_lagM1 tauUp_pos.ne' s).add (((hasDerivAt_lagM3 s).const_mul (24 * alphaMax)).mul
        (hasDerivAt_expK K s))).const_mul (amax * δ)).congr_deriv ?_
      ring)
    (by simp [sensV, lagM1_zero, lagM3_zero])
    (fun s hs => by
      obtain ⟨⟨qu, -⟩, ⟨qw, -⟩⟩ := hb s hs
      have hDq : QBd (traj x u s - traj x w s) (sensQ Ω δ s) := QBd_of_quat (by rw [quat_sub]; exact hqs s hs)
      have hF := thr_sub_le (traj_sens_thr (x := x) (u := u) (w := w) s hs)
      have ha := abs_accel_sub_le_of hF
      have haw := accel_le (thr (traj x w s))
      have haw0 := accel_nonneg (thr (traj x w s))
      obtain ⟨d0, d1, d2⟩ := dn_sub_le (QBd_one_of_unit qu) (QBd_one_of_unit qw) hDq
      obtain ⟨e0, e1, e2⟩ := abs_down_le (traj x u s)
      rw [qu] at e0 e1 e2
      have hdj : |dn (traj x u s) j - dn (traj x w s) j| ≤ 8 * 1 * sensQ Ω δ s := by
        fin_cases j
        exacts [d0, d1, d2]
      have hdu : |dn (traj x u s) j| ≤ 1 := by
        fin_cases j
        exacts [e0, e1, e2]
      have e : (grav * ez j - accel (thr (traj x u s)) * dn (traj x u s) j) -
          (grav * ez j - accel (thr (traj x w s)) * dn (traj x w s) j) - 0 =
          -((accel (thr (traj x u s)) - accel (thr (traj x w s))) * dn (traj x u s) j +
            accel (thr (traj x w s)) * (dn (traj x u s) j - dn (traj x w s) j)) := by ring
      rw [e, abs_neg]
      have h0 := lagM0_nonneg (τ := tauUp) tauUp_pos hs.1
      have h2 := lagM2_nonneg (τ := tauUp) tauUp_pos hs.1
      have h3 := lagM3_nonneg (τ := tauUp) tauUp_pos hs.1
      have hex := Real.exp_pos (K * s)
      calc _ ≤ |(accel (thr (traj x u s)) - accel (thr (traj x w s))) * dn (traj x u s) j| +
            |accel (thr (traj x w s)) * (dn (traj x u s) j - dn (traj x w s) j)| := abs_add_le _ _
        _ ≤ amax * (lagM0 tauUp s * δ) * 1 + amax * (8 * 1 * sensQ Ω δ s) := by
            rw [abs_mul, abs_mul, abs_of_nonneg haw0]
            exact add_le_add (mul_le_mul ha hdu (abs_nonneg _) (by positivity))
              (mul_le_mul haw hdj (abs_nonneg _) hAm.le)
        _ ≤ _ := by
            unfold sensQ
            have : 0 ≤ amax * δ * 24 * alphaMax * (lagM3 tauUp s * (Real.exp (K * s) * K)) := by positivity
            nlinarith)
  intro t ht
  simpa [traj_zero] using key t ht

/-- **Position rows**: `|Δp_j(t)| ≤ amax δ (lagM2(t) + 24 alphaMax t lagM3(t) e^{Kq t})`. -/
theorem traj_sens_pos (hq : qnormSq x = 1) (hW : WBd x W) (hΩ : wTA W alphaMax ≤ Ω) (j : Fin 3) :
    ∀ t ∈ Icc 0 h, |traj x u t (pI j) - traj x w t (pI j)| ≤ sensP Ω ‖u - w‖ t := by
  have hv := traj_sens_vel (u := u) (w := w) hq hW hΩ j
  have hΩ0 : 0 ≤ Ω := ((abs_nonneg _).trans hW.1).trans ((le_wTA alphaMax_pos.le).trans hΩ)
  set δ := ‖u - w‖
  have hδ : 0 ≤ δ := norm_nonneg _
  have hal := alphaMax_pos
  have hAm := amax_pos
  have hg := gyro_nonneg
  set K := (3 / 2 + 2 * gyro) * Ω
  have hK : 0 ≤ K := by positivity
  have hd : ∀ (v : Fin 4 → ℝ), ∀ s ∈ Icc 0 h,
      HasDerivAt (fun s => traj x v s (pI j)) (traj x v s (vI j)) s := fun v s hs => by
    have := hasDerivAt_pi.1 (traj_hasDerivAt x v s hs) (pI j)
    rwa [vf_pI] at this
  have key := abs_sub_poly_le (f := fun s => traj x u s (pI j) - traj x w s (pI j))
    (g := fun s => traj x u s (vI j) - traj x w s (vI j))
    (P := fun _ => 0) (p := fun _ => 0) (B := sensP Ω δ)
    (B' := fun s => amax * δ * (lagM1 tauUp s + 24 * alphaMax *
      ((lagM3 tauUp s + s * lagM2 tauUp s) * Real.exp (K * s) + s * lagM3 tauUp s * (Real.exp (K * s) * K))))
    (fun s hs => (hd u s hs).sub (hd w s hs)) (fun _ => hasDerivAt_const _ _)
    (fun s => by
      refine (((hasDerivAt_lagM2 s).add ((((hasDerivAt_id s).mul (hasDerivAt_lagM3 s)).const_mul
        (24 * alphaMax)).mul (hasDerivAt_expK K s))).const_mul (amax * δ)).congr_deriv ?_
      simp only [Pi.mul_apply, id]; ring)
    (by simp [sensP, lagM2_zero, lagM3_zero])
    (fun s hs => by
      have := hv s hs
      rw [sub_zero]
      refine this.trans ?_
      unfold sensV
      have h2 := lagM2_nonneg (τ := tauUp) tauUp_pos hs.1
      have h3 := lagM3_nonneg (τ := tauUp) tauUp_pos hs.1
      have hex := Real.exp_pos (K * s)
      have : 0 ≤ amax * δ * 24 * alphaMax * (s * lagM2 tauUp s * Real.exp (K * s) +
          s * lagM3 tauUp s * (Real.exp (K * s) * K)) := by
        have := hs.1; positivity
      nlinarith)
  intro t ht
  simpa [traj_zero] using key t ht

/-- **The sharp input sensitivity of the trajectory, all blocks.** From the same state `x` (unit quaternion, rates at
most `W`, thrusts in `[0, 1]⁴`) under two held commands, with `Ω ≥ wTA W alphaMax`, for `t ∈ [0, h]`: the thrust,
rate, quaternion, velocity and position errors are at most `δ μ`, `sensW`, `sensQ`, `sensV`, `sensP` (sup norms per
block, `δ = ‖u - w‖`). -/
theorem traj_input_sens (hq : qnormSq x = 1) (hW : WBd x W) (hΩ : wTA W alphaMax ≤ Ω) :
    ∀ t ∈ Icc 0 h,
      FBd (traj x u t - traj x w t) (lagM0 tauUp t * ‖u - w‖) ∧
      ‖rates (traj x u t) - rates (traj x w t)‖ ≤ sensW Ω ‖u - w‖ t ∧
      ‖quat (traj x u t) - quat (traj x w t)‖ ≤ sensQ Ω ‖u - w‖ t ∧
      (∀ j : Fin 3, |traj x u t (vI j) - traj x w t (vI j)| ≤ sensV Ω ‖u - w‖ t) ∧
      (∀ j : Fin 3, |traj x u t (pI j) - traj x w t (pI j)| ≤ sensP Ω ‖u - w‖ t) := fun t ht =>
  ⟨traj_sens_thr t ht, traj_sens_rates hq hW hΩ t ht, traj_sens_quat hq hW hΩ t ht,
    fun j => traj_sens_vel hq hW hΩ j t ht, fun j => traj_sens_pos hq hW hΩ j t ht⟩

/-- **The sharp input sensitivity of the step**: the case `t = h`. -/
theorem step_input_sens (hq : qnormSq x = 1) (hW : WBd x W) (hΩ : wTA W alphaMax ≤ Ω) :
    FBd (step x u - step x w) (lagM0 tauUp h * ‖u - w‖) ∧
      ‖rates (step x u) - rates (step x w)‖ ≤ sensW Ω ‖u - w‖ h ∧
      ‖quat (step x u) - quat (step x w)‖ ≤ sensQ Ω ‖u - w‖ h ∧
      (∀ j : Fin 3, |step x u (vI j) - step x w (vI j)| ≤ sensV Ω ‖u - w‖ h) ∧
      (∀ j : Fin 3, |step x u (pI j) - step x w (pI j)| ≤ sensP Ω ‖u - w‖ h) :=
  traj_input_sens hq hW hΩ h ⟨h_pos.le, le_rfl⟩

end sens

end

end Plant
