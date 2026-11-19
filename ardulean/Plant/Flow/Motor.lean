module

public import Plant.Flow.Flow
public import Plant.Field.Actuators

/-!
# The thrust block of the flow, exactly

The motor rows of the field depend only on the thrust of the same propeller and the held command
(`vf_fI`): `ḟᵢ = lagRate (clip01 uᵢ) fᵢ`. The lag is globally `1/tauUp`-Lipschitz, so the scalar equation has unique
solutions (`lag_unique`), and the thrust block of the trajectory is the exact lag (`traj_fI`):
```
fᵢ(t) = cᵢ + (fᵢ(0) - cᵢ) e^{-t/τ(cᵢ, fᵢ(0))},   cᵢ = clip01 uᵢ,
```
whatever the rest of the state does. At the end of the period this is the simulator's three substeps of the lag
(`step_fI_sim`): the model and the simulator agree exactly on the motor block.

**Invariant.** The thrust range `[0, 1]⁴` (`ThrustRange`) is invariant (`traj_thrustRange`, `step_thrustRange`), each
thrust moves monotonically toward its command (`traj_fI_toward`), so the total thrust acceleration stays in
`[0, amax]` and the clip in the force map is inactive along the flow (`clip_thr_traj`).

**Sensitivity, sharp.** A command change of `δ` on one propeller moves its thrust at time `t` by at most
`δ (1 - e^{-t/tauUp})` (`abs_traj_fI_sub_input_le`), in newtons `fmax δ (1 - e^{-t/tauUp})`
(`abs_force_traj_sub_input_le`); a change of the start thrust by `ε` moves it by at most `ε e^{-t/tauDown}`; both
constants are attained (`Plant.Field.Motor`).
-/

@[expose] public section

namespace Plant

noncomputable section

open Set Metric

/-- Thrust coordinate `i` (`13, …, 16`) of the flat state. -/
def fI (i : Fin 4) : Fin 17 := ⟨i.val + 13, by omega⟩

/-- The thrust block reads the thrust coordinates. -/
theorem thr_apply (x : X) (i : Fin 4) : thr x i = x (fI i) := by fin_cases i <;> rfl

/-- The motor rows of the field. -/
theorem vf_fI (x : X) (u : Fin 4 → ℝ) (i : Fin 4) :
    vf x u (fI i) = lagRate (clip01 (u i)) (x (fI i)) := by fin_cases i <;> rfl

/-- The lag is globally Lipschitz in the thrust. -/
theorem lagRate_lipschitz (c : ℝ) : LipschitzWith (Real.toNNReal (1 / tauUp)) (lagRate c) := by
  refine LipschitzWith.of_dist_le_mul fun a b => ?_
  rw [Real.dist_eq, Real.dist_eq, Real.coe_toNNReal _ (by have := tauUp_pos; positivity)]
  have := abs_lagRate_sub_thrust_le c a b
  rwa [div_eq_inv_mul, ← one_div] at this

theorem continuous_lagSol (c f : ℝ) : Continuous (lagSol c f) :=
  continuous_iff_continuousAt.2 fun t => (hasDerivAt_lagSol c f t).continuousAt

/-- **Uniqueness of the lag.** A curve continuous on `[0, T]` from `f` with right derivative `lagRate c g` is the
exact flow `lagSol c f`. -/
theorem lag_unique {c f T : ℝ} {g : ℝ → ℝ} (h0 : g 0 = f) (hc : ContinuousOn g (Icc 0 T))
    (hd : ∀ t ∈ Ico 0 T, HasDerivWithinAt g (lagRate c (g t)) (Ici t) t) :
    EqOn g (lagSol c f) (Icc 0 T) :=
  ODE_solution_unique_of_mem_Icc_right (v := fun _ y => lagRate c y) (s := fun _ => univ)
    (K := Real.toNNReal (1 / tauUp)) (fun _ _ => (lagRate_lipschitz c).lipschitzOnWith) hc hd
    (fun _ _ => mem_univ _) (continuous_lagSol c f).continuousOn
    (fun t _ => (hasDerivAt_lagSol c f t).hasDerivWithinAt) (fun _ _ => mem_univ _)
    (by rw [h0, lagSol_zero])

section traj
variable (x : X) (u : Fin 4 → ℝ) (i : Fin 4)

/-- **The thrust block of the trajectory is the exact lag**, whatever the rest of the state does. -/
theorem traj_fI : ∀ t ∈ Icc 0 h, traj x u t (fI i) = lagSol (clip01 (u i)) (x (fI i)) t :=
  lag_unique (g := fun t => traj x u t (fI i)) (by simp [traj_zero])
    (fun t ht => (hasDerivAt_pi.1 (traj_hasDerivAt x u t ht) (fI i)).continuousAt.continuousWithinAt)
    (fun t ht => by
      have := hasDerivAt_pi.1 (traj_hasDerivAt x u t (Ico_subset_Icc_self ht)) (fI i)
      rw [vf_fI] at this
      exact this.hasDerivWithinAt)

/-- **The thrust block of the step is the exact lag over the period.** -/
theorem step_fI : step x u (fI i) = lagSol (clip01 (u i)) (x (fI i)) h :=
  traj_fI x u i h ⟨h_pos.le, le_rfl⟩

/-- The thrust block of the trajectory, as `thr`. -/
theorem thr_traj : ∀ t ∈ Icc 0 h, thr (traj x u t) i = lagSol (clip01 (u i)) (thr x i) t := by
  intro t ht; rw [thr_apply, thr_apply, traj_fI x u i t ht]

/-- **The model's thrust after one period is the simulator's**: three substeps of `hPhys` of the simulator's lag
update with the command held (`sim/world/airframes.py:64-66`). -/
theorem step_fI_sim :
    step x u (fI i) = simLag (clip01 (u i)) (simLag (clip01 (u i)) (simLag (clip01 (u i)) (x (fI i)) hPhys)
      hPhys) hPhys := by
  rw [step_fI, simLag_three]

/-- **Each thrust moves monotonically toward its command**: between two times in the period, the later value lies
between the earlier value and the command, and the gap to the command shrinks. -/
theorem traj_fI_toward {s t : ℝ} (hs : s ∈ Icc 0 h) (ht : t ∈ Icc 0 h) (hst : s ≤ t) :
    (min (traj x u s (fI i)) (clip01 (u i)) ≤ traj x u t (fI i) ∧
      traj x u t (fI i) ≤ max (traj x u s (fI i)) (clip01 (u i))) ∧
    |clip01 (u i) - traj x u t (fI i)| ≤ |clip01 (u i) - traj x u s (fI i)| := by
  rw [traj_fI x u i s hs, traj_fI x u i t ht]
  exact ⟨lagSol_mono_toward _ _ hst, abs_sub_lagSol_le _ _ hst⟩

end traj

/-! ## The thrust range -/

/-- The thrusts are in the physical range `[0, 1]⁴`. -/
def ThrustRange (x : X) : Prop := ∀ i, thr x i ∈ Icc (0 : ℝ) 1

/-- **The thrust range is invariant along the trajectory.** -/
theorem traj_thrustRange {x : X} (hx : ThrustRange x) (u : Fin 4 → ℝ) :
    ∀ t ∈ Icc 0 h, ThrustRange (traj x u t) := fun t ht i => by
  rw [thr_traj x u i t ht]
  exact lagSol_mem ⟨clip01_nonneg _, clip01_le_one _⟩ (hx i) ht.1

/-- **The thrust range is invariant under the step.** -/
theorem step_thrustRange {x : X} (hx : ThrustRange x) (u : Fin 4 → ℝ) : ThrustRange (step x u) :=
  traj_thrustRange hx u h ⟨h_pos.le, le_rfl⟩

/-- On the thrust range the clip in the force and torque maps is inactive along the trajectory. -/
theorem clip_thr_traj {x : X} (hx : ThrustRange x) (u : Fin 4 → ℝ) (i : Fin 4) :
    ∀ t ∈ Icc 0 h, clip01 (thr (traj x u t) i) = lagSol (clip01 (u i)) (thr x i) t := by
  intro t ht
  rw [clip01_of_mem (traj_thrustRange hx u t ht i).1 (traj_thrustRange hx u t ht i).2, thr_traj x u i t ht]

/-- **The total thrust acceleration stays in `[0, amax]`** along the trajectory. -/
theorem accel_traj_mem (x : X) (u : Fin 4 → ℝ) :
    ∀ t ∈ Icc 0 h, accel (thr (traj x u t)) ∈ Icc 0 amax := fun _ _ =>
  ⟨accel_nonneg _, accel_le _⟩

/-! ## Sensitivity of the thrust block -/

/-- **A command error becomes a thrust error, sharply**: from the same state, the thrust of propeller `i` at time
`t` under commands `u` and `w` differs by at most `(1 - e^{-t/tauUp}) |uᵢ - wᵢ|`. -/
theorem abs_traj_fI_sub_input_le (x : X) (u w : Fin 4 → ℝ) (i : Fin 4) :
    ∀ t ∈ Icc 0 h, |traj x u t (fI i) - traj x w t (fI i)| ≤ lagM0 tauUp t * |u i - w i| := by
  intro t ht
  rw [traj_fI x u i t ht, traj_fI x w i t ht]
  exact (abs_lagSol_sub_cmd_le _ _ _ ht.1).trans
    (mul_le_mul_of_nonneg_left (abs_clip01_sub_le _ _) (lagM0_nonneg tauUp_pos ht.1))

/-- The same for the step: `|f_u(h) - f_w(h)| ≤ (1 - e^{-h/tauUp}) |uᵢ - wᵢ|`. -/
theorem abs_step_fI_sub_input_le (x : X) (u w : Fin 4 → ℝ) (i : Fin 4) :
    |step x u (fI i) - step x w (fI i)| ≤ lagM0 tauUp h * |u i - w i| :=
  abs_traj_fI_sub_input_le x u w i h ⟨h_pos.le, le_rfl⟩

/-- The thrust block of the trajectory, in the sup norm: at most `(1 - e^{-t/tauUp}) ‖u - w‖`. -/
theorem norm_mot_traj_sub_input_le (x : X) (u w : Fin 4 → ℝ) :
    ∀ t ∈ Icc 0 h, ‖mot (traj x u t) - mot (traj x w t)‖ ≤ lagM0 tauUp t * ‖u - w‖ := by
  intro t ht
  refine norm_block_le (mul_nonneg (lagM0_nonneg tauUp_pos ht.1) (norm_nonneg _)) fun i => ?_
  refine (abs_traj_fI_sub_input_le x u w i t ht).trans
    (mul_le_mul_of_nonneg_left ?_ (lagM0_nonneg tauUp_pos ht.1))
  rw [← Pi.sub_apply, ← Real.norm_eq_abs]; exact norm_le_pi_norm (u - w) i

/-- **In newtons**: the force of propeller `i` under `u` and `w` differs by at most
`fmax |uᵢ - wᵢ| (1 - e^{-t/tauUp})` (the thrusts stay in `[0, 1]`, so the clip changes nothing). -/
theorem abs_force_traj_sub_input_le (x : X) (u w : Fin 4 → ℝ) (i : Fin 4) :
    ∀ t ∈ Icc 0 h, |force (thr (traj x u t)) i - force (thr (traj x w t)) i| ≤
      fmax * |u i - w i| * lagM0 tauUp t := by
  intro t ht
  have hf := fmax_pos
  rw [force, force, ← mul_sub, abs_mul, abs_of_pos hf, mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ hf.le
  rw [mul_comm]
  refine (abs_clip01_sub_le _ _).trans ?_
  rw [thr_apply, thr_apply]
  exact abs_traj_fI_sub_input_le x u w i t ht

/-- **Joint sensitivity of the thrust block**: in the command and in the start thrust. -/
theorem abs_step_fI_sub_le (x y : X) (u w : Fin 4 → ℝ) (i : Fin 4) :
    |step x u (fI i) - step y w (fI i)| ≤
      lagM0 tauUp h * |u i - w i| + Real.exp (-h / tauDown) * |x (fI i) - y (fI i)| := by
  rw [step_fI, step_fI]
  refine (abs_lagSol_sub_le _ _ _ _ h_pos.le).trans (add_le_add ?_ le_rfl)
  exact mul_le_mul_of_nonneg_left (abs_clip01_sub_le _ _) (lagM0_nonneg tauUp_pos h_pos.le)

end

end Plant
