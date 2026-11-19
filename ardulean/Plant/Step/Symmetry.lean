module

public import Plant.Flow.Flow

/-!
# Symmetries of the field and of the step

**Translation.** The field does not depend on the position: `F(x + P a, u) = F(x, u)` for the
position shift `P a = (a, 0, …, 0)` (`vf_add_posVec`). Hence the trajectory and the step commute
with the shift (`traj_add_posVec`, `step_add_posVec`).

**Rotation about the vertical axis.** For `c² + s² = 1` (a yaw rotation by the angle `ψ` with
`c = cos ψ/2`, `s = sin ψ/2`), `yawRot c s` rotates position and velocity by
`Rz = [[c² - s², -2cs, 0], [2cs, c² - s², 0], [0, 0, 1]]`, multiplies the attitude on the left by
`(c, 0, 0, s)` (a yaw of the body frame in NED), and keeps the body rates. It is linear, and the
field is equivariant: `F(yawRot x, u) = yawRot (F(x, u))` (`vf_yawRot`). The down axis turns with
`Rz` (inside the proof of `vf_yawRot`), and gravity and the body-frame quantities are unchanged.
Hence the trajectory and the step are equivariant (`traj_yawRot`, `step_yawRot`). The rotation
keeps the norm of the quaternion block (`qnormSq_yawRot`). `posVec`, `yawRot`, `yawRotLin` and
`qnormSq_yawRot` are model-free and live in `Plant.Lib.Blocks`.

Both symmetries are structural: no number of the vehicle enters.
-/

@[expose] public section

namespace Plant

noncomputable section

open Set

/-! ## Translation -/

/-- **The field does not depend on the position.** -/
theorem vf_add_posVec (x : X) (a : Fin 3 → ℝ) (u : Fin 4 → ℝ) : vf (x + posVec a) u = vf x u := by
  have ht : thr (x + posVec a) = thr x := by funext i; fin_cases i <;> simp [thr, posVec]
  funext i
  fin_cases i <;> simp only [Fin.reduceFinMk, Fin.isValue, vf_0, vf_1, vf_2, vf_3, vf_4, vf_5, vf_6, vf_7, vf_8, vf_9, vf_10, vf_11, vf_12, vf_13, vf_14, vf_15, vf_16, ht] <;> simp [posVec]

/-- **The trajectory commutes with translations.** -/
theorem traj_add_posVec (x : X) (a : Fin 3 → ℝ) (u : Fin 4 → ℝ) :
    ∀ t ∈ Icc 0 h, traj (x + posVec a) u t = traj x u t + posVec a := fun _ ht =>
  (traj_unique (γ := fun t => traj x u t + posVec a) (by simp [traj_zero])
    (fun s hs => ((traj_hasDerivAt x u s hs).add_const _).continuousAt.continuousWithinAt)
    (fun s hs => by
      have := (traj_hasDerivAt x u s (Ico_subset_Icc_self hs)).add_const (posVec a)
      rw [← vf_add_posVec _ a u] at this
      exact this.hasDerivWithinAt) ht).symm

/-- **The step commutes with translations.** -/
theorem step_add_posVec (x : X) (a : Fin 3 → ℝ) (u : Fin 4 → ℝ) :
    step (x + posVec a) u = step x u + posVec a :=
  traj_add_posVec x a u h ⟨h_pos.le, le_rfl⟩

/-! ## Rotation about the vertical axis -/

/-- **The field is equivariant under rotations about the vertical axis.** -/
theorem vf_yawRot {c s : ℝ} (hcs : c ^ 2 + s ^ 2 = 1) (x : X) (u : Fin 4 → ℝ) :
    vf (yawRot c s x) u = yawRot c s (vf x u) := by
  have ht : thr (yawRot c s x) = thr x := by funext i; fin_cases i <;> rfl
  funext i
  fin_cases i <;> simp only [Fin.reduceFinMk, Fin.isValue, vf_0, vf_1, vf_2, vf_3, vf_4, vf_5, vf_6, vf_7, vf_8, vf_9, vf_10, vf_11, vf_12, vf_13, vf_14, vf_15, vf_16, ht] <;>
    simp [yawRot, vf_0, vf_1, vf_2, vf_3, vf_4, vf_5, vf_6, vf_7, vf_8, vf_9, vf_10, vf_11, vf_12, vf_13, vf_14, vf_15, vf_16]
  all_goals first
    | ring1
    | (left; linear_combination (x 6 ^ 2 + x 9 ^ 2 - x 7 ^ 2 - x 8 ^ 2) * hcs)

/-- **The trajectory is equivariant under rotations about the vertical axis.** -/
theorem traj_yawRot {c s : ℝ} (hcs : c ^ 2 + s ^ 2 = 1) (x : X) (u : Fin 4 → ℝ) :
    ∀ t ∈ Icc 0 h, traj (yawRot c s x) u t = yawRot c s (traj x u t) := by
  set L := LinearMap.toContinuousLinearMap (yawRotLin c s)
  have hL : ∀ y, L y = yawRot c s y := fun _ => rfl
  have hd : ∀ t ∈ Icc 0 h, HasDerivAt (fun t => yawRot c s (traj x u t))
      (vf (yawRot c s (traj x u t)) u) t := fun t ht => by
    have := L.hasFDerivAt.comp_hasDerivAt t (traj_hasDerivAt x u t ht)
    simp only [Function.comp_def, hL] at this
    rwa [vf_yawRot hcs]
  intro t ht
  exact (traj_unique (γ := fun t => yawRot c s (traj x u t)) (by simp [traj_zero])
    (fun s hs => (hd s hs).continuousAt.continuousWithinAt)
    (fun s hs => (hd s (Ico_subset_Icc_self hs)).hasDerivWithinAt) ht).symm

/-- **The step is equivariant under rotations about the vertical axis.** -/
theorem step_yawRot {c s : ℝ} (hcs : c ^ 2 + s ^ 2 = 1) (x : X) (u : Fin 4 → ℝ) :
    step (yawRot c s x) u = yawRot c s (step x u) :=
  traj_yawRot hcs x u h ⟨h_pos.le, le_rfl⟩

end

end Plant
