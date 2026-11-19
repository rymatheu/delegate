module

public import Plant.Step.Sharp
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# The position and velocity rows as integrals

Over the period the velocity is the integral of gravity and the specific force, and the position the integral of
the velocity, exactly (`traj_vI_integral`, `traj_pI_integral`):
```
v_j(t) = v_j + t g e_z,j - ∫₀ᵗ a(s) d_j(q(s)) ds,        p_j(t) = p_j + ∫₀ᵗ v_j(s) ds,
```
with `a(s) = accel (thr (traj x u s))` the thrust acceleration of the lagged thrusts; on the thrust range it is the
closed form `accT x u s` (`traj_vI_integral_accT`). These are the identities a tube argument starts from: the only
unknown along the period is the attitude `q(s)`, and the thrust term is known in closed form from the state and the
held command.
-/

@[expose] public section

namespace Plant

noncomputable section

open Set MeasureTheory intervalIntegral

private theorem uIcc_sub {t : ℝ} (ht : t ∈ Icc 0 h) : uIcc 0 t ⊆ Icc 0 h := by
  rw [uIcc_of_le ht.1]; exact Icc_subset_Icc le_rfl ht.2

/-- The field along the trajectory is continuous on the period. -/
theorem continuousOn_vf_traj (x : X) (u : Fin 4 → ℝ) (j : Fin 17) :
    ContinuousOn (fun s => vf (traj x u s) u j) (Icc 0 h) :=
  ((continuous_apply j).comp (vf_continuous u)).comp_continuousOn (traj_continuousOn x u)

/-- **The velocity rows as an integral.** -/
theorem traj_vI_integral (x : X) (u : Fin 4 → ℝ) (j : Fin 3) {t : ℝ} (ht : t ∈ Icc 0 h) :
    traj x u t (vI j) = x (vI j) + t * (grav * ez j) -
      ∫ s in (0 : ℝ)..t, accel (thr (traj x u s)) * dn (traj x u s) j := by
  have hc := continuousOn_vf_traj x u (vI j)
  have hint : IntervalIntegrable (fun s => vf (traj x u s) u (vI j)) volume 0 t :=
    (hc.mono (uIcc_sub ht)).intervalIntegrable
  have hftc := integral_eq_sub_of_hasDerivAt (f := fun s => traj x u s (vI j))
    (fun s hs => hasDerivAt_pi.1 (traj_hasDerivAt x u s (uIcc_sub ht hs)) (vI j)) hint
  simp only [vf_vI, traj_zero] at hftc
  have hint2 : IntervalIntegrable (fun s => accel (thr (traj x u s)) * dn (traj x u s) j) volume 0 t := by
    have : IntervalIntegrable (fun s => grav * ez j - (grav * ez j - accel (thr (traj x u s)) *
        dn (traj x u s) j)) volume 0 t := intervalIntegrable_const.sub (by simpa [vf_vI] using hint)
    simpa using this
  rw [intervalIntegral.integral_sub intervalIntegrable_const hint2, intervalIntegral.integral_const,
    smul_eq_mul, sub_zero] at hftc
  linarith

/-- **The velocity rows as an integral, with the thrust in closed form** (thrusts in `[0, 1]⁴`). -/
theorem traj_vI_integral_accT {x : X} (hf : ThrustRange x) (u : Fin 4 → ℝ) (j : Fin 3) {t : ℝ}
    (ht : t ∈ Icc 0 h) :
    traj x u t (vI j) = x (vI j) + t * (grav * ez j) -
      ∫ s in (0 : ℝ)..t, accT x u s * dn (traj x u s) j := by
  rw [traj_vI_integral x u j ht]
  congr 1
  refine integral_congr fun s hs => ?_
  show accel (thr (traj x u s)) * dn (traj x u s) j = accT x u s * dn (traj x u s) j
  rw [accel_traj_eq hf u s (uIcc_sub ht hs)]

/-- **The position rows as an integral of the velocity.** -/
theorem traj_pI_integral (x : X) (u : Fin 4 → ℝ) (j : Fin 3) {t : ℝ} (ht : t ∈ Icc 0 h) :
    traj x u t (pI j) = x (pI j) + ∫ s in (0 : ℝ)..t, traj x u s (vI j) := by
  have hc : ContinuousOn (fun s => traj x u s (vI j)) (Icc 0 h) :=
    (continuous_apply (vI j)).comp_continuousOn (traj_continuousOn x u)
  have hftc := integral_eq_sub_of_hasDerivAt (f := fun s => traj x u s (pI j))
    (f' := fun s => traj x u s (vI j))
    (fun s hs => by
      have := hasDerivAt_pi.1 (traj_hasDerivAt x u s (uIcc_sub ht hs)) (pI j)
      rwa [vf_pI] at this) ((hc.mono (uIcc_sub ht)).intervalIntegrable)
  simp only [traj_zero] at hftc
  linarith

/-- **The step's position and velocity rows as integrals over the period.** -/
theorem step_pv_integral (x : X) (u : Fin 4 → ℝ) (j : Fin 3) :
    step x u (vI j) = x (vI j) + h * (grav * ez j) -
        ∫ s in (0 : ℝ)..h, accel (thr (traj x u s)) * dn (traj x u s) j ∧
      step x u (pI j) = x (pI j) + ∫ s in (0 : ℝ)..h, traj x u s (vI j) :=
  ⟨traj_vI_integral x u j ⟨h_pos.le, le_rfl⟩, traj_pI_integral x u j ⟨h_pos.le, le_rfl⟩⟩

end

end Plant
