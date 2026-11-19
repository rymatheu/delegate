module

public import Plant.Step.Sharp

/-!
# Per-period bounds without evaluated constants

The thrust acts along the body down axis `d(q)`, whose Euclidean length is `‖q‖²` (`sum_dn_sq`), and the thrust
acceleration over the period is the lagged one, `a(t) = accT x u t` (`Plant.Step.Sharp`). So over `[0, t]` the
velocity differs from free fall, `v + t g e_z`, by a vector of Euclidean length at most `accK1(t) ‖q‖²`, where
`accK1(t) = ∫₀ᵗ a` is the integral of the lagged thrust acceleration, whatever the attitude does (`traj_v_dev_le`),
and the position differs from free fall, `p + t v + (t²/2) g e_z`, by at most `accK3(t) ‖q‖²`, `accK3 = ∫ accK1`
(`traj_p_dev_le`). With `a ≤ amax` and a unit quaternion the velocity moves by at most `(g + amax) h`
(`step_v_sub_le`), and the vertical velocity lies in `[v_z + g h - accK1(h) ‖q‖², v_z + g h + accK1(h) ‖q‖²]`
(`step_vz_mem`). Thrusts in `[0, 1]⁴`; no rate bound and no number of the vehicle enter.
-/

@[expose] public section

namespace Plant

noncomputable section

open Set Finset

private theorem abs_sum_mul_dn_le (x : X) (e : Fin 3 → ℝ) :
    |∑ j, e j * dn x j| ≤ Real.sqrt (∑ j, e j ^ 2) * qnormSq x := by
  have cs := Finset.sum_mul_sq_le_sq_mul_sq univ e (dn x)
  rw [sum_dn_sq] at cs
  have hq := qnormSq_nonneg x
  calc |∑ j, e j * dn x j| ≤ Real.sqrt ((∑ j, e j ^ 2) * qnormSq x ^ 2) := Real.abs_le_sqrt cs
    _ = _ := by rw [Real.sqrt_mul (by positivity), Real.sqrt_sq hq]

/-- From `E ≤ k √E` with `k ≥ 0`: `E ≤ k²`. -/
private theorem le_sq_of_le_mul_sqrt {E k : ℝ} (hE : 0 ≤ E) (hk : 0 ≤ k)
    (h : E ≤ k * Real.sqrt E) : E ≤ k ^ 2 := by
  set r := Real.sqrt E
  have hr : 0 ≤ r := Real.sqrt_nonneg E
  have hrr : r ^ 2 = E := Real.sq_sqrt hE
  rw [← hrr] at h ⊢
  rcases le_or_gt r k with hrk | hrk
  · nlinarith
  · nlinarith

theorem accK1_nonneg {x : X} {u : Fin 4 → ℝ} (hf : ThrustRange x) : ∀ t ∈ Icc 0 h, 0 ≤ accK1 x u t := by
  intro t ht
  have := abs_sub_le_of_deriv (f := accK1 x u) (g := accT x u) (C := amax)
    (fun s _ => hasDerivAt_accK1 x u s)
    (fun s hs => by rw [abs_of_nonneg (accT_nonneg hf s hs)]; exact accT_le hf s hs) t ht
  have hm := monotoneOn_of_hasDerivWithinAt_nonneg (D := Icc 0 h) (convex_Icc 0 h) (f := accK1 x u)
    (f' := accT x u) (fun s _ => (hasDerivAt_accK1 x u s).continuousAt.continuousWithinAt)
    (fun s _ => (hasDerivAt_accK1 x u s).hasDerivWithinAt)
    (fun s hs => accT_nonneg hf s (interior_subset hs))
  have := hm ⟨le_rfl, h_pos.le⟩ ht ht.1
  rwa [accK1_zero] at this

theorem accK1_le {x : X} {u : Fin 4 → ℝ} (hf : ThrustRange x) : ∀ t ∈ Icc 0 h, accK1 x u t ≤ amax * t := by
  intro t ht
  have := abs_sub_le_of_deriv (f := accK1 x u) (g := accT x u) (C := amax)
    (fun s _ => hasDerivAt_accK1 x u s)
    (fun s hs => by rw [abs_of_nonneg (accT_nonneg hf s hs)]; exact accT_le hf s hs) t ht
  rw [accK1_zero, sub_zero] at this
  exact (le_abs_self _).trans this

/-- **The velocity deviates from free fall by at most `accK1(t) ‖q‖²`** (Euclidean norm, squared), on `[0, h]`,
`accK1(t) = ∫₀ᵗ a` the integral of the lagged thrust acceleration. -/
theorem traj_v_dev_le {x : X} (hf : ThrustRange x) (u : Fin 4 → ℝ) :
    ∀ t ∈ Icc 0 h, ∑ j, (traj x u t (vI j) - x (vI j) - t * (grav * ez j)) ^ 2 ≤
      (accK1 x u t * qnormSq x) ^ 2 := by
  intro t ht
  set e : Fin 3 → ℝ := fun j => traj x u t (vI j) - x (vI j) - t * (grav * ez j)
  set E := ∑ j, e j ^ 2
  have hq := qnormSq_nonneg x
  have hE : 0 ≤ E := sum_nonneg fun _ _ => sq_nonneg _
  set f := fun s => ∑ j, e j * (traj x u s (vI j) - x (vI j) - s * (grav * ez j))
  have hd : ∀ s ∈ Icc 0 h, HasDerivAt f (∑ j, e j * (-(accT x u s * dn (traj x u s) j))) s := by
    intro s hs
    refine HasDerivAt.fun_sum fun j _ => ?_
    have h1 := hasDerivAt_pi.1 (traj_hasDerivAt x u s hs) (vI j)
    have := ((h1.sub_const (x (vI j))).sub ((hasDerivAt_id s).mul_const (grav * ez j))).const_mul (e j)
    convert this using 1
    · funext y; simp
    · rw [vf_vI, accel_traj_eq hf u s hs]; ring
  have hb : ∀ s ∈ Icc 0 h, |∑ j, e j * (-(accT x u s * dn (traj x u s) j)) - 0| ≤
      Real.sqrt E * qnormSq x * accT x u s := by
    intro s hs
    have e1 : ∑ j, e j * (-(accT x u s * dn (traj x u s) j)) - 0 =
        -(accT x u s * ∑ j, e j * dn (traj x u s) j) := by
      rw [sub_zero, mul_sum, ← sum_neg_distrib]; congr 1; funext j; ring
    rw [e1, abs_neg, abs_mul, abs_of_nonneg (accT_nonneg hf s hs)]
    have := abs_sum_mul_dn_le (traj x u s) e
    rw [qnormSq_traj x u s hs] at this
    calc accT x u s * |∑ j, e j * dn (traj x u s) j| ≤ accT x u s * (Real.sqrt E * qnormSq x) :=
          mul_le_mul_of_nonneg_left this (accT_nonneg hf s hs)
      _ = _ := by ring
  have key := abs_sub_poly_le (f := f) (P := fun _ => 0) (p := fun _ => 0)
    (B := fun s => Real.sqrt E * qnormSq x * accK1 x u s) (B' := fun s => Real.sqrt E * qnormSq x * accT x u s)
    hd (fun _ => hasDerivAt_const _ _) (fun s => (hasDerivAt_accK1 x u s).const_mul _)
    (by simp [accK1_zero]) hb t ht
  have f0 : f 0 = 0 := by simp [f, traj_zero]
  have ft : f t = E := by simp only [f, E, e, sq]
  rw [f0, ft, sub_zero, sub_self, sub_zero, abs_of_nonneg hE] at key
  exact le_sq_of_le_mul_sqrt hE (mul_nonneg (accK1_nonneg hf t ht) hq)
    (by linarith [key] : E ≤ (accK1 x u t * qnormSq x) * Real.sqrt E)

/-- **The position deviates from free fall by at most `accK3(t) ‖q‖²`** (Euclidean norm, squared), on `[0, h]`. -/
theorem traj_p_dev_le {x : X} (hf : ThrustRange x) (u : Fin 4 → ℝ) :
    ∀ t ∈ Icc 0 h, ∑ j, (traj x u t (pI j) - x (pI j) - t * x (vI j) - t ^ 2 / 2 * (grav * ez j)) ^ 2 ≤
      (accK3 x u t * qnormSq x) ^ 2 := by
  intro t ht
  set e : Fin 3 → ℝ := fun j => traj x u t (pI j) - x (pI j) - t * x (vI j) - t ^ 2 / 2 * (grav * ez j)
  set E := ∑ j, e j ^ 2
  have hq := qnormSq_nonneg x
  have hE : 0 ≤ E := sum_nonneg fun _ _ => sq_nonneg _
  set f := fun s => ∑ j, e j * (traj x u s (pI j) - x (pI j) - s * x (vI j) - s ^ 2 / 2 * (grav * ez j))
  set g := fun s => ∑ j, e j * (traj x u s (vI j) - x (vI j) - s * (grav * ez j))
  have hd : ∀ s ∈ Icc 0 h, HasDerivAt f (g s) s := by
    intro s hs
    refine HasDerivAt.fun_sum fun j _ => ?_
    have h1 := hasDerivAt_pi.1 (traj_hasDerivAt x u s hs) (pI j)
    have := (((h1.sub_const (x (pI j))).sub ((hasDerivAt_id s).mul_const (x (vI j)))).sub
      (((hasDerivAt_pow 2 s).div_const 2).mul_const (grav * ez j))).const_mul (e j)
    convert this using 1
    · funext y; simp
    · rw [vf_pI]; simp
  have hg : ∀ s ∈ Icc 0 h, |g s - 0| ≤ Real.sqrt E * qnormSq x * accK1 x u s := by
    intro s hs
    rw [sub_zero]
    have cs := Finset.sum_mul_sq_le_sq_mul_sq univ e
      (fun j => traj x u s (vI j) - x (vI j) - s * (grav * ez j))
    have hv := traj_v_dev_le hf u s hs
    have hk := accK1_nonneg (u := u) hf s hs
    calc |g s| ≤ Real.sqrt (E * (accK1 x u s * qnormSq x) ^ 2) :=
          Real.abs_le_sqrt (cs.trans (mul_le_mul_of_nonneg_left hv hE))
      _ = _ := by
          rw [Real.sqrt_mul hE, Real.sqrt_sq (by positivity)]; ring
  have key := abs_sub_poly_le (f := f) (P := fun _ => 0) (p := fun _ => 0)
    (B := fun s => Real.sqrt E * qnormSq x * accK3 x u s) (B' := fun s => Real.sqrt E * qnormSq x * accK1 x u s)
    hd (fun _ => hasDerivAt_const _ _) (fun s => (hasDerivAt_accK3 x u s).const_mul _)
    (by simp [accK3_zero]) hg t ht
  have f0 : f 0 = 0 := by simp [f, traj_zero]
  have ft : f t = E := by simp only [f, E, e, sq]
  have hk3 : 0 ≤ accK3 x u t := by
    have := abs_sub_poly_le (f := accK3 x u) (g := accK1 x u) (P := fun _ => 0) (p := fun _ => 0)
      (B := accK3 x u) (B' := accK1 x u) (fun s _ => hasDerivAt_accK3 x u s) (fun _ => hasDerivAt_const _ _)
      (fun s => hasDerivAt_accK3 x u s) (accK3_zero x u)
      (fun s hs => by rw [sub_zero, abs_of_nonneg (accK1_nonneg hf s hs)]) t ht
    exact (abs_nonneg _).trans (by simpa [accK3_zero] using this)
  rw [f0, ft, sub_zero, sub_self, sub_zero, abs_of_nonneg hE] at key
  exact le_sq_of_le_mul_sqrt hE (mul_nonneg hk3 hq) (by linarith [key])

/-- The velocity rows of the step against free fall. -/
theorem step_v_dev_le {x : X} (hf : ThrustRange x) (u : Fin 4 → ℝ) :
    ∑ j, (step x u (vI j) - x (vI j) - h * (grav * ez j)) ^ 2 ≤ (accK1 x u h * qnormSq x) ^ 2 :=
  traj_v_dev_le hf u h ⟨h_pos.le, le_rfl⟩

/-- The position rows of the step against free fall. -/
theorem step_p_dev_le {x : X} (hf : ThrustRange x) (u : Fin 4 → ℝ) :
    ∑ j, (step x u (pI j) - x (pI j) - h * x (vI j) - h ^ 2 / 2 * (grav * ez j)) ^ 2 ≤
      (accK3 x u h * qnormSq x) ^ 2 :=
  traj_p_dev_le hf u h ⟨h_pos.le, le_rfl⟩

/-- **The vertical velocity over one period** lies in
`[v_z + g h - accK1(h) ‖q‖², v_z + g h + accK1(h) ‖q‖²]`. -/
theorem step_vz_mem {x : X} (hf : ThrustRange x) (u : Fin 4 → ℝ) :
    x 5 + grav * h - accK1 x u h * qnormSq x ≤ step x u 5 ∧
      step x u 5 ≤ x 5 + grav * h + accK1 x u h * qnormSq x := by
  have hv := step_v_dev_le hf u
  simp only [Fin.sum_univ_three] at hv
  have a0 := sq_nonneg (step x u (vI 0) - x (vI 0) - h * (grav * ez 0))
  have a1 := sq_nonneg (step x u (vI 1) - x (vI 1) - h * (grav * ez 1))
  have e5 : step x u (vI 2) - x (vI 2) - h * (grav * ez 2) = step x u 5 - x 5 - h * grav := by
    have : ez 2 = 1 := by simp [ez]
    rw [this, mul_one]; rfl
  have h2 : (step x u 5 - x 5 - h * grav) ^ 2 ≤ (accK1 x u h * qnormSq x) ^ 2 := by
    rw [← e5]; linarith
  have hk : 0 ≤ accK1 x u h * qnormSq x :=
    mul_nonneg (accK1_nonneg hf h ⟨h_pos.le, le_rfl⟩) (qnormSq_nonneg x)
  have := abs_le_of_sq_le_sq' h2 hk
  constructor <;> nlinarith [this.1, this.2]

/-- **Per-period velocity change in the thrust range**: for a unit quaternion each velocity component moves by at
most `(g + amax) h`. -/
theorem step_v_sub_le {x : X} (hq : qnormSq x = 1) (hf : ThrustRange x) (u : Fin 4 → ℝ) (j : Fin 3) :
    |step x u (vI j) - x (vI j)| ≤ (grav + amax) * h := by
  have hv := step_v_dev_le hf u
  rw [hq, mul_one] at hv
  have hj : (step x u (vI j) - x (vI j) - h * (grav * ez j)) ^ 2 ≤ (accK1 x u h) ^ 2 :=
    le_trans (single_le_sum (f := fun j => (step x u (vI j) - x (vI j) - h * (grav * ez j)) ^ 2)
      (fun _ _ => sq_nonneg _) (mem_univ j)) hv
  have hh : h ∈ Icc 0 h := ⟨h_pos.le, le_rfl⟩
  have hk : 0 ≤ accK1 x u h := accK1_nonneg hf h hh
  have hA : accK1 x u h ≤ amax * h := accK1_le hf h hh
  have h1 := abs_le_of_sq_le_sq' hj hk
  have hez : |ez j| ≤ 1 := by fin_cases j <;> simp [ez]
  have hgz : |h * (grav * ez j)| ≤ grav * h := by
    rw [abs_mul, abs_mul, abs_of_pos h_pos, abs_of_pos grav_pos]
    have := mul_le_mul_of_nonneg_left hez (mul_pos h_pos grav_pos).le
    linarith
  rw [abs_le] at hgz ⊢
  constructor <;> nlinarith [h1.1, h1.2, hgz.1, hgz.2, h_pos]

end

end Plant
