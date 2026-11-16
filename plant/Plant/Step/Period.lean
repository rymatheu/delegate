module

public import Plant.Step.Sharp

/-!
# Per-period bounds without evaluated constants

The thrust acts along the body down axis `d(q)`, whose Euclidean length is `‖q‖²`
(`sum_dn_sq`), and the thrust acceleration `a = T/m` is held over the period. So over `[0, t]` the
velocity differs from free fall, `v + t g e_z`, by a vector of Euclidean length at most `a ‖q‖² t`,
whatever the attitude does (`traj_v_dev_le`), and the position differs from free fall,
`p + t v + (t²/2) g e_z`, by at most `a ‖q‖² t² / 2` (`traj_p_dev_le`). These are the per-period
bounds of the translation block in the thrust range: with `a ≤ amax` and a unit quaternion the
velocity moves by at most `(g + amax) h` (`step_v_sub_le`), and the vertical velocity lies in
`[v_z + (g - a) h, v_z + (g + a) h]` (`step_vz_mem`). No rate bound and no CF2X number enter.
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

/-- **The velocity deviates from free fall by at most `a ‖q‖² t`** (Euclidean norm, squared), on
`[0, h]`. -/
theorem traj_v_dev_le (x : X) (u : Fin 4 → ℝ) :
    ∀ t ∈ Icc 0 h, ∑ j, (traj x u t (vI j) - x (vI j) - t * (grav * ez j)) ^ 2 ≤
      (accel u * qnormSq x * t) ^ 2 := by
  intro t ht
  set e : Fin 3 → ℝ := fun j => traj x u t (vI j) - x (vI j) - t * (grav * ez j)
  set E := ∑ j, e j ^ 2
  have ha := accel_nonneg u
  have hq := qnormSq_nonneg x
  have hE : 0 ≤ E := sum_nonneg fun _ _ => sq_nonneg _
  set f := fun s => ∑ j, e j * (traj x u s (vI j) - x (vI j) - s * (grav * ez j))
  have hd : ∀ s ∈ Icc 0 h, HasDerivAt f (∑ j, e j * (-(accel u * dn (traj x u s) j))) s := by
    intro s hs
    refine HasDerivAt.fun_sum fun j _ => ?_
    have h1 := hasDerivAt_pi.1 (traj_hasDerivAt x u s hs) (vI j)
    have := ((h1.sub_const (x (vI j))).sub ((hasDerivAt_id s).mul_const (grav * ez j))).const_mul (e j)
    convert this using 1
    · funext y; simp
    · rw [vf_vI]; ring
  have hb : ∀ s ∈ Icc 0 h, |∑ j, e j * (-(accel u * dn (traj x u s) j))| ≤
      accel u * (Real.sqrt E * qnormSq x) := by
    intro s hs
    have e1 : ∑ j, e j * (-(accel u * dn (traj x u s) j)) = -(accel u * ∑ j, e j * dn (traj x u s) j) := by
      rw [mul_sum, ← sum_neg_distrib]; congr 1; funext j; ring
    rw [e1, abs_neg, abs_mul, abs_of_nonneg ha]
    have := abs_sum_mul_dn_le (traj x u s) e
    rw [qnormSq_traj x u s hs] at this
    exact mul_le_mul_of_nonneg_left this ha
  have key := abs_sub_le_of_deriv hd hb t ht
  have f0 : f 0 = 0 := by simp [f, traj_zero]
  have ft : f t = E := by simp only [f, E, e, sq]
  rw [f0, ft, sub_zero, abs_of_nonneg hE] at key
  have := le_sq_of_le_mul_sqrt hE (by have := ht.1; positivity)
    (by linarith [key] : E ≤ (accel u * qnormSq x * t) * Real.sqrt E)
  exact this

/-- **The position deviates from free fall by at most `a ‖q‖² t² / 2`** (Euclidean norm, squared),
on `[0, h]`. -/
theorem traj_p_dev_le (x : X) (u : Fin 4 → ℝ) :
    ∀ t ∈ Icc 0 h, ∑ j, (traj x u t (pI j) - x (pI j) - t * x (vI j) - t ^ 2 / 2 * (grav * ez j)) ^ 2 ≤
      (accel u * qnormSq x * t ^ 2 / 2) ^ 2 := by
  intro t ht
  set e : Fin 3 → ℝ := fun j => traj x u t (pI j) - x (pI j) - t * x (vI j) - t ^ 2 / 2 * (grav * ez j)
  set E := ∑ j, e j ^ 2
  have ha := accel_nonneg u
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
  have hg : ∀ s ∈ Icc 0 h, |g s - g 0| ≤ accel u * qnormSq x * Real.sqrt E * s := by
    intro s hs
    have g0 : g 0 = 0 := by simp [g, traj_zero]
    rw [g0, sub_zero]
    have cs := Finset.sum_mul_sq_le_sq_mul_sq univ e
      (fun j => traj x u s (vI j) - x (vI j) - s * (grav * ez j))
    have hv := traj_v_dev_le x u s hs
    have hs0 := hs.1
    calc |g s| ≤ Real.sqrt (E * (accel u * qnormSq x * s) ^ 2) :=
          Real.abs_le_sqrt (cs.trans (mul_le_mul_of_nonneg_left hv hE))
      _ = _ := by
          rw [Real.sqrt_mul hE, Real.sqrt_sq (by positivity)]; ring
  have key := taylor2 hd hg t ht
  have f0 : f 0 = 0 := by simp [f, traj_zero]
  have g0 : g 0 = 0 := by simp [g, traj_zero]
  have ft : f t = E := by simp only [f, E, e, sq]
  rw [f0, g0, ft, sub_zero, mul_zero, sub_zero, abs_of_nonneg hE] at key
  exact le_sq_of_le_mul_sqrt hE (by have := ht.1; positivity) (by linarith [key])

/-- The velocity rows of the step against free fall. -/
theorem step_v_dev_le (x : X) (u : Fin 4 → ℝ) :
    ∑ j, (step x u (vI j) - x (vI j) - h * (grav * ez j)) ^ 2 ≤ (accel u * qnormSq x * h) ^ 2 :=
  traj_v_dev_le x u h ⟨h_pos.le, le_rfl⟩

/-- The position rows of the step against free fall. -/
theorem step_p_dev_le (x : X) (u : Fin 4 → ℝ) :
    ∑ j, (step x u (pI j) - x (pI j) - h * x (vI j) - h ^ 2 / 2 * (grav * ez j)) ^ 2 ≤
      (accel u * qnormSq x * h ^ 2 / 2) ^ 2 :=
  traj_p_dev_le x u h ⟨h_pos.le, le_rfl⟩

/-- **The vertical velocity over one period** lies in `[v_z + (g - a‖q‖²) h, v_z + (g + a‖q‖²) h]`. -/
theorem step_vz_mem (x : X) (u : Fin 4 → ℝ) :
    x 5 + (grav - accel u * qnormSq x) * h ≤ step x u 5 ∧
      step x u 5 ≤ x 5 + (grav + accel u * qnormSq x) * h := by
  have hv := step_v_dev_le x u
  simp only [Fin.sum_univ_three] at hv
  have a0 := sq_nonneg (step x u (vI 0) - x (vI 0) - h * (grav * ez 0))
  have a1 := sq_nonneg (step x u (vI 1) - x (vI 1) - h * (grav * ez 1))
  have e5 : step x u (vI 2) - x (vI 2) - h * (grav * ez 2) = step x u 5 - x 5 - h * grav := by
    have : ez 2 = 1 := by simp [ez]
    rw [this, mul_one]; rfl
  have h2 : (step x u 5 - x 5 - h * grav) ^ 2 ≤ (accel u * qnormSq x * h) ^ 2 := by
    rw [← e5]; linarith
  have hk : 0 ≤ accel u * qnormSq x * h := by
    have := accel_nonneg u; have := qnormSq_nonneg x; have := h_pos; positivity
  have := abs_le_of_sq_le_sq' h2 hk
  constructor <;> nlinarith [this.1, this.2]

/-- **Per-period velocity change in the thrust range**: for a unit quaternion each velocity
component moves by at most `(g + amax) h`. -/
theorem step_v_sub_le {x : X} (hq : qnormSq x = 1) (u : Fin 4 → ℝ) (j : Fin 3) :
    |step x u (vI j) - x (vI j)| ≤ (grav + amax) * h := by
  have hv := step_v_dev_le x u
  rw [hq, mul_one] at hv
  have hj : (step x u (vI j) - x (vI j) - h * (grav * ez j)) ^ 2 ≤ (accel u * h) ^ 2 :=
    le_trans (single_le_sum (f := fun j => (step x u (vI j) - x (vI j) - h * (grav * ez j)) ^ 2)
      (fun _ _ => sq_nonneg _) (mem_univ j)) hv
  have hk : 0 ≤ accel u * h := mul_nonneg (accel_nonneg u) h_pos.le
  have h1 := abs_le_of_sq_le_sq' hj hk
  have hez : |ez j| ≤ 1 := by fin_cases j <;> simp [ez]
  have hgz : |h * (grav * ez j)| ≤ grav * h := by
    rw [abs_mul, abs_mul, abs_of_pos h_pos, abs_of_pos grav_pos]
    have := mul_le_mul_of_nonneg_left hez (mul_pos h_pos grav_pos).le
    linarith
  have hA := accel_le u
  rw [abs_le] at hgz ⊢
  constructor <;> nlinarith [h1.1, h1.2, hgz.1, hgz.2, h_pos]

end

end Plant
