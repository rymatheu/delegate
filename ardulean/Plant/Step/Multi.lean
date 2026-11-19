module

public import Plant.Step.Sample
public import Plant.Step.Exact
public import Plant.Step.Symmetry

/-!
# Several periods

`stepN us n x` is the state after `n` periods from `x`, with the thrust fractions `us k` held over
period `k`; `trajN us x` is the piecewise trajectory through those periods. Every period is the
exact flow, so:
* periods compose (`stepN_add`), constant inputs give the sampled flow (`stepN_const`), and a run
  of the sampled plant is `stepN` of its inputs (`run_stepN`);
* `trajN` passes through `stepN` at the sample times `n h` (`trajN_sample`), is on each period the
  trajectory of that period (`trajN_eq_traj`), and solves the ODE with the period's input inside
  each period (`trajN_hasDerivAt`);
* `‖q‖²` (`qnormSq_stepN`), hover (`stepN_hover`), translations (`stepN_add_posVec`) and yaw
  rotations (`stepN_yawRot`) carry over to any number of periods;
* level flight under equal commands with equal thrusts stays level, the thrusts follow the lag across periods
  (`lagSol c f (n h)`), and the vertical velocity and altitude after `n` periods are explicit, with the integrals of
  the lagged thrust over the whole time `n h` (`stepN_level_vz`, `stepN_level_pz`).
Structural throughout.
-/

@[expose] public section

namespace Plant

noncomputable section

open Set

/-- **`n` periods**, with `us k` held over period `k`. -/
def stepN (us : ℕ → Fin 4 → ℝ) : ℕ → X → X
  | 0, x => x
  | n + 1, x => step (stepN us n x) (us n)

theorem stepN_zero (us : ℕ → Fin 4 → ℝ) (x : X) : stepN us 0 x = x := rfl

theorem stepN_succ (us : ℕ → Fin 4 → ℝ) (n : ℕ) (x : X) :
    stepN us (n + 1) x = step (stepN us n x) (us n) := rfl

/-- **Periods compose**: `m + n` periods are `m` periods, then `n` periods of the shifted inputs. -/
theorem stepN_add (us : ℕ → Fin 4 → ℝ) (m n : ℕ) (x : X) :
    stepN us (m + n) x = stepN (fun k => us (m + k)) n (stepN us m x) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [← add_assoc, stepN_succ, ih, stepN_succ]

/-- Constant inputs give the sampled flow. -/
theorem stepN_const (u : Fin 4 → ℝ) (n : ℕ) (x : X) :
    stepN (fun _ => u) n x = sampledFlow u n x := by
  rw [sampledFlow_apply]
  induction n with
  | zero => rfl
  | succ n ih => rw [stepN_succ, ih, Function.iterate_succ_apply']

/-- **A run of the sampled plant is `stepN` of its inputs.** -/
theorem run_stepN {s : ℕ → PState} {us : ℕ → Fin 4 → ℝ} (hs : IsRun s us) (n : ℕ) :
    (s n).x = stepN us n (s 0).x := by
  induction n with
  | zero => rfl
  | succ n ih => rw [hs n, nextR, stepN_succ, ih]

/-- **`‖q‖²` is kept over any number of periods.** -/
theorem qnormSq_stepN (us : ℕ → Fin 4 → ℝ) (n : ℕ) (x : X) :
    qnormSq (stepN us n x) = qnormSq x := by
  induction n with
  | zero => rfl
  | succ n ih => rw [stepN_succ, qnormSq_step, ih]

/-- **Hover is kept over any number of periods.** -/
theorem stepN_hover (z : ℝ) {u : Fin 4 → ℝ} (hu : ∀ i, u i = 1 / thrust2weight) (n : ℕ) :
    stepN (fun _ => u) n (hoverX z) = hoverX z := by
  induction n with
  | zero => rfl
  | succ n ih => rw [stepN_succ, ih, step_hover z hu]

/-- Several periods commute with translations. -/
theorem stepN_add_posVec (us : ℕ → Fin 4 → ℝ) (n : ℕ) (x : X) (a : Fin 3 → ℝ) :
    stepN us n (x + posVec a) = stepN us n x + posVec a := by
  induction n with
  | zero => rfl
  | succ n ih => rw [stepN_succ, ih, step_add_posVec, stepN_succ]

/-- Several periods are equivariant under rotations about the vertical axis. -/
theorem stepN_yawRot {c s : ℝ} (hcs : c ^ 2 + s ^ 2 = 1) (us : ℕ → Fin 4 → ℝ) (n : ℕ) (x : X) :
    stepN us n (yawRot c s x) = yawRot c s (stepN us n x) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [stepN_succ, ih, step_yawRot hcs, stepN_succ]

/-! ## Level flight over several periods -/

/-- **Level flight stays level** under equal commands: a yaw-only attitude without rates, with equal thrusts in
`[0, 1]`, stays so; the attitude is unchanged and the common thrust is the lag over the whole time. -/
theorem stepN_level_state {x : X} (hx : SpinState x) (h12 : x 12 = 0) (hf : ThrustRange x) (he : EqualThr x)
    (c : ℝ) (n : ℕ) :
    SpinState (stepN (fun _ => fun _ => c) n x) ∧ stepN (fun _ => fun _ => c) n x 12 = 0 ∧
      ThrustRange (stepN (fun _ => fun _ => c) n x) ∧ EqualThr (stepN (fun _ => fun _ => c) n x) ∧
      stepN (fun _ => fun _ => c) n x 6 = x 6 ∧ stepN (fun _ => fun _ => c) n x 9 = x 9 ∧
      thr (stepN (fun _ => fun _ => c) n x) 0 = lagSol (clip01 c) (thr x 0) (n * h) := by
  induction n with
  | zero => exact ⟨hx, h12, hf, he, rfl, rfl, by simp [lagSol_zero, stepN_zero]⟩
  | succ n ih =>
    obtain ⟨hs, hr, hfr, hee, h6, h9, h0⟩ := ih
    obtain ⟨s1, s2, s3, s4, s5, s6⟩ := step_level hs hr hfr hee c
    refine ⟨s1, s2, step_thrustRange hfr _, s5, s3.trans h6, s4.trans h9, ?_⟩
    rw [stepN_succ, s6, h0, lagSol_add]; push_cast; ring_nf

/-- **The vertical velocity after `n` level periods** with a unit quaternion, equal thrusts `f` and equal commands
`c`: `v_z + n h g - amax lagK1 (clip01 c) f (n h)`, the integral of the lagged thrust over the whole time. -/
theorem stepN_level_vz {x : X} (hx : SpinState x) (h12 : x 12 = 0) (hf : ThrustRange x) (he : EqualThr x)
    (hq : qnormSq x = 1) (c : ℝ) (n : ℕ) :
    stepN (fun _ => fun _ => c) n x 5 = x 5 + n * h * grav - amax * lagK1 (clip01 c) (thr x 0) (n * h) := by
  induction n with
  | zero => simp [stepN_zero, lagK1_zero]
  | succ n ih =>
    obtain ⟨hs, -, hfr, hee, h6, h9, h0⟩ := stepN_level_state hx h12 hf he c n
    have hq' : stepN (fun _ => fun _ => c) n x 6 ^ 2 + stepN (fun _ => fun _ => c) n x 9 ^ 2 = 1 := by
      rw [h6, h9]; simp only [qnormSq, hx.1, hx.2.1] at hq; linarith
    rw [stepN_succ, step_level_vz hs hfr hee hq', ih, h0, show ((n + 1 : ℕ) : ℝ) * h = n * h + h by push_cast; ring,
      lagK1_add]
    ring

/-- **The altitude after `n` level periods**: `p_z + n h v_z + g (n h)²/2 - amax lagK3 (clip01 c) f (n h)`. -/
theorem stepN_level_pz {x : X} (hx : SpinState x) (h12 : x 12 = 0) (hf : ThrustRange x) (he : EqualThr x)
    (hq : qnormSq x = 1) (c : ℝ) (n : ℕ) :
    stepN (fun _ => fun _ => c) n x 2 =
      x 2 + n * h * x 5 + (n * h) ^ 2 / 2 * grav - amax * lagK3 (clip01 c) (thr x 0) (n * h) := by
  induction n with
  | zero => simp [stepN_zero, lagK3_zero]
  | succ n ih =>
    obtain ⟨hs, -, hfr, hee, h6, h9, h0⟩ := stepN_level_state hx h12 hf he c n
    have hq' : stepN (fun _ => fun _ => c) n x 6 ^ 2 + stepN (fun _ => fun _ => c) n x 9 ^ 2 = 1 := by
      rw [h6, h9]; simp only [qnormSq, hx.1, hx.2.1] at hq; linarith
    have hp : PairedThr (stepN (fun _ => fun _ => c) n x) := ⟨hee 1, by rw [hee 3, hee 2]⟩
    rw [stepN_succ, step_spin_pz hs hfr hp (pairedCmd_const c), hq', ih,
      stepN_level_vz hx h12 hf he hq c n]
    have hk : accK3 (stepN (fun _ => fun _ => c) n x) (fun _ => c) h =
        amax * lagK3 (clip01 c) (thr (stepN (fun _ => fun _ => c) n x) 0) h := by
      simp only [accK, hee 1, hee 2, hee 3]; ring
    rw [hk, h0, show ((n + 1 : ℕ) : ℝ) * h = n * h + h by push_cast; ring, lagK3_add]
    ring

/-! ## The trajectory through several periods -/

/-- **The piecewise trajectory**: in period `n = ⌊T / h⌋`, the trajectory of that period from
`stepN us n x` under `us n`. -/
def trajN (us : ℕ → Fin 4 → ℝ) (x : X) (T : ℝ) : X :=
  traj (stepN us ⌊T / h⌋₊ x) (us ⌊T / h⌋₊) (T - ⌊T / h⌋₊ * h)

private theorem floor_eq_of_mem {n : ℕ} {T : ℝ} (hT : T ∈ Ico (n * h) ((n + 1) * h)) :
    ⌊T / h⌋₊ = n := by
  have hh := h_pos
  rw [Nat.floor_eq_iff (div_nonneg ((by positivity : (0 : ℝ) ≤ n * h).trans hT.1) hh.le)]
  constructor
  · rw [le_div_iff₀ hh]; exact hT.1
  · rw [div_lt_iff₀ hh]; exact hT.2

/-- **On period `n` the piecewise trajectory is the trajectory of that period.** -/
theorem trajN_eq_traj (us : ℕ → Fin 4 → ℝ) (x : X) {n : ℕ} {T : ℝ}
    (hT : T ∈ Ico (n * h) ((n + 1) * h)) :
    trajN us x T = traj (stepN us n x) (us n) (T - n * h) := by
  rw [trajN, floor_eq_of_mem hT]

/-- **At the sample times the piecewise trajectory is `stepN`.** -/
theorem trajN_sample (us : ℕ → Fin 4 → ℝ) (x : X) (n : ℕ) : trajN us x (n * h) = stepN us n x := by
  rw [trajN_eq_traj us x ⟨le_rfl, by nlinarith [h_pos]⟩, sub_self, traj_zero]

/-- The piecewise trajectory reaches `stepN us (n + 1) x` at the end of period `n`, as the
trajectory of period `n` at `h`. -/
theorem trajN_end (us : ℕ → Fin 4 → ℝ) (x : X) (n : ℕ) :
    traj (stepN us n x) (us n) h = trajN us x ((n + 1 : ℕ) * h) := by
  rw [trajN_sample, stepN_succ]; rfl

/-- **Inside each period the piecewise trajectory solves the ODE** with that period's input. -/
theorem trajN_hasDerivAt (us : ℕ → Fin 4 → ℝ) (x : X) {n : ℕ} {T : ℝ}
    (hT : T ∈ Ioo (n * h) ((n + 1) * h)) :
    HasDerivAt (trajN us x) (vf (trajN us x T) (us n)) T := by
  have hev : (fun S => traj (stepN us n x) (us n) (S - n * h)) =ᶠ[nhds T] trajN us x := by
    filter_upwards [Ioo_mem_nhds hT.1 hT.2] with S hS
    exact (trajN_eq_traj us x ⟨hS.1.le, hS.2⟩).symm
  have hd := traj_hasDerivAt (stepN us n x) (us n) (T - n * h)
    ⟨by linarith [hT.1], by linarith [hT.2]⟩
  have := hd.comp_sub_const T (n * h)
  rw [trajN_eq_traj us x ⟨hT.1.le, hT.2⟩]
  exact this.congr_of_eventuallyEq hev.symm

end

end Plant
