module

public import Plant.Model.Field
public import Plant.Lib.Gronwall
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Tactic

/-!
# The motor lag

The lag `lagRate c f = (c - f) / τ(c, f)` with `τ = tauUp` when `c > f` and `tauDown` otherwise is the maximum of the
two linear lags (`lagRate_eq_max`, because `tauUp < tauDown`): `max ((c - f)/tauUp) ((c - f)/tauDown)`. Hence it is
continuous, increasing in `c`, decreasing in `f`, zero exactly at `f = c`, and Lipschitz with constant `1/tauUp`
in `c - f` (`abs_lagRate_sub_le`), although the time constant jumps at `f = c`.

**Exact flow** (`lagSol`). For a constant command `c` the solution from `f` is
`lagSol c f t = c + (f - c) e^{-t/τ(c, f)}`: it never crosses `c`, so the time constant chosen at the start is kept
(`lagTau_lagSol`), and it solves `ḟ = lagRate c f` for every `t` (`hasDerivAt_lagSol`). It is a flow
(`lagSol_add`).

**The simulator's update** (`simLag`): once per physics substep `dt` the simulator replaces the thrust by
`f + (c - f)(1 - e^{-dt/τ(c, f)})` (`AirframeAviary._physics`, `sim/world/airframes.py:64-66`). This is the exact
flow over `dt` (`simLag_eq_lagSol`), so three substeps of `hPhys` with the command held give the exact flow over the
control period `h` (`simLag_three`): on the motor block the model and the simulator agree exactly.

**Sensitivity of the exact flow.** The end value is increasing in the command with slope at most
`1 - e^{-t/tauUp}` (`abs_lagSol_sub_cmd_le`) and increasing in the start value with slope at most `e^{-t/tauDown}`
(`abs_lagSol_sub_init_le`); both are attained (a command step up, a start value above the command). A thrust in
`[0, 1]` under a command in `[0, 1]` stays in `[0, 1]` and moves monotonically toward the command (`lagSol_mem`).
-/

@[expose] public section

namespace Plant

noncomputable section

open Set

/-! ## The lag rate -/

theorem lagTau_pos (c f : ℝ) : 0 < lagTau c f := by
  unfold lagTau; split_ifs
  · exact tauUp_pos
  · exact tauDown_pos

theorem tauUp_le_lagTau (c f : ℝ) : tauUp ≤ lagTau c f := by
  unfold lagTau; split_ifs
  · exact le_rfl
  · exact tauUp_le_tauDown

/-- `e / tauDown ≤ e / tauUp` for `e ≥ 0`. -/
theorem div_tauDown_le {e : ℝ} (he : 0 ≤ e) : e / tauDown ≤ e / tauUp :=
  div_le_div_of_nonneg_left he tauUp_pos tauUp_le_tauDown

/-- `e / tauUp ≤ e / tauDown` for `e ≤ 0`. -/
theorem div_tauUp_le {e : ℝ} (he : e ≤ 0) : e / tauUp ≤ e / tauDown := by
  have := div_tauDown_le (e := -e) (by linarith)
  rw [neg_div, neg_div] at this; linarith

/-- **The lag is the larger of the two linear lags.** -/
theorem lagRate_eq_max (c f : ℝ) : lagRate c f = max ((c - f) / tauUp) ((c - f) / tauDown) := by
  unfold lagRate lagTau
  split_ifs with hcf
  · exact (max_eq_left (div_tauDown_le (by linarith))).symm
  · exact (max_eq_right (div_tauUp_le (by linarith))).symm

/-- **The lag is `1/tauUp`-Lipschitz** in the gap `c - f`. -/
theorem abs_lagRate_sub_le (c f c' f' : ℝ) :
    |lagRate c f - lagRate c' f'| ≤ |(c - f) - (c' - f')| / tauUp := by
  rw [lagRate_eq_max, lagRate_eq_max]
  refine (abs_max_sub_max_le_max _ _ _ _).trans (max_le ?_ ?_)
  · rw [← sub_div, abs_div, abs_of_pos tauUp_pos]
  · rw [← sub_div, abs_div, abs_of_pos tauDown_pos]
    exact div_le_div_of_nonneg_left (abs_nonneg _) tauUp_pos tauUp_le_tauDown

/-- `|lagRate c f| ≤ |c - f| / tauUp`. -/
theorem abs_lagRate_le (c f : ℝ) : |lagRate c f| ≤ |c - f| / tauUp := by
  have := abs_lagRate_sub_le c f 0 0
  simpa [lagRate, lagTau] using this

/-- The lag is Lipschitz in the thrust with constant `1/tauUp`. -/
theorem abs_lagRate_sub_thrust_le (c f f' : ℝ) : |lagRate c f - lagRate c f'| ≤ |f - f'| / tauUp := by
  refine (abs_lagRate_sub_le c f c f').trans (le_of_eq ?_)
  rw [show c - f - (c - f') = -(f - f') by ring, abs_neg]

/-- The lag is Lipschitz in the command with constant `1/tauUp`. -/
theorem abs_lagRate_sub_cmd_le (c c' f : ℝ) : |lagRate c f - lagRate c' f| ≤ |c - c'| / tauUp := by
  refine (abs_lagRate_sub_le c f c' f).trans (le_of_eq ?_)
  rw [show c - f - (c' - f) = c - c' by ring]

/-- The lag pushes toward the command: `(c - f) · lagRate c f ≥ 0`. -/
theorem lagRate_mul_nonneg (c f : ℝ) : 0 ≤ (c - f) * lagRate c f := by
  unfold lagRate
  rw [mul_div_assoc', le_div_iff₀ (lagTau_pos c f), zero_mul]
  exact mul_self_nonneg _

theorem lagRate_self (c : ℝ) : lagRate c c = 0 := by simp [lagRate]

/-- The lag is monotone in the command. -/
theorem lagRate_mono {c c' : ℝ} (f : ℝ) (h : c ≤ c') : lagRate c f ≤ lagRate c' f := by
  rw [lagRate_eq_max, lagRate_eq_max]
  exact max_le_max (div_le_div_of_nonneg_right (by linarith) tauUp_pos.le)
    (div_le_div_of_nonneg_right (by linarith) tauDown_pos.le)

/-! ## The exact flow of one propeller -/

/-- **The exact flow of the lag** under the constant command `c` from the thrust `f`:
`c + (f - c) e^{-t/τ(c, f)}`. -/
def lagSol (c f t : ℝ) : ℝ := c + (f - c) * Real.exp (-t / lagTau c f)

theorem lagSol_zero (c f : ℝ) : lagSol c f 0 = f := by simp [lagSol]

/-- The gap to the command shrinks by the factor `e^{-t/τ}`. -/
theorem sub_lagSol (c f t : ℝ) : c - lagSol c f t = (c - f) * Real.exp (-t / lagTau c f) := by
  unfold lagSol; ring

/-- The flow does not cross the command, so the time constant chosen at the start is kept. -/
theorem lagTau_lagSol (c f t : ℝ) : lagTau c (lagSol c f t) = lagTau c f := by
  have he := Real.exp_pos (-t / lagTau c f)
  have hs := sub_lagSol c f t
  unfold lagTau
  by_cases h : c > f
  · have : c > lagSol c f t := by nlinarith
    rw [ite_eq_left h, ite_eq_left this]
  · have : ¬ c > lagSol c f t := by push Not at h ⊢; nlinarith
    rw [ite_eq_right h, ite_eq_right this]

/-- **The exact flow solves the lag.** -/
theorem hasDerivAt_lagSol (c f t : ℝ) :
    HasDerivAt (fun s => lagSol c f s) (lagRate c (lagSol c f t)) t := by
  have hτ := (lagTau_pos c f).ne'
  have := ((hasDerivAt_exp_neg_div (τ := lagTau c f) t).const_mul (f - c)).const_add c
  refine this.congr_deriv ?_
  rw [lagRate, lagTau_lagSol, sub_lagSol]
  field_simp
  ring

/-- The exact flow is a flow. -/
theorem lagSol_add (c f s t : ℝ) : lagSol c (lagSol c f s) t = lagSol c f (s + t) := by
  show c + (lagSol c f s - c) * Real.exp (-t / lagTau c (lagSol c f s)) = _
  rw [lagTau_lagSol]
  unfold lagSol
  rw [show -(s + t) / lagTau c f = -s / lagTau c f + -t / lagTau c f by ring, Real.exp_add]
  ring

/-- The exact flow in terms of the step response: `f + (c - f)(1 - e^{-t/τ})`. -/
theorem lagSol_eq (c f t : ℝ) : lagSol c f t = f + (c - f) * lagM0 (lagTau c f) t := by
  unfold lagSol lagM0; ring

/-! ## The simulator's update -/

/-- **The simulator's lag update** over one physics substep `dt`:
`f + (c - f)(1 - e^{-dt/τ(c, f)})` (`sim/world/airframes.py:64-66`, in normalized thrust). -/
def simLag (c f dt : ℝ) : ℝ := f + (c - f) * (1 - Real.exp (-dt / lagTau c f))

/-- **The simulator's update is the exact flow** over the substep. -/
theorem simLag_eq_lagSol (c f dt : ℝ) : simLag c f dt = lagSol c f dt := by
  unfold simLag lagSol; ring

/-- **Three substeps of the simulator are the exact flow over the control period.** -/
theorem simLag_three (c f : ℝ) :
    simLag c (simLag c (simLag c f hPhys) hPhys) hPhys = lagSol c f h := by
  simp only [simLag_eq_lagSol, lagSol_add, h_eq_three_hPhys]
  ring_nf

/-! ## Range and monotonicity -/

/-- The flow stays between its start and the command. -/
theorem lagSol_between (c f : ℝ) {t : ℝ} (ht : 0 ≤ t) :
    min f c ≤ lagSol c f t ∧ lagSol c f t ≤ max f c := by
  have he0 := Real.exp_pos (-t / lagTau c f)
  have he1 : Real.exp (-t / lagTau c f) ≤ 1 :=
    Real.exp_le_one_iff.2 (div_nonpos_of_nonpos_of_nonneg (by linarith) (lagTau_pos c f).le)
  unfold lagSol
  rcases le_total f c with hfc | hcf
  · rw [min_eq_left hfc, max_eq_right hfc]; constructor <;> nlinarith
  · rw [min_eq_right hcf, max_eq_left hcf]; constructor <;> nlinarith

/-- **The thrust range is invariant**: a thrust in `[0, 1]` under a command in `[0, 1]` stays in `[0, 1]`. -/
theorem lagSol_mem {c f : ℝ} (hc : c ∈ Icc (0 : ℝ) 1) (hf : f ∈ Icc (0 : ℝ) 1) {t : ℝ} (ht : 0 ≤ t) :
    lagSol c f t ∈ Icc (0 : ℝ) 1 := by
  obtain ⟨h1, h2⟩ := lagSol_between c f ht
  exact ⟨le_trans (le_min hf.1 hc.1) h1, h2.trans (max_le hf.2 hc.2)⟩

/-- **The thrust moves monotonically toward the command**: the gap `|c - f|` decreases. -/
theorem abs_sub_lagSol_le (c f : ℝ) {s t : ℝ} (hst : s ≤ t) :
    |c - lagSol c f t| ≤ |c - lagSol c f s| := by
  rw [sub_lagSol, sub_lagSol, abs_mul, abs_mul, abs_of_pos (Real.exp_pos _),
    abs_of_pos (Real.exp_pos _)]
  exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.2
    (div_le_div_of_nonneg_right (by linarith) (lagTau_pos c f).le)) (abs_nonneg _)

/-- The thrust approaches the command monotonically: between two times the later value lies between the earlier
value and the command. -/
theorem lagSol_mono_toward (c f : ℝ) {s t : ℝ} (hst : s ≤ t) :
    min (lagSol c f s) c ≤ lagSol c f t ∧ lagSol c f t ≤ max (lagSol c f s) c := by
  have := lagSol_between c (lagSol c f s) (t := t - s) (by linarith)
  rwa [lagSol_add, add_sub_cancel] at this

/-! ## Sensitivity of the exact flow -/

/-- The end value as a function of the command, for `c ≥ f` and `c ≤ f`. -/
private theorem lagSol_up {c f t : ℝ} (h : f < c) : lagSol c f t = f + (c - f) * lagM0 tauUp t := by
  rw [lagSol_eq, lagTau, ite_eq_left h]

private theorem lagSol_down {c f t : ℝ} (h : c ≤ f) : lagSol c f t = f + (c - f) * lagM0 tauDown t := by
  rw [lagSol_eq, lagTau, ite_eq_right (not_lt.2 h)]

theorem lagM0_tauDown_le {t : ℝ} (ht : 0 ≤ t) : lagM0 tauDown t ≤ lagM0 tauUp t := by
  unfold lagM0
  have : -t / tauUp ≤ -t / tauDown := div_tauUp_le (by linarith)
  have := Real.exp_le_exp.2 this
  linarith

/-- The end value is monotone in the command. -/
theorem lagSol_mono_cmd {c c' : ℝ} (f : ℝ) (hcc : c ≤ c') {t : ℝ} (ht : 0 ≤ t) :
    lagSol c f t ≤ lagSol c' f t := by
  have hu := lagM0_nonneg tauUp_pos ht
  have hd := lagM0_nonneg tauDown_pos ht
  have hud := lagM0_tauDown_le ht
  rcases lt_or_ge f c with h1 | h1
  · rw [lagSol_up h1, lagSol_up (lt_of_lt_of_le h1 hcc)]; nlinarith
  · rcases lt_or_ge f c' with h2 | h2
    · rw [lagSol_down h1, lagSol_up h2]; nlinarith
    · rw [lagSol_down h1, lagSol_down h2]; nlinarith

/-- One-sided slope bound: `lagSol c' f t - lagSol c f t ≤ (c' - c)(1 - e^{-t/tauUp})` for `c ≤ c'`. -/
private theorem lagSol_sub_cmd_le {c c' : ℝ} (f : ℝ) (hcc : c ≤ c') {t : ℝ} (ht : 0 ≤ t) :
    lagSol c' f t - lagSol c f t ≤ (c' - c) * lagM0 tauUp t := by
  have hu := lagM0_nonneg tauUp_pos ht
  have hd := lagM0_nonneg tauDown_pos ht
  have hud := lagM0_tauDown_le ht
  rcases lt_or_ge f c with h1 | h1
  · rw [lagSol_up h1, lagSol_up (lt_of_lt_of_le h1 hcc)]; nlinarith
  · rcases lt_or_ge f c' with h2 | h2
    · rw [lagSol_down h1, lagSol_up h2]; nlinarith
    · rw [lagSol_down h1, lagSol_down h2]; nlinarith

/-- **Command sensitivity of the lag, sharp**: `|lagSol c f t - lagSol c' f t| ≤ (1 - e^{-t/tauUp}) |c - c'|`,
with equality when both commands are above `f`. -/
theorem abs_lagSol_sub_cmd_le (c c' f : ℝ) {t : ℝ} (ht : 0 ≤ t) :
    |lagSol c f t - lagSol c' f t| ≤ lagM0 tauUp t * |c - c'| := by
  rcases le_total c c' with h | h
  · have h1 := lagSol_sub_cmd_le f h ht
    have h2 := lagSol_mono_cmd f h ht
    rw [abs_sub_comm, abs_of_nonneg (by linarith), abs_sub_comm, abs_of_nonneg (by linarith)]
    linarith
  · have h1 := lagSol_sub_cmd_le f h ht
    have h2 := lagSol_mono_cmd f h ht
    rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]
    linarith

/-- The equality case: both commands above the start value. -/
theorem lagSol_sub_cmd_eq {c c' f t : ℝ} (hc : f < c) (hc' : f < c') :
    lagSol c f t - lagSol c' f t = lagM0 tauUp t * (c - c') := by
  rw [lagSol_up hc, lagSol_up hc']; ring

/-- One-sided slope bound in the start value. -/
private theorem lagSol_sub_init_le {f f' : ℝ} (c : ℝ) (hff : f ≤ f') {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ lagSol c f' t - lagSol c f t ∧
      lagSol c f' t - lagSol c f t ≤ (f' - f) * Real.exp (-t / tauDown) := by
  have hu : Real.exp (-t / tauUp) ≤ Real.exp (-t / tauDown) := Real.exp_le_exp.2 (div_tauUp_le (by linarith))
  have hu0 := Real.exp_pos (-t / tauUp)
  have hd1 : Real.exp (-t / tauDown) ≤ 1 :=
    Real.exp_le_one_iff.2 (div_nonpos_of_nonpos_of_nonneg (by linarith) tauDown_pos.le)
  have hu1 : Real.exp (-t / tauUp) ≤ 1 :=
    Real.exp_le_one_iff.2 (div_nonpos_of_nonpos_of_nonneg (by linarith) tauUp_pos.le)
  simp only [lagSol, lagTau]
  by_cases h1 : c > f'
  · have h2 : c > f := lt_of_le_of_lt hff h1
    rw [ite_eq_left h1, ite_eq_left h2]; constructor <;> nlinarith
  · by_cases h2 : c > f
    · rw [ite_eq_right h1, ite_eq_left h2]; push Not at h1; constructor <;> nlinarith
    · rw [ite_eq_right h1, ite_eq_right h2]; push Not at h1 h2; constructor <;> nlinarith

/-- **Start-value sensitivity of the lag, sharp**: `|lagSol c f t - lagSol c f' t| ≤ e^{-t/tauDown} |f - f'|`, with
equality when both start values are at or above the command. -/
theorem abs_lagSol_sub_init_le (c f f' : ℝ) {t : ℝ} (ht : 0 ≤ t) :
    |lagSol c f t - lagSol c f' t| ≤ Real.exp (-t / tauDown) * |f - f'| := by
  rcases le_total f f' with h | h
  · obtain ⟨h1, h2⟩ := lagSol_sub_init_le c h ht
    rw [abs_sub_comm, abs_of_nonneg h1, abs_sub_comm, abs_of_nonneg (by linarith)]; linarith
  · obtain ⟨h1, h2⟩ := lagSol_sub_init_le c h ht
    rw [abs_of_nonneg h1, abs_of_nonneg (by linarith)]; linarith

/-- **Joint sensitivity of the lag**: in the command and the start value. -/
theorem abs_lagSol_sub_le (c c' f f' : ℝ) {t : ℝ} (ht : 0 ≤ t) :
    |lagSol c f t - lagSol c' f' t| ≤ lagM0 tauUp t * |c - c'| + Real.exp (-t / tauDown) * |f - f'| := by
  calc |lagSol c f t - lagSol c' f' t|
      = |(lagSol c f t - lagSol c' f t) + (lagSol c' f t - lagSol c' f' t)| := by ring_nf
    _ ≤ |lagSol c f t - lagSol c' f t| + |lagSol c' f t - lagSol c' f' t| := abs_add_le _ _
    _ ≤ _ := add_le_add (abs_lagSol_sub_cmd_le c c' f ht) (abs_lagSol_sub_init_le c' f f' ht)

/-! ## Integrals of the exact flow -/

/-- `∫₀ᵗ lagSol c f`: `f t + (c - f) lagM1 τ t`. -/
def lagK1 (c f t : ℝ) : ℝ := f * t + (c - f) * lagM1 (lagTau c f) t

/-- `∫₀ᵗ s · lagSol c f s ds`: `f t²/2 + (c - f)(t lagM1 τ t - lagM2 τ t)`. -/
def lagK2 (c f t : ℝ) : ℝ :=
  f * t ^ 2 / 2 + (c - f) * (t * lagM1 (lagTau c f) t - lagM2 (lagTau c f) t)

/-- `∫₀ᵗ lagK1`: `f t²/2 + (c - f) lagM2 τ t`. -/
def lagK3 (c f t : ℝ) : ℝ := f * t ^ 2 / 2 + (c - f) * lagM2 (lagTau c f) t

/-- `∫₀ᵗ lagK2`: `f t³/6 + (c - f)(t lagM2 τ t - 2 lagM3 τ t)`. -/
def lagK4 (c f t : ℝ) : ℝ :=
  f * t ^ 3 / 6 + (c - f) * (t * lagM2 (lagTau c f) t - 2 * lagM3 (lagTau c f) t)

theorem hasDerivAt_lagK1 (c f t : ℝ) : HasDerivAt (lagK1 c f) (lagSol c f t) t := by
  have hτ := (lagTau_pos c f).ne'
  refine (((hasDerivAt_id t).const_mul f).add ((hasDerivAt_lagM1 hτ t).const_mul (c - f))).congr_deriv ?_
  rw [lagSol_eq]; simp

theorem hasDerivAt_lagK2 (c f t : ℝ) : HasDerivAt (lagK2 c f) (t * lagSol c f t) t := by
  have hτ := (lagTau_pos c f).ne'
  refine ((((hasDerivAt_pow 2 t).const_mul f).div_const 2).add
    ((((hasDerivAt_id t).mul (hasDerivAt_lagM1 hτ t)).sub (hasDerivAt_lagM2 t)).const_mul (c - f))).congr_deriv ?_
  rw [lagSol_eq]; simp; ring

theorem hasDerivAt_lagK3 (c f t : ℝ) : HasDerivAt (lagK3 c f) (lagK1 c f t) t := by
  refine ((((hasDerivAt_pow 2 t).const_mul f).div_const 2).add
    ((hasDerivAt_lagM2 t).const_mul (c - f))).congr_deriv ?_
  simp [lagK1]; ring

theorem hasDerivAt_lagK4 (c f t : ℝ) : HasDerivAt (lagK4 c f) (lagK2 c f t) t := by
  refine ((((hasDerivAt_pow 3 t).const_mul f).div_const 6).add
    ((((hasDerivAt_id t).mul (hasDerivAt_lagM2 t)).sub
      ((hasDerivAt_lagM3 t).const_mul 2)).const_mul (c - f))).congr_deriv ?_
  simp [lagK2]; ring

theorem lagK1_zero (c f : ℝ) : lagK1 c f 0 = 0 := by simp [lagK1, lagM1_zero]
theorem lagK2_zero (c f : ℝ) : lagK2 c f 0 = 0 := by simp [lagK2, lagM2_zero]
theorem lagK3_zero (c f : ℝ) : lagK3 c f 0 = 0 := by simp [lagK3, lagM2_zero]
theorem lagK4_zero (c f : ℝ) : lagK4 c f 0 = 0 := by simp [lagK4, lagM3_zero]

/-- Two functions with equal derivatives that agree at `0` agree everywhere. -/
private theorem eq_of_hasDerivAt {F G F' : ℝ → ℝ} (hF : ∀ t, HasDerivAt F (F' t) t)
    (hG : ∀ t, HasDerivAt G (F' t) t) (h0 : F 0 = G 0) (t : ℝ) : F t = G t := by
  have hd : ∀ s, HasDerivAt (fun s => F s - G s) 0 s := fun s => ((hF s).sub (hG s)).congr_deriv (sub_self _)
  have := is_const_of_deriv_eq_zero (f := fun s => F s - G s) (fun s => (hd s).differentiableAt)
    (fun s => (hd s).deriv) t 0
  simp only [h0, sub_self] at this
  linarith

/-- **The integral of the lag is additive over consecutive intervals.** -/
theorem lagK1_add (c f s t : ℝ) :
    lagK1 c f (s + t) = lagK1 c f s + lagK1 c (lagSol c f s) t := by
  refine eq_of_hasDerivAt (F := fun t => lagK1 c f (s + t)) (G := fun t => lagK1 c f s + lagK1 c (lagSol c f s) t)
    (F' := fun t => lagSol c f (s + t)) (fun t => ?_) (fun t => ?_) (by simp [lagK1_zero]) t
  · exact (hasDerivAt_lagK1 c f (s + t)).comp_const_add s t
  · refine ((hasDerivAt_lagK1 c (lagSol c f s) t).const_add _).congr_deriv ?_
    rw [lagSol_add]

/-- The second integral over consecutive intervals. -/
theorem lagK3_add (c f s t : ℝ) :
    lagK3 c f (s + t) = lagK3 c f s + t * lagK1 c f s + lagK3 c (lagSol c f s) t := by
  refine eq_of_hasDerivAt (F := fun t => lagK3 c f (s + t))
    (G := fun t => lagK3 c f s + t * lagK1 c f s + lagK3 c (lagSol c f s) t)
    (F' := fun t => lagK1 c f (s + t)) (fun t => ?_) (fun t => ?_) (by simp [lagK3_zero]) t
  · exact (hasDerivAt_lagK3 c f (s + t)).comp_const_add s t
  · refine ((((hasDerivAt_id t).mul_const (lagK1 c f s)).const_add _).add
      (hasDerivAt_lagK3 c (lagSol c f s) t)).congr_deriv ?_
    rw [lagK1_add c f s t]; simp

end

end Plant
