module

public import Plant.Step.Sharp

/-!
# Closed-form solutions

**Pure yaw spin with the thrust transient.** From a state whose attitude is a rotation about the vertical axis only
(`q2 = q3 = 0`) with zero roll and pitch rates (`SpinState`), with thrusts in `[0, 1]⁴` that are equal within each
spin pair (`PairedThr`: slots 0 and 1 are the CCW pair, 2 and 3 the CW pair) and commands equal within each pair
(`PairedCmd`), the roll and pitch torques stay zero (the pairs lag alike) and the solution is explicit (`spinSol`):
* the thrusts are the exact lags `Lᵢ(t) = lagSol cᵢ fᵢ t`;
* the yaw rate is `r(t) = r + κ (lagK1 c₀ f₀ t - lagK1 c₂ f₂ t)`, `κ = 2 (km/kf) fmax / Jz` (the integral of the yaw
  torque of the lagged thrusts; the gyroscopic term vanishes);
* the quaternion turns about the vertical axis by `θ(t) = r t + κ (lagK3 c₀ f₀ t - lagK3 c₂ f₂ t)`;
* the thrust is vertical: the horizontal velocity is constant, and
  `v_z(t) = v_z + g t - (q1² + q4²) accK1(t)`, `p_z(t) = p_z + t v_z + g t²/2 - (q1² + q4²) accK3(t)`, with the
  integrals `accK1`, `accK3` of the lagged thrust acceleration (`Plant.Step.Sharp`).
The trajectory over the period is `spinSol` (`traj_spin`), and so is the step (`step_spin`, components
`step_spin_vz`, `step_spin_pz`, `step_spin_rate`, …).

**Level flight** is the case of zero yaw rate with all thrusts equal and all commands equal: the attitude does not
change, the motion is vertical and `v_z(h) = v_z + g h - amax lagK1 c f h` (`step_level_vz`), with
`lagK1 c f h = c h + (f - c) lagM1 τ h` the integral of the lagged thrust fraction. **Free fall** (zero thrust,
nonpositive commands): the position and velocity rows integrate exactly whatever the attitude does
(`step_freeFall`). **Hover** is the only rest equilibrium: a level state at rest with thrusts in `[0, 1]⁴` is an
equilibrium exactly when every thrust is at the hover thrust and every command at the hover command
(`vf_levelRest_eq_zero_iff`).
-/

@[expose] public section

namespace Plant

noncomputable section

open Set

/-! ## Pure yaw spin -/

/-- The state is a rotation about the vertical axis with zero roll and pitch rates. -/
def SpinState (x : X) : Prop := x 7 = 0 ∧ x 8 = 0 ∧ x 10 = 0 ∧ x 11 = 0

/-- The thrusts are equal within each spin pair (slots 0, 1 CCW; slots 2, 3 CW). -/
def PairedThr (x : X) : Prop := thr x 1 = thr x 0 ∧ thr x 3 = thr x 2

/-- The clipped commands are equal within each spin pair. -/
def PairedCmd (u : Fin 4 → ℝ) : Prop := clip01 (u 1) = clip01 (u 0) ∧ clip01 (u 3) = clip01 (u 2)

/-- The thrusts give no roll and no pitch torque. -/
def TorqueFreeXY (f : Fin 4 → ℝ) : Prop := torqueX f = 0 ∧ torqueY f = 0

/-- The yaw acceleration per unit of normalized thrust difference between the pairs: `2 (km/kf) fmax / Jz`. -/
def kappa : ℝ := 2 * kmkf * fmax / Jz

/-- The lagged thrust of slot `i` from `x` under `u`. -/
abbrev lagT (x : X) (u : Fin 4 → ℝ) (i : Fin 4) (t : ℝ) : ℝ := lagSol (clip01 (u i)) (thr x i) t

/-- The yaw angle turned by time `t`: `r t + κ (lagK3 c₀ f₀ t - lagK3 c₂ f₂ t)`. -/
def spinAngle (x : X) (u : Fin 4 → ℝ) (t : ℝ) : ℝ :=
  x 12 * t + kappa * (lagK3 (clip01 (u 0)) (thr x 0) t - lagK3 (clip01 (u 2)) (thr x 2) t)

/-- The yaw rate at time `t`. -/
def spinRate (x : X) (u : Fin 4 → ℝ) (t : ℝ) : ℝ :=
  x 12 + kappa * (lagK1 (clip01 (u 0)) (thr x 0) t - lagK1 (clip01 (u 2)) (thr x 2) t)

/-- **The closed-form spin solution.** -/
def spinSol (x : X) (u : Fin 4 → ℝ) (t : ℝ) : X :=
  ![x 0 + t * x 3, x 1 + t * x 4,
    x 2 + t * x 5 + t ^ 2 / 2 * grav - (x 6 ^ 2 + x 9 ^ 2) * accK3 x u t,
    x 3, x 4, x 5 + t * grav - (x 6 ^ 2 + x 9 ^ 2) * accK1 x u t,
    x 6 * Real.cos (spinAngle x u t / 2) - x 9 * Real.sin (spinAngle x u t / 2), 0, 0,
    x 6 * Real.sin (spinAngle x u t / 2) + x 9 * Real.cos (spinAngle x u t / 2),
    0, 0, spinRate x u t, lagT x u 0 t, lagT x u 1 t, lagT x u 2 t, lagT x u 3 t]

theorem thr_spinSol (x : X) (u : Fin 4 → ℝ) (t : ℝ) : thr (spinSol x u t) = fun i => lagT x u i t := by
  funext i; fin_cases i <;> rfl

theorem spinSol_zero {x : X} (u : Fin 4 → ℝ) (hx : SpinState x) : spinSol x u 0 = x := by
  obtain ⟨h7, h8, h10, h11⟩ := hx
  funext i
  fin_cases i <;> simp [spinSol, spinAngle, spinRate, h7, h8, h10, h11, accK1_zero, accK3_zero,
    lagK1_zero, lagK3_zero, lagSol_zero, thr_apply, fI]

section spin
variable {x : X} {u : Fin 4 → ℝ}

private theorem clip_lagT (hf : ThrustRange x) (i : Fin 4) {t : ℝ} (ht : 0 ≤ t) :
    clip01 (lagT x u i t) = lagT x u i t := by
  have := lagSol_mem ⟨clip01_nonneg (u i), clip01_le_one (u i)⟩ (hf i) ht
  exact clip01_of_mem this.1 this.2

private theorem lagT_pair (hp : PairedThr x) (hu : PairedCmd u) (t : ℝ) :
    lagT x u 1 t = lagT x u 0 t ∧ lagT x u 3 t = lagT x u 2 t := by
  exact ⟨by simp only [lagT, hp.1, hu.1], by simp only [lagT, hp.2, hu.2]⟩

theorem accel_spinSol (hf : ThrustRange x) {t : ℝ} (ht : 0 ≤ t) :
    accel (thr (spinSol x u t)) = accT x u t := by
  rw [thr_spinSol, accel_eq, clip_lagT hf 0 ht, clip_lagT hf 1 ht, clip_lagT hf 2 ht, clip_lagT hf 3 ht]
  rfl

theorem torque_spinSol (hf : ThrustRange x) (hp : PairedThr x) (hu : PairedCmd u) {t : ℝ} (ht : 0 ≤ t) :
    torqueX (thr (spinSol x u t)) = 0 ∧ torqueY (thr (spinSol x u t)) = 0 ∧
      torqueZ (thr (spinSol x u t)) / Jz = kappa * (lagT x u 0 t - lagT x u 2 t) := by
  obtain ⟨p1, p3⟩ := lagT_pair hp hu t
  simp only [thr_spinSol, torqueX, torqueY, torqueZ, force, km_maxRPM_sq, clip_lagT hf _ ht, p1, p3, kappa]
  refine ⟨by ring, by ring, ?_⟩
  field_simp [Jz_pos.ne']; ring

private theorem hasDerivAt_spinAngle (x : X) (u : Fin 4 → ℝ) (t : ℝ) :
    HasDerivAt (fun s => spinAngle x u s / 2) (spinRate x u t / 2) t := by
  refine ((((hasDerivAt_id t).const_mul (x 12)).add (((hasDerivAt_lagK3 _ _ t).sub
    (hasDerivAt_lagK3 _ _ t)).const_mul kappa)).div_const 2).congr_deriv ?_
  simp [spinRate]

/-- **The spin solution solves the ODE** on `[0, ∞)`. -/
theorem spinSol_hasDerivAt (hf : ThrustRange x) (hp : PairedThr x) (hu : PairedCmd u) {t : ℝ}
    (ht : 0 ≤ t) : HasDerivAt (spinSol x u) (vf (spinSol x u t) u) t := by
  obtain ⟨tX, tY, tZ⟩ := torque_spinSol hf hp hu ht
  have hA := accel_spinSol (u := u) hf ht
  set c := fun s => Real.cos (spinAngle x u s / 2)
  set sn := fun s => Real.sin (spinAngle x u s / 2)
  have hθ := hasDerivAt_spinAngle x u t
  have hc : HasDerivAt c (-Real.sin (spinAngle x u t / 2) * (spinRate x u t / 2)) t := by
    simpa [c] using hθ.cos
  have hs : HasDerivAt sn (Real.cos (spinAngle x u t / 2) * (spinRate x u t / 2)) t := by
    simpa [sn] using hθ.sin
  have pyth := Real.cos_sq_add_sin_sq (spinAngle x u t / 2)
  have hq : (spinSol x u t 6) ^ 2 + (spinSol x u t 9) ^ 2 = x 6 ^ 2 + x 9 ^ 2 := by
    simp only [spinSol]; simp
    linear_combination (x 6 ^ 2 + x 9 ^ 2) * pyth
  have hL : ∀ i : Fin 4, HasDerivAt (fun s => lagT x u i s) (lagRate (clip01 (u i)) (lagT x u i t)) t :=
    fun i => hasDerivAt_lagSol _ _ t
  rw [hasDerivAt_pi]
  intro i
  fin_cases i
  · exact (((hasDerivAt_id t).mul_const (x 3)).const_add (x 0)).congr_deriv (by simp [spinSol, vf_0])
  · exact (((hasDerivAt_id t).mul_const (x 4)).const_add (x 1)).congr_deriv (by simp [spinSol, vf_1])
  · refine (((((hasDerivAt_id t).mul_const (x 5)).const_add (x 2)).add
      (((hasDerivAt_pow 2 t).div_const 2).mul_const grav)).sub
      ((hasDerivAt_accK3 x u t).const_mul (x 6 ^ 2 + x 9 ^ 2))).congr_deriv ?_
    simp [spinSol, vf_2]
  · exact (hasDerivAt_const t (x 3)).congr_deriv (by
      simp only [Fin.reduceFinMk, Fin.isValue, vf_3, hA]; simp [spinSol])
  · exact (hasDerivAt_const t (x 4)).congr_deriv (by
      simp only [Fin.reduceFinMk, Fin.isValue, vf_4, hA]; simp [spinSol])
  · refine ((((hasDerivAt_id t).mul_const grav).const_add (x 5)).sub
      ((hasDerivAt_accK1 x u t).const_mul (x 6 ^ 2 + x 9 ^ 2))).congr_deriv ?_
    simp only [Fin.reduceFinMk, Fin.isValue, vf_5, hA]
    have e : spinSol x u t 6 * spinSol x u t 6 - spinSol x u t 7 * spinSol x u t 7 -
        spinSol x u t 8 * spinSol x u t 8 + spinSol x u t 9 * spinSol x u t 9 = x 6 ^ 2 + x 9 ^ 2 := by
      rw [← hq]; simp [spinSol]; ring
    rw [e]; ring
  · refine ((hc.const_mul (x 6)).sub (hs.const_mul (x 9))).congr_deriv ?_
    simp [spinSol, vf_6]; try ring
  · exact (hasDerivAt_const t (0 : ℝ)).congr_deriv (by simp [spinSol, vf_7])
  · exact (hasDerivAt_const t (0 : ℝ)).congr_deriv (by simp [spinSol, vf_8])
  · refine ((hs.const_mul (x 6)).add (hc.const_mul (x 9))).congr_deriv ?_
    simp [spinSol, vf_9]; try ring
  · refine (hasDerivAt_const t (0 : ℝ)).congr_deriv ?_
    simp only [Fin.reduceFinMk, Fin.isValue, vf_10, tX]; simp [spinSol]
  · refine (hasDerivAt_const t (0 : ℝ)).congr_deriv ?_
    simp only [Fin.reduceFinMk, Fin.isValue, vf_11, tY]; simp [spinSol]
  · refine (((((hasDerivAt_lagK1 _ _ t).sub (hasDerivAt_lagK1 _ _ t)).const_mul kappa).const_add (x 12))).congr_deriv ?_
    simp only [Fin.reduceFinMk, Fin.isValue, vf_12]
    have e : (torqueZ (thr (spinSol x u t)) - (spinSol x u t 10 * (Jy * spinSol x u t 11) -
        spinSol x u t 11 * (Jx * spinSol x u t 10))) / Jz = torqueZ (thr (spinSol x u t)) / Jz := by
      simp [spinSol]
    rw [e, tZ]
  · exact (hL 0).congr_deriv (by simp [spinSol, vf_13])
  · exact (hL 1).congr_deriv (by simp [spinSol, vf_14])
  · exact (hL 2).congr_deriv (by simp [spinSol, vf_15])
  · exact (hL 3).congr_deriv (by simp [spinSol, vf_16])

/-- **The trajectory of a spin is the closed form** on `[0, h]`. -/
theorem traj_spin (hx : SpinState x) (hf : ThrustRange x) (hp : PairedThr x) (hu : PairedCmd u) :
    ∀ t ∈ Icc 0 h, traj x u t = spinSol x u t := fun _ ht =>
  (traj_unique (spinSol_zero u hx)
    (fun _ hs => (spinSol_hasDerivAt hf hp hu hs.1).continuousAt.continuousWithinAt)
    (fun _ hs => (spinSol_hasDerivAt hf hp hu hs.1).hasDerivWithinAt) ht).symm

/-- **The step of a spin is the closed form at `h`.** -/
theorem step_spin (hx : SpinState x) (hf : ThrustRange x) (hp : PairedThr x) (hu : PairedCmd u) :
    step x u = spinSol x u h :=
  traj_spin hx hf hp hu h ⟨h_pos.le, le_rfl⟩

/-- The vertical velocity after a spin step: `v_z + g h - (q1² + q4²) accK1(h)`. -/
theorem step_spin_vz (hx : SpinState x) (hf : ThrustRange x) (hp : PairedThr x) (hu : PairedCmd u) :
    step x u 5 = x 5 + h * grav - (x 6 ^ 2 + x 9 ^ 2) * accK1 x u h := by
  rw [step_spin hx hf hp hu]; rfl

/-- The altitude after a spin step: `p_z + h v_z + g h²/2 - (q1² + q4²) accK3(h)`. -/
theorem step_spin_pz (hx : SpinState x) (hf : ThrustRange x) (hp : PairedThr x) (hu : PairedCmd u) :
    step x u 2 = x 2 + h * x 5 + h ^ 2 / 2 * grav - (x 6 ^ 2 + x 9 ^ 2) * accK3 x u h := by
  rw [step_spin hx hf hp hu]; rfl

/-- **The thrust of a spin is vertical**: the horizontal velocity is constant and the horizontal position moves
by `h v`. -/
theorem step_spin_horizontal (hx : SpinState x) (hf : ThrustRange x) (hp : PairedThr x)
    (hu : PairedCmd u) :
    step x u 0 = x 0 + h * x 3 ∧ step x u 1 = x 1 + h * x 4 ∧ step x u 3 = x 3 ∧ step x u 4 = x 4 := by
  rw [step_spin hx hf hp hu]; exact ⟨rfl, rfl, rfl, rfl⟩

/-- The yaw rate after a spin step: `r + κ (lagK1 c₀ f₀ h - lagK1 c₂ f₂ h)`. -/
theorem step_spin_rate (hx : SpinState x) (hf : ThrustRange x) (hp : PairedThr x) (hu : PairedCmd u) :
    step x u 12 = spinRate x u h := by
  rw [step_spin hx hf hp hu]; rfl

/-- **A spin stays a spin**, with paired thrusts. -/
theorem spinState_step (hx : SpinState x) (hf : ThrustRange x) (hp : PairedThr x) (hu : PairedCmd u) :
    SpinState (step x u) ∧ PairedThr (step x u) := by
  rw [step_spin hx hf hp hu, PairedThr, thr_spinSol]
  obtain ⟨p1, p3⟩ := lagT_pair hp hu h
  exact ⟨⟨rfl, rfl, rfl, rfl⟩, p1, p3⟩

end spin

/-- Paired thrusts give no roll and pitch torque. -/
theorem torqueFreeXY_of_paired {x : X} (hp : PairedThr x) : TorqueFreeXY (thr x) := by
  simp only [TorqueFreeXY, torqueX, torqueY, force, hp.1, hp.2]; constructor <;> ring

/-- Equal thrusts are free of roll and pitch torque. -/
theorem torqueFreeXY_const (c : ℝ) : TorqueFreeXY (fun _ => c) := by
  simp only [TorqueFreeXY, torqueX, torqueY, force]; constructor <;> ring

/-- Thrusts that are all nonpositive give zero thrust acceleration. -/
theorem accel_eq_zero_of_nonpos {f : Fin 4 → ℝ} (hf : ∀ i, f i ≤ 0) : accel f = 0 := by
  have hc : ∀ i, clip01 (f i) = 0 := fun i =>
    le_antisymm (max_le le_rfl ((min_le_right _ _).trans (hf i))) (clip01_nonneg _)
  rw [accel_eq, hc 0, hc 1, hc 2, hc 3]; ring

/-- Equal commands are paired. -/
theorem pairedCmd_const (c : ℝ) : PairedCmd (fun _ => c) := ⟨rfl, rfl⟩

/-! ## Level flight -/

/-- Equal thrusts: every thrust equals that of slot 0. -/
def EqualThr (x : X) : Prop := ∀ i, thr x i = thr x 0

/-- **The vertical velocity in level flight.** From a yaw-only attitude without roll and pitch rates, with equal
thrusts `f` in `[0, 1]` and a unit quaternion, equal commands `c` give the vertical velocity
`v_z + g h - amax lagK1 (clip01 c) f h`, where `lagK1 c f h = c h + (f - c) lagM1 τ h` is the integral of the lagged
thrust fraction over the period. -/
theorem step_level_vz {x : X} (hx : SpinState x) (hf : ThrustRange x) (he : EqualThr x)
    (hq : x 6 ^ 2 + x 9 ^ 2 = 1) (c : ℝ) :
    step x (fun _ => c) 5 = x 5 + h * grav - amax * lagK1 (clip01 c) (thr x 0) h := by
  have hp : PairedThr x := ⟨he 1, by rw [he 3, he 2]⟩
  rw [step_spin_vz hx hf hp (pairedCmd_const c), hq]
  simp only [accK, he 1, he 2, he 3]; ring

/-- **Level flight keeps the attitude and the rates**: the rotation and the rates are unchanged and the thrusts
are the common lag. -/
theorem step_level {x : X} (hx : SpinState x) (h12 : x 12 = 0) (hf : ThrustRange x) (he : EqualThr x)
    (c : ℝ) :
    SpinState (step x (fun _ => c)) ∧ step x (fun _ => c) 12 = 0 ∧
      step x (fun _ => c) 6 = x 6 ∧ step x (fun _ => c) 9 = x 9 ∧
      EqualThr (step x (fun _ => c)) ∧ thr (step x (fun _ => c)) 0 = lagSol (clip01 c) (thr x 0) h := by
  have hp : PairedThr x := ⟨he 1, by rw [he 3, he 2]⟩
  have hs : spinAngle x (fun _ => c) h = 0 := by simp [spinAngle, h12, he 2]
  have hr : spinRate x (fun _ => c) h = 0 := by simp [spinRate, h12, he 2]
  rw [step_spin hx hf hp (pairedCmd_const c)]
  refine ⟨⟨rfl, rfl, rfl, rfl⟩, by simp [spinSol, hr], by simp [spinSol, hs], by simp [spinSol, hs], ?_, ?_⟩
  · intro i; rw [thr_spinSol]; simp only [lagT, he i]
  · rw [thr_spinSol]

/-- **The hover command keeps the vertical velocity** in level flight at the hover thrust. -/
theorem step_level_hover_vz {x : X} (hx : SpinState x) (hf : ThrustRange x)
    (he : ∀ i, thr x i = 1 / thrust2weight) (hq : x 6 ^ 2 + x 9 ^ 2 = 1) :
    step x (fun _ => 1 / thrust2weight) 5 = x 5 := by
  rw [step_level_vz hx hf (fun i => by rw [he i, he 0]) hq, clip01_of_mem hover_mem.1 hover_mem.2, he 0]
  simp only [lagK1, sub_self, zero_mul, add_zero, amax]
  field_simp [thrust2weight_pos.ne']; ring

/-! ## Free fall -/

/-- **Free fall, the velocity rows**: with zero thrust and nonpositive commands the thrust stays zero and the
velocity gains `g t` downward on `[0, h]`, whatever the attitude does. -/
theorem traj_freeFall_v {x : X} {u : Fin 4 → ℝ} (h0 : ∀ i, thr x i = 0) (hu : ∀ i, u i ≤ 0) :
    ∀ t ∈ Icc 0 h, traj x u t 3 = x 3 ∧ traj x u t 4 = x 4 ∧ traj x u t 5 = x 5 + t * grav := by
  have hc : ∀ i, clip01 (u i) = 0 := fun i =>
    le_antisymm (max_le le_rfl ((min_le_right _ _).trans (hu i))) (clip01_nonneg _)
  have ha : ∀ s ∈ Icc 0 h, accel (thr (traj x u s)) = 0 := fun s hs => by
    have : thr (traj x u s) = fun _ => 0 := by
      funext i; rw [thr_traj x u i s hs, hc i, h0 i]; simp [lagSol]
    rw [this, accel_eq]; simp [clip01]
  have hd : ∀ j, ∀ t ∈ Icc 0 h, HasDerivAt (fun s => traj x u s j) (vf (traj x u t) u j) t :=
    fun j t ht => hasDerivAt_pi.1 (traj_hasDerivAt x u t ht) j
  have row : ∀ j : Fin 17, ∀ c : ℝ, (∀ s ∈ Icc 0 h, vf (traj x u s) u j = c) →
      ∀ t ∈ Icc 0 h, traj x u t j = x j + t * c := by
    intro j c hj t ht
    have h0' : vf x u j = c := by simpa [traj_zero] using hj 0 ⟨le_rfl, h_pos.le⟩
    have := taylor2 (f := fun s => traj x u s j) (g := fun s => vf (traj x u s) u j) (C := 0)
      (hd j) (fun s hs => by rw [hj s hs, hj 0 ⟨le_rfl, h_pos.le⟩]; simp) t ht
    simp only [zero_mul, zero_div, traj_zero, h0'] at this
    have := abs_nonpos_iff.1 this
    linarith
  intro t ht
  refine ⟨?_, ?_, ?_⟩
  · have := row 3 0 (fun s hs => by rw [vf_3, ha s hs]; ring) t ht; linarith
  · have := row 4 0 (fun s hs => by rw [vf_4, ha s hs]; ring) t ht; linarith
  · exact row 5 grav (fun s hs => by rw [vf_5, ha s hs]; ring) t ht

/-- **Free fall over one period**: with zero thrust and nonpositive commands the position and velocity rows of the
step are exact, `v ↦ v + g h e_z`, `p ↦ p + h v + (g h² / 2) e_z`, whatever the attitude does. -/
theorem step_freeFall {x : X} {u : Fin 4 → ℝ} (h0 : ∀ i, thr x i = 0) (hu : ∀ i, u i ≤ 0) :
    step x u 3 = x 3 ∧ step x u 4 = x 4 ∧ step x u 5 = x 5 + h * grav ∧
      step x u 0 = x 0 + h * x 3 ∧ step x u 1 = x 1 + h * x 4 ∧
      step x u 2 = x 2 + h * x 5 + h ^ 2 / 2 * grav := by
  have hv := traj_freeFall_v (x := x) h0 hu
  have hd : ∀ j, ∀ t ∈ Icc 0 h, HasDerivAt (fun s => traj x u s j) (vf (traj x u t) u j) t :=
    fun j t ht => hasDerivAt_pi.1 (traj_hasDerivAt x u t ht) j
  have hh : h ∈ Icc 0 h := ⟨h_pos.le, le_rfl⟩
  have prow : ∀ (j k : Fin 17) (c : ℝ), (∀ y : X, vf y u j = y k) →
      (∀ t ∈ Icc 0 h, traj x u t k = x k + t * c) → traj x u h j = x j + h * x k + h ^ 2 / 2 * c := by
    intro j k c hj hk
    have := taylor3 (f := fun s => traj x u s j) (g := fun s => vf (traj x u s) u j) (C := 0) (k := c)
      (hd j) (fun s hs => by
        rw [hj, hj, hk s hs, traj_zero]; simp) h hh
    simp only [zero_mul, zero_div, traj_zero, hj] at this
    have := abs_nonpos_iff.1 this
    linarith
  refine ⟨(hv h hh).1, (hv h hh).2.1, (hv h hh).2.2, ?_, ?_, ?_⟩
  · simpa [step] using prow 0 3 0 (fun y => vf_0 y u) (fun t ht => by simp [(hv t ht).1])
  · simpa [step] using prow 1 4 0 (fun y => vf_1 y u) (fun t ht => by simp [(hv t ht).2.1])
  · exact prow 2 5 grav (fun y => vf_2 y u) (fun t ht => by rw [(hv t ht).2.2])

/-! ## Hover is the only rest equilibrium -/

/-- A level state at rest facing north (any position, any thrusts). -/
def LevelRest (x : X) : Prop :=
  x 3 = 0 ∧ x 4 = 0 ∧ x 5 = 0 ∧ x 6 = 1 ∧ x 7 = 0 ∧ x 8 = 0 ∧ x 9 = 0 ∧ x 10 = 0 ∧ x 11 = 0 ∧ x 12 = 0

/-- **Hover is the only rest equilibrium.** A level state at rest with thrusts in `[0, 1]⁴` is an equilibrium of
`F` exactly when every thrust is at the hover thrust `1 / thrust2weight` and every command clips to it. -/
theorem vf_levelRest_eq_zero_iff {x : X} (hx : LevelRest x) (hf : ThrustRange x) (u : Fin 4 → ℝ) :
    vf x u = 0 ↔ ∀ i, thr x i = 1 / thrust2weight ∧ clip01 (u i) = 1 / thrust2weight := by
  obtain ⟨h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩ := hx
  have hc : ∀ i, clip01 (thr x i) = thr x i := fun i => clip01_of_mem (hf i).1 (hf i).2
  have ht := thrust2weight_pos
  constructor
  · intro h0
    -- the motor rows: every thrust is at its command
    have hm : ∀ i, clip01 (u i) = thr x i := fun i => by
      have := congrFun h0 (fI i)
      rw [vf_fI, Pi.zero_apply, lagRate, div_eq_zero_iff, ← thr_apply x i] at this
      rcases this with h | h
      · linarith
      · exact absurd h (lagTau_pos _ _).ne'
    -- the rate rows: no torque
    have tx := congrFun h0 10
    have ty := congrFun h0 11
    have tz := congrFun h0 12
    have vz := congrFun h0 5
    rw [vf_10, h11, h12, Pi.zero_apply, div_eq_zero_iff] at tx
    rw [vf_11, h12, h10, Pi.zero_apply, div_eq_zero_iff] at ty
    rw [vf_12, h10, h11, Pi.zero_apply, div_eq_zero_iff] at tz
    rw [vf_5, h6, h7, h8, h9, Pi.zero_apply] at vz
    simp only [mul_zero, sub_zero] at tx ty tz
    have tx' : -thr x 0 + thr x 1 + thr x 2 - thr x 3 = 0 := by
      rcases tx with h | h
      · simp only [torqueX, force, hc] at h
        have := mul_pos lever_pos fmax_pos
        nlinarith [h]
      · exact absurd h Jx_pos.ne'
    have ty' : thr x 0 - thr x 1 + thr x 2 - thr x 3 = 0 := by
      rcases ty with h | h
      · simp only [torqueY, force, hc] at h
        have := mul_pos lever_pos fmax_pos
        nlinarith [h]
      · exact absurd h Jy_pos.ne'
    have tz' : thr x 0 + thr x 1 - thr x 2 - thr x 3 = 0 := by
      rcases tz with h | h
      · rw [torqueZ, km_maxRPM_sq, hc, hc, hc, hc] at h
        have := mul_pos kmkf_pos fmax_pos
        nlinarith [h]
      · exact absurd h Jz_pos.ne'
    have hsum : thr x 0 + thr x 1 + thr x 2 + thr x 3 = 4 / thrust2weight := by
      rw [accel_eq, hc, hc, hc, hc, amax] at vz
      field_simp at vz ⊢
      nlinarith [grav_pos]
    have h4 : 4 / thrust2weight = 4 * (1 / thrust2weight) := by ring
    have e : ∀ i, thr x i = 1 / thrust2weight := by
      intro i; fin_cases i
      all_goals (simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Fin.isValue]; linarith)
    exact fun i => ⟨e i, by rw [hm i, e i]⟩
  · intro hh
    have hth : ∀ i, clip01 (thr x i) = 1 / thrust2weight := fun i => by rw [hc, (hh i).1]
    have hA : accel (thr x) = grav := accel_hover (fun i => (hh i).1)
    have tX : torqueX (thr x) = 0 := by simp only [torqueX, force, hth]; ring
    have tY : torqueY (thr x) = 0 := by simp only [torqueY, force, hth]; ring
    have tZ : torqueZ (thr x) = 0 := by simp only [torqueZ, hth]; ring
    have hm : ∀ i, vf x u (fI i) = 0 := fun i => by
      rw [vf_fI, ← thr_apply x i, (hh i).1, (hh i).2, lagRate_self]
    funext j
    fin_cases j
    any_goals first | exact hm 0 | exact hm 1 | exact hm 2 | exact hm 3
    all_goals simp only [Fin.reduceFinMk, Fin.isValue, Pi.zero_apply, vf_0, vf_1, vf_2, vf_3, vf_4, vf_5, vf_6,
      vf_7, vf_8, vf_9, vf_10, vf_11, vf_12, hA, tX, tY, tZ, h3, h4, h5, h6, h7, h8,
      h9, h10, h11, h12]
    all_goals ring

end

end Plant
