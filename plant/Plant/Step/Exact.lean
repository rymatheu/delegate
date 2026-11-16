module

public import Plant.Flow.Flow
public import Plant.Field.Actuators

/-!
# Closed-form solutions

**Pure yaw spin.** From a state whose attitude is a rotation about the vertical axis only
(`q2 = q3 = 0`) and whose roll and pitch rates are zero (`SpinState`), under commands with zero roll
and pitch torque (`TorqueFreeXY`), the solution is explicit (`spinSol`):
* the yaw rate grows linearly, `r(t) = r + t τz / Jz` (the gyroscopic term vanishes);
* the quaternion turns about the vertical axis by the angle `θ(t) = r t + (τz / Jz) t² / 2`:
  `(q1, q4)(t) = (q1 cos θ/2 - q4 sin θ/2, q1 sin θ/2 + q4 cos θ/2)`, `q2 = q3 = 0`;
* the thrust is vertical: the horizontal velocity is constant, and the vertical acceleration is
  `az = g - (T/m)(q1² + q4²)` (`= g - T/m` for a unit quaternion).
The trajectory over the period is `spinSol` (`traj_spin`), and so is the step (`step_spin`), with
the components written out (`step_spin_vz`, `step_spin_pz`, `step_spin_rate`, …).

**Level flight** is the case of zero yaw rate and equal commands: the attitude does not change and
the motion is purely vertical (`step_level`, `step_level_vz`). **Free fall** (zero thrust): the
position and velocity rows integrate exactly whatever the attitude does (`step_freeFall`).

Everything here is structural (no CF2X number).
-/

@[expose] public section

namespace Plant

noncomputable section

open Set

/-! ## Pure yaw spin -/

/-- The state is a rotation about the vertical axis with zero roll and pitch rates. -/
def SpinState (x : X) : Prop := x 7 = 0 ∧ x 8 = 0 ∧ x 10 = 0 ∧ x 11 = 0

/-- The commands give no roll and no pitch torque. -/
def TorqueFreeXY (u : Fin 4 → ℝ) : Prop := torqueX u = 0 ∧ torqueY u = 0

/-- The vertical acceleration of a spin: `g - (T/m)(q1² + q4²)`. -/
def spinAz (x : X) (u : Fin 4 → ℝ) : ℝ := grav - accel u * (x 6 ^ 2 + x 9 ^ 2)

/-- The yaw angle turned by time `t`: `r t + (τz / Jz) t² / 2`. -/
def spinAngle (x : X) (u : Fin 4 → ℝ) (t : ℝ) : ℝ := x 12 * t + torqueZ u / Jz * t ^ 2 / 2

/-- **The closed-form spin solution.** -/
def spinSol (x : X) (u : Fin 4 → ℝ) (t : ℝ) : X :=
  ![x 0 + t * x 3, x 1 + t * x 4, x 2 + t * x 5 + t ^ 2 / 2 * spinAz x u,
    x 3, x 4, x 5 + t * spinAz x u,
    x 6 * Real.cos (spinAngle x u t / 2) - x 9 * Real.sin (spinAngle x u t / 2), 0, 0,
    x 6 * Real.sin (spinAngle x u t / 2) + x 9 * Real.cos (spinAngle x u t / 2),
    0, 0, x 12 + t * (torqueZ u / Jz)]

theorem spinSol_zero {x : X} (u : Fin 4 → ℝ) (hx : SpinState x) : spinSol x u 0 = x := by
  obtain ⟨h7, h8, h10, h11⟩ := hx
  funext i
  fin_cases i <;> simp [spinSol, spinAngle, h7, h8, h10, h11]

private theorem hasDerivAt_spinAngle (x : X) (u : Fin 4 → ℝ) (t : ℝ) :
    HasDerivAt (fun s => spinAngle x u s / 2) ((x 12 + t * (torqueZ u / Jz)) / 2) t := by
  have := (((hasDerivAt_id t).const_mul (x 12)).add
    (((hasDerivAt_pow 2 t).const_mul (torqueZ u / Jz)).div_const 2)).div_const 2
  convert this using 1
  · funext s; simp [spinAngle]
  · simp; ring

/-- **The spin solution solves the ODE.** -/
theorem spinSol_hasDerivAt {x : X} {u : Fin 4 → ℝ} (hu : TorqueFreeXY u) (t : ℝ) :
    HasDerivAt (spinSol x u) (vf (spinSol x u t) u) t := by
  obtain ⟨hX, hY⟩ := hu
  set c := fun s => Real.cos (spinAngle x u s / 2)
  set sn := fun s => Real.sin (spinAngle x u s / 2)
  have hθ := hasDerivAt_spinAngle x u t
  have hc : HasDerivAt c (-Real.sin (spinAngle x u t / 2) * ((x 12 + t * (torqueZ u / Jz)) / 2)) t :=
    by simpa [c] using hθ.cos
  have hs : HasDerivAt sn (Real.cos (spinAngle x u t / 2) * ((x 12 + t * (torqueZ u / Jz)) / 2)) t :=
    by simpa [sn] using hθ.sin
  have pyth := Real.cos_sq_add_sin_sq (spinAngle x u t / 2)
  rw [hasDerivAt_pi]
  intro i
  fin_cases i
  · convert ((hasDerivAt_id t).mul_const (x 3)).const_add (x 0) using 1 <;> simp [spinSol, vf, field, State.toX, State.ofX, specForce, downAxis, quatRate, Quat.mul, Quat.pure, rateAccel, torque, hX, hY, spinAz]
  · convert ((hasDerivAt_id t).mul_const (x 4)).const_add (x 1) using 1 <;> simp [spinSol, vf, field, State.toX, State.ofX, specForce, downAxis, quatRate, Quat.mul, Quat.pure, rateAccel, torque, hX, hY, spinAz]
  · convert ((((hasDerivAt_id t).mul_const (x 5)).const_add (x 2)).add
      (((hasDerivAt_pow 2 t).div_const 2).mul_const (spinAz x u))) using 1
    · funext s; simp [spinSol]
    · simp [spinSol, vf, field, State.toX, State.ofX, specForce, downAxis, quatRate, Quat.mul, Quat.pure, rateAccel, torque, hX, hY, spinAz]
  · convert hasDerivAt_const t (x 3) using 1
    · funext s; simp [spinSol]
    · simp [spinSol, vf, field, State.toX, State.ofX, specForce, downAxis, quatRate, Quat.mul, Quat.pure, rateAccel, torque, hX, hY, spinAz]
  · convert hasDerivAt_const t (x 4) using 1
    · funext s; simp [spinSol]
    · simp [spinSol, vf, field, State.toX, State.ofX, specForce, downAxis, quatRate, Quat.mul, Quat.pure, rateAccel, torque, hX, hY, spinAz]
  · convert ((hasDerivAt_id t).mul_const (spinAz x u)).const_add (x 5) using 1
    · funext s; simp [spinSol]
    · simp [spinSol, vf, field, State.toX, State.ofX, specForce, downAxis, quatRate, Quat.mul, Quat.pure, rateAccel, torque, hX, hY, spinAz]
      linear_combination (-(accel u) * (x 6 ^ 2 + x 9 ^ 2)) * pyth
  · convert (hc.const_mul (x 6)).sub (hs.const_mul (x 9)) using 1
    · funext s; simp [spinSol, c, sn]
    · simp [spinSol, vf, field, State.toX, State.ofX, specForce, downAxis, quatRate, Quat.mul, Quat.pure, rateAccel, torque, hX, hY, spinAz]; ring
  · convert hasDerivAt_const t (0 : ℝ) using 1
    · funext s; simp [spinSol]
    · simp [spinSol, vf, field, State.toX, State.ofX, specForce, downAxis, quatRate, Quat.mul, Quat.pure, rateAccel, torque, hX, hY, spinAz]
  · convert hasDerivAt_const t (0 : ℝ) using 1
    · funext s; simp [spinSol]
    · simp [spinSol, vf, field, State.toX, State.ofX, specForce, downAxis, quatRate, Quat.mul, Quat.pure, rateAccel, torque, hX, hY, spinAz]
  · convert (hs.const_mul (x 6)).add (hc.const_mul (x 9)) using 1
    · funext s; simp [spinSol, c, sn]
    · simp [spinSol, vf, field, State.toX, State.ofX, specForce, downAxis, quatRate, Quat.mul, Quat.pure, rateAccel, torque, hX, hY, spinAz]; ring
  · convert hasDerivAt_const t (0 : ℝ) using 1
    · funext s; simp [spinSol]
    · simp [spinSol, vf, field, State.toX, State.ofX, specForce, downAxis, quatRate, Quat.mul, Quat.pure, rateAccel, torque, hX, hY, spinAz]
  · convert hasDerivAt_const t (0 : ℝ) using 1
    · funext s; simp [spinSol]
    · simp [spinSol, vf, field, State.toX, State.ofX, specForce, downAxis, quatRate, Quat.mul, Quat.pure, rateAccel, torque, hX, hY, spinAz]
  · convert ((hasDerivAt_id t).mul_const (torqueZ u / Jz)).const_add (x 12) using 1
    · funext s; simp [spinSol]
    · simp [spinSol, vf, field, State.toX, State.ofX, specForce, downAxis, quatRate, Quat.mul, Quat.pure, rateAccel, torque, hX, hY, spinAz]

/-- **The trajectory of a spin is the closed form** on `[0, h]`. -/
theorem traj_spin {x : X} {u : Fin 4 → ℝ} (hx : SpinState x) (hu : TorqueFreeXY u) :
    ∀ t ∈ Icc 0 h, traj x u t = spinSol x u t := fun _ ht =>
  (traj_unique (spinSol_zero u hx)
    (fun s _ => (spinSol_hasDerivAt hu s).continuousAt.continuousWithinAt)
    (fun s _ => (spinSol_hasDerivAt hu s).hasDerivWithinAt) ht).symm

/-- **The step of a spin is the closed form at `h`.** -/
theorem step_spin {x : X} {u : Fin 4 → ℝ} (hx : SpinState x) (hu : TorqueFreeXY u) :
    step x u = spinSol x u h :=
  traj_spin hx hu h ⟨h_pos.le, le_rfl⟩


/-! ### Components of the spin step -/

section spin
variable {x : X} {u : Fin 4 → ℝ}

/-- The vertical velocity after a spin step: `v_z + h (g - (T/m)(q1² + q4²))`. -/
theorem step_spin_vz (hx : SpinState x) (hu : TorqueFreeXY u) :
    step x u 5 = x 5 + h * spinAz x u := by
  rw [step_spin hx hu]; simp [spinSol]

/-- The altitude after a spin step: `p_z + h v_z + (h² / 2) az`. -/
theorem step_spin_pz (hx : SpinState x) (hu : TorqueFreeXY u) :
    step x u 2 = x 2 + h * x 5 + h ^ 2 / 2 * spinAz x u := by
  rw [step_spin hx hu]; simp [spinSol]

/-- **The thrust of a spin is vertical**: the horizontal velocity is constant and the horizontal
position moves by `h v`. -/
theorem step_spin_horizontal (hx : SpinState x) (hu : TorqueFreeXY u) :
    step x u 0 = x 0 + h * x 3 ∧ step x u 1 = x 1 + h * x 4 ∧ step x u 3 = x 3 ∧
      step x u 4 = x 4 := by
  rw [step_spin hx hu]; simp [spinSol]

/-- The yaw rate after a spin step: `r + h τz / Jz`. -/
theorem step_spin_rate (hx : SpinState x) (hu : TorqueFreeXY u) :
    step x u 12 = x 12 + h * (torqueZ u / Jz) := by
  rw [step_spin hx hu]; simp [spinSol]

/-- **A spin stays a spin**: the step of a spin state under roll- and pitch-torque-free commands
is again a spin state. -/
theorem spinState_step (hx : SpinState x) (hu : TorqueFreeXY u) : SpinState (step x u) := by
  rw [step_spin hx hu]; simp [SpinState, spinSol]

end spin

/-- Equal commands are free of roll and pitch torque. -/
theorem torqueFreeXY_const (c : ℝ) : TorqueFreeXY (fun _ => c) :=
  ⟨(torque_const c).1, (torque_const c).2.1⟩

/-! ## Level flight -/

/-- Level flight with vertical acceleration `a`: the attitude and the rates do not change. -/
def levelSol (x : X) (a t : ℝ) : X :=
  ![x 0 + t * x 3, x 1 + t * x 4, x 2 + t * x 5 + t ^ 2 / 2 * a, x 3, x 4, x 5 + t * a,
    x 6, 0, 0, x 9, 0, 0, 0]

/-- **Level flight is purely vertical.** From a yaw-only attitude at rest in rotation, equal
commands keep the attitude and the zero rates, keep the horizontal velocity, and accelerate
vertically by `g - (T/m)(q1² + q4²)`. -/
theorem step_level {x : X} (hx : SpinState x) (h12 : x 12 = 0) (c : ℝ) :
    step x (fun _ => c) = levelSol x (spinAz x (fun _ => c)) h := by
  obtain ⟨h7, h8, h10, h11⟩ := hx
  have hz := (torque_const c).2.2
  rw [step_spin ⟨h7, h8, h10, h11⟩ (torqueFreeXY_const c)]
  funext i
  fin_cases i <;> simp [spinSol, levelSol, spinAngle, h12, hz]

/-- **The vertical velocity in level flight** with a unit quaternion and equal commands `c`:
`v_z + h (g - amax · clip01 c)`. -/
theorem step_level_vz {x : X} (hx : SpinState x) (hq : x 6 ^ 2 + x 9 ^ 2 = 1) (c : ℝ) :
    step x (fun _ => c) 5 = x 5 + h * (grav - amax * clip01 c) := by
  rw [step_spin_vz hx (torqueFreeXY_const c), spinAz, hq, accel_const, mul_one]

/-- **The hover command keeps the vertical velocity** in level flight with a unit quaternion
(and the yaw rate, if the vehicle spins). -/
theorem step_level_hover_vz {x : X} (hx : SpinState x) (hq : x 6 ^ 2 + x 9 ^ 2 = 1) :
    step x (fun _ => 1 / thrust2weight) 5 = x 5 := by
  have h1 : (1 : ℝ) / thrust2weight ≤ 1 := by norm_num [thrust2weight]
  have h0 : (0 : ℝ) ≤ 1 / thrust2weight := by norm_num [thrust2weight]
  rw [step_level_vz hx hq, ← accel_const, (accel_const_eq_grav_iff h0 h1).2 rfl]; ring

/-! ## Free fall -/

/-- Commands that are all nonpositive give zero thrust. -/
theorem accel_eq_zero_of_nonpos {u : Fin 4 → ℝ} (hu : ∀ i, u i ≤ 0) : accel u = 0 := by
  have hc : ∀ i, clip01 (u i) = 0 := fun i =>
    le_antisymm (max_le le_rfl ((min_le_right _ _).trans (hu i))) (clip01_nonneg _)
  rw [accel_eq, hc 0, hc 1, hc 2, hc 3]; ring

/-- **Free fall, the velocity rows**: under zero thrust the velocity gains `g t` downward on
`[0, h]`, whatever the attitude does. -/
theorem traj_freeFall_v {x : X} {u : Fin 4 → ℝ} (ha : accel u = 0) :
    ∀ t ∈ Icc 0 h, traj x u t 3 = x 3 ∧ traj x u t 4 = x 4 ∧ traj x u t 5 = x 5 + t * grav := by
  have hd : ∀ j, ∀ t ∈ Icc 0 h, HasDerivAt (fun s => traj x u s j) (vf (traj x u t) u j) t :=
    fun j t ht => hasDerivAt_pi.1 (traj_hasDerivAt x u t ht) j
  have row : ∀ j : Fin 13, (∀ y : X, vf y u j = vf x u j) →
      ∀ t ∈ Icc 0 h, traj x u t j = x j + t * vf x u j := by
    intro j hj t ht
    have := taylor2 (f := fun s => traj x u s j) (g := fun s => vf (traj x u s) u j) (C := 0)
      (hd j) (fun s _ => by rw [hj (traj x u s), hj (traj x u 0)]; simp) t ht
    simp only [zero_mul, zero_div, traj_zero] at this
    have := abs_nonpos_iff.1 this
    linarith
  intro t ht
  refine ⟨?_, ?_, ?_⟩
  · rw [row 3 (fun y => by simp [vf_3, ha]) t ht]; simp [vf_3, ha]
  · rw [row 4 (fun y => by simp [vf_4, ha]) t ht]; simp [vf_4, ha]
  · rw [row 5 (fun y => by simp [vf_5, ha]) t ht]; simp [vf_5, ha]

/-- **Free fall over one period**: under zero thrust the position and velocity rows of the step
are exact, `v ↦ v + g h e_z`, `p ↦ p + h v + (g h² / 2) e_z`, whatever the attitude does. -/
theorem step_freeFall {x : X} {u : Fin 4 → ℝ} (ha : accel u = 0) :
    step x u 3 = x 3 ∧ step x u 4 = x 4 ∧ step x u 5 = x 5 + h * grav ∧
      step x u 0 = x 0 + h * x 3 ∧ step x u 1 = x 1 + h * x 4 ∧
      step x u 2 = x 2 + h * x 5 + h ^ 2 / 2 * grav := by
  have hv := traj_freeFall_v (x := x) ha
  have hd : ∀ j, ∀ t ∈ Icc 0 h, HasDerivAt (fun s => traj x u s j) (vf (traj x u t) u j) t :=
    fun j t ht => hasDerivAt_pi.1 (traj_hasDerivAt x u t ht) j
  have hh : h ∈ Icc 0 h := ⟨h_pos.le, le_rfl⟩
  have prow : ∀ (j k : Fin 13) (c : ℝ), (∀ y : X, vf y u j = y k) →
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

end

end Plant
