import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Contracts.Plant.Constants

/-!
# The vertical channel as a real linear system (milestone M5, discrete-time part)

TRACK_PLAN.md 3.3 splits the linear regime of the closed loop into channels. This file is the
vertical channel `V`: its eight states, the matrices `Av`, `Bv` read off the translated code, the
change of coordinates from the code's variables to the tracking error, and the generic tools the
certificates use (trajectories of `x (k+1) = A x k + u k`, quadratic forms, the Young inequality,
the one-step ISS inequality and the discrete comparison lemma). The certificate itself (the
Lyapunov matrix `Pv`, `λv`, the `L D Lᵀ` factorizations) is `VerticalCert.lean`; the computed
responses are `VerticalData.lean` and `VerticalClimb.lean`. `VERTICAL.md` records the derivation,
the validation against `sim/out/lean-course-1ms/flight.csv` and the interface to the controller
lemmas (C-series).

## The tick, in the order of `Vehicle.tick` (TRACK_PLAN.md 3.1)

All quantities are deviations from hover trim (`thr = 1/2.25`, level, zero error). At tick `k` the
controller reads the sample `s_k` of the plant state `x_k` and of the actuators `held_k` of the
period that ended at `k`, and the navigator's target `(sp_k, vsp_k, asp_k)` (down position,
velocity, acceleration, `AC_PosControl._pos_target/_vel_desired/_accel_desired`). In code order:

1. `motors.output` (`AP_MotorsMulticopter::update_throttle_filter`): the 2 Hz throttle filter runs
   on the `_throttle_in` that tick `k-1` set: `f ← f + αT (u - f)`; the actuators of the period
   `[k, k+1]` are `act = f` (mixer with zero roll/pitch/yaw input, linear thrust curve);
2. `D_update_controller`: `AC_P_1D::update_all` (linear branch of the sqrt controller,
   `PSC_D_POS_P = 1`): `vt = kpPos (sp - z) + vsp`; `AC_PID_Basic::update_all` (`PSC_D_VEL_P = 5`,
   `I = D = FF = 0`, 5 Hz error filter): `eV ← eV + αV ((vt - vz) - eV)`, `at = kpVel eV + asp`;
   `AC_PID::update_all` (`PSC_D_ACC_P = 0.05`, `I = 0.1`, `D = FF = 0`, `FLTT = 0`, 20 Hz error
   filter): `eA ← eA + αA ((at - am) - eA)` with the measured acceleration
   `am = accel_ef.z + g = -amax · held`, `I ← I + ki dt eA`;
   `thrust_d_norm = kpAcc eA + I - hover` and `set_throttle_out(-thrust_d_norm)`: `u ← -(kpAcc eA + I)`;
3. the plant (exact vertical double integrator at hover, linearized thrust `-amax · act`,
   `amax = thrust2weight · g`): `z ← z + h vz + h²/2 acc`, `vz ← vz + h acc`, `held ← act`.

The one-tick delays are the states `u` (`_throttle_in` read by the next `motors.output`) and `w`
(`held`, read by the next sample's specific force); `f` and `w` coincide after one tick, and `u`
is a function of `(eA, I)` after one tick, so `Av` has two zero eigenvalues.

## Constants

The controller gains and filter coefficients are the exact values of the `Float32` numbers the
code computes (`calc_lowpass_alpha_dt (2500 · 1e-6f) fc` and the parameters of
`sim/params/copter-cf2x*.txt`, MissionData), written as fractions; the plant constants are those of
`Contracts/Plant/Constants.lean` (`per_eq`, `amax_eq`). The real law in the C-lemmas uses these
coefficients, so its `β` is pure rounding.
-/

namespace Contracts.Track.Vertical

open Matrix Finset

/-! ## Constants (exact rationals) -/

/-- Sample period `h = 1/400 s` (`Contracts.Plant.h`). -/
def per : ℚ := 1 / 400
/-- Gravity, m/s² (`Contracts.Plant.grav`). -/
def grav : ℚ := 196133 / 20000
/-- Thrust-to-weight ratio (`Contracts.Plant.thrust2weight`). -/
def tw : ℚ := 9 / 4
/-- Maximum vertical acceleration of the thrust, `thrust2weight · g` (`Contracts.Plant.amax`). -/
def amax : ℚ := tw * grav
/-- `calc_lowpass_alpha_dt(0.0025f, 5)` (`PSC_D_VEL_FLTE 5`), the float32 value `0x3D9523D2`. -/
def αV : ℚ := 4886901 / 67108864
/-- `calc_lowpass_alpha_dt(0.0025f, 20)` (`PSC_D_ACC_FLTE 20`), the float32 value `0x3E74CA9B`. -/
def αA : ℚ := 16042859 / 67108864
/-- `calc_lowpass_alpha_dt(0.0025f, 2)` (the `set_throttle_out(…, 2.0)` cutoff), `0x3CF98637`. -/
def αT : ℚ := 16352567 / 536870912
/-- `PSC_D_POS_P = 1`. -/
def kpPos : ℚ := 1
/-- `PSC_D_VEL_P = 5`. -/
def kpVel : ℚ := 5
/-- `PSC_D_ACC_P = 0.05f`. -/
def kpAcc : ℚ := 13421773 / 268435456
/-- `PSC_D_ACC_I · dt = 0.1f · 0.0025f` (exact product of the two float32 values). -/
def kiDt : ℚ := 72057593501057 / 288230376151711744

theorem per_eq : (per : ℝ) = Contracts.Plant.h := by
  simp [per, Contracts.Plant.h]

theorem amax_eq : (amax : ℝ) = Contracts.Plant.amax := by
  simp [amax, tw, grav, Contracts.Plant.amax, Contracts.Plant.thrust2weight, Contracts.Plant.grav]
  norm_num

/-! ## The matrices, row by row in code order -/

/-- Actuator (throttle filter after `update_throttle_filter`) as a row: `f + αT (u - f)`. -/
def rowAct : Fin 8 → ℚ := ![0, 0, 0, 0, 0, 1 - αT, αT, 0]
/-- New velocity error filter `eV + αV ((-kpPos ez - ev) - eV)`. -/
def rowEV : Fin 8 → ℚ := ![-(αV * kpPos), -αV, 1 - αV, 0, 0, 0, 0, 0]
/-- New acceleration error filter `eA + αA ((kpVel eV' + amax w) - eA)` (without the `asp` term). -/
def rowEA : Fin 8 → ℚ := fun j => αA * kpVel * rowEV j + ![0, 0, 0, 1 - αA, 0, 0, 0, αA * amax] j
/-- New integrator `I + kiDt eA'`. -/
def rowI : Fin 8 → ℚ := fun j => kiDt * rowEA j + ![0, 0, 0, 0, 1, 0, 0, 0] j
/-- New `_throttle_in` deviation `-(kpAcc eA' + I')`. -/
def rowU : Fin 8 → ℚ := fun j => -(kpAcc * rowEA j + rowI j)
/-- New position error `ez + h ev + h²/2 (-amax act)`. -/
def rowEz : Fin 8 → ℚ := fun j => ![1, per, 0, 0, 0, 0, 0, 0] j + per ^ 2 / 2 * (-amax) * rowAct j
/-- New velocity error `ev + h (-amax act)`. -/
def rowEv : Fin 8 → ℚ := fun j => ![0, 1, 0, 0, 0, 0, 0, 0] j + per * (-amax) * rowAct j

/-- `A_v`: state `(ez, ev, eV, eA, I, f, u, w)`. -/
def Av : Matrix (Fin 8) (Fin 8) ℚ := Matrix.of ![rowEz, rowEv, rowEV, rowEA, rowI, rowAct, rowU, rowAct]

/-- `B_v`: the input `asp` (target acceleration, down) enters as feedforward and as the reference's
own acceleration in the error kinematics. -/
def Bv : Fin 8 → ℚ :=
  ![-(per ^ 2 / 2), -per, 0, αA, kiDt * αA, 0, -(kpAcc * αA + kiDt * αA), 0]

/-- Real versions. -/
noncomputable def AvR : Matrix (Fin 8) (Fin 8) ℝ := Av.map (fun q : ℚ => (q : ℝ))
noncomputable def BvR : Fin 8 → ℝ := fun i => (Bv i : ℝ)
/-- Unit vectors of `ez` and `ev` (directions of the reference defects). -/
noncomputable def e0 : Fin 8 → ℝ := Pi.single 0 1
noncomputable def e1 : Fin 8 → ℝ := Pi.single 1 1

/-! ## The tick in error coordinates -/

/-- One tick of the vertical channel in error coordinates `(ez, ev, eV, eA, I, f, u, w)` with
target acceleration `a` and reference defects `d₁, d₂` (`d = 0` for a reference that is an exact
double integrator of `a` over the tick). Each `let` is one statement of the code (module doc). -/
noncomputable def tick (x : Fin 8 → ℝ) (a d₁ d₂ : ℝ) : Fin 8 → ℝ :=
  let act : ℝ := x 5 + (αT : ℝ) * (x 6 - x 5)
  let eV' : ℝ := x 2 + (αV : ℝ) * ((-((kpPos : ℝ) * x 0) - x 1) - x 2)
  let eA' : ℝ := x 3 + (αA : ℝ) * (((kpVel : ℝ) * eV' + a) - (-((amax : ℝ) * x 7)) - x 3)
  let I' : ℝ := x 4 + (kiDt : ℝ) * eA'
  let u' : ℝ := -((kpAcc : ℝ) * eA' + I')
  let acc : ℝ := -((amax : ℝ) * act)
  ![x 0 + (per : ℝ) * x 1 + (per : ℝ) ^ 2 / 2 * (acc - a) - d₁,
    x 1 + (per : ℝ) * (acc - a) - d₂, eV', eA', I', act, u', act]

/-- **The tick is the linear system `(A_v, B_v)`.** -/
theorem tick_eq (x : Fin 8 → ℝ) (a d₁ d₂ : ℝ) :
    tick x a d₁ d₂ = AvR *ᵥ x + (a • BvR - d₁ • e0 - d₂ • e1) := by
  ext i
  fin_cases i <;>
    simp [tick, AvR, BvR, Av, Bv, rowEz, rowEv, rowEV, rowEA, rowI, rowU, rowAct, e0, e1,
      mulVec, dotProduct, Fin.sum_univ_eight] <;>
    ring

/-! ## The code's variables and the change of coordinates -/

/-- The vertical channel in the code's variables (deviations from trim): plant `z`, `vz` (down),
`_pid_vel_d_m._error`, `_pid_accel_d_m._error`, `_pid_accel_d_m._integrator`,
`_throttle_filter`, `_throttle_in` (motors), `held` (mean actuator of the last period). -/
structure VAbs where
  z : ℝ
  vz : ℝ
  eV : ℝ
  eA : ℝ
  I : ℝ
  f : ℝ
  u : ℝ
  w : ℝ

/-- One tick of the code's variables with target `(sp, vsp, asp)` (module doc, items 1–3). -/
noncomputable def absTick (s : VAbs) (sp vsp asp : ℝ) : VAbs :=
  let act : ℝ := s.f + (αT : ℝ) * (s.u - s.f)
  let vt : ℝ := (kpPos : ℝ) * (sp - s.z) + vsp
  let eV' : ℝ := s.eV + (αV : ℝ) * ((vt - s.vz) - s.eV)
  let atgt : ℝ := (kpVel : ℝ) * eV' + asp
  let am : ℝ := -((amax : ℝ) * s.w)
  let eA' : ℝ := s.eA + (αA : ℝ) * ((atgt - am) - s.eA)
  let I' : ℝ := s.I + (kiDt : ℝ) * eA'
  let u' : ℝ := -((kpAcc : ℝ) * eA' + I')
  let acc : ℝ := -((amax : ℝ) * act)
  { z := s.z + (per : ℝ) * s.vz + (per : ℝ) ^ 2 / 2 * acc, vz := s.vz + (per : ℝ) * acc,
    eV := eV', eA := eA', I := I', f := act, u := u', w := act }

/-- Error coordinates against the target `(sp, vsp)`. -/
def errOf (s : VAbs) (sp vsp : ℝ) : Fin 8 → ℝ := ![s.z - sp, s.vz - vsp, s.eV, s.eA, s.I, s.f, s.u, s.w]

/-- The reference defects of a target sequence over one tick. -/
noncomputable def defect₁ (sp sp' vsp asp : ℝ) : ℝ := sp' - sp - (per : ℝ) * vsp - (per : ℝ) ^ 2 / 2 * asp
noncomputable def defect₂ (vsp vsp' asp : ℝ) : ℝ := vsp' - vsp - (per : ℝ) * asp

/-- **Change of coordinates**: the code's tick, read in error coordinates, is `tick` driven by the
target acceleration and the defects of the target sequence. -/
theorem errOf_absTick (s : VAbs) (sp vsp asp sp' vsp' : ℝ) :
    errOf (absTick s sp vsp asp) sp' vsp' =
      tick (errOf s sp vsp) asp (defect₁ sp sp' vsp asp) (defect₂ vsp vsp' asp) := by
  ext i
  fin_cases i <;>
    simp [errOf, absTick, tick, defect₁, defect₂, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;>
    ring

/-! ## Trajectories of `x (k+1) = A x k + u k` -/

section Traj

variable {n : ℕ}

/-- The trajectory of `x (k+1) = A x k + u k` from `x 0 = x₀`. -/
noncomputable def traj (A : Matrix (Fin n) (Fin n) ℝ) (x₀ : Fin n → ℝ) (u : ℕ → Fin n → ℝ) :
    ℕ → Fin n → ℝ
  | 0 => x₀
  | k + 1 => A *ᵥ traj A x₀ u k + u k

@[simp] theorem traj_zero (A : Matrix (Fin n) (Fin n) ℝ) (x₀ u) : traj A x₀ u 0 = x₀ := rfl

theorem traj_succ (A : Matrix (Fin n) (Fin n) ℝ) (x₀ u) (k : ℕ) :
    traj A x₀ u (k + 1) = A *ᵥ traj A x₀ u k + u k := rfl

theorem traj_add (A : Matrix (Fin n) (Fin n) ℝ) (x₀ y₀ : Fin n → ℝ) (u v : ℕ → Fin n → ℝ) (k : ℕ) :
    traj A (x₀ + y₀) (fun j => u j + v j) k = traj A x₀ u k + traj A y₀ v k := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [traj_succ, ih, mulVec_add]; abel

theorem traj_smul (A : Matrix (Fin n) (Fin n) ℝ) (c : ℝ) (x₀ : Fin n → ℝ) (u : ℕ → Fin n → ℝ)
    (k : ℕ) : traj A (c • x₀) (fun j => c • u j) k = c • traj A x₀ u k := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [traj_succ, ih, mulVec_smul, smul_add]

theorem traj_zero_input (A : Matrix (Fin n) (Fin n) ℝ) (k : ℕ) :
    traj A 0 (fun _ => 0) k = 0 := by
  induction k with
  | zero => rfl
  | succ k ih => simp [traj_succ, ih]

/-- Delaying the input by `J` ticks (from rest) delays the trajectory by `J` ticks. -/
theorem traj_shift (A : Matrix (Fin n) (Fin n) ℝ) (u : ℕ → Fin n → ℝ) (J k : ℕ) :
    traj A 0 (fun j => if J ≤ j then u (j - J) else 0) k =
      if J ≤ k then traj A 0 u (k - J) else 0 := by
  induction k with
  | zero =>
    by_cases hJ : J = 0
    · subst hJ; simp
    · simp [Nat.pos_of_ne_zero hJ, Nat.not_le.mpr]
  | succ k ih =>
    rw [traj_succ, ih]
    by_cases hk : J ≤ k
    · have hk' : J ≤ k + 1 := by omega
      simp only [hk, hk', ite_true]
      rw [show k + 1 - J = (k - J) + 1 by omega, traj_succ]
    · by_cases hk1 : J = k + 1
      · subst hk1; simp
      · have : ¬ J ≤ k + 1 := by omega
        simp [hk, this]

/-- The trajectory from rest is the convolution of the input with the powers of `A`. -/
theorem traj_eq_sum (A : Matrix (Fin n) (Fin n) ℝ) (u : ℕ → Fin n → ℝ) (k : ℕ) :
    traj A 0 u k = ∑ j ∈ range k, (A ^ (k - 1 - j)) *ᵥ u j := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [traj_succ, ih, sum_range_succ, mulVec_sum]
    congr 1
    · refine sum_congr rfl fun j hj => ?_
      have hj := mem_range.mp hj
      rw [mulVec_mulVec, ← pow_succ']
      congr 2; omega
    · simp

/-- Two trajectories of the same matrix: their difference is the trajectory of the difference. -/
theorem traj_sub (A : Matrix (Fin n) (Fin n) ℝ) (x₀ y₀ : Fin n → ℝ) (u v : ℕ → Fin n → ℝ) (k : ℕ) :
    traj A x₀ u k - traj A y₀ v k = traj A (x₀ - y₀) (fun j => u j - v j) k := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [traj_succ, ← ih, mulVec_sub]; abel

end Traj

/-! ## Quadratic forms -/

section Quad

variable {n : ℕ}

/-- The quadratic form `xᵀ P x`. -/
noncomputable def qf (P : Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ) : ℝ := x ⬝ᵥ (P *ᵥ x)

/-- A matrix given as `L · diag d · Lᵀ` with `d ≥ 0` has a nonnegative quadratic form. -/
theorem qf_nonneg_of_ldl (P L : Matrix (Fin n) (Fin n) ℝ) (d : Fin n → ℝ) (hd : ∀ i, 0 ≤ d i)
    (hP : P = L * diagonal d * Lᵀ) (x : Fin n → ℝ) : 0 ≤ qf P x := by
  have hD : (diagonal d).PosSemidef := PosSemidef.diagonal (fun i => hd i)
  have h := hD.mul_mul_conjTranspose_same L
  rw [conjTranspose_eq_transpose_of_trivial] at h
  have := h.dotProduct_mulVec_nonneg x
  simpa [qf, hP] using this

theorem qf_mulVec (P A : Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ) :
    qf P (A *ᵥ x) = qf (Aᵀ * P * A) x := by
  simp only [qf]
  rw [← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec x Aᵀ, vecMul_transpose]

theorem qf_smul_sub (c : ℝ) (P Q : Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ) :
    qf (c • P - Q) x = c * qf P x - qf Q x := by
  simp [qf, sub_mulVec, smul_mulVec, dotProduct_sub, dotProduct_smul]

theorem qf_smul_vec (P : Matrix (Fin n) (Fin n) ℝ) (c : ℝ) (x : Fin n → ℝ) :
    qf P (c • x) = c ^ 2 * qf P x := by
  simp [qf, mulVec_smul, dotProduct_smul, smul_dotProduct]; ring

/-- The bilinear form of a symmetric matrix is symmetric. -/
theorem bf_symm (P : Matrix (Fin n) (Fin n) ℝ) (hP : Pᵀ = P) (x y : Fin n → ℝ) :
    y ⬝ᵥ (P *ᵥ x) = x ⬝ᵥ (P *ᵥ y) := by
  rw [dotProduct_mulVec, ← mulVec_transpose, hP, dotProduct_comm]

theorem qf_add (P : Matrix (Fin n) (Fin n) ℝ) (hP : Pᵀ = P) (x y : Fin n → ℝ) :
    qf P (x + y) = qf P x + 2 * (x ⬝ᵥ (P *ᵥ y)) + qf P y := by
  simp only [qf, mulVec_add, add_dotProduct, dotProduct_add]
  rw [bf_symm P hP y x]; ring

theorem qf_sub (P : Matrix (Fin n) (Fin n) ℝ) (hP : Pᵀ = P) (x y : Fin n → ℝ) :
    qf P (x - y) = qf P x - 2 * (x ⬝ᵥ (P *ᵥ y)) + qf P y := by
  simp only [qf, mulVec_sub, sub_dotProduct, dotProduct_sub]
  rw [bf_symm P hP y x]; ring

/-- **Young's inequality** for a positive semidefinite symmetric form. -/
theorem qf_add_le (P : Matrix (Fin n) (Fin n) ℝ) (hP : Pᵀ = P) (hpsd : ∀ z, 0 ≤ qf P z)
    {η : ℝ} (hη : 0 < η) (x y : Fin n → ℝ) :
    qf P (x + y) ≤ (1 + η) * qf P x + (1 + 1 / η) * qf P y := by
  have h0 := hpsd (η • x - y)
  rw [qf_sub P hP, qf_smul_vec, smul_dotProduct, smul_eq_mul] at h0
  rw [qf_add P hP]
  set b := x ⬝ᵥ (P *ᵥ y)
  have key : 2 * b ≤ η * qf P x + qf P y / η := by
    rw [div_eq_mul_inv]
    have hη' : 0 < η⁻¹ := inv_pos.mpr hη
    have : 0 ≤ η⁻¹ * (η ^ 2 * qf P x - 2 * (η * b) + qf P y) := mul_nonneg hη'.le (by linarith)
    have e : η⁻¹ * (η ^ 2 * qf P x - 2 * (η * b) + qf P y) =
        η * qf P x - 2 * b + qf P y * η⁻¹ := by field_simp
    linarith
  have : (1 + 1 / η) * qf P y = qf P y + qf P y / η := by ring
  nlinarith

/-- **One ISS step**: if `qf P (A x) ≤ μ² qf P x` then `qf P (A x + w) ≤ μ qf P x + qf P w / (1 - μ)`. -/
theorem qf_iss_step (P A : Matrix (Fin n) (Fin n) ℝ) (hP : Pᵀ = P) (hpsd : ∀ z, 0 ≤ qf P z)
    {μ : ℝ} (hμ0 : 0 < μ) (hμ1 : μ < 1) (hA : ∀ z, qf P (A *ᵥ z) ≤ μ ^ 2 * qf P z)
    (x w : Fin n → ℝ) : qf P (A *ᵥ x + w) ≤ μ * qf P x + qf P w / (1 - μ) := by
  have hη : 0 < (1 - μ) / μ := div_pos (by linarith) hμ0
  have h1 := qf_add_le P hP hpsd hη (A *ᵥ x) w
  have e1 : 1 + (1 - μ) / μ = 1 / μ := by field_simp; ring
  have e2 : 1 + 1 / ((1 - μ) / μ) = 1 / (1 - μ) := by
    have : (1 - μ) ≠ 0 := by linarith
    field_simp; ring
  rw [e1, e2] at h1
  have h2 : 1 / μ * qf P (A *ᵥ x) ≤ 1 / μ * (μ ^ 2 * qf P x) :=
    mul_le_mul_of_nonneg_left (hA x) (by positivity)
  have e3 : 1 / μ * (μ ^ 2 * qf P x) = μ * qf P x := by field_simp
  have e4 : 1 / (1 - μ) * qf P w = qf P w / (1 - μ) := by ring
  linarith

/-- `qf P w ≤ (Σ |P i j|) ε²` when every `|w i| ≤ ε`. -/
theorem qf_le_of_abs_le (P : Matrix (Fin n) (Fin n) ℝ) {ε : ℝ} (w : Fin n → ℝ)
    (hw : ∀ i, |w i| ≤ ε) : qf P w ≤ (∑ i, ∑ j, |P i j|) * ε ^ 2 := by
  simp only [qf, dotProduct, mulVec, Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_le_sum; intro i _
  apply Finset.sum_le_sum; intro j _
  have hi := hw i
  have hj := hw j
  have hε : 0 ≤ ε := (abs_nonneg _).trans hi
  calc w i * (P i j * w j) ≤ |w i * (P i j * w j)| := le_abs_self _
    _ = |P i j| * (|w i| * |w j|) := by rw [abs_mul, abs_mul]; ring
    _ ≤ |P i j| * (ε * ε) := by gcongr
    _ = |P i j| * ε ^ 2 := by ring

end Quad

/-! ## The discrete comparison lemma -/

/-- **Discrete comparison lemma.** `V (k+1) ≤ μ V k + c k` for all `k` gives
`V n ≤ μⁿ V 0 + Σ_{k<n} μ^(n-1-k) c k`. -/
theorem comparison {V c : ℕ → ℝ} {μ : ℝ} (hμ : 0 ≤ μ) (h : ∀ k, V (k + 1) ≤ μ * V k + c k)
    (n : ℕ) : V n ≤ μ ^ n * V 0 + ∑ k ∈ range n, μ ^ (n - 1 - k) * c k := by
  induction n with
  | zero => simp
  | succ n ih =>
    calc V (n + 1) ≤ μ * V n + c n := h n
      _ ≤ μ * (μ ^ n * V 0 + ∑ k ∈ range n, μ ^ (n - 1 - k) * c k) + c n := by
          gcongr
      _ = μ ^ (n + 1) * V 0 + ∑ k ∈ range (n + 1), μ ^ (n + 1 - 1 - k) * c k := by
          rw [sum_range_succ, Nat.add_sub_cancel, Nat.sub_self, pow_zero, one_mul, mul_add,
            mul_sum, pow_succ]
          have hk : ∀ k ∈ range n, μ * (μ ^ (n - 1 - k) * c k) = μ ^ (n - k) * c k := by
            intro k hk
            have := mem_range.mp hk
            rw [← mul_assoc, ← pow_succ']
            congr 2; omega
          rw [sum_congr rfl hk]; ring

/-- With a constant bound: `V n ≤ μⁿ V 0 + c / (1 - μ)` for `0 ≤ μ < 1`, `c ≥ 0`. -/
theorem comparison_const {V : ℕ → ℝ} {μ c : ℝ} (hμ : 0 ≤ μ) (hμ1 : μ < 1) (hc : 0 ≤ c)
    (h : ∀ k, V (k + 1) ≤ μ * V k + c) (n : ℕ) : V n ≤ μ ^ n * V 0 + c / (1 - μ) := by
  have h1 := comparison (c := fun _ => c) hμ h n
  have hs : ∑ k ∈ range n, μ ^ (n - 1 - k) = ∑ k ∈ range n, μ ^ k :=
    sum_range_reflect (fun k => μ ^ k) n
  have hg : ∑ k ∈ range n, μ ^ k ≤ 1 / (1 - μ) := by
    have hm := mul_neg_geom_sum μ n
    rw [le_div_iff₀ (by linarith)]
    nlinarith [pow_nonneg hμ n]
  have h2 : ∑ k ∈ range n, μ ^ (n - 1 - k) * c ≤ c / (1 - μ) := by
    rw [← sum_mul, hs]
    calc (∑ k ∈ range n, μ ^ k) * c ≤ 1 / (1 - μ) * c := mul_le_mul_of_nonneg_right hg hc
      _ = c / (1 - μ) := by ring
  linarith

end Contracts.Track.Vertical
