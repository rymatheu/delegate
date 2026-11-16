import Contracts.Mission.SubSpec
import Contracts.Track.Actuators
import Contracts.Track.Integrators
import Contracts.Quick.Order
import Contracts.Track.VerticalSCurve
import Contracts.Track.HorizontalCourse

/-!
# M9, part 1: the run of the closed loop and its channel coordinates

Everything the induction of `track_contract` reads off one behavior `x` of `Mloop`:

* `run w₀ x t`: the controller's world before tick `t` (the takeover of `w₀` at tick 0, then
  `Vehicle.tick`). `hidden_run` proves that it is the hidden state of every witness of
  `x ∈ Mctrl w₀` (the witness is unique), and that the output of tick `t` is read from it (`outW`).
* the target triples per axis (`refAx`: position target, velocity target, acceleration target
  after the tick), the commanded horizontal acceleration (`cmd`), the realized mean acceleration
  over a period (`aReal`), the attitude-lag state (`aLag`) and its deviation (`etaA`);
* the code's variables of the vertical channel (`vabs`, VERTICAL.md §1) and of each horizontal
  axis (`habs`, HORIZONTAL.md §1), and the error coordinates `ξV`, `ξH`;
* the generic tube lemma `tube_out`: the output of `η (t₀ + n)` for `η' = A η + w` is bounded by
  peak gains on the initial state plus ℓ1 gains on a componentwise bound of `w`.

The vertical integrator is read against its trim `hover - 1/2.25` (the hover throttle of the
world's motors, as `CtrlV.vstate`).
-/

namespace Contracts.Track.Induction

open Contracts Contracts.STL Contracts.Mission Matrix Finset

noncomputable section

/-! ## The hidden run -/

/-- The controller's world before tick `t`: the takeover of `w₀` on the first sample, then one
`Vehicle.tick` per sample. -/
def run (w₀ : Vehicle.World) (x : ℕ → Mission.X) : ℕ → Vehicle.World
  | 0 => Vehicle.takeover w₀ (x 0).smp
  | t + 1 => (Vehicle.tick (run w₀ x t) (x t).smp).1

/-- `run` is the specification's `Mission.ctrlWorld` (the same recursion). -/
theorem run_eq_ctrlWorld (w₀ : Vehicle.World) (x : ℕ → Mission.X) (t : ℕ) :
    run w₀ x t = ctrlWorld w₀ x t := by
  induction t with
  | zero => rfl
  | succ t ih => simp only [run, ctrlWorld, ih]

/-- What `tickT` writes, from the result of `Vehicle.tick`. -/
def outW (r : Vehicle.World × Array Float32) : CtrlOut :=
  { act := actVec r.2, posTarget := AC_PosControl_lib.AC_PosControl.get_pos_desired_NED_m r.1.ps,
    velTarget := AC_PosControl_lib.AC_PosControl.get_vel_desired_NED_ms r.1.ps }

theorem tickT_some (w₀ w : Vehicle.World) (smp : Vehicle.Sample) :
    tickT w₀ (some w) smp = (some (Vehicle.tick w smp).1, outW (Vehicle.tick w smp)) := rfl

theorem tickT_none (w₀ : Vehicle.World) (smp : Vehicle.Sample) :
    tickT w₀ none smp =
      (some (Vehicle.tick (Vehicle.takeover w₀ smp) smp).1,
        outW (Vehicle.tick (Vehicle.takeover w₀ smp) smp)) := rfl

/-- **The hidden state is the run.** For every witness `s` of `x ∈ Mctrl w₀`, the state after tick
`t` is `run w₀ x (t + 1)`, and the output of tick `t` is computed from `run w₀ x t`. -/
theorem hidden_run {w₀ : Vehicle.World} {x : ℕ → Mission.X} {s : ℕ → Option Vehicle.World}
    (hs0 : s 0 = none) (hs : ∀ t, (s (t + 1), (x t).out) = tickT w₀ (s t) (x t).smp) :
    ∀ t, s (t + 1) = some (run w₀ x (t + 1)) ∧
      (x t).out = outW (Vehicle.tick (run w₀ x t) (x t).smp) := by
  intro t
  induction t with
  | zero =>
    have h := hs 0
    rw [hs0, tickT_none, Prod.mk.injEq] at h
    exact ⟨h.1, h.2⟩
  | succ t ih =>
    have h := hs (t + 1)
    rw [ih.1, tickT_some, Prod.mk.injEq] at h
    exact ⟨h.1, h.2⟩

theorem out_run {w₀ : Vehicle.World} {x : ℕ → Mission.X} (hx : x ∈ Mctrl w₀) (t : ℕ) :
    (x t).out = outW (Vehicle.tick (run w₀ x t) (x t).smp) := by
  obtain ⟨s, hs0, hs⟩ := mem_Mctrl.1 hx
  exact (hidden_run hs0 hs t).2

/-- The position target after tick `t` is the world's `_pos_desired_ned_m` after the tick. -/
theorem posTarget_run {w₀ : Vehicle.World} {x : ℕ → Mission.X} (hx : x ∈ Mctrl w₀) (t : ℕ) :
    (x t).out.posTarget = (run w₀ x (t + 1)).ps._pos_desired_ned_m := by
  rw [out_run hx t]; rfl

theorem velTarget_run {w₀ : Vehicle.World} {x : ℕ → Mission.X} (hx : x ∈ Mctrl w₀) (t : ℕ) :
    (x t).out.velTarget = (run w₀ x (t + 1)).ps._vel_desired_ned_ms := by
  rw [out_run hx t]; rfl

theorem act_run {w₀ : Vehicle.World} {x : ℕ → Mission.X} (hx : x ∈ Mctrl w₀) (t : ℕ) :
    (x t).out.act = actVec (Vehicle.tick (run w₀ x t) (x t).smp).2 := by
  rw [out_run hx t]; rfl

/-! ## Signals of a behavior -/

/-- The rigid-body coordinate `i` at tick `t`. -/
def ph (x : ℕ → Mission.X) (t : ℕ) (i : Fin 13) : ℝ := (x t).phys.x i

/-- Index of the position coordinate of axis `i` (NED). -/
def pIx (i : Fin 3) : Fin 13 := ⟨i.val, by omega⟩

/-- Index of the velocity coordinate of axis `i` (NED). -/
def vIx (i : Fin 3) : Fin 13 := ⟨i.val + 3, by omega⟩

/-- The vehicle's velocity (NED, m/s). -/
def vel (x : Mission.X) : P3 := !₂[x.phys.x 3, x.phys.x 4, x.phys.x 5]

/-- The acceleration target `_accel_desired_ned_mss` after tick `t` (NED, m/s²): the navigator's
feed-forward. -/
def accDes (w₀ : Vehicle.World) (x : ℕ → Mission.X) (t : ℕ) : P3 :=
  let a := (run w₀ x (t + 1)).ps._accel_desired_ned_mss
  !₂[a.x.toReal, a.y.toReal, a.z.toReal]

/-- **The target triple of axis `i` at tick `t`**: position target, velocity target, acceleration
target, all after tick `t` (the `r k` of VERTICAL.md and HORIZONTAL.md). -/
def refAx (w₀ : Vehicle.World) (x : ℕ → Mission.X) (i : Fin 3) (t : ℕ) : ℝ × ℝ × ℝ :=
  (posTarget (x t) i, velTarget (x t) i, accDes w₀ x t i)

/-- The commanded horizontal acceleration of tick `k` on axis `a` (0 north, 1 east):
`_accel_target_ned_mss` after the tick (HORIZONTAL.md: the horizontal part of
`get_thrust_vector`). -/
def cmd (w₀ : Vehicle.World) (x : ℕ → Mission.X) (k : ℕ) (a : Fin 2) : ℝ :=
  ![(run w₀ x (k + 1)).ps._accel_target_ned_mss.x.toReal,
    (run w₀ x (k + 1)).ps._accel_target_ned_mss.y.toReal] a

/-- The command of `d` ticks before tick `t` (`0` before the first tick). -/
def cmdAgo (w₀ : Vehicle.World) (x : ℕ → Mission.X) (t d : ℕ) (a : Fin 2) : ℝ :=
  if d ≤ t then cmd w₀ x (t - d) a else 0

/-- The realized mean acceleration of axis `a` over the period `[t, t + 1]`. -/
def aReal (x : ℕ → Mission.X) (t : ℕ) (a : Fin 2) : ℝ :=
  (ph x (t + 1) (vIx a.castSucc) - ph x t (vIx a.castSucc)) / Plant.h

/-- The attitude-lag state of HORIZONTAL.md §7 (the `â` of the M4 interface):
`â_{t+1} = â_t + αL (c_{t-3} - â_t)`, from `â_0 = 0` (hover at the takeover). -/
def aLag (w₀ : Vehicle.World) (x : ℕ → Mission.X) (a : Fin 2) : ℕ → ℝ
  | 0 => 0
  | t + 1 => aLag w₀ x a t + (Horizontal.αL : ℝ) * (cmdAgo w₀ x t 3 a - aLag w₀ x a t)

/-- The deviation of the realized acceleration from the lag law (the `η` of HORIZONTAL.md §7). -/
def etaA (w₀ : Vehicle.World) (x : ℕ → Mission.X) (t : ℕ) (a : Fin 2) : ℝ :=
  aReal x t a - aLag w₀ x a t

/-! ## The channel coordinates -/

/-- Hover thrust fraction `1 / thrust2weight` (the trim of the vertical model). -/
def hoverT : ℝ := 1 / Plant.thrust2weight

/-- The vertical channel in the code's variables (VERTICAL.md §1): plant `z`, `vz` (down),
`_pid_vel_d_m._error`, `_pid_accel_d_m._error`, `_pid_accel_d_m._integrator` (minus the trim
the trim `hover - hoverT`), the throttle filter's output, `_throttle_in`, and the mean held actuator, all before the
tick (the last three as deviations from `hoverT`). -/
def vabs (w₀ : Vehicle.World) (x : ℕ → Mission.X) (t : ℕ) : Vertical.VAbs :=
  let w := run w₀ x t
  { z := ph x t 2, vz := ph x t 5,
    eV := w.ps._pid_vel_d_m._error.toReal,
    eA := w.ps._pid_accel_d_m._error.toReal,
    I := w.ps._pid_accel_d_m._integrator.toReal - ((hov w).toReal - hoverT),
    f := w.ms._throttle_filter.output.toReal - hoverT,
    u := w.ms._throttle_in.toReal - hoverT,
    w := ((x t).phys.held 0 + (x t).phys.held 1 + (x t).phys.held 2 + (x t).phys.held 3) / 4 - hoverT }

/-- The vertical target triple. -/
def refV (w₀ : Vehicle.World) (x : ℕ → Mission.X) : ℕ → ℝ × ℝ × ℝ := refAx w₀ x 2

/-- **The vertical error coordinates** `(ez, ev, eV, eA, I, f, u, w)` at tick `t`. -/
def ξV (w₀ : Vehicle.World) (x : ℕ → Mission.X) (t : ℕ) : Fin 8 → ℝ :=
  Vertical.errOf (vabs w₀ x t) (refV w₀ x t).1 (refV w₀ x t).2.1

/-- One horizontal axis in the code's variables (HORIZONTAL.md §1): plant position and velocity,
`_pid_vel_ne_m`'s `_error`, `_derivative`, `_integrator` (this axis), the attitude-lag state and
the last three commands. -/
def habs (w₀ : Vehicle.World) (x : ℕ → Mission.X) (t : ℕ) (a : Fin 2) : Horizontal.HAbs :=
  let p := (run w₀ x t).ps._pid_vel_ne_m
  { p := ph x t (pIx a.castSucc), v := ph x t (vIx a.castSucc),
    E := ![p._error.x.toReal, p._error.y.toReal] a,
    D := ![p._derivative.x.toReal, p._derivative.y.toReal] a,
    I := ![p._integrator.x.toReal, p._integrator.y.toReal] a,
    a := aLag w₀ x a t,
    c₁ := cmdAgo w₀ x t 1 a, c₂ := cmdAgo w₀ x t 2 a, c₃ := cmdAgo w₀ x t 3 a }

/-- The horizontal target triple of axis `a`. -/
def refH (w₀ : Vehicle.World) (x : ℕ → Mission.X) (a : Fin 2) : ℕ → ℝ × ℝ × ℝ :=
  refAx w₀ x a.castSucc

/-- **The horizontal error coordinates** `(e, ev, E, D, I, a, c₁, c₂, c₃)` of axis `a`. -/
def ξH (w₀ : Vehicle.World) (x : ℕ → Mission.X) (t : ℕ) (a : Fin 2) : Fin 9 → ℝ :=
  Horizontal.errOf (habs w₀ x t a) (refH w₀ x a t).1 (refH w₀ x a t).2.1

/-- The direction in which an acceleration deviation enters one horizontal axis over a period
(HORIZONTAL.md §7: `w = (h²/2, h, 0, …) η`). -/
def eAcc : Fin 9 → ℝ := ![Plant.h ^ 2 / 2, Plant.h, 0, 0, 0, 0, 0, 0, 0]

theorem ξV_zero (w₀ : Vehicle.World) (x : ℕ → Mission.X) (t : ℕ) :
    ξV w₀ x t 0 = ph x t 2 - posTarget (x t) 2 := by
  simp [ξV, Vertical.errOf, vabs, refV, refAx]

theorem ξV_one (w₀ : Vehicle.World) (x : ℕ → Mission.X) (t : ℕ) :
    ξV w₀ x t 1 = ph x t 5 - velTarget (x t) 2 := by
  simp [ξV, Vertical.errOf, vabs, refV, refAx]

theorem ξH_zero (w₀ : Vehicle.World) (x : ℕ → Mission.X) (t : ℕ) (a : Fin 2) :
    ξH w₀ x t a 0 = ph x t (pIx a.castSucc) - posTarget (x t) a.castSucc := by
  simp [ξH, Horizontal.errOf, habs, refH, refAx]

theorem ξH_one (w₀ : Vehicle.World) (x : ℕ → Mission.X) (t : ℕ) (a : Fin 2) :
    ξH w₀ x t a 1 = ph x t (vIx a.castSucc) - velTarget (x t) a.castSucc := by
  simp [ξH, Horizontal.errOf, habs, refH, refAx]

/-! ## The generic tube lemma -/

section Tube

variable {n : ℕ}

/-- The response of output `o` to a unit initial state in coordinate `j` after `m` ticks. -/
def resp (A : Matrix (Fin n) (Fin n) ℝ) (o : Fin n → ℝ) (m : ℕ) (j : Fin n) : ℝ :=
  o ⬝ᵥ ((A ^ m) *ᵥ Pi.single j 1)

theorem dot_mulVec_eq (A : Matrix (Fin n) (Fin n) ℝ) (o v : Fin n → ℝ) (m : ℕ) :
    o ⬝ᵥ ((A ^ m) *ᵥ v) = ∑ j, v j * resp A o m j := by
  have hv : v = ∑ j, v j • (Pi.single j (1 : ℝ) : Fin n → ℝ) := by
    ext i; simp [Finset.sum_apply, Pi.single_apply]
  conv_lhs => rw [hv]
  rw [mulVec_sum, dotProduct_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [mulVec_smul, dotProduct_smul, smul_eq_mul, resp]

theorem abs_dot_mulVec_le (A : Matrix (Fin n) (Fin n) ℝ) (o v e : Fin n → ℝ) (m : ℕ)
    (hv : ∀ j, |v j| ≤ e j) : |o ⬝ᵥ ((A ^ m) *ᵥ v)| ≤ ∑ j, e j * |resp A o m j| := by
  rw [dot_mulVec_eq]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_right (hv j) (abs_nonneg _)

/-- The solution of `η (t + 1) = A η t + w t` from `t₀`, as the free response plus the convolution. -/
theorem eta_eq_sum (A : Matrix (Fin n) (Fin n) ℝ) (η w : ℕ → Fin n → ℝ) (t₀ : ℕ)
    (hη : ∀ t, t₀ ≤ t → η (t + 1) = A *ᵥ η t + w t) (N : ℕ) :
    η (t₀ + N) = (A ^ N) *ᵥ η t₀ + ∑ k ∈ range N, (A ^ (N - 1 - k)) *ᵥ w (t₀ + k) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [show t₀ + (N + 1) = (t₀ + N) + 1 by omega, hη _ (by omega), ih, mulVec_add, mulVec_mulVec,
      ← pow_succ', mulVec_sum, sum_range_succ, add_assoc]
    congr 1
    congr 1
    · refine Finset.sum_congr rfl fun k hk => ?_
      have hk := mem_range.mp hk
      rw [mulVec_mulVec, ← pow_succ']
      congr 2
      omega
    · simp

/-- **The tube lemma.** For `η (t + 1) = A η t + w t` from `t₀`, with `|η t₀ j| ≤ ε₀ j` and
`|w (t₀ + k) j| ≤ ε j` for `k < N`, the output `o` at `t₀ + N` is at most
`∑ⱼ P j ε₀ j + ∑ⱼ G j ε j`, where `P j` bounds the peak and `G j` the ℓ1 norm of the response of
`o` to a unit state in coordinate `j`. -/
theorem tube_out (A : Matrix (Fin n) (Fin n) ℝ) (η w : ℕ → Fin n → ℝ) (t₀ N : ℕ)
    (hη : ∀ t, t₀ ≤ t → η (t + 1) = A *ᵥ η t + w t) (o ε₀ ε P G : Fin n → ℝ)
    (hε : ∀ j, 0 ≤ ε j) (h₀ : ∀ j, |η t₀ j| ≤ ε₀ j) (hw : ∀ k < N, ∀ j, |w (t₀ + k) j| ≤ ε j)
    (hP : ∀ j m, |resp A o m j| ≤ P j) (hG : ∀ j N, ∑ m ∈ range N, |resp A o m j| ≤ G j) :
    |o ⬝ᵥ η (t₀ + N)| ≤ ∑ j, P j * ε₀ j + ∑ j, G j * ε j := by
  have hε₀ : ∀ j, 0 ≤ ε₀ j := fun j => (abs_nonneg _).trans (h₀ j)
  rw [eta_eq_sum A η w t₀ hη N, dotProduct_add, dotProduct_sum]
  refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
  · refine (abs_dot_mulVec_le A o _ ε₀ N h₀).trans (Finset.sum_le_sum fun j _ => ?_)
    rw [mul_comm]
    exact mul_le_mul_of_nonneg_right (hP j N) (hε₀ j)
  · refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ k ∈ range N, |o ⬝ᵥ ((A ^ (N - 1 - k)) *ᵥ w (t₀ + k))|
        ≤ ∑ k ∈ range N, ∑ j, ε j * |resp A o (N - 1 - k) j| :=
          Finset.sum_le_sum fun k hk => abs_dot_mulVec_le A o _ ε _ (hw k (mem_range.mp hk))
      _ = ∑ j, ε j * ∑ k ∈ range N, |resp A o (N - 1 - k) j| := by
          rw [Finset.sum_comm]; simp only [Finset.mul_sum]
      _ = ∑ j, ε j * ∑ m ∈ range N, |resp A o m j| := by
          congr 1; ext j; congr 1
          exact Finset.sum_range_reflect (fun m => |resp A o m j|) N
      _ ≤ ∑ j, G j * ε j := Finset.sum_le_sum fun j _ => by
          rw [mul_comm (G j)]; exact mul_le_mul_of_nonneg_left (hG j N) (hε j)

end Tube

end

end Contracts.Track.Induction
