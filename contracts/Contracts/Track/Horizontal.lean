import Contracts.Track.Vertical

/-!
# The horizontal channel as a real linear system (milestone M6, discrete-time part)

TRACK_PLAN.md 3.3 splits the linear regime of the closed loop into channels. This file is the
horizontal channel `H`, one axis at a time (north and east have the same matrices: the position
controller is rotation-equivariant and the attitude loop is abstracted per axis). `HORIZONTAL.md`
records the derivation, the validation against `sim/out/lean-course-1ms/flight.csv` and the
interface the theorems need.

## The tick, in the order of `Vehicle.tick` (TRACK_PLAN.md 3.1)

At tick `k` the controller reads the sample of the plant state (position `p`, velocity `v` of one
horizontal axis) and the navigator's target `(sp, vsp, asp)`. `NE_update_controller` runs:

1. `AC_P_2D::update_all` (linear branch of the sqrt controller, `PSC_NE_POS_P = 1.5`):
   `vt = kpPos (sp - p) + vsp`;
2. `AC_PID_2D::update_all` (`PSC_NE_VEL_P = 6`, `I = 1`, `D = 0.5`, `FF = 0`, error and derivative
   filters at 5 Hz): `E ← E + αE ((vt - v) - E)`, `D ← D + αD ((E⁺ - E)/dt - D)`,
   `I ← I + ki dt E⁺` (`update_i` after the filters, so with the new error), and the output
   `kp E⁺ + I⁺ + kd D⁺`;
3. the acceleration command `c = output + asp` (`_accel_target_ned_mss`, `limit_accel_xy` inactive),
   which becomes the horizontal part of the thrust vector (`get_thrust_vector`);
4. **the attitude interface** (milestone M4, the attitude agent's contract, taken here as a
   hypothesis): the horizontal acceleration the vehicle realizes over the period `[k, k+1]` is `a`,
   a first-order lag of the command with a delay of `dL = 3` ticks,
   `a ← a + αL (c_{k-3} - a)`, `αL = 13/500` (time constant `0.095 s`). The deviation of the real
   acceleration from this law is a disturbance (the tube);
5. the plant (exact double integrator over the period): `p ← p + h v + h²/2 a`, `v ← v + h a`.

The state in error coordinates is `ξ = (e, ev, E, D, I, a, c₁, c₂, c₃)`, with `e = p - sp`,
`ev = v - vsp` and `c_j` the command of `j` ticks ago. The reference enters through its
acceleration (feedforward and the error kinematics) and through the defects `d₁, d₂` of the target
sequence (zero for an exact double integral of a piecewise-constant acceleration).

## Constants

The controller coefficients are the exact values of the `Float32` numbers the code computes:
`calc_lowpass_alpha_dt (0.0025f) 5` for both filters, `dt = 0.0025f`, and the gains of
`sim/params/copter-cf2x-tuned.txt` (all exact in binary). The attitude constants `αL` and `dL` are
the measured interface (`HORIZONTAL.md` §2); a different interface changes `Ah` and the generated
certificates (the generator is parametrized by them).
-/

namespace Contracts.Track.Horizontal

open Matrix Finset

/-! ## Constants (exact rationals) -/

/-- Sample period `h = 1/400 s` (`Contracts.Plant.h`). -/
def per : ℚ := 1 / 400
/-- `dt = 0.0025f` as the code computes it (`last_loop_time_s`), `0x3B23D70A`. -/
def dtf : ℚ := 5368709 / 2147483648
/-- `calc_lowpass_alpha_dt(0.0025f, 5)` (`PSC_NE_VEL_FLTE 5`, `PSC_NE_VEL_FLTD 5`), `0x3D9523D2`. -/
def αE : ℚ := 4886901 / 67108864
/-- `PSC_NE_POS_P = 1.5`. -/
def kpPos : ℚ := 3 / 2
/-- `PSC_NE_VEL_P = 6`. -/
def kp : ℚ := 6
/-- `PSC_NE_VEL_I = 1`. -/
def ki : ℚ := 1
/-- `PSC_NE_VEL_D = 0.5`. -/
def kd : ℚ := 1 / 2
/-- The attitude interface: lag coefficient per tick (time constant `0.095 s`). -/
def αL : ℚ := 13 / 500

theorem per_eq : (per : ℝ) = Contracts.Plant.h := by
  simp [per, Contracts.Plant.h]

/-! ## The matrices, row by row in code order -/

/-- New error filter `E + αE ((-kpPos e - ev) - E)`. -/
def rowE : Fin 9 → ℚ := ![-(αE * kpPos), -αE, 1 - αE, 0, 0, 0, 0, 0, 0]
/-- New derivative filter `D + αE ((E' - E)/dt - D)`. -/
def rowD : Fin 9 → ℚ := fun j => αE / dtf * (rowE j - ![0, 0, 1, 0, 0, 0, 0, 0, 0] j) +
  ![0, 0, 0, 1 - αE, 0, 0, 0, 0, 0] j
/-- New integrator `I + ki dt E'`. -/
def rowI : Fin 9 → ℚ := fun j => ki * dtf * rowE j + ![0, 0, 0, 0, 1, 0, 0, 0, 0] j
/-- The command without its feedforward, `kp E' + I' + kd D'`. -/
def rowC : Fin 9 → ℚ := fun j => kp * rowE j + rowI j + kd * rowD j
/-- The interface: `a + αL (c₃ - a)`. -/
def rowA : Fin 9 → ℚ := ![0, 0, 0, 0, 0, 1 - αL, 0, 0, αL]
/-- New position error `e + h ev + h²/2 a`. -/
def rowEp : Fin 9 → ℚ := ![1, per, 0, 0, 0, per ^ 2 / 2, 0, 0, 0]
/-- New velocity error `ev + h a`. -/
def rowEv : Fin 9 → ℚ := ![0, 1, 0, 0, 0, per, 0, 0, 0]

/-- `A_h`: state `(e, ev, E, D, I, a, c₁, c₂, c₃)`. -/
def Ah : Matrix (Fin 9) (Fin 9) ℚ :=
  Matrix.of ![rowEp, rowEv, rowE, rowD, rowI, rowA, rowC, ![0, 0, 0, 0, 0, 0, 1, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 1, 0]]

/-- `B_h`: the target acceleration enters the error kinematics and the command (feedforward). -/
def Bh : Fin 9 → ℚ := ![-(per ^ 2 / 2), -per, 0, 0, 0, 0, 1, 0, 0]

/-- Real versions. -/
noncomputable def AhR : Matrix (Fin 9) (Fin 9) ℝ := Ah.map (fun q : ℚ => (q : ℝ))
noncomputable def BhR : Fin 9 → ℝ := fun i => (Bh i : ℝ)
/-- Unit vectors of `e` and `ev` (directions of the reference defects). -/
noncomputable def e0 : Fin 9 → ℝ := Pi.single 0 1
noncomputable def e1 : Fin 9 → ℝ := Pi.single 1 1

/-! ## The tick in error coordinates -/

/-- One tick of one horizontal axis in error coordinates `(e, ev, E, D, I, a, c₁, c₂, c₃)` with
target acceleration `r` and reference defects `d₁, d₂`. Each `let` is one statement of the code or
of the interface (module doc). -/
noncomputable def tick (x : Fin 9 → ℝ) (r d₁ d₂ : ℝ) : Fin 9 → ℝ :=
  let E' : ℝ := x 2 + (αE : ℝ) * ((-((kpPos : ℝ) * x 0) - x 1) - x 2)
  let D' : ℝ := x 3 + (αE : ℝ) * ((E' - x 2) / (dtf : ℝ) - x 3)
  let I' : ℝ := x 4 + (ki : ℝ) * (dtf : ℝ) * E'
  let c : ℝ := (kp : ℝ) * E' + I' + (kd : ℝ) * D' + r
  let a' : ℝ := x 5 + (αL : ℝ) * (x 8 - x 5)
  ![x 0 + (per : ℝ) * x 1 + (per : ℝ) ^ 2 / 2 * (x 5 - r) - d₁,
    x 1 + (per : ℝ) * (x 5 - r) - d₂, E', D', I', a', c, x 6, x 7]

theorem dtf_ne : (dtf : ℝ) ≠ 0 := by norm_num [dtf]

/-- **The tick is the linear system `(A_h, B_h)`.** -/
theorem tick_eq (x : Fin 9 → ℝ) (r d₁ d₂ : ℝ) :
    tick x r d₁ d₂ = AhR *ᵥ x + (r • BhR - d₁ • e0 - d₂ • e1) := by
  have hd := dtf_ne
  ext i
  fin_cases i <;>
    simp [tick, AhR, BhR, Ah, Bh, rowEp, rowEv, rowE, rowD, rowI, rowC, rowA, e0, e1,
      mulVec, dotProduct, Fin.sum_univ_succ] <;>
    field_simp <;>
    ring

/-! ## The code's variables and the change of coordinates -/

/-- One horizontal axis in the code's variables: plant position and velocity, `_pid_vel_ne_m`'s
`_error`, `_derivative`, `_integrator` (this axis), the acceleration of the attitude interface and
the last three acceleration commands. -/
structure HAbs where
  p : ℝ
  v : ℝ
  E : ℝ
  D : ℝ
  I : ℝ
  a : ℝ
  c₁ : ℝ
  c₂ : ℝ
  c₃ : ℝ

/-- One tick of the code's variables with target `(sp, vsp, asp)` (module doc, items 1–5). -/
noncomputable def absTick (s : HAbs) (sp vsp asp : ℝ) : HAbs :=
  let vt : ℝ := (kpPos : ℝ) * (sp - s.p) + vsp
  let E' : ℝ := s.E + (αE : ℝ) * ((vt - s.v) - s.E)
  let D' : ℝ := s.D + (αE : ℝ) * ((E' - s.E) / (dtf : ℝ) - s.D)
  let I' : ℝ := s.I + (ki : ℝ) * (dtf : ℝ) * E'
  let c : ℝ := (kp : ℝ) * E' + I' + (kd : ℝ) * D' + asp
  { p := s.p + (per : ℝ) * s.v + (per : ℝ) ^ 2 / 2 * s.a, v := s.v + (per : ℝ) * s.a,
    E := E', D := D', I := I', a := s.a + (αL : ℝ) * (s.c₃ - s.a), c₁ := c, c₂ := s.c₁,
    c₃ := s.c₂ }

/-- Error coordinates against the target `(sp, vsp)`. -/
def errOf (s : HAbs) (sp vsp : ℝ) : Fin 9 → ℝ :=
  ![s.p - sp, s.v - vsp, s.E, s.D, s.I, s.a, s.c₁, s.c₂, s.c₃]

/-- The reference defects of a target sequence over one tick. -/
noncomputable def defect₁ (sp sp' vsp asp : ℝ) : ℝ :=
  sp' - sp - (per : ℝ) * vsp - (per : ℝ) ^ 2 / 2 * asp
noncomputable def defect₂ (vsp vsp' asp : ℝ) : ℝ := vsp' - vsp - (per : ℝ) * asp

/-- **Change of coordinates**: the code's tick, read in error coordinates, is `tick` driven by the
target acceleration and the defects of the target sequence. -/
theorem errOf_absTick (s : HAbs) (sp vsp asp sp' vsp' : ℝ) :
    errOf (absTick s sp vsp asp) sp' vsp' =
      tick (errOf s sp vsp) asp (defect₁ sp sp' vsp asp) (defect₂ vsp vsp' asp) := by
  ext i
  fin_cases i <;>
    simp [errOf, absTick, tick, defect₁, defect₂, -mul_eq_mul_left_iff,
      -mul_eq_mul_right_iff] <;>
    ring

/-- The forcing of the error coordinates by a target sequence `r k = (sp, vsp, asp)`. -/
noncomputable def forceOf (r : ℕ → ℝ × ℝ × ℝ) (k : ℕ) : Fin 9 → ℝ :=
  (r k).2.2 • BhR - defect₁ (r k).1 (r (k + 1)).1 (r k).2.1 (r k).2.2 • e0 -
    defect₂ (r k).2.1 (r (k + 1)).2.1 (r k).2.2 • e1

/-- The error response (from zero error) of one horizontal axis to a target sequence. -/
noncomputable def errResp (r : ℕ → ℝ × ℝ × ℝ) : ℕ → Fin 9 → ℝ :=
  Contracts.Track.Vertical.traj AhR 0 (forceOf r)

/-- **The error response is the code's tracking error.** If the code's variables (with the
attitude interface) evolve by `absTick` with the target sequence `r`, from a state with zero error
coordinates, then their error coordinates are `errResp r`; in particular `p k - sp k = errResp r k 0`. -/
theorem errResp_eq_code (x : ℕ → HAbs) (r : ℕ → ℝ × ℝ × ℝ)
    (hx : ∀ k, x (k + 1) = absTick (x k) (r k).1 (r k).2.1 (r k).2.2)
    (h0 : errOf (x 0) (r 0).1 (r 0).2.1 = 0) (k : ℕ) :
    errOf (x k) (r k).1 (r k).2.1 = errResp r k := by
  induction k with
  | zero => simpa [errResp] using h0
  | succ k ih =>
    rw [hx k, errOf_absTick, tick_eq, ih]
    rfl

/-- The code's tick with a disturbance: the attitude interface realizes `a + η` instead of `a`
over the period (the deviation of the real attitude loop from the lag law), and the controller
law has float errors `β` (C-series). In error coordinates this is `A_h ξ + forceOf r + w`. -/
theorem errOf_traj_dist (ξ : ℕ → Fin 9 → ℝ) (r : ℕ → ℝ × ℝ × ℝ) (w : ℕ → Fin 9 → ℝ)
    (hξ : ∀ k, ξ (k + 1) = AhR *ᵥ ξ k + forceOf r k + w k) (k : ℕ) :
    ξ k - errResp r k = Contracts.Track.Vertical.traj AhR (ξ 0) w k := by
  induction k with
  | zero => simp [errResp]
  | succ k ih =>
    rw [hξ k, Contracts.Track.Vertical.traj_succ, ← ih]
    simp only [errResp, Contracts.Track.Vertical.traj_succ, mulVec_sub]
    abel

end Contracts.Track.Horizontal
