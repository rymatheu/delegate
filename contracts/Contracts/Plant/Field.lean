module

public import Contracts.Plant.Constants
public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Data.Fin.VecNotation

/-!
# State, frames and the vector field of the rigid body

**Frames.** ArduPilot's: world NED (x north, y east, z down), body FRD (x forward, y right,
z down). The simulator works in ENU world / FLU body; `run_copter.py` converts each observation
with the fixed proper rotations `T = ENU_TO_NED = [[0,1,0],[1,0,0],[0,0,-1]]`
(`run_copter.py:40`) and `D = FRD_TO_FLU = diag(1,-1,-1)` (`run_copter.py:45`):
`p_ned = T p_enu`, `v_ned = T v_enu`, `R_ned_frd = T R_enu_flu D`, body rates
`ω_frd = R_ned_frdᵀ T ω_world` (`enu_state_to_ned`, `run_copter.py:66-75`), and the quaternion
`q_ned_frd = q(T) ⊗ q_pyb ⊗ q(D)` with `q(T) = (0, √½, √½, 0)`, `q(D) = (0, 1, 0, 0)`, normalized
and with its sign chosen so that `q1 ≥ 0` (`quat_ned_frd`, `run_copter.py:118-126`). The plant
here is written directly in NED/FRD.

**State** (`State`, 13 reals): position `p` and velocity `v` (NED, m and m/s), the attitude
quaternion `q = (q1, q2, q3, q4)` (`q1` scalar, ArduPilot's order), body to NED, and the body rates
`ω = (p, q, r)` (FRD, rad/s). The ODE lives on `X = Fin 13 → ℝ` with the sup norm; the index map
is `p ↦ 0,1,2`, `v ↦ 3,4,5`, `q ↦ 6,7,8,9`, `ω ↦ 10,11,12` (`State.toX`, `State.ofX`).

**Motors** (`run_copter.py:92-98`, `SLOT_TO_SIM = [0, 2, 3, 1]`; `assets/cf2x.urdf` link
positions in FLU): slot 0 front right CCW (sim prop 0 at FLU `(+a, -a)`), slot 1 rear left CCW
(prop 2 at `(-a, +a)`), slot 2 front left CW (prop 3 at `(+a, +a)`), slot 3 rear right CW (prop 1
at `(-a, -a)`), `a = lever = 0.028`. Actuator `uᵢ` is clipped to `[0, 1]` and gives
`rpm = MAX_RPM √uᵢ` (`actuators_to_rpm`, `run_copter.py:339-346`), hence the force
`fᵢ = kf · rpm² = fmax · uᵢ` along body up (FLU `+z`, FRD `-z`), at the motor link
(`BaseAviary._physics`, `envs/BaseAviary.py:690-699`), and the drag torque `km · rpm²`, which
enters the FLU yaw torque as `-t0 + t1 - t2 + t3` over sim props (`envs/BaseAviary.py:694`).

**Torques.** A force `f` along FLU `+z` at FLU `(rx, ry, 0)` has the moment `(ry f, -rx f, 0)`.
Summing over the slots and changing FLU to FRD (`(x, y, z) ↦ (x, -y, -z)`):
* `τx = a (-f₀ + f₁ + f₂ - f₃)` (left motors raise roll),
* `τy = a ( f₀ - f₁ + f₂ - f₃)` (front motors raise pitch),
* `τz = km MAX_RPM² (u₀ + u₁ - u₂ - u₃)` (the CCW props' reaction turns the body clockwise seen
  from above, positive about FRD down).
`BaseAviary._dynamics` (`envs/BaseAviary.py:839-848`, `CF2X`) has the same signs in FLU:
`x_torque = -(F0 + F1 - F2 - F3) L/√2`, `y_torque = (-F0 + F1 + F2 - F3) L/√2`, over sim props;
with `SLOT_TO_SIM` these are `a(-f₀ + f₁ + f₂ - f₃)` and `a(-f₀ + f₁ - f₂ + f₃)` in slots, i.e.
the FRD `τx`, `-τy` above.

**Vector field** (`field`, `vf`) for a held actuator vector `u` (clipped inside, so `vf` is defined
for every `u : Fin 4 → ℝ`):
* `ṗ = v`,
* `v̇ = g e_z - (T/m) d(q)`, `T = Σ fᵢ`, with `d(q) = q ⊗ (0, e_z) ⊗ q̄` the body down axis in NED,
  `d(q) = (2(q2 q4 + q1 q3), 2(q3 q4 - q1 q2), q1² - q2² - q3² + q4²)` (`downAxis`), which is
  `‖q‖²` times the third column of the rotation matrix of `q / ‖q‖`; for a unit quaternion it is
  the third column of `R(q)`,
* `q̇ = ½ q ⊗ (0, ω)` (`quatRate`), no normalization term,
* `ω̇ = J⁻¹ (τ - ω × J ω)` with `J = diag(Jx, Jy, Jz)` (`rateAccel`).
No drag, ground effect, downwash or motor dynamics (`Physics.PYB`, and PyBullet's default damping
is removed in `reset_env`, `run_copter.py:331`).
-/

@[expose] public section

namespace Contracts.Plant

noncomputable section

/-! ## Readable state -/

/-- A real 3-vector with named components. -/
structure Vec3 where
  /-- First component (north, or body forward). -/
  x : ℝ
  /-- Second component (east, or body right). -/
  y : ℝ
  /-- Third component (down, or body down). -/
  z : ℝ

/-- A real quaternion `q1 + q2 i + q3 j + q4 k`, `q1` the scalar part (ArduPilot's
`Quaternion`). -/
structure Quat where
  /-- Scalar part. -/
  q1 : ℝ
  /-- `i` component. -/
  q2 : ℝ
  /-- `j` component. -/
  q3 : ℝ
  /-- `k` component. -/
  q4 : ℝ

/-- The rigid-body state: position, velocity (NED), body-to-NED attitude quaternion, body rates
(FRD). -/
structure State where
  /-- Position, m (NED). -/
  p : Vec3
  /-- Velocity, m/s (NED). -/
  v : Vec3
  /-- Attitude, body (FRD) to world (NED). -/
  q : Quat
  /-- Body rates `(p, q, r)` about FRD, rad/s. -/
  ω : Vec3

/-- The state space of the ODE: 13 reals with the sup norm. -/
abbrev X : Type := Fin 13 → ℝ

/-- The flat coordinates of a state. -/
def State.toX (s : State) : X :=
  ![s.p.x, s.p.y, s.p.z, s.v.x, s.v.y, s.v.z, s.q.q1, s.q.q2, s.q.q3, s.q.q4, s.ω.x, s.ω.y, s.ω.z]

/-- The named view of flat coordinates. -/
def State.ofX (x : X) : State :=
  ⟨⟨x 0, x 1, x 2⟩, ⟨x 3, x 4, x 5⟩, ⟨x 6, x 7, x 8, x 9⟩, ⟨x 10, x 11, x 12⟩⟩

/-- `ofX` undoes `toX`. -/
@[simp] theorem State.ofX_toX (s : State) : State.ofX s.toX = s := by
  rcases s with ⟨⟨_, _, _⟩, ⟨_, _, _⟩, ⟨_, _, _, _⟩, ⟨_, _, _⟩⟩; rfl

/-- `toX` undoes `ofX`. -/
@[simp] theorem State.toX_ofX (x : X) : (State.ofX x).toX = x := by
  funext i; fin_cases i <;> rfl

/-! ## Actuators, forces and torques -/

/-- Saturation to `[0, 1]`. -/
def clip01 (u : ℝ) : ℝ := max 0 (min 1 u)

theorem clip01_nonneg (u : ℝ) : 0 ≤ clip01 u := le_max_left _ _
theorem clip01_le_one (u : ℝ) : clip01 u ≤ 1 := max_le zero_le_one (min_le_left _ _)
theorem clip01_of_mem {u : ℝ} (h0 : 0 ≤ u) (h1 : u ≤ 1) : clip01 u = u := by
  rw [clip01, min_eq_right h1, max_eq_right h0]

/-- Force of motor slot `i`, N: `kf · (MAX_RPM √uᵢ)² = fmax · uᵢ` with `uᵢ` clipped. -/
def force (u : Fin 4 → ℝ) (i : Fin 4) : ℝ := fmax * clip01 (u i)

/-- Total thrust, N. -/
def thrust (u : Fin 4 → ℝ) : ℝ := force u 0 + force u 1 + force u 2 + force u 3

/-- Thrust acceleration `T / m`, m/s². -/
def accel (u : Fin 4 → ℝ) : ℝ := thrust u / mass

/-- Roll torque about FRD x, N m. -/
def torqueX (u : Fin 4 → ℝ) : ℝ := lever * (-force u 0 + force u 1 + force u 2 - force u 3)

/-- Pitch torque about FRD y, N m. -/
def torqueY (u : Fin 4 → ℝ) : ℝ := lever * (force u 0 - force u 1 + force u 2 - force u 3)

/-- Yaw torque about FRD z, N m: `km · MAX_RPM² · (u₀ + u₁ - u₂ - u₃)`. -/
def torqueZ (u : Fin 4 → ℝ) : ℝ :=
  km * maxRPM ^ 2 * (clip01 (u 0) + clip01 (u 1) - clip01 (u 2) - clip01 (u 3))

/-! ## Rotation and kinematics -/

/-- Hamilton product `a ⊗ b` (`run_copter.py:108`, `qmul`). -/
def Quat.mul (a b : Quat) : Quat :=
  ⟨a.q1 * b.q1 - a.q2 * b.q2 - a.q3 * b.q3 - a.q4 * b.q4,
   a.q1 * b.q2 + a.q2 * b.q1 + a.q3 * b.q4 - a.q4 * b.q3,
   a.q1 * b.q3 - a.q2 * b.q4 + a.q3 * b.q1 + a.q4 * b.q2,
   a.q1 * b.q4 + a.q2 * b.q3 - a.q3 * b.q2 + a.q4 * b.q1⟩

/-- The pure quaternion `(0, w)`. -/
def Quat.pure (w : Vec3) : Quat := ⟨0, w.x, w.y, w.z⟩

/-- Squared Euclidean norm of a quaternion. -/
def Quat.normSq (q : Quat) : ℝ := q.q1 ^ 2 + q.q2 ^ 2 + q.q3 ^ 2 + q.q4 ^ 2

/-- The body down axis `q ⊗ (0, e_z) ⊗ q̄` in NED; the third column of the rotation matrix of a
unit `q`. -/
def downAxis (q : Quat) : Vec3 :=
  ⟨2 * (q.q2 * q.q4 + q.q1 * q.q3), 2 * (q.q3 * q.q4 - q.q1 * q.q2),
   q.q1 * q.q1 - q.q2 * q.q2 - q.q3 * q.q3 + q.q4 * q.q4⟩

/-- The quaternion kinematics `½ q ⊗ (0, ω)`. -/
def quatRate (q : Quat) (w : Vec3) : Quat :=
  let r := q.mul (Quat.pure w)
  ⟨r.q1 / 2, r.q2 / 2, r.q3 / 2, r.q4 / 2⟩

/-- Euler's equations for `J = diag(Jx, Jy, Jz)`: `J⁻¹ (τ - ω × J ω)`. -/
def rateAccel (τ w : Vec3) : Vec3 :=
  ⟨(τ.x - (w.y * (Jz * w.z) - w.z * (Jy * w.y))) / Jx,
   (τ.y - (w.z * (Jx * w.x) - w.x * (Jz * w.z))) / Jy,
   (τ.z - (w.x * (Jy * w.y) - w.y * (Jx * w.x))) / Jz⟩

/-- The body torque vector (FRD). -/
def torque (u : Fin 4 → ℝ) : Vec3 := ⟨torqueX u, torqueY u, torqueZ u⟩

/-- Earth-frame specific force `-(T/m) d(q)` (NED): the acceleration minus gravity. -/
def specForce (q : Quat) (u : Fin 4 → ℝ) : Vec3 :=
  let d := downAxis q
  ⟨-(accel u) * d.x, -(accel u) * d.y, -(accel u) * d.z⟩

/-! ## The vector field -/

/-- **The vector field** on the named state, for held actuators `u`. -/
def field (s : State) (u : Fin 4 → ℝ) : State :=
  let f := specForce s.q u
  { p := s.v
    v := ⟨f.x, f.y, grav + f.z⟩
    q := quatRate s.q s.ω
    ω := rateAccel (torque u) s.ω }

/-- **The vector field** on flat coordinates: `F(x, u)`. -/
def vf (x : X) (u : Fin 4 → ℝ) : X := (field (State.ofX x) u).toX

/-- The field on flat coordinates is the field on the named state. -/
theorem vf_toX (s : State) (u : Fin 4 → ℝ) : vf s.toX u = (field s u).toX := by
  simp [vf]

/-! ### Components -/

section components
variable (x : X) (u : Fin 4 → ℝ)

theorem vf_0 : vf x u 0 = x 3 := rfl
theorem vf_1 : vf x u 1 = x 4 := rfl
theorem vf_2 : vf x u 2 = x 5 := rfl
theorem vf_3 : vf x u 3 = -(accel u) * (2 * (x 7 * x 9 + x 6 * x 8)) := rfl
theorem vf_4 : vf x u 4 = -(accel u) * (2 * (x 8 * x 9 - x 6 * x 7)) := rfl
theorem vf_5 : vf x u 5 = grav + -(accel u) * (x 6 * x 6 - x 7 * x 7 - x 8 * x 8 + x 9 * x 9) :=
  rfl
theorem vf_6 : vf x u 6 = (x 6 * 0 - x 7 * x 10 - x 8 * x 11 - x 9 * x 12) / 2 := rfl
theorem vf_7 : vf x u 7 = (x 6 * x 10 + x 7 * 0 + x 8 * x 12 - x 9 * x 11) / 2 := rfl
theorem vf_8 : vf x u 8 = (x 6 * x 11 - x 7 * x 12 + x 8 * 0 + x 9 * x 10) / 2 := rfl
theorem vf_9 : vf x u 9 = (x 6 * x 12 + x 7 * x 11 - x 8 * x 10 + x 9 * 0) / 2 := rfl
theorem vf_10 : vf x u 10 = (torqueX u - (x 11 * (Jz * x 12) - x 12 * (Jy * x 11))) / Jx := rfl
theorem vf_11 : vf x u 11 = (torqueY u - (x 12 * (Jx * x 10) - x 10 * (Jz * x 12))) / Jy := rfl
theorem vf_12 : vf x u 12 = (torqueZ u - (x 10 * (Jy * x 11) - x 11 * (Jx * x 10))) / Jz := rfl

end components

end

end Contracts.Plant
