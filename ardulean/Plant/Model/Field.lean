module

public import Plant.Model.Constants
public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Data.Fin.VecNotation

/-!
# State, frames, motors and the vector field of the X500

**Frames.** ArduPilot's: world NED (x north, y east, z down), body FRD (x forward, y right, z down). The simulator
works in ENU world / FLU body; the drivers convert each observation with the fixed proper rotations
`T = ENU_TO_NED = [[0,1,0],[1,0,0],[0,0,-1]]` (`sim/run_copter.py:40`) and `D = FRD_TO_FLU = diag(1,-1,-1)`
(`run_copter.py:45`): `p_ned = T p_enu`, `v_ned = T v_enu`, `R_ned_frd = T R_enu_flu D`, body rates
`ω_frd = R_ned_frdᵀ T ω_world` (`enu_state_to_ned`, `run_copter.py:66-75`), and the quaternion
`q_ned_frd = q(T) ⊗ q_pyb ⊗ q(D)` with `q(T) = (0, √½, √½, 0)`, `q(D) = (0, 1, 0, 0)`, normalized and with its sign
chosen so that `q1 ≥ 0` (`quat_ned_frd`, `run_copter.py:118-126`). The plant here is written directly in NED/FRD.

**State** (`State`, 17 reals): position `p` and velocity `v` (NED, m and m/s), the attitude quaternion
`q = (q1, q2, q3, q4)` (`q1` scalar, ArduPilot's order), body to NED, the body rates `ω = (p, q, r)` (FRD, rad/s), and
the four propeller thrusts `f = (f₀, f₁, f₂, f₃)` in motor-slot order, **normalized**: `fᵢ` is the thrust of slot `i`
as a fraction of the maximum `fmax` (the simulator's `lag_thrust / fmax`, `sim/world/airframes.py:60-67`). The ODE
lives on `X = Fin 17 → ℝ` with the sup norm; the index map is `p ↦ 0,1,2`, `v ↦ 3,4,5`, `q ↦ 6,7,8,9`,
`ω ↦ 10,11,12`, `f ↦ 13,14,15,16` (`State.toX`, `State.ofX`). Normalized thrusts make the motor block free of
`fmax` and put the physical range at `[0, 1]⁴`, the range of the clipped commands.

**Motors** (`sim/run_copter.py:92-98`, `SLOT_TO_SIM = [0, 2, 3, 1]`; `sim/world/x500/x500.urdf:72, 84, 96, 108`,
propeller link positions in FLU): slot 0 front right CCW (prop 0 at FLU `(+a, -a)`), slot 1 rear left CCW (prop 2 at
`(-a, +a)`), slot 2 front left CW (prop 3 at `(+a, +a)`), slot 3 rear right CW (prop 1 at `(-a, -a)`), `a = lever`.
**Commands.** Actuator `uᵢ = (PWMᵢ - 1000)/1000` is clipped to `[0, 1]` (`sim/fly_reference.py:121-122`) and gives the
propeller speed `MAX_RPM √uᵢ` (`actuators_to_rpm`, `run_copter.py:346-353`), hence the commanded thrust
`kf · (MAX_RPM √uᵢ)² = fmax · uᵢ`, i.e. the normalized command `cᵢ = clip01 uᵢ`, held over the period.
**Lag** (`AirframeAviary._physics`, `sim/world/airframes.py:58-68`): each propeller's thrust follows its command
through a first-order lag, `ḟᵢ = (cᵢ - fᵢ) / τ(cᵢ, fᵢ)` with `τ = tauUp` when `cᵢ > fᵢ` and `tauDown` otherwise
(`lagRate`, `lagTau`). The simulator applies the exact step response of this lag once per physics substep,
`f ← f + (c - f)(1 - e^{-hPhys/τ})`, and then turns the lagged thrust back into the speed `√(f fmax / kf)` that
`BaseAviary._physics` applies; so both the force and the drag torque follow the lagged thrust.
**Forces and torques.** Propeller `i` pushes with `fmax · fᵢ` along body up (FLU `+z`, FRD `-z`), at its link
(`gpd/envs/BaseAviary.py:690-701`), and turns the body with the drag torque `km · rpm² = (km/kf) fmax fᵢ`, which enters
the FLU yaw torque as `-t0 + t1 - t2 + t3` over sim props (`BaseAviary.py:694`). The thrust in the force and torque
maps is clipped to `[0, 1]` (`force`); the clip is inactive on the physical range `[0, 1]⁴`, which the flow keeps
(`Plant.Flow.Motor`), and it makes the force and torque bounds hold on every state.

**Torques.** A force `F` along FLU `+z` at FLU `(rx, ry, rz)` has the moment `(ry F, -rx F, 0)` (the height
`rz = 0.06` of the X500's thrust points gives none). Summing over the slots and changing FLU to FRD
(`(x, y, z) ↦ (x, -y, -z)`):
* `τx = a fmax (-f₀ + f₁ + f₂ - f₃)` (left motors raise roll),
* `τy = a fmax ( f₀ - f₁ + f₂ - f₃)` (front motors raise pitch),
* `τz = km MAX_RPM² (f₀ + f₁ - f₂ - f₃)` (the CCW props' reaction turns the body clockwise seen from above, positive
  about FRD down).

**Vector field** (`field`, `vf`) for a held command vector `u` (clipped inside, so `vf` is defined for every
`u : Fin 4 → ℝ`):
* `ṗ = v`,
* `v̇ = g e_z - (T(f)/m) d(q)`, `T(f) = fmax Σ clip01 fᵢ`, with `d(q) = q ⊗ (0, e_z) ⊗ q̄` the body down axis in NED,
  `d(q) = (2(q2 q4 + q1 q3), 2(q3 q4 - q1 q2), q1² - q2² - q3² + q4²)` (`downAxis`), which is `‖q‖²` times the third
  column of the rotation matrix of `q / ‖q‖`,
* `q̇ = ½ q ⊗ (0, ω)` (`quatRate`), no normalization term,
* `ω̇ = J⁻¹ (τ(f) - ω × J ω)` with `J = diag(Jx, Jy, Jz)` (`rateAccel`),
* `ḟᵢ = lagRate (clip01 uᵢ) fᵢ`.
No drag, ground effect, downwash, rotor inertia or contact (`Physics.PYB` without wind; PyBullet's default damping is
removed, `run_copter.py:338`).
-/

@[expose] public section

namespace Plant

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

/-- A real quaternion `q1 + q2 i + q3 j + q4 k`, `q1` the scalar part (ArduPilot's `Quaternion`). -/
structure Quat where
  /-- Scalar part. -/
  q1 : ℝ
  /-- `i` component. -/
  q2 : ℝ
  /-- `j` component. -/
  q3 : ℝ
  /-- `k` component. -/
  q4 : ℝ

/-- The state: position, velocity (NED), body-to-NED attitude quaternion, body rates (FRD), and the four
normalized propeller thrusts in motor-slot order. -/
structure State where
  /-- Position, m (NED). -/
  p : Vec3
  /-- Velocity, m/s (NED). -/
  v : Vec3
  /-- Attitude, body (FRD) to world (NED). -/
  q : Quat
  /-- Body rates `(p, q, r)` about FRD, rad/s. -/
  ω : Vec3
  /-- Thrust of each motor slot as a fraction of `fmax`. -/
  f : Fin 4 → ℝ

/-- The state space of the ODE: 17 reals with the sup norm. -/
abbrev X : Type := Fin 17 → ℝ

/-- The thrust block `(x 13, x 14, x 15, x 16)` of flat coordinates. -/
def thr (x : X) : Fin 4 → ℝ := ![x 13, x 14, x 15, x 16]

/-- The flat coordinates of a state. -/
def State.toX (s : State) : X :=
  ![s.p.x, s.p.y, s.p.z, s.v.x, s.v.y, s.v.z, s.q.q1, s.q.q2, s.q.q3, s.q.q4, s.ω.x, s.ω.y, s.ω.z,
    s.f 0, s.f 1, s.f 2, s.f 3]

/-- The named view of flat coordinates. -/
def State.ofX (x : X) : State :=
  ⟨⟨x 0, x 1, x 2⟩, ⟨x 3, x 4, x 5⟩, ⟨x 6, x 7, x 8, x 9⟩, ⟨x 10, x 11, x 12⟩, thr x⟩

/-- `ofX` undoes `toX`. -/
@[simp] theorem State.ofX_toX (s : State) : State.ofX s.toX = s := by
  rcases s with ⟨⟨_, _, _⟩, ⟨_, _, _⟩, ⟨_, _, _, _⟩, ⟨_, _, _⟩, f⟩
  unfold State.ofX
  congr 1
  funext i; fin_cases i <;> rfl

/-- `toX` undoes `ofX`. -/
@[simp] theorem State.toX_ofX (x : X) : (State.ofX x).toX = x := by
  funext i; fin_cases i <;> rfl

/-! ## Commands, the motor lag, forces and torques -/

/-- Saturation to `[0, 1]`. -/
def clip01 (u : ℝ) : ℝ := max 0 (min 1 u)

theorem clip01_nonneg (u : ℝ) : 0 ≤ clip01 u := le_max_left _ _
theorem clip01_le_one (u : ℝ) : clip01 u ≤ 1 := max_le zero_le_one (min_le_left _ _)
theorem clip01_of_mem {u : ℝ} (h0 : 0 ≤ u) (h1 : u ≤ 1) : clip01 u = u := by
  rw [clip01, min_eq_right h1, max_eq_right h0]

/-- The time constant of the lag of a propeller with normalized command `c` and thrust `f`: `tauUp` when the
command is above the thrust, `tauDown` otherwise (`np.where(cmd > self.lag_thrust, up, down)`,
`sim/world/airframes.py:65`). -/
def lagTau (c f : ℝ) : ℝ := if c > f then tauUp else tauDown

/-- **The motor lag**: the rate of the normalized thrust `f` of a propeller under the normalized command `c`,
`(c - f) / τ(c, f)`. -/
def lagRate (c f : ℝ) : ℝ := (c - f) / lagTau c f

/-- Force of motor slot `i`, N, at the normalized thrusts `f`: `fmax · fᵢ`, with `fᵢ` clipped to `[0, 1]`. -/
def force (f : Fin 4 → ℝ) (i : Fin 4) : ℝ := fmax * clip01 (f i)

/-- Total thrust, N. -/
def thrust (f : Fin 4 → ℝ) : ℝ := force f 0 + force f 1 + force f 2 + force f 3

/-- Thrust acceleration `T / m`, m/s². -/
def accel (f : Fin 4 → ℝ) : ℝ := thrust f / mass

/-- Roll torque about FRD x, N m. -/
def torqueX (f : Fin 4 → ℝ) : ℝ := lever * (-force f 0 + force f 1 + force f 2 - force f 3)

/-- Pitch torque about FRD y, N m. -/
def torqueY (f : Fin 4 → ℝ) : ℝ := lever * (force f 0 - force f 1 + force f 2 - force f 3)

/-- Yaw torque about FRD z, N m: `km · MAX_RPM² · (f₀ + f₁ - f₂ - f₃)` (each propeller's `km · rpm²` with
`rpm² = MAX_RPM² · fᵢ`). -/
def torqueZ (f : Fin 4 → ℝ) : ℝ :=
  km * maxRPM ^ 2 * (clip01 (f 0) + clip01 (f 1) - clip01 (f 2) - clip01 (f 3))

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

/-- The body down axis `q ⊗ (0, e_z) ⊗ q̄` in NED; the third column of the rotation matrix of a unit `q`. -/
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

/-- The body torque vector (FRD) of the normalized thrusts `f`. -/
def torque (f : Fin 4 → ℝ) : Vec3 := ⟨torqueX f, torqueY f, torqueZ f⟩

/-- Earth-frame specific force `-(T/m) d(q)` (NED) at the thrusts `f`: the acceleration minus gravity. -/
def specForce (q : Quat) (f : Fin 4 → ℝ) : Vec3 :=
  let d := downAxis q
  ⟨-(accel f) * d.x, -(accel f) * d.y, -(accel f) * d.z⟩

/-! ## The vector field -/

/-- **The vector field** on the named state, for held commands `u`. -/
def field (s : State) (u : Fin 4 → ℝ) : State :=
  let a := specForce s.q s.f
  { p := s.v
    v := ⟨a.x, a.y, grav + a.z⟩
    q := quatRate s.q s.ω
    ω := rateAccel (torque s.f) s.ω
    f := fun i => lagRate (clip01 (u i)) (s.f i) }

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
theorem vf_3 : vf x u 3 = -(accel (thr x)) * (2 * (x 7 * x 9 + x 6 * x 8)) := rfl
theorem vf_4 : vf x u 4 = -(accel (thr x)) * (2 * (x 8 * x 9 - x 6 * x 7)) := rfl
theorem vf_5 : vf x u 5 = grav + -(accel (thr x)) * (x 6 * x 6 - x 7 * x 7 - x 8 * x 8 + x 9 * x 9) :=
  rfl
theorem vf_6 : vf x u 6 = (x 6 * 0 - x 7 * x 10 - x 8 * x 11 - x 9 * x 12) / 2 := rfl
theorem vf_7 : vf x u 7 = (x 6 * x 10 + x 7 * 0 + x 8 * x 12 - x 9 * x 11) / 2 := rfl
theorem vf_8 : vf x u 8 = (x 6 * x 11 - x 7 * x 12 + x 8 * 0 + x 9 * x 10) / 2 := rfl
theorem vf_9 : vf x u 9 = (x 6 * x 12 + x 7 * x 11 - x 8 * x 10 + x 9 * 0) / 2 := rfl
theorem vf_10 : vf x u 10 = (torqueX (thr x) - (x 11 * (Jz * x 12) - x 12 * (Jy * x 11))) / Jx := rfl
theorem vf_11 : vf x u 11 = (torqueY (thr x) - (x 12 * (Jx * x 10) - x 10 * (Jz * x 12))) / Jy := rfl
theorem vf_12 : vf x u 12 = (torqueZ (thr x) - (x 10 * (Jy * x 11) - x 11 * (Jx * x 10))) / Jz := rfl
theorem vf_13 : vf x u 13 = lagRate (clip01 (u 0)) (x 13) := rfl
theorem vf_14 : vf x u 14 = lagRate (clip01 (u 1)) (x 14) := rfl
theorem vf_15 : vf x u 15 = lagRate (clip01 (u 2)) (x 15) := rfl
theorem vf_16 : vf x u 16 = lagRate (clip01 (u 3)) (x 16) := rfl

end components

end

end Plant
