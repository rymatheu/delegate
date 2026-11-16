module

public import Plant.Step.Euler
public import Plant.Step.Sharp
public import DynamicalSystems.Basic.NonAutonomous
-- the body of `Function.autonomousFlow` (an iterate) is needed for `sampledFlow_apply`
import all DynamicalSystems.Basic.NonAutonomous

/-!
# The sampled plant

The plant part of the archive's `Quadrotor.lean`: the plant state at a tick, the next state under
held thrust fractions, the real-valued sample of a tick, the sampled flow under constant
actuators, and hover.

**Plant state** (`PState`): the rigid-body state `x : X` at the tick and the thrust fractions
`held` applied over the period that ended at the tick. **Next state** (`nextR`):
`⟨step x u, u⟩`. **Sample** (`sampleR`): the exact real quantities the vehicle's sensing reads at
the tick: NED position and velocity, the earth-frame specific force `-(T/m) d(q)` with the held
thrust (`tickSpecForce`), the body-to-NED quaternion and the body rates, and the period `2500` µs.

Left out (they need floats or the contract library, `OPEN.md`, "for the mid level"): the float
sample `Sample` and its ports `sense32`/`senseP` with their hypotheses (`Sense32Spec`,
`SensePSpec`, `CopterSense`), the reading of `Float32` actuators `act`, the float plant `next`,
`plant`, the universe `CX` and the lifted component `Mplant` with `mem_Mplant`, `Mplant_flow`,
`Mplant_qnormSq`, `Mplant_const`, `sample_hover`. Their real content is here as statements about
runs (`IsRun`): `run_flow`, `run_qnormSq`, `run_const`, and `sampleR_hover`.
-/

@[expose] public section

namespace Plant

noncomputable section

/-! ## The sample -/

/-- The period in microseconds as the driver sends it: `1/400` s. -/
def dtUs : Nat := 2500

/-- The real-valued sample of one tick: position, velocity, earth-frame specific force, attitude,
body rates, period. -/
structure SampleR where
  /-- NED position, m. -/
  pos : Vec3
  /-- NED velocity, m/s. -/
  vel : Vec3
  /-- Earth-frame specific force, NED, m/s². -/
  accel_ef : Vec3
  /-- Body-to-NED attitude, `q1` scalar. -/
  quat : Quat
  /-- Body rates, rad/s. -/
  gyro : Vec3
  /-- Loop time in whole microseconds. -/
  dt_us : Nat

/-! ## Plant state, step and sample -/

/-- The plant state at a tick. -/
structure PState where
  /-- The rigid-body state at the tick. -/
  x : X
  /-- The thrust fractions held over the period that ended at the tick. -/
  held : Fin 4 → ℝ

/-- The next plant state at real thrust fractions `u` held over the coming period. -/
def nextR (s : PState) (u : Fin 4 → ℝ) : PState := ⟨step s.x u, u⟩

/-- The specific force at the tick: instantaneous, with the held thrust. -/
def tickSpecForce (s : PState) : Vec3 := specForce (State.ofX s.x).q s.held

/-- **The sample at a tick**, exact. -/
def sampleR (s : PState) : SampleR :=
  let st := State.ofX s.x
  { pos := st.p, vel := st.v, accel_ef := tickSpecForce s, quat := st.q, gyro := st.ω,
    dt_us := dtUs }

/-! ## Runs -/

/-- A run of the sampled plant: the plant state at each tick and the thrust fractions held over
each period, related by `nextR`. -/
def IsRun (s : ℕ → PState) (u : ℕ → Fin 4 → ℝ) : Prop := ∀ t, s (t + 1) = nextR (s t) (u t)

/-- **The rigid-body state of a run follows the exact flow**: at every tick it is the endpoint of
the solution over the period with the actuators of the previous tick held. -/
theorem run_flow {s : ℕ → PState} {u : ℕ → Fin 4 → ℝ} (hs : IsRun s u) (t : ℕ) :
    ∃ γ : ℝ → X, γ 0 = (s t).x ∧ γ h = (s (t + 1)).x ∧
      ∀ τ ∈ Set.Icc 0 h, HasDerivAt γ (vf (γ τ) (u t)) τ := by
  rw [hs t]
  exact step_spec _ _

/-- `‖q‖²` is the same at every tick of a run. -/
theorem run_qnormSq {s : ℕ → PState} {u : ℕ → Fin 4 → ℝ} (hs : IsRun s u) (t : ℕ) :
    qnormSq (s t).x = qnormSq (s 0).x := by
  induction t with
  | zero => rfl
  | succ n ih =>
    rw [hs n, ← ih]
    exact qnormSq_step _ _

/-- **The sampled plant under constant actuators** as the library's discrete flow:
`Function.autonomousFlow` of the step, `n ↦ (step · u)^[n]`. -/
def sampledFlow (u : Fin 4 → ℝ) : AutonomousFlow ℕ X := Function.autonomousFlow (fun x => step x u)

/-- The sampled flow is the `n`-th iterate of the step. -/
theorem sampledFlow_apply (u : Fin 4 → ℝ) (n : ℕ) (x : X) :
    sampledFlow u n x = (fun y => step y u)^[n] x := by
  change Function.autonomousFlow (fun y => step y u) n x = _
  rfl

/-- A run whose actuators are the constant thrust fractions `u` follows the sampled flow: the
rigid-body state at tick `n` is `sampledFlow u n` of the initial one. -/
theorem run_const {s : ℕ → PState} {u : ℕ → Fin 4 → ℝ} (hs : IsRun s u) {w : Fin 4 → ℝ}
    (hu : ∀ t, u t = w) (n : ℕ) : (s n).x = sampledFlow w n (s 0).x := by
  induction n with
  | zero => exact ((sampledFlow w).map_id _).symm
  | succ n ih =>
    rw [hs n, sampledFlow_apply, Function.iterate_succ_apply', ← sampledFlow_apply, ← ih, hu n]
    rfl

/-! ## Hover -/

/-- The plant state of hover at height `z`: level, at rest, the hover thrust held. -/
def hoverP (z : ℝ) : PState := ⟨hoverX z, fun _ => 1 / thrust2weight⟩

/-- **Hover is a fixed point of the plant** at the hover thrust fraction on every motor. -/
theorem nextR_hover (z : ℝ) {u : Fin 4 → ℝ} (hu : ∀ i, u i = 1 / thrust2weight) :
    nextR (hoverP z) u = hoverP z := by
  simp only [nextR, hoverP, step_hover z hu]
  congr 1; funext i; exact hu i

/-- The specific force of hover is `(0, 0, -g)`. -/
theorem tickSpecForce_hover (z : ℝ) : tickSpecForce (hoverP z) = ⟨0, 0, -grav⟩ := by
  have hA := accel_hover (u := fun _ => 1 / thrust2weight) (fun _ => rfl)
  simp only [tickSpecForce, specForce, downAxis, hoverP, hoverX, hoverState, State.toX, State.ofX,
    hA]
  simp

/-- **The sample of hover**: position `(0, 0, z)`, at rest, specific force `(0, 0, -g)`, level. -/
theorem sampleR_hover (z : ℝ) :
    sampleR (hoverP z) =
      { pos := ⟨0, 0, z⟩, vel := ⟨0, 0, 0⟩, accel_ef := ⟨0, 0, -grav⟩,
        quat := ⟨1, 0, 0, 0⟩, gyro := ⟨0, 0, 0⟩, dt_us := dtUs } := by
  have hf := tickSpecForce_hover z
  simp only [sampleR, hf]
  simp [hoverP, hoverX, hoverState, State.toX, State.ofX]

end

end Plant
