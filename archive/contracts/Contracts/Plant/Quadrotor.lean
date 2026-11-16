module

public import Contracts.Plant.Euler
public import Contracts.Plant.Sharp
public import Contracts.Lift
public import FloatModel.Float32
-- the body of `Function.autonomousFlow` (an iterate) is needed for `Mplant_const`
import all DynamicalSystems.Basic.NonAutonomous

/-!
# The Crazyflie 2.x as an ODE under zero-order hold, sampled at 400 Hz

The plant of the ArduCopter contracts: the rigid body that gym-pybullet-drones simulates for
`sim/run_copter.py` (`DroneModel.CF2X`, `Physics.PYB`, no drag, ground effect or downwash, PyBullet
damping removed), as the ODE `ẋ = F(x, u)` (`Field.lean`) on `X = Fin 13 → ℝ` (position, velocity,
body-to-NED quaternion, body rates; NED/FRD), with the four actuators held over each control period
`h = 1/400 s`, and its sampled flow lifted as a discrete-time component.

Files:
* `Constants.lean`: the constants with their sources, `kf_maxRPM_sq`;
* `Field.lean`: frames, motor slots, the named state `State` and flat `X`, the vector field `vf`;
* `Bounds.lean`: explicit Lipschitz and magnitude bounds (`vf_lipschitz_ball`, `norm_vf_le`);
* `Invariants.lean`: `‖q‖²` invariance, the energy estimate, the one-period box `box`;
* `Flow.lean`: truncated flow, `traj`, `step`, uniqueness, Grönwall bound, hover;
* `Euler.lean`: the step against one Euler step, the specific force against the backward
  difference;
* `Sharp.lean`: the sharp one-period step, block by block (exact integration of the `p`, `v` rows,
  Grönwall on the attitude block alone);
* this file: the outputs, the sensing ports, the plant state, the lift.

**Plant state** (`PState`): the rigid-body state `x : X` at the tick and the thrust fractions
`held` that were applied over the period ending at the tick. **Input**: the four `Float32`
actuators, read exactly and clipped (`act`). **Next state** (`next`): `⟨step x (act a), act a⟩`.
**Output** (`sample`), the `Copter.AHRS.Sample` of the tick: NED position through the `postype`
(`double`) port `senseP`; NED velocity, earth-frame specific force, body-to-NED quaternion
`(q1, q2, q3, q4)` and body rates through the `float` port `sense32`; the period `2500` µs.
The specific force is the model's instantaneous `-(T/m) d(q)` at the tick, with the thrust of the
held actuators (`specForce`). The output depends on the state only, never on the actuators of the
same tick, as in the driver (`fly`, `run_copter.py:390-425`: the sample is built, then the
controller answers, then the simulator steps).

**Differences from the simulator** (see `PLANT.md`): the model is the exact flow; PyBullet
integrates with its own semi-implicit scheme at 1200 Hz (three substeps per tick). PyBullet
renormalizes the orientation quaternion; the exact flow keeps `‖q‖` (`qnormSq_step`) and has no
normalization term. The driver normalizes the reported quaternion and flips its sign to `q1 ≥ 0`
(`quat_ned_frd`); the model reports `q` as it is (same rotation, possibly the opposite sign after
large rotations). The driver's specific force is the backward difference of the simulated velocity
over the last period minus gravity; for the exact flow that differs from the instantaneous value by
at most `cV Q W · h / 2` (`backwardDiff_sub_specForce`). The ground contact of the simulator (the
vehicle starts on the ground) is not modeled.
-/

@[expose] public section

namespace Contracts.Plant

open Contracts.Lift

noncomputable section

/-! ## The sample -/

/-- `Vector3f` of the controller: three `float`s. -/
structure Vector3f where
  /-- North (or body forward). -/
  x : Float32
  /-- East (or body right). -/
  y : Float32
  /-- Down. -/
  z : Float32

/-- `Vector3p` of the controller: three `postype_t = double`s. -/
structure Vector3p where
  /-- North. -/
  x : Float
  /-- East. -/
  y : Float
  /-- Down. -/
  z : Float

/-- `Quaternion` of the controller: `q1` scalar, `float`s. -/
structure Quaternionf where
  /-- Scalar part. -/
  q1 : Float32
  /-- `i` component. -/
  q2 : Float32
  /-- `j` component. -/
  q3 : Float32
  /-- `k` component. -/
  q4 : Float32

/-- The sample of one tick, field for field `Copter.AHRS.Sample` of the port
(`Copter/AHRS.lean`): position, velocity, earth-frame specific force, attitude, body rates,
period. -/
structure Sample where
  /-- NED position, m (`postype_t`). -/
  pos : Vector3p
  /-- NED velocity, m/s. -/
  vel : Vector3f
  /-- Earth-frame specific force `get_accel_ef()`, NED, m/s². -/
  accel_ef : Vector3f
  /-- Body-to-NED attitude, `q1` scalar. -/
  quat : Quaternionf
  /-- Body rates, rad/s. -/
  gyro : Vector3f
  /-- Loop time in whole microseconds. -/
  dt_us : Nat

/-- The period in microseconds as the driver sends it: `1/400` s. -/
def dtUs : Nat := 2500

/-! ## Plant state, input, step and output -/

/-- The thrust fraction of slot `i`: the exact value of the actuator, clipped to `[0, 1]`
(`actuators_to_rpm`, `run_copter.py:339-346`). -/
def act (a : Vector Float32 4) (i : Fin 4) : ℝ := clip01 (a[i]).toReal

/-- The plant state at a tick. -/
structure PState where
  /-- The rigid-body state at the tick. -/
  x : X
  /-- The thrust fractions held over the period that ended at the tick. -/
  held : Fin 4 → ℝ

/-- The next plant state at real thrust fractions `u` held over the coming period. -/
def nextR (s : PState) (u : Fin 4 → ℝ) : PState := ⟨step s.x u, u⟩

/-- The next plant state under the four actuators. -/
def next (s : PState) (a : Vector Float32 4) : PState := nextR s (act a)

/-- The specific force at the tick: instantaneous, with the held thrust. -/
def tickSpecForce (s : PState) : Vec3 := specForce (State.ofX s.x).q s.held

/-- **The sample at a tick**: every real component through its port. -/
def sample (sense32 : ℝ → Float32) (senseP : ℝ → Float) (s : PState) : Sample :=
  let st := State.ofX s.x
  let f := tickSpecForce s
  { pos := ⟨senseP st.p.x, senseP st.p.y, senseP st.p.z⟩
    vel := ⟨sense32 st.v.x, sense32 st.v.y, sense32 st.v.z⟩
    accel_ef := ⟨sense32 f.x, sense32 f.y, sense32 f.z⟩
    quat := ⟨sense32 st.q.q1, sense32 st.q.q2, sense32 st.q.q3, sense32 st.q.q4⟩
    gyro := ⟨sense32 st.ω.x, sense32 st.ω.y, sense32 st.ω.z⟩
    dt_us := dtUs }

/-- The plant as a module with visible state: next state and this tick's sample. -/
def plant (sense32 : ℝ → Float32) (senseP : ℝ → Float) (s : PState) (a : Vector Float32 4) :
    PState × Sample :=
  (next s a, sample sense32 senseP s)

/-! ## Sensing hypotheses -/

/-- A `float` port: on `|r| ≤ R` the reading is finite and within `ε |r| + η`; `0` reads `+0` and
`1` reads `1`. -/
structure Sense32Spec (ε η R : ℝ) (sense : ℝ → Float32) : Prop where
  /-- Finite and within relative error `ε` plus absolute `η` on the range. -/
  err : ∀ r : ℝ, |r| ≤ R → (sense r).IsFinite ∧ |(sense r).toReal - r| ≤ ε * |r| + η
  /-- `0` reads `+0`. -/
  zero : sense 0 = 0
  /-- `1` reads `1`. -/
  one : sense 1 = 1

/-- The `postype` (`double`) port: on `|r| ≤ R` the reading is finite and within `ε |r| + η`;
`0` reads `+0`. -/
structure SensePSpec (ε η R : ℝ) (sense : ℝ → Float) : Prop where
  /-- Finite and within relative error `ε` plus absolute `η` on the range. -/
  err : ∀ r : ℝ, |r| ≤ R → (sense r).IsFinite ∧ |(sense r).toReal - r| ≤ ε * |r| + η
  /-- `0` reads `+0`. -/
  zero : sense 0 = 0

/-- The ports at round-to-nearest accuracy: binary32 on `|r| ≤ 100`, binary64 on `|r| ≤ 10⁴`. -/
structure CopterSense (sense32 : ℝ → Float32) (senseP : ℝ → Float) : Prop where
  /-- The `float` port. -/
  f32 : Sense32Spec ((2 : ℝ) ^ (-24 : ℤ)) ((2 : ℝ) ^ (-150 : ℤ)) 100 sense32
  /-- The `double` port. -/
  pos : SensePSpec ((2 : ℝ) ^ (-53 : ℤ)) ((2 : ℝ) ^ (-1075 : ℤ)) 10000 senseP

/-! ## Universe and component -/

/-- One tick of a behavior of the closed loop: the plant state, the sample sent to the controller,
and the actuators sent back. -/
structure CX where
  /-- The plant state. -/
  phys : PState
  /-- The sample the controller reads. -/
  smp : Sample
  /-- The actuators the controller writes. -/
  act : Vector Float32 4

/-- **The plant component**: visible state, reads `act`, writes `smp`, lifted with `liftStep`. -/
def Mplant (sense32 : ℝ → Float32) (senseP : ℝ → Float) : Set (ℕ → CX) :=
  liftStep (·.phys) (·.act) (·.smp) (plant sense32 senseP)

/-- Membership in the plant component, unfolded. -/
theorem mem_Mplant {sense32 : ℝ → Float32} {senseP : ℝ → Float} {b : ℕ → CX} :
    b ∈ Mplant sense32 senseP ↔ ∀ t, (b (t + 1)).phys = next (b t).phys (b t).act ∧
      (b t).smp = sample sense32 senseP (b t).phys := by
  simp only [Mplant, mem_liftStep, plant, Prod.mk.injEq]

/-- **The rigid-body state of a plant behavior follows the exact flow**: at every tick it is the
endpoint of the solution over the period with the actuators of the previous tick held. -/
theorem Mplant_flow {sense32 : ℝ → Float32} {senseP : ℝ → Float} {b : ℕ → CX}
    (hb : b ∈ Mplant sense32 senseP) (t : ℕ) :
    ∃ γ : ℝ → X, γ 0 = (b t).phys.x ∧ γ h = (b (t + 1)).phys.x ∧
      ∀ τ ∈ Set.Icc 0 h, HasDerivAt γ (vf (γ τ) (act (b t).act)) τ := by
  rw [((mem_Mplant.1 hb) t).1]
  exact step_spec _ _

/-- `‖q‖²` is the same at every tick of a plant behavior. -/
theorem Mplant_qnormSq {sense32 : ℝ → Float32} {senseP : ℝ → Float} {b : ℕ → CX}
    (hb : b ∈ Mplant sense32 senseP) (t : ℕ) : qnormSq (b t).phys.x = qnormSq (b 0).phys.x := by
  induction t with
  | zero => rfl
  | succ n ih =>
    rw [((mem_Mplant.1 hb) n).1, ← ih]
    exact qnormSq_step _ _

/-- **The sampled plant under constant actuators** as the library's discrete flow:
`Function.autonomousFlow` of the step, `n ↦ (step · u)^[n]`. -/
def sampledFlow (u : Fin 4 → ℝ) : AutonomousFlow ℕ X := Function.autonomousFlow (fun x => step x u)

/-- A plant behavior whose actuators read the constant thrust fractions `u` follows the sampled
flow: the rigid-body state at tick `n` is `sampledFlow u n` of the initial one. -/
theorem Mplant_const {sense32 : ℝ → Float32} {senseP : ℝ → Float} {b : ℕ → CX}
    (hb : b ∈ Mplant sense32 senseP) {u : Fin 4 → ℝ} (hu : ∀ t, act (b t).act = u) (n : ℕ) :
    (b n).phys.x = sampledFlow u n (b 0).phys.x := by
  induction n with
  | zero => exact ((sampledFlow u).map_id _).symm
  | succ n ih =>
    rw [((mem_Mplant.1 hb) n).1]
    change step (b n).phys.x (act (b n).act) = (fun x => step x u)^[n + 1] (b 0).phys.x
    rw [Function.iterate_succ_apply', hu n, ih]
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

/-- The sample of hover under ports that send `0` to `+0` and `1` to `1`. -/
theorem sample_hover {sense32 : ℝ → Float32} {senseP : ℝ → Float} (hz32 : sense32 0 = 0)
    (h1 : sense32 1 = 1) (hzP : senseP 0 = 0) (z : ℝ) :
    sample sense32 senseP (hoverP z) =
      { pos := ⟨0, 0, senseP z⟩, vel := ⟨0, 0, 0⟩, accel_ef := ⟨0, 0, sense32 (-grav)⟩,
        quat := ⟨1, 0, 0, 0⟩, gyro := ⟨0, 0, 0⟩, dt_us := dtUs } := by
  have hf := tickSpecForce_hover z
  simp only [sample, hf]
  simp [hoverP, hoverX, hoverState, State.toX, State.ofX, hz32, h1, hzP]

end

end Contracts.Plant
