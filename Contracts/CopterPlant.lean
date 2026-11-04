import Contracts.QuadPlant
import FloatModel.Float32
import Copter.AHRS

/-!
# The Crazyflie plant for the ArduCopter port: 400 Hz, `Float32` ports

The rigid body of `Contracts.QuadPlant` (Crazyflie 2.x, X configuration, gym-pybullet-drones
`DroneModel.CF2X`, no drag, ground effect or downwash), discretized by one forward-Euler step per
ArduCopter main-loop period `h = 1/400` s, with the ports of the ported ArduCopter stack
(`Copter.loop`, `Copter/Main.lean`, `Copter/PROTOCOL.md`):

* **input**: the four `Float32` actuators `Copter.State.actuators` (motor slots 0..3 of
  `AP_MotorsMatrix::setup_quad_matrix`, `MOTOR_FRAME_TYPE_X`) read exactly (`Float32.toReal`) and
  clipped to `[0, 1]`. In the linear thrust configuration (`MOT_THST_EXPO 0`, `MOT_SPIN_MIN 0`,
  `MOT_SPIN_MAX 1`, `MOT_BAT_VOLT_MAX 0`, `sim/params/copter-cf2x.txt`) the actuator is the thrust
  fraction: motor `i` produces `kf · MAX_RPM² · uᵢ` along body `-z`, as `sim/run_copter.py`
  (`actuators_to_rpm`, `rpm = MAX_RPM √a`) feeds the simulator;
* **output**: the `Copter.AHRS.Sample` of one tick: NED position through the `postype` port
  `senseP : ℝ → Float`; NED velocity, earth-frame specific force, body-to-NED quaternion and body
  rates through the `float` port `sense32 : ℝ → Float32`; the period `2500` µs.

**Constants** as in `QuadPlant` (mass, arm, `kf`, `km`, inertia, thrust-to-weight `2.25`), except
gravity, which is ArduPilot's `GRAVITY_MSS = 9.80665` (the simulator's gravity is set to it by
`sim/run_copter.py`, `make_env`); hence `MAX_RPM = √(2.25 m g / (4 kf))` with that `g`
(`kf_maxRPM_sq`).

**Motor slots** (`Copter/PROTOCOL.md`, `run_copter.py:SLOT_TO_SIM`): slot 0 front right CCW,
slot 1 rear left CCW, slot 2 front left CW, slot 3 rear right CW, which are motors 1-4 of
`QuadPlant`; hence the same force and torque law (`torque`).

**State** (`CState`): position `p`, velocity `v` (NED), ZYX Euler angles `att`, body rates `ω`, as
in `QuadPlant.QState`, and the specific force `sf` of the last period. `sf` is what the
simulator reports as `get_accel_ef()`: the backward difference of the NED velocity over the last
period minus `(0, 0, g)` (`run_copter.py`, `accel_ef`), i.e. `-(T/m) R(att) e_z` with the thrust
and attitude of the previous step. At rest in hover it is `(0, 0, -g)`.

**Dynamics** (`dynR` on real thrust fractions, `dyn` on the actuators), with `R e_z`
(`QuadPlant.thrustDir`), the ZYX kinematics `E` (`QuadPlant.eulerRate`) and `J⁻¹(τ - ω × Jω)`
(`QuadPlant.rateAccel`):
* `p' = p + h v`, `v' = v + h (g e_z - (T/m) R(att) e_z)`, `att' = att + h E(att) ω`,
  `ω' = ω + h J⁻¹(τ - ω × Jω)`, `sf' = -(T/m) R(att) e_z`.

**Outputs**: the quaternion of the Euler angles (`quatOf`, the formula of
`Quaternion::from_euler`, `AP_Math/quaternion.lean`), each component through `sense32`.

**What the plant leaves out**: aerodynamic drag, ground effect, downwash, the propeller and motor
dynamics (thrust follows the actuator within the tick), gyroscopic and inflow effects, battery
sag, air density (`run.air_density_ratio = 1`), sensor noise, bias and delay beyond the rounding
of the ports, the EKF (the sample is the true state, rounded), and the simulator's integration at
1200 Hz (here one Euler step per 400 Hz tick). The attitude is stored as Euler angles (as in
`QuadPlant`), so the plant is not defined through the pitch singularity `cos θ = 0`.

**Sensing** is a hypothesis (`Sense32Spec`, `SensePSpec`, bundled in `CopterSense`) in the style of
`FloatReal.SenseSpec` and `QuadHover.HoverSense`: on a range, each port returns a finite value
within a relative error `ε` plus an absolute `η` (round to nearest gives `ε = 2⁻²⁴`, `η = 2⁻¹⁵⁰` for
binary32 and `2⁻⁵³`, `2⁻¹⁰⁷⁵` for binary64), and maps `0` to `+0` and `1` to `1`, which a level
attitude needs (quaternion `(1, 0, 0, 0)`).

The plant is lifted with `liftStep` on the universe `CX` (state `phys`, input `act`, output
`smp`): `Mplant sense32 senseP`. The hover fixed point is `dynR_hover`; four equal actuators move a
level state at rest horizontally only along the vertical (`dyn_vert`).
-/

namespace Contracts.CopterPlant

open Contracts.Lift Flight

noncomputable section

/-! ## Constants -/

/-- Gravity, `GRAVITY_MSS` (`AP_Math/definitions.h:45`), meters per second squared. -/
def gravity : ℝ := 9.80665
/-- The main-loop period, `1 / SCHED_LOOP_RATE` with `SCHED_LOOP_RATE = 400`, seconds. -/
def h : ℝ := 1 / 400
/-- The maximum rotor speed, rpm, as the environment derives it, with `g = GRAVITY_MSS`. -/
def maxRPM : ℝ :=
  Real.sqrt (QuadPlant.thrust2weight * gravity * QuadPlant.mass / (4 * QuadPlant.kf))

/-- The maximum thrust of one motor, `kf · MAX_RPM²`, is a quarter of `2.25 m g`. -/
theorem kf_maxRPM_sq :
    QuadPlant.kf * maxRPM ^ 2 = QuadPlant.thrust2weight * gravity * QuadPlant.mass / 4 := by
  rw [maxRPM, Real.sq_sqrt (by norm_num [QuadPlant.thrust2weight, gravity, QuadPlant.mass,
    QuadPlant.kf])]
  unfold QuadPlant.kf; field_simp

/-! ## State, input, forces and torques -/

/-- Real plant state: position, velocity (NED), ZYX attitude, body rates (FRD), and the specific
force (NED) of the last period. -/
structure CState where
  /-- Position, meters (NED). -/
  p : Vec3 ℝ
  /-- Velocity, meters per second (NED). -/
  v : Vec3 ℝ
  /-- Attitude, ZYX Euler angles, radians. -/
  att : Euler ℝ
  /-- Body rates `(p, q, r)`, radians per second. -/
  ω : Vec3 ℝ
  /-- Specific force of the last period, `(v - v_prev)/h - g e_z`, meters per second squared. -/
  sf : Vec3 ℝ

/-- The thrust fraction of slot `i`: the exact value of the actuator, clipped to `[0, 1]`
(linear thrust configuration, see the header). -/
def act (a : Vector Float32 4) (i : Fin 4) : ℝ := QuadPlant.clip01 (a[i]).toReal

/-- Thrust of one motor at thrust fraction `u`, newtons. -/
def force (u : ℝ) : ℝ := QuadPlant.kf * maxRPM ^ 2 * u

/-- Total thrust, newtons. -/
def thrust (u : Fin 4 → ℝ) : ℝ := force (u 0) + force (u 1) + force (u 2) + force (u 3)

/-- Body torques `(τx, τy, τz)` about forward, right and down, newton meters: slot 0 front right
CCW, 1 rear left CCW, 2 front left CW, 3 rear right CW (`QuadPlant.torque` with motors 1-4). -/
def torque (u : Fin 4 → ℝ) : Vec3 ℝ :=
  ⟨QuadPlant.armXY * (-force (u 0) + force (u 1) + force (u 2) - force (u 3)),
   QuadPlant.armXY * (force (u 0) - force (u 1) + force (u 2) - force (u 3)),
   QuadPlant.km * maxRPM ^ 2 * (u 0 + u 1 - u 2 - u 3)⟩

/-! ## One step of the plant -/

/-- The forward-Euler step over one main-loop period at real thrust fractions `u`. -/
-- <<copterDynR>>
def dynR (s : CState) (u : Fin 4 → ℝ) : CState :=
  let T := thrust u
  let d := QuadPlant.thrustDir s.att
  let ea := QuadPlant.eulerRate s.att s.ω
  let α := QuadPlant.rateAccel (torque u) s.ω
  ⟨⟨s.p.x + h * s.v.x, s.p.y + h * s.v.y, s.p.z + h * s.v.z⟩,
   ⟨s.v.x + h * (-(T / QuadPlant.mass) * d.x), s.v.y + h * (-(T / QuadPlant.mass) * d.y),
    s.v.z + h * (gravity - (T / QuadPlant.mass) * d.z)⟩,
   ⟨s.att.roll + h * ea.roll, s.att.pitch + h * ea.pitch, s.att.yaw + h * ea.yaw⟩,
   ⟨s.ω.x + h * α.x, s.ω.y + h * α.y, s.ω.z + h * α.z⟩,
   ⟨-(T / QuadPlant.mass) * d.x, -(T / QuadPlant.mass) * d.y, -(T / QuadPlant.mass) * d.z⟩⟩
-- <</copterDynR>>

/-- The step driven by the four actuators. -/
def dyn (s : CState) (a : Vector Float32 4) : CState := dynR s (act a)

/-! ## Outputs -/

/-- A real quaternion `(q1, q2, q3, q4)`, `q1` the scalar part. -/
structure RQuat where
  q1 : ℝ
  q2 : ℝ
  q3 : ℝ
  q4 : ℝ

/-- The body-to-NED quaternion of ZYX Euler angles (`Quaternion::from_euler`,
`AP_Math/quaternion.cpp`, ported as `AP_Math.Quaternion.from_euler`). -/
def quatOf (a : Euler ℝ) : RQuat :=
  let cr2 := Real.cos (a.roll / 2)
  let cp2 := Real.cos (a.pitch / 2)
  let cy2 := Real.cos (a.yaw / 2)
  let sr2 := Real.sin (a.roll / 2)
  let sp2 := Real.sin (a.pitch / 2)
  let sy2 := Real.sin (a.yaw / 2)
  ⟨cr2 * cp2 * cy2 + sr2 * sp2 * sy2, sr2 * cp2 * cy2 - cr2 * sp2 * sy2,
   cr2 * sp2 * cy2 + sr2 * cp2 * sy2, cr2 * cp2 * sy2 - sr2 * sp2 * cy2⟩

/-- The main-loop period in microseconds, as the harness sends it. -/
def dtUs : Nat := 2500

/-- The sample the controller receives: every real component through its port. -/
-- <<copterSample>>
def sample (sense32 : ℝ → Float32) (senseP : ℝ → Float) (s : CState) : Copter.AHRS.Sample :=
  let q := quatOf s.att
  { pos := ⟨senseP s.p.x, senseP s.p.y, senseP s.p.z⟩
    vel := ⟨sense32 s.v.x, sense32 s.v.y, sense32 s.v.z⟩
    accel_ef := ⟨sense32 s.sf.x, sense32 s.sf.y, sense32 s.sf.z⟩
    quat := ⟨sense32 q.q1, sense32 q.q2, sense32 q.q3, sense32 q.q4⟩
    gyro := ⟨sense32 s.ω.x, sense32 s.ω.y, sense32 s.ω.z⟩
    dt_us := dtUs }
-- <</copterSample>>

/-- The plant as a module with visible state: next state and this tick's sample. -/
def plant (sense32 : ℝ → Float32) (senseP : ℝ → Float) (s : CState) (a : Vector Float32 4) :
    CState × Copter.AHRS.Sample :=
  (dyn s a, sample sense32 senseP s)

/-! ## Sensing hypotheses -/

/-- A `float` port: on `|r| ≤ R` the reading is finite and within `ε |r| + η`; `0` reads `+0` and
`1` reads `1`. -/
-- <<Sense32Spec>>
structure Sense32Spec (ε η R : ℝ) (sense : ℝ → Float32) : Prop where
  err : ∀ r : ℝ, |r| ≤ R → (sense r).IsFinite ∧ |(sense r).toReal - r| ≤ ε * |r| + η
  zero : sense 0 = 0
  one : sense 1 = 1
-- <</Sense32Spec>>

/-- The `postype` (`double`) port: on `|r| ≤ R` the reading is finite and within `ε |r| + η`;
`0` reads `+0`. -/
-- <<SensePSpec>>
structure SensePSpec (ε η R : ℝ) (sense : ℝ → Float) : Prop where
  err : ∀ r : ℝ, |r| ≤ R → (sense r).IsFinite ∧ |(sense r).toReal - r| ≤ ε * |r| + η
  zero : sense 0 = 0
-- <</SensePSpec>>

/-- The ports of the copter plant at round-to-nearest accuracy: binary32 on `|r| ≤ 100`, binary64
on `|r| ≤ 10⁴`. -/
-- <<CopterSense>>
structure CopterSense (sense32 : ℝ → Float32) (senseP : ℝ → Float) : Prop where
  f32 : Sense32Spec ((2 : ℝ) ^ (-24 : ℤ)) ((2 : ℝ) ^ (-150 : ℤ)) 100 sense32
  pos : SensePSpec ((2 : ℝ) ^ (-53 : ℤ)) ((2 : ℝ) ^ (-1075 : ℤ)) 10000 senseP
-- <</CopterSense>>

/-! ## Universe and component -/

/-- One tick of a behavior of the closed loop: the real plant state, the sample sent to the
controller, and the actuators sent back. -/
-- <<CX>>
structure CX where
  /-- The real rigid-body state. -/
  phys : CState
  /-- The sample the controller reads. -/
  smp : Copter.AHRS.Sample
  /-- The actuators the controller writes. -/
  act : Vector Float32 4
-- <</CX>>

/-- The plant component: visible real state, reads `act`, writes `smp`. -/
-- <<MplantCopter>>
def Mplant (sense32 : ℝ → Float32) (senseP : ℝ → Float) : Set (ℕ → CX) :=
  liftStep (·.phys) (·.act) (·.smp) (plant sense32 senseP)
-- <</MplantCopter>>

/-! ## The plant on the vertical -/

/-- A state on the vertical, level, not rotating, with vertical specific force `f`. -/
def vstate (z w f : ℝ) : CState := ⟨⟨0, 0, z⟩, ⟨0, 0, w⟩, ⟨0, 0, 0⟩, ⟨0, 0, 0⟩, ⟨0, 0, f⟩⟩

/-- Four equal thrust fractions `c` give the vertical specific force `-2.25 g c`. -/
theorem thrust_div_mass (u : Fin 4 → ℝ) (c : ℝ) (hu : ∀ i, u i = c) :
    thrust u / QuadPlant.mass = QuadPlant.thrust2weight * gravity * c := by
  simp only [thrust, force, hu]
  rw [kf_maxRPM_sq]
  unfold QuadPlant.mass; ring

/-- **Vertical motion.** Four equal thrust fractions `c` move a level state at rest horizontally
along the vertical: no torque, no horizontal force, the attitude and rates stay zero, and only the
vertical pair `(z, w)` and the specific force change. -/
theorem dynR_vert (z w f c : ℝ) (u : Fin 4 → ℝ) (hu : ∀ i, u i = c) :
    dynR (vstate z w f) u =
      vstate (z + h * w) (w + h * (gravity - QuadPlant.thrust2weight * gravity * c))
        (-(QuadPlant.thrust2weight * gravity * c)) := by
  have hT := thrust_div_mass u c hu
  simp only [dynR, vstate, QuadPlant.thrustDir, QuadPlant.eulerRate, QuadPlant.rateAccel, torque,
    Real.sin_zero, Real.cos_zero, hu, hT]
  congr 2 <;> ring

/-- **The hover fixed point.** At the hover thrust fraction `1/2.25` on all four motors, a level
state at rest with the hover specific force `(0, 0, -g)` stays where it is. -/
theorem dynR_hover (z : ℝ) (u : Fin 4 → ℝ) (hu : ∀ i, u i = 1 / QuadPlant.thrust2weight) :
    dynR (vstate z 0 (-gravity)) u = vstate z 0 (-gravity) := by
  rw [dynR_vert z 0 (-gravity) _ u hu]
  have : QuadPlant.thrust2weight * gravity * (1 / QuadPlant.thrust2weight) = gravity := by
    unfold QuadPlant.thrust2weight; ring
  rw [this]; congr 1 <;> ring

/-- Four actuators of one exact value `c ∈ [0, 1]` drive the vertical motion of `dynR_vert`. -/
theorem dyn_vert (z w f c : ℝ) (a : Vector Float32 4) (hc0 : 0 ≤ c) (hc1 : c ≤ 1)
    (ha : ∀ i : Fin 4, (a[i]).toReal = c) :
    dyn (vstate z w f) a =
      vstate (z + h * w) (w + h * (gravity - QuadPlant.thrust2weight * gravity * c))
        (-(QuadPlant.thrust2weight * gravity * c)) := by
  apply dynR_vert
  intro i
  rw [act, QuadPlant.clip01, ha i, min_eq_right hc1, max_eq_right hc0]

/-- The quaternion of the level attitude facing north is `(1, 0, 0, 0)`. -/
theorem quatOf_level : quatOf ⟨0, 0, 0⟩ = ⟨1, 0, 0, 0⟩ := by
  simp [quatOf]

/-- The sample of a vertical state under ports that send `0` to `+0` and `1` to `1`: zero
horizontal position, velocity, specific force and rates, the identity quaternion. -/
theorem sample_vstate {sense32 : ℝ → Float32} {senseP : ℝ → Float} (hz32 : sense32 0 = 0)
    (h1 : sense32 1 = 1) (hzP : senseP 0 = 0) (z w f : ℝ) :
    sample sense32 senseP (vstate z w f) =
      { pos := ⟨0, 0, senseP z⟩, vel := ⟨0, 0, sense32 w⟩, accel_ef := ⟨0, 0, sense32 f⟩,
        quat := ⟨1, 0, 0, 0⟩, gyro := ⟨0, 0, 0⟩, dt_us := dtUs } := by
  simp only [sample, vstate, quatOf_level, hz32, h1, hzP]

end

end Contracts.CopterPlant
