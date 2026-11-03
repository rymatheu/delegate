import Contracts.Basic
import Contracts.Lift
import Contracts.FloatReal
import Flight.Controller
import Flight.FloatInstance
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# A rigid-body quadcopter plant with `Float` ports, closed with the flight controller

The plant is the Crazyflie 2.x in the X configuration as flown in `sim/` (gym-pybullet-drones,
`DroneModel.CF2X`, `Physics.PYB`), without drag, ground effect or downwash, discretized by one
forward-Euler step per control period `h = 1/120` s.

**Constants** (from `gym_pybullet_drones/assets/cf2x.urdf`): mass `0.027` kg, arm `L = 0.0397` m,
`kf = 3.16e-10`, `km = 7.94e-12`, thrust-to-weight `2.25`, inertia `diag(1.4e-5, 1.4e-5, 2.17e-5)`;
gravity `9.8` (as in the environment and `params/cf2x.txt`). The environment derives
`MAX_RPM = sqrt(2.25 · m g / (4 kf))` (`maxRPM`), and maps a command `u ∈ [0,1]` to
`rpm = MAX_RPM · sqrt u`, so the thrust of one motor is `kf · MAX_RPM² · u`, linear in `u`.

**State** (`QState`), all in NED with a forward-right-down body frame, as in `Flight.Types`:
position `p`, velocity `v` (world frame), ZYX Euler angles `att` (roll `φ`, pitch `θ`, yaw `ψ`), and
body rates `ω = (p, q, r)`. Vectors are `Flight.Vec3 ℝ`, angles `Flight.Euler ℝ`; no operation of the
`Arith` interface is used on them, every component is written out.

**Input**: `Motors Float`. Each command is read exactly (`Float.toReal`) and clipped to `[0, 1]`
in `ℝ` (`cmd`); motor `i` produces the force `fᵢ = kf · MAX_RPM² · uᵢ` along body `-z`.

**Geometry** (`Flight.Mixer`, `sim/README.md`): with `a = L/√2`, motor 1 front-right at body
`(a, a)`, motor 2 rear-left at `(-a, -a)`, motor 3 front-left at `(a, -a)`, motor 4 rear-right at
`(-a, a)`; motors 1, 2 spin counter-clockwise seen from above and their drag torque turns the body
clockwise, i.e. positive about body down. Hence
* `T  = f₁ + f₂ + f₃ + f₄`,
* `τx = a · (-f₁ + f₂ + f₃ - f₄)` (left motors raise roll),
* `τy = a · ( f₁ - f₂ + f₃ - f₄)` (front motors raise pitch),
* `τz = km · MAX_RPM² · (u₁ + u₂ - u₃ - u₄)`,
which is the simulator's `CF2X` torque law (`BaseAviary._dynamics`) transported from FLU to FRD.

**Dynamics** (`dyn`), with `R(att)` the ZYX body-to-NED rotation `Rz(ψ) Ry(θ) Rx(φ)` and
`R e_z = (cψ sθ cφ + sψ sφ, sψ sθ cφ - cψ sφ, cθ cφ)` the body down axis in NED (`thrustDir`):
* `p' = p + h v`,
* `v' = v + h (g e_z - (T / m) R(att) e_z)`,
* `att' = att + h E(att) ω`, with the ZYX kinematic matrix
  `E = [[1, sφ sθ/cθ, cφ sθ/cθ], [0, cφ, -sφ], [0, sφ/cθ, cφ/cθ]]` (`eulerRate`),
* `ω' = ω + h J⁻¹ (τ - ω × J ω)` with `J = diag(Jx, Jy, Jz)` (`rateAccel`).

**Output** (`measure`): the `SimInput Float` obtained by applying `sense : ℝ → Float` to every real
component, with `dt` the literal `0.008333333333333333`, the shortest decimal of `1/120` that the
simulator sends.

The universe `QX` holds the real state and the two `Float` signals; the plant is lifted with
`liftStep` (state `phys`, input `mot`, output `sim`), the controller `Flight.Controller.step` at the
`Float` instance with the flown parameters `cf2xParams` is lifted with `liftHidden` from
`Controller.State.init`, and the closed loop is `Mquad sense = Mplant sense ∩ Mctrl`.
-/

namespace Contracts.QuadPlant

open Contracts.Lift Flight

noncomputable section

/-! ## Constants -/

/-- Mass, kilograms. -/
def mass : ℝ := 0.027
/-- Arm length (center to rotor), meters. -/
def armL : ℝ := 0.0397
/-- Thrust coefficient, newtons per rpm². -/
def kf : ℝ := 3.16e-10
/-- Drag-torque coefficient, newton meters per rpm². -/
def km : ℝ := 7.94e-12
/-- Thrust-to-weight ratio. -/
def thrust2weight : ℝ := 2.25
/-- Gravitational acceleration, meters per second squared. -/
def grav : ℝ := 9.8
/-- Principal moments of inertia, kilogram square meters. -/
def Jx : ℝ := 1.4e-5
def Jy : ℝ := 1.4e-5
def Jz : ℝ := 2.17e-5
/-- The control period, seconds. -/
def h : ℝ := 1 / 120
/-- The maximum rotor speed, rpm, as the environment derives it. -/
def maxRPM : ℝ := Real.sqrt (thrust2weight * grav * mass / (4 * kf))
/-- Half-diagonal lever arm of the X configuration. -/
def armXY : ℝ := armL / Real.sqrt 2

/-- The maximum thrust of one motor, `kf · MAX_RPM²`, is a quarter of `2.25 m g`. -/
theorem kf_maxRPM_sq : kf * maxRPM ^ 2 = thrust2weight * grav * mass / 4 := by
  rw [maxRPM, Real.sq_sqrt (by norm_num [thrust2weight, grav, mass, kf])]
  unfold kf; field_simp

/-! ## State, input conversion, forces and torques -/

/-- Real plant state: position, velocity (NED), ZYX attitude, body rates (FRD). -/
structure QState where
  /-- Position, meters (NED). -/
  p : Vec3 ℝ
  /-- Velocity, meters per second (NED). -/
  v : Vec3 ℝ
  /-- Attitude, ZYX Euler angles, radians. -/
  att : Euler ℝ
  /-- Body rates `(p, q, r)`, radians per second. -/
  ω : Vec3 ℝ

/-- Saturation to `[0, 1]` in `ℝ`. -/
def clip01 (u : ℝ) : ℝ := max 0 (min 1 u)

/-- The exact value of a motor command, clipped to `[0, 1]`. -/
def cmd (m : Float) : ℝ := clip01 m.toReal

/-- Thrust of one motor under a clipped command. -/
def force (u : ℝ) : ℝ := kf * maxRPM ^ 2 * u

/-- Total thrust, newtons. -/
def thrust (m : Motors Float) : ℝ :=
  force (cmd m.m1) + force (cmd m.m2) + force (cmd m.m3) + force (cmd m.m4)

/-- Body torques `(τx, τy, τz)` about forward, right and down, newton meters. -/
def torque (m : Motors Float) : Vec3 ℝ :=
  ⟨armXY * (-force (cmd m.m1) + force (cmd m.m2) + force (cmd m.m3) - force (cmd m.m4)),
   armXY * (force (cmd m.m1) - force (cmd m.m2) + force (cmd m.m3) - force (cmd m.m4)),
   km * maxRPM ^ 2 * (cmd m.m1 + cmd m.m2 - cmd m.m3 - cmd m.m4)⟩

/-- The ZYX rotation body → NED applied to `e_z`: the body down axis in NED. -/
def thrustDir (a : Euler ℝ) : Vec3 ℝ :=
  ⟨Real.cos a.yaw * Real.sin a.pitch * Real.cos a.roll + Real.sin a.yaw * Real.sin a.roll,
   Real.sin a.yaw * Real.sin a.pitch * Real.cos a.roll - Real.cos a.yaw * Real.sin a.roll,
   Real.cos a.pitch * Real.cos a.roll⟩

/-- ZYX Euler-angle rates `E(att) ω` from body rates. -/
def eulerRate (a : Euler ℝ) (w : Vec3 ℝ) : Euler ℝ :=
  ⟨w.x + (Real.sin a.roll * w.y + Real.cos a.roll * w.z) * Real.sin a.pitch / Real.cos a.pitch,
   Real.cos a.roll * w.y - Real.sin a.roll * w.z,
   (Real.sin a.roll * w.y + Real.cos a.roll * w.z) / Real.cos a.pitch⟩

/-- Body angular acceleration `J⁻¹ (τ - ω × J ω)` for diagonal `J`. -/
def rateAccel (τ w : Vec3 ℝ) : Vec3 ℝ :=
  ⟨(τ.x - (w.y * (Jz * w.z) - w.z * (Jy * w.y))) / Jx,
   (τ.y - (w.z * (Jx * w.x) - w.x * (Jz * w.z))) / Jy,
   (τ.z - (w.x * (Jy * w.y) - w.y * (Jx * w.x))) / Jz⟩

/-! ## One step of the plant -/

/-- The forward-Euler step of the rigid body over one control period. -/
-- <<quadDyn>>
def dyn (s : QState) (m : Motors Float) : QState :=
  let T := thrust m
  let d := thrustDir s.att
  let ea := eulerRate s.att s.ω
  let α := rateAccel (torque m) s.ω
  ⟨⟨s.p.x + h * s.v.x, s.p.y + h * s.v.y, s.p.z + h * s.v.z⟩,
   ⟨s.v.x + h * (-(T / mass) * d.x), s.v.y + h * (-(T / mass) * d.y),
    s.v.z + h * (grav - (T / mass) * d.z)⟩,
   ⟨s.att.roll + h * ea.roll, s.att.pitch + h * ea.pitch, s.att.yaw + h * ea.yaw⟩,
   ⟨s.ω.x + h * α.x, s.ω.y + h * α.y, s.ω.z + h * α.z⟩⟩
-- <</quadDyn>>

/-- The control period as the simulator sends it. -/
def dtF : Float := 0.008333333333333333

/-- The `Float` sample the controller receives: every real component through `sense`. -/
-- <<quadMeasure>>
def measure (sense : ℝ → Float) (s : QState) : SimInput Float :=
  ⟨⟨sense s.p.x, sense s.p.y, sense s.p.z⟩, ⟨sense s.v.x, sense s.v.y, sense s.v.z⟩,
   ⟨sense s.att.roll, sense s.att.pitch, sense s.att.yaw⟩,
   ⟨sense s.ω.x, sense s.ω.y, sense s.ω.z⟩, dtF⟩
-- <</quadMeasure>>

/-- The plant as a module with visible state: next state and this tick's measurement. -/
def plant (sense : ℝ → Float) (s : QState) (m : Motors Float) : QState × SimInput Float :=
  (dyn s m, measure sense s)

end

/-! ## The flown controller parameters (`sim/params/cf2x.txt`) -/

/-- The mission of `cf2x.txt`: climb to 1 m, 2 m north, then 2 m east turning to face east. -/
def cf2xMission : List (Waypoint Float) :=
  [⟨⟨0, 0, -1⟩, 0⟩, ⟨⟨2, 0, -1⟩, 0⟩, ⟨⟨2, 2, -1⟩, 1.5707963267948966⟩]

/-- The controller parameters of `sim/params/cf2x.txt`, field by field. -/
-- <<cf2xParams>>
def cf2xParams : Controller.Params Float where
  nav := { waypoints := cf2xMission, acceptRadius := 0.05, wpSpeed := 1.0, wpAccel := 1.5,
           cornerRadius := 0.3, yawAlongPath := false }
  pos := { posGainXY := 1.0, posGainZ := 1.5, maxSpeedXY := 1.0, maxSpeedZ := 1.0,
           velXY := { kp := 3.0, ki := 0.5, kd := 0.25, iMax := 2.0 },
           velZ := { kp := 4.0, ki := 2.0, kd := 0.0, iMax := 3.0 },
           maxAccelXY := 3.0, maxAccelZ := 3.0 }
  target := { gravity := 9.8, hoverThrottle := 0.4444444444444444, maxLean := 0.35 }
  att := { rollGain := 8.0, pitchGain := 8.0, yawGain := 4.5, maxRollPitchRate := 3.5,
           maxYawRate := 1.57 }
  rate := { roll := { kp := 0.135, ki := 0.135, kd := 0.0, iMax := 0.5 },
            pitch := { kp := 0.135, ki := 0.135, kd := 0.0, iMax := 0.5 },
            yaw := { kp := 0.2, ki := 0.02, kd := 0.0, iMax := 0.5 } }
  mixer := { f1 := ⟨-0.5, 0.5, 0.5⟩, f2 := ⟨0.5, -0.5, 0.5⟩, f3 := ⟨0.5, 0.5, -0.5⟩,
             f4 := ⟨-0.5, -0.5, -0.5⟩ }
-- <</cf2xParams>>

/-- `cf2x.txt` followed by `hover.txt`: the same gains, mission the single waypoint `(0, 0, -1)`
at yaw `0`. -/
def hoverParams : Controller.Params Float :=
  { cf2xParams with nav := { cf2xParams.nav with waypoints := [⟨⟨0, 0, -1⟩, 0⟩] } }

/-- The figure-eight course of `sim/params/cf2x-course.txt`. -/
def courseMission : List (Waypoint Float) :=
  [⟨⟨0, 0, -0.8⟩, 0.7853981633974483⟩, ⟨⟨1.25, 1.25, -1.0⟩, 0.7853981633974483⟩,
   ⟨⟨0, 2.5, -1.2⟩, 2.356194490192345⟩, ⟨⟨-1.25, 1.25, -1.4⟩, -2.356194490192345⟩,
   ⟨⟨1.25, -1.25, -1.6⟩, -0.7853981633974483⟩, ⟨⟨0, -2.5, -1.4⟩, -2.356194490192345⟩,
   ⟨⟨-1.25, -1.25, -1.1⟩, 2.356194490192345⟩, ⟨⟨0, 0, -0.8⟩, 0.7853981633974483⟩]

/-- `cf2x.txt` followed by `cf2x-course.txt`: the figure-eight course, heading along the path, and
a horizontal speed limit of `1.5` m/s. -/
def courseParams : Controller.Params Float :=
  { cf2xParams with
    nav := { cf2xParams.nav with waypoints := courseMission, yawAlongPath := true }
    pos := { cf2xParams.pos with maxSpeedXY := 1.5 } }

/-! ## Universe and components -/

/-- One tick of a behavior of the closed loop: the real plant state, the `Float` sample sent to
the controller, and the `Float` motor commands sent back. -/
-- <<QX>>
structure QX where
  /-- The real rigid-body state. -/
  phys : QState
  /-- The sample the controller reads. -/
  sim : SimInput Float
  /-- The motor commands the controller writes. -/
  mot : Motors Float
-- <</QX>>

/-- The plant component: visible real state, reads `mot`, writes `sim`. -/
-- <<Mplant>>
noncomputable def Mplant (sense : ℝ → Float) : Set (ℕ → QX) :=
  liftStep (·.phys) (·.mot) (·.sim) (plant sense)
-- <</Mplant>>

/-- The controller component: the full `Float` controller with hidden state from `State.init`,
reads `sim`, writes `mot`. -/
-- <<Mctrl>>
def MctrlP (P : Controller.Params Float) : Set (ℕ → QX) :=
  liftHidden (·.sim) (·.mot) (Controller.step P) Controller.State.init

/-- The controller flown in the simulator. -/
def Mctrl : Set (ℕ → QX) := MctrlP cf2xParams
-- <</Mctrl>>

/-- The closed loop. -/
-- <<Mquad>>
noncomputable def Mquad (sense : ℝ → Float) : Set (ℕ → QX) := Mplant sense ∩ Mctrl
-- <</Mquad>>

/-- The closed loop with the hover mission. -/
noncomputable def MquadHover (sense : ℝ → Float) : Set (ℕ → QX) :=
  Mplant sense ∩ MctrlP hoverParams

end Contracts.QuadPlant
