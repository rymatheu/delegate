import Flight.FloatInstance
import Flight.Mixer

/-!
# Crude built-in plant for the self-test

A deliberately rough quadcopter model in `Float`, used only by `flight --selftest` so the
controller can be exercised without an external simulator; the real plant is external. It is a
point mass with linear drag, driven by a thrust along the body up axis proportional to the mean
motor command, plus rigid-body attitude whose body angular acceleration is proportional to the
torque the motors produce (recovered through the mixer factors) with linear rate damping. Euler
angles follow the exact ZYX kinematics. A flat ground at `z = 0` stops the vehicle from sinking.
Motor dynamics, gyroscopic effects, aerodynamics beyond drag, and sensor noise are ignored.
-/

namespace Flight

namespace TestPlant

/-- Physical constants of the self-test plant; they are illustrative, not identified from a real airframe. -/
structure Params where
  /-- Gravitational acceleration, meters per second squared. -/
  gravity : Float := 9.80665
  /-- Mean motor command at which thrust balances gravity (deliberately different from the controller's guess). -/
  hoverThrottle : Float := 0.45
  /-- Linear drag coefficient, per second. -/
  drag : Float := 0.2
  /-- Roll and pitch angular acceleration per unit normalized torque, radians per second squared. -/
  rollPitchAuthority : Float := 150.0
  /-- Yaw angular acceleration per unit normalized torque, radians per second squared. -/
  yawAuthority : Float := 20.0
  /-- Linear damping of body rates, per second. -/
  rateDamping : Float := 1.0
  /-- Number of Euler integration sub-steps per controller tick. -/
  substeps : Nat := 10

/-- State of the self-test plant: position, velocity, attitude, body rates. -/
structure State where
  /-- Position, meters (NED). -/
  pos : Vec3 Float
  /-- Velocity, meters per second (NED). -/
  vel : Vec3 Float
  /-- Attitude, ZYX Euler angles. -/
  att : Euler Float
  /-- Body rates, radians per second. -/
  rates : Vec3 Float
  deriving Repr

/-- The vehicle at rest on the ground at the origin, facing north. -/
def State.init : State := ⟨⟨0, 0, 0⟩, ⟨0, 0, 0⟩, ⟨0, 0, 0⟩, ⟨0, 0, 0⟩⟩

/-- Sensor reading handed to the controller: the exact plant state plus the tick length. -/
def State.measure (s : State) (dt : Float) : SimInput Float := ⟨s.pos, s.vel, s.att, s.rates, dt⟩

/-- Advance the plant by `h` seconds with one forward-Euler step under fixed motor commands. -/
def eulerStep (p : Params) (s : State) (m : Motors Float) (h : Float) : State :=
  let mix : MixerParams Float := {}
  let cmds := [(mix.f1, m.m1), (mix.f2, m.m2), (mix.f3, m.m3), (mix.f4, m.m4)]
  let τ : Vec3 Float := cmds.foldl (fun acc (f, u) => acc + Vec3.smul u ⟨f.roll, f.pitch, f.yaw⟩) ⟨0, 0, 0⟩
  let force := (m.m1 + m.m2 + m.m3 + m.m4) / 4 * p.gravity / p.hoverThrottle
  let φ := s.att.roll
  let θ := s.att.pitch
  let ψ := s.att.yaw
  -- Body down axis in the world frame (third column of the ZYX rotation).
  let bz : Vec3 Float :=
    ⟨Float.cos ψ * Float.sin θ * Float.cos φ + Float.sin ψ * Float.sin φ,
     Float.sin ψ * Float.sin θ * Float.cos φ - Float.cos ψ * Float.sin φ,
     Float.cos θ * Float.cos φ⟩
  let acc : Vec3 Float := ⟨0, 0, p.gravity⟩ - Vec3.smul force bz - Vec3.smul p.drag s.vel
  let ω := s.rates
  let ωdot : Vec3 Float :=
    ⟨p.rollPitchAuthority * τ.x - p.rateDamping * ω.x,
     p.rollPitchAuthority * τ.y - p.rateDamping * ω.y,
     p.yawAuthority * τ.z - p.rateDamping * ω.z⟩
  let attDot : Euler Float :=
    ⟨ω.x + (ω.y * Float.sin φ + ω.z * Float.cos φ) * Float.tan θ,
     ω.y * Float.cos φ - ω.z * Float.sin φ,
     (ω.y * Float.sin φ + ω.z * Float.cos φ) / Float.cos θ⟩
  let pos := s.pos + Vec3.smul h s.vel
  let vel := s.vel + Vec3.smul h acc
  -- Flat ground: no sinking below `z = 0`, and no downward speed while on it.
  let (pos, vel) :=
    if pos.z > 0 then (({ pos with z := 0 } : Vec3 Float), ({ vel with z := min vel.z 0 } : Vec3 Float))
    else (pos, vel)
  let att : Euler Float := ⟨φ + h * attDot.roll, θ + h * attDot.pitch, wrapAngle (ψ + h * attDot.yaw)⟩
  ⟨pos, vel, att, ω + Vec3.smul h ωdot⟩

/-- Advance the plant by one controller tick of `dt` seconds, split into `substeps` Euler steps. -/
def step (p : Params) (s : State) (m : Motors Float) (dt : Float) : State :=
  let h := dt / p.substeps.toFloat
  (List.range p.substeps).foldl (fun st _ => eulerStep p st m h) s

end TestPlant

end Flight
