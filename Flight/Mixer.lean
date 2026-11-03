import Flight.Types

/-!
# Quad X motor mixer

Structured after the matrix mixer of ArduPilot's `AP_Motors` library (`AP_MotorsMatrix.cpp`,
quad X frame): each motor command is the collective thrust plus a weighted sum of the roll, pitch
and yaw torques, with per-motor factors fixed by the motor's position and spin direction.

Motor layout (body frame forward-right-down, seen from above):
* motor 1 front-right, counter-clockwise; motor 2 rear-left, counter-clockwise;
* motor 3 front-left, clockwise; motor 4 rear-right, clockwise.
Positive roll torque raises the left motors, positive pitch torque raises the front motors, and
positive yaw torque (nose right) raises the counter-clockwise motors, whose drag turns the body
clockwise. All factors have magnitude `1/2`, so an unsaturated command reproduces the requested
torque as the factor-weighted sum of the motor commands.

Saturation (simplified): thrust is clipped to `[0, 1]` and torques to `[-1, 1]`. If some motor
would exceed `1` or fall below `0`, the whole torque contribution is scaled down by the largest
common factor that keeps every motor in `[0, 1]` with the collective thrust unchanged; a final clip
guards rounding. ArduCopter's scheme is more elaborate: it reserves yaw headroom, gives roll and
pitch priority over yaw, may move the collective thrust to preserve attitude authority, applies
a minimum spin and thrust-curve linearization, compensates battery voltage, and detects a failed
motor. None of that is modelled here.
-/

namespace Flight

/-- How one motor responds to the three torque commands. -/
structure MotorFactors (α : Type) where
  /-- Weight of the roll torque. -/
  roll : α
  /-- Weight of the pitch torque. -/
  pitch : α
  /-- Weight of the yaw torque. -/
  yaw : α
  deriving Repr

/-- Mixer parameters: the factors of the four motors, defaulting to the quad X frame. -/
structure MixerParams (α : Type) [Arith α] where
  /-- Front-right, counter-clockwise. -/
  f1 : MotorFactors α := ⟨-0.5, 0.5, 0.5⟩
  /-- Rear-left, counter-clockwise. -/
  f2 : MotorFactors α := ⟨0.5, -0.5, 0.5⟩
  /-- Front-left, clockwise. -/
  f3 : MotorFactors α := ⟨0.5, 0.5, -0.5⟩
  /-- Rear-right, clockwise. -/
  f4 : MotorFactors α := ⟨-0.5, -0.5, -0.5⟩

/-- Mixer input: collective thrust and normalized torques `(roll, pitch, yaw)`. -/
structure MixerInput (α : Type) where
  /-- Collective thrust, nominally in `[0, 1]`. -/
  thrust : α
  /-- Torques about the body axes, nominally in `[-1, 1]`. -/
  torque : Vec3 α

/-- Torque contribution of one motor. -/
def MotorFactors.apply {α : Type} [Arith α] (f : MotorFactors α) (τ : Vec3 α) : α :=
  f.roll * τ.x + f.pitch * τ.y + f.yaw * τ.z

/-- The largest factor in `[0, 1]` by which the torque contributions between `lo` and `hi` can be scaled so that `thr` plus each stays in `[0, 1]`. -/
def Mixer.torqueScale {α : Type} [Arith α] (thr lo hi : α) : α :=
  let sHi : α := if 1 < thr + hi then (1 - thr) / hi else 1
  let sLo : α := if thr + lo < 0 then thr / (-lo) else 1
  min sHi sLo

/-- Map collective thrust and torques to four motor commands in `[0, 1]`, scaling the torques down when a motor would saturate. -/
def Mixer.step {α : Type} [Arith α] (p : MixerParams α) (inp : MixerInput α) : Motors α :=
  let thr := clip 0 1 inp.thrust
  let τ := inp.torque.map (clipSym 1)
  let r1 := p.f1.apply τ
  let r2 := p.f2.apply τ
  let r3 := p.f3.apply τ
  let r4 := p.f4.apply τ
  let hi := max (max r1 r2) (max r3 r4)
  let lo := min (min r1 r2) (min r3 r4)
  let k := Mixer.torqueScale thr lo hi
  ⟨clip 0 1 (thr + k * r1), clip 0 1 (thr + k * r2),
   clip 0 1 (thr + k * r3), clip 0 1 (thr + k * r4)⟩

end Flight
