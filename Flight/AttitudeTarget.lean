import Flight.Types

/-!
# Acceleration to thrust and attitude target

Structured after the acceleration-to-attitude step shared by ArduPilot's `AC_AttitudeControl`
library (`AC_PosControl.cpp` converting acceleration to lean angles, and the thrust-vector input
of `AC_AttitudeControl.cpp`): the acceleration setpoint minus gravity is the specific force the
rotors must produce; its magnitude, scaled by the hover throttle, is the collective thrust, and
its direction fixes the desired roll and pitch, and the heading setpoint is passed through as the
desired yaw. As in ArduCopter's acceleration-to-lean-angle conversion, roll and pitch are resolved
in the frame of the vehicle's *current* heading, so that while a heading change is still in
progress the tilt acts in the direction the acceleration asks for.

Frames are NED, so gravity is `+g` along `z` and the thrust vector `t = a - g e_z` points up
(negative `z`) whenever the vertical acceleration setpoint is below `g`. The body down axis must
point along `-t`; rotating `-t` by minus the current heading gives `(sinθ cosφ, -sinφ, cosθ cosφ)` up to
scale, from which pitch and roll follow by `atan2`.

Simplified relative to ArduCopter: the target is ZYX Euler angles rather than a quaternion; roll
and pitch are each clipped to the lean limit instead of limiting the tilt of the thrust vector;
the hover throttle is a fixed parameter rather than learned in flight; and there is no angle boost,
battery-voltage compensation, or thrust-curve linearization.
-/

namespace Flight

/-- Parameters of the thrust and attitude target; defaults are untuned. -/
structure AttTargetParams (α : Type) [Arith α] where
  /-- Gravitational acceleration, meters per second squared. -/
  gravity : α := 9.80665
  /-- Normalized collective thrust that balances gravity. -/
  hoverThrottle : α := 0.5
  /-- Bound on the magnitude of desired roll and of desired pitch, radians (30 degrees). -/
  maxLean : α := 0.5235987755982988

/-- Input of the thrust and attitude target: acceleration setpoint, heading setpoint, and measured heading. -/
structure AttTargetInput (α : Type) where
  /-- Acceleration setpoint, meters per second squared (NED, without gravity). -/
  accelSp : Vec3 α
  /-- Heading setpoint, radians. -/
  yawSp : α
  /-- Measured heading, radians, in whose frame roll and pitch are resolved. -/
  yaw : α

/-- Output of the thrust and attitude target: collective thrust in `[0, 1]` and the desired attitude. -/
structure AttTargetOutput (α : Type) where
  /-- Normalized collective thrust. -/
  thrust : α
  /-- Desired attitude as ZYX Euler angles. -/
  attitude : Euler α
  deriving Repr

/-- Map an acceleration setpoint, heading setpoint and measured heading to collective thrust and desired roll, pitch and yaw. -/
def AttitudeTarget.step {α : Type} [Arith α] (p : AttTargetParams α) (inp : AttTargetInput α) :
    AttTargetOutput α :=
  let a := inp.accelSp
  let t : Vec3 α := ⟨a.x, a.y, a.z - p.gravity⟩
  let thrust := clip 0 1 (Vec3.norm t * p.hoverThrottle / p.gravity)
  let c := Arith.cos inp.yaw
  let s := Arith.sin inp.yaw
  -- Desired body down axis `-t`, expressed in the frame of the current heading.
  let fwd := -(c * t.x + s * t.y)
  let right := -(c * t.y - s * t.x)
  let down := -t.z
  let pitch := Arith.atan2 fwd down
  let roll := Arith.atan2 (-right) (Arith.sqrt (sq fwd + sq down))
  ⟨thrust, ⟨clipSym p.maxLean roll, clipSym p.maxLean pitch, inp.yawSp⟩⟩

end Flight
