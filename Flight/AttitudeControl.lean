import Flight.Types

/-!
# Attitude controller

Structured after the angle loop of ArduPilot's `AC_AttitudeControl` library
(`AC_AttitudeControl.cpp`): the attitude error on each axis, times an angle gain, is the body-rate
setpoint, limited to a maximum rate. The heading error is wrapped to `(-π, π]` so the vehicle turns
the short way.

Simplified relative to ArduCopter: ArduCopter represents attitude and attitude error as
quaternions, separates the thrust-vector (roll/pitch) correction from the heading correction, and
uses a square-root controller with acceleration limits plus body-rate feed-forward from input
shaping. Here the error is taken directly between ZYX Euler angles and fed to a plain proportional
gain, and the Euler-angle error is used as a body-rate error without the kinematic transformation
from Euler rates to body rates (accurate near level flight). Roll and pitch rates are limited per
axis rather than as a 2-vector.
-/

namespace Flight

/-- Attitude-controller parameters; defaults are in the range ArduCopter ships with and are untuned. -/
structure AttCtlParams (α : Type) [Arith α] where
  /-- Roll angle gain, per second. -/
  rollGain : α := 4.5
  /-- Pitch angle gain, per second. -/
  pitchGain : α := 4.5
  /-- Yaw angle gain, per second. -/
  yawGain : α := 4.5
  /-- Bound on the roll-rate and pitch-rate setpoints, radians per second (about 200 degrees per second). -/
  maxRollPitchRate : α := 3.5
  /-- Bound on the yaw-rate setpoint, radians per second (about 90 degrees per second). -/
  maxYawRate : α := 1.57

/-- Attitude-controller input: measured and desired attitude. -/
structure AttCtlInput (α : Type) where
  /-- Measured attitude, ZYX Euler angles. -/
  current : Euler α
  /-- Desired attitude, ZYX Euler angles. -/
  desired : Euler α

/-- Map attitude error to a limited body-rate setpoint `(p, q, r)`, with the yaw error wrapped to `(-π, π]`. -/
def AttitudeControl.step {α : Type} [Arith α] (p : AttCtlParams α) (inp : AttCtlInput α) : Vec3 α :=
  let eRoll := inp.desired.roll - inp.current.roll
  let ePitch := inp.desired.pitch - inp.current.pitch
  let eYaw := wrapAngle (inp.desired.yaw - inp.current.yaw)
  ⟨clipSym p.maxRollPitchRate (p.rollGain * eRoll),
   clipSym p.maxRollPitchRate (p.pitchGain * ePitch),
   clipSym p.maxYawRate (p.yawGain * eYaw)⟩

end Flight
