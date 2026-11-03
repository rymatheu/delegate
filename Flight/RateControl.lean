import Flight.Pid

/-!
# Body-rate controller

Structured after the rate loop of ArduPilot's `AC_AttitudeControl` library
(`AC_AttitudeControl_Multi.cpp`, which runs one `AC_PID` per body axis): body-rate error on each
axis goes through a PID whose output is a normalized torque, clipped to `[-1, 1]`.

Simplified relative to ArduCopter: no target, error or derivative filters, no feed-forward, no
slew-rate limiting or gain backoff, no landed-gain scaling, and anti-windup by integrator clamping
only (the integrator is not frozen when the mixer saturates).
-/

namespace Flight

/-- Rate-controller parameters; defaults are in the range ArduCopter ships with and are untuned. -/
structure RateParams (α : Type) [Arith α] where
  /-- Roll-rate PID; input rad/s, output normalized torque. -/
  roll : PidGains α := { kp := 0.135, ki := 0.135, kd := 0.0036, iMax := 0.5 }
  /-- Pitch-rate PID; input rad/s, output normalized torque. -/
  pitch : PidGains α := { kp := 0.135, ki := 0.135, kd := 0.0036, iMax := 0.5 }
  /-- Yaw-rate PID; input rad/s, output normalized torque. -/
  yaw : PidGains α := { kp := 0.2, ki := 0.02, kd := 0.0, iMax := 0.5 }

/-- Rate-controller memory: one PID per body axis. -/
structure RateState (α : Type) where
  /-- Roll-rate PID memory. -/
  roll : PidState α
  /-- Pitch-rate PID memory. -/
  pitch : PidState α
  /-- Yaw-rate PID memory. -/
  yaw : PidState α
  deriving Repr

/-- Rate-controller memory before the first step. -/
def RateState.init {α : Type} [Arith α] : RateState α := ⟨PidState.init, PidState.init, PidState.init⟩

/-- Rate-controller input: measured body rates, body-rate setpoint, and time step. -/
structure RateInput (α : Type) where
  /-- Measured body rates `(p, q, r)`, radians per second. -/
  rates : Vec3 α
  /-- Body-rate setpoint `(p, q, r)`, radians per second. -/
  rateSp : Vec3 α
  /-- Time step, seconds. -/
  dt : α

/-- One rate-controller step: a PID per axis on body-rate error, giving normalized torques `(roll, pitch, yaw)` in `[-1, 1]`. -/
def RateControl.step {α : Type} [Arith α] (p : RateParams α) (s : RateState α)
    (inp : RateInput α) : RateState α × Vec3 α :=
  let e := inp.rateSp - inp.rates
  let (sr, ur) := Pid.step p.roll s.roll e.x inp.dt
  let (sp, up) := Pid.step p.pitch s.pitch e.y inp.dt
  let (sy, uy) := Pid.step p.yaw s.yaw e.z inp.dt
  (⟨sr, sp, sy⟩, ⟨clipSym 1 ur, clipSym 1 up, clipSym 1 uy⟩)

end Flight
