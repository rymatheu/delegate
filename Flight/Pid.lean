import Flight.Types

/-!
# Scalar PID with a clamped integrator

A single-axis PID shared by the velocity loop (`Flight.PositionControl`) and the body-rate loop
(`Flight.RateControl`), structured after the PID object of ArduPilot's `AC_PID` library: the
integrator accumulates `ki * error * dt` and is clamped to `[-iMax, iMax]`, the derivative acts on
the error, and the output is the sum of the three terms.

Simplified relative to `AC_PID`: no low-pass filters on the target, error or derivative, no
feed-forward term, no slew-rate limiter, no notch filters, and anti-windup is by clamping alone
(the integrator is not frozen when a downstream limit is hit). The derivative is zero on the first
step and whenever `dt ≤ 0`, so there is no derivative kick at start-up.
-/

namespace Flight

/-- Gains and integrator limit of a scalar PID; zero by default so every use states its own values. -/
structure PidGains (α : Type) [Arith α] where
  /-- Proportional gain. -/
  kp : α := 0
  /-- Integral gain, per second. -/
  ki : α := 0
  /-- Derivative gain, seconds. -/
  kd : α := 0
  /-- Bound on the magnitude of the integral term. -/
  iMax : α := 0

/-- Memory of a scalar PID: the integral term, the previous error, and whether a previous error exists. -/
structure PidState (α : Type) where
  /-- Current value of the integral term (already multiplied by `ki`). -/
  integral : α
  /-- Error seen on the previous step. -/
  prevError : α
  /-- `true` once at least one step has been taken, so `prevError` is meaningful. -/
  primed : Bool
  deriving Repr

/-- The PID memory before the first step. -/
def PidState.init {α : Type} [Arith α] : PidState α := ⟨0, 0, false⟩

/-- One PID step: given the error and the time step, return the updated memory and the unclipped output `kp e + I + kd de/dt`. -/
def Pid.step {α : Type} [Arith α] (g : PidGains α) (s : PidState α) (err dt : α) :
    PidState α × α :=
  let integral := clipSym g.iMax (s.integral + g.ki * err * dt)
  let deriv : α := if s.primed then (if 0 < dt then (err - s.prevError) / dt else 0) else 0
  (⟨integral, err, true⟩, g.kp * err + integral + g.kd * deriv)

end Flight
