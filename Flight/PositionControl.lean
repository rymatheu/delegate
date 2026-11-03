import Flight.Pid

/-!
# Position controller

Structured after the position controller of ArduPilot's `AC_AttitudeControl` library
(`AC_PosControl.cpp`): a proportional loop turns position error into a velocity correction, which
is added to the navigator's velocity feed-forward to give the velocity setpoint, which is limited,
and a PID loop turns velocity error into an acceleration, which is added to the navigator's
acceleration feed-forward to give the acceleration setpoint, which is limited again.
Horizontal and vertical axes have separate gains and limits, as in ArduCopter.

Simplified relative to `AC_PosControl`: the position loop is a plain proportional gain rather than
a square-root controller; the limit applies to the sum of feed-forward and correction rather than
to the correction alone (and likewise for the acceleration); there is no input shaping, no offsets, no terrain or EKF-reset handling, and no gain scaling; limits are applied per
axis (a box) rather than to the horizontal vector norm; the vertical loop outputs an
acceleration directly instead of passing through a separate acceleration PID to throttle; the
integrators are not frozen when the acceleration limit is hit, only clamped; and the derivative is
unfiltered.
-/

namespace Flight

/-- Position-controller parameters; defaults are in the range ArduCopter ships with and are untuned. -/
structure PosParams (α : Type) [Arith α] where
  /-- Horizontal position gain, per second. -/
  posGainXY : α := 1.0
  /-- Vertical position gain, per second. -/
  posGainZ : α := 1.0
  /-- Bound on each horizontal velocity-setpoint component, meters per second. -/
  maxSpeedXY : α := 5.0
  /-- Bound on the vertical velocity-setpoint magnitude, meters per second. -/
  maxSpeedZ : α := 2.5
  /-- Horizontal velocity PID; output is acceleration in meters per second squared. -/
  velXY : PidGains α := { kp := 2.0, ki := 1.0, kd := 0.25, iMax := 2.0 }
  /-- Vertical velocity PID; output is acceleration in meters per second squared. -/
  velZ : PidGains α := { kp := 4.0, ki := 2.0, kd := 0.0, iMax := 3.0 }
  /-- Bound on each horizontal acceleration-setpoint component, meters per second squared. -/
  maxAccelXY : α := 5.0
  /-- Bound on the vertical acceleration-setpoint magnitude, meters per second squared (below gravity, so thrust always points up). -/
  maxAccelZ : α := 5.0

/-- Position-controller memory: one velocity PID per world axis. -/
structure PosState (α : Type) where
  /-- North velocity PID memory. -/
  vx : PidState α
  /-- East velocity PID memory. -/
  vy : PidState α
  /-- Down velocity PID memory. -/
  vz : PidState α
  deriving Repr

/-- Position-controller memory before the first step. -/
def PosState.init {α : Type} [Arith α] : PosState α := ⟨PidState.init, PidState.init, PidState.init⟩

/-- Position-controller input: measured position and velocity, the position setpoint with velocity and acceleration feed-forward, and the time step. -/
structure PosInput (α : Type) where
  /-- Measured position, meters (NED). -/
  pos : Vec3 α
  /-- Measured velocity, meters per second (NED). -/
  vel : Vec3 α
  /-- Position setpoint from the navigator, meters (NED). -/
  posSp : Vec3 α
  /-- Velocity feed-forward from the navigator, meters per second (NED). -/
  velSp : Vec3 α
  /-- Acceleration feed-forward from the navigator, meters per second squared (NED, without gravity). -/
  accSp : Vec3 α
  /-- Time step, seconds. -/
  dt : α

/-- The limited velocity setpoint: the feed-forward plus the proportional correction of the position error. -/
def PositionControl.velocitySetpoint {α : Type} [Arith α] (p : PosParams α)
    (pos posSp velSp : Vec3 α) : Vec3 α :=
  let e := posSp - pos
  ⟨clipSym p.maxSpeedXY (velSp.x + p.posGainXY * e.x),
   clipSym p.maxSpeedXY (velSp.y + p.posGainXY * e.y),
   clipSym p.maxSpeedZ (velSp.z + p.posGainZ * e.z)⟩

/-- One position-controller step: feed-forward and position error to limited velocity setpoint, then feed-forward and velocity PID to limited acceleration setpoint (NED, without gravity). -/
def PositionControl.step {α : Type} [Arith α] (p : PosParams α) (s : PosState α)
    (inp : PosInput α) : PosState α × Vec3 α :=
  let ev := PositionControl.velocitySetpoint p inp.pos inp.posSp inp.velSp - inp.vel
  let (sx, ax) := Pid.step p.velXY s.vx ev.x inp.dt
  let (sy, ay) := Pid.step p.velXY s.vy ev.y inp.dt
  let (sz, az) := Pid.step p.velZ s.vz ev.z inp.dt
  (⟨sx, sy, sz⟩, ⟨clipSym p.maxAccelXY (inp.accSp.x + ax), clipSym p.maxAccelXY (inp.accSp.y + ay),
    clipSym p.maxAccelZ (inp.accSp.z + az)⟩)

end Flight
