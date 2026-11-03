import Flight.Navigator
import Flight.PositionControl
import Flight.AttitudeTarget
import Flight.AttitudeControl
import Flight.RateControl
import Flight.Mixer

/-!
# The composed controller

A minimal quadcopter flight controller structured after the ArduCopter stack. One tick runs the
cascade

  navigator (`AC_WPNav`) → position control (`AC_PosControl`) → acceleration to thrust and
  attitude target → attitude control (`AC_AttitudeControl`) → rate control
  (`AC_AttitudeControl_Multi`, `AC_PID`) → quad X mixer (`AP_MotorsMatrix`)

and every stage is a pure function: memoryless stages are `I → O`, stateful ones are
`S → I → S × O`, and the whole controller is `State → SimInput → State × Motors`.

What was simplified relative to ArduCopter, overall (each file lists its own details):
* all loops run at one rate, set by the `dt` of each input sample, with no scheduler;
* the navigator's path is straight legs with blended corners and a trapezoidal speed profile, not
  S-curves or splines, its velocity and acceleration are the only feed-forward between stages,
  and there is no input shaping;
* no filters on PID terms, no notch filters, no EKF interaction or estimator resets;
* attitude is handled as ZYX Euler angles with proportional angle loops, not quaternions and
  square-root controllers;
* the vertical channel ends at an acceleration setpoint, not a separate acceleration-to-throttle PID,
  and hover throttle is a fixed parameter;
* anti-windup is by integrator clamping only;
* the mixer uses a single common torque scale instead of ArduCopter's prioritized scheme;
* no arming, take-off, landing, flight modes, failsafes, geofence, or parameter tables;
* gains are defaults in the range ArduCopter ships with, untuned for any airframe.
-/

namespace Flight

namespace Controller

/-- Parameters of the whole controller, one record per component. -/
structure Params (α : Type) [Arith α] where
  /-- Waypoint navigator. -/
  nav : NavParams α := {}
  /-- Position and velocity loops. -/
  pos : PosParams α := {}
  /-- Acceleration to thrust and attitude target. -/
  target : AttTargetParams α := {}
  /-- Angle loops. -/
  att : AttCtlParams α := {}
  /-- Body-rate loops. -/
  rate : RateParams α := {}
  /-- Motor mixer. -/
  mixer : MixerParams α := {}

/-- Memory of the whole controller: the three stateful components. -/
structure State (α : Type) where
  /-- Navigator memory. -/
  nav : NavState α
  /-- Position-controller memory. -/
  pos : PosState α
  /-- Rate-controller memory. -/
  rate : RateState α
  deriving Repr

/-- Controller memory before the first tick. -/
def State.init {α : Type} [Arith α] : State α := ⟨NavState.init, PosState.init, RateState.init⟩

/-- Every intermediate signal of one tick, for logging and for stating properties of the cascade. -/
structure Trace (α : Type) where
  /-- Navigator output. -/
  nav : NavOutput α
  /-- Acceleration setpoint from the position controller. -/
  accelSp : Vec3 α
  /-- Collective thrust and desired attitude. -/
  target : AttTargetOutput α
  /-- Body-rate setpoint from the attitude controller. -/
  rateSp : Vec3 α
  /-- Normalized torques from the rate controller. -/
  torque : Vec3 α
  /-- Motor commands from the mixer. -/
  motors : Motors α
  deriving Repr

/-- One controller tick with every intermediate signal exposed; `step` is its projection onto the motors. -/
def stepTrace {α : Type} [Arith α] (p : Params α) (s : State α) (inp : SimInput α) :
    State α × Trace α :=
  let (navS, navOut) := Navigator.step p.nav s.nav inp.pos inp.dt
  let (posS, accelSp) :=
    PositionControl.step p.pos s.pos ⟨inp.pos, inp.vel, navOut.posSp, navOut.velSp, navOut.accSp, inp.dt⟩
  let target := AttitudeTarget.step p.target ⟨accelSp, navOut.yawSp, inp.att.yaw⟩
  let rateSp := AttitudeControl.step p.att ⟨inp.att, target.attitude⟩
  let (rateS, torque) := RateControl.step p.rate s.rate ⟨inp.rates, rateSp, inp.dt⟩
  let motors := Mixer.step p.mixer ⟨target.thrust, torque⟩
  (⟨navS, posS, rateS⟩, ⟨navOut, accelSp, target, rateSp, torque, motors⟩)

/-- One controller tick: navigator, position control, attitude target, attitude control, rate control and mixer, in that order. -/
def step {α : Type} [Arith α] (p : Params α) (s : State α) (inp : SimInput α) :
    State α × Motors α :=
  let (s', tr) := stepTrace p s inp
  (s', tr.motors)

end Controller

end Flight
