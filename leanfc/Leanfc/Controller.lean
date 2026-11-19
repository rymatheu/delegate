import Leanfc.Navigator
import Leanfc.AttitudeFilter
import Leanfc.NavFilter
import Leanfc.EKF
import Leanfc.Position
import Leanfc.Attitude
import Leanfc.Mixer
import Leanfc.Copter.Params

/-!
# Controller

The one tick: estimator → navigator (position target, feedforward, heading setpoint and yaw-rate
feedforward) → position → attitude → mixer; pyfc
`controller.FlightController.step` with the navigator of `mission.py` folded in (DESIGN.md order:
the navigator sees the position estimate of this tick, where pyfc `mission.py` passes the
previous tick's). The estimator is the parameter `estimator`: `fixed` (attitude filter → nav
filter) or `ekf` (`EKF.step`); the state carries the active one's state and `step` dispatches
once. `calibrate` sets the gyro bias to the mean of samples taken at rest (pyfc
`FlightController.calibrate`); the EKF also sets its gyro-bias prior from the sample count.

`step` is the composition of three parts that the vehicle layer (`Leanfc/Copter/*`) also uses
on their own: `estimateStep` (the estimator), a target (here `Navigator.step`; the vehicle layer
may brake the navigator or command a descent instead) and `track` (position → attitude → mixer
from a target). Two more output laws serve the ground phases: `level` (attitude held level at a
heading with a given collective thrust: the takeoff throttle ramp) and `idle` (every motor at
one command, both PI integrators reset: disarmed or armed on the ground). `step` computes
exactly what it computed before this split.
-/

/-- Which estimator the controller runs (parameter `estimator fixed|ekf`). -/
inductive Estimator where
  | fixed
  | ekf
  deriving Inhabited, Repr, BEq

/-- One tick of sensor readings. Fixes are `none` on ticks without one; the heading is a unit
vector (cos ψ, sin ψ). -/
structure Sensors where
  gyro : Vec3
  accel : Vec3
  heading : Option (R × R)
  position : Option Vec3
  velocity : Option Vec3
  deriving Inhabited, Repr

/-- The initial heading setpoint as a unit vector (cos ψ, sin ψ); the navigator turns it toward the
path (`nav.yawBehavior` 1) or holds it (0). Positions come from the navigator. -/
structure Setpoint where
  hc : R
  hs : R
  deriving Inhabited, Repr

/-- Everything the controller is configured with, built once at startup from the parameter file
(`ParamFile.load`); the derived constants inside the module params are computed there too. -/
structure Params where
  vehicle : Vehicle
  /-- control period, s -/
  dt : R
  /-- interval between position fixes the navigation-filter gains are tuned for, s -/
  dtFix : R
  estimator : Estimator
  attFilter : AttFilterParams
  navFilter : NavFilterParams
  ekf : EKF.Params
  nav : NavParams
  /-- where the vehicle starts (NED, m); the navigator's first leg starts here -/
  start : Vec3
  /-- the mission as the file gives it (the navigator's legs, in `nav`, are built from it) -/
  waypoints : Array Waypoint
  setpoint : Setpoint
  position : PositionParams
  attitude : AttitudeParams
  /-- the vehicle layer's parameters (arming, takeoff, landing, failsafes; `Leanfc/Copter/*`) -/
  copter : CopterParams
  deriving Inhabited, Repr

/-- The active estimator's state. -/
inductive EstState where
  | fixed (att : AttFilterState) (nav : NavFilterState)
  | ekf (s : EKF.State)
  deriving Inhabited, Repr

structure State where
  est : EstState
  nav : NavState
  posPI : PIState
  attPI : PIState
  /-- The navigator's output of the last tick (for logging; not read by `step`). -/
  target : Target
  deriving Inhabited, Repr

namespace Controller

/-- Controller at rest at the start point, level, heading 0, zero bias, navigator at the start of the first
leg with the heading setpoint `P.setpoint`, with the estimator of `P.estimator`. -/
def init (P : Params) : State :=
  { est := match P.estimator with
      | .fixed => .fixed (AttitudeFilter.init Quat.identity) (NavFilter.init P.start)
      | .ekf => .ekf (EKF.init P.ekf P.start Quat.identity),
    nav := Navigator.init P.start (P.setpoint.hc, P.setpoint.hs), posPI := PI.init, attPI := PI.init,
    target := ⟨P.start, Vec3.zero, Vec3.zero, (P.setpoint.hc, P.setpoint.hs), 0⟩ }

/-- Gyro bias ← mean of the gyro samples taken at rest (unchanged if there are none). -/
def calibrate (P : Params) (samples : Array Vec3) (st : State) : State :=
  if samples.isEmpty then st else
  match st.est with
  | .fixed af nf =>
    let (sum, n) := samples.foldl (fun (acc : Vec3 × R) g => (acc.1 + g, acc.2 + 1)) (Vec3.zero, 0)
    { st with est := .fixed { af with bias := Vec3.div sum n } nf }
  | .ekf e => { st with est := .ekf (EKF.calibrate P.ekf samples e) }

/-- The active estimator's p̂, v̂, q̂ (for logging). -/
def estimate (st : State) : Vec3 × Vec3 × Quat :=
  match st.est with
  | .fixed af nf => (nf.p, nf.v, af.q)
  | .ekf e => (e.p, e.v, e.q)

/-- The estimator's output of one tick: q̂, ω̂ (filtered body rates), p̂, v̂. -/
abbrev Estimate := Quat × Vec3 × Vec3 × Vec3

/-- The estimator part of a tick (dispatched once on the active estimator). -/
def estimateStep (P : Params) (est : EstState) (s : Sensors) : EstState × Estimate :=
  match est with
  | .fixed af nf =>
    let (af, (qHat, omegaHat)) := AttitudeFilter.step P.attFilter af s.gyro s.accel s.heading P.dt
    let (nf, (pHat, vHat)) := NavFilter.step P.navFilter nf qHat s.accel s.position s.velocity P.dt
    (EstState.fixed af nf, (qHat, omegaHat, pHat, vHat))
  | .ekf e =>
    let (e, out) := EKF.step P.ekf e s.gyro s.accel s.heading s.position s.velocity
    (EstState.ekf e, out)

/-- Position → attitude → mixer from the target `tgt` (the new navigator state `nav` is stored). -/
def track (P : Params) (st : State) (est : EstState) (e : Estimate) (nav : NavState) (tgt : Target) :
    State × Motors :=
  let (qHat, omegaHat, pHat, vHat) := e
  let (posPI, (thrust, qDes)) :=
    Position.step P.vehicle P.position st.posPI tgt.pSp tgt.vFF tgt.aFF tgt.heading pHat vHat
  let (attPI, torque) := Attitude.step P.vehicle P.attitude st.attPI qDes qHat omegaHat tgt.yawRate
  ({ est, nav := nav, posPI := posPI, attPI := attPI, target := tgt },
   Mixer.step P.vehicle thrust torque)

/-- One 400 Hz tick. -/
def step (P : Params) (st : State) (s : Sensors) : State × Motors :=
  let (est, e) := estimateStep P st.est s
  let (nav, tgt) := Navigator.step P.nav st.nav e.2.2.1 P.dt
  track P st est e nav tgt

/-- Attitude held level with the nose along `heading`, collective thrust `thrust` (N): the
takeoff throttle ramp. The position integrator is reset; the rate integrator is reset as
ArduCopter resets it before liftoff (`reset_rate_controller_I_terms`). -/
def level (P : Params) (st : State) (est : EstState) (e : Estimate) (thrust : R) (heading : R × R) :
    State × Motors :=
  let (qHat, omegaHat, _, _) := e
  let qDes := Quat.fromThrustHeading ⟨0, 0, 1⟩ heading
  let (_, torque) := Attitude.step P.vehicle P.attitude PI.init qDes qHat omegaHat 0
  ({ st with est, posPI := PI.init, attPI := PI.init }, Mixer.step P.vehicle thrust torque)

/-- Every motor at command `m` (0 disarmed, MOT_SPIN_ARM armed on the ground) with both
integrators reset; the estimator keeps running. -/
def idle (st : State) (est : EstState) (m : R) : State × Motors :=
  ({ st with est, posPI := PI.init, attPI := PI.init }, ⟨m, m, m, m⟩)

/-- The estimator started at position `p` with attitude `q` (the vehicle on the ground after its
boot calibration), the navigator holding `p` with the heading setpoint `h`. -/
def initAt (P : Params) (p : Vec3) (q : Quat) (h : R × R) : State :=
  { est := match P.estimator with
      | .fixed => .fixed (AttitudeFilter.init q) (NavFilter.init p)
      | .ekf => .ekf (EKF.init P.ekf p q),
    nav := Navigator.init p h, posPI := PI.init, attPI := PI.init,
    target := ⟨p, Vec3.zero, Vec3.zero, h, 0⟩ }

/-- The active estimator's filtered body rates ω̂ (rad/s). -/
def rates (st : State) : Vec3 :=
  match st.est with
  | .fixed af _ => af.omega
  | .ekf e => e.omega

end Controller
