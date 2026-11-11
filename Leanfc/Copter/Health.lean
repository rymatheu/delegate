import Leanfc.Copter.State

/-!
# Copter.Health (sensor and estimator health, pre-arm checks)

`of s` summarizes the vehicle's health from its state: the boot calibration, the estimator (started,
settled, its position covariance), the recency of the fixes, and attitude and motion at rest.
`prearm` turns it into ArduPilot's arming refusal texts (the first failing check; ArduPilot's
wording, `AP_Arming.cpp`, `AP_Arming_Copter.cpp`), and `sysStatus` into the SYS_STATUS health bits,
PREARM_CHECK among them (QGroundControl's "Ready to fly").

| check | fails while | text (sent as "PreArm: ..." or "Arm: ...") |
|---|---|---|
| gyros calibrated | the boot calibration has not finished | Gyros not calibrated |
| estimator started and settled | no fix to start at yet, or started less than 2 s ago | AHRS: EKF still initialising |
| position fix present | no position fix for 1 s | Need Position Estimate |
| heading fix present | no heading fix for 1 s | Compass not healthy |
| estimator healthy | north or east position 1σ above `copter.ekfPosMax` (EKF covariance) | EKF position variance |
| ground-station failsafe | the failsafe is on | GCS failsafe on |
| level | tilt above 30° (ArduCopter ANGLE_MAX default) | Leaning (an "Arm:" check) |
| at rest | estimated rate above 0.2 rad/s or speed above 0.5 m/s | Vehicle moving (leanfc's own) |

The thresholds of the last two are literals (cos 30° = 0.8660254 on the body z axis's down
component, 0.2 rad/s, 0.5 m/s), as ArduPilot's are constants of its source.
-/

namespace Copter

open Mavlink

structure Health where
  calibrated : Bool
  started : Bool
  settled : Bool
  posFix : Bool
  hdgFix : Bool
  ekfOk : Bool
  level : Bool
  still : Bool
  deriving Repr, Inhabited

/-- A fix seen at `t?` is present at `now` if it is less than `n` ticks old. -/
def recent (now n : Nat) : Option Nat → Bool
  | some t => now < t + n
  | none => false

/-- The estimator's position covariance is within `copter.ekfPosMax` (north and east). The fixed
estimator has no covariance and counts as healthy while its position fixes arrive. -/
def ekfHealthy (P : Params) (st : _root_.State) : Bool :=
  match st.est with
  | .ekf e => e.P[6][6] ≤ P.copter.ekfPosMax2 && e.P[7][7] ≤ P.copter.ekfPosMax2
  | .fixed _ _ => true

def Health.of (s : State) : Health :=
  let k := s.P.copter
  let (since, started) := match s.boot with
    | .running t => (t, true)
    | _ => (0, false)
  let (_, v, q) := Controller.estimate s.ctl
  let w := Controller.rates s.ctl
  { calibrated := match s.boot with | .calibrating _ => false | _ => true,
    started,
    settled := started && s.tick ≥ since + k.settleTicks,
    posFix := recent s.tick k.fixTicks s.lastPosFix,
    hdgFix := recent s.tick k.fixTicks s.lastHdgFix,
    ekfOk := started && ekfHealthy s.P s.ctl,
    level := started && 1 - 2 * (q.x * q.x + q.y * q.y) ≥ (0.8660254 : R),
    still := started && Vec3.dot w w ≤ (0.04 : R) && Vec3.dot v v ≤ (0.25 : R) }

/-- The estimator can be trusted for position control (ArduCopter `position_ok`). -/
def Health.positionOk (h : Health) : Bool := h.started && h.ekfOk

/-- The first failing pre-arm check, as ArduPilot words it ("PreArm: ..." or "Arm: ..."). -/
def prearm (h : Health) (fsGcs : Bool) : Option String :=
  if !h.calibrated then some "PreArm: Gyros not calibrated"
  else if !h.started || !h.settled then some "PreArm: AHRS: EKF still initialising"
  else if !h.posFix then some "PreArm: Need Position Estimate"
  else if !h.hdgFix then some "PreArm: Compass not healthy"
  else if !h.ekfOk then some "PreArm: EKF position variance"
  else if fsGcs then some "PreArm: GCS failsafe on"
  else if !h.level then some "Arm: Leaning"
  else if !h.still then some "PreArm: Vehicle moving"
  else none

/-- SYS_STATUS onboard_control_sensors_health (MAV_SYS_STATUS_SENSOR bits): gyro and accelerometer
when calibrated, GPS with a recent position fix, AHRS when the estimator is started and healthy,
PREARM_CHECK when `prearm` passes, the control bits always. -/
def sysStatus (h : Health) (armable : Bool) : UInt32 :=
  let b (c : Bool) (bit : UInt32) : UInt32 := if c then bit else 0
  b h.calibrated 0x3 ||| b h.posFix 0x20 ||| 0xFC00 ||| b (h.started && h.ekfOk) 0x200000 |||
    b armable 0x10000000

end Copter
