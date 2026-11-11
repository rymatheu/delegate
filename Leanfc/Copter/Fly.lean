import Leanfc.Copter.Modes
import Leanfc.Copter.Land

/-!
# Copter.Fly (the vehicle layer's tick and its telemetry)

`step s cmds gcsSeen sensors = (s', motors)`, once per control tick:

1. the fixes of this tick are noted (their recency is part of the health);
2. boot: a vehicle started on the ground collects the gyro samples of its first second (motors
   off) and calibrates, then starts the estimator at the first tick with a position and a heading
   fix, level at that heading (`Controller.initAt`); home is set there unless locked;
3. the commands are applied in order (`Copter.Modes`), against the health at the start of the tick;
4. the failsafes: the ground station's HEARTBEAT older than FS_GCS_TIMEOUT (`gcsSeen` is the tick
   of the last one, from the services) with FS_GCS_ENABLE set, and the estimator unhealthy for 1 s
   (FS_EKF_ACTION), with ArduCopter's actions and texts (`events.cpp`, `ekf_check.cpp`): on the
   ground armed, a ground-station failsafe disarms; in the air it starts RTL (or LAND with its 4 s
   pause if RTL is refused) or LAND with the pause, by FS_GCS_ENABLE; the estimator failsafe lands
   with the pause in the modes that need a position;
5. the phase's law (`Copter.State`), one estimator step and one output, and the phase's
   transitions: spool-up → throttle ramp → liftoff (throttle at TKOFF_THR_MAX or a climb rate of a
   tenth of `nav.vMaxZ`, ArduCopter's `_AutoTakeoff::run`) → climb on the navigator → takeoff
   complete; a path's legs reached and its end (`Copter.Plan.pathDone`); a brake's stop; a wait's
   end; touchdown (`Copter.Land`); the spool-down after it, then the disarm (LAND, RTL, AUTO);
6. the automatic disarm: DISARM_DELAY on the ground armed without a takeoff.

In the batch start (`initAir`, no commands, no ground station) the phase is the mission's path
from the first tick and every tick is `Controller.step` with the parameter file's legs, so the
output equals that of the controller alone, bit for bit.
-/

namespace Copter

open Mavlink

/-- The ground-station failsafe's action on `s` (FS_GCS_ENABLE; ArduCopter `failsafe_gcs_on_event`). -/
def gcsFailsafe (h : Health) (s : State) : State :=
  if !s.armed then s.say 4 "GCS Failsafe"
  else if !s.flying then (disarm s).say 4 "GCS Failsafe - Disarming"
  else
    let s := s.say 4 "GCS Failsafe"
    let a := s.P.copter.fsGcs
    if a == 4 || a == 5 then landWithPause s
    else if a == 7 then
      match enterMode h s Mode.brake with
      | .ok s' => s'
      | .error _ => landWithPause s
    else
      match enterMode h s Mode.rtl with
      | .ok s' => s'
      | .error _ => landWithPause s

/-- The estimator failsafe's action (FS_EKF_ACTION; ArduCopter `failsafe_ekf_event`). -/
def ekfFailsafe (s : State) : State :=
  if !s.armed then s
  else if s.P.copter.fsEkf == 0 || !s.flying || !requiresPosition s.mode then s.say 2 "EKF Failsafe"
  else (landWithPause s).say 2 "EKF Failsafe: changed to Land Mode"

def failsafes (h : Health) (gcsSeen : Option Nat) (s : State) : State :=
  let k := s.P.copter
  let lost := k.fsGcs != 0 && match gcsSeen with
    | some t => s.tick > t + k.fsGcsTicks
    | none => false
  let s := if lost && !s.fsGcs then gcsFailsafe h { s with fsGcs := true }
    else if !lost && s.fsGcs then ({ s with fsGcs := false }).say 4 "GCS Failsafe Cleared" else s
  let n := if h.started && !h.ekfOk then s.ekfBadTicks + 1 else 0
  let s := { s with ekfBadTicks := n }
  if n ≥ k.ekfFsTicks && !s.fsEkf then ekfFailsafe { s with fsEkf := true }
  else if n == 0 && s.fsEkf then ({ s with fsEkf := false }).say 2 "EKF Failsafe Cleared"
  else s

/-- Touchdown spooled down: the disarm, which in AUTO completes the landing item and the mission. -/
def touchdownDone (s : State) : State :=
  let s := if s.mode == Mode.auto && s.cur ≥ 1 then { s with reached := some s.cur, missionState := .complete } else s
  disarm s

/-- One tick of the phase's law and its transitions. -/
def runPhase (s : State) (sens : Sensors) : State × Motors :=
  let P := s.P
  let k := P.copter
  let (est, e) := Controller.estimateStep P s.ctl.est sens
  let (qHat, _, pHat, vHat) := e
  -- on the ground the navigator follows the vehicle (a path starts where it is, nose as it points)
  let onGround (s : State) : State :=
    let h := Quat.headingVec qHat
    { s with ctl := { s.ctl with nav := Navigator.init pHat h, target := ⟨pHat, Vec3.zero, Vec3.zero, h, 0⟩ } }
  let idle (s : State) (m : R) : State × Motors :=
    let (ctl, mot) := Controller.idle s.ctl est m
    (onGround { s with ctl }, mot)
  let path (s : State) : State × Motors × NavState :=
    let (nav, tgt) := Navigator.step s.navP s.ctl.nav pHat P.dt
    let (ctl, mot) := Controller.track P s.ctl est e nav tgt
    ({ s with ctl }, mot, nav)
  match s.phase with
  | .ground => idle s (if s.armed then k.spinArm else 0)
  | .touchdown t =>
    let (s, m) := idle s k.spinArm
    (if t + 1 ≥ k.spoolTicks then touchdownDone s else { s with phase := .touchdown (t + 1) }, m)
  | .spool t goal =>
    let (s, m) := idle s k.spinArm
    (if t + 1 ≥ k.spoolTicks then { s with phase := .ramp k.spinArm goal } else { s with phase := .spool (t + 1) goal }, m)
  | .ramp thr goal =>
    let (ctl, m) := Controller.level P s.ctl est e (thr * 4 * P.vehicle.tMax) s.ctl.nav.heading
    let s := { s with ctl }
    if thr ≥ k.tkoffThrMax || -vHat.z ≥ P.nav.vMaxZ / 10 then
      -- liftoff: climb straight up from here on the navigator
      let s := { s with ctl := { s.ctl with nav := Navigator.init pHat s.ctl.nav.heading } }
      let item := if s.mode == Mode.auto then some s.cur else none
      (startPath s #[⟨{ pHat with z := goal }, .line, true⟩] (.takeoff item), m)
    else ({ s with phase := .ramp (thr + k.tkoffSlew) goal }, m)
  | .path goal =>
    let before := s.ctl.nav.leg
    let (s, m, nav) := path s
    let s := match goal with
      | .run first last =>
        let s := if nav.leg > before then { s with reached := some (first + before) } else s
        { s with cur := min (first + nav.leg) last }
      | _ => s
    (if nav.leg ≥ s.navP.legs.size then pathDone s goal else s, m)
  | .wait t next =>
    let (s, m, _) := path s
    (if t ≤ 1 then after s next else { s with phase := .wait (t - 1) next }, m)
  | .brake next =>
    let (nav, tgt) := Navigator.brake s.navP s.ctl.nav P.dt
    let (ctl, m) := Controller.track P s.ctl est e nav tgt
    let s := { s with ctl }
    (if nav.u ≤ 0 then after s next else s, m)
  | .descend =>
    let (cnt, maybe, down) := Land.detect P s.landCount s.motors vHat.z
    let hp := s.ctl.nav.pos
    let pSp : Vec3 := if maybe then pHat else ⟨hp.x, hp.y, pHat.z⟩
    let vd := Land.speed P (s.home.z - pHat.z)
    let tgt : Target := ⟨pSp, ⟨0, 0, vd⟩, Vec3.zero, s.ctl.nav.heading, 0⟩
    let ctl := if maybe then { s.ctl with posPI := ⟨⟨0, 0, s.ctl.posPI.integral.z⟩⟩, attPI := PI.init } else s.ctl
    let nav := { s.ctl.nav with pos := pSp, vel := Vec3.zero, u := 0, yawRate := 0 }
    let (ctl, m) := Controller.track P ctl est e nav tgt
    let s := { s with ctl, landCount := cnt }
    (if down then { s with phase := .touchdown 0 } else s, m)

/-- One tick of the vehicle (see the module comment). -/
def step (s : State) (cmds : Array Command) (gcsSeen : Option Nat) (sens : Sensors) : State × Motors :=
  let s := { s with results := #[], texts := #[], reached := none,
                    lastPosFix := if sens.position.isSome then some s.tick else s.lastPosFix,
                    lastHdgFix := if sens.heading.isSome then some s.tick else s.lastHdgFix }
  let s := match s.boot, sens.position, sens.heading with
    | .calibrating smp, _, _ =>
      let smp := smp.push sens.gyro
      { s with boot := if smp.size ≥ s.P.copter.calTicks then .waitFix smp else .calibrating smp }
    | .waitFix smp, some p, some hd =>
      let ctl := Controller.calibrate s.P smp (Controller.initAt s.P p (levelQuat hd) hd)
      { s with boot := .running s.tick, ctl, home := if s.homeLocked then s.home else p }
    | _, _, _ => s
  let h := Health.of s
  let s := cmds.foldl (apply h) s
  let (s, m) := match s.boot with
    | .running _ =>
      let s := failsafes h gcsSeen s
      runPhase s sens
    | _ => (s, ⟨0, 0, 0, 0⟩)
  -- DISARM_DELAY: armed on the ground with no takeoff under way
  let grounded := match s.phase with | .ground => s.armed | _ => false
  let g := if grounded then s.groundTicks + 1 else 0
  let s := if grounded && s.P.copter.disarmTicks > 0 && g ≥ s.P.copter.disarmTicks then disarm s
    else { s with groundTicks := g }
  ({ s with motors := m, tick := s.tick + 1 }, m)

/-- The telemetry of the contract (`Mavlink.Telemetry`) from the vehicle's state. -/
def telemetry (s : State) (origin : Origin) : Telemetry :=
  let (p, v, q) := Controller.estimate s.ctl
  let h := Health.of s
  { tick := s.tick, armed := s.armed, mode := s.mode, landed := s.landed, position := p, velocity := v,
    attitude := q, rates := Controller.rates s.ctl, origin, home := s.home, missionSeq := s.cur,
    missionState := s.missionState, reached := s.reached, target := s.ctl.target.pSp,
    targetHeading := s.ctl.target.heading, throttle := Land.throttle s.motors,
    health := sysStatus h (prearm h s.fsGcs).isNone, failsafe := s.fsGcs || s.fsEkf,
    results := s.results, texts := s.texts }

end Copter
