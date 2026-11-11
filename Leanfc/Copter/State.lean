import Leanfc.Mavlink.Vehicle

/-!
# Copter.State (the vehicle layer's state)

The vehicle layer wraps the flight law (`Controller`) in ArduCopter's vehicle logic: arming, flight
modes, takeoff, missions, landing, failsafes. This module holds its data and the small state
updates every other `Copter` module uses; `Copter.Plan` (missions and paths), `Copter.Modes`
(commands and mode changes) and `Copter.Fly` (the tick and the telemetry) are the logic.

**Phases.** What the vehicle does inside its mode is a `Phase`, and every phase has one output law
(`Copter.Fly`):

| phase | law | landed state |
|---|---|---|
| `ground` | every motor 0 (disarmed) or MOT_SPIN_ARM (armed) | on ground |
| `spool t goal` | MOT_SPIN_ARM for MOT_SPOOL_TIME, then `ramp` | on ground |
| `ramp thr goal` | level attitude, collective `thr` rising by dt/TKOFF_SLEW_TIME per tick, until liftoff | on ground |
| `path goal` | the navigator on the legs `navP` (a finished navigator holds its target) | takeoff for `goal = takeoff`, else in air |
| `brake next` | the navigator braking along its path at aMax, then `next` | in air |
| `wait t next` | holding the target for `t` more ticks, then `next` | landing if `next` is LAND's descent, else in air |
| `descend` | the landing descent (`Copter.Land`) | landing |
| `touchdown t` | MOT_SPIN_ARM for MOT_SPOOL_TIME, then disarm | on ground |

The landed state (MAV_LANDED_STATE) is a function of the phase (`landedOf`), as ArduCopter derives
it from `land_complete` and the mode's taking-off and landing states.

**Boot.** A vehicle that starts on the ground first calibrates its gyros (the samples of the
first second, at rest), then waits for a position and a heading fix and starts the estimator there
(`Boot`); the batch start (`initAir`) is already running.

All positions are NED m from the origin, as in `Mavlink.Vehicle`.
-/

namespace Copter

open Mavlink

/-- What a navigator path is for, which decides what happens when it is done. -/
inductive Goal where
  /-- GUIDED go-to, change of altitude, or a plain hold: hold the end point -/
  | hold
  /-- AUTO: mission items `first` .. `last` (1-based), one leg each -/
  | run (first last : Nat)
  /-- takeoff climb; `item` is the AUTO NAV_TAKEOFF item, none for a GUIDED takeoff -/
  | takeoff (item : Option Nat)
  /-- AUTO NAV_LAND with a location: fly there at the current altitude, then descend -/
  | landAt
  /-- RTL (mode, or AUTO item `item`): climb and return over home, wait RTL_LOIT_TIME, descend -/
  | home (item : Option Nat)
  deriving Repr, BEq, Inhabited

/-- What follows a brake or a wait. -/
inductive After where
  | hold
  | fly (wps : Array Waypoint) (goal : Goal)
  /-- AUTO: start mission item `i` (1-based) -/
  | item (i : Nat)
  | descend
  /-- RTL's final descent (after its wait above home, which is not yet a landing) -/
  | rtlDescend
  /-- hold `ticks`, then descend (ArduCopter's land with pause) -/
  | pause (ticks : Nat)
  /-- RTL: the climb-and-return path, for the AUTO item if any -/
  | home (item : Option Nat)
  deriving Repr, Inhabited

/-- What the vehicle does inside its mode; see the module comment for the laws. -/
inductive Phase where
  | ground
  | spool (t : Nat) (goal : R)
  | ramp (thr : R) (goal : R)
  | path (goal : Goal)
  | brake (next : After)
  | wait (t : Nat) (next : After)
  | descend
  | touchdown (t : Nat)
  deriving Repr, Inhabited

/-- The start-up sequence of a vehicle started on the ground. -/
inductive Boot where
  /-- gyro samples for the calibration (motors off, at rest) -/
  | calibrating (samples : Array Vec3)
  /-- calibrated; waiting for a position and a heading fix to start the estimator at -/
  | waitFix (samples : Array Vec3)
  /-- the estimator runs since tick `since` -/
  | running (since : Nat)
  deriving Repr, Inhabited

structure State where
  P : Params
  /-- ticks since start -/
  tick : Nat := 0
  boot : Boot
  ctl : _root_.State
  /-- the legs being flown: `P.nav` with a run-time mission (`Navigator.withLegs`) -/
  navP : NavParams
  /-- where the current path started and its waypoints (to rebuild it at a new speed) -/
  pathStart : Vec3
  pathWps : Array Waypoint := #[]
  armed : Bool := false
  /-- ArduCopter mode number -/
  mode : Nat := Mode.stabilize
  phase : Phase := .ground
  home : Vec3
  /-- set by DO_SET_HOME: arming does not move it (ArduPilot's locked home) -/
  homeLocked : Bool := false
  /-- WP_SPD, or the speed of DO_CHANGE_SPEED -/
  speed : R
  mission : Array MissionCmd := #[]
  /-- current mission item, 1-based; 0 none -/
  cur : Nat := 0
  missionState : MissionState := .noMission
  /-- the item reached this tick (MISSION_ITEM_REACHED) -/
  reached : Option Nat := none
  /-- the last motor commands -/
  motors : Motors := ⟨0, 0, 0, 0⟩
  /-- touchdown detector count (`Copter.Land`) -/
  landCount : Nat := 0
  /-- ticks armed on the ground (DISARM_DELAY) -/
  groundTicks : Nat := 0
  /-- ticks of bad estimator health (FS_EKF_ACTION) -/
  ekfBadTicks : Nat := 0
  fsGcs : Bool := false
  fsEkf : Bool := false
  /-- ticks of the last position and heading fixes -/
  lastPosFix : Option Nat := none
  lastHdgFix : Option Nat := none
  results : Array CommandResult := #[]
  texts : Array (Severity × String) := #[]

/-- The landed state of a phase (MAV_LANDED_STATE). -/
def landedOf : Phase → Landed
  | .ground | .spool _ _ | .ramp _ _ | .touchdown _ => .onGround
  | .path (.takeoff _) => .takeoff
  | .descend | .wait _ .descend | .wait _ (.pause _) => .landing
  | _ => .inAir

def State.landed (s : State) : Landed := landedOf s.phase

/-- Level attitude with the nose along `(c, s)`: (cos ψ/2, 0, 0, sin ψ/2) by the half-angle
formulas (square roots only). -/
def levelQuat (h : R × R) : Quat :=
  let (c, s) := h
  let w := R.sqrt (max 0 ((1 + c) / 2))
  let z := R.sqrt (max 0 ((1 - c) / 2))
  ⟨w, 0, 0, if s < 0 then -z else z⟩

/-- Started on the ground, disarmed, in ArduCopter's boot mode STABILIZE, calibrating; home and
the estimator wait for the first fixes. `mission` is the initial stored mission. -/
def initGround (P : Params) (mission : Array MissionCmd) : State :=
  { P, boot := .calibrating #[], ctl := Controller.init P, navP := P.nav, pathStart := P.start,
    home := ⟨P.start.x, P.start.y, 0⟩, speed := P.nav.vMax, mission,
    cur := if mission.isEmpty then 0 else 1,
    missionState := if mission.isEmpty then .noMission else .notStarted }

/-- The batch start (today's behavior of the executable): in the air at the parameter file's start
point, armed, in AUTO, flying the file's mission (`P.nav`, items `mission` = the file's waypoints)
from item 1, estimator running (the caller applies the gyro calibration). Home is below the start
point at down 0. -/
def initAir (P : Params) (mission : Array MissionCmd) : State :=
  { P, boot := .running 0, ctl := Controller.init P, navP := P.nav, pathStart := P.start,
    pathWps := P.waypoints, armed := true, mode := Mode.auto,
    phase := .path (.run 1 mission.size), home := ⟨P.start.x, P.start.y, 0⟩, speed := P.nav.vMax,
    mission, cur := if mission.isEmpty then 0 else 1,
    missionState := if mission.isEmpty then .noMission else .active }

/-! ## Small updates -/

def ok (s : State) : State := { s with results := s.results.push .accepted }
def fail (s : State) (texts : Array (Severity × String) := #[]) : State :=
  { s with results := s.results.push .failed, texts := s.texts ++ texts }
def State.say (s : State) (sev : Severity) (t : String) : State := { s with texts := s.texts.push (sev, t) }

/-- The estimated position (p̂). -/
def State.position (s : State) : Vec3 := (Controller.estimate s.ctl).1

/-- The navigator's current target (where a new path starts). -/
def State.target (s : State) : Vec3 := s.ctl.nav.pos

/-- Waypoints with any point equal to the one before it removed (a leg of zero length). -/
def dropRepeats (start : Vec3) (wps : Array Waypoint) : Array Waypoint :=
  (wps.foldl (fun (acc : Array Waypoint × Vec3) w =>
    let d := w.pos - acc.2
    if Vec3.dot d d > 0 then (acc.1.push w, w.pos) else acc) (#[], start)).1

/-- Fly `wps` from the current target, for `goal`: the navigator restarts at rest on the new legs
(the heading setpoint kept). -/
def startPath (s : State) (wps : Array Waypoint) (goal : Goal) : State :=
  let start := s.target
  let navP := Navigator.withLegs s.P.nav s.speed s.P.dt start wps
  { s with navP, pathStart := start, pathWps := wps, phase := .path goal,
           ctl := { s.ctl with nav := Navigator.init start s.ctl.nav.heading } }

/-- Hold the current target (a path of no legs). -/
def hold (s : State) : State := startPath s #[] .hold

/-- Disarm: motors off, on the ground. -/
def disarm (s : State) : State :=
  ({ s with armed := false, phase := .ground, groundTicks := 0, landCount := 0 }).say 6 "Disarming motors"

end Copter
