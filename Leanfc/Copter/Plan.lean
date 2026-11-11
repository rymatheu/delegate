import Leanfc.Copter.State
import Leanfc.Mavlink.Mission

/-!
# Copter.Plan (AUTO missions and the paths of the modes)

How the vehicle layer turns mission items and mode goals into navigator paths, and what happens
when a path, a brake or a wait is done. ArduCopter's AUTO runs one command at a time
(`ModeAuto`, `AP_Mission`); leanfc does the same, except that consecutive NAV_WAYPOINT and
NAV_SPLINE_WAYPOINT items are flown as one path (a "run"), so that the navigator can pass a
waypoint at speed and shape a spline leg with the next point, as ArduCopter's waypoint navigation
does with its next destination. A run ends after an item with a hold time.

| item | started (`startItem`) | done |
|---|---|---|
| NAV_TAKEOFF | on the ground: spool-up, throttle ramp, climb (`Phase.spool`); in the air: climb to its altitude if below it | reached, next item |
| NAV_WAYPOINT, NAV_SPLINE_WAYPOINT | the run from this item: one leg per item (`Mission.toWaypoints`) from the current target | each item reached as its leg ends; after the run, the last item's hold time, then the next item |
| NAV_LAND | with a location: fly there at the current altitude, then descend; without: descend | at touchdown (reached, mission complete, disarm) |
| NAV_RETURN_TO_LAUNCH | RTL's path (climb to RTL_ALT_M if below it, return over home), RTL_LOIT_TIME, descend | at touchdown |
| past the last item | mission complete; the vehicle holds where it is (ArduCopter `exit_mission`: loiter) | |

RTL (`rtlWaypoints`): from the current target, straight up to RTL_ALT_M above home if lower, then
straight to the point above home at that altitude (ArduCopter: the higher of RTL_ALT_M and the
current altitude).
-/

namespace Copter

open Mavlink

/-- The hold time of a waypoint item (0 for other items). -/
def holdOf : Option MissionCmd → R
  | some (.waypoint _ h) => h
  | some (.spline _ h) => h
  | _ => 0

/-- One past the last item (1-based) of the run that starts at item `i`: the consecutive waypoint
and spline-waypoint items from `i`, up to and including the first one with a hold time. -/
def runEnd (m : Array MissionCmd) (i : Nat) : Nat := Id.run do
  let mut j := i
  let mut open_ := true
  for k in [i:m.size + 1] do
    if open_ then
      match m[k - 1]? with
      | some (.waypoint _ h) | some (.spline _ h) =>
        j := k + 1
        if h > 0 then open_ := false
      | _ => open_ := false
  return j

/-- RTL's path from the current target: up to RTL_ALT_M above home if lower, then over home. -/
def rtlWaypoints (s : State) : Array Waypoint :=
  let t := s.target
  let z := min t.z (s.home.z - s.P.copter.rtlAlt)
  dropRepeats t #[⟨{ t with z }, .line, true⟩, ⟨{ s.home with z }, .line, true⟩]

/-- Start the landing descent at the current target's north and east. -/
def descend (s : State) : State := { s with phase := .descend, landCount := 0 }

/-- Start mission item `i` (1-based) from the current target; past the last item the mission is
complete and the vehicle keeps holding (its navigator state untouched). -/
def startItem (s : State) (i : Nat) : State :=
  let s := { s with cur := min i s.mission.size }
  match s.mission[i - 1]? with
  | none => { s with missionState := .complete, phase := .path .hold }
  | some c =>
    let s := { s with missionState := .active }
    match c with
    | .takeoff d =>
      if s.landed == .onGround then { s with phase := .spool 0 d }
      else if d < s.target.z then startPath s #[⟨{ s.target with z := d }, .line, true⟩] (.takeoff (some i))
      else startPath s #[] (.takeoff (some i))
    | .waypoint _ _ | .spline _ _ =>
      let j := runEnd s.mission i
      startPath s (Mission.toWaypoints s.target s.home (s.mission.extract (i - 1) (j - 1))) (.run i (j - 1))
    | .land (some p) => startPath s (dropRepeats s.target #[⟨{ p with z := s.target.z }, .line, true⟩]) .landAt
    | .land none => descend s
    | .rtl => startPath s (rtlWaypoints s) (.home (some i))

/-- What follows a brake or a wait. -/
def after (s : State) : After → State
  | .hold => hold s
  | .fly wps goal => startPath s (dropRepeats s.target wps) goal
  | .item i => startItem s i
  | .descend | .rtlDescend => descend s
  | .pause t => { s with phase := .wait t .descend }
  | .home item => startPath s (rtlWaypoints s) (.home item)

/-- The navigator has finished the path flown for `goal` (the vehicle is at its end). -/
def pathDone (s : State) : Goal → State
  | .hold => s
  | .run _ last =>
    let t := CopterParams.ticksOf (holdOf s.mission[last - 1]?) s.P.dt
    if t > 0 then { s with phase := .wait t (.item (last + 1)) } else startItem s (last + 1)
  | .takeoff (some i) => startItem { s with reached := some i } (i + 1)
  | .takeoff none => { s with phase := .path .hold }
  | .landAt => descend s
  | .home _ => { s with phase := .wait s.P.copter.rtlLoitTicks .rtlDescend }

end Copter
