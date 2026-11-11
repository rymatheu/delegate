import Leanfc.Mavlink.Format
import Leanfc.Mavlink.Messages

/-!
# Mission (stored mission items ↔ the vehicle's mission and the controller's waypoint list)

The services store a waypoint mission as the MISSION_ITEM_INT fields the ground station sent
(items 1..n; item 0 is home, which ArduPilot never overwrites from an upload and reports from the
vehicle's home). `toCmd` validates an uploaded item and converts it to the vehicle's local form
(`MissionCmd`), with the MAV_MISSION_RESULT of a rejection, following ArduPilot's
`AP_Mission::mavlink_int_to_mission_cmd` rules for the five commands kept:

- commands NAV_WAYPOINT (16), NAV_SPLINE_WAYPOINT (82), NAV_TAKEOFF (22), NAV_LAND (21),
  NAV_RETURN_TO_LAUNCH (20); others UNSUPPORTED;
- frames for the commands with a location: GLOBAL (0), GLOBAL_INT (5) and MISSION (2) absolute
  (altitude AMSL), GLOBAL_RELATIVE_ALT (3) and GLOBAL_RELATIVE_ALT_INT (6) relative to home; others
  (terrain) UNSUPPORTED_FRAME; RTL takes any frame;
- latitude within ±90°, longitude within ±180° (INVALID_PARAM5_X, INVALID_PARAM6_Y), a finite altitude
  (INVALID_PARAM7), a finite param1 (INVALID_PARAM1) and a hold time in [0, 65535] s for waypoints.

`downloadItem` gives what ArduPilot reports back: the stored item with its frame folded to the
non-INT frame (5 → 0, 6 → 3), and item 0 the home position with frame GLOBAL and its AMSL altitude.

`toWaypoints` turns the vehicle's mission into the navigator's waypoint list (`Waypoint`: NED point,
leg kind, stop), and `ofWaypoints` turns a waypoint list back into a mission (each point a
NAV_WAYPOINT or NAV_SPLINE_WAYPOINT; `storedOf` gives the MISSION_ITEM_INT form, relative
altitude). Latitude and longitude go through
`Format.toNE`/`toLatLon` (integer differences, then binary32 scaling with the origin's cosine).
-/

namespace Mavlink.Mission

open Format FloatLib.Floats

/-- MAV_MISSION_RESULT codes used here. -/
def accepted : UInt8 := 0
def unsupportedFrame : UInt8 := 2
def unsupported : UInt8 := 3
def invalidParam1 : UInt8 := 6
def invalidX : UInt8 := 10
def invalidY : UInt8 := 11
def invalidZ : UInt8 := 12

def cmdWaypoint : UInt16 := 16
def cmdRtl : UInt16 := 20
def cmdLand : UInt16 := 21
def cmdTakeoff : UInt16 := 22
def cmdSpline : UInt16 := 82

def isFinite (x : R) : Bool := (ExecFloat.Binary.toRat? x).isSome

/-- Down coordinate of a stored altitude in its frame (`none`: frame not accepted). -/
def downOf (o : Origin) (home : Vec3) (frame : UInt8) (z : R) : Option R :=
  if frame == 0 || frame == 5 || frame == 2 then some (downOfAmsl o z)
  else if frame == 3 || frame == 6 then some (home.z - z)
  else none

/-- The local form of a stored item, or the MAV_MISSION_RESULT rejecting it. -/
def toCmd (o : Origin) (home : Vec3) (it : MissionItemInt) : Except UInt8 MissionCmd :=
  let c := it.command
  if c == cmdRtl then .ok .rtl else
  if !(c == cmdWaypoint || c == cmdSpline || c == cmdTakeoff || c == cmdLand) then .error unsupported else
  if !isFinite it.param1 then .error invalidParam1 else
  if (c == cmdWaypoint || c == cmdSpline) && (it.param1 < 0 || it.param1 > 65535) then
    .error invalidParam1 else
  let lat := it.x.toInt
  let lon := it.y.toInt
  if lat < -900000000 || lat > 900000000 then .error invalidX else
  if lon < -1800000000 || lon > 1800000000 then .error invalidY else
  if !isFinite it.z then .error invalidZ else
  match downOf o home it.frame it.z with
  | none => .error unsupportedFrame
  | some d =>
    let (n, e) := toNE o lat lon
    let p : Vec3 := ⟨n, e, d⟩
    if c == cmdTakeoff then .ok (.takeoff d)
    else if c == cmdLand then .ok (.land (if lat == 0 && lon == 0 then none else some p))
    else if c == cmdSpline then .ok (.spline p it.param1)
    else .ok (.waypoint p it.param1)

/-- Item 0 as ArduPilot reports it: home, frame GLOBAL, altitude AMSL in m. -/
def homeItem (o : Origin) (home : Vec3) : MissionItemInt :=
  let (lat, lon) := toLatLon o home
  { seq := 0, frame := 0, command := cmdWaypoint, autocontinue := 1,
    x := Int32.ofInt lat, y := Int32.ofInt lon, z := ofRat ((amslMm o home.z : ℚ) / 1000) }

/-- A stored item as reported in a download: INT frames folded to the plain ones. -/
def downloadItem (it : MissionItemInt) (seq : Nat) : MissionItemInt :=
  let frame := if it.frame == 5 then 0 else if it.frame == 6 then 3 else it.frame
  { it with seq := seq.toUInt16, frame, current := 0, target_system := 0, target_component := 0,
            mission_type := 0 }

/-- The stored form of a local mission command (relative-altitude frame). -/
def storedOf (o : Origin) (home : Vec3) : MissionCmd → MissionItemInt
  | .rtl => { command := cmdRtl, frame := 2, autocontinue := 1 }
  | .takeoff d =>
    let (lat, lon) := toLatLon o home
    { command := cmdTakeoff, frame := 3, autocontinue := 1, x := Int32.ofInt lat, y := Int32.ofInt lon,
      z := home.z - d }
  | .land p =>
    let (lat, lon) := match p with | some p => toLatLon o p | none => (0, 0)
    { command := cmdLand, frame := 3, autocontinue := 1, x := Int32.ofInt lat, y := Int32.ofInt lon }
  | .waypoint p hold =>
    let (lat, lon) := toLatLon o p
    { command := cmdWaypoint, frame := 3, autocontinue := 1, param1 := hold,
      x := Int32.ofInt lat, y := Int32.ofInt lon, z := home.z - p.z }
  | .spline p hold =>
    let (lat, lon) := toLatLon o p
    { command := cmdSpline, frame := 3, autocontinue := 1, param1 := hold,
      x := Int32.ofInt lat, y := Int32.ofInt lon, z := home.z - p.z }

/-- The navigator's waypoint list of a mission flown from `start` (`Navigator.Waypoint`: the point,
the leg kind, and whether the target stops there): takeoff climbs vertically; waypoints and spline
waypoints are legs of their kind (`line`, `spline`), with a stop where the item has a hold time;
land descends to home's altitude (at its point, or where the previous leg ended); RTL flies back
over home at the current altitude, then down to home. This is the geometry the navigator flies; the
modes themselves (takeoff, land and RTL logic, touchdown) are the vehicle layer's, which flies a
mission one run of consecutive waypoint items at a time (`Copter.Mission`) through this function. -/
def toWaypoints (start home : Vec3) (cmds : Array MissionCmd) : Array Waypoint :=
  (cmds.foldl (fun (acc : Array Waypoint × Vec3) c =>
    let (legs, cur) := acc
    match c with
    | .takeoff d => let p := { cur with z := d }; (legs.push ⟨p, .line, true⟩, p)
    | .waypoint p hold => (legs.push ⟨p, .line, hold > 0⟩, p)
    | .spline p hold => (legs.push ⟨p, .spline, hold > 0⟩, p)
    | .land p =>
      let q : Vec3 := match p with | some p => ⟨p.x, p.y, home.z⟩ | none => { cur with z := home.z }
      ((match p with | some p => legs.push ⟨{ p with z := cur.z }, .line, true⟩ | none => legs).push
        ⟨q, .line, true⟩, q)
    | .rtl =>
      let over : Vec3 := { home with z := cur.z }
      ((legs.push ⟨over, .line, true⟩).push ⟨home, .line, true⟩, home)) (#[], start)).1

/-- A waypoint list as a mission (each point a NAV_WAYPOINT or NAV_SPLINE_WAYPOINT by its leg kind,
no hold; a `stop` mark has no MAVLink form and is dropped); with `toWaypoints` the round trip gives
the same points and kinds. -/
def ofWaypoints (wps : Array Waypoint) : Array MissionCmd :=
  wps.map fun w => match w.kind with
    | .line => .waypoint w.pos 0
    | .spline => .spline w.pos 0

end Mavlink.Mission
