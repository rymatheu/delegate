import Leanfc.Controller

/-!
# Vehicle (the contract between the MAVLink services and a vehicle)

Plain data in both directions. Each 400 Hz tick the vehicle hands `Gcs.step` its `Telemetry`;
`Gcs.step` returns the `Command`s the ground station asked for, which the vehicle applies, in
order, before its next tick, and it reports one `CommandResult` per command, in the same order,
in the next tick's `Telemetry.results`. The services only translate: whether an arm, a mode change
or a takeoff is allowed is the vehicle's decision; the services turn the result into the
COMMAND_ACK (or MISSION_ACK) and pass on the vehicle's status texts.

Positions are NED meters from the origin (`Origin`, the EKF origin of ArduPilot), velocities NED
m/s, the attitude a unit quaternion body FRD → NED (as `Quat`), rates body rad/s. Mode numbers are
ArduCopter's (`ArduCopter/mode.h`, `Mode::Number`), listed in `Mode`.

`Leanfc/Copter/*` implements it with the real controller (`Copter.apply` in `Modes.lean` for the commands,
`Copter.telemetry` in `Fly.lean` for the telemetry); README.md, "Vehicle layer" and "MAVLink interface", lists
what each field is fed from.
-/

namespace Mavlink

/-! ArduCopter's flight-mode numbers (`custom_mode` of HEARTBEAT, param2 of DO_SET_MODE). -/
namespace Mode
def stabilize : Nat := 0
def altHold : Nat := 2
def auto : Nat := 3
def guided : Nat := 4
def loiter : Nat := 5
def rtl : Nat := 6
def land : Nat := 9
def posHold : Nat := 16
def brake : Nat := 17

/-- ArduCopter's mode names (QGroundControl shows its own names for the same numbers). -/
def name : Nat → String
  | 0 => "Stabilize" | 1 => "Acro" | 2 => "AltHold" | 3 => "Auto" | 4 => "Guided"
  | 5 => "Loiter" | 6 => "RTL" | 7 => "Circle" | 9 => "Land" | 11 => "Drift" | 13 => "Sport"
  | 14 => "Flip" | 15 => "AutoTune" | 16 => "PosHold" | 17 => "Brake" | 18 => "Throw"
  | 19 => "Avoid_ADSB" | 20 => "Guided_NoGPS" | 21 => "Smart_RTL" | 22 => "FlowHold"
  | 23 => "Follow" | 24 => "ZigZag" | 25 => "SystemID" | 26 => "Heli_Autorotate"
  | 27 => "Auto RTL" | 28 => "Turtle"
  | n => s!"Mode({n})"

/-- Modes whose horizontal position controller runs (HEARTBEAT's GUIDED_ENABLED flag when armed). -/
def usesPosition (m : Nat) : Bool := [3, 4, 5, 6, 7, 9, 16, 17, 21, 27].contains m
end Mode

/-- EXTENDED_SYS_STATE `landed_state` (MAV_LANDED_STATE). -/
inductive Landed where
  | onGround
  | inAir
  | takeoff
  | landing
  deriving Repr, BEq, Inhabited

/-- MISSION_CURRENT `mission_state` (MISSION_STATE). -/
inductive MissionState where
  | noMission
  | notStarted
  | active
  | paused
  | complete
  deriving Repr, BEq, Inhabited

/-- The geodetic origin of the NED frame (WGS84 degrees · 1e7, altitude above mean sea level in mm)
and the cosine of its latitude, which the vehicle supplies (the services never compute a cosine;
it scales east offsets: Δlon·1e-7 deg ↔ east m). -/
structure Origin where
  latE7 : Int
  lonE7 : Int
  altMm : Int
  cosLat : R
  deriving Repr, Inhabited

/-- A stored mission item the vehicle flies, in the local frame: the commands of the waypoint
mission type the services accept. `alt` and the down coordinates are already converted (down from
the origin, from altitude relative to home). -/
inductive MissionCmd where
  /-- NAV_TAKEOFF: climb to `down` (NED down from the origin) above the current position -/
  | takeoff (down : R)
  /-- NAV_WAYPOINT: fly straight to `p`, wait `hold` s -/
  | waypoint (p : Vec3) (hold : R)
  /-- NAV_SPLINE_WAYPOINT: fly a spline leg to `p`, wait `hold` s -/
  | spline (p : Vec3) (hold : R)
  /-- NAV_LAND at `p` (north, east; down ignored), or where the vehicle is (latitude and
  longitude 0, as in ArduPilot) -/
  | land (p : Option Vec3)
  /-- NAV_RETURN_TO_LAUNCH -/
  | rtl
  deriving Repr, Inhabited

/-- What the ground station asks for. -/
inductive Command where
  /-- MAV_CMD_COMPONENT_ARM_DISARM param1 = 1; `force` for param2 = 2989 or 21196 -/
  | arm (force : Bool)
  /-- param1 = 0; `force` for param2 = 21196 -/
  | disarm (force : Bool)
  /-- MAV_CMD_DO_SET_MODE (custom mode) or SET_MODE: switch to ArduCopter mode `mode` -/
  | setMode (mode : Nat)
  /-- MAV_CMD_NAV_TAKEOFF: climb to `alt` m above home (ArduCopter: armed, landed, a mode with
  user takeoff such as GUIDED) -/
  | takeoff (alt : R)
  /-- MAV_CMD_MISSION_START: switch to AUTO and run the mission from its current item -/
  | missionStart
  /-- MAV_CMD_DO_SET_MISSION_CURRENT or MISSION_SET_CURRENT: make item `seq` (1-based; 0 is home)
  current -/
  | setCurrent (seq : Nat)
  /-- MAV_CMD_NAV_LAND: switch to LAND -/
  | land
  /-- MAV_CMD_NAV_RETURN_TO_LAUNCH: switch to RTL -/
  | returnToLaunch
  /-- MAV_CMD_DO_SET_HOME: home at `p` (NED from the origin), or at the current position -/
  | setHome (p : Option Vec3)
  /-- Fly to `p` (NED from the origin) in GUIDED: DO_REPOSITION, a MISSION_ITEM with current = 2
  (go to) or 3 (change altitude), or SET_POSITION_TARGET_LOCAL_NED (position only). With
  `changeMode` the vehicle switches to GUIDED first (DO_REPOSITION's CHANGE_MODE flag). -/
  | goTo (p : Vec3) (changeMode : Bool)
  /-- MAV_CMD_DO_CHANGE_SPEED: horizontal speed `speed` m/s for the rest of the flight -/
  | changeSpeed (speed : R)
  /-- A new mission was uploaded (items 1..n; item 0 is home and not included). -/
  | setMission (items : Array MissionCmd)
  /-- A parameter was set: the new configuration, built by `ParamFile.build` exactly as from a
  parameter file. -/
  | setParams (P : Params)
  deriving Inhabited

/-- The vehicle's verdict on one command (MAV_RESULT for COMMAND_ACK). -/
inductive CommandResult where
  | accepted
  | denied
  | failed
  deriving Repr, BEq, Inhabited

/-- MAV_SEVERITY: 0 emergency .. 7 debug. QGroundControl pops up 0..3 as critical. -/
abbrev Severity := Nat

/-- What the vehicle reports each tick. -/
structure Telemetry where
  /-- ticks since boot; the services' clock (`GcsConfig.tickUs` µs per tick) -/
  tick : Nat
  armed : Bool
  /-- ArduCopter mode number -/
  mode : Nat
  landed : Landed
  /-- estimated position, NED m from the origin -/
  position : Vec3
  /-- estimated velocity, NED m/s -/
  velocity : Vec3
  /-- estimated attitude, body FRD → NED -/
  attitude : Quat
  /-- estimated body rates, rad/s -/
  rates : Vec3
  origin : Origin
  /-- home, NED m from the origin (mission item 0; RTL returns here) -/
  home : Vec3
  /-- current mission item (MAVLink seq: 1..n, 0 when none) and the mission's state -/
  missionSeq : Nat
  missionState : MissionState
  /-- the mission item completed this tick, if any (MISSION_ITEM_REACHED) -/
  reached : Option Nat
  /-- navigation target position, NED m (NAV_CONTROLLER_OUTPUT: distance, bearing, alt error) -/
  target : Vec3
  /-- heading setpoint (cos ψ, sin ψ) (NAV_CONTROLLER_OUTPUT nav_bearing) -/
  targetHeading : R × R
  /-- collective thrust as a fraction of the maximum, 0..1 (VFR_HUD throttle) -/
  throttle : R
  /-- SYS_STATUS sensor bits (MAV_SYS_STATUS_SENSOR) currently healthy; PREARM_CHECK set when the
  vehicle would arm -/
  health : UInt32
  /-- a failsafe is active (HEARTBEAT system_status CRITICAL) -/
  failsafe : Bool
  /-- one result per command received after the previous tick, in order -/
  results : Array CommandResult
  /-- status texts to send (severity, text of at most 50 bytes), e.g. "Arm: Auto mode not armable" -/
  texts : Array (Severity × String)
  deriving Inhabited

end Mavlink
