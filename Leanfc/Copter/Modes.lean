import Leanfc.Copter.Plan
import Leanfc.Copter.Health

/-!
# Copter.Modes (flight modes and the ground station's commands)

The `Command`s of the MAVLink contract (`Mavlink.Vehicle`) applied to the vehicle state, each
answered with one `CommandResult`, by ArduCopter's rules (`mode.cpp` `set_mode`, `mode.h`,
`AP_Arming_Copter.cpp`, `takeoff.cpp`, `mode_auto.cpp`, `mode_guided.cpp`, `mode_rtl.cpp`,
`mode_land.cpp`, `GCS_MAVLink_Copter.cpp`).

| mode (number) | arming | entered in the air | entered armed on the ground | takeoff command |
|---|---|---|---|---|
| STABILIZE (0), the boot mode | allowed | refused ("no pilot input": leanfc has no RC) | stays on the ground | refused |
| AUTO (3) | refused ("Arm: Auto mode not armable") | brake, then the current item | starts item 1, which must be a takeoff ("Auto: Missing Takeoff Cmd") | refused |
| GUIDED (4) | allowed | brake, then hold; go-to and change of altitude fly a path | stays on the ground | climbs to the altitude |
| LOITER (5) | allowed | brake, then hold | stays on the ground | climbs to the altitude |
| RTL (6) | refused | brake, climb to RTL_ALT_M, return, wait, land, disarm | disarms (after the spool-down) | refused |
| LAND (9) | refused | brake, descend, disarm | disarms (after the spool-down) | refused |
| BRAKE (17), QGroundControl's pause | refused | brake, then hold | stays on the ground | refused |

Every other mode number is refused with ArduPilot's "No such mode N" (a mode not built into the
firmware). The same mode again is accepted and changes nothing (ArduCopter). Disarmed, every
supported mode can be selected; armed, the modes that need a position (all but STABILIZE and LAND)
are refused while the estimator is unhealthy ("requires position"). Leaving AUTO during a mission
pauses it (MISSION_CURRENT state PAUSED); AUTO resumes at the current item from where the vehicle
is.

Arming: allowed modes only, then the pre-arm checks (`Copter.Health`; skipped with force, as
ArduPilot's force-arm skips its checks). Arming sets home to the current position unless
DO_SET_HOME locked it. Disarming in the air needs force (refused without a text otherwise, as in
ArduCopter's `AP_Arming_Copter::disarm`).
-/

namespace Copter

open Mavlink

def supported (m : Nat) : Bool := [0, 3, 4, 5, 6, 9, 17].contains m
def allowsArming (m : Nat) : Bool := [0, 4, 5].contains m
def hasUserTakeoff (m : Nat) : Bool := [4, 5].contains m
def requiresPosition (m : Nat) : Bool := [3, 4, 5, 6, 17].contains m

/-- Armed and off the ground (spool-up and the throttle ramp count as on the ground). -/
def State.flying (s : State) : Bool := s.armed && s.landed != .onGround

/-- Enter mode `m`; the status texts of a refusal otherwise. -/
def enterMode (h : Health) (s : State) (m : Nat) : Except (Array (Severity × String)) State :=
  let refuse (why : String) := Except.error #[((4 : Nat), s!"Mode change to {Mode.name m} failed: {why}")]
  if m == s.mode then .ok s
  else if !supported m then .error #[(4, s!"No such mode {m}")]
  else if s.armed && requiresPosition m && !h.positionOk then refuse "requires position"
  else
    let s := if s.mode == Mode.auto && s.missionState == .active then { s with missionState := .paused } else s
    let s := { s with mode := m }
    -- a takeoff not yet lifted off is abandoned by any mode change
    let s := match s.phase with | .spool _ _ | .ramp _ _ => { s with phase := .ground } | _ => s
    if m == Mode.stabilize then
      if s.flying then refuse "no pilot input" else .ok s
    else if m == Mode.auto then
      if !s.armed then .ok s
      else if s.mission.isEmpty then refuse "initialisation failed"
      else if s.landed == .onGround then
        match (s.mission[0]? : Option MissionCmd) with
        | some (.takeoff _) => .ok (startItem s 1)
        | _ => .error #[(2, "Auto: Missing Takeoff Cmd"), (4, "Mode change to Auto failed: initialisation failed")]
      else
        let i := if s.cur == 0 || s.cur > s.mission.size then 1 else s.cur
        .ok { s with missionState := .active, phase := .brake (.item i) }
    else if m == Mode.rtl then
      if s.flying then .ok { s with phase := .brake (.home none) }
      else if s.armed then .ok { s with phase := .touchdown 0 } else .ok s
    else if m == Mode.land then
      if s.flying then .ok { s with phase := .brake .descend }
      else if s.armed then .ok { s with phase := .touchdown 0 } else .ok s
    else -- GUIDED, LOITER, BRAKE
      if s.flying then .ok { s with phase := .brake .hold } else .ok s

def setMode (h : Health) (s : State) (m : Nat) : State :=
  match enterMode h s m with
  | .ok s' => ok s'
  | .error texts => fail s texts

/-- LAND with ArduCopter's 4 s pause before the descent (failsafes, `set_mode_land_with_pause`). -/
def landWithPause (s : State) : State :=
  { s with mode := Mode.land, phase := .brake (.pause s.P.copter.landPauseTicks),
           missionState := if s.mode == Mode.auto && s.missionState == .active then .paused else s.missionState }

/-- The speed limit for new legs, and the legs being flown rebuilt at it (same geometry, so the
navigator's leg, τ and speed stay valid). Capped at the position loop's `vMaxXY`. -/
def setSpeed (s : State) (v : R) : State :=
  let speed := min v s.P.position.vMaxXY
  let s := { s with speed }
  match s.phase with
  | .path _ => { s with navP := Navigator.withLegs s.P.nav speed s.P.dt s.pathStart s.pathWps }
  | _ => s

/-- Arm (the checks passed). -/
def armNow (s : State) : State :=
  let p := s.position
  ({ s with armed := true, phase := .ground, groundTicks := 0,
            home := if s.homeLocked then s.home else p }).say 6 "Arming motors"

/-- Apply one command; one result is pushed. -/
def apply (h : Health) (s : State) : Command → State
  | .arm force =>
    if s.armed then ok s
    else if !allowsArming s.mode then fail s #[(2, s!"Arm: {Mode.name s.mode} mode not armable")]
    else match (if force then none else prearm h s.fsGcs) with
      | some why => fail s #[(2, why)]
      | none => ok (armNow s)
  | .disarm force =>
    if !s.armed then ok s
    else if s.flying && !force then fail s   -- refused without a text, as ArduCopter
    else ok (disarm s)
  | .setMode m => setMode h s m
  | .takeoff alt =>
    let d := s.home.z - alt
    let onGround := match s.phase with | .ground => true | _ => false
    if s.armed && onGround && hasUserTakeoff s.mode && d < s.position.z then
      ok { s with phase := .spool 0 d }
    else fail s
  | .missionStart =>
    match enterMode h s Mode.auto with
    | .ok s' => ok s'
    | .error texts => fail s texts
  | .setCurrent i =>
    if i ≥ 1 && i ≤ s.mission.size then
      ok (if s.mode == Mode.auto && s.flying then { s with cur := i, phase := .brake (.item i) }
          else { s with cur := i })
    else fail s
  | .land => setMode h s Mode.land
  | .returnToLaunch => setMode h s Mode.rtl
  | .setHome p => ok { s with home := p.getD s.position, homeLocked := true }
  | .goTo p changeMode =>
    match (if changeMode then enterMode h s Mode.guided else .ok s) with
    | .ok s1 =>
      if s1.mode == Mode.guided && s1.flying then ok { s1 with phase := .brake (.fly #[⟨p, .line, true⟩] .hold) }
      else fail s
    | .error _ => fail s
  | .changeSpeed v => ok (setSpeed s v)
  | .setMission cmds =>
    let s := { s with mission := cmds, cur := if cmds.isEmpty then 0 else 1,
                      missionState := if cmds.isEmpty then .noMission else .notStarted }
    ok (if s.mode == Mode.auto && s.flying then
          { s with missionState := if cmds.isEmpty then .noMission else .active,
                   phase := .brake (if cmds.isEmpty then .hold else .item 1) }
        else s)
  | .setParams P => ok (setSpeed { s with P } P.nav.vMax)

end Copter
