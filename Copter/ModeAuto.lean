import Copter.AutoYaw

/-!
# `Copter.ModeAuto`: Auto mode on a waypoint mission

Mirrors, at ArduPilot 802db19de1, `ArduCopter/mode_auto.cpp`: `init` (`:22-74`), `run`
(`:89-185`, the `STARTING`, `WP` and `LOITER` cases), `set_submode` (`:194-...`), `loiter_start`
(`:374-395`), `wp_start` (`:465-501`), `start_command`/`verify_command` for
`MAV_CMD_NAV_WAYPOINT` (`:765-780`, `:989-...`), `exit_mission` (`:904-917`), `wp_run`
(`:1134-1154`), `loiter_run` (`:1194-1198`), `do_nav_wp` (`:1578-1615`), `set_next_wp`
(`:1623-1690`, the waypoint case), `verify_nav_wp` (`:2297-2322`); and the `AP_Mission` calls they
make, `libraries/AP_Mission/AP_Mission.cpp`: `start` (`:109-120`), `update` (`:310-360`, nav
commands), `advance_current_nav_cmd` (`:2157-...`), `get_next_nav_cmd`, `complete`.

`wp_run` is in the order of `mode_auto.cpp:1134-1154`:
1. `wp_nav->update_wpnav()` (which ends with `pos_control->NE_update_controller()`);
2. `pos_control->D_update_controller()`, whose `set_throttle_out` call is applied to the attitude
   controller and the motors object right there (it only stores `_throttle_in` etc. for the next
   `motors_output`);
3. `attitude_control->input_thrust_vector_heading(pos_control->get_thrust_vector(),
   auto_yaw.get_heading())`, which stores `_ang_vel_body_rads` for the next
   `rate_controller_run`.

Environment assumptions: armed, not landed (`is_disarmed_or_landed()` false, so
`make_safe_ground_handling` is never called; it is not ported), motor interlock on and the desired
spool state `THROTTLE_UNLIMITED` (the `AP_Motors` port's assumption), an EKF origin exists
(`ahrs.get_origin` succeeds on the first `run`), `position_ok()`, no mission changes from a GCS
(`mis_change_detector` reports none), no DO commands, `MIS_RESTART = 0` with a never-run mission
(so `start_or_resume` starts it).

Not one to one:
- Waypoints are NED vectors from the EKF origin with their altitude above the origin, not
  `Location`s; `get_loc_from_cmd`'s zero-coordinate defaults (`default_loc`) are not ported, so
  `do_nav_wp`'s computation of `default_loc` is left out.
- The mission holds `MAV_CMD_NAV_WAYPOINT` items only, each with `p1 = 0` (no loiter time).
- `ModeAuto::init` is called by the harness (`Copter.Loop`), as `Copter::set_mode(AUTO)` would
  call it; it fails, as in the C++, if the mission is empty (`mission.present()` false).
- `desired_speed_override_ms` is zero (no `DO_CHANGE_SPEED`), so `wp_start` passes speed 0.
-/

namespace Copter

open AP_Math

namespace ModeAuto

/-- `mission.present()`: at least one command besides home. -/
def mission_present (p : Parameters) : Bool := !p.mission.isEmpty

/-- The mission command stored at `index` (1-based: index 0 is home). -/
def mission_cmd (p : Parameters) (index : Nat) : Option MissionCommand :=
  match index with
  | 0 => none
  | i + 1 => p.mission[i]?.map fun loc => { index := i + 1, location := loc }

/-- `get_next_nav_cmd(start_index, cmd)`: every stored command is a nav command. -/
def get_next_nav_cmd (p : Parameters) (start_index : Nat) : Option MissionCommand :=
  mission_cmd p start_index

/-- `set_submode(new_submode)` (`mode_auto.cpp:194-...`); the `NAV_ATTITUDE_TIME` recheck does not
apply. -/
def set_submode (s : State) (new_submode : SubMode) : State :=
  { s with mode_auto := { s.mode_auto with _mode := new_submode } }

/-- `ModeAuto::init(ignore_checks)` (`mode_auto.cpp:22-74`); `none` if the mission is empty
(the C++ returns false and the mode change fails). -/
def init (p : Parameters) (s : State) : Option State :=
  if !mission_present p then none
  else
    -- (landed-with-motors-armed check: not landed, header)
    let s := { s with mode_auto := { s.mode_auto with _mode := .STARTING } }
    -- (ROI carry-over: auto_yaw is never ROI here)
    -- initialise waypoint and spline controller
    let (wp, psc) := AC_WPNav.wp_and_spline_init_m p.wpnav p.psc s.wp_nav s.pos_control (s.wpEnv p)
    let s := { s with wp_nav := wp, pos_control := psc }
    -- initialise desired speed overrides (zero), LOITER_TURNS state (none)
    -- set flag to start mission
    some { s with mode_auto := { s.mode_auto with waiting_to_start := true } }

/-- `set_next_wp(current_cmd, default_loc)` (`mode_auto.cpp:1623-1690`), waypoint case. -/
def set_next_wp (p : Parameters) (s : State) (current_cmd : MissionCommand) : State :=
  -- Do not add the next WP if the current command includes a delay (p1 > 0).
  if current_cmd.p1 > 0 then s
  else
    -- do not add next wp if there are no more navigation commands
    match get_next_nav_cmd p (current_cmd.index + 1) with
    | none => s
    | some next_cmd =>
      -- MAV_CMD_NAV_WAYPOINT: whether vehicle should stop at the target position depends upon the next command
      { s with wp_nav := AC_WPNav.set_wp_destination_next_NED_m p.wpnav s.wp_nav s.pos_control next_cmd.location }

/-- `wp_start(dest_loc)` (`mode_auto.cpp:465-501`). -/
def wp_start (p : Parameters) (s : State) (dest : Vector3p) : State := Id.run do
  let mut s := s
  -- init wpnav and set origin if transitioning from takeoff (not from takeoff here)
  if !AC_WPNav.is_active s.wp_nav s.clock then
    let des_speed_xy_ms : ftype := 0
    let (wp, psc) := AC_WPNav.wp_and_spline_init_m p.wpnav p.psc s.wp_nav s.pos_control (s.wpEnv p)
      des_speed_xy_ms {}
    s := { s with wp_nav := wp, pos_control := psc }
    -- (no speed overrides)
  let (wp, psc) := AC_WPNav.set_wp_destination_NED_m p.wpnav p.psc s.wp_nav s.pos_control (s.wpEnv p) dest
  s := { s with wp_nav := wp, pos_control := psc }
  -- initialise yaw (auto_yaw is neither ROI nor FIXED here)
  s := AutoYaw.set_mode_to_default p s false
  -- set submode
  return set_submode s .WP

/-- `do_nav_wp(cmd)` (`mode_auto.cpp:1578-1615`). -/
def do_nav_wp (p : Parameters) (s : State) (cmd : MissionCommand) : State :=
  -- get waypoint's location from command and send to wp_nav
  let s := wp_start p s cmd.location
  -- this will be used to remember the time in millis after we reach or pass the WP.
  let s := { s with mode_auto := { s.mode_auto with loiter_time := 0, loiter_time_max := cmd.p1 } }
  -- set next destination if necessary
  set_next_wp p s cmd

/-- `start_command(cmd)` for `MAV_CMD_NAV_WAYPOINT` (`mode_auto.cpp:777-780`). -/
def start_command (p : Parameters) (s : State) (cmd : MissionCommand) : State := do_nav_wp p s cmd

/-- `verify_nav_wp(cmd)` (`mode_auto.cpp:2297-2322`). -/
def verify_nav_wp (s : State) : State × Bool :=
  -- check if we have reached the waypoint
  if !AC_WPNav.reached_wp_destination s.wp_nav then (s, false)
  else
    -- start timer if necessary
    let s := if s.mode_auto.loiter_time == 0 then
        { s with mode_auto := { s.mode_auto with loiter_time := s.millis } }
      else s
    -- check if timer has run out
    if ((s.millis - s.mode_auto.loiter_time) / 1000) ≥ s.mode_auto.loiter_time_max.toUInt32 then
      (s, true)
    else (s, false)

/-- `loiter_start()` (`mode_auto.cpp:374-395`). -/
def loiter_start (p : Parameters) (s : State) : State :=
  -- calculate stopping point
  let stopping_point_ned_m := AC_WPNav.get_wp_stopping_point_NED_m p.psc s.pos_control
  -- initialise waypoint controller target to stopping point
  let (wp, psc) := AC_WPNav.set_wp_destination_NED_m p.wpnav p.psc s.wp_nav s.pos_control (s.wpEnv p)
    stopping_point_ned_m
  let s := { s with wp_nav := wp, pos_control := psc }
  -- hold yaw at current heading
  let s := AutoYaw.set_mode s .HOLD
  -- set submode
  set_submode s .LOITER

/-- `exit_mission()` (`mode_auto.cpp:904-917`): not landed, so loiter (which succeeds,
`position_ok()`). -/
def exit_mission (p : Parameters) (s : State) : State := loiter_start p s

/-- `AP_Mission::complete()`: mark the mission complete and call `exit_mission`. -/
def mission_complete (p : Parameters) (s : State) : State :=
  let s := { s with mode_auto := { s.mode_auto with
    mission := { s.mode_auto.mission with state := .MISSION_COMPLETE } } }
  exit_mission p s

/-- `AP_Mission::advance_current_nav_cmd()` (`AP_Mission.cpp:2157-...`): load and start the next
nav command; `none` if there is none (the C++ returns false). -/
def advance_current_nav_cmd (p : Parameters) (s : State) : Option State :=
  let m := s.mode_auto.mission
  if m.state != .MISSION_RUNNING then none
  else if m.nav_cmd_loaded then none
  else
    -- start from one position past the current nav command, or from the first real command
    let cmd_index := match m.nav_cmd with
      | none => 1
      | some c => c.index + 1
    match get_next_nav_cmd p cmd_index with
    | none => none
    | some cmd =>
      let s := { s with mode_auto := { s.mode_auto with
        mission := { m with nav_cmd := some cmd, nav_cmd_loaded := true } } }
      some (start_command p s cmd)

/-- `AP_Mission::start()` (`AP_Mission.cpp:109-120`). -/
def mission_start (p : Parameters) (s : State) : State :=
  let s := { s with mode_auto := { s.mode_auto with
    mission := { state := .MISSION_RUNNING, nav_cmd := none, nav_cmd_loaded := false } } }
  match advance_current_nav_cmd p s with
  | some s => s
  | none => mission_complete p s

/-- `AP_Mission::update()` (`AP_Mission.cpp:310-360`), nav commands only. -/
def mission_update (p : Parameters) (s : State) : State :=
  let m := s.mode_auto.mission
  -- exit immediately if not running or no mission commands
  if m.state != .MISSION_RUNNING || p.mission.isEmpty then s
  else if !m.nav_cmd_loaded || m.nav_cmd.isNone then
    -- advance in mission if no active nav command
    match advance_current_nav_cmd p s with
    | some s => s
    | none => mission_complete p s
  else
    -- run the active nav command (verify_command → verify_nav_wp)
    let (s, done) := verify_nav_wp s
    if done then
      -- mark _nav_cmd as complete
      let s := { s with mode_auto := { s.mode_auto with
        mission := { s.mode_auto.mission with nav_cmd_loaded := false } } }
      match advance_current_nav_cmd p s with
      | some s => s
      | none => mission_complete p s
    else s

/-- `wp_run()` (`mode_auto.cpp:1134-1154`). -/
def wp_run (p : Parameters) (s : State) : State := Id.run do
  let mut s := s
  -- if not armed set throttle to zero and exit immediately (armed and flying, header)
  -- set motors to full range (THROTTLE_UNLIMITED, header)
  -- run waypoint controller
  let (wp, psc, _ret) := AC_WPNav.update_wpnav p.wpnav p.psc s.wp_nav s.pos_control (s.wpEnv p)
  s := { s with wp_nav := wp, pos_control := psc }
  -- WP_Nav has set the vertical position control targets
  -- run the vertical position controller and set output throttle
  let (psc, thr) := AC_PosControl.D_update_controller p.psc s.pos_control s.ahrs.posInputs
    s.motors.toInputs (attInputs p s.attitude_control) s.clock
  s := { s with pos_control := psc }
  -- (inside D_update_controller, AC_PosControl.cpp:1145) _attitude_control.set_throttle_out(...)
  let (att, m) := AC_AttitudeControl_Multi.set_throttle_out p.att s.attitude_control s.motors.toInputs
    s.ahrs.cos_pitch s.ahrs.cos_roll thr.throttle_in thr.apply_angle_boost thr.filt_cutoff
  s := { s with attitude_control := att, motors := { s.motors with toInputs := m } }
  -- call attitude controller with auto yaw
  let (s', heading) := AutoYaw.get_heading s
  s := s'
  let att := AC_AttitudeControl_Multi.input_thrust_vector_heading p.att s.attitude_control
    s.ahrs.quat_body_to_ned (AC_PosControl.get_thrust_vector s.pos_control) heading
  return { s with attitude_control := att }

/-- `loiter_run()` (`mode_auto.cpp:1194-1198`): the waypoint controller. -/
def loiter_run (p : Parameters) (s : State) : State := wp_run p s

/-- `ModeAuto::run()` (`mode_auto.cpp:89-185`). -/
def run (p : Parameters) (s : State) : State := Id.run do
  let mut s := s
  -- start or update mission
  if s.mode_auto.waiting_to_start then
    -- don't start the mission until we have an origin (we have one, header)
    -- start/resume the mission (based on MIS_RESTART parameter)
    s := mission_start p s
    s := { s with mode_auto := { s.mode_auto with waiting_to_start := false } }
  else
    -- check for mission changes (none, header)
    s := mission_update p s
  -- call the correct auto controller
  match s.mode_auto._mode with
  -- hold position until the mission dispatches the first navigation submode
  | .STARTING => return loiter_run p s
  | .WP => return wp_run p s
  | .LOITER => return loiter_run p s

end ModeAuto

end Copter
