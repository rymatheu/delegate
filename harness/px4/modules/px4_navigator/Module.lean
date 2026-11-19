import px4.modules.px4_navigator.Ports
import px4.modules.px4_cmd_window.Module

/-! # px4_navigator: PX4's navigator with its mission storage

PX4's `navigator` (src/modules/navigator: mission, loiter, RTL, takeoff, land, precision land,
geofence, mission feasibility, with the libraries its CMakeLists.txt links) and PX4's `dataman`
(src/modules/dataman, RAM backend), real and unmodified, PX4 v1.17.0, in one process: dataman is
started first (`dataman start -r`), then `navigator start`, as PX4's startup script does.

Both are task modules. Navigator's loop waits in `px4_poll` on vehicle_local_position (rate-limited
to 20 Hz by orb_set_interval), vehicle_status and mission, with a 1 s timeout
(navigator_main.cpp:165-195); dataman's task waits in `px4_poll` on dataman_request. Navigator
reads its mission, geofence and safe points from dataman through DatamanClient (synchronous calls
that publish a request and poll for the answer, and asynchronous ones that check for it at the next
pass): in the harness both tasks are threads run one at a time by the shim, and a synchronous call
completes within the step (navigator blocks, dataman answers, navigator resumes).

What a step runs: dataman's answer to an injected request, then as many navigator passes as its
poll allows (one at most per 50 ms of local position, one per vehicle_status or mission message).

The mission comes in as MAVLink's mission manager stores it (mavlink_mission.cpp): one DM_WRITE per
item on dataman_request (item 6 or 7, DM_KEY_WAYPOINTS_OFFBOARD_0/1, one `mission_item_s` of 56
bytes as `parse_mavlink_mission_item` makes it), the mission state (item 8, `mission_s`), then the
`mission` topic with the same content (`update_active_mission`, :155-188). The mission topic's
mission_dataman_id is the dataman item (6 or 7), not 0 or 1 as Mission.msg's comment says:
MissionBase::isMissionValid compares it with DM_KEY_WAYPOINTS_OFFBOARD_0/1 (mission_base.cpp:963).

Contract, from the code:
* `triplet_stamped`: position_setpoint_triplet carries the clock of the pass that published it.
* `setpoint_types`: every setpoint type is one of PositionSetpoint.msg's (0-5).
* `current_located`: a valid current setpoint other than idle has a finite position.
* `no_px4_error`. -/

namespace Px4.Modules.Px4Navigator

open Harness Harness.Contract.Lang

private def sp (s : String) : String := s!"position_setpoint_triplet_{s}"

def guarantee : List Clause := [
  ⟨"triplet_stamped", ¬. "position_setpoint_triplet_updated" ∨.
      "position_setpoint_triplet_timestamp" =. "t_us"⟩,
  ⟨"setpoint_types", Expr.var (sp "previous_type") ≤. 5 ∧. Expr.var (sp "current_type") ≤. 5 ∧.
      Expr.var (sp "next_type") ≤. 5⟩,
  ⟨"current_located", ¬. Expr.var (sp "current_valid") ∨. Expr.var (sp "current_type") =. 5 ∨.
      (finite (.var (sp "current_lat")) ∧. finite (.var (sp "current_lon")))⟩,
  ⟨"no_px4_error", "px4_navigator_errors" =. 0⟩]

/-- The first statement. Campaigns refuted it twice:
* regime x500_clocked, seed 1, case 3 (of 10 x 400): the process died with SIGSEGV at step 1 after
  a `mission` message with mission_dataman_id = 35. PX4 defect: navigator does not check the
  dataman item it is told about. DatamanCache::update passes `g_per_item_size[item]` as the read
  length (DatamanClient.cpp:609-612) and DatamanClient::readAsync checks `length >
  g_per_item_size[item]` (:248), both indexing a 10-entry array (DM_KEY_NUM_KEYS) with item 35;
  the garbage length then drives `memcpy(_active_request.buffer, response.data, length)` in
  DatamanClient::update (:371), which reads past the stack (macOS crash report:
  _platform_memmove ← DatamanClient::update ← DatamanCache::update ← RTL::updateDatamanCache ←
  RTL::on_inactive ← Navigator::run). On the vehicle only MAVLink's mission manager and navigator
  publish `mission`, with 6 or 7; any other publisher is trusted the same way.
* regime flight, seeds 1 and 2 (10 x 400): `no_px4_error` with "Async request type 2 failed!
  status=3 item=6 index=1986007363" and "Caching: item 6, index ...": the generated mission
  messages had land and jump indices, and the generated storage writes mission items whose bytes
  name, far beyond the stored mission; navigator reports the failed reads at error level. -/
def contractAsFirstStated : Contract where
  assume := Ports.widths ++ Ports.paramRanges
  guarantee := guarantee

/-- What navigator has to be given, from the refutations above: a mission message as MAVLink's
mission manager makes it (mission storage 6 or 7, fence 3 or 4, safe points 0 or 1, at most
CONFIG_NUM_MISSION_ITMES_SUPPORTED = 10000 items, indices within the mission or -1), and no
storage requests from outside except MAVLink's own (`storage_from_mavlink_only`).
The storage requests arrive on the mirror port `dataman_request_mirror_*` (px4.txt `mirror 170`):
every request px4_mavlink's mission manager made in the step, whole, replayed into this process's
dataman one at a time. Standalone the clause is `mirror_count = 0`: generated words are not
MAVLink's requests (the first statement, `storage_reads_only`, was refuted with random writes,
above). What navigator needs of mirrored requests, that they are the complete, ordered requests
of MAVLink's mission manager, is a property of where the words come from, not a predicate on one
tick's fields; px4_mavlink's guarantee `mirror_complete` (nothing lost) is the part a clause can
state. In px4_sup this clause is an obligation px4_mavlink does not discharge (see the report).
`command_paced`: regime x500_clocked, seeds 1-3 (10 x 400), refuted `no_px4_error` with
"vehicle_command lost, generation 15 -> 18": vehicle_command has a queue of 8 and navigator drains
at most 8 per pass (navigator_main.cpp:245-256), but a pass only comes with its poll (local
position at most every 50 ms, vehicle_status, mission, or the 1 s timeout), and after a mode
command it stops reading commands until a newer vehicle_status (:269, :883). The per-step
condition used: at most one command, and only in a step that also brings a vehicle_status (which
wakes navigator in that step). That this suffices after a mode command needs the status
timestamps to increase; the regimes stamp them with the clock. -/
def missionWellFormedAsFirstStated : Clause :=
  ⟨"mission_well_formed", ¬. "mission_updated" ∨.
    ((("mission_mission_dataman_id" =. 6) ∨. ("mission_mission_dataman_id" =. 7)) ∧.
     (("mission_fence_dataman_id" =. 3) ∨. ("mission_fence_dataman_id" =. 4)) ∧.
     "mission_safepoint_dataman_id" ≤. 1 ∧. "mission_count" ≤. 10000 ∧.
     -1 ≤. "mission_current_seq" ∧. "mission_current_seq" <. "mission_count" + 1 ∧.
     -1 ≤. "mission_land_start_index" ∧. "mission_land_start_index" <. "mission_count" ∧.
     -1 ≤. "mission_land_index" ∧. "mission_land_index" <. "mission_count")⟩

/-- `mission_well_formed` restated: the fence storage may also be 0. The first statement
(`missionWellFormedAsFirstStated`, fence storage 3 or 4) failed in px4_full's mission flight
(2026-11-18, seed 1, step 2372, the first `mission` after the upload): mission_fence_dataman_id = 0,
with mission_dataman_id 6, safe points 0, 3 items, current_seq -1, land_start_index and land_index
2. That is what MAVLink's mission manager publishes before any fence was stored: it takes the fence
storage from the fence state it reads at start (`load_geofence_stats`, mavlink_mission.cpp:116-130)
and a fresh dataman's state is zeroed, so `dataman_id` 0 (DM_KEY_SAFE_POINTS_0, dataman.h:47), with
no fence points; navigator's geofence then loads no vertex (geofence.cpp:448-456 run over the
stored count). What navigator needs of the storage ids is an index within dataman's 10 keys (the
SIGSEGV of the first contract was id 35) and, for the fence, a fence storage whenever a fence is
stored; 0 is in range and comes only with no fence stored. -/
def missionWellFormed : Clause :=
  ⟨"mission_well_formed", ¬. "mission_updated" ∨.
    ((("mission_mission_dataman_id" =. 6) ∨. ("mission_mission_dataman_id" =. 7)) ∧.
     (("mission_fence_dataman_id" =. 0) ∨. ("mission_fence_dataman_id" =. 3) ∨.
      ("mission_fence_dataman_id" =. 4)) ∧.
     "mission_safepoint_dataman_id" ≤. 1 ∧. "mission_count" ≤. 10000 ∧.
     -1 ≤. "mission_current_seq" ∧. "mission_current_seq" <. "mission_count" + 1 ∧.
     -1 ≤. "mission_land_start_index" ∧. "mission_land_start_index" <. "mission_count" ∧.
     -1 ≤. "mission_land_index" ∧. "mission_land_index" <. "mission_count")⟩

/-- The input conditions as first stated (above). Two of them fail by construction in px4_full,
where PX4's MAVLink feeds navigator (served flights of 2026-11-18, `harness serve px4_full` through
px4/harnesses/px4_full/dev/fly_headless.sh, seed 1; the failing clauses printed by the serve log):
* `command_paced` at 8 of 17208 steps of the commanded flight (steps 2369, 2897, 3710, 4512, 5324,
  5326, 8402, 13217: the arm attempts, takeoff, reposition and land arrive in ticks without a
  vehicle_status) and at 6 steps of the mission flight, while navigator logged no error
  (`no_px4_error` held at every step): the clause is stronger than what navigator needs.
* `storage_from_mavlink_only` at the 3 steps of the mission flight that carry the mission
  manager's storage requests on the mirror port: the clause excludes exactly the words px4_full
  is built to deliver. -/
def assumeInputsAsFirstStated : List Clause := [
  missionWellFormedAsFirstStated,
  ⟨"storage_from_mavlink_only", "dataman_request_mirror_count" =. 0⟩,
  ⟨"command_paced", "vehicle_command_count" =. 0 ∨.
    ("vehicle_command_count" =. 1 ∧. "vehicle_status_updated")⟩]

/-- What navigator needs, restated from the code:
* `storage_from_mavlink`: no mirrored storage requests, or the mirror is px4_mavlink's
  (`dataman_request_mirror_by_px4_mavlink`, the mark px4_mavlink's generated glue sets on its
  mirror port, and px4_mavlink's guarantee `mirror_from_mission_manager`). A generated word is not
  a storage request of a mission manager; a campaign of this module alone never sets the mark (its
  regimes say so).
* `command_window`: at most 4 vehicle_command messages from outside in any 400 ticks (1 s), as the
  observer px4_cmd_window counts them (`vehicle_command_last_400_ticks`, this tick included). From
  the code: vehicle_command has a queue of 8 (ORB_QUEUE_LENGTH); navigator reads up to 8 of them
  at every pass and logs "vehicle_command lost" when the generation skipped
  (navigator_main.cpp:245-256); a pass comes with every vehicle_status, every mission and at most
  every 50 ms of local position, with a 1 s poll timeout (:166-185); after a reposition, takeoff
  or land command it reads no command until a newer vehicle_status (:269, :431, :507, :555, :883),
  which commander publishes at least every 500 ms (Commander.cpp:1932). So between two reads at
  most 1 s passes. Navigator also publishes vehicle_command itself (publish_vehicle_command,
  navigator_main.cpp:1402-1493), into the same queue; 4 of the 8 are left for those (the most
  found in one pass is 3, navigator_main.cpp:1237-1251; not proved). MAVLink does not enforce it:
  a ground station can put about 11 COMMAND_LONG frames into one tick's 512 bytes. In px4_full the
  clause is therefore an assumption on the ground station's traffic, an open obligation at the
  composite's boundary (the composite's inputs are one tick of bytes; the window is not one of
  them), checked at every tick of a served session.
* `window_holds_tick`: the window counts this tick's commands (true of the observer; stated so
  that a campaign of this module alone draws coherent values). A campaign of this module alone
  cannot make the window mean anything; its regimes keep the first statement's pacing. -/
def assumeInputs : List Clause := [
  missionWellFormed,
  ⟨"storage_from_mavlink", "dataman_request_mirror_count" =. 0 ∨.
    "dataman_request_mirror_by_px4_mavlink"⟩,
  ⟨"command_window", "vehicle_command_last_400_ticks" ≤. 4⟩,
  ⟨"window_holds_tick", "vehicle_command_count" ≤. "vehicle_command_last_400_ticks"⟩]

def contract : Contract where
  assume := Ports.widths ++ Ports.paramRanges ++ assumeInputs
  guarantee := guarantee

/-! ## Regimes -/

private def num (x : Float) : Expr := .lit x.toFloat32.toBits

private def natLit (n : Nat) : Expr := .lit n.toFloat.toFloat32.toBits

private def anyOf (x : String) (vs : List Nat) : Expr :=
  match vs with
  | [] => ff
  | v :: rest => rest.foldl (fun e w => e ∨. (Expr.var x =. natLit w)) (Expr.var x =. natLit v)

/-- The parameters the X500 airframe (4001_gz_x500) sets among navigator's. -/
def x500Sets : List (String × Expr) := [("NAV_ACC_RAD", num 2), ("RTL_RETURN_ALT", num 30),
  ("RTL_DESCEND_ALT", num 10)]

def x500Params : List Clause :=
  (Ports.paramDefaults.filter fun c => !x500Sets.any fun (n, _) => c.name == s!"default_{n}") ++
  x500Sets.map fun (n, v) => ⟨s!"x500_{n}", Expr.var n =. v⟩

private def isTime (n : String) : Bool := n.endsWith "_timestamp" || n.endsWith "_timestamp_sample"

private def ofTopics (topics : List String) (n : String) : Bool :=
  topics.any fun t => n.startsWith (t ++ "_")

def inf : Expr := .lit 0x7f800000

/-- Every input field of `topics` pinned to its value in `vals`, or 0 / false (`_updated` true),
except the fields of `free` and the timestamps. -/
def pinned (topics : List String) (vals : List (String × Expr)) (free : List String) :
    List Clause :=
  Ports.input.toList.filterMap fun f =>
    if !ofTopics topics f.name || free.contains f.name || isTime f.name then none
    else
      let v := (vals.lookup f.name).getD (if f.name.endsWith "_updated" then tt
        else if f.type == .bool then ff else num 0)
      some ⟨s!"pin_{f.name}", Expr.var f.name =. v⟩

def lat : Float := 47.397742
def lon : Float := 8.545594
def alt : Float := 488

/-- The vehicle as commander, the estimator and the land detector publish it every tick: armed,
airborne, a rotary wing, home set at the SITL home, position valid. -/
def flyingTopics : List String := ["vehicle_status", "vehicle_land_detected",
  "vehicle_local_position", "vehicle_global_position", "home_position"]

def flyingValues : List (String × Expr) := [
  ("vehicle_status_arming_state", num 2), ("vehicle_status_vehicle_type", num 1),
  ("vehicle_status_system_id", num 1), ("vehicle_status_component_id", num 1),
  ("vehicle_status_pre_flight_checks_pass", tt),
  ("vehicle_local_position_xy_valid", tt), ("vehicle_local_position_z_valid", tt),
  ("vehicle_local_position_v_xy_valid", tt), ("vehicle_local_position_v_z_valid", tt),
  ("vehicle_local_position_xy_global", tt), ("vehicle_local_position_z_global", tt),
  ("vehicle_local_position_heading_good_for_control", tt),
  ("vehicle_local_position_ref_lat", num lat), ("vehicle_local_position_ref_lon", num lon),
  ("vehicle_local_position_ref_alt", num alt), ("vehicle_local_position_eph", num 0.5),
  ("vehicle_local_position_epv", num 0.5), ("vehicle_local_position_vxy_max", inf),
  ("vehicle_local_position_vz_max", inf), ("vehicle_local_position_hagl_min", inf),
  ("vehicle_local_position_hagl_max_z", inf), ("vehicle_local_position_hagl_max_xy", inf),
  ("vehicle_global_position_lat_lon_valid", tt), ("vehicle_global_position_alt_valid", tt),
  ("vehicle_global_position_eph", num 0.5), ("vehicle_global_position_epv", num 0.5),
  ("home_position_lat", num lat), ("home_position_lon", num lon), ("home_position_alt", num alt),
  ("home_position_valid_alt", tt), ("home_position_valid_hpos", tt),
  ("home_position_valid_lpos", tt), ("home_position_update_count", num 1)]

/-- Free within the flight: the auto modes navigator serves, the position within 100 m of home and
10-60 m up (local and global consistent only roughly: each in its own range). -/
def flyingFree : List Clause := [
  ⟨"auto_mode", anyOf "vehicle_status_nav_state" [3, 4, 5, 17, 18]⟩,
  ⟨"user_intention", anyOf "vehicle_status_nav_state_user_intention" [3, 4, 5, 17, 18]⟩,
  ⟨"near_home", abs "vehicle_local_position_x" ≤. 100 ∧. abs "vehicle_local_position_y" ≤. 100 ∧.
      -60 ≤. "vehicle_local_position_z" ∧. "vehicle_local_position_z" ≤. -10 ∧.
      abs "vehicle_local_position_vx" ≤. 5 ∧. abs "vehicle_local_position_vy" ≤. 5 ∧.
      abs "vehicle_local_position_vz" ≤. 2 ∧. abs "vehicle_local_position_heading" ≤. 3.14⟩,
  ⟨"global_near_home", 47.3968 ≤. "vehicle_global_position_lat" ∧.
      "vehicle_global_position_lat" ≤. 47.3986 ∧. 8.5443 ≤. "vehicle_global_position_lon" ∧.
      "vehicle_global_position_lon" ≤. 8.5469 ∧. 498 ≤. "vehicle_global_position_alt" ∧.
      "vehicle_global_position_alt" ≤. 548⟩]

/-- Mission traffic: mission messages naming 6 or 7 with up to 10 items, no mirrored storage
requests (the storage is empty; the stored mission of the hand-checked case is the nominal one). -/
def missionTraffic : List Clause := [
  ⟨"dm_none", "dataman_request_mirror_count" =. 0⟩,
  ⟨"mission_storage", anyOf "mission_mission_dataman_id" [6, 7]⟩,
  ⟨"mission_fence", anyOf "mission_fence_dataman_id" [3, 4]⟩,
  ⟨"mission_safe_points", "mission_safepoint_dataman_id" ≤. 1⟩,
  ⟨"mission_count", "mission_count" ≤. 10⟩,
  ⟨"mission_seq", -1 ≤. "mission_current_seq" ∧. "mission_current_seq" ≤. 9⟩,
  ⟨"mission_land", "mission_land_start_index" =. -1 ∧. "mission_land_index" =. -1⟩]

/-- The clock and the timestamps of the vehicle topics: one 400 Hz tick per step from 1 s. -/
def tickHints : List Hint :=
  Hint.increasing "t_us" 1000000 2500 2500 :: ((Ports.input.toList.filter fun f =>
    isTime f.name && ofTopics ("mission" :: "dataman_request" :: flyingTopics) f.name).map
      fun f => Hint.increasing f.name 1000000 2500 2500)

/-- What a campaign of this module alone keeps: no source mark on generated storage words, and
the first statement's pacing of commands (the window input cannot make it). -/
def standalone : List Clause := [
  ⟨"no_mark", "dataman_request_mirror_by_px4_mavlink" =. ff⟩,
  ⟨"command_paced", "vehicle_command_count" =. 0 ∨.
    ("vehicle_command_count" =. 1 ∧. "vehicle_status_updated")⟩]

/-- In flight in an auto mode, with mission traffic; no commands, no other inputs. -/
def flight : Regime where
  name := "flight"
  doc := "X500 parameters; armed, airborne near home in an auto mode; MAVLink mission traffic"
  clauses := x500Params ++ pinned flyingTopics flyingValues (flyingFree.flatMap (·.expr.vars)) ++
    flyingFree ++ missionTraffic ++ [
    ⟨"no_command", "vehicle_command_count" =. 0⟩,
    ⟨"no_gps", "vehicle_gps_position_updated" =. ff⟩,
    ⟨"no_controller_status", "position_controller_status_updated" =. ff ∧.
      "position_controller_landing_status_updated" =. ff⟩,
    ⟨"no_wind", "wind_updated" =. ff⟩] ++ standalone
  hints := tickHints

/-- PX4's defaults and the X500 airframe, any inputs, a 400 Hz clock. -/
def x500Clocked : Regime where
  name := "x500_clocked"
  doc := "PX4 defaults with the X500 airframe; any inputs; t_us advancing 2500 us per step"
  clauses := x500Params ++ standalone
  hints := [.increasing "t_us" 1000000 2500 2500]

def coverage : List Clause := [
  ⟨"triplet_published", "position_setpoint_triplet_updated" =. tt⟩,
  ⟨"position_setpoint", Expr.var (sp "current_valid") ∧. Expr.var (sp "current_type") =. 0⟩,
  ⟨"loiter_setpoint", Expr.var (sp "current_valid") ∧. Expr.var (sp "current_type") =. 2⟩,
  ⟨"mission_valid", "mission_result_valid" =. tt⟩,
  ⟨"mission_running", "mission_result_valid" ∧. ¬. "mission_result_finished"⟩,
  ⟨"next_setpoint", Expr.var (sp "next_valid") =. tt⟩]

def module : Module where
  name := "px4_navigator"
  doc := "PX4 navigator (v1.17.0) with dataman, unmodified: task modules run by the shim"
  params := Ports.params
  -- and the observer's command window (px4_cmd_window), which the PX4 code does not read
  input := Ports.input ++ Px4.Modules.Px4CmdWindow.output
  output := Ports.output
  contract := { contract with guarantee := contract.guarantee ++ Ports.outWidths }
  exe := "build/modules/px4_navigator/px4_navigator"
  stack := .px4
  regimes := [flight, x500Clocked]
  coverage := coverage

end Px4.Modules.Px4Navigator
