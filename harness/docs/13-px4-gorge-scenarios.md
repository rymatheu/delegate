# 13. The gorge scenarios on the PX4 stack

**Status (2026-11-19):** the three scenarios fly on the PX4 stack (PX4 v1.17.0, unmodified, one harness per module),
headless and from a stand-in QGroundControl with live video.

| Scenario | Node | Vehicles | Plan files (px4/plans) |
|---|---|---|---|
| `single` | `px4_full` | one, MAVLink system 1 | `gorge.plan` |
| `abreast` | `px4_formation`, `formation` 1 | two side by side, systems 1 and 2 | `formation-abreast-v1.plan`, `-v2.plan` |
| `staggered` | `px4_formation`, `formation` 2 | two staggered, vehicle 2 rear and nose-backward | `formation-staggered-v1.plan`, `-v2.plan` |

Commands, from `px4/`: `./fly_qgc.sh [abreast|staggered]` (QGroundControl) and `./fly_gorge.sh
[single|abreast|staggered]` (no ground station). The pieces: `px4/harnesses/px4_full/dev/relay.py` (the served
session, one UDP socket per vehicle toward the ground station's port, the camera poses, the truth CSVs),
`px4/gorge/gcs.py` (the scripted ground station of `fly_gorge.sh` and of the stand-in session check),
`px4/gorge/make_plans.py` (the plans), `px4/gorge/metrics.py` and `summary.py` (clearance, heading, separation,
PASS/FAIL), `px4/gorge/session_check.py` (the stand-in QGroundControl session with the video check).

## The plans

PX4 flies neither NAV_SPLINE_WAYPOINT nor CONDITION_YAW in a mission, so the simulator's ArduCopter plans
(`sim/plans`) are rewritten item by item by `px4/gorge/make_plans.py` (deterministic; never edited by hand): the
takeoff, DO_CHANGE_SPEED 2 m/s (PX4's MPC_XY_CRUISE is 5 m/s), one NAV_WAYPOINT per spline waypoint at the same point
and altitude (straight legs; acceptance radius 1 m in param 2), and the landing. No point is added: the route's
waypoints lie on the gorge's centerline, or a constant offset from it, and the straight leg between two of them stays
within 0.35 m of the centerline (`Gorge.flight_path`, max_dev). Where the land site is not the last waypoint (the
formation plans' level land sites), a waypoint above the land site at the last waypoint's altitude and heading comes
before NAV_LAND, because PX4 drops a land item's yaw (`mission_base.cpp:624`) and would turn to face the site.

Clearance achieved (headless flights below, the simulator's measure: the closest distance from the vehicle's
collision body to any body of the gorge, floor and rocks included, in the air): 1.63 m for the single vehicle, 1.45 m
and 2.10 m abreast, 1.53 m and 0.97 m staggered (vehicle 2's least is at north 5.3 m while it still climbs to the
route's height, 2.5 m above the start). The plant's own `wall_clear` (side walls only, capped at 2 m) stayed at its cap
for every vehicle.

## The nose-backward vehicle

Vehicle 2 of `staggered` starts facing south (the shared simulator's `FormationPlant`). Each CONDITION_YAW heading of
the source plan becomes param 4 (yaw) of the waypoint after it; navigator puts a mission item's yaw into the
position-setpoint triplet (`mission_block.cpp:627`) and the flight task holds it (`FlightTaskAuto`: a finite triplet
yaw overrides MPC_YAW_MODE); navigator accepts the waypoint when the heading is within MIS_YAW_ERR (12 deg). No
parameter is changed. Measured (headless, seed 1): after the first leg, heading minus direction of travel median
-177.4 deg, 95 % of the 100 Hz samples within 6.9 deg of it, all within 12.7 deg.

What this found: px4_fmm's assumption `triplet_in_range` held a setpoint's yaw to [-π, π]. MAVLink's mission manager
stores param 4 as `wrap_2pi(radians(param4))` (`mavlink_mission.cpp:1443`), in [0, 2π), so every heading above
180 deg (the rear vehicle's run 162 to 189 deg) failed it at its first such waypoint (a discharge failure in the
served session; the obligation was open, no discharge stated). The assumption now admits [-π, 2π] (NaN still
allowed), the code's range; px4_fmm's guarantee `setpoint_yaw_in_range` ([-π, π] on its output) held throughout.
px4_fmm's campaign was re-recorded under the new contract.

## Two PX4 stacks in one gorge

`px4_formation` (doc 11): `composeAll [plant_formation, inst px4_vehicle "v1" ["t_us"], inst px4_vehicle "v2"
["t_us"]]`, where `px4_vehicle` is px4_full's children after plant_sim (the bridges stay) with px4_full's discharges;
px4_full's truth clause (EKF2 against the simulator) becomes the formation's, once per vehicle; plus `min_separation`
(1.5 m) and `wall_clearance` (0.5 m), monitored at every tick; `concurrently`. Nothing is shared between the stacks but
the clock: each has its own parameters (vehicle N gets `vN_MAV_SYS_ID` = N), its own MAVLink byte ports and UDP
socket, and its own dataman (RAM backend, in process); no PX4 module opens a file. Every vehicle gets px4_full's
regime `x500_full_noise` under its prefix; vehicle 2's noise seed is the session's + 100 (the plant's).

## How the mission reaches the vehicle

Through the real mission protocol, never onboard at boot: in a QGroundControl session the person uploads each
vehicle's plan (Plan view), then arms and starts the mission; in `fly_gorge.sh` the scripted ground station does the
same as QGroundControl does (heartbeats, the parameter list, MISSION_COUNT and MISSION_ITEM_INT per request, then arm
and MAV_CMD_MISSION_START; with two vehicles both are armed and started together) and waits for PX4's own landing and
disarm. Navigator's assumption that external commands come at most 4 per 400 ticks (an obligation on the ground
station's traffic, monitored by `px4_cmd_window`) held: the scripted station sent at most 2 per vehicle second.
PX4's MAVLink receiver answers REQUEST_MESSAGE itself and ignores commands addressed to the camera's component, so
QGroundControl's discovery traffic does not count; a real QGroundControl session was not run here.

## Measured (2026-11-19, sensor noise on, seed 1; vehicle 2 seed 101)

Headless (`fly_gorge.sh`, stepped as fast as it goes, the scripted ground station in the loop; the wall time includes
the session's end, when the ledger is written):

| | single | abreast | staggered |
|---|---|---|---|
| result | PASS | PASS | PASS |
| simulated / wall | 69.2 s / 25.5 s | 74.9 s / 67.7 s | 72.6 s / 65.7 s |
| mean step round trip (of the 2.5 ms tick) | 0.81 ms | 1.73 ms (two stacks, concurrent) | 1.72 ms |
| mission | every waypoint and the landing reached, disarmed by PX4 | both | both |
| min clearance in the air | 1.63 m | 1.45 m, 2.10 m | 1.53 m, 0.97 m |
| min separation (centers, collision bodies) | | 1.75 m, 1.20 m | 3.04 m, 2.51 m |
| guarantee violations, discharge failures | 0, 0 (17 instances) | 0, 0 (34 instances) | 0, 0 (34 instances) |

Stand-in QGroundControl sessions with video (`px4/gorge/session_check.py SCENARIO`, test ports): the launcher
started as a person starts it, every vehicle's heartbeat, parameters, plan upload, each camera's heartbeat,
CAMERA_INFORMATION and VIDEO_STREAM_INFORMATION, every stream decoded for 8 s (RGB 640 x 480 at 10.0 to 10.2 fps,
thermal 640 x 512 at 8.65 to 8.78 fps, not blank), arm, mission start, the flight to PX4's disarm, all processes gone
after SIGTERM, the monitors clean: PASS for all three (7/7, 9/9, 9/9; load average 1.9 to 4.7). The shared check
`sim/checks/video_check.py staggered --launcher px4/fly_qgc.sh` (with the switch of the shared RGB port from vehicle 1's
camera to vehicle 2's): PASS 19/19. Under a load average near 10 the RGB rate fell to 7.0 fps and once, with two
vehicles, to none in the 8 s window (the cameras run at low priority by design); not seen at the load above.

Real time (the same sessions, paced at one tick per 2.5 ms): one vehicle keeps real time (at most 3 ticks behind,
mean step 0.91 ms); two vehicles stay within 166 ticks (0.42 s) of real time over the flight (mean step 1.91 ms of
2.5, both stacks stepped concurrently), so they run in real time with that lag.

## Evidence

`harness status px4_full` and `px4_formation`: every clause backed (served sessions of these flights). Re-recorded
after the shared simulator changed plant_sim's code hash and contract: px4_cmd_loop (`harness test px4_cmd_loop
--seed 7 --cases 1 --steps 14000 --regime x500_cmd_step_noise`), px4_nav_loop (`--seed 1 --cases 1 --steps 20000
--regime x500_nav_noise`), px4_fmm (`--seed 33 --cases 20 --steps 100 --regime x500_loiter`, its new contract):
0 violations. The five intermediate loops and px4_est_flying, never recorded before, each got one campaign
(seed 1, one case: px4_closed_rate `x500_hover` 2000 steps, px4_est `rest_noise` 4000, px4_est_flying `hover_noise`
4000, px4_att_loop `x500_takeoff_noise` 6000, px4_pos_loop `x500_step_noise` 8000, px4_auto_loop `x500_auto_step_noise`
8000), and the modules' own campaigns were rerun with the commands their ledgers name, which backs the generated
`width_*` guarantees added after those campaigns first ran (px4_sensors 27, px4_alloc 19, px4_ekf2 24, px4_commander
35, px4_pos 1): 0 violations. Every PX4 node is backed except `px4_vehicle` by itself (321 clauses), whose clauses are
monitored inside `px4_formation` (the instances v1 and v2) and backed there.

The headless runs are not bit-for-bit repeatable when two vehicles fly: the scripted ground station runs on the wall
clock, so its commands reach the vehicles at different ticks from run to run. A second `staggered` run (in this
repository after the import) gave 76.2 s simulated, clearance 1.53 m and 1.12 m, separation 3.16 m and 2.63 m, and the
rear vehicle's heading after the first leg 171.2 deg from the direction of travel (95 % within 13.3 deg); the single
vehicle repeated exactly.
