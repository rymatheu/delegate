# 12. The gorge scenarios on the ArduPilot stack

**Status (2026-11-19):** the three scenarios fly on the real-estimator stack, headless and from a stand-in
QGroundControl with live video.

| Scenario | Node | Vehicles | Plan files (sim/plans) |
|---|---|---|---|
| `single` | `ap_full_ekf` | one, MAVLink system 1 | `gorge.plan` |
| `abreast` | `ap_formation`, `formation` 1 | two side by side, systems 1 and 2 | `formation-abreast-v1.plan`, `-v2.plan` |
| `staggered` | `ap_formation`, `formation` 2 | two staggered, vehicle 2 rear and nose-backward | `formation-staggered-v1.plan`, `-v2.plan` |

Commands, from `ardupilot/`: `./fly_qgc.sh [abreast|staggered]` (QGroundControl) and `./fly_gorge.sh
[single|abreast|staggered]` (no ground station). The shared pieces are `ardupilot/scenario.py` (node, parameters per
vehicle, plan files as mission items), `ardupilot/fly_gorge.py` (headless) and `ardupilot/qgc_bridge.py` (real time).

## How the mission reaches the vehicle

Through the real mission protocol, never onboard at boot: in a QGroundControl session the person uploads each
vehicle's plan file (Plan view); in `fly_gorge.sh` a scripted ground station per vehicle (the shared simulator's
`gorgesim.ground_station.GCS`) uploads the same file's items (home, TAKEOFF, the spline waypoints, LAND; vehicle 2 of
`staggered` also a CONDITION_YAW before each spline waypoint), downloads them back and compares, then GUIDED, arm,
takeoff, AUTO. With two vehicles every phase waits for both, so they take off and enter AUTO at the same tick.
The nose-backward vehicle holds the CONDITION_YAW heading on the spline legs because its WP_YAW_BEHAVIOR is 0, set at
boot by the supervisor's parameter `wp_yaw_behavior` (2, ArduCopter's default, for the other vehicles).

No stage was missing: the guidance stage (`AC_WPNav`) already holds the spline legs, and the supervisor
(ArduCopter's mode code) issues `set_spline_destination_NED_m` for SPLINE_WAYPOINT and the yaw commands for
CONDITION_YAW. One port was added: EKF3's status texts ("EKF3 IMU0 is using GPS", ...) are written in the estimator
stage, whose GCS is a stand-in; they now leave it as `est_text_*` (one text per tick, at most 50 characters, a queue
of 8) and the supervisor's real GCS sends them, as ArduCopter's one GCS does. Before, a ground station never saw them.

## What the formation contract adds

`ap_formation` (doc 11) adds `min_separation` (the two true positions at least 1.5 m apart) and `wall_clearance`
(each vehicle at least 0.5 m from the gorge's side surfaces, `v*_wall_clear` of the plant), monitored at every tick of
every served session.

## Measured (2026-11-19, sensor noise on, seed 1; vehicle 2 seed 101)

Headless (`fly_gorge.sh`, stepped as fast as it goes, scripted ground stations in the loop):

| | single | abreast | staggered |
|---|---|---|---|
| result | PASS | PASS | PASS |
| simulated / wall | 81.0 s / 22.6 s | 82.0 s / 49.2 s | 81.0 s / 47.4 s |
| mission | 11 spline items reached, LAND, disarmed | both: 11, LAND, disarmed | both: all spline items, LAND, disarmed |
| landing error | (see out/gorge-single.json) | 0.16 m, 0.07 m | 0.11 m, 0.08 m |
| min wall clearance in the air | 1.15 m | 1.33 m, 1.31 m | 1.25 m, 2.0 m (capped) |
| min separation | | 1.68 m | 2.83 m |
| guarantee violations, discharge failures | 0, 0 | 0, 0 | 0, 0 |

Vehicle 2 of `staggered` flies nose-backward: in AUTO above 1.5 m its heading stays within 26 degrees of south
(|yaw| ≥ 154 deg) while the route runs north.

Stand-in QGroundControl sessions with video (`sim/checks/video_check.py SCENARIO --launcher ardupilot/fly_qgc.sh
--mission`, test ports): every vehicle's heartbeat, each camera's MAVLink component and streams decoded (RGB and
thermal, both vehicles' with the RGB switch), the mission uploaded by the stand-in ground station, GUIDED, arm,
takeoff, AUTO past the first spline waypoint, all processes gone after SIGTERM: PASS for all three (10/10, 20/20,
20/20 checks). Real-time factor with video running (the bridge's Pacer line): one vehicle 57.54 s simulated in 58.38 s
wall (0.986; mean step work 1.22 ms of the 2.5 ms tick, p99 4.6 ms); two vehicles 55.25 s in 56.77 s (0.973; mean
1.93 ms, p99 6.5 ms) and 55.70 s in 57.10 s (0.975; mean 1.77 ms, p99 4.1 ms). Two vehicles hold real time on
average, with a third to a half of the ticks ending late by a few milliseconds and caught up after; the session ended
1.4 to 1.5 s behind the wall clock, most of it from the boot. The served sessions had 0 guarantee violations and 0
discharge failures.

Concurrency: `ap_formation` served with its two stacks stepped concurrently and with `HARNESS_SEQUENTIAL=1` gives
byte-identical output records over 2000 ticks (1.2 to 1.5 ms per tick either way at rest; the gain is small for two
ArduPilot stacks, which hold real time stepped one after the other).
