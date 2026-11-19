# 0. Status and layout

**2026-11-19:** imported into this repository (subproject `harness/`); the simulator module runs the repository's shared `sim/`; the ArduPilot stack flies the three gorge scenarios (doc 12) with the two-vehicle system `ap_formation` (doc 11). New files: `ardupilot/scenario.py`, `fly_gorge.sh`/`.py`, `qgc_bridge.py`, `fly_qgc.sh [abreast|staggered]`; `ardupilot/harnesses/ap_formation/`; `sim/modules/plant_formation/`; `tools/fetch_deps.sh`, `tools/build_modules.sh`, `tools/case_add_fields.py`. Later on 2026-11-19: the simulator modules' code hash no longer depends on where or when the world was built (the world cache is hashed by content, doc 3), so a fresh clone matches the committed evidence; `tools/check_fresh_clone.sh` checks that. This changed the code hash of `plant_sim`, `plant_formation` and the 16 systems that contain them once; their campaigns and served sessions were re-recorded with the commands their ledgers name and the superseded records removed. The same check found the supervisor's generated sources (`gen/out/shadow_*.cpp`) naming ArduPilot's headers by a path relative to where the checkout lies; they now name them relative to its `libraries/`, which changed the supervisor's code hash once (its campaign and the sessions of ap_full, ap_full_ekf and ap_formation re-recorded). `tools/build_modules.sh ardupilot` also writes the launcher of the module `top` (`build/top/top_serve`), which no script wrote before. The text below is the state at the import (2026-11-18); where it names `ardupilot/fly_qgc.sh [PORT]` that form still works (one vehicle).

The state of the two stacks as of the import into this repository (2026-11-18), moved here from the README, and the full list of development commands. The README has the short Build and Run sections; doc 11 has the two-vehicle formation.

**Status (2026-11-18): the whole ArduCopter stack flies as modules.** The ArduPilot stages are modules of real ArduPilot C++: `rate_pid` (one `AC_PID`), `mixer` (`AP_MotorsMatrix`, quad X, with hover-throttle learning), `position` (`AC_PosControl`), `attitude` (`AC_AttitudeControl_Multi`), `guidance` (`AC_WPNav`), `loiter` (`AC_Loiter`, with the attitude controller's command model it calls, compiled from the real AC_AttitudeControl.cpp), `estimator` (AP_InertialSensor, AP_AHRS, EKF3) and `supervisor` (ArduCopter's vehicle code: modes, arming, failsafes, mission, MAVLink); `plant_sim` is the gorge simulator. Systems compose them by port name: `rate`, `inner_loop`, `closed_inner`, `ap_ctl` (the controller chain rate → mixer → guidance → position → attitude, with its obligations), `ap_flight` (the chain in the simulator with the test fixtures `truth_est` and `script`), `ap_full` (the full stack with the supervisor, flown from a scripted ground station, `ardupilot/modules/supervisor/dev/fly.py`) and `ap_full_ekf` (the same with the real estimator). Controller commands carry the supervisor's call order (`cmd_<stage>_<method>_seq`). A served session (`harness serve`, how the ground-station flights run) writes `monitored` ledger records at its end, so flights back clauses; a session with a discharge failure shows its clauses as `undischarged`. `harness obligations NAME --status` prints, for each obligation of a composite, whether it is proved (by the link's transport or range checker, from neighbors' guarantees, the composite's assumption or the constants that feed it), stated (a discharge-table entry no checker proves: a hypothesis of the link theorem) or open: `ap_ctl` has 24, 17 proved, 5 stated and 2 open (the table's two hypotheses); `ap_full_ekf` has 77, 32 proved, 3 stated and 42 open (the controller chain's discharge table is shared by `ap_ctl`, `ap_flight`, `ap_full` and `ap_full_ekf`, `ardupilot/harnesses/chain/Discharges.lean`). The simulator's IMU saturates at a full scale (16 g, 2000 deg/s by default), which discharges the estimator's sample-range assumption. On `ap_full_ekf` with sensor noise (seed 1) the scenarios `guided`, `auto10`, `rtl`, `althold` and `loiter` of `fly.py` each end in a normal disarm with 0 guarantee violations and 0 discharge failures, recorded as served sessions (`harness status ap_full_ekf`); `loiter` also with seed 2 (hands-off hold drift against the simulator's truth 0.065 m and 0.101 m over 8 s). LOITER flies because AC_Loiter is its own stage, `loiter`, between `guidance` and `position`: the supervisor's `loiter_nav` calls are its commands (`cmd_loiter_<method>`, `_seq`), and its calls on AC_PosControl are handed to the position stage as the guidance stage hands AC_WPNav's (`lt_tgt_…`, `lt_cmd_position_…`). ALT_HOLD takes off because the position stage applies the same-tick throttle rule: a `D_init_controller` whose `_seq` follows the supervisor's `set_throttle_out` of the tick seeds the accel PID from that call's throttle, as in ArduCopter (`position`'s `sameTickThrottle`). The estimator takes `AP_AHRS::set_terrain_hgt_stable` as a command (the real call), so the supervisor's calls are all mapped in these flights (in ALT_HOLD and LOITER with RC one call remains unmapped: `AP_Motors::set_radio_passthrough`). `ardupilot/fly_qgc.sh [PORT]` flies `ap_full_ekf` from QGroundControl (default port 14550). A system is built by one call, `composeAll name [H1, H2, …]`, and `ardupilot/Top.lean` is a top-level harness compiled to its own executable. Every node has a contract, monitors at every level and a hash-bound ledger ([docs/9-nesting.md](docs/9-nesting.md)). The algebra is formalized in `Harness/Algebra.lean`, and the Lean ODE plant is a formal harness in `formal/PlantHarness.lean`. The formal link is built ([docs/10-formal-link.md](docs/10-formal-link.md), `Harness/Link.lean`): one Lean theorem, proved for every system as the runtime steps it, that the children's contracts as wired give the system's contract, with the remaining hypotheses named (each module's leaf claim, the stated discharges, the open obligations); `harness link NAME` prints them. Not built: AC_Circle (no stage holds it, so CIRCLE does not fly), model checking. Open obligations of the composition are listed by `harness obligations ap_ctl` (doc 9).

**PX4 (2026-11-18): the whole PX4 stack flies as modules, from main.** Both stacks are now in this project. The PX4 stages are modules of real, unmodified PX4 v1.17.0 C++ (deps/px4) behind one generic shim (px4/shim: the uORB bus, parameters, the work queue and task scheduler, logging, byte-stream devices) with their ports generated from PX4's .msg and parameter files (px4/ports.py): `px4_sensors`, `px4_ekf2`, `px4_rate` (mc_rate_control), `px4_att` (mc_att_control), `px4_pos` (mc_pos_control), `px4_fmm` (flight_mode_manager with its flight tasks), `px4_land` (land_detector), `px4_alloc` (control_allocator), `px4_commander`, `px4_navigator` (with its dataman in process), `px4_mavlink` (PX4's MAVLink on byte ports), the generated merge node `px4_merge_ack`, the bridges to the shared simulator `px4_sim_in` and `px4_sim_out`, and test drivers. They compose by topic field name with no renames: `px4_inner`, `px4_closed_rate`, `px4_est`, `px4_est_flying`, `px4_att_loop`, `px4_pos_loop`, `px4_auto_loop`, `px4_cmd_loop` (with PX4's commander), `px4_nav_loop` (with the navigator) and `px4_full` (no test driver: every command arrives as MAVLink bytes). The PX4 regimes pin the simulator's IMU full scale to its defaults (`imu_full_scale_default`). `harness run px4_cmd_loop --steps 14000 --seed 3 --regime x500_cmd_step_noise`: 0 violations of its 71 clauses and of the 68 monitored inner clauses, all 13 discharge rows held at every step. Headless flights of `px4_full` over UDP 127.0.0.1:14570 (`px4/harnesses/px4_full/dev/fly_headless.sh commands|mission SEED`, seed 1): every stage passes, PX4 lands and disarms by itself, every GLOBAL_POSITION_INT report within 0.52 m horizontally and 0.85 m in altitude of the simulator's truth; the stack keeps real time (step round trip 1.5 ms of the 2.5 ms tick). Navigator's input conditions are restated from the code: its mission storage may come from MAVLink's mirror port, which px4_mavlink marks as its mission manager's (`dataman_request_mirror_by_px4_mavlink`, guarantee `mirror_from_mission_manager`, discharged through the PX4 discharge table), and its command pacing is a bound per pass window (at most 4 external commands in any 400 ticks), counted by the observer `px4_cmd_window`; that bound is an assumption on the ground station's traffic (MAVLink does not enforce it), monitored at every tick. The headless flights now end with 0 discharge failures, and `harness status px4_full` is backed by the served sessions. `px4/fly_qgc.sh [PORT]` flies `px4_full` from QGroundControl (default port 14550; the vehicle sends first, its first heartbeat about 20 s after the start). The PX4 discharge table (`px4/harnesses/px4_chain/Discharges.lean`) discharges the width and slot obligations between generated ports by the publisher's generated guarantees (`Ports.outWidths`, facts of the generated glue), MAVLink's mirror mark and the observer's window: `harness obligations NAME --status` gives `px4_inner` 18 (2 proved, 16 stated, 0 open), `px4_cmd_loop` 348 (181 proved, 16 stated, 151 open), `px4_full` 535 (364 proved, 17 stated, 154 open); the 16 stated are signed (int8) widths, which the range checker does not compare (it reads f32 words and u32 below 2^24). The registry is lazy: a system is composed when it is named (`harness list` does not compose them; `harness list --compose` does), so a command starts in milliseconds.

## Layout

```
Harness/              the generic Lean library: schemas, contracts, protocol client, systems, compose, campaigns, ledger, CLI
cpp/module_protocol.h the generic C++ side of the module protocol
py/module_protocol.py the generic Python side
py/regime_case.py     a replayable case of a system from one of its regimes (also the relay's parameters)
py/replay_csv.py      a saved case replayed to a per-tick CSV
py/px4_case.py        records a PX4 module's hand-checked case from a script of derived values
ardupilot/            everything ArduPilot
  modules/<name>/     leaves: real ArduPilot C++ (rate_pid, mixer, position, attitude, guidance,
                      loiter, estimator, supervisor) and test fixtures (est_scenario, truth_est, script)
  harnesses/<name>/   compositions (rate, inner_loop, rate_c, inner_loop_c, top, closed_inner,
                      est_loop, ap_ctl, ap_flight, ap_full, ap_full_ekf)
  build.sh            builds one ArduPilot module: ardupilot/build.sh NAME
  fly_qgc.sh          flies ap_full_ekf from QGroundControl: ardupilot/fly_qgc.sh [PORT] (14550 default)
  gen_mavlink.sh      the MAVLink headers waf would generate, once
  Top.lean            the top-level harness (ArduPilot's inner loop), compiled as `top`
px4/                  everything PX4 (v1.17.0, deps/px4, unmodified)
  modules/<name>/     leaves: real PX4 C++ (px4_rate, px4_alloc, px4_sensors, px4_ekf2, px4_att,
                      px4_pos, px4_fmm, px4_land, px4_commander, px4_navigator, px4_mavlink), the
                      generated merge node px4_merge_ack, the simulator bridges px4_sim_in and
                      px4_sim_out, test drivers px4_drive_att, _pos, _auto, _cmd, _nav, the observer
                      px4_cmd_window (vehicle_command per 400 ticks); px4_common (clause helpers, no node)
  harnesses/<name>/   compositions (px4_inner, px4_closed_rate, px4_est, px4_est_flying,
                      px4_att_loop, px4_pos_loop, px4_auto_loop, px4_cmd_loop, px4_nav_loop,
                      px4_full; px4_full/dev: the UDP relay, the scripted ground station, headless flights)
  harnesses/px4_chain/ the PX4 discharge table shared by the compositions (Discharges.lean)
  shim/               the generic uORB / work-queue / parameter / task / byte-stream shim every PX4 module links
  ports.py            a PX4 module's ports from px4.txt and PX4's .msg and parameter files
  gen.sh, build.sh    PX4's generated headers, once; one PX4 module: px4/build.sh NAME
  plain_build.sh      a PX4-stack module with no PX4 sources (bridges, drivers); px4/build.sh calls it
  fetch_mavlink.sh    PX4's pinned MAVLink (33af200d) into build/src/mavlink, once, and the Python dialect
  fly_qgc.sh          flies px4_full from QGroundControl: px4/fly_qgc.sh [PORT] (14550 default)
  px4_test_drive.h    the test drivers' shared script (not PX4 code)
sim/                  shared by both stacks
  modules/plant_sim/  the gorge simulator as a module, with its build.sh
formal/               the ODE plant as a formal harness, and its check
deps/                 mavlink and PX4 clones (read only)
docs/                 the design documents
tools/import_node.sh  brings a node from an old-layout copy (modules/, harnesses/ side by side) into this layout
Main.lean             the `harness` command and its registry, grouped by stack
```

Each node declares its stack (`stack := .ardupilot`, `.px4` or `.sim` on a module; a system takes the one flight stack its children other than `sim` share, or declares one). The stack gives the node's folder, STACK/modules/NAME or STACK/harnesses/NAME, where its evidence (`evidence/ledger.json`, `evidence/tested/`) lives. Node names are unique across stacks. Build products stay in `build/modules/NAME`, `build/gen/NAME` and `.lake/`.


## All development commands

```
LEAN_NUM_THREADS=1 lake build
ardupilot/build.sh rate_pid
ardupilot/gen_mavlink.sh                   # once, for mixer; reads deps/mavlink (ArduPilot/mavlink at the pinned commit)
ardupilot/build.sh mixer
px4/gen.sh                                 # once, for the PX4 modules; reads deps/px4, writes build/gen/px4
px4/fetch_mavlink.sh                       # once, for px4_mavlink: PX4's pinned MAVLink into build/src/mavlink
for m in px4_rate px4_alloc px4_sensors px4_ekf2 px4_att px4_pos px4_fmm px4_land px4_commander \
         px4_navigator px4_mavlink px4_merge_ack px4_sim_in px4_sim_out px4_drive_att px4_drive_pos \
         px4_drive_auto px4_drive_cmd px4_drive_nav; do px4/build.sh $m; done   # about 4 min
sim/modules/plant_sim/build.sh             # the simulator module; reads the ArduLean repository, writes nothing there
for m in position attitude guidance loiter script; do ardupilot/build.sh $m; done
ardupilot/modules/estimator/build.sh       # EKF3 and the sensor front ends (4 compiles at a time)
ardupilot/modules/supervisor/build.sh      # ArduCopter's vehicle code (4 compiles at a time)
ardupilot/modules/truth_est/build.sh       # a Python fixture
ardupilot/modules/supervisor/dev/gen_pymavlink.sh   # the Python MAVLink dialect fly.py uses
.lake/build/bin/harness obligations ap_ctl --status
.lake/build/bin/harness test ap_ctl --regime auto_wp --cases 30 --steps 400
.lake/build/bin/harness run ap_flight --steps 8000 --regime quiet --log build/ap_flight.csv   # a 20 s flight, per-tick CSV
python3 -I ardupilot/modules/supervisor/dev/fly.py guided --node ap_full --noise --csv build/a.csv
python3 -I ardupilot/modules/supervisor/dev/fly.py guided --node ap_full_ekf --noise --steps 32000 --csv build/b.csv
python3 -I ardupilot/modules/supervisor/dev/fly.py auto10 --node ap_full_ekf --noise --steps 40000
python3 -I ardupilot/modules/supervisor/dev/fly.py rtl --node ap_full_ekf --noise --steps 48000
python3 -I ardupilot/modules/supervisor/dev/fly.py althold --node ap_full_ekf --noise --steps 48000   # --seed N for another noise seed
python3 -I ardupilot/modules/supervisor/dev/fly.py loiter --node ap_full_ekf --noise --seed 2 --steps 50000   # prints the hold drift and nudge response
python3 -I ardupilot/modules/loiter/hand-checked-case.py   # the loiter stage's hand-checked case, worked out and replayed
.lake/build/bin/harness test supervisor --regime rest --seed 1 --cases 10 --steps 200
.lake/build/bin/harness status ap_full_ekf
ardupilot/fly_qgc.sh                       # QGroundControl on its default UDP port 14550; Ctrl-C stops
.lake/build/bin/harness run px4_cmd_loop --steps 14000 --seed 3 --regime x500_cmd_step_noise   # PX4 with its commander, 35 s
px4/harnesses/px4_full/dev/fly_headless.sh commands 1   # the whole PX4 stack from a scripted ground station on UDP 14570
px4/harnesses/px4_full/dev/fly_headless.sh mission 1    # (SEED last; logs in build/logs/full_MODE_SEED.*)
px4/fly_qgc.sh                             # PX4 from QGroundControl on its default UDP port 14550; Ctrl-C stops
.lake/build/bin/harness status px4_full
.lake/build/bin/harness list
.lake/build/bin/top tree --depth 1          # the top-level harness of ardupilot/Top.lean, compiled
.lake/build/bin/harness test closed_inner --regime stock_hover --cases 4 --steps 400   # C++ and simulator in one loop
.lake/build/bin/harness tree inner_loop
.lake/build/bin/harness test inner_loop --regime stock_flight --cases 40 --steps 500
.lake/build/bin/harness status inner_loop
bash formal/check.sh                       # the ODE plant harness, against the plant library's build
```

ArduPilot's checkout is read from `$ARDUPILOT_ROOT` (default `deps/ardupilot`, fetched by `tools/fetch_deps.sh`) and never modified. See [docs/8-first-example.md](docs/8-first-example.md).

