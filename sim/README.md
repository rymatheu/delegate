# Closed-loop flights of the two vehicles

This directory flies the two copter vehicles against the gym-pybullet-drones simulator, with the
Crazyflie 2.x model in the X configuration (CF2X):

- `copter_lean` (`lean/.lake/build/bin/copter_lean`): the Lean translations of ArduPilot's
  AP_MotorsMatrix, AC_AttitudeControl_Multi, AC_PosControl and AC_WPNav and of the AHRS view
  derivation, with the mission harness of `lean/Vehicle.lean`;
- `copter_ref` (`build/vehicle/copter_ref`): the same ArduPilot classes compiled unmodified with the
  stub headers of `ardupilot/stubs`, with the same harness in C++ (`ardupilot/vehicle/copter_ref.cpp`).

Both are built by `ardupilot/vehicle/build.sh` and speak the lock-step protocol of `PROTOCOL.md`:
the simulator writes the vehicle's state as ArduPilot's AHRS reports it (17 numbers per 400 Hz tick)
and reads back the four actuator outputs, which it turns into propeller speeds. No controller
bundled with gym-pybullet-drones is used; the simulator only integrates the rigid-body physics of
the propeller speeds it is given.

## Setup

The simulator lives in a virtual environment `.venv` (Python 3.12, created with uv).
gym-pybullet-drones is not on PyPI, so it is installed from the GitHub archive of the utiasDSL
repository. PyBullet has no prebuilt wheel for this platform and is built from source; its bundled
zlib defines `fdopen` as a macro that collides with the macOS SDK headers, which the `CFLAGS`
setting below works around.

```
cd sim
/opt/homebrew/bin/uv venv --python 3.12 .venv
CFLAGS="-Dfdopen=fdopen" /opt/homebrew/bin/uv pip install --python .venv/bin/python pybullet
/opt/homebrew/bin/uv pip install --python .venv/bin/python \
  "gym-pybullet-drones @ https://github.com/utiasDSL/gym-pybullet-drones/archive/refs/heads/main.zip" \
  numpy matplotlib scipy
```

Here `.venv` is a symbolic link to an existing environment created this way (Python 3.12.13,
gym-pybullet-drones 2.2.0, pybullet 3.2.7, numpy 2.5.4, scipy 1.18.1, matplotlib 3.11.2).

## The driver (`run_copter.py`)

```
.venv/bin/python run_copter.py --backend bin --bin PATH [--params FILE]... [--set 'NAME VALUE']...
    [--duration S] [--hold S] [--tol M] [--pass-tol M] [--out DIR] [--no-plots]
    [--init N E D] [--init-accel hover|freefall]
.venv/bin/python run_copter.py --check-frames      # conversion and motor-map checks, no controller
```

`--bin` names the vehicle (`copter_lean` or `copter_ref`; default `copter_lean`); `--params` are
passed to it (default `params/copter-cf2x.txt`). The simulator is `CtrlAviary` with
`DroneModel.CF2X` and `Physics.PYB` (no drag, ground effect or downwash), physics at 1200 Hz
(`--pyb-hz`) and control at 400 Hz, so each command is held for three physics steps; gravity is
ArduPilot's `GRAVITY_MSS`. The vehicle starts at rest on the ground at the origin, facing north;
with `--init N E D` (also spelled `--init-ned`) it starts level, facing north and at rest at that NED
position instead: in the air, or resting on the ground at N, E when D is 0 or the altitude -D is
below the resting altitude of the vehicle on the ground (0.0135 m, where its collision cylinder would
overlap the ground plane). An in-air start reports the specific force (0, 0, -g) on the first tick
(`--init-accel hover`, the default), the reading of a vehicle held at rest by its hover thrust: the
vehicles take over hovering at `MOT_THST_HOVER` (`PROTOCOL.md`, `run.start_hover`) and their first
actuators apply that thrust. `--init-accel freefall` reports (0, 0, 0), the reading of a vehicle
released with no thrust; on that single reading both vehicles cut the throttle (to 0.12 to 0.30
within 0.2 s) and an in-air start below about 0.12 m sinks to the ground before it climbs. A
run ends when every waypoint has been passed in order (within `--pass-tol`, 0.2 m) and the last one
has then been held within `--tol` (0.1 m) for `--hold` seconds (3 s), at the time limit
(`--duration`), when roll or pitch passes 80 degrees, or when the vehicle is still on the ground
after 3 s. After the flight the recorded state lines are replayed through the same binary with
`--trace`; the driver checks that the replayed actuators equal the flown ones (an error otherwise)
and stores the 18 trace numbers.

Each run writes to `--out`: `flight.csv` (per tick: time, NED position, velocity, specific force,
quaternion, Euler angles, body rates, the four actuators, the controller's round-trip time, and the
18 trace numbers), `inputs.txt` and `motors.txt` (the lines sent to and received from the vehicle),
`trace.txt`, `summary.txt`, and the plots `timeseries.png` and `path.png`.

Changes from the earlier driver this one was copied from: the frame conversion helpers it imported
from another script are defined in it, `--bin` defaults to `copter_lean`, the `lake` and `interp`
backends run `copter_lean` from `lean/`, and the summary and plot titles name the binary.

## Flights

Three missions, each flown with both vehicles (fresh runs, the same initial conditions), compared
tick by tick by `compare_flights.py`:

```
ardupilot/vehicle/build.sh        # both vehicles
sim/fly.sh                        # the six flights, sim/out/compare-*.csv, sim/RESULTS.md
BIN --params ... --bench < sim/out/lean-MISSION/inputs.txt   # tick time alone, sim/BENCH.md
```

`sim/fly.sh` runs, for `V` in `lean` and `ref` (binary `copter_lean`, `copter_ref`):

```
.venv/bin/python run_copter.py --backend bin --bin BIN --params params/copter-cf2x.txt --params params/copter-hover.txt --params params/copter-cf2x-tuned.txt --duration 10 --hold 99 --out out/V-hover
.venv/bin/python run_copter.py --backend bin --bin BIN --params params/copter-cf2x.txt --params params/copter-course-speed.txt --params params/copter-cf2x-tuned.txt --duration 60 --out out/V-course-1ms
.venv/bin/python run_copter.py --backend bin --bin BIN --params params/copter-cf2x.txt --params params/copter-cf2x-tuned.txt --duration 30 --out out/V-figure8
```

- hover: one waypoint 1 m above the origin (`copter-hover.txt`), 10 s;
- course-1ms: the figure-eight course of `copter-cf2x.txt` (eight waypoints, two diamonds of
  1.25 m half-diagonal meeting over the origin, from 0.8 m up to 1.6 m) at `WP_SPD 1`,
  `WP_ACC 1.5` (`copter-course-speed.txt`);
- figure8: the same course with ArduPilot's default `WP_SPD` (10 m/s) and `WP_ACC` (2.5 m/s²).

Every flight ends with `copter-cf2x-tuned.txt`, the gains tuned for the CF2X (attitude input
shaping and angle P, horizontal position and velocity gains, `WP_RADIUS_M 0.1`, `WP_JERK 5`);
`UNTUNED=1 sim/fly.sh` flies ArduPilot's default gains instead.

`compare_flights.py` compares the flown actuator lines and the simulator's state lines tick by
tick, replays each run's state lines through its own binary with `--exact --trace --bits` to get
the bit patterns of all 22 values of every tick (4 actuators, 18 trace numbers), and writes
`RESULTS.md` (per mission and binary: flight time, ticks, tracking error mean, rms and max, final
position error, waypoints passed and reached, and the per-tick comparison) and
`out/compare-<mission>.csv` (per tick: tick, time, the four actuators of each binary as bit patterns,
the vehicle's position from the simulator in each run, and each run's position target).

### Results

The two vehicles fly identically: on every tick of the three missions the actuators the simulator
received, the simulator's states, and all 22 values are bit-identical between `copter_lean` and
`copter_ref` (4000, 7797 and 6325 ticks with the tuned gains; first differing tick: none), and
`run_copter.py`'s own `--trace` replay check passes for all six runs. The numbers of each run
(identical for the two binaries; `RESULTS.md` has them per binary):

| mission | end | tracking error mean / rms / max | final position error | waypoints passed / reached |
|---|---|---|---|---|
| hover | time limit 10 s (4000 ticks) | 1.76 / 3.40 / 10.70 cm | 6.17 cm (NED 0.0000 -0.0001 -0.9383) | 1 of 1 / 1 of 1, first within 0.1 m at 1.857 s |
| course-1ms | last waypoint held 3 s within 0.1 m, 19.49 s (7797 ticks) | 1.71 / 2.30 / 8.70 cm | 2.97 cm (NED -0.0015 -0.0008 -0.8297) | 8 of 8 / 8 of 8, last waypoint first within 0.1 m at 16.490 s |
| figure8 | last waypoint held 3 s within 0.1 m, 15.81 s (6325 ticks) | 3.03 / 3.52 / 9.65 cm | 3.88 cm (NED -0.0063 -0.0053 -0.8379) | 8 of 8 / 8 of 8, last waypoint first within 0.1 m at 12.810 s |

The tracking error is the distance from the simulated vehicle to AC_PosControl's position target of
the same tick. With the tuned gains (`WP_RADIUS_M 0.1`, `WP_JERK 5`, the attitude and position gains
of `copter-cf2x-tuned.txt`) both courses end by the hold condition. With ArduPilot's default gains
(`UNTUNED=1`) they run to the time limit instead: AC_WPNav reports the last waypoint reached within
the default 2 m radius once its S-curve has finished, the mission completes, and `ModeAuto::loiter_start`
holds the stopping point of that moment, about 17 cm from the waypoint and outside the 0.1 m hold
sphere; the corners are flown as S-curve blends, so most inner waypoints are passed within 0.2 m but
not within 0.1 m (4000, 24000 and 12000 ticks, also bit-identical on every tick). The hover ends at
the time limit either way: once AC_WPNav reports the waypoint reached the mission completes and the
stopping point it then holds is 6.2 cm below the waypoint.
`run_copter.py --check-frames` passes all 12 of its checks (`out/copter-frames.txt`).

## Monte Carlo validation of the course contract

```
.venv/bin/python monitor.py --derive-spec          # spec/mission-course.json from out/lean-course-1ms
.venv/bin/python montecarlo.py                     # N = 200, both vehicles: out/montecarlo/
.venv/bin/python monitor.py RUN_DIR                # verdict and margins of one recorded flight
```

The contract is about the closed loop of the course-1ms flight (either vehicle, the CF2X, the
course of `params/copter-cf2x.txt` at 1 m/s with the tuned gains). Assumption A, on the state at
tick 0: level, any heading (yaw uniform in [-pi, pi), the attitude a rotation about the down axis),
at rest (the actuators held at tick 0 are the hover actuators), the position in the takeoff box, north and east in [-0.15, 0.15] m and down in [-0.3, 0] m (corners
0.212 m from the climb axis, inside the 0.25 m corridor). Guarantee ψ, over the 400 Hz ticks (the formula in STL
notation is in the docstring of `monitor.py`): safety on every tick of the horizon (altitude at most
2.0 m, and inside S, the union of the box and the corridor of radius 0.25 m around the path through
the takeoff point and w0..w7); the waypoints reached in order, each within r = 0.1 m and within its
allowance after the previous one (nested eventually operators, w0 counted from tick 0); and within
the sum of the allowances, within r of w7 for 3 s. The allowances come from the nominal flight's
"first within 0.1 m" times (`out/lean-course-1ms/summary.txt`) as ceil(1.25 leg + 0.5 s):
3, 3, 3, 3, 6, 3, 3, 3 s (the nominal legs are 1.685, 1.933, 1.845, 1.854, 3.621, 1.852, 1.85,
1.85 s), 27 s in all, so the horizon is K = 27 + 3 s = 12000 ticks. All numbers are in
`spec/mission-course.json`.

`monitor.py` evaluates ψ with STL's qualitative semantics over the ticks of a finite trace, the
ordered reach exactly by a backward pass over the ticks, and reports the margins: ceiling
clearance, the largest distance to S, the largest distance to the path after the first tick outside
the box and over the whole run, the first-reach time of each waypoint with its leg time and slack,
and the hold's best window. `montecarlo.py` draws the initial positions uniformly from the box
and then a heading uniformly from [-pi, pi) (`numpy.random.default_rng(20261105)`; the positions are
those of the same seed without headings, `--yaw0` sets every heading to 0), flies each with both vehicles for the whole horizon
(12001 ticks) in parallel worker processes (physical cores minus one, each with its own PyBullet
DIRECT environment, reset per flight, and its own controller process), checks the two vehicles'
actuators bit for bit on every tick, and writes `out/montecarlo/summary.csv`, `RESULTS.md` and per
run a compressed per-tick trace (t, position, yaw, actuators as float32 hex) and a one-line summary.
Its driver loop is `run_copter.fly`'s; its state lines and actuators equal `run_copter.py`'s for
the same start (checked on the nominal ground start, in-air starts and a start below the resting
altitude), without the recording, trace replay and plots.

Results (`out/montecarlo/RESULTS.md`): ψ holds on all 200 runs of each vehicle (14 of the 200
samples lie below the resting altitude and start on the ground), and the two vehicles' actuators are
bit-identical on every tick of every pair (0 differing ticks of 2 400 200). Margins, min / median /
max: ceiling clearance 40.81 cm on every run; largest distance to the path after leaving the box
7.70 / 8.71 / 18.62 cm (bound 25 cm; the smallest corridor margin, 6.38 cm, is sample 22 at
(-0.149, 0.114, -0.297), heading 64.4 deg, near a top corner); from the start 7.70 / 12.49 /
19.74 cm; leg slack at least 0.92 s (leg 1) and 1.31 s (leg 0); the hold's best window within
2.81 cm of w7 (bound 10 cm).

The heading barely matters: flown at heading 0 (`--yaw0`), the same 200 positions give the same
leg-0 slack distribution (1.31 / 1.43 / 1.63 s), each run's leg-0 time differs by at most one tick
(2.5 ms) from its run at the sampled heading and the other legs by at most two, and the corridor
margins agree to 0.01 mm. With `WP_YAW_BEHAVIOR 2` the vehicle turns toward the next waypoint while
it climbs, and the position controller works in the NED frame, so the yaw transient stays out of
the translation. A heading-0 start reproduces the runs made before headings were added byte for
byte (12 runs of `out/montecarlo` and 8 worst-case runs checked).

Worst cases (`montecarlo.py --worst-case --out out/montecarlo-worst-case`): the 8 corners of the box
(the 4 on the ground start resting there) and the 4 midpoints of its top edges, each at the headings
0, 90, 180 and -90 deg, and the 4 top corners also at 45 and -135 deg, 56 starts flown with both
vehicles: ψ holds on all 56, 0 differing ticks of 672 056. The smallest corridor margin, 3.79 cm,
is at the 4 top corners at every heading, where the vehicle leaves the box through its top 21.21 cm
from the climb axis; at the top-edge midpoints it is 10.00 cm. Settling on the contact moves a
ground start by a few micrometers: the ground corner (-0.15, 0.15) rests 3.6 um outside the box
(inside the corridor, so inside S), so its farthest distance after leaving the box is its start's.

A second uniform sample of 2000 starts flown with `copter_ref` only (`montecarlo.py --vehicles ref
--n 2000 --seed 20261106 --no-traces --out out/montecarlo-ref-2000`, 396 s): ψ holds on all 2000;
smallest corridor margin 4.57 cm (sample 113 at (0.148, -0.145, -0.293), heading 71.8 deg).

The box was 0.4 x 0.4 x 0.3 m before: its corners are 0.283 m from the climb axis, outside the
corridor, and flown from its top corners both vehicles left S by up to 1.92 cm on the climb; 2 of
2000 uniform starts failed that way. The 0.3 m box removes that.

With `--first-accel freefall` (`out/montecarlo-freefall/`, `copter_ref`, the same 200 samples), ψ
holds on 121 of 200 runs: every in-air start below 0.122 m sinks to the ground first and reaches w0
after 3.01 to 3.62 s, past its 3 s allowance.

Sensing noise (`montecarlo.py --noise L1..L4`, `out/montecarlo-noise-<level>/`, levels in the spec's
`sensing` entry, not part of the assumption): every tick the sample the controller receives is the
true state plus independent errors uniform in [-b, b] per component (position bp, velocity bv, body
rates bw, specific force bf; the attitude rotated by a small body-frame rotation with angles in
[-bq, bq], renormalized); the physics and the monitored positions use the true state, and the noise
of sample i comes from `default_rng([seed, 1, i])`, the same for both vehicles. With all bounds 0 the
runs equal the noise-free ones byte for byte. The same 200 starts and headings, both vehicles:

| level | bp, bv, bq, bw | ψ holds (Lean, C++) | differing ticks | smallest corridor margin | smallest leg slack | hold margin min / median |
|---|---|---|---|---|---|---|
| L1 | 5 mm, 2 cm/s, 0, 0 | 200, 200 | 0 | 5.36 cm | 0.91 s | 4.56 / 7.11 cm |
| L2 | 2 cm, 5 cm/s, 0, 0 | 200, 200 | 0 | 4.57 cm | 0.89 s | 0.37 / 5.49 cm |
| L3 | 2 cm, 5 cm/s, 0.5 deg, 0.01 rad/s | 199, 199 | 0 | 4.56 cm | 0.89 s | -0.46 / 5.45 cm |
| L4 | 5 cm, 10 cm/s, 1 deg, 0.02 rad/s | 120, 120 | 0 | 3.17 cm | 0.81 s | -9.00 / 0.76 cm |

Safety and the ordered reach hold on every run of every level; every failure is the reach and hold:
after the last waypoint the vehicle holds the stopping point computed from the noisy sample at
mission completion (`loiter_start`), which lands off w7, mostly vertically (10.4 cm for the one L3
failure, sample 43; up to 18.8 cm at L4), while the jitter around it stays under 1.1 cm.

The constants of the Lean sub-contracts (`contracts/Contracts/Mission/Sub.lean`) are checked on every
start of `out/montecarlo` and `out/montecarlo-worst-case` by `check_constants.py`
(`out/montecarlo/CONSTANTS.md`, `constants.csv`): each start flown again with `copter_ref` (equal
to the recorded run on every tick), its state lines replayed with `--exact --trace` for the position
target. δ, δ₀, ρ and δs hold on all 256 starts; the transfer property near the waypoints with
rPass = 0.105 m does not: on 82 of the 256 runs the vehicle leaves the 0.1 m ball around w0 (= w7)
on its way to w1 up to 10 ticks before the target leaves the 0.105 m ball (vehicle up to 11.47 cm
from w0, target at least 9.10 cm), all for in-air starts at 0.131 m or higher.

Time: the 400 flights (12 001 simulated seconds) take 143 to 153 s of wall clock (three runs) with 9 workers on the
10-core M4. In one process a 30 s flight takes 2.80 s (`copter_lean`) and 0.92 s (`copter_ref`) in
`montecarlo.py`, against 11.67 s and 2.33 s for `run_copter.py` with its trace replay and plots and
3.24 s and 1.27 s with `--no-plots --no-trace` (process start, environment construction and
`--print-params` per flight); the loop itself is unchanged at 0.090 and 0.028 s per simulated second.
Most of `copter_lean`'s time per tick is inside the binary: replayed in one batch, it takes 167 us
per line with `--exact` and 70 us without, against 16 us for `copter_ref` and the 10 us of its tick
alone (`BENCH.md`), so its decimal input parsing and exact decimal output take about 150 us per
tick, and the pipe itself little.


## The translated whole vehicle: scenario suite and live sessions (Phase 5d)

`fly_reference.py` flies a lock-step vehicle binary (default `build/reference/copter_ref`); `sim/lean_vehicle.py` puts the
translated whole vehicle (`lean/.lake/build/bin/vehicle_replay` in live mode) in that place (`--bin sim/lean_vehicle.py`).
README.md's "Phase 5c summary" and "Phase 5d summary" have the results.

### The scenario suite (`sim/scenarios.py`)

Six short sessions, recorded with the reference through `fly_reference.py --script NAME` (the scripted ground station of
`lockstep_gcs.py`; the scripts are `fly_reference.py`'s `SCENARIOS`), each booting from `build/reference/storage-cf2x.bin`
and waiting for EKF3 to use GPS (41.8 s on every session from this image) before its own part:

| name | what it does | simulated |
|---|---|---|
| loiter | GUIDED takeoff to 3 m, LOITER with roll, pitch, yaw and climb stick input, LAND, disarm | 71 s |
| brake | GUIDED toward a point 8 m north (SET_POSITION_TARGET_LOCAL_NED), BRAKE while moving, ALT_HOLD with sticks, LAND | 71 s |
| rtl | RTL_ALT_M 4 and RTL_LOIT_TIME 1 s set over MAVLink, GUIDED 12 m north (SET_POSITION_TARGET_GLOBAL_INT), RTL to landing | 80 s |
| guided | DO_REPOSITION (COMMAND_INT), CONDITION_YAW, DO_CHANGE_SPEED, a velocity target, NAV_LAND | 71 s |
| battery | BATT_FS_LOW_ACT 1 and BATT_LOW_TIMER 2 set, the battery reading dropped to 10.2 V in flight: battery failsafe, LAND | 67 s |
| prearm | arming refused at 3 s (`Arm: EKF attitude is bad`, `Arm: AHRS: not using configured AHRS type`), armed in STABILIZE after the origin is set and auto-disarmed, then GUIDED takeoff and the receiver silenced (FS_THR_ENABLE 3): radio failsafe, LAND | 66 s |

The scenario scripts change only what the ground station sends and two sensor-layer inputs, through the `GCS` object:
`gcs.rc` (the RC frame sent every 8th step, instead of the neutral one), `gcs.rc_off` (no RC frame: the receiver silent)
and `gcs.bat` (the battery's voltage and current).

```
python3 sim/scenarios.py --record          # the reference recordings (sim/out/scenario-NAME) and their --est traces (build/scenarios/NAME/est.txt)
python3 sim/scenarios.py                   # the whole-vehicle replay of each recording: one line per scenario
python3 sim/scenarios.py --live            # and one closed-loop flight per scenario with the translated vehicle (cmp of inputs.txt and outputs.txt)
```

### A live QGroundControl session with the translated vehicle

```
build/reference/venv/bin/python sim/run_qgc_reference.py --vehicle lean --seconds 120 --out sim/out/lockstep-qgc-lean
```

This is `run_qgc_reference.py`'s procedure (`fly_reference.py --udp`: the vehicle resting on the ground in
gym-pybullet-drones in real time, SERIAL0 bridged to UDP 127.0.0.1:14550; then the installed QGroundControl with console
logging; QGroundControl terminated first at the end, then the harness) with `--bin sim/lean_vehicle.py`. The session is
recorded (`OUT/harness/inputs.txt`, `outputs.txt`) and can be replayed afterwards through either vehicle. The translated
vehicle has to keep up with the 400 Hz real-time pace: a step slower than 2.5 ms delays the next ones (nothing is
dropped; the harness catches up), so a loaded machine shows up as a lag of the vehicle's clock against the wall clock, not
as a different session. Without QGroundControl, `--gcs scripted` runs `sim/udp_gcs_check.py` (pymavlink on the same port:
heartbeat, PARAM_REQUEST_LIST, the first PARAM_VALUEs) for `--seconds` and prints what it received.

## Gorge flight

The translated whole vehicle (`sim/lean_vehicle.py` over `lean/.lake/build/bin/vehicle_replay`) flown in leanfc's gorge
world (seed 7) on leanfc's gorge mission, on leanfc's X500 (Holybro X500 V2 model), and the flight rendered with the
gorge's cameras. The world, the plan, the X500 model, the wind and the renderers are leanfc's, imported from its checkout
(`LEANFC_ROOT`, default `/Users/ryan/Research/leanfc`); nothing is copied into this repository and nothing is written into
leanfc (no bytecode; its `Gorge` takes its build lock file and rebuilds its asset cache only if that is missing).

```
V=build/reference/venv/bin/python
# once: the X500's storage image (copter_ref, blank storage, the overrides of sim/params/reference-x500.txt)
$V sim/fly_reference.py --script image --params sim/params/reference-x500.txt --storage-out build/gorge-port/storage-x500.bin --out build/gorge-port/image-x500 --duration 60
# once: H.264 for the render (the versions of leanfc's sim/world/requirements-video.txt)
/opt/homebrew/bin/uv venv --python 3.12 build/gorge-video && /opt/homebrew/bin/uv pip install --python build/gorge-video/bin/python av==19.0.2 numpy==2.5.4
# the record flight, its whole-vehicle replay, the render
$V sim/gorge_lockstep.py --replay-check --ref-check --out sim/out/gorge-port-x500/flight
LEAN_NUM_THREADS=1 python3 ardupilot/vehicle/vehicle_replay.py sim/out/gorge-port-x500/flight --est sim/out/gorge-port-x500/flight/est.txt --out-dir build/gorge-port/vehicle_replay-x500
$V sim/render_gorge.py --run sim/out/gorge-port-x500/flight --out sim/out/gorge-port-x500
# options: --seed N (sensor noise of fly_reference.py), --wind MEAN GUST (leanfc's wind.Wind, X500 only),
#          --vehicle cf2x --params sim/params/gorge-port.txt (the CF2X, below)
```

`build/reference/venv` has pymavlink and the world's dependencies (numpy, scipy, Pillow, pybullet, gym-pybullet-drones,
matplotlib).

### The harness (`sim/gorge_lockstep.py`, harness code; its docstring has the details)

`fly_reference.py`'s lock step, sensor layer and ground station, in leanfc's `fly_gorge.GorgeAviary` (the gorge's collision
bodies in place of the ground plane):

- `--vehicle x500` (default): `run_leanfc.AIRFRAMES["x500"]["urdf"]` (leanfc `sim/assets/x500.urdf`: 2.0643 kg, inertia
  0.02167 / 0.02167 / 0.04 kg m^2, 8.54858 N per motor at 1000 rad/s, thrust-to-weight 1.6891, collision cylinder r 0.25 m)
  and `fly_gorge.LAG` (first-order motor lag 12.5 ms up, 25 ms down, starting at zero thrust), physics 1200 Hz, control
  400 Hz (three physics steps per vehicle line); placed as leanfc's `gorge_session.py` places it (base 5 mm above
  `gorge_plan.start_rest_z`) and settled on its contact. `--vehicle cf2x`: the package's CF2X, no lag.
- Output map: PWM 1000..2000 of ArduPilot's motor slots 0..3 (quad X: front right CCW, rear left CCW, front left CW, rear
  right CW, `PROTOCOL.md`) is the actuator a = (PWM - 1000) / 1000 of PX4's rotor_0..3, which are the same motors with the
  same spins (`x500.urdf`'s comment: rotor_0 front right ccw, rotor_1 rear left ccw, rotor_2 front left cw, rotor_3 rear
  right cw) and the URDF's propeller links 0, 2, 3, 1 (`run_copter.SLOT_TO_SIM = [0, 2, 3, 1]`); propeller speed
  MAX_RPM sqrt(a) (`run_copter.actuators_to_rpm`, as `run_leanfc.py`), so a motor's thrust is a x 8.54858 N, linear in a.
- Home of the sensor layer at the gorge's geographic origin (leanfc `params/ground.params`: 38.8405556, -105.0441667,
  4302 m; world ENU 0, 0, 0), with ArduPilot's earth field there; battery reading 16.0 V (4S) for the X500.
- The mission of `gorge_plan.plan_items` (NAV_TAKEOFF, 10 NAV_SPLINE_WAYPOINTs 3.5 m above the floor on the centerline,
  NAV_LAND) as MISSION_ITEM_INT with the plan's relative altitudes (for the CF2X re-referred to its rest height); the
  spline items' param4 `null` is sent as 0 (ArduPilot answers a NaN there with MAV_MISSION_INVALID_PARAM4). GUIDED, arm,
  NAV_TAKEOFF, AUTO, until the vehicle disarms.
- The record: every 4th step the true pose, the actuators, the clearance (PyBullet `getClosestPoints` from the vehicle's
  collision cylinder to every gorge body, up to 4 m, as leanfc's `gorge_session.py`) and the contacts (`track.csv`), and
  the numbers of `flight.json`. "In the air" is from the takeoff item's MISSION_ITEM_REACHED to the land item's
  MISSION_CURRENT (leanfc's `test_gorge_flight.py` uses the landed state IN_AIR, which is not streamed here); the route is
  the takeoff column and the chords between the spline waypoints, as there. `--ref-check` replays `inputs.txt` through
  `copter_ref` (output lines compared; `est.txt` for `vehicle_replay.py`).

### The X500's configuration (`sim/params/reference-x500.txt`, in the storage image)

Every parameter that differs from ArduPilot's code defaults, with its reason, is in that file: the vehicle configuration
of the CF2X image (frame, GPS and battery stand-ins, accelerometer offsets); the plant (`MOT_THST_EXPO 0`,
`MOT_SPIN_ARM 0`, `MOT_SPIN_MIN 0`, `MOT_SPIN_MAX 1`: thrust linear in the actuator from zero; `MOT_HOVER_LEARN 0`,
`MOT_THST_HOVER 0.3835`); the attitude gains of ArduPilot's `Tools/Frame_params/Holybro-X500v2-bdshot.param` (roll and
pitch unchanged; yaw changed, below; its notch, DShot, ESC-RPM and battery-scaling entries left out); `WP_SPD 2`.

The gorge is at 4302 m. ArduPilot sets the field elevation from the EKF origin and divides every motor demand by the
1976-atmosphere density ratio 0.6478 (`AP_Motors_Thrust_Linearization::get_compensation_gain`); the simulator's thrust
does not depend on altitude (leanfc's physics, unchanged). The configuration accounts for it in two places:
`MOT_THST_HOVER` is the throttle demand that hovers this plant there (1/1.6891 x 0.6478 = 0.3835, what hover learning
would converge to), and the yaw rate gains are the file's times 0.648. Yaw (flights `try1` to `try5`): with the file's yaw
values the yaw loop limit-cycled at 1.5 Hz, motors at 0 and 1, and the vehicle touched the terrain at N 31.7 m; the
model's yaw authority is small (momentConstant 0.016 m: 6.8 rad/s^2 per unit of yaw output, about 5.5 rad/s^2 in all at the
hover actuator 0.592), less than the file's `ATC_ACC_Y_MAX` (6.3 rad/s^2). Set: `ATC_ACC_Y_MAX 90`, `ATC_RAT_YAW_P/I/D`
0.78 / 0.078 / 0.0144, `ATC_RAT_YAW_FLTE 2.5` (default), `ATC_ANG_YAW_P 3`.

### Results (2026-11-13; deterministic for given options)

| flight (`sim/out/gorge-port-x500/`) | completed | MISSION_ITEM_REACHED | arm to disarm | clearance in the air | route distance max / rms | top speed | tilt max | contacts |
|---|---|---|---|---|---|---|---|---|
| `flight` (record) | yes | 1..11 | 57.0 s (vehicle texts 56.26 s) | 1.75 m (N 25.0 m) | 0.523 / 0.157 m | 2.05 m/s | 9.0 deg | 0 |
| `flight-noise-s1` (`--seed 1`) | yes | 1..11 | 57.0 s | 1.76 m | 0.556 / 0.196 m | 2.08 m/s | 8.9 deg | 0 |
| `flight-wind-4-1` (`--wind 4 1`) | yes | 1..11 | 56.0 s | 1.77 m | 0.504 / 0.151 m | 2.08 m/s | 11.7 deg | 0 |

Arm to disarm is between the ground station's armed and disarmed heartbeats (1 Hz); the vehicle's `Arming motors` and
`Disarming motors` texts are at 41.890 and 98.145 s. Record flight: liftoff 45.38 s, touchdown 95.51 s at 0.50 m/s,
0.04 m from the land item. Actuators in the air 0.370..0.809 (std per motor 0.039..0.043, no tick at 0 or 1); in cruise
(50 to 58 s) 0.571..0.601, std per motor 0.0026..0.0035; the larger excursions are the heading changes at the spline
transitions (`WP_YAW_BEHAVIOR` default: face the next waypoint), where the heading rings by up to about 2.6 deg.
Checks: the Lean replay of `inputs.txt` identical byte for byte (40,413 lines); `copter_ref` on the same lines identical;
`vehicle_replay.py`: PWM, downlink and tasks identical on 40,413 of 40,413 lines, storage 0 bytes differ,
`# unreached=[rejected AP_Param::convert_g2_objects, rejected AP_Param::convert_toplevel_objects, rejected AP_Notify::update]`
(defaults answered: `AP_InertialSensor::periodic`, `Compass::configured`), the same as on the recorded flight.
For reference, leanfc's own controller flew the plan arm to disarm in 51.5 s with 1.75 m least clearance.

Render (`sim/render_gorge.py`, adapter code; leanfc's world, scene renderer, X500 meshes and propeller blur, cameras on
`sensors.FORWARD`, exposure, thermal detector and AGC, fonts and H.264 encoder, imported): `gorge-port.mp4` (20 fps,
real speed, from 1 s before arming to 1 s after the disarm; chase view, under it the forward RGB and thermal cameras),
`gorge-port-{overview,chase,rgb,thermal}.png`, every 20th frame in `gorge-port-frames/`.

### The fast flight (`sim/out/gorge-port-x500-fast/`)

`$V sim/gorge_lockstep.py --params sim/params/gorge-fast-x500.txt --replay-check --out sim/out/gorge-port-x500-fast/flight`
(PARAM_SET of WP_SPD 7, WP_ACC 4.5, WP_JERK 6 on the X500 image), rendered with `sim/render_gorge.py --run
sim/out/gorge-port-x500-fast/flight --out sim/out/gorge-port-x500-fast`: completed, arm to disarm 34.0 s, the gorge from the
first to the last spline waypoint in 12.36 s (5.37 m/s mean, 7.04 m/s top), clearance 1.77 m, tilt 23.4 deg, actuators up to
0.970, no saturated tick; it also passes with `--seed 1` and `--wind 4 1`. The speed ladder (`ladder-*`, table by
`$V sim/gorge_stability.py RUN... --markdown`): WP_SPD 4 to 7 pass; WP_SPD 8 (WP_ACC 4.5 or 5) and 10 fail by thrust margin,
motor 1 at full thrust for about 50 ms in the bank reversal at N 26 m, and their top speed stays at 7.6 m/s (the legs of at
most 10 m with bends, under ArduPilot's largest WP_ACC of 5 m/s^2).

### The smooth flight (`sim/out/gorge-port-x500-smooth/`)

```
$V sim/gorge_lockstep.py --params sim/params/gorge-smooth-x500.txt --replay-check --out sim/out/gorge-port-x500-smooth/flight
$V sim/render_gorge.py --run sim/out/gorge-port-x500-smooth/flight --out sim/out/gorge-port-x500-smooth
$V sim/gorge_stability.py sim/out/gorge-port-x500/flight sim/out/gorge-port-x500-fast/flight sim/out/gorge-port-x500-smooth/flight --markdown --smooth
```

The fast flight looks jerky because it speeds up and brakes on almost every leg, not because a loop oscillates. In its
cruise the along-track acceleration (rms 1.40 m/s^2) is larger than the cornering acceleration (1.30 m/s^2), and the pitch
swings between -15 and +15 deg with 7 sign reversals. The mechanism is ArduPilot's spline speed planning
(`libraries/AP_Math/SplineCurve.cpp`, `calc_dt_speed_max` and `advance_target_along_track`). The target speed is capped
by the curvature, speed_max = sqrt(0.5 WP_ACC / curvature) (LATERAL_ACCEL_SCALER 0.5, the vertical part of the cornering
acceleration limited by 0.5 WP_ACC_Z, the climb and descent speeds by WP_SPD_UP/DN), and the speed moves toward that cap
at +-0.5 WP_ACC (TANGENTIAL_ACCEL_SCALER) with no jerk limit. On spline legs the position controller gets the target
position and velocity only, with zero acceleration feedforward. WP_ACC_CNR and PSC_NE_JERK act on S-curve legs and on
shaped inputs, not on spline legs (PSC_NE_JERK 2.5 moved the flight by at most 6 mm and changed no number of the tables below, `build/gorge-smooth/runs/g2-*`).
A spline leg leaves each waypoint along W[k+1] - W[k-1], a vector about two legs long (scaled down only when the two end
vectors together exceed 4 chords), so its parametric speed falls to about a quarter in the middle of the leg and the
leg's whole turn is packed there. A replica of `SplineCurve` (scratch, `build/gorge-smooth/spline_model.py`) on this plan
gives turning radii of 2.3 m in leg 5 (y 24.1 to 29.5 m) and 3.2 m in leg 8, an S of +13 to -10 deg of heading within
1.5 m. The gorge's centerline itself bends no tighter than 20.6 m. With WP_ACC 5 (@Range 0.5 to 5, the largest) and
WP_ACC_Z 3 the caps of the interior legs are 12.0, 4.1, 2.4, 5.2, 4.5, 2.8, 9.3, 2.2 m/s (legs 3 to 10); with the default
WP_ACC_Z 1 the rise of the floor caps leg 10 at about 1.3 m/s.

Tuning therefore keeps WP_SPD near the curvature caps and softens the attitude response to the S-kinks. The parameters,
applied on top of the X500 image like the fast flight's (`sim/params/gorge-smooth-x500.txt`, its comments give the
reasons):

| parameter | value (default / image) | why |
|---|---|---|
| WP_SPD | 4 m/s (image 2) | the fastest speed held within +-10 % on this route; at 4.5 and 5 the dips at legs 5, 8, 10 come back (4 to 5 pitch reversals) |
| WP_ACC | 5 m/s^2 (2.5) | the largest of its range: raises every curvature cap (lateral limit 0.5 WP_ACC = 2.5 m/s^2) |
| WP_ACC_Z | 3 m/s^2 (1) | without it the cruise dips to 2.46 m/s, band 47 %, 9 pitch reversals (`runs/i1-e3-noaccz`) |
| WP_JERK | 5 m/s^3 (1) | the track-progress scaler's time constant WP_ACC / WP_JERK becomes 1 s instead of 5 s: the lag after the start no longer leaves a slow speed recovery over legs 3 to 7 (`c1` to `c3` at WP_SPD 4: cruise band 14 % to 10 %, pitch reversals 5 to 2) |
| WP_YAW_BEHAVIOR | 3 (2) | face along the GPS course (the EKF velocity) instead of the heading of the spline target's velocity, which copies the S-kinks (yaw rate max 53 to 47 deg/s) |
| ATC_INPUT_TC | 0.15 s (0.10) | softer attitude input shaping |
| ATC_RATE_R_MAX, ATC_RATE_P_MAX | 45 deg/s (0, unlimited) | roll and pitch rate limits of the attitude command model; with them and ATC_INPUT_TC 0.15 (`c3` to the record) the roll rate peak at the leg-5 kink falls from 69 to 39 deg/s and the jerk peak from 13.0 to 6.7 m/s^3 |

The attitude gains, the yaw configuration and the plant are the reference configuration's, unchanged. Each value was
confirmed in the vehicle's parameter echo (`flight/log.txt`).

Results, cruise = the gorge segment without the acceleration from rest and the final braking (`sim/gorge_stability.py
--smooth`; the gorge segment there is MISSION_CURRENT 2..11 in AUTO):

| | 2 m/s (`gorge-port-x500/flight`) | fast (`gorge-port-x500-fast/flight`) | smooth (`gorge-port-x500-smooth/flight`) |
|---|---|---|---|
| gorge, first to last spline waypoint | 33.55 s, 1.96 m/s mean | 12.36 s, 5.37 m/s | 17.20 s, 3.84 m/s |
| arm to disarm | 57.0 s | 34.0 s | 41.0 s |
| cruise speed min / mean / max (band) | 1.79 / 1.98 / 2.05 m/s (13 %) | 4.34 / 5.99 / 7.04 m/s (45 %) | 3.49 / 3.92 / 4.17 m/s (17 %) |
| cruise acceleration rms / max (along-track / cornering rms) | 0.28 / 1.19 (0.09 / 0.27) m/s^2 | 1.91 / 4.21 (1.40 / 1.30) | 0.80 / 2.20 (0.31 / 0.74) |
| cruise jerk rms / max | 0.80 / 4.6 m/s^3 | 6.89 / 17.5 | 2.44 / 6.7 |
| cruise roll rate rms / max | 3.9 / 22 deg/s | 27.0 / 97 | 12.3 / 39 |
| cruise pitch rate rms / max | 2.7 / 21 deg/s | 28.9 / 54 | 7.5 / 33 |
| cruise yaw rate rms / max | 8.2 / 47 deg/s | 20.2 / 51 | 13.4 / 36 |
| cruise pitch min / max / rms (sign reversals, 3 deg hysteresis) | -3.8 / 2.2 / 0.6 deg (0) | -15.1 / 14.9 / 8.1 (7) | -5.7 / 3.8 / 1.8 (2) |
| clearance in the air, route distance max | 1.75 m, 0.52 m | 1.77 m, 0.56 m | 1.75 m (N 24.9 m), 0.49 m |
| tilt max, actuators, saturated ticks, contacts | 9.0 deg, 0.370..0.809, 0, 0 | 23.4 deg, up to 0.970, 0, 0 | 20.9 deg (the final braking), 0.369..0.809, 0, 0 |

The smooth flight's cruise minimum of 3.49 m/s is in leg 3, after the start; legs 4 to 10 stay between 3.73 and 4.17 m/s
(+-6 %), with three short dips of about 7 % (legs 5, 8 and 10, pitch to about -5 deg) at the curvature caps. Completed,
MISSION_ITEM_REACHED 1..11, touchdown 0.50 m/s, 0.09 m from the land item; the Lean replay of `inputs.txt` is identical
byte for byte (34,013 lines). `--seed 1` (`flight-noise-s1`): completed, clearance 1.88 m, cruise band 19 %, roll rate max
40 deg/s, jerk max 6.7 m/s^3, 0 saturated ticks. `--wind 4 1` (`flight-wind-4-1`): completed, clearance 1.81 m, band 12 %,
roll rate max 38 deg/s, jerk max 7.3 m/s^3, 0 saturated ticks.

The trade-off (cruise numbers; flights in `build/gorge-smooth/runs/`, scratch). All of them completed with clearance 1.74
to 1.77 m, no contact and no saturated tick:

| flight | settings | speed min / mean / max (band) | along-track acc rms | jerk rms / max | roll rate rms / max | pitch rms (reversals) |
|---|---|---|---|---|---|---|
| p-s3 | WP_SPD 3, WP_ACC 5, WP_ACC_Z 3 | 2.53 / 2.91 / 3.17 (22 %) | 0.22 | 1.71 / 8.6 | 8.1 / 42 | 1.3 (1) |
| p-s4 | WP_SPD 4, WP_ACC 5, WP_ACC_Z 3 | 3.44 / 3.82 / 4.00 (15 %) | 0.32 | 2.76 / 12.7 | 12.8 / 63 | 1.9 (7) |
| c3 | p-s4 + WP_JERK 5, WP_YAW_BEHAVIOR 3 | 3.68 / 3.96 / 4.06 (10 %) | 0.29 | 2.92 / 13.0 | 14.3 / 69 | 1.7 (2) |
| e1 | c3 at WP_SPD 4.5 | 3.97 / 4.44 / 4.56 (13 %) | 0.40 | 3.55 / 14.0 | 17.5 / 74 | 2.3 (4) |
| e2 | c3 at WP_SPD 5 | 4.39 / 4.92 / 5.07 (14 %) | 0.47 | 4.28 / 16.0 | 20.9 / 85 | 2.7 (4) |
| c2 | c3 + ATC_INPUT_TC 0.2, PSC_NE_VEL_FLTE 2 | 2.34 / 3.68 / 4.54 (60 %) | 1.11 | 3.10 / 6.2 | 9.6 / 25 | 6.4 (10) |
| d1 | c3 + ATC_INPUT_TC 0.2 | 3.44 / 3.93 / 4.15 (18 %) | 0.32 | 2.16 / 5.1 | 11.0 / 29 | 1.9 (4) |
| d3 | c3 + ATC_RATE_R/P/Y_MAX 30 | 3.66 / 3.96 / 4.21 (14 %) | 0.32 | 2.71 / 6.5 | 13.4 / 31 | 1.8 (6) |
| f3 | chosen at WP_SPD 3.5 | 3.26 / 3.48 / 3.63 (11 %) | 0.25 | 2.16 / 6.5 | 11.1 / 37 | 1.4 (2) |
| **e3 = record** | **the file** | 3.49 / 3.92 / 4.17 (17 %) | 0.31 | 2.44 / 6.7 | 12.3 / 39 | 1.8 (2) |
| g1 | chosen at WP_SPD 4.5 | 3.94 / 4.40 / 4.71 (18 %) | 0.42 | 2.92 / 7.1 | 14.3 / 39 | 2.5 (5) |

ATC_RATE_Y_MAX 30 on top of the file (`h1`) moved the flight by at most 3 cm and changed no number of the tables: the auto
yaw command is already limited by min(ATC_RATE_Y_MAX, ATC_RATE_WPY_MAX), and following the GPS course it seldom asks for
more than 30 deg/s. Raising WP_JERK to 10 (`h2`) adds reversals (5). Filtering the velocity loop (PSC_NE_VEL_FLTE 2 Hz,
`c2`) makes the speed oscillate; `d1`, with the same ATC_INPUT_TC 0.2 and no filter, keeps 18 %. What
limits a faster smooth flight on this route is the curvature caps of the spline legs between unequal waypoints: 2.4 m/s
at leg 5, 2.8 m/s at leg 8 and 2.2 m/s at leg 10 for WP_ACC 5. The 0.5 WP_ACC slew lets the vehicle carry 4 m/s through those short
kinks with dips of about 7 %. Above that, the dips and the pitch reversals return, and the bank rate in the kinks grows
with the cube of the speed. The thrust margin (actuators up to 0.81) is not the limit.

Re-spaced spline waypoints (`--spline-north`, off by default; scratch runs `r-*`, `g3-r35`). The same centerline
(Gorge.xc_fn, floor_c + 3.5 m) at north 16.29, 30.44, 43.71, 56.88, 72.0 m: 5 spline legs instead of 10, chosen with the
SplineCurve replica to maximize the smallest curvature cap (3.92 m/s for WP_ACC 5) with at least 1.75 m of PyBullet
clearance along the spline. Uniform spacing gives 3.0 to 3.75 m/s, and no spacing beat about 4.05 m/s. With c3's settings
it holds the speed steadier: WP_SPD 4 band 8 %, along-track rms 0.16 m/s^2, 0 pitch reversals; WP_SPD 4.5 band 10 %,
2 reversals; WP_SPD 3.5 band 7 %, roll rate max 37 deg/s. It is not faster: at WP_SPD 5 the dips return (17 %, 6
reversals). The bank reversal in its leg 4 (the centerline's S near N 37 m) still reaches 49 deg/s at 4 m/s, and the
attitude softening of the file makes it worse there (`f1`, WP_SPD 4.5: start overshoot to 5.18 m/s, band 28 %). Since the parameters alone
give a steady 4 m/s, no re-spaced flight is delivered; the option stays for further work.

Render (`sim/render_gorge.py`, unchanged except that the overview draws the flight's own waypoints, flight.json "path"):
`gorge-port.mp4` (861 frames, 41.03 to 84.03 s, 28.4 MB), `gorge-port-{overview,chase,rgb,thermal}.png`, every 20th frame
(1 s apart) in `gorge-port-frames/`. The forward RGB camera turns with the body, so pitch shows as the sky and the far end
of the gorge moving in the frame. In the fast render's cruise (frames 220 to 400, 52 to 61 s) the view swings from nose
down, ground only (52 and 56 s, pitch +12 and +13 deg in `track.csv`), to nose up, sky in view (54 and 55 s, -3 and -7
deg), every one to two seconds. In the smooth render's cruise (frames 280 to 560, 55 to 69 s) the pitch at every saved
frame is within +-3 deg. The view tilts only where the vehicle banks: 60 s (leg 5 kink, roll -13 deg) and 66 s (leg 8,
roll +10 deg). The saved frames are 1 s apart, about the fast flight's pitch period, so they sample its pitching and do
not resolve it.

### The S-curve flight (`sim/out/gorge-port-x500-scurve/`)

```
$V sim/gorge_lockstep.py --straight-north 26.34,47.3,72.0 --params sim/params/gorge-scurve-x500.txt --replay-check --out sim/out/gorge-port-x500-scurve/flight
$V sim/render_gorge.py --run sim/out/gorge-port-x500-scurve/flight --out sim/out/gorge-port-x500-scurve
$V sim/gorge_stability.py sim/out/gorge-port-x500/flight sim/out/gorge-port-x500-fast/flight sim/out/gorge-port-x500-smooth/flight sim/out/gorge-port-x500-scurve/flight --markdown --smooth
```

The smooth flight is limited by the spline legs' own 2 to 3 m kinks, not by the gorge or the thrust. This flight uses
ArduPilot's other leg type on the same gorge. `--straight-north` (off by default; with the option off, a flight of the smooth
flight's parameters gives `inputs.txt`, `outputs.txt`, `track.csv` and `mission.json` identical byte for byte to
`gorge-port-x500-smooth/flight`) sends the route as MAV_CMD_NAV_WAYPOINT items at points of leanfc's centerline, with the
same takeoff and the same NAV_LAND at the last waypoint. The translated vehicle flies them; every waypoint was reached and
blended.

Mechanism (`libraries/AP_Math/SCurve.cpp`, `libraries/AC_WPNav/AC_WPNav.cpp`, `ArduCopter/mode_auto.cpp` at 802db19de1).
- **Leg profile.** A straight leg is an S-curve to WP_SPD with the position, velocity and acceleration targets all fed
  forward. Its jerk is min(WP_JERK, ATC_RATE_R/P_MAX x g) and its snap J pi / (4 max(ATC_INPUT_TC, 0.1)).
- **Fast waypoints.** A NAV_WAYPOINT with hold time 0 followed by a NAV_WAYPOINT or NAV_LAND is a fast waypoint
  (`set_next_wp`).
- **Corner blending.** The next leg's S-curve is started while this one decelerates (`advance_target_along_track`), once
  this leg's remaining time is within the next leg's acceleration time. Conditions at the turn midpoint: within
  WP_RADIUS_M of the waypoint, a speed below both legs', a horizontal acceleration below WP_ACC_CNR (default 2 WP_ACC), and
  a vertical acceleration below WP_ACC_Z.
- **What the corner costs.** The two profiles add up. A corner of angle t is passed at about WP_SPD cos(t/2) with a
  cornering acceleration of about 2 WP_ACC sin(t/2), whatever the speed, and with jerk bounded by WP_JERK. WP_ACC_CNR acts
  only in that check and on arc legs; PSC_NE_JERK does not shape these targets.
- **Leg length.** Each leg must hold its own acceleration and deceleration, about WP_SPD^2 / WP_ACC + WP_SPD WP_ACC /
  WP_JERK. Long legs are needed, and straight chords cut the gorge's bends.
- **Choosing the waypoints.** An approximate model of the S-curves and their blending (scratch, `build/gorge-smooth/
  scurve_model.py`) with the offline PyBullet clearance of the modeled path chose them: three legs (26.6, 21.7, 24.8 m;
  turns of 23 and 20 deg) at north 26.34, 47.3, 72.0 m gave 1.97 m. Four legs gave 1.78 m, five 1.79 m.
- **Speed.** The 21.7 m middle leg sets the reachable speed.

`sim/params/gorge-scurve-x500.txt` (on top of the X500 image, nothing else changed):

| parameter | value (default / image) | why |
|---|---|---|
| WP_SPD | 9 m/s (10 / 2) | above what the middle leg reaches (about 8.5 m/s), so every leg runs its full acceleration profile; the last leg reaches 9.1 m/s before braking |
| WP_ACC | 5 m/s^2 (2.5) | the largest of its range: the reachable speed on the 21.7 m leg; start and stop at about 27 deg tilt; corners 2 x 5 x sin(t/2), about 2 m/s^2 at these two |
| WP_JERK | 8 m/s^3 (1) | the S-curves' jerk; with 1 every acceleration phase takes 5 s; the onset of the final braking pitches at about WP_JERK / g (52 deg/s here); 20 swings the pitch within a leg (`s6`) |

Results (cruise as before). The gorge is from the takeoff point at rest (MISSION_CURRENT 2) to the arrival at the last
waypoint, the same two points for all four flights:

| | 2 m/s | fast | smooth spline | S-curve (`gorge-port-x500-scurve/flight`) |
|---|---|---|---|---|
| route | 10 spline legs | 10 spline legs | 10 spline legs | 3 straight legs |
| gorge, takeoff point to last waypoint | 39.2 s | 16.0 s | 20.7 s | 11.7 s |
| arm to disarm | 57.0 s | 34.0 s | 41.0 s | 29.0 s |
| cruise speed min / mean / max (band) | 1.79 / 1.98 / 2.05 m/s (13 %) | 4.34 / 5.99 / 7.04 (45 %) | 3.49 / 3.92 / 4.17 (17 %) | 8.53 / 8.71 / 9.09 (6 %) |
| cruise acceleration rms / max (along / cross rms) | 0.28 / 1.19 (0.09 / 0.27) m/s^2 | 1.91 / 4.21 (1.40 / 1.30) | 0.80 / 2.20 (0.31 / 0.74) | 1.10 / 2.80 (0.57 / 0.94) |
| cruise jerk rms / max | 0.80 / 4.6 m/s^3 | 6.89 / 17.5 | 2.44 / 6.7 | 2.90 / 9.5 |
| cruise roll rate rms / max | 3.9 / 22 deg/s | 27.0 / 97 | 12.3 / 39 | 9.6 / 19 |
| cruise pitch rate rms / max | 2.7 / 21 deg/s | 28.9 / 54 | 7.5 / 33 | 14.0 / 52 |
| cruise pitch rate max before the final braking | 16 deg/s | 54 | 23 | 23 |
| cruise yaw rate rms / max | 8.2 / 47 deg/s | 20.2 / 51 | 13.4 / 36 | 9.6 / 15 |
| cruise pitch min / max / rms (reversals) | -3.8 / 2.2 / 0.6 deg (0) | -15.1 / 14.9 / 8.1 (7) | -5.7 / 3.8 / 1.8 (2) | -16.4 / 5.8 / 3.4 (1) |
| gorge pitch min / max (start, stop) | -9.0 / 6.8 deg | -18.2 / 14.9 | -20.9 / 11.4 | -28.9 / 22.9 |
| clearance in the air | 1.75 m | 1.77 m | 1.75 m | 1.93 m (N 69.6 m) |
| distance from the original route (plan's chords), max / rms | 0.52 / 0.16 m | 0.56 / 0.20 | 0.49 / 0.18 | 1.51 / 0.62 (horizontal 1.48 at N 29.3 m) |
| actuators, saturated ticks, contacts | 0.370..0.809, 0, 0 | 0.246..0.970, 0, 0 | 0.369..0.809, 0, 0 | 0.441..0.868, 0, 0 |

The cruise window ends when the speed falls below 0.95 WP_SPD, so it holds the onset of the final braking. The S-curve
flight's pitch rate of 52 deg/s and pitch of -16 deg are there; before its top speed (57.31 s) they are at most 23 deg/s
and -1.1 to +5.8 deg. The speed rises gently through the cruise, 8.48 to 8.75 m/s in the middle leg and 9.09 m/s in the
last, because a blended corner adds the next leg's acceleration to an unfinished deceleration. The start and the stop
are single jerk-limited pitches of +23 and -29 deg. Completed (MISSION_ITEM_REACHED 1..4), touchdown 0.50 m/s, 0.17 m from
the land item. The Lean replay of `inputs.txt` is identical byte for byte (29,213 lines). `--seed 1`: completed,
clearance 2.06 m, band 6 %, roll rate max 20 deg/s, jerk max 9.4 m/s^3, 0 saturated ticks. `--wind 4 1`: completed,
clearance 2.00 m, band 5 %, roll max 19 deg/s, jerk max 9.7 m/s^3, 0 saturated ticks. The distance from the original
route is 1.51 / 1.58 / 1.54 m at most (N 29.3 m, the chord of the first leg across the bend).

Trade-off (cruise; scratch runs in `build/gorge-smooth/runs/`). All completed with no contact and no saturated tick.
"Pitch rate max" is over the cruise, then before the final braking:

| flight | legs | WP_SPD / WP_ACC / WP_JERK | speed min / mean / max (band) | roll rate rms / max | jerk rms / max | pitch rate max | tilt max | clearance |
|---|---|---|---|---|---|---|---|---|
| s3 | 5 | 6 / 5 / 10 | 5.70 / 5.99 / 6.06 (6 %) | 12.5 / 33 | 2.63 / 11.5 | 66 | 29.6 | 1.86 |
| s2 | 5 | 7 / 5 / 10 | 6.61 / 6.86 / 7.11 (7 %) | 12.7 / 31 | 2.88 / 11.6 | 66 | 29.5 | 1.89 |
| s1 | 4 | 8 / 5 / 10 | 7.60 / 7.84 / 8.22 (8 %) | 10.3 / 21 | 2.74 / 11.3 | 65 | 29.2 | 1.75 |
| s5 | 4 | 7 / 4 / 6 | 6.65 / 6.86 / 7.14 (7 %) | 6.7 / 13 | 1.78 / 7.3 | 42 | 26.1 | 1.75 |
| s6 | 4 | 9 / 5 / 20 | pitch -12.7 to +14.9 deg within leg 4: rejected | 16.5 / 29 | 8.11 / 10.8 | 62 | 29.2 | 1.74 |
| t3 | 3 | 7 / 3 / 5 | 6.65 / 6.83 / 7.02 (5 %) | 5.4 / 14 | 1.56 / 6.1 | 35 | 20.1 | 1.97 |
| t1 | 3 | 8 / 4 / 6 | 7.60 / 7.83 / 8.03 (5 %) | 7.0 / 15 | 2.02 / 7.3 | 41 / 13 | 26.0 | 1.94 |
| u1 | 3 | 8.5 / 4.5 / 7 | 8.08 / 8.28 / 8.55 (6 %) | 8.2 / 17 | 2.44 / 8.4 | 47 / 17 | 28.5 | 1.94 |
| **v1 = record** | 3 | 9 / 5 / 8 | 8.53 / 8.71 / 9.09 (6 %) | 9.6 / 19 | 2.90 / 9.5 | 52 / 23 | 29.1 | 1.93 |
| t2 | 3 | 9 / 4 / 6 | the middle leg cannot reach it: accelerates and brakes in the last leg (cruise 0.9 s) | 7.5 / 13 | 4.46 / 6.9 | 39 | 26.3 | 1.94 |
| x1 (spline route, outside the documented range) | 10 spline | 6 / **10** / 5, WP_ACC_Z 3, WP_YAW_BEHAVIOR 3 | 5.40 / 5.86 / 6.03 (11 %) | 23.4 / 64 | 5.38 / 13.6 | 72 | 29.8 | 1.75 |

- **Limit.** The faster flights pay at the start and the stop, not in the cruise. The reachable speed on a leg of length
  L grows like (WP_JERK L^2 / 4)^(1/3) with WP_ACC at its 5 m/s^2 maximum. The pitch rate at the onset of braking grows
  with WP_JERK. Longer legs cut the bends further. Three legs already put the track 1.5 m off the original route, at
  1.93 m clearance.
- **Gentler variants.** t1 (8 m/s) and t3 (7 m/s) cruise as smoothly, with start and stop at 26 and 20 deg.
- **Raising WP_ACC on the spline route** above its range (x1, WP_ACC 10) raises the curvature caps. The vehicle then takes
  the same 2 to 3 m kinks harder (roll rate 64 deg/s in cruise, 91 in the segment), so that alone gives no fast smooth
  flight.

Render (`sim/render_gorge.py`; the overview now names the leg type): `gorge-port.mp4` (621 frames, 41.03 to 72.03 s,
19.7 MB), `gorge-port-{overview,chase,rgb,thermal}.png`, every 20th frame in `gorge-port-frames/`.
- **Overview.** One wide, smooth curve through the gorge, passing about 1.5 m inside waypoints 1 and 2 (the blended
  corners).
- **Forward RGB, cruise (53 to 57 s).** The view stays steady and the sky band does not jump between frames: pitch -1 to
  +6 deg (`track.csv`; +6 at 53 s and +5 at 57 s while the speed still rises toward 9 m/s), roll -12 to +6 deg in the two
  corners.
- **Final braking (58 to 59 s).** A single nose-up, with the gorge's end and the sky filling the view (pitch -25 deg at
  58 s, -24 at 59 s), then the descent to land.
- **Compared with the fast render.** Its view swings between ground only and sky every one to two seconds in the cruise.

### Formation flight (`sim/out/gorge-formation-x500/`)

Two X500s in the gorge at the same time, each flown by its own instance of the translated whole vehicle, on leanfc's two
formation plans (`sim/world/formation_plan.py`, imported): `abreast` (side by side, 1.8 m apart, both noses along the
direction of travel) and `staggered` (vehicle 2 2.2 m to the right of and 1.8 m behind vehicle 1, centre distance 2.84 m;
vehicle 2 flies with its nose against the direction of travel, so its camera looks behind the formation, as in leanfc's
plan). Vehicle 2's route is vehicle 1's plus a
constant offset; the plan also moves the first point to a level start site and gives each vehicle a level land site on
the continuation of its last leg.

```
V=build/reference/venv/bin/python
for F in abreast staggered; do
  $V sim/gorge_formation_lockstep.py --plan $F --replay-check --ref-check --out sim/out/gorge-formation-x500/$F/flight
  for K in v1 v2; do
    LEAN_NUM_THREADS=1 python3 ardupilot/vehicle/vehicle_replay.py sim/out/gorge-formation-x500/$F/flight/$K \
      --est sim/out/gorge-formation-x500/$F/flight/$K/est.txt --out-dir build/gorge-formation/vehicle_replay-$F-$K
  done
  $V sim/render_gorge_formation.py --run sim/out/gorge-formation-x500/$F/flight --out sim/out/gorge-formation-x500/$F
done
# noise: --seed N (vehicle 1 seed N, vehicle 2 seed N + 100), --out .../$F/flight-noise-sN
# staggered with both noses forward (the earlier flight): --plan staggered --noses-forward --out .../staggered/flight-noses-forward
```

The harness (`sim/gorge_formation_lockstep.py`, harness code; its docstring has the details) imports
`sim/gorge_lockstep.py` for everything per vehicle (sensor layer, PWM map, ground-station script, record, metrics) and
leanfc's `formation.FormationAviary` for the world: one gym-pybullet-drones world (1200 Hz, the gorge's collision
bodies) with both X500s and the motor lag kept per vehicle; no wind; no aerodynamic interaction between the vehicles.
Two `sim/lean_vehicle.py` processes, each with its own copy of the boot image (`OUT/vN/storage_in.bin`, from
`build/gorge-port/storage-x500.bin`: the configuration of `sim/params/reference-x500.txt`, WP_SPD 2, no PARAM_SET), its
own `LEAN_VEHICLE_OUT` (`OUT/vN/lean`, and `OUT/vN/lean-replay` for the replay check), timing file and record
(`OUT/vN/inputs.txt`, `outputs.txt`); the translated vehicle writes only its output, task and storage files there, so the
two instances share no file. Each has its own scripted ground station seeing only its own vehicle (upload, GUIDED, arm,
takeoff, AUTO, wait for the disarm); nothing links the vehicles besides the common world tick. Missions: the plan's
items translated as for the single route (NAV_TAKEOFF, 10 NAV_SPLINE_WAYPOINTs with param4 0, NAV_LAND at the vehicle's
land site; relative altitudes about each vehicle's rest height, equal takeoff climbs). Heading: ArduCopter's
`WP_YAW_BEHAVIOR` default (face the next waypoint) for both vehicles of `abreast` and vehicle 1 of `staggered`.

The reversed rear vehicle (`staggered` vehicle 2; the plan's `reverse` flag, `--noses-forward` turns it off; leanfc did
this with its own `nav.yawReverse`, which ArduCopter has no counterpart for) uses ArduPilot's own mechanisms only (pinned
source `ArduCopter/mode_auto.cpp`, `autoyaw.cpp`, `libraries/AP_Mission/AP_Mission.cpp`): its ground station sets
`WP_YAW_BEHAVIOR 0` (NONE; PARAM_SET after the parameter download), and its mission has a `MAV_CMD_CONDITION_YAW` before
each spline waypoint (absolute heading = that leg's chord direction + 180 deg, 10 deg/s, shortest way; frame
MAV_FRAME_MISSION): 23 items instead of 13. `do_yaw` puts the auto-yaw in FIXED; `sl_start` and `wp_start` reset the yaw
mode to the default at every waypoint unless it is ROI or FIXED with `WP_YAW_BEHAVIOR` NONE, so with NONE the FIXED
heading carries across the spline legs (the default yaw mode for NONE is HOLD, used for the takeoff and landing, which
`takeoff_start` and `land_start` set to HOLD anyway). AP_Mission starts the do and condition commands that follow a nav command
when that nav command completes, so the item placed after waypoint k - 1 (after the takeoff for leg 1) turns the nose on
leg k; a first flight with the items after the waypoints (`build/gorge-formation/stag-rev-try1`) turned one leg late
(deviation from backward up to 30.3 deg, rms 10.8). The vehicle starts on the floor already facing backward (harness
side: placed at leg 1's heading + 180 = 189.3 deg; leanfc's formation.py placed both vehicles nose north and let its
controller turn), so the takeoff needs no turn. Both kinds of item are handled by the translated vehicle as by
`copter_ref`: every CONDITION_YAW is reached (MISSION_ITEM_REACHED for all 21 items), and the checks below are identical. Per
vehicle `OUT/vN/` has the files of a single-vehicle flight (`track.csv`'s `contacts` counts vehicle-terrain contacts
only); `OUT/formation.csv` (100 Hz: centre distance, closest distance of the two collision cylinders, contacts
vehicle-vehicle and vehicle-terrain, both clearances) and `OUT/formation.json` (the pair's numbers) are the pair's.

Results (2026-11-13; deterministic for given options: the record flights flown twice gave the same `outputs.txt`).
Clearance and route distance "in the air" as for the single vehicle (takeoff item reached to land item started);
separation is the distance between the two vehicle centres; "both airborne" is from the later liftoff to the earlier
touchdown; actuators and saturated ticks (some motor at <= 0.001 or >= 0.999) over every 400 Hz tick from liftoff to
touchdown.

| flight (`sim/out/gorge-formation-x500/`) | arm to disarm v1 / v2 | separation min, whole flight | separation min, both airborne | separation on the routes min / mean / max | clearance v1 / v2 | route start v2 - v1 | actuators max v1 / v2 | saturated ticks |
|---|---|---|---|---|---|---|---|---|
| `abreast/flight` | 58.765 / 58.755 s | 1.763 m (86.76 s) | 1.763 m | 1.763 / 1.800 / 1.808 m | 1.544 m (N 24.9) / 1.952 m (N 58.8) | +0.005 s | 0.812 / 0.812 | 0 / 0 |
| `abreast/flight-noise-s1` | 58.947 / 58.737 s | 1.691 m | 1.691 m | 1.691 / 1.834 / 1.971 m | 1.532 / 1.923 m | -0.032 s | 0.813 / 0.818 | 0 / 0 |
| `staggered/flight` (vehicle 2 reversed) | 59.175 / 59.065 s | 2.842 m (at rest) | 2.865 m (45.77 s) | 2.887 / 3.656 / 3.948 m (planned 2.84) | 1.487 m (N 24.9) / 1.994 m (N 49.1) | +0.57 s | 0.811 / 0.689 | 0 / 0 |
| `staggered/flight-noise-s1` (vehicle 2 reversed) | 59.257 / 58.780 s | 2.842 m (at rest) | 2.857 m | 2.972 / 3.382 / 3.674 m | 1.446 / 1.955 m | +0.30 s | 0.809 / 0.690 | 0 / 0 |
| `staggered/flight-noses-forward` | 59.175 / 58.910 s | 2.814 m (48.75 s) | 2.814 m | 2.818 / 3.360 / 3.578 m | 1.487 m (N 24.9) / 1.994 m (N 49.1) | +0.37 s | 0.811 / 0.811 | 0 / 0 |
| `staggered/flight-noses-forward-noise-s1` | 59.257 / 58.822 s | 2.803 m | 2.803 m | 2.918 / 3.409 / 3.720 m | 1.446 / 1.957 m | +0.325 s | 0.809 / 0.814 | 0 / 0 |

Every flight: both vehicles completed (MISSION_ITEM_REACHED 1 to 11 each).

Every flight in the table: no vehicle-terrain contact between liftoff and touchdown, no vehicle-vehicle contact at any
time (closest distance between the collision cylinders in the air 1.26 m abreast, 2.31 m staggered with both noses
forward, 2.36 m with vehicle 2 reversed), no saturated tick (also none in the landings), touchdown at 0.50 to 0.52 m/s,
0.01 to 0.03 m from the land site, slide after touchdown at most 0.065 m (abreast vehicle 1). Heading on the route
(takeoff item reached to land item started, ground speed above 0.5 m/s): every forward-flying vehicle within 6.1 deg
of the direction of travel (rms 1.6 to 2.2 deg); the reversed vehicle 2 within 14.8 deg of exactly backward (p95
11.0, rms 4.4 deg; noise flight 15.8 / 10.6 / 4.5 deg): the nose holds each leg's chord heading while the spline
track curves, the largest deviations at the bends. With the nose fixed instead of swinging at every waypoint its
actuators stay within 0.499..0.689 (0.370..0.811 nose forward). Vehicle 1 of `staggered` flies the same record whether
vehicle 2 is reversed or not (identical numbers: the vehicles meet only through contact). Abreast: the two vehicles arm
on the same step and start their routes 5 ms apart; the separation on the route stays 1.763 to 1.808 m (mean 1.800 m; the
least at 86.76 s, at the turn onto the last spline waypoint), at most 2.06 m during the landing (the land sites are 2.05
m apart). Staggered: vehicle 2's EKF3 reports "using GPS" 0.22 s after vehicle 1's (the two rest on different ground;
GPS at 5 Hz), so with both noses forward it arms 0.21 s later and starts its route 0.37 s later; at 2 m/s that adds
about 0.7 m along track to the planned 1.8 m, and the separation on the route is 2.82 to 3.58 m, mean 3.36 m (planned
2.84 m), least (2.81 m) at 48.75 s, as vehicle 1 leaves the takeoff column while vehicle 2 is still climbing. With
vehicle 2 reversed its longer mission upload (23 items) arms it 0.26 s after vehicle 1, and its ground station's
check of the takeoff height (GLOBAL_POSITION_INT at 4 Hz) switches it to AUTO 0.25 s later than with 13 items, so its
route starts 0.57 s after vehicle 1's (harness timing, not the vehicle) and the separation on the route is 2.89 to
3.95 m, mean 3.66 m; in the air it is least at liftoff (2.865 m). Vehicle 1's least
clearance is at N 24.9 m (the same narrows as the single flight's 1.75 m), lower here because the plan puts it 0.9 to
1.1 m left of the centre line: 1.544 m abreast, 1.487 m staggered (leanfc's plan study gives a nominal 1.57 m abreast).
Checks, per vehicle of each record flight (abreast, staggered reversed, staggered noses forward): the Lean replay of
`inputs.txt` identical byte for byte (41,213 lines abreast, 41,613 staggered), `copter_ref` on the same lines identical; `vehicle_replay.py`: PWM, downlink and tasks identical on
every line, storage 0 bytes differ, the same `# unreached=[...]` as the single-vehicle flight. The noise flights pass the
Lean replay check too.

Render (`sim/render_gorge_formation.py`, adapter code; leanfc's `render_formation.render_sharded` imported, 2 workers,
mp4 only through `build/gorge-video`): per formation `formation-$F.mp4` (20 fps; abreast 1200 frames, 31.1 MB, 663 s to
render; staggered 1240 frames, 31.2 MB, 765 s; vehicle 2 reversed), stills `formation-$F-{N12,N25,N45,N65,landing}.png`, a top-down
`formation-$F-overview.png` with both tracks, the least-clearance points and the land sites (`--overview-only` renders
just that), every 20th frame in `formation-$F-frames/`, and `formation-$F-render.json`. The chase view labels the
vehicles V1 and V2 (staggered: "V2 (rear, flying backward)", render_formation's label for a reversed vehicle) and shows
the separation; below it are each vehicle's mode, mission item and clearance and its forward
RGB and thermal panels (staggered: V2's "rear-view" panels, its forward camera looking back along the
route). The render of the staggered flight with both noses forward was replaced by the reversed one.

### The CF2X (`--vehicle cf2x`, earlier flight)

`sim/out/gorge-port/flight`: `$V sim/gorge_lockstep.py --vehicle cf2x --params sim/params/gorge-port.txt --replay-check
--ref-check --out sim/out/gorge-port/flight` (boot image `build/reference/storage-cf2x.bin`; `gorge-port.txt` sends the
CF2X rate gains with PARAM_SET: with the image's gains its rate loops limit-cycle, roll and pitch at 23 Hz, yaw at 5 Hz, as
in `sim/out/lockstep-flight`). Completed: 1..11 reached, 57.0 s, clearance 2.02 m, route 0.475 / 0.143 m, 2.08 m/s,
no contacts; with `--seed 1` (`flight-noise-s1`) completed, clearance 1.99 m. Rendered as `sim/out/gorge-port/gorge-port.mp4`
and stills (`$V sim/render_gorge.py --run sim/out/gorge-port/flight --out sim/out/gorge-port`).
