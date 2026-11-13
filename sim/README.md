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
