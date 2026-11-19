# Monte Carlo validation of the course contract

Closed loop: each vehicle (`copter_lean`, the Lean translations; `copter_ref`, ArduPilot's classes compiled unmodified) in lock step with the CF2X in gym-pybullet-drones (PYB physics at 1200 Hz, control at 400 Hz, gravity 9.80665 m/s², no damping), flying the figure-eight course of `sim/params/copter-cf2x.txt` at 1 m/s with the tuned gains (`copter-cf2x.txt`, `copter-course-speed.txt`, `copter-cf2x-tuned.txt`, `--exact`), the parameters of `sim/fly.sh`'s course-1ms flight. Spec: `sim/spec/mission-course.json`; monitor: `sim/monitor.py` (the formula in STL notation is in its docstring); runner: `sim/montecarlo.py`.

## The contract

- Assumption A, on the state at tick 0: level (roll and pitch 0), any heading (the attitude a rotation about the down axis), at rest (zero velocity and body rates, the hover actuators held), position in the box north [-0.15, 0.15], east [-0.15, 0.15], down [-0.3, 0.0] m (NED from the takeoff point).
- Safety, every tick 0..K: altitude at most 2.0 m, and distance 0 to S, the union of the box and the corridor of radius 0.25 m around the path (the takeoff point, then w0..w7).
- Ordered reach: nested eventually operators, waypoint i within r = 0.1 m within its allowance T_i after waypoint i-1 is reached (w0 from tick 0). Allowances T0 = 3 s, T1 = 3 s, T2 = 3 s, T3 = 3 s, T4 = 6 s, T5 = 3 s, T6 = 3 s, T7 = 3 s (rule: allowance_i = ceil(1.25 * leg_i + 0.5) s, leg_i from the nominal first-within times (leg_0 from t = 0); nominal legs 1.685, 1.933, 1.845, 1.854, 3.621, 1.852, 1.85, 1.85 s from `sim/out/lean-course-1ms`).
- Reach and hold: within T = 27 s, within r of w7 and staying within r for H = 3 s.
- Horizon K = T + H = 12000 ticks (30 s); every flight is simulated for ticks 0..K unless it crashes.

## Samples

N = 200 initial positions, uniform in the box, `numpy.random.default_rng(20261105).uniform(lo, hi, size=(N, 3))` with lo, hi the box corners (north, east, down), and then the headings from the same generator, `.uniform(-pi, pi, size=N)` (radians, from north, clockwise seen from above); each flown with `copter_lean` and `copter_ref` (400 flights). 14 of them lie below the vehicle's resting altitude (0.0135 m), where its collision cylinder would overlap the ground plane; those start resting on the ground at the sampled north and east (settled as the nominal flight; the realized position is in summary.csv), the other 186 start in the air at the sampled position. Tick-0 specific force of an in-air start: (0, 0, -g), the reading of a vehicle held at rest by its hover thrust, as the controllers' takeover assumes (`--first-accel hover`).

## Verdicts

| vehicle | runs | ψ holds | safety | ordered reach | reach and hold |
|---|---|---|---|---|---|
| `copter_lean` | 200 | 200 | 200 | 200 | 200 |
| `copter_ref` | 200 | 200 | 200 | 200 | 200 |

No run violates the contract.

## Margins

Over all 200 runs of each vehicle; the two vehicles' runs are identical tick by tick (below), so their margins are equal and are given once (`copter_lean`).

| margin | min | median | max | bound |
|---|---|---|---|---|
| ceiling clearance (2.0 m minus max altitude) | 40.81 cm | 40.81 cm | 40.81 cm | > 0 |
| max distance to S | 0.00 cm | 0.00 cm | 0.00 cm | = 0 |
| max distance to the path after leaving the box | 7.70 cm | 8.71 cm | 18.62 cm | ≤ 25 cm |
| corridor margin (25 cm minus the above) | 6.38 cm | 16.29 cm | 17.30 cm | ≥ 0 |
| max distance to the path, whole run | 7.70 cm | 12.49 cm | 19.74 cm | (includes the start offset) |
| time of leaving the box | 0.20 s | 0.95 s | 1.14 s |  |
| leg 0 time | 1.37 s | 1.57 s | 1.69 s | ≤ 3 s |
| leg 1 time | 1.93 s | 1.98 s | 2.08 s | ≤ 3 s |
| leg 2 time | 1.84 s | 1.85 s | 1.85 s | ≤ 3 s |
| leg 3 time | 1.85 s | 1.85 s | 1.86 s | ≤ 3 s |
| leg 4 time | 3.62 s | 3.62 s | 3.62 s | ≤ 6 s |
| leg 5 time | 1.85 s | 1.85 s | 1.85 s | ≤ 3 s |
| leg 6 time | 1.85 s | 1.85 s | 1.85 s | ≤ 3 s |
| leg 7 time | 1.85 s | 1.85 s | 1.85 s | ≤ 3 s |
| leg 0 slack | 1.31 s | 1.43 s | 1.63 s | ≥ 0 |
| leg 1 slack | 0.92 s | 1.02 s | 1.07 s | ≥ 0 |
| leg 2 slack | 1.15 s | 1.15 s | 1.16 s | ≥ 0 |
| leg 3 slack | 1.14 s | 1.15 s | 1.15 s | ≥ 0 |
| leg 4 slack | 2.38 s | 2.38 s | 2.38 s | ≥ 0 |
| leg 5 slack | 1.15 s | 1.15 s | 1.15 s | ≥ 0 |
| leg 6 slack | 1.15 s | 1.15 s | 1.15 s | ≥ 0 |
| leg 7 slack | 1.15 s | 1.15 s | 1.15 s | ≥ 0 |
| hold first achieved at | 16.32 s | 16.42 s | 16.50 s | ≤ 27 s |
| hold, best window: max distance to w7 | 2.81 cm | 2.81 cm | 2.81 cm | ≤ 10 cm |
| hold margin (10 cm minus the above) | 7.19 cm | 7.19 cm | 7.19 cm | ≥ 0 |

## Parity

200 paired runs; the four actuators of every tick are compared as float32 bit patterns between `copter_lean` and `copter_ref`: 0 paired runs with any differing tick (0 differing ticks in all, 2400200 ticks compared).

## Timing

Machine: arm64, 10 physical cores, 9 workers, Python 3.12.13. Total wall clock 153.3 s for 400 flights (12001 simulated seconds).

| vehicle | flights | simulated s per flight | wall s per flight (loop), median | wall s per flight (with trace file and monitor), median | wall s per simulated s, median |
|---|---|---|---|---|---|
| `copter_lean` | 200 | 30.0025 | 4.762 | 4.876 | 0.1587 |
| `copter_ref` | 200 | 30.0025 | 1.761 | 1.879 | 0.0587 |

The per-flight times are measured inside the workers, which run concurrently; a flight's wall clock therefore includes the contention of the other workers.

## Reproduce

```
sim/.venv/bin/python sim/monitor.py --derive-spec     # the spec from sim/out/lean-course-1ms (once)
sim/.venv/bin/python sim/montecarlo.py
```

Outputs in `sim/out/montecarlo`: summary.csv, samples.json, runs/<lean|ref>-<i>.csv.gz (per tick t, NED position, yaw, the four actuators as float32 hex) and runs/<lean|ref>-<i>.txt (one line per run).
