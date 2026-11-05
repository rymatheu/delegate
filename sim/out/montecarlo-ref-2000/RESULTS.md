# Monte Carlo validation of the course contract

Closed loop: each vehicle (`copter_lean`, the Lean translations; `copter_ref`, ArduPilot's classes compiled unmodified) in lock step with the CF2X in gym-pybullet-drones (PYB physics at 1200 Hz, control at 400 Hz, gravity 9.80665 m/s², no damping), flying the figure-eight course of `sim/params/copter-cf2x.txt` at 1 m/s with the tuned gains (`copter-cf2x.txt`, `copter-course-speed.txt`, `copter-cf2x-tuned.txt`, `--exact`), the parameters of `sim/fly.sh`'s course-1ms flight. Spec: `sim/spec/mission-course.json`; monitor: `sim/monitor.py` (the formula in STL notation is in its docstring); runner: `sim/montecarlo.py`.

## The contract

- Assumption A, on the state at tick 0: level (roll and pitch 0), any heading (the attitude a rotation about the down axis), at rest (zero velocity and body rates, the hover actuators held), position in the box north [-0.15, 0.15], east [-0.15, 0.15], down [-0.3, 0.0] m (NED from the takeoff point).
- Safety, every tick 0..K: altitude at most 2.0 m, and distance 0 to S, the union of the box and the corridor of radius 0.25 m around the path (the takeoff point, then w0..w7).
- Ordered reach: nested eventually operators, waypoint i within r = 0.1 m within its allowance T_i after waypoint i-1 is reached (w0 from tick 0). Allowances T0 = 3 s, T1 = 3 s, T2 = 3 s, T3 = 3 s, T4 = 6 s, T5 = 3 s, T6 = 3 s, T7 = 3 s (rule: allowance_i = ceil(1.25 * leg_i + 0.5) s, leg_i from the nominal first-within times (leg_0 from t = 0); nominal legs 1.685, 1.933, 1.845, 1.854, 3.621, 1.852, 1.85, 1.85 s from `sim/out/lean-course-1ms`).
- Reach and hold: within T = 27 s, within r of w7 and staying within r for H = 3 s.
- Horizon K = T + H = 12000 ticks (30 s); every flight is simulated for ticks 0..K unless it crashes.

## Samples

N = 2000 initial positions, uniform in the box, `numpy.random.default_rng(20261106).uniform(lo, hi, size=(N, 3))` with lo, hi the box corners (north, east, down), and then the headings from the same generator, `.uniform(-pi, pi, size=N)` (radians, from north, clockwise seen from above); each flown with `copter_ref` (2000 flights). 98 of them lie below the vehicle's resting altitude (0.0135 m), where its collision cylinder would overlap the ground plane; those start resting on the ground at the sampled north and east (settled as the nominal flight; the realized position is in summary.csv), the other 1902 start in the air at the sampled position. Tick-0 specific force of an in-air start: (0, 0, -g), the reading of a vehicle held at rest by its hover thrust, as the controllers' takeover assumes (`--first-accel hover`).

## Verdicts

| vehicle | runs | ψ holds | safety | ordered reach | reach and hold |
|---|---|---|---|---|---|
| `copter_ref` | 2000 | 2000 | 2000 | 2000 | 2000 |

No run violates the contract.

## Margins

Over all 2000 runs of `copter_ref`.

| margin | min | median | max | bound |
|---|---|---|---|---|
| ceiling clearance (2.0 m minus max altitude) | 40.81 cm | 40.81 cm | 40.81 cm | > 0 |
| max distance to S | 0.00 cm | 0.00 cm | 0.00 cm | = 0 |
| max distance to the path after leaving the box | 7.63 cm | 8.54 cm | 20.43 cm | ≤ 25 cm |
| corridor margin (25 cm minus the above) | 4.57 cm | 16.46 cm | 17.37 cm | ≥ 0 |
| max distance to the path, whole run | 7.63 cm | 11.92 cm | 20.73 cm | (includes the start offset) |
| time of leaving the box | 0.15 s | 0.91 s | 1.14 s |  |
| leg 0 time | 1.36 s | 1.55 s | 1.70 s | ≤ 3 s |
| leg 1 time | 1.92 s | 1.99 s | 2.08 s | ≤ 3 s |
| leg 2 time | 1.84 s | 1.85 s | 1.85 s | ≤ 3 s |
| leg 3 time | 1.85 s | 1.85 s | 1.86 s | ≤ 3 s |
| leg 4 time | 3.62 s | 3.62 s | 3.62 s | ≤ 6 s |
| leg 5 time | 1.85 s | 1.85 s | 1.85 s | ≤ 3 s |
| leg 6 time | 1.85 s | 1.85 s | 1.85 s | ≤ 3 s |
| leg 7 time | 1.85 s | 1.85 s | 1.85 s | ≤ 3 s |
| leg 0 slack | 1.30 s | 1.45 s | 1.64 s | ≥ 0 |
| leg 1 slack | 0.92 s | 1.01 s | 1.08 s | ≥ 0 |
| leg 2 slack | 1.15 s | 1.15 s | 1.16 s | ≥ 0 |
| leg 3 slack | 1.14 s | 1.15 s | 1.15 s | ≥ 0 |
| leg 4 slack | 2.38 s | 2.38 s | 2.38 s | ≥ 0 |
| leg 5 slack | 1.15 s | 1.15 s | 1.15 s | ≥ 0 |
| leg 6 slack | 1.15 s | 1.15 s | 1.15 s | ≥ 0 |
| leg 7 slack | 1.15 s | 1.15 s | 1.15 s | ≥ 0 |
| hold first achieved at | 16.32 s | 16.41 s | 16.52 s | ≤ 27 s |
| hold, best window: max distance to w7 | 2.81 cm | 2.81 cm | 2.81 cm | ≤ 10 cm |
| hold margin (10 cm minus the above) | 7.19 cm | 7.19 cm | 7.19 cm | ≥ 0 |

## Parity

Not compared: one vehicle flown.

## Timing

Machine: arm64, 10 physical cores, 9 workers, Python 3.12.13. Total wall clock 395.8 s for 2000 flights (60005 simulated seconds).

| vehicle | flights | simulated s per flight | wall s per flight (loop), median | wall s per flight (with trace file and monitor), median | wall s per simulated s, median |
|---|---|---|---|---|---|
| `copter_ref` | 2000 | 30.0025 | 1.712 | 1.741 | 0.0571 |

The per-flight times are measured inside the workers, which run concurrently; a flight's wall clock therefore includes the contention of the other workers.

## Reproduce

```
sim/.venv/bin/python sim/monitor.py --derive-spec     # the spec from sim/out/lean-course-1ms (once)
sim/.venv/bin/python sim/montecarlo.py --vehicles ref --n 2000 --seed 20261106 --no-traces --out out/montecarlo-ref-2000
```

Outputs in `sim/out/montecarlo-ref-2000`: summary.csv, samples.json, runs/<lean|ref>-<i>.csv.gz (per tick t, NED position, yaw, the four actuators as float32 hex; not written for this run, --no-traces) and runs/<lean|ref>-<i>.txt (one line per run).
