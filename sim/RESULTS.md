# Flights of the two vehicles

Each mission is flown twice in gym-pybullet-drones (CF2X, PyBullet physics at 1200 Hz, control at 400 Hz,
start at rest on the ground at the origin, facing north), once with `copter_lean` (the Lean translations
of AP_MotorsMatrix, AC_AttitudeControl_Multi, AC_PosControl, AC_WPNav and the AHRS view, with the mission
harness of `lean/Vehicle.lean`) and once with `copter_ref` (ArduPilot's classes compiled unmodified, with
the same harness in C++, `ardupilot/vehicle/copter_ref.cpp`). The two runs are separate processes and
separate simulations; they start from the same initial conditions. Commands: `sim/fly.sh` (README.md).

Tracking error: the distance from the simulated vehicle to AC_PosControl's position target after the
same tick (`--trace`). Final position error: distance to the last waypoint at the end of the run.
Waypoints passed: in order within 0.2 m (the run's end condition); reached: closest approach within
0.1 m. The per-tick comparison is bit for bit: the actuators the simulator received, and all 22 values
of the tick (4 actuators, 18 trace numbers) from each run's replay with `--exact --trace --bits`.

## Hover 1 m above the origin (copter-cf2x.txt + copter-hover.txt + copter-cf2x-tuned.txt, 10 s)

| | `copter_lean` | `copter_ref` |
|---|---|---|
| end of the run | time limit 10 s | time limit 10 s |
| flight time, ticks | 10.0000 s, 4000 | 10.0000 s, 4000 |
| tracking error mean, rms, max | 1.76, 3.40, 10.70 cm | 1.76, 3.40, 10.70 cm |
| final position error (final position NED, m) | 6.17 cm (0.0000 -0.0001 -0.9383) | 6.17 cm (0.0000 -0.0001 -0.9383) |
| waypoints passed | 1 of 1 (within 0.2 m) | 1 of 1 (within 0.2 m) |
| waypoints reached | 1 of 1 (within 0.1 m) | 1 of 1 (within 0.1 m) |
| last waypoint first within 0.1 m | 1.857 s | 1.857 s |
| output directory | `sim/out/lean-hover` | `sim/out/ref-hover` |

Per-tick comparison: 4000 ticks compared (4000 and 4000 flown); simulator states identical on 4000; actuators identical (as flown) on 4000, (bits) on 4000; all 22 values identical (bits) on 4000; first differing tick: none. `run_copter.py`'s own `--trace` replay check: passed for both. Per-tick data: `sim/out/compare-hover.csv`.

## Figure-eight course at 1 m/s (copter-cf2x.txt + copter-course-speed.txt + copter-cf2x-tuned.txt, up to 60 s)

| | `copter_lean` | `copter_ref` |
|---|---|---|
| end of the run | last waypoint held 3 s within 0.1 m | last waypoint held 3 s within 0.1 m |
| flight time, ticks | 19.4925 s, 7797 | 19.4925 s, 7797 |
| tracking error mean, rms, max | 1.71, 2.30, 8.70 cm | 1.71, 2.30, 8.70 cm |
| final position error (final position NED, m) | 2.97 cm (-0.0015 -0.0008 -0.8297) | 2.97 cm (-0.0015 -0.0008 -0.8297) |
| waypoints passed | 8 of 8 (within 0.2 m) | 8 of 8 (within 0.2 m) |
| waypoints reached | 8 of 8 (within 0.1 m) | 8 of 8 (within 0.1 m) |
| last waypoint first within 0.1 m | 16.490 s | 16.490 s |
| output directory | `sim/out/lean-course-1ms` | `sim/out/ref-course-1ms` |

Per-tick comparison: 7797 ticks compared (7797 and 7797 flown); simulator states identical on 7797; actuators identical (as flown) on 7797, (bits) on 7797; all 22 values identical (bits) on 7797; first differing tick: none. `run_copter.py`'s own `--trace` replay check: passed for both. Per-tick data: `sim/out/compare-course-1ms.csv`.

## Figure-eight course with ArduPilot's default WP_SPD 10 m/s, WP_ACC 2.5 m/s^2 (copter-cf2x.txt + copter-cf2x-tuned.txt, up to 30 s)

| | `copter_lean` | `copter_ref` |
|---|---|---|
| end of the run | last waypoint held 3 s within 0.1 m | last waypoint held 3 s within 0.1 m |
| flight time, ticks | 15.8125 s, 6325 | 15.8125 s, 6325 |
| tracking error mean, rms, max | 3.03, 3.52, 9.65 cm | 3.03, 3.52, 9.65 cm |
| final position error (final position NED, m) | 3.88 cm (-0.0063 -0.0053 -0.8379) | 3.88 cm (-0.0063 -0.0053 -0.8379) |
| waypoints passed | 8 of 8 (within 0.2 m) | 8 of 8 (within 0.2 m) |
| waypoints reached | 8 of 8 (within 0.1 m) | 8 of 8 (within 0.1 m) |
| last waypoint first within 0.1 m | 12.810 s | 12.810 s |
| output directory | `sim/out/lean-figure8` | `sim/out/ref-figure8` |

Per-tick comparison: 6325 ticks compared (6325 and 6325 flown); simulator states identical on 6325; actuators identical (as flown) on 6325, (bits) on 6325; all 22 values identical (bits) on 6325; first differing tick: none. `run_copter.py`'s own `--trace` replay check: passed for both. Per-tick data: `sim/out/compare-figure8.csv`.
