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

## Sensing noise

Level L4: every tick the sample sent to the controller is the true state plus independent errors uniform in [-b, b] per component: position bp = 0.05 m, velocity bv = 0.1 m/s, specific force bf = 0 m/s², body rates bw = 0.02 rad/s, and the attitude rotated by a small body-frame rotation with angles uniform in [-bq, bq], bq = 1 deg (quaternion renormalized). The physics, the end conditions and the monitored positions use the true state. The noise of sample i comes from `numpy.random.default_rng([20261105, 1, i])`, 15 uniforms per tick, the same stream for both vehicles of a pair (`montecarlo.perturb`).

## Verdicts

| vehicle | runs | ψ holds | safety | ordered reach | reach and hold |
|---|---|---|---|---|---|
| `copter_lean` | 200 | 120 | 200 | 200 | 120 |
| `copter_ref` | 200 | 120 | 200 | 200 | 120 |

Violations:

- `copter_lean` sample 3, sampled NED (0.1060, -0.0266, -0.0446), heading 128.80 deg, start in the air: reach and hold: no 3 s window within 0.1 m of w7 starting by 27 s (best window max distance 12.31 cm)
- `copter_lean` sample 5, sampled NED (-0.0490, -0.0352, -0.2235), heading 49.72 deg, start in the air: reach and hold: no 3 s window within 0.1 m of w7 starting by 27 s (best window max distance 11.00 cm)
- `copter_lean` sample 6, sampled NED (0.0387, 0.0973, -0.0411), heading -96.40 deg, start in the air: reach and hold: no 3 s window within 0.1 m of w7 starting by 27 s (best window max distance 12.43 cm)
- `copter_lean` sample 10, sampled NED (-0.1102, 0.0677, -0.1656), heading 89.58 deg, start in the air: reach and hold: no 3 s window within 0.1 m of w7 starting by 27 s (best window max distance 13.34 cm)
- `copter_lean` sample 13, sampled NED (0.1385, -0.0877, -0.2391), heading -136.05 deg, start in the air: reach and hold: no 3 s window within 0.1 m of w7 starting by 27 s (best window max distance 13.60 cm)
- `copter_lean` sample 14, sampled NED (0.0922, 0.1071, -0.2728), heading -121.98 deg, start in the air: reach and hold: no 3 s window within 0.1 m of w7 starting by 27 s (best window max distance 11.05 cm)
- `copter_lean` sample 16, sampled NED (-0.1264, 0.0290, -0.0715), heading -109.37 deg, start in the air: reach and hold: no 3 s window within 0.1 m of w7 starting by 27 s (best window max distance 16.49 cm)
- `copter_lean` sample 18, sampled NED (0.0387, -0.0462, -0.1997), heading 11.82 deg, start in the air: reach and hold: no 3 s window within 0.1 m of w7 starting by 27 s (best window max distance 15.26 cm)
- `copter_lean` sample 20, sampled NED (-0.0872, 0.0959, -0.1303), heading -56.31 deg, start in the air: reach and hold: no 3 s window within 0.1 m of w7 starting by 27 s (best window max distance 11.85 cm)
- `copter_lean` sample 21, sampled NED (-0.0466, 0.0114, -0.2296), heading -94.31 deg, start in the air: reach and hold: no 3 s window within 0.1 m of w7 starting by 27 s (best window max distance 11.41 cm)
- `copter_lean` sample 23, sampled NED (-0.0550, -0.0799, -0.1561), heading -49.13 deg, start in the air: reach and hold: no 3 s window within 0.1 m of w7 starting by 27 s (best window max distance 10.99 cm)
- `copter_lean` sample 26, sampled NED (0.1078, -0.0032, -0.1188), heading -64.28 deg, start in the air: reach and hold: no 3 s window within 0.1 m of w7 starting by 27 s (best window max distance 11.88 cm)
- `copter_lean` sample 27, sampled NED (-0.1026, 0.1020, -0.0845), heading -97.29 deg, start in the air: reach and hold: no 3 s window within 0.1 m of w7 starting by 27 s (best window max distance 11.91 cm)
- `copter_lean` sample 31, sampled NED (-0.0455, 0.0773, -0.0123), heading -127.53 deg, start on the ground: reach and hold: no 3 s window within 0.1 m of w7 starting by 27 s (best window max distance 14.53 cm)
- `copter_lean` sample 32, sampled NED (0.1319, 0.0856, -0.0326), heading -26.96 deg, start in the air: reach and hold: no 3 s window within 0.1 m of w7 starting by 27 s (best window max distance 12.24 cm)
- `copter_lean` sample 33, sampled NED (-0.1447, -0.0106, -0.1507), heading 136.86 deg, start in the air: reach and hold: no 3 s window within 0.1 m of w7 starting by 27 s (best window max distance 14.71 cm)
- `copter_lean` sample 35, sampled NED (-0.1207, 0.1369, -0.1014), heading -29.25 deg, start in the air: reach and hold: no 3 s window within 0.1 m of w7 starting by 27 s (best window max distance 11.36 cm)
- `copter_lean` sample 36, sampled NED (0.0563, -0.0790, -0.0382), heading -85.46 deg, start in the air: reach and hold: no 3 s window within 0.1 m of w7 starting by 27 s (best window max distance 12.62 cm)
- `copter_lean` sample 37, sampled NED (-0.1026, -0.1161, -0.0650), heading 18.32 deg, start in the air: reach and hold: no 3 s window within 0.1 m of w7 starting by 27 s (best window max distance 15.60 cm)
- `copter_lean` sample 42, sampled NED (-0.0913, 0.1348, -0.2244), heading 79.66 deg, start in the air: reach and hold: no 3 s window within 0.1 m of w7 starting by 27 s (best window max distance 11.19 cm)
- `copter_lean` sample 44, sampled NED (-0.0040, 0.1117, -0.0292), heading 164.06 deg, start in the air: reach and hold: no 3 s window within 0.1 m of w7 starting by 27 s (best window max distance 12.53 cm)
- `copter_lean` sample 48, sampled NED (0.0047, -0.0256, -0.0385), heading 171.85 deg, start in the air: reach and hold: no 3 s window within 0.1 m of w7 starting by 27 s (best window max distance 13.83 cm)
- `copter_lean` sample 50, sampled NED (0.0325, 0.0814, -0.2832), heading 80.57 deg, start in the air: reach and hold: no 3 s window within 0.1 m of w7 starting by 27 s (best window max distance 10.11 cm)
- `copter_lean` sample 52, sampled NED (0.0093, -0.0132, -0.1168), heading -110.17 deg, start in the air: reach and hold: no 3 s window within 0.1 m of w7 starting by 27 s (best window max distance 13.06 cm)
- `copter_lean` sample 65, sampled NED (0.1281, -0.0603, -0.0438), heading 174.77 deg, start in the air: reach and hold: no 3 s window within 0.1 m of w7 starting by 27 s (best window max distance 10.04 cm)
- `copter_lean` sample 67, sampled NED (0.0036, 0.0751, -0.0114), heading -87.42 deg, start on the ground: reach and hold: no 3 s window within 0.1 m of w7 starting by 27 s (best window max distance 14.22 cm)
- `copter_lean` sample 72, sampled NED (0.0546, -0.0101, -0.2642), heading 113.15 deg, start in the air: reach and hold: no 3 s window within 0.1 m of w7 starting by 27 s (best window max distance 14.21 cm)
- `copter_lean` sample 75, sampled NED (0.1342, 0.0221, -0.2857), heading 137.45 deg, start in the air: reach and hold: no 3 s window within 0.1 m of w7 starting by 27 s (best window max distance 12.43 cm)
- `copter_lean` sample 78, sampled NED (-0.0013, -0.1137, -0.2686), heading -165.48 deg, start in the air: reach and hold: no 3 s window within 0.1 m of w7 starting by 27 s (best window max distance 17.15 cm)
- `copter_lean` sample 91, sampled NED (0.0536, -0.0679, -0.0486), heading -78.24 deg, start in the air: reach and hold: no 3 s window within 0.1 m of w7 starting by 27 s (best window max distance 11.67 cm)
- `copter_lean` sample 92, sampled NED (0.1410, -0.0086, -0.2294), heading 142.84 deg, start in the air: reach and hold: no 3 s window within 0.1 m of w7 starting by 27 s (best window max distance 15.34 cm)
- `copter_lean` sample 96, sampled NED (0.1055, -0.1289, -0.2106), heading -66.37 deg, start in the air: reach and hold: no 3 s window within 0.1 m of w7 starting by 27 s (best window max distance 13.71 cm)
- `copter_lean` sample 102, sampled NED (-0.1120, 0.0868, -0.0848), heading 54.28 deg, start in the air: reach and hold: no 3 s window within 0.1 m of w7 starting by 27 s (best window max distance 16.46 cm)
- `copter_lean` sample 103, sampled NED (0.0050, -0.0269, -0.1829), heading -172.84 deg, start in the air: reach and hold: no 3 s window within 0.1 m of w7 starting by 27 s (best window max distance 10.21 cm)
- `copter_lean` sample 104, sampled NED (0.1443, 0.0168, -0.2036), heading 30.64 deg, start in the air: reach and hold: no 3 s window within 0.1 m of w7 starting by 27 s (best window max distance 10.62 cm)
- `copter_lean` sample 106, sampled NED (-0.1220, 0.0542, -0.1643), heading -91.26 deg, start in the air: reach and hold: no 3 s window within 0.1 m of w7 starting by 27 s (best window max distance 14.66 cm)
- `copter_lean` sample 108, sampled NED (-0.0343, 0.0449, -0.2079), heading 69.77 deg, start in the air: reach and hold: no 3 s window within 0.1 m of w7 starting by 27 s (best window max distance 14.26 cm)
- `copter_lean` sample 110, sampled NED (0.0749, -0.0871, -0.0251), heading 152.20 deg, start in the air: reach and hold: no 3 s window within 0.1 m of w7 starting by 27 s (best window max distance 10.84 cm)
- `copter_lean` sample 111, sampled NED (0.1239, 0.0004, -0.2248), heading 53.85 deg, start in the air: reach and hold: no 3 s window within 0.1 m of w7 starting by 27 s (best window max distance 14.62 cm)
- `copter_lean` sample 117, sampled NED (-0.0870, 0.0376, -0.0359), heading -101.09 deg, start in the air: reach and hold: no 3 s window within 0.1 m of w7 starting by 27 s (best window max distance 15.93 cm)
- `copter_lean` sample 119, sampled NED (0.0321, 0.1333, -0.0164), heading -88.30 deg, start in the air: reach and hold: no 3 s window within 0.1 m of w7 starting by 27 s (best window max distance 13.68 cm)
- `copter_lean` sample 123, sampled NED (0.0596, 0.0013, -0.2179), heading -132.71 deg, start in the air: reach and hold: no 3 s window within 0.1 m of w7 starting by 27 s (best window max distance 11.29 cm)
- `copter_lean` sample 125, sampled NED (0.0825, 0.0155, -0.1928), heading -99.64 deg, start in the air: reach and hold: no 3 s window within 0.1 m of w7 starting by 27 s (best window max distance 12.42 cm)
- `copter_lean` sample 127, sampled NED (0.0584, -0.1202, -0.2575), heading -103.30 deg, start in the air: reach and hold: no 3 s window within 0.1 m of w7 starting by 27 s (best window max distance 13.04 cm)
- `copter_lean` sample 130, sampled NED (-0.1046, 0.0356, -0.0041), heading -18.32 deg, start on the ground: reach and hold: no 3 s window within 0.1 m of w7 starting by 27 s (best window max distance 10.36 cm)
- `copter_lean` sample 131, sampled NED (0.0881, -0.0103, -0.1407), heading 163.16 deg, start in the air: reach and hold: no 3 s window within 0.1 m of w7 starting by 27 s (best window max distance 11.67 cm)
- `copter_lean` sample 133, sampled NED (-0.0720, -0.0324, -0.1830), heading 25.25 deg, start in the air: reach and hold: no 3 s window within 0.1 m of w7 starting by 27 s (best window max distance 19.00 cm)
- `copter_lean` sample 137, sampled NED (0.1268, -0.1106, -0.0514), heading 139.93 deg, start in the air: reach and hold: no 3 s window within 0.1 m of w7 starting by 27 s (best window max distance 15.99 cm)
- `copter_lean` sample 138, sampled NED (0.0345, 0.1169, -0.1763), heading -44.90 deg, start in the air: reach and hold: no 3 s window within 0.1 m of w7 starting by 27 s (best window max distance 12.57 cm)
- `copter_lean` sample 139, sampled NED (-0.0834, -0.0089, -0.0836), heading -122.72 deg, start in the air: reach and hold: no 3 s window within 0.1 m of w7 starting by 27 s (best window max distance 10.50 cm)
- `copter_lean` sample 142, sampled NED (-0.0670, 0.1200, -0.2711), heading -13.33 deg, start in the air: reach and hold: no 3 s window within 0.1 m of w7 starting by 27 s (best window max distance 10.21 cm)
- `copter_lean` sample 143, sampled NED (0.1203, 0.1099, -0.0567), heading 160.85 deg, start in the air: reach and hold: no 3 s window within 0.1 m of w7 starting by 27 s (best window max distance 16.07 cm)
- `copter_lean` sample 148, sampled NED (0.0496, 0.0833, -0.0902), heading -117.77 deg, start in the air: reach and hold: no 3 s window within 0.1 m of w7 starting by 27 s (best window max distance 10.62 cm)
- `copter_lean` sample 149, sampled NED (0.0914, 0.0367, -0.0635), heading -143.44 deg, start in the air: reach and hold: no 3 s window within 0.1 m of w7 starting by 27 s (best window max distance 15.22 cm)
- `copter_lean` sample 150, sampled NED (0.1333, 0.0759, -0.1216), heading -128.46 deg, start in the air: reach and hold: no 3 s window within 0.1 m of w7 starting by 27 s (best window max distance 16.69 cm)
- `copter_lean` sample 154, sampled NED (0.0910, 0.0075, -0.0767), heading -105.35 deg, start in the air: reach and hold: no 3 s window within 0.1 m of w7 starting by 27 s (best window max distance 11.05 cm)
- `copter_lean` sample 158, sampled NED (-0.0494, 0.0836, -0.0404), heading 10.83 deg, start in the air: reach and hold: no 3 s window within 0.1 m of w7 starting by 27 s (best window max distance 13.09 cm)
- `copter_lean` sample 159, sampled NED (-0.1015, -0.0405, -0.1516), heading -83.21 deg, start in the air: reach and hold: no 3 s window within 0.1 m of w7 starting by 27 s (best window max distance 14.10 cm)
- `copter_lean` sample 161, sampled NED (-0.1471, -0.1182, -0.1389), heading 12.84 deg, start in the air: reach and hold: no 3 s window within 0.1 m of w7 starting by 27 s (best window max distance 11.49 cm)
- `copter_lean` sample 164, sampled NED (0.1340, 0.0782, -0.1290), heading -177.95 deg, start in the air: reach and hold: no 3 s window within 0.1 m of w7 starting by 27 s (best window max distance 10.11 cm)
- `copter_lean` sample 165, sampled NED (0.0961, 0.1215, -0.1447), heading 176.82 deg, start in the air: reach and hold: no 3 s window within 0.1 m of w7 starting by 27 s (best window max distance 11.34 cm)
- `copter_lean` sample 166, sampled NED (-0.1312, 0.0517, -0.1866), heading 31.43 deg, start in the air: reach and hold: no 3 s window within 0.1 m of w7 starting by 27 s (best window max distance 15.84 cm)
- `copter_lean` sample 168, sampled NED (-0.0327, -0.0972, -0.2525), heading -71.29 deg, start in the air: reach and hold: no 3 s window within 0.1 m of w7 starting by 27 s (best window max distance 12.31 cm)
- `copter_lean` sample 170, sampled NED (-0.0819, -0.0590, -0.1514), heading -34.44 deg, start in the air: reach and hold: no 3 s window within 0.1 m of w7 starting by 27 s (best window max distance 13.72 cm)
- `copter_lean` sample 171, sampled NED (0.1467, -0.0380, -0.2230), heading 13.82 deg, start in the air: reach and hold: no 3 s window within 0.1 m of w7 starting by 27 s (best window max distance 11.62 cm)
- `copter_lean` sample 172, sampled NED (-0.0171, -0.0680, -0.0169), heading -33.23 deg, start in the air: reach and hold: no 3 s window within 0.1 m of w7 starting by 27 s (best window max distance 16.81 cm)
- `copter_lean` sample 174, sampled NED (-0.0737, -0.0156, -0.0370), heading 153.20 deg, start in the air: reach and hold: no 3 s window within 0.1 m of w7 starting by 27 s (best window max distance 14.05 cm)
- `copter_lean` sample 177, sampled NED (0.1006, -0.0457, -0.0433), heading 25.08 deg, start in the air: reach and hold: no 3 s window within 0.1 m of w7 starting by 27 s (best window max distance 15.97 cm)
- `copter_lean` sample 179, sampled NED (0.0148, 0.0664, -0.2015), heading 96.23 deg, start in the air: reach and hold: no 3 s window within 0.1 m of w7 starting by 27 s (best window max distance 13.63 cm)
- `copter_lean` sample 180, sampled NED (-0.0101, -0.0699, -0.1650), heading -126.25 deg, start in the air: reach and hold: no 3 s window within 0.1 m of w7 starting by 27 s (best window max distance 12.27 cm)
- `copter_lean` sample 183, sampled NED (0.0643, 0.0646, -0.2209), heading -153.58 deg, start in the air: reach and hold: no 3 s window within 0.1 m of w7 starting by 27 s (best window max distance 11.31 cm)
- `copter_lean` sample 184, sampled NED (-0.1335, -0.0190, -0.0262), heading -127.67 deg, start in the air: reach and hold: no 3 s window within 0.1 m of w7 starting by 27 s (best window max distance 10.92 cm)
- `copter_lean` sample 185, sampled NED (-0.0839, 0.0774, -0.0094), heading -137.21 deg, start on the ground: reach and hold: no 3 s window within 0.1 m of w7 starting by 27 s (best window max distance 13.38 cm)
- `copter_lean` sample 186, sampled NED (0.0089, 0.0967, -0.2219), heading -128.69 deg, start in the air: reach and hold: no 3 s window within 0.1 m of w7 starting by 27 s (best window max distance 15.76 cm)
- `copter_lean` sample 188, sampled NED (-0.1318, -0.0125, -0.2765), heading 178.03 deg, start in the air: reach and hold: no 3 s window within 0.1 m of w7 starting by 27 s (best window max distance 12.50 cm)
- `copter_lean` sample 191, sampled NED (-0.0296, 0.0190, -0.0303), heading -68.60 deg, start in the air: reach and hold: no 3 s window within 0.1 m of w7 starting by 27 s (best window max distance 13.27 cm)
- `copter_lean` sample 192, sampled NED (-0.1270, -0.0728, -0.1310), heading -144.05 deg, start in the air: reach and hold: no 3 s window within 0.1 m of w7 starting by 27 s (best window max distance 13.86 cm)
- `copter_lean` sample 195, sampled NED (-0.0473, -0.0250, -0.1068), heading -137.50 deg, start in the air: reach and hold: no 3 s window within 0.1 m of w7 starting by 27 s (best window max distance 11.81 cm)
- `copter_lean` sample 197, sampled NED (-0.0938, -0.1188, -0.0465), heading -5.95 deg, start in the air: reach and hold: no 3 s window within 0.1 m of w7 starting by 27 s (best window max distance 12.97 cm)
- `copter_lean` sample 199, sampled NED (-0.0893, 0.1293, -0.2476), heading 59.84 deg, start in the air: reach and hold: no 3 s window within 0.1 m of w7 starting by 27 s (best window max distance 10.26 cm)
- `copter_ref` sample 3, sampled NED (0.1060, -0.0266, -0.0446), heading 128.80 deg, start in the air: reach and hold: no 3 s window within 0.1 m of w7 starting by 27 s (best window max distance 12.31 cm)
- `copter_ref` sample 5, sampled NED (-0.0490, -0.0352, -0.2235), heading 49.72 deg, start in the air: reach and hold: no 3 s window within 0.1 m of w7 starting by 27 s (best window max distance 11.00 cm)
- `copter_ref` sample 6, sampled NED (0.0387, 0.0973, -0.0411), heading -96.40 deg, start in the air: reach and hold: no 3 s window within 0.1 m of w7 starting by 27 s (best window max distance 12.43 cm)
- `copter_ref` sample 10, sampled NED (-0.1102, 0.0677, -0.1656), heading 89.58 deg, start in the air: reach and hold: no 3 s window within 0.1 m of w7 starting by 27 s (best window max distance 13.34 cm)
- `copter_ref` sample 13, sampled NED (0.1385, -0.0877, -0.2391), heading -136.05 deg, start in the air: reach and hold: no 3 s window within 0.1 m of w7 starting by 27 s (best window max distance 13.60 cm)
- `copter_ref` sample 14, sampled NED (0.0922, 0.1071, -0.2728), heading -121.98 deg, start in the air: reach and hold: no 3 s window within 0.1 m of w7 starting by 27 s (best window max distance 11.05 cm)
- `copter_ref` sample 16, sampled NED (-0.1264, 0.0290, -0.0715), heading -109.37 deg, start in the air: reach and hold: no 3 s window within 0.1 m of w7 starting by 27 s (best window max distance 16.49 cm)
- `copter_ref` sample 18, sampled NED (0.0387, -0.0462, -0.1997), heading 11.82 deg, start in the air: reach and hold: no 3 s window within 0.1 m of w7 starting by 27 s (best window max distance 15.26 cm)
- `copter_ref` sample 20, sampled NED (-0.0872, 0.0959, -0.1303), heading -56.31 deg, start in the air: reach and hold: no 3 s window within 0.1 m of w7 starting by 27 s (best window max distance 11.85 cm)
- `copter_ref` sample 21, sampled NED (-0.0466, 0.0114, -0.2296), heading -94.31 deg, start in the air: reach and hold: no 3 s window within 0.1 m of w7 starting by 27 s (best window max distance 11.41 cm)
- `copter_ref` sample 23, sampled NED (-0.0550, -0.0799, -0.1561), heading -49.13 deg, start in the air: reach and hold: no 3 s window within 0.1 m of w7 starting by 27 s (best window max distance 10.99 cm)
- `copter_ref` sample 26, sampled NED (0.1078, -0.0032, -0.1188), heading -64.28 deg, start in the air: reach and hold: no 3 s window within 0.1 m of w7 starting by 27 s (best window max distance 11.88 cm)
- `copter_ref` sample 27, sampled NED (-0.1026, 0.1020, -0.0845), heading -97.29 deg, start in the air: reach and hold: no 3 s window within 0.1 m of w7 starting by 27 s (best window max distance 11.91 cm)
- `copter_ref` sample 31, sampled NED (-0.0455, 0.0773, -0.0123), heading -127.53 deg, start on the ground: reach and hold: no 3 s window within 0.1 m of w7 starting by 27 s (best window max distance 14.53 cm)
- `copter_ref` sample 32, sampled NED (0.1319, 0.0856, -0.0326), heading -26.96 deg, start in the air: reach and hold: no 3 s window within 0.1 m of w7 starting by 27 s (best window max distance 12.24 cm)
- `copter_ref` sample 33, sampled NED (-0.1447, -0.0106, -0.1507), heading 136.86 deg, start in the air: reach and hold: no 3 s window within 0.1 m of w7 starting by 27 s (best window max distance 14.71 cm)
- `copter_ref` sample 35, sampled NED (-0.1207, 0.1369, -0.1014), heading -29.25 deg, start in the air: reach and hold: no 3 s window within 0.1 m of w7 starting by 27 s (best window max distance 11.36 cm)
- `copter_ref` sample 36, sampled NED (0.0563, -0.0790, -0.0382), heading -85.46 deg, start in the air: reach and hold: no 3 s window within 0.1 m of w7 starting by 27 s (best window max distance 12.62 cm)
- `copter_ref` sample 37, sampled NED (-0.1026, -0.1161, -0.0650), heading 18.32 deg, start in the air: reach and hold: no 3 s window within 0.1 m of w7 starting by 27 s (best window max distance 15.60 cm)
- `copter_ref` sample 42, sampled NED (-0.0913, 0.1348, -0.2244), heading 79.66 deg, start in the air: reach and hold: no 3 s window within 0.1 m of w7 starting by 27 s (best window max distance 11.19 cm)
- `copter_ref` sample 44, sampled NED (-0.0040, 0.1117, -0.0292), heading 164.06 deg, start in the air: reach and hold: no 3 s window within 0.1 m of w7 starting by 27 s (best window max distance 12.53 cm)
- `copter_ref` sample 48, sampled NED (0.0047, -0.0256, -0.0385), heading 171.85 deg, start in the air: reach and hold: no 3 s window within 0.1 m of w7 starting by 27 s (best window max distance 13.83 cm)
- `copter_ref` sample 50, sampled NED (0.0325, 0.0814, -0.2832), heading 80.57 deg, start in the air: reach and hold: no 3 s window within 0.1 m of w7 starting by 27 s (best window max distance 10.11 cm)
- `copter_ref` sample 52, sampled NED (0.0093, -0.0132, -0.1168), heading -110.17 deg, start in the air: reach and hold: no 3 s window within 0.1 m of w7 starting by 27 s (best window max distance 13.06 cm)
- `copter_ref` sample 65, sampled NED (0.1281, -0.0603, -0.0438), heading 174.77 deg, start in the air: reach and hold: no 3 s window within 0.1 m of w7 starting by 27 s (best window max distance 10.04 cm)
- `copter_ref` sample 67, sampled NED (0.0036, 0.0751, -0.0114), heading -87.42 deg, start on the ground: reach and hold: no 3 s window within 0.1 m of w7 starting by 27 s (best window max distance 14.22 cm)
- `copter_ref` sample 72, sampled NED (0.0546, -0.0101, -0.2642), heading 113.15 deg, start in the air: reach and hold: no 3 s window within 0.1 m of w7 starting by 27 s (best window max distance 14.21 cm)
- `copter_ref` sample 75, sampled NED (0.1342, 0.0221, -0.2857), heading 137.45 deg, start in the air: reach and hold: no 3 s window within 0.1 m of w7 starting by 27 s (best window max distance 12.43 cm)
- `copter_ref` sample 78, sampled NED (-0.0013, -0.1137, -0.2686), heading -165.48 deg, start in the air: reach and hold: no 3 s window within 0.1 m of w7 starting by 27 s (best window max distance 17.15 cm)
- `copter_ref` sample 91, sampled NED (0.0536, -0.0679, -0.0486), heading -78.24 deg, start in the air: reach and hold: no 3 s window within 0.1 m of w7 starting by 27 s (best window max distance 11.67 cm)
- `copter_ref` sample 92, sampled NED (0.1410, -0.0086, -0.2294), heading 142.84 deg, start in the air: reach and hold: no 3 s window within 0.1 m of w7 starting by 27 s (best window max distance 15.34 cm)
- `copter_ref` sample 96, sampled NED (0.1055, -0.1289, -0.2106), heading -66.37 deg, start in the air: reach and hold: no 3 s window within 0.1 m of w7 starting by 27 s (best window max distance 13.71 cm)
- `copter_ref` sample 102, sampled NED (-0.1120, 0.0868, -0.0848), heading 54.28 deg, start in the air: reach and hold: no 3 s window within 0.1 m of w7 starting by 27 s (best window max distance 16.46 cm)
- `copter_ref` sample 103, sampled NED (0.0050, -0.0269, -0.1829), heading -172.84 deg, start in the air: reach and hold: no 3 s window within 0.1 m of w7 starting by 27 s (best window max distance 10.21 cm)
- `copter_ref` sample 104, sampled NED (0.1443, 0.0168, -0.2036), heading 30.64 deg, start in the air: reach and hold: no 3 s window within 0.1 m of w7 starting by 27 s (best window max distance 10.62 cm)
- `copter_ref` sample 106, sampled NED (-0.1220, 0.0542, -0.1643), heading -91.26 deg, start in the air: reach and hold: no 3 s window within 0.1 m of w7 starting by 27 s (best window max distance 14.66 cm)
- `copter_ref` sample 108, sampled NED (-0.0343, 0.0449, -0.2079), heading 69.77 deg, start in the air: reach and hold: no 3 s window within 0.1 m of w7 starting by 27 s (best window max distance 14.26 cm)
- `copter_ref` sample 110, sampled NED (0.0749, -0.0871, -0.0251), heading 152.20 deg, start in the air: reach and hold: no 3 s window within 0.1 m of w7 starting by 27 s (best window max distance 10.84 cm)
- `copter_ref` sample 111, sampled NED (0.1239, 0.0004, -0.2248), heading 53.85 deg, start in the air: reach and hold: no 3 s window within 0.1 m of w7 starting by 27 s (best window max distance 14.62 cm)
- `copter_ref` sample 117, sampled NED (-0.0870, 0.0376, -0.0359), heading -101.09 deg, start in the air: reach and hold: no 3 s window within 0.1 m of w7 starting by 27 s (best window max distance 15.93 cm)
- `copter_ref` sample 119, sampled NED (0.0321, 0.1333, -0.0164), heading -88.30 deg, start in the air: reach and hold: no 3 s window within 0.1 m of w7 starting by 27 s (best window max distance 13.68 cm)
- `copter_ref` sample 123, sampled NED (0.0596, 0.0013, -0.2179), heading -132.71 deg, start in the air: reach and hold: no 3 s window within 0.1 m of w7 starting by 27 s (best window max distance 11.29 cm)
- `copter_ref` sample 125, sampled NED (0.0825, 0.0155, -0.1928), heading -99.64 deg, start in the air: reach and hold: no 3 s window within 0.1 m of w7 starting by 27 s (best window max distance 12.42 cm)
- `copter_ref` sample 127, sampled NED (0.0584, -0.1202, -0.2575), heading -103.30 deg, start in the air: reach and hold: no 3 s window within 0.1 m of w7 starting by 27 s (best window max distance 13.04 cm)
- `copter_ref` sample 130, sampled NED (-0.1046, 0.0356, -0.0041), heading -18.32 deg, start on the ground: reach and hold: no 3 s window within 0.1 m of w7 starting by 27 s (best window max distance 10.36 cm)
- `copter_ref` sample 131, sampled NED (0.0881, -0.0103, -0.1407), heading 163.16 deg, start in the air: reach and hold: no 3 s window within 0.1 m of w7 starting by 27 s (best window max distance 11.67 cm)
- `copter_ref` sample 133, sampled NED (-0.0720, -0.0324, -0.1830), heading 25.25 deg, start in the air: reach and hold: no 3 s window within 0.1 m of w7 starting by 27 s (best window max distance 19.00 cm)
- `copter_ref` sample 137, sampled NED (0.1268, -0.1106, -0.0514), heading 139.93 deg, start in the air: reach and hold: no 3 s window within 0.1 m of w7 starting by 27 s (best window max distance 15.99 cm)
- `copter_ref` sample 138, sampled NED (0.0345, 0.1169, -0.1763), heading -44.90 deg, start in the air: reach and hold: no 3 s window within 0.1 m of w7 starting by 27 s (best window max distance 12.57 cm)
- `copter_ref` sample 139, sampled NED (-0.0834, -0.0089, -0.0836), heading -122.72 deg, start in the air: reach and hold: no 3 s window within 0.1 m of w7 starting by 27 s (best window max distance 10.50 cm)
- `copter_ref` sample 142, sampled NED (-0.0670, 0.1200, -0.2711), heading -13.33 deg, start in the air: reach and hold: no 3 s window within 0.1 m of w7 starting by 27 s (best window max distance 10.21 cm)
- `copter_ref` sample 143, sampled NED (0.1203, 0.1099, -0.0567), heading 160.85 deg, start in the air: reach and hold: no 3 s window within 0.1 m of w7 starting by 27 s (best window max distance 16.07 cm)
- `copter_ref` sample 148, sampled NED (0.0496, 0.0833, -0.0902), heading -117.77 deg, start in the air: reach and hold: no 3 s window within 0.1 m of w7 starting by 27 s (best window max distance 10.62 cm)
- `copter_ref` sample 149, sampled NED (0.0914, 0.0367, -0.0635), heading -143.44 deg, start in the air: reach and hold: no 3 s window within 0.1 m of w7 starting by 27 s (best window max distance 15.22 cm)
- `copter_ref` sample 150, sampled NED (0.1333, 0.0759, -0.1216), heading -128.46 deg, start in the air: reach and hold: no 3 s window within 0.1 m of w7 starting by 27 s (best window max distance 16.69 cm)
- `copter_ref` sample 154, sampled NED (0.0910, 0.0075, -0.0767), heading -105.35 deg, start in the air: reach and hold: no 3 s window within 0.1 m of w7 starting by 27 s (best window max distance 11.05 cm)
- `copter_ref` sample 158, sampled NED (-0.0494, 0.0836, -0.0404), heading 10.83 deg, start in the air: reach and hold: no 3 s window within 0.1 m of w7 starting by 27 s (best window max distance 13.09 cm)
- `copter_ref` sample 159, sampled NED (-0.1015, -0.0405, -0.1516), heading -83.21 deg, start in the air: reach and hold: no 3 s window within 0.1 m of w7 starting by 27 s (best window max distance 14.10 cm)
- `copter_ref` sample 161, sampled NED (-0.1471, -0.1182, -0.1389), heading 12.84 deg, start in the air: reach and hold: no 3 s window within 0.1 m of w7 starting by 27 s (best window max distance 11.49 cm)
- `copter_ref` sample 164, sampled NED (0.1340, 0.0782, -0.1290), heading -177.95 deg, start in the air: reach and hold: no 3 s window within 0.1 m of w7 starting by 27 s (best window max distance 10.11 cm)
- `copter_ref` sample 165, sampled NED (0.0961, 0.1215, -0.1447), heading 176.82 deg, start in the air: reach and hold: no 3 s window within 0.1 m of w7 starting by 27 s (best window max distance 11.34 cm)
- `copter_ref` sample 166, sampled NED (-0.1312, 0.0517, -0.1866), heading 31.43 deg, start in the air: reach and hold: no 3 s window within 0.1 m of w7 starting by 27 s (best window max distance 15.84 cm)
- `copter_ref` sample 168, sampled NED (-0.0327, -0.0972, -0.2525), heading -71.29 deg, start in the air: reach and hold: no 3 s window within 0.1 m of w7 starting by 27 s (best window max distance 12.31 cm)
- `copter_ref` sample 170, sampled NED (-0.0819, -0.0590, -0.1514), heading -34.44 deg, start in the air: reach and hold: no 3 s window within 0.1 m of w7 starting by 27 s (best window max distance 13.72 cm)
- `copter_ref` sample 171, sampled NED (0.1467, -0.0380, -0.2230), heading 13.82 deg, start in the air: reach and hold: no 3 s window within 0.1 m of w7 starting by 27 s (best window max distance 11.62 cm)
- `copter_ref` sample 172, sampled NED (-0.0171, -0.0680, -0.0169), heading -33.23 deg, start in the air: reach and hold: no 3 s window within 0.1 m of w7 starting by 27 s (best window max distance 16.81 cm)
- `copter_ref` sample 174, sampled NED (-0.0737, -0.0156, -0.0370), heading 153.20 deg, start in the air: reach and hold: no 3 s window within 0.1 m of w7 starting by 27 s (best window max distance 14.05 cm)
- `copter_ref` sample 177, sampled NED (0.1006, -0.0457, -0.0433), heading 25.08 deg, start in the air: reach and hold: no 3 s window within 0.1 m of w7 starting by 27 s (best window max distance 15.97 cm)
- `copter_ref` sample 179, sampled NED (0.0148, 0.0664, -0.2015), heading 96.23 deg, start in the air: reach and hold: no 3 s window within 0.1 m of w7 starting by 27 s (best window max distance 13.63 cm)
- `copter_ref` sample 180, sampled NED (-0.0101, -0.0699, -0.1650), heading -126.25 deg, start in the air: reach and hold: no 3 s window within 0.1 m of w7 starting by 27 s (best window max distance 12.27 cm)
- `copter_ref` sample 183, sampled NED (0.0643, 0.0646, -0.2209), heading -153.58 deg, start in the air: reach and hold: no 3 s window within 0.1 m of w7 starting by 27 s (best window max distance 11.31 cm)
- `copter_ref` sample 184, sampled NED (-0.1335, -0.0190, -0.0262), heading -127.67 deg, start in the air: reach and hold: no 3 s window within 0.1 m of w7 starting by 27 s (best window max distance 10.92 cm)
- `copter_ref` sample 185, sampled NED (-0.0839, 0.0774, -0.0094), heading -137.21 deg, start on the ground: reach and hold: no 3 s window within 0.1 m of w7 starting by 27 s (best window max distance 13.38 cm)
- `copter_ref` sample 186, sampled NED (0.0089, 0.0967, -0.2219), heading -128.69 deg, start in the air: reach and hold: no 3 s window within 0.1 m of w7 starting by 27 s (best window max distance 15.76 cm)
- `copter_ref` sample 188, sampled NED (-0.1318, -0.0125, -0.2765), heading 178.03 deg, start in the air: reach and hold: no 3 s window within 0.1 m of w7 starting by 27 s (best window max distance 12.50 cm)
- `copter_ref` sample 191, sampled NED (-0.0296, 0.0190, -0.0303), heading -68.60 deg, start in the air: reach and hold: no 3 s window within 0.1 m of w7 starting by 27 s (best window max distance 13.27 cm)
- `copter_ref` sample 192, sampled NED (-0.1270, -0.0728, -0.1310), heading -144.05 deg, start in the air: reach and hold: no 3 s window within 0.1 m of w7 starting by 27 s (best window max distance 13.86 cm)
- `copter_ref` sample 195, sampled NED (-0.0473, -0.0250, -0.1068), heading -137.50 deg, start in the air: reach and hold: no 3 s window within 0.1 m of w7 starting by 27 s (best window max distance 11.81 cm)
- `copter_ref` sample 197, sampled NED (-0.0938, -0.1188, -0.0465), heading -5.95 deg, start in the air: reach and hold: no 3 s window within 0.1 m of w7 starting by 27 s (best window max distance 12.97 cm)
- `copter_ref` sample 199, sampled NED (-0.0893, 0.1293, -0.2476), heading 59.84 deg, start in the air: reach and hold: no 3 s window within 0.1 m of w7 starting by 27 s (best window max distance 10.26 cm)

## Margins

Over all 200 runs of each vehicle; the two vehicles' runs are identical tick by tick (below), so their margins are equal and are given once (`copter_lean`).

| margin | min | median | max | bound |
|---|---|---|---|---|
| ceiling clearance (2.0 m minus max altitude) | 40.21 cm | 40.74 cm | 41.50 cm | > 0 |
| max distance to S | 0.00 cm | 0.00 cm | 0.00 cm | = 0 |
| max distance to the path after leaving the box | 7.89 cm | 11.31 cm | 21.83 cm | ≤ 25 cm |
| corridor margin (25 cm minus the above) | 3.17 cm | 13.69 cm | 17.11 cm | ≥ 0 |
| max distance to the path, whole run | 7.89 cm | 14.25 cm | 21.83 cm | (includes the start offset) |
| time of leaving the box | 0.12 s | 0.88 s | 1.15 s |  |
| leg 0 time | 1.36 s | 1.56 s | 1.73 s | ≤ 3 s |
| leg 1 time | 1.93 s | 2.03 s | 2.19 s | ≤ 3 s |
| leg 2 time | 1.84 s | 1.87 s | 1.89 s | ≤ 3 s |
| leg 3 time | 1.85 s | 1.88 s | 1.90 s | ≤ 3 s |
| leg 4 time | 3.64 s | 3.66 s | 3.68 s | ≤ 6 s |
| leg 5 time | 1.85 s | 1.88 s | 1.89 s | ≤ 3 s |
| leg 6 time | 1.85 s | 1.88 s | 1.89 s | ≤ 3 s |
| leg 7 time | 1.85 s | 1.87 s | 1.89 s | ≤ 3 s |
| leg 0 slack | 1.27 s | 1.44 s | 1.64 s | ≥ 0 |
| leg 1 slack | 0.81 s | 0.97 s | 1.07 s | ≥ 0 |
| leg 2 slack | 1.11 s | 1.13 s | 1.16 s | ≥ 0 |
| leg 3 slack | 1.10 s | 1.12 s | 1.15 s | ≥ 0 |
| leg 4 slack | 2.32 s | 2.34 s | 2.36 s | ≥ 0 |
| leg 5 slack | 1.11 s | 1.12 s | 1.15 s | ≥ 0 |
| leg 6 slack | 1.11 s | 1.12 s | 1.15 s | ≥ 0 |
| leg 7 slack | 1.11 s | 1.13 s | 1.15 s | ≥ 0 |
| hold first achieved at | 16.46 s | 16.72 s | 26.11 s | ≤ 27 s |
| hold, best window: max distance to w7 | 2.78 cm | 9.24 cm | 19.00 cm | ≤ 10 cm |
| hold margin (10 cm minus the above) | -9.00 cm | 0.76 cm | 7.22 cm | ≥ 0 |

## Parity

200 paired runs; the four actuators of every tick are compared as float32 bit patterns between `copter_lean` and `copter_ref`: 0 paired runs with any differing tick (0 differing ticks in all, 2400200 ticks compared).

## Timing

Machine: arm64, 10 physical cores, 9 workers, Python 3.12.13. Total wall clock 214.3 s for 400 flights (12001 simulated seconds).

| vehicle | flights | simulated s per flight | wall s per flight (loop), median | wall s per flight (with trace file and monitor), median | wall s per simulated s, median |
|---|---|---|---|---|---|
| `copter_lean` | 200 | 30.0025 | 6.284 | 6.474 | 0.2094 |
| `copter_ref` | 200 | 30.0025 | 2.846 | 3.163 | 0.0948 |

The per-flight times are measured inside the workers, which run concurrently; a flight's wall clock therefore includes the contention of the other workers.

## Reproduce

```
sim/.venv/bin/python sim/monitor.py --derive-spec     # the spec from sim/out/lean-course-1ms (once)
sim/.venv/bin/python sim/montecarlo.py --noise L4 --out out/montecarlo-noise-L4
```

Outputs in `sim/out/montecarlo-noise-L4`: summary.csv, samples.json, runs/<lean|ref>-<i>.csv.gz (per tick t, NED position, yaw, the four actuators as float32 hex) and runs/<lean|ref>-<i>.txt (one line per run).
