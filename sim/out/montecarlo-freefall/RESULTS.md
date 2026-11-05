# Monte Carlo validation of the course contract

Closed loop: each vehicle (`copter_lean`, the Lean translations; `copter_ref`, ArduPilot's classes compiled unmodified) in lock step with the CF2X in gym-pybullet-drones (PYB physics at 1200 Hz, control at 400 Hz, gravity 9.80665 m/s², no damping), flying the figure-eight course of `sim/params/copter-cf2x.txt` at 1 m/s with the tuned gains (`copter-cf2x.txt`, `copter-course-speed.txt`, `copter-cf2x-tuned.txt`, `--exact`), the parameters of `sim/fly.sh`'s course-1ms flight. Spec: `sim/spec/mission-course.json`; monitor: `sim/monitor.py` (the formula in STL notation is in its docstring); runner: `sim/montecarlo.py`.

## The contract

- Assumption A, on the state at tick 0: level (roll and pitch 0), any heading (the attitude a rotation about the down axis), at rest (zero velocity and body rates, the hover actuators held), position in the box north [-0.15, 0.15], east [-0.15, 0.15], down [-0.3, 0.0] m (NED from the takeoff point).
- Safety, every tick 0..K: altitude at most 2.0 m, and distance 0 to S, the union of the box and the corridor of radius 0.25 m around the path (the takeoff point, then w0..w7).
- Ordered reach: nested eventually operators, waypoint i within r = 0.1 m within its allowance T_i after waypoint i-1 is reached (w0 from tick 0). Allowances T0 = 3 s, T1 = 3 s, T2 = 3 s, T3 = 3 s, T4 = 6 s, T5 = 3 s, T6 = 3 s, T7 = 3 s (rule: allowance_i = ceil(1.25 * leg_i + 0.5) s, leg_i from the nominal first-within times (leg_0 from t = 0); nominal legs 1.685, 1.933, 1.845, 1.854, 3.621, 1.852, 1.85, 1.85 s from `sim/out/lean-course-1ms`).
- Reach and hold: within T = 27 s, within r of w7 and staying within r for H = 3 s.
- Horizon K = T + H = 12000 ticks (30 s); every flight is simulated for ticks 0..K unless it crashes.

## Samples

N = 200 initial positions, uniform in the box, `numpy.random.default_rng(20261105).uniform(lo, hi, size=(N, 3))` with lo, hi the box corners (north, east, down), and then the headings from the same generator, `.uniform(-pi, pi, size=N)` (radians, from north, clockwise seen from above); each flown with `copter_ref` (200 flights). 14 of them lie below the vehicle's resting altitude (0.0135 m), where its collision cylinder would overlap the ground plane; those start resting on the ground at the sampled north and east (settled as the nominal flight; the realized position is in summary.csv), the other 186 start in the air at the sampled position. Tick-0 specific force of an in-air start: (0, 0, 0), free fall, the reading of a vehicle released with no thrust (`--first-accel freefall`).

## Verdicts

| vehicle | runs | ψ holds | safety | ordered reach | reach and hold |
|---|---|---|---|---|---|
| `copter_ref` | 200 | 121 | 200 | 121 | 200 |

Violations:

- `copter_ref` sample 0, sampled NED (0.0787, 0.1380, -0.0180), heading 169.33 deg, start in the air: ordered reach: waypoint 0 not reached within its allowance (leg 3.5675 s, allowance 3 s)
- `copter_ref` sample 2, sampled NED (-0.1341, -0.0810, -0.0790), heading -52.19 deg, start in the air: ordered reach: waypoint 0 not reached within its allowance (leg 3.2150 s, allowance 3 s)
- `copter_ref` sample 3, sampled NED (0.1060, -0.0266, -0.0446), heading 128.80 deg, start in the air: ordered reach: waypoint 0 not reached within its allowance (leg 3.4225 s, allowance 3 s)
- `copter_ref` sample 6, sampled NED (0.0387, 0.0973, -0.0411), heading -96.40 deg, start in the air: ordered reach: waypoint 0 not reached within its allowance (leg 3.4450 s, allowance 3 s)
- `copter_ref` sample 8, sampled NED (0.0606, -0.1466, -0.0273), heading -89.43 deg, start in the air: ordered reach: waypoint 0 not reached within its allowance (leg 3.5300 s, allowance 3 s)
- `copter_ref` sample 11, sampled NED (-0.0245, -0.0890, -0.0395), heading -51.64 deg, start in the air: ordered reach: waypoint 0 not reached within its allowance (leg 3.4325 s, allowance 3 s)
- `copter_ref` sample 12, sampled NED (-0.0261, -0.0388, -0.1057), heading -27.71 deg, start in the air: ordered reach: waypoint 0 not reached within its allowance (leg 3.0925 s, allowance 3 s)
- `copter_ref` sample 15, sampled NED (0.0807, 0.1424, -0.1162), heading 97.57 deg, start in the air: ordered reach: waypoint 0 not reached within its allowance (leg 3.0300 s, allowance 3 s)
- `copter_ref` sample 16, sampled NED (-0.1264, 0.0290, -0.0715), heading -109.37 deg, start in the air: ordered reach: waypoint 0 not reached within its allowance (leg 3.2625 s, allowance 3 s)
- `copter_ref` sample 25, sampled NED (0.0851, -0.0434, -0.0894), heading -98.45 deg, start in the air: ordered reach: waypoint 0 not reached within its allowance (leg 3.1675 s, allowance 3 s)
- `copter_ref` sample 26, sampled NED (0.1078, -0.0032, -0.1188), heading -64.28 deg, start in the air: ordered reach: waypoint 0 not reached within its allowance (leg 3.0275 s, allowance 3 s)
- `copter_ref` sample 27, sampled NED (-0.1026, 0.1020, -0.0845), heading -97.29 deg, start in the air: ordered reach: waypoint 0 not reached within its allowance (leg 3.1900 s, allowance 3 s)
- `copter_ref` sample 32, sampled NED (0.1319, 0.0856, -0.0326), heading -26.96 deg, start in the air: ordered reach: waypoint 0 not reached within its allowance (leg 3.4925 s, allowance 3 s)
- `copter_ref` sample 34, sampled NED (0.0026, 0.0099, -0.0401), heading -119.02 deg, start in the air: ordered reach: waypoint 0 not reached within its allowance (leg 3.4600 s, allowance 3 s)
- `copter_ref` sample 35, sampled NED (-0.1207, 0.1369, -0.1014), heading -29.25 deg, start in the air: ordered reach: waypoint 0 not reached within its allowance (leg 3.0625 s, allowance 3 s)
- `copter_ref` sample 36, sampled NED (0.0563, -0.0790, -0.0382), heading -85.46 deg, start in the air: ordered reach: waypoint 0 not reached within its allowance (leg 3.4675 s, allowance 3 s)
- `copter_ref` sample 37, sampled NED (-0.1026, -0.1161, -0.0650), heading 18.32 deg, start in the air: ordered reach: waypoint 0 not reached within its allowance (leg 3.2950 s, allowance 3 s)
- `copter_ref` sample 39, sampled NED (0.1433, 0.1243, -0.0254), heading 89.41 deg, start in the air: ordered reach: waypoint 0 not reached within its allowance (leg 3.5350 s, allowance 3 s)
- `copter_ref` sample 40, sampled NED (0.0667, -0.0692, -0.0901), heading 172.29 deg, start in the air: ordered reach: waypoint 0 not reached within its allowance (leg 3.1650 s, allowance 3 s)
- `copter_ref` sample 44, sampled NED (-0.0040, 0.1117, -0.0292), heading 164.06 deg, start in the air: ordered reach: waypoint 0 not reached within its allowance (leg 3.5250 s, allowance 3 s)
- `copter_ref` sample 45, sampled NED (0.1292, 0.1151, -0.0276), heading 31.54 deg, start in the air: ordered reach: waypoint 0 not reached within its allowance (leg 3.5225 s, allowance 3 s)
- `copter_ref` sample 47, sampled NED (0.0837, 0.1390, -0.1219), heading -4.11 deg, start in the air: ordered reach: waypoint 0 not reached within its allowance (leg 3.0075 s, allowance 3 s)
- `copter_ref` sample 48, sampled NED (0.0047, -0.0256, -0.0385), heading 171.85 deg, start in the air: ordered reach: waypoint 0 not reached within its allowance (leg 3.4700 s, allowance 3 s)
- `copter_ref` sample 49, sampled NED (-0.1347, -0.0005, -0.0692), heading 17.63 deg, start in the air: ordered reach: waypoint 0 not reached within its allowance (leg 3.2700 s, allowance 3 s)
- `copter_ref` sample 52, sampled NED (0.0093, -0.0132, -0.1168), heading -110.17 deg, start in the air: ordered reach: waypoint 0 not reached within its allowance (leg 3.0400 s, allowance 3 s)
- `copter_ref` sample 53, sampled NED (0.0826, -0.1413, -0.0701), heading 45.05 deg, start in the air: ordered reach: waypoint 0 not reached within its allowance (leg 3.2625 s, allowance 3 s)
- `copter_ref` sample 61, sampled NED (0.0668, -0.1166, -0.0977), heading -128.94 deg, start in the air: ordered reach: waypoint 0 not reached within its allowance (leg 3.1225 s, allowance 3 s)
- `copter_ref` sample 63, sampled NED (0.0385, -0.0337, -0.0318), heading 67.15 deg, start in the air: ordered reach: waypoint 0 not reached within its allowance (leg 3.5125 s, allowance 3 s)
- `copter_ref` sample 65, sampled NED (0.1281, -0.0603, -0.0438), heading 174.77 deg, start in the air: ordered reach: waypoint 0 not reached within its allowance (leg 3.4225 s, allowance 3 s)
- `copter_ref` sample 66, sampled NED (0.0217, -0.1314, -0.0837), heading 73.64 deg, start in the air: ordered reach: waypoint 0 not reached within its allowance (leg 3.1925 s, allowance 3 s)
- `copter_ref` sample 70, sampled NED (-0.0922, -0.0926, -0.0163), heading 59.68 deg, start in the air: ordered reach: waypoint 0 not reached within its allowance (leg 3.6100 s, allowance 3 s)
- `copter_ref` sample 83, sampled NED (-0.0676, -0.0772, -0.0303), heading -129.44 deg, start in the air: ordered reach: waypoint 0 not reached within its allowance (leg 3.5200 s, allowance 3 s)
- `copter_ref` sample 86, sampled NED (0.1269, 0.0379, -0.0821), heading 18.60 deg, start in the air: ordered reach: waypoint 0 not reached within its allowance (leg 3.2000 s, allowance 3 s)
- `copter_ref` sample 87, sampled NED (-0.1099, 0.0040, -0.0169), heading -93.12 deg, start in the air: ordered reach: waypoint 0 not reached within its allowance (leg 3.6000 s, allowance 3 s)
- `copter_ref` sample 88, sampled NED (0.1440, 0.1342, -0.0532), heading 96.38 deg, start in the air: ordered reach: waypoint 0 not reached within its allowance (leg 3.3550 s, allowance 3 s)
- `copter_ref` sample 90, sampled NED (-0.1289, 0.0770, -0.1017), heading 12.78 deg, start in the air: ordered reach: waypoint 0 not reached within its allowance (leg 3.0375 s, allowance 3 s)
- `copter_ref` sample 91, sampled NED (0.0536, -0.0679, -0.0486), heading -78.24 deg, start in the air: ordered reach: waypoint 0 not reached within its allowance (leg 3.4000 s, allowance 3 s)
- `copter_ref` sample 97, sampled NED (-0.0657, 0.0370, -0.0232), heading 104.03 deg, start in the air: ordered reach: waypoint 0 not reached within its allowance (leg 3.5625 s, allowance 3 s)
- `copter_ref` sample 99, sampled NED (0.0424, 0.0640, -0.0754), heading -136.71 deg, start in the air: ordered reach: waypoint 0 not reached within its allowance (leg 3.2450 s, allowance 3 s)
- `copter_ref` sample 100, sampled NED (-0.0671, -0.0569, -0.0983), heading 143.85 deg, start in the air: ordered reach: waypoint 0 not reached within its allowance (leg 3.1250 s, allowance 3 s)
- `copter_ref` sample 102, sampled NED (-0.1120, 0.0868, -0.0848), heading 54.28 deg, start in the air: ordered reach: waypoint 0 not reached within its allowance (leg 3.1850 s, allowance 3 s)
- `copter_ref` sample 105, sampled NED (0.0378, -0.1448, -0.0481), heading 66.08 deg, start in the air: ordered reach: waypoint 0 not reached within its allowance (leg 3.3925 s, allowance 3 s)
- `copter_ref` sample 109, sampled NED (0.0680, -0.1167, -0.0964), heading -69.72 deg, start in the air: ordered reach: waypoint 0 not reached within its allowance (leg 3.1300 s, allowance 3 s)
- `copter_ref` sample 110, sampled NED (0.0749, -0.0871, -0.0251), heading 152.20 deg, start in the air: ordered reach: waypoint 0 not reached within its allowance (leg 3.5525 s, allowance 3 s)
- `copter_ref` sample 113, sampled NED (0.1454, -0.1268, -0.0777), heading -142.84 deg, start in the air: ordered reach: waypoint 0 not reached within its allowance (leg 3.2175 s, allowance 3 s)
- `copter_ref` sample 115, sampled NED (-0.0004, 0.1384, -0.0316), heading -11.04 deg, start in the air: ordered reach: waypoint 0 not reached within its allowance (leg 3.5025 s, allowance 3 s)
- `copter_ref` sample 116, sampled NED (0.1021, 0.0580, -0.0758), heading 30.13 deg, start in the air: ordered reach: waypoint 0 not reached within its allowance (leg 3.2400 s, allowance 3 s)
- `copter_ref` sample 117, sampled NED (-0.0870, 0.0376, -0.0359), heading -101.09 deg, start in the air: ordered reach: waypoint 0 not reached within its allowance (leg 3.4800 s, allowance 3 s)
- `copter_ref` sample 119, sampled NED (0.0321, 0.1333, -0.0164), heading -88.30 deg, start in the air: ordered reach: waypoint 0 not reached within its allowance (leg 3.5875 s, allowance 3 s)
- `copter_ref` sample 121, sampled NED (-0.1116, -0.0838, -0.1025), heading -29.88 deg, start in the air: ordered reach: waypoint 0 not reached within its allowance (leg 3.0975 s, allowance 3 s)
- `copter_ref` sample 126, sampled NED (-0.0834, 0.1358, -0.0704), heading -0.22 deg, start in the air: ordered reach: waypoint 0 not reached within its allowance (leg 3.2625 s, allowance 3 s)
- `copter_ref` sample 129, sampled NED (-0.0887, -0.1310, -0.1109), heading 56.95 deg, start in the air: ordered reach: waypoint 0 not reached within its allowance (leg 3.0550 s, allowance 3 s)
- `copter_ref` sample 132, sampled NED (-0.1414, 0.0751, -0.0317), heading 7.66 deg, start in the air: ordered reach: waypoint 0 not reached within its allowance (leg 3.4975 s, allowance 3 s)
- `copter_ref` sample 134, sampled NED (-0.1296, -0.0137, -0.0832), heading -163.90 deg, start in the air: ordered reach: waypoint 0 not reached within its allowance (leg 3.1975 s, allowance 3 s)
- `copter_ref` sample 137, sampled NED (0.1268, -0.1106, -0.0514), heading 139.93 deg, start in the air: ordered reach: waypoint 0 not reached within its allowance (leg 3.3700 s, allowance 3 s)
- `copter_ref` sample 139, sampled NED (-0.0834, -0.0089, -0.0836), heading -122.72 deg, start in the air: ordered reach: waypoint 0 not reached within its allowance (leg 3.2000 s, allowance 3 s)
- `copter_ref` sample 143, sampled NED (0.1203, 0.1099, -0.0567), heading 160.85 deg, start in the air: ordered reach: waypoint 0 not reached within its allowance (leg 3.3400 s, allowance 3 s)
- `copter_ref` sample 144, sampled NED (-0.0938, -0.1181, -0.0975), heading 163.53 deg, start in the air: ordered reach: waypoint 0 not reached within its allowance (leg 3.1200 s, allowance 3 s)
- `copter_ref` sample 145, sampled NED (0.0263, 0.0262, -0.1068), heading -47.97 deg, start in the air: ordered reach: waypoint 0 not reached within its allowance (leg 3.0875 s, allowance 3 s)
- `copter_ref` sample 146, sampled NED (0.0262, 0.0802, -0.1186), heading -71.11 deg, start in the air: ordered reach: waypoint 0 not reached within its allowance (leg 3.0300 s, allowance 3 s)
- `copter_ref` sample 147, sampled NED (-0.0997, 0.1397, -0.0551), heading 166.46 deg, start in the air: ordered reach: waypoint 0 not reached within its allowance (leg 3.3475 s, allowance 3 s)
- `copter_ref` sample 148, sampled NED (0.0496, 0.0833, -0.0902), heading -117.77 deg, start in the air: ordered reach: waypoint 0 not reached within its allowance (leg 3.1650 s, allowance 3 s)
- `copter_ref` sample 149, sampled NED (0.0914, 0.0367, -0.0635), heading -143.44 deg, start in the air: ordered reach: waypoint 0 not reached within its allowance (leg 3.3100 s, allowance 3 s)
- `copter_ref` sample 150, sampled NED (0.1333, 0.0759, -0.1216), heading -128.46 deg, start in the air: ordered reach: waypoint 0 not reached within its allowance (leg 3.0075 s, allowance 3 s)
- `copter_ref` sample 154, sampled NED (0.0910, 0.0075, -0.0767), heading -105.35 deg, start in the air: ordered reach: waypoint 0 not reached within its allowance (leg 3.2375 s, allowance 3 s)
- `copter_ref` sample 155, sampled NED (-0.0221, -0.1370, -0.0574), heading -125.71 deg, start in the air: ordered reach: waypoint 0 not reached within its allowance (leg 3.3400 s, allowance 3 s)
- `copter_ref` sample 156, sampled NED (-0.1269, -0.0369, -0.0397), heading 57.51 deg, start in the air: ordered reach: waypoint 0 not reached within its allowance (leg 3.4500 s, allowance 3 s)
- `copter_ref` sample 158, sampled NED (-0.0494, 0.0836, -0.0404), heading 10.83 deg, start in the air: ordered reach: waypoint 0 not reached within its allowance (leg 3.4525 s, allowance 3 s)
- `copter_ref` sample 172, sampled NED (-0.0171, -0.0680, -0.0169), heading -33.23 deg, start in the air: ordered reach: waypoint 0 not reached within its allowance (leg 3.6150 s, allowance 3 s)
- `copter_ref` sample 173, sampled NED (-0.0845, 0.0579, -0.1084), heading -120.70 deg, start in the air: ordered reach: waypoint 0 not reached within its allowance (leg 3.0750 s, allowance 3 s)
- `copter_ref` sample 174, sampled NED (-0.0737, -0.0156, -0.0370), heading 153.20 deg, start in the air: ordered reach: waypoint 0 not reached within its allowance (leg 3.4775 s, allowance 3 s)
- `copter_ref` sample 175, sampled NED (-0.1309, -0.0960, -0.0834), heading 29.18 deg, start in the air: ordered reach: waypoint 0 not reached within its allowance (leg 3.1900 s, allowance 3 s)
- `copter_ref` sample 177, sampled NED (0.1006, -0.0457, -0.0433), heading 25.08 deg, start in the air: ordered reach: waypoint 0 not reached within its allowance (leg 3.4325 s, allowance 3 s)
- `copter_ref` sample 182, sampled NED (0.1184, 0.0837, -0.1076), heading 151.85 deg, start in the air: ordered reach: waypoint 0 not reached within its allowance (leg 3.0750 s, allowance 3 s)
- `copter_ref` sample 184, sampled NED (-0.1335, -0.0190, -0.0262), heading -127.67 deg, start in the air: ordered reach: waypoint 0 not reached within its allowance (leg 3.5400 s, allowance 3 s)
- `copter_ref` sample 189, sampled NED (0.0118, -0.0437, -0.0711), heading -102.92 deg, start in the air: ordered reach: waypoint 0 not reached within its allowance (leg 3.2700 s, allowance 3 s)
- `copter_ref` sample 191, sampled NED (-0.0296, 0.0190, -0.0303), heading -68.60 deg, start in the air: ordered reach: waypoint 0 not reached within its allowance (leg 3.5250 s, allowance 3 s)
- `copter_ref` sample 195, sampled NED (-0.0473, -0.0250, -0.1068), heading -137.50 deg, start in the air: ordered reach: waypoint 0 not reached within its allowance (leg 3.0850 s, allowance 3 s)
- `copter_ref` sample 197, sampled NED (-0.0938, -0.1188, -0.0465), heading -5.95 deg, start in the air: ordered reach: waypoint 0 not reached within its allowance (leg 3.4050 s, allowance 3 s)

## Margins

Over all 200 runs of `copter_ref`.

| margin | min | median | max | bound |
|---|---|---|---|---|
| ceiling clearance (2.0 m minus max altitude) | 40.80 cm | 40.81 cm | 40.81 cm | > 0 |
| max distance to S | 0.00 cm | 0.00 cm | 0.00 cm | = 0 |
| max distance to the path after leaving the box | 5.23 cm | 6.88 cm | 11.16 cm | ≤ 25 cm |
| corridor margin (25 cm minus the above) | 13.84 cm | 18.12 cm | 19.77 cm | ≥ 0 |
| max distance to the path, whole run | 5.26 cm | 12.49 cm | 19.74 cm | (includes the start offset) |
| time of leaving the box | 1.14 s | 2.20 s | 3.03 s |  |
| leg 0 time | 1.69 s | 2.85 s | 3.62 s | ≤ 3 s |
| leg 1 time | 1.93 s | 1.96 s | 2.04 s | ≤ 3 s |
| leg 2 time | 1.83 s | 1.85 s | 1.86 s | ≤ 3 s |
| leg 3 time | 1.84 s | 1.85 s | 1.86 s | ≤ 3 s |
| leg 4 time | 3.61 s | 3.62 s | 3.63 s | ≤ 6 s |
| leg 5 time | 1.85 s | 1.85 s | 1.85 s | ≤ 3 s |
| leg 6 time | 1.85 s | 1.85 s | 1.85 s | ≤ 3 s |
| leg 7 time | 1.85 s | 1.85 s | 1.85 s | ≤ 3 s |
| leg 0 slack | -0.62 s | 0.15 s | 1.31 s | ≥ 0 |
| leg 1 slack | 0.96 s | 1.04 s | 1.07 s | ≥ 0 |
| leg 2 slack | 1.14 s | 1.15 s | 1.17 s | ≥ 0 |
| leg 3 slack | 1.14 s | 1.15 s | 1.16 s | ≥ 0 |
| leg 4 slack | 2.37 s | 2.38 s | 2.39 s | ≥ 0 |
| leg 5 slack | 1.15 s | 1.15 s | 1.15 s | ≥ 0 |
| leg 6 slack | 1.15 s | 1.15 s | 1.15 s | ≥ 0 |
| leg 7 slack | 1.15 s | 1.15 s | 1.15 s | ≥ 0 |
| hold first achieved at | 16.49 s | 17.69 s | 18.42 s | ≤ 27 s |
| hold, best window: max distance to w7 | 2.81 cm | 2.81 cm | 2.82 cm | ≤ 10 cm |
| hold margin (10 cm minus the above) | 7.18 cm | 7.19 cm | 7.19 cm | ≥ 0 |

## Parity

Not compared: one vehicle flown.

## Timing

Machine: arm64, 10 physical cores, 9 workers, Python 3.12.13. Total wall clock 40.4 s for 200 flights (6000 simulated seconds).

| vehicle | flights | simulated s per flight | wall s per flight (loop), median | wall s per flight (with trace file and monitor), median | wall s per simulated s, median |
|---|---|---|---|---|---|
| `copter_ref` | 200 | 30.0025 | 1.739 | 1.768 | 0.0580 |

The per-flight times are measured inside the workers, which run concurrently; a flight's wall clock therefore includes the contention of the other workers.

## Reproduce

```
sim/.venv/bin/python sim/monitor.py --derive-spec     # the spec from sim/out/lean-course-1ms (once)
sim/.venv/bin/python sim/montecarlo.py --vehicles ref --first-accel freefall --no-traces --out out/montecarlo-freefall
```

Outputs in `sim/out/montecarlo-freefall`: summary.csv, samples.json, runs/<lean|ref>-<i>.csv.gz (per tick t, NED position, yaw, the four actuators as float32 hex; not written for this run, --no-traces) and runs/<lean|ref>-<i>.txt (one line per run).
