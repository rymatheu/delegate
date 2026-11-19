# The sub-contract constants on every Monte Carlo start

A read-only check of the constants of `contracts/Contracts/Mission/Sub.lean` (tuned on the nominal flight `sim/out/lean-course-1ms`) against the 200 uniform starts of `sim/out/montecarlo` and the 56 worst-case starts of `sim/out/montecarlo-worst-case` (box north and east [-0.15, 0.15] m, down [-0.3, 0] m, any heading), one vehicle per start since the two are identical on every tick. Each start was flown again with `copter_ref` (the loop of `sim/montecarlo.py`, recording the state lines); the flown positions and actuator bit patterns equal the recorded runs on every tick for all 256 starts, and the state lines replayed through `copter_ref --exact --trace` give the flown actuators again; the first three trace numbers are the position target after each tick. Ticks 0..12000 of each run. Script: `sim/check_constants.py` (71 s with 9 workers); per start: `constants.csv`.

Definitions as in `Loop.lean` and `Spec.lean`: err = |pos(t) - target(t)| with the target after tick t; the sampled error uses the position of tick t's state line; polyDist is the distance to the polyline through `pathPt` (the takeoff point, then w0..w7, so the climb segment is part of it); `inColumn` is |n|, |e| <= 0.151 m and -0.8 <= d <= 0.001 m (the prism over the box up to w0).

| quantity | constant | min | median | max over runs | holds |
|---|---|---|---|---|---|
| (a) max tracking error err | 9.50 cm | 7.35 cm | 8.27 cm | 8.77 cm | yes |
| (b) max err while the target is in `inColumn` and polyDist > ρ (80 of 256 runs have such ticks) | 3.50 cm | 0.04 cm | 1.08 cm | 1.37 cm | yes |
| (b') as (b), with the distance to the polyline w0..w7 only, without the climb segment (256 of 256 runs) | 3.50 cm | 2.79 cm | 3.50 cm | 4.54 cm | no |
| (c) max target distance to polyline-or-prism (0 inside `inColumn`, else polyDist) | 15.50 cm | 7.14 cm | 7.14 cm | 7.14 cm | yes |
| (d) ticks with the target within rPass = 0.105 m of a waypoint and the vehicle not within r = 0.1 m | 0 | 0 | 0 | 20 (total 682) | no |
| (e) max sampled error \|sampled position - target\| | 9.60 cm | 7.35 cm | 8.27 cm | 8.77 cm | yes |

(d), slack in ticks on each side of each window in which the target is within rPass of a waypoint: before it, the ticks the vehicle was already within r; after it, the ticks it stays within r (a window that runs to the end of the trace together with the vehicle's is not counted on the right). Minimum over runs:

| waypoint | w0 | w1 | w2 | w3 | w4 | w5 | w6 | w7 |
|---|---|---|---|---|---|---|---|---|
| before | 12 | 19 | 21 | 21 | 20 | 21 | 22 | 12 |
| after | 0 | 20 | 20 | 21 | 23 | 19 | 19 | 0 |

- δ = 0.095 m (tracking error): holds; worst 8.77 cm at t = 2.1975 s, worst-case start 12 at NED (0.150, 0.150, 0.000), heading 0.0 deg.
- δ₀ = 0.035 m (climb out of the box): holds; worst 1.37 cm, worst-case start 24 at NED (0.150, -0.150, -0.300), heading 0.0 deg (360 ticks in the condition in that run).
- ρ = 0.155 m (target near the polyline or in the prism): holds; worst 7.14 cm at t = 12.7050 s, worst-case start 49 at NED (-0.150, -0.150, -0.300), heading -135.0 deg.
- rPass = 0.105 m (transfer near the waypoints): VIOLATED in 82 of 256 runs (56 uniform, 26 worst-case), 341 distinct ticks (682 counted per waypoint; by waypoint w0 341, w1 0, w2 0, w3 0, w4 0, w5 0, w6 0, w7 341; w0 and w7 are the same point, so each tick counts for both). All of them are at w0 (= w7) as the vehicle leaves it toward w1, t = 1.7350 to 1.8650 s: the vehicle leaves the 0.1 m ball (up to 11.47 cm from w0) while the target is still within 0.105 m of it (at least 9.10 cm from w0). Entry into each window is fine (slack at least the 'before' row); the failing side is the exit at w0. Most: worst-case start 16 at NED (-0.150, -0.150, -0.300), heading 0.0 deg, 10 ticks. The affected starts are in the air at 0.131 to 0.300 m; no start below 0.131 m and no ground start is affected. At w0 the property would hold on every run with a target radius below 9.10 cm (the target passes through w0 itself on the climb, so w0 does not need the corner allowance that sets rPass above 0.1006 m for w1..w6); at w1..w6 it holds with rPass = 0.105 m.
- δs = 0.096 m (sampled error): holds; worst 8.77 cm, worst-case start 12 at NED (0.150, 0.150, 0.000), heading 0.0 deg; the sampled position is the simulator's position (the state line carries its shortest round-trip decimal), so the sampled error equals err on 256 of 256 runs.
