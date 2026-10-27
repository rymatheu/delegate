# Delegate checker (scripts/agentic)

Checks a proposed contract delegate for the stack planner M1 -> controller M2 of `scripts/vcore.py`, against the top-level contract (A, G) of `scripts/validate.py`. Use the interpreter `.venv/bin/python` (Z3 5.3.1).

## Run

```
.venv/bin/python scripts/agentic/check.py <proposal.py>                  # phase 1: D1, D2, D3, R, sample
.venv/bin/python scripts/agentic/check.py <proposal.py> --phase2         # + C1 (planners R1..R4), C2 (controller)
  options: --timeout S (seconds per check, default 120)   --only D1,D2,D3,R,S,C1,C2   --full-horizon (no tick reduction)
```
Exit status 0 iff every counted check printed PASS. Measured on `example_proposal.py` (idle 10-core machine): D1 0.03 s, D2 1.3 s, D3 7.7 s, R(a) 0.7 s, R(b) 0.2 s, sample 0.3 s (phase 1 about 10 s); C1 R4 0.6 s, C2 17.5 s. `--full-horizon` D3: 33 s.

## Writing a proposal

A Python file defining four functions, built only from `scripts/agentic/proposal.py` (read its docstring):

| function | argument shapes | meaning |
|---|---|---|
| `A1(u)` | `u = U(s, h, g)`, `h = (hx, hy)`, `g = (gx, gy)` | planner assumption |
| `G1(u, w)` | `w = W(w1, w2)`, `w1 = (w1x, w1y)`, `w2 = (w2x, w2y)` | planner guarantee |
| `A2(w)` | | controller assumption |
| `G2(w, e, y)` | `e = E(p0, dts)`, `p0 = (px, py)`, `dts` = Ticks of H = 8 tick lengths, `y` = Ticks of H+1 = 9 targets `(x, y)` | controller guarantee |

Optional: `witness(u)` returning `(w1, w2)` (a mission for every u in A1; route (b) of R and the sample), `NAME` (string), `PLANNER_MARGIN` (inward margin m passed to the planner revisions, default 1), `PLANNER_REVISION` (the revision whose C1 result counts, default 4).

Operations: `And, Or, Not, Implies, Ite, Abs, Max, Min`, `+ - *`, comparisons, `Q(a, b)` exact rational, points `sub, add, scale, mid, cross, dot`, norms `ninf` (infinity norm term), `nsq`, `dist_inf`, `dist_sq` (squared Euclidean distance), linear infinity-norm atoms `inf_le, inf_lt, inf_ge, inf_gt` (|v|_inf <= c etc.), `in_box`, `near_segment_inf(p, a, b, r)` (p within inf-distance r of segment [a, b]), temporal `Box(seq, f)` (f at every tick), `Diamond(seq, f)` (f at some tick), `seq` = `y` or `e.dts`. Never use Python `and/or/not/if`, chained comparisons, `abs/max/min` or `math` on arguments: the same function runs on Z3 terms and on numbers. `vc_op(...)` gives a `scripts/vcore.py` arithmetic interface so vcore functions can be called. Start from `example_proposal.py` (the algorithm's own delegates) and see `tests/wrong_*.py` for small edits of it.

Speed: prefer `inf_*` atoms (linear). Products (`cross`, `dot`, `nsq`, `dist_sq`) make a query nonlinear; the checker warns and names the solver mode. Write Euclidean bounds as `dist_sq(a, b) <= c * c` with c a rational constant: the checker then uses exact distance variables, the triangle inequality and polygon brackets, and stays linear.

## Conditions checked

Phase 1 (Z3, u, w, e, y free):
- D1 `A <= A1`; D2 `G1 <= A2`; D3 `A & G1 & A2 & G2 <= G`.
- R: for every u in A1 some w with G1(u, w). (a) quantified query `A1(u) & forall w. not G1(u, w)`: linear G1 by LRA (qsat); Euclidean atoms bracketed by inner/outer rational n-gons (n = 8, 32, 128; inner realizable proves R, outer unrealizable refutes it), else NRA (nlqsat). (b) `A1(u) -> G1(u, witness(u))` quantifier-free. R is PASS if either route proves it, FAIL only on a counterexample u from (a) (confirmed by a fixed-u query); a failing witness alone gives UNKNOWN.
- S (information only): fraction of 10,000 random u (uniform on the u-part of A, and on a wide box filtered by A1) for which `G1(u, witness(u))` holds, in floats.

Horizon for D1/D3: if every formula uses y and dts only through Box/Diamond over all ticks with bodies looking at their own tick (pointwise class), the checker solves over k ticks, k = number of existential temporal operators in the query (Diamonds in positive, Boxes in negative position), at least 1: a satisfying run of H ticks restricts to its witness ticks and a short run extends by repeating a tick. The output prints the horizon used and why. Indexing (`y[-1]`), iteration, `ticks=` windows or nesting force full unrolling (H+1 = 9 targets, 8 tick lengths). Counterexamples are extended to the full horizon and replayed exactly.

Phase 2 (`--phase2`):
- C1: each planner revision R1..R4 (`vcore.planner`, margin `PLANNER_MARGIN`) with u symbolic under A1, every feasible path of the planner code enumerated (`vcore.explore`), `not G1(u, M1(u))` asked per path. Only `PLANNER_REVISION` counts for the exit status; the others are informational (R1..R3 are known defective and FAIL on the example).
- C2: controller M2 (`vcore.controller`) over H = 8 ticks with w, p0, dts free under A2, every feasible path enumerated, `not G2` asked per path and tick. The y-free disjuncts E of G2 (e.g. `not P`) make G2 true by themselves, so runs are restricted to `not E`.

## Reading the output

Each line: check, PASS / FAIL / UNKNOWN / TIMEOUT, seconds; then the solver mode, number of parts the query was split into (top-level disjunctions) and how they were decided, the horizon, and for FAIL a counterexample (u: s, h, g; w: w1, w2; e: p0, dts; y) with a replay line (`confirmed exactly` = the proposal's own functions, evaluated on exact rationals, agree). TIMEOUT/UNKNOWN is never a verdict: simplify atoms (linear) or raise `--timeout`.

## Instance parameters

H = 8. A: 25 <= s <= 50, |h|_inf <= s - 3, |g|_inf <= s + 1/2, |p0 - h|_inf <= 1 (delta), every dt in [9/10, 11/10]. G: every y_t in the fence [-s, s]^2 and some |y_t - g| <= 3 (eps, Euclidean). Controller (vcore.CTRL): v_max 40, a_max 18, nominal tick 1, WP radius R = 2, l_min 5, l_max 100, length classes D = 10, K = 10, dt clamp [1/2, 3/2], box B = 100. Guards: V = l_min <= |w2 - w1|_inf <= l_max, |w1|_inf, |w2|_inf <= B; P = l_min <= |w1 - p0|_inf <= l_max, |p0|_inf <= B, every dt in [1/2, 3/2]. Certified tube rho = 1.00 at H = 8, reach radius eta = 1/2.

## Status

Tested: `example_proposal.py --phase2` passes everything (exit 0, 34 s wall: D1 0.03, D2 1.6, D3 8.2, R(a) 0.65, R(b) 0.21, S 0.35, C1 R4 0.66, C2 22 s under load 2). `tests/test_equiv.py`: 35 of 35 self-tests pass (the example and the contract equal the vcore/validate formulas, polygon brackets, pointwise detection; about 4.5 min). Wrong proposals, each caught with a counterexample that is confirmed exactly: `tests/wrong_d1.py` (D1), `tests/wrong_d3.py` (D3, waypoint margin 0.5 < rho), `tests/wrong_r.py` (G1 empty, R), `tests/wrong_c2.py` (tube 0.90 m, phase 1 passes, C2 fails at tick 2). Runs are recorded in `notes/agentic-run/checker-log.md`.
