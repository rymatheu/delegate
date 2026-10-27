# Experimental validation of the delegation algorithm

Everything below is produced by one command, `.venv/bin/python scripts/validate.py` (default `--full`; `--quick` runs a subset in about 90 s). The models are in `scripts/vcore.py`, the experiments, figures and reports in `scripts/validate.py`. Numbers are copied from `notes/validation/results.json` of the full run recorded in `notes/validation/experiment-log.md`; `results.md` is the machine-written summary of the same run.

## 1. What is modelled

**Two instances.** The worked example of Section 6 of `docs/delegation-algorithm.tex` (Euclidean start disc, Euclidean leg lengths, round tube of radius 2) is reproduced as stated, by closed-form computation and sampling (E4). The controller experiments use a *validation instance* with the same fence family and the same structure of A, G, V, P and T, but measured in the infinity norm (start box, leg lengths, tube). The reason is solver capacity, recorded in the log: with Euclidean geometry the corner-blend tube query is out of reach of Z3 5.3.1 within minutes even at two ticks. For an axis-aligned square fence the erosion formula of Section 6 is unchanged by this switch, because the support of a disc and of a square of the same radius agree in the four axis directions; only part (ii) (leg-1 length over all admissible starts) changes from Euclidean to infinity-norm distances, and it stays exact because the start set is now an infinity-norm box.

**Top-level contract (validation instance).** Planner input u = (s, h, g), environment E = (p0, dt_0..dt_{H-1}), output y_0..y_H in R^2.
A := 25 <= s <= 50, |h|_inf <= s-3, |g|_inf <= s+0.5, |p0-h|_inf <= delta, and every dt in [0.9, 1.1] s, with delta = 1 m.
G := at every tick y in F_s = [-s,s]^2, and at some tick |y-g| <= eps, with eps = 3 m (Euclidean disc).
Goals up to 0.5 m outside the fence are allowed by A on purpose: a planner that flies to such a goal really leaves the fence, so revisions R1 and R3 have real defects that the monolithic check must find.

**Controller M2** (`controller` in `scripts/vcore.py`, 34 lines including its docstring, plus the two helpers `le_inf` and `lt_inf`). One function over an arithmetic interface `op` (ite, And, Or, Not, min, max, constants); the same code runs on floats (`Num`), on Z3 terms (`Sym`, one formula) and on the path-splitting interface `Fork` used for bounded model checking. Behaviour, following the ArduPilot facts in `notes/ardupilot/controller-ports.md` in spirit:
- the target starts at p0 and advances along leg 1 (p0 -> w1) and leg 2 (w1 -> w2), stored as leg fractions a, b in [0,1], so y = p0 + a(w1-p0) + b(w2-w1);
- speed cap v_max = 40 m/s, speed change per tick 18 m/s (acceleration cap a_max = 18 m/s^2 at the nominal tick of 1 s), trapezoidal: on leg 2 the target decelerates once v^2/(2 a_max) reaches the remaining class length;
- the per-tick advance is speed x nominal tick / class bound of the leg, where the class bound is the upper end of the leg's 10 m length class (bounded loop over K = 10 classes); this keeps the true speed at or below v_max and makes every leg fraction a rational along every branch;
- fast-waypoint handover: when the rest of leg 1 is shorter than WP_RADIUS R = 2 m (infinity norm), leg 2 starts at once and the rest of leg 1 is blended out over two ticks (halved, then dropped); this is the only source of deviation from the polyline, and it is below R/2;
- guards: a mission is rejected (target holds at p0 for all ticks) unless l_min <= |w2-w1|_inf <= l_max (feeds V), l_min <= |w1-p0|_inf <= l_max (feeds P), and waypoints and start lie in the box |.|_inf <= B = 100 m (upload range check; feeds V and P); l_min = 5 m, l_max = 100 m;
- dt is clamped into [dt_min, dt_max] = [0.5, 1.5] s; a tick whose measured dt the clamp changes is held (no advance), which feeds the dt range of P;
- no loop depends on data: the tick loop runs H times, the class loop K-1 times.

Deviation from ArduPilot, kept on purpose and stated here: kinematics are integrated with the nominal tick length (fixed-rate integration), while ArduPilot integrates with the measured dt. With the measured dt inside the advance, every product of the branch-dependent speed with a coordinate is a nonlinear monomial for the solver, and the single-formula encodings with dt in the advance stayed unknown at 120 s per tick (log, attempts 1-5). Path enumeration was only tried after this change, so whether it would also cope with dt in the advance is not known.

**Vocabulary read from the guards (step 1).** V := l_min <= |w2-w1|_inf <= l_max and |w1|_inf, |w2|_inf <= B. P := l_min <= |w1-p0|_inf <= l_max, |p0|_inf <= B and every dt in [dt_min, dt_max]. T_j := at every tick y lies within infinity-distance rho_j of the polyline p0 -> w1 -> w2, and at some tick |y-w2| <= eta, eta = 0.5 m. The tube atom is written without quantifiers: y is in the rho-neighbourhood (infinity norm) of [a,b] iff y lies in the bounding box of a, b grown by rho and |(y-a) x (b-a)| <= rho(|b_x-a_x| + |b_y-a_y|). rho_1 is the largest infinity-distance to the polyline over 42 fixed test legs (leg-1 lengths 12, 15, 18, 19, 35, 60, 97 m; leg-2 lengths 20, 50 m; turns of 45, 90, 135 degrees) run with dt = 1 s for 30 ticks, rounded down to 0.01 m with a 1e-6 tolerance (the floating-point maximum is 0.9499999999999993, which is 0.95; an earlier version floored it to 0.94); rho_1 = 0.95 m, kappa = 0.05 m, k = 8, so the chain is 0.95, 1.00, ..., 1.30 m.

**Closed-form planner guarantee.** G1 := V and (not A1 or [(ii) and (iii) and (iv)]) with A1 := 25 <= s <= 50, |h|_inf <= s-3, |g|_inf <= s+0.5, and
(ii) l_min + delta <= |w1-h|_inf <= l_max - delta;
(iii) |h|_inf <= s - rho - delta, |w1|_inf <= s - rho, |w2|_inf <= s - rho;
(iv) |w2-g| <= eps - eta.
Bad := A1 and no w meets G1, in closed form |h|_inf > s - rho - delta, or dist(g, F_{s-rho}) > eps - eta. Inside A1, (iii) for h is implied as soon as rho + delta <= 3, so for rho = 1.00 the home conjunct can never fail; Bad is empty iff (0.5 + rho) sqrt(2) <= 2.5, that is rho <= 1.268.

**Planner revisions M1** (`planner` in `scripts/vcore.py`), each a function of u only, with the inward margin m = rho_j*:
- R1: one straight line from h to g, cut at its midpoint (the wire format carries two legs): w1 = (h+g)/2, w2 = g. Decision on the fence: a straight segment between two points of the convex fence stays in the fence, so R1 breaks the fence only when g itself lies outside it (A admits goals up to 0.5 m outside); when h or g is merely near the edge from inside, R1 is safe but G1 rejects it (the tube needs a margin rho). R1 also fails when g is near h (some start makes leg 1 shorter than l_min, and the controller rejects the mission).
- R2: w2 = g clipped into F_{s-m}, w1 = midpoint of h and w2. Fixes the fence; still fails when g is near h.
- R3: R4 with the margin applied with the wrong sign (clip into F_{s+m}): goals up to 0.5 m outside the fence are flown to.
- R4: R2 plus a short-leg branch: if |h-w2|_inf < 12 m = 2(l_min+delta), w1 := h moved 20 m along x towards the centre.

**Decision procedures.** Z3 5.3.1 throughout. Step 2 and the monolithic checks use bounded model checking by exhaustive path enumeration: the code is executed on `Fork`, which splits at every branch whose condition is symbolic, asks Z3 which sides are feasible under the assumptions and the path condition so far, and enumerates all feasible paths depth first; along each path every target is linear in (w, p0) (or in (u, p0) for the composition), and Z3 decides the property atom at every tick (identical target terms at later ticks of the same path are decided once). This is exhaustive over the unrolled code; it is not sampling. Every Z3 call carries the remaining time of its check as a timeout, and a timed-out check is recorded as a timeout, never as a verdict. Monolithic and per-input checks report 'vacuous' if no path is feasible, so an empty assumption cannot pass as an accept.

**Seeds.** Python `random.Random(20261027)` for the sampled inputs and missions of E1; numpy generators with seeds 20261028 (E5 controller sampling), 20261029 (Section 6 Bad check), 20261030 (validation-instance Bad sampling), 20261031 (E4 figure points).

**Timeouts, horizons, workers.** Step 2: 300 s per check; scripted H in {2, 4, 8, 16, 32, 64, 128}. E1 (a): horizon H = 1 (the pointwise lemma needs H >= m = 1; at H = 2 two of sixteen trial queries took 87 s), 120 s per query part. E1 (b): H = 8, the smallest horizon at which step 2 certifies the reach part; 120 s per monolithic check. E3: monolithic checks with u free 600 s, H in {2, 4, 8, 16, 32}. E2 (one horizon per worker) and E1 run at the same time on a pool of 8 worker processes on a 10-core machine, so their times are measured under load. Every E3 time is measured afterwards, one check at a time in the main process with the pool idle (1-minute load average 2.27 before the E3 phase, 1.51 after; nothing else of mine running, no reviewer jobs). E4 and E5 run in the main process.

## 2. Results of the reported run

Full run 4 of 27 Oct 2026, 03:27-03:44 EDT, 1000.2 s wall, all 15 soundness checks pass (`notes/validation/results.json`, `results.md`).

### E1 Soundness of G1 and end-to-end soundness

**(a) Closed-form G1 against Z3.** Setup: 60 pairs (u, w) with the closed-form G1 true, and 60 pairs with A1(u) and V(w) true and exactly one core conjunct of G1 false by a margin between 0.05 and 0.9 m (16 on the leg-1 length (ii), 22 on a waypoint margin (iii), 22 on the goal (iv)); inputs are drawn with a bias towards the fence edge and towards goals near home. For each pair Z3 searches p0, dt_0 and y_0, y_1 (H = 1) with A and A2 and G2 and not G, where G2 = not P or T_{j*} with rho_{j*} = 1.00 m; not G is split into its nine disjuncts (fence side x tick, goal).

| G1 at (u,w) | pairs | unsat | sat | unknown |
|---|---|---|---|---|
| true | 60 | 60 | 0 | 0 |
| false | 60 | 0 | 60 | 0 |

Mean time per pair 2.2 s (true) and 0.63 s (false); slowest pair 44.6 s. What it shows: on these samples the closed form is sound (no counterexample where it accepts) and exact relative to G2 (a counterexample exists wherever it rejects a valid mission). What it does not show: exactness relative to the controller itself (G2 over-approximates M2; see (b)); the home conjunct of (iii) is never exercised because A already gives |h|_inf <= s-3 <= s - rho - delta.

**(b) End to end.** Setup: 60 inputs u (rational, on a 0.25 m grid; biased to the fence edge and to short distances), four planner revisions. Delegated verdict: G1 (closed form, exact rationals) holds at (u, M1(u)) and step 2 certified the controller at H = 8. Monolithic verdict: bounded model checking of M1 at this u followed by M2 over 8 ticks, p0 and dt free under A (fair atom order, see E3); accept iff A and not G is unsatisfiable on every path. Figure `docs/figs/validation/e1_end_to_end.pdf`.

| revision | both accept | delegation rejects, monolithic accepts | both reject | delegation accepts, monolithic rejects |
|---|---|---|---|---|
| R1 | 30 | 6 | 24 | 0 |
| R2 | 42 | 0 | 18 | 0 |
| R3 | 44 | 6 | 10 | 0 |
| R4 | 60 | 0 | 0 | 0 |

No case where delegation accepts and the monolithic check rejects (0 of 240), and no monolithic check was unknown or vacuous. 12 conservative cases (5 % of the pairs), all of one class: the last waypoint w2 = g lies inside the fence but within rho_{j*} = 1.00 m of its edge (for example s = 25, g = (24.5, -1)). G1 asks |w2|_inf <= s - rho because the tube admits targets up to rho beyond w2; the controller stops exactly at w2 and leaves the polyline only inside a corner blend, which cuts towards the inside of the turn, so the real targets stay in the fence. The corner class (a w1 near the fence whose tube sticks out while the blend cuts inward) did not arise, because no revision places w1 near the fence; it is the rejected mission ((0,-49),(40,40)) of Section 6, shown in E4. Monolithic rejections: R1 and R2 at short distances (goal not reached: a leg is shorter than 5 m for some start and the controller holds at p0), R1 and R3 at goals outside the fence (fence broken when the target reaches w2 = g). Mean time of one fixed-input monolithic check: 0.035 s.

### E2 Certification of the controller (step 2)

Setup: M2 and V and P and not T_j, w, p0 and dt free, unrolled over H ticks, decided by exhaustive path enumeration; binary search over the chain 0.95, 1.00, ..., 1.30 m (k = 8: checks j = 8, 4, 2, 1); the reach part does not depend on rho and is checked once per H. Times measured on the 8-worker pool (see above). Figures `e2_certification_time.pdf` (time against H) and `e2_counterexample.pdf`.

| H | reach part | j* (rho) | check j=8 | j=4 | j=2 | j=1 | step 2 total |
|---|---|---|---|---|---|---|---|
| 2 | sat 0.1 s | 2 (1.00) | 2.8 s | 2.7 s | 3.0 s | sat 0.2 s | 8.7 s |
| 4 | sat 0.2 s | 2 (1.00) | 5.4 s | 3.7 s | 3.8 s | sat 0.2 s | 13.3 s |
| 8 | unsat 3.3 s | 2 (1.00) | 5.5 s | 4.6 s | 4.0 s | sat 0.3 s | 17.7 s |
| 16 | unsat 5.6 s | 2 (1.00) | 7.1 s | 6.5 s | 6.2 s | sat 0.5 s | 25.9 s |
| 32 | unsat 10.8 s | 2 (1.00) | 10.7 s | 9.1 s | 8.1 s | sat 0.7 s | 39.4 s |
| 64 | unsat 20.6 s | 2 (1.00) | 16.8 s | 15.8 s | 16.0 s | sat 1.5 s | 70.6 s |
| 128 | unsat 41.0 s | 2 (1.00) | 36.9 s | 35.6 s | 33.1 s | sat 3.5 s | 150.0 s |

Every unsat entry is a certification; no check reached the 300 s limit. There are 110 feasible paths at every H (the controller stops branching once the mission is flown); the time still grows about linearly in H because every tick adds branch checks for the dt clamp on every path. Not in the scripted run (budget): with the earlier chain 0.94 + 0.05(j-1) and the same controller code, step 2 took 384.8 s at H = 256 (run 2) and 1133.8 s at H = 512 (one-off, 600 s per check, j* = 3). At H = 2 and 4 the reach part fails (a mission of two long legs is not finished), so step 2 reports no controller guarantee there and G1 is empty; from H = 8 the controller is certified with j* = 2, rho_{j*} = 1.00 m. rho_1 = 0.95 m fails at every H, consistent with the analytic supremum R/2 = 1 m of the blend, which is not attained. Radius below rho_1: rho = 0.90 m is refuted at tick 2 by a counterexample of deviation 0.967 m (start (79.05, 100), w1 = (79.12, 80.67), w2 = (78.09, 85.67): leg 1 is in the 10-20 m class, the handover happens just under 2 m before w1, and the blend moves the target 0.967 m off the polyline), so the chain is not satisfied trivially.

For the record, the same controller written as one unrolled Z3 formula (no path enumeration) is also decided at small horizons: tube part for rho = 1.00 m unsat in 1.1 s (H = 1), 1.0 s (H = 2), 9.6 s (H = 4); larger H were not tried in the scripted run. For the earlier controller encodings this was not so (unknown at 120 s per tick, log).

### E3 Speed: monolithic against delegated

**The earlier "monolithic times out at 600 s" was an artefact of my encoding, not a monolithic cost.** Runs 1 and 2 posed the property atoms of each path as the fence atom tick by tick from tick 0 and then the goal as one conjunction over all ticks. On some path that conjunction (nine quadratic atoms in s, h, g, p0) is hard for Z3, while a single last-tick query settles the same path at once. A reviewer found this (`notes/validation/checks/review/`, `alt_path.py`, modes `last` and `lastor`). The reported monolithic check (`mono_check(order='fair')`) now uses the same Fork path enumeration and solver settings and changes only how a path's atoms are asked: the fence atoms of all ticks as one disjunction, then the goal for single ticks from the last tick backwards (unsat for one tick settles the path; sound), and only if no single tick settles it the conjunction. The original order is kept and measured as a second check, labelled "original order".

Setup: monolithic = planner revision composed with M2, u, p0 and dt free under A, query A and not G, 600 s limit, for R1-R4 at each H. Step 2 = the binary search of E2 plus the reach check, re-measured here. Planner check = M1 code against the quantifier-free G1 with u free (Z3, no ticks). Fixed u = the monolithic check of R4 at one fixed input, mean over the same 8 inputs. All rows sequential on the idle pool. Figures `e3_time_vs_H.pdf`, `e3_cumulative_R.pdf`, `e3_cumulative_Q.pdf` (single panels) and `e3_cumulative_cost.pdf` (both panels, 7 in).

| H | monolithic R4, fair order | monolithic R4, original order | step 2 | planner check R4 | monolithic R4, one fixed u |
|---|---|---|---|---|---|
| 2 | reject 0.042 s (goal not reachable) | reject 0.042 s | 6.60 s (not certified: reach fails) | 0.339 s | 0.009 s (3 accept, 5 reject) |
| 4 | accept 9.03 s (360 paths) | not run in run 4 (timeout at 600 s in run 2, on the busy pool) | 8.58 s (not certified: reach fails) | 0.384 s | 0.016 s |
| 8 | accept 12.04 s (360 paths) | timeout 600.1 s (64 paths) | 12.66 s (certified) | 0.356 s | 0.025 s |
| 16 | accept 18.52 s (360 paths) | not run in run 4 (timeout in run 2) | 18.54 s (certified) | 0.336 s | 0.046 s |
| 32 | accept 32.20 s (360 paths) | not run in run 4 (timeout in run 2) | 31.70 s (certified) | 0.355 s | 0.093 s |

The original order was run sequentially only at H = 2 and H = 8 because each timeout costs the full 600 s; the H = 4, 16, 32 entries are from run 2, where these checks ran in parallel on the pool and also timed out.

Wrong revisions, u free, fair monolithic check (all reject) and planner check against G1 (all fail):

| H | R1 monolithic | R2 monolithic | R3 monolithic | R1 / R2 / R3 planner check |
|---|---|---|---|---|
| 2 | 0.022 s | 0.057 s | 0.017 s | 0.002 / 0.004 / 0.004 s |
| 4 | 0.027 s | 0.052 s | 0.023 s | 0.004 / 0.004 / 0.006 s |
| 8 | 0.035 s | 0.083 s | 0.031 s | 0.002 / 0.004 / 0.004 s |
| 16 | 0.054 s | 0.117 s | 0.050 s | 0.004 / 0.004 / 0.004 s |
| 32 | 0.095 s | 0.249 s | 0.090 s | 0.002 / 0.004 / 0.005 s |

R1 and R3 are rejected on the fence, R2 on the goal. A wrong revision is cheap to refute on both routes.

**Cost model (measured, no bounds).** The monolithic route pays c_M for every revision it proves and c_M^rej for every revision it refutes; the delegated route pays c_2 once per horizon and c_1 per planner check (c_1^rej for a failing one). With n accepted planner checks sharing one controller certification, delegation is cheaper iff n c_M > c_2 + n c_1, i.e. n > c_2/(c_M - c_1).

| H | c_M (R4 accept) | c_2 | c_1 | break-even n > c_2/(c_M - c_1) | sequence R1, R2, R3, R4: monolithic | delegated |
|---|---|---|---|---|---|---|
| 8 | 12.04 s | 12.66 s | 0.356 s | 1.08 (cheaper from n = 2) | 12.19 s | 13.02 s |
| 16 | 18.52 s | 18.54 s | 0.336 s | 1.02 (from n = 2) | 18.75 s | 18.89 s |
| 32 | 32.20 s | 31.70 s | 0.355 s | 1.00 (from n = 1, by 0.5 %) | 32.63 s | 32.07 s |

The R1..R4 sequence costs, at H = 8, 0.035 + 0.083 + 0.031 + 12.04 = 12.19 s monolithically and 12.66 + 0.002 + 0.004 + 0.004 + 0.356 = 13.02 s delegated: **for the actual sequence of four revisions, of which only one is correct, delegation is slower at H = 8 and H = 16** (by 7 % and 1 %) and about equal at H = 32. The reason is that c_M and c_2 are nearly the same (both are dominated by unrolling the controller over the same paths), and the wrong revisions cost almost nothing on either route. Delegation wins only through amortisation: from the second accepted planner check (or the second query running the same sequence, break-even Q = 1.07 at H = 8) that shares one certification, each further check costs 0.36 s instead of 12 s.

**Plainly: for a single fixed input the monolithic check is much faster.** One fixed-input monolithic check of R4 costs 0.025 s at H = 8, against 12.66 + 0.36 = 13.02 s for step 2 plus one planner check (factor 510; with the same delegated cost of 13.02 s on both sides of the comparison, delegation pays off from about 510 fixed inputs per horizon). The H = 2 fixed-input mean averages 3 accepts and 5 rejects.

**Completeness loss at H = 4.** At H = 4 the fair monolithic check proves R4 composed with M2 correct (accept, 9.03 s, 360 paths; the reviewer's 100,000 concrete runs show no violation at H = 4 and violations at H = 3), but step 2 cannot certify the reach part of T at H = 4: some mission in V (two legs of up to 100 m) is not finished in 4 ticks, so the controller has no guarantee there, G1 is empty and the delegated route rejects a correct system. The planner R4 only emits missions short enough to finish within 4 ticks (inside a 50 m fence), but the controller certification quantifies over every mission in V. This is a loss of completeness of the delegation (not of soundness): delegation can only use what the controller guarantees for all missions in V, and a V that ignores mission length gives nothing below H = 8.

### E4 Geometry of Section 6 and the Bad set

Setup: the Section 6 instance exactly (s = 50, h = (-40,-40), g = (40,40), rho = 2, delta = 1, l_min = 5, l_max = 100, eps = 3, eta = 0.5; Euclidean). Figure `e4_geometry_bad.pdf`: (a) fence, admissible region |w|_inf <= 48 for w1 and w2, the rho-tubes of the accepted mission ((-30,30),(40,40)) and of the rejected mission ((0,-49),(40,40)) with the point (-1.72,-50.02); (b), (c) Bad at s = 50 in the h-plane (g = 0) and in the g-plane (h = 0), shaded from the closed form, with sampled points marked by whether the constructed mission of Section 6 meets G1.
Numbers: the closed form gives G1 true for ((-30,30),(40,40)) and false for ((0,-49),(40,40)) (fence), ((-30,30),(44,40)) (goal) and ((-36,-40),(-36,0)) (leg 1 can be shorter than 5 m for some start). The point (-1.72,-50.02) lies 1.34 m from leg 1 for some admissible start, so inside the tube and outside the fence; the lowest tube point is (0,-51). The closed-form Bad = {|h|_inf > 47} or {dist(g,[-48,48]^2) > 2.5} agrees with the constructed witnesses on 200,000 random inputs (0 mismatches), and random search (2000 missions each) finds no mission for any of 57 inputs predicted Bad. For the validation instance Bad is empty on A (0 of 200,000 sampled inputs), as predicted by rho_{j*} = 1.00 <= 1.268.
What it does not show: E4 reproduces Section 6 by closed form and sampling; the Euclidean instance was not model-checked by Z3 here (the earlier attempt in notes/algorithm/log.md and attempt 1 of the log both time out).

### E5 Two discharge means per delegate

| delegate | means | result | time |
|---|---|---|---|
| planner R4 against (A1, G1) | Z3 on G1 with u free, path enumeration of M1 | pass, 30 paths | 0.34 s |
| planner R4 against (A1, G1) | grid enumeration of u, closed-form G1 (s in 25..50 step 5, h and g on a 1 m grid) | 231,877,100 inputs, 0 failures | 4.2 s |
| controller against (A2, G2) | BMC, E2 | certified rho_{j*} = 1.00 m at H = 8 | 17.7 s (pool), 12.66 s (quiet) |
| controller against (A2, G2) | concrete runs, 40,000 random (w, p0, dt) in V and P, dt uniform in [0.5, 1.5] s, H = 8 | max inf-deviation 0.9997 m <= 1.00 m; 19.9 % of runs leave the polyline; 0 reach failures | 5.9 s |

The two planner means agree. The sampled maximum 0.9997 m is a lower bound on the true supremum and lies between the refuted 0.95 m and the certified 1.00 m; it matches the analytic value R/2 = 1 m. Figure `e5_controller_sampling.pdf` (histogram of the per-run deviation of the runs that leave the polyline). What it does not show: the grid covers a finite set of inputs; sampling certifies nothing (Section 5 of the write-up); only Z3 decides all inputs.

## 3. Where delegation is slower or weaker

1. **One verified revision costs about the same on both routes, and the actual sequence is slower delegated.** With the fair monolithic check, c_M = 12.04 s against c_2 + c_1 = 13.02 s at H = 8 (18.52 against 18.87 s at H = 16; 32.20 against 32.06 s at H = 32). For the sequence R1, R2, R3, R4 delegation costs 13.02 s against 12.19 s monolithic at H = 8. Delegation is cheaper only from the second accepted planner check (or query) sharing one controller certification.
2. **Wrong revisions are cheap on both routes.** The monolithic check refutes R1-R3 in 0.02-0.25 s, so a cost model that charged c_M for every monolithic check (runs 1-2) overstated the monolithic cost.
3. **One fixed input.** The monolithic check of R4 at one fixed input takes 0.009-0.093 s for H = 2..32; delegation is about 510 times slower for a single mission at H = 8.
4. **Completeness loss below the certified horizon.** At H = 4 the monolithic check proves the composite correct while step 2 has no controller guarantee (reach fails over V), so delegation rejects a correct system; at H = 2 both reject (the goal is unreachable).
5. **The earlier speed claim was an encoding artefact.** With the original atom order the monolithic check times out at 600 s at H = 4..32; with the fair order it finishes in 9-32 s. Measured speed belongs to an encoding, not to delegation or to monolithic checking as such.
6. **Conservatism.** 12 of 240 planner outputs (R1 6, R3 6) are rejected by G1 although the composed system meets (A, G). All are waypoint-margin cases (w2 within rho of the fence). G1 is weakest relative to G2, not relative to the controller; a thinner tube is the only repair, and the certified chain cannot go below 1.00 m.
7. **Geometry had to change.** With Euclidean leg lengths, start disc and round tube (the setting of Section 6), Z3 5.3.1 did not certify the corner blend within minutes even at two ticks. The validation instance therefore uses the infinity norm throughout and a controller whose leg fractions are rational along every branch (length classes of 10 m, fixed-rate integration). The algorithm is unchanged, but the certified controller is a simplification of the ArduPilot navigator: speed only reaches v_max for legs at the top of their class, and the measured dt does not enter the motion.
8. **Horizon.** Step 2 grows about linearly with H (150 s at H = 128, 385 s at H = 256, 1134 s at H = 512). The tick count of a real 30 s mission at 400 Hz (about 1.2e4 ticks, Section 5) is far beyond what was run; the validation tick is a coarse 1 s guidance step.
9. **Samples.** E1 inputs are biased to the fence edge and to short distances, so the counts are not population frequencies; E1 (a) tests 120 pairs, not all of U x W.
