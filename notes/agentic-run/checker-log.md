# Checker log (scripts/agentic)

## 2026-10-27 10:41:06 EDT start

Read scripts/vcore.py, scripts/validate.py, notes/validation/experiments.md Section 1, docs/algorithm-onepage.tex. Plan: proposal.py (ops dispatching on Z3 vs concrete arguments, tick sequences that record non-pointwise access), check.py (D1, D2, D3, R by Z3 with top-level disjunction splitting; phase 2 by vcore.explore over the planner and controller code). Z3 5.3.1, machine load: load averages: 1.16 1.34 1.37.

## 2026-10-27 11:07:58 EDT phase 1 solver strategy

- D3 on the example at the reduced horizon (y 2 ticks, dts 1 tick, pointwise lemma) split into 448 parts. Plain nlsat (QF_NRA) and the default Z3 solver both returned unknown at 3-5 s on 139 parts; the whole check timed out at 120 s. Diagnosis: the goal parts need the triangle inequality |y-g| <= |y-w2| + |w2-g| with zero slack (eps = eta + (eps - eta)); even the four purely nonlinear conjuncts alone (8 variables) were unknown after 5 s in nlsat.
- Fix 1, linear product abstraction (each product of non-constants a fresh real, squares >= 0): sound refutation, settles the fence parts (the tube bounding box is linear).
- Fix 2, distance lemmas: every dist_sq(a, b) term of the vocabulary gets a real d_ab >= 0; atoms dist_sq ~ k with k a rational square become d_ab ~ sqrt(k) (exact); lemmas |.|_inf <= d <= |.|_1, d >= 0.7071 |.|_1 and the triangle inequality for every triple of points whose three distances occur. With both, D3 PASS in 7.7 s (32 parts linear, 416 by the relaxation).
- R (a): nlqsat (NRA) timed out at 120 s; default solver unknown at 60 s; qe2 cancelled. Fix: bracket the Euclidean atoms of G1 by rational regular n-gons (inner subset, outer superset, checked exactly with Fractions), giving two LRA queries with a universal quantifier (qsat): inner unsat proves R, outer sat refutes it; exact NRA only if both are inconclusive at n = 8, 32, 128. Example: PASS at n = 8 in 0.67 s.
- R (b) witness: PASS 0.20 s. Sample: 10,000/10,000 u from the u-part of A have witness(u) in G1; wide box: 35 of 10,000 in A1, all with a witness.

## 2026-10-27 11:10:48 EDT first runs of the three wrong proposals, phase 2, full horizon

- tests/wrong_d1.py (A1 asks |g|_inf <= s): D1 FAIL 0.02 s, cex s=25 h=(-0.25,-0.5) g=(25.25,25.5), p0=(0,0), dt=0.9; replay A=True A1=False. D3 also FAIL (inputs outside the narrow A1 get G1 = V only), R PASS.
- tests/wrong_d3.py (waypoint margin 0.5 < rho = 1): D3 FAIL 0.87 s, cex s=25.75 h=g=(0,0) w1=(-6,-25) w2=(0,0) p0=(0,0) dt=1, y0=(-7,-26) outside the fence; replay on the full horizon confirmed exactly. D1, D2, R PASS.
- tests/wrong_r.py (leg-1 bounds with l_min/l_max swapped, G1 empty): D1, D2, D3 PASS (vacuous), R (a) FAIL 0.15 s via the outer 8-gon, cex s=50 h=(-47,47) g=(-19.9361,50.5), fixed-u query confirms no mission; R (b) FAIL; sample 0/10,000.
- Phase 2 on the example: C1 R1/R2/R3 FAIL (informational) with counterexamples, R4 PASS 0.60 s (30 paths, as in validate.py); C2 PASS 17.5 s (110 paths, 727 queries; validate.py also reports 110 paths).
- --full-horizon (no pointwise reduction): example D3 PASS 32.7 s (512 parts); wrong_d3 D3 FAIL 3.5 s. Same verdicts as at the reduced horizon.

## 2026-10-27 11:16:18 EDT README written (coordinator deadline)

scripts/agentic/README.md written from the state that works now; check.py interface frozen from here (bug fixes only). tests/test_equiv.py: 35 of 35 self-tests pass in 264 s (strict 128-gon checks take about 51 s each).

## 2026-10-27 11:18:02 EDT recorded runs (default --timeout 120; load average about 2 at start)

### example_proposal.py --phase2 (exit 0, 33.9 s wall)
```
proposal  scripts/agentic/example_proposal.py  (algorithm delegates, rho = 1.00)
instance  H = 8, (A, G) of scripts/validate.py, controller and planners of scripts/vcore.py, Z3 5.3.1, 120 s per check
atoms
  A1  linear
  G1  NONLINEAR (proposal), e.g. (w2x - gx)*(w2x - gx) + (w2y - gy)*(w2y - gy) <= 25/4
  A2  linear
  G2  NONLINEAR (proposal), e.g. (y0x - px)*(w1y - py) - (y0y - py)*(w1x - px) <= 1* (If(w1x - px >= 0, w1x - px, -(w1x - px)) +  If(w1y - py >...
  A   linear
  G   NONLINEAR (top-level contract), e.g. (y0x - gx)*(y0x - gx) + (y0y - gy)*(y0y - gy) <= 9
  WARNING: the proposal has nonlinear atoms in G1, G2; queries with them run in nonlinear real arithmetic (QF_NRA, nlsat; NRA with nlqsat for the quantified R route), which is slower and may return UNKNOWN. Infinity-norm atoms (inf_le, inf_ge, ...) keep a part linear.

phase 1
D1  A <= A1                              PASS         0.03 s
    mode: linear, QF_LRA
    parts: 10, decided by {'linear': 10}
    horizon: dts: 1 of 8 ticks (pointwise class, 0 existential temporal operator(s) in the query)
D2  G1 <= A2                             PASS         1.55 s
    mode: nonlinear, QF_NRA (nlsat)
    parts: 440, decided by {'linear': 232, 'linear relaxation with distance lemmas': 208}
D3  A & G1 & A2 & G2 <= G                PASS         8.16 s
    mode: nonlinear, QF_NRA (nlsat)
    parts: 448, decided by {'linear': 32, 'linear relaxation with distance lemmas': 416}
    horizon: y: 2 of 9 ticks (pointwise class, 2 existential temporal operator(s) in the query)
    horizon: dts: 1 of 8 ticks (pointwise class, 1 existential temporal operator(s) in the query)
R   (a) quantified: A1 & forall w. ~G1   PASS         0.65 s
    mode: nonlinear G1/A1 bracketed by linear 8-gons: inner approximation of G1 realizable (LRA, qsat): it is a subset of G1, so R holds
R   (b) witness: A1(u) -> G1(u, witness(u)) PASS         0.21 s
    mode: nonlinear, QF_NRA (nlsat)
    parts: 31, decided by {'linear': 30, 'full part': 1}
R   verdict                              PASS     (PASS if either route proves it; FAIL only on a quantified counterexample u; a failing witness alone leaves R open)
S   non-vacuity sample                   INFO         0.35 s   (witness(u), concrete floats)
    u drawn from the u-part of A: 10000 draws, 10000 in A1, 10000 with a witness (1.0000)
    u drawn from a wide box, kept if in A1: 10000 draws, 35 in A1, 35 with a witness (1.0000)

phase 2
C1  planner R1 against (A1, G1) [informational] FAIL         0.01 s
    mode: nonlinear
    paths: 1
    counterexample:
      u: s=25 h=(0, 0) g=(0, 0)
      w: w1=(0, 0) w2=(0, 0)
      replay: G1(u, M1(u)) evaluated exactly: False
C1  planner R2 against (A1, G1) [informational] FAIL         0.01 s
    mode: nonlinear
    paths: 1
    counterexample:
      u: s=25 h=(0, 0) g=(8, 8)
      w: w1=(4, 4) w2=(8, 8)
      replay: G1(u, M1(u)) evaluated exactly: False
C1  planner R3 against (A1, G1) [informational] FAIL         0.01 s
    mode: nonlinear
    paths: 1
    counterexample:
      u: s=25 h=(-13, -14) g=(-24.5, -25.5)
      w: w1=(7, -14) w2=(-24.5, -25.5)
      replay: G1(u, M1(u)) evaluated exactly: False
C1  planner R4 against (A1, G1) [deployed] PASS         0.66 s
    mode: nonlinear atoms; default Z3 solver, incremental on each path condition
    paths: 30
    margin: 1
C2  controller M2 against (A2, G2), H=8  PASS        22.06 s
    mode: nonlinear atoms; default Z3 solver, incremental on each path condition
    paths: 110
    queries: 727
    note: runs restricted to not E, E = the 1 disjunct(s) of G2 that do not mention y (G2 holds whenever E does)

summary: ALL PASS   total 33.8 s   (D1 PASS, D2 PASS, D3 PASS, R PASS, C1-R4 PASS, C2 PASS)
```

### tests/wrong_d1.py (exit 1)
```
phase 1
D1  A <= A1                              FAIL         0.03 s
    mode: linear, QF_LRA
    parts: 7, decided by {'linear': 7}
    horizon: dts: 1 of 8 ticks (pointwise class, 0 existential temporal operator(s) in the query)
    counterexample:
      u: s=25 h=(-0.25, -0.5) g=(25.25, 25.5)
      e: p0=(0, 0) dts=[0.9, 0.9, 0.9, 0.9, 0.9, 0.9, 0.9, 0.9]
      replay: confirmed exactly on the full horizon: A=True, A1=False
D2  G1 <= A2                             PASS         2.29 s
    mode: nonlinear, QF_NRA (nlsat)
    parts: 456, decided by {'linear': 248, 'linear relaxation with distance lemmas': 208}
D3  A & G1 & A2 & G2 <= G                FAIL         0.43 s
    mode: nonlinear, QF_NRA (nlsat)
    parts: 1, decided by {'linear': 1}
    horizon: y: 2 of 9 ticks (pointwise class, 2 existential temporal operator(s) in the query)
    horizon: dts: 1 of 8 ticks (pointwise class, 1 existential temporal operator(s) in the query)
    counterexample:
      u: s=50 h=(46.75, -47) g=(-50.25, -50.5)
      w: w1=(52.5, -41.25) w2=(100, 0)
      e: p0=(47.75, -46) dts=[0.9, 0.9, 0.9, 0.9, 0.9, 0.9, 0.9, 0.9]
      y: [(-50.25, -50.25), (0, 0), (0, 0), (0, 0), (0, 0), (0, 0), (0, 0), (0, 0), (0, 0)]
      note: y repeated from the last solved tick to 9 ticks
      replay: confirmed exactly on the full horizon: A=True, G1=True, A2=True, G2=True, G=False
R   (a) quantified: A1 & forall w. ~G1   PASS         0.48 s
    mode: nonlinear G1/A1 bracketed by linear 8-gons: inner approximation of G1 realizable (LRA, qsat): it is a subset of G1, so R holds
R   (b) witness: A1(u) -> G1(u, witness(u)) PASS         0.28 s
    mode: nonlinear, QF_NRA (nlsat)
    parts: 44, decided by {'linear': 43, 'linear relaxation with distance lemmas': 1}
R   verdict                              PASS     (PASS if either route proves it; FAIL only on a quantified counterexample u; a failing witness alone leaves R open)
S   non-vacuity sample                   INFO         0.43 s   (witness(u), concrete floats)
    u drawn from the u-part of A: 10000 draws, 9740 in A1, 9740 with a witness (1.0000)
    u drawn from a wide box, kept if in A1: 10000 draws, 35 in A1, 35 with a witness (1.0000)

summary: NOT ALL PASS   total 4.0 s   (D1 FAIL, D2 PASS, D3 FAIL, R PASS)
```

### tests/wrong_d3.py (exit 1)
```
phase 1
D1  A <= A1                              PASS         0.03 s
    mode: linear, QF_LRA
    parts: 10, decided by {'linear': 10}
    horizon: dts: 1 of 8 ticks (pointwise class, 0 existential temporal operator(s) in the query)
D2  G1 <= A2                             PASS         1.55 s
    mode: nonlinear, QF_NRA (nlsat)
    parts: 440, decided by {'linear': 232, 'linear relaxation with distance lemmas': 208}
D3  A & G1 & A2 & G2 <= G                FAIL         0.91 s
    mode: nonlinear, QF_NRA (nlsat)
    parts: 27, decided by {'linear': 8, 'linear relaxation with distance lemmas': 18, 'full part': 1}
    horizon: y: 2 of 9 ticks (pointwise class, 2 existential temporal operator(s) in the query)
    horizon: dts: 1 of 8 ticks (pointwise class, 1 existential temporal operator(s) in the query)
    counterexample:
      u: s=25.75 h=(0, 0) g=(0, 0)
      w: w1=(-6, -25) w2=(0, 0)
      e: p0=(0, 0) dts=[1, 1, 1, 1, 1, 1, 1, 1]
      y: [(-7, -26), (0, 0), (0, 0), (0, 0), (0, 0), (0, 0), (0, 0), (0, 0), (0, 0)]
      note: y repeated from the last solved tick to 9 ticks
      replay: confirmed exactly on the full horizon: A=True, G1=True, A2=True, G2=True, G=False
R   (a) quantified: A1 & forall w. ~G1   PASS         0.27 s
    mode: nonlinear G1/A1 bracketed by linear 8-gons: inner approximation of G1 realizable (LRA, qsat): it is a subset of G1, so R holds
R   (b) witness: A1(u) -> G1(u, witness(u)) PASS         0.21 s
    mode: nonlinear, QF_NRA (nlsat)
    parts: 31, decided by {'linear': 30, 'full part': 1}
R   verdict                              PASS     (PASS if either route proves it; FAIL only on a quantified counterexample u; a failing witness alone leaves R open)
S   non-vacuity sample                   INFO         0.36 s   (witness(u), concrete floats)
    u drawn from the u-part of A: 10000 draws, 10000 in A1, 10000 with a witness (1.0000)
    u drawn from a wide box, kept if in A1: 10000 draws, 35 in A1, 35 with a witness (1.0000)

summary: NOT ALL PASS   total 3.4 s   (D1 PASS, D2 PASS, D3 FAIL, R PASS)
```

### tests/wrong_r.py (exit 1)
```
phase 1
D1  A <= A1                              PASS         0.03 s
    mode: linear, QF_LRA
    parts: 10, decided by {'linear': 10}
    horizon: dts: 1 of 8 ticks (pointwise class, 0 existential temporal operator(s) in the query)
D2  G1 <= A2                             PASS         1.54 s
    mode: nonlinear, QF_NRA (nlsat)
    parts: 440, decided by {'linear': 232, 'linear relaxation with distance lemmas': 208}
D3  A & G1 & A2 & G2 <= G                PASS         7.87 s
    mode: nonlinear, QF_NRA (nlsat)
    parts: 448, decided by {'linear': 32, 'linear relaxation with distance lemmas': 416}
    horizon: y: 2 of 9 ticks (pointwise class, 2 existential temporal operator(s) in the query)
    horizon: dts: 1 of 8 ticks (pointwise class, 1 existential temporal operator(s) in the query)
R   (a) quantified: A1 & forall w. ~G1   FAIL         0.16 s
    mode: nonlinear G1 bracketed by linear 8-gons: outer approximation of G1 (a superset) has no mission at this u (LRA, qsat)
    counterexample:
      u: s=50 h=(-47, 47) g=(-19.9361, 50.5)
      replay: fixed-u query "exists w. G1(u, w)": unsat (confirmed: no mission); A1(u)=True
R   (b) witness: A1(u) -> G1(u, witness(u)) FAIL         0.14 s
    mode: nonlinear, QF_NRA (nlsat)
    parts: 14, decided by {'linear': 14}
    counterexample:
      u: s=25 h=(-12.5, -22) g=(-24.5, -10)
      w: w1=(-18.25, -16) w2=(-24, -10)
      replay: witness(u) evaluated exactly: A1=True, G1=False
R   verdict                              FAIL     (PASS if either route proves it; FAIL only on a quantified counterexample u; a failing witness alone leaves R open)
S   non-vacuity sample                   INFO         0.35 s   (witness(u), concrete floats)
    u drawn from the u-part of A: 10000 draws, 10000 in A1, 0 with a witness (0.0000); first without: s=28.8251 h=(15.918, -15.9774) g=(-18.3231, -23.3936)
    u drawn from a wide box, kept if in A1: 10000 draws, 35 in A1, 0 with a witness (0.0000); first without: s=49.4173 h=(-34.4249, -37.7262) g=(-25.9773, 40.9358)

summary: NOT ALL PASS   total 10.2 s   (D1 PASS, D2 PASS, D3 PASS, R FAIL)
```

### tests/wrong_c2.py --phase2 (exit 1; tube 0.90 m in G2, phase 1 passes, C2 fails)
```
C2  controller M2 against (A2, G2), H=8  FAIL         2.49 s
    paths: 11
    queries: 56
    note: runs restricted to not E, E = the 1 disjunct(s) of G2 that do not mention y (G2 holds whenever E does)
    counterexample:
      w: w1=(0, 0) w2=(0, -5)
      e: p0=(19.3333, 0) dts=[0.5, 0.5, 0.5, 0.5, 0.5, 0.5, 0.5, 0.5]
      y: [(19.3333, 0), (1.9333, 0), (0.9667, -5), (0, -5), (0, -5), (0, -5), (0, -5), (0, -5), (0, -5)]
      replay: controller re-run on these values, G2 evaluated exactly: False

summary: NOT ALL PASS   total 14.2 s   (D1 PASS, D2 PASS, D3 PASS, R PASS, C1-R4 PASS, C2 FAIL)
```

C2 counterexample: y_2 = (0.9667, -5) is 0.9667 m from the leg w1 -> w2 (x = 0), > 0.90; the same blend deviation (0.967 m) as validate.py's refutation of rho = 0.90.

## 2026-10-27 11:18:13 EDT done

README status updated (wrong_c2 added, timings of the recorded run). Files: scripts/agentic/{proposal.py, contract.py, example_proposal.py, check.py, README.md}, scripts/agentic/tests/{test_equiv.py, wrong_d1.py, wrong_d3.py, wrong_r.py, wrong_c2.py}. scripts/validate.py, scripts/vcore.py, docs/ and notes/validation/ untouched.
