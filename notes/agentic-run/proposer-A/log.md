# Proposer A log

- 11:13:52 start. Read vcore.py (controller, planner, contracts), proposal.py, check.py, contract.py, example format.
- 11:15:46 concrete simulation of controller (dt = 1): reaches w2 exactly by tick 7 for 100 m + 100 m legs.
- 11:16:03 round 1: propA_r1.py (hull box with +-1 only on w2's coordinate, exact reach eta = 0; margins |w2| <= s-1, |w1| <= s, |h| <= s-1, |w2-g| <= 3).
- 11:16:12 round 1 phase 1: D1 PASS 0.03 s, D2 PASS 1.43 s, D3 PASS 6.73 s, R PASS (quantified 0.31 s, witness 0.19 s), S 1.0000. No counterexample.
- 11:18:27 round 1 phase 2: C1 R1/R2/R3 FAIL (informational; R1 u=(25,(0,0),(0,0)) gives w1=w2=h, R2 g=(8,8) leg 1 too short, R3 g=(-24.5,-25.5) outside fence kept), C1 R4 PASS 0.62 s (30 paths), C2 TIMEOUT 120 s (377 paths): G2 = box AND (not P or reach) has no y-free top-level disjunct, so every environment incl. held ticks is explored. Lesson: put not P outermost. Round 2 = same sets but box stated only under P.
- 11:19:25 round 2 (propA_r2.py) phase 1: D1 PASS 0.03 s, D2 PASS 1.46 s, D3 PASS 5.82 s, R PASS (0.49 s / witness 0.20 s), S 1.0000. Phase 2: C1 R4 PASS 0.67 s (30 paths), R1-R3 FAIL (informational, as in round 1), C2 PASS 38.82 s (110 paths, 2377 queries). ALL PASS.
- 11:19:37 tightness probe (probe_off099.py, OFF = 99/100, otherwise round 2), C2 only: FAIL 4.01 s. Counterexample w1=(-10.0215, 89.9933), w2=(8.9285, 100), p0=(9.9119, 90), dts all 0.5; blend-tick target y2=(9.9252, 100.0003) is 0.9967 beyond w2x (and beyond max(p0x, w1x)). So the offset 1 is tight up to 1%. Final proposal = propA_r2.py.
