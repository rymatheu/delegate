# Proposer B log (2026-10-27)

11:14:03 start. Read vcore.py (controller M2, planner R1..R4, vcore.G1/A1/Vw), proposal.py vocabulary, contract.py, example_proposal.py (format only).

Design (propB.py): A1 = u-part of A; A2 = controller mission guards V (leg-2 length in [5,100], waypoints in |.|_inf<=100); G1 = V and (not A1 or core), core = leg 1 in [6,99], |h|<=s-rho-1, |w1|,|w2|<=s-rho, |w2-g|_2<=5/2; G2 = not P or (every y_t in the axis-aligned bounding box of {p0,w1,w2} grown by 1, and some y_t within 1/2 of w2). Difference from the example: G2 uses a bounding box (linear, coarser) instead of a tube around the two segments; rho = 5/4 instead of 1. Reasoning: target = p0 + a d1 + b d2 with a,b in [0,1]; off the polyline only during blend-out by < R/2 = 1, so the box grown by 1 holds; D3 fence needs box growth <= rho; R needs sqrt2 (1/2 + rho) <= 5/2, i.e. rho <= 1.2678.

## Round 1, 11:14:48, rho = 5/4
D1 PASS 0.03 s; D2 PASS 1.52 s; D3 PASS 6.32 s; R PASS (quantified 0.31 s, witness 0.21 s); S 10000/10000. ALL PASS, 8.8 s. No counterexample.

11:15:03 margin sweep launched; env vars passed wrongly (zsh no word split), runs errored; relaunched 11:22:10 with rho in {13/10, 51/40, 507/400, 9/10} plus phase 2 at rho = 5/4.

## Round 2 (margin sweep, phase 1, launched 11:22:10)
- rho = 13/10: D1 PASS, D2 PASS, D3 PASS, R FAIL (quantified 1.05 s, witness FAIL). Corner goal is more than 5/2 from F_{s-rho}.
- rho = 51/40 (1.275): D1/D2/D3 PASS, R FAIL 18.45 s. Counterexample u: s=25, h=(-22,-22), g=(-25.4961, 25.5); fixed-u query "exists w. G1" unsat. Largest failing margin recorded: 51/40.
- rho = 507/400 (1.2675): ALL PASS 9.5 s. Largest passing margin found: 507/400 (bound is (5/2)/sqrt2 - 1/2 = 1.26777).
- rho = 9/10: D3 FAIL 0.67 s, R PASS. Counterexample u: s=26, h=(-22,-22), g=(0,0); w1=(-25, 25.0625), w2=(0,0); p0=(-22,-22), dts all 1: box grown by 1 reaches |y|_inf = 26.0625 > s. So rho >= R_BOX = 1 is needed.

## Round 3, phase 2 at rho = 5/4 (11:22:10 -> 11:22:46)
D1 PASS 0.04 s, D2 PASS 1.78 s, D3 PASS 6.61 s, R PASS (0.31/0.21 s), C1 R4 (deployed) PASS 0.67 s (R1, R2, R3 FAIL, informational), C2 controller PASS 18.85 s (110 paths, 727 queries). ALL PASS, 28.9 s.
Final kept: rho = 5/4 (safe interior of the passing range [1, 1.2677]).
