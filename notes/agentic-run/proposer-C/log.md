# Proposer C log

- 11:14:16 start; read README (absent), proposal.py, example_proposal.py (format only), check.py docstring, vcore.py, contract.py, validate.A_f.
- 11:16:25 round 1, proposal_C1.py, phase 1: D1 PASS 0.03 s, D2 PASS 1.36 s, D3 PASS 7.92 s, R PASS (quantified 0.48 s, witness 0.19 s), S 1.0000. No counterexample.
- 11:16:41 round 1, phase 2 (--only C1,C2): C1 R4 PASS 0.51 s (30 paths, margin 1); R1/R2/R3 FAIL (informational; R1 cex s=25 h=g=(0,0) w1=w2=(0,0): leg 1 too short; R2 cex h=(0,0) g=(8,8) w1=(4,4): leg 1 |.|=4 < 6; R3 cex g=(-24.5,-25.5) kept outside s-1); C2 PASS 42.26 s (110 paths, 2377 queries).
- 11:17:29 round 1, full run --phase2: D1 PASS 0.03 s, D2 PASS 1.41 s, D3 PASS 8.00 s, R PASS (0.43 s / 0.19 s), C1-R4 PASS 0.52 s, C2 PASS 42.77 s. summary ALL PASS 53.8 s. Done after 1 round.
