# Figures of the agentic delegation run

Script: `scripts/agentic/figures.py` (run `.venv/bin/python scripts/agentic/figures.py`, about 45 s). Output: `docs/figs/agentic/fig_shapes.pdf`, `fig_regions.pdf`, `fig_sweep.pdf`. Style of `docs/figs/validation`: matplotlib, black and gray, serif, 8 pt, PDF. Every shaded set is computed by calling the proposals' own `A1`, `G1`, `G2` on Python floats over a grid (no formula is re-typed in the script); the targets are `vcore.controller` run on floats (`vcore.Num`).

Proposals used: `scripts/agentic/example_proposal.py` (algorithm, rho = 1), `notes/agentic-run/proposer-A/propA_r2.py`, `notes/agentic-run/proposer-B/propB.py` with rho = 5/4 (B_RHO_NUM = 5, B_RHO_DEN = 4), `notes/agentic-run/proposer-C/proposal_C1.py`.

## fig_shapes.pdf (7 in, four panels)

The region of targets each controller guarantee allows, for one mission, with the controller's actual targets.

- Mission and start: s = 50, h = p0 = (-40, -40), w1 = (-30, 30), w2 = (40, 40), dt_t = 1 for all 8 ticks.
- Shaded: points y with G2(w, (p0, dts), (y, w2)) true, i.e. G2 on a two-tick run whose second target is w2 (w2 lies in every tube and meets every reach part, so this is the tube part alone; every tube is the same at every tick). Grid [-52, 52]^2, step 0.25 m.
- Black dots: y_0..y_8 from `vcore.controller`: (-40, -40), (-37.43, -22), (-32.29, 14), (-30, 30), (10, 35.71), (32, 38.86), (40, 40), (40, 40), (40, 40). Circle: handover tick t = 3, the first tick with |y_t - w1|_inf < R = 2 (the code's handover test while the target is on leg 1). Here leg 1 is finished exactly at the handover tick, so the blend tick has no offset.
- Dashed: the polyline p0, w1, w2. Thick square: the fence [-50, 50]^2.
- Titles: fence margin each G1 requires on w1 and w2: algorithm 1 and 1; A 0 and 1; B 5/4 and 5/4; C 0 and 1.
- Reading: the algorithm keeps a radius-1 tube around both legs; A and B allow the bounding box of p0, w1, w2 (A grown by 1 only beyond w2, B grown by 1 on all sides); C allows the leg-1 box plus the leg-2 box grown by at most 1 on the sides facing p0.

## fig_regions.pdf (7 in, two panels)

The missions each planner guarantee G1 admits, near the fence.

- (a) admissible w2: u = (s, h, g) = (50, (-40, -40), (50, 50)), w1 = (-30, 30); w2 on the grid [46.5, 50.9]^2, step 0.02 m; G1(u, (w1, w2)) evaluated per point. Region areas: algorithm 1.02 m^2, A 2.15, B 0.49, C 2.15 (A and C give the same set: disc of radius 3 around g cut by |w2|_inf <= 49; the algorithm and B use radius 5/2, cut at 49 and 48.75).
- (b) admissible w1: u = (50, (-40, -40), (40, 40)), w2 = g = (40, 40); w1 on the grid [-51.5, -43.5] x [43.5, 51.5], step 0.02 m (the upper-left fence corner). The sets are the squares |w1|_inf <= 50 (A, C), 49 (algorithm), 48.75 (B); the leg-length guards are not active in this window.
- Fills nested from the largest set to the smallest; outlines: algorithm solid, A dashed, B thin solid, C dotted.
- Change from the requested parameters: panel (a) uses g = (50, 50) instead of (40, 40). With g = (40, 40) every disc lies well inside every margin square, so the four sets are two discs (radius 3 for A and C, 5/2 for the algorithm and B) and B coincides with the algorithm; with the goal on the fence corner the margins cut the discs and B is visibly the smallest.

## fig_sweep.pdf (7 in, three panels)

Proposer B's fence margin rho and the two counterexamples that bound it.

- (a) rho from 0.8 to 1.4 m. Values tried and their phase 1 verdicts: 9/10 D3 fail, 1 pass, 5/4 pass, 507/400 pass, 51/40 R fail, 13/10 R fail (from `notes/agentic-run/proposer-B/log.md` and its run files; rho = 1 was not in that log and was run for this figure: `B_RHO_NUM=1 B_RHO_DEN=1 .venv/bin/python scripts/agentic/check.py notes/agentic-run/proposer-B/propB.py`, ALL PASS in 8.3 s). Shaded: [1, 1.2675], the passing interval found. Lower bound: the box grown by 1 must stay in the fence (rho >= 1); upper bound: a corner goal must keep a mission, sqrt(2) (1/2 + rho) <= 5/2, rho <= 1.26777.
- (b) D3 counterexample at rho = 9/10: s = 26, h = p0 = (-22, -22), g = (0, 0), w1 = (-25, 25.0625), w2 = (0, 0), dt = 1. Gray: B's grown box [-26, 1] x [-23, 26.0625]; thick: fence s = 26; dashed: s - rho = 25.1. Inset (vertical scale stretched): the box top at 26.0625 above the fence and the checker's target y_0 = (0, 26.0312), inside the box and outside the fence.
- (c) R counterexample at rho = 51/40: s = 25, g = (-25.4961, 25.5) (h = (-22, -22)). Gray dashed square: |w2|_inf <= s - rho = 23.725; circle: the disc of radius 5/2 around g that G1 requires w2 to lie in. Dotted: g to the corner (-23.725, 23.725), distance 2.5075 m. Inset (about 0.024 m wide): the 0.0075 m gap between the disc and the square.
