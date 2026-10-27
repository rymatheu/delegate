# Theory review log

## Mon Oct 26 23:58:15 EDT 2026 -- start
Start stamp of the review session: Mon Oct 26 23:55:30 EDT 2026. Read docs/delegation-algorithm.tex, notes/algorithm/log.md, notes/algorithm/checks/Deleg.lean and pointwise.py, lean/Contracts.lean and Hiding.lean, book Sections VII-A and VIII-E (Algorithm 1), and the two literature surveys (quotient and weakest-assumption sections).

## Tue Oct 27 00:03:24 EDT 2026 -- first pass over the soundness claims
F0-F4 re-proved by hand (all need Omega to be a product over ports; F3/F4 need C over Pi minus X; every use in the proof satisfies it). Theorem (a)-(f) re-proved. Findings so far:
- The 'Hence G1 nonempty iff ...' paragraph is true but vacuous: G1 contains V x (not A1), so G1 is nonempty whenever V is nonempty and A1 is not everything (in the example s<=0). The informative test is A1 cap G1 nonempty, or Bad empty.
- Strict D2 (G1 sub A2) is what forces P out of A2; the side condition of rule_general (A cap G1 sub A2) would not. Moving P to G2 is equivalent to using the weaker side condition.
- (A1,G1) has exactly the implementations over U cup W of the AG quotient (A,G)/(A2,G2) (closed form of Incer et al. 2018), i.e. G1 cup not A1 = forall_{E cup Y}(not A cup (A2 cap (not G2 cup G))). Equivalently the weakest assumption (Giannakopoulou et al. 2002) of the most permissive implementation not A2 cup G2.
- Deadline conversion is sound only for positive Diamond windows in G; Box windows in G and any window in A need the opposite rounding.
- Worked example: P keeps the code's dt range 1/2000..1/50, so the reach part of T cannot be certified over 1.2e4 ticks for 100 m legs (6 v metres of travel at dt=1/2000); inconsistent with the cost paragraph's own advice.
- Pointwise class requires every window to be [0,H]; a deadline shorter than H leaves the class.

## Tue Oct 27 00:08:23 EDT 2026 -- Lean check compiled
notes/validation/Deleg.lean compiles with `cd lean && lake env lean /Users/ryan/Research/delegate/notes/validation/Deleg.lean` (exit 0, no sorry, no warnings; #print axioms shows only propext, Classical.choice, Quot.sound). Covers D1, D2, D3+, (c) with and without the hidden wire, (d), (e), (f) as an iff with a total relation and with a function (needs Nonempty W), chain monotonicity and the up-set, quotient identity (planner_iff_quotient, saturated_G1; needs Nonempty Y), exact inlined guarantee G1x and G1 sub V cap G1x, inlining recovers the exact quotient, maximality under the weak side condition, pointwise lemma (box_iff with m <= H, dia_iff with m <= H+1) and a counterexample for H < m, deadline conversion with Box/Diamond polarity, D3+ as the tightening side condition after AG.rule_general, and the typed construction lifted into the library.
New finding from the Lean work: the Diamond half of the pointwise lemma only needs H >= m-1; only the Box half needs H >= m.
New finding: initial internal state of M2 (S-curve state, previous target, vehicle velocity at tick 0) is not a port; BMC from one initial state certifies only that state.

## Tue Oct 27 00:09:49 EDT 2026 -- conservatism computed
Scratch script (scratchpad gap.py): two legs with a 90-degree-ish corner at the lowest vertex, inward circular blend of length L. rho_min = 0.3L, cut depth in the facet direction = 0.5L; G1 at rho = rho_min demands margin rho_min inside the fence, the exact quotient tolerates the vertex 0.5L outside; gap = rho_min + cut = 0.8L, about 2.7 rho_min. The gap does not vanish as rho -> rho_min: it is a shape gap, not a width gap.
arXiv MCP rate-limited (HTTP 429) on first attempt; references so far taken from the existing survey plus my own knowledge; retry later.

## Tue Oct 27 00:14:14 EDT 2026 -- critique drafted; side conditions of the lemma separated by brute force
notes/validation/theory-critique.md written (findings 1.1-5.2, corrections list). Scratch pw2.py (6000 random cases on a 4-value tick domain): Box half 0 disagreements with H>=m, 205/2229 with H<m; Diamond half 0 disagreements with H+1>=m, 33/1138 with H+1<m. Confirms the Lean result: Diamond needs only H >= m-1.

## Tue Oct 27 00:16:47 EDT 2026 -- literature confirmed; major finding on Pacti
arXiv: Pacti (2303.17751) and Hypercontracts (2106.02449) confirmed (authors, titles). Searched the Pacti text: quotient formula (a and (not a' or g'), (a' and g) or not a or (a' and not g')) matches mine; ContractQuotient types the missing component with I^q = (O' minus O) cup (I minus I') and O^q = (O minus O') cup (I' minus I), eliminating other variables by context-aided elimination (UCB/EECS-2023-15). For this architecture I^q = U and O^q = W: steps 3-4 are Pacti's IO quotient with exact real QE in place of polyhedral refinement and with temporal formulas. Pacti cites Incer et al. MEMOCODE 2018 (pp. 67-77, DOI 10.1109/MEMCOD.2018.8556872), confirming that reference. Finding 2.1 and 2.4 updated.

## Tue Oct 27 00:17:50 EDT 2026 -- two more findings
1.19: per-tick U coupling mechanism is elimination of static E_s ports (example: covering of R by intervals [v_t,u_t] yields atoms u_1 >= v_2). 1.20: decidability of step 2 'over the reals' fails for transcendental library calls (atan2, sin, cos; Richardson 1968); suggest inductive-invariant certification of the Box part of T and a progress measure for the reach part, removing H from step 2. Corrections list renumbered (16 items).

## Tue Oct 27 00:18:37 EDT 2026 -- exact vs G1 on the example's rejected mission
Scratch inst.py: toy inward-arc controller on ((0,-49),(40,40)), s=50, h=(-40,-40), 73 starts on the unit circle around h, blend L in {0.5,1,2,3}: max |target|_inf 48.91..48.49 < 50, so the exact quotient accepts while G1 (rho=2) rejects. At L=3, rho_min ~ 0.83 and the residual shape gap at rho=rho_min is 49.83-48.49 = 1.34 m = rho_min + 0.51 m cut. Added to Finding 4.2.

## Tue Oct 27 00:19:25 EDT 2026 -- correction to my own Finding 1.9
I had called 'move P into G2' equivalent to 'keep P in A2 under the weak side condition'. Not quite: Lean G1alt_sub / G1_sub_alt show G1alt is contained in G1 on A1, with equality only when every allowed (u,e) admits a target outside G. Finding 1.9 and correction 11 rewritten. Deleg.lean recompiled, exit 0.

## Tue Oct 27 00:20:31 EDT 2026 -- major finding: reach part of T is closed-loop
Read ardupilot/libraries/AC_WPNav/AC_WPNav.cpp lines 557-655: progress scalar 0.05 + (v_est.dir - kP*pos_err.dir)/|v_tgt| clamped to [0,1], and non-fast waypoint handover requires the position estimate within the waypoint radius. With E_d free (as in step 2) the target can stall forever, so the reach conjunct of every T_j fails in step 2 regardless of rho. Needs a tracking bound relating E_d and Y, i.e. P over W cup E cup Y and A mentioning Y. Added Finding 1.21 and correction 4 (list now 17 items).

## Tue Oct 27 00:20:51 EDT 2026 -- initial state confirmed in the source
AC_WPNav.cpp lines 252-255: origin of the first leg = stopping point from position and velocity estimates at init. Added to Finding 1.5(iii): p0 must be the stopping point or A must bound the initial speed.

## Tue Oct 27 00:21:27 EDT 2026 -- window mismatch is unsound, not just out of class
Lean dia_window_mismatch: H=1, alpha=top, gamma=d={true}, antecedent Diamond over 0..1, consequent deadline at tick 0: the pointwise condition holds but (false,true) violates. Finding 1.10 now says applying the formula with a shorter deadline is unsound. Compiles, exit 0.

## Tue Oct 27 00:22:01 EDT 2026 -- finite-model cross-check
Scratch finite.py, 3000 random finite models (ports with 1-3 values): 0 disagreements for planner-vs-quotient implementation (15000 sampled planners), G1 sub V cap G1x under certification, Bad empty iff total planner, and the Hence reading under its hypothesis; without the hypothesis the reading is wrong in 242/3000 models (as the write-up's own qualifier says).

## Tue Oct 27 00:22:49 EDT 2026 -- non-vacuity lemma
Added compose_nonvacuous to Deleg.lean (total planner + controller answering every mission in V give a composite behaviour for every (u,e) in A); compiles, exit 0. Critique Section 3 updated; references section added.

## Tue Oct 27 00:23:22 EDT 2026 -- code evidence for the shape gap
notes/ardupilot/controller-ports.md corner section: blended target W - r u1 + s u2, r,s >= 0. It is a convex combination of the three vertices when r/L1 + s/L2 <= 1, so the real target lies in conv(w_{i-1}, w_i, w_{i+1}); the isotropic WP_RADIUS_M tube throws away about 2 m of fence margin per outer vertex. Added to Finding 4.2 with the side condition for the triangle-hull guarantee.

## Tue Oct 27 00:24:00 EDT 2026 -- cost threats 9 and 10
Added: cq ~ 0 only by hand or with a per-leg split (5+2N free reals otherwise); c1 is a nonlinear validity query in symbolic u, the same class as the author's timed-out solver run. Corrections item for the cost paragraph updated.

## Tue Oct 27 00:24:33 EDT 2026 -- Z3 maximality instance checks started
Scratch maxcheck.py: 30 random missions in V with hand G1 false at s=50; ask Z3 (H=1, complete by the pointwise lemma) for p0, dt, y with A, A2, G2, not G. Expect sat for every one if the hand G1 is maximal (Theorem e on the example). Running in background.

## Tue Oct 27 00:25:37 EDT 2026 -- Lean: corrected Hence paragraph
hence_on_A1 proved (restricted to A1, under the 'some target breaks G' hypothesis). Deleg.lean now 47 theorems, compiles, exit 0. Scripts copied to notes/validation/checks/.

## Tue Oct 27 00:26:40 EDT 2026 -- Z3 maximality: 30/30 sat; edge run started; related paper found
maxcheck.py: 30 random missions in V with hand G1 false at s=50: Z3 sat (counterexample to G) for all 30, 103 s total. Random cases mostly fail by large margins, so an edge run (maxedge.py: exactly one conjunct fails, margin < 0.5 m, 0.1 m grid) is running in background.
arXiv search found Damera, Matheu, Baras, 'Contract-Based Agentic Systems Engineering: Delegation as Quotient for Assured System Design', arXiv:2610.33349 (Oct 2026): quotient of STL contracts over a common signal space (Prop. 3.3, closure by Boolean substitution), no alphabet restriction. Relevant to the novelty paragraph: the delta of the present write-up over that paper is the universal projection onto the planner's ports, the pointwise lemma and the code certification.

## Tue Oct 27 00:27:17 EDT 2026 -- corrections reordered by severity
Closed-loop reach (1.21) is now correction 1, the deadline/window unsoundness 2, the false repair sentence 3, the semantics of Theorem (d) 4. Related paper added to Finding 2.4 and references.

## Tue Oct 27 00:28:09 EDT 2026 -- Lean: F2-F4 over a product of ports
Added a section with behaviours as dependent functions over arbitrary ports: F3a, F3b, F4, exP_exP (product fact), F2_ex, F3_needs_over. Compiles, exit 0, no warnings. Critique Section 3 updated.

## Tue Oct 27 00:28:28 EDT 2026 -- F2_all added
F2 for the universal projection proved from F2_ex and complement. Full file compiles: exit 0, 0 errors, 0 warnings. 55 theorems.

## Tue Oct 27 00:29:24 EDT 2026 -- Bad under the triangle guarantee in the example
Goal part of Bad: >50.5 (tube rho=2) vs >52 (triangle, rho'=0.5) vs 53 (exact reach, inside fence); home part >47 vs >48.5 vs 49. Added to Finding 4.2.

## Tue Oct 27 00:29:49 EDT 2026 -- window extension of the Diamond half
Derived: antecedent Diamond over [0,D1], consequent over [0,D2]: D1 <= D2 gives the Phi formula (alpha cap gamma sub d); D1 > D2 gives alpha sub d or alpha cap gamma empty. Added to Finding 1.10.

## Tue Oct 27 00:30:13 EDT 2026 -- Lean: short-deadline Diamond lemma
dia_short_deadline proved (D2 < D1 <= H: valid iff alpha sub d or alpha cap gamma empty). File compiles, exit 0, 56 theorems.

## Tue Oct 27 00:31:38 EDT 2026 -- Z3 edge maximality: 24/24 sat
maxedge.py: 24 missions in V failing exactly one conjunct of the hand G1 by < 0.5 m (down to 0.002 m): Z3 sat for all (20 goal, 2 w2, 2 home), 280 s. Second run (maxedge2.py) targets leg1min, w1, home, w2 conjuncts; running.

## Tue Oct 27 00:37:04 EDT 2026 -- Z3 edge run 2: 16/16 sat
maxedge2.py: 16 missions failing exactly one fence conjunct (9 w1, 5 home, 2 w2) by < 0.5 m: all sat, 305 s. Leg-length conjunct not sampled. Finding 3.2 item (5) added.

## Tue Oct 27 00:37:37 EDT 2026 -- Z3 leg-length edge: 10/10 sat
maxleg.py: 10 missions with |w1-h| in (5.5,6), all other conjuncts met: all sat (trivial for the solver). Every conjunct of the hand G1 now has edge-case evidence of maximality.

## Tue Oct 27 00:56:47 EDT 2026 -- end
Final recompile of notes/validation/Deleg.lean: exit 0, no errors or warnings, 56 theorems, no sorry. Deliverables: notes/validation/theory-critique.md (findings 1.1-5.2, 17 corrections, references), notes/validation/Deleg.lean, notes/validation/checks/ (scripts and Z3 outputs). Start 23:55:30, end stamp above; elapsed over 60 minutes.
