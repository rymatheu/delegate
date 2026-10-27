# Status (orchestrator: Fable 5.1; researchers: Opus 5.5)

_2026-10-18._ Directory created. Problem statement and scope guard in README.md / SCOPE.md.

## Direction being tried
The validity conditions (C1)/(C2) certify a delegation and the fixed-point sweep maximizes one (theory/foundations.md),
but the sweep needs a seed; constructing the delegation from (graph, query) alone is the open step.
This round tries to make the construction itself algebraic, in four slices run in parallel:

| slice | question | output |
|---|---|---|
| lit | who has decomposed a global spec into local contracts from architecture + spec only? | lit/existing-work.md |
| conjunctive | Farkas certificate of (C1) as a flow on the graph; canonical choice rule; LP procedure | theory/conjunctive-decomposition.md, scripts/conjunctive_decomp.py |
| temporal | syntax-directed operator D for ◇, ∨, U, EARS trigger/response; decider rule; non-decomposable forks | theory/temporal-decomposition.md, scripts/polystl_decomp_check.py |
| interface | what an edge must carry; canonical encoding as the seed; interpolation; non-existence theorem | theory/interface-cuts.md, scripts/interface_cuts.py |

Synthesis goes in notes/ANSWER.md once all four report.

## 2026-10-18, round 1 complete
All four agents reported; orchestrator re-ran the three check suites (conjunctive 2.3 s, temporal 4.3 s / 93 checks,
interface 29 s): 0 failures. Synthesis in notes/ANSWER.md. Tooling: arXiv MCP server registered (.mcp.json) with a
stdio bridge at scripts/arxiv_tool.py; 58-entry lit/existing-work.bib.
Headline: the decomposition is constructive (flow LP + choice rule R* + encoding seed + syntax-directed operator D);
relay answer 1/4 : 1/4; non-existence certificates for k=0, rank, exact, capacity, and information-fork cases.
Next: unify the conjunctive LP and D into one implementation; settle the fan-out tie; completeness of the template.
- 2026-10-18: theory summary PDF at docs/theory-summary.pdf (14 pp, LaTeX source docs/theory-summary.tex, latexmk clean).

## 2026-10-18, provenance correction (author's instruction)
The author wants this directory to be completely original. The orchestrator had copied four files from
another project into this directory and briefed the agents to build on them. That was wrong. Those files are deleted;
README/SCOPE rewritten; the foundations are being re-derived here (theory/foundations.md, PDF Section 2) and every
citation to the copied files is being removed from theory/, notes/, lit/ and docs/.

## 2026-10-18, round 2: clean deliverable
Author verdict on round 1: incomprehensible, not reproducible, contaminated by copied files and their vocabulary.
Round 1 material moved to notes/round1-archive/ (not a deliverable). New design fixed in notes/algorithm-spec.md,
then one script (scripts/decompose.py, 17/17 Z3 verdicts, <1 s) and one 9-page document (docs/decomposition.pdf)
built from it; every number in the document is printed by the script. One index error in the spec (the time range
of the quiet obligation) was caught by Z3 and corrected in both files.

## 2026-10-18, correction: no numeric type bounds
"Typed" ports = distinct variables with a known owner, nothing more. The bound Y_v was an invented input.
Removed from spec (header of notes/algorithm-spec.md), SCOPE.md, and being removed from decompose.py and
decomposition.tex: no (rec) constraint, leaks priced only by A_P via LP duality, gains fixed by the unit-gain
convention, assumptions A_i = projection of A_P onto in(i).

## 2026-10-18, round 3: template-free general method (current deliverable)
Author's requirement: no assumed templates for delegated specs; general PolySTL queries. Design in
notes/algorithm-spec.md (v3): each component forwards the query's own linear forms of its private variables
(continuous for delay 0, atom truth values through regions for delay 1); every obligation is the universal
projection of the remaining query (Z3 qe2, cross-checked); one tolerance ε fixed by max-min slack. 
scripts/decompose.py (899 lines, ~30 s, 259 cross-checked projections, all verdicts ok, exit 0) and
docs/decomposition.pdf (10 pages). Examples: relay, fan-in, 3-chain, a disjunctive query, a capacity stop, and
the relay with a deadline under delays (1,1) and (0,0). Unproved: causal version of exact-forwarding theorem for
H > 0 (conjecture), monotonicity of the slack verdict in ε.

## 2026-10-18, reset to foundations (author): docs/existence.pdf (2 pages)
Author rejected the 10-page method document as shallow. New rule: two pages maximum per document; only valid contract
operations. docs/existence.pdf answers: (1) existence vs construction are the same problem (last component is the
closed form rho(P / composition of the others); one sweep gives a maximal delegation); (2) validity alone is empty
(vacuous or input-pinning delegations always exist); acceptable (receptive, causal) delegations exist iff a
PolySTL-definable distributed strategy exists; strictly stronger than any distributed strategy (dimension argument),
which is strictly stronger than central realizability (forks); on pipelines with enough edge capacity all coincide.
- docs/algorithm.pdf (2 pages): the decision/construction algorithm. Nested architectures (chain edges with
  capacity, pure interface variables, and either H = 0 or all fresh information entering at the first component):
  decide the linearised first-order sentence by QE; if true, piecewise-affine Skolem functions (virtual substitution,
  midpoint rule) composed to respect the information structure give an acceptable delegation; sweep for maximality.
  Forks: linearisations give a sound refutation test; otherwise enumerate piecewise-affine budgets over the real
  closed field (semi-decision). Open: a computable budget bound.
- scripts/delegate.py: executable DELEGATE (algorithm.pdf) + FORK at budget 1. Z3 qe2 for Phi and the R_k(t),
  Skolem functions by virtual-substitution test points (midpoints first), recursive substitution, decoding,
  Z3 verification of (C1)/receptiveness/causality, and the sweep. Runs relay (H=0), 3-chain, disjunctive relay,
  relay H=2 (realizable and unrealizable), fan-in (fork -> affine strategies) in 0.6 s.
- docs/results.pdf (2 pages): verified results of delegate.py on six instances (generated by scripts/results_report.py).
- docs/procedure.pdf (3 pages): the complete procedure in one notation: objects, elimination with witnesses (lemma+proof), forwarding/carriers, the 8-step procedure, necessity/soundness/sweep theorems with proofs, the relay derived line by line.

## 2026-10-18, docs/complete.pdf (5 pages): write/review/rebut/revise loop, 2 rounds
Writer (Opus) + three reviewers (rigor, clarity, reproducibility). Round 1: 2 blocking, 15 major, ~45 minor; three
code defects found and fixed in scripts/delegate.py (carrier decoding, assumptions after the sweep + (V2) check,
Scope check, substitution termination, deterministic candidate order, regression instances). Round 2: 0 blocking,
3 major (one paragraph's inference; the fork-search description), fixed in revision 3. Orchestrator verification:
script exit 0 (all verdicts), latexmk clean, 5 pages, no banned words, quoted block byte-identical to the script's
first 21 lines. Deliverable: docs/complete.pdf + scripts/delegate.py. Reviews and rebuttals in docs/reviews/.
- docs/example.pdf (2 pages): timed speed-governor chain (H=2, three components, □/◇ query) worked by delegate.py; final contracts show Perception must preserve exactly one feature (o(1)>=3); plus an unrealizable timed variant refuted. Generated by scripts/example_report.py with Z3-verified forms; instance added to the one command.

## 2026-10-19, pivot: agentic formulation
Author: the algorithmic route is not fruitful at scale (sweep QE on the longitudinal stack, H=2, does not finish).
New question: compute delegates by agents subject to the algebraic constraints of the calculus; can it be built with
Strands Labs / Strands Agents SDK (AWS)? Three Opus research agents: notes/agentic/formulation.md (constraints,
proposer/verifier loop, guarantees), notes/agentic/strands.md (SDK feasibility), notes/agentic/literature.md (+ .bib).
Plan document to follow in docs/.
Results (2026-10-19, later): notes/agentic/formulation.md (constraint set, proposer/verifier/coordinator loop with
cell-projected counterexamples, soundness by construction, semi-decision claim at every horizon, governor checks:
101 verdicts in 0.25 s vs the 70 s sweep), notes/agentic/strands.md (Strands Agents 1.61.1 fits for the proposers only;
coordinator and verifier stay plain Python; AI Functions in Strands Labs fits per-component checks; blockers: forced
tool choice, no sampling control, weekly churn, Bedrock default), notes/agentic/literature.md (50 verified arXiv
papers; nobody does agent proposers for AG-contract decomposition). Plan: docs/plan.pdf (5 pages), one review round
(docs/reviews/plan-A.md: 5 blocking, 12 major, 22 minor; all fixed, docs/reviews/plan-rebuttal.md).

Soundness defect found and fixed in scripts/delegate.py: Z3 5.3.1's virtual-substitution tactic 'qe' (introduced
for the abandoned big example) returned a NON-EQUIVALENT (too strong) elimination on the governor Actuator sweep
step, and the cross-check Then('qe','smt') built on the same tactic accepted it. qe() now uses only 'qe2' and
cross-checks with the default solver (sound) or Then('qe2','smt'); regression 5 asserts the swept Actuator set equals
the documented maximal set. README run time: about 2 s again (the 85-100 s measured with the faulty tactic were its cost). The quoted output block in
docs/complete.tex was refreshed to the current byte-identical output.

## 2026-10-21 Inference-rule notes
Author pasted set-theoretic AG rules (lemma, Refinement, Composition, Assumption Relaxation, Guarantee Tightening, two-component scheme). All checked pointwise by notes/agentic/rules_check.py (15/15). Composition premise typo (G1 <= A1 should be G1 <= A2), "M1||M1", "A-2"; nonemptiness hypothesis unnecessary; last step of scheme needs G1 <= A2, not Guarantee Tightening alone. Scheme implies (V1),(V2); converse fails (edge rule G1 <= A2 is the context-free, per-edge form). Mapping in notes/agentic/rules.md.

## 2026-10-21 Lean formalisation
lean/Contracts.lean: definitions, refines_iff (no nonemptiness hypothesis), four rules, compose_refines, delegation theorem (tighten, compose, relax). lake build clean, 0 warnings; delegation depends on no axioms, lemma on propext/choice/Quot.sound.

## 2026-10-21 Lean listings for the paper
docs/lean-listings/: custom Pygments lexer (declared names, brackets, angle brackets as own classes), leanstyle.tex (VS Code hues darkened for paper, hooked into minted 3 style loading), JetBrains Mono + JuliaMono fallback (LuaLaTeX luaotfload fallback; XeLaTeX newunicodechar list), tested both engines; needs ~/.latexminted_config with lexer sha256; latexminted 0.5.0 breaks on Python 3.14. Theorem delegation reflowed to <= 50 chars/line for two-column; lake build clean.

## 2026-10-21 Overleaf route
docs/lean-listings: colours split into leancolors.tex; prehighlight.py (static route, fancyvrb fragment, no shell escape) tested lua+xe; XeLaTeX fallback scoped to the monospace family via \leanfb; fonts share 0.600 em advance and 0.550 x-height. Overleaf: custom lexer expected blocked (home config), static route recommended.

## 2026-10-21 Proposal experiment
notes/agentic/proposal_loop.py + runs/: Opus 5.5 proposers vs Z3 verifier. Governor: accepted round 1 in 3/3 runs. Stand-in stack (not nested; delegate.py does not apply): accepted in rounds 1, 3, 2. Rejections were neighbour interface mismatches, repaired from projected counterexamples. Contracts readable but over-strong: 6-12 of 24-30 conjuncts individually removable (minimality.py). Write-up notes/agentic/experiment.md.

## 2026-10-21 Composition.lean
Saturation, contract composition (saturated), composeSat_refines (scheme hypotheses => (A1,G1)||(A2,G2) refines (A,G), no implementation hypotheses needed), implements_composeSat, delegation' via rule_refinement. lake build clean.

## 2026-10-26 Chain.lean
chain_delegation: lists of components/contracts, composeAll, ImplementsAll, Chain (edge conditions), lastC; proof = tighten last, compose along edges (rule_composition iterated), relax first. Two- and three-component instances as examples. lake build clean; depends on propext only.

## 2026-10-26 Chain contracts refine
Chain.lean: composeChainSat (nested saturated composition), compose_sat_refines_step, composeChainSat_refines (chain hypotheses => composition of saturated delegates refines (A,G), no implementations), and the saturated-query variant. lake build clean.

## 2026-10-26 Big-operator composition
Chain.lean: top, BigPar, notation `∥ x ∈ l, f x` (macro over List.map), par_top, bigPar_cons (= composeAll), chain_delegation_bigPar. lake build clean.

## 2026-10-26 Parallel, fan-in, fan-out rules
Contracts.lean: rule_parallel (A1 n A2, G1 n G2), rule_fan_in, rule_fan_out (derived). Z3 pointwise: parallel/fan rules sound; naive circular rule (G1<=A2, G2<=A1) UNSOUND without time; with the code known, a chain delegate exists iff M1 n M2 n A <= G (envelope M1 n A <= G1 <= A2 <= -M2 u G).

## 2026-10-26 Notation split
Lean: `⊗` (seq) for sequential composition, `∥` (par) for parallel; seq_eq_par; Composition rule, delegation, chain theorems use ⊗; Parallel rule and contract composition use ∥; fan-in (M1 ∥ M2) ⊗ M3, fan-out M1 ⊗ (M2 ∥ M3); big operators BigSeq/BigPar with `⊗ x ∈ l, f x` and `∥ x ∈ l, f x`. Paper listing lean/delegation.pdf in the ICCPS repo still shows ∥ for the chain; regenerate after copying Contracts.lean.

## 2026-10-26 Notation reverted
All composition back to `∥` (single `compose` = intersection); BigPar only. Author: keep the set definition for now.

## 2026-10-26 Book read
notes/book-ag-ports.md: Benveniste et al. RR-8147 ports/alphabets summary; one composition operator (intersection) with Σout disjointness; sequential vs parallel = port-set property; alphabet equalization = cylinders; Property 7 gives well-formedness (G input-enabled, A constrains inputs only).

## 2026-10-26 General rule
Composition.lean: implements_composeSat is the general rule (no flow condition); rule_parallel_of_general, rule_composition_of_general, rule_mixed_of_general (E ∩ G1 ⊆ A2 => (E ∩ A1, G2)) derived from it by relaxation + tightening. lake build clean.

## 2026-10-26 Unsaturated general rule
Author: composition formula is for saturated contracts. Z3: formula on unsaturated G fails; on G' it holds but the assumption is vacuous (M_i ⊆ G_i'). Correct basis for unsaturated contracts: Parallel + new rule_assumption_discharge; rule_sequential and rule_mixed derived from them in Contracts.lean. lake build clean.

## 2026-10-26 General unsaturated rule
Contracts.lean: rule_general (A ⊆ A1, A ∩ G1 ⊆ A2 => M1||M2 |= (A, G1 ∩ G2)); Parallel/Sequential/Mixed as instances; general_assumption_iff: admissible A iff A ⊆ A1 ∩ (A2 ∪ ∁G1). Z3 pointwise checks agree. lake build clean.

## 2026-10-26 DAG theorem
Chain.lean: Acc (accumulated edge conditions A_E ∩ ⋂_{j<i} G_j ⊆ A_i), allG, acc_compose (iterated pure sequential composition via rule_general), dag_delegation, chain_delegation_of_dag (consecutive conditions imply accumulated ones). Answer: pure sequential suffices for any DAG given environment-as-component, no hiding, acyclic. lake build clean.

## 2026-10-26 Hiding
Hiding.lean: B = X × H, hide = existential projection, lift = cylinder; rule_hide, hide_implements_iff (external contracts unaffected by hiding), rule_general_hide. Composite guarantee over external wires = ∃hidden (G1 ∩ G2). lake build clean.

## 2026-10-26 Convention adopted
Author: drop port tracking; ⊗ = pure sequential (all outputs of M1 consumed by M2), ∥ = pure parallel (no wires between). Lean: seq/par both intersection, seq_eq_par; Sequential rule (rule_composition, rule_sequential) over ⊗, Parallel over ∥, fan-in (M1 ∥ M2) ⊗ M3, fan-out M1 ⊗ (M2 ∥ M3); chain/DAG theorems over ⊗; BigSeq/BigPar. Triangles (A→B, A→C, B→C) need pass-through nodes under strict ⊗ (figs/triangle.png). lake build clean.

## 2026-10-26 Identity rule
Contracts.lean: Pass inp out (out = inp), rule_pass: I ⊨ (A, A') with A' the same property on the output wire.

## 2026-10-26 Bypass rule
Contracts.lean: rule_bypass_via_pass (M1 ⊗ ((M2 ∥ I) ⊗ M3) from Parallel+Pass+Sequential) and rule_bypass (no node, edge conditions G1 ⊆ A2 ∩ A, G2 ∩ A ⊆ A3). lake build clean.

## 2026-10-26 Triangle rule
Author rejected the pass-through node and A/A'. Replaced by rule_triangle: G1 ⊆ A2, G1 ∩ G2 ⊆ A3 => M1 ⊗ (M2 ⊗ M3) ⊨ (A1, G3). Pass/bypass rules removed. lake build clean.

## 2026-10-26 Three composition symbols
⨯ (wire) = architecture-determined composition, always intersection; ⊗ and ∥ its pure cases (seq_eq_wire, par_eq_wire). rule_triangle concludes M1 ⨯ M2 ⨯ M3. lake build clean.

## Triangle as `Tria` (2026-10-26)
Dropped the `⨯` operator. `Contracts.lean` now defines `Tria M₁ M₂ M₃ := M₁ ∩ M₂ ∩ M₃` with
`tria_eq_seq : Tria M₁ M₂ M₃ = M₁ ⊗ M₂ ⊗ M₃` (rfl). `rule_triangle` concludes
`Tria M₁ M₂ M₃ ⊨ (A₁, G₃)` from `M_i ⊨ (A_i, G_i)`, `G₁ ⊆ A₂`, `G₁ ∩ G₂ ⊆ A₃` (pointwise proof);
`rule_triangle_of_sequential` derives the same from `rule_general` + `rule_composition`.
LaTeX statement and proof: `docs/figs/tikz/triangle-rule.tex`. Figure labels updated to `Tria(M_1,M_2,M_3)`.
Answer to "are seq, par, triangle enough": yes once Sequential keeps `G₁` in its conclusion and only
sources read the environment; otherwise the Node rule `A ∩ G₁ ⊆ A₂` is needed, and with the
guarantee-dropping Sequential no finite set of shapes suffices (4-node counterexample).

## Validated delegation write-up (2026-10-27, 23:54 to 04:00 EDT)
Deliverable: docs/delegation.pdf (5 pages, source docs/delegation.tex) and scripts/validate.py (one command, about 17 min full, --quick about 100 s, --plot-only regenerates figures from notes/validation/results.json). Supporting material: notes/validation/theory-critique.md (21 findings, 17 corrections, all applied), notes/validation/Deleg.lean (56 theorems, no sorry; `cd lean && lake env lean .../notes/validation/Deleg.lean`), notes/validation/review.md (fresh adversarial review), notes/validation/experiments.md and results.md (run 4 numbers), figures in docs/figs/validation/.
Outcome on the speed claim: the first monolithic encoding timed out because of one goal query on the shared incremental solver; with the goal atom asked last tick first the monolithic check accepts R4 in 12.04 s at H=8 against 12.66 s for step 2 plus 0.356 s per planner check. One-shot cost is equal within noise; delegation is cheaper from the second accepted planner check sharing one controller certification (break-even n > 1.08 at H=8); over the sequence R1..R4 it is 7% slower at H=8; at H=4 delegation cannot certify reach while the monolithic check proves the composite correct (completeness loss). Novelty is modest and stated: steps 3-4 are the AG quotient projected onto the planner's ports; new are the pointwise lemma, the exact real-QE projection, the certified code-to-guarantee step and the loss account.
