# Answer: algebraic decomposition of a global PolySTL contract over an architecture graph

_2026-10-18. Orchestrator synthesis of lit/existing-work.md, theory/conjunctive-decomposition.md,
theory/interface-cuts.md, theory/temporal-decomposition.md. Every numbered claim below is backed by a
proof in those notes, in theory/foundations.md (cited as "foundations §n"), or a Z3/LP check in scripts/ (all three suites re-run by the orchestrator: 0 failures)._

## The question, as posed
Given only (1) the architecture graph (components, typed ports, who reads/writes what, unit delays) and
(2) a global PolySTL contract P = (A_P, G_P) over the full variable vector, produce one contract per component
that mentions only that component's ports, such that any components meeting their contracts make the system
meet P. Some components get nothing.

## The answer in one paragraph
The decomposition is an operator DECOMPOSE(graph, P) built from three algebraic pieces that compose by
structural recursion on P. (i) **Support**: a time-expanded cone-of-influence plus an LP-necessity test decides
which components get rows; the rest get (true, true). (ii) **Predicates**: every polytope row of P is rewritten
as a sum of port-local rows along the graph. The coefficients form a *flow* on the graph (writer and readers of a
shared variable must balance), the row's bound is *split* among the components on the flow, and the pass-through
gains are *centred* in the edge types. In certificate form this is jointly linear in normals, offsets and
multipliers, so it is an LP, and a lexicographic max-min rule R* picks a unique point. The same object seen from
one edge is the *canonical encoding*: the edge carries the linear functional of upstream-private variables that the
query couples to downstream outputs, with a tolerance band, and that band is the seed that the fixed-point
sweep (foundations §9) needs. (iii) **Temporal/Boolean structure**: ∧ and □ distribute; every ∨, ◇, U, R node goes through one unified
disjunction rule with a *decider* component chosen by a fixed preference order, with branch flags carried in the
free width of existing edge variables. Assumptions are then solved last as shadows (existential projections) of
A_P and the other guarantees onto each component's inputs, time-sliced on cycles. The result satisfies (C1),
(C2), receptiveness and causality. One Gauss–Seidel sweep makes it maximal. When no delegation exists the
operator returns a certificate naming the cut, the functionals the edge would have to carry, and its dimension.

## The operator, step by step
1. **Unroll** P over [0,H] into columns (variable, time). Build the time-expanded graph with delay and memory edges.
2. **Normal form**: NNF of G_P. Atoms are polytope rows; mixed-owner rows are the only place real-valued
   information must cross the graph.
3. **Support** (conjunctive note Thm 2): for each row, the time-expanded cone of influence COI_k from the row's
   output columns backwards; LP-necessity Nec_k ⊆ COI_k; everything outside COI_k is a bystander. Certificate
   support gives (true,true) with no receptiveness hypothesis (bystanders: foundations §10).
4. **Split each row** (conjunctive Thm 1 and 3; interface Thm 7): head-band template, one band row per
   (component, query row), supported on the component's causal port columns with its latest output column in the
   cone as head. Feasible set = "leaky-flow" polyhedron: per-column conservation between writer and readers,
   leaks priced by the support function of A_P ∧ types, plus two linear receptiveness margins per row.
   Equivalently, per cut: edge carries T·L·x with L a basis of the needed functionals (SVD), T identity or
   type-scaled, tolerance a ≤ a*.
5. **Choose** (conjunctive §5, rule R*): (a) support by leximin of freedom with uninvolved = +∞;
   (b) bound shares by water-filling (max-min fair); (c) gains by water-filling the receptiveness margins;
   (d) LP certificate that the optimum is a point. Unique in shares and margins; covariant under rescaling and
   sign flips of internal signals. Equivalent on the relay to the interface note's a = a*/2.
6. **Disjunctive nodes** (temporal note §3, rule UD): parameters = branch budget J', decider k, informed set,
   flags on k's outputs, guards on receivers' inputs. Decider: ψ_k = ⋁_j (ψ_k^j ∧ σ^j); informed: ⋀_j (f_i^j → ψ_i^j);
   others: ⋀_j ψ_i^j; side condition: Ctx ∧ σ^j ∧ relays ⊨ f_i^j. Decider preference: static witness, then
   the unique actor, then the most-downstream admissible observer, then shrink J', else fail at that node.
   Flags need no new ports: an edge carries any finite number of flags iff its writer's other duties leave it
   positive width on every reachable history (comb construction).
7. **Assumptions** (all three notes agree with the shadow assumption, foundations §5): A_i = π_in(i)(A_P ∧ ⋀_{j≠i} G_j) via qe2.
   On cyclic supports the full-horizon A_i is UNSOUND (Z3 counterexamples); use time-sliced A_i^h that include the
   component's own earlier guarantees. This is a time-inductive circular rule (Circ) produced by projection rather than by hand.
8. **Maximize** (optional): one sweep of quotient + universal projection from the constructed seed (fixed-point sweep,
   foundations §9). On the relay the canonical seed is already a fixed point.
9. **Verify**: (C1), (C2), per-component ∀∃ realizability, all QF_LRA after unrolling.

## What it returns on the relay
Radio: (|r| ≤ 1, |m − r| ≤ 1/4). Display: (|m| ≤ 5/4, |d − m| ≤ 1/4). Unique under R*, receptive, (C1)+(C2) hold,
fixed point of the sweep. The hand-chosen 0.2/0.3 split of the relay example (foundations §11) is the proportional-to-type split with R*'s gains.

## Which components get contracts
Exactly the support of the certificate: owners of query atoms, components on a flow carrying a needed functional,
deciders, informed receivers, relays. Being on a path from an A_P variable to a G_P variable is not enough:
in the model-free tracking loop, Perception gets (true,true) because the canonical decomposition opens the loop;
it becomes necessary only when the Plant's physical normal is fixed, and then R* reproduces the hand-chosen 0.1/0.1/0.1 of the tracking-loop example (foundations §11).

## When it cannot be done, and what it says instead
- Cut with edge dimension k = 0 (incl. causal capacity 0, e.g. delay-1 Radio with lag-0 query): no delegation of any kind.
- n jointly informative functionals across an edge of dimension k < n: no delegation with conjunctive upstream
  obligations (rank theorem); with zero tolerance, no PolySTL delegation at all; with positive tolerance a
  disjunctive quantizer may exist (verified: 4-piece code through a 1-D edge), bounded by the capacity theorem
  ∏⌈W_i/2ε_i⌉ ≤ ∏ Y_j/a_j.
- Information fork (two actors, disjoint independent information, no path, exclusive branches): delegable iff a
  static branch is; otherwise nothing exists (agreement lemma, Z3 finite-sample UNSAT). One added edge repairs it.
- EARS chain □(trig → ◇_[0,k] resp) with no-spurious-response conjunct: delegable iff Σ delays ≤ k; window budget
  Σ(d_l + s_l) ≤ k is the temporal analogue of a + b ≤ 0.5.

## Three structural facts
- (C1) is jointly linear in normals and offsets in certificate form, also when the normals are free; it looks bilinear
  only under the rows×multipliers parametrisation. Bilinearity survives only in receptiveness with shared heads (fan-out).
- Ghost-free handouts (foundations §6) computed for one component at a time are sound only sequentially or on acyclic
  supports.
- Interpolation: Craig interpolants over the edge plus ghosts are exactly the (Seq) cuts, i.e. the cut formulas handed
  from upstream to downstream; they certify, they do not choose.

## Open (honest list)
- Fan-out: one output heading two query bands; the tie between head coefficients is the one remaining bilinear step.
- Support search is 2^(optional components); greedy works on all examples, unproved.
- Completeness of the head-band template (does it refine every valid conjunctive delegation?) and of D for a given
  syntax (D is syntax-dependent: DNF vs CNF); Conjecture C1 (guarded form) stated.
- Circular UD for discrete decisions around feedback; joint objective for window budget and tolerance budget.
- n > k with ε > 0: canonical quantizer not constructed (search).
- Unbounded horizon: time-invariant code plus Circ; not done.

## Where this sits in the literature
No existing work takes only an I/O architecture and a global real-valued temporal contract and returns port-local
contracts by a canonical construction. Closest: Albarghouthi–Dillig–Gurfinkel (POPL'16) linear multi-abduction
(= (C1), sweep from a model seed, no I/O direction), Filippidis–Murray (finite-state GR(1), transition relation
= model), Marchesini et al. (telescoping bands along a path, fixed templates, sufficient only). Pacti chained from
trivial contracts lands on the vacuous fixed point (reproduced, scripts/lit_pacti_relay.py).
