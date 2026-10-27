# Specification of the deliverable (2026-10-18; revised: NO numeric type bounds)

CORRECTION (author, 2026-10-18): "typed" ports means only that the variables are distinct and each one is
assigned to a known component. There are NO numeric range bounds Y_v. Every mention of Y_v, 'types', 'typed
trace', '(rec)', 'margin' below is superseded by the rules in this header:
- Traces are arbitrary real-valued. No 'types' conjunct anywhere. (C1): A_P ∧ ⋀S_i ⊨ G_P; (C2): A_P ∧ ⋀S_i ⊨ A_j.
- Receptive = for every input history there is an output history in S_i (no box). A band row with c > 0 is
  always receptive, so (rec) is dropped.
- (budget): Σ w_i + h(λ_k) ≤ g_k where h(λ) = max{λ^T z : z satisfies A_P} is the support function of A_P,
  written linearly by LP duality: A_P = {M z ≤ b} ⇒ h(λ) = min{ b^T y : y ≥ 0, M^T y = λ }. If A_P does not bound
  the direction λ, the leak is impossible (the dual is infeasible). With A_P = true, λ = 0: exact cancellation.
- Choice rule steps 1–3 (support, water-filling of shares) unchanged. Step 4 (replaces margins): among the
  solutions with the chosen shares, minimise Σ_i |c_i − 1| + Σ_i |κ_i| (one LP). Convention: unit pass-through
  gains where the flow allows, offsets not split without need. Relay: c_R = c_D = 1. Fan-in: c_A = c_B = c_F = 1,
  emitted rows |a − s1| ≤ 1/3, |b − s2| ≤ 1/3, |f − a − b| ≤ 1/3, Logger (true,true).
- Emitted assumptions: A_i := the existential projection of A_P onto in(i) (true when in(i) has no environment
  variable). (C2) is then immediate since A_P ⊨ π_in(i)(A_P). Relay: Radio (|r| ≤ 1, |m − r| ≤ 1/4),
  Display (true, |d − m| ≤ 1/4). Remark 1 (strengthening by projecting A_P ∧ ⋀_{j≠i} G_j) stays.
- Fan-in example: A_P = true, no bounds on s1, s2 (leaks impossible; support {A,B,Fuser} forced).
- Temporal part: no bounds; A_i = true; edge predicates are any two disjoint nonempty predicates on m_l, the
  script uses |m_l| ≥ 1/2 and |m_l| ≤ 1/4; 'typed point' becomes 'a point'. Theorems 3, 4 unchanged.
- Lemma 1 unchanged (it uses A_P = |r| ≤ 1, which is part of the query).


One document `docs/decomposition.pdf` (LaTeX source `docs/decomposition.tex`, target 8 pages) and one script
`scripts/decompose.py` (run: `.venv/bin/python scripts/decompose.py`) that implements the algorithm of the document
and prints the emitted contracts for the two worked examples, then verifies them with Z3.
Everything below is the fixed design. Do not add machinery, vocabulary, or results beyond it.

## 1. Setting (single notation, used everywhere)

- Variables V, each with a type bound |v| <= Y_v. Horizon H; time t in {0,...,H}. A *column* is a pair (v,t).
  A trace z assigns a real z_v(t) to every column, within type.
- Components i = 1..n with input variables in(i), output variables out(i), ports(i) = in(i) ∪ out(i).
  Every variable has at most one writer; variables with no writer are *environment* variables.
  Each component has a delay d_i ∈ {0,1}: its output at time t may depend on its inputs at times <= t − d_i
  and on its own outputs at times < t.
- PolySTL (bounded): predicates a^T x_t <= b over the full variable vector x at a single time t; Boolean ∧, ∨, ¬;
  temporal □_[a,b], ◇_[a,b] with bounded intervals. Semantics on finite traces over [0,H]; after unrolling, every
  formula denotes a finite union of polytopes in column space; validity and containment are QF_LRA queries.
- A *contract* for component i is a pair (A_i, G_i) of PolySTL formulas over ports(i) only. Its behaviour set is
  S_i = ¬A_i ∨ G_i. The *query* is P = (A_P, G_P) over V.
- Definition (valid delegation). (A_i,G_i)_i is valid for P iff
  (C1) A_P ∧ types ∧ ⋀_i S_i ⊨ G_P and (C2) A_P ∧ types ∧ ⋀_i S_i ⊨ A_j for every j.
  (Prove in the document that this is exactly refinement of P by the composition of the component contracts,
  from the standard definitions of composition and refinement; cite Benveniste et al. 2018 only for those
  definitions.)
- Definition (receptive, causal). S_i is receptive if for every typed history of in(i) there is a typed history of
  out(i) with the joint trace in S_i; causal if that output can be chosen time step by time step using only inputs
  up to t − d_i and own outputs before t. A delegation must be valid, receptive and causal; otherwise G_i = false
  would be "valid".
- Lemma (why the edge must carry information). On the relay below, the set of (m,d) that satisfy
  |d − r| <= 1/2 for EVERY r with |r| <= 1 is empty. So no contract for Display alone can discharge the query;
  the obligation must be split so that m carries r. (One-line proof. This motivates the flow.)

## 2. Running examples (defined once, used in both parts)

- Relay. Environment r with |r| <= 1. Radio reads r, writes m, |m| <= 2, delay 0. Display reads m, writes d,
  |d| <= 3, delay 0. H = 0. Query: A_P = (|r| <= 1), G_P = (|d − r| <= 1/2).
- Relay with a deadline (temporal example). Same graph with delays (d_R, d_D) ∈ {(0,0),(1,1)}, H = 4,
  Query: A_P = true (types only), G_P = □_[0,T] ( |r(t)| > 1/2 → ◇_[0,k] |d| >= 2/5 ) with k = 2 and T = H − k.
  (For (1,1) the only feasible split has zero slack; for (0,0) there are several; show both.)
- A fan-in example for the conjunctive part, to show a bystander and a three-way split: environment s1, s2 with
  |s_j| <= 1; A reads s1 writes a (|a| <= 2); B reads s2 writes b (|b| <= 2); Fuser reads a,b writes f (|f| <= 4);
  Logger reads f writes l (|l| <= 4). All delays 0, H = 0. Query: types, G_P = (|f − (s1 + s2)| <= 1).
  Expected: Logger gets (true,true).

## 3. Part A: conjunctive queries (G_P is a conjunction of bands)

After unrolling, G_P = ⋀_k |n_k^T z − κ_k| <= g_k  (each □_[a,b] of a band gives one band per time instance;
one-sided rows are bands with one bound at infinity, allowed). A_P is a conjunction of rows on environment columns.

Part A assumes all delays are 0 so that every emitted row is a single-time predicate (pure PolySTL).
Delays enter in Part B through the intervals of ◇. (State this restriction plainly in the document.)
Template for component i and band k: one *band row*
   | c · z_h − β^T z_Caus − κ | <= w,   c > 0, w >= 0,
where h = (v,t) is an output column of i ("head"), Caus(i,h) = {(u,t): u ∈ in(i)} (same time, delay 0),
and β is supported on Caus(i,h). This is a single-time predicate over ports(i); it is causal by construction.
Row vector of the band row: ρ_ik := c e_h − β (in column space).

Decomposition constraint (flow): choose a support I ⊆ {1..n} and one row per (i ∈ I, k) such that
   Σ_{i∈I} ρ_ik  =  n_k  +  λ_k,       with λ_k supported on ENVIRONMENT columns only,          (flow)
   Σ_{i∈I} w_ik  +  Σ_c Y_c |λ_k[c]|  <=  g_k,                                                  (budget)
   Σ_{i∈I} κ_ik  =  κ_k.                                                                         (offset)
Interpretation: on every system column the writer's and readers' coefficients cancel exactly against the query
(Kirchhoff); on environment columns a residual λ is allowed and is paid for at its type bound. All constraints are
LINEAR in (c, β, κ, w, λ) (absolute values by epigraph). This is the whole algebra: the query row is written as a
telescoping sum of local rows and the bound is split along the sum.

Receptiveness constraint (per row, linear): the band fixes z_h to an interval of half-width w/c around
(β^T z_Caus + κ)/c; it intersects [−Y_h, Y_h] for every typed input iff
   Σ_{u∈Caus} |β_u| Y_u + |κ| − w  <=  c · Y_h.                                                 (rec)
Restriction (state it plainly in the document): each output column is the head of at most one band row. Fan-out of
one output into two query bands is NOT covered by this version.

Theorem A (soundness). If (flow),(budget),(offset),(rec) hold then the contracts
   A_i := types of in(i),   G_i := ⋀_k band row_ik   (i ∈ I);   (true,true) for i ∉ I
are valid for P, receptive and causal.
Proof: (C1) is the triangle inequality: n_k^T z − κ_k = Σ_i (ρ_ik^T z − κ_ik) − λ_k^T z, so
|n_k^T z − κ_k| <= Σ_i w_ik + Σ_c |λ_k[c]| Y_c <= g_k. (C2) is trivial since A_i are types. Receptiveness: (rec)
gives a value for each head given its causal inputs, in order of time. Causality: by the support of β.

Choice rule (fixed, simple, stated once):
 1. Cone of influence: COI_k = components with a directed path in the (time-expanded) graph to the writer of a
    column where n_k is nonzero. Only I ⊆ COI_k are considered.
 2. For each feasible I (enumerate subsets of COI_k, small in practice; say so), compute the max-min share
    t(I) = max min_{i∈I} w_ik subject to the constraints (one LP), then water-fill (freeze the components whose
    share cannot exceed the level, raise the rest; at most |I| LPs).
 3. Pick I with the lexicographically largest sorted share vector, ties broken by smaller |I|.
    (Thus a component is left out when leaving it out does not lower anyone's share: that is "only some components
    get contracts".)
 4. With shares fixed, maximise the minimum receptiveness margin  c·Y_h − (Σ|β_u|Y_u + |κ| − w)  over the
    remaining freedom (one LP, then water-fill likewise). This centres each interface signal in its type range.
 5. Report the contracts. If no I is feasible, report "no band delegation exists for row k" together with the
    row and COI_k.
Expected outputs (must be reproduced by the script, verified by Z3):
 - Relay: Radio (|r|<=1, |m − r| <= 1/4), Display (|m|<=2, |d − m| <= 1/4).
 - Fan-in: shares 1/3 each (budget units); support {A, B, Fuser}; Logger (true,true). Flow forces c_F = 1,
   β_1 = β_2 = 1, c_A = β_a, c_B = β_b. Step 4 margins: A: 2c_A − 2/3, B: 2c_B − 2/3, Fuser: 13/3 − 2c_A − 2c_B;
   max-min gives c_A = c_B = 5/6 with all three margins equal to 1. Emitted rows (normalised by the head
   coefficient): |a − (6/5) s1| <= 2/5, |b − (6/5) s2| <= 2/5, |f − (5/6)(a + b)| <= 1/3.
   The script must COMPUTE these; if the LP gives something else, report the discrepancy, do not force the numbers.
   Relay check of the same rule: flow forces c_D = 1, β_R = 1, β_D = c_R; shares 1/4, 1/4; margins
   2c_R − 3/4 and 13/4 − 2c_R, equal at c_R = 1 (both 5/4).

Remark (tighter assumptions). A_i may be strengthened to the existential projection of A_P ∧ types ∧ ⋀_{j≠i} G_j
onto in(i) (e.g. Display may assume |m| <= 5/4 on the relay). State that this preserves (C1) and gives (C2) when the
support graph is acyclic, with a two-line proof, and that it is not used by default. No more than that.

## 4. Part B: a temporal query (trigger → bounded response along a chain)

First the fact that fixes the example (state it in the document, one paragraph): a query of the shape
□(φ → ◇_[0,k] ψ) alone, with ψ over the last component's outputs and satisfiable within type, is met by the
degenerate delegation "C_n always outputs a point of ψ, everyone else (true,true)". That is valid, receptive and
causal, and carries no information along the chain. So the meaningful query has a second conjunct that forbids
spurious responses (a quiet requirement). The temporal example is therefore

   G_P = □_[0,T] ( φ → ◇_[0,k] ψ )  ∧  □_[0,T] ( □_[0,k] ¬φ → ◇_[k,k] ψ̄ ),

where φ is a predicate over environment variables read by C_1, ψ and ψ̄ are DISJOINT nonempty predicates over the
outputs of C_n (respond / stay quiet), and C_1 → ... → C_n is a path with delays d_l and edge variables m_l written
by C_l and read by C_{l+1}. Read: a trigger at t gets a response within k steps; if there has been no trigger during
the last k steps the output is quiet. Horizon H >= T + k. Relay instance: φ = (|r| > 1/2), ψ = (|d| >= 2/5),
ψ̄ = (|d| <= 1/5), k = 2, delays (0,0) and (1,1), T = 2, H = 4.

Why not distribute ◇ naively: counterexample on the relay with G_P = ◇_[0,1] |d − r| <= 1/2 and naive obligations
Radio ◇_[0,1] |m − r| <= 1/5, Display ◇_[0,1] |d − m| <= 3/10: trace r = (−1,−1), m = (0,−4/5), d = (0,0)
satisfies both and violates the query (Radio accurate at t=1 only, Display at t=0 only). Z3-checked in the script.

Decomposition (the temporal analogue of the band split). Choose for each edge two DISJOINT nonempty predicates
F_l ("trigger seen") and F̄_l ("quiet") over m_l within type (script default: |m_l| >= Y/4 and |m_l| <= Y/8), and
slacks s_l >= 0 with
   Σ_l (d_l + s_l) <= k.                                                                         (window budget)
Writing F_0 := φ, F̄_0 := ¬φ, F_n := ψ, F̄_n := ψ̄, emit for every l = 1..n, over ports(C_l) only:
   C_l:   □_[0,T_l] ( F_{l−1} → ◇_[d_l, d_l+s_l] F_l )   ∧   □_[0,T_l] ( □_[0,s_l] F̄_{l−1} → ◇_[d_l+s_l, d_l+s_l] F̄_l ),
with T_l = T + Σ_{j<l}(d_j + s_j) (the response part may be stated on [0,T] + accumulated shift; just make the
indices right and verify by Z3). Components off the path get (true,true). A_i = types.
Theorem B (soundness). Under (window budget) the emitted contracts are valid for P.
Proof, response part: φ at t gives F_1 at some t_1 ∈ t + [d_1, d_1+s_1], ..., ψ at some t_n ∈ t + [Σd_l, Σ(d_l+s_l)]
⊆ t + [0,k]. Quiet part: if ¬φ on [t, t+k], then for every τ with [τ, τ+s_1] ⊆ [t, t+k], F̄_1 at τ + d_1 + s_1, so F̄_1
holds on [t + d_1 + s_1, t + k + d_1]; inductively F̄_l holds on [t + Σ_{j<=l}(d_j+s_j), t + k + Σ_{j<=l} d_j]; for
l = n this interval contains t + k iff Σ(d_l + s_l) <= k. Write it out for n = 2 in the document.
Receptiveness and causality: the strategy "m_l(τ) := a point of F_l if F_{l−1} held at τ − d_l, else a point of
F̄_l" meets both conjuncts (check it in two lines); it uses only inputs at τ − d_l.
Choice of the slacks: split k − Σ d_l by the max-min rule (equal slacks, remainder to the earliest components).
Theorem B' (necessity). If Σ d_l > k, no valid receptive causal delegation exists for this query. Proof: suppose one
exists; by receptiveness and causality pick causal strategies f_i with graph(f_i) ⊆ S_i. Take t >= k and two
environment traces identical before t: trace 1 has ¬φ everywhere, trace 2 has φ at t and ¬φ elsewhere. Run the
strategies on both. For τ ∈ [t, t+k], C_n's output at τ depends on inputs up to τ − d_n, which depend on inputs up to
τ − d_n − d_{n−1}, ..., up to τ − Σ d_l < t, so the outputs of C_n agree on [t, t+k] in both runs. Both composed
traces satisfy A_P and every S_i, hence G_P by (C1). In run 1 the quiet conjunct forces ψ̄ at every τ ∈ [t, t+k]
(apply it at τ − k); in run 2 the response conjunct forces ψ at some τ ∈ [t, t+k]. ψ and ψ̄ are disjoint:
contradiction. Hence for this query shape: delegable iff Σ d_l <= k.
Expected outputs (script, Z3-verified), relay instance k = 2:
 - delays (0,0): rule picks s_R = s_D = 1. Radio: □_[0,2](|r| > 1/2 → ◇_[0,1] |m| >= 1/2) ∧ □_[0,2](□_[0,1] |r| <= 1/2 → ◇_[1,1] |m| <= 1/4);
   Display: □_[0,3](|m| >= 1/2 → ◇_[0,1] |d| >= 2/5) ∧ □_[0,3](□_[0,1] |m| <= 1/4 → ◇_[1,1] |d| <= 1/5).
   Z3: (C1) holds; with s_R = s_D = 2 (budget exceeded) Z3 returns a violating trace.
 - delays (1,1): s_R = s_D = 0. Radio: □(|r| > 1/2 → ◇_[1,1] |m| >= 1/2) ∧ □(|r| <= 1/2 → ◇_[1,1] |m| <= 1/4);
   Display likewise with d. Z3: (C1) holds. With k = 1: Theorem B' applies; Z3 confirms by checking that the two-run
   argument's finite instance is UNSAT (encode: two environment traces, shared outputs up to the causal prefix,
   G_P required of both).

## 5. What the document must NOT contain
No references to any file outside this directory. None of these words: EARS, prior (except "prior width" if ever
needed, which it should not be), Display*, decider, leaky, head-band, R*, UD, announce, certifier, informed set,
ghost, cut set, Hoare, triple, interpolant, network coding, quantizer, capacity theorem, orchestrator, agent, note.
Allowed words that look like the banned ones: 'quiet', 'trigger', 'response'.
No literature section beyond: Benveniste et al. 2018 (contract definitions) and, in one sentence in the
introduction, the statement that Pacti-style quotient chaining from trivial contracts returns the empty obligation
on the relay (that is the Lemma of §1 in algebraic clothing).
Structure: 1 Problem. 2 Definitions and running examples. 3 Validity of a delegation (theorem + proof).
4 Conjunctive queries: algorithm, soundness, choice rule, relay and fan-in worked from input to output.
5 A temporal query: the degenerate always-respond delegation, the quiet conjunct, counterexample to naive distribution,
  algorithm, soundness, necessity, relay with deadline worked for both delay settings.
6 Which components get contracts, and when none exists. 7 Limitations (fan-out, completeness unproved, general
∨/◇ beyond the chain shape, cycles for temporal choices, unbounded horizon). 8 Reproduction: the one command,
and what the script prints. Total ≈ 8 pages, 11pt.

## 6. The script
`scripts/decompose.py`, Python 3, needs only z3-solver, numpy, scipy (in ./.venv). Structure:
  - data classes Architecture (variables, types, components with in/out/delay), Band query, Temporal chain query;
  - unroll(); cone_of_influence(); the LP of §3 with scipy.optimize.linprog (highs); water-filling; the gain LP;
  - emit_contracts() returning formulas as plain strings AND as Z3 expressions;
  - verify(): Z3 checks of (C1) (unsat of A_P ∧ types ∧ ⋀G_i ∧ ¬G_P), receptiveness (∀ inputs ∃ outputs, per
    component, with the delay prefix) via Z3 quantifiers or the closed form (rec) cross-checked, and for Part B
    bounded-horizon (C1) and the Theorem B' impossibility;
  - main(): runs relay, fan-in, relay-with-deadline (0,0) and (1,1), prints the emitted contracts in readable form,
    then the Z3 verdicts, exits nonzero if any verdict fails. Under 600 lines. No other files needed.
