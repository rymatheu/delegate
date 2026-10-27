# Specification v3: template-free decomposition of a general bounded PolySTL query (2026-10-18)

Author's requirements (verbatim intent): no assumed templates for delegated specs; must work for general
PolySTL contract queries; "typed" ports means only that variables are distinct and each has a known owner;
no numeric range bounds exist; only the graph and the query are given.

Deliverables: docs/decomposition.pdf (source docs/decomposition.tex, about 8–10 pages) and
scripts/decompose.py (run: `.venv/bin/python scripts/decompose.py`, prints the emitted contracts for every
example and the Z3 verdicts, exit 0 iff all verdicts hold). Nothing else. Build the script first.

## 1. Setting

- V: finite set of real-valued variables, each with exactly one owner: a component (its writer) or the environment.
  Component i: in(i), out(i), ports(i) = in(i) ∪ out(i), delay d_i ∈ {0,1} (output at t may depend on inputs at
  times ≤ t − d_i and own outputs at times < t). Horizon H; column = (v,t), t ∈ {0..H}. Traces are arbitrary reals.
- PolySTL (bounded): atoms a^T x_t ≤ b over the full vector at ONE time; ¬, ∧, ∨; □_[a,b], ◇_[a,b] with bounded
  integer intervals. Unrolling turns a formula into a Boolean combination of time-stamped atoms (an atom at time t
  is the PolySTL formula ◇_[t,t] μ). Conversely any Boolean combination of time-stamped atoms over a set of
  variables W is a PolySTL formula over W. So "PolySTL formula over ports(i)" = "Boolean combination of
  single-time linear atoms over the columns of ports(i)". Cross-time atoms (relating x(t) and x(s), s ≠ t) are
  NOT PolySTL. This matters for delays (§4).
- Contract (A_i, G_i) over ports(i); S_i = ¬A_i ∨ G_i. Query P = (A_P, G_P). Valid: (C1) A_P ∧ ⋀S_i ⊨ G_P,
  (C2) A_P ∧ ⋀S_i ⊨ A_j ∀j. Receptive: for every input history there is an output history in S_i.
  Causal: it can be produced step by step respecting d_i. Acceptable = valid + receptive + causal.
  Theorem 1 (valid = refinement of P by the composition, Benveniste et al. 2018 definitions) with proof.
- Projections, for a formula Q and a column set W: the universal projection Π_W(Q) := ∀(columns ∉ W). Q and the
  existential projection π_W(Q) := ∃(columns ∉ W). Q. Both are computed by linear quantifier elimination
  (Z3 tactic qe2; cross-check each result against its input by a validity query). Fact (prove it): if Q is a
  Boolean combination of single-time atoms and the eliminated columns are coupled to the kept columns only through
  single-time atoms, the result is again a Boolean combination of single-time atoms, hence PolySTL.
  (Fourier–Motzkin combines two atoms only when they share an eliminated column; both are then at that column's time.)

## 2. The method for a DAG of delay-0 components (the core)

Notation. N := the support = components with a directed path (writer→reader edges) to a writer of a variable
occurring in G_P. Components outside N get (true,true) [Lemma: they never affect (C1)]. Order N topologically
i_1, …, i_p (ties broken by name; say so). For k = 1..p define
  rest_k := {i_k, …, i_p},   private_k := columns of ports(i_k) not belonging to ports(rest_{k+1}),
  edge_k := columns of out(i_k) read by some component in rest_{k+1}.
(private_k = i_k's inputs that no later component reads, plus i_k's outputs that no later component reads.)
Also env_k := environment columns read by rest_{k+1} but not by i_k (what the rest sees and i_k does not).

Recursion. Q_1 := G_P (over all columns). For k = 1..p−1:
 (a) Needed forms. Collect the atoms of Q_k. For each atom a^T x_t ≤ b take its part on private_k at time t,
     the row vector a|_{private_k,t}. Keep the nonzero ones; take a maximal linearly independent subset in order of
     first occurrence (rank ρ_k(t) per time t). Call them L_k(t) (a ρ_k(t) × |private_k(t)| matrix).
     These are the query's own linear forms of what only i_k sees.
 (b) Capacity. e_k(t) := number of edge_k columns at time t. If ρ_k(t) > e_k(t) for some t, STOP and report:
     "component i_k must forward ρ_k(t) independent linear forms of {private variables} at time t but has only
     e_k(t) edge variables" (non-delegable by forwarding; list the forms). Otherwise assign the forms to the first
     ρ_k(t) edge columns in variable-name order (a labelling convention, state it).
 (c) Interface relation, with a tolerance ε ≥ 0 shared by every interface:
        I_k(ε) := ⋀_t ⋀_{j≤ρ_k(t)} | m_{k,j}(t) − L_k(t)_j · private_k(t) | ≤ ε.
     Edge columns beyond ρ_k(t) are unconstrained. I_k is a conjunction of single-time atoms over ports(i_k).
 (d) Local feasibility (shadow). Σ_k := the set of ports(i_k)-traces that the rest can complete whatever the
     environment it alone sees does:  Σ_k := Π_{ports(i_k)} ( ∃ outputs of rest_{k+1} . (A_P → Q_k) )
     computed as: first π over the outputs of rest_{k+1}, then Π over env_k. If this is simpler in your
     implementation, compute ∀ env_k ∃ out(rest_{k+1}) directly with qe2 on the alternation.
 (e) Emit  G_{i_k} := I_k(ε) ∧ Σ_k,   A_{i_k} := π_{in(i_k)}(A_P)   (true if no environment input).
 (f) Remaining query. Q_{k+1} := Π_{ports(rest_{k+1})} ( (A_P ∧ I_k(ε) ∧ Σ_k) → Q_k ), eliminating private_k.
     By the Fact in §1 it is PolySTL over ports(rest_{k+1}). Simplify with Z3 (ctx-solver-simplify or
     simplify+propagate) so it is readable; cross-check equivalence.
 Last component: G_{i_p} := Q_p (over ports(i_p)), A_{i_p} := π_{in(i_p)}(A_P).

Theorem 2 (soundness). For every ε ≥ 0 the emitted delegation satisfies (C1) and (C2).
Proof: (C2): A_P ⊨ π_{in(i)}(A_P). (C1): by induction on k, A_P ∧ ⋀_{j≤k} G_{i_j} ∧ Q_{k+1} ⊨ Q_k (definition of
Π and the implication), so A_P ∧ ⋀_i G_i ⊨ Q_1 = G_P. Write it out.
Receptiveness is NOT guaranteed by construction; it is decided per component by one quantified sentence
∀ inputs ∃ outputs (time-stepwise alternation for causality) and the procedure reports the verdict.
Theorem 3 (exact forwarding). With ε = 0 (and no capacity STOP), the delegation is receptive and causal iff the
query is centrally realizable on the support, i.e. ∀ env ∃ out(N) causal . (A_P → G_P) holds AND each Σ_k is
nonempty on reachable inputs. Prove at least the "if" direction carefully (with ε = 0 every later component can
reconstruct the private columns exactly, so the local problems chain); if the "only if" needs more hypotheses,
state exactly what you proved and label the rest a conjecture.

Choice of ε (the only free number, fixed by a symmetric rule, not by a template). Define the slack of an
obligation S over ports(i) as the largest δ ≥ 0 such that some causal strategy's outputs can be perturbed by up
to δ in every output coordinate and still satisfy S: slack(S) = sup{δ : ∀ inputs ∃ outputs ∀ η (|η|_∞ ≤ δ) :
(inputs, outputs + η) ∈ S}, a quantified LRA sentence for each fixed rational δ. Rule: ε* := the largest ε such that
every emitted obligation has slack ≥ ε (interfaces have slack exactly ε by the forwarding strategy; the last
component's slack decreases in ε). Compute by bisection on ε with a fixed tolerance 1/1024 and report the rational
found and the two verdicts bracketing it. This equalises implementation tolerance across the chain; it assumes no
shape. If ε* = 0 the delegation is exact forwarding.

Worked examples (script must compute; document must show every intermediate formula):
 E1 Relay. r env; Radio r→m; Display m→d; H = 0; A_P = |r| ≤ 1; G_P = |d − r| ≤ 1/2.
    N = {Radio, Display}, order Radio, Display. private_1 = {r}, edge_1 = {m}, form L = [1] (from the atom d − r).
    I_1 = |m − r| ≤ ε. Σ_1 = π_m,r(∃d: |d − r| ≤ 1/2) = true. Q_2 = Π_{m,d}(|r| ≤ 1 ∧ |m − r| ≤ ε → |d − r| ≤ 1/2):
    expected (compute!) for 0 ≤ ε ≤ 1/2: { |m| ≤ 1 − ε ∧ |d − m| ≤ 1/2 − ε } ∨ { 1 − ε < m ≤ 1 + ε ∧ 1/2 ≤ d ≤ m + 1/2 − ε }
    ∨ { −1 − ε ≤ m < −1 + ε ∧ m − 1/2 + ε ≤ d ≤ −1/2 } ∨ { |m| > 1 + ε }  (the last: no r is consistent).
    Slack of Q_2 = 1/2 − ε (bisection must find ε* = 1/4). Emitted: Radio (|r| ≤ 1, |m − r| ≤ 1/4),
    Display (true, Q_2 at ε = 1/4) printed in full. Note the Display obligation is NOT a band: it is what the
    projection returns. Z3: (C1), (C2), receptive, causal.
 E2 Fan-in. s1,s2 env; A s1→a; B s2→b; Fuser a,b→f; Logger f→l; H = 0; A_P = true; G_P = |f − s1 − s2| ≤ 1.
    N = {A, B, Fuser}; Logger (true,true). Order A, B, Fuser. I_A = |a − s1| ≤ ε, I_B = |b − s2| ≤ ε;
    Q_Fuser = |f − a − b| ≤ 1 − 2ε (compute); ε* = 1/3. Print all.
 E3 Three-stage chain. r env; C1 r→m1; C2 m1→m2; C3 m2→d; H = 0; A_P = |r| ≤ 1; G_P = |d − r| ≤ 1/2.
    Shows forwarding of a forwarded form: private_2 = {m1}, the atom of Q_2 has a part on m1, so L_2 = [1],
    I_2 = |m2 − m1| ≤ ε. ε* = 1/6 expected. Print all three obligations.
 E4 A disjunctive query (general Boolean structure, no template). Relay graph, H = 0, A_P = |r| ≤ 1,
    G_P = (r ≥ 0 → d ≥ 1) ∧ (r < 0 → d ≤ −1) ∨ |d − 2r| ≤ 1/4  (parenthesise as (∧) ∨ atom; it is one formula with
    atoms r ≥ 0, d ≥ 1, d ≤ −1, |d − 2r| ≤ 1/4). Forms on private_1 = {r}: from r ≥ 0 the form r; from d − 2r the
    form r (dependent): ρ = 1, I_1 = |m − r| ≤ ε. Q_2 computed by qe2; print it; ε* by bisection; verify.
 E5 Capacity failure. r1, r2 env; Radio r1,r2→m (one edge variable); Display m→d1,d2; G_P = |d1 − r1| ≤ 1/2 ∧
    |d2 − r2| ≤ 1/2 (A_P = |r1| ≤ 1 ∧ |r2| ≤ 1). Forms r1, r2 independent: ρ = 2 > e = 1: STOP with the report.
    Also show by Z3 that no acceptable delegation exists where Radio's obligation is a single polytope? NO: that was a
    template-relative claim; do not claim it. Only report the forwarding obstruction and state in the document
    that this is an obstruction for the forwarding method, not a proof that no delegation exists.

## 3. Delays (d_i = 1): what PolySTL can and cannot express

With d_i = 1 the exact forwarding m(t+1) = L private(t) is a cross-time relation and is NOT a PolySTL formula.
So continuous information cannot be forwarded across a delayed edge in this specification language. What can be
forwarded is finite information: the truth values of atoms. Rule: if every atom of Q_k with a nonzero part on
private_k is PURELY over private_k (no part on later components' columns), then the rest needs only the truth
values of those atoms. Let μ_1..μ_q be these atoms (at time t). Forward them with delay through disjoint regions
of one edge variable m: choose 2^q pairwise disjoint intervals R_c of m (one per truth assignment c), e.g.
R_c := [2c, 2c+1] for c = 0..2^q−1, and emit
   I_k := ⋀_t ⋀_c ( (⋀_j μ_j(t)^{c_j}) → ◇_[1,1] (m ∈ R_c) )    (PolySTL: single-time atoms under ◇_[1,1]),
and continue the recursion with Q_{k+1} := Π_{ports(rest)}((A_P ∧ I_k ∧ Σ_k) → Q_k) exactly as before (it stays
PolySTL: the eliminated columns private_k(t) are coupled to the rest only through the atoms μ_j(t), which I_k ties
to m(t+1) by Boolean structure, not by a cross-time atom). If some atom mixes private_k with later columns and
d_{i_k} = 1, STOP and report "forwarding the form … across the delay-1 edge of i_k is not expressible in PolySTL".
Theorem 4: soundness of this step (same induction). Example:
 E6 Relay with a deadline. Delays (1,1), H = 4, A_P = true,
    G_P = □_[0,2]( |r| > 1/2 → ◇_[0,2] |d| ≥ 2/5 ) ∧ □_[0,2]( □_[0,2] |r| ≤ 1/2 → ◇_[2,2] |d| ≤ 1/5 ).
    (First conjunct: a trigger gets a response within 2 steps; second: no trigger in the last 2 steps ⇒ quiet.
    Without the second conjunct the delegation "Display always outputs 1, Radio nothing" is acceptable: show this
    as a Lemma, it is why the second conjunct is there.) The only atom on private_Radio = {r} is |r| > 1/2 (i.e.
    r > 1/2 ∨ r < −1/2 as atoms; treat the two atoms r > 1/2, −r > 1/2 → q = 2, or merge them into one Boolean
    "trigger" flag if the rest only needs their disjunction: implement the general 2^q version and note that
    unused regions are harmless). I_Radio := □( trigger(t) → ◇_[1,1] m ∈ R_1 ) ∧ □( ¬trigger(t) → ◇_[1,1] m ∈ R_0 ).
    Q_Display := Π_{m,d}((I_Radio ∧ Σ_Radio) → G_P), computed by qe2 and printed (it should say: if m ∈ R_1 at t then
    some |d| ≥ 2/5 in [t, t+1]... and the quiet part), verify (C1), (C2), receptive, causal, with the
    causal alternation for delay 1. Also run the same query with delays (0,0): then the forward method of §2
    applies with the continuous form r itself (ρ = 1): I = |m − r| ≤ ε, Q_Display by qe2, ε* by bisection. Print both.
    And run k = 1 with delays (1,1) and show the procedure's Display obligation is not receptive (Z3), reported.

## 4. Document structure (≈ 8–10 pages, 11pt, one notation)
 1 Problem (verbatim). 2 Definitions (§1 here), projections and the PolySTL-closure Fact with proof, Theorem 1.
 3 Why the pure algebra cannot choose: Lemma (relay: Π_{m,d}(A_P → G_P) is empty), and the statement that the set of
   acceptable delegations has no greatest element (relay: (ε_R, ε_D) = (0.2,0.3) and (0.3,0.2) both acceptable,
   their pointwise union not: give the Z3-checked counterexample), hence a rule is needed; ours is max-min slack.
 4 The method (§2): recursion, Theorem 2 with proof, Theorem 3 with proof of what is proved, the ε rule.
 5 Worked E1 (every intermediate formula shown), E2, E3 briefly, E4 (disjunctive) with the computed Q_2 printed, E5.
 6 Delays (§3): the expressiveness limit, the finite-information forwarding, Theorem 4, E6 both delay settings.
 7 Which components get contracts; what is reported when the method stops (capacity, inexpressible, non-receptive).
 8 Limitations: forwarding is sufficient not necessary (a coarser encoding might exist); receptiveness checked not
   guaranteed for ε > 0; QE cost exponential; cycles not treated (a delay-1 component on every cycle would allow
   time-expansion, not done); unbounded horizon not treated.
 9 Reproduction: the command and the verbatim printed contracts and verdicts.
Banned words: EARS, prior, template (except in "no template is assumed"), band (except when describing E1's
Radio interface as "a tolerance ε around the forwarded form"), decider, flag (use "region"), ghost, Hoare,
interpolant, network coding, quantizer, capacity theorem, orchestrator, agent, note(s), any path outside this dir.

## 5. Script
scripts/decompose.py: Architecture + PolySTL AST (atoms with rational coefficients, Not/And/Or/Always/Eventually),
unroll, support, topological order, needed forms by rank (fractions.Fraction Gaussian elimination), interface
relations (continuous for delay 0, region-based for delay 1), projections with Z3 qe2 cross-checked (assert
equivalence of qe2 output with the quantified input via a validity check), simplification, receptiveness/causality
by quantified Z3 sentences with the right alternation, slack by bisection, pretty-printer that prints obligations as
PolySTL (atoms at time t printed as "@t:" or as ◇_[t,t]). main() runs E1–E6 and the no-greatest-element check, prints
contracts and verdicts, exit 0 iff all as expected. ≤ 900 lines. Only z3-solver, numpy (optional), fractions.
