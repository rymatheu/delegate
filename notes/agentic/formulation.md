# Delegation by proposal and check

19 October 2026. Internal note on the author's question: can per-component delegate contracts be computed by
proposers (language-model or symbolic), subject to the constraints of the contract calculus, with a verifier
deciding acceptance? Notation is that of `docs/complete.tex` throughout. Every verdict quoted in Section 8 is
printed by one command, `.venv/bin/python notes/agentic/governor_checks.py` (0.3 s, 101 verdicts, exit 0 iff
all are as expected; saved output in `notes/agentic/governor_checks.out`). Times are machine-dependent and are
quoted only for scale.

## 0. The answer in brief

**Yes, and the calculus already has the right shape for it.** `complete.tex` splits the problem in two parts. The
first is a set of conditions that says exactly which families of contracts are correct answers: validity (V1),
(V2), and receptiveness and causality (R), (K). The second is a *selection*, made there by fixed rules (steps 2
to 7), because no best answer exists (the proposition "no greatest solution"). The agentic formulation keeps the
first part unchanged as a verifier and replaces the fixed selection rules with a search. Three facts, proved
below, make this worth doing:

1. For a concrete proposed family of quantifier-free formulas, (V1) and (V2) are validity checks in
   quantifier-free linear real arithmetic. (K) is a check over **one component's ports**. If the proposal comes
   with an explicit causal strategy, (K) is quantifier-free as well. No check eliminates quantifiers over the
   variables a component cannot see, and that elimination is what makes the sweep expensive.
2. The quotient and the projection never have to be computed. Whether a proposal refines
   $\rho_{\mathrm{ports}(i)}(P/\bigotimes_{j\ne i}C_j)$ takes two quantifier-free validity checks, and whether a single
   local history is allowed by it takes one quantifier-free satisfiability check.
3. When an acceptable delegation exists, there is one in a simple normal form: graphs of piecewise-affine causal
   strategies. For that form the whole check is a single quantifier-free validity. So a fair enumeration
   semi-decides existence at **every** horizon. `complete.tex` states the semi-decision only for $H=0$.

What is lost: maximality, canonicity (unless the proposer is a deterministic enumerator), and any guarantee of
termination outside nested architectures, where $\Phi$ and the seed still decide.

On the speed governor at $H=2$, each check of each proposal took at most 6 ms. The sweep on the same instance
takes 71 s inside the one command `scripts/delegate.py` and 440 s when run alone
(`notes/agentic/sweep_timing.py`).

## 1. Objects (recalled)

- $V$: the finite set of real variables, each written by one component or by the environment. Component $i$ reads
  $\mathrm{in}(i)$ and writes $\mathrm{out}(i)$, and $\mathrm{ports}(i)=\mathrm{in}(i)\cup\mathrm{out}(i)$. Time is discrete,
  $t\in\{0,\dots,H\}$, and $v(t)$ is a timed variable.
- $\mathcal L$: Boolean combinations of atoms $\sum_v a_v v(t)\le b$ with rational coefficients and one time per
  atom. Bounded PolySTL compiles into $\mathcal L$ by $[\psi]_0$.
- A contract is $(A,G)$, saturated as $(A,S)$ with $S:=\neg A\vee G$. The query is $P=(A_P,G_P)$.
- $N$: the components that write a variable of $G_P$, together with every component that has a path to one of
  them. (Scope): every variable of $A_P$ or $G_P$ is a port of some component in $N$.
- For component $i$ and a family of sets $S_j$: $X_i$ is the set of timed variables $v(t)$ with
  $v\notin\mathrm{ports}(i)$ (the timed variables $i$ cannot see), and $R_i:=A_P\wedge\bigwedge_{j\ne i}S_j$ (what the
  query's assumption and the others' sets allow).

## 2. The constraint set

A proposal is a family $\{(A_i,G_i)\}$ over all components, optionally with a causal rule list $f_i$ for each
component (defined below). Put $S_i:=\neg A_i\vee G_i$. The family is **accepted** iff all of the following hold:

| | constraint | how it is checked |
|---|---|---|
| (C0) scope | $(A_i,G_i)=(\mathsf{true},\mathsf{true})$ for $i\notin N$ | by construction |
| (C1) ports | $A_i,G_i\in\mathcal L$ mention only $v(t)$, $v\in\mathrm{ports}(i)$, $t\le H$ | syntactic |
| (C2) saturation | $\neg A_i\models S_i$ | true by the definition of $S_i$; nothing to check |
| (C3) = (V1) | $A_P\wedge\bigwedge_iS_i\models G_P$ | $A_P\wedge\bigwedge_iS_i\wedge\neg G_P$ unsat |
| (C4) = (V2) | $A_P\wedge\bigwedge_iS_i\models A_j$ for every $j$ | $A_P\wedge\bigwedge_iS_i\wedge\neg A_j$ unsat |
| (C5) = (K) | $\forall\mathrm{in}_i(0)\exists\mathrm{out}_i(0)\cdots\forall\mathrm{in}_i(H)\exists\mathrm{out}_i(H)\,S_i$; this implies (R) | alternation over $\mathrm{ports}(i)$, or a certificate |

By the validity-conditions proposition and the definition of *acceptable* in `complete.tex`, (C1) to (C5) say
exactly "acceptable delegation". The following lemma shows that (C0) loses nothing.

**Lemma (scope restriction).** Assume (Scope). If a family is acceptable, it stays acceptable when every
$C_i$ with $i\notin N$ is replaced by $(\mathsf{true},\mathsf{true})$.

*Proof.* Let $Z$ be the timed variables written by components outside $N$. A writer of an input of a component in
$N$ is itself in $N$, so no $S_j$ or $A_j$ with $j\in N$ mentions $Z$. By (Scope), neither $A_P$ nor $G_P$ does.
Let $\Psi:=\bigwedge_{i\notin N}S_i$. Fix all timed variables outside $Z$. Go through the components outside $N$
in a topological order: each one's inputs are already fixed, so (R) gives output histories in its $S_i$.
Therefore $\exists Z\,\Psi\equiv\mathsf{true}$. Now let $\Xi:=A_P\wedge\bigwedge_{j\in N}S_j$ and let $\varphi$ be any
formula free of $Z$. If $x\models\Xi\wedge\neg\varphi$, change $x$ on $Z$ so that it satisfies $\Psi$; this leaves
$\Xi$ and $\varphi$ unchanged. So $\Xi\wedge\Psi\models\varphi$ iff $\Xi\models\varphi$. Taking $\varphi=G_P$
gives (V1), and taking $\varphi=A_j$ for $j\in N$ gives (V2). The trivial contracts satisfy (V2) and (K)
outright. ∎

Inside $N$, a proposer may also return $(\mathsf{true},\mathsf{true})$. Which members of $N$ get a non-trivial contract is a
choice (Section 3).

**Causal rule lists (the certificate for (K)).** A causal rule list for component $i$ assigns to each output $y$
of $i$ and each time $t\le H$ a term $f_{y,t}$ = "if $\pi_1$ then $c_1$, else if $\pi_2$ then $c_2$, …, else
$0$". Each region $\pi_l$ is a formula of $\mathcal L$ over the inputs of $i$ at times $\le t$, and each value
$c_l$ is affine, with rational coefficients, in the inputs of $i$ at time $t$.

**Lemma (certificates).** (a) If $S_i[y(t):=f_{y,t}]_{y,t}$ is valid, then (K) holds for $S_i$. (b) If (K)
holds for $S_i\in\mathcal L$, then a causal rule list with this property exists.

*Proof.* (a) The rule list is a causal strategy, because each $f_{y,t}$ reads only inputs at times $\le t$.
Validity says the trace it produces from every input history lies in $S_i$.

(b) Eliminate the quantifiers of the (K) sentence from the inside out, as in step 4 of `complete.tex`, and record
the witness of every existential timed variable using elimination with witnesses, part (b). By part (c) of that
lemma, each value is affine at its time and each region is in $\mathcal L$. Bounds of atoms with rational
coefficients are rational affine forms. The witness of $y(t)$ mentions only variables quantified before it:
inputs at times $\le t$, and outputs of $i$ at earlier times or earlier in the list. Substitute their witnesses
for those outputs, as in step 6. Each round brings in only earlier variables, so the substitution ends. The
induction in the (V1) part of the soundness theorem, applied to this one sentence, shows that from every input
history the trace produced lies in $S_i$. ∎

So requiring a certificate excludes no acceptable contract. It only moves the work for (K) from the verifier to
the proposer. Checking a certificate takes a syntactic test (each $f_{y,t}$ reads only inputs at times $\le t$)
and one quantifier-free validity over the input history of $i$.

**Lemma (the quotient is checked, not computed).** Fix every contract except $C_i$, and let
$Q_i:=\rho_{\mathrm{ports}(i)}\big(P/\bigotimes_{j\ne i}C_j\big)$.

(a) $S_{Q_i}\equiv\forall X_i\big(R_i\to G_P\wedge\bigwedge_{j\ne i}A_j\big)$ and $A_{Q_i}\equiv\exists X_iR_i$.

(b) $C_i\preccurlyeq Q_i$ iff $R_i\wedge S_i\models G_P\wedge\bigwedge_{j\ne i}A_j$ and $R_i\models A_i$. Both are
quantifier-free validity checks.

(c) A history $z$ of $\mathrm{ports}(i)$ satisfies $S_{Q_i}$ iff
$R_i\wedge(\mathrm{ports}(i)=z)\wedge\neg\big(G_P\wedge\bigwedge_{j\ne i}A_j\big)$ is unsatisfiable, and it satisfies
$A_{Q_i}$ iff $R_i\wedge(\mathrm{ports}(i)=z)$ is satisfiable. Each is one quantifier-free call over $X_i$.

*Proof.* (a) Write $(A',S')$ for the composition of the others, so $A'=\bigwedge_{j\ne i}A_j\vee\neg S'$ and
$S'=\bigwedge_{j\ne i}S_j$. The quotient has assumption $A_P\wedge S'=R_i$ and guarantee
$(S_P\wedge A')\vee\neg R_i$. On $R_i$ we have $S_P=G_P$ and $A'=\bigwedge_{j\ne i}A_j$, so the guarantee is
$R_i\to G_P\wedge\bigwedge_{j\ne i}A_j$. The two forms then follow from the definition of projection.

(b) This is refinement against (a). Here $S_i\models\forall X_i\varphi$ iff $S_i\models\varphi$, and
$\exists X_iR_i\models A_i$ iff $R_i\models A_i$, because $S_i$ and $A_i$ do not mention $X_i$.

(c) Immediate from (a). ∎

Since $R_i\wedge S_i=A_P\wedge\bigwedge_jS_j$, part (b) is (V1) together with (V2) for $j\ne i$. Under
saturation, $R_i\models A_i$ is equivalent to (V2) for $j=i$. So (b) is the whole validity check, seen from
component $i$. That is the adjunction lemma. Step 8 of the sweep computes $S_{Q_i}$ itself as a formula of
$\mathcal L$. Only that computation costs.

**Costs.** Write $n_V:=|V|(H+1)$ for the number of timed variables and $n_i:=|\mathrm{ports}(i)|(H+1)$.

| check | variables | quantifier blocks | formula given to the solver |
|---|---|---|---|
| (V1) | $n_V$ | none | $A_P$, $G_P$ and all proposals |
| (V2), per $j$ | $n_V$ | none | the same, with $A_j$ |
| (K) by certificate | $\lvert\mathrm{in}(i)\rvert(H+1)$ | none | $S_i$ with the rule list substituted |
| (K) by alternation | $n_i$ | $2(H+1)$ | $S_i$ only |
| refinement of $Q_i$ | $n_V$ | none | as for (V1), (V2) |
| membership in $Q_i$ of one local history | $n_V-n_i$ | none | as for (V1), with $\mathrm{ports}(i)$ fixed |
| sweep, step 8 for $i_k$ | eliminates $\lvert X_{i_k}\rvert\le n_V-n_{i_k}$ (fewer after substituting equations) | one block, but an equivalent quantifier-free formula must be produced | $A_P$, $G_P$ and all other current sets |

A quantifier-free check returns one bit, plus a model when the formula is satisfiable. Satisfiability in
quantifier-free linear real arithmetic is NP-complete (propositional satisfiability is the special case of
independent atoms $x_p\ge1$), but the solver never rewrites the formula: it searches truth assignments to the
given atoms and tests each by linear programming. Elimination, by contrast, must output a new formula. By the
cost remark of `complete.tex`, each eliminated variable multiplies the atom count $n$ by up to
$n(n-1)/2+3n+1$, so $k$ eliminations can reach about $n^{3^k}$ atoms. In the sweep, that output then becomes
part of $R_k$ for the next component. The case that did not finish had $k=12$ over two general formulas.

(K) by alternation also eliminates quantifiers. It does so only over $n_i$ variables and only in the proposal
$S_i$. A component with two inputs and two outputs at $H=2$ also has 12 timed variables, so with large proposals
this check can be expensive too. That is why the loop below asks for certificates.

## 3. What is fixed and what is chosen

**Fixed by the algebra.**

- Acceptance, (C0) to (C5).
- For each $i$ with the others fixed, the admissible contracts are exactly the $C$ with $C\preccurlyeq Q_i$ that
  satisfy (K).
- The quotient is the exact remaining obligation given the others, and the projection is exactly what can be
  said over $\mathrm{ports}(i)$: by the localisation lemma, $Q_i$ is the greatest contract over $\mathrm{ports}(i)$ that does
  the job. So the feedback "your contract must refine $\rho(P/\text{others})$" is not advice. It is the
  condition itself, and by the quotient lemma above it is checkable without quantifier elimination.

**Chosen.** In the relay, $D$ ($m=r$, $d=m$) and $D'$ ($m=-r$, $d=-m$) are both acceptable, and no valid family
contains both. So every procedure that returns one delegation makes a selection. `complete.tex` makes its
selection through:

- the lexicographically first nested ordering,
- the alphabetical pairing $\sigma_k$ of private variables to edge variables,
- the candidate order of the witnesses,
- the prefix order,
- the sweep order.

Concretely, a selection decides five things:

1. **The meaning of internal variables.** $e$ and $u$ do not occur in $P$, so their relation to $o$ ($e=o$;
   "$e\ge3$ when $o\ge3$"; $e=-o$) has to be invented.
2. **The division of labour.** Which component discharges which conjunct of $G_P$, and when. For example,
   whether the speed governor is fast at time 0 unconditionally or in response to the input.
3. **Which members of $N$ get $(\mathsf{true},\mathsf{true})$.**
4. **The split between assumption and guarantee.**
5. **The strength.** Anything from the graph of one strategy up to a maximal family.

These five, and nothing else, are what a proposer legitimately chooses.

**Why this is not "pulling functions out of thin air".** The proposer is outside the trust base. An output is
accepted only after:

- (V1) and (V2) are proved by unsatisfiability,
- (K) is proved by a certificate's validity or by the alternation check,
- (C1) passes the syntactic test.

By the validity-conditions proposition, that is a theorem about the output, whoever produced it. The agent plays
exactly the role that steps 2 to 7 already play in `complete.tex`: the one part of the procedure that is not a
contract operation, which `complete.tex` also justifies only by checking.

**Canonicity.** `SCOPE.md` asks for a choice made "canonically from (G, P) alone". A language-model proposer does
not give that: the same $(G,P)$ can produce different outputs on different runs. Two remedies:

- The proposer is a deterministic enumerator over a fixed candidate list, and the output is the first accepted
  candidate. The output is then a function of $(G,P)$ and the list order, which is canonical in the same sense as
  the witness candidate order of `complete.tex`.
- The language model is used only to search, and its output is recorded. The result is then reproducible from the
  record but not canonical. This does not meet the wording of `SCOPE.md`, and a report should say so.

## 4. The loop

**Participants.**

- **Verifier:** Z3, deterministic, sees everything.
- **Coordinator:** a deterministic program that sees everything and decides who is asked next.
- **Proposers $p_i$, $i\in N$:** each sees the query, the graph, its own ports, the current family, and every
  counterexample, projected onto $\mathrm{ports}(i)$. It outputs $(A_i,G_i)$ in bounded PolySTL or in $\mathcal L$
  (compiled by $[\cdot]_0$), together with a causal rule list $f_i$ where it can.

**The verifier** stops at the first failure, cheapest check first:

```
verify(F):
  for i in N:  if not ports_ok(i): return PORTS(i, offending timed variables)
  S_i := Or(Not(A_i), G_i) for every i
  for i in N:  if f_i given:  if not valid(S_i[f_i]): return K(i, input history of i)   # quantifier-free
               elif not K_alternation(S_i):          return K(i, -)                     # over ports(i) only
  for j in N:  if not valid(A_P & AND S -> A_j):     return V2(j, trace x)
  if not valid(A_P & AND S -> G_P):                  return V1(trace x)
  return ACCEPT
```

(V2) comes before (V1). If $x$ violates (V1) but also violates some $A_j$, saturation lets $j$ do anything at
$x$, so the fault is that $A_j$ was not discharged. Section 8 shows a run where this happens.

**What a counterexample means.**

**Lemma (no culprit).** If $x$ violates (V1), then for every $i$ the projection $x|_{\mathrm{ports}(i)}$ satisfies $S_i$
but not $S_{Q_i}$.

*Proof.* $x\models R_i\wedge S_i\wedge\neg G_P$. Apply the quotient lemma, part (c), with $z=x|_{\mathrm{ports}(i)}$
and completion $x$. ∎

So at a counterexample, every contract is too weak given the others, and the algebra does not say which one must
change. That is a policy decision for the coordinator, which is consistent with there being no greatest solution.

**Points are useless feedback; cells are not.** In the reals, a proposer can exclude finitely many points
without changing anything that matters, so repairing against individual points need not converge. The verifier
therefore generalises each counterexample:

- The **cell** of $x$ is the conjunction of the literals of all atoms of the negated obligation, each taken with
  its truth value at $x$. Every trace in the cell is a counterexample, because no atom changes truth inside it.
  Computing the cell costs one evaluation.
- The **projected cell** for $i$ is $\exists X_i\,\mathrm{cell}(x)$. This is elimination from a single
  conjunction: one polyhedron, the Fourier–Motzkin case of `complete.tex`, with no Boolean case split.
- Every history in the projected cell lies outside $S_{Q_i}$: by the quotient lemma, part (c), using the
  completion inside the cell. So the projected cell is a sound forbidden region, over $\mathrm{ports}(i)$, given the
  current others. It stays forbidden while the others' sets $S_j$ only grow: the completion still satisfies $R_i$
  and still violates $G_P$.
- Dually, a history of $\mathrm{ports}(i)$ outside $S_i$ but inside $S_{Q_i}$ is a positive example: $S_i$ may be
  enlarged to include it. Membership costs one quantifier-free call by part (c). An example stays positive while
  the others' sets only shrink and their assumptions only weaken, because then $R_i$ shrinks and $S_{Q_i}$
  grows.

**Routing (the coordinator's policy, deterministic):**

1. On a (V2) failure for $j$, or a (V1) trace that violates some $A_j$, ask the writers of the non-environment
   variables of $A_j$, in topological order, to exclude their projected cells. If $A_j$ mentions only environment
   variables, or every writer declines, ask $j$ to weaken $A_j$.
2. On any other (V1) failure, ask in reverse topological order, so the writers of variables of $G_P$ are asked
   first. The proposer asked may:
   - strengthen $G_i$ so that it excludes its projected cell while keeping (K);
   - add an assumption over $\mathrm{in}(i)$ that is false on the cell, which shifts the obligation to the writers of its
     inputs (case 1 in the next round);
   - decline, and the next component in the order is asked.
3. Rejected pairs (component, proposal) are recorded together with a hash of the others' state. Re-proposing a
   pair rejected under the same state counts as a decline.

**Weakening mode.** When an acceptable family is known (the seed, or an earlier accepted family), a proposal
$S_i'$ replaces $S_i$ if three quantifier-free checks pass: $S_i\models S_i'$, (V1), and (V2) on the new family.
(R) and (K) are inherited, because they survive enlarging $S_i$, so no (K) check is needed. Every state the loop
passes through is acceptable, so the loop can be stopped at any time with a correct answer. Proposers are given
positive examples. Deciding maximality means deciding $S_{Q_i}\models S_i$, that is, whether
$\exists z\,\big(\neg S_i(z)\wedge\forall X_i(\dots)\big)$ holds. That is an $\exists\forall$ question, and the
sweep step answers it by computing $S_{Q_i}$. Sampling can show that a family is not maximal, but never that it
is.

```
input: graph G, query P = (A_P, G_P), horizon H, budget B, proposers p_i
 1  N := relevant components;  if (Scope) fails: return "does not apply"
 2  C_i := (TRUE, TRUE) for i not in N                                   # scope restriction lemma
 3  if a nested ordering exists and Phi is cheap at this H:
 4      if Phi is false: return "none exists"                             # necessity theorem
 5      F := seed (steps 6-7 of complete.tex); mode := WEAKEN             # soundness theorem
 6  else:
 7      if Phi° is false for some topological ordering: return "none exists"
 8      F := {p_i.propose(P, G, ports(i)) : i in N}; mode := REPAIR
 9  best := F if verify(F) = ACCEPT else NONE
10  for round = 1 .. B:
11      if mode = REPAIR:
12          r := verify(F)
13          if r = ACCEPT: best := F; mode := WEAKEN; continue
14          i, region := route(r, F)                  # projected cell over ports(i), or input history for K
15          C := p_i.propose(..., forbidden := forbidden_i + region)
16          if (i, C, hash(F without i)) in rejected: C := DECLINE   # then route asks the next component
17          F := F with C_i := C
18      else:                                                          # WEAKEN
19          i := next component of N in a fixed cyclic order
20          Z := sampled histories z of ports(i) with z not in S_i and z in S_{Q_i}   # one call per z
21          if Z is empty for every i in one full cycle: break
22          C := p_i.propose(..., allowed := Z)
23          if S_i |= S_C and V1(F with C) and V2(F with C): F := F with C_i := C; best := F
24      log(round, i, raw proposal, parsed formula, verdict, counterexample, region)
25  return best with its certificates, or "not found within budget"
```

Lines 3 to 5 bring in the algorithmic route wherever it is cheap. On the failing instance, deciding $\Phi$ and
computing the seed were fast, so the loop would start there in weakening mode, which needs no (K) checks at all.

## 5. Guarantees

**Soundness.** If the loop returns $F$, then $F$ is acceptable, satisfies (C0), and each contract mentions only
its own ports.

*Proof.* $F$ is returned only after `verify` accepts (lines 9 and 13), or after a weakening step from an accepted
family (line 23). The weakening step checks (V1) and (V2), checks ports syntactically, and inherits (K) from
$S_i\models S_i'$. ∎

The trust base is:

- Z3's unsat answers in quantifier-free linear real arithmetic;
- Z3's answer to the (K) alternation, if that check is used instead of a certificate;
- the compiler $[\cdot]_0$ from PolySTL to $\mathcal L$.

An answer of `unknown` counts as a rejection.

**Normal form.** If an acceptable delegation exists, there is one in which every assumption is $\mathsf{true}$ and every
$S_i$ is the defining formula $\bigwedge_{y,t}[\![\,y(t)=f_{y,t}\,]\!]$ of a causal rule list with rational data.

*Proof.* The certificates lemma, part (b), gives rule lists whose traces lie in the given $S_i$. Their defining
formulas are in $\mathcal L$ (elimination with witnesses, part (c)) and define subsets of the $S_i$. So (V1)
survives, because it survives shrinking. (V2) is trivial with assumptions $\mathsf{true}$, and (K) holds by the rule
lists. ∎

**Semi-decision at every horizon (corollary).** Enumerate the tuples of causal rule lists with rational data
(a countable set) in any order in which each tuple appears. For each tuple, check (V1) for their defining
formulas. That is one quantifier-free validity, or equivalently $\forall(A_P\to G_P)$ with the outputs
substituted in topological order. The enumeration halts with an acceptable delegation iff one exists.

This extends the semi-decision remark of the scope section of `complete.tex` from $H=0$ to every $H$, and to
every acyclic architecture with zero delay. The extension uses only the certificates lemma. It is argued here and
is not yet in `complete.tex`.

**Completeness of the agentic loop.**

- **Nested architectures, (Scope) holds, $\Phi$ decided.** The loop is complete and terminates, but lines 3 to 5
  provide that, not the proposers. If $\Phi$ is too expensive at the given $H$, there is no completeness.
- **General architectures (forks).** The loop halts with a delegation whenever one exists iff the stream of
  proposals is fair over a countable set that contains the normal forms. A language-model proposer gives no such
  guarantee. Interleaving it with an enumerator (every $k$-th proposal from the enumerator) restores completeness,
  at a factor $k$ in rounds, and keeps whatever the language model finds sooner.
- **Non-existence.** The only test is the $\Phi^\circ$ refutation. It is sound but not complete: a true
  $\Phi^\circ$ proves nothing (the Left/Right example of `complete.tex`).
- So existence is semi-decided, non-existence is only refuted sometimes, and whether the general problem is
  decidable is open here.

**Termination.**

1. **Budget $B$.** The loop always stops. "Not found within budget" is not a refutation.
2. **Finite candidate space.** Fix $\mathcal K_B$: rule lists with at most $B$ pairs, regions with at most $B$
   atoms, coefficients from a finite set. Exhausting $\mathcal K_B$ stops with "none in $\mathcal K_B$". This is
   a refutation only relative to $\mathcal K_B$. As `complete.tex` says, no $B$ is known for which "none in
   $\mathcal K_B$" implies "none exists".
3. **Weakening mode.** It may run forever, through infinitely many strict weakenings, so it is stopped by the
   budget. Every state it passes through is acceptable.
4. **Repair mode** can cycle. For example, $j$ adds an assumption, its writer declines, and $j$ weakens the
   assumption again. Line 16 makes every (component, proposal, state of the others) occur at most once. Over a
   finite candidate space this ends the loop; over an infinite one, only the budget does.

**Reproducibility.**

- **Verdicts are deterministic.** Quantifier-free linear real arithmetic is decidable, and with no timeout Z3
  answers sat or unsat. Which verdict comes back does not depend on solver state. The models returned do depend on
  it. In `governor_checks.py`, the same script produced different counterexample models under different Python
  string-hash seeds, because formulas were built by iterating over sets. Sorting fixed this: four hash seeds now
  give byte-identical output apart from times. The same effect shows up in the algorithmic route: the sweep on the
  governor takes 71 s inside the one command and 440 s in a fresh process, and the seed printed today for $v(0)$
  is $\tfrac18$ where `docs/example.tex` shows $1$.
- **Artifacts.**
  - A run log (JSON lines): the prompt hash, model identifier, raw proposal text, parsed formula as SMT-LIB 2,
    verdict, counterexample as exact rationals, and Z3 version.
  - A certificate file: the graph, $P$, $H$, the final $(A_i,G_i)$, and the rule lists.
- **One command.** `verify.py certificate.json` re-checks (C0) to (C5), all quantifier-free when rule lists are
  present, and exits 0 iff all pass. It needs no proposer. Every number in a written report should be a verdict or
  a formula reproduced by this command.
- **Replay.** `replay.py log.jsonl` re-verifies each logged proposal. It checks each logged counterexample by
  evaluating it with exact rationals, rather than asking the solver for the same model again.
- **Proposers.** A symbolic proposer with a fixed enumeration order and fixed seeds reproduces the whole
  trajectory. A language-model proposer is not reproducible even at temperature 0, so its search is recorded, not
  re-run.

## 6. Comparison with the algorithmic route

**What the agents buy.**

- **No elimination over variables a component cannot see.** The cost of a check grows with the unrolled size of
  the proposals and the query. It does not grow with the number of eliminated variables, because there are none.
  The reactive family below, written as $\square$ formulas, unrolls to any $H$: (V1) took 0.5 ms at $H=2$ and
  12 ms at $H=80$ (324 timed variables), and the three (K) certificates took 1.3 ms and 16 ms.
- **Short contracts.** Proposals can be short PolySTL formulas. Compare the four-line lazy family below with the
  seed's nested if-then-else for $v$ and the sweep's printed output, both in `scripts/delegate.py`.
- **Concrete failures.** Every rejection comes with a trace, a cell, or an input history.

**What they lose.**

- **Maximality.** No quantifier-free test for maximality exists, and the sweep step is exactly that test. One
  consequence: the sweep *proves* that Perception need preserve only $o(1)\ge3$, while an agent's lazy family
  shows only that preserving it suffices.
- **Canonicity** (Section 3).
- **Completeness and termination** outside the nested case with $\Phi$ decided.

**Where the algorithmic pieces still belong.**

- $N$, (Scope) and the scope restriction lemma: always.
- $\Phi$: as a pre-check. It took 0.03 s on the governor and was fast on the failing instance. It yields "none
  exists" or, on nested orderings, the seed.
- The seed: as round 0, followed by weakening.
- $\Phi^\circ$: as the refutation test for forks.
- The sweep: only on small instances, or as an optional final step for a single component whose $X_k$ is small.
  The formulas in $R_k$ produced by agents are shorter than the seed's, so a final sweep step may be cheaper when
  started from an agent's family. This is a conjecture; I have not tested it.

## 7. Risks

1. **Variables outside the ports.** Caught syntactically by (C1), as are times above $H$. A certificate that
   reads a non-input, or an input at a later time, is also rejected syntactically (shown in Section 8).

2. **Valid but useless contracts.**
   - **$A_i=\mathsf{false}$.** Then $S_i=\mathsf{true}$, and (V2) for $i$ demands that $A_P\wedge\bigwedge_jS_j$ be
     unsatisfiable. *If $A_P$ mentions only environment variables and is satisfiable, and every $S_j$ satisfies
     (R), then $A_P\wedge\bigwedge_jS_j$ is satisfiable, so (V2) rejects $A_i=\mathsf{false}$.* (Proof: fix an
     environment history satisfying $A_P$, and choose outputs component by component in topological order using
     (R).) If $A_P$ mentions outputs, as in regression 2 of `scripts/delegate.py`, the calculus does accept
     families that make $A_P$ false. That is a property of the query. An optional non-vacuity check (is
     $A_P\wedge\bigwedge_jS_j$ satisfiable?) is one quantifier-free call.
   - **$G_i=\mathsf{false}$ with $A_i=\mathsf{true}$.** $S_i$ is empty, so (R) fails at every input history and (K) rejects it.
   - **Input pinning.** For example $\square(u=0\wedge v=0)$ for the Actuator, or the trace-pinning family of the
     "validity alone is empty" proposition. (R) fails at every other input history, and the certificate check
     returns one such history ($u\equiv-1$ in Section 8).
   - **What (R) and (K) do not catch.** Contracts that are acceptable but needlessly strong, such as copies
     $e=o$, a constant output that happens to work, or an assumption on the component's own outputs. These
     affect quality, not correctness, and weakening mode addresses them.

3. **Proposers blaming each other forever.** By the no-culprit lemma, assigning blame is a policy, not a fact.
   Routing is deterministic. Combined with the rejected-pairs record and the budget, this bounds the loop (see
   Termination).

4. **What a proposer may see.** The problem gives the *decomposer* the graph and the query. The restriction "only
   its own variables" applies to the delegated *contract*, not to what the decomposer reads; the sweep itself
   reads $G_P$ and all other contracts to compute each one. So a proposer may see $P$, the graph and the current
   family. Only its output is restricted, and (C1) enforces that. No leakage of information can make an accepted
   output unsound. Counterexamples are still projected, for two reasons. First, a proposer can use only what it
   can write, and values of non-port variables invite references that are rejected, or constants overfitted to
   one trace. Second, the projected cell is exactly the part a component can act on (quotient lemma, part (c)).
   One case falls outside the stated problem: if proposers stand for independent suppliers who must not learn the
   global query, that is a confidentiality requirement. The loop still works with such proposers, if they see
   only membership answers for $Q_i$, but the search becomes harder.

5. **Shared meaning of internal variables.** The writer and the readers of $e$ must agree on what $e$ means.
   Independent proposers cannot agree without communicating. In the loop, the meaning travels through
   assumptions: a reader states what it needs on its inputs, and (V2) obliges the writer to guarantee it
   (Section 8). With fan-in, an assumption over inputs from two writers is itself a smaller delegation problem, and
   the difficulties of forks reappear there.

## 8. Worked sketch: the speed governor at $H=2$

**The instance.** Perception reads $o$ and writes $e$; Controller reads $e$ and writes $u$; Actuator reads $u$ and
writes $v$. The query:

- $A_P=\square_{[0,2]}(0\le o\le5)$
- $G_P=\square_{[0,2]}(0\le v\le2)\wedge\square_{[0,1]}(o\le1\to\Diamond_{[0,1]}v\le\frac14)\wedge\square_{[0,1]}(o\ge3\to\Diamond_{[0,1]}v\ge1)$

**What a good proposer reasons.** There are four response obligations, for $t=0,1$:

- A close obstacle ($o\le1$) at time 0 or 1 can be answered blind, by $v(1)\le\frac14$.
- A clear road ($o\ge3$) at time 0 can be answered blind, by $v(0)\ge1$.
- A clear road at time 1 cannot be answered blind at time 1, because $v(1)$ is already slow. It must therefore be
  answered at time 2, with information, so the fact $o(1)\ge3$ must reach the Actuator by time 2.

This gives two proposals. All assumptions are $\mathsf{true}$. Certificates are in brackets.

**$D_{\rm react}$**, threshold-preserving and memoryless:

- Perception: $\square_{[0,2]}\big((o\ge3\to e\ge3)\wedge(o\le1\to e\le1)\big)$ [$e(t):=o(t)$]
- Controller: the same with $e\to u$ [$u(t):=e(t)$]
- Actuator: $\square_{[0,2]}\big(0\le v\le2\wedge(u\ge3\to v\ge1)\wedge(u\le1\to v\le\frac14)\big)$
  [$v(t):=1$ if $u(t)\ge3$, else $0$]

**$D_{\rm lazy}$**, where only $o(1)\ge3$ crosses the edges:

- Perception: $o(1)\ge3\to e(1)\ge3$ [$e(t):=o(t)$]
- Controller: $e(1)\ge3\to u(1)\ge3$ [$u(t):=e(t)$]
- Actuator: $\square_{[0,2]}(0\le v\le2)\wedge v(0)\ge1\wedge v(1)\le\frac14\wedge\big(u(1)\ge3\to v(2)\ge1\big)$
  [$v(0):=1$, $v(1):=0$, $v(2):=1$ if $u(1)\ge3$, else $0$]

**What the verifier printed.** All 101 verdicts were as expected.

- **Both families accepted.** Ports, (V1), (V2), and (K) both by certificate and by alternation over the
  component's ports all pass. For $D_{\rm react}$, (V1) took 1.1 ms, (V2) for all components 1.0 ms, each
  certificate at most 0.7 ms, and each alternation at most 5.9 ms. For each component of $D_{\rm react}$, the
  refinement of $\rho(P/\text{others})$ also holds, checked by the quotient lemma, part (b), without computing
  the quotient.
- **The swept family is checked by the same verifier.** The swept family of `docs/example.tex`, transcribed,
  passes (V1), (V2) and (K) by alternation, each in under 2 ms. $S_{\rm Actuator}$ of $D_{\rm lazy}$ entails the
  swept one, but $S_{\rm Perception}$ and $S_{\rm Controller}$ do not. So $D_{\rm lazy}$ is not inside the maximal
  family: maximal is not greatest.
- **Sampled quotient.** The local history $u\equiv0$, $v=(\frac18,1,\frac18)$ violates $D_{\rm lazy}$'s Actuator
  contract but is allowed by $\rho(P/\text{others})$, as one quantifier-free call shows. So $D_{\rm lazy}$'s
  Actuator is not maximal, and this history is a positive example for weakening. The history $v\equiv\frac18$ is
  forbidden. The completion shown is $o=(3,0,0)$: a clear road at time 0 that is never answered.
- **Weakening from forwarding.** Start from $e=o$, $u=e$ and $D_{\rm lazy}$'s Actuator. Weakening Perception to
  $o(1)\ge3\to e(1)\ge3$ and then Controller to $e(1)\ge3\to u(1)\ge3$ each passes "old $\models$ new" and (V1),
  with (K) inherited. All checks are quantifier-free. This recovers the conclusion of the sweep — only $o(1)\ge3$
  must be forwarded — as a sufficient condition rather than a proof of minimality. Weakening Perception further, to
  $\mathsf{true}$, fails (V1) with the counterexample $o=(0,3,0)$, $v=(1,0,0)$, projected to Perception as $o=(0,3,0)$,
  $e\equiv0$.
- **Repair with a cell.** Round 0 is $D_{\rm react}$ without Perception's conjunct $o\le1\to e\le1$. (V1) fails
  at $o=(0,\frac{11}8,0)$, $e=u\equiv\frac{11}8$, $v\equiv\frac58$. Each component's projection lies outside its
  quotient guarantee, which illustrates the no-culprit lemma. Perception's projected cell, computed in 2 ms, is
  $0\le o(0)\le1$, $1<o(1)<3$, $0\le o(2)<3$, and $1<e(t)<3$ for all $t$: a close obstacle reported as a middling
  estimate. The repaired guarantee excludes the whole cell.
- **Assume–guarantee round.** The Actuator assumes $\square(u\ge3\vee u\le1)$, a decisive command. (V2) fails at
  $u\equiv2$. (V1) also fails, at a trace that violates the Actuator's assumption, which confirms the reason for
  checking (V2) first. The writer of $u$, the Controller, adds $\square(u\ge3\vee u\le1)$ with the certificate
  $u:=3$ if $e\ge3$, else $0$. Every check then passes.
- **Rejections.**
  - Actuator proposes $\square(o\le1\to v\le\frac14)$: rejected by (C1), offending variable $o(0)$.
  - $A_{\rm Actuator}=\mathsf{false}$: (V2) fails at $o=e=u\equiv2$.
  - $(\mathsf{true},\mathsf{false})$: (K) fails.
  - Pinning, $\square(u=0\wedge v=0)$: (K) fails, with input history $u\equiv-1$.
  - A wrong certificate ($v(2)$ reading $u(2)$ instead of $u(1)$): fails at $u=(0,3,0)$.
  - A certificate in which $v(0)$ reads $u(1)$: rejected syntactically.

**Against the sweep.** On this instance, `scripts/delegate.py` decides $\Phi$ in 0.03 s and computes the seed
in about 0.02 s. The sweep then takes 71 s inside the one command
(`notes/agentic/delegate_instance_times.txt`) and 440 s alone (`notes/agentic/sweep_timing.py`). All checks of
`governor_checks.py`, including five families, the sampled quotients, a cell projection, and the horizon scan up
to $H=80$, run in 0.3 s.

**What did not run.** I did not implement the loop with a language model, `verify.py` or `replay.py`. The
proposals above are hand-written stand-ins for proposer output. The failing instance (three components, two
environment inputs, two terminal outputs) is not in this directory, so it was not tested.

---
**Correction (2026-10-19, later).** The sweep times quoted above (71 s inside the suite, 440 s alone) were measured
while `scripts/delegate.py` used Z3's virtual-substitution tactic `qe`. That tactic was found to return a
non-equivalent (too strong) elimination on the governor Actuator step; `qe()` now uses `qe2` with a sound cross-check,
and the whole suite, including the governor sweep, runs in about 2 s. The comparison "milliseconds versus a minute"
does not hold on the governor; the sweep's cost is an issue on the larger instance (three components, two environment
inputs, horizon 2), which did not finish in nine minutes.
