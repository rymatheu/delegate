# Temporal decomposition: a syntax-directed operator $D$ for full bounded PolySTL

_Slice: temporal (∨, ◇, U, nesting, EARS trigger/response). 2026-10-18. Checks: `scripts/polystl_decomp_check.py`
(93 checks, 0 failed, about 4 s; Z3 5.1, eliminations by `qe2` only, each one cross-checked by two decision paths)._

---

## 0. Results in brief

1. **$D$ is defined by cases on the NNF formula tree** (table in §3). Atoms go through the conjunctive agent's
   `split`, ∧ and □ distribute, and every disjunctive node (∨, ◇, U, R) goes through **one rule**, the
   *unified disjunction rule* (UD). UD has four parameters:
   - a branch budget $J'$;
   - a decider $k$;
   - an informed set $\mathrm{Inf}$;
   - a code of flags on existing edge variables.

   Static witness, decider/cover, and announcement are special cases of UD. Every output formula mentions
   only $\mathrm{ports}(i)$.
2. **Soundness (Thm 1).** For every annotation that meets its side conditions, $A_P\cap\bigcap_i D(P)_i\subseteq G_P$,
   proved by structural induction on trace sets. Assumptions are then computed last as shadows (the shadow assumption, foundations §5), which gives (C2).
   Realizability is a **local** check, one per component. A realizable output of $D$ is a **seed**, and the fixed-point
   sweep (foundations §9) makes it maximal. This supplies the seed the sweep needs for every query on which $D$
   succeeds.
3. **Naive distribution of ◇/∨/U is unsound** (Prop 2; Z3 counterexample on the relay).
4. **Decider rule** (§4.3). The decider must be able to *certify* the branch it picks from its own information, and it
   must *reach* every component that cannot cover all branches, within the timing budget. Canonical preference:
   static witness, then the unique actor, then the most-downstream admissible observer.
5. **Witness signals without new ports** (§4.4). An edge variable can carry flags iff, at the relevant time, the
   writer's other duties leave it a set of positive width on every reachable history. Then it carries **any finite
   number** of flags, by a comb of intervals (Prop 5). With zero width it carries none, except flags that can be
   derived from what the edge already carries.
6. **Information-fork theorem** (Thm 6, agreement lemma). Take two actors with disjoint, independent information
   and no path between them, and a query whose branches are mutually exclusive per actor. Then the query is delegable
   iff a *static* branch is. Example: no local delegation exists. A Z3 finite-sample UNSAT confirms it, and adding one
   edge makes $D$ succeed.
7. **EARS chain (Thm 4).** Query $\Box_{[0,T]}(\text{trig}\to\Diamond_{[0,k]}\text{resp})$ over $C_1\to\dots\to C_n$ with
   delays $d_l$. Each component gets a guarded response over its own ports: $C_1$ detects and encodes, the middle
   components relay, $C_n$ decodes and responds. The **window budget is additive**:
   $\sum_l(d_l+s_l)\le k$, the temporal analogue of $a+b\le0.5$. If the query also forbids spurious responses, it is
   delegable **iff** $\sum_l d_l\le k$, and $D$ attains this bound.
8. **Temporal assumptions** (§6). They flow forward by guarded-response arithmetic (liveness transfer). The forward
   image is a valid (C2) assumption that contains the shadow, and on the test instance it *equals* the shadow (Z3).
   Only ancestors shape a component's assumption.

---

## 1. Setting and what is reused

Architecture, types, horizon and query are exactly as in SCOPE.md and the setting of `theory/foundations.md` (foundations §1):
- components $i\in\mathcal C$ with $\mathrm{in}(i)$, $\mathrm{out}(i)$, $\mathrm{ports}(i)$, and delays $d_i\in\mathbb N$;
- every cycle contains a delay;
- environment variables $\mathrm{Env}$;
- typed traces on $[0,H]$;
- $P=(A_P,G_P)$, with $A_P$ over $\mathrm{Env}$.

A formula over $\mathrm{ports}(i)$ denotes a **cylinder**: a set of full traces that ignores the other variables.
$\mathrm{Ctx}:=A_P\wedge\mathrm{Types}$.

Reused without re-derivation (`theory/foundations.md`, cited as "foundations §n"):
- validity (C1) $A_P\cap\bigcap_iS_i\subseteq G_P$ and (C2) (the validity theorem, foundations §4);
- assumptions solved last: $A_j:=\pi_{\mathrm{in}(j)}(A_P\wedge\bigwedge_{i\ne j}S_i)$ (the shadow assumption, foundations §5);
- receptiveness and causality ("realizable") (foundations §7);
- the universal projection $\Pi_i$ and the shadow $\pi_i$ (foundations §6);
- the fixed-point sweep (foundations §9);
- the bounded unrolling of PolySTL into QF_LRA (PolySTL semantics, foundations §2).

Two proof rules are named below. (Seq) is the sequential rule: a cut formula over the interface is handed from upstream
to downstream. (Circ) is a time-inductive circular rule: each component may assume the others' guarantees at earlier
times.

**Normal form.** Push negation to atoms. A negated polytope $\neg(Ax\le b)$ is the disjunction $\bigvee_r a_r^\top x>b_r$,
so it becomes an ∨-node of strict rows. The grammar is then
$$\varphi::=\mu\mid\varphi\wedge\varphi\mid\varphi\vee\varphi\mid\Box_I\varphi\mid\Diamond_I\varphi\mid\varphi\,\mathcal U_I\,\varphi\mid\varphi\,\mathcal R_I\,\varphi ,$$
with $I=[a,b]$ bounded. An implication $\alpha\to\beta$ is the node $\neg\alpha\vee\beta$.

**Latency.** For a directed path $k=c_0\to c_1\to\dots\to c_m=i$ (where $c_{l-1}$ writes an edge variable that $c_l$ reads),
$\ell(\text{path})=\sum_{l=1}^m d_{c_l}$ is the delay from a value on $\mathrm{out}(k)$ to the earliest output of $i$
that can depend on it. $\ell(k\rightsquigarrow i)$ is the minimum over paths ($\infty$ if there is none).

**Information cone.** $\mathrm{info}(i)$ is the set of environment samples $(e,t)$ joined to $i$ by a path in the
time-expanded graph. By induction over that graph, which is acyclic because every cycle has a delay, the outputs of any
causal strategy of $i$ are functions of $\mathrm{info}(i)$ alone.

---

## 2. Atoms: ownership, split, and environment atoms as guards

### 2.1 The `split` interface (black box from the conjunctive slice)
For one row $\mu\equiv a^\top x\le b$ evaluated at time $t$ (possibly cross-time), `split` returns three things:
- an **owner set** $\mathrm{Own}(\mu)\subseteq\mathcal C$;
- local rows $\mu_i(\theta_i)$ over $\mathrm{ports}(i)$ for $i\in\mathrm{Own}(\mu)$, with time offsets that respect delays;
- a linear side constraint $\Lambda_\mu(\theta)$ on tolerances.

It satisfies

$$\text{(Sp)}\qquad \forall\theta\in\Lambda_\mu:\quad \mathrm{Ctx}\wedge\textstyle\bigwedge_{i\in\mathrm{Own}(\mu)}\mu_i(\theta_i)\ \models\ \mu@t .$$

A polytope atom is split row by row, and the pieces are conjoined.

**What the owner set is.** By the Farkas row decomposition (Theorem 1 of `theory/conjunctive-decomposition.md`) and
receptiveness (foundations §7), $\mathrm{Own}(\mu)$ has three properties:
- it contains the writers of the non-environment variables of $\mu$;
- it is closed under coefficient cancellation: a coefficient that one member puts on a variable not in $\mu$ is cancelled
  by the reader or writer of that variable;
- every member contributes through its outputs.

So $\mathrm{Own}(\mu)$ is the vertex set of a connected sub-hypergraph of the port graph that links
$\mathrm{vars}(\mu)$, oriented toward the writers. Relay example: $d-r=(d-m)+(m-r)$ gives $\mathrm{Own}=\{R,D\}$ and
$\Lambda:\theta_R+\theta_D\le0.5$.

With delays the split is time-shifted:
$$d(t)-r(t)=(d(t)-m(t{-}1))+(m(t{-}1)-r(t{-}2))+(r(t{-}2)-r(t)).$$
The last term is not anybody's obligation. It must be bounded by a row of $A_P$ (a rate bound on $r$): that is the
Farkas row $a_{0}$ contributed by $A_P$. Without such a row the atom is not delegable at all. From here on
`split` is used as given.

### 2.2 Environment atoms
An atom $\varepsilon$ with $\mathrm{vars}(\varepsilon)\subseteq\mathrm{Env}$ is nobody's obligation. It occurs in two roles.
- **Implied by $\mathrm{Ctx}$.** It is dropped ($D(\varepsilon)=\mathrm{true}$).
- **Branch condition.** It occurs inside a disjunctive node, as in $\neg\mathrm{trig}\vee\dots$ or
  $\Diamond(|r|\le0.5\wedge\dots)$. There it is **certified**: some component $c$ receives a *guard* $g_c$ over
  $\mathrm{in}(c)$. Together with the relay obligations $\rho$ of the components upstream of $c$ (if any), the guard implies the atom:
  $$\text{(Cert)}\qquad \mathrm{Ctx}\wedge\rho\wedge g_c\models\varepsilon .$$
  - Direct certification: $\mathrm{vars}(\varepsilon)\subseteq\mathrm{in}(c)$ and $g_c=\varepsilon$.
  - Derived certification: Display certifies $|r|\le0.5$ through Radio's band $|m-r|\le a$ with $g=|m|\le0.5-a$.

A guard constrains $c$'s *input*, so on its own it is not receptive (receptiveness, foundations §7). It is legitimate only inside a
decider's disjunction, and the local realizability check enforces this. In check `ii-b.static`, a static branch that
forces a guard on Radio's input is rejected exactly so.

**Guard weakening.** In $\neg\alpha\vee\beta$, $D$ may replace $\alpha$ by any $\alpha'$ with $\mathrm{Ctx}\models\alpha\to\alpha'$.
This is sound because $\neg\alpha'\vee\beta\models\neg\alpha\vee\beta$. It is used to replace a trigger by the part of
it that is causally observable in time. Example: $\Box_{[0,k]}\mathrm{quiet}$ is weakened to $\mathrm{quiet}@(t+k-\Delta)$.

---

## 3. The operator $D$

**Annotation.** An annotation $\kappa$ fixes the following:
- a `split` choice (owner set, normals, tolerances $\theta$) for every atom occurrence;
- a certifier and guard for every environment atom in branch position;
- a mode for every disjunctive node $\nu$.

Annotations are per syntax-tree node and uniform over the time instances generated by enclosing □. That uniformity is
what keeps the output a *temporal* formula rather than an absolute-time one; non-uniform annotations are allowed and give
absolute-time obligations.

**Output.** $D_\kappa(\varphi)=\big((\psi_i)_{i\in\mathcal C},\Lambda\big)$, with $\psi_i$ over $\mathrm{ports}(i)$
interpreted at the evaluation time of $\varphi$. A missing entry means $\mathrm{true}$.

### 3.1 The unified disjunction rule (UD)
A disjunctive node at time $t$ has a branch family $(\varphi_j)_{j\in J}$:

| node | $J$ | $\varphi_j$ |
|---|---|---|
| $\varphi_1\vee\varphi_2$ | $\{1,2\}$ | $\varphi_j$ |
| $\Diamond_I\varphi$ | $t+I$ | $\varphi@\tau$ |
| $\varphi_1\,\mathcal U_I\,\varphi_2$ | $t+I$ | $\varphi_2@\tau\wedge\bigwedge_{s\in[t,\tau)}\varphi_1@s$ |

Let $\psi^j_i:=D_\kappa(\varphi_j)_i$. A mode is a tuple $(J',k,\mathrm{Inf},\sigma,f,\rho)$:
- a nonempty **branch budget** $J'\subseteq J$;
- a **decider** $k$;
- **informed components** $\mathrm{Inf}\subseteq\mathcal C\setminus\{k\}$;
- **flags** $\sigma^j$ over $\mathrm{out}(k)$;
- **receiver guards** $f^j_i$ over $\mathrm{in}(i)$ (the default $f^j_i=\mathrm{true}$ means "$i$ covers branch $j$");
- **relay obligations** $\rho_c$ over $\mathrm{ports}(c)$.

$$
\psi_k=\bigvee_{j\in J'}\big(\psi^j_k\wedge\sigma^j\big),\qquad
\psi_i=\rho_i\wedge\bigwedge_{j\in J'}\big(f^j_i\to\psi^j_i\big)\ \ (i\in\mathrm{Inf}),\qquad
\psi_i=\rho_i\wedge\bigwedge_{j\in J'}\psi^j_i\ \ (\text{otherwise}),
$$
with the **delivery** side condition
$$\text{(Del)}\qquad \mathrm{Ctx}\wedge\sigma^j\wedge\textstyle\bigwedge_c\rho_c\ \models\ f^j_i\qquad(j\in J',\ i\in\mathrm{Inf}).$$
Delivery along a path $k=c_0\to\dots\to c_m=i$ is obtained by relay obligations $\rho_{c_l}=\bigwedge_j\big(F^j_{l}(e_l)\to\bigcirc^{d_{c_l}}F^j_{l+1}(e_{l+1})\big)$
on the edge variables $e_l$. Here $F^j$ are flag regions, with $F^j_1=\sigma^j$, and $f^j_i$ is the decoding of the
last edge, shifted by the path latency.

**Named special cases.**

| mode | parameters | meaning |
|---|---|---|
| `stat(j*)` | $J'=\{j^*\}$, $\mathrm{Inf}=\emptyset$, $\sigma\equiv\mathrm{true}$ | the designer picks the branch or witness time |
| `dec(k,J')` | $\mathrm{Inf}=\emptyset$, $\sigma\equiv\mathrm{true}$ | $k$ picks at run time; everyone else covers all of $J'$ |
| `ann(k,…)` | general | $k$ picks and announces on existing edges; informed components act only on the announced branch |

The budget $J'$ is the temporal analogue of the tolerance split. Enlarging $J'$ gives the decider more freedom and
everyone else more to cover. For ◇ it is a sub-window $I'\subseteq I$.

### 3.2 The table (folded forms, uniform annotation)
$\psi^{(1)},\psi^{(2)}$ denote the children's outputs. $k$ is the decider. "Others" are $i\ne k$ not informed. $\bigcirc^\lambda$ is $\Box_{[\lambda,\lambda]}$.

| shape of $\varphi$ | mode | $D(\varphi)_k$ (decider) | $D(\varphi)_i$, $i\neq k$ | side conditions |
|---|---|---|---|---|
| atom $\mu$ (owned) | — | $\mu_k(\theta_k)$ | $\mu_i(\theta_i)$; true if $i\notin\mathrm{Own}$ | (Sp), $\Lambda_\mu$ |
| env atom $\varepsilon$, implied by Ctx | — | true | true | $\mathrm{Ctx}\models\varepsilon$ |
| env atom $\varepsilon$, branch position | — | guard $g_c$ for its certifier $c$ | true | (Cert) |
| $\varphi_1\wedge\varphi_2$ | — | $\psi^{(1)}_k\wedge\psi^{(2)}_k$ | $\psi^{(1)}_i\wedge\psi^{(2)}_i$ | $\Lambda_1\cup\Lambda_2$ |
| $\Box_I\varphi$ | — | $\Box_I\psi_k$ | $\Box_I\psi_i$ | — |
| $\varphi_1\vee\varphi_2$ | `stat(j)` | $\psi^{(j)}_k$ | $\psi^{(j)}_i$ | — |
| $\varphi_1\vee\varphi_2$ | `dec(k)` | $\psi^{(1)}_k\vee\psi^{(2)}_k$ | $\psi^{(1)}_i\wedge\psi^{(2)}_i$ | — |
| $\varphi_1\vee\varphi_2$ | `ann(k)` | $(\psi^{(1)}_k\wedge\sigma^1)\vee(\psi^{(2)}_k\wedge\sigma^2)$ | $\mathrm{Inf}$: $\rho_i\wedge\bigwedge_j(f^j_i\to\psi^{(j)}_i)$; others: $\psi^{(1)}_i\wedge\psi^{(2)}_i$ | (Del) |
| $\alpha\to\beta$ ($\alpha$ observable) | `ann(obs)` | observer: $\alpha'\to\sigma$ (EARS form) | $\mathrm{Inf}$: $f_i\to\psi^\beta_i$; others: $\psi^\beta_i$ | (Del), $\alpha\models\alpha'$ |
| $\Diamond_I\varphi$ | `stat(τ)` | $\bigcirc^\tau\psi_k$ | $\bigcirc^\tau\psi_i$ | $\tau\in I$ |
| $\Diamond_I\varphi$ | `dec(k,I')` | $\Diamond_{I'}\psi_k$ | $\Box_{I'}\psi_i$ | $I'\subseteq I$ |
| $\Diamond_I\varphi$ | `ann(k)`, commit-ahead $\lambda$ | $\Diamond_{I-\lambda}(\sigma\wedge\bigcirc^{\lambda}\psi_k)$ | $\mathrm{Inf}$: $\Box_{I-\lambda+\ell_i}(f_i\to\bigcirc^{\lambda-\ell_i}\psi_i)$; others: $\Box_I\psi_i$ | (Del) with latency $\ell_i$; $\lambda\ge\max_i(\ell_i+d_i)$; $\min I\ge\lambda$ (otherwise the commitment precedes the evaluation time) |
| $\varphi_1\,\mathcal U_I\,\varphi_2$, $I=[a,b]$ | `dec(k)` | $\psi^{(1)}_k\,\mathcal U_I\,\psi^{(2)}_k$ | $\Box_{[0,b)}\psi^{(1)}_i\wedge\Box_I\psi^{(2)}_i$ | — |
| $\varphi_1\,\mathcal U_I\,\varphi_2$ | `ann(k)` | $(\psi^{(1)}_k\wedge\neg\sigma)\,\mathcal U_I\,(\psi^{(2)}_k\wedge\sigma)$ (first flag marks the witness) | $(\psi^{(1)}_i\,\mathcal W\,f_i)\wedge\Box_I(f_i\to\psi^{(2)}_i)$ | delay-0 delivery of $\sigma$ and of $\neg\sigma$ |
| $\varphi_1\,\mathcal R_I\,\varphi_2$ | `stat(□)` | $\Box_I\psi^{(2)}_k$ | $\Box_I\psi^{(2)}_i$ | — |
| $\varphi_1\,\mathcal R_I\,\varphi_2$ | `dec(k)` | $\psi^{(1)}_k\,\mathcal R_I\,\psi^{(2)}_k$ | $\Box_{[0,b)}\psi^{(1)}_i\wedge\Box_I\psi^{(2)}_i$ | — |
| nested, e.g. $\Diamond_I\Box_J\varphi$ | `dec(k)` | $\Diamond_I\Box_J\psi_k$ | $\Box_{I\oplus J}\psi_i$ | by composition |
| nested, e.g. $\Box_I\Diamond_J\varphi$ | `dec(k)` per instance | $\Box_I\Diamond_J\psi_k$ | $\Box_{I\oplus J}\psi_i$ | by composition |

**Notes on the table.**
- **Derivation.** Every ◇/U/R row is UD after unrolling, refolded. For example, the U cover is
  $\bigwedge_{\tau\in I}\big(\psi^{(2)}_i@\tau\wedge\bigwedge_{s<\tau}\psi^{(1)}_i@s\big)=\Box_I\psi^{(2)}_i\wedge\Box_{[0,b)}\psi^{(1)}_i$.
- **Commit-ahead $\lambda$.** An informed component that acts at the witness time must have received the flag $d_i$
  steps earlier. The decider must therefore *commit* $\lambda$ steps in advance (schema `S.ev-announce-d1`). The ◇
  announcement therefore works only if the information that determines a good witness is available $\lambda$ steps
  early. Otherwise use `dec` (cover).
- **D is a mechanical interpreter.** `scripts/polystl_decomp_check.py` §[D] implements this table in unrolled form
  (≈90 lines). It reproduces the hand-derived obligations of the EARS chain *exactly*: Z3 checks equivalence for both
  delay settings.

---

## 4. Disjunction and eventually

### 4.1 Naive distribution is unsound
**Proposition 2.** Define $D_{\text{naive}}(\Diamond_I\varphi)_i:=\Diamond_I D(\varphi)_i$ and $D_{\text{naive}}(\varphi_1\vee\varphi_2)_i:=\psi^{(1)}_i\vee\psi^{(2)}_i$.
Both are unsound whenever two components have nontrivial parts. They are sound when at most one component's part
depends on the branch, because that is `dec(k)` with branch-independent covers.

*Counterexample (Z3 `ii-a.naive`).* Relay, $H=1$, $G_P=\Diamond_{[0,1]}|d-r|\le0.5$, split $|m-r|\le0.2$, $|d-m|\le0.3$. Naive obligations:
- Radio: $\Diamond_{[0,1]}|m-r|\le0.2$;
- Display: $\Diamond_{[0,1]}|d-m|\le0.3$.

Trace $r=(-1,-1)$, $m=(0,-0.8)$, $d=(0,0)$:
- Radio is accurate at $t=1$ only.
- Display is accurate at $t=0$ only.
- $|d-r|=1$ at both times.

The components picked different witness times. The same failure happens for ∨: in $(u\ge.5\wedge v\ge.5)\vee(u\le-.5\wedge v\le-.5)$
the naive split allows $u=.5,v=-.5$ (`S.or-naive`). It also happens for U and R (`S.until-naive`, `S.release-naive`).

### 4.2 The sound options
All of these are instances of UD and verified as schemas: `S.ev-decide`, `S.ev-static`, `S.ev-announce`, `S.ev-announce-d1`,
`S.ev-announce-ahead`, `S.or-decide`, `S.or-announce`, `S.until-decide`, `S.until-announce`, `S.release-decide`, `S.ev-alw`.

- **(a0) Static witness.** The designer resolves the choice. This is the cheapest option, and it is enough whenever the
  choice need not depend on run-time data. On `ii-a` it is valid and realizable.
- **(a) Decider and cover.** One component $k$ owns the choice, and the others satisfy their part of *every* branch in
  $J'$: the □-shaped obligations.
  - On `ii-a`, both Radio-decides (Display $\Box_{[0,1]}|d-m|\le.3$) and Display-decides (Radio □) are valid and
    realizable.
  - This is exactly the structure the fixed-point sweep (foundations §9) produces: the first-updated component receives
    the choice. The sweep picks the decider by its update order. $D$ picks it by rule.
- **(b) Announcement (witness signal).** The others need to satisfy only the branch announced to them, through a flag
  carried by an *existing* edge variable (§4.4).
  - On `ii-a`, Radio commits $\Diamond(|m-r|\le a\wedge\mathrm{comb}(m))$ and Display needs only
    $\Box(\mathrm{comb}(m)\to|d-m|\le b)$, which is strictly weaker than its cover (Z3 `ii-a.announce gain`).
  - The sweep cannot produce this from a cover seed. A flag is a *commitment* that shrinks the decider's set, and the
    sweep only enlarges.
- **(c) No decider admissible.** If no decider is admissible and the covers are not realizable, $D$ fails at that node.
  Thm 6 shows that in the exclusive-fork case this failure is not a weakness of $D$: no delegation exists at all.

### 4.3 The decider rule
Fix a node $\nu$ with branch parts $\psi^j_i$, and let $R_i$ denote $i$'s obligations from the rest of the tree.
- $\mathrm{Act}(\nu,J')=\{i:\ R_i\wedge\bigwedge_{j\in J'}\psi^j_i\ \text{not realizable}\}$: the components that **cannot
  cover** and must decide or be told.
- $\mathrm{Dec}(\nu,J')=\{k:\ R_k\wedge\bigvee_{j\in J'}(\psi^j_k\wedge\sigma^j)\ \text{realizable for some code}\}$: $k$
  can, for every reachable input history, pick a branch whose environment conditions it can **certify** (Cert) and
  whose part it can perform.
- **Admissible deciders.** $W(\nu,J')=\{k\in\mathrm{Dec}:\ \forall a\in\mathrm{Act}\setminus\{k\}:\ \ell(k\rightsquigarrow a)\le\lambda_a,\ \text{and the path edges have capacity (Prop 5) or derived flags}\}$.
  Here $\lambda_a$ is the time between when $k$ can commit and when $a$ must act.

**Canonical choice.** Try, in order:
- **(P0)** `stat`: a singleton $J'=\{j^*\}$ with $\mathrm{Act}=\emptyset$, taking the earliest witness.
- **(P1)** `dec(a)`: $\mathrm{Act}(\nu,J)\subseteq\{a\}$ and $a\in\mathrm{Dec}$. *The unique actor decides*. This
  includes "the unique writer of the variables of a ◇ body", e.g. $\Diamond|d|\ge0.4$ goes to Display.
- **(P2)** `ann(k)`: $k\in W(\nu,J)$, preferring derived flags over band flags, then the **most downstream** candidate
  (the most information and the fewest relays), then the lowest index.
- **(P3)** Shrink $J'$ (sub-windows, largest first) and repeat. If nothing works, $D$ fails at $\nu$.

**Search.** Realizability couples nodes through $R_i$: in the EARS example the cover of one conjunct is killed by
another conjunct. So the procedure fixes this total order on annotations and returns the **first** annotation whose
output is realizable for every component. Each test is $n$ local $\forall\exists$ checks. The search is exponential
only in the number of disjunctive nodes.

**When a decider must exist.** This follows from Thm 6. If the branches are exclusive per actor and no static branch
works, then any delegation needs either an information path between the actors (a decider/follower pair) or shared
environment information (both deciding from a common observation). "A component downstream of all observers" is the
case where the certifying information is spread over several readers. The decider must then be a *join* of the
observers' paths that still reaches the actors, as in (P2). For example, a trigger $x+y\ge0$ with $x$ and $y$ read by
different components needs a join that receives both, relayed with tolerances via `split`.

### 4.4 Witness signals through existing ports: the flag-in-a-band trick
Let $e$ be an edge variable written by $k$ at time $t$. Let $R(h)\subseteq[-Y_e,Y_e]$ be the set of values that $k$'s
*other* obligations leave for $e(t)$, given $k$'s input history $h$.

**Proposition 5 (capacity dichotomy).**
- (a) Suppose some $\epsilon>0$ is such that every reachable $R(h)$ contains an interval of length $\epsilon$. Then for
  every $N$ there are $N$ pairwise disjoint finite unions of closed intervals $F^1,\dots,F^N$ over $e$ alone (PolySTL
  predicates) with $R(h)\cap F^c\neq\emptyset$ for all $h$ and $c$. So $e$ carries any finite number of flags without
  breaking $k$'s other duties.
- (b) If $R(h)$ is a single point for some reachable $h$, then at that $(t,h)$ no flag can be set freely. Only flags
  that are functions of what $e$ already carries can be used.

*Proof.* (a) Take period $p=\epsilon/2$ and tooth width $w=p/(2N)$, and let
$F^c=\bigcup_n[np+cp/N,\ np+cp/N+w]$, intersected with the type. Teeth of different classes are $p/N>w$ apart, so the
classes are disjoint. Every interval of length $\epsilon\ge p+w$ contains a full tooth of each class. Finitely many teeth
fit in the bounded type. (b) A value forced by $h$ is a function of $h$. ∎

**Verification.** On `ii-a` the band $|m-r|\le0.2$ has width $0.4$:
- a comb with period $0.3$ and teeth $0.1$ keeps Radio receptive (Z3);
- a comb with period $0.6$ (gaps $0.5>0.4$) does not.

**Three ways a flag gets across.**
- **(b0) Derived flag.** The information is already a function of the edge's duty, so no capacity is needed, but the
  guard over-approximates. For example, if $m$ tracks $r$ within $a$, then $|r|>0.5\Rightarrow|m|\ge0.5-a$.
- **(b1) Band flag.** Uses the comb; needs positive width.
- **(b2) Time-multiplexed flag.** Uses a sample of $e$ inside the commit window at which the band has positive width.

**When the architecture permits (b).** An announcement from $k$ to the set $\mathrm{Inf}$ can be built with all relays
realizable **iff** for every $i\in\mathrm{Inf}$:
- (i) there is a directed path $k\rightsquigarrow i$ with $\ell\le\lambda_i$;
- (ii) at the transmission times, every edge on the path has positive width (b1/b2) or carries the information already (b0).

Without (i), $i$'s inputs are independent of $k$'s choice, so (Del) forces $f^j_i=\mathrm{true}$ and $i$ covers.
Without (ii), Prop 5(b) applies.

**Interplay with the tolerance split** (check `i.4`). Take EARS with a tracking conjunct $\Box|d-r|\le0.5$. The flags
are *derived* from Radio's band:
- on: $|m|\ge0.5-a$;
- off: $|m|\le0.2+a$.

The decomposition is sound for every $a+b\le0.5$. It is realizable only if the flags are disjoint ($a<0.15$) and
$b\ge0.1+a$. Z3: $(0.1,0.3)$ is realizable; $(0.2,0.3)$ is sound but Display is not receptive. So the tolerance split
spends *information capacity* as well as accuracy.

### 4.5 The information fork: non-decomposability
**Lemma (agreement).** If $f:X\to J$ and $g:Y\to J$ satisfy $f(x)=g(y)$ for all $(x,y)\in X\times Y$, then $f$ and $g$
are the same constant. *Proof.* Fix $y_0$: $f\equiv g(y_0)$, and symmetrically for $g$. ∎

**Theorem 6 (exclusive fork).** Assume:
- two components $a,b$ with $\mathrm{info}(a)\cap\mathrm{info}(b)=\emptyset$;
- no directed path between $a$ and $b$;
- $A_P$, restricted to $\mathrm{info}(a)\cup\mathrm{info}(b)$, is a product $A_a\times A_b$;
- $G_P\equiv\bigvee_{j\in J}(\gamma_j\wedge\alpha_j\wedge\beta_j)$ with $\gamma_j$ over $\mathrm{Env}$, $\alpha_j$
  pairwise disjoint over $a$'s outputs, and $\beta_j$ pairwise disjoint over $b$'s outputs.

Then $P$ has a valid realizable delegation iff there is a $j^*$ with $\mathrm{Ctx}\models\gamma_{j^*}$, $\alpha_{j^*}$
realizable by $a$, and $\beta_{j^*}$ realizable by $b$. That is, iff a static branch works.

*Proof.* (⇐) Delegate $\alpha_{j^*}$ to $a$ and $\beta_{j^*}$ to $b$.

(⇒) Take causal strategies $f_a\subseteq S_a$ and $f_b\subseteq S_b$ (realizability). $a$'s outputs are a function of
$x_a\in\mathrm{info}(a)$, and $b$'s of $x_b$. For each environment in $A_P$, $G_P$ holds, so some branch $j$ holds. By
disjointness, $j$ is the *unique* index with $\alpha_j(f_a(x_a))$, and also the unique index with $\beta_j(f_b(x_b))$.
So $J_a(x_a)=J_b(x_b)$ on $A_a\times A_b$, and by the lemma this index is a constant $j^*$. Then $\gamma_{j^*}$ holds on
all of $A_P$, and $f_a,f_b$ realize $\alpha_{j^*},\beta_{j^*}$. ∎

The proof uses no horizon bound: it holds for unbounded time as well.

**Minimal example** (check `iii`). $H=0$; $C_1$ reads $x$ and writes $u$; $C_2$ reads $y$ and writes $v$; all types $|\cdot|\le1$; no edges. Define
$$G_P=(\Phi_+\vee\Phi_-)\wedge(E_+\to\Phi_+)\wedge(E_-\to\Phi_-),$$
$$\Phi_\pm=\{\pm u\ge.5,\ \pm v\ge.5\},\qquad E_\pm=\{\pm x\ge.5,\ \pm y\ge.5\}.$$
In words: agree on a side, and follow the environment when it is unanimous.

Since $\Phi_\pm$ are exclusive, $G_P\equiv(\Phi_+\wedge\neg E_-)\vee(\Phi_-\wedge\neg E_+)$, which is Thm 6's form. Neither
$\neg E_-$ nor $\neg E_+$ is implied by $A_P$, so **no local delegation exists**, for any obligation language and any $H$.

Z3 confirms the instance in three ways:
- **Finite-sample UNSAT** (necessary for any delegation): there are no values $f(\pm1)$, $g(\pm1)$ satisfying $G_P$ on
  all four $(x,y)\in\{\pm1\}^2$.
- **Centralized realizability holds:** $\forall x,y\,\exists u,v\,G_P$ is valid. So the obstruction is information, not
  feasibility.
- **$D$ fails on every annotation:** all 256 annotations of $D$ (stat/dec at the three nodes × certifier choices) yield
  sound but unrealizable outputs.

The fork's game is a Henkin quantifier ($u$ blind to $y$, $v$ blind to $x$), which is not first-order. That is why
the non-existence proof goes through the agreement lemma and a finite sample rather than a QE query. The first-order
check $\exists u\,\forall x,y\,\exists v\,G_P$ (blind $C_1$) is false, as expected.

**Adding the edge $C_1\to C_2$** ($C_2$ also reads $u$) makes the query decomposable. $D$ with decider $C_1$ (P2) at
all three nodes and the *derived* flag "sign region of $u$" gives:
$$C_1:\ (x>-.5\wedge u\ge.5)\vee(x<.5\wedge u\le-.5),\qquad C_2:\ (u\ge.5\to v\ge.5)\wedge(u\le-.5\to v\le-.5).$$
Z3: (C1) holds, both obligations are receptive, and $\forall x\,\exists u\,\forall y\,\exists v\,G_P$ is valid.
$C_2$ ignores $y$ completely. This is the Pnueli–Rosner/Finkbeiner–Schewe picture in miniature: the
*information fork* (incomparable information, no join) is what makes the query undecomposable, and one edge removes it.

---

## 5. Implication-shaped queries: EARS "when trigger, response within $k$"

**Lemma 3 (guarded response, GRL).**
$$\Box_{[0,T]}(\alpha\to\Diamond_{[a_1,b_1]}\beta)\wedge\Box_{[0,T+b_1]}(\beta\to\Diamond_{[a_2,b_2]}\gamma)\ \models\ \Box_{[0,T]}(\alpha\to\Diamond_{[a_1+a_2,\,b_1+b_2]}\gamma).$$
*Proof.* Suppose $\alpha$ holds at $t$. Then $\beta$ holds at some $s\in[t+a_1,t+b_1]$, and $\gamma$ at some
$s'\in[s+a_2,s+b_2]\subseteq[t+a_1+a_2,t+b_1+b_2]$. ∎

Schema `S.GRL` checks this, and `S.GRL-budget` checks that the window cannot shrink below the sum. GRL is the
temporal relay insight: a response window splits additively along a chain, just as $d-r=(d-m)+(m-r)$ splits a tolerance.

**Setting.** Chain $C_1\to C_2\to\dots\to C_n$:
- $C_1$ reads the environment vector $e$, with trigger $\alpha(e)$;
- $C_l$ writes $m_l$, which is read by $C_{l+1}$;
- $C_n$ writes $y$, with response $\beta(y)$;
- delays $d_l$, and $\Delta:=\sum_l d_l$;
- the query is $G_P=\Box_{[0,T]}(\alpha\to\Diamond_{[0,k]}\beta)$.

Optionally the query also has the **no-spurious-response** conjunct
$$Q=\Box_{[0,T]}\big(\Box_{[0,k]}\kappa\to\bigcirc^k\beta'\big),$$
with a quiet condition $\kappa$ (env, disjoint from $\alpha$) and a quiet output $\beta'$ (disjoint from $\beta$).

**What D does.**
- The outer node $\neg\alpha\vee\Diamond\beta$: the certifier of $\neg\alpha$ is $C_1$, which reads $e$.
  - Without $Q$, (P1) applies: $\mathrm{Act}=\emptyset$, because $C_n$ can cover by $\Box\beta$. $D$ returns the
    **cover delegation**: $C_n:\Box\beta$, everyone else trivial (Z3 `i.cover`).
  - With $Q$, the cover is unrealizable jointly with $Q$'s part (`i.cover+Q` fails), so (P2) applies. The decider is
    the observer $C_1$, with $\mathrm{Inf}=\{C_2,\dots,C_n\}$, flag regions $F_l$ on $m_l$, and relays along the chain.
- The inner $\Diamond_{[0,k]}\beta$ has the unique actor $C_n$: (P0) gives the static witness $\Delta$, and (P1) a window.
- $Q$'s node is handled the same way, after **guard weakening** $\Box_{[0,k]}\kappa\leadsto\kappa@(t+k-\Delta)$, with
  "off" flags $F'_l$ disjoint from $F_l$.

**Theorem 4 (EARS chain).** Let $F_l,F'_l$ be disjoint nonempty polytopes in the type of $m_l$, and let $s_l\ge0$. The output of $D$ is:

| component | on-chain (from $G_P$) | off-chain (from $Q$) |
|---|---|---|
| $C_1$ | $\Box_{[0,T]}\big(\alpha\to\Diamond_{[d_1,d_1+s_1]}F_1(m_1)\big)$ | $\Box\big(\kappa\to\bigcirc^{d_1}F'_1(m_1)\big)$ |
| $C_l$, $1<l<n$ | $\Box_{[0,T_l]}\big(F_{l-1}(m_{l-1})\to\Diamond_{[d_l,d_l+s_l]}F_l(m_l)\big)$ | $\Box\big(F'_{l-1}\to\bigcirc^{d_l}F'_l\big)$ |
| $C_n$ | $\Box_{[0,T_n]}\big(F_{n-1}(m_{n-1})\to\Diamond_{[d_n,d_n+s_n]}\beta(y)\big)$ | $\Box\big(F'_{n-1}\to\bigcirc^{d_n}\beta'\big)$ |

Here $T_l=T+\sum_{l'<l}(d_{l'}+s_{l'})$.

- **(a) Soundness.** If $\Delta+\sum_ls_l\le k$, the on-chain gives $G_P$. If $\Delta\le k$, the off-chain gives $Q$.
- **(b) Realizability.** Every obligation is receptive and causal. Each component's guards are disjoint ($\alpha\cap\kappa=\emptyset$,
  $F_l\cap F'_l=\emptyset$), and each consequent is a nonempty region of its own output, $d_l$ or more steps after the input.
- **(c) Necessity.** Suppose $T\ge k$ and $A_P$ contains the constant quiet environment and its single-sample trigger
  perturbations. If $\Delta>k$, then $G_P\wedge Q$ has **no** valid realizable delegation at all.
- **(d)** Without $Q$, $G_P$ is always delegable, by the cover.

So with $Q$, the query is delegable iff $\Delta\le k$, and $D$ finds the delegation. The slack $k-\Delta$ is a free
budget $\sum_ls_l$, as $a+b\le0.5$ was. The canonical choice is $s\equiv0$; an objective or the sweep may distribute it.

*Proof.* (a) Apply GRL $n-1$ times. For $Q$: if $\kappa$ holds on $[t,t+k]$, then it holds at $t+k-\Delta\ge t$, and the
off-chain delivers $\beta'$ at $t+k$. (b) Explicit strategies: encode the trigger as a flag value, re-encode at each relay,
decode at $C_n$. (c) Take trace $B$, quiet everywhere, and trace $A$, equal to $B$ except for a trigger at some
$t\in[k,T]$. For $\tau\in[t,t+k]$, $y(\tau)$ depends only on $e(\le\tau-\Delta)\subseteq e(<t)$, where $A$ and $B$ agree.
In $B$, $Q$ forces $\beta'(y(\tau))$ for all $\tau\in[k,T+k]\supseteq[t,t+k]$. In $A$, $G_P$ forces $\beta(y(\tau))$ for
some such $\tau$. But $\beta\cap\beta'=\emptyset$. ∎

### 5.1 Worked example: Radio → Display (check `i`, `D.i`)
- **Query.** $\Box_{[0,2]}(|r|>0.5\to\Diamond_{[0,2]}|d|\ge0.4)$; types $|r|,|m|,|d|\le1$; $H=5$.
- **Optional conjunct.** $Q=\Box_{[0,2]}(\Box_{[0,2]}|r|\le0.2\to\bigcirc^2|d|\le0.1)$.
- **Flags.** On: $|m|\ge0.5$. Off: $|m|\le0.1$.

**Delays (0,0), $\Delta=0$, budget 2.**
$$\text{Radio: }\Box_{[0,2]}(|r|>0.5\to|m|\ge0.5)\wedge\Box(|r|\le0.2\to|m|\le0.1),$$
$$\text{Display: }\Box(|m|\ge0.5\to|d|\ge0.4)\wedge\Box(|m|\le0.1\to|d|\le0.1).$$
Window-split family: Radio $\Box(\mathrm{trig}\to\Diamond_{[0,s_R]}|m|\ge.5)$ and Display $\Box_{[0,2+s_R]}(|m|\ge.5\to\Diamond_{[0,s_D]}|d|\ge.4)$.
Z3 over all ten pairs: (C1) holds **exactly** when $s_R+s_D\le2$.

**Delays (1,1), $\Delta=2$, budget 0.**
$$\text{Radio: }\Box_{[0,2]}(|r(t)|>0.5\to|m(t{+}1)|\ge0.5)\wedge\Box(|r(t)|\le0.2\to|m(t{+}1)|\le0.1),$$
$$\text{Display: }\Box_{[1,3]}(|m(t)|\ge0.5\to|d(t{+}1)|\ge0.4)\wedge\Box(|m(t)|\le0.1\to|d(t{+}1)|\le0.1).$$
Z3: (C1) holds for $s=(0,0)$ and fails for $s=(1,0),(0,1)$. Both obligations are receptive and causal (the
$\forall\exists$ sentence with delay-respecting prefix, qe2 and the default engine agree; explicit strategies also check).
The mechanical interpreter's output equals these formulas.

**Lower bound.** With delays (1,1) and $k=1<\Delta$, the two-trace argument of Thm 4(c) is UNSAT (`i.lower`). The same
traces with delays (0,0) are not contradictory (`i.lower-d0`).

**Three components** (`i.3`). Radio (delay 1) → Filter (delay 0) → Display (delay 1), $k=3$, budget 1:
- valid with the slack unused, and valid with it given to Filter ($\Diamond_{[0,1]}$);
- all three obligations are realizable;
- giving Filter $\Diamond_{[0,2]}$ fails.

**Assumptions.** $A_{\mathrm{Radio}}=$ types. $A_{\mathrm{Display}}=$ types: every $m$ is reachable with $r\in(0.2,0.5]$.

### 5.2 Variants (rules, not separately checked)
- **AND-trigger** $\alpha_1\wedge\alpha_2$, observed by different components. A responder reachable from only one
  observer may weaken the guard to that conjunct (guard weakening). This is sound, but it over-responds, and $Q$
  penalizes over-response. The exact guard needs a join on both paths, whose cross-time guard aligns the two latencies.
- **OR-trigger** $\alpha_1\vee\alpha_2$. Every disjunct needs its own path to the responder. Otherwise the responder
  must cover: respond always.
- **Several responders** with $\Diamond_{[0,k]}(\beta_1\wedge\beta_2)$. The witness must be common. A common trigger
  acts as a clock: a static offset $\tau^*\ge\max_i\ell(C_1\rightsquigarrow C_{n_i})$, if $\tau^*\le k$, synchronizes
  them without any announcement.
- **Mixed response body**, e.g. $\Diamond|d-r|\le\epsilon$. `split` spreads the body over the chain at the witness time.
  Synchronizing the split parts then needs commit-ahead (§3.2).

---

## 6. Assumptions

**Forward flow, first components.** $A_P$ is over $\mathrm{Env}$, so a component $C_1$ that reads the environment
receives $A_1=\pi_{\mathrm{in}(1)}(A_P\wedge\bigwedge_{i\neq1}S_i)$. The following lemma reduces this to $A_P$ restricted to $\mathrm{in}(1)$.

**Lemma 7 (only ancestors matter).** If every $S_i$ is realizable, then
$$\pi_{\mathrm{in}(j)}\big(A_P\wedge\textstyle\bigwedge_{i\neq j}S_i\big)=\pi_{\mathrm{in}(j)}\big(A_P\wedge\textstyle\bigwedge_{i\in\mathrm{anc}(j)}S_i\big),$$
where $\mathrm{anc}(j)$ is the set of components $i\neq j$ with a directed path to $j$.

*Proof.* ⊆ holds because the left side has more conjuncts. For ⊇, take $z$ in the right side. Re-generate the outputs of
the non-ancestors and of $j$ by their strategies, in the time-expanded order. No ancestor and no input of $j$ reads them,
and $A_P$ is over $\mathrm{Env}$. So the new trace lies in the left set and has the same $\mathrm{in}(j)$-projection. ∎

This is the bystander argument (foundations §10) applied to assumptions. Z3 `iv.ancestors` and `iv.A_R` confirm it.

**Downstream assumptions are shadows of upstream obligations**, as in the shadow assumption (foundations §5, "assumptions solved last"). $D$ never puts
assumptions into the $\psi_i$; it produces saturated obligations. Syntactic **forward rules** give valid (C2)
assumptions without QE. They are all instances of GRL:

| $A_P\wedge\bigwedge_{\mathrm{anc}}S$ contains | and $S_c$ contains | then the readers of $q'$ may assume |
|---|---|---|
| $\Box_I q$ | $\Box(q\to\bigcirc^{d}q')$ | $\Box_{I+d}\,q'$ |
| $\Box_I\Diamond_{[0,w]}q$ (liveness) | $\Box(q\to\Diamond_{[a,b]}q')$ | $\Box_I\Diamond_{[a,\,w+b]}q'$ |
| $\Box(p\to\Diamond_{[0,w]}q)$ | $\Box(q\to\Diamond_{[a,b]}q')$ | $\Box(p\to\Diamond_{[a,\,w+b]}q')$ |

**Proposition 8.** A forward image $\mathrm{Fwd}_j$ built by these rules satisfies (C2), and $\mathrm{Fwd}_j\supseteq A_j$ (the shadow).
*Proof.* Each rule is an entailment from $A_P\wedge\bigwedge S$, and the shadow is the strongest set over $\mathrm{in}(j)$ that is so entailed. ∎

**How a temporal $A_P$ is *used*: liveness transfer.** A guarantee conjunct $\Box_I\Diamond_{[0,w']}p$ with
$A_P\models\Box_I\Diamond_{[0,w]}q$ and $w'\ge w+k$ may be replaced by $\Box(q\to\Diamond_{[0,k]}p)$, because
$\mathrm{Ctx}\wedge\text{new}\models\text{old}$ (schema `S.LT`). The liveness requirement becomes an EARS chain whose
trigger is the environment's own liveness. This is the temporal counterpart of using $A_P$'s rows in the Farkas
combination. The general principle: $D$ may replace a positive subformula $\varphi$ by $\varphi'$ whenever
$\mathrm{Ctx}\wedge\varphi'\models\varphi$.

**Check `iv`.** Relay with delays 0, $H=3$.
- **Query.** $A_P=\Box_{[0,1]}\Diamond_{[0,1]}|r|\le0.2$ ("the environment rests") and
  $G_P=\Box_{[0,1]}\Diamond_{[0,2]}|d|\le0.1\ \wedge\ \Box(|r|\ge.5\to|d|\ge.4)$.
- **$D$.** Liveness transfer, then the EARS chain with flags $|m|\le0.1$ and $|m|\ge0.5$.
- **Results.**
  - (C1) holds.
  - "Display always rests" fails.
  - $A_P\wedge S_R\models\mathrm{Fwd}_D=\Box_{[0,1]}\Diamond_{[0,1]}|m|\le0.1$, so (C2) holds.
  - The qe2 shadow $\pi_m(A_P\wedge S_R)$ **equals** $\mathrm{Fwd}_D$: the environment's liveness becomes the
    interface's liveness, exactly.
  - $\pi_m$ is unchanged by adding $S_D$.
  - (C1) still holds with Display's contract $(\mathrm{Fwd}_D,S_D)$ saturated.

---

## 7. Soundness, realizability, completeness

**Theorem 1 (soundness of $D$).** Let $\kappa$ be an annotation whose side conditions hold ((Sp), (Cert), (Del), interval
conditions), and let $\theta\in\Lambda_\kappa$. Put $S_i:=D_\kappa(G_P)_i$ and $A_i:=\pi_{\mathrm{in}(i)}(A_P\wedge\bigwedge_{j\neq i}S_j)$. Then:
1. each $S_i$ is a PolySTL formula over $\mathrm{ports}(i)$;
2. $S_i=\mathrm{true}$ for every $i$ outside $\mathrm{supp}(\kappa)$, the owners, certifiers, deciders, informed components and relays;
3. (C1) $A_P\cap\bigcap_iS_i\subseteq G_P$, and (C2) holds, so $\parallel_i(A_i,S_i)\preceq P$.

*Proof.* Locality and support hold by construction: each table entry combines local pieces of the same component, and
flags and guards live on that component's own ports.

For (C1), prove the **term invariant**: for every subformula $\varphi$ and every $t$,
$$\mathrm{Ctx}\wedge\textstyle\bigwedge_iD_\kappa(\varphi,t)_i\models\varphi@t,$$
reading formulas as cylinders. The proof is by structural induction.
- **Atom:** (Sp).
- **Environment atom:** implied by Ctx, or (Cert).
- **∧:** both induction hypotheses on the same trace.
- **$\Box_I$:** the induction hypothesis at each $t'\in t+I$.
- **Disjunctive node (UD):** let $z$ satisfy the left side.
  1. From $\psi_k$, some $j\in J'$ has $z\models\psi^j_k\wedge\sigma^j$.
  2. The $\rho_c$ are conjuncts of the $\psi_c$, so (Del) gives $z\models f^j_i$ for every $i\in\mathrm{Inf}$.
  3. Hence $z\models\psi^j_i$ for all $i$: by modus ponens for $\mathrm{Inf}$, and as a conjunct for the others.
  4. The induction hypothesis for $\varphi_j$ gives $z\models\varphi_j$.
  5. So $z\models\bigvee_J\varphi_j$, because $J'\subseteq J$.

  ◇, U and R are UD after unrolling (R as a conjunction over $\tau$ of UD nodes), and the folded forms denote the same
  sets.

At $\varphi=G_P$, $t=0$, the invariant is (C1). (C2) is ghost-freeness of the projected handouts (foundations §6), for shadow assumptions. ∎

**Theorem 1′ (realizability is local; D seeds the sweep).** Whether each $S_i$ is realizable is decided per component,
by one $\forall\exists$ sentence with a delay-respecting prefix, over $\mathrm{ports}(i)$ only. If every $S_i$ is
realizable, then $(S_i)\in\mathcal V$, and one sweep (fixed-point sweep, foundations §9) yields a **maximal** valid realizable delegation
that contains it.

Check `ii-a.sweep`: starting from $D$'s Radio-decider seed, the sweep reaches a fixed point that grew. Display still owes
$|d-m|\le0.3$ at *both* times on central inputs, so maximization keeps the decider structure.

**Completeness: what holds.**
- **(K1)** $D$ is complete for the EARS-chain class with $Q$: decomposable iff $\Delta\le k$ (Thm 4).
- **(K2)** $D$ is complete for exclusive two-actor disjunctions with independent information: decomposable iff
  `stat` works (Thm 6).
- **(K2′)** With a path $a\rightsquigarrow b$ within the latency budget, capacity on its edges (Prop 5), and a guard cover
  certifiable by $a$, `ann(a)` succeeds.
- **(K3)** $D$ + sweep reaches a maximal delegation whenever $D$'s output is realizable.
- All of these are complete **relative to** the chosen tolerances: the tolerance coupling is the conjunctive slice's LP.

**Completeness: what does not hold.**
- **Syntax dependence.** Write $G=(\alpha_1\vee\alpha_2)\wedge(\beta_1\vee\beta_2)$ in DNF as $\bigvee_{a,b}(\alpha_a\wedge\beta_b)$,
  with $\alpha$ owned by one component and $\beta$ by another, independently. Every single-decider annotation of the DNF
  fails: the other component would have to cover $\beta_1\wedge\beta_2$. The CNF form succeeds with two deciders.
  Completeness "modulo equivalence-preserving rewriting" is *trivially* true, because
  $G_P\equiv_{\mathrm{Ctx}}\bigwedge_iS_i\vee(G_P\wedge\neg\bigwedge_iS_i)$ for any valid $S$ and `stat(1)` returns the
  $S_i$. So the meaningful question is completeness for the given syntax, and that fails.
- **Choices with no single owner.** Patterns such as veto, or consensus around a cycle, where the branch is a joint
  function of several components' information with feedback, are not produced by UD. On cycles this would need a
  circular version of UD in the style of (Circ). Not done.
- **Continuous information.** Information that must cross an edge as a real value is the business of `split`. UD only
  moves finitely many discrete choices.

**Conjecture C1.** Assume an acyclic architecture and $G_P$ in *guarded form*: every disjunctive node has either a
single actor, or branch conditions certifiable by one component that reaches all actors within its latency budget. Then
$D$ with codes (b0–b2) is complete for $G_P$ as written. Open: an inductive argument would need a canonical extraction
of flags from an arbitrary realizable delegation, and Prop 5 supplies only the encoding direction.

---

## 8. Experimental verdicts (`scripts/polystl_decomp_check.py`)

| id | claim | verdict |
|---|---|---|
| S.* | 21 rule schemas over bounded time: □; ◇ naive, decide, static, announce at delay 0 and 1, announce with commit-ahead; ∨ naive, decide, announce; U naive, decide, announce; R naive, decide; GRL and its budget; LT; ◇□. Sound rows valid, naive rows refuted | as expected |
| i.C1 (13) | EARS window split: (C1) holds iff $s_R+s_D\le k-\Delta$ (10 pairs for delays 0,0; 3 for 1,1) | exactly the predicted 7 of 13 valid |
| i.C1Q, i.strat, i.real | with $Q$: sound, explicit strategies in $S_i$, $\forall\exists$ realizability (qe2 = default) | true |
| i.cover / i.cover+Q | "Display always responds": valid for $G_P$, invalid for $G_P\wedge Q$ | true / false |
| i.lower | delays (1,1), $k=1$: two-trace sample UNSAT, so no delegation; delays (0,0): SAT | as predicted |
| i3.* | three-component chain, budget 1: valid with the slack unused or given to Filter, realizable; budget exceeded fails | as predicted |
| i4.* | derived flags from a tracking band: sound for both splits; realizable for $a=0.1$, not for $a=0.2$ | as predicted |
| ii-a.* | relay ◇: naive invalid (cex above); Radio-dec, Display-dec, static valid and realizable; comb announcement valid, realizable, strictly weaker for Display; sparse comb not receptive; sweep from D seed valid, grew, fixed point | all as predicted |
| ii-b.* | data-dependent witness: naive invalid; Radio-dec valid and realizable on $A_P$; Display-dec (derived guard) sound but not receptive at reachable $m=(0.6,0.6)$; static not receptive | as predicted |
| iii.* | fork: sample UNSAT; centralized valid; static unsound; cover unsatisfiable; with edge: valid, receptive, $\forall\exists\forall\exists$ valid; blind $C_1$ false | as predicted |
| iv.* | liveness transfer: (C1); cover fails; (C2) for Fwd; shadow = Fwd; ancestors lemma; contract form; $A_R=A_P$ | as predicted |
| D.* | the table run mechanically: EARS outputs equal the hand formulas; ii-b both deciders; all 256 fork annotations sound and none realizable; the edge annotation succeeds | as predicted |

Every quantified sentence was decided by `qe2`+smt and by Z3's default engine, and the two always agreed. Every
elimination was cross-checked for equivalence. No disagreement or `unknown` occurred.

---

## 9. Unbounded intervals (limits, no solution attempted)

With $\Box_{[0,\infty)}$, $\Diamond_{[0,\infty)}$ or unbounded U, nothing unrolls. Trace sets are no longer finite unions
of polytopes, $\Pi_i$ and the shadow are not computable by QE, and the sweep does not run.

What survives:
- the set-theoretic soundness proof of Thm 1, which never used finiteness;
- GRL with unbounded windows ($\Box(\alpha\to\Diamond\beta)\wedge\Box(\beta\to\Diamond\gamma)\models\Box(\alpha\to\Diamond\gamma)$),
  where the window budget turns into fairness;
- Thm 6, whose proof has no horizon;
- the latency lower bound.

What is required: the folded outputs of a *uniform* annotation are already invariant-shaped (time-invariant local
relations under □). That is the only form that can be checked once rather than unrolled. Cycles need (Circ), with
the flag relays as part of the cyclic invariant.

What is lost:
- realizability becomes infinite-alternation distributed synthesis: GR(1)-like per component, and undecidable in general
  for architectures with information forks (Pnueli–Rosner);
- maximal obligations with absolute-time features disappear.

---

## 10. Summary of results

1. **A constructive operator.** The fixed-point sweep (foundations §9) maximizes a delegation but needs a seed.
   $D$ *constructs* the seed by structural recursion on the query for full PolySTL. Its only
   free choices are the annotation (split tolerances, deciders, budgets, codes), and a canonical preference order with
   local realizability tests resolves them.
2. **The unified disjunction rule and its hierarchy** (static ⊂ decide ⊂ announce), with the branch budget $J'$ as the
   temporal analogue of the tolerance split.
3. **An explanation of decider assignment by the sweep.** "The first-updated component gets the choice of ◇" is decider
   assignment by sweep order. $D$ replaces the order with the decider rule. It also adds announcements, which the sweep cannot create
   because a flag is a commitment that shrinks the decider's set.
4. **Flags without new ports:** the capacity dichotomy (Prop 5, comb construction), derived flags, and the observation
   that the tolerance split also spends information capacity (check `i.4`).
5. **A non-existence theorem for any delegation** (Thm 6, agreement lemma). A structural condition (information fork plus
   exclusive branches) is shown to imply non-existence.
6. **EARS chain characterization** (Thm 4): additive window budget, delegable iff $\Delta\le k$ under the
   no-spurious-response conjunct, and the explicit per-component guarded responses.
7. **Temporal assumption flow:** the ancestors-only lemma, forward rules, and liveness transfer. On the test instance the
   forward image equals the qe2 shadow, so this is consistent with "assumptions solved last".
8. **Guards on inputs made legitimate.** A receptive obligation cannot constrain a component's own inputs. Here a guard on
   an input is shown to be sound and realizable *inside a decider's disjunction* (certification), with the local
   realizability check as the precise boundary.

## 11. Open

- Conjecture C1 (completeness for guarded form).
- A circular UD for decisions around feedback loops.
- The objective that distributes the window budget $k-\Delta$ jointly with the tolerance LP of the conjunctive slice.
  Check `i.4` shows the two interact through flag separability.
- An automatic search for codes (b1/b2). The script uses hand-chosen combs; Prop 5 gives the construction, but
  computing $R(h)$ needs a QE per edge.
