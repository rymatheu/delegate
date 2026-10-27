# Conjunctive decomposition: a constructive operator for band queries

Status: definitions, theorems with proofs, one algorithm, experiments. Companion script `scripts/conjunctive_decomp.py`, full log `scripts/conjunctive_decomp.out`. All Z3 projections use `qe2` and are cross-checked for equivalence with the quantified input by two decision paths; every validity verdict is decided by both `qe2+smt` and the default engine, and the script asserts that they agree.

References of the form "foundations §n" are to `theory/foundations.md`. Facts used from there without re-derivation: validity is (C1)+(C2) (the validity theorem, foundations §4); assumptions can be solved last by projection (the shadow assumption, foundations §5); the projections $\Pi,\pi$ and ghost-freeness (foundations §6); the down-set observation (foundations §8) and the fixed-point sweep (foundations §9). That one row per query row per delegate suffices, and that each query row is a sum of delegate rows, is the affine Farkas argument of Theorem 1 below.

---

## 0. Summary

* **Main theorem (§6, Theorem 4).** For a conjunction of band queries $|N_kz-\kappa_k|\le g_k$ over $[0,H]$, with $A_P$ on environment columns, box types, and delays that break every cycle, the following is constructive. Fix the *head-band template*: per component and band, one band row, supported on the causal columns of the component's ports, whose head is the component's latest output column in the band's time-expanded cone of influence. Then:
  * the template delegations satisfying (C1) and receptiveness over the type box form, band by band, an explicit polyhedron (the leaky-flow LP of Theorem 1). This needs no output column to be the head of two bands with free coefficient ratio; that case is exactly where bilinearity is unavoidable.
  * the choice rule $R^\*$ selects one point of it as a function of (graph, query) alone.
  * the handout $G_i$, together with time-sliced assumptions $A_i^h$ obtained by existential projection, satisfies (C1), (C2), receptiveness and causality, with contracts over $\mathrm{ports}(i)$ only.
  * full-horizon assumptions are sound for acyclic supports (proved) and can fail for cyclic ones (Z3 counterexamples).
* **Recommended rule $R^\*$ (§5)** is a four-step lexicographic program:
  1. the support is chosen by leximin of the extended freedom vector, where an uninvolved component counts $+\infty$;
  2. budget shares are split by water-filling (max-min fair, i.e. constrained equal awards);
  3. pass-through gains are set by water-filling of the receptiveness margins;
  4. a uniqueness certificate checks that the optimal face is a point.

  Every step is an LP, the rule is covariant under rescaling and sign flips of internal signals, and shares and margins are unique.
* **Experiments (§7).** Every example passes every check, except where the theory predicts a failure:
  * (a) relay: $|m-r|\le\frac14$, $|d-m|\le\frac14$.
  * (b) chain: shares $\frac16$ each.
  * (c) fan-in: shares $\frac13$ each; the Logger gets $(\mathrm{true},\mathrm{true})$.
  * (d) loop: the canonical decomposition opens the loop, so Perception gets $(\mathrm{true},\mathrm{true})$.
  * With the Plant's physical normal fixed, Perception becomes necessary and $R^\*$ derives the hand-chosen $0.1/0.1/0.1$ split of the tracking-loop running example (foundations §11). Full-horizon assumptions then fail (C1) (a Z3 counterexample is reported), while the time-sliced assumptions pass.
* **Where the construction fails:**
  * shared heads across bands, i.e. fan-out of one signal to two query bands. Per-band LPs are fine but the joint obligation is not receptive (Z3); tying the head coefficients restores linearity, but choosing the tie value is the bilinear step.
  * physically fixed normals are not box-receptive. Receptiveness is then only relative and is checked after the fact.
  * the support search is exponential in the number of optional components.

---

## 1. Setting

**Columns.** A column is $c=(v,t)$, $t\in[0,H]$. The trace vector is $z\in\mathbb R^{\mathcal C}$. Each column has at most one writer $\mathrm{wr}(c)$; a column with no writer is an *environment* column. This includes initial values of delayed outputs, e.g. $x(0)$ in the loop. $\mathrm{col}(i)$ is the set of columns of $\mathrm{ports}(i)$; $\mathrm{in}(i),\mathrm{out}(i)$ split it. Types are boxes $|z_c|\le Y_c$.

**Query.**
* $P_0:=A_P\wedge\text{types}$. $A_P$ constrains environment columns only (foundations §1), so $P_0=P_0^{\mathrm{env}}\times\prod_{c\ \text{system}}[-Y_c,Y_c]$.
* Implementation: $A_P$ is a box $[\ell_c,u_c]$ on environment columns. The theory needs only the product structure.
* The support function is $h_0(\rho):=\max_{z\in P_0}\rho^\top z$. For a box, $h_0(\rho)=\sum_c\max(\rho_cu_c,\rho_c\ell_c)$.
* $G_P=\bigwedge_k\{\kappa_k-g_k\le N_kz\le\kappa_k+g_k\}$, a conjunction of *bands*. One-sided rows are bands with an infinite side and are omitted for brevity. A $\square$-query over $[0,H]$ unrolls into one band per time.

**Column graph** $\mathcal G$. Its edges are:
* $c\to h$ whenever $h\in\mathrm{out}(i)$, $c\in\mathrm{in}(i)$ and $t(c)\le t(h)-d_i$ (delay edges);
* $c\to h$ whenever $c,h\in\mathrm{out}(i)$ and $t(c)<t(h)$ (memory edges: a component may remember its own past outputs).

$\mathcal G$ is acyclic because every architectural cycle has a delay. $C_k:=$ the backward closure of $\mathrm{supp}(N_k)$ in $\mathcal G$. $\mathrm{COI}_k:=\{i:\mathrm{out}(i)\cap C_k\neq\emptyset\}$. The **head** $h(i,k)$ is the latest output column of $i$ in $C_k$; the implementation refuses ties, so there is one output per head time.

**Head-band template.** Component $i\in\mathrm{COI}_k$ receives for band $k$ one row
$$\kappa_{ik}-w_{ik}\ \le\ c_{ik}\,z_{h(i,k)}+\beta_{ik}^\top z\ \le\ \kappa_{ik}+w_{ik},\qquad \mathrm{supp}(\beta_{ik})\subseteq \mathrm{Caus}(i,k),$$
where $\mathrm{Caus}(i,k):=\{c\in\mathrm{in}(i):t(c)\le t(h)-d_i\}\cup\{c\in\mathrm{out}(i):t(c)<t(h)\}$, $w_{ik}\ge0$. All coefficients and offsets are in **budget units** of band $k$: the row is used with Farkas multiplier $1$ in the certificate of band $k$ (the multiplier is absorbed into the row). The delegated guarantee is $G_i:=\bigwedge_k(\text{row}_{ik})$. The template is a restriction: it excludes asymmetric row pairs and rows with two heads.

---

## 2. Graph structure of Farkas

**Theorem 1 (leaky-flow form of (C1)).**

(a) *Certificate form.* Let $S_i\subseteq\mathrm{Tr}(\mathrm{ports}(i))$ be polytopes with $P_0\cap\bigcap_iS_i\neq\emptyset$. Then (C1) holds iff for every query row $k$ (each side of each band) there are rows $n_{ik}^\top z\le b_{ik}$ implied by $S_i$, with $\mathrm{supp}(n_{ik})\subseteq\mathrm{col}(i)$, such that
$$\rho_k:=N_k-\sum_in_{ik},\qquad h_0(\rho_k)+\sum_ib_{ik}\ \le\ g_k .\tag{F}$$
(If $P_0\cap\bigcap_iS_i=\emptyset$, (C1) holds vacuously; receptiveness excludes this, §4.)

(b) *Per-column conservation.* For every column $c$ and query row $k$,
$$\rho_k[c]\;=\;N_k[c]\;-\;n_{\mathrm{wr}(c),k}[c]\;-\sum_{j\ \text{reads}\ c}n_{jk}[c],$$
and a nonzero imbalance $\rho_k[c]$ is a *leak*. Its price is the support function of $P_0$; for box $P_0$ that is $\max(\rho_cu_c,\rho_c\ell_c)$. A shared variable written by $i$ and read by $j$ thus carries a conserved quantity: the writer's coefficient and the readers' coefficients must sum to the query's own coefficient there, up to a paid leak. Exact cancellation (Kirchhoff) is the zero-leak case. A leak on a system column costs $Y_c|\rho_c|$, the full type range, which is why leaks occur only on environment columns at optimum in all experiments.

(c) *Linearity.* In the certificate parametrisation $(n_{ik},b_{ik},\text{leak epigraph})$, (F) is a system of linear inequalities: **(C1) is jointly linear in normals and offsets.** By contrast:
* with **fixed normals and free multipliers**, the set of offsets $m$ satisfying (C1) is $\{m:\min_{\lambda\in D(M)}\lambda^\top m\le g\}$, a finite *union* of half-spaces over the vertices of the dual polyhedron $D(M)$, and is in general non-convex. Example: Display has rows $d-m_1\le b_1$, $d-m_2\le b_2$, writers $m_1\le a_1$, $m_2\le a_2$, query $d\le g$. Then (C1) iff $\min(a_1+b_1,a_2+b_2)\le g$.
* with **fixed normals in certificate form**, one row per $(i,k)$ known up to a positive scale $\lambda_{ik}$, (F) is linear in $(\lambda,b,\text{leaks})$, with $b$ the scaled offset.

*Proof.* (a) For a nonempty polyhedron $Q=\{Mz\le m\}$, $\max_QN_k^\top z\le g_k$ iff $\exists\lambda\ge0$: $\lambda^\top M=N_k$, $\lambda^\top m\le g_k$ (affine Farkas). Split $\lambda$ by blocks ($P_0$; each $S_i$) and put $n_{ik}:=\lambda_i^\top M_i$, $b_{ik}:=\lambda_i^\top m_i$. The $P_0$-block gives $\lambda_0^\top M_0=\rho_k$, and minimising $\lambda_0^\top m_0$ over such $\lambda_0$ gives $h_0(\rho_k)$ by LP duality ($P_0$ is nonempty and bounded). Conversely, (F) and weak duality give $N_k^\top z=\rho_k^\top z+\sum_in_{ik}^\top z\le h_0(\rho_k)+\sum_ib_{ik}\le g_k$ on $P_0\cap\bigcap S_i$. (b) is (a) read per coordinate, using $\mathrm{supp}(n_{ik})\subseteq\mathrm{col}(i)$. (c) The epigraph of the polyhedral convex function $h_0$ is polyhedral. The union statement is the case analysis $\max_Q N^\top z=\min_{\lambda\in\mathrm{vert}\,D(M)}\lambda^\top m$; the example is direct. $\square$

**Answer to question 1.**
* (C1) looks bilinear only when it is parametrised by rows × multipliers. In certificate form, (C1) is an LP in normals, offsets and leaks *without* the "one row per path" restriction.
* The genuine non-linearity sits in **receptiveness**. It compares the rows of one component that constrain the same output column, which involves ratios of their output coefficients.
* Under the head-band template, receptiveness is linear (Theorem 3(b)) **unless an output column is the head of rows from two different bands whose head coefficients have a free ratio**. There the receptive set is non-convex (Theorem 3(c)): bilinearity is unavoidable.
* Two other sources are avoidable by relaxation:
  * receptiveness *relative to the reachable inputs* $A_i$: the support function of $A_i$ is bilinear in the others' multipliers and offsets. It is replaced by a box (types, or the induced box of Remark 4.3).
  * the sign of each internal pass-through coefficient: a disjunction, removed by the gauge argument (Proposition 5.3).

---

## 3. Which components get rows

**Theorem 2 (support, cone of influence, necessity).**

(a) *Certificate support suffices.* If a Farkas certificate for (C1) uses no row of component $j$, then $S_j:=\mathrm{Tr}(\mathrm{ports}(j))$ preserves (C1). No receptiveness is needed: the certificate proves $P_0\cap\bigcap_{i\neq j}S_i\subseteq G_P$ directly.

(b) *Row-level cone of influence.* Let every row have a head, involve only columns preceding its head in $\mathcal G$, and let the rows sharing a head be jointly satisfiable for every value of their other columns in the box. This is what the LP enforces. Then for each band $k$, (C1)$_k$ holds iff it holds when every row whose head lies outside $C_k$ is deleted. Hence some optimal certificate of band $k$ is supported on $\mathrm{COI}_k$, and components outside $\mathrm{COI}_k$ need no row for band $k$.

(c) *Necessity by domination.* Let $c\in\mathrm{supp}(N_k)$ be an environment column on which $A_P$ is a box factor $[\ell_c,u_c]$, or an output of $i$ (then $[\ell_c,u_c]=[-Y_c,Y_c]$). Suppose that, after deleting $\mathrm{out}(i)\setminus\{c\}$ from $\mathcal G$, $c$ reaches no other column of $\mathrm{supp}(N_k)$, and that $\tfrac12(u_c-\ell_c)\,|N_k[c]|>g_k$. Then every valid receptive causal delegation gives $i$ a nontrivial obligation.

*Proof.*
(a) Weak duality as in Theorem 1(a).

(b) "If" is monotonicity. For "only if", take $z\in P_0$ satisfying all rows with heads in $C_k$. Keep $z$ on environment columns and on $C_k$. Re-choose the remaining system columns in a topological order of $\mathcal G$:
* a column that is a head gets a value in the intersection of its rows, which is nonempty for every value of the preceding columns, by hypothesis;
* any other column gets $0$.

Rows with heads in $C_k$ involve only columns preceding their heads, which lie in $C_k$ (backward closed), so they are unchanged. Rows with heads outside $C_k$ hold by construction. The new point lies in $P_0$ by the product structure and agrees with $z$ on $\mathrm{supp}(N_k)\subseteq C_k$. Farkas applied to the reduced system gives the certificate.

(c) Suppose $S_i$ is trivial. Let $D$ be the set of columns reachable from $c$ without passing through $\mathrm{out}(i)\setminus\{c\}$. Every component other than $i$ that reads a column of $D$ writes into $D$. So the rows whose heads lie outside $D\cup\mathrm{out}(i)$ involve no column of $D$ (receptive components do not constrain inputs; rows involve preceding columns only). Given a valid trace $z$, set $z_c$ to any value in $[\ell_c,u_c]$ (if $c\in\mathrm{out}(i)$ this is allowed because $S_i$ is trivial). Re-choose $D\setminus\{c\}$ in topological order by receptiveness, keeping everything else. The result is valid and agrees with $z$ on $\mathrm{supp}(N_k)\setminus\{c\}$. Hence $N_kz$ ranges over an interval of length at least $(u_c-\ell_c)|N_k[c]|>2g_k$, which no band of half-width $g_k$ contains. $\square$

**Chain of inclusions.** $\mathrm{Nec}_k^{\mathrm{dom}}\subseteq\mathrm{Nec}_k^{\mathrm{LP}}\subseteq\mathrm{supp}_{R^\*}(k)\subseteq\mathrm{Nec}_k^{\mathrm{LP}}\cup\mathrm{Poss}_k\subseteq\mathrm{COI}_k\subseteq\mathrm{COI}(W)$, where:
* $\mathrm{Nec}^{\mathrm{LP}}_k$: the LP with $i$'s row removed is infeasible;
* $\mathrm{Poss}_k$: positive *claim*, i.e. maximal single share;
* $\mathrm{COI}(W)$: the variable-level cone of influence (bystanders, foundations §10).

Both inner inclusions can be strict:
* (c) fan-in is a knife edge. $\tfrac12(u_{s_1}-\ell_{s_1})\cdot1=1=g$, so $A$ is not LP-necessary (it can be dropped if everyone else is exact), yet $R^\*$ involves it.
* (d'') loop with physical Plant normal. Perception is LP-necessary, since it must *cancel* the Plant's $x(t)$ coefficient, but it is not a dominator. Theorem 2(c) is sufficient, not necessary.

**A component on an $A_P\to G_P$ path that gets $(\mathrm{true},\mathrm{true})$.**
* Loop (d), free normals: Perception lies on the path $x(0)\to\text{Perception}\to\hat x(0)\to\text{Controller}\to u(0)\to\text{Plant}\to x(1)$, from the $A_P$ variable $x(0)$ to the $G_P$ variable $x$.
* Its claim is $\frac12>0$, so it *could* carry budget. But involving it lowers everyone: support $\{P,C\}$ gives shares $(\frac14,\frac14,+\infty)$, support $\{P,C,\mathrm{Perc}\}$ gives $(\frac16,\frac16,\frac16)$, and $R^\*$ prefers the former.
* The model-free decomposition sends the $x(0)$ coefficient to zero (Plant obligation $x(t{+}1)\approx\frac35u(t)$), so no information about $x$ needs to flow. A rule-independent case: any component whose on-path outputs fall outside $C_k$ because of delays and the horizon. For example, a delay-1 Radio at $H=0$ writes nothing inside the horizon.

---

## 4. Receptiveness and causality as linear conditions

$S_i$ is receptive and causal if
$$\forall\mathrm{in}(0)\,\exists\mathrm{out}(d_i)\,\forall\mathrm{in}(1)\,\exists\mathrm{out}(1{+}d_i)\cdots\ (\mathrm{in},\mathrm{out})\in S_i\quad[\text{A§3, A§5(g)}],$$
with inputs ranging over a box $X$ (types, or $A_P$ on environment columns) and outputs over their types.

**Theorem 3.**

(a) *Fixed normals: exact and polyhedral in the offsets.* For a polytope $S_i=\{M^{o}y+M^{x}x\le m\}$ with $M$ fixed, the set $R_i(M)$ of offsets $m$ for which $S_i$ is receptive and causal is a polyhedron. It is computed by alternating two operations from the innermost quantifier outwards:
* $\exists y_t$: Fourier–Motzkin elimination, i.e. projection of a polyhedron in $(m,\cdot)$;
* $\forall x_t\in X_t$: for each resulting inequality $\gamma^\top(\cdot)+\delta^\top x_t\le\eta(m)$, replace $\delta^\top x_t$ by the support function $h_{X_t}(\delta)$. This is exact because $\forall$ distributes over $\wedge$.

Without causality this is "the projection of $S_i\cap(\text{output types})$ onto the inputs covers $X$". Equivalently, there are vertex scenarios $\exists y^v$ for each vertex $x^v$ of $X$, a single LP in $(m,y^v)$ with $2^{\dim X}$ copies; the causal version is a scenario tree. The inequality count can be exponential. Deciding receptiveness of a given polytope in general is the feasibility of an adjustable robust LP, which is known to be intractable in general (Ben-Tal, Goryashko, Guslitser, Nemirovski 2004). We do not use or re-prove a hardness result.

(b) *Head-band template: polynomial, jointly linear in normals and offsets.* Take one band row with head $h$, $c\neq0$, and other columns over the box $X$. For every value of the other columns there is $z_h\in[-Y_h,Y_h]$ satisfying the row iff
$$w\ge0,\qquad |c|Y_h+w-\kappa-h_X(-\beta)\ \ge\ 0,\qquad |c|Y_h+w+\kappa-h_X(\beta)\ \ge0 .\tag{R}$$
(For $c=0$ the same two inequalities say that the input-only band is implied by the box, i.e. it does not constrain the inputs.) With the sign of $c$ fixed, (R) is convex piecewise-linear $\le$ linear, hence LP-representable jointly in $(c,\beta,\kappa,w)$. For symmetric $X$, the classical band $|y-Lx-\kappa|\le w$ is receptive iff $w\ge0$ and $h_X(L)+|\kappa|\le Y_y+w$. That makes precise "bands with $w\ge0$ are receptive if the types allow".

**Causality.** In the template, row$_{ik}$ involves only inputs at times $\le t(h)-d_i$ and own outputs at times $<t(h)$. If every head satisfies (R), with own past outputs ranging over their type box, then the strategy "at each head, pick a value in the row's interval" is causal and its graph lies in $G_i$. So $G_i$ is receptive and causal. This is sufficient. It is exact when no own past output occurs in a row; otherwise it is conservative.

(c) *Where it stops being convex.* Two rows of one component on the same head with free coefficient ratio, e.g. $y\le b_1$ and $-cy\le b_2$ with $|y|\le10$, have a non-convex receptive set: receptive at $(c,b_1,b_2)=(1,-1,1)$ and $(3,1,-3)$, not at the midpoint $(2,0,-1)$ (Z3 confirms, log line 112). In the architecture this is a **shared head**: one output column heading rows of two bands (fan-out of a signal to two query bands, or one signal used at two query times). If the head coefficients are tied ($c_k=c_{k'}$, a common variable), the cross-band pair conditions $\frac{\kappa_k+w_k-\beta_k^\top x}{c}\ge\frac{\kappa_{k'}-w_{k'}-\beta_{k'}^\top x}{c}$ for all $x$ are again linear.

*Proof.* (a) Each $\exists$ step is a linear projection, so polyhedra map to polyhedra in $(m,\text{remaining})$. Each $\forall$ step over a box is an intersection over the box's vertices, or equivalently the support-function substitution row by row. Both preserve polyhedrality and treat $m$ as a variable throughout. (b) For $c>0$ the feasible $z_h$ form the interval $[(\kappa-w-\beta^\top x)/c,(\kappa+w-\beta^\top x)/c]$. It meets $[-Y_h,Y_h]$ for all $x\in X$ iff $w\ge0$, $\kappa-w-\beta^\top x\le cY_h$ for all $x$, and $\kappa+w-\beta^\top x\ge-cY_h$ for all $x$; take the maxima over $x$. For $c<0$ the interval flips. Causality: the head's interval depends only on columns that precede it. (c) Direct computation; the tied case is (b) with a common factor $c>0$. $\square$

**Remark 4.3 (relative receptiveness).** The exact requirement for the handed-out $S_i=\neg A_i\cup G_i$ is receptiveness *relative to* $A_i$. That is bilinear, since $A_i$ depends on the other rows. The LP uses a box instead:
* the **type box**, for which Theorem 4 gives a proof;
* or the **induced box**: the range of each column under $P_0$ and the query bands whose columns all precede the head (used in (d'')). Soundness of the induced box is then *checked* by Z3 relative to the time-sliced $A_i^h$, not proved.

---

## 5. The choice rule

Fix a band $k$. Let $\mathcal D_k(I)$ be the polyhedron of Theorem 1 with Theorem 3(b), using rows only for $I\subseteq\mathrm{COI}_k$. The *share* of $i$ is $w_{ik}$, its half-width in budget units. The *margins* $\mu^\pm_{ik}$ are the two left sides of (R). Bands are independent LPs when no head is shared.

**Definition ($R^\*$).**
1. **Support.** For each feasible $I$ with $\mathrm{Nec}^{\mathrm{LP}}_k\subseteq I\subseteq\mathrm{COI}_k$, let $\sigma(I)$ be the water-filling share vector on $I$ (step 2). The *extended freedom vector* gives $i\in I$ the value $\sigma_i(I)$ and $i\notin I$ the value $+\infty$. Choose $I^\*$ maximising the sorted extended vector lexicographically.
2. **Shares.** Leximin of $(w_{ik})_{i\in I^\*}$ over $\mathcal D_k(I^\*)$, computed by water-filling: raise a common level $t$; freeze the coordinates that cannot exceed $t$ (one LP each); repeat.
3. **Gains.** With the shares fixed, leximin of the margins $(\mu^\pm_{ik})_{i\in I^\*}$.
4. **Certificate.** For every decision variable, minimise and maximise it over the final face. If all spreads vanish the delegation is unique; otherwise report the face and return its minimum-$\ell_1$ point. Report the sign gauge of internal heads with positive dominant gain (Proposition 5.3).

**Proposition 5.1 (uniqueness of shares and margins).** For a convex compact attainable set $F\subseteq\mathbb R^p$ of a linear map, the leximin-optimal vector is unique and equals the water-filling output. At every stage at least one coordinate is blocked.

*Proof.* Let $t_s$ be the stage optimum and $F_s$ the stage set. If no free coordinate were blocked, pick $f^j\in F_s$ with $f^j_j>t_s$ for each free $j$. Their average lies in $F_s$ (convex) and has all free coordinates $>t_s$, contradicting the optimality of $t_s$. Blocked coordinates equal $t_s$ on $F_s$, hence on every later $F_{s'}\subseteq F_s$. Any $f\notin F_s$ has some free coordinate below $t_s$ while all earlier coordinates are at their levels, so its sorted vector is lexicographically smaller than that of any point of $F_s$. Hence every leximin optimum lies in $\bigcap_sF_s$, where every coordinate equals its blocking level. $\square$

**Proposition 5.2 (ties).**
* Within a support, shares and margins are unique (Proposition 5.1).
* Ties in $R^\*$ arise only (i) between supports with equal sorted extended vectors (redundant symmetric routes), or (ii) as a non-point final face. Case (ii) is certified by $2\times\#$variables LPs.
* In all 17 solved band LPs of the experiments (one more was infeasible by design) the spread is $\le3\cdot10^{-8}$ (unique) and there were no support ties.

**Proposition 5.3 (covariance).** Two transformations map $\mathcal D_k(I)$ to itself and preserve shares, margins and leak costs, so $R^\*$ commutes with them:
* rescaling an internal variable ($z_v\mapsto\alpha z_v$, $Y_v\mapsto\alpha Y_v$, $\alpha>0$; coefficients on $v$ scale by $1/\alpha$);
* flipping the sign of an internal column with a symmetric type.

*Proof.* The terms are invariant: $|c|Y_h$, $h_X(\beta)$ (coefficient times box), and the leak cost $\rho_cu_c$; the flow equations have $N_k[c]=0$ on internal columns. $\square$

The sign-of-$c$ disjunction is therefore pure gauge for internal heads (fix $c\ge0$). It is not a choice the rule has to make, except for shared heads (Theorem 3(c)).

**Justification.**
* Step 1 encodes "only some components receive a contract": an uninvolved component is maximally free. The $+\infty$ convention also handles knife edges correctly. In (c), excluding $A$ forces everyone else to be exact, $(0,0,\infty)$, which loses to $(\frac13,\frac13,\frac13)$.
* Step 2 is max-min fairness, i.e. the constrained-equal-awards rule of bankruptcy problems with the claims as caps. It is anonymous and consistent.
* Step 3 centres every interface signal in its type range: the worst headroom between a band and its type limit is maximised. This is robustness of implementability, measured in budget units, which is what makes it covariant.

Measuring widths in each component's own output units is gauge-dependent. Maximising the minimum relative width $w/(|c|Y_h)$ (proportional-to-type) is covariant, but drives gains to the receptiveness boundary: Radio's margin becomes $0$ in the table below. That is the "use the whole channel range" effect, and it is fragile.

**Relay comparison** (log lines 28–34; widths in budget units; Radio obligation $|m-r/c|\le w_R/c$, Display $|d-cm|\le w_D$):

| rule | $w_R$ | $w_D$ | $c$ | Radio | Display | comment |
|---|---|---|---|---|---|---|
| $R^\*$ | 0.25 | 0.25 | 1 | $\|m-r\|\le0.25$ | $\|d-m\|\le0.25$ | unique, margins $\frac54,\frac54$ |
| proportional-to-type, $R^\*$ gains | 0.20 | 0.30 | 1 | $\|m-r\|\le0.2$ | $\|d-m\|\le0.3$ | the relay split of foundations §11 |
| proportional-to-type, free gains | 0.114 | 0.386 | 0.443 | $\|m-2.257r\|\le0.257$ | $\|d-0.443m\|\le0.386$ | Radio margin $0$: saturates $\|m\|\le2$ |
| slack-to-first, Radio first | 0.5 | 0 | 0.875 | $\|m-1.143r\|\le0.571$ | $d=0.875m$ | = sweep from the copy seed (foundations §9) |
| slack-to-first, Display first | 0 | 0.5 | 1.125 | $m=0.889r$ | $\|d-1.125m\|\le0.5$ | order-dependent |

---

## 6. The procedure

**Algorithm DECOMPOSE**$(\mathcal A,P)$
1. Unroll to columns. Build $\mathcal G$ (delay and memory edges) and $P_0$.
2. For each band $k$:
   1. compute $C_k$, $\mathrm{COI}_k$, the heads and $\mathrm{Caus}(i,k)$;
   2. flag shared heads;
   3. compute $\mathrm{Nec}^{\mathrm{LP}}_k$ ($|\mathrm{COI}_k|$ feasibility LPs) and the claims;
   4. run $R^\*$ (§5) and obtain the rows $(c_{ik},\beta_{ik},\kappa_{ik},w_{ik})$.
3. $G_i:=\bigwedge_k\mathrm{row}_{ik}$. Components with no row get $(\mathrm{true},\mathrm{true})$.
4. Assumptions, by existential projection (Z3 `qe2`, cross-checked):
   - full horizon: $A_i:=\pi_{\mathrm{in}(i)}\big(P_0\wedge\bigwedge_{j\ne i}G_j\big)$;
   - time-sliced, for each head $h$ of $i$: $A_i^h:=\pi_{\{c\in\mathrm{in}(i):\,t(c)\le t(h)-d_i\}}\big(P_0\wedge\bigwedge_{j\ne i}G_j\wedge\bigwedge_{h'\in\mathrm{heads}(i),\,t(h')<t(h)}\mathrm{row}_{h'}\big)$, and the obligation $S_i^{ts}:=\bigwedge_h(A_i^h\rightarrow\mathrm{row}_h)$.
5. Output $(A_i,G_i)$ (acyclic support), or the time-sliced contract (general).

**Theorem 4 (soundness).** Suppose every band LP is feasible with type-box receptiveness and no head is shared. Then:
1. $P_0\wedge\bigwedge_iG_i\Rightarrow G_P$.
2. The time-sliced contracts satisfy (C1) and (C2) (every $A_i^h$), and each $S_i^{ts}$ is receptive and causal.
3. If the support graph is acyclic after removing self-loops, the full-horizon $(A_i,G_i)$ satisfy (C1), (C2), receptiveness and causality. The support graph has an edge $j\to i$ when both are involved and $i$ reads a column written by $j$; trivial components cut paths.
4. Item 3 fails without acyclicity: in (d′) and (d″) Z3 returns traces where every assumption is false and $G_P$ fails (log lines 398–399, 477–478).

*Proof.*
(1) Theorem 1(a), weak direction.

(2) Topologically order the system columns of $\mathcal G$. Every row involves only columns preceding its head. Let $z\in P_0\cap\bigcap_iS_i^{ts}$; we show by induction over heads that every row holds at $z$.

For the head $h$ of $i$, all rows with earlier heads hold. Build $z'$:
* equal to $z$ on environment columns and on all columns before $h$, which include the columns of $A_i^h$ and the heads of $i$'s rows at times $<t(h)$ (memory edges);
* then re-choose $h$ and the later columns in order. A head of some $j\neq i$ gets a value in its row's interval (type-box receptiveness); every other column gets $0$.

Then $z'\in P_0\wedge\bigwedge_{j\ne i}G_j\wedge(\text{own earlier rows})$ and $z'$ agrees with $z$ on the columns of $A_i^h$. So $A_i^h(z)$ holds, and $S_i^{ts}(z)$ gives $\mathrm{row}_h(z)$. Hence $z\in\bigcap G_i$ and (1) applies. (C2) is the line "$A_i^h(z)$". Receptiveness: $S_i^{ts}\supseteq G_i$, and $G_i$ is causally receptive by Theorem 3(b).

(3) Induct along a topological order of the support graph. To show $A_i(z)$, keep $z$ on environment columns, on the outputs of $i$'s involved ancestors (valid by induction), and on $i$'s own and trivial components' outputs. Re-choose the outputs of the other involved components in topological order by receptiveness. The inputs of $i$ are unchanged. The rest is as in (2). $\square$

**Complexity.**

Notation:
* $n$ components, $K$ bands ($K=$ #band templates $\times(H+1)$ for a $\square$ query), $p=\max_i|\mathrm{ports}(i)|$;
* $q_k=|\mathrm{COI}_k|\le n$ and $o_k=|\mathrm{COI}_k\setminus\mathrm{Nec}^{\mathrm{LP}}_k|$.

Costs:
* One band LP has $O(q_kp(H+1)+|C_k|)$ variables and constraints.
* Claims and necessity take $2q_k$ LPs.
* Supports take $2^{o_k}$ water-fillings, each $\le q_k(q_k+1)$ LPs.
* Margins take $\le2q_k(2q_k+1)$ LPs; the certificate $O(q_kp(H+1))$ LPs.
* The LP stage is therefore polynomial in $(n,K,H)$ except for the factor $2^{o_k}$.
* Checking (C1) for $\bigcap G_i$ is $2K$ LPs. Projection is the expensive step: $n$ (full) or $\sum_i\#\mathrm{heads}(i)$ (time-sliced) eliminations of up to $|V|(H+1)$ variables, worst case exponential (Fourier–Motzkin).

Measured: the whole suite (11 system runs, 18 band problems, all Z3 checks) runs in 2.2 s; the largest system, the loop at $H=2$ with 11 columns, takes 0.1 s for LPs and 0.4 s for projections and checks.

---

## 7. Experiments

$R^\*$ unless stated. Rows are shown normalised by the head coefficient; "budget" shares are in units of the query bound. Z3 columns:
* C1G: $P_0\wedge\bigwedge G_i\Rightarrow G_P$;
* C1/C2 full: full-horizon contracts;
* C1/C2 ts: time-sliced contracts;
* RC: receptive and causal, time-sliced obligations of the involved components.

| system | involved, shares | delegated guarantees $G_i$ | assumptions $A_i$ | C1G | C1 full | C2 full | C1 ts | C2 ts | RC |
|---|---|---|---|---|---|---|---|---|---|
| (a) relay, $\|r\|\le1,\|m\|\le2,\|d\|\le3$, $\|d-r\|\le\frac12$ | Radio $\frac14$, Display $\frac14$ | $\|m-r\|\le\frac14$; $\|d-m\|\le\frac14$ | $\|r\|\le1$; $\|m\|\le\frac54$ | T | T | T | T | T | T,T |
| (b) chain $r\to m_1\to m_2\to d$ ($Y=1,2,2,3$) | Radio, Relay, Display $\frac16$ each | $\|m_1-\frac65r\|\le\frac15$; $\|m_2-\frac57m_1\|\le\frac17$; $\|d-\frac76m_2\|\le\frac16$ | $\|r\|\le1$; $\|m_1\|\le\frac75$; $\|m_2\|\le\frac87$ | T | T | T | T | T | T,T,T |
| (c) fan-in, $\|s_i\|\le1$, $\|a\|,\|b\|\le2$, $\|f\|,\|\log\|\le3$, $\|f-s_1-s_2\|\le1$ | A, B, Fuser $\frac13$ each; Logger trivial | $\|a-\frac32s_1\|\le\frac12$; $\|b-\frac32s_2\|\le\frac12$; $\|f-\frac23(a+b)\|\le\frac13$ | $\|s_1\|\le1$; $\|s_2\|\le1$; types | T | T | T | T | T | T,T,T |
| (d) loop, $H=2$, Plant delay 1, free normals | Plant, Controller $\frac14$ each (both bands); Perception trivial | Plant $\|x(t{+}1)-\frac35u(t)\|\le\frac14$; Controller $\|u(t)-\frac53r(t)\|\le\frac5{12}$ | Plant: $\|x(0)\|\le1$, $\|u(t)\|\le\frac{25}{12}$, $\|w\|\le\frac15$; Controller: types | T | T | T | T | T | T,T |
| (d′) loop, egalitarian-over-COI | all three $\frac16$ | Plant $\|x(t{+}1)-\frac{11}{15}u(t)\|\le\frac16$; Perception $\|\hat x(t)\|\le\frac58$ (range only!); Controller $\|u-(\frac{15}{11}r+\frac4{11}\hat x)\|\le\frac5{22}$ | (projections) | T | **F** | **F** | T | T | T,T,T |
| (d″) loop, Plant normal fixed to $x(t{+}1)-x(t)-u(t)-w(t)$, induced boxes | all three $\frac1{10}$ (both bands; $w$-leak costs $0.2$) | Plant $\|x(t{+}1)-x(t)-u(t)-w(t)\|\le\frac1{10}$; Perception $\|\hat x(0)-2x(0)\|\le\frac15$, $\|\hat x(1)-\frac{20}{11}x(1)\|\le\frac2{11}$; Controller $\|u(0)-r(0)+\frac12\hat x(0)\|\le\frac1{10}$, $\|u(1)-r(1)+\frac{11}{20}\hat x(1)\|\le\frac1{10}$ | e.g. Plant: $\|x(t)+u(t)\|\le\frac65$, $\|x(0)\|\le1$ | T | **F** | **F** | T | T | T,T,T |
| (e) fan-out $r\to m\to\{d_1,d_2\}$, bands $\|d_1-r\|,\|d_2+r\|\le\frac12$, $\|d_2\|\le3$ | shared head $m$ | Radio $\|m-r\|\le\frac14$ (twice); $\|d_1-m\|\le\frac14$; $\|d_2+m\|\le\frac14$ | — | T | T | T | T | T | T |
| (e) same, $\|d_2\|\le1.2$ | shared head, per-band optima disagree | Radio $\|m-r\|\le\frac14$ and $\|m-\frac{20}{11}r\|\le\frac5{11}$ | — | T | T | T | T | T | **Radio F** |
| (e) same, head coefficient tied $c=1$ | — | band 2 LP infeasible ($D_2$ cannot echo $\|m\|\le2$ into $\|d_2\|\le1.2$) | — | | | | | | |
| (e) same, tied $c=\frac{11}{20}$ | Radio, $D_1$, $D_2$ $\frac14$ | Radio $\|m-\frac{20}{11}r\|\le\frac5{11}$ (both) | — | T | T | T | T | T | T |

Notes on the table.
* **(d)** The model-free decomposition of the tracking query is *open loop*. Since nothing forces the Plant to integrate, the cheapest certificate sends the $x(t)$ coefficient to zero. Perception's claim is $\frac12$, but involving it would lower the others, so $R^\*$ leaves it out.
* **(d″)** Fixing the Plant's physical normal makes the $x(t)$ coefficient $-1$. Leaking it would cost $1>0.3$, so it must be cancelled through Controller and Perception, which makes Perception LP-necessary. With the remaining budget $0.5-0.2=0.3$, $R^\*$ derives the $0.1/0.1/0.1$ widths that the tracking-loop example (foundations §11) chooses by hand. The composite gain from $x$ to $u$ is $-1$, as physics requires. The individual gains ($\hat x\approx2x$, $u\approx r-\frac12\hat x$) are the margin-centred representatives of a covariance orbit (Proposition 5.3): the type of $\hat x$ is 5, larger than the range of $x(0)$, which is 1.
* **(d″)** Bare $G_i$ over the *type* box is not receptive for Plant and Perception: Plant's $x(1)+u(1)$ can exceed $5$. The full-horizon $S_{\mathrm{Perc}}$ is not receptive either. The time-sliced $S_i^{ts}$, whose $A_i^h$ include own earlier rows, is receptive for all three. This is why step 4 of the algorithm includes own earlier rows.
* **(d′)** The egalitarian-over-COI rule gives Perception a share by making it *range-limit* $\hat x$, not by feedback. This pointless obligation is the main argument for step 1 of $R^\*$. It also creates a cyclic support, and the full-horizon handout then fails (C1). The counterexample trace has all three assumptions false.
* **(e)** The per-band LP is sound band by band but blind to the cross-band receptiveness of a shared head (Theorem 3(c)). The script warns, and Z3 catches the failure. Tying the coefficients restores both linearity and receptiveness; choosing the tie value is the bilinear step and is not automated.

---

## 7½. Limits: $\vee$ and $\lozenge$

If $G_P$ contains $\vee$ or $\lozenge$, its unrolling is a finite union $\bigcup_\ell Q_\ell$ of polytopes, and the following breaks:
1. (C1) asks a polytope $P_0\cap\bigcap S_i$ to lie in a union. That is not row-wise and not equivalent to lying in one piece ($[0,2]\subseteq[0,1]\cup[1,2]$), so Theorem 1 loses its "iff". A certificate becomes a polyhedral *cover* of the delegation polytope with one Farkas certificate per cell. The cells are unknown and depend on the obligations, so (C1) is no longer jointly linear.
2. The best obligations are themselves unions (e.g. the relay cut set, foundations §11), so receptiveness (Theorem 3) is again a $\forall\exists$ over a non-convex set.
3. The feasible parameter set becomes a union of polyhedra. Proposition 5.1 fails: leximin over a non-convex set has ties, and "which component takes which disjunct" is a combinatorial choice that the order of the fixed-point sweep (foundations §9) settles arbitrarily.
4. Theorem 2(b),(c) survive per disjunct, but the support can differ between disjuncts.

---

## 8. Summary of results

1. **(C1) is jointly linear in normals and offsets** in certificate form (Theorem 1(c)), including when the normals are unknown. Conversely, fixed normals with free multipliers give a *non-convex* union of half-spaces in the offsets. "Linear in the offsets with fixed normals" holds only in certificate form.
2. **The leaky-flow reading**: per-column conservation between writer and readers, with leaks priced by the support function of $A_P\wedge$types. It states exactly when imbalance is allowed.
3. **Bilinearity is localised in receptiveness** (Theorem 3(c)): shared heads with free coefficient ratio, witnessed by Z3 and by the fan-out run.
4. **Causal receptiveness is polyhedral in the offsets for fixed normals** (Theorem 3(a)), by alternating Fourier–Motzkin and support functions. Under the head-band template it reduces to the two inequalities (R).
5. **Support and necessity.**
   - Certificate support yields $(\mathrm{true},\mathrm{true})$ *without* receptiveness (Theorem 2(a)).
   - A row-level, time-expanded cone of influence with memory edges (Theorem 2(b)).
   - A domination criterion with an explicit threshold $\frac12(u_c-\ell_c)|N_k[c]|>g_k$ (Theorem 2(c)), plus two examples showing that it is only sufficient and that LP-necessity is not the involved set.
6. **A canonical choice rule** $R^\*$ that is LP-computable, unique in shares and margins, covariant, and comes with a uniqueness certificate. It is compared with proportional and slack-to-first rules.
7. **The seed problem is solved in the conjunctive fragment.** DECOMPOSE outputs a valid, receptive, causal delegation directly, i.e. a member of $\mathcal V$, which is the seed that the fixed-point sweep (foundations §9) needs to reach a maximal fixed point. The sweep was not rerun here.
8. **Handouts on cycles.** Full-horizon projected assumptions are unsound for cyclic supports (Z3 counterexamples in (d′), (d″)). Handing out projected assumptions one component at a time is therefore sound only sequentially or acyclically. The fix is the time-sliced $A_i^h$, which include the component's own earlier guarantees (Theorem 4). It is a time-inductive circular rule (each component may assume the others' guarantees at earlier times) produced by projection, not by hand.
9. **Model-free decomposition opens loops.** The canonical decomposition of the tracking query never needs feedback. Feedback appears exactly when a physical normal is fixed, and then $R^\*$ reproduces the hand-chosen contracts of the tracking-loop example (foundations §11).

## 9. Open items (not proved here)

* **Joint multi-band LP with tied shared heads.** Its linearity is proved (Theorem 3(c)). The implementation only supports manual ties. Choosing the tie canonically (a 1-D search per shared head) is the remaining bilinear step.
* **Relative receptiveness.** *Conjecture*: replacing $h_{A_i}$ by auxiliary range rows certified by the other components (one Farkas certificate per head) gives an LP that is exact for relative receptiveness. Missing: termination and size bound of the recursion, and a proof that the induced box of Remark 4.3 is always sound.
* **Completeness of the head-band template.** Is every valid receptive conjunctive delegation of a symmetric band query refined by a template delegation? Open. Theorem 1 gives one row per $(i,k)$, but not band shape or a single head.
* **Support search.** Is the $2^{o_k}$ factor avoidable? Greedy addition is correct on all examples but unproved.
