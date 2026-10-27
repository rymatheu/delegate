# Interface cuts: what an edge must carry, the canonical encoding, and when no delegation exists

_Slice "interface", 2026-10-18. Script: `scripts/interface_cuts.py` (all checks pass; output summarised in §8).
Builds on `theory/foundations.md`, cited as "foundations §n" (the projections $\Pi,\pi$ and ghost-freeness §6,
vacuity §7, the fixed-point sweep and seeds §9, the relay running example and its relay cut set §11). Nothing proved there
is re-proved here. (Seq) denotes the sequential rule: a cut formula $I$ over the interface is handed from upstream $U$ to
downstream $D$, with $\{A_P\}U\{I\}$ and $\{I\}D\{G_P\}$. (Circ) denotes a time-inductive circular rule._

---

## 0. Results in one table

| # | Statement | Status | Class |
|---|---|---|---|
| L1 | **Fibre lemma.** A cut $(U,D)$ admits a valid receptive delegation iff the upstream relation $K\subseteq X\times E$ is receptive and every reachable fibre $F(e)$ is *robustly decodable* by $D$. | proved | any obligations |
| P2 | Linear query: robust decodability is a finite set of Farkas-ray inequalities $\sigma_F(\lambda^\top N_X)+\Delta_\lambda(F)\le\beta_\lambda$. The *information deficit* $\Delta_\lambda$ is the tolerance-budget term. For a band $\lvert\ell x+\dots\rvert\le\varepsilon$ it says $\mathrm{width}_\ell F(e)\le2\varepsilon$. | proved | conjunctive $G_P$ |
| T3 | **Rank theorem.** If the upstream obligations are conjunctive (closed polytopes) and $n$ jointly informative bands cross the cut, then $n\le k=\dim E$. The proof separates sets and counts hyperplane-arrangement cells. Downstream obligations are arbitrary. | proved | conjunctive upstream |
| T4 | **Exact queries.** With zero tolerance ($\varepsilon_i=0$), no PolySTL delegation (any finite union of polytopes) exists when $n>k$. | proved | all PolySTL |
| T5 | **Capacity theorem (type bounds plus tolerance).** If upstream must leave slack $a_j$ on each edge coordinate, then $\prod_i\lceil W_i/2\varepsilon_i\rceil\le\prod_j Y_j/a_j$. | proved | **any** obligations |
| P6 | **Sharpness.** T3 does not extend to disjunctive obligations: a 4-piece quantizer carries the 2-D signal through the 1-D edge (Z3-verified). | verified | |
| T7 | **Sufficiency, one cut.** If $n\le k$ (causally), the edges are pure interface, the environment is independent, and the "ideal relay" has margin, then the canonical encoding $\chi_a=\{\lvert e-TLx\rvert\le a\}$ is a valid seed for every $a<a^*$. | proved | conjunctive coupling |
| P9 | On the relay ($n=k=1$, box prior), the type-scaled canonical encoding attains the T5 bound. It is optimal among *all* encodings, including disjunctive ones. | proved + verified | |
| §4 | Multi-path: the coefficients form a flow with conservation (the Farkas row decomposition in graph form). Type capacity at query outputs forces how a coefficient is split. The vector case is network coding: routing fails on the butterfly and a linear code succeeds. | verified; multicast sufficiency cited | |
| §5 | Craig interpolants over $E\cup$ghosts are **exactly** the (Seq) cuts. Strongest = the $\pi$-cut (foundations §6), weakest = $\Pi(\neg B)$. The Farkas interpolant is the canonical encoding. **Interpolation does not choose anything.** | proved + verified | |
| T11 | **Non-existence report.** Gives (cut, functional, $n$, $k$, budgets) with four strengths: $k=0$ (any delegation), $n>k$ (conjunctive), $\varepsilon=0$ (PolySTL), robust (any). | proved | |

---

## 1. Setting

Everything is as in `theory/foundations.md` §§1–7: traces over $[0,H]$, types $\lvert v\rvert\le Y_v$, obligations $S_i=\neg A_i\cup G_i$ over $\ports(i)$, validity (C1)/(C2), receptive and causal ("realizable"). $\Pi_W$ is the universal projection and $\pi_W$ the shadow. Statements are for $H=0$. With $H>0$ they apply to the time-expanded graph (one node per component and time step), which is acyclic because every cycle has a delay; see Cor. 12.

**Cut.** A partition $\Sys=U\sqcup D$ such that no variable written in $D$ is read in $U$ ($U$ is upstream-closed). Put
$$X:=\ports(U)\setminus\ports(D),\qquad E:=\ports(U)\cap\ports(D),\qquad Y:=\ports(D)\setminus\ports(U).$$
$X$ holds $U$'s environment inputs $W_U$ and its private outputs. $E$ holds $U$'s outputs that $D$ reads (the edge variables), $k:=\dim E$. $Y$ holds $D$'s environment inputs $W_D$ and its outputs $O_D$.

**Standing assumptions** (each is used where stated; §6 says what breaks without it).
- (Ind) *Independent environment:* $A_P=A_X(W_U)\wedge A_Y(W_D)$. The environment seen by $U$ carries no information about the environment seen by $D$, so $E$ is the only channel.
- (Pure) *Pure interface:* $G_P$ does not mention $E$. This only matters for sufficiency (T7), because an edge pinned by the query cannot also be a free code.
- No environment variable is read by both sides. Such shared variables are common information and only condition the fibres.

**Query.** Conjunctive part: $G_P=\{N_Xx+N_Ee+N_Ww_D+N_Oo\le g\}$, with $D$'s output type rows included. A **coupling row** has $N_{X,k}\neq0$ and $N_{O,k}\ne0$. The **needed functional** of the cut is a basis $L$ (an $n_L\times\dim X$ matrix) of $\mathrm{span}\{N_{X,k}:k\text{ coupling}\}$, computed by SVD in the script. A **band** across the cut is a pair of rows that reads
$$\lvert\ell^\top x+c^\top o+h^\top e+q^\top w_D-g_0\rvert\le\varepsilon,\qquad \ell\neq0,\ c\neq0 .$$
The band is **informative** if the prior width $W_\ell:=\max_{A_X}\ell^\top x-\min_{A_X}\ell^\top x$ exceeds $2\varepsilon$.

Relay: $X=\{r\}$, $E=\{m\}$, $O=\{d\}$. One band, $\ell=r$, $\varepsilon=0.5$, $W=2>1$. $L=[1]$, $n=k=1$.

---

## 2. The information requirement of a cut

### 2.1 Fibre lemma (exact)

Let $K:=\pi_{X\cup E}\big(A_P\cap\bigcap_{j\in U}S_j\big)$ be the **upstream relation**: which edge values $U$ may emit for which private values. Its fibres are $F(e):=\{x:(x,e)\in K\}$.

**Lemma 1.** Assume (Ind) and an acyclic architecture. A tuple of receptive causal obligations is valid (C1) iff there is a map $f_D:(e,w_D)\mapsto o$, realizable by $D$'s components, such that
$$\forall e\in\pi_EK\ \ \forall w_D\in A_Y\ \ \forall x\in F(e):\quad (x,e,w_D,f_D(e,w_D))\in G_P. \tag{RD}$$
Conversely, if $K$ comes from receptive causal $U$-obligations and some realizable $f_D$ satisfies (RD), then $(S_U,\ \Pi_D(A_P\wedge\bigwedge_US_j\to G_P))$ is valid, receptive and causal.

*Proof.* (⇒) Compose $D$'s strategies in topological order ($D$ reads only $E\cup W_D$ and its own outputs). The result is $f_D$ with $\mathrm{graph}(f_D)\subseteq\bigcap_DS_j$. Given $(x,e)\in K$ and $w_D\in A_Y$, the trace $(x,e,w_D,f_D(e,w_D))$ lies in $A_P$ by (Ind), in every $U$-obligation (these read only $X\cup E=\ports(U)$), and in every $D$-obligation. So it lies in $G_P$ by (C1). (⇐) $\Pi_D(\cdot)$ is the largest $D$-obligation keeping (C1) (fixed-point sweep, foundations §9). It contains $\mathrm{graph}(f_D)$ by (RD), so it is realizable. ∎

(RD) is the exact meaning of "$E$ carries what $D$ needs": $D$ must commit to an output that is correct for every private value $U$ might have had, given what $U$ put on the edge. The vacuous fixed point (vacuity, foundations §7) is the case $F(e)=$ the whole prior, which happens whenever $U$'s obligation says nothing about $e$.

### 2.2 Linear queries: the budget condition

**Proposition 2.** Let $G_P$ be conjunctive and $F$ compact. At a fixed $(e,w_D)$, (RD) holds for some $o$ iff for every extreme ray $\lambda$ of $C:=\{\lambda\ge0:\lambda^\top N_O=0\}$
$$\underbrace{\sigma_F(\lambda^\top N_X)}_{\text{net upstream term}}+\underbrace{\Delta_\lambda(F)}_{\text{information deficit}}\ \le\ \beta_\lambda(e,w_D):=\lambda^\top(g-N_Ee-N_Ww_D),$$
where $\sigma_F(a)=\max_{x\in F}a^\top x$ and $\Delta_\lambda(F):=\sum_k\lambda_k\sigma_F(N_{X,k})-\sigma_F\big(\sum_k\lambda_kN_{X,k}\big)\ge0$.

*Proof.* $o$ is chosen before $x$ and each row is universally quantified on its own, so the robust counterpart is exact row by row: $N_Oo\le g-N_Ee-N_Ww_D-h(F)$ with $h_k=\sigma_F(N_{X,k})$. Farkas over the rays of $C$ gives the condition. Splitting $\lambda^\top h$ into the two terms is an identity, and $\Delta\ge0$ by sublinearity of $\sigma_F$. ∎

Reading. The rays $\lambda$ are the combinations of query rows in which $D$'s outputs cancel. The first term involves only $U$'s side, so it is an upstream obligation that needs no communication. $\Delta_\lambda(F)$ vanishes iff the functionals $N_{X,k}$ with $k\in\mathrm{supp}\lambda$ have a common maximiser on $F$. It measures how spread the fibre is in the directions that $D$ must handle at once. **For a band**, $\lambda=e_{k^+}+e_{k^-}$, the net term is $0$, $\beta=2\varepsilon$ and $\Delta_\lambda(F)=\mathrm{width}_\ell(F)$:
$$\boxed{\ \mathrm{width}_\ell\,F(e)\le2\varepsilon\quad\text{for every reachable }e\ }\tag{B}$$
This is the precise tolerance-budget form of "$m$ must relay $r$". With no information, $F=$ prior and the width is $W_\ell$. The **zero-information test** "$W_\ell>2\varepsilon$" therefore decides whether the band forces information across the cut. It is the general form of $\Pi_D(\lvert d-r\rvert\le0.5)=\emptyset$ (script [a]).

### 2.3 Rank theorem (conjunctive upstream)

Bands $\ell_1,\dots,\ell_n$ that read only $W_U$ are **jointly informative** if there are $\alpha_i<\beta_i$ with $\beta_i-\alpha_i>2\varepsilon_i$ such that for every sign vector $s\in\{\pm1\}^n$ some $w_s\in A_X$ has $\ell_i(w_s)\le\alpha_i$ when $s_i=-1$ and $\ell_i(w_s)\ge\beta_i$ when $s_i=+1$. This holds whenever $L(A_X)$ contains an axis box with sides $>2\varepsilon_i$, in particular for box priors with $W_i>2\varepsilon_i$.

**Theorem 3.** Assume (Ind). Let every $U$-obligation be a closed polytope, so that $K$ is a compact convex polytope. $D$'s obligations may be arbitrary receptive causal sets. If $G_P$ has $n$ jointly informative bands across the cut and the delegation is valid and receptive, then $n\le k$.

*Proof.* Put $M_i^-:=\pi_E(K\cap\{\ell_i\le\alpha_i\})$ and $M_i^+:=\pi_E(K\cap\{\ell_i\ge\beta_i\})$. Both are compact and convex. They are disjoint: an $e$ in both would have a fibre containing $x,x'$ with $\ell_i(x')-\ell_i(x)\ge\beta_i-\alpha_i>2\varepsilon_i$, which contradicts (B). (Fix any $w_D$ and $o=f_D(e,w_D)$; the band's non-$x$ part is then the same for $x$ and $x'$.) So there are affine $h_i:\mathbb R^k\to\mathbb R$ with $h_i<0$ on $M_i^-$ and $h_i>0$ on $M_i^+$. For each $s$, $U$-receptiveness gives $(x_s,e_s)\in K$ extending $w_s$. Then $e_s\in M_i^{s_i}$ for all $i$, so $\mathrm{sign}\,h_i(e_s)=s_i$. The $n$ hyperplanes $\{h_i=0\}$ in $\mathbb R^k$ therefore realise all $2^n$ strict sign vectors. Each sign vector occupies at most one cell, because cells are convex, so the arrangement has $\ge2^n$ cells. An arrangement of $n$ affine hyperplanes in $\mathbb R^k$ has at most $\Phi(n,k)=\sum_{j=0}^k\binom nj$ cells (Buck 1943; Zaslavsky 1975), and $\Phi(n,k)<2^n$ iff $n>k$. ∎

Remarks. (i) For $k=0$ convexity is not needed: $F(e)\supseteq$ prior, so no delegation of any kind exists. (ii) The theorem is about the *upstream* obligations only. $D$ may use any PolySTL or any set at all. (iii) Script [b]: every exact linear 1-D encoding of $(r_1,r_2)$ leaves Display non-receptive (qe2, nine angles; a QF_NRA witness proof covers all $(\alpha,\beta)$). In 500 random convex receptive relations, the $k=1$ form of the argument ("some fibre meets two opposite sides of the box") held every time.

### 2.4 Exact queries: any PolySTL

**Theorem 4.** Assume (Ind). Let the $n$ bands have $\varepsilon_i=0$ (equalities), let $L$ read only $W_U$, and let $L(A_X)$ have nonempty interior in $\mathbb R^n$. If the $U$-obligations are finite unions of polytopes (any PolySTL) and $n>k$, no valid receptive delegation exists.

*Proof.* $K=\bigcup_jK_j$ is a finite union of polytopes. By (B) with $\varepsilon=0$, $L$ is constant on every fibre of $K$, hence on every fibre of each $K_j$. So $\Gamma_j=\{(e,Lx):(x,e)\in K_j\}$ is a convex set that is the graph of a map $\varphi_j$ on $\pi_E(K_j)$. A convex graph forces $\varphi_j$ to be affine: the segment between two graph points stays in the graph. So $L(\pi_XK_j)=\varphi_j(\pi_EK_j)$ lies in an affine set of dimension $\le k<n$ and is Lebesgue-null. Receptiveness gives $L(A_X)\subseteq\bigcup_jL(\pi_XK_j)$, a null set, which contradicts the nonempty interior. ∎

The finiteness is essential. With arbitrary sets, a Borel bijection $[-1,1]^2\to[-2,2]$ (digit interleaving) delegates exactly. So T4 is an obstruction of the PolySTL obligation language, not of information.

### 2.5 Capacity theorem: type bounds and tolerance, any obligations

In exact arithmetic a linear encoding can always be rescaled into any type box, so a type bound alone never obstructs. It starts to obstruct when the upstream obligation must leave **slack**. Call $K$ **$a$-robust** if for every $w\in A_X$ the set $\{e:\exists x\supseteq w,(x,e)\in K\}$ contains a box $\prod_j[c_j-a_j,c_j+a_j]$. This is the formal version of "the obligation is not an equality".

**Theorem 5.** Assume (Ind). Let the bands $\ell_i$ read only $W_U$ and let $L(A_X)$ contain a box with sides $W_i$. If an $a$-robust valid receptive delegation exists, then
$$\prod_{i=1}^n\Big\lceil\frac{W_i}{2\varepsilon_i}\Big\rceil\ \le\ \prod_{j=1}^k\frac{Y_j}{a_j}.$$
*Proof.* $\lceil W/2\varepsilon\rceil$ is the largest number of points in an interval of length $W$ that are pairwise more than $2\varepsilon$ apart. Take the product grid of such points in $L$-space. Pick $w_g\in A_X$ with $Lw_g=g$ and a slack box $B_g$ for each grid point $g$. If $e\in B_g\cap B_{g'}$, then $F(e)$ contains two points more than $2\varepsilon_i$ apart in some $\ell_i$, which contradicts (B). So the boxes are disjoint. They lie in the type box $\prod_j[-Y_j,Y_j]$, and comparing volumes gives the inequality. ∎

This is the counting form of the information requirement and holds for **all** obligations, disjunctive ones included. If the tolerance is proportional ($a_j=\kappa\varepsilon$, $\varepsilon\to0$), the left side grows like $\varepsilon^{-n}$ and the right like $\varepsilon^{-k}$. So **the rank condition $n\le k$ is the fine-tolerance limit of T5 for every obligation class.** At coarse tolerance only the count matters, and disjunctive codes can beat the rank condition.

### 2.6 Sharpness: the rank condition is not necessary for disjunctive delegations

**Proposition 6.** Take $r\in[-1,1]^2$, $\lvert m\rvert\le2$ and $G_P=\{\lvert d_1-r_1\rvert\le.5,\ \lvert d_2-r_2\rvert\le.5\}$, so $n=2>k=1$. The quantizer
$$S_R=\textstyle\bigvee_{j=1}^4\big(r\in C_j\wedge\lvert m-\mu_j\rvert\le0.4\big),\qquad C_j=\text{quadrants},\ \mu=(-1.5,-.5,.5,1.5),$$
with $S_D=\Pi_D(A_P\wedge S_R\to G_P)$ ("$d=$ centre of $C_j$ on interval $j$; anything in the gaps") is valid, receptive and causal. Script [b] verifies this with qe2. T5 gives $4\le2/a$, i.e. $a\le0.5$, so the quantizer is within $0.1$ of capacity. The same construction works for every $\varepsilon>0$ with $\lceil1/\varepsilon\rceil^2$ pieces. Only $\varepsilon=0$ is impossible (T4).

So the honest statement of the "dimension counting" obstruction has three tiers: conjunctive (T3, hard rank), exact (T4, hard rank), robust (T5, counting). The 2-D/1-D relay is **not** non-delegable for PolySTL at $\varepsilon=0.5$. It is non-delegable by conjunctive contracts.

### 2.7 Sufficiency in the conjunctive case (one cut)

The **ideal relay** of the cut is the same problem with $D$ also shown $\ell=Lx$ exactly. It is *solvable with margin* if there is $a^*>0$ such that $\Pi_D(A_P\wedge S_U^{\rm own}\wedge\chi_a\to G_P)$ is receptive for $a<a^*$, where $\chi_a$ is defined below.

**Theorem 7.** Assume (Ind), (Pure) and $n_L=\mathrm{rank}\,L\le k$. Let $T:\mathbb R^{n_L}\to\mathbb R^k$ be injective and scaled so that $TL(A_X)$ fits $E$'s type box. Let $S_U^{\rm own}$ be any realizable $U$-obligation for the rows without $D$-outputs; under (Pure) these rows do not mention $E$. Then:
(i) with $\chi_0:=\{e=TLx\}$, the pair $(S_U^{\rm own}\wedge\chi_0,\ \Pi_D(A_P\wedge S_U^{\rm own}\wedge\chi_0\to G_P))$ is valid and realizable iff the ideal relay is solvable;
(ii) if it is solvable with margin $a^*$, the same holds for $\chi_a:=\{\lvert e-TLx\rvert_\infty\le a\}$ for every $a<a^*$, and $U$ is $a$-robust;
(iii) if $L$ spans the $X$-dependence of every row with a $D$-output (true by construction), the ideal relay is solvable iff the centralized problem is ($\forall$ environment $\exists$ outputs) on the $D$-rows given $U$'s own rows.

*Proof.* (i) $T$ is injective, so $Lx$ is constant on $F(e)$. Every row with a $D$-output depends on $x$ only through $Lx$. So (RD) at $e$ is the ideal-relay condition at $\ell=T^{-1}e$; apply L1. (ii) The fibres shrink monotonically as $a\downarrow0$, so receptiveness of $\Pi_D$ is monotone in $a$. $U$'s output $e=TLx$ lies inside the slack box. (iii) $D$'s feasible set at $(\ell,w_D)$ is the same for every $x$ with $Lx=\ell$, so any centralized solution induces a $D$-strategy on $(\ell,w_D)$. ∎

Single-cut sufficiency therefore holds: **rank fits + ideal relay has margin ⇒ delegable, by a canonical seed.** For several cuts at once see §4: multicast is fine (network coding), general demands are open.

---

## 3. Canonical cut = canonical encoding

**Construction** (input: graph and query only).
1. Remove query rows implied by types (LP). For each cut that separates a writer of a $G_P$-output from the $U$-private variables of a coupling row, compute $L$ (SVD), $n_L$, the bands and their widths. Apply the zero-information test.
2. Check the rank and causal capacity (Cor. 12). If $n_L>k$ for some cut, go to §6 and report.
3. **Encoding $T$.** Use the identity when $n_L=k$ and $L(A_X)$ fits $E$'s type (readable: "$m$ relays $r$"). Otherwise use the type-scaled $T=\mathrm{diag}(Y_{e_j}/\rho_j)$, $\rho_j=\max_{A_X}\lvert(Lx)_j\rvert$, on $n_L$ edge coordinates and zero on the other $k-n_L$; those edge variables get no obligation. With several edges and paths, choose the routing by §4.
4. **Tolerance.** Compute $a^*$ (bisection on qe2 receptiveness; for bands it is closed form). The canonical choice is the **max-min split** in each component's own output units, $a=a^*/2$ on the relay.
5. Cut $\chi_a=\{\lvert e-TLx\rvert\le a\}$. Seed: $S_U=A_P\to\chi_a$, $S_D=\Pi_D(A_P\wedge\chi_a\to G_P)$ (qe2). Run one Gauss–Seidel sweep (fixed-point sweep, foundations §9) to reach a maximal delegation. Hand out ghost-free contracts (foundations §6).

Every object is a function of (graph, query). No search and no model are needed. Hand-picked seeds are instances: the copy-strategy seed is $\chi_0$, and the band seed $0.2/0.3$ of the relay example (foundations §11) is $\chi_{0.2}$ with $D$ shrunk to a band.

**Relay, verified (script [a]).** $L=[1]$, $n=k=1$, identity fits.
- $\Pi_D(A_P\wedge\chi_{0.2}\to G_P)$ equals the relay cut set (foundations §11) exactly.
- $a^*=0.5$ (receptive at $0.5$, not at $0.5001$).
- Canonical $a=0.25$: both obligations are receptive, (C1) holds, and $F_R(S_D)=\chi_{0.25}$. **The canonical seed is already a fixed point of the sweep.**

**Proposition 9 (optimality, $n=k=1$).** For a box prior $\ell\in[-\rho,\rho]$ and a decoder with zero own tolerance, the type-scaled encoding $m=(Y/\rho)\ell$ admits slack $a\le\varepsilon Y/\rho$. T5 gives $a\le Y/\lceil\rho/\varepsilon\rceil$. These are equal when $\rho/\varepsilon\in\mathbb N$, so the type-scaled linear code is optimal among **all** (also disjunctive) robust encodings. On the relay: $a^*=1.0$ in $m$-units (receptive at $1$, not at $1.001$), which equals the bound. A 1-bit quantizer also reaches $a=1$, and its Display is then exact ($d=\pm.5$). For $n<k$, linear codes waste capacity: T5 allows $a\sim YN^{-1/k}$ and a linear code gets $YN^{-1/n}$. A serpentine or quantized code can do better. This is a remark, not used.

**Where the construction works.** Conjunctive coupling (bands or polytope rows), (Ind), (Pure), $n_L\le k$ on every cut with causal capacity, and single-sink or multicast demands (§4).
**Where it does not.**
(a) $n>k$: no conjunctive seed exists (T3). Disjunctive quantizers may exist if $\varepsilon>0$ (P6), but finding them is search.
(b) $\varepsilon=0$ and $n>k$: nothing in PolySTL works (T4).
(c) No causal capacity (Cor. 12), e.g. a delay-1 Radio with $\lvert d(t)-r(t)\rvert\le.5$.
(d) Edges that the query pins (not Pure): the code must live in the free directions of $E$, which reduces $k$.
(e) Correlated environments: $D$ has side information, and T3/T5 hold with that side channel added to $E$. The construction then over-encodes.
(f) Queries with $\vee$ that need a flag (§7).
(g) One-sided coupling rows: $L$ may exceed the informative directions, $n_{\rm band}\le n_{\rm needed}\le n_L$. The construction may then over-carry, and fail on capacity although a smaller code would do.

Free interface coefficients. A Farkas decomposition into one row per component leaves free, for each row and each variable the row does not mention, the coefficient passed through it, and the split of the bound. The canonical encoding fixes the first: row $k$ passes $N_{X,k}x=c_k^\top TLx$ through $E$ with $c_k^\top=N_{X,k}(TL)^+$. The bound split stays, and it is an LP.

---

## 4. Multi-path, fan-in, fan-out: a flow, then network coding

**Coefficient flow (scalar functional).** With the coefficients fixed by §3, the affine Farkas lemma makes each query row a sum of one row per involved component (Theorem 1 of `theory/conjunctive-decomposition.md`), and the coefficients on non-query variables cancel. In graph form, the variables are nodes and each component is a hyperarc from $\mathrm{in}(i)$ to $\mathrm{out}(i)$. Component $i$'s row puts a coefficient $f$ on its output and $g_{i,u}$ on its inputs. **Conservation:** at every internal variable, the writer's coefficient equals minus the sum of the readers'. At an environment variable, the readers' coefficients sum to its query coefficient (the source split). At a query output, the writer's coefficient is fixed by the query. A band row $\lvert f\,o_i+\sum_ug_{i,u}u\rvert\le b_i$ with box-typed inputs (reachable ranges $R_u$) is receptive iff
$$\textstyle\sum_u\lvert g_{i,u}\rvert R_u\le\lvert f\rvert Y_{o_i}+b_i, \tag{cap}$$
which is linear for fixed signs. For internal edges $f$ is a free gain, so (cap) never binds; only the tolerance units change. **For query outputs $f$ is fixed, so (cap) is a real capacity on how much coefficient a sink can absorb.** The tolerance split (for $\sum_ib_i\le$ the row's budget) is an LP.

**Canonical rule.** Maximise the minimum tolerance in each component's own output units. Break ties by the fewest involved components (L1 surrogate $\min\sum\lvert g\rvert$). Spreading appears only when (cap) forces it.
- *Fan-in* (script [c1]): two radios read $r$. Every routing $c=(c_1,1-c_1)$ gives the same max-min tolerance $0.25$. **Worst-case redundancy buys nothing**; it only allows asymmetric splits ($a_1=.4,a_2=.1$ is valid with $c=(.5,.5)$). Canonical: a single path, with the other radio a bystander. Both delegations are qe2-verified.
- *Fan-out with a type-forced split* (script [c2]): $m$ is read by $D_1,D_2$ with $\lvert d_i\rvert\le1$ and $G_P=\lvert d_1+d_2-2r\rvert\le.5$. A single path is not receptive ($D_1$ cannot absorb coefficient 2). The split $(1.5,.5)$ and $(1.2,.8)$ violate (cap). $(1,1)$ works. The split is forced by type capacity.

**Vector functionals: network coding.** When $n_L>1$, each scalar of $Lx$ is a commodity and each edge variable sample has rank capacity 1. For a single sink, max-flow/min-cut (Menger) gives a routing whenever every cut has $n\le k$. For several sinks needing the same functional (multicast), routing can fail although every cut is fine, and **linear network coding over $\mathbb R$ achieves the min-cut** (Ahlswede–Cai–Li–Yeung 2000; Li–Yeung–Cai 2003; Koetter–Médard 2003; generic coefficients over an infinite field suffice). Script [c3] uses the butterfly: sources $r_1,r_2$, a bottleneck $c$ of dimension 1, and sinks $D_1$ (sees $a_1,c$) and $D_2$ (sees $a_2,c$), each needing both. Every sink's cut has $k=2=n$.
- **Routing** ($c\approx b_1$): $D_1$'s largest obligation for its $r_2$-row is not receptive (qe2).
- **Coding** ($c\approx b_1+b_2$, $D_1$ decodes $r_2\approx c-a_1$) with bands $0.08/0.1/0.1$: (C1), (C2) and receptiveness all hold.

The canonical encoding on general DAGs is therefore a generic linear network code. The tolerance accumulates through the decoding coefficients, here $\gamma+3\alpha+\delta$, and the budget LP is unchanged.

**Corollary 10 (multicast).** Assume (Ind) and (Pure), conjunctive bands, and that every sink needs the same functional. A conjunctive delegation exists iff every cut separating the sources from a sink has $n\le k$ (causally), *and* the ideal problem has margin. Necessity is T3 per cut. Sufficiency is a generic real linear code plus T7 per sink, with the margin taken at the worst decoding gain. *Status:* sufficiency is assembled from cited results and T7. The tolerance bookkeeping is shown on the butterfly, not proved in general.

**Conjecture 10'.** For general (non-multicast) demands the cut condition is necessary (T3) but not sufficient. It is known that linear codes are insufficient over finite fields (Dougherty–Freiling–Zeger 2005). Whether conjunctive PolySTL delegability equals "an $\mathbb R$-linear code with margins exists" is open.

---

## 5. Craig interpolation: what it is here, and what it adds

Z3 5.1 has **no interpolation API**; it was removed after 4.8 (checked in the script). Interpolants are computed from Farkas multipliers by LP and verified with Z3.

**The brief's premise needs a correction.** $A_P\wedge\chi\wedge\neg G_P$ is **SAT** even for the ideal $\chi_0=\{m=r\}$, because nothing constrains $d$ (checked). Unsatisfiability needs $D$'s obligation, which is the unknown.

**Proposition 13 (interpolants = cuts).** Let $A:=A_P\wedge\bigwedge_{j\in U}S_j$ and $B:=\bigwedge_{j\in D}S_j\wedge\neg G_P$. Then (C1) iff $A\wedge B$ is UNSAT. The shared vocabulary is $E\cup(\mathrm{vars}(G_P)\cap X)$, i.e. the edges plus the ghosts. A formula $I$ over it is a Craig interpolant iff $\Gamma\models\{A_P\}U\{I\}$ and $\Gamma\models\{I\}D\{G_P\}$, i.e. iff $I$ is a valid (Seq) cut. The strongest interpolant is $\pi_{\rm shared}(A)$, the existential projection (foundations §6). The weakest is $\Pi_{\rm shared}(\neg B)$.
*Proof.* This unfolds the definitions: $A\models I$ is the first triple, and $I\wedge B$ UNSAT is $I\wedge\bigwedge_DS_j\to G_P$, the second. The strongest and weakest interpolants are standard (shadow and dual shadow). ∎

Verified on the relay with Radio $\lvert m-r\rvert\le.2$ and Display $\lvert d-m\rvert\le.3$:
- The two Farkas interpolants (one per disjunct of $\neg G_P$) conjoin to **$\lvert m-r\rvert\le0.2$, the canonical encoding itself**.
- The strongest interpolant is $\lvert r\rvert\le1\wedge\lvert m-r\rvert\le.2$.
- The weakest is $\lvert m-r\rvert\le0.5-b$.
- The interpolant interval is exactly the tolerance split.

On a chain Radio→Repeater→Display, the sequence interpolants are $I_1=\lvert m_1-r\rvert\le a_1$ and $I_2=\lvert m_2-r\rvert\le a_1+a_2$. Their consistency condition $I_1\wedge S_{\rm Rep}\models I_2$ is the Hoare triple $\{I_1\}\mathrm{Rep}\{I_2\}$, i.e. the (Seq) premise. For tree-shaped architectures this is McMillan-style tree interpolation. When a variable fans out to two readers one needs DAG interpolants (Albarghouthi–Gurfinkel–Chechik, VMCAI 2012). Each per-component obligation "in-edge interpolants → out-edge interpolants" carries ghosts, and its ghost-free handout is $\Pi_i$ of it (foundations §6).

**Verdict.** Interpolation is the *certificate side* of the same object. Given a delegation, it extracts per-edge cuts from a (C1) refutation, in closed form from Farkas multipliers. This is a proof-producing implementation of (Seq) and of the Farkas row decomposition. It **does not choose**. With $D$ unknown there is nothing to interpolate. With $D$ set to the canonical decoder, it returns $\chi_0$ or $\chi_a$, which §3 already computed. The zero-tolerance interpolants are equalities, realizable but with no slack, and the slack split is the LP of §3–4. Item 3 adds nothing over item 2 for *construction*. Its value is certification and proof logging.

---

## 6. Non-existence

**Theorem 11 (obstruction report).** Assume (Ind). Let $(U,D)$ be a cut with edge dimension $k$ (causal, Cor. 12), carrying $n$ jointly informative bands $\ell_1..\ell_n$ that read $U$'s environment, with prior widths $W_i>2\varepsilon_i$.
- (a) If $k=0$: **no** delegation exists, of any kind.
- (b) If $n>k$: no delegation with **conjunctive upstream obligations** exists, whatever the downstream obligations.
- (c) If $n>k$ and every $\varepsilon_i=0$: no **PolySTL** delegation exists.
- (d) For every $n,k$: no **$a$-robust** delegation exists unless $\prod_i\lceil W_i/2\varepsilon_i\rceil\le\prod_jY_j/a_j$.

In each case the honest output is the tuple (cut $U\mid D$, edge set $E$, functionals $\ell_i$, $n$, $k$, budgets $\varepsilon_i$, required slack). Example: "the query needs the 2 functionals $r_1,r_2$ across edge $\{m\}$, which carries 1. Not delegable by conjunctive contracts. A disjunctive code with 4 levels exists if Radio may keep slack $\le0.5$."
*Proof.* (a) Remark (i) of T3. (b) T3. (c) T4. (d) T5. ∎

**Sharpness.** (b) cannot be extended to disjunctive obligations (P6). (d) is tight up to boundary effects (P6: 4 levels, $a=0.4$ works and $a\le0.5$ is the bound; P9). Without (Ind) all four statements fail as stated, since a correlated $W_D$ is a side channel. They hold with $E$ replaced by $E\cup W_D$ when the correlation is arbitrary.

**Corollary 12 (causal capacity).** In the time-expanded graph, suppose a band needs $\ell(r(u..u'))$ by deadline $t$. Only edge samples $m(\tau)$ with $u'+d_U\le\tau\le t-d_D$ can carry it, because earlier samples are independent of $r(u..u')$ under (Ind) and later ones are unreadable. Applying T3/T11 to the restricted cut gives Hall-type conditions: for every set of needed scalars, the usable edge samples must be at least as many. For interval demands this is a bipartite matching between needed scalars and edge samples. Script [e] ($H=2$): delay 0 with lag 0 or 1 is fine. **Delay-1 Radio with lag 0 has capacity 0 at every deadline**, which is case (a) of Theorem 11 ($k=0$). Delay 1 with lag 1 is fine, and the canonical $m(t)\approx r(t-1)$, $d(t)\approx m(t)$ is Z3-verified. *Status:* the interval reduction is proved as stated. The general Hall condition is a direct consequence only for interval-structured demands.

---

## 7. Limits: when the needed "encoding" is not linear

With $\vee$ in $G_P$, what $D$ needs may be a *cell label* instead of a functional. An example is $(r\ge0\to d\ge.5)\wedge(r<0\to d\le-.5)$: $D$ needs one bit, $[r\ge0]$. The exact linear code $m=r$ still works, with a thresholding (disjunctive) Display. But any positive tolerance on $m$ makes the fibre at $m\approx0$ straddle the boundary and kills receptiveness, so the only robust codes are flags with margin, $m\ge1$ if $r\ge0$ and $m\le-1$ otherwise. These are disjunctive upstream obligations. The row-space machinery of §2–3 does not see them. The correct "functional" is the map from $U$'s private values to the cells of the query's predicate arrangement. In the free-trajectory semantics this alphabet is finite, so the capacity question becomes one of distinguishable levels with margins, as in T5, not of rank. The canonical encoding for such queries, and its interaction with $\lozenge$ (the decider choice in the temporal slice), is left open; no solution is attempted here.

---

## 8. Experimental verdicts (`scripts/interface_cuts.py`, about 30 s)

| Check | Verdict |
|---|---|
| [a] needed functional of the relay | $L=[1]$, $n=k=1$; zero-information test: $\Pi_D(A_P\to G_P)=\emptyset$ ✔ |
| [a] $\Pi_D(\chi_{0.2}\wedge A_P\to G_P)=$ relay cut set (foundations §11) | equal ✔ (qe2, cross-checked) |
| [a] threshold $a^*$, identity code | $0.5$ (receptive at $0.5$, not at $0.5001$) ✔ |
| [a] canonical $a=0.25$: receptive both, (C1), band inside, sweep fixed point | ✔ ✔ ✔ ✔ |
| [a] type-scaled $m\approx2r$: $a^*=1.0$ equals the capacity bound $Y/\lceil W/2\varepsilon\rceil$ | ✔ (and the 1-bit quantizer also reaches 1) |
| [b] 2-D $r$, 1-D $m$: exact linear codes at 9 angles | Display not receptive in all 9 ✔ |
| [b] all affine band codes, direct $\exists\forall$ NRA query (qsat) | **unknown (timeout 20 s): failed**; replaced by a QF_NRA witness proof ✔ |
| [b] 500 random convex receptive relations | 0 counterexamples to the opposite-sides lemma ✔ |
| [b] 4-piece quantizer delegation | valid, receptive, $\Pi_D$ = hand formula ✔: **delegable by disjunctive contracts** |
| [c1] fan-in routings | all max-min $0.25$; single path and spread both verified ✔ |
| [c2] fan-out $\lvert d_i\rvert\le1$ | single path ✘, $(1.5,.5)$ ✘, $(1.2,.8)$ ✘, $(1,1)$ ✔ (type-forced split) |
| [c3] butterfly | routing ✘ (qe2), linear code ✔ (C1), (C2), receptive |
| [d] interpolation API in Z3 5.1 | absent; Farkas by LP |
| [d] relay: Farkas interpolant, strongest, weakest | $\lvert m-r\rvert\le.2$ (= canonical encoding), $\pi(A)$, $\lvert m-r\rvert\le.5-b$ ✔ |
| [d] 3-chain sequence interpolants | $\lvert m_1-r\rvert\le.1$, $\lvert m_2-r\rvert\le.25$; Hoare consistency ✔ |
| [e] causal capacity, $H=2$ | delay 1/lag 0: capacity 0 (not delegable); other three fine; canonical delay-1 code verified ✔ |

---

## 9. Summary of results

1. **The seed is computed, not searched.** The fixed-point sweep (foundations §9) needs a valid seed. Here the seed is $(\chi_a,\Pi_D(\chi_a\to G_P))$ with $L,T,a$ computed from (graph, query). The hand-picked copy-strategy and band seeds are $\chi_0$ and $\chi_{0.2}$. On the relay the canonical seed is already a fixed point.
2. **Exact information requirement of a cut** (Lemma 1) and its linear form (Prop. 2: net term plus information deficit). It says not only *that* $r$ must cross but *how much*, $\mathrm{width}_\ell F(e)\le2\varepsilon$.
3. **Three non-existence theorems** (T3 conjunctive rank, T4 exact PolySTL, T5 counting for any obligations), with a sharp counterexample (P6) showing the rank condition is **not** an obstruction for disjunctive PolySTL.
4. **Optimality of the type-scaled code** for $n=k=1$ (P9): type bounds matter only through required slack.
5. **The free interface coefficients** of the Farkas row decomposition (§3) are fixed by the encoding. Multi-path choices become a coefficient-flow LP with type capacity at sinks. The vector case is linear network coding (butterfly).
6. **Interpolation, honestly:** it equals the (Seq) cuts, with the existential projection as the strongest. It is a certificate tool and does not choose.
7. **Causal capacity** (Cor. 12) is a matching condition on the time-expanded graph; the delay-1 relay of script [e] is its smallest instance.

## 10. Open

- A canonical construction when $n>k$ but $\varepsilon>0$ (quantizers): the minimum number of pieces, and whether a lattice or serpentine code is canonical.
- Conjecture 10' (general demands).
- Removing (Pure): codes in the free directions of a query-pinned edge.
- Choosing $L$ for one-sided coupling rows (the $n_{\rm band}$ vs $n_L$ gap): use Prop. 2's deficit to keep only directions with $\Delta>\beta$.
- Unbounded horizon: the time-invariant code $m(t)\approx Lr(t-\cdot)$ with (Circ).

**References cited, not re-proved:** R. C. Buck, *Partition of space*, Amer. Math. Monthly 1943; T. Zaslavsky, Mem. AMS 1975 (hyperplane arrangement cell counts). Ahlswede, Cai, Li, Yeung, *Network information flow*, IEEE T-IT 2000; Li, Yeung, Cai, *Linear network coding*, IEEE T-IT 2003; Koetter, Médard, *An algebraic approach to network coding*, IEEE/ACM ToN 2003; Dougherty, Freiling, Zeger, *Insufficiency of linear coding in network information flow*, IEEE T-IT 2005. K. McMillan, *An interpolating theorem prover*, TCS 2005; Albarghouthi, Gurfinkel, Chechik, *Whale: an interpolation-based algorithm for inter-procedural verification*, VMCAI 2012 (DAG interpolants).
