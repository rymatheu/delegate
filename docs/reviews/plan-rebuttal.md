# Rebuttal to docs/reviews/plan-A.md (review of docs/plan.tex)

19 October 2026. `cd docs && latexmk -pdf plan.tex` was rebuilt from a clean state. The log has no warnings and no
overfull or underfull boxes, and the PDF has **5 pages**. Fonts are still 10pt and margins 0.75in. To make room for
the fixes I cut the following:
- the discrepancy paragraph (B5);
- the "Recommended shape" and "honest alternative" sentences (Strands section);
- the Strands repository footnote (three footnotes remain);
- two citations not on the required list (Incer et al. on the quotient; Xu et al. on cross-component
  specifications);
- some wording in the Risks list and the work packages.

## Blocking

- **B1** fixed: before the table, the notation paragraph now defines in plain words a causal strategy, receptive (R),
  causal (K) ((K) implies (R)) and acceptable delegation (each $C_i$ over $\ports(i)$; (V1), (V2), (R), (K) hold).
  It also defines the contract $C_i=(A_i,S_i)$ of $i$.
- **B2** fixed: the proof of Lemma 1(b) now uses the review's sentence. The witness of $y(t)$ mentions inputs at
  times $\le t$, outputs of $i$ at times $<t$ (in regions only), and outputs of $i$ at time $t$ earlier in the block
  (in regions and values). In regions these are substituted as in step 6. In values the pair $(\pi,c)$ is replaced by
  the pairs $(\pi\wedge\pi',c[z(t):=c'])$. Values stay affine at time $t$, and the substitution ends.
- **B3** fixed: the cell claim now covers only the (V1) obligation and the (V2) obligation of some $j\ne i$. For (V2)
  the cell stays forbidden only while $A_j$ is unchanged. For the (V2) obligation of $i$ itself, the projected cell
  lies inside $A_{Q_i}$ and violates $A_i$, which shows that $A_i$ is too strong. Routing rule (1) now asks "the
  writers other than $j$" and then $j$, to weaken $A_j$.
- **B4** fixed: the false sentence is gone.
  - The loop ends in three ways: by the budget; when every component that routing may ask has declined on the
    current failure (new pseudocode lines 13–14, with a `declined` set that is reset when $F$ changes); or, in
    weakening, after a full cycle with no positive example.
  - None of these says anything about existence.
  - Only the WP3 enumerator, which checks every tuple of a finite candidate set, can say "none in this set". WP1 and
    WP3 are worded to match.
- **B5** fixed: the paragraph is replaced by one sentence: "The README's run time was corrected today: the suite
  takes about 100 s, almost all of it the governor sweep." Note: README.md line 27 currently says "about 90 s"; the
  review measured 98.7 s. The sentence was written as instructed. If the README keeps "90 s", one of the two should
  be changed so they agree.

## Major

- **M1** fixed: "not guaranteed to be maximal".
- **M2** fixed with the proposed wording. Maximality is lost because deciding it is $\exists\forall$, which only the
  sweep answers. Selection is not new.
- **M3** fixed:
  - The notation now defines $\hid W$ and gives $\rho_W$ inline, with one display for $\otimes$ and $/$ and a plain
    gloss for each.
  - It defines $S_P$.
  - The proof of Lemma 2(a) now composes the others to $(A',S')$, writes out the quotient, and states the projection
    step.
- **M4** fixed: the (V2)-first reason is replaced by the review's wording ("it is a (V2) counterexample, and the right
  fault to report ...; once (V2) holds, every (V1) counterexample satisfies all $A_j$"). The dead clause "or a (V1)
  trace violating some $A_j$" is deleted from rule (1).
- **M5** fixed: rule (3) returns the failing input history only when a rule list was given. When (K) is checked by
  the sentence, the verifier returns no history and $i$ is told only "(K) failed".
- **M6** fixed:
  - "Phi cheap" is a fixed size, $|V|(H+1)\le 12$ (the governor's size at $H=2$), stated in the text and in line 2.
    This is a variable count, not a time limit, as instructed.
  - `C := none` is set on line 7, so line 12 records nothing in round 1.
  - DECLINE is never stored as a contract: line 16 adds $i$ to `declined`, line 17 installs only real proposals.
  - The feedback is "projected cell or (K) feedback" plus `forbidden_i`; forbidden cells and (K) histories are kept
    apart.
  - Line 23 and the weakening paragraph now check (C1).
  - Line 7 is stated to re-check the seed, which is acceptable by `complete.tex`.
  - Partly rejected: the remark that the seed's rule list sets edge values outside the forwarding to 0. It was left
    out for space. It is in the (R), (K) part of the soundness proof in `complete.tex`, and line 7 checks the seed
    either way.
- **M7** fixed: proposer $i$ keeps its cells in `forbidden_i`, which is emptied whenever another set shrinks.
- **M8** fixed as the coordinator directed, per component: "the proposer of component $i$ returns the enumerator's
  next candidate every $k$-th time it is asked".
  - The review is right that this alone does not obviously give a fair enumeration of tuples under routing. The plan
    therefore says that this property is part of WP1, and WP1 now lists "completeness when interleaved".
  - The review's alternative (every $k$-th round verifies the next tuple on its own) is not adopted, to keep a single
    mechanism.
- **M9** fixed: the trust base now includes the verifier's Python code, which parses proposals, checks (C1) and
  rule-list syntax, and builds $S_i$, $S_i[f_i]$ and the (V1), (V2) formulas.
- **M10** fixed: Lemma 1 is proved in the plan (with B2). WP1 now says "Re-check Lemma 1 (proved here)".
- **M11** fixed: "440 s alone" is dropped. The table row now says "sweep: most of the 99 s run of `delegate.py`". The
  71 s figure is not kept, because it could not be labelled with the tactic order it was measured under.
- **M12** fixed:
  - Section 1 now says "the existence sentences $\Phi$ and $\Phi^\circ$ of complete.tex (all defined in Section 2)".
  - The notation paragraph defines topological ordering, nested ordering and forwarding (with the carriers lemma),
    as well as $\Phi$, $\Phi^\circ$, the seed and the sweep.

## Minor

- **m1** fixed: $\df{y(t)=f_{y,t}}$ is written out.
- **m2** fixed: the rewriting is "applied for each $y(t)$ in turn".
- **m3** fixed: "$\exists X_iR_i\models A_i$ iff $R_i\models A_i$" is written out.
- **m4** fixed: "a rational history $z$".
- **m5** fixed: the remark after Lemma 2 now cites $\neg A_i\models S_i$.
- **m6** fixed: the claim says "for every $i\in N$". The argument adds that (V2) is trivial and that (K) holds by the
  rule lists.
- **m7** fixed with the proposed wording.
- **m8** fixed: "the projected cell (computed in 2.4 ms)".
- **m9** fixed in Section 1: "re-asks the model, up to a fixed number of attempts".
- **m10** fixed: "cannot be reproduced by re-running".
- **m11** fixed:
  - The bullet now reads "Cost", priced per call.
  - It adds "(at most 16 calls)".
  - The price source is given as "an estimate from the Claude API notes".
- **m12** fixed: "The alternative".
- **m13** fixed: $\square_{[0,2]}(u=0\wedge v=0)$.
- **m14** fixed: "(or, for (K) without a rule list, one sentence over the component's ports)".
- **m15** fixed: "Only the sweep, which computes $S_{Q_i}$, eliminates what $i$ cannot see."
- **m16** fixed: "(Opus 5.5 by its migration guide, Sonnet 5.5 by the API notes)".
- **m17** fixed: "outputs of components outside $N$".
- **m18** fixed: "Quantifier-free verdicts are deterministic".
- **m19** fixed: the $A_i=\FALSE$ bullet now says that every $S_j$ already passed (K), hence (R), before (V2) is
  reached.
- **m20** fixed: Chatterjee et al. is described as "the natural symbolic proposer for one component's (K), and a
  baseline".
- **m21** no change needed. The review found every Strands claim backed by `strands.md`. The only edits are m9, m16
  and a shorter section.
- **m22** fixed: "trivial (all $A_j=\TRUE$)".
