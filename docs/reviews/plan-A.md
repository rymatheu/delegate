# Review of docs/plan.tex ("Delegation by proposal and verification: a research plan"), reviewer A

Reviewed 19 October 2026, against notes/agentic/{formulation.md, strands.md, literature.md, literature.bib,
governor_checks.out}, lit/existing-work.bib and docs/complete.tex.

**What I ran.**
- `latexmk -pdf plan.tex`: compiles with no warnings and no overfull boxes; **5 pages**, so the limit is met with no
  slack. Every fix below that adds text needs a cut (see the end of the review).
- `.venv/bin/python notes/agentic/governor_checks.py` under `PYTHONHASHSEED=0,1,2,3`: exit 0 every time,
  "101 verdicts; all as expected", 0.24 to 0.27 s wall. With times masked, the output is byte-identical across the
  four seeds and identical to the saved `governor_checks.out`.
- `notes/agentic/sweep_timing.py`: **40.3 s** (fresh process), against the "440 s alone" in the plan.
- `.venv/bin/python scripts/delegate.py`: exit 0, 98.7 s in total.
- grep of every `\cite` key: all 11 exist (10 in notes/agentic/literature.bib, `incer2018quotient` in
  lit/existing-work.bib).
- grep for the banned words: none occur. "ears" matches only inside "appears" (line 114). One cited title,
  Chatterjee et al., contains "Template-based"; that is acceptable.

---

## (1) BLOCKING issues

**B1. (R), (K), "causal strategy" and "acceptable delegation" are never defined in the plan.** They are the core of
the constraint table, of Lemma 1 and of the soundness theorem. The notation paragraph defines ≼ in a formula but
gives none of these four. Section 1 says only "(V1), (V2), (R), (K) below", and "below" gives only the quantified
form of (K) in a table cell and the words "(K) implies receptiveness (R)".
- Quoted: "(K) implies receptiveness (R). By the validity proposition of \texttt{complete.tex}, (C1), (V1), (V2), (K) say exactly ``acceptable delegation''."
- Proposed (add to the notation paragraph): "Component $i$ is *receptive* (R) if for every history of $\inp(i)$
  some history of $\outp(i)$ gives a trace in $S_i$. A *causal strategy* for $i$ gives, for each $t\le H$, the
  values of $\outp(i)$ at time $t$ as a function of the values of $\inp(i)$ at times $\le t$; $S_i$ is *causal*
  (K) if some causal strategy produces, from every history of $\inp(i)$, a trace in $S_i$. A family is an
  *acceptable delegation* if each $C_i$ is over $\ports(i)$ and (V1), (V2), (R), (K) hold."

**B2. Lemma 1(b): the proof does not handle outputs of the same component at the same time.** In the (K) sentence
the block $\exists\outp_i(t)$ holds every output of $i$ at time $t$. Eliminated from the inside out, the witness of
$y(t)$ may mention an output $y'(t)$ of $i$ quantified before it in the same block, **and it may mention it in a
value**. Lemma 6(c) of complete.tex makes values affine *at time t*, and $y'(t)$ is at time $t$. Example:
$S_i=(y_1=x)\wedge(y_2=y_1)$; eliminating $y_2$ first gives the witness $s_{y_2}=y_1$. The plan's rule list allows
values affine only in $\inp_i(t)$, so these occurrences must be substituted away. Step 6 of complete.tex, cited as
"Substitute the witnesses of those outputs as in step 6", does not do this. Step 6 substitutes only into
*regions*, and it justifies that by "$s<t$ ... so $z(s)$ occurs only in regions (values are at time $t$)". That
premise fails for same-time outputs. The conclusion still holds, because composing piecewise-affine rules gives
piecewise-affine rules, but the proof as written has a gap. On the other question asked: earlier inputs (times
$<t$) can occur only in regions, never in values (Lemma 6(c)). So the plan's restriction "values affine in
$\inp_i(t)$" matches formulation.md (§2, "affine ... in the inputs of $i$ at time $t$") and is what elimination
gives once the same-time outputs are substituted. Given $S_i\in\mathcal L$, the lemma holds as stated.
- Quoted: "the witness of $y(t)$ mentions only inputs at times $\le t$ and earlier outputs of $i$. Substitute the witnesses of those outputs as in step 6; this ends."
- Proposed: "the witness of $y(t)$ mentions only inputs of $i$ at times $\le t$, outputs of $i$ at times $<t$
  (in regions only), and outputs of $i$ at time $t$ earlier in the block (in regions and values). Substitute the
  witnesses of these outputs, earliest first: in a region, replace each atom $\alpha$ mentioning $z$ by
  $\bigvee_{(\pi',c')}(\pi'\wedge\alpha[z:=c'])$ as in step 6; in a value $c$ mentioning $z(t)$, replace the pair
  $(\pi,c)$ by the pairs $(\pi\wedge\pi',c[z(t):=c'])$. Values stay affine at time $t$, regions stay in
  $\mathcal L$, and each round brings in only earlier variables, so this ends."

**B3. "Cells, not points": the claim that every projected history lies outside $S_{Q_i}$ is false for one of the
obligations to which it is applied.** The cell is defined for any obligation $\omega$, and routing (1) uses
projected cells of (V2) failures. Take a (V2) failure of $j$ and the component $i=j$; this case arises because
routing (1) asks "the writers of the non-environment variables of $A_j$", and $j$ writes its own outputs, which
$A_j$ may mention. Then the cell entails $R_j\wedge\neg A_j$. A history $z$ in the projected cell has a completion
in $R_j$, so $z\in A_{Q_j}$, but $z$ need not lie outside $S_{Q_j}=\forall X_j(R_j\to G_P\wedge\bigwedge_{k\ne
j}A_k)$. The fault there is $A_{Q_j}\not\models A_j$, not $S_j\not\models S_{Q_j}$. For the (V1) obligation, and
for a (V2) obligation of $j\ne i$, the claim is right.
- Quoted: "By Lemma~\ref{lem:quot}(c), every history in it lies outside $S_{Q_i}$, and stays outside while the other sets only grow."
- Proposed: "If $\omega$ is the (V1) obligation, or the (V2) obligation of some $j\ne i$, every history in the
  projected cell lies outside $S_{Q_i}$ (Lemma~\ref{lem:quot}(c)). For the (V1) obligation it stays outside while
  the other sets only grow; for (V2) it does so only while $A_j$ is also unchanged. For the (V2) obligation of $i$
  itself, the projected cell lies inside $A_{Q_i}$ and violates $A_i$: it shows that $A_i$ is too strong."

**B4. Termination over a finite candidate set: unsupported, and false as read.**
- Quoted: "Over a finite candidate set the no-repeat record also ends the loop, and exhausting it means only ``none in this set''."
- (i) The record does not end the loop. A repeated triple becomes DECLINE, and nothing in the pseudocode or in
  routing stops when every component has declined. The loop then idles until the budget $B$ runs out.
- (ii) Even with a stop rule, the loop is a local search: each round changes one $C_i$, chosen by routing. When it
  stops, all *neighbours of the current family* have been rejected, not all tuples in the set. "None in this set"
  does not follow from that. formulation.md (Termination, item 2) makes the "none in $\mathcal K_B$" claim only for
  exhausting $\mathcal K_B$, and that is what the enumerator does, not the routed loop.
- Proposed: "Over a finite candidate set, the enumerator of WP3 checks every tuple, and if none passes it reports
  ``none in this set'' (not ``none exists''). The routed loop ends only by the budget, or by a rule ``stop when every
  component of $N$ declines on the same failure'', and that stop says nothing about the set."
  WP1's "no repeats end the loop over finite candidate sets" needs the same correction.

**B5. "A discrepancy" is contradicted by README.md.**
- Quoted: "\texttt{README.md} says \texttt{scripts/delegate.py} runs in about 1\,s. ... The README will be corrected."
- README.md line 27 now reads "about 90 s in total; the speed-governor sweep at horizon 2 takes most of it". My run
  took 98.7 s.
- Proposed: delete the paragraph. This also frees about three lines for B1. If a sentence is wanted:
  "\texttt{scripts/delegate.py} takes 85\,s in total, 71\,s of it the governor sweep
  (\texttt{notes/agentic/delegate\_instance\_times.txt})."

---

## (2) MAJOR issues

**M1. "the result is not maximal"** (Section 1, condition (3)) is false as stated. The result may be maximal; it is
only not guaranteed to be. Proposed: "the result is not guaranteed to be maximal".

**M2. Non sequitur on maximality.**
- Quoted: "Maximality is given up: by the proposition ``no greatest solution'' of \texttt{complete.tex}, no acceptable delegation contains all others, so \texttt{complete.tex} already selected one by fixed orders"
- That no greatest solution exists explains why a *selection* is needed. It does not explain why *maximality* is
  lost; the sweep yields a maximal selection. Maximality is lost because no quantifier-free check decides it.
- Proposed: "Maximality is given up, because deciding it is an $\exists\forall$ question that only the sweep
  answers (Section~3). Selection itself is not new: by the proposition ``no greatest solution'', no acceptable
  delegation contains all others, so \texttt{complete.tex} already selected one by fixed orders (orderings,
  candidates, prefix, sweep). Now proposers select."

**M3. Lemma 2(a): the proof skips the step that matters, and ⊗, /, ρ_W are not defined in the plan.** The
mathematics is right. I checked it against complete.tex. The others compose to $(A',S')$ with
$S'=\bigwedge_{j\ne i}S_j$ and $A'=\bigwedge_{j\ne i}A_j\vee\neg S'$. Then $P/(A',S')=(A_P\wedge
S',(S_P\wedge A')\vee\neg(A_P\wedge S'))$, whose assumption is $R_i$. On $R_i$, $S_P=G_P$ and
$A'=\bigwedge_{j\ne i}A_j$, so the guarantee is $R_i\to G_P\wedge\bigwedge_{j\ne i}A_j$. "Equal, on $R_i$, to ..."
alone does not determine the guarantee: one also needs that it is true off $R_i$. A reader of the plan cannot check
any of this, because the notation paragraph only says the operations "are those of complete.tex".
- Quoted: "(a) The quotient has assumption $A_P\wedge\bigwedge_{j\ne i}S_j=R_i$ and a guarantee equal, on $R_i$, to $G_P\wedge\bigwedge_{j\ne i}A_j$; then project."
- Proposed: "(a) The others compose to $(A',S')$, $S'=\bigwedge_{j\ne i}S_j$, $A'=\bigwedge_{j\ne i}A_j\vee\neg
  S'$. The quotient $P/(A',S')=(A_P\wedge S',\,(S_P\wedge A')\vee\neg(A_P\wedge S'))$ has assumption $R_i$, and,
  as $S_P=G_P$ and $A'=\bigwedge_{j\ne i}A_j$ on $R_i$, guarantee $R_i\to G_P\wedge\bigwedge_{j\ne i}A_j$.
  $\rho_{\ports(i)}$ takes $\exists X_i$ of the assumption and $\forall X_i$ of the guarantee."
- Also add the three operation formulas (one display line) to the notation paragraph.

**M4. Routing: the sentence on (V2) is true, but its reason is wrong, and it makes part of routing rule (1)
unreachable.**
- Quoted: "(V2) comes first: a (V1) trace violating some $A_j$ is a (V2) failure, since off $A_j$ saturation lets $j$ do anything."
- Such a trace satisfies $A_P\wedge\bigwedge_iS_i\wedge\neg A_j$, so it is a (V2) counterexample by definition.
  Saturation explains why $j$'s assumption is the right thing to blame, not why the trace is a (V2) failure.
  Because the verifier stops at the first failure and checks (V2) first, a (V1) failure is reported only when
  (V2) holds for every $j$. Then no (V1) trace violates any $A_j$, so the clause "or a (V1) trace violating some
  $A_j$" in routing (1) can never fire. The governor run shows both failures only because governor_checks.py runs
  every check.
- Proposed: "(V2) comes first: a (V1) counterexample that violates some $A_j$ satisfies $A_P\wedge\bigwedge_iS_i
  \wedge\neg A_j$, so it is a (V2) counterexample, and the right fault to report, since off $A_j$ saturation lets
  $j$ do anything. Once (V2) holds, every (V1) counterexample satisfies all $A_j$." Then delete "or a (V1) trace
  violating some $A_j$" from routing (1).

**M5. Routing (3) promises an input history that the sentence check cannot give.**
- Quoted: "(3) On a (K) failure for $i$: return the failing input history to $i$."
- When the quantified (K) sentence is false, there is in general no single failing input history: the
  environment's refutation adapts to the outputs. formulation.md's verifier returns `K(i, -)` in that case, and
  governor_checks.out prints no history for "(K) by alternation: False".
- Proposed: "(3) On a (K) failure for $i$: return the failing input history if a rule list was given; otherwise
  return only the verdict."

**M6. Pseudocode: undefined names and mismatches with the text.**
- Line 2: "Phi is cheap at this H" has no criterion. Give a time limit $T_\Phi$.
- Line 12: "(last i, last C, ...)" is undefined in round 1, where $F$ comes from line 6 and no single $i$ was last.
- Lines 15–16: `C := DECLINE` and then `F := F with C_i := C` installs DECLINE as a contract. "Ask the next one" is
  a comment, not code, and nothing records who has declined on the current failure. Routing (1)'s "if there are
  none, or all decline, ask $j$ to weaken $A_j$" is not represented either.
- Line 14: `forbidden_i + region` adds an input history (the (K) case of line 13) to a set of forbidden regions
  over $\ports(i)$. These are different kinds of object.
- Line 22 checks $S_i\models S_C$, (V1) and (V2), but not (C1). Yet the soundness proof says the weakening step
  "checks (V1), (V2), the ports by syntax". Add "and $C$ passes (C1)" to line 22 and to the weakening paragraph
  ("three quantifier-free checks" plus the syntax check).
- Line 7 runs `verify` on the seed, which checks (K), while the text says the seed route "needs no (K) check". The
  seed is acceptable by the soundness theorem of complete.tex. Either say line 7 re-checks it, or skip the check.
  If (K) is checked by rule list, say that the seed's rule list sets edge values outside $\sigma_k$ to 0, as in the
  (R), (K) part of the soundness proof in complete.tex; otherwise those values are unconstrained.

**M7. Forbidden regions accumulate in repair mode, where the other sets shrink.** A cell stays forbidden "while the
other sets only grow". Repair mode strengthens guarantees (it shrinks $S_j$), and then $R_i$ shrinks and an old
cell can become allowed. Line 14 never drops old regions, so an enumerator that obeys `forbidden_i` can exclude the
only solutions. That breaks completeness and canonicity, though not soundness. Proposed: "forbidden_i holds only
the cells computed since the last change of the other sets that shrank one of them; older cells are dropped."
Alternatively, state that forbidden regions are advice only and that the enumerator ignores them.

**M8. Completeness by interleaving is not defined for this loop.**
- Quoted: "taking every $k$-th proposal from the enumerator restores it at a factor $k$ in rounds."
- The semi-decision claim enumerates *tuples* and checks each tuple on its own. The loop changes one $C_i$ per
  round, under routing, the forbidden regions and the no-repeat record. A "proposal from the enumerator" inside
  this loop is not a fair enumeration of tuples. Proposed: "every $k$-th round verifies the next tuple of the fair
  enumeration on its own (not as a change to $F$); this restores completeness at a factor $k$ in rounds."

**M9. The trust base leaves out the verifier's own code.**
- Quoted: "The trust base is Z3's unsat answers in quantifier-free linear real arithmetic, Z3's answer on the (K) sentence when no rule list is given, and the compiler $[\cdot]_0$ from PolySTL to $\mathcal L$."
- Soundness also rests on the Python that parses proposals with only the ports declared ((C1)), checks rule-list
  causality by syntax, builds $S_i[f_i]$ and $S_i=\neg A_i\vee G_i$, and assembles the (V1) and (V2) formulas.
  Proposed: append "and the verifier's Python code that parses proposals, checks (C1) and rule-list syntax, and
  builds $S_i$, $S_i[f_i]$ and the (V1), (V2) formulas."

**M10. Lemma 1 is presented as proved, but WP1 lists it as still to be proved.** WP1 says "Lemma~\ref{lem:rules} in
full". Either fix the proof (B2) and drop it from WP1, or title it "Lemma (proof sketch)". As it stands, the claim
that follows rests on a lemma whose status is unclear.

**M11. "440 s alone" is not backed by any saved output and was not reproduced.** No output file of
`sweep_timing.py` exists; its docstring says "about 7 minutes on the author's machine". My run took **40.3 s**.
Proposed: "sweep 71\,s inside \texttt{scripts/delegate.py}; alone in a fresh process 40\,s to 440\,s across runs
(Z3's term order depends on earlier symbols)". Or drop "440 s alone" and keep 71 s, which
delegate_instance_times.txt backs (4.30 s to 75.53 s).

**M12. Symbols used in Section 1 before the notation paragraph.** Section 1 uses $N$, $\Phi$, $\Phi^\circ$,
"nested orderings", "seed", "sweep" and "forwarding". $\Phi$ and $\Phi^\circ$ are described only in Section 2, and
"forwarding" is never described. Proposed: in Section 1, write "the existence sentences $\Phi$ and $\Phi^\circ$ of
complete.tex (Section 2)". Add to the notation paragraph: "*Forwarding*: on a nested ordering, each component
copies onto the edge to the next component the values that the next cannot see (complete.tex, Lemma carriers)."

---

## (3) MINOR issues

- m1. $\df{y(t)=f_{y,t}}$ is used and never written out. Add: "$\df{y(t)=f_{y,t}}:=\bigvee_l(\pi_l\wedge\bigwedge_{l'<l}\neg\pi_{l'}\wedge y(t)=c_l)\vee(\bigwedge_l\neg\pi_l\wedge y(t)=0)$".
- m2. The atom rewriting for $S_i[f_i]$ handles one $y(t)$ per atom. An atom may mention several outputs at time
  $t$. Add "applied for each such $y(t)$ in turn".
- m3. Lemma 2(b) proof: "and likewise for $A_i$" is the dual statement. Write it: "$\exists X_iR_i\models A_i$ iff
  $R_i\models A_i$".
- m4. Lemma 2(c): $(\ports(i)=z)$ is a formula of $\mathcal L$ only for a rational $z$. Write "a rational history $z$".
- m5. "(b) is (V1), (V2) seen from $i$": for $j=i$ this needs saturation. Add: "($R_i\models A_i$ is (V2) for $i$,
  as $\neg A_i\models S_i$)".
- m6. Semi-decision claim: "every $S_i$ is $\df{f_i}$" conflicts with (C0) for $i\notin N$; write "every $i\in N$".
  The argument after it should also say that (V2) is trivial with assumptions $\TRUE$ and that (K) holds by the
  rule lists.
- m7. "excluding finitely many points changes nothing that matters" is vague. Proposed: "a proposer can exclude a
  counterexample point while every nearby trace still fails the obligation, so repair against single points need
  not converge."
- m8. "its repair excludes the projected cell (2.4\,ms)": the 2.4 ms is the time to compute the projected cell
  (governor_checks.out). Proposed: "its repair excludes the projected cell, computed in 2.4\,ms".
- m9. "re-asks the model until a Python check passes" (Section 1): the re-asking stops after `max_attempts`
  attempts (default 10, strands.md §3). Add "up to a fixed number of attempts".
- m10. "Language-model runs cannot be re-run" → "Language-model runs cannot be reproduced by re-running".
- m11. Cost: "under \$2 for the relay over 8 rounds" comes from strands.md's skeleton, which calls every proposer
  every round (16 calls). The plan's loop asks one proposer per round. Write "(at most 16 calls)". The bullet says
  "Cost per round" but quotes a cost per call. The prices come from a cached skill table, not an official page
  (strands.md §7.5); "an estimate" covers this, but name the source.
- m12. "The honest alternative" is evaluative. Use "The alternative."
- m13. "$\square(u=0\wedge v=0)$" has no interval. Write $\square_{[0,2]}$.
- m14. "quantifier-free validity queries check it" (Section 1): (K) without a rule list is quantified. Add "(or, for
  (K) without a rule list, one sentence over the component's ports)".
- m15. "The sweep computes $S_{Q_i}$ as a formula; only that is costly." Deciding $\Phi$ by elimination is also
  costly in general. Proposed: "only that step eliminates variables the component cannot see."
- m16. The tool-choice blocker for `claude-sonnet-5-5` rests on "the Claude API skill's model notes", not on the
  official migration guide (strands.md §7.1). Say so, or cite it for Opus only.
- m17. "(C0) loses nothing: outputs outside $N$" → "outputs of components outside $N$".
- m18. "Verdicts are deterministic": this holds for the quantifier-free checks with no timeout. The (K) sentence is
  quantified and may return "unknown"; the next sentence of the plan treats "unknown" as a rejection. Add
  "quantifier-free".
- m19. Risks, $A_i=\FALSE$: the argument is correct. With $A_i=\FALSE$, $S_i=\TRUE$, and (V2) for $i$ needs
  $A_P\wedge\bigwedge_jS_j$ to be unsatisfiable. With $A_P$ satisfiable over environment variables only, fix such
  an environment history, then choose outputs component by component in topological order using (R). Acyclicity
  makes every component's inputs fixed before its turn. The hypothesis "every $S_j$ satisfies (R)" always holds
  when (V2) is reached, because the verifier checks (K) first. Saying so makes the bullet self-contained.
- m20. Related work. Each characterisation matches literature.md: Katis (realizability and Skolem extraction for
  one contract over LRA), Golia 2021 (DQF(T)), Manthan3 (Boolean learn–verify–repair), Chatterjee (linear Skolem
  functions for quantified LRA), Sun (closest architecture; literature.md: "What it lacks: a global contract
  algebra, real-valued time, and receptiveness"), Xu, Finkbeiner–Metzger–Moses, Bloem, Jha–Seshia, and the negative
  finding (d)1. One nuance: literature.md (d)5 says template Skolemization "handles quantified LRA with linear
  prefixes, not dependency sets". That fits one component's (K) sentence, not the whole family, so write "the
  natural symbolic proposer for one component's (K)". The summaries are from abstracts only (literature.md
  header); "as far as a search ... shows" covers this.
- m21. Strands section: every claim checks against strands.md: version and date, Python ≥3.10, Apache-2.0,
  `AnthropicModel`, `structured_output_model` with validation retries, hooks, Graph with Python predicates and text
  passing and a custom verifier node, Swarm and Agents-as-Tools rejected, AI Functions 0.5.0 on Python ≥3.12,
  experimental, the forced tool choice, no temperature or seed, the pins, Bedrock as the default, the plain-SDK
  alternative. Nothing is added beyond the note, apart from m9 and m16.
- m22. Evidence table: every number matches governor_checks.out exactly. $D_{\rm react}$: 2.9, 0.9, max(0.3, 0.4,
  0.6)=0.6, max(6.9, 4.5, 4.9)=6.9. $D_{\rm lazy}$: 0.5, 0.8, 0.3, max(0.5, 0.4, 1.1)=1.1. Swept family: 0.6, 0.9,
  max(0.6, 0.5, 1.5)=1.5. $H=80$: 12.1, 15.5, 324 timed variables. $\Phi$ 0.03 s, seed 0.02 s and sweep 71 s match
  delegate_instance_times.txt. 101 verdicts, 0.26 s: I measured 0.24 to 0.27 s. "(V2) trivial" at $H=80$ is not a
  printed verdict; it follows from all assumptions being $\TRUE$. Say "trivial (all assumptions true)".

---

## Answers to the specific questions

- **Lemma 1(a)**: yes, immediate. The rule list is syntactically a causal strategy, and validity of $S_i[f_i]$ says
  exactly that its traces lie in $S_i$.
- **Lemma 1(b)**: it draws correctly on Lemma 6(b), (c) and on the (V1) induction of the soundness theorem. The
  same-time, same-component case is a gap (B2). "Affine at its time" is right: earlier inputs occur only in regions.
  The plan's definition, which allows regions over inputs at times $\le t$ and values in $\inp_i(t)$ only, agrees
  with formulation.md, and the lemma holds as stated once B2 is fixed.
- **Lemma 2**: (a), (b), (c) are correct, including the conjunct $\bigwedge_{j\ne i}A_j$ in the guarantee. The
  proof of (a) is too terse (M3).
- **Routing sentence**: true, wrong reason, and it makes a routing clause dead (M4).
- **Pseudocode**: see M6 and M7.
- **No culprit**: correct. $x\models A_P\wedge\bigwedge S\wedge\neg G_P$ gives $x|_{\ports(i)}\in S_i$, because
  $S_i$ is over $\ports(i)$, and $x$ is a completion that makes the formula of Lemma 2(c) satisfiable. This holds
  for every $i$, including $i\notin N$.
- **Evidence table**: matches exactly (m22). The verdict count of 101 was reproduced under four hash seeds. "440 s"
  was not reproduced (M11). The README discrepancy is stale (B5).
- **Related work and Strands**: all cite keys exist, and the characterisations match the notes (m20, m21).
- **Risks, $A_i=\FALSE$**: correct (m19).
- **Vocabulary**: clean. "Template-based" in a cited title is acceptable.
- **Pages**: 5. Fixes B1, M3 and M12 add about 8 lines. Deleting the stale discrepancy paragraph (B5) frees
  about 3. Cutting the repeated "Recommended shape" and "honest alternative" sentences in Strands, which Section 1
  already says, and the parenthetical list in Section 1 "(orderings, candidates, prefix, sweep)" frees about 4 more.

## (4) Verdict

**Not acceptable as is: 5 blocking, 12 major, 22 minor.** The contract mathematics (validity, quotient, projection,
no culprit, the $A_i=\FALSE$ argument) is correct, and the evidence numbers are exact. The blocking problems are
local: four undefined constraint names (B1), a gap in the proof of Lemma 1(b) (B2), one over-general claim about
cells (B3), a false termination claim (B4), and a stale claim about README.md (B5). Each has a one- or two-sentence
fix. The major issues are mostly about the loop as written (routing, pseudocode, forbidden regions, interleaving),
which does not yet match what the theorems need. Fix B1–B5 and M1–M9 within the 5-page limit, and the plan is
acceptable.
