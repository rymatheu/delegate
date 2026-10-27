# Round 2, Reviewer B (clarity and comprehensibility): docs/complete.tex / complete.pdf (revised)

I re-read the revised PDF from the start, linearly, as the skeptical author would. I checked exact wording
against the tex, then read docs/reviews/round1-rebuttal.md.

Checks:
- The PDF is 5 pages.
- `.venv/bin/python scripts/delegate.py` exits 0.
- Its first 21 lines are identical to the Verbatim block (checked with `diff`).
- The relay candidate list follows from the stated order rule. The listed T is correct, but see N3: two
  candidates are duplicates, not one.
- The new Lemma 1 proofs are correct. So are the trivial-start relay computation and the fork example of
  Section 10. I checked each by hand.

Severity: BLOCKING = the reader stops or is misled; MAJOR = the reader has to reconstruct something or
distrusts a claim; MINOR = friction.

---

## Part 1. Round-1 items: does the fix answer the reader's objection?

| # | Round 1 | Status | Comment |
|---|---|---|---|
| 1 | BLOCKING: "only contract operations" | **Mostly resolved; one MAJOR remains (N1)** | Lemma 1 and the computation from trivial contracts settle the question. The concluding sentence is a non sequitur. |
| 2 | BLOCKING: why Φ has this form | **Resolved** | The "Why one sentence" paragraph and the fork example make the order and (E)/(Cap)/(Info)/(Pure) feel necessary. One small gap remains (N5). |
| 3 | Candidates without reason | Resolved | The "Idea" paragraph comes before T. |
| 4 | Witness ambiguous; order unstated | Resolved | Regions π_c, the rule s_y, ⟦y=s_y⟧ and φ[y:=s_y] are all defined. A reader can now state the order. Small slip in the example (N3). |
| 5 | Three elimination methods | Resolved | Fourier–Motzkin is labelled as a hand-computation aid. The end of Section 6 says any equivalent formula may be used, and that witnesses depend on the choice. |
| 6 | L vs quantified formulas | Resolved | |
| 7 | Operations only as formulas | Resolved | |
| 8 | "graph" used twice | Resolved | "architecture graph" vs "defining formula ⟦y=s_y⟧". |
| 9 | Overview: no example, dishonest scope | Resolved in substance | Honest about chains-only completeness. Telegraphic (N7). "Elsewhere it can only refute" overlooks the H=0 Remark (N4). |
| 10 | Step 6 not an operation | Resolved | It is now an operation on (region, value) pairs, with the s<t argument and termination. Step 4 states that s_y mentions only earlier variables. |
| 11 | Script's step 9 and (V2) | Resolved | "(V2) after sweep: True" appears in the quoted output. |
| 12 | Semi-decision underspecified | Resolved | The enumeration over rational θ with decidable linear checks is well defined. Jargon nits in N6. |
| 13 | Density, margins, verbatim | Partly resolved; rebuttal accepted | 8pt verbatim is readable. I accept the margin rebuttal (0.75in at 10pt is defensible, and the page budget is binding). The Display line still wraps and keeps the 8-space gaps from Z3's printer; this is now MINOR. |
| 14 | Unstated modeling assumptions | Resolved | |
| 15 | E_k(t), Y_k(t) wording | Resolved | |
| 16 | Index clash | Resolved | |
| 17 | Formulas as sets; "environment" | Resolved | |
| 18 | "Read Φ as a game" | Resolved | |
| 19 | Fork use of Theorem 9 | Resolved | Via Φ°. |
| 20 | Relay step 7 | Resolved | |
| 21 | Legend "(K) by Lemma 5" | Resolved | "Choice functions" is undefined jargon (N6). |
| 22 | Mapping printed contracts | Resolved | |
| 23 | Disjunctive example unverifiable | Resolved by removal | The refutation instance was also removed. Now no instance shows the "none exists" branch (N8). |
| 24 | "as far as correctness allows" | Resolved | |
| 25 | κ well defined; plain words | Resolved | "(largest such j)" is badly placed (N10). |
| 26 | S_j vs S_{i_j} | Resolved | |
| 27 | Delay argument | Resolved | |
| 28 | Edge variables' meaning | Resolved | |
| 29 | Prop. 3(a) gloss | Resolved | |

Old blocking item 2, specifically. "Radio chooses nothing" is now explained before the reader reaches it. The
example in Section 10 makes the danger concrete: a true sentence for the ordering B, A with no strategies. So the
four conditions read as fixes for a demonstrated failure, not as assertions.

Old item 4, specifically. A reader can now write T for any formula by hand. The ASCII rule is unusual in a
mathematics document, but it is honest and complete. The document also says plainly that equivalent rewritings
change the witnesses and that the output is not canonical.

---

## Part 2. Remaining and new issues

### MAJOR

**N1. The conclusion of "What the algebra alone gives" does not follow, and "unavoidable" overclaims.**

*Where:* end of Section 3: "Each operation returns one determined result, so the algebra needs non-trivial
contracts to start from, and none is best. So steps 2 to 7 ... select one acceptable delegation; this is the
only part that is not a contract operation, unavoidable by Proposition 5".

*Reader:* "Your procedure also returns one determined result. So 'each operation returns one determined result'
cannot be the reason. Proposition 5 shows there is no greatest acceptable delegation. It does not show that
every expression built from the operations fails. 'Unavoidable' is not proved."

The computation before this sentence is convincing. The inference after it is not. The honest argument is
already on the page: Lemma 1 gives each contract as a function of the others. That is a condition linking the
contracts to each other, not a way to start. Starting from trivial others fails on the relay.

*Rewrite* (replace the two sentences after "neither is receptive."):

> So the algebra relates each contract to the others but does not supply a starting point. Started from trivial
> contracts, it gives unusable ones. By Proposition 5 there is also no best acceptable delegation that some
> combination of the operations could be asked to return. We therefore *select* one, in steps 2 to 7
> (Section 6). This selection is the only part of the procedure that is not a contract operation, and
> Proposition 2 checks its result. Steps 8 and 9 use only quotient and projection.

Also write the skipped step: "With all others (true, true), `P / ⊗_{j≠i}(true,true) = P`, so the relay gets
`ρ_{r,m}(P) = …`".

### MINOR

**N2. Name clash in the fork example.** "Let unconnected A, B map s1 ↦ a, s2 ↦ b". A already denotes
assumptions. B is the budget in the very next sentences ("at most B pairs"). Rename the components, e.g. Left
and Right.

**N3. Duplicates in the relay candidate list.** "T is r, r−1/2, r+1/2, r+3/2, r−3/2, 0 (r + 1/2 − 1 is a
duplicate)". Two candidates are dropped: (r+1/2)−1 = r−1/2, and (r−1/2)+1 = r+1/2. The list is right; the
parenthesis is incomplete. Write "((r−1/2)+1 and (r+1/2)−1 are duplicates)".

**N4. The overview contradicts the Remark.** "elsewhere it can only refute (Section 10)". Section 10 also gives
a semi-decision search that can construct a delegation when H = 0. Write: "elsewhere it can refute, and for H = 0
search for a delegation without a guarantee of halting (Section 10)".

**N5. The Φ rationale omits one kind of granted value.** The paragraph explains why fresh environment inputs of
later components are harmless (Info). It does not cover the earlier outputs of later components. Example: the
choice of `i_1` at time 1 comes after `Y_2(0)`, which `i_1` never sees. Step 3 mentions this only as "removed by
step 6". Add after the (Info) sentence: "The earlier outputs of later components are also granted. They are
themselves rules in values that `i_k` sees, so step 6 substitutes those rules."

**N6. Terms used without a gloss.**
- "context" (refinement, in words): "a context is an environment, i.e. a trace set the assumption must accept".
- "choice functions" (Section 9): "functions picking each ∃-value from the earlier values".
- "closed formula over L" (Remark): "a formula with every variable quantified".
- "first-match list" (Remark): "the first pair whose region holds gives the value".
- "regression instances" (Section 9): "extra test instances with known verdicts".

One clause each.

**N7. The overview is telegraphic.** Example: "Refinement by the composition is two implications, which
unmeetable contracts satisfy; so each contract must also be met by a component computing outputs from inputs
received so far." This breaks the brief's rule of one idea per sentence, and the overview is what the author
reads first. Split at the semicolons, e.g.:

> Refinement by the composition amounts to two implications. Contracts that no component can meet satisfy them.
> So each contract must also be meetable by a component that computes its outputs from the inputs received so
> far.

The cost is about two lines.

**N8. No instance shows a false Φ.** Removing the refutation leaves "none exists" with no example. The script
still prints it. One line restores it:

> The script's H = 2 instance with `□|d−r| ≤ 1/2 ∧ ◇ d ≥ 1/4` prints Φ false: `r(t) = −1` forces `d(t) ≤ −1/2`.

**N9. The verbatim Display line still wraps and keeps 8-space runs.** This comes from the script's `fmt()`. It
is legible, but `" ".join(...split())` in the script would remove the wraps at no cost to exactness.

**N10. Lemma 8: "(largest such j)" sits at the end of the statement**, after the conclusion. Move it to the start:
"Let j < k be largest with v ∈ ports(i_j)."

---

## Part 3. New material

- **"Only contract operations" paragraph and trivial-start computation.** The facts and the computation are
  convincing. Showing Radio `(|r| ≤ 1, |r| > 1)` and Display `(true, false)` is exactly what this reader needs.
  Only the closing inference needs rewording (N1).
- **Φ rationale.** The quantifier order and the four conditions now feel necessary rather than asserted. The
  Section 10 fork example, a true sentence with no strategies, shows the failure that nesting prevents.
  (E) is shown to follow from (Cap), and the use made of (Info) is stated. One gap remains (N5).
- **Witness.** Defined precisely as a rule with regions. A reader can state its order and apply it by hand.
- **Step 6.** Now an operation on named objects, with a termination argument.
- **Overview.** Honest about chains-only completeness. Slightly inaccurate about "only refute" (N4), and too
  compressed (N7).
- **Readability at 5 pages.** Still dense. The run-in Section 8 and the compressed overview are the hardest
  parts. Dropping the disjunctive and fan-in instances costs nothing in comprehension; dropping the refutation
  costs a little (N8).
- **Forward references and jargon.** The forward references are harmless: to Lemma 6(a) in Section 2, to
  Lemma 8 and the condition labels in the rationale, and to Section 10. Each has a plain-words description where
  it is used. The new jargon is listed in N6, and the name clash is N2.

---

## Verdict: **revise (minor)**

No BLOCKING issue remains. One MAJOR remains (N1), and it is a two-sentence fix. The MINOR items total a few
lines. I do not need another full round if N1 is fixed as suggested.

**What the reader would still not understand:**
- Why the paragraph on algebra concludes that selection is "unavoidable": the justification offered, that each
  operation returns one determined result, applies equally to the procedure itself.
- Why the earlier outputs of later components may be granted to an earlier chooser. The rationale paragraph is
  silent on this, and only step 3 and the proof of Theorem 10 handle it.
- What an unrealizable query looks like, since no worked instance with Φ false remains.

Beyond these, a careful reader can follow every object, step and proof in the document, and can reproduce the
relay by hand, including the candidate order.
