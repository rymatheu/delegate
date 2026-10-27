# Round 2 rebuttal: docs/complete.tex

Writer's response to round2-A.md (rigor), round2-B.md (clarity) and round2-C.md (reproducibility).

**State of the revision**
- `docs/complete.tex` / `complete.pdf`: 5 pages, 10pt, 0.75in margins. latexmk exits 0, with no warnings, no overfull boxes and no undefined references.
- The relay block in Section 9 is set at 8pt on an 8.8pt baseline. It is a diff-exact copy of lines 1–21 of `.venv/bin/python scripts/delegate.py`, which still exits 0.
- The banned-word grep of `complete.tex` returns 0 lines. It also covers "Skolem", "notes", em-dashes, "---" and outside paths.
- The symbol-before-use check passes.

**Files changed outside the tex**
- `README.md`: the install line now pins `z3-solver==5.3.1.0`.
- `scripts/results_report.py`: only the hard-coded prose strings changed, to cite docs/complete.pdf (step 7, steps 8 and 9 with Theorem 11, Theorem 9) and "witness". No computation changed.
- `docs/results.tex`: regenerated. The diff is exactly those three lines.
- `docs/results.pdf`: recompiled, 2 pages, exit 0.

**Cut to fit five pages**
- The stand-alone example in Section 4. It is merged into relay step 4, which now lists the bounds, T, the two duplicates and the witness.
- The four-range reading of S_Display. It is now "(d = m on |m| ≤ 1/2)".
- The second half of step 3's grant sentence. The rationale paragraph in Section 5 now covers it, including B-N5.
- The relay sentence in the rationale is shortened.
- The phrase "so finitely many cannot fill it" in the delay argument (see A-9).
- Paragraph, section and theorem spacing is slightly tighter.

The verbatim block was not shrunk below 8pt.

Counts:
- Reviewer A: 9 issues; 9 ACCEPTED (A-9 in part).
- Reviewer B: 10 issues; 9 ACCEPTED, 1 REBUTTED (N9).
- Reviewer C: 5 issues; 5 ACCEPTED.

---

## Reviewer A

**A-1 (MAJOR), "unavoidable by Proposition 5" does not follow: ACCEPTED.** The paragraph *What the algebra alone gives* (end of Section 3) now makes these points, in order:
- **The skipped step:** P/(true, true) = (A_P, S_P ∨ ¬A_P) = P.
- **The trivial-start result:** Radio gets (|r| ≤ 1, |r| > 1) and Display gets (true, false). Neither is receptive.
- **The proof you supplied.** "No acceptable relay delegation comes from P and constant contracts by the operations: these introduce no variable and m is not in P, so Radio's set is over {r}, Display's over {d}; by (R) the first holds for all r, the second contains some d₀, and (V1) would need |d₀ − r| ≤ ½ on [−1, 1]."
- **The closing inference, in B's words.** "So the algebra relates each contract to the others but supplies no starting point, and by Proposition 5 there is no best delegation for it to compute. Steps 2 to 7 therefore select one (the only part that is not a contract operation, checked by Proposition 2)."
- **Deleted:** "unavoidable by Proposition 5" and "each operation returns one determined result".

**A-2, the algebra sense of "cannot be enlarged alone": ACCEPTED.**
- Theorem 11 now states (A_{i_k}, S_{i_k}) = ρ(P / ⊗_{j≠k}(true, S_{i_j})) = ρ(P / ⊗_{j≠k} C_{i_j}), where the C_{i_j} are the full output contracts.
- Proof: "the second quotient has the same assumption and a guarantee R_k → (G_P ∧ ⋀_{j≠k} A_{i_j}), equivalent by Lemma 1 as the output is valid."
- This is your argument. One direction holds because the stronger guarantee projects into S_{i_k}. The other holds because validity and Lemma 1 give C_k ≼ ρ(…).

**A-3, qe2 output not checked to be in L: ACCEPTED (as a disclosure).** End of Section 6: "simplified and checked equivalent (not checked for one time per atom)". The script belongs to the engineer, so I did not add the assertion. The document no longer implies the check is made.

**A-4, two duplicates: ACCEPTED.** Relay step 4: "(r − ½ + 1 and r + ½ − 1 are duplicates)".

**A-5, Lemma 8 wording and invariant: ACCEPTED.**
- The statement now opens "Let j < k be largest with v ∈ ports(i_j)."
- The proof opens "By induction w_l ∈ ports(i_l); …".

**A-6, gaps in the semi-decision remark: ACCEPTED.**
- (i) "Substitute in topological order and decide …".
- (ii) The strategies from Lemma 6(b) now fit the family "(disjoint regions in disjunctive normal form)".

**A-7, the Left/Right example is refuted under the other ordering: ACCEPTED.**
- *Forks*: Φ° is true whenever an acceptable delegation exists, "so a refutation test decides Φ° for every topological ordering".
- The example ends "((Cap) fails; Left, Right refutes)".
- Step 2 already points to this test for the case where no ordering is nested.

**A-8, the overview omits (Scope): ACCEPTED.** "If the query mentions only ports of relevant components forming a forwarding chain, this is complete and a false sentence proves none exists".

**A-9, the delay argument: ACCEPTED in part.**
- "With the other values fixed" is restored: "(with other values fixed, a formula gives a finite union of products in the (m(t+1), r(t))-plane, and a product inside the line is a point)".
- The closing clause "so finitely many cannot fill it" did not fit. The remaining step is immediate: a finite union of points is finite, and the line is not. I also corrected round-1-rebuttal's claim that it was present.

## Reviewer B

**N1 (MAJOR), the closing inference: ACCEPTED.** See A-1. Your replacement sentences are used, along with the explicit P/(true, true) = P step.

**N2, name clash: ACCEPTED.** The components of the fork example are now Left and Right, with orderings "Right, Left" and "Left, Right".

**N3, duplicates: ACCEPTED.** See A-4.

**N4, the overview contradicts the Remark: ACCEPTED.** "Otherwise it can refute, and for H = 0 search without a halting guarantee (Section 10)."

**N5, granted earlier outputs of later components: ACCEPTED.** The rationale paragraph now says: "Earlier outputs of later components are granted too; under (Info) they are rules in values the chooser knows, which step 6 substitutes."

**N6, terms without a gloss: ACCEPTED.**
- context: "every context (environment behaviour)".
- choice functions: replaced by "functions picking each ∃-value from earlier ones".
- closed formula: the term is gone.
- first-match list: replaced by "the first region that holds gives the value (default 0)".
- regression instances: "(tests with known verdicts)".

**N7, the overview is telegraphic: ACCEPTED.** "Refinement by the composition amounts to two implications." is now a sentence of its own. "Contracts no component can meet satisfy them, so each contract must also be met by a component computing its outputs from the inputs received so far." The choice sentence and its rule are also split. Further splitting did not fit in five pages.

**N8, no instance with a false Φ: ACCEPTED.** End of Section 8: "False Φ. H = 2, A_P = □_[0,2] |r| ≤ 1, G_P = □_[0,2] |d−r| ≤ ½ ∧ ◇_[0,2] d ≥ ¼, Φ is false (r ≡ −1 forces d ≤ −½)." The script prints this instance as "Phi (linearised sentence) = False".

**N9, wrapping and 8-space runs in the Display line: REBUTTED.**
- The block must reproduce the script's output byte for byte. Reviewer C checks it with `cmp`, and the brief requires exact printed lines.
- The runs of spaces come from the script's `fmt()`, which belongs to the engineer and was not in the coordinator's list.
- Changing it would change the quoted output for every reader on z3 5.3.1, so it is a script decision, not a document decision.
- At 8pt the line is legible, as you note.

**N10, Lemma 8 qualifier: ACCEPTED.** See A-5.

## Reviewer C

**N1 (MAJOR), the script's B = 1 run: ACCEPTED.** The Remark now ends: "The script runs one instance of this search, not the enumeration: on a fan-in graph Z3 decides the nonlinear ∃θ∀(environment)(A_P → G_P) for one affine map per output on the whole space (60 s timeout), then checks θ linearly."

**N2, "conjunctive normal form": ACCEPTED.** Section 9: "the sweep's G is S_{i_k}, a Boolean combination of atoms printed as Z3 simplifies it (order may vary with Z3's version)". This is the coordinator's wording. The printed G is equivalent to a formula of L, as Section 6 says of every quantified formula.

**N3, where witness atoms come from: ACCEPTED.** End of Section 6: the script "reads each witness from Z3's simplified ψ, which DELEGATE_TRACE=1 prints with T".

**N4, README pin: ACCEPTED.** The install line now reads `uv pip install -p .venv/bin/python z3-solver==5.3.1.0 numpy scipy`.

**N5, small inaccuracies: ACCEPTED.**
- Duplicates: see A-4.
- results_report.py prose now cites docs/complete.pdf (step 7, steps 8–9 and Theorem 11, Theorem 9) and says "witness term". results.tex is regenerated (the only diff is those three lines) and results.pdf recompiled.
