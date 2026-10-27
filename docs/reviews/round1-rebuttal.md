# Round 1 rebuttal: docs/complete.tex

Writer's response to round1-A.md (rigor), round1-B.md (clarity) and round1-C.md (reproducibility).

**State of the revision**
- `docs/complete.tex` / `complete.pdf`: 5 pages, 10pt, 0.75in margins. latexmk exits 0, with no warnings, no overfull boxes and no undefined references.
- The relay block in Section 9 is set at 8pt. It is a diff-exact copy of lines 1–21 of the new `.venv/bin/python scripts/delegate.py` output: the version line, the separator, and every relay line, including the new (V2) and after-sweep lines.
- The script was fixed by the engineer, not by me. It now implements the document's procedure.

**Numbering in the revised document**
- Lemma 1: adjunction and localisation (new).
- Proposition 2: validity conditions.
- Proposition 3: validity alone is empty.
- Definition 4: (R), (K), acceptable.
- Proposition 5: no greatest solution.
- Lemma 6: elimination with witnesses.
- Definition 7: nested ordering.
- Lemma 8: carriers.
- Theorems 9, 10 and 11: necessity, soundness and sweep.
- Sections are numbered 1 to 10.

**Dropped for space**
- The disjunctive-query instance. Its witness, m−3/8 on [−1,−1/8), 0 on [−1/8,1/8], m+3/8 on (1/8,1], is now fully derivable from the candidate order stated in Section 4. I checked the derivation by hand and with Z3. It no longer fits in five pages at 8pt verbatim.
- The refutation instance.
- The fan-in strategy details.

The brief allows both instances, but does not require them ("may be summarized"). I chose this over shrinking the verbatim block.

Counts:
- Reviewer A: 20 issues; 20 ACCEPTED, 0 REBUTTED.
- Reviewer B: 29 issues; 28 ACCEPTED, 1 partly REBUTTED (B-13).
- Reviewer C: 3 MAJOR and 13 minor issues; 15 ACCEPTED, 1 partly REBUTTED (m13, the same point as B-13).

---

## Reviewer A (rigor)

**A-1 (BLOCKING), (Scope) counterexample: ACCEPTED.**
- The reviewer is right. Without (Scope), o(0) is free and Φ is undefined. Closing it universally misreads an output of Q as an environment value. With ∃o the sentence is true.
- I deleted the counterexample and the claim "Theorem 6 can fail".
- (Scope) is now stated as a restriction, with its role: "(Scope) makes Φ a sentence; if it fails, step 1 says 'does not apply'." (Section 10, *Other limits*.)
- Step 1 checks (Scope): "If (Scope) fails, stop: does not apply." The script does the same, and regression 3 prints "(Scope) fails ... the procedure does not apply".
- I did not add the "add the writers to N" extension. The script does not implement it, and its correctness for (Cap) is not proved.

**A-2, semi-decision procedure: ACCEPTED (option (a)).** It is now a labelled *Remark (semi-decision, H = 0)* in Section 10.
- Pieces are defined: f_i^θ is a first-match list of at most B pairs (region, affine map of in(i)). Each region is a conjunction of at most B atoms or negated atoms over in(i). The default value is 0.
- The procedure enumerates pairs (B, rational θ). For fixed θ, the closed formula ∀(A_P→G_P)[out(i):=f_i^θ(in(i))] is linear and is decided by Lemma 6. Tarski's theorem and the irrational-witness gap are gone.
- Halting: if an acceptable delegation exists, (K) and Lemma 6(b) give rational strategies of this form, so the enumeration halts. Otherwise it runs forever, and no bound on B is known.
- The note that for H > 0 the defining formula of a strategy is in general not in L was cut for space. The remark is stated for H = 0 only.

**A-3, script step 9 and (V2): ACCEPTED.**
- The engineer changed the script to compute step 9 from the final sets and to check and print (V2). The relay block now shows "(V2) after sweep: True".
- Regression 2 (A_P = d ≥ r, G_P = d ≥ r − 1) is in the script output with (V2) true and both assumptions true.
- I deleted the disclaimer sentence and the relay step-9 remark about the in-pass formula.

**A-4, script decoding: ACCEPTED.**
- The engineer changed the script's κ to the recursion of Lemma 8, starting from the latest earlier component. It asserts that seeds and swept contracts are over the component's ports.
- Regressions 1a (C1..C4, seed d = g1) and 1b (X/Y/Z/W, seed d = z1) print true.
- Lemma 8 now states the recursion explicitly: w_{l+1} := w_l if w_l ∈ ports(i_{l+1}), else σ_l(w_l).

**A-5, candidate order: ACCEPTED.**
- Section 4 now states the order in the exact terms of the `witness` docstring:
  - five tiers: midpoints of all pairs of distinct bounds; bounds; bounds plus one; bounds minus one; 0;
  - within a tier: constants by increasing absolute value, a negative constant before the positive one of the same absolute value;
  - then non-constant candidates in ASCII order of the canonical printing (alphabetical variables, then the constant, reduced fractions, joined by ' + ', with the docstring's example);
  - a candidate equal to one met earlier is dropped.
- The end of Section 6 says that any equivalent formula may be used in steps 4, 8 and 9. The theorems do not depend on the choice; the witnesses do, because T is read from the atoms. The script uses Z3's qe2 output, simplified and checked equivalent.
- Section 9 pins z3-solver==5.3.1.0, gives the install command, and quotes the printed version line.
- The relay example in Section 4 lists T exactly as the script's trace does: r, r−1/2, r+1/2, r+3/2, r−3/2, 0, with the duplicate dropped.
- The disjunctive term was dropped for space (see the top of this file). It can now be derived from the stated order.

**A-6, "a true Φ proves nothing" needs an example: ACCEPTED.** Section 10 now contains the reviewer's example:
- unconnected A: s1 ↦ a and B: s2 ↦ b; A_P = true; G_P = |a−b| ≤ 1/2 ∧ |b−s2| ≤ 1/2;
- for the ordering B, A, (Pure) holds and ∀s2∃b∀s1∃a G_P is true;
- strategies a = f(s1), b = g(s2) would make g both bounded (fix s1) and unbounded, so none exists; here (Cap) fails.
- The "Why one sentence" paragraph points to this example.

**A-7, proof of step 3's claims: ACCEPTED.** Step 3 now gives both arguments:
- "a writer of v would be in N before i_k, so v is an environment variable";
- "Φ is a sentence: a port of i_k is an output (in Y_k, or in edge_k, excluded by (Pure)), a fresh input, or a port of an earlier component, so by (Scope) all of A_P → G_P is quantified."

**A-8, (E) is redundant: ACCEPTED.** After Definition 7: "(E) follows from (Cap): i_k ∈ N writes a variable, which lies in priv_k if i_{k+1} reads none." I kept (E) in the definition, because it names the chain shape and the script checks it. The fan-in sentence that cited (E) was removed.

**A-9, (Info) is stronger than needed: ACCEPTED (as a note).**
- After Definition 7: "The proofs use (Info) only through: for H > 0, no i_k with k ≥ 2 reads an environment variable that no earlier component reads."
- The stronger form stays in the definition, because the script checks the stronger form. Stating the weaker one as the definition would put the document and the code out of step again.

**A-10, hypotheses omitted: ACCEPTED.**
- The overview now says the method is complete only on chains, where a false sentence proves none exists, and elsewhere can only refute.
- Step 1 checks (Scope).
- Step 2 says "If none, stop: does not apply (Section 10 still offers a refutation test)". The refutation is the corollary on Φ° in Section 10, which applies to any topological ordering.

**A-11, unproved meta-claims: ACCEPTED.**
- "No contract operation expresses this" is now: "[accepting whatever arrives] depends on which ports are inputs, a distinction no operation uses". This can be checked against the four definitions.
- "Contract operations cannot single one out" is gone. It is replaced by an explicit computation: from trivial others, the relay gets Radio (|r| ≤ 1, |r| > 1) and Display (true, false), neither receptive. Then: "Each operation returns one determined result, so the algebra needs non-trivial contracts to start from, and none is best."
- I did not use the reviewer's word "monotone": the quotient is antitone in its second argument.

**A-12, connection to the algebra: ACCEPTED.**
- Lemma 1(b) proves that ρ_W(C) is the ≼-greatest contract over W refining C.
- Theorem 11 now states: "With the final sets, (A_{i_k}, S_{i_k}) = ρ_{ports(i_k)}(P / ⊗_{j≠k}(true, S_{i_j}))." The proof ends with S ≡ S*, so the claim is step 8's identity plus the definition of step 9.
- Step 8 completes the identity: S_P ∨ ¬R_k = ¬A_P ∨ G_P ∨ ¬R_k ≡ R_k → G_P, as ¬A_P ⊨ ¬R_k.

**A-13, κ well defined: ACCEPTED.** Lemma 8 fixes the largest j with v ∈ ports(i_j), and the recursion is explicit.

**A-14, family maximality: ACCEPTED.** Theorem 11: no formula strictly weaker than S_{i_k} works, "nor does any family weaker in every set and strictly in one". The proof gives the reduction: restore all but one set, since (V1) survives shrinking.

**A-15, the (K) check: ACCEPTED.**
- Section 9: the script's sentence ∀in(0)∃out(0)···∀in(H)∃out(H) S_i is "(K) through choice functions, made explicit by Lemma 6(b)".
- The proof of Theorem 9 opens with the semantics: "Φ is true iff functions choosing each existential timed variable from the earlier ones make A_P → G_P hold for all universal values."

**A-16, L underspecified: ACCEPTED.**
- TRUE and FALSE are the atoms 0 ≤ 0 and 0 ≤ −1.
- "A formula with quantifiers is not in L, but by Lemma 6(a) it is equivalent to one; below it always stands for that formula."
- E_k(t) and Y_k(t) are sets of timed variables.

**A-17, gloss of Proposition 3: ACCEPTED.** "In (a) the component given (true, false) has no implementation; in (b) each component with an input forbids all input histories but one."

**A-18, Fourier–Motzkin notation: ACCEPTED.** A "case" is "a conjunction of atoms and negated atoms". The relation is now ◁_{ℓu}, strict iff either bound is strict.

**A-19, cost bound: ACCEPTED.** "Lemma 6(a) multiplies the n atoms by at most n(n−1)/2+3n+1 per elimination." The bound is stated for the lemma's elimination, and n counts all atoms.

**A-20, the fork corollary: ACCEPTED.** Section 10, *Forks*: "under (Scope), Φ°, built as in step 3 from any topological ordering but with Y_k(t) all outputs of i_k at t, is true if an acceptable delegation exists (proof of Theorem 9, without (Pure))." This is citable on its own and no longer leans on Theorem 9's (Pure) hypothesis.

---

## Reviewer B (clarity)

**B-1 (BLOCKING), "only contract operations": ACCEPTED.**
- New Lemma 1 (adjunction, localisation), with two-line proofs.
- New paragraph *What the algebra alone gives* (end of Section 3):
  - With all contracts but C_i fixed, the best C_i is ρ_{ports(i)}(P / ⊗_{j≠i} C_j): one quotient and one projection.
  - From trivial others, the relay gets Radio ρ_{r,m}(P) = (|r| ≤ 1, |r| > 1), which forbids every admissible input, and Display ρ_{m,d}(P) = (true, false). Neither is receptive.
  - "Steps 2 to 7 select one acceptable delegation; this is the only part that is not a contract operation, unavoidable by Proposition 5, and Proposition 2 checks its result. Steps 8 and 9 use only quotient and projection."
- Steps 8 and 9 are each identified as a projection of a quotient, and Theorem 11 states the equality for the output.

**B-2 (BLOCKING), rationale for Φ: ACCEPTED.**
- New paragraph *Why one sentence with one quantifier order* (Section 5), before Definition 7. It explains:
  - the exact question (one causal strategy per component, each reading only its own inputs);
  - why a ∀∃ prefix over-grants, pointing to the A-6 example;
  - how (E) and (Cap) let i_k copy what i_{k+1} cannot see, so knowledge is nested along the list (hence the name);
  - (Info): with time first, i_1's choice at time 1 follows i_2's inputs at time 0, and (Info) stops i_2 reading the environment, which i_1 would be granted unseen;
  - (Pure): edge values are copies, not choices, so they are not quantified and must stay out of the query, which the copies could falsify;
  - in the relay, "Radio chooses nothing; Display knows r via m = r".
- Step 3 adds: "The chooser of Y_k(t) is granted every earlier value, more than i_k sees; on a nested ordering each is seen via forwarding or removed by step 6 (Theorem 10)."
- The failure (E) and (Cap) prevent is the A-6 example.

**B-3, the reason for the candidates: ACCEPTED.** Section 4 opens with **Idea**: atoms compare y with its bounds, so φ is constant between consecutive bounds; it suffices to test each bound, a point between each two, points beyond the outermost, and one point if there is no bound. The definition of T follows.

**B-4, the witness is ambiguous: ACCEPTED.**
- The region of c is π_c := φ[y:=c] ∧ ⋀_{c' before c} ¬φ[y:=c'], and π₀* covers "none".
- The witness s_y is the rule "on π_c take c; on π₀* take 0".
- φ[y:=s_y] is defined as ⋁_c (π_c ∧ φ[y:=c]) ∨ (π₀* ∧ φ[y:=0]).
- The defining formula ⟦y = s_y⟧ is ⋁_c (π_c ∧ y = c) ∨ (π₀* ∧ y = 0).
- The exact order is as in A-5. Non-canonicity is stated at the end of Section 7: the output "depends on the orders of T, the prefix and the sweep".

**B-5, three elimination methods: ACCEPTED.**
- Lemma 6 is THE procedure. The Fourier–Motzkin paragraph is headed "(for hand computation; witnesses always come from (b))".
- The end of Section 6 says that any equivalent formula of L may be used, and that the script uses Z3's qe2 output, simplified and checked equivalent.

**B-6, quantified formulas versus L: ACCEPTED.** Section 2 now says that a quantified formula is not in L but, by Lemma 6(a), is equivalent to one, and always stands for that formula below.

**B-7, operations in words: ACCEPTED.**
- Words are given for refinement, composition (side by side; both promises; both assumptions unless a promise is broken), quotient (what a component must meet so that, next to one meeting C', the pair meets C) and projection (what can be said over W).
- Adjunction and localisation are Lemma 1.
- Step 8 completes the identity (see A-12).

**B-8, "graph" used for two things: ACCEPTED.** "Architecture graph" is used for the system throughout. For s_y it is now "the defining formula ⟦y = s_y⟧", also in steps 6 and 7, Section 9 and the Remark.

**B-9, the overview: ACCEPTED.** The plain-words paragraph now:
- uses the relay as its example;
- describes the three moves with relay values: m = r; d = r, decoded to d = m; enlargement "until none can be enlarged alone";
- states the class restriction and the refutation-only status outside it.

**B-10, step 6 well defined: ACCEPTED.**
- Step 6 now works on the list of (region, value) pairs. It notes that z(s) has s < t and occurs only in regions, and replaces each atom α mentioning z(s) by ⋁_{(π',c')} (π' ∧ α[z(s):=c']). It repeats with a termination argument.
- Step 4 states the fact step 6 relies on: "Later variables are already eliminated, so s_y mentions only earlier ones."

**B-11, script step 9: ACCEPTED.** Script fixed (see A-3), disclaimer removed, new output quoted.

**B-12, semi-decision procedure: ACCEPTED.** See A-2. "Branch" is replaced with "Strategies reading non-nested sets of values fit no single order of ∀, ∃."

**B-13, density and legibility: ACCEPTED in part, REBUTTED in part.**
- Accepted:
  - the verbatim block is at 8pt (it was 6.2pt);
  - the script labels are now (V1), (V2) and "necessity theorem", so the translation key is gone;
  - the "(K) vs (R)" example was folded into one clause;
  - "Steps 4, 8, 9 eliminate ..." was dropped.
- Rebutted: margins (0.75in) and the run-in Section 8.
  - The brief sets two binding constraints: five pages, and every listed derivation written out. The brief also asks that "every elimination" of the relay be written out; Section 8 does that, with bold step numbers matching the step list one to one.
  - Turning Section 8 into a list costs about 6 lines. Widening margins to 1in costs about 15% of the text width. Either would force dropping required derivations, such as the Fourier–Motzkin case computations, or B-1/B-2 material.
  - 0.75in is an ordinary margin for a 10pt technical note; it is not a squeeze.
- Not done: collapsing whitespace in the script's `fmt()`. The script belongs to the engineer and I am restricted to complete.tex and this file. The block reproduces the output exactly, as reviewer C requires.

**B-14, modelling assumptions: ACCEPTED.** "We assume: (i) discrete time t ∈ {0,…,H}; (ii) no directed cycle; (iii) zero delay: an output at time t may depend on inputs at time t (Section 10 discusses delays)."

**B-15, step 3 wording: ACCEPTED.**
- E_k(t) and Y_k(t) are sets of timed variables, and the step gives the reason fresh inputs are environment variables.
- "Terminal outputs" is defined as "not on the edge to i_{k+1}". I kept the name because the script prints "terminal outputs Y_k".

**B-16, index clash: ACCEPTED.** Bounds are b_1..b_n with pair indices a, a' (½(b_a + b_{a'})), not i, j.

**B-17, formulas as sets, implementations, "environment": ACCEPTED.**
- "A formula is identified with the set of traces satisfying it."
- "An implementation is any set of traces inside S."
- "Environments" is replaced by "context".
- Saturated has a gloss: "the guarantee allows every trace violating the assumption".

**B-18, semantics of Φ: ACCEPTED.** See A-15; the "game" wording is gone.

**B-19, the fork use of Theorem 9: ACCEPTED.** See A-20.

**B-20, relay step 7: ACCEPTED.**
- The Section 4 example now says that π_r ≡ TRUE, so ⟦d = s_d⟧ ≡ (d = r).
- Relay step 7: "⟦d = s_d⟧ ≡ (d = r) and κ_2(r) = m, so δ_2 gives d = m."

**B-21, the "(K) by Lemma 5" legend: ACCEPTED.** The sentence is about S_i, not G, and the legend reads "(K) through choice functions, made explicit by Lemma 6(b)".

**B-22, mapping the printed sweep contracts: ACCEPTED.** Section 9: "the sweep's G is S_{i_k} in conjunctive normal form (clause order may vary with Z3's version)". The CNFs are those of the Section 8 formulas, which A, B and C each verified as equivalent.

**B-23, disjunctive example not checkable: ACCEPTED (resolved by removal).**
- The order is now fully specified (A-5), so the term can be derived. I had added such a derivation, and it agrees with the new output (m−3/8, 0, m+3/8).
- The instance was cut for space (see the top of this file).

**B-24, "as far as correctness allows": ACCEPTED.** Now "until none can be enlarged alone".

**B-25, Lemma 8 and the decoding: ACCEPTED.**
- Largest j.
- A plain-words sentence: "So every value an earlier component saw arrives as a copy on an input κ_k(v) of i_k."
- Prefix notation δ_k(φ) is used throughout.

**B-26, S_j versus S_{i_j}: ACCEPTED.** Step 8 uses S_{i_j} and notes "outside N: TRUE".

**B-27, the delay argument: ACCEPTED.** "In the (m(t+1), r(t))-plane it gives a finite union of products, and a product inside the line is a point". So finitely many products cannot fill the line.

**B-28, the physical meaning of edge variables: ACCEPTED.** "Other edge variables are unconstrained (their values need have no physical meaning)." I placed it at the definition of F_k, where edge values are assigned.

**B-29, the gloss of Proposition 3(a): ACCEPTED.** See A-17.

---

## Reviewer C (reproducibility)

**M1, (Scope) not checked: ACCEPTED.** The script checks it (engineer), step 1 states the check, and the wrong counterexample is gone (A-1). Regression 3 prints "does not apply".

**M2, decoding: ACCEPTED.** See A-4. Regression 1b is the reviewer's X/Y/Z/W instance, with seed d = z1.

**M3, step 9 and (V2): ACCEPTED.** See A-3. The verbatim block now includes "(V2) after sweep: True" and "receptive & causal after sweep (every component): True". The two disclaimer sentences are deleted, and the block was regenerated from the script, not edited by hand.

**m1, results.tex at m = −1/8: ACCEPTED.** The engineer fixed results_report.py; results.tex now reads −1 ≤ m < −1/8. complete.tex no longer quotes the table.

**m2, substring loop in step 6: ACCEPTED.** The script fix compares symbols by term traversal (regression 4). Step 6 in the document is defined on terms and regions, not strings (B-10).

**m3, orders that determine the output: ACCEPTED.**
- Candidate order: Section 4, as in A-5.
- Step 2: "Enumerate the permutations of N, sorted by name, in lexicographic order; take the first that is topological and nested."
- Step 3: "each set in port declaration order".
- σ_k pairs the two alphabetically sorted lists.

**m4, elimination granularity: ACCEPTED.** End of Section 6: any equivalent formula of L may be used in steps 4, 8 and 9, and the script uses the qe2 output, simplified and checked equivalent. Calling qe2 on a whole block gives an equivalent formula, so it is covered. Lemma 6 is used for witnesses.

**m5, version dependence and an exact quote: ACCEPTED.**
- Section 9 gives `uv venv && uv pip install -p .venv/bin/python z3-solver==5.3.1.0` and says clause order may vary with Z3's version.
- The quoted block is "the first 21 lines", starting with "z3 version 5.3.1" and the separator line.
- The note that the fan-in case prints two blocks was cut for space. The fan-in case is no longer described in the document.

**m6, printed seed form: ACCEPTED.** "A seed prints as y == If(...), i.e. ⟦y = s_y⟧."

**m7, only (V1) checked after the sweep: ACCEPTED.** The script now prints (V1), (V2) and receptive & causal after the sweep (engineer), and the block quotes all three.

**m8, fan-in description incomplete: ACCEPTED (resolved by removal).** For space, the document only says "The script tries B = 1"; the graph is no longer described, so nothing in it is incomplete.

**m9, labels from other documents: ACCEPTED.** The script now prints "(V1)", "(V2)", "(necessity theorem)" and "the procedure does not apply", and the mapping sentence is gone. "Phi (linearised sentence)" remains a script label; it is printed next to the Φ of step 3 and needs no key.

**m10, README: ACCEPTED (already done).** README.md now names `docs/complete.pdf` and `.venv/bin/python scripts/delegate.py`.

**m11, "nine clauses" in results.tex: ACCEPTED (already done by the engineer).** The text now says the clause count depends on the Z3 version and is not reproduced. complete.tex never used it.

**m12, in(t)/out(t) clash: ACCEPTED.** "(values at time t of in(i), out(i))".

**m13, format: ACCEPTED in part, REBUTTED in part.** Same as B-13: the verbatim is at 8pt, and the margins stay at 0.75in for the reasons given there.
