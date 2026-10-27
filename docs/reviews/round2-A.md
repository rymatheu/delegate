# Round 2, Reviewer A (mathematical rigor): docs/complete.tex (revised)

## What I checked

I re-read the whole document. I re-ran `.venv/bin/python scripts/delegate.py`:
- it exits 0;
- lines 1–21 of the output are identical to the verbatim block;
- all regression verdicts print True.

Scratch checks are in `/private/tmp/claude-501/-Users-ryan-Research-delegate/547e050f-c29a-418f-816a-16412bc752a6/scratchpad/`, in `r2.py` and the round-1 scripts.

## Part 1. Status of the round-1 items

| # | Status |
|---|---|
| A-1 | **Fixed.** The wrong counterexample is gone. (Scope) is a stated restriction, and its role ("makes Φ a sentence") is correct. Step 1 and the script check (Scope); regression 3 prints "does not apply". |
| A-2 | **Fixed.** The rational enumeration gives a correct semi-decision procedure for H = 0, and pieces are defined. Two small gaps remain; see new item 6. |
| A-3 | **Fixed.** Step 9 is computed from the final sets and (V2) is printed. In regression 2, A_Radio = A_Display = true and (V2) holds, matching my round-1 Z3 result. |
| A-4 | **Fixed.** Regressions 1a and 1b give seeds d = g1 and d = z1. These agree with Lemma 8 as now stated. |
| A-5 | **Fixed.** The tiers and the within-tier order in Section 4 match the `witness` docstring. For the relay, the T printed by `DELEGATE_TRACE=1` is exactly the document's list. One wording slip remains; see new item 4. |
| A-6 | **Fixed.** I re-verified the A/B example with Z3: Φ for the ordering (B, A) is true, and the boundedness argument is correct. See new item 7 for a related remark. |
| A-7 | **Fixed.** Both arguments in step 3 are correct. |
| A-8 | **Fixed.** The note "(E) follows from (Cap)" is correct. |
| A-9 | **Fixed.** The note is correct. The weaker condition it states is exactly what step 3 and Theorem 10 use. |
| A-10 | **Fixed.** One small residue; see new item 8. |
| A-11 | **Partly fixed.** "No operation uses [the input/output distinction]" can now be checked against the definitions. The replacement claim "unavoidable by Proposition 5" is not justified; see new item 1. |
| A-12 | **Fixed.** Lemma 1 is correct (I checked part (a) with Z3 over an uninterpreted sort, under saturation; no counterexample). The step 8 identity is complete. Theorem 11's last claim is correct. |
| A-13 | **Fixed.** A wording point remains; see new item 5. |
| A-14 | **Fixed.** The reduction argument (restore all sets but one) is correct. |
| A-15 | **Fixed.** |
| A-16 | **Fixed.** |
| A-17 | **Fixed.** |
| A-18 | **Fixed.** |
| A-19 | **Fixed.** The count C(n,2) + 3n + 1 matches the five tiers. |
| A-20 | **Fixed.** The Φ° corollary is correct: with edge outputs quantified, the proof of Theorem 9 needs no (Pure). |

## Part 2. Checks of the new statements

These new statements are all correct:

- **Lemma 1 (a) and (b).** Both proofs are correct.
  - In (a), the left side reduces to A∧S1∧S2 ⊨ A1∧A2∧S using ¬A ⊨ S.
  - On the right side, A∧S2 ⊨ A1 is equivalent to A∧S1∧S2 ⊨ A1, using ¬A1 ⊨ S1.
  - In (b), C' ≼ C if and only if C' ≼ ρ_W(C) for every C' over W. Together with ρ_W(C) ≼ C, this makes ρ_W(C) the greatest.
- **"What the algebra alone gives".**
  - The adjunction statement is correct.
  - The relay values are correct (Z3): ρ_{r,m}(P) = (|r| ≤ 1, |r| > 1) and ρ_{m,d}(P) = (true, false).
  - The non-receptiveness of both is correct.
  - The concluding sentence is a separate matter; see item 1.
- **Rationale for Φ, (E), (Cap), (Pure), (Info).**
  - It is consistent with the proofs.
  - At a single time, the prefix grants Y_k(t) only E_j(t) and Y_j(t) for j ≤ k. Forwarding delivers these.
  - Across times, the extra grants are E_j(s) and Y_j(s) with j > k and s < t. (Info) removes the first and step 6 removes the second.
- **(Scope) and the sentence property of Φ.** Correct.
- **Witness by regions; φ[y:=s_y]; the defining formula; step 6 on (region, value) pairs.**
  - All correct.
  - The default pair (π₀*, 0) must be among "the pairs of s_{z(s)}" in step 6. It is, given the definition of s_y as a list.
- **"Any equivalent formula of L may be used".**
  - Correct for the theorems, because Lemma 6 applies to any formula of L.
  - See item 3 for the script.
- **Theorem 11, "each output contract equals the projected quotient".** Correct, by S_{i_k} ≡ S* and the definition of step 9.
- **The A/B example and the semi-decision remark.** Correct, up to items 6 and 7.

## Part 3. Issues

1. **MAJOR. "Unavoidable by Proposition 5" does not follow.**
   - Location: Section 3, end: "this is the only part that is not a contract operation, unavoidable by Proposition~\ref{prop:nogreatest}". Also: "Each operation returns one determined result, so the algebra needs non-trivial contracts to start from, and none is best."
   - What is wrong:
     - Proposition 5 shows that there is no greatest acceptable delegation. It does not show that no sequence of contract operations yields some acceptable delegation.
     - "Returns one determined result" does not imply this either. Symmetry arguments alone do not settle it. For example, Radio (true, m = r+2 ∨ m = −(r+2)), Display (true, d = |m| − 2) is acceptable and invariant under m ↦ −m (I checked this by hand).
   - Fix: the claim is true for the relay and has a short proof, so prove it.
     - The four operations never introduce a variable: every formula they produce mentions only variables of their arguments.
     - So every contract obtained from P and constant contracts mentions only r and d.
     - Then Radio's S does not mention m, and (R) forces it to hold for every r. Display's S mentions only d, and (R) gives some d0 in it.
     - Then (V1) would need |d0 − r| ≤ ½ for every r ∈ [−1, 1], which is impossible.
     - Hence, in the relay, no acceptable delegation is obtained from P by contract operations alone, and a selection step is needed.
     - Replace "unavoidable by Proposition 5" with this argument. Cite Proposition 5 only for "and no choice is best".

2. **MINOR. "Until none can be enlarged alone" is proved only in the (V1) sense. The algebra sense also holds, but is not stated.**
   - Location: Section 1 and Theorem 11.
   - The "algebra alone" paragraph defines the best C_k given the other contracts as ρ(P / ⊗_{j≠k} C_j). These are the full output contracts, with their assumptions.
   - Theorem 11 states the identity with (true, S_{i_j}).
   - The two coincide:
     - The output is valid, so by Lemma 1, C_k ≼ ρ(P / ⊗_{j≠k} C_j). This gives S_{i_k} ⊨ S_best.
     - Also S_best = ∀X(R_k → G_P ∧ ⋀_{j≠k} A_{i_j}) ⊨ S_{i_k}.
     - The two assumptions are both ∃X R_k.
   - Fix: add this one-line argument to Theorem 11. It makes the overview's phrase a theorem in the algebra's own sense.

3. **MINOR. The script does not check that the `qe2` output is a formula of L.**
   - Location: end of Section 6: "The script uses Z3's \texttt{qe2} output, simplified and checked equivalent".
   - The theorems need a formula of L, with one time per atom: Lemma 6(c) and the Language part of Theorem 10 depend on it. The script checks only equivalence.
   - In practice `qe2` combines atoms of the eliminated variable's time, but this is not asserted.
   - Fix: add an assertion in `qe` that every atom of the result mentions one time. Alternatively, write "checked equivalent and checked to have one time per atom".

4. **MINOR. The relay candidate list drops two duplicates, not one.**
   - Location: Section 4 Example: "($r+\frac12-1$ is a duplicate)".
   - r − ½ + 1 = r + ½ in tier 3 is also dropped, as the printed list shows.
   - Fix: "(r − ½ + 1 and r + ½ − 1 are duplicates)".

5. **MINOR. Lemma 8 wording.**
   - "(largest such j)" sits at the end of the conclusion. It should qualify the definition of κ_k(v): the claim holds for every j, while κ_k is defined with the largest j.
   - The proof also uses the invariant w_l ∈ ports(i_l) without stating it. Add: "by induction w_l ∈ ports(i_l)".

6. **MINOR. Two small gaps in the semi-decision remark.**
   - (i) The substitution [out(i) := f_i^θ(in(i))] must be done in topological order, so that the formula mentions only environment values. Say so.
   - (ii) The strategies from Lemma 6(b) have regions π_c that are Boolean combinations of atoms, not conjunctions. Add: "writing each region in disjunctive normal form; the regions are disjoint, so first-match order is immaterial". Then they fit the "conjunction of at most B literals" family for some B.

7. **MINOR. The A/B example is refuted by Theorem 9 with the other ordering.**
   - (A, B) is also topological with (Pure), and ∀s1∃a∀s2∃b G_P is false (Z3).
   - The example still shows that a true Φ for one ordering proves nothing. But the procedure stops with "does not apply" when a refutation is available.
   - Fix: suggest in step 2, or in *Forks*, that Φ° (or Φ, when (Pure) holds) should be decided for every topological ordering, since any false one refutes. Or note that the example is refuted this way.

8. **MINOR. The overview omits (Scope).**
   - Location: Section 1: "this is complete, and a false sentence proves none exists".
   - Fix: add "under (Scope)", or "when every query variable is a port of a relevant component".

9. **MINOR. The delay argument lost "with the other values fixed".**
   - Location: Section 10: "in the $(m(t+1),r(t))$-plane it gives a finite union of products".
   - This is true only for the section with all other timed variables fixed. Restore that phrase.
   - Add "so finitely many cannot fill the line"; the rebuttal says it is present, but it is not in the .tex.

## Verdict

**Revise (minor).**

All twenty round-1 items are resolved, and the new mathematics is correct: Lemma 1, the witness by regions, step 6, the Φ° corollary, the semi-decision remark and Theorem 11's identity. The script now matches the document on every instance I tested.

One MAJOR item remains (item 1). The justification "unavoidable by Proposition 5" is a non sequitur. A three-line proof, given in item 1, replaces it.

The minor items are wording, or one-line additions.
