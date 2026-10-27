# Round 1, Reviewer A (mathematical rigor): docs/complete.tex

Scope of this review: every definition, lemma, theorem and proof in `docs/complete.tex`. I checked each
claim by hand. Where a claim could be tested I used Z3, with scratch scripts under
`/private/tmp/claude-501/-Users-ryan-Research-delegate/547e050f-c29a-418f-816a-16412bc752a6/scratchpad/`
(`misc.py`, `v2check.py`, `decodebug.py`, `fork_phi.py`). Every counterexample below is also written out
in full here, so it can be reproduced without those files.

## What I checked and found correct

These results hold as stated. I list them so the revision does not touch them unnecessarily.

- The closed form of the n-fold composition, and the proof of Proposition 1 (validity conditions (V1), (V2)). Both are correct.
- Every operation result is saturated. This is correct for composition, quotient and projection.
- Proposition 2 (a) and (b) are correct. The (R)-versus-(K) example at H = 1 is correct (Z3: receptive true; causal sentence ∀m0∃d0∀m1∃d1 false).
- Proposition 3 (no greatest solution) is correct (Z3: D and D' satisfy (V1); the union fails at r=1, m=-1, d=-1).
- Lemma 4 (elimination with witnesses) is correct.
  - The cell argument is exhaustive: points, open gaps, and two rays, or all of ℝ when r = 0.
  - Every cell contains a candidate. A midpoint ½(b_i+b_j) with i≠j exists for each pair of consecutive distinct bound values.
  - The ∀ case follows from ¬φ, which has the same atoms.
  - Value terms are affine at time t only, so the graph formula is in L.
- The case/Fourier–Motzkin paragraph is correct up to the notation in item 18.
- Lemma 5 (carriers) is correct up to well-definedness (item 13). The decoding statement is correct.
- Theorem 6 (necessity) is correct under (Scope) and (Pure) with any topological ordering.
  - The prefix gives each chooser at least what the component sees, which is the direction necessity needs.
  - The proof uses only (V1) and (K).
- Theorem 7 (soundness) is correct.
  - Substituting later witnesses terminates, because each replaced variable is strictly earlier in the prefix.
  - The replaced z(s) have s < t, so they occur only in region conditions. The "one time per atom" argument is right.
  - Under (Info), the only values granted to i_k but not seen by it are later components' existential outputs, and step 6 removes those.
  - The (V1) induction over the prefix is correct: x(y) = s_y(x) by induction, then x ⊨ ψ_l for all l.
- Theorem 8 (sweep), in the form the draft now states it, is correct.
  - Step 8 yields the weakest S over ports(i_k) satisfying (V1) given the current other sets.
  - The sets only grow, and (R)/(K) are inherited.
  - The maximality argument (S_{i_k} ≡ S* for the final others) is correct.
  - (V2) and saturation for the step-9 assumptions, recomputed from the final sets, are correctly proved. Z3 confirms the draft's step 9 on the instance of item 3.
- The relay worked example is correct in every step. Z3 confirms S_Radio, S_Display (both cases of the Fourier–Motzkin computation), A_Display = |m| ≤ 3/2 and A_Radio = |r| ≤ 1.
- The verbatim script block matches the current output of `.venv/bin/python scripts/delegate.py` line for line.
- The disjunctive-query piecewise term, the refutation and the fan-in output match what the script prints.
- The delay argument (a formula of L, with the other values fixed, defines a finite union of rectangles in the (m(t+1), r(t))-plane) is correct.

## Issues

1. **BLOCKING. The counterexample offered for dropping (Scope) is not a counterexample to Theorem 6.**
   - Location: Section 9, "Other limits": "Without (Scope), Theorem~\ref{thm:nec} can fail. ... yet $\Phi$ with $\forall o$ fails at $o=-1$, $r=2$."
   - What is wrong:
     - Without (Scope), Φ as defined in step 3 is not a sentence: o(0) is free. So Theorem 6 cannot "fail"; its conclusion is undefined.
     - The draft then closes Φ universally in o. But o is an output of Q, chosen by Q's strategy, not by the environment. The proof of Theorem 6 itself treats outputs of components outside N existentially ("the outputs of components outside N by their strategies").
     - With the correct quantifier, the sentence is true. Z3: ∃o ∀r ∃d (A_P → G_P) is true, while ∀o ∀r ∃d is false.
     - So the example shows only that quantifying an output universally is wrong.
     - It does not show what (Scope) is for. The reason for (Scope) is that N, defined from G_P alone, can omit writers of A_P variables.
     - For environment variables read by no component, universal closure placed anywhere (for example innermost) keeps Theorem 6 true, because no strategy depends on them.
   - Fix: replace the paragraph with a correct account:
     - "Without (Scope) the matrix has timed variables that are not in the prefix, so Φ is undefined."
     - "Variables of A_P written by components outside N can be handled by adding their writers and those writers' ancestors to N." Note that in the example Q then breaks (Cap), so the procedure reports "does not apply" instead of a wrong answer.
     - "Environment variables read by no component may be quantified universally innermost without affecting Theorem 6."
     - Or simply state (Scope) as a restriction and delete the "can fail" claim.

2. **MAJOR. The semi-decision procedure for forks is not defined precisely enough to check, and its proof has a gap.**
   - Location: Section 9, "Forks": "take piecewise-affine $f_i$ with at most $B$ pieces and unknown coefficients $\theta$, and decide $\exists\theta\,\forall(\text{environment})\ldots$ ... A rational witness $\theta$ gives the acceptable delegation".
   - What is wrong:
     - "B pieces" is not defined: how are the regions parameterized, and how are strict and non-strict boundaries handled? Without that, the claim that the Lemma-derived strategies belong to the family for some B cannot be checked. Those strategies have regions that are Boolean combinations of half-spaces.
     - Tarski's procedure decides the truth of ∃θ. It does not produce a rational θ. A true sentence whose witnesses are all irrational gives strategies whose graphs are not in L, so the procedure as written can stop without an output in L.
     - The draft does not say what happens in that case, so it has not shown that the procedure is a semi-decision procedure that returns a delegation in L.
   - Fix (either one):
     - (a) Enumerate pairs (B, θ ∈ ℚ^m). For a fixed rational θ the check ∀env (A_P → G_P)[out := f^θ(in)] is a sentence of linear real arithmetic, decidable by Lemma 4, so Tarski is not needed. Combined with the draft's argument that a rational piecewise-affine solution exists whenever a delegation exists, this is a correct semi-decision procedure.
     - (b) Keep Tarski, and add a proof that truth at level B implies a rational witness at some level B' ≥ B.
   - In both cases, define the piece parameterization explicitly. For example: each piece is a conjunction of at most B literals a·in ⋈ c with unknown a and c, and ⋈ ∈ {≤, <}.

3. **MAJOR. The script does not implement step 9, and its version can violate (V2).**
   - Location: Section 6, after step 9: "The script computes $A_{i_k}$ during the pass of step 8, with the others as they are then; Section~\ref{sec:relay} shows that for the relay this is the same formula." Also Section 8 (Reproduction).
   - What is wrong:
     - Theorem 8 proves (V2) for assumptions computed from the final sets. The script computes them from the sets current at step k, which can make them too strong.
     - Concrete instance on the relay graph, H = 0: A_P = (d ≥ r), G_P = (d ≥ r − 1). The query's assumption mentions an output, which Section 2 permits ("formulas over V").
       - The script prints seed Radio m = r, Display d = m − 1/2.
       - Its sweep gives Radio: A = (m ≥ r + 1/2), G = true; Display: A = true, G = true.
       - The trace r = m = d = 0 satisfies A_P and every implementation set, but not A_Radio. So (V2) fails, and the composition does not refine P.
       - The script reports "(C1) after sweep: True", because it never checks (V2).
     - The draft's step 9 gives A_Radio = true and is correct (Z3).
     - The two versions agree whenever A_P mentions no output of a component later than i_k. At step k, the sets of earlier components are already final, and later sets that are receptive and causal can always be satisfied by their outputs. That is why the relay agrees.
   - Fix (either one):
     - (a) Make the script recompute the assumptions after the pass, as in step 9, and check (V2) explicitly.
     - (b) Replace the sentence above with an exact statement: "the script's assumptions coincide with step 9 when A_P mentions no output of a component later than i_k; otherwise they may violate (V2)", and do not present the script as an implementation of step 9.

4. **MAJOR. The script's decoding is not the decoding of Lemma 5. On a nested instance it outputs a contract that is not over the component's ports, and after the sweep a guarantee equivalent to false.**
   - Location: Section 8 (Reproduction) and the general claim that the script computes the procedure ("Steps 4, 8, 9 eliminate, steps 6, 7 substitute; nothing else is computed").
   - What is wrong:
     - In the script, `decode` follows a forwarded variable only while it is private to each successive component. It stops as soon as the variable is a port of the next component, even if a later component drops it again.
     - Lemma 5's recursion keeps following it ("if $v\in\ports(i_{j+1})$ let $w:=v$", then recurse).
     - Instance, H = 0: C1: r → e; C2: e → f; C3: e, f → g1, g2; C4: g1, g2 → d; A_P = |r| ≤ 1, G_P = |d − r| ≤ 1/2. This ordering is nested: (Cap) holds as 1 ≤ 1, 0 ≤ 1 and 2 ≤ 2.
       - Lemma 5 gives κ_4(r) = g1, so the seed for C4 should be d = g1.
       - The script prints "contract C4: A = true ; G = d_0 == e_0". But e is not a port of C4.
       - All of the script's checks still print True.
       - The sweep then gives C4 the guarantee (1/2 ≤ d ∧ d ≤ −1/2), which is false. That is the useless delegation of Proposition 2(a), reported as "(C1) after sweep: True".
   - Fix: implement κ_k exactly as in the proof of Lemma 5, and assert that every seed and sweep formula mentions only ports(i_k). The document's mathematics is not affected. But the reproduction section should not imply that the script is correct beyond the printed instances until this is fixed.

5. **MAJOR. The order of the candidates T is not specified well enough to reproduce the printed witnesses.**
   - Location: Section 4: "The candidates $T$ are, in a fixed order"; "(in each group of $T$, smaller constants first)". Section 7, disjunctive query: "the printed term is $m-\frac38$ ...".
   - What is wrong:
     - The witness of Lemma 4(b), and hence the seed, depends on the order of T.
     - The script orders each group as follows: rational constants first, by absolute value; then non-constant terms in the lexicographic order of Z3's printed string. That is why r − 3/8 comes before r − 5/8.
     - The ±1 group is one merged, sorted group, not "b_i+1, then b_i−1".
     - Moreover, after the first elimination, the atoms (hence the bounds) are those of Z3's `qe2` output, not those of Lemma 4(a).
     - So a reader cannot derive the disjunctive term from the text. The brief requires every number to be printed by the script or derived in the text.
   - Fix:
     - State the order exactly.
     - State that the bounds are read from the current formula as returned by `qe2`, and give the Z3 version.
     - Or drop the claim that the term can be derived, and present it only as script output.

6. **MAJOR. "A true Φ proves nothing" is asserted without an example.**
   - Location: Section 9, "Forks".
   - What is wrong: this is the main reason the class is restricted, yet it is unsupported. A two-line example exists and is easy to verify:
     - Components A: s1 → a and B: s2 → b, with no edge between them. A_P = true, G_P = |a − b| ≤ 1/2 ∧ |b − s2| ≤ 1/2.
     - (Scope) and (Pure) hold, so (B, A) is a topological ordering with (Pure).
     - Φ(B,A) = ∀s2 ∃b ∀s1 ∃a (…) is true.
     - No acceptable delegation exists: A would have to track b ≈ s2 without seeing s2. Z3 shows that ∀s1 ∃a ∀s2 ∃b (…) is false, and already that sentence gives A more information than it has.
   - Fix: add the example. It also shows that (Cap) and (E) are needed, not just convenient.

7. **MINOR. The proof of step 3's claim is missing.**
   - Location: step 3, "(\emph{fresh inputs}; they are environment variables)" and "By (Scope) and (Pure) every timed variable of $A_P\to G_P$ is quantified".
   - Fix: add the argument.
     - A writer of an input of an N-component is in N and precedes the reader in the ordering, so a fresh input has no writer.
     - Each port of i_k is then one of three things: an output, which lies in Y_k or in edge_k (and edge_k is excluded by (Pure)); a fresh input, which lies in E_k; or a port of an earlier component, which is handled by induction.

8. **MINOR. (E) is redundant.**
   - Location: Definition of nested ordering.
   - Every component of N writes a variable (it writes a G_P variable or has an outgoing path).
   - If i_k writes nothing that i_{k+1} reads, its outputs lie in priv_k, so (Cap) forces edge_k ≠ ∅. So (E) follows from (Cap).
   - Fix: say so, or drop (E). The fan-in sentence "where (E) fails" should then cite (Cap).

9. **MINOR. (Info) is stronger than the proof needs.**
   - The proof uses only E_k(t) = ∅ for k ≥ 2 when H > 0.
   - (Info) also forbids i_k, k ≥ 2, from reading an environment variable that i_1 already reads.
   - Fix: state the weaker condition, or note that the stronger one is a simplification.

10. **MINOR. The plain-words summary and step 5 omit hypotheses.**
    - Location: Section 1: "If the sentence is false, no such delegation exists." This needs (Scope) and (Pure).
    - Location: step 2: "If none is nested, stop". By the Forks paragraph, a false Φ refutes even then, so stopping discards a valid refutation.
    - Location: step 1. It does not check (Scope), although the input is required to satisfy it. It should output "does not apply" when (Scope) fails.

11. **MINOR. Some meta-claims are unproved.**
    - "No contract operation expresses this" (Section 3) and "contract operations cannot single one out" (after Proposition 3) are not proved.
    - Fix: replace them with provable statements. For example: "(R) and (K) depend on which ports are inputs, which none of the four operations uses"; "the operations are monotone set operations and produce no choice between D and D'".

12. **MINOR. The connection between the output and the contract algebra is not stated.**
    - Location: step 9: "the assumption of the same projected quotient".
    - The quotient in step 8 uses the non-final others. Only through the maximality part of Theorem 8 (S_{i_k} ≡ S*) does the output equal ρ_{ports(i_k)}(P / ⊗_{j≠k}(TRUE, S_j)) with the final S_j.
    - Fix: state this equality as part of Theorem 8, since it is what makes the output a result of contract operations.
    - Also state, with its one-line proof, that ρ_W(C) is the ≼-greatest contract over W that refines C. This justifies calling ρ a projection.
    - In step 8, add the step S_P ∨ ¬R_k ≡ R_k → G_P (because ¬A_P ⊨ ¬R_k).

13. **MINOR. κ_k(v) is not well defined as a function of v.**
    - The recursion starts from a particular j with v ∈ ports(i_j). If v is a port of several earlier components, different starting points can give different carriers.
    - Fix: start from the largest j < k with v ∈ ports(i_j), or say "any choice works".

14. **MINOR. Theorem 8's maximality is stated coordinatewise.**
    - It also implies maximality for inclusion of the whole family: if every S'_j ⊇ S_j, one inclusion is strict, and (V1) holds, then monotonicity reduces this to the coordinatewise case.
    - Fix: say so in one line, since "maximal" is otherwise ambiguous.

15. **MINOR. The equivalence of the script's check with (K) is too terse.**
    - Location: Section 8: "which is (K) by Lemma~\ref{lem:elim}".
    - The equivalence is Skolemization in the prefix order. Lemma 4(b) supplies definable witnesses, so no choice principle is needed. Composing witnesses that depend on earlier outputs gives functions of the inputs alone.
    - Fix: one sentence.

16. **MINOR. The language L is not fully specified, and some wording is loose.**
    - TRUE and FALSE are used but are not formulas of L as defined. Say they are the atoms 0 ≤ 0 and 0 ≤ −1.
    - Quantified formulas (projections, the step 8 and 9 formulas) are not in L until Lemma 4(a) is applied. Say so where contracts are required to be in L.
    - E_k(t) and Y_k(t) are called "the set of values". They are sets of timed variables.

17. **MINOR. Proposition 2(b)'s gloss is not always true.**
    - "Each component forbids all input histories but one" holds only for components with inputs. Say "each component that has an input".
    - In 2(a), "no component can produce any trace" should be "the component given (TRUE, FALSE) has no implementation".

18. **MINOR. The Fourier–Motzkin paragraph's notation is ambiguous.**
    - "a conjunction of atoms (a \emph{case})" should be "a conjunction of atoms and negated atoms".
    - In "$\ell\lhd u$" the symbol ⊲ means a different relation in each conjunct. Write ⊲_{ℓu}, defined as < if either bound is strict and ≤ otherwise.

19. **MINOR. The cost bound applies to Lemma 4(a), not to the computation the script performs.**
    - The script uses `qe2`. Say that the bound is for the lemma's elimination.
    - Also, n should be the total number of atoms in φ. (The count of candidates uses the atoms that contain y, and each substituted copy keeps all n atoms.)

20. **MINOR. The fork sentence does not follow from Theorem 6 as stated.**
    - Location: Section 9: "Theorem~\ref{thm:nec} still refutes (its proof needs only a topological ordering, with $Y_k(t)$ all outputs of $i_k$ at $t$)".
    - Theorem 6 as stated requires (Pure).
    - Fix: state the variant as a corollary (all outputs existential, (Pure) not needed, same proof), so it can be cited.

## Verdict

**Revise.**

The core mathematics is correct and, with the small additions above, complete. That core is Proposition 1, Lemma 4, Lemma 5, and Theorems 6, 7 and 8 in their current form, including the recomputed step 9.

Two claims in Section 9 are wrong or unproved and must be fixed: the (Scope) counterexample (item 1) and the semi-decision procedure (item 2).

The script, which the document presents as its implementation, differs from the procedure in two places that produce invalid output on instances inside the class (items 3 and 4). Either fix the script, or limit the reproduction claims to the printed instances and state the differences exactly.
