# Round 1, Reviewer B (clarity and comprehensibility): docs/complete.tex / complete.pdf

I read the PDF once, linearly, as the author would: a formal-methods researcher who has seen nothing else. Only
after that did I open the sources (docs/existence.tex, docs/algorithm.tex, docs/procedure.tex, SCOPE.md,
scripts/delegate.py) and run the script, to check whether missing material was available.

Checks that pass:
- Length: 5 pages. But see issue 13 on margins and spacing.
- No banned words, no em-dashes.
- The problem is quoted in the author's words. The added sentence about contract operations matches the brief.
- The relay block in Section 9 is byte-identical to what `.venv/bin/python scripts/delegate.py` prints.
- Every elimination in the relay hand computation (Section 8, steps 8 and 9) checks out by hand. It agrees with
  the printed CNF.
- Propositions 1, 2 and 4, Lemma 5, Lemma 7 and Theorems 8 to 10 are correct as far as I could follow them.
  Every problem below is about whether the reader can follow them, and about what is left unsaid.

Severity: BLOCKING = the reader stops or is misled; MAJOR = the reader has to reconstruct something or
distrusts a claim; MINOR = friction.

---

## BLOCKING

### 1. The document never squarely faces the author's requirement "only contract operations"
**Where:** Section 1, "the algebra may use only contract operations". Section 3, after Prop. 4: "contract
operations cannot single one out. The procedure selects one by the witnesses of Section 4".

**Reader:** "I said: decompose ALGEBRAICALLY, using refinement, composition, quotient and projection. Steps 2 to 7
use quantifier elimination with witnesses and forwarding equalities. Neither is a contract operation. Then you
say 'contract operations cannot single one out'. Where is that proved? Proposition 4 says there is no greatest
acceptable delegation. It does not say what the algebra itself produces. Are you doing what I asked, or synthesis
under another name?"

The sources contain exactly the material that answers this, and the document left it out:
- existence.tex: the adjunction `C1 ⊗ C2 ≼ C iff C1 ≼ C / C2`.
- existence.tex, Lemma (localisation): `ρ_W(C)` is the ≼-greatest contract over W that refines C.
- existence.tex, Theorem (closed form of the last component).

With these, the document can show what pure algebra gives on the relay, and why it fails. I computed it.

**Rewrite.** Replace the paragraph after Prop. 4 ("So acceptable delegations ... quotient and projection.") with:

> *What the algebra alone gives.* Two facts hold for the operations of Section 2.
> (Adjunction) `C' ⊗ C'' ≼ C` iff `C'' ≼ C / C'`.
> (Localisation) `ρ_W(C)` is the most permissive contract over W that refines C.
> [One-line proofs, as in existence.tex.]
> So once all contracts but one are fixed, the best contract for the remaining component i is
> `ρ_ports(i)(P / ⊗_{j≠i} C_j)`. This is one quotient and one projection.
>
> Start from nothing, that is, all other contracts `(true, true)`. In the relay this gives:
> - Radio `(|r| ≤ 1, |r| > 1)`. It forbids every admissible input.
> - Display `(true, false)`. It has no implementation.
>
> Neither contract is receptive. So the algebra must be applied to contracts that are not trivial. By Proposition
> 4 there is no best choice of them.
>
> The procedure therefore has two parts. Steps 2 to 7 select one acceptable delegation. This selection is the
> only step that is not a contract operation, and the algebra checks its result through Proposition 1. Steps 8
> and 9 then use only quotient and projection.

Then delete "contract operations cannot single one out". As written it is a claim with no proof.

### 2. The sentence Φ, the core object, is introduced with no reason for its form
**Where:** Definition 6 (nested ordering), and step 3: "In words: whoever chooses Y_k(t) may use every value
quantified before it." Relay step 3: "Y_1 = ∅".

**Reader:** "Why is this the right sentence? A component cannot see 'every value quantified before it'. Radio
does not see d, and Display does not see r. So your own gloss makes me suspect the sentence is too generous. Why
is Radio's output m not quantified at all? Radio 'chooses nothing'? Why these four conditions (E), (Cap), (Pure),
(Info)? Why are they called 'nested'?"

This is the "pulled out of thin air" complaint, now aimed at Φ instead of at the witnesses. The answer is only
assembled implicitly, inside the proof of Theorem 9. algorithm.tex has a remark on (Info) ("what makes the grants
of Φ harmless") that was dropped.

**Rewrite.** Insert a paragraph before Definition 6:

> *Why one sentence with one quantifier order.* The exact question asks for one causal strategy per component,
> each reading only its own inputs. A sentence `∀∃∀∃…` lets each existential choice depend on everything
> quantified to its left. In general that grants a component values it never receives.
>
> Forwarding removes the excess. Suppose each component is followed in the list by a component it feeds (E), and
> the edge between them has at least as many variables as the first sees and the second does not (Cap). Then
> `i_k` can copy all those values onto the edge. By induction (Lemma 7), `i_{k+1}` sees, through copies,
> everything `i_1, …, i_k` saw. What the components know therefore grows along the list ("nested"). At a single
> time, one quantifier order along the list grants each component exactly what it can know.
>
> (Info) handles later times. The prefix is ordered by time first, so the choice of `i_1` at time 1 comes after
> the inputs of `i_2` at time 0. If `i_2` read the environment, `i_1` would be granted a value it never receives.
>
> Edge values are copies, not choices. So they are left out of the sentence, and they must not occur in the query
> (Pure).
>
> In the relay: Radio's only output m is its edge to Display. So Radio chooses nothing (`Y_1 = ∅`), and forwarding
> fixes `m = r`. Display chooses d, and through m it knows r.

In step 3, add after "In words: ...": "This is more than `i_k` sees. Theorem 9 shows that, on a nested ordering,
every such value is either seen by `i_k` through forwarding or removed by step 6."

---

## MAJOR

### 3. The candidate set T is defined before any reason for it
**Where:** Section 4, first paragraph: "The candidates T are, in a fixed order: the midpoints ...; the bounds ...;
the b_i+1 and b_i−1; and 0." The reason (cells) appears only inside the proof of Lemma 5.

**Reader:** "Why midpoints? Why ±1? Why 0? This is the 'thin air' I complained about."

**Rewrite.** Put this before the definition of T:

> *Idea.* Fix the values of every timed variable other than y. Each atom that contains y then compares y with one
> number, its bound. Between two consecutive bounds, no atom changes truth value, so φ is constant there. Hence φ
> holds for some y iff it holds at one test point of each such piece, or at a bound. The candidates are a fixed
> list of expressions in the other variables that contains such a test point for every possible arrangement of
> the bounds:
> - each bound itself;
> - the midpoint of each pair of bounds (a point between two consecutive bounds);
> - each bound plus or minus 1 (points beyond the outermost bounds);
> - 0 (for the case of no bound at all).

### 4. The witness s_y is ambiguous between a rule, a term and a value, and its exact order is not given
**Where:** Lemma 5(b): "the first c ∈ T with φ[y:=c] true". Lemma 5(b): "∃y φ ⊨ φ[y:=s_y]". Section 4, last
paragraph: "in each group of T, smaller constants first".

**Reader:** "First in which sense? φ[y:=c] is a formula. Its truth depends on the other values. So s_y is a
function, not an element of T. And what is `φ[y:=s_y]`, substituting a function into a formula? Also, 'smaller
constants first' for candidates like `r + 1/2` means what? I cannot reproduce your disjunctive example."

I checked `skolem()` in scripts/delegate.py:
- Within each group, the candidates that are numbers come first, ordered by absolute value.
- All other candidates follow, in lexicographic order of Z3's printed string.
- The atoms come from whatever formula Z3's `qe2` returned at the previous elimination.

So the witnesses depend on the syntactic form of ψ, and on Z3's printer. A reader cannot recompute them by hand
beyond the first elimination. This affects the disjunctive example: `m − 3/8` is chosen over `2m` because the
string "-3/8 + r_0" sorts before "2*r_0".

**Rewrite** of Lemma 5(b):

> The *witness* of y in φ is the rule s_y: given values of the other timed variables, evaluate `φ[y:=c]` for
> c ∈ T in the fixed order, and return the value of the first c for which it is true (0 if none). Written out,
> s_y equals:
> - `c_1` on the region `φ[y:=c_1]`;
> - `c_2` on the region `¬φ[y:=c_1] ∧ φ[y:=c_2]`;
> - and so on.
>
> `φ[y:=s_y]` denotes the disjunction over c ∈ T of (region of c ∧ `φ[y:=c]`).

Add to the last paragraph of Section 4:

> T depends on the atoms of φ, so equivalent formulas can yield different witnesses. All results hold for any
> choice. The script lists each group's numeric candidates by increasing absolute value, then the other candidates
> in lexicographic order of their printed form, and it takes the atoms from the formula Z3 returns. The
> witnesses it prints, beyond the relay, depend on these choices.

Also add a line to Section 10 or the end of Section 7: "So the result is not canonical in (graph, P). It depends
on these orders." SCOPE.md asks for a canonical choice, so this must be said.

### 5. Three elimination methods appear, and the reader cannot tell which one the procedure uses
**Where:** Section 4 has three:
- Lemma 5 (candidates);
- "Cases, interval bounds, Fourier–Motzkin";
- "The script obtains the eliminated formula from Z3's qe2 tactic, checks it equivalent".

Step 4 says "Lemma 5". Section 8 computes by Fourier–Motzkin.

**Reader:** "Which one is the procedure? Checked equivalent to what?"

**Rewrite.** Open the Fourier–Motzkin paragraph with:

> The procedure needs only Lemma 5. The rule below produces a shorter equivalent formula. We use it for the hand
> computations in Section 8. It never changes a witness: witnesses always come from Lemma 5(b).

Replace "checks it equivalent" with "checks with Z3 that the returned formula is equivalent to the quantified
one".

### 6. L is quantifier-free, but contracts are built from quantified formulas
**Where:** Section 2: "Formulas of L are built from atoms with ¬,∧,∨,→". A contract is "a pair of formulas of
L". Projection `ρ_W(A,S) := (∃W̄ A, ∀W̄ S)` and "ρ_W(C) is over W".

**Reader:** "So the projection of a contract is not a contract? Is ∃W̄ A in L?"

**Rewrite.** Add after the operations table:

> A formula with quantifiers is not in L. But by Lemma 5(a), proved in Section 4, each one is equivalent to a
> formula of L. Below, a quantified formula always stands for that equivalent formula, computed by Lemma 5.

### 7. The contract operations are given only as formulas, never in words, and the step-8 identity is not finished
**Where:** Section 2. Only refinement gets an "In words" gloss. Step 8: "the quotient's guarantee is
(S_P ∧ true) ∨ ¬(A_P ∧ ⋀S_j), which is the formula under ∀".

**Reader:** "Brief rule: words first. What is a quotient for? Why is it the right tool in step 8? And
`(S_P ∧ true) ∨ ¬R_k` is not literally `R_k → G_P`."

**Rewrite.** Add:

> - *Composition* describes two components side by side. It promises both guarantees. It needs both assumptions,
>   unless one promise is already broken.
> - *Quotient* `C / C'` is the most permissive contract that, composed with C', still refines C (adjunction,
>   issue 1).
> - *Projection* `ρ_W(C)` is the most permissive contract that mentions only W and still refines C.

In step 8 add: "Since `R_k ⊨ A_P`, the formula `¬A_P ∨ G_P ∨ ¬R_k` is equivalent to `R_k → G_P`."

### 8. "Graph" means two different things
**Where:**
- Section 2: "The graph has an edge u→w" (the architecture).
- Lemma 5(c): "The graph of s_y".
- Step 7: "the decoded graphs of the witnesses".
- Section 10: "graph of f_i^θ".

**Reader:** "I objected to 'graph of a function' before. Now the same word names two objects."

**Rewrite.** Call the architecture "the architecture graph" throughout. For s_y, write: "the *defining formula*
of s_y, written `[y = s_y]`: the formula that holds exactly when y equals the value of s_y." Use the same term in
step 7 and Section 10.

### 9. The plain-language overview has no example, omits the class restriction, and states conditional results as unconditional
**Where:** Section 1, "The solution in plain words".

**Reader:** "'It decides one sentence ... whose quantifiers follow the order in which components see values.'
Which order? There may be no such order. 'If the sentence is false, no such delegation exists.' Always? 'As far
as correctness allows.' The best possible? I learn only on page 5 that the method works only for chains."

**Rewrite** (replace the paragraph):

> **The solution in plain words.** Take a relay. A Radio reads r from the environment and sends m to a Display,
> which outputs d. The query says: if `|r| ≤ 1`, then `|d − r| ≤ 1/2`.
>
> The composition of the delegated contracts refines the query exactly when two implications between formulas
> hold. Contracts that no component can meet satisfy both trivially. So we also require each contract to be
> meetable by a component that computes its outputs from the inputs it has received so far. Among such
> delegations there is no best one, so the procedure must pick one. It does this in three moves.
>
> 1. *Forwarding.* Each component copies onto the variables it sends to the next component the values that the
>    next component cannot see. Radio: `m = r`.
> 2. *Choice.* One sentence of linear real arithmetic says: for every input the environment gives, each component
>    in turn has an output that makes the query true. Eliminating its quantifiers from the inside out yields, for
>    every chosen output, an explicit rule: try these candidate values in this order, take the first that works.
>    Display: `d = r`, which forwarding lets us write in Display's own input as `d = m`.
> 3. *Enlargement.* Quotient and projection then enlarge each contract in turn, until no single contract can be
>    enlarged alone. Display: from `d = m` to any d that is within 1/2 of every r compatible with m.
>
> If the sentence is false, no acceptable delegation exists. The construction is proved correct and complete only
> when the components form a chain along which each can forward to the next ("nested ordering", Section 5).
> Outside that class the method can only prove that no delegation exists (Section 10).

### 10. Step 6 is not a well-defined operation as written
**Where:** Step 6: "in s_y, replace every z(s) ... by s_{z(s)}".

**Reader:** "s_{z(s)} is a piecewise rule, not a term. What does substituting it do?" The answer is in the
"Language" part of the proof of Theorem 9 ("occurs only in region conditions; replacing it in an atom α ... gives
⋁_c(...)"). That is the procedure itself, hidden inside a proof.

**Rewrite** of step 6:

> Write s_y as its list of pairs (region, value). Let z(s) be an output of some `i_j` with j > k that occurs in
> s_y. Since (s, j) precedes (t, k) and j > k, we have s < t. So z(s) occurs only in regions; every value is at
> time t. Replace each atom α containing z(s) by `⋁_{c'} (region'_{c'} ∧ α[z(s):=c'])`, where
> `(region'_{c'}, c')` are the pairs of `s_{z(s)}`. Repeat until no such z(s) is left.

Also say, in step 4: "Variables after y in the prefix have already been eliminated. So ψ, and hence s_y, mention
only y and variables before y." Step 6 relies on this fact, and it is never stated.

### 11. The script computes a different step 9, and nothing checks (V2)
**Where:** after the step list: "The script computes A_{i_k} during the pass of step 8, with the others as they
are then; Section 8 shows that for the relay this is the same formula."

**Reader:** "So the script does not implement your procedure, and its variant is not proved."

The variant uses the seed S_j for j > k. Those sets are smaller than the final ones. So the script's `A_{i_k}`
can be smaller than the document's, and Theorem 10's proof of (V2) does not cover it. The script prints only
"(C1) after sweep". It never checks (V2).

**Fix:** change the script to compute the assumptions after the sweep, with the final S_j, and to print
"(V2) after sweep: True". Then delete the sentence above. If the script is frozen, prove (V2) for the variant or
state plainly that it is unproved.

### 12. The semi-decision procedure is underspecified and its output claim has a gap
**Where:** Section 10, "Forks":
- "piecewise-affine f_i with at most B pieces and unknown coefficients θ";
- "decidable by Tarski's theorem";
- "A rational witness θ gives ...";
- "such quantifiers branch".

**Reader:** "A piece of what shape? With B pieces but unboundedly many inequalities per piece, θ has no fixed
length. And if the sentence is true but only irrational θ work, what do you output?" "Branch" and the content of
Tarski's theorem are never stated.

algorithm.tex has the missing parametrisation: "each cut out by at most B affine atoms".

**Rewrite.**

> For B = 1, 2, …, consider for each i a function f_i given by at most B pieces. Each piece is a conjunction of at
> most B affine inequalities over `in(i)`, and f_i is affine on each piece. Range over all choices of rational
> coefficients θ. For fixed θ, the formula `(A_P → G_P)[out(i) := f_i^θ(in(i))]` is in L, so Lemma 5 decides
> whether it holds for every environment. Enumerate the pairs (B, θ).
>
> If an acceptable delegation exists, then (K) and Lemma 5(b) give piecewise-affine strategies with rational
> coefficients, each reading only `in(i)`. So the enumeration halts. It outputs `(true, [y = f_i^θ])`, which is in
> L. If no acceptable delegation exists, it runs forever. No bound on B is known.

This removes Tarski's theorem and the rational-witness gap. Replace "such quantifiers branch and form no
first-order prefix" with: "Each f_i depends on a different set of values, and these sets are not nested. So no
single order of ∀ and ∃ expresses the question."

### 13. Density and legibility
**Where:** the whole document.
- The preamble uses 0.75in margins, 1pt paragraph skip, 3pt display skips and a hand-shrunk section style. The
  brief says normal margins.
- Section 8 is run-in text with bold step numbers.
- The verbatim block is set at 6.2pt. The two sweep lines wrap with ↪ markers and contain runs of 8 spaces. These
  come from Z3's pretty-printer, flattened by `fmt()`.

**Reader:** "I cannot find step 8 for Display. I cannot read the printed contract."

**Fixes:**
- In `fmt()`, collapse whitespace: `" ".join(str(simplify(f)).split())`. Print the guarantee's conjuncts one per
  line. Re-paste at 7.5pt or more.
- Rename the script labels so the document needs no translation key: "(C1)" → "(V1)", "(Lemma 1)" →
  "(Theorem 8)", "Phi (linearised sentence)" → "Phi". This removes most of Section 9's legend.
- Set Section 8 as an enumerated list, one item per procedure step.
- To make room:
  - shorten the "In case form" half of the Section 4 example (Section 8 shows the same computation in full);
  - fold the (K)-versus-(R) example into one sentence;
  - drop "Steps 4, 8, 9 eliminate, steps 6, 7 substitute; nothing else is computed". It is inaccurate anyway:
    steps 1 to 3 compute N, the ordering and the sets.

---

## MINOR

14. **Unstated modeling assumptions.**
    - Section 2: "Time is discrete" and "We assume it has no directed cycle" are stated as facts. The author said
      "STL" and did not exclude feedback.
    - Definition 3 allows the output at t to depend on the input at t (zero delay). This should be said in words.

    Rewrite: "We assume (i) discrete time 0..H, (ii) no directed cycle in the architecture graph, and (iii) zero
    delay: a component's output at t may depend on its inputs at t. Section 10 discusses delays."

15. **Step 3: "the set of values at time t of the inputs".** These are timed variables, not values.
    - Rewrite: "E_k(t) is the set of timed variables v(t) with v ∈ in(i_k) and v not a port of any earlier i_j."
    - Give the reason they are environment variables: "a component that writes v is in N and precedes i_k, so v
      would be its port."
    - "Terminal outputs" is misleading. Such an output may be read by `i_{k+2}`. Say "outputs not on the edge to
      `i_{k+1}`".

16. **Section 4: index clash.** "b_i", "i<j" reuse i, j, which name components everywhere else. Number the atoms
    1..n and write β-indices or `b_a`.

17. **Section 2: formulas used as sets, and "environment" with two meanings.**
    - Never stated: a formula is identified with the set of traces satisfying it. Yet the text uses "implementation
      set", "S_i grows", "⊇".
    - "A component implements the contract if every trace it produces lies in S." There are no component models.
      Say "an implementation is any set of traces; it implements the contract if it is contained in S".
    - "Environments (the traces in A)" conflicts with "environment variable".
    - Give a plain gloss for saturated: "the guarantee already allows every trace that violates the assumption".

18. **Theorem 8: "Read Φ as a game".** State the semantics actually used: "Φ is true iff there are functions
    choosing each existential value from the values before it in the prefix, such that the matrix holds for all
    universal values."

19. **Theorem 8 and Section 10: "Theorem 8 still refutes".** As stated, Theorem 8 assumes (Pure), and its Y_k
    exclude edge variables. Section 10 uses a different Φ (all outputs quantified). State this as a remark with
    its own one-line justification.

20. **Relay step 7: "(d = r)δ_2 is d = m".** The Lemma 5(c) formula for s_d is a disjunction over T. Say: "since the
    first candidate r satisfies ψ[d:=r] ≡ true, the defining formula reduces to d = r."

21. **Section 9 legend: "which is (K) by Lemma 5".** The equivalence of `∀in(0)∃out(0)…` with (K) is reading the
    sentence through choice functions, not Lemma 5. Lemma 5(b) makes those functions explicit. Also, "G" in that
    sentence should be S_i.

22. **Section 9: map the printed sweep contracts to Section 8.** Say "the printed G of Radio is the CNF of
    `|r| ≤ 1 → |m−r| ≤ 1/2`; that of Display is the CNF of the displayed S_Display". Note that the script's "G" is
    the implementation set S.

23. **Disjunctive example.** "the printed term is m − 3/8 for ..." cannot be checked from the document. No
    printout is shown, and the order is not given (issue 4). Either list the first three candidates and the order,
    or say "printed by the script; not derived here".

24. **Overview: "as far as correctness allows".** This suggests greatest. Say "until no single contract can be
    enlarged alone" (Theorem 10).

25. **Lemma 7 and the decoding.**
    - κ_k(v) is used as a function, but v may be a port of several i_j, and the construction depends on j. Fix
      the largest such j.
    - Add plain words: "Under forwarding, every value an earlier component saw arrives, as a copy, on some input
      of i_k. κ_k(v) is that input. δ_k rewrites a formula about earlier variables into one about these inputs."
    - Write `δ_k(φ)`, not the postfix `φδ_k`.

26. **Section 6: notation S_j versus S_{i_j}.** "⋀_{j≠k} S_j" mixes a position index with a component index. Write
    `S_{i_j}`, and say that components outside N contribute `true`.

27. **Section 10, delays: "never a line of slope one".** Add the one-line reason: "a finite union of products
    containing every point (a, a) contains some product I × J with I, J intervals of positive length. It then
    contains a point (a, b) with a ≠ b."

28. **Honesty: forwarding treats every edge variable as a free channel.** In the relay, m = r is natural. In
    general, an edge variable may have physical meaning that the query does not mention. Add to Section 10: "The
    procedure may assign edge variables values that are meaningless physically; only the query constrains them."

29. **Prop. 2(a): "no component can produce any trace".** Only the component given false cannot. Say "the
    component given (true, false) has no implementation".

---

## Verdict: **revise**

The mathematics is sound, the relay computations are exact, and the output block matches the script. The
document does not yet meet the author's standard on two points.

First, it never squarely addresses his requirement to use only contract operations. It says the algebra "cannot
single one out" without showing it. Issue 1 gives a two-line demonstration from the relay, and the sources
already contain the needed lemmas.

Second, it introduces its central object, the sentence Φ with its quantifier order and its four nestedness
conditions, without saying why that order models what each component knows. The explanation exists only inside
the proof of Theorem 9.

**What the reader would still not understand after this draft:**
- why a single ∀∃ prefix is the right question to ask;
- why Radio "chooses nothing";
- why forwarding and the four conditions make the generous prefix harmless;
- why the candidates are midpoints, ±1 and 0, until he reaches the middle of a proof;
- whether the witness is a function or a term, and how to substitute it in step 6;
- which of three elimination methods the procedure actually uses;
- how to reproduce any witness beyond the relay, since the order depends on Z3's printed strings;
- whether the script's step 9 is the proved one;
- what exactly the semi-decision procedure enumerates.

He would also have to read to page 5 to learn that the construction is complete only for chains.
