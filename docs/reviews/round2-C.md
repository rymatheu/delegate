# Round 2, Reviewer C: reproducibility and consistency with the code

Reviewed: docs/complete.tex (188 lines), scripts/delegate.py (422 lines), scripts/results_report.py,
docs/results.tex, README.md, docs/reviews/round1-rebuttal.md.
Environment: z3-solver 5.3.1.0, Python 3.12.13.
Scratch is /private/tmp/claude-501/-Users-ryan-Research-delegate/547e050f-c29a-418f-816a-16412bc752a6/scratchpad/r2/ :
- delegate.out: the full output from a clean shell;
- quoted.txt and first21.txt: the byte comparison;
- r2_check.py: the Z3 checks of the document's claims;
- tex/: latexmk runs.

**Verdict: revise (light).**
- No BLOCKING item.
- Every round-1 item is fixed in both the code and the document.
- The verbatim block is byte-identical to the first 21 lines of the new output.
- I reproduced the disjunctive witness by hand from the stated candidate order.
- One MAJOR item remains (N1). It is a one-sentence fix in the document: the script's B = 1 run does not do what the
  semi-decision Remark describes.
- Four MINOR items remain.

## 1. Runs (clean shell: `env -i HOME=$HOME PATH=/usr/bin:/bin /bin/sh`)

| Command | Result |
|---|---|
| `.venv/bin/python scripts/delegate.py` | exit 0, 1.6 s, 241 lines, ends `all verdicts as expected`. md5 ab21854a... is the same for the clean-shell run and two normal runs. |
| `.venv/bin/python scripts/results_report.py` | exit 0, prints `results.tex written; disj pieces: 3 ; H2 pieces: 2 4`. The regenerated docs/results.tex is byte-identical to the committed one. |
| `latexmk -pdf complete.tex` (scratch copy, clean env) | exit 0, **5 pages**, no warnings, no overfull or underfull boxes. |
| `latexmk -pdf results.tex` | exit 0, 2 pages. One harmless font warning (`OT1/cmr/bx/sc`, from \textsc inside \textbf). |

## 2. Round-1 items

| Item | Code | Document | Evidence |
|---|---|---|---|
| M1 (Scope) | Fixed: lines 180-185 check Scope and return "does not apply (Scope)" | Fixed: step 1 checks it; the wrong counterexample is gone; Section 10 states the role of (Scope) | Regression 3 prints `(Scope) fails: ['o'] ... the procedure does not apply`. |
| M2 carriers | Fixed: lines 248-262 implement the Lemma 8 recursion from the largest j. Lines 254, 276 and 308 assert carriers, seeds and swept contracts are over ports | Fixed: Lemma 8 states the recursion explicitly | My X/Y/Z/W instance (regression 1b): seed `d_0 == z1_0`, swept W non-trivial, (V1), (V2) and receptive & causal all True. Reviewer A's C1..C4 (regression 1a): seed `d_0 == g1_0`, all True. I re-derived κ by hand for both (r→e→e→z1 and r→e→e→g1). |
| M3 step 9, (V2) | Fixed: step 9 runs after step 8, with the final sets (lines 302-309). (V2) is checked and printed | Fixed: the disclaimer is gone; the block quotes `(V2) after sweep: True` | (V2) is True on all 9 nested runs. Regression 2 also has (V2) True, with both assumptions TRUE. |
| m1 results.tex row at -1/8 | Fixed: results_report.py line 50 sets the open end | n/a (complete.tex no longer quotes it) | results.tex row: `$-1\le m<-1/8$`. Z3 confirms all three pieces on the new seed. |
| m2 substring loop | Fixed: `resolve` matches symbols by term traversal (`syms_of`), with a bounded number of rounds | Step 6 is defined on terms | Regression 4 (names `d`, `ad`) terminates. Regression 4b shows step 6 really substitutes: the witness of q_1 mentions d_0, and the Radio seed is `q_1 == r_0`. |
| m3 candidate order | `witness` docstring and code (lines 110-172) | Section 4 states the five tiers, the constant-first sort with negative before positive, ASCII order of the canonical printing, and dropping of duplicates. Steps 2 and 3 state the enumeration and declaration orders. | **Reproduced by hand; see below.** |
| m5 version | The first printed line is `z3 version 5.3.1` | Section 9 pins `z3-solver==5.3.1.0`, gives the install command, and warns that clause order may vary | OK. README does not pin the version (N4). |
| m7 checks after sweep | (V1), (V2) and receptive & causal printed after the sweep | Quoted | OK. |
| m10 README | README names `docs/complete.pdf` and `.venv/bin/python scripts/delegate.py` | n/a | OK. |
| m11 clause count | results.tex no longer gives a count; it says the count depends on the Z3 version | n/a | OK. |
| m4, m6, m8, m9, m12 | Script labels are now (V1), (V2), "necessity theorem" | Line 124 ("any equivalent formula ... qe2 output"); Section 9 (`y == If(...)` is ⟦y = s_y⟧; the in(i)/out(i) wording); the fan-in text was removed | OK. |

**Disjunctive witness, by hand from Section 4 only.**
- Formula: φ = |r|≤1 → ((r≥0→d≥1) ∧ (r<0→d≤−1)) ∨ |d−2r|≤1/4.
- Bounds of d: 1, −1, 2r+1/4, 2r−1/4.
- Tier 1, midpoints. The six pairs give 0, r+5/8, r+3/8, r−3/8, r−5/8, 2r. The constant 0 comes first. The others go in
  ASCII order of `1*r_0 + -3/8`, `1*r_0 + -5/8`, `1*r_0 + 3/8`, `1*r_0 + 5/8`, `2*r_0 + 0`.
- Tier 2, bounds: −1, 1, 2r−1/4, 2r+1/4.
- Tier 3, bounds plus one: 2, 2r+3/4, 2r+5/4. The 0 is a duplicate.
- Tier 4, bounds minus one: −2, 2r−3/4, 2r−5/4.
- Tier 5: 0, a duplicate.
- This list equals the `DELEGATE_TRACE=1` candidate list exactly:
  `['0', '1*r_0 + -3/8', '1*r_0 + -5/8', '1*r_0 + 3/8', '1*r_0 + 5/8', '2*r_0 + 0', '-1', '1', '2*r_0 + -1/4', '2*r_0 + 1/4', '2', '2*r_0 + 3/4', '2*r_0 + 5/4', '-2', '2*r_0 + -3/4', '2*r_0 + -5/4']`.
- Testing the candidates in order:
  - 0 works iff |r| ≤ 1/8, or |r| > 1.
  - Otherwise, for r < 0, r−3/8 works on [−1,−1/8): it satisfies |d−2r| ≤ 1/4 on [−5/8,−1/8] and d ≤ −1 on [−1,−5/8].
  - For r > 0, r−3/8 and r−5/8 fail, and r+3/8 works on (1/8,1]: it satisfies |d−2r| ≤ 1/4 on [1/8,5/8] and d ≥ 1 on [5/8,1].
- Result: **m−3/8 on [−1,−1/8), 0 on [−1/8,1/8], m+3/8 on (1/8,1]**, after decoding r ↦ m. Z3 proves this equal to the
  script's witness on |r| ≤ 1, and proves that it satisfies G_P (r2_check.py).
- Caveat: hand reproduction works here because this is the first elimination. A later witness is built from qe2 output,
  so it needs the trace. The script's docstring says this; the document does not (N3).

## 3. Numbers and quoted lines in the revised complete.tex

- **Verbatim block (lines 160-180):** byte-identical (`cmp`) to lines 1-21 of the clean-shell output and of a live run.
- **Section 4 example:** T = r, r−1/2, r+1/2, r+3/2, r−3/2, 0. This equals the trace (`['1*r_0 + 0', '1*r_0 + -1/2', '1*r_0 + 1/2', '1*r_0 + 3/2', '1*r_0 + -3/2', '0']`).
  The witness is `s_d = r_0`.
- **Section 3, "What the algebra alone gives":** confirmed by Z3. ρ_{r,m}(P) = (|r|≤1, |r|>1) and ρ_{m,d}(P) = (true, false).
- **Section 8, every step:**
  - The seed equals the printed seed.
  - The printed swept Radio and Display contracts are equivalent to the document's output (A and G, each checked).
  - The two Fourier-Motzkin cases hold. A_Display = |m|≤3/2.
  - A_Radio = |r|≤1, computed with the final S_Display.
  - Both final sets are maximal.
  - These were already verified in round 1 and re-checked against the new output.
- **Section 10, fork example:** ∀s2 ∃b ∀s1 ∃a (|a−b|≤1/2 ∧ |b−s2|≤1/2) is true (Z3). For the ordering B, A: edge_B = ∅ and
  priv_B = {s2, b}, so (Cap) fails while (Pure) holds, as stated.
- **Cost:** n(n−1)/2 + 3n + 1 (unchanged).
- **Mismatches:** none.

## 4. Document versus code, step by step

| Step | Status |
|---|---|
| 1, relevance and (Scope) | Agree (lines 180-185). |
| 2, ordering | Agree. `topo_orders` permutes sorted(N) lexicographically; (E), (Cap), (Pure), (Info) at lines 193-198. |
| 3, sentence | Agree. E_k and Y_k in declaration order; σ pairs the sorted lists; the prefix is by t, then k. |
| 4, elimination | Agree, with the caveat of N3. Witnesses last first, using the stated T; ∀ blocks by qe2, covered by line 124. |
| 5, decision | Agree. |
| 6, substitution | Agree semantically. The code substitutes the If-term s_{z(s)} for z(s). This equals the document's atom-wise replacement. |
| 7, seed | Agree. Decoding is δ_k with κ from the largest j; the seed prints as `y == If(...)`, as Section 9 says. |
| 8, sweep | Agree. `S[c] = qe(ForAll(X_k, G_P ∨ ¬R_k))`, with R_k over all other components (TRUE outside N). |
| 9, assumptions | Agree. Computed after the sweep, from the final sets. |
| Remark (semi-decision, H = 0) | **Disagrees** (N1). |

## Findings

### MAJOR

**N1. "The script tries B = 1" (line 185) does not describe what `fork_affine` does.**
- The Remark's procedure:
  - enumerates rational θ;
  - uses first-match lists with at most B pairs (region, affine map), each region having at most B atoms, default 0;
  - decides the linear closed formula for each θ by Lemma 6.
- The script (lines 321-345):
  - uses one affine map per output on the whole space. That is the region-TRUE subclass of B = 1. It never tries a
    one-atom region with default 0;
  - does not enumerate θ. It asks Z3 to decide the nonlinear sentence ∃θ ∀env (A_P→G_P)[strategies], with a 60 s
    timeout, so `unknown` is possible;
  - only then checks the linear sentence for the θ found (`check forall env`).
- The output is correct when that check passes, but the sentence claims the script runs the Remark's procedure at B = 1.
- Fix (document, one sentence): "The script tries one affine map per output (the region-TRUE case of B = 1). It finds θ
  with Z3 on ∃θ∀(environment)(A_P→G_P)[...], which is nonlinear, and then checks the linear formula for that θ."
- Alternative fix (code): implement the enumeration. This is not needed.

### MINOR

**N2. "The sweep's G is S_{i_k} in conjunctive normal form" (Section 9) is not true in general.**
- It is true for the quoted relay lines.
- In three of the script's runs, the swept G of Radio contains `If(...)` terms inside atoms (the qe2 output after
  eliminating d = If(...)). These are the disjunctive run (output line 61), regression 4 (line 208) and regression 4b
  (line 228). Such a formula is equivalent to a formula of L, but it is not one as printed, and it is not a CNF.
- Fix (document): "the sweep's G is a quantifier-free formula equivalent to S_{i_k}; for the relay, a CNF".

**N3. Where the witness atoms come from is stated only for the later eliminations.**
- Line 124 says the script uses qe2 output, simplified.
- The code reads the bounds from `simplify(R)` every time, including the first witness, where R = A_P→G_P.
- In the relay and disjunctive cases, simplify does not change the bound set. But a reader reproducing a first witness
  by hand should know the formula is simplified first.
- Fix (document): add "(each witness is read from Z3's simplify of the current ψ; DELEGATE_TRACE=1 prints it and T)".
  This also tells the reader how to reproduce later witnesses.

**N4. README's install line does not pin the version.**
- README.md, Tooling, reads `uv pip install -p .venv/bin/python z3-solver numpy scipy`. complete.tex pins
  `z3-solver==5.3.1.0`, and the byte-exact quote depends on that pin.
- Fix (README): use `z3-solver==5.3.1.0`.

**N5. Small inaccuracies.**
- Line 91: "(r+1/2−1 is a duplicate)". Both shifted copies are duplicates: (r−1/2)+1 = r+1/2 is dropped in tier 3, and
  (r+1/2)−1 = r−1/2 is dropped in tier 4. Fix (document): "(r−1/2+1 and r+1/2−1 are duplicates)".
- docs/results.tex is not part of complete.tex, but it is regenerated with stale text. It still cites
  "step 4 of algorithm.pdf", "Corollary 1 of existence.pdf", "Lemma 1 of algorithm.pdf" and "Skolem term" (results.tex
  lines 6, 16, 37). These are hard-coded in results_report.py. Fix (code): change the strings to "step 7", "Theorem 11",
  "Theorem 9" and "witness", referring to complete.tex.

## 5. Banned words and format

- Case-insensitive grep of complete.tex returns 0 hits each for: EARS, prior, template, band, decider, flag, ghost,
  Hoare, interpolant, network coding, quantizer, capacity theorem, orchestrator, agent, "the notes", column, support,
  Skolem, `(C1)`, "Lemma 1)", algorithm.pdf, existence, results.pdf, /Users, notes/, `---`, em-dash.
- Length: 5 pages.
- Layout: 10pt, 0.75 in margins, verbatim at 8 pt. The writer partly rebutted m13; I accept the rebuttal for this
  review's scope.
