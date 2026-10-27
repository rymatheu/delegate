# Round 1, Reviewer C: reproducibility and consistency with the code

Reviewed: docs/complete.tex (190 lines, 5 pages), scripts/delegate.py, scripts/results_report.py, docs/results.tex.
Environment: .venv/bin/python 3.12.13, z3-solver 5.3.1.0.
Scratch scripts are in /private/tmp/claude-501/-Users-ryan-Research-delegate/547e050f-c29a-418f-816a-16412bc752a6/scratchpad/ :
relay_check.py (task 3), other_checks.py and v2_search.py (sweep audit, disjunctive witness), divergence.py (Scope and
decoding counterexamples), substring.py (hang), clauses.py, patched/delegate.py and delegate.patch (proposed code patch),
rr/ (patched results_report.py).

**Verdict: revise.** No BLOCKING item. Every number, formula, contract, verdict and printed line that complete.tex
quotes is reproduced. Three MAJOR items: the code does not implement the procedure as the document states it.
For two of them (M1, M2) I built in-class or in-document instances where the program prints a wrong or non-local result.

## Summary of checks

| Check | Result |
|---|---|
| `.venv/bin/python scripts/delegate.py` | exit 0, 0.49 s, output byte-identical over 3 runs (md5 90bbf74b...) |
| Same command from `env -i HOME=$HOME PATH=/usr/bin:/bin /bin/sh` | exit 0, output identical |
| `.venv/bin/python scripts/results_report.py` | exit 0; prints `results.tex written; disj pieces: 3 ; H2 pieces: 2 4`; regenerated docs/results.tex is byte-identical to the committed one |
| Verbatim block (complete.tex lines 167-183) vs. script lines 2-18 | identical, 17 lines, including the multiple spaces inside lines 181-182 |
| Relay walk-through (Section 8), every step, re-derived with Z3 | all claims hold (list below) |
| Disjunctive witness, refutation, fan-in, cost formula | all hold |
| results.tex at m = -1/8 | it is wrong; complete.tex is right. Cause: a bug in results_report.py, not a typo (m1) |
| Banned words (case-insensitive grep, full brief list, plus "support", "column", em-dash, `---`, paths outside the directory) | 0 hits |
| Page count | 5 pages (docs/complete.log; recompiled in scratch: 5 pages, no warnings after 3 passes, labels stable) |

Relay facts confirmed by Z3 (relay_check.py; every line printed True or the stated value):
- Phi = forall r exists d (|r|<=1 -> |d-r|<=1/2) is true. The bounds of d are r+1/2 and r-1/2. The first candidate is the midpoint r.
  `skolem` returns exactly `r_0`. psi[d:=r] is valid. qe(exists d psi) is True.
- Seed Radio (true, m=r), Display (true, d=m): (V1) holds, and both contracts are receptive and causal.
- Step 8, Radio: forall d((|r|<=1 & d=m) -> G_P) is equivalent to |r|<=1 -> |m-r|<=1/2.
- R_2 is equivalent to |r|<=1 & |m-r|<=1/2.
- Case r > d+1/2 gives |m|<=3/2 & d<1/2 & d<m. Case r < d-1/2 gives |m|<=3/2 & d>-1/2 & d>m.
- S_Display is equivalent to |m|<=3/2 -> ((d>=1/2 | d>=m) & (d<=-1/2 | d<=m)). The four region readings (line 158) hold.
- Step 9: A_Display is |m|<=3/2. A_Radio is |r|<=1, both with the final S_Display and with the in-pass seed (d=m).
- The printed swept contracts are equivalent to the document's output contracts (line 159).
- On the final delegation: (V1), (V2), (R), (K) and saturation hold. The seed sets are contained in the final sets.
  Each final S_i is the weakest one given the other final S_j (maximality).
- Proposition 4: the trace r=1, m=-1, d=-1 lies in both unions and violates G_P.
- (K) is stronger than (R): the H=1 example is receptive and not causal.
- Cost: |T| = n(n-1)/2 + 3n + 1.
- Disjunctive query: the witness is m-3/8 on [-1,-1/8), 0 on [-1/8,1/8], 2m on (1/8,1], and it is 0 at m=-1/8.
  The seed satisfies (V1).
- Refutation: with r(t) = -1 for all t, no d satisfies G_P. The script prints `Phi (linearised sentence) = False`.
- Fan-in: printed `a = -1*s1_0`, `b = -1*s2_0`, `f = -1*a_0 + -1*b_0`, `check forall env: True`.
- Section 10 (Scope) example: the stated delegation satisfies (V1), and Phi fails at o=-1, r=2 (see M1).

Sweep audit on all four nested instances (relay, chain, disjunctive, H=2) (other_checks.py). On each one:
- the swept delegation satisfies (V2);
- each swept contract is receptive and causal;
- each seed mentions only the component's ports;
- the code's in-pass assumption equals the document's step-9 assumption (computed with the final S_j).

## Findings

### MAJOR

**M1. (Scope) is not checked. The program then prints a wrong "no acceptable delegation exists".**
- Location: complete.tex line 95 (standing assumption), line 109 ("Input: ... satisfying (Scope)"), line 189 (counterexample).
  delegate.py lines 87-134 contain no Scope test.
- What the code does: it builds Phi with the variables outside N left free. It then treats them as universally quantified
  outermost (`valid(cur)`) and reports a refutation.
- Run on the document's own example (relay plus Q writing o; A_P = (o>=0 -> r<=1), G_P = (d=0 & r<=1)). Output:
  `Phi (linearised sentence) = 0 <= o_0`, then `Phi is false: NO acceptable delegation exists (Lemma 1)`.
  Section 10 shows, and Z3 confirms, that an acceptable delegation exists.
- Fix (code): after computing N, print "does not apply" and return when some variable of A_P or G_P is not a port of N.
  See hunk 2 of the patch below. With the patch the example prints
  `(Scope) fails: ... DELEGATE does not apply`. The six instances in the script are unaffected.

**M2. The decoding in the code is not the decoding of Lemma 7 (carriers). On a nested ordering the seed can mention
variables that are not ports, and the sweep then outputs an unsatisfiable guarantee.**
- Location: complete.tex lines 100-106 and step 7 (line 119). delegate.py lines 147-156.
- What the code does: it maps only the variables in priv_j. It follows a carrier only while the carrier is again private
  (`while jj < k and e in sigma[order[jj]]`). It stops when the carrier is a shared port of the next component. The
  Lemma's case "if v in ports(i_{j+1}) let w := v" is missing. It also replaces variables that are ports of i_k, which
  delta_k leaves alone. The substitution is simultaneous, so chained keys do not compose.
- Counterexample (divergence.py): X: r -> e; Y: e -> y1; Z: e, y1 -> z1, z2; W: z1, z2 -> d; H=0; A_P=|r|<=1,
  G_P=|d-r|<=1/2. The ordering X, Y, Z, W satisfies (E), (Cap), (Pure), (Info), and (Scope) holds. The code accepts it.
  - The Lemma gives kappa_4(r) = z1, so W's seed should be d = z1.
  - The code prints `contract W: A = true ; G = d_0 == e_0`. But e is not a port of W.
  - The code's checks do not catch this. They print `(C1) ... True` and `W receptive & causal: True`, because the free e
    is read as universally quantified.
  - The sweep then prints `W: A = True ; G = And(d_0 <= -1/2, 1/2 <= d_0)`. This guarantee is false, so the contract is
    not receptive. The output contradicts Theorems 9 and 10 inside their class.
- Fix (code): implement kappa as in the Lemma, and assert that each seed is over its ports. See hunks 3 and 4.
  With the patch, W's seed is `d_0 == z1_0`, the swept W contract is non-trivial, and (V2) holds. Seeds of the six
  instances are unchanged.

**M3. Step 9 as stated (assumptions from the final S_j) is not what the code computes. The code never checks (V2)
for the output.**
- Location: complete.tex step 9 (line 123), line 125, Theorem 10 proof ("Step 9", line 148), relay step 9 (line 159).
  delegate.py lines 185-194.
- What the code does: it computes A_c inside the step-8 loop, with the later components still at their seeds. Its only
  final check is (V1) (`(C1) after sweep`). The document discloses the timing (line 125) and shows equality for the relay.
  But Theorem 10's (V2) argument uses the final R_k. The in-pass R_k is smaller, so the in-pass A_c can be smaller, and
  then (V2) is not covered by the proof.
- I found no instance where they differ. They agree on all four nested instances and on five extra variants with
  A_P mentioning d (v2_search.py). But the program's output is not what the theorem certifies.
- Fix (code, preferred): after the loop, recompute A_c with the final S_j, and print `(V2) after sweep: ...`. See hunk 5.
  Then delete the sentence at line 125 and the sentence "During step 8 the script computes ... the same." at line 159.
  Add the new line `  (V2) after sweep: True` to the verbatim block.
  Caution: regenerate the verbatim block from the patched script; do not hand-edit it (see m5).
  Alternative (document): state step 9 as the code does it, and prove (V2) for the in-pass assumptions. I see no short proof.

### MINOR

**m1. The m = -1/8 entry of results.tex is wrong, as the writer says. The cause is a bug in results_report.py, not a typo.**
- Z3: the witness at m = -1/8 is 0. The first branch `And(m_0 >= -1/8, m_0 <= 1/8)` fires there.
  Z3 also proves that `-3/8 + m` on the closed interval [-1,-1/8] is false. complete.tex line 161
  (`-1 <= m < -1/8`, `-1/8 <= m <= 1/8`, `1/8 < m <= 1`) is correct.
- Cause: results_report.py line 50. When an open interval is merged after a point, the code keeps the point's closed
  flag (`pt or hic`) when it should set the upper end to open.
- Fix (code): `merged[-1] = (lo, loc, b, False, L) if not pt else (lo, loc, hi, True, L)`, then regenerate results.tex.
  Tested in scratch rr/: the only change in results.tex is row 1, which becomes `$-1\le m<-1/8$`.

**m2. A substring test in step 6 can loop forever.**
- delegate.py line 144 tests `yname in str(term)`. If a later output named `d` exists and the term mentions `ad_0`,
  the substitution is a no-op but sets `changed = True`, and the loop never ends. Demonstrated by substring.py (killed
  after 20 s).
- Fix (code): compare symbols, not strings. See hunk 1 and the changed line in hunk 3.

**m3. Orders that determine the output are not fully stated.** The document says the result "depends on the order of T
and of the sweep" (line 150). A reproducer needs the following exact orders:
- Within each group of T, the code sorts by printed form: constant candidates first, by increasing absolute value, ties
  by string; then non-constant candidates in lexicographic order of their Z3 string. Midpoints are not taken in the
  "i < j" order of line 79. "Smaller constants first" (line 92) does not say where non-constants go.
- Step 2 enumerates the permutations of the alphabetically sorted N, in lexicographic order. "The first nested one"
  (line 112) depends on this.
- The order within E_k(t) and Y_k(t) is the order in which the ports are declared ("a fixed order", line 113).
- Fix (document): one sentence each, in Section 4 and in steps 2-3.

**m4. Elimination granularity.**
- Step 4 says "eliminate forall ... for each timed variable of E_k(t) in turn". Steps 8-9 say "eliminated by Lemma 5".
- The code calls qe2 once on the whole block (line 131) and once on the whole hidden set (lines 190-191). It uses
  Lemma 5 only to build the witnesses (`skolem`).
- Line 92 says qe2 is used, but it also says "one at a time".
- Fix (document): "The script eliminates each universal block, and the hidden set of steps 8-9, with one call of Z3's
  qe2 and checks the result equivalent. It uses Lemma 5(b) only to build witnesses."

**m5. The verbatim output depends on the Z3 version and on incidental code.**
- The clause order inside printed formulas is Z3's.
- With the patch below, which does not change any computed set, the relay's `Display:` sweep line comes out with its
  disjuncts in a different order. G_P lines of other instances also reorder. Every verdict line is unchanged.
- Fix (document): line 165 should say "with z3-solver 5.3.1.0", give the install command (for example
  `uv venv && uv pip install -p .venv/bin/python z3-solver==5.3.1.0`), and say that other versions may print the same
  formulas with conjuncts and disjuncts in another order.
- Also: "exactly this" omits the separator line of `=` characters that precedes `relay, H = 0`. "One block per instance"
  is not exact: the fan-in prints two blocks (DELEGATE, then FORK). Say so.
- Fix (code, optional): add a requirements file pinning z3-solver==5.3.1.0.

**m6. Printed seed form.**
- The code prints the seed as a term equation `d_0 == If(...)`, not as the L-formula "graph" of Lemma 5(c).
  The two are equivalent, but the disjunctive seed in the output looks nothing like the graph formula of the text.
- Fix (document): one clause in Section 9 saying that "G = y == If(c, e1, e2)" prints the graph of Lemma 5(c) in term form.

**m7. The code checks only (V1) after the sweep.**
- Theorem 10 claims (V2), (R), (K), saturation and locality for the output. The script verifies none of these for the
  swept delegation.
- I verified them with Z3 on the four nested instances, and all hold.
- Fix (code): the (V2) line of hunk 5. Optionally, rerun the receptive-and-causal check on the swept S_i.

**m8. The fan-in description is incomplete.**
- Line 187 lists the graph as "s_1 -> a, s_2 -> b, a,b -> f". The script's graph also has Logger reading f and writing l.
  It is outside N and harmless.
- Fix (document): add "and a Logger f -> l outside N".

**m9. Output labels refer to numbering from other documents.**
- The script prints "(C1)", "(Lemma 1)", "DELEGATE", "see FORK". Its docstring cites docs/algorithm.pdf.
- Line 165 maps the first two to the document's names, but "see FORK" is not mapped. It does not appear in the
  quoted relay block, but it appears in the refutation and fan-in output the reader will see.
- Fix (code, preferred): print "(V1)", "(Theorem 8, necessity)", "does not apply (no nested ordering)".
  Then regenerate the verbatim block (see m5) and drop the mapping sentence.

**m10. README.md gives a different "one command".**
- It names `.venv/bin/python scripts/decompose.py` (the superseded method), and docs/decomposition.pdf as the deliverable.
  A reproducer who opens the README first will run the wrong script.
- Fix (README, outside the document): point to scripts/delegate.py and docs/complete.pdf.

**m11. results.tex: "a union of polyhedra with nine clauses" is not reproduced.**
- This is not used by complete.tex.
- The swept Display guarantee of the disjunctive instance has 37 top-level conjuncts as printed, also after
  ctx-solver-simplify (clauses.py).
- The text is hard-coded in results_report.py line 172.
- Fix (code): compute the count, or drop the number.

**m12. Notation clash.**
- Line 165 writes in(t), out(t) for "values at time t", but in(i), out(i) are sets of variables of component i
  (line 33).
- Fix (document): write "the values at time t of in(i) and of out(i)".

**m13. Format.**
- Five pages hold, but only with 0.75 in margins, compressed skips, and a 6.2 pt verbatim block.
- Lines 181-182 are hard to read at that size.
- Not a reproducibility error. Flagged for the writer, since the brief says "normal margins".

## Proposed code patch (scripts/delegate.py; tested in scratch, delegate.patch)

Effect on the script's own output:
- adds a `(V2) after sweep: True` line to each of the four nested instances;
- changes no verdict, seed or swept set (checked by equivalence);
- reorders some printed clauses (m5).

Effect on the counterexamples: M1 prints "does not apply", M2 gives a seed over W's ports, m2 terminates.

```diff
@@ -46,6 +46,12 @@
+def syms_of(f):
+    out = set()
+    def walk(e):
+        if is_const(e) and e.decl().kind() == Z3_OP_UNINTERPRETED: out.add(e)
+        for ch in e.children(): walk(ch)
+    walk(f); return out
 def vars_of(f):
@@ -85,6 +91,9 @@
     N = arch.support(vars_of(GP)); print(f"  N = {sorted(N)}")
+    portsN = {v for c in N for v in comps[c][0] + comps[c][1]}
+    if not (vars_of(AP) | vars_of(GP)) <= portsN:
+        print("  (Scope) fails: a variable of A_P or G_P is not a port of N; DELEGATE does not apply"); return None
@@ -141,19 +150,16 @@
-                if pos[cj] > pos[c] and yname in str(term):
+                if pos[cj] > pos[c] and yname in {str(x) for x in syms_of(term)}:
                     term = simplify(substitute(term, (SYM[yname], sj))); changed = True
         return term
-    decode = {}
-    for k, c in enumerate(order):
-        dmap = {}
-        for j in range(k):
-            for v in sigma[order[j]]:
-                e, jj = sigma[order[j]][v], j + 1
-                while jj < k and e in sigma[order[jj]]:
-                    e = sigma[order[jj]][e]; jj += 1
-                dmap[v] = e
-        decode[c] = dmap
+    pts = {c: set(comps[c][0]) | set(comps[c][1]) for c in order}
+    def kappa(v, j, k):                       # Lemma (carriers): v a port of order[j], j < k
+        for jj in range(j, k):
+            if v not in pts[order[jj + 1]]: v = sigma[order[jj]][v]
+        return v
+    decode = {c: {v: kappa(v, j, k) for j in range(k) for v in sorted(pts[order[j]]) if v not in pts[c]}
+              for k, c in enumerate(order)}
@@ -166,6 +172,7 @@
         contracts[c] = And(G) if G else BoolVal(True)
+        assert vars_of(contracts[c]) <= set(comps[c][0]) | set(comps[c][1]), "seed not over ports"
@@ -192,6 +199,14 @@
     print(f"  (C1) after sweep: {valid(Implies(And(AP, *S.values()), GP))}")
+    for c in order:                           # step 9 with the final S_j
+        i_, o_ = comps[c]; others = And([S[j] for j in S if j != c])
+        ports = {V(v, t) for v in set(i_) | set(o_) for t in range(H + 1)}
+        hidden = sorted(allsyms - ports, key=str)
+        A_f = qe(Exists(hidden, And(AP, others))) if hidden else And(AP, others)
+        if not valid(A_f == sweep_out[c][0]):
+            sweep_out[c] = (A_f, sweep_out[c][1]); print(f"    {c}: final A = {fmt(A_f)}")
+    print(f"  (V2) after sweep: {valid(Implies(And(AP, *S.values()), And([sweep_out[c][0] for c in order])))}")
```

Hunk 3 is correct for v in ports(order[j]) \ ports(order[k]): at every step where v leaves the next component's ports,
v lies in priv, so sigma is defined there.

If the patch is applied, the writer must regenerate the verbatim block of Section 9 from the patched script's output.
Also rerun results_report.py, whose assertions are up to equivalence and still pass.

## Items checked and found consistent (no action)

- (E), (Cap), (Pure) and (Info) in step 2 match delegate.py lines 94-99, including the k >= 2 reading of (Info).
- N: writers of G_P plus their ancestors, as in the code's `support`.
- Fresh inputs and terminal outputs match lines 113-117. The prefix order (t, then k) matches line 121.
- Witnesses are taken last-first within a block, on the current psi, as in Lemma 5(b), with default 0.
- sigma pairs the two sets alphabetically (line 99), as in the code (`zip(sorted, sorted)`).
- Step 6 replaces only later components' terminal outputs, as in the code (setting aside m2).
- The step 8 formula forall hid(R_k -> G_P), with R_k = A_P & AND_{j != k} S_j over all components, matches line 191.
  The code stores S = G or not A, which is equivalent: not(exists X R) entails forall X (R -> G).
- The receptive-and-causal check is exactly the alternation stated at line 165.
- The fan-in "(E) fails" claim holds: neither topological ordering of {A, B, Fuser} has the edge A -> B or B -> A.
- The refutation's output label "(Lemma 1)" is mapped correctly at line 165.
