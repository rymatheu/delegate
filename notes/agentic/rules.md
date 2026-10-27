# The author's inference rules and the verifier's constraints (2026-10-21)

Source: the author's set-theoretic notes (behaviours as sets, `M |= (A,G)` iff `M ∩ A ⊆ G`), four inference rules,
and the two-component scheme `∃A1 ⊇ A, ∃G1,A2: G1 ⊆ A2, ∃G2: G2 ∩ A2 ⊆ G, M1 |= (A1,G1), M2 |= (A2,G2)`.
Checked pointwise by `rules_check.py` (Z3, 15 statements, exit 0).

## Findings on the notes
1. Lemma (simplified refinement) is correct in both directions, and the hypothesis "A2 nonempty" is not needed:
   `A2 ⊆ A1` already makes `¬A1 ∩ A2` empty, which is all the (→) direction uses.
2. Composition rule, as typed: the premise reads `G1 ⊆ A1`; the proof uses `G1 ⊆ A2`, which is the right one
   (with `G1 ⊆ A1` the rule is false; Z3 gives a counterexample). The conclusion reads `M1 || M1`, meaning `M1 || M2`.
   The corrected rule also follows from the composition operator plus refinement: `(A1∩A2 ∪ ¬(G1∩G2), G1∩G2) ⪯ (A1, G2)`
   holds exactly when `G1 ⊆ A2` is available.
3. Typo `A-2` for `A_2` in the (←) proof of the lemma.
4. The last step of the scheme is not Guarantee Tightening alone: that rule needs `G2 ∩ A ⊆ G`, the scheme gives
   `G2 ∩ A2 ⊆ G`. The step closes because every behaviour of `M1 ∩ M2 ∩ A` lies in `G1 ⊆ A2`. The scheme is valid.

## Relation to the plan's constraints (docs/plan.tex, Section 2)
With `S_i := ¬A_i ∪ G_i`, the plan's checks for two components are
(V1) `A ∩ S1 ∩ S2 ⊆ G`, (V2) `A ∩ S1 ∩ S2 ⊆ A1` and `⊆ A2`.
- The scheme implies (V1) and (V2) (checked). So a proposal that meets the scheme passes the verifier.
- The converse fails: (V1), (V2) do not imply `G1 ⊆ A2` (checked). The scheme's edge condition is the
  *context-free* form `G1 ⊆ A2`; the verifier's form is `A ∩ G1 ⊆ A2` (relative to the top assumption and the
  other saturated sets). The context-free form is what makes a check *local to one edge*, so it is the better
  rule for an agent to target; the verifier can accept it as a sufficient condition and fall back to (V2).
- (V1), (V2) alone already give `M1 || M2 |= (A, G)` (checked); the inference-rule route and the saturated route
  prove the same conclusion.

## What the rules do not yet cover (needed for the graph case)
- Feedback. The scheme is a chain (1 feeds 2). With a cycle, `G1 ⊆ A2` and `G2 ⊆ A1` together are circular; the
  plan resolves this with saturation plus receptiveness (R) and causality (K), which the rules do not mention.
- Port locality. `A_i, G_i` must be over `ports(i)`; `G1 ⊆ A2` is then an inclusion of cylinders over the full
  behaviour set, and only the shared variables matter. (C1) in the plan.
- More than two components. The edge rule generalises to `⋂_{j feeds i} G_j ⊆ A_i` per component, or in the
  relative form `A ∩ ⋂_{j≠i} S_j ⊆ A_i` = (V2). Variables written by no component are covered by `A`.
- Selection. The existential quantifiers in the scheme are exactly what the proposers fill in; nothing in the
  rules picks a largest or canonical choice (no greatest acceptable delegation, complete.tex).
