# Brief for the document "Computing local delegations: the complete procedure"

Audience: a formal-methods researcher (contracts, STL, SMT) who distrusts hand-waving, has not read any other
file, and will try to reproduce every claim. He has said the earlier drafts were incomprehensible, concealed
steps, used undefined notation, and "pulled functions out of thin air".

Hard requirements
1. FIVE PAGES MAXIMUM (10pt or 11pt, normal margins). Self-contained: every symbol defined before use, in this
   document; no reference to any other document for a definition or a proof.
2. Plain words first, then the symbol. Never introduce a term without saying what it is (the author objected to
   "support", "topological ordering", "column", "graph of a function", "E_k(t)" appearing without explanation).
3. The problem must be stated as the author stated it: a graph of components with labelled inputs/outputs
   ("typed" = distinct variables with a known owner; NO numeric range bounds), a global PolySTL query contract
   (atoms are polytopes A x <= b over the full state vector), decompose it ALGEBRAICALLY into one contract per
   component mentioning only that component's inputs/outputs, such that the composition refines the query; only
   some components get a non-trivial contract; only the graph and the query are given; no component models.
   Only valid contract operations (refinement, composition, quotient, projection) may be used in the algebra.
4. Derive, do not assert: (a) the validity conditions A_P ∧ ⋀S_i ⊨ G_P and A_P ∧ ⋀S_i ⊨ A_j from the definitions
   of saturation, composition and refinement (full set-algebra derivation); (b) why validity alone is empty and
   why receptiveness/causality must be added; (c) why the solution set has no greatest element, hence a
   selection is needed; (d) the quantifier-elimination-with-witnesses lemma for linear real arithmetic with
   proof (cases, interval bounds, Fourier–Motzkin, witness = midpoint/endpoint±1/0, graph of the witness is a
   formula of the language); (e) forwarding and decoding (carrier lemma); (f) the procedure as numbered steps
   each naming the exact operation; (g) necessity, soundness, sweep-maximality theorems with complete proofs;
   (h) the exact class where this is complete (nested orderings: chain edges, capacity, pure edges, info
   condition) and what happens outside it (branching quantifiers; the semi-decision procedure; delays
   inexpressible in PolySTL), stated honestly with no overclaim.
5. One fully worked instance (the relay: Radio r→m, Display m→d, A_P = |r| ≤ 1, G_P = |d − r| ≤ 1/2) carried
   through every step with every elimination written out, matching scripts/delegate.py output exactly.
   A second, short instance showing a disjunctive query and one showing a refutation (unrealizable query) may
   be summarized from docs/results.pdf numbers.
6. Reproducibility: state the one command `.venv/bin/python scripts/delegate.py` and what it prints for the relay.
   Every number in the document must be one the script prints or one derived in the text.
7. Banned: EARS, prior, template, band, decider, flag, ghost, Hoare, interpolant, network coding, quantizer,
   capacity theorem, orchestrator, agent, "the notes", "column" (say "the value of v at time t" / "v(t)"),
   any path outside this directory. Allowed: "support" only if defined in the same sentence; prefer plain words.
8. Style: short sentences; one idea per sentence; theorems and proofs in standard environments; no em-dashes;
   no marketing; no claims beyond what is proved; label conjectures as such.

Sources (read all; they are the only sources; they are internally consistent except as noted):
- docs/procedure.tex (current 3-page version; the closest to the target but criticized as unclear)
- docs/existence.tex (derivation of validity conditions; existence vs construction)
- docs/algorithm.tex (the class, the sentence, the algorithm; DEFINITIONS of E_k(t), Y_k(t), nested ordering)
- docs/results.tex (verified numbers for six instances)
- scripts/delegate.py (the implementation; run it), scripts/results_report.py
- SCOPE.md (scope and provenance rules)
Do NOT read notes/round1-archive/ or docs/decomposition.tex (superseded, contains banned vocabulary and an
earlier, different method).
