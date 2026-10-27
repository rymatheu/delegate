# Scope guard (read first)

IN SCOPE
- Inputs: architecture graph G = (components, distinct labelled ports with a known owner, read/write map,
  optional unit delays) and a
  global PolySTL contract P = (A_P, G_P) over all system variables. Nothing else.
- Output: for each component i a contract (A_i, G_i) whose formulas mention only ports(i) = in(i) ∪ out(i),
  such that any components meeting their contracts make the composed system meet P.
  Components not needed get the trivial contract (true, true).
- The decomposition must be ALGEBRAIC/constructive: an operator or procedure that takes (G, P) and
  returns the per-component contracts, choosing canonically from (G, P) alone.
- Semantics: discrete time, bounded horizon [0,H] for now (unbounded is a stretch goal), free trajectories
  (no dynamics), real-valued variables with NO numeric range bounds ('typed' = distinct and assigned to a known
  component), PolySTL predicates are polytopes over the full variable vector.

OUT OF SCOPE (do not drift here)
- Component models, dynamics, plant identification, refinement modulo dynamics.
- Risk, probability, statistical evidence, testing budgets.
- Repair of existing component contracts (there are none).
- Lean formalization (later).
- MILP control synthesis / trajectory planning.
- Hypercontracts, probabilistic contracts, cost allocation beyond what is needed to pick one delegation.

PROVENANCE
- Everything in this directory is derived here from first principles. Do not copy or cite files from other
  projects. The definitions and proofs live in docs/decomposition.tex; the design is notes/algorithm-spec.md.
