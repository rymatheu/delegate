# delegate — algebraic decomposition of a global PolySTL contract over an architecture graph

## The problem (verbatim scope, do not widen or narrow)

We have a system which is a graph of components where each component has labeled/typed
inputs and outputs ("typed" means the variables are distinct and each is assigned to a known
component; there are no numeric range bounds). We have a global query contract written in PolySTL (polytopic signal
temporal logic: STL whose predicates are convex polytopes over the state variables,
mu(x) := A x <= b, where x is the vector of ALL system variables).

We need to ALGEBRAICALLY DECOMPOSE the global contract into obligations for the components.
The delegate contract handed to a component may ONLY reference the variables that component
has available, i.e. its own inputs and outputs.

Only some components will receive a (non-trivial) delegated contract: not every global
contract needs every component.

All that is available is: (1) the architectural graph (components, typed/labelled ports,
who reads/writes which variable), and (2) the top-level query contract. No component models.

How it is done is open. It must be done.

## Deliverable
- docs/complete.pdf  (source docs/complete.tex): the problem, the contract operations, the validity conditions,
  elimination with witnesses, forwarding, the procedure in numbered steps, its correctness theorems, the relay
  worked through every step, and the scope and limits.
- scripts/delegate.py: the procedure of docs/complete.tex, executable (about 2 s). It prints the Z3 version, every
  step for each instance, the verdicts (V1), (V2), receptive & causal, and the regression instances from review;
  it exits 0 iff every verdict is as expected. Reproduce everything with ONE command from this directory:
      .venv/bin/python scripts/delegate.py
- scripts/results_report.py: reruns the instances and writes docs/results.tex (summary tables).

## Layout
- docs/      the documents (complete.tex is the current one; decomposition.tex and scripts/decompose.py are an
             earlier, superseded method)
- scripts/   delegate.py (the deliverable), results_report.py, arxiv_tool.py (literature helper)
- lit/       literature survey and BibTeX (existing-work.md / .bib)
- notes/     algorithm-spec.md, STATUS.md,
             round1-archive/ (an earlier, superseded exploration; not part of the deliverable)

This directory is original work. Nothing is imported from other projects.

## Tooling
.venv/ here has z3-solver (5.3.1; the printed clause order depends on the version), numpy, scipy (`uv venv && uv pip install -p .venv/bin/python z3-solver==5.3.1.0 numpy scipy`).
LaTeX: `cd docs && latexmk -pdf complete.tex` (and `results.tex`).

## arXiv (blazickjp/arxiv-mcp-server)
Registered at project scope in .mcp.json (storage: lit/papers/). Native MCP tools appear after the next
Claude Code session start (approve the server when prompted). Until then, and from any shell:
    uv run --with mcp python scripts/arxiv_tool.py list
    uv run --with mcp python scripts/arxiv_tool.py search_papers '{"query":"...","max_results":10}'
    uv run --with mcp python scripts/arxiv_tool.py get_abstract '{"paper_id":"2103.13743"}'
    uv run --with mcp python scripts/arxiv_tool.py download_paper '{"paper_id":"2103.13743"}'
    uv run --with mcp python scripts/arxiv_tool.py export_citations '{"paper_ids":["2103.13743"]}'

**Lean check of the inference rules.** `lean/Contracts.lean` (core Lean 4.35, no Mathlib) defines unsaturated contracts, implementation and refinement over sets of behaviours (no contract operations), proves the simplified refinement lemma, the four rules (Refinement, Composition, Assumption Relaxation, Guarantee Tightening), and the two-component delegation theorem from the rules alone. `lean/Composition.lean` adds saturation, composition of (saturated) contracts, and proves that under the scheme's hypotheses the composition of the saturated delegates refines `(A, G)`, that implementations compose, and the delegation theorem a second way. `lean/Chain.lean` proves the n-component chain theorem (`chain_delegation`: `A ⊆ A₁`, `Gᵢ ⊆ Aᵢ₊₁`, `Gₙ ∩ Aₙ ⊆ G` give `M₁ ∥ ⋯ ∥ Mₙ ⊨ (A, G)`) by induction with the rules. Build with `cd lean && lake build`.
