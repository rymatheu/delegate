# 4. Harnesses compose like contracts

**Status (2026-11-18):** the algebra is formalized in `Harness/Algebra.lean` (core Lean 4.35, 34 theorems, no `sorry`) and written up in two pages, [harness-algebra.pdf](harness-algebra.pdf): contracts, the harness as a triple, evidence trees read under a trust policy, the operations below, the loop rule for feedback, and a plan for decomposing the tube theorem. The runner builds composites by these operations (`Harness/Compose.lean`, doc 9); the formal link from a running composite to the algebra is built in `Harness/Link.lean`, which instantiates the loop rule for the runtime's semantics (doc 10).

A harness is a triple: implementation, contract, evidence. The contract algebra lifts to these triples. The contract composes as in the theory; the implementation and the evidence are carried along.

| Operation | Implementation | Contract | Evidence |
|---|---|---|---|
| Compose | the executables wired together, run by a sub-schedule | the children's contracts composed, internal wires hidden | derived: the children's evidence plus a Lean proof that their composition refines the composite's stated contract |
| Refine | unchanged | a weaker contract | the old evidence plus a Lean refinement proof |
| Swap | a different implementation | unchanged | new leaf evidence only; everything above is untouched |
| Conjoin | unchanged | two contracts on one module (say safety and tracking) | one record per clause |
| Quotient | none yet | what the missing part must satisfy, given the system contract and the known parts | none; it is the specification of a module still to be harnessed |

## A harness inside a harness

A system of modules is itself a module: it answers `describe`, `init` and `step`, and its `step` runs its internal schedule once. So a composite can be a child of a larger harness.

- **Contract.** The parent sees only the composite's stated contract. A Lean proof inside the composite shows the children's contracts imply it.
- **Evidence is a tree.** Each node holds a refinement proof and points to its children. The leaves hold model-checker, test and monitor records.
- **Strength.** A composite is as strong as its weakest child. It is proved only if every child is proved and the refinement is proved.
- **Hashes.** A composite's code hash is the hash of its children's hashes and its wiring. A change in a leaf makes that leaf's evidence stale and marks the derived status of every ancestor stale. The refinement proofs stay valid: they do not mention code.
- **Monitors stay on inside.** Hiding removes internal ports from the interface, not from observation. A violation is reported at the smallest module that failed.
- **Direct evidence is allowed too.** A composite can be tested as a unit against its own contract. That is a second, independent support; a disagreement between the two localizes a fault.

## Conditions for soundness

1. **No instantaneous loops.** Within a tick the schedule is acyclic; feedback passes through the plant or a one-tick delay. The delay is also what makes circular assume-guarantee reasoning valid, by induction over ticks.
2. **Assumptions are discharged in the refinement proof.** Each child's assumption follows from its siblings' guarantees or from the composite's assumption.

## Relation to delegation

Decomposing a harness means finding child contracts whose composition refines the parent's contract. That is delegation of a contract over a known architecture. Composing harnesses is the same statement read from the bottom up.
