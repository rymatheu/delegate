# 1. The idea

## Goal

Prove system-level properties of a flight controller, such as "with bounded sensor noise the vehicle stays within a computed distance of its planned trajectory", for the real C++ code.

## Approach

1. **Partition.** Cut the C++ into modules along the control cascade. Each module has parameters, inputs and outputs.
2. **Wrap.** Give each module a Lean harness: its ports, a contract, a runtime monitor, and a record of evidence.
3. **Run.** Lean executes the modules in lock-step in the closed loop with the plant.
4. **Compose.** Lean proves that the module contracts and the plant's contract imply the system contract. No code appears in that proof.

This is the meta-theory of contracts applied to code: once a module is shown to satisfy its contract, the contract stands in for the module in everything above it.

## What is formal and what is not

The composition is a Lean theorem. It has the form: if every module satisfies its contract, the system contract holds. Each "module satisfies its contract" is a named hypothesis.

Lean cannot see inside C++, so each hypothesis is backed by evidence of one of four kinds:

| Kind | Backed by | A proof? |
|---|---|---|
| Proved | a model checker on the module's source: assuming the invariant and the input assumption, one step gives the guarantee and the invariant | yes, trusting that tool |
| Tested | the module run alone on generated inputs that satisfy its assumption | no |
| Monitored | the contract checked on every tick of closed-loop flights | no |
| Assumed | nothing | no |

The final claim is the theorem together with a ledger that says, hypothesis by hypothesis, which kind of evidence backs it. A test is never promoted to a proof.

## Why not translate the code

Translating ArduCopter to Lean was done (ArduLean). It gives proofs about the translation, function by function, but reaching a system-level property that way means proving facts about several hundred functions. Contracts let the proof effort go where it pays: the composition, and the small numeric modules.

## What this costs

- The decomposed vehicle is the real components in a new arrangement. That it behaves like the stock vehicle is a tested claim, tick by tick against the monolithic build.
- The modules that matter most for noise (the estimator) are the ones least likely to be proved; their contracts will be empirical.
