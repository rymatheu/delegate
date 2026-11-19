# 7. Open questions

Decisions not yet made.

1. **Name.** `harness` is a working name for this directory.
2. **The contract expression language.** A first version exists (doc 8): arithmetic, `abs`, comparisons, Boolean connectives and `finite`, evaluated in binary32. Integer fields are read as binary32, which is exact only below 2^24. How much temporal structure (previous tick only, or bounded windows) is open. It should match the contract algebra already formalized for delegation.
3. **Where the contract algebra lives.** Settled for the algebra itself (2026-11-18): `Harness/Algebra.lean` restates it in core Lean 4.35 with sets as predicates. Still open: the link from the runner's clause language (`Harness/Expr.lean`, evaluated in binary32) to the sets used there, and the STL layer of the older formalization.
4. **Empirical evidence, quantified.** Whether to add a statistical reading of test campaigns (a bound on the violation rate at a stated confidence), and what the sampling unit is, since inputs within one flight are not independent.
5. **Two-execution contracts.** Sensitivity contracts compare two runs of a module. They are needed for the tube; the harness needs a way to run and check pairs.
6. **Multi-rate modules.** Whether every module runs every tick, or the schedule carries rates.
7. **Model checker.** Which tool, and whether its C++ front end accepts ArduPilot's sources. Untested. The rate PID module gives a first target: four ArduPilot sources plus the stubs.
8. **State snapshots.** Which modules can support `save` / `load`, and what is lost for those that cannot.
9. **How the monolith is instrumented** to record ports for the replay test (step 2 of the order of work).
10. **Repository.** Decided: this directory is the subproject `harness/` of the flight-stacks repository, beside the shared simulator `sim/`.
11. **What the code hash leaves out.** It covers every file the compiler read, the flags and the compiler version. It does not cover the dynamically linked system libraries (libc++, and the math library, whose `expf` the slew limiter calls) or the harness itself. Whether to pin a math library (as the cpp2lean reference build does with musl) is open.
12. **What a test campaign covers.** The generator mixes edge values, values next to the assumption's bounds and seeded random values. Each result file records the outputs' ranges, but there is no coverage measure of the code, and no statistical reading (question 4).
13. **Ledger history.** The ledger is append-only, and status counts every record that matches the current hashes. Whether old records should be pruned, and whether a failing record should outweigh later passing ones for the same hashes (it does now), is a policy to settle.
