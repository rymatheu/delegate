# The plant library

## What this is

The plant is the vehicle's continuous dynamics: an ODE `ẋ = F(x, u)` over the reals, with the four actuators held constant over each control period. This package holds the plant's definitions and a library of theorems about them, built bottom-up, in the same way `lean/Corpus/` is built on the translated code. The two are separate for now. Later a mid-level library will import both and state how the code and the plant interact; high-level proofs will use only that mid level.

Everything is on Lean `v4.35.0` with the same Mathlib revision as `lean/` (`lean/lake-manifest.json`), so the later merge needs no toolchain change.

The starting point is the plant of the archived package `archive/contracts/Contracts/Plant/` (Lean `v4.36.0-rc2`), carried over here.

## Rules

1. **Separate.** Nothing here imports `lean/` (no `Vehicle_lib`, `Estimator_lib`, `Corpus`, FloatLib), and nothing here imports the archive (no `Contracts.*`, no `FloatModel`). The plant is real-valued. Floats, sensing ports, contracts and missions belong to the later mid level.
2. **The model is the definitions.** `Plant/Model/` holds the constants (each with its source) and the vector field. Once the port builds, these files are recorded in `MODEL.sha256` and are not edited as part of proving; a change to the model is a separate, announced step.
3. **A theorem names the model.** Every theorem outside `Plant/Model/` and `Plant/Lib/` has a model constant (the field, the flow, the step, a force or torque map) in its statement. Model-free mathematics goes in `Plant/Lib/`.
4. **Nothing unproved.** No `sorry`, `admit`, `axiom`, `native_decide`. Only `propext`, `Classical.choice`, `Quot.sound`. A statement that cannot be proved yet goes in `OPEN.md` with what blocks it.
5. **Check before proving.** A candidate statement with numbers in it is checked numerically first (a short script against the simulator's equations, or a hand evaluation recorded in the test file). A statement that fails goes in `FINDINGS.md` with its witness.
6. **Constants are traceable.** Every number in `Plant/Model/Constants.lean` cites where the simulator defines it. `sim/check_constants.py` compares them with the simulator.

## Layout

```
plant/
  lean-toolchain  lakefile.toml  lake-manifest.json
  Plant.lean
  Plant/
    Model/     Constants.lean  Field.lean            the definitions: constants, state, vector field
    Lib/                                             model-free lemmas (norms on Fin n → ℝ, Grönwall forms, …)
    Field/     Bounds.lean  Invariants.lean  …       properties of the vector field
    Flow/      Flow.lean  …                          the flow: existence, uniqueness, dependence on data
    Step/      Euler.lean  Sharp.lean  Sample.lean   the one-period step under zero-order hold
  tests/       AxiomCheck.lean  PlantAudit.lean  check_model_frozen.sh
  PLAN.md  LEDGER.md  OPEN.md  FINDINGS.md  MODEL.sha256
```

## Kinds of plant property

| kind | says | example |
|---|---|---|
| Algebra | an identity of the field or of the force and torque maps | thrust is linear in the clipped commands; the field is equivariant under yaw rotation |
| Range | a bound on a force, torque or acceleration | `0 ≤ T/m ≤ amax` |
| Regularity | continuity, Lipschitz or differentiability | the field is Lipschitz on a ball with an explicit constant |
| Invariant | a quantity or set the flow preserves | `‖q‖²` is constant along solutions |
| Existence | the flow exists, is unique, composes | `step` is the unique solution's value at `h` |
| Sensitivity | how the solution moves with the initial state or the held input | `‖step x u - step y w‖ ≤ L ‖x - y‖ + K ‖u - w‖` |
| Exact | a closed form | the `p` and `v` rows integrate exactly; hover is an equilibrium; level flight is vertical |
| Step | a bound on one period | `step` against the Euler step; per-block change over one period |

## Measure of progress

`LEDGER.md`: per model constant, the kinds of theorem proved about it, written from `tests/PlantAudit.lean`.
