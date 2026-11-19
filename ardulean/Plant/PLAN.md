# The plant library

## What this is

The plant is the vehicle's continuous dynamics: an ODE `ẋ = F(x, u)` over the reals, with the four actuator commands held constant over each control period and each propeller's thrust following its command through a first-order lag. This package holds the plant's definitions and a library of theorems about them, built bottom-up, in the same way `Corpus/` is built on the translated code. The two are separate for now. Later a mid-level library will import both and state how the code and the plant interact; high-level proofs will use only that mid level.

The plant is a library of the same Lake project as the flight code and its corpus (`lakefile.toml` at the repository root), so the later merge needs no toolchain or dependency change.

The vehicle is the X500 as simulated (`MODEL.md`); the state is 17 reals (rigid body and the four lagged propeller thrusts). The theorems were first written for the archived plant (`archive/contracts/Contracts/Plant/`) and carried over to this model on 2026-11-16.

## Rules

1. **Separate.** Nothing here imports the flight code or its corpus (no `ArduLean.*`, no `Corpus`, no FloatLib), and nothing here imports the archive (no `Contracts.*`, no `FloatModel`). The plant is real-valued. Floats, sensing ports, contracts and missions belong to the later mid level.
2. **The model is the definitions.** `Plant/Model/` holds the constants (each with its source) and the vector field. Once the port builds, these files are recorded in `MODEL.sha256` and are not edited as part of proving; a change to the model is a separate, announced step.
3. **A theorem names the model.** Every theorem outside `Plant/Model/` and `Plant/Lib/` has a model constant (the field, the flow, the step, a force or torque map) in its statement. Model-free mathematics goes in `Plant/Lib/`.
4. **Nothing unproved.** No `sorry`, `admit`, `axiom`, `native_decide`. Only `propext`, `Classical.choice`, `Quot.sound`. A statement that cannot be proved yet goes in `OPEN.md` with what blocks it.
5. **Check before proving.** A candidate statement with numbers in it is checked numerically first (a short script against the simulator's equations, or a hand evaluation recorded in the test file). A statement that fails goes in `FINDINGS.md` with its witness.
6. **Constants are traceable.** Every number in `Plant/Model/Constants.lean` cites where the simulator defines it. `tests/plant/check_constants.py` compares them with the simulator.

## Layout

```
Plant.lean
Plant/
  Model/     Constants.lean  Field.lean            the definitions: constants, state, vector field
  Lib/                                             model-free lemmas (norms on Fin n → ℝ, Grönwall forms, …)
  Field/     Motor.lean  Bounds.lean  …            properties of the vector field
  Flow/      Flow.lean  Motor.lean  …              the flow: existence, uniqueness, dependence on data
  Step/      Sharp.lean  InputSens.lean  …         the one-period step under zero-order hold
  PLAN.md  MODEL.md  LEDGER.md  OPEN.md  FINDINGS.md  MODEL.sha256
tests/plant/   AxiomCheck.lean  PlantAudit.lean  check_model_frozen.sh  check_constants.py  numcheck.py
```

## Kinds of plant property

| kind | says | example |
|---|---|---|
| Algebra | an identity of the field or of the force and torque maps | thrust is linear in the clipped thrusts; the field is equivariant under yaw rotation |
| Range | a bound on a force, torque or acceleration | `0 ≤ T/m ≤ amax` |
| Regularity | continuity, Lipschitz or differentiability | the field is Lipschitz on a ball with an explicit constant |
| Invariant | a quantity or set the flow preserves | `‖q‖²` is constant along solutions |
| Existence | the flow exists, is unique, composes | `step` is the unique solution's value at `h` |
| Sensitivity | how the solution moves with the initial state or the held input | `‖step x u - step y w‖ ≤ L ‖x - y‖ + K ‖u - w‖` |
| Exact | a closed form | the thrust block is the exact lag; the `p` and `v` rows are integrals; hover is the only rest equilibrium |
| Step | a bound on one period | `step` against the Euler step; per-block change over one period |

## Measure of progress

`LEDGER.md`: per model constant, the kinds of theorem proved about it, written from `tests/plant/PlantAudit.lean`.
