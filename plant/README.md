# plant: the quadrotor plant as a Lean library

The plant is the vehicle's continuous dynamics, an ODE `ẋ = F(x, u)` over the reals on `X = Fin 13 → ℝ`
(position, velocity, body-to-NED quaternion, body rates; NED/FRD), with the four actuators held constant over each
1/400 s period; `step x u` is the exact flow over one period. The vehicle is the Crazyflie 2.x as gym-pybullet-drones
simulates it for `sim/run_copter.py` (`Physics.PYB`). This package carries the archived plant
(`archive/contracts/Contracts/Plant/`, Lean 4.36-rc2) over to Lean 4.35 and adds a library of theorems about it. It
imports nothing from `lean/` or `archive/` (`PLAN.md`).

Toolchain `leanprover/lean4:v4.35.0`, Mathlib `v4.35.0` (`56a00585…`, the revision of `lean/`), DynamicalSystems at
`c2a753b` (global flow of Lipschitz fields, radial truncation, discrete flows).

## Build and checks

```
cd plant
lake exe cache get                                  # Mathlib's build products (once)
LEAN_NUM_THREADS=1 lake build                       # the library, about 1 min after the cache
LEAN_NUM_THREADS=1 lake env lean tests/PlantAudit.lean   # rules 3 and 4, coverage table (LEDGER.md)
LEAN_NUM_THREADS=1 lake env lean tests/AxiomCheck.lean   # #print axioms of the main theorems
bash tests/check_model_frozen.sh                    # Plant/Model/*.lean against MODEL.sha256
python3 tests/check_constants.py                    # Constants.lean against cf2x.urdf and run_copter.py
python3 tests/numcheck.py                           # numerical check of the phase-3 statements
```

## Layout

| path | content |
|---|---|
| `Plant/Model/` | `Constants.lean` (constants with sources), `Field.lean` (state, frames, motor slots, the field `vf`); frozen |
| `Plant/Lib/` | model-free lemmas: `Real.lean` (derivative bounds, Taylor), `Blocks.lean` (block bounds, `qnormSq`, rotation columns, `posVec`, `yawRot`), `RadialTrunc.lean` |
| `Plant/Field/` | `Bounds.lean` (force, torque, Lipschitz bounds), `Invariants.lean` (`‖q‖²`, energy, the one-period box), `Actuators.lean` (mixer, its inverse, image, input Lipschitz) |
| `Plant/Flow/` | `Flow.lean` (truncated flow, `traj`, `step`, uniqueness, Grönwall, hover), `Sensitivity.lean` (state and input sensitivity, continuity) |
| `Plant/Step/` | `Euler.lean`, `Sharp.lean` (the step against Euler, sharp block bounds, evaluated constants), `Sample.lean` (plant state, real sample, runs, hover), `Exact.lean` (yaw spin, level flight, free fall), `Symmetry.lean` (translation, yaw rotation), `Period.lean` (per-period bounds), `Multi.lean` (several periods) |
| `tests/` | `PlantAudit.lean`, `AxiomCheck.lean`, `check_model_frozen.sh`, `check_constants.py`, `numcheck.py` |

## Other files

* `PLAN.md`: the rules, the layout, the kinds of property.
* `LEDGER.md`: the audit's summary and the per-constant coverage by kind.
* `OPEN.md`: what was left out for the mid level, and unproved statements.
* `FINDINGS.md`: findings of the port and of the checks.
* `VEHICLES.md`: which vehicle each recorded flight uses, the X500 as simulated, what in `Plant/` depends on CF2X
  numbers.
* `MODEL.sha256`: hashes of `Plant/Model/*.lean`.
* The archive's `PLANT.md` (`archive/contracts/PLANT.md`) still describes the carried-over definitions and theorems;
  names are unchanged, the namespace is `Plant` instead of `Contracts.Plant`.
