# Plant: the X500 plant as a Lean library

The plant is the vehicle's continuous dynamics, an ODE `ẋ = F(x, u)` over the reals on `X = Fin 17 → ℝ` (position,
velocity, body-to-NED quaternion, body rates, and the four normalized propeller thrusts; NED/FRD), with the four
commands held constant over each 1/400 s period and each propeller's thrust following its command through the
simulator's first-order lag (time constants 12.5 ms up, 25 ms down); `step x u` is the exact flow over one period.
The vehicle is the X500 as gym-pybullet-drones simulates it for the gorge flights (`../sim/world/x500/x500.urdf`,
`../sim/world/airframes.py`, `sim/fly_gorge.py`; `Physics.PYB`, no wind). `MODEL.md` states the model, its
constants and their sources, and what the simulator does that the ODE does not. The library imports nothing from
the flight code or its corpus (`PLAN.md`).

It is the library `Plant` of the repository's Lake project (Lean `v4.35.0`, Mathlib `v4.35.0`), with DynamicalSystems at
`c2a753b` (global flow of Lipschitz fields, radial truncation, discrete flows).

## Build and checks

From the repository root:

```
lake exe cache get                                        # Mathlib's build products (once)
LEAN_NUM_THREADS=1 lake build Plant                       # the library, about 1.5 min after the cache
LEAN_NUM_THREADS=1 lake env lean tests/plant/PlantAudit.lean   # rules 3 and 4, coverage table (LEDGER.md)
LEAN_NUM_THREADS=1 lake env lean tests/plant/AxiomCheck.lean   # #print axioms of the main theorems
bash tests/plant/check_model_frozen.sh                    # Plant/Model/*.lean against MODEL.sha256
PYTHONDONTWRITEBYTECODE=1 .venv/bin/python tests/plant/check_constants.py   # Constants.lean against the sources
PYTHONDONTWRITEBYTECODE=1 .venv/bin/python tests/plant/numcheck.py          # (a) model checks, (b) model vs simulator
```
`tests/plant/numcheck.py --model` runs part (a) only (plain `python3` suffices).

## Layout

| path | content |
|---|---|
| `Plant/Model/` | `Constants.lean` (X500 constants with sources, the facts of the numbers), `Field.lean` (state, frames, motor slots, the lag, the field `vf`); frozen |
| `Plant/Lib/` | model-free lemmas: `Real.lean` (derivative bounds, Taylor), `Blocks.lean` (block bounds and block maps of `Fin 17 → ℝ`, `qnormSq`, rotation columns, `posVec`, `yawRot`), `RadialTrunc.lean`, `Gronwall.lean` (comparison with a supersolution, the integrals `lagM0`…`lagM3` of the lag's step response, `e^{-1/5}`) |
| `Plant/Field/` | `Motor.lean` (the lag: max form, Lipschitz, exact flow `lagSol`, the simulator's update `simLag`, range, sharp sensitivity, integrals `lagK1`…`lagK4`), `Bounds.lean` (force, torque, block and Lipschitz bounds), `Invariants.lean` (`‖q‖²`, energy, thrust growth, the one-period box), `Actuators.lean` (thrust-to-wrench map, its inverse, image, command dependence) |
| `Plant/Flow/` | `Flow.lean` (truncated flow, `traj`, `step`, uniqueness, Grönwall, hover), `Motor.lean` (the thrust block of the flow is the exact lag; range invariant; thrust sensitivity), `Sensitivity.lean` (joint Grönwall in state and command, continuity) |
| `Plant/Step/` | `Euler.lean`, `Sharp.lean` (the step against Euler; sharp translation step with the lagged thrust in closed form; attitude block), `InputSens.lean` (sharp block-wise command sensitivity), `Integral.lean` (position and velocity rows as integrals), `Sample.lean` (plant state, real sample, runs, hover), `Exact.lean` (yaw spin and level flight with the thrust transient, free fall, hover characterization), `Symmetry.lean` (translation, yaw rotation), `Period.lean` (per-period bounds), `Multi.lean` (several periods), `Numbers.lean` (evaluated X500 constants and bounds) |
| `tests/plant/` | `PlantAudit.lean`, `AxiomCheck.lean`, `check_model_frozen.sh`, `check_constants.py`, `numcheck.py` |

## Other files

* `PLAN.md`: the rules, the layout, the kinds of property.
* `MODEL.md`: the model, its constants with sources, what the simulator does that the ODE does not, the measured gap.
* `LEDGER.md`: the audit's summary and the per-constant coverage by kind.
* `OPEN.md`: what was left out for the mid level, and unproved statements.
* `FINDINGS.md`: findings of the port and of the checks.
* `MODEL.sha256`: hashes of `Plant/Model/*.lean`.
