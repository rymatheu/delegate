# Open items of the plant library

## For the mid level (left out of this library on purpose)

These archive declarations relate the plant to floats, sensing ports, the contract library or the port's Euler-angle
plant. They are not in `plant/` because the plant imports nothing from `lean/` or the archive and is real-valued
(`PLAN.md`, rule 1). Their real-valued content is here where it exists.

From `archive/contracts/Contracts/Plant/Quadrotor.lean`:

| left out | what it is | needs | real-valued counterpart here |
|---|---|---|---|
| `Vector3f`, `Vector3p`, `Quaternionf`, `Sample` | the float sample of a tick (`Float32`/`Float` fields) | the controller's float types | `SampleR` |
| `act` | reading of `Float32` actuators (`Float32.toReal`, clipped) | `FloatModel.Float32` | `nextR` takes real thrust fractions |
| `next`, `plant` | the float plant step and the plant with visible state | `act`, `Sample` | `nextR`, `sampleR` |
| `Sense32Spec`, `SensePSpec`, `CopterSense` | hypotheses on the `float`/`double` sensing ports | `FloatModel` (`IsFinite`, `toReal`) | none |
| `sample` | the float sample through the ports | the ports | `sampleR` |
| `CX`, `Mplant`, `mem_Mplant` | the closed-loop universe and the lifted plant component | `Contracts.Lift.liftStep` | `IsRun` |
| `Mplant_flow`, `Mplant_qnormSq`, `Mplant_const` | ODE solution per tick, `‖q‖²` per tick, constant actuators | `Mplant` | `run_flow`, `run_qnormSq`, `run_const` (and `run_stepN`) |
| `sample_hover` | the float sample of hover | ports | `sampleR_hover` |

From `archive/contracts/Contracts/Plant/Euler.lean`:

| left out | what it is | needs |
|---|---|---|
| `eulerStep_pv_quatOf` | the `p`, `v` rows of `eulerStep` at a state with attitude `quatOf roll pitch yaw` are the rows of the port's Euler-angle plant `dynR` | the port's `dynR` (not in this repository's `lean/`); the statement itself is about `eulerStep` only and could come back as a plant lemma if wanted |

Kept here as plant geometry (their docstrings no longer mention the port): `quatOf`, `thrustDir`, `normSq_quatOf`,
`downAxis_quatOf`.

## Unproved statements

| statement | blocks |
|---|---|
| Multi-period sensitivity: `‖stepN us n x - stepN ws n x‖ ≤ K_n · sup_k ‖us k - ws k‖` | an a priori radius over `n` periods: each period's bound (`norm_step_sub_step_le`) needs a ball containing both states, and `box` grows with the radius each period (`box r ≥ r + h(g + 4 amax r²)`), so iterating gives a radius that blows up after a few periods. Needs either a bound by blocks that keeps the position out of the Lipschitz radius (the field does not depend on `p`), or rate and velocity invariants from the controller (mid level). |
| A sharp input sensitivity by blocks (velocity rows `≈ amax h ‖u - w‖`, rate rows `≈ 2 alphaMax h ‖u - w‖` plus higher order) | the sup-norm Grönwall over the whole state uses `Klip (box r)`, which contains the position and the velocity radius; at `‖x‖ ≤ 1` the input factor is about 11 per unit command against the leading-order 3 (`FINDINGS.md`, F5). A block-wise Grönwall as in `Sharp.lean` (attitude block alone, then exact integration of `p`, `v`) is the route; not started. |
| Pure yaw spin under unequal commands with nonzero roll or pitch rates; exact solution for constant body rates | no closed form in general (the gyroscopic coupling); only the torque-free axisymmetric case would have one |
| The converse of `run_stepN` (a sequence with `x n = stepN us n x0` and `held` = previous input is a run) | not attempted; easy |
| Bounds of the step against PyBullet's integrator (three semi-implicit substeps of 1/1200 s) | PyBullet's integrator is not modeled (archive `PLANT.md`, "Where the model differs") |
| The X500 plant (motor lag, `VEHICLES.md`) | the model would need lagged thrust states; deciding the parametrization is the purpose of `VEHICLES.md` |
