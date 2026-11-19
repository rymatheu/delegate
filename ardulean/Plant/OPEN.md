# Open items of the plant library

## For the mid level (left out of this library on purpose)

These archive declarations relate the plant to floats, sensing ports, the contract library or the port's Euler-angle
plant. They are not in `Plant/` because the plant imports nothing from the flight code or the archive and is real-valued
(`PLAN.md`, rule 1). Their real-valued content is here where it exists.

From `archive/contracts/Contracts/Plant/Quadrotor.lean`:

| left out | what it is | needs | real-valued counterpart here |
|---|---|---|---|
| `Vector3f`, `Vector3p`, `Quaternionf`, `Sample` | the float sample of a tick (`Float32`/`Float` fields) | the controller's float types | `SampleR` |
| `act` | reading of `Float32` actuators (`Float32.toReal`, clipped) | `FloatModel.Float32` | `nextR` takes real commands |
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
| Multi-period sensitivity: `‖stepN us n x - stepN ws n y‖ ≤ K_n (‖x - y‖ + sup_k ‖us k - ws k‖)` with a useful `K_n` | the per-period command sensitivity is now sharp and block-wise (`step_input_sens`), but iterating it needs the same for a difference in the **initial state** (next row), and an a priori rate bound over `n` periods (`wTA` grows each period; from the controller, mid level) |
| A sharp state sensitivity by blocks (`‖step x u - step y u‖` block by block, without the whole-state Lipschitz constant) | not started; the route is the one of `Plant.Step.InputSens` with the initial differences as `B 0` (the motor block is exact: `abs_lagSol_sub_init_le`, factor `e^{-h/tauDown}`; the position enters nothing, the velocity only through itself). The joint bound `norm_step_sub_step_le_exp` exists but is useful only near the origin (`FINDINGS.md`, F5) |
| Bounds of the step against PyBullet's integrator (three semi-implicit substeps of `hPhys` with the thrust held per substep at its end value) | PyBullet's integrator is not modeled; the gap is measured and first order in `hPhys` (`MODEL.md`, `FINDINGS.md` F7). A first formal step would be the "substep model" of `tests/plant/numcheck.py` (the ODE with the thrust held piecewise constant), which explains the command-step part of the gap to `1e-7` |
| Pure yaw spin under unequal commands with nonzero roll or pitch rates; exact solution for constant body rates | no closed form in general (the gyroscopic coupling); only the torque-free axisymmetric case would have one |
| The converse of `run_stepN` (a sequence with `x n = stepN us n x0` and `held` = previous input is a run) | not attempted; easy |
| The wind runs (`flight-wind-4-1`): rotor and body drag of `sim/world/wind.py` | outside the no-wind plant by decision; would add an input (the wind) and a drag term to the `v` rows |

## Carried-over theorems whose content changed with the model

Every theorem of the earlier 13-state plant was carried over under its name except `Kin_nonneg` (the input constant
`Kin` of the field is gone: the commands now enter the field only through the motor rows, with constant `1/tauUp`,
`norm_vf_sub_input_le`). The statements that changed beyond the index layout, and why, are listed in `LEDGER.md`
("Carried over, changed").
