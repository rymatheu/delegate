# Plant

The ODE plant: a rigid-body quadrotor under zero-order hold, copied on 2026-11-10 from cpp2lean
`contracts/Contracts/Plant/` with the namespace `Contracts.Plant` renamed `Plant` and nothing else
changed. `Constants` (CF2X), `Field` (state, frames, the vector field `vf`), `Bounds`,
`Invariants`, `Flow` (the flow under zero-order hold, `traj`, the sampled `step`).

Builds in this project as the library `Plant` (`lake build Plant`) on Lean v4.35.0 with Mathlib
v4.35.0 and DynamicalSystems at commit c2a753b. The controller executable does not import it.

Not copied: the sensing ports of `Quadrotor.lean`; the sensor model for this stack is to be
designed. Not yet done: the constants are the CF2X's; the X500 needs its own.
