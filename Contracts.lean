import Contracts.Basic
import Contracts.STL
import Contracts.Lift
import Contracts.FloatReal
import Contracts.FloatLoop
import Contracts.FloatLoopIEEE
import Contracts.QuadFloat
import Contracts.QuadPlant
import Contracts.QuadCode
import Contracts.QuadNear
import Contracts.QuadDivSqrt
import Contracts.QuadHoverZero
import Contracts.QuadHoverVert
import Contracts.QuadHover
import Contracts.CopterLift
import Contracts.CopterCode
import Contracts.CopterAxioms
import Contracts.CopterVertNear
import Contracts.CopterVertNearStep
import Contracts.CopterVertNearTick
import Contracts.CopterHover
import Contracts.CopterHoverAxioms

/-!
# Assume-guarantee contracts over sets of behaviors

Re-exports the library: `Contracts.Basic` (contracts, implementation, refinement, composition and the
chain rule), `Contracts.STL` (discrete-time signal temporal logic, formulas as sets of behaviors),
`Contracts.Lift` (the selector-form lifts of code to sets of behaviors `ℕ → X`),
`Contracts.FloatReal` (the exact value of a `Float` and the rounding hypotheses),
`Contracts.FloatLoop` (a closed loop with a `Float` controller), `Contracts.FloatLoopIEEE` (the
rounding hypotheses discharged from the binary64 model, a concrete sensor, non-vacuity),
`Contracts.QuadPlant` (the rigid-body Crazyflie plant with `Float` ports closed with the full flight
controller), `Contracts.QuadFloat` (the `Float` clip), `Contracts.QuadCode` (code-only contracts of
the flight controller: motor range and finiteness), `Contracts.QuadNear` (forward error propagation
through `Float` code), `Contracts.QuadDivSqrt` (rounding bounds of `Float` division and square root
from the binary64 model), `Contracts.QuadHoverZero` and `Contracts.QuadHoverVert` (the controller at
a hover sample) and `Contracts.QuadHover` (hover invariance of the closed loop).
-/
