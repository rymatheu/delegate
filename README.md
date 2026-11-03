# A verified quadcopter flight stack in Lean 4

A quadcopter flight controller written in Lean 4 over `Float`, verified against a rigid-body plant model as the very source code that runs, and flown in simulation from the same source compiled to C.

The controller is the object of every theorem. It is lifted, as source, to a set of behaviors; specifications are discrete-time signal temporal logic formulas read as sets of behaviors; a contract `(A, G)` holds of a component `M` when `M ∩ A ⊆ G`. Floating-point rounding enters the proofs through Lean's own bit-level model of binary64 (`Float.Model`, Lean 4.33 and later), from which the needed rounding bounds are proved. No `sorry` and no custom axiom: every theorem depends only on `propext`, `Classical.choice` and `Quot.sound`.

## Layout

| Directory | Contents |
|---|---|
| `Flight/` | The controller: navigator, position control, attitude target, attitude control, rate control, mixer, their composition `Flight.Controller.step`, and the executable `Flight.Main`. Written over a scalar interface `Flight.Arith` and run at its `Float` instance. Nothing here imports Mathlib. |
| `FloatModel/` | The exact real value of a `Float` (`Float.toReal`) and rounding bounds for `+`, `-`, `*`, proved from `Float.Model`. |
| `Contracts/` | Contract algebra, STL, lifts of code to behavior sets, the plant model, and the closed-loop theorems. |
| `sim/` | The closed-loop simulation in gym-pybullet-drones, the C build, and the parameter files. |

## What is proved

| Theorem | File | Statement |
|---|---|---|
| `Contracts.chain`, `compose_refines`, `refines_sound` | `Contracts/Basic.lean` | The contract algebra: saturation, refinement, composition, and the chain rule. |
| `Contracts.Lift.liftHidden_inter_nonempty` | `Contracts/Lift.lean` | A lifted stateful module intersected with any receptive environment has a behavior. |
| `Float.add_error`, `sub_error`, `mul_error`, `*_small` | `FloatModel/Add.lean`, `FloatModel/Small.lean` | Relative error `2⁻⁵³` in the normal range; exact sums and differences and absolute error `2⁻¹⁰⁷⁵` for products below it. |
| `Contracts.FloatLoopIEEE.ieeeArith` | `Contracts/FloatLoopIEEE.lean` | The rounding hypotheses `FloatArith` hold of binary64. |
| `Contracts.QuadDivSqrt.divSqrtSpec` | `Contracts/QuadDivSqrt.lean` | Rounding bounds for `Float` division and square root, from the model. |
| `Contracts.FloatLoopIEEE.loop_spec_nearest` | `Contracts/FloatLoopIEEE.lean` | A `Float` proportional-derivative altitude loop with a concrete sensor meets a ceiling and a reach-and-hold specification, with no hypotheses. `M_inter_A_nonempty` shows the contract is not vacuous. |
| `Contracts.QuadCode.motors_in_unit` | `Contracts/QuadCode.lean` | Every motor command of the full controller is a finite float in `[0, 1]`, for every input and every parameter record. |
| `Contracts.QuadCode.controller_finite` | `Contracts/QuadCode.lean` | On finite inputs the hidden controller state stays finite. |
| `Contracts.QuadHover.hover_invariant_nearest` | `Contracts/QuadHover.lean` | The full controller at the flown gains, closed with the rigid-body Crazyflie plant and a concrete sensor, keeps a hover within 1 cm of the setpoint and 1 cm/s of rest for all time, assuming only `LibmZero`. |

`LibmZero` (`Contracts/QuadNear.lean`) states three facts about the C library's `sin`, `cos` and `atan2` at zero, which C99 Annex F requires. Lean declares these functions as opaque externs, so they cannot be proved and remain a hypothesis.

To list the axioms yourself:

```
cat > axioms.lean <<'EOF'
import Contracts
#print axioms Contracts.QuadHover.hover_invariant_nearest
#print axioms Contracts.FloatLoopIEEE.loop_spec_nearest
#print axioms Contracts.QuadCode.motors_in_unit
EOF
lake env lean axioms.lean
```

## Trusted base

- The Lean 4 kernel and the toolchain pinned in `lean-toolchain`.
- Lean's `Float.Model` as a faithful model of IEEE 754 binary64, and the assumption that the compiled code's arithmetic agrees with it: the Lean compiler's C emitter, clang as invoked by `leanc` (which passes `-ffp-contract=off`, so no fused multiply-adds), and the platform's `libm` for `sin`, `cos`, `atan2`, `sqrt`.
- The plant model (`Contracts/QuadPlant.lean`): rigid-body dynamics with the CF2X constants of gym-pybullet-drones, forward Euler at 120 Hz, no drag, ground effect or downwash. The simulation is a check of this model, not a proof about it.

## Building

Requires `elan`. Mathlib is a dependency, so fetch its prebuilt cache before building:

```
lake exe cache get
lake build
```

`lake build` builds the three libraries and the executable `flight`. `lake exe flight --selftest` closes the loop against the crude plant of `Flight/TestPlant.lean` with the built-in mission.

## Running the experiment

The controller flies a figure-eight course in gym-pybullet-drones through three routes that produce the same motor commands bit for bit: `lake exe flight`, a standalone binary compiled from the C that Lean emits, and Lean's interpreter. Set up the simulator as described in `sim/README.md`, then:

```
sim/build_c.sh                                   # the C route: sim/build/flight-c
cd sim
.venv/bin/python run_demo.py --backend bin       # or lake, or interp; --gui opens a window
.venv/bin/python run_demo.py --determinism       # fly all three routes and compare
```

Results and logs go to `sim/out/<backend>/`. The parameters are in `sim/params/cf2x.txt` (vehicle and controller gains, mirrored in Lean as `Contracts.QuadPlant.cf2xParams`) and `sim/params/cf2x-course.txt` (the course). The recorded result: 2381 ticks, final position error 0.22 cm, maximum tilt 10.8 degrees, and 0 of 2381 motor lines differing between any two routes.

## Toolchain

Lean `v4.33.0-rc1` with Mathlib at the matching tag (see `lake-manifest.json`). The simulation used gym-pybullet-drones 2.2.0, PyBullet 3.2.7 and Python 3.12 on macOS; `sim/README.md` records the versions and the install steps.
