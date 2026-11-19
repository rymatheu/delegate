# The proofs of the paper

All proofs are in the Lake package `contracts/` (Lean v4.36.0-rc2, Mathlib v4.36.0-rc2). They are stated on the translated ArduPilot controller (`contracts/Translated/`, the same code as `lean/`), in closed loop with the Crazyflie 2.x plant as an ODE under zero-order hold (`Contracts/Plant/`), one tick = 1/400 s.

## The five theorems

Every statement has the form `Mloop sense32 senseP w₀ ⊨ ⟨A, G⟩`: every behavior of the closed loop that starts in `A` (hover at `p₀`, at rest and level, any heading `ψ₀`) satisfies `G`.

| theorem (namespace `Contracts.Track.Reach`) | file | guarantee, in one line |
|---|---|---|
| `Leg.waypoint_reach_h` | `Reach/LegHold.lean` | horizontal reachability: a waypoint at the same altitude, 1 cm to 3.6 m away, is reached within 0.1 m in at most 4800 ticks and held for 1200 ticks |
| `Leg3.waypoint_reach` | `Reach/Leg3Hold.lean` | 3D reachability (paper's `waypoint_reach`): a waypoint in any direction, 1 cm to 3.6 m away, within 0.1 m in at most 6000 ticks, held for 1200 ticks (`PSC_D_ACC_P 0.25`) |
| `Safe.tracking_safe_h` | `Reach/Safe.lean` | safety, horizontal legs: at every tick the vehicle is within 0.2156 m of the instantaneous position target |
| `Safe.tracking_safe` | `Reach/Safe3.lean` | safety, 3D legs (paper's `tracking_safe`): within 0.2668 m of the position target at every tick |
| `Hover.hover_stable` | `Reach/Hover.lean` | practical exponential stability of hover: from within 2.1 cm per axis, distance to the hold point ≤ 3.68 · 0.9997ᵗ · d₀ + 3.6 mm at every tick |

## Hypotheses

The proofs are complete (no `sorry`), but they take named hypotheses. They are not proved; they were checked against measured C++ flights (`contracts/REACH.md` §9.3, §10.3, §11.4, §8.7).
- `hS : Plant.CopterSense`: the sensor ports read the plant state.
- `hL : LibmSpec`: error bounds of the C library functions the code calls.
- `hP : LegParams`/`LegParams3`, `hW : ReachWorld`, `HoldWorld`: the parameter values and the one-waypoint mission.
- `hF : LegFacts`, `LegFacts3`, `TrackFacts`, `TrackFacts3`, `HoverFacts`: per-tick facts of every closed-loop run (bounds on the navigator's target sequence, its phases, the attitude-loop deviation).

## Files and size

- `contracts/Contracts/Track/Reach/`: 33 files, 11,046 lines. `LegGainsData.lean` and `Leg3GainsData.lean` (1,848 lines) are generated certificate data.
  - Horizontal leg: `Leg`, `LegTube`, `LegGains(Data)`, `LegNav`, `LegHold`.
  - 3D leg: `Leg3`, `Leg3Tube`, `Leg3Gains(Data)`, `Leg3GainV`, `Leg3Nav`, `Leg3Hold`.
  - Safety: `Safe`, `Safe3`, `SafeRule`.
  - Stability: `Hover`, `HoverCert`, `HoverModel`, `HoverTube`.
  - Shared: `Glue*`, `Loop`, `Model`, `Composite`, `Liveness`, `Equilibrium`.
- These files rest on the rest of the package:
  - `Contracts/Track/` (channel models, kernel-checked certificates with `decide +kernel`, the induction framework).
  - `Contracts/Plant/` (the ODE and its exact one-tick flow `step_spec`).
  - `FloatModel/` (real semantics of `Float32`/`Float`).
  - `Contracts/{Basic,STL,Lift,Invariant}.lean` (contract algebra, STL semantics, lifting of code to behaviors, the invariant rule).

Theorems each top-level theorem uses, transitively, from this package (named theorems only; printed by `PaperAxioms.lean`):

| | total | in `Track/Reach` |
|---|---|---|
| `waypoint_reach_h` | 547 | 257 |
| `waypoint_reach` | 778 | 479 |
| `tracking_safe_h` + `tracking_safe` | 793 | 490 |
| `hover_stable` | 1008 | 141 |
| all five | 1608 | 720 |

## Axioms

`cd contracts && lake env lean PaperAxioms.lean` (after `lake build` and `lake build Track Quick`):

```
'Contracts.Track.Reach.Leg.waypoint_reach_h' depends on axioms: [propext, Classical.choice, Quot.sound]
'Contracts.Track.Reach.Leg3.waypoint_reach' depends on axioms: [propext, Classical.choice, Quot.sound]
'Contracts.Track.Reach.Safe.tracking_safe_h' depends on axioms: [propext, Classical.choice, Quot.sound]
'Contracts.Track.Reach.Safe.tracking_safe' depends on axioms: [propext, Classical.choice, Quot.sound]
'Contracts.Track.Reach.Hover.hover_stable' depends on axioms: [propext, Classical.choice, Quot.sound]
```

What was run for this repository (2026-11-19):
- The from-scratch build of `contracts/` here was stopped at the 45-minute cap. It built 104 of the package's modules without error, but not yet `Contracts/Track/Reach`.
- The output above comes from a separate copy of the tag's `contracts/`, byte-identical to it, with the package's original build directory of 2026-11-11. The Lean files here differ from that copy only in the header comment of `Translated/*.lean` (the ArduPilot path) and in the added `PaperAxioms.lean`.

The same holds for the plant theorem `Contracts.Plant.step_spec` and for `Contracts.compose_refines`. No `native_decide` is used anywhere. `contracts/AxiomCheck.lean` prints the axioms of 914 theorems of the package.

## In the package, but not results of the paper

- `Contracts.Mission.mission_contract` (`Contracts/Mission/Theorem.lean`, `MISSION.md`) is the mission-level contract of the whole course flight. Two sub-contracts are open:
  - `nav_contract` has a `sorry` in `Contracts/Mission/Sub.lean`.
  - `track_contract` rests on the `pieces` instance, whose fields are `sorry` in `Contracts/Track/Induction/Instance.lean`.
  - So `mission_contract` depends on `sorryAx`, and the default `lake build` warns about these `sorry`s.
  - The five theorems above import these modules but do not use the open declarations, as their axioms show.
- `Contracts/Quick/` (`QUICK.md`) holds quick controller-only contracts:
  - one is proved (`mission_in_order`, standard axioms);
  - several are refuted by counterexamples (`quick_cex`).
