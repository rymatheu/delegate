# cpp2lean (legacy)

**Legacy: the paper artifact, frozen at its 2026-11-11 state (translator, differential test, the paper's proofs); not developed further.**

cpp2lean translates the control subset of C++ (as clang's JSON AST) into executable Lean 4, deterministically and syntax-directed.
It was applied to ArduPilot's control libraries (AC_PID, AP_Math, AP_Motors, AC_AttitudeControl, AC_PosControl, AC_WPNav, the AHRS view).
The Lean output is checked against the compiled C++ by differential execution, bit for bit (`difftest.py`, the replay of a recorded flight).
Contracts are proved on the translated code in closed loop with an ODE plant (`contracts/`, Lean + Mathlib).
The theorems of the paper, their files and axioms are listed in `docs/PROOFS.md`.

## Prerequisites

- macOS (arm64) or Linux, `clang++` (checked with Apple clang 17), `python3` (standard library only), `git`.
- [elan](https://github.com/leanprover/elan); each package selects its own Lean: `lean/` v4.33.0-rc1, `contracts/` v4.36.0-rc2 (with Mathlib).
- Disk: about 1 GB for ArduPilot, 8 GB for `contracts/.lake` (Mathlib cache and build).

## Build

From `cpp2lean/`:

```
tools/fetch_ardupilot.sh                         # ArduPilot 802db19de1 into deps/ (git-ignored), ~15 s
(cd lean && lake build)                          # translated modules and executables, Lean v4.33.0-rc1
cd contracts
lake exe cache get                               # Mathlib build cache
LEAN_NUM_THREADS=1 lake build                    # plant, contract algebra, translated vehicle, mission
LEAN_NUM_THREADS=1 lake build Track Quick        # the paper's theorems (Contracts/Track/Reach)
cd ..
```

The two `contracts/` builds take about 80 minutes from scratch with `LEAN_NUM_THREADS=1` on a shared machine; both were run to completion here, and `PaperAxioms.lean` then prints only `propext`, `Classical.choice` and `Quot.sound` for the five theorems.

`ARDUPILOT_LOCAL=<clean clone at 802db19de1> tools/fetch_ardupilot.sh` links an existing clone instead of downloading.

## Run

From `cpp2lean/`:

```
python3 cpp2lean.py examples/numeric.cpp -o out/numeric    # translate one example -> out/numeric/Numeric.lean
python3 difftest.py pid                                     # C++ against Lean on one example, exit 0 iff 0 lines differ (*)
tests/run_tests.sh                                          # whole suite (below), prints "all tests passed", about 5 min
(cd contracts && lake env lean PaperAxioms.lean)            # axioms of the paper's theorems
```

`tests/run_tests.sh` checks: every example translates to its golden file in `tests/golden/`, deterministically; the rejection tests; the seven ArduPilot translations reproduce `tests/golden/ardupilot/`; `lean/` builds from clean without warnings; the differential test of all examples and ArduPilot classes; the per-tick composition against the recorded C++ output (500 ticks); both vehicles (`copter_ref` in C++, `copter_lean` in Lean) bit-identical on the recorded flight.
(*) `difftest.py` regenerates the committed driver `lean/Main.lean` for the targets it is given; `tests/run_tests.sh` restores it (or `git checkout lean/Main.lean`).
Outputs: `out/` (translator), `build/` (C++ drivers, difftest inputs and outputs, `build/vehicle/copter_ref`), `lean/.lake/build/bin/` (`demo`, `compose`, `copter_lean`); all git-ignored.

## Where things are

| path | content |
|---|---|
| `cpp2lean.py`, `difftest.py` | the translator; the differential test |
| `examples/`, `tests/` | demonstration inputs with their configurations; goldens, rejection tests, `run_tests.sh` |
| `ardupilot/` | translation scripts and unity files, stub headers, recorded flight (`data/`), composition check, the two vehicles |
| `lean/` | Lake package (Lean v4.33.0-rc1, no Mathlib) with the translated modules and the Lean vehicle |
| `contracts/` | Lake package (Lean v4.36.0-rc2, Mathlib): plant ODE, STL contracts, float model, proofs; its `*.md` files document each proof campaign |
| `sim/`, `figs/` | closed-loop flights in gym-pybullet-drones (not rechecked here, see `docs/SIM.md`); the paper's figures (`figs/pdf/`) with sources |
| `docs/` | `PROOFS.md` (the paper's theorems), `TRANSLATOR.md` (the original README: options, subset, mapping, compilation assumptions; "README.md" in code comments and generated files means this file), `SIM.md`, `FIGURES.md` |
| `tools/fetch_ardupilot.sh` | puts ArduPilot at the pinned commit into `deps/ardupilot` |
