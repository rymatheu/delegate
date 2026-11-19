# Provenance

ArduLean's flight code was not written by hand. It was generated from ArduPilot's C++ by the cpp2lean translator,
which lives in `../cpp2lean/` of this repository together with everything needed to run it again. ArduLean was
developed on its own branch (`ardulean`) of the translator's history; this directory imports that branch's files
(without the history), with its simulator replaced by the repository's shared `../sim/`. The branch and commit names
below refer to that history.

## Where the branch comes from

Branch `ardulean` starts from commit `4d4a5d4` of branch `cpp2lean` and keeps only the ArduLean product. The flight
code was last regenerated in commit `c4cd626` ("Total definitions and size_t as UInt64 in the translated vehicle");
the later commits on `cpp2lean` up to `4d4a5d4` did not change it.

## What the code was generated from

- **ArduPilot** at commit `802db19de135d4275f227b0cd5081d013de6eafc` (ArduCopter V4.8.0-dev), unmodified:
  ArduCopter, its libraries, and the navigation filter EKF3.
- **musl 1.2.5**, the math functions the flight code calls (`ArduLean/Musl/`), unmodified sources, translated by the same
  translator.
- **FloatLib** at commit `acba2057e452f32f4ed4f06bb0adbeda5342ba92`: the IEEE 754 binary32 and binary64 arithmetic
  in software that the code computes with. Mathlib at `v4.35.0`. Both pinned in `lake-manifest.json`.

## Which file is which

| file | origin |
|---|---|
| `ArduLean/Vehicle.lean`, `ArduLean/Vehicle/` | ArduCopter, translated (`ardupilot/vehicle/translate_vehicle.sh` on branch `cpp2lean`) |
| `ArduLean/Estimator.lean`, `ArduLean/Estimator/` | the sensor front ends, AP_AHRS and EKF3, translated (`ardupilot/translate_estimator.sh`) |
| `ArduLean/Musl/*.lean` | musl's math functions, translated (`libm/translate_libm.sh`) |
| `ArduLean/Runtime/Memory.lean`, `GcsPort.lean`, `Boundary.lean`, `BridgeMap.lean` | the byte memory, the MAVLink port and the vehicle's boundary, generated (`support/gen_param_memory_v.py`) from hand-written templates |
| `ArduLean/Runtime/Bridge.lean` | the bridge between the vehicle and the estimator, generated (`ardupilot/vehicle/gen_bridge.py`) |
| `ArduLean/Runtime/Hal.lean`, `ArduLean/Runtime/CFloat.lean` | written by hand for the translator (`support/`): the hardware layer's devices, and C's floating-point conversions |
| `Main.lean` | written by hand: the driver of the executable (named `VehicleReplay.lean` on branch `cpp2lean`) |
| `ArduLean/Driver/EstimatorProbe.lean` | written by hand: the parser of the estimator's sensor records |
| `Corpus.lean`, `Corpus/` | the proof corpus, written against this code |
| `Plant.lean`, `Plant/` | the X500's equations of motion and theorems about them, written by hand |

The 138 files of the first six rows are frozen: `Corpus/CODE.sha256` records their hashes and
`tests/check_code_frozen.sh` checks them.

## Layout

The translator emits the vehicle and the estimator as one file each. On this branch they are split into modules laid
out after ArduPilot's tree (`ArduLean/Vehicle/ArduCopter/`, `ArduLean/Vehicle/libraries/<name>/`, and the same under
`ArduLean/Estimator/`) by `tools/split_modules.py`. No declaration changes: `tools/check_split.py` reassembles the
modules and compares the result byte for byte with the original files. ArduPilot's libraries call each other in
cycles and Lean modules cannot, so a library folder may hold several numbered files, and four files at the top of
`ArduLean/Vehicle/` (`Arming`, `ModeSwitching`, `GcsMessages`, `SchedulerLoop`) hold code from several libraries.
`ArduLean/Vehicle/INDEX.md` maps each ArduPilot source file to its modules.

## Corrections made by hand

One translator defect was corrected directly in the vehicle code on this branch (2026-11-16, in what was then the single file `lean/Vehicle_lib.lean`), not by
regenerating: C++ case ranges (`case lo ... hi:`) had been translated as `case lo:`. Seven conditions in five
functions were changed to test the whole range; `Corpus/FINDINGS.md` (F20) lists them. At those seven lines the
code differs from the translator's output on branch `cpp2lean`, where the translator still has the defect.

## How to regenerate

Regenerating the code needs the translator, clang, and an ArduPilot checkout at the commit above. The steps are in
`README.md` of the translator (`../cpp2lean/`; the "Phase 3" to "Phase 5" sections and the scripts they name). Do not
regenerate here: any change to the frozen files invalidates the corpus.

## The simulator

The flight programs of `sim/` and the lock-step bridge `sim/bridge/` come from the simulator of the translator's
history, restructured on the `ardulean` branch without changing a flight (the scripted flights' records are
byte-identical). In this repository the simulator itself (the gorge world, the X500, sensors, motors, missions,
scripted ground station, record, UDP bridge, cameras, plans, checks) is the shared `../sim/` (package `gorgesim`, which
was `sim/harness/` here, and `../sim/world/`, which was `sim/world/`); `sim/` keeps only what is ArduLean's. The flights
are unchanged by the move: the scripted flights' records (`inputs.txt`, `outputs.txt`, `track.csv`) are byte-identical
to the recorded ones. The gorge world came from the Lean-native flight controller (`../leanfc/`). The X500's render
meshes are PX4's (BSD 3-Clause, notice in `../sim/world/x500/x500_meshes/LICENSE`). Comments in the frozen files
(`Plant/Model/Constants.lean`) cite the simulator by its earlier paths: `sim/harness/X` is `../sim/gorgesim/X`,
`sim/world/` is `../sim/world/`.
