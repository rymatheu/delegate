# The ArduLean proof corpus: plan

## What this is

ArduLean is the code: the vehicle `ArduLean/Vehicle/` (namespace `Vehicle_lib`) and the estimator `ArduLean/Estimator/` (namespace `Estimator_lib`), each laid out after ArduPilot's source tree and imported whole through `ArduLean/Vehicle.lean` and `ArduLean/Estimator.lean`, with their support modules, translated from ArduCopter by cpp2lean, compiled into the binary that flies and replays. Those files are the definitions. They are frozen and are never edited, regenerated, split or annotated for the sake of a proof.

The corpus is a separate Lean library, `Corpus`, in the same Lake package. It imports the code and proves theorems about its constants. It plays the role for ArduLean that Mathlib plays for the definitions of mathematics: a body of lemmas that makes each definition usable without reopening it, so that later, higher statements are short.

## Rules

1. **The code is not touched.** `Corpus/CODE.sha256` records the hashes of the code files; `tests/check_code_frozen.sh` fails if any differs. If a proof seems to need a change to the code, the proof is wrong or the statement is; report it, do not change the code.
2. **A low-level theorem names the code.** Every theorem under `Corpus/Code/` has a constant of `Vehicle_lib` or `Estimator_lib` in its statement. Its proof opens that constant's body (`unfold`, `simp only [f]`, `rfl`) or uses corpus lemmas that did. `tests/CorpusAudit.lean` rejects a theorem in `Corpus/Code/` whose statement names no code constant.
3. **One body per proof.** A proof about `f` opens `f` and no other code function. What it needs about a function `f` calls comes from that function's own lemmas. The corpus is therefore built in call-graph order (`ardupilot/out/Vehicle/Vehicle_lib.callgraph.txt` lists callees first).
4. **Nothing unproved in the library.** No `sorry`, no `axiom`, no `native_decide`, no `implemented_by`, no `unsafe`. `#print axioms` of every theorem shows only `propext`, `Classical.choice`, `Quot.sound`. A statement that is not proved yet lives in `Corpus/OPEN.md`, not in a `.lean` file of the library.
5. **Facts about things we have not yet proved are hypotheses, never axioms.** A lemma that needs a property of a libm function (`Musl.asinf.asinf`, `Musl.fmodf.fmodf`, ...) takes it as a named premise until `Corpus/Code/Musl/` proves it.
6. **Test before proving.** Every candidate statement is first evaluated on the edge inputs (`Corpus/Test/`: NaN, ±∞, ±0, the smallest subnormal, the largest finite, 1, FLT_EPSILON and its neighbors, ±π and neighbors) and, for stateful code, on states of the recorded flights. A statement that fails is a finding, recorded in `Corpus/FINDINGS.md` with the witness, and the true statement is proved instead.
7. **Proof-side definitions stay proof-side.** Predicates, real-valued functions and structures that the corpus needs are defined in the corpus (`Machine/`, `Theory/`), never added to the code.

## Layout

```
ArduLean/                       the code (frozen, imported only)
  Vehicle.lean  Vehicle/          the vehicle translation: ArduCopter/, libraries/<Lib>/, mavlink/ as in ArduPilot,
                                  the cross-library top (Arming, ModeSwitching, GcsMessages, SchedulerLoop) and the
                                  generated Layout, Dispatch, World, Startup; Vehicle/INDEX.md maps source files to modules
  Estimator.lean  Estimator/      the estimator translation, likewise (Estimator/INDEX.md)
  Musl/  Runtime/                 the C math library and what the code runs on (memory, HAL, bridge)

Corpus/
  Machine/      what the code is written in. No ArduPilot function appears here.
    Float.lean      Binary32/Binary64 as the code uses them: order and comparison, NaN and infinity,
                    literals and conversions (Int32.toBinary32, Binary64.toBinary32, ofBits), abs, neg,
                    + - * / sqrt as rounded real operations. A thin interface over FloatLib, grown on demand.
    Memory.lean     PMem: load after store (same address, disjoint addresses), store-store, word encodings,
                    enter/leave, the bridge region, memcpy.
    Loop.lean       invariant rules for `for i in [a:b]` and for `PMem.loopFuel`; fuel and depth flags.
    Hoare.lean      triples over `PMem.M`, `Agree` (the frame of a run), the step tactic over translated bodies,
                    the heap (`alloc`) and the stack discipline of calls (third increment).
  Code/         LOW-LEVEL PROOFS. One file per ArduPilot source file, one section per function.
    AP_Math/AP_Math.lean        ↔ libraries/AP_Math/AP_Math.{h,cpp}, ftype.h, definitions.h
    AP_Math/Control.lean        ↔ libraries/AP_Math/control.cpp
    AP_Math/Vector3.lean, Quaternion.lean, ...
    AC_PID/AC_PID.lean          ↔ libraries/AC_PID/AC_PID.cpp
    Filter/LowPassFilter.lean
    AP_Motors/...               AC_AttitudeControl/...    AC_PosControl/...    AC_WPNav/...
    ArduCopter/Mode.lean, LandDetector.lean, ...
    AP_NavEKF3/...              (Estimator_lib)
    Musl/...                    (the translated libm)
  Theory/       mathematics with no code constant: saturation, convex updates, rate limiters,
                debounce counters, codecs, transition systems, discrete systems, the plant ODE.
  Bridge/       instance lemmas: this code function is that theory object.
  Test/         edge-input evaluation of candidate statements.
  PLAN.md  LEDGER.md  OPEN.md  FINDINGS.md  CODE.sha256
```

`Machine/` is demand-driven: a lemma is added there when a proof in `Code/` needs it. `Theory/` and `Bridge/` start only when a pattern has three proved instances in `Code/`.

## Kinds of low-level proof

Each function in `Code/` gets lemmas of these kinds, as far as they apply. The suffix is the kind.

| Kind | Suffix examples | Says | The proof takes from the code |
|---|---|---|---|
| Case | `_of_nonneg`, `_of_nan`, `_eq` | which branch runs under which condition, and what it returns | the branch structure of the body |
| Safety | `_not_nan`, `_finite`, `_fuel`, `_depth` | no NaN or infinity out for stated inputs; no division by zero taken; index in bounds; fuel and depth flags not set | the guards |
| Range | `_mem_Icc`, `_le`, `_nonneg` | bounds on the result, in floats or integers | the clamps |
| Order | `_mono`, `_odd`, `_idem`, `_inv` | monotone, odd, idempotent, inverse of another code function | the formula |
| Meaning | `_toReal` | the real number the result represents, exactly or within a stated error | the formula, with `Machine/Float` |
| Effect | `_frame`, `_reads` | (memory functions) which bytes are written, which are preserved, stack restored; result as a function of the fields read | the loads and stores |
| Invariant | `_preserves_…`, `_le_imax` | a property of the object that holds after the call if it held before | the stateful update |
| Protocol | `_eq`, `_iff` | flags, counters, enums, tables | the discrete logic |

Names: `Corpus.<SourceFile>.<function>_<kind suffix>`, the function named as in C++ (`safe_sqrt_of_nonneg`, `AC_PID.update_i_integrator_le_imax`). Each section starts with a docstring giving the C++ signature and source lines, copied from the code's own docstring.

## Tiers (order of work)

- **Tier 0: pure leaves.** The 381 functions the translation already gives as pure functions (`f.pure'`, in `Id`), and the pure functions of `Estimator_lib`. No memory reasoning. For each `f.pure'`, also the one-line lemma that the memory-side `f` is `pure (f.pure' …)`.
- **Tier 1: one object.** Functions that read and write the fields of a single object and call only tier 0: `AC_PID.update_i`, `AC_PID.update_all`, `LowPassFilter.apply`, `AC_P_1D.update_all`, `shape_accel`, `Thrust_Linearization.*`, the vector and quaternion methods. Needs `Machine/Memory`.
- **Tier 2 and up: by call-graph height.** `rate_controller_run`, the mixer and output chain (`output_armed_stabilizing`, `output_to_motors`, `output_to_pwm`), the attitude and position controllers, the navigator, then the mode and mission logic (Protocol lemmas), the land detector, arming.
- **Estimator.** `Estimator_lib` is already pure-functional. Its tier 0 runs alongside the vehicle's; first targets are the code's own clamps and normalizations (`ConstrainStates`, `ConstrainVariances`, quaternion normalize).
- **libm.** `Corpus/Code/Musl/` is its own sub-corpus (`fmodf`, `sqrtf` are exact; `sinf`, `cosf`, `atan2f`, `asinf` need error bounds). Until then their properties are premises (rule 5).

## First increment (Tier 0, AP_Math)

Scaffold (`Corpus` library, `CODE.sha256`, the audit, the edge-test harness), then the complete lemma set, by kind, for:

| Function | Lemmas wanted |
|---|---|
| `is_zero`, `is_positive'float`, `is_negative'float`, `is_equal'float_float` | Case (the exact threshold), behavior on NaN, Meaning for finite input |
| `sq`, `norm`, `radians`, `degrees`, `cd_to_rad` | Case, Safety, Range (nonneg) where it applies |
| `constrain_value_line'float` | NaN case (midpoint); result in [low, high] for every `amt` when `low ≤ high`; identity on [low, high]; idempotent; monotone; result is one of `amt`, `low`, `high` when `amt` is not NaN |
| `constrain_value'short`, `constrain_int16` | Range, identity, idempotent, monotone |
| `safe_sqrt'float` | of nonneg, of negative, of NaN; never NaN; nonneg; Meaning (the correctly rounded root) |
| `safe_asin'float` | Case for all four branches; never NaN and range, under a named premise on `Musl.asinf.asinf` |
| `wrap_2PI`, `wrap_PI'float` | Case; range under a named premise on `Musl.fmodf.fmodf`; test the 2π edge first |
| `input_expo` | Case; odd; fixes 0; range [-1, 1] (test first: rounding may break it) |
| `sqrt_controller_accel`, `inv_sqrt_controller`, `stopping_distance`, `angle_rad_to_accel_mss`, `accel_mss_to_angle_rad` | Case per branch; Safety (which branches divide, and by what) |
| the mode tables (`Mode*.requires_position`, `allows_arming`, `has_manual_throttle`, `is_autopilot`, `mode_number`, …) | Protocol, by evaluation |

Then the first tier-1 proof as a trial of `Machine/Memory`: `AC_PID.update_i` — Effect (writes only the integrator field) and Invariant (`|integrator| ≤ kimax` after the call when `kimax ≥ 0` and the update branch runs; unchanged or zero otherwise).

## Tooling

- `tests/check_code_frozen.sh`: hashes of the code files against `Corpus/CODE.sha256`.
- `tests/CorpusAudit.lean`: for every theorem of `Corpus.Code.*`: names a code constant (rule 2); axioms used (rule 4); and the coverage table written to `Corpus/LEDGER.md`: per code function, which kinds are proved.
- `Corpus/Test/Edge.lean`: the edge inputs and a helper that evaluates a decidable candidate statement on all of them.
- Build: `LEAN_NUM_THREADS=1 lake build Corpus` (one Lean build at a time in this workspace).

## Measure of progress

`LEDGER.md`: functions with a complete lemma set over functions in scope, per tier and per source file; controller path = 822 definitions. `FINDINGS.md`: statements that looked true and are not, each with its witness.
