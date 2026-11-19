# 8. The first example: one rate PID

**Status (2026-11-16): built and tested.** One module, `rate_pid`, runs under the harness. Its contract was tested, failed, was corrected, and now passes. Since then (2026-11-18) two more modules and two systems run; see doc 9. This document describes the first example as it was built.

## What exists

```
lakefile.toml, lean-toolchain     Lean 4.35.0, core Lean only
Harness/                          the generic library (nothing in it mentions a PID)
  Schema.lean                     field types f32, i32, u32, bool; records as one word per field
  F32.lean                        binary32 bit patterns as hex and as shortest decimals
  Expr.lean                       the contract language: evaluation, printing, margins
  Contract.lean                   assumption and guarantee as named clauses; clause hashes
  Module.lean                     the module declaration, its checks, the generated C++ header
  Protocol.lean                   the client: child process, describe, init, step, quit
  Generate.lean                   inputs that satisfy the assumption (edge values, seeded random)
  Campaign.lean                   test campaigns and replay
  Ledger.lean                     result files, the ledger, status
  Sha256.lean                     SHA-256
Main.lean                         the `harness` command and the list of modules
cpp/module_protocol.h             the generic C++ side: main(), the protocol
ardupilot/build.sh                builds any ArduPilot module: ardupilot/build.sh NAME
ardupilot/modules/rate_pid/
  Module.lean                     schemas and contract
  sources.txt                     the ArduPilot sources compiled into the module
  adapter.cpp                     init and step around the real AC_PID
  stubs.cpp                       what was cut
  hand-checked-case.json          two steps with outputs worked out by hand
  evidence/ledger.json            one record per clause per campaign
  evidence/tested/                result files and replayable cases
```

## Build and run

From the harness directory, with ArduPilot's checkout at `$ARDUPILOT_ROOT` (default `deps/ardupilot`, fetched by `tools/fetch_deps.sh`; read only):

```
LEAN_NUM_THREADS=1 lake build                 # the harness command
ardupilot/build.sh rate_pid                   # runs `harness gen rate_pid`, compiles, links
.lake/build/bin/harness describe rate_pid
.lake/build/bin/harness test rate_pid         # seed 1, 2000 cases x 200 steps
.lake/build/bin/harness status rate_pid
.lake/build/bin/harness replay ardupilot/modules/rate_pid/hand-checked-case.json
```

Build products go to `build/` and `.lake/`.

## The module

The step is one call of `AC_PID::update_all(target, measurement, dt, limit, pd_scale, i_scale)`, as ArduCopter's rate controller makes it.

| Port | Fields |
|---|---|
| params | `kp ki kd kimax kpdmax filt_T_hz filt_E_hz filt_D_hz slew_max` (f32) |
| input | `target measurement dt pd_scale i_scale` (f32), `limit` (bool), `now_ms` (u32) |
| output | `command integrator p_term d_term dmod` (f32), `pd_limit` (bool), `internal_errors` (u32) |

Three ports came from reading the code rather than from the sketch in doc 5:

- `now_ms`. The slew limiter on the step path reads the clock, `AP_HAL::millis()`. The clock is outside the module, so it is an input.
- `pd_scale`, `i_scale`. ArduCopter passes them on every call.
- `internal_errors`. On a NaN, `constrain_float` reports an internal error and returns the midpoint of its bounds. The count is an output so that a contract can forbid it.

Feed-forward (`FF`, `D_FF`) is not part of `update_all`'s result, so it is set to 0 and left out. The notch filters are off (indices 0).

**Compiled from the checkout**, unmodified: `AC_PID.cpp`, `AP_Math.cpp`, `SlewLimiter.cpp`, `LowPassFilter.cpp`, plus `adapter.cpp`, `stubs.cpp` and `cpp/module_protocol.h`. The flags are ArduPilot's SITL flags that affect code (`-std=gnu++11 -cl-single-precision-constant -fsigned-char -fno-exceptions -fno-builtin -ftrapping-math` and the SITL defines) with `-O2 -ffp-contract=off -fno-fast-math`. `-cl-single-precision-constant` makes unsuffixed literals `float` in C++ too (checked). The waf-generated configuration is replaced by two small headers that `build.sh` writes: the cmath checks, and the stock SITL `hwdef.dat` turned into defines.

**The cut** (`stubs.cpp`). Each stand-in is listed with the reason the symbol is outside the module:

| Symbol | Outside because | Stand-in |
|---|---|---|
| `AP_HAL::millis()` | the clock (HAL) | returns the input `now_ms` |
| `AP_HAL::panic` | HAL; only AP_Math code off the step path refers to it | prints, aborts |
| `AP_InternalError::error`, `AP::internalerror()` | the reporter's real body also writes the HAL's persistent data | records the bit, count and line as the real one does; skips the HAL write |
| `AP_Param::setup_object_defaults` | parameter storage (loads defaults from the parameter table) | no-op; `init` sets every parameter of the object |
| `AP_Param::load`, `AP_Param::save` | parameter storage (EEPROM) | abort; only `load_gains`/`save_gains` call them |
| `AP::filters()`, `AP_Filters::get_filter` | the filter-definition singleton | abort; only `set_notch_sample_rate` calls them, never called |
| `NotchFilter<float>::apply`, `::reset` | its source pulls in MAVLink logging | abort; reachable only through notch pointers that stay null |

`AP_Float` is the real type; `set` and reads are ArduPilot's inline code. A fresh object is built in zeroed storage at every `init`, as ArduCopter's statically allocated controllers start zeroed; the constructor leaves the integrator, the filter states and the slew limiter's state to that zeroing.

**The code hash** is SHA-256 of a list: the SHA-256 of every file the compiler read for the module (its dependency output: 474 files, sources, ArduPilot headers, SDK headers, the generated header), the compile flags, the link flags and the compiler version. Not covered: the dynamically linked system libraries (libc++, and the math library, whose `expf` the slew limiter calls) and the harness itself.

## The contract as first stated, and what broke it

Doc 5's contract, with the parameter assumptions it left open (gains finite; `kimax`, `kpdmax`, the filter frequencies and `slew_max` finite and at least 0; `pd_scale`, `i_scale` in [0, 1]), plus a third clause:

```
assume     finite(target) ∧ finite(measurement), 0 < dt ∧ dt ≤ 0.01, the parameter clauses above
guarantee  integrator_bounded: |integrator| ≤ kimax
           command_finite:     finite(command)
           no_internal_error:  internal_errors = 0
```

Campaign `harness test rate_pid` (seed 1, 2000 cases × 200 steps): 400,000 steps in 2.7 s.

| Clause | Violations | Smallest margin |
|---|---|---|
| integrator_bounded | 0 | -0 (`kimax` = -0, integrator 0) |
| command_finite | 358,104 | |
| no_internal_error | 159,307 | |

Result: `ardupilot/modules/rate_pid/evidence/tested/20261116T231125Z-seed1.json`, with its counterexamples in the folder of the same name.

**command_finite, case 0, step 0.** `kp` = 1.6727039e38, `target` = -6.9982974e37, `measurement` = -1.6791359e38, `dt` = 1e-45 (the full record is in the file). On the first call the filters reset: `_error = target - measurement` = 9.79e37, finite. Then `P_out = _error * _kp` overflows to +∞. `dt` is below `FLT_EPSILON`, so ArduPilot's `is_positive(dt)` is false: there is no derivative, the integrator is zeroed, and the slew modifier is 1. `kpdmax` = 1.1754944e-38 is also below `FLT_EPSILON`, so the P+D limit is off. The command is +∞. The same thing happens with smaller gains whenever `target - measurement`, `_error * _kp`, `_derivative * _kd` or their sum leaves the binary32 range, and "finite" allows inputs up to 3.4e38.

**no_internal_error, case 3, step 34.** In the 35-step case:
- At step 31, `target - _target` = 2.34e38 + 1.55e38 overflows to +∞. `dt` = 1.1754944e-38 is below `FLT_EPSILON`, so `calc_lowpass_alpha_dt` returns 0, and the target filter computes `_target += 0 * ∞`, which is NaN. NaN then stays in the target and error filters for good.
- Steps 31 to 33 have `dt` below `FLT_EPSILON`, so `update_i` zeroes the integrator without calling `constrain_float`.
- Step 34 has `dt` = 6.06e-4. `update_i` adds NaN to the integrator, `constrain_float` receives NaN, raises `INTERNAL_ERROR(constraining_nan)` and returns `(-kimax + kimax)/2 = 0`.

A probe that calls the same objects directly, outside the harness, confirmed `_target` = NaN from step 31 and the error at step 34.

**integrator_bounded held.** Every update of the integrator goes through `constrain_float(_integrator, -kimax, kimax)`. With `limit` set, it is left unchanged. When `dt` or `ki` is below `FLT_EPSILON` it is set to 0. A NaN becomes the midpoint 0. The smallest margin is 0: the clamp is exactly the bound.

## The corrected contract

The guarantee is unchanged. The assumption bounds the signals and the gains instead of only requiring them to be finite:

```
gains_bounded:    |kp| ≤ 10000 ∧ |ki| ≤ 10000 ∧ |kd| ≤ 10000
signals_bounded:  |target| ≤ 10000 ∧ |measurement| ≤ 10000
(the other assumption clauses as before)
```

Why these bounds suffice, read from the C++ (an argument, not a proof):
- Each filter update `x += α(y - x)` has α in [0, 1], so the filters stay within the bounds of their inputs: |target| ≤ 1e4 and |error| ≤ 2e4.
- The derivative is computed only when `dt ≥ FLT_EPSILON`, so it is at most 4e4/1.19e-7 ≈ 3.4e11, and |D| ≤ 3.4e15. Also |P| ≤ 2e8, and one integrator increment is at most 2e6.
- The slew modifier is in (0, 1]. The P+D limit only scales down.
- The integrator is at most `kimax`, which is finite. Even at `kimax` = 3.4e38, adding 3.4e15 rounds back to 3.4e38.

So no operation overflows, and no NaN can arise.

| Campaign | Steps | Time | Violations | integrator_bounded smallest margin |
|---|---|---|---|---|
| seed 1, 2000 × 200 | 400,000 | 2.8 s | 0, 0, 0 | 0 |
| seed 2, 500 × 1000 | 500,000 | 3.4 s | 0, 0, 0 | -0 |

The outputs seen show that the campaign reached the parts of the step that matter: the slew modifier went down to 0.069, the P+D limit acted at about 15,000 steps, and the integrator reached its clamp.

## Behavior worth knowing

These are not violations.
- A `dt` below `FLT_EPSILON` (1.19e-7) resets the integrator to 0 and freezes the target and error filters. This follows from ArduPilot's `is_positive` and `is_zero`.
- `0 ≤ kimax` admits `kimax` = -0, which reads as 0.

## Evidence, status, replay

- Each campaign writes a result file and appends one ledger record per clause. Each record holds the code hash from `describe`, the clause's contract hash (of the printed assumption and that clause) and the result file's hash. The first contract's failing records stay in the ledger; their contract hash no longer matches.
- `harness status rate_pid` reports all three clauses **backed** (2 campaigns, 900,000 checks).
- Changing one character in `adapter.cpp` makes `status` report "sources changed since the executable was built" before a rebuild. After `ardupilot/build.sh rate_pid`, all three clauses are **stale** (new code hash). Restoring the character restores the old hash and the clauses are backed again.
- Changing `command_finite` in `Module.lean` (and `lake build`) makes only that clause stale (contract hash). The other two stay backed.
- Changing a field type in the declaration without rebuilding the executable makes every command refuse to run it (schema mismatch).
- `harness replay` on the saved counterexamples reproduces every output bit for bit (35 of 35 steps for no_internal_error). On `hand-checked-case.json`, whose outputs were worked out by hand from `update_all` with exact binary32 values, it also reproduces them bit for bit.

Speed: about 145,000 steps per second through the pipe on this machine (Apple M4, macOS 15.6), including the contract checks in Lean.

## What is not built

- Model-checker query generation, and any proved evidence.
- Monitoring in a closed loop, the lock-step runtime with a plant, and wiring between modules.
- The proposition reading of contracts for Lean proofs, and composition of harnesses (doc 4).
- The replay test against the monolithic vehicle (doc 5, step 5), so the cut is checked by reading the code, not by recorded traffic.
- `save`/`load`, fixed arrays in schemas, access to the previous tick in the contract language.
- Coverage measures beyond the output ranges in each result file.
