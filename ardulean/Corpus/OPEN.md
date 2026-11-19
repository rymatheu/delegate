# Open statements (plan rule 4: stated here, not in the library)

Every statement here was evaluated on the edge inputs and held (`Corpus/Test/`). Each entry says what blocks the proof.
`f'` is `Id.run (Vehicle_lib.f.pure' …)`. Updated 2026-11-16 (second increment): the four FloatLib gaps of the first
increment are closed in `Machine/Float.lean` (section "Rounding with overflow, negation, signs"), and so are the
entries that waited on them (see LEDGER.md). Updated 2026-11-16 (fourth increment): `SlewLimiter::modifier`'s value is closed; `update_all`'s value is tested and
open (below), and the pure leaves' open items are listed. Updated 2026-11-16 (third increment): `LowPassFilter::apply`,
`SlewLimiter::modifier`'s Effect, `update_all`'s Effect and integrator bound are closed; what remains of them is below.

## Float facts still missing (`Machine/Float`)

1. **Overflow threshold for division.** `isFinite_roundDyadic_of_abs_roundAt_le` covers `+ - *` (dyadic rounding).
   Division rounds a rational (`Model.roundRatScaled`), and the same threshold is not proved for it, so the sign of an
   overflowed quotient is known (`signBit_roundRatScaled`, `div_nonneg_of_pos`) but monotonicity of division is not.
2. **Division with an infinite operand.** `finite / ±∞ = ±0` and `±∞ / finite = ±∞` (FloatLib's `Spec.divSpecial`)
   are not restated for `Binary32`. Needed by `inv_sqrt_controller`'s NaN freedom (below).

## Open lemmas about the code

- `input_expo`: for finite `expo`, the result is in `[-1, 1]`. Not attempted in this increment (odd and fixes-0 are
  proved). Needs `round((1-e)·i) ≤ round(1 - round(e·|i|))` for `e < 0.95`, `|i| ≤ 1`: three roundings, and the
  quotient's monotonicity (item 1 above).
- `inv_sqrt_controller`: not NaN for finite inputs when `output²` and `2·D_max` do not both overflow (FINDINGS F9;
  tested on all edge triples). Every branch is a quotient: `(o·o) / (2·D_max)`, `o / p` (`p` not a zero), and
  `D_max / p² · 0.5 + o² / (2·D_max)`; the proof needs item 2 above (a quotient with an infinite operand is not NaN)
  and the sign of each term (`div_nonneg_of_pos` covers finite operands only).
- `wrap_PI'float`: identity on `[0, M_PI]`, and `wrap_2PI` identity on `[0, M_2PI)`. Each needs a further premise:
  `fmodf r M_2PI = r` for `0 ≤ r < M_2PI`. `wrap_2PI` of NaN or `±∞` is NaN: needs `fmodf` of a non-finite value to be
  NaN.
- `norm`: `|a| ≤ norm a b` when the squares do not underflow (FINDINGS F3; the exact hypothesis is still to be written).

## Premises on musl (plan rule 5; to be proved in `Corpus/Code/Musl/`)

- `Corpus.AP_Math.AsinfRange`: on `(-1, 1)`, `asinf` is a number in `[-π/2, π/2]` (the float words `0xbfc90fdb`,
  `0x3fc90fdb`).
- `Corpus.AP_Math.FmodfRange`: for finite `r`, `fmodf r M_2PI` is finite and strictly between `-M_2PI` and `M_2PI`.
- `Corpus.Control.AtanfNotNaN`: `atanf` maps a number to a number.

The first two are checked on the edge inputs and the 3000-word sample (`Corpus/Test/AP_Math.lean`).

## `AC_PID`: what is still assumed

- **`Pre`/`UPre` at the call sites.** `AC_PID.pre_of_regions` (for `update_i`, 16 bytes of stack) and
  `AC_PID.upre_of_regions` (for `update_all`, 48 bytes: FINDINGS F17) derive the hypotheses from two region facts:
  `StackOK s stackBase memSize n` and the owning object in the heap region `[heapBase, stackBase)`. The instance lemmas
  (`rate_{roll,pitch,yaw}_pid_pre`/`_upre`, `accel_pid_pre`/`_upre`) take the owning object (`AC_AttitudeControl_Multi`,
  1112 bytes; `AC_PosControl`, 984 bytes) in the heap region. Still open:
  (a) **the stack predicate at the call along a run.** Proved: `Mem.StackOK.call` (a call `enter k … leave` gives the
  callee `StackOK … (n - frameSize k)` and restores the caller's predicate when the body keeps the memory's size),
  `StackOK.enter`, `StackOK.leave`. Measured (`Test/Regions.lean`): from `AP_Vehicle::loop`'s entry the path
  `AP_Vehicle::loop` (frame 80) → `AP_Scheduler::loop` (16) → `AP_Scheduler::run`, the task functor, the method
  wrapper, `Copter::run_rate_controller_main` (no frame) → `AC_AttitudeControl_Multi::rate_controller_run` (32) →
  `rate_controller_run_dt` (16) → `AC_PID::update_all` (16) → `update_i` (16) is **176 bytes**; the deepest point under
  `update_all` (`SlewLimiter::modifier` 16 + `LowPassFilter::apply` 16) is **192 bytes**. The frames are checked
  against the code by `rfl` (`enter 72`, `16`, `28`, `12`, `4`, `12`, `4`, `4`); "no frame" for the four dispatch
  functions was read off their definitions (no `PMem.enter`), not proved. A whole-tick theorem must carry
  `StackOK s stackBase memSize 192` at `AP_Vehicle::loop`'s entry for this path (static construction leaves
  `sp = stackBase`, `0x30000`, with 64 KiB of stack above it; that the driver (Main.lean) enters `AP_Vehicle::loop` there was
  not checked), and still needs the invariant that every function between
  the scheduler and the rate controller keeps the memory's size (true of every primitive, not yet stated as a lemma
  over those functions' bodies).
  (b) **the two controllers in the heap region.** Proved (`Machine/Hoare.lean`): `Mem.alloc_run`; the heap predicate
  `HeapOK s heapBase stackBase`; `HeapOK.alloc`: when `hp + frameSize n ≤ stackBase`, the block returned is
  `InRegion … heapBase stackBase n`, the predicate holds again, `hp` moves by `frameSize n`, no byte outside the block
  changes; `HeapOK.alloc_disjoint`: successive blocks are disjoint. Only `PMem.alloc` writes `hp` in the code files
  (`ArduLean/Runtime/Memory.lean:438`; checked by search, and `PMem.halImpl` is opaque). Evaluated (`Test/Regions.lean`):
  `initMem` plus the C++ static construction (`staticDynamicInit`, `staticConstruct`) leave `hp = 0x20ee0` (3808 bytes
  of heap), `sp = stackBase`. **Remaining obligation:** along `AP_Vehicle::setup()` up to and including
  `Copter::allocate_motors` (its `PMem.alloc` calls, in program order: two of 776 bytes on the frame-class branches,
  the attitude controller (1112), the position controller (984), WPNav (2504), LoiterNav (104), CircleNav (104)), every `alloc n`
  satisfies `hp + frameSize n ≤ stackBase` (`0x30000`, 61 728 bytes above `0x20ee0`); with it, `HeapOK.alloc` places
  the two controllers in the heap region and the instance lemmas apply. The other allocation sites (`AP_Param::add_default`
  24, `GCS::update_send` 56, `GCS_Copter::new_gcs_mavlink_backend` 880, the `ObjectBuffer`s 24, `AP_BattMonitor::init`
  96, `AP_Scheduler::init`'s task arrays, `AP::PerfInfo::allocate_task_info`, `ObjectArray<GCS_statustext_t>`) must
  satisfy the same bound for the objects allocated after them. `setup()` calls the HAL (`PMem.halImpl`, `@[extern]`,
  implemented by the driver Main.lean), so the Lean interpreter cannot evaluate it: the check of the actual addresses needs
  a run of the executable `ardulean` (`VEHICLE_REPLAY_MEMDUMP` dumps memory; the pointers are `copter.attitude_control` and
  `copter.pos_control`), which this increment did not do.
- **Recorded-flight states.** The stateful tests (`Corpus/Test/AC_PID.lean`, `Corpus/Test/UpdateAll.lean`) use
  synthetic states; plan rule 6 also asks for states from the recorded flights. Not done.
- **Effect stated byte-wise.** The dead frame bytes are not restored (C leaves them as written); every Effect lemma
  names its stack bytes.

## `AC_PID::update_all`: where the fourth increment stopped

Done in the fourth increment: `SlewLimiter::modifier`'s value (`Corpus.Filter.modifier_eq`, `modVal`, and the Case
lemmas `modifier_of_nonpos_max`, `modifier_of_le`, `modifier_of_gt`; tested in `Test/Modifier.lean`), and the
value-tracking rules in `Machine/Hoare.lean` (section "Value-tracking rules": `bind_val`, `ldF32_val`, `ldU64_val`,
`ldBits_val`, `pure_val`, `stF32_pin`, `memcpy4_pin`, `stBits_keep`, `Stable.pin32`/`pinBit`/`and_w32`/`and_const`,
`triple_jp` and `triple_jp_w32` (join points with a precondition chosen by the caller), `triple_zeta_pure`,
`stable_tac`, `triple_step'`, and `MemIs` with `ldF32_mem`, `stF32_mem`, `stB_mem`, `stBits_mem`, `ldBits_mem`,
`val_mem` for straight-line code run on the memory alone).

1. **`update_all`'s value and fields (open, tested).** Statement (evaluated on 3456 synthetic states,
   `Test/UpdateAllValue.lean`): with `UPre s this` and `target`, `measurement` finite, writing `T0, E0, D0, TD0, I0` for
   the fields `+136, +140, +144, +152, +132` before the call, `αT, αE, αD` for `lpAlpha dt` of `+24, +28, +32`, and
   `rst` for bit 0 of the byte `+128`:
   `_target' = rst ? target : T0 + αT·(target - T0)`;
   `_error' = rst ? target - measurement : E0 + αE·((_target' - measurement) - E0)`;
   `_derivative' = rst ? 0 : is_positive(dt) ? D0 + αD·((_error' - E0)/dt - D0) : D0`;
   `_target_derivative' = rst ? 0 : is_positive(dt) ? (_target' - T0)/dt : TD0`;
   `_integrator'` = `update_i`'s value (`update_i_integrator_cases`) on `I0`, `_error'`, `_ki`, `_kimax`;
   bit 0 of `+128` clear; and the value returned is `(P + D) + _integrator'` with `(P, D)` = the `PD_max` limit
   (`is_positive(PD_max) ∧ |P0 + D0'| > PD_max` scales both by `PD_max / |P0 + D0'|`) of
   `P0 = ((_error'·kp)·m)·pd_scale`, `D0' = ((_derivative'·kd)·m)·pd_scale`, `m` the slew modifier, which the call
   leaves in `_pid_info.Dmod` (`+188`; `modifier_eq` gives it). A proof was carried out in a scratch development
   with the rules above: the part after the first join point (from the `update_i` call to the return) closes, with a
   pinned invariant (`_error'`, `_derivative'` etc. pinned in `R`, the integrator re-pinned across `update_i`
   by a call lemma, `+188` pinned by `stF32_pin`, the `PD_max` join point by `triple_jp_w32` with the property of its two
   arguments, the bit-1 store into `+128` by `stBits_keep`); the first part is run with `MemIs` (memory alone) and the
   join point's precondition is discharged per branch by rewriting the memory chain. **Blocker:** as one declaration
   this exceeds 3,000,000 heartbeats (about 90 s), almost all in the three branch closings (`simp` with arithmetic
   side conditions on six-deep `set4`/`set!` chains, over a large context). What remains is engineering: state the
   three join-point closings as separate lemmas over the memory chains (values abstracted), and the part after the
   join point as its own theorem, so that each declaration stays within a raised but modest limit.
2. **`update_all` not NaN.** Not attempted (needs item 1 and finiteness of the filters' state and gains).

## Pure leaves (fourth increment): what is still open

- `AP_SerialManager::map_baudrate` for codes above 2000 (`map_baudrate rate = rate.toUInt32` when
  `2000 < rate`; tested in `Test/Leaves.lean`): `simp` over the body's 17-way `switch` and join point exceeds its step
  limit; needs a lemma per comparison or a tactic that discharges the `switch` arm by arm.
- `is_zero (double)` of a widened float is `is_zero (float)` (`is_zero'2 (toBinary64 x) = is_zero x`, tested): needs
  `Binary64` versions of `ext_abs`, `abs_lt_iff` in `Machine/Float`.
- `sq`, `norm` over `double` (`sq'double`, `norm'double_double`, …): Case only; nonnegativity and NaN freedom need the
  `Binary64` sign lemmas (`mul_self_nonneg'`, `add_nonneg'`, `sqrt_of_nonneg` exist for `Binary32` only).
- `radians (int)`: never NaN (an `int` converts to a number): needs `Int32.toBinary32 d` not NaN (`CFloat.ofInt32`,
  `ExecFloat.Binary.ofRat`).
- The 124 `Unit`-valued pure leaves (default constructors of MAVLink message structures, parameter headers,
  semaphores, `assert_storage_size`): each is `pure ()`; not targeted.
- `Estimator_lib`'s scalar functions (101, listed in `SURVEY-pure.md`): not started.

## Not started

- Section 4 of the third increment's list (section 3 of the fourth's, not started in either for lack of time):
  `inv_sqrt_controller` NaN freedom (needs Float facts 1 and 2 above) and
  `input_expo`'s range for `expo < 0.95`.
