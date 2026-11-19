# First increment: candidate statements and their status

Each row gives a candidate lemma, its kind, its status (**proved** with its Lean name, **open** with the reason, or
**false**, see FINDINGS.md), what it depends on, and how it was tested. Rows come in dependency order: a lemma uses
only lemmas listed before it, plus `Machine/`.

Notation: `f'` is `Id.run (Vehicle_lib.f.pure' …)`; `ε` is the word `0x34000000` (`2⁻²³`); `ext` is `Corpus.F32.ext`.
Every proved lemma below is in namespace `Corpus.AP_Math`, `Corpus.Control`, `Corpus.AC_PID` or `Corpus.ArduCopter`.
Every `f.pure'` also has a proved **Wrapper** lemma `f_eq : Vehicle_lib.f … = pure (Vehicle_lib.f.pure' …)`, by `rfl`.

Tests: `Corpus/Test/AP_Math.lean` and `Corpus/Test/AC_PID.lean` check each statement as a `#guard` on the edge
inputs (all pairs or triples of the 53 edge words) and on 3000 xorshift words, so the build fails if a proved statement
fails on an input. Each false statement also has a `#guard` confirming that its witness falsifies it.

## `is_zero`, `is_positive`, `is_negative`, `is_equal` (ftype.h, AP_Math.h, AP_Math.cpp)

| Statement | Kind | Status | Depends on |
|---|---|---|---|
| `is_zero' x = decide (Binary32.abs x < ofBits 0x34000000)` | Case | proved `is_zero_pure_eq` (rfl) | — |
| `is_zero' x = true ↔ ofBits 0xb4000000 < x ∧ x < ofBits 0x34000000` | Case | proved `is_zero_iff` | `F32.abs_lt_iff`, `F32.neg_eps` |
| `isNaN x → is_zero' x = false` | Case (NaN) | proved `is_zero_of_isNaN` | |
| `is_zero' x = true ↔ isNaN x = false ∧ -2⁻²³ < ext x < 2⁻²³` | Meaning | proved `is_zero_iff_ext` | `F32.lt_iff_ext`, `ext_eps` |
| `is_positive' x = true ↔ ε ≤ x` | Case | proved `is_positive_iff` | |
| `… ↔ isNaN x = false ∧ 2⁻²³ ≤ ext x` (`+∞` included) | Meaning | proved `is_positive_iff_ext` | |
| `is_negative' x = true ↔ isNaN x = false ∧ ext x ≤ -2⁻²³` (the `double` comparison) | Meaning | proved `is_negative_iff_ext` | `F64.ext_toBinary64`, `F64.isNaN_toBinary64`, `F32.is_negative_const` |
| `is_negative' x = true ↔ x ≤ ofBits 0xb4000000` (in `float`) | Case | proved `is_negative_iff` | |
| NaN: `is_positive'`, `is_negative'` false | Case (NaN) | proved `is_positive_of_isNaN`, `is_negative_of_isNaN` | |
| zero excludes positive and negative; positive excludes negative | Order (relations) | proved `is_zero_not_positive`, `is_zero_not_negative`, `is_positive_not_negative` | |
| a non-NaN value is zero, positive or negative | Order | proved `is_zero_or_positive_or_negative` | |
| `is_equal' a b = is_zero' (a - b)` | Case | proved `is_equal_eq_is_zero` (rfl; the `double` branch is dead) | |
| `is_equal' a b = is_equal' b a` | Order | **open**; tested true on all edge pairs. Needs `a - b = -(b - a)` up to NaN payload, which FloatLib does not have. | |
| `is_equal' a a = isFinite a` | Case | **open**; tested true. Needs `x - x` for `±∞` and NaN. | |

## `constrain_value_line` (float), `constrain_int16` / `constrain_value` (short)

| Statement | Kind | Status | Depends on |
|---|---|---|---|
| body = `if isNaN amt then (low+high)/2 else if amt < low then low else if high < amt then high else amt` | Case | proved `constrain_float_pure_eq` | `F32.int32_two` |
| NaN case, `< low` case, `> high` case | Case | proved `constrain_float_of_isNaN`, `_of_lt`, `_of_gt` | |
| identity on `[low, high]` | Case | proved `constrain_float_of_mem` | `F32.not_lt_iff_le` |
| non-NaN `amt`: the result is `amt`, `low` or `high` | Case | proved `constrain_float_cases` | |
| `low ≤ high`, non-NaN `amt`: `ext r = max (ext low) (min (ext amt) (ext high))` | Meaning | proved `constrain_float_ext` | `F32.lt_iff_ext` |
| …: result not NaN | Safety | proved `constrain_float_not_isNaN` | |
| …: `low ≤ r ≤ high` | Range | proved `constrain_float_mem` | |
| …: idempotent | Order | proved `constrain_float_idem` | |
| `low ≤ high`, `a ≤ b`: `r a ≤ r b` | Order | proved `constrain_float_mono` | |
| range for **every** `amt` when `low ≤ high` | Range | **false** (FINDINGS F1): NaN `amt` with `low + high` overflowing or `-∞ + ∞` | |
| NaN `amt`, `low ≤ high`, `low + high` finite: `low ≤ (low+high)/2 ≤ high` | Range | **open**; tested true. The `(-M)+M` instance is proved (`F32.midpoint_neg_self_mem`). The general case needs `roundAt(l+h) ∈ [2l, 2h]` with `2l`, `2h` possibly outside the format. | |
| `constrain_short` body = `if a < l then l else if h < a then h else a` (the promoted comparisons) | Case | proved `constrain_short_pure_eq`, `constrain_int16_pure_eq` | |
| `l ≤ h → l ≤ r ≤ h`; identity; idempotent; monotone | Range, Case, Order | proved `constrain_int16_mem`, `_of_mem`, `_idem`, `_mono` | `omega` on `toInt` |
| idempotent for every `l, h` | Order | **false** (FINDINGS F2): `l > h` | |

## `safe_sqrt`, `sq`, `norm`, `radians`, `degrees`, `cd_to_rad`

| Statement | Kind | Status | Depends on |
|---|---|---|---|
| `safe_sqrt' v = if 0 ≤ v then sqrt v else 0` | Case | proved `safe_sqrt_pure_eq`, `_of_nonneg`, `_of_not_nonneg`, `_of_isNaN`, `_of_neg` | `F32.int32_zero` |
| never NaN (every input, `±∞` and NaN included) | Safety | proved `safe_sqrt_not_isNaN` | `F32.sqrt_of_nonneg` |
| `0 ≤ safe_sqrt' v` (it returns `-0` for `-0`, which compares equal to `0`) | Range | proved `safe_sqrt_nonneg` | |
| finite `v ≥ 0`: `real r = roundAt (√(real v))` | Meaning | proved `safe_sqrt_toReal` | `toReal_sqrt_eq_roundAt` |
| `sq' v = v * v` | Case | proved `sq_pure_eq` | |
| finite square: `0 ≤ sq' v`, `real = roundAt (v²)` | Range, Meaning | proved `sq_nonneg`, `sq_toReal` | `F32.mul_nonneg_of_isFinite` |
| `0 ≤ sq' v` for every non-NaN `v` (overflow to `+∞` included) | Range | **open**; tested true. Needs the sign of an overflowed product. | |
| `norm' a b = sqrt (sq' a + sq' b)` | Case | proved `norm_pure_eq` | |
| finite sum of squares: `norm` not NaN and `≥ 0` | Safety, Range | proved `norm_nonneg` | `F32.add_nonneg_of_isFinite`, `sqrt_of_nonneg` |
| non-NaN `a`, `b`: `norm` not NaN and `≥ 0` | Safety | **open**; tested true. Needs the sign of an overflowed sum or square. | |
| `|a| ≤ norm a b` | Range | **false** (FINDINGS F3): the square underflows | |
| `radians' d = d * ofBits 0x3c8efa35`, `degrees' r = r * ofBits 0x42652ee0`, `cd_to_rad' c = c * ofBits 0x393702d4` (constants folded by the kernel) | Case | proved `radians_pure_eq`, `degrees_pure_eq`, `cd_to_rad_pure_eq` | `F32.deg_to_rad_const` etc. |
| finite in, finite out (`radians`, `cd_to_rad`: the constant is below 1) | Safety | proved `radians_isFinite`, `cd_to_rad_isFinite` | `F32.isFinite_mul_of_le` |
| finite `≥ 0` in, `≥ 0` out (`degrees`: when the result is finite) | Range | proved `radians_nonneg`, `cd_to_rad_nonneg`, `degrees_nonneg` | |
| finite: `real (radians' d) = roundAt (real d · 9370165/2²⁹)` | Meaning | proved `radians_toReal` | |
| odd; monotone | Order | **open**; tested true on all edge pairs. Needs `mul (neg x) y = neg (mul x y)` and monotone rounded multiplication with overflow. | |
| sign kept strictly (`d < 0 → r < 0`) | Order | **false** (FINDINGS F4): underflow to `-0` | |

## `safe_asin`, `wrap_2PI`, `wrap_PI` (premises on musl, plan rule 5)

| Statement | Kind | Status | Depends on |
|---|---|---|---|
| four branches as one conditional; each branch | Case | proved `safe_asin_pure_eq`, `_of_isNaN`, `_of_ge_one`, `_of_le_neg_one`, `_of_mem` | `F32.half_pi_const`, `neg_half_pi_const`, `neg_one_const` |
| under `AsinfRange`: never NaN, in `[-π/2, π/2]` (the float words) | Safety, Range | proved `safe_asin_mem` | premise `AsinfRange` (tested on the edges and the sample) |
| `wrap_2PI' r = let m := fmodf r 2π; if m < 0 then m + 2π else m`; `wrap_PI'` likewise | Case | proved `wrap_2PI_pure_eq`, `wrap_PI_pure_eq` | `F32.two_pi_const`, `two_pi_const64`, `pi_const` |
| under `FmodfRange`, finite `r`: `wrap_2PI` finite, in `[0, 2π]` | Range | proved `wrap_2PI_mem` | premise `FmodfRange` (tested), `F32.add_mem` |
| `wrap_2PI` in `[0, 2π)` | Range | **false** (FINDINGS F5): `wrap_2PI(-ε) = 2π` | |
| under `FmodfRange`, finite `r`: `wrap_PI` finite, in `[-π, π]` | Range | proved `wrap_PI_mem` | `F32.sub_mem` (exact `2π = 2·π`) |
| `wrap_2PI` idempotent; `wrap_PI` identity on `[-π, π]` | Order, Case | **false** (FINDINGS F6, F7); true: `wrap_PI` is the identity on `[0, π]` (tested; open, needs `fmodf r 2π = r` on `[0, 2π)` as a premise) | |
| NaN or `±∞` in: NaN out | Case | **open**; tested. Needs a premise that `fmodf` of a non-finite value is NaN. | |

## `control.cpp`: `sqrt_controller_accel`, `inv_sqrt_controller`, `stopping_distance`, `input_expo`, `angle_rad_to_accel_mss`, `accel_mss_to_angle_rad`

| Statement | Kind | Status | Depends on |
|---|---|---|---|
| seven branch lemmas of `sqrt_controller_accel`, each from the values of the tests that select it | Case | proved `sqrt_controller_accel_of_not_pos`, `_of_not_pos_lim`, `_of_not_pos_p_of_zero`, `_of_not_pos_p`, `_of_linear`, `_of_sqrt_of_zero`, `_of_sqrt` | `F32.zero64_const` |
| the divisor `|rate_cmd|` is `≥ ε` or NaN wherever the code divides by it | Safety | proved `sqrt_controller_accel_divisor` | `is_zero_pure_eq` |
| finite inputs: result not NaN | Safety | **open**; tested true on all 11⁵ combinations of 11 finite edge values (exploration run, not kept as a `#guard`) | |
| `result · rate_state ≤ 0` (it opposes the rate) | Order | **false** for `p < 0` (FINDINGS F8); open for `p ≥ 0` | |
| `inv_sqrt_controller` branches: `D>0, p=0`; `D≤0, p≠0`; `D≤0, p=0`; inside/outside the linear region | Case | proved `inv_sqrt_controller_of_pos_zero`, `_of_linear`, `_of_zero`, `_of_inside`, `_of_outside` | AP_Math relations |
| `stopping_distance = inv_sqrt_controller` | Case | proved `stopping_distance_pure_eq` | |
| finite inputs: `inv_sqrt_controller` not NaN | Safety | **false** (FINDINGS F9); true statement open (`|output|² < 2·D_max·FLT_MAX`) | |
| odd in `output` | Order | **false** for `p < 0` (FINDINGS F10); open for `p > 0` | |
| `input_expo` body (constants as words: `0.95` is `0x3f733333`) | Case | proved `input_expo_pure_eq` | `F32.expo_max_const`, `one64_const`, `neg_one64_const` |
| `expo ≥ 0.95` or NaN: result in `[-1, 1]` for every input | Range | proved `input_expo_mem_of_not_lt` | `constrain_float_mem` |
| finite `expo`: result in `[-1, 1]` | Range | **open**; tested on 3000 × 700 samples near the edges. Needs three roundings. | |
| odd; `input_expo 0 e = 0` | Order, Case | **open** for finite `expo`; **false** for `expo = -∞` (FINDINGS F11) | |
| monotone in the input | Order | **false** for large negative `expo` (FINDINGS F12) | |
| `angle_rad_to_accel_mss' a = g * tanf a`, `accel_mss_to_angle_rad' a = atanf (a / g)` | Case | proved `angle_rad_to_accel_mss_pure_eq`, `accel_mss_to_angle_rad_pure_eq` | |
| under `AtanfNotNaN`: `accel_mss_to_angle_rad` maps a number to a number | Safety | proved `accel_mss_to_angle_rad_not_isNaN` | `Model.isNaN_div_eq_false_of_isFinite` |

## Mode tables (`mode.h`)

All 97 `Mode*.f.pure'` that return a constant, each with `_val` (**Protocol**: the constant) and `_eq` (**Wrapper**),
plus `Mode.gcs_eq`: proved in `Code/ArduCopter/Mode.lean`, all by `rfl`, generated from the code's definitions.
Also proved: `mode_numbers_nodup`, the eight constant mode numbers are distinct (`decide`). Not covered:
`ModeAuto.mode_number`, `ModeAuto.requires_position`, `ModeAuto.allows_arming` and `ModeGuided.allows_arming` read
memory (tier 1).

## Tier-1 trial: `AC_PID::update_i` (`AC_PID.cpp:340-351`)

Hypotheses `Pre s this`: the frame `[sp, sp+16)`, its first word and the fields `_ki` (+4), `_kimax` (+16),
`_integrator` (+132) and `_error` (+140) are outside the bridged range and inside the memory, with no wrap-around; the
frame is disjoint from `[this+4, this+144)`.

| Statement | Kind | Status | Depends on (Machine/Memory) |
|---|---|---|---|
| the state after the call is `s` with a new memory, of one of three shapes: frame only; `_integrator := 0`; the two stores of the update branch (`updMem`) | Effect | proved `update_i_shape` | `enter4_run`, `memcpy4_run`, `ldF32_run`, `stF32_run`, `leave_run`, `run_ite`, `discard_run`; callee lemmas `is_zero_param_run`, `operator_neg_run`, `operator_const_float_run`, `is_positive_eq`, `is_negative_eq`, `constrain_float_eq` |
| every byte outside `_integrator` and the frame is unchanged; the other parts of the state are unchanged | Effect (`_frame`) | proved `update_i_frame`, `update_i_w32` | `get!_enter4`, `get!_memcpy4`, `get!_set4_of_lt` |
| `_kimax` unchanged | Effect | proved `update_i_kimax` | |
| integrator after = before, `0`, or `constrain_float(x, -kimax, kimax)` | Effect/Case | proved `update_i_integrator` | `w32_set4_self`, `w32_set4_of_disjoint`, `F32.ofBits_toBits` |
| finite `kimax ≥ 0` and `-kimax ≤ I ≤ kimax` before ⇒ the same after (a NaN update gives `(-kimax+kimax)/2 = 0`) | Invariant | proved `update_i_preserves_bound` | `constrain_float_mem`, `F32.midpoint_neg_self_mem`, `F32.neg_le_self` |

Tested: `Corpus/Test/AC_PID.lean` runs `update_i` on 47,916 concrete states (edge values in every field, `dt`,
`i_scale`, `limit`), checking that the stack pointer is restored, `_kimax` is unchanged and the bound is preserved. These
are not states of the recorded flights.
