# Findings: statements that looked true and are not

Each witness was found by evaluating the code on the edge inputs (`Corpus/Test/`), and each is checked there by a
`#guard`. Values are given as `float` words, with the decimal value in parentheses. The true statement is the one proved
or listed in `STATEMENTS-tier0.md` and `OPEN.md`.

| # | Function | Naive statement | Witness | What happens | True statement |
|---|---|---|---|---|---|
| F1 | `constrain_value_line'float` | for `low ≤ high`, the result is in `[low, high]` for every `amt` | `amt = NaN`, `low = high = 0x7f7fffff` (`FLT_MAX`): result `+∞`. `amt = NaN`, `low = -∞`, `high = +∞`: result NaN. | The NaN branch returns `(low + high) / 2`, and the sum overflows or is `-∞ + ∞`. | In range for non-NaN `amt` (`constrain_float_mem`, proved). For NaN `amt` when `low + high` is finite: tested, open. Idempotence and "never NaN" need the same proviso. |
| F2 | `constrain_int16` | idempotent | `amt = -32768`, `low = -32767`, `high = -32768`: first call `-32767`, second `-32768` | With `low > high` the clamps disagree. | Idempotent when `low ≤ high` (`constrain_int16_idem`, proved). |
| F3 | `norm` | `|a| ≤ norm a b` | `a = 0x00000001` (smallest subnormal), `b = 0`: `norm = 0` | `a*a` underflows to `0`. | Open: holds when `a*a` and `b*b` do not underflow (not yet stated exactly). |
| F4 | `radians` | `d < 0 → radians d < 0` | `d = 0x80000001`: result `-0` | The product underflows to `-0`, which is not `< 0`. | `0 ≤ d → 0 ≤ radians d` for finite `d` (`radians_nonneg`, proved); monotone (tested, open). |
| F5 | `wrap_2PI` | result in `[0, 2π)` for finite input | `radian = 0x80000001` or `0xb4000000` (`-ε`): result `0x40c90fdb` (= `M_2PI`) | `fmodf` returns the tiny negative input, and `res + M_2PI` rounds to `M_2PI`. | Result in `[0, M_2PI]`, closed (`wrap_2PI_mem`, proved under `FmodfRange`). |
| F6 | `wrap_2PI` | idempotent | `wrap_2PI(wrap_2PI(-ε)) = wrap_2PI(M_2PI) = 0`, but `wrap_2PI(-ε) = M_2PI` | Consequence of F5. | Idempotent on `[0, M_2PI)` (tested, open). |
| F7 | `wrap_PI'float` | identity on `[-π, π]` | `radian = 0xbf7fffff` (`-0.99999994`): result `0xbf800000` (`-1`); `radian = 0x80000001`: result `0` | Negative inputs go through `+ M_2PI` and then `- M_2PI`, which rounds twice. | Identity on `[0, π]` (tested, open); result in `[-π, π]` (`wrap_PI_mem`, proved under `FmodfRange`). |
| F8 | `sqrt_controller_accel` | the acceleration opposes `rate_state` (`r · rate_state ≤ 0`) | `error = rate_cmd = rate_state = p = second_ord_lim = -2`: result `-4`, `r · rs = 8` | With `p < 0`, `-p * rate_state` has the sign of `rate_state`. | Open, for `p ≥ 0`. |
| F9 | `inv_sqrt_controller` | finite inputs, result not NaN | `output = FLT_MAX`, `p = 0`, `D_max = FLT_MAX`: NaN | `output² / (2·D_max)` is `∞ / ∞`. | Open: not NaN when `output²` and `2·D_max` do not both overflow. |
| F10 | `inv_sqrt_controller` | odd in `output` | `output = ±0`, `p = -1`, `D_max = 1`: both give `0xbf000000` (`-0.5`) | With `p < 0`, `|output| < D_max/p` is false even at `0`; the sign then comes from `is_positive(output)`, which is false for both zeros. | Open, for `p > 0`. |
| F11 | `input_expo` | `input_expo 0 expo = 0`; result never NaN | `input = 0`, `expo = -∞`: NaN | `(1 - expo) * 0 = ∞ · 0`. | Open, for finite `expo` (tested true on all edge pairs). |
| F12 | `input_expo` | monotone in the input | `expo = 0xcbe42a8e` (≈ `-2.99e7`): `input_expo(0x3f070ba2) = 0x3f7fffff`, but `input_expo(0x3f206aa9) = 0x3f7ffffe` | Numerator and denominator are both near `|expo|·input`, and their roundings do not preserve order. | Not monotone for large `|expo|`. Range `[-1, 1]` still holds on all samples (open). |

Exploration (not a finding): `is_equal(a, a)` is false for `±∞` (`∞ - ∞` is NaN) and for NaN. The proved
characterization `is_equal_eq_is_zero` covers this case.

## Second increment (2026-11-16)

Witnesses checked by `#guard` in `Corpus/Test/Float.lean` and `Corpus/Test/AP_Math.lean`.

| # | Function | Naive statement | Witness | What happens | True statement |
|---|---|---|---|---|---|
| F13 | `Binary32` subtraction (`Machine/Float`) | `x - y = -(y - x)` as words, for numbers `x`, `y` | `x = y = 1` (`0x3f800000`): `x - y = 0x00000000` (`+0`), `-(y - x) = 0x80000000` (`-0`) | An exact zero difference is `+0` in both orders under round-to-nearest. On the edge pairs this is the only failure (`x == y`). | `F32.sub_antisymm`: `x - y` and `y - x` are both NaN or both numbers, and `ext (x - y) = -ext (y - x)` (proved; all of `is_equal`'s symmetry needs). |
| F14 | `inv_sqrt_controller` | odd in `output` for `p > 0` | `output = ±1`, `p = 0x00000001` (smallest subnormal), `D_max = 1`: both give `0.5` | `0 < p < ε` makes `is_zero(p)` true, which selects `output² / (2·D_max)`, even in `output`. | Odd for `is_positive(p)` (`p ≥ ε`) and `|output| ≥ ε` (`Control.inv_sqrt_controller_odd`, proved, as words or both NaN). |
| F15 | `inv_sqrt_controller` | odd in `output` for `p ≥ ε` | `output = ±0x33e66666` (`±0.9ε`), `p = 2`, `D_max = ε`: both give `-stop` (`stop ≈ 0.53ε`) | Outside the linear region the sign comes from `is_positive(output)`, false for both `±0.9ε`. | As F14: needs `|output| ≥ ε` (the C++ code's `is_positive` test, not a sign test). |
| F16 | `AC_PID::update_i` (`Pre`) | `Pre s this` follows from a stack predicate alone for the controller's PIDs, by their address constants | no `Vehicle_lib.addr'…` constant exists for any `AC_PID`; e.g. `this = PMem.Bridge.lo` (`0x844d`, the bridged range) would violate `Pre.ki` | The four `AC_PID` objects are members of heap objects (`AC_AttitudeControl_Multi` at `+376/+616/+856`, `AC_PosControl` at `+384`) allocated by `PMem.alloc` during `Copter::allocate_motors`; their addresses are run-time values. | `AC_PID.pre_of_regions` and the four instance lemmas: `Pre` from the stack predicate (`StackOK s stackBase memSize 16`) and the owning object lying in the heap region `[heapBase, stackBase)` (proved). `PMem.alloc` does not check that the heap stays below `stackBase`; that is an obligation on the initialization run (OPEN.md). |

## Third increment (2026-11-16)

Witnesses checked by `#guard` in `Corpus/Test/Regions.lean`.

| # | Function | Naive statement | Witness | What happens | True statement |
|---|---|---|---|---|---|
| F17 | `AC_PID::update_all` (stack) | the 16 bytes of stack headroom of `Pre` (enough for `update_i`) cover `update_all`: its frame and `update_i`'s, 32 bytes from the stack pointer | `Test/Regions.lean`, `hwm`: the `AC_PID` test state (`kp = ki = kimax = 1`, `I = 0`, `E = 1`, flags `0`), `target = 1`, `measurement = 0`, `dt = 0.01`: the highest stack byte written is `sp + 47` | `update_all` calls `SlewLimiter::modifier` (frame 16 at `sp + 16`), which calls `LowPassFilter<float>::apply` (frame 16 at `sp + 32`) | `update_all` needs 48 bytes: `UPre`, `upre_of_regions` take `StackOK s stackBase memSize 48`; `update_all_agree` names `[sp, sp + 48)` |
| F18 | `PMem.alloc` | `alloc n` hands out a zeroed block of `frameSize n` bytes (what it reserves) | `Test/Regions.lean`, `allocCheck 0x20ee0 17`: the bytes `hp + 17 … hp + 31` keep their old contents (`0xaa`) while `hp` moves by 32 | `alloc` zeroes `n` bytes (`memset base 0 n`) and rounds only the heap pointer | `HeapOK.alloc`: the block `[hp, hp + n)` is zeroed and in the heap region, `hp` moves by `frameSize n`, every byte outside `[hp, hp + n)` is unchanged |

## Fourth increment (2026-11-16)

Witnesses checked by `#guard` in `Corpus/Test/Leaves.lean`.

| # | Function | Naive statement | Witness | What happens | True statement |
|---|---|---|---|---|---|
| F19 | `valid_channel` (`GCS_MAVLink.h:62-65`) | `valid_channel(chan)` iff `chan < 16` | `chan = 0x80000000` (`2^31`): `true` | The translation compares `UInt32.toInt32 chan < 16`, a signed comparison: every value from `2^31` on is negative as an `int` and passes. (C++ promotes the enum to `int` the same way; values `≥ 2^31` do not occur as `mavlink_channel_t`.) | `valid_channel_table`: `chan < 16 ∨ 2^31 ≤ chan` (proved); `valid_channel_of_lt` for `0 … 15`. |
| F20 | `SRV_Channel::should_e_stop` (`SRV_Channel.cpp:325-354`) | as in the C++ source, `true` for `k_motor13 … k_motor32` (160–179), so every `is_motor` function is stopped | `fn = 161` (`k_motor14`): the translation returns `false`; `is_motor(161)` is `true` | **Translation defect.** The source has the GNU case range `case Function::k_motor13 ... Function::k_motor32:`; the translated `switch` tests `sw'1 == 160` only. The same pattern drops `1` from `case 0 ... 1:` in `AP_Mission::mavlink_int_to_mission_cmd` (`AP_Mission.cpp:1144`; translation `sw'32 == 0` only, read off `ArduLean/Vehicle.lean`, not evaluated). Other GNU case ranges in the sources (`SRV_Channel.cpp:391-395` `get_motor_num`, `SRV_Channel_aux.cpp:44-211`, `GCS_serial_control.cpp:77`, `AP_GPS_NMEA.cpp`) were not checked against the translation. The code is frozen; the translator (cpp2lean) needs a fix for `case lo ... hi:`. | What the code does: `should_e_stop_table` (the 21 listed values, 160 the only one of 160–179) and `should_e_stop_of_is_motor` (for a motor function, `should_e_stop ↔ fn ≤ 160`), both proved. |

## F20 corrected (2026-11-16)

The defect of F20 was corrected by hand in `lean/Vehicle_lib.lean` on branch `ardulean`: each case range `case lo ... hi:` now tests `lo ≤ x ∧ x ≤ hi` where the translation tested `x == lo`. The clang syntax trees show ten case ranges in the translated sources; seven are in translated functions, and those are the seven edited conditions:

| C++ site | range | Lean function |
|---|---|---|
| `SRV_Channel.cpp:347` | 160 … 179 (`k_motor13 … k_motor32`) | `SRV_Channel.should_e_stop.pure'` |
| `SRV_Channel_aux.cpp:44` | 51 … 66 (`k_rcin1 … k_rcin16`) | `SRV_Channel.output_ch` |
| `SRV_Channel_aux.cpp:47` | 140 … 155 (`k_rcin1_mapped … k_rcin16_mapped`) | `SRV_Channel.output_ch` |
| `SRV_Channel_aux.cpp:193` | 140 … 155 | `SRV_Channel.aux_servo_function_setup` |
| `SRV_Channel_aux.cpp:211` | 184 … 189 (`k_actuator1 … k_actuator6`) | `SRV_Channel.aux_servo_function_setup` |
| `AP_Mission.cpp:1144` | 0 … 1 | `AP_Mission.mavlink_int_to_mission_cmd.body` |
| `mode_rtl.cpp:123` | 0 … 1 (`RTLAltType::RELATIVE … TERRAIN`) | `ModeRTL.get_alt_type` |

`should_e_stop_table` and `should_e_stop_of_is_motor` (`Code/SRV_Channel/SRV_Channel.lean`) state the corrected behavior. The other three case ranges are in `SRV_Channel::get_motor_num`, which is not translated. The translator on branch `cpp2lean` still has the defect.
