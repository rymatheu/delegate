# Ledger

Generated from `tests/CorpusAudit.lean` (`LEAN_NUM_THREADS=1 lake env lean tests/CorpusAudit.lean`) on
2026-11-16 (fourth increment), after a clean `LEAN_NUM_THREADS=1 lake build Corpus` (the `Corpus` outputs under
`.lake/build` deleted first): 3 min 58 s wall clock.

Pure leaves covered: 257 of 381 (every one of the 256 that return a value; 1 of the 125 `Unit`-valued ones).

## Audit

```
theorems in Corpus.Code.*: 727
rule 2 (statement names a code constant): 727 of 727; violations: []
rule 4 (axioms): violations: []
axioms used: [Quot.sound, Classical.choice, propext]
theorems by kind: [(Wrapper, 253), (Case, 158), (Safety, 29), (Range, 28), (Order, 19), (Meaning, 49), (Effect, 44), (Invariant, 3), (Protocol, 144)]
pure leaves covered (at least two theorems): 257 of 381; returning a value: 256 of 256
```

The kind of a theorem is read from its name suffix. A **Wrapper** is the one-line lemma `f … = pure (f.pure' …)`. A
theorem counts for every code function in its conclusion. If the conclusion names none, as with
`sqrt_controller_accel_divisor`, it counts for the code functions in its hypotheses. Second increment: the classifier
also counts `odd`/`comm` as Order and `_pre`/`pre_of`/`bridged`/`layout` as Safety (address safety). Third increment: `_agree`,
`_triple`, `_call`, `_size`, `_run'`, `_state` count as Effect, `_cases` and `integrator_of_` as Case (they would
otherwise fall under `integrator` = Effect), `_upre`/`upre_of` as Safety. Hypothesis plumbing without a code constant
(`UBody.pre`, `UBody.wok`, `ModBody.wok`, `LPFApplyPre.inner`, `lpfMem_get!`, `lpfMem_w32`, `IBound.stable`) is
`private`, as `Pre.toNat4` and its siblings already were; the audit does not list private theorems, and their axioms
are counted through the public theorems that use them. Fourth increment: `_table` counts as Protocol, names containing
`toNat`/`toInt` as Meaning, `ne_zero` as Safety (no earlier theorem changes kind); the audit also prints the pure-leaf
coverage (a leaf `f.pure'` is covered when at least two theorems name `f` or `f.pure'` in their conclusion).

## First increment (Tier 0, AP_Math) against the plan's table

| Function | Plan wants | State |
|---|---|---|
| `is_zero`, `is_positive'float`, `is_negative'float` | Case (exact threshold), NaN, Meaning | complete |
| `is_equal'float_float` | Case, NaN, Meaning | complete (second increment: `is_equal_comm`, `is_equal_self`) |
| `sq`, `norm` | Case, Safety, Range | complete (second increment: `sq_nonneg_of_not_isNaN`, `norm_nonneg_of_not_isNaN`, overflow included); `|a| ≤ norm a b` open (F3) |
| `radians`, `degrees`, `cd_to_rad` | Case, Safety, Range | complete; second increment: `_odd` (as words), `_mono` (through overflow), `_isNaN` |
| `constrain_value_line'float` | NaN case, range, identity, idempotent, monotone, one of three | complete (second increment: `constrain_float_mem_of_isNaN`, `_mem_all`, `_not_isNaN_all`, `_idem_all` for finite `low + high`; `_odd`); FINDINGS F1 |
| `constrain_value'short`, `constrain_int16` | Range, identity, idempotent, monotone | complete (for `low ≤ high`; FINDINGS F2) |
| `safe_sqrt'float` | of nonneg, of negative, of NaN, never NaN, nonneg, Meaning | complete |
| `safe_asin'float` | Case for all four branches, never NaN and range under a premise | complete (premise `AsinfRange`) |
| `wrap_2PI`, `wrap_PI'float` | Case, range under a premise, 2π edge tested | complete (premise `FmodfRange`; range closed, FINDINGS F5–F7) |
| `input_expo` | Case, odd, fixes 0, range | Case, odd (`input_expo_odd`), fixes 0 (`input_expo_zero`) proved; range for `expo ≥ 0.95` proved, for `expo < 0.95` open; FINDINGS F11, F12 |
| `sqrt_controller_accel`, `inv_sqrt_controller`, `stopping_distance`, `angle_rad_to_accel_mss`, `accel_mss_to_angle_rad` | Case per branch, Safety (which branches divide, by what) | complete: every branch has a Case lemma whose hypotheses guard its divisor; `sqrt_controller_accel_divisor`; `accel_mss_to_angle_rad_not_isNaN` (premise `AtanfNotNaN`). Second increment: `sqrt_controller_accel_not_isNaN`, `sqrt_controller_accel_opposes_nonneg` (`p ≥ 0`), `inv_sqrt_controller_odd` (`p ≥ ε`, `|output| ≥ ε`); `inv_sqrt_controller` NaN freedom open; FINDINGS F8–F10, F14, F15 |
| mode tables | Protocol by evaluation | complete for the 97 constant answers (+ `mode_numbers_nodup`); the 4 memory-reading ones done in the second increment (`_run`) |
| tier-1 trial `AC_PID.update_i` | Effect, Invariant | proved: `update_i_shape`, `update_i_frame`, `update_i_w32`, `update_i_kimax`, `update_i_integrator`, `update_i_preserves_bound`, under the hypotheses `Pre`; second increment: `Pre` discharged from region facts (`pre_of_regions`, four instance lemmas), exact update value (`update_i_shape_exact`, `update_i_integrator_exact`) |

Counting the 22 functions of the table plus the mode tables as one entry, after the second increment 21 of 23 have
the lemma set the plan asks for. Two are partial: `input_expo` (range for `expo < 0.95`) and `inv_sqrt_controller`
(NaN freedom); `norm`'s `|a| ≤ norm a b` (F3) is beyond the plan's table. Progress on the controller path (822
definitions) has not been measured yet.

## Second increment (2026-11-16)

| Item | State |
|---|---|
| 1. Four float lemmas (`Machine/Float.lean`) | done: sign under overflow (`mul_self_nonneg'`, `add_nonneg'`, `mul_nonneg_of_isFinite'`, `mul_nonpos_of_isFinite'`, `div_nonneg_of_pos`; general tool `toEReal_roundDyadic` with the overflow threshold `isFinite_roundDyadic_of_abs_roundAt_le`); negation (`neg_mul'`, `mul_neg'`, `neg_div'` as words when the result is a number; `sub_antisymm` in value, F13); monotone multiplication through overflow (`mul_le_mul_of_pos_right'`, finite `c > 0`, `±∞` operands); doubling (`genericFormat_two_mul`, `midpoint_mem`) |
| 1. AP_Math / Control closures | done except `input_expo` range (not attempted) and `inv_sqrt_controller` NaN freedom (blocked, OPEN.md) |
| 2. `Pre` for the real PID objects | done modulo two region facts (F16, OPEN.md): `pre_of_regions`, `rate_{roll,pitch,yaw}_pid_pre`, `accel_pid_pre`; `Machine/Memory`: `enter_run` (any `k`, frame ≤ 4096), `memcpy_run` (any `n`), `InRegion`, `StackOK`, `StackOK.enter`, `StackOK.leave` |
| 3. `update_all` | partial: callees `calc_lowpass_alpha_dt`, `get_filt_*_alpha`, `is_positive` (param), `MIN`, `DigitalLPF::_apply`, `SlewLimiter::get_slew_rate` done; `update_i` exact; `LowPassFilter::apply`, `SlewLimiter::modifier`, `update_all` not started (OPEN.md says what each needs) |
| 4. Memory-reading mode-table functions | done: `ModeAuto.mode_number_run` (+ `_val`), `ModeAuto.requires_position_run`, `ModeAuto.option_is_enabled_run`, `ModeAuto.allows_arming_run`, `ModeGuided.option_is_enabled_run`, `ModeGuided.allows_arming_run` |

## Third increment (2026-11-16)

| Item | State |
|---|---|
| 1. Counted loops (`Machine/Loop.lean`) | done: `forIn_range` (a range is the loop over `List.range'`), unrolling `forIn_range_0_1` … `_0_4` (`simp`), `forIn_cons_run`, `forIn_list_inv`/`forIn_range_inv` (invariant `I`, early exit to `Q` via `StepOK`), `forIn_range_state` |
| 1. Fuel loops | done: `fuel_loop_zero_run`, `fuel_loop_succ_run`, `fuel_loop_inv`/`loopFuel_inv` (conclusion: `Q`, or `fuelOut` set and an `I` state with the flag set), `loopFuel_of_fuelOut_false` |
| 1. Bit-fields, small integers (`Machine/Memory.lean`) | done: `ldBits_run`, `stBits_run` (one-bit fields at bit `o < 8`), `ldBits_stBits_self`, `ldBits_stBits_ne` (other bits of the byte kept), `stBits_get!_ne` (other bytes kept), `bitOf_setBit_self/_ne`; `ldI8_run`, `ldU64_run`; every load leaves the state unchanged at any address (`ldU8/ldB/ldI8/ldWord/ldU32/ldF32/ldU64/ldBits_state`) |
| 1. (new) Hoare triples (`Machine/Hoare.lean`) | `Triple`, `Agree`, `Inv`, `Stable`, `WOk`; rules for bind, pure, `if`, `discard`, counted loops, join points (`Triple.jp` and the tactic `triple_let`), stores into raw bytes (`stF32'`, `stU32'`, `stU8'`, `stB'`, `stBits'`, `memcpy'`), callees (`Triple.call`), the reset-then-index pattern (`reset_index`); tactics `triple_step`, `sub_tac`; `Agree.frame` (enter/leave); `Raw.sub`, `inBridgeN_false_iff` |
| 2. `LowPassFilter<float>::apply` | done: `LowPassFilter_apply_run` (reduction to `DigitalLPF::_apply`), `LowPassFilter_apply_eq` (Case: the two returns), `LowPassFilter_apply_agree` (Effect: `[this, this+5)` and its frame) |
| 2. `SlewLimiter::modifier` | Effect done (`modifier_agree`: `[this+16, this+78)` and 32 bytes of stack; `modifier_body_triple`); Case for `!is_positive(dt)` (`modifier_of_not_pos`); the other two returns open (OPEN.md) |
| 2. `AC_PID::update_all` | Effect (`update_all_agree`: `[this+48, this+200)` and 48 bytes of stack), Invariant (`update_all_preserves_bound`: `-kimax ≤ integrator ≤ kimax`, `kimax` finite `≥ 0`), Case (`update_all_of_not_finite`), `UPre` from regions (`upre_of_regions`, `rate_{roll,pitch,yaw}_pid_upre`, `accel_pid_upre`); the reset path and NaN freedom open (OPEN.md) |
| 2. `update_i` conditions | done: `update_i_integrator_cases` (the value as an `if` on the code's conditions), `_of_off`, `_of_hold`, `_of_update`; `update_i_agree`, `update_i_size`, `update_i_preserves_ibound` |
| 3(a). Stack across a call | done: `StackOK.call` (callee gets `n - frameSize k`, the caller's predicate holds after `leave`); depth on the path to `update_i` 176 bytes, 192 at the deepest point under `update_all` (Test/Regions.lean, frames checked by `rfl`); `update_all` itself needs 48 (F17) |
| 3(b). Heap | partial: `alloc_run`, `HeapOK`, `HeapOK.alloc` (block `InRegion … heapBase stackBase n`, heap predicate kept, hp moves by `frameSize n`, other bytes kept), `HeapOK.alloc_disjoint`; static construction evaluated (`hp = 0x20ee0`); `AP_Vehicle::setup` (where the two controllers are allocated) calls the HAL and cannot be evaluated by the interpreter: obligation in OPEN.md |
| 4. `inv_sqrt_controller` not NaN, `input_expo` range | not started |

## Fourth increment (2026-11-16)

| Item | State |
|---|---|
| 1. `SlewLimiter::modifier`, the other two returns | done: `modifier_eq` (the value as `modVal dt M msr`: `M` the target of the `slew_rate_max` reference, `msr` the field `+32` as the call leaves it), `modifier_of_nonpos_max`, `modifier_of_le`, `modifier_of_gt`; `modifier_body_value`, `modifier_lpf_pinned_triple`; tested in `Test/Modifier.lean` (all four branches occur) |
| 1. `update_all` return value and fields | partial: statement written and tested (`Test/UpdateAllValue.lean`, 3456 states); a proof built in a scratch development exceeds 3,000,000 heartbeats as one declaration and is not in the library (OPEN.md item 1 says how to split it) |
| 1. `update_all` not NaN | not started |
| 1. `Machine/Hoare.lean` | value-tracking loads (`bind_val`, `ldF32_val`, `ldU32_val`, `ldU64_val`, `ldBits_val`, `pure_val`), pins (`stF32_pin`, `memcpy4_pin`, `Stable.pin32`, `pinBit`, `and_w32`, `and_const`, `mono`), `stBits_keep`, join points with a chosen precondition (`Triple.jp_with`, tactics `triple_jp`, `triple_jp_w32`), `triple_zeta_pure`, `guard_not_jp`, `guard_jp_call`, `Triple.of_jp`, `sub_tac'`, `stable_tac`, `triple_step'`, and memory-only symbolic execution (`MemIs`, `bind_exact`, `mem_step`, `ldF32_mem`, `ldBits_mem`, `stF32_mem`, `stB_mem`, `stBits_mem`, `val_mem`, `MemIs.agree`) |
| 2. Survey | `SURVEY-pure.md`: the 381 `f.pure'` by source file with fan-in (from the code text: the callgraph file lists only recursive components) and coverage; the 101 scalar functions of `Estimator_lib` |
| 2. Breadth | 133 further pure leaves, every value-returning one now covered (256 of 256): `Machine/Int.lean` (integer promotions, `table_tac`, `table_tac32`, address arithmetic), 12 new `Code/` files and additions to `AP_Param`, `AP_Math`, `Filter` (list below); findings F19 (`valid_channel` is a signed comparison), F20 (translation defect: GNU case ranges keep their low end only, `should_e_stop`) |
| 3. `inv_sqrt_controller` not NaN, `input_expo` range | not started |

New pure leaves by corpus file (getters returning `this + k` get `_eq`, `_pure_eq`, `_toNat`; getters returning
`this` get `_eq`, `_pure_eq`; constant answers get `_eq`, `_val`; the others as listed in each file):

- `AC_AttitudeControl/Accessors.lean` (18): the `AC_AttitudeControl`, `AC_AttitudeControl_Multi`, `AC_PosControl`
  member accessors; `get_roll_trim_cd`, `get_roll_trim_rad` (`= 0`).
- `AC_PID/Accessors.lean` (15): `AC_PID.kP/kI/kD/ff/filt_T_hz/filt_E_hz/get_pid_info`, `AC_PID_2D.kP/ff/get_error`,
  `AC_PID_Basic.kP`, `AC_P.kP`, `AC_P_1D.kP`, `AC_P_2D.kP/get_error`.
- `AC_WPNav/Accessors.lean` (2): `AC_WPNav.get_wp_destination_NED_m`, `AC_Circle.get_center_NED_m`.
- `AP_BattMonitor/AP_BattMonitor.lean` (5): `get_cell_voltages` (Meaning), `calculate_mah` (Case, NaN), three constants.
- `AP_Common/AP_Common.lean` (9): `Location.diff_longitude` (Case, Meaning, Range), `limit_lattitude` (Meaning, Range,
  identity), `wrap_longitude` (Meaning, Range), `Bitmask<102/190/317>.validate`, `Bitmask<317>.size`,
  `is_bounded_int32`, `AP_CANManager.get_num_drivers`.
- `AP_Math/AP_Math.lean` (12): `is_zero (double)` (Case, NaN), `norm (float³)` (Case, never NaN and `≥ 0`), `sq`/`norm`
  over `double` (Case), `atan2 (int, int)`, `is_equal (double, double)` (Case, NaN), `radians (int)` (`= radians` of the
  conversion), `check_lat`, `check_lng` (Case as float bounds, NaN, `check_lat → check_lng`).
- `AP_Math/Accessors.lean` (5): `Vector3<float>::xy`, `Vector3<double>::xy`, `Vector3<float>::operator[]` (Meaning),
  `SplineCurve::get_destination_vel`, `SCurve::get_origin_to_destination`.
- `AP_Mission/AP_Mission.lean` (11): `stored_in_location`, `cmd_has_location`, `is_landing_type_cmd`,
  `is_takeoff_type_cmd` (Protocol tables), the six `start_command_*` constants, `get_current_nav_cmd`.
- `AP_Param/AP_Param.lean` (14): the 13 `AP_ParamT`/`AP_ParamTBase`/`AP_ParamV` accessors, `type_size` (table, `≤ 12`).
- `AP_SerialManager/AP_SerialManager.lean` (1): `map_baudrate` (table, codes `≤ 0`); codes above 2000 open.
- `ArduCopter/Copter.lean` (8): `Copter.mode_from_mode_num` (table, non-null for the build's modes), `Copter.gcs`,
  `Mode.gcs`, `AP_Arming.method_is_GCS`, four constants.
- `Filter/Filter.lean` (2): `DigitalLPF<float>::get`, `DigitalLPF<Vector3f>::get`.
- `GCS_MAVLink/GCS.lean` (22): `mav_param_type` (table, range), `valid_channel` (F19), `mavlink_msg_target_field`
  (Meaning `min t 255`, Range), `command_long_stores_location`, `command_int_only`,
  `should_send_message_in_delay_callback` (tables), both `capabilities` (values), `convert_COMMAND_LONG_loc_param`
  (three cases), three accessors, eight constants.
- `RC_Channel/RC_Channel.lean` (5): `RC_Channels_Copter.channel` (null from 16, Meaning below), both
  `get_rcmap_channel_nonnull` (never null), `init_position_on_first_radio_read` (table), `string_for_aux_pos` (table).
- `SRV_Channel/SRV_Channel.lean` (4): `get_motor_function` (Meaning; the first 32 are motors), `valid_function`,
  `is_motor`, `should_e_stop` (table; F20).

Of the 133, 83 are member accessors or constant answers (their lemmas are evaluations), 50 have case splits, tables or
arithmetic meanings.

## Coverage per code function

| code function | Wrapper | Case | Safety | Range | Order | Meaning | Effect | Invariant | Protocol |
|---|---|---|---|---|---|---|---|---|---|
| `AC_AttitudeControl.get_angle_pitch_p` | 1 | 1 |  |  |  | 1 |  |  |  |
| `AC_AttitudeControl.get_angle_roll_p` | 1 | 1 |  |  |  | 1 |  |  |  |
| `AC_AttitudeControl.get_angle_yaw_p` | 1 | 1 |  |  |  | 1 |  |  |  |
| `AC_AttitudeControl.get_att_target_euler_rad` | 1 | 1 |  |  |  | 1 |  |  |  |
| `AC_AttitudeControl.get_attitude_target_ang_vel` | 1 | 1 |  |  |  | 1 |  |  |  |
| `AC_AttitudeControl.get_roll_trim_cd` | 1 | 1 |  |  |  |  |  |  | 1 |
| `AC_AttitudeControl.get_roll_trim_rad` | 1 | 1 |  |  |  |  |  |  | 1 |
| `AC_AttitudeControl_Multi.get_rate_pitch_pid` |  |  | 2 |  |  |  |  |  |  |
| `AC_AttitudeControl_Multi.get_rate_roll_pid` |  |  | 2 |  |  |  |  |  |  |
| `AC_AttitudeControl_Multi.get_rate_yaw_pid` |  |  | 2 |  |  |  |  |  |  |
| `AC_AttitudeControl_Multi.get_rate_yaw_pid'2` | 1 | 1 |  |  |  | 1 |  |  |  |
| `AC_Circle.get_center_NED_m` | 1 | 1 |  |  |  | 1 |  |  |  |
| `AC_P.kP` | 1 | 1 |  |  |  |  |  |  |  |
| `AC_PID.ff` | 1 | 1 |  |  |  | 1 |  |  |  |
| `AC_PID.filt_E_hz` | 1 | 1 |  |  |  | 1 |  |  |  |
| `AC_PID.filt_T_hz` | 1 | 1 |  |  |  | 1 |  |  |  |
| `AC_PID.get_filt_D_alpha` |  |  |  |  |  |  | 2 |  |  |
| `AC_PID.get_filt_E_alpha` |  |  |  |  |  |  | 2 |  |  |
| `AC_PID.get_filt_T_alpha` |  |  |  |  |  |  | 2 |  |  |
| `AC_PID.get_pid_info` | 1 | 1 |  |  |  | 1 |  |  |  |
| `AC_PID.kD` | 1 | 1 |  |  |  | 1 |  |  |  |
| `AC_PID.kI` | 1 | 1 |  |  |  | 1 |  |  |  |
| `AC_PID.kP` | 1 | 1 |  |  |  |  |  |  |  |
| `AC_PID.update_all` |  | 1 |  |  |  |  | 1 | 1 |  |
| `AC_PID.update_all.body` |  |  |  |  |  |  | 1 |  |  |
| `AC_PID.update_i` |  | 4 |  |  |  |  | 10 | 2 |  |
| `AC_PID_2D.ff` | 1 | 1 |  |  |  | 1 |  |  |  |
| `AC_PID_2D.get_error` | 1 | 1 |  |  |  | 1 |  |  |  |
| `AC_PID_2D.kP` | 1 | 1 |  |  |  |  |  |  |  |
| `AC_PID_Basic.kP` | 1 | 1 |  |  |  |  |  |  |  |
| `AC_P_1D.kP` | 1 | 1 |  |  |  |  |  |  |  |
| `AC_P_2D.get_error` | 1 | 1 |  |  |  | 1 |  |  |  |
| `AC_P_2D.kP` | 1 | 1 |  |  |  |  |  |  |  |
| `AC_PosControl.D_get_accel_pid` |  |  | 2 |  |  |  |  |  |  |
| `AC_PosControl.D_get_pos_p` | 1 | 1 |  |  |  | 1 |  |  |  |
| `AC_PosControl.D_get_vel_pid` | 1 | 1 |  |  |  | 1 |  |  |  |
| `AC_PosControl.NE_get_pos_p` | 1 | 1 |  |  |  | 1 |  |  |  |
| `AC_PosControl.NE_get_vel_pid` | 1 | 1 |  |  |  | 1 |  |  |  |
| `AC_PosControl.get_accel_target_NED_mss` | 1 | 1 |  |  |  | 1 |  |  |  |
| `AC_PosControl.get_pos_desired_NED_m` | 1 | 1 |  |  |  | 1 |  |  |  |
| `AC_PosControl.get_pos_estimate_NED_m` | 1 | 1 |  |  |  | 1 |  |  |  |
| `AC_PosControl.get_pos_offset_NED_m` | 1 | 1 |  |  |  | 1 |  |  |  |
| `AC_PosControl.get_vel_desired_NED_ms` | 1 | 1 |  |  |  | 1 |  |  |  |
| `AC_PosControl.get_vel_estimate_NED_ms` | 1 | 1 |  |  |  | 1 |  |  |  |
| `AC_WPNav.get_wp_destination_NED_m` | 1 | 1 |  |  |  | 1 |  |  |  |
| `AP_Arming.method_is_GCS` | 1 |  |  |  |  |  |  |  | 1 |
| `AP_Arming_Copter.oa_checks` | 1 |  |  |  |  |  |  |  | 1 |
| `AP_Arming_Copter.winch_checks` | 1 |  |  |  |  |  |  |  | 1 |
| `AP_BattMonitor.get_cell_voltages` | 1 |  |  |  |  | 1 |  |  |  |
| `AP_BattMonitor_Backend.calculate_mah` | 1 | 2 |  |  |  |  |  |  |  |
| `AP_BattMonitor_Backend.get_mavlink_fault_bitmask` | 1 |  |  |  |  |  |  |  | 1 |
| `AP_BattMonitor_Backend.has_cell_voltages` | 1 |  |  |  |  |  |  |  | 1 |
| `AP_BattMonitor_Backend.has_temperature` | 1 |  |  |  |  |  |  |  | 1 |
| `AP_CANManager.get_num_drivers` | 1 |  |  |  |  |  |  |  | 1 |
| `AP_Mission.cmd_has_location` | 1 | 1 |  |  |  |  |  |  | 1 |
| `AP_Mission.get_current_nav_cmd` | 1 | 1 |  |  |  | 1 |  |  |  |
| `AP_Mission.is_landing_type_cmd` | 1 |  |  |  |  |  |  |  | 1 |
| `AP_Mission.is_takeoff_type_cmd` | 1 |  |  |  |  |  |  |  | 1 |
| `AP_Mission.start_command_do_gimbal_manager_pitchyaw` | 1 |  |  |  |  |  |  |  | 1 |
| `AP_Mission.start_command_do_scripting` | 1 |  |  |  |  |  |  |  | 1 |
| `AP_Mission.start_command_do_set_roi` | 1 |  |  |  |  |  |  |  | 1 |
| `AP_Mission.start_command_do_set_roi_wpnext_offset` | 1 |  |  |  |  |  |  |  | 1 |
| `AP_Mission.start_command_do_sprayer` | 1 |  |  |  |  |  |  |  | 1 |
| `AP_Mission.start_command_parachute` | 1 |  |  |  |  |  |  |  | 1 |
| `AP_Mission.stored_in_location` | 1 | 2 |  |  |  |  |  |  | 1 |
| `AP_Param.type_size` | 1 |  |  | 1 |  |  |  |  | 1 |
| `AP_ParamT'float_4.operator_'3` |  |  |  |  |  |  | 1 |  |  |
| `AP_ParamT'float_4.operator_const_float__'1` | 1 | 1 |  |  |  |  | 2 |  |  |
| `AP_ParamT'int_3.operator_const_int__` | 1 | 1 |  |  |  |  |  |  |  |
| `AP_ParamT'short_2.operator_const_short__` | 1 | 1 |  |  |  |  |  |  |  |
| `AP_ParamT'signed_char_1.operator_const_signed_char__` | 1 | 1 |  |  |  |  |  |  |  |
| `AP_ParamT'unsigned_char_1.operator_const_unsigned_char__` | 1 | 1 |  |  |  |  |  |  |  |
| `AP_ParamT'unsigned_int_3.operator_const_unsigned_int__` | 1 | 1 |  |  |  |  |  |  |  |
| `AP_ParamT'unsigned_short_2.operator_const_unsigned_short__` | 1 | 1 |  |  |  |  |  |  |  |
| `AP_ParamTBase'float_4.get` | 1 | 1 |  |  |  |  |  |  |  |
| `AP_ParamTBase'int_3.get` | 1 | 1 |  |  |  |  |  |  |  |
| `AP_ParamTBase'short_2.get` | 1 | 1 |  |  |  |  |  |  |  |
| `AP_ParamTBase'signed_char_1.get` | 1 | 1 |  |  |  |  |  |  |  |
| `AP_ParamTBase'unsigned_int_3.get` | 1 | 1 |  |  |  |  |  |  |  |
| `AP_ParamTBase'unsigned_short_2.get` | 1 | 1 |  |  |  |  |  |  |  |
| `AP_ParamV'Vector3_float_5.get` | 1 | 1 |  |  |  |  |  |  |  |
| `AP_SerialManager.map_baudrate` | 1 | 1 |  |  |  |  |  |  | 1 |
| `Bitmask'102.validate` | 1 | 1 |  |  |  |  |  |  |  |
| `Bitmask'190.validate` | 1 | 1 |  |  |  |  |  |  |  |
| `Bitmask'317.size` | 1 |  |  |  |  |  |  |  | 1 |
| `Bitmask'317.validate` | 1 | 1 |  |  |  |  |  |  |  |
| `Copter.gcs` | 1 | 2 |  |  |  | 1 |  |  |  |
| `Copter.get_rangefinder_height_interpolated_m` | 1 |  |  |  |  |  |  |  | 1 |
| `Copter.is_tradheli` | 1 |  |  |  |  |  |  |  | 1 |
| `Copter.mode_from_mode_num` | 1 |  | 1 |  |  |  |  |  | 1 |
| `DigitalLPF'Vector3_float.get` | 1 | 1 |  |  |  |  |  |  |  |
| `DigitalLPF'float._apply` |  |  |  |  |  |  | 2 |  |  |
| `DigitalLPF'float.get` | 1 | 1 |  |  |  |  |  |  |  |
| `GCS.min_status_for_gps_healthy` | 1 |  |  |  |  |  |  |  | 1 |
| `GCS.statustext_queue` | 1 | 1 |  |  |  | 1 |  |  |  |
| `GCS_Copter.min_loop_time_remaining_for_message_send_us` | 1 |  |  |  |  |  |  |  | 1 |
| `GCS_MAVLINK.capabilities` | 1 |  |  |  |  |  |  |  | 1 |
| `GCS_MAVLINK.channel_buffer` | 1 | 1 |  |  |  | 1 |  |  |  |
| `GCS_MAVLINK.channel_status` | 1 | 1 |  |  |  | 1 |  |  |  |
| `GCS_MAVLINK.command_long_stores_location` | 1 |  |  |  |  |  |  |  | 1 |
| `GCS_MAVLINK.mav_param_type` | 1 |  |  | 1 |  |  |  |  | 1 |
| `GCS_MAVLINK.persist_streamrates` | 1 |  |  |  |  |  |  |  | 1 |
| `GCS_MAVLINK.should_send_message_in_delay_callback` | 1 |  |  |  |  |  |  |  | 1 |
| `GCS_MAVLINK_Copter.capabilities` | 1 |  |  |  |  |  |  |  | 1 |
| `GCS_MAVLINK_Copter.command_int_only` | 1 |  |  |  |  |  |  |  | 1 |
| `GCS_MAVLINK_Copter.vtol_state` | 1 |  |  |  |  |  |  |  | 1 |
| `Location.diff_longitude` | 1 | 1 |  | 1 |  | 1 |  |  |  |
| `Location.limit_lattitude` | 1 |  |  | 2 |  | 1 |  |  |  |
| `Location.wrap_longitude` | 1 |  |  | 1 |  | 1 |  |  |  |
| `LowPassFilter'float.apply` |  | 1 |  |  |  |  | 4 |  |  |
| `MIN'unsigned_int_unsigned_int` |  |  |  |  |  |  | 2 |  |  |
| `MissionItemProtocol.allocate_receive_resources` | 1 |  |  |  |  |  |  |  | 1 |
| `MissionItemProtocol.allocate_update_resources` | 1 |  |  |  |  |  |  |  | 1 |
| `MissionItemProtocol_Waypoints.mission_type` | 1 |  |  |  |  |  |  |  | 1 |
| `MissionItemProtocol_Waypoints.next_item_ap_message_id` | 1 |  |  |  |  |  |  |  | 1 |
| `Mode.allows_GCS_or_SCR_arming_with_throttle_high` | 1 |  |  |  |  |  |  |  | 1 |
| `Mode.allows_entry_in_rc_failsafe` | 1 |  |  |  |  |  |  |  | 1 |
| `Mode.allows_save_trim` | 1 |  |  |  |  |  |  |  | 1 |
| `Mode.crash_check_enabled` | 1 |  |  |  |  |  |  |  | 1 |
| `Mode.crosstrack_error_m` | 1 |  |  |  |  |  |  |  | 1 |
| `Mode.enabled` | 1 |  |  |  |  |  |  |  | 1 |
| `Mode.exit` | 1 |  |  |  |  |  |  |  | 1 |
| `Mode.gcs` | 1 | 2 |  |  |  |  |  |  |  |
| `Mode.get_avoidance_adjusted_climbrate_ms` | 1 |  |  |  |  |  |  |  | 1 |
| `Mode.get_wp` | 1 |  |  |  |  |  |  |  | 1 |
| `Mode.has_user_takeoff` | 1 |  |  |  |  |  |  |  | 1 |
| `Mode.in_guided_mode` | 1 |  |  |  |  |  |  |  | 1 |
| `Mode.init` | 1 |  |  |  |  |  |  |  | 1 |
| `Mode.is_landing` | 1 |  |  |  |  |  |  |  | 1 |
| `Mode.move_vehicle_on_ekf_reset` | 1 |  |  |  |  |  |  |  | 1 |
| `Mode.pause` | 1 |  |  |  |  |  |  |  | 1 |
| `Mode.requires_terrain_failsafe` | 1 |  |  |  |  |  |  |  | 1 |
| `Mode.resume` | 1 |  |  |  |  |  |  |  | 1 |
| `Mode.set_speed_NE_ms` | 1 |  |  |  |  |  |  |  | 1 |
| `Mode.set_speed_down_ms` | 1 |  |  |  |  |  |  |  | 1 |
| `Mode.set_speed_up_ms` | 1 |  |  |  |  |  |  |  | 1 |
| `Mode.use_pilot_yaw` | 1 |  |  |  |  |  |  |  | 1 |
| `Mode.wp_bearing_deg` | 1 |  |  |  |  |  |  |  | 1 |
| `Mode.wp_distance_m` | 1 |  |  |  |  |  |  |  | 1 |
| `ModeAltHold.allows_arming` | 1 |  |  |  |  |  |  |  | 1 |
| `ModeAltHold.allows_save_trim` | 1 |  |  |  |  |  |  |  | 1 |
| `ModeAltHold.has_manual_throttle` | 1 |  |  |  |  |  |  |  | 1 |
| `ModeAltHold.has_user_takeoff` | 1 |  |  |  |  |  |  |  | 1 |
| `ModeAltHold.is_autopilot` | 1 |  |  |  |  |  |  |  | 1 |
| `ModeAltHold.mode_number` | 1 |  |  |  |  |  |  |  | 2 |
| `ModeAltHold.name` | 1 |  |  |  |  |  |  |  | 1 |
| `ModeAltHold.name4` | 1 |  |  |  |  |  |  |  | 1 |
| `ModeAltHold.requires_position` | 1 |  |  |  |  |  |  |  | 1 |
| `ModeAuto.allows_GCS_or_SCR_arming_with_throttle_high` | 1 |  |  |  |  |  |  |  | 1 |
| `ModeAuto.allows_arming` |  |  |  |  |  |  | 1 |  |  |
| `ModeAuto.has_manual_throttle` | 1 |  |  |  |  |  |  |  | 1 |
| `ModeAuto.is_autopilot` | 1 |  |  |  |  |  |  |  | 1 |
| `ModeAuto.mode_number` |  |  |  |  |  |  | 1 |  | 1 |
| `ModeAuto.option_is_enabled` |  |  |  |  |  |  | 1 |  |  |
| `ModeAuto.requires_position` |  |  |  |  |  |  | 1 |  |  |
| `ModeAuto.requires_terrain_failsafe` | 1 |  |  |  |  |  |  |  | 1 |
| `ModeAuto.verify_loiter_unlimited` | 1 |  |  |  |  |  |  |  | 1 |
| `ModeBrake.allows_arming` | 1 |  |  |  |  |  |  |  | 1 |
| `ModeBrake.has_manual_throttle` | 1 |  |  |  |  |  |  |  | 1 |
| `ModeBrake.is_autopilot` | 1 |  |  |  |  |  |  |  | 1 |
| `ModeBrake.mode_number` | 1 |  |  |  |  |  |  |  | 2 |
| `ModeBrake.name` | 1 |  |  |  |  |  |  |  | 1 |
| `ModeBrake.name4` | 1 |  |  |  |  |  |  |  | 1 |
| `ModeBrake.requires_position` | 1 |  |  |  |  |  |  |  | 1 |
| `ModeCircle.allows_arming` | 1 |  |  |  |  |  |  |  | 1 |
| `ModeCircle.has_manual_throttle` | 1 |  |  |  |  |  |  |  | 1 |
| `ModeCircle.is_autopilot` | 1 |  |  |  |  |  |  |  | 1 |
| `ModeCircle.mode_number` | 1 |  |  |  |  |  |  |  | 2 |
| `ModeCircle.name` | 1 |  |  |  |  |  |  |  | 1 |
| `ModeCircle.name4` | 1 |  |  |  |  |  |  |  | 1 |
| `ModeCircle.requires_position` | 1 |  |  |  |  |  |  |  | 1 |
| `ModeGuided.allows_GCS_or_SCR_arming_with_throttle_high` | 1 |  |  |  |  |  |  |  | 1 |
| `ModeGuided.allows_arming` |  |  |  |  |  |  | 1 |  |  |
| `ModeGuided.get_target_accel_NED_mss` | 1 |  |  |  |  |  |  |  | 1 |
| `ModeGuided.get_target_pos_NED_m` | 1 |  |  |  |  |  |  |  | 1 |
| `ModeGuided.get_target_vel_NED_ms` | 1 |  |  |  |  |  |  |  | 1 |
| `ModeGuided.has_manual_throttle` | 1 |  |  |  |  |  |  |  | 1 |
| `ModeGuided.has_user_takeoff` | 1 |  |  |  |  |  |  |  | 1 |
| `ModeGuided.in_guided_mode` | 1 |  |  |  |  |  |  |  | 1 |
| `ModeGuided.is_autopilot` | 1 |  |  |  |  |  |  |  | 1 |
| `ModeGuided.mode_number` | 1 |  |  |  |  |  |  |  | 2 |
| `ModeGuided.name` | 1 |  |  |  |  |  |  |  | 1 |
| `ModeGuided.name4` | 1 |  |  |  |  |  |  |  | 1 |
| `ModeGuided.option_is_enabled` |  |  |  |  |  |  | 1 |  |  |
| `ModeGuided.requires_position` | 1 |  |  |  |  |  |  |  | 1 |
| `ModeGuided.requires_terrain_failsafe` | 1 |  |  |  |  |  |  |  | 1 |
| `ModeLand.allows_arming` | 1 |  |  |  |  |  |  |  | 1 |
| `ModeLand.has_manual_throttle` | 1 |  |  |  |  |  |  |  | 1 |
| `ModeLand.is_autopilot` | 1 |  |  |  |  |  |  |  | 1 |
| `ModeLand.is_landing` | 1 |  |  |  |  |  |  |  | 1 |
| `ModeLand.mode_number` | 1 |  |  |  |  |  |  |  | 2 |
| `ModeLand.name` | 1 |  |  |  |  |  |  |  | 1 |
| `ModeLand.name4` | 1 |  |  |  |  |  |  |  | 1 |
| `ModeLand.requires_position` | 1 |  |  |  |  |  |  |  | 1 |
| `ModeLoiter.allows_arming` | 1 |  |  |  |  |  |  |  | 1 |
| `ModeLoiter.has_manual_throttle` | 1 |  |  |  |  |  |  |  | 1 |
| `ModeLoiter.has_user_takeoff` | 1 |  |  |  |  |  |  |  | 1 |
| `ModeLoiter.is_autopilot` | 1 |  |  |  |  |  |  |  | 1 |
| `ModeLoiter.mode_number` | 1 |  |  |  |  |  |  |  | 2 |
| `ModeLoiter.name` | 1 |  |  |  |  |  |  |  | 1 |
| `ModeLoiter.name4` | 1 |  |  |  |  |  |  |  | 1 |
| `ModeLoiter.requires_position` | 1 |  |  |  |  |  |  |  | 1 |
| `ModeRTL.allows_arming` | 1 |  |  |  |  |  |  |  | 1 |
| `ModeRTL.has_manual_throttle` | 1 |  |  |  |  |  |  |  | 1 |
| `ModeRTL.is_autopilot` | 1 |  |  |  |  |  |  |  | 1 |
| `ModeRTL.mode_number` | 1 |  |  |  |  |  |  |  | 2 |
| `ModeRTL.name` | 1 |  |  |  |  |  |  |  | 1 |
| `ModeRTL.name4` | 1 |  |  |  |  |  |  |  | 1 |
| `ModeRTL.requires_position` | 1 |  |  |  |  |  |  |  | 1 |
| `ModeRTL.requires_terrain_failsafe` | 1 |  |  |  |  |  |  |  | 1 |
| `ModeStabilize.allows_arming` | 1 |  |  |  |  |  |  |  | 1 |
| `ModeStabilize.allows_entry_in_rc_failsafe` | 1 |  |  |  |  |  |  |  | 1 |
| `ModeStabilize.allows_save_trim` | 1 |  |  |  |  |  |  |  | 1 |
| `ModeStabilize.has_manual_throttle` | 1 |  |  |  |  |  |  |  | 1 |
| `ModeStabilize.is_autopilot` | 1 |  |  |  |  |  |  |  | 1 |
| `ModeStabilize.mode_number` | 1 |  |  |  |  |  |  |  | 2 |
| `ModeStabilize.name` | 1 |  |  |  |  |  |  |  | 1 |
| `ModeStabilize.name4` | 1 |  |  |  |  |  |  |  | 1 |
| `ModeStabilize.requires_position` | 1 |  |  |  |  |  |  |  | 1 |
| `RC_Channel.init_position_on_first_radio_read` | 1 |  |  |  |  |  |  |  | 1 |
| `RC_Channel.string_for_aux_pos` | 1 |  |  |  |  |  |  |  | 1 |
| `RC_Channels.get_rcmap_channel_nonnull` | 1 | 2 | 1 |  |  |  |  |  |  |
| `RC_Channels.get_rcmap_channel_nonnull'2` | 1 | 1 | 1 |  |  |  |  |  |  |
| `RC_Channels_Copter.channel` | 1 | 2 |  |  |  | 1 |  |  |  |
| `SCurve.get_origin_to_destination` | 1 | 1 |  |  |  | 1 |  |  |  |
| `SRV_Channel.is_motor` | 1 | 2 |  |  |  |  |  |  |  |
| `SRV_Channel.should_e_stop` | 1 | 1 |  |  |  |  |  |  | 1 |
| `SRV_Channel.valid_function'2` | 1 | 1 |  |  |  |  |  |  |  |
| `SRV_Channels.get_motor_function` | 1 | 1 |  |  |  | 1 |  |  |  |
| `SlewLimiter.get_slew_rate` |  |  |  |  |  |  | 2 |  |  |
| `SlewLimiter.modifier` |  | 4 |  | 1 |  |  | 2 |  |  |
| `SlewLimiter.modifier.body` |  | 1 |  |  |  |  | 1 |  |  |
| `SplineCurve.get_destination_vel` | 1 | 1 |  |  |  | 1 |  |  |  |
| `Vector3'double.xy` | 1 | 1 |  |  |  |  |  |  |  |
| `Vector3'float.operator__` | 1 |  |  |  |  | 1 |  |  |  |
| `Vector3'float.xy` | 1 | 1 |  |  |  |  |  |  |  |
| `accel_mss_to_angle_rad` | 1 | 1 | 1 |  |  |  |  |  |  |
| `addr'copter` |  |  | 1 |  |  |  |  |  |  |
| `angle_rad_to_accel_mss` | 1 | 1 |  |  |  |  |  |  |  |
| `atan2'int_int_0` | 1 | 1 |  |  |  |  |  |  |  |
| `calc_lowpass_alpha_dt` |  |  |  |  |  |  | 5 |  |  |
| `camera_command_result_param2'mavlink_command_int_t` | 1 |  |  |  |  |  |  |  | 1 |
| `camera_command_result_param2'mavlink_command_long_t` | 1 |  |  |  |  |  |  |  | 1 |
| `cd_to_rad` | 1 | 2 | 2 | 1 | 2 |  |  |  |  |
| `check_lat'2` | 1 | 2 |  |  |  |  |  |  |  |
| `check_lng'2` | 1 | 3 |  |  |  |  |  |  |  |
| `constrain_int16` | 1 | 1 |  | 2 | 2 |  |  |  |  |
| `constrain_value'short` | 1 | 2 |  |  |  |  |  |  |  |
| `constrain_value_line'float` | 1 | 8 | 2 | 4 | 4 | 1 | 2 |  |  |
| `convert_COMMAND_LONG_loc_param` | 1 | 3 |  |  |  |  |  |  |  |
| `degrees` | 1 | 1 | 1 | 1 | 2 |  |  |  |  |
| `heapBase` |  |  | 3 |  |  |  |  |  |  |
| `input_expo` | 1 | 2 |  | 1 | 1 |  |  |  |  |
| `inv_sqrt_controller` | 1 | 6 |  |  | 1 |  |  |  |  |
| `is_bounded_int32` | 1 | 1 |  |  |  |  |  |  |  |
| `is_equal'double_double` | 1 | 2 |  |  |  |  |  |  |  |
| `is_equal'float_float` | 1 | 2 |  |  | 1 |  |  |  |  |
| `is_negative'float` | 1 | 3 |  |  | 3 | 1 | 1 |  |  |
| `is_positive'AP_ParamT_float_AP_PARAM_FLOAT` |  |  |  |  |  |  | 2 |  |  |
| `is_positive'float` | 1 | 4 |  |  | 2 | 1 | 1 |  |  |
| `is_zero` | 1 | 6 | 1 |  | 1 | 1 | 2 |  |  |
| `is_zero'2` | 1 | 2 |  |  |  |  |  |  |  |
| `is_zero'AP_ParamT_float_AP_PARAM_FLOAT` |  |  |  |  |  |  | 1 |  |  |
| `mavlink_msg_target_field` | 1 |  |  | 1 |  | 1 |  |  |  |
| `memSize` |  |  | 3 |  |  |  |  |  |  |
| `norm` | 1 | 1 | 1 | 1 |  |  |  |  |  |
| `norm'2` | 1 | 2 | 1 |  |  |  |  |  |  |
| `norm'double_double` | 1 | 1 |  |  |  |  |  |  |  |
| `norm'double_double_double` | 1 | 1 |  |  |  |  |  |  |  |
| `radians` | 1 | 2 | 2 | 1 | 2 | 1 |  |  |  |
| `radians'2` | 1 | 1 |  |  |  |  |  |  |  |
| `safe_asin'float` | 1 | 4 |  | 2 |  |  |  |  |  |
| `safe_sqrt'float` | 1 | 3 | 1 | 3 |  | 1 |  |  |  |
| `sq` | 1 | 4 | 1 | 1 |  | 1 |  |  |  |
| `sq'double` | 1 | 1 |  |  |  |  |  |  |  |
| `sq'double_double` | 1 | 1 |  |  |  |  |  |  |  |
| `sq'double_double_double` | 1 | 1 |  |  |  |  |  |  |  |
| `sqrt_controller_accel` | 1 | 7 | 1 | 1 |  |  |  |  |  |
| `stackBase` |  |  | 3 |  |  |  |  |  |  |
| `stopping_distance` | 1 | 1 |  |  |  |  |  |  |  |
| `valid_channel` | 1 | 1 |  |  |  |  |  |  | 1 |
| `wrap_2PI` | 1 | 2 |  | 1 |  |  |  |  |  |
| `wrap_PI'float` | 1 | 1 |  | 1 |  |  |  |  |  |
