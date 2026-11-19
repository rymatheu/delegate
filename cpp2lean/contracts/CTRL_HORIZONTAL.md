# C-series for the horizontal channel (milestone M6, float part)

This note documents `Contracts/Track/CtrlHorizontal*.lean` (library `Track`). The lemmas connect the
translated horizontal controller (`AC_PosControl::NE_update_controller`) to the real model of
`HORIZONTAL.md` (`Contracts/Track/Horizontal.lean`). They give the rows HORIZONTAL.md §7 asks for,
each as "the `float` result is the ideal real row of the `float` inputs, plus `β`, `|β|` explicit",
and compose them into `horizontal_tick_eq`, the form `A_h ξ + forcing + w` that
`Horizontal.errOf_traj_dist` and `course_tube` take.

Everything is sorry-free. `#print axioms` shows only `propext`, `Classical.choice` and `Quot.sound`
(AxiomCheck.lean, end of file). `LibmSpec` enters as an argument (the opaque conversions
`(double) f`, `(float) d`).

## Status

| function | lemma | file | status |
|---|---|---|---|
| tools: `flen_le`, `limit_length_inactive`, `lensq_le_sq`, `limit_accel_xy_inactive`, `alpha5` | | `CtrlHorizontalBase.lean` | done |
| `AC_P_2D::update_all` (position P, sqrt controller linear zone) | `p_spec` | `CtrlHorizontalP.lean` | done |
| `AC_PID_2D::update_all` (velocity PID) | `pid_spec` | `CtrlHorizontalPID.lean` | done |
| `limit_accel_xy` (inactive) | `limit_accel_xy_inactive` | `CtrlHorizontalBase.lean` | done |
| `NE_update_controller` (composition) | `ne_spec` | `CtrlHorizontalNE.lean`, `CtrlHorizontalSpec.lean` | done |
| `update_estimates` (C1, horizontal rows) | `estimates_ne`, `estimates_ne_world` | `CtrlHorizontalTick.lean` | done |
| `get_thrust_vector` (horizontal part) | `thrust_xy`, `thrust_after_D` | `CtrlHorizontalTick.lean` | done |
| `D_update_controller` leaves the horizontal fields alone | `d_frame` | `CtrlHorizontalTick.lean` | done |
| the tick | `horizontal_tick_eq`, `horizontal_tick_eq_D` | `CtrlHorizontalTick.lean` | done |

## 1. Parameters (field hypotheses)

* `PosGains` (`_p_pos_ne_m`): `kp = 1.5` (`PSC_NE_POS_P`), `_D1_max ∈ [1, 2²⁰]`, `_error_max`
  either not positive or at least `1/2`.
* `VelGains` (`_pid_vel_ne_m`, `_dt_s`): `kp = 6`, `ki = 1`, `kd = 1/2`, `kff = 0`, `kimax = 10`,
  `_filt_E_hz = _filt_D_hz = 5`, `⟦_dt_s⟧ = dtf = 5368709/2³¹` (`0.0025f`).
* The filter coefficient is computed by the code each tick (`calc_lowpass_alpha_dt`). `alpha5` proves
  it is within `2⁻²²` of `αE = 4886901/2²⁶`, the `float` value HORIZONTAL.md lists. `LibmSpec` does not
  determine `(float) M_PI` (both neighbors of `π` are within its `2⁻²⁴` relative bound), so the
  coefficient is bounded rather than fixed. The proof is that of `CtrlV.alpha5`
  (`CtrlVerticalFloat.lean`); it is restated here, so the horizontal files do not depend on the
  vertical ones.
* `get_control_gain_scaler_XY = 1`, `_ne_control_scale_factor = 1` (values).
* The acceleration limit `nAmax = 9.80665 · tanf(min(althold lean max, lean max))` is a hypothesis
  on its value (`tanf` is not in `LibmSpec`): finite, in `[2⁻²⁰, 2⁴⁰]`.

## 2. The region (`NERegion`)

* `NE_handle_ekf_reset` is the identity (reset counts equal); `NE_is_active`.
* Offsets zero after `NE_update_offsets` (`OffZero (nS3 s inp)`), disturbances zero.
* Position: finite `double`s, `|sp - p| ≤ 2/5` as a 2-vector. This is the sqrt controller's linear
  zone with margin (`D1_max / kp² ≥ 4/9`; in flight `D1_max = 1.5`, linear distance `2/3`).
* `|vsp| ≤ 3`, `|v| ≤ 4`, `|asp| ≤ 4` per axis.
* The PID (`PIDState`): `_reset_filter = false`, `|E| ≤ 4`, `|D| ≤ 64` per axis, `|I| ≤ 9` as a
  2-vector (inside `IMAX = 10`, so `limit_length` is inactive), the limit vector `_limit_vector_ned.xy`
  zero (the limiter did not act on the previous tick).
* D7: the ideal command `c` of the law (`lawC`, from the values before the tick) satisfies
  `|c| + 10⁻³ ≤ nAmax (1 - 2⁻²⁰)` as a 2-vector. Then `limit_accel_xy` is inactive
  (`limit_accel_xy_inactive`, for every reference velocity).

## 3. The rows (`ne_spec`, `NEAxis`, per axis)

With `sp, p, vsp, v, asp` the values of `_pos_desired_ned_m`, `_pos_estimate_ned_m`,
`_vel_desired_ned_ms`, `_vel_estimate_ned_ms`, `_accel_desired_ned_mss`, and `E, D, I` those of
`_pid_vel_ne_m` before the call:

| row | statement | `β` |
|---|---|---|
| `vt` (`p_spec` + feed-forward) | `⟦vt⟧ = 1.5 (sp - p) + vsp + β` | `5·10⁻⁷` |
| `E⁺` | `⟦E⁺⟧ = E + αE ((⟦vt⟧ - v) - E) + β` | `3.5·10⁻⁶` |
| `D⁺` | `⟦D⁺⟧ = D + αE ((⟦E⁺⟧ - E)/dtf - D) + β` | `1.2·10⁻⁴` |
| `I⁺` | `⟦I⁺⟧ = I + ki dtf ⟦E⁺⟧ + β` | `6·10⁻⁷` |
| PID output | `⟦out⟧ = kp ⟦E⁺⟧ + ⟦I⁺⟧ + kd ⟦D⁺⟧ + β` | `1.5·10⁻⁵` |
| `accel_target` | `⟦acc⟧ = ⟦out⟧ + asp + β` | `6·10⁻⁶` |

`p_spec` alone: `⟦P output⟧ = 1.5 (sp - p) + β`, `|β| ≤ 2.5·10⁻⁷`. Below `|e| = 2⁻²³` the code
returns the zero vector (`is_positive(error_length)` false); `1.5 |e|` is then below `1.8·10⁻⁷`,
inside the same `β`. In the linear branch the output is `e · ((|e| kp)/|e|)`: the rounding of the
length cancels, and the factor is within `2.1·10⁻⁷` of `1.5` (`ratio_near`).

The `β` of `E⁺` and `D⁺` are dominated by the coefficient's bound `2⁻²²` (`alpha5`) times the region's
bounds on `(t - m) - E` and `(E⁺ - E)/dt - D`; with the exact coefficient they are `5·10⁻⁷` and
`2·10⁻⁵`.

After the call, the new `_pid_vel_ne_m` is the PID's (`_reset_filter = false`) and the limit vector
`_limit_vector_ned.xy` is `Int32.toFloat32 0`, so the PID part of the region carries the limit
condition to the next tick. The bounds `|E|, |D|, |I|` are not invariant under the crude region; they
are hypotheses per tick (the closed-loop values are orders of magnitude inside).

## 4. The tick (`horizontal_tick_eq`)

Per axis, with `ξ = (p - sp, v - vsp, E, D, I, a, c₁, c₂, c₃)` (`xiOf`) and
`ξ⁺ = (pN - spN, vN - vspN, ⟦E⁺⟧, ⟦D⁺⟧, ⟦I⁺⟧, a', ⟦acc⟧, c₁, c₂)` (`xiNext`), where

* the plant rows are hypotheses: `pN = p + h v + h²/2 a + ρp`, `vN = v + h a + ρv` (PLANT.md;
  `ρ` is the plant remainder);
* the attitude interface is a hypothesis, as `Horizontal.lean` parameterizes it:
  `a' = a + αL (c₃ - a) + η`;

the theorem gives `ξ⁺ = A_h ξ + (asp B_h - d₁ e₀ - d₂ e₁) + w`, with
`d₁ = defect₁ sp spN vsp asp`, `d₂ = defect₂ vsp vspN asp` (the target sequence's defects) and
`w = wOf …` within `WBound`:

| `w` | value or bound |
|---|---|
| `w₀`, `w₁` | `ρp`, `ρv` |
| `w₂` (`E`) | `≤ 3.6·10⁻⁶` |
| `w₃` (`D`) | `≤ 2.3·10⁻⁴` |
| `w₄` (`I`) | `≤ 6.1·10⁻⁷` |
| `w₅` | `η` |
| `w₆` (command) | `≤ 1.6·10⁻⁴` |
| `w₇`, `w₈` | `0` |

`rows_compose` does the propagation: `w₂ = β_E + αE β_vt`, `w₃ = β_D + (αE/dtf) w₂`,
`w₄ = β_I + ki dtf w₂`, `w₆ = β_acc + β_out + kp w₂ + w₄ + kd w₃`.

The command row is `get_thrust_vector(s').xy` (`thrust_xy`: the thrust vector is
`(accel_target.x, accel_target.y, -g)`). `horizontal_tick_eq_D` states the same after
`D_update_controller` (`d_frame`: it writes only `.z` of the acceleration target and of the limit
vector and does not touch `_pid_vel_ne_m`, provided the vertical controller is active). That is the
thrust vector `wp_run` hands to `input_thrust_vector_heading`. C1 (`estimates_ne_world`): the
estimates the controller reads are the sample of the world (`posInputs`), exactly.

## 5. What is not covered

* `OffZero` is a hypothesis on the state after `NE_update_offsets`. With zero offset targets, the
  offsets should stay zero (`update_pos_vel_accel_xy` adds zero steps; `shape_pos_vel_accel_xy` of
  zeros is zero); this invariant is not proved here.
* The ordering inside `Vehicle.tick` (the navigator's log calls `NE_update_controller` once per tick
  with the targets it has just set, through `replayPos`) belongs to the navigator lemmas. The
  theorems here take the state handed to `NE_update_controller` and the region on it.
* `nAmax` (`tanf`) is a value hypothesis.
* The attitude interface (`η`) and the plant remainder (`ρ`) are hypotheses, as HORIZONTAL.md §7
  states.

## 6. Files

All in `contracts/Contracts/Track/`:

* `CtrlHorizontalBase.lean`: the comparisons of `AP_Math`, `alpha5`, `B32` helpers, `flen_le`,
  `limit_length_inactive`, `lensq_le_sq`, `limit_accel_xy_inactive`.
* `CtrlHorizontalP.lean`: `p_update_all_eq`, `sqrtc_vec_eq`, `sqrtc_lin`, `ratio_near`, `out_comp`,
  `err_comp`, `PosGains`, `PosRegion`, `p_spec`.
* `CtrlHorizontalPID.lean`: `update_all_eq`, `rowE`, `rowD`, `rowI`, `rowOut`, `update_i_zero`,
  `VelGains`, `VelRegion`, `PIDAxis`, `pid_axis`, `pid_spec`.
* `CtrlHorizontalNE.lean`: frames of `calculate_yaw_and_rate_yaw` and `NE_update_offsets`, the names
  of the intermediate values (`nS3`, `nPosTgt`, `nCombPos`, `nP`, `nVelP`, `nVelT`, `nCombVel`,
  `nPID`, `nAccP`, `nAcc`, `nAmax`, `nVnorm`), the field lemmas `ne_pid`, `ne_raw`, `ne_out`, the
  laws `lawVt … lawC`, `rows_compose`, `OffZero`, `PIDState`, `AxisIn`, `NERegion`, `NEAxis`.
* `CtrlHorizontalSpec.lean`: `ne_spec`.
* `CtrlHorizontalTick.lean`: `estimates_ne`, `estimates_ne_world`, `thrust_xy`, `xiOf`, `xiNext`,
  `wOf`, `WBound`, `axis_tick`, `horizontal_tick_eq`, `HFrame`, `d_frame`, `thrust_after_D`,
  `horizontal_tick_eq_D`.

**Lean notes.**

* A structure literal whose fields continue on a new line at a smaller column than `{` does not
  parse (`expected '}'`); keep such literals on one line or name them.
* The result of `NE_update_controller` is reached by `unfold`, `simp only [Id.run, …]` with the
  frame lemmas of the callees, `split` on the remaining `if`s, and `rfl` against the named
  intermediate values. An `if` inside a named value (`nVnorm`) blocks `rfl`; split on its condition
  first. `erw` against the unfolded body timed out.
* `linarith` sometimes misses a chain through `2 ^ (-24 : ℤ)` atoms; combining the two inequalities
  first (`err.trans h3`) fixes it.
