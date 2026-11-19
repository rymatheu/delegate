# Quick controller-only contracts (Q1–Q7)

Library `Quick` (`Contracts/Quick/*.lean`, `lake build Quick`), plus the executable `quick_cex`
(`Contracts/Quick/Cex.lean`, `lake build quick_cex`), which evaluates the counterexamples below on
the translated controller (`tickT` copied verbatim, from `boot w`, `construct lines = .ok w`).
Axioms: `lake env lean AxiomCheck.lean` (standard axioms only for every `Contracts.Quick` theorem).

Status (this file is updated as theorems land):

| | statement | status | file |
|---|---|---|---|
| Q5 | `mission_in_order` | **proved** on `Mctrl w₀`, any sample stream, any dt | `Order.lean` |
| Q1 | `rate_outputs_bounded` | **false as posed** (counterexample); the clamps that exist are proved | `Mixer.lean` |
| Q2 | `rate_targets_bounded` | **false as posed** (counterexample inside the mission's sample envelope); the limiter `ang_vel_limit` is proved | `Rates.lean` |
| Q3 | `tilt_target_bounded` | **false as posed** (finite counterexample, `float` rounding; NaN passes); the limiter is proved for zero reference velocity | `Tilt.lean` |
| Q4 | `nav_reference_limits` | **not proved**; acceleration part false as posed (corner blend), velocity part held on every stream tried | — |
| Q6 | `finite_state_preservation` | **false as posed** (finite sample → NaN state) | — |
| Q7 | dt independence | every proved statement quantifies over the state or samples that carry the period: it holds for every dt | all |

All `Contracts.Quick` theorems depend only on `propext`, `Classical.choice`, `Quot.sound`
(`lake env lean AxiomCheck.lean`). None uses `LibmSpec`: the `float` operations they meet
(`+ - * /`, `sqrtf`, comparisons) are defined through core's `Float32` model.

## Q5 `mission_in_order` (proved, `Contracts/Quick/Order.lean`)

```lean
theorem mission_in_order (w₀ : World) (h0 : w₀.in_auto = false) (hz : w₀.au.loiter_time_max = 0)
    {x : ℕ → Contracts.Mission.X} {s : ℕ → Option World} (hs0 : s 0 = none)
    (hs : ∀ t, (s (t + 1), (x t).out) = Contracts.Mission.tickT w₀ (s t) (x t).smp) :
    (∀ t, ∃ w, s (t + 1) = some w ∧ MInv w₀.mission w) ∧
    (∀ t w w', s (t + 1) = some w → s (t + 2) = some w' →
      OrderStep w₀.mission w w' ∧ NavOrder w₀.mission w w')

theorem mission_in_order_Mctrl {lines : List String} {w : World} (hc : construct lines = .ok w)
    {x : ℕ → Contracts.Mission.X} (hx : x ∈ Contracts.Mission.Mctrl (boot w)) :
    ∃ s, s 0 = none ∧ (∀ t, (s (t + 1), (x t).out) = tickT (boot w) (s t) (x t).smp) ∧
      (∀ t, ∃ v, s (t + 1) = some v ∧ MInv (boot w).mission v) ∧
      (∀ t v v', s (t + 1) = some v → s (t + 2) = some v' →
        OrderStep (boot w).mission v v' ∧ NavOrder (boot w).mission v v')
```

Form: an invariant on the hidden run of `Mctrl w₀` (the index is not a field of the universe `X`,
so an STL atom cannot read it; `s` is the hidden `Option World` of `liftHidden`, unique given the
samples). `s (t+1)` is the world after tick `t`. With `N = w₀.mission.size`:

* `MInv N w` (after every tick): mission unchanged, in Auto, not waiting to start, loiter time limit
  `0`, `-1 ≤ nav_index < N`, state `RUNNING` (then command loaded and `nav_index ≥ 0`) or `COMPLETE`
  (then `nav_index = N - 1`: the mission completes only at the last waypoint's command).
* `NavOrder N w w'` (tick to tick): `idx ≤ idx' ≤ idx + 1`;
  `idx' = idx + 1 ↔ state = RUNNING ∧ reached w ∧ idx + 1 < N`;
  `state' = COMPLETE ↔ state = COMPLETE ∨ (state = RUNNING ∧ reached w ∧ idx + 1 = N)`,
  where `reached w = AC_WPNav::reached_wp_destination w.wps` of the world before the tick.
* `OrderStep` is the same per case (complete stays complete; running and not reached keeps the
  index; running and reached advances or completes).

Preconditions: `w₀.in_auto = false` and `w₀.au.loiter_time_max = 0`; both hold for `boot w` of
every `w` that `construct` returns (`mission_start_of_construct`), so for `MissionWorld w₀`.
Nothing is assumed about the samples (NaN, infinities, any `dt_us`).

What makes it true: the index is written only by `mission_start` (`-1`) and `mission_advance`
(`0` from `-1`, else `+1`, only below `N`); after the first tick `mission_advance` is reached only
from `mission_update` after `verify_nav_wp` reports done, which is exactly `reached_wp_destination`
once `loiter_time_max = 0` (`verify_nav_wp_done`; `do_nav_wp` sets it to `0`); `mission_complete`
is called only when `mission_advance` finds no next waypoint. Every other function the tick calls
keeps the seven mission fields (`mkey`; frame lemmas `mk_replayPos`, `mk_afterWP`, `mk_withMotors`,
`mk_applyPos`, `mk_auto_yaw_set_mode`, `mk_wp_run`, `mk_set_next_wp`, `mk_wp_start`,
`mk_do_nav_wp`, `mk_loiter_start`, `mk_mission_complete`, `verify_nav_wp_mk`; the tick before
`auto_run`: `tick_eq_auto_run`).

## Counterexamples (evaluated with `quick_cex`)

All from `boot w`, `w` built from `MissionData.courseLines` (the mission's parameters), plus the
listed extra parameter lines; first sample at rest at the origin, level, `dt = 2500 µs`.

**Q1 is false for roll/pitch/yaw.** No clamp to `[-1, 1]` exists between the rate PIDs and the
mixer: `rate_controller_run_dt` writes `set_roll := update_all(...) + _actuator_sysid.x`
(`P + D + I`, unclamped; the PD limit acts only when `ATC_RAT_*_PDMX > 0`, default 0), the setters
`AP_MotorsMatrix::set_roll` etc. store the value unchanged, and `output_armed_stabilizing` uses it
unclamped (it only rescales `rpy` jointly). `quick_cex q1`: a second sample with gyro `x = 10 rad/s`
(inside the envelope `smpEnv` of `ψnavA`, 11 rad/s) gives `_roll_in = -4.7958` after the tick.

**Q1 is false for the throttle input.** `AC_PosControl::D_update_controller` sends
`set_throttle_out(-thrust_d_norm)` unclamped and `AC_AttitudeControl_Multi::set_throttle_out` stores
it (`_throttle_in`, then `set_throttle`). `quick_cex q6`: position down `1e300` (a finite double)
gives `_throttle_in = -0.1837`. The mixer's own throttle is clamped (see below).

**Q2 is false.** `attitude_controller_run_quat` applies `ang_vel_limit` and then *adds* the
feedforward, and above 30° of thrust-angle error replaces the yaw target by a blend with the
sampled gyro: `z := gyro.z * (1 - ff_scalar) + z * ff_scalar` (and `z := gyro.z` above 60°).
`quick_cex q2c` with `ATC_RATE_R_MAX = ATC_RATE_P_MAX = ATC_RATE_Y_MAX = 30` (deg/s), second sample
tilted 45° about north, gyro `z = 10 rad/s` (inside `smpEnv`): `rate_bf_targets = (-0.5236, 0,
4.999999)` rad/s, yaw `5.0 > 0.5236`. `quick_cex q2` (upside down, gyro `z = 100`): yaw target
`100`. (In the mission's parameters `ATC_RATE_*_MAX = 0`: no limit at all.)

**Q6 is false.** `quick_cex q6b`: a second sample with velocity north `3e38` (a finite float) gives
`AC_PosControl::_accel_target_ned_mss.x = NaN`, `_roll_target_rad = _pitch_target_rad = NaN`, and a
NaN thrust vector (`get_thrust_vector`). The PID products overflow to `±∞` and their difference is
NaN. So finiteness of the state needs magnitude bounds on the samples (e.g. `smpEnv`) and a
per-field overflow analysis, not finiteness alone. (The world before the bad sample is the world
after one tick at rest from the mission's boot world; the NaN comes from the sample alone, through
the mechanism below, whatever the other finite fields hold.)

**Q3 at tick level** fails for the same stream: the thrust vector is NaN (`q6b`), because
`limit_accel_xy` lets NaN through (`length_squared(accel) ≤ accel_max²` is false on NaN, and
`limit_length` divides by a NaN length).

## Q1: the clamps that exist (`Contracts/Quick/Mixer.lean`, proved)

```lean
theorem rate_pid_nonfinite (p : AC_PID.Params) (s : AC_PID.State) inp (target meas dt : Float32)
    (limit : Bool) (pd i : Float32) (h : target.isFinite = false ∨ meas.isFinite = false) :
    AC_PID.update_all p s inp target meas dt limit pd i = (s, 0.0)

theorem rate_controller_nonfinite (p : Params) (s : State) (o : Outputs) (inp : Inputs) :
    (inp.get_gyro_latest.x.isFinite = false →
      (rate_controller_run p s o inp).2.set_roll = 0.0 + s._actuator_sysid.x) ∧
    (inp.get_gyro_latest.y.isFinite = false →
      (rate_controller_run p s o inp).2.set_pitch = 0.0 + s._actuator_sysid.y) ∧
    (inp.get_gyro_latest.z.isFinite = false →
      (rate_controller_run p s o inp).2.set_yaw = 0.0 + s._actuator_sysid.z)

theorem set_throttle_avg_max_unit01 (ms : AP_MotorsMatrix.State) (v : Float32) :
    Unit01 (AP_MotorsMatrix.set_throttle_avg_max ms v)._throttle_avg_max

theorem update_throttle_filter_out (s : AP_MotorsMatrix.State) inp :
    (update_throttle_filter s inp)._throttle_filter.output.isNaN = true ∨
      Unit01 (update_throttle_filter s inp)._throttle_filter.output
```

`Unit01 a := a.IsFinite ∧ 0 ≤ a.toReal ∧ a.toReal ≤ 1`. What makes each true:

* `AC_PID::update_all`'s entry guard `if (!isfinite(target) || !isfinite(measurement)) return 0`;
  so a non-finite gyro sample on an axis gives the mixer `0 + _actuator_sysid` on that axis
  (`rate_controller_target_reset` sets `_actuator_sysid` to zero at every tick; nothing in the
  harness writes it otherwise).
* `AP_Motors::set_throttle_avg_max`: `constrain_value(v, 0, 1)` (NaN goes to the midpoint).
* `AP_MotorsMulticopter::update_throttle_filter`: after the low-pass step, `if < 0 reset 0`,
  `if > 1 reset 1`; a NaN passes both, so the mixer's throttle `get_throttle()` is NaN or in
  `[0, 1]` (precondition for `[0, 1]`: the filter's output is not NaN). This is the first step of
  `AP_MotorsMulticopter::output`; `output_armed_stabilizing` then clamps its local
  `throttle_thrust` to `[0, throttle_thrust_max]` (not a stored field), and the actuators are clamped
  to `[0, 1]` by `set_actuator_with_slew` (the Track campaign's M1).

Not proved here: that `output_logic`, `output_armed_stabilizing`, `output_to_motors` leave
`_throttle_filter` alone (true by inspection: no write to it; a `mvcgen` frame proof of
`output_armed_stabilizing` did not finish in 4 minutes), so the statement is at the
`update_throttle_filter` call, not after the whole tick.

## Q2: the rate limiter (`Contracts/Quick/Rates.lean`, proved)

```lean
theorem ang_vel_limit_z (e : Vector3f.State) (r p y : Float32) (hy0 : is_zero_float y = false)
    (hyf : y.IsFinite) (hyb : |y.toReal| ≤ maxFinite32 / 2) :
    (ang_vel_limit e r p y).z.IsFinite ∧ |(ang_vel_limit e r p y).z.toReal| ≤ |y.toReal|

theorem ang_vel_limit_x_single (e r p y) (hr0 : is_zero_float r = false)
    (hp0 : is_zero_float p = true) (hrf : r.IsFinite) (hrb : |r.toReal| ≤ maxFinite32 / 2) :
    (ang_vel_limit e r p y).x.IsFinite ∧ |(ang_vel_limit e r p y).x.toReal| ≤ |r.toReal|
-- ang_vel_limit_y_single: the same for pitch with a zero roll limit

theorem ang_vel_limit_xy (e : Vector3f.State) (r p y : Float32) (hx : e.x.IsFinite)
    (hy : e.y.IsFinite) (hr : r.IsFinite) (hp : p.IsFinite) (hx' : |e.x.toReal| ≤ 2 ^ 16)
    (hy' : |e.y.toReal| ≤ 2 ^ 16) (hr0 : is_zero_float r = false) (hp0 : is_zero_float p = false)
    (hr2 : |r.toReal| ≤ 2 ^ 20) (hp2 : |p.toReal| ≤ 2 ^ 20) :
    (ang_vel_limit e r p y).x.IsFinite ∧
      |(ang_vel_limit e r p y).x.toReal| ≤ |r.toReal| * (1 + 1 / 2 ^ 19) + 1 / 2 ^ 50 ∧
    (ang_vel_limit e r p y).y.IsFinite ∧
      |(ang_vel_limit e r p y).y.toReal| ≤ |p.toReal| * (1 + 1 / 2 ^ 19) + 1 / 2 ^ 50
```

What makes them true: `AC_AttitudeControl::ang_vel_limit` (`AC_AttitudeControl.cpp:1206-1226`):
yaw (and roll or pitch when the other limit is zero) by `constrain_value(·, -max, max)`, which holds
for every input, NaN included; roll and pitch together by scaling `(x/r, y/p)` by its `float`
length when that exceeds 1, which needs finite inputs (a NaN length fails `> 1` and the NaN passes)
and costs a relative `2^-19` of rounding. The limits are `radians(ATC_RATE_*_MAX)`; their value as
reals needs `LibmSpec.f64ToF32` (`radians` multiplies by `(float)M_PI / 180`), so the theorems are
stated for any finite limit `y`, `r`, `p`.

As posed (after a tick) Q2 is false (counterexample above): the limiter's output is not the stored
target; `attitude_controller_run_quat` adds the feedforward and mixes in the sampled gyro afterwards.

## Q3: the lean limiter (`Contracts/Quick/Tilt.lean`, proved for zero reference velocity)

```lean
theorem limit_accel_xy_bound (v a : Vector2f.State) (m : Float32) (hx : a.x.IsFinite)
    (hy : a.y.IsFinite) (hx' : |a.x.toReal| ≤ 2 ^ 40) (hy' : |a.y.toReal| ≤ 2 ^ 40)
    (hm : m.IsFinite) (hm1 : 1 / 2 ^ 23 ≤ m.toReal) (hm2 : m.toReal ≤ 2 ^ 40)
    (hv : is_positive_float (Vector2f.length v) = false) :
    (limit_accel_xy v a m).1.x.IsFinite ∧ (limit_accel_xy v a m).1.y.IsFinite ∧
      N2 (limit_accel_xy v a m).1.x.toReal (limit_accel_xy v a m).1.y.toReal ≤
        m.toReal * (1 + 1 / 2 ^ 19) + 1 / 2 ^ 70

theorem limit_length_bound (v : Vector2f.State) (m : Float32) (hx : v.x.IsFinite)
    (hy : v.y.IsFinite) (hx' : |v.x.toReal| ≤ 2 ^ 40) (hy' : |v.y.toReal| ≤ 2 ^ 40)
    (hm : m.IsFinite) (hm1 : 1 / 2 ^ 23 ≤ m.toReal) :
    (limit_length v m).1.x.IsFinite ∧ (limit_length v m).1.y.IsFinite ∧
      N2 (limit_length v m).1.x.toReal (limit_length v m).1.y.toReal ≤
        m.toReal * (1 + 1 / 2 ^ 19) + 1 / 2 ^ 70
```

`N2 a b = √(a² + b²)`. `AC_PosControl::NE_update_controller` passes
`limit_accel_xy(vel_desired / vel_max, accel_target_NE, accel_max)` with
`accel_max = 9.80665 · tanf(min(althold_lean_angle_max, get_lean_angle_max_rad()))`, and
`get_thrust_vector` is `(accel_target.x, accel_target.y, -9.80665)`; so the theorem bounds the
tangent of the commanded tilt by `tan(angle_max) (1 + 2^-19)` (plus `2^-70 / g`) on the ticks where
the navigator's desired velocity is zero (hover, ends of legs). Turning it into an angle needs a
`tanf` accuracy hypothesis, which `LibmSpec` does not have yet.

**Q3 as posed is false**, already for finite inputs. With a non-zero reference velocity
`limit_accel_xy` limits the cross-track component with `limit_length` and the along-track component
with `constrain_value(dir, ±sqrt(max² - |cross|²))`; the cross-track part is
`accel - ref·(ref·accel)`, whose `float` rounding is of the order of `2^-24 |accel|`, so a huge
along-track acceleration leaves a spurious cross-track part that the along-track allowance does not
account for:

* function level (`quick_cex q3`): `accel = (-1507693, 30746904)`, `vel_norm = (-0.03738, 0.7623)`,
  `accel_max = 5.66` → output length `1.2435 · accel_max`; the excess grows with `|accel| / accel_max`
  (search over `|accel| ≤ 10^2`: `1.000005`; `≤ 10^4`: `1.00048`; `≤ 10^6`: `1.029`);
* tick level (`quick_cex q3t`): nominal feedback stream to tick 500, then one sample with velocity
  `2·10^7 m/s` off the target along the track: `|thrust_NE| = 1.0114 · g tan(30°)` (tilt 30.3°);
* a NaN or overflowing acceleration passes the limiter (`quick_cex q6b`: NaN thrust vector).

## Q4: navigator references (not proved)

Evaluated (`quick_cex q4`, nominal feedback stream, 12000 ticks, the mission's parameters
`WP_SPD = 1`, `WP_SPD_UP = 2.5`, `WP_SPD_DN = 1.5`, `WP_ACC = 1.5`, `WP_ACC_Z = 1`, `WP_ACC_C = 0`,
i.e. corner acceleration `2 · WP_ACC = 3`): largest horizontal desired speed `0.99999998`, up
`0.7165`, down `0.1697`, vertical acceleration `1.0`; **largest horizontal desired acceleration
`2.1213 = 1.5 √2` at tick 1386** (corner `w0 → w1`): the corner blend adds the decelerating and the
accelerating leg (`SCurve::advance_target_along_track` with `_scurve_next_leg`), so the acceleration
part of Q4 against `WP_ACC` is false; a bound by the corner acceleration (`WP_ACC_C`, or `2 WP_ACC`)
is what the code is designed for. No Lean proof: the bound must come from the S-curve's segment
table (`SCurve::calculate_path`, `add_segments`, `get_jerk_accel_vel_pos_at_time` with `powf`, which
`LibmSpec` does not cover) and the blend, which is the scope of the navigator campaign
(`Contracts/Mission/SCurveReal.lean` has the real-valued segment formulas, not yet the table
bounds). The clamps on the way are `track_dt_scalar ∈ [0, 1]` (`constrain_value` in
`advance_wp_target_along_track`; it scales time, not velocity) and `vel_dt_scalar =
_offset_vel / _wp_desired_speed` (shaped by `shape_vel_accel`, not clamped).

## Q6: finite state preservation (false)

`quick_cex q6b`: from the mission's boot world, one tick at rest, then a sample with north velocity
`3e38` (finite) gives NaN in `AC_PosControl::_accel_target_ned_mss.x`, `_roll_target_rad`,
`_pitch_target_rad` and the thrust vector. Mechanism: `AC_PID_2D` forms the velocity error
`-3e38`, its derivative `/ dt` and its products with the gains overflow to `∓∞`, and
`Vector2f::limit_length` computes `∞ · (max / ∞) = NaN`. Finiteness of the world
needs magnitude bounds on the samples (e.g. `smpEnv`) and a per-field overflow budget. Fields that
are finite after every call whatever the input, by a clamp: `_throttle_avg_max`
(`set_throttle_avg_max_unit01`), the PID integrators (Track's M2), the actuators (Track's M1), and
the yaw rate leaving `ang_vel_limit` when its limit is non-zero.

## Files

* `Contracts/Quick/Order.lean` (Q5), `Mixer.lean` (Q1), `Rates.lean` (Q2), `Tilt.lean` (Q3, and the
  rounding core `flen_ge`, `N2`), `Cex.lean` (the executable `quick_cex`: `q1 nan q2 q2b q2c q3 q3t
  q4 q6 q6b q6c thr`).
* `lakefile.toml`: `[[lean_lib]] Quick` and `[[lean_exe]] quick_cex` (neither is a default target:
  `lake build Quick quick_cex`).
