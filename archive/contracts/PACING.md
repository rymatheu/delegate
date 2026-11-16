# Target pacing (milestone M8)

This note documents `Contracts/Track/Pacing*.lean` (library `Track`), milestone M8 of
TRACK_PLAN.md: lemmas P-1, P-2 and P-3 of TRACK_PLAN.md §5, and the hold at `w7`. Everything is
sorry-free. `#print axioms` (AxiomCheck.lean, end of file) shows only `propext`,
`Classical.choice` and `Quot.sound`. `LibmSpec` enters as an argument of `hold_w7` and
`hold_course` (through the navigator's `loiter_dest_bound`); P-1 and P-2 need no libm hypothesis.

Build: `lake build Contracts.Track.PacingArrive` (about 2 min from a built Mission library).

## 0. Results

| lemma | statement | Lean |
|---|---|---|
| the filter step of the code | `_track_dt_scalar ← s + (rawScaler … − s) · (dt / tc)` without terrain following | `advance_track_dt_scalar` |
| raw scaler in `[0, 1]` | for all inputs (NaN and infinities included) | `rawScaler_unit` |
| **P-1** | `rawScaler ≥ min 1 (1.05 − (ε_v + 1.5 ε_e)/v_min − 10⁻³)` | `rawScaler_ge`, `rawScaler_ge_iso` |
| filter coefficient | `0.0025f / (1.5f / 5f) = 1118481/2²⁷` (`1/α = 120.0000072`) | `alpha_eval`, `trackTc_eq` |
| one `float` filter step | within `10⁻⁷` of `s + (r − s) α` | `filter_step`, `code_filter_step` |
| **P-2** | a stretch with `s < 1 − η` and `r ≥ ρ` after its first `W` ticks is shorter than `W + n` when `(1 − α)ⁿ(1 + c) + (1 − ρ) + c < η` | `stretch_bound` |
| P-2 on the course | `η = 2/5`, `ρ = 0.7712`: shorter than `W + 212` ticks | `stretch_course` |
| S-curve time step | `fl(s · 1 · 0.0025f) · 400` within `10⁻⁷` of `s` | `prog_step` |
| **P-3** | the nested reach formula from the leg conditions | `leg_arrive`, `leg0_arrive`, `chain_reach`, `pacing_reach` |
| P-3 on the course | the reach conjunct of `ψtrack` | `pacing_course` |
| the hold | the hold conjunct of `ψtrack` | `hold_w7`, `hold_formula`, `hold_course` |

## 1. P-1: the raw scaler (`PacingScaler.lean`)

`rawScaler vT pe ve kP` is the emitted expression of `AC_WPNav.cpp:582-590`, verbatim:
`constrain(0.05f + (ve·d − kP · pe·d) / |vT|, 0, 1)` with `d = vT.normalized()` when
`is_positive(|vT|²)`, else `1`. `advance_track_dt_scalar` proves that the field `_track_dt_scalar`
after `AC_WPNav.advance_wp_target_along_track` is `s + (rawScaler … − s) · (dt / trackTc p)`, the
inputs read from the call's log (`get_vel_desired_NED_ms` minus the vertical offset,
`get_pos_error_NED_m`, `get_vel_estimate_NED_ms`, `NE_get_pos_p_kP`).

```lean
theorem rawScaler_ge (vT pe ve : AC_WPNav_lib.Vector3f.State) (kP : Float32) (hkPf : kP.IsFinite)
    (hkP : kP.toReal = 3 / 2) (hvT : Fin3 vT 3) (hpe : Fin3 pe 4) (hve : Fin3 ve 3)
    {vmin εv εe : ℝ} (hvmin : 1 / 10 ≤ vmin) (hL : vmin ≤ len3 vT) (hε : 0 ≤ εv + 3 / 2 * εe)
    (hv : dot3 vT vT - dot3 ve vT ≤ εv * len3 vT) (he : dot3 pe vT ≤ εe * len3 vT) :
    min 1 (21 / 20 - (εv + 3 / 2 * εe) / vmin - 1 / 1000) ≤ (rawScaler vT pe ve kP).toReal
```

The hypotheses are along the track: `(vT − ve)·vT ≤ ε_v |vT|` (velocity lag) and
`pe·vT ≤ ε_e |vT|` (position error ahead of the vehicle). `rawScaler_ge_iso` is the isotropic form
(`|ve − vT| ≤ ε_v`, `|pe| ≤ ε_e`, Cauchy–Schwarz). The `10⁻³` covers all `float` rounding: the
length within `2⁻²¹` (`len_approx`), the direction within `10⁻⁶` per component (`div_len`), the two
projections and their difference within `3.5·10⁻⁵`, the quotient by the length within `5·10⁻⁴`.

**Why the along-track form.** With the certified isotropic bounds the lower bound is too weak to pace
the course: at the `w0` blend `|v_T|` drops to `0.366` m/s and the climb's vertical error is up to
`0.0875` m, so `1.05 − (0.135 + 1.5 · 0.092)/0.366 < 0.3`. Along the track the measured errors are
small (position `0.0216` m, velocity lag `0.0425` m/s over 15 closed-loop flights), because at the
`w0` blend the climb overshoot is across the new direction.

## 2. P-2: the filter (`PacingFilter.lean`)

`FilterRun s r α ε_f` is `∀ t, |s (t+1) − (s t + (r (t+1) − s t) α)| ≤ ε_f`; `code_filter_step`
proves it for one call of the code with `α = α₀`, `ε_f = 10⁻⁷` (WP_ACC 1.5, WP_JERK 5,
`dt = 0.0025f`; `dt_first` shows the first tick's `1.0f/400.0f` is the same float).

* `filter_bounds`: `s ∈ [−c, 1 + c]`, `c = ε_f/α ≤ 1.3·10⁻⁵`.
* `deficit_sum`: `α Σ(1 − s) ≤ (1 − α)(D₀ − D_n) + α Σ(1 − r) + n ε_f`: the lag of a stretch is its
  raw deficit plus `(1/α − 1) ≈ 119` ticks times the initial deficit.
* `deficit_decay`: while `r ≥ ρ`, `1 − s` decays at rate `1 − α` to `(1 − ρ) + c`.

```lean
theorem stretch_bound (hα0 : 0 < α) (hα1 : α ≤ 1) (hf : FilterRun s r α εf) (hεf : 0 ≤ εf)
    (hs : ∀ t, -(εf / α) ≤ s t ∧ s t ≤ 1 + εf / α) {ρ η : ℝ} (hρ1 : ρ ≤ 1) {W n : ℕ}
    (hn : (1 - α) ^ n * (1 + εf / α) + ((1 - ρ) + εf / α) < η) (t0 L : ℕ)
    (hgood : ∀ k, W < k → k ≤ L → ρ ≤ r (t0 + k)) (hlow : ∀ k ≤ L, s (t0 + k) < 1 - η) :
    L < W + n
```

On the course (`stretch_course`): with `r ≥ 0.7712` after the first `W` ticks, every stretch with
`s < 3/5` is shorter than `W + 212` ticks. `W` is where the raw scaler has no lower bound: the
leg-start phase, while the S-curve speed is below `v_min` (P-1 is vacuous there). On this course the
only such phase is the start of leg 0: the corners are blended (fast waypoints) and the speed stays
above `0.366` m/s from the escape to the arrival at `w7`.

**The leg-start phase needs a closed-loop hypothesis (counterexample).** No tick-wise tracking bound
excludes a freeze at the leg start: `copter_lean36` driven from the nominal start with every sample at
the start position (offset `3` mm down) and zero velocity stalls the target `1.5` cm above the start
for all 12000 ticks, with position error at most `0.0184` m and velocity error at most `0.160` m/s
(`scratchpad/pacing/freeze.py`). The escape comes from the closed-loop dynamics (the velocity
feedforward moves the vehicle ahead, `e·d` turns negative, the scaler returns to 1). It is stated as
the hypothesis `hesc`: by tick `W₀` the S-curve time reaches `τ_v`, the time from which the climb's
speed stays above `v_min`.

## 3. P-3: arrival and the hold (`PacingArrive.lean`)

**Model.** `q t` is the S-curve time after tick `t`, in ticks: the sum of the steps
`_track_dt_scalar · vel_dt_scalar · dt` passed to `SCurve::advance_target_along_track`.
`prog_step` proves `|step · 400 − s| ≤ 10⁻⁷` with `vel_dt_scalar = 1`. `Pace s r q α ε_f ε_q`
bundles the code facts (`pace_of` builds it from `FilterRun`, `rawScaler_unit`, the initial `1.0`
and `prog_step`).

**Interface to M7 and the certificates** (hypotheses, on S-curve-time intervals):

* windows: while `q ∈ [a_i, a_i + 2)` the arrival atom of leg `i` holds. For `w1 … w7` this is the
  S-curve geometry (target within `rPass w_i`); for `w0` it is the climb certificate (vehicle within
  `r = 0.1`, the new ψtrack of SubSpec.lean);
* phases: while `q ∈ [a_{i−1} − 1, a_i)`, the raw scaler of the next tick is at least `ρ_i`;
  `rawScaler_ge_course` derives this from P-1 with the S-curve speed `≥ v_min` on the phase and the
  along-track bounds;
* `hesc`: the leg-start escape (§2).

**The leg argument** (`leg_arrive`). From a tick in `[A, B)` with deficit `≤ D₀`: if no tick within
`T` reached `B`, all those ticks were in the phase, so (`deficit_sum`) the S-curve time advanced by at
least `ρT − (1/α − 1)(D₀ + c) − T(c + ε_q)`, which the leg condition makes `≥ B − A`. The first tick
with `q ≥ B` is below `B + 1 + c + ε_q`, inside a window of width 2. The leak `c + ε_q` per tick
(the filter may dip below 0 by `c`) is at most `0.157` tick over the horizon.

`leg0_arrive` starts at the escape tick `E` from deficit `1 + c`, and shows that at the arrival the
deficit has decayed for at least `K` ticks to `(1 − α)^K (1 + c) + (1 − ρ₀) + c`.
`chain_reach` keeps the deficit below that level `Δ` on the later legs (`deficit_inv`).

```lean
theorem pacing_course (P : Pace s r q α₀ (1 / 10 ^ 7) (1 / 10 ^ 7)) (x : ℕ → X) {τv : ℝ}
    (a : Fin 8 → ℝ) (hτv : 0 ≤ τv) (hesc : ∃ t ≤ 350, τv ≤ q t)
    (ha0 : 240 ≤ a 0 - τv ∧ a 0 - τv ≤ 510)
    (ha1 : 2 ≤ a 1 - a 0 ∧ a 1 - a 0 ≤ 860) (ha2 : 2 ≤ a 2 - a 1 ∧ a 2 - a 1 ≤ 743)
    (ha3 : 2 ≤ a 3 - a 2 ∧ a 3 - a 2 ≤ 743) (ha4 : 2 ≤ a 4 - a 3 ∧ a 4 - a 3 ≤ 1450)
    (ha5 : 2 ≤ a 5 - a 4 ∧ a 5 - a 4 ≤ 743) (ha6 : 2 ≤ a 6 - a 5 ∧ a 6 - a 5 ≤ 743)
    (ha7 : 2 ≤ a 7 - a 6 ∧ a 7 - a 6 ≤ 750)
    (hph0 : ∀ t < 12000, τv - 1 ≤ q t → q t < a 1 → ρLo ≤ r (t + 1))
    (hph : ∀ i : Fin 8, 2 ≤ (i : ℕ) → (i : ℕ) ≤ 6 → ∀ t < 12000,
      a (i - 1) - 1 ≤ q t → q t < a i → ρMid ≤ r (t + 1))
    (hph7 : ∀ t < 12000, a 6 - 1 ≤ q t → q t < a 7 → ρEnd ≤ r (t + 1))
    (hwin0 : ∀ t ≤ 12000, a 0 ≤ q t → q t < a 0 + 2 → sat x t (near (wp 0) rWp))
    (hwin : ∀ i : Fin 8, 1 ≤ (i : ℕ) → ∀ t ≤ 12000, a i ≤ q t → q t < a i + 2 →
      sat x t (nearT (wp i) (rPass (wp i)))) :
    sat x 0 (.eventually 0 1200 (.and (near (wp 0) rWp)
      (reachSeqF (fun w => nearT w (rPass w)) legs.tail))) ∧ ∃ t ≤ 10800, a 7 ≤ q t
```

The first conjunct is the reach conjunct of the new `ψtrack` (SubSpec.lean, 2026-11-05 evening):
the vehicle within `r` of `w0` within 1200 ticks, then the target within `rPass` of `w1 … w7` in
order within the allowances. `ρLo = 0.7712`, `ρMid = 0.8823`, `ρEnd = 0.8406` are P-1 with
`ε_v = 0.055`, `ε_e = 0.03` and `v_min = 0.36`, `0.6`, `0.48` (`rho_course`).

`hold_course` gives the hold conjunct `◇_[0,10800] □_[0,1200] nearT w7 (rPass w7)` from: the second
conjunct above; until completion, the target within `rPass w7 = 0.085` of `w7` whenever
`q ≥ a₇ − 1` (end of the last S-curve, M7); after completion, the target on the loiter leg
(`dist ≤ dist (stopPt pc sc) w7`, M7); the navigator's `loiter_dest_bound` at the completion tick
with sampled position within `0.03` m of `w7` and sampled speed at most `0.05` m/s
(`0.03 + 0.05 + 10⁻⁵ ≤ 0.085`).

**The numbers** (ticks). Leg 0: `0.7712 · 850 − 119.1 · (1 + 2c) − 850 (c + ε_q) = 536.4 ≥ 510`.
`Δ = (1 − α₀)²³⁰ (1 + c) + 0.2288 + c ≤ 0.146 · 1.000013 + 0.2288 ≤ 0.38`, so each later leg loses
at most `119.1 · 0.38 = 45.3` ticks to the initial deficit: leg 1 `0.7712 · 1200 − 45.3 = 880.2 ≥ 860`,
legs 2, 3, 5, 6 `1013.4 ≥ 743`, leg 4 `2072 ≥ 1450`, leg 7 `963.4 ≥ 750`.

## 4. Validation of the constants

Script `scratchpad/pacing/validate.py` (scratchpad
`/private/tmp/claude-501/-Users-ryan-Research-delegate/547e050f-c29a-418f-816a-16412bc752a6/scratchpad/pacing/`):
(a) S-curve geometry from ideal-tracking runs of `copter_lean36` (every sample at the previous
target with the previous velocity target), 101 starts on a 5×5×4 grid of the box plus the nominal
start; this geometry does not depend on the vehicle (§5); (b) closed-loop quantities from the nominal
flight and 14 PyBullet flights of `copter_lean36 --trace` (the 8 box corners at heading 0, the centre
column, headings 90°, 180°, −135°, 45°; `fly.py`), with the scaler, filter and `q` reconstructed from
the traced targets (`analyze.py`; the reconstruction reproduces the targets as `Γ(q)` within 5 mm,
`interface.py`).

| constant | value | measured | margin |
|---|---|---|---|
| `W₀` (escape tick) | 350 | ≤ 291 | 59 ticks |
| `τ_v` (speed ≥ 0.36 from here to `a₁`) | ≥ 0 | 218–226 | |
| `a₀ − τ_v` (vehicle within 0.1 of `w0`) | [240, 510] | 260–378 | |
| `a₁ − a₀` | ≤ 860 | ≤ 841 | 19 |
| `a_i − a_{i−1}`, i = 2…7 | ≤ 743, 743, 1450, 743, 743, 750 | ≤ 740, 740, 1448, 741, 741, 744 | |
| windows (ticks of `q`) | ≥ 2 | ≥ 30 (`w1…w6`), ≥ 441 (`w7`), ≥ 97 (vehicle at `w0`) | |
| speed on the phases | 0.36 / 0.6 / 0.48 | ≥ 0.3602 / 0.6172 / 0.4854 | |
| along-track position error | 0.03 | ≤ 0.0216 | ×1.39 |
| along-track velocity lag | 0.055 | ≤ 0.0425 | ×1.29 |
| raw scaler on the phases | ≥ 0.7712 / 0.8823 / 0.8406 | ≥ 0.988 / 0.985 / 1.000 | |
| target after `q ≥ a₇ − 1` | ≤ 0.085 | ≤ 0.0847 (ideal) | 0.3 mm |
| completion: sampled position to `w7` / speed | 0.03 / 0.05 | 0.0156 / 0.0330 | |

The closed-loop leg durations (vehicle at `w0`, then target at `w1 … w7`) are at most 679, 843, 741,
742, 1448, 741, 741, 745 ticks against 1200, …, 2400, …, 1200. The time warp costs 78–83 ticks on
leg 0 and at most 1.4 ticks per later leg.

## 5. Findings

1. **The target never enters `0.09` of `w0` on the climb for low starts (the first ψtrack was
   false).** The target cuts the `w0` corner (the climb blends into leg 1): its closest approach is
   `0.0431`–`0.0995` m over the 101 grid starts; 23 of them (all with down ≥ −0.1 m) never come
   within `0.09`, e.g. the nominal start `(0, 0, −0.0135)` at `0.0942` m (also on the recorded
   flight, tick 737). The path is the same for every behavior from a start: perturbed streams
   (`perturb.py`: 3 cm lag, 2 cm lead, ±5 cm noise) give `0.0940`–`0.0942`. So
   `◇_[0,1200] nearT w0 0.09` failed whatever the vehicle did. The coordinator's spec change (the
   reach chain starts with the vehicle at `w0`) is what `pacing_course` proves.
2. **With the new `rPassEnd = 0.085` the margin at `w7` is 0.3 mm** in the ideal runs (the target
   after the `w7` entry is at most `0.0847` m from `w7`; the entry is at `0.085` by definition, so this
   is the S-curve's monotone approach, not a margin to tune).
3. **The leg-start phase cannot be paced by tracking bounds** (§2, the freeze stream).

## 6. What M9 must supply

The per-tick code facts are proved (`code_filter_step`, `rawScaler_unit`, `prog_step`). M9 has to
assemble them along the closed-loop trace (`FilterRun` and the steps of `q` from `Vehicle.tick` →
`update_wpnav`, with `_is_terrain_alt = false`, `vel_dt_scalar = 1` from `_offset_vel_ms =
_wp_desired_speed_ne_ms`, the params WP_ACC 1.5, WP_JERK 5, `dt = 0.0025f`), and discharge:

* from M7: `target = Γ(q)`, the windows `a_i`, the leg durations, the speed profile on the phases,
  the end of the last S-curve and the loiter leg;
* from the tracking certificates: the along-track bounds on the phases (`rawScaler_ge_course`), the
  vehicle within `r` of `w0` on the window `[a₀, a₀ + 2)`, the completion-tick bounds;
* the escape `hesc` (closed loop, leg 0).

## 7. Files

| file | content |
|---|---|
| `Contracts/Track/PacingScaler.lean` | `rawScaler`, `advance_track_dt_scalar`, `rawScaler_unit`, P-1 |
| `Contracts/Track/PacingFilter.lean` | `alpha_eval`, `filter_step`, `code_filter_step`, the deficit lemmas, P-2 |
| `Contracts/Track/PacingArrive.lean` | `Pace`, `prog_step`, `leg_arrive`, `leg0_arrive`, `chain_reach`, P-3, the hold, the course |
| scratchpad `pacing/*.py` | `drive.py` (ideal and perturbed streams through `copter_lean36`), `fly.py`, `analyze.py`, `geom.py`, `interface.py`, `freeze.py`, `validate.py` |
