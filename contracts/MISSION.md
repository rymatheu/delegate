# The mission contract of the translated ArduCopter stack in closed loop

This is stage one of a formal proof that a mission-level STL contract holds for ArduPilot's
translated control stack in closed loop with the Crazyflie ODE plant.

This stage delivers:

* the translated controller and the plant in one Lean package (`v4.36.0-rc2`, Mathlib);
* the closed loop on one universe;
* the mission theorem, stated with the numbers of `sim/spec/mission-course.json`;
* its assembly from sub-contracts through the contract algebra, fully proved;
* everything else that can be proved now.

Two sub-contracts are open (`sorry`). Nothing else is.

## Build

```
cd cpp2lean/contracts
lake build                      # all targets; the only warnings are the two `sorry`s of Sub.lean
lake env lean AxiomCheck.lean   # axiom audit
```

## Files

| file | content |
|---|---|
| `Translated/*.lean` | the translated vehicle, a byte-identical snapshot of `cpp2lean/lean/` (`TRANSLATED.md`) |
| `MissionData/Course.lean` | the three course parameter files, verbatim; `courseLines` |
| `MissionData/Check.lean` | the executable `mission_world_check` |
| `Contracts/MissionPrelude.lean` | the Mathlib and plant imports of the mission files (a module) |
| `Contracts/Mission/Loop.lean` | `CtrlOut`, `tickT`, the universe `X`, `Mplant`, `Mctrl`, `Mloop`, the signals `pos`, `posTarget`, `err`, `alt`, `smpPos`, `smpErr` |
| `Contracts/Mission/Spec.lean` | the spec numbers, the geometry, the formulas, `ψmission`, `Atakeoff`, `MissionParams`, `MissionWorld`, `LibmSpec` |
| `Contracts/Mission/SubSpec.lean` | the decomposition constants and the formulas `ψnavA`, `ψnavG`, `ψtrack` |
| `Contracts/Mission/Sub.lean` | `nav_contract`, `track_contract` (open), `arrive_lemma` (proved) |
| `Contracts/Mission/NavFloat.lean` | float literals, `fabsf`, the approximation calculus `A32`/`A64` over `FloatModel` and `LibmSpec` |
| `Contracts/Mission/NavStop.lean` | navigator milestone (a): the stopping point and the loiter destination |
| `Contracts/Mission/NavLeg.lean` | navigator milestone (b), geometric part: a straight S-curve leg |
| `Contracts/Mission/NavBlend.lean` | navigator milestone (c), geometric part: the corner blend |
| `MissionData/Params.lean` | `missionParamsOk`: the parameter values of `MissionWorld`, as a bitwise check |
| `FloatModel/*.lean` | exact real values of `Float`/`Float32` and the rounding bounds of `+ - * / sqrt` (the delegate port's library, as modules) |
| `Contracts/Mission/Theorem.lean` | the bridge, the assembly `mission_of_sub`, `mission_contract`, `mission_nonvacuous` |
| `AxiomCheck.lean` | the axiom audit, now covering the mission as well |
| `MissionData/NavCex.lean` | executable `nav_cex`: evaluated counterexamples to `nav_contract` (not a default target) |

## The closed loop (`Loop.lean`)

**Controller.** `tickT w₀ : Option World → Sample → Option World × CtrlOut` processes one input line
of `VehicleMain.loop`. On the first sample (state `none`) it runs `takeover w₀ smp`, then
`Vehicle.tick`.

The hidden state is `loop`'s own `Option World`, so the takeover runs exactly once, as in the
executable. A test on `ticks32 = 0` would fire again after `2³²` ticks.

`CtrlOut` holds:

* the four actuators (`Vector Float32 4`);
* `posTarget`, which is `AC_PosControl::get_pos_desired_NED_m` read from the world after the tick;
* `velTarget`, which is `AC_PosControl::get_vel_desired_NED_ms` after the tick (the velocity the
  S-curve feeds, the second three `--trace` numbers).

`posTarget` is the value `--trace` prints first. `traceValues_posTarget` proves that it equals the
first three entries of `traceValues`. It is read from the world directly rather than from
`traceValues`, so that it keeps its type (`Vector3p`, doubles) and no array index enters the
statements.

The controller is lifted as `Mctrl w₀ = liftHidden (·.smp) (·.out) (tickT w₀) none`.

**Universe.** `X = { phys : PState, smp : Vehicle.Sample, out : CtrlOut }`.

**Plant.** `Mplant = liftStep (·.phys) (·.out.act) (·.smp) (plantV …)`. Here
`plantV s a = (Plant.next s a, toVSample (Plant.sample sense32 senseP s))`: the plant package's
step, with its sample converted field for field to the controller's `Vehicle.Sample`.
`mem_Mplant_iff_plant` proves that this is exactly the plant package's `Mplant`, read through that
conversion.

**Loop.** `Mloop = Mplant ∩ Mctrl w₀`.

**Signals:**

* `pos x`: the first three rigid-body coordinates, in `EuclideanSpace ℝ (Fin 3)`;
* `posTarget x`: the target's three doubles, read as reals with `Float.toReal`;
* `err x = dist (pos x) (posTarget x)`;
* `alt x = -down`;
* `smpPos`, `smpErr`: the same as `pos` and `err`, for the sampled position;
* `velTarget`, `smpVel`, `smpVelErr`: the velocity target, the sampled velocity, their distance.

## The statement (`Spec.lean`, `Theorem.lean`)

```lean
theorem mission_contract (sense32 : ℝ → Float32) (senseP : ℝ → Float) (w₀ : Vehicle.World)
    (hM : MissionWorld w₀) (hS : Plant.CopterSense sense32 senseP) (hL : LibmSpec) :
    Mloop sense32 senseP w₀ ⊨ ⟨Atakeoff, lang_t 0 ψmission⟩

def ψmission : Formula X :=
  .and (.always 0 horizonTicks safeF)
    (.and (reachSeq rWp legs) (.eventually 0 totalTicks (.always 0 holdTicks (near w7 rWp))))
```

**In words.** Take the vehicle built from the three course parameter files, sensing ports at
round-to-nearest accuracy, and the C library hypotheses. Then every behavior of the closed loop
that starts at rest in the takeoff box satisfies three things:

* **Safety.** Over the 12000-tick horizon (30 s) the vehicle stays in the safe set `S` and below
  the ceiling. `S` is the corridor of radius 0.25 m around the planned polyline, union the
  takeoff box.
* **Reach.** It reaches `w0 … w7` in order, each within `r = 0.1` m. Each waypoint is reached
  within its allowance, counted from the arrival at the previous one.
* **Hold.** Within the 10800-tick total allowance, it is within 0.1 m of `w7` for 1200 ticks
  (3 s).

**In symbols:**

```
□_[0,12000] (pos ∈ S ∧ alt ≤ 2)
∧ ◇_[0,T₀](‖pos − w0‖ ≤ r ∧ ◇_[0,T₁](‖pos − w1‖ ≤ r ∧ … ◇_[0,T₇](‖pos − w7‖ ≤ r) …))
∧ ◇_[0,10800] □_[0,1200] ‖pos − w7‖ ≤ r
```

with `(T₀, …, T₇) = (1200, 1200, 1200, 1200, 2400, 1200, 1200, 1200)`.

STL here has only bounded operators, so safety is stated over the mission horizon, not forever.
The ceiling conjunct is implied by the corridor: `down_of_inSafe` proves `S` is below 1.85 m.

**Hypotheses:**

* `MissionWorld w₀`, a structure of two hypotheses:
  * `built`: `∃ w, construct courseLines = .ok w ∧ w₀ = boot w`. `courseLines` comes from the
    embedded file texts;
  * `params : MissionParams w₀`: explicit equalities of the fields the proofs read: the eight
    waypoints (`missionWps`), the navigator's parameters (`wppC`: `WP_SPD 1`, `WP_SPD_UP 2.5`,
    `WP_SPD_DN 1.5`, `WP_RADIUS_M 0.1`, `WP_ACC 1.5`, `WP_ACC_CNR 0`, `WP_ACC_Z 1`, `WP_JERK 5`,
    `WP_TER_MARGIN 10`, `WP_RFND_USE 1`), `PSC_NE_POS_P 1.5`, `PSC_D_POS_P 1`, `PSC_NE_JERK 5`,
    `ATC_RATE_R_MAX 0`, `ATC_RATE_P_MAX 0`, `ATC_ACC_R_MAX 1800`, `ATC_ACC_P_MAX 1800`,
    `ATC_INPUT_TC 0.05`.

  **Trusted step.** `params` is not derived from `built` in Lean: the kernel cannot evaluate
  `construct courseLines` (`String.splitOn` is well-founded recursion, `Vehicle.parseDecimal` a
  `while` loop through the `partial` `repeatM`). `mission_world_check` evaluates
  `MissionData.missionParamsOk (boot w)` on the world built from the embedded texts (`true`, exit
  code 0), and `missionParams_of_ok` proves that this Boolean gives the equalities. The executable
  also checks the texts against the files and prints the parameters as `copter_lean --print-params`.
* `CopterSense`: the plant package's sensing ports at round-to-nearest accuracy.
* `LibmSpec`: finite results, ranges and accuracy for the libm externs, as they can be foreseen
  now. It covers:
  * `sinf`, `cosf`, `sqrtf`, `atan2f`, `asinf`, `acosf`;
  * `fmaxf`, `fminf`, `fmodf` (exact);
  * the double `sin`, `cos`, `sqrt`, `fmax`, `fmin`;
  * added for `nav_contract`: the conversions `(double) f` (exact, `f32ToF64`) and `(float) d`
    (correctly rounded: relative `2⁻²⁴` plus `2⁻¹⁵⁰`, `f64ToF32`; exact on `float` values,
    `f64ToF32_exact`). They are opaque in Lean 4.36 (`Float32.toFloat`, `Float.toFloat32`).

  The trigonometric accuracy is `2⁻²²` for `float` and `2⁻⁵¹` for `double`. `sqrt` is correctly
  rounded.

**Assumption `Atakeoff`:** `∃ p ∈ box, ∃ ψ, (x 0).phys = startP p ψ`. The start state is:

* position `p`;
* velocity 0;
* attitude `yawQuat ψ = (cos(ψ/2), 0, 0, sin(ψ/2))`: level (roll = pitch = 0), any heading `ψ`;
* body rates 0;
* held actuators `1/thrust2weight` on each motor, so the tick-0 specific force is `(0, 0, -g)`
  whatever the heading (`tickSpecForce_startP`).

(Spec change of 2026-11-05: the attitude was `(1,0,0,0)`, facing north. Any heading is now
admitted; `smpStart` and `navA_of_loop` follow, and `mission_nonvacuous` picks heading 0.)

## The spec numbers

All values come from `sim/spec/mission-course.json`, version of 2026-11-05 13:30, which includes
the coordinator's corrections. They are named constants in `Spec.lean`, each with its JSON path.

| constant | value | JSON |
|---|---|---|
| `tickHz` | 400 | `tick_hz` |
| `rWp` | 0.1 m | `r_m` |
| `ceiling` | 2.0 m | `ceiling_m` |
| `corridor` | 0.25 m | `corridor_radius_m` |
| `boxNE`, `boxDownLo`, `boxDownHi` | north and east `[-0.15, 0.15]`, down `[-0.3, 0]` m | `box_ned_m` |
| `wp` | `w0 … w7` | `waypoints_ned_m` (= the `waypoint` lines of `params/copter-cf2x.txt`) |
| `pathPt` | origin, `w0 … w7` | `path_ned_m` |
| `allowanceSec`, `allowanceTicks` | 3,3,3,3,6,3,3,3 s = 1200,…,2400,…,1200 ticks | `allowances_s`, `allowances_ticks` |
| `totalTicks`, `holdTicks`, `horizonTicks` | 10800, 1200, 12000 | `total_ticks`, `hold_ticks`, `horizon_ticks` |
| `nominalLegSec` | 1.685, 1.933, 1.845, 1.854, 3.621, 1.852, 1.85, 1.85 s | `nominal.leg_s` |
| `wpRadius` | 0.1 m | `WP_RADIUS_M` of `params/copter-cf2x-tuned.txt` |

Facts proved by evaluation:

* `allowance_rule`: `⌈1.25 · leg + 0.5⌉ = allowance_s` for all eight legs;
* `span_legs`, `allowanceTicks_sum`: the allowances sum to 10800;
* `allowanceTicks_eq`: ticks = seconds · 400;
* `holdTicks_eq`, `horizonTicks_eq`: hold = 3 · 400, horizon = total + hold;
* `rWp_le_wpRadius`;
* `legs_allowances`, `legs_waypoints`.

The safe set `S` (`inSafe`) is `polyDist p ≤ 0.25 ∨ inBox p`, where
`polyDist p = Metric.infDist p (⋃ segments)`. As an STL atom it is `safeMargin`, which is
nonnegative exactly on `S` (`safeMargin_nonneg_iff`).

## The decomposition (`Sub.lean`)

### Constants

| constant | value | evidence (nominal run `sim/out/lean-course-1ms`) |
|---|---|---|
| `ρ` | 0.155 m: target-to-polyline bound | max 0.071 m |
| `δ` | 0.095 m: tracking bound | max 0.0870 m |
| `δ₀` | 0.035 m: tracking bound during the climb out of the box | max 0.012 m up to 0.37 m of climb |
| `rPass w` | 0.09 m at `w0 = w7` (`rPassEnd`), 0.105 m at `w1 … w6` (`rPassMid`): target radius in the transfer property | the corner cut is 0.1000–0.1006 m; with 0.105 at `w0` the transfer fails on 82 of 256 Monte Carlo runs (`sim/out/montecarlo/CONSTANTS.md`) |
| `δs` | 0.096 m: sampled tracking bound the navigator may assume | `δ` plus the sensing error |
| column | `|n|, |e| ≤ 0.151`, down `∈ [-0.8, 0.002]` | the box enlarged by 0.001 (0.002 below, for the `float` rounding of the start) |
| `rRest` | 0.001 m and m/s: the rest gate (target within it of `w7`, velocity target at most it) | holds at the completion tick; never before it on this course |
| `δv` | 0.055 m/s: sampled velocity error while the target rests at `w7` | nominal max 0.0407 m/s over the 141 rest ticks (`1.35×`) |

Proved numeric facts:

* `hρδ : ρ + δ ≤ corridor` (equality);
* `hδ : δ < r`;
* `hδs : δ < δs`;
* `hrPass : r < rPassMid`, `hrPassEnd : rPassEnd < r`, `rPass_w7`, `rPass_w0`, `rPass_mid`;
* `polyDist_of_inColumn`: the column is within `0.2136` m of the polyline (`√(2·0.151² + 0.002²)`).

### `nav_contract` (open): the controller alone

```lean
theorem nav_contract (w₀ : Vehicle.World) (hM : MissionWorld w₀) (hL : LibmSpec) :
    Mctrl w₀ ⊨ ⟨lang_t 0 ψnavA, lang_t 0 ψnavG⟩
```

**Assumption `ψnavA`.** It is stated on the samples and the target only:

* the first sample is of a vehicle at rest in the box, enlarged by 0.001 m (`smpStart`; its down
  coordinate is at most `0.001`, `0.001` inside the column's face):
  * velocity and body rates `+0`;
  * attitude level with any heading: `q2 = q3 = +0`, `|q1² + q4² - 1| ≤ 0.001`;
  * specific force `(0, 0, -g ± 0.001)`;
* over the horizon:
  * the period is always 2500 µs;
  * every sample is finite and inside the envelope `smpEnv`: position 11 m, velocity 3 m/s,
    specific force 23 m/s², quaternion components 2, rates 11 rad/s;
  * the sampled position is within `δs` of the target;
  * the rest condition `restF`: while the target is within `rRest` of `w7` and its velocity target
    at most `rRest`, the sampled velocity is within `δv` of the velocity target.

**Guarantee `ψnavG`.** Over the horizon the target is within `ρ` of the polyline or in the takeoff
column.

### `track_contract` (open): the loop

```lean
theorem track_contract (sense32 senseP w₀) (hM) (hS : Plant.CopterSense sense32 senseP) (hL) :
    Mloop sense32 senseP w₀ ⊨ ⟨Atakeoff, lang_t 0 ψtrack⟩
```

`ψtrack` has two parts.

Over the horizon:

* (T1) `err ≤ δ`;
* (T2) the envelope `physEnv`: `|p| ≤ 10` m, `|v| ≤ 2` m/s, `|ω| ≤ 10` rad/s per component;
* (T3) `takeoffF`: when the target is in the column but not within `ρ` of the polyline,
  `err ≤ δ₀`;
* (T4) `proxAllF`: for each waypoint `w`, `‖target − w‖ ≤ rPass w → ‖pos − w‖ ≤ r`;
* (T6) `restF`, the rest condition of `ψnavA` (on the loop's samples, so `chain` discharges it).

And the target's pacing:

* (T5) `reachSeqF (fun w => nearT w (rPass w)) legs`;
* `◇_[0,10800] □_[0,1200] ‖target − w7‖ ≤ rPass w7 = 0.09`.

### `arrive_lemma` (proved)

Suppose that at every tick up to `N`, `F w` implies `G w` for every point `w` of the list. Then
`reachSeqF F L` at `t` implies `reachSeqF G L` at `t`, provided `t + span L ≤ N`. No time shift is
needed, because the transfer holds tick by tick.

There are two instances:

* `arrive_of_err` (proved): the caller's form. If `err ≤ δ'` and `rT + δ' ≤ r`, reaching
  transfers from the target to the vehicle.
* The mission's own form, through T4.

## `nav_contract`: two counterexamples to the first statement, and the corrections

The first statement of `nav_contract` was false. The corrections (2026-11-05) are
`colDownHi = 0.002` with the first sample still at most `0.001` below ground, and the rest condition
`restF` in `ψnavA` (and in `ψtrack`). The counterexamples, as evaluated on the first statement:

`nav_cex` runs `tickT w₀` (copied verbatim, without Mathlib) from the mission world on a feedback
sample stream: the first sample at rest at a chosen start, every later sample at the previous tick's
target with the previous tick's desired velocity, attitude `(1,0,0,0)`, specific force
`(0, 0, -9.80665f)`, period 2500 µs. It checks `ψnavA` and `ψnavG` at every tick up to 12000
(`inColumn` exactly on the doubles' rational values). Both streams below meet `ψnavA` at every tick
(max `smpErr` 0.0025 m).

1. **Float rounding at the column's bottom face** (`nav_cex 0.151 0.151 0.0009999999999999998 none 0 0 0`).
   The first sample's down coordinate is the largest double `≤ 0.001` (allowed by `smpStart`). The
   stopping point of `wp_and_spline_init_m` goes through `float`
   (`AC_PosControl::get_stopping_point_D_m`: `curr_pos_d_m = (float) _pos_estimate_ned_m.z`), and
   `(float) 0.001 = 0.0010000000474974513`. The target is then at down `0.001 + 4.57·10⁻¹¹`
   (tick 0) and `0.001 + 2.64·10⁻¹¹` (tick 1), north and east `0.151`: outside the column, and
   `0.2135` m from the polyline. The S-curve start is snap-limited, so the first steps move it by less
   than the rounding. Fix: keep the first sample `float`-rounding away from the column's faces
   (e.g. `smpStart` with down `≤ boxDownHi + 0.0005`, which `navA_of_loop` still proves), or raise
   `colDownHi` to `0.002` (`polyDist_of_inColumn` still gives `≤ 0.2136`).
2. **The loiter at mission completion follows the sampled velocity** (`nav_cex 0 0 0 complete 1 -1 0`).
   At tick 6771 the mission completes and `loiter_start` sets the destination to
   `get_wp_stopping_point_NED_m`, computed from the sampled position and velocity:
   NE offset `min(|v_NE|, WP_SPD)/PSC_NE_POS_P = min(|v_NE|, 1)/1.5` along `v_NE`, D offset
   `clamp(stopping_distance(v_D, 1, 1), -3, 2)`. The velocity sample `(1, -1, 0)` at that tick puts the
   destination at `(0.4714, -0.4714, -0.8)`; the target leaves the column at tick 7088 and settles
   `0.667` m from the polyline (4913 violating ticks up to 12000). `ψnavA` bounds the velocity only by
   the envelope (3 m/s), so nothing in the controller-alone assumption prevents this. The target's
   geometry after completion depends on the vehicle's velocity at completion, a closed-loop quantity
   (nominal: the loiter target sits 0.028 m from `w7`).

Before completion the geometry holds on every stream tried: the nominal-like stream and eight
`fuzz` streams (persistent position offsets up to 0.09 m, velocities uniform in `[-3, 3]³`) give no
violation, with the target at most 0.072 m from the polyline outside the column.

**Against the corrected statement** (`nav_cex` checks the new column and `restF`):

* stream 1 (`0.151 0.151 0.0009999999999999998`): no violation, `ψnavA` holds;
* stream 2 (spike `(1, -1, 0)` at completion): `ψnavA` now fails at tick 6771 (rest gate open:
  target `0` from `w7`, velocity target `0`; sampled velocity error `1.414 > δv`), so the stream is
  no longer admissible;
* the largest admissible spikes at the completion tick, with the sampled position also offset by
  up to `0.0958` m: `(0.0388, -0.0388, 0)` with offset `(0.0678, -0.0678, 0)` puts the loiter
  target at `(0.0937, -0.0937, -0.8)` (0.1325 m from `w7`); `(0, 0, ±0.0548)` with offset
  `(0, 0, ±0.0958)` at down `-0.6494` / `-0.9506` (0.1506 m from `w7`, on the vertical leg resp.
  within `ρ` of `w7`): no violation in any of them;
* eight `fuzznear` streams (velocities within 0.3 m/s of the velocity target per axis, within
  0.03 m/s while the target rests at `w7`; offsets up to 0.09 m) complete the mission at ticks
  7276–7324: no violation, `ψnavA` holds, the target at most 0.0720 m from the polyline outside the
  column;
* the eight `fuzz` streams: no violation.

**The velocity bound `δv`.** A uniform conjunct `|v_smp − v_target| ≤ δv` over the horizon does not
work: the loiter destination is within `δs + |v|` of `w7` (`loiter_dest_bound`), so `ρ = 0.155`
needs `δv ≤ 0.058`, while the nominal maximum over the flight is `0.136` m/s (at the `w0` corner),
and `ρ` cannot grow (`ρ + δ = 0.25`). The gate restricts the conjunct to the ticks where the target
rests at `w7` (within `rRest = 0.001` m, velocity target at most `0.001` m/s): the completion tick is
one of them, and on this course the target never rests at `w7` before it. The nominal maximum over
those ticks is `0.0407` m/s; `δv = 0.055` (`1.35×`, not `1.5×`: `1.5×` gives `0.061`, and
`δs + rRest + rRest + 0.061 = 0.159 > ρ`). With `δv = 0.055` the bound is
`0.096 + 0.001 + 0.056 + 10⁻⁵ = 0.15301 ≤ 0.155` (`loiter_dest_near_w7`). The Monte Carlo CSVs
carry no velocity or setpoint (only `t, x_n, y_e, z_d, yaw, m1..m4`), so `δv` rests on the nominal
run only. The hold radius `rPass w7 = 0.09` is a closed-loop guarantee of `track_contract` (nominal
loiter offset 0.028 m); the navigator alone can only give `0.153` from its assumption.

**The S-curve tables** (`nav_cex 0 0 0 scurve 0 0 0`): for legs 1–7, for the first leg from 183
starts across the box, and for 1200 loiter legs up to 0.16 m, sampled at 40000 times each, the
S-curve position stays in `[0, L]` (overshoot below `10⁻⁶` m) and never steps back by more than
`10⁻⁶` m.

The kernel cannot evaluate `construct courseLines` (see `MissionWorld`); `MissionParams` carries the
parameter values instead. Float arithmetic itself reduces in the kernel (`Float.add` etc. are
defined through `Float.Model`); `sinf`, `cosf`, `powf` and the `float`/`double` conversions do not.

### Progress on the proof of `nav_contract`

* **(a) The loiter target bound: proved** (`NavStop.lean`).
  * `stop_NE_bound`: `AC_PosControl::get_stopping_point_NE_m` with `PSC_NE_POS_P = 1.5`,
    `WP_ACC = 1.5`, `WP_SPD = 1`, zero offsets: the estimate plus `T v` with `0 ≤ T ≤ ⅔(1 + 2⁻¹⁹)`,
    up to `2⁻²⁰(|p| + |v|) + 2⁻¹⁰⁰` per axis (`invSqrt_15`: `inv_sqrt_controller o 1.5 1.5`).
  * `stop_D_bound`: `get_stopping_point_D_m` with `PSC_D_POS_P = 1`, `WP_ACC_Z = 1`, `|v_D| ≤ 0.9`:
    the estimate plus `v_D`, up to `2⁻²⁰(|p| + |v|) + 2⁻¹⁰⁰` (two `float` roundings of the position).
  * `loiter_dest_bound`: the stopping point is within `d + ‖v‖ + 10⁻⁵` of any point within `d` of
    the estimate; `loiter_dest_near_w7`: with the rest condition, within `ρ` of `w7`.
* **(b) A straight leg: the geometric part is proved** (`NavLeg.lean`).
  * `len_approx`: the `float` length of `seg_delta` within `2⁻²¹` relative;
  * `proj_straight_near`: `SCurve::project_scurve_onto_track` of a straight segment puts the target
    within `e + P/2¹⁷ + 2⁻⁴⁰` of the segment when `0 ≤ P ≤ ‖seg_delta‖ + e`;
  * `scurve_pos_nonneg`: the position of `get_jerk_accel_vel_pos_at_time` is `≥ 0` when finite
    (the `MAX(0, ·)` clamp);
  * `move_from_near`: hence `SCurve::move_from_pos_vel_accel` of a straight leg, given the upper
    bound `P ≤ ‖seg_delta‖ + e`.

  **Blocked**: the upper bound `P ≤ ‖seg_delta‖ + e` (and monotonicity of `P` in time) is a property
  of the segment table that `SCurve::calculate_track` builds (`calculate_path`, `add_segments`,
  `add_segment_incr_jerk`/`decr_jerk`). It needs (i) the accelerating phase to cover at most half
  the leg (`calculate_path`'s closed forms, with `powf` roots on short legs), (ii) nonnegative
  velocity in every segment, both over the reals with the table's `float` rounding, and (iii)
  accuracy bounds for `powf`, `sinf`, `cosf` at the arguments used. `powf` is not in `LibmSpec`
  (it would need e.g. `|powf a b − a^b| ≤ 2⁻²² |a^b|` for `a > 0`). Evaluated, the property holds
  on every leg of this course (above).
* **(c) The corner blend: the geometric part is proved** (`NavBlend.lean`). `blend_near`: with
  `u`, `v` the unit directions of the legs into and out of the corner `c`, the target `c − a u + b v`
  is within `‖b_m v − a_m u‖` of the two legs when `a ≥ a_m, b ≤ b_m` (before the switch) or
  `a ≤ a_m, b ≥ b_m` (after it). `SCurve::advance_target_along_track` starts the blend only if
  `‖turn_pos‖ = ‖b_m v − a_m u‖ < WP_RADIUS_M`, and switches at the midpoint, so the blend stays
  within `WP_RADIUS_M = 0.1` (plus rounding) of the polyline. **Blocked** on the same table
  properties (monotonicity of `a` and `b` in time), and on relating `turn_pos` (computed with
  `move_from_time_pos_vel_accel` in `float`/`double`) to `b_m v − a_m u`.
* **(d) The invariant: not started.** It needs, beyond (b) and (c): a characterization of one
  `Vehicle.tick` on the fields the target depends on (the mission logic `mission_update`,
  `verify_nav_wp`, `do_nav_wp`, `set_wp_destination_NED_m`, `set_wp_destination_next_NED_m`,
  `loiter_start`; `update_wpnav` with the speed-change path, the offset shaping and
  `track_dt_scalar`; the event replay into `AC_PosControl`; `NE_update_controller` and
  `D_update_controller`, whose offsets, EKF-reset handling and leash `AC_P_2D::update_all` /
  `AC_P_1D::update_all` must be shown to leave `_pos_desired` as the navigator set it while the
  sampled error is at most `δs`), and the first tick (`takeover`, `auto_init`,
  `wp_and_spline_init_m`'s stopping point, rounded to `float` in down).

## Why the sub-contracts differ from the first design

Two facts in the nominal flight data rule out the first design ("the target reaches each
waypoint, the error is below δ < r, so the vehicle reaches it").

1. **The target never comes within `r` of `w0 … w6`.** ArduPilot's S-curves blend the corners and
   cut each one by the waypoint radius: the target's closest approach is 0.1000–0.1006 m. After
   mission completion the loiter target sits 0.028 m from `w7`.

   The vehicle reaches every waypoint within 0.1 m (closest 0.070–0.073 m) because it lags the
   target into the corner. No isotropic error bound can carry that: `rT + δ ≤ 0.1` would need the
   target within 0.005 m. So the transfer near the waypoints is a closed-loop statement, (T4).

   In the run, while the target was within 0.105 m of a waypoint, the vehicle was within 0.1 m at
   every such tick. The target's windows lie inside the vehicle's with 12 to 37 ticks to spare at
   each end. For example, at `w1` the target is within 0.105 m during ticks 1467–1498 and the
   vehicle within 0.1 m during 1447–1519.

2. **The target's progress depends on the vehicle.** `AC_WPNav::advance_wp_target_along_track`
   advances S-curve time at the rate
   `track_scaler_dt = clamp(0.05 + (v·d − kP e·d)/|v_T|, 0, 1)`.

   In the nominal run this rate is 0 at every leg start, and below 0.8 on 418 ticks. A sample
   stream with a small constant lag and zero velocity freezes the target while satisfying any
   tick-wise tracking tolerance. So the timing of the target cannot be a contract of the
   controller alone under tick-wise sample assumptions. It is in `track_contract` (T5).

   `nav_contract` keeps what is true of the controller alone: the target's geometry.

Safety from a start in a corner of the box is handled by (T3) and `polyDist_of_inColumn`. A corner
start puts the target 0.212 m from the climb axis. Points within 0.035 m of the column are within
0.2486 m of the polyline.

## Proof structure

```
mission_contract
 └─ mission_of_sub                        [proved; hypotheses: htrack, hnav, hS]
     ├─ chain (Basic.lean)                [proved]
     │   ├─ htrack = track_contract       [OPEN]
     │   └─ hnav, read on Mloop ⊆ Mctrl:
     │       ├─ nav_contract              [OPEN]
     │       └─ navA_of_loop              [proved]   samples meet ψnavA:
     │           ├─ mem_Mplant, mem_Mplant_iff_plant, Plant.Mplant_qnormSq
     │           ├─ port32, portP, f32Bd_of, f64Bd_of      (CopterSense)
     │           ├─ specForce_bound, accel_bounds, amax_le
     │           └─ tickSpecForce_startP
     └─ refines_sound ∘ refines_of_inter_subset            [proved]
         └─ mission_of_guarantees         [proved]   Gtrack ∩ Gnav ⊆ ψmission:
             ├─ safety:  safe_of_parts ── polyDist_le (1-Lipschitz), polyDist_of_inColumn,
             │                            hρδ, down_of_inSafe ── down_of_polyDist
             ├─ reach:   arrive_lemma + prox_of_sat (T4) + span_legs
             └─ hold:    prox_of_sat (T4) + horizonTicks_eq
mission_nonvacuous                        [proved]   witness = runState of jointStep
```

## What is proved and what is open

**Open (`sorry`):**

* `nav_contract`. It needs a proof about the translated `AC_WPNav` and `AC_PosControl`; milestone
  (a) is proved, (b) and (c) are proved in their geometric part, (d) is open (see "Progress on the
  proof of `nav_contract`").
* `track_contract`. It needs the closed-loop analysis: tracking, envelope, climb-out, the corner
  property and pacing.

The constants of both are chosen with margin over the nominal run. They have not yet been checked
against the Monte Carlo runs.

**Proved, with no `sorry` (`lake env lean AxiomCheck.lean`):**

```
'Contracts.Mission.mission_contract' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Contracts.Mission.nav_contract' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Contracts.Mission.track_contract' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Contracts.Mission.mission_of_sub' depends on axioms: [propext, Classical.choice, Quot.sound]
'Contracts.Mission.mission_nonvacuous' depends on axioms: [propext, Classical.choice, Quot.sound]
'Contracts.Mission.mission_of_guarantees' depends on axioms: [propext, Classical.choice, Quot.sound]
'Contracts.Mission.navA_of_loop' depends on axioms: [propext, Classical.choice, Quot.sound]
'Contracts.Mission.arrive_lemma' depends on axioms: [propext, Classical.choice, Quot.sound]
'Contracts.Mission.arrive_of_err' depends on axioms: [propext, Classical.choice, Quot.sound]
'Contracts.Mission.safe_of_parts' depends on axioms: [propext, Classical.choice, Quot.sound]
'Contracts.Mission.polyDist_of_inColumn' depends on axioms: [propext, Classical.choice, Quot.sound]
'Contracts.Mission.down_of_inSafe' depends on axioms: [propext, Classical.choice, Quot.sound]
'Contracts.Mission.sat_imp_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'Contracts.Mission.allowance_rule' depends on axioms: [propext, Classical.choice, Quot.sound]
'Contracts.Mission.span_legs' depends on axioms: [propext, Classical.choice, Quot.sound]
'Contracts.Mission.horizonTicks_eq' does not depend on any axioms
'Contracts.Mission.hρδ' depends on axioms: [propext, Classical.choice, Quot.sound]
'Contracts.Mission.hδ' depends on axioms: [propext, Classical.choice, Quot.sound]
'Contracts.Mission.mem_Mplant_iff_plant' depends on axioms: [propext, Classical.choice, Quot.sound]
'Contracts.Mission.traceValues_posTarget' depends on axioms: [propext, Classical.choice, Quot.sound]
'Contracts.Mission.actVec_toArray' depends on axioms: [propext, Quot.sound]
'Contracts.Mission.tickSpecForce_startP' depends on axioms: [propext, Classical.choice, Quot.sound]
'Contracts.Mission.yawQuat_normSq' depends on axioms: [propext, Classical.choice, Quot.sound]
'Contracts.Mission.missionParams_of_ok' depends on axioms: [propext, Classical.choice, Quot.sound]
'Contracts.Mission.rPass_mid' depends on axioms: [propext, Classical.choice, Quot.sound]
'Contracts.Mission.rPass_w7' depends on axioms: [propext, Classical.choice, Quot.sound]
'Contracts.Mission.invSqrt_15' depends on axioms: [propext, Classical.choice, Quot.sound]
'Contracts.Mission.stop_NE_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'Contracts.Mission.stop_D_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'Contracts.Mission.loiter_dest_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'Contracts.Mission.loiter_dest_near_w7' depends on axioms: [propext, Classical.choice, Quot.sound]
'Contracts.Mission.len_approx' depends on axioms: [propext, Classical.choice, Quot.sound]
'Contracts.Mission.axis_proj' depends on axioms: [propext, Classical.choice, Quot.sound]
'Contracts.Mission.proj_straight_near' depends on axioms: [propext, Classical.choice, Quot.sound]
'Contracts.Mission.scurve_pos_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
'Contracts.Mission.move_from_near' depends on axioms: [propext, Classical.choice, Quot.sound]
'Contracts.Mission.blend_near_first' depends on axioms: [propext, Classical.choice, Quot.sound]
'Contracts.Mission.blend_near_second' depends on axioms: [propext, Classical.choice, Quot.sound]
'Contracts.Mission.blend_near' depends on axioms: [propext, Classical.choice, Quot.sound]
```

`sat_imp_iff` is the semantics of `Formula.imp`, restating the STL library's `sat_imp`.

**Not proved in Lean, but checked by evaluation:**

* `construct courseLines` is `.ok`, and it builds the same parameters as the binaries
  (`mission_world_check`).
* `MissionWorld`, `CopterSense` and `LibmSpec` are hypotheses. Their satisfiability is not proved:
  * `MissionWorld` needs the translated `construct` to reduce in the kernel, which `String.splitOn`
    and the `while` loop of `parseDecimal` prevent; its `params` field is the executed check of
    `mission_world_check` (a trusted step);
  * `CopterSense` needs a round-to-nearest map ℝ → float, which is not constructed;
  * `LibmSpec` concerns the opaque libm externs.

## Replay (step 1, `TRANSLATED.md`)

The snapshot compiles on `v4.36.0-rc2` with **no edits**. Every `Translated/*.lean` file is
byte-identical to its source in `lean/`.

`copter_lean36` (v4.36) and `lean/.lake/build/bin/copter_lean` (v4.33) were run on
`sim/out/lean-course-1ms/inputs.txt` with `--exact --trace --bits` and the three course parameter
files:

* 7797 lines each;
* **0 differing lines**: the outputs are byte-identical (SHA-1
  `f8c77ace613c41c8604be3d8e3ef9efc51731d6a`).

`--print-params` is identical as well.
