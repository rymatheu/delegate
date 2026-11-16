# Waypoint reach from hover: status, proved pieces, and the open fact

This note documents `Contracts/Track/AttitudeCert.lean` and `Contracts/Track/Reach/*.lean`
(library `Track`). Everything listed as proved is sorry-free and depends only on `propext`,
`Classical.choice` and `Quot.sound` (`AxiomCheck.lean`, last block).

## 0. Status in one paragraph

The target theorem (`Mloop sense32 senseP w₀ ⊨ ⟨Ahover p₀ ψ₀, ◇□ near w' r⟩`, no named hypothesis
beyond `ReachWorld`, `CopterSense`, `LibmSpec`) is **not proved**. It cannot be proved without
one more fact about the loop: **the tick glue**, the statement that one `Vehicle.tick` of the
loop's world, together with the plant step, is the certified linear model plus a bounded
disturbance, at every tick, for unbounded time. That fact is the open part of `track_contract`
(INDUCTION.md §3: `ne_glue`, `vglue`, `attitude_tracks`, `att_step`, `ctrl_step`, `nav_step`,
`init`; all `sorry` in `Induction/Instance.lean`). On top of it the reach theorem needs facts
that `track_contract` does not need (§6). The control argument above the glue is proved:
milestones (1)–(4) at the model level, and two loop theorems conditional on the glue, stated as
the Lean propositions `HoverGlue` and `ReachFacts`.

**Update (§8 "Glue").** `HoverGlue` as stated is false (`not_hoverGlue`, GlueFalse.lean), so
`hover_practically_exponentially_stable` is vacuous; and no `Vc`-ball instance of it fits the code's
`acosf` tilt quantization (`ball_route_floor`). §8 replaces it by the tube-form glue `HoverGlueT` /
`HoverGlueG` (still open) and proves the hover theorems from it with usable constants
(`hover_practically_exponentially_stable_tube`, `_gen`, `hover_hold`: region 2.1 cm, `λ = 0.9997`,
`c = 3.47`, `b = 3.9` mm), together with the tick split and part of the readout glue.

## 1. The statement (`Reach/Loop.lean`)

| name | content |
|---|---|
| `ReachParams w w'`, `ReachWorld w₀ w'` | MissionParams' fields with the mission array `#[w']`; booted from some parameter lines |
| `Ahover p₀ ψ₀` | `(x 0).phys = startP p₀ ψ₀`: at `p₀`, at rest, level, heading `ψ₀` (any), hover actuators held |
| `ReachGoal r w'` | `{x | ∃ T, ∀ t ≥ T, dist (pos (x t)) w' ≤ r}` (unbounded `◇□`) |
| `waypoint_reach_nonvacuous` | **proved**: `(Mloop sense32 senseP w₀ ∩ Ahover p₀ ψ₀).Nonempty` for every world, ports, `p₀`, `ψ₀` |
| `waypoint_reach_of_facts` | **proved, conditional on `ReachFacts`**: `Mloop ⊨ ⟨Ahover p₀ ψ₀, ReachGoal (max b_E (d_Z + b_S)) w'⟩` |
| `hover_practically_exponentially_stable` | proved, conditional on `HoverGlue`, which is **false** (§8: `not_hoverGlue`); superseded by `Glue.hover_practically_exponentially_stable_tube`/`_gen` |

## 2. Milestones (1) and (2): the certificates

### (1) The attitude certificate (`AttitudeCert.lean`)

The model is `AttitudeJoint.lean`'s joint per-axis model (14 states: the NE position PID, the
attitude shaping in its linear zone with the `sqrt_controller_accel` switch `σ ∈ {0, 1}`, angle P,
rate PID, mixer, attitude and position rows of the rigid body; tilt scaled by `g`). Kernel checks
(`decide +kernel`, rational arithmetic, about 25 s for the file; a false identity is rejected):

* `certA0`, `certA1`: `λ² Pj − Ajσᵀ Pj Ajσ = Lcσ diag(Dcσ) Lcσᵀ`, `Dcσ ≥ 0`, `λ = 0.9997`: a
  common quadratic Lyapunov function of both modes, so every switching sequence is stable;
* `certP`, `Dp_pos`: `Pj = Lp diag(Dp) Lpᵀ`, `Dp > 0`;
* 17 output certificates `cert_*` (`Lp y = c`, `Σ yᵢ²/Dpᵢ ≤ γ_c`), and `out_sq_le`:
  `(c·x)² ≤ γ_c V x` (weighted Cauchy–Schwarz over the `LDLᵀ` form). Among them the tilt error from
  the commanded tilt, `sq_a_le` (`γ_a = 1.39·10⁻¹²`), and the position error `sq_e_le`
  (`γ_e = 1.438459·10⁻¹²`);
* `V_A`, `V_iss_sw`, `V_traj_sw`: contraction, ISS step, and the discrete ISS bound of the switched
  system; `jtick_eq_sw`.

Yaw is the proved phase lemma (`AttitudeYawPhase.lean`): from any heading error `e₀ ∈ (0, π]`,
`|e_t| < π` for `t ≥ 2`, `e_t ≤ max e₀ 0.00884`, monotone decrease in the sqrt zone
(`yaw_no_wrap`, `yaw_bounds`, `yaw_sqrt_zone_monotone`, `yaw_slew_decrease`). In the composite it
enters through the join disturbance (the rotation of the horizontal axes by the heading rate).

### (2) The composite (`Reach/Composite.lean`)

`Vc ξ = V_j(ξ_N) + V_j(ξ_E) + μ_v V_v(ξ_D)`, `μ_v = 38.57` (`≥ γ_v/γ_e`, so one `γ_e` bounds the 3D
position error). The joins (tilt into the vertical channel, heading rotation, plant remainder,
`float` rounding) are the disturbance `w`, bounded on `D = {Vc ≤ ν}` by `κ Vc + c₀`.

* `Vc_step`: `Vc (A ξ + w) ≤ λ Vc ξ + Vc w/(1 − λ)`, `λ = 0.9997` (the vertical `0.998` is dominated);
* `Vc_step_join`: `Vc' ≤ ρ Vc + c₀/(1 − λ)`, `ρ = λ + κ/(1 − λ)`;
* `Vc_traj`: if `ρ < 1` and `ρ ν + c₀/(1 − λ) ≤ ν`, `D` is forward invariant and
  `Vc (ξ t) ≤ ρᵗ Vc (ξ 0) + c₀/((1 − λ)(1 − ρ))`;
* **`hover_pes_model`** (target fixed at `w`, start a pure position offset `p₀ − w`, any heading):
  `‖p_t − w‖ ≤ c (√ρ)ᵗ ‖p₀ − w‖ + b`, `c = √(10¹⁵ γ_e) ≤ 37.93` (`c_hover_le`),
  `b = √(γ_e c₀/((1 − λ)(1 − ρ)))`;
* **`track_iss_model`** (moving reference, `κ = 0`, every disturbance coordinate `≤ ε̄`):
  `‖p_t − p^T_t‖ ≤ √γ_e (√λ)ᵗ √(Vc ξ₀) + γ ε̄`, `γ = √(γ_e PsumC)/(1 − λ) ≈ 3.9·10⁵`
  (`PsumC = 2 Σ|Pj| + μ_v Σ|Pv| = 9.40·10¹⁵`).

**The form chosen for hover**: the target fixed at `w` and the error state starting as the pure
position offset (vehicle at rest and level, controller states zero); this is what `Vc_traj` makes
immediate.

**Numbers.**

| constant | value |
|---|---|
| `λ` (V per tick) | `0.9997`; position rate `√λ = 0.99985` per tick (time constant 6667 ticks, 16.7 s: conservative) |
| `c` | `≤ 37.93` |
| `D` | `Vc ≤ ν`, `ν = 1.99·10⁹` (the previous agent's linear-zone limits, `attM4/roa.py`, float evaluation) |
| `D`, radii per axis | `|e| ≤ √(γ_e ν) = 0.0535` m, tilt error `≤ √(γ_a ν) = 0.053` m/s², `|e_D| ≤ 0.053` m |
| `D`, pure position offset | `‖p₀ − w‖ ≤ √(ν/10¹⁵) = 1.41` mm |
| admissible floor (`κ = 0`) | `c₀ ≤ ν(1 − λ)² = 179`, i.e. per-tick disturbance `ε ≤ 1.38·10⁻⁷` per coordinate |
| `b` at that floor | `0.054` m; in general `b = 3.9·10⁵ ε` |

So **R as large as the certificates admit is 1.41 mm** for a step of the target, and the
certificate-only ISS gain `γ ≈ 3.9·10⁵` is far too large to carry an S-curve flight
(INDUCTION.md §1 reached the same conclusion for the V-ball tube and switched to `ℓ1`/peak gains of
exact responses). A usable `R` for a moving S-curve target needs those exact-response tubes, for the
whole family of legs `‖w' − p₀‖ ≤ R` (the S-curve table lemmas cover half legs up to 1.81 m,
SCurveCalc.lean, so `R ≤ 3.62` m is the navigator's side).

## 3. Milestone (3): liveness without a time bound (`Reach/Liveness.lean`, `Reach/Equilibrium.lean`)

* `code_filter_nonneg` (code fact, `float`): the update `s + (r − s) * alphaF` stays finite and
  `≥ 0` exactly (monotone rounding: `fl(r − s) ≥ −s`, `fl(fl(r − s)·α) ≥ −s`, `fl(s + ·) ≥ 0`). So
  `navProgress` is nondecreasing (`navProgress_succ` is exact).
* `liveness`, `liveness_code`, `passes_or_stalls`: if, off a stall set `Z`, a converging clock lets
  the raw scaler recover to `ρ ≥ 1.3·10⁻⁵`, then the clock tends to `∞` or converges into `Z`.
* `joint_stall_eq`, `vert_stall_eq` (exact, both shaping modes): at a stalled target with S-curve
  speed `v*` and acceleration `a*`, the equilibria are `e = (2/3) v*, ev = −v*, I = −a*`
  (horizontal) and `e_z = v* + a*/5, ev = −v*, eV = −a*/5` (vertical: the velocity loop has no
  integrator). `stall_dev`: the deviation follows the same switched model; `asymptotic_gain`:
  convergence to the equilibrium up to the floor.
* `stall_ratio`: the stalled raw-scaler numerator over `|v_T|` is `1 + d_z²(1/2 + 3/10 · a/v)`.
  `stall_ratio_ge_one`: on a horizontal leg, or while the S-curve does not decelerate, no stall.
  `stall_scaler_ge`, `stall_scaler_horizontal`: through P-1 (`rawScaler_ge`), within `δ ≤ 0.004` of
  the stalled equilibrium at speed `≥ 0.1` m/s the code's raw scaler is `≥ 0.9`.

**Finding: the LaSalle argument does not exclude a stall at the end of a leg with a vertical
component.** `stall_needs`: a stall needs `d_z ≠ 0` and `a/v ≤ −(10/3)((1.05 − ρ)/d_z² + 1/2)`
(for a vertical leg `a/v ≤ −5.17` s⁻¹), which the S-curve's final deceleration reaches. There the
stalled equilibrium has raw scaler `0` (the vertical feed-forward `a*` makes the vehicle sit behind
the target). Such a stall would leave the target short of `w'` by the remaining S-curve distance:
`≤ 0.021` m (`WP_ACC_Z = 1`) and `≤ 0.034` m (accel `1.5`), computed numerically for the
raised-cosine end (`scratchpad/reach/stall.py`, not certified). This is why `reach_model` carries
`d_Z`. Whether this equilibrium is attractive was not determined.

## 4. Milestone (4): reach (`Reach/Model.lean`)

`reach_model`: from the clock's code facts, `HL`, `HS` (the vehicle converges to within `b_S` of a
stalled target) and `HE` (after the end of the S-curve the vehicle ends within `b_E` of `w'`),
`∃ T, ∀ t ≥ T, ‖p_t − w'‖ ≤ max b_E (d_Z + b_S)`.

**The radius.** `d_Z ≤ 0.035` (numerical) plus `b_S`. For `b_E`: after the end of the S-curve the
single (non-fast) waypoint completes only when the vehicle is within `WP_RADIUS_M = 0.1`, and the
loiter target is then the stopping point, within `d + |v| + 10⁻⁵` of `w'` (`loiter_dest_bound`).
If the vehicle lags the target at the end of the leg, it completes on entering the 0.1 ball, so
`b_E` is about `0.1 + |v_c| + b`, not `0.085`. **`r = 0.1` needs a tight tracking bound at the
completion tick** (vehicle within about 0.03 m and slow, as `nom_complete` asks for the course), for
the whole family of legs. The certificates of §2 cannot give it (`γ ≈ 3.9·10⁵`).

## 5. The open fact, precisely

`HoverGlue sense32 senseP w₀ wp κ c₀ ν` (Loop.lean): every behavior of `Mloop` has a composite error
state `ξ`, read off the controller's world (`ctrlWorld`, the position PID, the attitude target and
shaping states, the rate PID) and the plant, with `posErr (ξ t) = pos (x t) − wp`, starting as the
pure offset, and following `cstep` with a disturbance bounded on `D` by `κ Vc + c₀`. It needs:

1. **The tick glue** (open in INDUCTION.md): `Vehicle.tick` split into the C-series calls on the
   loop's world (`ne_glue`, `vglue`), the attitude inner loop from C8–C16 (`attitude_tracks`, the
   joint model's attitude rows), the code invariant `CtrlInv` (finiteness, flags, branches) kept by
   every tick, and the first tick (`takeover`, `auto_init`) from `startP p₀ ψ₀`.
2. **The joins, quantitatively, in `D`**: the tilt coupling into the vertical channel and the
   heading rotation of the horizontal axes as `κ Vc` with `κ < (1 − λ)² ≈ 9·10⁻⁸` (the Young split
   of `Vc_step`), and the `float`/plant residuals as `c₀ ≤ 179` (per-tick `≤ 1.38·10⁻⁷` per
   coordinate). INDUCTION.md's table has rows up to `2.3·10⁻⁴` (at flight magnitudes); at hover the
   residuals must be shown to scale with the state.
3. **Unbounded time** (not needed for the 12000-tick `track_contract`): `ticks32` wraps after `2³²`
   ticks and re-takes the `first_tick` branch of `Vehicle.tick` (`last_loop_time_s := 1.0f/400.0f`,
   the same float as `0.0025f` by `dt_first`, so likely harmless, but unproved); `millis` (`UInt32`)
   wraps every 49.7 days and `micros32` every 71.6 minutes (slew limiter, motors, the loiter timer);
   the `float` S-curve time stops advancing once its ulp exceeds `2·dt` (after about 11.6 hours of
   S-curve time).

`ReachFacts` (Loop.lean) adds, per behavior: the clock's code facts along the run (`pace_filter`,
`pace_raw` of INDUCTION.md, and the sign `code_filter_nonneg` placed in the tick), the target path
`Γ` in S-curve time (`nav_step`, `NavInv`, the S-curve table for the leg `w' − p₀`), the
closed-loop facts `HL` (from `asymptotic_gain` + `stall_scaler_ge`, which still needs a version of
P-1 below `0.1` m/s: `rawScaler_ge` assumes `v_min ≥ 1/10`, so a stall at an interior point of
speed below 0.1 m/s near the leg start is not yet excluded), `HS`, and `HE` (completion and loiter,
§4).

The strongest theorems proved without these facts are the model-level ones: `hover_pes_model`,
`track_iss_model`, `liveness_code`, `joint_stall_eq`/`vert_stall_eq`/`stall_ratio`,
`asymptotic_gain`, `reach_model`, and on the loop `waypoint_reach_nonvacuous`.

## 6. Axioms (`lake env lean AxiomCheck.lean`, the new block; checked on the new files)

```
'Contracts.Track.AttJ.certA0' depends on axioms: [propext, Classical.choice, Quot.sound]
'Contracts.Track.AttJ.V_A' depends on axioms: [propext, Classical.choice, Quot.sound]
'Contracts.Track.AttJ.V_traj_sw' depends on axioms: [propext, Classical.choice, Quot.sound]
'Contracts.Track.AttJ.out_sq_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'Contracts.Track.Reach.hover_pes_model' depends on axioms: [propext, Classical.choice, Quot.sound]
'Contracts.Track.Reach.track_iss_model' depends on axioms: [propext, Classical.choice, Quot.sound]
'Contracts.Track.Reach.code_filter_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
'Contracts.Track.Reach.liveness_code' depends on axioms: [propext, Classical.choice, Quot.sound]
'Contracts.Track.Reach.joint_stall_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'Contracts.Track.Reach.vert_stall_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'Contracts.Track.Reach.stall_scaler_ge' depends on axioms: [propext, Classical.choice, Quot.sound]
'Contracts.Track.Reach.reach_model' depends on axioms: [propext, Classical.choice, Quot.sound]
'Contracts.Track.Reach.waypoint_reach_nonvacuous' depends on axioms: [propext, Classical.choice, Quot.sound]
'Contracts.Track.Reach.hover_practically_exponentially_stable' depends on axioms: [propext, Classical.choice, Quot.sound]
'Contracts.Track.Reach.waypoint_reach_of_facts' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The two conditional theorems take `HoverGlue`/`ReachFacts` as hypotheses; these are the open
facts, not axioms. `LibmSpec` is not used by any of the new theorems.

## 7. Files and build

| file | content |
|---|---|
| `Contracts/Track/AttitudeCert.lean` | milestone (1): kernel checks and `V` of the joint axis |
| `Contracts/Track/Reach/Composite.lean` | milestone (2): `Vc`, `Vc_traj`, `hover_pes_model`, `track_iss_model` |
| `Contracts/Track/Reach/Liveness.lean` | milestone (3): `code_filter_nonneg`, `liveness` |
| `Contracts/Track/Reach/Equilibrium.lean` | stalled equilibria, `stall_ratio`, `asymptotic_gain` |
| `Contracts/Track/Reach/Model.lean` | milestone (4): `stall_scaler_ge`, `reach_model` |
| `Contracts/Track/Reach/Loop.lean` | the loop statements, nonvacuity, the open facts, the conditional theorems |

Build: `LEAN_NUM_THREADS=1 lake build Contracts.Track.Reach.Loop` (each file 10–30 s once its imports
are built). Scripts: `scratchpad/reach/` (`eq.py`, `eqv.py`: the equilibria; `stall.py`: the stall
set), `scratchpad/attM4/` (the joint model and certificate generator of the previous agent).

## 8. Glue

Files `Contracts/Track/Reach/Glue{Tick,False,Tube,Loop,Mix,NE}.lean` (library `Track`), all
sorry-free, axioms `propext`, `Classical.choice`, `Quot.sound` (AxiomCheck.lean, last block). Build:
`LEAN_NUM_THREADS=1 lake build Contracts.Track.Reach.GlueLoop` (it imports the others;
each file 4–30 s once its imports are built; `CtrlAttitudeMixer` and `Induction/TickGlue` had to be
rebuilt, 13 s and 2.7 min).

### 8.1 Findings: `HoverGlue` is false, and the `Vc`-ball cannot carry the code

1. **The quantifier** (`not_hoverGlue`, `hoverGlue_hyps_false`). `HoverGlue` ranges over every
   behavior of `Mloop`, and `Mloop` does not constrain the initial plant state. The behavior from
   `wp` itself, level, moving north at speed `V` (`driftB`), must have `ξ 0 = pureOffset 0 = 0 ∈ D`,
   hence `Vc (w 0) ≤ c₀` and `‖p₁ − wp‖ ≤ √(γ_e c₀)`; the plant moves it by at least
   `hV − (g + a_max) h²` north whatever the actuators (`drift_north_ge`, from `v_scaledSol`). So
   `¬ HoverGlue … κ c₀ ν` for every world, ports, `wp` and `ν ≥ 0`; the hypotheses of
   `hover_practically_exponentially_stable` force `ν ≥ 0`, so that theorem is vacuous.
   **Corrected statement**: restrict to the behaviors of a scenario (`S`: the hover world, started in
   the region), as `HoverGlueT`/`HoverGlueG` below do.
2. **The constants** (`ball_route_floor`). `attitude_from_thrust_vector` takes the commanded tilt
   as `acosf(-n.z)` of the normalized thrust vector. In `float` the dot product is exactly `1` for
   every horizontal command `|a| ≤ 3.38·10⁻³` m/s² (tilt `≤ 3.45·10⁻⁴` rad; float32 emulation
   `scratchpad/glue/quant.py`, max tilt error `3.45·10⁻⁴` rad over `|a| ≤ 0.5`; not kernel-checked:
   the length uses the opaque `sqrtf`), so the desired attitude is exactly level. In the joint model
   this is the disturbance `δ h_c k_v² (e₆ + h_c e₇ + e₈ − e₉)`, whose `V_j` at `δ = 3.38·10⁻³` is
   `7.1·10⁵` (`quant_V_ge`, kernel-checked), against `c₀ ≤ ν (1 − λ)² ≤ 179.1` inside the linear zone
   `ν ≤ 1.99·10⁹` (`c₀_le_of_hyps`). Accommodating it needs `ν ≥ 7.9·10¹²`, i.e. `b ≥ 3.4` m. The
   quantization fits the tube design: it is below INDUCTION.md's attitude-deviation bound `εη = 0.01`
   m/s².
3. **The pure-offset start is not the code's start** (`ξ 0 = pureOffset` fails on the readout). The
   vertical readout's integrator is `I − (hover − 1/2.25)` and the filter, `_throttle_in` and held
   actuators are `· − 1/2.25`. At the takeover `I = 0` and the throttle is `MOT_THST_HOVER`, so these
   coordinates are `±(1/2.25 − hover)`: `4.4·10⁻⁵` for `0.4444` (copter-cf2x), `0.054` for the
   construct default `0.39`. Corrected: the start is the offset plus deviations within `ε0`
   (`HoverStart`), or any state in a weighted-ℓ1 region (`HoverStartG`).
4. **The world** (`ReachParams`). It fixes `kp_ne`, `kp_d`, the jerk, the attitude limits, `input_tc`
   and the `kimax`s, but not the gains and filters the models are built on (`PSC_NE_VEL_*`,
   `PSC_D_VEL_P`, `PSC_D_ACC_*`, `ATC_RAT_*`, `ATC_ANG_*_P`, the filter cutoffs, `MOT_THST_HOVER`).
   A `ReachWorld` booted with other values has other dynamics. `MissionParams` has the same gap;
   INDUCTION carries the values in the per-tick hypotheses (`DPar2`, `NERegion.velg`, …). The
   corrected glue must assume the copter-cf2x values, as fields of the world or in `S`.
5. **The target is not held at the waypoint.** With the mission `#[w']`, `mission_start` runs an
   S-curve from the stopping point at the start to `w'`; at completion (`reached_wp_destination`)
   `loiter_start` sets a second S-curve from `w'` to the stopping point of that moment (within
   `d + |v| + 10⁻⁵` of `w'`, `loiter_dest_bound`). "The target fixed at `w`" holds only in the hold,
   after that second S-curve ends, with `w` the loiter point (`HoldScenario`). A start exactly at
   `w'` gives a leg shorter than `FLT_EPSILON` (treated as zero) but still a target move at
   completion.
6. **Unbounded time, `ticks32`** (`schedW_loop_time`, `dt_first_eq`, kernel evaluation of core's
   float model): at the wrap `first_tick` sets `last_loop_time_s := 1.0f/400.0f`, which is the same
   `float` as `2500 · 1e-6f`; nothing else of `Vehicle.tick` reads `first_tick` (`in_auto` gates
   `ModeAuto::init`). The `micros32`/`millis` wraps and the S-curve clock's ulp (REACH.md §5.3)
   remain for the glue.

### 8.2 (1) The tick as its calls (`GlueTick.lean`)

`tick_split`: `Vehicle.tick w smp = (finW (postD (navW (missionW (preNav w smp)))),
actOf (postMot (preMotS w smp)))`, with
`preMotS = tresetW ∘ rateW ∘ dtW ∘ gyroW ∘ schedW` (scheduler; gyro; `set_dt_s` × 3;
`rate_controller_run`; `rate_controller_target_reset`), then `postMot` (`output`; the actuators are
read here), `preNav = rhmW ∘ landW ∘ modeW ∘ estW ∘ viewUpdate ∘ smpW` (sample, view,
`update_estimates`, first tick only `ModeAuto::init` + rate time constants, `landed_gain_reduction`,
`set_reset_handling_method`), `missionW` (`mission_start` on the first run, else `mission_update`),
`navW` (spool state, `update_wpnav`, its events replayed), `postD = applyPos ∘ dW`
(`D_update_controller`, then `set_throttle_out`), `finW` (`get_thrust_vector`, the heading,
`input_thrust_vector_heading`). The order matches `copter_ref.cpp`; no discrepancy with the brief's
list except that it omits the gyro and sample stages (`gyroW`, `smpW`) and that the first run is
`mission_start`, not `mission_update`.

The hold (`au.state ≠ RUNNING`, after the start): `tick_hold` (`missionW` is the identity),
`tick_hold_ps` (with the navigator steady: `set_pos_terrain_target_D_m 0`,
`set_pos_vel_accel_NED_m P V A`, **one** `NE_update_controller`, then `D_update_controller`, and
nothing later writes `ps`), `offZ_tick_hold` (the horizontal offsets stay zero, given the
conditions of `NE_update_controller`'s offset lemma at the state the tick hands it).

### 8.3 (2) Readouts (`GlueLoop.lean`, `GlueMix.lean`)

* The readouts are INDUCTION's `ξV`, `ξH` (`Induction/Run.lean`); with the target held,
  `ξV_pos`, `ξH_pos`: their position coordinates are `pos − wp`.
* `hmix` (`GlueMix.hmix_of_spec`): from the two first conclusions of `Mixer.tick_output_spec` at
  the tick's output call `preMotS w smp`, the tick's mean actuator is within `3·10⁻⁷` of the stored
  filter (`act_tick`: the returned actuators are those `output` stores; `filt_tick`: no later call
  touches the filter's output; `utf_eq`: it is the float update `F`; `Σ RF = Σ PF = Σ YF = 0`).
* `NEGlue` (INDUCTION's `ne_glue`, `GlueNE.neGlue_hold`): on a steady hold tick the tick hands
  `NE_update_controller` the state `neIn … P V A`; if that call is in `NERegion` and the vertical
  controller is active after it, `NEGlue w₀ x t` holds. The readouts are matched by frames:
  `D_update_controller` keeps the horizontal targets (`nef_D`), `NE_update_controller` keeps
  `_vel_desired`, `_accel_desired` and, in its region, the value of `_pos_desired` (`ne_posd_val`:
  the P controller returns the target, and `(d + 0) − 0 = d` in `double`); the estimates are the
  sample and the PID state is the tick's start (`preNav_pid_est`). With INDUCTION's proved
  `wHβ_bound` this gives the horizontal rows of `dist` from `NERegion`.
* `NavV` of `VTickHyp` (`GlueMix.navV_hold`): on a steady hold tick the mission update is the
  identity and `update_wpnav` logs no `D_init_controller_stopping_point`.
* Not done: `VTickHyp`'s region fields (`DPar2`, `DReg2`, `MotReg`, `BoostReg`, the mixer region)
  and `NERegion` from the box (they need the code invariant `CtrlInv`, which INDUCTION also leaves
  open), `VGlue`'s target readouts (the vertical `_pos_desired.z` after `D_update_controller`,
  the analogue of `ne_posd_val` with the 1D P controller), the attitude readouts (the tube form
  abstracts the attitude loop by `aLag` and `εη`, so the joint model's attitude rows are not
  needed), the first ticks into the region.
* **Discrepancy (unbounded time)**: `VTickHyp.ht0 : ticks32 ≠ 0` fails once every `2³²` ticks, at
  the wrap, although that tick computes the same loop time (`schedW_loop_time`). For unbounded time
  `vertical_tick_split`'s hypothesis `ht0` must be replaced by `smp.dt_us = 2500` (which already
  gives the loop time `0.0025f` in both branches).

### 8.4 (3) The region and its forward invariance (`GlueTube.lean`)

`HoverModel` / `HoverModelG`: from `t₀`, the readouts follow `A_v`, `A_h`, and, while the box `BoxT`
has held at every tick since `t₀`, the disturbances are within `εVh`, `εHh` per coordinate.
`hover_box` / `hover_box_gen` prove, by strong induction with the ℓ1 tube
(`chan_tube`, `chan_tube_gen`, from INDUCTION's `tube_out` and the certified gains `peakV'`,
`gainV'`, `peakH'`, `gainH'`), that the box holds at every tick and every output is within
`Σ G ε` (plus `Σ P ε₀`) of its free response. The free position response decays by the
Lyapunov certificates (`respV_decay`, `respH_decay`, `freeV_decay`, `freeH_decay`).

| | vertical (`ez, ev, eV, eA, I, f, u, w`) | horizontal (`e, ev, E, D, I, a, c₁, c₂, c₃`) |
|---|---|---|
| `ε` per tick | `1e-8, 7.6e-6, 2e-7, 4.2e-6, 2e-7, 1e-7, 3.2e-6, 4e-7` | `2.2e-7, 2.5e-5, 3.7e-6, 2.31e-4, 6.2e-7, 0, 1.61e-4, 0, 0` |
| `ε0` (pure-offset start) | `0, 1e-6, 1e-5, 1e-5, 1e-4, 1e-4, 1e-4, 1e-4` | `0, 1e-6, 1e-5, 1e-4, 1e-5, 1e-5, 1e-4, 1e-4, 1e-4` |
| box | `|ez| ≤ 0.1`, `|ev| ≤ 0.5`, `|I| ≤ 0.5`, `|f|, |u| ≤ 0.12` | `|e| ≤ 0.1`, `|ev| ≤ 0.5`, `|I| ≤ 5`, `|c₁| ≤ 0.5`, `|c₁ − c₂| ≤ 0.05` |
| position tube | `0.93` mm (`+ 0.15` from `ε0`) | `2.51` mm |

`εH` is INDUCTION.md's (controller and plant rows, attitude deviation `εη = 0.01` m/s² from the
lag law, which covers the tilt quantization). `εV` is INDUCTION.md's plus the structured part
`CtrlV.wS` at hover (plant remainder and tilt coupling `≤ 3·10⁻³` m/s² through `(h²/2, h)`, the
sampled specific force's `float` floor through `αA`); the horizontal command box is `0.5` instead
of `4` so that the tilt (`≤ 0.051` rad) keeps that coupling small. These `ε` are the hypotheses
of the glue (their discharge is the open part, §8.6).

### 8.5 (4) The hover theorems and their constants (`GlueLoop.lean`)

* `hover_practically_exponentially_stable_tube S … wp t₀ (hG : HoverGlueT S …)`: for every
  behavior in `S` whose hold starts at `t₀` in `HoverStart` (offset `|dᵢ| ≤ 2.1` cm per axis, the
  other readouts within `ε0`),
  `‖p_t − wp‖ ≤ 3.47 · 0.9997^(t − t₀) · ‖p_{t₀} − wp‖ + 0.0039` for all `t ≥ t₀`
  (`hover_tube_axes`: per axis `3.47 · 0.9997ᴺ |dₐ| + 2.51` mm and `1.452 · 0.998ᴺ |d_D| + 1.08` mm,
  and the box at every tick).
* `hover_practically_exponentially_stable_gen S … (hG : HoverGlueG S …)`: from any start in
  `RegionG` (peak-weighted ℓ1 size plus tube inside the box), the box at every tick and
  `‖p_t − wp‖ ≤ 0.9997^(t − t₀) · √(γ_h V_h(ξ_N) + γ_h V_h(ξ_E) + γ_v V_v(ξ_D)) + 0.0039`.
  `hover_hold` is it for `S = HoldScenario` (the single waypoint completed, the loiter S-curve
  finished, the target at `wp`).

| constant | value |
|---|---|
| `λ` (position bound per tick) | `0.9997` (horizontal certificate; vertical `0.998`); time constant 3333 ticks = 8.3 s |
| `c` | `3.47` (`√(γ_h P_h,00) = 3.466`; vertical `1.452`) |
| `b` | `3.9` mm (`√(2 · 2.51² + 1.08²) = 3.70` mm) |
| region, pure offset | `|dᵢ| ≤ 2.1` cm per axis (binding: `|c₁ − c₂| ≤ 0.05`, peak gain `2.3`; vertical alone `9.7` cm) |
| region, one coordinate alone (`RegionG`) | horizontal: `|e| ≤ 2.1` cm, `|ev| ≤ 3.2` cm/s, lag state `|a| ≤ 0.85` m/s² (tilt `0.087` rad), `|c₁| ≤ 0.048` m/s²; vertical: `|ez| ≤ 9.7` cm, `|ev| ≤ 0.38` m/s |
| invariant box | speeds `|ev| ≤ 0.5` m/s, commanded tilt `≤ 0.5/g = 0.051` rad, command rate `≤ 0.05` m/s² per tick |

Compared with the `Vc`-ball (§2): region 2.1 cm instead of 1.41 mm, `b` 3.9 mm instead of an
admissible floor that the code exceeds by a factor `4·10³`.

### 8.6 What remains open

Superseded by §8.7 (2026-11-06). `HoverGlueT`/`HoverGlueG` as stated are **false** on flights
(§8.7, findings 2–4): their `dist` field bounds the attitude deviation by `εη = 0.01` and the
vertical rows by `εVh` at every tick, and the start table has `eA ≤ 10⁻⁵`; the measured transient
exceeds all three. `hover_practically_exponentially_stable_tube`, `_gen` and `hover_hold` are kept
as model-level results; the theorem of record is `Hover.hover_stable` (§8.7). Open after §8.7:

* the fields of `HoverFacts` that stay assumed: the hold flags per tick (`hold`), the horizontal
  controller's region (`ne`, INDUCTION's `CtrlInv` part of `NERegion`), the body rates (`rates`),
  the attitude deviation (`att`, M4's `attitude_tracks` in its measured form), the vertical code rows
  (`vcode`, INDUCTION's `vglue`; `VTickHyp.ht0` fails at the `ticks32` wrap, so the field is stated
  on the rows), the structured vertical disturbance (`vstruct`);
* the `micros32` and `millis` wraps (71.6 min, 49.7 days) and the S-curve clock's ulp for unbounded
  time: the fields are per tick for all `t`, measured on 30 s;
* the first ticks into the hold (the scenario starts in the hold world).

### 8.7 The hover theorem of record (`Hover*.lean`, the hover campaign)

Files `Contracts/Track/Reach/HoverTube.lean` (the tube with a transient excess), `HoverModel.lean`
(the constants, the model `HoverModelS`, `hover_box_s`, `hover_axes_s`), `HoverCert.lean` (decay
constants of the position responses), `Hover.lean` (the facts, the discharge, the theorem). All
sorry-free; all 72 theorems depend only on `propext`, `Classical.choice`, `Quot.sound`
(AxiomCheck.lean, last block). Build: `LEAN_NUM_THREADS=1 lake build Contracts.Track.Reach.Hover`
(the four files 17 + 16 + 18 + 19 s once GlueLoop and LegGains are built; HoverCert imports
LegGains for the certified state `A_h^{1728} e₁`). Campaign: `staging/text/hover-campaign.md`,
`hover-campaign.csv`; scripts in the scratch directory `hover/campaign/` (`fly_disp.py`,
`campaign.py`, `recon.py`, `analyze.py`, `s2.py`) and `hover/` (`calib.py`, `budget.py`, `post.py`).

```lean
theorem hover_stable (sense32 : ℝ → Float32) (senseP : ℝ → Float) (w₀ : Vehicle.World)
    (wp p₀ : P3) (ψ₀ : ℝ) (_hP : Leg.LegParams w₀) (_hH : HoldWorld w₀ wp)
    (hd : ∀ i, |(p₀ - wp) i| ≤ 21 / 1000) (hwp : ∀ i : Fin 2, |wp i.castSucc| ≤ 39 / 10)
    (hS : Plant.CopterSense sense32 senseP) (hL : LibmSpec)
    (hF : HoverFacts sense32 senseP w₀ wp p₀ ψ₀) :
    Mloop sense32 senseP w₀ ⊨
      ⟨Reach.Ahover p₀ ψ₀, {x | ∀ t, dist (pos (x t)) wp ≤
        368 / 100 * (9997 / 10000 : ℝ) ^ t * dist (pos (x 0)) wp + 36 / 10000}⟩
```

Companions: `hover_stable_box` (the box `BoxS` at every tick) and `hover_stable_nonvacuous`.
`pos (x 0) = p₀` (`pos_zero`). `HoldWorld` (in Auto past the start, mission `COMPLETE`, S-curve
finished, target `wp`) and `LegParams` are the context, not used by the proof; `hwp` bounds the
horizontal position for M6's sensing lemmas.

**The scenario.** "Hovering at a fixed position target" is the hold: the controller's world holds
`wp`, the vehicle is displaced by `d` at rest, level, any heading, hover actuators held, and
`Mloop`'s takeover hands it over. The start the brief describes (`run_copter.py --init-ned` at
`w + d` with the single waypoint `w`) does not hold the target at `w`: 24 such flights
(`waypoint-start` rows of the CSV) run an S-curve to `w`, then the loiter moves the target to the
stopping point at completion, 4.1 to 22.1 mm from `w` (0.59 to 0.96 times the offset), held from
tick ≤ 785; the bound with `w` fails on 23 of 24 (ratio up to 3.06). The campaign therefore flies
the hold: `copter_ref` from rest at `w` (zero-length leg, the target never moves), 4000 ticks, then
the simulated body is moved to `w + d` at rest and level (specific force `(0, 0, −g)` on that tick),
12000 more ticks. The move does not run `Mloop`'s takeover: the takeover's throttle reset
(`f = u = 0.4444 − 1/2.25 = −4.4·10⁻⁵`) is within the start table, the attitude relax is a no-op
on a level hold at the same heading.

**Findings (2026-11-06).**

1. The single-waypoint start does not hold the target (above); the field "the target held at `w`"
   is false there and true (exactly: position, velocity and acceleration targets) in the hold.
2. **The attitude deviation from the lag law** (`etaA = aReal − aLag`) reaches `0.0584` m/s² at a
   corner start; `εη = 0.01` (HoverGlueT's `dist`, INDUCTION's
   `attitude_tracks`) is false during the first 237 ticks. After them `≤ 0.00395` (the `acosf` tilt
   quantization's limit cycle).
3. **The vertical rows**: the tilt of the transient couples into the vertical channel through the
   plant (`ρz`, `ρv`), the sampled specific force (`ρam`, through the 20 Hz filter into `eA`, `I`,
   `u`) and the angle boost (`τ`, whose angle is AC_AttitudeControl's `_thrust_angle_rad`, the
   **current** lean angle of the previous tick's sample, checked against the throttle recovered
   from the actuators within `7.3·10⁻⁷`). Rows `ez, ev, eA, I, u` reach `6.9·10⁻⁸, 1.02·10⁻⁵,
   9.78·10⁻⁴, 2.44·10⁻⁷, 2.35·10⁻⁴` against `εVh = 10⁻⁸, 7.6·10⁻⁶, 4.2·10⁻⁶, 2·10⁻⁷, 3.2·10⁻⁶`: false.
   The boost and the plant loss cancel physically; the per-row ℓ1 tube does not see the
   cancellation.
4. **The start**: in a settled hold `eA` reaches `1.04·10⁻⁵` against `ε0Vh = 10⁻⁵`: false; now
   `2·10⁻⁵`. `ev` at the start is `0` exactly (at rest, velocity target `0`); `eV ≤ 1.9·10⁻⁶`,
   `I ≤ 1.1·10⁻⁷`, `f, u, w ≤ 6.3·10⁻⁸` (`−4.4·10⁻⁵` after `Mloop`'s takeover); horizontal readouts
   besides the offset `0`. (This is the hold's start; the leg's start after the takeover from rest,
   with `ev ≈ 5·10⁻⁶` and `eA ≈ 2.3·10⁻⁴` at tick 2, is another table, `ε0VL`.)
5. The simulator's position row (`2.09·10⁻⁷`) exceeds the Lean plant's proved `1.8·10⁻⁷`
   (`prow_le`): pybullet's integrator, not the ODE; the Lean bound is used.

**The budget with the measured disturbance class.** Each row's per-tick disturbance is within a
floor `ε` (the persistent part) plus an excess `exc = max(|w| − ε, 0)` whose weighted sum
`Σ_k exc_k / λ^(k+1)` is at most `κ · ‖d‖∞` (`HoverModelS`). The tube (`tube_exc`) adds the
convolution of the response with the excess, bounded through the peak gains (box: `exc_peak`) and
through per-coordinate decay constants (decay: `exc_decay`). The excess thus enters the
**decaying term**, not the floor.

| | value | from |
|---|---|---|
| horizontal floor `εHs` | `εHh` (`εη = 0.01`) | unchanged |
| vertical floor `εVs` | `εV + (1e-9, 1e-8, 0, 1e-6, 3e-10, 0, 2e-7, 0)` | ≥ 3× the measured persistent level |
| `κη` (attitude excess) | `226` (horizontal rows `κη · (h²/2, h)`) | measured `220.75` |
| `κV` | `8.1e-4, 0.035, 0, 3.32, 8.3e-4, 0, 0.8, 0` | measured `7.86e-4, 0.0339, 0, 3.245, 8.10e-4, 0, 0.779, 0` |
| start `ε0Vs` | `0, 1e-6, 1e-5, 2e-5, 1e-4, 1e-4, 1e-4, 1e-4` (was `eA 1e-5`) | measured above |
| horizontal box | rate `|c₁ − c₂| ≤ 0.075` (was `0.05`) | the region closes at `0.068` |
| decay constants `cHd` | Lyapunov `√(γ_h P_jj)`, except `ev`: `1/4` | `respH_e1`: peak `0.147` before tick 1728, certified `V(A_h^{1728} e₁) ≤ 1.5·10⁹` after (`γ V ≤ (λ^{1728}/4)²`, `λ^{1728} ≥ 0.595`) |
| decay constants `cVd` | `1.08, 0.32, ·, 0.0023, 1.71, ·, 0.0077, ·` | `decay_of_min`, `respV_cVd`: `min(P_j, c_j λ_vᵐ) ≤ c'' λᵐ` at switch ticks `176, 680, 1528, 872, 1176` (Lyapunov `1.452, 1.003, 0.0307, 7.448, 0.0562`) |
| `mH = Σ cHd κH`, `mV = Σ cVd κV` | `≤ 0.1438`, `≤ 0.0274` | `mH_le`, `mV_le` |

Region (pure offset `2.1` cm per axis, kept): horizontal outputs at `0.026, 0.045, 0.021, 0.455,
0.068` of the box `0.1, 0.5, 5, 0.5, 0.075`; vertical at `0.022, 0.021, 0.0014, 0.0035, 0.024` of
`0.1, 0.5, 0.5, 0.12, 0.12` (`regionHs`, `regionVs`). Per axis (`hover_axes_s`):
`|eₐ| ≤ 3.47 λᴺ |dₐ| + 0.1438 λᴺ ‖d‖∞ + 2.51` mm, `|e_D| ≤ 1.452 λ_vᴺ |d_D| + 0.0274 λᴺ ‖d‖∞ +
0.35` mm (the vertical floor drops from `1.08` mm with the lower persistent floors). Distance
(`norm_le_axes3`): `C = 3.47 + √(2 · 0.1438² + 0.0274²) ≤ 3.68`, `b = √(2 · 2.51² + 0.35²) ≤ 3.6` mm.

| constant | before | after |
|---|---|---|
| `C` | `3.47` | `3.68` (the transient excess) |
| `λ` | `0.9997` | `0.9997` |
| `b` | `0.0039` | `0.0036` |
| region | `2.1` cm per axis | `2.1` cm per axis |

**`HoverFacts`: the fields, measured against assumed** (244 starts; every assumed number at least
2 % above the measured one).

| field | assumed | measured (max) | status |
|---|---|---|---|
| `init` | `ε0Vs`, `ε0Hs` | above (finding 4) | holds |
| `target` | target `= wp`, velocity and acceleration targets `0`, every tick | exactly | holds |
| `hold` | in Auto, past the start, not running, `SpeedSteady`, no terrain, every tick | not observable | assumed |
| `ne` | `NERegion` at the tick's `NE_update_controller`, `D` active after, while in the box | `‖e‖ ≤ 0.0297`, speed `≤ 0.0343`, command `≤ 0.434` | assumed (code invariant) |
| `rates` | `|p|, |q| ≤ 2`, `|r| ≤ 1.4` rad/s | `0.285, 0.282, 1.1e-4` | holds |
| `att` | `Σ exc(etaA, 0.01)/λ^(k+1) ≤ 226 ‖d‖∞` | `220.75 ‖d‖∞`; `etaA ≤ 0.0584`, `≤ 0.00395` after the transient | holds (replaces the false `εη` row bound) |
| `vcode` | vertical row minus `wS` within `εV` | not observable (float rounding) | assumed (`vglue`) |
| `vstruct` | `Σ exc(wS_j, εS_j)/λ^(k+1) ≤ κV_j ‖d‖∞` | finding 3; ends by tick 919 | holds (replaces the false `εVh`) |

**Discharged from the code** (`Hover.rowH_code`, `excH_le`, `hoverModelS_of_run`): the horizontal
rows, which `HoverGlueT` assumed, now follow from `hold` and `ne` by `neGlue_hold` (which uses
`tick_hold_ps`), INDUCTION's `wHβ_bound` (M6's `horizontal_tick_eq_D`) and the plant row
`prow_ahover` (`Plant.step_pv_sharp`, from `rates`); the speeds and positions `wHβ_bound` needs come
from the box and `hwp`. What remains of the horizontal row is the attitude deviation (`att`). The
forcing of the target is zero from `target` (`forceH_zero`, `forceV_zero`). The vertical rows split
into the code part (`vcode`) and `CtrlV.wS` (`vstruct`); `navV_hold` and `hmix_of_spec` are not
used, because the code part is stated on the rows (`VTickHyp.ht0`, the hypothesis that would let
`wV_bound` discharge it from `VGlue`, fails at the tick-counter wrap).

**Audit at the extremes.** The start set's extremes (the 8 corners, at 4 headings each) give the
maxima of every measured field; across the four headings `κη` varies by `3.2` % (`213.7` to
`220.75`) and `κV` by `1.0` %, across the three targets by less than `0.001` %. The box the fields are conditioned on allows
more than the region reaches (proved envelopes: command `0.455`, rate `0.068`; measured `0.307`,
`0.0472`): at the box's command `0.5` per axis the tilt `0.072` rad would give `ρam ≈ 0.026` m/s²
and `τ ≈ 1.2·10⁻³` per tick (measured at the corners `4.1·10⁻³`, `2.3·10⁻⁴`); those behaviors are
not behaviors from the region (`hover_stable_box`).

**Measured against proved**: the largest ratio of `‖p_t − wp‖` to the bound is `0.267` (`0.282`
against the earlier constants), the smallest margin `3.96` mm; the error is below 1 mm from
`2.585` s on and below `0.23` mm at 30 s; per-axis bounds reached at most `0.789`. Parity: 20 starts
also flown with `copter_lean`: `motors.txt` and `flight.csv` (without `tick_us`) identical on all
16000 lines of each.

## 9. The leg theorem

Files `Contracts/Track/Reach/Leg.lean` (the facts and the statement), `LegTube.lean` (the tube),
`LegGainsData.lean` (generated kernel certificates, `gen_lean_A.py`) and `LegGains.lean`
(`refGains_certified`), `LegNav.lean` (the tube on the loop, completion, loiter), `LegHold.lean`
(the hold and the theorem), `LegBox.lean` (the box variant with the loiter target from the code).
All sorry-free; all 223 theorems depend only on `propext`, `Classical.choice`, `Quot.sound`
(AxiomCheck.lean, last block; checked with a scratch file importing `LegBox`). Build:
`LEAN_NUM_THREADS=1 lake build Contracts.Track.Reach.LegBox` (about 4 min once GlueLoop is built;
`LegGainsData` is about 100 s of kernel checks).

**Repaired 2026-11-06.** The field `legH` (and `TickBounds`) bounded the velocity defect `d₂` of the
target sequence by `1.3·10⁻⁴`; the coordinator measured `7.68·10⁻⁴` (§9.4, finding 7). The field was
false on every leg of 0.2 m or more, so the theorem as stated on 2026-11-05 was vacuous. The repair
raises the bound to `8·10⁻⁴` (in `TickBounds`; `legH` itself was then unused and is removed), which breaks three closures of the previous proof (the box, the
completion through the tube along the leg, the hold), and replaces each (§9.2). The per-tick audit of
the campaign traces found three more false fields (`order`, the vertical `d₂` of `tick`, and the
form of `arrive`), repaired the same way (§9.3).

### 9.1 The statements

```lean
theorem waypoint_reach_h (sense32 : ℝ → Float32) (senseP : ℝ → Float) (w₀ : Vehicle.World)
    (p₀ : P3) (w' : AC_WPNav_lib.Vector3p.State) (ψ₀ : ℝ) (hP : LegParams w₀)
    (hmin : 1 / 100 ≤ dist p₀ (wpt w')) (hR : dist p₀ (wpt w') ≤ 36 / 10) (hZ : wpt w' 2 = p₀ 2) (hW : ReachWorld w₀ w')
    (hS : Plant.CopterSense sense32 senseP) (hL : LibmSpec)
    (hF : LegFacts sense32 senseP w₀ p₀ w' ψ₀) :
    Mloop sense32 senseP w₀ ⊨
      ⟨Ahover p₀ ψ₀, lang_t 0 (.eventually 0 4800 (.always 0 1200 (near (wpt w') (1 / 10))))⟩

theorem waypoint_reach_h_box ... (hP : LegParams w₀) (hmin) (hR) (hZ) (_hbox : ∀ i, |p₀ i| ≤ 3 / 2)
    (hw : ∀ i, |wpt w' i| ≤ 19 / 10) (hW) (hS) (hL) (hF : LegFactsBox sense32 senseP w₀ p₀ w' ψ₀) :
    (the same conclusion)
```

The statement is unchanged by the repair: radius `0.1`, `◇_[0,4800] □_[0,1200]`, horizon 6000.
What changed is the content of `LegFacts` (§9.3).

**`hP : LegParams w₀`** pins the parameters the channel models and their ε tables are built on and
that `ReachWorld` does not fix (§8.1 item 4), with the copter-cf2x values as `Float32` literals (the
form of `MissionParams`): `MOT_THST_HOVER 0.4444` (`_throttle_hover`; the construct default is
`0.35`), no hover learning, the linear thrust curve (`MOT_THST_EXPO 0`, `MOT_SPIN_MIN 0`,
`MOT_SPIN_MAX 1`, `MOT_BAT_VOLT_MAX 0`), `ATC_ANG_RLL_P 9`, `ATC_ANG_PIT_P 9`, the horizontal
velocity PID (`PSC_NE_VEL_P 6`, `I 1`, `D 0.5`, `FF 0`, filters 5 Hz), and the vertical controllers
(`CtrlV.DPar2`: `PSC_D_POS_P 1`, `PSC_D_VEL_P 5`, `PSC_D_ACC_P 0.05`, `PSC_D_ACC_I 0.1`, filters 5, 5,
20 Hz, `IMAX ≤ 2`). The attitude rate PIDs are not pinned (the attitude loop enters only through the
lag law and the row `εη`, a fact of `tick`). That the course world has these values is, as for
`MissionParams`, an executed check (the kernel cannot evaluate `construct`), not a Lean proof.

`w'` is the mission's `Vector3p.State` because `ReachWorld` takes that type; the formula reads it
as `wpt w'`. **`hmin`**: a leg shorter than 1 cm starts with the vehicle already at the setpoint
(the hover of `Glue.hover_hold`, not a leg); the hypothesis makes the vertical reference bound
`legV` satisfiable (§9.3). `hP`, `hmin`, `hR`, `hZ`, `hW`, `hS` are not used by the proof: they are the
context in which the fields are discharged; `hL` is used by the box variant.
`waypoint_reach_h_nonvacuous`: `Mloop ∩ Ahover p₀ ψ₀` is nonempty for every world, ports, `p₀`, `ψ₀`.

**The box variant**: `LegFactsBox` is `LegFacts` with `loiter` replaced by `loiterCode` (the loiter
target is within `10⁻⁶` of the code's stopping point `stopPt p s` of the completion tick's position
controller state, `LoiterHyps p s`, estimates within `10⁻⁶` of the plant state). The loiter bound is
then proved from `loiter_dest_bound` (`loiter_of_code`). `hw` is needed because `loiter_dest_bound`
asks for the estimate within 2 m per axis, and `hR` with `|p₀ i| ≤ 1.5` gives only `|w' i| ≤ 5.1`.

### 9.2 The proof

1. **The tube** (`LegTube`). The readouts `ξV`, `ξH` (INDUCTION's) follow
   `ξ' = A ξ + asp • B − d₁ • e₀ − d₂ • e₁ + w` (`legModel_of_run`). Every watched output is its free
   response plus three reference terms plus the ℓ1 tube of `w` (`forced_eq`, `out_le`); the
   reference terms use the gains in the reference directions (`env_const`, `env_tail2`,
   `env_tail_l1`). The feed-forward cancels the kinematics (`Ah_vAcc : A_h vAcc + B_h = vAcc`), so
   the position error's gain in the direction `B_h` is 0.030.
2. **The box** (`leg_box`): at every tick from 2 to 6000. With `d₂ ≤ 8·10⁻⁴` the plain ℓ1 envelopes
   give the position error `0.143`, the command `4.14`, the command rate `0.055`: above INDUCTION's
   box `0.1 / 4 / 0.05` in all three. The repair:
   * **position error**: the leg box `bHL` widens it to `0.15` (margin 4.5 %). The command and its
     rate are M4's class `CmdOK` (`≤ 4`, `≤ 0.05`) and are kept; the position error enters the
     horizontal controller's tick only through `NERegion.e` (`‖e‖ ≤ 0.4`), so the rows `εHL` are
     claimed on the wider box (a stronger `tick`, discharged by the same `ne_glue`).
   * **command** (`c1_bound`): in `ζ = ξ − asp • vAcc` the command is `asp + c₁(ζ)` and `ζ` is driven
     by the jerk; the jerk gain of `c₁` is the `c₁` coordinate of the certified `vAcc` trajectory
     (`60.54`): `|c₁| ≤ 1.514 + 1.491 = 3.005 ≤ 4`.
   * **command rate** (`rate_bound`): in `ζ₂ = ζ − d₂ • u₂`, with `u₂ = (1/3, −1/2, 0, 0, 400, …, 400)`
     the steady state of a constant velocity defect (`Ah_u2 : A_h u₂ = u₂ + e₁`), the rate sees
     neither shift (`outH4_vAcc`, `outH4_u2`) and `ζ₂` is driven by the jerk, `d₁` and the change
     `Δd₂` per tick, whose rate gain is the `c₁` gain of `e₁` (`rate_u2`, `gainU2`: `643`). With
     `|Δd₂| ≤ 1.1·10⁻⁵` (field, measured `1.007·10⁻⁵`): `0.0036 + 0.0298 + 0.0045 + 0.0071 + 0.0012
     = 0.0462 ≤ 0.05` (start, jerk, `d₁`, `Δd₂`, rows).
   * the velocity error `0.414 ≤ 0.5`, the integrator `0.414 ≤ 5`; vertically `0.073, 0.175,
     0.028, 0.038, 0.044` against `0.1, 0.5, 0.5, 0.12, 0.12` (with the vertical `d₂ ≤ 2·10⁻⁵`).
3. **The leg** (removed 2026-11-06): the ℓ1 tube along the leg would give `err ≤ 0.145` (the velocity
   defect contributes `8·10⁻⁴ · 74.3 = 0.059`; campaign max `0.0419`), too wide for the completion
   radius `0.099`. Nothing else used it, so `err_leg`, `leg_e`, `leg_3d`, the field `legH` and the
   direction witness `c` were removed (an unused field must not stay in `LegFacts`). The vertical
   tube on the leg (`leg_z`, `vzL ≤ 7.91` mm from `legV`) is kept: the completion uses it.
4. **Completion by decay** (`tail_e_c`, `complete_3d`, `Tc_le`): the leg's S-curve has finished by
   `Te ≤ 2200` and from `Te` to the completion the reference is at rest (`arrive`). If the mission has
   not completed by `Te + Mc`, `Mc = 416`, then per axis
   `|e| ≤ 1.501·TBc + 1.3·10⁻⁴·T0c + ¼·P1c + residual + τe = 0.0252 + 0.0121 + 0.0139 + 0.0002 +
   0.0025 = 0.0539`: the tails past `Mc` of the responses to `B_h` and `e₀`, and the velocity defect
   through its **sum over the run** (`d2sum`: `Σ |d₂| ≤ 1/4`, measured `0.2404`) times the **peak of
   the tail** of the `e₁` response (`env_tail_l1`; `P1c = 0.0557`). With the vertical `7.9` mm the 3D
   error is `≤ 0.077`, the target is at `w'` within `10⁻³`, so the vehicle is within `0.078 ≤ 0.099`
   and the completion fires on the next tick: `Tc ≤ 2200 + 416 + 1 = 2617`. `Mc = 416` is the
   smallest checkpoint (multiple of 32) above the smallest closing one, 384 (`0.087`); 352 gives
   `0.0983 > 0.098`. Through the plain envelope `8·10⁻⁴ · T1(Mc)` the velocity defect alone would be
   `0.047` at `Mc = 416` (against `0.0139`): the slow mode of the velocity integrator (`λ ≈ 0.99958`) keeps `T1` above
   22 until 2000 ticks.
5. **Loiter** (`loiter_near`): within `0.081` of `w'`.
6. **The hold** (`err_hold`, `hold_3d`): from `Tl + Mt`, `Mt = 1728`, to 6000, `err ≤ 0.0166`
   (horizontal `0.0097` per axis: `0.0017 + 0.0006 + ¼·0.0186 + 0.0002 + 0.0025`; vertical `0.0092`),
   the same decay with the velocity defect through its sum and the peak tail `P1 = 0.0186`. Through
   the plain envelope (`8·10⁻⁴ · T1(1984) = 0.018` per axis) the hold would need `Mt ≈ 4300`
   (extrapolated with the slow mode) and the window would not fit in 4800 ticks.
7. **Assembly**: the window starts at `Tl + 1728 ≤ 2617 + 450 + 1728 = 4795 ≤ 4800`; on it
   `‖p − w'‖ ≤ 0.0166 + 0.081 = 0.0976 ≤ 0.1` (margin 2.4 mm). `eventually` stays at 4800.
8. **The certified gains** (`refGains_certified : RefGains`). The direction gains are the
   per-coordinate gains of the transposed models (`resp Aᵀ D m j = (Aᵐ D)ⱼ`, `resp_transpose`);
   `Nominal.gain_assemble` on `Âᵀ` with the initial vector `S · D` certifies them (forward
   trajectories of `B_h` and `vAcc`, 4096 ticks, and `B_v`, 2048 ticks, chunks of 32, Neumann tails
   with `Mnᵀ`). Certified: `B_h`: `e 0.0300, ev 0.1654, I 0.0389, c₁ 2.2373`; `vAcc`: `c₁ 60.542`;
   `B_v`: `0.1161, 0.2902, 0.0505, 0.0675, 0.0792`. The jerk gain of the command rate is the `c₁`
   gain of `B_h` one tick later (`rate_shift`). The tails are the certified states `A^{416} D`,
   `A^{1728} D` (`round_err` at the checkpoints 13 and 54, `stateAt`) weighted by the certified
   `GH 0`, `GV 0` (`tail_of_state`) or `PH 0` (`peak_of_state`): `TBc = 0.01679`, `T0c = 92.8`,
   `P1c = 0.05575`; `TB = 0.001118`, `T0 = 4.81`, `P1 = 0.0186`; `TBV = 0.002173`, `TV0 = 5.49`,
   `TV1 = 0.475`.

### 9.3 `LegFacts`: the fields, measured against assumed

`LegFacts sense32 senseP w₀ p₀ w' ψ₀` has one field, `run : ∀ x ∈ Mloop ∩ Ahover p₀ ψ₀,
LegRun w₀ (wpt w') x`; `LegRun` has `init`, `tick`, `d2sum`, `phase`. Measured values: the
coordinator's horizontal campaign (204 legs from hover, 0.2–3.6 m, 6 directions, headings
0/90/180/−45°, altitudes 0.5–3 m, `staging/text/reach-legs-campaign.csv`,
`reach-legs-defects.csv`), read per tick from the flight traces (scratchpad `leg3/traces.py`,
`phases.py`); every assumed number is at least 2 % above the measured one. Phases as measured: `Te`
the first tick with the target at `w'` (`10⁻³`) and its velocity and acceleration `≤ 10⁻⁷`; `Tc` the
last tick before the loiter S-curve moves the target; `Tl` the first tick from which the target is
constant and its velocity and acceleration are `≤ 5·10⁻⁷`.

| field | assumed | measured (max over the campaign) | status | discharge |
|---|---|---|---|---|
| `init` | readouts at tick 2 within `ε0VL`, `ε0HL`; `|asp| ≤ 10⁻³`; **`|d₂| ≤ 10⁻⁶`** (new) | `|asp| ≤ 4.9·10⁻⁵`, `|d₂| ≤ 7.5·10⁻⁸` (`1.2·10⁻⁷` on the 3D campaigns); readouts: horizontal `e ≤ 2.2·10⁻¹⁰`, `ev ≤ 1.5·10⁻⁷`; vertical **`ev 4.90–5.03·10⁻⁶`, `eA ≈ 2.34·10⁻⁴`** (the trim sink, finding 11), `w 4.45·10⁻⁵` | was **false** (vertical `ev`, `eA`); repaired 2026-11-06 (`10⁻⁵`, `2·10⁻³`) | C16: takeover, `ModeAuto::init`, `mission_start` |
| `tick` rows | `legWV ≤ εVL`, `legWH ≤ εHL` while `BoxL` holds; **`BoxL` widens `|e|` to `0.15`** | tracking `≤ 0.0419`; rows not observable in the trace | as before; the wider box is inside `NERegion` (`‖e‖ ≤ 0.4`) | `ne_glue`, `vglue`, M4 `attitude_tracks` |
| `tick` horizontal reference | `|asp| ≤ 1.501`, `|Δasp| ≤ 0.013`, `|d₁| ≤ 1.3·10⁻⁴`, **`|d₂| ≤ 8·10⁻⁴`** (was `1.3·10⁻⁴`), **`|Δd₂| ≤ 1.1·10⁻⁵`** (new) | `1.5000003`, `0.0125`, `1.258·10⁻⁴`, **`7.68·10⁻⁴`**, `1.007·10⁻⁵` | `d₂` was **false**; now holds | S-curve tables, the scaler |
| `tick` vertical reference | `|aZ| ≤ 0.5`, `|d₁Z| ≤ 10⁻⁵`, **`|d₂Z| ≤ 2·10⁻⁵`** (was `10⁻⁵`) | `0.028`, `2.4·10⁻⁶`, **`1.89·10⁻⁵`** (the loiter's vertical move) | `d₂Z` was **false**; now holds | S-curve tables |
| `d2sum` (new) | `Σ_{t<hzn} |d₂| ≤ 1/4` per axis while the box holds | `0.2404` (whole recorded run; held target after it, `≤ 10⁻⁸`/tick) | holds | S-curve tables + the scaler along the run |
| `phase.c`, `phase.legH` | **removed** (unused after the repair) | `legH`'s `d₂` was false (`7.68·10⁻⁴` against `1.3·10⁻⁴`) | — | — |
| `phase.order` | `2 ≤ Tc ≤ Tl ≤ Tc + 450` (was `400`) | `Tl − Tc ≤ 436` (0.2 m legs; `434` on the 3D campaign) | was **false**; now holds | loiter S-curve tables |
| `phase.legV` | before completion `|aZ| ≤ 10⁻³`, `|d₁Z| ≤ 10⁻⁸`, `|d₂Z| ≤ 10⁻⁷` | exactly 0 | holds | navigator run invariant (§9.6) |
| `phase.hold` | from `Tl`: target constant, velocity and acceleration `≤ 10⁻⁶` | `1.0·10⁻⁸`, `4.9·10⁻⁷` | holds | `tick_hold_ps` |
| `phase.arrive` | **`Te ≤ 2200`** (was 2400, "target within 1 mm"); **on `[Te, Tc)`: target within `10⁻³` of `w'`, `|asp| ≤ 10⁻⁶`, `|d₁| ≤ 10⁻⁸`, `|d₂| ≤ 3·10⁻⁶`** (new); the completion test | `Te ≤ 2107` (3.6 m), `Tc − Te ≤ 1`; on `[Te, Tc)`: `8.6·10⁻⁷`, `1.0·10⁻⁷`, `2.2·10⁻¹⁰`, `8.6·10⁻⁸` | holds (the old form held but no longer suffices) | S-curve tables, `reached_destination` |
| `phase.atComplete` | `dist + ‖v‖ ≤ 0.08` at `Tc` | `0.0554` (`0.0698` on the 3D campaign) | holds | certified nominal of the leg family (open) |
| `phase.loiter` | loiter point within `dist + ‖v‖ + 10⁻³` | within the bound minus `0.0012` | holds | `loiter_dest_bound` (box variant) |

**Measured against proved** (horizontal campaign): at the completion check (`Te + 416`) the 3D error `≤ 0.077` (the campaign
completes within one tick of `Te`); completion `Tc ≤ 2108` against `≤ 2617`; final distance
`0.0341` against `0.0976`; box: command `2.92` (course MC) against `3.005`, command change
`0.0286` against `0.0462`.

### 9.4 Findings

1. **The time warp of the S-curve is a reference defect.** `advance_wp_target_along_track`
   advances the S-curve clock by `_track_dt_scalar · dt` but feeds the velocity and acceleration
   targets unscaled: `d₁ ≈ (s − 1) h |v_T|`, `d₂ ≈ (s − 1) h |a_T|`. Their ℓ1 gains into the
   position error are 272 and 74 per unit; the raw scaler `≥ 0.9` of the first brief does not bound
   the tube.
2. **The completion state cannot come from envelopes** (0.059 m, 0.19 m/s at the S-curve end; 0.105
   for the stopping-point combination): `atComplete` is a field.
3. **The first brief's budget was inconsistent with `loiter_dest_bound`** (`d + |v|`): the theorem
   uses `d + |v| ≤ 0.08`.
4. **Float limits**: acceleration `1.5000003`, speed `1.0000002`: envelopes `1.501`, jerk `0.013`.
5. **`clock` was likely false at the leg start** (raw scaler `≈ 0.05 − 0.5 τ` while the vehicle is at
   rest and `|v_T|` small): replaced by `arrive`.
6. **`AxiomCheck.lean`**: imports precede declarations, so one import line was inserted after the
   last import and the `#print axioms` block appended.
7. **(2026-11-06) The velocity defect is six times the assumed bound.** `d₂ = vsp' − vsp − h·asp`
   reaches `7.68·10⁻⁴` per tick (`(1 − s)|a_T| = 0.307` m/s², not `0.046`), exceeds `1.3·10⁻⁴` for up
   to 498 ticks per leg, early in the acceleration, in the deceleration and in the loiter S-curve.
   `legH` and `TickBounds` were false on every leg ≥ 0.2 m; the theorem of 2026-11-05 was vacuous.
   Treated as an arbitrary sequence bounded by `8·10⁻⁴`, the defect breaks INDUCTION's box (position
   error `0.143`, command `4.14`, command rate `0.055`) and, through the slow mode of the velocity
   integrator, any decay shorter than about 4000 ticks. What the code's defect has that an arbitrary
   one does not, and what the repair uses: it is **smooth** (`|Δd₂| ≤ 1.007·10⁻⁵` per tick, so the
   rate closes in `ζ₂`) and **summable** (`Σ |d₂| ≤ 0.2404` per axis over the run, so its old part
   counts through the peak of the tail, not the ℓ1 tail).
8. **(2026-11-06) The loiter S-curve lasts up to 436 ticks** (0.2 m legs, a loiter move of
   `0.034` m with jerk 5): `order`'s `Tl ≤ Tc + 400` was false; now `450`.
9. **(2026-11-06) The vertical velocity defect in the loiter reaches `1.89·10⁻⁵`**: `TickBounds`'s
   vertical `d₂ ≤ 10⁻⁵` was false; now `2·10⁻⁵`.
10. **(2026-11-06) The S-curve "stops" before it finishes.** At `|vsp| < 10⁻⁶` the target
    acceleration is still `2·10⁻⁴`; the S-curve finishes (all targets 0) about 8 ticks later, and the
    completion fires on the next tick. `arrive` now names the finished S-curve (`Te ≤ 2200`,
    measured `2107`) and the reference at rest from `Te` to the completion.

11. **(2026-11-06, second repair) The start fact was false.** `LegRun.init` asked the vertical
    readouts at tick 2 within INDUCTION's `ε0V`, whose velocity entry is `10⁻⁶` and whose
    acceleration-PID entry is `10⁻⁵`. Every run of the three campaigns has the vertical velocity
    error `4.90–5.03·10⁻⁶` at tick 2: `MOT_THST_HOVER 0.4444` (`0.44440001` as `float`) against the
    plant's hover fraction `1/2.25` is a thrust deficit of `10⁻⁴`, a sink of `9.80·10⁻⁴` m/s² from
    tick 0 (`az_d = −9.80567` in the traces from tick 1), so `|ev| = 2h · 9.8·10⁻⁴`; the 20 Hz error
    filter of the acceleration PID (`α = 0.239`) holds `2.34·10⁻⁴` of the sampled sink (computed; not
    logged). The theorems of 2026-11-06 morning were vacuous through `init`. `ε0VL` (LegTube.lean) now
    has `10⁻⁵` and `2·10⁻³` in these entries; the horizontal start `ε0HL` and the bounds `|asp| ≤ 10⁻³`,
    `|d₂| ≤ 10⁻⁶` were rechecked and hold with margin (measured `e 2.2·10⁻¹⁰`, `ev 1.5·10⁻⁷`, commands
    `2.3·10⁻⁵`; `7.6·10⁻⁵`, `1.2·10⁻⁷`). Budgets that read the start, before → after: box vertical
    `ez 0.073285 → 0.073290`, `ev 0.174765 → 0.174782`, `I 0.028431 → 0.028433`,
    `f 0.038061 → 0.038070`, `u 0.044226 → 0.044305` (box `0.1, 0.5, 0.5, 0.12, 0.12`); `τz 0.0077628 →
    0.0077679`; the vertical tube on the leg `vzL 0.0078956 → 0.0079007`, its lemma `vzL_le` from `7.9`
    to `7.91` mm; the completion check `√(2·0.054² + vzL²) ≤ 0.0768 ≤ 0.077` (unchanged statement);
    the vertical hold `vT 0.0092063 → 0.0092115`, `vT_le` from `0.00921` to `0.00922`; the hold
    `0.01653 → 0.01654 ≤ 0.0166` (unchanged); the final distance `0.0166 + 0.081 = 0.0976` unchanged.
    The horizontal budgets (`τe`, `hC`, `hT`) do not read `ε0VL` and are unchanged. Statements
    unchanged. INDUCTION's own `ε0V` (Induction/Inv.lean, the hover glue) has the same two entries and
    was not touched here.

### 9.5 Discharged after milestone 5

* `gains`: certified (`refGains_certified`), removed from `LegFacts`.
* `loiter`: inside the box (`LegFactsBox`, `waypoint_reach_h_box`).

### 9.6 The navigator's `phase` sub-fields from the code (not removed)

Each needs a **per-tick navigator invariant along the run** (INDUCTION's open `NavInv`/`nav_step`:
the leg's S-curve state of `run w₀ x t` is the one `mission_start` built, with only its time
advanced, and the targets the tick hands to `set_pos_vel_accel_NED_m` are its evaluation).
`navW_steady` (TickGlue) splits one tick and `move_from_near` (NavLeg) bounds one advance's
position; nothing carries the leg's segment table, origin and destination from tick to tick.

1. **`legV`**: the vertical targets are `u_z · (P, V, A)`; with `hmin` the bound holds (§9.3), but the
   run invariant is missing.
2. **`arrive`**: the duration half needs the S-curve tables at the code's parameters (snap
   `≈ 39.27`, jerk 5) and the scaler (P-1 needs along-track errors from a nominal); evaluating the
   translated `SCurve.calculate_track` in the interpreter fails (`CppLibm.fmodf` has no interpreter
   implementation). The completion half is two consecutive ticks of the run.
3. **`order`**: the loiter S-curve's duration (tables) after `loiter_start`, and the first ticks.
4. **`d2sum`, `Δd₂`**: the analogue of `move_from_near` for the velocity and acceleration
   targets, and the scaler for the defects (the scaler is a feedback of the along-track errors:
   `1 − s ≈ (kP e_track + lag − 0.05 |v_T|)⁺ / |v_T|`; a discharge of the sum and of the smoothness
   needs the closed loop with the scaler, not an envelope).

## 10. The 3D leg theorem at `PSC_D_ACC_P 0.25`

Files `Contracts/Track/VerticalHi.lean` (the vertical model at the new gain), `VerticalHiCertData.lean`
and `VerticalHiCert.lean` (its Lyapunov certificate), `Contracts/Track/Reach/Leg3GainV.lean`
(the per-coordinate ℓ1 and peak gains `GVH`, `PVH`, generated by `leg3/hi/gen_gainv_hi.py`),
`Leg3GainsData.lean` (generated by `gen_lean_B.py`) and `Leg3Gains.lean` (`refGains3_certified`),
`Leg3Tube.lean` (the 3D box and tubes), `Leg3.lean` (the facts, the parameters, the statement),
`Leg3Nav.lean`, `Leg3Hold.lean`, `Leg3Box.lean`. All sorry-free; all 265 theorems depend only on
`propext`, `Classical.choice`, `Quot.sound` (AxiomCheck.lean, last block). Build:
`LEAN_NUM_THREADS=1 lake build Contracts.Track.Reach.Leg3Box` (`Leg3GainV` about 150 s and
`Leg3GainsData` about 170 s of kernel checks). The horizontal theorem (§9) and the mission
theorem are untouched by the world change: the 3D theorem is about the world with
`PSC_D_ACC_P 0.25` (`LegParams3`).

### 10.1 The statement

```lean
theorem waypoint_reach (sense32 : ℝ → Float32) (senseP : ℝ → Float) (w₀ : Vehicle.World)
    (p₀ : P3) (w' : AC_WPNav_lib.Vector3p.State) (ψ₀ : ℝ) (hP : LegParams3 w₀)
    (hmin : 1 / 100 ≤ dist p₀ (wpt w')) (hR : dist p₀ (wpt w') ≤ 36 / 10)
    (hW : ReachWorld w₀ w') (hS : Plant.CopterSense sense32 senseP) (hL : LibmSpec)
    (hF : LegFacts3 sense32 senseP w₀ p₀ w' ψ₀) :
    Mloop sense32 senseP w₀ ⊨
      ⟨Ahover p₀ ψ₀, lang_t 0 (.eventually 0 6000 (.always 0 1200 (near (wpt w') (1 / 10))))⟩
```

Companions: `waypoint_reach_nonvacuous` (Leg3.lean) and `waypoint_reach_box` (Leg3Box.lean, the
loiter target from `loiter_dest_bound` inside `|p₀ i| ≤ 1.5`, `|w' i| ≤ 1.9`, via the new
`Leg.loiter_of_code'`). `hZ` is dropped; `LegParams3` is `LegParams` with the vertical part `DPar3`
(`CtrlV.DPar2` with `PSC_D_ACC_P = 0.25`). **The `eventually` bound is 6000, not 4800** (REACH-plan
§2): the hold does not fit in 4800 ticks (10.2, item 5). Radius `0.1` kept.

### 10.2 The proof

1. **The vertical model at the new gain** (`VerticalHi`): `rowU` and `B_v` with `kpAcc = 1/4`.
   Spectral radius `0.99901` (it was `0.99744` at `0.05`): the stiffer acceleration loop makes the
   integrator's mode slower, not faster (the plan expected `λ_v` to improve). Lyapunov certificate
   `λ = 0.9995` (Stein at `0.9993`, `R = 181`), kernel-checked like `VerticalCert`. Per-coordinate
   gains (5 adjoint trajectories, 4096 ticks, Neumann tails with `|A^2048| ≤ Mn`), e.g.
   `GVH 0 = (401, 88.5, 12.8, 0.637, 801, 30.7, 0.962, 4.42)`. Direction gains of `B_v`:
   `ez 0.0434, ev 0.0642, I 0.0453, f 0.0565, u 0.3407`.
2. **The box** (`leg_box3`): horizontal as §9 (`bHL`); vertical `bV3 = (0.2, 0.5, 0.5, 0.12, 0.12)`:
   `ez` `0.173` (the vertical defects `1.3·10⁻⁴ · 401 + 8·10⁻⁴ · 88.5 = 0.123` alone exceed INDUCTION's
   `0.1`; the vertical controller's region asks `E ≤ 1`), `ev 0.250`, `I 0.063`, `f 0.082`; the
   throttle `u` through the plain envelope is `0.34 + …` (the feed-forward `kpAcc αA` of a 1 m/s²
   target), so it closes in `ζ = ξ − asp_z • vAccV` with `vAccV = (0, 0, 0, 0, 1, −1, −1, −1)/amax`
   (`Av_vAccV : A_v vAccV + B_v = vAccV`): `|u| ≤ 1.014/amax + 0.054 = 0.0995 ≤ 0.12`.
3. **Completion** (`tail_e_c3`, `tail_z_c3`, `complete3_3d`, `Tc_le3`): `Te ≤ 2200`; at `Te + 704`
   per horizontal axis `0.054` (tails past 416, §9) and vertically `0.0514`
   (`1.001 · 0.02234 + 1.3·10⁻⁴ · 70.55 + ¼ · 0.0502 + 0.0003 + τz 0.0070`): 3D `0.0921 ≤ 0.098`, so
   `Tc ≤ 2905`.
4. **Loiter**: within `0.081`.
5. **The hold** (`err_hold3`, `hold3_3d`): from `Tl + 2624`: horizontal `0.0097` per axis (tails
   past 1728, §9), vertical `0.0122` (`1.001 · 0.004256 + 1.3·10⁻⁴ · 1.10 + ¼ · 0.00218 + 0.0003 +
   τz 0.0070`): `0.0184`. The vertical `B_v` tail (`0.0094` past 1728, `0.0043` past 2624) is the
   binding term: the slow vertical mode. With `◇_[0,4800]` the window would have to start by
   `4800`, so `Mc3 + Mt3 ≤ 2149`, against `Mc3 ≥ 608` for the completion and `Mt3 ≥ 2496` for the hold budget `0.019`.
6. **Assembly**: `Tl + 2624 ≤ 2905 + 450 + 2624 = 5979 ≤ 6000`; on the window
   `‖p − w'‖ ≤ 0.0184 + 0.081 = 0.0994 ≤ 0.1` (margin 0.6 mm); horizon `6000 + 1200 = 7200`.

### 10.3 `LegFacts3`: the fields, measured against assumed

Measured: the coordinator's 3D campaign at `PSC_D_ACC_P 0.25` (426 legs,
`reach-legs3d-campaign.csv`, `reach-legs3d-defects.csv`), read per tick from the traces
(scratchpad `legs3d/`, `leg3/traces.py`, `phases.py`, `sums3.py`). No direction witness, no
c-scaling: per-axis bounds (the coordinator's decision). In 3D the S-curve's along-track
acceleration reaches `1.732 |u_a|` per axis (`|a_a|/|u_a|` measured `1.7320511` on 30° legs): a
c-scaled `1.501 c_a` (or `1.001 c_z`) bound would have been false.

| field | assumed | measured (max, 3D campaign) | discharge |
|---|---|---|---|
| `init` | readouts within `ε0`; `|asp_a|, |asp_z| ≤ 10⁻³`; `|d₂| ≤ 10⁻⁶` | `|asp| ≤ 1.6·10⁻⁴` (ticks 0–3, all axes), `|d₂| ≤ 1.1·10⁻⁷` | C16 |
| `tick` rows | `legWV3 ≤ εVL3` (`u` row `4·10⁻⁶`), `legWH ≤ εHL`, while `BoxL3` holds (vertical `|ez| ≤ 0.2`) | the code's `βcode` at `E = 0.21`, `kpAcc = 0.25`: `u 3.89·10⁻⁶`, `eA 3.88·10⁻⁶`, `eV 1.12·10⁻⁷` (computed, not a trace) | `vglue`, `ne_glue`, M4 |
| `tick` horizontal reference | per axis `1.501`, `0.013`, `1.3·10⁻⁴`, `8·10⁻⁴`, `Δd₂ ≤ 1.1·10⁻⁵` | `1.5000002`, `0.0125`, `1.258·10⁻⁴`, `7.68·10⁻⁴`, `1.007·10⁻⁵` | S-curve tables, scaler |
| `tick` vertical reference | `1.001`, `0.013`, `1.3·10⁻⁴`, `8·10⁻⁴` | `1.0000001` (`WP_ACC_Z 1`), `0.0125`, `6.9·10⁻⁵`, `4.0·10⁻⁴` | S-curve tables |
| `d2sum` | per axis `≤ 1/4` | horizontal `0.2389`, vertical `0.1134` | S-curve + scaler along the run |
| `order` | `Tl ≤ Tc + 450` | `434` | loiter S-curve tables |
| `hold` | velocity and acceleration targets `≤ 10⁻⁶` from `Tl` | `4.2·10⁻⁸`, `4.9·10⁻⁷` | `tick_hold_ps` |
| `arrive` | `Te ≤ 2200`; on `[Te, Tc)` target within `10⁻³`, all three axes at rest (`10⁻⁶`, `10⁻⁸`, `3·10⁻⁶`); completion test | `Te ≤ 2105`, `Tc − Te ≤ 1`; `8.6·10⁻⁷`; `1.0·10⁻⁷`, `2.2·10⁻¹⁰`, `8.6·10⁻⁸` | S-curve tables, `reached_destination` |
| `atComplete` | `dist + ‖v‖ ≤ 0.08` at `Tc` | `0.0698` | certified nominal (open) |
| `loiter` | within `dist + ‖v‖ + 10⁻³` | within the bound | `loiter_dest_bound` (box variant) |

**The two numbers that were not measured before are now measured**: the velocity defect `d₂`
(`7.68·10⁻⁴` per tick, horizontal; `4.0·10⁻⁴` vertical) and its change per tick (`1.007·10⁻⁵`),
with the sums over the run; and the phase ticks (`Te`, `Tc`, `Tl`) from the traces instead of the
target's first arrival.

**Measured against proved**: first entry `≤ 4.32` s (`1727` ticks) against the window start
`≤ 5979`; final distance `≤ 0.0348` against `0.0994`; vertical tracking `0.0304` against the box
`0.2`; throttle (not logged) against `0.0995`.

### 10.4 Findings

1. **The vertical loop at `PSC_D_ACC_P 0.25` is slower in its slowest mode** (`0.99901` against
   `0.99744`): the tails of the vertical responses decide the hold, and the theorem needs
   `◇_[0,6000]`, not `◇_[0,4800]`.
2. **The throttle's ℓ1 gain to the vertical target acceleration is `0.34`** at the new gain (the
   feed-forward through `kpAcc`): the box `|u| ≤ 0.12` closes only in the shifted coordinates.
3. **The vertical position error needs a box of `0.2`** for the plain envelopes of the vertical
   defects; the rows are rechecked at that magnitude.
4. **c-scaled reference bounds are false in 3D** (`1.732 |u_a|`).
5. **(2026-11-06) The start fact was false** (as §9.4, finding 11): `LegRun3.init`'s vertical
   velocity entry `10⁻⁶` against `5.03·10⁻⁶` measured (the trim sink `9.80·10⁻⁴` m/s² of
   `MOT_THST_HOVER 0.4444` against `1/2.25`), the acceleration-PID entry `10⁻⁵` against `2.34·10⁻⁴`
   computed; repaired through `ε0VL` (`10⁻⁵`, `2·10⁻³`). The rechecked `init` bounds `|asp_a|, |asp_z| ≤
   10⁻³`, `|d₂| ≤ 10⁻⁶` hold (`7.6·10⁻⁵`, `7.0·10⁻⁵`, `1.2·10⁻⁷`). Budgets before → after: box vertical
   `ez 0.173403 → 0.173407`, `ev 0.249839 → 0.249863`, `I 0.062770 → 0.062771`,
   `f 0.081509 → 0.081541` (box `0.2, 0.5, 0.5, 0.12`), throttle `u 0.099593 → 0.099977 ≤ 0.12`;
   `τz3 0.0069995 → 0.0070037`; completion `vC3 0.0513529 → 0.0513571 ≤ 0.0514`, 3D `0.09203 ≤ 0.0921`
   (unchanged); hold `vT3 0.0122142 → 0.0122185 ≤ 0.01222` (margin `1.5·10⁻⁶`), `0.018378 → 0.018381 ≤
   0.0184`; the final distance `0.0184 + 0.081 = 0.0994` unchanged, the 0.6 mm margin kept. No
   constant of the 3D files changed; the statement is unchanged.

## 11. The safety theorem

Files `Contracts/Track/Reach/SafeRule.lean` (the invariant rule on histories), `Safe.lean` (the
horizontal-leg world of §9 and the shared horizontal axis), `Safe3.lean` (the 3D world of §10). All
sorry-free; the 33 theorems depend only on `propext`, `Classical.choice`, `Quot.sound` (or fewer)
(AxiomCheck.lean, last block; checked with a scratch file importing `Safe3`). Build:
`LEAN_NUM_THREADS=1 lake build Contracts.Track.Reach.Safe3` (about 45 s for the three files once
`Leg3Box`'s dependencies are built: 14 s, 18 s, 12 s).

### 11.1 The statements

```lean
def track (δ : ℝ) : Formula X := .atom fun x => δ - dist (pos x) (posTarget x)

theorem tracking_safe_h (sense32 senseP w₀) (p₀ : P3) (w' : Vector3p.State) (ψ₀ : ℝ)
    (hP : LegParams w₀) (hW : ReachWorld w₀ w') (hS : Plant.CopterSense sense32 senseP)
    (hL : LibmSpec) (hF : TrackFacts sense32 senseP w₀ p₀ ψ₀) (T : ℕ) :
    Mloop sense32 senseP w₀ ⊨ ⟨Ahover p₀ ψ₀, lang_t 0 (.always 0 T (track δH))⟩   -- δH = 0.2156

theorem tracking_safe (sense32 senseP w₀) (p₀ : P3) (w' : Vector3p.State) (ψ₀ : ℝ)
    (hP : LegParams3 w₀) (hW : ReachWorld w₀ w') (hS : Plant.CopterSense sense32 senseP)
    (hL : LibmSpec) (hF : TrackFacts3 sense32 senseP w₀ p₀ ψ₀) (T : ℕ) :
    Mloop sense32 senseP w₀ ⊨ ⟨Ahover p₀ ψ₀, lang_t 0 (.always 0 T (track δ3))⟩    -- δ3 = 0.2668
```

and the unbounded forms `tracking_safe_h_forever`, `tracking_safe_forever` (guarantee
`lang (track δ)`, every tick). The atom is untimed: `posTarget` is the target the controller writes
at the tick, part of the state `X` (it is `errLE δ` of the specification). `hP`, `hW`, `hS`, `hL`
are the context of the fields and are not used by the proof. Nonvacuity: `Mloop ∩ Ahover p₀ ψ₀`
is nonempty (`waypoint_reach_nonvacuous`).

**The horizon is unbounded** (`T` arbitrary). The box induction is uniform in the tick: every gain
it uses is certified for every length `N` (`RefGains`, `RefGains3`, `gainH'`, `gainV'`, `gainVH'`),
and the inductive step at `t₀ + N` needs only the per-tick facts on `[t₀, t₀ + N)`. So the facts are
stated at every tick (`TrackRun.tick` has no horizon; `LegRun.tick` stops at `hzn` only because the
leg formula ends there) and the theorem holds for every `T`. The measured side covers every tick
of every recorded run (up to 7400 ticks on the random campaign); after the loiter the target is
held and the reference limits hold with the defects below `10⁻⁸`.

### 11.2 The proof, as an instance of the invariant rule

1. **The rule on histories** (`implements_always_of_prefix`, SafeRule.lean). The box cannot be a
   family of sets of `X`: the readouts `ξV`, `ξH` read `run w₀ x t`, the controller's world
   reconstructed from all earlier samples, and the box at `t + 1` follows from the box at every
   earlier tick (the ℓ1 envelopes are convolutions over the past), not from the box at `t`. The
   rule `Contracts.STL.implements_always_of_invariant` is therefore applied literally on the
   history state `Hist X` (the states of ticks `0 … τ`): the extended behavior is `hist x τ = pre x τ`,
   `R = histStep Mloop` (one tick of the loop on prefixes: `s'` is the next prefix of a loop behavior
   whose prefix is `s`), `I τ` the prefixes of length `τ` of behaviors from hover on which every such
   behavior has had the box on `[2, τ]`, the base at tick 0, the target `f s.last ≥ 0`. The
   conclusion is transferred back to `X` through `pre_last`. The assumption `Ahover` reads tick 0
   only (`ahover_tick0`), which is what lets `R` be the loop's step without the assumption.
2. **The family** (`SBox`, `SBox3`): `BoxL` (`BoxL3`) and the per-axis position bounds
   `|e_a| ≤ 0.1433` (each horizontal axis), `|ez| ≤ 0.0735` (§9) or `0.1735` (§10).
3. **The inductive step** (`sbox_step`, `sbox3_step`, on the loop `sbox_run`, `sbox3_run`) is the
   step of `leg_box`'s (`leg_box3`'s) strong induction for any `N`, restated on a model without the
   horizon and with the corrected vertical start `ε0VS` (11.4): the horizontal axis (`axis_out`,
   `axis_c1`, `axis_rate`: LegTube's `outH_bound`, `c1_bound`, `rate_bound` on one axis), the
   vertical outputs through `out_le`, the throttle at 0.25 (`u_boundS`: `u_bound` with `ε0VS`).
   The closures with `ε0VS`: `boxVS_close`, `boxV3S_close`, `boxU3S_close` (`u ≤ 0.1000 ≤ 0.12`).
4. **The position bounds** are the plain ℓ1 envelopes at the reference limits:
   horizontally `2.9·10⁻⁶ + 1.501·0.0306 + 1.3·10⁻⁴·272 + 8·10⁻⁴·74.3 + 0.0025 = 0.1432`
   (`posH_close`; the velocity defect `0.059` is the largest term); vertically at 0.05
   `0.0002 + 0.5·0.119 + 10⁻⁵·408 + 2·10⁻⁵·97.1 + 0.0076 = 0.0733` (`posVS_close`), at 0.25
   `0.00006 + 1.001·0.0434 + 1.3·10⁻⁴·401 + 8·10⁻⁴·88.5 + 0.0069 = 0.1734` (`posV3S_close`).
5. **The target inclusion** (`err_le_of_sbox`, `err_le_of_sbox3`, `norm3_le`):
   `err = √(e₀² + e₁² + ez²)` (`err_eq`), so `err ≤ √(2·0.1433² + 0.0735²) = 0.21557 ≤ δH = 0.2156`
   and `err ≤ √(2·0.1433² + 0.1735²) = 0.26678 ≤ δ3 = 0.2668`. From the box sizes alone it would be
   `√0.055 = 0.2345` and `√0.085 = 0.2916`.
6. **Ticks 0 and 1** (before the tube starts at `ts = 2`): the field `early`.

### 11.3 δ proved against δ measured

`‖p − sp‖` per tick, over every tick of every run, from the traces' `x_n y_e z_d` and
`sp_n sp_e sp_d` (scratchpad `safe/measure.py`):

| world | δ proved | campaign | runs | measured max | per axis (horizontal, vertical) |
|---|---|---|---|---|---|
| §9, gain 0.05 | `0.2156` | horizontal legs (`hlegs`) | 204 (200 ref, 4 Lean) | `0.04187` | `0.04186`, `0.00155` |
| §10, gain 0.25 | `0.2668` | 3D legs (`legs3d`) | 426 (420 ref, 6 Lean) | `0.04181` | `0.04180`, `0.03038` |
| §10, gain 0.25 | `0.2668` | random legs (`legsrand`) | 320 (300 ref, 20 Lean) | `0.04271` | `0.04215`, `0.03006` |
| (§9 gain) | — | course flight (`ref-course-1ms`) | 1 | `0.08704` | `0.02999`, `0.08477` |

The course flight is **not covered** by either theorem: it starts on the ground (not `Ahover`) and
its navigator limits exceed `TrackFacts`'s (horizontal acceleration `2.12` per axis, vertical
acceleration `1.0` and defects `1.4·10⁻⁴`, `7.4·10⁻⁴` against §9's `0.5`, `10⁻⁵`, `2·10⁻⁵`); its
vertical error `0.0848` is above §9's vertical bound `0.0735`, which is consistent: §9's bound is for
a vertical reference that hardly moves. The proved δ is five to six times the measured maximum; the
gap is the plain envelope of the velocity defect (`0.059` per horizontal axis against `|e| ≤ 0.042`
measured), the price of a bound that holds at every tick of every reference within the limits.

### 11.4 `TrackFacts`, `TrackFacts3`: the fields, assumed against measured

Per behavior (`TrackRun`, `TrackRun3`): `early`, `init`, `tick`. No navigator phase, no completion,
loiter or hold, no `d2sum` (the box does not use it). Measured: every tick from 2 on of every run
(scratchpad `safe/refs.py`, `safe/init.py`, `safe/initw.py`, outputs `safe/refs.out`); 3D columns
over `legs3d` and `legsrand`.

| field | assumed | measured §9 (`hlegs`) | measured §10 (`legs3d`, `legsrand`) |
|---|---|---|---|
| `early` (ticks 0, 1) | `err ≤ 10⁻⁶` | `4.1·10⁻⁹` | `1.22·10⁻⁷` |
| `init` vertical `ez` | `10⁻⁶` | `1.4·10⁻⁸` | `1.32·10⁻⁷` |
| `init` vertical `ev` | **`10⁻⁵`** (`ε0VL` before the repair: `10⁻⁶`) | `4.90·10⁻⁶` | `5.03·10⁻⁶` |
| `init` vertical `eA` | **`2·10⁻³`** (`ε0VL` before the repair: `10⁻⁵`) | `2.34·10⁻⁴` (computed) | `2.34·10⁻⁴` (computed) |
| `init` vertical `w` | `10⁻⁴` | `4.43·10⁻⁵` | `4.45·10⁻⁵` |
| `init` vertical `eV, I, f, u` | `10⁻⁵, 10⁻⁴, 10⁻⁴, 10⁻⁴` | not logged (estimated `1.8·10⁻⁷`, `4.4·10⁻⁵`, `4.4·10⁻⁵`, `≤ 4.4·10⁻⁵`) | same |
| `init` horizontal `e, ev` | `10⁻⁶`, `10⁻⁶` (`ε0HL`) | `1.4·10⁻¹⁰`, `9.2·10⁻⁸` | `2.1·10⁻¹⁰`, `1.4·10⁻⁷` |
| `init` `|asp|`, `|asp_z|` (3D), `|d₂|` | `10⁻³`, `10⁻³`, `10⁻⁶` | `4.9·10⁻⁵`, —, `7.5·10⁻⁸` | `7.6·10⁻⁵`, `7.0·10⁻⁵`, `1.17·10⁻⁷` |
| `tick` `|asp|` | `1.501` | `1.5` (configured max) | `1.5` (configured max) |
| `tick` `|Δasp|` | `0.013` | `0.0125003` | `0.0125003` |
| `tick` `|d₁|` | `1.3·10⁻⁴` | `1.2583·10⁻⁴` | `1.2585·10⁻⁴` |
| `tick` `|d₂|` | `8·10⁻⁴` | `7.6813·10⁻⁴` | `7.6819·10⁻⁴` |
| `tick` `|Δd₂|` | `1.1·10⁻⁵` | `1.0070·10⁻⁵` | `1.0402·10⁻⁵` (`legsrand`) |
| `tick` vertical `|asp_z|` | §9 `0.5`; §10 `1.001` | `0.0282` | `1.0` (configured max) |
| `tick` vertical `|Δasp_z|` (§10) | `0.013` | — | `0.0125002` |
| `tick` vertical `|d₁z|` | §9 `10⁻⁵`; §10 `1.3·10⁻⁴` | `2.44·10⁻⁶` | `6.98·10⁻⁵` |
| `tick` vertical `|d₂z|` | §9 `2·10⁻⁵`; §10 `8·10⁻⁴` | `1.889·10⁻⁵` | `4.017·10⁻⁴` |
| `tick` rows | `legWV ≤ εVL` / `legWV3 ≤ εVL3`, `legWH ≤ εHL` while the box holds | not observable (§9.3, §10.3) | not observable |

Every number is at least 2 % above its measured value except the configured maxima `1.5` and
`1.0` (`1.501`, `1.001`, as in §10.3). The random campaign's `|Δd₂| = 1.040·10⁻⁵` (not in §10.3's
`1.007·10⁻⁵`) is within `1.1·10⁻⁵` (5.7 %). `eA` at tick 2 is not logged: it is the code's 20 Hz
filter (`α = 0.2391`) of the acceleration error the controller samples at tick 1, the sink
`|a_z + g| = 9.80·10⁻⁴` m/s² of the traces (`α · 9.80·10⁻⁴ = 2.34·10⁻⁴`; a priori at most the sink
plus the target, `≤ 10⁻³`).

### 11.5 Findings

1. **`LegRun.init` and `LegRun3.init` were false in the vertical start**: the vertical velocity
   error at tick 2 is `4.90–5.03·10⁻⁶` against `ε0VL 1 = 10⁻⁶`, the acceleration-PID error about
   `2.34·10⁻⁴` against `10⁻⁵` (the trim sink, §9.4 finding 11). Repaired the same day: `ε0VL` has
   `10⁻⁵` and `2·10⁻³` there, and `ε0VS = ε0VL` (`ε0VS_eq`); the budgets of §9 and §10 were re-closed
   with unchanged statements (§9.4 finding 11, §10.4 finding 5).
2. **The safety theorem needs no navigator facts**: the box is the whole proof; `d2sum`, the phases,
   the completion and the hold are only for reachability.
3. **The per-axis bounds are tighter than the box**: `0.1433` against `0.15` horizontally, `0.0735`
   against `0.1`, `0.1735` against `0.2` vertically; carried in the invariant family, they give
   `δH = 0.2156` and `δ3 = 0.2668` instead of `0.2345` and `0.2916`.
