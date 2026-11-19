# M9: the induction that proves `track_contract`

This note documents `Contracts/Track/Induction/*.lean`. It covers the final milestone M9 of
TRACK_PLAN.md: the invariant of the closed loop, the induction over the ticks, and `ψtrack` from the
invariant. Every lemma the induction needs from the other milestones is a field of one structure,
`Pieces`. Everything is proved, without `sorry`, from those fields.

```lean
theorem track_contract_of_pieces (sense32 senseP w₀) (P : Pieces sense32 senseP w₀)
    (hM : MissionWorld w₀) (hS : Plant.CopterSense sense32 senseP) (hL : LibmSpec)
    (hE : ClimbEscape sense32 senseP w₀) :
    Mloop sense32 senseP w₀ ⊨ ⟨Atakeoff, lang_t 0 ψtrack⟩
```

`hE` is the escape of the climb (`Mission.ClimbEscape`, Spec.lean), a named hypothesis of
`track_contract` and `mission_contract`. It is validated on the Monte Carlo runs and not proved
(MISSION.md, "The escape of the climb"; VERTICAL.md §9). `Instance.lean` gives `pieces`, the
instance for the mission flight, with the open fields `sorry`, and
`track_contract_proof := track_contract_of_pieces … pieces …`. `Sub.lean`'s `track_contract` is
`track_contract_proof`. The fields are discharged one by one as the other milestones finish.

The finished theorems of the other milestones are used directly:

* M1 `tick_actOK`, M2 `intOK_tick`/`intOK_takeover`, Q5 `mission_in_order` (`Step.lean`);
* M6 `HCtl.horizontal_tick_eq_D` (`Horiz.lean`, `wHβ_bound`);
* M8 `Pacing.pace_of`, `Pacing.rawScaler_ge`, `Pacing.rho_course`, `Pacing.pacing_course`,
  `Pacing.hold_course`, `Pacing.hold_formula` (`Main.lean`);
* the navigator's `loiter_dest_bound`, through `hold_course`.

## 0. Files

| file | content |
|---|---|
| `Run.lean` | `run w₀ x t`: the world before tick `t`. `hidden_run` proves that every witness of `x ∈ Mctrl w₀` has this hidden state and these outputs. The target triples `refAx`, the commands `cmd`/`cmdAgo`, the realized acceleration `aReal`, the attitude-lag state `aLag`, the deviation `etaA`. The code's variables `vabs` (VERTICAL.md §1) and `habs` (HORIZONTAL.md §1), the error coordinates `ξV`, `ξH`. The generic tube lemma `tube_out`. |
| `Inv.lean` | `Iface` (the data of the other milestones), the constants, the nominal `nomV`/`nomH`, the disturbances `wV`/`wHβ`/`wH`, the tubes `ηV`/`ηH`, `Region`, `TubeOK`, `Inv1`, `Inv`, `Pre`, `CmdOK`, `complete`, and the numeric checks (`τV_spec`, `τH_spec`, `εH_spec`, `τ3_spec`, `τ3v_spec`). |
| `Horiz.lean` | the sensing lemmas, `NEGlue` (the tick glue of the horizontal controller), `prow`, `axis_dev` and `wHβ_bound` (the horizontal disturbance from M6's `horizontal_tick_eq_D`) |
| `Vert.lean` | `VGlue` (the tick glue of the vertical join), `wSv`, `βcode_le`, `heldM_succ`, `wV_bound` (the vertical disturbance from the C-series' `vertical_tick_split`) |
| `PlantRow.lean` | `wB_two_le`, `wTA_two_le`, `Cd_two_le`, `prow_step`, `qnorm_one`, `prow_le` (the plant's position row) |
| `Pieces.lean` | `Pieces` (extends `Iface`), `LoiterHyps`, `Beh`, `v3`, `cIdx` |
| `Step.lean` | `world_all`, the tube readings, `err_le`, `smpErr_le`, `vel_bound_of`, `inv_zero`, `tube_succ`, `inv_succ`, `inv_all` |
| `Main.lean` | T1–T6 at a tick (`always_at`, `prox_corner`); the pacing (`sc_bounds`, `pace_run`, `phase_r`, `reach_chain`, `q_leak`, `hold`); `ψtrack_of_inv`, `track_contract_of_pieces` |
| `InitWorld.lean` | `intOK_missionWorld` (`init_world`: the M2 invariant of the booted course world, from `MissionParams`' `kimax` fields) |
| `Instance.lean` | `pieces` (the remaining `sorry`s), `track_contract_proof` |

Build: `lake build Contracts.Track.Induction.Instance`. Each file builds in 8–20 s once its imports
are built.

## 1. The invariant in words

For one behavior `x` of the closed loop from `Atakeoff`, `Inv x t` says that `Inv1 x k` holds at
every tick `k ≤ t`. The induction runs over the horizon: `Region` includes `t ≤ 12000`, and
`inv_all` gives `Inv t` for every `t ≤ 12000`. M8's `Pace` is about all ticks, so its sequences are
continued past the horizon by the exact filter (`rE`, `sE`, `qE`, Main.lean). `Inv1 x k` holds when the following hold.

**The world** (`WorldOK`). The stored actuators are in `[0, 1]` (M1, `tick_actOK`). The integrators
are within their limits (M2, `intOK_tick`). From tick 1 on, the mission state machine is in order
(Q5, `MInv`, `mission_in_order`). These hold at every tick without the induction (`world_all`).

**The region `D°`** (`Region`):

* The vertical box `BoxV`:
  * `|ez| ≤ 0.1` (D6);
  * `|ev| ≤ 0.5`;
  * the acceleration integrator deviation `≤ 0.5` (D13);
  * the throttle filter and `_throttle_in` within `0.12` of hover, that is in
    `[0.32, 0.57] ⊂ [0.30, 0.62]` (D8).
* The horizontal box `BoxH`, per axis:
  * `|e| ≤ 0.1`;
  * `|ev| ≤ 0.5`;
  * `|I| ≤ 5` (IMAX 10);
  * the command `|c₁| ≤ 4` (D7);
  * the command rate `|c₁ - c₂| ≤ 0.05` per tick.
* The subsystem invariants of the other milestones:
  * `AttInv` (M4: tilt, rates, actuators in `[0.30, 0.62]`, no saturation flag);
  * `YawInv` (3.8, Y1–Y5);
  * `NavInv` (the navigator: geometry, leg index, S-curve state);
  * `CtrlInv` (the C-series: finite floats, flags, branches).
* **The phase.** The navigator's invariant `NavInv` is per tick. The pacing (T5) is a statement
  about the whole run, proved after the induction by M8's `pacing_course` from the code facts of
  the scaler along the run (`Pace`) and the tubes. It therefore needs no per-tick budget in the
  invariant.

**The tubes** (`TubeOK`). For each channel the error coordinates `ξ` are split as `ξ = ξ̂ + η`.
The nominal `ξ̂` is the linear model's response, from zero, to the actual target sequence of the run
and to the structured disturbance: the tilt coupling and angle boost `wVs` vertically, the heading
coupling `etaHat` horizontally. The deviation `η` is bounded through the watched outputs:
`|outV o ⬝ ηV| ≤ τV o` and `|outH o ⬝ ηH| ≤ τH o`.

**The tube is ℓ1/peak-gain based, not a V-ball.** TRACK_PLAN.md §3.4 proposed a constant-radius
ball in the Lyapunov measure `V`. It does not close. `P_v` and `P_h` are badly conditioned
(cond ~10⁵), so an invariant ball of the size of a 3 mm position tube admits per-tick disturbances of
only about `1.7·10⁻⁷`, while the plant remainder alone is about `2.5·10⁻⁵` m/s per tick. VERTICAL.md
§7 already suggests the alternative used here. With `η(t+1) = A η(t) + w(t)` from tick 2,
`tube_out` gives

`|o ⬝ η(2 + N)| ≤ Σⱼ P_oj ε0_j + Σⱼ G_oj ε_j`,

where `P` bounds the peaks and `G` the ℓ1 norms of the responses `o ⬝ Aᵐ eⱼ`, `ε0` bounds `η(2)`,
and `ε` bounds `w` per coordinate. The bounds on `w` come from the C-series pieces at every tick
`2 … t`, so the tube is a statement about the history. That is why `Inv t` is the invariant at all
ticks up to `t`.

## 2. The numbers and their validation

### Disturbance bounds (the C-series targets, per coordinate)

| channel | coordinates | ε (per tick) | ε0 (after tick 2) |
|---|---|---|---|
| vertical `εV` (after `wVs = CtrlV.wS`) | `ez, ev, eV, eA, I, f, u, w` | `1e-10, 2.5e-8, 2e-7, 4e-6, 2e-7, 1e-7, 3.2e-6, 4e-7` | `1e-6, 1e-6, 1e-5, 1e-5, 1e-4, 1e-4, 1e-4, 1e-4` |
| horizontal `εHβ` (controller and plant rows) | `e, ev, E, D, I, a, c₁, c₂, c₃` | `1.8e-7, 0, 3.7e-6, 2.31e-4, 6.2e-7, 0, 1.61e-4, 0, 0` | `1e-6, 1e-6, 1e-5, 1e-4, 1e-5, 1e-5, 1e-4, 1e-4, 1e-4` |
| attitude `εη` (after the structured `etaHat`) | realized minus lag-law acceleration | `0.01` m/s² | |
| horizontal total `εH` | `εHβ + |eAcc| εη` | `2.2e-7, 2.5e-5, 3.7e-6, 2.31e-4, 6.2e-7, 0, 1.61e-4, 0, 0` | |

Notes on the table:

* The vertical rows are the C-series' `βcode` (`CtrlV.vertical_tick_split`) at the region's
  magnitudes, checked by `βcode_le` (Vert.lean): `1.0e-11, 8.3e-9, 1.0e-7, 3.84e-6, 1.28e-7,
  5.1e-8, 3.11e-6, 1.5e-7`. The structured part `CtrlV.wS` goes into the nominal (`wVs`): the
  plant residuals `ρz`, `ρv` (remainder and tilt coupling), the sampled specific force's residual
  `ρam` through the acceleration filter, and the boost's deviation `τ`. The vertical radii `τV`
  are unchanged, so they are now conservative (`G·εV ≈ 0.19` mm).
* The horizontal position row `1.8e-7` is `prow_le` (PlantRow.lean): `a h³ ḋ/12 + r_p − (h/2) r_v`
  from `Plant.step_pv_sharp` at `|ω| ≤ 2`.
* The horizontal controller rows are the bounds `ne_spec` proves (CtrlHorizontalTick.lean),
  plus the sensing difference through `A_h`. M6 reads the sampled position and velocity; `ξH`
  reads the plant state. `axis_dev` proves rows 0 and 1 cancel exactly. Rows 2, 3, 4, 6 gain
  `|A_j0|·10⁻⁹ + |A_j1|·2·10⁻⁷`. The `D` row (2.31e-4) and the command row (1.61e-4) raise the
  position tube from 2.0 to 2.5 mm.
* In the horizontal channel the `ev` row is exact, because `aReal` is the realized mean
  acceleration. The `a`, `c₂`, `c₃` rows are exact by definition (`aLag`, `cmdAgo`).

### Gains

`GV`, `PV`, `GH`, `PH` are the ℓ1 and peak gains of the exact rational models `A_v`, `A_h`, computed
in floating point over 40000/80000 ticks (tails below `10⁻¹⁵`), plus 2 %, rounded up to three digits
(`scratchpad/induction/consts.py`). Proving them is a certificate piece (`peakV`, `gainV`, `peakH`,
`gainH`). It costs one certified free response per input coordinate plus a V-tail, as in
`l1_gain`. Values that matter: `G(ez ← ev) = 97.1` and `G(e ← ev) = 74.3`.

### Tube radii

The radii `τV`, `τH`, `τ3`, `τ3v` are checked from the tables by `norm_num`:

| output | ez | ev | I | f | u |
|---|---|---|---|---|---|
| `τV` | 2.8 mm | 6.3 mm/s | 7.5e-4 | 1e-3 | 1.2e-3 |

| output | e | ev | I | c₁ | c₁−c₂ |
|---|---|---|---|---|---|
| `τH` | 2.6 mm | 4.0 mm/s | 0.015 | 0.022 m/s² | 1.6e-3 m/s² |

From these, the 3D position tube is `τ3 = 4.7 mm` (`√(2·2.6² + 2.8²) = 4.62`) and the 3D velocity
tube is `τ3v = 8.5 mm/s`.

### Pacing

T5 and the hold come from M8's `pacing_course` and `hold_course` (PACING.md). The constants are
theirs:

* windows `a_i`, with gaps ≤ 860, 743, 743, 1450, 743, 743, 750 ticks;
* escape by tick 350;
* `ρLo`, `ρMid`, `ρEnd` from P-1 with along-track errors 0.055 m/s and 0.03 m.

`nom_along` asks the nominal for those along-track errors with the tubes to spare
(`0.055 − τ3v − 10⁻⁴`, `0.03 − τ3 − 10⁻⁴`). PACING.md measures 0.0425 and 0.0216.

Cross-check from this file's Monte Carlo (`scratchpad/induction/newspec.py`, time warp included):

* the vehicle's arrival at `w0` comes at most 679 ticks after tick 0;
* the target's arrival at `w1` comes at most 851 ticks after that;
* every other leg's arrival comes at most 742 ticks (1449 for leg 4) after the previous one.

### Validation against the Monte Carlo

All 256 starts (200 uniform, 56 worst-case) were flown again with `copter_ref` and `--trace`
(`scratchpad/induction/check_ind.py`, `mc_traces.pkl`, `mc_an.py`). Results:

| quantity | measured max | used |
|---|---|---|
| err | 8.77 cm | δ = 9.5 cm; `nom_T1` needs nominal ≤ 9.04 cm |
| rest-gate velocity error | 0.0407 m/s | `nom_rest`: nominal + 8.5 mm/s + 1e-4 ≤ 0.055 |
| actuators | 0.385–0.501 | `[0.30, 0.62]` |
| velocity target, per axis | 0.709 m/s | 1.5 (`nav_bounds`) |
| velocity error, per axis | 0.130 m/s | box 0.5 |
| target coordinate | 2.40 m | 3 (`nav_bounds`) |
| horizontal command | 2.92 m/s² | 4 |
| command change per tick | 0.0286 m/s² | 0.05 |
| vehicle distance to `w0` while the target is within 0.085 | 0.0934 m | `nom_w07`: needs nominal ≤ 0.0954 |
| target distance to `w7` in the loiter | 0.0282 m | hold radius 0.085 |
| max `|dz|` at the corners, target within 0.105 (ideal course) | 0.0131 m | `Bz` = 0.018 with the vertical nominal |

**The corner budget** is in the field `nom_corner`, per corner. See "Open fields", which gives
the formula and the reason only the additive 2.5 mm term is needed. An earlier planar version
closed at 3D 0.0998, and its vertical bound (0.018) was below the measured vertical offset (0.0218).

**Finding: the reach chain at `w0` (fixed in the spec).** With `rPassEnd = 0.09` the conjunct
`reachSeqF (nearT · rPass) legs` was false on 52 of the 256 runs, the nominal flight among them. On
the climb the target's closest approach to `w0` is 0.0433–0.0995 m (0.0942 at tick 737 on
`lean-course-1ms`). No single radius serves both arrival and transfer:

* arrival needs a radius of at least 0.0995 m;
* the transfer `target ≤ R → vehicle ≤ 0.1` needs `R < 0.091`. At `R = 0.09` the vehicle is up to
  0.0994 m from `w0`, which leaves 0.6 mm and no room for the 4 mm tube.

`ψtrack` now starts its reach chain with the vehicle (`◇_[0,1200](near w0 r ∧ …)`), and
`rPassEnd = 0.085`. With these, the chain, the hold and T4 hold on all 256 runs (MISSION.md).

**`corner_transfer` cannot be used as it stands.** It assumes the target within 1 mm of the table
and concludes a planar `≤ 0.1`, which leaves nothing for the 3D distance. The per-corner certified
planar bounds at window 0.105 are used instead (see "Open fields").

## 3. The pieces, by source

| field | statement (short) | from |
|---|---|---|
| `toIface` | `wVs`, `etaHat`, `AttInv`, `YawInv`, `NavInv`, `CtrlInv`, `sc`, `r`, `q`, `ar`, `τv` | the milestones below |
| `init_world` | `IntOK w₀` | filled (`intOK_missionWorld`, from `MissionParams`) |
| `init` | `AttInv`, `YawInv`, `NavInv`, `CtrlInv` at tick 0 | C16 (takeover, first tick) |
| `init_tube` | `TubeOK` at ticks 0–2; `|η(2)| ≤ ε0` per coordinate | C16 |
| `vglue` | `VGlue w₀ x t` on `Region` at `t ≥ 2` | C15 tick glue (helper 2) for the C-series' `vertical_tick_split` |
| `wVs_def` | `wVs = wSv w₀` | filled (`rfl`) |
| `ne_glue` | `NEGlue w₀ x t` on `Region` at `t ≥ 2` | C15 tick glue (helper 2) |
| `attitude_tracks` | `|etaA − etaHat| ≤ εη` | M4, HORIZONTAL.md §7 structured form |
| `att_step`, `att_rates` | `AttInv` kept under `CmdOK`; rates ≤ 2, 2, 1.4 | M4 (TRACK_PLAN.md §8.2) |
| `yaw_step` | `YawInv` kept | yaw phase lemma, TRACK_PLAN.md §3.8 |
| `ctrl_step` | `CtrlInv` kept | C-series |
| `nav_step` | with `smpErr ≤ δs`: `NavInv` kept | navigator (MISSION.md `nav_contract` (d), leash) |
| `nav_bounds` | targets ≤ 3 m, velocity targets ≤ 1.5 m/s | navigator |
| `pace_filter`, `pace_raw`, `pace_s0`, `pace_q`, `pace_q0`, `pace_scaler` | the code facts of the scaler along the run | C15 tick glue (helper 2) of M8's `code_filter_step`, `rawScaler_unit`, `prog_step` |
| `q_nav`, `τv_nav` | `q` and `τ_v` are the navigator's `navProgress` and `climbTau` (so `hesc` is `ClimbEscape`) | filled (`rfl`) |
| `pace_gaps`, `pace_speed`, `pace_win`, `pace_end` | the course windows, speeds, arrival geometry, end of the last S-curve | M7 / navigator |
| `peakV`, `gainV`, `peakH`, `gainH` | peak and ℓ1 gains ≤ the tables | M5/M6 certificates (helper 1) |
| `nom_box`, `nom_T1`, `nom_climbout`, `nom_w07`, `nom_corner`, `nom_win0`, `nom_along`, `nom_rest`, `nom_complete` | phase-resolved nominal bounds | certified nominal (helper 1) |
| `loiter_nav` | at completion the stopping point comes from the estimates; afterwards the target is no farther from `w7` than it | navigator (`loiter_start`) |

Every step hypothesis concerns one tick (`Region` at `t`, conclusion at `t+1`). The pacing facts
are per tick along the run. `loiter_nav` (the loiter after completion) takes more. The escape of
the climb is not a field: it is the hypothesis `hE` (`pace_esc_of` in Main.lean reads `hesc` off it
through `q_nav` and `τv_nav`).

## 4. How the proof goes

**`inv_succ`** builds `Inv1` at `t + 1` in this order:

1. `nav_step`, using `smpErr ≤ δs` at `t` (`smpErr_le`: nominal plus tube plus sensing).
2. `Pre (t+1)`.
3. The tubes, by `tube_out` from `wV_bound` (`vglue`, the C-series' `vertical_tick_split`), from
   `wHβ_bound` (`ne_glue`, `prow_le`, M6's `horizontal_tick_eq_D`, sensing) and from
   `attitude_tracks`, at ticks `2 … t` (`init_tube` up to tick 2).
4. The boxes (`nom_box` plus the tubes).
5. `CmdOK t`, read off the box at `t + 1` (`c₁ = cmd t`, `c₁ − c₂ = Δcmd`).
6. `att_step`, `yaw_step`, `ctrl_step`, and `world_all`.

**`ψtrack_of_inv`** (`Main.lean`):

* **T1**: `err = ‖nomE3 + η3‖ ≤ ‖nomE3‖ + τ3`.
* **T2**: positions from `nav_bounds` and T1; velocities from the velocity targets and the boxes;
  rates from `att_rates`.
* **T3**: `nom_climbout`.
* **T4**: `nom_w07` at `w0 = w7` and `nom_corner` at `w₁ … w₆`, each plus `τ3`.
* **T6**: `nom_rest` plus `τ3v` plus `float` sensing.
* **T5**: `Pacing.pacing_course` with:
  * `Pace` from `pace_run` (`pace_of` plus this file's induction keeping the scaler in
    `[−c, 1 + c]`);
  * the phase bounds from `phase_r`: P-1 (`rawScaler_ge`) with the along-track hypotheses derived
    from `nom_along` and the tubes, and the speeds from `pace_speed`;
  * the window at `w0` from `nom_win0` plus the tube;
  * the windows at `w₁ … w₇` from `pace_win`.
* **Hold**:
  * if the mission completes within the horizon, `Pacing.hold_course`, with `loiter_nav` and
    `hd`/`hv` (≤ 0.03, ≤ 0.05) from `nom_complete`, the tubes and the estimates;
  * otherwise `Pacing.hold_formula`, with `pace_end` and the S-curve time's leak (`q_leak`: less
    than one tick over the hold).

## Open fields (for the helpers)

The fields below are copied from `Contracts/Track/Induction/Pieces.lean` (structure `Pieces`, which
`extends Iface`). In them `toIface` is the `Iface` of the instance. Its data
(`wVs`, `etaHat`, `AttInv`, `YawInv`, `NavInv`, `CtrlInv`, `sc`, `r`, `q`, `ar`, `τv`) is
only partly fixed (`wVs`, `sc`, `q`, `τv` are, see "Proved or filled"), so **deliver each field as a theorem generic in `I : Iface`** (and in `sense32`,
`senseP`, `w₀`, `x`, with `MissionWorld w₀`, `CopterSense sense32 senseP`, `LibmSpec` as you need
them), with `toIface` replaced by `I`. Add only the hypotheses on `I`'s data your proof needs, and
list them in the docstring. Two exceptions:

* the glue helper defines `sc`, `r` and `q`;
* the nominal helper may fix `wVs` and `etaHat`.

`Instance.lean` plugs the theorems in. The definitions used are in `Run.lean` (readouts),
`Inv.lean` (constants, `Region`, `Pre`, `nomV`/`nomH`/`nomE3`/`nomV3`, `wV`, `TubeOK`) and
`Horiz.lean` (`NEGlue`, `prow`).

### Certified nominal (helper 1, `Contracts/Track/Induction/Nominal.lean`)

From the finished `Vertical*` and `Horizontal*` theorems. The gains are those of the exact models
`AvR`, `AhR` for the outputs `outV`, `outH` (tables `PV`, `GV`, `PH`, `GH` in Inv.lean).

**The corner field `nom_corner`, per corner** (`i : Fin 6`, waypoint `cIdx i`). It is a 3D bound
on the nominal vehicle (target plus nominal error) with the tube `τ3 = 4.6` mm to spare. Each
corner uses its own bounds:

`sqrt((B_i + 0.0025 + ε_al)² + V_i²) + τ3 ≤ 0.1`

* `B_i` is the certified planar bound at window 0.105 (`corner_vehicle_per_105`: 0.07841, 0.07948,
  0.07990, 0.08074, 0.07960, 0.07933).
* `0.0025` is the target-to-table whole-tick displacement.
* `ε_al` is the deviation of the actual horizontal nominal from the course response at the aligned
  index (time warp, blend start, heading coupling).
* `V_i` is the vertical offset: the target's `|dz|` (≤ 0.0131 on the ideal course) plus the vertical
  nominal on the corner window.

**Why the window stays at 0.105 and only the additive 2.5 mm term is needed.** The target `q` lies
on the course between two table points `T(m)`, `T(m+1)` that are at most 2.5 mm apart (1 m/s,
one tick). Pick the one on the corner's side.

* On the way in, the later point is closer to the corner than `q`; on the way out, the earlier one.
  Either way `|T(m) − c| ≤ |q − c|` up to the second-order apex term `(1.25 mm)²/(2·0.1) < 10⁻⁵`.
* That term matters only if `|q − c|` is within `10⁻⁵` of 0.105 at the apex. The apex distance is
  0.1000–0.1008, so it cannot happen. Hence `|T(m) − c| ≤ 0.105`: the certified window already
  covers every tick where the real target is within 0.105, and no widening is needed.
* What the window does not cover is that the nominal vehicle is `q + err`, not `T(m) + err(m)`. The
  difference is `q − T(m)` (≤ 2.5 mm) plus the change of the response over a sub-tick (< 10⁻⁵ m,
  inside `ε_al`). That is the additive term, and it is needed once.

Monte Carlo, target within 0.105 of `w₁ … w₆`: vehicle planar ≤ 0.0783, `|dz|` ≤ 0.0218, 3D ≤ 0.0801.

```lean
peakV : ∀ o j m, |resp Vertical.AvR (outV o) m j| ≤ PV o j
gainV : ∀ o j N, ∑ m ∈ range N, |resp Vertical.AvR (outV o) m j| ≤ GV o j
peakH : ∀ o j m, |resp Horizontal.AhR (outH o) m j| ≤ PH o j
gainH : ∀ o j N, ∑ m ∈ range N, |resp Horizontal.AhR (outH o) m j| ≤ GH o j
nom_box : ∀ x, Beh sense32 senseP w₀ x → ∀ t, Pre toIface w₀ x t →
  (∀ o, |outV o ⬝ᵥ nomV toIface w₀ x t| ≤ bV o - τV o) ∧
    ∀ a o, |outH o ⬝ᵥ nomH toIface w₀ x a t| ≤ bH o - τH o
nom_T1 : ∀ x, Beh sense32 senseP w₀ x → ∀ t, Pre toIface w₀ x t → ‖nomE3 toIface w₀ x t‖ + τ3 ≤ δ
nom_climbout : ∀ x, Beh sense32 senseP w₀ x → ∀ t, Pre toIface w₀ x t →
  inColumn (posTarget (x t)) → ρ < polyDist (posTarget (x t)) → ‖nomE3 toIface w₀ x t‖ + τ3 ≤ δ₀
nom_w07 : ∀ x, Beh sense32 senseP w₀ x → ∀ t, Pre toIface w₀ x t →
  dist (posTarget (x t)) w7 ≤ rPassEnd → dist (posTarget (x t) + nomE3 toIface w₀ x t) w7 + τ3 ≤ rWp
nom_corner : ∀ x, Beh sense32 senseP w₀ x → ∀ t, Pre toIface w₀ x t → ∀ i : Fin 6,
  dist (posTarget (x t)) (wp (cIdx i)) ≤ rPassMid →
    dist (posTarget (x t) + nomE3 toIface w₀ x t) (wp (cIdx i)) + τ3 ≤ rWp
nom_win0 : ∀ x, Beh sense32 senseP w₀ x → ∀ t, Pre toIface w₀ x t →
  toIface.ar x 0 ≤ toIface.q x t → toIface.q x t < toIface.ar x 0 + 2 →
    dist (posTarget (x t) + nomE3 toIface w₀ x t) (wp 0) + τ3 ≤ rWp
nom_along : ∀ x, Beh sense32 senseP w₀ x → ∀ t, Pre toIface w₀ x (t + 1) →
  toIface.τv x - 1 ≤ toIface.q x t → toIface.q x t < toIface.ar x 7 →
    inner ℝ (velTarget (x t)) (velTarget (x t) - (velTarget (x (t + 1)) + nomV3 toIface w₀ x (t + 1)))
        ≤ (55 / 1000 - τ3v - 1 / 10 ^ 4) * ‖velTarget (x t)‖ ∧
      inner ℝ (velTarget (x t)) (posTarget (x t) - (posTarget (x (t + 1)) + nomE3 toIface w₀ x (t + 1)))
        ≤ (3 / 100 - τ3 - 1 / 10 ^ 4) * ‖velTarget (x t)‖
nom_rest : ∀ x, Beh sense32 senseP w₀ x → ∀ t, Pre toIface w₀ x t →
  dist (posTarget (x t)) w7 ≤ rRest → ‖velTarget (x t)‖ ≤ rRest →
    ‖nomV3 toIface w₀ x t‖ + τ3v + 1 / 10 ^ 4 ≤ δv
nom_complete : ∀ x, Beh sense32 senseP w₀ x → ∀ tc, Pre toIface w₀ x tc → complete w₀ x tc →
  (∀ k < tc, ¬ complete w₀ x k) →
    dist (posTarget (x tc) + nomE3 toIface w₀ x tc) w7 + τ3 + 1 / 10 ^ 6 ≤ 3 / 100 ∧
      ‖velTarget (x tc) + nomV3 toIface w₀ x tc‖ + τ3v + 1 / 10 ^ 6 ≤ 5 / 100
```

### Tick glue (helper 2, `Contracts/Track/Induction/TickGlue.lean`)

The glue of the per-tick lemmas of the other milestones to `Vehicle.tick` of `run w₀ x t`
(`tick_split` of CtrlVerticalWorld.lean, the navigator's `replayPos` events). Two glue fields
deliver hypotheses that finished theorems then use:

* **`ne_glue`** delivers `NEGlue` (Horiz.lean): the `NE_update_controller` call with
  `HCtl.NERegion`, the active `D_update_controller` after it, and the readouts. `wHβ_bound`
  (proved) uses it with M6's `HCtl.horizontal_tick_eq_D`.
* **`vglue`** delivers `VGlue` (Vert.lean): `CtrlV.VTickHyp` at the region's magnitudes (`0.11`,
  `0.6`, `2`, `3`, `5`, `16`, `16`, `cos θ ≥ 0.9`, mixer mean `εmix = 3·10⁻⁷`), the targets read
  by `D_update_controller`, and `|thr| ≤ 3`, `|I| ≤ 2`. `wV_bound` (proved) uses it with the
  C-series' `CtrlV.vertical_tick_split`.

  **`hmix` (C12, the mixer mean).** The CtrlV agent could not unroll `output_armed_stabilizing` for
  this field. `VTickHyp.hmix` is
  `|meanAct (Vehicle.tick w smp).2 - (Vehicle.tick w smp).1.ms._throttle_filter.output.toReal| ≤ εmix`.
  It comes from the attitude agent's `Mixer.tick_output_spec` (CtrlAttitudeMixer.lean):
  * that lemma puts each actuator `i < 4` within `3·10⁻⁷` of
    `F.toReal + RF i·r + PF i·q + YF i·y`, where `F = f + (u − f)·α` is the `float` filter update;
  * `RF`, `PF`, `YF` each sum to 0, so the mean is within `3·10⁻⁷` of `F.toReal`.

  Hence `εmix = 3·10⁻⁷`, not the `10⁻⁷` used first. With `εmix = 3·10⁻⁷`, `βcode` rows 1 and 7 are
  `1.94·10⁻⁸` and `3.51·10⁻⁷`. `εV` rows 1 and 7 are raised to `2.5·10⁻⁸` and `4·10⁻⁷`. `βcode_le`
  and `τV_spec` still hold, and the tube moves by under `6·10⁻⁶` m, against slack of at least
  `5.8·10⁻⁴`. The rest of `hmix` is tick glue (helper 2):
  * `tick_output_spec` is stated at the world where `Vehicle.tick` calls `output`. It must be
    instantiated at the intermediate world of the tick.
  * The stored filter output after the tick must be identified with `F`: `update_throttle_filter`
    stores it, with no reset, and the rest of the tick does not touch `ms._throttle_filter`.
  * The emitted `act` must be identified with `_actuator[0…3]` after `output`.
  * The mixer region must be supplied from the invariant (`CtrlInv`/`Region`):
    * `f, u ∈ [0.301, 0.619]` (the hover throttle is about 0.44);
    * `|roll_in|, |pitch_in|, |yaw_in| ≤ 0.15`;
    * the frame facts `Quad`, the factors within `10⁻⁷`, armed, interlock, `THROTTLE_UNLIMITED`,
      no boost, zero slew and expo, `lift_max = 1`, battery output `1`, and air density ratio `1`.

    None of these is a gap in the attitude agent's lemma.

The remaining glue fields:

* **`pace_filter`, `pace_raw`, `pace_s0`, `pace_scaler`** place M8's `code_filter_step` and
  `rawScaler_unit`. The instance fixes `sc x t = (run w₀ x (t + 1)).wps._track_dt_scalar.toReal`
  (the scaler after tick `t`) and `q x t = navProgress w₀ x t` (the sum of `sc` over ticks
  `0 … t`, the S-curve time in ticks). The glue helper defines `r`, the raw scaler of the tick's
  logged inputs. `pace_q` and `pace_q0` are filled: with these definitions they hold with error 0.
  `prog_step` is therefore no longer needed for `q`. The drift between `q` and the S-curve's
  `float` clock belongs to the navigator's facts on `q` (`pace_speed`, `pace_win`, `pace_end`).

All step hypotheses now include `t ≤ horizonTicks` (in `Region`), so the glue is asked only about
the 12000 ticks of `ψtrack`. For example, `ticks32 ≠ 0` holds there.

```lean
ne_glue : ∀ x, Beh sense32 senseP w₀ x → ∀ t, 2 ≤ t → Region toIface w₀ x t → NEGlue w₀ x t
vglue : ∀ x, Beh sense32 senseP w₀ x → ∀ t, 2 ≤ t → Region toIface w₀ x t → VGlue w₀ x t
pace_filter : ∀ x, Beh sense32 senseP w₀ x → ∀ t, Region toIface w₀ x (t + 1) →
  -(1 / 1000) ≤ toIface.sc x t → toIface.sc x t ≤ 1 + 1 / 1000 →
    |toIface.sc x (t + 1) - (toIface.sc x t + (toIface.r x (t + 1) - toIface.sc x t) * Pacing.α₀)|
      ≤ 1 / 10 ^ 7
pace_raw : ∀ x, Beh sense32 senseP w₀ x → ∀ t, 0 ≤ toIface.r x t ∧ toIface.r x t ≤ 1
pace_s0 : ∀ x, Beh sense32 senseP w₀ x →
  -((1 / 10 ^ 7) / Pacing.α₀) ≤ toIface.sc x 0 ∧ toIface.sc x 0 ≤ 1 + (1 / 10 ^ 7) / Pacing.α₀
pace_q : ∀ x, Beh sense32 senseP w₀ x → ∀ t, Region toIface w₀ x (t + 1) →
  |toIface.q x (t + 1) - toIface.q x t - toIface.sc x (t + 1)| ≤ 1 / 10 ^ 7
pace_q0 : ∀ x, Beh sense32 senseP w₀ x → |toIface.q x 0 - toIface.sc x 0| ≤ 1 / 10 ^ 7
pace_scaler : ∀ x, Beh sense32 senseP w₀ x → ∀ t, (∀ k ≤ t + 1, Inv1 toIface w₀ x k) →
  ∃ (vT pe ve : AC_WPNav_lib.Vector3f.State) (kP : Float32),
    toIface.r x (t + 1) = (Pacing.rawScaler vT pe ve kP).toReal ∧ kP.IsFinite ∧
    kP.toReal = 3 / 2 ∧ Pacing.Fin3 vT 3 ∧ Pacing.Fin3 pe 4 ∧ Pacing.Fin3 ve 3 ∧
    v3 vT = velTarget (x t) ∧ dist (v3 ve) (vel (x (t + 1))) ≤ 1 / 10 ^ 5 ∧
    dist (v3 pe) (posTarget (x t) - pos (x (t + 1))) ≤ 1 / 10 ^ 5
```

### Proved or filled

* `plant_rows`: removed from the fields. `prow_le` (PlantRow.lean) proves it from
  `Plant.step_pv_sharp`, with `|ω| ≤ 2` from `att_rates`, at `1.8·10⁻⁷`.
* `wVs_def`: `rfl` in the instance (`wVs := wSv w₀`).
* `sc`, `q`, `τv` (interface data): `sc` is the world's `_track_dt_scalar` after the tick,
  `q := navProgress w₀`, `τv := climbTau w₀` (Spec.lean).
* `pace_q`, `pace_q0`: exact (`Finset.sum_range_succ`, `run_eq_ctrlWorld`).
* `q_nav`, `τv_nav`: `rfl`.
* `init_world`: `intOK_missionWorld` (InitWorld.lean).
  * The limits are `MissionParams`' `kimax_rr`, `kimax_rp`, `kimax_ry` (`0.5`), `kimax_vd` (`10`)
    and `kimax_ad` (`0.8`). These are `KOK` from the literals, and `0.8 ≤ KA` is `le_max_left`.
  * The integrators are those of `AC_AttitudeControl_Multi.init` and `AC_PosControl.init`, which
    are `0` by evaluation (`construct_as_ps`; `boot` touches only the motors).
* `pace_esc`: removed. It is now the hypothesis `hE : ClimbEscape sense32 senseP w₀` of
  `track_contract`, by the coordinator's decision (VERTICAL.md §9: no cheap certificate exists).

### Trusted fact

`(float) M_PI = 3.14159274f` is the field `LibmSpec.pi32` (Spec.lean; MISSION.md lists it with the
conversion clauses). `Step.lean` passes `hL.pi32` to `wV_bound`; it is no longer a Pieces field.

### Remaining fields (other milestones)

```lean
init : ∀ x, Beh sense32 senseP w₀ x →
  toIface.AttInv x 0 ∧ toIface.YawInv x 0 ∧ toIface.NavInv x 0 ∧ toIface.CtrlInv x 0
init_tube : ∀ x, Beh sense32 senseP w₀ x →
  (∀ t ≤ 2, TubeOK toIface w₀ x t) ∧ (∀ j, |ηV toIface w₀ x 2 j| ≤ ε0V j) ∧
    ∀ a j, |ηH toIface w₀ x 2 a j| ≤ ε0H j
attitude_tracks : ∀ x, Beh sense32 senseP w₀ x → ∀ t, 2 ≤ t → Region toIface w₀ x t →
  ∀ a, |etaA w₀ x t a - toIface.etaHat x t a| ≤ εη
att_step : ∀ x, Beh sense32 senseP w₀ x → ∀ t, Region toIface w₀ x t → CmdOK w₀ x t →
  toIface.AttInv x (t + 1)
att_rates : ∀ x, Beh sense32 senseP w₀ x → ∀ t, toIface.AttInv x t →
  |ph x t 10| ≤ 2 ∧ |ph x t 11| ≤ 2 ∧ |ph x t 12| ≤ 7 / 5
yaw_step : ∀ x, Beh sense32 senseP w₀ x → ∀ t, Region toIface w₀ x t → toIface.YawInv x (t + 1)
ctrl_step : ∀ x, Beh sense32 senseP w₀ x → ∀ t, Region toIface w₀ x t →
  toIface.CtrlInv x (t + 1)
nav_step : ∀ x, Beh sense32 senseP w₀ x → ∀ t, Region toIface w₀ x t → smpErr (x t) ≤ δs →
  toIface.NavInv x (t + 1)
nav_bounds : ∀ x, Beh sense32 senseP w₀ x → ∀ t, toIface.NavInv x t →
  ∀ i, |posTarget (x t) i| ≤ 3 ∧ |velTarget (x t) i| ≤ 3 / 2
pace_gaps : ∀ x, Beh sense32 senseP w₀ x →
  (240 ≤ toIface.ar x 0 - toIface.τv x ∧ toIface.ar x 0 - toIface.τv x ≤ 510) ∧
  (2 ≤ toIface.ar x 1 - toIface.ar x 0 ∧ toIface.ar x 1 - toIface.ar x 0 ≤ 860) ∧
  (2 ≤ toIface.ar x 2 - toIface.ar x 1 ∧ toIface.ar x 2 - toIface.ar x 1 ≤ 743) ∧
  (2 ≤ toIface.ar x 3 - toIface.ar x 2 ∧ toIface.ar x 3 - toIface.ar x 2 ≤ 743) ∧
  (2 ≤ toIface.ar x 4 - toIface.ar x 3 ∧ toIface.ar x 4 - toIface.ar x 3 ≤ 1450) ∧
  (2 ≤ toIface.ar x 5 - toIface.ar x 4 ∧ toIface.ar x 5 - toIface.ar x 4 ≤ 743) ∧
  (2 ≤ toIface.ar x 6 - toIface.ar x 5 ∧ toIface.ar x 6 - toIface.ar x 5 ≤ 743) ∧
  (2 ≤ toIface.ar x 7 - toIface.ar x 6 ∧ toIface.ar x 7 - toIface.ar x 6 ≤ 750)
pace_speed : ∀ x, Beh sense32 senseP w₀ x → ∀ t, toIface.NavInv x t →
  (toIface.τv x - 1 ≤ toIface.q x t → toIface.q x t < toIface.ar x 1 →
    36 / 100 ≤ ‖velTarget (x t)‖) ∧
  (∀ i : Fin 8, 2 ≤ (i : ℕ) → (i : ℕ) ≤ 6 → toIface.ar x (i - 1) - 1 ≤ toIface.q x t →
    toIface.q x t < toIface.ar x i → 6 / 10 ≤ ‖velTarget (x t)‖) ∧
  (toIface.ar x 6 - 1 ≤ toIface.q x t → toIface.q x t < toIface.ar x 7 →
    48 / 100 ≤ ‖velTarget (x t)‖)
pace_win : ∀ x, Beh sense32 senseP w₀ x → ∀ i : Fin 8, 1 ≤ (i : ℕ) → ∀ t, toIface.NavInv x t →
  toIface.ar x i ≤ toIface.q x t → toIface.q x t < toIface.ar x i + 2 →
    dist (posTarget (x t)) (wp i) ≤ rPass (wp i)
pace_end : ∀ x, Beh sense32 senseP w₀ x → ∀ t, toIface.NavInv x t → ¬ complete w₀ x t →
  toIface.ar x 7 - 1 ≤ toIface.q x t → dist (posTarget (x t)) w7 ≤ rPass w7
loiter_nav : ∀ x, Beh sense32 senseP w₀ x → ∀ tc, (∀ k ≤ tc, Inv1 toIface w₀ x k) →
  complete w₀ x tc → (∀ k < tc, ¬ complete w₀ x k) →
    ∃ (p : AC_PosControl.Params) (s : AC_PosControl.State), LoiterHyps p s ∧
      dist (estPos s) (pos (x tc)) ≤ 1 / 10 ^ 6 ∧ dist (estVel s) (vel (x tc)) ≤ 1 / 10 ^ 6 ∧
      ∀ t, tc ≤ t → (∀ k ≤ t, Inv1 toIface w₀ x k) →
        dist (posTarget (x t)) w7 ≤ dist (stopPt p s) w7
```

**What each remaining field still needs.**

* **The escape of the climb** is the hypothesis `ClimbEscape` (MISSION.md). The route to
  discharge it is in VERTICAL.md §9: a tighter early tube on the first 350 ticks plus the
  deviation analysis along a computed nominal.
* **`pace_speed`, `pace_win`, `pace_end`, `pace_gaps`** are stated on `q = navProgress` and
  `τ_v = climbTau`. The navigator must account for the drift between `navProgress` and
  `400 × _scurve_this_leg.time`, which comes from the rounding of the steps and of the S-curve
  clock.
* **`init`, `init_tube`, `ctrl_step`** concern the glue helper's code invariant `CtrlInv`: the
  finiteness, flags and branch conditions that `vglue`, `ne_glue` and `pace_*` need per tick. Its
  initial value comes from the takeover; the first two ticks (`first_tick`, `reset_filter`) need a
  direct evaluation from `startP p ψ₀` (C16).
* **`init_world`** is filled (see "Proved or filled").

## 5. Discharge plan

1. **Helper 1 (certified nominal, `Nominal.lean`)**: the gains `peakV`, `gainV`, `peakH`, `gainH`,
   and `nom_box`, `nom_T1`, `nom_climbout`, `nom_w07`, `nom_corner` (per corner), `nom_win0`,
   `nom_along`, `nom_rest`, `nom_complete`. Inputs: the finished `scurve_climb`, `course_norm`,
   `corner_vehicle_per_105`, and the vertical per-leg family.
2. **Helper 2 (tick glue, `TickGlue.lean`)**: `ne_glue`, `vglue`, and `pace_filter`, `pace_raw`,
   `pace_s0`, `pace_scaler`, defining `r` (`sc` and `q` are fixed in the instance).
3. **C-series and C16**: `ctrl_step` with their `CtrlInv`, `init`, `init_tube`.
4. **M4**: `AttInv`, `att_step`, `att_rates`, `attitude_tracks` with `etaHat` (the heading
   coupling as an explicit profile, HORIZONTAL.md §7 option 1/2), `YawInv`, `yaw_step`.
5. **Navigator / M7**: `NavInv`, `nav_step`, `nav_bounds`, `loiter_nav`, `ar`, `pace_gaps`,
   `pace_speed`, `pace_win`, `pace_end`.

When `pieces` has no `sorry`, `track_contract` is proved: `Sub.lean` already uses
`track_contract_proof`.
