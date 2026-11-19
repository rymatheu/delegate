# Ledger of the plant library

Written from `tests/plant/PlantAudit.lean` (2026-11-16, the X500 model): `LEAN_NUM_THREADS=1 lake env lean
tests/plant/PlantAudit.lean` after `LEAN_NUM_THREADS=1 lake build`. The audit covers every theorem of the modules `Plant.*`
outside `Plant.Model.*` and `Plant.Lib.*` (the constants Lean generates for structures are left out).

## Summary lines (verbatim)

```
theorems outside Plant.Model and Plant.Lib: 344
rule 3 (statement names a model, flow or step constant): 288 of 344 directly, 56 through a derived definition, 0 violations
  through a derived definition: [Plant.Cd_alphaMax_le, Plant.Cd_mono, Plant.Cd_nonneg, Plant.Cd_spread_le, Plant.Katt_num, Plant.Katt_pos, Plant.Klip_pos, Plant.Mbd_nonneg, Plant.TorqueBd.nonneg, Plant.TorqueBdT.nonneg, Plant.accK1_zero, Plant.accK2_zero, Plant.accK3_zero, Plant.accK4_zero, Plant.alphaMax_ge_num, Plant.alphaMax_le_num, Plant.alphaMax_num, Plant.alphaMax_pos, Plant.box_mono, Plant.box_nonneg, Plant.ctau_nonneg, Plant.ctau_num, Plant.energy_nonneg, Plant.gyro_nonneg, Plant.gyro_num, Plant.hasDerivAt_accK1, Plant.hasDerivAt_accK2, Plant.hasDerivAt_accK3, Plant.hasDerivAt_accK4, Plant.hasDerivAt_lagK3, Plant.hasDerivAt_lagK4, Plant.lagK1_zero, Plant.lagK2_zero, Plant.lagK3_zero, Plant.lagK4_zero, Plant.le_wTA, Plant.mix_add, Plant.mix_smul, Plant.mix_unmix, Plant.norm_le_box, Plant.p_scaledSol, Plant.pairedCmd_const, Plant.qnormSq_scaledSol, Plant.range_wrench, Plant.spinSol_zero, Plant.torqueBdT_alphaMax, Plant.torqueBd_alphaMax, Plant.torqueBd_of_spread, Plant.torqueFreeXY_const, Plant.unmix_mix, Plant.unmix_wrench, Plant.vB_nonneg, Plant.wB_one_le, Plant.wTA_one_alphaMax_le, Plant.wTA_one_spread_le, Plant.wrench_eq_mix]
  violations: []
rule 4 (axioms): violations: []
axioms used: [Quot.sound, Classical.choice, propext]
theorems by kind: [(Algebra, 41), (Range, 97), (Regularity, 35), (Invariant, 17), (Existence, 23), (Sensitivity, 34), (Exact, 55), (Step, 42)]
```

Rule 3: 288 theorems name a model, flow or step constant in their statement; 56 name only a derived definition (a
definition outside `Plant.Model` whose value reaches the model, e.g. `alphaMax`, `box`, `Cd`, `accK1`, `mix`).
No violations: the model-free lemmas are in `Plant/Lib/`. Rule 4: no theorem uses an axiom beyond `propext`,
`Classical.choice`, `Quot.sound`. `lagSol` and `simLag` (the exact flow of the lag and the simulator's update) are
counted as flow constants.

How kinds are assigned: by `kindOverride` or `newOverride` in `tests/plant/PlantAudit.lean`, else by the module
(`moduleKind`), else by the name (`kindOf`). The assignment is a reading aid, not a checked property.

## The X500 port in numbers

* The 13-state plant had 207 audited theorems. **206 are carried over** under their names to the 17-state X500
  model; **1 is dropped** (`Kin_nonneg`: the input constant `Kin` no longer exists, the commands enter the field only
  through the motor rows). None is left open.
* **138 new audited theorems** (344 in all), and 34 new model-free lemmas in `Plant/Lib/` (62 there in all).
* Numeric (evaluated) lemmas are only in `Plant/Step/Numbers.lean`, with X500 numbers.

## Theorems by file

| file | theorems | content |
|---|---|---|
| `Plant/Model/Constants.lean`, `Field.lean` | 26 + 23 (not audited: model) | X500 constants, facts of the numbers; state, lag, field, component lemmas |
| `Plant/Lib/{Real,Blocks,RadialTrunc,Gronwall}.lean` | 8 + 31 + 1 + 22 (not audited: model-free) | derivative bounds, Taylor; blocks of `Fin 17 → ℝ`; radial truncation; forced Grönwall, lag integrals, `e^{-1/5}` |
| `Plant/Field/Motor.lean` | 40 | the lag: max form, Lipschitz, exact flow, simulator update, range, sharp sensitivity, integrals |
| `Plant/Field/Bounds.lean` | 35 | forces, torques, thrust Lipschitz, block differences, Lipschitz on balls |
| `Plant/Field/Invariants.lean` | 16 | `‖q‖²`, energy, thrust growth, the one-period box |
| `Plant/Field/Actuators.lean` | 22 | thrust-to-wrench map and inverse, image, monotonicity, command dependence |
| `Plant/Flow/Flow.lean` | 31 | truncated flow, `traj`, `step`, uniqueness, Grönwall, hover |
| `Plant/Flow/Motor.lean` | 19 | the thrust block is the exact lag, `step_fI_sim`, thrust range invariant, thrust sensitivity |
| `Plant/Flow/Sensitivity.lean` | 9 | joint Grönwall in state and command, continuity |
| `Plant/Step/Euler.lean` | 17 | the step against Euler, backward difference, Euler angles |
| `Plant/Step/Sharp.lean` | 48 | torque bounds along the period, closed-form thrust acceleration, sharp translation step, attitude block |
| `Plant/Step/InputSens.lean` | 9 | sharp block-wise command sensitivity |
| `Plant/Step/Integral.lean` | 5 | position and velocity rows as integrals |
| `Plant/Step/Sample.lean` | 7 | plant state, sample, runs, hover |
| `Plant/Step/Exact.lean` | 22 | spin and level flight with the lag, free fall, hover is the only rest equilibrium |
| `Plant/Step/Symmetry.lean` | 6 | translation, yaw rotation |
| `Plant/Step/Period.lean` | 8 | deviation from free fall, per-period velocity bounds |
| `Plant/Step/Multi.lean` | 16 | several periods, level flight over `n` periods |
| `Plant/Step/Numbers.lean` | 34 | evaluated X500 constants and bounds |
## Carried over, changed

The carried-over theorems keep their names and their role; these changed beyond the index layout (13 to 17
coordinates):

* **Thrusts instead of commands.** `force`, `thrust`, `accel`, `torqueX/Y/Z`, `wrench`, `mix` and `TorqueBd` take
  the normalized thrusts; the field uses `thr x`. Statements about them (`thrust_eq`, `accel_le`, `abs_torque*`,
  `wrench_eq_mix`, `range_wrench`, `torqueBd_of_spread`, `accel_hover`, …) read the same with this meaning.
* **Field bounds** (`Field/Bounds.lean`): `vf_sub_v` and `vf_sub_w` gain the thrust difference
  (`+ 4 amax Rq² Df`, `+ 2 alphaMax Df`); `Klip` and `Mbd` gain `1/tauUp`, `2 alphaMax`, `gyro` terms;
  `gyro = (Jz - Jx)/Jx` and `Cd` uses `Jz/Jx` (`FINDINGS.md`, F3); `box` gains the thrust radius `fB`.
* **Commands** (`Field/Actuators.lean`, `Flow/Sensitivity.lean`): `norm_vf_sub_input_le` is `‖u - w‖ / tauUp`
  (motor rows only), and the joint Grönwall bounds use that forcing.
* **Thrust range as a hypothesis** (`FINDINGS.md`, F10): `traj_moves`, `vf_traj_sub`, `vf_traj_sub_v`,
  `step_sub_eulerStep_le`, `step_sub_eulerStep_le_ball`, `backwardDiff_sub_specForce`, `traj_pv_sharp`,
  `step_pv_sharp`, `traj_pv_first`, `traj_qw_gronwall`, `step_qw_gronwall`, `traj_att_taylor`, `traj_v_dev_le`,
  `traj_p_dev_le`, `step_v_dev_le`, `step_p_dev_le`, `step_vz_mem`, `step_v_sub_le`, the spin and level families.
* **Lagged thrust in the closed forms.** `traj_pv_sharp`, `step_pv_sharp`, `traj_pv_first`: the held-thrust terms
  `a t`, `a t²/2`, … become the integrals `accK1`…`accK4` of the lagged thrust acceleration (`accK_held`: equal when
  every thrust is at its command), the remainders use `amax`; `traj_v_dev_le`, `traj_p_dev_le`, `step_vz_mem` use
  `accK1`, `accK3`; the spin solution carries the lag kernels (`spinSol`, `step_spin_*`), with paired thrusts and
  commands (`PairedThr`, `PairedCmd`) in place of `TorqueFreeXY` of the commands; `step_level` states that the attitude
  and rates are kept and the thrusts follow the lag (instead of an equality with `levelSol`, removed);
  `step_level_vz`, `stepN_level_*` use `lagK1`, `lagK3` over the whole time; free fall needs zero thrust and
  nonpositive commands.
* **Attitude block**: `vf_att_lipschitz` gains `2 alphaMax Df`; `traj_qw_gronwall` gains the forcing
  `2 alphaMax Mf h`; `cW` gains `2 alphaMax Mf`; torque bounds along the period are `TorqueBdT`.
* **Numbers** (`Step/Numbers.lean`, X500): `alphaMax_le_num` 137.31, `alphaMax_ge_num` 137.30, `amax_le_num` 16.5646,
  `wB_one_le` 3.34, `wTA_one_alphaMax_le` 1.37, `Cd_alphaMax_le` 200, `wTA_one_spread_le` 1.14, `Cd_spread_le` 66.
* **Sample**: `tickSpecForce` uses the thrusts of the state; `hoverP` and `hoverState` carry the hover thrust.

## Coverage per constant

Per model, flow or step constant, the number of audited theorems of each kind whose conclusion names it (or, when the
conclusion names none, whose hypotheses do). A theorem counts once for every such constant.

| constant | Algebra | Range | Regularity | Invariant | Existence | Sensitivity | Exact | Step |
|---|---|---|---|---|---|---|---|---|
| `IsRun` |  |  |  | 1 |  |  |  |  |
| `Jx` | 2 | 9 | 2 |  |  | 1 |  |  |
| `Jy` | 1 | 6 | 2 |  |  | 1 |  |  |
| `Jz` | 1 | 8 | 2 |  |  | 1 | 1 |  |
| `Quat.normSq` | 1 |  |  |  |  |  |  |  |
| `State.ofX` | 1 |  |  |  |  |  |  |  |
| `accel` | 5 | 8 | 1 |  |  | 1 | 5 |  |
| `amax` | 2 | 9 | 2 |  |  | 1 | 3 | 8 |
| `clip01` | 5 | 1 | 1 | 3 |  | 1 | 9 |  |
| `downAxis` | 2 |  |  |  |  |  |  |  |
| `eulerStep` |  |  |  |  |  |  |  | 2 |
| `flowT` |  |  |  |  | 3 |  |  |  |
| `fmax` | 2 | 5 |  |  |  | 1 |  |  |
| `force` |  | 1 |  |  |  | 1 |  |  |
| `grav` | 3 | 2 |  |  |  |  | 14 | 16 |
| `h` | 1 | 11 | 3 | 2 | 9 | 12 | 13 | 17 |
| `hPhys` |  |  |  |  |  |  | 2 |  |
| `kmkf` | 1 | 2 |  |  |  |  |  |  |
| `lagRate` | 3 | 3 | 4 |  |  |  | 1 |  |
| `lagSol` |  |  | 1 | 6 | 1 | 5 | 16 |  |
| `lagTau` |  | 2 |  |  |  |  | 3 |  |
| `lever` | 1 | 2 |  |  |  |  |  |  |
| `mass` | 1 |  |  |  |  |  |  |  |
| `nextR` |  |  |  |  |  |  | 1 |  |
| `sampleR` |  |  |  |  |  |  | 1 |  |
| `sampledFlow` |  |  |  |  | 3 |  |  |  |
| `sfX` | 1 |  |  |  |  |  |  | 1 |
| `simLag` |  |  |  |  |  |  | 3 |  |
| `step` | 2 |  | 3 | 3 | 5 | 9 | 13 | 12 |
| `stepN` | 2 |  |  | 2 | 8 |  | 3 |  |
| `tauDown` | 1 | 3 |  |  |  | 3 |  |  |
| `tauUp` | 1 | 12 | 5 |  |  | 17 |  | 1 |
| `thr` | 5 | 7 |  | 2 |  | 1 | 12 |  |
| `thrust` | 1 | 1 |  |  |  |  |  |  |
| `thrust2weight` | 1 | 1 |  |  |  |  | 5 |  |
| `tickSpecForce` |  |  |  |  |  |  | 1 |  |
| `torqueX` | 2 | 3 | 1 |  |  | 1 | 1 |  |
| `torqueY` | 2 | 3 | 1 |  |  | 1 | 1 |  |
| `torqueZ` | 3 | 3 | 1 |  |  | 1 | 1 |  |
| `traj` | 3 | 1 | 3 | 4 | 6 | 10 | 8 | 23 |
| `trajN` |  |  |  |  | 4 |  |  |  |
| `vf` | 11 | 8 | 15 | 1 | 5 | 1 | 3 | 9 |
| `vfT` | 1 |  | 1 |  | 1 |  |  |  |
