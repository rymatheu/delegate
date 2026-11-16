# Ledger of the plant library

Written from `tests/PlantAudit.lean` (2026-11-16): `cd plant && LEAN_NUM_THREADS=1 lake env lean tests/PlantAudit.lean`
after `LEAN_NUM_THREADS=1 lake build`. The audit covers every theorem of the modules `Plant.*` outside `Plant.Model.*`
and `Plant.Lib.*` (the constants Lean generates for structures are left out).

## Summary lines (verbatim)

```
theorems outside Plant.Model and Plant.Lib: 207
rule 3 (statement names a model, flow or step constant): 171 of 207 directly, 33 through a derived definition, 3 violations
  through a derived definition: [Plant.Cd_alphaMax_le, Plant.Cd_spread_le, Plant.Kin_nonneg, Plant.Klip_pos, Plant.Mbd_nonneg, Plant.TorqueBd.nonneg, Plant.abs_dnDDot_le, Plant.alphaMax_ge_num, Plant.alphaMax_le_num, Plant.alphaMax_pos, Plant.box_mono, Plant.box_nonneg, Plant.ctau_nonneg, Plant.energy_nonneg, Plant.le_wTA, Plant.mix_add, Plant.mix_smul, Plant.mix_unmix, Plant.norm_le_box, Plant.p_scaledSol, Plant.qnormSq_scaledSol, Plant.range_wrench, Plant.spinSol_zero, Plant.torqueBd_alphaMax, Plant.torqueBd_of_spread, Plant.torqueFreeXY_const, Plant.unmix_mix, Plant.unmix_wrench, Plant.vB_nonneg, Plant.wB_one_le, Plant.wTA_one_alphaMax_le, Plant.wTA_one_spread_le, Plant.wrench_eq_mix]
  violations: [Plant.Cd_mono, Plant.Cd_nonneg, Plant.Katt_pos]
rule 4 (axioms): violations: []
axioms used: [Quot.sound, Classical.choice, propext]
theorems by kind: [(Algebra, 32), (Range, 52), (Regularity, 20), (Invariant, 9), (Existence, 22), (Sensitivity, 12), (Exact, 23), (Step, 37)]
```

Rule 3: 171 theorems name a model, flow or step constant in their statement; 33 name only a derived definition (a
definition outside `Plant.Model` whose value reaches the model, e.g. `alphaMax`, `box`, `wB`, `wTA`, `Kin`, `mix`,
`spinSol`). The three violations are lemmas about the numeric functions `Cd` and `Katt` of `Step/Sharp.lean`, whose
definitions carry CF2X ratios as literals (`31/20 = Jz/Jx` in `Cd`, `gyro = 11/20` in `Katt`) instead of model
constants (`FINDINGS.md`, F3). Rule 4: no theorem uses an axiom beyond `propext`, `Classical.choice`, `Quot.sound`.

How kinds are assigned: for the theorems carried over from the archive, by `kindOverride` or by the name (`kindOf`);
for the files written in phase 3, by the module (`Field/Actuators`: Algebra, `Flow/Sensitivity`: Sensitivity,
`Step/Exact`: Exact, `Step/Symmetry`: Algebra, `Step/Period`: Step, `Step/Multi`: Existence) with the exceptions in
`newOverride`. The assignment is a reading aid, not a checked property.

## Theorems by file

| file | origin | theorems |
|---|---|---|
| `Plant/Model/Constants.lean`, `Plant/Model/Field.lean` | archive (frozen, `MODEL.sha256`) | 17 + 19 (not audited: model) |
| `Plant/Lib/{Real,Blocks,RadialTrunc}.lean` | archive (moved, names kept) + `sum_dn_sq`, `qnormSq_yawRot` | 8 + 19 + 1 (not audited: model-free) |
| `Plant/Field/Bounds.lean`, `Invariants.lean` | archive | 23 + 15 |
| `Plant/Flow/Flow.lean` | archive | 29 |
| `Plant/Step/Euler.lean`, `Sharp.lean` | archive (`eulerStep_pv_quatOf` left out) | 16 + 40 |
| `Plant/Step/Sample.lean` | archive `Quadrotor.lean`, real-valued part | 7 |
| `Plant/Field/Actuators.lean` | phase 3 | 24 |
| `Plant/Flow/Sensitivity.lean` | phase 3 | 9 |
| `Plant/Step/Exact.lean` | phase 3 | 16 |
| `Plant/Step/Symmetry.lean` | phase 3 | 6 |
| `Plant/Step/Period.lean` | phase 3 | 6 |
| `Plant/Step/Multi.lean` | phase 3 | 16 |

## Coverage per constant

Per model, flow or step constant, the number of audited theorems of each kind whose conclusion names it (or, when the
conclusion names none, whose hypotheses do). A theorem counts once for every such constant.

| constant | Algebra | Range | Regularity | Invariant | Existence | Sensitivity | Exact | Step |
|---|---|---|---|---|---|---|---|---|
| `IsRun` |  |  |  | 1 |  |  |  |  |
| `Jx` | 2 | 4 | 1 |  |  | 1 |  |  |
| `Jy` | 1 | 3 | 1 |  |  | 1 |  |  |
| `Jz` | 1 | 3 | 1 |  |  | 1 | 1 |  |
| `Quat.normSq` | 1 |  |  |  |  |  |  |  |
| `State.ofX` | 1 |  |  |  |  |  |  |  |
| `accel` | 4 | 6 |  |  |  | 1 | 2 | 10 |
| `amax` | 2 | 5 | 1 |  |  | 1 | 3 | 2 |
| `clip01` | 4 | 1 | 1 |  |  | 1 | 3 |  |
| `downAxis` | 2 |  |  |  |  |  |  |  |
| `eulerStep` |  |  |  |  |  |  |  | 2 |
| `flowT` |  |  |  |  | 3 |  |  |  |
| `fmax` | 2 | 3 |  |  |  |  |  |  |
| `force` |  | 1 |  |  |  |  |  |  |
| `grav` | 3 | 2 |  |  |  |  | 9 | 13 |
| `h` | 1 | 1 | 2 | 1 | 9 | 5 | 10 | 13 |
| `kmkf` | 1 | 1 |  |  |  |  |  |  |
| `lever` | 1 | 2 |  |  |  |  |  |  |
| `mass` | 1 |  |  |  |  |  |  |  |
| `nextR` |  |  |  |  |  |  | 1 |  |
| `sampleR` |  |  |  |  |  |  | 1 |  |
| `sampledFlow` |  |  |  |  | 3 |  |  |  |
| `sfX` | 1 |  |  |  |  |  |  | 1 |
| `step` | 2 |  | 3 | 2 | 5 | 5 | 10 | 10 |
| `stepN` | 2 |  |  | 2 | 8 |  | 3 |  |
| `thrust` | 1 | 1 |  |  |  |  |  |  |
| `thrust2weight` | 1 |  |  |  |  |  | 2 |  |
| `tickSpecForce` |  |  |  |  |  |  | 1 |  |
| `torqueX` | 2 | 3 |  |  |  | 1 |  |  |
| `torqueY` | 2 | 3 |  |  |  | 1 |  |  |
| `torqueZ` | 3 | 3 |  |  |  | 1 | 1 |  |
| `traj` | 2 |  | 2 | 1 | 6 | 1 | 2 | 22 |
| `trajN` |  |  |  |  | 4 |  |  |  |
| `vf` | 8 | 7 | 13 | 1 | 5 | 1 | 2 | 8 |
| `vfT` | 1 |  | 1 |  | 1 |  |  |  |
