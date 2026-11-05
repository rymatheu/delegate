# The translated vehicle in the proof package

`Translated/` holds a snapshot of the translated controller of `cpp2lean/lean/` (Lean
`v4.33.0-rc1`), built in this package on Lean `v4.36.0-rc2`.

## What was copied

Copied on 2026-11-05 at 13:32 from `cpp2lean/lean/`. That directory is the one
`lean/.lake/build/bin/copter_lean` (built 12:06) was built from. Its translated libraries are
byte-identical to `ardupilot/out/<lib>/` (checked with `cmp`).

| file | SHA-1 |
|---|---|
| `AC_Attitude_lib.lean` | `8910e8c9d4a51e64d71d4fd707782488901559b1` |
| `AC_PID_lib.lean` | `df0ae78343bd4b4ba61a791b8ae2746b0927847c` |
| `AC_PosControl_lib.lean` | `04f6ed5d0cf0f69b41ce09c6bda23d154d1fd4a1` |
| `AC_WPNav_lib.lean` | `c6b0f4c66cf263cb2631ef4e50ead79e353e7d3b` |
| `AHRS_View_lib.lean` | `2a8bb41105300692be9a8560d460d7c050102c2b` |
| `AP_Math_lib.lean` | `a15960c6a5eb2c6223b18dbfca841fab27336e80` |
| `AP_Motors_lib.lean` | `6f93ac61b4bd523bce3d2325446e49b4ade980c7` |
| `CppLibm.lean` | `cc3c0555bed6c80177e104696e4138b86a8407b2` |
| `Vehicle.lean` | `adfe29e05bba962c4adc411f411ecc380195c843` |
| `VehicleMain.lean` | `c13b25f9c2f4acc9bee3107af119ff3c1758e555` |
| `VehicleParams.lean` | `2f549e5c7c1eb154057886ccee85b323fbc89f5c` |

File names and module names are unchanged.

## Edits for v4.36.0-rc2

**None.** Every file compiles on `v4.36.0-rc2` as copied: no API renames were needed, and the
build shows no warnings. Each file in `Translated/` is byte-identical to its source in
`cpp2lean/lean/`.

The changes are all in the build configuration (`lakefile.toml`):

* The `Translated` library has `srcDir = "Translated"`, so the module names stay the same
  (`AC_WPNav_lib`, `Vehicle`, …). Its roots are the translated libraries plus `VehicleParams` and
  `Vehicle`.
* The executable `copter_lean36` is built from `Translated/VehicleMain.lean`, an unchanged copy of
  `lean/VehicleMain.lean`.
* The package-level `moreLeancArgs` are copied from `lean/lakefile.toml`:
  `-ffp-contract=off -fno-builtin-sinf -fno-builtin-cosf -fno-builtin-sin -fno-builtin-cos -fno-builtin`.
  These are the code-generation assumptions of the translation: no FMA contraction, no fused
  `sincosf`, and no libm simplification. Without them the C compiler could change bits.
* `autoImplicit = false` is set in both packages.

The translated files are plain Lean files, not modules. A `module` file cannot import a
non-module, so the mission files (`Contracts/Mission/*.lean`) are plain files as well. They take
their Mathlib and plant imports from the module `Contracts/MissionPrelude.lean`.

## Replay: the toolchain bump changes no bit

Input: `sim/out/lean-course-1ms/inputs.txt` (7797 lines). Both binaries were run with
`--exact --trace --bits --params sim/params/copter-cf2x.txt --params sim/params/copter-course-speed.txt --params sim/params/copter-cf2x-tuned.txt`:

* `lean/.lake/build/bin/copter_lean` (v4.33.0-rc1, run read-only);
* `contracts/.lake/build/bin/copter_lean36` (v4.36.0-rc2).

Result:

* 7797 output lines from each binary;
* **0 differing lines**: the two outputs are byte-identical, SHA-1
  `f8c77ace613c41c8604be3d8e3ef9efc51731d6a`;
* each line carries 22 values: the 4 actuators and the 18 trace numbers, as exact decimals, with
  their hex bit patterns after `|`.

`--print-params` with the same three files is also identical between the two binaries (133 lines).

## The embedded parameter texts

`MissionData/Course.lean` holds the three course parameter files verbatim, as raw string
literals, together with their SHA-1. `courseLines` is the line list that `VehicleMain` passes to
`construct`.

`mission_world_check <cpp2lean dir>` does two things:

* it compares the embedded texts with the files (all three `same`);
* it prints the parameters of `construct courseLines`.

That output is identical to `copter_lean --print-params` on the files. The mission theorem's
`MissionWorld` is stated with `courseLines`.

To reproduce:

```
cd cpp2lean/contracts
lake build copter_lean36 mission_world_check
P="--params ../sim/params/copter-cf2x.txt --params ../sim/params/copter-course-speed.txt --params ../sim/params/copter-cf2x-tuned.txt"
bash -c ".lake/build/bin/copter_lean36 --exact --trace --bits $P < ../sim/out/lean-course-1ms/inputs.txt > /tmp/o36"
bash -c "../lean/.lake/build/bin/copter_lean --exact --trace --bits $P < ../sim/out/lean-course-1ms/inputs.txt > /tmp/o33"
cmp /tmp/o33 /tmp/o36
.lake/build/bin/mission_world_check .. | diff - <(bash -c ".lake/build/bin/copter_lean36 --print-params $P")
```
