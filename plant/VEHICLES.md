# Vehicles: which model each recorded flight uses, the X500 as simulated, and what in `Plant/` is CF2X-specific

Survey of 2026-11-16. Facts only, each with its source. Paths without a prefix are relative to `cpp2lean/`;
`gpd/` is the installed simulator package `sim/.venv/lib/python3.12/site-packages/gym_pybullet_drones/`
(gym-pybullet-drones 2.2.0, pybullet 3.2.7); `leanfc/` is `/Users/ryan/Research/leanfc/` (read only, imported by the
gorge harnesses through `LEANFC_ROOT`).

## 1. Which recorded flights use which vehicle model

All runs below use the same simulator set-up: gym-pybullet-drones `Physics.PYB` (`gpd/envs/BaseAviary.py:350-369`:
`_physics` then `p.stepSimulation`), gravity set to `GRAVITY_MSS = 9.80665` in place of the package's `9.8`
(`sim/run_copter.py:89`, `gpd/envs/BaseAviary.py:74`; `sim/gorge_lockstep.py:182-186`), PyBullet's default velocity
damping removed (`sim/run_copter.py:338`, called by both harnesses), a 400 Hz lock-step vehicle line (`STEP_US = 2500`),
and the environment stepped at the physics rate with the PWM held for `pyb_hz // 400` substeps
(`sim/fly_reference.py:419-424`, `sim/gorge_lockstep.py:177-180, 424`). PWM 1000..2000 maps to `a = (PWM - 1000)/1000`
clipped to `[0, 1]` (`sim/fly_reference.py:120-122`) and to propeller speed `MAX_RPM sqrt(a)` on sim propeller
`SLOT_TO_SIM[i] = [0, 2, 3, 1][i]` (`sim/run_copter.py:98, 346-353`).

| output directory | harness and command (source) | vehicle model | vehicle binary | boot image / parameter files | physics, control | extra plant terms |
|---|---|---|---|---|---|---|
| `sim/out/lockstep-flight` | `sim/fly_reference.py --script flight --storage build/reference/storage-cf2x.bin` (`reference/REFERENCE.md:94`) | CF2X: `CtrlAviary(drone_model=DroneModel.CF2X)` via `run_copter.make_env` (`sim/fly_reference.py:424`, `sim/run_copter.py:266`), `gpd/assets/cf2x.urdf` | `build/reference/copter_ref` (default `--bin`, `sim/fly_reference.py:47`); the C++ reference build | image from `sim/params/reference-cf2x.txt` (`reference/REFERENCE.md:85, 92-93`) | 1200 Hz (default `--pyb-hz`, `sim/fly_reference.py:395`), 400 Hz lines | none |
| `sim/out/gorge-port-x500/` (`flight`, `flight-noise-s1`, `flight-wind-4-1`, `try1`..`try5`) | `sim/gorge_lockstep.py` (default `--vehicle x500`) (`sim/README.md:317`) | X500: leanfc's `GorgeAviary` with `leanfc/sim/assets/x500.urdf` and motor lag `(0.0125, 0.025)` (`sim/gorge_lockstep.py:426-427`) | `sim/lean_vehicle.py` (the translated vehicle, `flight.json` key `bin`) | `build/gorge-port/storage-x500.bin` from `sim/params/reference-x500.txt` (`sim/README.md:313`); `try2`..`try5` add yaw-gain `PARAM_SET`s (`flight.json` `params_set`) | 1200 Hz, 400 Hz | motor lag; wind and aerodynamic force only in `flight-wind-4-1` (`flight.json` `wind: [4.0, 1.0]`) |
| `sim/out/gorge-port-x500-fast/` (`flight`, `flight-noise-s1`, `flight-wind-4-1`, `ladder-s4..s10`, `ladder-s8-acc4.5`) | `sim/gorge_lockstep.py --params sim/params/gorge-fast-x500.txt` (`sim/README.md:399`) | X500, as above | `sim/lean_vehicle.py` | X500 image + `gorge-fast-x500.txt` (WP_SPD 7, WP_ACC 4.5, WP_JERK 6; ladder runs vary WP_SPD/WP_ACC) | 1200 Hz, 400 Hz | as above |
| `sim/out/gorge-port-x500-smooth/` (`flight`, `flight-noise-s1`, `flight-wind-4-1`) | `sim/gorge_lockstep.py --params sim/params/gorge-smooth-x500.txt` (`sim/README.md:411`) | X500 | `sim/lean_vehicle.py` | X500 image + `gorge-smooth-x500.txt` (8 navigation/attitude-shaping parameters) | 1200 Hz, 400 Hz | as above |
| `sim/out/gorge-port-x500-scurve/` (`flight`, `flight-noise-s1`, `flight-wind-4-1`) | `sim/gorge_lockstep.py --straight-north 26.34,47.3,72.0 --params sim/params/gorge-scurve-x500.txt` (`sim/README.md:523`) | X500 | `sim/lean_vehicle.py` | X500 image + `gorge-scurve-x500.txt` (WP_SPD 9, WP_ACC 5, WP_JERK 8) | 1200 Hz, 400 Hz | as above |
| `sim/out/gorge-port/` (`flight`, `flight-noise-s1`, `try1`..`try3`) | `sim/gorge_lockstep.py --vehicle cf2x --params sim/params/gorge-port.txt` (`sim/README.md:743`) | CF2X in the gorge world, no lag, no wind (`sim/gorge_lockstep.py:428-429`) | `sim/lean_vehicle.py` | `build/reference/storage-cf2x.bin` + `gorge-port.txt` (rate gains) | 1200 Hz, 400 Hz | none |
| `sim/out/gorge-formation-x500/{abreast,staggered}/` | `sim/gorge_formation_lockstep.py --plan ...` (`sim/README.md:641-651`) | two X500s in leanfc's `FormationAviary`, lag per vehicle, no wind (`sim/gorge_formation_lockstep.py:93-123`) | two `sim/lean_vehicle.py` processes | copies of `storage-x500.bin` | 1200 Hz, 400 Hz | lag; no aerodynamic interaction |

Evidence in the output directories: every `flight/flight.json` of the gorge runs records `vehicle` (`"x500"`, or absent
for `gorge-port`, whose `storage` is `storage-cf2x.bin` and whose `log.txt` line 2 says "CF2X settled"), `bin`,
`storage`, `wind`, `seed` and `params_set`; each X500 `log.txt` line 2 reads "mass 2.0643 kg, inertia [0.02167,
0.02167, 0.04], kf 9.37457e-08 N/RPM^2, km 1.49993e-09, thrust-to-weight 1.6891, MAX_RPM 9549.30, motor lag (0.0125,
0.025), collision r 0.25 h 0.22". `sim/out/lockstep-flight` has no `flight.json`; its `log.txt` names only the frame
(QUAD/X) and its `summary.txt` the step count (36,013 lines, 90.03 s). Its vehicle model (CF2X) and binary
(`copter_ref`) are determined from the producing script and the command in `reference/REFERENCE.md:94`, not from a
file in the directory. The physics rate is not written in any output file; it is determined from the code defaults
(`--pyb-hz 1200`, no README command overrides it) and from `inputs.txt`, whose `imu0=` field carries three samples per
400 Hz line in both `lockstep-flight` and `gorge-port-x500/flight` (one per physics substep, `sim/gorge_lockstep.py:11`).
`sim/fly.sh` drives the older `run_copter.py` flights (`sim/out/{lean,ref}-{hover,course-1ms,figure8}`), all CF2X
(`sim/run_copter.py:266`, params `sim/params/copter-cf2x*.txt`); they are not the flights surveyed here.

## 2. The X500 as simulated

**Origin.** No X500 model exists in `sim/`, in `gpd/assets/` (only `cf2x`, `cf2p`, `racer` URDFs), or as ArduPilot
SITL/Gazebo parameters in this repository. The model is leanfc's `leanfc/sim/assets/x500.urdf`, a URDF in
gym-pybullet-drones' format whose header (lines 3-38) derives every number from PX4-gazebo-models `x500_base/model.sdf`
and `x500/model.sdf`. It is loaded by `leanfc/sim/run_leanfc.py:117-119, 161-188` (`AIRFRAMES["x500"]`,
`LeanfcAviary`: URDF from outside the package plus the motor lag), wrapped by `leanfc/sim/world/wind.py:96-118`
(`WindAviary`) and `leanfc/sim/world/fly_gorge.py:55-83` (`LAG`, `GorgeAviary`, `URDF_USE_INERTIA_FROM_FILE` at line 82).
`DroneModel.CF2X` is still passed (`sim/gorge_lockstep.py:179`), which selects the CF2X branches of `BaseAviary`
(e.g. `MAX_XY_TORQUE`, the `_dynamics` model), none of which `Physics.PYB` uses.

| quantity | X500 | source | CF2X (for comparison, `Plant/Model/Constants.lean`) |
|---|---|---|---|
| mass | 2.0643076923076924 kg (base 2.0 + 4 rotors 0.016077, lumped) | `x500.urdf:9-10, 48` | 0.027 kg |
| inertia tensor | diag(0.021666…, 0.021666…, 0.04) kg m², products 0; rotor share (~0.002 per axis) left out | `x500.urdf:11-13, 49` | diag(1.4e-5, 1.4e-5, 2.17e-5) |
| motor positions (FLU, m) | prop0 (+0.174, −0.174, 0.06), prop1 (−0.174, −0.174, 0.06), prop2 (−0.174, +0.174, 0.06), prop3 (+0.174, +0.174, 0.06) | `x500.urdf:73, 85, 97, 109` | (±0.028, ±0.028, 0) |
| roll/pitch lever | 0.174 m (arm 0.174·√2 = 0.24607 m, `arm` attribute, used only by `_dynamics`) | `x500.urdf:14, 42` | 0.028 m |
| spins | prop0 CCW, prop1 CW, prop2 CCW, prop3 CW (cf2x.urdf's order; package yaw sum `−t0 + t1 − t2 + t3`) | `x500.urdf:24-26`, `gpd/envs/BaseAviary.py:694` | same |
| slot order | ArduPilot quad-X slots 0..3 (FR CCW, RL CCW, FL CW, RR CW) = PX4 rotor_0..3 = props 0, 2, 3, 1 = `SLOT_TO_SIM` | `x500.urdf:15-16, 26-27`, `sim/README.md:336-339` | same map |
| thrust coefficient | kf = 9.37456697678494e-08 N/rpm² (= 8.54858e-06 N/(rad/s)²) | `x500.urdf:17, 20, 42` | 3.16e-10 N/rpm² |
| drag-torque coefficient | km = 1.4999307162855904e-09 N m/rpm²; km/kf = 0.016 m (momentConstant) | `x500.urdf:18, 20, 42` | km/kf = 0.025127 m |
| thrust-to-weight | 1.689113625148385 | `x500.urdf:21, 42` | 2.25 |
| max motor speed | MAX_RPM = 9549.2966 rpm = 1000 rad/s (with g = 9.80665) | `x500.urdf:22-23`, `fly_gorge.py:99` | 21710.0 rpm |
| max thrust per motor | fmax = 8.54858 N | `x500.urdf:23` | 0.148938 N |
| collision | cylinder r 0.25 m, length 0.22 m, centered 0.09 m below base | `x500.urdf:29-32, 62-67` | cylinder from `cf2x.urdf` |
| URDF coefficients not used by `Physics.PYB` | `drag_coeff_xy` 8.06428e-05, `drag_coeff_z` 0, `gnd_eff_coeff` 0, `dw_coeff_*` 0, `max_speed_kmh` 43.2, `prop_radius` 0.1396 | `x500.urdf:33-38, 42` | nonzero CF2X values, `cf2x.urdf:5` |

**Actuator map.** Identical to the CF2X: `a = (PWM − 1000)/1000` clipped to `[0, 1]`, rpm `= MAX_RPM √a`, so the
commanded thrust is `a · 8.54858 N`, linear in `a` from zero (`sim/gorge_lockstep.py:23-24`,
`sim/params/reference-x500.txt:15-18`). ArduPilot is configured to match: `MOT_PWM_MIN 1000`, `MOT_PWM_MAX 2000`,
`MOT_THST_EXPO 0`, `MOT_SPIN_ARM 0`, `MOT_SPIN_MIN 0`, `MOT_SPIN_MAX 1`, `MOT_HOVER_LEARN 0`, `MOT_THST_HOVER 0.3835`
(`reference-x500.txt:19-30`); `MOT_BAT_VOLT_MAX` stays at its default 0 (`reference-x500.txt:35-36`). The hover value
0.3835 is `1/1.689114 × 0.64783`: ArduPilot divides motor demands by the 1976-atmosphere density ratio at the gorge's
4302 m (`AP_Motors_Thrust_Linearization::get_compensation_gain`), while the simulated thrust does not depend on altitude
(`reference-x500.txt:26-29`, `sim/README.md:363-367`). Attitude gains are those of ArduPilot's
`Tools/Frame_params/Holybro-X500v2-bdshot.param` with yaw changed (`reference-x500.txt:32-71`; the file is at
`build/reference/ap/Tools/Frame_params/`).

**Derived quantities** (python evaluation of the formulas above, g = 9.80665):

| quantity | X500 | CF2X |
|---|---|---|
| weight m g | 20.2439 N | 0.264780 N |
| total max thrust 4 fmax | 34.1943 N | 0.595754 N |
| hover thrust fraction 1/thrust2weight | 0.592026 | 0.444444 |
| amax = thrust2weight · g | 16.5645 m/s² | 22.0650 m/s² |
| alphaMax = 2 · lever · fmax / Jx (roll, pitch) | 137.303 rad/s² | 595.754 rad/s² |
| yaw bound 2 · (km/kf) · fmax / Jz | 6.8389 rad/s² | 344.914 rad/s² |
| yaw bound / roll bound | 0.0498 | 0.579 |
| h · alphaMax (rate change per 1/400 s) | 0.3433 rad/s | 1.4894 rad/s |
| (Jz − Jx)/Jx | 0.846154 (= 11/13) | 0.55 (= 11/20) |
| Jz / Jx | 1.846154 (= 24/13) | 1.55 (= 31/20) |
| (km/kf) · Jx ≤ lever · Jz | 3.467e-4 ≤ 6.96e-3, true | 3.518e-7 ≤ 6.076e-7, true |
| rotor speed at hover | 769.43 rad/s | — |

**Terms in the X500 simulation that the CF2X equations of `Plant/Model/Field.lean` do not have.**

| term | X500 as simulated | source |
|---|---|---|
| motor lag | first-order lag on each propeller's thrust, time constant 0.0125 s rising and 0.025 s falling (PX4 gz `timeConstantUp/Down`), chosen per substep by the sign of `cmd − thrust`; applied once per 1/1200 s substep as `T ← T + (cmd − T)(1 − e^{−dt/τ})`, then `rpm = √(T/kf)`, so both the force and the drag torque `km rpm²` follow the lagged thrust. Per substep the step fraction is 0.0645 up, 0.0328 down; per 1/400 s period 0.181 up, 0.095 down. Starts from the first command (motors off, zero thrust) in the gorge runs | `leanfc/sim/run_leanfc.py:32-39, 178-188`, `fly_gorge.py:55`, `sim/gorge_lockstep.py:20-21, 26-27` |
| consequence for the hold | the command is held over the 1/400 s period, the applied thrust is not: it is piecewise constant over the three 1/1200 s substeps | same |
| aerodynamic force (wind runs only, `flight-wind-4-1`) | rotor drag `−C_R Σ|ω_i| v_rel⊥` with `C_R = 8.06428e-05` N/(m/s)/(rad/s) (0.248 N/(m/s) lumped at hover) plus body drag `−½ ρ CdA |v_rel| v_rel`, ρ = 1.16, CdA = 0.04 m²; at the center of mass (no moment), every substep; Dryden-style turbulence | `leanfc/sim/world/wind.py:22-35, 51-63, 105-118` |
| ground effect, downwash | none (coefficients 0, and `Physics.PYB` calls neither) | `x500.urdf:33-36`, `gpd/envs/BaseAviary.py:352-366` |
| rotor inertia, gyroscopic rotor torque, rolling moment | none (propeller links have mass and inertia 0) | `x500.urdf:33-36, 74-75` |
| thrust point height | 0.06 m above the base; for a force along body z this adds no moment | `x500.urdf:28, 73` |
| integration, physics rate, control rate, gravity, damping | the same as the CF2X runs: PyBullet `stepSimulation` at 1200 Hz, 400 Hz vehicle lines, g = 9.80665, damping 0 | `sim/gorge_lockstep.py:177-186`, `sim/run_copter.py:338` |
| contact | PyBullet contact with the gorge bodies (both vehicles); not in the Lean plant for either | `fly_gorge.py:59-83` |

## 3. What in the Lean plant depends on CF2X numbers

Method: every declaration in `Plant/` (outside `Model/Constants.lean`) was listed, scanned for `norm_num [...]` over
model constants, `unfold ... gyro`, the literals `11 / 20` and `31 / 20`, `Jy_eq_Jx`, `Jx_le_Jz` and
`kmkf * Jx ≤ lever * Jz`, and then the dependence was closed under references. `Model/Constants.lean` itself has 32
declarations (15 defs, all CF2X literals or derived from them; 17 theorems, of which `kf_maxRPM_sq`, `km_maxRPM_sq`, the
ten positivity facts, `Jy_eq_Jx` and `Jx_le_Jz` are proved by `norm_num` on the numbers, and `four_kf_maxRPM_sq`,
`fmax_eq`, `four_fmax_div_mass` follow from `kf_maxRPM_sq` by algebra).

**Counts** (275 declarations outside `Constants.lean`, including 9 `example`s):

| file | decls | (a) structural | (b) direct CF2X numbers | (b′) only through (b) |
|---|---|---|---|---|
| `Lib/Real.lean`, `Lib/Blocks.lean`, `Lib/RadialTrunc.lean` | 35 | 35 | 0 | 0 |
| `Model/Field.lean` | 42 | 42 | 0 | 0 |
| `Field/Bounds.lean` | 31 | 24 | 7 | 0 |
| `Field/Invariants.lean` | 22 | 21 | 1 | 0 |
| `Flow/Flow.lean` | 35 | 5 | 3 | 27 |
| `Step/Euler.lean` | 28 | 12 | 3 | 13 |
| `Step/Sharp.lean` | 66 | 21 | 24 | 21 |
| `Step/Sample.lean` | 16 | 6 | 0 | 10 |
| **total** | **275** | **166** | **38** | **71** |

**(a) Structural.** Valid for any values of the constants given the facts they cite. `Lib/` imports no model file.
`Model/Field.lean` is definitions and `rfl`/`simp` component lemmas. The structural theorems in `Field/`, `Flow/` and
`Step/` use only `Jx_pos` (8 declarations), `Jy_pos` (6), `Jz_pos` (6), `fmax_pos` (7), `amax_pos` (6), `h_pos` (6),
`grav_pos` (5), `mass_pos` (3), `lever_pos` (3), `four_fmax_div_mass` (2), `kmkf_pos`, `km_maxRPM_sq`, `fmax_eq` (1 each).
Examples: `thrust_eq`, `accel_le`, `abs_torque{X,Y,Z}_le`, `abs_torqueX_div_le`, `vf_sub_p/v/q`, `abs_vf_v/q`, `Klip`,
`Mbd` (Bounds); `q_dot_scaled`, `energy_dot_scaled`, `energy_scaledSol`, `ctau`, `box`, `energy_le_of_norm_le`
(Invariants); `vfT`, `vfT_eq_vf`, `hoverState`, `hoverX` (Flow); `eulerStep`, `energy_le_of_WBd`, `quatOf`,
`downAxis_quatOf` (Euler); `TorqueBd`, `accel_le_mul`, `hasDerivAt_dn/dnDot`, `dnDDot`, `abs_vf_vI_le`, `alphaMax_eq`
(Sharp); `dtUs`, `SampleR`, `PState`, `tickSpecForce`, `sampleR`, `hoverP` (Sample).

**(b) Direct dependence on CF2X numbers or ratios** (38):

| kind | declarations (file:line) | what is used | holds for the X500 numbers? |
|---|---|---|---|
| literal `gyro = 11/20` | `gyro` (`Bounds.lean:132`) | `(Jz − Jx)/Jx` of the CF2X, exactly | value is 11/13 |
| `|(Jz−Jy)/Jx|, |(Jx−Jz)/Jy|, |(Jy−Jx)/Jz| ≤ 11/20` by `norm_num [Jx, Jy, Jz, gyro]` | `vf_sub_w` (`Bounds.lean:229-262`), `abs_vf_w` (`:311-333`), `abs_vf_wA` (`Sharp.lean:146-168`) | numbers of J | no (0.846 > 0.55) |
| numeric size of `gyro` (`unfold ... gyro; nlinarith`) | `vf_lipschitz_ball` (`Bounds.lean:367`), `norm_vf_le` (`:398`) | `2·gyro ≤ 3`, `gyro ≤ 4 amax + 2` | yes, with gyro = 11/13 |
| `0 ≤ gyro` by `norm_num [gyro]` | `WBd_traj` (`Euler.lean:97`), `le_wTA` (`Sharp.lean:178`), `WBd_trajA` (`:191`) | sign only | yes |
| literal `31/20 = Jz/Jx` | `Cd` (`Sharp.lean:277`), `Cd_mono` (`:282-292`), `abs_dnDDot_le` (`:299-302`, `(Jz − Jx)/Jy + 1 = 31/20` by `norm_num [Jx, Jy, Jz]`) | Jz/Jx of the CF2X, exactly | no (24/13) |
| `Jy_eq_Jx` | `abs_torqueY_div_le` (`Bounds.lean:111`), `torqueBd_of_spread` (`Sharp.lean:120`), `norm_le_box_of_scaledSol` (`Invariants.lean:314`), `WBd_of_energy_le` (`Euler.lean:51`) | Jx = Jy | yes |
| `Jx_le_Jz` | `norm_le_box_of_scaledSol`, `WBd_of_energy_le` (same lines) | Jx is the smallest moment | yes |
| `kmkf * Jx ≤ lever * Jz` by `norm_num [kmkf, km, kf, Jx, lever, Jz]` | `abs_torqueZ_div_le` (`Bounds.lean:120`), `torqueBd_of_spread` (`Sharp.lean:130`) | yaw bound below `alphaMax` | yes |
| `0 ≤ Jx + Jy + Jz` by `norm_num [Jx, Jy, Jz]` | `norm_le_box_of_scaledSol` (`Invariants.lean:309`), `box_mono` (`Flow.lean:235`), `WBd_traj_energy` (`Euler.lean:80`) | follows from positivity | yes |
| `0 ≤ 1/thrust2weight ≤ 1` by `norm_num [thrust2weight]` | `accel_hover` (`Flow.lean:297-302`), `vf_hover` (`:307-311`) | thrust2weight ≥ 1 | yes |
| evaluated constants (`Sharp.lean:697-838`) | `alphaMax_le_num`, `alphaMax_ge_num` (595.75..595.76), `amax_le_num` (22.066), `wB_one_le` (5), `wTA_one_alphaMax_le` (2.53), `Cd_alphaMax_le` (857), `wTA_one_spread_le` (1.52), `Cd_spread_le` (275), and the 9 `example`s at lines 742, 749, 754, 761, 771, 776, 799, 806, 827 (4.93e-5, 2.19e-5, 3.1e-8, 4.93e-5, `Katt = 5.295`, 1.511, 2.86e-3/5.22e-3, 3.85e-3, 9.8e-6) | `norm_num` on CF2X values, `h`, `gyro`, `31/20` | values change (alphaMax 137.30, amax 16.56) |

**(b′) Only through (b)** (71). Two roots carry most of them. (1) `vf_lipschitz_ball` (uses `vf_sub_w` and the size of
`gyro`) gives `vfT_lipschitz`, hence `flowT`, `traj`, `step`, and everything built on them: all of `Flow.lean` except
5 declarations, `nextR`, `IsRun`, `sampledFlow`, `run_*` in `Sample.lean`, and the trajectory theorems of `Euler.lean`
and `Sharp.lean`. (2) `norm_le_box_of_scaledSol` (`Jy_eq_Jx`, `Jx_le_Jz`) gives `traj_norm_le`, hence
`traj_hasDerivAt`. Further: `wT`, `Mw`, `cE`, `wTA`, `Katt`, `attF0`, `Mw1`, `cW`, `cQ` contain `gyro` in their
definitions; `traj_dn`, `traj_pv_sharp`, `step_pv_sharp`, `traj_pv_first` contain `Cd`; `torqueBd_alphaMax` uses
`abs_torqueY_div_le`/`abs_torqueZ_div_le`; `sampleR_hover` and `step_hover` use `accel_hover`/`vf_hover`.

**Features that are CF2X-specific in form, not only in value** (with the X500 fact for each):

| feature of `Model/Field.lean` | X500 as simulated |
|---|---|
| `J = diag(Jx, Jy, Jz)` with `Jx = Jy` used in proofs | diagonal, Jx = Jy |
| X layout with one `lever` for roll and pitch, signs fixed by `SLOT_TO_SIM` | square ±0.174, same slot map |
| yaw torque `(km/kf) · fmax · (u0 + u1 − u2 − u3)`, proportional to thrust | same form, km/kf = 0.016 |
| force `fmax · clip01(u_i)`, instantaneous in `u` | thrust lags the command (4 extra states, rise/fall time constants differ) |
| actuators constant over the period, exact flow of one ODE | command constant, thrust piecewise constant on three 1/1200 s substeps |
| no aerodynamic force | none in record flights; rotor and body drag with wind in `flight-wind-4-1` |
| thrust in the plane z = 0 of the center of mass | at z = +0.06 m; no effect on the moment of a body-z force |

## What a second vehicle would need

1. Its own constants (mass, J, lever, kf, km, thrust2weight) with sources, from `leanfc/sim/assets/x500.urdf`.
2. `gyro` defined as `(Jz − Jx)/Jx` (or a max of the three ratios) and `31/20` replaced by `Jz/Jx`, so that `vf_sub_w`,
   `abs_vf_w`, `abs_vf_wA`, `Cd`, `abs_dnDDot_le` hold for other inertias; the facts `Jy_eq_Jx`, `Jx_le_Jz`,
   `kmkf * Jx ≤ lever * Jz`, `1 ≤ thrust2weight` stated as hypotheses or proved per vehicle.
3. Re-evaluation of the numeric section of `Step/Sharp.lean` (lines 697-838).
4. For the X500 as flown: a motor-lag state (four lagged thrusts, asymmetric time constants, updated per 1/1200 s
   substep) in the state and the field; the wind runs additionally need the drag force of `leanfc/sim/world/wind.py`.

## Addendum: the phase-3 files

The counts above cover the files carried over from the archive and `Lib/`. The files added afterwards
(`Field/Actuators.lean`, `Flow/Sensitivity.lean`, `Step/Exact.lean`, `Step/Symmetry.lean`, `Step/Period.lean`,
`Step/Multi.lean`) were written without evaluated constants. Their direct uses of CF2X facts are:

| declaration | CF2X fact used | holds for the X500 |
|---|---|---|
| `abs_torqueZ_div_sub_le` (`Field/Actuators.lean`), hence `norm_vf_sub_input_le` and the input bounds of `Flow/Sensitivity.lean` | `kmkf * Jx ≤ lever * Jz` by `norm_num` | yes (survey above) |
| `abs_torqueY_div_sub_le` | `Jy_eq_Jx` | yes |
| `accel_const_eq_grav_iff`, `step_level_hover_vz` | `0 < thrust2weight`, `1 / thrust2weight ≤ 1` by `norm_num` | yes (1.6891) |

`Flow/Sensitivity.lean` also depends on `vf_lipschitz_ball` and `box`, so it is in class (b′) of the table above
(through `gyro = 11/20` in `vf_sub_w`). `Step/Exact.lean`, `Step/Symmetry.lean`, `Step/Period.lean` and
`Step/Multi.lean` use only the field's form, positivity facts and the flow's existence and uniqueness; the spin and
level-flight solutions use the X layout (roll and pitch torque zero for pairwise equal commands) and `Jx = Jy` only
through the gyroscopic term vanishing when two rates are zero, which holds for any diagonal `J`.
