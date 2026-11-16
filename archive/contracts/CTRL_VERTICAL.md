# The vertical controller lemmas (C1, C5, C6, C7, C12)

Files: `Contracts/Track/CtrlVerticalFloat.lean`, `CtrlVerticalPID.lean`, `CtrlVerticalIO.lean`,
`CtrlVerticalD.lean`, `CtrlVerticalWorld.lean`, `CtrlVertical.lean`, `CtrlVerticalNav.lean`
(library `Track`, namespace `Contracts.Track.CtrlV`). Everything below is sorry-free and depends
on `propext`, `Classical.choice`, `Quot.sound` only (`#print axioms` at the end of
`AxiomCheck.lean`); `LibmSpec` and `PiF32` enter as arguments.

## Status

| lemma | translated function | file | form |
|---|---|---|---|
| C1 `estimates` | `AC_PosControl::update_estimates` | `CtrlVerticalIO` | exact (`β = 0`): the sample's position and velocity |
| C5 `pos_p` | `AC_P_1D::update_all` | `CtrlVerticalPID` | linear zone: target kept, error `A32 (t-m) (2uE+2η)` |
| C5 `vel_pi`, `vel_pi2` | `AC_PID_Basic::update_all` (5 Hz E and D filters) | `CtrlVerticalPID` | output `5·E'` within `10u·Me+η`, integrator `0` |
| C6 `accel_pid`, `accel_pid2` | `AC_PID::update_all` (20 Hz E filter, IMAX inactive) | `CtrlVerticalPID` | target, filtered error, integrator, `kp·E'+I'`, `ff = 0` |
| C5/C6 `dctrl2_*` | the same inside `D_update_controller` | `CtrlVerticalD` | `vt`, `vel`, `at`, `am`, `acc`, `thr` |
| C7 `boost_A32`, `boost_c` | `set_throttle_out` with angle boost | `CtrlVerticalIO` | `t / cos θ` within `β_b·|t| + η` (`cos θ ≥ c0`) |
| C12 `throttle_filter`, `throttle_filter2` | `update_throttle_filter` (2 Hz) | `CtrlVerticalIO` | `f + αT(u - f)` within `(1.02+4.11αT)·u·3/4 + 2η` |
| C12 mixer mean | `output_armed_stabilizing`, `output_to_motors` | | hypothesis `hmix` |
| `vtick_real`, `vtick_split` | the join in real numbers | `CtrlVertical` | `βvec`; `βcode` after `wS` |
| `vertical_tick_rel` | `Vehicle.tick`: code values satisfy the C-relations | `CtrlVertical` | `VRel` + `vstate` before/after |
| `vertical_tick_eq` | `Vehicle.tick`, vertical rows | `CtrlVertical` | `|ξ' - (A_v ξ + asp·B_v + defects)| ≤ βvec` |
| `vertical_tick_split` | the same, `wS` split off | `CtrlVertical` | `|ξ' - tick ξ - wS| ≤ βcode` |
| `navV_mk`, `navV_of_logs` | the navigator's frame `NavV` | `CtrlVerticalNav` | see below |

The state is `vstate w z vz held sp vsp` = `[z-sp, vz-vsp, eV, eA, I-(hover-1/2.25), f-1/2.25,
u-1/2.25, held-1/2.25]` (`VERTICAL.md` §1). The coefficients are the code's own float values,
exact under `PiF32`: `αV = 4886901/2^26`, `αA = 16042859/2^26`, `αT = 16352567/2^29`,
`kiDt = 72057593501057/2^58`, `kpAcc = 13421773/2^28`, period `dtR = 5368709/2^31`.

## The tick's `β` (`veOf`, `βcode`)

`u = 2^-24`, `η = 2^-149`, `MeV = E + Ev + 1/8`:

* `vt = u(4E+Vv) + 4η`, `V = αV(u·MeV+η) + (1.02+4.11αV)u·MeV + 2η`
* `atg = u(21·MeV + Aa) + 3η`, `am = u(Aa+Aam) + η`
* `E = αA(5.14u·Ma + u·MeA + 4η) + (1.02+4.11αA)u·MeA + 2η`
* `I = u|I| + u·MeA/2^7 + 4η`, `N = u(MeA + 2K + 2) + 6η`
* `b = (2^-22/((c0-2^-22)c0) + 3u/(c0-2^-22) + η)|thr| + η`, `f = (1.02+4.11αT)u·3/4 + 2η`, `mix = εmix`
* `βcode = [per²/2·amax(f+mix), per·amax(f+mix), W2, W3c, W4c, f, kpAcc·W3c + W4c + N + b, f+mix]`
  with `W2 = αV(vt+smp) + V`, `W3c = αA(5W2 + atg + am) + E`, `W4c = kiDt·W3c + I`.

At the magnitudes `Induction/Vert.lean` uses (E 0.11, Ev 0.6, Vv 2, Aa 3, Aam 5, Ma 16, MeA 16,
K 2, |I| 2, |thr| 3, c0 0.9, εmix 1e-7, εsmp 0): `βcode ≈ [1.0e-11, 8.3e-9, 8.0e-8, 3.8e-6,
1.3e-7, 5.1e-8, 3.1e-6, 1.5e-7]`. Row 4 (`eA`) is dominated by the float rounding of the 20 Hz
error filter, `≈ 2u·MeA`; it scales linearly with `MeA` and `Ma`.

## Hypotheses of `vertical_tick_eq` (`VTickHyp`)

* schedule: Auto mode, mission started, not the first tick, `dt_us = 2500`;
* `NavV`: the navigator leaves `_pid_vel_d_m`, `_pid_accel_d_m`, the estimates, `_dt_s`, the
  throttle filter, the motors' parameters and the sample alone. `CtrlVerticalNav` proves the
  motors/sample part unconditionally (`nf_mission_update`, `nf_navW`) and the position
  controller part for every replayed call except `D_init_controller_stopping_point`
  (`vf_replayPos`, `vf_navW`); `mission_update_steady` covers a tick whose waypoint is loaded and
  not reached; `navV_of_logs` assembles `NavV` from "mission update keeps `ps`" and "the
  `update_wpnav` log has no `D_init_controller_stopping_point`";
* `DPar2` (tuning: kP, kI, filter frequencies, `FLTT = 0`, `SMAX = 0`, `PDMX = 0`, `IMAX`) and
  `DReg2` (region: errors inside the P_1D linear zone, PID inputs and states bounded by
  `E, Ev, Vv, Aa, Aam, Ma, MeA`, offsets zero, hover in `[1/4, 3/4]`);
* the controller active, no EKF reset on this tick, vibration compensation off, hover below `IMAX`;
* `MotReg` (armed, filter initialized, cutoff 2 Hz, filter and `_throttle_in` in `[1/4, 3/4]`);
* `BoostReg` (boost enabled, `cos θ ≥ c0` for the attitude controller's target tilt);
* `hmix`: the mean of the four actuators is the throttle filter's output within `εmix`.

## Findings

* The angle boost divides by the cosine of the attitude controller's `_thrust_angle_rad` (the
  target tilt), not `cos_roll·cos_pitch` of the AHRS view; `VERTICAL.md` should say so.
* The QUAD-X roll factors are `[-0.49999997, 0.49999997, 0.49999997, -0.5]` as floats; they sum to
  `-2^-25`, not `0` as `VERTICAL.md` states. The effect on the mean actuator is below `2^-25`
  times the roll input, absorbed in `εmix`.
* `(float)π` is not determined by `LibmSpec` (both neighbors are within `2^-24` relative); the
  coefficients are exact only under the explicit fact `PiF32`
  (`Float.toFloat32 3.1415926535897931 = 3.14159274`).
* Trims: the integrator trim is `hover - 1/2.25` (`0.4444f ≠ 1/2.25`); `9.80665016f - g` enters
  `ρam`.

## Not discharged

`hmix` (the mixer mean, C12 second half: the full unrolling of `output_armed_stabilizing` exceeds
the elaborator's budget; `output_to_motors` unrolls), the position-controller part of `NavV` on a
waypoint switch, `DReg2`/`MotReg`/`BoostReg` (region invariants for the induction), `PiF32`.
